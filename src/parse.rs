use std::cell::RefCell;
use std::fmt::Debug;
use std::num::NonZeroUsize;
use std::rc::Rc;

use antlr_rust::common_token_stream::CommonTokenStream;
use antlr_rust::error_listener::ErrorListener;
use antlr_rust::errors::ANTLRError;
use antlr_rust::parser_rule_context::ParserRuleContext;
use antlr_rust::token::CommonToken;
use antlr_rust::token_factory::TokenFactory;
use antlr_rust::tree::TerminalNode;
use antlr_rust::{InputStream, Parser};
use thiserror::Error;

use crate::grammar::lexer::LibSLLexer;
use crate::grammar::libslparser::{
    ActionDeclContextAll, ActionDeclContextAttrs, ActionDeclParamListContextAttrs,
    ActionParameterContextAttrs, AnnotationDeclContextAll, AnnotationDeclContextAttrs,
    AnnotationDeclParamsContextAttrs, AnnotationDeclParamsPartContextAttrs,
    AnnotationUsageContextAll, AutomatonDeclContextAll, EnumBlockContextAll, EnumBlockContextAttrs,
    EnumBlockStatementContextAll, EnumBlockStatementContextAttrs, EnumSemanticTypeContextAttrs,
    EnumSemanticTypeEntryContextAll, EnumSemanticTypeEntryContextAttrs, ExpressionAtomicContextAll,
    ExpressionContextAll, FileContextAttrs, FunctionDeclContextAll, GenericContextAll,
    GlobalStatementContextAll, GlobalStatementContextAttrs, HeaderContextAll,
    IntegerNumberContextAll, LibSLParserContextType, NameWithTypeContextAll,
    NameWithTypeContextAttrs, SemanticTypeDeclContextAll, SemanticTypeDeclContextAttrs,
    SimpleSemanticTypeContextAttrs, TargetTypeContextAttrs, TopLevelDeclContextAttrs,
    TypeDefBlockContextAll, TypeDefBlockContextAttrs, TypeDefBlockStatementContextAttrs,
    TypeExpressionContextAll, TypeIdentifierContextAll, TypeListContextAttrs,
    TypealiasStatementContextAll, TypealiasStatementContextAttrs, TypesSectionContextAttrs,
    VariableDeclContextAll, WhereConstraintsContextAll,
};
use crate::grammar::parser::{FileContextAll, LibSLParser};
use crate::loc::{Loc, Span};
use crate::{LibSl, ast};

pub type Result<T, E = ParseError> = std::result::Result<T, E>;

type Terminal<'a> = TerminalNode<'a, LibSLParserContextType>;

fn strip_surrounding(s: &str, prefix: char, suffix: char) -> &str {
    s.strip_prefix(prefix)
        .and_then(|s| s.strip_suffix(suffix))
        .unwrap_or(s)
}

fn parse_string_lit(token: &CommonToken<'_>) -> String {
    strip_surrounding(&token.text, '"', '"').into()
}

fn parse_ident(token: &CommonToken<'_>) -> String {
    strip_surrounding(&token.text, '`', '`').into()
}

fn strip_prefix_ascii_case_insensitive<'a>(s: &'a str, prefix: &str) -> Option<&'a str> {
    let (p, tail) = s.split_at_checked(prefix.len())?;

    p.eq_ignore_ascii_case(prefix).then_some(tail)
}

fn parse_import_or_include(ctx: &Terminal<'_>, kw: &str, rule_name: &str) -> Result<String> {
    let Some(tail) = strip_prefix_ascii_case_insensitive(&ctx.symbol.text, kw) else {
        panic!("a terminal `{rule_name}` does not start with '{kw}': {ctx:?}");
    };
    let Some(path) = tail.strip_suffix(';') else {
        panic!("a terminal `{rule_name}` does not end with `;`: {ctx:?}");
    };

    let path = path.trim_ascii();

    if path.is_empty() {
        Err(ParseError::SyntaxError {
            line: ctx.symbol.line,
            column: ctx.symbol.column,
            msg: format!("no path specified for the {kw} declaration"),
        })
    } else {
        Ok(path.into())
    }
}

#[derive(Error, Debug, Clone)]
pub enum ParseError {
    #[error("encountered a syntax error at L{line}:{column}: {msg}")]
    SyntaxError {
        line: isize,
        column: isize,
        msg: String,
    },
}

#[derive(Debug, Clone)]
struct ErrorCollector(Rc<RefCell<Vec<ParseError>>>);

impl ErrorCollector {
    fn new() -> (Self, Rc<RefCell<Vec<ParseError>>>) {
        let errors: Rc<RefCell<Vec<ParseError>>> = Default::default();

        (Self(errors.clone()), errors)
    }
}

impl<'input, T: Parser<'input>> ErrorListener<'input, T> for ErrorCollector {
    fn syntax_error(
        &self,
        _recognizer: &T,
        _offending_symbol: Option<&<<T>::TF as TokenFactory<'input>>::Inner>,
        line: isize,
        column: isize,
        msg: &str,
        _error: Option<&ANTLRError>,
    ) {
        self.0.borrow_mut().push(ParseError::SyntaxError {
            line,
            column,
            msg: msg.into(),
        });
    }
}

impl LibSl {
    pub fn parse_file(&mut self, file_name: String, contents: &str) -> Result<ast::File> {
        let input_stream = InputStream::new(contents);
        let lexer = LibSLLexer::new(input_stream);
        let token_stream = CommonTokenStream::new(lexer);
        let mut parser = LibSLParser::new(token_stream);
        parser.remove_error_listeners();
        let (error_listener, errors) = ErrorCollector::new();
        parser.add_error_listener(Box::new(error_listener));

        let tree = match parser.file() {
            Ok(tree) => tree,

            Err(e) => {
                let mut errors = errors.borrow_mut();

                if errors.is_empty() {
                    // the error listener didn't get a call but we still ended up with an error.
                    // we'll assume it's an internal error and panic.
                    panic!(
                        "got an error parsing `{file_name}` with no errors collected by the listener: {e}"
                    );
                }

                return Err(errors.swap_remove(0));
            }
        };

        AstConstructor::new(self, file_name).construct(&tree)
    }
}

struct AstConstructor<'a> {
    libsl: &'a mut LibSl,
    file_idx: usize,
}

impl<'a> AstConstructor<'a> {
    fn new(libsl: &'a mut LibSl, file_name: String) -> Self {
        let file_idx = libsl.file_names.len();
        libsl.file_names.push(file_name);

        Self { libsl, file_idx }
    }

    fn get_loc(&self, start: &CommonToken<'_>, stop: &CommonToken<'_>) -> Loc {
        let line = (start.line > 0).then_some(NonZeroUsize::new(start.line as usize).unwrap());
        let col = (start.column > 0).then_some(NonZeroUsize::new(start.column as usize).unwrap());

        Span {
            start: start.start as usize,
            len: (stop.stop as usize).saturating_sub(start.start as usize),
            file: self.file_idx,
            line,
            col,
        }
        .into()
    }

    fn construct(mut self, tree: &FileContextAll<'_>) -> Result<ast::File> {
        let loc = self.get_loc(&tree.start(), &tree.stop());
        let header = tree
            .header()
            .map(|header| self.process_header(&header))
            .transpose()?;

        let mut decls = vec![];

        for ctx in tree.globalStatement_all() {
            decls.extend(self.process_global_stmt(&ctx)?);
        }

        Ok(ast::File { loc, header, decls })
    }

    fn process_header(&mut self, ctx: &HeaderContextAll<'_>) -> Result<ast::Header> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());

        let libsl_version = ctx
            .lslver
            .as_ref()
            .map(|t| parse_string_lit(t))
            .unwrap_or_default();
        let library_name = ctx
            .libraryName
            .as_ref()
            .map(|t| parse_ident(t))
            .unwrap_or_default();
        let version = ctx.ver.as_ref().map(|t| parse_string_lit(t));
        let language = ctx.lang.as_ref().map(|t| parse_string_lit(t));
        let url = ctx.link.as_ref().map(|t| parse_string_lit(t));

        Ok(ast::Header {
            loc,
            libsl_version,
            library_name,
            version,
            language,
            url,
        })
    }

    fn process_global_stmt(
        &mut self,
        ctx: &GlobalStatementContextAll<'_>,
    ) -> Result<Vec<ast::Decl>> {
        fn unit_vec<T>(value: T) -> Vec<T> {
            vec![value]
        }

        if let Some(import) = ctx.ImportStatement() {
            self.process_decl_import(&import).map(unit_vec)
        } else if let Some(include) = ctx.IncludeStatement() {
            self.process_decl_include(&include).map(unit_vec)
        } else if let Some(ctx) = ctx.typesSection() {
            ctx.semanticTypeDecl_all()
                .into_iter()
                .map(|decl| self.process_decl_semantic_ty(&decl))
                .collect()
        } else if let Some(ty_alias) = ctx.typealiasStatement() {
            self.process_decl_ty_alias(&ty_alias).map(unit_vec)
        } else if let Some(ty) = ctx.typeDefBlock() {
            self.process_decl_struct(&ty).map(unit_vec)
        } else if let Some(ty) = ctx.enumBlock() {
            self.process_decl_enum(&ty).map(unit_vec)
        } else if let Some(decl) = ctx.annotationDecl() {
            self.process_decl_annotation(&decl).map(unit_vec)
        } else if let Some(decl) = ctx.actionDecl() {
            self.process_decl_action(&decl).map(unit_vec)
        } else if let Some(ctx) = ctx.topLevelDecl() {
            if let Some(decl) = ctx.automatonDecl() {
                self.process_decl_automaton(&decl).map(unit_vec)
            } else if let Some(decl) = ctx.functionDecl() {
                self.process_decl_function(&decl).map(unit_vec)
            } else if let Some(decl) = ctx.variableDecl() {
                self.process_decl_variable(&decl).map(unit_vec)
            } else {
                panic!("unrecognized topLevelDecl node: {ctx:?}");
            }
        } else {
            panic!("unrecognized globalStatement node: {ctx:?}");
        }
    }

    fn process_decl_import(&mut self, ctx: &Terminal<'_>) -> Result<ast::Decl> {
        let path = parse_import_or_include(ctx, "import", "ImportStatement")?;

        Ok(ast::Decl {
            id: self.libsl.decls.insert(()),
            loc: self.get_loc(&ctx.symbol, &ctx.symbol),
            kind: ast::DeclImport { path }.into(),
        })
    }

    fn process_decl_include(&mut self, ctx: &Terminal<'_>) -> Result<ast::Decl> {
        let path = parse_import_or_include(ctx, "include", "IncludeStatement")?;

        Ok(ast::Decl {
            id: self.libsl.decls.insert(()),
            loc: self.get_loc(&ctx.symbol, &ctx.symbol),
            kind: ast::DeclInclude { path }.into(),
        })
    }

    fn process_decl_semantic_ty(
        &mut self,
        ctx: &SemanticTypeDeclContextAll<'_>,
    ) -> Result<ast::Decl> {
        if let Some(ctx) = ctx.simpleSemanticType() {
            let annotations = self.process_annotation_usage_list(ctx.annotationUsage_all())?;
            let ty_name = self
                .process_ty_identifier_as_qualified_ty_name(ctx.semanticName.as_ref().unwrap())?;
            let real_ty = self.process_ty_identifier_as_ty_expr(ctx.realName.as_ref().unwrap())?;

            Ok(ast::Decl {
                id: self.libsl.decls.insert(()),
                loc: self.get_loc(&ctx.start(), &ctx.stop()),
                kind: ast::DeclSemanticTy {
                    annotations,
                    ty_name,
                    real_ty,
                    kind: ast::SemanticTyKind::Simple,
                }
                .into(),
            })
        } else if let Some(ctx) = ctx.enumSemanticType() {
            let annotations = self.process_annotation_usage_list(ctx.annotationUsage_all())?;
            let ty_name = self.process_identifier_as_qualified_ty_name(&Terminal::new(
                ctx.semanticName.clone().unwrap(),
            ))?;
            let real_ty = self.process_ty_identifier_as_ty_expr(ctx.realName.as_ref().unwrap())?;
            let entries = ctx
                .enumSemanticTypeEntry_all()
                .into_iter()
                .map(|entry| self.process_semantic_ty_enum_value(&entry))
                .collect::<Result<Vec<_>>>()?;

            Ok(ast::Decl {
                id: self.libsl.decls.insert(()),
                loc: self.get_loc(&ctx.start(), &ctx.stop()),
                kind: ast::DeclSemanticTy {
                    annotations,
                    ty_name,
                    real_ty,
                    kind: ast::SemanticTyKind::Enumerated(entries),
                }
                .into(),
            })
        } else {
            panic!("unrecognized semanticTypeDecl node: {ctx:?}");
        }
    }

    fn process_semantic_ty_enum_value(
        &mut self,
        ctx: &EnumSemanticTypeEntryContextAll<'_>,
    ) -> Result<ast::SemanticTyEnumValue> {
        let name = self.process_identifier(&ctx.Identifier().unwrap())?;
        let expr = self.process_expr_atomic(&ctx.expressionAtomic().unwrap())?;

        Ok(ast::SemanticTyEnumValue { name, expr })
    }

    fn process_decl_ty_alias(
        &mut self,
        ctx: &TypealiasStatementContextAll<'_>,
    ) -> Result<ast::Decl> {
        let annotations = self.process_annotation_usage_list(ctx.annotationUsage_all())?;
        let ty_name =
            self.process_ty_identifier_as_qualified_ty_name(ctx.left.as_ref().unwrap())?;
        let ty_expr = self.process_ty_identifier_as_ty_expr(ctx.right.as_ref().unwrap())?;

        Ok(ast::Decl {
            id: self.libsl.decls.insert(()),
            loc: self.get_loc(&ctx.start(), &ctx.stop()),
            kind: ast::DeclTyAlias {
                annotations,
                ty_name,
                ty_expr,
            }
            .into(),
        })
    }

    fn process_decl_struct(&mut self, ctx: &TypeDefBlockContextAll<'_>) -> Result<ast::Decl> {
        let annotations = self.process_annotation_usage_list(ctx.annotationUsage_all())?;
        let ty_name =
            self.process_ty_identifier_as_qualified_ty_name(ctx.r#type.as_ref().unwrap())?;

        let (is_ty, for_tys) = if let Some(target_ty_ctx) = ctx.targetType() {
            (
                target_ty_ctx
                    .typeIdentifier()
                    .map(|t| self.process_ty_identifier_as_ty_expr(&t))
                    .transpose()?,
                target_ty_ctx
                    .typeList()
                    .unwrap()
                    .typeIdentifier_all()
                    .into_iter()
                    .map(|t| self.process_ty_identifier_as_ty_expr(&t))
                    .collect::<Result<Vec<_>>>()?,
            )
        } else {
            Default::default()
        };

        let ty_constraints = ctx
            .whereConstraints()
            .map(|c| self.process_where_constraints(&c))
            .transpose()?
            .unwrap_or_default();

        let decls = ctx
            .typeDefBlockStatement_all()
            .into_iter()
            .map(|stmt_ctx| {
                if let Some(decl) = stmt_ctx.variableDecl() {
                    self.process_decl_variable(&decl)
                } else if let Some(decl) = stmt_ctx.functionDecl() {
                    self.process_decl_function(&decl)
                } else {
                    panic!("unrecognized typeDefBlockStatement node: {stmt_ctx:?}");
                }
            })
            .collect::<Result<Vec<_>>>()?;

        Ok(ast::Decl {
            id: self.libsl.decls.insert(()),
            loc: self.get_loc(&ctx.start(), &ctx.stop()),
            kind: ast::DeclStruct {
                annotations,
                ty_name,
                is_ty,
                for_tys,
                ty_constraints,
                decls,
            }
            .into(),
        })
    }

    fn process_decl_enum(&mut self, ctx: &EnumBlockContextAll<'_>) -> Result<ast::Decl> {
        let annotations = self.process_annotation_usage_list(ctx.annotationUsage_all())?;
        let name =
            self.process_ty_identifier_as_qualified_ty_name(&ctx.typeIdentifier().unwrap())?;

        let variants = ctx
            .enumBlockStatement_all()
            .into_iter()
            .map(|e| self.process_enum_variant(&e))
            .collect::<Result<Vec<_>>>()?;

        Ok(ast::Decl {
            id: self.libsl.decls.insert(()),
            loc: self.get_loc(&ctx.start(), &ctx.stop()),
            kind: ast::DeclEnum {
                annotations,
                name,
                variants,
            }
            .into(),
        })
    }

    fn process_enum_variant(
        &mut self,
        ctx: &EnumBlockStatementContextAll<'_>,
    ) -> Result<ast::EnumVariant> {
        let name = self.process_identifier(&ctx.Identifier().unwrap())?;
        let value = self.process_integer_number(&ctx.integerNumber().unwrap())?;

        Ok(ast::EnumVariant { name, value })
    }

    fn process_decl_annotation(&mut self, ctx: &AnnotationDeclContextAll<'_>) -> Result<ast::Decl> {
        let name = self.process_identifier(&Terminal::new(ctx.name.clone().unwrap()))?;

        let params = ctx
            .annotationDeclParams()
            .into_iter()
            .flat_map(|l| l.annotationDeclParamsPart_all())
            .map(|param| {
                let (name, ty_expr) = self.process_name_with_ty(&param.nameWithType().unwrap())?;
                let default = param
                    .expression()
                    .map(|e| self.process_expr(&e))
                    .transpose()?;

                Ok(ast::AnnotationParam {
                    name,
                    ty_expr,
                    default,
                })
            })
            .collect::<Result<Vec<_>>>()?;

        Ok(ast::Decl {
            id: self.libsl.decls.insert(()),
            loc: self.get_loc(&ctx.start(), &ctx.stop()),
            kind: ast::DeclAnnotation { name, params }.into(),
        })
    }

    fn process_decl_action(&mut self, ctx: &ActionDeclContextAll<'_>) -> Result<ast::Decl> {
        let annotations = self.process_annotation_usage_list(ctx.annotationUsage_all())?;

        let generics = ctx
            .generic()
            .map(|g| self.process_generics(&g))
            .transpose()?
            .unwrap_or_default();

        let name = self.process_identifier(&Terminal::new(ctx.actionName.clone().unwrap()))?;

        let params = ctx
            .actionDeclParamList()
            .into_iter()
            .flat_map(|l| l.actionParameter_all())
            .map(|p| {
                let annotations = self.process_annotation_usage_list(p.annotationUsage_all())?;
                let name = self.process_identifier(&Terminal::new(p.name.clone().unwrap()))?;
                let ty_expr = self.process_ty_identifier_as_ty_expr(p.r#type.as_ref().unwrap())?;

                Ok(ast::ActionParam {
                    annotations,
                    name,
                    ty_expr,
                })
            })
            .collect::<Result<Vec<_>>>()?;

        let ret_ty_expr = ctx
            .actionType
            .as_ref()
            .map(|t| self.process_ty_identifier_as_ty_expr(t))
            .transpose()?;

        let ty_constraints = ctx
            .whereConstraints()
            .map(|c| self.process_where_constraints(&c))
            .transpose()?
            .unwrap_or_default();

        Ok(ast::Decl {
            id: self.libsl.decls.insert(()),
            loc: self.get_loc(&ctx.start(), &ctx.stop()),
            kind: ast::DeclAction {
                annotations,
                generics,
                name,
                params,
                ret_ty_expr,
                ty_constraints,
            }
            .into(),
        })
    }

    fn process_decl_automaton(&mut self, ctx: &AutomatonDeclContextAll<'_>) -> Result<ast::Decl> {
        todo!()
    }

    fn process_decl_function(&mut self, ctx: &FunctionDeclContextAll<'_>) -> Result<ast::Decl> {
        todo!()
    }

    fn process_decl_variable(&mut self, ctx: &VariableDeclContextAll<'_>) -> Result<ast::Decl> {
        todo!()
    }

    fn process_ty_expr(&mut self, ctx: &TypeExpressionContextAll<'_>) -> Result<ast::TyExpr> {
        todo!()
    }

    fn process_expr(&mut self, ctx: &ExpressionContextAll<'_>) -> Result<ast::Expr> {
        todo!()
    }

    fn process_expr_atomic(&mut self, ctx: &ExpressionAtomicContextAll<'_>) -> Result<ast::Expr> {
        todo!()
    }

    fn process_annotation_usage_list(
        &mut self,
        annotations: Vec<Rc<AnnotationUsageContextAll<'_>>>,
    ) -> Result<Vec<ast::Annotation>> {
        annotations
            .into_iter()
            .map(|a| self.process_annotation(&a))
            .collect()
    }

    fn process_annotation(
        &mut self,
        ctx: &AnnotationUsageContextAll<'_>,
    ) -> Result<ast::Annotation> {
        todo!()
    }

    fn process_ty_identifier_as_qualified_ty_name(
        &mut self,
        ctx: &TypeIdentifierContextAll<'_>,
    ) -> Result<ast::QualifiedTyName> {
        todo!()
    }

    fn process_identifier_as_qualified_ty_name(
        &mut self,
        ctx: &Terminal<'_>,
    ) -> Result<ast::QualifiedTyName> {
        todo!()
    }

    fn process_ty_identifier_as_ty_expr(
        &mut self,
        ctx: &TypeIdentifierContextAll<'_>,
    ) -> Result<ast::TyExpr> {
        todo!()
    }

    fn process_identifier(&mut self, ctx: &Terminal<'_>) -> Result<ast::Name> {
        todo!()
    }

    fn process_integer_number(&mut self, ctx: &IntegerNumberContextAll<'_>) -> Result<ast::IntLit> {
        todo!()
    }

    fn process_name_with_ty(
        &mut self,
        ctx: &NameWithTypeContextAll<'_>,
    ) -> Result<(ast::Name, ast::TyExpr)> {
        let name = self.process_identifier(&Terminal::new(ctx.name.clone().unwrap()))?;
        let ty_expr = self.process_ty_expr(&ctx.typeExpression().unwrap())?;

        Ok((name, ty_expr))
    }

    fn process_where_constraints(
        &mut self,
        ctx: &WhereConstraintsContextAll,
    ) -> Result<Vec<ast::TyConstraint>> {
        todo!()
    }

    fn process_generics(&mut self, ctx: &GenericContextAll<'_>) -> Result<Vec<ast::Generic>> {
        todo!()
    }
}
