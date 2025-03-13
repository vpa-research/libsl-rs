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
    ActionParameterContextAttrs, ActionUsageContextAll, ActionUsageContextAttrs,
    AnnotationDeclContextAll, AnnotationDeclContextAttrs, AnnotationDeclParamsContextAttrs,
    AnnotationDeclParamsPartContextAttrs, AnnotationUsageContextAll, ArgPairContextAttrs,
    ArrayLiteralContextAll, ArrayLiteralContextAttrs, AssignmentRightContextAttrs,
    AssignsContractContextAll, AssignsContractContextAttrs, AutomatonDeclContextAll,
    AutomatonDeclContextAttrs, AutomatonShiftDeclContextAll, AutomatonShiftDeclContextAttrs,
    AutomatonStateDeclContext, AutomatonStateDeclContextAttrs, AutomatonStatementContextAll,
    AutomatonStatementContextAttrs, BitShiftOpContextAttrs,
    CallAutomatonConstructorWithNamedArgsContextAll,
    CallAutomatonConstructorWithNamedArgsContextAttrs, ConstructorDeclContextAll,
    ConstructorDeclContextAttrs, ConstructorHeaderContextAttrs, ConstructorVariablesContextAll,
    ConstructorVariablesContextAttrs, DestructorDeclContextAll, DestructorDeclContextAttrs,
    DestructorHeaderContextAttrs, ElseStatementContextAttrs, EnsuresContractContextAll,
    EnsuresContractContextAttrs, EnumBlockContextAll, EnumBlockContextAttrs,
    EnumBlockStatementContextAll, EnumBlockStatementContextAttrs, EnumSemanticTypeContextAttrs,
    EnumSemanticTypeEntryContextAll, EnumSemanticTypeEntryContextAttrs, ExpressionAtomicContextAll,
    ExpressionAtomicContextAttrs, ExpressionContextAll, ExpressionContextAttrs,
    ExpressionsListContextAttrs, FileContextAttrs, FloatNumberContextAll, FunctionBodyContextAll,
    FunctionBodyContextAttrs, FunctionBodyStatementContextAll, FunctionBodyStatementContextAttrs,
    FunctionContractContextAll, FunctionContractContextAttrs, FunctionDeclArgListContextAll,
    FunctionDeclArgListContextAttrs, FunctionDeclContextAll, FunctionDeclContextAttrs,
    FunctionHeaderContextAttrs, FunctionsListContextAttrs, FunctionsListPartContextAll,
    FunctionsListPartContextAttrs, GenericContextAll, GlobalStatementContextAll,
    GlobalStatementContextAttrs, HasAutomatonConceptContextAll, HasAutomatonConceptContextAttrs,
    HeaderContextAll, IdentifierListContextAttrs, IfStatementContextAll, IfStatementContextAttrs,
    ImplementedConceptsContextAttrs, IntegerNumberContextAll, LibSLParserContextType,
    NameWithTypeContextAll, NameWithTypeContextAttrs, NamedArgsContextAttrs, ParameterContextAttrs,
    PeriodSeparatedFullNameContextAll, PrimitiveLiteralContextAll, PrimitiveLiteralContextAttrs,
    ProcDeclContextAll, ProcDeclContextAttrs, ProcHeaderContextAttrs, ProcUsageContextAll,
    ProcUsageContextAttrs, QualifiedAccessContextAll, RequiresContractContextAll,
    RequiresContractContextAttrs, SemanticTypeDeclContextAll, SemanticTypeDeclContextAttrs,
    SimpleSemanticTypeContextAttrs, TargetTypeContextAttrs, TopLevelDeclContextAttrs,
    TypeDefBlockContextAll, TypeDefBlockContextAttrs, TypeDefBlockStatementContextAttrs,
    TypeExpressionContextAll, TypeExpressionContextAttrs, TypeIdentifierContextAll,
    TypeIdentifierContextAttrs, TypeIdentifierNameContextAttrs, TypeListContextAttrs,
    TypealiasStatementContextAll, TypealiasStatementContextAttrs, TypesSectionContextAttrs,
    VariableAssignmentContextAll, VariableAssignmentContextAttrs, VariableDeclContextAll,
    VariableDeclContextAttrs, WhereConstraintsContextAll,
};
use crate::grammar::parser::{FileContextAll, LibSLParser};
use crate::loc::{Loc, Span};
use crate::{LibSl, ast, grammar};

pub type Result<T, E = ParseError> = std::result::Result<T, E>;

type Terminal<'a> = TerminalNode<'a, LibSLParserContextType>;

fn strip_surrounding(s: &str, prefix: char, suffix: char) -> &str {
    s.strip_prefix(prefix)
        .and_then(|s| s.strip_suffix(suffix))
        .unwrap_or(s)
}

fn hex_digit_to_u8(c: char) -> u8 {
    match c {
        '0'..='9' => c as u8 - '0' as u8,
        'a'..='f' => c as u8 - 'a' as u8,
        'A'..='F' => c as u8 - 'A' as u8,
        _ => panic!("not a hex digit: {c:?}"),
    }
}

fn parse_char_escape(s: &str) -> u32 {
    // assumes the backslash was already consumed.

    match s.chars().next().unwrap() {
        'b' => 0x08, // backspace.
        't' => '\t' as u32,
        'n' => '\n' as u32,
        'f' => 0x0c, // form feed.
        'r' => '\r' as u32,
        c @ ('"' | '\'' | '\\') => c as u32,

        // unicode escape.
        'u' => s[1..5]
            .chars()
            .fold(0, |acc, c| (acc << 8) | hex_digit_to_u8(c) as u32),

        // octal escape.
        '0'..='7' => s
            .chars()
            .take_while(|c| ('0'..='7').contains(c))
            .fold(0, |acc, c| (acc << 3) | (c as u32 - '0' as u32)),

        c => panic!("unrecognized escape sequence: \\{c}"),
    }
}

fn parse_string_lit(token: &CommonToken<'_>) -> String {
    // string literals allow only the \" escape sequence.
    strip_surrounding(&token.text, '"', '"').replace("\\\'", "\'")
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

fn unit_vec<T>(value: T) -> Vec<T> {
    vec![value]
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
        let value = self.process_int_lit(&ctx.integerNumber().unwrap())?;

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
        let annotations = self.process_annotation_usage_list(ctx.annotationUsage_all())?;
        let is_concept = ctx.CONCEPT().is_some();
        let name = self
            .process_period_separated_full_name_as_qualified_ty_name(ctx.name.as_ref().unwrap())?;

        let constructor_variables = ctx
            .constructorVariables_all()
            .into_iter()
            .map(|v| self.process_constructor_variable(&v))
            .collect::<Result<Vec<_>>>()?;

        let ty_expr = self.process_ty_expr(ctx.r#type.as_ref().unwrap())?;

        let mut implemented_concepts = vec![];

        for c in ctx.implementedConcepts_all() {
            let implements = c.implements.as_ref().unwrap();

            if !implements.text.eq_ignore_ascii_case("implements") {
                return Err(ParseError::SyntaxError {
                    line: implements.line,
                    column: implements.column,
                    msg: format!("expected 'implements', got '{}'", implements.text),
                });
            }

            for concept in c.concept_all() {
                implemented_concepts
                    .push(self.process_identifier(&Terminal::new(concept.name.clone().unwrap()))?);
            }
        }

        let mut decls = vec![];

        for d in ctx.automatonStatement_all() {
            decls.extend(self.process_automaton_decl(&d)?);
        }

        Ok(ast::Decl {
            id: self.libsl.decls.insert(()),
            loc: self.get_loc(&ctx.start(), &ctx.stop()),
            kind: ast::DeclAutomaton {
                annotations,
                is_concept,
                name,
                constructor_variables,
                ty_expr,
                implemented_concepts,
                decls,
            }
            .into(),
        })
    }

    fn process_constructor_variable(
        &mut self,
        ctx: &ConstructorVariablesContextAll<'_>,
    ) -> Result<ast::Decl> {
        let annotations = self.process_annotation_usage_list(ctx.annotationUsage_all())?;

        let kind = self.process_var_kind(ctx.keyword.as_ref().unwrap())?;
        let (name, ty_expr) = self.process_name_with_ty(&ctx.nameWithType().unwrap())?;

        let init = ctx
            .assignmentRight()
            .map(|e| self.process_expr(&e.expression().unwrap()))
            .transpose()?;

        Ok(ast::Decl {
            id: self.libsl.decls.insert(()),
            loc: self.get_loc(&ctx.start(), &ctx.stop()),
            kind: ast::DeclVariable {
                annotations,
                kind,
                name,
                ty_expr,
                init,
            }
            .into(),
        })
    }

    fn process_automaton_decl(
        &mut self,
        ctx: &AutomatonStatementContextAll<'_>,
    ) -> Result<Vec<ast::Decl>> {
        if let Some(decl) = ctx.automatonStateDecl() {
            self.process_decl_state(&decl)
        } else if let Some(decl) = ctx.automatonShiftDecl() {
            self.process_decl_shift(&decl).map(unit_vec)
        } else if let Some(decl) = ctx.constructorDecl() {
            self.process_decl_constructor(&decl).map(unit_vec)
        } else if let Some(decl) = ctx.destructorDecl() {
            self.process_decl_destructor(&decl).map(unit_vec)
        } else if let Some(decl) = ctx.procDecl() {
            self.process_decl_proc(&decl).map(unit_vec)
        } else if let Some(decl) = ctx.functionDecl() {
            self.process_decl_function(&decl).map(unit_vec)
        } else if let Some(decl) = ctx.variableDecl() {
            self.process_decl_variable(&decl).map(unit_vec)
        } else {
            panic!("unrecognized automatonStatement node: {ctx:?}");
        }
    }

    fn process_decl_function(&mut self, ctx: &FunctionDeclContextAll<'_>) -> Result<ast::Decl> {
        let header = ctx.functionHeader().unwrap();
        let annotations = self.process_annotation_usage_list(header.annotationUsage_all())?;

        let is_static = if let Some(modifier) = header.modifier.as_ref() {
            match &modifier.text {
                m if m.eq_ignore_ascii_case("static") => true,

                m => {
                    return Err(ParseError::SyntaxError {
                        line: modifier.line,
                        column: modifier.column,
                        msg: format!("unknown modifier `{m}`"),
                    });
                }
            }
        } else {
            false
        };

        let extension_for = header
            .automatonName
            .as_ref()
            .map(|n| self.process_period_separated_full_name(n))
            .transpose()?;

        let is_method = header.headerWithAsterisk().is_some();
        let name = self.process_identifier(&Terminal::new(header.functionName.clone().unwrap()))?;

        let generics = header
            .generic()
            .map(|g| self.process_generics(&g))
            .transpose()?
            .unwrap_or_default();

        let params = header
            .functionDeclArgList()
            .map(|a| self.process_function_params(&a))
            .transpose()?
            .unwrap_or_default();

        let ret_ty_expr = header
            .functionType
            .as_ref()
            .map(|t| self.process_ty_expr(t))
            .transpose()?;

        let ty_constraints = header
            .whereConstraints()
            .map(|w| self.process_where_constraints(&w))
            .transpose()?
            .unwrap_or_default();

        let body = ctx
            .functionBody()
            .map(|b| self.process_function_body(&b))
            .transpose()?;

        Ok(ast::Decl {
            id: self.libsl.decls.insert(()),
            loc: self.get_loc(&ctx.start(), &ctx.stop()),
            kind: ast::DeclFunction {
                annotations,
                is_static,
                extension_for,
                is_method,
                name,
                generics,
                params,
                ret_ty_expr,
                ty_constraints,
                body,
            }
            .into(),
        })
    }

    fn process_function_params(
        &mut self,
        ctx: &FunctionDeclArgListContextAll<'_>,
    ) -> Result<Vec<ast::FunctionParam>> {
        ctx.parameter_all()
            .into_iter()
            .map(|p| {
                let annotations = self.process_annotation_usage_list(p.annotationUsage_all())?;
                let name = self.process_identifier(&Terminal::new(p.name.clone().unwrap()))?;
                let ty_expr = self.process_ty_expr(&p.typeExpression().unwrap())?;

                Ok(ast::FunctionParam {
                    annotations,
                    name,
                    ty_expr,
                })
            })
            .collect()
    }

    fn process_decl_variable(&mut self, ctx: &VariableDeclContextAll<'_>) -> Result<ast::Decl> {
        let annotations = self.process_annotation_usage_list(ctx.annotationUsage_all())?;
        let kind = self.process_var_kind(ctx.keyword.as_ref().unwrap())?;
        let (name, ty_expr) = self.process_name_with_ty(&ctx.nameWithType().unwrap())?;
        let init = ctx
            .assignmentRight()
            .map(|e| self.process_expr(&e.expression().unwrap()))
            .transpose()?;

        Ok(ast::Decl {
            id: self.libsl.decls.insert(()),
            loc: self.get_loc(&ctx.start(), &ctx.stop()),
            kind: ast::DeclVariable {
                annotations,
                kind,
                name,
                ty_expr,
                init,
            }
            .into(),
        })
    }

    fn process_var_kind(&mut self, ctx: &CommonToken<'_>) -> Result<ast::VariableKind> {
        Ok(match ctx.token_type {
            grammar::parser::VAR => ast::VariableKind::Var,
            grammar::parser::VAL => ast::VariableKind::Val,
            _ => panic!("unrecognized variable keyword: `{}`", ctx.text),
        })
    }

    fn process_decl_state(
        &mut self,
        ctx: &AutomatonStateDeclContext<'_>,
    ) -> Result<Vec<ast::Decl>> {
        let kw = ctx.keyword.as_ref().unwrap();
        let kind = match kw.token_type {
            grammar::parser::INITSTATE => ast::StateKind::Initial,
            grammar::parser::STATE => ast::StateKind::Regular,
            grammar::parser::FINISHSTATE => ast::StateKind::Final,
            _ => panic!("unrecognized state kind: `{}`", kw.text),
        };

        ctx.identifierList()
            .into_iter()
            .flat_map(|l| l.Identifier_all())
            .map(|i| {
                self.process_identifier(&i).map(|name| ast::Decl {
                    id: self.libsl.decls.insert(()),
                    loc: name.loc.clone(),
                    kind: ast::DeclState { kind, name }.into(),
                })
            })
            .collect::<Result<Vec<_>>>()
    }

    fn process_decl_shift(&mut self, ctx: &AutomatonShiftDeclContextAll<'_>) -> Result<ast::Decl> {
        let from_token = ctx.from.as_ref().unwrap();

        let from = match from_token.token_type {
            grammar::parser::Identifier => {
                vec![self.process_identifier(&Terminal::new(from_token.clone()))?]
            }

            grammar::parser::L_BRACKET => ctx
                .identifierList()
                .unwrap()
                .Identifier_all()
                .into_iter()
                .map(|i| self.process_identifier(&i))
                .collect::<Result<Vec<_>>>()?,

            _ => panic!(
                "unrecognized token for `from` field in rule `automatonShiftDecl`: `{}`",
                from_token.text,
            ),
        };

        let to = self.process_identifier(&Terminal::new(ctx.to.clone().unwrap()))?;

        let by = if let Some(f) = ctx.functionsListPart() {
            vec![self.process_qualified_function_name(&f)?]
        } else {
            ctx.functionsList()
                .into_iter()
                .flat_map(|l| l.functionsListPart_all())
                .map(|f| self.process_qualified_function_name(&f))
                .collect::<Result<Vec<_>>>()?
        };

        Ok(ast::Decl {
            id: self.libsl.decls.insert(()),
            loc: self.get_loc(&ctx.start(), &ctx.stop()),
            kind: ast::DeclShift { from, to, by }.into(),
        })
    }

    fn process_qualified_function_name(
        &mut self,
        ctx: &FunctionsListPartContextAll<'_>,
    ) -> Result<ast::QualifiedFunctionName> {
        let name = self.process_identifier(&Terminal::new(ctx.name.clone().unwrap()))?;

        let params = if ctx.L_BRACKET().is_some() {
            Some(
                ctx.typeIdentifier_all()
                    .into_iter()
                    .map(|t| self.process_ty_identifier_as_ty_expr(&t))
                    .collect::<Result<Vec<_>>>()?,
            )
        } else {
            None
        };

        Ok(ast::QualifiedFunctionName { name, params })
    }

    fn process_decl_constructor(
        &mut self,
        ctx: &ConstructorDeclContextAll<'_>,
    ) -> Result<ast::Decl> {
        let header = ctx.constructorHeader().unwrap();
        let annotations = self.process_annotation_usage_list(header.annotationUsage_all())?;
        let is_method = header.headerWithAsterisk().is_some();

        let name = header
            .functionName
            .as_ref()
            .map(|n| self.process_identifier(&Terminal::new(n.clone())))
            .transpose()?;

        let params = header
            .functionDeclArgList()
            .map(|a| self.process_function_params(&a))
            .transpose()?
            .unwrap_or_default();

        let ret_ty_expr = header
            .functionType
            .as_ref()
            .map(|t| self.process_ty_identifier_as_ty_expr(t))
            .transpose()?;

        let body = ctx
            .functionBody()
            .map(|b| self.process_function_body(&b))
            .transpose()?;

        Ok(ast::Decl {
            id: self.libsl.decls.insert(()),
            loc: self.get_loc(&ctx.start(), &ctx.stop()),
            kind: ast::DeclConstructor {
                annotations,
                is_method,
                name,
                params,
                ret_ty_expr,
                body,
            }
            .into(),
        })
    }

    fn process_decl_destructor(&mut self, ctx: &DestructorDeclContextAll<'_>) -> Result<ast::Decl> {
        let header = ctx.destructorHeader().unwrap();
        let annotations = self.process_annotation_usage_list(header.annotationUsage_all())?;
        let is_method = header.headerWithAsterisk().is_some();

        let name = header
            .functionName
            .as_ref()
            .map(|n| self.process_identifier(&Terminal::new(n.clone())))
            .transpose()?;

        let params = header
            .functionDeclArgList()
            .map(|a| self.process_function_params(&a))
            .transpose()?
            .unwrap_or_default();

        let ret_ty_expr = header
            .functionType
            .as_ref()
            .map(|t| self.process_ty_identifier_as_ty_expr(t))
            .transpose()?;

        let body = ctx
            .functionBody()
            .map(|b| self.process_function_body(&b))
            .transpose()?;

        Ok(ast::Decl {
            id: self.libsl.decls.insert(()),
            loc: self.get_loc(&ctx.start(), &ctx.stop()),
            kind: ast::DeclDestructor {
                annotations,
                is_method,
                name,
                params,
                ret_ty_expr,
                body,
            }
            .into(),
        })
    }

    fn process_decl_proc(&mut self, ctx: &ProcDeclContextAll<'_>) -> Result<ast::Decl> {
        let header = ctx.procHeader().unwrap();
        let annotations = self.process_annotation_usage_list(header.annotationUsage_all())?;
        let is_method = header.headerWithAsterisk().is_some();
        let name = self.process_identifier(&Terminal::new(header.functionName.clone().unwrap()))?;

        let generics = header
            .generic()
            .map(|g| self.process_generics(&g))
            .transpose()?
            .unwrap_or_default();

        let params = header
            .functionDeclArgList()
            .map(|a| self.process_function_params(&a))
            .transpose()?
            .unwrap_or_default();

        let ret_ty_expr = header
            .functionType
            .as_ref()
            .map(|t| self.process_ty_expr(t))
            .transpose()?;

        let ty_constraints = header
            .whereConstraints()
            .map(|w| self.process_where_constraints(&w))
            .transpose()?
            .unwrap_or_default();

        let body = ctx
            .functionBody()
            .map(|b| self.process_function_body(&b))
            .transpose()?;

        Ok(ast::Decl {
            id: self.libsl.decls.insert(()),
            loc: self.get_loc(&ctx.start(), &ctx.stop()),
            kind: ast::DeclProc {
                annotations,
                is_method,
                name,
                generics,
                params,
                ret_ty_expr,
                ty_constraints,
                body,
            }
            .into(),
        })
    }

    fn process_function_body(
        &mut self,
        ctx: &FunctionBodyContextAll<'_>,
    ) -> Result<ast::FunctionBody> {
        let contracts = ctx
            .functionContract_all()
            .into_iter()
            .map(|c| self.process_contract(&c))
            .collect::<Result<Vec<_>>>()?;

        let stmts = ctx
            .functionBodyStatement_all()
            .into_iter()
            .map(|c| self.process_stmt(&c))
            .collect::<Result<Vec<_>>>()?;

        Ok(ast::FunctionBody { contracts, stmts })
    }

    fn process_contract(&mut self, ctx: &FunctionContractContextAll<'_>) -> Result<ast::Contract> {
        if let Some(ctx) = ctx.requiresContract() {
            self.process_contract_requires(&ctx)
        } else if let Some(ctx) = ctx.ensuresContract() {
            self.process_contract_ensures(&ctx)
        } else if let Some(ctx) = ctx.assignsContract() {
            self.process_contract_assigns(&ctx)
        } else {
            panic!("unrecognized functionContract node: {ctx:?}");
        }
    }

    fn process_contract_requires(
        &mut self,
        ctx: &RequiresContractContextAll<'_>,
    ) -> Result<ast::Contract> {
        let name = ctx
            .name
            .as_ref()
            .map(|i| self.process_identifier(&Terminal::new(i.clone())))
            .transpose()?;

        let expr = self.process_expr(&ctx.expression().unwrap())?;

        Ok(ast::ContractRequires { name, expr }.into())
    }

    fn process_contract_ensures(
        &mut self,
        ctx: &EnsuresContractContextAll<'_>,
    ) -> Result<ast::Contract> {
        let name = ctx
            .name
            .as_ref()
            .map(|i| self.process_identifier(&Terminal::new(i.clone())))
            .transpose()?;

        let expr = self.process_expr(&ctx.expression().unwrap())?;

        Ok(ast::ContractEnsures { name, expr }.into())
    }

    fn process_contract_assigns(
        &mut self,
        ctx: &AssignsContractContextAll<'_>,
    ) -> Result<ast::Contract> {
        let name = ctx
            .name
            .as_ref()
            .map(|i| self.process_identifier(&Terminal::new(i.clone())))
            .transpose()?;

        let expr = self.process_expr(&ctx.expression().unwrap())?;

        Ok(ast::ContractAssigns { name, expr }.into())
    }

    fn process_stmt(&mut self, ctx: &FunctionBodyStatementContextAll<'_>) -> Result<ast::Stmt> {
        if let Some(stmt) = ctx.variableAssignment() {
            self.process_stmt_assign(&stmt)
        } else if let Some(decl) = ctx.variableDecl() {
            self.process_stmt_decl_variable(&decl)
        } else if let Some(stmt) = ctx.ifStatement() {
            self.process_stmt_if(&stmt)
        } else if let Some(expr) = ctx.expression() {
            self.process_stmt_expr(&expr)
        } else {
            panic!("unrecognized funcionBodyStatement node: {ctx:?}");
        }
    }

    fn process_stmt_decl_variable(
        &mut self,
        ctx: &VariableDeclContextAll<'_>,
    ) -> Result<ast::Stmt> {
        let decl = self.process_decl_variable(ctx)?;

        Ok(ast::Stmt {
            id: self.libsl.stmts.insert(()),
            loc: self.get_loc(&ctx.start(), &ctx.stop()),
            kind: Box::new(decl).into(),
        })
    }

    fn process_stmt_if(&mut self, ctx: &IfStatementContextAll<'_>) -> Result<ast::Stmt> {
        let cond = self.process_expr(&ctx.expression().unwrap())?;

        let then_branch = ctx
            .functionBodyStatement_all()
            .into_iter()
            .map(|s| self.process_stmt(&s))
            .collect::<Result<Vec<_>>>()?;

        let else_branch = ctx
            .elseStatement()
            .into_iter()
            .flat_map(|e| e.functionBodyStatement_all())
            .map(|s| self.process_stmt(&s))
            .collect::<Result<Vec<_>>>()?;

        Ok(ast::Stmt {
            id: self.libsl.stmts.insert(()),
            loc: self.get_loc(&ctx.start(), &ctx.stop()),
            kind: ast::StmtIf {
                cond,
                then_branch,
                else_branch,
            }
            .into(),
        })
    }

    fn process_stmt_assign(&mut self, ctx: &VariableAssignmentContextAll<'_>) -> Result<ast::Stmt> {
        let lhs = self.process_qualified_access(&ctx.qualifiedAccess().unwrap())?;

        let op = ctx.op.as_ref().unwrap();
        let in_place_op = match op.token_type {
            grammar::parser::ASSIGN_OP => None,
            grammar::parser::PLUS_EQ => Some(ast::InPlaceOp::Add),
            grammar::parser::MINUS_EQ => Some(ast::InPlaceOp::Sub),
            grammar::parser::ASTERISK_EQ => Some(ast::InPlaceOp::Mul),
            grammar::parser::SLASH_EQ => Some(ast::InPlaceOp::Div),
            grammar::parser::PERCENT_EQ => Some(ast::InPlaceOp::Mod),
            grammar::parser::AMPERSAND_EQ => Some(ast::InPlaceOp::BitAnd),
            grammar::parser::OR_EQ => Some(ast::InPlaceOp::BitOr),
            grammar::parser::XOR_EQ => Some(ast::InPlaceOp::BitXor),
            grammar::parser::R_SHIFT_EQ => Some(ast::InPlaceOp::Sar),
            grammar::parser::L_SHIFT_EQ => Some(ast::InPlaceOp::Sal),
            _ => panic!("unrecognized assignment operator: `{}`", op.text),
        };

        let rhs = self.process_expr(&ctx.assignmentRight().unwrap().expression().unwrap())?;

        Ok(ast::Stmt {
            id: self.libsl.stmts.insert(()),
            loc: self.get_loc(&ctx.start(), &ctx.stop()),
            kind: ast::StmtAssign {
                lhs,
                in_place_op,
                rhs,
            }
            .into(),
        })
    }

    fn process_stmt_expr(&mut self, ctx: &ExpressionContextAll<'_>) -> Result<ast::Stmt> {
        let expr = self.process_expr(ctx)?;

        Ok(ast::Stmt {
            id: self.libsl.stmts.insert(()),
            loc: self.get_loc(&ctx.start(), &ctx.stop()),
            kind: expr.into(),
        })
    }

    fn process_ty_expr(&mut self, ctx: &TypeExpressionContextAll<'_>) -> Result<ast::TyExpr> {
        if let Some(ty) = ctx.typeIdentifier() {
            self.process_ty_identifier_as_ty_expr(&ty)
        } else if ctx.AMPERSAND().is_some() {
            let lhs = self.process_ty_expr(&ctx.typeExpression(0).unwrap())?;
            let rhs = self.process_ty_expr(&ctx.typeExpression(1).unwrap())?;

            Ok(ast::TyExpr {
                id: self.libsl.ty_exprs.insert(()),
                loc: self.get_loc(&ctx.start(), &ctx.stop()),
                kind: ast::TyExprIntersection {
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                }
                .into(),
            })
        } else if ctx.BIT_OR().is_some() {
            let lhs = self.process_ty_expr(&ctx.typeExpression(0).unwrap())?;
            let rhs = self.process_ty_expr(&ctx.typeExpression(1).unwrap())?;

            Ok(ast::TyExpr {
                id: self.libsl.ty_exprs.insert(()),
                loc: self.get_loc(&ctx.start(), &ctx.stop()),
                kind: ast::TyExprUnion {
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                }
                .into(),
            })
        } else {
            panic!("unrecognized typeExpression node: {ctx:?}");
        }
    }

    fn process_expr(&mut self, ctx: &ExpressionContextAll<'_>) -> Result<ast::Expr> {
        if let Some(expr) = ctx.expressionAtomic() {
            self.process_expr_atomic(&expr)
        } else if ctx.apostrophe.is_some() {
            self.process_expr_prev(ctx)
        } else if let Some(expr) = ctx.procUsage() {
            self.process_expr_proc_call(&expr)
        } else if let Some(expr) = ctx.actionUsage() {
            self.process_expr_action_call(&expr)
        } else if let Some(expr) = ctx.callAutomatonConstructorWithNamedArgs() {
            self.process_expr_instantiate(&expr)
        } else if ctx.lbracket.is_some() {
            self.process_expr(&ctx.expression(0).unwrap())
        } else if let Some(expr) = ctx.hasAutomatonConcept() {
            self.process_expr_has_concept(&expr)
        } else if ctx.unaryOp.is_some() {
            self.process_expr_unary(ctx)
        } else if ctx
            .typeOp
            .as_ref()
            .is_some_and(|token| token.token_type == grammar::parser::AS)
        {
            self.process_expr_cast(ctx)
        } else if ctx.op.is_some() {
            self.process_expr_binary(ctx)
        } else if ctx.bitShiftOp().is_some() {
            self.process_expr_shift(ctx)
        } else if ctx
            .typeOp
            .as_ref()
            .is_some_and(|token| token.token_type == grammar::parser::IS)
        {
            self.process_expr_ty_compare(ctx)
        } else {
            panic!("unrecognized expression node: {ctx:?}");
        }
    }

    fn process_expr_atomic(&mut self, ctx: &ExpressionAtomicContextAll<'_>) -> Result<ast::Expr> {
        if let Some(expr) = ctx.primitiveLiteral() {
            self.process_expr_primitive_lit(&expr)
        } else if let Some(expr) = ctx.arrayLiteral() {
            self.process_expr_array_lit(&expr)
        } else if let Some(expr) = ctx.qualifiedAccess() {
            self.process_expr_qualified_access(&expr)
        } else {
            panic!("unrecognized expressionAtomic node: {ctx:?}");
        }
    }

    fn process_expr_primitive_lit(
        &mut self,
        ctx: &PrimitiveLiteralContextAll<'_>,
    ) -> Result<ast::Expr> {
        let lit = self.process_primitive_lit(ctx)?;

        Ok(ast::Expr {
            id: self.libsl.exprs.insert(()),
            loc: self.get_loc(&ctx.start(), &ctx.stop()),
            kind: ast::ExprPrimitiveLit { lit }.into(),
        })
    }

    fn process_expr_array_lit(&mut self, ctx: &ArrayLiteralContextAll<'_>) -> Result<ast::Expr> {
        let elems = ctx
            .expressionsList()
            .into_iter()
            .flat_map(|e| e.expression_all())
            .map(|e| self.process_expr(&e))
            .collect::<Result<Vec<_>>>()?;

        Ok(ast::Expr {
            id: self.libsl.exprs.insert(()),
            loc: self.get_loc(&ctx.start(), &ctx.stop()),
            kind: ast::ExprArrayLit { elems }.into(),
        })
    }

    fn process_expr_qualified_access(
        &mut self,
        ctx: &QualifiedAccessContextAll<'_>,
    ) -> Result<ast::Expr> {
        let access = self.process_qualified_access(ctx)?;

        Ok(ast::Expr {
            id: self.libsl.exprs.insert(()),
            loc: self.get_loc(&ctx.start(), &ctx.stop()),
            kind: ast::ExprQualifiedAccess { access }.into(),
        })
    }

    fn process_expr_prev(&mut self, ctx: &ExpressionContextAll<'_>) -> Result<ast::Expr> {
        let access = self.process_qualified_access(&ctx.qualifiedAccess().unwrap())?;

        Ok(ast::Expr {
            id: self.libsl.exprs.insert(()),
            loc: self.get_loc(&ctx.start(), &ctx.stop()),
            kind: ast::ExprPrev { access }.into(),
        })
    }

    fn process_expr_proc_call(&mut self, ctx: &ProcUsageContextAll<'_>) -> Result<ast::Expr> {
        let callee = self.process_qualified_access(&ctx.qualifiedAccess().unwrap())?;

        let generics = ctx
            .generic()
            .map(|g| self.process_ty_args(&g))
            .transpose()?
            .unwrap_or_default();

        let args = ctx
            .expressionsList()
            .into_iter()
            .flat_map(|e| e.expression_all())
            .map(|e| self.process_expr(&e))
            .collect::<Result<Vec<_>>>()?;

        Ok(ast::Expr {
            id: self.libsl.exprs.insert(()),
            loc: self.get_loc(&ctx.start(), &ctx.stop()),
            kind: ast::ExprProcCall {
                callee,
                generics,
                args,
            }
            .into(),
        })
    }

    fn process_expr_action_call(&mut self, ctx: &ActionUsageContextAll<'_>) -> Result<ast::Expr> {
        let name = self.process_identifier(&ctx.Identifier().unwrap())?;
        let generics = ctx
            .generic()
            .map(|g| self.process_ty_args(&g))
            .transpose()?
            .unwrap_or_default();

        let args = ctx
            .expressionsList()
            .into_iter()
            .flat_map(|e| e.expression_all())
            .map(|e| self.process_expr(&e))
            .collect::<Result<Vec<_>>>()?;

        Ok(ast::Expr {
            id: self.libsl.exprs.insert(()),
            loc: self.get_loc(&ctx.start(), &ctx.stop()),
            kind: ast::ExprActionCall {
                name,
                generics,
                args,
            }
            .into(),
        })
    }

    fn process_expr_instantiate(
        &mut self,
        ctx: &CallAutomatonConstructorWithNamedArgsContextAll<'_>,
    ) -> Result<ast::Expr> {
        let name =
            self.process_period_separated_full_name(&ctx.periodSeparatedFullName().unwrap())?;

        let generics = ctx
            .generic()
            .map(|g| self.process_ty_args(&g))
            .transpose()?
            .unwrap_or_default();

        let args = ctx
            .namedArgs()
            .into_iter()
            .flat_map(|a| a.argPair_all())
            .map(|a| {
                Ok(if a.STATE().is_some() {
                    ast::ConstructorArg::State(
                        self.process_expr_atomic(&a.expressionAtomic().unwrap())?,
                    )
                } else if let Some(id) = a.Identifier() {
                    ast::ConstructorArg::Var(
                        self.process_identifier(&id)?,
                        self.process_expr(&a.expression().unwrap())?,
                    )
                } else {
                    panic!("unrecognized argPair node: {a:?}");
                })
            })
            .collect::<Result<Vec<_>>>()?;

        Ok(ast::Expr {
            id: self.libsl.exprs.insert(()),
            loc: self.get_loc(&ctx.start(), &ctx.stop()),
            kind: ast::ExprInstantiate {
                name,
                generics,
                args,
            }
            .into(),
        })
    }

    fn process_expr_has_concept(
        &mut self,
        ctx: &HasAutomatonConceptContextAll<'_>,
    ) -> Result<ast::Expr> {
        let scrutinee = self.process_qualified_access(&ctx.qualifiedAccess().unwrap())?;
        let has = ctx.has.as_ref().unwrap();

        if !has.text.eq_ignore_ascii_case("has") {
            return Err(ParseError::SyntaxError {
                line: has.line,
                column: has.column,
                msg: format!("expected 'has', got '{}'", has.text),
            });
        }

        let concept = self.process_identifier(&Terminal::new(ctx.name.clone().unwrap()))?;

        Ok(ast::Expr {
            id: self.libsl.exprs.insert(()),
            loc: self.get_loc(&ctx.start(), &ctx.stop()),
            kind: ast::ExprHasConcept { scrutinee, concept }.into(),
        })
    }

    fn process_expr_cast(&mut self, ctx: &ExpressionContextAll<'_>) -> Result<ast::Expr> {
        let expr = self.process_expr(&ctx.expression(0).unwrap())?;
        let ty_expr = self.process_ty_identifier_as_ty_expr(&ctx.typeIdentifier().unwrap())?;

        Ok(ast::Expr {
            id: self.libsl.exprs.insert(()),
            loc: self.get_loc(&ctx.start(), &ctx.stop()),
            kind: ast::ExprCast {
                expr: Box::new(expr),
                ty_expr,
            }
            .into(),
        })
    }

    fn process_expr_ty_compare(&mut self, ctx: &ExpressionContextAll<'_>) -> Result<ast::Expr> {
        let expr = self.process_expr(&ctx.expression(0).unwrap())?;
        let ty_expr = self.process_ty_identifier_as_ty_expr(&ctx.typeIdentifier().unwrap())?;

        Ok(ast::Expr {
            id: self.libsl.exprs.insert(()),
            loc: self.get_loc(&ctx.start(), &ctx.stop()),
            kind: ast::ExprTyCompare {
                expr: Box::new(expr),
                ty_expr,
            }
            .into(),
        })
    }

    fn process_expr_unary(&mut self, ctx: &ExpressionContextAll<'_>) -> Result<ast::Expr> {
        let op = ctx.unaryOp.as_ref().unwrap();

        let op = match op.token_type {
            grammar::parser::PLUS => ast::UnOp::Plus,
            grammar::parser::MINUS => ast::UnOp::Neg,
            grammar::parser::TILDE => ast::UnOp::BitNot,
            grammar::parser::EXCLAMATION => ast::UnOp::Not,
            _ => panic!("unrecognized unary operator: `{}`", op.text),
        };

        let expr = self.process_expr(&ctx.expression(0).unwrap())?;

        Ok(ast::Expr {
            id: self.libsl.exprs.insert(()),
            loc: self.get_loc(&ctx.start(), &ctx.stop()),
            kind: ast::ExprUnary {
                op,
                expr: Box::new(expr),
            }
            .into(),
        })
    }

    fn process_expr_shift(&mut self, ctx: &ExpressionContextAll<'_>) -> Result<ast::Expr> {
        let op_ctx = ctx.bitShiftOp().unwrap();

        let op = if op_ctx.lShift().is_some() {
            ast::BinOp::Sal
        } else if op_ctx.rShift().is_some() {
            ast::BinOp::Sar
        } else if op_ctx.uRShift().is_some() {
            ast::BinOp::Shl
        } else if op_ctx.uLShift().is_some() {
            ast::BinOp::Shr
        } else {
            panic!("unrecognized bitShiftOp node: {op_ctx:?}");
        };

        let lhs = self.process_expr(&ctx.expression(0).unwrap())?;
        let rhs = self.process_expr(&ctx.expression(1).unwrap())?;

        Ok(ast::Expr {
            id: self.libsl.exprs.insert(()),
            loc: self.get_loc(&ctx.start(), &ctx.stop()),
            kind: ast::ExprBinary {
                lhs: Box::new(lhs),
                op,
                rhs: Box::new(rhs),
            }
            .into(),
        })
    }

    fn process_expr_binary(&mut self, ctx: &ExpressionContextAll<'_>) -> Result<ast::Expr> {
        let op_ctx = ctx.op.as_ref().unwrap();

        let op = match op_ctx.token_type {
            grammar::parser::ASTERISK => ast::BinOp::Mul,
            grammar::parser::SLASH => ast::BinOp::Div,
            grammar::parser::PERCENT => ast::BinOp::Mod,
            grammar::parser::PLUS => ast::BinOp::Add,
            grammar::parser::MINUS => ast::BinOp::Sub,
            grammar::parser::L_ARROW => ast::BinOp::Lt,
            grammar::parser::R_ARROW => ast::BinOp::Gt,
            grammar::parser::L_ARROW_EQ => ast::BinOp::Le,
            grammar::parser::R_ARROW_EQ => ast::BinOp::Ge,
            grammar::parser::EQ => ast::BinOp::Eq,
            grammar::parser::EXCLAMATION_EQ => ast::BinOp::Ne,
            grammar::parser::BIT_OR => ast::BinOp::BitOr,
            grammar::parser::XOR => ast::BinOp::BitXor,
            grammar::parser::AMPERSAND => ast::BinOp::BitAnd,
            grammar::parser::LOGIC_OR => ast::BinOp::Or,
            grammar::parser::DOUBLE_AMPERSAND => ast::BinOp::And,
            _ => panic!("unrecognized binary expression operator: `{}`", op_ctx.text),
        };

        let lhs = self.process_expr(&ctx.expression(0).unwrap())?;
        let rhs = self.process_expr(&ctx.expression(1).unwrap())?;

        Ok(ast::Expr {
            id: self.libsl.exprs.insert(()),
            loc: self.get_loc(&ctx.start(), &ctx.stop()),
            kind: ast::ExprBinary {
                lhs: Box::new(lhs),
                op,
                rhs: Box::new(rhs),
            }
            .into(),
        })
    }

    fn process_primitive_lit(
        &mut self,
        ctx: &PrimitiveLiteralContextAll<'_>,
    ) -> Result<ast::PrimitiveLit> {
        if let Some(lit) = ctx.integerNumber() {
            Ok(self.process_int_lit(&lit)?.into())
        } else if let Some(lit) = ctx.floatNumber() {
            Ok(self.process_float_lit(&lit)?.into())
        } else if let Some(token) = ctx.DoubleQuotedString() {
            Ok(ast::PrimitiveLit::String(parse_string_lit(&token.symbol)))
        } else if let Some(token) = ctx.CHARACTER() {
            let s = strip_surrounding(&token.symbol.text, '\'', '\'');

            let c = if let Some(escape) = s.strip_prefix('\\') {
                parse_char_escape(escape)
            } else {
                s.chars().next().unwrap() as u32
            };

            Ok(ast::PrimitiveLit::Char(c))
        } else if let Some(token) = &ctx.bool {
            Ok(ast::PrimitiveLit::Bool(match token.token_type {
                grammar::parser::TRUE => true,
                grammar::parser::FALSE => false,
                _ => panic!("unrecognized boolean literal: `{}`", token.text),
            }))
        } else if ctx.nullLiteral.is_some() {
            Ok(ast::PrimitiveLit::Null)
        } else {
            panic!("unrecognized primitiveLiteral node: {ctx:?}");
        }
    }

    fn process_qualified_access(
        &mut self,
        ctx: &QualifiedAccessContextAll<'_>,
    ) -> Result<ast::QualifiedAccess> {
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
        let name_ctx = ctx.typeIdentifierName().unwrap();

        let ty_expr = if let Some(name_ctx) = name_ctx.periodSeparatedFullName() {
            let name = self.process_period_separated_full_name(&name_ctx)?;

            let generics = ctx
                .generic()
                .map(|g| self.process_ty_args(&g))
                .transpose()?
                .unwrap_or_default();

            ast::TyExpr {
                id: self.libsl.ty_exprs.insert(()),
                loc: self.get_loc(&name_ctx.start(), &ctx.stop()),
                kind: ast::TyExprName { name, generics }.into(),
            }
        } else if let Some(lit_ctx) = name_ctx.primitiveLiteral() {
            let lit = self.process_primitive_lit(&lit_ctx)?;

            if let Some(g) = ctx.generic() {
                return Err(ParseError::SyntaxError {
                    line: g.start().line,
                    column: g.start().column,
                    msg: "a primitive literal type expression cannot have type parameters".into(),
                });
            }

            ast::TyExpr {
                id: self.libsl.ty_exprs.insert(()),
                loc: self.get_loc(&name_ctx.start(), &lit_ctx.stop()),
                kind: ast::TyExprPrimitiveLit { lit }.into(),
            }
        } else {
            panic!("unrecognized typeIdentifierName node: {name_ctx:?}");
        };

        if let Some(token) = &ctx.asterisk {
            Ok(ast::TyExpr {
                id: self.libsl.ty_exprs.insert(()),
                loc: self.get_loc(token, &ctx.stop()),
                kind: ast::TyExprPointer {
                    base: Box::new(ty_expr),
                }
                .into(),
            })
        } else {
            Ok(ty_expr)
        }
    }

    fn process_period_separated_full_name(
        &mut self,
        ctx: &PeriodSeparatedFullNameContextAll<'_>,
    ) -> Result<ast::Name> {
        todo!()
    }

    fn process_period_separated_full_name_as_qualified_ty_name(
        &mut self,
        ctx: &PeriodSeparatedFullNameContextAll<'_>,
    ) -> Result<ast::QualifiedTyName> {
        todo!()
    }

    fn process_identifier(&mut self, ctx: &Terminal<'_>) -> Result<ast::Name> {
        todo!()
    }

    fn process_int_lit(&mut self, ctx: &IntegerNumberContextAll<'_>) -> Result<ast::IntLit> {
        todo!()
    }

    fn process_float_lit(&mut self, ctx: &FloatNumberContextAll<'_>) -> Result<ast::FloatLit> {
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

    fn process_ty_args(&mut self, ctx: &GenericContextAll<'_>) -> Result<Vec<ast::TyArg>> {
        todo!()
    }
}
