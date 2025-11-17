//! A parser working with a single file at a time.

use std::cell::RefCell;
use std::error::Error;
use std::fmt::{self, Debug, Display};
use std::num::{NonZeroUsize, ParseIntError};
use std::rc::Rc;

use antlr_rust::common_token_stream::CommonTokenStream;
use antlr_rust::error_listener::ErrorListener;
use antlr_rust::errors::ANTLRError;
use antlr_rust::parser_rule_context::ParserRuleContext;
use antlr_rust::token::CommonToken;
use antlr_rust::token_factory::TokenFactory;
use antlr_rust::tree::{ParseTree, TerminalNode};
use antlr_rust::{InputStream, Parser};

use crate::grammar::lexer::LibSLLexer;
use crate::grammar::parser::{
    AccessAutomatonFieldContext, AccessAutomatonFieldContextAttrs, AccessContextAll,
    AccessFieldContext, AccessIndexContext, AccessNameContext, ActionCallExprContextAll,
    ActionDeclContextAll, ActionParamContextAll, AddBinOpContextAll, AnnotationArgContextAll,
    AnnotationContextAll, AnnotationDeclContextAll, AnnotationParamContextAll,
    ArrayLitExprContextAll, AssignOpContextAll, AssignStmtContextAll, AssignsContractContextAll,
    AtomicExprAccessContext, AtomicExprAccessContextAttrs, AtomicExprArrayLitContextAttrs,
    AtomicExprContextAll, AtomicExprPrimitiveLitContext, AtomicExprSetLitContextAttrs,
    AtomicExprSignedNumLitContext, AtomicExprSignedNumLitContextAttrs, AutomatonDeclContextAll,
    AutomatonDefDeclConstructorContextAttrs, AutomatonDefDeclContextAll,
    AutomatonDefDeclDestructorContextAttrs, AutomatonDefDeclFunctionContextAttrs,
    AutomatonDefDeclProcContextAttrs, AutomatonDefDeclShiftContextAttrs,
    AutomatonDefDeclStateContextAttrs, AutomatonDefDeclVariableContextAttrs, BitShiftOpContextAll,
    BlockContextAll, BlockLoneStmtContextAttrs, BlockPredicateContextAll, CancelStmtContextAll,
    ConstructorArgContextAll, ConstructorDeclContextAll, ConstructorVariableContextAll,
    ContractAssignsContextAttrs, ContractContextAll, ContractEnsuresContextAttrs,
    ContractPredicateBlockContextAttrs, ContractPredicateContextAll,
    ContractPredicateExprContextAttrs, ContractPredicateIfContextAttrs,
    ContractRequiresContextAttrs, DestructorDeclContextAll, EnsuresContractContextAll,
    EnumDeclContextAll, EnumDeclVariantContextAll, EnumSemanticTypeValueContextAll,
    ExprAccessContext, ExprAccessContextAttrs, ExprActionCallContextAttrs, ExprAdditiveContext,
    ExprAndContext, ExprArrayLitContextAttrs, ExprBitAndContext, ExprBitOrContext,
    ExprBitXorContext, ExprCastContext, ExprContextAll, ExprHasConceptContext,
    ExprInstantiationContextAttrs, ExprMultiplicativeContext, ExprOrContext,
    ExprPredicateBlockContextAttrs, ExprPredicateContextAll, ExprPredicateExprContextAttrs,
    ExprPrevContext, ExprPrimitiveLitContext, ExprPrimitiveLitContextAttrs,
    ExprProcCallContextAttrs, ExprRelationalContext, ExprSetLitContextAttrs, ExprShiftContext,
    ExprTypeComparisonContext, ExprUnaryContext, FileContextAll, FileContextAttrs,
    FullNameContextAll, FunctionBodyContextAll, FunctionDeclContextAll,
    FunctionDefBracedContextAttrs, FunctionDefContextAll, FunctionModifierContextAll,
    FunctionParamContextAll, FunctionSignatureContextAll, GenericContextAll, GenericsContextAll,
    GlobalDeclActionContextAttrs, GlobalDeclAnnotationContextAttrs,
    GlobalDeclAutomatonContextAttrs, GlobalDeclContextAll, GlobalDeclEnumContextAttrs,
    GlobalDeclFunctionContextAttrs, GlobalDeclImportContextAttrs, GlobalDeclIncludeContextAttrs,
    GlobalDeclProcContextAttrs, GlobalDeclSemanticTypeSectionContextAttrs,
    GlobalDeclStructContextAttrs, GlobalDeclTypeAliasContextAttrs, GlobalDeclVariableContextAttrs,
    HeaderContextAll, IdentContextAll, IfPredicateContextAll, IfStmtContextAll,
    ImportDeclContextAll, ImportDeclContextAttrs, IncludeDeclContextAll, IncludeDeclContextAttrs,
    InstantiationExprContextAll, LibSLParser, LibSLParserContextType, MulBinOpContextAll,
    NameTypeExprContextAll, PathBareContextAttrs, PathContextAll, PathStringLitContextAttrs,
    PointerTypeExprContextAll, PredicateBlockContextAttrs, PredicateContextAll,
    PredicateExprContextAttrs, PredicateIfContextAttrs, PredicateNamedContext,
    PredicateNamedContextAttrs, PredicateVariableDeclContextAttrs, PrimitiveLitCharContextAttrs,
    PrimitiveLitContextAll, PrimitiveLitFloatContextAttrs, PrimitiveLitIntContextAttrs,
    PrimitiveLitStringLitContextAttrs, ProcCallExprContextAll, ProcDeclContextAll,
    ProcModifierContextAll, QualifiedTypeNameContextAll, RelOpContextAll,
    RequiresContractContextAll, SemanticTypeDeclContextAll, SemanticTypeDeclContextAttrs,
    SemanticTypeDefContextAll, SetLitExprContextAll, ShiftByContextAll, ShiftDeclContextAll,
    ShiftSourceStateContextAll, ShiftSourceStateShorthandContextAttrs, SignContextAll,
    SignedIntLitContextAll, SignedIntLitContextAttrs, SignedNumLitContextAll,
    SignedNumLitFloatContextAttrs, SignedNumLitIntContextAttrs, StateDeclContextAll,
    StateKindContextAll, StmtAssignContextAttrs, StmtCancelContextAttrs, StmtContextAll,
    StmtExprContext, StmtIfContextAttrs, StmtVariableDeclContext, StmtVariableDeclContextAttrs,
    StructDeclContextAll, StructDefDeclContextAll, StructDefDeclFunctionContextAttrs,
    StructDefDeclVariableContextAttrs, TypeAliasDeclContextAll, TypeArgContextAll,
    TypeArgSpecContextAll, TypeArgTypeExprContextAttrs, TypeConstraintContextAll,
    TypeExprContextAll, TypeExprIntersectionContext, TypeExprNameContextAttrs,
    TypeExprPointerContextAttrs, TypeExprPrimitiveLitContext, TypeExprUnionContext, UnOpContextAll,
    VariableDeclContextAll, VariableKindContextAll, VarianceSpecContextAll, WhereClauseContextAll,
};
use crate::loc::{Loc, Span};
use crate::{AccessId, DeclId, ExprId, FileId, LibSl, PredId, StmtId, TyExprId, ast, grammar};

type Result<T, E = ParseError> = std::result::Result<T, E>;

type Terminal<'a> = TerminalNode<'a, LibSLParserContextType>;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Sign {
    Plus,
    Minus,
}

fn strip_surrounding(s: &str, prefix: char, suffix: char) -> &str {
    s.strip_prefix(prefix)
        .and_then(|s| s.strip_suffix(suffix))
        .unwrap_or(s)
}

fn hex_digit_to_u8(c: char) -> u8 {
    match c {
        '0'..='9' => c as u8 - b'0',
        'a'..='f' => c as u8 - b'a' + 10,
        'A'..='F' => c as u8 - b'A' + 10,
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
            .fold(0, |acc, c| (acc << 4) | hex_digit_to_u8(c) as u32),

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

fn parse_ident(ctx: &IdentContextAll<'_>) -> String {
    strip_surrounding(&ctx.get_text(), '`', '`').into()
}

/// The radix of an integer literal.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Radix {
    /// Binary (`0b` prefix).
    Binary,

    /// Octal (`0` prefix).
    Octal,

    /// Decimal (no prefix).
    Decimal,

    /// Hexadecimal (`0x` prefix).
    Hexadecimal,
}

impl Display for Radix {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Radix::Binary => write!(f, "binary"),
            Radix::Octal => write!(f, "octal"),
            Radix::Decimal => write!(f, "decimal"),
            Radix::Hexadecimal => write!(f, "hexadecimal"),
        }
    }
}

impl From<Radix> for u32 {
    fn from(radix: Radix) -> Self {
        match radix {
            Radix::Binary => 2,
            Radix::Octal => 8,
            Radix::Decimal => 10,
            Radix::Hexadecimal => 16,
        }
    }
}

fn parse_line_or_col(number: isize) -> Option<NonZeroUsize> {
    if number > 0 {
        Some(NonZeroUsize::new(number as usize).unwrap())
    } else {
        None
    }
}

fn fmt_line_col(line: Option<NonZeroUsize>, col: Option<NonZeroUsize>) -> impl Display {
    struct Fmt {
        line: Option<NonZeroUsize>,
        column: Option<NonZeroUsize>,
    }

    impl Display for Fmt {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match (self.line, self.column) {
                (Some(line), Some(column)) => write!(f, "L{line}:{column}"),
                (Some(line), None) => write!(f, "L{line}"),
                (None, Some(column)) => write!(f, "L<unknown>:{column}"),
                (None, None) => write!(f, "<unknown>"),
            }
        }
    }

    Fmt { line, column: col }
}

/// An error that occurred while parsing a file.
#[derive(Debug, Clone)]
pub enum ParseError {
    /// A syntax error.
    Syntax {
        /// The identifier of the file being parsed.
        file_id: FileId,

        /// The line number (1-based) this error occurred in.
        line: Option<NonZeroUsize>,

        /// The column number (1-based) this error occurred in.
        col: Option<NonZeroUsize>,

        /// The error message.
        msg: String,
    },

    /// Could not parse an integer literal.
    Int {
        /// The radix of the integer literal.
        radix: Radix,

        /// The identifier of the file being parsed.
        file_id: FileId,

        /// The line number (1-based) this error occurred in.
        line: Option<NonZeroUsize>,

        /// The column number (1-based) this error occurred in.
        col: Option<NonZeroUsize>,

        /// The underlying error.
        inner: ParseIntError,
    },
}

impl ParseError {
    /// Returns the identifier of the file that caused this error.
    pub fn file_id(&self) -> FileId {
        match *self {
            Self::Syntax { file_id, .. } => file_id,
            Self::Int { file_id, .. } => file_id,
        }
    }
}

impl Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParseError::Syntax { line, col, msg, .. } => {
                write!(
                    f,
                    "encountered a syntax error at {loc}: {msg}",
                    loc = fmt_line_col(*line, *col),
                )
            }

            ParseError::Int {
                radix,
                line,
                col,
                inner,
                ..
            } => write!(
                f,
                "could not parse {radix_article} {radix} integer literal at {loc}: {inner}",
                radix_article = match radix {
                    Radix::Octal => "an",
                    _ => "a",
                },
                loc = fmt_line_col(*line, *col),
            ),
        }
    }
}

impl Error for ParseError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            ParseError::Syntax { .. } => None,
            ParseError::Int { inner, .. } => Some(inner),
        }
    }
}

#[derive(Debug, Clone)]
struct ErrorCollector {
    errors: Rc<RefCell<Vec<ParseError>>>,
    file_id: FileId,
}

impl ErrorCollector {
    fn new(file_id: FileId) -> (Self, Rc<RefCell<Vec<ParseError>>>) {
        let errors: Rc<RefCell<Vec<ParseError>>> = Default::default();

        (
            Self {
                errors: errors.clone(),
                file_id,
            },
            errors,
        )
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
        self.errors.borrow_mut().push(ParseError::Syntax {
            line: parse_line_or_col(line),
            col: parse_line_or_col(column),
            msg: msg.into(),
            file_id: self.file_id,
        });
    }
}

impl LibSl {
    /// Parses the `contents` as a LibSL file with the given name.
    ///
    /// If the file has syntax errors, returns an `Err(ParseError)`.
    ///
    /// The name is treated opaquely and only used for emitting diagnostic messages. It can, but
    /// does not have to, be a file path.
    ///
    /// Note that loading the same file twice, even with the same file name, means you'll get two
    /// distinct [`ast::File`]s back. They will be treated as if they were different files whose
    /// contents that just happened to be same. For this reason this method is **not**
    /// an appropriate choice for resolving imports unless you implement deduplication and file name
    /// canonicalization.
    pub fn parse_file(&mut self, file_name: String, contents: &str) -> Result<FileId, ParseError> {
        let ctor = AstConstructor::new(self, file_name.clone());
        let file_id = ctor.file_id;

        let input_stream = InputStream::new(contents);
        let lexer = LibSLLexer::new(input_stream);
        let token_stream = CommonTokenStream::new(lexer);
        let mut parser = LibSLParser::new(token_stream);
        parser.remove_error_listeners();
        let (error_listener, errors) = ErrorCollector::new(file_id);
        parser.add_error_listener(Box::new(error_listener));

        let tree = match parser.file() {
            Ok(tree) if errors.borrow().is_empty() => tree,

            Ok(_) => {
                return Err(errors.borrow_mut().swap_remove(0));
            }

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

        let file = ctor.construct(&tree)?;
        self.files[file_id] = file;

        Ok(file_id)
    }
}

struct AstConstructor<'a> {
    libsl: &'a mut LibSl,
    file_id: FileId,
}

impl<'a> AstConstructor<'a> {
    fn new(libsl: &'a mut LibSl, file_name: String) -> Self {
        let file_id = libsl.files.insert(Default::default());
        libsl.file_names.insert(file_id, file_name);

        Self { libsl, file_id }
    }

    fn get_loc(&self, start: &CommonToken<'_>, stop: &CommonToken<'_>) -> Loc {
        let line = parse_line_or_col(start.line);
        let col = parse_line_or_col(start.column);

        Span {
            start: start.start as usize,
            len: usize::try_from(stop.stop)
                .ok()
                .and_then(|stop| Some(stop.saturating_sub(start.start.try_into().ok()?)))
                .unwrap_or(0),
            file_id: self.file_id,
            line,
            col,
        }
        .into()
    }

    fn construct(mut self, ctx: &FileContextAll<'_>) -> Result<ast::File> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());
        let header = ctx
            .header()
            .map(|header| self.process_header(&header))
            .transpose()?;

        let mut decls = Vec::with_capacity(ctx.decls.len());

        for ctx in &ctx.decls {
            decls.extend(self.process_global_decl(ctx)?);
        }

        Ok(ast::File { loc, header, decls })
    }

    fn process_header(&mut self, ctx: &HeaderContextAll<'_>) -> Result<ast::Header> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());
        let libsl_version = parse_string_lit(ctx.libslVersion.as_ref().unwrap());
        let library_name = parse_ident(ctx.libraryName.as_ref().unwrap());
        let version = ctx.version.as_ref().map(|t| parse_string_lit(t));
        let language = ctx.language.as_ref().map(|t| parse_string_lit(t));
        let url = ctx.url.as_ref().map(|t| parse_string_lit(t));

        Ok(ast::Header {
            loc,
            libsl_version,
            library_name,
            version,
            language,
            url,
        })
    }

    fn process_global_decl(&mut self, ctx: &GlobalDeclContextAll<'_>) -> Result<Vec<DeclId>> {
        Ok(match ctx {
            GlobalDeclContextAll::GlobalDeclImportContext(ctx) => {
                vec![self.process_import_decl(&ctx.importDecl().unwrap())?]
            }

            GlobalDeclContextAll::GlobalDeclIncludeContext(ctx) => {
                vec![self.process_include_decl(&ctx.includeDecl().unwrap())?]
            }

            GlobalDeclContextAll::GlobalDeclSemanticTypeSectionContext(ctx) => ctx
                .semanticTypeSectionDecl()
                .unwrap()
                .decls
                .iter()
                .map(|ctx| self.process_semantic_type_decl(ctx))
                .collect::<Result<_>>()?,

            GlobalDeclContextAll::GlobalDeclTypeAliasContext(ctx) => {
                vec![self.process_type_alias_decl(&ctx.typeAliasDecl().unwrap())?]
            }

            GlobalDeclContextAll::GlobalDeclStructContext(ctx) => {
                vec![self.process_struct_decl(&ctx.structDecl().unwrap())?]
            }

            GlobalDeclContextAll::GlobalDeclEnumContext(ctx) => {
                vec![self.process_enum_decl(&ctx.enumDecl().unwrap())?]
            }

            GlobalDeclContextAll::GlobalDeclAnnotationContext(ctx) => {
                vec![self.process_annotation_decl(&ctx.annotationDecl().unwrap())?]
            }

            GlobalDeclContextAll::GlobalDeclActionContext(ctx) => {
                vec![self.process_action_decl(&ctx.actionDecl().unwrap())?]
            }

            GlobalDeclContextAll::GlobalDeclAutomatonContext(ctx) => {
                vec![self.process_automaton_decl(&ctx.automatonDecl().unwrap())?]
            }

            GlobalDeclContextAll::GlobalDeclFunctionContext(ctx) => {
                vec![self.process_function_decl(&ctx.functionDecl().unwrap())?]
            }

            GlobalDeclContextAll::GlobalDeclProcContext(ctx) => {
                vec![self.process_proc_decl(&ctx.procDecl().unwrap())?]
            }

            GlobalDeclContextAll::GlobalDeclVariableContext(ctx) => {
                vec![self.process_variable_decl(&ctx.variableDecl().unwrap())?]
            }

            GlobalDeclContextAll::Error(_) => unreachable!(),
        })
    }

    fn process_import_decl(&mut self, ctx: &ImportDeclContextAll<'_>) -> Result<DeclId> {
        let path = self.process_path(&ctx.path().unwrap());
        let loc = self.get_loc(&ctx.start(), &ctx.stop());

        Ok(self.libsl.decls.insert_with_key(|id| ast::Decl {
            id,
            loc,
            kind: ast::DeclImport { path }.into(),
        }))
    }

    fn process_include_decl(&mut self, ctx: &IncludeDeclContextAll<'_>) -> Result<DeclId> {
        let path = self.process_path(&ctx.path().unwrap());
        let loc = self.get_loc(&ctx.start(), &ctx.stop());

        Ok(self.libsl.decls.insert_with_key(|id| ast::Decl {
            id,
            loc,
            kind: ast::DeclInclude { path }.into(),
        }))
    }

    fn process_path(&mut self, ctx: &PathContextAll<'_>) -> String {
        match ctx {
            PathContextAll::PathStringLitContext(ctx) => {
                parse_string_lit(&ctx.StringLit().unwrap().symbol)
            }

            PathContextAll::PathBareContext(ctx) => ctx.BarePath().unwrap().symbol.text.to_string(),

            PathContextAll::Error(_) => unreachable!(),
        }
    }

    fn process_semantic_type_decl(
        &mut self,
        ctx: &SemanticTypeDeclContextAll<'_>,
    ) -> Result<DeclId> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());
        let annotations = self.process_annotations(&ctx.annotations)?;
        let ty_name = self.process_qualified_type_name(ctx.typeName.as_ref().unwrap())?;
        let real_ty = self.process_type_expr(ctx.realType.as_ref().unwrap())?;

        let kind = match &*ctx.semanticTypeDef().unwrap() {
            SemanticTypeDefContextAll::SemanticTypeDefSimpleContext(_) => {
                ast::SemanticTyKind::Simple
            }

            SemanticTypeDefContextAll::SemanticTypeDefEnumContext(ctx) => {
                ast::SemanticTyKind::Enumerated(
                    ctx.values
                        .iter()
                        .map(|ctx| self.process_enum_semantic_type_value(ctx))
                        .collect::<Result<_>>()?,
                )
            }

            SemanticTypeDefContextAll::Error(_) => unreachable!(),
        };

        Ok(self.libsl.decls.insert_with_key(|id| ast::Decl {
            id,
            loc,
            kind: ast::DeclSemanticTy {
                annotations,
                ty_name,
                real_ty,
                kind,
            }
            .into(),
        }))
    }

    fn process_enum_semantic_type_value(
        &mut self,
        ctx: &EnumSemanticTypeValueContextAll<'_>,
    ) -> Result<ast::SemanticTyEnumValue> {
        let name = self.process_name(ctx.name.as_ref().unwrap());
        let expr = self.process_atomic_expr(ctx.value.as_ref().unwrap())?;

        Ok(ast::SemanticTyEnumValue { name, expr })
    }

    fn process_type_alias_decl(&mut self, ctx: &TypeAliasDeclContextAll<'_>) -> Result<DeclId> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());
        let annotations = self.process_annotations(&ctx.annotations)?;
        let ty_name = self.process_qualified_type_name(ctx.typeName.as_ref().unwrap())?;
        let ty_expr = self.process_type_expr(ctx.def.as_ref().unwrap())?;

        Ok(self.libsl.decls.insert_with_key(|id| ast::Decl {
            id,
            loc,
            kind: ast::DeclTyAlias {
                annotations,
                ty_name,
                ty_expr,
            }
            .into(),
        }))
    }

    fn process_struct_decl(&mut self, ctx: &StructDeclContextAll<'_>) -> Result<DeclId> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());
        let annotations = self.process_annotations(&ctx.annotations)?;
        let ty_name = self.process_qualified_type_name(ctx.typeName.as_ref().unwrap())?;

        let (is_ty, for_tys) = match &ctx.targetType {
            Some(ctx) => (
                ctx.isType
                    .as_ref()
                    .map(|ctx| self.process_type_expr(ctx))
                    .transpose()?,
                ctx.forTypes
                    .as_ref()
                    .unwrap()
                    .typeExprs
                    .iter()
                    .map(|ctx| self.process_type_expr(ctx))
                    .collect::<Result<_>>()?,
            ),

            None => (None, vec![]),
        };

        let ty_constraints = ctx
            .typeConstraints
            .as_ref()
            .map(|ctx| self.process_where_clause(ctx))
            .transpose()?
            .unwrap_or_default();

        let decls = ctx
            .decls
            .iter()
            .map(|ctx| match &**ctx {
                StructDefDeclContextAll::StructDefDeclVariableContext(ctx) => {
                    self.process_variable_decl(&ctx.variableDecl().unwrap())
                }

                StructDefDeclContextAll::StructDefDeclFunctionContext(ctx) => {
                    self.process_function_decl(&ctx.functionDecl().unwrap())
                }

                StructDefDeclContextAll::Error(_) => unreachable!(),
            })
            .collect::<Result<_>>()?;

        Ok(self.libsl.decls.insert_with_key(|id| ast::Decl {
            id,
            loc,
            kind: ast::DeclStruct {
                annotations,
                ty_name,
                is_ty,
                for_tys,
                ty_constraints,
                decls,
            }
            .into(),
        }))
    }

    fn process_enum_decl(&mut self, ctx: &EnumDeclContextAll<'_>) -> Result<DeclId> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());
        let annotations = self.process_annotations(&ctx.annotations)?;
        let ty_name = self.process_qualified_type_name(ctx.typeName.as_ref().unwrap())?;
        let variants = ctx
            .variants
            .iter()
            .map(|ctx| self.process_enum_decl_variant(ctx))
            .collect::<Result<_>>()?;

        Ok(self.libsl.decls.insert_with_key(|id| ast::Decl {
            id,
            loc,
            kind: ast::DeclEnum {
                annotations,
                ty_name,
                variants,
            }
            .into(),
        }))
    }

    fn process_enum_decl_variant(
        &mut self,
        ctx: &EnumDeclVariantContextAll<'_>,
    ) -> Result<ast::EnumVariant> {
        let name = self.process_name(ctx.name.as_ref().unwrap());
        let value = self.process_signed_int_lit(ctx.value.as_ref().unwrap())?;

        Ok(ast::EnumVariant { name, value })
    }

    fn process_signed_int_lit(&mut self, ctx: &SignedIntLitContextAll<'_>) -> Result<ast::IntLit> {
        let sign = self.process_sign(&ctx.sign().unwrap());

        self.process_integer_lit(sign, &ctx.IntegerLit().unwrap())
    }

    fn process_sign(&mut self, ctx: &SignContextAll<'_>) -> Sign {
        match ctx {
            SignContextAll::PlusSignContext(_) => Sign::Plus,
            SignContextAll::MinusSignContext(_) => Sign::Minus,
            SignContextAll::Error(_) => unreachable!(),
        }
    }

    fn process_annotation_decl(&mut self, ctx: &AnnotationDeclContextAll<'_>) -> Result<DeclId> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());
        let name = self.process_name(ctx.name.as_ref().unwrap());
        let params = ctx
            .params
            .as_ref()
            .map(|ctx| {
                ctx.params
                    .iter()
                    .map(|ctx| self.process_annotation_param(ctx))
                    .collect::<Result<_>>()
            })
            .transpose()?
            .unwrap_or_default();

        Ok(self.libsl.decls.insert_with_key(|id| ast::Decl {
            id,
            loc,
            kind: ast::DeclAnnotation { name, params }.into(),
        }))
    }

    fn process_annotation_param(
        &mut self,
        ctx: &AnnotationParamContextAll<'_>,
    ) -> Result<ast::AnnotationParam> {
        let name = self.process_name(ctx.name.as_ref().unwrap());
        let ty_expr = self.process_type_expr(ctx.r#type.as_ref().unwrap())?;
        let default = ctx
            .default
            .as_ref()
            .map(|ctx| self.process_expr(ctx))
            .transpose()?;

        Ok(ast::AnnotationParam {
            name,
            ty_expr,
            default,
        })
    }

    fn process_action_decl(&mut self, ctx: &ActionDeclContextAll<'_>) -> Result<DeclId> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());
        let annotations = self.process_annotations(&ctx.annotations)?;
        let name = self.process_name(ctx.name.as_ref().unwrap());

        let generics = ctx
            .typeParams
            .as_ref()
            .map(|ctx| self.process_generics(ctx))
            .unwrap_or_default();

        let params = ctx
            .params
            .as_ref()
            .map(|ctx| {
                ctx.params
                    .iter()
                    .map(|ctx| self.process_action_param(ctx))
                    .collect::<Result<_>>()
            })
            .transpose()?
            .unwrap_or_default();

        let ret_ty_expr = ctx
            .retType
            .as_ref()
            .map(|ctx| self.process_type_expr(ctx))
            .transpose()?;

        let ty_constraints = ctx
            .typeConstrants
            .as_ref()
            .map(|ctx| self.process_where_clause(ctx))
            .transpose()?
            .unwrap_or_default();

        Ok(self.libsl.decls.insert_with_key(|id| ast::Decl {
            id,
            loc,
            kind: ast::DeclAction {
                annotations,
                name,
                generics,
                params,
                ret_ty_expr,
                ty_constraints,
            }
            .into(),
        }))
    }

    fn process_action_param(
        &mut self,
        ctx: &ActionParamContextAll<'_>,
    ) -> Result<ast::ActionParam> {
        let annotations = self.process_annotations(&ctx.annotations)?;
        let name = self.process_name(ctx.name.as_ref().unwrap());
        let ty_expr = self.process_type_expr(ctx.r#type.as_ref().unwrap())?;

        Ok(ast::ActionParam {
            annotations,
            name,
            ty_expr,
        })
    }

    fn process_automaton_decl(&mut self, ctx: &AutomatonDeclContextAll<'_>) -> Result<DeclId> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());
        let annotations = self.process_annotations(&ctx.annotations)?;
        let is_concept = ctx.concept.is_some();
        let name = self.process_qualified_type_name(ctx.name.as_ref().unwrap())?;

        let constructor_variables = ctx
            .constructorVariables
            .as_ref()
            .map(|ctx| {
                ctx.variables
                    .iter()
                    .map(|ctx| self.process_constructor_variable(ctx))
                    .collect::<Result<_>>()
            })
            .transpose()?
            .unwrap_or_default();

        let ty_expr = self.process_type_expr(ctx.r#type.as_ref().unwrap())?;

        let implemented_concepts = ctx
            .implements
            .as_ref()
            .map(|ctx| {
                ctx.concepts
                    .iter()
                    .map(|ctx| self.process_name(ctx))
                    .collect()
            })
            .unwrap_or_default();

        let ty_constraints = ctx
            .typeConstraints
            .as_ref()
            .map(|ctx| self.process_where_clause(ctx))
            .transpose()?
            .unwrap_or_default();

        let mut decls = Vec::with_capacity(ctx.decls.len());

        for ctx in &ctx.decls {
            match &**ctx {
                AutomatonDefDeclContextAll::AutomatonDefDeclStateContext(ctx) => {
                    decls.extend(self.process_state_decl(&ctx.stateDecl().unwrap()))
                }

                AutomatonDefDeclContextAll::AutomatonDefDeclShiftContext(ctx) => {
                    decls.push(self.process_shift_decl(&ctx.shiftDecl().unwrap())?)
                }

                AutomatonDefDeclContextAll::AutomatonDefDeclConstructorContext(ctx) => {
                    decls.push(self.process_constructor_decl(&ctx.constructorDecl().unwrap())?)
                }

                AutomatonDefDeclContextAll::AutomatonDefDeclDestructorContext(ctx) => {
                    decls.push(self.process_destructor_decl(&ctx.destructorDecl().unwrap())?)
                }

                AutomatonDefDeclContextAll::AutomatonDefDeclProcContext(ctx) => {
                    decls.push(self.process_proc_decl(&ctx.procDecl().unwrap())?)
                }

                AutomatonDefDeclContextAll::AutomatonDefDeclFunctionContext(ctx) => {
                    decls.push(self.process_function_decl(&ctx.functionDecl().unwrap())?)
                }

                AutomatonDefDeclContextAll::AutomatonDefDeclVariableContext(ctx) => {
                    decls.push(self.process_variable_decl(&ctx.variableDecl().unwrap())?)
                }

                AutomatonDefDeclContextAll::Error(_) => unreachable!(),
            }
        }

        Ok(self.libsl.decls.insert_with_key(|id| ast::Decl {
            id,
            loc,
            kind: ast::DeclAutomaton {
                annotations,
                is_concept,
                name,
                constructor_variables,
                ty_expr,
                implemented_concepts,
                ty_constraints,
                decls,
            }
            .into(),
        }))
    }

    fn process_constructor_variable(
        &mut self,
        ctx: &ConstructorVariableContextAll<'_>,
    ) -> Result<DeclId> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());
        let annotations = self.process_annotations(&ctx.annotations)?;
        let kind = self.process_variable_kind(ctx.kind.as_ref().unwrap());
        let name = self.process_name(ctx.name.as_ref().unwrap());
        let ty_expr = self.process_type_expr(ctx.r#type.as_ref().unwrap())?;

        let init = ctx
            .init
            .as_ref()
            .map(|ctx| self.process_expr(ctx))
            .transpose()?;

        Ok(self.libsl.decls.insert_with_key(|id| ast::Decl {
            id,
            loc,
            kind: ast::DeclVariable {
                annotations,
                kind,
                name,
                ty_expr,
                init,
            }
            .into(),
        }))
    }

    fn process_function_decl(&mut self, ctx: &FunctionDeclContextAll<'_>) -> Result<DeclId> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());
        let annotations = self.process_annotations(&ctx.annotations)?;

        let mut is_static = false;

        for modifier in &ctx.modifiers {
            match &**modifier {
                FunctionModifierContextAll::FunctionModifierStaticContext(_) => {
                    is_static = true;
                }

                FunctionModifierContextAll::Error(_) => unreachable!(),
            }
        }

        let extension_for = ctx
            .extensionFor
            .as_ref()
            .map(|ctx| self.process_full_name(ctx));
        let is_method = ctx.method.is_some();
        let name = self.process_name(ctx.name.as_ref().unwrap());

        let generics = ctx
            .typeParams
            .as_ref()
            .map(|ctx| self.process_generics(ctx))
            .unwrap_or_default();

        let params = ctx
            .params
            .as_ref()
            .map(|ctx| {
                ctx.params
                    .iter()
                    .map(|ctx| self.process_function_param(ctx))
                    .collect::<Result<_>>()
            })
            .transpose()?
            .unwrap_or_default();

        let ret_ty_expr = ctx
            .retType
            .as_ref()
            .map(|ctx| self.process_type_expr(ctx))
            .transpose()?;

        let ty_constraints = ctx
            .typeConstraints
            .as_ref()
            .map(|ctx| self.process_where_clause(ctx))
            .transpose()?
            .unwrap_or_default();

        let body = self.process_function_def(ctx.def.as_ref().unwrap())?;

        Ok(self.libsl.decls.insert_with_key(|id| ast::Decl {
            id,
            loc,
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
        }))
    }

    fn process_function_def(
        &mut self,
        ctx: &FunctionDefContextAll<'_>,
    ) -> Result<Option<ast::FunctionBody>> {
        Ok(match ctx {
            FunctionDefContextAll::FunctionDefBracedContext(ctx) => {
                Some(self.process_function_body(&ctx.functionBody().unwrap())?)
            }

            FunctionDefContextAll::FunctionDefSemicolonContext(_) => None,

            FunctionDefContextAll::Error(_) => unreachable!(),
        })
    }

    fn process_variable_decl(&mut self, ctx: &VariableDeclContextAll<'_>) -> Result<DeclId> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());
        let annotations = self.process_annotations(&ctx.annotations)?;
        let kind = self.process_variable_kind(ctx.kind.as_ref().unwrap());
        let name = self.process_name(ctx.name.as_ref().unwrap());
        let ty_expr = self.process_type_expr(ctx.r#type.as_ref().unwrap())?;

        let init = ctx
            .init
            .as_ref()
            .map(|ctx| self.process_expr(ctx))
            .transpose()?;

        Ok(self.libsl.decls.insert_with_key(|id| ast::Decl {
            id,
            loc,
            kind: ast::DeclVariable {
                annotations,
                kind,
                name,
                ty_expr,
                init,
            }
            .into(),
        }))
    }

    fn process_variable_kind(&mut self, ctx: &VariableKindContextAll<'_>) -> ast::VariableKind {
        match ctx {
            VariableKindContextAll::VariableKindVarContext(_) => ast::VariableKind::Var,
            VariableKindContextAll::VariableKindValContext(_) => ast::VariableKind::Val,
            VariableKindContextAll::Error(_) => unreachable!(),
        }
    }

    fn process_state_decl(&mut self, ctx: &StateDeclContextAll<'_>) -> Vec<DeclId> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());

        let kind = match **ctx.kind.as_ref().unwrap() {
            StateKindContextAll::StateKindInitialContext(_) => ast::StateKind::Initial,
            StateKindContextAll::StateKindFinalContext(_) => ast::StateKind::Final,
            StateKindContextAll::StateKindRegularContext(_) => ast::StateKind::Regular,
            StateKindContextAll::Error(_) => unreachable!(),
        };

        ctx.names
            .as_ref()
            .unwrap()
            .names
            .iter()
            .map(move |ctx| {
                let name = self.process_name(ctx);

                self.libsl.decls.insert_with_key(|id| ast::Decl {
                    id,
                    loc: loc.clone(),
                    kind: ast::DeclState { kind, name }.into(),
                })
            })
            .collect()
    }

    fn process_shift_decl(&mut self, ctx: &ShiftDeclContextAll<'_>) -> Result<DeclId> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());

        let from = match &**ctx.from.as_ref().unwrap() {
            ShiftSourceStateContextAll::ShiftSourceStateShorthandContext(ctx) => {
                vec![self.process_name(&ctx.ident().unwrap())]
            }

            ShiftSourceStateContextAll::ShiftSourceStateListContext(ctx) => ctx
                .states
                .as_ref()
                .map(|ctx| ctx.names.iter().map(|ctx| self.process_name(ctx)).collect())
                .unwrap_or_default(),

            ShiftSourceStateContextAll::Error(_) => unreachable!(),
        };

        let to = self.process_name(ctx.to.as_ref().unwrap());

        let by = match &**ctx.by.as_ref().unwrap() {
            ShiftByContextAll::ShiftByShorthandContext(ctx) => {
                vec![self.process_function_signature(ctx.signature.as_ref().unwrap())?]
            }

            ShiftByContextAll::ShiftByListContext(ctx) => ctx
                .signatures
                .as_ref()
                .map(|ctx| {
                    ctx.signatures
                        .iter()
                        .map(|ctx| self.process_function_signature(ctx))
                        .collect::<Result<_>>()
                })
                .transpose()?
                .unwrap_or_default(),

            ShiftByContextAll::Error(_) => unreachable!(),
        };

        Ok(self.libsl.decls.insert_with_key(|id| ast::Decl {
            id,
            loc,
            kind: ast::DeclShift { from, to, by }.into(),
        }))
    }

    fn process_function_signature(
        &mut self,
        ctx: &FunctionSignatureContextAll<'_>,
    ) -> Result<ast::QualifiedFunctionName> {
        Ok(match ctx {
            FunctionSignatureContextAll::FunctionSignatureShorthandContext(ctx) => {
                let name = self.process_name(ctx.name.as_ref().unwrap());

                ast::QualifiedFunctionName { name, params: None }
            }

            FunctionSignatureContextAll::FunctionSignatureQualifiedContext(ctx) => {
                let name = self.process_name(ctx.name.as_ref().unwrap());
                let params = ctx
                    .params
                    .as_ref()
                    .map(|ctx| {
                        ctx.typeExprs
                            .iter()
                            .map(|ctx| self.process_type_expr(ctx))
                            .collect::<Result<_>>()
                    })
                    .transpose()?
                    .unwrap_or_default();

                ast::QualifiedFunctionName {
                    name,
                    params: Some(params),
                }
            }

            FunctionSignatureContextAll::Error(_) => todo!(),
        })
    }

    fn process_constructor_decl(&mut self, ctx: &ConstructorDeclContextAll<'_>) -> Result<DeclId> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());
        let annotations = self.process_annotations(&ctx.annotations)?;
        let is_method = ctx.method.is_some();
        let name = ctx.name.as_ref().map(|ctx| self.process_name(ctx));

        let params = ctx
            .params
            .as_ref()
            .map(|ctx| {
                ctx.params
                    .iter()
                    .map(|ctx| self.process_function_param(ctx))
                    .collect::<Result<_>>()
            })
            .transpose()?
            .unwrap_or_default();

        let ret_ty_expr = ctx
            .retType
            .as_ref()
            .map(|ctx| self.process_type_expr(ctx))
            .transpose()?;

        let body = self.process_function_def(ctx.def.as_ref().unwrap())?;

        Ok(self.libsl.decls.insert_with_key(|id| ast::Decl {
            id,
            loc,
            kind: ast::DeclConstructor {
                annotations,
                is_method,
                name,
                params,
                ret_ty_expr,
                body,
            }
            .into(),
        }))
    }

    fn process_destructor_decl(&mut self, ctx: &DestructorDeclContextAll<'_>) -> Result<DeclId> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());
        let annotations = self.process_annotations(&ctx.annotations)?;
        let is_method = ctx.method.is_some();
        let name = ctx.name.as_ref().map(|ctx| self.process_name(ctx));

        let params = ctx
            .params
            .as_ref()
            .map(|ctx| {
                ctx.params
                    .iter()
                    .map(|ctx| self.process_function_param(ctx))
                    .collect::<Result<_>>()
            })
            .transpose()?
            .unwrap_or_default();

        let ret_ty_expr = ctx
            .retType
            .as_ref()
            .map(|ctx| self.process_type_expr(ctx))
            .transpose()?;

        let body = self.process_function_def(ctx.def.as_ref().unwrap())?;

        Ok(self.libsl.decls.insert_with_key(|id| ast::Decl {
            id,
            loc,
            kind: ast::DeclDestructor {
                annotations,
                is_method,
                name,
                params,
                ret_ty_expr,
                body,
            }
            .into(),
        }))
    }

    fn process_proc_decl(&mut self, ctx: &ProcDeclContextAll<'_>) -> Result<DeclId> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());
        let annotations = self.process_annotations(&ctx.annotations)?;

        let mut is_pure = false;

        for modifier in &ctx.modifiers {
            match &**modifier {
                ProcModifierContextAll::ProcModifierPureContext(_) => {
                    is_pure = true;
                }

                ProcModifierContextAll::Error(_) => unreachable!(),
            }
        }

        let is_method = ctx.method.is_some();
        let name = self.process_name(ctx.name.as_ref().unwrap());

        let generics = ctx
            .typeParams
            .as_ref()
            .map(|ctx| self.process_generics(ctx))
            .unwrap_or_default();

        let params = ctx
            .params
            .as_ref()
            .map(|ctx| {
                ctx.params
                    .iter()
                    .map(|ctx| self.process_function_param(ctx))
                    .collect::<Result<_>>()
            })
            .transpose()?
            .unwrap_or_default();

        let ret_ty_expr = ctx
            .retType
            .as_ref()
            .map(|ctx| self.process_type_expr(ctx))
            .transpose()?;

        let ty_constraints = ctx
            .typeConstraints
            .as_ref()
            .map(|ctx| self.process_where_clause(ctx))
            .transpose()?
            .unwrap_or_default();

        let body = self.process_function_def(ctx.def.as_ref().unwrap())?;

        Ok(self.libsl.decls.insert_with_key(|id| ast::Decl {
            id,
            loc,
            kind: ast::DeclProc {
                annotations,
                is_pure,
                is_method,
                name,
                generics,
                params,
                ret_ty_expr,
                ty_constraints,
                body,
            }
            .into(),
        }))
    }

    fn process_function_param(
        &mut self,
        ctx: &FunctionParamContextAll<'_>,
    ) -> Result<ast::FunctionParam> {
        let annotations = self.process_annotations(&ctx.annotations)?;
        let name = self.process_name(ctx.name.as_ref().unwrap());
        let ty_expr = self.process_type_expr(ctx.r#type.as_ref().unwrap())?;

        Ok(ast::FunctionParam {
            annotations,
            name,
            ty_expr,
        })
    }

    fn process_function_body(
        &mut self,
        ctx: &FunctionBodyContextAll<'_>,
    ) -> Result<ast::FunctionBody> {
        let contracts = ctx
            .contracts
            .iter()
            .map(|ctx| self.process_contract(ctx))
            .collect::<Result<_>>()?;

        let stmts = ctx
            .stmts
            .iter()
            .map(|ctx| self.process_stmt(ctx))
            .collect::<Result<_>>()?;

        Ok(ast::FunctionBody { contracts, stmts })
    }

    fn process_contract(&mut self, ctx: &ContractContextAll<'_>) -> Result<ast::Contract> {
        Ok(match ctx {
            ContractContextAll::ContractRequiresContext(ctx) => self
                .process_requires_contract(&ctx.requiresContract().unwrap())?
                .into(),

            ContractContextAll::ContractEnsuresContext(ctx) => self
                .process_ensures_contract(&ctx.ensuresContract().unwrap())?
                .into(),

            ContractContextAll::ContractAssignsContext(ctx) => self
                .process_assigns_contract(&ctx.assignsContract().unwrap())?
                .into(),

            ContractContextAll::Error(_) => unreachable!(),
        })
    }

    fn process_requires_contract(
        &mut self,
        ctx: &RequiresContractContextAll<'_>,
    ) -> Result<ast::ContractRequires> {
        let name = ctx.name.as_ref().map(|ctx| self.process_name(ctx));
        let pred = self.process_contract_predicate(ctx.spec.as_ref().unwrap())?;

        Ok(ast::ContractRequires { name, pred })
    }

    fn process_ensures_contract(
        &mut self,
        ctx: &EnsuresContractContextAll<'_>,
    ) -> Result<ast::ContractEnsures> {
        let name = ctx.name.as_ref().map(|ctx| self.process_name(ctx));
        let pred = self.process_contract_predicate(ctx.spec.as_ref().unwrap())?;

        Ok(ast::ContractEnsures { name, pred })
    }

    fn process_assigns_contract(
        &mut self,
        ctx: &AssignsContractContextAll<'_>,
    ) -> Result<ast::ContractAssigns> {
        let name = ctx.name.as_ref().map(|ctx| self.process_name(ctx));
        let expr = self.process_expr(ctx.spec.as_ref().unwrap())?;

        Ok(ast::ContractAssigns { name, expr })
    }

    fn process_contract_predicate(
        &mut self,
        ctx: &ContractPredicateContextAll<'_>,
    ) -> Result<PredId> {
        match ctx {
            ContractPredicateContextAll::ContractPredicateIfContext(ctx) => {
                self.process_if_predicate(&ctx.ifPredicate().unwrap())
            }

            ContractPredicateContextAll::ContractPredicateExprContext(ctx) => self
                .process_predicate_expr(
                    &ctx.expr().unwrap(),
                    self.get_loc(&ctx.start(), &ctx.stop()),
                ),

            ContractPredicateContextAll::ContractPredicateBlockContext(ctx) => {
                self.process_block_predicate(&ctx.blockPredicate().unwrap())
            }

            ContractPredicateContextAll::Error(_) => unreachable!(),
        }
    }

    #[allow(unused)]
    fn process_expr_predicate(&mut self, ctx: &ExprPredicateContextAll<'_>) -> Result<PredId> {
        match ctx {
            ExprPredicateContextAll::ExprPredicateBlockContext(ctx) => {
                self.process_block_predicate(&ctx.blockPredicate().unwrap())
            }

            ExprPredicateContextAll::ExprPredicateExprContext(ctx) => self.process_predicate_expr(
                &ctx.expr().unwrap(),
                self.get_loc(&ctx.start(), &ctx.stop()),
            ),

            ExprPredicateContextAll::Error(_) => unreachable!(),
        }
    }

    fn process_predicate(&mut self, ctx: &PredicateContextAll<'_>) -> Result<PredId> {
        match ctx {
            PredicateContextAll::PredicateExprContext(ctx) => self.process_predicate_expr(
                &ctx.expr().unwrap(),
                self.get_loc(&ctx.start(), &ctx.stop()),
            ),

            PredicateContextAll::PredicateNamedContext(ctx) => self.process_predicate_named(ctx),

            PredicateContextAll::PredicateIfContext(ctx) => {
                self.process_if_predicate(&ctx.ifPredicate().unwrap())
            }

            PredicateContextAll::PredicateVariableDeclContext(ctx) => {
                self.process_predicate_variable_decl(&ctx.variableDecl().unwrap())
            }

            PredicateContextAll::PredicateBlockContext(ctx) => {
                self.process_block_predicate(&ctx.blockPredicate().unwrap())
            }

            PredicateContextAll::Error(_) => unreachable!(),
        }
    }

    fn process_block_predicate(&mut self, ctx: &BlockPredicateContextAll<'_>) -> Result<PredId> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());

        let preds = ctx
            .predicates
            .iter()
            .map(|ctx| self.process_predicate(ctx))
            .collect::<Result<Vec<_>>>()?;

        Ok(self.libsl.preds.insert_with_key(|id| ast::Pred {
            id,
            loc,
            kind: ast::PredBlock { preds }.into(),
        }))
    }

    fn process_predicate_named(&mut self, ctx: &PredicateNamedContext<'_>) -> Result<PredId> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());
        let name = self.process_name(ctx.name.as_ref().unwrap());
        let pred = self.process_predicate(&ctx.predicate().unwrap())?;

        Ok(self.libsl.preds.insert_with_key(|id| ast::Pred {
            id,
            loc,
            kind: ast::PredNamed { name, pred }.into(),
        }))
    }

    fn process_predicate_variable_decl(
        &mut self,
        ctx: &VariableDeclContextAll<'_>,
    ) -> Result<PredId> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());
        let decl_id = self.process_variable_decl(ctx)?;

        Ok(self.libsl.preds.insert_with_key(|id| ast::Pred {
            id,
            loc,
            kind: decl_id.into(),
        }))
    }

    fn process_if_predicate(&mut self, ctx: &IfPredicateContextAll<'_>) -> Result<PredId> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());
        let cond = self.process_expr(ctx.condition.as_ref().unwrap())?;
        let then_branch = self.process_predicate(ctx.thenBranch.as_ref().unwrap())?;
        let else_branch = ctx
            .elseBranch
            .as_ref()
            .map(|ctx| self.process_predicate(ctx))
            .transpose()?;

        Ok(self.libsl.preds.insert_with_key(|id| ast::Pred {
            id,
            loc,
            kind: ast::PredIf {
                cond,
                then_branch,
                else_branch,
            }
            .into(),
        }))
    }

    fn process_predicate_expr(&mut self, ctx: &ExprContextAll<'_>, loc: Loc) -> Result<PredId> {
        let expr_id = self.process_expr(ctx)?;

        Ok(self.libsl.preds.insert_with_key(|id| ast::Pred {
            id,
            loc,
            kind: expr_id.into(),
        }))
    }

    fn process_annotations(
        &mut self,
        ctx: &[Rc<AnnotationContextAll<'_>>],
    ) -> Result<Vec<ast::Annotation>> {
        ctx.iter().map(|ctx| self.process_annotation(ctx)).collect()
    }

    fn process_annotation(&mut self, ctx: &AnnotationContextAll<'_>) -> Result<ast::Annotation> {
        let name = self.process_name(ctx.name.as_ref().unwrap());
        let args = ctx
            .args
            .as_ref()
            .map(|ctx| {
                ctx.args
                    .iter()
                    .map(|ctx| self.process_annotation_arg(ctx))
                    .collect::<Result<_>>()
            })
            .transpose()?
            .unwrap_or_default();

        Ok(ast::Annotation { name, args })
    }

    fn process_annotation_arg(
        &mut self,
        ctx: &AnnotationArgContextAll<'_>,
    ) -> Result<ast::AnnotationArg> {
        let name = ctx.name.as_ref().map(|ctx| self.process_name(ctx));
        let expr = self.process_expr(ctx.value.as_ref().unwrap())?;

        Ok(ast::AnnotationArg { name, expr })
    }

    fn process_qualified_type_name(
        &mut self,
        ctx: &QualifiedTypeNameContextAll<'_>,
    ) -> Result<ast::QualifiedTyName> {
        let ty_name = self.process_full_name(ctx.typeName.as_ref().unwrap());

        let generics = ctx
            .typeParams
            .as_ref()
            .map(|ctx| self.process_generics(ctx))
            .unwrap_or_default();

        Ok(ast::QualifiedTyName { ty_name, generics })
    }

    fn process_full_name(&mut self, ctx: &FullNameContextAll<'_>) -> ast::FullName {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());
        let components = ctx
            .components
            .iter()
            .map(|ctx| self.process_name(ctx))
            .collect();

        ast::FullName { loc, components }
    }

    fn process_name(&mut self, ctx: &IdentContextAll<'_>) -> ast::Name {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());
        let name = parse_ident(ctx);

        ast::Name { loc, name }
    }

    fn process_where_clause(
        &mut self,
        ctx: &WhereClauseContextAll<'_>,
    ) -> Result<Vec<ast::TyConstraint>> {
        ctx.constraints
            .iter()
            .map(|ctx| self.process_type_constraint(ctx))
            .collect()
    }

    fn process_type_constraint(
        &mut self,
        ctx: &TypeConstraintContextAll<'_>,
    ) -> Result<ast::TyConstraint> {
        let param = self.process_name(ctx.param.as_ref().unwrap());
        let bound = self.process_type_expr(ctx.bound.as_ref().unwrap())?;

        Ok(ast::TyConstraint { param, bound })
    }

    fn process_generics(&mut self, ctx: &GenericsContextAll<'_>) -> Vec<ast::Generic> {
        ctx.list
            .as_ref()
            .map(|ctx| {
                ctx.params
                    .iter()
                    .map(|ctx| self.process_generic(ctx))
                    .collect()
            })
            .unwrap_or_default()
    }

    fn process_generic(&mut self, ctx: &GenericContextAll<'_>) -> ast::Generic {
        let variance = ctx
            .variance
            .as_ref()
            .map(|ctx| self.process_variance_spec(ctx));

        let name = self.process_name(ctx.name.as_ref().unwrap());

        ast::Generic { variance, name }
    }

    fn process_variance_spec(&mut self, ctx: &VarianceSpecContextAll<'_>) -> ast::Variance {
        match ctx {
            VarianceSpecContextAll::CovariantContext(_) => ast::Variance::Covariant,
            VarianceSpecContextAll::ContravariantContext(_) => ast::Variance::Contravariant,
            VarianceSpecContextAll::InvariantContext(_) => ast::Variance::Invariant,
            VarianceSpecContextAll::Error(_) => unreachable!(),
        }
    }

    fn process_type_expr(&mut self, ctx: &TypeExprContextAll<'_>) -> Result<TyExprId> {
        match ctx {
            TypeExprContextAll::TypeExprPrimitiveLitContext(ctx) => {
                self.process_type_expr_primitive_lit(ctx)
            }

            TypeExprContextAll::TypeExprNameContext(ctx) => {
                self.process_name_type_expr(&ctx.nameTypeExpr().unwrap())
            }

            TypeExprContextAll::TypeExprPointerContext(ctx) => {
                self.process_pointer_type_expr(&ctx.pointerTypeExpr().unwrap())
            }

            TypeExprContextAll::TypeExprIntersectionContext(ctx) => {
                self.process_type_expr_intersection(ctx)
            }

            TypeExprContextAll::TypeExprUnionContext(ctx) => self.process_type_expr_union(ctx),

            TypeExprContextAll::Error(_) => unreachable!(),
        }
    }

    fn process_type_expr_primitive_lit(
        &mut self,
        ctx: &TypeExprPrimitiveLitContext<'_>,
    ) -> Result<TyExprId> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());
        let lit = self.process_primitive_lit(ctx.lit.as_ref().unwrap())?;

        Ok(self.libsl.ty_exprs.insert_with_key(|id| ast::TyExpr {
            id,
            loc,
            kind: ast::TyExprPrimitiveLit { lit }.into(),
        }))
    }

    fn process_name_type_expr(&mut self, ctx: &NameTypeExprContextAll<'_>) -> Result<TyExprId> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());
        let ty_name = self.process_full_name(ctx.typeName.as_ref().unwrap());

        let generics = ctx
            .typeArgs
            .as_ref()
            .map(|ctx| self.process_type_arg_spec(ctx))
            .transpose()?;

        Ok(self.libsl.ty_exprs.insert_with_key(|id| ast::TyExpr {
            id,
            loc,
            kind: ast::TyExprName { ty_name, generics }.into(),
        }))
    }

    fn process_pointer_type_expr(
        &mut self,
        ctx: &PointerTypeExprContextAll<'_>,
    ) -> Result<TyExprId> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());
        let base = self.process_type_expr(ctx.base.as_ref().unwrap())?;

        Ok(self.libsl.ty_exprs.insert_with_key(|id| ast::TyExpr {
            id,
            loc,
            kind: ast::TyExprPointer { base }.into(),
        }))
    }

    fn process_type_expr_intersection(
        &mut self,
        ctx: &TypeExprIntersectionContext<'_>,
    ) -> Result<TyExprId> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());
        let lhs = self.process_type_expr(ctx.lhs.as_ref().unwrap())?;
        let rhs = self.process_type_expr(ctx.rhs.as_ref().unwrap())?;

        Ok(self.libsl.ty_exprs.insert_with_key(|id| ast::TyExpr {
            id,
            loc,
            kind: ast::TyExprIntersection { lhs, rhs }.into(),
        }))
    }

    fn process_type_expr_union(&mut self, ctx: &TypeExprUnionContext<'_>) -> Result<TyExprId> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());
        let lhs = self.process_type_expr(ctx.lhs.as_ref().unwrap())?;
        let rhs = self.process_type_expr(ctx.rhs.as_ref().unwrap())?;

        Ok(self.libsl.ty_exprs.insert_with_key(|id| ast::TyExpr {
            id,
            loc,
            kind: ast::TyExprUnion { lhs, rhs }.into(),
        }))
    }

    fn process_type_arg_spec(
        &mut self,
        ctx: &TypeArgSpecContextAll<'_>,
    ) -> Result<Vec<ast::TyArg>> {
        Ok(ctx
            .list
            .as_ref()
            .map(|ctx| {
                ctx.typeArgs
                    .iter()
                    .map(|ctx| self.process_type_arg(ctx))
                    .collect()
            })
            .transpose()?
            .unwrap_or_default())
    }

    fn process_type_arg(&mut self, ctx: &TypeArgContextAll<'_>) -> Result<ast::TyArg> {
        Ok(match ctx {
            TypeArgContextAll::TypeArgTypeExprContext(ctx) => {
                let variance = ctx
                    .variance
                    .as_ref()
                    .map(|ctx| self.process_variance_spec(ctx));

                ast::TyArg::TyExpr(variance, self.process_type_expr(&ctx.typeExpr().unwrap())?)
            }

            TypeArgContextAll::TypeArgWildcardContext(ctx) => {
                ast::TyArg::Wildcard(self.get_loc(&ctx.start(), &ctx.stop()))
            }

            TypeArgContextAll::Error(_) => unreachable!(),
        })
    }

    fn process_block(&mut self, ctx: &BlockContextAll<'_>) -> Result<Vec<StmtId>> {
        Ok(match ctx {
            BlockContextAll::BlockLoneStmtContext(ctx) => {
                vec![self.process_stmt(&ctx.stmt().unwrap())?]
            }

            BlockContextAll::BlockBracedContext(ctx) => ctx
                .stmts
                .iter()
                .map(|ctx| self.process_stmt(ctx))
                .collect::<Result<_>>()?,

            BlockContextAll::Error(_) => unreachable!(),
        })
    }

    fn process_stmt(&mut self, ctx: &StmtContextAll<'_>) -> Result<StmtId> {
        match ctx {
            StmtContextAll::StmtVariableDeclContext(ctx) => self.process_stmt_variable_decl(ctx),

            StmtContextAll::StmtIfContext(ctx) => self.process_if_stmt(&ctx.ifStmt().unwrap()),

            StmtContextAll::StmtAssignContext(ctx) => {
                self.process_assign_stmt(&ctx.assignStmt().unwrap())
            }

            StmtContextAll::StmtCancelContext(ctx) => {
                self.process_cancel_stmt(&ctx.cancelStmt().unwrap())
            }

            StmtContextAll::StmtExprContext(ctx) => self.process_stmt_expr(ctx),

            StmtContextAll::Error(_) => unreachable!(),
        }
    }

    fn process_stmt_variable_decl(&mut self, ctx: &StmtVariableDeclContext<'_>) -> Result<StmtId> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());
        let decl_id = self.process_variable_decl(&ctx.variableDecl().unwrap())?;

        Ok(self.libsl.stmts.insert_with_key(|id| ast::Stmt {
            id,
            loc,
            kind: decl_id.into(),
        }))
    }

    fn process_if_stmt(&mut self, ctx: &IfStmtContextAll<'_>) -> Result<StmtId> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());
        let cond = self.process_expr(ctx.condition.as_ref().unwrap())?;
        let then_branch = self.process_block(ctx.thenBranch.as_ref().unwrap())?;

        let else_branch = ctx
            .elseBranch
            .as_ref()
            .map(|ctx| self.process_block(ctx))
            .transpose()?
            .unwrap_or_default();

        Ok(self.libsl.stmts.insert_with_key(|id| ast::Stmt {
            id,
            loc,
            kind: ast::StmtIf {
                cond,
                then_branch,
                else_branch,
            }
            .into(),
        }))
    }

    fn process_assign_stmt(&mut self, ctx: &AssignStmtContextAll<'_>) -> Result<StmtId> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());
        let lhs = self.process_access(ctx.lhs.as_ref().unwrap())?;

        let in_place_op = match &**ctx.op.as_ref().unwrap() {
            AssignOpContextAll::OpAssignContext(_) => None,
            AssignOpContextAll::OpAddAssignContext(_) => Some(ast::InPlaceOp::Add),
            AssignOpContextAll::OpSubAssignContext(_) => Some(ast::InPlaceOp::Sub),
            AssignOpContextAll::OpMulAssignContext(_) => Some(ast::InPlaceOp::Mul),
            AssignOpContextAll::OpDivAssignContext(_) => Some(ast::InPlaceOp::Div),
            AssignOpContextAll::OpModAssignContext(_) => Some(ast::InPlaceOp::Mod),
            AssignOpContextAll::OpBitAndAssignContext(_) => Some(ast::InPlaceOp::BitAnd),
            AssignOpContextAll::OpBitOrAssignContext(_) => Some(ast::InPlaceOp::BitOr),
            AssignOpContextAll::OpBitXorAssignContext(_) => Some(ast::InPlaceOp::BitXor),
            AssignOpContextAll::OpLShiftAssignContext(_) => Some(ast::InPlaceOp::Sal),
            AssignOpContextAll::OpRShiftAssignContext(_) => Some(ast::InPlaceOp::Sar),
            AssignOpContextAll::Error(_) => unreachable!(),
        };

        let rhs = self.process_expr(ctx.rhs.as_ref().unwrap())?;

        Ok(self.libsl.stmts.insert_with_key(|id| ast::Stmt {
            id,
            loc,
            kind: ast::StmtAssign {
                lhs,
                in_place_op,
                rhs,
            }
            .into(),
        }))
    }

    fn process_cancel_stmt(&mut self, ctx: &CancelStmtContextAll<'_>) -> Result<StmtId> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());

        Ok(self.libsl.stmts.insert_with_key(|id| ast::Stmt {
            id,
            loc,
            kind: ast::StmtCancel.into(),
        }))
    }

    fn process_stmt_expr(&mut self, ctx: &StmtExprContext<'_>) -> Result<StmtId> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());
        let expr_id = self.process_expr(ctx.inner.as_ref().unwrap())?;

        Ok(self.libsl.stmts.insert_with_key(|id| ast::Stmt {
            id,
            loc,
            kind: expr_id.into(),
        }))
    }

    fn process_atomic_expr(&mut self, ctx: &AtomicExprContextAll<'_>) -> Result<ExprId> {
        match ctx {
            AtomicExprContextAll::AtomicExprParenContext(ctx) => {
                self.process_atomic_expr(ctx.inner.as_ref().unwrap())
            }

            AtomicExprContextAll::AtomicExprPrimitiveLitContext(ctx) => {
                self.process_atomic_expr_primitive_lit(ctx)
            }

            AtomicExprContextAll::AtomicExprSignedNumLitContext(ctx) => {
                self.process_atomic_expr_signed_num_lit(ctx)
            }

            AtomicExprContextAll::AtomicExprArrayLitContext(ctx) => {
                self.process_array_lit_expr(&ctx.arrayLitExpr().unwrap())
            }

            AtomicExprContextAll::AtomicExprSetLitContext(ctx) => {
                self.process_set_lit_expr(&ctx.setLitExpr().unwrap())
            }

            AtomicExprContextAll::AtomicExprAccessContext(ctx) => {
                self.process_atomic_expr_access(ctx)
            }

            AtomicExprContextAll::Error(_) => unreachable!(),
        }
    }

    fn process_atomic_expr_primitive_lit(
        &mut self,
        ctx: &AtomicExprPrimitiveLitContext<'_>,
    ) -> Result<ExprId> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());
        let lit = self.process_primitive_lit(ctx.lit.as_ref().unwrap())?;

        Ok(self.libsl.exprs.insert_with_key(|id| ast::Expr {
            id,
            loc,
            kind: ast::ExprPrimitiveLit { lit }.into(),
        }))
    }

    fn process_atomic_expr_signed_num_lit(
        &mut self,
        ctx: &AtomicExprSignedNumLitContext<'_>,
    ) -> Result<ExprId> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());
        let ctx = ctx.signedNumLit().unwrap();

        let lit = match &*ctx {
            SignedNumLitContextAll::SignedNumLitIntContext(ctx) => {
                let sign = self.process_sign(&ctx.sign().unwrap());

                self.process_integer_lit(sign, &ctx.IntegerLit().unwrap())?
                    .into()
            }

            SignedNumLitContextAll::SignedNumLitFloatContext(ctx) => {
                let sign = self.process_sign(&ctx.sign().unwrap());

                self.process_float_lit(sign, &ctx.FloatLit().unwrap())?
                    .into()
            }

            SignedNumLitContextAll::Error(_) => unreachable!(),
        };

        Ok(self.libsl.exprs.insert_with_key(|id| ast::Expr {
            id,
            loc,
            kind: ast::ExprPrimitiveLit { lit }.into(),
        }))
    }

    fn process_atomic_expr_access(&mut self, ctx: &AtomicExprAccessContext<'_>) -> Result<ExprId> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());
        let access = self.process_access(&ctx.access().unwrap())?;

        Ok(self.libsl.exprs.insert_with_key(|id| ast::Expr {
            id,
            loc,
            kind: ast::ExprAccess { access }.into(),
        }))
    }

    fn process_expr(&mut self, ctx: &ExprContextAll<'_>) -> Result<ExprId> {
        match ctx {
            ExprContextAll::ExprParenContext(ctx) => self.process_expr(ctx.inner.as_ref().unwrap()),

            ExprContextAll::ExprPrimitiveLitContext(ctx) => self.process_expr_primitive_lit(ctx),

            ExprContextAll::ExprArrayLitContext(ctx) => {
                self.process_array_lit_expr(&ctx.arrayLitExpr().unwrap())
            }

            ExprContextAll::ExprSetLitContext(ctx) => {
                self.process_set_lit_expr(&ctx.setLitExpr().unwrap())
            }

            ExprContextAll::ExprPrevContext(ctx) => self.process_expr_prev(ctx),

            ExprContextAll::ExprProcCallContext(ctx) => {
                self.process_proc_call_expr(&ctx.procCallExpr().unwrap())
            }

            ExprContextAll::ExprActionCallContext(ctx) => {
                self.process_action_call_expr(&ctx.actionCallExpr().unwrap())
            }

            ExprContextAll::ExprInstantiationContext(ctx) => {
                self.process_instantiation_expr(&ctx.instantiationExpr().unwrap())
            }

            ExprContextAll::ExprAccessContext(ctx) => self.process_expr_access(ctx),

            ExprContextAll::ExprUnaryContext(ctx) => self.process_expr_unary(ctx),

            ExprContextAll::ExprHasConceptContext(ctx) => self.process_expr_has_concept(ctx),

            ExprContextAll::ExprTypeComparisonContext(ctx) => {
                self.process_expr_type_comparison(ctx)
            }

            ExprContextAll::ExprCastContext(ctx) => self.process_expr_cast(ctx),

            ExprContextAll::ExprMultiplicativeContext(ctx) => self.process_expr_multiplicative(ctx),

            ExprContextAll::ExprAdditiveContext(ctx) => self.process_expr_additive(ctx),

            ExprContextAll::ExprShiftContext(ctx) => self.process_expr_shift(ctx),

            ExprContextAll::ExprBitAndContext(ctx) => self.process_expr_bit_and(ctx),

            ExprContextAll::ExprBitXorContext(ctx) => self.process_expr_bit_xor(ctx),

            ExprContextAll::ExprBitOrContext(ctx) => self.process_expr_bit_or(ctx),

            ExprContextAll::ExprRelationalContext(ctx) => self.process_expr_relational(ctx),

            ExprContextAll::ExprAndContext(ctx) => self.process_expr_and(ctx),

            ExprContextAll::ExprOrContext(ctx) => self.process_expr_or(ctx),

            ExprContextAll::Error(_) => unreachable!(),
        }
    }

    fn process_expr_primitive_lit(&mut self, ctx: &ExprPrimitiveLitContext<'_>) -> Result<ExprId> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());
        let lit = self.process_primitive_lit(&ctx.primitiveLit().unwrap())?;

        Ok(self.libsl.exprs.insert_with_key(|id| ast::Expr {
            id,
            loc,
            kind: ast::ExprPrimitiveLit { lit }.into(),
        }))
    }

    fn process_primitive_lit(
        &mut self,
        ctx: &PrimitiveLitContextAll<'_>,
    ) -> Result<ast::PrimitiveLit> {
        match ctx {
            PrimitiveLitContextAll::PrimitiveLitIntContext(ctx) => self
                .process_integer_lit(Sign::Plus, &ctx.IntegerLit().unwrap())
                .map(Into::into),

            PrimitiveLitContextAll::PrimitiveLitFloatContext(ctx) => self
                .process_float_lit(Sign::Plus, &ctx.FloatLit().unwrap())
                .map(Into::into),

            PrimitiveLitContextAll::PrimitiveLitStringLitContext(ctx) => Ok(
                ast::PrimitiveLit::String(parse_string_lit(&ctx.StringLit().unwrap().symbol)),
            ),

            PrimitiveLitContextAll::PrimitiveLitCharContext(ctx) => {
                Ok(self.process_char_lit(&ctx.CharacterLit().unwrap()))
            }

            PrimitiveLitContextAll::PrimitiveLitTrueContext(_) => Ok(ast::PrimitiveLit::Bool(true)),

            PrimitiveLitContextAll::PrimitiveLitFalseContext(_) => {
                Ok(ast::PrimitiveLit::Bool(false))
            }

            PrimitiveLitContextAll::PrimitiveLitNullContext(_) => Ok(ast::PrimitiveLit::Null),

            PrimitiveLitContextAll::Error(_) => unreachable!(),
        }
    }

    fn process_integer_lit(&mut self, sign: Sign, ctx: &Terminal<'_>) -> Result<ast::IntLit> {
        debug_assert_eq!(ctx.symbol.token_type, grammar::parser::IntegerLit);

        enum Suffix {
            Byte,
            UByte,
            Short,
            UShort,
            Int,
            UInt,
            Long,
            ULong,
        }

        let s = &ctx.symbol.text;

        let (s, suffix) = if let Some(s) = s.strip_suffix("uL") {
            (s, Suffix::ULong)
        } else if let Some(s) = s.strip_suffix('l').or_else(|| s.strip_suffix('L')) {
            (s, Suffix::Long)
        } else if let Some(s) = s.strip_suffix("ux") {
            (s, Suffix::UByte)
        } else if let Some(s) = s.strip_suffix('x') {
            (s, Suffix::Byte)
        } else if let Some(s) = s.strip_suffix("us") {
            (s, Suffix::UShort)
        } else if let Some(s) = s.strip_suffix('s') {
            (s, Suffix::Short)
        } else if let Some(s) = s.strip_suffix('u') {
            (s, Suffix::UInt)
        } else {
            (&**s, Suffix::Int)
        };

        let (s, radix) = if let Some(s) = s.strip_prefix("0x").or_else(|| s.strip_prefix("0X")) {
            (s, Radix::Hexadecimal)
        } else if let Some(s) = s.strip_prefix("0b").or_else(|| s.strip_prefix("0B")) {
            (s, Radix::Binary)
        } else if s == "0" {
            (s, Radix::Decimal)
        } else if let Some(s) = s.strip_prefix('0') {
            (s, Radix::Octal)
        } else {
            (s, Radix::Decimal)
        };

        let s = match sign {
            Sign::Plus => format!("+{s}"),
            Sign::Minus => format!("-{s}"),
        };

        let n: Result<ast::IntLit, _> = match suffix {
            Suffix::Byte => i8::from_str_radix(&s, radix.into()).map(Into::into),
            Suffix::UByte => u8::from_str_radix(&s, radix.into()).map(Into::into),
            Suffix::Short => i16::from_str_radix(&s, radix.into()).map(Into::into),
            Suffix::UShort => u16::from_str_radix(&s, radix.into()).map(Into::into),
            Suffix::Int => i32::from_str_radix(&s, radix.into()).map(Into::into),
            Suffix::UInt => u32::from_str_radix(&s, radix.into()).map(Into::into),
            Suffix::Long => i64::from_str_radix(&s, radix.into()).map(Into::into),
            Suffix::ULong => u64::from_str_radix(&s, radix.into()).map(Into::into),
        };

        n.map_err(|inner| ParseError::Int {
            radix,
            file_id: self.file_id,
            line: parse_line_or_col(ctx.symbol.line),
            col: parse_line_or_col(ctx.symbol.column),
            inner,
        })
    }

    fn process_float_lit(&mut self, sign: Sign, ctx: &Terminal<'_>) -> Result<ast::FloatLit> {
        debug_assert_eq!(ctx.symbol.token_type, grammar::parser::FloatLit);

        enum Suffix {
            Float,
            Double,
        }

        let s = &*ctx.symbol.text;

        let (s, suffix) = if let Some(s) = s.strip_suffix(['f', 'F']) {
            (s, Suffix::Float)
        } else if let Some(s) = s.strip_suffix(['d', 'D']) {
            (s, Suffix::Double)
        } else {
            (s, Suffix::Double)
        };

        let s = match sign {
            Sign::Plus => format!("+{s}"),
            Sign::Minus => format!("-{s}"),
        };

        Ok(match suffix {
            Suffix::Float => ast::FloatLit::F32(s.parse().unwrap()),
            Suffix::Double => ast::FloatLit::F64(s.parse().unwrap()),
        })
    }

    fn process_char_lit(&mut self, ctx: &Terminal<'_>) -> ast::PrimitiveLit {
        debug_assert_eq!(ctx.symbol.token_type, grammar::parser::CharacterLit);

        let s = strip_surrounding(&ctx.symbol.text, '\'', '\'');

        let c = if let Some(escape) = s.strip_prefix('\\') {
            parse_char_escape(escape)
        } else {
            s.chars().next().unwrap() as u32
        };

        ast::PrimitiveLit::Char(c)
    }

    fn process_array_lit_expr(&mut self, ctx: &ArrayLitExprContextAll<'_>) -> Result<ExprId> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());

        let elems = ctx
            .elems
            .as_ref()
            .map(|ctx| {
                ctx.exprs
                    .iter()
                    .map(|ctx| self.process_expr(ctx))
                    .collect::<Result<_>>()
            })
            .transpose()?
            .unwrap_or_default();

        Ok(self.libsl.exprs.insert_with_key(|id| ast::Expr {
            id,
            loc,
            kind: ast::ExprArrayLit { elems }.into(),
        }))
    }

    fn process_set_lit_expr(&mut self, ctx: &SetLitExprContextAll<'_>) -> Result<ExprId> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());

        let elems = ctx
            .elems
            .as_ref()
            .map(|ctx| {
                ctx.exprs
                    .iter()
                    .map(|ctx| self.process_expr(ctx))
                    .collect::<Result<_>>()
            })
            .transpose()?
            .unwrap_or_default();

        Ok(self.libsl.exprs.insert_with_key(|id| ast::Expr {
            id,
            loc,
            kind: ast::ExprSetLit { elems }.into(),
        }))
    }

    fn process_expr_prev(&mut self, ctx: &ExprPrevContext<'_>) -> Result<ExprId> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());
        let access = self.process_access(ctx.base.as_ref().unwrap())?;

        Ok(self.libsl.exprs.insert_with_key(|id| ast::Expr {
            id,
            loc,
            kind: ast::ExprPrev { access }.into(),
        }))
    }

    fn process_proc_call_expr(&mut self, ctx: &ProcCallExprContextAll<'_>) -> Result<ExprId> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());
        let callee = self.process_access(ctx.callee.as_ref().unwrap())?;

        let generics = ctx
            .typeArgs
            .as_ref()
            .map(|ctx| self.process_type_arg_spec(ctx))
            .transpose()?;

        let args = ctx
            .args
            .as_ref()
            .map(|ctx| {
                ctx.exprs
                    .iter()
                    .map(|ctx| self.process_expr(ctx))
                    .collect::<Result<_>>()
            })
            .transpose()?
            .unwrap_or_default();

        Ok(self.libsl.exprs.insert_with_key(|id| ast::Expr {
            id,
            loc,
            kind: ast::ExprProcCall {
                callee,
                generics,
                args,
            }
            .into(),
        }))
    }

    fn process_action_call_expr(&mut self, ctx: &ActionCallExprContextAll<'_>) -> Result<ExprId> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());
        let name = self.process_name(ctx.name.as_ref().unwrap());

        let generics = ctx
            .typeArgs
            .as_ref()
            .map(|ctx| self.process_type_arg_spec(ctx))
            .transpose()?;

        let args = ctx
            .args
            .as_ref()
            .map(|ctx| {
                ctx.exprs
                    .iter()
                    .map(|ctx| self.process_expr(ctx))
                    .collect::<Result<_>>()
            })
            .transpose()?
            .unwrap_or_default();

        Ok(self.libsl.exprs.insert_with_key(|id| ast::Expr {
            id,
            loc,
            kind: ast::ExprActionCall {
                name,
                generics,
                args,
            }
            .into(),
        }))
    }

    fn process_instantiation_expr(
        &mut self,
        ctx: &InstantiationExprContextAll<'_>,
    ) -> Result<ExprId> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());
        let name = self.process_full_name(ctx.name.as_ref().unwrap());

        let generics = ctx
            .typeArgs
            .as_ref()
            .map(|ctx| self.process_type_arg_spec(ctx))
            .transpose()?;

        let args = ctx
            .args
            .as_ref()
            .map(|ctx| {
                ctx.args
                    .iter()
                    .map(|ctx| self.process_constructor_arg(ctx))
                    .collect::<Result<_>>()
            })
            .transpose()?
            .unwrap_or_default();

        Ok(self.libsl.exprs.insert_with_key(|id| ast::Expr {
            id,
            loc,
            kind: ast::ExprInstantiate {
                name,
                generics,
                args,
            }
            .into(),
        }))
    }

    fn process_constructor_arg(
        &mut self,
        ctx: &ConstructorArgContextAll<'_>,
    ) -> Result<ast::ConstructorArg> {
        Ok(match ctx {
            ConstructorArgContextAll::ConstructorArgStateContext(ctx) => {
                let value = self.process_name(ctx.state.as_ref().unwrap());

                ast::ConstructorArg::State(value)
            }

            ConstructorArgContextAll::ConstructorArgVarContext(ctx) => {
                let name = self.process_name(ctx.name.as_ref().unwrap());
                let value = self.process_expr(ctx.value.as_ref().unwrap())?;

                ast::ConstructorArg::Var(name, value)
            }

            ConstructorArgContextAll::Error(_) => unreachable!(),
        })
    }

    fn process_expr_access(&mut self, ctx: &ExprAccessContext<'_>) -> Result<ExprId> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());
        let access = self.process_access(&ctx.access().unwrap())?;

        Ok(self.libsl.exprs.insert_with_key(|id| ast::Expr {
            id,
            loc,
            kind: ast::ExprAccess { access }.into(),
        }))
    }

    fn process_expr_unary(&mut self, ctx: &ExprUnaryContext<'_>) -> Result<ExprId> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());

        let (sign, op) = match &**ctx.op.as_ref().unwrap() {
            UnOpContextAll::UnOpNegContext(_) => (Some(Sign::Minus), ast::UnOp::Neg),
            UnOpContextAll::UnOpPlusContext(_) => (Some(Sign::Plus), ast::UnOp::Plus),
            UnOpContextAll::UnOpBitNotContext(_) => (None, ast::UnOp::BitNot),
            UnOpContextAll::UnOpNotContext(_) => (None, ast::UnOp::Not),
            UnOpContextAll::Error(_) => unreachable!(),
        };

        'signed_lit: {
            if let Some(sign) = sign
                && let ExprContextAll::ExprPrimitiveLitContext(ctx) = &**ctx.rhs.as_ref().unwrap()
            {
                let lit = match &**ctx.lit.as_ref().unwrap() {
                    PrimitiveLitContextAll::PrimitiveLitIntContext(ctx) => self
                        .process_integer_lit(sign, &ctx.IntegerLit().unwrap())?
                        .into(),

                    PrimitiveLitContextAll::PrimitiveLitFloatContext(ctx) => self
                        .process_float_lit(sign, &ctx.FloatLit().unwrap())?
                        .into(),

                    _ => break 'signed_lit,
                };

                return Ok(self.libsl.exprs.insert_with_key(|id| ast::Expr {
                    id,
                    loc,
                    kind: ast::ExprPrimitiveLit { lit }.into(),
                }));
            }
        }

        let expr = self.process_expr(ctx.rhs.as_ref().unwrap())?;

        Ok(self.libsl.exprs.insert_with_key(|id| ast::Expr {
            id,
            loc,
            kind: ast::ExprUnary { op, expr }.into(),
        }))
    }

    fn process_expr_has_concept(&mut self, ctx: &ExprHasConceptContext<'_>) -> Result<ExprId> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());
        let scrutinee = self.process_access(ctx.lhs.as_ref().unwrap())?;
        let concept = self.process_name(ctx.concept.as_ref().unwrap());

        Ok(self.libsl.exprs.insert_with_key(|id| ast::Expr {
            id,
            loc,
            kind: ast::ExprHasConcept { scrutinee, concept }.into(),
        }))
    }

    fn process_expr_type_comparison(
        &mut self,
        ctx: &ExprTypeComparisonContext<'_>,
    ) -> Result<ExprId> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());
        let expr = self.process_expr(ctx.lhs.as_ref().unwrap())?;
        let ty_expr = self.process_type_expr(ctx.r#type.as_ref().unwrap())?;

        Ok(self.libsl.exprs.insert_with_key(|id| ast::Expr {
            id,
            loc,
            kind: ast::ExprTyCompare { expr, ty_expr }.into(),
        }))
    }

    fn process_expr_cast(&mut self, ctx: &ExprCastContext<'_>) -> Result<ExprId> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());
        let expr = self.process_expr(ctx.lhs.as_ref().unwrap())?;
        let ty_expr = self.process_type_expr(ctx.r#type.as_ref().unwrap())?;

        Ok(self.libsl.exprs.insert_with_key(|id| ast::Expr {
            id,
            loc,
            kind: ast::ExprCast { expr, ty_expr }.into(),
        }))
    }

    fn process_expr_multiplicative(
        &mut self,
        ctx: &ExprMultiplicativeContext<'_>,
    ) -> Result<ExprId> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());
        let lhs = self.process_expr(ctx.lhs.as_ref().unwrap())?;

        let op = match &**ctx.op.as_ref().unwrap() {
            MulBinOpContextAll::BinOpMulContext(_) => ast::BinOp::Mul,
            MulBinOpContextAll::BinOpDivContext(_) => ast::BinOp::Div,
            MulBinOpContextAll::BinOpModContext(_) => ast::BinOp::Mod,
            MulBinOpContextAll::Error(_) => unreachable!(),
        };

        let rhs = self.process_expr(ctx.rhs.as_ref().unwrap())?;

        Ok(self.libsl.exprs.insert_with_key(|id| ast::Expr {
            id,
            loc,
            kind: ast::ExprBinary { lhs, op, rhs }.into(),
        }))
    }

    fn process_expr_additive(&mut self, ctx: &ExprAdditiveContext<'_>) -> Result<ExprId> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());
        let lhs = self.process_expr(ctx.lhs.as_ref().unwrap())?;

        let op = match &**ctx.op.as_ref().unwrap() {
            AddBinOpContextAll::BinOpAddContext(_) => ast::BinOp::Add,
            AddBinOpContextAll::BinOpSubContext(_) => ast::BinOp::Sub,
            AddBinOpContextAll::Error(_) => unreachable!(),
        };

        let rhs = self.process_expr(ctx.rhs.as_ref().unwrap())?;

        Ok(self.libsl.exprs.insert_with_key(|id| ast::Expr {
            id,
            loc,
            kind: ast::ExprBinary { lhs, op, rhs }.into(),
        }))
    }

    fn process_expr_shift(&mut self, ctx: &ExprShiftContext<'_>) -> Result<ExprId> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());
        let lhs = self.process_expr(ctx.lhs.as_ref().unwrap())?;

        let op = match &**ctx.op.as_ref().unwrap() {
            BitShiftOpContextAll::BinOpLogicalLeftContext(_) => ast::BinOp::Shl,
            BitShiftOpContextAll::BinOpLogicalRightContext(_) => ast::BinOp::Shr,
            BitShiftOpContextAll::BinOpArithmeticLeftContext(_) => ast::BinOp::Sal,
            BitShiftOpContextAll::BinOpArithmeticRightContext(_) => ast::BinOp::Sar,
            BitShiftOpContextAll::Error(_) => unreachable!(),
        };

        let rhs = self.process_expr(ctx.rhs.as_ref().unwrap())?;

        Ok(self.libsl.exprs.insert_with_key(|id| ast::Expr {
            id,
            loc,
            kind: ast::ExprBinary { lhs, op, rhs }.into(),
        }))
    }

    fn process_expr_bit_and(&mut self, ctx: &ExprBitAndContext<'_>) -> Result<ExprId> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());
        let lhs = self.process_expr(ctx.lhs.as_ref().unwrap())?;
        let rhs = self.process_expr(ctx.rhs.as_ref().unwrap())?;

        Ok(self.libsl.exprs.insert_with_key(|id| ast::Expr {
            id,
            loc,
            kind: ast::ExprBinary {
                lhs,
                op: ast::BinOp::BitAnd,
                rhs,
            }
            .into(),
        }))
    }

    fn process_expr_bit_xor(&mut self, ctx: &ExprBitXorContext<'_>) -> Result<ExprId> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());
        let lhs = self.process_expr(ctx.lhs.as_ref().unwrap())?;
        let rhs = self.process_expr(ctx.rhs.as_ref().unwrap())?;

        Ok(self.libsl.exprs.insert_with_key(|id| ast::Expr {
            id,
            loc,
            kind: ast::ExprBinary {
                lhs,
                op: ast::BinOp::BitXor,
                rhs,
            }
            .into(),
        }))
    }

    fn process_expr_bit_or(&mut self, ctx: &ExprBitOrContext<'_>) -> Result<ExprId> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());
        let lhs = self.process_expr(ctx.lhs.as_ref().unwrap())?;
        let rhs = self.process_expr(ctx.rhs.as_ref().unwrap())?;

        Ok(self.libsl.exprs.insert_with_key(|id| ast::Expr {
            id,
            loc,
            kind: ast::ExprBinary {
                lhs,
                op: ast::BinOp::BitOr,
                rhs,
            }
            .into(),
        }))
    }

    fn process_expr_relational(&mut self, ctx: &ExprRelationalContext<'_>) -> Result<ExprId> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());
        let lhs = self.process_expr(ctx.lhs.as_ref().unwrap())?;

        let op = match &**ctx.op.as_ref().unwrap() {
            RelOpContextAll::BinOpLessEqualsContext(_) => ast::BinOp::Le,
            RelOpContextAll::BinOpGreaterEqualsContext(_) => ast::BinOp::Ge,
            RelOpContextAll::BinOpLessContext(_) => ast::BinOp::Lt,
            RelOpContextAll::BinOpGreaterContext(_) => ast::BinOp::Gt,
            RelOpContextAll::BinOpEqualsContext(_) => ast::BinOp::Eq,
            RelOpContextAll::BinOpNotEqualsContext(_) => ast::BinOp::Ne,
            RelOpContextAll::BinOpInContext(_) => ast::BinOp::In,
            RelOpContextAll::Error(_) => unreachable!(),
        };

        let rhs = self.process_expr(ctx.rhs.as_ref().unwrap())?;

        Ok(self.libsl.exprs.insert_with_key(|id| ast::Expr {
            id,
            loc,
            kind: ast::ExprBinary { lhs, op, rhs }.into(),
        }))
    }

    fn process_expr_and(&mut self, ctx: &ExprAndContext<'_>) -> Result<ExprId> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());
        let lhs = self.process_expr(ctx.lhs.as_ref().unwrap())?;
        let rhs = self.process_expr(ctx.rhs.as_ref().unwrap())?;

        Ok(self.libsl.exprs.insert_with_key(|id| ast::Expr {
            id,
            loc,
            kind: ast::ExprBinary {
                lhs,
                op: ast::BinOp::And,
                rhs,
            }
            .into(),
        }))
    }

    fn process_expr_or(&mut self, ctx: &ExprOrContext<'_>) -> Result<ExprId> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());
        let lhs = self.process_expr(ctx.lhs.as_ref().unwrap())?;
        let rhs = self.process_expr(ctx.rhs.as_ref().unwrap())?;

        Ok(self.libsl.exprs.insert_with_key(|id| ast::Expr {
            id,
            loc,
            kind: ast::ExprBinary {
                lhs,
                op: ast::BinOp::Or,
                rhs,
            }
            .into(),
        }))
    }

    fn process_access(&mut self, ctx: &AccessContextAll<'_>) -> Result<AccessId> {
        match ctx {
            AccessContextAll::AccessNameContext(ctx) => Ok(self.process_access_name(ctx)),

            AccessContextAll::AccessFieldContext(ctx) => self.process_access_field(ctx),

            AccessContextAll::AccessIndexContext(ctx) => self.process_access_index(ctx),

            AccessContextAll::AccessAutomatonFieldContext(ctx) => {
                self.process_access_automaton_field(ctx)
            }

            AccessContextAll::Error(_) => unreachable!(),
        }
    }

    fn process_access_name(&mut self, ctx: &AccessNameContext<'_>) -> AccessId {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());
        let name = self.process_name(ctx.name.as_ref().unwrap());

        self.libsl.accesses.insert_with_key(|id| ast::Access {
            id,
            loc,
            kind: ast::AccessName { name }.into(),
        })
    }

    fn process_access_field(&mut self, ctx: &AccessFieldContext<'_>) -> Result<AccessId> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());
        let base = self.process_access(ctx.base.as_ref().unwrap())?;
        let field = self.process_name(ctx.field.as_ref().unwrap());

        Ok(self.libsl.accesses.insert_with_key(|id| ast::Access {
            id,
            loc,
            kind: ast::AccessField { base, field }.into(),
        }))
    }

    fn process_access_index(&mut self, ctx: &AccessIndexContext<'_>) -> Result<AccessId> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());
        let base = self.process_access(ctx.base.as_ref().unwrap())?;
        let index = self.process_expr(ctx.index.as_ref().unwrap())?;

        Ok(self.libsl.accesses.insert_with_key(|id| ast::Access {
            id,
            loc,
            kind: ast::AccessIndex { base, index }.into(),
        }))
    }

    fn process_access_automaton_field(
        &mut self,
        ctx: &AccessAutomatonFieldContext<'_>,
    ) -> Result<AccessId> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());
        let automaton_name = self.process_name(ctx.name.as_ref().unwrap());

        let generics = ctx
            .typeArgs
            .as_ref()
            .map(|ctx| self.process_type_arg_spec(ctx))
            .transpose()?;

        let base = self.process_access(&ctx.access().unwrap())?;
        let field = self.process_name(ctx.field.as_ref().unwrap());

        Ok(self.libsl.accesses.insert_with_key(|id| ast::Access {
            id,
            loc,
            kind: ast::AccessAutomatonField {
                automaton_name,
                generics,
                base,
                field,
            }
            .into(),
        }))
    }
}
