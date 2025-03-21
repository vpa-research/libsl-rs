//! Implements dumping the AST nodes back as LibSL source text.
//!
//! The AST built by [parsing](LibSl::parse_file) can always by converted to a syntactically correct
//! LibSL source. However, the module performs no additional checks to ensure that, and invalid text
//! may still be emitted if you, for instance, put an illegal identifier as the name for a type or
//! insert a wrong node into the AST (such as a state declaration in the global scope).

use std::fmt::{self, Display, Write as _};

use crate::{DeclId, LibSl, StmtId, ast};

const INDENT: &str = "    ";

pub trait Prec: Copy + Ord {
    /// The maximal precedence level that forces parentheses around an expression.
    const MAX: Self;

    /// The minimal precedence level that forces no parentheses around an expression.
    const MIN: Self;

    /// Returns the next (higher) precedence level (or `MAX` if there's none).
    fn higher(self) -> Self;

    /// Returns the previous (lower) precedence level (or `MIN` if there's none).
    fn lower(self) -> Self;
}

macro_rules! define_prec {
    {
        $(#[$attr:meta])*
        $vis:vis enum $name:ident {
            $(
                $(#[$variant_attr:meta])*
                $variant:ident,
            )+
        }
    } => {
        $(#[$attr])*
        #[repr(u8)]
        #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
        $vis enum $name {
            $(
                $(#[$variant_attr])*
                $variant,
            )+

            /// The precedence level higher than any other.
            Max = u8::MAX,
        }

        impl $name {
            fn from_u8(value: u8) -> Option<Self> {
                Some(match value {
                    $(_ if Self::$variant as u8 == value => Self::$variant,)+
                    u8::MAX => Self::Max,
                    _ => return None,
                })
            }
        }

        impl Prec for $name {
            const MAX: Self = Self::Max;
            const MIN: Self = define_prec!(@first $(Self::$variant,)+);

            fn higher(self) -> Self {
                (self as u8)
                    .checked_add(1)
                    .and_then(Self::from_u8)
                    .unwrap_or(Self::MAX)
            }

            fn lower(self) -> Self {
                (self as u8)
                    .checked_sub(1)
                    .and_then(Self::from_u8)
                    .unwrap_or(Self::MIN)
            }
        }
    };

    (@first $expr:expr, $($rest:expr,)*) => ($expr);
}

define_prec! {
    /// Precedence levels of type expressions.
    pub enum TyExprPrec {
        /// Intersection and union type expressions.
        IntersectionOrUnion,

        /// Pointer type expressions.
        Pointer,

        /// Name type expressions.
        Name,
    }
}

define_prec! {
    /// Precedence levels of expressions.
    pub enum ExprPrec {
        /// Logical and (`&&`) expressions.
        And,

        /// Logical or (`||`) expressions.
        Or,

        /// Bitwise and (`&`) expressions.
        BitAnd,

        /// Bitwise xor (`^`) expressions.
        BitXor,

        /// Bitwise or (`|`) expressions.
        BitOr,

        /// Type comparison expressions.
        TyCmp,

        /// Comparison expressions.
        Cmp,

        /// Bit shift expressions.
        Shift,

        /// Additive expressions: addition and subtraction.
        Add,

        /// Multiplicative expressions: multiplication, division, modulus.
        Mul,

        /// Cast and has-concept expressions.
        Cast,

        /// Unary operator expressions.
        Unary,

        /// Atomic expressions: literals, calls, qualified access.
        Atomic,
    }
}

macro_rules! make_display_struct {
    ($name:ident { $field:ident } for $ast:ty) => {
        impl $ast {
            #[doc = concat!("Returns an object that implements [Display] to convert the [", stringify!($ast), "] back to LibSL source text.")]
            pub fn display<'a>(&'a self, libsl: &'a LibSl) -> $name<'a> {
                $name {
                    $field: self,
                    libsl,
                }
            }
        }

        #[doc = concat!("A helper struct that writes the [", stringify!($ast), "] out as LibSL source text.")]
        #[derive(Debug, Clone, Copy)]
        pub struct $name<'a> {
            $field: &'a $ast,
            libsl: &'a LibSl,
        }
    };

    ($name:ident { $field:ident } for $ast:ty where precedence: $prec_ty:ty = $prec:expr $(,)?) => {
        impl $ast {
            /// The precedence level of this expression.
            ///
            /// See [`display_prec`][Self::display_prec] for more details.
            pub const fn precedence(&self) -> $prec_ty {
                #[allow(unused)]
                let $field = self;

                $prec
            }

            #[doc = concat!("Returns an object that implements [Display] to convert the [", stringify!($ast), "] back to LibSL source text.")]
            ///
            /// This is analogous to calling [`display_prec`][Self::display_prec] with the precedence of zero.
            pub fn display<'a>(&'a self, libsl: &'a LibSl) -> $name<'a> {
                self.display_prec(libsl, <$prec_ty>::MIN)
            }

            #[doc = concat!("Returns an object that implements [Display] to convert the [", stringify!($ast), "] back to LibSL source text.")]
            ///
            /// The parameter `prec` provides the precedence level of the outer context. If it's
            /// greater than [Self::precedence], parentheses will be printed around the expression.
            pub fn display_prec<'a>(&'a self, libsl: &'a LibSl, prec: $prec_ty) -> $name<'a> {
                $name {
                    $field: self,
                    libsl,
                    prec,
                }
            }
        }

        #[doc = concat!("A helper struct that writes the [", stringify!($ast), "] out as LibSL source text.")]
        #[derive(Debug, Clone, Copy)]
        pub struct $name<'a> {
            $field: &'a $ast,
            libsl: &'a LibSl,
            prec: $prec_ty,
        }
    };
}

/// A wrapper [writer](fmt::Write) type that indents all lines written to the inner writer.
///
/// It recognizes `\n` and `\r\n` as line terminators, and does not indent empty lines. A line is
/// considered empty if it doesn't contain anything, including whitespace.
#[derive(Debug)]
pub struct IndentedWriter<'a, W> {
    indent: &'a str,
    w: &'a mut W,
    at_line_start: bool,
}

impl<'a, W: fmt::Write> IndentedWriter<'a, W> {
    /// Creates a new writer that indents every line written in `w`, including the very first one.
    pub fn new(indent: &'a str, w: &'a mut W) -> Self {
        Self {
            indent,
            w,
            at_line_start: true,
        }
    }

    /// Creates a new writer that indent every line written to `w` except the first one.
    pub fn new_skipping_first_indent(indent: &'a str, w: &'a mut W) -> Self {
        Self {
            indent,
            w,
            at_line_start: false,
        }
    }
}

impl<W: fmt::Write> fmt::Write for IndentedWriter<'_, W> {
    fn write_str(&mut self, mut s: &str) -> fmt::Result {
        while !s.is_empty() {
            let nl_pos = s.find('\n');
            let (line, rest) = s.split_at(nl_pos.map(|n| n + 1).unwrap_or(s.len()));

            if line == "\r\n" || line == "\n" {
                // we're at the start of the line and the line is empty, or we're at its end. either
                // way, no indentation is necessary.
                self.w.write_str(line)?;
                self.at_line_start = true;
            } else {
                if self.at_line_start {
                    self.w.write_str(self.indent)?;
                }

                self.w.write_str(line)?;
                self.at_line_start = line.ends_with('\n');
            }

            s = rest;
        }

        Ok(())
    }
}

fn display_list<W: fmt::Write, F>(
    w: &mut W,
    (left, sep, right): (&str, &str, &str),
    blank_line_between_items: bool,
    trailing_sep: bool,
    mut items: impl Iterator<Item = F>,
) -> fmt::Result
where
    F: FnOnce(&mut dyn fmt::Write) -> fmt::Result,
{
    write!(w, "{left}")?;

    {
        let mut w = IndentedWriter::new(INDENT, w);
        let mut next_item = items.next();
        let mut first = true;

        if next_item.is_some() {
            writeln!(w)?;
        }

        while let Some(item) = next_item {
            next_item = items.next();

            if first {
                first = false;
            } else if blank_line_between_items {
                writeln!(w)?;
            }

            item(&mut w)?;

            if next_item.is_some() || trailing_sep {
                writeln!(w, "{sep}")?;
            } else {
                writeln!(w)?;
            }
        }
    }

    write!(w, "{right}")
}

fn display_parens<W: fmt::Write, P: Prec, F>(
    w: &mut W,
    self_prec: P,
    outer_prec: P,
    fmt_inner: F,
) -> fmt::Result
where
    F: FnOnce(&mut dyn fmt::Write) -> fmt::Result,
{
    if self_prec < outer_prec {
        write!(w, "(")?;
    }

    fmt_inner(w)?;

    if self_prec < outer_prec {
        write!(w, ")")?;
    }

    Ok(())
}

/// A wrapper type that formats a string by enclosing it in double quotes and escaping characters if
/// necessary according to LibSL's rules.
///
/// If the string contains a `\n` or a `\r` character, the result will not be a legal LibSL string.
#[derive(Debug, Clone, Copy)]
pub struct QuotedString<'a>(pub &'a str);

impl Display for QuotedString<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "\"")?;

        let mut remaining = self.0;

        while !remaining.is_empty() {
            if let Some((s, rest)) = remaining.split_once('"') {
                write!(f, "{s}\\\"")?;
                remaining = rest;
            } else {
                write!(f, "{remaining}")?;

                break;
            }
        }

        Ok(())
    }
}

/// A wrapper type that formats a string as a LibSL identifier: either as-is or by enclosing in the
/// backticks (<code>`</code>).
///
/// If the string already contains a backtick, the result will not be a legal identifier.
#[derive(Debug, Clone, Copy)]
pub struct Identifier<'a>(pub &'a str);

impl Display for Identifier<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let needs_escaping = self.0.chars().enumerate().any(|(idx, c)| {
            !c.is_ascii_alphabetic() && !"_$".contains(c) && (idx == 0 || !c.is_ascii_digit())
        });

        if needs_escaping {
            write!(f, "`{}`", self.0)
        } else {
            write!(f, "{}", self.0)
        }
    }
}

make_display_struct!(FileDisplay { f } for ast::File);

enum GlobalDeclDisplay<'a> {
    Decl { d: &'a ast::Decl, libsl: &'a LibSl },

    SemanticTyGroup(SemanticTyGroupDisplay<'a>),
}

impl Display for GlobalDeclDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Decl { d, libsl } => write!(f, "{}", d.display(libsl)),
            Self::SemanticTyGroup(group) => write!(f, "{group}"),
        }
    }
}

struct SemanticTyGroupDisplay<'a> {
    decls: &'a [DeclId],
    libsl: &'a LibSl,
}

impl Display for SemanticTyGroupDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "types ")?;
        display_list(
            f,
            ("{", "", "}"),
            true,
            false,
            self.decls.iter().map(|&decl_id| {
                move |f: &mut dyn fmt::Write| {
                    write!(f, "{}", self.libsl.decls[decl_id].display(self.libsl))
                }
            }),
        )
    }
}

struct GlobalDeclIter<'a> {
    decls: &'a [DeclId],
    libsl: &'a LibSl,
}

impl<'a> Iterator for GlobalDeclIter<'a> {
    type Item = GlobalDeclDisplay<'a>;

    fn next(&mut self) -> Option<GlobalDeclDisplay<'a>> {
        let mut decls = self.decls.iter().map(|&decl_id| &self.libsl.decls[decl_id]);
        let group_size = decls
            .clone()
            .take_while(|d| matches!(d.kind, ast::DeclKind::SemanticTy(_)))
            .count();

        let (r, len) = if group_size == 0 {
            let r = decls.next().map(|d| GlobalDeclDisplay::Decl {
                d,
                libsl: self.libsl,
            });

            (r, self.decls.len().max(1))
        } else {
            (
                Some(GlobalDeclDisplay::SemanticTyGroup(SemanticTyGroupDisplay {
                    decls: &self.decls[..group_size],
                    libsl: self.libsl,
                })),
                group_size,
            )
        };

        self.decls = &self.decls[len..];

        r
    }
}

impl Display for FileDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(header) = &self.f.header {
            writeln!(f, "{}", header.display(self.libsl))?;
        }

        let iter = GlobalDeclIter {
            decls: &self.f.decls,
            libsl: self.libsl,
        };

        for (idx, group) in iter.enumerate() {
            if idx > 0 || self.f.header.is_some() {
                writeln!(f)?;
            }

            writeln!(f, "{}", group)?;
        }

        Ok(())
    }
}

make_display_struct!(HeaderDisplay { h } for ast::Header);

impl Display for HeaderDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "libsl {};", QuotedString(&self.h.libsl_version))?;
        write!(f, "library {}", Identifier(&self.h.library_name))?;

        if let Some(version) = &self.h.version {
            write!(f, " {}", QuotedString(version))?;
        }

        if let Some(language) = &self.h.language {
            write!(f, " {}", QuotedString(language))?;
        }

        if let Some(url) = &self.h.url {
            write!(f, " {}", QuotedString(url))?;
        }

        write!(f, ";")
    }
}

make_display_struct!(DeclDisplay { d } for ast::Decl);

impl Display for DeclDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.d.kind {
            ast::DeclKind::Dummy => write!(f, "/* a dummy declaration */"),
            ast::DeclKind::Import(decl) => write!(f, "{}", decl.display(self.libsl)),
            ast::DeclKind::Include(decl) => write!(f, "{}", decl.display(self.libsl)),
            ast::DeclKind::SemanticTy(decl) => write!(f, "{}", decl.display(self.libsl)),
            ast::DeclKind::TyAlias(decl) => write!(f, "{}", decl.display(self.libsl)),
            ast::DeclKind::Struct(decl) => write!(f, "{}", decl.display(self.libsl)),
            ast::DeclKind::Enum(decl) => write!(f, "{}", decl.display(self.libsl)),
            ast::DeclKind::Annotation(decl) => write!(f, "{}", decl.display(self.libsl)),
            ast::DeclKind::Action(decl) => write!(f, "{}", decl.display(self.libsl)),
            ast::DeclKind::Automaton(decl) => write!(f, "{}", decl.display(self.libsl)),
            ast::DeclKind::Function(decl) => write!(f, "{}", decl.display(self.libsl)),
            ast::DeclKind::Variable(decl) => write!(f, "{}", decl.display(self.libsl)),
            ast::DeclKind::State(decl) => write!(f, "{}", decl.display(self.libsl)),
            ast::DeclKind::Shift(decl) => write!(f, "{}", decl.display(self.libsl)),
            ast::DeclKind::Constructor(decl) => write!(f, "{}", decl.display(self.libsl)),
            ast::DeclKind::Destructor(decl) => write!(f, "{}", decl.display(self.libsl)),
            ast::DeclKind::Proc(decl) => write!(f, "{}", decl.display(self.libsl)),
        }
    }
}

make_display_struct!(DeclImportDisplay { d } for ast::DeclImport);

impl Display for DeclImportDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "import {};", self.d.path)
    }
}

make_display_struct!(DeclIncludeDisplay { d } for ast::DeclInclude);

impl Display for DeclIncludeDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "include {};", self.d.path)
    }
}

make_display_struct!(DeclSemanticTyDisplay { d } for ast::DeclSemanticTy);

impl Display for DeclSemanticTyDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for annotation in &self.d.annotations {
            writeln!(f, "{}", annotation.display(self.libsl))?;
        }

        write!(
            f,
            "{ty_name} ({real_ty})",
            ty_name = self.d.ty_name.display(self.libsl),
            real_ty = self.libsl.ty_exprs[self.d.real_ty].display(self.libsl),
        )?;

        match &self.d.kind {
            ast::SemanticTyKind::Simple => write!(f, ";"),

            ast::SemanticTyKind::Enumerated(values) => {
                writeln!(f, " ")?;
                display_list(
                    f,
                    ("{", ";", "}"),
                    false,
                    true,
                    values.iter().map(|entry| {
                        move |f: &mut dyn fmt::Write| {
                            write!(
                                f,
                                "{name}: {value}",
                                name = entry.name,
                                value = self.libsl.exprs[entry.expr].display(self.libsl),
                            )
                        }
                    }),
                )
            }
        }
    }
}

make_display_struct!(DeclTyAliasDisplay { d } for ast::DeclTyAlias);

impl Display for DeclTyAliasDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for annotation in &self.d.annotations {
            writeln!(f, "{}", annotation.display(self.libsl))?;
        }

        write!(
            f,
            "typealias {lhs} = {rhs};",
            lhs = self.d.ty_name.display(self.libsl),
            rhs = self.libsl.ty_exprs[self.d.ty_expr].display(self.libsl),
        )
    }
}

make_display_struct!(DeclStructDisplay { d } for ast::DeclStruct);

impl Display for DeclStructDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for annotation in &self.d.annotations {
            writeln!(f, "{}", annotation.display(self.libsl))?;
        }

        write!(f, "type {}", self.d.ty_name.display(self.libsl))?;

        if let Some(ty_expr_id) = self.d.is_ty {
            write!(
                f,
                "\n{INDENT}is {}",
                self.libsl.ty_exprs[ty_expr_id].display(self.libsl)
            )?;
        }

        for (idx, &ty_expr_id) in self.d.for_tys.iter().enumerate() {
            if idx == 0 {
                write!(f, "\n{INDENT}for ")?;
            } else {
                write!(f, ", ")?;
            }

            write!(f, "{}", self.libsl.ty_exprs[ty_expr_id].display(self.libsl))?;
        }

        if !self.d.ty_constraints.is_empty() {
            write!(
                IndentedWriter::new(INDENT, f),
                "\n{}",
                WhereClauseDisplay {
                    ty_constraints: &self.d.ty_constraints,
                    libsl: self.libsl,
                }
            )?;
        }

        if !self.d.decls.is_empty() {
            if self.d.is_ty.is_none()
                && self.d.for_tys.is_empty()
                && self.d.ty_constraints.is_empty()
            {
                write!(f, " ")?;
            } else {
                writeln!(f)?;
            }

            display_list(
                f,
                ("{", "", "}"),
                true,
                false,
                self.d.decls.iter().map(|&decl_id| {
                    move |f: &mut dyn fmt::Write| {
                        write!(f, "{}", self.libsl.decls[decl_id].display(self.libsl))
                    }
                }),
            )?;
        }

        Ok(())
    }
}

make_display_struct!(DeclEnumDisplay { d } for ast::DeclEnum);

impl Display for DeclEnumDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for annotation in &self.d.annotations {
            writeln!(f, "{}", annotation.display(self.libsl))?;
        }

        write!(f, "enum {} ", self.d.ty_name.display(self.libsl))?;

        display_list(
            f,
            ("{", ";", "}"),
            false,
            true,
            self.d.variants.iter().map(|variant| {
                move |f: &mut dyn fmt::Write| {
                    write!(
                        f,
                        "{name} = {value}",
                        name = variant.name,
                        value = variant.value,
                    )
                }
            }),
        )
    }
}

make_display_struct!(DeclAnnotationDisplay { d } for ast::DeclAnnotation);

impl Display for DeclAnnotationDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "annotation {}", self.d.name)?;

        display_list(
            f,
            ("(", ",", ")"),
            false,
            true,
            self.d.params.iter().map(|param| {
                move |f: &mut dyn fmt::Write| {
                    write!(
                        f,
                        "{name}: {ty_expr}",
                        name = param.name,
                        ty_expr = self.libsl.ty_exprs[param.ty_expr].display(self.libsl),
                    )
                }
            }),
        )?;

        write!(f, ";")
    }
}

make_display_struct!(DeclActionDisplay { d } for ast::DeclAction);

impl Display for DeclActionDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for annotation in &self.d.annotations {
            writeln!(f, "{}", annotation.display(self.libsl))?;
        }

        write!(f, "define action ")?;

        if !self.d.generics.is_empty() {
            write!(
                f,
                "{} ",
                GenericsDisplay {
                    generics: &self.d.generics,
                }
            )?;
        }

        write!(f, "{}", self.d.name)?;

        display_list(
            f,
            ("(", ",", ")"),
            false,
            true,
            self.d.params.iter().map(|param| {
                move |f: &mut dyn fmt::Write| {
                    for annotation in &self.d.annotations {
                        writeln!(f, "{}", annotation.display(self.libsl))?;
                    }

                    writeln!(
                        f,
                        "{INDENT}{name}: {ty_expr}",
                        name = param.name,
                        ty_expr = self.libsl.ty_exprs[param.ty_expr].display(self.libsl),
                    )
                }
            }),
        )?;

        if let Some(ty_expr_id) = self.d.ret_ty_expr {
            write!(
                f,
                ": {}",
                self.libsl.ty_exprs[ty_expr_id].display(self.libsl)
            )?;
        }

        if !self.d.ty_constraints.is_empty() {
            write!(
                IndentedWriter::new(INDENT, f),
                "\n{}",
                WhereClauseDisplay {
                    ty_constraints: &self.d.ty_constraints,
                    libsl: self.libsl,
                }
            )?;
        }

        write!(f, ";")
    }
}

make_display_struct!(DeclAutomatonDisplay { d } for ast::DeclAutomaton);

impl Display for DeclAutomatonDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for annotation in &self.d.annotations {
            writeln!(f, "{}", annotation.display(self.libsl))?;
        }

        write!(f, "automaton ")?;

        if self.d.is_concept {
            write!(f, "concept ")?;
        }

        write!(f, "{}", self.d.name.display(self.libsl))?;

        if !self.d.constructor_variables.is_empty() {
            display_list(
                f,
                ("(", ",", ")"),
                false,
                true,
                self.d.constructor_variables.iter().map(|&decl_id| {
                    move |f: &mut dyn fmt::Write| {
                        write!(f, "{}", self.libsl.decls[decl_id].display(self.libsl))
                    }
                }),
            )?;
        }

        write!(
            f,
            " : {}",
            self.libsl.ty_exprs[self.d.ty_expr].display(self.libsl)
        )?;

        if self.d.implemented_concepts.is_empty() {
            write!(f, " ")?;
        } else {
            writeln!(f)?;

            for (idx, concept) in self.d.implemented_concepts.iter().enumerate() {
                if idx == 0 {
                    write!(f, "{INDENT}implements ")?;
                } else {
                    write!(f, ", ")?;
                }

                write!(f, "{concept}")?;
            }

            writeln!(f)?;
        }

        display_list(
            f,
            ("{", "", "}"),
            true,
            false,
            self.d.decls.iter().map(|&decl_id| {
                move |f: &mut dyn fmt::Write| {
                    write!(f, "{}", self.libsl.decls[decl_id].display(self.libsl))
                }
            }),
        )
    }
}

make_display_struct!(DeclFunctionDisplay { d } for ast::DeclFunction);

impl Display for DeclFunctionDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for annotation in &self.d.annotations {
            writeln!(f, "{}", annotation.display(self.libsl))?;
        }

        if self.d.is_static {
            write!(f, "static ")?;
        }

        write!(f, "fun ")?;

        if let Some(automaton_name) = &self.d.extension_for {
            write!(f, "{automaton_name}.")?;
        }

        if self.d.is_method {
            write!(f, "*.")?;
        }

        write!(f, "{}", self.d.name)?;

        if !self.d.generics.is_empty() {
            write!(
                f,
                "{}",
                GenericsDisplay {
                    generics: &self.d.generics,
                }
            )?;
        }

        display_list(
            f,
            ("(", ",", ")"),
            false,
            false,
            self.d.params.iter().map(|param| {
                move |f: &mut dyn fmt::Write| write!(f, "{}", param.display(self.libsl))
            }),
        )?;

        if let Some(ty_expr_id) = self.d.ret_ty_expr {
            write!(
                f,
                ": {}",
                self.libsl.ty_exprs[ty_expr_id].display(self.libsl)
            )?;
        }

        if !self.d.ty_constraints.is_empty() {
            let mut f = if self.d.ret_ty_expr.is_some() || self.d.params.is_empty() {
                writeln!(f)?;

                IndentedWriter::new(INDENT, f)
            } else {
                write!(f, " ")?;

                IndentedWriter::new_skipping_first_indent(INDENT, f)
            };

            write!(
                f,
                "{}",
                WhereClauseDisplay {
                    ty_constraints: &self.d.ty_constraints,
                    libsl: self.libsl,
                }
            )?;
        }

        if let Some(body) = &self.d.body {
            if self.d.ty_constraints.is_empty() {
                write!(f, " ")?;
            } else {
                writeln!(f)?;
            }

            write!(f, "{}", body.display(self.libsl))
        } else {
            write!(f, ";")
        }
    }
}

make_display_struct!(DeclVariableDisplay { d } for ast::DeclVariable);

impl Display for DeclVariableDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for annotation in &self.d.annotations {
            writeln!(f, "{}", annotation.display(self.libsl))?;
        }

        match self.d.kind {
            ast::VariableKind::Var => write!(f, "var ")?,
            ast::VariableKind::Val => write!(f, "val ")?,
        }

        write!(
            f,
            "{name}: {ty_expr}",
            name = self.d.name,
            ty_expr = self.libsl.ty_exprs[self.d.ty_expr].display(self.libsl),
        )?;

        if let Some(expr_id) = self.d.init {
            write!(f, " = {}", self.libsl.exprs[expr_id].display(self.libsl))?;
        }

        write!(f, ";")
    }
}

make_display_struct!(DeclStateDisplay { d } for ast::DeclState);

impl Display for DeclStateDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.d.kind {
            ast::StateKind::Initial => write!(f, "initstate ")?,
            ast::StateKind::Regular => write!(f, "state ")?,
            ast::StateKind::Final => write!(f, "finishstate ")?,
        }

        write!(f, "{};", self.d.name)
    }
}

make_display_struct!(DeclShiftDisplay { d } for ast::DeclShift);

impl Display for DeclShiftDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "shift ")?;

        if self.d.from.len() == 1 {
            write!(f, "{}", self.d.from[0])?;
        } else {
            write!(f, "(")?;

            for (idx, state) in self.d.from.iter().enumerate() {
                if idx > 0 {
                    write!(f, ", ")?;
                }

                write!(f, "{state}")?;
            }

            write!(f, ")")?;
        }

        write!(f, " -> {} by ", self.d.to)?;

        if self.d.by.len() == 1 {
            write!(f, "{}", self.d.by[0].display(self.libsl))?;
        } else {
            display_list(
                f,
                ("[", ",", "]"),
                false,
                true,
                self.d.by.iter().map(|fn_name| {
                    move |f: &mut dyn fmt::Write| write!(f, "{}", fn_name.display(self.libsl))
                }),
            )?;
        }

        write!(f, ";")
    }
}

make_display_struct!(QualifiedFunctionNameDisplay { f } for ast::QualifiedFunctionName);

impl Display for QualifiedFunctionNameDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.f.name)?;

        if let Some(params) = &self.f.params {
            write!(f, "(")?;

            for (idx, &ty_expr_id) in params.iter().enumerate() {
                if idx > 0 {
                    write!(f, ", ")?;
                }

                write!(f, "{}", self.libsl.ty_exprs[ty_expr_id].display(self.libsl))?;
            }

            write!(f, ")")?;
        }

        Ok(())
    }
}

make_display_struct!(DeclConstructorDisplay { d } for ast::DeclConstructor);

impl Display for DeclConstructorDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for annotation in &self.d.annotations {
            writeln!(f, "{}", annotation.display(self.libsl))?;
        }

        write!(f, "constructor")?;
        let mut have_space = false;

        if self.d.is_method {
            if !have_space {
                write!(f, " ")?;
                have_space = true;
            }

            write!(f, "*.")?;
        }

        if let Some(name) = &self.d.name {
            #[expect(
                unused_assignments,
                reason = "the last assignment to `have_space` is there for consistency"
            )]
            if !have_space {
                write!(f, " ")?;
                have_space = true;
            }

            write!(f, "{name}")?;
        }

        display_list(
            f,
            ("(", ",", ")"),
            false,
            false,
            self.d.params.iter().map(|param| {
                move |f: &mut dyn fmt::Write| write!(f, "{}", param.display(self.libsl))
            }),
        )?;

        if let Some(ty_expr_id) = self.d.ret_ty_expr {
            write!(
                f,
                " : {}",
                self.libsl.ty_exprs[ty_expr_id].display(self.libsl)
            )?;
        }

        if let Some(body) = &self.d.body {
            write!(f, " {}", body.display(self.libsl))
        } else {
            write!(f, ";")
        }
    }
}

make_display_struct!(DeclDestructorDisplay { d } for ast::DeclDestructor);

impl Display for DeclDestructorDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for annotation in &self.d.annotations {
            writeln!(f, "{}", annotation.display(self.libsl))?;
        }

        write!(f, "destructor")?;
        let mut have_space = false;

        if self.d.is_method {
            if !have_space {
                write!(f, " ")?;
                have_space = true;
            }

            write!(f, "*.")?;
        }

        if let Some(name) = &self.d.name {
            #[expect(
                unused_assignments,
                reason = "the last assignment to `have_space` is there for consistency"
            )]
            if !have_space {
                write!(f, " ")?;
                have_space = true;
            }

            write!(f, "{name}")?;
        }

        display_list(
            f,
            ("(", ",", ")"),
            false,
            false,
            self.d.params.iter().map(|param| {
                move |f: &mut dyn fmt::Write| write!(f, "{}", param.display(self.libsl))
            }),
        )?;

        if let Some(ty_expr_id) = self.d.ret_ty_expr {
            write!(
                f,
                " : {}",
                self.libsl.ty_exprs[ty_expr_id].display(self.libsl)
            )?;
        }

        if let Some(body) = &self.d.body {
            write!(f, " {}", body.display(self.libsl))
        } else {
            write!(f, ";")
        }
    }
}

make_display_struct!(DeclProcDisplay { d } for ast::DeclProc);

impl Display for DeclProcDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for annotation in &self.d.annotations {
            writeln!(f, "{}", annotation.display(self.libsl))?;
        }

        write!(f, "proc ")?;

        if self.d.is_method {
            write!(f, "*.")?;
        }

        write!(f, "{}", self.d.name)?;

        if !self.d.generics.is_empty() {
            write!(
                f,
                "{}",
                GenericsDisplay {
                    generics: &self.d.generics,
                },
            )?;
        }

        display_list(
            f,
            ("(", ",", ")"),
            false,
            false,
            self.d.params.iter().map(|param| {
                move |f: &mut dyn fmt::Write| write!(f, "{}", param.display(self.libsl))
            }),
        )?;

        if let Some(ty_expr_id) = self.d.ret_ty_expr {
            write!(
                f,
                ": {}",
                self.libsl.ty_exprs[ty_expr_id].display(self.libsl)
            )?;
        }

        if !self.d.ty_constraints.is_empty() {
            let mut f = if self.d.ret_ty_expr.is_some() || self.d.params.is_empty() {
                writeln!(f)?;

                IndentedWriter::new(INDENT, f)
            } else {
                write!(f, " ")?;

                IndentedWriter::new_skipping_first_indent(INDENT, f)
            };

            write!(
                f,
                "{}",
                WhereClauseDisplay {
                    ty_constraints: &self.d.ty_constraints,
                    libsl: self.libsl,
                }
            )?;
        }

        if let Some(body) = &self.d.body {
            if self.d.ty_constraints.is_empty() {
                write!(f, " ")?;
            } else {
                writeln!(f)?;
            }

            write!(f, "{}", body.display(self.libsl))
        } else {
            write!(f, ";")
        }
    }
}

make_display_struct!(FunctionParamDisplay { p } for ast::FunctionParam);

impl Display for FunctionParamDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for annotation in &self.p.annotations {
            writeln!(f, "{}", annotation.display(self.libsl))?;
        }

        write!(
            f,
            "{name}: {ty_expr}",
            name = self.p.name,
            ty_expr = self.libsl.ty_exprs[self.p.ty_expr].display(self.libsl),
        )
    }
}

make_display_struct!(FunctionBodyDisplay { b } for ast::FunctionBody);

impl Display for FunctionBodyDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        enum Item<'a> {
            Contract(&'a ast::Contract),
            Empty,
            Stmt(StmtId),
        }

        display_list(
            f,
            ("{", "", "}"),
            false,
            false,
            self.b
                .contracts
                .iter()
                .map(Item::Contract)
                .chain(
                    (self.b.contracts.is_empty() && self.b.stmts.is_empty()).then_some(Item::Empty),
                )
                .chain(self.b.stmts.iter().copied().map(Item::Stmt))
                .map(|item| {
                    move |f: &mut dyn fmt::Write| match item {
                        Item::Contract(c) => write!(f, "{}", c.display(self.libsl)),
                        Item::Empty => Ok(()),
                        Item::Stmt(stmt_id) => {
                            write!(f, "{}", self.libsl.stmts[stmt_id].display(self.libsl))
                        }
                    }
                }),
        )
    }
}

make_display_struct!(ContractDisplay { c } for ast::Contract);

impl Display for ContractDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.c {
            ast::Contract::Requires(c) => write!(f, "{}", c.display(self.libsl)),
            ast::Contract::Ensures(c) => write!(f, "{}", c.display(self.libsl)),
            ast::Contract::Assigns(c) => write!(f, "{}", c.display(self.libsl)),
        }
    }
}

make_display_struct!(ContractRequiresDisplay { c } for ast::ContractRequires);

impl Display for ContractRequiresDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "requires ")?;

        if let Some(name) = &self.c.name {
            write!(f, "{name}: ")?;
        }

        write!(f, "{};", self.libsl.exprs[self.c.expr].display(self.libsl))
    }
}

make_display_struct!(ContractEnsuresDisplay { c } for ast::ContractEnsures);

impl Display for ContractEnsuresDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ensures ")?;

        if let Some(name) = &self.c.name {
            write!(f, "{name}: ")?;
        }

        write!(f, "{};", self.libsl.exprs[self.c.expr].display(self.libsl))
    }
}

make_display_struct!(ContractAssignsDisplay { c } for ast::ContractAssigns);

impl Display for ContractAssignsDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "assigns ")?;

        if let Some(name) = &self.c.name {
            write!(f, "{name}: ")?;
        }

        write!(f, "{};", self.libsl.exprs[self.c.expr].display(self.libsl))
    }
}

make_display_struct!(AnnotationDisplay { a } for ast::Annotation);

impl Display for AnnotationDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "@{}", self.a.name)?;

        if !self.a.args.is_empty() {
            display_list(
                f,
                ("(", ",", ")"),
                false,
                true,
                self.a.args.iter().map(|arg| {
                    move |f: &mut dyn fmt::Write| {
                        if let Some(name) = &arg.name {
                            write!(f, "{name} = ")?;
                        }

                        write!(f, "{}", self.libsl.exprs[arg.expr].display(self.libsl))
                    }
                }),
            )?;
        }

        Ok(())
    }
}

make_display_struct!(
    TyExprDisplay { t } for ast::TyExpr
    where precedence: TyExprPrec = match &t.kind {
        ast::TyExprKind::Dummy => TyExprPrec::MAX,
        ast::TyExprKind::PrimitiveLit(t) => t.precedence(),
        ast::TyExprKind::Name(t) => t.precedence(),
        ast::TyExprKind::Pointer(t) => t.precedence(),
        ast::TyExprKind::Intersection(t) => t.precedence(),
        ast::TyExprKind::Union(t) => t.precedence(),
    },
);

impl Display for TyExprDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.t.kind {
            ast::TyExprKind::Dummy => Ok(()),
            ast::TyExprKind::PrimitiveLit(t) => {
                write!(f, "{}", t.display_prec(self.libsl, self.prec))
            }
            ast::TyExprKind::Name(t) => write!(f, "{}", t.display_prec(self.libsl, self.prec)),
            ast::TyExprKind::Pointer(t) => write!(f, "{}", t.display_prec(self.libsl, self.prec)),
            ast::TyExprKind::Intersection(t) => {
                write!(f, "{}", t.display_prec(self.libsl, self.prec))
            }
            ast::TyExprKind::Union(t) => write!(f, "{}", t.display_prec(self.libsl, self.prec)),
        }
    }
}

make_display_struct!(
    TyExprPrimitiveLitDisplay { t } for ast::TyExprPrimitiveLit
    where precedence: TyExprPrec = TyExprPrec::Name,
);

impl Display for TyExprPrimitiveLitDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        display_parens(f, self.t.precedence(), self.prec, |f| {
            write!(f, "{}", self.t.lit.display(self.libsl))
        })
    }
}

make_display_struct!(
    TyExprNameDisplay { t } for ast::TyExprName
    where precedence: TyExprPrec = TyExprPrec::Name,
);

impl Display for TyExprNameDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        display_parens(f, self.t.precedence(), self.prec, |f| {
            write!(f, "{}", self.t.ty_name)?;

            if !self.t.generics.is_empty() {
                write!(f, "<")?;

                for (idx, ty_arg) in self.t.generics.iter().enumerate() {
                    if idx > 0 {
                        write!(f, ", ")?;
                    }

                    write!(f, "{}", ty_arg.display(self.libsl))?;
                }

                write!(f, ">")?;
            }

            Ok(())
        })
    }
}

make_display_struct!(
    TyExprPointerDisplay { t } for ast::TyExprPointer
    where precedence: TyExprPrec = TyExprPrec::Pointer,
);

impl Display for TyExprPointerDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        display_parens(f, self.t.precedence(), self.prec, |f| {
            write!(
                f,
                "*{}",
                self.libsl.ty_exprs[self.t.base].display_prec(self.libsl, self.t.precedence()),
            )
        })
    }
}

make_display_struct!(
    TyExprIntersectionDisplay { t } for ast::TyExprIntersection
    where precedence: TyExprPrec = TyExprPrec::IntersectionOrUnion,
);

impl Display for TyExprIntersectionDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        display_parens(f, self.t.precedence(), self.prec, |f| {
            write!(
                f,
                "{lhs} & {rhs}",
                lhs = self.libsl.ty_exprs[self.t.lhs]
                    .display_prec(self.libsl, self.t.precedence().higher()),
                rhs = self.libsl.ty_exprs[self.t.rhs]
                    .display_prec(self.libsl, self.t.precedence().higher()),
            )
        })
    }
}

make_display_struct!(
    TyExprUnionDisplay { t } for ast::TyExprUnion
    where precedence: TyExprPrec = TyExprPrec::IntersectionOrUnion,
);

impl Display for TyExprUnionDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        display_parens(f, self.t.precedence(), self.prec, |f| {
            write!(
                f,
                "{lhs} + {rhs}",
                lhs = self.libsl.ty_exprs[self.t.lhs]
                    .display_prec(self.libsl, self.t.precedence().higher()),
                rhs = self.libsl.ty_exprs[self.t.rhs]
                    .display_prec(self.libsl, self.t.precedence().higher()),
            )
        })
    }
}

make_display_struct!(StmtDisplay { s } for ast::Stmt);

impl Display for StmtDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.s.kind {
            ast::StmtKind::Dummy => Ok(()),
            ast::StmtKind::Decl(decl_id) => {
                write!(f, "{}", self.libsl.decls[*decl_id].display(self.libsl))
            }
            ast::StmtKind::If(s) => write!(f, "{}", s.display(self.libsl)),
            ast::StmtKind::Assign(s) => write!(f, "{}", s.display(self.libsl)),
            ast::StmtKind::Expr(expr_id) => {
                write!(f, "{}", self.libsl.exprs[*expr_id].display(self.libsl))
            }
        }
    }
}

make_display_struct!(StmtIfDisplay { s } for ast::StmtIf);

impl Display for StmtIfDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "if {} ",
            self.libsl.exprs[self.s.cond].display(self.libsl)
        )?;

        display_list(
            f,
            ("{", "", "}"),
            false,
            false,
            self.s.then_branch.iter().map(|&stmt_id| {
                move |f: &mut dyn fmt::Write| {
                    write!(f, "{}", self.libsl.stmts[stmt_id].display(self.libsl))
                }
            }),
        )?;

        if !self.s.else_branch.is_empty() {
            write!(f, " else ")?;

            display_list(
                f,
                ("{", "", "}"),
                false,
                false,
                self.s.else_branch.iter().map(|&stmt_id| {
                    move |f: &mut dyn fmt::Write| {
                        write!(f, "{}", self.libsl.stmts[stmt_id].display(self.libsl))
                    }
                }),
            )?;
        }

        Ok(())
    }
}

make_display_struct!(StmtAssignDisplay { s } for ast::StmtAssign);

impl Display for StmtAssignDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} ",
            self.libsl.qualified_accesses[self.s.lhs].display(self.libsl),
        )?;

        if let Some(in_place_op) = self.s.in_place_op {
            write!(f, "{in_place_op}")?;
        } else {
            write!(f, "=")?;
        }

        write!(f, " {};", self.libsl.exprs[self.s.rhs].display(self.libsl))
    }
}

impl Display for ast::InPlaceOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ast::InPlaceOp::Add => write!(f, "+="),
            ast::InPlaceOp::Sub => write!(f, "-="),
            ast::InPlaceOp::Mul => write!(f, "*="),
            ast::InPlaceOp::Div => write!(f, "/="),
            ast::InPlaceOp::Mod => write!(f, "%="),
            ast::InPlaceOp::BitAnd => write!(f, "&="),
            ast::InPlaceOp::BitOr => write!(f, "|="),
            ast::InPlaceOp::BitXor => write!(f, "^="),
            ast::InPlaceOp::Sal => write!(f, "<<="),
            ast::InPlaceOp::Sar => write!(f, ">>="),
        }
    }
}

make_display_struct!(
    ExprDisplay { e } for ast::Expr
    where precedence: ExprPrec = match &e.kind {
        ast::ExprKind::Dummy => ExprPrec::MAX,
        ast::ExprKind::PrimitiveLit(e) => e.precedence(),
        ast::ExprKind::ArrayLit(e) => e.precedence(),
        ast::ExprKind::QualifiedAccess(e) => e.precedence(),
        ast::ExprKind::Prev(e) => e.precedence(),
        ast::ExprKind::ProcCall(e) => e.precedence(),
        ast::ExprKind::ActionCall(e) => e.precedence(),
        ast::ExprKind::Instantiate(e) => e.precedence(),
        ast::ExprKind::HasConcept(e) => e.precedence(),
        ast::ExprKind::Cast(e) => e.precedence(),
        ast::ExprKind::TyCompare(e) => e.precedence(),
        ast::ExprKind::Unary(e) => e.precedence(),
        ast::ExprKind::Binary(e) => e.precedence(),
    },
);

impl Display for ExprDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.e.kind {
            ast::ExprKind::Dummy => Ok(()),
            ast::ExprKind::PrimitiveLit(e) => {
                write!(f, "{}", e.display_prec(self.libsl, self.prec))
            }
            ast::ExprKind::ArrayLit(e) => write!(f, "{}", e.display_prec(self.libsl, self.prec)),
            ast::ExprKind::QualifiedAccess(e) => {
                write!(f, "{}", e.display_prec(self.libsl, self.prec))
            }
            ast::ExprKind::Prev(e) => write!(f, "{}", e.display_prec(self.libsl, self.prec)),
            ast::ExprKind::ProcCall(e) => write!(f, "{}", e.display_prec(self.libsl, self.prec)),
            ast::ExprKind::ActionCall(e) => write!(f, "{}", e.display_prec(self.libsl, self.prec)),
            ast::ExprKind::Instantiate(e) => write!(f, "{}", e.display_prec(self.libsl, self.prec)),
            ast::ExprKind::HasConcept(e) => write!(f, "{}", e.display_prec(self.libsl, self.prec)),
            ast::ExprKind::Cast(e) => write!(f, "{}", e.display_prec(self.libsl, self.prec)),
            ast::ExprKind::TyCompare(e) => write!(f, "{}", e.display_prec(self.libsl, self.prec)),
            ast::ExprKind::Unary(e) => write!(f, "{}", e.display_prec(self.libsl, self.prec)),
            ast::ExprKind::Binary(e) => write!(f, "{}", e.display_prec(self.libsl, self.prec)),
        }
    }
}

make_display_struct!(
    ExprPrimitiveLitDisplay { e } for ast::ExprPrimitiveLit
    where precedence: ExprPrec = ExprPrec::Atomic,
);

impl Display for ExprPrimitiveLitDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        display_parens(f, self.e.precedence(), self.prec, |f| {
            write!(f, "{}", self.e.lit.display(self.libsl))
        })
    }
}

make_display_struct!(
    ExprArrayLitDisplay { e } for ast::ExprArrayLit
    where precedence: ExprPrec = ExprPrec::Atomic,
);

impl Display for ExprArrayLitDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        display_parens(f, self.e.precedence(), self.prec, |f| {
            write!(f, "[")?;

            for (idx, &expr_id) in self.e.elems.iter().enumerate() {
                if idx > 0 {
                    write!(f, ", ")?;
                }

                write!(f, "{}", self.libsl.exprs[expr_id].display(self.libsl))?;
            }

            write!(f, "]")
        })
    }
}

make_display_struct!(
    ExprQualifiedAccessDisplay { e } for ast::ExprQualifiedAccess
    where precedence: ExprPrec = ExprPrec::Atomic,
);

impl Display for ExprQualifiedAccessDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        display_parens(f, self.e.precedence(), self.prec, |f| {
            write!(
                f,
                "{}",
                self.libsl.qualified_accesses[self.e.access].display(self.libsl),
            )
        })
    }
}

make_display_struct!(
    ExprPrevDisplay { e } for ast::ExprPrev
    where precedence: ExprPrec = ExprPrec::Atomic,
);

impl Display for ExprPrevDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        display_parens(f, self.e.precedence(), self.prec, |f| {
            write!(
                f,
                "{}'",
                self.libsl.qualified_accesses[self.e.access].display(self.libsl),
            )
        })
    }
}

make_display_struct!(
    ExprProcCallDisplay { e } for ast::ExprProcCall
    where precedence: ExprPrec = ExprPrec::Atomic,
);

impl Display for ExprProcCallDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        display_parens(f, self.e.precedence(), self.prec, |f| {
            write!(
                f,
                "{}",
                self.libsl.qualified_accesses[self.e.callee].display(self.libsl)
            )?;

            if !self.e.generics.is_empty() {
                write!(f, "<")?;

                for (idx, ty_arg) in self.e.generics.iter().enumerate() {
                    if idx > 0 {
                        write!(f, ", ")?;
                    }

                    write!(f, "{}", ty_arg.display(self.libsl))?;
                }

                write!(f, ">")?;
            }

            write!(f, "(")?;

            for (idx, &expr_id) in self.e.args.iter().enumerate() {
                if idx > 0 {
                    write!(f, ", ")?;
                }

                write!(f, "{}", self.libsl.exprs[expr_id].display(self.libsl))?;
            }

            write!(f, ")")
        })
    }
}

make_display_struct!(
    ExprActionCallDisplay { e } for ast::ExprActionCall
    where precedence: ExprPrec = ExprPrec::Atomic,
);

impl Display for ExprActionCallDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        display_parens(f, self.e.precedence(), self.prec, |f| {
            write!(f, "{}", self.e.name)?;

            if !self.e.generics.is_empty() {
                write!(f, "<")?;

                for (idx, ty_arg) in self.e.generics.iter().enumerate() {
                    if idx > 0 {
                        write!(f, ", ")?;
                    }

                    write!(f, "{}", ty_arg.display(self.libsl))?;
                }

                write!(f, ">")?;
            }

            write!(f, "(")?;

            for (idx, &expr_id) in self.e.args.iter().enumerate() {
                if idx > 0 {
                    write!(f, ", ")?;
                }

                write!(f, "{}", self.libsl.exprs[expr_id].display(self.libsl))?;
            }

            write!(f, ")")
        })
    }
}

make_display_struct!(
    ExprInstantiateDisplay { e } for ast::ExprInstantiate
    where precedence: ExprPrec = ExprPrec::Atomic,
);

impl Display for ExprInstantiateDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        display_parens(f, self.e.precedence(), self.prec, |f| {
            write!(f, "new {}", self.e.name)?;

            if !self.e.generics.is_empty() {
                write!(f, "<")?;

                for (idx, ty_arg) in self.e.generics.iter().enumerate() {
                    if idx > 0 {
                        write!(f, ", ")?;
                    }

                    write!(f, "{}", ty_arg.display(self.libsl))?;
                }

                write!(f, ">")?;
            }

            write!(f, "(")?;

            for (idx, arg) in self.e.args.iter().enumerate() {
                if idx > 0 {
                    write!(f, ", ")?;
                }

                let expr_id = match arg {
                    ast::ConstructorArg::State(expr_id) => {
                        write!(f, "state = ")?;

                        *expr_id
                    }

                    ast::ConstructorArg::Var(name, expr_id) => {
                        write!(f, "{name} = ")?;

                        *expr_id
                    }
                };

                write!(f, "{}", self.libsl.exprs[expr_id].display(self.libsl))?;
            }

            write!(f, ")")
        })
    }
}

make_display_struct!(
    ExprHasConceptDisplay { e } for ast::ExprHasConcept
    where precedence: ExprPrec = ExprPrec::Cast,
);

impl Display for ExprHasConceptDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        display_parens(f, self.e.precedence(), self.prec, |f| {
            write!(
                f,
                "{lhs} has {concept}",
                lhs = self.libsl.qualified_accesses[self.e.scrutinee].display(self.libsl),
                concept = self.e.concept,
            )
        })
    }
}

make_display_struct!(
    ExprCastDisplay { e } for ast::ExprCast
    where precedence: ExprPrec = ExprPrec::Cast,
);

impl Display for ExprCastDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        display_parens(f, self.e.precedence(), self.prec, |f| {
            write!(
                f,
                "{lhs} as {rhs}",
                lhs = self.libsl.exprs[self.e.expr].display_prec(self.libsl, self.e.precedence()),
                rhs = self.libsl.ty_exprs[self.e.ty_expr].display(self.libsl),
            )
        })
    }
}

make_display_struct!(
    ExprTyCompareDisplay { e } for ast::ExprTyCompare
    where precedence: ExprPrec = ExprPrec::TyCmp,
);

impl Display for ExprTyCompareDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        display_parens(f, self.e.precedence(), self.prec, |f| {
            write!(
                f,
                "{lhs} is {rhs}",
                lhs = self.libsl.exprs[self.e.expr].display_prec(self.libsl, self.e.precedence()),
                rhs = self.libsl.ty_exprs[self.e.ty_expr].display(self.libsl),
            )
        })
    }
}

make_display_struct!(
    ExprUnaryDisplay { e } for ast::ExprUnary
    where precedence: ExprPrec = match e.op {
        ast::UnOp::Plus | ast::UnOp::Neg | ast::UnOp::BitNot | ast::UnOp::Not => ExprPrec::Unary,
    },
);

impl Display for ExprUnaryDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        display_parens(f, self.e.precedence(), self.prec, |f| {
            write!(
                f,
                "{op}{expr}",
                op = self.e.op,
                expr = self.libsl.exprs[self.e.expr].display_prec(self.libsl, self.e.precedence()),
            )
        })
    }
}

impl Display for ast::UnOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                ast::UnOp::Plus => "+",
                ast::UnOp::Neg => "-",
                ast::UnOp::BitNot => "~",
                ast::UnOp::Not => "!",
            }
        )
    }
}

make_display_struct!(
    ExprBinaryDisplay { e } for ast::ExprBinary
    where precedence: ExprPrec = match e.op {
        ast::BinOp::Mul | ast::BinOp::Div | ast::BinOp::Mod => ExprPrec::Mul,
        ast::BinOp::Add | ast::BinOp::Sub => ExprPrec::Add,
        ast::BinOp::Sal | ast::BinOp::Sar | ast::BinOp::Shl | ast::BinOp::Shr => ExprPrec::Shift,
        ast::BinOp::BitOr => ExprPrec::BitOr,
        ast::BinOp::BitXor => ExprPrec::BitXor,
        ast::BinOp::BitAnd => ExprPrec::BitAnd,

        ast::BinOp::Lt
        | ast::BinOp::Le
        | ast::BinOp::Gt
        | ast::BinOp::Ge
        | ast::BinOp::Eq
        | ast::BinOp::Ne => ExprPrec::Cmp,

        ast::BinOp::Or => ExprPrec::Or,
        ast::BinOp::And => ExprPrec::And,
    },
);

impl Display for ExprBinaryDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let lassoc_or_prec = |prec| match &self.libsl.exprs[self.e.lhs].kind {
            // allow left association without parentheses.
            ast::ExprKind::Binary(e) if e.op == self.e.op => self.e.precedence(),

            // otherwise require the supplied (presumably higher) precedence.
            _ => prec,
        };

        display_parens(f, self.e.precedence(), self.prec, |f| match self.e.op {
            ast::BinOp::Mul
            | ast::BinOp::Div
            | ast::BinOp::Mod
            | ast::BinOp::Add
            | ast::BinOp::Sub
            | ast::BinOp::Sal
            | ast::BinOp::Sar
            | ast::BinOp::Shl
            | ast::BinOp::Shr
            | ast::BinOp::Lt
            | ast::BinOp::Le
            | ast::BinOp::Gt
            | ast::BinOp::Ge
            | ast::BinOp::Eq
            | ast::BinOp::Ne => {
                write!(
                    f,
                    "{lhs} {op} {rhs}",
                    lhs =
                        self.libsl.exprs[self.e.lhs].display_prec(self.libsl, self.e.precedence()),
                    op = self.e.op,
                    rhs = self.libsl.exprs[self.e.rhs]
                        .display_prec(self.libsl, self.e.precedence().higher()),
                )
            }

            ast::BinOp::BitOr | ast::BinOp::BitXor | ast::BinOp::BitAnd => {
                // skip over a bunch of precedence levels straight to shift ops for clarity because
                // these operators' precedence is very confusing.
                let non_assoc_prec = ExprPrec::Shift;

                write!(
                    f,
                    "{lhs} {op} {rhs}",
                    lhs = self.libsl.exprs[self.e.lhs]
                        .display_prec(self.libsl, lassoc_or_prec(non_assoc_prec)),
                    op = self.e.op,
                    rhs = self.libsl.exprs[self.e.rhs].display_prec(self.libsl, non_assoc_prec),
                )
            }

            ast::BinOp::Or | ast::BinOp::And => {
                // skip over a bunch of precedence levels straight to bitwise AND for clarity
                // because these operator's precedence is very confusing.
                let non_assoc_prec = ExprPrec::BitAnd;

                write!(
                    f,
                    "{lhs} {op} {rhs}",
                    lhs = self.libsl.exprs[self.e.lhs]
                        .display_prec(self.libsl, lassoc_or_prec(non_assoc_prec)),
                    op = self.e.op,
                    rhs = self.libsl.exprs[self.e.rhs].display_prec(self.libsl, non_assoc_prec),
                )
            }
        })
    }
}

impl Display for ast::BinOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                ast::BinOp::Mul => "*",
                ast::BinOp::Div => "/",
                ast::BinOp::Mod => "%",
                ast::BinOp::Add => "+",
                ast::BinOp::Sub => "-",
                ast::BinOp::Sal => "<<",
                ast::BinOp::Sar => ">>",
                ast::BinOp::Shl => "<<<",
                ast::BinOp::Shr => ">>>",
                ast::BinOp::BitOr => "|",
                ast::BinOp::BitXor => "^",
                ast::BinOp::BitAnd => "&",
                ast::BinOp::Lt => "<",
                ast::BinOp::Le => "<=",
                ast::BinOp::Gt => ">",
                ast::BinOp::Ge => ">=",
                ast::BinOp::Eq => "==",
                ast::BinOp::Ne => "!=",
                ast::BinOp::Or => "||",
                ast::BinOp::And => "&&",
            },
        )
    }
}

make_display_struct!(PrimitiveLitDisplay { l } for ast::PrimitiveLit);

impl Display for PrimitiveLitDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

make_display_struct!(QualifiedAccessDisplay { a } for ast::QualifiedAccess);

impl Display for QualifiedAccessDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

struct WhereClauseDisplay<'a> {
    ty_constraints: &'a [ast::TyConstraint],
    libsl: &'a LibSl,
}

impl Display for WhereClauseDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "where")?;

        for ty_constraint in self.ty_constraints {
            write!(f, "\n{INDENT}{}", ty_constraint.display(self.libsl))?;
        }

        Ok(())
    }
}

struct GenericsDisplay<'a> {
    generics: &'a [ast::Generic],
}

impl Display for GenericsDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "<")?;

        for (idx, generic) in self.generics.iter().enumerate() {
            if idx > 0 {
                write!(f, ", ")?;
            }

            write!(f, "{generic}")?;
        }

        write!(f, ">")
    }
}

impl Display for ast::Generic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(variance) = &self.variance {
            write!(
                f,
                "{} ",
                match variance {
                    ast::Variance::Covariant => "out",
                    ast::Variance::Contravariant => "in",
                    ast::Variance::Invariant => "in out",
                }
            )?;
        }

        write!(f, "{}", self.name)
    }
}

make_display_struct!(TyArgDisplay { t } for ast::TyArg);

impl Display for TyArgDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

make_display_struct!(TyConstraintDisplay { t } for ast::TyConstraint);

impl Display for TyConstraintDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

impl Display for ast::IntLit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

make_display_struct!(QualifiedTyNameDisplay { t } for ast::QualifiedTyName);

impl Display for QualifiedTyNameDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.t.ty_name)?;

        if !self.t.generics.is_empty() {
            write!(f, "<")?;

            for (idx, generic) in self.t.generics.iter().enumerate() {
                if idx > 0 {
                    write!(f, ", ")?;
                }

                write!(f, "{generic}")?;
            }
        }

        Ok(())
    }
}

impl Display for ast::FullName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (idx, component) in self.components.iter().enumerate() {
            if idx > 0 {
                write!(f, ".")?;
            }

            write!(f, "{component}")?;
        }

        Ok(())
    }
}

impl Display for ast::Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", Identifier(&self.name))
    }
}
