//! Implements dumping the AST nodes back as LibSL source text.
//!
//! The AST built by [parsing](LibSl::parse_file) can always by converted to a syntactically correct
//! LibSL source. However, the module performs no additional checks to ensure that, and invalid text
//! may still be emitted if you, for instance, put an illegal identifier as the name for a type or
//! insert a wrong node into the AST (such as a state declaration in the global scope).

use std::fmt::{self, Display, Write as _};

use crate::{DeclId, LibSl, ast};

const INDENT: &str = "    ";

macro_rules! make_display_struct {
    ($name:ident { $field:ident } for $ast:ty) => {
        impl $ast {
            #[doc = concat!(
                                "Returns an object that implements [Display] to convert the [",
                                stringify!($ast),
                                "] back to LibSL source text.",
                            )]
            pub fn display<'a>(&'a self, libsl: &'a LibSl) -> $name<'a> {
                $name {
                    $field: self,
                    libsl,
                }
            }
        }

        #[doc = concat!(
                            "A helper struct that writes the [",
                            stringify!($ast),
                            "] out as LibSL source text."
                        )]
        #[derive(Debug, Clone, Copy)]
        pub struct $name<'a> {
            $field: &'a $ast,
            libsl: &'a LibSl,
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

/// A wrapper type that formats a string by enclosing it in double quotes and escaping characters if
/// necessary according to LibSL's rules.
///
/// If the string contains a `\n` or a `\r` character, the result will not be a legal LibSL string.
#[derive(Debug, Clone, Copy)]
pub struct QuotedString<'a>(&'a str);

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
pub struct Identifier<'a>(&'a str);

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
        writeln!(f, "types {{")?;

        {
            let mut f = IndentedWriter::new(INDENT, f);

            for (idx, &decl_id) in self.decls.iter().enumerate() {
                if idx > 0 {
                    writeln!(f)?;
                }

                writeln!(f, "{}", self.libsl.decls[decl_id].display(self.libsl))?;
            }
        }

        write!(f, "}}")
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
                writeln!(f, " {{")?;

                {
                    let mut f = IndentedWriter::new(INDENT, f);

                    for entry in values {
                        writeln!(
                            f,
                            "{name}: {value};",
                            name = entry.name.display(self.libsl),
                            value = self.libsl.exprs[entry.expr].display(self.libsl),
                        )?;
                    }
                }

                write!(f, "}}")
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
                writeln!(f, " {{")?;
            } else {
                writeln!(f, "\n{{")?;
            }

            {
                let mut f = IndentedWriter::new(INDENT, f);

                for &decl_id in &self.d.decls {
                    writeln!(f, "{}", self.libsl.decls[decl_id].display(self.libsl))?;
                }
            }

            write!(f, "}}")?;
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

        write!(f, "enum {} {{", self.d.ty_name.display(self.libsl))?;

        for variant in &self.d.variants {
            write!(
                f,
                "\n{INDENT}{name} = {value};",
                name = variant.name.display(self.libsl),
                value = variant.value,
            )?;
        }

        write!(f, "}}")
    }
}

make_display_struct!(DeclAnnotationDisplay { d } for ast::DeclAnnotation);

impl Display for DeclAnnotationDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "annotation {}(", self.d.name.display(self.libsl))?;

        if !self.d.params.is_empty() {
            writeln!(f)?;
        }

        for param in &self.d.params {
            writeln!(
                f,
                "{INDENT}{name}: {ty_expr},",
                name = param.name.display(self.libsl),
                ty_expr = self.libsl.ty_exprs[param.ty_expr].display(self.libsl),
            )?;
        }

        write!(f, ");")
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
                    libsl: self.libsl,
                }
            )?;
        }

        write!(f, "{}(", self.d.name.display(self.libsl))?;

        if !self.d.params.is_empty() {
            writeln!(f)?;
        }

        for param in &self.d.params {
            for annotation in &self.d.annotations {
                writeln!(f, "{}", annotation.display(self.libsl))?;
            }

            writeln!(
                f,
                "{INDENT}{name}: {ty_expr}",
                name = param.name.display(self.libsl),
                ty_expr = self.libsl.ty_exprs[param.ty_expr].display(self.libsl),
            )?;
        }

        write!(f, ")")?;

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
            writeln!(f, "(")?;

            {
                let mut f = IndentedWriter::new(INDENT, f);

                for &decl_id in &self.d.constructor_variables {
                    writeln!(f, "{},", self.libsl.decls[decl_id].display(self.libsl))?;
                }
            }

            write!(f, ")")?;
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

                write!(f, "{}", concept.display(self.libsl))?;
            }

            writeln!(f)?;
        }

        write!(f, "{{")?;

        {
            let mut f = IndentedWriter::new(INDENT, f);

            for &decl_id in &self.d.decls {
                writeln!(f)?;
                writeln!(f, "{}", self.libsl.decls[decl_id].display(self.libsl))?;
            }
        }

        write!(f, "}}")
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
            write!(f, "{}.", automaton_name.display(self.libsl))?;
        }

        if self.d.is_method {
            write!(f, "*.")?;
        }

        write!(f, "{}", self.d.name.display(self.libsl))?;

        if !self.d.generics.is_empty() {
            write!(
                f,
                "{}",
                GenericsDisplay {
                    generics: &self.d.generics,
                    libsl: self.libsl,
                }
            )?;
        }

        write!(f, "(")?;

        {
            let mut f = IndentedWriter::new(INDENT, f);

            for (idx, param) in self.d.params.iter().enumerate() {
                writeln!(
                    f,
                    "{}{}",
                    param.display(self.libsl),
                    if idx + 1 == self.d.params.len() {
                        ""
                    } else {
                        ","
                    }
                )?;
            }
        }

        write!(f, ")")?;

        if let Some(ty_expr_id) = self.d.ret_ty_expr {
            write!(
                f,
                " : {}",
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

            write!(f, "{}", body.display(self.libsl))?;
        } else {
            write!(f, ";")?;
        }

        Ok(())
    }
}

make_display_struct!(DeclVariableDisplay { d } for ast::DeclVariable);

impl Display for DeclVariableDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

make_display_struct!(DeclStateDisplay { d } for ast::DeclState);

impl Display for DeclStateDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

make_display_struct!(DeclShiftDisplay { d } for ast::DeclShift);

impl Display for DeclShiftDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

make_display_struct!(DeclConstructorDisplay { d } for ast::DeclConstructor);

impl Display for DeclConstructorDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

make_display_struct!(DeclDestructorDisplay { d } for ast::DeclDestructor);

impl Display for DeclDestructorDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

make_display_struct!(DeclProcDisplay { d } for ast::DeclProc);

impl Display for DeclProcDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
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
            name = self.p.name.display(self.libsl),
            ty_expr = self.libsl.ty_exprs[self.p.ty_expr].display(self.libsl),
        )
    }
}

make_display_struct!(FunctionBodyDisplay { b } for ast::FunctionBody);

impl Display for FunctionBodyDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{{")?;

        if !self.b.contracts.is_empty() || !self.b.stmts.is_empty() {
            writeln!(f)?;
        }

        {
            let mut f = IndentedWriter::new(INDENT, f);

            for contract in &self.b.contracts {
                writeln!(f, "{}", contract.display(self.libsl))?;
            }

            if !self.b.contracts.is_empty() && !self.b.stmts.is_empty() {
                writeln!(f)?;
            }

            for &stmt_id in &self.b.stmts {
                writeln!(f, "{}", self.libsl.stmts[stmt_id].display(self.libsl))?;
            }
        }

        write!(f, "}}")
    }
}

make_display_struct!(ContractDisplay { c } for ast::Contract);

impl Display for ContractDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

make_display_struct!(TyExprDisplay { t } for ast::TyExpr);

impl Display for TyExprDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

make_display_struct!(StmtDisplay { s } for ast::Stmt);

impl Display for StmtDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

make_display_struct!(ExprDisplay { e } for ast::Expr);

impl Display for ExprDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

make_display_struct!(AnnotationDisplay { a } for ast::Annotation);

impl Display for AnnotationDisplay<'_> {
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
    libsl: &'a LibSl,
}

impl Display for GenericsDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "<")?;

        for (idx, generic) in self.generics.iter().enumerate() {
            if idx > 0 {
                write!(f, ", ")?;
            }

            write!(f, "{}", generic.display(self.libsl))?;
        }

        write!(f, ">")
    }
}

make_display_struct!(GenericDisplay { g } for ast::Generic);

impl Display for GenericDisplay<'_> {
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
        todo!()
    }
}

make_display_struct!(FullNameDisplay { n } for ast::FullName);

impl Display for FullNameDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

make_display_struct!(NameDisplay { n } for ast::Name);

impl Display for NameDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}
