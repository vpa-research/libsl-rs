//! Implements dumping the AST nodes back as LibSL source text.
//!
//! The AST built by [parsing](LibSL::parse_file) can always by converted to a syntactically correct
//! LibSL source. However, the module performs no additional checks to ensure that, and invalid text
//! may still be emitted if you, for instance, put an illegal identifier as the name for a type or
//! insert a wrong node into the AST (such as a state declaration in the global scope).

use std::fmt::{self, Display, Write as _};

use crate::{DeclId, LibSl, ast};

const INDENT: &str = "    ";

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
#[derive(Debug, Clone, Copy)]
pub struct QuotedString<'a>(&'a str);

impl Display for QuotedString<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
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
        todo!()
    }
}

impl ast::File {
    /// Returns an object that implements [Display] to convert the [ast::File] back to LibSL source
    /// text.
    pub fn display<'a>(&'a self, libsl: &'a LibSl) -> FileDisplay<'a> {
        FileDisplay { f: self, libsl }
    }
}

/// A helper struct that writes the [ast::File] out as LibSL source text.
#[derive(Debug, Clone, Copy)]
pub struct FileDisplay<'a> {
    f: &'a ast::File,
    libsl: &'a LibSl,
}

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

impl ast::Header {
    /// Returns an object that implements [Display] to convert the [ast::Header] back to LibSL
    /// source text.
    pub fn display<'a>(&'a self, libsl: &'a LibSl) -> HeaderDisplay<'a> {
        HeaderDisplay { h: self, libsl }
    }
}

/// A helper struct that writes the [ast::Header] out as LibSL source text.
#[derive(Debug, Clone, Copy)]
pub struct HeaderDisplay<'a> {
    h: &'a ast::Header,
    libsl: &'a LibSl,
}

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

impl ast::Decl {
    /// Returns an object that implements [Display] to convert the [ast::Decl] back to LibSL source
    /// text.
    pub fn display<'a>(&'a self, libsl: &'a LibSl) -> DeclDisplay<'a> {
        DeclDisplay { d: self, libsl }
    }
}

/// A helper struct that writes the [ast::Decl] out as LibSL source text.
#[derive(Debug, Clone, Copy)]
pub struct DeclDisplay<'a> {
    d: &'a ast::Decl,
    libsl: &'a LibSl,
}

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

impl ast::DeclImport {
    /// Returns an object that implements [Display] to convert the [ast::DeclImport] back to LibSL
    /// source text.
    pub fn display<'a>(&'a self, libsl: &'a LibSl) -> DeclImportDisplay<'a> {
        DeclImportDisplay { d: self, libsl }
    }
}

/// A helper struct that writes the [ast::DeclImport] out as LibSL source text.
#[derive(Debug, Clone, Copy)]
pub struct DeclImportDisplay<'a> {
    d: &'a ast::DeclImport,
    libsl: &'a LibSl,
}

impl Display for DeclImportDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "import {};", self.d.path)
    }
}

impl ast::DeclInclude {
    /// Returns an object that implements [Display] to convert the [ast::DeclInclude] back to LibSL
    /// source text.
    pub fn display<'a>(&'a self, libsl: &'a LibSl) -> DeclIncludeDisplay<'a> {
        DeclIncludeDisplay { d: self, libsl }
    }
}

/// A helper struct that writes the [ast::DeclInclude] out as LibSL source text.
#[derive(Debug, Clone, Copy)]
pub struct DeclIncludeDisplay<'a> {
    d: &'a ast::DeclInclude,
    libsl: &'a LibSl,
}

impl Display for DeclIncludeDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "include {};", self.d.path)
    }
}

impl ast::DeclSemanticTy {
    /// Returns an object that implements [Display] to convert the [ast::DeclSemanticTy] back to
    /// LibSL source text.
    pub fn display<'a>(&'a self, libsl: &'a LibSl) -> DeclSemanticTyDisplay<'a> {
        DeclSemanticTyDisplay { d: self, libsl }
    }
}

/// A helper struct that writes the [ast::DeclSemanticTy] out as LibSL source text.
#[derive(Debug, Clone, Copy)]
pub struct DeclSemanticTyDisplay<'a> {
    d: &'a ast::DeclSemanticTy,
    libsl: &'a LibSl,
}

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

impl ast::DeclTyAlias {
    /// Returns an object that implements [Display] to convert the [ast::DeclTyAlias] back to LibSL
    /// source text.
    pub fn display<'a>(&'a self, libsl: &'a LibSl) -> DeclTyAliasDisplay<'a> {
        DeclTyAliasDisplay { d: self, libsl }
    }
}

/// A helper struct that writes the [ast::DeclTyAlias] out as LibSL source text.
#[derive(Debug, Clone, Copy)]
pub struct DeclTyAliasDisplay<'a> {
    d: &'a ast::DeclTyAlias,
    libsl: &'a LibSl,
}

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

impl ast::DeclStruct {
    /// Returns an object that implements [Display] to convert the [ast::DeclStruct] back to LibSL
    /// source text.
    pub fn display<'a>(&'a self, libsl: &'a LibSl) -> DeclStructDisplay<'a> {
        DeclStructDisplay { d: self, libsl }
    }
}

/// A helper struct that writes the [ast::DeclStruct] out as LibSL source text.
#[derive(Debug, Clone, Copy)]
pub struct DeclStructDisplay<'a> {
    d: &'a ast::DeclStruct,
    libsl: &'a LibSl,
}

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

                for (idx, &decl_id) in self.d.decls.iter().enumerate() {
                    writeln!(f, "{}", self.libsl.decls[decl_id].display(self.libsl))?;
                }
            }

            write!(f, "}}")?;
        }

        Ok(())
    }
}

impl ast::DeclEnum {
    /// Returns an object that implements [Display] to convert the [ast::DeclEnum] back to LibSL
    /// source text.
    pub fn display<'a>(&'a self, libsl: &'a LibSl) -> DeclEnumDisplay<'a> {
        DeclEnumDisplay { d: self, libsl }
    }
}

/// A helper struct that writes the [ast::DeclEnum] out as LibSL source text.
#[derive(Debug, Clone, Copy)]
pub struct DeclEnumDisplay<'a> {
    d: &'a ast::DeclEnum,
    libsl: &'a LibSl,
}

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

impl ast::DeclAnnotation {
    /// Returns an object that implements [Display] to convert the [ast::DeclAnnotation] back to
    /// LibSL source text.
    pub fn display<'a>(&'a self, libsl: &'a LibSl) -> DeclAnnotationDisplay<'a> {
        DeclAnnotationDisplay { d: self, libsl }
    }
}

/// A helper struct that writes the [ast::DeclAnnotation] out as LibSL source text.
#[derive(Debug, Clone, Copy)]
pub struct DeclAnnotationDisplay<'a> {
    d: &'a ast::DeclAnnotation,
    libsl: &'a LibSl,
}

impl Display for DeclAnnotationDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "annotation {}(", self.d.name.display(self.libsl))?;

        if !self.d.params.is_empty() {
            writeln!(f);
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

impl ast::DeclAction {
    /// Returns an object that implements [Display] to convert the [ast::DeclAction] back to LibSL
    /// source text.
    pub fn display<'a>(&'a self, libsl: &'a LibSl) -> DeclActionDisplay<'a> {
        DeclActionDisplay { d: self, libsl }
    }
}

/// A helper struct that writes the [ast::DeclAction] out as LibSL source text.
#[derive(Debug, Clone, Copy)]
pub struct DeclActionDisplay<'a> {
    d: &'a ast::DeclAction,
    libsl: &'a LibSl,
}

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

impl ast::DeclAutomaton {
    /// Returns an object that implements [Display] to convert the [ast::DeclAutomaton] back to
    /// LibSL source text.
    pub fn display<'a>(&'a self, libsl: &'a LibSl) -> DeclAutomatonDisplay<'a> {
        DeclAutomatonDisplay { d: self, libsl }
    }
}

/// A helper struct that writes the [ast::DeclAutomaton] out as LibSL source text.
#[derive(Debug, Clone, Copy)]
pub struct DeclAutomatonDisplay<'a> {
    d: &'a ast::DeclAutomaton,
    libsl: &'a LibSl,
}

impl Display for DeclAutomatonDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

impl ast::DeclFunction {
    /// Returns an object that implements [Display] to convert the [ast::DeclFunction] back to LibSL
    /// source text.
    pub fn display<'a>(&'a self, libsl: &'a LibSl) -> DeclFunctionDisplay<'a> {
        DeclFunctionDisplay { d: self, libsl }
    }
}

/// A helper struct that writes the [ast::DeclFunction] out as LibSL source text.
#[derive(Debug, Clone, Copy)]
pub struct DeclFunctionDisplay<'a> {
    d: &'a ast::DeclFunction,
    libsl: &'a LibSl,
}

impl Display for DeclFunctionDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

impl ast::DeclVariable {
    /// Returns an object that implements [Display] to convert the [ast::DeclVariable] back to LibSL
    /// source text.
    pub fn display<'a>(&'a self, libsl: &'a LibSl) -> DeclVariableDisplay<'a> {
        DeclVariableDisplay { d: self, libsl }
    }
}

/// A helper struct that writes the [ast::DeclVariable] out as LibSL source text.
#[derive(Debug, Clone, Copy)]
pub struct DeclVariableDisplay<'a> {
    d: &'a ast::DeclVariable,
    libsl: &'a LibSl,
}

impl Display for DeclVariableDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

impl ast::DeclState {
    /// Returns an object that implements [Display] to convert the [ast::DeclState] back to LibSL
    /// source text.
    pub fn display<'a>(&'a self, libsl: &'a LibSl) -> DeclStateDisplay<'a> {
        DeclStateDisplay { d: self, libsl }
    }
}

/// A helper struct that writes the [ast::DeclState] out as LibSL source text.
#[derive(Debug, Clone, Copy)]
pub struct DeclStateDisplay<'a> {
    d: &'a ast::DeclState,
    libsl: &'a LibSl,
}

impl Display for DeclStateDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

impl ast::DeclShift {
    /// Returns an object that implements [Display] to convert the [ast::DeclShift] back to LibSL
    /// source text.
    pub fn display<'a>(&'a self, libsl: &'a LibSl) -> DeclShiftDisplay<'a> {
        DeclShiftDisplay { d: self, libsl }
    }
}

/// A helper struct that writes the [ast::DeclShift] out as LibSL source text.
#[derive(Debug, Clone, Copy)]
pub struct DeclShiftDisplay<'a> {
    d: &'a ast::DeclShift,
    libsl: &'a LibSl,
}

impl Display for DeclShiftDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

impl ast::DeclConstructor {
    /// Returns an object that implements [Display] to convert the [ast::DeclConstructor] back to
    /// LibSL source text.
    pub fn display<'a>(&'a self, libsl: &'a LibSl) -> DeclConstructorDisplay<'a> {
        DeclConstructorDisplay { d: self, libsl }
    }
}

/// A helper struct that writes the [ast::DeclConstructor] out as LibSL source text.
#[derive(Debug, Clone, Copy)]
pub struct DeclConstructorDisplay<'a> {
    d: &'a ast::DeclConstructor,
    libsl: &'a LibSl,
}

impl Display for DeclConstructorDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

impl ast::DeclDestructor {
    /// Returns an object that implements [Display] to convert the [ast::DeclDestructor] back to
    /// LibSL source text.
    pub fn display<'a>(&'a self, libsl: &'a LibSl) -> DeclDestructorDisplay<'a> {
        DeclDestructorDisplay { d: self, libsl }
    }
}

/// A helper struct that writes the [ast::DeclDestructor] out as LibSL source text.
#[derive(Debug, Clone, Copy)]
pub struct DeclDestructorDisplay<'a> {
    d: &'a ast::DeclDestructor,
    libsl: &'a LibSl,
}

impl Display for DeclDestructorDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

impl ast::DeclProc {
    /// Returns an object that implements [Display] to convert the [ast::DeclProc] back to LibSL
    /// source text.
    pub fn display<'a>(&'a self, libsl: &'a LibSl) -> DeclProcDisplay<'a> {
        DeclProcDisplay { d: self, libsl }
    }
}

/// A helper struct that writes the [ast::DeclProc] out as LibSL source text.
#[derive(Debug, Clone, Copy)]
pub struct DeclProcDisplay<'a> {
    d: &'a ast::DeclProc,
    libsl: &'a LibSl,
}

impl Display for DeclProcDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

impl ast::TyExpr {
    /// Returns an object that implements [Display] to convert the [ast::TyExpr] back to LibSL
    /// source text.
    pub fn display<'a>(&'a self, libsl: &'a LibSl) -> TyExprDisplay<'a> {
        TyExprDisplay { t: self, libsl }
    }
}

/// A helper struct that writes the [ast::TyExpr] out as LibSL source text.
#[derive(Debug, Clone, Copy)]
pub struct TyExprDisplay<'a> {
    t: &'a ast::TyExpr,
    libsl: &'a LibSl,
}

impl Display for TyExprDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

impl ast::Expr {
    /// Returns an object that implements [Display] to convert the [ast::Expr] back to LibSL source
    /// text.
    pub fn display<'a>(&'a self, libsl: &'a LibSl) -> ExprDisplay<'a> {
        ExprDisplay { e: self, libsl }
    }
}

/// A helper struct that writes the [ast::Expr] out as LibSL source text.
#[derive(Debug, Clone, Copy)]
pub struct ExprDisplay<'a> {
    e: &'a ast::Expr,
    libsl: &'a LibSl,
}

impl Display for ExprDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

impl ast::Annotation {
    /// Returns an object that implements [Display] to convert the [ast::Annotation] back to LibSL
    /// source text.
    pub fn display<'a>(&'a self, libsl: &'a LibSl) -> AnnotationDisplay<'a> {
        AnnotationDisplay { a: self, libsl }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct AnnotationDisplay<'a> {
    a: &'a ast::Annotation,
    libsl: &'a LibSl,
}

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

impl ast::Generic {
    /// Returns an object that implements [Display] to convert the [ast::Generic] back to LibSL
    /// source text.
    pub fn display<'a>(&'a self, libsl: &'a LibSl) -> GenericDisplay<'a> {
        GenericDisplay { g: self, libsl }
    }
}

/// A helper struct that writes the [ast::Generic] out as LibSL source text.
pub struct GenericDisplay<'a> {
    g: &'a ast::Generic,
    libsl: &'a LibSl,
}

impl Display for GenericDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

impl ast::TyConstraint {
    /// Returns an object that implements [Display] to convert the [ast::TyConstraint] back to LibSL
    /// source text.
    pub fn display<'a>(&'a self, libsl: &'a LibSl) -> TyConstraintDisplay<'a> {
        TyConstraintDisplay { t: self, libsl }
    }
}

/// A helper struct that writes the [ast::QualifiedTyName] out as LibSL source text.
#[derive(Debug, Clone, Copy)]
pub struct TyConstraintDisplay<'a> {
    t: &'a ast::TyConstraint,
    libsl: &'a LibSl,
}

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

impl ast::QualifiedTyName {
    /// Returns an object that implements [Display] to convert the [ast::QualifiedTyName] back to
    /// LibSL source text.
    pub fn display<'a>(&'a self, libsl: &'a LibSl) -> QualifiedTyNameDisplay<'a> {
        QualifiedTyNameDisplay { t: self, libsl }
    }
}

/// A helper struct that writes the [ast::QualifiedTyName] out as LibSL source text.
#[derive(Debug, Clone, Copy)]
pub struct QualifiedTyNameDisplay<'a> {
    t: &'a ast::QualifiedTyName,
    libsl: &'a LibSl,
}

impl Display for QualifiedTyNameDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

impl ast::Name {
    /// Returns an object that implements [Display] to convert the [ast::Name] back to LibSL source
    /// text.
    pub fn display<'a>(&'a self, libsl: &'a LibSl) -> NameDisplay<'a> {
        NameDisplay { n: self, libsl }
    }
}

/// A helper struct that writes the [ast::Name] out as LibSL source text.
#[derive(Debug, Clone, Copy)]
pub struct NameDisplay<'a> {
    n: &'a ast::Name,
    libsl: &'a LibSl,
}

impl Display for NameDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}
