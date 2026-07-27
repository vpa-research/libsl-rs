use std::fmt::{self, Display};

pub(crate) fn format_sep_list<T, F>(elems: &[T], f: F) -> impl Display
where
    F: Fn(&mut fmt::Formatter<'_>, &T) -> fmt::Result,
{
    fmt::from_fn(move |fmt| {
        for (idx, elem) in elems.iter().enumerate() {
            if idx > 0 {
                write!(fmt, ", ")?;
            }

            f(fmt, elem)?;
        }

        Ok(())
    })
}

pub(crate) fn format_list<T, F>(elems: &[T], f: F) -> impl Display
where
    F: Fn(&mut fmt::Formatter<'_>, &T) -> fmt::Result,
{
    fmt::from_fn(move |fmt| {
        for (idx, elem) in elems.iter().enumerate() {
            if idx > 0 && !(idx == 1 && elems.len() == 2) {
                write!(fmt, ", ")?;
            }

            if idx > 0 && idx + 1 == elems.len() {
                if idx == 1 {
                    write!(fmt, " ")?;
                }

                write!(fmt, "and ")?;
            }

            f(fmt, elem)?;
        }

        Ok(())
    })
}
