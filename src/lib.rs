//! # pretty-trait
//!
//! `pretty-trait` is a simple trait-based library for producing pretty debug output.  It is
//! intended to make it easy to render large tree-like structures (such as program syntax trees) in
//! such a way that long items are broken across multiple lines and indented.
//!
//! The core feature of this crate is the `Pretty` trait, which represents types that can be
//! pretty-printed.  This crate provides a number of built-in types implementing `Pretty`, which be
//! combined to implement a wide variety of formatting and layout strategies.  For many purposes,
//! you will not need to implement `Pretty` for your own types, but can instead convert your type
//! into a structure composed out of these built-in types.
//!
//! # Examples
//!
//! Converting a custom type to built-in `Pretty` types:
//!
//! ```
//! use pretty_trait::{Pretty, JoinExt, Group, Indent, Sep, delimited, Conditional, to_string};
//!
//! enum NestList {
//!     Atom(i32),
//!     List(Vec<NestList>),
//! }
//!
//! fn to_pretty(nest_list: &NestList) -> Box<Pretty> {
//!     match nest_list {
//!         &NestList::Atom(val) => Box::new(val.to_string()),
//!         &NestList::List(ref children) => {
//!             Box::new(Group::new(
//!                 "["
//!                     .join(Indent(
//!                         Sep(0)
//!                             .join(delimited(&",".join(Sep(1)), children.iter().map(to_pretty)))
//!                             .join(Conditional::OnlyBroken(",")),
//!                     )).join(Sep(0))
//!                     .join("]"),
//!             ))
//!         }
//!     }
//! }
//!
//! let max_line = Some(40);
//! let tab_size = 4;
//!
//! let small_list = NestList::List(vec![NestList::Atom(1), NestList::Atom(2), NestList::Atom(3)]);
//! assert_eq!(to_string(&to_pretty(&small_list), max_line, tab_size), "[1, 2, 3]");
//!
//! let large_list = NestList::List(vec![
//!     NestList::List(vec![
//!         NestList::Atom(1),
//!         NestList::Atom(2),
//!         NestList::Atom(3),
//!         NestList::Atom(4),
//!         NestList::Atom(5),
//!     ]),
//!     NestList::List(vec![
//!         NestList::Atom(6),
//!         NestList::Atom(7),
//!         NestList::Atom(8),
//!         NestList::Atom(9),
//!         NestList::Atom(10),
//!     ]),
//!     NestList::List(vec![
//!         NestList::List(vec![NestList::Atom(11), NestList::Atom(12), NestList::Atom(13)]),
//!         NestList::List(vec![NestList::Atom(14), NestList::Atom(15), NestList::Atom(16)]),
//!     ]),
//! ]);
//! let expected = "\
//! [
//!     [1, 2, 3, 4, 5],
//!     [6, 7, 8, 9, 10],
//!     [[11, 12, 13], [14, 15, 16]],
//! ]";
//! assert_eq!(to_string(&to_pretty(&large_list), max_line, tab_size), expected);
//! ```

use std::io;
use std::ops::{Add, Mul, Deref};

/// Represents the number of visual columns a value would take up if it were displayed on one line,
/// unless it is inherently multi-line.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Size {
    Size(usize),
    MultiLine,
}

impl Size {
    fn exceeds(self, max_line: Option<usize>) -> bool {
        self >
            match max_line {
                Some(max) => Size::Size(max),
                None => Size::MultiLine,
            }
    }
}

impl Add<Size> for Size {
    type Output = Size;

    fn add(self, other: Size) -> Size {
        match (self, other) {
            (Size::Size(size1), Size::Size(size2)) => Size::Size(size1 + size2),
            _ => Size::MultiLine,
        }
    }
}

impl Mul<usize> for Size {
    type Output = Size;

    fn mul(self, other: usize) -> Size {
        match self {
            Size::Size(size) => Size::Size(size * other),
            Size::MultiLine => Size::MultiLine,
        }
    }
}

pub struct Context<'a> {
    pub max_line: Option<usize>,
    pub tab_size: usize,
    pub indent_level: usize,
    pub broken: bool,
    pub writer: &'a mut io::Write,
}

impl<'a> Context<'a> {
    fn reborrow<'b>(&'b mut self) -> Context<'b> {
        Context {
            max_line: self.max_line,
            tab_size: self.tab_size,
            indent_level: self.indent_level,
            broken: self.broken,
            writer: &mut self.writer,
        }
    }
}

pub trait Pretty {
    fn size(&self) -> Size;

    fn pretty_write(&self, Context) -> io::Result<()>;
}

impl<'a, T: Pretty + ?Sized> Pretty for &'a T {
    fn size(&self) -> Size {
        (*self).size()
    }

    fn pretty_write(&self, context: Context) -> io::Result<()> {
        (*self).pretty_write(context)
    }
}

impl<'a, T: Pretty + ?Sized> Pretty for &'a mut T {
    fn size(&self) -> Size {
        (**self).size()
    }

    fn pretty_write(&self, context: Context) -> io::Result<()> {
        (**self).pretty_write(context)
    }
}

impl<'a, T: Pretty + ?Sized> Pretty for Box<T> {
    fn size(&self) -> Size {
        self.deref().size()
    }

    fn pretty_write(&self, context: Context) -> io::Result<()> {
        self.deref().pretty_write(context)
    }
}

impl<'a> Pretty for &'a str {
    fn size(&self) -> Size {
        Size::Size(self.chars().count())
    }

    fn pretty_write(&self, context: Context) -> io::Result<()> {
        write!(context.writer, "{}", self)
    }
}

impl Pretty for String {
    fn size(&self) -> Size {
        Size::Size(self.chars().count())
    }

    fn pretty_write(&self, context: Context) -> io::Result<()> {
        write!(context.writer, "{}", self)
    }
}

/// A wrapper which groups its contents so they will fit onto one line if possible, even if their
/// environment has been broken across multiple lines.
///
/// # Examples
///
/// ```
/// use pretty_trait::{JoinExt, Group, Sep, to_string};
///
/// let max_line = Some(10);
/// let tab_size = 4;
///
/// let expected_ungrouped = "\
/// hello
/// ,
/// world
/// !";
///
/// assert_eq!(
///     to_string(
///         &"hello"
///             .join(Sep(0))
///             .join(",")
///             .join(Sep(1))
///             .join("world")
///             .join(Sep(0))
///             .join("!"),
///         max_line,
///         tab_size,
///     ),
///     expected_ungrouped
/// );
///
/// let expected_grouped = "\
/// hello,
/// world!";
///
/// assert_eq!(
///     to_string(
///         &Group::new("hello".join(Sep(0)).join(","))
///             .join(Sep(1))
///             .join(Group::new("world".join(Sep(0)).join("!"))),
///         max_line,
///         tab_size,
///     ),
///     expected_grouped,
/// );
/// ```
#[derive(Clone, Copy, Debug)]
pub struct Group<T> {
    size: Size,
    content: T,
}

impl<T: Pretty> Group<T> {
    pub fn new(content: T) -> Self {
        Group {
            size: content.size(),
            content,
        }
    }
}

impl<T: Pretty> Pretty for Group<T> {
    fn size(&self) -> Size {
        self.size
    }

    fn pretty_write(&self, mut context: Context) -> io::Result<()> {
        context.broken = self.size.exceeds(context.max_line);
        self.content.pretty_write(context)
    }
}

/// A whitespace separator, rendered as a space if unbroken or a newline if broken.
///
/// The most common uses of `Sep` are `Sep(1)`, which renders as a single space or a newline, and
/// `Sep(0)`, which introduces a point where a newline will be inserted if the content is broken.
///
/// # Examples
///
/// Breaking into multiple lines:
///
/// ```
/// use pretty_trait::{JoinExt, Sep, to_string};
///
/// let max_line = Some(10);
/// let tab_size = 4;
///
/// // Exceeding the line length without a separator:
/// assert_eq!(to_string(&"hello".join("world!"), max_line, tab_size), "helloworld!");
///
/// let expected_broken = "\
/// hello
/// world!";
///
/// assert_eq!(
///     to_string(&"hello".join(Sep(0)).join("world!"), max_line, tab_size),
///     expected_broken
/// );
///
/// assert_eq!(
///     to_string(&"hello".join(Sep(1)).join("world!"), max_line, tab_size),
///     expected_broken
/// );
/// ```
///
/// Introducing spaces on a single line:
///
/// ```
/// # use pretty_trait::{JoinExt, Sep, to_string};
/// # let tab_size = 4;
/// #
/// assert_eq!(
///     to_string(&"hello".join(Sep(1)).join("world!"), None, tab_size),
///     "hello world!"
/// );
///
/// assert_eq!(
///     to_string(&"hello".join(Sep(0)).join("world!"), None, tab_size),
///     "helloworld!"
/// );
/// ```
#[derive(Clone, Copy, Debug)]
pub struct Sep(pub usize);

impl Pretty for Sep {
    fn size(&self) -> Size {
        Size::Size(self.0)
    }

    fn pretty_write(&self, context: Context) -> io::Result<()> {
        if context.broken {
            writeln!(context.writer, "")?;
            for _ in 0..(context.tab_size * context.indent_level) {
                write!(context.writer, " ")?;
            }
        } else {
            for _ in 0..self.0 {
                write!(context.writer, " ")?;
            }
        }
        Ok(())
    }
}

/// A wrapper which indents any newlines inside its contents.
///
/// # Examples
///
/// Basic usage:
///
/// ```
/// use pretty_trait::{JoinExt, Sep, Indent, to_string};
///
/// let max_line = Some(20);
/// let tab_size = 4;
///
/// let expected = "\
/// (
///     lorem
///     ipsum
///     dolor
///     sit
///     amet
/// )";
///
/// assert_eq!(
///     to_string(
///         &"(".join(Indent(
///             Sep(0)
///                 .join("lorem")
///                 .join(Sep(1))
///                 .join("ipsum")
///                 .join(Sep(1))
///                 .join("dolor")
///                 .join(Sep(1))
///                 .join("sit")
///                 .join(Sep(1))
///                 .join("amet")
///         )).join(Sep(0)).join(")"),
///         max_line,
///         tab_size,
///     ),
///     expected
/// );
/// ```
///
/// # Caution
///
/// To indent a block enclosed in paired delimiters like brackets, care must be taken to ensure that
/// the first line of the content *is* indented, and that the closing delimiter *is not* indented
/// along with its contents.  To ensure this, the newline after the opening delimiter should occur
/// *inside* the `Indent` block, and the newline before the closing delimiter should occur *outside*
/// the `Indent` block, as in the example above.
#[derive(Clone, Copy, Debug)]
pub struct Indent<T>(pub T);

impl<T: Pretty> Pretty for Indent<T> {
    fn size(&self) -> Size {
        self.0.size()
    }

    fn pretty_write(&self, mut context: Context) -> io::Result<()> {
        context.indent_level += 1;
        self.0.pretty_write(context)
    }
}

/// A wrapper which concatenates two pretty-printable values.
///
/// This struct is created by the [`join`] method from the `JoinExt` trait.  See its documentation
/// for more.
///
/// [`join`]: trait.JoinExt.html#method.join
#[derive(Clone, Copy, Debug)]
pub struct Join<T, U>(pub T, pub U);

impl<T: Pretty, U: Pretty> Pretty for Join<T, U> {
    fn size(&self) -> Size {
        self.0.size() + self.1.size()
    }

    fn pretty_write(&self, mut context: Context) -> io::Result<()> {
        self.0.pretty_write(context.reborrow())?;
        self.1.pretty_write(context)?;
        Ok(())
    }
}

/// Allows `join` to be called on any `Pretty` type.
///
/// This trait is automatically implemented for all `Pretty` types.  It should never be implemented
/// manually.
pub trait JoinExt: Sized {
    /// Concatenate two pretty-printable values.  This directly displays one after the other, with
    /// no separation or line breaks.  For separation, use the [`Sep`] type.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use pretty_trait::{JoinExt, to_string};
    ///
    /// let max_line = Some(10);
    /// let tab_size = 4;
    ///
    /// // Exceeds maximum line length, but does not break because there is no break-point:
    /// assert_eq!(
    ///     to_string(&"hello".join("world!"), max_line, tab_size),
    ///     "helloworld!"
    /// );
    /// ```
    ///
    /// [`Sep`]: struct.Sep.html
    fn join<U>(self, other: U) -> Join<Self, U>;
}

impl<T: Pretty> JoinExt for T {
    fn join<U>(self, other: U) -> Join<Self, U> {
        Join(self, other)
    }
}

/// A wrapper that concatenates an arbitrary sequence of pretty-printable values.
///
/// # Examples
///
/// Basic usage:
///
/// ```
/// use pretty_trait::{JoinExt, Sep, Seq, to_string};
///
/// let max_line = Some(10);
/// let tab_size = 4;
///
/// let expected = "\
/// lorem
/// ipsum
/// dolor
/// sit
/// amet";
///
/// assert_eq!(
///     to_string(
///         &Seq(vec![
///             "lorem".join(Some(Sep(1))),
///             "ipsum".join(Some(Sep(1))),
///             "dolor".join(Some(Sep(1))),
///             "sit".join(Some(Sep(1))),
///             "amet".join(None),
///         ]),
///         max_line,
///         tab_size,
///     ),
///     expected
/// );
/// ```
///
/// # Note
///
/// Because a `Seq` is just a thin wrapper around a `Vec`, all of its items must be of the same
/// type.  When working with combinators like `join` this can sometimes be confusing. For example,
/// the following code will not compile because the final element of the `Vec` does not have the
/// same type as the others:
///
/// ```compile_fail
/// # use pretty_trait::{JoinExt, Seq, Sep};
/// Seq(vec![
///     "lorem".join(Some(Sep(1))),
///     "ipsum".join(Some(Sep(1))),
///     "dolor".join(Some(Sep(1))),
///     "sit".join(Some(Sep(1))),
///     "amet",
/// ]);
/// ```
#[derive(Clone, Debug)]
pub struct Seq<T>(pub Vec<T>);

impl<T: Pretty> Pretty for Seq<T> {
    fn size(&self) -> Size {
        self.0.iter().fold(
            Size::Size(0),
            |total, item| total + item.size(),
        )
    }

    fn pretty_write(&self, mut context: Context) -> io::Result<()> {
        for item in &self.0 {
            item.pretty_write(context.reborrow())?;
        }
        Ok(())
    }
}

pub fn write<T: Pretty>(
    writer: &mut io::Write,
    content: &T,
    max_line: Option<usize>,
    tab_size: usize,
) -> io::Result<()> {
    let size = content.size();
    let context = Context {
        max_line,
        tab_size,
        indent_level: 0,
        broken: size.exceeds(max_line),
        writer,
    };
    content.pretty_write(context)
}

pub fn to_string<T: Pretty>(content: &T, max_line: Option<usize>, tab_size: usize) -> String {
    let mut result = Vec::new();
    write(&mut result, content, max_line, tab_size).expect("Writing to a string should not fail");
    String::from_utf8(result).expect("Invalid UTF8")
}

pub fn println_simple<T: Pretty>(content: &T) {
    write(&mut io::stdout(), content, Some(80), 2).unwrap();
    println!("");
}

#[derive(Clone, Copy, Debug)]
pub enum Conditional<T> {
    Always(T),
    OnlyBroken(T),
    OnlyUnbroken(T),
}

impl<T: Pretty> Pretty for Conditional<T> {
    fn size(&self) -> Size {
        Size::Size(0)
    }

    fn pretty_write(&self, context: Context) -> io::Result<()> {
        match (self, context.broken) {
            (&Conditional::Always(ref inner), _) |
            (&Conditional::OnlyBroken(ref inner), true) |
            (&Conditional::OnlyUnbroken(ref inner), false) => inner.pretty_write(context),
            _ => Ok(()),
        }
    }
}

impl<T: Pretty> Pretty for Option<T> {
    fn size(&self) -> Size {
        match self {
            &Some(ref inner) => inner.size(),
            &None => Size::Size(0),
        }
    }

    fn pretty_write(&self, context: Context) -> io::Result<()> {
        match self {
            &Some(ref inner) => inner.pretty_write(context),
            &None => Ok(()),
        }
    }
}

pub fn delimited<Delim, Item, It>(delim: &Delim, it: It) -> Seq<Join<Item, Option<Delim>>>
where
    Delim: Pretty + Clone,
    Item: Pretty,
    It: IntoIterator<Item = Item>,
{
    let mut iter = it.into_iter().peekable();
    let mut results = Vec::new();
    while let Some(item) = iter.next() {
        let cond_delim = if iter.peek().is_some() {
            Some(delim.clone())
        } else {
            None
        };
        results.push(item.join(cond_delim));
    }
    Seq(results)
}
