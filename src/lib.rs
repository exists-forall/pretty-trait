use std::io;
use std::ops::{Add, Deref};

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

pub trait JoinExt: Sized {
    fn join<U>(self, other: U) -> Join<Self, U>;
}

impl<T: Pretty> JoinExt for T {
    fn join<U>(self, other: U) -> Join<Self, U> {
        Join(self, other)
    }
}

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
    content: T,
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

pub fn println_simple<T: Pretty>(content: T) {
    write(&mut io::stdout(), content, Some(80), 2).unwrap();
    println!("");
}
