use std::iter::Peekable;

pub(crate) struct PeekMap<I: Iterator, F> {
    iter: Peekable<I>,
    f: F,
}

impl<B, I: Iterator, F> Iterator for PeekMap<I, F>
where
    F: FnMut(I::Item, Option<&I::Item>) -> B,
{
    type Item = B;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|f| (self.f)(f, self.iter.peek()))
    }
}

impl<B, I: Iterator, F> PeekMap<I, F>
where
    F: FnMut(I::Item, Option<&I::Item>) -> B,
{
    pub(crate) fn new(iter: Peekable<I>, f: F) -> Self {
        Self { iter, f }
    }
}
