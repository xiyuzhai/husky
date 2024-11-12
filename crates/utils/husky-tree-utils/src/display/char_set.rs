#[derive(Clone, Copy)]
pub struct CharSet {
    /// The characters used in the horizontal portion of a branch.
    ///
    /// Should resemble a plain horizontal line, eg. '─'.
    pub horizontal: char,
    /// The character used in the space between branches in place of
    /// [`connector`](CharSet::connector).
    ///
    /// Should resemble a plain vertical line, eg. '│'.
    pub vertical: char,
    /// The character connecting the vertical and horizontal portions of a
    /// branch.
    ///
    /// Should resemble a vertical line with an offshoot on the right, eg. '├'.
    pub connector: char,
    /// The character connecting the vertical and horizontal portions of the
    /// last branch under a node.
    ///
    /// Should resemble an "L" shape, eg. '└'.
    pub end_connector: char,
}

impl Default for CharSet {
    fn default() -> Self {
        Self {
            horizontal: '─',
            vertical: '│',
            connector: '├',
            end_connector: '└',
        }
    }
}
