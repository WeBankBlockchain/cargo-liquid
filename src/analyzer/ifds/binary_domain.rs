#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum BinaryDomain {
    /// The bottom element is used to initialize the function computation at entry points.
    Bottom,
    /// The top element is used at merge points and is typically the neutral element of the
    /// join operator, which is used to merge values a those points.
    Top,
}

impl BinaryDomain {
    pub fn top_element() -> Self {
        return Self::Top;
    }

    pub fn bottom_element() -> Self {
        return Self::Bottom;
    }

    pub fn meet(&self, right: &Self) -> Self {
        if self == &Self::Top && right == &Self::Top {
            return Self::Top;
        } else {
            return Self::Bottom;
        }
    }
}
