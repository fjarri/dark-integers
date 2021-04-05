pub trait AddWithCarry {
    type CarryType;
    fn add_with_carry(x: &Self, y: &Self) -> (Self::CarryType, Self);
}

pub trait SubWithBorrow {
    type BorrowType;
    fn sub_with_borrow(x: &Self, y: &Self) -> (Self::BorrowType, Self);
}
