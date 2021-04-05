use crate::primitives::PrimitiveUInt;

pub trait AddWithCarry {
    type CarryType: PrimitiveUInt;
    fn add_with_carry(x: &Self, y: &Self) -> (Self::CarryType, Self);
}

pub trait SubWithBorrow {
    type BorrowType: PrimitiveUInt;
    fn sub_with_borrow(x: &Self, y: &Self) -> (Self::BorrowType, Self);
}
