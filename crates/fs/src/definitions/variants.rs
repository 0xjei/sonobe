use sonobe_primitives::{
    commitments::{GroupBasedVectorCommitment, VectorCommitmentDef},
    traits::CF2,
};

use crate::{
    FoldingSchemeDef, FoldingSchemeDefGadget, FoldingSchemeFullVerifierGadget, FoldingSchemeOps,
    FoldingSchemePartialVerifierGadget,
};

pub trait GroupBasedFoldingSchemePrimaryDef:
    FoldingSchemeDef<
    VC: GroupBasedVectorCommitment,
    TranscriptField = <<Self as FoldingSchemeDef>::VC as VectorCommitmentDef>::Scalar,
>
{
    type Gadget: FoldingSchemeDefGadget<
        Native = Self,
        VC = <Self::VC as GroupBasedVectorCommitment>::Gadget2,
    >;
}

pub trait GroupBasedFoldingSchemePrimary<const M: usize, const N: usize>:
    GroupBasedFoldingSchemePrimaryDef<Gadget: FoldingSchemePartialVerifierGadget<M, N>>
    + FoldingSchemeOps<M, N>
{
}

impl<FS, const M: usize, const N: usize> GroupBasedFoldingSchemePrimary<M, N> for FS where
    FS: GroupBasedFoldingSchemePrimaryDef<Gadget: FoldingSchemePartialVerifierGadget<M, N>>
{
}

pub trait GroupBasedFoldingSchemeSecondaryDef:
    FoldingSchemeDef<
    VC: GroupBasedVectorCommitment,
    TranscriptField = CF2<<<Self as FoldingSchemeDef>::VC as VectorCommitmentDef>::Commitment>,
>
{
    type Gadget: FoldingSchemeDefGadget<
        Native = Self,
        VC = <Self::VC as GroupBasedVectorCommitment>::Gadget1,
    >;
}

pub trait GroupBasedFoldingSchemeSecondary<const M: usize, const N: usize>:
    GroupBasedFoldingSchemeSecondaryDef<Gadget: FoldingSchemeFullVerifierGadget<M, N>>
    + FoldingSchemeOps<M, N>
{
}

impl<FS, const M: usize, const N: usize> GroupBasedFoldingSchemeSecondary<M, N> for FS where
    FS: GroupBasedFoldingSchemeSecondaryDef<Gadget: FoldingSchemeFullVerifierGadget<M, N>>
{
}
