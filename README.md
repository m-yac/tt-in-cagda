A (very experimental) attempt at formalizing type theory internally in cubical agda such that:

1. Only well-typed terms are permitted

2. Equality of terms is exactly βη-equality.

The first condition can be acheived in plain agda (e.g. https://github.com/AndrasKovacs/stlc-nbe) but the second can only be acheived with higher inductive types.

This work was inspired by [Type Theory in Type Theory using Quotient Inductive Types](http://www.cs.nott.ac.uk/~psztxa/publ/tt-in-tt.pdf) by Thorsten Altenkirch and Ambrus Kaposi, and an adaptation of the core of their paper can be found in `DTLC.agda`.

### Structure

- `STLC.Base` gives a higher inductive presentation of a simply typed lambda calculus with a type of natural numbers with a recursor. For now, see the file itself for more detail.

   Note: If you're wondering why we bother with `apˡ` and `apʳ` in the first place, see `Cubical.HITs.Ints.BiInvInt` and `Cubical.HITs.Ints.IsoInt` in [agda/cubical](https://github.com/agda/cubical).
   
Currently normalization for STLC is a mess and incomplete.

- `STLC.NormShort` was my first pass at trying to do this directly, and it got very difficult to work with.

- After doing some research, I began trying normalization by evaluation in `STLC.NormLong` -- inspired by Andras Kovacs' above repository, among others. Finishing up the proofs in this file is ongoing work.
