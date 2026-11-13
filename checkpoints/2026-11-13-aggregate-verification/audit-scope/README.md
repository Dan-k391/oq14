# Scope of the declaration axiom audit

The audit checks every kernel-safe declaration owned by the accepted project modules,
including private declarations and those without a printed axiom command. It collects
the complete dependency closure of each selected declaration. Only `propext`,
`Classical.choice`, and `Quot.sound` are allowed.

The first attempt also selected unsafe executable compiler implementations as roots.
It reported `Equiv.symm._elambda_2`, an unsafe axiom-shaped compiler helper. The retained
probe shows that this helper is unsafe while the kernel definition `Equiv.symm` is safe
and has no axiom dependencies. Lean 4.19.0's `Lean/Compiler/Old.lean` identifies the
eager-lambda-lifting helper names; `Lean/Declaration.lean` defines `ConstantInfo.isUnsafe`.
`Lean/Util/CollectAxioms.lean` traverses the checked types and values of definitions and
theorems. Hashes of these pinned compiler sources accompany the probe.

The corrected root selection excludes only declarations marked unsafe by Lean. It
lists every excluded implementation separately. The dependency collector is unchanged:
no dependency reached from a safe declaration is filtered, and no custom axiom has been
added to the allowlist. Thus a nonstandard axiom reached by any safe declaration would
still fail the audit. The initial failed source and output are retained under
`all-constants-stage111/attempt-including-unsafe.*`.

The audit is a check of kernel-safe proof dependencies, not a claim that executable
compiler implementation declarations contain no unsafe operations. It complements
the fresh source build and the mathematical review of the theorem statements.
