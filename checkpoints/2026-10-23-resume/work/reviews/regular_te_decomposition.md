# Exact regular TE electric and magnetic decomposition

Frozen source: lean/RegularTEDecomposition.lean.
SHA256: 6842E8EB82A15171EED5B0661AB7C351C3083F72C47451CFCC568C8C3C0EF0E3.
Author final pinned compiler/object PASS: exit 0, no warnings, four standard-only reports. Log: lean/logs/RegularTEDecomposition-final.log. Independent audit pending.

The actual regular electric half-Hankel split is extended from rays to every nonzero point by genuine sphere normalization. Actual punctured regularity of each Hankel electric part is derived. Its literal magnetic part equals minus I times its actual curl. The electric split holds on an actual open punctured neighborhood, so locality of the Frechet curl and actual finite curl addition derive the magnetic split. Thus both physical fields of the regular wave split into precisely the same outgoing/incoming Debye halves. No curl equality, Maxwell field identity or decomposition conclusion is an input.
