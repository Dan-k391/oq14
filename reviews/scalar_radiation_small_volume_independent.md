# Scalar radiation and small-volume assembly audit

Full read-only review of the twelve-export version of `lean/ScalarRadiation.lean` and the six-export version of `lean/SmallVolumeMaxwell.lean` passes.

The scalar radiation estimate uses the exact gradient factorization, the coordinate bound on the difference of normalized directions, and the lower bound `‖x-y‖ ≥ ‖x‖/2` outside twice the source radius. The resulting constant `(2 |k| R + 1)/(π ‖x‖²)` is correct. Both actual source convolutions are proved absolutely integrable at the exterior observation point before their difference is combined under the integral. The statement concerns the actual scalar response and actual gradient-kernel response; it does not silently identify the latter with a classical derivative or assert the vector Silver–Müller condition.

The small-volume assembly constructs the weighted incident L2 datum from local L2 regularity, obtains the actual volume inverse using the explicit `252 * c.bound * k² * R² < 1` condition, and returns the exact volume equation and norm bound. Actual electric and magnetic local L2 properties and the two compact-smooth-test Maxwell equations follow from the previously proved response constructions. The classical-incident specialization obtains local L2 from continuity on compact balls. No global incident-field L2 condition or scattered-field PDE is assumed.

The appended thirteenth export, `response_outgoing_limit`, was also independently reviewed and passes. For an arbitrary path whose norm tends to infinity, eventual membership in the exterior region is derived from that hypothesis. The radius-scaled complex defect is bounded by a fixed constant divided by the radius; the actual complex limit follows by the norm squeeze theorem. No path-continuity or uniform-convergence assumption is inserted.

The final `IntegrableOn.mono_set` spelling correction in the compiled small-volume module was checked and does not change its mathematical scope. The source files remain owned by the coordinator and were not edited during review.

## Regional H(curl) assembly

Full independent review of `lean/MaterialHCurl.lean` (eight exports) also passes. The actual curl candidates are `ikH` and `-ikεE`, with regional L2 membership proved before forming graph representatives. The generic compact-smooth identities enter the proved compact-C1 density upgrade with the correct coordinate orientation. Substitution of field representatives is explicitly almost everywhere in the restricted measure.

The material specialization obtains regional L2 from the already proved ball L2 bounds and obtains εE in regional L2 from the actual measurable bounded dielectric. Its quantifiers retain one fixed inverse solution u for every bounded open observation region, including regions crossing material interfaces. No boundary trace or global field L2 claim is introduced.
