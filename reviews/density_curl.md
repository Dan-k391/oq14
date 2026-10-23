# Actual density field coordinate derivatives and curl interchange

Frozen source: lean/DensityCurl.lean.
SHA256: C7BAED2B95113B5CDA24B75937E4134E2BE14A4753B9C2FFD07B44E4BCC07465.
Author final pinned compiler/object emission PASS: exit 0, no warnings,
all three reports standard-only. Log: lean/logs/DensityCurl-final.log.
Independent audit pending.

Literal finite-component density fields are differentiable, with actual
coordinate derivatives given by genuine source integrals, under actual
point-kernel differentiability, source-variable differential continuity,
uniform differential bounds and integrability. Curl interchanges with these
finite sums and genuine integrals. A proved point-kernel curl identity then
passes to the density fields. All derivative integrands are genuinely
integrable, derived using DensityDerivatives and real norm-density domination.
No density derivative or density PDE is a premise.

The point curl identity is an explicit generic hypothesis of the final
abstract lemma. ParityDensityMaxwell discharges it with the already-proved
actual point parity Maxwell equations and all remaining actual kernel
hypotheses. This generic module does not identify radial-stack Green fields.
