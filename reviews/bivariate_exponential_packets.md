# Two-variable exponential-polynomial independence

Frozen source: lean/BivariateExponentialPackets.lean.
SHA256: 3BD19D7313F0FEC18A487326E1C4D7B147C4C68388A9329C412E122615FED0A0.
Author final pinned compiler/object PASS: exit 0, no warnings, two reports
using standard foundations only. Log: lean/logs/BivariateExponentialPackets-final.log.
Independent audit pending.

The literal two-variable finite packet expression has an exact double-sum
expansion with phase zeta_i*s+mu_ij*t. If it vanishes on a nonempty real
rectangle, distinct horizontal frequencies and distinct vertical frequencies
within each horizontal group force every bivariate polynomial coefficient
of degree at most two in each variable to vanish. This follows by applying
the actual real-interval identity and generalized derivative eigenspace result
twice. No Fourier uniqueness or coefficient-vanishing conclusion is assumed.
The intended specialization is the actual positive/negative edge phases in
the symmetric scalar cosine jet functional.
