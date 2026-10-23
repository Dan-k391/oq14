# Actual whole-plane static trial flux limit

Frozen source: lean/StaticTrialLimit.lean.
SHA256: E4C2E9B7B8F2AC54214AFFE1A87FC04846B226B1051FF8EFBAFEE62AF8AC9742.
Author final pinned compiler/object PASS: exit 0, no warnings, two reports
using standard foundations only. Log: lean/logs/StaticTrialLimit-final.log.
Independent audit pending.

For actual compact source families of mass O(a^2), a genuine source-plane gap
gamma*a, and literal finite magnetic parity illuminations with coefficient
mass O(1/a), the complete incident-plus-free trial flux converges in whole-plane
L1 to its actual static coherent flux. The proof combines the derived uniform-
gap coherent remainder bound with the actual quadratic source-source flux
bound; its wholeConstant(gamma*a)*a^4 factor tends to zero by an explicit
polynomial identity. Integrability of both terms is proved. The source mass
and geometry remain explicit at this intermediate generic level, to be
discharged by actual finite-ball sources. No PDE or flux-convergence conclusion
is a hypothesis. No physical finite-stack identification is asserted.
