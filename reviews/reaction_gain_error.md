# Actual parity gain amplification of field errors

Frozen source: lean/ReactionGainError.lean.
SHA256: C41B0B4A9C9541741DAF872124CC1B41A066FC32AF5D68B85678C67BB8DA57D1.

Author final pinned compiler and object emission PASS: exit 0, no warnings,
all five reports standard-only. Log: lean/logs/ReactionGainError-final.log.
Root independent complete-source mathematical review and pinned compiler PASS: exit 0, no warnings, standard-only reports.

For 0<a<=1, the actual electric gain coefficient abs((b/a)^2-1) is at most
(b squared + 1)/a squared. The actual reciprocal gain coefficient is at most
1+1/b squared. Thus an actual complex error bounded by C*a cubed is amplified
to O(a) electrically and remains O(a cubed) magnetically. The sum of the two
actual amplified errors is bounded by (b squared+2+1/b squared)*C*a.
These are actual numeric coefficient bounds, with no asymptotic premise.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. Pinned compiler exit 0, no warnings; all 5 reports use only standard foundations. Final source SHA256 `c41b0b4a9c9541741daf872124cc1b41a066fc32af5d68b85678c67bb8da57d1`. Independent log `lean/logs/ReactionGainError-root-audit.log`, SHA256 `3c72abd7cd5b8e8e96f3af397906b02754ab36ab36946cb7647cff0926580bdb`. This verifies the stated scope; neither full OQ14 construction is yet formally closed.
