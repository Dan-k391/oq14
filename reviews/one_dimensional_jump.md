# Actual compact-test point-source jump theorem

Source: `lean/OneDimensionalJump.lean`.
SHA256: `303043C95AA5BFBDE68A7A45B8BE7F3C86B8BF02747620941A3075C9A4032380`.

Author target plus importable object compiler exit 0, no warnings. Object 473752 bytes. Nine selected reports standard-only. Log: `lean/logs/OneDimensionalJump-final.log`. Forbidden-token scan passed.

Actual localization by compact tests makes the concomitant a eta'+(b-a')eta globally smooth and compactly supported, even though the coefficients need only be genuinely smooth on the open test domain. Actual localized product derivatives prove its derivative equals a eta''+b eta'+(b'-a'')eta everywhere. Genuine halfline FTC then proves that the integral of a literal left/right derivative split is the left value minus right value at the split point. Applying it to the actual concomitants gives the exact jump integral, without a distributional integration-by-parts premise.

A literal smooth bump centered at s>0 with radii s/4 and s/2, multiplied by an actual affine complex polynomial, constructs compact positive-radius tests with independently prescribed value and derivative at s. These actual tests prove the required separation rather than assuming it. The final theorem takes actual smooth coefficients, actual first/second derivatives and the actual compact-test point-source integral, and concludes a_plus(s)=a_minus(s) and (b_plus-a_plus')(s)=(b_minus-a_minus')(s)+S. It includes no matching or jump premise. Actual radial Green data are substituted in the subsequent adapter.

Status: author PASS; frozen pending root complete-source and independent pinned compiler audit.

## Independent integration verification, October 22, 2026

Complete source independently reviewed. Pinned compiler exit 0, no warnings; all 9 reports use only standard foundations. Final source SHA256 `303043c95aa5bfbde68a7a45b8be7f3c86b8bf02747620941a3075c9a4032380`. Independent log `lean/logs/OneDimensionalJump-root-audit.log`, SHA256 `f51ebb933b2e8d2d243c872925e572adbdc59c2db14fcd14bdca385636b2f59b`. The audit verifies this stated scope; complete OQ14 formalization remains unfinished.
