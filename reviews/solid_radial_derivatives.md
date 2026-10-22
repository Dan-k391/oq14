# All-order normalized regular radial derivatives

Source: `lean/SolidRadialDerivatives.lean`.
SHA256: `42863443B5046743725F6FB89286CA95A2F3FF70B4342CDC3F915414C37216BB`.

Author final compiler exit 0, no warnings; importable object 203144 bytes. All eleven selected reports use only propext, Classical.choice, Quot.sound. Log: `lean/logs/SolidRadialDerivatives-final.log`.

The actual j-times shifted coefficient sequence defines a genuinely entire derivative series, and induction identifies it with iteratedDeriv j F_l. Its coefficient norm is at most the original positive amplitude at every order, giving the uniform all-order bound norm(D^j F_l(t)) <= A_l exp(norm(t)/2). Exact shifted factorial coefficients and exact derivatives at zero are also proved. No derivative identity or analyticity conclusion is assumed. These are derivatives in the complex squared-radius variable; spatial derivatives require the successor composition/product argument.

Status: author PASS and root full-source / independent pinned compiler PASS. Frozen unchanged.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. Pinned compiler exit 0, no warnings; all 11 reports use only standard foundations. Final source SHA256 `42863443b5046743725f6fb89286ca95a2f3ff70b4342cdc3f915414c37216bb`. Independent log `lean/logs/SolidRadialDerivatives-root-audit.log`, SHA256 `5574c378ba95b8fe0f9947e19bd99ce94850eaad593d4c7e915e72c762c4bc81`. This verifies the stated scope; neither full OQ14 construction is yet formally closed.
