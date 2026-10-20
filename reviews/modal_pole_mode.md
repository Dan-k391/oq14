# ModalPoleMode — the pole residue and the actual weak mode coincide

Source: `lean/ModalPoleMode.lean`

SHA256: `495E6F6DDD2280B834B5148F25FD5356B601F717B6114F2D0B12C1CB92CB92C3`

Evidence: `lean/logs/modal-pole-mode-check.log`. All nine exported theorems compile cleanly with only `propext`, `Classical.choice`, and `Quot.sound`.

The exact matching residue amplitudes define the global regular-interior/outgoing-exterior electric and magnetic fields. Because these very amplitudes lie in the matching kernel, the previously proved interface assembly gives their global weak Maxwell equations. Actual local L2 regularity and nonzero regional H(curl) graph elements are supplied for the same fields.

The shell-response residue is identified almost everywhere with this global mode restricted to the physical shell. The interface sphere is explicitly removed as a null set; pointwise equality of the normal electric field across that sphere is not assumed. A nonzero residue input has both interior and outgoing amplitudes nonzero and gives a genuinely nonzero shell L2 output.

The final existence theorem uses one frequency and one matching-data vector for both the meromorphic response pole of order −1 and the nonzero global weak residue mode. It does not merely juxtapose two unrelated existence theorems.

Self-audit: checked the common amplitudes throughout, the actual weak equation instantiation, shell measure transport and null sphere removal, nonzero amplitude-to-field implication, and regional graph representatives.

Independent audit: channels read the complete source and confirmed all steps and the scope. No defect was found.

Scope: full Maxwell resolvent identification and cross-degree isolation remain separate. Complex-frequency radiation asymptotics of the explicit outgoing fields are being proved in the next module.
