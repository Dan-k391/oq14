# Editorial and mathematical review notes

This article presents the project's explicitly quantified formulations. It
does not claim to settle all interpretations of the original OQ14. In
particular, the channel counterexample uses `delta > eta` and the complete
outgoing scattering map, including reflection; receiving-only outputs,
stricter bypass thresholds, and fixed total support are separate questions.
The connection between the reciprocal-residue modal normalization and other
possible interpretations of the original modal-volume question also needs
separate justification.

The editorial review did not establish a new mathematical contradiction.
The following points should be addressed before presenting the manuscript as
a fully vetted publication:

1. In the counted-subspace definition, the square is written using `L`, but
   the definition does not explicitly state `L > 0`. The main channel
   counterexample does state it. Confirm the intended hypothesis and its
   consequences throughout before changing the formal definition.
2. The proof of `hs:three-rounding` summarizes fixed-interface
   difference-quotient, collar, and trace estimates; the proof of
   `hs:modal-coefficient-continuation` summarizes a uniform-in-contrast
   annular projection and constant cancellation. These are demanding,
   compressed steps that merit an independent specialist examination and a
   comparison with the exact formal statements. This observation is a
   verification risk, not a finding that either proof is incorrect.
3. The manuscript cites two unpublished, user-supplied research artifacts
   (`priorreport` and `priorhtml`) whose authors and public locations are not
   identified. Establish accurate attribution, availability, and permission
   before distributing or relying on them externally. The missing companion
   file noted in the introduction has not been independently inspected.
4. The title page intentionally leaves author information to be supplied.
   Identify the responsible human contributor(s) and prepare an accurate
   account of AI assistance appropriate for the chosen venue.
5. The paper is 113 pages in the present layout. A journal submission may
   require a focused article and separate supporting material; any such
   reorganization must retain the hypotheses and proof dependencies.

The reported Lean endpoints, trusted dependencies, and numerical diagnostic
limits are described in the manuscript's verification appendix and the
unchanged historical audit. This editorial revision did not rerun or extend
the Lean proof audit and is not independent human peer review.
