# Independent phase AE bound review

The source and root-author log hashes match, and a fresh direct pinned-compiler build used the corrected isolated PhaseGluing object. One public report uses only propext, Classical.choice and Quot.sound; no warnings, placeholders or custom axioms were found. Exact hashes, paths, command and timing are in independent-build.json.

The theorem assumes U and V open, f continuous on closure U ∩ V, AE equality of f with a on U ∩ V, and an AE upper bound on a over V. It first restricts the AE bound to U ∩ V, uses open-set positivity to turn equality of min(f,B) and f into pointwise equality on that open set, then extends by continuity to closure U ∩ V. It does not infer boundary AE field values or provide the uniform AE bound B itself.

Reviewed source SHA-256: cfe74d397a6dddca5466c71ce0d8e505ef82c4c9050ad3d84d788ffcdb4867b3
