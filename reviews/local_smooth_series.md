# Actual spatial series differentiation infrastructure

Source `lean/LocalSmoothSeries.lean`, SHA256 `E80E5E5D815B66CFD22E8CDC5E7B44D4195F72F65F00A0D5D0EE9C2D7130322D`.

Author target+object EXIT0/no warnings, 242432 bytes. All 2 dependency reports standard-only. Forbidden-token scan passed. Log `lean/logs/LocalSmoothSeries-final.log`.

A genuine local termwise iterated-Frechet theorem on an open preconnected set follows by induction from actual summed-derivative bounds and actual differentiability of the summands. The first derivative uses the proved preconnected-set differentiation-under-sum theorem. Each inductive equality is local on the actual open set and curry isometries commute with the actual convergent sums. No derivative-of-sum conclusion or separation principle is a premise.

Status: author PASS; frozen pending root complete-source and independent pinned compiler audit.
