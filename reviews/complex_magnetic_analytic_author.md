# Complex magnetic kernel analyticity author review

PASS. `lean/logs/complex_magnetic_analytic_author_final.log` is the complete compiler log; `lean/logs/complex_magnetic_analytic_author_final.exit.log` records exit 0. Source SHA256 AB1E4062B345328C7971E9C6438E984813B41786D1EEBE1B111327A819DE57BF; log SHA256 1079CE554C3F88CB5653C03C9FC03D70794043266B241F08B0E7312ECBE96917; receipt SHA256 5E0E6077065598E0B3B20A5D8BDA3CF3D641EE1039780467E49ABEED04B6903C.

Proves the exact entire complex-frequency derivative of the Green gradient difference, explicit compact-ball bounds, and differentiability of the actual truncated L2 gradient-difference kernel. The singular static gradient is retained separately; this does not yet identify magnetic response pairings or assert Maxwell equations. Reported dependencies are only propext, Classical.choice, and Quot.sound.
