# Compact limits of the actual vector reaction series

`lean/VectorReactionLimit.lean` has seven clean author-final reports and a
compiled object. Independent audit is pending. All reports use only the
standard foundations.

The literal TE/TM regular Maxwell dyads carry the source coefficient
`-(gamma + I)/(l(l+1))`. Their actual finite spatial derivatives form
continuous maps on the compact product of core balls. The proved angular
majorant and the actual finite-stack radial limit give dominated convergence
in that continuous-map norm. The sum of the finite-stack derivative maps
is proved equal to the actual derivative of the literal vector series.
The radius control depends on the requested derivative order and includes
the additional curls. Both spatial origins are included.

This establishes a series limit. Identifying the series with the full
outgoing Maxwell point-source Green response remains separate work.

Evidence: `lean/logs/VectorReactionLimit-final.log` and its zero exit receipt.
