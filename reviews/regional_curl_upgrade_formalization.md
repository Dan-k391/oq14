# Regional weak-curl upgrade

`lean/WeakPoynting/RegionalCurlUpgrade.lean` is frozen after a clean direct Lean 4.19.0 check. Its four selected exports use only `propext`, `Classical.choice`, and `Quot.sound`.

Source SHA-256: `ed980e72403a1b79d4e779565754ed0075fd66582f51c56ce76f3fd1a013392d`.

`OQ14.RegionalCurlUpgrade.hasWeakCurl_of_schwartz_integrals` upgrades actual compact smooth scalar curl identities to `DomainCurl.HasWeakCurl Ω E C`. This target is the existing graph definition tested against every compact C1 scalar function supported in Ω. The proof uses the constructed interior-supported approximation from `InteriorTestDensity`, zero-extends the regional L2 classes solely for continuous L2 pairings, and passes both value and derivative pairings to the limit.

`hasWeakCurl_of_smooth_integrals` accepts ordinary smooth functions instead of bundled Schwartz maps. The main application interface is `fields_hasWeakCurl_of_global_smooth`: actual coordinate fields E and C, each square-integrable on Ω, satisfy the regional graph identity whenever their global integrals satisfy the curl equations on compact smooth tests supported in Ω. Compact support makes the global integrals equal to the regional ones, including derivative tests.

No global square-integrability of scattering fields, boundary regularity, field differentiability, test-density premise, or Maxwell equation for the fields is inserted by the upgrade. The smooth-test curl equations remain explicit input and must be proved for each construction. The result does not assert a boundary trace or extension by zero preserving curl.

The complete compiler output and source-hash-scoped dependency provenance are saved as `lean/WeakPoynting/regional-curl-upgrade-verification.txt` and `lean/WeakPoynting/regional-curl-upgrade-provenance.json`. The independently emitted olean is available in the local build cache.
