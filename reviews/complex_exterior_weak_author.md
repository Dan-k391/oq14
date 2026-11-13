# Complex exterior weak response author review

PASS. `lean/logs/complex_exterior_weak_author_final.log` is the full compiler log; `lean/logs/complex_exterior_weak_author_final.exit.log` records exit 0. Source SHA256 E7D061F8B5837366B1DEDA7C35C8E789A2ED850BA61FD1E727819159D38FB1BF; log SHA256 396E4EAD2E4232C1E6532701FB26958CAF3C992F12814EF61428E31014803DDD; receipt SHA256 5E0E6077065598E0B3B20A5D8BDA3CF3D641EE1039780467E49ABEED04B6903C.

For any input source, proves the actual complex-frequency localized exterior response obeys the homogeneous weak curl-curl equation, divergence-free condition, and component Helmholtz identities on compact smooth Schwartz tests supported outside the source ball and inside the observation ball. It assumes nonzero frequency only for divergence and scalar Helmholtz. Compatibility, full smooth-test interface, outgoing asymptotics and matching remain open. The sole reported dependencies are propext, Classical.choice, and Quot.sound.
