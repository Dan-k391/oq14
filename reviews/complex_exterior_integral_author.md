# Complex exterior integral author review

PASS. `lean/logs/complex_exterior_integral_author_final.log` is the complete compiler log; `lean/logs/complex_exterior_integral_author_final.exit.log` records exit 0. Source SHA256 AE8F68F0B8D691D47419DB5487BC1AEE1A63AC6F3E4F84F3E037B06916F7877F; log SHA256 3B3DF8810817EB19E525C95F28C10148FBEC766265D86139CEFFEBFCF5D5C152; receipt SHA256 5E0E6077065598E0B3B20A5D8BDA3CF3D641EE1039780467E49ABEED04B6903C.

Constructs the literal complex-frequency dyadic source integral and proves it continuous outside the compact source. It proves this integral agrees almost everywhere with the actual localized L2 response on every separated exterior observation region. Its outgoing asymptotics and spherical matching are not asserted. Reported dependencies are only propext, Classical.choice, and Quot.sound.
