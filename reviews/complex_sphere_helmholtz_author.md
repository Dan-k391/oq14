# Complex sphere Helmholtz author review

PASS. `lean/logs/complex_sphere_helmholtz_author_final.log` is the full compiler log; `lean/logs/complex_sphere_helmholtz_author_final.exit.log` records exit 0. Source SHA256 5ADB7B51865F1DCC068F99280D5007534F7AF8C65705B7258723EF0AD0343BD4; log SHA256 490B3A79498169A884A0F17AD466EAF53C63AF495586D2F3D40854410BDD44C2; receipt SHA256 5E0E6077065598E0B3B20A5D8BDA3CF3D641EE1039780467E49ABEED04B6903C.

For an actual complex sphere volume-kernel vector and nonzero frequency, proves each coordinate of its actual localized response is locally integrable and satisfies IsWeakHelmholtz at frequency z*n on the full open unit ball, with all smooth compact tests. The proof converts such tests to Schwartz functions and uses the actual complex-frequency curl-curl source identity and material self-consistency. Exterior matching and kernel classification are not asserted. The sole reported dependencies are propext, Classical.choice, and Quot.sound.
