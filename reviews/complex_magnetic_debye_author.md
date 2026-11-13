# Complex magnetic Debye scalar author review

PASS. `lean/logs/complex_magnetic_debye_author_final.log` is the full compiler log; `lean/logs/complex_magnetic_debye_author_final.exit.log` records exit 0. Source SHA256 B779C5CD9AC2811C6BE606C8992E7BCE8CFA51D2B771B67987029F2221DFCCCD; log SHA256 2F54EC594D06AC9D63347645DB22FAABB2D6BEE173030611DBE072706398084C; receipt SHA256 5E0E6077065598E0B3B20A5D8BDA3CF3D641EE1039780467E49ABEED04B6903C.

For every actual complex sphere-kernel vector, constructs the locally L2 magnetic radial Debye scalar x·H, proves its interior weak Helmholtz equation from actual Maxwell and divergence, and identifies every interior radial harmonic coefficient with one global regular Riccati mode. This does not yet establish exterior magnetic outgoing selection, parity, interface matching, or full kernel classification. Reported dependencies are only propext, Classical.choice, and Quot.sound.
