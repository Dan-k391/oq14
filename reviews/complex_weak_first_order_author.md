# Complex weak first-order Maxwell author review

PASS. `lean/logs/complex_weak_first_order_author_final.log` is the full compiler log; `lean/logs/complex_weak_first_order_author_final.exit.log` records exit 0. Source SHA256 D4DCAC9D83ECF720D30DF3976B0CE85693877110270A7EB193ECD353CCA84878; log SHA256 D8F36841A86DB39424C984A9E28005C69233C8CDC803BA2FD716AC2FE7BCB8CE; receipt SHA256 5E0E6077065598E0B3B20A5D8BDA3CF3D641EE1039780467E49ABEED04B6903C.

For actual localized complex electric response and source, defines magnetic field as a distributional pairing via curl E/(i*z) and proves both first-order weak Maxwell curl equations on compact tests across the source interface, at nonzero z. It does not establish a locally L2 or pointwise magnetic representative or transmission traces. Reported dependencies are only propext, Classical.choice, and Quot.sound.
