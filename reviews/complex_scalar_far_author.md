# Complex scalar far field author review

PASS. `lean/logs/complex_scalar_far_author_final.log` is the full compiler log; `lean/logs/complex_scalar_far_author_final.exit.log` records exit 0. Source SHA256 1FA8CD3FEDD28697AFD66EE553A67DF753C934A9106DA69E0D8393CD83CD33CE; log SHA256 F53B5255642FDBC7CF3EBF37D3B2127504216671F02C608F0047C32092B95309; receipt SHA256 5E0E6077065598E0B3B20A5D8BDA3CF3D641EE1039780467E49ABEED04B6903C.

Proves the actual outgoing scalar Green-potential far-field limit for every complex frequency and every integrable compactly supported source. The proof includes an explicit uniform source-support bound with exp(norm(z)*R), hence handles complex frequencies without assuming real-frequency modulus identities. The electric dyadic far-field limit is not asserted. Reported dependencies are only propext, Classical.choice, and Quot.sound.
