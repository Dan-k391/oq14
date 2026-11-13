# Complex magnetic reflection author review

PASS. `lean/logs/complex_magnetic_reflection_author_final.log` is the complete compiler log; `lean/logs/complex_magnetic_reflection_author_final.exit.log` records exit 0. Source SHA256 2F9718C4AAD5059AE6924233C1244D8914D9F1B20FC61F5180DC3B89834C3BFD; log SHA256 9BD3362EA91FF706FEC5634C5F3F40C2A5548A762383F9226AB00D3BC1F87D16; receipt SHA256 5E0E6077065598E0B3B20A5D8BDA3CF3D641EE1039780467E49ABEED04B6903C.

Proves reflection covariance of the actual complex Green-gradient source integral, using actual source transformation and measure-preserving change of variables. For every vector in the existing axisymmetric electric sector, the actual magnetic field has axial-vector reflection parity and its radial Debye scalar x·H is odd under meridional reflection. Rotation invariance and vanishing of this scalar are not yet asserted. Reported dependencies are only propext, Classical.choice, and Quot.sound.
