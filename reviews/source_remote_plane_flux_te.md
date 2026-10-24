# SourceRemotePlaneFluxTE — author verification

Frozen source SHA256 `F146A7FA1D00E56DC7201B4D2E3A39D501FDF55A9A5D73270A5DEEF58891A333` (2034 bytes). Draft check1 and final/object run EXIT0, no warnings, no errors, no `sorry`, two standard-only reports (`[propext, Classical.choice, Quot.sound]`). Final log `lean/logs/SourceRemotePlaneFluxTE-final.log` SHA256 `88b67cd35d81f172bd4a9d3d45f017f85e0424ba6c819fc4e42dad8e6b7948ae`; exit file `lean/logs/SourceRemotePlaneFluxTE-final.exit.log` = 0; object `lean/.lake/build/lib/lean/SourceRemotePlaneFluxTE.olean` 117064 bytes. Imports `SourceRemotePlaneFlux` (frozen) and `SourceTERadiation`.

The actual TE source fields are defined by `SourceGeneralMaxwell.teElectric d p = SourceUnclippedMaxwell.magnetic d p` and `teMagnetic d p x i = - SourceUnclippedMaxwell.electric d p x i`. `te_flux_eq_conj` proves that the normal flux density of the TE pair is exactly the complex conjugate of that of the TM pair, so `te_plane_flux_bound` gives, with the same `r0` and `C` as `plane_flux_bound`, `‖crossProduct (teElectric d P x) (conjugate (teMagnetic d P x)) 2‖ ≤ C/‖x‖^3` for `x 2 = 0`, `r0 ≤ ‖x‖`, `d.X < ‖x‖`.

Scope: single layered source mode, exterior only (outside the stack radius `d.X`), no annulus layers, no uniformity in the degree or polynomial, no inclusion or incident field.

Root independent audit pending.
