# Quantitative weak L2 translation and mollification

`lean/WeakPoynting/Translations.lean` is frozen at SHA-256
`0bfff8dc2417e9f9ae2aa475bb50125f32e86811e2211c5bb712538cab3d3229`.
The complete direct compiler capture and source-scoped provenance are
`translations-verification.txt` and `translations-provenance.json` beside
the source. All seven selected exports use only `propext`,
`Classical.choice`, and `Quot.sound`; the compiled object is available.

For a genuine L2 class with a compact representative and actual weak
partials `D i`, the module proves

```
norm (translate u a - u) <= norm a * sum i, norm (D i)
norm (mollify phi u - u) <= phi.rOut * sum i, norm (D i).
```

The first estimate follows from the existing distributional test definition.
Weak derivatives commute with test convolution; the actual finite-dimensional
derivative and mean value theorem bound the resulting test pairing. The
actual measure-preserving translation of its integral has the required sign.
The L2 norm is recovered using conjugated compact mollifications of the
translated difference itself, whose strong convergence is already proved.
Thus neither a dual norm formula on an assumed dense test class nor an H1
translation theorem is postulated.

The second estimate applies the normalized bump convolution bound to that
actual L2 translation orbit. Its constant is the actual support radius.
Compactness of the whole bounded family remains separate work.

Independent full source reviews by the coordinator and hotspot agent passed,
including the reflection/translation signs and the self-mollification dual
norm argument.
