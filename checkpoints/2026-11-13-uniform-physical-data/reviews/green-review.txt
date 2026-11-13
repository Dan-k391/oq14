# Independent uniform Green H² review

The helper and six root modules match their frozen source and author-log hashes. A fresh direct pinned-compiler build retained isolated objects in dependency order, including Packet06UniformGreenOperators before its users. Seven modules/16 public reports passed using only propext, Classical.choice and Quot.sound; no warnings, placeholders, missing theorem reports or custom axioms were found. Exact source/object/log hashes, paths, declarations, commands and timings appear in independent-build.json. The helper was authored by this reviewer; root separately reviewed and rebuilt it in checkpoints/2026-11-13-uniform-green-operators/reviews/root-build.json and root-review.txt.

GreenRepresentativeBounds bounds the actual local Green response representative by the L² convolution operator norm and establishes the static Newton Hessian bound. QuantitativeCompactGreen constructs actual first and second weak L² derivatives of a cutoff scalar Green response and bounds them by supplied scalar, gradient and dynamic Hessian operator bounds. ContinuousH2Bound turns a compactly supported continuous representative with full weak H² arrays into a pointwise bound, using AE equality of continuous representatives.

UniformCompactGreen derives fixed cutoff derivative bounds and finite common operator constants from the compact-frequency Green helper, yielding actual compact H² representatives uniformly for all sources with the stated common support. UniformCompactCorrection scales by z² and proves the bound for the literal continuous scalar response on the cutoff plateau. UniformMaterialCorrection applies the actual source AE identification and source norm bound to arbitrary material/mode families with common susceptibility, frequency, mode norm and support bounds. Its output contains genuine weak H² arrays and a pointwise correction bound; it does not itself bound the scalar-potential gradient, compose chart forcing, or establish the final collar estimate.

Reviewed exact source SHA-256:
- Packet06UniformGreenOperators: 627fe461f07fc43e1391ab47f3d422882792b2d599d615c1aba727a5a44eba6f
- Packet05GreenRepresentativeBounds: 44cdb96757c4d843874413d0edc1fb6b04f108d608d5616cc8078168616324ea
- Packet05QuantitativeCompactGreen: 809d516a11fe67131376e2ea3ef4ebc147ff0eb265c276da1a7828e10776ef72
- Packet05ContinuousH2Bound: 4cdb86c8f61dc7ac3f62bc7033b1690476cff29e3eff42c12378ffbb927b3090
- Packet05UniformCompactGreen: 68c2b073d650b02c74214adc2578ef8aad106491c95512c23a859dc7b2bc12e9
- Packet05UniformCompactCorrection: 19346c736252c9f0722948f672bb3f3dc76b9a00eb8f59b0a4b6987fd83e004e
- Packet05UniformMaterialCorrection: cb4aac7a96bb66b7fa181102959e3ff006558fb6733a3e0d06aeec5fcc5255dd
