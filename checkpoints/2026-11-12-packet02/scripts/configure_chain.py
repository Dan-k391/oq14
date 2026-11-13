"""Freeze the explicit Packet 02 module/declaration inventory for checking."""
from pathlib import Path
import json
import re

checkpoint = Path(__file__).resolve().parent.parent
root = checkpoint.parent.parent
names = '''ComplexSphereMaxwell ComplexMagneticHelmholtz ComplexMagneticDivergence
ComplexMagneticDebye ComplexMagneticReflection Packet02SourceSymmetry
Packet02MagneticRotation Packet02GoodSet Packet02GoodRotation Packet02VanishingAlgebra
Packet02MagneticVanishing Packet02DebyeVanishing Packet02ExteriorGood Packet02Axis
Packet02ExteriorSmooth Packet02LogSquare Packet02RadialLog Packet02Surface
Packet02Majorant Packet02SurfaceGeometry Packet02SurfaceL2 Packet02GoodMeasurable
Packet02SphereVanishing Packet02Chain'''.split()
modules = []
for module in names:
    source = root / 'lean' / (module+'.lean')
    data = source.read_text(encoding='utf-8').replace('\r\n','\n').rstrip()+'\n'
    source.write_text(data, encoding='utf-8', newline='\n')
    namespace = re.findall(r'^namespace (\S+)', data, re.M)
    assert len(namespace) == 1, module
    decls = [namespace[0]+'.'+m for m in re.findall(r'^\s*(?:theorem|lemma)\s+(\S+)', data, re.M)]
    prints = re.findall(r'#print axioms\s+(\S+)', data)
    assert len(prints) == len(decls) and set(prints) == set(decls), (module, decls, prints)
    modules.append(dict(module=module, declarations=prints))
(checkpoint/'modules.json').write_text(json.dumps(modules,indent=2)+'\n', encoding='utf-8', newline='\n')
print(f'{len(modules)} modules; {sum(len(m["declarations"]) for m in modules)} declarations.')
