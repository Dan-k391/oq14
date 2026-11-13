# Magnetic inverse-weight curl–curl system: author review

PASS for the stated weak equations and coercivity. Source SHA256 `F0EB8074401E69F9FD01FDBEAA7430324C13870E3BD8D9DFBC673D5C4AAD9E03`; final log `lean/logs/MaxwellInverseCurlCurl-author-final.log` SHA256 `4EA5842E51DDC6E40A83241BC2631FB1CBD083655609485504527E6DDC194BF2`; exit 0, no errors or warnings, three reports using only propext, Classical.choice, Quot.sound.

For actual regional H(curl) fields satisfying weak Maxwell with pointwise positive dielectric, the proof constructs an L² field equal almost everywhere to ε⁻¹ curl H whose actual weak curl is k²H. It combines this with the existing magnetic local H¹ construction for nonzero frequency. For measurable 1≤ε≤M, the inverse-weighted L² energy is integrable and bounded below by M⁻¹ times the unweighted energy. No interface traces, H² estimates, pointwise electric regularity or maxima are assumed or proved.
