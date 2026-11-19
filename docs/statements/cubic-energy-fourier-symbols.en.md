# Fourier symbols for the cubic-energy commutator

[简体中文](cubic-energy-fourier-symbols.zh-CN.md)

Lines 626–677 use a real symbol which is smooth off zero and positively homogeneous of degree one. The following results cover the symbol decomposition and its Fourier pairing on Schwartz tests.

- `segment_norm_lower` — When the low cutoff is nonzero, every point on the integration segment has norm at least three quarters of the second input frequency norm and avoids zero.

- `commutator_symbol_decomposition` — One real degree-one homogeneous symbol gives the exact four-dimensional splitting and all Cartesian derivative bounds for the three joint symbols and the one-frequency factor. The identity includes zero product frequency.

- `pieces_integrable` — Each of the three terms is absolutely integrable on joint frequency space when tested against the Fourier transforms of three Schwartz functions.

- `fourier_trilinear_identity` — The Lebesgue pairing uses the conjugate of the third Fourier transform at the sum frequency. The equality preserves the signs and positions of both one-frequency multipliers.

The types and axioms of all 38 public declarations in the eight production modules agree with the independent native replay.

The global symbol decomposition and absolutely integrable Fourier pairings for Schwartz tests are proved. Identify the physical commutator, prove the finite-exponent multiplier bounds, then connect symmetric polarization, continuity, and coefficient differences. [Source bindings](cubic-energy-fourier-symbols-source-bindings.json)
