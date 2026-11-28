# X02: a complete candidate for the auxiliary trilinear counterexample

The source identity remains the locked SHA256 of `paper/burnett.tex`. Formal proposition `prop:cubic` is at lines3175–3181, with proof at3182–3209. This deliverable implements every conclusion using an alternative proof through explicit divergence and integration by parts. On2026-11-16 the user selected1A, delegating confirmation of this proposition and reviewed support results to root and an independent agent. The technical content retains reviewed explanation f14afadd…; this is not recorded as the user personally reading Lean.

## The same pair of actual sequences

The space is real four-dimensional coordinate space with standard Euclidean Lebesgue volume; indices0,1,2,3 are t,x,y,z. D_i evaluates the actual Fréchet derivative on the standard coordinate vector. Box=−D_0D_0+D_1D_1+D_2D_2+D_3D_3; Q_0 contracts with the same Minkowski signs.

Take N=n+1, a=N², b=N, u=t−x, and v=t+x,

\[
f_n=a^{-1}\cos(bv)\sin(au),\qquad w_n=(2b)^{-1}\sin(2bv).
\]

This is a finite initial reindexing of the original positive-integer sequence; every denominator is nonzero for every natural n. The final existence theorem `Burnett.CubicCounterexample.auxiliary_trilinear_counterexample` uses the same f/w for all conclusions, without selecting different sequences for different limits. The actual proof gives:

- Every term is smooth, and f/w converge uniformly to zero on the whole space, stronger than the original local-uniform requirement.
- Uniform first-derivative bounds hold for every n, point, and all four coordinate directions, with constants2 and1 respectively.
- Both actual wave sources tend strongly to zero in the precise H⁻¹_loc model below.
- For each fixed actual smooth compactly supported test φ, the actually integrable cubic product satisfies

\[
\int\varphi\,Q_0(df_n,dw_n)D_0f_n\longrightarrow-\tfrac14\int\varphi.
\]

An actual nonnegative smooth compactly supported unitTest with integral1 is also constructed. Its cubic test integral tends to −1/4 and does not tend to zero. This is not pointwise convergence: at the origin the cubic product is always −2.

## Precise meaning of the negative Sobolev space

Test space D consists of all real smooth compactly supported functions on R⁴, without a single fixed support compact set; the source uses actual `ContDiff ℝ ∞`. The five-component jet is Jφ=([φ],[D_0φ],…,[D_3φ]); each component is proved L² before entering its quotient space. Ambient uses PiLp2, with squared norm the sum of the five squared L² norms, including the time derivative, all positive.

The project uses the standard completion definition: H¹ is the closure of J(D) in this Hilbert fivefold L² space, and H⁻¹ is its continuous real dual with operator norm. Density of the test image, uniqueness of continuous dual elements from their test values, and correct operator-norm bounds for coefficient functionals are actually proved. Injectivity of dual restriction is not inferred from an assumed injective original test map.

For locally integrable T_n, `StrongHminusLocalZero` requires actual local integrability of each T_n and, for every fixed χ∈D, continuous dual elements L_n satisfying L_n(Jφ)=∫χT_nφ for all actual tests and converging to zero in operator norm. The local-integrability guard prevents misuse of default Bochner integrals for nonintegrable functions; an additional independent query actually proves this guard ensures integrability of χT_nφ.

This uses the standard whole-space C∞c completion/dual model, without claiming all equivalences with weak-derivative, Fourier/Bessel, or arbitrary boundary-domain models have been formalized. The theorem does not use those other models or rename testwise convergence as strong negative-norm convergence.

## Actual analytic proof

Actual second differentiation gives Box f_n=4b sin(bv)cos(au) and Box w_n=0. Set A_n=(4b/a)sin(bv)sin(au) and F_n=(A_n/2,−A_n/2,0,0). Then actual div F_n=Box f_n and F_n is uniformly O(1/N).

After fixing χ, the localized source r_n=χBox f_n is independently proved L² before its actual source functional is defined. With V_i=χF_i and g=−Σ_i(D_iχ)F_i, actual smooth compactly supported integration by parts gives

\[
\int r_n\varphi=\int g_n\varphi-\sum_i\int V_{n,i}D_i\varphi.
\]

All coefficients actually belong to L², controlled by χ and its first derivatives independently of n, and their L² norms tend to zero. Coefficient functionals tend to zero in the actual continuous-dual operator norm; test density then identifies them with the previously independently defined source functional. The desired integral identity is not assumed as a parameter or field.

The cubic product actually equals the constant −1/4 plus seven nonconstant cosine modes and an O(1/N) remainder. For n≥2, all seven actual linear phases have time-frequency absolute value at least2N. One actual time integration by parts removes each mode against a fixed test. Integrability is proved before every finite-sum/integral interchange; weak limits are not multiplied.

## Statements not yet covered

The user selected2A to require the strong L² off-null gradient-projection property at original line3193, and separately chose fixed Fourier cone projections. It is not an explicit conclusion of the formal proposition, is not consumed by this alternative proof, and remains unformalized at this stage. See [cubic-off-null-localization.md](cubic-off-null-localization.en.md) for its exact target and status. Proving prop:cubic does not prove this additional property or verify every mathematical sentence in X02.

f/w are scalar functions, not exact Einstein solutions; this counterexample does not replace analysis of the complete physical contraction in the Einstein equations. The forward kinetic limit connects the quadratic measure construction to the transport conclusion. [Original variational transport and forward kinetic limit](original-forward-kinetic-limit.en.md)

Lean checks, independent semantic review, user/author confirmation, CI, and PR merging are recorded separately in this batch's review record.
