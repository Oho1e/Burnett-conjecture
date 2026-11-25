# Formal results and mathematical/Lean correspondence

The 17 formal result environments in the locked source are retained individually below. The statements are received with their original proposed-proof status; excerpts and source references are not a mathematical correctness review. These numbered results do not yet have complete Lean statements and proofs. The mathematical interface of the main theorem is expanded in [main-interface.md](main-interface.en.md); the latest actual declarations for unnumbered algebraic dependencies are in [quadratic-real-algebra.md](quadratic-real-algebra.en.md), and the first noncharacteristic fragment is in [ricci-symbol.md](ricci-symbol.en.md). References and notation in the source must be read with their surrounding sections.

## T01

Source: theorem 1.1, label `thm:main`, source lines 139–168. Title: Forward kinetic limit in the smooth-limit class.

Original TeX statement:

```tex
\begin{theorem}[Forward kinetic limit in the smooth-limit class]
\label{thm:main}
Assume \eqref{eq:admissible}. After passage to one subsequence, there exists
a nonnegative Radon measure $\mu$ on $S_r^*M$ such that:
\begin{enumerate}[label=\textup{(\roman*)}]
\item $\mu$ is locally finite over the base and supported on $P=0$;
\item the Einstein moment identity \eqref{eq:moment} holds, and
$\Scal(g)=0$;
\item the same measure satisfies \eqref{eq:transport} for every smooth
positively one-homogeneous test with compact base support.
\end{enumerate}
Moreover, on every globally hyperbolic open subspacetime $U\subset M$
there is a nonnegative Radon measure $\nu$ on $T^*U\setminus0$, supported
on its null cone, with
\begin{equation}\label{eq:full-moment-bound}
\int_{\pi^{-1}(K)}|\xi|_r^2\,\dd\nu<\infty
\qquad(K\Subset U),
\end{equation}
and
\begin{equation}\label{eq:full-equations}
\begin{gathered}
\int_U G(g)_{ab}S^{ab}\,\dV
=\int_{T^*U\setminus0}S^{ab}\xi_a\xi_b\,\dd\nu,\\
\int_{T^*U\setminus0}H_Pb\,\dd\nu=0
\qquad(b\in C_c^\infty(T^*U\setminus0)).
\end{gathered}
\end{equation}
The first equality holds for all compactly supported smooth symmetric
contravariant tensors $S$ on $U$.
\end{theorem}
```

Mathematical/Lean correspondence: not yet modeled; no actual declaration, type, or proof. The full context, important definitions, implicit parameters, and additional technical assumptions remain to be checked. Independent reverse review and user/author confirmation have not taken place.

## T02

Source: theorem 2.1, label `thm:quadratic`, source lines 354–356. Title: Positive null second moments, without transport.

Original TeX statement:

```tex
\begin{theorem}[Positive null second moments, without transport]\label{thm:quadratic}
Assume \eqref{eq:admissible}. After extraction of one subsequence, there is a globally defined nonnegative Radon measure $\mu$ on $S_r^*M$, locally finite over compact base sets and supported on $P=0$, such that \eqref{eq:moment} holds. In particular $\Scal(g)=0$. The construction is compatible with fixed smooth coordinate changes. The transport equation is not part of this intermediate theorem.
\end{theorem}
```

Mathematical/Lean correspondence: not yet modeled; no actual declaration, type, or proof. The full context, important definitions, implicit parameters, and additional technical assumptions remain to be checked. Independent reverse review and user/author confirmation have not taken place.

## T03

Source: corollary 2.2, label `cor:base-marginal`, source lines 487–506. Title: Base marginal and angular disintegration.

Original TeX statement:

```tex
\begin{corollary}[Base marginal and angular disintegration]
\label{cor:base-marginal}
Under the hypotheses of Theorem~\ref{thm:quadratic}, put
$e_r=r^{ab}G(g)_{ab}$. Then $e_r$ is smooth and nonnegative, and
\begin{equation}\label{eq:base-marginal}
\pi_*\mu=e_r\,\dV.
\end{equation}
There is a measurable family of nonnegative finite measures $\mu_x$ on
the unit null covectors at $x$, defined for almost every $x$, such that
\begin{equation*}
\dd\mu(x,\xi)=\dd\mu_x(\xi)\,\dV(x),\qquad
\mu_x(S_{r,x}^*M)=e_r(x),\qquad
G(g)_{ab}(x)=\int_{S_{r,x}^*M}\xi_a\xi_b\,\dd\mu_x(\xi).
\end{equation*}
No angular regularity or determination by the moment tensor alone is asserted.
For a fixed $\mu$, disintegration has its usual almost-everywhere uniqueness.
In particular,
the physical measure has no concentration in its base marginal, and it
vanishes over every open vacuum region of $g$.
\end{corollary}
```

`Burnett.F08.IntrinsicBaseMarginal.baseMarginal_and_angularDisintegration` proves the smooth nonnegative base marginal of the fixed quadratic measure, disintegration and reconstruction on the actual unit null fibers, all tangent-vector moments on a common conull set, almost-everywhere uniqueness for this measure, absolute continuity of the base marginal, and vanishing above open vacuum regions. Author confirmation is pending. [Statement and evidence](base-marginal-and-angular-disintegration.en.md)

[Local disintegration](local-disintegration.en.md) · [Countable-cover disintegration](countable-fiber-disintegration.en.md) · [Angular kernel transforms](angular-kernel-transforms.en.md)

## T04

Source: lemma 3.1, label `lem:commutator`, source lines 566–575. Title: Lipschitz-small coefficients in a symmetric energy pairing.

Original TeX statement:

```tex
\begin{lemma}[Lipschitz-small coefficients in a symmetric energy pairing]\label{lem:commutator}
Let $u$ be a compactly supported smooth vector-valued function, let $r^{ab}=r^{ba}$ be real smooth scalar coefficients in the field indices, and let $B=B^*$ be a fixed properly supported matrix pseudodifferential operator of order one with smooth $S^1_{1,0}$ symbol. Then
\begin{equation}\label{eq:lip-estimate}
\bigl|2\Im\ip{r^{ab}\partial_{ab}u}{Bu}\bigr|
\leq C_B\|r\|_{W^{1,\infty}(\R^4)}\|u\|_{H^1(\R^4)}^2.
\end{equation}
The constant is independent of second derivatives of $r$ or $u$.
The same estimate holds for matrix coefficients $R^{ab}$ with
$(R^{ab})^*=R^{ba}$ if $B$ is scalar at every symbol order.
\end{lemma}
```

Mathematical/Lean correspondence: not yet modeled; no actual declaration, type, or proof. The full context, important definitions, implicit parameters, and additional technical assumptions remain to be checked. Independent reverse review and user/author confirmation have not taken place.

## T05

Source: lemma 3.2, label `lem:cubic-continuity`, source lines 613–623. Title: Continuity of the complete cubic energy.

Original TeX statement:

```tex
\begin{lemma}[Continuity of the complete cubic energy]\label{lem:cubic-continuity}
For smooth compactly supported fields,
\begin{equation}\label{eq:cubic-continuity}
|\mathcal E(u)-\mathcal E(v)|
\leq C\|\partial(u-v)\|_{L^3(\R^4)}
(\|\partial u\|_{L^3(\R^4)}+\|\partial v\|_{L^3(\R^4)})^2.
\end{equation}
With fixed inhomogeneous regularizations, the corresponding estimate
holds with $W^{1,3}(\R^4)$ norms. The estimate applies to the complete
polarized energy; it does not estimate isolated unsymmetrized pairings.
\end{lemma}
```

Mathematical/Lean correspondence: not yet modeled; no actual declaration, type, or proof. The full context, important definitions, implicit parameters, and additional technical assumptions remain to be checked. Independent reverse review and user/author confirmation have not taken place.

## T06

Source: lemma 3.3, label `lem:freezing`, source lines 736–764. Title: Quantitative freezing of a complete cubic energy.

Original TeX statement:

```tex
\begin{lemma}[Quantitative freezing of a complete cubic energy]
\label{lem:freezing}
Work in a fixed relatively compact chart in $\mathbb R^4$ with a fixed
finite-dimensional real field space. Let $\mathcal T$ be a real symmetric
trilinear action form whose principal cubic polynomial is, up to its
fixed normalization,
\begin{equation}\label{eq:freezing-statement-1}
 P_C(z)=\int_{\R^4} C_{IJK}^{ab}(x)z^I\partial_a z^J\partial_b z^K\,\dd x,
 \qquad C_{IJK}^{ab}=C_{IKJ}^{ba},
\end{equation}
and whose remaining terms have at most one field derivative in total.
All coefficients are fixed and smooth. Let $B$ be a scalar self-adjoint
order-one test with real odd principal symbol $a(x,\xi)$, chosen so that
$Q=-\ii B$ preserves real fields. Use one fixed infrared regularization.
For $x_0$ in a fixed compact subset let $\mathcal T_0$ retain just the
principal coefficients frozen at $x_0$, and put $Q_0=-\ii a(x_0,D)$.
For real $z\in C_c^\infty(B(x_0,R\ell))$, $0<\ell\leq\ell_0\leq1$,
\begin{equation}\label{eq:freezing-quantitative}
 \big|\mathcal T(z,z,Qz)-\mathcal T_0(z,z,Q_0z)\big|
 \leq A\ell\|\partial z\|_{L^3(\R^4)}^3+B_\ell\|z\|_{L^3(\R^4)}\|\partial z\|_{L^3(\R^4)}^2.
\end{equation}
Here $A$ depends only on $R$, the field dimension, and finitely many
fixed smooth coefficient and normalized test-symbol seminorms.
It is independent of $\ell$, $x_0$, the number of patches, and the
frequencies of $z$. For each fixed $\ell$, $B_\ell$ is finite and
uniform in $x_0$, with the same independence from the frequencies of
$z$; it may depend on further fixed smooth seminorms and on $\ell^{-1}$.
No second derivative of $z$ is present in the estimate.
\end{lemma}
```

Mathematical/Lean correspondence: not yet modeled; no actual declaration, type, or proof. The full context, important definitions, implicit parameters, and additional technical assumptions remain to be checked. Independent reverse review and user/author confirmation have not taken place.

## T07

Source: lemma 3.4, label `lem:analytic-near`, source lines 1026–1057. Title: All-scale transfer and angular summation.

Original TeX statement:

```tex
\begin{lemma}[All-scale transfer and angular summation]\label{lem:analytic-near}
Suppose a translation-invariant trilinear Fourier multiplier on
$p+q+r=0$ has, after factoring the three first-derivative weights,
a symbol $m$ homogeneous of degree zero under simultaneous positive
dilation of its three frequencies. On each piece of a fixed smooth
homogeneous low/high partition, require
$m=M(\omega,\theta,\rho)$, where $\omega=p/\lambda_p$, $\theta=q/\lambda_q$, and
$\rho=\lambda_p/\lambda_q$. Let $\mathfrak A_{100}$ bound its $C^{100}$ extension to
$\rho=0$ in a fixed finite angular atlas, together with the
$C^{100}$ extension norms of the comparable pieces to fixed normalized
annular boxes. Fixed factorwise infrared cutoffs are allowed separately.
For the three differentiated factors $f,g,w$, the form satisfies
\begin{equation}\label{eq:analytic-near-statement-2}
|\mathcal T_m(f,g,w)|
\leq C_\kappa\mathfrak A_{100}
\|f\|_{L^3(\R^4)}\|g\|_{L^3(\R^4)}\|w\|_{L^3(\R^4)}.
\end{equation}
The constant is uniform in
finite smooth dyadic truncations of the factors and does not depend on their
highest frequency or number of scales.

If in addition the symbol is supported on adjacent null caps and equals
$\delta^2$ times a symbol with $\mathfrak A_{100}\leq A$ uniformly in
normalized cap variables, including the ratio endpoint, then, for
every fixed $p_*>3$,
\begin{equation}\label{eq:analytic-near-bound}
|\mathcal T^{\mathrm{near}}(f,g,w)|
\leq C_{\kappa,p_*}A\delta^{\beta_*}\|f\|_{L^3(\R^4)}\|g\|_{L^3(\R^4)}\|w\|_{L^3(\R^4)}.
\end{equation}
Thin-cone multipliers are included in the individual cap symbols. The
right-hand side contains no norm of the full thin-cone projection.
\end{lemma}
```

Mathematical/Lean correspondence: not yet modeled; no actual declaration, type, or proof. The full context, important definitions, implicit parameters, and additional technical assumptions remain to be checked. Independent reverse review and user/author confirmation have not taken place.

## T08

Source: lemma 3.5, label `lem:analytic-correction-bounds`, source lines 1380–1394. Title: Bounds for the correction and its rough commutator.

Original TeX statement:

```tex
\begin{lemma}[Bounds for the correction and its rough commutator]
\label{lem:analytic-correction-bounds}
An operator satisfying \eqref{eq:analytic-extension} obeys
\begin{equation}\label{eq:analytic-correction-bounds}
\begin{gathered}
\|T_Hu\|_{L^2(\R^4)}\leq C_\delta\|H\|_{L^4(\R^4)}\|\partial u\|_{L^4(\R^4)},\\
\|[\partial_a,T_H]u\|_{L^2(\R^4)}
\leq C_\delta\|\partial_aH\|_{L^4(\R^4)}\|\partial u\|_{L^4(\R^4)},\\
\|[d,T_H]v\|_{L^2(\R^4)}
\leq C_\delta\|\partial d\|_{L^{\infty}(\R^4)}\|H\|_{L^4(\R^4)}\|v\|_{L^4(\R^4)}
\end{gathered}
\end{equation}
for real scalar Lipschitz $d$. The analogous bound for the formal adjoint
pieces holds. Inhomogeneous variants add only lower-order norms of $u$.
\end{lemma}
```

Mathematical/Lean correspondence: not yet modeled; no actual declaration, type, or proof. The full context, important definitions, implicit parameters, and additional technical assumptions remain to be checked. Independent reverse review and user/author confirmation have not taken place.

## T09

Source: proposition 4.1, label `prop:general-projection`, source lines 1600–1616. Title: A projected source without a coordinate condition.

Original TeX statement:

```tex
\begin{proposition}[A projected source without a coordinate condition]
\label{prop:general-projection}
Under \eqref{eq:admissible}, fix a chart $U\Subset\R^4$ and
$\chi\in C_c^\infty(U)$. Extend $\chi h_n$ by zero to $\R^4$. There is a fixed real even order-zero matrix Fourier multiplier
$\Pi$ such that $u_n=\Pi(\chi h_n)$ has the following properties.
For every fixed $1<p<\infty$, $\partial u_n$ is bounded in $L^p(\R^4)$ and
$u_n\to0$ in $L^p(\R^4)$ and $L^\infty(\R^4)$. If $a_n^{ab}$ is a smooth uniformly
Lipschitz extension to $\R^4$ of $g_n^{ab}$ from a neighborhood of $\supp\chi$, then
\begin{equation}\label{eq:general-bounded-source}
\big\|-\partial_a(a_n^{ab}\partial_bu_n)\big\|_{L^2(\R^4)}\leq C_\chi.
\end{equation}
The constant may depend on the uniform Lipschitz bound of the chosen
extension family; no bound on its second derivatives is required.
Over the region where $\chi=1$, the derivative defect of $u_n$ is null,
Lorenz polarized, and has exactly the physical scalar measure
\eqref{eq:mu-invariant}.
\end{proposition}
```

Mathematical/Lean correspondence: not yet modeled; no actual declaration, type, or proof. The full context, important definitions, implicit parameters, and additional technical assumptions remain to be checked. Independent reverse review and user/author confirmation have not taken place.

## T10

Source: theorem 5.1, label `thm:variational-transport`, source lines 1729–1735. Title: Transport under the original first-derivative hypotheses.

Original TeX statement:

```tex
\begin{theorem}[Transport under the original first-derivative hypotheses]
\label{thm:variational-transport}
Under \eqref{eq:admissible}, the invariant nonnegative measure of
Theorem~\ref{thm:quadratic} satisfies \eqref{eq:transport} for every smooth
positively one-homogeneous test with compact base support.
No coordinate condition and no second-derivative scale are assumed.
\end{theorem}
```

Mathematical/Lean correspondence: not yet modeled; no actual declaration, type, or proof. The full context, important definitions, implicit parameters, and additional technical assumptions remain to be checked. Independent reverse review and user/author confirmation have not taken place.

## T11

Source: lemma 6.1, label `lem:lift`, source lines 2989–2991. Title: Local-moment version of the globally hyperbolic lift.

Original TeX statement:

```tex
\begin{lemma}[Local-moment version of the globally hyperbolic lift]\label{lem:lift}
Suppose a smooth globally hyperbolic spacetime has a nonnegative locally finite measure on $S_r^*M$, supported on $P=0$, satisfying both \eqref{eq:moment} and \eqref{eq:transport}. Then it has a full null cotangent representation $\nu$ with $\int_{\pi^{-1}(K)}|\xi|_r^2\,\dd\nu<\infty$ for every $K\Subset M$.
\end{lemma}
```

Mathematical/Lean correspondence: not yet modeled; no actual declaration, type, or proof. The full context, important definitions, implicit parameters, and additional technical assumptions remain to be checked. Independent reverse review and user/author confirmation have not taken place.

## T12

Source: corollary 6.2, label `cor:strong`, source lines 3063–3078. Title: Vacuum limits and strong physical compactness.

Original TeX statement:

```tex
\begin{corollary}[Vacuum limits and strong physical compactness]
\label{cor:strong}
Assume \eqref{eq:admissible}, and let $U\subset M$ be open. Then
$\Ric(g)=0$ on $U$ if and only if, for every coordinate chart in $U$
and every $\chi\in C_c^\infty$ of that chart,
\begin{equation}\label{eq:physical-strong-criterion}
\|\partial\Pi_E(D)(\chi h_n)\|_{L^2(\R^4)}\longrightarrow0.
\end{equation}
Here the compactly supported tensor $\chi h_n$ is extended by zero, and $\Pi_E$ is
the homogeneous Euclidean gauge-complement projection from
Proposition~\ref{prop:general-projection}; its value at frequency zero
is immaterial. The convergence holds for the entire sequence.
In particular, $Dh_n\to0$ strongly in $L^2_{\loc}(U)$ implies
$\mu|_{S_r^*U}=0$ and $\Ric(g)=0$ on $U$. The converse need only hold after the physical
projection: pure coordinate oscillations may remain.
\end{corollary}
```

`Burnett.P01.vacuumOpen_strongCompactness` gives the equivalence of pointwise vacuum and full-sequence projected gradient convergence on every open set. The unprojected intrinsic sufficient condition gives vacuum and zero restriction of the fixed physical measure. The production modules passed the local native replay and realize the frozen independent statement. Author confirmation is pending. [Statement and evidence](strong-compactness.en.md)

## T13

Source: proposition A.1, label `prop:shear`, source lines 3121–3123. Title: Failure of a background $L^2$ source estimate.

Original TeX statement:

```tex
\begin{proposition}[Failure of a background $L^2$ source estimate]\label{prop:shear}
There are globally smooth flat metrics $g_n$ on $\R^4$, satisfying \eqref{eq:admissible} with $g=m$, and satisfying $H(g_n)=H(m)=0$ exactly, for which $\|\Box_mh_n\|_{L^2(K)}\to\infty$ on a fixed compact set $K$.
\end{proposition}
```

Mathematical/Lean correspondence: `Burnett.HarmonicShear.Bounds.harmonic_coordinate_source_counterexample` constructs the admissible, flat harmonic-coordinate sequence and proves divergence on one fixed compact set. Author confirmation is pending. [Statement and verification evidence](harmonic-shear.en.md)

## T14

Source: proposition B.1, label `prop:cubic`, source lines 3175–3181. Title: An auxiliary trilinear counterexample.

Original TeX statement:

```tex
\begin{proposition}[An auxiliary trilinear counterexample]\label{prop:cubic}
There are smooth scalar $f_n,w_n\to0$ locally uniformly with uniformly bounded first derivatives and $\Box_m f_n,\Box_mw_n\to0$ strongly in $H^{-1}_{\loc}(\R^4)$ such that
\begin{equation*}
Q_0(\dd f_n,\dd w_n)\partial_tf_n\rightharpoonup-\f14
\end{equation*}
in distributions. Here $Q_0(\dd f,\dd w)=m^{ab}\partial_af\partial_bw$.
\end{proposition}
```

Mathematical/Lean correspondence: a complete candidate using the same witnesses has been implemented; independent reverse review of the actual types and definitions in the frozen source has passed. Through choice 1A, the user delegated confirmation of this technical correspondence to root and an independent agent. The actual confirming parties were agents, rather than the user personally. Production combination checks and remote CI evidence are recorded separately.

See [cubic-counterexample.md](cubic-counterexample.en.md) for the complete candidate, precise test/H⁻¹ model, and remaining scope. The actual declaration is `Burnett.CubicCounterexample.auxiliary_trilinear_counterexample`. All conclusions for the same f/w have been implemented and their correspondence confirmed under the delegation. The fixed Fourier off-null property at source line 3193 is separately required for the final deliverable and remains unproved.

## T15

Source: proposition C.1, label `prop:bianchi`, source lines 3245–3247. Title: Geometric nonrepresentability without vacuum approximation.

Original TeX statement:

```tex
\begin{proposition}[Geometric nonrepresentability without vacuum approximation]\label{prop:bianchi}
There exists a smooth Lorentzian metric on a product interval times $\R^3$ whose Einstein tensor is trace-free, positive semidefinite, and pointwise a positive sum of two null squares, but which admits no nonnegative null ray measure satisfying both its Einstein identity and Hamilton transport.
\end{proposition}
```

Mathematical/Lean correspondence: `Burnett.Bianchi.exists_bianchi_intrinsic_counterexample` constructs the smooth metric and excludes every nonnegative null-ray measure satisfying both the prescribed tensor moments and Hamilton transport. Author confirmation is pending. [Statement and verification evidence](bianchi-counterexample.en.md)

## T16

Source: proposition D.1, label `prop:rosen`, source lines 3307–3312. Title: Two-polarization Rosen closure.

Original TeX statement:

```tex
\begin{proposition}[Two-polarization Rosen closure]\label{prop:rosen}
Let $I\subset\R$ be an interval and
$g_n=-2\dd u\dd v+\gamma_{n,AB}(u)\dd y^A\dd y^B$ on
$M=I\times\R^3$, with $A,B\in\{1,2\}$ and $\gamma_n$ smooth
positive definite on $I$. Suppose \eqref{eq:admissible} holds with smooth positive definite $\gamma$. Then $g$ has a full massless kinetic representation, without any second-derivative scale assumption.
\end{proposition}
```

`Burnett.RosenPlaneWave.two_polarization_rosen_closure` constructs one full kinetic graph measure for the general two-polarization Rosen product spacetime and proves the moment, transport and local second-moment statements. Independent reverse review passed. Author confirmation is pending. [Statement and evidence](rosen-two-polarization.en.md)

## T17

Source: proposition D.2, label `prop:flat-rigidity`, source lines 3390–3392. Title: Flat admissible sequences have flat smooth limits.

Original TeX statement:

```tex
\begin{proposition}[Flat admissible sequences have flat smooth limits]\label{prop:flat-rigidity}
If, in addition to \eqref{eq:admissible}, the full curvature of every $g_n$ vanishes, then the full curvature of $g$ vanishes.
\end{proposition}
```

Mathematical/Lean correspondence: `Burnett.FlatRigidity.isFlat_of_original_flat_sequence` proves full intrinsic Riemann flatness of the smooth limit. The frozen proof passed independent reverse review. Author confirmation is pending. [Statement and verification evidence](flat-rigidity.en.md)
