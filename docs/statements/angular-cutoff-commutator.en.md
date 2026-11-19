# Angular Fourier multipliers and compact cutoffs

[简体中文](angular-cutoff-commutator.zh-CN.md)

The localization argument for the quadratic defect measure uses cutoffs whose commutators vanish on the sequence (F05, manuscript lines 395–412). For a fixed angular Fourier multiplier $m(D)$ on $\mathbb R^4$ and multiplication by a smooth compactly supported complex function $\chi$, Lean proves

$$
\big\|m(D)(\chi u_n)-\chi m(D)u_n\big\|_{L^2}\longrightarrow 0.
$$

Here the real smooth inputs are supported where one fixed compact cutoff equals one, are uniformly bounded in $L^2$, and tend to zero against all real smooth compactly supported tests. Lean takes their complex Schwartz representatives in the displayed formula. The symbol is bounded, smooth away from the origin, and homogeneous of degree zero under positive dilations. Replacing it by a bounded symbol that agrees with it outside a fixed frequency ball preserves the conclusion.

On the Fourier side the kernel contains the factor $m(\xi)-m(\eta)$. An angular difference bound and an integrable first moment of the Fourier transform of $\chi$ control the high input frequencies. The sequence assumptions imply that the Fourier energy in each fixed ball tends to zero. The same splitting proves strong convergence to zero for a bounded frequency multiplier whose symbol vanishes uniformly at infinity.

The Lean namespace is `Burnett.Microlocal.AngularCommutator`. The homogeneous result is `cutoffCommutator_tendsto_zero_of_localized_weak_zero`. The fixed low-frequency modification is handled by `cutoffCommutator_tendsto_zero_of_infrared_regularization`. F05 also requires base-dependent operators, comparison of coordinate charts and a common tensor-valued measure. These have separate proof obligations.
