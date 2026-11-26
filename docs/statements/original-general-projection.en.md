# Projected source in arbitrary charts

This implements Proposition 4.1, `prop:general-projection`, in the locked paper, lines 1600–1616.

`Burnett.P01.exists_originalGeneralProjection` fixes a single subsequence, an intrinsic tensor covariance and the physical cosphere measure supplied by the original quadratic theorem. For every maximal chart and every smooth real cutoff compactly supported inside it, the same fixed real, even order-zero multiplier acts on the actual zero extension of the cutoff times the metric perturbation. The projected fields converge to zero in $L^p$ for every $1<p<\infty$ and in $L^\infty$, with derivatives uniformly bounded in each such $L^p$. The norm and divergence source estimates hold for the full sequence.

Given a common Lipschitz bound, the source constant is chosen uniformly over all smooth inverse-metric extension families that agree near the cutoff support, and over all sequence indices. The resulting divergence source belongs to $L^2$ on the entire coordinate space.

On the original subsequence, mixed pairings in arbitrary derivative directions and tensor slots use the actual regularized projection on both arguments, and allow complex smooth degree-zero angular multipliers. On the cutoff plateau, the projected covariance is supported on the null characteristic set and satisfies the Lorenz contraction. Its quarter-weighted physical contraction equals the restriction of the original cosphere measure on all Borel sets. The original Einstein moment identity remains part of the returned witnesses.

The three modules and their consumer have passed a qualified Lean replay. The public-root build and independent semantic review apply to the integrated candidate. Author confirmation is pending.
