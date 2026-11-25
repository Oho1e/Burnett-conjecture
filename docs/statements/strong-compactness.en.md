# Vacuum limits and strong physical compactness

The entry `Burnett.P01.vacuumOpen_strongCompactness` formalizes `cor:strong` in the locked manuscript, lines 3063–3113. Let $B$ be the smooth Lorentzian background and $(g_n)$ the original smooth vacuum sequence. The sequence converges locally uniformly to $B$ and has the manuscript's local uniform bound on the first covariant derivatives. The auxiliary metric $r$ fixes their intrinsic norms and the unit cosphere.

For every open region $U$, the Ricci tensor of $B$ vanishes pointwise on $U$ if and only if every compatible chart with source in $U$ and every smooth compactly supported cutoff $\chi$ in that chart satisfy

$$
\|\partial\Pi_E(D)(\chi(g_n-B))\|_{L^2(\mathbb R^4)}\longrightarrow 0.
$$

The metric components are taken using the actual inverse chart differential. The input is extended by zero and the homogeneous Fourier multiplier is applied on all of $\mathbb R^4$. The multiplier depends on the Lebesgue almost-everywhere class of its symbol, with a free choice of value at frequency zero. The norm is the unweighted Lebesgue norm of all ordered tensor and derivative components. The weak derivative identity uses Lebesgue pairings with Schwartz tests. Convergence is along the whole original sequence.

The second conclusion starts from strong convergence of the unprojected covariant derivative in the background geometric volume on every compact subset of $U$. This gives pointwise vacuum and zero restriction to the cosphere above $U$ for each fixed quadratic measure with the original Einstein moment, zero scalar curvature, and finite mass above compact base sets. The restriction concerns the same measure supplied to the theorem.

## Proof and evidence

The pairings for classical symbols depending jointly on position and frequency give the local energy limit for the actual homogeneous projection. The covariance of the Ricci symbol kernel identifies zero local energy with zero mass of the same physical measure on the cutoff window. For a vacuum background on $U$, every strictly increasing subsequence has a refined subsequence with zero physical energy. The criterion along the whole sequence follows. In the other direction, a countable covering by cutoff windows makes the fixed measure vanish on the region, and its Einstein moment gives pointwise vacuum. The proof uses the quadratic construction and the base marginal.

For the unprojected sufficient condition, the actual chart half-density changes the background geometric volume exactly on the compact cutoff support. Uniform comparison with the intrinsic covariant derivative norm gives strong convergence of the receiving inputs. This step keeps the original auxiliary metric, derivative and volume.

The production replay and the independent statement comparison are recorded separately from integration and author confirmation. The paper status is `development`.
