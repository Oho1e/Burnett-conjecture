# Positive matrix-measure representation

The defect-measure construction on manuscript lines 395–408 passes from limits of quadratic tests to a positive Hermitian measure. This result formalizes the representation step on a compact test space.

Let $X$ be compact Hausdorff with its Borel measurable structure. The Lean statement also records local compactness and the closed-set outer approximation hypothesis `HasOuterApproxClosed X`. Let $F_{ij}$ be a finite matrix of bounded complex-linear functionals on $C(X,\mathbb C)$. Suppose that for every constant complex vector $v$ and every $f$ in a fixed uniformly dense family, the compression of $F$ by $v$ at $\overline f f$ is real and nonnegative.

There is one family of finite regular positive measures $\nu_v$ representing these compressions on every continuous complex test. Polarizing the four measures associated with $e_i+e_j,e_i-e_j,e_i+\mathrm{i}e_j,e_i-\mathrm{i}e_j$ gives a countably additive complex measure $M_{ij}$. In that order the weights are $1/4,-1/4,-\mathrm{i}/4,\mathrm{i}/4$. The entry formula for $F_{ij}(f)$ uses the four Bochner integrals of $f$ with these weights.

For each Borel set $S$, the matrix $M(S)$ is Hermitian positive semidefinite and $v^*M(S)v=\nu_v(S)$. The finite positive measure $\tau=\sum_i\nu_{e_i}$ gives the trace of $M(S)$ on every such set. Every $M_{ij}$ is absolutely continuous with respect to $\tau$.

The F05 construction still has to supply the functionals from the original metric sequence and identify their local measures on overlaps. The joint representation is `Burnett.Microlocal.MatrixMeasureAssembly.exists_positiveMatrixMeasure_of_dense_square_positive`. [Lean statement and proof](../../Burnett/Analysis/Microlocal/MatrixMeasure/Representation.lean) · [简体中文](positive-matrix-measure.zh-CN.md)
