# 正矩阵值测度表示

论文第 395–408 行从二次测试的极限构造正 Hermitian 测度。此处形式化其中在紧测试空间上的表示定理。

设 $X$ 是紧 Hausdorff 空间，带有 Borel 可测结构。Lean 声明还列出局部紧性和闭集的外逼近条件 `HasOuterApproxClosed X`。设 $F_{ij}$ 是由 $C(X,\mathbb C)$ 上有界复线性泛函组成的有限矩阵。假定对每个常复向量 $v$ 和一个固定的一致稠密族中的每个 $f$，用 $v$ 压缩该矩阵后，在 $\overline f f$ 上的取值为非负实数。

存在同一族有限正则正测度 $\nu_v$，对全部复值连续测试函数表示这些压缩泛函。依次取 $e_i+e_j,e_i-e_j,e_i+\mathrm{i}e_j,e_i-\mathrm{i}e_j$ 对应的四个测度，按 $1/4,-1/4,-\mathrm{i}/4,\mathrm{i}/4$ 极化，得到可数可加的复测度 $M_{ij}$。$F_{ij}(f)$ 的表示公式采用这四个权重以及 $f$ 对相应正测度的 Bochner 积分。

对每个 Borel 集 $S$，矩阵 $M(S)$ 为 Hermitian 半正定矩阵，且 $v^*M(S)v=\nu_v(S)$。有限正测度 $\tau=\sum_i\nu_{e_i}$ 在每个这样的集合上的值等于 $M(S)$ 的迹。所有 $M_{ij}$ 都关于 $\tau$ 绝对连续。

F05 还需从原度量序列构造这些泛函，并识别各局部测度在重叠区域上的关系。联合表示定理为 `Burnett.Microlocal.MatrixMeasureAssembly.exists_positiveMatrixMeasure_of_dense_square_positive`。[Lean 声明与证明](../../Burnett/Analysis/Microlocal/MatrixMeasure/Representation.lean) · [English](positive-matrix-measure.en.md)
