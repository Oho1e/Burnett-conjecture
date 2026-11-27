# 完整三次能量的定量冻结

[English](original-cubic-freezing.en.md)

锁定论文第 736–764 行的 `lem:freezing` 对应 `Burnett.A03.exists_symmetric_action_freezing_of_local_classical_amplitude`。实有限维场以固定有限坐标表示。输入为实对称三线性作用，其中主对角多项式含 $C_{IJK}^{ab}z^I\partial_a z^J\partial_b z^K$，且 $C_{IJK}^{ab}=C_{IKJ}^{ba}$。其余项至多含一个场导数。冻结作用只保留中心点 $x_0$ 的主系数。两条对角式经由极化识别实际三槽取值，并包含固定的作用归一化。

在固定坐标窗内，外层截断在所有受支撑输入的邻域内等于一。用紧支撑经典二点振幅及其光滑核表示局部算子的弱振荡积分极限。约化给出实际齐次左主部和在值与一阶导数上均有有限 $L^3$ 界的零阶余项。场支撑邻域上的测试相等识别三次作用的三个取位。中心乘子使用同一实奇主符号在中心的值与固定偶红外截断。

对支撑在 $B(x_0,R\ell)$ 的实光滑场及 $0<\ell\leq\ell_0\leq1$，入口证明

$$
\bigl|\mathcal T(z,z,Qz)-\mathcal T_0(z,z,Q_0z)\bigr|
\leq A\ell\|\partial z\|_3^3+B_\ell\|z\|_3\|\partial z\|_3^2.
$$

先选定 $A$，再选择尺度。固定尺度后，$B_\ell$ 在中心和测试场之前选定。两个常数均与补丁数量及测试场的频率分片无关。低阶项通过一次分部积分把测试场上的导数移到值场和固定系数上，右端只使用一阶场导数。

具名模块编译和公理读回已通过。独立复核已对照锁定原稿核对实际声明。作者确认与整库项目审计待完成。 [源码与回执](local-classical-cubic-freezing-source-bindings.json)
