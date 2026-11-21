# 冻结屏幕与相位恒等式

[English](frozen-screen.en.md)

证明对应锁定原稿第 2053–2107 行，使用四维有序坐标指标与实逆度规 \(B\)。

- 实际 \(w\) 与 \(Q\) 给出同时正交于 \(e\) 和 \(Be\) 的欧氏屏幕，其中 \(e\) 具有单位欧氏长度。零锥上的 Lorentz 二次型在 \(e\) 的 Lorentz 正交补上非负，只在 \(e\) 张成的直线上为零。其在欧氏屏幕上的限制正定。
- 零锥上的 \(\mathsf A=QBQ+(I-Q)\) 可逆。给定 \(\mathsf A\) 可逆及 \(w\ne0\)，实际去迹公式恰好固定满足 \(Je=JBe=0\) 和 \(\operatorname{tr}(BJ)=0\) 的对称张量 \(J\)。对称的 \(B,H\) 给出对称的投影张量。
- 对满足所列非退化及 Lorentz 标架条件的紧度规族，可以在单位零锥集上取同一个邻域。邻域中 \(w\) 的欧氏长度平方，以及每个单位屏幕向量的二次型值，均有一致正下界。代入 \(e=\xi/|\xi|_E\) 得到偶的符号，并在 \(\xi\) 正伸缩下保持不变。
- 对度规迹和 Lorentz 收缩都为零的复振幅，冻结度规下带密度的 Fourier Ricci 符号迹反转等于 \(\tfrac12\sqrt{|\det m|}\,q_m(q)J^{\sharp\sharp}=2\sqrt{|\det m|}\,q_m(q)\mathsf C_m J\)。证明使用 \(B=m^{-1}\)，也适用于略离锥的频率。

后续接口包括同一锥邻域内的可逆性和光滑符号界、全局角向截断及有限指数乘子估计，以及复恒等式在变分 Hessian 实际 Fourier 槽中的应用。

## 已登记的 Lean 声明

- `Burnett.V06.frozenNullScreenProjection_constraints`
- `Burnett.V06.frozenScreenProjection_fixed_iff`
- `Burnett.V06.frozenScreenProjection_symmetric`
- `Burnett.V06.exists_uniform_wide_screen_bounds`
- `Burnett.V06.frozenScreenSymbol_even`
- `Burnett.V06.frozenScreenSymbol_degreeZero`
- `Burnett.V06.frozenEinsteinSymbol_screen_phase`

[共同源码对应](frozen-screen-source-bindings.json)
