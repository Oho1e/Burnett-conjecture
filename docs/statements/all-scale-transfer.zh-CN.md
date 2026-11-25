# 全尺度与相邻帽三线性估计

[English](all-scale-transfer.en.md)

原稿对应区间为第 1026–1245 行。

- 未缩放界作用于实际弧度制三线性形式，保留原第三频率。每一因子可各取有限频率指标及模长不超过一的权重。
- 相邻帽界使用单一帽指标与三个投影场共用的放大帽等一条件。系数因子 `δ²` 结合角向计数得到原稿的幂次。
- 有界可测标量符号及 Schwartz 界给出三槽复线性的 L³ 延拓，常数与原界相同，延拓在原 Schwartz 代表上还原 Fourier 公式。
- 具体应用须为所用符号提供三个放大帽等一条件和归一化 C¹⁰⁰ 界。

本次登记覆盖下列具体 Lean 声明。原定理的确认及发布检查另行记录。

- `Burnett.A05.exists_unscaled_radianTrilinearForm_bound`
- `Burnett.A05.exists_radianTrilinearForm_factorwise_truncation_bound`
- `Burnett.A05.exists_actual_radian_near_field_bound`
- `Burnett.A05.exists_radianTrilinearForm_Lp3_extension`

[共同源码对应](all-scale-transfer-source-bindings.json)
