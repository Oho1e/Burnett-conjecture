# 局部 H⁻¹ 的分析核心

本批对应原文384–388行，新增六模块75声明，选择14个语义端点登记。它提供两种真实分析消费者：强零L²余项的方向导数，以及具有共同光滑紧截断的有界L²源。准确源码、类型与独审身份见[绑定](analysis-hminus-source-bindings.json)及[复核](analysis-hminus-review.md)。新解释的作者确认尚未记录，父结果和整篇认证不因此完成。

## 实际测试空间与范数

空间为实四维EuclideanSpace。D是全部真实实值C∞紧支撑测试的子模，Jφ由φ和四个实际Fréchet方向导数组成，置于五槽真实L² Hilbert空间。H¹模型取J(D)的闭包；testMap具有实际稠密像，连续泛函由所有真实测试上的值唯一确定。H⁻¹模型是其真实连续实对偶，使用operator norm。

任意真实L²源u及方向v构造方向分布泛函，测试值为−∫u D_vφ，operator norm≤‖v‖‖u‖。若u由真实smooth函数f表示，局部积分分部把它识别为∫φ D_vf，并证明该测试积分实际可积。没有要求D_vf属于L²，也不要求f自身紧支撑。强零L²序列的这些泛函及范数实际强趋零。

## 同一截断下的 Fourier 与对偶桥

实smooth序列fₙ有同一真实χ∈D，在所有fₙ非零处χ=1；真实L²范数有统一有限界，且每个固定φ∈D的∫fₙφ趋零。参数、χ和测试均先于n固定。

该χ和L²配对给真实L¹可积及统一Fourier上界。固定实测试先作真实实部/虚部复化，再用χ乘负2π相位，得到每个频率的实际Fourier变换趋零。真实Schwartz转换和固定频球的有限测度、同一主控函数给平方能量DCT。

唯一权重为W(ξ)=1+4π²‖ξ‖²。实际Schwartz导数Fourier公式和Parseval证明

    ‖Jφ‖² = ∫ W(ξ) |Fφ(ξ)|²。

实际weighted L²构造、Cauchy–Schwarz及Plancherel配对先给所有真实测试的界，再由testMap稠密与闭不等式扩到整个H¹模型，得到真实sourceFunctional的operator norm≤sqrt(∫|Ff|²/W)。没有把这条桥作为调用者假设。

高频部分实际证明：非负可积能量F的全负阶积分≤频球内积分+C/R，R先于n固定。由Parseval给统一全频能量，再令固定球内能量趋零，得到∫|Ffₙ|²/W及其sqrt趋零。

最终CompactRellich消费者内部构造同一序列的实际Fₙ，返回所有n、所有真实测试的积分身份、Fₙ强零和‖Fₙ‖趋零。eLpNorm接口的指数为2，界是L²范数界；它内部证明各项MemLp。函数型见证置于所有测试之前，不按测试重新选取。

## 生产模块和剩余边界

StrongL2Hminus、LocalHminusFourier、H1FourierEnergy、HminusWeightedDual、WeightedFourierTail、CompactRellich分别含18、13、11、21、8、4项。三个文件的module名与声明namespace不同，登记使用各自准确qualified name。frequencyWeight只在H1FourierEnergy定义一次。

这些是一般分析支持。原真空序列的实际局部化、有限早期指标、主算子精确分解、同一背景和见证的装配，须以相应几何交付另行登记。完整Lorentz/真空数据实例化、全局张量接口、F04/F05及输运仍不由本批自动关闭；未增加uniform D²gₙ或全局光滑标架假设。文章及信任A保持锁定。
