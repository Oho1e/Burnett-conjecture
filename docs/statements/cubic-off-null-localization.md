# X02：固定Fourier离零锥梯度局部化（必做、证明已实现）

源为锁定paper/burnett.tex第3193行最后一句，claim_id为unnum:cubic-off-null-gradient-localization。用户2026-11-16先选2A明确纳入最终目标，随后选择固定Fourier锥投影；没有要求一般依赖位置x的Ψ⁰投影，也没有批准改写整个Fourier/Rellich证明路线。

保留prop:cubic的同一fSequence、wSequence，分别对h=f和h=w。对每个固定实χ∈C∞c(R⁴)、每个固定δ>0，设q(ξ)=−ξ₀²+ξ₁²+ξ₂²+ξ₃²，Eδ={ξ≠0: |q(ξ)|≥δ|ξ|²}。目标是局部化梯度在该离锥频率区域中的全空间L²能量趋零，因此得到相应固定Fourier投影L²范数趋零；覆盖光滑锥截断和锐锥投影。符号、χ、δ均在n趋于无穷前固定，不要求对趋零δ或n依赖的截断一致。

Fourier乘子须由实际Fourier变换、符号乘法及逆变换构造。锐锥特征函数给真实正交投影；光滑角截断是通常所称的频率局部化算子，不额外要求其符号平方等于自身。作用于四个梯度分量，使用欧氏正L²范数。需要实际处理归一化、零频a.e.及投影的非紧支撑尾部。

两种表述A(χ∇h_n)与A(∇(χh_n))之差为A((∇χ)h_n)，应由既有幅度小量和实际L²算子有界性证明等价，不能把χ和非局部投影交换。目标可先用离锥Fourier能量表述，再覆盖固定有界乘子；不存在尚未实现却被当作参数的“会消去该序列”假设。

第一批已为同一fSequence/wSequence、任意原有实C∞c截断及固定δ>0证明实际Fourier全Eδ能量的四分量总和趋零；实际正负频率、2π调制平移、全空间尾及Schwartz Parseval均有Lean证明。另已构造两种cutoff位置的真实L²对象，证明它们在任意固定连续线性映射下之差趋零。该阶段仍是部分形式化，实际声明与分批独立回读见[第一批基础证明](initial-foundations.md)及[复核](initial-foundations-review.md)。

第二批已实际证明Schwartz在L²中的稠密性、构造Fourier等距同构、真实锐锥正交投影和有界乘子，并接合到原见证。父目标现登记实际声明 `Burnett.CubicOffNull.fixed_offNull_gradient_localization_away_zero`：对原范围中每个固定有界符号，四个梯度分量的物理全空间正L²强零同时覆盖f/w及两种cutoff位置；非零频率上要求支撑于Eδ，零频任意赋值通过a.e.等价消去。锐/光滑类均有真实实例，正交性及非紧物理输出尾得到处理。

新增九模块范围与独立实际回读见[第二批证明](second-foundations.md)、[复核](second-foundations-review.md)和[源码绑定](second-foundations-source-bindings.json)。本父项的Lean状态是proof-implemented；新增数学解释的人类确认、最终工程检查和主线整合分别记录，旧prop:cubic委托不自动覆盖此次新增解释。原范围、三公理政策和整篇verified=false保持不变。
