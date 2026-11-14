# 首个代数片段的集成复核

2026-11-15，只读复核当前配置、源码导入关系、状态措辞与现有机器证据；未新增数学审查，未重跑构建/完整工具套件。

**结论：未发现阻止当前5条支持定理继续集成的配置或源码绑定问题。** 发现的汇总字段读取问题已作最小修正，最终入口待按既定流程刷新。机器通过、独立数学复核、作者确认及整篇完成状态继续分开。

## 固定环境及源码

- `lean-toolchain` 固定 Lean 4.24.0；`lakefile.toml`、manifest 和实际项目 `.lake/packages/mathlib` HEAD 同为 `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`。项目9包的实际 HEAD 逐一匹配 manifest，逐包 `git status --porcelain=v1 --untracked-files=normal` 均为空。
- `.project-verification/dependency-setup.json` 记录独立 Git 对象/工作树检出、未共享对象存储及未复制父缓存。`.project-verification/mathlib-cache-resume.log` 实际记录定向917个缓存文件解包成功；这是当前导入闭包的依赖预编译产物，不是整个 Mathlib 全库重编译或全库缓存齐备的声明。
- `Burnett.lean` 导入 `Burnett.Overview` 和 `Burnett.Algebra.RicciSymbol`；Overview 无反向导入，叶模块只导入5个 Mathlib 模块，未见本地循环依赖。CI/README 的定向缓存模块列表与该叶模块导入相符。
- 当前叶源码 SHA256 为 `f9cfae66918e599d0fb1fc9380118ca6f3a0c96449dc194d69bbca79fb736bf8`，与格式变更记录、目标检查 receipt、独立回读追加记录一致。已用保留旧源逐字比较：去掉文件尾空白后两者相同；未观察到数学 token 变更。
- 项目工作树目前有本轮预期修改及新增文件；目标 receipt 如实记录 `dirty: true`，没有将旧 HEAD 冒充当前源码提交。

## 构建和声明检查的责任

`scripts/check_project.py` 先实际运行 `lake build Burnett`，再对非空目标清单调用原 `scripts/check_paper.py`。原 checker 未被本轮修改；仍拒绝空目标，检查目标来自指定本地模块、属于 theorem，并收集传递公理依赖，再比较检查前后的输入快照。

复核初次读取时，`.project-verification/result.json` 和 `.paper-verification/result.json` 均为 `machine-check-passed`。实际库入口构建日志记录成功；原目标 checker 的模块构建和审计退出码均为0。原 receipt 绑定最终叶源码、scope、工具链、lakefile、manifest 及 checker 哈希；初次读取时关键哈希均与文件一致，外层 receipt 保存的目标 receipt SHA256 也与原 receipt 实际字节相同。随后 scope 的进度文字和 wrapper 摘要取值已修正，因此最终收束应使用既定刷新入口产生的新 receipt，不能把修正前的输入指纹冒充新输入证据；叶源码哈希仍为上述 `f9cfae…`。

预编译缓存用于加载固定依赖；本地构建和声明检查负责当前论文模块及5条登记声明的机器证据。它们不等同于重新核验所有依赖源码，也不判断原文语义或全篇覆盖。checker 产生的 `.paper-verification` 被排除于自身输入快照之外；外层 receipt 绑定内层 receipt，不反过来绑定自己，未见证据哈希的循环依赖。原 checker 另将 `.project-verification` 内现有 `.lean` 探针纳入快照，因此后续更改那些探针会改变其输入指纹，不能静默沿用旧指纹。

**已修正项**：初次读取的 `check_project.py` 使用 `target_result.get("input_fingerprint")`，而原 receipt 的该值在 `target_result["inputs"]["input_fingerprint"]`，导致外层摘要字段为 null；完整目标 receipt 的 SHA256 绑定当时仍有效。现已核实 wrapper 改为直接读取嵌套字段，缺字段按既有 `KeyError` 路径失败；原 checker 保持不变。最终既定入口复跑将刷新外层 receipt，并由集成者核对其摘要是64位且与原 receipt 相同。

## 范围、确认及收束

scope 中只有5条支持目标；17项原编号结果的完成数仍为0，`unnum:quadratic-symbol-algebra` 保持 `partially_formalized`。README 和 Overview 没有声称主定理或整篇已证。外层 `paper_formalization_verified` 与 `semantic_correspondence_verified` 继续为 false；原 checker 自身不负责原文哈希核对，该责任由外层已执行的来源检查承担。

当前源码的独立回读追加记录已经存在，报告项目环境探针退出0、类型与公理输出与格式整理前一致；本次集成复核未代替该数学复核。用户/作者确认仍待实际答复，最终信任政策仍待决。真实新提交的远程CI与旧初始化CI继续区分。

已核实 scope 五条支持项更新为本地机器通过、独立项目环境复编通过；作者确认仍 pending，父项仍为 partial。复核记录及新提交CI按最终实际证据收束。本记录不替代最终入口刷新或真实CI结果；若上述配置或源码随后改变，更新相应哈希和机器记录。
