# 形式化复核与工程状态

## 本轮范围

2026-11-15：仅做工程初始化与锁定原文索引。没有开始证明整篇论文，也没有审稿判断原文结论真假。采用 `paper-results` 第1.2版，完整标准位于 `standard.zh-CN.md`。

原文身份见 `paper/source.json`；主文件176424字节，SHA256为 `e5e9fc351bbd5540884dc7f2fec42cdba94d591a2d4f5ebb4a409f316823904e`。原文副本按原字节保存，用户原件未改动。文稿源码自述为匿名 proposed proof；该措辞是原文身份信息，不是本工程作出的正确性结论。

标准 SHA256：`8caad6c9439a86c17567c84bcc065c24a44e11830657ff9996bb13f259cae2f0`。

## 范围及数学状态

正式结果环境的来源索引与初始 inventory 见 `../statements/source-index.json`、`scope.json`。17项均待建模；尚无完整数学/Lean对应、实际Lean类型或证明。关键未编号结果、必要定义与依赖闭包仍待独立核对，不能据环境计数声称全部正式结果覆盖已复核。

项目状态：`development`。实际 Lean 论文目标：0。最终信任政策：`pending-user-decision`。当前工具可用的标准三公理配置不构成用户选择。Mathlib兼容版本尚未选择。

独立反向语义核验：未开始。论文结果覆盖的独立复核：待完成。用户/作者对数学解释的确认：尚未发生。额外未证接口：尚未开始建模，当前没有以条件参数替代论文目标。

## 机器证据

Lean工具链固定为4.24.0，无外部依赖；库入口为空命名空间文档。检查入口为 `scripts/check_project.py`。本地初始化构建和hash/配置检查的实际结果保存在忽略目录 `.project-verification/`；检查记录明确 `paper_formalization_verified: false`，不属于论文目标证明或传递公理闭合证据。

CI配置为运行相同入口；实际执行与结论见 [GitHub Actions](https://github.com/Oho1e/Burnett-conjecture/actions) 及运行绑定的提交。配置文件本身不作为执行证据。构建绿色只反映当前阶段工程检查。

## 远程发布

用户指定：owner `Oho1e`，名称 `Burnett-conjecture`，私有。已使用用户完成登录的账号创建 [私有仓库](https://github.com/Oho1e/Burnett-conjecture)，并通过 GitHub API 再次确认 private=true。初始代码推送与 CI 的固定提交/运行记录以 GitHub 及本轮工程证据为准。建库和工程检查不表示论文已形式化；没有发布论文已验证标签。
