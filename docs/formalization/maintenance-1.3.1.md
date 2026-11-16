# 1.3.1维护：输入快照与PR证据交接

本轮修改工程工具及说明，数学标准仍为paper-results1.2。论文、Lean证明、21个数学支持目标、信任决定和已有语义确认范围保持不变。旧1.3技能包及F06历史回执保留；旧指纹不回写为新值。

本轮到可审阅PR为止，不执行合并。用户尚未选择未来最终合并执行者，工具允许明确记录pending，不默认替用户选择人类或代理。

## 输入快照

普通入口仍为`python scripts/check_project.py --repo .`。工程入口向底层check_paper传递：

```text
--generated-root .project-verification --entry-module Burnett
```

额外生成目录是显式、根级边界；通用检查器默认不新增该排除。配置、manifest、注册模块源码与该目录重叠时拒绝。其余项目Lean源码仍保守纳入，包括未跟踪或Git忽略的源码；不按Git状态代替核验输入。策略与额外入口一起写入输入指纹。

声明排除时，真实Lean审计输出目标和额外入口实际加载的直接/传递模块路径。Python核对源码及olean路径，拒绝从生成证据目录加载模块，并确认普通本地源已在输入快照且内容一致。临时证据增长不再参与中央输入稳定性判定；所用辅助探针、审计代码与日志仍各自保留哈希。

该守卫已在本项目固定Lean4.24.0、默认源码布局上实测。findLean是源码搜索映射，不证明任意多srcDir/同名源根的对象编译来源；既有SDK、固定依赖及预编译缓存信任仍需按原政策说明。布局变化时先适配实测，不能将生成目录约定写成任意项目的完整依赖保证。

## PR与保护判定

`scripts/pr_readiness.py`只读取明确JSON并输出判定，不访问网络、调用Git、修改文件或执行合并：

```text
python scripts/pr_readiness.py readiness --expected <本PR版本锁.json> --observed <本轮API观察.json>
python scripts/pr_readiness.py protection --expected docs/formalization/github-policy.json --observed <本轮保护回读.json>
```

两项结果分别检查，交接时须同时成立。就绪判定绑定仓库、PR、branch、受审head、当前base/main、实际组合候选，以及CI run、job/check-run身份、实际成功步骤和候选工件。GitHub运行的head_sha保留其原值，不能改写成组合候选SHA凑一致。缺字段、旧版本、错身份、步骤被跳过或工件失效均不能通过。

保护比较依据本项目[期望配置](github-policy.json)，逐项核对PR要求、批准数、严格检查及提供者、管理员适用、禁止强推/删除、线性历史、讨论解决和合并方式等已约定字段。旧[配置观察](github-settings.json)只是历史回读，不冒充当前状态；未知字段不默认通过，也不以两个布尔值代表整套约定。观察器应保存原始API事实及标准化来源，字段归一化不改变其含义。

纯判定不验证输入来自真实API或仍然最新；协调者从当前服务端获取证据，并在head/base变化后刷新受影响部分。它也不产生数学复核、用户确认或远程操作授权。

## 最终执行者及交接

明确选择human时，机器条件满足输出`ready-for-human-merge`；明确pending时输出`checks-passed-awaiting-merge-actor`。后者只表示所给机器条件吻合，不表示已选择执行者或允许AI合并。缺少执行者字段不会默认人类。

由人类执行时，代理交付PR链接、实际head、最新组合CI、独立复核、剩余问题及建议合并方式。人类在GitHub核对当前版本后执行Squash and merge；这项操作不意味着人类逐行审过Lean，也不签发数学认证。由代理执行须有对应的明确授权；本维护工具本身没有合并能力。同一GitHub账号下，分工属于工作流/工具边界，不能声称平台能仅凭账号识别操作者。

未合并时只报告就绪/待决，不报告本次整合完成。实际合并后，再在当前可观察会话或获授权的后续任务核对精确main的CI；不为等待人类点击建立自动后台监控。

## 验证与维护频率

- `scripts/test_pr_readiness.py`直接测试实际纯函数和CLI，包括旧候选、错身份、跨run拼装、缺失/跳过步骤、失效工件、保护偏离、pending及严格JSON边界。
- `scripts/test_snapshot_policy.py`包含快测和可选真实Core-only Lean fixtures，直接断言源集合及有效源码变化，也验证真实生成依赖与运行中变更被指定守卫拒绝。坏证明拒绝不能替代快照覆盖测试。
- 原`test_check_paper.py`继续验证编译、定理类别、来源及传递公理的原拒绝行为。
- `maintenance-check.yml`只在工具相关PR路径变化或手动触发时运行维护套件；普通数学交付不必重复整套维护负例。原项目构建和切片CI继续。

本地与CI的实际命令、跳过项、独立审查及PR状态另记本轮维护报告。函数级样本、受控时间注入、真实Lean运行和真实GitHub运行分别标明，不外推为所有故障或全部数学内容已验证。
