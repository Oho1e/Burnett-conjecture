# 隔离决策探针：F06 实混合极化整合门槛

观察快照：2026-11-15 15:41:37 UTC（北京时间23:41:37）。本报告只判断所提供的当前本地快照，不判断后来产生的证据。

本次为隔离决策探针，无真实远程 mutation。仅以只读方式读取项目规则、当前范围/切片、所列 PR/机器收据及相关解释/复核材料，并计算输入哈希；未访问网络，未执行 Git、Lean、Lake、构建、真实 PR 或合并操作。唯一写入为本报告。它不代替独立数学回读、用户/作者确认或真实合并检查，也不是一次被平台实际拒绝的合并尝试。

## 判断

**不可据当前快照放行进入 main，也不可报告“本次整合完成”。可以继续完成本次局部交付的最终工程检查和 PR 整合。**

局部独立语义回读已经存在，并且其绑定输入与当前相关文件一致；它不是本判断所缺的项目。缺口在当前数学交付的完整机器检查及最终 PR 候选/主线证据。初始草稿 CI 的绿色不能补这些缺口。合并后 main CI 本来就应在实际合并后取得；缺少它不构成要求先合并前取得未来证据，而是说明现在尚不能报告整合已经完成。

## 已有证据与仍缺证据

| 项目 | 当前已有 | 当前门槛判断 |
| --- | --- | --- |
| 交付边界 | `f06-workflow-test.md` 明确选择 F06 的实混合极化局部交付；不提升整个 F06 或17项编号结果 | 范围合适。复 Hermitian、零标架/物理商正性、几何/测度桥接仍开放，与局部开发整合相容 |
| 随交付登记 | `Burnett.lean` 已导入 `RealPolarization`；scope 有21个目标、86条 inventory，其中12个 `polarization:` 目标和对应 inventory；12条 placement 均映射 F06 | 本地登记已准备好，但不能由本地文件存在推定它们已经进入最终 PR 候选 |
| 独立语义回读 | `real-polarization-review.md` 记录先独立提取原文规格，再读冻结源码、重要定义和全部29项实际类型，局部核对通过；另核对普通数学解释及12目标映射 | 可按其局部范围沿用。本探针实际核对其15个输入哈希，均与当前文件一致。`reviewed_head=null` 不抹去已存在的独立回读，只说明最终提交绑定尚未填实 |
| 中央实际类型/公理查询 | `actual-types-receipt.json` 的 source SHA为 `5993bc61…7dd4`，exit_code=0、status=passed；29个声明齐全，missing为空、unexpected为空，均仅标准三公理；查询源和日志哈希与独立回读绑定一致 | 是适用于当前冻结模块的查询证据。它不单独代替完整库构建、21个注册目标的存在性/来源/传递公理检查及相关切片检查 |
| 最终本地工程检查 | scope 中12个新条目仍为 `implemented-pending-central-check`；`f06-workflow-test.md` 仍写“执行中”，阶段证据待补 | 所读快照未给出适用于当前21目标最终交付的完整工程通过证据；应实际执行或补入已有适用收据，再按事实更新状态。不能把 pending 字段单独解释为数学失败 |
| PR 组合检查 | `draft-ci.json` 与当前 `pr-ci.json` 相同：PR2、head `896c883e…f749`、base/main `6880f4ab…9103`、candidate `839e172a…af4`，run `43729124482` 为 pull_request/success，`project-check` 实际步骤均 success，artifact 名含该 candidate | 这是有效的初始草稿历史。监督记录明确它对应新增 Lean 目标前的9目标快照；不能认证现在的21目标候选。快照仍 draft=true、merged=false，且配置 `reviewed_head=null`；缺最终受审 head、最新 base/候选及其真实组合检查绑定 |
| 合并及 main CI | `github-config.json` 仅预设 `main_receipt: main-ci.json`；该文件当前不存在；没有实际 squash 后 main SHA及其 push CI成功记录 | 尚无整合完成证据。即使补齐合并前门槛，仍须实际合并并确认精确 main 提交的 CI 后才能报告完成 |

独立回读所说“没有亲自运行 Lean/CI”与其职责相容：它独立解释了协调者产生的实际机器类型，并未冒充自己运行过构建。中央查询与独立解释是两个分别记录的事实，本探针不再制造第三份数学签字。

## 应采取的下一步

1. 协调者冻结实际将交付的版本，确保源码、库入口、12个新目标、scope/切片映射及必要说明在同一个候选中。完成或提供适用于该实际输入的完整 `check_project`、全部21目标的来源/传递公理检查及相关切片检查；依据真实结果更新 pending 状态，保留先前失败和初始草稿收据。
2. 将已有局部独立回读绑定到实际最终数学 head。当前已核对的冻结源码、相关定义、工具链、依赖和解释均匹配，无须重复整套回读；若候选之后有实质变化，仅补查受影响部分。`reviewed_head` 应填写实际已审提交，不能只为让门槛通过而写入任意值。
3. 在项目既有授权下，由协调者核对真实 PR 的最新 head、当前 main/base及合并候选；取得覆盖当前交付的组合 CI，核实应执行步骤和目标确实运行。主线若前进，刷新组合检查及受影响证据。随后按已检查 head 执行既定 ready/squash 流程；本探针不执行这些操作。
4. 实际合并后记录 PR head到最终 squash/main 提交的对应，并确认该精确 main 提交的 push CI成功，才写“本次局部交付整合完成”。失败或结果不明时暂停后续合并并诊断，不能沿用旧绿色或削弱目标/检查。
5. 最终报告分别陈述局部数学内容、未闭合义务、机器检查、独立语义复核、作者确认/信任状态和远程整合状态；实际执行、此隔离探针及未测试故障路径分别记录。

## 不应因此触发的重做或额外门槛

- 不要求先闭合复 Hermitian、物理商正性、全部 F06、17项编号结果或整篇论文，才能合入本次准确标识的开发成果。
- 不因本文档/登记更新或 head SHA变化，就重读全文、重做全部范围审计或重复已适用的局部独立语义回读。已有全文范围待核仍需为最终整篇认证解决，但不是本次局部开发合并的新前置条件。
- 不把 `human_semantic_confirmation=pending`、最终信任政策待决当成每次例行开发合并必须重新申请用户批准的理由。应继续如实保留 pending；代理复核、编译或合并都不产生人类确认，也不支持整篇 verified 标签。若以后改变数学含义、补假设或扩确认范围，才按对应规则处理该处决定。
- 不要求 mathlib 投稿级泛化、所有辅助引理独立登记为论文结果、固定代理配额或另建重复账本；本次12目标与29项公共声明的分别审计已经有明确说明。
- 不新增第二 GitHub账号 Approve 门槛，也不把同账号代理报告当作另一账号审批；沿用项目既定单账号 PR/CI与独立复核安排。
- 不改锁定原文、升级依赖、重做无关维护负例套件、删除失败记录、放宽信任、移除目标或跳过检查以取得绿色。

## 快照绑定

下列哈希为本探针实际读取时的 SHA256。后续进展不回写本次探针为“当时已通过”。

| 输入 | SHA256 |
| --- | --- |
| `AGENTS.md` | `ac50deefc592397a8e2d502f9bf853b741d1d9463ad424428c69a708833c5279` |
| `docs/formalization/f06-workflow-test.md` | `a895c7c1a0fa5361edd3f8dc3abe968c1a9f8a5a3e2eb67d6d7c0091a60b9a84` |
| `docs/formalization/scope.json` | `163bca895aa34dd4f9ed28402b9919b2f6def42df4bb29e72b29e4887fdebcdc` |
| `docs/formalization/slices.json` | `ae444bcb40341b135d1a16088f80fc4e309fe072b3ca6f84ab22b7621aa5101e` |
| `docs/formalization/slices.md` | `9863f2d1b83f7ec573d052e16f7613bbbcea8aa14fda4cc54a4d0c9eda743c14` |
| `Burnett.lean` | `34e6411d204d1577bece4f8cece686fb4cf603770df9118755d2b440ea81c3aa` |
| `Burnett/Algebra/RealPolarization.lean` | `5993bc6169017387715a3a3e926aa4202ffff3e45ab080414e11f2ef993b7dd4` |
| `docs/statements/real-polarization.md` | `de1ca6bda24b85980fe45968869841696bac314187c83ddd8eeb63ad60d19edc` |
| `docs/statements/real-polarization-review.md` | `fc4f02ad8f5e99e4956b209f6439098fe69d9a6e04edf980277ef059c18c9b8d` |
| `.project-verification/slice-workflow-test/github-config.json` | `9479f7c788b89a1fe60e8f7e360d9d33fc31d6fb8ab93087d1d2d7d6db5012e3` |
| `.project-verification/slice-workflow-test/draft-ci.json`（与所读pr-ci相同） | `f67c183cb5a40fef9643cd348cad6a236f33e9c754539931e21ee318601bc5c2` |
| `.project-verification/slice-workflow-test/central/actual-types-receipt.json` | `4eb035a28887350522cd559c2472b0fdeb261ab764a85a06b6ab83bf734f4ce0` |

另实际核对独立回读表中锁定原文、冻结副本、5个直接导入源、toolchain、manifest、lakefile、实际类型查询源和原始日志，15个表内输入全部匹配。本报告的“不可”是当前证据门槛判断，不是发现局部实代数定理错误，也不声称远程当前状态已获实时核实。
