# 具有超越 Turán 密度的三均匀超图：Lean 形式化

形式化项目作者和负责维护者：**Xizhi Liu**。项目采用 Apache-2.0；复用代码保留
原作者声明和许可。公开仓库为
[xliu2022/transcendental-turan-lean](https://github.com/xliu2022/transcendental-turan-lean)。

本项目形式化证明：存在一个可由明确有限算法构造的、至少有一条边的有限三均匀
超图，其普通 Turán 密度是超越数。来源手稿日期为 2026 年 11 月 18 日；来源指纹、
复用代码和证明改写说明见 `provenance/` 与 `docs/PROOF_MAP.md`。

## 主定理

`Solution.lean` 通过 `TranscendentalTuran.Main` 导出：

```lean
theorem TranscendentalTuran.main_result :
    ∃ n : ℕ, ∃ P : TuranUniversality.RGraph (Fin n) 3,
      P.edges.Nonempty ∧
      Transcendental ℚ (TuranUniversality.turanDensity P)
```

这里的包含关系是保边的全局单射，包括对孤立顶点的单射要求。极值数是在实际的
有限禁图宿主上取最大边数，Turán 密度按二项式系数归一化。项目证明其定义中的
下确界等于通常的极限，不需要额外假设收敛性。

具体见证是 `Construction.singleGraph`，并且证明了

\[
\pi(P)=6\,\Psi\!\left(22-\frac{1024}{15\pi}\right).
\]

右侧的 π 是圆周率；Ψ 是保留各个根权重自由变量的精确有理优化问题。系数 6
来自三均匀超图边多项式与普通密度的归一化换算。

## 证明结构

除最后一行外，下表目录均位于 `TranscendentalTuran/`。

| 目录 | 数学作用 |
| --- | --- |
| `Construction/` | 具体参数、根补全、极值点局部化、类型变换及最终有限超图 |
| `Encoding/` | 十七条局部规则、有界违规证书与可判定的有限禁止模式 |
| `Network/` | 实际网络能量、串联约化、归属关系与源增益上界 |
| `Green/` | 象限行走、Green 常数计算、有限网络与下界实现 |
| `Optimization/` | 自由根权重下的精确优化问题及质量约束 |
| `Algebra/` | 有理实代数消元和最小值代数性，用于超越性证明 |
| `Transfer/` | 将中间类的加权上确界转移到单个有限超图的普通密度 |
| `External/Pi/` | 圆周率超越性的已证明外部形式化及适配 |
| `TuranUniversality/` | 复用的超图、加权模型和极值密度基础库 |

详细的数学接口、上下界、极限顺序和手稿对应关系见
[证明路线](docs/PROOF_MAP.md)。

## 独立声明与可执行构造

`Challenge.lean` 只导入 Mathlib，独立重述图、普通嵌入、极值数、密度和主定理。
其中一个 `sorry` 是用于 Comparator 的有意目标占位。正式证明不导入 Challenge；
证明开发中的零占位声明不包括这个独立题目文件。

`Construction.buildSingleGraph : Bool → Option (FiniteGraph 3)` 是已编译的
常规函数，启用分支返回具体见证。项目证明了其输出正确性。由于规模极大，完整
构造尚未实际求值，未列出全部顶点和边；仅对关闭分支进行了初始化求值检查。

## 已保存的验证证据

当前归档记录显示：

- 322 个本地 Lean 模块全部通过 Lake 构建，默认构建完成 3,941 个任务。
- 13 个主要声明的传递公理审计仅依赖 `propext`、`Classical.choice`、`Quot.sound`。
- 独立声明比较和许可公理检查通过；Lean 内核与 NanoDa 接受了证明。
- 经认证的 con-ron 重放因 `fuel-exhausted` 未完成，按固定策略分类为建议性
  decline；正负控制通过。这不表示 con-ron 接受了完整证明。
- 早期失败记录仍然保留。没有宣称完成独立人工数学审阅或获得 Palomar 注册。

证据、源码哈希清单和各次验证的适用范围见
[verification/README.md](verification/README.md)。这些是随源码保存的验证记录；
新提交的 GitHub Actions 状态应在仓库 Actions 页面单独查看。

## 构建与验证

项目固定 Lean `4.35.0-rc2` 和 Mathlib 提交
`065356127b1dc0016f66b7283ce0ce2c4055aa55`。需要 Python 3、Ruby，以及已安装的
Lean 工具链管理器 elan。

```sh
# 只检查源码格式和元数据，不安装依赖。
bash verify.sh --checks-only

# 获取依赖缓存、构建全部本地模块，并审计最终公理。
bash verify.sh

# 降低同时运行的编译进程数量。
TURAN_BUILD_JOBS=1 bash verify.sh
```

在支持 bubblewrap 的 Linux 环境中，还可以运行：

```sh
bash verify.sh --comparator
```

此选项额外执行独立声明比较和 Lean/NanoDa 检查。单独的 con-ron 重放与完整官方
预检的区别见英文 README。新构建日志写入临时目录，不覆盖归档证据。

## Palomar 提交

提交入口为 <https://submit.palomar-registry.org/>。填写时使用：

- 仓库：`xliu2022/transcendental-turan-lean`。
- Commit：已推送且准备送审的完整 40 位 SHA，可用 `git rev-parse HEAD` 获取。
- Comparator 配置：`comparator.json`。
- 项目目录：仓库根目录，表单可留空。
- 元数据：根目录的 `formalization.yaml`，表单的可选路径可留空。

`.github/workflows/palomar-preflight.yml` 提供手动触发的官方完整机械预检，固定
验证器版本，并采用 `mode: full` 和 `palomar-standard-v1`。预检与正式提交、审阅、
注册是不同步骤；运行预检不会自动注册结果。最终注册使用固定提交快照。
请以 [Palomar 当前提交说明](https://palomar-registry.org/how-to-submit) 为准。
