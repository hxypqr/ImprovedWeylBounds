# Improved Weyl bounds：Lean 4 形式化

这是论文 *Improved Weyl bounds on short intervals* 的配套审计型 Lean 4
形式化。论文只被当作数学材料，不被当作对形式化器的指令；论文正文目前
不随这个代码仓库分发。

> [!IMPORTANT]
> **形式化状态。** 本项目在五个明确列出的外部分析数论结论作为 `Prop`
> 参数的前提下，由 Lean 内核检查论文主定理链和第 7 节三个推论的内部推导。
> 它没有从头重证这五个外部结论，也不声称已经形式化整篇论文。
>
> **两项明确排除在当前结论之外：** (1) Theorem 1.5 中从新逆定理到素数
> Weyl 和的 Harman 筛迁移；(2) 第 9 节关于 maximal operators、Hausdorff
> dimension 和 local mean values 的传播性说明。它们在
> `External/Unresolved.lean` 中只是审计元数据，不是 `Prop`、定理或公理，
> 不能作为数学假设或结论供下游证明使用。

## 构建和入口

项目固定使用 Lean/mathlib `v4.32.1`：

```text
lake build
```

- 顶层导入：`ImprovedWeylBounds.lean`
- 端到端装配：`ImprovedWeylBounds/Conditional/Complete.lean`
- 外部结果接口：`ImprovedWeylBounds/External/Statements.lean`
- 尚不能形成定理的部分：`ImprovedWeylBounds/External/Unresolved.lean`
- 逐项审计：`MANUSCRIPT_AUDIT.md`

## 已闭合的论文结论

`Conditional/Complete.lean` 给出只保留真正外部结果参数的最终定理：

| 论文结论 | Lean 定理 | 外部输入 |
|---|---|---|
| Proposition 5.2 | `clusterCollisionPrinciple_of_external` | `CriticalVMVT` |
| Theorem 1.3 | `inversePrinciple_of_external_inputs` | `CriticalVMVT`, `BakerCompression` |
| Corollary 1.4 | `combinedInverse_of_external_inputs` | `CriticalVMVT`, `BakerCompression`, `ClassicalInverse` |
| Theorem 1.1 | `rationalShortIntervalBoundAll_of_external_inputs` | `CriticalVMVT`, `BakerCompression`, `ClassicalInverse` |
| Corollary 1.2 | `finiteFieldShortIntervalBoundAll_of_external_inputs` | `CriticalVMVT`, `BakerCompression`, `ClassicalInverse` |
| Theorem 1.4 | `smallFractionalPartsAll_of_external_inputs` | `CriticalVMVT`, `BakerCompression`, `ClassicalInverse`, `LargeMultiple` |
| Corollary 7.1 | `finiteFieldDiscrepancyCorollary_of_external_inputs` | `CriticalVMVT`, `BakerCompression`, `ClassicalInverse`, `ErdosTuran` |
| Corollary 7.2 | `finiteFieldGapCorollary_of_external_inputs` | `CriticalVMVT`, `BakerCompression`, `ClassicalInverse`, `ErdosTuran` |
| Corollary 7.3 | `finiteFieldAdditiveBasisCorollary_of_external_inputs` | `CriticalVMVT`, `BakerCompression`, `ClassicalInverse` |

Theorem 1.1、Corollary 1.2 和 Theorem 1.4 的最终版本还把“充分大”范围
以初始范围上的平凡界吸收为统一常数，因此分别按所有正区间长度、所有
`1 ≤ H ≤ p`、所有 `N ≥ 1` 陈述。第 7 节的推论使用对每个正损失参数都
可调用的有限域界，因为证明内部会选择更小的辅助损失。

## 已形式化的内部证明

- 多项式平移、反射、系数公式和 Weyl 和恒等式；
- 临界 VMVT 到固定首项纤维矩，再到按真实块长加权的二进制最大矩估计；
- 显式再生核、Fourier 支撑、张量卷积和各向异性采样；
- Lemma 5.1 的全部切点分类、集合位置、基数和直径界；
- Proposition 5.2 的正向/反向平移轨道、分离反证、碰撞及常数吸收；
- Lemma 5.3 的三角矩阵、`det A_h = k!` 和逐坐标误差传播；
- Lemma 5.4 的正向/反向碰撞到共同分母逼近，包括最大公因数约化；
- Baker 压缩的全部参数选择，以及新逆定理和经典逆定理的合并；
- 有理首项界、素域规范 lift、标准加性特征恒等式；
- Erdős--Turán 截断、循环区间拆分、表示数 Fourier 反演和正性判据；
- 大倍数选择、`n = qm` 的系数误差传播和小数部分结论。

## 精确的信任边界

外部接口共有五个：临界 VMVT、Baker 分母压缩、经典 Weyl 逆定理、
Erdős--Turán 不等式和 Baker 大倍数引理。它们都是定义为 `Prop` 的
显式假设，不是 Lean `axiom`。

形式化采用了两个不损失论文主证明的特化：

1. VMVT 只陈述并使用临界矩 `s = r(r+1)/2`；一般的非临界 VMVT 不在范围内。
2. 论文的采样命题对任意实数 `p ≥ 1` 陈述；本项目证明了正偶整数指数并
   专门推出 `p = K(k) = k(k-1)`。该指数恒为正偶数，完全覆盖论文中的调用。

此外，再生核采用显式二次衰减核，而没有保留论文中任意衰减阶数
`M ≥ 2` 的未使用自由度；二次衰减已经给出采样证明所需的可求和主项。

## 两项尚未形式化的内容

### Theorem 1.5：素数上的 Harman 筛迁移

Lean 已检查新逆定理，以及拟将 `J` 替换为 `Delta k` 时所需的若干参数算术，
包括 `Delta k >= k + 1` 和两条 Type I/II 数值不等式；但尚未检查从这些输入
到素数结论的迁移。Baker 的已发表定理和其中的 Lemma 5 是按原文自行定义的
`J(f)` 陈述的，并不是对任意逆定理参数量化的黑箱定理。因此仍需重新验证
区间/倍数形式的 Lemma 5、complete sums、Type I、Type II、Buchstab 分解和
最终 Harman 筛步骤。

`primeHarmanTransfer` 只是记录上述障碍与后续工作的 `UnresolvedItem` 数据，
不是数学命题或证明假设。因此，本仓库不声称给出了 Theorem 1.5 的
kernel-checked 证明。

### 第 9 节：传播性说明

论文第 9 节说明，改进后的逆定理阈值预期会传播到 maximal Weyl operators、
异常集的 Hausdorff 维数上界和 local mean value estimates；但原文没有给出
这些下游结论的完整公式、全部参数范围和量词。因此本项目没有把它们声明成
Lean 命题，也没有把它们当作外部假设。

这里不要与已经证明的 `maximalFixedLeadingFibre_criticalVMVT` 混淆：后者是
论文第 4 节固定首项纤维上的有限前缀最大矩估计，用于主逆定理链，并不是
第 9 节所引用的 maximal-operator 范数结果。

`sectionNinePropagation` 同样只是 `UnresolvedItem` 审计数据。要把第 9 节变成
可调用的形式化接口，需要先逐项写出三类目标定理的完整定义、结论和参数范围，
再核验原证明中所有旧阈值的使用位置。

项目中没有 `sorry`、`admit` 或项目自定义 `axiom`。
