# Hilbert 空间闭凸集投影性质
# 命题：投影算子的 1-Lipschitz 连续性
证明：在实内积空间 $E$ 中，对于闭凸非空集合 $C$，其投影算子 $P_C$ 满足：
$\|P_C(x) - P_C(y)\| \le \|x - y\|$ 对于所有 $x, y \in E$ 成立。

## 1. 最小化距离
在 Hilbert 空间 $H$ 中，点 $x$ 到闭凸集 $C$ 的投影 $p = \text{proj}_C x$ 定义为：

$$p = \arg\min_{z \in C} \frac{1}{2}\|z - x\|^2$$

最优解 $p$ 的一阶必要充分条件（最优性条件）为：
$$\langle \nabla f(p), y - p \rangle \geq 0, \quad \forall y \in C$$

由于 $\nabla f(p) = p - x$，代入整理得到 **变分不等式 (Variational Inequality)**：
$$\langle x - p, y - p \rangle \leq 0, \quad \forall y \in C \quad \dots (1)$$

---

## 2. Pythagoras 型恒等式
对于任意 $y \in C$，由内积性质展开：
$$\|x - y\|^2 = \|(x - p) + (p - y)\|^2 = \|x - p\|^2 + \|p - y\|^2 + 2\langle x - p, p - y \rangle$$

知 $\langle x - p, y - p \rangle \leq 0$，因此：
$$2\langle x - p, p - y \rangle = -2\langle x - p, y - p \rangle \geq 0$$

由此得到 **Pythagoras 不等式**：
$$\|x - y\|^2 \geq \|x - p\|^2 + \|p - y\|^2$$

---

## 3. 1-Lipschitz
取两点 $x_1, x_2 \in H$，其投影分别为 $p_1, p_2$。

### 利用变分不等式
* 对 $x_1$ 投影，取 $y = p_2 \in C$: $\langle x_1 - p_1, p_2 - p_1 \rangle \leq 0$
* 对 $x_2$ 投影，取 $y = p_1 \in C$: $\langle x_2 - p_2, p_1 - p_2 \rangle \leq 0$

### 组合
将上述两式相加并提取公因子：
$$\langle (x_1 - x_2) - (p_1 - p_2), p_1 - p_2 \rangle \geq 0$$
$$\|p_1 - p_2\|^2 \leq \langle x_1 - x_2, p_1 - p_2 \rangle \quad \dots (\text{Firmly Non-expansive})$$

### 1-Lipschitz
**Cauchy-Schwarz 不等式**：
$$\|p_1 - p_2\|^2 \leq \|x_1 - x_2\| \cdot \|p_1 - p_2\|$$

得：
$$\|\text{proj}_C x_1 - \text{proj}_C x_2\| \leq \|x_1 - x_2\|$$
