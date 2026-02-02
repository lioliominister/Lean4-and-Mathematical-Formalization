
## 1. 最小化距离
在 Hilbert 空间 $H$ 中，点 $x$ 到闭凸集 $C$ 的投影 $p = \text{proj}_C x$ 定义为：
$$p = \arg\min_{z \in C} f(z), \quad \text{其中 } f(z) = \frac{1}{2}\|z - x\|^2$$

最优解 $p$ 的一阶必要充分条件是梯度在所有可行方向上的分量非负：
$$\langle \nabla f(p), y - p \rangle \geq 0, \quad \forall y \in C$$

由于 $\nabla f(p) = p - x$，代入整理得 **变分不等式 (VI)**：
$$\langle x - p, y - p \rangle \leq 0, \quad \forall y \in C \quad \dots (1)$$

---

## 2. Pythagoras 型恒等式
对于任意 $y \in C$，考虑以下分解：
$$\|x - y\|^2 = \|(x - p) + (p - y)\|^2 = \|x - p\|^2 + \|p - y\|^2 + 2\langle x - p, p - y \rangle$$

由式 (1)  $\langle x - p, y - p \rangle \leq 0$，则有：
$$2\langle x - p, p - y \rangle = -2\langle x - p, y - p \rangle \geq 0$$

得
$$\|x - y\|^2 \geq \|x - p\|^2 + \|p - y\|^2$$

---

## 3. 非扩张性 (1-Lipschitz) 的证明
取两点 $x_1, x_2 \in H$，记其投影分别为 $p_1 = \text{proj}_C x_1, p_2 = \text{proj}_C x_2$。

1. **利用变分不等式**：
   - 对 $x_1$ 投影，取 $y = p_2 \in C$: $\langle x_1 - p_1, p_2 - p_1 \rangle \leq 0$
   - 对 $x_2$ 投影，取 $y = p_1 \in C$: $\langle x_2 - p_2, p_1 - p_2 \rangle \leq 0 \implies \langle p_2 - x_2, p_2 - p_1 \rangle \leq 0$

2. **相加并整理**：
   $$\langle (x_1 - p_1) + (p_2 - x_2), p_2 - p_1 \rangle \leq 0$$
   $$\langle (x_1 - x_2) - (p_1 - p_2), p_2 - p_1 \rangle \leq 0$$
   $$\langle x_1 - x_2, p_2 - p_1 \rangle + \|p_1 - p_2\|^2 \leq 0$$

3. **导出牢靠非扩张性 (FNE)**：
   $$\|p_1 - p_2\|^2 \leq \langle x_1 - x_2, p_1 - p_2 \rangle$$

4. **应用 Cauchy-Schwarz 导出 1-Lipschitz**：
   $$\|p_1 - p_2\|^2 \leq \|x_1 - x_2\| \cdot \|p_1 - p_2\|$$
   当 $p_1 \neq p_2$ 时，两边同除以 $\|p_1 - p_2\|$：
   $$\|p_1 - p_2\| \leq \|x_1 - x_2\|$$

即：$\|\text{proj}_C x_1 - \text{proj}_C x_2\| \le \|x_1 - x_2\|$。
