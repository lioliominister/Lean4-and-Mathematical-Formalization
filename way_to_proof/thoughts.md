最小化距离
在 Hilbert 空间 $H$ 中，点 $x$ 到闭凸集 $C$ 的投影 $p = \text{proj}_C x$ 为：$$p = \arg\min_{z \in C} f(z), \quad \text{其中 } f(z) = \frac{1}{2}\|z - x\|^2$$
最优解 $p$ 的一阶必要充分条件是梯度在所有可行方向上的分量非负：$$\langle \nabla f(p), y - p \rangle \geq 0, \quad \forall y \in C$$
$\nabla f(p) = p - x$
$$\langle p - x, y - p \rangle \geq 0 \implies \langle x - p, y - p \rangle \leq 0, \quad \forall y \in C \quad \text{(1)}$$
Pythagoras型恒等式
对于任意 $y \in C$：$$\|x - y\|^2 = \|(x - p) + (p - y)\|^2 = \|x - p\|^2 + \|p - y\|^2 + 2\langle x - p, p - y \rangle$$
$\langle x - p, y - p \rangle \leq 0$，所以：$$2\langle x - p, p - y \rangle = -2\langle x - p, y - p \rangle \geq 0$$
有 $$\|x - y\|^2 \geq \|x - p\|^2 + \|p - y\|^2$$
取两点 $x_1, x_2 \in H$，记它们的投影分别为 $p_1 = \text{proj}_C x_1$ 和 $p_2 = \text{proj}_C x_2$。
取 $y = p_2 \in C$：$\langle x_1 - p_1, p_2 - p_1 \rangle \leq 0 \quad$
取 $y = p_1 \in C$：$\langle x_2 - p_2, p_1 - p_2 \rangle \leq 0 \quad$
$$\langle p_2 - x_2, p_2 - p_1 \rangle \leq 0 \quad $$
$$\langle (x_1 - p_1) + (p_2 - x_2), p_2 - p_1 \rangle \leq 0$$
$$\langle (x_1 - x_2) - (p_1 - p_2), p_2 - p_1 \rangle \leq 0$$
$$\langle x_1 - x_2, p_2 - p_1 \rangle - \langle p_1 - p_2, p_2 - p_1 \rangle \leq 0$$
由于 $\|p_1 - p_2\|^2 = -\langle p_1 - p_2, p_2 - p_1 \rangle$
$$\|p_1 - p_2\|^2 \leq \langle x_1 - x_2, p_1 - p_2 \rangle \quad $$
应用 Cauchy-Schwarz
$$\|p_1 - p_2\|^2 \leq \langle x_1 - x_2, p_1 - p_2 \rangle \leq \|x_1 - x_2\| \cdot \|p_1 - p_2\|$$
若 $\|p_1 - p_2\| \neq 0$
$$\|p_1 - p_2\| \leq \|x_1 - x_2\|$$ $$/->$$ $$\|\text{proj}_C x_1 - \text{proj}_C x_2\| \leq \|x_1 - x_2\|$$
