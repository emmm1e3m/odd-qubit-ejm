# 任意奇数 n≥5 的显式可调 Elegant Joint Measurement

**作者：Tingyu Zhang**  
**日期：2026-10-30**

本报告给出所有奇数 $n\ge5$ 的统一构造。由同一个固定五变量布尔函数控制的相位族具有共同 Bloch 半径

$$
\boxed{r_n(t)=\frac{\sqrt3}{2^{n-1}}(1-\sin t),
\qquad t\in J=[-\pi/2,\pi/2].}
$$

它在 $t=0$ 逐态恢复已知的 $n$ 比特 EJM，保持全部局部正四面体方向，并精确覆盖

$$
\boxed{r_n(J)=[0,\sqrt3/2^{n-2}].}
$$

两个端点均包含；最大半径为已知点的两倍，零端点的所有单比特约化态完全混合。证明对任意奇数 $n\ge5$ 成立。五变量函数是统一构造中的固定代数工具。

完整背景及另一条直接 Fourier 证明见[中文论文](paper/main.pdf)；实际量子测量的形式化对应见[Lean 工程](lean/README.md)。

## 1. 统一构造

取 $n=2m+1\ge5$，计算基第一比特在最左，Pauli 矩阵采用 $Y=iXZ$ 的约定。定义两个非空位置集合

$$
\mathcal E=\{2,4,\ldots,n-3\},\qquad
\mathcal O=\{3,5,\ldots,n-2\}.
$$

它们各有 $m-1$ 个元素。所有 $\oplus$ 都表示模2相加。将 $n$ 位输入压缩为五个布尔特征：

$$
L_nz=\left(z_1,\ \bigoplus_{j\in\mathcal E}z_j,\
\bigoplus_{j\in\mathcal O}z_j,\ z_{n-1},z_n\right).
\tag{1}
$$

定义固定五位函数 $Q$。按第一位最高位的整数编码，其取值1的集合为

$$
\boxed{\mathcal Q=\{0,5,6,7,11,12,13,14,18,20,21,23,24,25,26,31\}.}
\tag{2}
$$

其余16个输入取值0。等价的布尔多项式为

$$
Q(a,b,c,d,e)=1\oplus a\oplus b\oplus c\oplus d\oplus e
\oplus de\oplus be\oplus bd\oplus ae\oplus abe.
\tag{3}
$$

普通乘法表示布尔与。定义实际相位支持

$$
\boxed{d_n(z)=
\begin{cases}
0,&z=0^n,\\
Q(L_nz),&z\ne0^n.
\end{cases}}
\tag{4}
$$

这里只单独去掉**物理全零串**，不能把所有满足 $L_nz=00000$ 的输入删去。由于 $L_n$ 满秩5、$Q$ 有16个1且 $Q(0)=1$，支持大小为 $2^{n-1}-1$。

令 $e_q$ 为基本对称多项式，$|z|$ 为串的 Hamming 重量。已知 EJM 的相位为

$$
f_0(z)=\sum_{q=2}^{n}(-1)^q e_q(z)\pmod4
=\begin{cases}0,&z=0^n,\\ |z|-1\pmod4,&z\ne0^n.\end{cases}
$$

定义

$$
f_t(z)=f_0(z)+\frac{2t}{\pi}d_n(z),\qquad
D_t|z\rangle=i^{f_0(z)}e^{itd_n(z)}|z\rangle.
\tag{5}
$$

采用相位正规形的门序

$$
C_n=S(n)H_n,\qquad
S(n)=\mathrm{CNOT}_{2\to1}\cdots\mathrm{CNOT}_{n\to n-1},
$$

其中 $H_n$ 是末位 Hadamard 门，最右门先作用。全部测量态可直接写成

$$
\boxed{|\psi_{e,s}(t)\rangle
=C_nD_tH^{\otimes n}|e_1\cdots e_{n-1}s\rangle,\quad
(e,s)\in\{0,1\}^{n-1}\times\{0,1\}.}
\tag{6}
$$

式(1)–(6)是统一显式公式，不随 $n$ 重新搜索，也不在每个 $t$ 求解方程。参数只有实数 $t$，所有表达式在全实轴解析。

**主定理。** 对每个奇数 $n\ge5$，式(6)给出 $2^n$ 个正交归一态；每个单比特的局部态具有固定正四面体几何，全部比特及结果共享半径 $r_n(t)$。每个局部顶点在 $r>0$ 时出现 $2^{n-2}$ 次；$t=0$ 与已知 $n$ 比特 EJM 逐个投影相同。

## 2. 正交性与 Pauli 轨道

因为式(6)是酉矩阵 $C_nD_tH^{\otimes n}$ 的所有列，正交归一性立即成立。它也可表示为同一种子的 Pauli 轨道。令

$$
g_{e,s}=\left[\prod_{h=1}^{n-1}(Z_hZ_{h+1})^{e_h}\right](X^{\otimes n})^s.
$$

CNOT链把输入位 $y$ 送到 $x_j=y_j\oplus\cdots\oplus y_n$，从而

$$
C_n^\dagger(Z_hZ_{h+1})C_n=Z_h,\qquad
C_n^\dagger X^{\otimes n}C_n=Z_n.
\tag{7}
$$

故 $\psi_{e,s}=g_{e,s}\psi_{0,0}$。$n$ 个生成元对易且独立，给出恰好 $2^n$ 个群元素。下面只需计算种子的 $3n$ 个 Pauli 期望。

## 3. 全 n 证明：把背景项化为固定有限恒等式

本节对任意奇数 $n\ge5$ 的背景项作完整归约，余下条件为16个各含32项的整数恒等式。固定证书由[精确程序](paper/verify_certificate.py)复算；[论文](paper/main.pdf)还给出一条直接布尔 Fourier 消去证明。

### 3.1 乘积相位背景与零点修正

置 $u=e^{it}$，定义未归一化背景向量

$$
|\chi(t)\rangle=\sum_z i^{|z|}u^{Q(L_nz)}|z\rangle.
$$

利用 $Q(0)=1$ 与式(4)，种子可以精确写为

$$
|\psi(t)\rangle
=\frac{-i}{\sqrt{2^n}}C_n\big[|\chi(t)\rangle+(i-u)|0^n\rangle\big].
\tag{8}
$$

对非零串，这还原 $i^{|z|-1}u^{d_n(z)}$；对零串，括号中为 $u+i-u=i$，外乘 $-i$ 后相位因子为1。

为统一符号，定义 $\widetilde P_{j\alpha}=\sigma_{j\alpha}$，仅 $\widetilde P_{ny}=-Y_n$。写其拉回为

$$
R=C_n^\dagger\widetilde P_{j\alpha}C_n=i^k X^aZ^b,
\qquad h=a\oplus b,\qquad \Gamma=i^{k-|a|}.
$$

$a,b,h$ 是 $n$ 位掩码，$X^aZ^b$ 的次序固定为先 $Z^b$ 后 $X^a$。拉回表如下，$e_j$ 表示第 $j$ 个单位位：

| 观测量 | 翻转掩码 $a$ | $Z$掩码 $b$ | $i^k$ | $\Gamma$ |
| --- | --- | --- | --- | --- |
| $X_1$ | $e_1$ | 0 | 1 | $-i$ |
| $X_j,\ 2\le j<n$ | $e_{j-1}+e_j$ | 0 | 1 | $-1$ |
| $X_n$ | $e_{n-1}$ | $e_n$ | 1 | $-i$ |
| $Y_1$ | $e_1+e_n$ | $\sum_{\ell=1}^{n-1}e_\ell$ | $i$ | $-i$ |
| $Y_j,\ 2\le j<n$ | $e_{j-1}+e_j+e_n$ | $\sum_{\ell=j}^{n-1}e_\ell$ | $i$ | $-1$ |
| $-Y_n$ | $e_{n-1}+e_n$ | $e_n$ | $i$ | $-i$ |
| $Z_j,\ 1\le j\le n$ | $e_n$ | $\sum_{\ell=j}^{n-1}e_\ell$ | 1 | $-i$ |

表内掩码的加法均为模2。它来自 $S^\dagger X_1S=X_1$、$S^\dagger X_jS=X_{j-1}X_j$、$S^\dagger Z_jS=Z_j\cdots Z_n$，再在末位作Hadamard共轭。

### 3.2 字符消去与任意长度分类

背景期望为

$$
\langle\chi|R|\chi\rangle
=\Gamma\sum_z(-1)^{h\cdot z}
u^{Q(L_nz)-Q(L_nz\oplus L_na)}.
\tag{9}
$$

如果 $h$ 不属于 $L_n$ 的行空间，则它在某个核方向 $w\in\ker L_n$ 上取非零内积。配对 $z$ 与 $z\oplus w$，指数相同而符号相反，式(9)立即为0。

若 $h=L_n^{\mathsf T}H$，令 $A=L_na$，每个五位特征有 $2^{n-5}$ 个原像，故

$$
\langle\chi|R|\chi\rangle
=\Gamma\,2^{n-5}W_{A,H}(u),\qquad
W_{A,H}(u)=\sum_{v\in\mathbb F_2^5}(-1)^{H\cdot v}
u^{Q(v)-Q(v\oplus A)}.
\tag{10}
$$

行空间成员的判定极简单：掩码在 $\mathcal E$ 上必须全0或全1，在 $\mathcal O$ 上也必须全0或全1；第1、$n-1$、$n$ 位不受限制。由上一张拉回表，所有可能情况如下：

| 比特数 | 未被核字符配对直接消去的物理观测量 |
| --- | --- |
| $n=5$ | 全部15个；此时 $L_5$ 是恒等映射 |
| $n=7$ | $X_1,Y_1,Z_1,Z_2,Z_{n-1},X_n,-Y_n,Z_n$，另有 $Y_4$ |
| 任意奇数 $n\ge9$ | 只有 $X_1,Y_1,Z_1,Z_2,Z_{n-1},X_n,-Y_n,Z_n$ |

这是按集合形状作的全 $n$ 分类。对于 $X_j$ 内部项，$h=\{j-1,j\}$，当两块各至少两个元素时必有块被部分选中。对于 $Z_j$，$h=\{j,\ldots,n\}$，只有 $j=1,2,n-1,n$ 能把两块分别全选或全不选。对于 $Y_j$ 内部项，

$$
h=\{j-1\}\cup\{j+1,\ldots,n\}.
$$

对 $n\ge7$，当 $j=2$ 时偶块缺少2但含4；当 $j=3$ 时奇块缺少3但含5，都不是行空间成员。当 $j=4$ 时奇块全选、偶块缺少2和4，只有 $n=7$ 的偶块恰为空选；$n\ge9$ 还选中6，仍是非空真子集。当 $j\ge5$ 时，$h$ 含内部位置 $j-1$，却遗漏同一奇偶块最前的2或3，同样不能属于行空间。因此仅 $n=7,j=4$ 是额外情形；$n=5$ 已单独处理，没有随着 $n$ 增大而遗漏的新情况。

### 3.3 固定16项整数证书

式(10)的指数仅可能为 $-1,0,1$。定义

$$
N_s(A,H)=\sum_{\substack{v\in\mathbb F_2^5\\Q(v)-Q(v\oplus A)=s}}
(-1)^{H\cdot v}.
$$

下表给出覆盖上述全 $n$ 分类的全部有限检查；$A,H$ 用五位十进制编码。每行均有 $(N_{-1},N_0,N_1)=(0,0,0)$。

| 五位标签 | $A$ | $H$ | $(N_{-1},N_0,N_1)$ |
| --- | ---: | ---: | --- |
| $X_1$ | 16 | 16 | (0,0,0) |
| $Y_1$ | 17 | 15 | (0,0,0) |
| $Z_1$ | 1 | 31 | (0,0,0) |
| $X_2$ | 24 | 24 | (0,0,0) |
| $Y_2$ | 25 | 23 | (0,0,0) |
| $Z_2$ | 1 | 15 | (0,0,0) |
| $X_3$ | 12 | 12 | (0,0,0) |
| $Y_3$ | 13 | 11 | (0,0,0) |
| $Z_3$ | 1 | 7 | (0,0,0) |
| $X_4$ | 6 | 6 | (0,0,0) |
| $Y_4$ | 7 | 5 | (0,0,0) |
| $Z_4$ | 1 | 3 | (0,0,0) |
| $X_5$ | 2 | 3 | (0,0,0) |
| $-Y_5$ | 3 | 2 | (0,0,0) |
| $Z_5$ | 1 | 1 | (0,0,0) |
| $n=7$额外 $Y_4$ | 13 | 7 | (0,0,0) |

例如第一行按 $-1,0,1$ 三类分别有12、8、12个输入，带字符符号后均恰好抵消。每行都能由式(2)在32个输入上直接核查；[certificate.json](paper/certificate.json)给出完整计数。由式(9)–(10)，对所有奇数 $n\ge5$ 和所有实 $t$，

$$
\boxed{\langle\chi(t)|C_n^\dagger\widetilde P_{j\alpha}C_n|\chi(t)\rangle=0.}
\tag{11}
$$

证明中有限检查的对象是固定五位函数；任意 $n$ 的覆盖来自行空间分类，未将有限 $n$ 枚举外推成定理。

## 4. 零点交叉项给出统一半径律

所有拉回的翻转掩码 $a\ne0$，因此 $\langle0|R|0\rangle=0$。又有

$$
\langle\chi|R|0\rangle=\Gamma u^{-Q(L_na)}.
$$

由式(8)、式(11)，

$$
2^n\langle\widetilde P_{j\alpha}\rangle
=2\operatorname{Re}\!\left[\Gamma u^{-Q(L_na)}(i-u)\right].
\tag{12}
$$

拉回表中的两类恰满足

$$
\begin{array}{c|c|c}
\Gamma&L_na\text{ 的可能五位整数}&Q(L_na)\\ \hline
-i&1,2,3,16,17&0\\
-1&6,7,12,13,24,25&1
\end{array}
\tag{13}
$$

这也是由相邻位置的奇偶性直接得到的任意 $n$ 分类。第一类的实部为
$\operatorname{Re}[-i(i-u)]=1-\sin t$；第二类为
$\operatorname{Re}[-u^{-1}(i-u)]=1-\sin t$。

所以全部 $3n$ 个带统一符号的期望恒等于

$$
\langle\widetilde P_{j\alpha}\rangle
=c_n(t):=\frac{1-\sin t}{2^{\,n-1}}.
$$

换回标准 Pauli 符号，

$$
\boxed{\mathbf m_j(t)=c_n(t)(1,1,1)\quad(j<n),\qquad
\mathbf m_n(t)=c_n(t)(1,-1,1).}
\tag{14}
$$

该恒等式在所有实 $t$ 成立。

## 5. 全测量几何、已知点与精确范围

令 $e_0=e_n=0$，$q_j=e_{j-1}\oplus e_j$，并置 $\epsilon_j=1$ 当 $j<n$、$\epsilon_n=-1$。由群元素的局部 Pauli 共轭，

$$
\mathbf m_{j,e,s}(t)=c_n(t)
\big((-1)^{q_j},\epsilon_j(-1)^{q_j+s},(-1)^s\big).
$$

故固定顶点和标号为

$$
\mathbf v_{j,2q+s}=\frac1{\sqrt3}
\big((-1)^q,\epsilon_j(-1)^{q+s},(-1)^s\big),\qquad
a_j(e,s)=2q_j+s.
\tag{15}
$$

不同标号恰改变两个坐标符号，内积为 $-1/3$。固定 $j$ 后 $q_j$ 是 $n-1$ 个边标签的非零线性函数，指定 $(q_j,s)$ 恰有 $2^{n-2}$ 个原像。

局部偏迹和期望由 Pauli 正交基连接：
$\operatorname{Tr}(\rho_j\sigma_\alpha)=\langle\sigma_{j\alpha}\rangle$。
因此全部约化态严格为

$$
\boxed{\rho_{j,e,s}(t)=\tfrac12\left[I+r_n(t)
\mathbf v_{j,a_j(e,s)}\cdot\boldsymbol\sigma\right].}
\tag{16}
$$

在 $t=\pi/2$ 时它们全为 $I/2$，是四面体连续收缩端点。

在 $t=0$，$D_0=D_{f_0}$，种子、门序和群标签都与已知 $n$ 比特 EJM 相同，故逐个投影相等，无须额外局域变换或重标号。

在 $J=[-\pi/2,\pi/2]$，$\sin t$ 连续严格递增，所以

$$
r_n(-\pi/2)=\frac{\sqrt3}{2^{n-2}},\quad
r_n(0)=\frac{\sqrt3}{2^{n-1}},\quad r_n(\pi/2)=0.
$$

精确像集就是两端包含的 $[0,\sqrt3/2^{n-2}]$。半径平方在已知点的导数为

$$
(r_n^2)'(0)=-\frac6{2^{2n-2}}\ne0.
$$

因此该参数变化真实改变纠缠谱，不是局域旋转或整体相位。

所有结果及比特的纯度和任意 $1|(n-1)$ 划分纠缠熵为

$$
\operatorname{Tr}\rho_j^2=\frac12+\frac{3(1-\sin t)^2}{2^{2n-1}},
\qquad
S_{1|(n-1)}(t)=h_2\!\left(\frac12+
\frac{\sqrt3(1-\sin t)}{2^n}\right).
\tag{17}
$$

其中 $h_2(p)=-p\log_2p-(1-p)\log_2(1-p)$。随 $t$ 在 $J$ 上增加，半径和纯度下降，该划分的纠缠熵增加到1 bit。零端点的所有单比特边缘完全混合。

## 6. 适用范围与已有工作

主定理覆盖每个奇数 $n\ge5$。两组非空的内部位置使 $L_n$ 满秩，并为背景消去提供所需的独立坐标。这是本构造对比特数的结构条件。

Pauwels 与 Gisin 在 *Tunable Families of Multiqubit Elegant Joint Measurements* 中给出任意比特数的已知 EJM 点，以及偶数比特的特定坐标零支持余弦族，并保留奇数 $n\ge5$ 的显式可调族问题。本文通过同一个五变量函数及物理全零串修正，给出这些奇数比特数的统一参数域、完整测量态、共同半径律和任意 $n$ 的证明。[原文 arXiv:2607.16020v1](https://arxiv.org/abs/2607.16020v1)

上述文献的奇数障碍针对其特定坐标零支持及相应余弦机制。本文使用内部块的奇偶校验，采用不同的支持结构。Ding 等的奇数构造在一个比特上具有中心对称的局部结果集合；正半径时，对径点的内积为 $-r^2$，而单个正四面体的不同顶点内积为 $-r^2/3$，所以两种几何不相同。He 等的多比特推广则限定于偶数比特。[Ding 等](https://arxiv.org/abs/2503.08993v1)、[He 等](https://arxiv.org/abs/2602.04173v1)

本文的半径区间是所构造路径的精确像集，未求解全部 EJM 的全局最优半径。完整文献背景及书目信息见[论文](paper/main.pdf)与[参考文献文件](paper/references.bib)。

## 7. 精确复算与 Lean 形式化

在仓库根目录使用 Python 3.10+ 运行：

```text
python paper/verify_certificate.py
python paper/verify_measurement.py
```

两个程序只使用标准库。前者生成第3.3节的十六项整数证书，输出 [certificate.json](paper/certificate.json)。后者从原基本对称相位及逐门 Hadamard、CNOT 作用出发，以高斯整数精确核对 $n=5,7,9,11$ 的归一化、全部局部 Pauli 期望、背景零期望及局部顶点计数，输出 [exact_results.json](paper/exact_results.json)。这些有限规模检查用于核对符号、门序与归一化；第3节的分类和下述 Lean 证明承担任意 $n$ 的结论。

Lean 工程固定为 Lean 4.35.0 和 mathlib v4.35.0。安装 elan 后，在仓库根目录执行：

```text
cd lean
lake exe cache get
lake build
lake env lean Audit.lean
```

主入口 [Main.lean](lean/OddEJM/Main.lean) 中的 `OddEJM.odd_ejm_family` 仅假设 $5\le n$ 和 `Odd n`。形式化从实际复振幅、逐门电路及偏迹有限和开始，覆盖：

- 全部测量列正交归一，秩一投影之和为恒等矩阵；
- 全部单比特偏迹的固定正四面体公式及每个标签的 $2^{n-2}$ 重数；
- 半径连续性、在 $J$ 上严格递减及精确像集；
- $t=0$ 逐列恢复原基本对称相位构造。

[Main.lean](lean/OddEJM/Main.lean) 还证明实际偏迹的纯度；[Consequences.lean](lean/OddEJM/Consequences.lean) 给出非零半径下实际局部矩阵的重数和约化谱特征根。式(17)的基 2 对数纠缠熵表达式保留为由约化谱得到的解析推论，未纳入 Lean 工程。

[Audit.lean](lean/Audit.lean) 输出定理类型及其传递公理依赖，保存的结果见 [axioms.txt](lean/axioms.txt)。证明未使用 `sorry`、自定义公理或 `native_decide`，标准公理依赖为 `propext`、`Classical.choice`、`Quot.sound`。模块与论文步骤的对应及详细构建说明见 [Lean README](lean/README.md)。
