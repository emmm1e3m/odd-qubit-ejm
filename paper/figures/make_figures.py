"""用已审闭式公式绘制新版 PRA 论文的三张科学图。"""

from pathlib import Path
import json
import sys

ROOT = Path(__file__).resolve().parent
LOCAL_DEPS = ROOT / ".python-deps"
if LOCAL_DEPS.exists():
    sys.path.insert(0, str(LOCAL_DEPS))

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib import patheffects
from matplotlib.patches import FancyArrowPatch
import numpy as np


plt.rcParams.update({
    "font.family": "serif",
    "font.serif": ["DejaVu Serif"],
    "mathtext.fontset": "dejavuserif",
    "font.size": 9,
    "axes.labelsize": 10,
    "axes.titlesize": 10,
    "xtick.labelsize": 9,
    "ytick.labelsize": 9,
    "legend.fontsize": 8,
    "axes.spines.top": False,
    "axes.spines.right": False,
    "axes.linewidth": 0.65,
    "lines.linewidth": 1.6,
    "xtick.direction": "out",
    "ytick.direction": "out",
    "xtick.major.width": 0.65,
    "ytick.major.width": 0.65,
    "savefig.dpi": 240,
    "pdf.fonttype": 42,
    "ps.fonttype": 42,
})

INK = "#202a35"
BLUE = "#175a8c"
GRAY = "#747474"


def save(fig, name):
    fig.savefig(ROOT / f"{name}.pdf", bbox_inches="tight", pad_inches=0.035,
                metadata={"Title": name, "Creator": "Matplotlib; closed-form EJM data"})
    fig.savefig(ROOT / f"{name}.png", bbox_inches="tight", pad_inches=0.035)
    plt.close(fig)


def panel(ax, text):
    ax.text(-0.12, 1.035, text, transform=ax.transAxes, weight="bold",
            ha="left", va="bottom", color=INK, fontsize=10)


def figure_unified():
    fig = plt.figure(figsize=(7.0, 2.45))
    gs = fig.add_gridspec(1, 2, width_ratios=(1.1, 1), wspace=0.24,
                          left=0.035, right=0.985, bottom=0.20, top=0.89)
    scheme = fig.add_subplot(gs[0, 0])
    ax = fig.add_subplot(gs[0, 1])
    scheme.set_axis_off()
    scheme.set_xlim(0, 1)
    scheme.set_ylim(0, 1)
    scheme.text(0.0, 1.055, "(a)", weight="bold", fontsize=10)
    # 用括号归组四个特征；输入、箭头与核函数共用组中心线。
    flow_y = 0.585
    scheme.text(0.10, 0.80, r"$n\geq 5$", ha="center", va="center")
    scheme.text(0.10, flow_y, r"$\mathbf{z}$", fontsize=16,
                ha="center", va="center")
    scheme.annotate("", xy=(0.315, flow_y), xytext=(0.18, flow_y),
                    arrowprops={"arrowstyle": "->", "lw": 0.9, "color": INK})
    definitions = [
        r"$x=z_1\oplus z_{n-1}$",
        r"$b=\bigoplus_{j\in E_n} z_j$",
        r"$c=\bigoplus_{j\in O_n} z_j$",
        r"$s=z_1\oplus z_n$",
    ]
    for y, label in zip((0.93, 0.72, 0.48, 0.25), definitions):
        scheme.text(0.37, y, label, fontsize=9.1, va="center")
    for outer, inner in ((0.33, 0.35), (0.69, 0.67)):
        scheme.plot([inner, outer, outer, inner], [1.00, 1.00, 0.17, 0.17],
                    color=INK, lw=0.75, solid_capstyle="butt")
    scheme.annotate("", xy=(0.87, flow_y), xytext=(0.705, flow_y),
                    arrowprops={"arrowstyle": "->", "lw": 0.9, "color": INK})
    scheme.text(0.92, flow_y, r"$F$", fontsize=16, va="center", ha="center")
    scheme.text(0.51, 0.035, r"$q_n(\mathbf{z})=F(x,b,c,s)$",
                ha="center", va="center", fontsize=10)
    scheme.text(0.51, -0.16, r"$d_n=q_n-\delta_{\mathbf{z},0}$",
                ha="center", va="center", fontsize=10)
    t = np.linspace(-np.pi/2, np.pi/2, 601)
    ax.plot(t, 1-np.sin(t), color=BLUE)
    ax.scatter([-np.pi/2, 0, np.pi/2], [2, 1, 0], s=22, color=BLUE, zorder=4)
    ax.axvline(0, color="0.78", lw=0.65, ls=(0, (3, 3)), zorder=0)
    ax.axhline(1, color="0.78", lw=0.65, ls=(0, (3, 3)), zorder=0)
    ax.annotate("base point", xy=(0, 1), xytext=(0.34, 1.22), fontsize=8,
                arrowprops={"arrowstyle": "-", "color": GRAY, "lw": 0.6})
    ax.text(-0.80, 1.78, r"$1-\sin t$", fontsize=10, color=BLUE)
    ax.set(xlim=(-1.68, 1.68), ylim=(-0.09, 2.12), xlabel=r"$t$", ylabel=r"$r_n/r_E(n)$")
    ax.set_xticks([-np.pi/2, 0, np.pi/2], [r"$-\pi/2$", r"$0$", r"$\pi/2$"])
    ax.set_yticks([0, 1, 2])
    panel(ax, "(b)")
    save(fig, "fig1_unified")


def figure_embedding():
    fig = plt.figure(figsize=(7.0, 2.85))
    gs = fig.add_gridspec(1, 2, width_ratios=(1.9, 1), wspace=0.48,
                         left=0.09, right=0.975, bottom=0.23, top=0.89)
    ax = fig.add_subplot(gs[0, 0])
    inset = fig.add_subplot(gs[0, 1])
    # 横纵轴分别以 pi/2 为单位；Omega 是由闭式不等式确定的闭五边形。
    u = np.linspace(-1, 1, 401)
    v = np.linspace(-1, 1, 401)
    uu, vv = np.meshgrid(u, v)
    val = np.ma.masked_where(vv > 1-np.abs(uu)+1e-12,
                            np.cos(np.pi*uu/2)-np.sin(np.pi*vv/2))
    # contourf 的填充多边形在 PDF 中保持矢量输出。
    filled = ax.contourf(uu, vv, val, levels=np.linspace(0, 2, 33), cmap="viridis",
                         vmin=0, vmax=2, antialiased=False)
    # 同色细边覆盖 PDF 查看器在相邻矢量多边形之间产生的抗锯齿白缝。
    filled.set_edgecolor("face")
    filled.set_linewidth(0.15)
    ax.plot([-1, -1, 0, 1, 1, -1], [-1, 0, 1, 0, -1, -1], color=INK, lw=0.8)
    halo = [patheffects.Stroke(linewidth=3.3, foreground="white"), patheffects.Normal()]
    ax.plot([-1, 1], [0, 0], color=INK, ls=(0, (4, 2)), lw=1.4,
            path_effects=halo, label=r"$\beta=0$: even-qubit family")
    ax.plot([0, 0], [-1, 1], color=INK, lw=1.4,
            path_effects=halo, label=r"$\alpha=0$: unified family")
    ax.plot(0, 0, marker="o", markersize=4.4, mfc="white", mec=INK, mew=0.8, zorder=6)
    ax.set(xlim=(-1.05, 1.05), ylim=(-1.06, 1.08), xlabel=r"$\alpha/(\pi/2)$", ylabel=r"$\beta/(\pi/2)$")
    ax.set_xticks([-1, 0, 1])
    ax.set_yticks([-1, 0, 1])
    ax.set_title(r"Even $n\geq8$", pad=7)
    panel(ax, "(a)")
    cax = ax.inset_axes([1.035, 0.0, 0.04, 1.0])
    cb = fig.colorbar(filled, cax=cax, ticks=[0, 1, 2])
    cb.ax.tick_params(labelsize=8)
    cb.outline.set_linewidth(0.6)
    cb.set_label(r"$r_n/r_E(n)$", fontsize=9, labelpad=4)
    ax.legend(loc="upper center", bbox_to_anchor=(0.51, -0.29), ncol=1,
              frameon=False, borderaxespad=0, handlelength=2.7, labelspacing=0.35)
    inset.plot([-1, 1], [0, 0], color=INK, lw=1.4, ls=(0, (4, 2)))
    inset.plot([0, 0], [-1, 1], color=INK, lw=1.4)
    inset.plot(0, 0, marker="o", markersize=4.4, mfc="white", mec=INK, mew=0.8)
    inset.set(xlim=(-1.15, 1.15), ylim=(-1.15, 1.15))
    inset.set_xticks([])
    inset.set_yticks([])
    for spine in inset.spines.values():
        spine.set_visible(False)
    inset.text(1.05, -0.16, r"$\alpha$", ha="left", va="top")
    inset.text(0.11, 1.02, r"$\beta$", ha="left", va="bottom")
    inset.set_title(r"$n=6$", pad=7)
    panel(inset, "(b)")
    inset.text(0.5, -0.19, "Four-color model", ha="center", transform=inset.transAxes, fontsize=9)
    inset.text(0.5, -0.34, "Local solution set (schematic)", ha="center", transform=inset.transAxes, fontsize=8)
    save(fig, "fig2_embedding")


def curved_family(b):
    s, c = np.sin(b), np.cos(b)
    aa, bb, cc = c*(1+2*s), 2*c+s+1, 2*s*c
    discr = bb*bb-4*aa*cc
    z = 2*cc/(bb+np.sqrt(discr))
    q = 2*np.arctan(z)
    radius_ratio = np.cos(b-q)+np.sin(q)
    return q, radius_ratio, discr


def figure_curved():
    fig, ax = plt.subplots(figsize=(3.45, 2.62))
    fig.subplots_adjust(left=0.20, right=0.97, bottom=0.22, top=0.90)
    b = np.linspace(0, np.pi/4, 801)
    q, r, discr = curved_family(b)
    ax.plot(b, r, color=BLUE, label="Curved phase path")
    ax.axhline(1, color=GRAY, ls=(0, (4, 3)), lw=1.1,
               label="Real phase-line bound")
    ax.scatter([0, np.pi/4], [1, 1+1/np.sqrt(2)], s=21, color=BLUE, zorder=4)
    ax.text(0.035, 0.947, "base point", fontsize=8, ha="left", va="center")
    ax.annotate(r"$1+1/\sqrt{2}$", xy=(np.pi/4, 1+1/np.sqrt(2)),
                xytext=(0.46, 1.42), fontsize=9,
                arrowprops={"arrowstyle": "-", "color": GRAY, "lw": 0.6})
    ax.set(xlim=(-0.025, np.pi/4+0.028), ylim=(0.90, 1.84), xlabel=r"$b$", ylabel=r"$r_4/r_E(4)$")
    ax.set_xticks([0, np.pi/8, np.pi/4], [r"$0$", r"$\pi/8$", r"$\pi/4$"])
    ax.set_yticks([1, 1.25, 1.5, 1.75], [r"$1$", r"$1.25$", r"$1.5$", r"$1.75$"])
    ax.legend(loc="upper left", frameon=False, fontsize=7.8, borderaxespad=0.35)
    save(fig, "fig3_curved")
    # 这组数值只检查图的生成公式与采样，连续结论依赖已审解析证明。
    h = np.cos(b)-2*np.sin(q)*np.cos(b)+2*np.sin(2*b)
    metrics = {
        "sample_count": int(len(b)),
        "b_interval": [0.0, float(np.pi/4)],
        "q_endpoints": [float(q[0]), float(q[-1])],
        "radius_ratio_endpoints": [float(r[0]), float(r[-1])],
        "endpoint_target": float(1+1/np.sqrt(2)),
        "min_discriminant_sampled": float(np.min(discr)),
        "minimum_radius_increment": float(np.min(np.diff(r))),
        "max_H_minus_T_sampled": float(np.max(np.abs(h-r))),
    }
    assert abs(r[0]-1) < 1e-14
    assert abs(r[-1]-(1+1/np.sqrt(2))) < 1e-14
    assert abs(q[-1]-np.pi/4) < 1e-14
    assert np.min(discr) > 0
    assert np.min(np.diff(r)) > 0
    assert np.max(np.abs(h-r)) < 1e-13
    (ROOT / "figure_checks.json").write_text(json.dumps(metrics, indent=2), encoding="utf-8")


if __name__ == "__main__":
    figure_unified()
    figure_embedding()
    figure_curved()
    print("PASS: three PDF/PNG pairs generated; curve formula and endpoints checked.")


