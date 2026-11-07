"""Reproduce the constructed Giffen diagram for Kreps I, Problem 4.3 (p. 78).

Requires matplotlib (tested with 3.11.2). Run this script from any directory.
The exact utility, budgets, and unique maximizers are proved in GiffenExample.lean.
The numerical witness is ours; the source asks for a diagram without specifying one.
"""

from fractions import Fraction
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt


def utility(x, y):
    """The two affine pieces from the Lean definition GiffenUtility."""
    return min(x + 2 * y, 13 * x + 6 * y - 48)


def indifference_height(x, level):
    """Solve min(x + 2*y, 13*x + 6*y - 48) = level for y."""
    return max((level - x) / 2, (level + 48 - 13 * x) / 6)


def main():
    # These exact checks keep plotted labels aligned with the verified example.
    assert utility(Fraction(1), Fraction(9)) == 19
    assert utility(Fraction(2), Fraction(6)) == 14
    assert 1 + 9 == 10 and 2 * 2 + 6 == 10
    assert indifference_height(Fraction(1), Fraction(19)) == 9
    assert indifference_height(Fraction(2), Fraction(14)) == 6

    plt.rcParams.update({
        "font.family": "DejaVu Sans",
        "font.size": 11,
        "axes.spines.top": False,
        "axes.spines.right": False,
        "svg.fonttype": "none",
        "svg.hashsalt": "kreps-foundations-giffen-example",
    })
    figure, axes = plt.subplots(1, 2, figsize=(12.5, 7.4), sharex=True, sharey=True)
    figure.subplots_adjust(left=0.07, right=0.98, bottom=0.18, top=0.80, wspace=0.20)
    figure.suptitle("A Giffen good with unique demand", fontsize=20, y=0.97)
    figure.text(
        0.5, 0.90,
        r"$u(x_1,x_2)=\min\{x_1+2x_2,\;13x_1+6x_2-48\}$",
        ha="center", fontsize=16,
    )

    grid = [10.2 * index / 2040 for index in range(2041)]
    cases = [
        (1, (1, 9), 19, "#2761a5", "Before: prices (1, 1)"),
        (2, (2, 6), 14, "#ba5425", "After: prices (2, 1)"),
    ]
    for axis, (price, choice, optimum, color, title) in zip(axes, cases):
        affordable_x = [x for x in grid if x <= 10 / price]
        budget_y = [10 - price * x for x in affordable_x]
        axis.fill_between(affordable_x, budget_y, color=color, alpha=0.10)
        axis.plot(affordable_x, budget_y, color=color, lw=2.4)

        for level in (9, 14, 19):
            heights = [indifference_height(x, level) for x in grid]
            heights = [y if 0 <= y <= 11 else float("nan") for y in heights]
            active = level == optimum
            axis.plot(
                grid, heights, color="#27764f" if active else "#8eb99c",
                lw=2.2 if active else 1.3, linestyle="-" if active else "--",
            )
            axis.text(
                7.8, indifference_height(7.8, level) + 0.20, f"u = {level}",
                color="#27764f" if active else "#588368", fontsize=10,
            )

        x_star, y_star = choice
        axis.plot([x_star, x_star], [0, y_star], ":", color="#555555", lw=1)
        axis.plot([0, x_star], [y_star, y_star], ":", color="#555555", lw=1)
        axis.scatter([x_star], [y_star], s=65, color="#172b3c", edgecolor="white", zorder=5)
        axis.annotate(
            f"Unique optimum ({x_star}, {y_star})",
            xy=choice, xytext=(3.5, 9.0 if price == 1 else 6.8),
            arrowprops={"arrowstyle": "->", "color": "#172b3c"},
            color="#172b3c", fontsize=11,
            bbox={"facecolor": "white", "edgecolor": "none", "alpha": 0.9, "pad": 2},
        )
        axis.text(0.97, 0.95, f"Income = 10\nBudget: {price}x₁ + x₂ ≤ 10",
                  ha="right", va="top", transform=axis.transAxes, color=color)
        axis.set_title(title, fontsize=14, pad=12)
        axis.set_xlim(0, 10.2)
        axis.set_ylim(0, 11)
        axis.set_aspect("equal", adjustable="box")
        axis.set_xticks([0, 1, 2, 4, 6, 8, 10])
        axis.set_yticks([0, 2, 4, 6, 8, 10])
        axis.set_xlabel("Good 1")
        axis.set_ylabel("Good 2")
        axis.tick_params(length=3, color="#888888")

    figure.text(
        0.5, 0.095,
        "Income stays at 10. The unique quantity of good 1 rises from 1 to 2 "
        "as its price rises from 1 to 2.",
        ha="center", fontsize=12,
    )
    figure.text(
        0.5, 0.045,
        "Constructed witness for Kreps I, Problem 4.3. "
        "Global optimality and uniqueness are proved in GiffenExample.lean.",
        ha="center", fontsize=10, color="#555555",
    )

    output = Path(__file__).resolve().parents[1] / "docs" / "assets"
    output.mkdir(parents=True, exist_ok=True)
    svg = output / "giffen-example.svg"
    figure.savefig(svg, metadata={"Date": None})
    # Matplotlib emits trailing spaces in path data; keep the tracked SVG clean.
    svg.write_text("\n".join(line.rstrip() for line in svg.read_text(
        encoding="utf-8").splitlines()) + "\n", encoding="utf-8", newline="\n")
    figure.savefig(output / "giffen-example.png", dpi=180)
    plt.close(figure)
    print(output / "giffen-example.svg")
    print(output / "giffen-example.png")


if __name__ == "__main__":
    main()
