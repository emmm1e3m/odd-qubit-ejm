"""从 TikZ 源文件生成可印刷 PDF，并生成 200 dpi 审阅图。"""

from pathlib import Path
import subprocess

import pymupdf


def main() -> None:
    # 始终在脚本所在目录构建，避免污染正式稿目录。
    target = Path(__file__).resolve().parent
    subprocess.run(
        [
            "pdflatex",
            "-interaction=nonstopmode",
            "-halt-on-error",
            "-jobname=fig4_clifford",
            "fig4_clifford_source.tex",
        ],
        cwd=target,
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    with pymupdf.open(target / "fig4_clifford.pdf") as document:
        page = document[0]
        page.get_pixmap(dpi=200).save(target / "fig4_clifford.png")
        print(f"PDF: {page.rect.width / 72:.3f} x {page.rect.height / 72:.3f} inches")
        print("Wrote fig4_clifford.pdf and fig4_clifford.png")


if __name__ == "__main__":
    main()
