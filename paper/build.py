"""使用本机 TeX Live 编译双语 PRA 初稿，辅助文件写入 .build。"""
from pathlib import Path
import argparse
import os
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent
parser = argparse.ArgumentParser()
parser.add_argument("language", nargs="?", choices=("en", "zh", "both"), default="both")
args = parser.parse_args()
build = ROOT / ".build"
build.mkdir(exist_ok=True)
environment = os.environ.copy()
environment["BIBINPUTS"] = str(build) + os.pathsep + str(ROOT) + os.pathsep + environment.get("BIBINPUTS", "")

for language in (("en", "zh") if args.language == "both" else (args.language,)):
    stem, engine = ("main", "pdflatex") if language == "en" else ("main-zh", "xelatex")
    commands = [
        [engine, "-interaction=nonstopmode", "-halt-on-error", "-file-line-error", "-output-directory=.build", stem + ".tex"],
        ["bibtex", ".build/" + stem],
        [engine, "-interaction=nonstopmode", "-halt-on-error", "-file-line-error", "-output-directory=.build", stem + ".tex"],
        [engine, "-interaction=nonstopmode", "-halt-on-error", "-file-line-error", "-output-directory=.build", stem + ".tex"],
    ]
    with (build / (stem + "-build.log")).open("w", encoding="utf-8") as log:
        for command in commands:
            result = subprocess.run(command, cwd=ROOT, env=environment, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                    text=True, encoding="utf-8", errors="replace")
            log.write(" ".join(command) + "\n" + result.stdout + "\n")
            log.flush()
            if result.returncode:
                print(result.stdout[-7000:])
                raise SystemExit(f"编译失败；见 .build/{stem}-build.log")
    shutil.copy2(build / (stem + ".pdf"), ROOT / (stem + ".pdf"))
    print(f"{stem}.pdf 编译成功")
