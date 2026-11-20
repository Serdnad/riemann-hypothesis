#!/usr/bin/env python3
"""Migrate exact-signature forwarding modules and validate their direct importers."""

import argparse
import csv
import json
import os
import re
import shlex
import shutil
import subprocess
import tempfile
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PROJECT = ROOT / "lean"
SOURCE = PROJECT / "src"
IMPORT = re.compile(rb"(?m)^(?:(?:public|private|meta)[ \t]+)*import[ \t]+([^\r\n]+)")
SIGNATURE = re.compile(
    r"(?m)^(?:theorem|lemma)[ \t]+([^\s:({\[]+)[ \t]*:[ \t]*(.+?)[ \t]+:=[ \t]*(?:by[ \t]*)?$"
)
WRAPPER = re.compile(
    r"(?m)^theorem[ \t]+([^\s:({\[]+)[ \t]*:[ \t]*(.+?)[ \t]+:=[ \t]*by\n"
    r"[ \t]+first \| exact @(\S+) \| exact \3 \| \(intros; apply \3 <;> assumption\)\s*\Z"
)


@dataclass(frozen=True)
class Migration:
    wrapper: str
    provider: str
    theorem: str
    implementation: str
    signature: str
    scoped_commands: tuple
    callers: tuple
    dependencies: frozenset

    @property
    def targets(self):
        return self.wrapper, self.provider, *self.callers


def imported(source):
    return tuple(name.decode() for match in IMPORT.finditer(source) for name in match[1].split())


def index_sources():
    entries = subprocess.check_output(["rg", "--files", "-0", "-g", "*.lean"], cwd=SOURCE)
    locations = {}
    graph = {}
    importers = defaultdict(list)
    for entry in entries.split(b"\0"):
        if not entry:
            continue
        relative = Path(os.fsdecode(entry))
        module = ".".join(relative.with_suffix("").parts)
        locations[module] = relative
        imports = imported((SOURCE / relative).read_bytes())
        graph[module] = imports
        for dependency in set(imports):
            importers[dependency].append(module)
    return locations, graph, importers


def closure(graph, roots, limit=None):
    visited = set()
    pending = list(roots)
    while pending:
        module = pending.pop()
        if module in visited or module not in graph:
            continue
        visited.add(module)
        if limit is not None and len(visited) > limit:
            return None
        pending.extend(graph[module])
    return visited


def import_line(module):
    return re.compile(rb"(?m)^import[ \t]+" + re.escape(module.encode()) + rb"[ \t]*(?=\r?$)")


def plan_row(row, locations, graph, importers, main_modules, max_closure):
    wrapper = row["statement_module"]
    provider = row["implementation_module"]
    callers = tuple(sorted(importers[wrapper]))
    if wrapper not in main_modules or provider not in graph[wrapper] or not callers:
        return None
    dependency_set = closure(graph, [wrapper, *callers], max_closure)
    if dependency_set is None:
        return None
    provider_closure = closure(graph, [provider], max_closure)
    available = provider_closure | {dep for module in provider_closure for dep in graph[module]}
    if not set(graph[wrapper]).issubset(available):
        return None

    text = (SOURCE / locations[wrapper]).read_text()
    match = WRAPPER.search(text)
    if match is None or match[1] != row["statement_theorem"] or match[3] != row["implementation_theorem"]:
        return None
    commands = tuple(
        line.strip() for line in text[:match.start()].splitlines()
        if line.strip() and not line.startswith("import ")
    )
    if any(not command.startswith(("open ", "attribute [local ")) and
           not (command.startswith("set_option ") and command.endswith(" in")) for command in commands):
        return None
    provider_source = (SOURCE / locations[provider]).read_text()
    name = match[3].rsplit(".", 1)[-1]
    signatures = [item[2].strip() for item in SIGNATURE.finditer(provider_source)
                  if item[1].rsplit(".", 1)[-1] == name]
    if signatures != [match[2].strip()]:
        return None
    pattern = import_line(wrapper)
    if any(len(pattern.findall((SOURCE / locations[caller]).read_bytes())) != graph[caller].count(wrapper)
           for caller in callers):
        return None
    return Migration(wrapper, provider, match[1], match[3], match[2].strip(),
                     commands, callers, frozenset(dependency_set))


def select_migrations(inventory, locations, graph, importers, max_closure, limit):
    main_modules = closure(graph, ["Main"])
    with inventory.open(newline="") as rows:
        candidates = [candidate for row in csv.DictReader(rows, delimiter="\t")
                      if (candidate := plan_row(row, locations, graph, importers, main_modules, max_closure))]
    selected = []
    occupied = set()
    for candidate in sorted(candidates, key=lambda item: (len(item.dependencies), item.wrapper)):
        if occupied.intersection(candidate.targets):
            continue
        selected.append(candidate)
        occupied.update(candidate.targets)
        if len(selected) == limit:
            break
    return selected


def qualified(name):
    return "_root_." + name.removeprefix("_root_.")


def edit(migration, paths):
    provider = paths[migration.provider]
    original = provider.read_bytes()
    theorem, implementation = map(qualified, (migration.theorem, migration.implementation))
    appendix = (
        f"\ntheorem {theorem} : type_of% @{implementation} :=\n"
        f"  @{implementation}\n"
    ).encode()
    provider.write_bytes(original + (b"" if original.endswith(b"\n") else b"\n") + appendix)
    paths[migration.wrapper].write_text(f"import {migration.provider}\n")
    pattern = import_line(migration.wrapper)
    for caller in migration.callers:
        path = paths[caller]
        path.write_bytes(pattern.sub(f"import {migration.provider}".encode(), path.read_bytes()))


def signature_checks(migrations):
    imports = [f"import {item.wrapper}" for item in migrations]
    blocks = []
    for item in migrations:
        theorem = qualified(item.theorem)
        blocks.extend([
            "section",
            *item.scoped_commands,
            f"example : (type_of% @{theorem}) = ({item.signature}) := rfl",
            "end",
            "",
        ])
    return "\n".join([*imports, "", "set_option autoImplicit false",
                      "set_option relaxedAutoImplicit false", "", *blocks])


def run_checks(sandbox, migrations, jobs, log_dir, number):
    targets = sorted({f"+{module}" for item in migrations for module in item.targets})
    guard = sandbox / "CheckForwardingSignatures.lean"
    guard.write_text(signature_checks(migrations))
    shutil.copyfile(guard, log_dir / f"trial-{number:03d}.lean")
    commands = [
        ["lake", "--no-ansi", "build", *targets],
        ["lake", "env", "lean", guard.name],
    ]
    env = dict(os.environ, LEAN_NUM_THREADS=str(jobs),
               ELAN_TOOLCHAIN=(sandbox / "lean-toolchain").read_text().strip())
    log_path = log_dir / f"trial-{number:03d}.log"
    with log_path.open("w") as output:
        for command in commands:
            print("$ " + shlex.join(command), file=output, flush=True)
            status = subprocess.run(command, cwd=sandbox, env=env, stdout=output,
                                    stderr=subprocess.STDOUT, check=False).returncode
            if status:
                break
        else:
            return True
    if "incompatible header" in log_path.read_text(errors="replace"):
        raise SystemExit(f"Incompatible Lean build artifacts. See {log_path}. Source edits were discarded.")
    return False


def migrate(selected, locations, log_dir, jobs, apply):
    dependencies = set().union(*(item.dependencies for item in selected))
    originals = {module: (SOURCE / locations[module]).read_bytes() for module in dependencies}
    passed = []
    rejected = {}
    trials = 0
    with tempfile.TemporaryDirectory(prefix="rh-forwarding-") as temporary:
        sandbox = Path(temporary)
        for filename in ("lean-toolchain", "lakefile.toml", "lake-manifest.json"):
            shutil.copyfile(PROJECT / filename, sandbox / filename)
        (sandbox / ".lake").mkdir()
        (sandbox / ".lake" / "packages").symlink_to(PROJECT / ".lake" / "packages", target_is_directory=True)
        paths = {module: sandbox / "src" / locations[module] for module in dependencies}
        for module, path in paths.items():
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(originals[module])

        def try_group(group):
            nonlocal trials
            snapshot = {module: paths[module].read_bytes() for item in group for module in item.targets}
            for item in group:
                edit(item, paths)
            trials += 1
            number = trials
            print(f"Trial {number}: {len(group)} migrations", flush=True)
            if run_checks(sandbox, [*passed, *group], jobs, log_dir, number):
                passed.extend(group)
                print(f"  passed: {len(group)}", flush=True)
                return
            for module, content in snapshot.items():
                paths[module].write_bytes(content)
            if len(group) == 1:
                rejected[group[0].wrapper] = f"trial-{number:03d}.log"
                print(f"  rejected: {group[0].wrapper}", flush=True)
                return
            middle = len(group) // 2
            try_group(group[:middle])
            try_group(group[middle:])

        try_group(selected)
        if apply:
            for module, content in originals.items():
                if (SOURCE / locations[module]).read_bytes() != content:
                    raise SystemExit(f"Source changed during validation: {module}. Source edits were discarded.")
            written = []
            try:
                for module in sorted({module for item in passed for module in item.targets}):
                    written.append(module)
                    (SOURCE / locations[module]).write_bytes(paths[module].read_bytes())
            except BaseException:
                for module in written:
                    (SOURCE / locations[module]).write_bytes(originals[module])
                raise

    report = {
        "validated": [{"wrapper": item.wrapper, "provider": item.provider, "callers": item.callers}
                      for item in passed],
        "rejected": rejected,
        "trials": trials,
        "applied": apply,
    }
    (log_dir / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"{len(passed)} passed, {len(rejected)} rejected, {trials} trials. Logs: {log_dir}", flush=True)


def positive(value):
    number = int(value)
    if number < 1:
        raise argparse.ArgumentTypeError("must be positive")
    return number


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("inventory", type=Path, help="TSV of exact-signature candidates")
    parser.add_argument("--limit", type=positive, default=32, help="maximum migrations in one run")
    parser.add_argument("--max-closure", type=positive, default=12,
                        help="maximum project modules needed by one migration and its callers")
    parser.add_argument("--jobs", type=positive, default=6, help="Lean task threads")
    parser.add_argument("--log-dir", type=Path, required=True)
    parser.add_argument("--apply", action="store_true", help="copy only validated edits into the checkout")
    args = parser.parse_args()
    if not (PROJECT / ".lake" / "packages").is_dir():
        parser.error("Lake dependencies must be available in lean/.lake/packages")
    args.log_dir.resolve().mkdir(parents=True, exist_ok=False)
    locations, graph, importers = index_sources()
    selected = select_migrations(args.inventory, locations, graph, importers, args.max_closure, args.limit)
    if selected:
        print(f"Selected {len(selected)} candidates", flush=True)
        migrate(selected, locations, args.log_dir.resolve(), args.jobs, args.apply)
    else:
        print("No candidates matched the current sources and limits.", flush=True)


if __name__ == "__main__":
    main()
