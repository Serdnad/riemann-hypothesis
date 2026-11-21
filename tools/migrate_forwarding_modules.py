#!/usr/bin/env python3
"""Migrate exact-signature forwarders and build direct importers of both module paths."""

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
PACKAGE_FILES = ("lean-toolchain", "lakefile.toml", "lake-manifest.json")
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
    provider_callers: tuple
    dependencies: frozenset

    @property
    def edited_modules(self):
        return self.wrapper, self.provider, *self.callers

    @property
    def targets(self):
        return self.edited_modules + self.provider_callers


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


def reusable_modules(packages, locations):
    """Find complete Lake artifacts with matching source and package settings."""
    settings = {name: (PROJECT / name).read_bytes() for name in PACKAGE_FILES}
    modules = {}
    for package in packages:
        if any(not (package / name).is_file() or (package / name).read_bytes() != content
               for name, content in settings.items()):
            raise SystemExit(f"Cache package settings differ from {PROJECT}: {package}")
        build = package / ".lake" / "build"
        library = build / "lib" / "lean"
        for object_file in library.rglob("*.olean"):
            module = ".".join(object_file.relative_to(library).with_suffix("").parts)
            if module in modules or module not in locations:
                continue
            source = package / "src" / locations[module]
            if (not source.is_file() or not object_file.with_suffix(".trace").is_file() or
                    object_file.stat().st_mtime_ns < source.stat().st_mtime_ns):
                continue
            if source.read_bytes() == (SOURCE / locations[module]).read_bytes():
                modules[module] = build
    return modules


def seed_artifacts(sandbox, dependencies, locations, reusable):
    target = sandbox / ".lake" / "build"
    for module in sorted(dependencies & reusable.keys()):
        stem = locations[module].with_suffix("")
        for folder in ("lib/lean", "ir"):
            source = reusable[module] / folder / stem
            for artifact in source.parent.glob(f"{stem.name}.*"):
                if artifact.is_file() and not artifact.name.endswith(".setup.json"):
                    destination = target / folder / stem.parent / artifact.name
                    destination.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copy2(artifact, destination)


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


def plan_row(row, locations, graph, importers, main_modules, max_closure,
             include_prefixes=(), exclude_prefixes=()):
    wrapper = row["statement_module"]
    provider = row["implementation_module"]
    callers = tuple(sorted(importers[wrapper]))
    if wrapper not in main_modules or provider not in graph[wrapper] or not callers:
        return None
    edited_modules = (wrapper, provider, *callers)
    if include_prefixes and not all(module.startswith(include_prefixes) for module in edited_modules):
        return None
    if any(module.startswith(exclude_prefixes) for module in edited_modules):
        return None
    provider_callers = tuple(sorted(set(importers[provider]) - {wrapper, *callers}))
    dependency_set = closure(graph, [wrapper, *callers, *provider_callers], max_closure)
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
                     commands, callers, provider_callers, frozenset(dependency_set))


def select_migrations(inventory, locations, graph, importers, max_closure, limit,
                      include_prefixes=(), exclude_prefixes=(), reusable=frozenset()):
    main_modules = closure(graph, ["Main"])
    with inventory.open(newline="") as rows:
        candidates = [candidate for row in csv.DictReader(rows, delimiter="\t")
                      if (candidate := plan_row(row, locations, graph, importers, main_modules,
                                                max_closure, include_prefixes, exclude_prefixes))]
    selected = []
    edited_modules = set()
    theorem_modules = set()
    def build_priority(item):
        needed = (item.dependencies - reusable) | set(item.targets)
        return len(needed), len(item.dependencies), item.wrapper

    for candidate in sorted(candidates, key=build_priority):
        module_paths = {candidate.wrapper, candidate.provider}
        if edited_modules & module_paths or theorem_modules.intersection(candidate.callers):
            continue
        selected.append(candidate)
        edited_modules.update(candidate.edited_modules)
        theorem_modules.update(module_paths)
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


def run_checks(sandbox, migrations, jobs, log_dir, number, runner=(), reuse_cache=False):
    targets = sorted({f"+{module}" for item in migrations for module in item.targets})
    guard = sandbox / "CheckForwardingSignatures.lean"
    guard.write_text(signature_checks(migrations))
    shutil.copyfile(guard, log_dir / f"trial-{number:03d}.lean")
    lake_options = ["--rehash"] if reuse_cache else []
    commands = [
        ["lake", "--no-ansi", *lake_options, "build", *targets],
        ["lake", "env", "lean", guard.name],
    ]
    env = dict(os.environ, LEAN_NUM_THREADS=str(jobs),
               ELAN_TOOLCHAIN=(sandbox / "lean-toolchain").read_text().strip())
    log_path = log_dir / f"trial-{number:03d}.log"
    with log_path.open("w") as output:
        for command in commands:
            command = [*runner, *command]
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


def migrate(selected, locations, log_dir, jobs, apply, runner=(), reusable=None, save_cache=False):
    reusable = reusable or {}
    dependencies = set().union(*(item.dependencies for item in selected))
    originals = {module: (SOURCE / locations[module]).read_bytes() for module in dependencies}
    passed = []
    rejected = {}
    trials = 0
    with tempfile.TemporaryDirectory(prefix="rh-forwarding-") as temporary:
        sandbox = Path(temporary)
        for filename in PACKAGE_FILES:
            shutil.copyfile(PROJECT / filename, sandbox / filename)
        (sandbox / ".lake").mkdir()
        (sandbox / ".lake" / "packages").symlink_to(PROJECT / ".lake" / "packages", target_is_directory=True)
        paths = {module: sandbox / "src" / locations[module] for module in dependencies}
        for module, path in paths.items():
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(originals[module])
        seed_artifacts(sandbox, dependencies, locations, reusable)

        def try_group(group):
            nonlocal trials
            snapshot = {module: paths[module].read_bytes()
                        for item in group for module in item.edited_modules}
            for item in group:
                edit(item, paths)
            trials += 1
            number = trials
            print(f"Trial {number}: {len(group)} migrations", flush=True)
            if run_checks(sandbox, [*passed, *group], jobs, log_dir, number, runner, bool(reusable)):
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
        if save_cache and passed:
            shutil.copytree(sandbox / ".lake" / "build", log_dir / "cache" / ".lake" / "build",
                            ignore=shutil.ignore_patterns("*.setup.json"))
            shutil.copytree(sandbox / "src", log_dir / "cache" / "src")
            for filename in PACKAGE_FILES:
                shutil.copyfile(sandbox / filename, log_dir / "cache" / filename)
        if apply:
            validated_dependencies = set().union(*(item.dependencies for item in passed))
            for module in validated_dependencies:
                if (SOURCE / locations[module]).read_bytes() != originals[module]:
                    raise SystemExit(f"Source changed during validation: {module}. Source edits were discarded.")
            written = []
            try:
                for module in sorted({module for item in passed for module in item.edited_modules}):
                    written.append(module)
                    (SOURCE / locations[module]).write_bytes(paths[module].read_bytes())
            except BaseException:
                for module in written:
                    (SOURCE / locations[module]).write_bytes(originals[module])
                raise

    report = {
        "validated": [{"wrapper": item.wrapper, "provider": item.provider, "callers": item.callers,
                       "provider_callers": item.provider_callers}
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
    parser.add_argument("--include-prefix", action="append", default=[],
                        help="only edit modules under the selected module prefixes")
    parser.add_argument("--exclude-prefix", action="append", default=[],
                        help="exclude edits in a module prefix reserved for other work")
    parser.add_argument("--runner", type=shlex.split, default=[],
                        help="command prefix for the compile and signature checks")
    parser.add_argument("--reuse-cache", type=Path, action="append", default=[],
                        help="copy matching artifacts from this already-built Lean package")
    parser.add_argument("--save-cache", action="store_true",
                        help="save the source snapshot and compiled artifacts in the log folder")
    parser.add_argument("--plan-only", action="store_true",
                        help="report the selected batch without building or editing")
    parser.add_argument("--apply", action="store_true", help="copy only validated edits into the checkout")
    args = parser.parse_args()
    if not (PROJECT / ".lake" / "packages").is_dir():
        parser.error("Lake dependencies must be available in lean/.lake/packages")
    args.log_dir.resolve().mkdir(parents=True, exist_ok=False)
    locations, graph, importers = index_sources()
    reusable = reusable_modules(args.reuse_cache, locations)
    selected = select_migrations(args.inventory, locations, graph, importers, args.max_closure,
                                 args.limit, tuple(args.include_prefix), tuple(args.exclude_prefix),
                                 reusable.keys())
    if selected:
        dependencies = set().union(*(item.dependencies for item in selected))
        print(f"Selected {len(selected)} candidates across {len(dependencies)} project modules, "
              f"with {len(dependencies & reusable.keys())} matching cached artifacts", flush=True)
        if args.plan_only:
            (args.log_dir / "plan.txt").write_text(
                "".join(f"{item.wrapper}\n" for item in selected))
        else:
            migrate(selected, locations, args.log_dir.resolve(), args.jobs, args.apply, args.runner,
                    reusable, args.save_cache)
    else:
        print("No candidates matched the current sources and limits.", flush=True)


if __name__ == "__main__":
    main()
