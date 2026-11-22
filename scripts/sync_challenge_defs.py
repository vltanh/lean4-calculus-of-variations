#!/usr/bin/env python3
"""Copy the shared definitions of the library into the Challenges, or check the copies.

Comparator requires every constant that a Challenge statement uses to be the same in the Challenge
and in the Solution's environment. A Challenge may not import the library, so the definitions that
the Challenges need are marked blocks of one module of the library, each between

    -- BEGIN SHARED DEFINITIONS: <name>
    -- END SHARED DEFINITIONS: <name>

and this script copies the blocks of each Challenge verbatim from that module. The Challenge and
the module must also import exactly the same modules (so that the definitions elaborate in the same
way in both), which the script checks; with it, every Challenge declares the same definitions as
the library.

Run from anywhere in the repository:

    python3 scripts/sync_challenge_defs.py           # rewrite the blocks in the Challenges
    python3 scripts/sync_challenge_defs.py --check   # exit 1 if a copy differs (for CI)
"""

import re
import sys
from pathlib import Path

# ---- configuration -------------------------------------------------------------------------
# The library module that holds the shared definitions, and the blocks of each Challenge.
DEFS = 'CalculusOfVariations/Basic.lean'
CHALLENGES = {
    'palomar/Quasiconvexity/Challenge.lean': ['core', 'periodic'],
    'palomar/QuasiconvexEnvelope/Challenge.lean': ['core', 'envelope'],
    'palomar/NullLagrangians/Challenge.lean': ['core', 'minors'],
}
BEGIN = '-- BEGIN SHARED DEFINITIONS: {}\n'
END = '-- END SHARED DEFINITIONS: {}\n'
# ---------------------------------------------------------------------------------------------

ROOT = Path(__file__).resolve().parent.parent


def span(text: str, name: str, block: str) -> tuple[int, int]:
    """The span of a block in `text`, markers included."""
    begin, end = BEGIN.format(block), END.format(block)
    i, j = text.find(begin), text.find(end)
    if i < 0 or j < i or text.count(begin) != 1 or text.count(end) != 1:
        sys.exit(f'{name}: expected exactly one pair of markers for the block "{block}"')
    return i, j + len(end)


def imports(text: str) -> set[str]:
    """The modules that a file imports."""
    return set(re.findall(r'^(?:public )?import (?:all )?(\S+)', text, re.M))


def sync(chal_name: str, blocks: list[str], check: bool) -> bool:
    """Copy (or, with `check`, compare) the blocks of one Challenge; return whether it was current."""
    defs, path = (ROOT / DEFS).read_text(), ROOT / chal_name
    chal, current = path.read_text(), True
    found = re.findall(r'^-- BEGIN SHARED DEFINITIONS: (.*)$', chal, re.M)
    if found != blocks:
        sys.exit(f'{chal_name}: expected the blocks {blocks}, found {found}')
    if imports(chal) != imports(defs):
        print(f'{chal_name}: the imports differ from those of {DEFS}: '
              f'{sorted(imports(chal) ^ imports(defs))}')
        current = False
    for block in blocks:
        di, dj = span(defs, DEFS, block)
        ci, cj = span(chal, chal_name, block)
        if chal[ci:cj] != defs[di:dj]:
            current = False
            if check:
                print(f'{chal_name}: the block "{block}" differs from {DEFS}; '
                      f'run python3 scripts/sync_challenge_defs.py')
            chal = chal[:ci] + defs[di:dj] + chal[cj:]
    if not check:
        path.write_text(chal)
        print(f'{chal_name}: {", ".join(blocks)} copied from {DEFS}')
    elif current:
        print(f'{chal_name}: the blocks {", ".join(blocks)} and the imports match {DEFS}')
    return current


def main() -> None:
    args = sys.argv[1:]
    if args and args[0] in ('-h', '--help') or any(a != '--check' for a in args):
        print(__doc__.strip())
        sys.exit(0 if args and args[0] in ('-h', '--help') else 2)
    check = '--check' in args
    current = [sync(c, blocks, check) for c, blocks in CHALLENGES.items()]
    if check and not all(current):
        sys.exit(1)


if __name__ == '__main__':
    main()
