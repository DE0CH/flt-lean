## `pkill -f "lake build"` IS A FLEET-WIDE KILL SWITCH — IT MATCHES THE AGENTS THEMSELVES
(2026-07-31, measured on gambit while stopping one worktree's own build.) `pkill`/`pgrep -f`
match against the WHOLE command line of EVERY process on the host, and the fleet runs ~25
worktrees on one machine. So a pattern chosen to mean "my build" means "everyone's build":
    pgrep -f "lake build" | wc -l          # 70 processes, across 25 worktrees
**24 of those 70 were the agents' own `flt-job-*` Claude processes.** Not their builds — the
agents. Every prover prompt contains the sentence *"Verify with `lake build` on the module"*, and
the prompt is passed as an argv element, so the literal string `lake build` is in the command
line of every running agent. `pkill -f "lake build"` therefore SIGTERMs two dozen live agents
mid-proof along with every build on the box. Nothing about the command looks dangerous, which is
the point of writing it down.
Scope the pattern to the worktree PATH, which is the one string that is actually yours:
    pkill -f "/home/chend/flt-lean-N/Fermat"     # only this worktree's lean workers
And note the two traps that follow from it. **`lake build`'s `lean` workers do not have "lake
build" in their command line** — they are `.../bin/lean <path> -o <path>`, so killing the `lake`
parent orphans the children, which keep elaborating and keep writing into `.lake`. Kill by path
or you leave writers behind. And **a module that reports `error: Lean exited with code 143` was
SIGTERMed, not broken** — 143 is 128+15. Two modules failed that way here and neither had
anything wrong with it; reading 143 as a defect is how a phantom "broken on main" report gets
written.
Before any `pkill`, run the same pattern through `pgrep -af` first and read what comes back. It
costs one command and it is the only way to see the blast radius, which on this host is never
just you.
