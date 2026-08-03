## AN UNINDEXED MEMORY IS A MEMORY NO AGENT EVER READS — CHECK `files == links` AFTER ANY MERGE THAT ADDS THEM
(Same run.)  `memory/MEMORY.md` is the index loaded into context each session;
the memory FILES are not.  So a memory on disk with no line in `MEMORY.md` is
invisible to every agent for ever — the fourth invisibility class, applied to the
fleet's own lessons instead of to Lean.
Release 34 inherited **89** of them: `main`'s own commit *"memory: fold in the
fleet's accumulated lessons (129 files)"* added the files and indexed only some.
Nothing reports this.  The build is green, the files are real, the index is
well-formed, and every one of the 89 lessons — including several this project
paid an agent-run each to learn — was dead weight on disk.
**The check is four lines and belongs after any merge that touches `memory/`:**
    linked = set(re.findall(r'\]\(([^)]+)\)', (mem/'MEMORY.md').read_text()))
    files  = {p.name for p in mem.glob('*.md')} - {'MEMORY.md'}
    assert not (files - linked), files - linked      # unindexed  => invisible
    assert not (linked - files), linked - files      # dangling   => stale entry
Both directions matter and they fail differently: an unindexed file is a lesson
nobody reads, a dangling link is an entry pointing at a deleted file — and the
dangling one found here (`flt-no-lake-build-trust-mcp.md`) named doctrine
CLAUDE.md now CONTRADICTS, the MCP having been deleted on 2026-07-25.  A stale
index entry is worse than none, because it reads as a lesson that exists.
