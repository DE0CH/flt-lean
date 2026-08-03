## WRITING THE NOTE THAT RECORDS COMMENT DAMAGE CAN REOPEN IT

(Same release, caught by re-running the scan.)  CLAUDE.md already says a comment
delimiter spelled inside block-comment prose still NESTS.  It bites hardest in the
one place you are guaranteed to write such prose: the note explaining the repair.
My first draft of three "orphaned docstring body, reopened" notes contained the
opener and closer as inline code, which added two levels of nesting per note and
turned three STRAY reports into an UNCLOSED one.

Name the delimiters in WORDS in any comment about comments, and say in the note that
you did — the next editor will otherwise "improve" it back.  And re-run the scan
after every such edit, not just after the repair it documents.

`tools/merge/commentscan.py` (added this release) is the scanner: character-level,
nesting-aware, and it reports **UNCLOSED and STRAY separately** because the two
cancel.  `checks.py check-comment` walks LINES and clears a block at the first line
containing a terminator, so it cannot see either shape — it reported the whole tree
balanced while four files were wounded.  Run the new one tree-wide, every release,
before the first build: it is the cheapest check there is and one parse error hides
every later error in an 84 000-line module.

