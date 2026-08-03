## `set_option … in` GOES BEFORE THE DOCSTRING, NOT BETWEEN IT AND THE DECLARATION

(2026-07-31.) `/-- doc -/ set_option maxHeartbeats 2000000 in theorem foo …` does not parse:
`unexpected token 'set_option'; expected 'lemma'`. The doc comment must be immediately followed by
a declaration keyword, so the modifier belongs ABOVE it:

    set_option maxHeartbeats 2000000 in
    /-- doc -/
    theorem foo …

Trivial, and it cost a full 40-minute build of a 25 000-line module to discover, because the
elaborator reaches the syntax error only after loading the whole import cone. Cheap insurance: after
inserting any `set_option … in`, grep the file for `-/$` immediately preceding it.

