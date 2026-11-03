# Projective blowups in Lean 4

Lean 4 formalization of projective blowups along finite families of closed
subschemes, accompanying the paper "Projective blowups: a formal and
multicentered proof".

Main results: `GlobalBlowup_UnivProp` (Project/Blowups/BlowupExists.lean),
`exists_blowup_isEffectiveCartier` (Project/Blowups/IdealSheaf.lean).

Lean v4.22.0-rc3, mathlib 7b332d3. Build: `lake exe cache get && lake build`.

Includes portions of the code of A. Mayeux and J. Zhang, J. Automat. Reason. 70
(2026), doi:10.1007/s10817-026-09764-x, updated to this version of mathlib.
