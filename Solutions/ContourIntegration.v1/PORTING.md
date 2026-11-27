# Porting notes

`ResidueRectangle.lean` is `Mathlib/Analysis/Complex/ResidueRectangle.lean` of branch
`mv-lemma-12-14` of `Garald1/mathlib-at-ICERM26` at `e62f9988` (Lean v4.30.0-rc2), built here at
IEANTN's pin (Lean v4.34.0-rc2, Mathlib `71a80585`). Changes:

- `module` and `@[expose] public section` deleted, `public import` → `import`.
- `convert` → `convert!`: Mathlib's `convert` now closes leftover goals only at reducible
  transparency, and here it left instance goals such as
  `addCommGroup = DenselyNormedField.toNontriviallyNormedField.toDivisionRing.toAddCommGroup` open.
- Three local repairs where `simpa`/`simp` stopped matching across instance paths on `ℂ`:
  `simpa using (hΦ x hx).comp x hin` → `rw [mul_one]` then `exact`;
  `simpa using (hasDerivAt_id _).neg` → `exact hasDerivAt_neg _`; two no-op `simp only []` removed.

No statement was changed.
