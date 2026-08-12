import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.AlgebraicGeometry.Limits

open AlgebraicGeometry CategoryTheory

universe u

instance (X Y : TopCat) [ie : IsEmpty X] : Unique (X ⟶ Y) where
  default := TopCat.ofHom
    { toFun i := False.elim <| ie.elim i
      continuous_toFun := by continuity }
  uniq := by
    intro f
    ext x
    exact False.elim <| ie.elim x

open ZeroObject Zero

noncomputable instance (X : Scheme) [ie : IsEmpty X] : Limits.IsInitial X := isInitialOfIsEmpty

noncomputable instance (X Y : Scheme) [ie : IsEmpty X] : Unique (X ⟶ Y) where
  default := Limits.IsInitial.to isInitialOfIsEmpty Y
  uniq f := Limits.IsInitial.hom_ext isInitialOfIsEmpty f _
