import Mathlib.AlgebraicGeometry.Over
import Project.Proj.Construction

suppress_compilation

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace GoodPotionIngredient

universe u
variable {ι : Type} {τ R₀ A : Type u}
variable [AddCommGroup ι] [CommRing R₀] [CommRing A] [Algebra R₀ A] {𝒜 : ι → Submodule R₀ A}
variable [DecidableEq ι] [GradedAlgebra 𝒜]

variable (ℱ : τ → GoodPotionIngredient 𝒜)

scoped notation "SpecBase"ℬ => Spec (CommRingCat.of (ℬ 0))

def over : Proj ℱ ⟶ SpecBase 𝒜 :=
  Multicoequalizer.desc _ _
    (fun S ↦ (Spec.map <| CommRingCat.ofHom <| algebraMap _ _)) <| by
    intro S
    simp only [GlueData.diagram_left, GlueData.diagram_right]
    change (Spec.map _) ≫ _ = (Spec.map _ ≫ Spec.map _) ≫ _
    simp only [mul_toHomogeneousSubmonoid, HomogeneousSubmonoid.mul_toSubmonoid, ← Spec.map_comp,
      RingEquiv.toRingHom_eq_coe]
    congr 1

instance : Scheme.Over (X := Proj ℱ) (SpecBase 𝒜) where
  hom :=  over ℱ

lemma proj_structureMorphism_eq : (Proj ℱ) ↘ (SpecBase 𝒜) = over ℱ := rfl

end GoodPotionIngredient
