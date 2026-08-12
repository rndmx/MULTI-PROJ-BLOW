import Project.Dilatation.Family
import Project.Dilatation.lemma
import Project.Grading.Injection

import Project.Potions.Basic

import Mathlib.RingTheory.GradedAlgebra.Basic

suppress_compilation

open DirectSum Family

section semiring

variable {A : Type*} [CommSemiring A]
variable {ι : Type*} (F : ι → Ideal A)

@[ext]
structure ReesAlgebra where
  val : ⨁ (v : ι →₀ ℕ), F^v

namespace ReesAlgebra

instance : Zero (ReesAlgebra F) where
  zero := { val := 0 }

lemma zero_def :
  (0 : ReesAlgebra F) = { val := 0 } := rfl

instance : SMul ℕ (ReesAlgebra F) where
  smul n x := { val := n • x.val }

lemma nsmul_def (n : ℕ) (x : ReesAlgebra F) :
  n • x = { val := n • x.val } := rfl

instance : Add (ReesAlgebra F) where
  add x y := { val := x.val + y.val }

lemma add_def {x y : ReesAlgebra F} :
  x + y = { val := x.val + y.val } := rfl

lemma add_val {x y : ReesAlgebra F} :
  (x + y).val = x.val + y.val := rfl

lemma injective_val : Function.Injective (val : ReesAlgebra F → ⨁ (v : ι →₀ ℕ), F^v) := by
  intro x y h
  cases x; cases y
  simp only [ReesAlgebra.val] at h
  subst h
  rfl

instance : AddCommMonoid (ReesAlgebra F) :=
  Function.Injective.addCommMonoid (val (F := F)) (injective_val F) rfl
    (fun _ _ => rfl) (fun _ _ => rfl)

variable [DecidableEq ι]

variable {F}

def mul' : (⨁ (v : ι →₀ ℕ), F^v) →+ ((⨁ (v : ι →₀ ℕ), F^v) →+ (⨁ (v : ι →₀ ℕ), F^v)) :=
  DirectSum.toAddMonoid fun v ↦
    { toFun x := DirectSum.toAddMonoid fun w ↦
        { toFun y := DirectSum.of _ (v + w) ⟨x * y, Ideal.mem_familyPow_add x.2 y.2⟩
          map_zero' := by ext; simp [DirectSum.coe_of_apply]
          map_add' := by intros; ext; simp [DirectSum.coe_of_apply]; split_ifs <;> simp [mul_add]
          }
      map_zero' := by ext; simp [DirectSum.coe_of_apply]
      map_add' := by intros; ext; simp [DirectSum.coe_of_apply]; split_ifs <;> simp [add_mul] }

@[simp]
lemma mul'_of_of (v w :  ι →₀ ℕ) (x : F^v) (y : F^w) :
    mul' (.of _ v x) (.of _ w y) =
    .of _ (v + w) ⟨x.1 * y.1, Ideal.mem_familyPow_add x.2 y.2⟩ := by
  simp [mul']

instance : Mul (ReesAlgebra F) where
  mul x y := { val := mul' x.val y.val }

lemma mul_def (x y : ReesAlgebra F) :
  x * y = { val := mul' x.val y.val } := rfl

lemma mul_val (x y : ReesAlgebra F) :
  (x * y).val = mul' x.val y.val := rfl

@[simp]
lemma mul_of_of (v w : ι →₀ ℕ) (x y) :
    ({ val := .of _ v x } : ReesAlgebra F) * { val := .of _ w y } =
    { val := .of _ (v + w) ⟨x.1 * y.1, Ideal.mem_familyPow_add x.2 y.2⟩ } := by
  ext : 1
  exact mul'_of_of ..

instance : One (ReesAlgebra F) where
  one := { val := .of _ 0 ⟨1, by simp⟩ }

lemma one_def :
  (1 : ReesAlgebra F) = { val := .of _ 0 ⟨1, by simp⟩ } := rfl

lemma one_val :
  (1 : ReesAlgebra F).val = .of _ 0 ⟨1, by simp⟩ := rfl

instance : LeftDistribClass (ReesAlgebra F) where
  left_distrib := by intros; simp [mul_def, add_def]

instance : RightDistribClass (ReesAlgebra F) where
  right_distrib := by intros; simp [mul_def, add_def]

lemma induction_on (P : ReesAlgebra F → Prop) (H_zero : P 0) (H_basic : ∀ v x, P { val := .of _ v x })
  (H_plus : ∀ x y, P x → P y → P (x + y)) : ∀ x, P x := by
  rintro ⟨x⟩
  induction x using DirectSum.induction_on with
  |zero => exact H_zero
  |of v x => exact H_basic v x
  |add x y hx hy => exact H_plus _ _ hx hy

instance : Semigroup (ReesAlgebra F) where
  mul_assoc := by
   intro a b c
   induction a using induction_on with
   |H_zero => simp [mul_def, zero_def]
   |H_basic va ma =>
    induction b using induction_on with
     |H_zero => simp [mul_def, zero_def]
     |H_basic vb mb =>
       induction c using induction_on with
       |H_zero => simp [mul_def, zero_def]
       |H_basic vc mc =>
        simp only [mul_of_of]
        ext
        simp only [mul_assoc, coe_of_apply, add_assoc]
        split_ifs <;> rfl
       |H_plus x y hx hy =>
        simp only [mul_def, mul'_of_of, mk.injEq, add_def, map_add] at hx hy ⊢
        rw[← hx,← hy]
     |H_plus x y hx hy =>
      simp only [mul_def, mk.injEq, add_def, map_add, AddMonoidHom.add_apply] at hx hy ⊢
      rw[← hx,← hy]
   |H_plus x y hx hy =>
    simp only [mul_def, mk.injEq, add_def, map_add, AddMonoidHom.add_apply] at hx hy ⊢
    rw[← hx,← hy]

instance : MulOneClass (ReesAlgebra F) where
  one_mul := by
    intro a
    induction  a using induction_on with
    |H_zero =>
      simp [mul_def, one_def, zero_def]
    | H_basic i x =>
      rw [one_def, mul_of_of]
      ext
      simp only [one_mul, coe_of_apply, zero_add]
      split_ifs <;> rfl
    | H_plus x y hx hy =>
      rw [mul_add, hx, hy]
  mul_one := by
    intro a
    induction  a using induction_on with
    |H_zero =>
      simp [mul_def, one_def, zero_def]
    | H_basic i x =>
      rw [one_def, mul_of_of]
      ext
      simp only [mul_one, coe_of_apply, add_zero]
      split_ifs <;> rfl
    | H_plus x y hx hy =>
      rw [add_mul, hx, hy]

instance : Monoid (ReesAlgebra F) where
  one_mul := one_mul
  mul_one := mul_one

instance : CommMonoid (ReesAlgebra F) where
  mul_comm := by
   intro a b
   induction  a using induction_on with
   |H_zero =>
    simp [mul_def, zero_def]
   |H_basic va ma =>
    induction b using induction_on with
    |H_zero =>
     simp [mul_def, zero_def]
    |H_basic vb mb =>
     simp only [mul_of_of]
     ext
     simp only [mul_comm, coe_of_apply, add_comm]
     split_ifs <;> rfl
    |H_plus x y hx hy =>
     rw [mul_add, hx, hy, add_mul]
   |H_plus x y hx hy =>
    rw [mul_add, add_mul, hx, hy]

instance : MonoidWithZero (ReesAlgebra F) where
  zero_mul := by
   intro a
   simp [mul_def, zero_def]
  mul_zero := by
   intro a
   simp [mul_def, zero_def]

instance : CommSemiring (ReesAlgebra F) where
  __ := inferInstanceAs <| AddCommMonoid (ReesAlgebra F)
  left_distrib := left_distrib
  right_distrib := right_distrib
  mul_assoc := mul_assoc
  mul_comm := mul_comm
  one_mul := one_mul
  mul_one := mul_one
  zero_mul := zero_mul
  mul_zero := mul_zero

variable (F) in
@[simps]
def algebraMap' : A →+* ReesAlgebra F where
  toFun a := { val := .of _ 0 ⟨a, by simp⟩ }
  map_one' := rfl
  map_mul' a b := by
    ext : 3
    rw [DirectSum.coe_of_apply, mul_of_of, DirectSum.coe_of_apply]
    simp only [add_zero]
    split_ifs <;> rfl
  map_zero' := by
    ext
    rw [DirectSum.coe_of_apply]
    simp [zero_def]
  map_add' := by
    intro a b
    ext
    simp only [add_def, add_apply, Submodule.coe_add]
    erw [DirectSum.coe_of_apply, DirectSum.coe_of_apply, DirectSum.coe_of_apply]
    split_ifs <;> simp

instance : Algebra A (ReesAlgebra F) := RingHom.toAlgebra (algebraMap' F)

lemma algebraMap_eq : (algebraMap A (ReesAlgebra F)) = (algebraMap' F) := rfl

lemma algebraMap_apply_val (a : A) :
  (algebraMap A (ReesAlgebra F) a).val = .of _ 0 ⟨a, by simp⟩  := rfl

lemma algebraMap'_apply (a : A) :
  algebraMap' F a = { val := .of _ 0 ⟨a, by simp⟩ } := rfl
lemma smul_of (a : A) (v : ι →₀ ℕ) (x) :
    (a • { val := .of _ v x } : ReesAlgebra F) = { val := .of _ v (a • x) } := by
  ext : 1
  simp only [Algebra.smul_def, algebraMap_eq, algebraMap'_apply_val, Finsupp.prod_zero_index, mul_def,
    mul'_of_of]
  ext
  simp only [coe_of_apply, zero_add]
  split_ifs <;> rfl

lemma smul_of_val (a : A) (v : ι →₀ ℕ) (x) :
    (a • { val := .of _ v x } : ReesAlgebra F).val = .of _ v (a • x) := by
  simp [smul_of]

lemma smul_val (a : A) (x : ReesAlgebra F) :
    (a • x).val = a • x.val := by
  induction x using induction_on with
  |H_zero =>
    simp [Algebra.smul_def, algebraMap_apply, zero_def, mul_val]
  |H_basic i x =>
    simp only [smul_of_val]
    ext
    simp [DirectSum.coe_of_apply, smul_apply]
    split_ifs <;> simp
  | H_plus x y hx hy =>
    simp only [smul_add, add_val] at hx hy ⊢
    rw [hx, hy]

variable (F) in
@[simps]
def single (v : ι →₀ ℕ) : F^v →ₗ[A] ReesAlgebra F where
  toFun x := { val := .of _ v x }
  map_add' x y := by ext; simp [add_def]
  map_smul' x y := by simp [smul_of]

lemma single_def (v : ι →₀ ℕ) (x) :
  single F v x = { val := .of _ v x } := rfl

lemma single_eq (v v' : ι →₀ ℕ) (eq : v = v') (x : A) (hx : x ∈ F^v) :
    single F v ⟨x, hx⟩ = single F v' ⟨x, by subst eq; exact hx⟩ := by
  subst eq
  rfl

lemma single_eq_iff (v v' : ι →₀ ℕ) (x : A) (hx : x ∈ F^v) (hx' : x ∈ F^v') (x_ne_zero : x ≠ 0) :
    single F v ⟨x, hx⟩ = single F v' ⟨x, hx'⟩ ↔ v = v' := by
  constructor
  · intro eq
    rw [ReesAlgebra.ext_iff] at eq
    simp only [single_apply_val] at eq
    have eq' := congr($eq v)
    simp only [of_eq_same, of_apply, Subtype.ext_iff] at eq'
    split_ifs at eq' with h
    · exact h.symm
    simp only [ZeroMemClass.coe_zero] at eq'
    tauto
  · rintro rfl
    rfl

lemma single_eq' (v v' : ι →₀ ℕ) (eq : v = v')
    (x : A) (hx : x ∈ F^v)
    (y : A) (hy : y ∈ F^v')
    (eq' : x = y) :
    single F v ⟨x, hx⟩ = single F v' ⟨y, hy⟩ := by
  subst eq eq'
  rfl

@[simp]
lemma single_eq_zero (v : ι →₀ ℕ) (x) :
    single F v x = 0 ↔ x = 0 := by
  refine ⟨?_, by rintro rfl; simp⟩
  intro h
  simp only [zero_def, ReesAlgebra.ext_iff, single_apply_val, DirectSum.ext_iff] at h
  simpa using h v

lemma single_mul (v w : ι →₀ ℕ) (x y) :
    single F v x * single F w y = single F (v + w) ⟨x.1 * y.1, Ideal.mem_familyPow_add x.2 y.2⟩ := by
  ext : 1
  simp only [mul_val, single_def, mul'_of_of]

lemma single_prod {index : Type*} (v : index → (ι →₀ ℕ)) (x : ∀ j : index, F^(v j)) (s : Finset index) :
    ∏ j ∈ s, single F (v j) (x j) = single F (∑ j ∈ s, v j) ⟨∏ j ∈ s, x j, by
      classical
      rw [familyPow_sum]
      apply Ideal.prod_mem_prod
      simp⟩ := by
  induction s using Finset.cons_induction with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]; rfl
  | cons i s hi ih =>
    simp only [Finset.prod_cons, ih, single_mul]
    apply single_eq
    rw [Finset.sum_cons]

lemma single_npow (v : ι →₀ ℕ) (x) (n : ℕ) :
    single F v x ^ n = single F (n • v) ⟨x.1 ^ n, by
      rw [familyPow_nsmul]
      apply Ideal.pow_mem_pow
      exact x.2⟩ := by
  induction n with
  | zero =>
    ext : 1
    simp only [pow_zero, one_def, single_apply_val]
    ext w
    rw [DirectSum.coe_of_apply, DirectSum.coe_of_apply]
    simp_rw [zero_smul]
    split_ifs <;> rfl

  | succ n ih =>
    simp only [pow_succ, ih, single_mul, one_mul]
    apply single_eq
    rw [add_smul, one_smul]

end ReesAlgebra

end semiring

section ring

variable {A : Type*} [CommRing A]
variable {ι : Type*} (F : ι → Ideal A)

namespace ReesAlgebra

instance : Neg (ReesAlgebra F) where
  neg x := { val := -x.val }

lemma neg_def (x : ReesAlgebra F) : -x = { val := -x.val } := rfl

instance : Sub (ReesAlgebra F) where
  sub x y := { val := x.val - y.val }

lemma sub_def (x y : ReesAlgebra F) : x - y = { val := x.val - y.val } := rfl

instance : SMul ℤ (ReesAlgebra F) where
  smul n x := { val := n • x.val }

lemma zsmul_def (n : ℤ) (x : ReesAlgebra F) : n • x = { val := n • x.val } := rfl

variable [DecidableEq ι]
instance : AddCommGroup (ReesAlgebra F) where
  __ := inferInstanceAs <| AddCommMonoid (ReesAlgebra F)
  __ := (Function.Injective.addCommGroup (val (F := F)) (injective_val F) rfl
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) : AddCommGroup (ReesAlgebra F))

instance : CommRing (ReesAlgebra F) where
  __ := inferInstanceAs <| CommSemiring (ReesAlgebra F)
  __ := inferInstanceAs <| AddCommGroup (ReesAlgebra F)

lemma algebraMap_mem_nonZeroDivisors {a : A} (ha : a ∈ nonZeroDivisors A) :
    algebraMap A (ReesAlgebra F) a ∈ nonZeroDivisors (ReesAlgebra F) := by
  have key : ∀ x : ReesAlgebra F, algebraMap A (ReesAlgebra F) a * x = 0 → x = 0 := by
    intro x hx
    have hx' : (a • x : ReesAlgebra F) = 0 := by rw [Algebra.smul_def]; exact hx
    have hv : a • x.val = 0 := by rw [← smul_val, hx']; rfl
    apply injective_val
    rw [zero_def]
    ext v
    have h1 : a • (x.val v) = 0 := by
      rw [← DFinsupp.smul_apply, hv]; rfl
    have h2 : ((x.val v : A)) * a = 0 := by
      have := congrArg Subtype.val h1
      simpa [mul_comm] using this
    exact congrArg Subtype.val (Subtype.ext ((mem_nonZeroDivisors_iff.mp ha).2 _ h2))
  rw [mem_nonZeroDivisors_iff]
  exact ⟨key, fun x hx => key x (by rw [mul_comm]; exact hx)⟩

def grading (v : ι →₀ ℕ) : Submodule A (ReesAlgebra F) := LinearMap.range (single F v)

instance : SetLike.GradedOne (grading F) where
  one_mem := by
    simp only [grading, Finsupp.prod_zero_index, LinearMap.mem_range, Subtype.exists,
      Ideal.one_eq_top, Submodule.mem_top, exists_true_left]
    use 1
    simp [one_def, single]

instance : SetLike.GradedMul (grading F) where
  mul_mem := by
    rintro v w _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    simp only [single, LinearMap.coe_mk, AddHom.coe_mk, mul_of_of]
    exact ⟨⟨x * y, _⟩, rfl⟩

instance : SetLike.GradedMonoid (grading F) where

def decomposeAux : (⨁ (v : ι →₀ ℕ), F^v) →ₗ[A] ⨁ (v : ι →₀ ℕ), grading F v :=
  DirectSum.toModule _ _ _ fun v ↦
  { toFun x := .of _ v ⟨_, ⟨x, rfl⟩⟩
    map_add' x y := by
      simp only [single_def, map_add]
      ext w w'
      simp only [coe_of_apply, add_apply, Submodule.coe_add]
      split_ifs <;> simp
    map_smul' a x := by
      dsimp
      ext w w'
      rw [coe_of_apply, smul_apply]
      simp only [map_smul, SetLike.val_smul, SetLike.coe_eq_coe]
      split_ifs with h
      · subst h
        simp only [of_eq_same]
      · simp [zero_def, Algebra.smul_def, algebraMap_eq, algebraMap'_apply, mul_def, mul'_of_of,
          DirectSum.coe_of_apply, if_neg h] }

def decompose : ReesAlgebra F →ₗ[A] ⨁ (v : ι →₀ ℕ), grading F v :=
  decomposeAux F ∘ₗ
    { toFun := val
      map_add' _ _ := rfl
      map_smul' _ _ := by dsimp; rw [smul_val] }

@[simp]
lemma decompose_single (v : ι →₀ ℕ) (x) :
    decompose F (single F v x) = .of _ v ⟨_, ⟨x, rfl⟩⟩ := by
  simp only [decompose, decomposeAux, LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk,
    Function.comp_apply, single_apply_val]
  erw [toModule_lof]
  rfl

@[simp]
lemma decompose_val_of (v : ι →₀ ℕ) (x) :
    decompose F { val := .of _ v x } = .of _ v ⟨_, ⟨x, rfl⟩⟩ :=
  decompose_single ..

instance : GradedAlgebra (grading F) where
  decompose' := decompose F
  left_inv x := by
    induction x using induction_on with
    |H_zero => simp
    |H_basic v x => simp [single]
    |H_plus x y hx hy => simp [hx, hy]
  right_inv x := by
    induction x using DirectSum.induction_on with
    |zero => simp
    |of v x => rcases x with ⟨_, ⟨x, rfl⟩⟩; simp
    |add x y hx hy => simp [hx, hy]

lemma single_has_degree (v : ι →₀ ℕ) (x) :
    single F v x ∈ grading F v := by
  rw [grading, LinearMap.mem_range]
  use x

lemma eq_single_of_homogeneous (x : ReesAlgebra F) (hx : SetLike.IsHomogeneousElem (grading F) x) :
    ∃ v, x = single F v (x.val v) := by
  rcases hx with ⟨v, ⟨y, rfl⟩⟩
  use v
  simp

lemma single_familyPow {index : Type*}
    (n : index →₀ ℕ) (v : index → (ι →₀ ℕ)) (a : ∀ i : index, F^(v i)) :
    (fun i : index ↦ single F (v i) (a i))^n =
    single F (∑ i ∈ n.support, n i • v i)
      ⟨∏ i ∈ n.support, (a i)^(n i), n.induction (by simp) (by
        intro i n f _ _ ih
        change (f.prod fun j ↦ _) ∈ _ at ih
        change Finsupp.prod _ _ ∈ _
        rw [Finsupp.prod_add_index']
        · simp only [pow_zero, Finsupp.prod_single_index]
          change _ ∈ F ^ ((Finsupp.single i n + f).sum (fun i n ↦ n • (v i)) : ι →₀ ℕ)
          rw [Finsupp.sum_add_index']
          · rw [familyPow_add]
            apply Ideal.mul_mem_mul
            · simp only [zero_smul, Finsupp.sum_single_index, familyPow_nsmul]
              apply Ideal.pow_mem_pow
              exact (a i).2
            · exact ih
          · simp
          · simp [add_smul]
        · simp
        · simp [pow_add])⟩ := by
  refine n.induction ?_ ?_
  · simp only [familyPow_zero, Finsupp.support_zero, Finsupp.coe_zero, Pi.zero_apply,
    Finset.sum_empty, pow_zero, Finset.prod_const_one]
    rfl
  · intro j n f hj hn ih
    rw [familyPow_add, ih, familyPow_single', single_npow, single_mul]
    simp_rw [add_comm _ f, f.support_add_single hj hn, Finset.prod_cons]
    apply single_eq'

    · rw [add_comm _ f, f.support_add_single hj hn, Finset.sum_cons]
      simp only [Finsupp.mem_support_iff, ne_eq, Decidable.not_not] at hj
      simp only [Finsupp.coe_add, Pi.add_apply, hj, Finsupp.single_eq_same, zero_add, add_smul,
        add_right_inj]
      refine Finset.sum_congr rfl ?_
      intro k hk
      classical
      rw [Finsupp.single_apply, if_neg (by
        rintro rfl
        simp only [Finsupp.mem_support_iff, ne_eq] at hk
        exact hk hj), zero_smul, add_zero]
    simp only [Finsupp.mem_support_iff, ne_eq, Decidable.not_not] at hj
    simp only [Finsupp.coe_add, Pi.add_apply, hj, Finsupp.single_eq_same, zero_add]
    congr 1
    apply Finset.prod_congr rfl
    intro k hk
    simp only [Finsupp.mem_support_iff, ne_eq] at hk
    classical
    rw [Finsupp.single_apply, if_neg (by
      rintro rfl
      exact hk hj), add_zero]

@[simps]
def degreeZeroIso : A ≃+* (ReesAlgebra.grading F 0) where
  toFun a := ⟨.single F 0 ⟨a, by simp⟩, by simp [grading]⟩
  invFun a := a.1.val 0 |>.1
  left_inv a := by simp
  right_inv a := by
    ext v
    simp only [Subtype.coe_eta, single_apply_val, SetLike.coe_eq_coe]
    ext
    rw [DirectSum.coe_of_apply]
    obtain ⟨x, hx⟩ := a.2
    rw [← hx]
    simp only [ZeroMemClass.coe_zero, single_apply_val]
    rw [DirectSum.coe_of_apply]
    simp
  map_mul' x y := by
    ext v
    simp only [single_apply_val, SetLike.GradeZero.coe_mul, single_mul, SetLike.coe_eq_coe]
    ext
    simp only [coe_of_apply, zero_add]
    split_ifs <;> rfl
  map_add' x y := by
    ext v
    simp only [single_apply_val, coe_of_apply, AddMemClass.mk_add_mk, add_val, add_apply,
      Submodule.coe_add]
    split_ifs
    · rfl
    · simp

variable [(i : ι →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt ι))]
abbrev intGrading := (gradingOfInjection (grading F) (ρNatToInt ι))
instance : GradedAlgebra (intGrading F) :=
  gradingOfInjection_isGradedAlgebra (grading F) (ρNatToInt ι)

def degreeZeroIso' : A ≃+* (ReesAlgebra.intGrading F 0) :=
  degreeZeroIso F |>.trans
  (gradingOfInjection₀Iso (ReesAlgebra.grading F) (ρNatToInt ι)).symm

@[simp]
lemma degreeZeroIso'_apply (a : A) :
  degreeZeroIso' F a = ⟨.single F 0 ⟨a, by simp⟩, by
    delta intGrading gradingOfInjection
    rw [dif_pos ⟨0, by simp⟩]
    rw [Set.rangeSplitting_apply_zero (inj := ρNatToInt_inj) (hf := by simp)]
    exact single_has_degree F 0 _⟩ := rfl

lemma single_has_degree' (v : ι →₀ ℕ) (x) :
    single F v x ∈ intGrading F (ρNatToInt _ v) := by
  rw [intGrading, gradingOfInjection]
  rw [dif_pos (by simp)]
  erw [Set.rangeSplitting_apply_coe]
  exact single_has_degree F v x
  exact ρNatToInt_inj

lemma eq_single_of_homogeneous' (x : ReesAlgebra F) (hx : SetLike.IsHomogeneousElem (intGrading F) x) :
    ∃ v, x = single F v (x.val v) := by
  rcases hx with ⟨v, hv⟩
  simp only [intGrading, gradingOfInjection, Set.mem_range, ρNatToInt_apply] at hv
  split_ifs at hv with h
  · rcases h with ⟨v, rfl⟩
    rcases hv with ⟨⟨x, hx⟩, rfl⟩

    use v
    ext w
    simp only [single_apply_val, SetLike.coe_eq_coe]
    ext
    simp only [coe_of_apply]
    split_ifs with h h'
    · subst h'
      rw [coe_of_apply, if_pos h]
    · refine h' (h ▸ ?_) |>.elim
      rw [Set.rangeSplitting_apply_coe (inj := ρNatToInt_inj)]
    · refine h ?_ |>.elim
      rwa [Set.rangeSplitting_apply_coe (inj := ρNatToInt_inj)]
    · rfl

  simp only [Submodule.mem_bot] at hv
  subst hv
  use 0
  ext w
  simp [zero_def]

instance (S : HomogeneousSubmonoid (ReesAlgebra.intGrading F)) : Algebra A S.Potion :=
  RingHom.toAlgebra <| RingHom.comp (algebraMap _ _) (degreeZeroIso' F).toRingHom

lemma potion_algebraMap_mem_nonZeroDivisors
    (S : HomogeneousSubmonoid (ReesAlgebra.intGrading F)) {a : A} (ha : a ∈ nonZeroDivisors A) :
    algebraMap A S.Potion a ∈ nonZeroDivisors S.Potion :=
  S.potion_nonzero_divisor_of_nonzeroDivisor _ (degreeZeroIso' F a).2
    (algebraMap_mem_nonZeroDivisors F ha)

end ReesAlgebra

end ring

section functoriality

open Family

variable {A B : Type*} [CommSemiring A] [CommSemiring B]
variable {ι : Type*} [DecidableEq ι] (F : ι → Ideal A) (χ : A →+* B)

namespace ReesAlgebra

abbrev mapFamily : ι → Ideal B := fun i => Ideal.map χ (F i)

variable {F χ} in
lemma mem_mapFamily_familyPow {v : ι →₀ ℕ} {a : A} (ha : a ∈ F^v) :
    χ a ∈ (mapFamily F χ)^v := by
  classical
  have h : χ a ∈ Ideal.map χ (F^v) := Ideal.mem_map_of_mem _ ha
  rw [Ideal.familyPow_def, Finsupp.prod, Ideal.prod_map] at h
  simp_rw [Ideal.map_pow] at h
  rw [Ideal.familyPow_def, Finsupp.prod]
  exact h

def mapAux : (⨁ (v : ι →₀ ℕ), F^v) →+ ReesAlgebra (mapFamily F χ) :=
  DirectSum.toAddMonoid fun v =>
    { toFun := fun x => single (mapFamily F χ) v ⟨χ x.1, mem_mapFamily_familyPow x.2⟩
      map_zero' := by
        refine Eq.trans ?_ (single (mapFamily F χ) v).map_zero
        congr 1
        exact Subtype.ext (by simp)
      map_add' := fun x y => by
        refine Eq.trans ?_ ((single (mapFamily F χ) v).map_add _ _)
        congr 1
        exact Subtype.ext (by simp) }

@[simp]
lemma mapAux_of (v : ι →₀ ℕ) (x : F^v) :
    mapAux F χ (DirectSum.of _ v x) =
      single (mapFamily F χ) v ⟨χ x.1, mem_mapFamily_familyPow x.2⟩ :=
  DirectSum.toAddMonoid_of _ _ _

def map : ReesAlgebra F →+* ReesAlgebra (mapFamily F χ) where
  toFun x := mapAux F χ x.val
  map_zero' := by simp [zero_def]
  map_add' x y := by simp [add_def]
  map_one' := by
    rw [one_val]
    rw [mapAux_of]
    ext w
    simp only [single_apply_val, one_val]
    rw [DirectSum.coe_of_apply, DirectSum.coe_of_apply]
    split_ifs <;> simp
  map_mul' x y := by
    induction x using ReesAlgebra.induction_on with
    | H_zero => simp [mul_def, zero_def]
    | H_basic v a =>
      induction y using ReesAlgebra.induction_on with
      | H_zero => simp [mul_def, zero_def]
      | H_basic w b =>
        simp only [mul_of_of, mapAux_of]
        rw [single_mul]
        exact single_eq' _ _ rfl _ _ _ _ (map_mul χ _ _)
      | H_plus y z hy hz =>
        rw [mul_add]
        show mapAux F χ ((_ * y : ReesAlgebra F).val + (_ * z : ReesAlgebra F).val) =
          mapAux F χ _ * mapAux F χ (y.val + z.val)
        rw [map_add, map_add, hy, hz, mul_add]
    | H_plus x z hx hz =>
      rw [add_mul]
      show mapAux F χ ((x * y : ReesAlgebra F).val + (z * y : ReesAlgebra F).val) =
        mapAux F χ (x.val + z.val) * mapAux F χ y.val
      rw [map_add, map_add, hx, hz, add_mul]

@[simp]
lemma map_single (v : ι →₀ ℕ) (x : F^v) :
    map F χ (single F v x) = single (mapFamily F χ) v ⟨χ x.1, mem_mapFamily_familyPow x.2⟩ :=
  mapAux_of F χ v x

end ReesAlgebra

end functoriality

section gradedFunctoriality

open Family
open scoped Graded

variable {A B : Type*} [CommRing A] [CommRing B]
variable {ι : Type*} [DecidableEq ι] (F : ι → Ideal A) (χ : A →+* B)
variable [(i : ι →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt ι))]

namespace ReesAlgebra

def mapGraded : (intGrading F) →+* (intGrading (mapFamily F χ)) where
  __ := map F χ
  map_mem' := by
    intro d x hx
    delta intGrading gradingOfInjection at hx ⊢
    split_ifs at hx with hd
    · rw [dif_pos hd]
      obtain ⟨y, rfl⟩ := hx
      exact ⟨⟨χ y.1, mem_mapFamily_familyPow y.2⟩, (map_single F χ _ y).symm ▸ rfl⟩
    · rw [dif_neg hd]
      simp only [Submodule.mem_bot] at hx ⊢
      rw [hx]
      exact map_zero _

end ReesAlgebra

end gradedFunctoriality

section restrictBase

open Family
open scoped Graded

variable {B : Type*} [CommRing B]
variable {ι : Type*} [DecidableEq ι] (G : ι → Ideal B)
variable [(i : ι →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt ι))]

namespace ReesAlgebra

instance algebraOfBase (A : Type*) [CommRing A] [Algebra A B] : Algebra A (ReesAlgebra G) :=
  RingHom.toAlgebra ((algebraMap B (ReesAlgebra G)).comp (algebraMap A B))

instance (A : Type*) [CommRing A] [Algebra A B] : IsScalarTower A B (ReesAlgebra G) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

abbrev intGradingRestrict (A : Type*) [CommRing A] [Algebra A B] :
    (ι →₀ ℤ) → Submodule A (ReesAlgebra G) :=
  fun d => (intGrading G d).restrictScalars A

instance (A : Type*) [CommRing A] [Algebra A B] :
    SetLike.GradedMonoid (intGradingRestrict G A) where
  one_mem := SetLike.GradedOne.one_mem (A := intGrading G)
  mul_mem := @fun _ _ _ _ hx hy => SetLike.GradedMul.mul_mem (A := intGrading G) hx hy

instance (A : Type*) [CommRing A] [Algebra A B] :
    GradedAlgebra (intGradingRestrict G A) where
  decompose' := DirectSum.decompose (intGrading G)
  left_inv := DirectSum.Decomposition.left_inv (ℳ := intGrading G)
  right_inv := DirectSum.Decomposition.right_inv (ℳ := intGrading G)

end ReesAlgebra

end restrictBase

section functorialityOverBase

open Family
open scoped Graded

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable {ι : Type*} [DecidableEq ι] (F : ι → Ideal A)
variable [(i : ι →₀ ℤ) → Decidable (i ∈ Set.range (ρNatToInt ι))]

namespace ReesAlgebra

def mapGradedOverBase :
    (intGrading F) →+* (intGradingRestrict (mapFamily F (algebraMap A B)) A) where
  __ := map F (algebraMap A B)
  map_mem' := (mapGraded F (algebraMap A B)).map_mem'

@[simp]
lemma mapGradedOverBase_apply (x : ReesAlgebra F) :
    mapGradedOverBase F x = map F (algebraMap A B) x := rfl

end ReesAlgebra

end functorialityOverBase
