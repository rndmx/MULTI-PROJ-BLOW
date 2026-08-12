import Project.Proj.Over

import Mathlib.AlgebraicGeometry.Restrict

suppress_compilation

universe u
variable {ι : Type} {R₀ A : Type u}
variable [AddCommGroup ι] [CommRing R₀] [CommRing A] [Algebra R₀ A] {𝒜 : ι → Submodule R₀ A}
variable [DecidableEq ι] [GradedAlgebra 𝒜]

variable {τ : Type u} (f : τ → A)

open HomogeneousSubmonoid AlgebraicGeometry GoodPotionIngredient CategoryTheory

instance specOverSpecBase' (B : Type u) [CommRing B] [Algebra (𝒜 0) B] :
  Scheme.Over (Spec <| CommRingCat.of B) (SpecBase 𝒜) where
    hom := Spec.map <| CommRingCat.ofHom <| algebraMap _ _

abbrev sum_potion_finset {d : ι} (s : Finset τ)
    (deg : ∀ a ∈ s, f a ∈ 𝒜 d)
    (_ : ∀ (a : τ) (mem : a ∈ s), ElemIsRelevant (f a) ⟨d, deg _ mem⟩) :=
    Potion (HomogeneousSubmonoid.closure (𝒜 := 𝒜) {∑ a ∈ s, f a} <| by
      rintro - rfl
      refine ⟨d, sum_mem ?_⟩
      apply deg)

abbrev s_elem_finset  {d : ι} (s : Finset τ)
    (deg : ∀ a ∈ s, f a ∈ 𝒜 d)
    (rel : ∀ (a : τ) (mem : a ∈ s), ElemIsRelevant (f a) ⟨d, deg _ mem⟩)
    (i : τ) (hi : i ∈ s) :
    sum_potion_finset f s deg rel :=
  Quotient.mk''
    { deg := d
      num := ⟨f i, deg i hi⟩
      den := ⟨∑ i ∈ s, f i, sum_mem <| by aesop⟩
      den_mem := by
        simp only [mem_toSubmonoid_iff]
        exact Submonoid.mem_closure_singleton_self }

lemma bar_eq_of_le_bar (S T : HomogeneousSubmonoid 𝒜) (h1 : S ≤ T.bar) (h2 : T ≤ S.bar) :
    S.bar = T.bar :=
  le_antisymm (by simpa using HomogeneousSubmonoid.bar_mono _ _ h1)
    (by simpa using HomogeneousSubmonoid.bar_mono _ _ h2)

lemma bar_closure_singleton_mul {x y : A} (hx : SetLike.IsHomogeneousElem 𝒜 x)
    (hy : SetLike.IsHomogeneousElem 𝒜 y) :
    (HomogeneousSubmonoid.closure (𝒜 := 𝒜) {x}
        (by intro a ha; simp only [Set.mem_singleton_iff] at ha; rw [ha]; exact hx) *
      HomogeneousSubmonoid.closure (𝒜 := 𝒜) {y}
        (by intro a ha; simp only [Set.mem_singleton_iff] at ha; rw [ha]; exact hy)).bar =
    (HomogeneousSubmonoid.closure (𝒜 := 𝒜) {x * y} (by rintro - rfl; exact hx.mul hy)).bar := by
  set S : HomogeneousSubmonoid 𝒜 :=
    HomogeneousSubmonoid.closure {x}
      (by intro a ha; simp only [Set.mem_singleton_iff] at ha; rw [ha]; exact hx) with hS
  set T : HomogeneousSubmonoid 𝒜 :=
    HomogeneousSubmonoid.closure {y}
      (by intro a ha; simp only [Set.mem_singleton_iff] at ha; rw [ha]; exact hy) with hT
  show (S * T).bar = _
  refine bar_eq_of_le_bar _ _ ?_ ?_
  · have hx_mem : x ∈ (HomogeneousSubmonoid.closure {x * y}
        (by rintro - rfl; exact hx.mul hy)).bar :=
      ⟨hx, ⟨x * y, Submonoid.mem_closure_singleton_self, ⟨y, rfl⟩⟩⟩
    have hy_mem : y ∈ (HomogeneousSubmonoid.closure {x * y}
        (by rintro - rfl; exact hx.mul hy)).bar :=
      ⟨hy, ⟨x * y, Submonoid.mem_closure_singleton_self, ⟨x, by ring⟩⟩⟩
    intro z hz
    obtain ⟨p, hp, q, hq, rfl⟩ := HomogeneousSubmonoid.mem_mul_iff z |>.1 hz
    obtain ⟨m, rfl⟩ := Submonoid.mem_closure_singleton.1 hp
    obtain ⟨n, rfl⟩ := Submonoid.mem_closure_singleton.1 hq
    exact mul_mem (pow_mem hx_mem m) (pow_mem hy_mem n)
  · intro z hz
    obtain ⟨n, rfl⟩ := Submonoid.mem_closure_singleton.1 hz
    refine pow_mem (HomogeneousSubmonoid.self_le_bar _ ?_) n
    exact HomogeneousSubmonoid.mem_mul_iff _ |>.2
      ⟨x, Submonoid.mem_closure_singleton_self, y, Submonoid.mem_closure_singleton_self, rfl⟩

lemma bar_closure_singleton_mul3 {x y z : A} (hx : SetLike.IsHomogeneousElem 𝒜 x)
    (hy : SetLike.IsHomogeneousElem 𝒜 y) (hz : SetLike.IsHomogeneousElem 𝒜 z) :
    (HomogeneousSubmonoid.closure (𝒜 := 𝒜) {x}
        (by intro a ha; simp only [Set.mem_singleton_iff] at ha; rw [ha]; exact hx) *
      HomogeneousSubmonoid.closure (𝒜 := 𝒜) {y}
        (by intro a ha; simp only [Set.mem_singleton_iff] at ha; rw [ha]; exact hy) *
      HomogeneousSubmonoid.closure (𝒜 := 𝒜) {z}
        (by intro a ha; simp only [Set.mem_singleton_iff] at ha; rw [ha]; exact hz)).bar =
    (HomogeneousSubmonoid.closure (𝒜 := 𝒜) {x * y * z}
        (by rintro - rfl; exact (hx.mul hy).mul hz)).bar := by
  set S : HomogeneousSubmonoid 𝒜 :=
    HomogeneousSubmonoid.closure {x}
      (by intro a ha; simp only [Set.mem_singleton_iff] at ha; rw [ha]; exact hx) with hS
  set T : HomogeneousSubmonoid 𝒜 :=
    HomogeneousSubmonoid.closure {y}
      (by intro a ha; simp only [Set.mem_singleton_iff] at ha; rw [ha]; exact hy) with hT
  set U : HomogeneousSubmonoid 𝒜 :=
    HomogeneousSubmonoid.closure {z}
      (by intro a ha; simp only [Set.mem_singleton_iff] at ha; rw [ha]; exact hz) with hU
  show (S * T * U).bar = _
  refine bar_eq_of_le_bar _ _ ?_ ?_
  · have hx_mem : x ∈ (HomogeneousSubmonoid.closure {x * y * z}
        (by rintro - rfl; exact (hx.mul hy).mul hz)).bar :=
      ⟨hx, ⟨x * y * z, Submonoid.mem_closure_singleton_self, ⟨y * z, by ring⟩⟩⟩
    have hy_mem : y ∈ (HomogeneousSubmonoid.closure {x * y * z}
        (by rintro - rfl; exact (hx.mul hy).mul hz)).bar :=
      ⟨hy, ⟨x * y * z, Submonoid.mem_closure_singleton_self, ⟨x * z, by ring⟩⟩⟩
    have hz_mem : z ∈ (HomogeneousSubmonoid.closure {x * y * z}
        (by rintro - rfl; exact (hx.mul hy).mul hz)).bar :=
      ⟨hz, ⟨x * y * z, Submonoid.mem_closure_singleton_self, ⟨x * y, by ring⟩⟩⟩
    intro w hw
    obtain ⟨p, hp, q, hq, rfl⟩ := HomogeneousSubmonoid.mem_mul_iff w |>.1 hw
    obtain ⟨p', hp', q', hq', rfl⟩ := HomogeneousSubmonoid.mem_mul_iff p |>.1 hp
    obtain ⟨l, rfl⟩ := Submonoid.mem_closure_singleton.1 hp'
    obtain ⟨m, rfl⟩ := Submonoid.mem_closure_singleton.1 hq'
    obtain ⟨n, rfl⟩ := Submonoid.mem_closure_singleton.1 hq
    exact mul_mem (mul_mem (pow_mem hx_mem l) (pow_mem hy_mem m)) (pow_mem hz_mem n)
  · intro w hw
    obtain ⟨n, rfl⟩ := Submonoid.mem_closure_singleton.1 hw
    refine pow_mem (HomogeneousSubmonoid.self_le_bar _ ?_) n
    refine HomogeneousSubmonoid.mem_mul_iff _ |>.2
      ⟨x * y, HomogeneousSubmonoid.mem_mul_iff _ |>.2
        ⟨x, Submonoid.mem_closure_singleton_self, y, Submonoid.mem_closure_singleton_self, rfl⟩,
        z, Submonoid.mem_closure_singleton_self, ?_⟩
    ring

def s_lemma_finset {d : ι} (s : Finset τ)
    (deg : ∀ a ∈ s, f a ∈ 𝒜 d)
    (rel : ∀ (a : τ) (mem : a ∈ s), ElemIsRelevant (f a) ⟨d, deg _ mem⟩)
    (i : τ) (hi : i ∈ s) :
  Localization.Away (s_elem_finset f s deg rel i hi) ≃ₐ[𝒜 0]
  Potion (HomogeneousSubmonoid.closure (𝒜 := 𝒜) {f i * ∑ j ∈ s, f j} <| by
    rintro - rfl
    exact SetLike.IsHomogeneousElem.mul ⟨d, by aesop⟩ ⟨d, sum_mem <| by aesop⟩) := by
  classical

  have hsum : (∑ a ∈ s, f a) ∈ 𝒜 d := sum_mem (by aesop)
  have hfi : f i ∈ 𝒜 d := deg i hi
  set S : HomogeneousSubmonoid 𝒜 :=
    HomogeneousSubmonoid.closure {∑ a ∈ s, f a} (by rintro - rfl; exact ⟨d, hsum⟩) with hS
  set T : HomogeneousSubmonoid 𝒜 :=
    HomogeneousSubmonoid.closure {f i} (by rintro - rfl; exact ⟨d, hfi⟩) with hT

  let G : PotionGen S T :=
    { index := Unit
      elem := fun _ => f i
      elem_mem := fun _ => Submonoid.mem_closure_singleton_self
      gen := by
        simp only [hT, Set.range_const]
        rfl
      n := fun _ => 1
      s := fun _ => ∑ a ∈ s, f a
      s' := fun _ => 1
      s_mem_bar := fun _ => S.le_bar Submonoid.mem_closure_singleton_self
      s'_mem_bar := fun _ => one_mem _
      i := fun _ => d
      i' := fun _ => 0
      t_deg := fun _ => by simpa using hfi
      s_deg := fun _ => hsum
      s'_deg := fun _ => SetLike.GradedOne.one_mem }

  have key : (S.equivBarPotion.symm (HomogeneousLocalization.mk
      { deg := d
        num := ⟨(f i) ^ (1 : ℕ) * 1, by simpa using hfi⟩
        den := ⟨∑ a ∈ s, f a, hsum⟩
        den_mem := G.s_mem_bar () }) : S.Potion) = s_elem_finset f s deg rel i hi := by
    apply_fun S.equivBarPotion using S.equivBarPotion.injective
    rw [RingEquiv.apply_symm_apply, HomogeneousSubmonoid.equivBarPotion_apply]
    erw [HomogeneousSubmonoid.toBarPotion_mk]
    congr 1
    ext
    · rfl
    · simp
    · rfl
  have hgen : G.genSubmonoid = Submonoid.powers (s_elem_finset f s deg rel i hi) := by
    rw [Submonoid.powers_eq_closure]
    show Submonoid.closure _ = Submonoid.closure _
    congr 1
    ext x
    constructor
    · rintro ⟨-, rfl⟩
      exact key
    · rintro rfl
      exact ⟨(), key.symm⟩

  haveI : IsLocalization G.genSubmonoid
      (Localization.Away (s_elem_finset f s deg rel i hi)) := by
    rw [hgen]; infer_instance

  have hbar : (S * T).bar =
      (HomogeneousSubmonoid.closure (𝒜 := 𝒜) {f i * ∑ j ∈ s, f j} (by
        rintro - rfl
        exact SetLike.IsHomogeneousElem.mul ⟨d, hfi⟩ ⟨d, hsum⟩)).bar := by
    refine bar_eq_of_le_bar _ _ ?_ ?_
    ·
      have hsum_mem : (∑ j ∈ s, f j) ∈
          (HomogeneousSubmonoid.closure (𝒜 := 𝒜) {f i * ∑ j ∈ s, f j} (by
            rintro - rfl
            exact SetLike.IsHomogeneousElem.mul ⟨d, hfi⟩ ⟨d, hsum⟩)).bar :=
        ⟨⟨d, hsum⟩, ⟨f i * ∑ j ∈ s, f j, Submonoid.mem_closure_singleton_self,
          ⟨f i, by ring⟩⟩⟩
      have hfi_mem : f i ∈
          (HomogeneousSubmonoid.closure (𝒜 := 𝒜) {f i * ∑ j ∈ s, f j} (by
            rintro - rfl
            exact SetLike.IsHomogeneousElem.mul ⟨d, hfi⟩ ⟨d, hsum⟩)).bar :=
        ⟨⟨d, hfi⟩, ⟨f i * ∑ j ∈ s, f j, Submonoid.mem_closure_singleton_self,
          ⟨∑ j ∈ s, f j, rfl⟩⟩⟩
      intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := HomogeneousSubmonoid.mem_mul_iff x |>.1 hx
      obtain ⟨m, rfl⟩ := Submonoid.mem_closure_singleton.1 ha
      obtain ⟨n, rfl⟩ := Submonoid.mem_closure_singleton.1 hb
      exact mul_mem (pow_mem hsum_mem m) (pow_mem hfi_mem n)
    · intro x hx
      obtain ⟨n, rfl⟩ := Submonoid.mem_closure_singleton.1 hx
      refine pow_mem (HomogeneousSubmonoid.self_le_bar _ ?_) n
      exact HomogeneousSubmonoid.mem_mul_iff _ |>.2
        ⟨∑ j ∈ s, f j, Submonoid.mem_closure_singleton_self,
          f i, Submonoid.mem_closure_singleton_self, by ring⟩

  let E : Localization.Away (s_elem_finset f s deg rel i hi) ≃ₐ[S.Potion] (S * T).Potion :=
    (IsLocalization.algEquiv G.genSubmonoid
        (Localization.Away (s_elem_finset f s deg rel i hi))
        (Localization G.genSubmonoid)).trans (localizationAlgEquivPotion G)
  refine AlgEquiv.ofRingEquiv (f := E.toRingEquiv.trans
      ((S * T).equivBarPotion.trans (HomogeneousSubmonoid.potionEquiv hbar) |>.trans
        (HomogeneousSubmonoid.equivBarPotion _).symm)) ?_
  intro z
  show _ = _
  rw [RingEquiv.trans_apply, IsScalarTower.algebraMap_apply (𝒜 0) S.Potion
    (Localization.Away (s_elem_finset f s deg rel i hi)) z]
  rw [show E.toRingEquiv (algebraMap S.Potion
      (Localization.Away (s_elem_finset f s deg rel i hi))
      (algebraMap (𝒜 0) S.Potion z)) = algebraMap S.Potion (S * T).Potion
      (algebraMap (𝒜 0) S.Potion z) from E.commutes _]
  rw [HomogeneousSubmonoid.mul_potion_algebraMap_eq,
    HomogeneousSubmonoid.potionToMul_algebraMap]
  simp

def sigmaToSumMul {d : ι} (s : Finset τ)
    (deg : ∀ a ∈ s, f a ∈ 𝒜 d)
    (rel : ∀ (a : τ) (mem : a ∈ s), ElemIsRelevant (f a) ⟨d, deg _ mem⟩)
    (i : τ) (hi : i ∈ s) :
    sum_potion_finset f s deg rel →+*
    (HomogeneousSubmonoid.closure (𝒜 := 𝒜) {f i * ∑ j ∈ s, f j} (by
      rintro - rfl
      exact SetLike.IsHomogeneousElem.mul ⟨d, deg i hi⟩ ⟨d, sum_mem <| by aesop⟩)).Potion := by
  refine RingHom.comp (HomogeneousSubmonoid.equivBarPotion _).symm.toRingHom
    (RingHom.comp (HomogeneousSubmonoid.potionMapOfLE _ _ ?_)
      (HomogeneousSubmonoid.equivBarPotion _).toRingHom)
  refine le_trans (HomogeneousSubmonoid.bar_mono _ _ ?_)
    (le_of_eq (HomogeneousSubmonoid.bar_bar _))
  intro x hx
  obtain ⟨n, rfl⟩ := Submonoid.mem_closure_singleton.1 hx
  refine pow_mem ?_ n
  exact ⟨⟨d, sum_mem <| by aesop⟩, ⟨f i * ∑ j ∈ s, f j,
    Submonoid.mem_closure_singleton_self, ⟨f i, by ring⟩⟩⟩

abbrev s_elem_pow {d : ι} (s : Finset τ)
    (deg : ∀ a ∈ s, f a ∈ 𝒜 d)
    (rel : ∀ (a : τ) (mem : a ∈ s), ElemIsRelevant (f a) ⟨d, deg _ mem⟩)
    (m : ℕ) (c : A) (hc : c ∈ 𝒜 (m • d)) :
    sum_potion_finset f s deg rel :=
  Quotient.mk''
    { deg := m • d
      num := ⟨c, hc⟩
      den := ⟨(∑ i ∈ s, f i) ^ m, SetLike.pow_mem_graded m (sum_mem <| by aesop)⟩
      den_mem := by
        simp only [mem_toSubmonoid_iff]
        exact pow_mem Submonoid.mem_closure_singleton_self m }

def s_lemma_pow {d : ι} (s : Finset τ)
    (deg : ∀ a ∈ s, f a ∈ 𝒜 d)
    (rel : ∀ (a : τ) (mem : a ∈ s), ElemIsRelevant (f a) ⟨d, deg _ mem⟩)
    (m : ℕ) (c : A) (hc : c ∈ 𝒜 (m • d)) :
  Localization.Away (s_elem_pow f s deg rel m c hc) ≃ₐ[𝒜 0]
  Potion (HomogeneousSubmonoid.closure (𝒜 := 𝒜) {c * ∑ j ∈ s, f j} <| by
    rintro - rfl
    exact SetLike.IsHomogeneousElem.mul ⟨m • d, hc⟩ ⟨d, sum_mem <| by aesop⟩) := by
  classical
  have hsum : (∑ a ∈ s, f a) ∈ 𝒜 d := sum_mem (by aesop)
  have hpow : ((∑ a ∈ s, f a) ^ m) ∈ 𝒜 (m • d) := SetLike.pow_mem_graded m hsum
  set S : HomogeneousSubmonoid 𝒜 :=
    HomogeneousSubmonoid.closure {∑ a ∈ s, f a} (by rintro - rfl; exact ⟨d, hsum⟩) with hS
  set T : HomogeneousSubmonoid 𝒜 :=
    HomogeneousSubmonoid.closure {c} (by

      intro y hy
      simp only [Set.mem_singleton_iff] at hy
      rw [hy]
      exact ⟨m • d, hc⟩) with hT
  let G : PotionGen S T :=
    { index := Unit
      elem := fun _ => c
      elem_mem := fun _ => Submonoid.mem_closure_singleton_self
      gen := by
        simp only [hT, Set.range_const]
        rfl
      n := fun _ => 1
      s := fun _ => (∑ a ∈ s, f a) ^ m
      s' := fun _ => 1
      s_mem_bar := fun _ =>
        S.le_bar (pow_mem Submonoid.mem_closure_singleton_self m)
      s'_mem_bar := fun _ => one_mem _
      i := fun _ => m • d
      i' := fun _ => 0
      t_deg := fun _ => by simpa using hc
      s_deg := fun _ => hpow
      s'_deg := fun _ => SetLike.GradedOne.one_mem }
  have key : (S.equivBarPotion.symm (HomogeneousLocalization.mk
      { deg := m • d
        num := ⟨c ^ (1 : ℕ) * 1, by simpa using hc⟩
        den := ⟨(∑ a ∈ s, f a) ^ m, hpow⟩
        den_mem := G.s_mem_bar () }) : S.Potion) = s_elem_pow f s deg rel m c hc := by
    apply_fun S.equivBarPotion using S.equivBarPotion.injective
    rw [RingEquiv.apply_symm_apply, HomogeneousSubmonoid.equivBarPotion_apply]
    erw [HomogeneousSubmonoid.toBarPotion_mk]
    congr 1
    ext
    · rfl
    · simp
    · rfl
  have hgen : G.genSubmonoid = Submonoid.powers (s_elem_pow f s deg rel m c hc) := by
    rw [Submonoid.powers_eq_closure]
    show Submonoid.closure _ = Submonoid.closure _
    congr 1
    ext x
    constructor
    · rintro ⟨-, rfl⟩
      exact key
    · rintro rfl
      exact ⟨(), key.symm⟩
  haveI : IsLocalization G.genSubmonoid
      (Localization.Away (s_elem_pow f s deg rel m c hc)) := by
    rw [hgen]; infer_instance
  have hbar : (S * T).bar =
      (HomogeneousSubmonoid.closure (𝒜 := 𝒜) {c * ∑ j ∈ s, f j} (by
        rintro - rfl
        exact SetLike.IsHomogeneousElem.mul ⟨m • d, hc⟩ ⟨d, hsum⟩)).bar := by
    refine bar_eq_of_le_bar _ _ ?_ ?_
    · have hsum_mem : (∑ j ∈ s, f j) ∈
          (HomogeneousSubmonoid.closure (𝒜 := 𝒜) {c * ∑ j ∈ s, f j} (by
            rintro - rfl
            exact SetLike.IsHomogeneousElem.mul ⟨m • d, hc⟩ ⟨d, hsum⟩)).bar :=
        ⟨⟨d, hsum⟩, ⟨c * ∑ j ∈ s, f j, Submonoid.mem_closure_singleton_self,
          ⟨c, by ring⟩⟩⟩
      have hc_mem : c ∈
          (HomogeneousSubmonoid.closure (𝒜 := 𝒜) {c * ∑ j ∈ s, f j} (by
            rintro - rfl
            exact SetLike.IsHomogeneousElem.mul ⟨m • d, hc⟩ ⟨d, hsum⟩)).bar :=
        ⟨⟨m • d, hc⟩, ⟨c * ∑ j ∈ s, f j, Submonoid.mem_closure_singleton_self,
          ⟨∑ j ∈ s, f j, rfl⟩⟩⟩
      intro x hx
      obtain ⟨p, hp, q, hq, rfl⟩ := HomogeneousSubmonoid.mem_mul_iff x |>.1 hx
      obtain ⟨k, rfl⟩ := Submonoid.mem_closure_singleton.1 hp
      obtain ⟨n, rfl⟩ := Submonoid.mem_closure_singleton.1 hq
      exact mul_mem (pow_mem hsum_mem k) (pow_mem hc_mem n)
    · intro x hx
      obtain ⟨n, rfl⟩ := Submonoid.mem_closure_singleton.1 hx
      refine pow_mem (HomogeneousSubmonoid.self_le_bar _ ?_) n
      exact HomogeneousSubmonoid.mem_mul_iff _ |>.2
        ⟨∑ j ∈ s, f j, Submonoid.mem_closure_singleton_self,
          c, Submonoid.mem_closure_singleton_self, by ring⟩
  let E : Localization.Away (s_elem_pow f s deg rel m c hc) ≃ₐ[S.Potion] (S * T).Potion :=
    (IsLocalization.algEquiv G.genSubmonoid
        (Localization.Away (s_elem_pow f s deg rel m c hc))
        (Localization G.genSubmonoid)).trans (localizationAlgEquivPotion G)
  refine AlgEquiv.ofRingEquiv (f := E.toRingEquiv.trans
      ((S * T).equivBarPotion.trans (HomogeneousSubmonoid.potionEquiv hbar) |>.trans
        (HomogeneousSubmonoid.equivBarPotion _).symm)) ?_
  intro z
  show _ = _
  rw [RingEquiv.trans_apply, IsScalarTower.algebraMap_apply (𝒜 0) S.Potion
    (Localization.Away (s_elem_pow f s deg rel m c hc)) z]
  rw [show E.toRingEquiv (algebraMap S.Potion
      (Localization.Away (s_elem_pow f s deg rel m c hc))
      (algebraMap (𝒜 0) S.Potion z)) = algebraMap S.Potion (S * T).Potion
      (algebraMap (𝒜 0) S.Potion z) from E.commutes _]
  rw [HomogeneousSubmonoid.mul_potion_algebraMap_eq,
    HomogeneousSubmonoid.potionToMul_algebraMap]
  simp

def sumPotionGen {d : ι} (s : Finset τ)
    (deg : ∀ a ∈ s, f a ∈ 𝒜 d)
    (m : ℕ) (c : A) (hc : c ∈ 𝒜 (m • d)) :
    PotionGen
      (HomogeneousSubmonoid.closure (𝒜 := 𝒜) {∑ a ∈ s, f a}
        (by rintro - rfl; exact ⟨d, sum_mem (by aesop)⟩))
      (HomogeneousSubmonoid.closure (𝒜 := 𝒜) {c}
        (by intro y hy; simp only [Set.mem_singleton_iff] at hy; rw [hy]; exact ⟨m • d, hc⟩)) where
  index := Unit
  elem _ := c
  elem_mem _ := Submonoid.mem_closure_singleton_self
  gen := by simp only [Set.range_const]; rfl
  n _ := 1
  s _ := (∑ a ∈ s, f a) ^ m
  s' _ := 1
  s_mem_bar _ :=
    HomogeneousSubmonoid.le_bar _ (pow_mem Submonoid.mem_closure_singleton_self m)
  s'_mem_bar _ := one_mem _
  i _ := m • d
  i' _ := 0
  t_deg _ := by simpa using hc
  s_deg _ := SetLike.pow_mem_graded m (sum_mem (by aesop))
  s'_deg _ := SetLike.GradedOne.one_mem

lemma sumPotionGen_genSubmonoid {d : ι} (s : Finset τ)
    (deg : ∀ a ∈ s, f a ∈ 𝒜 d)
    (rel : ∀ (a : τ) (mem : a ∈ s), ElemIsRelevant (f a) ⟨d, deg _ mem⟩)
    (m : ℕ) (c : A) (hc : c ∈ 𝒜 (m • d)) :
    (sumPotionGen f s deg m c hc).genSubmonoid =
      Submonoid.powers (s_elem_pow f s deg rel m c hc) := by
  classical
  have hsum : (∑ a ∈ s, f a) ∈ 𝒜 d := sum_mem (by aesop)
  have hpow : ((∑ a ∈ s, f a) ^ m) ∈ 𝒜 (m • d) := SetLike.pow_mem_graded m hsum
  set S : HomogeneousSubmonoid 𝒜 :=
    HomogeneousSubmonoid.closure {∑ a ∈ s, f a} (by rintro - rfl; exact ⟨d, hsum⟩) with hS
  have key : (S.equivBarPotion.symm (HomogeneousLocalization.mk
      { deg := m • d
        num := ⟨c ^ (1 : ℕ) * 1, by simpa using hc⟩
        den := ⟨(∑ a ∈ s, f a) ^ m, hpow⟩
        den_mem := (sumPotionGen f s deg m c hc).s_mem_bar () }) : S.Potion) =
      s_elem_pow f s deg rel m c hc := by
    apply_fun S.equivBarPotion using S.equivBarPotion.injective
    rw [RingEquiv.apply_symm_apply, HomogeneousSubmonoid.equivBarPotion_apply]
    erw [HomogeneousSubmonoid.toBarPotion_mk]
    congr 1
    ext
    · rfl
    · simp
    · rfl
  rw [Submonoid.powers_eq_closure]
  show Submonoid.closure _ = Submonoid.closure _
  congr 1
  ext x
  constructor
  · rintro ⟨-, rfl⟩
    exact key
  · rintro rfl
    exact ⟨(), key.symm⟩

lemma isLocalization_sumPotionGen {d : ι} (s : Finset τ)
    (deg : ∀ a ∈ s, f a ∈ 𝒜 d)
    (rel : ∀ (a : τ) (mem : a ∈ s), ElemIsRelevant (f a) ⟨d, deg _ mem⟩)
    (m : ℕ) (c : A) (hc : c ∈ 𝒜 (m • d)) :
    IsLocalization (sumPotionGen f s deg m c hc).genSubmonoid
      (Localization.Away (s_elem_pow f s deg rel m c hc)) := by
  rw [sumPotionGen_genSubmonoid f s deg rel m c hc]
  infer_instance

noncomputable def sumMagicE {d : ι} (s : Finset τ)
    (deg : ∀ a ∈ s, f a ∈ 𝒜 d)
    (rel : ∀ (a : τ) (mem : a ∈ s), ElemIsRelevant (f a) ⟨d, deg _ mem⟩)
    (m : ℕ) (c : A) (hc : c ∈ 𝒜 (m • d)) :=
  haveI := isLocalization_sumPotionGen f s deg rel m c hc
  (IsLocalization.algEquiv (sumPotionGen f s deg m c hc).genSubmonoid
      (Localization.Away (s_elem_pow f s deg rel m c hc))
      (Localization (sumPotionGen f s deg m c hc).genSubmonoid)).trans
    (localizationAlgEquivPotion (sumPotionGen f s deg m c hc))

lemma sumMagicE_algebraMap {d : ι} (s : Finset τ)
    (deg : ∀ a ∈ s, f a ∈ 𝒜 d)
    (rel : ∀ (a : τ) (mem : a ∈ s), ElemIsRelevant (f a) ⟨d, deg _ mem⟩)
    (m : ℕ) (c : A) (hc : c ∈ 𝒜 (m • d)) (r : sum_potion_finset f s deg rel) :
    sumMagicE f s deg rel m c hc (algebraMap _ _ r) =
      HomogeneousSubmonoid.potionToMul _ _ r :=
  (sumMagicE f s deg rel m c hc).commutes r

noncomputable def sumMagicTail {d : ι} (s : Finset τ)
    (deg : ∀ a ∈ s, f a ∈ 𝒜 d)
    (m : ℕ) (c : A) (hc : c ∈ 𝒜 (m • d)) :
    ((HomogeneousSubmonoid.closure (𝒜 := 𝒜) {∑ a ∈ s, f a}
        (by intro y hy; simp only [Set.mem_singleton_iff] at hy; rw [hy]
            exact ⟨d, sum_mem (by aesop)⟩)) *
      (HomogeneousSubmonoid.closure (𝒜 := 𝒜) {c}
        (by intro y hy; simp only [Set.mem_singleton_iff] at hy; rw [hy]
            exact ⟨m • d, hc⟩))).Potion ≃+*
    (HomogeneousSubmonoid.closure (𝒜 := 𝒜) {c * ∑ j ∈ s, f j}
      (by rintro - rfl
          exact SetLike.IsHomogeneousElem.mul ⟨m • d, hc⟩ ⟨d, sum_mem (by aesop)⟩)).Potion :=
  (HomogeneousSubmonoid.potionEquiv (mul_comm _ _)).trans
    ((HomogeneousSubmonoid.equivBarPotion _).trans
      ((HomogeneousSubmonoid.potionEquiv
          (bar_closure_singleton_mul (𝒜 := 𝒜)
            (⟨m • d, hc⟩ : SetLike.IsHomogeneousElem 𝒜 c)
            (⟨d, sum_mem (by aesop)⟩ :
              SetLike.IsHomogeneousElem 𝒜 (∑ a ∈ s, f a)))).trans
        (HomogeneousSubmonoid.equivBarPotion _).symm))

def sigmaToPowMul {d : ι} (s : Finset τ)
    (deg : ∀ a ∈ s, f a ∈ 𝒜 d)
    (rel : ∀ (a : τ) (mem : a ∈ s), ElemIsRelevant (f a) ⟨d, deg _ mem⟩)
    (m : ℕ) (c : A) (hc : c ∈ 𝒜 (m • d)) :
    sum_potion_finset f s deg rel →+*
    (HomogeneousSubmonoid.closure (𝒜 := 𝒜) {c * ∑ j ∈ s, f j}
      (by rintro - rfl
          exact SetLike.IsHomogeneousElem.mul ⟨m • d, hc⟩ ⟨d, sum_mem (by aesop)⟩)).Potion := by
  refine RingHom.comp (HomogeneousSubmonoid.equivBarPotion _).symm.toRingHom
    (RingHom.comp (HomogeneousSubmonoid.potionMapOfLE _ _ ?_)
      (HomogeneousSubmonoid.equivBarPotion _).toRingHom)
  refine le_trans (HomogeneousSubmonoid.bar_mono _ _ ?_)
    (le_of_eq (HomogeneousSubmonoid.bar_bar _))
  intro x hx
  obtain ⟨n, rfl⟩ := Submonoid.mem_closure_singleton.1 hx
  refine pow_mem ?_ n
  exact ⟨⟨d, sum_mem (by aesop)⟩, ⟨c * ∑ j ∈ s, f j,
    Submonoid.mem_closure_singleton_self, ⟨c, by ring⟩⟩⟩

lemma sumMagicTail_potionToMul {d : ι} (s : Finset τ)
    (deg : ∀ a ∈ s, f a ∈ 𝒜 d)
    (rel : ∀ (a : τ) (mem : a ∈ s), ElemIsRelevant (f a) ⟨d, deg _ mem⟩)
    (m : ℕ) (c : A) (hc : c ∈ 𝒜 (m • d)) (r : sum_potion_finset f s deg rel) :
    sumMagicTail f s deg m c hc (HomogeneousSubmonoid.potionToMul _ _ r) =
      sigmaToPowMul f s deg rel m c hc r := by
  induction r using Quotient.inductionOn' with | h r =>
  unfold sumMagicTail sigmaToPowMul
  simp only [RingEquiv.trans_apply, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingHom.coe_coe, HomogeneousSubmonoid.potionToMul_mk',
    HomogeneousSubmonoid.potionMapOfLE_mk', HomogeneousSubmonoid.potionEquiv_mk,
    HomogeneousSubmonoid.equivBarPotion_apply, HomogeneousSubmonoid.toBarPotion_mk,
    RingEquiv.apply_symm_apply]

lemma sumMagic_algebraMap {d : ι} (s : Finset τ)
    (deg : ∀ a ∈ s, f a ∈ 𝒜 d)
    (rel : ∀ (a : τ) (mem : a ∈ s), ElemIsRelevant (f a) ⟨d, deg _ mem⟩)
    (m : ℕ) (c : A) (hc : c ∈ 𝒜 (m • d)) (r : sum_potion_finset f s deg rel) :
    sumMagicTail f s deg m c hc (sumMagicE f s deg rel m c hc (algebraMap _ _ r)) =
      sigmaToPowMul f s deg rel m c hc r := by
  rw [sumMagicE_algebraMap, sumMagicTail_potionToMul]

def sumPotionGen' {d : ι} (s : Finset τ)
    (deg : ∀ a ∈ s, f a ∈ 𝒜 d)
    (c : A) (hc : c ∈ 𝒜 d) :
    PotionGen
      (HomogeneousSubmonoid.closure (𝒜 := 𝒜) {∑ a ∈ s, f a}
        (by rintro - rfl; exact ⟨d, sum_mem (by aesop)⟩))
      (HomogeneousSubmonoid.closure (𝒜 := 𝒜) {c}
        (by intro y hy; simp only [Set.mem_singleton_iff] at hy; rw [hy]; exact ⟨d, hc⟩)) where
  index := Unit
  elem _ := c
  elem_mem _ := Submonoid.mem_closure_singleton_self
  gen := by simp only [Set.range_const]; rfl
  n _ := 1
  s _ := ∑ a ∈ s, f a
  s' _ := 1
  s_mem_bar _ := HomogeneousSubmonoid.le_bar _ Submonoid.mem_closure_singleton_self
  s'_mem_bar _ := one_mem _
  i _ := d
  i' _ := 0
  t_deg _ := by simpa using hc
  s_deg _ := sum_mem (by aesop)
  s'_deg _ := SetLike.GradedOne.one_mem

lemma sumPotionGen'_genSubmonoid {d : ι} (s : Finset τ)
    (deg : ∀ a ∈ s, f a ∈ 𝒜 d)
    (rel : ∀ (a : τ) (mem : a ∈ s), ElemIsRelevant (f a) ⟨d, deg _ mem⟩)
    (i : τ) (hi : i ∈ s) :
    (sumPotionGen' f s deg (f i) (deg i hi)).genSubmonoid =
      Submonoid.powers (s_elem_finset f s deg rel i hi) := by
  classical
  have hsum : (∑ a ∈ s, f a) ∈ 𝒜 d := sum_mem (by aesop)
  set S : HomogeneousSubmonoid 𝒜 :=
    HomogeneousSubmonoid.closure {∑ a ∈ s, f a} (by rintro - rfl; exact ⟨d, hsum⟩) with hS
  have key : (S.equivBarPotion.symm (HomogeneousLocalization.mk
      { deg := d
        num := ⟨(f i) ^ (1 : ℕ) * 1, by simpa using deg i hi⟩
        den := ⟨∑ a ∈ s, f a, hsum⟩
        den_mem := (sumPotionGen' f s deg (f i) (deg i hi)).s_mem_bar () }) : S.Potion) =
      s_elem_finset f s deg rel i hi := by
    apply_fun S.equivBarPotion using S.equivBarPotion.injective
    rw [RingEquiv.apply_symm_apply, HomogeneousSubmonoid.equivBarPotion_apply]
    erw [HomogeneousSubmonoid.toBarPotion_mk]
    congr 1
    ext
    · rfl
    · simp
    · rfl
  rw [Submonoid.powers_eq_closure]
  show Submonoid.closure _ = Submonoid.closure _
  congr 1
  ext x
  constructor
  · rintro ⟨-, rfl⟩
    exact key
  · rintro rfl
    exact ⟨(), key.symm⟩

lemma isLocalization_sumPotionGen' {d : ι} (s : Finset τ)
    (deg : ∀ a ∈ s, f a ∈ 𝒜 d)
    (rel : ∀ (a : τ) (mem : a ∈ s), ElemIsRelevant (f a) ⟨d, deg _ mem⟩)
    (i : τ) (hi : i ∈ s) :
    IsLocalization (sumPotionGen' f s deg (f i) (deg i hi)).genSubmonoid
      (Localization.Away (s_elem_finset f s deg rel i hi)) := by
  rw [sumPotionGen'_genSubmonoid f s deg rel i hi]
  infer_instance

noncomputable def sumMagicE' {d : ι} (s : Finset τ)
    (deg : ∀ a ∈ s, f a ∈ 𝒜 d)
    (rel : ∀ (a : τ) (mem : a ∈ s), ElemIsRelevant (f a) ⟨d, deg _ mem⟩)
    (i : τ) (hi : i ∈ s) :=
  haveI := isLocalization_sumPotionGen' f s deg rel i hi
  (IsLocalization.algEquiv (sumPotionGen' f s deg (f i) (deg i hi)).genSubmonoid
      (Localization.Away (s_elem_finset f s deg rel i hi))
      (Localization (sumPotionGen' f s deg (f i) (deg i hi)).genSubmonoid)).trans
    (localizationAlgEquivPotion (sumPotionGen' f s deg (f i) (deg i hi)))

lemma sumMagicE'_algebraMap {d : ι} (s : Finset τ)
    (deg : ∀ a ∈ s, f a ∈ 𝒜 d)
    (rel : ∀ (a : τ) (mem : a ∈ s), ElemIsRelevant (f a) ⟨d, deg _ mem⟩)
    (i : τ) (hi : i ∈ s) (r : sum_potion_finset f s deg rel) :
    sumMagicE' f s deg rel i hi (algebraMap _ _ r) =
      HomogeneousSubmonoid.potionToMul _ _ r :=
  (sumMagicE' f s deg rel i hi).commutes r

lemma s_elem_finset_mul {d : ι} (s : Finset τ)
    (deg : ∀ a ∈ s, f a ∈ 𝒜 d)
    (rel : ∀ (a : τ) (mem : a ∈ s), ElemIsRelevant (f a) ⟨d, deg _ mem⟩)
    (a b : τ) (ha : a ∈ s) (hb : b ∈ s) :
    s_elem_finset f s deg rel a ha * s_elem_finset f s deg rel b hb =
      s_elem_pow f s deg rel 2 (f a * f b)
        (by rw [two_smul]; exact SetLike.mul_mem_graded (deg a ha) (deg b hb)) := by
  show HomogeneousLocalization.mk _ * HomogeneousLocalization.mk _ =
    HomogeneousLocalization.mk _
  rw [← HomogeneousLocalization.mk_mul]
  congr 1
  ext
  · exact (two_smul ℕ d).symm
  · rfl
  · exact (sq _).symm

section AwayTensor

open scoped TensorProduct

lemma isLocalization_away_tensor {R : Type*} [CommRing R] (a b : R) :
    IsLocalization.Away (a * b) (Localization.Away a ⊗[R] Localization.Away b) :=
  IsLocalization.Away.mul' (Localization.Away a) _ a b

noncomputable def transportAway {R : Type*} [CommRing R] {x y : R} (h : x = y) :
    Localization.Away x ≃ₐ[R] Localization.Away y := by
  subst h; exact AlgEquiv.refl

@[simp]
lemma transportAway_algebraMap {R : Type*} [CommRing R] {x y : R} (h : x = y) (r : R) :
    transportAway h (algebraMap R (Localization.Away x) r) =
      algebraMap R (Localization.Away y) r :=
  (transportAway h).commutes r

noncomputable def awayTensorAwayEquiv {R : Type*} [CommRing R] (a b : R) :
    Localization.Away a ⊗[R] Localization.Away b ≃ₐ[R] Localization.Away (a * b) :=
  haveI := isLocalization_away_tensor a b
  IsLocalization.algEquiv (Submonoid.powers (a * b)) _ _

end AwayTensor

lemma sum_s_elem_finset_eq_one {d : ι} (s : Finset τ)
    (deg : ∀ a ∈ s, f a ∈ 𝒜 d)
    (rel : ∀ (a : τ) (mem : a ∈ s), ElemIsRelevant (f a) ⟨d, deg _ mem⟩) :
    ∑ i ∈ s.attach, s_elem_finset f s deg rel i.1 i.2 = 1 := by
  classical
  have hden : (∑ i ∈ s, f i) ∈
      (HomogeneousSubmonoid.closure (𝒜 := 𝒜) {∑ a ∈ s, f a} (by
        rintro - rfl
        exact ⟨d, sum_mem (by aesop)⟩)).toSubmonoid :=
    Submonoid.mem_closure_singleton_self
  have key : ∀ t : Finset {x // x ∈ s},
      (∑ i ∈ t, s_elem_finset f s deg rel i.1 i.2).val =
        Localization.mk (∑ i ∈ t, f i.1) ⟨∑ i ∈ s, f i, hden⟩ := by
    intro t
    induction t using Finset.induction_on with
    | empty => simpa using (Localization.mk_zero _).symm
    | insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, HomogeneousLocalization.val_add, ih]
      rw [show (s_elem_finset f s deg rel a.1 a.2).val =
        Localization.mk (f a.1) ⟨∑ i ∈ s, f i, hden⟩ from rfl]
      rw [Localization.add_mk_self]
  ext
  rw [key, Finset.sum_attach, HomogeneousLocalization.val_one]
  exact Localization.mk_self ⟨_, hden⟩

lemma span_s_elem_finset_eq_top {d : ι} (s : Finset τ)
    (deg : ∀ a ∈ s, f a ∈ 𝒜 d)
    (rel : ∀ (a : τ) (mem : a ∈ s), ElemIsRelevant (f a) ⟨d, deg _ mem⟩) :
    Ideal.span (Set.range (fun i : {x // x ∈ s} => s_elem_finset f s deg rel i.1 i.2)) = ⊤ := by
  rw [Ideal.eq_top_iff_one, ← sum_s_elem_finset_eq_one f s deg rel]
  exact Ideal.sum_mem _ fun i _ => Ideal.subset_span ⟨i, rfl⟩

def potionToSumMul {d : ι} (s : Finset τ)
    (deg : ∀ a ∈ s, f a ∈ 𝒜 d)
    (rel : ∀ (a : τ) (mem : a ∈ s), ElemIsRelevant (f a) ⟨d, deg _ mem⟩)
    (i : τ) (hi : i ∈ s) :
    (HomogeneousSubmonoid.closure (𝒜 := 𝒜) {f i} (by
      rintro - rfl
      exact ⟨d, deg i hi⟩)).Potion →+*
    (HomogeneousSubmonoid.closure (𝒜 := 𝒜) {f i * ∑ j ∈ s, f j} (by
      rintro - rfl
      exact SetLike.IsHomogeneousElem.mul ⟨d, deg i hi⟩ ⟨d, sum_mem <| by aesop⟩)).Potion := by
  refine RingHom.comp (HomogeneousSubmonoid.equivBarPotion _).symm.toRingHom
    (RingHom.comp (HomogeneousSubmonoid.potionMapOfLE _ _ ?_)
      (HomogeneousSubmonoid.equivBarPotion _).toRingHom)
  refine le_trans (HomogeneousSubmonoid.bar_mono _ _ ?_)
    (le_of_eq (HomogeneousSubmonoid.bar_bar _))
  intro x hx
  obtain ⟨n, rfl⟩ := Submonoid.mem_closure_singleton.1 hx
  refine pow_mem ?_ n
  exact ⟨⟨d, deg i hi⟩, ⟨f i * ∑ j ∈ s, f j,
    Submonoid.mem_closure_singleton_self, ⟨∑ j ∈ s, f j, rfl⟩⟩⟩

def overlapToM {d : ι} (s : Finset τ)
    (deg : ∀ a ∈ s, f a ∈ 𝒜 d)
    (rel : ∀ (a : τ) (mem : a ∈ s), ElemIsRelevant (f a) ⟨d, deg _ mem⟩)
    (a b : τ) (ha : a ∈ s) (hb : b ∈ s) :
    ((HomogeneousSubmonoid.closure (𝒜 := 𝒜) {f a} (by
        intro w hw; simp only [Set.mem_singleton_iff] at hw; rw [hw]; exact ⟨d, deg a ha⟩) *
      HomogeneousSubmonoid.closure (𝒜 := 𝒜) {f b} (by
        intro w hw; simp only [Set.mem_singleton_iff] at hw; rw [hw]; exact ⟨d, deg b hb⟩))).Potion →+*
    (HomogeneousSubmonoid.closure (𝒜 := 𝒜) {f a * f b * ∑ j ∈ s, f j} (by
      rintro - rfl
      exact SetLike.IsHomogeneousElem.mul (SetLike.IsHomogeneousElem.mul ⟨d, deg a ha⟩
        ⟨d, deg b hb⟩) ⟨d, sum_mem <| by aesop⟩)).Potion :=
  RingHom.comp (HomogeneousSubmonoid.equivBarPotion _).symm.toRingHom
    (RingHom.comp (HomogeneousSubmonoid.potionEquiv
        (bar_closure_singleton_mul3 (⟨d, deg a ha⟩ : SetLike.IsHomogeneousElem 𝒜 (f a))
          (⟨d, deg b hb⟩ : SetLike.IsHomogeneousElem 𝒜 (f b))
          (⟨d, sum_mem <| by aesop⟩ : SetLike.IsHomogeneousElem 𝒜 (∑ j ∈ s, f j)))).toRingHom
      (RingHom.comp (HomogeneousSubmonoid.equivBarPotion _).toRingHom
        (HomogeneousSubmonoid.potionToMul _
          (HomogeneousSubmonoid.closure (𝒜 := 𝒜) {∑ j ∈ s, f j}
            (by rintro - rfl; exact ⟨d, sum_mem <| by aesop⟩)))))

def potionToSumMul2 {d : ι} (s : Finset τ)
    (deg : ∀ a ∈ s, f a ∈ 𝒜 d)
    (rel : ∀ (a : τ) (mem : a ∈ s), ElemIsRelevant (f a) ⟨d, deg _ mem⟩)
    (a b : τ) (ha : a ∈ s) (hb : b ∈ s) :
    (HomogeneousSubmonoid.closure (𝒜 := 𝒜) {f a * ∑ j ∈ s, f j} (by
      rintro - rfl
      exact SetLike.IsHomogeneousElem.mul ⟨d, deg a ha⟩ ⟨d, sum_mem <| by aesop⟩)).Potion →+*
    (HomogeneousSubmonoid.closure (𝒜 := 𝒜) {f a * f b * ∑ j ∈ s, f j} (by
      rintro - rfl
      exact SetLike.IsHomogeneousElem.mul (SetLike.IsHomogeneousElem.mul ⟨d, deg a ha⟩
        ⟨d, deg b hb⟩) ⟨d, sum_mem <| by aesop⟩)).Potion := by
  refine RingHom.comp (HomogeneousSubmonoid.equivBarPotion _).symm.toRingHom
    (RingHom.comp (HomogeneousSubmonoid.potionMapOfLE _ _ ?_)
      (HomogeneousSubmonoid.equivBarPotion _).toRingHom)
  refine le_trans (HomogeneousSubmonoid.bar_mono _ _ ?_)
    (le_of_eq (HomogeneousSubmonoid.bar_bar _))
  intro x hx
  obtain ⟨n, rfl⟩ := Submonoid.mem_closure_singleton.1 hx
  refine pow_mem ?_ n
  exact ⟨SetLike.IsHomogeneousElem.mul ⟨d, deg a ha⟩ ⟨d, sum_mem <| by aesop⟩,
    ⟨f a * f b * ∑ j ∈ s, f j, Submonoid.mem_closure_singleton_self, ⟨f b, by ring⟩⟩⟩

lemma overlapToM_potionToMul_eq {d : ι} (s : Finset τ)
    (deg : ∀ a ∈ s, f a ∈ 𝒜 d)
    (rel : ∀ (a : τ) (mem : a ∈ s), ElemIsRelevant (f a) ⟨d, deg _ mem⟩)
    (a b : τ) (ha : a ∈ s) (hb : b ∈ s)
    (z : (HomogeneousSubmonoid.closure (𝒜 := 𝒜) {f a} (by
        intro w hw; simp only [Set.mem_singleton_iff] at hw; rw [hw]; exact ⟨d, deg a ha⟩)).Potion) :
    overlapToM f s deg rel a b ha hb
        (HomogeneousSubmonoid.potionToMul _
          (HomogeneousSubmonoid.closure (𝒜 := 𝒜) {f b} (by
            intro w hw; simp only [Set.mem_singleton_iff] at hw; rw [hw]; exact ⟨d, deg b hb⟩)) z) =
      potionToSumMul2 f s deg rel a b ha hb (potionToSumMul f s deg rel a ha z) := by
  induction z using Quotient.inductionOn' with | h z =>
  unfold overlapToM potionToSumMul2 potionToSumMul
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    HomogeneousSubmonoid.potionToMul_mk', HomogeneousSubmonoid.potionMapOfLE_mk',
    HomogeneousSubmonoid.equivBarPotion_apply, HomogeneousSubmonoid.toBarPotion_mk,
    HomogeneousSubmonoid.potionEquiv_mk, RingEquiv.apply_symm_apply]

def sigmaToM {d : ι} (s : Finset τ)
    (deg : ∀ a ∈ s, f a ∈ 𝒜 d)
    (rel : ∀ (a : τ) (mem : a ∈ s), ElemIsRelevant (f a) ⟨d, deg _ mem⟩)
    (a b : τ) (ha : a ∈ s) (hb : b ∈ s) :
    sum_potion_finset f s deg rel →+*
    (HomogeneousSubmonoid.closure (𝒜 := 𝒜) {f a * f b * ∑ j ∈ s, f j} (by
      rintro - rfl
      exact SetLike.IsHomogeneousElem.mul (SetLike.IsHomogeneousElem.mul ⟨d, deg a ha⟩
        ⟨d, deg b hb⟩) ⟨d, sum_mem <| by aesop⟩)).Potion := by
  refine RingHom.comp (HomogeneousSubmonoid.equivBarPotion _).symm.toRingHom
    (RingHom.comp (HomogeneousSubmonoid.potionMapOfLE _ _ ?_)
      (HomogeneousSubmonoid.equivBarPotion _).toRingHom)
  refine le_trans (HomogeneousSubmonoid.bar_mono _ _ ?_)
    (le_of_eq (HomogeneousSubmonoid.bar_bar _))
  intro x hx
  obtain ⟨n, rfl⟩ := Submonoid.mem_closure_singleton.1 hx
  refine pow_mem ?_ n
  exact ⟨⟨d, sum_mem <| by aesop⟩, ⟨f a * f b * ∑ j ∈ s, f j,
    Submonoid.mem_closure_singleton_self, ⟨f a * f b, by ring⟩⟩⟩

lemma potionToSumMul2_sigmaToSumMul_eq {d : ι} (s : Finset τ)
    (deg : ∀ a ∈ s, f a ∈ 𝒜 d)
    (rel : ∀ (a : τ) (mem : a ∈ s), ElemIsRelevant (f a) ⟨d, deg _ mem⟩)
    (a b : τ) (ha : a ∈ s) (hb : b ∈ s) (r : sum_potion_finset f s deg rel) :
    potionToSumMul2 f s deg rel a b ha hb (sigmaToSumMul f s deg rel a ha r) =
      sigmaToM f s deg rel a b ha hb r := by
  induction r using Quotient.inductionOn' with | h r =>
  unfold potionToSumMul2 sigmaToSumMul sigmaToM
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    HomogeneousSubmonoid.potionMapOfLE_mk', HomogeneousSubmonoid.equivBarPotion_apply,
    HomogeneousSubmonoid.toBarPotion_mk, RingEquiv.apply_symm_apply]

lemma sigmaToPowMul_eq_sigmaToM {d : ι} (s : Finset τ)
    (deg : ∀ a ∈ s, f a ∈ 𝒜 d)
    (rel : ∀ (a : τ) (mem : a ∈ s), ElemIsRelevant (f a) ⟨d, deg _ mem⟩)
    (a b : τ) (ha : a ∈ s) (hb : b ∈ s) (r : sum_potion_finset f s deg rel) :
    sigmaToPowMul f s deg rel 2 (f a * f b)
        (by rw [two_smul]; exact SetLike.mul_mem_graded (deg a ha) (deg b hb)) r =
      sigmaToM f s deg rel a b ha hb r := rfl

def overlapToM' {d : ι} (s : Finset τ)
    (deg : ∀ a ∈ s, f a ∈ 𝒜 d)
    (rel : ∀ (a : τ) (mem : a ∈ s), ElemIsRelevant (f a) ⟨d, deg _ mem⟩)
    (a b : τ) (ha : a ∈ s) (hb : b ∈ s) :
    ((HomogeneousSubmonoid.closure (𝒜 := 𝒜) {f b} (by
        intro w hw; simp only [Set.mem_singleton_iff] at hw; rw [hw]; exact ⟨d, deg b hb⟩) *
      HomogeneousSubmonoid.closure (𝒜 := 𝒜) {f a} (by
        intro w hw; simp only [Set.mem_singleton_iff] at hw; rw [hw]; exact ⟨d, deg a ha⟩))).Potion →+*
    (HomogeneousSubmonoid.closure (𝒜 := 𝒜) {f a * f b * ∑ j ∈ s, f j} (by
      rintro - rfl
      exact SetLike.IsHomogeneousElem.mul (SetLike.IsHomogeneousElem.mul ⟨d, deg a ha⟩
        ⟨d, deg b hb⟩) ⟨d, sum_mem <| by aesop⟩)).Potion :=
  RingHom.comp (overlapToM f s deg rel a b ha hb) (HomogeneousSubmonoid.potionEquiv (mul_comm _ _)).toRingHom

def potionToSumMul2' {d : ι} (s : Finset τ)
    (deg : ∀ a ∈ s, f a ∈ 𝒜 d)
    (rel : ∀ (a : τ) (mem : a ∈ s), ElemIsRelevant (f a) ⟨d, deg _ mem⟩)
    (a b : τ) (ha : a ∈ s) (hb : b ∈ s) :
    (HomogeneousSubmonoid.closure (𝒜 := 𝒜) {f b * ∑ j ∈ s, f j} (by
      rintro - rfl
      exact SetLike.IsHomogeneousElem.mul ⟨d, deg b hb⟩ ⟨d, sum_mem <| by aesop⟩)).Potion →+*
    (HomogeneousSubmonoid.closure (𝒜 := 𝒜) {f a * f b * ∑ j ∈ s, f j} (by
      rintro - rfl
      exact SetLike.IsHomogeneousElem.mul (SetLike.IsHomogeneousElem.mul ⟨d, deg a ha⟩
        ⟨d, deg b hb⟩) ⟨d, sum_mem <| by aesop⟩)).Potion := by
  refine RingHom.comp (HomogeneousSubmonoid.equivBarPotion _).symm.toRingHom
    (RingHom.comp (HomogeneousSubmonoid.potionMapOfLE _ _ ?_)
      (HomogeneousSubmonoid.equivBarPotion _).toRingHom)
  refine le_trans (HomogeneousSubmonoid.bar_mono _ _ ?_)
    (le_of_eq (HomogeneousSubmonoid.bar_bar _))
  intro x hx
  obtain ⟨n, rfl⟩ := Submonoid.mem_closure_singleton.1 hx
  refine pow_mem ?_ n
  exact ⟨SetLike.IsHomogeneousElem.mul ⟨d, deg b hb⟩ ⟨d, sum_mem <| by aesop⟩,
    ⟨f a * f b * ∑ j ∈ s, f j, Submonoid.mem_closure_singleton_self, ⟨f a, by ring⟩⟩⟩

lemma overlapToM'_potionToMul_eq {d : ι} (s : Finset τ)
    (deg : ∀ a ∈ s, f a ∈ 𝒜 d)
    (rel : ∀ (a : τ) (mem : a ∈ s), ElemIsRelevant (f a) ⟨d, deg _ mem⟩)
    (a b : τ) (ha : a ∈ s) (hb : b ∈ s)
    (z : (HomogeneousSubmonoid.closure (𝒜 := 𝒜) {f b} (by
        intro w hw; simp only [Set.mem_singleton_iff] at hw; rw [hw]; exact ⟨d, deg b hb⟩)).Potion) :
    overlapToM' f s deg rel a b ha hb
        (HomogeneousSubmonoid.potionToMul _
          (HomogeneousSubmonoid.closure (𝒜 := 𝒜) {f a} (by
            intro w hw; simp only [Set.mem_singleton_iff] at hw; rw [hw]; exact ⟨d, deg a ha⟩)) z) =
      potionToSumMul2' f s deg rel a b ha hb (potionToSumMul f s deg rel b hb z) := by
  induction z using Quotient.inductionOn' with | h z =>
  unfold overlapToM' overlapToM potionToSumMul2' potionToSumMul
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    HomogeneousSubmonoid.potionToMul_mk', HomogeneousSubmonoid.potionMapOfLE_mk',
    HomogeneousSubmonoid.equivBarPotion_apply, HomogeneousSubmonoid.toBarPotion_mk,
    HomogeneousSubmonoid.potionEquiv_mk, RingEquiv.apply_symm_apply]

noncomputable def chartIsoPow {d : ι} (s : Finset τ)
    (deg : ∀ a ∈ s, f a ∈ 𝒜 d)
    (rel : ∀ (a : τ) (mem : a ∈ s), ElemIsRelevant (f a) ⟨d, deg _ mem⟩)
    (m : ℕ) (c : A) (hc : c ∈ 𝒜 (m • d)) :
    Localization.Away (s_elem_pow f s deg rel m c hc) ≃+*
    (HomogeneousSubmonoid.closure (𝒜 := 𝒜) {c * ∑ j ∈ s, f j}
      (by rintro - rfl
          exact SetLike.IsHomogeneousElem.mul ⟨m • d, hc⟩ ⟨d, sum_mem (by aesop)⟩)).Potion :=
  (sumMagicE f s deg rel m c hc).toRingEquiv.trans (sumMagicTail f s deg m c hc)

set_option maxHeartbeats 1600000 in

lemma chartIsoPow_algebraMap {d : ι} (s : Finset τ)
    (deg : ∀ a ∈ s, f a ∈ 𝒜 d)
    (rel : ∀ (a : τ) (mem : a ∈ s), ElemIsRelevant (f a) ⟨d, deg _ mem⟩)
    (m : ℕ) (c : A) (hc : c ∈ 𝒜 (m • d)) (r : sum_potion_finset f s deg rel) :
    chartIsoPow f s deg rel m c hc (algebraMap _ _ r) =
      sigmaToPowMul f s deg rel m c hc r := by
  unfold chartIsoPow
  rw [RingEquiv.trans_apply]
  erw [sumMagicE_algebraMap]
  rw [sumMagicTail_potionToMul]

@[simp]
lemma sigmaToPowMul_algebraMap {d : ι} (s : Finset τ)
    (deg : ∀ a ∈ s, f a ∈ 𝒜 d)
    (rel : ∀ (a : τ) (mem : a ∈ s), ElemIsRelevant (f a) ⟨d, deg _ mem⟩)
    (m : ℕ) (c : A) (hc : c ∈ 𝒜 (m • d)) (z : 𝒜 0) :
    sigmaToPowMul f s deg rel m c hc (algebraMap (𝒜 0) _ z) = algebraMap (𝒜 0) _ z := by
  unfold sigmaToPowMul
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    HomogeneousSubmonoid.equivBarPotion_algebraMap,
    HomogeneousSubmonoid.potionMapOfLE_algebraMap,
    HomogeneousSubmonoid.equivBarPotion_symm_algebraMap]

noncomputable def chartIso {d : ι} (s : Finset τ)
    (deg : ∀ a ∈ s, f a ∈ 𝒜 d)
    (rel : ∀ (a : τ) (mem : a ∈ s), ElemIsRelevant (f a) ⟨d, deg _ mem⟩)
    (i : τ) (hi : i ∈ s) :
    Localization.Away (s_elem_finset f s deg rel i hi) ≃+*
    (HomogeneousSubmonoid.closure (𝒜 := 𝒜) {f i * ∑ j ∈ s, f j}
      (by rintro - rfl
          exact SetLike.IsHomogeneousElem.mul ⟨d, deg i hi⟩ ⟨d, sum_mem (by aesop)⟩)).Potion :=
  (sumMagicE' f s deg rel i hi).toRingEquiv.trans
    (sumMagicTail f s deg 1 (f i) (by rw [one_smul]; exact deg i hi))

set_option maxHeartbeats 1600000 in

lemma chartIso_algebraMap {d : ι} (s : Finset τ)
    (deg : ∀ a ∈ s, f a ∈ 𝒜 d)
    (rel : ∀ (a : τ) (mem : a ∈ s), ElemIsRelevant (f a) ⟨d, deg _ mem⟩)
    (i : τ) (hi : i ∈ s) (r : sum_potion_finset f s deg rel) :
    chartIso f s deg rel i hi (algebraMap _ _ r) =
      sigmaToPowMul f s deg rel 1 (f i) (by simpa using deg i hi) r := by
  unfold chartIso
  rw [RingEquiv.trans_apply]
  erw [sumMagicE'_algebraMap]
  rw [sumMagicTail_potionToMul]

lemma chartIso_algebraMap0 {d : ι} (s : Finset τ)
    (deg : ∀ a ∈ s, f a ∈ 𝒜 d)
    (rel : ∀ (a : τ) (mem : a ∈ s), ElemIsRelevant (f a) ⟨d, deg _ mem⟩)
    (i : τ) (hi : i ∈ s) (z : 𝒜 0) :
    chartIso f s deg rel i hi (algebraMap (𝒜 0) _ z) = algebraMap (𝒜 0) _ z := by
  rw [IsScalarTower.algebraMap_apply (𝒜 0) (sum_potion_finset f s deg rel)
    (Localization.Away (s_elem_finset f s deg rel i hi)) z, chartIso_algebraMap,
    sigmaToPowMul_algebraMap]

lemma chartIso_symm_algebraMap0 {d : ι} (s : Finset τ)
    (deg : ∀ a ∈ s, f a ∈ 𝒜 d)
    (rel : ∀ (a : τ) (mem : a ∈ s), ElemIsRelevant (f a) ⟨d, deg _ mem⟩)
    (i : τ) (hi : i ∈ s) (z : 𝒜 0) :
    (chartIso f s deg rel i hi).symm (algebraMap (𝒜 0) _ z) = algebraMap (𝒜 0) _ z := by
  rw [← chartIso_algebraMap0 f s deg rel i hi z, RingEquiv.symm_apply_apply]

noncomputable def overlapChartIso {d : ι} (s : Finset τ)
    (deg : ∀ a ∈ s, f a ∈ 𝒜 d)
    (rel : ∀ (a : τ) (mem : a ∈ s), ElemIsRelevant (f a) ⟨d, deg _ mem⟩)
    (a b : τ) (ha : a ∈ s) (hb : b ∈ s) :=
  (transportAway (s_elem_finset_mul f s deg rel a b ha hb)).toRingEquiv.trans
    (chartIsoPow f s deg rel 2 (f a * f b)
      (by rw [two_smul]; exact SetLike.mul_mem_graded (deg a ha) (deg b hb)))

set_option maxHeartbeats 1600000 in

lemma overlapChartIso_algebraMap {d : ι} (s : Finset τ)
    (deg : ∀ a ∈ s, f a ∈ 𝒜 d)
    (rel : ∀ (a : τ) (mem : a ∈ s), ElemIsRelevant (f a) ⟨d, deg _ mem⟩)
    (a b : τ) (ha : a ∈ s) (hb : b ∈ s) (r : sum_potion_finset f s deg rel) :
    overlapChartIso f s deg rel a b ha hb (algebraMap _ _ r) =
      sigmaToPowMul f s deg rel 2 (f a * f b)
        (by rw [two_smul]; exact SetLike.mul_mem_graded (deg a ha) (deg b hb)) r := by
  unfold overlapChartIso
  rw [RingEquiv.trans_apply]
  erw [transportAway_algebraMap]
  rw [chartIsoPow_algebraMap]

lemma sigmaToPowMul_one {d : ι} (s : Finset τ)
    (deg : ∀ a ∈ s, f a ∈ 𝒜 d)
    (rel : ∀ (a : τ) (mem : a ∈ s), ElemIsRelevant (f a) ⟨d, deg _ mem⟩)
    (i : τ) (hi : i ∈ s) (r : sum_potion_finset f s deg rel) :
    sigmaToPowMul f s deg rel 1 (f i) (by simpa using deg i hi) r =
      sigmaToSumMul f s deg rel i hi r := rfl

set_option maxHeartbeats 1600000 in

lemma chartIso_overlap_compat {d : ι} (s : Finset τ)
    (deg : ∀ a ∈ s, f a ∈ 𝒜 d)
    (rel : ∀ (a : τ) (mem : a ∈ s), ElemIsRelevant (f a) ⟨d, deg _ mem⟩)
    (a b : τ) (ha : a ∈ s) (hb : b ∈ s) :
    RingHom.comp (overlapChartIso f s deg rel a b ha hb).toRingHom
        (IsLocalization.Away.awayToAwayRight
          (S := Localization.Away (s_elem_finset f s deg rel a ha))
          (P := Localization.Away
            (s_elem_finset f s deg rel a ha * s_elem_finset f s deg rel b hb))
          (s_elem_finset f s deg rel a ha) (s_elem_finset f s deg rel b hb)) =
      RingHom.comp (potionToSumMul2 f s deg rel a b ha hb)
        (chartIso f s deg rel a ha).toRingHom := by
  refine IsLocalization.ringHom_ext
    (Submonoid.powers (s_elem_finset f s deg rel a ha)) ?_
  ext r
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  rw [IsLocalization.Away.awayToAwayRight_eq, overlapChartIso_algebraMap,
    chartIso_algebraMap, sigmaToPowMul_one, potionToSumMul2_sigmaToSumMul_eq,
    ← sigmaToPowMul_eq_sigmaToM]

lemma potionToSumMul2'_sigmaToSumMul_eq {d : ι} (s : Finset τ)
    (deg : ∀ a ∈ s, f a ∈ 𝒜 d)
    (rel : ∀ (a : τ) (mem : a ∈ s), ElemIsRelevant (f a) ⟨d, deg _ mem⟩)
    (a b : τ) (ha : a ∈ s) (hb : b ∈ s) (r : sum_potion_finset f s deg rel) :
    potionToSumMul2' f s deg rel a b ha hb (sigmaToSumMul f s deg rel b hb r) =
      sigmaToM f s deg rel a b ha hb r := by
  induction r using Quotient.inductionOn' with | h r =>
  unfold potionToSumMul2' sigmaToSumMul sigmaToM
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    HomogeneousSubmonoid.potionMapOfLE_mk', HomogeneousSubmonoid.equivBarPotion_apply,
    HomogeneousSubmonoid.toBarPotion_mk, RingEquiv.apply_symm_apply]

set_option maxHeartbeats 1600000 in

lemma chartIso_overlap_compat' {d : ι} (s : Finset τ)
    (deg : ∀ a ∈ s, f a ∈ 𝒜 d)
    (rel : ∀ (a : τ) (mem : a ∈ s), ElemIsRelevant (f a) ⟨d, deg _ mem⟩)
    (a b : τ) (ha : a ∈ s) (hb : b ∈ s) :
    RingHom.comp (overlapChartIso f s deg rel a b ha hb).toRingHom
        (IsLocalization.Away.awayToAwayLeft
          (S := Localization.Away (s_elem_finset f s deg rel b hb))
          (P := Localization.Away
            (s_elem_finset f s deg rel a ha * s_elem_finset f s deg rel b hb))
          (s_elem_finset f s deg rel b hb) (s_elem_finset f s deg rel a ha)) =
      RingHom.comp (potionToSumMul2' f s deg rel a b ha hb)
        (chartIso f s deg rel b hb).toRingHom := by
  refine IsLocalization.ringHom_ext
    (Submonoid.powers (s_elem_finset f s deg rel b hb)) ?_
  ext r
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  rw [IsLocalization.Away.awayToAwayLeft_eq, overlapChartIso_algebraMap,
    chartIso_algebraMap, sigmaToPowMul_one, potionToSumMul2'_sigmaToSumMul_eq,
    ← sigmaToPowMul_eq_sigmaToM]

abbrev unionFam {d : ι} (s : Finset τ)
    (deg : ∀ a ∈ s, f a ∈ 𝒜 d)
    (rel : ∀ (a : τ) (mem : a ∈ s), ElemIsRelevant (f a) ⟨d, deg _ mem⟩) :
    s → GoodPotionIngredient 𝒜 := fun i =>
  { toHomogeneousSubmonoid := .closure { f i.1 } <| by
      cases i
      simpa using ⟨d, by aesop⟩
    relevant := rel _ i.2
    fg := ⟨{f i.1}, by simp; rfl⟩ }

abbrev unionSpecFinset {d : ι} (s : Finset τ)
    (deg : ∀ a ∈ s, f a ∈ 𝒜 d)
    (rel : ∀ (a : τ) (mem : a ∈ s), ElemIsRelevant (f a) ⟨d, deg _ mem⟩) : Scheme :=
  Proj (𝒜 := 𝒜) (τ := s) (unionFam f s deg rel)

abbrev componentToUnionSpecFinset {d : ι} (s : Finset τ)
    (deg : ∀ a ∈ s, f a ∈ 𝒜 d)
    (rel : ∀ (a : τ) (mem : a ∈ s), ElemIsRelevant (f a) ⟨d, deg _ mem⟩)
    (i : τ) (hi : i ∈ s) :
    Spec (CommRingCat.of <| (HomogeneousSubmonoid.closure {f i} (by
      rintro - rfl
      exact ⟨d, by aesop⟩) : HomogeneousSubmonoid 𝒜).Potion) ⟶
    unionSpecFinset f s deg rel :=
  (glueData (𝒜 := 𝒜) (τ := s) (unionFam f s deg rel)).ι ⟨i, hi⟩

set_option maxHeartbeats 3200000 in
lemma sum_open_finset {d : ι} (s : Finset τ)
    (deg : ∀ a ∈ s, f a ∈ 𝒜 d)
    (rel : ∀ (a : τ) (mem : a ∈ s), ElemIsRelevant (f a) ⟨d, deg _ mem⟩) :
  ∃ (f : Spec (CommRingCat.of <| sum_potion_finset f s deg rel) ⟶ unionSpecFinset f s deg rel),
    Scheme.Hom.IsOver f (SpecBase 𝒜) := by
  classical

  have hUtop : ⨆ i : {x // x ∈ s},
      (PrimeSpectrum.basicOpen (s_elem_finset f s deg rel i.1 i.2) :
        (Spec (CommRingCat.of <| sum_potion_finset f s deg rel)).Opens) = ⊤ :=
    PrimeSpectrum.iSup_basicOpen_eq_top_iff.2 (span_s_elem_finset_eq_top f s deg rel)
  let 𝒰 : (Spec (CommRingCat.of <| sum_potion_finset f s deg rel)).OpenCover :=
    Scheme.openCoverOfISupEqTop _
      (fun i : {x // x ∈ s} =>
        (PrimeSpectrum.basicOpen (s_elem_finset f s deg rel i.1 i.2) :
          (Spec (CommRingCat.of <| sum_potion_finset f s deg rel)).Opens)) hUtop

  let g : ∀ i : {x // x ∈ s}, 𝒰.obj i ⟶ unionSpecFinset f s deg rel := fun i =>
    (show 𝒰.obj i ⟶
        Spec (CommRingCat.of (Localization.Away (s_elem_finset f s deg rel i.1 i.2))) from
      (AlgebraicGeometry.basicOpenIsoSpecAway
        (R := CommRingCat.of (sum_potion_finset f s deg rel))
        (s_elem_finset f s deg rel i.1 i.2)).hom) ≫
      Spec.map (CommRingCat.ofHom
          (chartIso f s deg rel i.1 i.2).symm.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (potionToSumMul f s deg rel i.1 i.2)) ≫
          componentToUnionSpecFinset f s deg rel i.1 i.2
  refine ⟨𝒰.glueMorphisms g ?_, ⟨?_⟩⟩
  ·

    intro a b
    simp only [𝒰, Scheme.openCoverOfISupEqTop_map]

    set Ua : (Spec (CommRingCat.of <| sum_potion_finset f s deg rel)).Opens :=
      PrimeSpectrum.basicOpen (s_elem_finset f s deg rel a.1 a.2) with hUa
    set Ub : (Spec (CommRingCat.of <| sum_potion_finset f s deg rel)).Opens :=
      PrimeSpectrum.basicOpen (s_elem_finset f s deg rel b.1 b.2) with hUb
    set W : (Spec (CommRingCat.of <| sum_potion_finset f s deg rel)).Opens :=
      PrimeSpectrum.basicOpen
        (s_elem_finset f s deg rel a.1 a.2 * s_elem_finset f s deg rel b.1 b.2) with hW
    have hWinf : W = Ua ⊓ Ub := by
      rw [hW, hUa, hUb]; exact PrimeSpectrum.basicOpen_mul _ _
    have hWa : W ≤ Ua := by rw [hWinf]; exact inf_le_left
    have hWb : W ≤ Ub := by rw [hWinf]; exact inf_le_right

    have hrange : Set.range (W.ι).base =
        Set.range ((Limits.pullback.fst (Ua.ι) (Ub.ι) ≫ Ua.ι)).base := by
      rw [IsOpenImmersion.range_pullback_to_base_of_left, Scheme.Opens.range_ι,
        Scheme.Opens.range_ι, Scheme.Opens.range_ι, hWinf]
      rfl
    let ε := IsOpenImmersion.isoOfRangeEq (W.ι) (Limits.pullback.fst (Ua.ι) (Ub.ι) ≫ Ua.ι) hrange
    have hεfac : ε.hom ≫ (Limits.pullback.fst (Ua.ι) (Ub.ι) ≫ Ua.ι) = W.ι :=
      IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hrange
    have hεa : ε.hom ≫ Limits.pullback.fst (Ua.ι) (Ub.ι) = Scheme.homOfLE _ hWa := by
      rw [← cancel_mono (Ua.ι), Category.assoc, hεfac, Scheme.homOfLE_ι]
    have hεb : ε.hom ≫ Limits.pullback.snd (Ua.ι) (Ub.ι) = Scheme.homOfLE _ hWb := by
      rw [← cancel_mono (Ub.ι), Category.assoc, ← Limits.pullback.condition, hεfac,
        Scheme.homOfLE_ι]

    have hAa : Scheme.homOfLE _ hWa ≫
        (basicOpenIsoSpecAway (R := CommRingCat.of (sum_potion_finset f s deg rel))
          (s_elem_finset f s deg rel a.1 a.2)).hom =
        (basicOpenIsoSpecAway (R := CommRingCat.of (sum_potion_finset f s deg rel))
            (s_elem_finset f s deg rel a.1 a.2 * s_elem_finset f s deg rel b.1 b.2)).hom ≫
          Spec.map (CommRingCat.ofHom (IsLocalization.Away.awayToAwayRight
            (s_elem_finset f s deg rel a.1 a.2) (s_elem_finset f s deg rel b.1 b.2))) := by
      have L := basicOpenIsoSpecAway_inv_homOfLE
        (R := CommRingCat.of (sum_potion_finset f s deg rel))
        (s_elem_finset f s deg rel a.1 a.2) (s_elem_finset f s deg rel b.1 b.2)
        (s_elem_finset f s deg rel a.1 a.2 * s_elem_finset f s deg rel b.1 b.2) rfl
      rw [Iso.inv_comp_eq] at L
      rw [L]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    haveI : IsLocalization.Away
        (s_elem_finset f s deg rel b.1 b.2 * s_elem_finset f s deg rel a.1 a.2)
        (Localization.Away
          (s_elem_finset f s deg rel a.1 a.2 * s_elem_finset f s deg rel b.1 b.2)) := by
      rw [mul_comm]; infer_instance
    have hAb : Scheme.homOfLE _ hWb ≫
        (basicOpenIsoSpecAway (R := CommRingCat.of (sum_potion_finset f s deg rel))
          (s_elem_finset f s deg rel b.1 b.2)).hom =
        (basicOpenIsoSpecAway (R := CommRingCat.of (sum_potion_finset f s deg rel))
            (s_elem_finset f s deg rel a.1 a.2 * s_elem_finset f s deg rel b.1 b.2)).hom ≫
          Spec.map (CommRingCat.ofHom (IsLocalization.Away.awayToAwayRight
            (s_elem_finset f s deg rel b.1 b.2) (s_elem_finset f s deg rel a.1 a.2))) := by
      have L := basicOpenIsoSpecAway_inv_homOfLE
        (R := CommRingCat.of (sum_potion_finset f s deg rel))
        (s_elem_finset f s deg rel b.1 b.2) (s_elem_finset f s deg rel a.1 a.2)
        (s_elem_finset f s deg rel a.1 a.2 * s_elem_finset f s deg rel b.1 b.2)
        (mul_comm _ _)
      rw [Iso.inv_comp_eq] at L
      rw [L]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

    rw [← cancel_epi ε.hom, reassoc_of% hεa, reassoc_of% hεb]
    simp only [g]
    rw [reassoc_of% hAa, reassoc_of% hAb, cancel_epi (basicOpenIsoSpecAway
      (R := CommRingCat.of (sum_potion_finset f s deg rel))
      (s_elem_finset f s deg rel a.1 a.2 * s_elem_finset f s deg rel b.1 b.2)).hom]

    have key_a : RingHom.comp (IsLocalization.Away.awayToAwayRight
          (s_elem_finset f s deg rel a.1 a.2) (s_elem_finset f s deg rel b.1 b.2))
          (RingHom.comp (chartIso f s deg rel a.1 a.2).symm.toRingHom
            (potionToSumMul f s deg rel a.1 a.2)) =
        RingHom.comp (overlapChartIso f s deg rel a.1 b.1 a.2 b.2).symm.toRingHom
          (RingHom.comp (overlapToM f s deg rel a.1 b.1 a.2 b.2)
            (HomogeneousSubmonoid.potionToMul _ _)) := by
      ext x
      apply (overlapChartIso f s deg rel a.1 b.1 a.2 b.2).injective
      have h1 := RingHom.congr_fun (chartIso_overlap_compat f s deg rel a.1 b.1 a.2 b.2)
        ((chartIso f s deg rel a.1 a.2).symm (potionToSumMul f s deg rel a.1 a.2 x))
      simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingHom.coe_coe, RingEquiv.apply_symm_apply] at h1 ⊢
      rw [h1, overlapToM_potionToMul_eq]
    have key_b : RingHom.comp (IsLocalization.Away.awayToAwayRight
          (s_elem_finset f s deg rel b.1 b.2) (s_elem_finset f s deg rel a.1 a.2))
          (RingHom.comp (chartIso f s deg rel b.1 b.2).symm.toRingHom
            (potionToSumMul f s deg rel b.1 b.2)) =
        RingHom.comp (overlapChartIso f s deg rel a.1 b.1 a.2 b.2).symm.toRingHom
          (RingHom.comp (overlapToM f s deg rel a.1 b.1 a.2 b.2)
            (RingHom.comp (HomogeneousSubmonoid.potionEquiv (mul_comm _ _)).toRingHom
              (HomogeneousSubmonoid.potionToMul _ _))) := by
      ext x
      apply (overlapChartIso f s deg rel a.1 b.1 a.2 b.2).injective
      have h1 := RingHom.congr_fun (chartIso_overlap_compat' f s deg rel a.1 b.1 a.2 b.2)
        ((chartIso f s deg rel b.1 b.2).symm (potionToSumMul f s deg rel b.1 b.2 x))
      simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingHom.coe_coe, RingEquiv.apply_symm_apply] at h1 ⊢
      rw [show (IsLocalization.Away.awayToAwayRight
          (s_elem_finset f s deg rel b.1 b.2) (s_elem_finset f s deg rel a.1 a.2) :
            Localization.Away (s_elem_finset f s deg rel b.1 b.2) →+*
            Localization.Away (s_elem_finset f s deg rel a.1 a.2 *
              s_elem_finset f s deg rel b.1 b.2)) =
        IsLocalization.Away.awayToAwayLeft
          (s_elem_finset f s deg rel b.1 b.2) (s_elem_finset f s deg rel a.1 a.2) from rfl]
      rw [h1]
      exact (overlapToM'_potionToMul_eq f s deg rel a.1 b.1 a.2 b.2 _).symm

    simp only [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [key_a, key_b]
    simp only [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    exact congrArg (fun z => Spec.map (CommRingCat.ofHom
        (overlapChartIso f s deg rel a.1 b.1 a.2 b.2).symm.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (overlapToM f s deg rel a.1 b.1 a.2 b.2)) ≫ z)
      ((GoodPotionIngredient.glueData (𝒜 := 𝒜) (τ := s)
        (unionFam f s deg rel)).glue_condition a b).symm
  ·

    refine 𝒰.hom_ext _ _ fun i => ?_
    rw [← Category.assoc, 𝒰.ι_glueMorphisms]
    simp only [g, Category.assoc]
    rw [show componentToUnionSpecFinset f s deg rel i.1 i.2 ≫
        (unionSpecFinset f s deg rel ↘ SpecBase 𝒜) =
        Spec.map (CommRingCat.ofHom (algebraMap _ _)) from ?_]
    ·
      simp only [𝒰, Scheme.openCoverOfISupEqTop_map]
      rw [show (Spec (CommRingCat.of (sum_potion_finset f s deg rel)) ↘ SpecBase 𝒜) =
        Spec.map (CommRingCat.ofHom
          (algebraMap (𝒜 0) (sum_potion_finset f s deg rel))) from rfl]
      rw [← Iso.eq_inv_comp]
      simp only [basicOpenIsoSpecAway, IsOpenImmersion.isoOfRangeEq_inv_fac_assoc]
      simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      refine congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun z => ?_))
      simp only [CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply,
        RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.coe_ringEquiv,
        AlgEquiv.coe_ringEquiv']
      rw [show (potionToSumMul f s deg rel i.1 i.2)
          (algebraMap (𝒜 0) _ z) = algebraMap (𝒜 0) _ z from ?_]
      · rw [chartIso_symm_algebraMap0]
        exact (IsScalarTower.algebraMap_apply (𝒜 0) _ _ z).symm
      · simp [potionToSumMul]
    · show ((glueData _).ι _) ≫ (GoodPotionIngredient.over _) = _
      erw [CategoryTheory.Limits.Multicoequalizer.π_desc]
