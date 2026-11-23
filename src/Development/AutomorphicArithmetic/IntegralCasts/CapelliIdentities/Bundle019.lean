module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.Analysis.Calculus.FDeriv.Mul

@[expose] public section

section

@[reducible] noncomputable def UpperTheory.Reformulated.B.Yt7.Sp :
    (R : Type) → [CommRing R] → AlgebraicGeometry.Scheme :=
    fun (R : Type) [CommRing R] ↦ AlgebraicGeometry.Spec (CommRingCat.of R)

@[reducible] noncomputable def UpperTheory.Reformulated.B.Yt7.spMap :
    {R R' : Type} →
      [inst : CommRing R] → [inst_1 : CommRing R'] → (R →+* R') → (UpperTheory.Reformulated.B.Yt7.Sp R' ⟶ UpperTheory.Reformulated.B.Yt7.Sp R) :=
    fun {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') ↦ AlgebraicGeometry.Spec.map (CommRingCat.ofHom f)

open CategoryTheory AlgebraicGeometry in
private theorem UpperTheory.Reformulated.B.Yt7.ring_lift {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [IsIntegrallyClosed R] {A : Type} [CommRing A] (φ : R →+* A) (hφ : φ.Finite)
    (ψ : A →+* K) (h : ψ.comp φ = algebraMap R K) :
    ∃ σ : A →+* R, σ.comp φ = RingHom.id R ∧ (algebraMap R K).comp σ = ψ := by
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hmem : ∀ a : A, ψ a ∈ (algebraMap R K).range := by
    intro a
    have hi : (algebraMap R K).IsIntegralElem (ψ a) := by
      rw [← h]
      exact (hφ.to_isIntegral a).map ψ
    exact IsIntegrallyClosed.isIntegral_iff.mp hi
  let e : R ≃+* (algebraMap R K).range :=
    RingEquiv.ofBijective (algebraMap R K).rangeRestrict
      ⟨fun a b hab => hinj (congrArg Subtype.val hab), (algebraMap R K).rangeRestrict_surjective⟩
  have key : ∀ a : A, algebraMap R K (e.symm ⟨ψ a, hmem a⟩) = ψ a := fun a =>
    congrArg Subtype.val (e.apply_symm_apply ⟨ψ a, hmem a⟩)
  refine ⟨e.symm.toRingHom.comp (ψ.codRestrict _ hmem), ?_, ?_⟩
  · ext r
    apply hinj
    exact (key (φ r)).trans (RingHom.congr_fun h r)
  · ext a
    exact key a

open CategoryTheory AlgebraicGeometry in
private theorem UpperTheory.Reformulated.B.Yt7.section_lift {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [IsIntegrallyClosed R] {P : Scheme} (g : P ⟶ Spec (CommRingCat.of R)) [IsFinite g]
    (s : Spec (CommRingCat.of K) ⟶ P)
    (h : s ≫ g = Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    ∃ t : Spec (CommRingCat.of R) ⟶ P,
      t ≫ g = 𝟙 _ ∧ Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ t = s := by
  have : IsAffine P := isAffine_of_isAffineHom g
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (P.isoSpec.inv ≫ g)
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (s ≫ P.isoSpec.hom)
  have hfin : φ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hφ]
    infer_instance
  have hc : φ ≫ ψ = CommRingCat.ofHom (algebraMap R K) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, hψ, ← h]
    simp
  obtain ⟨σ, h1, h2⟩ := UpperTheory.Reformulated.B.Yt7.ring_lift (K := K) φ.hom hfin ψ.hom
    (congrArg CommRingCat.Hom.hom hc)
  have h1' : φ ≫ CommRingCat.ofHom σ = 𝟙 _ := CommRingCat.hom_ext h1
  have h2' : CommRingCat.ofHom σ ≫ CommRingCat.ofHom (algebraMap R K) = ψ := CommRingCat.hom_ext h2
  refine ⟨Spec.map (CommRingCat.ofHom σ) ≫ P.isoSpec.inv, ?_, ?_⟩
  · rw [Category.assoc, ← hφ, ← Spec.map_comp, h1', Spec.map_id]
  · rw [← Category.assoc, ← Spec.map_comp, h2', hψ]
    simp

theorem UpperTheory.Reformulated.B.Yt7.lift_finite :
    ∀ {R K : Type} [inst : CommRing R] [IsDomain R] [inst_2 : Field K] [inst_3 : Algebra R K] [IsFractionRing R K]
      [IsIntegrallyClosed R] {X S : AlgebraicGeometry.Scheme} (f : X ⟶ S) [AlgebraicGeometry.IsFinite f]
      (y : UpperTheory.Reformulated.B.Yt7.Sp R ⟶ S) (w : UpperTheory.Reformulated.B.Yt7.Sp K ⟶ X),
      CategoryTheory.CategoryStruct.comp w f =
          CategoryTheory.CategoryStruct.comp (UpperTheory.Reformulated.B.Yt7.spMap (Algebra.algebraMap R K)) y →
        ∃ (v : UpperTheory.Reformulated.B.Yt7.Sp R ⟶ X),
          CategoryTheory.CategoryStruct.comp v f = y ∧
            CategoryTheory.CategoryStruct.comp (UpperTheory.Reformulated.B.Yt7.spMap (Algebra.algebraMap R K)) v = w := by
  intro R K _ _ _ _ _ _ X S f _ y w h
  obtain ⟨t, ht1, ht2⟩ := UpperTheory.Reformulated.B.Yt7.section_lift (K := K) (CategoryTheory.Limits.pullback.snd f y)
    (CategoryTheory.Limits.pullback.lift w _ h) (CategoryTheory.Limits.pullback.lift_snd _ _ _)
  refine ⟨CategoryTheory.CategoryStruct.comp t (CategoryTheory.Limits.pullback.fst f y), ?_, ?_⟩
  · rw [CategoryTheory.Category.assoc, CategoryTheory.Limits.pullback.condition,
      ← CategoryTheory.Category.assoc, ht1, CategoryTheory.Category.id_comp]
  · rw [← CategoryTheory.Category.assoc, ht2, CategoryTheory.Limits.pullback.lift_fst]
end

section

namespace UpperTheory.Reformulated.B.RegularUnitPoints

theorem aux1 : ∀ {Ω : Type} [inst : Field Ω], IsLocalRing Ω := by
  intro Ω inst
  infer_instance

noncomputable def genPt : {X : AlgebraicGeometry.Scheme} →
  {Ω : Type} → [inst : Field Ω] → (AlgebraicGeometry.Spec ↧Ω ⟶ X) → ↥X :=
  fun {X} {Ω} [Field Ω] ξ => ξ (IsLocalRing.closedPoint Ω)

noncomputable def Cpt : {X : AlgebraicGeometry.Scheme} →
  {Ω : Type} → [inst : Field Ω] → (AlgebraicGeometry.Spec ↧Ω ⟶ X) → Type :=
  fun {X} {Ω} [Field Ω] ξ => { p // genPt ξ ⤳ p }

theorem aux4 : ∀ {X : AlgebraicGeometry.Scheme} {Ω : Type} [inst : Field Ω]
  (ξ : AlgebraicGeometry.Spec ↧Ω ⟶ X) (p : Cpt ξ),
  genPt ξ ⤳ p.val := by
  intro X Ω inst ξ p
  exact p.2

theorem aux5 : ∀ {Ω : Type} [inst : Field Ω], IsLocalRing (CommRingCat.of Ω) := by
  intro Ω inst
  show IsLocalRing Ω
  infer_instance

noncomputable def genMap : {X : AlgebraicGeometry.Scheme} →
  {Ω : Type} →
    [inst : Field Ω] →
      (ξ : AlgebraicGeometry.Spec ↧Ω ⟶ X) →
        (p : Cpt ξ) → ↑(X.presheaf.stalk p.val) →+* Ω :=
  fun {X} {Ω} [Field Ω] ξ p =>
    CommRingCat.Hom.hom
      (CategoryTheory.CategoryStruct.comp
        (X.presheaf.stalkSpecializes (aux4 ξ p))
        (AlgebraicGeometry.Scheme.stalkClosedPointTo ξ))

noncomputable def regAt : {X : AlgebraicGeometry.Scheme} →
  {Ω : Type} →
    [inst : Field Ω] →
      (ξ : AlgebraicGeometry.Spec ↧Ω ⟶ X) → Cpt ξ → Subring Ω :=
  fun {X} {Ω} [Field Ω] ξ p => (genMap ξ p).range

noncomputable def unitAt : {X : AlgebraicGeometry.Scheme} →
  {Ω : Type} →
    [inst : Field Ω] →
      (ξ : AlgebraicGeometry.Spec ↧Ω ⟶ X) → Cpt ξ → Ω → Prop :=
  fun {X} {Ω} [Field Ω] ξ p a =>
    a ≠ 0 ∧
      a ∈ regAt ξ p ∧
        a⁻¹ ∈ regAt ξ p

noncomputable def InFibre : {X : AlgebraicGeometry.Scheme} →
  {Ω : Type} →
    [inst : Field Ω] →
      (ξ : AlgebraicGeometry.Spec ↧Ω ⟶ X) → ℕ → Cpt ξ → Prop :=
  fun {X} {Ω} [Field Ω] ξ p q => ¬unitAt ξ q ↑p

theorem main : ∀ {X : AlgebraicGeometry.Scheme} {Ω : Type} [inst : Field Ω]
  {ξ : AlgebraicGeometry.Spec ↧Ω ⟶ X} {q : Cpt ξ},
  (∀ (r : ℕ), Nat.Prime r → ¬InFibre ξ r q) →
    ∀ (n : ℕ), n ≠ 0 → unitAt ξ q ↑n := by
  intro X Ω inst ξ q hq n hn
  have key : ∀ m : ℕ, m ≠ 0 → unitAt ξ q (m : Ω) := by
    intro m
    induction m using Nat.recOnMul with
    | zero => intro h; exact absurd rfl h
    | one =>
      intro _
      refine ⟨by simp, ?_, ?_⟩
      · simp [(regAt ξ q).one_mem]
      · simp [(regAt ξ q).one_mem]
    | prime p hp =>
      intro _
      have := hq p hp
      unfold InFibre at this
      exact not_not.mp this
    | mul a b ha hb =>
      intro hab
      have ha0 : a ≠ 0 := by rintro rfl; simp at hab
      have hb0 : b ≠ 0 := by rintro rfl; simp at hab
      obtain ⟨a1, a2, a3⟩ := ha ha0
      obtain ⟨b1, b2, b3⟩ := hb hb0
      refine ⟨?_, ?_, ?_⟩
      · push_cast; exact mul_ne_zero a1 b1
      · push_cast; exact Subring.mul_mem _ a2 b2
      · push_cast; rw [mul_inv]; exact Subring.mul_mem _ a3 b3
  exact key n hn

end UpperTheory.Reformulated.B.RegularUnitPoints
end

section

namespace UpperTheory.Reformulated.B.GenericMap

theorem aux1 : ∀ {Ω : Type} [inst : Field Ω], IsLocalRing Ω := by
  intro Ω inst
  infer_instance

noncomputable def genPt : {X : AlgebraicGeometry.Scheme} →
  {Ω : Type} → [inst : Field Ω] → (AlgebraicGeometry.Spec ↧Ω ⟶ X) → ↥X :=
  fun {X} {Ω} [Field Ω] ξ => ξ (IsLocalRing.closedPoint Ω)

noncomputable def Cpt : {X : AlgebraicGeometry.Scheme} →
  {Ω : Type} → [inst : Field Ω] → (AlgebraicGeometry.Spec ↧Ω ⟶ X) → Type :=
  fun {X} {Ω} [Field Ω] ξ => { p // genPt ξ ⤳ p }

theorem aux4 : ∀ {X : AlgebraicGeometry.Scheme} {Ω : Type} [inst : Field Ω]
  (ξ : AlgebraicGeometry.Spec ↧Ω ⟶ X) (p : Cpt ξ),
  genPt ξ ⤳ p.val := by
  intro X Ω inst ξ p
  exact p.2

theorem aux5 : ∀ {Ω : Type} [inst : Field Ω], IsLocalRing (CommRingCat.of Ω) := by
  intro Ω inst
  infer_instance

noncomputable def genMap : {X : AlgebraicGeometry.Scheme} →
  {Ω : Type} →
    [inst : Field Ω] →
      (ξ : AlgebraicGeometry.Spec ↧Ω ⟶ X) →
        (p : Cpt ξ) → ↑(X.presheaf.stalk p.val) →+* Ω :=
  fun {X} {Ω} [Field Ω] ξ p =>
    CommRingCat.Hom.hom
      (CategoryTheory.CategoryStruct.comp (X.presheaf.stalkSpecializes (aux4 ξ p))
        (AlgebraicGeometry.Scheme.stalkClosedPointTo ξ))

noncomputable def regAt : {X : AlgebraicGeometry.Scheme} →
  {Ω : Type} →
    [inst : Field Ω] → (ξ : AlgebraicGeometry.Spec ↧Ω ⟶ X) → Cpt ξ → Subring Ω :=
  fun {X} {Ω} [Field Ω] ξ p => (genMap ξ p).range

noncomputable def unitAt : {X : AlgebraicGeometry.Scheme} →
  {Ω : Type} →
    [inst : Field Ω] → (ξ : AlgebraicGeometry.Spec ↧Ω ⟶ X) → Cpt ξ → Ω → Prop :=
  fun {X} {Ω} [Field Ω] ξ p a =>
    a ≠ 0 ∧ a ∈ regAt ξ p ∧ a⁻¹ ∈ regAt ξ p

noncomputable def InFibre : {X : AlgebraicGeometry.Scheme} →
  {Ω : Type} →
    [inst : Field Ω] → (ξ : AlgebraicGeometry.Spec ↧Ω ⟶ X) → ℕ → Cpt ξ → Prop :=
  fun {X} {Ω} [Field Ω] ξ p q => ¬unitAt ξ q ↑p

noncomputable def Char0 : {X : AlgebraicGeometry.Scheme} →
  {Ω : Type} →
    [inst : Field Ω] → (ξ : AlgebraicGeometry.Spec ↧Ω ⟶ X) → Cpt ξ → Prop :=
  fun {X} {Ω} [Field Ω] ξ p => ∀ (r : ℕ), Nat.Prime r → ¬InFibre ξ r p

namespace Hlp
private theorem units_nat {Ω : Type} [Field Ω] (S : Subring Ω)
    (hp : ∀ r : ℕ, r.Prime → ((r : Ω) ≠ 0 ∧ (r : Ω) ∈ S ∧ (r : Ω)⁻¹ ∈ S)) :
    ∀ n : ℕ, n ≠ 0 → ((n : Ω) ≠ 0 ∧ (n : Ω) ∈ S ∧ (n : Ω)⁻¹ ∈ S) := by
  intro n
  induction n using Nat.recOnMul with
  | zero => intro h; exact absurd rfl h
  | one => intro _; simp [S.one_mem]
  | prime p hpp => intro _; exact hp p hpp
  | mul a b ha hb =>
    intro hab
    have ha0 : a ≠ 0 := fun h => hab (by simp [h])
    have hb0 : b ≠ 0 := fun h => hab (by simp [h])
    obtain ⟨a1, a2, a3⟩ := ha ha0
    obtain ⟨b1, b2, b3⟩ := hb hb0
    refine ⟨by push_cast; exact mul_ne_zero a1 b1, by push_cast; exact S.mul_mem a2 b2, ?_⟩
    push_cast; rw [mul_inv]; exact S.mul_mem a3 b3
end Hlp

theorem main : ∀ {X : AlgebraicGeometry.Scheme} {Ω : Type} [inst : Field Ω]
  {ξ : AlgebraicGeometry.Spec ↧Ω ⟶ X} {q : Cpt ξ},
  Char0 ξ q →
    ∀ (n : ℕ), n ≠ 0 → unitAt ξ q ↑n := by
  intro X Ω inst ξ q hq n hn
  have key := Hlp.units_nat (regAt ξ q)
    (fun r hr => by
      have := hq r hr
      unfold InFibre at this
      exact not_not.mp this) n hn
  exact key

end UpperTheory.Reformulated.B.GenericMap
end

section

namespace SupNormSqLeSumNormSq

private lemma entry_le {m n : ℕ} (x : Fin m → Fin n → ℂ) (a : Fin m) (j : Fin n) :
    ‖x a j‖ ≤ Real.sqrt (∑ a : Fin m, ∑ j : Fin n, ‖x a j‖ ^ (2 : ℕ)) := by
  apply Real.le_sqrt_of_sq_le
  calc ‖x a j‖ ^ (2 : ℕ) ≤ ∑ j : Fin n, ‖x a j‖ ^ (2 : ℕ) :=
        Finset.single_le_sum (f := fun j => ‖x a j‖ ^ (2 : ℕ)) (fun _ _ => by positivity)
          (Finset.mem_univ j)
    _ ≤ ∑ a : Fin m, ∑ j : Fin n, ‖x a j‖ ^ (2 : ℕ) :=
        Finset.single_le_sum (f := fun a => ∑ j : Fin n, ‖x a j‖ ^ (2 : ℕ))
          (fun _ _ => by positivity) (Finset.mem_univ a)

end SupNormSqLeSumNormSq

theorem UpperTheory.Reformulated.B.Yhb3.main :
    ∀ {m n : ℕ} (x : Fin m → Fin n → ℂ), ‖x‖ ^ (2 : ℕ) ≤ ∑ a : Fin m, ∑ j : Fin n, ‖x a j‖ ^ (2 : ℕ) := by
  intro m n x
  have hS : 0 ≤ ∑ a : Fin m, ∑ j : Fin n, ‖x a j‖ ^ (2 : ℕ) := by positivity
  have h : ‖x‖ ≤ Real.sqrt (∑ a : Fin m, ∑ j : Fin n, ‖x a j‖ ^ (2 : ℕ)) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun a => ?_
    exact (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun j => SupNormSqLeSumNormSq.entry_le x a j
  calc ‖x‖ ^ (2 : ℕ) ≤ (Real.sqrt (∑ a : Fin m, ∑ j : Fin n, ‖x a j‖ ^ (2 : ℕ))) ^ (2 : ℕ) :=
        pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = _ := Real.sq_sqrt hS
end

section

theorem UpperTheory.Reformulated.B.DYka1.main :
    ∀ {m n : ℕ} (x : Fin m → Fin n → ℂ), ‖x‖ ^ (2 : ℕ) ≤ ∑ a : Fin m, ∑ i : Fin n, ‖x a i‖ ^ (2 : ℕ) := by
  intro m n x
  have hS : 0 ≤ ∑ a : Fin m, ∑ i : Fin n, ‖x a i‖ ^ (2 : ℕ) :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun i _ => by positivity
  have hle : ‖x‖ ≤ Real.sqrt (∑ a : Fin m, ∑ i : Fin n, ‖x a i‖ ^ (2 : ℕ)) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun a => ?_
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    apply Real.le_sqrt_of_sq_le
    calc ‖x a i‖ ^ (2 : ℕ) ≤ ∑ j : Fin n, ‖x a j‖ ^ (2 : ℕ) :=
          Finset.single_le_sum (f := fun j : Fin n => ‖x a j‖ ^ (2 : ℕ))
            (fun j _ => by positivity) (Finset.mem_univ i)
      _ ≤ ∑ b : Fin m, ∑ j : Fin n, ‖x b j‖ ^ (2 : ℕ) :=
          Finset.single_le_sum (f := fun b : Fin m => ∑ j : Fin n, ‖x b j‖ ^ (2 : ℕ))
            (fun b _ => Finset.sum_nonneg fun j _ => by positivity) (Finset.mem_univ a)
  calc ‖x‖ ^ (2 : ℕ) ≤ (Real.sqrt (∑ a : Fin m, ∑ i : Fin n, ‖x a i‖ ^ (2 : ℕ))) ^ (2 : ℕ) := by
        gcongr
    _ = ∑ a : Fin m, ∑ i : Fin n, ‖x a i‖ ^ (2 : ℕ) := Real.sq_sqrt hS
end

section

theorem UpperTheory.Reformulated.B.SquareNormBound.sq_norm_le :
    ∀ {m n : ℕ} (x : Fin m → Fin n → ℂ),
    ‖x‖ ^ (2 : ℕ) ≤ ∑ a : Fin m, ∑ i : Fin n, ‖x a i‖ ^ (2 : ℕ) := by
  intro m n x
  have hS0 : 0 ≤ ∑ a : Fin m, ∑ i : Fin n, ‖x a i‖ ^ (2 : ℕ) :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun i _ => by positivity
  have h : ‖x‖ ≤ Real.sqrt (∑ a : Fin m, ∑ i : Fin n, ‖x a i‖ ^ (2 : ℕ)) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun a =>
      (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    apply Real.le_sqrt_of_sq_le
    calc ‖x a i‖ ^ (2 : ℕ) ≤ ∑ j : Fin n, ‖x a j‖ ^ (2 : ℕ) :=
          Finset.single_le_sum (f := fun j => ‖x a j‖ ^ (2 : ℕ))
            (fun _ _ => by positivity) (Finset.mem_univ i)
      _ ≤ ∑ b : Fin m, ∑ j : Fin n, ‖x b j‖ ^ (2 : ℕ) :=
          Finset.single_le_sum (f := fun b => ∑ j : Fin n, ‖x b j‖ ^ (2 : ℕ))
            (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ a)
  calc ‖x‖ ^ (2 : ℕ)
      ≤ (Real.sqrt (∑ a : Fin m, ∑ i : Fin n, ‖x a i‖ ^ (2 : ℕ))) ^ (2 : ℕ) := by gcongr
    _ = ∑ a : Fin m, ∑ i : Fin n, ‖x a i‖ ^ (2 : ℕ) := Real.sq_sqrt hS0
end

section

namespace UpperTheory.Reformulated.B.Qh27

open scoped ContDiff Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable def Jm : {n : ℕ} → (Fin n → Bool) → Matrix (Fin n) (Fin n) ℂ :=
  fun {_} ε ↦ Matrix.diagonal fun a ↦ if ε a then 1 else -1

noncomputable def inUJ : {n : ℕ} → (Fin n → Bool) → Matrix (Fin n) (Fin n) ℂ → Prop :=
  fun {_} ε g ↦ gᴴ * Jm ε * g = Jm ε

noncomputable def SmoothOnG :
    {n : ℕ} → (Fin n → Bool) → (Matrix (Fin n) (Fin n) ℂ → ℂ) → Prop :=
  fun {n} ε f ↦
    ∀ g₀ : Matrix (Fin n) (Fin n) ℂ, inUJ ε g₀ →
      ∃ (U : Set (Matrix (Fin n) (Fin n) ℂ)) (F : Matrix (Fin n) (Fin n) ℂ → ℂ),
        IsOpen U ∧ g₀ ∈ U ∧ ContDiffOn ℝ ∞ F U ∧ ∀ g ∈ U, inUJ ε g → f g = F g

theorem smooth_on_group_sum.{u_1} :
    ∀ {n : ℕ} {ε : Fin n → Bool} {ι : Type u_1} (s : Finset ι) (f : ι → Matrix (Fin n) (Fin n) ℂ → ℂ),
      (∀ i ∈ s, SmoothOnG ε (f i)) → SmoothOnG ε (fun x ↦ ∑ i ∈ s, f i x) := by
  intro n ε ι s f h g₀ hg₀
  choose! U F hU hmem hF heq using fun i hi ↦ h i hi g₀ hg₀
  refine ⟨⋂ i ∈ s, U i, fun x ↦ ∑ i ∈ s, F i x, isOpen_biInter_finset hU,
    Set.mem_iInter₂.2 hmem, ?_, ?_⟩
  · exact ContDiffOn.sum fun i hi ↦ (hF i hi).mono (Set.biInter_subset_of_mem (Finset.mem_coe.2 hi))
  · intro g hg hgu
    exact Finset.sum_congr rfl fun i hi ↦ heq i hi g (Set.mem_iInter₂.1 hg i hi) hgu

end UpperTheory.Reformulated.B.Qh27
end

section

namespace UpperTheory.Reformulated.B.Qf26

open scoped ContDiff Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable def Jm : {n : ℕ} → (Fin n → Bool) → Matrix (Fin n) (Fin n) ℂ :=
  fun {_} ε ↦ Matrix.diagonal fun a ↦ if ε a then 1 else -1

noncomputable def inUJ : {n : ℕ} → (Fin n → Bool) → Matrix (Fin n) (Fin n) ℂ → Prop :=
  fun {_} ε g ↦ gᴴ * Jm ε * g = Jm ε

noncomputable def SmoothOnG :
    {n : ℕ} → (Fin n → Bool) → (Matrix (Fin n) (Fin n) ℂ → ℂ) → Prop :=
  fun {n} ε f ↦
    ∀ g₀ : Matrix (Fin n) (Fin n) ℂ, inUJ ε g₀ →
      ∃ (U : Set (Matrix (Fin n) (Fin n) ℂ)) (F : Matrix (Fin n) (Fin n) ℂ → ℂ),
        IsOpen U ∧ g₀ ∈ U ∧ ContDiffOn ℝ ∞ F U ∧ ∀ g ∈ U, inUJ ε g → f g = F g

theorem tmA_sm_sum.{u_1} :
    ∀ {n : ℕ} {ε : Fin n → Bool} {ι : Type u_1} (s : Finset ι) (F : ι → Matrix (Fin n) (Fin n) ℂ → ℂ),
      (∀ i ∈ s, SmoothOnG ε (F i)) → SmoothOnG ε (fun x ↦ ∑ i ∈ s, F i x) := by
  intro n ε ι s F h g₀ hg
  classical
  choose! U G hUo hUm hG hE using fun i hi => h i hi g₀ hg
  refine ⟨⋂ i ∈ s, U i, fun x => ∑ i ∈ s, G i x, isOpen_biInter_finset hUo, ?_, ?_, ?_⟩
  · exact Set.mem_iInter₂.2 hUm
  · exact ContDiffOn.sum fun i hi => (hG i hi).mono (Set.biInter_subset_of_mem hi)
  · intro g hgU hgJ
    exact Finset.sum_congr rfl fun i hi => hE i hi g (Set.mem_iInter₂.1 hgU i hi) hgJ

end UpperTheory.Reformulated.B.Qf26
end

section

theorem UpperTheory.Reformulated.B.Yhd5.main :
    ∀ {n : ℕ} {U : Set (Fin n → ℂ)} {ι : Type} (u : Finset ι) {f : ι → (Fin n → ℂ) → ℂ},
      (∀ i ∈ u, DifferentiableOn ℂ (f i) U) → DifferentiableOn ℂ (fun (t : Fin n → ℂ) ↦ ∏ i ∈ u, f i t) U := by
  intro n U ι u f h
  classical
  induction u using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact differentiableOn_const (1 : ℂ)
  | insert a s ha ih =>
    have h1 : DifferentiableOn ℂ (f a) U := h a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    simp only [Finset.prod_insert ha]
    exact h1.mul h2
end
