module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle051
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitLemmaResiduallyUnipotentCayleyTransform
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle064
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitLemmaResiduallyUnipotentViaCayley
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle101
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle616
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle014

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.GaloisCartDesc

theorem epi_of_isGaloisCover {X Y : Scheme.{0}} {Ga : Type} [Group Ga] {ρ : Ga → (X ⟶ X)} {π : X ⟶ Y}
    (h : GlobalTheory.ZM.IsGaloisCover Ga ρ π) : Epi π := by
  refine ⟨fun {Z} g₁ g₂ e ↦ ?_⟩
  obtain ⟨f', -, hu⟩ := h.existsUnique_desc (π ≫ g₁) (fun a ↦ by rw [← Category.assoc, h.inv])
  exact (hu g₁ rfl).trans (hu g₂ e.symm).symm

theorem epi_pullback_fst {X Y : Scheme.{0}} {Ga : Type} [Group Ga] {ρ : Ga → (X ⟶ X)} {π : X ⟶ Y}
    (h : GlobalTheory.ZM.IsGaloisCover Ga ρ π) {T : Scheme.{0}} (t : T ⟶ Y) : Epi (pullback.fst t π) := by
  let ρ' : Ga → (pullback t π ⟶ pullback t π) := fun a ↦
    pullback.map t π t π (𝟙 _) (ρ a) (𝟙 _) (by simp) (by simp [h.inv])
  have hg : GlobalTheory.ZM.IsGaloisCover Ga ρ' (pullback.fst t π) :=
    by
      let hp := (IsPullback.of_hasPullback t π).flip
      have hu : ∀ a, ρ' a ≫ pullback.snd t π = pullback.snd t π ≫ ρ a :=
        fun a ↦ by simp only [ρ', pullback.map, pullback.lift_snd]
      exact ((GlobalTheory.ZM.galoisCover_descent _ _ _ _ _ h).2.2 _ _ _ _ _ _ hu hp.w).2 hp
        (fun a ↦ by simp only [ρ', pullback.map, pullback.lift_fst, Category.comp_id])
  exact epi_of_isGaloisCover hg

theorem isGrpPullback_of_galoisCover : ∀ (S S₁ Y : Scheme.{0}) (π₁ : S₁ ⟶ S) (Ga : Type) [Group Ga] (ρ₁ : Ga → (S₁ ⟶ S₁)) (f : S ⟶ Y)
    (A' : Over S₁) (A : Over S) (B : Over Y) [GrpObj A'] [GrpObj A] [GrpObj B] (φ₁ : A'.left ⟶ A.left)
    (ψ : A'.left ⟶ B.left) (φ : A.left ⟶ B.left), GlobalTheory.ZM.IsGaloisCover Ga ρ₁ π₁ → IsGrpPullback A' A π₁ φ₁ →
    IsGrpPullback A' B (π₁ ≫ f) ψ → φ₁ ≫ φ = ψ → IsGrpPullback A B f φ := by
  intro S S₁ Y π₁ Ga _ ρ₁ f A' A B _ _ _ φ₁ ψ φ hG hφ₁ hψ hφ

  let τ : Ga → (A'.left ⟶ A'.left) := fun a ↦
    hφ₁.1.lift φ₁ (A'.hom ≫ ρ₁ a) (by rw [hφ₁.1.w, Category.assoc, hG.inv])
  have hτ₁ : ∀ a, τ a ≫ φ₁ = φ₁ := fun a ↦ hφ₁.1.lift_fst _ _ _
  have hτ₂ : ∀ a, τ a ≫ A'.hom = A'.hom ≫ ρ₁ a := fun a ↦ hφ₁.1.lift_snd _ _ _
  have gφ₁ : GlobalTheory.ZM.IsGaloisCover Ga τ φ₁ := ((GlobalTheory.ZM.galoisCover_descent _ _ _ _ _ hG).2.2 _ _ _ _ _ _ hτ₂ hφ₁.1.flip.w).2 hφ₁.1.flip hτ₁
  have eφ₁ : Epi φ₁ := epi_of_isGaloisCover gφ₁

  have w : φ ≫ B.hom = A.hom ≫ f := by
    rw [← cancel_epi φ₁, reassoc_of% hφ, hψ.1.w, ← reassoc_of% hφ₁.1.w]

  let q : A'.left ⟶ pullback B.hom f := pullback.lift ψ (A'.hom ≫ π₁) (by rw [hψ.1.w, Category.assoc])
  have hq₁ : q ≫ pullback.fst B.hom f = ψ := pullback.lift_fst _ _ _
  have hq₂ : q ≫ pullback.snd B.hom f = A'.hom ≫ π₁ := pullback.lift_snd _ _ _
  have hsq : IsPullback q A'.hom (pullback.snd B.hom f) π₁ := by
    refine IsPullback.of_right ?_ hq₂ (IsPullback.of_hasPullback B.hom f)
    rw [hq₁]
    exact hψ.1
  have hτq : ∀ a, τ a ≫ q = q := fun a ↦ by
    apply pullback.hom_ext
    · rw [Category.assoc, hq₁, ← hφ, reassoc_of% hτ₁ a]
    · rw [Category.assoc, hq₂, reassoc_of% hτ₂ a, hG.inv]
  have gq : GlobalTheory.ZM.IsGaloisCover Ga τ q := ((GlobalTheory.ZM.galoisCover_descent _ _ _ _ _ hG).2.2 _ _ _ _ _ _ hτ₂ hsq.flip.w).2 hsq.flip hτq
  have eq : Epi q := epi_of_isGaloisCover gq
  obtain ⟨d, hd, -⟩ := gq.existsUnique_desc φ₁ hτ₁
  let c : A.left ⟶ pullback B.hom f := pullback.lift φ A.hom w
  have hc : φ₁ ≫ c = q := by
    apply pullback.hom_ext
    · simp only [c, Category.assoc, hq₁]
      rw [pullback.lift_fst, hφ]
    · simp only [c, Category.assoc, hq₂]
      rw [pullback.lift_snd, hφ₁.1.w]
  have hcd : c ≫ d = 𝟙 _ := by rw [← cancel_epi φ₁, reassoc_of% hc, hd, Category.comp_id]
  have hdc : d ≫ c = 𝟙 _ := by rw [← cancel_epi q, reassoc_of% hd, hc, Category.comp_id]
  let i : A.left ≅ pullback B.hom f := ⟨c, d, hcd, hdc⟩
  refine ⟨IsPullback.of_iso_pullback ⟨w⟩ i (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _), ?_⟩

  intro T x y x₀ y₀ hx hy
  let e : pullback T.hom π₁ ⟶ T.left := pullback.fst T.hom π₁
  have ee : Epi e := epi_pullback_fst hG T.hom
  let T₁ : Over S₁ := Over.mk (pullback.snd T.hom π₁)
  let j : Over.mk (T₁.hom ≫ π₁) ⟶ T := Over.homMk e (by simp [T₁, e, pullback.condition])
  let j' : Over.mk (T₁.hom ≫ π₁ ≫ f) ⟶ Over.mk (T.hom ≫ f) :=
    Over.homMk e (by simp [T₁, e, pullback.condition_assoc])
  have lift : ∀ z : T ⟶ A, ∃ z₁ : T₁ ⟶ A', z₁.left ≫ φ₁ = e ≫ z.left := fun z ↦
    ⟨Over.homMk (hφ₁.1.lift (e ≫ z.left) (pullback.snd T.hom π₁)
      (by simp [e, pullback.condition])) (hφ₁.1.lift_snd _ _ _), hφ₁.1.lift_fst _ _ _⟩
  obtain ⟨x₁, hx₁⟩ := lift x
  obtain ⟨y₁, hy₁⟩ := lift y
  have a₁ : ((j ≫ x) * (j ≫ y)).left = (x₁ * y₁).left ≫ φ₁ :=
    hφ₁.2 T₁ x₁ y₁ (j ≫ x) (j ≫ y) (by simp [j, hx₁]) (by simp [j, hy₁])
  have a₂ : ((j' ≫ x₀) * (j' ≫ y₀)).left = (x₁ * y₁).left ≫ ψ :=
    hψ.2 T₁ x₁ y₁ (j' ≫ x₀) (j' ≫ y₀) (by simp [j', hx, ← hφ, reassoc_of% hx₁])
      (by simp [j', hy, ← hφ, reassoc_of% hy₁])
  rw [← MonObj.comp_mul] at a₁ a₂
  rw [← cancel_epi e]
  have b₁ : e ≫ (x * y).left = (x₁ * y₁).left ≫ φ₁ := by simpa [j] using a₁
  have b₂ : e ≫ (x₀ * y₀).left = (x₁ * y₁).left ≫ ψ := by simpa [j'] using a₂
  rw [b₂, reassoc_of% b₁, hφ]

end GlobalTheory.GaloisCartDesc
end
end

section

noncomputable section

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma.CongruenceCayley

open GlobalTheory.UnitLemma.CayleyCase

theorem inv_small {O A : Type} [CommRing O] [IsLocalRing O] [CommRing A] [Algebra O A] (g : A) (α β : O)
    (hg : IsIntegral O g) (hα : IsUnit α) (hβ : β ∈ IsLocalRing.maximalIdeal O) :
    ∃ w ∈ Algebra.adjoin O ({g} : Set A), (algebraMap O A α + algebraMap O A β * g) * w = 1 := by
  obtain ⟨Q, hQm, hQ⟩ := hg
  rw [← aeval_def] at hQ
  set D := algebraMap O A α + algebraMap O A β * g with hD
  set n := Q.natDegree
  let R : O[X] := ∑ i ∈ Finset.range (n + 1), C (Q.coeff i) * (X - C α) ^ i * C β ^ (n - i)
  have hR : aeval D R = 0 := by
    have : aeval D R = algebraMap O A β ^ n * aeval g Q := by
      conv_rhs => rw [aeval_eq_sum_range, Finset.mul_sum]

      simp only [R, map_sum, map_mul, map_pow, aeval_C, map_sub, aeval_X]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hin : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      rw [Algebra.smul_def, hD]
      have : algebraMap O A β ^ n = algebraMap O A β ^ i * algebraMap O A β ^ (n - i) := by
        rw [← pow_add, Nat.add_sub_cancel' hin]
      rw [this]; ring
    rw [this, hQ, mul_zero]
  have hR0 : IsUnit (R.eval 0) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    have hb : IsLocalRing.residue O β = 0 := (IsLocalRing.residue_eq_zero_iff _).2 hβ
    have ha : IsLocalRing.residue O α ≠ 0 := (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hα

    simp only [R, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_sub, eval_X, map_sum, map_mul, map_pow,
    map_sub, map_zero, hb]
    rw [Finset.sum_eq_single n]
    · simp [n, hQm.coeff_natDegree, ha]
    · intro i hi hin
      have : 0 < n - i := Nat.sub_pos_of_lt (lt_of_le_of_ne (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) hin)
      rw [zero_pow this.ne', mul_zero]
    · intro h; exact absurd (Finset.mem_range.2 (Nat.lt_succ_self n)) h
  obtain ⟨w, hw, hDw⟩ := sub_inv_mem D 0 R hR hR0
  rw [map_zero, sub_zero] at hDw
  refine ⟨w, ?_, hDw⟩
  have hDmem : D ∈ Algebra.adjoin O ({g} : Set A) :=
    add_mem (Subalgebra.algebraMap_mem _ _) (mul_mem (Subalgebra.algebraMap_mem _ _) (Algebra.subset_adjoin rfl))
  exact Algebra.adjoin_le (Set.singleton_subset_iff.2 hDmem) hw

theorem adjoin_both {O A : Type} [CommRing O] [IsLocalRing O] [CommRing A] [Algebra O A] (g Y : A) (α β γ : O)
    (hg : IsIntegral O g) (hα : IsUnit α) (hβ : β ∈ IsLocalRing.maximalIdeal O) (hγ : IsUnit γ)
    (hY : Y * (algebraMap O A α + algebraMap O A β * g) = algebraMap O A γ * g) :
    Y ∈ Algebra.adjoin O ({g} : Set A) ∧ g ∈ Algebra.adjoin O ({Y} : Set A) := by
  obtain ⟨w, hw, hDw⟩ := inv_small g α β hg hα hβ
  have h1 : Y ∈ Algebra.adjoin O ({g} : Set A) := by
    have e : Y = algebraMap O A γ * g * w := by linear_combination (-Y) * hDw + w * hY
    rw [e]
    exact mul_mem (mul_mem (Subalgebra.algebraMap_mem _ _) (Algebra.subset_adjoin rfl)) hw
  refine ⟨h1, ?_⟩
  have hYi : IsIntegral O Y := IsIntegral.of_mem_of_fg _ hg.fg_adjoin_singleton Y h1
  have hβ' : -β ∈ IsLocalRing.maximalIdeal O := neg_mem hβ
  obtain ⟨v, hv, hEv⟩ := inv_small Y γ (-β) hYi hγ hβ'
  have e : g = algebraMap O A α * Y * v := by
    rw [map_neg] at hEv
    linear_combination (-g) * hEv - v * hY
  rw [e]
  exact mul_mem (mul_mem (Subalgebra.algebraMap_mem _ _) (Algebra.subset_adjoin rfl)) hv

variable {K : UQ}

theorem congruence_selfadj (B : InvAlg K) (a x y : K.O) (ha0 : a ≠ 0)
    (hac : K.c (algebraMap K.O K.E a) = algebraMap K.O K.E a)
    (hxy : K.c (algebraMap K.O K.E x) = algebraMap K.O K.E y)
    (hu : (1 + algebraMap K.O B.A a * B.g) * B.σ (1 + algebraMap K.O B.A a * B.g) = 1)
    (Y w : B.A)
    (hw : (algebraMap K.O B.A (x - y) + algebraMap K.O B.A (x * a) * B.g) * w = 1)
    (hY : Y * (algebraMap K.O B.A (x - y) + algebraMap K.O B.A (x * a) * B.g) =
      algebraMap K.O B.A (x * y) * B.g) :
    B.σ Y = Y := by
  have sx : B.σ (algebraMap K.O B.A x) = algebraMap K.O B.A y := by
    rw [σ_algebraMap, hxy, ← IsScalarTower.algebraMap_apply]
  have sy : B.σ (algebraMap K.O B.A y) = algebraMap K.O B.A x := by
    rw [σ_algebraMap, ← hxy, K.c_c, ← IsScalarTower.algebraMap_apply]
  have sa : B.σ (algebraMap K.O B.A a) = algebraMap K.O B.A a := by
    rw [σ_algebraMap, hac, ← IsScalarTower.algebraMap_apply]
  have h1 := congrArg B.σ hY
  simp only [map_mul, map_sub, map_add (f := _), sx, sy, sa] at h1 hY hw
  rw [map_add (f := _), map_one, map_mul, sa] at hu
  set G := B.g
  set S := B.σ B.g
  set xA := algebraMap K.O B.A x
  set yA := algebraMap K.O B.A y
  set aA := algebraMap K.O B.A a
  have key : (B.σ Y - Y) * (xA - yA + xA * aA * G) * aA = 0 := by
    linear_combination (-aA * (1 + aA * G)) * h1 - (xA * yA - aA * B.σ Y * yA) * hu - aA * hY
  have key2 : (B.σ Y - Y) * aA = 0 := by
    calc (B.σ Y - Y) * aA = (B.σ Y - Y) * (xA - yA + xA * aA * G) * aA * w := by
          linear_combination (-(B.σ Y - Y) * aA) * hw
      _ = 0 := by rw [key, zero_mul]
  have hae : algebraMap K.O K.E a ≠ 0 := by
    intro h; exact ha0 (IsFractionRing.injective K.O K.E (by rw [h, map_zero]))
  have : (algebraMap K.O K.E a) • (B.σ Y - Y) = 0 := by
    rw [Algebra.smul_def, ← IsScalarTower.algebraMap_apply, mul_comm]; exact key2
  exact sub_eq_zero.1 ((smul_eq_zero.1 this).resolve_left hae)

end GlobalTheory.UnitLemma.CongruenceCayley

namespace GlobalTheory.UnitLemma.CongruenceCayley

open GlobalTheory.UnitLemma.CayleyCase

theorem identity_of_principal_congruence : UnitLemmaLie → ∀ (K : UQ) (a : K.O), K.Small a →
    ∀ B₁ B₂ : InvAlg K,
    (1 + algebraMap K.O B₁.A a * B₁.g) * B₁.σ (1 + algebraMap K.O B₁.A a * B₁.g) = 1 →
    (1 + algebraMap K.O B₂.A a * B₂.g) * B₂.σ (1 + algebraMap K.O B₂.A a * B₂.g) = 1 →
    (B₁.P * B₂.P).Separable → InvAlg.Identity B₁ B₂ := by
  intro hL K a ha B₁ B₂ hu₁ hu₂ hsep
  by_cases hint : IsIntegral K.O B₁.g ∧ IsIntegral K.O B₂.g
  swap
  · obtain ⟨h1, h2⟩ := kapSum_eq_zero_and_stSum_mul_eq_zero_of_not_isIntegral K B₁ B₂ hint
    unfold InvAlg.Identity
    rw [h1, h2, mul_zero]
  obtain ⟨i₁, i₂⟩ := hint
  obtain ⟨ha0, ham, hac⟩ := ha
  obtain ⟨x, y, hxy, hm⟩ := K.c_res
  have hyx : K.c (algebraMap K.O K.E y) = algebraMap K.O K.E x := by rw [← hxy, K.c_c]
  have hxu : IsUnit x := by
    by_contra hx
    have hy : ¬ IsUnit y := fun hy => hx (CayleyAny.isUnit_of_conj K x y hxy hy)
    exact hm (Ideal.sub_mem _ ((IsLocalRing.mem_maximalIdeal _).2 hx) ((IsLocalRing.mem_maximalIdeal _).2 hy))
  have hyu : IsUnit y := CayleyAny.isUnit_of_conj K y x hyx hxu
  have hxyu : IsUnit (x - y) := by
    by_contra h; exact hm ((IsLocalRing.mem_maximalIdeal _).2 h)
  have hβ : x * a ∈ IsLocalRing.maximalIdeal K.O := Ideal.mul_mem_left _ _ ham
  have hγ : IsUnit (x * y) := hxu.mul hyu
  obtain ⟨w₁, -, hw₁⟩ := inv_small B₁.g (x - y) (x * a) i₁ hxyu hβ
  obtain ⟨w₂, -, hw₂⟩ := inv_small B₂.g (x - y) (x * a) i₂ hxyu hβ
  set Y₁ := algebraMap K.O B₁.A (x * y) * B₁.g * w₁ with hY₁d
  set Y₂ := algebraMap K.O B₂.A (x * y) * B₂.g * w₂ with hY₂d
  have hY₁ : Y₁ * (algebraMap K.O B₁.A (x - y) + algebraMap K.O B₁.A (x * a) * B₁.g) =
      algebraMap K.O B₁.A (x * y) * B₁.g := by
    rw [hY₁d]; linear_combination (algebraMap K.O B₁.A (x * y) * B₁.g) * hw₁
  have hY₂ : Y₂ * (algebraMap K.O B₂.A (x - y) + algebraMap K.O B₂.A (x * a) * B₂.g) =
      algebraMap K.O B₂.A (x * y) * B₂.g := by
    rw [hY₂d]; linear_combination (algebraMap K.O B₂.A (x * y) * B₂.g) * hw₂
  have adj₁ := adjoin_both B₁.g Y₁ (x - y) (x * a) (x * y) i₁ hxyu hβ hγ hY₁
  have adj₂ := adjoin_both B₂.g Y₂ (x - y) (x * a) (x * y) i₂ hxyu hβ hγ hY₂
  have iP : IsIntegral K.O ((B₁.g, B₂.g) : B₁.A × B₂.A) := IsIntegral.pair i₁ i₂
  have hYp : ((Y₁, Y₂) : B₁.A × B₂.A) * (algebraMap K.O (B₁.A × B₂.A) (x - y) +
      algebraMap K.O (B₁.A × B₂.A) (x * a) * (B₁.g, B₂.g)) =
      algebraMap K.O (B₁.A × B₂.A) (x * y) * (B₁.g, B₂.g) :=
    Prod.ext hY₁ hY₂
  have adjP := adjoin_both ((B₁.g, B₂.g) : B₁.A × B₂.A) (Y₁, Y₂) (x - y) (x * a) (x * y) iP hxyu hβ hγ hYp
  have st₁ := stable_iff B₁.g Y₁ adj₁
  have st₂ := stable_iff B₂.g Y₂ adj₂
  have stP := stable_iff ((B₁.g, B₂.g) : B₁.A × B₂.A) (Y₁, Y₂) adjP

  have sa₁ := congruence_selfadj B₁ a x y ha0 hac hxy hu₁ Y₁ w₁ hw₁ hY₁
  have sa₂ := congruence_selfadj B₂ a x y ha0 hac hxy hu₂ Y₂ w₂ hw₂ hY₂
  have hsepP : (LinearMap.mulLeft K.E ((B₁.g, B₂.g) : B₁.A × B₂.A)).charpoly.Separable := by
    have := Orbit.prod_P B₁ B₂
    rw [← this] at hsep; exact hsep
  have hsepC : ((withG B₁ Y₁).P * (withG B₂ Y₂).P).Separable := by
    rw [← Orbit.prod_P]
    have := separable_of_adjoin (E := K.E) (A := B₁.A × B₂.A) (B₁.g, B₂.g) (Y₁, Y₂)
      (mem_adjoin_of_mem (O := K.O) adjP.1) (mem_adjoin_of_mem (O := K.O) adjP.2) hsepP
    exact this
  have hId := hL K (withG B₁ Y₁) (withG B₂ Y₂) sa₁ sa₂ hsepC

  have hr : resultant B₁.P B₂.P ≠ 0 :=
    ((isUnit_resultant_iff_isCoprime (LinearMap.charpoly_monic _)).2 hsep.isCoprime).ne_zero
  have hr' : resultant (withG B₁ Y₁).P (withG B₂ Y₂).P ≠ 0 :=
    ((isUnit_resultant_iff_isCoprime (LinearMap.charpoly_monic _)).2 hsepC.isCoprime).ne_zero
  obtain ⟨M₁, l₁, s₁⟩ := exists_stable_lat (E := K.E) B₁.g i₁
  obtain ⟨M₂, l₂, s₂⟩ := exists_stable_lat (E := K.E) B₂.g i₂
  have hv : val K.O (resultant B₁.P B₂.P) = val K.O (resultant (withG B₁ Y₁).P (withG B₂ Y₂).P) :=
    val_res_eq (O := K.O) (E := K.E) B₁.g Y₁ B₂.g Y₂ hr hr' st₁ st₂ stP M₁ M₂ l₁ l₂ s₁ s₂
  unfold InvAlg.Identity at hId ⊢
  rw [kapSum_withG B₁ B₂ Y₁ Y₂ stP, stSum_withG B₁ Y₁ st₁, stSum_withG B₂ Y₂ st₂] at hId
  change (-(K.q : ℚ)) ^ (-val K.O (resultant B₁.P B₂.P)) * _ = _
  rw [hv]
  exact hId

end GlobalTheory.UnitLemma.CongruenceCayley
end
end

section

open Formalism.UG GlobalTheory.SatakeWeyl

open Matrix

namespace GlobalTheory.SatakeWeyl.InclusionMultiplication

variable {L : Type} [Field L] {n r : ℕ}

def incl (L : Type) [Field L] (e : Fin r → Fin n) : Matrix (Fin n) (Fin r) L :=
  Matrix.of fun a i => if a = e i then 1 else 0

theorem incl_mul_apply {p : Type} {e : Fin r → Fin n} (he : Function.Injective e) (M : Matrix (Fin r) p L)
    (i : Fin r) (j : p) : (incl L e * M) (e i) j = M i j := by
  simp [Matrix.mul_apply, incl, he.eq_iff]

theorem incl_mul_apply_of_not {p : Type} {e : Fin r → Fin n} (M : Matrix (Fin r) p L)
    {a : Fin n} (ha : a ∉ Set.range e) (j : p) : (incl L e * M) a j = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  have : a ≠ e i := fun h => ha ⟨i, h.symm⟩
  simp [incl, this]

theorem mul_inclT_apply {p : Type} {e : Fin r → Fin n} (he : Function.Injective e) (M : Matrix p (Fin r) L)
    (i : p) (j : Fin r) : (M * (incl L e)ᵀ) i (e j) = M i j := by
  simp [Matrix.mul_apply, incl, he.eq_iff]

theorem mul_inclT_apply_of_not {p : Type} {e : Fin r → Fin n} (M : Matrix p (Fin r) L)
    (i : p) {a : Fin n} (ha : a ∉ Set.range e) : (M * (incl L e)ᵀ) i a = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  have : a ≠ e j := fun h => ha ⟨j, h.symm⟩
  simp [incl, this]

theorem inclT_mul_incl {e : Fin r → Fin n} (he : Function.Injective e) : (incl L e)ᵀ * incl L e = 1 := by
  ext i j
  simp [Matrix.mul_apply, incl, Function.swap, he.eq_iff, Matrix.one_apply, eq_comm]

theorem antiJ_apply (i j : Fin n) : antiJ L n i j = if i.rev = j then 1 else 0 := by
  have : (i.val + j.val + 1 = n) ↔ i.rev = j := by
    have := i.2
    rw [Fin.ext_iff, Fin.val_rev]; omega
  simp only [antiJ, this]

theorem antiJ_transpose : (antiJ L n)ᵀ = antiJ L n := by
  ext i j
  simp only [Matrix.transpose_apply, antiJ, add_comm i.val j.val]

theorem antiJ_mul_incl {e : Fin r → Fin n} (hr : ∀ i, e i.rev = (e i).rev) :
    antiJ L n * incl L e = incl L e * antiJ L r := by
  ext a i
  have h1 : (antiJ L n * incl L e) a i = incl L e a.rev i := by
    simp [Matrix.mul_apply, antiJ_apply]
  have h2 : (incl L e * antiJ L r) a i = incl L e a i.rev := by
    simp [Matrix.mul_apply, antiJ_apply, Fin.rev_eq_iff]
  rw [h1, h2]
  simp [incl, hr, Fin.rev_eq_iff]

theorem inclT_mul_antiJ {e : Fin r → Fin n} (hr : ∀ i, e i.rev = (e i).rev) :
    (incl L e)ᵀ * antiJ L n = antiJ L r * (incl L e)ᵀ := by
  have := congrArg Matrix.transpose (antiJ_mul_incl (L := L) hr)
  rwa [Matrix.transpose_mul, Matrix.transpose_mul, antiJ_transpose, antiJ_transpose] at this

def ext1 (e : Fin r → Fin n) (M : Matrix (Fin r) (Fin r) L) : Matrix (Fin n) (Fin n) L :=
  1 + incl L e * (M - 1) * (incl L e)ᵀ

theorem extendMatrixByIdentityAlongIndices_mul {e : Fin r → Fin n} (he : Function.Injective e) (M N : Matrix (Fin r) (Fin r) L) :
    ext1 e (M * N) = ext1 e M * ext1 e N := by
  have h : incl L e * (M - 1) * (incl L e)ᵀ * (incl L e * (N - 1) * (incl L e)ᵀ)
      = incl L e * ((M - 1) * (N - 1)) * (incl L e)ᵀ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (incl L e)ᵀ, inclT_mul_incl he, Matrix.one_mul]
  have h2 : M * N - 1 = (M - 1) + (N - 1) + (M - 1) * (N - 1) := by noncomm_ring
  unfold ext1
  rw [add_mul, mul_add, mul_add, h, h2]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one]
  abel

theorem conjTranspose_extendMatrixByIdentityAlongIndices (σ : L →+* L) (e : Fin r → Fin n) (M : Matrix (Fin r) (Fin r) L) :
    cT σ (ext1 e M) = ext1 e (cT σ M) := by
  ext a b

  simp only [cT, ext1, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.mul_apply, map_add (f := _),
  map_sum, map_mul, incl, Matrix.of_apply, Matrix.sub_apply, map_sub, Matrix.one_apply, apply_ite σ, map_one,
  map_zero, Finset.sum_mul]
  congr 1
  · simp only [eq_comm]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [eq_comm (a := i) (b := j)]
    ring

theorem extendMatrixByIdentityAlongIndices_unitary [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) {e : Fin r → Fin n} (he : Function.Injective e)
    (hr : ∀ i, e i.rev = (e i).rev) (M : Matrix (Fin r) (Fin r) L)
    (hM : cT σ M * antiJ L r * M = antiJ L r) :
    cT σ (ext1 e M) * antiJ L n * ext1 e M = antiJ L n := by
  have hJ : ∀ N : Matrix (Fin r) (Fin r) L, antiJ L n * ext1 e N
      = ext1 e (antiJ L r * N * antiJ L r) * antiJ L n := by
    intro N
    have h2 : antiJ L r * N * antiJ L r - 1 = antiJ L r * (N - 1) * antiJ L r := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, GlobalTheory.UnitarySwap.antiJ_mul_self]
    unfold ext1
    rw [h2, Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, antiJ_mul_incl hr]
    simp only [Matrix.mul_assoc]
    rw [inclT_mul_antiJ hr, ← Matrix.mul_assoc (antiJ L r) (antiJ L r), GlobalTheory.UnitarySwap.antiJ_mul_self,
      Matrix.one_mul]
  rw [conjTranspose_extendMatrixByIdentityAlongIndices, Matrix.mul_assoc, hJ, ← Matrix.mul_assoc, ← extendMatrixByIdentityAlongIndices_mul he, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hM,
    GlobalTheory.UnitarySwap.antiJ_mul_self]
  simp [ext1]

end GlobalTheory.SatakeWeyl.InclusionMultiplication


open GlobalTheory.SatakeWeyl.InclusionMultiplication in
theorem GlobalTheory.SatakeWeyl.embExists : GlobalTheory.SatakeWeyl.EmbExists := by
  intro L _ _ σ n r e he hr
  choose f hf using fun g : GU σ r => exists_mat (σ := σ) (ext1 e (mat g)) (extendMatrixByIdentityAlongIndices_unitary σ he hr _ g.2)
  refine ⟨MonoidHom.mk' f fun a b => mat_injective ?_, fun g => ⟨fun i j => ?_, fun a b hab => ?_⟩⟩
  · rw [mat_mul, hf, hf, hf, mat_mul, extendMatrixByIdentityAlongIndices_mul he]
  · rw [MonoidHom.mk'_apply, hf, ext1, Matrix.add_apply, mul_inclT_apply he, incl_mul_apply he]
    simp [Matrix.one_apply, he.eq_iff]
  · rw [MonoidHom.mk'_apply, hf, ext1, Matrix.add_apply]
    rcases hab with h | h
    · rw [Matrix.mul_assoc, incl_mul_apply_of_not _ h, add_zero]
    · rw [mul_inclT_apply_of_not _ _ h, add_zero]
end

section

open Module GlobalTheory.HTRho GlobalTheory.UPel.Sm GlobalTheory.UPel.Sm.Model

theorem _root_.GlobalTheory.T.finrank_equivariantHom_eq_augmentation_quotient : ∀ {k O C Idx H : Type*} [Field k] [AddCommGroup H] [Module k H] [Ring O] [CommRing C] [Algebra C O] (σ : O →+* Module.End k H) (G : Submodule k H) (hG : ∀ a, ∀ x ∈ G, σ a x ∈ G) (χ : Idx → C →+* k), (jSub σ χ ⊤ ≤ G → jSub (qAct σ G hG) χ ⊤ = ⊥) ∧ ∀ i, finrank k ((H ⧸ G) ⧸ mSub (qAct σ G hG) (χ i) ⊤) = finrank k (H ⧸ (G ⊔ mSub σ (χ i) ⊤)) := by
  first | exact @GlobalTheory.HTRho.quotFacts | exact GlobalTheory.HTRho.quotFacts | (intros; apply GlobalTheory.HTRho.quotFacts <;> assumption)
end

section

open Module GlobalTheory.HTRho GlobalTheory.UPel.Sm GlobalTheory.UPel.Sm.Model

theorem _root_.GlobalTheory.T.characterAugmentationSubspace_quotientAction_top : ∀ {k O C Idx W V : Type*} [Field k] [Ring O] [CommRing C] [Algebra C O] [Fintype Idx] [AddCommGroup W] [Module k W] [FiniteDimensional k W] [AddCommGroup V] [Module k V] [FiniteDimensional k V] (σW : O →+* Module.End k W) (τ : O →+* Module.End k V) (χ : Idx → C →+* k), Function.Injective χ → jSub τ χ ⊤ = ⊥ → finrank k (homO σW τ) = ∑ i, finrank k (homO σW (qAct τ (mSub τ (χ i) ⊤) (mSub_stable τ (χ i) ⊤ (fun _ _ _ => trivial)))) := by
  first | (exact @GlobalTheory.HTRho.finrank_homO_eq_sum_quot) | (exact GlobalTheory.HTRho.finrank_homO_eq_sum_quot) | (intros; apply GlobalTheory.HTRho.finrank_homO_eq_sum_quot  <;> assumption)
end
