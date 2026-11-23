module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle792
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle540
import Mathlib.Algebra.Group.ConjFinite
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle358
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle378
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle791
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle333
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle334
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle466
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle713
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle790
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle803
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle793
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle448
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle639
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle449
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle496
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle486
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.ChartSymmEventuallyEq
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.MeasurableSetImageOfIsLocalHomeomorph
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle005
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle011
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003

@[expose] public section

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.cuspidalCharacterGLFiniteField_eq_of_modEq : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ m k k' a : ℕ, 0 < m → k' ≡ k * Nat.card F ^ a [MOD Nat.card F ^ m - 1] → cusp θ m k' = cusp θ m k := by
  first | (exact @GlobalTheory.Shin.cusp_eq_of_modEq) | (exact GlobalTheory.Shin.cusp_eq_of_modEq) | (intros; apply GlobalTheory.Shin.cusp_eq_of_modEq <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem exists_isNorm : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'),
    (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (n : ℕ) (δ : GL (Fin n) F'), ∃ γ : GL (Fin n) F, IsNorm s δ γ := by
  intro F F' _ _ _ _ s hs n δ₀
  haveI : Finite F := Finite.of_injective _ (algebraMap F F').injective
  haveI : Finite (GL (Fin n) F) := inferInstance
  haveI : Finite (GL (Fin n) F') := inferInstance
  letI := Fintype.ofFinite (GL (Fin n) F)
  letI := Fintype.ofFinite (GL (Fin n) F')
  have hfib := GlobalTheory.T.card_isGaloisTwistedNormGL_mul_card_GL F F' s hs n
  have hnd := GlobalTheory.T.isConj_of_isConj_glFieldExtensionInclusion F F' n
  let cl : GL (Fin n) F → ℕ := fun γ => Nat.card {γ' : GL (Fin n) F // IsConj γ γ'}
  have hcl_pos : ∀ γ, 0 < cl γ := fun γ => Nat.card_pos_iff.2 ⟨⟨⟨γ, IsConj.refl γ⟩⟩, inferInstance⟩
  have hcl_eq : ∀ γ, (cl γ : ℚ) = ((Finset.univ.filter fun γ' => IsConj γ γ').card : ℚ) := by
    intro γ
    simp only [cl, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hcard : ∀ γ, Nat.card {δ : GL (Fin n) F' // IsNorm s δ γ}
      = (Finset.univ.filter fun δ => IsNorm s δ γ).card := by
    intro γ
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  let f : GL (Fin n) F' → GL (Fin n) F → ℚ := fun δ γ => if IsNorm s δ γ then ((cl γ : ℚ))⁻¹ else 0
  have h1 : ∀ δ, ∑ γ, f δ γ = if ∃ γ, IsNorm s δ γ then 1 else 0 := by
    intro δ
    by_cases h : ∃ γ, IsNorm s δ γ
    · obtain ⟨γ₀, h₀⟩ := h
      rw [if_pos ⟨γ₀, h₀⟩]
      have hiff : ∀ γ, IsNorm s δ γ ↔ IsConj γ₀ γ := by
        intro γ
        constructor
        · intro hγ
          exact hnd γ₀ γ (h₀.trans hγ.symm)
        · intro hγ
          exact (isConj_iff.2 (by
            obtain ⟨c, hc⟩ := isConj_iff.1 hγ
            exact ⟨incl F F' n c, by rw [← hc]; simp [map_mul, map_inv]⟩)).symm.trans h₀
      have hcl' : ∀ γ, IsConj γ₀ γ → cl γ = cl γ₀ := by
        intro γ hγ
        exact Nat.card_congr (Equiv.subtypeEquivRight fun γ' => ⟨fun h => hγ.trans h, fun h => hγ.symm.trans h⟩)
      have : ∀ γ, f δ γ = if IsConj γ₀ γ then ((cl γ₀ : ℚ))⁻¹ else 0 := by
        intro γ
        simp only [f, hiff γ]
        split_ifs with hh
        · rw [hcl' γ hh]
        · rfl
      simp only [this]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, ← hcl_eq]
      exact mul_inv_cancel₀ (by exact_mod_cast (hcl_pos γ₀).ne')
    · rw [if_neg h]
      apply Finset.sum_eq_zero
      intro γ _
      simp only [f]
      rw [if_neg (fun hh => h ⟨γ, hh⟩)]
  have h2 : ∀ γ, ∑ δ, f δ γ = (Nat.card (GL (Fin n) F') : ℚ) / Nat.card (GL (Fin n) F) := by
    intro γ
    simp only [f]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, ← hcard]
    have hG : (0 : ℚ) < Nat.card (GL (Fin n) F) := by exact_mod_cast Nat.card_pos
    have hc : (0 : ℚ) < cl γ := by exact_mod_cast hcl_pos γ
    have hq : (Nat.card {δ : GL (Fin n) F' // IsNorm s δ γ} : ℚ) * Nat.card (GL (Fin n) F)
        = cl γ * Nat.card (GL (Fin n) F') := by exact_mod_cast hfib γ
    field_simp
    linarith [hq]
  have hsum : ∑ δ : GL (Fin n) F', (if ∃ γ, IsNorm s δ γ then (1 : ℚ) else 0) = ∑ δ : GL (Fin n) F', (1 : ℚ) := by
    simp only [← h1]
    rw [Finset.sum_comm]
    simp only [h2]
    rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, Finset.card_univ, Finset.card_univ,
      ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    have hG : (0 : ℚ) < Nat.card (GL (Fin n) F) := by exact_mod_cast Nat.card_pos
    field_simp
  have hle : ∀ δ ∈ (Finset.univ : Finset (GL (Fin n) F')),
      (if ∃ γ, IsNorm s δ γ then (1 : ℚ) else 0) ≤ 1 := by
    intro δ _
    split_ifs <;> norm_num
  have := (Finset.sum_eq_sum_iff_of_le hle).1 hsum δ₀ (Finset.mem_univ _)
  by_contra hno
  rw [if_neg hno] at this
  norm_num at this

end GlobalTheory.Shin
end

section

set_option autoImplicit false

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef Polynomial

theorem GlobalTheory.Nef.deg_le_two_mul_of_triangular : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ (g : Place k F → Matrix (Fin 2) (Fin 2) F), admitted g → (∀ v, g v 1 0 = 0) → ∀ b : ℝ, LinesLE g b → (deg g : ℝ) ≤ 2 * b := by
  intro k F _ _ _ _ _ hFF g hg htri b hb
  by_cases hne : IsEmpty (Place k F)
  · have h0 : deg g = 0 := by simp [deg, finsum_of_isEmpty]
    have hres : IsRes (k := k) (F := F) (E := F) id := fun p x => by simp
    have hw : (![1, 0] : Fin 2 → F) ≠ 0 := by intro h; simpa using congrFun h 0
    have h1 := hb F id hres ![1, 0] hw
    have hl : degLine (pullAd id g) (![1, 0] : Fin 2 → F) = 0 := by simp [degLine, finsum_of_isEmpty]
    rw [hl] at h1
    simp at h1
    rw [h0]; push_cast; linarith
  rw [not_isEmpty_iff] at hne
  obtain ⟨v₀⟩ := hne
  obtain ⟨γ, hγ⟩ := GlobalTheory.T.exists_section_of_large_adelic_degree k F hFF
  obtain ⟨π, hπ0, hπ⟩ := (GlobalTheory.T.functionFieldPlaceOrder_calculus k F v₀).2.2.2.2.2.1
  have key : ∀ m : ℕ, ((m * (m + 1) / 2 : ℕ) : ℝ) * (deg g : ℝ) ≤ (m + 1) * (m * b + 1 + γ) := by
    intro m
    set N : ℕ := m * (m + 1) / 2 with hN
    set S : Place k F → Matrix (Fin (m + 1)) (Fin (m + 1)) F := fun v => symMat m (g v) with hS
    obtain ⟨hSadm, hSdeg⟩ := GlobalTheory.Nef.admissible_degree_symmetricPowerFamily k F m g hg htri
    rw [← hN] at hSdeg
    set D : ℤ := (N : ℤ) * deg g - (m + 1) * γ - 1 with hD
    set e : ℤ := D / (m + 1) with he
    have hm0 : (0 : ℤ) < m + 1 := by positivity
    have hdiv := Int.mul_ediv_add_emod D (m + 1)
    have hmod0 := Int.emod_nonneg D hm0.ne'
    have hmod1 := Int.emod_lt_of_pos D hm0
    rw [← he] at hdiv
    obtain ⟨hTadm, hTdeg⟩ := GlobalTheory.Nef.admissible_degree_twistFamilyAtPlaceByScalar k F (m + 1) S hSadm v₀ π hπ0 hπ e
    have hdegT : ((m + 1 : ℕ) : ℤ) * γ < deg (twistAt v₀ (π ^ (-e)) S) := by
      have hc1 : ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 := by push_cast; ring
      rw [hTdeg, hSdeg, hc1]; linarith
    obtain ⟨p, hp0, hpint⟩ := hγ (m + 1) _ hTadm hdegT
    have hep : e ≤ degLine S p := GlobalTheory.T.lineDegree_ge_of_twisted_section k F hFF (m + 1) S hSadm v₀ π hπ0 hπ e p hp0 hpint
    obtain ⟨E, _, _, _, c, s, t, hc, hst, hid⟩ := GlobalTheory.T.exists_binary_form_eq_mul_prod_linear F m p hp0
    letI : Algebra k E := ((algebraMap F E).comp (algebraMap k F)).toAlgebra
    haveI : IsScalarTower k F E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    obtain ⟨ρ, hρ⟩ := (GlobalTheory.T.functionFieldPlace_restriction_exists_pow k F E).1
    have hEFF : IsFF k E := (GlobalTheory.T.functionFieldOneVariable_transcendental_finite_and_ext k F hFF).2 E
    have pS := GlobalTheory.T.isAdmissibleAdelicMatrixFamily_pullback_extension k F E hFF ρ hρ (m + 1) S hSadm
    have pg := GlobalTheory.T.isAdmissibleAdelicMatrixFamily_pullback_extension k F E hFF ρ hρ 2 g hg
    have hpull : pullAd ρ S = fun P => symMat m (pullAd ρ g P) := by
      funext P; simp only [pullAd, hS, symMat_map]
    have htriE : ∀ P, pullAd ρ g P 1 0 = 0 := by intro P; simp [pullAd, htri]
    set q : Fin (m + 1) → E := fun i => algebraMap F E (p i) with hq
    have hpt : ∀ P, ordVec P ((symMat m (pullAd ρ g P)).mulVec q) =
        ord P c + ∑ j, ordVec P ((pullAd ρ g P).mulVec ![s j, t j]) := fun P =>
      GlobalTheory.T.gaussLemma_symPowMatrix_upperTriangular_placeOrder k E P m _ (htriE P) (pg.1.1 P) q c s t hc hst (by
        have h3 := hid E[X] (C ((pullAd ρ g P) 0 0)) (C ((pullAd ρ g P) 0 1) + C ((pullAd ρ g P) 1 1) * X)
        rw [Polynomial.algebraMap_eq] at h3
        exact h3)
    have h6 := GlobalTheory.T.lineDegree_eq_sum_of_scalar_split k E hEFF m (m + 1) (pullAd ρ g) pg.1 (fun P => symMat m (pullAd ρ g P)) q c
      (fun j => ![s j, t j]) hc hst hpt
    have h2 := pS.2.2.1 p hp0
    rw [hpull] at h2
    have hbound : ∀ j, (degLine (pullAd ρ g) ![s j, t j] : ℝ) ≤ b * Module.finrank F E :=
      fun j => hb E ρ hρ _ (hst j)
    have hsum : ((∑ j, degLine (pullAd ρ g) ![s j, t j] : ℤ) : ℝ) ≤ m * (b * Module.finrank F E) := by
      push_cast
      calc (∑ j : Fin m, (degLine (pullAd ρ g) ![s j, t j] : ℝ)) ≤ ∑ _j : Fin m, b * Module.finrank F E :=
            Finset.sum_le_sum fun j _ => hbound j
        _ = m * (b * Module.finrank F E) := by simp
    have hfr : (0 : ℝ) < Module.finrank F E := by exact_mod_cast Module.finrank_pos
    have h7 : (Module.finrank F E : ℝ) * (e : ℝ) ≤ m * (b * Module.finrank F E) := by
      have h8 : (Module.finrank F E : ℤ) * degLine S p = ∑ j, degLine (pullAd ρ g) ![s j, t j] := by
        rw [← h6, ← h2]
      have h8' : (Module.finrank F E : ℝ) * (degLine S p : ℝ) = ((∑ j, degLine (pullAd ρ g) ![s j, t j] : ℤ) : ℝ) := by
        exact_mod_cast h8
      have h9 : (e : ℝ) ≤ (degLine S p : ℝ) := by exact_mod_cast hep
      have h10 : (Module.finrank F E : ℝ) * (e : ℝ) ≤ (Module.finrank F E : ℝ) * (degLine S p : ℝ) :=
        mul_le_mul_of_nonneg_left h9 hfr.le
      linarith
    have hemb : (e : ℝ) ≤ m * b := by
      have : (Module.finrank F E : ℝ) * (e : ℝ) ≤ (Module.finrank F E : ℝ) * (m * b) := by linarith
      exact le_of_mul_le_mul_left this hfr
    have hint : (N : ℤ) * deg g ≤ (m + 1) * (e + 1 + γ) := by linarith
    have hreal : ((N : ℤ) : ℝ) * (deg g : ℝ) ≤ ((m : ℝ) + 1) * ((e : ℝ) + 1 + γ) := by exact_mod_cast hint
    push_cast at hreal
    have hm1 : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
    nlinarith
  by_contra hlt
  push_neg at hlt
  have hpos : (0 : ℝ) < (deg g : ℝ) - 2 * b := by linarith
  obtain ⟨m, hm⟩ := exists_nat_gt (2 * (1 + γ) / ((deg g : ℝ) - 2 * b))
  have hk := key m
  have hN : ((m * (m + 1) / 2 : ℕ) : ℝ) = (m : ℝ) * (m + 1) / 2 := by
    have h2 : 2 ∣ m * (m + 1) := (Nat.even_mul_succ_self m).two_dvd
    rw [Nat.cast_div h2 (by norm_num)]; push_cast; ring
  rw [hN] at hk
  rw [div_lt_iff₀ hpos] at hm
  have hm' : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have : (m : ℝ) * (deg g : ℝ) ≤ 2 * (m * b + 1 + γ) := by
    have h3 : ((m : ℝ) + 1) * ((m : ℝ) * (deg g : ℝ)) ≤ ((m : ℝ) + 1) * (2 * (m * b + 1 + γ)) := by nlinarith
    exact le_of_mul_le_mul_left h3 hm'
  nlinarith
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.EtaleMeasure

noncomputable section

variable {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La]

def rho (A : WeightedAtlas n Y ι La) (U : Set Y) (z : Y → V n) (x : U) : ℝ≥0∞ :=
  ENNReal.ofReal (A.nsq A.kap (jdet A z) x)⁻¹

theorem rho_measurable (A : WeightedAtlas n Y ι La) {U : Set Y} {z : Y → V n}
    (hE : Etale A U z) : Measurable (rho A U z) := by
  have hfr := GlobalTheory.T.jacobianDet_isFrameOn_canonicalWeight n Y ι La A U z hE
  have hc : ContinuousOn (A.nsq A.kap (jdet A z)) U := api_nsq_contOn A hE.isOpen hfr.1
  have hc' : Continuous (fun x : U => A.nsq A.kap (jdet A z) x) := hc.restrict
  exact ENNReal.measurable_ofReal.comp hc'.measurable.inv

theorem mu_piece (A : WeightedAtlas n Y ι La) {U : Set Y} {z : Y → V n}
    (hE : Etale A U z) (e : OpenPartialHomeomorph U (V n))
    (he : IsChart n (fun y : U => z y) e) (i : ι) (B : Set U)
    (hB : MeasurableSet B) (hBs : B ⊆ e.source) (hBi : ∀ m ∈ B, (m : Y) ∈ (A.chart i).source) :
    A.mu.comap Subtype.val B = ∫⁻ m in B, rho A U z m ∂vol n (fun y : U => z y) := by
  have hUm : MeasurableSet U := hE.isOpen.measurableSet
  have hemb := MeasurableEmbedding.subtype_coe hUm
  have hz : IsLocalHomeomorph (fun y : U => z y) := GlobalTheory.T.etale_isLocalHomeomorph' n Y ι La A U z hE
  have hfr := GlobalTheory.T.jacobianDet_isFrameOn_canonicalWeight n Y ι La A U z hE
  have hρ : Measurable (rho A U z) := rho_measurable A hE
  rw [hemb.comap_apply]
  have hBY : MeasurableSet (Subtype.val '' B : Set Y) := hemb.measurableSet_image.2 hB
  rw [A.mu_chart i _ hBY (by rintro _ ⟨m, hm, rfl⟩; exact hBi m hm)]
  have hBimg : MeasurableSet (e '' B) := by
    have := measurableSet_image_of_chart n (fun y : U => z y) e he B hB hBs
    rwa [Set.image_congr fun m hm => he (hBs hm)] at this
  have hR : ∫⁻ m in B, rho A U z m ∂vol n (fun y : U => z y) =
      ∫⁻ w in e '' B, rho A U z (e.symm w) := by
    rw [← lintegral_indicator hB, lintegral_vol_chart n _ hz e he _ (hρ.indicator hB)
      (fun m hm => Set.indicator_of_notMem (fun h => hm (hBs h)) _)]
    have hsub : e '' B ⊆ e.target := fun _ ⟨m, hm, hmw⟩ => hmw ▸ e.map_source (hBs hm)
    rw [← Set.inter_eq_left.2 hsub, ← Measure.restrict_restrict hBimg, ← lintegral_indicator hBimg]
    refine setLIntegral_congr_fun e.open_target.measurableSet fun w hw => ?_
    by_cases h : e.symm w ∈ B
    · have hw' : w ∈ e '' B := ⟨e.symm w, h, e.right_inv hw⟩
      simp only [Set.indicator_of_mem h, Set.indicator_of_mem hw']
    · have hw' : w ∉ e '' B := by
        rintro ⟨m, hm, rfl⟩
        exact h (by rw [e.left_inv (hBs hm)]; exact hm)
      simp only [Set.indicator_of_notMem h, Set.indicator_of_notMem hw']
  set F : V n → V n := z ∘ (A.chart i).symm with hFdef
  set S := A.chart i '' (Subtype.val '' B)
  have hS : MeasurableSet S :=
    measurableSet_image_of_chart n (A.chart i) (A.chart i) (fun _ _ => rfl) _ hBY
      (by rintro _ ⟨m, hm, rfl⟩; exact hBi m hm)
  have hOo : IsOpen ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) :=
    (A.chart i).isOpen_inter_preimage_symm hE.isOpen
  have hSO : S ⊆ (A.chart i).target ∩ (A.chart i).symm ⁻¹' U := by
    rintro _ ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    refine ⟨(A.chart i).map_source (hBi m hm), ?_⟩
    show (A.chart i).symm (A.chart i m) ∈ U
    rw [(A.chart i).left_inv (hBi m hm)]; exact m.2
  have hFm : ∀ m ∈ B, F (A.chart i m) = e m := fun m hm => by
    simp only [hFdef, Function.comp_apply, (A.chart i).left_inv (hBi m hm)]
    exact he (hBs hm)
  have himg : e '' B = F '' S := by
    rw [Set.image_image, Set.image_image]
    exact (Set.image_congr fun m hm => hFm m hm).symm
  have hinj : Set.InjOn F S := by
    rintro _ ⟨_, ⟨m1, hm1, rfl⟩, rfl⟩ _ ⟨_, ⟨m2, hm2, rfl⟩, rfl⟩ h
    rw [hFm m1 hm1, hFm m2 hm2] at h
    rw [e.injOn (hBs hm1) (hBs hm2) h]
  have hder : ∀ v ∈ S, HasFDerivWithinAt F
      ((fderiv ℂ F v).restrictScalars ℝ) S v := fun v hv =>
    ((((hE.holo i).differentiableAt (hOo.mem_nhds (hSO hv))).hasFDerivAt).restrictScalars ℝ).hasFDerivWithinAt
  rw [hR, himg, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hS hder hinj]
  refine setLIntegral_congr_fun hS ?_
  rintro _ ⟨_, ⟨m, hm, rfl⟩, rfl⟩
  have hmi := hBi m hm
  have hne : jdet A z i m ≠ 0 := hE.det_ne i m m.2 hmi
  have hns := api_nsq_eq A hfr.1 hmi m.2
  have hjd : (fderiv ℂ F (A.chart i m)).det = jdet A z i m := rfl
  simp only
  rw [hFm m hm, e.left_inv (hBs hm), (A.chart i).left_inv hmi, rho, ← hns,
    ← ENNReal.ofReal_mul (abs_nonneg _), fc_det_real, hjd]
  congr 1
  have h2 : 0 < ‖jdet A z i m‖ ^ 2 := by positivity
  rw [mul_inv, Real.exp_neg, inv_inv]
  field_simp

end

end GlobalTheory.EtaleMeasure

namespace GlobalTheory.EtaleMeasure

theorem lintegral_mu_etale : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (U : Set Y) (z : Y → V n), Etale A U z → ∀ φ : Y → ℝ≥0∞, Measurable φ → ∫⁻ y in U, φ y ∂A.mu = ∫⁻ x : U, φ x * ENNReal.ofReal (A.nsq A.kap (jdet A z) x)⁻¹ ∂vol n (fun y : U => z y) := by
  intro n Y _ _ _ _ _ ι La _ A U z hE φ hφ
  have hUm : MeasurableSet U := hE.isOpen.measurableSet
  have hz : IsLocalHomeomorph (fun y : U => z y) := GlobalTheory.T.etale_isLocalHomeomorph' n Y ι La A U z hE
  have hρ : Measurable (rho A U z) := rho_measurable A hE
  have hmeas : A.mu.comap Subtype.val = (vol n (fun y : U => z y)).withDensity (rho A U z) := by
    choose e he hxe using fun x : U => exists_chart n _ hz x
    let W : U → Set U := fun x =>
      (e x).source ∩ Subtype.val ⁻¹' (A.chart (A.pick x)).source
    have hWo : ∀ x, IsOpen (W x) := fun x =>
      (e x).open_source.inter ((A.chart _).open_source.preimage continuous_subtype_val)
    obtain ⟨T, hTc, hTW⟩ := TopologicalSpace.isOpen_iUnion_countable W hWo
    have huniv : ⋃ t : T, W t = Set.univ := by
      refine Set.eq_univ_of_forall fun x => ?_
      have hx : x ∈ ⋃ i ∈ T, W i := hTW ▸ Set.mem_iUnion.2 ⟨x, hxe x, A.mem_pick _⟩
      obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.1 hx
      exact Set.mem_iUnion.2 ⟨⟨t, ht⟩, hxt⟩
    haveI := hTc.to_subtype
    refine Measure.ext_of_iUnion_eq_univ huniv fun t => ?_
    ext B hB
    rw [Measure.restrict_apply hB, Measure.restrict_apply hB,
      withDensity_apply _ (hB.inter (hWo t).measurableSet)]
    exact mu_piece A hE (e t) (he t) (A.pick (t : Y)) (B ∩ W t)
      (hB.inter (hWo t).measurableSet) (fun m hm => hm.2.1) (fun m hm => hm.2.2)
  rw [← lintegral_subtype_comap hUm, hmeas]
  exact (lintegral_withDensity_eq_lintegral_mul _ hρ (hφ.comp measurable_subtype_coe)).trans
    (lintegral_congr fun x => mul_comm _ _)

end GlobalTheory.EtaleMeasure
end

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD

theorem twistedDual_omB : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (τ : DR k K →ₗ[K] K), IsTop k K x τ → ∀ I : Finset (Fin (d + 1)), I.Nonempty → ∀ p q : ℕ, p + q = d → ∀ y ∈ ⋀[K]^q Ω[K⁄k], (∀ a ∈ omB k K (rB k K x I) p, Algebra.trace F K (τ (a * y)) ∈ omA k x I) ↔ y ∈ omB k K (rB k K x I) q := by
  intro k _ _ F K _ _ _ _ _ _ d x hc τ hτ I hI p q hpq y hy
  obtain ⟨-, hfr, hsm⟩ := GlobalTheory.T.finite_cover_chart_smooth_normal k F K d x hc I hI
  have hrk : Module.finrank K Ω[K⁄k] = d := by
    obtain ⟨b, -⟩ := hc.exists_basis
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have htop := (GlobalTheory.T.exists_topDegreeCoefficientForm_and_eq_on_top_forms k F K d x hc).2 τ hτ
  constructor
  · intro h
    refine GlobalTheory.T.mem_regularForms_of_wedge_pairing_perfect k K (rB k K x I) d p q hrk hpq y hy fun a ha => ?_
    have haG : a ∈ ⋀[K]^p Ω[K⁄k] := ((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K (rB k K x I) p q).2.1 a ha).2.2.1
    have hay : a * y ∈ ⋀[K]^d Ω[K⁄k] := hpq ▸ SetLike.mul_mem_graded haG hy
    have hz : ∀ b ∈ rB k K x I, Algebra.trace F K (τ (a * y) * b) ∈ omA k x I := by
      intro b hb
      have hba : b • a ∈ omB k K (rB k K x I) p := ((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K (rB k K x I) p q).2.1 a ha).2.2.2 b hb
      have e : τ (a * y) * b = τ ((b • a) * y) := by
        rw [smul_mul_assoc, map_smul, smul_eq_mul, mul_comm]
      rw [e]
      exact h _ hba
    obtain ⟨y', hy', e'⟩ := (GlobalTheory.T.complementaryModule_standardOpens_iff k F K d x hc τ hτ I hI (τ (a * y))).1 hz
    have hy'G : y' ∈ ⋀[K]^d Ω[K⁄k] := ((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K (rB k K x I) d q).2.1 y' hy').2.2.1
    rw [htop _ hay, ← e', ← htop _ hy'G]
    exact hy'
  · intro h a ha
    have hay : a * y ∈ omB k K (rB k K x I) d := hpq ▸ (GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K (rB k K x I) p q).1 a ha y h
    have := (GlobalTheory.T.complementaryModule_standardOpens_iff k F K d x hc τ hτ I hI (τ (a * y))).2 ⟨a * y, hay, rfl⟩ 1 (Subalgebra.one_mem _)
    rwa [mul_one] at this

end GlobalTheory.PD
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace PDivGroup

theorem subsingleton_omega_of_isEt : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (G : PDivGroup p k), G.IsEt → Subsingleton G.omega ∧ Subsingleton G.dual.dual.omega := by
  intro p _ k _ _ _ G hG
  have hp : (p : k) = 0 := CharP.cast_eq_zero k p
  have h1 : Subsingleton G.omega := by
    refine ⟨fun v w => ?_⟩
    have hz : ∀ u : G.omega, u = 0 := fun u => Subtype.ext (funext fun n => by
      haveI := hG n
      obtain ⟨a, ha⟩ := AugCot.d_surjective _ (u.1 n)
      obtain ⟨b, rfl⟩ := GlobalTheory.T.exists_pow_char_eq_of_isReduced_finite' p k (G.A n) a
      rw [← ha]
      exact dUnit_pow_prime hp b)
    rw [hz v, hz w]
  refine ⟨h1, ?_⟩
  have hinj : Function.Injective (omegaMap G G.dual.dual G.bidual.hom) := by
    refine Function.LeftInverse.injective (g := omegaMap G.dual.dual G G.bidual.inv) fun x => ?_
    rw [← LinearMap.comp_apply, ← omegaMap_comp, Iso.inv_hom_id, omegaMap_id, LinearMap.id_apply]
  exact hinj.subsingleton

end PDivGroup

end GlobalTheory
end
end
