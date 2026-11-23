module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1098
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1099
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1114
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1086
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1100
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1078
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle032
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.ExistsLinearIndependentNormLe
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

theorem isOn_pull_comp : ∀ (X Z Z' : Scheme.{0}) (W : X.Opens) (L : LB X) (r : Z ⟶ X) (s : Z' ⟶ Z),
    IsOn W L → (∀ z, r z ∈ W) → LBIso ((L.pull r).pull s) (L.pull (s ≫ r)) := by
  intro X Z Z' W L r s hL hr
  have h : (L.pull (s ≫ r)).IsLB := GlobalTheory.T.isLineBundle_pull_of_isLineBundleOnOpen X Z' W L (s ≫ r) hL fun z ↦ by
    simpa using hr (s z)
  exact iso_of_chart h (chartPullLinComb L r (fun _ : PUnit => s) (fun _ => s ≫ r) (fun _ => 1) (𝟙 _)
    fun _ => (Category.id_comp _).symm)

end GlobalTheory.PicGlue
end
end

section

noncomputable section

open WeierstrassCurve
open scoped BigOperators

namespace GlobalTheory.CMModel

theorem avg_mem_of_card_unit (V : ValuationSubring ℂ) {ι : Type} [Fintype ι] (f : ι → ℂ)
    (hc : V.valuation (Fintype.card ι : ℂ) = 1) (hf : ∀ i, f i ∈ V) :
    (∑ i, f i) / Fintype.card ι ∈ V := by
  rw [div_eq_mul_inv]
  refine V.mul_mem _ _ (sum_mem (S := V) fun i _ => hf i) ?_
  rw [← V.valuation_le_one_iff, map_inv₀, hc, inv_one]

theorem intV_average (V : ValuationSubring ℂ) (a₄ a₆ r s t : ℂ) (u : ℂˣ) (ι : Type) [Fintype ι]
    (X Y : ι → ℂ)
    (h : IntV V ((⟨u, r, s, t⟩ : VariableChange ℂ) • (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve ℂ)))
    (hc : V.valuation (Fintype.card ι : ℂ) = 1)
    (hX : ∀ i, (X i - r) / (u : ℂ) ^ 2 ∈ V)
    (hY : ∀ i, (Y i - t - s * (X i - r)) / (u : ℂ) ^ 3 ∈ V)
    (h2 : ∀ i, V.valuation (2 * Y i) = V.valuation (u : ℂ) ^ 3) :
    IntV V ((⟨u, (∑ i, X i) / Fintype.card ι,
      (∑ i, (3 * X i ^ 2 + a₄) / (2 * Y i)) / Fintype.card ι,
      (∑ i, Y i) / Fintype.card ι⟩ : VariableChange ℂ) •
      (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve ℂ)) := by
  have hn : (Fintype.card ι : ℂ) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hc
    exact zero_ne_one hc
  have hu : (u : ℂ) ≠ 0 := u.ne_zero
  have hr := avg_mem_of_card_unit V _ hc hX
  have ht := avg_mem_of_card_unit V _ hc hY
  have hs := avg_mem_of_card_unit V _ hc fun i =>
    GlobalTheory.T.tangent_slope_mem_of_intV V a₄ a₆ r s t (X i) (Y i) u h (hX i) (hY i) (h2 i)
  simp only [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul] at hr hs ht
  set A := ∑ i, X i
  set B := ∑ i, (3 * X i ^ 2 + a₄) / (2 * Y i)
  set D := ∑ i, Y i
  set n : ℂ := ((Fintype.card ι : ℕ) : ℂ)
  have key : (⟨u, A / n, B / n, D / n⟩ : VariableChange ℂ) =
      (⟨1, (A - n * r) / (u : ℂ) ^ 2 / n, (B - n * s) / (u : ℂ) / n,
        (D - n * t - s * (A - n * r)) / (u : ℂ) ^ 3 / n⟩ : VariableChange ℂ) * ⟨u, r, s, t⟩ := by
    rw [VariableChange.mul_def]
    ext
    · simp
    all_goals
      simp only []
      field_simp
      ring
  rw [key, mul_smul]
  exact GlobalTheory.coeff_mem_variableChange V.toSubring h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2 hr hs ht rfl

end GlobalTheory.CMModel
end
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem card_sq_mod_prime : ∀ (p : ℕ), p.Prime → p % 4 = 3 →
    2 * Fintype.card (Sq p) + 1 = p ∧ Odd (Fintype.card (Sq p)) := by
  intro p hp h4
  obtain ⟨e, -⟩ := GlobalTheory.T.nonzeroSquares_sum_equiv_Ico_mod_four p hp h4
  have hc := Fintype.card_congr e
  rw [Fintype.card_sum] at hc
  have h2 : Fintype.card (Finset.Ico 1 p : Finset ℕ) = p - 1 := by
    simp
  rw [h2] at hc
  have hp2 := hp.two_le
  have hsum : 2 * Fintype.card (Sq p) + 1 = p := by omega
  refine ⟨hsum, ?_⟩
  rw [Nat.odd_iff]
  omega

end GlobalTheory.CMModel
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem torsion_coords_mem_of_odd : ∀ (L : PeriodPair) (β u : ℂ) (V : ValuationSubring ℂ) (N : ℕ), MulStable L β → β.im ≠ 0 → V.valuation u ^ 12 = V.valuation (latticeCurve L).Δ → V.valuation (N : ℂ) = 1 → Odd N → ∀ (hu : u ≠ 0) (r s t : ℂ), IntV V ((⟨Units.mk0 u hu, r, s, t⟩ : VariableChange ℂ) • latticeCurve L) → ∀ z, z ∉ L.lattice → (N : ℂ) * z ∈ L.lattice → (L.weierstrassP z - r) / u ^ 2 ∈ V ∧ (L.derivWeierstrassP z / 2 - t - s * (L.weierstrassP z - r)) / u ^ 3 ∈ V := by
  intro L β u V N hmul hβ hΔ hN hodd hu r s t hint z hz hNz
  have h2z : 2 * z ∉ L.lattice := by
    intro h
    obtain ⟨k, hk⟩ := hodd
    have e : z = (N : ℂ) * z - ((k : ℤ) • (2 * z)) := by
      rw [zsmul_eq_mul, hk]; push_cast; ring
    exact hz (e ▸ sub_mem hNz (L.lattice.smul_mem _ h))
  have hNz2 : (N : ℂ) * (2 * z) ∈ L.lattice := by
    have e : (N : ℂ) * (2 * z) = N * z + N * z := by ring
    rw [e]; exact add_mem hNz hNz
  obtain ⟨hP', -⟩ := GlobalTheory.T.torsion_weierstrassP_mem_valuationSubring L β u V N hmul hβ hΔ hN z z hz hz hNz hNz
  obtain ⟨-, hδ⟩ := GlobalTheory.T.torsion_weierstrassP_mem_valuationSubring L β u V N hmul hβ hΔ hN (2 * z) z h2z hz hNz2 hNz
  have dup := GlobalTheory.T.weierstrassP_two_mul_mul_deriv_sq L z hz h2z
  have sq := L.derivWeierstrassP_sq z hz
  set C : VariableChange ℂ := ⟨Units.mk0 u hu, r, s, t⟩ with hC
  have hCu : ((C.u⁻¹ : ℂˣ) : ℂ) = u⁻¹ := by simp [hC]
  have hCr : C.r = r := rfl
  have hCs : C.s = s := rfl
  have hCt : C.t = t := rfl
  set P := L.weierstrassP z with hPdef
  set P' := L.derivWeierstrassP z with hP'def
  set P2 := L.weierstrassP (2 * z) with hP2def
  have hD : 2 * ((P' / 2 - t - s * (P - r)) / u ^ 3) + (C • latticeCurve L).a₁ * ((P - r) / u ^ 2)
      + (C • latticeCurve L).a₃ = P' / u ^ 3 := by
    rw [variableChange_a₁, variableChange_a₃, hCu, hCr, hCs, hCt]
    simp only [latticeCurve]
    field_simp
    ring
  apply GlobalTheory.T.mem_of_duplication_eq_weierstrass V (C • latticeCurve L) _ _ ((P2 - P) / u ^ 2) hint
  · rw [Affine.equation_iff]
    simp only [WeierstrassCurve.toAffine]
    rw [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄, variableChange_a₆, hCu, hCr, hCs, hCt]
    simp only [latticeCurve]
    linear_combination (norm := skip) (1 / 4 * u⁻¹ ^ 6) * sq
    field_simp
    ring
  · rw [hD]; exact hP'
  · exact hδ
  · rw [hD, variableChange_b₄, variableChange_b₆, variableChange_b₈, hCu, hCr]
    simp only [latticeCurve, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    linear_combination (norm := skip) (u⁻¹ ^ 8) * (-dup + (2 * P + r) * sq)
    field_simp
    ring

end GlobalTheory.CMModel
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel


open GlobalTheory.ConjPoint PeriodPair in
theorem exists_conj_kernel_mul : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ), p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → ∀ σ : ℂ ≃+* ℂ, (∀ x ∈ F, σ x = x) → ∃ c : ℕ, ¬ p ∣ c ∧ ∀ k : ℕ, GlobalTheory.ConjPoint.IsConj L L σ ((k : ℂ) * t) ((k : ℂ) * ((c : ℂ) * t)) := by
  intro p F L t hp h4 h3 hD σ hσ
  have h₂ : L.g₂ = σ L.g₂ := (hσ _ hD.g₂_mem).symm
  have h₃ : L.g₃ = σ L.g₃ := (hσ _ hD.g₃_mem).symm
  obtain ⟨s, -, hc⟩ := exists_conjEquiv h₂ h₃
  obtain ⟨t', ht'⟩ := latticePoint_surjective L (s (latticePoint L t))
  have hct : IsConj L L σ t t' := (hc _ _).2 ht'.symm
  have ht'n : t' ∉ L.lattice := by
    rcases hct with h | h
    · exact (hD.notMem h.1).elim
    · exact h.2.1

  have hsq : (σ (sqrtNegNat p)) ^ 2 = (sqrtNegNat p) ^ 2 := by
    rw [← map_pow, sqrtNegNat_sq, map_neg, map_natCast]
  have hm := IsConj.mul h₂ h₃ hD.mul hct
  have hker : σ (sqrtNegNat p) * t' ∈ L.lattice := by
    rcases hm with h | h
    · exact h.2
    · exact (h.1 hD.ker).elim
  have hker' : sqrtNegNat p * t' ∈ L.lattice := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with e | e
    · rwa [e] at hker
    · rw [e, neg_mul] at hker
      simpa using neg_mem hker
  obtain ⟨-, hz, -⟩ := GlobalTheory.T.sqrtNegPrime_kernel_cyclic p F L t hp h4 h3 hD
  obtain ⟨c, hcp, hcl⟩ := hz t' hker'
  refine ⟨c, fun hdvd => ?_, fun k => ?_⟩
  · have hc0 : c = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hcp
    subst hc0
    exact ht'n (by simpa using hcl)
  · have hk := IsConj.mul h₂ h₃ (α := (k : ℂ))
      (fun l hl => by rw [← nsmul_eq_mul]; exact nsmul_mem hl k) hct
    rw [map_natCast] at hk
    have h0 : IsConj L L σ 0 ((k : ℂ) * ((c : ℂ) * t) - (k : ℂ) * t') := by
      left
      refine ⟨zero_mem _, ?_⟩
      have : (k : ℂ) * ((c : ℂ) * t) - (k : ℂ) * t' = -((k : ℂ) * (t' - (c : ℂ) * t)) := by ring
      rw [this, ← nsmul_eq_mul]
      exact neg_mem (nsmul_mem hcl k)
    have := IsConj.add h₂ h₃ hk h0
    simpa using this

end GlobalTheory.CMModel
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem mulStable_intCast_add {L : PeriodPair} {w : ℂ} (a : ℤ) (h : MulStable L w) :
    MulStable L ((a : ℂ) + w) := by
  intro ω hω
  rw [add_mul]
  refine add_mem ?_ (h ω hω)
  have : ((a : ℂ) * ω) = a • ω := by rw [zsmul_eq_mul]
  rw [this]
  exact zsmul_mem hω a

theorem mulStable_intCast_sub {L : PeriodPair} {w : ℂ} (a : ℤ) (h : MulStable L w) :
    MulStable L ((a : ℂ) - w) := by
  intro ω hω
  rw [sub_mul]
  refine sub_mem ?_ (h ω hω)
  have : ((a : ℂ) * ω) = a • ω := by rw [zsmul_eq_mul]
  rw [this]
  exact zsmul_mem hω a

theorem ringEquiv_sqrtNegNat (σ : ℂ ≃+* ℂ) (p : ℕ) :
    σ (sqrtNegNat p) = sqrtNegNat p ∨ σ (sqrtNegNat p) = -sqrtNegNat p := by
  have h : σ (sqrtNegNat p) ^ 2 = sqrtNegNat p ^ 2 := by
    rw [← map_pow, sqrtNegNat_sq, map_neg, map_natCast]
  exact sq_eq_sq_iff_eq_or_eq_neg.mp h

theorem stable_kerReps_add_sub : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (a : ℤ) (S S' : Finset ℂ), L.g₂ ∈ F → L.g₃ ∈ F → MulStable L (sqrtNegNat p) → IsKerReps L (a + sqrtNegNat p) S → IsKerReps L (a - sqrtNegNat p) S' → Stable L F (Sum.elim (fun t : S => (t : ℂ)) (fun t : S' => (t : ℂ))) := by
  intro p F L a S S' h2 h3 hm hS hS' σ hσ
  have e2 : L.g₂ = σ L.g₂ := (hσ _ h2).symm
  have e3 : L.g₃ = σ L.g₃ := (hσ _ h3).symm
  have mp := mulStable_intCast_add a hm
  have mm := mulStable_intCast_sub a hm
  have hσa : σ (a : ℂ) = a := map_intCast σ a
  rcases ringEquiv_sqrtNegNat σ p with hs | hs
  · have hp : σ ((a : ℂ) + sqrtNegNat p) = (a : ℂ) + sqrtNegNat p := by rw [map_add (f := _), hσa, hs]
    have hm' : σ ((a : ℂ) - sqrtNegNat p) = (a : ℂ) - sqrtNegNat p := by rw [map_sub, hσa, hs]
    obtain ⟨e, he⟩ := GlobalTheory.T.exists_kernel_equiv_conjugate_points L σ _ S S e2 e3 mp hS (by rw [hp]; exact hS)
    obtain ⟨e', he'⟩ := GlobalTheory.T.exists_kernel_equiv_conjugate_points L σ _ S' S' e2 e3 mm hS' (by rw [hm']; exact hS')
    refine ⟨Equiv.sumCongr e e', ?_⟩
    rintro (t | t)
    · exact he t
    · exact he' t
  · have hp : σ ((a : ℂ) + sqrtNegNat p) = (a : ℂ) - sqrtNegNat p := by
      rw [map_add (f := _), hσa, hs, sub_eq_add_neg]
    have hm' : σ ((a : ℂ) - sqrtNegNat p) = (a : ℂ) + sqrtNegNat p := by
      rw [map_sub, hσa, hs, sub_neg_eq_add]
    obtain ⟨e, he⟩ := GlobalTheory.T.exists_kernel_equiv_conjugate_points L σ _ S S' e2 e3 mp hS (by rw [hp]; exact hS')
    obtain ⟨e', he'⟩ := GlobalTheory.T.exists_kernel_equiv_conjugate_points L σ _ S' S e2 e3 mm hS' (by rw [hm']; exact hS)
    refine ⟨(Equiv.sumCongr e e').trans (Equiv.sumComm _ _), ?_⟩
    rintro (t | t)
    · exact he t
    · exact he' t

end GlobalTheory.CMModel
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem exists_ker_point_sqrtNegNat {p : ℕ} (hp : 1 < p) (L : PeriodPair)
    (hL : MulStable L (sqrtNegNat p)) :
    ∃ t : ℂ, t ∉ L.lattice ∧ sqrtNegNat p * t ∈ L.lattice := by
  have hn : Complex.normSq (sqrtNegNat p) = p := by
    rw [sqrtNegNat, map_mul, Complex.normSq_I, Complex.normSq_ofReal,
      Real.mul_self_sqrt (Nat.cast_nonneg p), mul_one]
  have hp' : (1 : ℝ) < p := by exact_mod_cast hp
  have h0 : sqrtNegNat p ≠ 0 := fun h => by
    rw [h, map_zero] at hn
    linarith
  obtain ⟨S, hS⟩ := kerRepsExist L _ h0 hL
  have hc := kerRepsCard L _ S h0 hL hS
  rw [hn] at hc
  have hpos : S.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < S.card := by
      push_cast at hc
      linarith
    exact_mod_cast this
  obtain ⟨t, ht⟩ := hpos
  have := hS.1 t ht
  exact ⟨t, by tauto, by tauto⟩

theorem g₂_mem_adjoin_j_of_eq (L : PeriodPair) (h0 : L.g₂ ≠ 0) (h : L.g₃ = L.g₂) :
    L.g₂ ∈ ℚ⟮(latticeCurve L).j⟯ := by
  have hΔ := latticeCurve_Δ_ne_zero L
  rw [latticeCurve_Δ, h] at hΔ
  have h27 : L.g₂ - 27 ≠ 0 := fun e => hΔ (by linear_combination L.g₂ ^ 2 * e)
  have hj : (latticeCurve L).j = 1728 * L.g₂ / (L.g₂ - 27) := by
    rw [latticeCurve_j_eq, h, div_eq_div_iff hΔ h27]
    ring
  have hj' : (latticeCurve L).j - 1728 = 1728 * 27 / (L.g₂ - 27) := by
    rw [hj]
    field_simp
    ring
  have e : L.g₂ = 27 * (latticeCurve L).j / ((latticeCurve L).j - 1728) := by
    rw [hj', hj]
    field_simp
  have hm := IntermediateField.mem_adjoin_simple_self ℚ (latticeCurve L).j
  rw [e]
  exact div_mem (mul_mem (ofNat_mem _ 27) hm) (sub_mem hm (ofNat_mem _ 1728))

theorem exists_datum_of_isIntegersLattice : ∀ (p : ℕ) (L₀ : PeriodPair), p.Prime → p % 4 = 3 →
    3 < p → IsIntegersLattice p L₀ → ∃ (L : PeriodPair) (t : ℂ),
      Datum p ℚ⟮(latticeCurve L₀).j⟯ L t ∧ (latticeCurve L).j = (latticeCurve L₀).j := by
  intro p L₀ hp _ h3 hL₀
  obtain ⟨h2, h3', hmul⟩ := GlobalTheory.T.integersLattice_g2_g3_ne_zero_and_mulStable p L₀ hp h3 hL₀
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (L₀.g₃ / L₀.g₂) two_pos
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact div_ne_zero h3' h2 (by rw [← hc]; simp)
  obtain ⟨L, hlat, hg2, hg3, -, hj⟩ := GlobalTheory.T.exists_scaled_periodPair_invariants L₀ c hc0
  have hmul' : MulStable L (sqrtNegNat p) := by
    intro ω hω
    have h1 : c⁻¹ * ω ∈ L₀.lattice := (hlat _).mp (by rwa [mul_inv_cancel_left₀ hc0])
    have h2 := (hlat _).mpr (hmul _ h1)
    rwa [mul_left_comm, mul_inv_cancel_left₀ hc0] at h2
  have hne : L.g₂ ≠ 0 := by
    rw [hg2]
    exact mul_ne_zero (inv_ne_zero (pow_ne_zero _ hc0)) h2
  have heq : L.g₃ = L.g₂ := by
    have : L₀.g₃ = c ^ 2 * L₀.g₂ := by rw [hc, div_mul_cancel₀ _ h2]
    rw [hg2, hg3, this]
    field_simp
  have hmem := g₂_mem_adjoin_j_of_eq L hne heq
  rw [hj] at hmem
  obtain ⟨t, ht, ht'⟩ := exists_ker_point_sqrtNegNat hp.one_lt L hmul'
  exact ⟨L, t, ⟨hmul', hmem, heq ▸ hmem, ht, ht'⟩, hj⟩

end GlobalTheory.CMModel
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Published
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NeronCurve.LieDescent

theorem semiNeg_of_iso {k : Type} [Field k] {C : Scheme.{0}} [Algebra k Γ(C, ⊤)] {F F' : C.Modules} (e : F ≅ F')
    (h : SemiNeg k F) : SemiNeg k F' := fun W r hW i _ =>
  h W r hW (i ≫ e.inv) (mono_comp i e.inv)

def lieBaseIso {C C' : Scheme.{0}} [IsIntegral C] (π : C' ⟶ C) (G : Over C) [GrpObj G] [IsSemiAbelian G] :
    (Scheme.Modules.pullback π).obj (Lie G) ≅ Lie ((Over.pullback π).obj G) :=
  have h := isGrpPullback_pullback G π
  have hg := (exists_isVB_of_isSemiAbelian G).choose_spec.1
  have := isIso_lieBase h hg
  asIso (lieBase h)

end GlobalTheory.NeronCurve.LieDescent

namespace GlobalTheory.NeronCurve

end GlobalTheory.NeronCurve
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ChiGrid
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChiGrid

theorem exists_ringEquiv_mem_iff_star {E : Type} [Field E] [NumberField E] [StarRing E] :
    ∃ σ : FractionalIdeal (𝓞 E)⁰ E ≃+* FractionalIdeal (𝓞 E)⁰ E,
      ∀ (a : FractionalIdeal (𝓞 E)⁰ E) (x : E), x ∈ σ a ↔ star x ∈ a := by
  let τ : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv (starRingAut : E ≃+* E)
  have hτ : ∀ x : E, IsFractionRing.ringEquivOfRingEquiv (K := E) (L := E) τ x = star x := by
    intro x
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
    rw [map_div₀, IsFractionRing.ringEquivOfRingEquiv_algebraMap,
      IsFractionRing.ringEquivOfRingEquiv_algebraMap, star_div₀]
    rfl
  refine ⟨FractionalIdeal.ringEquivOfRingEquiv E E τ, fun a x => ⟨?_, fun h => ?_⟩⟩
  · rintro ⟨y, hy, rfl⟩
    have h := (congrArg star (hτ y)).trans (star_star y)
    exact h.symm ▸ hy
  · exact ⟨star x, h, (hτ (star x)).trans (star_star x)⟩

theorem stairId_ne_zero_and_mem_rev_iff : ∀ (D : D7) (𝔞 𝔞' : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E), 𝔞 ≠ 0 → (∀ x, x ∈ 𝔞' ↔ star x ∈ 𝔞) → ∀ (c : ℕ) (p : Fin c), stairId 𝔞 𝔞' c p ≠ 0 ∧ ∀ x, x ∈ stairId 𝔞 𝔞' c p.rev ↔ star x ∈ (stairId 𝔞 𝔞' c p)⁻¹ := by
  intro D 𝔞 𝔞' h0 h c p
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_mem_iff_star (E := D.host.E)
  have h1 : σ 𝔞 = 𝔞' := by
    ext x
    rw [hσ, h]
  have h2 : σ 𝔞' = 𝔞 := by
    ext x
    rw [hσ, h, star_star]
  have h0' : 𝔞' ≠ 0 := h1 ▸ (map_ne_zero_iff _ σ.injective).2 h0
  refine ⟨mul_ne_zero (pow_ne_zero _ h0) (inv_ne_zero (pow_ne_zero _ h0')), fun x => ?_⟩
  have h3 : σ (stairId 𝔞' 𝔞 c p.rev) = stairId 𝔞 𝔞' c p.rev := by
    unfold stairId
    rw [map_mul, map_inv₀, map_pow, map_pow, h1, h2]
  rw [← stairId_rev, ← hσ, h3]

end GlobalTheory.ChiGrid
end
