module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle097
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle068
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle105
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle043
public import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle063
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle102
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.PicardGroup
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle007
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle096
public import Mathlib.FieldTheory.Galois.Infinite
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois GlobalTheory.GeoFix

theorem _root_.GlobalTheory.T.mem_subfield_of_fixed_by_geometric_tower_galois : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (n : ℕ) (F : Subfield Ω), (∀ c : O0 p, algebraMap (O0 p) Ω c ∈ F) → (∀ x : Ω, IsAlgZp (p := p) x → x ∈ F) → T.qq n ∈ F → ∀ o : Ω, (∀ g ∈ Ggeo (p := p) Ω ⊓ Gn T n, g o = o) → o ∈ F := by
  intro p hp Ω _ _ hc T n F hO hA hq o ho
  have : CharZero Ω := GlobalTheory.K5.Basic.charZero_of_isClo hc
  have : IsAlgClosed Ω := hc.clo
  let f : O0 p →+* F := (algebraMap (O0 p) Ω).codRestrict F hO
  let : Algebra (O0 p) F := f.toAlgebra
  have : IsScalarTower (O0 p) F Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hf : Function.Injective (algebraMap (O0 p) F) :=
    fun _ _ h => hc.inj (congrArg Subtype.val h)
  have : Algebra.IsAlgebraic (O0 p) Ω := hc.alg
  have : Algebra.IsAlgebraic F Ω := Algebra.IsAlgebraic.extendScalars (R := O0 p) hf
  have : IsAlgClosure F Ω := ⟨hc.clo, inferInstance⟩
  have : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  have hζ : IsAlgZp (p := p) (T.ζ n) := by
    refine ⟨Polynomial.X ^ (p ^ n) - 1, ?_, ?_⟩
    · exact (Polynomial.monic_X_pow_sub_C (1 : ℤ_[p]) (pow_ne_zero _ hp.out.ne_zero)).ne_zero
    · simp [(T.prim n).pow_eq_one]
  have ho' : o ∈ Set.range (algebraMap F Ω) := by
    refine (InfiniteGalois.mem_range_algebraMap_iff_fixed o).2 fun σ => ?_
    let g : Gal p Ω := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) fun c => σ.commutes (f c)
    have hg : g ∈ Ggeo (p := p) Ω ⊓ Gn T n := by
      refine ⟨fun x hx => σ.commutes ⟨x, hA x hx⟩, ?_, ?_⟩
      · show g • T.ζ n = T.ζ n
        exact σ.commutes ⟨T.ζ n, hA _ hζ⟩
      · show g • T.qq n = T.qq n
        exact σ.commutes ⟨T.qq n, hq⟩
    exact ho g hg
  obtain ⟨x, rfl⟩ := ho'
  exact x.2
end

section

open GlobalTheory.K5 Polynomial
open scoped NNReal

namespace GlobalTheory.K5.Dense

theorem exists_near_root {Ωl : Type} [Field Ωl] [CharZero Ωl] (v : Valuation Ωl ℝ≥0)
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] (j : Ω →+* Ωl) (e : Ωl) (t : ℝ≥0) (Q : ℤ[X])
    (h : v (Q.eval₂ (Int.castRingHom Ωl) e) < v (Q.leadingCoeff : Ωl) * t ^ Q.natDegree) :
    ∃ a : Ω, v (e - j a) < t := by
  have : CharZero Ω := j.charZero
  by_contra hcon
  push Not at hcon
  set R : Polynomial Ω := Q.map (Int.castRingHom Ω) with hR
  have hinj : Function.Injective (Int.castRingHom Ω) := Int.cast_injective
  have hdeg : R.natDegree = Q.natDegree := natDegree_map_eq_of_injective hinj Q
  have hlc : R.leadingCoeff = (Q.leadingCoeff : Ω) := leadingCoeff_map_of_injective hinj Q
  have hcard : Multiset.card R.roots = R.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hprod := C_leadingCoeff_mul_prod_multiset_X_sub_C hcard
  have h1 : Q.eval₂ (Int.castRingHom Ωl) e = R.eval₂ j e := by
    rw [hR, eval₂_map]
    congr 1
    exact RingHom.ext_int _ _
  have h2 : R.eval₂ j e = (Q.leadingCoeff : Ωl) * (R.roots.map fun a => e - j a).prod := by
    conv_lhs => rw [← hprod]
    rw [eval₂_mul, eval₂_C, eval₂_multiset_prod, Multiset.map_map, hlc, map_intCast]
    simp
  rw [h1, h2, map_mul, map_multiset_prod, Multiset.map_map] at h
  have h3 : t ^ Q.natDegree ≤ (R.roots.map (v ∘ fun a => e - j a)).prod := by
    have := Multiset.pow_card_le_prod (s := R.roots.map (v ∘ fun a => e - j a)) (a := t) (by
      intro x hx
      obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hx
      exact hcon a)
    rwa [Multiset.card_map, hcard, hdeg] at this
  exact absurd h (not_lt.2 (by gcongr))

theorem exists_approx {p : ℕ} [Fact p.Prime] (P : ℤ_[p][X]) (N : ℕ) :
    ∃ (Q : ℤ[X]) (R : ℤ_[p][X]), Q.natDegree ≤ P.natDegree ∧
      P = Q.map (Int.castRingHom ℤ_[p]) + C ((p : ℤ_[p]) ^ N) * R := by
  have h : ∀ x : ℤ_[p], ∃ (m : ℤ) (r : ℤ_[p]), x = m + (p : ℤ_[p]) ^ N * r := by
    intro x
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.1 (PadicInt.appr_spec N x)
    exact ⟨PadicInt.appr x N, r, by push_cast; linear_combination hr⟩
  choose m r hmr using h
  refine ⟨∑ i ∈ Finset.range (P.natDegree + 1), monomial i (m (P.coeff i)),
    ∑ i ∈ Finset.range (P.natDegree + 1), monomial i (r (P.coeff i)), ?_, ?_⟩
  · refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
    exact (natDegree_monomial_le _).trans (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))

  · rw [Polynomial.map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    conv_lhs => rw [P.as_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_monomial, C_mul_monomial, ← map_add (f := _), eq_intCast, ← hmr]

theorem exists_cong : ∀ (p : ℕ) [Fact p.Prime] (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl],
    IsClo p Ωl → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (j : Ω →+* Ωl) (k : ℕ) (e : Ωl),
    IsInt (p := p) e → IsAlgZp (p := p) e → ∃ a : Ω, IsInt (p := p) (j a) ∧ Cong (p := p) k e (j a) := by
  intro p hp Ωl _ _ hclo Ω _ _ j k e he ⟨P, hP0, hP⟩
  have : CharZero Ωl := Basic.charZero_of_isClo hclo
  have hpne : (p : Ωl) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hvaluation : ∃ v : Valuation Ωl ℝ≥0, (∀ x, v x ≤ 1 ↔ IsInt (p := p) x) ∧
      v (p : Ωl) < 1 := by
    obtain ⟨_, hdvr, hirr⟩ := GlobalTheory.T.completed_laurent_isDVR_statement p
    have : IsAdicComplete (IsLocalRing.maximalIdeal (O0 p)) (O0 p) := by
      rw [hirr.maximalIdeal_eq]
      exact GlobalTheory.T.unramified_integers_adic_complete p
    have := hclo.alg
    obtain ⟨v, hv⟩ := GlobalTheory.T.exists_valuation_le_one_iff_isIntegral_of_complete_dvr
      (O0 p) Ωl hclo.inj
    refine ⟨v, hv, lt_of_le_of_ne ((hv _).2 ?_) ?_⟩
    · simpa [IsInt] using Basic.isInt_intCast (p := p) (Ω := Ωl) (p : ℤ)
    · intro h_eq
      have hi : v (p : Ωl)⁻¹ ≤ 1 := by rw [map_inv₀, h_eq, inv_one]
      exact Basic.not_cong_one_zero hclo 1 one_ne_zero
        ⟨(p : Ωl)⁻¹, (hv _).1 hi, by rw [sub_zero, pow_one, mul_inv_cancel₀ hpne]⟩
  obtain ⟨v, hv, hp1⟩ := hvaluation
  set φ : ℤ_[p] →+* Ωl := (algebraMap (O0 p) Ωl).comp (algebraMap ℤ_[p] (O0 p)) with hφ
  have hPe : P.eval₂ φ e = 0 := by rwa [aeval_def, eval₂_map] at hP
  have hφint : ∀ x, v (φ x) ≤ 1 := fun x => (hv _).2 isIntegral_algebraMap
  have hc0 : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hP0
  have hc : φ P.leadingCoeff ≠ 0 := by
    rw [PadicInt.unitCoeff_spec hc0, map_mul, map_pow, map_natCast]
    exact mul_ne_zero ((Units.isUnit _).map φ).ne_zero (pow_ne_zero _ hpne)
  have hvc : 0 < v (φ P.leadingCoeff) := (Valuation.pos_iff v).2 hc
  have hp0 : 0 < v (p : Ωl) := (Valuation.pos_iff v).2 hpne
  obtain ⟨N, hN⟩ := NNReal.exists_pow_lt_of_lt_one
    (mul_pos hvc (pow_pos (pow_pos hp0 k) P.natDegree)) hp1
  have hpk : v (p : Ωl) ^ k ≤ 1 := pow_le_one₀ zero_le hp1.le
  have hN' : v (p : Ωl) ^ N < v (φ P.leadingCoeff) :=
    hN.trans_le (mul_le_of_le_one_right zero_le (pow_le_one₀ zero_le hpk))
  obtain ⟨Q, R, hdeg, hQR⟩ := exists_approx P N
  have hsmall : ∀ y : Ωl, v y ≤ 1 → v ((p : Ωl) ^ N * y) ≤ v (p : Ωl) ^ N := by
    intro y hy
    rw [map_mul, map_pow]
    exact mul_le_of_le_one_right zero_le hy
  have hco : φ P.leadingCoeff = (Q.coeff P.natDegree : Ωl) + (p : Ωl) ^ N * φ (R.coeff P.natDegree) := by
    have := congrArg (fun (S : ℤ_[p][X]) => φ (S.coeff P.natDegree)) hQR
    simp only [coeff_add, coeff_C_mul, coeff_map, map_add (f := _), map_mul, eq_intCast, map_intCast] at this
    rw [map_pow, map_natCast] at this
    exact this
  have hvQ : v (Q.coeff P.natDegree : Ωl) = v (φ P.leadingCoeff) := by
    rw [eq_sub_of_add_eq hco.symm]
    exact Valuation.map_sub_eq_of_lt_left v ((hsmall _ (hφint _)).trans_lt hN')
  have hQ0 : Q.coeff P.natDegree ≠ 0 := by
    intro h0
    rw [h0, Int.cast_zero, map_zero] at hvQ
    exact hvc.ne hvQ
  have hdeg' : Q.natDegree = P.natDegree := natDegree_eq_of_le_of_coeff_ne_zero hdeg hQ0
  have hRe : v (R.eval₂ φ e) ≤ 1 := by
    rw [eval₂_eq_sum_range]
    refine Valuation.map_sum_le v fun i _ => ?_
    rw [map_mul, map_pow]
    exact (mul_le_of_le_one_right zero_le (pow_le_one₀ zero_le ((hv _).2 he))).trans (hφint _)
  have hQe : Q.eval₂ (Int.castRingHom Ωl) e = -((p : Ωl) ^ N * R.eval₂ φ e) := by
    rw [hQR, eval₂_add, eval₂_mul, eval₂_C, eval₂_map, map_pow, map_natCast,
      RingHom.ext_int (φ.comp _) (Int.castRingHom Ωl)] at hPe
    exact eq_neg_of_add_eq_zero_left hPe
  obtain ⟨a, ha⟩ := exists_near_root v j e (v (p : Ωl) ^ k) Q (by
    rw [hQe, Valuation.map_neg, leadingCoeff, hdeg', hvQ]
    exact (hsmall _ hRe).trans_lt hN)
  refine ⟨a, (hv _).1 ?_, (e - j a) / (p : Ωl) ^ k, (hv _).1 ?_, ?_⟩
  · rw [show j a = e - (e - j a) by ring]
    exact Valuation.map_sub_le v ((hv _).2 he) (ha.le.trans hpk)
  · rw [map_div₀, map_pow]
    exact div_le_one_of_le₀ ha.le zero_le
  · field_simp

end GlobalTheory.K5.Dense
end

section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.K5

theorem exists_valuation_isInt : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω],
    IsClo p Ω → ∃ v : Valuation Ω ℝ≥0, (∀ x : Ω, v x ≤ 1 ↔ IsInt (p := p) x) ∧
      (∀ (g : Gal p Ω) (x : Ω), v (g x) = v x) ∧ 0 < v (p : Ω) ∧ v (p : Ω) < 1 := by
  intro p _ Ω _ _ h
  obtain ⟨_, hdvr, hirr⟩ := GlobalTheory.T.completed_laurent_isDVR_statement p
  have hmax : IsLocalRing.maximalIdeal (O0 p) = Ideal.span {(p : O0 p)} :=
    hirr.maximalIdeal_eq
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal (O0 p)) (O0 p) := by
    rw [hmax]; exact GlobalTheory.T.unramified_integers_adic_complete p
  haveI := h.alg
  obtain ⟨v, hv⟩ := GlobalTheory.T.exists_valuation_le_one_iff_isIntegral_of_complete_dvr (O0 p) Ω h.inj
  have hinv := GlobalTheory.T.valuation_algEquiv_apply_eq_of_le_one_iff_isIntegral (O0 p) Ω h.inj v hv
  haveI : CharZero Ω := GlobalTheory.K5.Basic.charZero_of_isClo h
  have hp0 : (p : Ω) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  refine ⟨v, hv, hinv, ?_, ?_⟩
  · exact (Valuation.pos_iff v).2 hp0
  · have hle : v (p : Ω) ≤ 1 := (hv _).2 (by
      have := GlobalTheory.K5.Basic.isInt_intCast (p := p) (Ω := Ω) (p : ℤ)
      simpa [IsInt] using this)
    refine lt_of_le_of_ne hle ?_
    intro heq
    have hi : v (p : Ω)⁻¹ ≤ 1 := by rw [map_inv₀, heq, inv_one]
    have hint : IsInt (p := p) ((p : Ω)⁻¹) := (hv _).1 hi
    exact GlobalTheory.K5.Basic.not_cong_one_zero h 1 one_ne_zero
      ⟨(p : Ω)⁻¹, hint, by rw [sub_zero, pow_one, mul_inv_cancel₀ hp0]⟩

end GlobalTheory.K5
end

section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

theorem _root_.GlobalTheory.T.exists_galoisInvariant_valuation_integers_eq_integral :
    ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω],
      IsClo p Ω → ∃ v : Valuation Ω ℝ≥0,
        (∀ x : Ω, v x ≤ 1 ↔ GlobalTheory.K5.IsInt (p := p) x) ∧
        (∀ (g : Gal p Ω) (x : Ω), v (g x) = v x) ∧ 0 < v (p : Ω) ∧ v (p : Ω) < 1 := by
  intro p _ Ω _ _ h
  obtain ⟨_, hdvr, hirr⟩ := GlobalTheory.T.completed_laurent_isDVR_statement p
  have hmax : IsLocalRing.maximalIdeal (O0 p) = Ideal.span {(p : O0 p)} :=
    hirr.maximalIdeal_eq
  have : IsAdicComplete (IsLocalRing.maximalIdeal (O0 p)) (O0 p) := by
    rw [hmax]
    exact GlobalTheory.T.unramified_integers_adic_complete p
  have := h.alg
  have hvaluation :=
    GlobalTheory.T.exists_valuation_le_one_iff_isIntegral_of_complete_dvr (O0 p) Ω h.inj
  obtain ⟨v, hv⟩ := hvaluation
  have hinv := GlobalTheory.T.valuation_algEquiv_apply_eq_of_le_one_iff_isIntegral (O0 p) Ω h.inj v hv
  have : CharZero Ω := GlobalTheory.K5.Basic.charZero_of_isClo h
  have hp0 : (p : Ω) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  refine ⟨v, hv, hinv, (Valuation.pos_iff v).2 hp0, ?_⟩
  have hle : v (p : Ω) ≤ 1 := (hv _).2 (by
    have := GlobalTheory.K5.Basic.isInt_intCast (p := p) (Ω := Ω) (p : ℤ)
    simpa [GlobalTheory.K5.IsInt] using this)
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hi : v (p : Ω)⁻¹ ≤ 1 := by rw [map_inv₀, heq, inv_one]
  have hint : GlobalTheory.K5.IsInt (p := p) ((p : Ω)⁻¹) := (hv _).1 hi
  exact GlobalTheory.K5.Basic.not_cong_one_zero h 1 one_ne_zero
    ⟨(p : Ω)⁻¹, hint, by rw [sub_zero, pow_one, mul_inv_cancel₀ hp0]⟩
end

section

open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare.EpsProj

variable {G : Type} [Group G] [Fintype G] {S : G → Prop} {χ : G → ℂ}

omit [Fintype G] in
theorem pow_spec (h1 : S 1) (hm : ∀ u v, S u → S v → S (u * v)) (c1 : χ 1 = 1)
    (cm : ∀ u v, S u → S v → χ (u * v) = χ u * χ v) {u : G} (hu : S u) (n : ℕ) :
    S (u ^ n) ∧ χ (u ^ n) = χ u ^ n := by
  induction n with
  | zero => simp [h1, c1]
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact ⟨hm _ _ ih.1 hu, by rw [cm _ _ ih.1 hu, ih.2]⟩

theorem inv_spec (h1 : S 1) (hm : ∀ u v, S u → S v → S (u * v)) (c1 : χ 1 = 1)
    (cm : ∀ u v, S u → S v → χ (u * v) = χ u * χ v) {u : G} (hu : S u) :
    S u⁻¹ ∧ χ u⁻¹ = (χ u)⁻¹ ∧ ‖χ u‖ = 1 := by
  have hc : Fintype.card G ≠ 0 := Fintype.card_ne_zero
  have hi : u⁻¹ = u ^ (Fintype.card G - 1) := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hc), pow_card_eq_one]
  have hS : S u⁻¹ := by rw [hi]; exact (pow_spec h1 hm c1 cm hu _).1
  refine ⟨hS, ?_, ?_⟩
  · have := cm _ _ hu hS
    rw [mul_inv_cancel, c1] at this
    exact (eq_inv_of_mul_eq_one_right this.symm)
  · have := (pow_spec h1 hm c1 cm hu (Fintype.card G)).2
    rw [pow_card_eq_one, c1] at this
    exact Complex.norm_eq_one_of_pow_eq_one this.symm hc

theorem eps_mul (h1 : S 1) (hm : ∀ u v, S u → S v → S (u * v)) (c1 : χ 1 = 1)
    (cm : ∀ u v, S u → S v → χ (u * v) = χ u * χ v) {u : G} (hu : S u) (y : G) :
    eps S χ (u⁻¹ * y) = χ u * eps S χ y := by
  obtain ⟨hi, ci, -⟩ := inv_spec h1 hm c1 cm hu
  unfold eps
  by_cases hy : S y
  · rw [if_pos hy, if_pos (hm _ _ hi hy), cm _ _ hi hy, ci, mul_inv, inv_inv, mul_div_assoc]
  · have : ¬ S (u⁻¹ * y) := fun h => hy (by simpa using hm _ _ hu h)
    rw [if_neg hy, if_neg this, mul_zero]

omit [Group G] in
theorem sum_ite_card : ∑ y, (if S y then (1 : ℂ) else 0) = (Nat.card {u // S u} : ℂ) := by
  rw [Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem sum_eps_chi (h1 : S 1) (hm : ∀ u v, S u → S v → S (u * v)) (c1 : χ 1 = 1)
    (cm : ∀ u v, S u → S v → χ (u * v) = χ u * χ v) :
    ∑ y, eps S χ y * χ y = 1 := by
  haveI : Nonempty {u // S u} := ⟨⟨1, h1⟩⟩
  have hc : (Nat.card {u // S u} : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have : ∀ y, eps S χ y * χ y = (if S y then (1 : ℂ) else 0) / (Nat.card {u // S u} : ℂ) := by
    intro y
    unfold eps
    by_cases hy : S y
    · have hn : χ y ≠ 0 := by
        intro h
        have := (inv_spec h1 hm c1 cm hy).2.2
        rw [h] at this
        simp at this
      rw [if_pos hy, if_pos hy]
      field_simp
    · simp [hy]
  simp_rw [this]
  rw [← Finset.sum_div, sum_ite_card, div_self hc]

theorem isProj_eps (h1 : S 1) (hm : ∀ u v, S u → S v → S (u * v)) (c1 : χ 1 = 1)
    (cm : ∀ u v, S u → S v → χ (u * v) = χ u * χ v) : IsProj (eps S χ) := by
  refine ⟨?_, ?_⟩
  · funext x
    unfold conv
    have : ∀ y, eps S χ y * eps S χ (y⁻¹ * x) = eps S χ y * χ y * eps S χ x := by
      intro y
      by_cases hy : S y
      · rw [eps_mul h1 hm c1 cm hy, mul_assoc]
      · have : eps S χ y = 0 := by simp [eps, hy]
        simp [this]
    simp_rw [this]
    rw [← Finset.sum_mul, sum_eps_chi h1 hm c1 cm, one_mul]
  · intro x
    unfold eps
    by_cases hx : S x
    · obtain ⟨hi, ci, hn⟩ := inv_spec h1 hm c1 cm hx
      rw [if_pos hx, if_pos hi, ci, map_div₀, map_inv₀, map_natCast, Complex.inv_eq_conj hn]
    · have : ¬ S x⁻¹ := fun h => hx (by simpa using (inv_spec h1 hm c1 cm h).1)
      rw [if_neg hx, if_neg this, map_zero]

theorem mem_range_iff {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M)
    (h1 : S 1) (hm : ∀ u v, S u → S v → S (u * v)) (c1 : χ 1 = 1)
    (cm : ∀ u v, S u → S v → χ (u * v) = χ u * χ v) (x : M) :
    x ∈ LinearMap.range (op ρ (eps S χ)) ↔ ∀ u, S u → ρ u x = χ u • x := by
  constructor
  · rintro ⟨z, rfl⟩ u hu

    simp only [op, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft u) _ _ fun y => ?_
    have := eps_mul h1 hm c1 cm hu (u * y)
    rw [inv_mul_cancel_left] at this
    simp only [Equiv.coe_mulLeft, map_mul, Module.End.mul_apply, smul_smul]
    rw [← this]
  · intro h
    refine ⟨x, ?_⟩
    simp only [op, LinearMap.sum_apply, LinearMap.smul_apply]
    have : ∀ y, eps S χ y • ρ y x = (eps S χ y * χ y) • x := by
      intro y
      by_cases hy : S y
      · rw [h y hy, smul_smul]
      · have : eps S χ y = 0 := by simp [eps, hy]
        simp [this]
    simp_rw [this]
    rw [← Finset.sum_smul, sum_eps_chi h1 hm c1 cm, one_smul]

theorem eps_spec : ∀ (G : Type) [Group G] [Fintype G] (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ G M), ∀ (S : G → Prop) (χ : G → ℂ), S 1 → (∀ u v, S u → S v → S (u * v)) → χ 1 = 1 → (∀ u v, S u → S v → χ (u * v) = χ u * χ v) → IsProj (eps S χ) ∧ eps S χ 1 = ((Nat.card {u // S u} : ℂ))⁻¹ ∧ (∀ x : M, x ∈ LinearMap.range (op ρ (eps S χ)) ↔ ∀ u, S u → ρ u x = χ u • x) ∧ ∀ (n : ℕ) (x : Fin n → M), LinearIndependent ℂ x → (∀ i u, S u → ρ u (x i) = χ u • x i) → n ≤ rk ρ (eps S χ) := by
  intro G _ _ M _ _ _ ρ S χ h1 hm c1 cm
  refine ⟨isProj_eps h1 hm c1 cm, ?_, mem_range_iff ρ h1 hm c1 cm, ?_⟩
  · simp only [eps, if_pos h1, c1, inv_one, one_div]
  · intro n x hx h
    have hmem : ∀ i, x i ∈ LinearMap.range (op ρ (eps S χ)) :=
      fun i => (mem_range_iff ρ h1 hm c1 cm _).2 (h i)
    have hli : LinearIndependent ℂ (fun i => (⟨x i, hmem i⟩ : LinearMap.range (op ρ (eps S χ)))) :=
      LinearIndependent.of_comp (LinearMap.range (op ρ (eps S χ))).subtype hx
    simpa [rk] using hli.fintype_card_le_finrank

end GlobalTheory.BadShare.EpsProj
end

section

open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

theorem conv_tens {ι G : Type} [Fintype ι] [Group G] [Fintype G] (a b : ι → G → ℂ) :
    conv (tens a) (tens b) = tens fun v => conv (a v) (b v) := by
  funext x
  simp only [conv, tens]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.prod_mul_distrib]
  rfl

theorem conv_tens2 {G G' : Type} [Group G] [Fintype G] [Group G'] [Fintype G'] (a a' : G → ℂ) (b b' : G' → ℂ) :
    conv (tens2 a b) (tens2 a' b') = tens2 (conv a a') (conv b b') := by
  funext x
  simp only [conv, tens2]
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
  simp only [Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv]
  ring

theorem tens_calculus : ∀ (ι G G' : Type) [Fintype ι] [Group G] [Fintype G] [Group G'] [Fintype G'], (∀ a b : ι → G → ℂ, conv (tens a) (tens b) = tens fun v => conv (a v) (b v)) ∧ (∀ a : ι → G → ℂ, (∀ v, IsProj (a v)) → IsProj (tens a)) ∧ (∀ (a a' : G → ℂ) (b b' : G' → ℂ), conv (tens2 a b) (tens2 a' b') = tens2 (conv a a') (conv b b')) ∧ (∀ (a : G → ℂ) (b : G' → ℂ), IsProj a → IsProj b → IsProj (tens2 a b)) ∧ tens2 (dirac : G → ℂ) (dirac : G' → ℂ) = dirac ∧ ∀ (a a' : G → ℂ) (b b' : G' → ℂ), tens2 (a - a') b = tens2 a b - tens2 a' b ∧ tens2 a (b - b') = tens2 a b - tens2 a b' := by
  intro ι G G' _ _ _ _ _
  refine ⟨conv_tens, fun a h => ⟨?_, fun x => ?_⟩, conv_tens2, fun a b ha hb => ⟨?_, fun x => ?_⟩, ?_,
    fun a a' b b' => ⟨?_, ?_⟩⟩
  · rw [conv_tens]
    congr 1
    funext v
    exact (h v).1
  · simp only [tens, map_prod]
    exact Finset.prod_congr rfl fun v _ => (h v).2 (x v)
  · rw [conv_tens2, ha.1, hb.1]
  · simp only [tens2, map_mul, Prod.fst_inv, Prod.snd_inv, ha.2, hb.2]
  · funext ⟨x, y⟩
    simp only [tens2, dirac, Prod.mk_eq_one]
    by_cases hx : x = 1 <;> by_cases hy : y = 1 <;> simp [hx, hy]
  · funext x
    simp only [tens2, Pi.sub_apply, sub_mul]
  · funext x
    simp only [tens2, Pi.sub_apply, mul_sub]

end GlobalTheory.BadShare
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.exists_common_level_span_multiple : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (K : ℕ) {ι : Type} [Fintype ι] (y : ι → X.Kl l), 0 < K → ∃ M : ℕ, 0 < M ∧ K ∣ M ∧ ∀ i, y i ∈ X.Lev l M := by
  first | exact @GlobalTheory.KZ.Tower.exists_lev_family | exact GlobalTheory.KZ.Tower.exists_lev_family | (intros; apply GlobalTheory.KZ.Tower.exists_lev_family <;> assumption)
end
