module

public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle001
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle009
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle024
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesIntegralBoundedClosure
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle002
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsFieldCmCurvesUnitDiscriminant
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ModularJExpansionAndPolynomialAndIsIntegral
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle025
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ
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
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.Valuation.Integral
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
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable

@[expose] public section

section

open GlobalTheory.ConvSer Filter Topology

namespace GlobalTheory.ConvSer

theorem tendsto_cofinite_double {K α β : Type*} [NormedField K] (c : α → β → K) (d : β → K)
    (C : ℝ) (hC : ∀ a b, ‖c a b‖ ≤ C) (hc : ∀ b, Tendsto (fun a => c a b) cofinite (𝓝 0))
    (hd : Tendsto d cofinite (𝓝 0)) :
    Tendsto (fun p : α × β => c p.1 p.2 * d p.2) cofinite (𝓝 0) := by
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  have h1 : Tendsto (fun b => C * ‖d b‖) cofinite (𝓝 0) := by
    simpa using (tendsto_zero_iff_norm_tendsto_zero.1 hd).const_mul C
  have h2 : {b | ¬ C * ‖d b‖ < ε}.Finite :=
    eventually_cofinite.1 (h1.eventually (gt_mem_nhds hε))
  have h3 : ∀ b, {a | ¬ ‖c a b * d b‖ < ε}.Finite := by
    intro b
    have : Tendsto (fun a => c a b * d b) cofinite (𝓝 0) := by
      simpa using (hc b).mul_const (d b)
    exact eventually_cofinite.1 (NormedAddGroup.tendsto_nhds_zero.1 this ε hε)
  rw [eventually_cofinite]
  refine (h2.biUnion (t := fun b => (fun a => (a, b)) '' {a | ¬ ‖c a b * d b‖ < ε})
    (fun b _ => (h3 b).image _)).subset ?_
  rintro ⟨a, b⟩ hp
  simp only [Set.mem_ofPred_eq] at hp
  simp only [Set.mem_iUnion]
  refine ⟨b, ?_, a, hp, rfl⟩
  intro hlt
  apply hp
  rw [norm_mul]
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (hC a b) (norm_nonneg _)) hlt

theorem small_csub_of_small (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (σ τ : Type) [Fintype σ] (t : σ → MvPowerSeries τ K) (ht : ∀ i, Small (t i))
    (u : MvPowerSeries σ K) (hu : Small u) : Small (csub t u) := by
  obtain ⟨hI, hB, hP, hC, -⟩ := GlobalTheory.BddAlg.bdd_alg K σ
  set c := MvPowerSeries.constantCoeff u with hc
  have hCi : Intg (MvPowerSeries.C c : MvPowerSeries σ K) := (hC c).2.1 hu.2.le
  have h1 : Intg (u - MvPowerSeries.C c) := (hI _ _ hu.1 hCi).2.1
  have hb1 : Bdd (u - MvPowerSeries.C c) := (hP _ 0).2.2 h1
  have hbu : Bdd u := (hP _ 0).2.2 hu.1
  have h2 : Small (csub t (u - MvPowerSeries.C c)) :=
    (GlobalTheory.ConvSer.csub_hasSum_and_bounds K σ τ t _ ht hb1).2.2.2 h1 (by simp [hc])
  obtain ⟨hR, hRC, -⟩ := GlobalTheory.T.mvPowerSeriesConvergentSubst_isRingHom_on_bounded K σ τ t ht
  have h3 : csub t u = csub t (u - MvPowerSeries.C c) + MvPowerSeries.C c := by
    rw [(hR _ _ hbu (hC c).1).2.1, hRC]; ring
  refine ⟨(GlobalTheory.ConvSer.csub_hasSum_and_bounds K σ τ t _ ht hbu).2.2.1 hu.1, ?_⟩
  rw [h3, map_add (f := _), MvPowerSeries.constantCoeff_C]
  exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h2.2 hu.2)

theorem csub_assoc : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (ρ σ τ : Type) [Fintype ρ] [Fintype σ] (s : ρ → MvPowerSeries σ K)
    (t : σ → MvPowerSeries τ K) (S : MvPowerSeries ρ K), (∀ j, Small (s j)) →
    (∀ i, Small (t i)) → Bdd S →
    (∀ j, Small (csub t (s j))) ∧ csub t (csub s S) = csub (fun j => csub t (s j)) S := by
  intro K _ _ _ ρ σ τ _ _ s t S hs ht hS
  have hst : ∀ j, Small (csub t (s j)) := fun j => small_csub_of_small K σ τ t ht _ (hs j)
  refine ⟨hst, ?_⟩
  obtain ⟨hI, hB, hP, hC, -, hF, -⟩ := GlobalTheory.BddAlg.bdd_alg K σ
  obtain ⟨-, -, -, hRP, hRF, -⟩ := GlobalTheory.T.mvPowerSeriesConvergentSubst_isRingHom_on_bounded K σ τ t ht
  have hint : ∀ ν : ρ →₀ ℕ, Intg (∏ j, s j ^ ν j) := fun ν =>
    ((hF ρ Finset.univ _).1 fun j _ => (hP _ _).1 (hs j).1).1
  have hbd : ∀ ν : ρ →₀ ℕ, Bdd (∏ j, s j ^ ν j) := fun ν => (hP _ 0).2.2 (hint ν)
  have hprod : ∀ ν : ρ →₀ ℕ, csub t (∏ j, s j ^ ν j) = ∏ j, csub t (s j) ^ ν j := by
    intro ν
    rw [hRF ρ Finset.univ _ fun j _ => (hP _ 0).2.2 ((hP _ _).1 (hs j).1)]
    exact Finset.prod_congr rfl fun j _ => hRP _ _ ((hP _ 0).2.2 (hs j).1)
  ext μ
  obtain ⟨C, hCS⟩ := id hS
  let c : (ρ →₀ ℕ) → (σ →₀ ℕ) → K := fun ν l =>
    MvPowerSeries.coeff ν S * MvPowerSeries.coeff l (∏ j, s j ^ ν j)
  let d : (σ →₀ ℕ) → K := fun l => MvPowerSeries.coeff μ (∏ i, t i ^ l i)
  have hcs : ∀ l, HasSum (fun ν => c ν l) (MvPowerSeries.coeff l (csub s S)) :=
    (GlobalTheory.ConvSer.csub_hasSum_and_bounds K ρ σ s S hs hS).1
  have hd : Tendsto d cofinite (𝓝 0) := by
    let U : MvPowerSeries σ K := fun _ => 1
    have hU : ∀ l, MvPowerSeries.coeff l U = 1 := fun _ => rfl
    have := ((GlobalTheory.ConvSer.csub_hasSum_and_bounds K σ τ t U ht ⟨1, fun l => by simp [hU]⟩).1 μ).summable.tendsto_cofinite_zero
    simpa only [hU, one_mul] using this
  have hsum : Summable (fun p : (ρ →₀ ℕ) × (σ →₀ ℕ) => c p.1 p.2 * d p.2) := by
    apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    refine tendsto_cofinite_double c d C ?_ (fun l => (hcs l).summable.tendsto_cofinite_zero) hd
    intro ν l
    simp only [c, norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (hint ν l)).trans (hCS ν)
  have hA : HasSum (fun ν : ρ →₀ ℕ => MvPowerSeries.coeff ν S *
      MvPowerSeries.coeff μ (∏ j, csub t (s j) ^ ν j))
      (∑' p : (ρ →₀ ℕ) × (σ →₀ ℕ), c p.1 p.2 * d p.2) := by
    refine hsum.hasSum.prod_fiberwise fun ν => ?_
    rw [← hprod]
    have := ((GlobalTheory.ConvSer.csub_hasSum_and_bounds K σ τ t _ ht (hbd ν)).1 μ).mul_left (MvPowerSeries.coeff ν S)
    simpa only [c, d, mul_assoc] using this
  have hB' : HasSum (fun l : σ →₀ ℕ => MvPowerSeries.coeff l (csub s S) * d l)
      (∑' p : (ρ →₀ ℕ) × (σ →₀ ℕ), c p.1 p.2 * d p.2) := by
    refine ((Equiv.prodComm _ _).hasSum_iff.2 hsum.hasSum).prod_fiberwise fun l => ?_
    exact (hcs l).mul_right (d l)
  exact hB'.tsum_eq.trans hA.tsum_eq.symm

end GlobalTheory.ConvSer
end

section

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology UpperHalfPlane

namespace GlobalTheory.MomOne

theorem model_norm_le_one_of_isIntegral {q : ℕ} [Fact q.Prime] {x : ℂ_[q]} (hx : IsIntegral ℤ x) :
    ‖x‖ ≤ 1 := by
  let S : Subring ℂ_[q] := (NormedField.valuation (K := ℂ_[q])).integer
  have hS := Valuation.integer.integers (NormedField.valuation (K := ℂ_[q]))
  have h1 : IsIntegral S x := hx.tower_top
  have h2 := hS.mem_of_integral h1
  have h3 : ‖x‖₊ ≤ 1 := h2
  exact_mod_cast h3

theorem model_isIntegral_j {d : ℕ} (hd : d ≠ 0) {L : PeriodPair} (hL : IsOK d L) :
    IsIntegral ℤ (GlobalTheory.latticeCurve L).j := by
  have hw : ((GlobalTheory.halfOneAddSqrtNeg d hd : ℍ) : ℂ) = wK d := by
    change (1 + √d * Complex.I) / 2 = _
    rw [wK]; ring
  rw [GlobalTheory.latticeCurve_j (a := 1) (τ := GlobalTheory.halfOneAddSqrtNeg d hd) one_ne_zero]
  · exact GlobalTheory.isIntegral_modularJ_halfOneAddSqrtNeg d hd
  · intro x
    rw [hL x, hw]
    constructor
    · rintro ⟨u, v, rfl⟩
      exact ⟨v, u, by ring⟩
    · rintro ⟨m, n, rfl⟩
      exact ⟨n, m, by ring⟩

theorem exists_model : ∀ (d q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (L : PeriodPair), d.Prime → d % 16 = 7 → IsOK d L → ∃ M : Mdl q, M.ι = ι ∧ M.L = L ∧ M.Ok ∧ IsAlgebraic ℚ M.W.a₁ ∧ IsAlgebraic ℚ M.W.a₂ ∧ IsAlgebraic ℚ M.W.a₃ ∧ IsAlgebraic ℚ M.W.a₄ ∧ IsAlgebraic ℚ M.W.a₆ := by
  intro d q _ ι L hd _ hL
  obtain ⟨E, h₁, h₂, h₃, h₄, h₆, hΔ, hc⟩ :=
    GlobalTheory.CMCurves.exists_integral_curve (model_isIntegral_j hd.ne_zero hL)
  have hE : E.IsElliptic := ⟨hΔ ▸ isUnit_one⟩
  have hj : (GlobalTheory.latticeCurve L).j = E.j := by
    rw [← hc, WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ', hΔ]
    simp
  obtain ⟨C, hC⟩ := WeierstrassCurve.exists_variableChange_of_j_eq _ _ hj
  have hu : (C.u : ℂ) ≠ 0 := C.u.ne_zero
  have e4 : E.c₄ / 12 = L.g₂ / (C.u : ℂ) ^ 4 := by
    rw [← hC, WeierstrassCurve.variableChange_c₄, GlobalTheory.latticeCurve_c₄, Units.val_inv_eq_inv_val]
    field_simp
  have e6 : E.c₆ / 216 = L.g₃ / (C.u : ℂ) ^ 6 := by
    have : (GlobalTheory.latticeCurve L).c₆ = 216 * L.g₃ := by
      simp only [GlobalTheory.latticeCurve, WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆]
      ring
    rw [← hC, WeierstrassCurve.variableChange_c₆, this, Units.val_inv_eq_inv_val]
    field_simp
  have hi : ∀ {x : ℂ}, IsIntegral ℤ x → IsIntegral ℤ ((ι : ℂ →+* ℂ_[q]) x) := fun hx ↦
    hx.map_of_comp_eq (RingHom.id ℤ) (ι : ℂ →+* ℂ_[q]) (RingHom.ext_int _ _)
  have ha : ∀ {x : ℂ}, IsIntegral ℤ x → IsAlgebraic ℚ ((ι : ℂ →+* ℂ_[q]) x) := fun hx ↦
    (IsIntegral.tower_top (A := ℚ) (hi hx)).isAlgebraic
  refine ⟨⟨ι, L, C.u, E.map (ι : ℂ →+* ℂ_[q])⟩, rfl, rfl,
    ⟨hu, model_norm_le_one_of_isIntegral (hi h₁), model_norm_le_one_of_isIntegral (hi h₂),
      model_norm_le_one_of_isIntegral (hi h₃), model_norm_le_one_of_isIntegral (hi h₄),
      model_norm_le_one_of_isIntegral (hi h₆), ?_, ?_, ?_⟩, ha h₁, ha h₂, ha h₃, ha h₄, ha h₆⟩
  · simp [WeierstrassCurve.map_Δ, hΔ]
  · change (E.map (ι : ℂ →+* ℂ_[q])).c₄ / 12 = ι (L.g₂ / (C.u : ℂ) ^ 4)
    rw [← e4, WeierstrassCurve.map_c₄, map_div₀, map_ofNat]
    rfl
  · change (E.map (ι : ℂ →+* ℂ_[q])).c₆ / 216 = ι (L.g₃ / (C.u : ℂ) ^ 6)
    rw [← e6, WeierstrassCurve.map_c₆, map_div₀, map_ofNat]
    rfl

end GlobalTheory.MomOne
end

section

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

theorem _root_.GlobalTheory.T.cpTransportedTaylorSeries_multiplicativeChart : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) (G : ℂ → ℂ), AnalyticAt ℂ G 0 → (DT (hat ι (C ω * logS) G) = C ω * hat ι (C ω * logS) (deriv G)) ∧ (∀ k : ℕ, constantCoeff (DT^[k] (hat ι (C ω * logS) G)) = ω ^ k * ι (iteratedDeriv k G 0)) ∧ (∀ (α : ℂ) (a : ℤ_[q]), ι α = zc a → hat ι (C ω * logS) (fun z => G (α * z)) = (hat ι (C ω * logS) G).subst (mulS a : ℂ_[q]⟦X⟧)) ∧ ∀ a : ℤ_[q], hat ι (C (ω * zc a) * logS) G = (hat ι (C ω * logS) G).subst (mulS a : ℂ_[q]⟦X⟧) := by
  first | exact @GlobalTheory.MomOne.hat_multiplicative_chart | exact GlobalTheory.MomOne.hat_multiplicative_chart | (intros; apply GlobalTheory.MomOne.hat_multiplicative_chart <;> assumption)
end

section

open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory.LowCasShift

theorem card_le {n : ℕ} (p : Fin n → Prop) [DecidablePred p] :
    (0 : ℝ) ≤ ((univ.filter p).card : ℝ) ∧ ((univ.filter p).card : ℝ) ≤ n := by
  refine ⟨Nat.cast_nonneg _, ?_⟩
  have h : (univ.filter p).card ≤ n := by
    simpa using card_filter_le (univ : Finset (Fin n)) p
  exact_mod_cast h

theorem rhoC_bd {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    -((n : ℝ) / 2) ≤ rhoC ε a ∧ rhoC ε a ≤ (n : ℝ) / 2 := by
  have h1 := card_le (fun b : Fin n => a < b ∧ ε b = ε a)
  have h2 := card_le (fun b : Fin n => b < a ∧ ε b = ε a)
  unfold rhoC
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem rhoN_bd {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    -((n : ℝ) / 2) ≤ rhoN ε a ∧ rhoN ε a ≤ (n : ℝ) / 2 := by
  have h1 := card_le (fun b : Fin n => a < b ∧ ε b ≠ ε a)
  have h2 := card_le (fun b : Fin n => b < a ∧ ε b ≠ ε a)
  unfold rhoN
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem nsq_sub_single {n : ℕ} (u : Fin n → ℝ) (s : Fin n) :
    nsq (u - Pi.single s 1) = nsq u - 2 * u s + 1 := by
  have h : ∀ a, (u - Pi.single s 1 : Fin n → ℝ) a * (u - Pi.single s 1 : Fin n → ℝ) a
      = u a * u a + (if a = s then 1 - 2 * u s else 0) := by
    intro a
    by_cases ha : a = s
    · subst ha; simp; ring
    · simp [ha]
  unfold nsq dot
  simp only [h, sum_add_distrib, sum_ite_eq', mem_univ, if_true]
  ring

theorem nsq_rhoC_le {n : ℕ} (ε : Fin n → Bool) : nsq (rhoC ε) ≤ (n : ℝ) ^ 3 := by
  unfold nsq dot
  have h : ∀ a ∈ (univ : Finset (Fin n)), rhoC ε a * rhoC ε a ≤ (n : ℝ) ^ 2 := by
    intro a _
    have := rhoC_bd ε a
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith [this.1, this.2]
  have := sum_le_card_nsmul _ _ _ h
  simp only [card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  calc _ ≤ (n : ℝ) * (n : ℝ) ^ 2 := this
    _ = _ := by ring

theorem sq_le_nsq {n : ℕ} (u : Fin n → ℝ) (a : Fin n) : u a * u a ≤ nsq u := by
  unfold nsq dot
  exact single_le_sum (f := fun a => u a * u a) (fun i _ => mul_self_nonneg _) (mem_univ a)

theorem sqrt_step {X Y b : ℝ} (hb : 4 ≤ b) (hX : (b / 2) ^ 2 ≤ X) (hY : X - b ≤ Y) :
    Real.sqrt X ≤ Real.sqrt Y + 2 := by
  have h1 : b / 2 ≤ Real.sqrt X := Real.le_sqrt_of_sq_le hX
  have h0 : 0 ≤ X := le_trans (sq_nonneg _) hX
  have h2 : Real.sqrt X ^ 2 = X := Real.sq_sqrt h0
  have h3 : Real.sqrt X - 2 ≤ Real.sqrt Y := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  linarith

end GlobalTheory.LowCasShift

namespace GlobalTheory


open LowCasShift in
theorem lowK_sub_single_and_sqrt_ckv_le :
    ∀ (n kk : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (bv : ℝ) (s : Fin n), Shape ε kk μ bv →
      lowK ε (μ - Pi.single s 1) = lowK ε μ - Pi.single s 1 ∧
      Real.sqrt (ckv ε (lowK ε μ)) + Real.sqrt n ≤
        Real.sqrt (ckv ε (lowK ε (μ - Pi.single s 1))) + 8 * n := by
  intro n kk ε μ bv s h
  obtain ⟨hk1, hk2, -, hc, hnode, hb⟩ := h
  refine ⟨by unfold lowK; abel, ?_⟩
  have hn2 : 2 ≤ n := by omega
  have hn : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have h37 : (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 7 := pow_le_pow_right₀ hn1 (by norm_num)
  have h13 : (n : ℝ) ≤ (n : ℝ) ^ 3 := by
    simpa using pow_le_pow_right₀ hn1 (show 1 ≤ 3 by norm_num)
  have hX : ckv ε (lowK ε μ) = nsq (μ + rhoN ε) - nsq (rhoC ε) := by
    unfold ckv lowK; congr 2; abel
  have hY : ckv ε (lowK ε (μ - Pi.single s 1))
      = nsq (μ + rhoN ε) - 2 * (μ s + rhoN ε s) + 1 - nsq (rhoC ε) := by
    have : lowK ε (μ - Pi.single s 1) + rhoC ε = (μ + rhoN ε) - Pi.single s 1 := by
      unfold lowK; abel
    unfold ckv
    rw [this, nsq_sub_single]; rfl
  have hs : μ s ≤ bv / 8 + bv / 100 := by
    by_cases hsk : s.val + 1 < kk
    · exact (hc s hsk).2.2
    · have := (hnode s (by omega)).2
      linarith
  have hNs := (rhoN_bd ε s).2
  let l : Fin n := ⟨n - 1, by omega⟩
  have hl := (hnode l (by show kk ≤ n - 1 + 1; omega)).2
  have hNl := (rhoN_bd ε l).2
  have hsq := sq_le_nsq (μ + rhoN ε) l
  have hC := nsq_rhoC_le ε
  have hneg : (μ + rhoN ε) l ≤ -(9 / 10 * bv) := by
    show μ l + rhoN ε l ≤ _
    linarith
  have hb4 : 4 ≤ bv := by linarith
  have hbig : (9 / 10 * bv) ^ 2 ≤ (μ + rhoN ε) l * (μ + rhoN ε) l := by nlinarith
  have hXl : (bv / 2) ^ 2 ≤ ckv ε (lowK ε μ) := by
    rw [hX]; nlinarith
  have hstep := sqrt_step hb4 hXl (Y := ckv ε (lowK ε (μ - Pi.single s 1))) (by rw [hX, hY]; linarith)
  have hsn : Real.sqrt n ≤ n := by
    apply Real.sqrt_le_iff.mpr
    constructor <;> nlinarith
  linarith

end GlobalTheory
end

section

open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem card_filter_fin_bounds {n : ℕ} (p : Fin n → Prop) [DecidablePred p] :
    (0 : ℝ) ≤ ((univ.filter p).card : ℝ) ∧ ((univ.filter p).card : ℝ) ≤ n := by
  refine ⟨Nat.cast_nonneg _, ?_⟩
  have h : (univ.filter p).card ≤ n :=
    le_trans (Finset.card_filter_le _ _) (by simp)
  exact_mod_cast h

theorem abs_lowK_sub_le {n : ℕ} (ε : Fin n → Bool) (μ : Fin n → ℝ) (a : Fin n) :
    -(n : ℝ) ≤ lowK ε μ a - μ a ∧ lowK ε μ a - μ a ≤ n := by
  have e : lowK ε μ a - μ a = rhoN ε a - rhoC ε a := by
    simp only [lowK, Pi.add_apply, Pi.sub_apply]
    ring
  rw [e]
  simp only [rhoN, rhoC]
  obtain ⟨h1, h2⟩ := card_filter_fin_bounds (fun b : Fin n => a < b ∧ ε b ≠ ε a)
  obtain ⟨h3, h4⟩ := card_filter_fin_bounds (fun b : Fin n => b < a ∧ ε b ≠ ε a)
  obtain ⟨h5, h6⟩ := card_filter_fin_bounds (fun b : Fin n => a < b ∧ ε b = ε a)
  obtain ⟨h7, h8⟩ := card_filter_fin_bounds (fun b : Fin n => b < a ∧ ε b = ε a)
  constructor <;> linarith

private lemma four_sq_add_le_of_large_bv {n : ℕ} {bv : ℝ} (hn : 2 ≤ n) (hb : 10 ^ 6 * (n : ℝ) ^ 7 ≤ bv) :
    4 * (n : ℝ) ^ 2 + 2 + n ≤ bv / 32 - bv / 100 := by
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h7 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 7 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hsq : 4 * (n : ℝ) ^ 2 + 2 + n ≤ 6 * (n : ℝ) ^ 2 := by nlinarith
  linarith

theorem shape_position : ∀ (n kk j : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (bv : ℝ), Shape ε kk μ bv → j ≤ 4 * n ^ 2 + 2 → 0 < bv ∧ (∀ ω : Fin n → ℝ, ∑ a, |ω a - lowK ε μ a| ≤ j → ∀ a : Fin n, (a.val + 1 < kk → -bv / 8 - bv / 32 ≤ -ω a ∧ -ω a ≤ bv / 32) ∧ (kk ≤ a.val + 1 → bv - bv / 32 ≤ -ω a ∧ -ω a ≤ 2 * bv + bv / 32)) ∧ ∀ a : Fin n, (a.val + 1 < kk → -bv / 8 - bv / 32 ≤ -μ a + (1 - (n : ℝ)) / 2 ∧ -μ a + (1 - (n : ℝ)) / 2 ≤ bv / 32) ∧ (kk ≤ a.val + 1 → bv - bv / 32 ≤ -μ a + (1 - (n : ℝ)) / 2 ∧ -μ a + (1 - (n : ℝ)) / 2 ≤ 2 * bv + bv / 32) := by
  intro n kk j ε μ bv hS hj
  obtain ⟨hk1, hkn, -, hcl, hnd, hb⟩ := hS
  have hn : 2 ≤ n := by omega
  have hm := four_sq_add_le_of_large_bv hn hb
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hbpos : 0 < bv := by
    have : (0 : ℝ) < (n : ℝ) ^ 7 := by positivity
    linarith
  have hjr : (j : ℝ) ≤ 4 * (n : ℝ) ^ 2 + 2 := by exact_mod_cast hj
  refine ⟨hbpos, ?_, ?_⟩
  · intro ω hω a
    have hle : |ω a - lowK ε μ a| ≤ j :=
      le_trans (Finset.single_le_sum (f := fun b => |ω b - lowK ε μ b|)
        (fun b _ => abs_nonneg _) (Finset.mem_univ a)) hω
    obtain ⟨hl1, hl2⟩ := abs_lowK_sub_le ε μ a
    obtain ⟨ha1, ha2⟩ := abs_le.mp hle
    constructor
    · intro ha
      obtain ⟨-, h1, h2⟩ := hcl a ha
      constructor <;> linarith
    · intro ha
      obtain ⟨h1, h2⟩ := hnd a ha
      constructor <;> linarith
  · intro a
    constructor
    · intro ha
      obtain ⟨-, h1, h2⟩ := hcl a ha
      constructor <;> linarith
    · intro ha
      obtain ⟨h1, h2⟩ := hnd a ha
      constructor <;> linarith

end GlobalTheory
end

section

open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

private lemma dualTens_casimir_sum {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ M) (x : Fin n → M) :
    ∑ a, ∑ b, dualTens E a b (dualTens E b a x)
      = (fun i => Cas E (x i)) + (n : ℂ) • x + (2 : ℂ) • splitCas E x := by
  funext i
  have h1 : ∀ a b, dualTens E a b (dualTens E b a x) i
      = E a b (E b a (x i)) - (if i = a then E a b (x b) else 0)
        - (if i = b then E b a (x a) else 0) + (if i = b then x b else 0) := by
    intro a b
    simp only [dualTens, map_sub, if_true]
    split_ifs <;> (try simp only [map_zero]) <;> abel
  simp only [Finset.sum_apply, h1, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Pi.add_apply, Pi.smul_apply, splitCas, Cas,
    LinearMap.sum_apply, Module.End.mul_apply]
  rw [Finset.sum_comm (f := fun a b => if i = a then E a b (x b) else 0)]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, Nat.cast_smul_eq_nsmul, two_smul]
  abel

private lemma casG_sub_single {n : ℕ} (μ : Fin n → ℝ) (s : Fin n) :
    casG (μ - Pi.single s 1) = casG μ - 2 * μ s + 1 := by
  unfold casG
  have : ∀ a, (μ - Pi.single s 1 : Fin n → ℝ) a ^ 2 = μ a ^ 2 + (if s = a then (-2 * μ s + 1) else 0) := by
    intro a
    by_cases h : s = a
    · subst h; simp; ring
    · simp [h, Ne.symm h]
  simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

theorem splitCas_eigenvalue_summand : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)] [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s)) (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (μ : Fin n → ℝ), IsMod ε E μ → (∀ s, IsMod ε (F s) (μ - Pi.single s 1)) → AlgTens ε E N F io pr → ∀ s (y : N s), splitCas E (io s y) = ((-μ s + (1 - (n : ℝ)) / 2 : ℝ) : ℂ) • io s y := by
  intro M _ _ n ε E N _ _ F io pr μ hE hF hT s y
  have h1 : io s (Cas (F s) y) = ∑ a, ∑ b, dualTens E a b (dualTens E b a (io s y)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Cas, LinearMap.sum_apply, Module.End.mul_apply, map_sum, hT.io_comm]
  rw [dualTens_casimir_sum, (hF s).2.2, map_smul, casG_sub_single] at h1
  have h2 : (fun i => Cas E (io s y i)) = (casG μ : ℂ) • io s y := by
    funext i; rw [hE.2.2]; rfl
  rw [h2] at h1
  have h3 : splitCas E (io s y) = (1 / 2 : ℂ) • (((casG μ - 2 * μ s + 1 : ℝ) : ℂ) • io s y
      - (casG μ : ℂ) • io s y - (n : ℂ) • io s y) := by
    rw [h1]; module
  rw [h3]; push_cast; module

end GlobalTheory
end
