module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DividedWeightUnique
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle409
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle463
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle613
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle505
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle648
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle608
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle507
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle800
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle728
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle919
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle506
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle798
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle799
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle765
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle687
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle247
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle920
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle651
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Order.CompletePartialOrder
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.L2.Indef.Tree NumberField GlobalTheory.MeanTop

namespace GlobalTheory.MeanTop

theorem le_two_mul_ediv {x m T h : ℤ} (hm : 0 < m) (hT : 4 * m ≤ 5 * T) (hh : 0 ≤ h)
    (hx : 3 * h ≤ 4 * (x - m)) : h ≤ 2 * T * (x / m) := by
  have h1 : m * (x / m) + x % m = x := Int.mul_ediv_add_emod x m
  have h2 : x % m < m := Int.emod_lt_of_pos x hm
  have h3 : 0 ≤ x / m := Int.ediv_nonneg (by omega) hm.le
  have h4 : 4 * m * (x / m) ≤ 5 * T * (x / m) := mul_le_mul_of_nonneg_right hT h3
  have h5 : 0 ≤ T * (x / m) := mul_nonneg (by omega) h3
  nlinarith

theorem divided_gaps : ∀ (ι : Type) [Fintype ι] (N : ℕ) (W : Wts ι N), W.Hyp → W.IsDiv → ∀ τ (a b : Fin N), (b : ℕ) = a + 1 → (((b : ℕ) ≠ W.p → (W.T : ℤ) + W.Dd + 2 + 2 * N ≤ W.u1 τ a - W.u1 τ b) ∧ ((b : ℕ) = W.p → W.h0 ≤ 2 * W.T * (W.u1 τ a - W.u1 τ b) ∧ W.h0 ≤ 4 * W.T * (W.u1 τ a - W.u1 τ b - 3 * N)) ∧ ((b : ℕ) ≠ W.p → W.kc ≤ (a : ℕ) → W.h0 ≤ 4 * W.T * (W.u1 τ a - W.u1 τ b))) := by
  intro ι _ N W H hD τ a b hab
  have hq := (hD τ).2 a b hab
  obtain ⟨g1, g2, g3⟩ := H.h4 τ a b hab
  obtain ⟨k1, k2⟩ := H.h2
  have c0 := H.weightConst_nonneg
  have h1 : 4 * (W.Dd : ℤ) + 4 ≤ W.T := by exact_mod_cast H.h1
  have hm : (0 : ℤ) < (W.T : ℤ) + W.Dd + 1 := by positivity
  have hT : 4 * ((W.T : ℤ) + W.Dd + 1) ≤ 5 * (W.T : ℤ) := by omega
  have hh : 0 ≤ W.h0 := by omega
  refine ⟨fun hb => ?_, fun hb => ?_, fun hb ha => ?_⟩
  · rw [hq, if_neg hb]
    refine Int.le_ediv_of_mul_le hm ?_
    have := g1 hb
    have h0 : (0 : ℤ) ≤ (W.T : ℤ) + W.Dd + 2 + 2 * N := by positivity
    nlinarith
  · have := g3 hb
    have key : W.h0 ≤ 2 * W.T * (W.u1 τ a - W.u1 τ b) := by
      rw [hq, if_pos hb]
      exact le_two_mul_ediv hm hT hh (by omega)
    exact ⟨key, by nlinarith⟩
  · have := g2 ha
    have key : W.h0 ≤ 2 * W.T * (W.u1 τ a - W.u1 τ b) := by
      rw [hq, if_neg hb]
      exact le_two_mul_ediv hm hT hh (by omega)
    nlinarith

end GlobalTheory.MeanTop
end

section

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.L2.Indef.Tree NumberField GlobalTheory.MeanTop

namespace GlobalTheory.MeanTop

theorem sum_padicValNat_mul_log_le_log (n : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∑ p ∈ S, (padicValNat p n : ℝ) * Real.log p ≤ Real.log n := by
  classical
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum]
  have h1 : ∑ p ∈ S, (padicValNat p n : ℝ) * Real.log p
      = ∑ p ∈ S, (n.factorization p : ℝ) * Real.log p :=
    Finset.sum_congr rfl fun p hp => by rw [Nat.factorization_def n (hS p hp), Nat.padicValNat_def]
  rw [h1]
  have h2 : ∑ p ∈ S ∪ n.factorization.support, (n.factorization p : ℝ) * Real.log p
      = ∑ p ∈ n.factorization.support, (n.factorization p : ℝ) * Real.log p := by
    symm
    refine Finset.sum_subset Finset.subset_union_right fun p _ hp => ?_
    rw [Finsupp.notMem_support_iff.1 hp]; simp
  rw [← h2]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
    fun p _ _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p)

theorem sum_vDiff_mul_log_le :
    ∀ (D : D7) (S : Finset ℕ), (∀ p ∈ S, p.Prime) → (∀ p, 0 ≤ vDiff D p) ∧ ∑ p ∈ S, vDiff D p * Real.log p ≤ Real.log D.host.rdE := by
  intro D S hS
  refine ⟨fun p => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), ?_⟩
  have hn : (0 : ℝ) < (Module.finrank ℚ D.host.E : ℝ) := by exact_mod_cast Module.finrank_pos
  have hd : (0 : ℝ) < |(discr D.host.E : ℝ)| := by
    rw [abs_pos]; exact_mod_cast discr_ne_zero D.host.E
  have hc : ((WeightThresholdDefs.dE D : ℕ) : ℝ) = |(discr D.host.E : ℝ)| := by
    rw [WeightThresholdDefs.dE, Nat.cast_natAbs, Int.cast_abs]
  have hr : Real.log D.host.rdE = Real.log (WeightThresholdDefs.dE D : ℕ) / (Module.finrank ℚ D.host.E : ℝ) := by
    rw [hc]
    unfold Host.rdE
    rw [Real.log_rpow hd]; ring
  rw [hr]
  refine le_trans (le_of_eq ?_) (div_le_div_of_nonneg_right (sum_padicValNat_mul_log_le_log (WeightThresholdDefs.dE D) S hS) hn.le)
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [vDiff]; ring

end GlobalTheory.MeanTop
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.EtC

theorem SemiMap.sub_op {S R : Type} [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ ρ' : SemiMap I J)
    (E : Spc) (n : ℤ) (x : CohomologyClass ((chains S).obj E) I n) :
    (ρ.sub ρ').op.app E n x = ρ.op.app E n x - ρ'.op.app E n x := by
  obtain ⟨α, rfl⟩ := x.mk_surjective
  obtain ⟨β, hβ⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R ρ).1 E n α
  obtain ⟨β', hβ'⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R ρ').1 E n α
  have hsub : (ρ.sub ρ').IsImage α.1 (β - β').1 := by
    intro p s h U x
    rw [show (β - β').1 = β.1 - β'.1 from rfl, ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).1 β.1 β'.1 p s h U x).2.1, hβ p s h U x,
      hβ' p s h U x]
    rfl
  rw [(GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R _).2 E n α _ hsub, (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R ρ).2 E n α β hβ,
    (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R ρ').2 E n α β' hβ', CohomologyClass.mk_sub]

theorem a8 : A8 := by
  intro R S _ _ φ E F n
  obtain ⟨ρ₀, h₀, hb⟩ := GlobalTheory.T.restrictScalars_resolution_comparison R S φ F
  have hz := GlobalTheory.T.semilinearResolutionMap_cohomology_eq_zero_of_kill S R F ((restr φ).obj F) ((restrMap φ F).sub ρ₀) (fun U a => by
    change (restrMap φ F).app U 0 _ - ρ₀.app U 0 _ = 0
    rw [GlobalTheory.T.restrictScalarsResolutionMap_augmentation_spec R S φ F U a, h₀ U a, sub_self])
  have he : restrH φ E F n = ρ₀.op.app E n := by
    ext x
    have := hz E n x
    rw [SemiMap.sub_op] at this
    exact sub_eq_zero.mp this
  rw [he]
  exact hb E n

end GlobalTheory.EtC
end
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.isMapOf_natMultiple_formalGroupLaw : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Katz.Chart G d) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), c.IsLawOf μ → ∀ j : ℕ, c.IsMapOf c ((j : ℤ_[p]) • 𝟙 G) (nmul μ j) := by
  first | exact @GlobalTheory.Katz.Chart.isMapOf_nmul | exact GlobalTheory.Katz.Chart.isMapOf_nmul | (intros; apply GlobalTheory.Katz.Chart.isMapOf_nmul <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.exists_formalGroupLaw_log_with_linearPart : ∀ (p : ℕ) [Fact p.Prime] (O C : Type) [CommRing O] [CommRing C] [Algebra O C], IsFrame p C (RingHom.id O) → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → ∀ w : Fin d → O, ∃ f : MvPowerSeries (Fin d) C, constantCoeff f = 0 ∧ (∀ i, lin f i = algebraMap O C (w i)) ∧ cob1 (up C μ) f = 0 := by
  first | exact @GlobalTheory.QLog.exists_log_of_lin | exact GlobalTheory.QLog.exists_log_of_lin | (intros; apply GlobalTheory.QLog.exists_log_of_lin <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.symmetricCocycle_modIdeal_eq_coboundary_quasiLog : ∀ (p : ℕ) [Fact p.Prime] (O C : Type) [CommRing O] [CommRing C] [Algebra O C], IsFrame p C (RingHom.id O) → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → ∀ (a : O), a ∣ p → ∀ c : MvPowerSeries (Fin d ⊕ Fin d) O, constantCoeff c = 0 → (∀ α, a ∣ coeff α (cob2 μ c)) → (∀ α, a ∣ coeff α (swap c - c)) → ∃ g : MvPowerSeries (Fin d) C, QL μ ⊤ g ∧ lin g = 0 ∧ In (Ideal.span {a}) (cob1 (up C μ) g - map (algebraMap O C) c) := by
  first | exact @GlobalTheory.CocLift.cocycle_lift | exact GlobalTheory.CocLift.cocycle_lift | (intros; apply GlobalTheory.CocLift.cocycle_lift <;> assumption)
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

namespace GlobalTheory.Katz

theorem coeff_powerSeriesEvalTwoGroups_eq_zero_of_degree_lt {R τ : Type} [CommRing R] {d : ℕ}
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) (u v : Fin d → MvPowerSeries τ R)
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) (M : ℕ)
    (hc : ∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree < M → coeff α c = 0) :
    ∀ γ : τ →₀ ℕ, γ.degree < M → coeff γ (at2 c u v) = 0 := by
  intro γ hγ
  have ha : ∀ s, constantCoeff (Sum.elim u v s) = 0 := by
    rintro (i | i)
    · exact hu i
    · exact hv i
  have hs : HasSubst (Sum.elim u v) := hasSubst_of_constantCoeff_zero ha
  have h1 : (1 : ℕ∞) ≤ ⨅ s, (Sum.elim u v s).order := le_iInf fun s => by
    apply MvPowerSeries.le_order
    intro δ hδ
    have h0 : δ.degree = 0 := by exact_mod_cast ENat.lt_one_iff_eq_zero.mp hδ
    rw [Finsupp.degree_eq_zero_iff] at h0
    subst h0
    rw [coeff_zero_eq_constantCoeff_apply]
    exact ha s
  have h2 : (M : ℕ∞) ≤ c.order := MvPowerSeries.le_order fun δ hδ => hc δ (by exact_mod_cast hδ)
  have h3 := le_order_subst hs c
  unfold at2
  apply coeff_of_lt_order
  calc (γ.degree : ℕ∞) < M := by exact_mod_cast hγ
    _ ≤ 1 * c.order := by rw [one_mul]; exact h2
    _ ≤ (⨅ s, (Sum.elim u v s).order) * c.order := mul_le_mul_left h1 _
    _ ≤ _ := h3

theorem coeff_formalGroupLawCoboundaryTwo_eq_zero_of_degree_lt {R : Type} [CommRing R] {d : ℕ}
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) (M : ℕ)
    (hc : ∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree < M → coeff α c = 0) :
    ∀ γ : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ, γ.degree < M → coeff γ (cob2 μ c) = 0 := by
  intro γ hγ
  have hx1 : ∀ i, constantCoeff ((x1 : Fin d → MvPowerSeries _ R) i) = 0 :=
    fun i => constantCoeff_X _
  have hx2 : ∀ i, constantCoeff ((x2 : Fin d → MvPowerSeries _ R) i) = 0 :=
    fun i => constantCoeff_X _
  have hx3 : ∀ i, constantCoeff ((x3 : Fin d → MvPowerSeries _ R) i) = 0 :=
    fun i => constantCoeff_X _
  have hop : ∀ (u v : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R),
      (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) →
      ∀ i, constantCoeff (op μ u v i) = 0 := by
    intro u v hu hv i
    rw [← coeff_zero_eq_constantCoeff_apply]
    refine coeff_powerSeriesEvalTwoGroups_eq_zero_of_degree_lt (μ i) u v hu hv 1 (fun α hα => ?_) 0 (by simp)
    have h0 : α.degree = 0 := by omega
    rw [Finsupp.degree_eq_zero_iff] at h0
    subst h0
    rw [coeff_zero_eq_constantCoeff_apply]
    exact hμ i
  unfold cob2
  simp only [map_add (f := _), map_sub]
  rw [coeff_powerSeriesEvalTwoGroups_eq_zero_of_degree_lt c _ _ hx2 hx3 M hc γ hγ,
    coeff_powerSeriesEvalTwoGroups_eq_zero_of_degree_lt c _ _ (hop _ _ hx1 hx2) hx3 M hc γ hγ,
    coeff_powerSeriesEvalTwoGroups_eq_zero_of_degree_lt c _ _ hx1 (hop _ _ hx2 hx3) M hc γ hγ,
    coeff_powerSeriesEvalTwoGroups_eq_zero_of_degree_lt c _ _ hx1 hx2 M hc γ hγ]
  simp

theorem degree_mapDomain_swap_ord {d : ℕ} (γ : Fin d ⊕ Fin d →₀ ℕ) :
    (γ.mapDomain Sum.swap).degree = γ.degree := by
  induction γ using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => rw [Finsupp.mapDomain_add, map_add (f := _), map_add (f := _), ha, hb]
  | single a n => rw [Finsupp.mapDomain_single, Finsupp.degree_single, Finsupp.degree_single]

end GlobalTheory.Katz

theorem GlobalTheory.Katz.quasiLog_approx_step : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), IsLaw μ → ∀ c, IsCoc μ c → ∀ (N : ℕ) (f : MvPowerSeries (Fin d) (Fr p k)), 2 ≤ N → f ∈ quasiInt p k (Fin d) → (∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree < N → ∃ w : WittVector p k, coeff γ (cob1 (fun i => Katz.lift p (μ i)) f - Katz.lift p c) = algebraMap (WittVector p k) (Fr p k) (p * w)) → ∃ h : MvPowerSeries (Fin d) (Fr p k), (∀ α : Fin d →₀ ℕ, α.degree ≠ N → coeff α h = 0) ∧ f - h ∈ quasiInt p k (Fin d) ∧ ∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree < N + 1 → ∃ w : WittVector p k, coeff γ (cob1 (fun i => Katz.lift p (μ i)) (f - h) - Katz.lift p c) = algebraMap (WittVector p k) (Fr p k) (p * w) := by
  intro p _ k _ _ _ d μ hμ c hc N f hN hf hlow
  have hL0 : ∀ i, constantCoeff ((fun i => Katz.lift p (μ i)) i) = 0 :=
    fun i => constantCoeff_lift p (hμ.const i)
  have CC := GlobalTheory.T.formalGroupLawCoboundaryTwo_coboundaryOne (Fr p k) d (fun i => Katz.lift p (μ i)) hL0 0
  have Q := GlobalTheory.T.coboundaryOne_teichmullerLift_isCocycle_mod_p p k d μ hμ f hf
  have RD := GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k (Fin d ⊕ Fin d)
  have RD3 := GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k (Fin d ⊕ (Fin d ⊕ Fin d))
  have RC := GlobalTheory.T.reduction_commutes_formalGroupLawCoboundaries p k d μ hμ.const
  have LIN := GlobalTheory.T.formal_group_law_linear_coeff_additive p k d μ hμ
  have LEAD := GlobalTheory.T.coboundary_eq_additive_leading_terms (Fr p k) d (fun i => Katz.lift p (μ i)) N (fun i α hα => (LIN i α hα).2)
  have HOM := GlobalTheory.T.additive_formal_group_coboundary_homogeneous (Fr p k) d N
  obtain ⟨g, hg⟩ : ∃ g, g = cob1 (fun i => Katz.lift p (μ i)) f - Katz.lift p c := ⟨_, rfl⟩
  rw [← hg] at hlow

  have hg2 : cob2 (fun i => Katz.lift p (μ i)) g ∈ intBy p k _ (p : WittVector p k) := by
    have h1 : Red p (cob2 (fun i => Katz.lift p (μ i)) (Katz.lift p c)) 0 := by
      have := (RC.1 (Katz.lift p c) c (RD.2.2.1 c)).1
      rwa [hc.1] at this
    rw [hg, (CC.2.2.1 _ _).2.1]
    exact sub_mem Q.1 ((RD3.2.2.2.2.2.1 _).2 h1)
  have hgs : swap g - g ∈ intBy p k _ (p : WittVector p k) := by
    have h1 : Red p (swap (Katz.lift p c) - Katz.lift p c) 0 := by
      have a := (RC.1 (Katz.lift p c) c (RD.2.2.1 c)).2
      rw [hc.2] at a
      have := (RD.2.2.2.1 _ _ _ _ a (RD.2.2.1 c)).2
      rwa [sub_self] at this
    have : swap g - g = (swap (cob1 (fun i => Katz.lift p (μ i)) f) -
        cob1 (fun i => Katz.lift p (μ i)) f) - (swap (Katz.lift p c) - Katz.lift p c) := by
      rw [hg, (CC.2.2.1 _ _).2.2]; abel
    rw [this]
    exact sub_mem Q.2 ((RD.2.2.2.2.2.1 _).2 h1)

  obtain ⟨e, he⟩ : ∃ e : MvPowerSeries (Fin d ⊕ Fin d) (Fr p k),
      ∀ γ, coeff γ e = if γ.degree = N then coeff γ g else 0 :=
    ⟨fun γ => if γ.degree = N then coeff γ g else 0, fun γ => rfl⟩
  obtain ⟨low, hlo⟩ : ∃ low : MvPowerSeries (Fin d ⊕ Fin d) (Fr p k),
      ∀ γ, coeff γ low = if γ.degree < N then coeff γ g else 0 :=
    ⟨fun γ => if γ.degree < N then coeff γ g else 0, fun γ => rfl⟩
  have hhigh : ∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree < N + 1 → coeff γ (g - low - e) = 0 := by
    intro γ hγ
    rw [map_sub, map_sub, he, hlo]
    by_cases h1 : γ.degree < N
    · rw [if_pos h1, if_neg (by omega)]; ring
    · rw [if_neg h1, if_pos (by omega)]; ring
  have hlowI : low ∈ intBy p k _ (p : WittVector p k) := by
    intro γ
    rw [hlo]
    by_cases h1 : γ.degree < N
    · rw [if_pos h1]; exact hlow γ h1
    · rw [if_neg h1]; exact ⟨0, by simp⟩
  have ehom : ∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree ≠ N → coeff γ e = 0 := by
    intro γ hγ; rw [he, if_neg hγ]
  have eord : ∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree < N → coeff γ e = 0 :=
    fun γ hγ => ehom γ (by omega)
  have hcob2e : cob2 (addLaw (Fr p k) d) e ∈ intBy p k _ (p : WittVector p k) := by
    intro γ
    by_cases hγ : γ.degree = N
    · rw [← LEAD.2 e eord γ hγ.le]
      have hsplit : e = g - low - (g - low - e) := by abel
      have hz := coeff_formalGroupLawCoboundaryTwo_eq_zero_of_degree_lt (fun i => Katz.lift p (μ i)) hL0
        (g - low - e) (N + 1) hhigh γ (by omega)
      obtain ⟨w1, hw1⟩ := hg2 γ
      obtain ⟨w2, hw2⟩ := (RC.2.2.2 _ low hlowI).1 γ
      refine ⟨w1 - w2, ?_⟩
      rw [hsplit, (CC.2.2.1 _ _).2.1, (CC.2.2.1 _ _).2.1, map_sub, map_sub, hz, hw1, hw2,
        mul_sub, map_sub, sub_zero]
    · rw [HOM.2.1 e ehom γ hγ]; exact ⟨0, by simp⟩
  have hswape : swap e - e ∈ intBy p k _ (p : WittVector p k) := by
    intro γ
    rw [map_sub, HOM.2.2.1, he, he, degree_mapDomain_swap_ord]
    by_cases hγ : γ.degree = N
    · rw [if_pos hγ, if_pos hγ]
      obtain ⟨w, hw⟩ := hgs γ
      rw [map_sub, HOM.2.2.1] at hw
      exact ⟨w, hw⟩
    · rw [if_neg hγ, if_neg hγ]; exact ⟨0, by simp⟩
  obtain ⟨h, hhom, hint⟩ := GlobalTheory.T.lazard_additive_law_wittVectorFractionField_mod_p p k d N e hN ehom hcob2e hswape
  have hord : ∀ α : Fin d →₀ ℕ, α.degree < N → coeff α h = 0 := fun α hα => hhom α (by omega)
  have hsub : cob1 (fun i => Katz.lift p (μ i)) (f - h) =
      cob1 (fun i => Katz.lift p (μ i)) f - cob1 (fun i => Katz.lift p (μ i)) h := by
    rw [eq_sub_iff_add_eq, ← formalCoboundary_add hL0, sub_add_cancel]
  have K : ∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree < N + 1 → ∃ w : WittVector p k,
      coeff γ (cob1 (fun i => Katz.lift p (μ i)) (f - h) - Katz.lift p c) =
        algebraMap (WittVector p k) (Fr p k) (p * w) := by
    intro γ hγ
    have e1 : cob1 (fun i => Katz.lift p (μ i)) (f - h) - Katz.lift p c =
        g - cob1 (fun i => Katz.lift p (μ i)) h := by rw [hsub, hg]; abel
    rw [e1, map_sub]
    obtain ⟨hL1, hL2⟩ := LEAD.1 h hord γ
    by_cases h1 : γ.degree < N
    · rw [hL1 h1, sub_zero]; exact hlow γ h1
    · have hN' : γ.degree = N := by omega
      rw [hL2 hN'.le]
      have : coeff γ g = coeff γ e := by rw [he, if_pos hN']
      rw [this, ← map_sub]
      exact hint γ
  have hnegq : -h ∈ quasiInt p k (Fin d) := by
    intro α i
    by_cases hα : α.degree = N
    · refine GlobalTheory.T.degree_part_integralDifferential_of_coboundary p k d μ hμ N f (-h) hN hf
        (fun β hβ => by rw [map_neg, hord β hβ, neg_zero]) (fun γ hγ => ?_) α i hα
      obtain ⟨w, hw⟩ := K γ (by omega)
      refine ⟨p * w + WittVector.teichmuller p (coeff γ c), ?_⟩
      rw [← sub_eq_add_neg, map_add (f := _), ← hw, map_sub, coeff_lift]; ring
    · rw [map_neg, hhom α hα, neg_zero, mul_zero]; exact ⟨0, by simp⟩
  refine ⟨h, hhom, sub_mem hf ((neg_mem_iff).1 hnegq), K⟩
end

section

set_option autoImplicit false

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

theorem isCoc_iff_mem_cocycles : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k)
    (c : Chart G d), ∀ (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), c.IsLawOf μ →
    ∀ s, IsCoc μ s ↔ (fun n => c.ev₂ n s) ∈ G.cocycles := by
  intro p k _ d G c μ hμ s
  have hcomp : ∀ n, pullbackTwo (G.res n) (c.ev₂ (n + 1) s) = c.ev₂ n s :=
    fun n => (GlobalTheory.T.functions_eq_series_in_chart p k d G c).2.1 n s
  have hnil := (GlobalTheory.T.eq_zero_of_eval_cube_levels p k d G c).1
  have hinj := (GlobalTheory.T.eq_zero_of_eval_cube_levels p k d G c).2
  have hcob : ∀ n, evA k _ (hnil n) (cob2 μ s) = cobTwo k (G.A n) (c.ev₂ n s) :=
    fun n => (GlobalTheory.T.connectedPDivGroupChart_coboundaryTwo_coord p k d G c μ hμ n (hnil n)).1 s
  have hswap : ∀ n, c.ev₂ n (Katz.swap s) = TensorProduct.comm k _ _ (c.ev₂ n s) :=
    fun n => (GlobalTheory.T.connectedChart_evalSquare_variables_swap_constant p k d G c n).2.2.1 s
  constructor
  · rintro ⟨h2, hs⟩ n
    refine ⟨mem_symCocycles.2 ⟨?_, ?_⟩, hcomp n⟩
    · rw [← hcob n, h2, map_zero]
    · rw [← hswap n, hs]
  · intro h
    refine ⟨?_, ?_⟩
    · refine hinj _ fun n hn => ?_
      have e := hcob n
      rw [(mem_symCocycles.1 (h n).1).1] at e
      exact e
    · obtain ⟨t, -, ht⟩ := (GlobalTheory.T.chart_square_coordinates_present_levels p k d G c).2 (fun n => c.ev₂ n s) hcomp
      have h1 := ht (Katz.swap s) fun n => by
        rw [hswap n]; exact (mem_symCocycles.1 (h n).1).2
      have h2 := ht s fun n => rfl
      rw [h1, h2]

end GlobalTheory.Katz
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

namespace GlobalTheory.HilbFam

theorem isFam_hfun_twist : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) (L : Lat F), 1 ≤ s → 0 < N → HasLevel N L → ∀ (ι : Type) (act : ι → SL(2, ℤ) → ι) (α : ι → Matrix (Fin 2) (Fin 2) (ZMod N)) (Ch : ι → ℍ → ℂ) (κ : Emb F → ℕ), (∀ i γ, α (act i γ) = α i * (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N)) → (∀ i (γ : SL(2, ℤ)) (τ : ℍ), Ch i (γ • τ) = (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) : ℂ) ^ 2 * Ch (act i γ) τ - ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) / (2 * Real.pi * Complex.I)) → IsFam act (wt (2 * s) κ : ℕ) (fun i ↦ hfun (2 * s) (twist N L (α i)) κ (Ch i)) := by
  intro hE F _ _ _ hF s N L hs hN hL ι act α Ch κ hα hC
  rw [GlobalTheory.T.isSLTwoPermutedModularFamily_iff_values]
  intro i γ τ
  have htw : twist N L (α (act i γ)) = mulMat (twist N L (α i)) (γ : Matrix (Fin 2) (Fin 2) ℤ) := by
    rw [hα]; exact GlobalTheory.T.hilbertLatticeTwistByMatrixModN_mul_SL2Z F N L (α i) γ hL.2
  have h := GlobalTheory.T.quasiPeriod_normalised_jet_modular_transform hE F hF s N (twist N L (α i)) hs hN (GlobalTheory.T.hilbertLatticeTwist_hasLevel F N L (α i) hL) κ γ (Ch i)
    (Ch (act i γ)) τ ⟨_, GlobalTheory.T.hilbertLatticeTwist_hasLevel F N L (α (act i γ)) hL, htw⟩ (hC i γ τ)
  rw [zpow_natCast]
  beta_reduce
  rw [h, htw]

end GlobalTheory.HilbFam
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.axesO1_of_projective_rank_cup : (∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → (Module.Finite R (HO1 A.hom) ∧ Module.Projective R (HO1 A.hom) ∧ ∀ p : PrimeSpectrum R, Module.rankAtStalk (HO1 A.hom) p = g) ∧ ∃ e : ⋀[R]^2 (HO1 A.hom) ≃ₗ[R] GlobalTheory.CatCoh.H2 (OAff A.hom), ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = GlobalTheory.CatCoh.cup (OAff A.hom) a b) → AxesVanishingStructureSheafDegOne := by
  first | exact @GlobalTheory.Obs.axesO1_of_cohomology_structure | exact GlobalTheory.Obs.axesO1_of_cohomology_structure | (intros; apply GlobalTheory.Obs.axesO1_of_cohomology_structure <;> assumption)
end
