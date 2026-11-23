module

public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle004
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle001
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle013
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle022
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MultiplicativeShiftEqTranslateBySmallPoint
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCmThetaEqSumProdTranslates
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsOrthogonalFrameNormsCoprimeOfUnimodular
public import Formalism.RealPlaceAnalysis.Bundle003
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle021
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
import Mathlib.RingTheory.Radical.NatInt
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle002
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open MvPowerSeries NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory.IndefiniteRowSideFullHecke

namespace GlobalTheory.GermDerivativeLinearMaps

section Calc

variable {k : Type} [CommRing k] {d : ℕ}

theorem dLin_comp (φ ψ : Pt k 1 d) (hψ : GP ψ) : dLin (comp1 φ ψ) = dLin φ * dLin ψ := by
  ext i j
  refine (FormalCalc.coeff_single_subst (a := fun p : Fin 1 × Fin d => (![ψ] : Fin 1 → Pt k 1 d) p.1 p.2)
    (fun p => single_point_zero_constant hψ p.1 p.2) (φ i) _).trans ?_
  rw [Fintype.sum_prod_type, Fin.sum_univ_one, Matrix.mul_apply]
  rfl

theorem germComp_matrixLinearMap_apply {n : ℕ} (U : Matrix (Fin d) (Fin d) k) (a : Pt k n d) (ha : GP a) (i : Fin d) :
    comp1 (LogExpAdaptedGauge.linMap U) a i = ∑ j, C (U i j) * a j := by
  have hz : FormalLog.CZ (![a] : Fin 1 → Pt k n d) := fun j l => single_point_zero_constant ha j l
  show ev ![a] (∑ j : Fin d, MvPowerSeries.C (U i j) * X ((0 : Fin 1), j)) = _
  rw [FormalLog.ev_sum hz]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [FormalLog.ev_mul hz, FormalLog.ev_C hz, FormalLog.ev_X hz]
  rfl

theorem gp_linMap (U : Matrix (Fin d) (Fin d) k) : GP (LogExpAdaptedGauge.linMap U) := fun i => by
  simp [LogExpAdaptedGauge.linMap]

theorem dLin_linMap (U : Matrix (Fin d) (Fin d) k) : dLin (LogExpAdaptedGauge.linMap U) = U := by
  classical
  ext i j
  simp [dLin, LogExpAdaptedGauge.linMap, coeff_C_mul, coeff_X, Finsupp.single_left_inj]

theorem linMap_one {n : ℕ} (a : Pt k n d) (ha : GP a) : comp1 (LogExpAdaptedGauge.linMap (1 : Matrix (Fin d) (Fin d) k)) a = a := by
  classical
  funext i
  rw [germComp_matrixLinearMap_apply _ _ ha, Finset.sum_eq_single i] <;> simp +contextual [Matrix.one_apply, eq_comm]

end Calc

section Log

variable {k : Type} [CommRing k] [Algebra ℚ k] {d : ℕ}

theorem additive_at {n : ℕ} (F : Fin d → PS k 2 d) (hF : ∀ i, constantCoeff (F i) = 0) (ψ : Pt k 1 d)
    (hψ : comp1 ψ (addOf F (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
      comp1 ψ (pt k (n := 2) d 0) + comp1 ψ (pt k (n := 2) d 1))
    (a b : Pt k n d) (ha : GP a) (hb : GP b) : comp1 ψ (addOf F a b) = comp1 ψ a + comp1 ψ b := by
  have hV := pair_points_zero_constant ha hb
  have e := congrArg (evP ![a, b]) hψ
  have e2 : ∀ u v : Pt k 2 d, evP ![a, b] (u + v) = evP ![a, b] u + evP ![a, b] v := fun u v =>
    funext fun i => gt_ev_add _ hV _ _
  rw [e2, evP_comp1 _ hV _ _ (gp_addOf F hF _ _ (gp_pt 0) (gp_pt 1)),
    evP_addOf _ hV _ _ _ (gp_pt 0) (gp_pt 1), evP_comp1 _ hV _ _ (gp_pt 0),
    evP_comp1 _ hV _ _ (gp_pt 1), evP_pt _ hV, evP_pt _ hV] at e
  exact e

theorem germLinearPart_coordinatePoint_zero : dLin (pt k (n := 1) d 0) = 1 := by
  rw [← linMap_one (pt k (n := 1) d 0) (gp_pt 0), gt_comp1_pt_right, dLin_linMap]

theorem additive_eq_lin (F : Fin d → PS k 2 d) (hF : ∀ i, constantCoeff (F i) = 0) (ℓ ε ψ : Pt k 1 d)
    (h1 : dLin ℓ = 1) (hℓ : comp1 ℓ (addOf F (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
      comp1 ℓ (pt k (n := 2) d 0) + comp1 ℓ (pt k (n := 2) d 1)) (hi : IsInvPair ℓ ε) (h0 : GP ψ)
    (hψ : comp1 ψ (addOf F (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
      comp1 ψ (pt k (n := 2) d 0) + comp1 ψ (pt k (n := 2) d 1)) :
    ψ = comp1 (LogExpAdaptedGauge.linMap (dLin ψ)) ℓ := by
  classical
  have hε : GP ε := hi.2.1
  have hℓ0 : GP ℓ := hi.1
  have p0 : GP (pt k (n := 2) d 0) := gp_pt 0
  have p1 : GP (pt k (n := 2) d 1) := gp_pt 1
  have q0 := gp_comp1 _ _ hε p0
  have q1 := gp_comp1 _ _ hε p1
  have ps : GP (pt k (n := 2) d 0 + pt k (n := 2) d 1) := fun i => by simp [pt]
  have e1 : comp1 ε (pt k (n := 2) d 0 + pt k (n := 2) d 1) =
      addOf F (comp1 ε (pt k (n := 2) d 0)) (comp1 ε (pt k (n := 2) d 1)) := by
    rw [← gt_comp_inv' hi _ (gp_addOf F hF _ _ q0 q1), additive_at F hF ℓ hℓ _ _ q0 q1,
      gt_comp_inv hi _ p0, gt_comp_inv hi _ p1]
  have e2 : comp1 (comp1 ψ ε) (pt k (n := 2) d 0 + pt k (n := 2) d 1) =
      comp1 (comp1 ψ ε) (pt k (n := 2) d 0) + comp1 (comp1 ψ ε) (pt k (n := 2) d 1) := by
    rw [gt_comp1_comp1 _ _ hε _ ps, gt_comp1_comp1 _ _ hε _ p0, gt_comp1_comp1 _ _ hε _ p1, e1,
      additive_at F hF ψ hψ _ _ q0 q1]
  have hdε : dLin ε = 1 := by
    have := dLin_comp ℓ ε hε
    rwa [hi.2.2.1, germLinearPart_coordinatePoint_zero, h1, one_mul, eq_comm] at this
  have e3 : comp1 ψ ε = LogExpAdaptedGauge.linMap (dLin ψ) := by
    have hd : dLin (comp1 ψ ε) = dLin (LogExpAdaptedGauge.linMap (dLin ψ)) := by
      rw [dLin_comp _ _ hε, hdε, mul_one, dLin_linMap]
    funext i
    ext e
    by_cases he : e.degree = 1
    · obtain ⟨⟨s, j⟩, rfl⟩ : ∃ s, e = Finsupp.single s 1 := by
        exact (Finsupp.sum_eq_one_iff e).1 he
      obtain rfl : s = 0 := Subsingleton.elim _ _
      exact congrFun (congrFun hd i) j
    · rw [addition_linear k d _ (congrFun e2 i) e he]

      simp only [LogExpAdaptedGauge.linMap, map_sum, coeff_C_mul, coeff_X]
      refine (Finset.sum_eq_zero fun j _ => ?_).symm
      rw [if_neg, mul_zero]
      rintro rfl
      simp at he
  rw [← e3, gt_comp1_comp1 _ _ hε _ hℓ0, hi.2.2.2, gt_comp1_pt_right]

end Log

section Predicates

variable {C : Type} [NormedField C] [IsUltrametricDist C] {d : ℕ}

end Predicates

section Predicates2

variable {R : Type} [CommRing R] {d : ℕ} (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]
  {O : Type} [CommRing O] [StarRing O]

end Predicates2

section Letters

variable {C : Type} [NormedField C] [IsUltrametricDist C] [CharZero C]
  {E : Type} [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] {d : ℕ}

end Letters

section Frame

variable {C : Type} [NormedField C] [IsUltrametricDist C] [CharZero C]
  {E : Type} [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] {d : ℕ}

end Frame

end GlobalTheory.GermDerivativeLinearMaps
end
end

section

open Finset

namespace GlobalTheory.WigSh

private theorem strictAnti_of_box {n : ℕ} {L : Fin (n+1) → ℤ} {M : Fin n → ℤ}
    (h : ∀ j : Fin n, L j.succ < M j ∧ M j ≤ L j.castSucc) : StrictAnti L :=
  Fin.strictAnti_iff_succ_lt.2 fun j => (h j).1.trans_le (h j).2

private theorem chain_prod_le {n₀ : ℕ} {D : ℝ} (hD : 1 ≤ D) (f : ℕ → ℝ)
    (hf : ∀ j < n₀, (D ^ 2)⁻¹ ≤ f j) : (D ^ (2 * n₀))⁻¹ ≤ ∏ j ∈ Finset.range n₀, f j := by
  have h1 : (D ^ (2 * n₀))⁻¹ = ∏ _j ∈ Finset.range n₀, (D ^ 2)⁻¹ := by
    rw [Finset.prod_const, Finset.card_range, pow_mul, inv_pow]
  rw [h1]
  exact Finset.prod_le_prod₀ (fun _ _ => by positivity)
    (fun j hj => hf j (Finset.mem_range.1 hj))

theorem chain_lower_bound : ∀ (n : ℕ) (L : Fin (n+1) → ℤ) (M : Fin n → ℤ) (i : Fin n) (n₀ : ℕ) (b : ℝ), StrictAnti L → (∀ j : Fin n, L j.succ < M j ∧ M j ≤ L j.castSucc) → L i.succ + 2 * (n₀ : ℤ) + 1 ≤ L i.castSucc → 1 ≤ b → (n₀ : ℝ) ≤ b → ((L 0 : ℝ) - L (Fin.last n) ≤ 2 * b) → (((3 * b) ^ (2 * n₀))⁻¹ ≤ ∏ j ∈ Finset.range n₀, GlobalTheory.WigSh.wP (Function.update L i.succ (L i.succ + (j : ℤ))) M i.succ) ∨ (((3 * b) ^ (2 * n₀))⁻¹ ≤ ∏ j ∈ Finset.range n₀, GlobalTheory.WigSh.wM (Function.update L i.castSucc (L i.castSucc - (j : ℤ))) M i.castSucc) := by
  intro n L M i n₀ b hL hbox hgap hb hn hspan
  have hD : (1 : ℝ) ≤ 3 * b := by linarith
  have h0 : ∀ k, (L k : ℝ) ≤ L 0 := fun k => by
    exact_mod_cast hL.antitone (Fin.zero_le k)
  have hl : ∀ k, (L (Fin.last n) : ℝ) ≤ L k := fun k => by
    exact_mod_cast hL.antitone (Fin.le_last k)
  have hlt : ∀ k : Fin n, k < i → L i.castSucc < M k := fun k hk =>
    lt_of_le_of_lt (hL.antitone (by
      rw [Fin.le_def]; simp only [Fin.val_succ, Fin.val_castSucc]; exact hk)) (hbox k).1
  have hgt : ∀ k : Fin n, i < k → M k ≤ L i.succ := fun k hk =>
    le_trans (hbox k).2 (hL.antitone (by
      rw [Fin.le_def]; simp only [Fin.val_succ, Fin.val_castSucc]; exact hk))
  by_cases hc : L i.succ + n₀ + 1 ≤ M i
  · left
    refine chain_prod_le hD _ fun j hj => ?_
    have hjZ : (j : ℤ) < n₀ := by exact_mod_cast hj
    have hjR : (j : ℝ) ≤ b := le_trans (by exact_mod_cast hj.le) hn
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hbox' : ∀ k : Fin n, Function.update L i.succ (L i.succ + (j : ℤ)) k.succ < M k ∧
        M k ≤ Function.update L i.succ (L i.succ + (j : ℤ)) k.castSucc := by
      intro k
      constructor
      · by_cases hk : k = i
        · subst hk
          rw [Function.update_self]; omega
        · rw [Function.update_of_ne (fun h => hk (Fin.succ_injective _ h))]
          exact (hbox k).1
      · by_cases hk : k.castSucc = i.succ
        · have := (hbox k).2
          rw [hk] at this ⊢
          rw [Function.update_self]; omega
        · rw [Function.update_of_ne hk]
          exact (hbox k).2
    refine GlobalTheory.T.inv_sq_le_wignerCoeffSqRaising n _ M i.succ (3 * b) (strictAnti_of_box hbox') hbox' ?_ hD ?_ ?_
    · intro k
      rw [Function.update_self]
      rcases lt_trichotomy k i with hk | hk | hk
      · have := hlt k hk; omega
      · subst hk; omega
      · have := hgt k hk; omega
    · rw [Function.update_self, Function.update_of_ne (Fin.succ_ne_zero i).symm]
      push_cast
      have := hl i.succ
      linarith
    · rw [Function.update_self]
      by_cases hk : Fin.last n = i.succ
      · rw [hk, Function.update_self]; linarith
      · rw [Function.update_of_ne hk]
        push_cast
        have := h0 i.succ
        linarith
  · right
    refine chain_prod_le hD _ fun j hj => ?_
    have hjZ : (j : ℤ) < n₀ := by exact_mod_cast hj
    have hjR : (j : ℝ) ≤ b := le_trans (by exact_mod_cast hj.le) hn
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hbox' : ∀ k : Fin n,
        Function.update L i.castSucc (L i.castSucc - (j : ℤ)) k.succ < M k ∧
        M k ≤ Function.update L i.castSucc (L i.castSucc - (j : ℤ)) k.castSucc := by
      intro k
      constructor
      · by_cases hk : k.succ = i.castSucc
        · have hki : k < i := by
            have := congrArg Fin.val hk
            simp only [Fin.val_succ, Fin.val_castSucc] at this
            rw [Fin.lt_def]; omega
          have := hlt k hki
          rw [hk, Function.update_self]; omega
        · rw [Function.update_of_ne hk]
          exact (hbox k).1
      · by_cases hk : k = i
        · subst hk
          rw [Function.update_self]; omega
        · rw [Function.update_of_ne (fun h => hk (Fin.castSucc_injective _ h))]
          exact (hbox k).2
    refine GlobalTheory.T.inv_sq_le_wignerCoeffSqLowering n _ M i.castSucc (3 * b) (strictAnti_of_box hbox') hbox' ?_ hD ?_ ?_
    · intro k
      rw [Function.update_self]
      rcases lt_trichotomy k i with hk | hk | hk
      · have := hlt k hk; omega
      · subst hk; omega
      · have := hgt k hk; omega
    · rw [Function.update_self]
      by_cases hk : 0 = i.castSucc
      · rw [hk, Function.update_self]; linarith
      · rw [Function.update_of_ne hk]
        push_cast
        have := hl i.castSucc
        linarith
    · rw [Function.update_self, Function.update_of_ne (Fin.castSucc_lt_last i).ne']
      push_cast
      have := h0 i.castSucc
      linarith

end GlobalTheory.WigSh
end

section

open GlobalTheory.ConvSer

theorem _root_.GlobalTheory.T.exists_limit_powerSeries_agree_on_annulus_points : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (G : ℕ → Finset K) (r : ℝ), 0 < r → r ≤ 1 → Monotone G → (∀ n, ∀ x ∈ G n, r ≤ ‖x‖ ∧ ‖x‖ < 1) → Filter.Tendsto (fun n => ∏ x ∈ G n, ‖x‖) Filter.atTop (nhds 0) → ∀ g : ℕ → PowerSeries K, (∀ n, Intg (g n)) → (∀ n, ∀ x ∈ G n, ev1 (g (n + 1)) x = ev1 (g n) x) → ∃ f : PowerSeries K, Intg f ∧ (∀ k, Filter.Tendsto (fun n => PowerSeries.coeff k (g n)) Filter.atTop (nhds (PowerSeries.coeff k f))) ∧ ∀ n, ∀ x ∈ G n, ev1 f x = ev1 (g n) x := by
  first | exact @GlobalTheory.ConvSer.exists_limit_of_agree_on_points | exact GlobalTheory.ConvSer.exists_limit_of_agree_on_points | (intros; apply GlobalTheory.ConvSer.exists_limit_of_agree_on_points <;> assumption)
end

section

open GlobalTheory.ConvSer

theorem _root_.GlobalTheory.T.mvPowerSeriesConvergentSubst_isRingHom_on_bounded : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (σ τ : Type) [Fintype σ] (s : σ → MvPowerSeries τ K), (∀ i, Small (s i)) → (∀ S T : MvPowerSeries σ K, Bdd S → Bdd T → csub s (S + T) = csub s S + csub s T ∧ csub s (S - T) = csub s S - csub s T ∧ csub s (S * T) = csub s S * csub s T) ∧ (∀ a : K, csub s (MvPowerSeries.C a) = MvPowerSeries.C a) ∧ (∀ i, csub s (MvPowerSeries.X i) = s i) ∧ (∀ (S : MvPowerSeries σ K) (n : ℕ), Bdd S → csub s (S ^ n) = csub s S ^ n) ∧ (∀ (ι : Type) (t : Finset ι) (f : ι → MvPowerSeries σ K), (∀ i ∈ t, Bdd (f i)) → csub s (∏ i ∈ t, f i) = ∏ i ∈ t, csub s (f i)) ∧ (∀ (k ι : Type) [CommRing k] (φ : k →+* K) (a : ι → MvPowerSeries σ K) (A : MvPolynomial ι k), (∀ j, Bdd (a j)) → csub s (MvPolynomial.eval₂ ((MvPowerSeries.C : K →+* MvPowerSeries σ K).comp φ) a A) = MvPolynomial.eval₂ ((MvPowerSeries.C : K →+* MvPowerSeries τ K).comp φ) (fun j => csub s (a j)) A) := by
  first | exact @GlobalTheory.ConvSer.csub_ring_map | exact GlobalTheory.ConvSer.csub_ring_map | (intros; apply GlobalTheory.ConvSer.csub_ring_map <;> assumption)
end

section

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne

theorem thue_normSq (d e : ℕ) (he : d + 1 = 4 * e) (u v : ℤ) :
    Complex.normSq ((u : ℂ) + (v : ℂ) * wK d) = ((u ^ 2 + u * v + e * v ^ 2 : ℤ) : ℝ) := by
  have hs : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt (Nat.cast_nonneg d)
  have he' : (d : ℝ) + 1 = 4 * e := by exact_mod_cast he
  have h1 : ((u : ℂ) + (v : ℂ) * wK d).re = u + v / 2 := by
    simp [wK]; ring
  have h2 : ((u : ℂ) + (v : ℂ) * wK d).im = v * Real.sqrt d / 2 := by
    simp [wK]; ring
  rw [Complex.normSq_apply, h1, h2]
  push_cast
  linear_combination ((v : ℝ) ^ 2 / 4) * hs + ((v : ℝ) ^ 2 / 4) * he'

theorem thue_norm_zc {q : ℕ} [Fact q.Prime] (a : ℤ_[q]) : ‖zc a‖ = ‖a‖ := by
  unfold zc
  rw [norm_algebraMap', PadicInt.padic_norm_e_of_padicInt]

theorem thue_pigeon {q : ℕ} [Fact q.Prime] (a : ℤ_[q]) (k : ℕ) :
    ∃ u v : ℤ, (u ≠ 0 ∨ v ≠ 0) ∧ u ^ 2 ≤ (q : ℤ) ^ k ∧ v ^ 2 ≤ (q : ℤ) ^ k ∧
      ‖(u : ℤ_[q]) + (v : ℤ_[q]) * a‖ ≤ (q : ℝ) ^ (-(k : ℤ)) := by
  have hq : q.Prime := Fact.out
  haveI : NeZero (q ^ k) := ⟨pow_ne_zero _ hq.ne_zero⟩
  set m := Nat.sqrt (q ^ k) with hm
  let f : Fin (m + 1) × Fin (m + 1) → ZMod (q ^ k) := fun p =>
    PadicInt.toZModPow k (((p.1 : ℕ) : ℤ_[q]) + ((p.2 : ℕ) : ℤ_[q]) * a)
  have hcard : Fintype.card (ZMod (q ^ k)) < Fintype.card (Fin (m + 1) × Fin (m + 1)) := by
    rw [ZMod.card, Fintype.card_prod, Fintype.card_fin]
    exact Nat.lt_succ_sqrt _
  obtain ⟨x, y, hxy, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  have hm2 : ((m : ℤ)) ^ 2 ≤ (q : ℤ) ^ k := by
    have := Nat.sqrt_le' (q ^ k)
    exact_mod_cast this
  have hb : ∀ i j : Fin (m + 1), (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) ^ 2 ≤ (q : ℤ) ^ k := by
    intro i j
    have hi := i.2
    have hj := j.2
    refine le_trans ?_ hm2
    apply sq_le_sq' <;> omega
  refine ⟨((x.1 : ℕ) : ℤ) - ((y.1 : ℕ) : ℤ), ((x.2 : ℕ) : ℤ) - ((y.2 : ℕ) : ℤ), ?_, hb _ _, hb _ _, ?_⟩
  · by_contra h
    push_neg at h
    apply hxy
    ext
    · have := h.1; omega
    · have := h.2; omega
  · rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker]
    have : PadicInt.toZModPow k ((((x.1 : ℕ) : ℤ_[q]) + ((x.2 : ℕ) : ℤ_[q]) * a) -
        (((y.1 : ℕ) : ℤ_[q]) + ((y.2 : ℕ) : ℤ_[q]) * a)) = 0 := by
      rw [map_sub, sub_eq_zero]; exact hf
    rw [← this]
    congr 1
    push_cast
    ring

theorem exists_small_in_prime_pow : ∀ (d q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]), d.Prime → d % 16 = 7 → Split d q → ∀ k : ℕ, ∃ (β : ℂ) (N : ℕ), InOK d β ∧ β ≠ 0 ∧ ‖ι β‖ ≤ (q : ℝ) ^ (-(k : ℤ)) ∧ (N : ℂ) = β * conj β ∧ N ≤ (d + 3) * q ^ k := by
  intro d q _ ι hd h16 hs k
  obtain ⟨⟨-, hw, -⟩, h2, -⟩ := GlobalTheory.T.imagQuadraticMaximalOrder_arithmetic_at_split_prime d q ι hd h16 hs
  obtain ⟨⟨a, ha⟩, -⟩ := h2 _ hw
  obtain ⟨u, v, huv, hu, hv, hn⟩ := thue_pigeon a k
  obtain ⟨e, he⟩ : ∃ e : ℕ, d + 1 = 4 * e := ⟨(d + 1) / 4, by omega⟩
  have he1 : (1 : ℤ) ≤ e := by omega
  have hed : (e : ℤ) ≤ d := by omega
  have hpos : 0 < u ^ 2 + u * v + e * v ^ 2 := by
    have h3 : v ^ 2 ≤ e * v ^ 2 := by nlinarith [sq_nonneg v]
    have h4 : 0 < u ^ 2 + v ^ 2 := by
      rcases huv with h | h
      · have := sq_pos_of_ne_zero h; nlinarith [sq_nonneg v]
      · have := sq_pos_of_ne_zero h; nlinarith [sq_nonneg u]
    nlinarith [sq_nonneg (u + v)]
  have hN := thue_normSq d e he u v
  obtain ⟨N, hNe⟩ := Int.eq_ofNat_of_zero_le hpos.le
  refine ⟨(u : ℂ) + (v : ℂ) * wK d, N, ⟨u, v, rfl⟩, ?_, ?_, ?_, ?_⟩
  · intro h
    rw [h, map_zero] at hN
    have : u ^ 2 + u * v + e * v ^ 2 = 0 := by exact_mod_cast hN.symm
    omega
  · have : ι ((u : ℂ) + (v : ℂ) * wK d) = zc ((u : ℤ_[q]) + (v : ℤ_[q]) * a) := by
      rw [map_add (f := _), map_mul, ha]
      simp [zc]
    rw [this, thue_norm_zc]
    exact hn
  · rw [Complex.mul_conj, hN, hNe]
    simp
  · have h5 : (e : ℤ) * v ^ 2 ≤ d * (q : ℤ) ^ k :=
      mul_le_mul hed hv (sq_nonneg v) (by positivity)
    have h6 : (N : ℤ) ≤ (d + 3) * (q : ℤ) ^ k := by
      rw [← hNe]
      nlinarith [sq_nonneg (u - v), sq_nonneg u, sq_nonneg v]
    exact_mod_cast h6

end GlobalTheory.MomOne
end

section

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

theorem _root_.GlobalTheory.T.exists_ellipticFunction_mul_prod_eq_xy : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (φ : ℂ → ℂ), M.Ok → Ell M.L φ → ∃ (m : ℕ) (P : Fin m → ℂ) (A B : Polynomial ℂ), (∀ i, P i ∉ M.L.lattice ∧ meromorphicOrderAt φ (P i) < 0) ∧ ∀ z₀ : ℂ, ∀ᶠ z in 𝓝[≠] z₀, φ z * (∏ i, (Polynomial.X - Polynomial.C (M.x (P i)))).eval (M.x z) = A.eval (M.x z) + B.eval (M.x z) * M.y z := by
  first | exact @GlobalTheory.EllipticModel.exists_mul_prod_eq_xy | exact GlobalTheory.EllipticModel.exists_mul_prod_eq_xy | (intros; apply GlobalTheory.EllipticModel.exists_mul_prod_eq_xy <;> assumption)
end

section

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

theorem _root_.GlobalTheory.T.multiplicativeShift_eq_translate_by_small_point : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (ω ζ : ℂ_[q]) (p : ℂ), M.MChart ω → M.At ω ζ p → hat M.ι (C ω * logS) (fun z => M.u (z + p)) = shiftS ζ (hat M.ι (C ω * logS) M.u) ∧ hat M.ι (C ω * logS) (fun z => M.w (z + p)) = shiftS ζ (hat M.ι (C ω * logS) M.w) := by
  first | exact @GlobalTheory.MomOne.SmallTranslate.shift_eq_translate | exact GlobalTheory.MomOne.SmallTranslate.shift_eq_translate | (intros; apply GlobalTheory.MomOne.SmallTranslate.shift_eq_translate <;> assumption)
end

section

open GlobalTheory.MomOne Formalism.L2.Ker.JMB
open scoped ComplexConjugate BigOperators

theorem _root_.GlobalTheory.T.exists_padicInt_frame_change_etale_basis : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (g : ℕ) (S : Setup g) (x : Fin g → Fin g → ℂ) (a : Fin g → ℕ) (r : ℕ) (b : Fin r → Fin g → ℂ), S.Ok → Split S.d q → (∀ i, x i ∈ S.La) → (∀ i j, beta S.d S.Hm (x i) (x j) = if i = j then (a i : ℂ) else 0) → (∀ i, 0 < a i ∧ Nat.Coprime (a i) q) → S.NNBasis q b → ∃ T : (Fin r → ℤ_[q]) ≃ₜ (Fin g → ℤ_[q]), ∀ A i, GlobalTheory.MomOne.zc (T A i) = ∑ j, GlobalTheory.MomOne.zc (A j) * ι (beta S.d S.Hm (x i) (b j)) := by
  first | exact @GlobalTheory.MomOne.frameChange | exact GlobalTheory.MomOne.frameChange | (intros; apply GlobalTheory.MomOne.frameChange <;> assumption)
end

section

open GlobalTheory.MomOne Formalism.L2.Ker.JMB
open scoped ComplexConjugate BigOperators

theorem _root_.GlobalTheory.T.exists_cmTheta_eq_sum_prod_translates : ∀ (q : ℕ) (g : ℕ) (S : Setup g) (x : Fin g → Fin g → ℂ) (a : Fin g → ℕ) (θ : ℂ → ℂ), q.Prime → S.Ok → (∀ i, x i ∈ S.La) → (∀ i j, beta S.d S.Hm (x i) (x j) = if i = j then (a i : ℂ) else 0) → (∀ i, 0 < a i ∧ Nat.Coprime (a i) q) → IsTh S.d θ → ∃ (m : ℕ) (r : Fin m → ℂ) (t : Fin m → Fin g → ℂ) (Θ : (Fin g → ℂ) → ℂ), S.IsTheta Θ ∧ Θ ≠ 0 ∧ (∀ j, r j ∈ Qbar) ∧ (∀ j i, PrimeTo S.d q (t j i)) ∧ ∀ z : Fin g → ℂ, Θ (∑ i, z i • x i) = ∑ j, r j * ∏ i, U1 S.d (t j i) θ (z i) ^ a i := by
  first | exact @GlobalTheory.MomOne.exists_theta_eq_sum_prod | exact GlobalTheory.MomOne.exists_theta_eq_sum_prod | (intros; apply GlobalTheory.MomOne.exists_theta_eq_sum_prod <;> assumption)
end

section

open GlobalTheory.MomOne Formalism.L2.Ker.JMB
open scoped ComplexConjugate BigOperators

theorem _root_.GlobalTheory.T.exists_orthogonal_frame_norms_coprime_of_unimodular : ∀ (q g : ℕ) (S : Setup g), q.Prime → S.Ok → ¬ q ∣ S.d → ∃ (x : Fin g → Fin g → ℂ) (a : Fin g → ℕ), (∀ i, x i ∈ S.La) ∧ (∀ i j, beta S.d S.Hm (x i) (x j) = if i = j then (a i : ℂ) else 0) ∧ ∀ i, 0 < a i ∧ Nat.Coprime (a i) q := by
  first | exact @GlobalTheory.MomOne.exists_orthFrame | exact GlobalTheory.MomOne.exists_orthFrame | (intros; apply GlobalTheory.MomOne.exists_orthFrame <;> assumption)
end

section

open Formalism.REAL Finset

theorem _root_.GlobalTheory.T.qminor_intertwining_apply : ∀ (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (n t : ℕ) (E : Fin n → Fin n → Module.End ℂ V) (E' : Fin n → Fin n → Module.End ℂ W) (ι : W →ₗ[ℂ] V), (∀ a b w, ι (E' a b w) = E a b (ι w)) → ∀ (a b : Fin t → Fin n) (u : ℂ) (w : W), ι (qminor E' a b u w) = qminor E a b u (ι w) := by
  first | exact @GlobalTheory.qminor_intertwine | exact GlobalTheory.qminor_intertwine | (intros; apply GlobalTheory.qminor_intertwine <;> assumption)
end
