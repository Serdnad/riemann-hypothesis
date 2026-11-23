module

public import Formalism.SharpRestriction.Divisibility.WeightFamilies
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle006
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFinsetSelfDualClassesHerm
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.TraceFormDualOneTraceFormDual
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsHermCoordOfDatum
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FinrankEqOfInjectiveOfSpan
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HermitianFormsSameSignatureSameSpace
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle015
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
import Formalism.SharpRestriction.Divisibility.WeightAlgebra
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory.LogSupMultiple

theorem le_exp_of_log_le {x b : ℝ} (h : Real.log x ≤ b) (hx : 0 ≤ x) : x ≤ Real.exp b := by
  rcases hx.eq_or_lt with rfl | hpos
  · exact (Real.exp_pos b).le
  · exact (Real.log_le_iff_le_exp hpos).1 h

theorem log_le_of_le_exp {x b : ℝ} (h : x ≤ Real.exp b) (hx : 0 ≤ x) (hb : 0 ≤ b) : Real.log x ≤ b := by
  rcases hx.eq_or_lt with rfl | hpos
  · simpa using hb
  · exact (Real.log_le_iff_le_exp hpos).2 h

theorem supN_sum_le {D : D7} (B : WeightFamilies.Prov D) (j : ℕ) (w : WeightFamilies.Wt D j) (σ : B.KO →+* ℂ) {ι : Type}
    (s : Finset ι) (F : ι → B.Cusp j w) :
    B.supN j w σ (∑ i ∈ s, F i) ≤ ∑ i ∈ s, B.supN j w σ (F i) :=
    Finset.le_sum_of_subadditive (B.supN j w σ) (le_of_eq ((B.supN_eq_zero j w σ 0).2 rfl))
      (B.supN_add j w σ) s F

theorem log_supN_bounds : ∀ (D : D7) (B : WeightFamilies.Prov D) (j : ℕ) (w : WeightFamilies.Wt D j), (∀ (σ : B.KO →+* ℂ) (s : B.KO) (F : B.Cusp j w) (a b : ℝ), 0 ≤ a + b → Real.log ‖σ s‖ ≤ a → Real.log (B.supN j w σ F) ≤ b → 0 ≤ b → 0 ≤ a → Real.log (B.supN j w σ (s • F)) ≤ a + b) ∧ (∀ (σ : B.KO →+* ℂ) (N : ℕ) (c : Fin N → ℕ) (F : Fin N → B.Cusp j w) (b : ℝ), 0 ≤ b → (∀ i, c i ≤ N) → (∀ i, Real.log (B.supN j w σ (F i)) ≤ b) → Real.log (B.supN j w σ (∑ i, (c i : B.KO) • F i)) ≤ 2 * Real.log N + b) ∧ ∀ b : ℝ, (∑ _σ : B.KO →+* ℂ, b) / (Fintype.card (B.KO →+* ℂ) : ℝ) = b := by
  intro D B j w
  refine ⟨?_, ?_, ?_⟩
  ·
    intro σ s F a b _ hs hF hb ha
    rw [B.supN_smul]
    have hF0 := B.supN_nonneg j w σ F
    have h1 : ‖σ s‖ ≤ Real.exp a := le_exp_of_log_le hs (norm_nonneg _)
    have h2 : B.supN j w σ F ≤ Real.exp b := le_exp_of_log_le hF hF0
    refine log_le_of_le_exp ?_ (mul_nonneg (norm_nonneg _) hF0) (add_nonneg ha hb)
    rw [Real.exp_add]
    exact mul_le_mul h1 h2 hF0 (Real.exp_pos a).le
  ·
    intro σ N c F b hb hc hF
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · rw [Fin.sum_univ_zero, (B.supN_eq_zero j w σ 0).2 rfl]
      simpa using hb
    · have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have hNpos : (0 : ℝ) < N := by linarith
      have hsum : B.supN j w σ (∑ i, (c i : B.KO) • F i) ≤ (N : ℝ) * ((N : ℝ) * Real.exp b) :=
        calc B.supN j w σ (∑ i, (c i : B.KO) • F i)
            ≤ ∑ i, B.supN j w σ ((c i : B.KO) • F i) := supN_sum_le B j w σ _ _
          _ ≤ ∑ _i : Fin N, (N : ℝ) * Real.exp b := by
            apply Finset.sum_le_sum
            intro i _
            rw [B.supN_smul, map_natCast, Complex.norm_natCast]
            exact mul_le_mul (by exact_mod_cast hc i) (le_exp_of_log_le (hF i) (B.supN_nonneg _ _ _ _))
              (B.supN_nonneg _ _ _ _) hNpos.le
          _ = (N : ℝ) * ((N : ℝ) * Real.exp b) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hexp : Real.exp (2 * Real.log N + b) = (N : ℝ) * ((N : ℝ) * Real.exp b) := by
        rw [Real.exp_add, two_mul, Real.exp_add, Real.exp_log hNpos]
        ring
      refine log_le_of_le_exp ?_ (B.supN_nonneg _ _ _ _) ?_
      · rw [hexp]
        exact hsum
      · have := Real.log_nonneg hN1
        linarith
  ·
    intro b
    have hcard : (Fintype.card (B.KO →+* ℂ) : ℝ) ≠ 0 := by
      have : 0 < Fintype.card (B.KO →+* ℂ) := Fintype.card_pos
      exact_mod_cast this.ne'
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_div_cancel_left₀ b hcard

end GlobalTheory.LogSupMultiple
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory

theorem page_two_le_L_and_signs : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), FamilyHypotheses.HypPage large₂ X H C2 A2 CR CT ka wL wF Tn nP nW h0 → ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ ka → 2 ≤ large₂.sc.L ∧ 2 ≤ D.R.f ∧ 6 ≤ D.R.r ∧ 0 ≤ lamStar D ∧ (1 ≤ j → 1 ≤ WeightFamilies.dimY D j) ∧ (FamilyHypotheses.SupBoundPageRows D large₂ ka ↔ ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ ka) := by
  intro D B P j X large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hp hc
  have hm := D.R.two_le_m
  have hk := D.R.m_add_three_le_k
  have hf : 2 ≤ D.R.f := by
    have : 0 < D.R.ord := D.R.ord_pos
    unfold Ranks.f Ranks.n; omega
  have hr : 6 ≤ D.R.r := by unfold Ranks.r; omega
  refine ⟨?_, hf, hr, ?_, ?_, Iff.rfl⟩
  · obtain ⟨-, hS, -⟩ := hp
    have hn : ka.n = D.R.nV := hS.1
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hC, hZ, -⟩ := hS
    obtain ⟨-, -, -, -, hlf, -, -, -, hln⟩ := hc
    by_contra hL
    push_neg at hL
    have hf0 : (0 : ℝ) < D.R.f := by exact_mod_cast (by omega : 0 < D.R.f)
    have hr0 : (0 : ℝ) < D.R.r := by exact_mod_cast (by omega : 0 < D.R.r)
    have hrn : (D.R.r : ℝ) ≤ ka.n := by
      rw [hn]; exact_mod_cast (by unfold Ranks.nV; omega : D.R.r ≤ D.R.nV)
    have he : Real.exp 1 ≤ 3 := (Real.exp_one_lt_d9.trans (by norm_num)).le
    have he4 : Real.exp 4 ≤ 81 := by
      have : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
      rw [this]
      calc Real.exp 1 ^ 4 ≤ 3 ^ 4 := pow_le_pow_left₀ (Real.exp_pos 1).le he 4
        _ = 81 := by norm_num
    have hf1 : (D.R.f : ℝ) ≤ 81 :=
      ((Real.log_le_iff_le_exp hf0).1 (by linarith : Real.log D.R.f ≤ 4)).trans he4
    have hr1 : (D.R.r : ℝ) ≤ 81 :=
      hrn.trans (((Real.log_le_iff_le_exp (hr0.trans_le hrn)).1
        (by linarith : Real.log ka.n ≤ 4)).trans he4)
    have hfr : (D.R.f : ℝ) * D.R.r ≤ 81 * 81 := mul_le_mul hf1 hr1 hr0.le (by norm_num)
    have hZ2 : Zb D large₂ ≤ 81 * 81 * 2 := by
      unfold Zb
      have := mul_pos hf0 hr0
      nlinarith
    have hC2 : (1000 : ℝ) ^ 20 ≤ H.C1 ^ 20 := pow_le_pow_left₀ (by norm_num) hC 20
    have : (81 * 81 * 2 : ℝ) < 1000 ^ 20 := by norm_num
    linarith
  · unfold lamStar
    have h1 := Real.log_natCast_nonneg (D.host.g 0 * D.host.g 1)
    have h2 := Real.log_natCast_nonneg (D.R.f ^ 2 * D.host.q * D.host.d)
    push_cast at h1 h2
    have e : 4 * ((D.R.f : ℝ) / 2) ^ 2 = (D.R.f : ℝ) ^ 2 := by ring
    rw [e]
    exact add_nonneg h1 h2
  · intro hj
    unfold WeightFamilies.dimY
    have hp5 : 5 ≤ (D.R.sigW j).1 := by
      show 5 ≤ D.R.k + j - 1
      omega
    have h1 : 1 ≤ (D.R.sigW j).1 * ((D.R.sigW j).1 - 1) / 2 := by
      have : 5 * 4 ≤ (D.R.sigW j).1 * ((D.R.sigW j).1 - 1) := Nat.mul_le_mul hp5 (by omega)
      omega
    exact Nat.mul_pos (by omega) (by omega)

end GlobalTheory
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory.ScaledGenerators

theorem span_scaled {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (wL : WeightFamilies.Wt D j)
    (s : 𝓞 B.KO) {N : ℕ} (w0 : Fin N → B.Cusp j wL)
    (h : Submodule.span (𝓞 B.KO) (Set.range w0) = X.thAll wL) :
    Submodule.span (𝓞 B.KO) (Set.range fun k => (s : B.KO) • w0 k) = X.WWc s wL := by

  have hfun : (fun k => (s : B.KO) • w0 k) =
      (s • (LinearMap.id : B.Cusp j wL →ₗ[𝓞 B.KO] B.Cusp j wL)) ∘ w0 := by
    funext k
    simp only [Function.comp_apply, LinearMap.smul_apply, LinearMap.id_apply]
    first
      | rfl
      | exact algebraMap_smul B.KO s (w0 k)
      | simp
  rw [hfun, Set.range_comp, ← Submodule.map_span, h]
  rfl

theorem scaled_family : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (ka wL wF : WeightFamilies.Wt D j) (S : Scal B) (N : ℕ) (w0 : Fin N → B.Cusp j wL) (a b G Prw : ℝ), 0 ≤ a → 0 ≤ b → (∀ σ : B.KO →+* ℂ, Real.log ‖σ (S.sW : B.KO)‖ ≤ a) → Submodule.span (𝓞 B.KO) (Set.range w0) = X.thAll wL → (∀ k σ, Real.log (B.supN j wL σ (w0 k)) ≤ b) → a + b ≤ G * wL.size → (∃ Sh : Finset (B.Cusp j wL), Submodule.span (𝓞 B.KO) (Sh : Set (B.Cusp j wL)) = X.WWc S.sW wL ∧ ∃ mx : (B.KO →+* ℂ) → ℝ, (∀ σ, ∀ g ∈ Sh, Real.log (B.supN j wL σ g) ≤ mx σ) ∧ (∑ σ, mx σ) / (Fintype.card (B.KO →+* ℂ) : ℝ) ≤ G * wL.size) ∧ (X.WWc S.sW wL ≤ B.Mlat j wL → Real.log N ≤ Prw * (wL.size - 1) → ∃ Gd : EtaleWeightGaps.GlobalFamilyData X ka wL wF, Gd.TiedW S G Prw) := by
  classical
  intro D B P j X ka wL wF S N w0 a b G Prw ha hb hS hspan hsup hG

  set w : Fin N → B.Cusp j wL := fun k => (S.sW : B.KO) • w0 k with hw
  have hspanw : Submodule.span (𝓞 B.KO) (Set.range w) = X.WWc S.sW wL := span_scaled X wL S.sW w0 hspan

  have hbound : ∀ σ k, Real.log (B.supN j wL σ (w k)) ≤ a + b := by
    intro σ k
    have hmul : B.supN j wL σ (w k) = ‖σ (S.sW : B.KO)‖ * B.supN j wL σ (w0 k) := B.supN_smul j wL σ _ (w0 k)
    rw [hmul]
    by_cases hx : ‖σ (S.sW : B.KO)‖ = 0
    · rw [hx, zero_mul, Real.log_zero]
      linarith
    by_cases hy : B.supN j wL σ (w0 k) = 0
    · rw [hy, mul_zero, Real.log_zero]
      linarith
    rw [Real.log_mul hx hy]
    linarith [hS σ, hsup k σ]

  have hmean : (∑ _σ : B.KO →+* ℂ, (a + b)) / (Fintype.card (B.KO →+* ℂ) : ℝ) ≤ G * wL.size := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rcases Nat.eq_zero_or_pos (Fintype.card (B.KO →+* ℂ)) with h0 | h0
    · rw [h0, Nat.cast_zero, zero_mul, zero_div]
      linarith
    · have hc : (Fintype.card (B.KO →+* ℂ) : ℝ) ≠ 0 := by positivity
      rw [mul_div_cancel_left₀ _ hc]
      exact hG
  refine ⟨⟨Finset.univ.image w, ?_, fun _ => a + b, ?_, hmean⟩, ?_⟩
  · rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    exact hspanw
  · intro σ g hg
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hg
    exact hbound σ k
  · intro hM hN

    refine ⟨{
        N := N
        w := w
        del := 0
        th' := fun i => Fin.elim0 i
        rz := 0
        alz := fun i => Fin.elim0 i
        th0 := fun i => Fin.elim0 i
        zc := fun i => Fin.elim0 i
        rq := 0
        th := fun i => Fin.elim0 i
        iet := 0
        et := 0
        mx := fun _ => a + b }, ?_⟩
    refine ⟨hspanw, ?_, hN, fun σ k => hbound σ k, hmean⟩
    intro k
    apply hM
    rw [← hspanw]
    exact Submodule.subset_span (Set.mem_range_self k)

end GlobalTheory.ScaledGenerators
end

section

open NumberField

namespace GlobalTheory.DataClassCount

open scoped nonZeroDivisors
open Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HermModel

variable {E : Type} [Field E] [NumberField E]

theorem mem_of_forall_mul_smul {V : Type} [AddCommGroup V] [Module E V]
    (AA : Submodule (𝓞 E) E) (hfg : AA.FG) (h0 : AA ≠ ⊥) (N : AddSubmonoid V) (v : V)
    (h : ∀ a ∈ AA, ∀ b : E, (∀ c ∈ AA, ∃ o : 𝓞 E, (o : E) = b * c) → (a * b) • v ∈ N) :
    v ∈ N := by
  let I : FractionalIdeal (𝓞 E)⁰ E := ⟨AA, FractionalIdeal.isFractional_of_fg hfg⟩
  have hI : I ≠ 0 := fun h => h0 ((congrArg FractionalIdeal.coeToSubmodule h).trans
    FractionalIdeal.coe_zero)
  have h1 : (1 : E) ∈ I * I⁻¹ := by
    rw [mul_inv_cancel₀ hI]
    exact FractionalIdeal.one_mem_one _
  have key : ∀ r ∈ I * I⁻¹, r • v ∈ N := by
    intro r hr
    refine FractionalIdeal.mul_induction_on (C := fun r => r • v ∈ N) hr ?_ ?_
    · intro a ha b hb
      refine h a ha b fun c hc => ?_
      exact (FractionalIdeal.mem_one_iff _).1 ((FractionalIdeal.mem_inv_iff hI).1 hb c hc)
    · intro x y hx hy
      rw [add_smul]
      exact N.add_mem hx hy
  simpa using key 1 h1

def divLat {r : ℕ} (AA : Submodule (𝓞 E) E) (M : Submodule (𝓞 E) (Fin r → E)) :
    Submodule (𝓞 E) (Fin r → E) where
  carrier := {v | ∀ a ∈ AA, a • v ∈ M}
  add_mem' := fun hx hy a ha => by
    rw [smul_add]; exact M.add_mem (hx a ha) (hy a ha)
  zero_mem' := fun a _ => by rw [smul_zero]; exact M.zero_mem
  smul_mem' := fun c x hx a ha => by
    rw [smul_comm]; exact M.smul_mem c (hx a ha)

theorem smul_mem_divLat {r : ℕ} {AA : Submodule (𝓞 E) E} {M : Submodule (𝓞 E) (Fin r → E)}
    {v : Fin r → E} (hv : v ∈ M) {b : E} (hb : ∀ c ∈ AA, ∃ o : 𝓞 E, (o : E) = b * c) :
    b • v ∈ divLat AA M := by
  intro a ha
  obtain ⟨o, ho⟩ := hb a ha
  rw [smul_smul, mul_comm, ← ho]
  exact M.smul_mem o hv

theorem mem_iff_divLat {r : ℕ} {AA : Submodule (𝓞 E) E} (hfg : AA.FG) (h0 : AA ≠ ⊥)
    (M : Submodule (𝓞 E) (Fin r → E)) (v : Fin r → E) :
    v ∈ M ↔ ∀ b : E, (∀ c ∈ AA, ∃ o : 𝓞 E, (o : E) = b * c) → b • v ∈ divLat AA M := by
  refine ⟨fun hv b hb => smul_mem_divLat hv hb, fun h => ?_⟩
  refine mem_of_forall_mul_smul AA hfg h0 M.toAddSubmonoid v fun a ha b hb => ?_
  rw [mul_smul]
  exact h b hb a ha

theorem isLattice_divLat {r : ℕ} {AA : Submodule (𝓞 E) E} (hfg : AA.FG) (h0 : AA ≠ ⊥)
    {M : Submodule (𝓞 E) (Fin r → E)} (hM : M.FG)
    (hs : Submodule.span E (M : Set (Fin r → E)) = ⊤) :
    ReciprocityTheory.MultiplicativeHeights.IsLattice (divLat AA M) := by
  constructor
  · obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
    let f : (Fin r → E) →ₗ[𝓞 E] (Fin r → E) := (LinearMap.lsmul E (Fin r → E) a).restrictScalars _
    have hf : Function.Injective f := smul_right_injective _ ha0
    apply Submodule.fg_of_fg_map_injective f hf
    haveI : IsNoetherian (𝓞 E) M := isNoetherian_of_fg_of_noetherian M hM
    refine Submodule.FG.of_le_of_isNoetherian (T := M) ?_
    rintro _ ⟨v, hv, rfl⟩
    exact hv a ha
  · apply top_unique
    rw [← hs]
    rw [Submodule.span_le]
    intro v hv
    apply mem_of_forall_mul_smul AA hfg h0 (Submodule.span E (divLat AA M : Set (Fin r → E))).toAddSubmonoid v
    intro a ha b hb
    rw [mul_smul]
    exact Submodule.smul_mem _ a (Submodule.subset_span (smul_mem_divLat hv hb))
variable [IsCMField E]

theorem herm_smul_smul {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (ξ a b : E) (x y : Fin r → E) :
    ξ * FD.herm G (a • x) (b • y) = ξ * FD.herm G x y * a * FD.cc b := by
  rw [herm_smul_left, herm_smul_right]; ring

theorem selfDual_divLat {r : ℕ} {AA : Submodule (𝓞 E) E} (hfg : AA.FG) (h0 : AA ≠ ⊥) (ξ : E)
    (hA : ∀ x : E, (∀ a ∈ AA, ∀ b ∈ AA, ∃ z : ℤ, Algebra.trace ℚ E (ξ * x * a * FD.cc b) = z) ↔
      IsIntegral ℤ x) (G : Matrix (Fin r) (Fin r) E) {M : Submodule (𝓞 E) (Fin r → E)}
    (hM : ∀ v, (∀ y ∈ M, ∃ n : ℤ, Algebra.trace ℚ E (ξ * FD.herm G v y) = n) ↔ v ∈ M) :
    (∀ x ∈ divLat AA M, ∀ y ∈ divLat AA M, IsIntegral ℤ (FD.herm G x y)) ∧
      ∀ x, (∀ y ∈ divLat AA M, IsIntegral ℤ (FD.herm G x y)) → x ∈ divLat AA M := by
  constructor
  · intro x hx y hy
    refine (hA _).1 fun a ha b hb => ?_
    rw [← herm_smul_smul]
    exact (hM _).2 (hx a ha) _ (hy b hb)
  · intro x hx a ha
    refine (hM _).1 fun y hy => ?_
    let N : AddSubmonoid (Fin r → E) :=
      { carrier := {y | ∃ n : ℤ, Algebra.trace ℚ E (ξ * FD.herm G (a • x) y) = n}
        add_mem' := by
          rintro u w ⟨n, hn⟩ ⟨k, hk⟩
          refine ⟨n + k, ?_⟩
          rw [herm_add_right, mul_add, map_add (f := _), hn, hk]
          push_cast; rfl
        zero_mem' := ⟨0, by rw [herm_zero_right]; simp⟩ }
    refine mem_of_forall_mul_smul AA hfg h0 N y fun a' ha' b hb => ?_
    change ∃ n : ℤ, _
    rw [mul_smul, herm_smul_smul]
    exact (hA _).2 (hx _ (smul_mem_divLat hy hb)) a ha a' ha'

theorem exists_isometry {H : Host E} (D D' : Datum H) {r : ℕ} (ξ : E)
    (G : Matrix (Fin r) (Fin r) E) (φ : D.La →ₗ[𝓞 E] (Fin r → E))
    (φ' : D'.La →ₗ[𝓞 E] (Fin r → E)) (hφ : Function.Injective φ) (hφ' : Function.Injective φ')
    (hE : ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm G (φ x) (φ y)))
    (hE' : ∀ x y, ((D'.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm G (φ' x) (φ' y)))
    (g : (Fin r → E) ≃ₗ[E] (Fin r → E)) (hg : ∀ x y, FD.herm G (g x) (g y) = FD.herm G x y)
    (hm : ∀ x, x ∈ LinearMap.range φ ↔ g x ∈ LinearMap.range φ') :
    ∃ gam : D.La ≃ₗ[𝓞 E] D'.La, ∀ a b, D'.EF (gam a) (gam b) = D.EF a b := by
  have hmap : (LinearMap.range φ).map
      ((g.restrictScalars (𝓞 E) : (Fin r → E) ≃ₗ[𝓞 E] (Fin r → E)) :
        (Fin r → E) →ₗ[𝓞 E] (Fin r → E)) = LinearMap.range φ' := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hm x).1 hx
    · intro hy
      refine ⟨g.symm y, (hm _).2 (by rwa [g.apply_symm_apply]), g.apply_symm_apply y⟩
  let gam : D.La ≃ₗ[𝓞 E] D'.La := ((LinearEquiv.ofInjective φ hφ).trans
    (LinearEquiv.ofSubmodules (g.restrictScalars (𝓞 E)) _ _ hmap)).trans
      (LinearEquiv.ofInjective φ' hφ').symm
  have hgam : ∀ a, φ' (gam a) = g (φ a) := fun a =>
    congrArg Subtype.val ((LinearEquiv.ofInjective φ' hφ').apply_symm_apply _)
  refine ⟨gam, fun a b => ?_⟩
  have : ((D'.EF (gam a) (gam b) : ℤ) : ℚ) = D.EF a b := by
    rw [hE', hE, hgam, hgam, hg]
  exact_mod_cast this

end GlobalTheory.DataClassCount

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory


open DataClassCount in
theorem card_nonisometric_data_le : GlobalTheory.Published.HasseNormSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (p q r : ℕ), r = p + q → ∀ (ξ : E) (AA : Submodule (𝓞 E) E), FD.cc ξ = -ξ → ξ ≠ 0 → AA.FG → AA ≠ ⊥ → (∀ x : E, (∀ a ∈ AA, ∀ b ∈ AA, ∃ z : ℤ, Algebra.trace ℚ E (ξ * x * a * FD.cc b) = z) ↔ IsIntegral ℤ x) → ∀ (m : ℕ) (Di : Fin m → Datum H), (∀ i, (Di i).p = p ∧ (Di i).q = q) → (∀ i j (gam : (Di i).La ≃ₗ[𝓞 E] (Di j).La), (∀ a b, (Di j).EF (gam a) (gam b) = (Di i).EF a b) → i = j) → (m : ℝ) ≤ (1 + 2 * max 1 ((2 * FD.fdeg E * r : ℝ) ^ 4 * FD.dE E ^ 2 / (4 * FD.fdeg E))) ^ (2 * FD.fdeg E * r ^ 2) * (r * max 1 ((2 * FD.fdeg E * r : ℝ) ^ 4 * FD.dE E ^ 2 / (4 * FD.fdeg E))) ^ (2 * FD.fdeg E * r ^ 2) := by
  intro hH E _ _ _ H p q r hr ξ AA hξ hξ0 hfg h0 hA m Di hpq hne
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [Nat.cast_zero]
    positivity
  let i0 : Fin m := ⟨0, hm⟩
  obtain ⟨G, φ0, hM0⟩ := GlobalTheory.exists_herm_coord_of_datum E H (Di i0) ξ hξ hξ0 r
    (by rw [(hpq i0).1, (hpq i0).2, hr])
  have hex := fun i => GlobalTheory.model_in_same_space (GlobalTheory.LocalQuad.landherrSt_of_hasseNormSt hH) hH E H
    (Di i0) (Di i) r ξ G φ0 (by rw [(hpq i0).1, (hpq i).1]) (by rw [(hpq i0).2, (hpq i).2]) hξ hM0
  choose φ hφ using hex
  obtain ⟨S, -, hS, hcard, -⟩ := GlobalTheory.exists_finset_selfDual_classes_herm G hM0.2.2.1
  have hcl := fun i => by
    have h := GlobalTheory.HermModel.rank_integral_selfDual E H (Di i) r ξ G (φ i) hξ (hφ i)
    have hsd := selfDual_divLat hfg h0 ξ hA G (M := LinearMap.range (φ i)) fun v => by
      rw [← h.2.2.2 v]
      exact ⟨fun h y => h _ ⟨y, rfl⟩, by rintro h _ ⟨y, rfl⟩; exact h y⟩
    exact hS _ (isLattice_divLat hfg h0 h.2.1 (hφ i).2.1) hsd.1 hsd.2
  choose L hL γ hγ hmem using hcl
  refine le_trans ?_ hcard
  have hinj : Function.Injective L := by
    intro i j hij
    let g : ∀ k : Fin m, (Fin r → E) ≃ₗ[E] (Fin r → E) := fun k =>
      Matrix.toLin'OfInv (γ k).inv_mul (γ k).mul_inv
    have hg : ∀ k x y, FD.herm G (g k x) (g k y) = FD.herm G x y := hγ
    have hgm : ∀ k x, x ∈ L k ↔ g k x ∈ divLat AA (LinearMap.range (φ k)) := hmem
    obtain ⟨gam, hgam⟩ := exists_isometry (Di i) (Di j) ξ G (φ i) (φ j) (hφ i).1 (hφ j).1
      (hφ i).2.2.2.2 (hφ j).2.2.2.2 ((g i).symm.trans (g j))
      (fun x y => by
        rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, hg, ← hg i,
          LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply])
      (fun x => by
        rw [mem_iff_divLat hfg h0, mem_iff_divLat hfg h0]
        refine forall₂_congr fun b _ => ?_
        rw [← map_smul, LinearEquiv.trans_apply, ← hgm, ← hij, hgm, LinearEquiv.apply_symm_apply])
    exact hne i j gam hgam
  have := Finset.card_le_card_of_injOn (s := Finset.univ) (t := S) L (fun i _ => hL i) hinj.injOn
  rw [Finset.card_univ, Fintype.card_fin] at this
  exact_mod_cast this

end GlobalTheory
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory

theorem pageRows_of_le : ∀ (D : D7) (large₂ : SizeData₂ D) (j : ℕ) (ka w : WeightFamilies.Wt D j), 0 ≤ large₂.sc.L → WeightAlgebra.DF w ≤ WeightAlgebra.DF ka → w.n ≤ ka.n → ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ ka → ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w := by
  intro D large₂ j ka w hL hd hn h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, ?_, ?_⟩
  · refine le_trans (Real.log_le_log (by positivity) ?_) h8
    have : ((WeightAlgebra.DF w : ℕ) : ℝ) ≤ ((WeightAlgebra.DF ka : ℕ) : ℝ) := by exact_mod_cast hd
    linarith
  · rcases Nat.eq_zero_or_pos w.n with h0 | h0
    · rw [h0]; simpa using hL
    · exact le_trans (Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hn)) h9

end GlobalTheory
end
