module

public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle031
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle039
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle028
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLevelBlockOfEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DetOfTriangular
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsIntegralCc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.BiextCoeffSecondLinear
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.HStable
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle007

@[expose] public section

section

open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem algTens_pr_single_lev :
    ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool)
      (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)]
      [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s))
      (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (μ : Fin n → ℝ) (kk j : ℕ) (bv : ℝ)
      (w : M), IsMod ε E μ → (∀ s, IsMod ε (F s) (μ - Pi.single s 1)) → AlgTens ε E N F io pr →
      Shape ε kk μ bv → j ≤ 4 * n ^ 2 → Lev ε E μ j w →
      ∀ c s, Lev ε (F s) (μ - Pi.single s 1) (j + 2) (pr s (Pi.single c w)) := by
  intro M _ _ n ε E N _ _ F io pr μ kk j bv w hE hF hT hS _ hw c s
  obtain ⟨hlow, hsq⟩ := GlobalTheory.T.lowK_sub_single_sqrt_ckv_le n kk ε μ bv s hS
  obtain ⟨hw1, hw2⟩ := hw
  have h0 : 0 ≤ Real.sqrt (ckv ε (lowK ε μ)) + 4 * (n : ℝ) * (j : ℝ) := by positivity
  refine ⟨?_, ?_⟩
  · obtain ⟨S, hS1, hS2, hS3, hS4⟩ :=
      GlobalTheory.T.compactCasimirBound_projection_dualTensor M n ε E N F io pr _ w hE.2.1 (fun s => (hF s).2.1) hT h0 hw1 s c
    refine ⟨S, hS1, hS2, hS3, fun x hx => (hS4 x hx).trans ?_⟩
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply pow_le_pow_left₀ (add_nonneg h0 (Real.sqrt_nonneg _))
    push_cast
    linarith
  · have h1 := (GlobalTheory.T.wtNear_pr_and_io_of_algTens M n ε E N F io pr (lowK ε μ) (j : ℝ) hT).1 w hw2 s c
    refine wtNear_le_of_add_dist_le (N s) n ε (F s) _ _ _ _ ?_ h1
    have h2 : ∑ a, |lowK ε μ a - lowK ε (μ - Pi.single s 1) a| = 1 := by
      rw [hlow, Finset.sum_eq_single s]
      · simp
      · intro b _ hb
        simp [Pi.single_eq_of_ne hb]
      · simp
    rw [h2]
    push_cast
    linarith

end GlobalTheory
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix

namespace GlobalTheory.TraceIsometry

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


open NumberField in
open scoped Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.TraceIsometry.eq_or_eq_neg_of_norm_eq {x y : E} (hx : _root_.ReciprocityTheory.ChartRestriction.G.FD.cc x = -x) (hy : _root_.ReciprocityTheory.ChartRestriction.G.FD.cc y = -y)
    (h : ∀ τ : E →+* ℂ, ‖τ x‖ = ‖τ y‖) : y = x ∨ y = -x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hre : ∀ z : E, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc z = -z → (τ z).re = 0 := by
    intro z hz
    have h1 := _root_.GlobalTheory.PerMove.map_cc τ z
    rw [hz, map_neg] at h1
    have h2 := congrArg Complex.re h1
    simp only [Complex.neg_re, Complex.conj_re] at h2
    linarith
  have hxr := hre x hx
  have hyr := hre y hy
  have key : (τ y).im = (τ x).im ∨ (τ y).im = -(τ x).im := by
    have h2 : ‖τ x‖ ^ 2 = ‖τ y‖ ^ 2 := by rw [h τ]
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply, hxr,
      hyr] at h2
    exact mul_self_eq_mul_self_iff.mp (by linarith)
  rcases key with k | k
  · left
    apply τ.injective
    apply Complex.ext <;> simp [hxr, hyr, k]
  · right
    apply τ.injective
    rw [map_neg]
    apply Complex.ext <;> simp [hxr, hyr, k]


open NumberField in
open scoped Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.TraceIsometry.exists_gl_of_trace_isometry : ∀ (E : Type) [Field E] [NumberField E]
    [IsCMField E] (r : ℕ) (X X' : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r), (∀ τ : E →+* ℂ, ‖τ X.ξ0‖ = ‖τ X'.ξ0‖) →
    ∀ (gam : X.Λ ≃ₗ[𝓞 E] X'.Λ), (∀ u v : X.Λ, Algebra.trace ℚ E (-X'.ξ0 * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X'.Gm
    (gam u : Fin r → E) (gam v : Fin r → E)) = Algebra.trace ℚ E (-X.ξ0 * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm
    (u : Fin r → E) (v : Fin r → E))) → ∃ (a : GL (Fin r) E) (ε : E), (ε = 1 ∨ ε = -1) ∧
    X'.ξ0 = ε * X.ξ0 ∧ (∀ v : X.Λ, (a : Matrix (Fin r) (Fin r) E) *ᵥ (v : Fin r → E) =
    (gam v : Fin r → E)) ∧ (∀ v, v ∈ X.Λ ↔ (a : Matrix (Fin r) (Fin r) E) *ᵥ v ∈ X'.Λ) ∧
    ∀ u v, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X'.Gm ((a : Matrix (Fin r) (Fin r) E) *ᵥ u)
    ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) = ε * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm u v := by
  intro E _ _ _ r X X' hξ gam hgam
  obtain ⟨ε, hε1, hεξ⟩ : ∃ ε : E, (ε = 1 ∨ ε = -1) ∧ X'.ξ0 = ε * X.ξ0 := by
    rcases _root_.GlobalTheory.TraceIsometry.eq_or_eq_neg_of_norm_eq X.ξ0_im X'.ξ0_im hξ with h | h
    · exact ⟨1, Or.inl rfl, by rw [h, one_mul]⟩
    · exact ⟨-1, Or.inr rfl, by rw [h, neg_one_mul]⟩
  have hsp : ∀ Y : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r, Submodule.span E (Set.range Y.Λ.subtype) = ⊤ := by
    intro Y
    have : Set.range Y.Λ.subtype = (Y.Λ : Set (Fin r → E)) := by ext; simp
    rw [this]
    exact Y.Λ_span
  obtain ⟨A, hA⟩ := _root_.GlobalTheory.FrameFibre.exists_matrix X.Λ.subtype
    Subtype.val_injective (hsp X) (X'.Λ.subtype ∘ₗ gam.toLinearMap)
  obtain ⟨B, hB⟩ := _root_.GlobalTheory.FrameFibre.exists_matrix X'.Λ.subtype
    Subtype.val_injective (hsp X') (X.Λ.subtype ∘ₗ gam.symm.toLinearMap)
  have hA' : ∀ v : X.Λ, A *ᵥ (v : Fin r → E) = (gam v : Fin r → E) := fun v => hA v
  have hB' : ∀ w : X'.Λ, B *ᵥ (w : Fin r → E) = (gam.symm w : Fin r → E) := fun w => hB w
  have hBA : B * A = 1 := by
    have hlin : Matrix.mulVecLin (B * A) = LinearMap.id := by
      apply LinearMap.ext_on X.Λ_span
      intro v hv
      simp only [Matrix.mulVecLin_apply, LinearMap.id_apply]
      rw [← Matrix.mulVec_mulVec, show A *ᵥ v = _ from hA' ⟨v, hv⟩, hB']
      simp
    apply Matrix.ext_of_mulVec_single
    intro i
    have h1 := LinearMap.congr_fun hlin (Pi.single i 1)
    simp only [Matrix.mulVecLin_apply, LinearMap.id_apply] at h1
    rw [h1, Matrix.one_mulVec]
  have hsm : ∀ (G : Matrix (Fin r) (Fin r) E) (c : 𝓞 E) (x y : Fin r → E),
      _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G (c • x) y = (c : E) * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G x y := by
    intro G c x y
    have h1 := _root_.GlobalTheory.FrameFibre.herm_smul_smul G (c : E) 1 x y
    rw [one_smul, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc_one, mul_one] at h1
    rw [← h1]
    rfl
  have hL : ∀ u v : X.Λ, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X'.Gm (A *ᵥ (u : Fin r → E)) (A *ᵥ (v : Fin r → E)) =
      ε * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm u v := by
    intro u v
    have hD : -X'.ξ0 * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X'.Gm (gam u) (gam v) - -X.ξ0 * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm u v = 0 := by
      apply _root_.GlobalTheory.FrameFibre.eq_zero_of_trace
      intro c
      have h1 := hgam (c • u) v
      rw [LinearEquiv.map_smul, Submodule.coe_smul, Submodule.coe_smul, hsm, hsm] at h1
      rw [mul_sub, map_sub, sub_eq_zero, mul_left_comm (c : E), mul_left_comm (c : E)]
      exact h1
    rw [hεξ, ← hA' u, ← hA' v] at hD
    have hε2 : ε * ε = 1 := by rcases hε1 with h | h <;> rw [h] <;> ring
    apply mul_left_cancel₀ X.ξ0_ne
    linear_combination (-ε) * hD -
      X.ξ0 * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X'.Gm (A *ᵥ (u : Fin r → E)) (A *ᵥ (v : Fin r → E)) * hε2
  have hall : ∀ u v : Fin r → E, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X'.Gm (A *ᵥ u) (A *ᵥ v) = ε * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm u v := by
    intro u v
    obtain ⟨c, u', hc, hu'⟩ := _root_.GlobalTheory.FrameFibre.exists_smul_eq X.Λ.subtype (hsp X) u
    obtain ⟨d, v', hd, hv'⟩ := _root_.GlobalTheory.FrameFibre.exists_smul_eq X.Λ.subtype (hsp X) v
    have h1 := hL u' v'
    have hu'' : (u' : Fin r → E) = (c : E) • u := hu'.symm
    have hv'' : (v' : Fin r → E) = (d : E) • v := hv'.symm
    rw [hu'', hv'', Matrix.mulVec_smul, Matrix.mulVec_smul, _root_.GlobalTheory.FrameFibre.herm_smul_smul,
      _root_.GlobalTheory.FrameFibre.herm_smul_smul] at h1
    have hc' : (c : E) ≠ 0 := by exact_mod_cast hc
    have hd' : (d : E) ≠ 0 := by exact_mod_cast hd
    have hcc : _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (d : E) ≠ 0 := by
      intro h0
      apply hd'
      rw [← _root_.ReciprocityTheory.ChartRestriction.G.FD.cc_cc (d : E), h0, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc_zero]
    apply mul_left_cancel₀ (mul_ne_zero hc' hcc)
    linear_combination h1
  refine ⟨⟨A, B, (mul_eq_one_comm.mp hBA), hBA⟩, ε, hε1, hεξ, hA', ?_, hall⟩
  intro v
  change v ∈ X.Λ ↔ A *ᵥ v ∈ X'.Λ
  constructor
  · intro hv
    rw [show A *ᵥ v = _ from hA' ⟨v, hv⟩]
    exact (gam ⟨v, hv⟩).2
  · intro hv
    have h1 : B *ᵥ (A *ᵥ v) = v := by rw [Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec]
    rw [← h1, show B *ᵥ (A *ᵥ v) = _ from hB' ⟨A *ᵥ v, hv⟩]
    exact (gam.symm _).2

end GlobalTheory.TraceIsometry
end

section

set_option autoImplicit false

open MvPowerSeries NumberField TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.TB (dAct bilinPart)

namespace GlobalTheory

theorem bilinPart_canonGauge_congr : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → (∀ i j, ((bilinPart k h)ᵀ - bilinPart k h) i j ∈ (algebraMap R k).range) ∧ (∀ a : O, (∀ i j, ((dAct k B a)ᵀ * bilinPart k h - bilinPart k h * dAct k B (star a)) i j ∈ (algebraMap R k).range)) ∧ (∀ a : O, (∀ i j, (dAct k B a) i j ∈ (algebraMap R k).range)) ∧ dAct k B 1 = 1 ∧ (∀ a b : O, dAct k B (a + b) = dAct k B a + dAct k B b) ∧ ∀ a b : O, dAct k B (a * b) = dAct k B a * dAct k B b := by
  intro R _ d O _ _ k _ _ _ B h hc
  refine ⟨fun i j => ?_, fun a i j => ?_, fun a i j => ?_, ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.dAct_one k B,
    ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.dAct_add k B, ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.dAct_mul k B⟩
  · have e := congrArg (coeff (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1)) hc.sy
    rw [ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_expS_two _ (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_swap_sub_low h hc.ax0 hc.ax1) _
      (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.degree_xz i j), map_sub, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_ev_swap', coeff_map,
      Finsupp.embDomain_add, Finsupp.embDomain_single, Finsupp.embDomain_single, add_comm (Finsupp.single (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.swE d _) 1)] at e
    exact ⟨_, e⟩
  · obtain ⟨r, hr⟩ := ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.M_int B h hc a j i
    refine ⟨-r, ?_⟩
    rw [map_neg, hr]
    simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gaugeBilinearTerm_eq_neg_double_sum, bilinPart,
      neg_mul, Finset.sum_neg_distrib, mul_comm (dAct k B _ _ _)]
    ring
  · exact ⟨coeff (Finsupp.single ((0 : Fin 1), j) 1) (B.A.act a i), by
      unfold dAct FB.actK; rw [coeff_map]⟩

end GlobalTheory
end
