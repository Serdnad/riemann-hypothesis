module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle018
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle017
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle022
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle023
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Topology.Germ
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle025
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.InnerProductSpace.OfNorm
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Polynomial.CauchyBound
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
import Mathlib.Tactic.TypeStar
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.Calculus.FDeriv.Basic

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem PrimitiveFormSheetedLocusCutOut.proof (hfac : PrimitiveFormFullRootFactor.Statement)
    (hiff : PrimitiveFormSheetedIffRootFull.Statement) : PrimitiveFormSheetedLocusCutOut.Statement := by
  intro σ _ X w d A hX hiso ℓ N a δ q ha hδ hq hδ0 hP hsep hQ
  obtain ⟨W, B, C, E, hW, hwW, hB, hwB, han, hCE, hroot⟩ :=
    hfac σ X w d A hX hiso ℓ N a δ q ha hδ hq hδ0 hP hsep hQ
  have hBn : ∀ᶠ z in 𝓝 w, A z ∈ B := A.continuous.continuousAt.preimage_mem_nhds (hB.mem_nhds hwB)
  have hc : ∀ F : (Fin d → ℂ) → ℂ → ℂ, AnalyticAt ℂ (fun u : (Fin d → ℂ) × ℂ => F u.1 u.2) (A w, ℓ w) →
      AnalyticAt ℂ (fun z => F (A z) (ℓ z)) w := fun F hF =>
    (show AnalyticAt ℂ (fun u : (Fin d → ℂ) × ℂ => F u.1 u.2) ((A.prod ℓ) w) from hF).comp
      ((A.prod ℓ).analyticAt w)
  refine ⟨fun z => C (A z) (ℓ z), fun z => E (A z) (ℓ z), hc C (han _ hwB _).1, hc E (han _ hwB _).2, ?_, ?_⟩
  · filter_upwards [hBn, hP] with z hz hPz hzX
    rw [hCE _ hz]
    exact hPz hzX
  · filter_upwards [hBn, hP, hiff σ X w d A ℓ N a δ q ha hδ hq hP hsep hQ, hW.mem_nhds hwW] with
      z hz hPz hsh hzW hzX hzδ
    have hr := hroot _ hz hzδ (ℓ z) (hPz hzX)
    have hs := hsh hzX hzδ W hW hzW
    exact ⟨hs.trans hr.1.symm, fun h h0 => hr.2.mp h0 (hs.mp h)⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem PrimitiveFormFullRootFactor.proof (hWin : PrimitiveFormWindow.Statement)
    (hBr : AnalyticRootBranch.Statement) (hConst : PrimitiveFormFullBranchConstant.Statement)
    (hFac : PolynomialRootPredicateFactor.Statement) : PrimitiveFormFullRootFactor.Statement := by
  intro σ _ X w d A hX hiso ℓ N a δ q ha hδ hq hδne hP hsep hQ
  obtain ⟨W, B, N', k, f, hWo, hwW, hBo, hBc, hAwB, hN'o, hcl, hf, hXN, hsph, hPW, -, haB, hδB, hqB,
    hsepB⟩ := hWin σ X w d A hX hiso ℓ N a δ q ha hδ hq hP hsep hQ
  have hex : ∃ t ∈ B, δ t ≠ 0 := by
    by_contra h
    push Not at h
    exact hδne (Filter.mem_of_superset (hBo.mem_nhds hAwB) h)
  have hloc : ∀ t₀ ∈ B, δ t₀ ≠ 0 → ∀ τ₀ : ℂ, τ₀ ^ N + ∑ j, a j t₀ * τ₀ ^ (j : ℕ) = 0 →
      ∃ (O : Set (Fin d → ℂ)) (r : (Fin d → ℂ) → ℂ), IsOpen O ∧ t₀ ∈ O ∧ ContinuousOn r O ∧ r t₀ = τ₀ ∧
        ∀ s ∈ O, r s ^ N + ∑ j, a j s * r s ^ (j : ℕ) = 0 ∧
          (PrimitiveFormRootFull X W A ℓ δ q s (r s) ↔ PrimitiveFormRootFull X W A ℓ δ q t₀ τ₀) := by
    intro t₀ ht₀ hδt₀ τ₀ hτ₀
    obtain ⟨O, r, hOo, ht₀O, hr, hrt₀, hroot⟩ :=
      hBr d N a t₀ τ₀ (fun j => haB j t₀ ht₀) (hsepB t₀ ht₀ hδt₀) hτ₀
    have hU : IsOpen (O ∩ (B ∩ δ ⁻¹' {0}ᶜ)) :=
      hOo.inter (hδB.continuousOn.isOpen_inter_preimage hBo isOpen_compl_singleton)
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU t₀ ⟨ht₀O, ht₀, hδt₀⟩
    have hsub : ∀ s ∈ Metric.ball t₀ ε, s ∈ O ∧ s ∈ B ∧ δ s ≠ 0 := fun s hs =>
      ⟨(hball hs).1, (hball hs).2.1, (hball hs).2.2⟩
    have hc := hConst σ X W N' k f d A ℓ N a δ q B (Metric.ball t₀ ε) r hWo hN'o hcl hf hXN hsph hPW hBo
      haB hδB hqB Metric.isOpen_ball (convex_ball t₀ ε).isPreconnected (fun s hs => (hsub s hs).2.1)
      (fun s hs => (hsub s hs).2.2) (fun s hs => hsepB s (hsub s hs).2.1 (hsub s hs).2.2)
      (hr.mono fun s hs => (hsub s hs).1) (fun s hs => hroot s (hsub s hs).1)
    refine ⟨Metric.ball t₀ ε, r, Metric.isOpen_ball, Metric.mem_ball_self hε,
      hr.continuousOn.mono fun s hs => (hsub s hs).1, hrt₀, fun s hs => ⟨hroot s (hsub s hs).1, ?_⟩⟩
    rw [← hrt₀]
    exact hc s hs t₀ (Metric.mem_ball_self hε)
  obtain ⟨C, E, hCE, hprod, hzero⟩ :=
    hFac d N B a δ (PrimitiveFormRootFull X W A ℓ δ q) hBo hBc haB hδB hex hsepB hloc
  exact ⟨W, B, C, E, hWo, hwW, hBo, hAwB, hCE, hprod, hzero⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology

theorem NormalRiemannExtension.proof (hloc : NormalRiemannExtensionLocal.Statement)
    (hirr : NormalLocallyIrreducible.Statement) : NormalRiemannExtension.Statement := by
  intro σ _ I h U f hI hIc hh hU hf hb
  classical
  have hex : ∀ w ∈ zeroSetIn I ∩ U, ∃ V : Set (σ → ℂ), IsOpen V ∧ w ∈ V ∧ V ⊆ U ∧
      ∃ F : (σ → ℂ) → ℂ, DifferentiableOn ℂ F V ∧
        Set.EqOn F f ((zeroSetIn I ∩ V) \ {z | eval z h = 0}) := fun w hw =>
    hloc σ I h w U f hI hIc hh hw.1 (hU.mem_nhds hw.2) hf hb
  choose! V hVo hwV hVU F hF hFf using hex

  have hagree : ∀ w ∈ zeroSetIn I ∩ U, ∀ y ∈ zeroSetIn I ∩ U, y ∈ V w → F y y = F w y := by
    intro w hw y hy hyw
    have hWo : IsOpen (V y ∩ V w) := (hVo y hy).inter (hVo w hw)
    obtain ⟨B, -, hyB, hBW, -, hdense⟩ :=
      hirr σ I h y hI hIc hh hy.1 (V y ∩ V w) (hWo.mem_nhds ⟨hwV y hy, hyw⟩)
    set S := (zeroSetIn I ∩ B) \ {z | eval z h = 0}
    have hSW : insert y S ⊆ V y ∩ V w :=
      Set.insert_subset_iff.2 ⟨⟨hwV y hy, hyw⟩, fun z hz => hBW hz.1.2⟩
    have heq : Set.EqOn (F y) (F w) S := fun z hz => by
      have hzW := hBW hz.1.2
      rw [hFf y hy ⟨⟨hz.1.1, hzW.1⟩, hz.2⟩, hFf w hw ⟨⟨hz.1.1, hzW.2⟩, hz.2⟩]
    exact heq.of_subset_closure ((hF y hy).continuousOn.mono fun z hz => (hSW hz).1)
      ((hF w hw).continuousOn.mono fun z hz => (hSW hz).2) (Set.subset_insert y S)
      (Set.insert_subset_iff.2 ⟨hdense ⟨hy.1, hyB⟩, subset_closure⟩) (Set.mem_insert y S)
  refine ⟨fun z => if z ∈ zeroSetIn I ∩ U then F z z else f z, ?_, ?_⟩
  · intro w hw
    refine ⟨V w, hVo w hw, hwV w hw, F w, hF w hw, fun y hy => ?_⟩
    simp only [if_pos hy.1]
    exact hagree w hw y hy.1 hy.2
  · intro z hz
    simp only [if_pos hz.1]
    exact hFf z hz.1 ⟨⟨hz.1.1, hwV z hz.1⟩, hz.2⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology Filter RealInnerProductSpace

theorem eq_of_sum_eq_nsmul_of_norm_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {m : ℕ}
    (a : Fin m → E) (c : E) (hle : ∀ j, ‖a j‖ ≤ ‖c‖) (hsum : ∑ j, a j = m • c) (j : Fin m) :
    a j = c := by
  have hj : ∀ i, ⟪c, a i⟫ ≤ ‖c‖ ^ 2 := fun i =>
    (real_inner_le_norm c (a i)).trans
      (by rw [sq]; exact mul_le_mul_of_nonneg_left (hle i) (norm_nonneg c))
  have htot : ∑ i, ⟪c, a i⟫ = m * ‖c‖ ^ 2 := by
    rw [← inner_sum, hsum, ← Nat.cast_smul_eq_nsmul ℝ, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sub_nonneg.2 (hj i))).1
    (by rw [Finset.sum_sub_distrib, htot, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, sub_self]) j (Finset.mem_univ j)
  have hsq : ‖a j - c‖ ^ 2 ≤ 0 := by
    rw [norm_sub_sq_real, real_inner_comm]
    nlinarith [hle j, norm_nonneg (a j), norm_nonneg c]
  exact sub_eq_zero.1 (norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1
    (le_antisymm hsq (sq_nonneg _))))

theorem NormalMaximumPrinciple.proof (htr : LocalTrace.Statement) : NormalMaximumPrinciple.Statement := by
  intro σ _ I w U g hI _ hw hU hg hle
  obtain ⟨k, A, B, D, m, T, hB, hwB, hBU, hD, hwD, hfib, hT, hrep⟩ := htr σ I w U g hI hw hU hg
  have hle' : ∀ z ∈ zeroSetIn I ∩ B, ‖g z‖ ≤ ‖g w‖ := fun z hz => hle z ⟨hz.1, hBU hz.2⟩

  have hTw : T (A w) = m • g w := by
    obtain ⟨x, hx, -, hTx⟩ := hrep (A w) hwD
    rw [hTx, Finset.sum_congr rfl fun j _ => congrArg g (hfib (x j) (hx j).1 (hx j).2),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin]

  have hmax : IsLocalMax (norm ∘ T) (A w) := by
    filter_upwards [hD.mem_nhds hwD] with y hy
    obtain ⟨x, hx, -, hTx⟩ := hrep y hy
    simp only [Function.comp_apply, hTx, hTw]
    calc ‖∑ j, g (x j)‖ ≤ ∑ j, ‖g (x j)‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin m, ‖g w‖ := Finset.sum_le_sum fun j _ => hle' _ (hx j).1
      _ = ‖m • g w‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; simp [nsmul_eq_mul]
  have hconst := Complex.eventually_eq_of_isLocalMax_norm
    (Filter.eventually_of_mem (hD.mem_nhds hwD) fun y hy =>
      (hT y hy).differentiableAt (hD.mem_nhds hy)) hmax
  have hcont : Tendsto A (𝓝 w) (𝓝 (A w)) := A.continuous.tendsto w
  filter_upwards [hB.mem_nhds hwB, hcont.eventually hconst, hcont.eventually (hD.mem_nhds hwD)]
    with z hzB hzT hzD hzZ
  obtain ⟨x, hx, hcov, hTx⟩ := hrep (A z) hzD
  obtain ⟨j, rfl⟩ := hcov z ⟨hzZ, hzB⟩ rfl
  exact eq_of_sum_eq_nsmul_of_norm_le (fun i => g (x i)) (g w) (fun i => hle' _ (hx i).1)
    (by rw [← hTx, hzT, hTw]) j

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Matrix

noncomputable section

def analyticAtSubring {σ : Type} [Fintype σ] (p : σ → ℂ) : Subring ((σ → ℂ) → ℂ) where
  carrier := {g | AnalyticAt ℂ g p}
  mul_mem' ha hb := AnalyticAt.mul ha hb
  one_mem' := analyticAt_const
  add_mem' ha hb := AnalyticAt.add ha hb
  zero_mem' := analyticAt_const
  neg_mem' ha := AnalyticAt.neg ha

theorem mem_analyticAtSubring {σ : Type} [Fintype σ] {p : σ → ℂ} {g : (σ → ℂ) → ℂ} :
    g ∈ analyticAtSubring p ↔ AnalyticAt ℂ g p :=
  Iff.rfl

def analyticAtComp {σ τ : Type} [Fintype σ] [Fintype τ] (x : σ → ℂ) (L : (σ → ℂ) →L[ℂ] (τ → ℂ)) :
    analyticAtSubring (L x) →+* analyticAtSubring x where
  toFun g := ⟨fun z => (g : (τ → ℂ) → ℂ) (L z), AnalyticAt.comp g.2 (L.analyticAt x)⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def analyticAtEval {σ : Type} [Fintype σ] (p y : σ → ℂ) : analyticAtSubring p →+* ℂ :=
  (Pi.evalRingHom (fun _ : σ → ℂ => ℂ) y).comp (analyticAtSubring p).subtype

@[simp] theorem analyticAtEval_apply {σ : Type} [Fintype σ] (p y : σ → ℂ) (g : analyticAtSubring p) :
    analyticAtEval p y g = (g : (σ → ℂ) → ℂ) y :=
  rfl

def analyticAtGerm {σ : Type} [Fintype σ] (p : σ → ℂ) : analyticAtSubring p →+* holGerms p :=
  ((Germ.coeRingHom (𝓝 p)).comp (analyticAtSubring p).subtype).codRestrict (holGerms p)
    fun g => ⟨g, g.2, rfl⟩

theorem analyticAtGerm_eq_iff {σ : Type} [Fintype σ] {p : σ → ℂ} (a b : analyticAtSubring p) :
    analyticAtGerm p a = analyticAtGerm p b ↔ (a : (σ → ℂ) → ℂ) =ᶠ[𝓝 p] b := by
  rw [Subtype.ext_iff]
  exact Germ.coe_eq

theorem analyticAtGerm_surjective {σ : Type} [Fintype σ] (p : σ → ℂ) :
    Function.Surjective (analyticAtGerm p) := by
  rintro ⟨φ, g, hg, rfl⟩
  exact ⟨⟨g, hg⟩, rfl⟩

theorem det_eq_zero_of_mulVec_eq_zero {Q : Type*} [CommRing Q] {n : ℕ} (A : Matrix (Fin n) (Fin n) Q)
    (e β : Fin n → Q) (hA : A *ᵥ e = 0) (h1 : ∑ m, β m * e m = 1) : A.det = 0 := by
  have he : (A.adjugate * A) *ᵥ e = 0 := by
    rw [← Matrix.mulVec_mulVec, hA, Matrix.mulVec_zero]
  rw [Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec] at he
  calc A.det = A.det * ∑ m, β m * e m := by rw [h1, mul_one]
    _ = ∑ m, β m * (A.det * e m) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => by ring
    _ = 0 := Finset.sum_eq_zero fun m _ => by
      have := congrFun he m
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
      rw [this, mul_zero]

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

noncomputable section

def HolGermsUFD.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ), UniqueFactorizationMonoid (holGerms w)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

noncomputable def holGermIdeal {σ : Type} [Fintype σ] (w : σ → ℂ) {k : ℕ} (f : Fin k → (σ → ℂ) → ℂ) : Ideal (holGerms w) :=
  Ideal.span {φ | ∃ i, (φ : Germ (𝓝 w) ℂ) = (f i : Germ (𝓝 w) ℂ)}

def PrimeGermNullstellensatz.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ) (k : ℕ) (p : Fin k → (σ → ℂ) → ℂ) (g : (σ → ℂ) → ℂ),
    (∀ i, AnalyticAt ℂ (p i) w) → AnalyticAt ℂ g w → (holGermIdeal w p).IsPrime →
    (∀ᶠ z in 𝓝 w, (∀ i, p i z = 0) → g z = 0) →
    ∃ h : Fin k → (σ → ℂ) → ℂ, (∀ i, AnalyticAt ℂ (h i) w) ∧ ∀ᶠ z in 𝓝 w, g z = ∑ i, h i z * p i z

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

theorem isRoot_map_eval_of_mem_zeroSetIn {n m : ℕ} {I : Ideal (MvPolynomial (Fin n ⊕ Fin m) ℂ)}
    {w : Fin n ⊕ Fin m → ℂ} (hw : w ∈ zeroSetIn I) (i : Fin m) (P : Polynomial (MvPolynomial (Fin n) ℂ))
    (hP : P.eval₂ (rename Sum.inl : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n ⊕ Fin m) ℂ).toRingHom
      (X (Sum.inr i)) ∈ I) :
    (P.map (eval (firstCoords w))).IsRoot (w (Sum.inr i)) := by
  have h0 := hw _ hP
  rw [Polynomial.hom_eval₂, eval_X] at h0
  have hcomp : (eval w).comp
      (rename Sum.inl : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n ⊕ Fin m) ℂ).toRingHom =
      eval (firstCoords w) := by
    ext q
    · simp
    · simp [firstCoords]
  rw [hcomp, Polynomial.eval₂_eq_eval_map] at h0
  exact h0

theorem norm_lt_of_isRoot_map_eval {n : ℕ} {P : Polynomial (MvPolynomial (Fin n) ℂ)} (hPm : P.Monic)
    (x : Fin n → ℂ) {a : ℂ} (ha : (P.map (eval x)).IsRoot a) :
    ‖a‖ < 1 + ∑ j ∈ Finset.range P.natDegree, ‖eval x (P.coeff j)‖ := by
  have hQm : (P.map (eval x)).Monic := hPm.map _
  have hlt := Polynomial.IsRoot.norm_lt_cauchyBound hQm.ne_zero ha
  have hcb : Polynomial.cauchyBound (P.map (eval x)) ≤
      (∑ j ∈ Finset.range P.natDegree, ‖eval x (P.coeff j)‖₊) + 1 := by
    rw [Polynomial.cauchyBound, hQm.leadingCoeff, nnnorm_one, div_one, hPm.natDegree_map]
    gcongr
    refine Finset.sup_le fun j hj => ?_
    rw [Polynomial.coeff_map]
    exact Finset.single_le_sum (f := fun j => ‖eval x (P.coeff j)‖₊) (fun _ _ => zero_le) hj
  have h := hlt.trans_le hcb
  rw [← NNReal.coe_lt_coe, NNReal.coe_add, NNReal.coe_sum, coe_nnnorm, NNReal.coe_one] at h
  simp only [coe_nnnorm] at h
  linarith

theorem NormalModelProper.proof : NormalModelProper.Statement := by
  intro n J M K hK
  choose P hPm hP using M.integral
  set f : (Fin n → ℂ) → ℝ := fun x =>
    ∑ i, ∑ j ∈ Finset.range (P i).natDegree, ‖eval x ((P i).coeff j)‖ with hf
  have hfc : Continuous f := by
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact (MvPolynomial.continuous_eval _).norm
  obtain ⟨C, hC⟩ := hK.isCompact_closure.exists_bound_of_continuousOn hfc.continuousOn
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hK
  refine isBounded_iff_forall_norm_le.2 ⟨max R (1 + C), fun w hw => ?_⟩
  obtain ⟨hwZ, hwK⟩ := hw
  have hxR : ‖firstCoords w‖ ≤ R := hR _ hwK
  have hR0 : 0 ≤ max R (1 + C) := (norm_nonneg _).trans (hxR.trans (le_max_left _ _))
  refine (pi_norm_le_iff_of_nonneg hR0).2 fun s => ?_
  rcases s with j | i
  · exact ((norm_le_pi_norm (firstCoords w) j).trans hxR).trans (le_max_left _ _)
  · have hroot := isRoot_map_eval_of_mem_zeroSetIn hwZ i (P i) (hP i)
    have hlt := norm_lt_of_isRoot_map_eval (hPm i) (firstCoords w) hroot
    have hfi : ∑ j ∈ Finset.range (P i).natDegree, ‖eval (firstCoords w) ((P i).coeff j)‖ ≤
        f (firstCoords w) :=
      Finset.single_le_sum (f := fun i => ∑ j ∈ Finset.range (P i).natDegree,
        ‖eval (firstCoords w) ((P i).coeff j)‖) (fun i _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
        (Finset.mem_univ i)
    have hfC : f (firstCoords w) ≤ C := by
      have := hC _ (subset_closure hwK)
      exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using this)
    exact (hlt.le.trans (by linarith)).trans (le_max_right _ _)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology Filter

noncomputable section

def holGermValue {σ : Type} [Fintype σ] (w : σ → ℂ) : holGerms w →+* ℂ :=
  (Germ.valueRingHom (x := w)).comp (holGerms w).subtype

def holGermPointIdeal {σ : Type} [Fintype σ] (w : σ → ℂ) : Ideal (holGerms w) :=
  RingHom.ker (holGermValue w)

def polyPointIdeal {σ : Type} [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) :
    Ideal (MvPolynomial σ ℂ ⧸ I) :=
  (RingHom.ker (MvPolynomial.eval w)).map (Ideal.Quotient.mk I)

def germQuotPointIdeal {σ : Type} [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) :
    Ideal (holGerms w ⧸ I.map (polyGerm w)) :=
  (holGermPointIdeal w).map (Ideal.Quotient.mk _)

theorem holGermValue_polyGerm {σ : Type} [Fintype σ] (w : σ → ℂ) (q : MvPolynomial σ ℂ) :
    holGermValue w (polyGerm w q) = eval w q := rfl

theorem polyPointIdeal_isMaximal {σ : Type} [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ)
    (hw : w ∈ zeroSetIn I) : (polyPointIdeal I w).IsMaximal := by
  have hmax : (RingHom.ker (MvPolynomial.eval w)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ fun a => ⟨C a, eval_C a⟩
  have hle : I ≤ RingHom.ker (MvPolynomial.eval w) := fun q hq => RingHom.mem_ker.2 (hw q hq)
  refine (Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective hmax).resolve_left ?_
  intro htop
  have h := Ideal.comap_map_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective (RingHom.ker (MvPolynomial.eval w))
  rw [htop, Ideal.comap_top, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.2 hle] at h
  exact hmax.ne_top h.symm

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing

theorem LocalGeneratorsClearDenominators.polyOriginIdeal_isPrime : polyOriginIdeal.IsPrime :=
  polyOriginIdeal_isMaximal.isPrime

attribute [local instance] LocalGeneratorsClearDenominators.polyOriginIdeal_isPrime

def LocalGeneratorsClearDenominators.Statement : Prop :=
  ∀ (T : Type) [CommRing T] [IsNoetherianRing T] (P : Ideal T) [P.IsPrime] (h : ℕ) (f : Fin h → T),
    (∀ i, f i ∈ P) →
    maximalIdeal (Localization.AtPrime P) ≤
        Ideal.span (Set.range fun i => algebraMap T (Localization.AtPrime P) (f i)) ⊔
          maximalIdeal (Localization.AtPrime P) ^ 2 →
      ∃ s ∉ P, ∀ x ∈ P, s * x ∈ Ideal.span (Set.range f)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
