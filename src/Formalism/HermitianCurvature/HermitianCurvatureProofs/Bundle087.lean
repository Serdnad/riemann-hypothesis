module

public import Formalism.HermitianCurvature.Bundle004
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle076
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LetterPairStep
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle038
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle080
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle027
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheSection
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle047
import Mathlib.Algebra.Module.StablyFree.Basic
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle070
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDomainMeasurable
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle083
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RightTypeAction
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.WeakDominationWordBounds

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.SandwichRhoAction Formalism.FourierDecayAlt.P.ChartIntegralLocal Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet
  Formalism.FourierDecayAlt.P.LetterPairRecursion

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]

section
variable (D : RealPlaceData k r Wp Wq) {m : ℕ} {F : Mat k r → (Wq →L[ℂ] Wp)} (hFm : CkOn (m : ℕ∞) (GV k r) F)
    (hDom1 : ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) → u.length + v.length ≤ m →
      ∀ g ∈ Om k r D.z D.z',
        AEStronglyMeasurable (fun p => rho D p (dLR (u.map (AdL p)) (v.map (AdR p)) F) g) D.μSS)
    (hDom2 : ∀ K : Set (Mat k r), IsCompact K → K ⊆ Om k r D.z D.z' →
      ∃ b : SS k r → ℝ, Integrable b D.μSS ∧
        ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) →
          u.length + v.length ≤ m → ∀ g ∈ K, ∀ᵐ p ∂D.μSS,
            ‖rho D p (dLR (u.map (AdL p)) (v.map (AdR p)) F) g‖ ≤ b p)
include hFm hDom1 hDom2

lemma words_all :
    ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) → u.length + v.length ≤ m →
      ∀ g ∈ Om k r D.z D.z', dLR u v (JF D F) g = ∫ p, xiP D p • dLR u v (rho D p F) g ∂D.μSS := by
  have base : ∀ v : List (Mat k r), (∀ X ∈ v, unitLie k r X) → v.length ≤ m →
      ∀ g ∈ Om k r D.z D.z', dLR [] v (JF D F) g = ∫ p, xiP D p • dLR [] v (rho D p F) g ∂D.μSS := by
    intro v
    induction v with
    | nil => intro _ _ g _; rfl
    | cons X v ih =>
      intro hv hl
      have hv' : ∀ Y ∈ v, unitLie k r Y := fun Y hY => hv Y (List.mem_cons_of_mem _ hY)
      exact step_pair D hFm hDom1 hDom2 false (hv X List.mem_cons_self) (u := []) (v := v) (u2 := [])
        (v2 := X :: v) (by simp) hv' (by simp) hv (by simpa using hl) (by simp) (fun f => rfl)
        (ih hv' (by simp at hl; omega))
  intro u
  induction u with
  | nil => intro v _ hv hl; exact base v hv (by simpa using hl)
  | cons X u ih =>
    intro v hu hv hl
    have hu' : ∀ Y ∈ u, unitLie k r Y := fun Y hY => hu Y (List.mem_cons_of_mem _ hY)
    exact step_pair D hFm hDom1 hDom2 true (hu X List.mem_cons_self) (u := u) (v := v) (u2 := X :: u) (v2 := v)
      hu' hv hu hv hl (by simp) (fun f => rfl) (ih v hu' hv (by simp at hl; omega))

lemma ck_all : Formalism.FourierDecayAlt.Q.CkLev k r 0 m (Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z') (JF D F) := by
  classical
  haveI : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  intro g0 hg0
  have hg0G : g0 ∈ GV k r := hg0.1.1
  have hchart0 : Formalism.FourierDecayAlt.P.Ux10.chart g0 0 = g0 := by
    have h1 : (0 : Formalism.FourierDecayAlt.P.Ux10.J k r → ℝ) = Formalism.FourierDecayAlt.P.Ux10.co 0 :=
      funext fun i => (Formalism.FourierDecayAlt.P.Ux10.co_zero i).symm
    unfold Formalism.FourierDecayAlt.P.Ux10.chart Formalism.FourierDecayAlt.P.Ux10.kap
    rw [h1, Formalism.FourierDecayAlt.P.Ux10.Mv_co, Formalism.FourierDecayAlt.P.Ux10.prj_zero]
    simp
  have hcont : ContinuousAt (Formalism.FourierDecayAlt.P.Ux10.chart g0) 0 :=
    (Formalism.FourierDecayAlt.P.Ux10.chart_diff g0 Formalism.FourierDecayAlt.P.Ux10.zero_mem_dom).continuousAt
  have hV : Formalism.FourierDecayAlt.P.Ux10.Dom k r ∩ Formalism.FourierDecayAlt.P.Ux10.chart g0 ⁻¹' Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z' ∈
      𝓝 (0 : Formalism.FourierDecayAlt.P.Ux10.J k r → ℝ) :=
    Filter.inter_mem (Formalism.FourierDecayAlt.P.Ux10.dom_open.mem_nhds Formalism.FourierDecayAlt.P.Ux10.zero_mem_dom)
      (hcont.preimage_mem_nhds ((isOpen_OmPlus _ _).mem_nhds (by rw [hchart0]; exact hg0.2)))
  obtain ⟨δ1, hδ1, hsub⟩ := Metric.mem_nhds_iff.1 hV
  set δ := δ1 / 2 with hδ
  have hδp : 0 < δ := by rw [hδ]; linarith
  have hclb : Metric.closedBall (0 : Formalism.FourierDecayAlt.P.Ux10.J k r → ℝ) δ ⊆ Metric.ball 0 δ1 :=
    Metric.closedBall_subset_ball (by rw [hδ]; linarith)
  have hcl : Metric.closedBall (0 : Formalism.FourierDecayAlt.P.Ux10.J k r → ℝ) δ ⊆ Formalism.FourierDecayAlt.P.Ux10.Dom k r :=
    fun Y hY => (hsub (hclb hY)).1
  set K := Formalism.FourierDecayAlt.P.Ux10.chart g0 '' Metric.closedBall (0 : Formalism.FourierDecayAlt.P.Ux10.J k r → ℝ) δ with hKdef
  have hK : IsCompact K :=
    (isCompact_closedBall _ _).image_of_continuousOn ((Formalism.FourierDecayAlt.P.Ux10.chart_cd g0).continuousOn.mono hcl)
  have hKOm : K ⊆ Om k r D.z D.z' := by
    rintro _ ⟨Y, hY, rfl⟩
    exact (⟨Formalism.FourierDecayAlt.P.Ux10.chart_mem hg0G (hcl hY), (hsub (hclb hY)).2⟩ :
      Formalism.FourierDecayAlt.P.Ux10.chart g0 Y ∈ GV k r ∩ Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z')
  have hKG : K ⊆ GV k r := fun x hx => (show x ∈ GV k r ∩ Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z' from hKOm hx).1
  have hmemK : ∀ Y ∈ Metric.ball (0 : Formalism.FourierDecayAlt.P.Ux10.J k r → ℝ) δ, Formalism.FourierDecayAlt.P.Ux10.chart g0 Y ∈ K :=
    fun Y hY => ⟨Y, Metric.ball_subset_closedBall hY, rfl⟩
  obtain ⟨bd, hbdI, hbd⟩ := hDom2 K hK hKOm
  set WS : Set (List (Mat k r) × List (Mat k r)) :=
    (fun w : List (Formalism.FourierDecayAlt.P.Ux10.J k r) => (w.map Formalism.FourierDecayAlt.P.Ux10.Lt, ([] : List (Mat k r)))) ''
      {w | w.length ≤ m} with hWSdef
  have hWS : WS.Countable := (Set.to_countable _).image _
  have hunit : ∀ w : List (Formalism.FourierDecayAlt.P.Ux10.J k r), ∀ X ∈ w.map Formalism.FourierDecayAlt.P.Ux10.Lt, unitLie k r X := by
    intro w X hX
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hX
    exact Formalism.FourierDecayAlt.P.Ux10.Lt_unit i
  have hWSl : ∀ uv ∈ WS, (∀ Y ∈ uv.1, unitLie k r Y) ∧ (∀ Y ∈ uv.2, unitLie k r Y) ∧
      uv.1.length + uv.2.length ≤ m := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨hunit w, by simp, by simpa using hw⟩
  have good := good_set D hFm hK hKG hWS hWSl bd fun uv huv g' hg' =>
    hbd uv.1 uv.2 (hWSl uv huv).1 (hWSl uv huv).2.1 (hWSl uv huv).2.2 g' hg'
  set P0 : Set (SS k r) := {p | D.inSS p ∧ ∀ uv ∈ WS, ∀ g' ∈ K, ‖dLR uv.1 uv.2 (rho D p F) g'‖ ≤ bd p} with hP0
  have goodae : ∀ᵐ p ∂D.μSS, p ∈ P0 := good
  set hK' : SS k r → Mat k r → (Wq →L[ℂ] Wp) := fun p => if p ∈ P0 then rho D p F else fun _ => 0 with hK'def
  have hsel : ∀ p (u' v' : List (Mat k r)),
      dLR u' v' (hK' p) = if p ∈ P0 then dLR u' v' (rho D p F) else fun _ => 0 := by
    intro p u' v'
    by_cases hp : p ∈ P0
    · simp only [hK'def, if_pos hp]
    · simp only [hK'def, if_neg hp, dLR_zero]
  have hAL := int_chart_loc (xiP D) (fun p => norm_xiP D p) (continuous_xiP D).aestronglyMeasurable hK' m
    (fun p => by
      by_cases hp : p ∈ P0
      · simp only [hK'def, if_pos hp]; exact ckOn_rho D hp.1 hFm
      · simp only [hK'def, if_neg hp]; exact ckOn_zero _)
    hg0G hδp hcl
    (fun w hw Y hY => by
      refine (hDom1 (w.map Formalism.FourierDecayAlt.P.Ux10.Lt) [] (hunit w) (by simp) (by simpa using hw) _
        (hKOm (hmemK Y hY))).congr ?_
      filter_upwards [goodae] with p hp
      rw [hsel, if_pos hp, dLR_rho D hp.1])
    (fun p => ‖bd p‖) hbdI.norm
    (fun w hw Y hY p => by
      rw [hsel]
      by_cases hp : p ∈ P0
      · rw [if_pos hp]; exact (hp.2 _ ⟨w, hw, rfl⟩ _ (hmemK Y hY)).trans (Real.le_norm_self _)
      · rw [if_neg hp, norm_zero]; exact norm_nonneg _)
  have hAL' : ContDiffOn ℝ ((m : ℕ) : WithTop ℕ∞) (fun Y => JF D F (Formalism.FourierDecayAlt.P.Ux10.chart g0 Y))
      (Metric.ball 0 δ) := by
    refine hAL.congr fun Y _ => ?_
    show ∫ p, xiP D p • rho D p F _ ∂D.μSS = _
    refine integral_congr_ae ?_
    filter_upwards [goodae] with p hp
    simp only [hK'def, if_pos hp]
  obtain ⟨U, F', hU, hgU, hF', hUF⟩ := ck_at_of_chart hg0G hδp hAL'
  exact ⟨U, F', hU, hgU, hF', fun g hg hgl => hUF g hg hgl.1⟩

end

theorem _root_.Formalism.FourierDecayAlt.P.bessel_words_of_domain : JWordsOfDom := by
  intro hDom k r Wp Wq _ _ _ _ _ _ D A m F hThr hCC
  obtain ⟨hDom1, hDom2⟩ := hDom k r Wp Wq D A m F hThr hCC
  obtain ⟨c, hc⟩ := hCC
  have hFm : CkOn (m : ℕ∞) (GV k r) F := hc.1
  have hW := words_all D hFm hDom1 hDom2
  refine ⟨ck_all D hFm hDom1 hDom2, fun u v hu hv hl g hg => ?_⟩
  obtain ⟨bd, hbdI, hbd⟩ := hDom2 {g} isCompact_singleton (Set.singleton_subset_iff.2 hg)
  have hb := hbd u v hu hv hl g (Set.mem_singleton g)
  refine ⟨hbdI.norm.mono' ((continuous_xiP D).aestronglyMeasurable.smul (hDom1 u v hu hv hl g hg)) ?_, ?_⟩
  · filter_upwards [hb] with p hp
    rw [norm_smul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_xiP D p)).trans (hp.trans (Real.le_norm_self _))
  · rw [hW u v hu hv hl g hg]
    refine integral_congr_ae ?_
    filter_upwards [Formalism.FourierDecayAlt.P.B7.ae_inSS D] with p hp
    rw [dLR_rho D hp]

end Formalism.FourierDecayAlt.P.WeakDominationWordBounds
end
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

def BsAt {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (μ0 : ℂ → Matrix (Fin (P.k + 1)) (Fin (P.k + 1)) ℂ) (h0 : IsSection P.k P.r Bs.z Bs.z' μ0) :
    B.RealPlaceData P.k P.r Wp Wq :=
  { Bs with μsec := μ0, sec := h0 }

def GTRMove : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k →
    ∀ (μ0 : ℂ → Matrix (Fin (P.k + 1)) (Fin (P.k + 1)) ℂ) (h0 : IsSection P.k P.r Bs.z Bs.z' μ0)
      (e0 : M.Ty P → ℂ → (Wq →L[ℂ] Wp)), IsFrameB P (BsAt P Bs μ0 h0) e0 →
      ∃ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e ∧
        ∀ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π', trR P Bs e Φ = trR P (BsAt P Bs μ0 h0) e0 Φ

def GTRConst : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∃ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e ∧ KapF P Bs d e ∧
      ∀ ρ (ζ ζ' : ℂ), e ρ ζ = e ρ ζ'

def GTRRot : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → Bs.μsec = TheSec.theSection P.k P.r Bs.z Bs.z' →
    ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e → (∀ ρ (ζ ζ' : ℂ), e ρ ζ = e ρ ζ') →
    ∀ (Rt : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) (s : ℤ),
      (∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z',
        (Rt Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
          (∑ a : Fin (Q.mdim P.k P.r (Fin.last P.r)),
            Q.EH P.k P.r (Q.posL P.k P.r (Fin.last P.r) a) (Q.posL P.k P.r (Fin.last P.r) a)
              ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1) x.2) +
            ((s : ℂ)) • (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2) →
      ∀ ρ : M.Ty P, ∃ m : ℤ, ∀ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
        trR P Bs e (Rt Φ) ρ = fnZ P (fun w => w) * dzQ P (trR P Bs e Φ ρ) -
          fnZ P (fun w => star w) * dzbQ P (trR P Bs e Φ ρ) + ((m : ℂ)) • trR P Bs e Φ ρ

def GTRInt : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ)
    (π : Q.Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Q.Mx P.k P.r → (Wq →L[ℂ] Wq)),
    Q.IsPlace P z z' π π' → 2 ≤ P.k → ∀ ρ : M.Ty P, ∃ n : ℤ, uSum P - rhoSum P ρ = n

def GTRTrans : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e →
      ∀ A B : M.Ty P → ℂ → ℂ, SmAB P A B → ConnF P Bs d e A B → ∀ (ρ : M.Ty P) (m : ℂ),
        (∀ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
          trR P Bs e ((ThetaNF P d).1 Φ) ρ = fnZ P (fun w => w) * dzQ P (trR P Bs e Φ ρ) -
            fnZ P (fun w => star w) * dzbQ P (trR P Bs e Φ ρ) + m • trR P Bs e Φ ρ) →
        ∀ ζ ∈ Ann P, ζ * A ρ ζ + star ζ * B ρ ζ =
          m + ((-rhoSum P ρ + P.TT * (uSum P - 2 * rhoSum P ρ) / (Complex.normSq ζ - P.TT) : ℝ) : ℂ)

theorem poly_coeff_zero {V : Type*} [AddCommGroup V] [Module ℂ V] (N : ℕ) (a : ℕ → V)
    (h : ∀ Y : ℂ, ∑ j ∈ Finset.range N, Y ^ j • a j = 0) : ∀ j < N, a j = 0 := by
  intro j hj
  refine (Module.forall_dual_apply_eq_zero_iff ℂ (a j)).mp ?_
  intro f
  have hp0 : (∑ i ∈ Finset.range N, Polynomial.C (f (a i)) * Polynomial.X ^ i : Polynomial ℂ) = 0 := by
    apply Polynomial.funext
    intro Y
    have hY := congrArg f (h Y)

    simp only [map_sum, map_smul, smul_eq_mul, map_zero] at hY
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_zero]
    rw [← hY]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  have hc := congrArg (fun q => q.coeff j) hp0
  simpa [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hj] using hc

theorem poly_coeff_eq {V : Type*} [AddCommGroup V] [Module ℂ V] (N : ℕ) (a b : ℕ → V)
    (h : ∀ Y : ℂ, ∑ j ∈ Finset.range N, Y ^ j • a j = ∑ j ∈ Finset.range N, Y ^ j • b j) :
    ∀ j < N, a j = b j := by
  intro j hj
  have hz : ∀ Y : ℂ, ∑ i ∈ Finset.range N, Y ^ i • (a - b) i = 0 := by
    intro Y
    simp only [Pi.sub_apply, smul_sub, Finset.sum_sub_distrib, h Y, sub_self]
  exact sub_eq_zero.mp (poly_coeff_zero N (a - b) hz j hj)

theorem pr_fst_smul {V : Type*} [AddCommGroup V] [Module ℂ V] (Y : ℂ) (x : Q.Pr V) : (Y • x).1 = Y • x.1 := by
  rw [Algebra.smul_def, Algebra.smul_def]
  rfl

theorem pr_fst_add {V : Type*} [AddCommGroup V] [Module ℂ V] (x y : Q.Pr V) : (x + y).1 = x.1 + y.1 := rfl

theorem pr_fst_one {V : Type*} [AddCommGroup V] [Module ℂ V] : (1 : Q.Pr V).1 = 1 := rfl

theorem pr_fst_sum {V : Type*} [AddCommGroup V] [Module ℂ V] (s : Finset ℕ) (f : ℕ → Q.Pr V) :
    (∑ j ∈ s, f j).1 = ∑ j ∈ s, (f j).1 := Prod.fst_sum

theorem final_arith (P : M.Par) (ρ : M.Ty P) (A ζ : ℂ) (hζ : P.TT < Complex.normSq ζ) (m N : ℤ)
    (hN : uSum P - rhoSum P ρ = N)
    (hA : ζ * A + star ζ * star A =
      (m : ℂ) + ((-rhoSum P ρ + P.TT * (uSum P - 2 * rhoSum P ρ) / (Complex.normSq ζ - P.TT) : ℝ) : ℂ)) :
    (ζ * (modA P ρ ζ - A)).re = ((N - m : ℤ) : ℝ) / 2 := by
  have hpos : 0 < Complex.normSq ζ - P.TT := sub_pos.mpr hζ
  have haC : M.aC P ρ = uSum P / 2 - rhoSum P ρ := rfl
  have hre := congrArg Complex.re hA
  have h1 : (ζ * A + star ζ * star A).re = 2 * (ζ * A).re := by
    rw [← star_mul', Complex.add_re, Complex.star_def, Complex.conj_re]; ring
  rw [h1, Complex.add_re, Complex.intCast_re, Complex.ofReal_re] at hre
  have h2 : ζ * modA P ρ ζ = ((M.aC P ρ * Complex.normSq ζ / (Complex.normSq ζ - P.TT) : ℝ) : ℂ) := by
    unfold modA
    rw [Complex.star_def]
    push_cast
    rw [← Complex.mul_conj]
    field_simp
  rw [mul_sub, Complex.sub_re, h2, Complex.ofReal_re, haC]
  have hA' : (ζ * A).re = ((m : ℝ) + (-rhoSum P ρ + P.TT * (uSum P - 2 * rhoSum P ρ) / (Complex.normSq ζ - P.TT))) / 2 := by
    linarith
  rw [hA']
  push_cast
  rw [← hN]
  field_simp
  ring

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section

noncomputable section

namespace Formalism.FourierDecayAlt.P

theorem jf_jDom_of_nnMaj : Formalism.FourierDecayAlt.P.JFxDs2.NNMaj → Formalism.FourierDecayAlt.JF.JDom := fun h =>
  Formalism.FourierDecayAlt.P.JFxDs2.jDom_of_parts Formalism.FourierDecayAlt.P.JFxDs3.bessel_domain_measurable (Formalism.FourierDecayAlt.P.JFxDs2.jDomBound_of_nnMaj h)

theorem jf_jConv_of_nnMaj : Formalism.FourierDecayAlt.P.JFxDs2.NNMaj → Formalism.FourierDecayAlt.JF.JConv := fun h =>
  Formalism.FourierDecayAlt.P.JFxDs1.jConv_of_jDom (jf_jDom_of_nnMaj h)

end Formalism.FourierDecayAlt.P
end
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def ebM (k r : ℕ) (v b : Fin (2 * r + k + 1) → ℂ) : B.Mat k r :=
  Matrix.of fun p q => v p * herm (Hpk k r) (bvec q) b

section tht

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def sandw (A : Wp →L[ℂ] Wp) (B' : Wq →L[ℂ] Wq) : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) :=
  (ContinuousLinearMap.compL ℂ Wq Wp Wp A).comp ((ContinuousLinearMap.compL ℂ Wq Wq Wp).flip B')

def tht (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : B.Mat k r → (Wp →L[ℂ] Wp)) (π' : B.Mat k r → (Wq →L[ℂ] Wq))
    (Bw Bw' : Fin k → Fin (2 * r + k + 1) → ℂ) (a a' : Fin (2 * r + k + 1) → ℂ) (ι : B.Mat k r) :
    (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) :=
  ∑ p, ∑ q, herm (Hpk k r) (ι *ᵥ Bw' q) (Bw p) •
    sandw (QrD.ecOp π (ebM k r (Bw p) (SSn.prWv k r z a))) (QrD.ecOp π' (ebM k r (SSn.prWv k r z' a') (Bw' q)))

def thtA (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : B.Mat k r → (Wp →L[ℂ] Wp)) (π' : B.Mat k r → (Wq →L[ℂ] Wq))
    (Bw Bw' : Fin k → Fin (2 * r + k + 1) → ℂ) (a a' : Fin (2 * r + k + 1) → ℂ) (ι : B.Mat k r) :
    (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) :=
  ∑ p, ∑ q, conj (herm (Hpk k r) (ι *ᵥ Bw' q) (Bw p)) •
    sandw (QrD.ecOp π (ebM k r (SSn.prWv k r z a) (Bw p))) (QrD.ecOp π' (ebM k r (Bw' q) (SSn.prWv k r z' a')))

end tht

def ThtFacts : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' →
    ∀ Bw Bw' : Fin P.k → Fin (2 * P.r + P.k + 1) → ℂ, Q.IsFrameOf P.k P.r [Bs.z] Bw → Q.IsFrameOf P.k P.r [Bs.z'] Bw' →
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : (Fin (2 * P.r + P.k + 1) → ℂ) × (Fin (2 * P.r + P.k + 1) → ℂ) ×
          B.Mat P.k P.r => tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' x.1 x.2.1 x.2.2) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : (Fin (2 * P.r + P.k + 1) → ℂ) × (Fin (2 * P.r + P.k + 1) → ℂ) ×
          B.Mat P.k P.r => thtA P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' x.1 x.2.1 x.2.2) ∧
      (∀ a a' ι A B', B.hsInner (tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' a a' ι A) B' =
        B.hsInner A (thtA P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' a a' ι B')) ∧
      (∀ h ∈ UWset P.k P.r Bs.z, ∀ h' ∈ UWset P.k P.r Bs.z', ∀ a a' ι X,
        tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (h *ᵥ a) (h' *ᵥ a') (h * ι * h'⁻¹)
            ((Bs.π h).comp (X.comp (Bs.π' h'⁻¹))) =
          (Bs.π h).comp ((tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' a a' ι X).comp (Bs.π' h'⁻¹)) ∧
        thtA P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (h *ᵥ a) (h' *ᵥ a') (h * ι * h'⁻¹)
            ((Bs.π h).comp (X.comp (Bs.π' h'⁻¹))) =
          (Bs.π h).comp ((thtA P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' a a' ι X).comp (Bs.π' h'⁻¹))) ∧
      ∀ (c : ℂ) a a' ι, tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (c • a) (conj c • a') ι =
        (conj c) ^ 2 • tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' a a' ι

def DatumUnit : Prop :=
  ∀ (Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ), BuiltOW Cc S T f χ ν' m₀ top A₀ → ∀ (v : Fin S.f) (ζ : ℂ), (D.parOf S v).TT < Complex.normSq ζ →
      SSn.prWv S.G.k S.G.r (T v).base.z (SSn.nu0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ) =
          SSn.nu0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ ∧
        herm (Hpk S.G.k S.G.r) (SSn.nu0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ)
          (SSn.nu0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ) = 1 ∧
        SSn.prWv S.G.k S.G.r (T v).base.z' (SSn.nu0' S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ) =
          SSn.nu0' S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ ∧
        herm (Hpk S.G.k S.G.r) (SSn.nu0' S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ)
          (SSn.nu0' S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ) = 1

def ThtGaugeConst : Prop :=
  ∀ (Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ) (v : Fin S.f) (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))),
    PRho.Hyp Cc S T f χ ν' m₀ top A₀ v e → 2 ≤ S.G.k → ∀ l ∈ Finset.Icc 1 (S.G.k - 1),
    ∀ Bw Bw' : Fin S.G.k → Fin (2 * S.G.r + S.G.k + 1) → ℂ,
      Q.IsFrameOf S.G.k S.G.r [(T v).base.z] Bw → Q.IsFrameOf S.G.k S.G.r [(T v).base.z'] Bw' →
      ∃ κ : M.Ty (D.parOf S v) → ℂ, ∀ ζ : ℂ, (D.parOf S v).TT < Complex.normSq ζ → ∀ π ρ : M.Ty (D.parOf S v),
        M.Up (D.parOf S v) l π ρ →
        κ π * inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec (tht S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' Bw Bw'
          (SSn.nu0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ)
          (SSn.nu0' S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ)
          (SSn.io0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ) (e π ζ))) =
          ((Real.sqrt (M.Nrm (D.parOf S v) l π) : ℝ) : ℂ)

def SSnRepOfCut : Prop :=
  PRho.PRhoExists → PRho.GaugeLines → ThtFacts → DatumUnit → ThtGaugeConst → SSnRep

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep
end
