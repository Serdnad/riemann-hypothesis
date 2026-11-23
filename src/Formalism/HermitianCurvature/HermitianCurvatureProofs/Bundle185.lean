module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutDec
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyContinuousOn
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpLEqZeroOfEventually
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle098
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle177
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.QxChain
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HasFDerivAtFsvOther
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle179
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.StandardPairingDecay
public import Formalism.HermitianCurvature.Bundle006
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle115
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle128
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceCompactSupportCoefficient
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwoByOneBlock
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle122
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology

noncomputable section

theorem limTopN_of_decay : ∃ c₃ : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A b₀ : ℝ),
    c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤ A →
    B.CCle A 0 G b₀ → B.CkOn ⊤ (B.GV P.k P.r) G → LimTopN p nn G := by
  obtain ⟨c₃, hc₃⟩ := Formalism.FourierDecayAlt.P.PBE.vecV_cut_empty
  refine ⟨c₃, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p nn G A b₀ hA hG hGk γ hγ

  have hcut : ∀ (n : ℕ) (g : B.Mat P.k P.r),
      cutN P.k P.r n g = 1 - Formalism.FourierDecayAlt.P.JCx2.pdPsi ((n : ℝ) + 1) g := by
    intro n g
    rw [Formalism.FourierDecayAlt.P.JCx2.pdPsi, sub_sub_cancel]
    rfl
  have hv := hc₃ P.k P.r Wp Wq p.T.base p.ν' p.m₀ γ G A b₀ (fun n g => cutN P.k P.r n g) hA hG hGk hcut

  have key : ∃ K : ℂ, ∀ F : B.Mat P.k P.r → (Wq →L[ℂ] Wp), TBB.Ew p nn F (P.r + 1) [] γ =
      (K * B.hsInner (D.vecV p.T.base p.ν' p.m₀ F γ) (D.vecV p.T.base p.ν' p.m₀ F γ)).re := by
    refine ⟨?_, fun F => ?_⟩
    swap
    unfold TBB.Ew TBB.NP KB.Pl.RR D.RRplace
    rw [dite_eq_left ⟨hγ, hγ⟩, dite_eq_right (show ¬ (P.r + 1 ≤ P.r) by omega), if_pos rfl, if_pos rfl]
  obtain ⟨K, hK⟩ := key
  simp only [hK]
  have hs : Continuous (fun V : Wq →L[ℂ] Wp => B.hsVec V) := by
    unfold B.hsVec
    fun_prop
  have hcont : Continuous (fun V : Wq →L[ℂ] Wp => (K * B.hsInner V V).re) := by
    unfold B.hsInner
    exact Complex.continuous_re.comp (continuous_const.mul (hs.inner hs))
  exact (hcont.tendsto _).comp hv

theorem limTopN_cut_of_inCC : ∃ c₃ : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (p : KB.Pl P Wp Wq) (nn χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ),
    c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤ A₀ → C6.IsCut0 χ →
    (∀ m : ℕ, B.InCC A₀ m F) → B.CkOn ⊤ (B.GV P.k P.r) F →
    ∀ ε : ℝ, 0 < ε → LimTopN p nn (D.cutF p.T.base χ F ε) := by
  obtain ⟨c₃, hc₃⟩ := limTopN_of_decay
  refine ⟨c₃, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p nn χ F A₀ hA hχ hF hFk ε hε
  obtain ⟨b₀, hb₀⟩ := Formalism.FourierDecayAlt.P.PBE.cutF_inCC p.T.base hχ hF hε A₀ 0 (by simp)
  exact hc₃ Wp Wq P p nn (D.cutF p.T.base χ F ε) A₀ b₀ hA hb₀
    (Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF p.T.base hχ hFk ε)

end

end Formalism.FourierDecayAlt.P.CutBP
end

section

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerC

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB

section Ent

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]
variable {P : M.Par} {z z' : Fin (2 * P.r + P.k + 1) → ℂ} {π : Mx P.k P.r → (Wp →L[ℂ] Wp)}
  {π' : Mx P.k P.r → (Wq →L[ℂ] Wq)}

theorem site_lc (X : ActualOps P.k P.r z z' π π') {L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r}
    (hAL : IsActualLevel X L) (l : Fin P.r) :
    L.p l ∈ presAlg (lcSub P.k P.r z z' π π') ∧ L.c l ∈ presAlg (lcSub P.k P.r z z' π π') ∧
      L.ci l ∈ presAlg (lcSub P.k P.r z z' π π') := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hAL.1 l]; exact mkPair_mem_preservingAlgebra (op_lc X l 0) (neg_lc (op_lc X l 3))
  · rw [hAL.2.2.1 l]; exact mkPair_mem_preservingAlgebra (op_lc X l 1) (op_lc X l 4)
  · rw [hAL.2.2.2.1 l]; exact mkPair_mem_preservingAlgebra (op_lc X l 2) (op_lc X l 5)

theorem QQ_lc (X : ActualOps P.k P.r z z' π π') (Y : ℂ) (a b : Fin 2) :
    X.QQ Y a b ∈ presAlg (lcSub P.k P.r z z' π π') :=
  mkPair_mem_preservingAlgebra (t_lc X Y a b) (t_lc X (star Y) b a)

theorem RRi_lc (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (hD : IsData P z z' π π' X μ L st l0) (i : Fin (P.r + 1)) (w : List (Letter ℂ S))
    (hw : ∀ l ∈ w, star l.pt = l.pt) : RRi L st i w ∈ entSub (presAlg (lcSub P.k P.r z z' π π')) := by
  obtain ⟨-, -, hAL, hQQ, -⟩ := hD
  refine rrw_mem (QQi L st i) (QQi_mem L st _ i (fun Y _ a b => ?_) (fun l _ => site_lc X hAL l)) w hw
  rw [hQQ Y, Matrix.smul_apply]
  exact (presAlg (lcSub P.k P.r z z' π π')).smul_mem (QQ_lc X Y a b) _

end Ent

section G

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem int_lc (μ : Measure (Mt k r)) (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) {Φ Ψ : RadSp k r z z' π π'}
    (hΦ : Φ ∈ lcSub k r z z' π π') (hΨ : Ψ ∈ lcSub k r z z' π π') (c : Fin r → ℂ) :
    Integrable (fun g : Mt k r => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))
      ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))) μ := by
  by_cases hc : c ∈ OmX r
  · exact intOn_cpt μ hμ c hc Φ (lcSub_le_cptSub hΦ) Ψ (lcSub_le_cptSub hΨ)
  · have e : (fun g : Mt k r => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))
        ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))) = fun _ => 0 := by
      funext g
      rw [radSp_zero_off Φ (x := (c, Matrix.of g)) (fun h => hc h.1)]
      exact hsInner_zero_left _
    rw [e]; exact integrable_zero _ _ _

end G

section Form

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

theorem formIntG_herKc (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq) (hD : IsData P z z' π π' X μ L st l0) (hz : D.z = z) (hz' : D.z' = z')
    (hπ : D.π = π) (hπ' : D.π' = π') (w : List (Letter ℂ S)) (hw : WordOK P z z' π π' st l0 w)
    (i : Fin (P.r + 1)) (c : Fin P.r → ℂ) (x y : Ix S → RadSp P.k P.r z z' π π')
    (hx : InK (herKc S P z z' π π' L st l0 D i) x) (hy : InK (herKc S P z z' π π' L st l0 D i) y)
    (c' : Cf P.r i) (a : Ix S) :
    Integrable (fun g : Mt P.k P.r =>
      B.hsInner ((act (RRi L st i w) x a : Fn P.k P.r (Wq →L[ℂ] Wp)) (glue i c c') (Matrix.of g))
        ((y a : Fn P.k P.r (Wq →L[ℂ] Wp)) (glue i c c') (Matrix.of g))) μ := by
  have hle := herKc_le_lc (S := S) (st := st) (l0 := l0) X hD.2.2.1
    (fun F Φ hF hΦ => jfCptLocAll Wp Wq P z z' π π' D F Φ hD.1 hz hz' hπ hπ' hF hΦ) i
  have hRR := RRi_lc X μ L st l0 hD i w hw.1.2.1
  have hu : act (RRi L st i w) x a ∈ lcSub P.k P.r z z' π π' :=
    (lcSub P.k P.r z z' π π').sum_mem fun b _ => (hRR a b).1 _ (hle (hx b))
  exact int_lc μ hD.2.1 hu (hle (hy a)) _

def FormIntOuterCpt : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    ∀ w : List (Letter ℂ S), WordOK P z z' π π' st l0 w → ∀ (i : Fin (P.r + 1)) (c : Fin P.r → ℂ), c ∈ OmX P.r →
    ∀ x y : Ix S → RadSp P.k P.r z z' π π', InK (herKc S P z z' π π' L st l0 D i) x →
      InK (herKc S P z z' π π' L st l0 D i) y →
      Integrable (fun c' : Cf P.r i => ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
        ∑ a, pairAt μ (act (RRi L st i w) x a) (y a) (glue i c c'))

def StepDensCptAll : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    StepDens (S := S) P z z' π π' μ L st (herKc S P z z' π π' L st l0 D) l0

theorem stepFormCptAll_of (hSD : StepDensCptAll) (hFO : FormIntOuterCpt) : StepFormCptAll := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ'
  refine ⟨hSD Wp Wq S P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ', fun w hw i c hc x y hx hy => ⟨?_, ?_⟩⟩
  · exact fun c' a => formIntG_herKc P z z' π π' X μ L st l0 D hD hz hz' hπ hπ' w hw i c x y hx hy c' a
  · exact hFO Wp Wq S P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' w hw i c hc x y hx hy

theorem thmPActualCpt_of_outer (hSD : StepDensCptAll) (hFO : FormIntOuterCpt) : ThmPActualCpt :=
  thmPActualCpt_of_stepForm (stepFormCptAll_of hSD hFO)

end Form

end Formalism.FourierDecayAlt.P5.HerC
end
end

section

open Matrix
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

namespace Formalism.FourierDecayAlt.P.CutMP.TemperedBoundGL3

noncomputable section

variable {k r : ℕ}

def lr (hr : 1 ≤ r) : Fin r := ⟨r - 1, by omega⟩

theorem lr_succ (hr : 1 ≤ r) : (lr hr).succ = Fin.last r := Fin.ext (by simp [lr]; omega)

section Br1

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem br1 (hz : inWb k r z) (hz' : inWb k r z') {D : Set (Mx k r)} (hD : IsDom k r z z' 0 D)
    {J : Mx k r → (Wq →L[ℂ] Wp)} (hJ : J ∈ FFl k r z z' π π' 0 D) {c : Fin r → ℂ} (hc : c ∈ OmX r) (l : Fin r) :
    resG k r l.castSucc J c ∈ FFl k r z z' π π' l.castSucc (Qx6.Dcell D l.castSucc c) ∧
      IsDom k r z z' l.castSucc (Qx6.Dcell D l.castSucc c) :=
  ⟨(Formalism.FourierDecayAlt.P.restriction_good_family Wp Wq k r z z' π π' D hz hz' hD J hJ l.castSucc).2 c hc,
    Qx6.dom_Dcell Formalism.FourierDecayAlt.P.restriction_mem hz hz' hD l.castSucc c hc⟩

end Br1

theorem cell_preimage_mem_domain {D : Set (Mx k r)} {c : Fin r → ℂ} (l : Fin r) {g : Mx k r}
    (hg : wCell k r l.succ c * g ∈ D) : g ∈ Qx6.Dc1 l (Qx6.Dcell D l.castSucc c) c := by
  show wCell k r l.castSucc c * (w1 k r l (c l) * g) ∈ D
  rw [← Matrix.mul_assoc, ← Qx6.wCell_succ]
  exact hg

section Br2

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem br2 (l : Fin r) (Θ : (Mx k r → X) → (Mx k r → X)) (hS : Formalism.FourierDecayAlt.P5.SmulC Θ) (c : Fin r → ℂ)
    (hL : ∀ f : Mx k r → X,
      Θ (fun x => f (wCell k r l.castSucc c * x)) = fun x => Θ f (wCell k r l.castSucc c * x))
    (J : Mx k r → X) (g : Mx k r) :
    resG k r l.succ (Θ J) c g =
      ((‖c l‖ ^ (Mdim k r l - 1) : ℝ) : ℂ) • Θ (resG k r l.castSucc J c) (w1 k r l (c l) * g) := by
  rw [Qx6.resG_succ]
  show ((‖c l‖ ^ (Mdim k r l - 1) : ℝ) : ℂ) • resG k r l.castSucc (Θ J) c (w1 k r l (c l) * g) = _
  congr 1
  have e : resG k r l.castSucc J c =
      ((Qx6.gam k r l.castSucc c : ℝ) : ℂ) • fun x => J (wCell k r l.castSucc c * x) := by
    funext x
    rfl
  rw [e, hS, hL]
  rfl

end Br2

theorem unipotent_fixes_base_vector (l : Fin r) (a : ℂ) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) :
    w1 k r l a *ᵥ z = z := by
  have hl := l.isLt
  have ze : z (eI k r l) = 0 := hz _ (Or.inl (by simp [eI]))
  have zs : z (esI k r l) = 0 := hz _ (Or.inr (by simp [esI]; omega))
  funext p
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (Qx3.sw k l p)]
  · rw [Qx3.w1_apply, Qx3.sw_sw, if_pos rfl]
    rcases Qx3.tri l p with h | h | ⟨h1, h2⟩
    · subst h; rw [Qx3.sw_e, zs, ze, mul_zero]
    · subst h; rw [Qx3.sw_es, ze, zs, mul_zero]
    · rw [Qx3.sw_o l h1 h2, Qx3.dd_o l a h1 h2, one_mul]
  · intro q _ hq
    have : p ≠ Qx3.sw k l q := fun h => hq (by rw [h, Qx3.sw_sw])
    rw [Qx3.w1_apply, if_neg this, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem wCell_fix_wb (i : Fin (r + 1)) (c : Fin r → ℂ) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) :
    wCell k r i c *ᵥ z = z := by
  unfold wCell
  induction ((List.finRange r).filter fun a => a.val < i.val) with
  | nil => simp
  | cons a l ih => rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec, ih, unipotent_fixes_base_vector a _ hz]

theorem hermitian_invariant_unipotent (l : Fin r) {a : ℂ} (ha : a ≠ 0) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z)
    (x : Mx k r) (v : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) ((w1 k r l a * x) *ᵥ v) z = herm (Hpk k r) (x *ᵥ v) z := by
  rw [← Matrix.mulVec_mulVec]
  conv_lhs => rw [← unipotent_fixes_base_vector l a hz]
  exact Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH (Qx3.weyl_cell_mem_unitary l ha) _ _

theorem hermitian_invariant_cell_action (i : Fin (r + 1)) {c : Fin r → ℂ} (hc : c ∈ OmX r) {z : Fin (2 * r + k + 1) → ℂ}
    (hz : inWb k r z) (x : Mx k r) (v : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) ((wCell k r i c * x) *ᵥ v) z = herm (Hpk k r) (x *ᵥ v) z := by
  rw [← Matrix.mulVec_mulVec]
  conv_lhs => rw [← wCell_fix_wb i c hz]
  exact Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH (Formalism.FourierDecayAlt.P.PBF.prod_w1_mem_unitary_Hpk c hc _) _ _

end

end Formalism.FourierDecayAlt.P.CutMP.TemperedBoundGL3
end

section

open Matrix MeasureTheory Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBO

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.P5

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section cont

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem continuous_hsInner [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] :
    Continuous fun q : (Wq →L[ℂ] Wp) × (Wq →L[ℂ] Wp) => B.hsInner q.1 q.2 := by
  have hv : Continuous (fun A : Wq →L[ℂ] Wp => B.hsVec A) := by
    unfold B.hsVec
    exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => continuous_eval_const _)
  unfold B.hsInner
  exact (hv.comp continuous_snd).inner (hv.comp continuous_fst)

theorem radSp_contOn {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    {π' : Mx k r → (Wq →L[ℂ] Wq)} (Ψ : RadSp k r z z' π π') (c0 : Fin r → ℂ) {g : ℂ → Mx k r} {O : Set ℂ}
    (hO : IsOpen O) (hg : ContinuousOn g O) (hdom : ∀ ζ ∈ O, (c0, g ζ) ∈ DomR k r z z') :
    ContinuousOn (fun ζ => (Ψ : Fn k r (Wq →L[ℂ] Wp)) c0 (g ζ)) O := by
  intro ζ₀ hζ₀
  have hmem := Ψ.2
  obtain ⟨-, hs, -⟩ := hmem
  obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := hs (c0, g ζ₀) (hdom ζ₀ hζ₀)
  have hgA : ContinuousAt g ζ₀ := hg.continuousAt (hO.mem_nhds hζ₀)
  have hpA : ContinuousAt (fun ζ => ((c0, g ζ) : (Fin r → ℂ) × Mx k r)) ζ₀ :=
    continuousAt_const.prodMk hgA
  have hev : ∀ᶠ ζ in 𝓝 ζ₀, ζ ∈ O ∧ ((c0, g ζ) : (Fin r → ℂ) × Mx k r) ∈ U :=
    Filter.Eventually.and (hO.mem_nhds hζ₀) (hpA.preimage_mem_nhds (hU.mem_nhds hxU))
  have hFc : ContinuousAt F (c0, g ζ₀) := hF.continuousOn.continuousAt (hU.mem_nhds hxU)
  have hcomp : ContinuousAt (fun ζ => F (c0, g ζ)) ζ₀ :=
    ContinuousAt.comp (g := F) (f := fun ζ => ((c0, g ζ) : (Fin r → ℂ) × Mx k r)) hFc hpA
  refine (hcomp.congr ?_).continuousWithinAt
  filter_upwards [hev] with ζ hζ
  exact (hΦ (c0, g ζ) hζ.2 (hdom ζ hζ.1).2.1).symm

theorem topDens_contOn {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    {π' : Mx k r → (Wq →L[ℂ] Wq)} [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S]
    [DecidableEq S] (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (st : Fr.Start (Pr (RadSp k r z z' π π')))
    (w : List (Letter ℂ S)) (x y : Ix S → RadSp k r z z' π π') (c0 : Fin r → ℂ) {g : ℂ → Mx k r} {O : Set ℂ}
    (hO : IsOpen O) (hg : ContinuousOn g O) (hdom : ∀ ζ ∈ O, (c0, g ζ) ∈ DomR k r z z') :
    ContinuousOn (fun ζ => topDens L st w x y c0 (g ζ)) O := by
  have h1 : ∀ e, ContinuousOn (fun ζ => B.hsInner
      ((act ((Fr.ofWord L st w).d L * (Fr.ofWord L st w).F) x e : Fn k r (Wq →L[ℂ] Wp)) c0 (g ζ))
      ((act (Fr.ofWord L st w).F y e : Fn k r (Wq →L[ℂ] Wp)) c0 (g ζ))) O := by
    intro e
    have ha := radSp_contOn (act ((Fr.ofWord L st w).d L * (Fr.ofWord L st w).F) x e) c0 hO hg hdom
    have hb := radSp_contOn (act (Fr.ofWord L st w).F y e) c0 hO hg hdom
    have hc := continuous_hsInner.comp_continuousOn (ha.prodMk hb)
    exact hc
  have h2 := continuousOn_finsetSum Finset.univ (fun e _ => h1 e)
  refine h2.congr fun ζ _ => ?_
  unfold topDens
  rfl

end cont

theorem one_mem_UWset {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) : (1 : Mx k r) ∈ UWset k r z := by
  simp [UWset, UH]

theorem topContOn_of (hP : P5.ThmPActualCpt) (hHT : KB.HeadTop) : TopContOn := by
  intro Wp Wq _ _ _ _ _ _ P p F w h h' hh hh' Cb hθ hF hw
  obtain ⟨hl1, hlk, -⟩ := p.hl
  let jF : Fin (P.r + 1) := ⟨P.r, by omega⟩
  have hPl := Formalism.FourierDecayAlt.P.JCTx5.isPlace_lev P p.T jF p.hP
  obtain ⟨X⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist _ _ _ _ _ _ _ hPl
  obtain ⟨L, st, h1, h2, h3, h4, h5, h6⟩ := Formalism.FourierDecayAlt.P.level_start_actual _ _ _ _ _ _ _ hPl X p.l0
  obtain ⟨μ0, hμ0⟩ := Formalism.FourierDecayAlt.P.JCTx5.exists_haar_level_zero (Nat.sub_self P.r) (p.T.bs P.r)
  have hD : IsData (JC.parLev P jF) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π' X
      (μ0.map (Formalism.FourierDecayAlt.P.JCTx5.embL P.k (P.r - P.r))) L st p.l0 :=
    ⟨hPl, Formalism.FourierDecayAlt.P.JCTx5.haar_glev μ0 hμ0, h1, h2, h3, h4, h5, h6⟩
  set μ := μ0.map (Formalism.FourierDecayAlt.P.JCTx5.embL P.k (P.r - P.r)) with hμ
  obtain ⟨K, -, -, -, hJ⟩ := hP Wp Wq (Fin w.length) (JC.parLev P jF) _ _ _ _ X μ L st p.l0
    (p.T.bs jF) _ _ hD hl1 hlk rfl rfl rfl rfl le_rfl le_rfl
  have hcx : ∀ e, KB.CptCoef (p.T.bs P.r) (KB.slv p.T F P.r le_rfl w h hh.2 e) := fun e =>
    Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F P.r le_rfl w h hh hF e
  have hcx' : ∀ e, KB.CptCoef (p.T.bs P.r) (KB.slv p.T F P.r le_rfl w h' hh'.2 e) := fun e =>
    Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F P.r le_rfl w h' hh' hF e
  choose Φ hΦK hΦ using fun e => pic_cpt (p.T.bs P.r) (K 0) hJ (hcx e)
  choose Φ' hΦ'K hΦ' using fun e => pic_cpt (p.T.bs P.r) (K 0) hJ (hcx' e)
  have hHTx := hHT Wp Wq P p F w h h' hh hh' X μ L st Cb Φ Φ' hD hθ hF hw hΦ hΦ'
  have hTT : Tz P.k (P.r - P.r) (p.T.bs P.r).z * Tz P.k (P.r - P.r) (p.T.bs P.r).z' = P.T * P.T' := by
    have e1 := hPl.2.2.2.1
    have e2 := hPl.2.2.2.2.1
    exact congrArg₂ (· * ·) e1 e2
  let O : Set ℂ := {c : ℂ | P.T * P.T' < Complex.normSq c}
  have hO : IsOpen O := isOpen_lt continuous_const Complex.continuous_normSq
  let g : ℂ → Mx P.k (P.r - P.r) := fun ζ => B2.embWb P.k (P.r - P.r) ((p.T.bs P.r).μsec ζ)
  let c0 : Fin (P.r - P.r) → ℂ := fun _ => 1
  have hfacts : ∀ ζ ∈ O, g ζ ∈ B2.UWb P.k (P.r - P.r) ∧
      herm (Hpk P.k (P.r - P.r)) (g ζ *ᵥ (p.T.bs P.r).z') (p.T.bs P.r).z = ζ := by
    intro ζ hζ
    have hζ' : Tz P.k (P.r - P.r) (p.T.bs P.r).z * Tz P.k (P.r - P.r) (p.T.bs P.r).z' < Complex.normSq ζ := by rw [hTT]; exact hζ
    have := Formalism.FourierDecayAlt.P.b2_rank_one_mem P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).μsec (p.T.bs P.r).z_mem (p.T.bs P.r).z'_mem (p.T.bs P.r).sec ζ hζ'
      1 (one_mem_UWset _) 1 (one_mem_UWset _)
    simpa using this
  have hdom : ∀ ζ ∈ O, (c0, g ζ) ∈ DomR P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' := by
    intro ζ hζ
    obtain ⟨hmem, hherm⟩ := hfacts ζ hζ
    refine ⟨fun _ => one_ne_zero, Formalism.FourierDecayAlt.P.JCx2.rb_uwb_glev hmem, ?_⟩
    unfold Q.GGl
    rw [P5.Rad.zetaL_last, hherm, hTT]
    exact sub_pos.2 hζ
  have hzeta : ∀ ζ ∈ O, Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) (g ζ) = ζ := by
    intro ζ hζ
    rw [P5.Rad.zetaL_last, (hfacts ζ hζ).2]
  have hg : ContinuousOn g O := by
    refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_
    simp only [g, B2.embWb]
    split_ifs
    · exact ((p.T.bs P.r).sec.1 _ _).continuousOn.mono (fun ζ hζ => by
        simp only [Set.mem_ofPred_eq]; rw [hTT]; exact hζ)
    · exact continuousOn_const
    · exact continuousOn_const
  have hcont : ContinuousOn (fun ζ => topDens L st (D.positionted w) Φ Φ' c0 (g ζ)) O :=
    topDens_contOn L st (D.positionted w) Φ Φ' c0 hO hg hdom
  refine hcont.congr fun ζ hζ => ?_
  have := hHTx (c0, g ζ) (hdom ζ hζ)
  simp only [] at this
  rw [hzeta ζ hζ] at this
  exact this.symm

end Formalism.FourierDecayAlt.P.PBO
end
end
