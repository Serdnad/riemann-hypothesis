module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle125
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle036
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSettingBis
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsCompactCutoffCoefficient
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadCorrespondenceOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGLet
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle204
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle113
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle200
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle094
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DirectionsInParabolic
import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfBetaAdjCOfLemmaBNorm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting
public import Formalism.HermitianCurvature.Bundle004
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle079
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LUFactorOrbitBounds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyZeroNear
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGInt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle131
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceCompactSupportCoefficient
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NegMulCCancel

@[expose] public section

section

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutHB

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates Formalism.FourierDecayAlt.P.PBQ

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def CutOffStep : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (j : ℕ) (hj : j + 1 ≤ P.r) (w : List C.Letter) (h : C.LPt) (hh : D.IsLocPt h j)
    (γ : B.Mat P.k (P.r - (j + 1))),
    γ ∈ B.GV P.k (P.r - (j + 1)) →
    γ ∈ Q.OmPlus P.k (P.r - (j + 1)) (p.T.bs (j + 1)).z (p.T.bs (j + 1)).z' →
    ∀ (t : ℂ) (ht : D.IsLocPt (h ++ [(1, t)]) (j + 1)) (e : Wd.Ix (Fin w.length))
      (Fc : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), KB.CptCoef p.T.base Fc →
      (∀ g, Dmin P.k P.r p.T.base.z p.T.base.z' g ⟨j + 1, by omega⟩ = (U.hMat (D.ptPerm h) (D.ptDiag h)).det * t →
        Fc g = D.uwG P.k P.r p.T.base.z p.T.base.z' F (j + 1) hj w e g) →
      B.JF (p.T.bs (j + 1)) (KB.slv p.T F (j + 1) hj w (h ++ [(1, t)]) ht.2 e) γ =
        B.JF (p.T.bs j) (KB.slv p.T Fc j (by omega) [] h hh.2 (fun a => a.elim0)) (mLev P j hj t γ)

def CutOffExists : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (j : ℕ) (hj : j + 1 ≤ P.r) (w : List C.Letter) (h : C.LPt) (hh : D.IsLocPt h j),
    KB.CptCoef p.T.base F →
    ∀ (t : ℂ) (ht : D.IsLocPt (h ++ [(1, t)]) (j + 1)) (e : Wd.Ix (Fin w.length)),
      ∃ Fc : B.Mat P.k P.r → (Wq →L[ℂ] Wp), KB.CptCoef p.T.base Fc ∧
        ∀ g, Dmin P.k P.r p.T.base.z p.T.base.z' g ⟨j + 1, by omega⟩ = (U.hMat (D.ptPerm h) (D.ptDiag h)).det * t →
          Fc g = D.uwG P.k P.r p.T.base.z p.T.base.z' F (j + 1) hj w e g

section proofs

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem det_hMat_app (h : C.LPt) (t : ℂ) :
    (U.hMat (D.ptPerm (h ++ [(1, t)])) (D.ptDiag (h ++ [(1, t)]))).det =
      (U.hMat (D.ptPerm h) (D.ptDiag h)).det * t := by
  rw [Formalism.FourierDecayAlt.P.PBI.det_hMat_pt, Formalism.FourierDecayAlt.P.PBI.det_hMat_pt h]
  have hsz : D.ptSize (h ++ [(1, t)]) = D.ptSize h + 1 := by
    simp [D.ptSize]
  rw [hsz, (Formalism.FourierDecayAlt.P.PBD.det_ptMatN_app t h (D.ptSize h) rfl).1, mul_comm]

theorem uwG_zero_of_G {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (ε : ℝ)
    (hε : ∀ g ∈ B.GV k r, F g ≠ 0 → ε ≤ Gf k r z z' g) (i : ℕ) (hi : i ≤ r) :
    ∀ (w : List C.Letter) (e : Wd.Ix (Fin w.length)), ∀ g ∈ B.GV k r,
      D.uwG k r z z' F i hi w e g ≠ 0 → ε ≤ Gf k r z z' g
  | [], _, g, hg, hne => hε g hg hne
  | l :: w, e, g, hg, hne => by
    by_contra hlt
    push Not at hlt
    apply hne
    show D.vLet k r z z' i hi l (e 0) (D.uwG k r z z' F i hi w fun a => e a.succ) g = 0
    refine Formalism.FourierDecayAlt.P.PBG.vLet_zero_near z z' i hi l (e 0) _ (V := {x | Gf k r z z' x < ε})
      (isOpen_lt (Formalism.FourierDecayAlt.P.DifferentialOperatorClasses.gf_cont k r z z') continuous_const) (fun x hx hxG => ?_) g hlt hg
    by_contra h0
    exact absurd (uwG_zero_of_G z z' F ε hε i hi w _ x hxG h0) (not_le.2 hx)

def cutW {P : M.Par} (Bs : B.RealPlaceData P.k P.r Wp Wq) (χ : ℂ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (i : ℕ)
    (hi : i ≤ P.r) (w : List C.Letter) (e : Wd.Ix (Fin w.length)) : B.Mat P.k P.r → (Wq →L[ℂ] Wp) :=
  fun g => χ (Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩) • D.uwG P.k P.r Bs.z Bs.z' F i hi w e g

theorem cutW_exists {P : M.Par} (Bs : B.RealPlaceData P.k P.r Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (hF : KB.CptCoef Bs F) (i : ℕ) (hi : i ≤ P.r) (w : List C.Letter) (e : Wd.Ix (Fin w.length)) (a : ℂ)
    (ha : a ≠ 0) :
    ∃ Fc : B.Mat P.k P.r → (Wq →L[ℂ] Wp), KB.CptCoef Bs Fc ∧
      ∀ g, Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩ = a → Fc g = D.uwG P.k P.r Bs.z Bs.z' F i hi w e g := by
  obtain ⟨hck, ⟨R, hR⟩, ε, hε, hεG⟩ := hF
  have hn : 0 < ‖a‖ := norm_pos_iff.mpr ha
  let b : ContDiffBump a := ⟨‖a‖ / 4, ‖a‖ / 2, by positivity, by linarith⟩
  have hD : ContDiff ℝ (⊤ : ℕ∞) (fun g : B.Mat P.k P.r => Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩) :=
    Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin Bs.z Bs.z' _
  have hbD : ContDiff ℝ (⊤ : ℕ∞) (fun g : B.Mat P.k P.r => b (Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩)) :=
    b.contDiff.comp hD
  have hne : ∀ g, cutW Bs b F i hi w e g ≠ 0 → D.uwG P.k P.r Bs.z Bs.z' F i hi w e g ≠ 0 := by
    intro g hg h0
    apply hg
    simp [cutW, h0]
  refine ⟨cutW Bs b F i hi w e, ⟨?_, ⟨R, fun g hg h1 => Formalism.FourierDecayAlt.P.PBG.uwG_supp Bs.z Bs.z' F R hR i hi w e g hg
      (hne g h1)⟩, ε, hε, fun g hg h1 => uwG_zero_of_G Bs.z Bs.z' F ε hεG i hi w e g hg (hne g h1)⟩, ?_⟩
  · intro g₀ hg₀
    by_cases h0 : Dmin P.k P.r Bs.z Bs.z' g₀ ⟨i, by omega⟩ = 0
    · refine ⟨{g | ‖Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩‖ < ‖a‖ / 2}, fun _ => 0,
        isOpen_lt (continuous_norm.comp hD.continuous) continuous_const, by simp [h0]; positivity,
        contDiffOn_const, fun g hg _ => ?_⟩
      have hb0 : b (Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩) = 0 := by
        apply Function.notMem_support.1
        rw [b.support_eq, Metric.mem_ball, dist_eq_norm]
        intro hlt
        have h1 : ‖a‖ ≤ ‖Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩ - a‖ + ‖Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩‖ := by
          have := norm_sub_le (Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩) (Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩ - a)
          simp at this
          linarith
        have h2 : b.rOut = ‖a‖ / 2 := rfl
        have h3 : ‖Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩‖ < ‖a‖ / 2 := hg
        linarith
      simp [cutW, hb0]
    · obtain ⟨U, f', hU, hgU, hf', hE⟩ :=
        Formalism.FourierDecayAlt.P.PBG.uwG_mem Bs.z Bs.z' i hi hck w e g₀ h0 hg₀
      refine ⟨U, fun g => b (Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩) • f' g, hU, hgU,
        (hbD.contDiffOn.of_le le_rfl).smul hf', fun g hg hgG => ?_⟩
      simp only [cutW]
      rw [hE g hg hgG]
  · intro g hg
    simp only [cutW]
    rw [hg, b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le), one_smul]

end proofs

theorem truncation_off_exists_formula : CutOffExists := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj w h hh hF t ht e
  have ht0 : t ≠ 0 := (ht.1 (1, t) (List.mem_append_right _ (List.mem_singleton_self _))).2
  have hH : (U.hMat (D.ptPerm h) (D.ptDiag h)).det ≠ 0 := by
    rw [Formalism.FourierDecayAlt.P.PBI.det_hMat_pt, hh.2]
    exact Formalism.FourierDecayAlt.P.PBI.det_ptMatN_ne h j hh
  exact cutW_exists p.T.base F hF (j + 1) hj w e _ (mul_ne_zero hH ht0)

theorem truncation_off_induction : CutOffStep := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj w h hh γ hγ hΩ t ht e Fc hFc hag
  have hs : KB.slv p.T F (j + 1) hj w (h ++ [(1, t)]) ht.2 e =
      KB.slv p.T Fc (j + 1) hj [] (h ++ [(1, t)]) ht.2 (fun a => a.elim0) := by
    unfold KB.slv
    congr 1
    apply Formalism.FourierDecayAlt.P.PBI.sliceAt_congr_Dr _ _ _ (by rw [ht.2]; exact hj)
    intro x hx
    symm
    show Fc x = _
    apply hag
    have e1 : (⟨j + 1, by omega⟩ : Fin (P.r + 2)) = ⟨D.ptSize (h ++ [(1, t)]), by rw [ht.2]; omega⟩ :=
      Fin.ext ht.2.symm
    rw [e1, hx, det_hMat_app]
  rw [hs, Formalism.FourierDecayAlt.P.slice_induction_level Wp Wq P p Fc j hj h t hh ht hFc γ hγ hΩ]
  rfl

end Formalism.FourierDecayAlt.P.CutHB
end
end

section

noncomputable section

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutEX.MkCptPf

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section casts

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def castBS {k a b : ℕ} (e : a = b) (Bs : B.RealPlaceData k a Wp Wq) : B.RealPlaceData k b Wp Wq := e ▸ Bs

theorem castBS_z_eq_castV {k a b : ℕ} (e : a = b) (Bs : B.RealPlaceData k a Wp Wq) : (castBS e Bs).z = D.castV e Bs.z := by
  subst e
  rfl

theorem castBS_z'_eq_castV {k a b : ℕ} (e : a = b) (Bs : B.RealPlaceData k a Wp Wq) : (castBS e Bs).z' = D.castV e Bs.z' := by
  subst e
  rfl

theorem cptCoef_castF {k a b : ℕ} (e : a = b) (Bs : B.RealPlaceData k a Wp Wq) (G : B.Mat k b → (Wq →L[ℂ] Wp))
    (h : KB.CptCoef (castBS e Bs) G) : KB.CptCoef Bs (D.castF e G) := by
  subst e
  exact h

end casts

theorem glev_last_iff {k ρ : ℕ} (hρ : ρ = 0) (g : B.Mat k ρ) :
    g ∈ Q.Glev k ρ (Fin.last ρ) ↔ g ∈ B.GV k ρ := by
  subst hρ
  exact Formalism.FourierDecayAlt.P.JCx2.sq_glev0 g

theorem gf_eq_ggl {k ρ : ℕ} (hρ : ρ = 0) (z z' : Fin (2 * ρ + k + 1) → ℂ) (g : B.Mat k ρ) :
    Gf k ρ z z' g = Q.GGl k ρ z z' g := by
  subst hρ
  have h0 : Dmin k 0 z z' g ⟨0, by omega⟩ = 1 := by
    unfold Dmin
    exact Matrix.det_isEmpty
  have h1 : Dmin k 0 z z' g (Fin.last 1) = Zhat k 0 z z' g (Fin.last 0) (Fin.last 0) := by
    unfold Dmin
    exact Matrix.det_fin_one _
  unfold Gf Q.GGl
  rw [Formalism.FourierDecayAlt.P.PBI.zetaL_eq_zhat, h0, h1]
  simp

end Formalism.FourierDecayAlt.P.CutEX.MkCptPf

namespace Formalism.FourierDecayAlt.P.CutEX.MkCptPf

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section top

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem lowV_top {k r : ℕ} (T : D.LevTower k r Wp Wq) (e : r = r + (r - r)) :
    U.lowV k r (r - r) (D.castV e T.base.z) = (T.bs r).z := by
  have hzl := (T.z_lev r le_rfl).symm
  change T.base.z = _ at hzl
  rw [hzl, Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV]
  exact Formalism.FourierDecayAlt.P.JCTx6.Link2.lowV_liftVec rfl _ _

theorem lowV_top' {k r : ℕ} (T : D.LevTower k r Wp Wq) (e : r = r + (r - r)) :
    U.lowV k r (r - r) (D.castV e T.base.z') = (T.bs r).z' := by
  have hzl := (T.z'_lev r le_rfl).symm
  change T.base.z' = _ at hzl
  rw [hzl, Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV]
  exact Formalism.FourierDecayAlt.P.JCTx6.Link2.lowV_liftVec rfl _ _

end top

theorem mkCpt : MkCpt := by
  intro Wp Wq _ _ _ _ _ _ P p b b' hb hbc hb' hb'c Φ hΦ K hK hKU hsupp
  have hρ : P.r - P.r = 0 := Nat.sub_self _
  have e : P.r = P.r + (P.r - P.r) := by omega
  have hz : U.lowV P.k P.r (P.r - P.r) (castBS e p.T.base).z = (p.T.bs P.r).z := by
    rw [castBS_z_eq_castV]; exact lowV_top p.T e
  have hz' : U.lowV P.k P.r (P.r - P.r) (castBS e p.T.base).z' = (p.T.bs P.r).z' := by
    rw [castBS_z'_eq_castV]; exact lowV_top' p.T e
  have hUTo : IsOpen (UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z') := by
    have c1 : Continuous (fun q : (Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r) => (Matrix.of q.1).det) :=
      Continuous.matrix_det continuous_fst
    have c2 : Continuous (fun q : (Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r) =>
        Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Matrix.of q.2)) :=
      (Formalism.FourierDecayAlt.P.Qx5.GGl_continuous _ _ _ _).comp continuous_snd
    exact (isOpen_ne_fun c1 continuous_const).inter (isOpen_lt continuous_const c2)
  have hCpt : KB.CptCoef (castBS e p.T.base) (PBI.chartCoefficient b b' Φ) := by
    refine PBI.chartCoefficient_hasCompactSupport (castBS e p.T.base) b b' hb hbc hb' hb'c Φ (UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z')
      hUTo ?_ K hK hKU ?_ ?_
    · intro q₀ hq₀ hG
      obtain ⟨U', F, hU', hq, hF, hEq⟩ := hΦ q₀ hq₀ ((glev_last_iff hρ _).2 hG)
      exact ⟨U', F, hU', hq, hF, fun q hqU hqG => hEq q hqU ((glev_last_iff hρ _).2 hqG)⟩
    · intro q hq
      obtain ⟨h1, h2⟩ := hKU hq
      refine ⟨h1, ?_⟩
      rw [hz, hz', gf_eq_ggl hρ]
      exact h2
    · intro q hG hq
      exact hsupp q ((glev_last_iff hρ _).2 hG) hq
  refine ⟨cptCoef_castF e p.T.base _ hCpt,
    (fun q : (Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r) => (Matrix.of q.1).det) '' K,
    hK.image (Continuous.matrix_det continuous_fst), ?_, ?_⟩
  · rintro ⟨q, hq, h0⟩
    exact (hKU hq).1 h0
  · intro g hg hne
    have hg' : D.castM e g ∈ B.GV P.k (P.r + (P.r - P.r)) := Formalism.FourierDecayAlt.P.PBE.castM_GV e hg
    have hne' : PBI.chartCoefficient b b' Φ (D.castM e g) ≠ 0 := hne
    have hD : U.DjU P.k P.r (P.r - P.r) (D.castM e g) ≠ 0 := by
      intro h0; apply hne'; unfold PBI.chartCoefficient; rw [if_neg (not_not.2 h0)]
    obtain ⟨-, hμ, heq⟩ := PBI.chart_spec (D.castM e g) hg' hD
    have hmk := hne'
    unfold PBI.chartCoefficient at hmk
    rw [if_pos hD] at hmk
    obtain ⟨-, hΦne⟩ := smul_ne_zero_iff.1 hmk
    have hμ' : Matrix.of (PBI.chart (Matrix.of.symm (D.castM e g))).2.2 ∈ B.GV P.k (P.r - P.r) := by
      simpa only [PBI.chart, Equiv.apply_symm_apply] using hμ
    have hK' : (PBI.chart (Matrix.of.symm (D.castM e g))).2 ∈ K := by
      by_contra hn
      exact hΦne (hsupp _ ((glev_last_iff hρ _).2 hμ') hn)
    refine ⟨_, hK', ?_⟩
    have hpsi : PBI.psiC (PBI.chart (Matrix.of.symm (D.castM e g))) = D.castM e g := by
      unfold PBI.psiC PBI.chart
      simp only [Equiv.apply_symm_apply]
      exact heq.symm
    have e1 := PBI.djU_psiC (PBI.chart (Matrix.of.symm (D.castM e g)))
    rw [hpsi] at e1
    show (Matrix.of (PBI.chart (Matrix.of.symm (D.castM e g))).2.1).det = _
    rw [← e1, ← Formalism.FourierDecayAlt.P.hat_z_minimum_degree P.k P.r (P.r - P.r) (D.castV e p.T.base.z) (D.castV e p.T.base.z'),
      Formalism.FourierDecayAlt.P.PBG.Dmin_castM e _ _ g P.r, Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV, Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV,
      Formalism.FourierDecayAlt.P.JCTx6.Link2.castV_self, Formalism.FourierDecayAlt.P.JCTx6.Link2.castV_self]

end Formalism.FourierDecayAlt.P.CutEX.MkCptPf

namespace Formalism.FourierDecayAlt.P

theorem compact_truncation_construction : CutEX.MkCpt := CutEX.MkCptPf.mkCpt

end Formalism.FourierDecayAlt.P
end
end

section

open Matrix MeasureTheory Filter Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutEXPbRight

theorem castM_nset {k a b : ℕ} (e : a = b) {g : B.Mat k a} (hg : g ∈ Nset k a) : D.castM e g ∈ Nset k b := by
  subst e
  have : D.castM rfl g = g := by
    ext i j
    simp [D.castM]
  rw [this]
  exact hg

end Formalism.FourierDecayAlt.P.CutEXPbRight

namespace Formalism.FourierDecayAlt.P

open CutEX

private theorem castM_mul_eq_mul_castM {k a b : ℕ} (e : a = b) (g h : B.Mat k a) :
    D.castM e (g * h) = D.castM e g * D.castM e h := by
  subst e
  ext i j
  simp [D.castM]

theorem pullback_right_action : CutEX.PbRight := by
  intro Wp Wq _ _ _ _ _ _ P p G _ Z u μ hu
  have hm : D.castM (by omega) (U.muP P.k P.r (P.r - P.r) u) ∈ Nset P.k P.r :=
    CutEXPbRight.castM_nset _ (BigCellDiagonalMap.leviElement_nset u hu)
  unfold CutEX.pbTop CutEX.psiU PBQ.pbT CutEX.xT
  rw [← Ux4.mMap_mul_muP, castM_mul_eq_mul_castM]
  exact PBQ.pbF_right _ _ _ _ _ _ hm

end Formalism.FourierDecayAlt.P
end
end

section

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt

theorem radial_slice_top : CutEX.RadSliceTop := by
  intro Wp Wq _ _ _ _ _ _ P p G hG h hh
  have hc : P.r - P.r = P.r - D.ptSize h := by rw [hh.2]
  have hcpt : KB.CptCoef (p.T.bs P.r) (D.castF hc (D.sliceAt P.k P.r p.T.base.z p.T.base.z' G h)) := by
    cases P with
    | mk k r T T' u u' =>
      rcases Nat.eq_zero_or_pos r with h0 | h0
      · subst h0
        exact PBE.slice_level_zero_compact_support k 0 Wp Wq p.T G hG.1 (Nat.zero_le _) [] h hc hh (fun x => x.elim0)
      · exact PBE.slice_pos_cpt k r Wp Wq p.T G hG.1 r le_rfl h0 [] h hc hh (fun x => x.elim0)
  obtain ⟨R, hR⟩ := hcpt.2.1
  have hJ : P5.JFOK (JC.parLev P P.r) (p.T.bs P.r).z (p.T.bs P.r).z'
      (D.castF hc (D.sliceAt P.k P.r p.T.base.z p.T.base.z' G h)) := by
    refine ⟨fun A m => JFxG.cptInCC_G hcpt.1 (PBE.isCompact_gN_le _ _ R) (fun g hg hgC => ?_) A m, hcpt.2.2⟩
    by_contra hne
    exact hgC (hR g hg hne)
  obtain ⟨Φ, hΦ⟩ := P5.radJFExists Wp Wq (JC.parLev P P.r) _ _ _ _ (p.T.bs P.r) _
    (JCTx5.isPlace_lev P p.T ⟨P.r, Nat.lt_succ_self _⟩ p.hP) rfl rfl rfl rfl hJ
  exact ⟨Φ, hΦ⟩

end Formalism.FourierDecayAlt.P
end
end

section

open Formalism.FourierDecayAlt MeasureTheory
open Formalism.REAL Formalism.QuantumDeterminants

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open NumberField Formalism.FourierDecayAlt.P.CutMP

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem locAdd_thr (k r : ℕ) {A : ℝ} (hA : 10 * ((r : ℝ) + 1) * nDim k r ^ 2 ≤ A) : JF.TransportedAlt k r A 0 := by
  unfold JF.TransportedAlt
  have hn : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1)
  have hr : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  have hA' : 10 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 ≤ A := by simpa [nDim] using hA
  have hn2 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
  rw [lt_div_iff₀ (by positivity)]
  simp only [Nat.cast_zero, mul_zero, sub_zero]
  nlinarith [mul_pos hr (lt_of_lt_of_le one_pos hn2)]

theorem local_additivity_transfer : JALocAdd := by
  refine ⟨10, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top Cb A₀ hB v Bg A J J' hBg hA hJ hJ'
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hTT : (D.parOf S v).TT = Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' := by
    rw [hPl.2.2.2.1, hPl.2.2.2.2.1]; rfl
  have hThr := locAdd_thr S.G.k S.G.r hA
  refine ⟨Formalism.FourierDecayAlt.P.Qx8.FFl_add hJ.1 hJ'.1, fun δ hδ => ?_⟩
  obtain ⟨F, hF1, hF2, hF3⟩ := hJ.2 δ hδ
  obtain ⟨F', hF1', hF2', hF3'⟩ := hJ'.2 δ hδ
  refine ⟨F + F', Formalism.FourierDecayAlt.P.JCx2.ckOn_add' hF1 hF1', fun m => ?_, fun x hx hG => ?_⟩
  · obtain ⟨c, hc⟩ := hF2 m
    obtain ⟨c', hc'⟩ := hF2' m
    exact ⟨c + c', Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_add hc hc'⟩
  · have hq : x ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z' := ⟨hx.1, hTT ▸ hx.2⟩
    have hg := Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom (T v).base hq
    have h0 : B.InCC A 0 F := by simpa using hF2 0
    have h0' : B.InCC A 0 F' := by simpa using hF2' 0
    have i1 := (Formalism.FourierDecayAlt.P.bessel_integral_converges S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base A F hThr h0).1 _ hg
    have i2 := (Formalism.FourierDecayAlt.P.bessel_integral_converges S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base A F' hThr h0').1 _ hg
    have e : ∀ G : GFn S v, B.JF (T v).base G (B.gq (T v).base x) =
        ∫ p, JF.integrand (T v).base G (B.gq (T v).base x) p ∂(T v).base.μSS := fun G => rfl
    rw [Pi.add_apply, hF3 x hx hG, hF3' x hx hG, e, e, e, ← integral_add i1 i2]
    congr 1
    funext p
    simp [JF.integrand, B.rho, smul_add]

end Formalism.FourierDecayAlt.P.CutMP.JA

end
end
