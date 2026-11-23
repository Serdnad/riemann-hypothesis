module

public import Formalism.HermitianCurvature.Bundle006
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle178
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle185
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.WordCorrespondence
public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle115
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle128
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle050
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChartCoefficientHasCompactSupport
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle146
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle056
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle189
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle123
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PtieLevTransportHerOf
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle132
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle179

@[expose] public section

section

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBO

open Formalism.FourierDecayAlt

def PStdOfParts : Prop := KB.RadHead → KB.HeadTop → FormOne → ZetaNormExists → KB.PStd

theorem pStdOfParts : PStdOfParts := fun hRH hHT hOne hZN hP =>
  pStd_of hRH hHT hOne hZN
    (fun Wp Wq _ _ _ _ _ _ P p F w h h' hh hh' Cb hθ hF hw => by
      have hPc : P5.ThmPActualCpt := by
        intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D A mm hD hl1 hl2 hz hz' hπ hπ' hA hmm
        obtain ⟨K, h1, h2, h3, h4⟩ := hP Wp Wq S P z z' π π' X μ L st l0 D A mm hD hl1 hl2 hz hz' hπ hπ' hA hmm
        exact ⟨K, h1, h2, h3, fun F ε hε hF _ hG => h4 F ε hε hF hG⟩
      exact topContOn_of hPc hHT Wp Wq P p F w h h' hh hh' Cb hθ hF hw) hP

theorem pStd_cpt_of_parts (hP : P5.ThmPActualCpt) (hRH : KB.RadHead) (hHT : KB.HeadTop) (hOne : FormOne)
    (hZN : ZetaNormExists) :
    ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter) (h h' : C.LPt)
    (hh : D.IsLocPt h j) (hh' : D.IsLocPt h' j) (Cb : ℝ), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ →
    KB.CptCoef p.T.base F → KB.CutWord P p.l0 w →
    ∃ φ : ℂ → ℂ, Continuous φ ∧ MeasureTheory.Integrable φ ∧
      (∀ c : ℂ, c ≠ 0 → φ c = (KB.levW P (j + 1) c : ℂ) * p.RR F (j + 1) w (h ++ [(1, c)]) (h' ++ [(1, c)])) ∧
      ∀ s : ℂ, ∫ c, P5.fsv s c * φ c =
        p.form j hj w (KB.waveG (p.T.bs j) s w (KB.slv p.T F j hj w h hh.2)) (KB.slv p.T F j hj w h' hh'.2) :=
  pStd_of_cpt hP hRH hHT hOne hZN (topContOn_of hP hHT)

end Formalism.FourierDecayAlt.P.PBO
end
end

section

namespace Formalism.FourierDecayAlt.P.ModuleFormPositivity

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.Q Formalism.QuantumDeterminants
open scoped ComplexOrder

def FormPosCpt : Prop :=
  P5.ThmPActualCpt → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter), KB.CutWord P p.l0 w → ∀ x,
    (∀ e, KB.CptCoef (p.T.bs j) (x e)) → 0 ≤ p.form j hj w x x

end Formalism.FourierDecayAlt.P.ModuleFormPositivity

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.Q Formalism.QuantumDeterminants
open scoped ComplexOrder

theorem module_form_pos_compact_support : ModuleFormPositivity.FormPosCpt := by
  intro hP Wp Wq _ _ _ _ _ _ P p j hj w hc x hx
  obtain ⟨ε, hε, R, hxN, hxR, -, -⟩ := Formalism.FourierDecayAlt.P.PBF.common_eps_R (p.T.bs j) x x hx hx
  obtain ⟨hl1, hlk, -⟩ := p.hl
  let jF : Fin (P.r + 1) := ⟨j, by omega⟩
  have hPl := Formalism.FourierDecayAlt.P.JCTx5.isPlace_lev P p.T jF p.hP
  obtain ⟨X⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist _ _ _ _ _ _ _ hPl
  obtain ⟨L, st, h1, h2, h3, h4, h5, h6⟩ := Formalism.FourierDecayAlt.P.level_start_actual _ _ _ _ _ _ _ hPl X p.l0
  obtain ⟨μ0, hμ0⟩ := Formalism.FourierDecayAlt.P.JCTx5.exists_haar_level_zero (Nat.sub_self P.r) (p.T.bs P.r)
  set μ := μ0.map (Formalism.FourierDecayAlt.P.JCTx5.embL P.k (P.r - j)) with hμ
  have hD : IsData (JC.parLev P jF) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π' X μ L st p.l0 :=
    ⟨hPl, Formalism.FourierDecayAlt.P.JCTx5.haar_glev μ0 hμ0, h1, h2, h3, h4, h5, h6⟩
  obtain ⟨K, hThm, -, -, hJc⟩ := hP Wp Wq (Fin w.length) (JC.parLev P jF) _ _ _ _ X μ L st p.l0
    (p.T.bs jF) _ _ hD hl1 hlk rfl rfl rfl rfl le_rfl le_rfl
  obtain ⟨Cst, hC, hform⟩ := Formalism.FourierDecayAlt.P.radial_module_form Wp Wq P p.T jF X μ L st p.l0 hD
  choose Φ hΦK hΦ using fun a =>
    Formalism.FourierDecayAlt.P.PBF.pic_of_cptClause (p.T.bs jF) (K 0) hJc hε (hxN a) (hxR a)
  have hW := Formalism.FourierDecayAlt.P.JCTx5.wordOK_of (JC.parLev P jF) _ _ _ _ st p.l0 hPl.1 hl1 hlk h3 h4 w hc.1 hc.2
  have hpos := ((hThm (D.positionted w) hW).2.2 0 (fun _ => 1) (fun _ => one_ne_zero)).2 Φ (fun a _ => hΦK a)
  have hpos' : 0 ≤ P5.form μ 0 (P5.act (P5.RRi L st 0 (D.positionted w)) Φ) Φ 0 :=
    hpos.trans_eq (Formalism.FourierDecayAlt.P.JCx2.form_zero_indep μ _ _ _ _)
  have e := hform w x x Φ Φ ε hε hxN hxN hΦ hΦ
  show 0 ≤ D.formLev p.T (M.sgn P p.l0) jF w x x
  rw [e]
  exact mul_nonneg (by exact_mod_cast hC.le) hpos'

end Formalism.FourierDecayAlt.P
end

section

noncomputable section

open Matrix MeasureTheory Filter Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutEX

section defs

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def xT (k r : ℕ) (Z : Matrix (Fin r) (Fin r) ℂ) (μ : B.Mat k (r - r)) : B.Mat k r :=
  D.castM (by omega) (U.mMap k r (r - r) Z μ)

def pbTop {P : M.Par} (p : KB.Pl P Wp Wq) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Z : Matrix (Fin P.r) (Fin P.r) ℂ)
    (μ : B.Mat P.k (P.r - P.r)) : Wq →L[ℂ] Wp :=
  PBQ.pbT p P.r le_rfl G (xT P.k P.r Z μ)

def TopCls {k r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) (G : B.Mat k r → (Wq →L[ℂ] Wp)) : Prop :=
  KB.CptCoef Bs G ∧ ∃ K : Set ℂ, IsCompact K ∧ (0 : ℂ) ∉ K ∧
    ∀ g ∈ B.GV k r, G g ≠ 0 → Dmin k r Bs.z Bs.z' g ⟨r, by omega⟩ ∈ K

def UT (k r : ℕ) (z z' : Fin (2 * (r - r) + k + 1) → ℂ) : Set ((Fin r → Fin r → ℂ) × Mt k (r - r)) :=
  {q | (Matrix.of q.1).det ≠ 0 ∧ 0 < Q.GGl k (r - r) z z' (Matrix.of q.2)}

def psiU {P : M.Par} (p : KB.Pl P Wp Wq) (u : Matrix (Fin P.r) (Fin P.r) ℂ) : ℂ :=
  psi P.k P.r p.T.base.z' cStd (D.castM (by omega) (U.muP P.k P.r (P.r - P.r) u))

def F2 {k r : ℕ} (b b' : U.RC k r (r - r) → ℝ) (Φ : (Fin r → Fin r → ℂ) → Mt k (r - r) → (Wq →L[ℂ] Wp)) :
    B.Mat k r → (Wq →L[ℂ] Wp) :=
  D.castF (by omega : r = r + (r - r)) (PBI.chartCoefficient b b' Φ)

end defs

def UwTop : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), TopCls p.T.base F →
    ∀ (w : List C.Letter) (e : Wd.Ix (Fin w.length)),
      TopCls p.T.base (D.uwG P.k P.r p.T.base.z p.T.base.z' F P.r le_rfl w e)

def SliceTop : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), TopCls p.T.base G →
    ∀ (h : C.LPt) (hh : D.IsLocPt h P.r) (γ : B.Mat P.k (P.r - P.r)), γ ∈ B.GV P.k (P.r - P.r) →
      0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' γ →
      Integrable (fun v : PBQ.XH h => PBQ.ellH h v (pbTop p G (PBQ.zxH h P.r hh.2 v) γ)) ∧
      B.JF (p.T.bs P.r) (D.castF (by rw [hh.2]) (D.sliceAt P.k P.r p.T.base.z p.T.base.z' G h)) γ =
        ∫ v, PBQ.ellH h v (pbTop p G (PBQ.zxH h P.r hh.2 v) γ)

def PbSmooth : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), TopCls p.T.base G →
    PBI.ParFam P.k (P.r - P.r) (UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z')
      (fun q => pbTop p G (Matrix.of q.1) (Matrix.of q.2))

def PbRight : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), TopCls p.T.base G →
    ∀ (Z u : Matrix (Fin P.r) (Fin P.r) ℂ) (μ : B.Mat P.k (P.r - P.r)), Formalism.DoubleCosetMeasures.IsUpUni u →
      pbTop p G (Z * u) μ = psiU p u • pbTop p G Z μ

def PbSupp : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), TopCls p.T.base G →
    ∃ K : Set ((Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r)), IsCompact K ∧
      K ⊆ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z' ∧
      ∀ q : (Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r), (Matrix.of q.1).det ≠ 0 →
        Matrix.of q.2 ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) → pbTop p G (Matrix.of q.1) (Matrix.of q.2) ≠ 0 →
        ∃ u : Matrix (Fin P.r) (Fin P.r) ℂ, Formalism.DoubleCosetMeasures.IsUpUni u ∧ (Matrix.of.symm (Matrix.of q.1 * u), q.2) ∈ K

def PbEquiv : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), TopCls p.T.base G →
    ∀ (Z : Matrix (Fin P.r) (Fin P.r) ℂ), Z.det ≠ 0 →
    ∀ μ ∈ Q.Glev P.k (P.r - P.r) (Fin.last _), ∀ h ∈ UWset P.k (P.r - P.r) (p.T.bs P.r).z,
    ∀ h' ∈ UWset P.k (P.r - P.r) (p.T.bs P.r).z',
      pbTop p G Z (h * μ * h') = ((p.T.bs P.r).π h).comp ((pbTop p G Z μ).comp ((p.T.bs P.r).π' h'))

def MkTop : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq),
    ∃ (b b' : U.RC P.k P.r (P.r - P.r) → ℝ) (β : (Fin P.r → Fin P.r → ℂ) → ℝ) (κ : ℂ),
      ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧ ContDiff ℝ ∞ b' ∧ HasCompactSupport b' ∧ κ ≠ 0 ∧
      ContDiffOn ℝ ∞ β {Z | (Matrix.of Z).det ≠ 0} ∧
      (∀ K : Set ((Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r)), IsCompact K →
        K ⊆ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z' →
        ∃ K' : Set ((Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r)), IsCompact K' ∧
          K' ⊆ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z' ∧
          ∀ q : (Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r), (Matrix.of q.1).det ≠ 0 → β q.1 ≠ 0 →
            (∃ u : Matrix (Fin P.r) (Fin P.r) ℂ, Formalism.DoubleCosetMeasures.IsUpUni u ∧ (Matrix.of.symm (Matrix.of q.1 * u), q.2) ∈ K) →
            q ∈ K') ∧
      ∀ Φ : (Fin P.r → Fin P.r → ℂ) → Mt P.k (P.r - P.r) → (Wq →L[ℂ] Wp),
        (∀ Z y, Matrix.of y ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) → ∀ h ∈ UWset P.k (P.r - P.r) (p.T.bs P.r).z,
          ∀ h' ∈ UWset P.k (P.r - P.r) (p.T.bs P.r).z',
            Φ Z (Matrix.of.symm (h * Matrix.of y * h')) = ((p.T.bs P.r).π h).comp ((Φ Z y).comp ((p.T.bs P.r).π' h'))) →
        (∀ Z y (u : Matrix (Fin P.r) (Fin P.r) ℂ), (Matrix.of Z).det ≠ 0 →
          Matrix.of y ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) → Formalism.DoubleCosetMeasures.IsUpUni u →
            Φ (Matrix.of.symm (Matrix.of Z * u)) y = psiU p u • Φ Z y) →
        ∀ Z y, (Matrix.of Z).det ≠ 0 → Matrix.of y ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) →
          pbTop p (F2 b b' (fun Z' y' => ((β Z' : ℝ) : ℂ) • Φ Z' y')) (Matrix.of Z) (Matrix.of y) = κ • Φ Z y

def MkCpt : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (b b' : U.RC P.k P.r (P.r - P.r) → ℝ), ContDiff ℝ ∞ b → HasCompactSupport b → ContDiff ℝ ∞ b' →
    HasCompactSupport b' → ∀ Φ : (Fin P.r → Fin P.r → ℂ) → Mt P.k (P.r - P.r) → (Wq →L[ℂ] Wp),
    PBI.ParFam P.k (P.r - P.r) (UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z') (fun q => Φ q.1 q.2) →
    ∀ K : Set ((Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r)), IsCompact K →
      K ⊆ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z' →
      (∀ q, Matrix.of q.2 ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) → q ∉ K → Φ q.1 q.2 = 0) →
      TopCls p.T.base (F2 b b' Φ)

def TopPt : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq),
    (∀ x ∈ Q.DomR P.k P.r p.T.base.z p.T.base.z', ∃ g : B.Mat P.k (P.r - P.r),
      g ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) ∧ 0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' g ∧
      x.2 = D.castM (by omega) (ιLev P.k P.r (P.r - P.r) g)) ∧
    ∀ γ : B.Mat P.k (P.r - P.r), γ ∈ B.GV P.k (P.r - P.r) ↔ γ ∈ Q.Glev P.k (P.r - P.r) (Fin.last _)

def ZxDet : Prop :=
  ∀ (r : ℕ) (h : C.LPt) (hh : D.IsLocPt h r) (v : PBQ.XH h), (PBQ.zxH h r hh.2 v).det ≠ 0

def HeadFam : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (h : C.LPt) (hh : D.IsLocPt h P.r) (f : (Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r) → (Wq →L[ℂ] Wp)),
    PBI.ParFam P.k (P.r - P.r) (UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z') f →
    ∀ K : Set ((Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r)), IsCompact K →
      K ⊆ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z' →
      (∀ q, Matrix.of q.2 ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) → f q ≠ 0 →
        ∃ u : Matrix (Fin P.r) (Fin P.r) ℂ, Formalism.DoubleCosetMeasures.IsUpUni u ∧ (Matrix.of.symm (Matrix.of q.1 * u), q.2) ∈ K) →
      PBI.ParFam P.k (P.r - P.r)
        (Set.univ ×ˢ {y | 0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Matrix.of y)})
        (fun q : PBQ.XH h × Mt P.k (P.r - P.r) => PBQ.ellH h q.1 (f (PBQ.zxH h P.r hh.2 q.1, q.2))) ∧
      ∃ Kp : Set (PBQ.XH h), IsCompact Kp ∧ ∀ v ∉ Kp, ∀ y : Mt P.k (P.r - P.r),
        Matrix.of y ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) → f (PBQ.zxH h P.r hh.2 v, y) = 0

def RadSliceTop : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), TopCls p.T.base G →
    ∀ (h : C.LPt) (hh : D.IsLocPt h P.r),
      ∃ Ψ : Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π
          (p.T.bs P.r).π',
        Top.IsRadOf (JC.parLev P P.r) (p.T.bs P.r) Ψ
          (D.castF (by rw [hh.2]; rfl) (D.sliceAt P.k P.r p.T.base.z p.T.base.z' G h))

section mx

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def RadOfFun : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (k ρ : ℕ) (z z' : Fin (2 * ρ + k + 1) → ℂ) (π : Q.Mx k ρ → (Wp →L[ℂ] Wp))
    (π' : Q.Mx k ρ → (Wq →L[ℂ] Wq)) (f : Q.Mx k ρ → (Wq →L[ℂ] Wp)),
    (∀ g₀, g₀ ∈ Q.Glev k ρ (Fin.last ρ) → 0 < Q.GGl k ρ z z' g₀ → ∃ (U : Set (Q.Mx k ρ)) (F : Q.Mx k ρ → (Wq →L[ℂ] Wp)),
      IsOpen U ∧ g₀ ∈ U ∧ ContDiffOn ℝ ∞ F U ∧ ∀ g ∈ U, g ∈ Q.Glev k ρ (Fin.last ρ) → f g = F g) →
    (∀ g, g ∈ Q.Glev k ρ (Fin.last ρ) → 0 < Q.GGl k ρ z z' g → ∀ h ∈ UWset k ρ z, ∀ h' ∈ UWset k ρ z',
      f (h * g * h') = (π h).comp ((f g).comp (π' h'))) →
    ∃ Ψ : Q.RadSp k ρ z z' π π', ∀ x ∈ Q.DomR k ρ z z', (Ψ : Q.Fn k ρ (Wq →L[ℂ] Wp)) x.1 x.2 = f x.2

end mx

def RadExt : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (k ρ : ℕ) (z z' : Fin (2 * ρ + k + 1) → ℂ) (π : Q.Mx k ρ → (Wp →L[ℂ] Wp))
    (π' : Q.Mx k ρ → (Wq →L[ℂ] Wq)) (Ψ Ψ' : Q.RadSp k ρ z z' π π'),
    (∀ x ∈ Q.DomR k ρ z z', (Ψ : Q.Fn k ρ (Wq →L[ℂ] Wp)) x.1 x.2 = (Ψ' : Q.Fn k ρ (Wq →L[ℂ] Wp)) x.1 x.2) → Ψ = Ψ'

def ResTop : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k ρ : ℕ), ρ = 0 →
    ∀ (J : Q.Mx k ρ → E) (c : Fin ρ → ℂ) (g : Q.Mx k ρ), Q.resG k ρ (Fin.last ρ) J c g = J g

def Asm : Prop :=
  UwTop → SliceTop → PbSmooth → PbRight → PbSupp → PbEquiv → MkTop → MkCpt → TopPt → ZxDet → HeadFam → RadSliceTop →
    RadOfFun → RadExt → ResTop → PBI.FrameParam → PBI.RadWordSlice → PBI.PicSlice → PBI.ExhPic

theorem exhPic_of_leaves (hA : Asm) (h1 : UwTop) (h2 : SliceTop) (h3 : PbSmooth) (h3' : PbRight) (h4 : PbSupp) (h5 : PbEquiv)
    (h6 : MkTop) (h7 : MkCpt) (h8 : TopPt) (h9 : ZxDet) (h10 : HeadFam) (h11 : RadSliceTop) (h12 : RadOfFun)
    (h13 : RadExt) (h14 : ResTop) (hFP : PBI.FrameParam) (hRW : PBI.RadWordSlice) (hPS : PBI.PicSlice) :
    PBI.ExhPic :=
  hA h1 h2 h3 h3' h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 hFP hRW hPS

end Formalism.FourierDecayAlt.P.CutEX
end
end

section

open Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open NumberField Formalism.FourierDecayAlt.P.CutMP

def JALocOp : Prop :=
  ∃ Cc Cg : ℝ, 0 ≤ Cg ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (Cb A₀ : ℝ),
    BuiltOW Cb S T f χ ν' m₀ top A₀ →
    ∀ v,
      ∀ (Θ : (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))) (d Bg A : ℝ) (J : GFn S v), 0 ≤ d → Cg * ((S.G.r : ℝ) + 1) ≤ Bg → IsAAOp S T v Θ →
        CutCoef S T v Θ d Bg →
        Cc * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 + 6 * (S.G.r : ℝ) * (B.opOrder Θ : ℝ) + d +
          2 * Bg * ((B.opOrder Θ : ℝ) + 1) ≤ A →
        LocCC S T v A Bg J → B.opApply Θ J ∈ smoothFormsPositiveCone S T v →
          LocCC S T v (A - d - 2 * Bg * (B.opOrder Θ : ℝ)) Bg (B.opApply Θ J)

def JALocAdj : Prop :=
  ∃ Cc Cg : ℝ, 0 ≤ Cg ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (Cb A₀ : ℝ),
    BuiltOW Cb S T f χ ν' m₀ top A₀ →
    ∀ v,
      ∀ (Θ : (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))) (d Bg A : ℝ) (J : GFn S v), 0 ≤ d → Cg * ((S.G.r : ℝ) + 1) ≤ Bg → IsAAOp S T v Θ →
        CutCoef S T v Θ d Bg →
        Cc * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 + 6 * (S.G.r : ℝ) * (B.opOrder Θ : ℝ) + d +
          2 * Bg * ((B.opOrder Θ : ℝ) + 1) ≤ A →
        LocCC S T v A Bg J → B.opAdj Θ J ∈ smoothFormsPositiveCone S T v →
          LocCC S T v (A - d - 2 * Bg * (B.opOrder Θ : ℝ)) Bg (B.opAdj Θ J)

def JALocPhi : Prop :=
  ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (Cb A₀ : ℝ),
    BuiltOW Cb S T f χ ν' m₀ top A₀ →
    ∀ v,
      ∀ (φ : ℝ → ℝ) (Bg A : ℝ) (J : GFn S v), LE.SmoothLog φ → (∀ p, ∃ C, ∀ x, 0 < x → |LE.ld p φ x| ≤ C) →
        Cg * ((S.G.r : ℝ) + 1) ≤ Bg → LocCC S T v A Bg J → mulG S T v φ J ∈ smoothFormsPositiveCone S T v →
          LocCC S T v A Bg (mulG S T v φ J)

def JALocAdd : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (Cb A₀ : ℝ),
    BuiltOW Cb S T f χ ν' m₀ top A₀ →
    ∀ v,
      ∀ (Bg A : ℝ) (J J' : GFn S v), 0 ≤ Bg → Cc * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 ≤ A →
        LocCC S T v A Bg J → LocCC S T v A Bg J' → LocCC S T v A Bg (J + J')

def LocalSquareIntegrableTransfer : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (Cb A₀ : ℝ),
    BuiltOW Cb S T f χ ν' m₀ top A₀ →
    ∀ v,
      ∀ (Bg A ε : ℝ) (J : GFn S v) (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsFrame S T v e → 0 ≤ Bg → 0 < ε →
        Cc * ((S.G.r : ℝ) + 1) ^ 2 * nDim S.G.k S.G.r + 5 * Bg ≤ A → LocCC S T v A Bg J →
        ∀ π, MeasureTheory.IntegrableOn (fun q => ‖MA.evQ (D.parOf S v) (trJ S T v e J π) q‖ ^ 2)
          {q | ε ≤ MA.Gq (D.parOf S v) q} (MA.mu0 (D.parOf S v).r (D.parOf S v).TT)

theorem nDim_nonneg (k r : ℕ) : 0 ≤ nDim k r := by unfold nDim; positivity

theorem mul_mul_le_mul_mul_of_nonneg {a b x y : ℝ} (h : a ≤ b) (hx : 0 ≤ x) (hy : 0 ≤ y) : a * x * y ≤ b * x * y :=
  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h hx) hy

theorem mul_le_of_le_of_mul_le {a b x B : ℝ} (h : a ≤ b) (hx : 0 ≤ x) (hB : b * x ≤ B) : a * x ≤ B :=
  (mul_le_mul_of_nonneg_right h hx).trans hB

theorem jALocCC_of_leaves (h2 : JALocOp) (h3 : JALocAdj) (h4 : JALocPhi) (h5 : JALocAdd) (h8 : LocalSquareIntegrableTransfer) :
    JALocCC := by
  obtain ⟨C2, G2, -, H2⟩ := h2
  obtain ⟨C3, G3, -, H3⟩ := h3
  obtain ⟨G4, -, H4⟩ := h4
  obtain ⟨C5, H5⟩ := h5
  obtain ⟨C8, H8⟩ := h8
  refine ⟨max (max C2 C3) (max C5 C8), max (max G2 G3) (max G4 0), le_max_of_le_right (le_max_right _ _), ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v
  have hr : (0 : ℝ) ≤ (S.G.r : ℝ) + 1 := by positivity
  have hn := nDim_nonneg S.G.k S.G.r
  have hn2 : 0 ≤ nDim S.G.k S.G.r ^ 2 := by positivity
  have hr2 : (0 : ℝ) ≤ ((S.G.r : ℝ) + 1) ^ 2 := by positivity
  have c2 : C2 ≤ max (max C2 C3) (max C5 C8) := le_max_of_le_left (le_max_left _ _)
  have c3 : C3 ≤ max (max C2 C3) (max C5 C8) := le_max_of_le_left (le_max_right _ _)
  have c5 : C5 ≤ max (max C2 C3) (max C5 C8) := le_max_of_le_right (le_max_left _ _)
  have c8 : C8 ≤ max (max C2 C3) (max C5 C8) := le_max_of_le_right (le_max_right _ _)
  have g2 : G2 ≤ max (max G2 G3) (max G4 0) := le_max_of_le_left (le_max_left _ _)
  have g3 : G3 ≤ max (max G2 G3) (max G4 0) := le_max_of_le_left (le_max_right _ _)
  have g4 : G4 ≤ max (max G2 G3) (max G4 0) := le_max_of_le_right (le_max_left _ _)
  refine ⟨fun F A Bg h1 h2 h3 h4 => locCC_JF h1 h2 h3 h4, ?_, ?_, ?_, ?_, fun Bg A c J hJ => locCC_smul c hJ,
    fun Bg A A' J h hJ => locCC_antiA h hJ, ?_⟩
  · intro Θ d Bg A J hd hG hAA hCut hA hJ hFF
    exact H2 E Wp Wq S T f χ ν' m₀ top _ A₀ hB v Θ d Bg A J hd (mul_le_of_le_of_mul_le g2 hr hG) hAA hCut
      (le_trans (by linarith [mul_mul_le_mul_mul_of_nonneg c2 hr hn2]) hA) hJ hFF
  · intro Θ d Bg A J hd hG hAA hCut hA hJ hFF
    exact H3 E Wp Wq S T f χ ν' m₀ top _ A₀ hB v Θ d Bg A J hd (mul_le_of_le_of_mul_le g3 hr hG) hAA hCut
      (le_trans (by linarith [mul_mul_le_mul_mul_of_nonneg c3 hr hn2]) hA) hJ hFF
  · intro φ Bg A J hφ hld hG hJ hFF
    exact H4 E Wp Wq S T f χ ν' m₀ top _ A₀ hB v φ Bg A J hφ hld (mul_le_of_le_of_mul_le g4 hr hG) hJ hFF
  · intro Bg A J J' hBg hA hJ hJ'
    exact H5 E Wp Wq S T f χ ν' m₀ top _ A₀ hB v Bg A J J' hBg (le_trans (mul_mul_le_mul_mul_of_nonneg c5 hr hn2) hA) hJ hJ'
  · intro Bg A ε J e hFr hBg hε hA hJ π
    exact H8 E Wp Wq S T f χ ν' m₀ top _ A₀ hB v Bg A ε J e hFr hBg hε
      (le_trans (by linarith [mul_mul_le_mul_mul_of_nonneg c8 hr2 hn]) hA) hJ π

end Formalism.FourierDecayAlt.P.CutMP.JA

end
end

section

namespace Formalism.FourierDecayAlt.P

theorem ptie_levTransportHer_of_sliceStep (hS : Formalism.FourierDecayAlt.P.PTie.SliceStepHer) : Formalism.FourierDecayAlt.P.PTie.LevTransportHer :=
  ptie_levTransportHer_of jacquet_scaling hS

end Formalism.FourierDecayAlt.P
end
