module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliWordSumExpansion
public import Formalism.HermitianCurvature.StatementD
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LocOfSmoothOnH
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle110
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle113
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHat
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle159
import Formalism.HermitianCurvature.HeisenbergConjugationMeasurePreserving
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle047
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle048
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle129
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle083
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle145
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeisenbergLeviConjugationMeasure
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle158
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormFactor
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LongWeylElement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixMul
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.InsertUnitMatrixZeroApply
public import Formalism.HermitianCurvature.StatementTL
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle162
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle160
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.PartialBesselProperness

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

section auxC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k n : ℕ}

theorem isOpen_dminNe (z z' : Fin (2 * n + k + 1) → ℂ) (i : ℕ) (hi : i ≤ n) :
    IsOpen {g : Q.Mx k n | Dmin k n z z' g ⟨i, by omega⟩ ≠ 0} :=
  isOpen_ne_fun (Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin z z' ⟨i, by omega⟩).continuous continuous_const

theorem uwG_locSupp {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (z z' : Fin (2 * n + k + 1) → ℂ) (i : ℕ)
    (hi : i ≤ n) {H : B.Mat k n → E} {Cs : Set (B.Mat k n)} (hCs : IsClosed Cs)
    (hL : ∀ g ∈ B.GV k n, Dmin k n z z' g ⟨i, by omega⟩ ≠ 0 → CapelliWordSumExpansion.Loc ⊤ H g)
    (hS : ∀ g ∈ B.GV k n, g ∉ Cs → H g = 0) :
    ∀ (w : List C.Letter) (ew : Wd.Ix (Fin w.length)),
      (∀ g ∈ B.GV k n, Dmin k n z z' g ⟨i, by omega⟩ ≠ 0 → CapelliWordSumExpansion.Loc ⊤ (D.uwG k n z z' H i hi w ew) g) ∧
        ∀ g ∈ B.GV k n, g ∉ Cs → D.uwG k n z z' H i hi w ew g = 0 := by
  set Dm : Set (Q.Mx k n) := {g | Dmin k n z z' g ⟨i, by omega⟩ ≠ 0} with hDm
  have hDo : IsOpen Dm := isOpen_dminNe z z' i hi
  have hH : Q.SmoothLev k n 0 Dm H := by
    intro g₀ hg₀
    obtain ⟨U, F, hU, hgU, hF, hE⟩ := hL g₀ hg₀.1.1 hg₀.2
    exact ⟨U, F, hU, hgU, hF, fun g hg hgl => hE g hg hgl.1⟩
  have hSm : ∀ (w : List C.Letter) (ew : Wd.Ix (Fin w.length)),
      Q.SmoothLev k n 0 Dm (D.uwG k n z z' H i hi w ew) := by
    intro w
    induction w with
    | nil => intro ew; exact hH
    | cons l w ih =>
      intro ew
      exact Formalism.FourierDecayAlt.P.SingleEntryHermitianProducts.smooth_vLet z z' i hi l _ hDo (ih _) (fun g hg => hg)
  have hSu : ∀ (w : List C.Letter) (ew : Wd.Ix (Fin w.length)),
      ∀ g ∈ B.GV k n, g ∉ Cs → D.uwG k n z z' H i hi w ew g = 0 := by
    intro w
    induction w with
    | nil => intro ew; exact hS
    | cons l w ih =>
      intro ew g hg hgC
      exact Formalism.FourierDecayAlt.P.PBG.vLet_zero_near z z' i hi l _ _ hCs.isOpen_compl (fun x hx hxG => ih _ x hxG hx) g hgC hg
  intro w ew
  refine ⟨fun g hg hd => ?_, hSu w ew⟩
  obtain ⟨U, F, hU, hgU, hF, hE⟩ := hSm w ew g ⟨Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hg, hd⟩
  exact ⟨U, F, hU, hgU, hF, fun x hx hxG => hE x hx (Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hxG)⟩

end auxC

end Formalism.FourierDecayAlt.P.PartialBesselProperness
end
end

section

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField

noncomputable section

def GaugeExistsQQ : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v, ∃ e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)),
      IsFrame S T v e ∧ IsGauge S T v e ∧ IsGaugeQQ S T v e

def JDecayTrQQ : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
      (L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r),
      IsFrame S T v e → IsGauge S T v e → IsGaugeQQ S T v e → MA.IsModelLevel (D.parOf S v) (MA.DQ (D.parOf S v)) L →
      B.JF (T v).base (f v) ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v) →
      MA.JDecay (D.parOf S v) L (trJ S T v e (B.JF (T v).base (f v))) (2 * S.Ntop + 2)

def JAdjTrQQ : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
      (L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r),
      IsFrame S T v e → IsGauge S T v e → IsGaugeQQ S T v e → MA.IsModelLevel (D.parOf S v) (MA.DQ (D.parOf S v)) L →
      B.JF (T v).base (f v) ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v) →
      MA.JAdj (D.parOf S v) L (trJ S T v e (B.JF (T v).base (f v))) (2 * S.Ntop + 2)

theorem gaugeExistsQQ_of_gCore (hK : Gauge.GCore) : GaugeExistsQQ := by
  refine ⟨0, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v
  exact jdg_exists_of_gCore hK 0 E Wp Wq S T f χ ν' m₀ top A₀ hB v

theorem modelPlaceBuilt3_of_leavesQQ (hMF : MA.ModelFrameAn) (h1 : LamCfgInterlaces) (h2 : AdmInCut)
    (h3 : GaugeExistsQQ) (h4 : RegFF3) (h5 : CVPresFF) (h6 : BesselEigen) (h7 : EnergyTr) (h8 : CutTr)
    (h9 : EnergyReal) (h10 : JDecayTrQQ) (h11 : JAdjTrQQ) : ModelPlaceBuilt3 := by
  obtain ⟨K3, g3⟩ := h3
  obtain ⟨K4, g4⟩ := h4
  obtain ⟨K5, g5⟩ := h5
  obtain ⟨K6, g6⟩ := h6
  obtain ⟨K7, g7⟩ := h7
  obtain ⟨K8, g8⟩ := h8
  obtain ⟨K9, g9⟩ := h9
  obtain ⟨K10, g10⟩ := h10
  obtain ⟨LastRowCutoff, g11⟩ := h11
  refine ⟨max 1 (max K3 (max K4 (max K5 (max K6 (max K7 (max K8 (max K9 (max K10 LastRowCutoff)))))))), ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB hJ hOk hW hW' c hc v
  have hOW : ∀ C', C' ≤ max 1 (max K3 (max K4 (max K5 (max K6 (max K7 (max K8 (max K9 (max K10 LastRowCutoff)))))))) →
      BuiltOW C' S T f χ ν' m₀ top A₀ := fun C' h => ⟨isBuiltPlace_mono h hB, hOk, hW, hW'⟩
  obtain ⟨_, _, _, hIB, hl1, hlk, hGr, hLC, _, _, hk2, _, hOn⟩ := hB
  obtain ⟨e, hF, hG, hQQ⟩ := g3 E Wp Wq S T f χ ν' m₀ top A₀ (hOW K3 (by simp)) v
  have hR := g4 E Wp Wq S T f χ ν' m₀ top A₀ (hOW K4 (by simp)) hJ v
  have hP := g5 E Wp Wq S T f χ ν' m₀ top A₀ (hOW K5 (by simp)) v
  have hE := g6 E Wp Wq S T f χ ν' m₀ top A₀ (hOW K6 (by simp)) v
  have hPOK : (D.parOf S v).OK := (hIB.2 v).2.2.2.1.1
  obtain ⟨L, hL, -⟩ := hMF (D.parOf S v) hPOK (S.l + 1) (by omega) (show S.l + 1 ≤ S.G.k by omega)
  have hI := h1 E Wp Wq S hk2 hOk hW hW' v
  have hlt : S.cutLo v < S.cutHi v := by
    have hv := hLC v
    have hN : (0 : ℝ) < S.Ntop := by unfold C.HidaSetting.Ntop C.Kst; positivity
    have hX : 0 < (S.G.k : ℝ) * S.Ntop * ((S.G.r : ℝ) + 1) ^ 2 + (S.Ntop : ℝ) ^ 2 * ((S.G.r : ℝ) + 1) ^ 2 +
        (S.Ntop : ℝ) ^ 3 := by positivity
    have h1le : (1 : ℝ) ≤ max 1 (max K3 (max K4 (max K5 (max K6 (max K7 (max K8 (max K9 (max K10 LastRowCutoff)))))))) :=
      le_max_left _ _
    nlinarith
  refine ⟨L, trJ S T v e (B.JF (T v).base (f v)), lamCfg S v, 1, 1, hc, one_pos, one_pos,
    ⟨hPOK, by omega, show S.l + 1 ≤ S.G.k by omega, hL, hI.1, hI.2, hlt, hOn v⟩,
    g10 E Wp Wq S T f χ ν' m₀ top A₀ (hOW K10 (by simp)) v e L hF hG hQQ hL hR.1,
    g11 E Wp Wq S T f χ ν' m₀ top A₀ (hOW LastRowCutoff (by simp)) v e L hF hG hQQ hL hR.1, ?_, ?_, ?_⟩
  ·
    intro Y
    rw [← hG _ hR.1 Y, trJ_congr S T v e _ (((S.P v Y : ℝ) : ℂ) • B.JF (T v).base (f v)) (hE Y), trJ_smul]
    funext π
    rw [Pi.smul_apply, ← prod_lamCfg S v Y]
    push_cast
    rfl
  ·
    intro ε hε a ha
    have key : C7.principalHermitianLattice (T v).base (M.sgn (D.parOf S v) (S.l + 1)) a (D.cutF (T v).base χ (f v) ε) =
        MA.ipA (D.parOf S v)
          (MA.actA (D.parOf S v) ((a.reverse.map fun x => Wd.C0 (MA.startM (D.parOf S v) (MA.DQ (D.parOf S v))
            (S.l + 1)).QQ (MA.sites (D.parOf S v) (MA.DQ (D.parOf S v))) (x.2 : ℂ)).prod)
            (MA.chiJ (D.parOf S v) (trJ S T v e (B.JF (T v).base (f v))) c ε))
          (MA.chiJ (D.parOf S v) (trJ S T v e (B.JF (T v).base (f v))) c ε) := by
      rw [g7 E Wp Wq S T f χ ν' m₀ top A₀ (hOW K7 (by simp)) v e hF hP ε hε (hR.2 ε hε) a ha,
        (trJ_foldr S T v e hG hP a.reverse _ (hR.2 ε hε)).2,
        g8 E Wp Wq S T f χ ν' m₀ top A₀ (hOW K8 (by simp)) v e hF hR.1 c hc ε hε]
    have hre := g9 E Wp Wq S T f χ ν' m₀ top A₀ (hOW K9 (by simp)) v ε hε a ha
    rw [key] at hre
    rw [key]
    clear g3 g4 g5 g6 g7 g8 g9 g10 g11 hOW key hE hP hR hG hF hI hQQ
    unfold MA.cutoffEnergyForm
    simp only [one_mul]
    apply Complex.ext
    · simp only [Complex.ofReal_re]
    · simp only [Complex.ofReal_im]
      exact hre
  ·
    intro Lb a ha
    exact level_system_admissible_size S v a ha (h2 E Wp Wq S hGr v a ha) (S.l + 1) L _ c Lb

theorem modelPlaceBuilt3_of_openQQ (h3 : GaugeExistsQQ) (h7 : EnergyTr) (h9 : EnergyReal) (h10 : JDecayTrQQ)
    (h11 : JAdjTrQQ) : ModelPlaceBuilt3 :=
  modelPlaceBuilt3_of_leavesQQ Formalism.FourierDecayAlt.Final.ma_modelFrameAn eigenvalue_configuration_interlaces admissible_in_truncation_holds h3
    regularity_smooth_forms_holds coefficient_vector_preserves_form bessel_eigenvalue_equation_holds h7 cutoff_transport_to_model h9 h10 h11

theorem modelPlaceBuilt3_of_openGC (hK : Gauge.GCore) (h7 : EnergyTr) (h9 : EnergyReal) (h10 : JDecayTrQQ)
    (h11 : JAdjTrQQ) : ModelPlaceBuilt3 :=
  modelPlaceBuilt3_of_openQQ (gaugeExistsQQ_of_gCore hK) h7 h9 h10 h11

theorem modelPlaceBuilt2_of_openQQ (hJ : JfSmoothDS) (hK : Gauge.GCore) (h7 : EnergyTr) (h9 : EnergyReal)
    (h10 : JDecayTrQQ) (h11 : JAdjTrQQ) : JCT.ModelPlaceBuilt2 :=
  modelPlaceBuilt2_of_3 hJ (modelPlaceBuilt3_of_openGC hK h7 h9 h10 h11)

end

end Formalism.FourierDecayAlt.P.CutMP
end

section

open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

variable {k : ℕ}

theorem phi_cont (ρ : ℕ) : Continuous (Dx2.MN.phi (k := k) (ρ := ρ)) := by
  have e : (Dx2.MN.phi (k := k) (ρ := ρ)) = fun x => Dx2.MN.phi x := rfl
  rw [e]
  simp only [Dx2.MN.phi]
  fun_prop

def heisT (ρ : ℕ) (x : B2.HPar k ρ) : Mt k (1 + ρ) := Matrix.of.symm (B2.heis0 k ρ x)

theorem heis_cont (ρ : ℕ) : Continuous (heisT (k := k) ρ) := B2x5.continuous_heis0 k ρ

theorem heis_emb (ρ : ℕ) : MeasurableEmbedding (heisT (k := k) ρ) :=
  (heis_cont ρ).measurableEmbedding (Formalism.FourierDecayAlt.P.heisenberg_subgroup_closed k ρ).1

def phiE (ρ : ℕ) : U.RC k 1 ρ ≃ᵐ B2.HPar k ρ where
  toFun := Dx2.MN.phi
  invFun p := (fun i _ => p.1 i, (fun _ => 0, fun _ => p.2))
  left_inv x := by
    obtain ⟨x1, x2, x3⟩ := x
    simp only [Dx2.MN.phi, Prod.mk.injEq]
    refine ⟨?_, Subsingleton.elim _ _, ?_⟩
    · funext i a; have : a = 0 := Subsingleton.elim _ _; subst this; rfl
    · funext a; have : a = 0 := Subsingleton.elim _ _; subst this; rfl
  right_inv p := by simp [Dx2.MN.phi]
  measurable_toFun := (phi_cont ρ).measurable
  measurable_invFun := by
    apply Continuous.measurable
    exact (continuous_pi fun i => continuous_pi fun _ => (continuous_apply i).comp continuous_fst).prodMk
      (continuous_const.prodMk (continuous_pi fun _ => continuous_snd))

theorem phi_emb (ρ : ℕ) : MeasurableEmbedding (Dx2.MN.phi (k := k) (ρ := ρ)) := by
  exact (phiE ρ).measurableEmbedding

theorem heis_int (ρ : ℕ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Φ : B.Mat k (1 + ρ) → B.Mat k (1 + ρ) → E) :
    ∫ p : Mt k (1 + ρ) × Mt k (1 + ρ), Φ (Matrix.of p.1) (Matrix.of p.2) ∂((B2.μHeis k ρ).prod (B2.μHeis k ρ)) =
      ∫ xx : U.RC k 1 ρ × U.RC k 1 ρ, Φ (U.Rn k 1 ρ xx.1) (U.Rn k 1 ρ xx.2)
        ∂((U.muRC k 1 ρ).prod (U.muRC k 1 ρ)) := by
  have e0 : B2.μHeis k ρ = (volume : Measure (B2.HPar k ρ)).map (heisT ρ) := rfl
  have e1 : (B2.μHeis k ρ).prod (B2.μHeis k ρ) =
      ((volume : Measure (B2.HPar k ρ)).prod volume).map (Prod.map (heisT (k := k) ρ) (heisT ρ)) := by
    rw [e0, Measure.map_prod_map _ _ (heis_emb ρ).measurable (heis_emb ρ).measurable]
  rw [e1, ((heis_emb ρ).prodMap (heis_emb ρ)).integral_map]
  have hmp : MeasurePreserving (Prod.map (Dx2.MN.phi (k := k) (ρ := ρ)) (Dx2.MN.phi (k := k) (ρ := ρ)))
      ((U.muRC k 1 ρ).prod (U.muRC k 1 ρ)) ((volume : Measure (B2.HPar k ρ)).prod volume) := by
    have := (Dx2.MN.phi_mp (k := k) (ρ := ρ)).prod (Dx2.MN.phi_mp (k := k) (ρ := ρ))
    simpa [U.muRC] using this
  rw [← hmp.integral_comp ((phi_emb ρ).prodMap (phi_emb ρ))]
  apply integral_congr_ae
  filter_upwards with xx
  rw [Dx2.MN.rn_heis, Dx2.MN.rn_heis]
  rfl

def conjE {r : ℕ} (b : B.Mat k r) (hb : IsUnit b.det) : Mt k r ≃ᵐ Mt k r where
  toFun := conjM b
  invFun := conjM b⁻¹
  left_inv x := by
    show b⁻¹ * (b * Matrix.of x * b⁻¹) * b⁻¹⁻¹ = Matrix.of x
    rw [Matrix.nonsing_inv_nonsing_inv _ hb]
    simp only [Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul_cancel_left _ _ hb, Matrix.nonsing_inv_mul _ hb, Matrix.mul_one]
  right_inv x := by
    show b * (b⁻¹ * Matrix.of x * b⁻¹⁻¹) * b⁻¹ = Matrix.of x
    rw [Matrix.nonsing_inv_nonsing_inv _ hb]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hb, Matrix.mul_nonsing_inv _ hb, Matrix.mul_one]
  measurable_toFun := B2x5.measurable_conjM b
  measurable_invFun := B2x5.measurable_conjM b⁻¹

theorem heis_conj_int (ρ : ℕ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g g' : B.Mat k ρ}
    (hg : g ∈ B.GV k ρ) (hg' : g' ∈ B.GV k ρ) (Φ : Mt k (1 + ρ) × Mt k (1 + ρ) → E) :
    ∫ p, Φ (conjM ((ιLev k 1 ρ g)⁻¹) p.1, conjM ((ιLev k 1 ρ g')⁻¹) p.2) ∂((B2.μHeis k ρ).prod (B2.μHeis k ρ)) =
      ∫ p, Φ p ∂((B2.μHeis k ρ).prod (B2.μHeis k ρ)) := by
  have := sf_heis (k := k) ρ
  have hu : IsUnit ((ιLev k 1 ρ g)⁻¹).det :=
    Matrix.isUnit_nonsing_inv_det_iff.2 (LongWeylElement.lev_unit _ (HermitianFormFactor.UH_unit (Ux3.hpk_det k ρ) hg))
  have hu' : IsUnit ((ιLev k 1 ρ g')⁻¹).det :=
    Matrix.isUnit_nonsing_inv_det_iff.2 (LongWeylElement.lev_unit _ (HermitianFormFactor.UH_unit (Ux3.hpk_det k ρ) hg'))
  have m1 : MeasurePreserving (conjE _ hu) (B2.μHeis k ρ) (B2.μHeis k ρ) :=
    ⟨(conjE _ hu).measurable, heis_meas_conj_inv ρ hg⟩
  have m2 : MeasurePreserving (conjE _ hu') (B2.μHeis k ρ) (B2.μHeis k ρ) :=
    ⟨(conjE _ hu').measurable, heis_meas_conj_inv ρ hg'⟩
  have := (m1.prod m2).integral_comp ((conjE _ hu).measurableEmbedding.prodMap (conjE _ hu').measurableEmbedding) Φ
  exact this

end Formalism.FourierDecayAlt.P.PBH
end
end

section

open MeasureTheory Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBN

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.P.PBF

section row

variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {n r : ℕ}

theorem unit_matrix_zero_mul_apply (N : SlopeTestRemainingChoices (Fin (n + 1)) A) (i : Fin 2) (e : Ix (Fin n)) (m : Ix (Fin (n + 1))) :
    (eU (0 : Fin (n + 1)) i 0 * N : SlopeTestRemainingChoices (Fin (n + 1)) A) (Fin.cons 0 e) m =
      if (0 : Fin 2) = i then N (Fin.cons 0 e) m else 0 := by
  rw [Matrix.mul_apply]
  simp only [insert_unit_matrix_zero_apply, ite_mul, one_mul, zero_mul]
  by_cases hi : (0 : Fin 2) = i
  · subst hi
    simp
  · simp [hi]

theorem row_sum (col : Fin 2 → SlopeTestRemainingChoices (Fin (n + 1)) A) (N : SlopeTestRemainingChoices (Fin (n + 1)) A) (e : Ix (Fin n))
    (m : Ix (Fin (n + 1))) :
    ((∑ i : Fin 2, eU (0 : Fin (n + 1)) i 0 * col i) * N : SlopeTestRemainingChoices (Fin (n + 1)) A) (Fin.cons 0 e) m =
      (col 0 * N : SlopeTestRemainingChoices (Fin (n + 1)) A) (Fin.cons 0 e) m := by
  rw [Finset.sum_mul, Matrix.sum_apply, Fin.sum_univ_two, mul_assoc, mul_assoc, unit_matrix_zero_mul_apply, unit_matrix_zero_mul_apply]
  simp

theorem io_mul_apply {S : Type} [Fintype S] [DecidableEq S] (x : A) (N : SlopeTestRemainingChoices S A) (z m : Ix S) :
    (io x * N : SlopeTestRemainingChoices S A) z m = x * N z m := by
  rw [io, Matrix.scalar_apply, Matrix.diagonal_mul]

theorem firstRow (hWS : TL.WordStep) (L : LevelData A r) (st : Start A) (hA : TL.AHyp L st) (y : ℂ)
    (u : List (Letter ℂ (Fin n))) (hadm : admitted st (⟨true, 0, y⟩ :: u.map upL)) (e : Ix (Fin n)) :
    ((ofWord L st (⟨true, 0, y⟩ :: u.map upL)).F * TL.bTA L (⟨true, 0, y⟩ :: u.map upL)) (Fin.cons 0 e) e1 =
      TL.aP L y * ((ofWord L st u).F * TL.bTA L u) e e1 := by
  rw [hWS A (Fin (n + 1)) r L st ⟨true, 0, y⟩ (u.map upL) hA hadm (Fin.cons 0 e)]
  rw [(lifted_ofWord L st u).F, bTA_lift, ← liftM_mul]
  dsimp only
  rw [row_sum]
  simp only [TL.letterCol, ↓reduceIte, Matrix.cons_val_zero]
  rw [io_mul_apply, liftM_apply]
  congr 1

end row

section act

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Q.Mx k r → (Wp →L[ℂ] Wp)} {π' : Q.Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]

theorem act_e1Vec (M : SlopeTestRemainingChoices S (Q.Pr (Q.RadSp k r z z' π π'))) (Φ : Q.RadSp k r z z' π π') (x : Ix S) :
    P5.act M (Top.firstStateVector Φ) x = (M x e1).1 Φ := by
  unfold P5.act Top.firstStateVector
  rw [Finset.sum_eq_single (e1 : Ix S)]
  · split_ifs with h
    · rfl
    · exact absurd rfl h
  · intro b _ hb
    have hb' : ¬(b = fun _ => 0) := hb
    simp [hb']
  · intro h
    exact absurd (Finset.mem_univ _) h

end act

theorem cutWord_tail {P : M.Par} {l0 : ℕ} {l : C.Letter} {w : List C.Letter} (h : KB.CutWord P l0 (l :: w)) :
    KB.CutWord P l0 w := by
  refine ⟨fun a => h.1 a.succ, fun a b hab => h.2 a.succ b.succ fun e => hab (Fin.succ_injective _ e)⟩

section main

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem rad_plus (hWS : TL.WordStep) (P : M.Par) (p : KB.Pl P Wp Wq) (X : Q.ActualOps P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π')
    (μ : Measure (Mt P.k P.r)) (L : R.LevelData (Q.Pr (Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π')) P.r)
    (st : Fr.Start (Q.Pr (Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π')))
    (hD : P5.IsData P p.T.base.z p.T.base.z' p.T.base.π p.T.base.π' X μ L st p.l0) (w : List C.Letter) (y : ℝ)
    (hcut : KB.CutWord P p.l0 ((true, y) :: w)) (Φ : Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π')
    (e : Ix (Fin w.length)) :
    P5.act ((Fr.ofWord L st (D.positionted ((true, y) :: w))).F * P5.bTall L (D.positionted ((true, y) :: w)))
        (Top.firstStateVector Φ) (Fin.cons 0 e) =
      (TL.aP L (y : ℂ)).1 (P5.act ((Fr.ofWord L st (D.positionted w)).F * P5.bTall L (D.positionted w)) (Top.firstStateVector Φ) e) := by
  have hA := (Formalism.FourierDecayAlt.P.actual_algebra_facts Wp Wq P _ _ _ _ X μ L st p.l0 hD).1
  have hOK := Formalism.FourierDecayAlt.P.JCTx5.wordOK_of P p.T.base.z p.T.base.z' p.T.base.π p.T.base.π' st p.l0 p.hP.1 p.hl.1
    p.hl.2.1 hD.2.2.2.2.1 hD.2.2.2.2.2.1 ((true, y) :: w) hcut.1 hcut.2
  have hadm := hOK.1
  rw [act_e1Vec, act_e1Vec]
  rw [positioned_cons] at hadm ⊢
  exact congrArg (fun x : Q.Pr _ => x.1 Φ) (firstRow hWS L st hA (y : ℂ) (D.positionted w) hadm e)

end main

end Formalism.FourierDecayAlt.P.PBN

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.PBN

end Formalism.FourierDecayAlt.P
end
end
