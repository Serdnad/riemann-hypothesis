module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle175
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsNormBoundThreeFamilies
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle075
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle050
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle195
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHB2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle200
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableCsmul
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle045
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle083
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CornerBlockActionInvariant
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle198
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHBPts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyZeroNear
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle212
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle113
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsCompactCutoffCoefficient
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle201
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RdVZeroOfVanish
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle147
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPCompactOfStepDensity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle226
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
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CornerBZero

@[expose] public section

section

namespace Formalism.FourierDecayAlt.P.CutBP.GT
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
open Classical

noncomputable def _root_.Formalism.FourierDecayAlt.P.CutBP.GT.FibreTopCpt : Prop :=
  P5.ThmPActualCpt → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (Cb : ℝ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base F → KB.CutWord P p.l0 w →
    ∀ a a' : C.LPt, D.IsLocPt a P.r → D.IsLocPt a' P.r →
      Integrable (fun c : ℂ => TBB.NP p nn F (P.r + 1) w (a ++ [(1, c)]) (a ++ [(1, c)])) ∧
      TBB.NP p nn F P.r w a a' = ∫ c : ℂ, TBB.NP p nn F (P.r + 1) w (a ++ [(1, c)]) (a' ++ [(1, c)])

end
end Formalism.FourierDecayAlt.P.CutBP.GT

namespace Formalism.FourierDecayAlt.P.CutBP
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
open Classical

noncomputable def _root_.Formalism.FourierDecayAlt.P.CutBP.GLFibreCpt : Prop :=
  P5.ThmPActualCpt → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ) (Cb : ℝ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base F → (∀ y, 0 < nn y) →
    ∀ j, j + 1 ≤ P.r → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → ∀ a b : C.LPt, D.IsLocPt a j → D.IsLocPt b j →
      Integrable (fun c : ℂ => TBB.NP p nn F (j + 1) w (a ++ [(1, c)]) (b ++ [(1, c)])) ∧
      ∫ c : ℂ, TBB.NP p nn F (j + 1) w (a ++ [(1, c)]) (b ++ [(1, c)]) = TBB.NP p nn F j w a b

end
end Formalism.FourierDecayAlt.P.CutBP

namespace Formalism.FourierDecayAlt.P.CutBP
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
open Classical

noncomputable def _root_.Formalism.FourierDecayAlt.P.CutBP.GLGramCpt : Prop :=
  P5.ThmPActualCpt → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ) (Cb : ℝ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base F → (∀ y, 0 < nn y) →
    ∀ i, i ≤ P.r → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N →
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H) (Vec : C.LPt → H),
      ∀ a b, TBB.NP p nn F i w a b = ⟪Vec a, Vec b⟫_ℂ

end
end Formalism.FourierDecayAlt.P.CutBP

namespace Formalism.FourierDecayAlt.P.CutBP
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate ENNReal InnerProductSpace
noncomputable section
open Classical

noncomputable def _root_.Formalism.FourierDecayAlt.P.CutBP.GermDataLowAllCpt : Prop :=
  P5.ThmPActualCpt → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (K N : ℕ) (Cb : ℝ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base F → (∀ y, 0 < nn y) →
    GermDataAt (fun i => i ≤ P.r) p nn F Y K N

end
end Formalism.FourierDecayAlt.P.CutBP

namespace Formalism.FourierDecayAlt.P.CutBP
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
open Classical

noncomputable def _root_.Formalism.FourierDecayAlt.P.CutBP.GLContCpt : Prop :=
  P5.ThmPActualCpt → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ) (Cb : ℝ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base F → (∀ y, 0 < nn y) →
    ∀ j m, 1 ≤ m → j + m ≤ P.r → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → ∀ a : C.LPt, D.IsLocPt a j →
      ContinuousOn (fun cc : ℂ × ℂ => TBB.NP p nn F (j + m) w (a ++ [(m, cc.1)]) (a ++ [(m, cc.2)]))
        ({0}ᶜ ×ˢ {0}ᶜ)

end
end Formalism.FourierDecayAlt.P.CutBP

namespace Formalism.FourierDecayAlt.KB
open Finset Filter Topology NumberField MeasureTheory Matrix Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Classical

noncomputable def _root_.Formalism.FourierDecayAlt.KB.PStdCpt : Prop :=
  P5.ThmPActualCpt → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : Pl P Wp Wq) (F) (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter) (h h' : C.LPt)
    (hh : D.IsLocPt h j) (hh' : D.IsLocPt h' j) (Cb : ℝ), InDDplus2 P p.l0 p.T.base Cb p.Θ → CptCoef p.T.base F → CutWord P p.l0 w →
    ∃ φ : ℂ → ℂ, Continuous φ ∧ Integrable φ ∧
      (∀ c : ℂ, c ≠ 0 → φ c = (levW P (j + 1) c : ℂ) * p.RR F (j + 1) w (h ++ [(1, c)]) (h' ++ [(1, c)])) ∧
      ∀ s : ℂ, ∫ c, P5.fsv s c * φ c =
        p.form j hj w (waveG (p.T.bs j) s w (slv p.T F j hj w h hh.2)) (slv p.T F j hj w h' hh'.2)

end
end Formalism.FourierDecayAlt.KB

namespace Formalism.FourierDecayAlt.P.TBBx5
open Formalism.FourierDecayAlt

noncomputable def _root_.Formalism.FourierDecayAlt.P.TBBx5.CurvatureIntegralOfPartsCpt : Prop :=
  P5.ThmPActualCpt → KB.PStdCpt → KB.VIsoCpt → KB.SizeStdCpt → KB.DegWave → PBL.FormPosCpt →
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (Λ : ℝ) (K N : ℕ) (Cb : ℝ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base F → (∀ y, 0 < nn y) → WaveGrid p nn Y Λ K N →
    TBB.KernelFourierIntegralBound p nn F Y Λ K N

end Formalism.FourierDecayAlt.P.TBBx5

namespace Formalism.FourierDecayAlt.P.TBBx5
open Formalism.FourierDecayAlt

noncomputable def _root_.Formalism.FourierDecayAlt.P.TBBx5.IntegralFourFromComponentsCpt : Prop :=
  P5.ThmPActualCpt → KB.SizeStdCpt → KB.DegLift → PBL.FormPosCpt →
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (Λ : ℝ) (K N : ℕ),
    KB.CptCoef p.T.base F → (∀ y, 0 < nn y) → LiftGrid p nn Y Λ K N → TBB.KernelArgumentHypothesisScalar p nn F Y Λ K N

end Formalism.FourierDecayAlt.P.TBBx5

namespace Formalism.FourierDecayAlt.P.CutBP
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
open Classical

noncomputable def _root_.Formalism.FourierDecayAlt.P.CutBP.GLGermCpt : Prop :=
  P5.ThmPActualCpt → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ) (Cb : ℝ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base F → (∀ y, 0 < nn y) →
    ∀ b s : ℕ, 1 ≤ b → 2 ≤ s → b + s - 1 ≤ P.r → ∀ h : C.LPt, D.IsLocPt h (b - 1) →
    ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (Vec : C.LPt → H),
      (∀ a a', TBB.NP p nn F (b + s - 1) w a a' = ⟪Vec a, Vec a'⟫_ℂ) →
      ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → ∃ C : ℝ, ∀ x : ℂ, x ≠ 0 → ∀ D ∈ K,
        ‖((((Real.pi ^ (s - 1))⁻¹ * ‖x‖ ^ (s - 1) : ℝ) : ℂ) • Vec (h ++ [(s - 1, x⁻¹), (1, x ^ (s - 1) * D)])) -
          ∑ z ∈ G.rootSet s ((-1) ^ (s + 1) * D),
            G.psi (-U.betaU) ((s : ℂ) * z * x) • (((((s : ℝ) * ‖z‖ ^ (s - 1))⁻¹ : ℝ) : ℂ) • Vec (h ++ [(s, z)]))‖ ≤
          C * ‖x‖⁻¹

end
end Formalism.FourierDecayAlt.P.CutBP

namespace Formalism.FourierDecayAlt.P.CutBP
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
noncomputable section

noncomputable def _root_.Formalism.FourierDecayAlt.P.CutBP.NFTopFormAllCpt : Prop :=
  P5.ThmPActualCpt → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (Y : Finset ℝ) (N : ℕ),
    NFHyp Cb Cc p f A₀ p₀ χ N → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N →
      NFTopForm p χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) w

end
end Formalism.FourierDecayAlt.P.CutBP

namespace Formalism.FourierDecayAlt.P.CutBP
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate ENNReal InnerProductSpace
noncomputable section
open Classical

noncomputable def _root_.Formalism.FourierDecayAlt.P.CutBP.GermDataTopAllCpt : Prop :=
  P5.ThmPActualCpt → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (K N : ℕ) (Cb : ℝ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base F → (∀ y, 0 < nn y) →
    GermDataAt (fun i => i = P.r + 1) p nn F Y K N

end
end Formalism.FourierDecayAlt.P.CutBP
end

section

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutHB

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates Formalism.FourierDecayAlt.P.PBQ

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def ProperDomP : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (j : ℕ) (hj : j ≤ P.r) (Cs : Set (B.Mat P.k P.r)), IsCompact Cs →
    PartialBesselProperness.Proper (p.T.bs j) p.T.base (by omega : j + (P.r - j) = P.r) Cs (domP P.k P.r j p.T.base.z p.T.base.z')

theorem zxH_rfl (h : C.LPt) (v : XH h) : zxH h (D.ptSize h) rfl v = LeftFubiniLemmas.lhOf (D.ptPerm h) v *
    U.hMat (D.ptPerm h) (D.ptDiag h) := by
  first
  | rfl
  | simp [zxH]

theorem supp_of (hW : PartialBesselProperness.PbWords) (hP : ProperDomP) : Supp := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj w h hh γ hF hw hγ hΩ K _ hK0
  obtain ⟨hh1, hh2⟩ := hh
  subst hh2
  have hhh : D.IsLocPt h (D.ptSize h) := ⟨hh1, rfl⟩
  obtain ⟨R, hR⟩ := hF.2.1
  set Cs : Set (B.Mat P.k P.r) := {g | B.gN g ≤ R} with hCs
  have hCc : IsCompact Cs := Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le P.k P.r R
  have e : D.ptSize h + (P.r - D.ptSize h) = P.r := by omega
  have hd : ∀ i, D.ptDiag h i ≠ 0 := ptDiag_ne hhh

  have hR1 : ∀ ew : Wd.Ix (Fin w.length), ∃ R1 : ℝ, ∀ v : XH h, R1 < ‖v‖ → ∀ g ∈ B.GV P.k P.r,
      U.Zh P.k (D.ptSize h) (P.r - D.ptSize h) (D.castM e.symm g) =
        LeftFubiniLemmas.lhOf (D.ptPerm h) v * U.hMat (D.ptPerm h) (D.ptDiag h) →
      pbF (p.T.bs (D.ptSize h)) p.T.base e
        (D.uwG P.k P.r p.T.base.z p.T.base.z' F (D.ptSize h) (by omega) w ew) g = 0 := by
    intro ew
    refine pb_head_support (p.T.bs (D.ptSize h)) p.T.base e (D.ptPerm h) (D.ptDiag h) hd _ Cs hCc ?_
    intro g hg hgC
    by_contra hne
    exact hgC (Formalism.FourierDecayAlt.P.PBG.uwG_supp p.T.base.z p.T.base.z' F R hR (D.ptSize h) (by omega) w ew g hg hne)
  choose R1 hR1 using hR1
  refine ⟨⋃ ew, Metric.closedBall (0 : XH h) (R1 ew), isCompact_iUnion fun ew => isCompact_closedBall _ _,
    fun v hv τ hτK ew => ?_⟩
  have hτ : τ ≠ 0 := hK0 hτK
  have hvR : R1 ew < ‖v‖ := by
    by_contra hle
    have hle : ‖v‖ ≤ R1 ew := not_lt.mp hle
    exact hv (Set.mem_iUnion.2 ⟨ew, by rw [Metric.mem_closedBall, dist_zero_right]; exact hle⟩)
  have hpt := pts Wp Wq P p (D.ptSize h) hj h hhh γ hγ hΩ v
  have hyD := hpt.2 τ hτ
  have hyG := x0_GV hj hpt.1 hτ hγ
  have hz : p.T.base.z = D.castV e (liftVec P.k (D.ptSize h) (P.r - D.ptSize h) (p.T.bs (D.ptSize h)).z) :=
    (p.T.z_lev (D.ptSize h) (by omega)).symm
  have hPW := hW P.k (D.ptSize h) (P.r - D.ptSize h) P.r Wp Wq (p.T.bs (D.ptSize h)) p.T.base e hz (D.ptSize h)
    (by omega) F Cs (fun g hg _ => hF.1 g hg) hCc
    (fun g hg hgC => by
      by_contra hne
      exact hgC (hR g hg hne))
    (domP P.k P.r (D.ptSize h) p.T.base.z p.T.base.z') (isOpen_domP _ _ _ _ _)
    (fun g hg => hg.1 ⟨D.ptSize h, by omega⟩ (show D.ptSize h ≤ D.ptSize h from le_rfl) (show D.ptSize h ≤ P.r by omega))
    (hP Wp Wq P p (D.ptSize h) (by omega) Cs hCc) w ew _ hyD hyG
  unfold phf
  unfold pbT
  rw [hPW]
  refine hR1 ew v hvR _ hyG ?_
  rw [leading_block_of_base_point hj _ τ γ e.symm, zxH_rfl]

end Formalism.FourierDecayAlt.P.CutHB
end
end

section

open Matrix MeasureTheory Filter Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutEXPbSupp

section gen

variable {k p ρ n : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem exists_orbit (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq) (e : p + ρ = n)
    (H : B.Mat k n → (Wq →L[ℂ] Wp)) (g0 : B.Mat k n) (h : PBQ.pbF Bj B0 e H g0 ≠ 0) :
    ∃ x, PBQ.GoodP Bj x ∧ ∃ ξ : Mt k n × Mt k n, PBG.InR B0 ξ ∧
      H (D.castM e (PBQ.sP Bj x) * g0 * Matrix.of ξ.2 * Matrix.of ξ.1) ≠ 0 := by
  by_contra hno
  push Not at hno
  apply h
  unfold PBQ.pbF
  rw [← integral_zero (PBQ.XP k p ρ) (Wq →L[ℂ] Wp)]
  refine integral_congr_ae ?_
  filter_upwards [PBQ.ae_goodP (p := p) Bj] with x hx
  show PBQ.pbI Bj B0 e H g0 x = 0
  unfold PBQ.pbI
  have hK : PBG.Kr B0 H (D.castM e (PBQ.sP Bj x) * g0) = 0 := by
    unfold PBG.Kr
    rw [← integral_zero (Mt k n × Mt k n) (Wq →L[ℂ] Wp)]
    refine integral_congr_ae ?_
    filter_upwards [PBG.ae_inR B0] with ξ hξ
    show _ = 0
    rw [hno x hx ξ hξ, ContinuousLinearMap.zero_comp, smul_zero]
  rw [hK, ContinuousLinearMap.comp_zero, smul_zero]

theorem norm_entry_le_gN (g : B.Mat k n) (i j : Fin (2 * n + k + 1)) : ‖g i j‖ ≤ B.gN g := by
  unfold B.gN
  rw [Complex.norm_def]
  refine Real.sqrt_le_sqrt ?_
  calc Complex.normSq (g i j) ≤ ∑ j', Complex.normSq (g i j') :=
        Finset.single_le_sum (f := fun j' => Complex.normSq (g i j')) (fun _ _ => Complex.normSq_nonneg _)
          (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', Complex.normSq (g i' j') :=
        Finset.single_le_sum (f := fun i' => ∑ j', Complex.normSq (g i' j'))
          (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ i)

theorem orbit_gen (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq) (e : p + ρ = n)
    (hz : B0.z = D.castV e (liftVec k p ρ Bj.z))
    (Z : Matrix (Fin p) (Fin p) ℂ) (μ : B.Mat k ρ) (hZ : Z.det ≠ 0) (hμ : μ ∈ B.GV k ρ)
    (x : PBQ.XP k p ρ) (hx : PBQ.GoodP Bj x) (ξ : Mt k n × Mt k n) (hξ : PBG.InR B0 ξ) (g : B.Mat k n)
    (hg : g = D.castM e (PBQ.sP Bj x) * D.castM e (U.mMap k p ρ Z μ) * Matrix.of ξ.2 * Matrix.of ξ.1) :
    g ∈ B.GV k n ∧ (∃ u : Matrix (Fin p) (Fin p) ℂ, Formalism.DoubleCosetMeasures.IsUpUni u ∧ ∀ a b, ‖(Z * u) a b‖ ≤ B.gN g) ∧
      (∀ l, Dmin k n B0.z B0.z' g l = Dmin k n B0.z B0.z' (D.castM e (U.mMap k p ρ Z μ)) l) ∧
      Gf k n B0.z B0.z' g = Gf k n B0.z B0.z' (D.castM e (U.mMap k p ρ Z μ)) := by
  subst e
  simp only [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl] at hg ⊢
  rw [Formalism.FourierDecayAlt.P.JCTx5.castV_rfl] at hz
  have hm : U.mMap k p ρ Z μ ∈ B.GV k (p + ρ) := (Formalism.FourierDecayAlt.P.slice_membership k p ρ).1 Z μ hZ hμ
  refine ⟨?_, ?_, ?_⟩
  · rw [hg]
    exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (PartialBesselProperness.sP_GV Bj x) hm) hξ.2.1)
      hξ.1.1
  · refine ⟨G.upper (fun q : G.UT p => (Matrix.of ξ.2 : B.Mat k (p + ρ)) ⟨q.1.1.val, by omega⟩ ⟨q.1.2.val, by omega⟩),
      LeftFubiniLemmas.upper_isUpUni _, fun a b => ?_⟩
    have hZh : U.Zh k p ρ g = Z * G.upper (fun q : G.UT p =>
        (Matrix.of ξ.2 : B.Mat k (p + ρ)) ⟨q.1.1.val, by omega⟩ ⟨q.1.2.val, by omega⟩) := by
      have e0 := Formalism.FourierDecayAlt.P.hat_z_on_slice k p ρ 0 0 Z μ
      rw [LeftFubiniLemmas.rn_zero, inv_one, Matrix.one_mul, Matrix.mul_one] at e0
      rw [hg, PBQ.zh_mul_UW _ _ _ hξ.1, LeftFubiniLemmas.zh_mul_N _ _ hξ.2, PBQ.zh_sP_mul, e0,
        PBQ.nblk_upper _ hξ.2]
    rw [← hZh]
    exact norm_entry_le_gN g _ _
  · obtain ⟨h, hh, m, hmN, hs⟩ := PartialBesselProperness.leftFactor_mem Bj x
    rw [← hz] at hh
    have hhu : IsUnit h.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hh.1
    have hmu : IsUnit m.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hmN.1
    set pp : B.SS k (p + ρ) := ((Matrix.of.symm h⁻¹, Matrix.of.symm m⁻¹), ξ) with hpp
    have hin : B0.inSS pp := ⟨Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh, Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_inv hmN, hξ.1, hξ.2⟩
    have hsg : B.sgs pp (U.mMap k p ρ Z μ) = g := by
      rw [hg, hs]
      simp only [B.sgs, hpp]
      change (h⁻¹)⁻¹ * (m⁻¹)⁻¹ * U.mMap k p ρ Z μ * Matrix.of ξ.2 * Matrix.of ξ.1 = _
      rw [Matrix.nonsing_inv_nonsing_inv _ hhu, Matrix.nonsing_inv_nonsing_inv _ hmu]
    refine ⟨fun l => ?_, ?_⟩
    · rw [← hsg]; exact Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs B0 hin _ l
    · rw [← hsg]; exact Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs B0 hin _

end gen

theorem gf_castM {k a b : ℕ} (e : a = b) (z z' : Fin (2 * b + k + 1) → ℂ) (g : B.Mat k a) :
    Gf k b z z' (D.castM e g) = Gf k a (D.castV e.symm z) (D.castV e.symm z') g := by
  subst e
  rw [Formalism.FourierDecayAlt.P.JCTx5.castM_rfl, Formalism.FourierDecayAlt.P.JCTx5.castV_rfl, Formalism.FourierDecayAlt.P.JCTx5.castV_rfl]

theorem castV_castV' {k a b c : ℕ} (h1 : a = b) (h2 : b = c) (v : Fin (2 * a + k + 1) → ℂ) :
    D.castV h2 (D.castV h1 v) = D.castV (h1.trans h2) v := by
  subst h1 h2; rfl

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem lowV_top {P : M.Par} (p : KB.Pl P Wp Wq) (e : P.r + (P.r - P.r) = P.r) :
    U.lowV P.k P.r (P.r - P.r) (D.castV e.symm p.T.base.z) = (p.T.bs P.r).z ∧
      U.lowV P.k P.r (P.r - P.r) (D.castV e.symm p.T.base.z') = (p.T.bs P.r).z' := by
  unfold D.LevTower.base
  rw [← p.T.z_lev P.r le_rfl, ← p.T.z'_lev P.r le_rfl, castV_castV', castV_castV']
  exact ⟨Formalism.FourierDecayAlt.P.JCTx6.Link2.lowV_liftVec rfl _ _, Formalism.FourierDecayAlt.P.JCTx6.Link2.lowV_liftVec rfl _ _⟩

theorem orbit_point {P : M.Par} (p : KB.Pl P Wp Wq) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (Z : Matrix (Fin P.r) (Fin P.r) ℂ) (μ : B.Mat P.k (P.r - P.r)) (hZ : Z.det ≠ 0)
    (hμ : μ ∈ Q.Glev P.k (P.r - P.r) (Fin.last _)) (h : CutEX.pbTop p G Z μ ≠ 0) :
    ∃ g ∈ B.GV P.k P.r, G g ≠ 0 ∧ ∃ u : Matrix (Fin P.r) (Fin P.r) ℂ, Formalism.DoubleCosetMeasures.IsUpUni u ∧
      (∀ a b, ‖(Z * u) a b‖ ≤ B.gN g) ∧ Dmin P.k P.r p.T.base.z p.T.base.z' g ⟨P.r, by omega⟩ = Z.det ∧
      Gf P.k P.r p.T.base.z p.T.base.z' g =
        Complex.normSq Z.det * Gf P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' μ := by
  have e : P.r + (P.r - P.r) = P.r := by omega
  have hμGV : μ ∈ B.GV P.k (P.r - P.r) := hμ.1
  unfold CutEX.pbTop PBQ.pbT at h
  obtain ⟨x, hx, ξ, hξ, hG⟩ := exists_orbit _ _ _ _ _ h
  have hz : p.T.base.z = D.castV e (liftVec P.k P.r (P.r - P.r) (p.T.bs P.r).z) := (p.T.z_lev P.r le_rfl).symm
  obtain ⟨hGV, ⟨u, hu, hb⟩, hD, hGf⟩ := orbit_gen (p.T.bs P.r) p.T.base e hz Z μ hZ hμGV x hx ξ hξ _ rfl
  refine ⟨_, hGV, hG, u, hu, hb, ?_, ?_⟩
  · rw [hD]
    rw [Formalism.FourierDecayAlt.P.PBI.dmin_castM e _ _ _ P.r (by omega) (by omega), Formalism.FourierDecayAlt.P.hat_z_minimum_degree P.k P.r (P.r - P.r)]
    have e0 := Formalism.FourierDecayAlt.P.hat_z_on_slice P.k P.r (P.r - P.r) 0 0 Z μ
    rw [Formalism.FourierDecayAlt.P.LeftFubiniLemmas.rn_zero, inv_one, Matrix.one_mul, Matrix.mul_one] at e0
    unfold U.DjU
    rw [e0]
  · rw [hGf, gf_castM e]
    have hz0 := Formalism.FourierDecayAlt.P.PBH.inWb_castV e.symm p.T.base.z_mem
    have hz0' := Formalism.FourierDecayAlt.P.PBH.inWb_castV e.symm p.T.base.z'_mem
    have hG0 := Formalism.FourierDecayAlt.P.level_function_slice P.k P.r (P.r - P.r) _ _ hz0 hz0' 0 0 Z μ
    rw [Formalism.FourierDecayAlt.P.LeftFubiniLemmas.rn_zero, inv_one, Matrix.one_mul, Matrix.mul_one] at hG0
    obtain ⟨hl1, hl2⟩ := lowV_top p e
    rw [hG0, hl1, hl2]

end Formalism.FourierDecayAlt.P.CutEXPbSupp
end
end

section

namespace Formalism.FourierDecayAlt.P5.HerD

theorem thmPActualCpt_of_stepExp0 (h0 : StepExp0) : ThmPActualCpt :=
  theorem_P_compact_of_step_density Formalism.FourierDecayAlt.P.level_transport_hermitian h0

end Formalism.FourierDecayAlt.P5.HerD
end
