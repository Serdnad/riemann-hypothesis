module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutMP2
public import Formalism.HermitianCurvature.Bundle004
public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField

noncomputable section

def GlobCoef {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Θ : B.DiffOp k r Wp Wq) (d : ℝ) : Prop :=
  ∀ Tm ∈ Θ, B.CkOn ⊤ (B.GV k r) Tm.coef ∧ B.CkOn ⊤ (B.GV k r) Tm.coefAdj ∧
    ∀ m : ℕ, ∃ Cb : ℝ, ∀ u w : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ w, B.unitLie k r X) →
      u.length + w.length ≤ m → ∀ g ∈ B.GV k r,
        ‖B.dLR u w Tm.coef g‖ ≤ Cb * B.gN g ^ d ∧ ‖B.dLR u w Tm.coefAdj g‖ ≤ Cb * B.gN g ^ d

def nDim (k r : ℕ) : ℝ := ((2 * r + k + 1 : ℕ) : ℝ)

def bddHat (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r) : Set (MA.A P (MA.DQ P)) :=
  {x | ∃ b ∈ Submonoid.closure (MA.bddSet P L), ∃ X ∈ MA.hatSet P L, x = b * X}

def JDHatBdd : Prop :=
  ∀ (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r), 0 ≤ P.TT → MA.IsModelLevel P (MA.DQ P) L →
    ∀ X ∈ MA.hatSet P L, ∀ b ∈ Submonoid.closure (MA.bddSet P L), X * b ∈ Submodule.span ℂ (bddHat P L)

def JDHatOp : Prop :=
  ∃ Cc : ℝ, 0 ≤ Cc ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
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
      IsFrame S T v e → IsGauge S T v e → MA.IsModelLevel (D.parOf S v) (MA.DQ (D.parOf S v)) L →
      ∀ X ∈ MA.hatSet (D.parOf S v) L,
        ∃ ts : List (MA.A (D.parOf S v) (MA.DQ (D.parOf S v)) × B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))),
          (∀ t ∈ ts, t.1 ∈ Submonoid.closure (MA.bddSet (D.parOf S v) L) ∧ B.SmoothCoef (B.GPos (T v).base) t.2 ∧
            B.Commutes (T v).base (B.GPos (T v).base) t.2 ∧
            GlobCoef t.2 (Cc * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r) ∧ (B.opOrder t.2 : ℝ) ≤ Cc * nDim S.G.k S.G.r) ∧
          ∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v),
            MA.actA (D.parOf S v) X (trJ S T v e J) =
              (ts.map fun t => MA.actA (D.parOf S v) t.1 (trJ S T v e (B.opApply t.2 J))).sum

def JDJComm : Prop :=
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
    ∀ v (Θ : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))) (d A : ℝ), 0 ≤ d →
      B.SmoothCoef (B.GPos (T v).base) Θ → B.Commutes (T v).base (B.GPos (T v).base) Θ → GlobCoef Θ d →
      Cc * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 + 6 * (S.G.r : ℝ) * (B.opOrder Θ : ℝ) + d ≤ A →
      ∀ F : B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)), B.CkOn ⊤ (B.GV S.G.k S.G.r) F →
        (∀ m : ℕ, B.InCC A m F) → B.JF (T v).base F ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v) →
        B.JF (T v).base (B.opApply Θ F) ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v) ∧
          ∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT,
            B.opApply Θ (B.JF (T v).base F) (B.gq (T v).base x) = B.JF (T v).base (B.opApply Θ F) (B.gq (T v).base x)

def JDCCLower : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Θ : B.DiffOp k r Wp Wq) (d A : ℝ),
    0 ≤ d → GlobCoef Θ d → ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) F → (∀ m : ℕ, B.InCC A m F) →
      B.CkOn ⊤ (B.GV k r) (B.opApply Θ F) ∧ ∀ m : ℕ, B.InCC (A - d) m (B.opApply Θ F)

def TransferSquareIntegrable : Prop :=
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
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsFrame S T v e →
      ∀ A : ℝ, Cc * ((S.G.r : ℝ) + 1) ^ 2 * nDim S.G.k S.G.r ≤ A →
      ∀ F : B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)), B.CkOn ⊤ (B.GV S.G.k S.G.r) F →
        (∀ m : ℕ, B.InCC A m F) → B.JF (T v).base F ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v) →
        ∀ π, MeasureTheory.Integrable
          (fun q => ‖MA.evQ (D.parOf S v) (trJ S T v e (B.JF (T v).base F) π) q‖ ^ 2) (MA.mu0 (D.parOf S v).r (D.parOf S v).TT)

def BoundedOperatorsSquareIntegrable : Prop :=
  ∀ (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r), 0 < P.TT → MA.IsModelLevel P (MA.DQ P) L →
    ∀ b ∈ Submonoid.closure (MA.bddSet P L), ∀ u : M.Ty P → MA.SmQ P.r P.TT,
      (∀ π, MeasureTheory.Integrable (fun q => ‖MA.evQ P (u π) q‖ ^ 2) (MA.mu0 P.r P.TT)) →
      ∀ π, MeasureTheory.Integrable (fun q => ‖MA.evQ P (MA.actA P b u π) q‖ ^ 2) (MA.mu0 P.r P.TT)

end

end Formalism.FourierDecayAlt.P.CutMP
end

section

open Formalism.FourierDecayAlt MeasureTheory
open Formalism.REAL Formalism.QuantumDeterminants
open NumberField

namespace Formalism.FourierDecayAlt.P.CutMP.En

noncomputable section

def foldCV (k r : ℕ) {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (s : ℂ) (a : List C.Letter)
    (H : B.Mat k r → E) : B.Mat k r → E :=
  a.foldr (fun x J => s • Q.CV k r (x.2 : ℂ) J) H

def CVLocal : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (U : Set (B.Mat k r)) (f₁ f₂ : B.Mat k r → E)
    (Y : ℂ), IsOpen U → B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (U ∩ B.GV k r) f₁ →
    B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (U ∩ B.GV k r) f₂ → (∀ g ∈ U ∩ B.GV k r, f₁ g = f₂ g) →
    ∀ g ∈ U ∩ B.GV k r, Q.CV k r Y f₁ g = Q.CV k r Y f₂ g

def FoldRev : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp))
    (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) (Dm : Set (Q.Mx k r)), IsOpen Dm →
    (∀ J ∈ Q.FFl k r z z' π π' 0 Dm, ∀ (Y : ℝ) (s : ℂ), s • Q.CV k r (Y : ℂ) J ∈ Q.FFl k r z z' π π' 0 Dm) →
    ∀ J ∈ Q.FFl k r z z' π π' 0 Dm, ∀ (s : ℂ) (a : List C.Letter), ∀ g ∈ Q.Glev k r 0 ∩ Dm,
      foldCV k r s a.reverse J g = foldCV k r s a J g

def AdmLen : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq) (v : Fin S.f)
    (a : List C.Letter), D.AdmAt S v a → a.length ≤ S.Ntop

def CVInCC : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (A : ℝ) (m : ℕ) (F : B.Mat k r → E) (Y s : ℂ),
    B.InCC A (m + (2 * r + k + 1)) F → B.InCC A m (s • Q.CV k r Y F)

def BesselFoldBuilt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW 100 S T f χ ν' m₀ top A₀ →
    ∀ v, (∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v), ∀ (Y : ℝ) (s : ℂ), s • Q.CV S.G.k S.G.r (Y : ℂ) J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v)) →
      ∀ ε : ℝ, 0 < ε → B.JF (T v).base (D.cutF (T v).base χ (f v) ε) ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v) →
      ∀ a : List C.Letter, a.length ≤ S.Ntop → ∀ g ∈ JF.Om S.G.k S.G.r (T v).base.z (T v).base.z',
        B.JF (T v).base (foldCV S.G.k S.G.r (M.sgn (D.parOf S v) (S.l + 1)) a (D.cutF (T v).base χ (f v) ε)) g =
          foldCV S.G.k S.G.r (M.sgn (D.parOf S v) (S.l + 1)) a (B.JF (T v).base (D.cutF (T v).base χ (f v) ε)) g

def L2BoundAtTowerPlace : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW 100 S T f χ ν' m₀ top A₀ →
    ∀ v, ∀ ε : ℝ, 0 < ε → ∀ a : List C.Letter, a.length ≤ S.Ntop →
      B.normSq (T v).base (foldCV S.G.k S.G.r (M.sgn (D.parOf S v) (S.l + 1)) a (D.cutF (T v).base χ (f v) ε)) ≠ ⊤

def FibMem : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f), Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' →
    ∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v),
      ∀ q ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT,
        J (B.gq (T v).base q) ∈ NF.Fib S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec (T v).base.π (T v).base.π' q.2

def TrSmooth : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f), Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' →
    ∀ (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsFrame S T v e →
    ∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v), ∀ ρ,
      (fun q : MA.Qp (D.parOf S v).r (D.parOf S v).TT =>
        ((Real.sqrt (MA.wq S.G.k q.1 (D.parOf S v).TT) : ℝ) : ℂ) *
          inner ℂ (B.hsVec (e ρ q.1.2)) (B.hsVec (J (B.gq (T v).base q.1)))) ∈ MA.smSub (D.parOf S v).r (D.parOf S v).TT

def BetaFrame : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f), Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' →
    ∀ (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsFrame S T v e →
    ∀ J₁ ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v),
    ∀ J₂ ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v),
      jNormSq S.G.k S.G.r (Tz S.G.k S.G.r (T v).base.z) (Tz S.G.k S.G.r (T v).base.z')
          (fun q => B.hsVec (J₁ (B.gq (T v).base q))) ≠ ⊤ →
      jNormSq S.G.k S.G.r (Tz S.G.k S.G.r (T v).base.z) (Tz S.G.k S.G.r (T v).base.z')
          (fun q => B.hsVec (J₂ (B.gq (T v).base q))) ≠ ⊤ →
      betaBig S.G.k S.G.r (Tz S.G.k S.G.r (T v).base.z) (Tz S.G.k S.G.r (T v).base.z') (T v).base.μsec
          (fun g => B.hsVec (J₁ g)) (fun g => B.hsVec (J₂ g)) =
        MA.ipA (D.parOf S v) (trJ S T v e J₁) (trJ S T v e J₂)

end

end Formalism.FourierDecayAlt.P.CutMP.En
end

section

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBO

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.P5

theorem norm_fsv (a t : ℂ) : ‖fsv a t‖ = 1 := by
  unfold fsv
  rw [Complex.norm_exp]
  have : (a * t - conj a * conj t).re = 0 := by
    simp [Complex.mul_re, Complex.sub_re, Complex.conj_re, Complex.conj_im]
  rw [this, Real.exp_zero]

theorem continuous_fsv₂ : Continuous (fun q : ℂ × ℂ => fsv q.1 q.2) := by
  unfold fsv
  exact Complex.continuous_exp.comp ((continuous_fst.mul continuous_snd).sub
    ((Complex.continuous_conj.comp continuous_fst).mul (Complex.continuous_conj.comp continuous_snd)))

theorem integrable_fsv_mul {φ : ℂ → ℂ} (hφ : Continuous φ) (hi : Integrable φ) (a : ℂ) :
    Integrable (fun t => fsv a t * φ t) := by
  refine hi.bdd_mul (c := 1) ?_ (Filter.Eventually.of_forall fun t => (norm_fsv a t).le)
  exact (continuous_fsv₂.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable

theorem continuous_transform {φ : ℂ → ℂ} (hφ : Continuous φ) (hi : Integrable φ) :
    Continuous (fun s : ℂ => ∫ t, fsv s t * φ t) := by
  refine continuous_of_dominated (bound := fun t => ‖φ t‖) (fun s => ?_) (fun s => ?_) hi.norm ?_
  · exact ((continuous_fsv₂.comp (continuous_const.prodMk continuous_id)).mul hφ).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun t => by rw [norm_mul, norm_fsv, one_mul]
  · exact Filter.Eventually.of_forall fun t =>
      (continuous_fsv₂.comp (continuous_id.prodMk continuous_const)).mul continuous_const

theorem integrable_decay3' : Integrable (fun s : ℂ => ((1 + ‖s‖) ^ 3)⁻¹) := by
  have hd : Integrable (fun t : ℂ => (1 + ‖t‖) ^ (-(3 : ℝ))) volume := by
    refine integrable_one_add_norm ?_
    rw [Complex.finrank_real_complex]; norm_num
  refine hd.congr (Filter.Eventually.of_forall fun t => ?_)
  have h1 : (0 : ℝ) < 1 + ‖t‖ := by positivity
  simp only []
  rw [Real.rpow_neg h1.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

theorem integral_norm_le_decay {Ξ : ℂ → ℂ} (hΞ : Continuous Ξ) {K : ℝ} (hK : ∀ s, ‖Ξ s‖ ≤ K * ((1 + ‖s‖) ^ 3)⁻¹) :
    Integrable Ξ ∧ ∫ s, ‖Ξ s‖ ≤ K * ∫ s : ℂ, ((1 + ‖s‖) ^ 3)⁻¹ := by
  have hint : Integrable Ξ :=
    Integrable.mono' (integrable_decay3'.const_mul K) hΞ.aestronglyMeasurable (Filter.Eventually.of_forall hK)
  refine ⟨hint, ?_⟩
  rw [← integral_const_mul]
  exact integral_mono hint.norm (integrable_decay3'.const_mul K) hK

theorem fsv_sigma {c : ℂ} (hc : c ≠ 0) :
    fsv (Complex.I * (Real.pi : ℂ) / (2 * c)) c = -1 ∧
      ‖Complex.I * (Real.pi : ℂ) / (2 * c)‖ = Real.pi / (2 * ‖c‖) := by
  constructor
  · unfold fsv
    have e1 : Complex.I * (Real.pi : ℂ) / (2 * c) * c = Complex.I * (Real.pi / 2 : ℝ) := by
      push_cast; field_simp
    have e2 : conj (Complex.I * (Real.pi : ℂ) / (2 * c)) * conj c = -(Complex.I * (Real.pi / 2 : ℝ)) := by
      rw [← map_mul, e1, map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
    rw [e1, e2, sub_neg_eq_add, ← two_mul, show (2 : ℂ) * (Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) =
      Real.pi * Complex.I by push_cast; ring, Complex.exp_pi_mul_I]
  · rw [norm_div, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, Complex.norm_two, one_mul]

theorem rr_eq_form {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par} (p : KB.Pl P Wp Wq)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter) (h : C.LPt)
    (hh : D.IsLocPt h j) :
    p.RR F j w h h = p.form j hj w (KB.slv p.T F j hj w h hh.2) (KB.slv p.T F j hj w h hh.2) := by
  unfold KB.Pl.RR D.RRplace
  rw [dite_eq_left ⟨hh, hh⟩, dite_eq_left hj]
  rfl

theorem bdd_of_tendsto {u : ℕ → ℂ} {x : ℂ} (hu : Tendsto u atTop (𝓝 x)) : ∃ B : ℝ, 0 ≤ B ∧ ∀ n, ‖u n‖ ≤ B := by
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto u hu)
  exact ⟨max B 0, le_max_right _ _, fun n => (hB _ ⟨n, rfl⟩).trans (le_max_left _ _)⟩

end Formalism.FourierDecayAlt.P.PBO
end
end

section

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBFV

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

section Supp

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem uInv_zero_at (s : ℂ) (g : B.Mat k r) :
    ∀ (w : List C.Letter) (x : Wd.Ix (Fin w.length) → B.Mat k r → (Wq →L[ℂ] Wp)),
      (∀ e', x e' g = 0) → ∀ e, KB.uInv s w x e g = 0 := by
  intro w
  induction w with
  | nil =>
    intro x hx e
    exact hx e
  | cons l w ih =>
    intro x hx e
    have h0 := ih (fun e' => x (Fin.cons (0 : Fin 2) e')) (fun e' => hx (Fin.cons (0 : Fin 2) e'))
    have h1 := ih (fun e' => x (Fin.cons (1 : Fin 2) e')) (fun e' => hx (Fin.cons (1 : Fin 2) e'))
    show (if e (0 : Fin (w.length + 1)) = 0 then KB.uInv s w (fun e' => x (Fin.cons (0 : Fin 2) e')) (fun a => e a.succ)
      else KB.uInv s w (fun e' => x (Fin.cons (1 : Fin 2) e')) (fun a => e a.succ) +
        (if l.1 then s else (starRingEnd ℂ) s) • KB.uInv s w (fun e' => x (Fin.cons (0 : Fin 2) e')) fun a => e a.succ) g = 0
    split_ifs <;> simp only [Pi.add_apply, Pi.smul_apply, h0, h1, smul_zero, add_zero]

theorem waveG_bs (Bs : B.RealPlaceData k r Wp Wq) (s : ℂ) (w : List C.Letter)
    (x : Wd.Ix (Fin w.length) → B.Mat k r → (Wq →L[ℂ] Wp)) (R : ℝ)
    (hx : ∀ e, ∀ g ∈ B.GV k r, x e g ≠ 0 → B.gN g ≤ R) :
    ∀ e, ∀ g ∈ B.GV k r, KB.waveG Bs s w x e g ≠ 0 → B.gN g ≤ R := by
  intro e g hg hne
  by_contra hR
  apply hne
  have hz : ∀ e', x e' g = 0 := fun e' => by
    by_contra h
    exact hR (hx e' g hg h)
  show P5.fsv s _ • KB.uInv s w x e g = 0
  rw [uInv_zero_at s g w x hz e, smul_zero]

theorem nice_mono {Bs : B.RealPlaceData k r Wp Wq} {F : B.Mat k r → (Wq →L[ℂ] Wp)} {ε ε' : ℝ} (h : ε' ≤ ε)
    (hF : JC.NiceCoef Bs ε F) : JC.NiceCoef Bs ε' F :=
  ⟨hF.1, hF.2.1, fun g hg hne => h.trans (hF.2.2 g hg hne)⟩

theorem common_R {ι : Type*} [Fintype ι] (F : ι → B.Mat k r → (Wq →L[ℂ] Wp))
    (h : ∀ i, ∃ R : ℝ, ∀ g ∈ B.GV k r, F i g ≠ 0 → B.gN g ≤ R) :
    ∃ R : ℝ, ∀ i, ∀ g ∈ B.GV k r, F i g ≠ 0 → B.gN g ≤ R := by
  classical
  choose R hR using h
  refine ⟨∑ i, |R i|, fun i g hg hne => (hR i g hg hne).trans ?_⟩
  exact (le_abs_self _).trans (Finset.single_le_sum (f := fun i => |R i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i))

end Supp

end Formalism.FourierDecayAlt.P.PBFV
end
end

section

namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt NumberField MeasureTheory Formalism.QuantumDeterminants
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

section defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def rrC (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) :
    Fin S.f → ℝ → ℕ → List C.Letter → C.LPt → C.LPt → ℂ :=
  fun v ε i w P Q =>
    ((1 / (D.bSt (D.kapG (S.g : ℝ) (S6.rd E)) P * D.bSt (D.kapG (S.g : ℝ) (S6.rd E)) Q *
      D.GamLev S.G.k S.G.r (D.kapG (S.g : ℝ) (S6.rd E)) (D.deG (S.g : ℝ) (S6.rd E)) i) : ℝ) : ℂ) *
      (p v).RR (F v ε) i w (D.toStd S.G.r (S.g : ℝ) 1 P) (D.toStd S.G.r (S.g : ℝ) 1 Q)

def setC (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) : C.HidaSetting E Wp Wq :=
  KB.withRR S (rrC S p F)

end defs

def FormPos : Prop :=
  P5.ThmPActual → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter), KB.CutWord P p.l0 w → ∀ x ε, 0 < ε →
    (∀ e, JC.NiceCoef (p.T.bs j) ε (x e)) → 0 ≤ p.form j hj w x x

end

end Formalism.FourierDecayAlt.P.PBL
end

section

namespace Formalism.FourierDecayAlt.P.PBJ

open MeasureTheory Formalism.FourierDecayAlt

def KCls {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (Ψ : G.Mat n → V) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) Ψ ∧ HasCompactSupport Ψ ∧ ∀ Z ∈ tsupport Ψ, G.detM Z ≠ 0

def FubTop : Prop :=
  ∀ (β : ℂ) (p s : ℕ) (σ : Equiv.Perm (Fin (p + s))) (d : Fin (p + s) → ℂ) (σh : Equiv.Perm (Fin p))
    (dh : Fin p → ℂ) (σb : Equiv.Perm (Fin s)) (db : Fin s → ℂ) (V : Type) [NormedAddCommGroup V]
    [NormedSpace ℂ V] [CompleteSpace V] (Ψ : G.Mat (p + s) → V),
    (∀ i, dh i ≠ 0) → (∀ i, db i ≠ 0) → U.hMat σ d = U.blk2 (U.hMat σh dh) 0 0 (U.hMat σb db) → KCls Ψ →
    U.PhiTop (p := p + s) (s := 0) β σ d Ψ (fun x => x.elim0) =
      U.PhiTop (p := s) (s := 0) β σb db (U.PhiTop (p := p) (s := s) β σh dh Ψ) (fun x => x.elim0)

def FreezeLast : Prop :=
  ∀ (β : ℂ) (p : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (Ψ : G.Mat (p + 1) → V), KCls Ψ → ∀ c : ℂ, c ≠ 0 →
    ∃ Ψc : G.Mat p → V, KCls Ψc ∧ ∀ (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ), (∀ i, d i ≠ 0) →
      U.PhiTop (p := p) (s := 1) β σ d Ψ (fun _ _ => c) = U.PhiTop (p := p) (s := 0) β σ d Ψc (fun x => x.elim0)

def OmLongTop : Prop :=
  ∀ β : ℂ, β ≠ 0 → ∀ n : ℕ, ∃ κ : ℂ, κ ≠ 0 ∧
    ∀ (σ : Equiv.Perm (Fin (n + 1))) (d : Fin (n + 1) → ℂ) (z : ℂ) (V : Type) [NormedAddCommGroup V]
      [NormedSpace ℂ V] [CompleteSpace V] (Φ : G.Mat (n + 1) → V),
      z ≠ 0 → U.hMat σ d = G.ptLong (n + 1) z →
      G.OmLong β n Φ z = κ • U.PhiTop (p := n + 1) (s := 0) β σ d Φ (fun x => x.elim0)

def OmBlockTop : Prop :=
  ∀ β : ℂ, β ≠ 0 → ∀ n : ℕ, ∃ κ : ℂ, κ ≠ 0 ∧
    ∀ (σ : Equiv.Perm (Fin (n + 1))) (d : Fin (n + 1) → ℂ) (t c : ℂ) (V : Type) [NormedAddCommGroup V]
      [NormedSpace ℂ V] [CompleteSpace V] (Φ : G.Mat (n + 1) → V),
      t ≠ 0 → c ≠ 0 → U.hMat σ d = G.ptBlock n t c →
      G.OmBlock β n Φ t c = κ • U.PhiTop (p := n + 1) (s := 0) β σ d Φ (fun x => x.elim0)

def KloostDensOfParts : Prop := FubTop → FreezeLast → OmLongTop → OmBlockTop → KB.KloostDens

end Formalism.FourierDecayAlt.P.PBJ
end
