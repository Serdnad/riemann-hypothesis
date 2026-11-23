module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle050
public import Formalism.HermitianCurvature.Bundle006
public import Formalism.HermitianCurvature.StatementHeads
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadicalUnipotentFirstBasisEqOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LinearFormRadicalRankOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OuterProductMatrix
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle102
import Mathlib.Algebra.AffineMonoid.UniqueSums
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MeasureTheory
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section defs

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}

def cc (j : ℕ) (hj : j + 1 ≤ P.r) (t : ℂ) (c : Fin (P.r - (j + 1)) → ℂ) : Fin (P.r - j) → ℂ :=
  fun l => consC t c (Fin.cast (by omega) l)

def gi (j : ℕ) (hj : j + 1 ≤ P.r) (g : Mx P.k (P.r - (j + 1))) : Mx P.k (P.r - j) :=
  D.castM (by omega) (ιLev P.k 1 (P.r - (j + 1)) g)

def GoodFam (T : D.LevTower P.k P.r Wp Wq) (j : ℕ) (G : ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)) : Prop :=
  (∀ t₀ : ℂ, t₀ ≠ 0 → ∀ γ₀ ∈ B.GV P.k (P.r - (j + 1)), ∃ (U : Set (ℂ × B.Mat P.k (P.r - (j + 1))))
      (f : ℂ × B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)), IsOpen U ∧ (t₀, γ₀) ∈ U ∧ ContDiffOn ℝ ∞ f U ∧
      ∀ p ∈ U, p.2 ∈ B.GV P.k (P.r - (j + 1)) → G p.1 p.2 = f p) ∧
  ∀ K : Set ℂ, IsCompact K → (∀ t ∈ K, t ≠ 0) → ∃ C : Set (B.Mat P.k (P.r - (j + 1))), IsCompact C ∧
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ K, ∀ γ, G t γ ≠ 0 → γ ∈ C ∧
      (γ ∈ B.GV P.k (P.r - (j + 1)) → ε ≤ Gf P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' γ)

def famP (j : ℕ) (G : ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)) (v : ℂ) :
    ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp) :=
  fun t => (B.GV P.k (P.r - (j + 1))).indicator fun γ => fderiv ℝ (fun u : ℂ => G u γ) t v

def Rep (T : D.LevTower P.k P.r Wp Wq) (j : ℕ) (hj : j + 1 ≤ P.r)
    (Ψ : RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
    (G : ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ t : ℂ, t ≠ 0 → ∀ x ∈ DomR P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z',
    (Ψ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) (cc j hj t x.1) (gi j hj x.2) =
      resG P.k (P.r - (j + 1)) (Fin.last _) (B.JF (T.bs (j + 1)) (G t)) x.1 x.2

def InC (T : D.LevTower P.k P.r Wp Wq) (j : ℕ) (hj : j + 1 ≤ P.r)
    (Ψ : RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π') : Prop :=
  ∃ G, GoodFam T j G ∧ Rep T j hj Ψ G

def sliceFam (T : D.LevTower P.k P.r Wp Wq) (j : ℕ) (hj : j + 1 ≤ P.r) (F : B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) :
    ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp) :=
  fun t => (B.GV P.k (P.r - (j + 1))).indicator fun γ =>
    ((‖t‖ ^ (2 * (P.r - j) + P.k) : ℝ) : ℂ) • ∫ xx : U.RC P.k 1 (P.r - (j + 1)) × U.RC P.k 1 (P.r - (j + 1)),
      (psi P.k (P.r - j) (T.bs j).z cStd (rn1 (by omega : P.r - (j + 1) + 1 = P.r - j) xx.1) *
          star (psi P.k (P.r - j) (T.bs j).z' cStd (rn1 (by omega : P.r - (j + 1) + 1 = P.r - j) xx.2))) •
        F ((rn1 (by omega : P.r - (j + 1) + 1 = P.r - j) xx.1)⁻¹ * mc (by omega : P.r - (j + 1) + 1 = P.r - j) t γ *
          rn1 (by omega : P.r - (j + 1) + 1 = P.r - j) xx.2)
      ∂((U.muRC P.k 1 (P.r - (j + 1))).prod (U.muRC P.k 1 (P.r - (j + 1))))

end defs

def FamJFOK : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq) (j : ℕ) (G : ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)),
    GoodFam T j G → ∀ t : ℂ, t ≠ 0 → JFOKCpt (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (G t)

def FamAlg : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq) (j : ℕ) (G G' : ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)),
    GoodFam T j G → GoodFam T j G' → ∀ m : ℂ → ℂ, ContDiffOn ℝ ∞ m {t | t ≠ 0} →
      GoodFam T j (fun t γ => G t γ + G' t γ) ∧ GoodFam T j (fun t γ => m t • G t γ)

def FamDeriv : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq) (j : ℕ) (G : ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)),
    GoodFam T j G → ∀ v : ℂ, GoodFam T j (famP j G v)

def RepLin : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq), IsPlace P T.base.z T.base.z' T.base.π T.base.π' → D.TowerNormalised T →
    ∀ (j : ℕ), j + 1 ≤ P.r →
    IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π' →
    ∀ (G G' : ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)), GoodFam T j G → GoodFam T j G' →
    ∀ t : ℂ, t ≠ 0 → ∀ (a : ℂ), ∀ x ∈ DomR P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z',
      resG P.k (P.r - (j + 1)) (Fin.last _) (B.JF (T.bs (j + 1)) (fun γ => G t γ + G' t γ)) x.1 x.2 =
          resG P.k (P.r - (j + 1)) (Fin.last _) (B.JF (T.bs (j + 1)) (G t)) x.1 x.2 +
            resG P.k (P.r - (j + 1)) (Fin.last _) (B.JF (T.bs (j + 1)) (G' t)) x.1 x.2 ∧
        resG P.k (P.r - (j + 1)) (Fin.last _) (B.JF (T.bs (j + 1)) (fun γ => a • G t γ)) x.1 x.2 =
          a • resG P.k (P.r - (j + 1)) (Fin.last _) (B.JF (T.bs (j + 1)) (G t)) x.1 x.2

def FamJFDeriv : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq), IsPlace P T.base.z T.base.z' T.base.π T.base.π' → D.TowerNormalised T →
    ∀ (j : ℕ), j + 1 ≤ P.r →
    IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π' →
    ∀ (G : ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)), GoodFam T j G →
    ∀ t : ℂ, t ≠ 0 → ∀ x ∈ DomR P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z', ∀ v : ℂ,
      HasDerivAt (fun s : ℝ =>
          resG P.k (P.r - (j + 1)) (Fin.last _) (B.JF (T.bs (j + 1)) (G (t + (s : ℂ) * v))) x.1 x.2)
        (resG P.k (P.r - (j + 1)) (Fin.last _) (B.JF (T.bs (j + 1)) (famP j G v t)) x.1 x.2) 0

def CellTie : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq), IsPlace P T.base.z T.base.z' T.base.π T.base.π' → D.TowerNormalised T →
    ∀ (j : ℕ) (hj : j + 1 ≤ P.r),
    IsPlace (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' →
    IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π' →
    ∀ t : ℂ, t ≠ 0 → ∀ x ∈ DomR P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z',
      (cc j hj t x.1, gi j hj x.2) ∈ DomR P.k (P.r - j) (T.bs j).z (T.bs j).z' ∧
        wCell P.k (P.r - (j + 1)) (Fin.last _) x.1 * x.2 ∈ B.GV P.k (P.r - (j + 1)) ∧
        wCell P.k (P.r - (j + 1)) (Fin.last _) x.1 * x.2 ∈ OmPlus P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z'

def SliceFamGood : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq), IsPlace P T.base.z T.base.z' T.base.π T.base.π' → D.TowerNormalised T →
    ∀ (j : ℕ) (hj : j + 1 ≤ P.r),
    IsPlace (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' →
    IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π' →
    ∀ F : B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp), JFOKCpt (JC.parLev P j) (T.bs j).z (T.bs j).z' F →
      GoodFam T j (sliceFam T j hj F)

def SliceFamJF : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq), IsPlace P T.base.z T.base.z' T.base.π T.base.π' → D.TowerNormalised T →
    ∀ (j : ℕ) (hj : j + 1 ≤ P.r),
    IsPlace (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' →
    IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π' →
    ∀ F : B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp), JFOKCpt (JC.parLev P j) (T.bs j).z (T.bs j).z' F →
    ∀ t : ℂ, t ≠ 0 → ∀ γ ∈ B.GV P.k (P.r - (j + 1)),
      γ ∈ OmPlus P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' →
      B.JF (T.bs (j + 1)) (sliceFam T j hj F t) γ =
        ((‖t‖ ^ (2 * (P.r - j) + P.k) : ℝ) : ℂ) • B.JF (T.bs j) F (mc (by omega : P.r - (j + 1) + 1 = P.r - j) t γ)

def OpClosed : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq), IsPlace P T.base.z T.base.z' T.base.π T.base.π' → D.TowerNormalised T →
    ∀ (j : ℕ) (hj : j + 1 ≤ P.r),
    IsPlace (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' →
    IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π' →
    ∀ (X : ActualOps P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π') (i : Fin 6)
      (Ψ : RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'),
      InC T j hj Ψ → InC T j hj (X.op ⟨0, by omega⟩ i Ψ)

def BTlAdjoin : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (k r : ℕ)
    (z z' : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (π' : Mx k r → (Wq →L[ℂ] Wq))
    (X : ActualOps k r z z' π π') (L : R.LevelData (Pr (RadSp k r z z' π π')) r), IsActualLevel X L →
    ∀ (S : Type) [Fintype S] [DecidableEq S] (l : Fin r) (w : List (Wd.Letter ℂ S)) (a b : Wd.Ix S),
      (bTl L l w a b).1 ∈ Algebra.adjoin ℂ (Set.range (X.op l))

def UUiwScalar : Prop :=
  ∀ (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] (S : Type) [Fintype S] [DecidableEq S] (s : ℂ)
    (w : List (Wd.Letter ℂ S)) (a b : Wd.Ix S), Wd.UUiw (A := A) s w a b ∈ (⊥ : Subalgebra ℂ A)

end Formalism.FourierDecayAlt.P.CutSH
end
end

section

open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate

set_option linter.style.haveILetI false

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Dx2.Split Dx2.SplitM

variable {k j ρ : ℕ}

def tauB (a : Fin 1 → Fin j → ℂ) : Fin j → Fin 1 → ℂ := fun i _ => star (a 0 i)

theorem bC_eq (x : U.RC k j (1 + ρ)) : bC x = tauB (aC x) := by
  funext i b
  have hb : b = 0 := Subsingleton.elim _ _
  subst hb
  simp [bC, tauB]

theorem tauB_mp : MeasurePreserving (tauB (j := j)) volume volume := by
  have u1 := measurePreserving_funUnique (volume : Measure (Fin j → ℂ)) (Fin 1)
  have u2 : MeasurePreserving (fun (v : Fin j → ℂ) (i : Fin j) => (MeasurableEquiv.funUnique (Fin 1) ℂ).symm (v i))
      volume volume :=
    measurePreserving_pi (fun _ => (volume : Measure ℂ)) (fun _ => (volume : Measure (Fin 1 → ℂ)))
      (f := fun _ => (MeasurableEquiv.funUnique (Fin 1) ℂ).symm)
      (fun _ => (measurePreserving_funUnique (volume : Measure ℂ) (Fin 1)).symm)
  have h := u2.comp (vconj_mp.comp u1)
  have e : (tauB (j := j)) =
      (fun (v : Fin j → ℂ) (i : Fin j) => (MeasurableEquiv.funUnique (Fin 1) ℂ).symm (v i)) ∘
        (fun v : Fin j → ℂ => star v) ∘ ⇑(MeasurableEquiv.funUnique (Fin 1) (Fin j → ℂ)) := by
    funext a i l
    rfl
  rw [e]; exact h

theorem PsiR_mp : MeasurePreserving (fun z : U.RC k j (1 + ρ) × U.RC k 1 ρ => (XC z.1 z.2, bC z.1)) volume volume := by
  haveI : SigmaFinite (volume : Measure (G.UT (j + 1) → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin (j + 1) → ℝ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin (2 * ρ + k + 1) → Fin (j + 1) → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure ((G.UT (j + 1) → ℂ) × (Fin (j + 1) → ℝ))) := inferInstance
  haveI : SigmaFinite (volume : Measure (U.RC k (j + 1) ρ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin 1 → Fin j → ℂ)) := inferInstance
  have h := ((MeasurePreserving.id (volume : Measure (U.RC k (j + 1) ρ))).prod tauB_mp).comp PsiL_mp
  have e : (fun z : U.RC k j (1 + ρ) × U.RC k 1 ρ => (XC z.1 z.2, bC z.1)) =
      Prod.map id tauB ∘ (fun z : U.RC k j (1 + ρ) × U.RC k 1 ρ => (XC z.1 z.2, aC z.1)) := by
    funext z; simp [bC_eq]
  rw [e]; exact h

theorem measurePreserving_snd_empty_block (σ : Equiv.Perm (Fin j)) :
    MeasurePreserving (fun η : U.XiH j 0 σ => η.2) volume volume := by
  have h0 : IsProbabilityMeasure (volume : Measure (Fin 0 → ℂ)) := by
    rw [MeasureTheory.volume_pi, MeasureTheory.Measure.pi_of_empty]
    infer_instance
  have h1 : IsProbabilityMeasure (volume : Measure (Fin 0 → Fin j → ℂ)) := by
    rw [MeasureTheory.volume_pi, MeasureTheory.Measure.pi_of_empty]
    infer_instance
  have h2 : IsProbabilityMeasure (volume : Measure (Fin j → Fin 0 → ℂ)) := by
    rw [MeasureTheory.volume_pi]
    infer_instance
  have h3 : IsProbabilityMeasure (volume : Measure ((Fin 0 → Fin j → ℂ) × (Fin j → Fin 0 → ℂ))) := by
    rw [MeasureTheory.Measure.volume_eq_prod]
    infer_instance
  exact MeasureTheory.measurePreserving_snd

end Formalism.FourierDecayAlt.P.PBH

namespace Formalism.FourierDecayAlt.P.PBH

open Dx2.Split Dx2.SplitM

variable {k j ρ : ℕ}

def TQ (σ : Equiv.Perm (Fin j)) (p : (U.RC k 1 ρ × U.RC k 1 ρ) × U.Xi k j 0 (1 + ρ) σ) : U.Xi k j 1 ρ σ :=
  ((XC p.2.1.1 p.1.1, XC p.2.1.2 p.1.2), ((aC p.2.1.1, bC p.2.1.2), p.2.2.2))

theorem TQ_mp (σ : Equiv.Perm (Fin j)) :
    MeasurePreserving (TQ (k := k) (ρ := ρ) σ) (((U.muRC k 1 ρ).prod (U.muRC k 1 ρ)).prod (U.muXi k j 0 (1 + ρ) σ))
      (U.muXi k j 1 ρ σ) := by
  haveI : SigmaFinite (volume : Measure (G.UT (j + 1) → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin (j + 1) → ℝ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin (2 * ρ + k + 1) → Fin (j + 1) → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure ((G.UT (j + 1) → ℂ) × (Fin (j + 1) → ℝ))) := inferInstance
  haveI : SigmaFinite (volume : Measure (U.RC k (j + 1) ρ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (G.UT j → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin j → ℝ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin (2 * (1 + ρ) + k + 1) → Fin j → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure ((G.UT j → ℂ) × (Fin j → ℝ))) := inferInstance
  haveI : SigmaFinite (volume : Measure (U.RC k j (1 + ρ))) := inferInstance
  haveI : SigmaFinite (volume : Measure (G.UT 1 → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin 1 → ℝ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin (2 * ρ + k + 1) → Fin 1 → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure ((G.UT 1 → ℂ) × (Fin 1 → ℝ))) := inferInstance
  haveI : SigmaFinite (volume : Measure (U.RC k 1 ρ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin 1 → Fin j → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin j → Fin 1 → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (U.LW σ → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure ((U.LW σ → ℂ) × (G.UT j → ℂ))) := inferInstance
  haveI : SigmaFinite (volume : Measure ((Fin 0 → Fin j → ℂ) × (Fin j → Fin 0 → ℂ))) := inferInstance
  haveI : SigmaFinite (volume : Measure (U.XiH j 0 σ)) := inferInstance
  set μX := (volume : Measure (U.RC k j (1 + ρ)))
  set μY := (volume : Measure (U.RC k 1 ρ))
  set μH := (volume : Measure (U.XiH j 0 σ))
  set μXC := (volume : Measure (U.RC k (j + 1) ρ))
  set μA := (volume : Measure (Fin 1 → Fin j → ℂ))
  set μB := (volume : Measure (Fin j → Fin 1 → ℂ))
  set μHr := (volume : Measure ((U.LW σ → ℂ) × (G.UT j → ℂ)))
  have s1 := Measure.measurePreserving_swap (μ := μY.prod μY) (ν := (μX.prod μX).prod μH)
  have s2 := measurePreserving_prodAssoc (μX.prod μX) μH (μY.prod μY)
  have s3 := (MeasurePreserving.id (μX.prod μX)).prod (Measure.measurePreserving_swap (μ := μH) (ν := μY.prod μY))
  have s4 := (measurePreserving_prodAssoc (μX.prod μX) (μY.prod μY) μH).symm
  have s5 := (middle_four_swap_measure_preserving μX μX μY μY).prod (MeasurePreserving.id μH)
  have c1 := ((PsiL_mp (k := k) (j := j) (ρ := ρ)).prod (PsiR_mp (k := k) (j := j) (ρ := ρ))).prod (measurePreserving_snd_empty_block σ)
  have t1 := (middle_four_swap_measure_preserving μXC μA μXC μB).prod (MeasurePreserving.id μHr)
  have t2 := measurePreserving_prodAssoc (μXC.prod μXC) (μA.prod μB) μHr
  have h := t2.comp (t1.comp (c1.comp (s5.comp (s4.comp (s3.comp (s2.comp s1))))))
  exact h

end Formalism.FourierDecayAlt.P.PBH

namespace Formalism.FourierDecayAlt.P.PBH

open Dx2.Split Dx2.SplitM

theorem pointStep : PointStep := by
  intro k j ρ σ d hd c hc zA zA' hzA hzA' E _ _ _ F γ hint
  set Gi : U.Xi k j 1 ρ σ → E := fun ξ => U.psiStar k ρ σ zA zA' ξ • F (U.gaXi k ρ σ d ξ (fun _ _ => c) γ) with hGi
  have hT := TQ_mp (k := k) (ρ := ρ) σ
  haveI : SigmaFinite (volume : Measure (G.UT j → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin j → ℝ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin (2 * (1 + ρ) + k + 1) → Fin j → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure ((G.UT j → ℂ) × (Fin j → ℝ))) := inferInstance
  haveI : SigmaFinite (volume : Measure (U.RC k j (1 + ρ))) := inferInstance
  haveI : SigmaFinite (volume : Measure (G.UT 1 → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin 1 → ℝ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin (2 * ρ + k + 1) → Fin 1 → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure ((G.UT 1 → ℂ) × (Fin 1 → ℝ))) := inferInstance
  haveI : SigmaFinite (volume : Measure (U.RC k 1 ρ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (U.LW σ → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure ((U.LW σ → ℂ) × (G.UT j → ℂ))) := inferInstance
  haveI : SigmaFinite (volume : Measure ((Fin 0 → Fin j → ℂ) × (Fin j → Fin 0 → ℂ))) := inferInstance
  haveI : SigmaFinite (volume : Measure (U.XiH j 0 σ)) := inferInstance
  haveI : SigmaFinite ((volume : Measure (U.RC k j (1 + ρ))).prod (volume : Measure (U.RC k j (1 + ρ)))) :=
    inferInstance
  haveI : SFinite (U.muXi k j 0 (1 + ρ) σ) := by
    unfold U.muXi U.muRC U.muXiH; infer_instance
  haveI : SFinite ((U.muRC k 1 ρ).prod (U.muRC k 1 ρ)) := by
    unfold U.muRC; infer_instance
  have hpt : ∀ p : (U.RC k 1 ρ × U.RC k 1 ρ) × U.Xi k j 0 (1 + ρ) σ, Gi (TQ σ p) =
      (psi k (1 + ρ) (U.lowV k j (1 + ρ) (D.castV (hsv k j ρ) zA)) cStd (U.Rn k 1 ρ p.1.1) *
        star (psi k (1 + ρ) (U.lowV k j (1 + ρ) (D.castV (hsv k j ρ) zA')) cStd (U.Rn k 1 ρ p.1.2))) •
      (U.psiStar (p := j) (s := 0) k (1 + ρ) σ (D.castV (hsv k j ρ) zA) (D.castV (hsv k j ρ) zA') p.2 •
        D.castF (hs' k j ρ) F (U.gaXi (p := j) (s := 0) k (1 + ρ) σ d p.2 (fun a => a.elim0)
          ((U.Rn k 1 ρ p.1.1)⁻¹ * U.mMap k 1 ρ (Matrix.of fun _ _ => c) γ * U.Rn k 1 ρ p.1.2))) := by
    rintro ⟨⟨y, y'⟩, ⟨⟨x, x'⟩, η⟩⟩
    have hgx : D.castM (hs' k j ρ) (U.gaXi (p := j) (s := 0) k (1 + ρ) σ d ((x, x'), η) (fun a => a.elim0)
        ((U.Rn k 1 ρ y)⁻¹ * U.mMap k 1 ρ (Matrix.of fun _ _ => c) γ * U.Rn k 1 ρ y')) =
        U.gaXi (p := j) (s := 1) k ρ σ d ((XC x y, XC x' y'), ((aC x, bC x'), η.2)) (fun _ _ => c) γ :=
      GX σ d hd c hc x x' η y y' γ
    simp only [hGi, TQ]
    rw [PS σ zA zA' hzA hzA' x x' η y y', ← hgx, mul_smul]
    rfl
  have hint' : Integrable (Gi ∘ TQ σ) (((U.muRC k 1 ρ).prod (U.muRC k 1 ρ)).prod (U.muXi k j 0 (1 + ρ) σ)) :=
    (hT.integrable_comp hint.aestronglyMeasurable).mpr hint
  show ∫ ξ, Gi ξ ∂(U.muXi k j 1 ρ σ) = _
  rw [← hT.map_eq, integral_map hT.measurable.aemeasurable (by rw [hT.map_eq]; exact hint.aestronglyMeasurable)]
  have e2 : (fun p => Gi (TQ σ p)) = fun p : (U.RC k 1 ρ × U.RC k 1 ρ) × U.Xi k j 0 (1 + ρ) σ =>
      (psi k (1 + ρ) (U.lowV k j (1 + ρ) (D.castV (hsv k j ρ) zA)) cStd (U.Rn k 1 ρ p.1.1) *
        star (psi k (1 + ρ) (U.lowV k j (1 + ρ) (D.castV (hsv k j ρ) zA')) cStd (U.Rn k 1 ρ p.1.2))) •
      (U.psiStar (p := j) (s := 0) k (1 + ρ) σ (D.castV (hsv k j ρ) zA) (D.castV (hsv k j ρ) zA') p.2 •
        D.castF (hs' k j ρ) F (U.gaXi (p := j) (s := 0) k (1 + ρ) σ d p.2 (fun a => a.elim0)
          ((U.Rn k 1 ρ p.1.1)⁻¹ * U.mMap k 1 ρ (Matrix.of fun _ _ => c) γ * U.Rn k 1 ρ p.1.2))) := funext hpt
  have hint2 := hint'
  rw [show Gi ∘ TQ σ = fun p => Gi (TQ σ p) from rfl, e2] at hint2
  rw [e2, integral_prod _ hint2]
  congr 1
  funext yy
  dsimp only
  rw [integral_smul]
  rfl

end Formalism.FourierDecayAlt.P.PBH
end
end

section

open Polynomial

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC

theorem pf_conj_eval' (q : ℂ[X]) (x : ℝ) :
    (q.map (starRingEnd ℂ)).eval (x : ℂ) = starRingEnd ℂ (q.eval (x : ℂ)) := by
  rw [Polynomial.eval_map]
  have hx : (x : ℂ) = starRingEnd ℂ (x : ℂ) := (Complex.conj_ofReal x).symm
  conv_lhs => rw [hx]
  exact Polynomial.eval₂_at_apply _ _

theorem pf_id (q : ℂ[X]) (n : ℕ) (a C : ℝ)
    (h : ∀ x : ℝ, a < x → Complex.normSq (q.eval (x : ℂ)) = C * (x - a) ^ (2 * n)) :
    q * q.map (starRingEnd ℂ) = Polynomial.C (C : ℂ) * (X - Polynomial.C (a : ℂ)) ^ (2 * n) := by
  have hroots : Set.Infinite {z : ℂ | IsRoot (q * q.map (starRingEnd ℂ) -
      Polynomial.C (C : ℂ) * (X - Polynomial.C (a : ℂ)) ^ (2 * n)) z} := by
    refine Set.infinite_of_injective_forall_mem (f := fun m : ℕ => ((a + 1 + m : ℝ) : ℂ)) ?_ ?_
    · intro s t hst
      have := Complex.ofReal_injective hst
      exact_mod_cast (by linarith : (s : ℝ) = t)
    · intro m
      simp only [Set.mem_ofPred_eq, IsRoot, eval_sub, eval_mul, eval_C, eval_pow, eval_X]
      have hx : a < a + 1 + (m : ℝ) := by have := m.cast_nonneg (α := ℝ); linarith
      rw [pf_conj_eval', Complex.mul_conj, h _ hx]
      push_cast
      ring
  exact sub_eq_zero.1 (Polynomial.eq_zero_of_infinite_isRoot _ hroots)

theorem polynomial_finish_holds : PolyFinish := by
  intro q n a C h
  have hid := pf_id q n a C h
  by_cases hq : q = 0
  · exact ⟨0, by simp [hq]⟩
  have hqb : q.map (starRingEnd ℂ) ≠ 0 := by
    rwa [Ne, Polynomial.map_eq_zero_iff (RingHom.injective _)]
  have hC : (C : ℂ) ≠ 0 := by
    intro h0
    rw [h0, Polynomial.C_0, zero_mul] at hid
    exact mul_ne_zero hq hqb hid
  have hroot : ∀ b ∈ q.roots, b = (a : ℂ) := by
    intro b hb
    have hb0 : q.eval b = 0 := (Polynomial.mem_roots hq).1 hb
    have := congrArg (Polynomial.eval b) hid
    simp only [eval_mul, hb0, zero_mul, eval_C, eval_pow, eval_sub, eval_X] at this
    have h2 := (mul_eq_zero.1 this.symm).resolve_left hC
    exact sub_eq_zero.1 (pow_eq_zero_iff'.1 h2).1
  have hcard : Multiset.card q.roots = q.natDegree := by
    first
      | exact (Polynomial.natDegree_eq_card_roots' (IsAlgClosed.splits q)).symm
      | exact IsAlgClosed.card_roots_eq_natDegree
  have hrep : q.roots = Multiset.replicate q.natDegree (a : ℂ) := by
    rw [← hcard]; exact Multiset.eq_replicate.2 ⟨rfl, hroot⟩
  have hform : q = Polynomial.C q.leadingCoeff * (X - Polynomial.C (a : ℂ)) ^ q.natDegree := by
    conv_lhs => rw [← Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hcard]
    rw [hrep, Multiset.map_replicate, Multiset.prod_replicate]
  have hdeg : q.natDegree = n := by
    have h1 := congrArg Polynomial.natDegree hid
    rw [Polynomial.natDegree_mul hq hqb, Polynomial.natDegree_map_eq_of_injective (RingHom.injective _),
      Polynomial.natDegree_C_mul hC, Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C] at h1
    omega
  exact ⟨q.leadingCoeff, by rw [← hdeg]; exact hform⟩

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC
end
