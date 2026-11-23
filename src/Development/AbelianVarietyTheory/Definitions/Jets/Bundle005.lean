module

public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle004
public import Formalism.HermitianCurvature.Bundle008
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle064
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective
public import Formalism.DropLevelBounds.ThBounds
public import Formalism.LocalToGlobal.Divisibility.Numbers
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.ExampleSatisfiesConditionsAtFive
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle040
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

@[expose] public section

section

namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

noncomputable section

section actual

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def PolyLift (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (o κ : ℕ) (a : RA P Bs) : Prop :=
  ∃ Θ : B.DiffOp P.k P.r Wp Wq, Formalism.FourierDecayAlt.P.CutMP.PolyOp o κ Θ ∧ TL.RadIs P Bs Θ a.1

end actual

def BasicLiftAll (a : ℕ → ℕ) : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r))
    (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)),
    P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ x ∈ basics d,
      x ∈ nfSpan d {θ | PolyLift P Bs (2 * P.r + P.k + 1) (8 * (P.r + 1) * (2 * P.r + P.k + 1)) θ} 0 (a P.r) 1

def CutPow (e : ℕ) (φ : ℝ → ℝ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧ (∃ δ : ℝ, 0 < δ ∧ ∀ x, x < δ → φ x = 0) ∧
    ∃ a R : ℝ, ∀ x, R ≤ x → φ x = a * x ^ e

def mulG {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (φ : ℝ → ℝ) (f : B.Mat k r → (Wq →L[ℂ] Wp)) :
    B.Mat k r → (Wq →L[ℂ] Wp) :=
  fun g => ((φ (Gf k r Bs.z Bs.z' g) : ℝ) : ℂ) • f g

def WordBound {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (a : ℕ)
    (w : List C.Letter) (C : ℝ) (J : ℕ) (Θs : List (B.DiffOp P.k P.r Wp Wq))
    (K : (ℝ → ℝ) → (B.Mat P.k P.r → (Wq →L[ℂ] Wp)) → Prop) : Prop :=
  0 ≤ C ∧ (∀ Θ ∈ Θs, Formalism.FourierDecayAlt.P.CutMP.PolyOp (w.length * (2 * P.r + P.k + 1))
      (w.length * (8 * (P.r + 1) * (2 * P.r + P.k + 1))) Θ) ∧
    ∀ φ f, K φ f → ∀ (e : Ix (Fin w.length)) (c : Fin (P.r + 1) → ℂ), (∀ l, c l ≠ 0) →
      0 < TBB.Gp p (TBB.bigPt P.r c) →
      ‖B.hsVec (p.V (p.Θ.Θ w e (mulG p.T.base φ f)) (TBB.bigPt P.r c))‖ ≤
        C * (‖∏ l, c l‖⁻¹ ^ w.length * (TBB.Gp p (TBB.bigPt P.r c))⁻¹ ^ (a * w.length)) *
          (∑ j ∈ Finset.range (J + 1), |LE.ld j φ (TBB.Gp p (TBB.bigPt P.r c))|) *
          (Θs.map fun Θ => ‖B.hsVec (p.V (B.opApply Θ f) (TBB.bigPt P.r c))‖).sum

end

end GlobalTheory.HatNF
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RunDepth

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree

variable {D : D7}

def plOf (D : D7) (z : RPl D.R) : D.what₂.Tau :=
  D.eTau.symm (if z.1 then ⟨D.R.tau2 z.2, rfl⟩ else ⟨D.R.tau1 z.2, rfl⟩)

def numOf (D : D7) (L : SizeData₂ D) : NumDatum where
  R := D.R
  sc := L.sc
  H := D.host.toHostAx
  g := D.host.g
  g_prime := D.host.g_prime
  TT := D.host.TT
  Del := ⌊(D.s.Del : ℝ)⌋₊
  h0 := ⌊LevelStarExponents.h0 L⌋₊
  hc := fun z => D.hc (plOf D z)

def vdOf (D : D7) (p : ℕ) : ℝ := if p ∈ D.host.small then (padicValNat p D.host.QS : ℝ) else 1 / 2

variable {L : SizeData₂ D} {Pm : ParameterChoice' D L}

theorem TO_pos (Tp : ParamsT D L Pm) : 0 < Tp.TO := lt_of_lt_of_le (by omega) Tp.TO_40

def depOf (T : Core D) (EX : ErrX D) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) : DepData D.host.E :=
  depRun T EX ⟨Tp.TO, TO_pos Tp⟩ (vdOf D) (lR Tp hK) (fR Tp hK) (kaR Tp hK)

structure RunTie (T : Core D) (EX : ErrX D) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) [StarRing (𝓞 D.host.E)]
    {K : Type} [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 T.Q.c.F) (𝓞 K)]
    [Algebra.IsIntegral (𝓞 T.Q.c.F) (𝓞 K)] [Algebra (𝓞 D.host.E) K]
    {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}
    (O : OnObj S P oc) (ι : Bs.J → ℕ) : Prop where
  inR : ∀ j, InR D (ι j)
  star_eq : ∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a
  conj : ∀ a : 𝓞 D.host.E, star (algebraMap (𝓞 D.host.E) K a) = algebraMap (𝓞 D.host.E) K (T.Q.H.bar a)
  E_eq : ∀ v j, O.E v j = EAt (Xo := T.Q.Xo (ι j)) (c := T.Q.c) (LL := K) (depOf T EX Tp hK) v (ι j)
  σ_eq : ∀ v j, O.σ v j = sigAt (Dw := T.Q.Dw (ι j)) (H := T.Q.H) (LL := K) (depOf T EX Tp hK) (ι j)
  nn_eq : ∀ j, O.nnK j = nnKAt (H := T.Q.H) (LL := K) (depOf T EX Tp hK) (ι j)
  T_eq : O.T = (Tp.TO : ℝ)
  jets_eq_fact : O.g1 = D.host.g 0
  g2_eq : O.g2 = D.host.g 1
  cmQuadraticForm_eq_alternatingForm : O.q1 = D.host.q
  dd_eq : O.dd = D.host.d
  sm_eq : O.sm = D.host.small
  k_eq : O.k = (D.R.k : ℝ)
  m_eq : O.m = (D.R.m : ℝ)
  f_eq : O.f = (D.R.f : ℝ)
  x_eq : O.x = L.sc.x
  eps_eq : O.eps = L.sc.eps
  Sc_eq : O.Sc = L.Sc
  eta_eq : O.eta = L.etaSz
  bp_eq : O.bp = L.sc.b'
  depthNumbers_threshold_eq : O.X2 = L.sc.X'' D.R.n
  vd_eq : O.vd = vd2 D
  wt_eq : ∀ j, O.wt j = 2 * (D.R.f : ℝ) * L.sc.b
  th_eq : ∀ l, O.th l = Formalism.UnitaryBoundIntegral.thl D.R.k l
  ad_eq : ∀ l, O.ad l = 0
  DF_ge : ∀ j, (WeightAlgebra.DF (lR Tp hK (ι j)) : ℝ) ≤ O.DF

end GlobalTheory.RunDepth
end
end
