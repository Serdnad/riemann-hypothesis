module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle016
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle015
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ZeroWeightSections

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def IsSecZ (G : WTZ E) (f : Rul Xo c) : Prop :=
  IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f ∧
    ∀ (p : TRing c.F) (t : Ix Dw → (p.R)ˣ) (y y' : FrPt Xo c p.R), FrBor t y y' →
      f p y' = ((∏ i, t i ^ exZ Dw G i : (p.R)ˣ) : p.R) * f p y

theorem isSecZ_wtZ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c) :
    IsSecZ (wtZ a n) f ↔ f ∈ sec Xo c a n := by
  have key : ∀ (S : Type) [CommRing S] (t : Ix Dw → Sˣ),
      ((∏ i, t i ^ exZ Dw (wtZ a n) i : Sˣ) : S) = wchar (ex Dw a n) t := by
    intro S _ t
    rw [wchar, Units.coe_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    cases i <;> simp [exZ, wtZ, ex]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun p t y y' hb => by rw [← key]; exact h2 p t y y' hb⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun p t y y' hb => by rw [key]; exact h2 p t y y' hb⟩


variable (Xo c) in
structure Input : Type where

  D : ℕ
  N : ℕ
  T : ℕ
  i : ℕ
  g0 : ℕ

  cc : ℝ

  wL : WTZ E
  wF : WTZ E
  wde : WTZ E

  Mr : Set (Rul Xo c)

  w : Fin (N + 1) → Rul Xo c
  jc : Comp Xo c → Fin (N + 1)

  np : ℕ
  thp : Fin np → Rul Xo c

  n0 : ℕ
  th0 : Fin n0 → Rul Xo c

  nk : ℕ
  thk : Fin nk → Rul Xo c

  et : Rul Xo c
  ta1 : Rul Xo c
  ta2 : Rul Xo c

  nu : IsDedekindDomain.HeightOneSpectrum (𝓞 c.F) → ℝ

  ip : (c.F →+* ℂ) → (∀ Z : Comp Xo c, AC Z) → (∀ Z : Comp Xo c, AC Z) → ℂ

  wsize : WTZ E → ℝ
  DF : ℝ
  cNu : ℝ
  cQuot : ℝ
  cLow : ℝ
  cLow' : ℝ
  cDim : ℝ
  cGen : ℝ
  crystallineInclusion : ℝ
  cEta : ℝ
  cBase : ℝ
  cBase' : ℝ
  cRank : ℝ
  cField : ℝ
  f : ℝ
  r : ℝ

namespace Input

variable (I : Input Xo c)

end Input

variable (Xo c)

variable {Xo c}

section
variable [Fintype (Comp Xo c)] (I : Input Xo c) (h : GenFrEx Xo c)
    (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))

end

end GlobalTheory.IndefiniteRowSideFullHecke.ZeroWeightSections
end
end

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.L2SquaredNorms

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

section Norms

variable {K₁ : Type} [Field K₁]

def hermSq {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) : ℝ :=
  (z ⬝ᵥ Hm.mulVec (star z)).re

def IsL2SquareIntegralProblem (P : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp K₁)) (rig : LB.Gen (P.L.pull (eSec P.A))) (σ : K₁ →+* ℂ)
    (s : P.L.Sec) (v : ℝ) : Prop :=
  rig.IsGen ∧
  ∃ (A' : Over (Sp ℂ)) (_ : GrpObj A') (φ : A'.left ⟶ P.A.left) (u : HolUnif A' (P.L.pull φ) P.g)
    (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (θ : (Fin P.g → ℂ) → ℂ) (Fd : Set (Fin P.g → ℂ)),
    IsGrpPullback A' P.A (spMap σ) φ ∧ u.IsAH Hm χ ∧
    (∀ i : P.L.ι, ⊤ ≤ (P.L.pull (eSec P.A)).U (fun _ => i) →
      u.fr (fun _ => i) 0 =
        σ (valR (A := K₁) (𝟙 (Sp K₁)) ((P.L.pull (eSec P.A)).U (fun _ => i)) (rig.s (fun _ => i)).val)) ∧
    (∀ (i : P.L.ι) (z : Fin P.g → ℂ), ⊤ ≤ ((u.ex z).left ≫ φ) ⁻¹ᵁ P.L.U i →
      valAt' ((u.ex z).left ≫ φ) (P.L.U i) (s.f i) = θ z * u.fr (fun _ => i) z) ∧
    IsAddFundamentalDomain u.Λ Fd volume ∧ volume Fd ≠ 0 ∧ volume Fd ≠ ⊤ ∧
    IntegrableOn (fun z => ‖θ z‖ ^ 2 * Real.exp (-Real.pi * hermSq Hm z)) Fd volume ∧
    v = (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * hermSq Hm z)) / (volume Fd).toReal

end Norms

section Line

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

def valLineLogNorm (n : ℤ) (mu : ArcLt Dw →₀ ℕ) (thSq : ℝ) (ℓ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → ℝ) : ℝ :=
  -((n : ℝ) / 2) * Real.log thSq - mu.sum fun x m => (m : ℝ) * ℓ x.1 x.2.2

variable {K₁ : Type} [Field K₁]

end Line

end GlobalTheory.IndefiniteRowSideFullHecke.L2SquaredNorms
end
end

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FractionGeneratorsArcs

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj Classical

def GeneratesFrac {O F : Type} [CommRing O] [Field F] (β : O →+* F) : Prop :=
  ∀ x : F, ∃ r s : O, β s ≠ 0 ∧ x * β s = β r

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l}

def UnivCompat {O₁ O₂ : Type} [CommRing O₁] [CommRing O₂] {β₁ : O₁ →+* c.F} {β₂ : O₂ →+* c.F}
    (Y₁ : Model Xo c β₁) (Y₂ : Model Xo c β₂) {S : Scheme.{0}} {t : SAB H S} {χ₁ : S ⟶ Y₁.X} {χ₂ : S ⟶ Y₂.X}
    (m₁ : SABMap t Y₁.t χ₁) (m₂ : SABMap t Y₂.t χ₂) : Prop :=
  ∀ (T : Scheme.{0}) (g : T ⟶ t.G.left) (g₁ : T ⟶ Y₁.oF.t.G.left) (g₂ : T ⟶ Y₂.oF.t.G.left),
    g ≫ m₁.φ = g₁ ≫ Y₁.m.φ → g₁ ≫ Y₁.m0.toSABMap.φ = g₂ ≫ Y₂.m0.toSABMap.φ →
    g₁ ≫ Y₁.oF.t.G.hom = g₂ ≫ Y₂.oF.t.G.hom → g ≫ m₂.φ = g₂ ≫ Y₂.m.φ

def SameWitness {k : Type} [Field k] {bF : c.F →+* k} {a : ArcIn D l (RingHom.id c.F) k bF}
    {O₁ O₂ : Type} [CommRing O₁] [CommRing O₂] {β₁ : O₁ →+* c.F} {β₂ : O₂ →+* c.F}
    {Y₁ : Model Xo c β₁} {Y₂ : Model Xo c β₂}
    {χ₁ : Sp (PowerSeries k) ⟶ Y₁.X} {χ₂ : Sp (PowerSeries k) ⟶ Y₂.X}
    (W₁ : ArcWit Y₁ (a.restrict β₁) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ₁)
    (W₂ : ArcWit Y₂ (a.restrict β₂) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ₂) : Prop :=
  ∃ (m₂ : SABMap W₁.t Y₂.t χ₂) (h : _),
    W₂ = { t := W₁.t, m := m₂, P := W₁.P, φ := W₁.φ, he := W₁.he, w := W₁.w, e := W₁.e, spec := h } ∧
    UnivCompat Y₁ Y₂ W₁.m m₂

end GlobalTheory.IndefiniteRowSideFullHecke.FractionGeneratorsArcs
end
end
