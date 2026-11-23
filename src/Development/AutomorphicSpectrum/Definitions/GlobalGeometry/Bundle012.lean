module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle011
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle006
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

def punct (n a : ℕ) (ρ : ℝ) : Set (Fin n → ℂ) := {z | z ∈ Metric.ball 0 ρ ∧ ∀ i : Fin n, i.val < a → z i ≠ 0}

def logSize {n : ℕ} (a : ℕ) (z : Fin n → ℂ) : ℝ :=
  1 + ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < a), |Real.log ‖z i‖|

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

structure BdryChart (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) where
  a_le : a ≤ n

  R : Type
  [ring : CommRing R]

  t : SAB H (Sp R)

  g : ℕ
  dim : SmoothOfRelativeDimension g t.G.hom

  M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)

  ψ : (Fin n → ℂ) → (R →+* ℂ)
  hol : IsHolPts (Metric.ball 0 1) ψ

  V : Scheme.{0}

  j : V ⟶ Sp R
  j_open : IsOpenImmersion j

  k : V ⟶ Xo.X

  tV : SAB H V

  m₁ : SABMap tV t j

  m₂ : SABMap tV Xo.univ.t k

  pt : (Fin n → ℂ) → (Sp ℂ ⟶ V)
  pt_eq : ∀ z ∈ punct n a 1, pt z ≫ j = spMap (ψ z) ∧ pt z ≫ k ≫ Xo.s = spMap σ

attribute [instance] BdryChart.ring

def BdryChart.IsVal {Xo : Moduli D l} {σ : KA l →+* ℂ} {n a : ℕ} (C : BdryChart Xo σ n a) (z : Fin n → ℂ) {m : ℕ}
    (u : Fin m → Fin C.g → C.R) (v : Fin m → (epsAt (spMap (C.ψ z)) ⟶ C.t.G)) : Prop :=
  ∀ i, (v i).left = spMap (dualMap (C.ψ z)) ≫ (C.M.pt (u i)).left

def BdryChart.IsRiem {Xo : Moduli D l} {σ : KA l →+* ℂ} {n a : ℕ} (C : BdryChart Xo σ n a) (z : Fin n → ℂ)
    (Hm : Matrix (Fin C.g) (Fin C.g) ℂ) : Prop :=
  ∀ (m : ℕ) (u : Fin m → Fin C.g → C.R) (v : Fin m → (epsAt (spMap (C.ψ z)) ⟶ C.t.G))
    (Γ : Matrix (Fin m) (Fin m) ℂ), C.IsVal z u v →
    (IsHodgeGram C.t.G C.t.PP.L (spMap (C.ψ z)) v Γ ↔
      ∀ i j, Γ i j = Real.pi * hermForm Hm (fun b => C.ψ z (u i b)) (fun b => C.ψ z (u j b)))

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp

open AlgebraicGeometry CategoryTheory NumberField Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

def rootOnFund {Ψ : Type} [DecidableEq Ψ] {N : ℕ} (r a : Ψ × Fin N) : ℤ :=
  if a.1 = r.1 then (if (a.2 : ℕ) + 1 = r.2 then 1 else 0) - (if a.2 = r.2 then 1 else 0) else 0

def fundOnRoot {Ψ : Type} [DecidableEq Ψ] {N : ℕ} (a r : Ψ × Fin N) : ℤ :=
  if r.1 = a.1 ∧ r.2 ≤ a.2 then -1 else 0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}


open Classical in
structure HodgeTie (Y : Model Xo c β) (S : Finset ℕ) (n : ℕ) (M : Top.RootModel (CMType H) (D.p + D.q)) where

  A : HodgeCpt Y S M.y

  Fl : A.Flag

  e : CMType H × Fin (D.p + D.q) → M.Ω
  roots : Fl.RootLines M.xdeg e

  sing : CMType H × Fin (D.p + D.q) → HermLine M.ι
  sing_deg : ∀ r, (sing r).a = M.xdeg r
  hodge : ∀ r, Fl.IsHodgeLine r (e r) (sing r)

  Sy : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (CMType H × Fin (D.p + D.q))

  Re : PB.Realis Sy M.P
  alg : AlgOver Re
  ref_deg : ∀ a, (Re.ref a).a = (Top.combLine sing (fundOnRoot a)).a
  sing_eq : ∀ a x, Re.π x ∉ ReciprocityTheory.AnForm.P.bdry Sy.s →
    Real.log ((Top.combLine sing (fundOnRoot a)).h (Re.R.lift x x)) =
      Real.log ((Re.ref a).h (Re.R.lift x x)) + Sy.ph a (Re.π x)
  line_eq : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ r, ∀ z ∈ mcPts M.P,
    (M.x t r).h z = (Top.combLine (fun a => Re.line a t) (rootOnFund r)).h z
  δ_eq : M.δ = n * Fl.deg
  discr : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ S
  ht_vb : ∀ p ∈ S, ∀ s, ((A.M.htOm A.t.PP.L (p ^ A.R p)).map (A.Vgen s).dualRestrict).IsVBOn
    {q | InFibre A.ξ p q} (labelRk D s) ⊤

def IsImageCpt {Y : Model Xo c β} {S : Finset ℕ} {Ω Ω' : Type} [Field Ω] [Field Ω'] {K K' : Type} [Fintype K]
    [Fintype K'] {J : K → Type} {J' : K' → Type} {y : (Σ k, J k) → Ω} {y' : (Σ k, J' k) → Ω'}
    (Φ : Xo.X ≅ Xo.X) (A : HodgeCpt Y S y) (A' : HodgeCpt Y S y') : Prop :=
  ∃ (x : Sp A.Ω₀ ⟶ Xo.XF c) (x' : Sp A'.Ω₀ ⟶ Xo.XF c) (ψ : A'.Ω₀ ≃+* A.Ω₀),
    A.ξ₀ = x ≫ Y.j ∧ A'.ξ₀ = x' ≫ Y.j ∧
    spMap ψ.toRingHom ≫ x' ≫ Limits.pullback.fst _ _ = x ≫ Limits.pullback.fst _ _ ≫ Φ.hom ∧
    spMap ψ.toRingHom ≫ x' ≫ Limits.pullback.snd _ _ = x ≫ Limits.pullback.snd _ _ ∧
    spMap A.fn ≫ x ≫ Limits.pullback.snd _ _ = spMap A.cst ∧
    spMap A'.fn ≫ x' ≫ Limits.pullback.snd _ _ = spMap A'.cst

end GlobalTheory.CompanionTheory.Ar.Cmp
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Br

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

abbrev FracBase {O : Type} [CommRing O] (β : O →+* c.F) : Prop :=
  Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a

def Reads (U : Set (Xo.XF c)) (τ : E →+* ℂ) (s : Formalism.L2.Pj.Rul Xo c) (φ : FrameFn Xo c) : Prop :=
  ∀ (p : Formalism.L2.Pj.TRing c.F) (z : Formalism.L2.Pj.FrPt Xo c p.R) (F : Type) [Field F] (ψ : p.R →+* F) (y : Sp F ⟶ Xo.XF c),
    under y = spMap ψ ≫ z.x → y ≫ pullback.snd _ _ = spMap (ψ.comp (algebraMap c.F p.R)) → Set.range y ⊆ U →
    ∀ (v : Vecs y D.p) (w : Vecs y D.q) (hp : D.mult τ = D.p) (hq : D.mult (ComplexEmbedding.conjugate τ) = D.q),
      (∀ i, (v i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ (i.cast hp.symm)) →
      (∀ j, (w j).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u (ComplexEmbedding.conjugate τ) (j.cast hq.symm)) →
      ψ (s p z) = φ F y v w

def UnitRule (Y : Model Xo c (RingHom.id c.F)) (U : (Xo.XF c).Opens) (τ : E →+* ℂ) (sig : GlobalTheory.IndefiniteRowSideFullHecke.EigenbasisGramSquares.Rule Y) :
    Prop :=
  ∀ (R : Type) [CommRing R] (j : c.F →+* R) (x : Sp R ⟶ Y.X) v w,
    GlobalTheory.IndefiniteRowSideFullHecke.EigenbasisGramSquares.IsFrame Y U τ j x v w → IsUnit (sig R x v w)

end GlobalTheory.CompanionTheory.Ar.Br
end
end
