module

public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.SharpRestriction.Divisibility.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
public import Formalism.LocalRingCardinality.Bundle008
public import Formalism.SharpRestriction.Bundle001
public import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.ZetaProductPairs

open Formalism.BasicNotions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure Loc (D : D7) (T : ThetaX D) where

  gl1 : D.what₂.Word → T.Gf (D.sp.Y 0)

  glSym : D.what₂.Word → T.Gf (D.sp.Y 0)

  ArchDat : D.what₂.Word → Type
  ArchDat_ne : ∀ u, Nonempty (ArchDat u)

  ellT : ∀ u, ArchDat u → ℂ

  Au : ∀ u, ArchDat u → ℂ

  B0 : ∀ u, D.what₂.Mu u →ₗ[ℂ] D.what₂.EE →ₗ[ℂ] ℂ

  zeX : D.what₂.Word → D.what₂.Tup → ℂ

  zeta_at_base_tuple : ∀ u, zeX u D.what₂.mu0 = 1

  zeX_fin : ∀ u μ, ∃ n : ℕ, 0 < n ∧ zeX u μ ^ n = 1

variable {D : D7}

variable {T : ThetaX D}

section Local

open MeasureTheory Matrix ComplexConjugate Finset

def qE (q : ℝ) (a c : ℕ) : ℝ := ∏ i ∈ Icc a c, (1 - q ^ (-(i : ℤ)))

def zetaProd (q : ℝ) (n : ℕ) : ℝ := (qE q 1 n)⁻¹

def idxPar (q : ℝ) (r s : ℕ) : ℝ := TH.parIdx q r s

def Lpair (q : ℝ) (t : ℕ) (x : ℂ) : ℂ :=
  (∏ s ∈ Icc 1 t, ((1 - x * ((q : ℂ) ^ (-(s : ℤ)))) * (1 - x⁻¹ * ((q : ℂ) ^ (-(s : ℤ))))))⁻¹


end Local

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (A : TH.ProvA)
  (GF : ∀ x (i : Fm.Ix x), Formalism.MainNotions.product_first_zeroth_parts.Th22 (Fm.D x i))
  (XF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Loc (Fm.D x i) (Fm.ex x hx i).th)

end Family

end Formalism.MainNotions.ZetaProductPairs

end
end

section

noncomputable section

open NumberField MvPolynomial Finset
open scoped BigOperators

namespace Formalism.MainNotions.LatticeTransfer

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.DegreeFormula

def wt (Tau : Type) [Fintype Tau] (N : ℕ) : Vm Tau N → ℕ
  | Sum.inl _ => 1
  | Sum.inr (_, k) => k

structure Loc (D : D7) (XD : DivX D) where

  rt : letI := D.host.cmStar; ∀ (S : HSpace D.host.E) (κ : XD.Lev) (p : ℕ) [Fact p.Prime]
    (la : XD.PlP p) (z : XD.Mp S κ p la), Bool × Rt D.what₂.Tau (XD.shv S κ).N → (XD.md S κ p la z).Z.LB

  rt_lie : letI := D.host.cmStar; ∀ (S : HSpace D.host.E) (κ : XD.Lev), HidaSetting D XD S κ →
    ∀ (p : ℕ) [Fact p.Prime] (la : XD.PlP p) (z : XD.Mp S κ p la) (τ0 : D.what₂.Tau) (τ : Emb D p), (XD.jC p la).comp τ = tauEmb D τ0 →
    ∀ (i : Fin (rkOf (PsiOf D (XD.jC p la)) (XD.shv S κ).N (XD.shv S κ).j τ)) (i' : Fin (XD.shv S κ).N),
      (i' : ℕ) = i →
      rt S κ p la z (false, (τ0, i')) = ((XD.md S κ p la z).lie τ).x i ∧
      rt S κ p la z (true, (τ0, i')) = ((XD.md S κ p la z).lie τ).x' i

  rt_om : letI := D.host.cmStar; ∀ (S : HSpace D.host.E) (κ : XD.Lev), HidaSetting D XD S κ →
    ∀ (p : ℕ) [Fact p.Prime] (la : XD.PlP p) (z : XD.Mp S κ p la) (τ0 : D.what₂.Tau) (τ : Emb D p), (XD.jC p la).comp τ = tauEmb D τ0 →
    ∀ (i : Fin ((XD.shv S κ).N - rkOf (PsiOf D (XD.jC p la)) (XD.shv S κ).N (XD.shv S κ).j τ))
      (i' : Fin (XD.shv S κ).N), (i' : ℕ) = (XD.shv S κ).j + i →
      rt S κ p la z (false, (τ0, i')) = ((XD.md S κ p la z).om τ).x i ∧
      rt S κ p la z (true, (τ0, i')) = ((XD.md S κ p la z).om τ).x' i

  lieW_gen : letI := D.host.cmStar; ∀ (S : HSpace D.host.E) (κ : XD.Lev), HidaSetting D XD S κ →
    ∀ (p : ℕ) [Fact p.Prime] (la : XD.PlP p) (z : XD.Mp S κ p la), ∃ (e : Fin (D.R.f * (XD.shv S κ).N) ≃ Rt D.what₂.Tau (XD.shv S κ).N)
      (V : Fin (D.R.f * (XD.shv S κ).N) → (XD.md S κ p la z).Z.VDiv), ∀ l,
      (XD.md S κ p la z).Z.c1 ((XD.md S κ p la z).lieW.x l) =
        (if ((e l).2 : ℕ) < (XD.shv S κ).j then (1 : ℚ) else -1) •
            (XD.md S κ p la z).Z.c1 (rt S κ p la z (false, e l)) +
          (XD.md S κ p la z).Z.cD (V l)

section One
variable (D : D7) (XD : DivX D) (T : Loc D XD)
  (S : letI := D.host.cmStar; HSpace D.host.E) (κ : XD.Lev)

def adm1 : Prop :=
  ∀ p : ℕ, p.Prime → ∀ c : (XD.shv S κ).FibComp p, ¬ (XD.shv S κ).fibInBd p c

end One

def PointsLemma (D : D7) (XD : DivX D) (P : DIV.Align.PrinLev XD) : Prop :=
  ∀ S κ, HidaSetting D XD S κ → DIV.Align.LevB P κ → ∀ (Sx : Finset ℕ) (R : ℝ) (p : ℕ),
  p.Prime → p ≠ 2 → UnramE D p → p ∉ (XD.shv S κ).lev → ∀ (τ : D.what₂.Tau) (k : ℕ), 1 ≤ k →
  ∀ (m : ℕ), m + k = dimFl D.what₂.Tau (XD.shv S κ).N + 1 →
  ∀ Q : MvPolynomial (Vm D.what₂.Tau (XD.shv S κ).N) ℝ,
    Q.IsWeightedHomogeneous (wt D.what₂.Tau (XD.shv S κ).N) m →
    (XD.shv S κ).arMix Sx R p
        ((tagDR D.what₂.Tau _ (C ((Nat.factorial k : ℝ)⁻¹) * pk D _ τ k) -
          tagHT D.what₂.Tau _ (C ((Nat.factorial k : ℝ)⁻¹) * pk D _ τ k)) * Q) =
      Real.log p * ((∑' n : ℕ, ((p : ℝ) ^ k)⁻¹ ^ (n + 1) *
          (XD.shv S κ).chern (chLie (XD.shv S κ).j (k - 1) (frobEmb D p (n + 1) (Sum.inl τ)) *
            collapse D _ Q)) -
        (XD.shv S κ).chern (chLie (XD.shv S κ).j (k - 1) (Sum.inl τ) * collapse D _ Q) /
          ((p : ℝ) - 1))

section One1
variable (D : D7) (XD : DivX D) (T : Loc D XD)
  (S : letI := D.host.cmStar; HSpace D.host.E) (κ : XD.Lev)

end One1

end Formalism.MainNotions.LatticeTransfer

end
end

section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.WeightThresholdDefs

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.DegreeFormula

open Classical

def dE (D : D7) : ℕ := (NumberField.discr D.host.E).natAbs

section Derived
variable {D : D7} (Y : ShimX D.what₂.Tau)

abbrev dimY : ℕ := dimFl D.what₂.Tau Y.N

def gap (lam : D.what₂.Tau → Fin Y.N → ℝ) (τ : D.what₂.Tau) : ℝ :=
  lam τ ⟨Y.j - 1, by have := Y.j_lt; omega⟩ - lam τ ⟨Y.j, Y.j_lt⟩

def supAbs (lam : D.what₂.Tau → Fin Y.N → ℝ) : ℝ := ⨆ x : Rt D.what₂.Tau Y.N, |lam x.1 x.2|

def bigB0 (u : D.what₂.Tau → Fin Y.N → ℝ) (g : ℝ) : ℝ :=
  4 * (D.R.f : ℝ) * (Y.N : ℝ) ^ 2 * (1 + supAbs Y u / g)

end Derived

def cP (p : ℕ) : ℝ := 1 / ((p : ℝ) - 1)

variable {D : D7} (V : DivX D) (P : DIV.Align.PrinLev V)

def TrivialFlagIntersectionCond : Prop := ∀ S κ, HidaSetting D V S κ → DIV.Align.LevB P κ → ∀ (Sx : Finset ℕ) (R : ℝ) (p : ℕ), p.Prime →
  ∀ (τ : D.what₂.Tau) (k : ℕ), 1 ≤ k → ∀ Q : MvPolynomial (Rt D.what₂.Tau (V.shv S κ).N) ℝ,
    (V.shv S κ).arMix Sx R p (tagHT D.what₂.Tau _ (pk D _ τ k) *
      (tagDR D.what₂.Tau _ Q - tagHT D.what₂.Tau _ Q)) = 0

structure Loc4 where

  dRho : V.Surf → ℕ
  dRho_pos : ∀ t, 0 < dRho t

  CHr : V.Surf → Type
  instCHr : ∀ t, AddCommGroup (CHr t)

  ch2 : ∀ t, CHr t

  ch2o : ∀ t, CHr t

  arithFirstChernHom : ∀ t, ℝ →+ CHr t

  degA : ∀ t, CHr t →+ ℝ

attribute [instance] Loc4.instCHr

section Fam
variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (PL : DIV.Align.PrinLevF Fm)

end Fam

end Formalism.MainNotions.WeightThresholdDefs

end
end
