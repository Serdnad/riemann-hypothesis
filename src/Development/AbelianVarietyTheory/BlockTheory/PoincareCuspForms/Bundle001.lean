module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import ReciprocityTheory.DualLattices.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Finsupp.Interval
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.LocalRing.Basic

@[expose] public section

section

noncomputable section

open TensorProduct ReciprocityTheory.PGsh

namespace GlobalTheory.IndefiniteRowSideFullHecke.EtaDualPairing

universe u

variable {R₀ : Type u} [CommRing R₀]

theorem isLocalRing_dualNumber (A : Type u) [CommRing A] [IsLocalRing A] :
    IsLocalRing (DualNumber A) := by
  haveI : Nontrivial (DualNumber A) := inferInstanceAs (Nontrivial (A × A))
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.isUnit_iff_isUnit_fst]
  simpa using IsLocalRing.isUnit_or_isUnit_one_sub_self a.fst

def dual (R : LAlg R₀) : LAlg R₀ :=
  @LAlg.mk R₀ _ (DualNumber R) _ _ (isLocalRing_dualNumber R)

def eta (R : LAlg R₀) : dual R := (DualNumber.eps : DualNumber R)

def red (R : LAlg R₀) : LHom (dual R) R :=
  ⟨TrivSqZeroExt.fstHom R₀ R R,
    ⟨fun _ h => TrivSqZeroExt.isUnit_iff_isUnit_fst.2 h⟩⟩

def incl (R : LAlg R₀) : LHom R (dual R) :=
  ⟨TrivSqZeroExt.inlAlgHom R₀ R R,
    ⟨fun _ h => TrivSqZeroExt.isUnit_inl_iff.1 h⟩⟩

theorem red_comp_incl (R : LAlg R₀) : (red R).comp (incl R) = LHom.id R :=
  Subtype.ext (AlgHom.ext fun _ => rfl)

theorem eta_mul_eta (R : LAlg R₀) : eta R * eta R = 0 := DualNumber.eps_mul_eps

theorem red_sqZero (R : LAlg R₀) : (red R).SqZero := by
  refine LHom.sqZero_of_span _ (eta R) (fun a => ⟨(incl R).1 a, rfl⟩) ?_ (eta_mul_eta R)
  ext x
  rw [RingHom.mem_ker, Ideal.mem_span_singleton']
  constructor
  · intro hx
    have key : ∀ b : DualNumber R, TrivSqZeroExt.fst b = 0 →
        (TrivSqZeroExt.inl (TrivSqZeroExt.snd b) : DualNumber R) * DualNumber.eps = b :=
      fun b hb => by ext <;> simp [hb]
    exact ⟨_, key x hx⟩
  · rintro ⟨a, rfl⟩
    have key : ∀ b : DualNumber R, TrivSqZeroExt.fst (b * DualNumber.eps) = 0 := fun b => by simp
    exact key a

def onePlusEta (R : LAlg R₀) (a : R) : (dual R)ˣ where
  val := 1 + eta R * (incl R).1 a
  inv := 1 - eta R * (incl R).1 a
  val_inv := by linear_combination (-((incl R).1 a) ^ 2) * eta_mul_eta R
  inv_val := by linear_combination (-((incl R).1 a) ^ 2) * eta_mul_eta R

variable (B : BX R₀)

end GlobalTheory.IndefiniteRowSideFullHecke.EtaDualPairing
end
end

section

noncomputable section

open IsLocalRing TensorProduct ReciprocityTheory.PGsh

namespace GlobalTheory.IndefiniteRowSideFullHecke.FormalGroupTorsionCharts

universe u v

section Eval

variable {A : Type*} {R : Type*} [CommRing A] [CommRing R] [Algebra A R] {σ : Type*}

def evalTerm (F : MvPowerSeries σ A) (x : σ → R) (d : σ →₀ ℕ) : R :=
  MvPowerSeries.coeff d F • d.prod fun i n => x i ^ n

theorem evalTerm_finite [Finite σ] (F : MvPowerSeries σ A) (x : σ → R)
    (hx : ∀ i, IsNilpotent (x i)) : (Function.support (evalTerm F x)).Finite := by
  classical
  choose N hN using hx
  haveI := Fintype.ofFinite σ
  refine (Set.finite_Iic (Finsupp.equivFunOnFinite.symm N)).subset fun d hd => ?_
  by_contra hcon
  apply hd
  have : ∃ i, N i < d i := by
    by_contra h
    push Not at h
    exact hcon fun i => by simpa using h i
  obtain ⟨i, hi⟩ := this
  have hi0 : i ∈ d.support := by
    rw [Finsupp.mem_support_iff]; omega
  unfold evalTerm
  have h0 : x i ^ d i = 0 := pow_eq_zero_of_le hi.le (hN i)
  rw [Finsupp.prod, Finset.prod_eq_zero (f := fun a => x a ^ d a) hi0 h0, smul_zero]

def evalNil [Finite σ] (F : MvPowerSeries σ A) (x : σ → R) (hx : ∀ i, IsNilpotent (x i)) : R :=
  ∑ d ∈ (evalTerm_finite F x hx).toFinset, evalTerm F x d

theorem evalNil_eq_finsum [Finite σ] (F : MvPowerSeries σ A) (x : σ → R)
    (hx : ∀ i, IsNilpotent (x i)) : evalNil F x hx = ∑ᶠ d, evalTerm F x d :=
  (finsum_eq_sum _ (evalTerm_finite F x hx)).symm

end Eval



variable {R₀ : Type u} [CommRing R₀]

structure ResAlg (k : LAlg R₀) where

  alg : LAlg R₀

  res : LHom alg k
  res_surj : Function.Surjective res.1
  res_ker : RingHom.ker res.1 = maximalIdeal (alg : Type u)

structure NilAlg (k : LAlg R₀) extends ResAlg k where
  nil : ∀ x ∈ maximalIdeal (alg : Type u), IsNilpotent x

variable {k : LAlg R₀}

abbrev Tors (B : BX R₀) (n : ℕ) (R : LAlg R₀) : AddSubgroup (B.G R) :=
  AddSubgroup.torsionBy (B.G R) n

structure TorsionRep (B : BX R₀) (p : ℕ) (O : ResAlg k) where

  A : Tors B p k → ResAlg k

  str : ∀ x, LHom O.alg (A x).alg
  str_res : ∀ x, (A x).res.comp (str x) = O.res

  y : ∀ x, Tors B p (A x).alg
  y_res : ∀ x, B.map (A x).res (y x : B.G (A x).alg) = (x : B.G k)
  universal : ∀ (S : LAlg R₀) (s : LHom O.alg S) (t : Tors B p S),
    ∃! c : Σ x : Tors B p k, LHom (A x).alg S,
      c.2.comp (str c.1) = s ∧ B.map c.2 (y c.1 : B.G (A c.1).alg) = (t : B.G S)

namespace TorsionRep

variable {B : BX R₀} {p : ℕ} {O : ResAlg k} (D : TorsionRep B p O)

variable (C : Type v) [Field C] [Algebra (O.alg : Type u) C]

end TorsionRep

end GlobalTheory.IndefiniteRowSideFullHecke.FormalGroupTorsionCharts
end
end

section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ProperlyDiscontinuousFlags

open NumberField ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def flagTransporter (X : Data E r) (K L : Set (Frame X.Ψ r)) : Set (GL (Fin r) E) :=
  {γ | γ ∈ X.Γ ∧ ∃ x ∈ K, ∃ y ∈ L, ∃ b ∈ Bor X.Ψ r, lact γ x = rmul y b}

def ProperlyDiscontinuousOnFlags (X : Data E r) : Prop :=
  ∀ K : Set (Frame X.Ψ r), IsCompact K → K ⊆ X.dom → (flagTransporter X K K).Finite

end GlobalTheory.IndefiniteRowSideFullHecke.ProperlyDiscontinuousFlags
end
