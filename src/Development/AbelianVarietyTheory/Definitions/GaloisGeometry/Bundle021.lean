module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CuspFormLimitTwoPlaces
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle015
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong MvPolynomial

namespace GlobalTheory.CongL

def DGen (a : ℕ) : MvPolynomial (Fin a) ℤ :=
  (∏ i : Fin a, ∏ j : Fin a, if i = j then 1 else ∏ c ∈ Finset.range a, (X i ^ (c + 1) - X j ^ (c + 1))) *
  (∏ i : Fin a, ∏ j : Fin a, ∏ k : Fin a, if j = i ∨ j = k then 1 else (X i * X k - X j ^ 2)) *
  (∏ m ∈ (Finset.univ : Finset (Fin a → Fin (a + 1))).filter (fun m => (∑ i, (m i : ℕ)) = a ∧ m ≠ fun _ => 1),
    ((∏ i, X i ^ (m i : ℕ)) - ∏ i, X i))

def GapJ (a : ℕ) (J : Multiset ℤ) : Prop :=
  ∀ i : ℕ, i + 1 < a →
    (J.sort (· ≤ ·)).getD (i + 1) 0 - (J.sort (· ≤ ·)).getD 0 0 > (a : ℤ) * ((J.sort (· ≤ ·)).getD i 0 - (J.sort (· ≤ ·)).getD 0 0)

def WtLac : SeedWtU := fun E _ _ _ l _ a ι w₀ v' U U' =>
  SameWtOff ι w₀ v' U U' ∧ ∃ τ₀ : E →+* ℂ, OverPl ι τ₀ v' ∧ ∀ lam, HasWeightAt U' τ₀ lam → ∀ J : Multiset ℤ,
    J.map (fun n : ℤ => (n : ℂ)) = (infOfWeight lam).map (fun z => ((a : ℂ) - 1) / 2 - z) → GapJ a J

end GlobalTheory.CongL

end
end

section

noncomputable section

namespace GlobalTheory.Pdv

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

def ColNorm : Prop :=
  ∀ a, B.R.m ≤ (I.cst a).A ∧ (I.cst a).M ≤ B.R.m ∧
    ∀ j, j ≤ B.R.m - 2 + 1 → ∀ (b : (I.idx a).β j) (P : rowSG (B.primes X) I.sel (I.tup a)), P.1 ∈ (B.primes X).vGs → (I.idx a).h j b P = 1

variable (l : I.Laws) (Z : TC.Later B (I.cols l))

def stabStd (u : B.Word) (a : I.ι) : GlobalTheory.KerJ.StabDat ((I.rec7 l Z).chTw u a) := fun i c =>
  {g | ∃ s : (I.stp u a i).Stab c, g = ((((I.stp u a i).gam c.1 s.1 : GL (Fin (B.R.N i)) B.host.E) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.host.E),
    B.embLL (((I.stp u a i).chr c.1 s.1 : B.LLˣ) : B.LL))}

def RdStd (u : B.Word) (a : I.ι) (r : KerRead ((I.rec7 l Z).chTw u a) B.fields) : Prop :=
  (∀ i c, r.N i c = ((I.stp u a i).rep c).1.1.deco.1.N) ∧
    ∀ i, i < B.R.m → ∀ c c' x, r.Xi i c c' x = B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1 c'.1
      ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c') x)

def StdRd {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)}
    {K : G.Consts} {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX} (t : KerEntTied ex) : Prop :=
  ∀ u a, ∃ r : KerRead ((I.rec7 l Z).chTw u a) B.fields, HEq (t.rd u a) r ∧ RdStd I l Z u a r

end GlobalTheory.Pdv

end
end
