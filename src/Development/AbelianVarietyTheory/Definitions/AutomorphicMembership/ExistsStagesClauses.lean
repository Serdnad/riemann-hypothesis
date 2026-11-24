module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RationalRootsDef
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResCharConj
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.EventuallyAllScaleContextsAndOfBoth

@[expose] public section

noncomputable section

namespace GlobalTheory.Mem.Top.V4.Model

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField IsDedekindDomain

theorem ev_imp {p q : Ctx → Prop} (hp : Ev p) (h : ∀ K, p K → q K) : Ev q := by
  apply _root_.GlobalTheory.Fc.eventuallyAllScaleContexts_mono_of_imp <;> assumption

theorem mem_iff {X : Stages} {f : Fr X.B.toPre} {T : TwDat X.B} {Wt : Set X.B.places.Pl} {xi : X.C.Tup → HChar X.B.host.E}
    (h : MuIsW X f T Wt xi) (w : X.B.places.Pl) : w ∈ Wt ↔ X.W.muAt w ≠ X.C.mu0 := by
  refine ⟨fun hw he => ?_, fun hw => by_contra fun hn => hw (h.off w hn)⟩
  have h1 := h.tw w
  rw [← h.on w hw, he, h.mu0] at h1
  exact (TwFin.tw_fin X.B f T).2.1 w h1.symm

variable (hH : DC.HostExQ) (hLP : LevelPrime) (hSP : SmallPrimeOne) (h2b : StandardLattice.SiegelMassRatioCM)






end GlobalTheory.Mem.Top.V4.Model

end
