module

public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle002
public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle003
public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle001
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain

namespace Formalism.L2

structure AUTied (D : D7) (L : LPTiedPlaceholder D) (M : MtFam D) (A : AVTied D M) where

  cls : ∀ j, 1 ≤ j → j ≤ D.R.m → NG.AutRep D.host.E D.R.nV → D.nbc.AU j
  surj : ∀ j h1 h2, Function.Surjective (cls j h1 h2)
  iso : ∀ j h1 h2 π π', cls j h1 h2 π = cls j h1 h2 π' ↔ π.Iso π'

  mult : ∀ j h1 h2 π, D.nbc.multAU j (cls j h1 h2 π) = π.mult

  sph : ∀ j h1 h2 π (w : PlE D.host) v, ¬ IsSplitPl D.host w → NG.OverPl w v →
    (D.nbc.sphAU j (cls j h1 h2 π) w ↔ π.SphAt v)

  sat : ∀ j h1 h2 π v (w : PlE D.host), NG.OverPl w v → ∀ (Dv : InertDatum D.host.E D.R.nV v w), (∃ α, NG.SatAt π Dv α) →
    ∃ α, NG.SatAt π Dv α ∧ D.nbc.satAU j (cls j h1 h2 π) w = Finset.univ.val.map α

  clsWt : ∀ j, 1 ≤ j → j ≤ D.R.m → NG.AlgWt D.host.E D.R.nV → D.nbc.Wt j
  surjWt : ∀ j h1 h2, Function.Surjective (clsWt j h1 h2)
  isoWt : ∀ j h1 h2 a b, clsWt j h1 h2 a = clsWt j h1 h2 b ↔ a.Iso b

  wt : ∀ j h1 h2 π a, π.toAlgWt.IsDual a → D.nbc.wtAU j (cls j h1 h2 π) = clsWt j h1 h2 a

  infW : ∀ j h1 h2 a (τ : D.host.E →+* ℂ) lam, a.HWAt τ lam → D.nbc.infW j (clsWt j h1 h2 a) τ = NG.infOf lam

  emb : ∀ i P, D.nbc.embAV i P = cls (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2 (A.rep i P)

structure NGalTied (D : D7) where
  fr : OmFrame D
  lp : LPTiedPlaceholder D
  mt : MtFam D
  hecke : HeckeTied D mt
  av : AVTied D mt
  au : AUTied D lp mt av

  rational : HeckeRational D mt

  tup : D.what₂.Tup → Fin D.R.m → Host.HChar D.host.E

  level : LevelTied D mt tup

end Formalism.L2
end
end

section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain

namespace Formalism.L2

variable {D : D7} {C : Host.CharFrame D} {nch : NChoice D}

theorem qPl_tup (Tp : Host.TupTied D C nch) (μ : D.what₂.Tup) (j : Fin D.R.m) :
    qPl D (Tp.tup μ j) = {v | v ∉ gPl D ∧ ∃ w : PlE D.host, NG.OverPl w v ∧ ¬ (Tp.xi μ).UnrAt w} := by
  ext v
  simp only [qPl, Set.mem_ofPred_eq, Host.TupTied.tup]
  refine and_congr_right fun hv => exists_congr fun w => and_congr_right fun hw => not_congr ?_
  have hm : (C.mu0 j).UnrAt w := by
    refine (C.isMu0 j).unr w fun k hk => hv ?_
    simp only [gPl, Set.mem_ofPred_eq]
    exact ⟨w, hw, k, hk⟩
  constructor
  · intro h x hx
    have hx' := h x hx
    change (C.mu0 j).loc w x * (Tp.xi μ).loc w x = 1 at hx'
    rw [hm x hx, one_mul] at hx'
    exact hx'
  · intro h x hx
    change (C.mu0 j).loc w x * (Tp.xi μ).loc w x = 1
    rw [hm x hx, h x hx, one_mul]

end Formalism.L2
end
end
