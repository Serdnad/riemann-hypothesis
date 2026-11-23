module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle016
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle020
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle002
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1880
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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeSupSt

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def HkSupSized : Prop :=
  ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize.SizeOK D → ∀ (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type)
    (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A),
    R.Char F → ∀ (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
      (_fw : FWTie T R κ v₀) (i : Fin D.R.m), GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.ReadAt0 T R κ v₀ i → GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.HkSupAt T R i

def HeckeReadTie : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), σ = T.σ₀ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i,
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i σ hV → GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.ReadsAt T R i σ hV (κ i)

section Checks

open GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [iA : Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}


end Checks

end GlobalTheory.HeckeSupSt
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames

namespace GlobalTheory.RowClaim.StepsModel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {T : Type}

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}


theorem exists_isTermVol {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {μ₀ : T}
    (hL : L.Is μ₀) (t : T) (Φ : G.Datum) (β : CosFam G t) : ∃ M, IsTermVol t S Φ β M := by
  obtain ⟨M₀, -⟩ := exists_vol G hL t
  have H : ∀ X : Node, ∃ (μ : Measure (GA D (G.V X))) (𝓕 : Set (GA D (G.V X))), (∀ j (h : j < D.R.m) (e : X = .top j), by
        subst e; exact if (Node.top j).neg D.R.m = 0 then IsMeasDef _ (S.levTop t Φ β j h) μ 𝓕
          else Lev.IsMeasFD _ (S.levTop t Φ β j h) μ 𝓕) ∧
      ∀ i (h : i ≤ D.R.m) (e : X = .grid i D.R.m), by
        subst e; exact if (Node.grid i D.R.m).neg D.R.m = 0 then IsMeasDef _ (S.levRow t i h) μ 𝓕
          else Lev.IsMeasFD _ (S.levRow t i h) μ 𝓕 := fun X => by
    by_cases h1 : ∃ j, j < D.R.m ∧ X = .top j
    · obtain ⟨j, hj, rfl⟩ := h1
      have hV := node_isV G hL (X := .top j) hj.le
      obtain ⟨μ, 𝓕, e⟩ := exists_meas _ hV.sigOK (fun τ => congrArg Prod.snd (hV.sig τ)) _ (S.isCO_levTop W t Φ β hj)
      refine ⟨μ, 𝓕, fun j' h e' => ?_, fun _ _ e' => by cases e'⟩
      cases e'; exact e
    · by_cases h2 : ∃ i, i ≤ D.R.m ∧ X = .grid i D.R.m
      · obtain ⟨i, hi, rfl⟩ := h2
        have hV := node_isV G hL (X := .grid i D.R.m) ⟨hi, le_rfl⟩
        obtain ⟨μ, 𝓕, e⟩ := exists_meas _ hV.sigOK (fun τ => congrArg Prod.snd (hV.sig τ)) _ (S.isCO_levRow W t hi)
        refine ⟨μ, 𝓕, fun _ _ e' => (by cases e'), fun j' h e' => ?_⟩
        cases e'; exact e
      · exact ⟨0, ∅, fun j h e => absurd ⟨j, h, e⟩ h1, fun i h e => absurd ⟨i, h, e⟩ h2⟩
  choose ν fd hν using H
  exact ⟨⟨ν, fd, M₀.νN, M₀.fdN⟩, fun j h => (hν _).1 j h rfl, fun i h => (hν _).2 i h rfl⟩

end GlobalTheory.RowClaim.StepsModel

end
end
