module

public import Formalism.AdmissibleDesigns.CharacterTrivialWhereLattice
public import Formalism.AdmissibleDesigns.SelmerInequalityOfInputs
public import Formalism.AdmissibleDesigns.TrCMemZ1D
public import Formalism.AdmissibleDesigns.Bundle007
public import Formalism.AdmissibleDesigns.FiniteClassesContinuousLattice
public import Formalism.AdmissibleDesigns.KernelLengthHigherColumns
public import Formalism.AdmissibleDesigns.RankReductionIdempotentOne
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle007
public import Formalism.AdmissibleDesigns.Bundle010
import Formalism.AdmissibleDesigns.EKSymmCont
public import Formalism.AdmissibleDesigns.IsDROfWpIso
public import Formalism.AdmissibleDesigns.MemIntegralSpanIffImage
import Formalism.AdmissibleDesigns.Bundle004
public import Formalism.AdmissibleDesigns.ToH1Cocycles
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.AdmissibleDesigns.GlobalIndexTheoremPlacesOfRNAdm
import Formalism.WachLatticeTwists.SplitClassesAll.Statement
public import Formalism.AdmissibleDesigns.CohomZeroEquivContinuous
import Formalism.AdmissibleDesigns.PiEquiv2

@[expose] public section

section

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core] [hH0Fin : Fact Formalism.MainNotions.N.K.H0.FinCore]

noncomputable section

open Finset Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.K.StC

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.SplitClassesAll Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop cupFG)
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)
open Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K Formalism.RepresentationBoundsCohomology.SF

attribute [local instance 2000] Topo.fracTopology Topo.rTopology

section Clauses

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
  (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (cB : ℕ)


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
def ClauseTB : Prop :=
  ∀ c : Fin (D.R.t + 1), 1 ≤ (c : ℕ) → ∀ w ∈ rowsN i dc,
      (∀ ψ : Ymod Dd.r Dd.χ Dd.E →ₗ[D.nd.O i] blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk c,
        (∀ g ∈ (decs D.host.E (Aw i dc)) w, ∀ y, ψ (uElt Dd.r Dd.χ g • y) = uElt Dd.r Dd.χ g • ψ y) →
        ∀ z : coZ1s (QS.resU i dc Dd c w),
          (∀ g : (decs D.host.E (Aw i dc)) w, (z : (decs D.host.E (Aw i dc)) w → blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk c) g =
            ψ (yY Dd.r Dd.χ Dd.E (g : GE D.nd))) →
          (((D.nd.l i : ℕ) : D.nd.O i) ^ cB) • (Submodule.mkQ _ z : H1z (QS.resU i dc Dd c w)) ∈
            St.FS i r π dc g0 eB e₁ s Dd hD hc c w) ∧
      Module.length (D.nd.O i) (↥(lcH1 (QS.resU i dc Dd c w) ⊓
          divBy (St.FS i r π dc g0 eB e₁ s Dd hD hc c w) (((D.nd.l i : ℕ) : D.nd.O i) ^ cB)) ⧸
        (St.FS i r π dc g0 eB e₁ s Dd hD hc c w).comap (lcH1 (QS.resU i dc Dd c w) ⊓
          divBy (St.FS i r π dc g0 eB e₁ s Dd hD hc c w) (((D.nd.l i : ℕ) : D.nd.O i) ^ cB)).subtype) ≤
        eON i * (cB : ℕ∞) * ((ReciprocityTheory.Gal.locDeg (plOf i dc w) : ℕ∞) + 1)




def ClauseChi : Prop :=
  ∀ c : Fin (D.R.t + 1), 2 ≤ (c : ℕ) →
    InChiFixReal (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk c) Dd.r Dd.χ Dd.E (colIdx i dc) (decs D.host.E (Aw i dc)) (rowsN i dc)
      (qsN i dc) (ShaN i ((c : ℕ) - 1)) (St.FS i r π dc g0 eB e₁ s Dd hD hc c) (QS.Io i) (QS.IS i) (QS.I i dc)
      (QS.γQ i dc) (QS.ζ i dc Dd) (QS.ζO i dc) (QS.nQ i dc)




def ClauseLoc1 : Prop :=
  InChiLoc (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk QS.c1) Dd.r Dd.χ Dd.E (decs D.host.E (Aw i dc)) (qsN i dc)
    (St.FS i r π dc g0 eB e₁ s Dd hD hc QS.c1) (QS.Io i) (QS.IS i) (QS.I i dc) (QS.γQ i dc) (QS.ζ i dc Dd)
    (QS.ζO i dc) (QS.nQ i dc)

end Clauses

section Proofs

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
  (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (cB : ℕ)

theorem locPos (hE : QS.Ev r π Dd) (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (hG4 : TruncatedSeriesCountingIdentities.admG4 i r)
    (hdec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) (hG5 : TruncatedSeriesCountingIdentities.admG5 i r) (h5x : TruncatedSeriesCountingIdentities.TameGeneratorConditions i) (hQP : QS.QPow i)
    (c : Fin (D.R.t + 1)) (hc0 : c ≠ 0) : QS.LocClause i dc Dd c := by
  obtain ⟨c', rfl⟩ := Fin.exists_succ_eq.mpr hc0
  apply QS.locClause (dc := dc) (hE := hE) (hN := hN) (hG4 := hG4) (hdec := hdec) (hG5 := hG5) (h5x := h5x)
    (hQP := hQP) (c' := c') (hS := QS.locS (hE := hE) (hN := hN) (hG5 := hG5) (h5x := h5x) (c' := c'))

theorem FS_eq (c : Fin (D.R.t + 1)) (hc0 : c ≠ 0) :
    St.FS i r π dc g0 eB e₁ s Dd hD hc c = QS.Fpos i dc Dd c := by
  obtain ⟨c', rfl⟩ := Fin.exists_succ_eq.mpr hc0
  funext w
  rfl

theorem first_character_index_ne_zero : (QS.c1 (D := D)) ≠ 0 := by
  intro h
  have h' := congrArg Fin.val h
  simp [QS.c1] at h'




theorem first_local_clause_of (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (hG4 : TruncatedSeriesCountingIdentities.admG4 i r) (hdec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π)
    (hG5 : TruncatedSeriesCountingIdentities.admG5 i r) (h5x : TruncatedSeriesCountingIdentities.TameGeneratorConditions i) (hQP : QS.QPow i) :
    ClauseLoc1 i r π dc g0 eB e₁ s Dd hD hc := by
  have hE := QS.ev_of (hD := hD)
  unfold ClauseLoc1
  rw [FS_eq (dc := dc) (hD := hD) (hc := hc) (c := QS.c1) (hc0 := first_character_index_ne_zero)]
  exact locPos (dc := dc) (hE := hE) (hN := hN) (hG4 := hG4) (hdec := hdec) (hG5 := hG5) (h5x := h5x)
    (hQP := hQP) (c := QS.c1) (hc0 := first_character_index_ne_zero)




theorem chi_of (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (hG4 : TruncatedSeriesCountingIdentities.admG4 i r) (hdec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π)
    (hG5 : TruncatedSeriesCountingIdentities.admG5 i r) (h5x : TruncatedSeriesCountingIdentities.TameGeneratorConditions i) (hQP : QS.QPow i) :
    ClauseChi i r π dc g0 eB e₁ s Dd hD hc := by
  have hE := QS.ev_of (hD := hD)
  unfold ClauseChi
  intro c hc2
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc2
  refine And.intro ?_ ?_
  · rw [FS_eq (dc := dc) (hD := hD) (hc := hc) (c := c) (hc0 := hc0)]
    exact locPos (dc := dc) (hE := hE) (hN := hN) (hG4 := hG4) (hdec := hdec) (hG5 := hG5) (h5x := h5x)
      (hQP := hQP) (c := c) (hc0 := hc0)
  · exact ShaT.tieSel2_full (dc := dc) (hD := hD) (hN := hN) (F0 := St.FirstBlockLocalConditions i r π dc g0 eB e₁ s Dd hD hc)
      (c := c) (hc := hc2)


omit [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)] in


theorem FS_row (c : Fin (D.R.t + 1)) (hc0 : c ≠ 0) {w : ℕ} (hw : w ∈ rowsN i dc) :
    St.FS i r π dc g0 eB e₁ s Dd hD hc c w = TB.Fc i dc Dd c w := by
  obtain ⟨c', rfl⟩ := Fin.exists_succ_eq.mpr hc0
  show QS.Fpos i dc Dd c'.succ w = TB.Fc i dc Dd c'.succ w
  rw [QS.Fpos_row (Dd := Dd) (c := c'.succ) (hw := hw)]
  rfl


omit [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)] in


theorem tb_of_target (hT : TB.TBTarget i dc Dd cB) : ClauseTB i r π dc g0 eB e₁ s Dd hD hc cB := by
  intro c hc1 w hw
  have hc0 : c ≠ 0 := fun h => by
    have := congrArg Fin.val h
    simp only [Fin.val_zero] at this
    omega
  have hF : St.FS i r π dc g0 eB e₁ s Dd hD hc c w = TB.Fc i dc Dd c w :=
    FS_row i r π dc g0 eB e₁ s Dd hD hc c hc0 hw
  have hx := hT w hw c hc1
  rewrite [← hF] at hx
  exact ⟨hx.2.2.1, hx.2.2.2⟩

end Proofs

section ForRN

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd (Norm.rN i r ρ π)) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
  (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i (Norm.rN i r ρ π)) (cB : ℕ)

end ForRN

end Formalism.MainNotions.N.K.StC

end
end

section

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core] [hH0Fin : Fact Formalism.MainNotions.N.K.H0.FinCore]

noncomputable section

open Finset Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.K.StA

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop cupFG)
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)
open Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K Formalism.RepresentationBoundsCohomology.SF Formalism.MainNotions.N.K.St

attribute [local instance 2000] Topo.fracTopology Topo.rTopology

section Cols2

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]




theorem colLx
    (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (hBK : TruncatedSeriesCountingIdentities.admBK i) (hG2 : TruncatedSeriesCountingIdentities.admG2 i r ρ π) (hFont : TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i)
    (hDec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) (hFin : LargeLevelLemmas.tateH1FinitenessAtPlacesOver i) :
    ∀ x' : Dd.X', Dd.p x' ∉ (D.nd.Z i : Set (D.nd.X i)) → ∀ l : Col i dc,
      ∃ Lx : Submodule (FractionRing (D.nd.O i))
          ((decs D.host.E (Aw i dc)) (colIdx i dc l) → EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x'),
        LinearMap.range (colD (K := FractionRing (D.nd.O i)) (V := EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x') Dd.r Dd.χ
          ((decs D.host.E (Aw i dc)) (colIdx i dc l))) ≤ Lx ∧
        (∀ (f : LeftId (D.nd.O i) Dd.e₁ →ₗ[Dd.R'] EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x')
          (z : coZ1s (resRep (uRep (D.nd.O i) (M := LeftId (D.nd.O i) Dd.e₁) Dd.r Dd.χ)
            ((decs D.host.E (Aw i dc)) (colIdx i dc l)))),
          Submodule.mkQ _ z ∈ KHf.Hfe₁ i dc Dd.r Dd.χ (Pe := LeftId (D.nd.O i) Dd.e₁) l →
          (fun g : (decs D.host.E (Aw i dc)) (colIdx i dc l) =>
            f ((z : (decs D.host.E (Aw i dc)) (colIdx i dc l) → LeftId (D.nd.O i) Dd.e₁) g)) ∈ Lx) ∧
        (∀ (f : LeftId (D.nd.O i) Dd.E →ₗ[Dd.R'] EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x')
          (z : coZ1s (resRep (uRep (D.nd.O i) (M := LeftId (D.nd.O i) Dd.E) Dd.r Dd.χ)
            ((decs D.host.E (Aw i dc)) (colIdx i dc l)))),
          Submodule.mkQ _ z ∈ KHf.Hfe₁ i dc Dd.r Dd.χ (Pe := LeftId (D.nd.O i) Dd.E) l →
          (fun g : (decs D.host.E (Aw i dc)) (colIdx i dc l) =>
            f ((z : (decs D.host.E (Aw i dc)) (colIdx i dc l) → LeftId (D.nd.O i) Dd.E) g)) ∈ Lx) ∧
        Module.rank (FractionRing (D.nd.O i))
            (Lx ⧸ (LinearMap.range
              (colD (K := FractionRing (D.nd.O i)) (V := EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x') Dd.r Dd.χ
                ((decs D.host.E (Aw i dc)) (colIdx i dc l)))).comap Lx.subtype) ≤
          (jN i ρ π dc (colIdx i dc l) + Module.finrank (FractionRing (D.nd.O i))
            (LinearMap.ker
              (colD (K := FractionRing (D.nd.O i)) (V := EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x') Dd.r Dd.χ
                ((decs D.host.E (Aw i dc)) (colIdx i dc l)))) : ℕ) := by
  have hρ := K.Norm.rhoCont_of i r ρ π hDec hc
  refine colLx_of_ringDef i r ρ π dc g0 eB e₁ s Dd hD hc hBK hG2 hFont hDec
    (fun x' l => K.Font.crysX_of (i := i) (dc := dc) (r := r) (π := π) (g0 := g0) (eB := eB) (e₁ := e₁) (s := s)
      (Dd := Dd) ρ hG2 hD x' l)
    (fun x' l => K.Font.negX_of (i := i) (dc := dc) (r := r) (ρ := ρ) (π := π) (g0 := g0) (eB := eB) (e₁ := e₁)
      (s := s) (Dd := Dd) hFont hG2 hDec hc hρ hD x' l)
    (fun x' l => KTate.finX (i := i) (dc := dc) (r := Dd.r) (χ := Dd.χ) hFin x' l
      (KDim.contX_of_orbC i dc Dd.r Dd.χ x' l (KOrb.orbC_repE i dc r π g0 eB e₁ s Dd hD hc x' (colIdx i dc l))))
    (fun l => K.Font.crysW_of (i := i) (dc := dc) (r := r) (ρ := ρ) (π := π) hFont hG2 hDec hc hρ l)

end Cols2

end Formalism.MainNotions.N.K.StA

end
end

section

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core] [hH0Fin : Fact Formalism.MainNotions.N.K.H0.FinCore]

noncomputable section

open Finset Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.K.StB

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop cupFG)
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)
open Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K Formalism.RepresentationBoundsCohomology.SF Formalism.MainNotions.N.K.St

attribute [local instance 2000] Topo.fracTopology Topo.rTopology

section Rho2

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
  (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r)
  (hT : Dd.Top (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R))
  (hrk : ((Dd.ρk 0 Dd.e₁).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))).rank = 1)




theorem selFS_of_normAt (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) :
    TieSel1 i ρ π (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) Dd.r Dd.χ (colIdx i dc) (decs D.host.E (Aw i dc))
      (rowsN i dc) (FS i r π dc g0 eB e₁ s Dd hD hc 0) (QS.Io i) := by
  letI := fun w => modS i r π dc g0 eB e₁ s Dd hD hc w
  haveI := fun w => KLat.towerT Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i)
    (hM0 i r π g0 eB e₁ s Dd hD hc) w
  letI := fun w => modS' i r π dc g0 eB e₁ s Dd hD hc w
  haveI := fun w => KLat.towerT' Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i)
    (hM0 i r π g0 eB e₁ s Dd hD hc) w
  exact Bk.tieSel1_K i dc Dd (hKm i) (hEps i) (hM0 i r π g0 eB e₁ s Dd hD hc) hD hN


end Rho2

end Formalism.MainNotions.N.K.StB

end
end
