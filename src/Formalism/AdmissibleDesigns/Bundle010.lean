module

public import Formalism.AdmissibleDesigns.CohomZeroEquivContinuous
public import Formalism.AdmissibleDesigns.Bundle001
public import Formalism.AdmissibleDesigns.IsDROfWpIso
public import Formalism.AdmissibleDesigns.KernelLengthHigherColumns
public import Formalism.AdmissibleDesigns.MemImageOfTensorSum
public import Formalism.AdmissibleDesigns.RankReductionIdempotentOne
public import Formalism.AdmissibleDesigns.Bundle007
public import Formalism.AdmissibleDesigns.EKSymmCont
public import Formalism.AdmissibleDesigns.Bundle002
public import Formalism.AdmissibleDesigns.Bundle006
public import Formalism.AdmissibleDesigns.FgTopContinuousLinearMap
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
import Mathlib.Tactic.Linter.Style
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
import Formalism.AdmissibleDesigns.PiEquiv2
import Formalism.WachLatticeTwists.SplitClassesAll.Statement

@[expose] public section

section

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core] [hH0Fin : Fact Formalism.MainNotions.N.K.H0.FinCore]

noncomputable section

open Finset Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.K.StA

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.SplitClassesAll Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop cupFG)
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)
open Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K Formalism.RepresentationBoundsCohomology.SF Formalism.MainNotions.N.K.St

attribute [local instance 2000] Topo.fracTopology Topo.rTopology

theorem r_pos (D : D7) : 0 < D.R.r := by
  have h := D.R.m_add_three_le_k
  show 0 < D.R.k + D.R.m - 1
  omega

theorem card_pos (D : D7) : 0 < Fintype.card (Fin D.R.nV) := by
  rw [Fintype.card_fin]
  have h := D.R.m_add_three_le_k
  show 0 < D.R.k + D.R.m - 1 + D.R.t
  omega

theorem jN_eq {D : D7} (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (dc : TruncatedSeriesCountingIdentities.Decl D i) : jN i ρ π dc = KHf.jK i dc ρ π := rfl

theorem leftId_alg {O : Type} [CommRing O] {A : Type} [Ring A] [Algebra O A] (x : A) (c : O) (m : LeftId O x) :
    c • m = (algebraMap O A c) • m := by
  exact Subtype.ext (Algebra.smul_def c m.1)

section Cols

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))

theorem colUz : ∀ l (g : decs D.host.E (Aw i dc) (colIdx i dc l)),
    (((KFin.uz i dc Dd.δO l : decs D.host.E (Aw i dc) (colIdx i dc l) → ↥(Ideal.span {Dd.δO})) g :
      ↥(Ideal.span {Dd.δO})) : D.nd.O i) = Dd.δO * KFin.u i dc l g := by
  intro l g
  first
  | (show Dd.δO * KFin.uCol i dc l g = Dd.δO * KFin.u i dc l g
     rw [KFin.u, dite_eq_left (show ((g : GE D.nd)) ∈ KFin.Γc i dc l from g.2)])
  | (simp [KFin.uz, KFin.uzOf, KFin.u, g.2])

theorem column_unramified_character : (∀ l, ∀ g ∈ QS.I i dc (colIdx i dc l), KFin.u i dc l (g : GE D.nd) = 0) ∧
    (∀ l, ∃ g ∈ (decs D.host.E (Aw i dc)) (colIdx i dc l), KFin.u i dc l g = 1) :=
  ⟨fun l => KFin.u_I i dc l (KUnr.unrHom i dc l), fun l => KFin.u_one i dc l (KUnr.unrHom i dc l)⟩

variable [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]




theorem colLx_of_ringDef
    (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (hBK : TruncatedSeriesCountingIdentities.admBK i) (hG2 : TruncatedSeriesCountingIdentities.admG2 i r ρ π) (hFont : TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i)
    (hDec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π)
    (hCr : ∀ x' l, KDim.CrysX i dc Dd.r Dd.χ x' l) (hNeg : ∀ x' l, KDim.NegX i dc Dd.r Dd.χ ρ π x' l)
    (hFin : ∀ x' l, KDim.FinX i dc Dd.r Dd.χ x' l) (hCrW : ∀ l, KDim.CrysW i dc ρ π l) :
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
  intro x' _ l
  have hO := KOrb.orbC_repE i dc r π g0 eB e₁ s Dd hD hc x' (colIdx i dc l)
  have hdim : KHf.DimLx i dc Dd.r Dd.χ (KHf.jK i dc ρ π) x' l :=
    KDim.dimLx_of_font i dc Dd.r Dd.χ ρ π r x' l (card_pos D) (r_pos D) hBK hG2 hFont
      (KDim.contX_of_orbC i dc Dd.r Dd.χ x' l hO) (hCr x' l) (hNeg x' l) (hFin x' l) (hCrW l)
      (KOrb.contW_rec i dc r ρ π hDec hc l)
  rw [jN_eq]
  exact KHf.exists_Lx i dc Dd.r Dd.χ (leftId_alg Dd.e₁) (leftId_alg Dd.E) (KHf.jK i dc ρ π) x' l hO hdim

end Cols

end Formalism.MainNotions.N.K.StA

end
end

section

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core] [hH0Fin : Fact Formalism.MainNotions.N.K.H0.FinCore]

noncomputable section



open Classical

namespace Formalism.MainNotions.N.K.Font

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.KHf Formalism.MainNotions.N.KDim NumberField IsDedekindDomain Formalism.NG Formalism.BasicNotions

section RhoC

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

theorem rhoCont_of (hc : TruncatedSeriesCountingIdentities.FamilyContinuous i r) (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) :
    Continuous fun g => rhoO D.nd i ρ π g := by
  have h : (fun g => rhoO D.nd i ρ π g) = fun g => (fun a b => rO D.nd i r π g (Fin.castAdd D.R.t a) (Fin.castAdd D.R.t b) :
      Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)) := by
    funext g
    exact Matrix.ext fun a b => (hN.2.2 g a b).symm
  rw [h]
  exact continuous_pi fun a => continuous_pi fun b => (hc π).matrix_elem _ _

end RhoC

section Lat

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (g0 : GE D.nd)
  (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  [TopologicalSpace (FractionRing (D.nd.O i))] [IsTopologicalAddGroup (FractionRing (D.nd.O i))]
  [ContinuousSMul (D.nd.O i) (FractionRing (D.nd.O i))]
  (hK : ContinuousMul (FractionRing (D.nd.O i)))
  (hε : Continuous fun g => ((epsU D.nd i g : (D.nd.O i)ˣ) : D.nd.O i))
  (hM : ∀ a b, Continuous fun g => KLat.M0 Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk g a b)

def phiW (n : ℕ) (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) :
    TrV (eK (D.nbr i _ hn)) (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R) n) ≃ₗ[Br.LL D.nbr i _ hn]
      (Fin D.R.r → Br.LL D.nbr i _ hn) where
  toFun v a := eK (D.nbr i _ hn) ((v : {a // RepresentationBoundsCohomology.blk D.R a = 0} → FractionRing (D.nd.O i)) (H0.e0 a))
  invFun w := (show {a // RepresentationBoundsCohomology.blk D.R a = 0} → FractionRing (D.nd.O i) from
    fun b => (eK (D.nbr i _ hn)).symm (w ((H0.e0 (D := D)).symm b)))
  map_add' u v := funext fun a => map_add (eK (D.nbr i _ hn)) _ _
  map_smul' c v := funext fun a => by
    show eK (D.nbr i _ hn) ((eK (D.nbr i _ hn)).symm c * _) = c * _
    rw [map_mul, RingEquiv.apply_symm_apply]
  left_inv v := by
    funext b
    show (eK (D.nbr i _ hn)).symm (eK (D.nbr i _ hn) (_ : FractionRing (D.nd.O i))) = _
    rw [RingEquiv.symm_apply_apply, Equiv.apply_symm_apply]
  right_inv w := by
    funext a
    show eK (D.nbr i _ hn) ((eK (D.nbr i _ hn)).symm (w ((H0.e0 (D := D)).symm (H0.e0 a)))) = w a
    rw [RingEquiv.apply_symm_apply, Equiv.symm_apply_apply]

theorem wpIso_dat (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0
      eB e₁ s Dd) (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π)
    (n : ℕ) (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) :
    WpIso i dc ρ π n hn (KLat.Dat Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (K.Aw i dc) hK hε hM n).ρT := by
  refine ⟨phiW i dc n hn, fun g x => funext fun a => ?_⟩
  show eK (D.nbr i _ hn) ((KLat.matK (Dd.ρk 0 (uElt Dd.r Dd.χ ((Br.iota D.nbr i _ hn g : _) : GE D.nd)))).mulVec
      (x : {a // RepresentationBoundsCohomology.blk D.R a = 0} → FractionRing (D.nd.O i)) (H0.e0 a)) =
    ∑ b, Br.loc D.nbr i _ hn (WpO D.nd i ρ π) g a b * eK (D.nbr i _ hn) ((x : {a // RepresentationBoundsCohomology.blk D.R a = 0} → FractionRing (D.nd.O i)) (H0.e0 b))
  refine (congrArg (eK (D.nbr i _ hn)) (KLat.matK_mulVec (Dd.ρk 0 (uElt Dd.r Dd.χ ((Br.iota D.nbr i _ hn g : _) : GE D.nd)))
    (show {a // RepresentationBoundsCohomology.blk D.R a = 0} → FractionRing (D.nd.O i) from x) (H0.e0 a))).trans ?_

  rw [map_sum]
  refine (Equiv.sum_comp (H0.e0 (D := D)) _).symm.trans (Finset.sum_congr rfl fun b _ => ?_)
  rw [Algebra.smul_def, map_mul, loc_apply, H0.unipotent_block_zero_entry hD hN]

end Lat

section RowDR2

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (g0 : GE D.nd)
  (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  [TopologicalSpace (FractionRing (D.nd.O i))] [IsTopologicalAddGroup (FractionRing (D.nd.O i))]
  [ContinuousSMul (D.nd.O i) (FractionRing (D.nd.O i))]
  (hK : ContinuousMul (FractionRing (D.nd.O i)))
  (hε : Continuous fun g => ((epsU D.nd i g : (D.nd.O i)ˣ) : D.nd.O i))
  (hM : ∀ a b, Continuous fun g => KLat.M0 Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk g a b)

theorem isDR_dat (hF : TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i) (hG2 : TruncatedSeriesCountingIdentities.admG2 i r ρ π) (hDec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π)
    (hCont : TruncatedSeriesCountingIdentities.FamilyContinuous i r)
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0
      eB e₁ s Dd) (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π)
    (n : ℕ) (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) :
    IsDR (Br.PD D.loc D.nbr i _ hn) (repL (eK (D.nbr i _ hn))
      (KLat.Dat Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (K.Aw i dc) hK hε hM n).ρT (Br.iota D.nbr i _ hn)) :=
  isDR_of_wpIso i dc r ρ π hF hG2 hDec hCont (rhoCont_of i r ρ π hCont hN) n hn _ (wpIso_dat i dc r ρ π g0 eB e₁ s Dd hK hε hM hD hN n hn)

end RowDR2

end Formalism.MainNotions.N.K.Font

end
end
