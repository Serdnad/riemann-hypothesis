module

public import Formalism.AdmissibleDesigns.LiftMapEquivariant
public import Formalism.AdmissibleDesigns.Bundle005
public import Formalism.AdmissibleDesigns.LengthSemilinear
public import Formalism.AdmissibleDesigns.MemIntegralSpanIffImage
public import Formalism.AdmissibleDesigns.KernelLengthHigherColumns
public import Formalism.AdmissibleDesigns.TwistedTargetOfInputs
public import Formalism.AdmissibleDesigns.FiniteClassesLocalEq
public import Formalism.AdmissibleDesigns.Bundle007
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
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
import Mathlib.Tactic.Linter.HaveILetI
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

@[expose] public section

section

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core] [hH0Fin : Fact Formalism.MainNotions.N.K.H0.FinCore]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.Sel

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K Formalism.NG Formalism.BasicNotions
  Formalism.RepresentationBoundsCohomology.FIN Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology

section Phi

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

theorem toKOG_surjective : Function.Surjective (H0.toKOG (D := D) i Dd) := by
  intro y
  refine ⟨fun b => (H0.kogEq _ y) (H0.e0.symm b), ?_⟩
  show (H0.kogEq _).symm (fun a => (H0.kogEq _ y) (H0.e0.symm (H0.e0 a))) = y
  simp only [Equiv.symm_apply_apply]
  exact (H0.kogEq _).symm_apply_apply y

def phi0 : blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0 ≃ₗ[D.nd.O i] KOG (D.nd.O i) D.R.r :=
  LinearEquiv.ofBijective (H0.toKOG i Dd) ⟨H0.toKOG_injective i Dd, toKOG_surjective i Dd⟩


variable {i r ρ π g0 eB e₁ s Dd} in
theorem invariants_map_equivariant
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (g : GE D.nd) (m : blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) :
    phi0 i Dd (uRep (D.nd.O i) (M := blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) Dd.r Dd.χ g m) = Br.WKO i ρ π g (phi0 i Dd m) := by
  exact H0.toKOG_equiv hD hN g m


variable {i r ρ π g0 eB e₁ s Dd} in
theorem tieSel1_rec
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π)
    (F : ∀ w, Submodule (D.nd.O i) (H1z (resRep (uRep (D.nd.O i) (M := blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) Dd.r Dd.χ)
      (decs D.host.E (Aw i dc) w))))
    (hBk : BkAt i dc ρ π (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) Dd.r Dd.χ (phi0 i Dd) (invariants_map_equivariant hD hN) F) :
    TieSel1 i ρ π (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) Dd.r Dd.χ (colIdx i dc) (decs D.host.E (Aw i dc)) (rowsN i dc) F
      (K.QS.Io i) := by
  exact tieSel1_of (hBk := hBk)


variable {i r ρ π g0 eB e₁ s Dd} in
theorem tieSel1_rec_loc
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π)
    (F : ∀ w, Submodule (D.nd.O i) (H1z (resRep (uRep (D.nd.O i) (M := blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) Dd.r Dd.χ)
      (decs D.host.E (Aw i dc) w))))
    (hBk : BkLoc i dc ρ π (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) Dd.r Dd.χ (phi0 i Dd) (invariants_map_equivariant hD hN) F) :
    TieSel1 i ρ π (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) Dd.r Dd.χ (colIdx i dc) (decs D.host.E (Aw i dc)) (rowsN i dc) F
      (K.QS.Io i) := by
  exact tieSel1_rec (hD := hD) (hN := hN) (F := F) (hBk := bkAt_of_loc (h := hBk))

end Phi

end Formalism.MainNotions.N.K.Sel

end
end

section

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.KRow

open Formalism.MainNotions.N.KHf Formalism.WeaklyAdmissibleFiltrations Module Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.BasicNotions Formalism.RepresentationBoundsCohomology.FIN Formalism.NG Formalism.BasicNotions.Loc

section Rec

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  [TopologicalSpace (FractionRing (D.nd.O i))] [IsTopologicalAddGroup (FractionRing (D.nd.O i))]
  [ContinuousSMul (D.nd.O i) (FractionRing (D.nd.O i))] [IsDiscreteValuationRing (D.nd.O i)]
  (VT VT' : ℕ → Type)
  [∀ w, AddCommGroup (VT w)] [∀ w, Module (D.nd.O i) (VT w)] [∀ w, TopologicalSpace (VT w)]
  [∀ w, IsTopologicalAddGroup (VT w)] [∀ w, ContinuousSMul (D.nd.O i) (VT w)]
  [∀ w, Module (FractionRing (D.nd.O i)) (VT w)] [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (VT w)]
  [∀ w, AddCommGroup (VT' w)] [∀ w, Module (D.nd.O i) (VT' w)] [∀ w, TopologicalSpace (VT' w)]
  [∀ w, IsTopologicalAddGroup (VT' w)] [∀ w, ContinuousSMul (D.nd.O i) (VT' w)]
  [∀ w, Module (FractionRing (D.nd.O i)) (VT' w)] [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (VT' w)]
  (Dat : ∀ w, Formalism.RepresentationBoundsCohomology.LOC.LatData (D.nd.O i) ↥(Γn i dc w) (VT w) (VT' w))
  {T₁ T₂ : Type} [AddCommGroup T₁] [Module (D.nd.O i) T₁] [TopologicalSpace T₁] [IsTopologicalAddGroup T₁]
  [ContinuousConstSMul (D.nd.O i) T₁] [AddCommGroup T₂] [Module (D.nd.O i) T₂]
  (ρ₁ : Representation (D.nd.O i) (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) T₁) (π : T₁ →ₗ[D.nd.O i] T₂)
  (vD : ∀ w, T₂ ≃ₗ[D.nd.O i] (Dat w).T') (hpD : ∀ w, Continuous fun t => vD w (π t))
  (heD : ∀ w g t, vD w (π (resRep ρ₁ (Γn i dc w) g t)) = (Dat w).ρTl' g (vD w (π t)))
  [∀ w, Module (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT')]
  [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT')]

theorem len_congr {O H : Type} [CommRing O] [AddCommGroup H] [Module O H] {A A' B B' : Submodule O H}
    (hA : A = A') (hB : B = B') :
    Module.length O (↥A ⧸ B.comap A.subtype) = Module.length O (↥A' ⧸ B'.comap A'.subtype) := by
  subst hA hB
  rfl

theorem fs_eq {n : ℕ} (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) :
    Fs i dc VT VT' Dat n = FsG (Γ := ↥(Γn i dc n)) (eK (D.nbr i _ hn)) (Br.PD D.loc D.nbr i _ hn) (Br.iota D.nbr i _ hn) (Dat n) := by
  have key : fZ i dc n (Dat n).ρT' = finZ (eK (D.nbr i _ hn)) (Br.PD D.loc D.nbr i _ hn) (Dat n).ρT' (Br.iota D.nbr i _ hn) := by
    unfold fZ
    rw [dite_eq_left hn]
  unfold Fs FsG Hf₂ finiteClassesContinuousMap fPre finiteClassesContinuous finPre
  rw [key]

theorem finite_classes_row_eq_generic {n : ℕ} (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) :
    Hf₁ i dc ρ₁ n = finiteClassesContinuousLattice (eK (D.nbr i _ hn)) (Br.PD D.loc D.nbr i _ hn) (Br.iota D.nbr i _ hn)
      (resRep ρ₁ (Γn i dc n)) := by
  have key : fZ i dc n (locRep (resRep ρ₁ (Γn i dc n))) = finZ (eK (D.nbr i _ hn)) (Br.PD D.loc D.nbr i _ hn) (locRep (resRep ρ₁ (Γn i dc n))) (Br.iota D.nbr i _ hn) := by
    unfold fZ
    rw [dite_eq_left hn]
  unfold Hf₁ finiteClassesContinuousLocal finiteClassesContinuousLattice finiteClassesContinuousMap fPre finiteClassesContinuous finPre
  rw [key]
  rfl

variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (πx : D.nd.X i)



theorem rowLenD_eq_gen {n : ℕ} (hw : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) :
    rowLenD i dc VT VT' Dat ρ₁ π vD hpD heD n =
      Module.length (D.nd.O i)
        (↥(FsG (Γ := ↥(Γn i dc n)) (eK (D.nbr i _ hw)) (Br.PD D.loc D.nbr i _ hw) (Br.iota D.nbr i _ hw) (Dat n)) ⧸
          (imG (Γ := ↥(Γn i dc n)) (eK (D.nbr i _ hw)) (Br.PD D.loc D.nbr i _ hw) (Br.iota D.nbr i _ hw) (Dat n)
            (resRep ρ₁ (Γn i dc n)) π (vD n) (hpD n) (heD n)).comap
            (FsG (Γ := ↥(Γn i dc n)) (eK (D.nbr i _ hw)) (Br.PD D.loc D.nbr i _ hw) (Br.iota D.nbr i _ hw)
              (Dat n)).subtype) := by
  unfold rowLenD
  exact len_congr (fs_eq i dc VT VT' Dat hw) (by unfold imRow; rw [finite_classes_row_eq_generic i dc ρ₁ hw]; rfl)



theorem rowLenD_eq {n : ℕ} (hw : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i))
    [Module.Finite (D.nd.O i) T₁] [Module.Free (D.nd.O i) T₁]
    [Module.Finite (D.nd.O i) (Dat n).T'] [Module.Free (D.nd.O i) (Dat n).T']
    (hsp : ∀ x : VT' n, ∃ c : D.nd.O i, c ≠ 0 ∧ ∃ m : (Dat n).T', (Dat n).T'.subtype m = c • x)
    (hcob : OrbC i dc (n := n) (Dat n).ρT')
    (htopV : ∀ c : ↥(Γn i dc n) → VT' n,
      Continuous (fun g => tr (eK (D.nbr i _ hw)) (c (Br.iota D.nbr i _ hw g))) → Continuous c)
    (htop1 : ∀ c : ↥(Γn i dc n) → T₁,
      Continuous (fun g => tr (eK (D.nbr i _ hw)) (mkK (O := D.nd.O i) (c (Br.iota D.nbr i _ hw g)))) →
        Continuous c) :
    rowLenD i dc VT VT' Dat ρ₁ π vD hpD heD n =
      (FR (Γ := ↥(Γn i dc n)) (eK (D.nbr i _ hw)) (D.nbr i _ hw).eO (heO_br i dc hw) (Br.iota D.nbr i _ hw) (Dat n)
        (resRep ρ₁ (Γn i dc n)) π (vD n) (heD n) hsp).col (Br.PD D.loc D.nbr i _ hw) := by
  have hbij : Function.Bijective (Br.iota D.nbr i _ hw) := (D.nbr i _ hw).e.symm.bijective
  have hcobn : ∀ x : VT' n, (fun γ => (Dat n).ρT' γ x - x) ∈
      finZ (eK (D.nbr i _ hw)) (Br.PD D.loc D.nbr i _ hw) (Dat n).ρT' (Br.iota D.nbr i _ hw) := by
    intro x
    have h := cob_mem_fZ i dc (Dat n).ρT' hcob x
    rwa [fZ_pos i dc _ hw] at h
  exact (rowLenD_eq_gen i dc VT VT' Dat ρ₁ π vD hpD heD hw).trans
    (len_eq_col (Γ := ↥(Γn i dc n)) (eK (D.nbr i _ hw)) (D.nbr i _ hw).eO (heO_br i dc hw)
      (Br.PD D.loc D.nbr i _ hw) (Br.iota D.nbr i _ hw) (Dat n) (resRep ρ₁ (Γn i dc n)) π (vD n) (hpD n) (heD n) hsp
      hbij hcobn htopV htop1)



theorem rowTie_disp (hπ : Function.Surjective π)
    (hSub : RowSub (ρ₁ := ρ₁) i dc r) (hOrb : RowOrb (ρ₁ := ρ₁) i dc)
    (hMat : RowMat i dc VT VT' Dat ρ πx) (hTop : RowTop i dc VT' (T₁ := T₁))
    (hFin : RowFin i dc VT VT' Dat (T₁ := T₁))
    (hcob : ∀ n ∈ K.rowsN i dc, OrbC i dc (n := n) (Dat n).ρT') :
    K.Sel.RowTie i dc r ρ πx (rowLenD i dc VT VT' Dat ρ₁ π vD hpD heD) := by
  intro n hn hw b hR
  obtain ⟨hF1, hF2, hFn⟩ := hFin
  obtain ⟨hF3, hF4, hsp⟩ := hFn n hn
  haveI := hF1
  haveI := hF2
  haveI := hF3
  haveI := hF4
  have hev : Function.Surjective ((vD n).toLinearMap ∘ₗ π) := (vD n).surjective.comp hπ
  have hrow := rowLenD_eq i dc VT VT' Dat ρ₁ π vD hpD heD hw hsp (hcob n hn) (hTop n hn hw).1 (hTop n hn hw).2
  have hR' : RowAt (Br.PD D.loc D.nbr i _ hw) (LL := Br.LLw (D.nbr i _ hw)) (O := Br.Ow (D.nbr i _ hw))
      (fun x : D.nd.X i => ⇑(TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i _ hw) (rDuO D.nd i r x)))
      ⇑(TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i _ hw) (T2O D.nd i ρ πx)) b := hR
  have hL1 := finDim_of_lat (Ow := Br.Ow (D.nbr i _ hw)) (Qp := ℚ_[D.nd.l i])
    (L1 (Γ := ↥(Γn i dc n)) (eK (D.nbr i _ hw)) (D.nbr i _ hw).eO (heO_br i dc hw) (Br.iota D.nbr i _ hw)
      (resRep ρ₁ (Γn i dc n)))
  have hL2 := finDim_of_lat (Ow := Br.Ow (D.nbr i _ hw)) (Qp := ℚ_[D.nd.l i])
    (L2 (Γ := ↥(Γn i dc n)) (eK (D.nbr i _ hw)) (D.nbr i _ hw).eO (heO_br i dc hw) (Br.iota D.nbr i _ hw) (Dat n) hsp)
  have hons : Function.Surjective (trL (eK (D.nbr i _ hw)) (f0 (Dat n) π (vD n))) :=
    trL_onto (hspQ := hsp) (hcomm := fun m => lift_map_mk (Dat n) π (vD n) m) hev
  have hc1 := hOrb n hn hw
  have hc2 : ∀ y, Continuous fun g => repL (eK (D.nbr i _ hw)) (Dat n).ρT' (Br.iota D.nbr i _ hw) g y := by
    intro y
    obtain ⟨x, rfl⟩ := hons y
    have h : (fun g => repL (eK (D.nbr i _ hw)) (Dat n).ρT' (Br.iota D.nbr i _ hw) g
        (trL (eK (D.nbr i _ hw)) (f0 (Dat n) π (vD n)) x)) =
        fun g => trL (eK (D.nbr i _ hw)) (f0 (Dat n) π (vD n))
          (repL (eK (D.nbr i _ hw)) (locRep (resRep ρ₁ (Γn i dc n))) (Br.iota D.nbr i _ hw) g x) :=
      funext fun g => (lift_map_equivariant (Dat n) (resRep ρ₁ (Γn i dc n)) π (vD n) (heD n) (Br.iota D.nbr i _ hw g) x).symm
    rw [h]
    exact (trL_cont (eK (D.nbr i _ hw)) _).comp (hc1 x)
  have hOnto := latHom_onto (ρP := resRep ρ₁ (Γn i dc n)) (ρQ := (Dat n).ρTl') (Br.iota D.nbr i _ hw) (heO_br i dc hw) mkK_inj Subtype.val_injective
    (fun γ m => (locRep_mkK (resRep ρ₁ (Γn i dc n)) γ m).symm) (fun _ _ => rfl) mkK_span hsp
    (lift_map_equivariant (Dat n) (resRep ρ₁ (Γn i dc n)) π (vD n) (heD n)) (fun m => lift_map_mk (Dat n) π (vD n) m) hev
  obtain ⟨m, k, hm, hk, hmk⟩ := hR' (TrV (eK (D.nbr i _ hw)) (VT' n))
    (repL (eK (D.nbr i _ hw)) (Dat n).ρT' (Br.iota D.nbr i _ hw))
    (L2 (Γ := ↥(Γn i dc n)) (eK (D.nbr i _ hw)) (D.nbr i _ hw).eO (heO_br i dc hw) (Br.iota D.nbr i _ hw) (Dat n) hsp)
    hc2 (hMat n hn hw) (TrV (eK (D.nbr i _ hw)) (MK (O := D.nd.O i) T₁))
    (repL (eK (D.nbr i _ hw)) (locRep (resRep ρ₁ (Γn i dc n))) (Br.iota D.nbr i _ hw))
    (L1 (Γ := ↥(Γn i dc n)) (eK (D.nbr i _ hw)) (D.nbr i _ hw).eO (heO_br i dc hw) (Br.iota D.nbr i _ hw)
      (resRep ρ₁ (Γn i dc n)))
    hc1 (hSub n hn hw)
    (FR (Γ := ↥(Γn i dc n)) (eK (D.nbr i _ hw)) (D.nbr i _ hw).eO (heO_br i dc hw) (Br.iota D.nbr i _ hw) (Dat n)
      (resRep ρ₁ (Γn i dc n)) π (vD n) (heD n) hsp) hOnto
  have hm' : rowLenD i dc VT VT' Dat ρ₁ π vD hpD heD n = m := hrow.trans hm
  have hk' : lenOl (Br.PD D.loc D.nbr i (K.plOf i dc n) hw)
      (O := ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i (K.plOf i dc n) hw).LL)) = k := hk
  refine ⟨by rw [hm']; exact ENat.coe_ne_top m, ?_⟩
  rw [hm', hk']
  simp only [ENat.toNat_coe]
  exact hmk


end Rec

end Formalism.MainNotions.N.KRow

end
end

section

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core] [hH0Fin : Fact Formalism.MainNotions.N.K.H0.FinCore]

noncomputable section

open Classical Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.NG

namespace Formalism.MainNotions.N.KTate

open Formalism.MainNotions.N.KHf

section RecIso2

open Formalism.MainNotions Formalism.MainNotions.N Formalism.RepresentationBoundsCohomology.SF NumberField IsDedekindDomain
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData)

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)



theorem isoV_of (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (g0 : GE D.nd)
    (eB e₁ s : D.nd.X i → MatN D.nd i)
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (l : K.Col i dc) : IsoV i dc Dd ρ π l := by
  have hn := KDim.col_over i dc l
  let F : TrV (eK (D.nbr i _ hn)) (KFin.Vr i Dd) ≃ₗ[Br.LL D.nbr i _ hn] (Fin D.R.r → Br.LL D.nbr i _ hn) :=
    { toFun := fun v a => eK (D.nbr i _ hn) ((show KFin.Vr i Dd from v) (K.H0.e0 (D := D) a))
      invFun := fun w => (show KFin.Vr i Dd from fun j => (eK (D.nbr i _ hn)).symm (w ((K.H0.e0 (D := D)).symm j)))
      map_add' := fun u v => funext fun a => map_add (eK (D.nbr i _ hn)) _ _
      map_smul' := fun c v => funext fun a => by
        show eK (D.nbr i _ hn) ((eK (D.nbr i _ hn)).symm c * (show KFin.Vr i Dd from v) (K.H0.e0 (D := D) a)) =
          c * eK (D.nbr i _ hn) ((show KFin.Vr i Dd from v) (K.H0.e0 (D := D) a))
        rw [map_mul, RingEquiv.apply_symm_apply]
      left_inv := fun v => funext fun j => by
        show (eK (D.nbr i _ hn)).symm (eK (D.nbr i _ hn)
          ((show KFin.Vr i Dd from v) (K.H0.e0 (D := D) ((K.H0.e0 (D := D)).symm j)))) = (show KFin.Vr i Dd from v) j
        rw [RingEquiv.symm_apply_apply, Equiv.apply_symm_apply]
      right_inv := fun w => funext fun a => by
        show eK (D.nbr i _ hn) ((eK (D.nbr i _ hn)).symm (w ((K.H0.e0 (D := D)).symm (K.H0.e0 (D := D) a)))) = w a
        rw [RingEquiv.apply_symm_apply, Equiv.symm_apply_apply] }
  refine ⟨F, fun g v => funext fun a => ?_⟩
  have h1 : F (repL (eK (D.nbr i _ hn)) (KFin.ρV i dc Dd l) (Br.iota D.nbr i _ hn) g v) a =
      eK (D.nbr i _ hn) (∑ j, Dd.ρk 0 (uElt Dd.r Dd.χ ((Br.iota D.nbr i _ hn g : KHf.Γn i dc (K.colIdx i dc l)) : GE D.nd))
        (K.H0.e0 (D := D) a) j • (show KFin.Vr i Dd from v) j) := rfl
  have h2 : KDim.repW i dc ρ π (K.colIdx i dc l) hn g (F v) a =
      ∑ b, algebraMap (Br.OLL D.nbr i _ hn) (Br.LL D.nbr i _ hn) ((D.nbr i _ hn).eO
        (WpO D.nd i ρ π ((Br.iota D.nbr i _ hn g : KHf.Γn i dc (K.colIdx i dc l)) : GE D.nd) a b)) * F v b := rfl

  rw [h1, h2, map_sum, ← Equiv.sum_comp (K.H0.e0 (D := D))]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Algebra.smul_def, map_mul, KHf.eK_apply, Br.toLLK_alg, K.H0.unipotent_block_zero_entry hD hN _ a b]
  rfl

theorem rankFf_normAt (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (g0 : GE D.nd)
    (eB e₁ s : D.nd.X i → MatN D.nd i)
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (l : K.Col i dc) : KFin.RankFf i dc Dd ρ π l := by
  apply rankFf_iso (hD := hD) (hc := hc)
  exact isoV_of i dc Dd ρ π r g0 eB e₁ s hD hN l

end RecIso2

end Formalism.MainNotions.N.KTate
end
end

section

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.StC

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.WeaklyAdmissibleFiltrations Formalism.NG Formalism.RepresentationBoundsCohomology.BR
open Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N.K.TB Formalism.MainNotions.N.KHf Formalism.MainNotions.N.K.TBa Formalism.MainNotions.N.KLift

section EmbRow

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (Formalism.MainNotions.N.RepresentationBoundsCohomology.blk D.R))

theorem msW_apply {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) (x : D.nd.X i)
    (g : Br.G D.nbr i w hw) (a b : Fin D.R.nV) :
    MsW i r hw x g a b = eS i hw (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))
      (rTwO D.nd i r x ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd) a b)) := by
  rw [msW_entry]
  first
  | rfl
  | simp [Matrix.map_apply]


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem embRW_of {T : Subalgebra (D.nd.O i) (D.nd.X i → D.nd.O i)} {π : D.nd.X i} {ε : GE D.nd →* (D.nd.O i)ˣ}
    {g0 : GE D.nd} {eB e₁ s : D.nd.X i → Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)}
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) T (Formalism.MainNotions.N.RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) ε g0 eB e₁ s Dd)
    [Module.Finite (D.nd.O i) Dd.R']
    {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) : EmbRW i dc r Dd hw := by
  obtain ⟨hr', hsm, hχ⟩ := ringDef_lift i r Dd hD
  have := nzsd_R' i Dd
  have : Module.Free (D.nd.O i) Dd.R' := Module.free_of_finite_type_torsion_free'
  set ρP := resRep (lRep (D.nd.O i) Dd.r Dd.χ) (Dw i dc (idx i dc w)) with hρP
  set e := eS i hw
  let κ : Dd.R' →ₗ[D.nd.O i] (Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) :=
    (Dd.R').val.toLinearMap
  have hκ : Function.Injective κ := Subtype.val_injective
  let Λ := liftK (V := Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) κ
  have hΛs : ∀ m (s : nonZeroDivisors (D.nd.O i)), (s : D.nd.O i) • Λ (LocalizedModule.mk m s) = κ m := by
    intro m s
    rw [← map_smul, smul_mk, liftK_mkK]
  have hΛi : ∀ v, Λ v = 0 → v = 0 := by
    intro v hv
    induction v using LocalizedModule.induction_on with
    | h m s =>
      have h1 := hΛs m s
      rw [hv, smul_zero] at h1
      rw [hκ (h1.symm.trans (map_zero κ).symm), LocalizedModule.zero_mk]
  have hΛe : ∀ (γ : ↥(Dw i dc (idx i dc w))) v, Λ (locRep ρP γ v) =
      ((Formalism.NG.uElt Dd.r Dd.χ (γ : GE D.nd) : Dd.R') :
        Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) * Λ v := by
    intro γ v
    induction v using LocalizedModule.induction_on with
    | h m s =>
      have h0 : locRep ρP γ (LocalizedModule.mk m s) = LocalizedModule.mk (ρP γ m) s := LocalizedModule.map_mk _ _ _ _
      rw [h0]
      apply smul_cancel s
      rw [hΛs, ← mul_smul_comm, hΛs]
      rfl
  let Ψ : Dd.X' × Fin D.R.nV → TrV e (MK (O := D.nd.O i) Dd.R') →ₗ[↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1]
      (Fin D.R.nV → ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1) := fun q =>
    { toFun := fun v a => e ((Λ (untr e v)) q.1 a q.2)
      map_add' := fun v v₂ => funext fun a => by
        show e ((Λ (untr e v + untr e v₂)) q.1 a q.2) = _
        rw [map_add (f := _)]
        simp [map_add (f := _)]
      map_smul' := fun c v => funext fun a => by
        show e ((Λ (e.symm c • untr e v)) q.1 a q.2) = c * e ((Λ (untr e v)) q.1 a q.2)
        rw [smulK]
        simp [Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, map_mul] }
  haveI : FiniteDimensional (↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1) (TrV e (MK (O := D.nd.O i) Dd.R')) :=
    finDim_of_lat (Ow := ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL)) (Qp := ℚ_[D.nd.l i])
      (latOf e (selfO i hw) mkK (eW i dc hw).symm.toMonoidHom (heS i hw) (locRep ρP) ρP mkK_inj
        (fun γ m => (locRep_mkK _ γ m).symm) mkK_span)
  have hinj : ∀ v, (∀ q, Ψ q v = 0) → v = 0 := by
    intro v hv
    have h0 : Λ (untr e v) = 0 := by
      funext x'
      ext a b
      have := congrFun (hv (x', b)) a
      simpa [Ψ] using this
    exact hΛi _ h0
  obtain ⟨m, xs, hxs⟩ := fin_sel Ψ hinj
  refine ⟨m, fun a => Dd.p (xs a).1, LinearMap.pi fun a => Ψ (xs a), fun v v' hvv => ?_, fun g v => funext fun a => ?_⟩
  · rw [← sub_eq_zero]
    refine hxs _ fun a => ?_
    rw [map_sub, sub_eq_zero]
    exact congrFun hvv a
  · have key : ∀ (q : Dd.X' × Fin D.R.nV) (γ : ↥(Dw i dc (idx i dc w))),
        (γ : GE D.nd) = ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd) → ∀ b,
        e ((Λ (locRep ρP γ (untr e v))) q.1 b q.2) = (MsW i r hw (Dd.p q.1) g).mulVec (Ψ q v) b := by
      intro q γ hγ b
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hΛe, Pi.mul_apply, hγ, uElt_at i r Dd hr' hsm hχ, Matrix.mul_apply, map_sum]
      simp only [Matrix.mulVec, dotProduct, msW_apply]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp [Ψ, Matrix.map_apply, map_mul]
      exact Or.inl rfl
    funext b
    exact key (xs a) ((eW i dc hw).symm g) rfl b

end EmbRow

end Formalism.MainNotions.N.K.StC

end
end
