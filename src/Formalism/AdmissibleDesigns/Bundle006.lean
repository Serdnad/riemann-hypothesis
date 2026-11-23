module

public import Formalism.AdmissibleDesigns.LengthSemilinear
public import Formalism.AdmissibleDesigns.FiniteClassesContinuousLattice
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle010
public import Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.Bundle001
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle003
import Formalism.WeaklyAdmissibleFiltrations.CrystallineStableLifts.Bundle002
public import Formalism.AdmissibleDesigns.MemImageOfTensorSum
public import Formalism.AdmissibleDesigns.RealDisplayAllK
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle011
public import Formalism.WachLatticeTwists.RamifiedBlockRings.DistinctEigenvalueCornerPerturbation
import Formalism.AdmissibleDesigns.CoboundaryMemFiniteClasses
public import Formalism.AdmissibleDesigns.ExistsWildInertiaCyclotomicGenerator
public import Formalism.AdmissibleDesigns.FiniteClassesLocalEq
public import Formalism.AdmissibleDesigns.Bundle002
public import Formalism.SharpRestriction.LevelLetterCocycles.EndomorphismIndexBound
public import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.CompositeOfChainHolds
import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.Bundle005
public import Formalism.WachLatticeTwists.RealDisplaySplitting.RealDisplayProofs.IdempotentRankOneAtPoint
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
import Mathlib.Tactic.Lemma
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

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

set_option linter.style.haveILetI false

open Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.KRowA

open Formalism.MainNotions.N.KHf Module Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.RepresentationBoundsCohomology.FIN Formalism.NG Formalism.RepresentationBoundsCohomology.BR
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)

section Gen

theorem sub_of_fam {LL : Type} [Field LL] {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module LL V]
    [FiniteDimensional LL V] {ρ : Representation LL G V} {ιx : Type} {k : ℕ}
    {Ms : ιx → G → Matrix (Fin k) (Fin k) LL} {I : Type} (xx : I → ιx)
    (Ψ : I → V →ₗ[LL] (Fin k → LL)) (hinj : ∀ v, (∀ a, Ψ a v = 0) → v = 0)
    (heq : ∀ a g v, Ψ a (ρ g v) = (Ms (xx a) g).mulVec (Ψ a v)) : IsSubOfSums ρ Ms := by
  obtain ⟨m, xs, hxs⟩ := KLift.fin_sel Ψ hinj
  refine ⟨m, xx ∘ xs, LinearMap.pi fun a => Ψ (xs a), fun v w hvw => ?_, fun g v => funext fun a => heq _ g v⟩
  rw [← sub_eq_zero]
  refine hxs _ fun a => ?_
  rw [map_sub, sub_eq_zero]
  exact congrFun hvw a

theorem orb_of_sub {LL : Type} [Field LL] [TopologicalSpace LL] [IsTopologicalRing LL] {G : Type} [Group G]
    [TopologicalSpace G] {V : Type} [AddCommGroup V] [Module LL V] [TopologicalSpace V] [IsModuleTopology LL V]
    [ContinuousAdd V] [ContinuousSMul LL V]
    {ρ : Representation LL G V} {ιx : Type} {k : ℕ} {Ms : ιx → G → Matrix (Fin k) (Fin k) LL}
    (h : IsSubOfSums ρ Ms) (hMs : ∀ x, Continuous (Ms x)) (v : V) : Continuous fun g => ρ g v := by
  obtain ⟨m, xs, φ, hφ, heq⟩ := h
  exact KLift.cont_of_inj xs φ hφ heq hMs v

end Gen

section Fin

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X' d : Type} [Fintype d] [DecidableEq d]
  {R' : Subalgebra O (X' → Matrix d d (FractionRing O))}

end Fin

section Rec

attribute [local instance 2000] K.Topo.fracTopology K.Topo.rTopology

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))

def kap1 : FirstSummandSubmodule (D.nd.O i) Dd.e₁ →ₗ[D.nd.O i]
    (Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) where
  toFun p := (((p : Dd.R')) : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem lattice_inclusion_injective : Function.Injective (kap1 i Dd) := by
  intro a b h
  exact Subtype.ext (Subtype.ext h)

theorem idempotent_part_representation_at
    (hr' : ∀ g x', ((Dd.r g : Dd.R') : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) x' =
      (rO D.nd i r (Dd.p x') g).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))))
    (hsm : ∀ (f : Dd.T') (a : Dd.R') x', ((f • a : Dd.R') : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV)
      (FractionRing (D.nd.O i))) x' = algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) ((f : Dd.X' → D.nd.O i) x') •
        (a : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) x')
    (hχ : ∀ g x', (((Dd.χ g : (Dd.T')ˣ) : Dd.T') : Dd.X' → D.nd.O i) x' = (chiU D.nd i 1 g : D.nd.O i))
    (g : GE D.nd) (p : FirstSummandSubmodule (D.nd.O i) Dd.e₁) (x' : Dd.X') :
    kap1 i Dd (firstSummandRep (D.nd.O i) Dd.r Dd.χ Dd.e₁ (epsU D.nd i) g p) x' =
      algebraMap (D.nd.O i) (FractionRing (D.nd.O i))
          ((chiU D.nd i 1 g : D.nd.O i) * ((epsU D.nd i g : (D.nd.O i)ˣ) : D.nd.O i)) •
        (kap1 i Dd p x' * (rO D.nd i r (Dd.p x') g⁻¹).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))) := by
  show (((((epsU D.nd i g : (D.nd.O i)ˣ) : D.nd.O i) • (((Dd.χ g : (Dd.T')ˣ) : Dd.T') •
    ((p : Dd.R') * Dd.r g⁻¹)) : Dd.R')) : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) x' = _
  rw [Subalgebra.coe_smul, Pi.smul_apply, hsm, hχ, Subalgebra.coe_mul, Pi.mul_apply, hr', map_mul, mul_smul,
    ← algebraMap_smul (FractionRing (D.nd.O i)) ((epsU D.nd i g : (D.nd.O i)ˣ) : D.nd.O i), smul_comm]
  rfl

theorem locC_apply {n : ℕ} (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) {k : ℕ}
    (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i _ hn) (a b : Fin k) :
    TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i _ hn) M g a b = eK (D.nbr i _ hn) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))
      (M ((Br.iota D.nbr i _ hn g : Gw D.nd (K.plOf i dc n)) : GE D.nd) a b)) := by
  rw [← KLift.heO_br i dc hn]
  rfl


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem rowSub_at
    (hr' : ∀ g x', ((Dd.r g : Dd.R') : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) x' =
      (rO D.nd i r (Dd.p x') g).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))))
    (hsm : ∀ (f : Dd.T') (a : Dd.R') x', ((f • a : Dd.R') : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV)
      (FractionRing (D.nd.O i))) x' = algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) ((f : Dd.X' → D.nd.O i) x') •
        (a : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) x')
    (hχ : ∀ g x', (((Dd.χ g : (Dd.T')ˣ) : Dd.T') : Dd.X' → D.nd.O i) x' = (chiU D.nd i 1 g : D.nd.O i))
    [Module.Finite (D.nd.O i) (FirstSummandSubmodule (D.nd.O i) Dd.e₁)] [Module.Free (D.nd.O i) (FirstSummandSubmodule (D.nd.O i) Dd.e₁)]
    {n : ℕ} (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) :
    IsSubOfSums (repL (eK (D.nbr i _ hn))
        (locRep (resRep (firstSummandRep (D.nd.O i) Dd.r Dd.χ Dd.e₁ (epsU D.nd i)) (Γn i dc n))) (Br.iota D.nbr i _ hn))
      (fun x : D.nd.X i => ⇑(TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i _ hn) (rDuO D.nd i r x))) := by
  set ρP := resRep (firstSummandRep (D.nd.O i) Dd.r Dd.χ Dd.e₁ (epsU D.nd i)) (Γn i dc n) with hρP
  set e := eK (D.nbr i _ hn)
  let Λ := liftK (V := Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) (kap1 i Dd)
  have hΛs : ∀ m (s : nonZeroDivisors (D.nd.O i)), (s : D.nd.O i) • Λ (LocalizedModule.mk m s) = kap1 i Dd m := by
    intro m s
    rw [← map_smul, KLift.smul_mk, liftK_mkK]
  have hΛi : ∀ v, Λ v = 0 → v = 0 := by
    intro v hv
    induction v using LocalizedModule.induction_on with
    | h m s =>
      have h1 := hΛs m s
      rw [hv, smul_zero] at h1
      rw [lattice_inclusion_injective i Dd (h1.symm.trans (map_zero (kap1 i Dd)).symm), LocalizedModule.zero_mk]
  have hΛe : ∀ (γ : ↥(Γn i dc n)) v x', Λ (locRep ρP γ v) x' =
      algebraMap (D.nd.O i) (FractionRing (D.nd.O i))
          ((chiU D.nd i 1 (γ : GE D.nd) : D.nd.O i) * ((epsU D.nd i (γ : GE D.nd) : (D.nd.O i)ˣ) : D.nd.O i)) •
        (Λ v x' * (rO D.nd i r (Dd.p x') (γ : GE D.nd)⁻¹).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))) := by
    intro γ v x'
    induction v using LocalizedModule.induction_on with
    | h m s =>
      have h0 : locRep ρP γ (LocalizedModule.mk m s) = LocalizedModule.mk (ρP γ m) s := LocalizedModule.map_mk _ _ _ _
      rw [h0]
      apply KLift.smul_cancel s
      have h1 := congrFun (hΛs (ρP γ m) s) x'
      have h2 := congrFun (hΛs m s) x'
      rw [Pi.smul_apply] at h1 h2
      rw [h1, smul_comm, ← Matrix.smul_mul, h2]
      exact idempotent_part_representation_at i r Dd hr' hsm hχ (γ : GE D.nd) m x'
  let Ψ : Dd.X' × Fin D.R.nV → TrV e (MK (O := D.nd.O i) (FirstSummandSubmodule (D.nd.O i) Dd.e₁)) →ₗ[Br.LLw (D.nbr i _ hn)]
      (Fin D.R.nV → Br.LLw (D.nbr i _ hn)) := fun q =>
    { toFun := fun v j => e ((Λ (KLift.untr e v)) q.1 q.2 j)
      map_add' := fun v w => funext fun j => by
        show e ((Λ (KLift.untr e v + KLift.untr e w)) q.1 q.2 j) = _
        rw [map_add (f := _)]
        simp [map_add (f := _)]
      map_smul' := fun c v => funext fun j => by
        show e ((Λ (e.symm c • KLift.untr e v)) q.1 q.2 j) = c * e ((Λ (KLift.untr e v)) q.1 q.2 j)
        rw [smulK]
        simp [Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, map_mul] }
  haveI : FiniteDimensional (Br.LLw (D.nbr i _ hn)) (TrV e (MK (O := D.nd.O i) (FirstSummandSubmodule (D.nd.O i) Dd.e₁))) :=
    KLift.finDim_of_lat (Ow := Br.Ow (D.nbr i _ hn)) (Qp := ℚ_[D.nd.l i])
      (KLift.latOf e (D.nbr i _ hn).eO mkK (Br.iota D.nbr i _ hn) (KLift.heO_br i dc hn) (locRep ρP) ρP KLift.mkK_inj
        (fun γ m => (locRep_mkK _ γ m).symm) KLift.mkK_span)
  refine sub_of_fam (fun q => Dd.p q.1) Ψ (fun v hv => ?_) (fun q g v => ?_)
  · have h0 : Λ (KLift.untr e v) = 0 := by
      funext x'
      ext a b
      have := congrFun (hv (x', a)) b
      simpa [Ψ] using this
    exact hΛi _ h0
  · funext j
    have key : ∀ γ : ↥(Γn i dc n), (γ : GE D.nd) = ((Br.iota D.nbr i _ hn g : Gw D.nd (K.plOf i dc n)) : GE D.nd) →
        e ((Λ (locRep ρP γ (KLift.untr e v))) q.1 q.2 j) =
          (TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i _ hn) (rDuO D.nd i r (Dd.p q.1)) g).mulVec (Ψ q v) j := by
      intro γ hγ
      rw [hΛe, hγ]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.mulVec, dotProduct, locC_apply i dc hn, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul,
        Finset.mul_sum, map_sum, map_mul, Matrix.map_apply, rDuO, twistM, dualM, MonoidHom.coe_mk, OneHom.coe_mk,
        Matrix.transpose_apply, Ψ, LinearMap.coe_mk, AddHom.coe_mk]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [MonoidHom.mul_apply, Units.val_mul, map_mul]
      rw [show eK (D.nbr i _ hn) = e from rfl]
      have hc : ∀ x y z w : Br.LLw (D.nbr i _ hn), x * y * (z * w) = x * y * w * z := fun x y z w => by ring
      exact hc _ _ _ _
    exact key (Br.iota D.nbr i _ hn g) rfl

end Rec

end Formalism.MainNotions.N.KRowA

end
end

section

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.Sel

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions Formalism.MainNotions.N
  Formalism.MainNotions.N.K Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N.KHf

section Col

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
  (π : D.nd.X i) {A T' : Type} [Ring A] [Algebra (D.nd.O i) A] [CommRing T'] [Algebra T' A]
  (M : Type) [AddCommGroup M] [Module A M] [Module (D.nd.O i) M] [SMulCommClass A (D.nd.O i) M]
  (r : GE D.nd →* A) (χ : GE D.nd →* T'ˣ)
  (φ : M ≃ₗ[D.nd.O i] KOG (D.nd.O i) D.R.r)
  (hφ : ∀ g m, φ (uRep (D.nd.O i) (M := M) r χ g m) = Br.WKO i ρ π g (φ m))


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in
theorem bkLoc_col (n : ℕ) (hw : plOf i dc n ∈ placesOver D.host.E (D.nd.l i))
    {V : Type} [AddCommGroup V] [Module (FractionRing (D.nd.O i)) V] [Module (D.nd.O i) V]
    [IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) V]
    (ρV : Representation (D.nd.O i) ↥(decs D.host.E (Aw i dc) n) V) (qV : V →ₗ[D.nd.O i] M)
    (Ψ : TrV (eK (D.nbr i _ hw)) V →ₗ[Br.LLw (D.nbr i _ hw)] (Fin D.R.r → Br.LLw (D.nbr i _ hw)))
    (hΨc : Continuous Ψ)
    (hΨe : ∀ g v, Ψ (repL (eK (D.nbr i _ hw)) ρV (Br.iota D.nbr i _ hw) g v) =
      matRep (Br.locM (D.nbr i _ hw) ((WpO D.nd i ρ π).comp (decS D.nd (plOf i dc n)))) g (Ψ v))
    (hcomp : ∀ v, Br.phi (D.nbr i _ hw) D.R.r (φ (qV v)) = Submodule.Quotient.mk (Ψ v))
    (y : ReciprocityTheory.Gal.H1 ((Br.WKO i ρ π).comp (decS D.nd (plOf i dc n))))
    (hy : psi (resRep (uRep (D.nd.O i) (M := M) r χ) (decs D.host.E (Aw i dc) n))
        ((Br.WKO i ρ π).comp (decS D.nd (plOf i dc n))) φ (fun g m => hφ g m) y ∈
      F0col i dc n ρV (resRep (uRep (D.nd.O i) (M := M) r χ) (decs D.host.E (Aw i dc) n)) qV) :
    y ∈ Br.bk D.loc D.nbr i (plOf i dc n) hw (WpO D.nd i ρ π) := by
  induction y using Submodule.Quotient.induction_on with
  | H f =>
    have hy' : Submodule.Quotient.mk (psiZ (resRep (uRep (D.nd.O i) (M := M) r χ) (decs D.host.E (Aw i dc) n))
        ((Br.WKO i ρ π).comp (decS D.nd (plOf i dc n))) φ (fun g m => hφ g m) f) ∈
        F0col i dc n ρV (resRep (uRep (D.nd.O i) (M := M) r χ) (decs D.host.E (Aw i dc) n)) qV := hy
    obtain ⟨c, hc, hceq⟩ := Submodule.mem_map.mp hy'
    have hd := (Submodule.Quotient.eq _).1 hceq
    have hpsi := Submodule.sub_mem _ hc (Submodule.mem_sup_right hd)
    simp only [Submodule.mem_comap, Submodule.coe_subtype, sub_sub_cancel] at hpsi
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hpsi
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp ha
    obtain ⟨m, rfl⟩ := hb
    have hz' : z ∈ fZ i dc n ρV := hz
    unfold fZ at hz'
    rw [dite_eq_left hw] at hz'
    have hz2 : (fun g => (z (Br.iota D.nbr i _ hw g) : TrV (eK (D.nbr i _ hw)) V)) ∈
        finiteCocycles (Br.PD D.loc D.nbr i _ hw) (repL (eK (D.nbr i _ hw)) ρV (Br.iota D.nbr i _ hw)) := hz'
    have hpt : ∀ x, f.1 x = φ (qV (z x)) + ((Br.WKO i ρ π) (x : GE D.nd) (φ m) - φ m) := by
      intro x
      have e := congrFun hab x
      change qV (z x) + (uRep (D.nd.O i) (M := M) r χ (x : GE D.nd) m - m) = φ.symm (f.1 x) at e
      rw [← hφ, ← map_sub, ← map_add (f := _), e, LinearEquiv.apply_symm_apply]
    have h1 : (fun g => Submodule.Quotient.mk (Ψ (z (Br.iota D.nbr i _ hw g))) :
        ↥(GK (D.nbr i _ hw).Kw) → (Fin D.R.r → Br.LLw (D.nbr i _ hw)) ⧸
          (Br.lat (D.nbr i _ hw) ((WpO D.nd i ρ π).comp (decS D.nd (plOf i dc n)))).T) ∈
        HfD ((D.loc (D.nd.l i)).PD (D.nbr i _ hw).Kw)
          (Br.lat (D.nbr i _ hw) ((WpO D.nd i ρ π).comp (decS D.nd (plOf i dc n)))) :=
      Submodule.mem_sup_left ⟨fun g => Ψ (z (Br.iota D.nbr i _ hw g)),
        (cocyclesFunctorial_holds _ _ _ _ _ _ _ _ _ _ _ _ Ψ hΨc hΨe _).2 hz2, rfl⟩
    have h2 : (fun g => actD (Br.lat (D.nbr i _ hw) ((WpO D.nd i ρ π).comp (decS D.nd (plOf i dc n)))) g
          (Br.phi (D.nbr i _ hw) D.R.r (φ m)) - (show (Fin D.R.r → Br.LLw (D.nbr i _ hw)) ⧸ (Br.lat (D.nbr i _ hw) ((WpO D.nd i ρ π).comp (decS D.nd (plOf i dc n)))).T from
            Br.phi (D.nbr i _ hw) D.R.r (φ m))) ∈
        HfD ((D.loc (D.nd.l i)).PD (D.nbr i _ hw).Kw)
          (Br.lat (D.nbr i _ hw) ((WpO D.nd i ρ π).comp (decS D.nd (plOf i dc n)))) :=
      Submodule.mem_sup_right ⟨Br.phi (D.nbr i _ hw) D.R.r (φ m), rfl⟩
    have h3 := Submodule.add_mem _ h1 h2
    have hfun : (Br.Phi (D.nbr i _ hw) ((Br.WKO i ρ π).comp (decS D.nd (plOf i dc n))) f :
        ↥(GK (D.nbr i _ hw).Kw) → (Fin D.R.r → Br.LLw (D.nbr i _ hw)) ⧸
          (Br.lat (D.nbr i _ hw) ((WpO D.nd i ρ π).comp (decS D.nd (plOf i dc n)))).T) =
        (fun g => Submodule.Quotient.mk (Ψ (z (Br.iota D.nbr i _ hw g)))) +
        (fun g => actD (Br.lat (D.nbr i _ hw) ((WpO D.nd i ρ π).comp (decS D.nd (plOf i dc n)))) g
          (Br.phi (D.nbr i _ hw) D.R.r (φ m)) - (show (Fin D.R.r → Br.LLw (D.nbr i _ hw)) ⧸ (Br.lat (D.nbr i _ hw) ((WpO D.nd i ρ π).comp (decS D.nd (plOf i dc n)))).T from
            Br.phi (D.nbr i _ hw) D.R.r (φ m))) := by
      funext g
      have hact : Br.phi (D.nbr i _ hw) D.R.r (Br.WKO i ρ π (Br.ι (D.nbr i _ hw) g : GE D.nd) (φ m)) =
          actD (Br.lat (D.nbr i _ hw) ((WpO D.nd i ρ π).comp (decS D.nd (plOf i dc n)))) g
            (Br.phi (D.nbr i _ hw) D.R.r (φ m)) :=
        phi_act D i (plOf i dc n) hw ((WpO D.nd i ρ π).comp (decS D.nd (plOf i dc n))) g (φ m)
      show Br.phi (D.nbr i _ hw) D.R.r (f.1 (Br.ι (D.nbr i _ hw) g)) = _
      rw [hpt, map_add (f := _), map_sub, hcomp]
      exact congrArg (fun t => Submodule.Quotient.mk (Ψ (z (Br.iota D.nbr i _ hw g))) +
        (t - Br.phi (D.nbr i _ hw) D.R.r (φ m))) hact
    have hmem : f ∈ (HfD ((D.loc (D.nd.l i)).PD (D.nbr i _ hw).Kw)
        (Br.lat (D.nbr i _ hw) ((WpO D.nd i ρ π).comp (decS D.nd (plOf i dc n))))).comap
          (Br.Phi (D.nbr i _ hw) ((Br.WKO i ρ π).comp (decS D.nd (plOf i dc n)))) := by
      exact Submodule.mem_comap.mpr (hfun ▸ h3)
    exact ⟨f, hmem, rfl⟩

end Col

end Formalism.MainNotions.N.K.Sel

end
end

section

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Formalism.BasicNotions Classical

namespace Formalism.MainNotions.N.KUnr

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions Formalism.MainNotions.N

section Gen

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime]

theorem exists_unr_dec (A : ValuationSubring Ω) (hp : A.valuation (p : Ω) < 1) :
    ∃ χ : ↥(A.decompositionSubgroup F) → ℤ_[p], Continuous χ ∧ (∀ g h, χ (g * h) = χ g + χ h) ∧
      (∀ g : ↥(A.decompositionSubgroup F), (g : Ω ≃ₐ[F] Ω) ∈ Ine (F := F) A → χ g = 0) ∧ ∃ g, χ g = 1 := by
  exact hT2Core.out.unr A hp

end Gen

section Rec

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)

private lemma plOf_colIdx (l : K.Col i dc) : K.plOf i dc (K.colIdx i dc l) = l.1 := by
  have hmem : l.1 ∈ K.plSet i dc := by
    simp only [K.plSet, Finset.mem_union]
    exact Or.inl (Or.inr l.2)
  have hlt : ((K.plSet i dc).equivFin ⟨l.1, hmem⟩ : ℕ) < (K.plSet i dc).card := Fin.is_lt _
  unfold K.colIdx K.idx K.plOf
  rw [dite_eq_left hmem, dite_eq_left hlt]
  simp

theorem col_over (l : K.Col i dc) : K.plOf i dc (K.colIdx i dc l) ∈ placesOver D.host.E (D.nd.l i) := by
  rw [plOf_colIdx]
  first
  | exact (dc.cover l.1).mp (Or.inr l.2)
  | exact ((dc.cover l.1).mp (Or.inr l.2)).1
  | (have h := (dc.cover l.1).mp (Or.inr l.2); done)

theorem col_hp (l : K.Col i dc) :
    (K.Aw i dc (K.colIdx i dc l)).valuation ((D.nd.l i : ℕ) : D.nd.Om) < 1 := by
  have hov := col_over i dc l
  rw [plOf_colIdx] at hov
  unfold K.Aw
  rw [plOf_colIdx]
  have h2 := (D.nd.plOm.2 l.1 ((D.nd.l i : ℕ) : 𝓞 D.host.E)).mpr hov
  simpa using h2

theorem unrHom (l : K.Col i dc) : KFin.UnrHom i dc l := by
  obtain ⟨χ, hc, hm, hI, g1, h1⟩ :=
    exists_unr_dec (F := D.host.E) (K.Aw i dc (K.colIdx i dc l)) (col_hp i dc l)
  refine ⟨fun g => algebraMap ℤ_[D.nd.l i] (D.nd.O i) (χ g), ⟨fun g h => ?_, fun g hg => ?_, fun hn => ?_⟩, g1, ?_⟩
  · show algebraMap ℤ_[D.nd.l i] (D.nd.O i) (χ (g * h)) = _ + _
    rw [hm, map_add (f := _)]
  · have hg' : ((g : D.nd.Om ≃ₐ[D.host.E] D.nd.Om)) ∈ Ine (F := D.host.E) (K.Aw i dc (K.colIdx i dc l)) :=
      Subgroup.mem_subgroupOf.1 hg
    show algebraMap ℤ_[D.nd.l i] (D.nd.O i) (χ g) = 0
    rw [hI g hg', map_zero]
  · have hf : Continuous fun g : ↥(KFin.Γc i dc l) => algebraMap ℤ_[D.nd.l i] (D.nd.O i) (χ g) :=
      (K.Topo.continuous_alg i).comp hc
    have e1 : ∀ c : D.nd.O i, KHf.eK (D.nbr i _ hn) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) c) =
        ((D.nbr i _ hn).eO c : Br.LLw (D.nbr i _ hn)) := fun c => by
      rw [KHf.eK_apply, Br.toLLK_alg]
      rfl
    simp only [e1]
    exact continuous_subtype_val.comp ((D.nbr i _ hn).eO_cont.comp (hf.comp (Br.iota_cont D.nbr i _ hn)))
  · show algebraMap ℤ_[D.nd.l i] (D.nd.O i) (χ g1) = 1
    rw [h1, map_one]

end Rec

end Formalism.MainNotions.N.KUnr
end
end

section

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Formalism.BasicNotions Classical

namespace Formalism.MainNotions.N.K

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Matrix Formalism.RepresentationBoundsCohomology.ringDataObjects Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities Formalism.NG Formalism.MainNotions.N.RepresentationBoundsCohomology

variable {D : D7} (i : D.nd.Loc)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)




theorem normalized_ring_data (hN : NormAt D.nd r ρ π)
    (hG1 : ∀ (γ : GE D.nd) (k : ℕ), (fun x : D.nd.X i => ((rO D.nd i r x γ).charpolyRev).coeff k) ∈ D.nd.T i)
    (hres : Submodule.span (kk D.nd i)
      (Set.range (mapM (IsLocalRing.residue (D.nd.O i)) (rhoO D.nd i ρ π))) = ⊤)
    (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
    (hI : IdemHyp (D.nd.O i) (D.nd.T i) (repX D.nd r) π (blk D.R) eB e₁)
    (hX : DistinctEigenvalueCornerPerturbation (D.nd.O i) (D.nd.T i) (repX D.nd r) π D.R.t g0 eB s) :
    ∃ Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (blk D.R),
      RingDef (D.nd.O i) (D.nd.T i) (repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd ∧
      vcc (D.nd.T i) (D.nd.Z i : Set (D.nd.X i)) (Dd.p Dd.π') =
        Module.length (D.nd.O i) (D.nd.O i ⧸ ccAt (D.nd.T i) (D.nd.Z i) π) ∧
      ∃ (_ : IsNoetherian Dd.R' Dd.R')
        (_ : ∀ x', IsScalarTower Dd.T' Dd.R' (EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x'))
        (_ : ∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (blk D.R) Dd.ρk k))
        (_ : ∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (blk D.R) Dd.ρk k))
        (_ : ∀ k, IsScalarTower (D.nd.O i) Dd.R' (blockRestrictedRepresentationType (blk D.R) Dd.ρk k)),
        Dd.Top (D.nd.T i) (one_le_letterBlockLength D.R) ∧
        ∀ [TopologicalSpace (FractionRing (D.nd.O i))] [IsTopologicalAddGroup (FractionRing (D.nd.O i))]
          [ContinuousSMul (D.nd.O i) (FractionRing (D.nd.O i))] [TopologicalSpace Dd.R']
          [IsTopologicalAddGroup Dd.R'] [ContinuousConstSMul (D.nd.O i) Dd.R'] [ContinuousMul Dd.R'],
          RealDisplayAllK (D.nd.l i) (D.nd.O i) (D.nd.X i) Dd.X' (D.nd.Z i : Set (D.nd.X i)) Dd.p (Fin D.R.nV)
            Dd.R' Dd.T' D.host.E D.nd.Om Dd.r Dd.χ Dd.E Dd.e₁ D.R.t (one_le_letterBlockLength D.R) (blk D.R) Dd.ρk Dd.δO
            (epsU D.nd i) g0 (Module.length (D.nd.O i) (D.nd.O i ⧸ ccAt (D.nd.T i) (D.nd.Z i) π)) := by
  obtain ⟨Dd, hD, ⟨i1, i2, -, i4, i5⟩, i3, hT⟩ := ring_objects_exist (D.nd.O i) (D.nd.X i) (D.nd.T i) (Fin D.R.nV) (GE D.nd)
    (repX D.nd r) π D.R.t (one_le_letterBlockLength D.R) (blk D.R) (chiU D.nd i 1) (epsU D.nd i) (primHyp_of D.nd r ρ π hN hG1)
    (absIrr_of_res D.nd r ρ π hN hres) eB e₁ hI g0 s hX
  have hFree := fun Z => displayFree (D.nd.O i) (D.nd.X i) (D.nd.T i) (Fin D.R.nV) (GE D.nd) (repX D.nd r) π D.R.t
    (one_le_letterBlockLength D.R) (blk D.R) (chiU D.nd i 1) (epsU D.nd i) (primHyp_of D.nd r ρ π hN hG1)
    (absIrr_of_res D.nd r ρ π hN hres) eB e₁ hI g0 s hX Dd hD hT Z
  have hp : Dd.p Dd.π' = π := by
    obtain ⟨-, -, -, -, h, -⟩ := hD
    exact h
  have hv : vcc (D.nd.T i) (D.nd.Z i : Set (D.nd.X i)) (Dd.p Dd.π') =
      Module.length (D.nd.O i) (D.nd.O i ⧸ ccAt (D.nd.T i) (D.nd.Z i) π) := by
    rw [hp, Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.length_ccAt]
  refine ⟨Dd, hD, hv, i1, i2, i3, i4, i5, hT, ?_⟩
  intro _ _ _ _ _ _ _
  exact realDisplayAllK_of (D.nd.l i) (D.nd.O i) (D.nd.X i) Dd.X' (D.nd.Z i : Set (D.nd.X i)) Dd.p (Fin D.R.nV)
    Dd.R' Dd.T' D.host.E D.nd.Om Dd.r Dd.χ Dd.E Dd.e₁ Dd.δ D.R.t (one_le_letterBlockLength D.R) (blk D.R) Dd.ρk Dd.δO
    (epsU D.nd i) g0 _ (D.nd.T i) Dd.T' Dd.q Dd.b Dd.π' Dd.ρπ Dd.sE Dd.tE (chiU D.nd i 1 g0) hT
    (hFree (D.nd.Z i : Set (D.nd.X i))) (Formalism.RepresentationBoundsCohomology.SF.deltaO_eq hD) hv.symm

end Formalism.MainNotions.N.K

end
end
