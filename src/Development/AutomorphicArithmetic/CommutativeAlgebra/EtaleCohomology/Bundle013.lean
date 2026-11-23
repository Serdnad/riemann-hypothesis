module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle010
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle011
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle007
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.PhiHIterSmul
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.PullbackFinRelation
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.AdmCrys
public import Development.AutomorphicArithmetic.ThetaCorrespondence.LocalComparison.Bundle001
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.NilToPhiAlt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle023
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernUnique
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Mathlib.Tactic.TypeStar

@[expose] public section

section



set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison UpperTheory.Ru.crystallineComparison

private theorem UpperTheory.Ru.crystallineComparison.quasiCompact_of_proj {R : Type} [CommRing R] {X : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of R)} (h : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver f) : QuasiCompact f := by
  refine Exists.elim h fun N hN => Exists.elim hN fun i hi => ?_
  have : IsProper (ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace.str R N) := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str R N
  have : IsClosedImmersion i := hi.1
  rw [← hi.2]
  infer_instance

theorem UpperTheory.Ru.crystallineComparison.final :
    UpperTheory.Ru.crystallineComparison.Final := by
  unfold UpperTheory.Ru.crystallineComparison.Final
  intro l _ K _ _ _ r f hf hx hC ϖ hϖ M hM n j T hr hPt A hA B₀
  obtain ⟨Amp, N, F, hFacts, hEt, hLaws, ⟨bm⟩, ⟨pm⟩, hfN, hTeich, hall⟩ := hC
  refine Exists.elim (CrystallineSemistableComparison.E.etMap l K) fun e he => ?_
  refine Exists.elim (UpperTheory.Ru.crystallineComparison.ePin l K Model.Sm Amp e he) fun e' hcomp => ?_
  refine Exists.elim (UpperTheory.Ru.crystallineComparison.pbIota l K B₀) fun ι hι' => ?_
  have hInj : InjE B₀ e M j :=
    UpperTheory.Ru.crystallineComparison.injOf l K B₀ ι hι'.1 hι'.2.1 hι'.2.2.1 Model.Sm Amp hFacts hEt hLaws e e' bm pm hcomp M hM j
  have hAbs : AbsInv B₀ e M j f ϖ :=
    UpperTheory.Ru.crystallineComparison.absInvOf l K r B₀ (UpperTheory.Ru.crystallineComparison.pbInv l K B₀ r) e he M hM f N j hx hfN hTeich F
      (hall M hM j).1 (hall M hM j).2 ϖ hϖ.not_isUnit
  have hP : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver M.p := hM.1.1
  have hSm : Smooth M.p := hM.2
  have hQC : QuasiCompact M.p := UpperTheory.Ru.crystallineComparison.quasiCompact_of_proj hP
  have hAff : UpperTheory.Gal.crystallineComparison.AffFin M.X := UpperTheory.Gal.crystallineComparison.affFin_of (OK l K) M.X M.p hP
  exact UpperTheory.Ru.crystallineComparison.top l K ϖ hϖ e he M hSm hQC hAff f n j hf T hr hPt A hA B₀ hInj hAbs
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc CrystallineSemistableComparison Module

namespace UpperTheory.Ru.crystallineComparison

private theorem exists_glRep {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V] {a : ℕ}
    (b : Basis (Fin a) k V) (π : Representation k G V) :
    ∃ r : G →* GL (Fin a) k, ∀ g, (r g : Matrix (Fin a) (Fin a) k) = LinearMap.toMatrix b b (π g) := by
  let f : G →* Matrix (Fin a) (Fin a) k :=
    { toFun := fun g => LinearMap.toMatrix b b (π g)
      map_one' := by rw [map_one]; exact LinearMap.toMatrix_one b
      map_mul' := fun g h => by rw [map_mul]; exact LinearMap.toMatrix_mul b _ _ }
  exact ⟨f.toHomUnits, fun g => MonoidHom.coe_toHomUnits f g⟩

private noncomputable def actRep {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (M : Model l K) (n : ℕ) :
    Representation ℚ_[l] K.fixingSubgroup (M.V n) :=
  (GlobalTheory.EtC.galHQ l (PadicAlgCl l) M.q n 0).comp (IntermediateField.fixingSubgroupEquiv K).toMonoidHom

end UpperTheory.Ru.crystallineComparison

open UpperTheory.Ru.crystallineComparison in
theorem UpperTheory.Ru.crystallineComparison.crysCopy :
    UpperTheory.Ru.crystallineComparison.CrysCopy := by
  intro hC l _ P AI hT K M hM j a b
  haveI := K.2
  obtain ⟨FreeQuotientRank⟩ := UpperTheory.Lit.Cmp.locTied6 l P AI hT
  obtain ⟨T⟩ := hT
  have hadm := UpperTheory.Gal.Seam.isAdmP_of_isAdm FreeQuotientRank (hC l K.1 M hM.1 hM.2 j a b)
  obtain ⟨r, hr⟩ : ∃ r : ↥(GK K) →* GL (Fin a) ℚ_[l], ∀ g : ↥(GK K),
      (r g : Matrix (Fin a) (Fin a) ℚ_[l]) = LinearMap.toMatrix b b (M.act j g) := exists_glRep b (actRep M j)
  have hadm' : UpperTheory.Gal.Seam.IsAdmP P (GK K) (fun σ => (r σ : Matrix (Fin a) (Fin a) ℚ_[l])) := by
    have h0 : (fun σ : ↥(GK K) => (r σ : Matrix (Fin a) (Fin a) ℚ_[l])) = (M.mat j b : ↥(GK K) → _) := funext hr
    rw [h0]
    exact hadm
  let r' : ↥(GK K) →* GL (Fin a) ↥K.1 :=
    (Units.map (RingHom.mapMatrix (algebraMap ℚ_[l] ↥K.1)).toMonoidHom).comp r
  have hr' : ∀ σ i j, (r' σ).val i j = algebraMap ℚ_[l] ↥K.1 ((r σ).val i j) := fun σ i j => rfl
  have hc := UpperTheory.Gal.Seam.isCrys_of_isAdmP l P AI T K K a r r' hr' hadm'
  have hcρ : WeaklyAdmissibleFiltrations.IsCrys (P.PD K) (((Matrix.toLinAlgEquiv' : Matrix (Fin a) (Fin a) ℚ_[l] ≃ₐ[ℚ_[l]] _) : _ →* _).comp
      ((Units.coeHom _).comp r) : Representation ℚ_[l] ↥(GK K) (Fin a → ℚ_[l])) :=
    (GlobalTheory.Pst.isCrys_ext_iff (P.PD K) (fun g => ⟨(r g : Matrix (Fin a) (Fin a) ℚ_[l]), fun x => rfl, fun x => rfl⟩)).1 hc
  refine ⟨_, fun g v => ?_, hcρ⟩
  show (r g : Matrix (Fin a) (Fin a) ℚ_[l]).mulVec (b.equivFun v) = b.equivFun (M.act j g v)
  rw [hr g]
  simpa using LinearMap.toMatrix_mulVec_repr b b (M.act j g) v
end

section

open CategoryTheory AlgebraicGeometry

private lemma flat_of_dvr {O O' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O'] [IsDomain O']
    (φ : O →+* O') (ϖ : O) (hϖ : Irreducible ϖ) (h0 : φ ϖ ≠ 0) : φ.Flat := by
  have hinj : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra hne
    obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hϖ
    rw [map_mul, map_pow] at ha
    rcases mul_eq_zero.1 ha with h | h
    · exact (u.isUnit.map φ).ne_zero h
    · exact pow_ne_zero k h0 h
  algebraize [φ]
  have : FaithfulSMul O O' := (faithfulSMul_iff_algebraMap_injective O O').2 hinj
  have : Module.IsTorsionFree O O' := inferInstance
  exact (inferInstance : Module.Flat O O')

theorem UpperTheory.Ru.crystallineComparison.ptIdBC :
    UpperTheory.Ru.crystallineComparison.PtIdBC := by
  intro l q n O O' _ _ _ _ _ _ φ ϖ hϖ hϖ' hq Y Y' p p' g hpb T hT hId
  have hflat : φ.Flat := flat_of_dvr φ ϖ hϖ hϖ'.ne_zero
  choose T' κ h1 h2 h3 _ using fun j => UpperTheory.Gal.crystallineComparison.corrPull_of l _ _ Y Y' _ p p' g hpb (T j) (hT j)
  refine ⟨T', κ, fun j => ⟨(h1 j).flip, (h2 j).symm, h3 j⟩, ?_⟩
  exact UpperTheory.Gal.crystallineComparison.ptIdBC_of l q n O O' φ hflat ϖ (φ ϖ) (fun _ _ => Iff.rfl)
    (fun a => Ideal.mem_span_singleton.2 (hq a)) Y Y' p p' g hpb T T' κ h1 h2 h3 hId
end
