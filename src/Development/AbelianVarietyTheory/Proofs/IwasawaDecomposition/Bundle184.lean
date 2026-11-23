module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle051
public import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle180
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle080
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle470
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecompositionGroupLocalGaloisIso
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle158
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1046
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle166
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle165
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle181
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle005
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle065
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DiscreteTopologyRationalPointsHermitianSpace
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
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
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.TensorProduct.Nontrivial
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle002
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull

@[expose] public section

section

open TensorProduct
namespace GlobalTheory.FieldExtensionExists

theorem exists_field_extension {R R' K : Type} [CommRing R] [CommRing R'] [Field K]
    (ρ : R →+* R') (hinj : Function.Injective ρ) (hfin : ρ.Finite) (φ : R →+* K) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L) (χ : R' →+* L),
      χ.comp ρ = (algebraMap K L).comp φ := by
  letI : Algebra R R' := ρ.toAlgebra
  haveI : Algebra.IsIntegral R R' := ⟨fun x => hfin.to_isIntegral x⟩
  haveI : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  obtain ⟨q, -, hq, hqc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (RingHom.ker φ) (⊥ : Ideal R') (by
    intro x hx
    have : ρ x = 0 := hx
    have h0 : x = 0 := hinj (this.trans (map_zero ρ).symm)
    rw [h0]; exact Ideal.zero_mem _)
  have hqc' : q.comap ρ = RingHom.ker φ := hqc
  let j : (R ⧸ RingHom.ker φ) →+* (R' ⧸ q) := Ideal.quotientMap q ρ hqc'.ge
  have hj : Function.Injective j := Ideal.quotientMap_injective' hqc'.le
  have hjf : j.Finite := by
    apply RingHom.Finite.of_comp_finite (f := Ideal.Quotient.mk (RingHom.ker φ))
    have : j.comp (Ideal.Quotient.mk (RingHom.ker φ)) = (Ideal.Quotient.mk q).comp ρ := by
      ext x; simp [j]
    rw [this]
    exact (RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective).comp hfin
  letI : Algebra (R ⧸ RingHom.ker φ) (R' ⧸ q) := j.toAlgebra
  letI : Algebra (R ⧸ RingHom.ker φ) K := (RingHom.kerLift φ).toAlgebra
  haveI : Module.Finite (R ⧸ RingHom.ker φ) (R' ⧸ q) := hjf
  haveI : Nontrivial (K ⊗[R ⧸ RingHom.ker φ] (R' ⧸ q)) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain _ _ _
      (RingHom.kerLift_injective φ) hj
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (K ⊗[R ⧸ RingHom.ker φ] (R' ⧸ q))
  refine ⟨(K ⊗[R ⧸ RingHom.ker φ] (R' ⧸ q)) ⧸ M, Ideal.Quotient.field M, inferInstance,
    (inferInstance : Module.Finite K ((K ⊗[R ⧸ RingHom.ker φ] (R' ⧸ q)) ⧸ M)),
    (Ideal.Quotient.mk M).comp ((Algebra.TensorProduct.includeRight (R := R ⧸ RingHom.ker φ) (A := K)
      (B := R' ⧸ q)).toRingHom.comp (Ideal.Quotient.mk q)), ?_⟩
  ext r
  change Ideal.Quotient.mk M (Algebra.TensorProduct.includeRight (R := R ⧸ RingHom.ker φ) (A := K)
      (B := R' ⧸ q) (algebraMap (R ⧸ RingHom.ker φ) (R' ⧸ q) (Ideal.Quotient.mk _ r))) =
    Ideal.Quotient.mk M ((φ r) ⊗ₜ 1)
  rw [AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply]
  rfl

theorem exists_extension : ∀ (R R' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (ρ : R →+* R'),
    Function.Injective ρ → ρ.Finite → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V →
    ∀ (ψ : R →+* V), IsLocalHom ψ → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V')
      (f : V →+* V') (ψ' : R' →+* V'), GlobalTheory.LN.CDvr V' ∧ Function.Injective f ∧ IsLocalHom f ∧ IsLocalHom ψ' ∧
      ψ'.comp ρ = f.comp ψ := by
  intro R R' _ _ _ _ ρ hinj hfin V _ _ _ hV ψ hψ
  obtain ⟨h1, h2, h3⟩ := hV
  haveI : CharZero (FractionRing V) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective V (FractionRing V))
  obtain ⟨L, _, _, _, χ, hχ⟩ := exists_field_extension ρ hinj hfin ((algebraMap V (FractionRing V)).comp ψ)
  obtain ⟨W, _, _, hW1, hW2, _, _, _, hc, -, hf, hl, hint, -⟩ :=
    GlobalTheory.SS.exists_complete_dvr_finite_extension V (FractionRing V) L
  have hWL : Function.Injective (algebraMap W L) := IsFractionRing.injective W L
  have hmem : ∀ x : R', ∃ w : W, algebraMap W L w = χ x := by
    intro x
    obtain ⟨P, hP, hPx⟩ := hfin.to_isIntegral x
    refine hint (χ x) ⟨P.map ψ, hP.map ψ, ?_⟩
    rw [Polynomial.eval₂_map, RingHom.comp_assoc, ← hχ, ← Polynomial.hom_eval₂, hPx, map_zero]
  choose g hg using hmem
  let ψ' : R' →+* W :=
    { toFun := g
      map_one' := hWL (by simp [hg])
      map_mul' := fun x y => hWL (by simp [hg])
      map_zero' := hWL (by simp [hg])
      map_add' := fun x y => hWL (by simp [hg]) }
  have hcomp : ψ'.comp ρ = (algebraMap V W).comp ψ := by
    ext r
    apply hWL
    have e1 := RingHom.congr_fun hχ r
    have e2 := RingHom.congr_fun hc (ψ r)
    simp only [RingHom.comp_apply] at e1 e2 ⊢
    rw [e2, ← e1]
    exact hg _
  have hloc : IsLocalHom (ψ'.comp ρ) := by rw [hcomp]; infer_instance
  have hmax : ((IsLocalRing.maximalIdeal W).comap ψ').IsMaximal := by
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_comap' ρ hfin.to_isIntegral
    have e : (IsLocalRing.maximalIdeal W).comap (ψ'.comp ρ) = IsLocalRing.maximalIdeal R :=
      ((IsLocalRing.local_hom_tfae (ψ'.comp ρ)).out 1 5).1 hloc
    rw [Ideal.comap_comap, e]
    infer_instance
  refine ⟨W, inferInstance, inferInstance, inferInstance, algebraMap V W, ψ',
    ⟨hW1, hW2, charZero_of_injective_algebraMap hf⟩, hf, hl, ?_, hcomp⟩
  exact ((IsLocalRing.local_hom_tfae ψ').out 1 5).2 (IsLocalRing.eq_maximalIdeal hmax)

end GlobalTheory.FieldExtensionExists
end

section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

theorem _root_.GlobalTheory.T.unitaryGroup_realPoints_equiv_pi_indefiniteUnitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (I : Type) [Fintype I] (τ : I → (E →+* ℂ)) (θ : I → (Ainf F ⊗[F] E →+* ℂ)) (P Q : I → ℕ) (A : ∀ i, Matrix (Fin (P i) ⊕ Fin (Q i)) (Fin M) ℂ), IsCMExt F E σ → IsCMFam τ → (∀ i, IsInfEmb (τ i) (θ i)) → (∀ i, Formalism.UG.HasSignature (J.map (τ i)) (P i) (Q i)) → (∀ i, (A i)ᴴ * Formalism.UG.Jpq (P i) (Q i) * A i = J.map (τ i)) → ∃ e : HA (Ainf F) σ J ≃ₜ* (∀ i, UpqT (P i) (Q i)), ∀ h i, UpqT.mat (e h i) * A i = A i * ((HA.mat (Ainf F) σ J h : GL (Fin M) (Ainf F ⊗[F] E)) : Matrix (Fin M) (Fin M) (Ainf F ⊗[F] E)).map (θ i) := by
  first | exact @GlobalTheory.Mem.InfGroup.real_points | exact GlobalTheory.Mem.InfGroup.real_points | (intros; apply GlobalTheory.Mem.InfGroup.real_points <;> assumption)
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocDec

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]

theorem exists_lifts_mul_mem (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (ι : Ω →ₐ[E] Kbar w) (θ : Dec (F := E) A ≃* GalLoc w) (hθ : Continuous θ)
    (hl : ∀ σ : Dec (F := E) A, Lifts ι (θ σ) (σ : G E Ω)) (g : GalLoc w) (H : Subgroup (GalLoc w))
    (hH : IsOpen (H : Set (GalLoc w))) :
    ∃ (σ : Weil h) (g' : GalLoc w), Lifts ι g' (σ : G E Ω) ∧ g⁻¹ * g' ∈ H := by
  have : IsGalois E Ω := IsAlgClosure.isGalois E Ω
  set d := θ.symm g with hd
  let S : Set (Dec (F := E) A) := (fun σ => g⁻¹ * θ σ) ⁻¹' (H : Set (GalLoc w))
  have hS : IsOpen S := hH.preimage (continuous_const.mul hθ)
  have hdS : d ∈ S := by
    show g⁻¹ * θ d ∈ H
    rw [hd, MulEquiv.apply_symm_apply, inv_mul_cancel]
    exact H.one_mem
  obtain ⟨t, ht, hts⟩ := isOpen_induced_iff.mp hS
  have hdt : (d : G E Ω) ∈ t := by
    rw [← hts] at hdS
    exact hdS
  have hnhds : {x : G E Ω | (d : G E Ω) * x ∈ t} ∈ nhds (1 : G E Ω) := by
    apply (continuous_const_mul (d : G E Ω)).continuousAt.preimage_mem_nhds
    simpa using ht.mem_nhds hdt
  obtain ⟨F, hF, hFs⟩ := (krullTopology_mem_nhds_one_iff E Ω _).mp hnhds
  let pb := Field.powerBasisOfFiniteOfSeparable E F
  obtain ⟨τ, hτW, hτ⟩ := GlobalTheory.T.weilGroupAtPlace_dense_in_decompositionGroup E Ω A w h (d : G E Ω) d.2 (pb.gen : Ω)
  have hfix : (d : G E Ω)⁻¹ * τ ∈ F.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have e : (((d : G E Ω)⁻¹ * τ : G E Ω) : Ω →ₐ[E] Ω).comp F.val = F.val := pb.algHom_ext (by
      show ((d : G E Ω)⁻¹ * τ) (pb.gen : Ω) = pb.gen
      rw [AlgEquiv.mul_apply, hτ]
      show ((d : G E Ω)⁻¹ * (d : G E Ω)) (pb.gen : Ω) = pb.gen
      simp)
    exact congrArg (fun φ : F →ₐ[E] Ω => φ ⟨x, hx⟩) e
  have hτt : τ ∈ t := by
    have := hFs hfix
    simpa using this
  let σ : Dec (F := E) A := ⟨τ, Weil_le_Dec h hτW⟩
  have hσS : σ ∈ S := by
    rw [← hts]
    exact hτt
  exact ⟨⟨τ, hτW⟩, θ σ, hl σ, hσS⟩

end GlobalTheory.LocDec

namespace GlobalTheory.LocDec

theorem eq_adjoin_of_fixing_iff (E K Ω : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] [Algebra K Ω] [Algebra E K] [IsScalarTower E K Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (ι : Ω →ₐ[E] Kbar w)
    (hι : IsLocEmb A w ι) (L : IntermediateField (w.adicCompletion E) (Kbar w))
    [FiniteDimensional (w.adicCompletion E) L]
    (hfix : ∀ (σ : Weil h) (g : GalLoc w), Lifts ι g σ →
      ((∀ z ∈ L, g z = z) ↔ ∀ x : K, (σ : G E Ω) (algebraMap K Ω x) = algebraMap K Ω x)) :
    L = IntermediateField.adjoin (w.adicCompletion E) (Set.range fun x : K => ι (algebraMap K Ω x)) := by
  obtain ⟨θ, hθ, -, hl⟩ := decomposition_mulEquiv_galLoc E Ω A w h ι hι
  set Kw := w.adicCompletion E
  have : CharZero Kw := charZero_of_injective_algebraMap (algebraMap E Kw).injective
  have : IsGalois Kw (Kbar w) := IsAlgClosure.isGalois Kw (Kbar w)
  set M := IntermediateField.adjoin Kw (Set.range fun x : K => ι (algebraMap K Ω x)) with hM
  have hfx : ∀ (σ : G E Ω) (g' : GalLoc w), Lifts ι g' σ → ∀ x : K,
      (g' (ι (algebraMap K Ω x)) = ι (algebraMap K Ω x) ↔ σ (algebraMap K Ω x) = algebraMap K Ω x) :=
    fun σ g' hg x => by rw [hg]; exact ι.toRingHom.injective.eq_iff
  have : FiniteDimensional E K := Module.Finite.of_restrictScalars_finite ℚ E K
  let pb := Field.powerBasisOfFiniteOfSeparable E K
  have hprim : ∀ σ : G E Ω, σ (algebraMap K Ω pb.gen) = algebraMap K Ω pb.gen →
      ∀ x : K, σ (algebraMap K Ω x) = algebraMap K Ω x := by
    intro σ hσ x
    have e : ((σ : Ω →ₐ[E] Ω).comp (IsScalarTower.toAlgHom E K Ω)) = IsScalarTower.toAlgHom E K Ω :=
      pb.algHom_ext (by simpa using hσ)
    simpa using congrArg (fun φ : K →ₐ[E] Ω => φ x) e
  have hopen : ∀ z : Kbar w,
      IsOpen ((IntermediateField.adjoin Kw {z}).fixingSubgroup : Set (GalLoc w)) := fun z => by
    have : FiniteDimensional Kw (IntermediateField.adjoin Kw {z}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral z)
    exact IntermediateField.fixingSubgroup_isOpen _
  have hmemz : ∀ (z : Kbar w) (k : GalLoc w), k ∈ (IntermediateField.adjoin Kw {z}).fixingSubgroup → k z = z :=
    fun z k hk => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hk z (IntermediateField.mem_adjoin_simple_self _ _)
  have hLopen : IsOpen (L.fixingSubgroup : Set (GalLoc w)) := IntermediateField.fixingSubgroup_isOpen L
  have hLfix : ∀ k : GalLoc w, k ∈ L.fixingSubgroup → ∀ z ∈ L, k z = z :=
    fun k hk => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hk
  apply le_antisymm
  · intro z hz
    rw [← InfiniteGalois.fixedField_fixingSubgroup M, IntermediateField.mem_fixedField_iff]
    intro g hg
    have hga : g (ι (algebraMap K Ω pb.gen)) = ι (algebraMap K Ω pb.gen) :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg _
        (IntermediateField.subset_adjoin _ _ ⟨pb.gen, rfl⟩)
    obtain ⟨σ, g', hlift, hk⟩ := exists_lifts_mul_mem A w h ι θ hθ hl g
      (L.fixingSubgroup ⊓ (IntermediateField.adjoin Kw {ι (algebraMap K Ω pb.gen)}).fixingSubgroup)
      (hLopen.inter (hopen _))
    have hg' : g' = g * (g⁻¹ * g') := by group
    have h1 : g' (ι (algebraMap K Ω pb.gen)) = ι (algebraMap K Ω pb.gen) := by
      rw [hg', AlgEquiv.mul_apply, hmemz _ _ (Subgroup.mem_inf.1 hk).2, hga]
    have h2 := hprim σ ((hfx σ g' hlift pb.gen).1 h1)
    have h3 := (hfix σ g' hlift).2 h2 z hz
    rw [hg', AlgEquiv.mul_apply, hLfix _ (Subgroup.mem_inf.1 hk).1 z hz] at h3
    exact h3
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨x, rfl⟩
    rw [← InfiniteGalois.fixedField_fixingSubgroup L]
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    intro g hg
    obtain ⟨σ, g', hlift, hk⟩ := exists_lifts_mul_mem A w h ι θ hθ hl g
      (L.fixingSubgroup ⊓ (IntermediateField.adjoin Kw {ι (algebraMap K Ω x)}).fixingSubgroup)
      (hLopen.inter (hopen _))
    have hg' : g' = g * (g⁻¹ * g') := by group
    have h1 : ∀ z ∈ L, g' z = z := fun z hz => by
      rw [hg', AlgEquiv.mul_apply, hLfix _ (Subgroup.mem_inf.1 hk).1 z hz, hLfix g hg z hz]
    have h2 := (hfx σ g' hlift x).2 ((hfix σ g' hlift).1 h1 x)
    rw [hg', AlgEquiv.mul_apply, hmemz _ _ (Subgroup.mem_inf.1 hk).2] at h2
    exact h2

theorem eq_adjoin_of_fixing_iff_weil : ∀ (E K Ω : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra E K] [IsScalarTower E K Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (ι : Ω →ₐ[E] Kbar w), IsLocEmb A w ι → ∀ L : IntermediateField (w.adicCompletion E) (Kbar w), FiniteDimensional (w.adicCompletion E) L → (∀ (σ : Weil h) (g : GalLoc w), Lifts ι g σ → ((∀ z ∈ L, g z = z) ↔ ∀ x : K, (σ : G E Ω) (algebraMap K Ω x) = algebraMap K Ω x)) → L = IntermediateField.adjoin (w.adicCompletion E) (Set.range fun x : K => ι (algebraMap K Ω x)) := by
  intro E K Ω _ _ _ _ _ _ _ _ _ _ _ A w h ι hι L _ hfix
  exact eq_adjoin_of_fixing_iff E K Ω A w h ι hι L hfix

end GlobalTheory.LocDec
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2.JetEx

namespace GlobalTheory.Mem.Col2.JetFin

theorem finAlg_range {E : Type} [Field E] [NumberField E] (f : E →+* ℂ) : FinAlg (Set.range f) := by
  classical
  let b := Module.finBasis ℚ E
  refine (finAlg_of_finite (T := Set.range (f ∘ b)) (Set.finite_range _) ?_).closure.mono ?_
  · rintro _ ⟨i, rfl⟩
    exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (b i)).algHom f.toRatAlgHom
  · rintro _ ⟨x, rfl⟩

    rw [← b.sum_repr x, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_rat_smul, Rat.smul_def]
    exact mul_mem (SubfieldClass.ratCast_mem _ _) (Subfield.subset_closure ⟨i, rfl⟩)

variable {X : Fields} (A : Amb X) {a b : ℕ} (S : Finset (HeightOneSpectrum (𝓞 X.E)))

theorem thInd_congr (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ) (x x' : HomE X.E a b)
    (h : x - x' ∈ mulLat c (homAt S N N')) : A.thInd S N N' c x = A.thInd S N N' c x' := by
  unfold Amb.thInd Amb.liftW
  rw [isLift_congr A S N N' c x x' h]

theorem finite_thInd (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (M c : ℕ)
    (hN : IsSdLat N) (hN' : IsSdLat N') (hM : 0 < M) (hc : 0 < c) :
    (A.thInd S N N' c '' (divLat M (homAt S N N') : Set (HomE X.E a b))).Finite := by
  have := (GlobalTheory.SemilocalClasses.finite_card_classes X.E a b S N N' M c hN.1 hN'.1 hM hc).1
  refine (Set.finite_range fun q : (↥(divLat M (homAt S N N')) ⧸ (mulLat c (homAt S N N')).comap (divLat M (homAt S N N')).subtype) =>
    A.thInd S N N' c (Quotient.out q).1).subset ?_
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨Submodule.Quotient.mk ⟨x, hx⟩, thInd_congr A S N N' c _ _ ?_⟩
  have := (Submodule.Quotient.eq ((mulLat c (homAt S N N')).comap (divLat M (homAt S N N')).subtype)).1
    (Quotient.out_eq (Submodule.Quotient.mk ⟨x, hx⟩ : (↥(divLat M (homAt S N N')) ⧸ (mulLat c (homAt S N N')).comap (divLat M (homAt S N N')).subtype)))
  exact this

noncomputable def pullLin (γ : Sp X.E a ≃ₗ[X.E] Sp X.E a) (γ' : Sp X.E b ≃ₗ[X.E] Sp X.E b) : VCx X.Tau a b →ₗ[ℂ] VCx X.Tau a b where
  toFun := A.pullV a b γ γ'
  map_add' z w := by
    funext τ i j
    simp only [Amb.pullV, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' t z := by
    funext τ i j
    simp only [Amb.pullV, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

theorem finAlg_jetSet : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (M n : ℕ), X.Ok → 0 < M → A.ESmooth a b → A.ThIndEq a b S M → A.ChiLaw a b → JetAlg A a b S M → (∀ τ, IsAlgebraic ℚ (A.cD τ)) → FinAlg (jetSet A a b S M n) := by
  intro X A a b S M n hX hM hE hT hC hJ hD
  classical
  obtain ⟨Ta, hTa, hTa'⟩ := GlobalTheory.Mem.Col2.JetEx.exists_finset_sdLat_reps X hX a
  obtain ⟨Tb, hTb, hTb'⟩ := GlobalTheory.Mem.Col2.JetEx.exists_finset_sdLat_reps X hX b
  let Z₀ : Set ℂ := ⋃ N ∈ (Ta : Set _), ⋃ N' ∈ (Tb : Set _), ⋃ c ∈ (M.divisors : Set ℕ),
    ⋃ G ∈ A.thInd S N N' c '' (divLat M (homAt S N N') : Set (HomE X.E a b)),
      ⋃ e ∈ {e : DVar X.Tau a b →₀ ℕ | e.degree ≤ n}, {(A.chiF a b N N')⁻¹ * derivAt0 G e}
  have hZ₀ : FinAlg Z₀ := by
    refine finAlg_biUnion Ta.finite_toSet fun N hN => finAlg_biUnion Tb.finite_toSet fun N' hN' =>
      finAlg_biUnion (Finset.finite_toSet _) fun c hc => ?_
    have hc' : c ∣ M := Nat.dvd_of_mem_divisors hc
    have hc0 : 0 < c := Nat.pos_of_mem_divisors hc
    refine finAlg_biUnion (finite_thInd A S N N' M c (hTa N hN) (hTb N' hN') hM hc0) ?_
    rintro _ ⟨x, hx, rfl⟩
    refine finAlg_biUnion (Finsupp.finite_of_degree_le n) fun e _ => finAlg_of_finite (Set.finite_singleton _) ?_
    rintro _ rfl
    exact hJ N N' c x ⟨hTa N hN, hTb N' hN', hc0, hc', hx⟩ e
  have h1 : FinAlg (Set.range A.cD) := finAlg_of_finite (Set.finite_range _) (by rintro _ ⟨τ, rfl⟩; exact hD τ)
  have h2 : FinAlg (⋃ τ ∈ (Set.univ : Set X.Tau), Set.range (X.embC A.σ₀ τ)) :=
    finAlg_biUnion Set.finite_univ fun τ _ => finAlg_range _
  refine ((hZ₀.union h1).union h2).closure.mono ?_
  set K₀ := Subfield.closure ((Z₀ ∪ Set.range A.cD) ∪ ⋃ τ ∈ (Set.univ : Set X.Tau), Set.range (X.embC A.σ₀ τ)) with hK₀
  have hemb : ∀ τ x, X.embC A.σ₀ τ x ∈ K₀ := fun τ x =>
    Subfield.subset_closure (Or.inr (Set.mem_biUnion (Set.mem_univ τ) ⟨x, rfl⟩))
  have hcD : ∀ τ, A.cD τ ∈ K₀ := fun τ => Subfield.subset_closure (Or.inl (Or.inr ⟨τ, rfl⟩))
  rintro _ ⟨N, N', c, x, e, hr, he, rfl⟩
  obtain ⟨N₀, hN₀, γ, rfl⟩ := hTa' N hr.1
  obtain ⟨N₀', hN₀', γ', rfl⟩ := hTb' N' hr.2.1
  obtain ⟨x₀, rfl⟩ : ∃ x₀ : HomE X.E a b, x = γ'.1.toLinearMap ∘ₗ x₀ ∘ₗ γ.1.symm.toLinearMap :=
    ⟨γ'.1.symm.toLinearMap ∘ₗ x ∘ₗ γ.1.toLinearMap, by ext v; simp⟩
  have hr₀ : InRange S M c N₀ N₀' x₀ :=
    ⟨hTa _ hN₀, hTb _ hN₀', hr.2.2.1, hr.2.2.2.1, (divLat_gmap_iff S M _ _ _ _ _).1 hr.2.2.2.2⟩
  have hth : A.thInd S (gmap γ.1 N₀) (gmap γ'.1 N₀') c (γ'.1.toLinearMap ∘ₗ x₀ ∘ₗ γ.1.symm.toLinearMap) =
      fun z => A.thInd S N₀ N₀' c x₀ (pullLin A γ.1 γ'.1 z) := funext (hT γ γ' N₀ N₀' c x₀ hr₀)
  have key : (A.chiF a b N₀ N₀')⁻¹ * derivAt0 (fun z => A.thInd S N₀ N₀' c x₀ (pullLin A γ.1 γ'.1 z)) e ∈ K₀ := by
    refine GlobalTheory.Mem.JetChain.derivAt0_comp_mem X.Tau a b n K₀ _ _ _ (indSmooth_of A a b S M hE N₀ N₀' c x₀ hr₀) ?_ ?_ e he
    · intro k τ i j
      show A.pullV a b γ.1 γ'.1 (coordX k) τ i j ∈ K₀
      unfold Amb.pullV
      refine sum_mem fun k' _ => sum_mem fun l _ => mul_mem (mul_mem (hemb _ _) ?_) (hemb _ _)
      unfold coordX
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    · intro e' he'
      refine Subfield.subset_closure (Or.inl (Or.inl ?_))
      refine Set.mem_biUnion hN₀ (Set.mem_biUnion hN₀' (Set.mem_biUnion (x := c) ?_ (Set.mem_biUnion ⟨x₀, hr₀.2.2.2.2, rfl⟩
        (Set.mem_biUnion (x := e') he'.le rfl))))
      exact Finset.mem_coe.2 (Nat.mem_divisors.2 ⟨hr₀.2.2.2.1, hM.ne'⟩)
  show _ ∈ K₀
  rw [hth, hC γ γ' N₀ N₀' hr₀.1 hr₀.2.1, jetC, mul_inv, mul_assoc, mul_left_comm (A.chiF a b N₀ N₀')⁻¹]
  refine mul_mem (inv_mem (mul_mem (zpow_mem (prod_mem fun τ _ => hemb _ _) _) (zpow_mem (prod_mem fun τ _ => hemb _ _) _)))
    (mul_mem (prod_mem fun k _ => pow_mem (hcD _) _) key)

end GlobalTheory.Mem.Col2.JetFin
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.hasDerivAt_gaussian_parameters_at_identity : ∀ (P Q : ℕ) (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ) (Z : Mat P Q) (g g' : ℝ → Mat P Q), g 0 = 1 → g' 0 = 1 → (∀ a b, HasDerivAt (fun t => g t a b) (Z a b) 0) → (∀ a b, HasDerivAt (fun t => g' t a b) (-Z a b) 0) → (∀ i j, HasDerivAt (fun t => matA (g t * baseY A) i j) (dA Z A i j) 0) ∧ (∀ l, HasDerivAt (fun t => linX (g t * baseY A) (g t *ᵥ baseV x) (baseF x ᵥ* g' t) l) (dX Z A x l) 0) ∧ HasDerivAt (fun t => scal (g t * baseY A) (g t *ᵥ baseV x) (baseF x ᵥ* g' t)) (dS Z A x) 0 := by
  first | exact @GlobalTheory.OscGauss.ParDer.par_deriv | exact GlobalTheory.OscGauss.ParDer.par_deriv | (intros; apply GlobalTheory.OscGauss.ParDer.par_deriv <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.Mem.Col2.IdxEx

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal

theorem nfMat_eq_qnf {E : Type} [Field E] (n c : ℕ) (q : E) (e : Fin c → ℤ) (z : Fin n → E) :
    nfMat n c q e z = GlobalTheory.QNF.nfMat n c q e z := by
  funext l s
  unfold nfMat GlobalTheory.QNF.nfMat
  by_cases hs : s.1 < n
  · simp [hs]
  · by_cases hls : l = s
    · subst hls
      simp [hs, _root_.Formalism.L2.Col.Loc.inX]
    · by_cases hn : s.1 = n
      · by_cases hl : l.1 < n
        · simp [hls, hn, hl, _root_.Formalism.L2.Col.Loc.inX]
        · simp [hls, hn, hl, _root_.Formalism.L2.Col.Loc.inX]
      · simp [hs, hls, hn]

theorem nf_matrix : ∀ (X : _root_.Formalism.L2.Col.Fields) (Pr : _root_.Formalism.L2.Col.Primes X) (R : Ranks) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), P ∉ Pr.vGs → ∀ h : _root_.Formalism.L2.Col.AutY X R j, GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm.NF Pr j P h → ∃ (e : Fin (_root_.Formalism.L2.Col.cOf R j) → ℤ) (z : Fin (R.N j) → X.E), (∀ i, -(j : ℤ) ≤ e i ∧ e i ≤ 0) ∧ (fun l : Fin (R.N j + _root_.Formalism.L2.Col.cOf R j) => if hl : l.1 < R.N j then z ⟨l.1, hl⟩ else 0) ∈ _root_.Formalism.L2.Col.lamYat (Pr := Pr) (R := R) j P ∧ (_root_.Formalism.L2.Col.lamYat (Pr := Pr) (R := R) j P).map (h.toLinearMap.restrictScalars (𝓞 X.E)) = (_root_.Formalism.L2.Col.lamYat (Pr := Pr) (R := R) j P).map ((Matrix.toLin' (nfMat (R.N j) (_root_.Formalism.L2.Col.cOf R j) (_root_.Formalism.L2.Col.qOf P : X.E) e z)).restrictScalars (𝓞 X.E)) := by
  intro X Pr R j P hP h hh
  obtain ⟨e, z, h1, h2, h3⟩ := (GlobalTheory.QNF.nf_iff_matNF X Pr R j P hP h).1 hh
  exact ⟨e, z, h1, h2, by rw [nfMat_eq_qnf]; exact h3⟩

end GlobalTheory.Mem.Col2.IdxEx

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta NumberField
open scoped TensorProduct

namespace GlobalTheory.RationalCountable

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem discrete_countable_GQ :
    ∀ (D : D7) (V : HSp D), DiscreteTopology (GQ V) ∧ Countable (GQ V) :=
  fun D V => ⟨GlobalTheory.RationalDiscrete.discreteTopology_GQ D V,
    Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram⟩

end GlobalTheory.RationalCountable
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MemberAdelicTop

theorem locallyCompact_secondCountable_t2 : ∀ (D : D7) (V : HSp D), LocallyCompactSpace (GA D V) ∧ SecondCountableTopology (GA D V) ∧ T2Space (GA D V) := fun D V =>
  GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary D.host.F D.host.E D.sp.cm.sig V.rank V.gram

end GlobalTheory.MemberAdelicTop
end
