module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Extension.Cotangent.BaseChange
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ProdSurjectiveGeometricPoints
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EndoLbIsoSymmetryHypothesisExtendNormalModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2757
public import Mathlib.RingTheory.Derivation.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2758
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle031
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.fibreProduct_affineOpen_closure_legs_eq_top : ∀ (Z Z' X X' : Scheme.{0}) (p : Z ⟶ X) (p' : Z' ⟶ X') (φ : Z' ⟶ Z) (g : X' ⟶ X), IsPullback φ p' p g → ∀ (U : X.affineOpens) (U' : X'.affineOpens), U'.1 ≤ g ⁻¹ᵁ U.1 → ∀ (O : Z.affineOpens), O.1 ≤ p ⁻¹ᵁ U.1 → IsAffineOpen (φ ⁻¹ᵁ O.1 ⊓ p' ⁻¹ᵁ U'.1) ∧ Subring.closure (Set.range (φ.appLE O.1 (φ ⁻¹ᵁ O.1 ⊓ p' ⁻¹ᵁ U'.1) inf_le_left).hom ∪ Set.range (p'.appLE U'.1 (φ ⁻¹ᵁ O.1 ⊓ p' ⁻¹ᵁ U'.1) inf_le_right).hom) = ⊤ := by
  first | exact @GlobalTheory.BaseChangeAffine.affine_and_closure_eq_top | exact GlobalTheory.BaseChangeAffine.affine_and_closure_eq_top | (intros; apply GlobalTheory.BaseChangeAffine.affine_and_closure_eq_top <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_derivation_fibreProduct_affine_compatible : ∀ (Z Z' X X' : Scheme.{0}) (p : Z ⟶ X) (p' : Z' ⟶ X') (φ : Z' ⟶ Z) (g : X' ⟶ X), IsPullback φ p' p g → ∀ (U : X.affineOpens) (U' : X'.affineOpens) (hU : U'.1 ≤ g ⁻¹ᵁ U.1) (D : Derivation ℤ Γ(X, U.1) Γ(X, U.1)) (D' : Derivation ℤ Γ(X', U'.1) Γ(X', U'.1)), (∀ r, D' ((g.appLE U.1 U'.1 hU).hom r) = (g.appLE U.1 U'.1 hU).hom (D r)) → ∀ (O : Z.affineOpens) (hO : O.1 ≤ p ⁻¹ᵁ U.1) (δ : Derivation ℤ Γ(Z, O.1) Γ(Z, O.1)), (∀ r, δ ((p.appLE U.1 O.1 hO).hom r) = (p.appLE U.1 O.1 hO).hom (D r)) → ∃ δ' : Derivation ℤ Γ(Z', φ ⁻¹ᵁ O.1 ⊓ p' ⁻¹ᵁ U'.1) Γ(Z', φ ⁻¹ᵁ O.1 ⊓ p' ⁻¹ᵁ U'.1), (∀ r, δ' ((p'.appLE U'.1 _ inf_le_right).hom r) = (p'.appLE U'.1 _ inf_le_right).hom (D' r)) ∧ ∀ f, δ' ((φ.appLE O.1 _ inf_le_left).hom f) = (φ.appLE O.1 _ inf_le_left).hom (δ f) := by
  first | exact @GlobalTheory.FibreDer.exists_der_fibre | exact GlobalTheory.FibreDer.exists_der_fibre | (intros; apply GlobalTheory.FibreDer.exists_der_fibre <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.EtaleAtDescent

open TensorProduct

theorem notMem_support_of_flat {B D M N : Type} [CommRing B] [CommRing D] [Algebra B D] [Module.Flat B D]
    [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N] [Module D N] [IsScalarTower B D N]
    (φ : M →ₗ[B] N) (hφ : Function.Injective (φ.liftBaseChange D)) (Q : PrimeSpectrum D)
    (hQ : Q ∉ Module.support D N) : PrimeSpectrum.comap (algebraMap B D) Q ∉ Module.support B M := by
  rw [Module.notMem_support_iff'] at hQ ⊢
  intro x
  by_contra hx
  push Not at hx
  obtain ⟨f, hf, hfx⟩ := hQ (φ x)
  have h0 : f ⊗ₜ[B] x = 0 := hφ (by simpa using hfx)
  have hex := Module.Flat.lTensor_exact D (LinearMap.exact_subtype_ker_map (LinearMap.toSpanSingleton B M x))
  obtain ⟨z, hz⟩ := (hex (f ⊗ₜ[B] 1)).1 (by simpa using h0)
  have key : ∀ z : D ⊗[B] LinearMap.ker (LinearMap.toSpanSingleton B M x),
      TensorProduct.rid B D (LinearMap.lTensor D (LinearMap.ker (LinearMap.toSpanSingleton B M x)).subtype z) ∈
        Q.asIdeal := by
    intro z
    induction z with
    | add a b ha hb => rw [map_add (f := _), map_add (f := _)]; exact Q.asIdeal.add_mem ha hb
    | tmul d r =>
      have hr : algebraMap B D r.1 ∈ Q.asIdeal := by
        by_contra h
        exact hx r.1 h (LinearMap.mem_ker.1 r.2)
      simpa [Algebra.smul_def] using Q.asIdeal.mul_mem_right d hr
  have := key z
  rw [hz] at this
  exact hf (by simpa using this)


attribute [local instance] Algebra.TensorProduct.rightAlgebra in
theorem mem_etaleLocus_of_flat {A B C : Type} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    [Module.Flat A C] (Q : PrimeSpectrum (C ⊗[A] B)) (hQ : Q ∈ Algebra.etaleLocus C (C ⊗[A] B)) :
    PrimeSpectrum.comap (algebraMap B (C ⊗[A] B)) Q ∈ Algebra.etaleLocus A B := by
  rw [Algebra.etaleLocus_eq_compl_support] at hQ ⊢
  haveI : Module.Flat B (C ⊗[A] B) :=
    Module.Flat.of_linearEquiv (Algebra.IsPushout.equiv A B C (C ⊗[A] B)).toLinearEquiv.symm
  refine ⟨notMem_support_of_flat (KaehlerDifferential.map A C B (C ⊗[A] B)) ?_ Q hQ.1,
    notMem_support_of_flat (Algebra.H1Cotangent.map A C B (C ⊗[A] B)) ?_ Q hQ.2⟩
  · have hc : (KaehlerDifferential.tensorKaehlerEquivBase A C B (C ⊗[A] B) : _ → _) =
        (KaehlerDifferential.map A C B (C ⊗[A] B)).liftBaseChange (C ⊗[A] B) ∘
          (Algebra.IsPushout.cancelBaseChange A C B (C ⊗[A] B) Ω[B⁄A]).symm := by
      funext z
      induction z with
      | add x y hx hy => simp only [Function.comp_apply, map_add (f := _)] at hx hy ⊢; rw [hx, hy]
      | tmul s m =>
        rw [KaehlerDifferential.tensorKaehlerEquivBase_tmul, Function.comp_apply,
          Algebra.IsPushout.cancelBaseChange_symm_tmul, LinearMap.liftBaseChange_tmul, algebraMap_smul]
    have hi := (KaehlerDifferential.tensorKaehlerEquivBase A C B (C ⊗[A] B)).injective
    rw [hc] at hi
    exact hi.of_comp_right (LinearEquiv.surjective _)
  · have hc : (Algebra.tensorH1CotangentOfFlat A B C : _ → _) =
        (Algebra.H1Cotangent.map A C B (C ⊗[A] B)).liftBaseChange (C ⊗[A] B) ∘
          (Algebra.IsPushout.cancelBaseChange A C B (C ⊗[A] B) (Algebra.H1Cotangent A B)).symm := by
      funext z
      induction z with
      | add x y hx hy => simp only [Function.comp_apply, map_add (f := _)] at hx hy ⊢; rw [hx, hy]
      | tmul s m =>
        rw [Algebra.tensorH1CotangentOfFlat_tmul, Function.comp_apply, Algebra.IsPushout.cancelBaseChange_symm_tmul,
          LinearMap.liftBaseChange_tmul, algebraMap_smul]
    have hi := (Algebra.tensorH1CotangentOfFlat A B C).injective
    rw [hc] at hi
    exact hi.of_comp_right (LinearEquiv.surjective _)


attribute [local instance] Algebra.TensorProduct.rightAlgebra in
theorem exists_etale_spec {A B C : Type} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    [Module.Flat A C] [Algebra.FinitePresentation A B] (W : (Spec (.of (C ⊗[A] B))).Opens)
    (p : Spec (.of (C ⊗[A] B))) (hp : p ∈ W)
    (hW : Etale (W.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap C (C ⊗[A] B))))) :
    ∃ V : (Spec (.of B)).Opens, Spec.map (CommRingCat.ofHom (algebraMap B (C ⊗[A] B))) p ∈ V ∧
      Etale (V.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
  obtain ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, hpf, hf⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hp W.isOpen
  let j := Spec.map (CommRingCat.ofHom (algebraMap (C ⊗[A] B) (Localization.Away f)))
  have hj : Set.range j ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    refine subset_trans ?_ hf
    exact (PrimeSpectrum.localization_away_comap_range (Localization.Away f) f).le
  have h1 : Etale (IsOpenImmersion.lift W.ι j hj ≫ W.ι ≫
      Spec.map (CommRingCat.ofHom (algebraMap C (C ⊗[A] B)))) := inferInstance
  rw [IsOpenImmersion.lift_fac_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq,
    HasRingHomProperty.Spec_iff (P := @Etale), CommRingCat.hom_ofHom, RingHom.etale_algebraMap] at h1
  have h2 := mem_etaleLocus_of_flat p (Algebra.basicOpen_subset_etaleLocus_iff_etale.2 h1 hpf)
  rw [Algebra.mem_etaleLocus_iff] at h2
  obtain ⟨g, hg, hE⟩ := Algebra.exists_etale_of_isEtaleAt (R := A)
    (PrimeSpectrum.comap (algebraMap B (C ⊗[A] B)) p).asIdeal
  let i := Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away g)))
  refine ⟨i.opensRange, ?_, ?_⟩
  · exact (PrimeSpectrum.localization_away_comap_range (Localization.Away g) g).ge hg
  · have h3 : Etale (i ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq,
        HasRingHomProperty.Spec_iff (P := @Etale), CommRingCat.hom_ofHom, RingHom.etale_algebraMap]
      exact hE
    rw [← i.isoOpensRange_inv_comp, Category.assoc]
    infer_instance

theorem exists_etale_of_isAffine {U T S : Scheme.{0}} [IsAffine S] (τ : U ⟶ S) (h : T ⟶ S)
    [LocallyOfFinitePresentation τ] [Flat h] (W : (pullback τ h).Opens) (p : ↥(pullback τ h)) (hp : p ∈ W)
    (hW : Etale (W.ι ≫ pullback.snd τ h)) : ∃ V : U.Opens, pullback.fst τ h p ∈ V ∧ Etale (V.ι ≫ τ) := by
  obtain ⟨B, i, _, q, hq⟩ := U.exists_Spec_apply_eq (pullback.fst τ h p)
  obtain ⟨C, k, _, t, ht⟩ := T.exists_Spec_apply_eq (pullback.snd τ h p)
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (i ≫ τ ≫ S.isoSpec.hom)
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (k ≫ h ≫ S.isoSpec.hom)
  letI := φ.hom.toAlgebra
  letI := ψ.hom.toAlgebra
  letI : Algebra B (C ⊗[Γ(S, ⊤)] B) := Algebra.TensorProduct.rightAlgebra
  haveI : Algebra.FinitePresentation Γ(S, ⊤) B := by
    have : LocallyOfFinitePresentation (Spec.map φ) := by rw [hφ]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).1 this
  haveI : Module.Flat Γ(S, ⊤) C := by
    have : Flat (Spec.map ψ) := by rw [hψ]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @Flat)).1 this
  have hpb : IsPullback (Spec.map (CommRingCat.ofHom (algebraMap B (C ⊗[Γ(S, ⊤)] B))))
      (Spec.map (CommRingCat.ofHom (algebraMap C (C ⊗[Γ(S, ⊤)] B)))) (Spec.map φ) (Spec.map ψ) :=
    (isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct Γ(S, ⊤) C B)).flip
  let m := pullback.map (Spec.map φ) (Spec.map ψ) τ h i k S.isoSpec.inv (by simp [hφ]) (by simp [hψ])
  have hm : IsOpenImmersion m := inferInstance
  have hpm : p ∈ Set.range m := by
    rw [Scheme.Pullback.range_map]
    exact ⟨⟨q, hq⟩, ⟨t, ht⟩⟩
  let j := hpb.isoPullback.hom ≫ m
  have j1 : j ≫ pullback.fst τ h = Spec.map (CommRingCat.ofHom (algebraMap B (C ⊗[Γ(S, ⊤)] B))) ≫ i := by
    simp only [j, m, pullback.map, Category.assoc, pullback.lift_fst, IsPullback.isoPullback_hom_fst_assoc]
  have j2 : j ≫ pullback.snd τ h = Spec.map (CommRingCat.ofHom (algebraMap C (C ⊗[Γ(S, ⊤)] B))) ≫ k := by
    simp only [j, m, pullback.map, Category.assoc, pullback.lift_snd, IsPullback.isoPullback_hom_snd_assoc]
  obtain ⟨p', rfl⟩ : ∃ p', j p' = p := by
    obtain ⟨p₀, rfl⟩ := hpm
    obtain ⟨p₁, rfl⟩ := hpb.isoPullback.hom.surjective p₀
    exact ⟨p₁, by simp [j]⟩
  have h1 : Etale ((j ∣_ W) ≫ W.ι ≫ pullback.snd τ h) := inferInstance
  rw [morphismRestrict_ι_assoc, j2, ← Category.assoc] at h1
  have h2 := Etale.of_comp ((j ⁻¹ᵁ W).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap C (C ⊗[Γ(S, ⊤)] B)))) k
  obtain ⟨V, hV, hE⟩ := exists_etale_spec (j ⁻¹ᵁ W) p' hp h2
  refine ⟨i ''ᵁ V, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, j1, Scheme.Hom.comp_apply]
    exact ⟨_, hV, rfl⟩
  · have hE' : Etale (V.ι ≫ Spec.map φ) := hE
    have e : (i ''ᵁ V).ι ≫ τ = (i.isoImage V).inv ≫ (V.ι ≫ Spec.map φ) ≫ S.isoSpec.inv := by
      simp [hφ]
    rw [e]
    infer_instance

theorem etale_nhds_of_flat_baseChange : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (U : Over (Sp R)) (g : ℕ) (τ : U.left ⟶ 𝔸(Fin g; Sp R)), LocallyOfFiniteType U.hom → τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = U.hom → ∀ (T : Scheme.{0}) (h : T ⟶ 𝔸(Fin g; Sp R)), Flat h → ∀ (W : (pullback τ h).Opens) (p : ↥(pullback τ h)), p ∈ W → Etale (W.ι ≫ pullback.snd τ h) → ∃ V : U.left.Opens, pullback.fst τ h p ∈ V ∧ Etale (V.ι ≫ τ) := by
  intro R _ _ _ hR U g τ hU hτ T h hh W p hp hW
  haveI := hR.1
  haveI : LocallyOfFiniteType (τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R)) := by rw [hτ]; exact hU
  haveI : LocallyOfFiniteType τ := locallyOfFiniteType_of_comp τ (𝔸(Fin g; Sp R) ↘ Sp R)
  haveI : IsLocallyNoetherian 𝔸(Fin g; Sp R) := LocallyOfFiniteType.isLocallyNoetherian (𝔸(Fin g; Sp R) ↘ Sp R)
  exact exists_etale_of_isAffine τ h W p hp hW

end GlobalTheory.EtaleAtDescent
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.EtLift

theorem exists_etale_to_affineSpace {k : CommRingCat.{0}} {X : Scheme.{0}} (f : X ⟶ Spec k) [Smooth f]
    (x : X) : ∃ (V : X.Opens) (n : ℕ) (u : V.toScheme ⟶ 𝔸(Fin n; Spec k)), x ∈ V ∧ Etale u ∧
      u ≫ (𝔸(Fin n; Spec k) ↘ Spec k) = V.ι ≫ f := by
  obtain ⟨U, hU, V, hV, hxV, e, hs⟩ := Smooth.exists_isStandardSmooth f x
  obtain ⟨n, g, hgC, hg⟩ := RingHom.IsStandardSmooth.exists_etale_mvPolynomial hs
  have hmap : Etale (AffineSpace.map (Fin n) hU.fromSpec) :=
    MorphismProperty.of_isPullback (P := @Etale) (AffineSpace.isPullback_map (n := Fin n) hU.fromSpec).flip inferInstance
  have hSg : Etale (Spec.map (CommRingCat.ofHom g)) := HasRingHomProperty.Spec_iff.mpr hg
  refine ⟨V, n, hV.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom g) ≫ (AffineSpace.SpecIso (Fin n) _).inv ≫
    AffineSpace.map (Fin n) hU.fromSpec, hxV, inferInstance, ?_⟩
  simp only [Category.assoc, AffineSpace.map_over, AffineSpace.SpecIso_inv_over_assoc, ← Spec.map_comp_assoc,
    ← CommRingCat.ofHom_comp, hgC]
  rw [CommRingCat.ofHom_hom, IsAffineOpen.SpecMap_appLE_fromSpec f hU hV e, hV.isoSpec_hom_fromSpec_assoc]

theorem exists_surjective_appTop {Y P : Scheme.{0}} (j : Y ⟶ P) [IsImmersion j] (y : Y) (U : Y.Opens)
    (hy : y ∈ U) : ∃ W : P.Opens, j y ∈ W ∧ j ⁻¹ᵁ W ≤ U ∧ Function.Surjective (j ∣_ W).appTop := by
  obtain ⟨O, hO, hOU⟩ := j.isEmbedding.isInducing.isOpen_iff.mp U.isOpen
  have hyC : j y ∈ (j.coborderRange : Set P) := subset_coborder ⟨y, rfl⟩
  have hyO : j y ∈ O := by
    rw [← Set.mem_preimage, hOU]; exact hy
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWs⟩ := P.isBasis_affineOpens.exists_subset_of_mem_open
    (show j y ∈ O ∩ (j.coborderRange : Set P) from ⟨hyO, hyC⟩) (hO.inter j.coborderRange.isOpen)
  refine ⟨W, hxW, ?_, ?_⟩
  · intro z hz
    show z ∈ (U : Set Y)
    rw [← hOU]
    exact (hWs hz).1
  · have : IsAffine W := hW
    have key : Set.range (j ∣_ W) = (Scheme.Opens.ι W) ⁻¹' closure (Set.range j) := by
      ext x
      constructor
      · rintro ⟨z, rfl⟩
        apply subset_closure
        refine ⟨(j ⁻¹ᵁ W).ι z, ?_⟩
        rw [← Scheme.Hom.comp_apply, ← morphismRestrict_ι, Scheme.Hom.comp_apply]
      · intro hx
        have hxW' : (Scheme.Opens.ι W) x ∈ (W : Set P) := by
          rw [← Scheme.Opens.range_ι]; exact ⟨x, rfl⟩
        have hxC : (Scheme.Opens.ι W) x ∈ (j.coborderRange : Set P) := (hWs hxW').2
        have h3 : (Scheme.Opens.ι W) x ∈ closure (Set.range j) ∩ coborder (Set.range j) := ⟨hx, hxC⟩
        rw [closure_inter_coborder] at h3
        obtain ⟨z, hz⟩ := h3
        have hzW : z ∈ j ⁻¹ᵁ W := by
          show j z ∈ W; rw [hz]; exact hxW'
        obtain ⟨z', hz'⟩ : z ∈ Set.range (j ⁻¹ᵁ W).ι := by
          rw [Scheme.Opens.range_ι]; exact hzW
        refine ⟨z', (Scheme.Opens.ι W).isOpenEmbedding.injective ?_⟩
        rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply, hz', hz]
    have : IsClosedImmersion (j ∣_ W) := by
      refine .of_isPreimmersion _ ?_
      rw [key]
      exact isClosed_closure.preimage (Scheme.Opens.ι W).continuous
    exact (IsClosedImmersion.isAffine_surjective_of_isAffine (j ∣_ W)).2

end GlobalTheory.Mum.EtLift


open GlobalTheory.Mum.EtLift in
theorem GlobalTheory.Mum.exists_etale_coords_lift_immersion : ∀ (R : Type) [CommRing R] [IsLocalRing R] (N : ℕ) (Y : Over (Sp (ResidueField R))), Smooth Y.hom → ∀ (j : Y.left ⟶ PSpace R N), IsImmersion j → j ≫ PSpace.str R N = Y.hom ≫ spMap (residue R) → ∀ y : Y.left, ∃ (W0 : (PSpace R N).Opens) (g : ℕ) (τ0 : W0.toScheme ⟶ 𝔸(Fin g; Sp R)) (O : Y.left.Opens) (e : O.toScheme ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) (spMap (residue R))), y ∈ O ∧ (O : Set Y.left) ⊆ j ⁻¹' W0 ∧ τ0 ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = W0.ι ≫ PSpace.str R N ∧ Etale e ∧ e ≫ pullback.snd _ _ = O.ι ≫ Y.hom ∧ ∀ (T : Scheme.{0}) (t : T ⟶ O.toScheme) (w : T ⟶ W0.toScheme), w ≫ W0.ι = t ≫ O.ι ≫ j → t ≫ e ≫ pullback.fst _ _ = w ≫ τ0 := by
  intro R _ _ N Y hsm j hj hjs y
  have : Smooth Y.hom := hsm
  obtain ⟨V, g, u, hyV, hu, huo⟩ := exists_etale_to_affineSpace (k := CommRingCat.of (ResidueField R)) Y.hom y
  have huo' : u ≫ (𝔸(Fin g; Sp (ResidueField R)) ↘ Sp (ResidueField R)) = V.ι ≫ Y.hom := huo
  obtain ⟨W, hyW, hWV, hsurj⟩ := exists_surjective_appTop j y V hyV
  let u' : (j ⁻¹ᵁ W).toScheme ⟶ 𝔸(Fin g; Sp (ResidueField R)) := Y.left.homOfLE hWV ≫ u
  have hu' : Etale u' := by
    have : Etale (Y.left.homOfLE hWV) := inferInstance
    exact inferInstanceAs (Etale (Y.left.homOfLE hWV ≫ u))
  choose s hs using fun i : Fin g => hsurj (u'.appTop (AffineSpace.coord (Sp (ResidueField R)) i))
  let τ0 : W.toScheme ⟶ 𝔸(Fin g; Sp R) := AffineSpace.homOfVector (W.ι ≫ PSpace.str R N) s
  have hP := AffineSpace.isPullback_map (n := Fin g) (spMap (residue R))
  have hfst : u' ≫ AffineSpace.map (Fin g) (spMap (residue R)) = (j ∣_ W) ≫ τ0 := by
    apply AffineSpace.hom_ext
    · simp only [Category.assoc, AffineSpace.map_over, τ0, AffineSpace.homOfVector_over, u']
      rw [reassoc_of% huo', Scheme.homOfLE_ι_assoc, ← Category.assoc (j ∣_ W), morphismRestrict_ι,
        Category.assoc, hjs]
    · intro i
      simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.map_appTop_coord, τ0,
        AffineSpace.homOfVector_appTop_coord]
      exact (hs i).symm
  refine ⟨W, g, τ0, j ⁻¹ᵁ W, u' ≫ hP.isoPullback.hom, hyW, fun z hz => hz,
    AffineSpace.homOfVector_over _ _, inferInstance, ?_, ?_⟩
  · simp only [Category.assoc, IsPullback.isoPullback_hom_snd, u']
    rw [huo', Scheme.homOfLE_ι_assoc]
  · intro T t w hw
    have hfst' : Y.left.homOfLE hWV ≫ u ≫ AffineSpace.map (Fin g) (spMap (residue R)) = (j ∣_ W) ≫ τ0 := by
      rw [← Category.assoc]; exact hfst
    rw [Category.assoc, Category.assoc, IsPullback.isoPullback_hom_fst]
    rw [hfst', ← Category.assoc]
    congr 1
    rw [← cancel_mono W.ι, Category.assoc, morphismRestrict_ι, hw]
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem geometricallyConnected_of_isPullback_of_surjective :
    ∀ (R : Type) [CommRing R] (S : Scheme.{0}) (π : S ⟶ Sp R), LocallyOfFiniteType π → Surjective π →
    ∀ (G' : Over S) (G : Over (Sp R)) (β : G'.left ⟶ G.left), IsPullback β G'.hom G.hom π →
    GeometricallyConnected G'.hom → GeometricallyConnected G.hom := by
  intro R _ S π hlft hsurj G' G β hpb hG'
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ y ↦ ?_⟩
  let jK : Spec (.of (AlgebraicClosure K)) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
  obtain ⟨t, ht⟩ := GlobalTheory.GeomSurj.exists_lift_of_surjective (Ω := AlgebraicClosure K) π (jK ≫ y)
  have hct : ConnectedSpace ↥(pullback G'.hom t) :=
    pullback_of_geometrically hG'.geometrically_connectedSpace _ t
  have hP : IsPullback (pullback.fst G'.hom t ≫ β) (pullback.snd G'.hom t) G.hom (t ≫ π) :=
    (IsPullback.of_hasPullback G'.hom t).paste_horiz hpb
  rw [← ht] at hP
  have hc' : ConnectedSpace ↥(pullback G.hom (jK ≫ y)) :=
    hP.isoPullback.hom.homeomorph.connectedSpace_iff.mp hct
  have hjK : Surjective jK := ⟨fun z ↦ by
    obtain ⟨w⟩ : Nonempty ↥(Spec (.of (AlgebraicClosure K))) := inferInstance
    exact ⟨w, Subsingleton.elim _ _⟩⟩
  have hc'' : ConnectedSpace ↥(pullback (pullback.snd G.hom y) jK) :=
    (pullbackLeftPullbackSndIso G.hom y jK).hom.homeomorph.connectedSpace_iff.mpr hc'
  exact (pullback.fst (pullback.snd G.hom y) jK).surjective.connectedSpace
    (pullback.fst (pullback.snd G.hom y) jK).continuous

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem lbIso_of_generic_local : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R], ∀ (H : Over (Sp R)) [Smooth H.hom] [GeometricallyIntegral H.hom] (e : Sp R ⟶ H.left), e ≫ H.hom = 𝟙 _ → ∀ L L' : LB H.left, L.IsLB → L'.IsLB → LBIso (L.pull (pullback.fst H.hom (jK R))) (L'.pull (pullback.fst H.hom (jK R))) → LBIso L L' := by
  intro R _ _ _ _ _ H _ _ e he L L' hL hL' h
  have hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp R) := GlobalTheory.Published.SemiAbelianHomExtension.isNormalScheme_spec R
  have : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have : Flat (jK R) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (nonZeroDivisors R))
  have : IsDominant (jK R) := ReciprocityTheory.ChartRestriction.G.DVR.isDominant_jK
  have : QuasiCompact (jK R) := inferInstance
  refine (GlobalTheory.CechPic.cls_eq_iff hL hL').1 (GlobalTheory.ZH.EndoExtend.pic_ext (jK R) hn H e he ?_ ?_)
  · exact (GlobalTheory.DualOpen.pic_sp_local_eq_zero R _).trans
      (GlobalTheory.DualOpen.pic_sp_local_eq_zero R _).symm
  · exact (GlobalTheory.CechPic.cls_eq_iff (pull_isLB hL _) (pull_isLB hL' _)).2 h

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option autoImplicit false

namespace GlobalTheory.OpenGeomIrr

theorem geometricallyIrreducible_comp_of_isOpenImmersion : ∀ (T W X : Scheme.{0}) (j : W ⟶ X), IsOpenImmersion j →
    ∀ (f : X ⟶ T), GeometricallyIrreducible f → Surjective (j ≫ f) → GeometricallyIrreducible (j ≫ f) := by
  intro T W X j hj f hf hs
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x => ?_⟩
  have h₁ : IrreducibleSpace ↥(Limits.pullback f x) :=
    GeometricallyIrreducible.geometrically_irreducibleSpace _ _ _ (.of_hasPullback _ _)
  have hne : Nonempty ↥(Limits.pullback (j ≫ f) x) := by
    obtain ⟨p⟩ : Nonempty ↥(Spec (.of K)) := inferInstance
    obtain ⟨z, -⟩ := (Limits.pullback.snd (j ≫ f) x).surjective p
    exact ⟨z⟩
  let e := pullbackRightPullbackFstIso f x j
  have hne' : Nonempty ↥(Limits.pullback j (Limits.pullback.fst f x)) := ⟨e.inv hne.some⟩
  have h₂ : IrreducibleSpace ↥(Limits.pullback j (Limits.pullback.fst f x)) :=
    (Limits.pullback.snd j (Limits.pullback.fst f x)).isOpenEmbedding.irreducibleSpace
  exact e.hom.homeomorph.irreducibleSpace_iff.1 h₂

end GlobalTheory.OpenGeomIrr
end
