module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1119
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle122
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle678
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1296
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle435
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2054
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2610
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2607
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2622
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2369
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2442
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2441
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2490
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2623
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Flat.EquationalCriterion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NormCover

open GlobalTheory.BplusDescent

theorem genericPoint_mem {X : Scheme.{0}} [IsIntegral X] {U : X.Opens} (hU : (U : Set X).Nonempty) :
    genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).2 (by simpa using hU)

theorem isFinite_fromNormalization_fieldPt {X : Scheme.{0}} [IsIntegral X] [GlobalTheory.IsNormalScheme X]
    [IsLocallyNoetherian X] {L : Type} [Field L] [CharZero L]
    (ψ : X.presheaf.stalk (genericPoint X) ⟶ .of L) (hψ : ψ.hom.Finite) :
    IsFinite (fieldPt ψ).fromNormalization := by
  refine ⟨fun U hU => ?_⟩
  by_cases hne : (U : Set X).Nonempty
  · have hη := genericPoint_mem hne
    haveI : Nonempty U := hne.to_subtype
    letI : Algebra Γ(X, U) Γ((fieldPt ψ).normalization, (fieldPt ψ).fromNormalization ⁻¹ᵁ U) :=
      ((fieldPt ψ).fromNormalization.app U).hom.toAlgebra
    letI : Algebra Γ((fieldPt ψ).normalization, (fieldPt ψ).fromNormalization ⁻¹ᵁ U) L :=
      (normFun ψ hη).hom.toAlgebra
    letI : Algebra Γ(X, U) L := (X.presheaf.germ U _ hη ≫ ψ).hom.toAlgebra
    letI : Algebra X.functionField L := ψ.hom.toAlgebra
    haveI : IsScalarTower Γ(X, U) Γ((fieldPt ψ).normalization, (fieldPt ψ).fromNormalization ⁻¹ᵁ U) L :=
      .of_algebraMap_eq' (congrArg CommRingCat.Hom.hom (app_normFun ψ hη)).symm
    haveI := functionField_isFractionRing_of_isAffineOpen X U hU
    haveI : IsScalarTower Γ(X, U) X.functionField L := .of_algebraMap_eq' rfl
    haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    haveI : FiniteDimensional X.functionField L := hψ
    haveI : CharZero X.functionField := ψ.hom.charZero
    haveI : IsIntegralClosure Γ((fieldPt ψ).normalization, (fieldPt ψ).fromNormalization ⁻¹ᵁ U) Γ(X, U) L :=
      ⟨(normFun_spec ψ hη hU).1, fun {x} => ((normFun_spec ψ hη hU).2 x).symm⟩
    exact IsIntegralClosure.finite Γ(X, U) X.functionField L _
  · haveI : Subsingleton Γ((fieldPt ψ).normalization, (fieldPt ψ).fromNormalization ⁻¹ᵁ U) := by
      refine subsingleton_of_forall_eq 0 fun s => ?_
      rw [← basicOpen_eq_bot_iff]
      exact eq_bot_iff.2 fun z hz => (hne ⟨_, ((fieldPt ψ).normalization.basicOpen_le s hz :)⟩).elim
    letI := ((fieldPt ψ).fromNormalization.app U).hom.toAlgebra
    change Module.Finite _ _
    infer_instance

end GlobalTheory.NormCover

namespace GlobalTheory.NormCover

open GlobalTheory.BplusDescent

theorem exists_normalization_model : ∀ (k Ω : Type) [CommRing k] [IsNoetherianRing k] [Field Ω] [CharZero Ω] [Algebra k Ω]
    (M : RatModel k Ω) (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [Algebra k Ω'] [IsScalarTower k Ω Ω']
    [FiniteDimensional Ω Ω'], Geo.Tor.IsNormalScheme M.Z → ∃ (M' : RatModel k Ω') (π : M'.Z ⟶ M.Z),
      Geo.Tor.IsNormalScheme M'.Z ∧ IsFinite π ∧ M'.pt ≫ π = spMap (algebraMap Ω Ω') ≫ M.pt := by
  intro k Ω _ _ _ _ _ M Ω' _ _ _ _ _ hN
  haveI : GlobalTheory.IsNormalScheme M.Z := GlobalTheory.IsNormalScheme.of_pred hN
  haveI := M.lft
  haveI := M.sep
  haveI := M.qc
  haveI : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  haveI : CharZero Ω' := charZero_of_injective_algebraMap (algebraMap Ω Ω').injective
  let ρ : M.Z.presheaf.stalk (genericPoint M.Z) ⟶ .of Ω :=
    M.Z.presheaf.stalkSpecializes (M.pt_specializes (IsLocalRing.closedPoint Ω) (genericPoint M.Z)) ≫
      Scheme.stalkClosedPointTo M.pt
  have hρ : fieldPt ρ = M.pt := by
    simp only [fieldPt, ρ, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk M.pt
  let ψ : M.Z.presheaf.stalk (genericPoint M.Z) ⟶ .of Ω' := ρ ≫ CommRingCat.ofHom (algebraMap Ω Ω')
  have hψ : fieldPt ψ = spMap (algebraMap Ω Ω') ≫ M.pt := by
    rw [← hρ]
    simp only [fieldPt, ψ, Spec.map_comp, Category.assoc]
  have hρs : Function.Surjective ρ.hom := by
    intro x
    obtain ⟨U, f, hU, rfl⟩ := M.onto x
    have hη := genericPoint_mem hU
    refine ⟨M.Z.presheaf.germ U _ hη f, ?_⟩
    have key : ∀ (g : Sp Ω ⟶ M.Z) (_ : fieldPt ρ = g) (e : ⊤ ≤ g ⁻¹ᵁ U),
        g.appLE U ⊤ e ≫ (Scheme.ΓSpecIso (.of Ω)).hom = M.Z.presheaf.germ U _ hη ≫ ρ := by
      rintro _ rfl e
      exact fieldPt_appLE ρ hη
    have e := M.top_le_preimage_pt hU
    rw [valF, dite_eq_left e]
    exact (congrArg (fun g => g.hom f) (key M.pt hρ e)).symm
  have hψfin : ψ.hom.Finite :=
    RingHom.Finite.comp (RingHom.finite_algebraMap.2 inferInstance) (RingHom.Finite.of_surjective ρ.hom hρs)
  haveI hfin : IsFinite (fieldPt ψ).fromNormalization := isFinite_fromNormalization_fieldPt ψ hψfin

  have hgen : Set.range (fieldPt ψ).toNormalization = {genericPoint (fieldPt ψ).normalization} := by
    have hc : ∀ w : Sp Ω', w = IsLocalRing.closedPoint Ω' := fun w =>
      Subsingleton.elim (α := PrimeSpectrum Ω') _ _
    have hr : Set.range (fieldPt ψ).toNormalization = {(fieldPt ψ).toNormalization (IsLocalRing.closedPoint Ω')} := by
      ext z
      constructor
      · rintro ⟨w, rfl⟩
        rw [hc w]
        rfl
      · rintro rfl
        exact ⟨_, rfl⟩
    have hd : closure (Set.range (fieldPt ψ).toNormalization) = Set.univ := (fieldPt ψ).toNormalization.denseRange.closure_range
    rw [hr] at hd ⊢
    have hg : IsGenericPoint ((fieldPt ψ).toNormalization (IsLocalRing.closedPoint Ω')) ⊤ := hd
    rw [hg.eq (genericPoint_spec (fieldPt ψ).normalization)]
  have hpts : (fieldPt ψ).toNormalization ≫ (fieldPt ψ).fromNormalization ≫ M.s = spMap (algebraMap k Ω') := by
    rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization, hψ, Category.assoc, M.pt_s, spMap, spMap,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have honto : ∀ x : Ω', ∃ (U : (fieldPt ψ).normalization.Opens) (f : Γ((fieldPt ψ).normalization, U)), (U : Set (fieldPt ψ).normalization).Nonempty ∧
      valF (fieldPt ψ).toNormalization U f = x := by
    intro x
    obtain ⟨U, hU, hηU, -⟩ := exists_isAffineOpen_mem_and_subset (x := genericPoint M.Z) (U := ⊤) trivial
    haveI : Nonempty U := ⟨⟨_, hηU⟩⟩
    letI : Algebra Γ(M.Z, U) Ω' := (M.Z.presheaf.germ U _ hηU ≫ ψ).hom.toAlgebra
    letI : Algebra M.Z.functionField Ω' := ψ.hom.toAlgebra
    haveI := functionField_isFractionRing_of_isAffineOpen M.Z U hU
    haveI : IsScalarTower Γ(M.Z, U) M.Z.functionField Ω' := .of_algebraMap_eq' rfl
    haveI : FiniteDimensional M.Z.functionField Ω' := hψfin
    obtain ⟨⟨a, ha⟩, hax⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (nonZeroDivisors Γ(M.Z, U)) x
      (Algebra.IsIntegral.isIntegral (R := M.Z.functionField) x)
    have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
    have hηV : genericPoint M.Z ∈ M.Z.basicOpen a := by
      refine genericPoint_mem ?_
      rw [Set.nonempty_iff_ne_empty]
      exact fun h => ha0 ((basicOpen_eq_bot_iff a).1 (SetLike.coe_injective h))
    have hV : IsAffineOpen (M.Z.basicOpen a) := hU.basicOpen a
    let r := M.Z.presheaf.map (homOfLE (M.Z.basicOpen_le a)).op
    letI : Algebra Γ(M.Z, U) Γ(M.Z, M.Z.basicOpen a) := r.hom.toAlgebra
    letI : Algebra Γ(M.Z, M.Z.basicOpen a) Ω' := (M.Z.presheaf.germ _ _ hηV ≫ ψ).hom.toAlgebra
    haveI : IsScalarTower Γ(M.Z, U) Γ(M.Z, M.Z.basicOpen a) Ω' := .of_algebraMap_eq' (by
      have e : r ≫ M.Z.presheaf.germ _ _ hηV = M.Z.presheaf.germ U _ hηU := TopCat.Presheaf.germ_res _ _ _ _
      change (M.Z.presheaf.germ U _ hηU ≫ ψ).hom = (r ≫ M.Z.presheaf.germ _ _ hηV ≫ ψ).hom
      simp only [← e, Category.assoc])
    have hunit : IsUnit (r.hom a) := M.Z.toRingedSpace.isUnit_res_basicOpen a
    have hxV : IsIntegral Γ(M.Z, M.Z.basicOpen a) x := by
      have h1 : IsIntegral Γ(M.Z, M.Z.basicOpen a) (algebraMap Γ(M.Z, U) Ω' a * x) := by
        have := hax.tower_top (A := Γ(M.Z, M.Z.basicOpen a))
        rwa [Submonoid.smul_def, Algebra.smul_def] at this
      have h2 : x = algebraMap Γ(M.Z, M.Z.basicOpen a) Ω' (↑hunit.unit⁻¹ : Γ(M.Z, M.Z.basicOpen a)) *
          (algebraMap Γ(M.Z, U) Ω' a * x) := by
        rw [IsScalarTower.algebraMap_apply Γ(M.Z, U) Γ(M.Z, M.Z.basicOpen a) Ω' a, ← _root_.mul_assoc, ← map_mul]
        have : (↑hunit.unit⁻¹ : Γ(M.Z, M.Z.basicOpen a)) * algebraMap Γ(M.Z, U) Γ(M.Z, M.Z.basicOpen a) a = 1 :=
          hunit.val_inv_mul
        rw [this, map_one, _root_.one_mul]
      rw [h2]
      exact isIntegral_algebraMap.mul h1
    obtain ⟨c, hc⟩ := ((normFun_spec ψ hηV hV).2 x).2 hxV
    have hW : ⊤ ≤ (fieldPt ψ).toNormalization ⁻¹ᵁ ((fieldPt ψ).fromNormalization ⁻¹ᵁ M.Z.basicOpen a) := by
      intro w _
      show (fieldPt ψ).fromNormalization ((fieldPt ψ).toNormalization w) ∈ M.Z.basicOpen a
      rw [← Scheme.Hom.comp_apply, Scheme.Hom.toNormalization_fromNormalization, fieldPt_apply]
      exact hηV
    refine ⟨(fieldPt ψ).fromNormalization ⁻¹ᵁ M.Z.basicOpen a, c,
      ⟨_, hW (x := IsLocalRing.closedPoint Ω') trivial⟩, ?_⟩
    rw [valF, dite_eq_left hW]
    exact hc
  let M' : RatModel k Ω' :=
    { Z := (fieldPt ψ).normalization
      s := (fieldPt ψ).fromNormalization ≫ M.s
      sep := inferInstance
      lft := inferInstance
      qc := inferInstance
      pt := (fieldPt ψ).toNormalization
      pt_s := hpts
      gen := hgen
      onto := honto }
  refine ⟨M', (fieldPt ψ).fromNormalization, (GlobalTheory.IsNormalScheme.normalization_of_isIntegral (fieldPt ψ)).pred _, hfin, ?_⟩
  exact (Scheme.Hom.toNormalization_fromNormalization (fieldPt ψ)).trans hψ

end GlobalTheory.NormCover
end
end

section

open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.GoodEtale

theorem hart_of_flat : ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (B : Type) [CommRing B] [Algebra A B] [Module.Flat A B], GlobalTheory.GoodEtale.Hart A B B := by
  intro A _ _ _ _ B _ _ _ a ha m hm
  classical
  let I : Ideal A := Ideal.comap (algebraMap A B) ((Ideal.span {algebraMap A B a}).colon {m})
  have hI : ∀ u, u ∈ I ↔ ∃ m' : B, algebraMap A B u * m = algebraMap A B a * m' := by
    intro u
    simp only [I, Ideal.mem_comap, Submodule.mem_colon_singleton, smul_eq_mul,
      Ideal.mem_span_singleton']
    constructor
    · rintro ⟨c, hc⟩; exact ⟨c, by rw [← hc, mul_comm]⟩
    · rintro ⟨c, hc⟩; exact ⟨c, by rw [hc, mul_comm]⟩
  obtain ⟨S, hS⟩ := (IsNoetherian.noetherian I : I.FG)
  have hm' : ∀ s : S, ∃ m' : B, algebraMap A B s * m = algebraMap A B a * m' := fun s =>
    (hI s).1 (hS ▸ Submodule.subset_span s.2)
  choose m' hm'' using hm'
  let f : (S → A) →ₗ[A] A × (S → A) :=
    LinearMap.prod (∑ s : S, (LinearMap.proj s).smulRight (s : A)) (a • LinearMap.id)
  let x : A × (S → A) →ₗ[A] B := (LinearMap.fst A A (S → A)).smulRight m -
    ∑ s : S, ((LinearMap.proj s).comp (LinearMap.snd A A (S → A))).smulRight (m' s)
  have hxf : x ∘ₗ f = 0 := by
    apply LinearMap.ext
    intro c
    have e : ∀ s : S, (c s * s) • m = (a * c s) • m' s := by
      intro s
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_mul, mul_assoc, hm'' s]; ring
    simp [x, f, Finset.sum_smul, e]
  obtain ⟨k, α, y, hxy, hαf⟩ := Module.Flat.exists_factorization_of_comp_eq_zero_of_free hxf
  set v := α ((1 : A), (0 : S → A)) with hvdef
  have hsv : ∀ s : S, ∀ j, (s : A) * v j ∈ Ideal.span {a} := by
    intro s j
    have e : f (Pi.single s 1) = (s : A) • ((1 : A), (0 : S → A)) + a • ((0 : A), Pi.single s 1) := by
      ext t
      · simp [f, Pi.single_apply]
      · simp [f]
    have h0 : α (f (Pi.single s 1)) = 0 := by
      simpa using congrArg (fun g => g (Pi.single s 1)) hαf
    rw [e, map_add (f := _), map_smul, map_smul] at h0
    have h1 := congrArg (fun w => w j) h0
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, Finsupp.coe_zero,
      Pi.zero_apply] at h1
    rw [Ideal.mem_span_singleton']
    exact ⟨-(α ((0 : A), Pi.single s 1)) j, by rw [← hvdef] at h1; linear_combination -h1⟩
  have hv : ∀ j, v j ∈ Ideal.span {a} := by
    intro j
    apply GlobalTheory.PrincipalHartogs.mem_span_singleton_of_forall_height_le_one
    intro q hq h1
    obtain ⟨u, hu, m'', h⟩ := hm q hq h1
    refine ⟨u, hu, ?_⟩
    have huI : u ∈ I := (hI u).2 ⟨m'', by simpa [smul_eq_mul] using h⟩
    have hle : I ≤ (Ideal.span {a}).colon {v j} := by
      rw [← hS, Submodule.span_le]
      intro s hs
      rw [SetLike.mem_coe, Submodule.mem_colon_singleton, smul_eq_mul]
      exact hsv ⟨s, hs⟩ j
    have := hle huI
    rwa [Submodule.mem_colon_singleton, smul_eq_mul] at this
  choose z hz using fun j => Ideal.mem_span_singleton'.mp (hv j)
  refine ⟨y (Finsupp.equivFunOnFinite.symm z), ?_⟩
  have hv' : v = a • Finsupp.equivFunOnFinite.symm z := by
    ext j; simp [← hz j, mul_comm]
  have hmx : m = x ((1 : A), (0 : S → A)) := by simp [x]
  rw [hmx, hxy, LinearMap.comp_apply, ← hvdef, hv', map_smul, Algebra.smul_def, smul_eq_mul]

end GlobalTheory.GoodEtale
end

section

open IsLocalRing
open scoped TensorProduct

namespace GlobalTheory.GoodEtaleSection

theorem hartRep_one (A R : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [CommRing R] [Algebra A R] (ρ : R →+* A) (hρ : ρ.comp (algebraMap A R) = RingHom.id A)
    (t : R) (hker : RingHom.ker ρ = Ideal.span {t}) (a : A) (r : R)
    (h : ∀ p : Ideal A, p.IsPrime → p.height ≤ 1 →
      ∃ u : A, u ∉ p ∧ ∃ m' : R, algebraMap A R u * r - algebraMap A R a * m' ∈ Ideal.span {t}) :
    ∃ r' : R, r - algebraMap A R a * r' ∈ Ideal.span {t} := by
  have hρa : ∀ b, ρ (algebraMap A R b) = b := fun b => by simpa using congrArg (fun f => f b) hρ
  have hmem : ρ r ∈ Ideal.span {a} := by
    refine GlobalTheory.PrincipalHartogs.mem_span_singleton_of_forall_height_le_one a (ρ r) fun p hp hp1 => ?_
    obtain ⟨u, hu, m', hm⟩ := h p hp hp1
    refine ⟨u, hu, Ideal.mem_span_singleton.2 ⟨ρ m', ?_⟩⟩
    rw [← hker, RingHom.mem_ker, map_sub, map_mul, map_mul, hρa, hρa, sub_eq_zero] at hm
    exact hm
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.1 hmem
  refine ⟨algebraMap A R b, ?_⟩
  rw [← hker, RingHom.mem_ker, map_sub, map_mul, hρa, hρa, hb, sub_self]

theorem hartRep (A R : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [CommRing R] [Algebra A R] (ρ : R →+* A) (hρ : ρ.comp (algebraMap A R) = RingHom.id A)
    (t : R) (hker : RingHom.ker ρ = Ideal.span {t}) (ht : t ∈ nonZeroDivisors R) (a : A) (ha : a ≠ 0) :
    ∀ n : ℕ, ∀ r : R, (∀ p : Ideal A, p.IsPrime → p.height ≤ 1 →
      ∃ u : A, u ∉ p ∧ ∃ m' : R, algebraMap A R u * r - algebraMap A R a * m' ∈ Ideal.span {t ^ n}) →
    ∃ r' : R, r - algebraMap A R a * r' ∈ Ideal.span {t ^ n} := by
  have hρa : ∀ b, ρ (algebraMap A R b) = b := fun b => by simpa using congrArg (fun f => f b) hρ
  have ht0 : ρ t = 0 := by rw [← RingHom.mem_ker, hker]; exact Ideal.mem_span_singleton_self t
  intro n
  induction n with
  | zero => intro r _; exact ⟨0, by simp⟩
  | succ n ih =>
    intro r hr
    obtain ⟨x, hx⟩ := hartRep_one A R ρ hρ t hker a r fun p hp hp1 => by
      obtain ⟨u, hu, m', hm⟩ := hr p hp hp1
      exact ⟨u, hu, m', Ideal.span_singleton_le_span_singleton.2 (dvd_pow_self t n.succ_ne_zero) hm⟩
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.1 hx
    obtain ⟨y', hy'⟩ := ih y fun p hp hp1 => by
      obtain ⟨u, hu, m', hm⟩ := hr p hp hp1
      obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.1 hm
      have key : t * (algebraMap A R u * y) - algebraMap A R a * (m' - algebraMap A R u * x)
          = t ^ (n + 1) * q := by
        linear_combination hq - (algebraMap A R u) * hy
      have h2 : a * ρ (m' - algebraMap A R u * x) = 0 := by
        have := congrArg ρ key
        rw [map_sub] at this
        simp only [map_mul, map_pow, ht0, hρa, zero_mul, zero_sub, zero_pow n.succ_ne_zero,
          neg_eq_zero] at this
        exact this
      have h3 : m' - algebraMap A R u * x ∈ Ideal.span {t} := by
        rw [← hker, RingHom.mem_ker]
        exact (mul_eq_zero.1 h2).resolve_left ha
      obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.1 h3
      refine ⟨u, hu, z, Ideal.mem_span_singleton.2 ⟨q, ?_⟩⟩
      have h4 : t * (algebraMap A R u * y - algebraMap A R a * z - t ^ n * q) = 0 := by
        rw [hz] at key
        linear_combination key
      exact sub_eq_zero.1 ((mul_left_mem_nonZeroDivisors_eq_zero_iff ht).1 h4)
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton.1 hy'
    refine ⟨x + t * y', Ideal.mem_span_singleton.2 ⟨s, ?_⟩⟩
    linear_combination hy + t * hs

theorem hart_quot : ∀ (A R : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [CommRing R] [Algebra A R] (ρ : R →+* A), ρ.comp (algebraMap A R) = RingHom.id A →
    ∀ t : R, RingHom.ker ρ = Ideal.span {t} → t ∈ nonZeroDivisors R →
    ∀ n : ℕ, GlobalTheory.GoodEtale.Hart A R (R ⧸ Ideal.span {t} ^ n) := by
  intro A R _ _ _ _ _ _ ρ hρ t hker ht n a ha m hm
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective m
  obtain ⟨r', hr'⟩ := hartRep A R ρ hρ t hker ht a ha n r fun p hp hp1 => by
    obtain ⟨u, hu, m', hm'⟩ := hm p hp hp1
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective m'
    refine ⟨u, hu, s, ?_⟩
    rw [Algebra.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, ← map_mul,
      Ideal.Quotient.eq, Ideal.span_singleton_pow] at hm'
    exact hm'
  refine ⟨Ideal.Quotient.mk _ r', ?_⟩
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq, Ideal.span_singleton_pow]
  exact hr'

end GlobalTheory.GoodEtaleSection
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotMove
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.Grid Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Mult MeasureTheory

noncomputable section

namespace GlobalTheory.BotMove

theorem rig_move {D : D7} {V : HSp D} (rr : Rig V) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (g : GA D V)
    (hr : rr.Is) (hΛ : IsSelfDualC V Λ) (hm : GlobalTheory.FinPl.Moves V g rr.Λ Λ (fun _ => True)) :
    Rig.Is (⟨Λ, Lev.finE V g * rr.β, rr.s, rr.B⟩ : Rig V) :=
  ⟨hΛ, GlobalTheory.Core.Mi.FrameMove.isFrame_of_moves D V g rr.Λ Λ rr.β hm hr.2.1, hr.2.2⟩

theorem moveTri_is : ∀ {D : D7} {T : Type} {A A' WW : HSp D} (Y : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (α β : T → ((AE D)ˣ →* Circle)) (νH : T → HChar D.host.E) (S : T → Finset (Formalism.L2.DIV.Pl D.host.E)),
    Y.Is ψ θ α β νH S →
    ∀ (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E))
      (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)),
    IsSelfDualC A ΛA → IsSelfDualC A' ΛA' → IsSelfDualC WW ΛW →
    ∀ g ∈ GfC A, ∀ g' ∈ GfC A', ∀ h ∈ GfC WW,
    GlobalTheory.FinPl.Moves A g Y.rA.Λ ΛA (fun _ => True) → GlobalTheory.FinPl.Moves A' g' Y.rA'.Λ ΛA' (fun _ => True) →
    GlobalTheory.FinPl.Moves WW h Y.rW.Λ ΛW (fun _ => True) →
    ∀ (t₀ : T) (r r' : T → ℂ), (∀ t, r t ≠ 0 ∧ r' t ≠ 0) →
    (∀ t, Y.ω t (g, h) Y.vac = r t • Y.ω t₀ (g, h) Y.vac) → (∀ t, Y.ω' t (g', h) Y.vac' = r' t • Y.ω' t₀ (g', h) Y.vac') →
    (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').Is ψ θ α β νH S := by
  intro D T A A' WW Y ψ θ α β νH S hY ΛA ΛA' ΛW hA hA' hW g hg g' hg' h hh mA mA' mW t₀ r r' hr hv hv'
  exact ⟨hY.rank, rig_move _ _ _ hY.rigA hA mA, rig_move _ _ _ hY.rigA' hA' mA', rig_move _ _ _ hY.rigW hW mW, hY.weil,
    hY.weil', GlobalTheory.T.movedVacuum_negHom_eq_vacuum_movedLattices Y ψ θ α β νH S hY ΛA ΛA' ΛW hA hA' hW g hg g' hg' h hh mA mA' mW t₀ r r' hr hv hv', GlobalTheory.T.movedVacuum_hom_eq_vacuum_movedLattices Y ψ θ α β νH S hY ΛA ΛA' ΛW hA hA' hW g hg g' hg' h hh mA mA' mW t₀ r r' hr hv hv', hY.idem, hY.expo, GlobalTheory.T.movedFiniteDatum_negHom_eq_standardPair_first Y ψ θ α β νH S hY ΛA ΛA' ΛW hA hA' hW g hg g' hg' h hh mA mA' mW t₀ r r' hr hv hv',
    GlobalTheory.T.translated_finite_datum_eq_standardPairSecondMember Y ψ θ α β νH S hY ΛA ΛA' ΛW hA hA' hW g hg g' hg' h hh mA mA' mW t₀ r r' hr hv hv', GlobalTheory.T.haar_fundamentalDomain_rightTranslate_unitary _ _ g hY.meas.1 hY.meas.2, GlobalTheory.T.haar_fundamentalDomain_rightTranslate_unitary _ _ g' hY.meas'.1 hY.meas'.2⟩

end GlobalTheory.BotMove

end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogKSDiv

theorem exists_genKS_local : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → FnAlgClosed (Xo := Xo) (c := c) → ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)], ∀ (x : X₀ TF.Y Z) (φ : c.F →+* (X₀ TF.Y Z).presheaf.stalk x) (f : GlobalTheory.ShFam.EigFrame TF.Y φ ((show Sp ((X₀ TF.Y Z).presheaf.stalk x) ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk x) ≫ (barComp TF.Y Z).ι)), (show Sp ((X₀ TF.Y Z).presheaf.stalk x) ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk x) ≫ s₀ TF.Y Z = spMap φ → ∃ D : Fin Dw.dim → GlobalTheory.LogKSDiv.GenDer TF Z, GlobalTheory.LogKSDiv.GenKS TF Z (fun τ k => spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField)) ≫ f.v τ k) D ∧ ∀ (U : (X₀ TF.Y Z).Opens) (ω : TopForm.FormsOn (s₀ TF.Y Z) Dw.dim U), TopForm.IsFrame ω → ∀ hx : x ∈ U, RegAt x (GlobalTheory.LogKSDiv.topPair (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)) D (formOf U (gen_mem hx) ω)) ∧ (UnitAt x (GlobalTheory.LogKSDiv.topPair (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)) D (formOf U (gen_mem hx) ω)) ↔ x ∈ (j₀ TF.Y Z).opensRange) := by
  intro E _ _ _ H Dw l Xo c TF Z _ _ _ _ x φ f hφ
  obtain ⟨U, hU, hxU, ρ, n, e, v, φU, hρ, htan, hbas, heig, hw⟩ := GlobalTheory.T.exists_spread_eigenFrame_lieAlgebra_toroidalComponent E H Dw l Xo c TF Z x φ f hφ
  obtain ⟨ε, b, hKS⟩ := GlobalTheory.T.exists_logKS_symPair_basis_alt E H Dw l Xo c TF U n e v φU htan hbas heig
  obtain ⟨D, hD⟩ := GlobalTheory.T.exists_logVectorField_extend_functionFieldDerivation E H Dw l Xo c TF Z U hU ρ hρ (fun j => b j)
  exact ⟨D, ⟨U, hU, ρ, n, e, v, ε, fun j => b j, hρ, htan, hbas, fun τ i => hw τ i, hKS, hD⟩,
    fun U' ω hω hx => GlobalTheory.T.exists_logVectorField_topForm_pairing_regular_at_point E H Dw l Xo c TF Z x U hU hxU ρ hρ b D hD U' ω hω hx⟩

end GlobalTheory.LogKSDiv
end
end
