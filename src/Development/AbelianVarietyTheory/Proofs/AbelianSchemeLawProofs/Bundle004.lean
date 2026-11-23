module

public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Factorization.Induction
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open scoped TensorProduct

theorem nonempty_equiv_prod_of_exact_of_projective {A : Type*} [CommRing A] {K F M : Type*}
    [AddCommGroup K] [Module A K] [AddCommGroup F] [Module A F] [AddCommGroup M] [Module A M]
    [Module.Projective A M] (g : K →ₗ[A] F) (f : F →ₗ[A] M) (hg : Function.Injective g)
    (hf : Function.Surjective f) (h : Function.Exact g f) : Nonempty (F ≃ₗ[A] K × M) := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  exact ⟨(h.splitSurjectiveEquiv hg ⟨s, hs⟩).1⟩

theorem isStablyFree_baseChange_of_hasProjectiveDimensionLE (R : Type) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (A : Type) [CommRing A] [Algebra R A] [Module.Flat R A]
    (n : ℕ) : ∀ (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M],
      HasProjectiveDimensionLE (ModuleCat.of R M) n → Module.Projective A (A ⊗[R] M) →
        Module.IsStablyFree A (A ⊗[R] M) := by
  induction n with
  | zero =>
    intro M _ _ _ h _
    have h1 : Projective (ModuleCat.of R M) :=
      (projective_iff_hasProjectiveDimensionLE_zero _).2 h
    have h2 : Module.Projective R M := (IsProjective.iff_projective M).2 h1
    have h3 : Module.Free R M := Module.free_of_flat_of_isLocalRing
    infer_instance
  | succ n ih =>
    intro M _ _ _ h hp
    obtain ⟨m, f, hf⟩ := Module.Finite.exists_fin' R M
    have hS := LinearMap.shortExact_shortComplexKer hf
    have hK : HasProjectiveDimensionLE (ModuleCat.of R (LinearMap.ker f)) n := by
      have hP : Projective (ModuleCat.of R (Fin m → R)) := inferInstance
      exact (hS.hasProjectiveDimensionLT_X₃_iff n hP).1 h
    have hex : Function.Exact ((LinearMap.ker f).subtype.baseChange A) (f.baseChange A) :=
      lTensor_exact A f.exact_subtype_ker_map hf
    have hinj : Function.Injective ((LinearMap.ker f).subtype.baseChange A) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ (LinearMap.ker f).injective_subtype
    have hsurj : Function.Surjective (f.baseChange A) := LinearMap.lTensor_surjective A hf
    obtain ⟨e⟩ := nonempty_equiv_prod_of_exact_of_projective _ _ hinj hsurj hex
    have hfree : Module.Free A ((A ⊗[R] LinearMap.ker f) × (A ⊗[R] M)) := Module.Free.of_equiv e
    have hKp : Module.Projective A (A ⊗[R] LinearMap.ker f) :=
      Module.Projective.of_split (LinearMap.inl A _ (A ⊗[R] M)) (LinearMap.fst A _ _)
        (LinearMap.ext fun _ ↦ rfl)
    have hKs := ih (LinearMap.ker f) hK hKp
    obtain ⟨N, _, _, _, _, _⟩ := Module.IsStablyFree.exist_free_prod A (A ⊗[R] LinearMap.ker f)
    have : Module.Free A ((A ⊗[R] M) × ((A ⊗[R] LinearMap.ker f) × N)) :=
      Module.Free.of_equiv (M := ((A ⊗[R] LinearMap.ker f) × (A ⊗[R] M)) × N)
        (((LinearEquiv.prodComm A _ _).prodCongr (LinearEquiv.refl A N)).trans
          (LinearEquiv.prodAssoc A _ _ _))
    exact Module.IsStablyFree.of_free_prod A _ ((A ⊗[R] LinearMap.ker f) × N)

section cofactor

variable {A : Type*} [CommRing A] {M N : Type*} [AddCommGroup M] [Module A M]
  [AddCommGroup N] [Module A N] {n : ℕ}

theorem exists_surjective_exteriorPower_prod (bN : Module.Basis (Fin n) A N) :
    ∃ φ : ⋀[A]^(n + 1) (M × N) →ₗ[A] M, Function.Surjective φ := by
  let c : M × N →ₗ[A] (M × N) [⋀^Fin n]→ₗ[A] M :=
    { toFun := fun x ↦ (bN.det.compLinearMap (LinearMap.snd A M N)).smulRight x.1
      map_add' := fun x y ↦ AlternatingMap.ext fun _ ↦ by simp
      map_smul' := fun c x ↦ AlternatingMap.ext fun _ ↦ by simp [smul_smul, mul_comm] }
  refine ⟨exteriorPower.alternatingMapLinearEquiv (AlternatingMap.alternatizeUncurryFin c),
    fun m ↦ ⟨exteriorPower.ιMulti A (n + 1) (Fin.cons (m, 0) fun i ↦ (0, bN i)), ?_⟩⟩
  simp [c, AlternatingMap.alternatizeUncurryFin_apply, Fin.sum_univ_succ, Module.Basis.det_self]

end cofactor

theorem isPrincipal_of_isStablyFree {A : Type} [CommRing A] (J : Ideal A) [Module.Finite A J]
    [Module.IsStablyFree A J] : J.IsPrincipal := by
  rcases subsingleton_or_nontrivial A with _ | _
  · rw [Subsingleton.elim J ⊥]
    exact bot_isPrincipal
  obtain ⟨N, _, _, _, _, _⟩ := Module.IsStablyFree.exist_free_prod A J
  let n := Module.finrank A N
  have hp : Module.finrank A (J × N) ≤ n + 1 := by
    have := LinearMap.finrank_le_finrank_of_injective
      (f := J.subtype.prodMap (LinearMap.id : N →ₗ[A] N))
      (Function.Injective.prodMap J.injective_subtype Function.injective_id)
    rwa [Module.finrank_prod (M := A), Module.finrank_self, add_comm] at this
  have h1 : Module.finrank A (⋀[A]^(n + 1) (J × N)) ≤ 1 := by
    rw [exteriorPower.finrank_eq]
    simpa using Nat.choose_le_choose (n + 1) hp
  obtain ⟨v, hv⟩ := finrank_le_one_iff.1 h1
  obtain ⟨φ, hφ⟩ := exists_surjective_exteriorPower_prod (M := J) (Module.finBasis A N)
  refine ⟨(φ v : A), le_antisymm (fun y hy ↦ ?_) ?_⟩
  · obtain ⟨w, hw⟩ := hφ ⟨y, hy⟩
    obtain ⟨c, rfl⟩ := hv w
    rw [map_smul] at hw
    exact Submodule.mem_span_singleton.2 ⟨c, congrArg Subtype.val hw⟩
  · rw [Submodule.span_singleton_le_iff_mem]
    exact (φ v).2

theorem isPrincipal_map_away_of_hasProjectiveDimensionLE :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsDomain R] (x : R) (R' : Type) [CommRing R'] [Algebra R R'] [IsLocalization.Away x R'] (I : Ideal R) (n : ℕ), HasProjectiveDimensionLE (ModuleCat.of R I) n → Module.Projective R' (I.map (algebraMap R R')) → (I.map (algebraMap R R')).IsPrincipal := by
  intro R _ _ _ _ x R' _ _ _ I n h hp
  have hflat : Module.Flat R R' := IsLocalization.flat R' (Submonoid.powers x)
  have hb : IsBaseChange R' (Algebra.idealMap R' I) :=
    IsLocalizedModule.isBaseChange (Submonoid.powers x) R' _
  have hp' : Module.Projective R' (R' ⊗[R] I) := Module.Projective.of_equiv hb.equiv.symm
  have hs := isStablyFree_baseChange_of_hasProjectiveDimensionLE R R' n I h hp'
  have := Module.IsStablyFree.equiv hb.equiv
  have := Module.Finite.equiv hb.equiv
  exact isPrincipal_of_isStablyFree _

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FlatFibreInjective

open TensorProduct

theorem one_tmul_ne_zero_of_domain {A P k : Type} [CommRing A] [IsDomain A] [AddCommGroup P]
    [Module A P] [Field k] [Algebra A k] (hinj : Function.Injective (algebraMap A k)) (y : P)
    (hy : ∀ a : A, a • y = 0 → a = 0) : (1 : k) ⊗ₜ[A] y ≠ 0 := by
  intro h1
  letI : Algebra (FractionRing A) k := (IsFractionRing.lift hinj).toAlgebra
  haveI : IsScalarTower A (FractionRing A) k :=
    IsScalarTower.of_algebraMap_eq (fun a => (IsFractionRing.lift_algebraMap hinj a).symm)
  haveI : Module.Flat A (FractionRing A) := IsLocalization.flat _ (nonZeroDivisors A)
  haveI : Module.Free (FractionRing A) k := Module.Free.of_divisionRing _ _
  haveI : Module.Flat (FractionRing A) k := Module.Flat.of_free
  haveI : Module.Flat A k := Module.Flat.trans _ (FractionRing A) _
  have hi : Function.Injective (LinearMap.toSpanSingleton A P y) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    exact hy
  have h2 : (1 : k) ⊗ₜ[A] (1 : A) = 0 := by
    apply Module.Flat.lTensor_preserves_injective_linearMap (M := k) _ hi
    rw [LinearMap.lTensor_tmul, LinearMap.toSpanSingleton_apply, one_smul, map_zero, h1]
  have h3 := congrArg (TensorProduct.rid A k) h2
  rw [TensorProduct.rid_tmul, one_smul, map_zero] at h3
  exact one_ne_zero h3

theorem one_tmul_ne_zero {R₀ P k : Type} [CommRing R₀] [AddCommGroup P] [Module R₀ P]
    [Field k] [Algebra R₀ k] (p : Ideal R₀) (hk : ∀ a, algebraMap R₀ k a = 0 ↔ a ∈ p)
    (hP : Module.IsTorsionBySet R₀ P p) (y : P) (hy : ∀ a : R₀, a • y = 0 → a ∈ p) :
    (1 : k) ⊗ₜ[R₀] y ≠ 0 := by
  intro h
  have hker : p = RingHom.ker (algebraMap R₀ k) := by
    ext a; simp [RingHom.mem_ker, hk]
  haveI : p.IsPrime := hker ▸ RingHom.ker_isPrime _
  letI : Module (R₀ ⧸ p) P := hP.module
  haveI : IsScalarTower R₀ (R₀ ⧸ p) P := hP.isScalarTower
  letI : Algebra (R₀ ⧸ p) k :=
    (Ideal.Quotient.lift p (algebraMap R₀ k) (fun a ha => (hk a).2 ha)).toAlgebra
  haveI : IsScalarTower R₀ (R₀ ⧸ p) k := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hinj : Function.Injective (algebraMap (R₀ ⧸ p) k) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact Ideal.Quotient.eq_zero_iff_mem.2 ((hk a).1 ha)
  refine one_tmul_ne_zero_of_domain (A := R₀ ⧸ p) hinj y ?_ ?_
  · intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hy a ha)
  · have := congrArg (TensorProduct.mapOfCompatibleSMul (R₀ ⧸ p) R₀ R₀ k P) h
    rwa [TensorProduct.mapOfCompatibleSMul_tmul, map_zero] at this

theorem one_tmul_eq_zero {R₀ M C₀ C₁ k : Type} [CommRing R₀] [AddCommGroup M] [Module R₀ M]
    [AddCommGroup C₀] [Module R₀ C₀] [AddCommGroup C₁] [Module R₀ C₁]
    [Field k] [Algebra R₀ k] (φ : C₀ →ₗ[R₀] C₁) (hφ : Function.Injective (φ.baseChange k))
    (y : M ⊗[R₀] C₀) (hy : φ.lTensor M y = 0) : (1 : k) ⊗ₜ[R₀] y = 0 := by
  obtain ⟨g, hg⟩ := (φ.baseChange k).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 hφ)
  have key : ∀ z : M ⊗[R₀] C₀,
      TensorProduct.leftComm R₀ M k C₀ ((g.restrictScalars R₀).lTensor M
        ((TensorProduct.mk R₀ k C₁ 1).lTensor M (φ.lTensor M z))) = (1 : k) ⊗ₜ[R₀] z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul m c =>
      have := LinearMap.congr_fun hg ((1 : k) ⊗ₜ[R₀] c)
      simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearMap.id_apply] at this
      simp [this]
    | add a b ha hb => simp only [map_add (f := _), ha, hb, tmul_add]
  rw [← key, hy]
  simp

theorem exists_of_torsion {R₀ N C : Type} [CommRing R₀] [AddCommGroup N] [Module R₀ N]
    [AddCommGroup C] [Module R₀ C] [Module.Flat R₀ C] (p : Ideal R₀) (hp : p.FG)
    (x : N ⊗[R₀] C) (hx : ∀ a ∈ p, a • x = 0) :
    ∃ y, (Submodule.torsionBySet R₀ N p).subtype.rTensor C y = x := by
  classical
  obtain ⟨s, rfl⟩ := hp
  let g : N →ₗ[R₀] (s → N) := LinearMap.pi fun a => (a : R₀) • LinearMap.id
  have hex : Function.Exact (Submodule.torsionBySet R₀ N (Ideal.span (s : Set R₀))).subtype g := by
    rw [LinearMap.exact_iff, Submodule.range_subtype, ← Submodule.torsionBySet_eq_torsionBySet_span]
    ext n
    simp [g, funext_iff, LinearMap.mem_ker]
  have h := Module.Flat.rTensor_exact C hex x
  refine h.1 ?_
  apply (TensorProduct.piLeft R₀ C (fun _ : s => N)).injective
  have key : ∀ z : N ⊗[R₀] C, ∀ a : s,
      TensorProduct.piLeft R₀ C (fun _ : s => N) (g.rTensor C z) a = (a : R₀) • z := by
    intro z a
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul n c => simp [g, smul_tmul']
    | add u v hu hv => simp only [map_add (f := _), Pi.add_apply, hu, hv, smul_add]
  funext a
  rw [key, hx _ (Ideal.subset_span a.2)]
  simp

theorem injective_baseChange :
    ∀ (R₀ R C₀ C₁ : Type) [CommRing R₀] [IsNoetherianRing R₀] [CommRing R] [Algebra R₀ R]
      [AddCommGroup C₀] [Module R₀ C₀] [AddCommGroup C₁] [Module R₀ C₁] [Module.Flat R₀ C₀]
      [Module.Flat R₀ C₁] (φ : C₀ →ₗ[R₀] C₁),
      (∀ (k : Type) [Field k] [Algebra R k] [Algebra R₀ k] [IsScalarTower R₀ R k],
        Function.Injective (φ.baseChange k)) → Function.Injective (φ.baseChange R) := by
  intro R₀ R C₀ C₁ _ _ _ _ _ _ _ _ _ _ φ H
  change Function.Injective (φ.lTensor R)
  rw [← LinearMap.ker_eq_bot]
  by_contra hne
  haveI : Nontrivial (LinearMap.ker (φ.lTensor R)) := Submodule.nontrivial_iff_ne_bot.2 hne
  obtain ⟨p, hp⟩ := associatedPrimes.nonempty R₀ (LinearMap.ker (φ.lTensor R))
  rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff] at hp
  obtain ⟨hp, ⟨x, hx0⟩, hx⟩ := hp
  have hann : ∀ a : R₀, a • x = 0 ↔ a ∈ p := by
    intro a
    rw [hx]
    simp [Submodule.mem_colon_singleton]
  let M := Submodule.torsionBySet R₀ R p
  obtain ⟨y, rfl⟩ : ∃ y, M.subtype.rTensor C₀ y = x :=
    exists_of_torsion p (IsNoetherian.noetherian p) x (fun a ha => (hann a).2 ha)
  have hy0 : φ.lTensor M y = 0 := by
    apply Module.Flat.rTensor_preserves_injective_linearMap (M := C₁) M.subtype M.injective_subtype
    rw [map_zero, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
      ← LinearMap.lTensor_comp_rTensor]
    exact hx0
  have hkill : ∀ a : R₀, (∀ m : M, a • m = 0) → ∀ z : M ⊗[R₀] C₀, a • z = 0 := by
    intro a ha z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul m c => rw [smul_tmul', ha, zero_tmul]
    | add u v hu hv => rw [smul_add, hu, hv, add_zero]
  have hy : ∀ a : R₀, a • y = 0 → a ∈ p := by
    intro a ha
    rw [← hann, ← map_smul, ha, map_zero]
  have hcm : (p.map (algebraMap R₀ R)).comap (algebraMap R₀ R) = p := by
    refine le_antisymm ?_ Ideal.le_comap_map
    intro a ha
    refine hy a (hkill a (fun m => ?_) y)
    have hle : p.map (algebraMap R₀ R) ≤ LinearMap.ker (LinearMap.toSpanSingleton R R m) := by
      rw [Ideal.map_le_iff_le_comap]
      intro b hb
      have := (Submodule.mem_torsionBySet_iff _ _).1 m.2 ⟨b, hb⟩
      simpa [Algebra.smul_def] using this
    have := hle ha
    apply Subtype.ext
    simpa [Algebra.smul_def] using this
  obtain ⟨q, hq, hqp⟩ := (Ideal.comap_map_eq_self_iff_of_isPrime p).1 hcm
  refine one_tmul_ne_zero (k := q.ResidueField) p ?_ ?_ y hy
    (one_tmul_eq_zero φ (H q.ResidueField) y hy0)
  · intro a
    rw [IsScalarTower.algebraMap_apply R₀ R q.ResidueField, Ideal.algebraMap_residueField_eq_zero,
      ← hqp]
    rfl
  · intro z a
    refine hkill a (fun m => Subtype.ext ?_) z
    exact (Submodule.mem_torsionBySet_iff _ _).1 m.2 a

end GlobalTheory.FlatFibreInjective
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace SerreTorsion

variable {E : Type} [Ring E]

theorem one_add_pow_expand (x : E) (n : ℕ) :
    ∃ y : E, (1 + x) ^ n = 1 + n • x + n.choose 2 • x ^ 2 + x ^ 3 * y := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨y, hy⟩ := ih
    refine ⟨n.choose 2 • (1 : E) + y * (1 + x), ?_⟩
    have hc : (n + 1).choose 2 = n + n.choose 2 := by
      rw [Nat.choose_succ_succ' n 1, Nat.choose_one_right]
    rw [pow_succ, hy, hc]
    simp only [add_mul, mul_add, _root_.one_mul, _root_.mul_one, smul_mul_assoc, mul_smul_comm, add_smul,
      one_smul, pow_succ, pow_zero, _root_.mul_assoc]
    abel

theorem one_add_smul_pow_expand (c : ℕ) (ψ : E) (n : ℕ) :
    ∃ z : E, (1 + c • ψ) ^ n = 1 + c • (n • ψ + (n.choose 2 * c) • ψ ^ 2 + (c ^ 2) • z) := by
  obtain ⟨y, hy⟩ := one_add_pow_expand (c • ψ) n
  refine ⟨ψ ^ 3 * y, ?_⟩
  rw [hy, smul_pow, smul_pow, smul_mul_assoc]
  module

theorem step (htf : ∀ (n : ℕ) (x : E), n ≠ 0 → n • x = 0 → x = 0) {q c l : ℕ} (hq : q.Prime)
    (hl : l.Prime) (hc0 : c ≠ 0) (hqc : q ∣ c) (h2 : q = 2 → 4 ∣ c) (ψ : E)
    (h : (1 + c • ψ) ^ l = 1) : ∃ y : E, ψ = q • y := by
  obtain ⟨z, hz⟩ := one_add_smul_pow_expand c ψ l
  rw [h] at hz
  have h0 := htf c _ hc0 (left_eq_add.mp hz)
  obtain ⟨d, rfl⟩ := hqc
  by_cases hlq : l = q
  · subst hlq
    have hdiv : l ∣ l.choose 2 * d := by
      by_cases hl2 : l = 2
      · subst hl2
        have := h2 rfl
        apply Dvd.dvd.mul_left
        omega
      · have := hl.two_le
        exact Dvd.dvd.mul_right (hl.dvd_choose_self (by norm_num) (by omega)) _
    obtain ⟨e, he⟩ := hdiv
    have h1 : l • (ψ + l • (e • ψ ^ 2 + (d ^ 2) • z)) = 0 := by
      rw [← h0, mul_left_comm, he]
      module
    have h3 := htf l _ hl.ne_zero h1
    exact ⟨-(e • ψ ^ 2 + (d ^ 2) • z), by rw [smul_neg]; exact eq_neg_of_add_eq_zero_left h3⟩
  · have hcop : IsCoprime (l : ℤ) (q : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hl hq).mpr hlq)
    obtain ⟨u, v, huv⟩ := hcop
    refine ⟨v • ψ - u • ((l.choose 2 * d) • ψ ^ 2 + (q * d ^ 2) • z), ?_⟩
    have h1 : ψ = (u * l + v * q) • ψ := by rw [huv, one_smul]
    have h4 : ψ = (u * l + v * q) • ψ
        - u • (l • ψ + (l.choose 2 * (q * d)) • ψ ^ 2 + ((q * d) ^ 2) • z) := by
      rw [h0, smul_zero, sub_zero]; exact h1
    refine h4.trans ?_
    module

theorem eq_zero_of_prime (htf : ∀ (n : ℕ) (x : E), n ≠ 0 → n • x = 0 → x = 0) {q c l : ℕ}
    (hq : q.Prime) (hsep : ∀ x : E, (∀ k : ℕ, ∃ y : E, x = q ^ k • y) → x = 0)
    (hl : l.Prime) (hc0 : c ≠ 0) (hqc : q ∣ c) (h2 : q = 2 → 4 ∣ c) (ψ : E)
    (h : (1 + c • ψ) ^ l = 1) : ψ = 0 := by
  apply hsep
  intro k
  induction k with
  | zero => exact ⟨ψ, by simp⟩
  | succ k ih =>
    obtain ⟨y, hy⟩ := ih
    have h' : (1 + (c * q ^ k) • y) ^ l = 1 := by rw [mul_smul, ← hy, h]
    obtain ⟨w, hw⟩ := step htf hq hl (mul_ne_zero hc0 (pow_ne_zero k hq.ne_zero))
      (hqc.mul_right _) (fun hq2 => (h2 hq2).mul_right _) y h'
    exact ⟨w, by rw [hy, hw, pow_succ, mul_smul]⟩

theorem eq_one_of_pow (htf : ∀ (n : ℕ) (x : E), n ≠ 0 → n • x = 0 → x = 0) {q c : ℕ}
    (hq : q.Prime) (hsep : ∀ x : E, (∀ k : ℕ, ∃ y : E, x = q ^ k • y) → x = 0)
    (hc0 : c ≠ 0) (hqc : q ∣ c) (h2 : q = 2 → 4 ∣ c) (m : ℕ) :
    m ≠ 0 → ∀ ψ : E, (1 + c • ψ) ^ m = 1 → 1 + c • ψ = 1 := by
  induction m using induction_on_primes with
  | zero => intro h; exact absurd rfl h
  | one => intro _ ψ h; simpa only [pow_one] using h
  | prime_mul l a hl ih =>
    intro hm ψ h
    have ha : a ≠ 0 := right_ne_zero_of_mul hm
    obtain ⟨z, hz⟩ := one_add_smul_pow_expand c ψ l
    rw [pow_mul, hz] at h
    have h1 := ih ha _ h
    rw [← hz] at h1
    rw [eq_zero_of_prime htf hq hsep hl hc0 hqc h2 ψ h1, smul_zero, add_zero]

end SerreTorsion

theorem eq_one_of_pow_eq_one_of_congr_one :
    ∀ (E : Type) [Ring E] (M : ℕ), 3 ≤ M → (∀ (n : ℕ) (x : E), n ≠ 0 → (n : E) * x = 0 → x = 0) → (∀ (q : ℕ) (x : E), 2 ≤ q → (∀ k : ℕ, ∃ y : E, x = (q : E) ^ k * y) → x = 0) → ∀ (σ φ : E) (m : ℕ), m ≠ 0 → σ = 1 + (M : E) * φ → σ ^ m = 1 → σ = 1 := by
  intro E _ M hM htf hsep σ φ m hm hσ h
  have hq : ∃ q : ℕ, q.Prime ∧ q ∣ M ∧ (q = 2 → 4 ∣ M) := by
    rcases Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt (by omega : 2 < M) with
      h4 | ⟨p, hp, hpM, hodd⟩
    · exact ⟨2, Nat.prime_two, Dvd.dvd.trans (by norm_num) h4, fun _ => h4⟩
    · refine ⟨p, hp, hpM, fun h2 => ?_⟩
      subst h2
      exact absurd hodd (by decide)
  obtain ⟨q, hq, hqM, h2⟩ := hq
  rw [← nsmul_eq_mul] at hσ
  subst hσ
  refine SerreTorsion.eq_one_of_pow (fun n x hn hx => htf n x hn (by rwa [← nsmul_eq_mul])) hq
    (fun x hx => hsep q x hq.two_le fun k => ?_) (by omega) hqM h2 m hm φ h
  obtain ⟨y, hy⟩ := hx k
  exact ⟨y, by rw [hy, nsmul_eq_mul, Nat.cast_pow]⟩

end GlobalTheory
end
