module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Regular.RegularSequence
public import ReciprocityTheory.GaloisValuations.Global
public import ReciprocityTheory.NeutralLocalFields.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle708
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle709
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.Valuation.LocalSubring
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.Artinian.Ring
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem exteriorSquare_equiv_of_baseChange : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (M N M' N' : Type) [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N] [AddCommGroup M'] [Module L M'] [AddCommGroup N'] [Module L N'] (c : M →ₗ[K] M →ₗ[K] N) (c' : M' →ₗ[L] M' →ₗ[L] N') (e₁ : L ⊗[K] M ≃ₗ[L] M') (e₂ : L ⊗[K] N ≃ₗ[L] N'), (∀ a b, e₂ (1 ⊗ₜ c a b) = c' (e₁ (1 ⊗ₜ a)) (e₁ (1 ⊗ₜ b))) → (∃ e : ⋀[L]^2 M' ≃ₗ[L] N', ∀ a b, e (exteriorPower.ιMulti L 2 ![a, b]) = c' a b) → ∃ e : ⋀[K]^2 M ≃ₗ[K] N, ∀ a b, e (exteriorPower.ιMulti K 2 ![a, b]) = c a b := by
  intro K L _ _ _ M N M' N' _ _ _ _ _ _ _ _ c c' e₁ e₂ hcomp hex
  classical
  obtain ⟨eL, heL⟩ := hex

  have hinj : Function.Injective (TensorProduct.mk K L N 1) := by
    have h1 : Function.Injective ((Algebra.linearMap K L).rTensor N) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ (algebraMap K L).injective
    intro x y hxy
    apply (TensorProduct.lid K N).symm.injective
    apply h1
    simpa [TensorProduct.lid_symm_apply] using hxy

  have hc : ∀ a, c a a = 0 := by
    intro a
    apply hinj
    apply e₂.injective
    have h0 : exteriorPower.ιMulti L 2 ![e₁ (1 ⊗ₜ a), e₁ (1 ⊗ₜ a)] = 0 :=
      AlternatingMap.map_eq_zero_of_eq _ _ (i := 0) (j := 1) rfl (by decide)
    simp only [TensorProduct.mk_apply, hcomp, TensorProduct.tmul_zero, map_zero, ← heL, h0]
  let f : M [⋀^Fin 2]→ₗ[K] N :=
    { toFun := fun w => c (w 0) (w 1)
      map_update_add' := by
        intro _ w i x y
        fin_cases i <;> simp
      map_update_smul' := by
        intro _ w i r x
        fin_cases i <;> simp
      map_eq_zero_of_eq' := by
        intro w i j hij hne
        fin_cases i <;> fin_cases j <;> simp_all [hc] }
  let φ := exteriorPower.alternatingMapLinearEquiv f
  have hφ : ∀ w : Fin 2 → M, φ (exteriorPower.ιMulti K 2 w) = c (w 0) (w 1) := fun w =>
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti f w
  let b := Module.Basis.ofVectorSpace K M
  letI : LinearOrder (Module.Basis.ofVectorSpaceIndex K M) := linearOrderOfSTO WellOrderingRel
  let B := b.exteriorPower 2
  let b' := (Algebra.TensorProduct.basis L b).map e₁
  have hb' : ∀ i, b' i = e₁ (1 ⊗ₜ b i) := fun i => by
    simp [b', Algebra.TensorProduct.basis_apply]
  let B' := b'.exteriorPower 2
  have key : ∀ s, e₂ (1 ⊗ₜ φ (B s)) = eL (B' s) := by
    intro s
    rw [exteriorPower.basis_apply, exteriorPower.basis_apply, exteriorPower.ιMulti_family,
      exteriorPower.ιMulti_family, hφ, hcomp, ← heL]
    congr 2
    funext i
    fin_cases i <;> simp [hb']
  let V' := B'.map (eL.trans e₂.symm)
  have hV' : ∀ s, V' s = (1 : L) ⊗ₜ[K] φ (B s) := fun s => by
    simp only [V', Module.Basis.map_apply, LinearEquiv.trans_apply]
    rw [← key, LinearEquiv.symm_apply_apply]
  have h1 : LinearIndependent L (fun s => (1 : L) ⊗ₜ[K] φ (B s)) := by
    have h := V'.linearIndependent
    rwa [show (⇑V') = fun s => (1 : L) ⊗ₜ[K] φ (B s) from funext hV'] at h
  have h2 : LinearIndependent K (fun s => (1 : L) ⊗ₜ[K] φ (B s)) := h1.restrict_scalars' K
  have h3 : LinearIndependent K (φ ∘ B) := LinearIndependent.of_comp (TensorProduct.mk K L N 1) h2
  let W := Submodule.span K (Set.range (φ ∘ B))
  have hs : Function.Surjective (W.subtype.lTensor L) := by
    have hr : LinearMap.range (W.subtype.baseChange L) = ⊤ := by
      rw [eq_top_iff, ← V'.span_eq, Submodule.span_le]
      rintro _ ⟨s, rfl⟩
      rw [hV']
      exact ⟨1 ⊗ₜ ⟨φ (B s), Submodule.subset_span ⟨s, rfl⟩⟩, rfl⟩
    intro x
    obtain ⟨y, hy⟩ := LinearMap.range_eq_top.mp hr x
    exact ⟨y, by rw [← LinearMap.baseChange_eq_ltensor]; exact hy⟩
  have hW : Function.Surjective W.subtype :=
    (Module.FaithfullyFlat.lTensor_surjective_iff_surjective K L W.subtype).mp hs
  have hspan : ⊤ ≤ W := fun x _ => by
    obtain ⟨y, rfl⟩ := hW x
    exact y.2
  let V := Module.Basis.mk h3 hspan
  refine ⟨B.equiv V (Equiv.refl _), fun a b => ?_⟩
  have hEq : (B.equiv V (Equiv.refl _)).toLinearMap = φ :=
    B.ext fun s => by simp [V, Module.Basis.mk_apply]
  rw [← LinearEquiv.coe_coe, hEq, hφ]
  rfl

end GlobalTheory.AbCoh
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory

theorem artinianLocal_finiteLength_and_socle_element :
    ∀ (R : Type) [CommRing R] [IsArtinianRing R] [IsLocalRing R],
      (∃ n : ℕ, Module.length R R = n) ∧
      (¬ IsField R → ∃ t : R, t ≠ 0 ∧ (∀ a ∈ IsLocalRing.maximalIdeal R, a * t = 0) ∧
        Module.length (R ⧸ Ideal.span {t}) (R ⧸ Ideal.span {t}) < Module.length R R) := by
  intro R _ _ _
  have hfin : IsFiniteLength R R :=
    isFiniteLength_iff_isNoetherian_isArtinian.2 ⟨inferInstance, inferInstance⟩
  have hne : Module.length R R ≠ ⊤ := Module.length_ne_top_iff.2 hfin
  refine ⟨⟨(Module.length R R).toNat, (ENat.natCast_toNat hne).symm⟩, ?_⟩
  intro hnf
  classical
  set m := IsLocalRing.maximalIdeal R with hmdef
  obtain ⟨k, hk⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R)
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hk
  have hex : ∃ n : ℕ, m ^ n = ⊥ := ⟨k, hk⟩
  have hn : m ^ Nat.find hex = ⊥ := Nat.find_spec hex
  have hn0 : Nat.find hex ≠ 0 := by
    intro h
    rw [h, pow_zero, Ideal.one_eq_top] at hn
    exact top_ne_bot hn
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hjne : m ^ j ≠ ⊥ := Nat.find_min hex (by omega)
  obtain ⟨t, htm, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hjne
  have hkill : ∀ a ∈ m, a * t = 0 := by
    intro a ha
    have h1 : a * t ∈ m ^ (j + 1) := by
      rw [pow_succ']
      exact Ideal.mul_mem_mul ha htm
    have hj' : Nat.find hex = j + 1 := hj
    rw [← hj', hn] at h1
    exact (Submodule.mem_bot R).1 h1
  refine ⟨t, ht0, hkill, ?_⟩
  set I : Ideal R := Ideal.span {t}
  rw [Module.length_eq_of_surjective (S := R) (R := R ⧸ I) (M := R ⧸ I)
    Ideal.Quotient.mk_surjective |>.symm]
  have hadd := Module.length_eq_add_of_exact (R := R) I.subtype I.mkQ I.injective_subtype
    I.mkQ_surjective (LinearMap.exact_subtype_mkQ I)
  have hI : Module.length R I ≠ 0 := by
    rw [Ne, Module.length_eq_zero_iff]
    intro hs
    have : (⟨t, Ideal.subset_span rfl⟩ : I) = 0 := Subsingleton.elim _ _
    exact ht0 (congrArg Subtype.val this)
  have hQ : Module.length R (R ⧸ I) ≠ ⊤ := by
    intro h
    rw [hadd, h] at hne
    simp at hne
  rw [hadd]
  lift Module.length R (R ⧸ I) to ℕ using hQ with q
  lift Module.length R I to ℕ using (by
    intro h; rw [hadd, h] at hne; simp at hne) with i
  norm_cast
  norm_cast at hI
  omega

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory


open RingTheory.Sequence in
theorem weaklyRegular_relations_koszul :
    ∀ (O : Type) [CommRing O] (g : ℕ) (f : Fin g → O), RingTheory.Sequence.IsWeaklyRegular O (List.ofFn f) → ∀ a : Fin g → O, ∑ i, a i * f i = 0 → ∃ c : Matrix (Fin g) (Fin g) O, (∀ i, c i i = 0) ∧ (∀ i j, c i j = - c j i) ∧ a = c.mulVec f := by
  intro O _ g
  induction g with
  | zero =>
    intro f _ a _
    exact ⟨0, by simp, by simp, funext fun i => i.elim0⟩
  | succ g ih =>
    intro f hf a ha
    have hsplit : List.ofFn f =
        List.ofFn (fun i : Fin g => f i.castSucc) ++ [f (Fin.last g)] := by
      rw [List.ofFn_succ_last]
    rw [hsplit, isWeaklyRegular_append_iff, isWeaklyRegular_singleton_iff] at hf
    obtain ⟨hf1, hf2⟩ := hf
    rw [Fin.sum_univ_castSucc] at ha
    have hIt : (Ideal.ofList (List.ofFn fun i : Fin g => f i.castSucc) • ⊤ : Submodule O O) =
        Ideal.ofList (List.ofFn fun i : Fin g => f i.castSucc) := by
      rw [smul_eq_mul, Ideal.mul_top]
    have hmem : a (Fin.last g) ∈
        (Ideal.ofList (List.ofFn fun i : Fin g => f i.castSucc) • ⊤ : Submodule O O) := by
      rw [← Submodule.Quotient.mk_eq_zero]
      apply hf2
      simp only [smul_zero]
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, hIt, smul_eq_mul, mul_comm,
        eq_neg_of_add_eq_zero_right ha, neg_mem_iff]
      exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    rw [hIt, Ideal.ofList, show {r | r ∈ List.ofFn fun i : Fin g => f i.castSucc}
        = Set.range (fun i : Fin g => f i.castSucc) by ext; simp [List.mem_ofFn],
      Ideal.mem_span_range_iff_exists_fun] at hmem
    obtain ⟨b, hb⟩ := hmem
    obtain ⟨c', hc0, hcs, hca⟩ := ih (fun i => f i.castSucc) hf1
      (fun i => a i.castSucc + b i * f (Fin.last g)) (by
        simp only [add_mul, Finset.sum_add_distrib]
        rw [← ha, ← hb, Finset.sum_mul, add_right_inj]
        exact Finset.sum_congr rfl fun i _ => by ring)
    refine ⟨fun i j => Fin.lastCases (Fin.lastCases 0 (fun j => b j) j)
      (fun i => Fin.lastCases (-b i) (fun j => c' i j) j) i, ?_, ?_, ?_⟩
    · intro i
      cases i using Fin.lastCases with
      | last => simp
      | cast i => simp [hc0]
    · intro i j
      cases i using Fin.lastCases <;> cases j using Fin.lastCases <;> simp <;> exact hcs _ _
    · funext i
      cases i using Fin.lastCases with
      | last => simp [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, hb]
      | cast i =>
        have := congrFun hca i
        simp only [Matrix.mulVec, dotProduct] at this
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, Fin.lastCases_castSucc,
          Fin.lastCases_last]
        rw [← this]
        ring

end GlobalTheory
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal Neutral.B1
open scoped nonZeroDivisors

namespace GlobalTheory.InertiaRestrict

theorem restrict_eq_one : ∀ {K : Type} [Field K] [NumberField K] {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (e : Ω ≃ₐ[K] AlgebraicClosure K) (L : IntermediateField K (AlgebraicClosure K)) (h : IsFiniteAbelian K L) (v : HeightOneSpectrum (𝓞 K)), IsUnramifiedIn K v L → ∀ (A : ValuationSubring Ω), Formalism.ConjugateSelfDual.IsPlaceOver A v → ∀ σ : Formalism.ConjugateSelfDual.G K Ω, σ ∈ ReciprocityTheory.Gal.Ine (F := K) A → haveI := h.isGalois; AlgEquiv.restrictNormalHom L ((e.symm.trans σ).trans e) = 1 := by
  intro K _ _ Ω _ _ _ e L h v hv A hA σ hσ
  haveI := h.isGalois
  haveI := h.finiteDimensional
  haveI : NumberField L := NumberField.of_module_finite K L
  have hint : ∀ y : 𝓞 L, e.symm ((y : L) : AlgebraicClosure K) ∈ A := by
    intro y
    have h1 : IsIntegral ℤ (e.symm ((y : L) : AlgebraicClosure K)) :=
      map_isIntegral_int ((e.symm : AlgebraicClosure K →+* Ω).comp (algebraMap L (AlgebraicClosure K)))
        y.isIntegral_coe
    obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).1 (h1.tower_top)
    rw [← ha]
    exact a.2
  let φ : 𝓞 L →+* A :=
    { toFun := fun y => ⟨e.symm ((y : L) : AlgebraicClosure K), hint y⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro a b; ext; simp }
  let Q : Ideal (𝓞 L) := (IsLocalRing.maximalIdeal A).comap φ
  have hmem : ∀ y : 𝓞 L, y ∈ Q ↔ A.valuation (e.symm ((y : L) : AlgebraicClosure K)) < 1 := fun y =>
    ValuationSubring.valuation_lt_one_iff A (φ y)
  haveI hQp : Q.IsPrime := Ideal.comap_isPrime _ _
  haveI hQo : Q.LiesOver v.asIdeal := by
    constructor
    ext x
    rw [Ideal.under, Ideal.mem_comap, hmem, ← hA x]
    have : ((algebraMap (𝓞 K) (𝓞 L) x : L) : AlgebraicClosure K) = algebraMap K (AlgebraicClosure K) (x : K) := by
      first
        | rfl
        | (rw [RingOfIntegers.algebraMap_coe]; rfl)
        | simp [IsScalarTower.algebraMap_apply K L (AlgebraicClosure K)]
    rw [this, AlgEquiv.commutes]
  have hram : Q.ramificationIdx (𝓞 K) = 1 := hv Q hQp hQo
  have hcard : Nat.card (Q.inertia (L ≃ₐ[K] L)) = 1 := by
    have : IsGaloisGroup (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) := IsGaloisGroup.of_isFractionRing _ _ _ K L
    have hpr : (Q.under (𝓞 K)).IsPrime := Ideal.IsPrime.under _ Q
    have hc := Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[K] L) (Q.under (𝓞 K)) Q
    rwa [Ideal.ramificationIdxIn_eq_ramificationIdx (Q.under (𝓞 K)) Q (L ≃ₐ[K] L), hram] at hc
  have hbot : Q.inertia (L ≃ₐ[K] L) = ⊥ := Subgroup.card_eq_one.1 hcard
  have hin : AlgEquiv.restrictNormalHom L ((e.symm.trans σ).trans e) ∈ Q.inertia (L ≃ₐ[K] L) := by
    refine AddSubgroup.mem_inertia.mpr fun y => ?_
    change _ ∈ Q
    rw [hmem]
    have h2 : (((AlgEquiv.restrictNormalHom L ((e.symm.trans σ).trans e) • y - y : 𝓞 L) : L) : AlgebraicClosure K)
        = e (σ (e.symm ((y : L) : AlgebraicClosure K))) - ((y : L) : AlgebraicClosure K) := by
      have h3 : ((AlgEquiv.restrictNormalHom L ((e.symm.trans σ).trans e) • y : 𝓞 L) : L) =
          AlgEquiv.restrictNormalHom L ((e.symm.trans σ).trans e) (y : L) := rfl
      simp only [map_sub, h3, AlgEquiv.restrictNormalHom_apply]
      have h4 := AlgEquiv.restrictNormalHom_apply L ((e.symm.trans σ).trans e) (y : L)
      rw [AddSubgroupClass.coe_sub, h4]
      rfl
    rw [h2, map_sub, AlgEquiv.symm_apply_apply]
    exact hσ.2 _ ((A.valuation_le_one_iff _).2 (hint y))
  rw [hbot] at hin
  exact hin

end GlobalTheory.InertiaRestrict
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.AbCoh

theorem prod_pullback_sq : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp R')) [GrpObj A'] (φ : A'.left ⟶ A.left), IsGrpPullback A' A (spMap σ) φ → ∃ Φ : (A' ⊗ A').left ⟶ (A ⊗ A).left, IsPullback Φ (A' ⊗ A').hom (A ⊗ A).hom (spMap σ) ∧ μ[A'].left ≫ φ = Φ ≫ μ[A].left ∧ (fst A' A').left ≫ φ = Φ ≫ (fst A A).left ∧ (snd A' A').left ≫ φ = Φ ≫ (snd A A).left ∧ (lift (𝟙 A') (toUnit A' ≫ η[A'])).left ≫ Φ = φ ≫ (lift (𝟙 A) (toUnit A ≫ η[A])).left ∧ (lift (toUnit A' ≫ η[A']) (𝟙 A')).left ≫ Φ = φ ≫ (lift (toUnit A ≫ η[A]) (𝟙 A)).left := by
  intro R R' _ _ σ A _ A' _ φ h
  have pA : IsPullback (fst A A).left (snd A A).left A.hom A.hom := IsPullback.of_hasPullback _ _
  have pA' : IsPullback (fst A' A').left (snd A' A').left A'.hom A'.hom := IsPullback.of_hasPullback _ _
  obtain ⟨Φ, h₁, h₂⟩ : ∃ Φ : (A' ⊗ A').left ⟶ (A ⊗ A).left,
      Φ ≫ (fst A A).left = (fst A' A').left ≫ φ ∧ Φ ≫ (snd A A).left = (snd A' A').left ≫ φ :=
    ⟨pA.lift ((fst A' A').left ≫ φ) ((snd A' A').left ≫ φ) (by
      rw [Category.assoc, Category.assoc, h.1.w, ← Category.assoc, ← Category.assoc, pA'.w]),
      pA.lift_fst _ _ _, pA.lift_snd _ _ _⟩
  have hP : IsPullback Φ (A' ⊗ A').hom (A ⊗ A).hom (spMap σ) := by
    have q := pA'.paste_horiz h.1
    rw [← h₁, ← h.1.w] at q
    have r := (IsPullback.of_right q h₂ pA).paste_vert h.1
    rwa [Over.w, Over.w] at r
  have one : ∀ T : Over (Sp R'), (toUnit T ≫ η[A']).left ≫ φ = (T.hom ≫ spMap σ) ≫ η[A].left := by
    intro T
    let x₀ : Over.mk (T.hom ≫ spMap σ) ⟶ A := Over.homMk ((toUnit T ≫ η[A']).left ≫ φ) (by
      rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]; rfl)
    have hx : x₀ * x₀ = x₀ := by
      apply Over.OverMorphism.ext
      rw [h.2 T 1 1 x₀ x₀ rfl rfl, _root_.mul_one]
      rfl
    have e : x₀ = 1 := mul_eq_left.1 hx
    have e' := congrArg (fun q => q.left) e
    refine e'.trans ?_
    show (toUnit _ ≫ η[A]).left = _
    rw [Over.comp_left, Over.toUnit_left]
    rfl
  let Ψ : Over.mk ((A' ⊗ A').hom ≫ spMap σ) ⟶ A ⊗ A := Over.homMk Φ hP.w
  have hm := h.2 (A' ⊗ A') (fst A' A') (snd A' A') (Ψ ≫ fst A A) (Ψ ≫ snd A A) h₁ h₂
  rw [← MonObj.comp_mul, Hom.mul_def, Hom.mul_def, lift_fst_snd, lift_fst_snd, Category.id_comp, Category.id_comp,
    Over.comp_left] at hm
  refine ⟨Φ, hP, hm.symm, h₁.symm, h₂.symm, ?_, ?_⟩
  · refine pA.hom_ext ?_ ?_
    · rw [Category.assoc, h₁, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc, ← Over.comp_left,
        lift_fst, Over.id_left, Over.id_left, Category.id_comp, Category.comp_id]
    · rw [Category.assoc, h₂, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc, ← Over.comp_left,
        lift_snd, one, Over.comp_left, Over.toUnit_left, ← Category.assoc, h.1.w]
  · refine pA.hom_ext ?_ ?_
    · rw [Category.assoc, h₁, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc, ← Over.comp_left,
        lift_fst, one, Over.comp_left, Over.toUnit_left, ← Category.assoc, h.1.w]
    · rw [Category.assoc, h₂, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc, ← Over.comp_left,
        lift_snd, Over.id_left, Over.id_left, Category.id_comp, Category.comp_id]

end GlobalTheory.AbCoh
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

theorem isIntegral_image_of_field {K : Type} [Field K] {S : Scheme.{0}} (g : Sp K ⟶ S) : IsIntegral g.image := by
  have : QuasiCompact g := inferInstance
  have := GlobalTheory.isSchemeTheoreticallyDominant_toImage g
  have : IsReduced g.image := IsSchemeTheoreticallyDominant.isReduced g.toImage
  have hi : IsIrreducible (Set.range g.toImage) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ g.toImage.continuous.continuousOn
  have hc := hi.closure
  rw [g.toImage.denseRange.closure_range] at hc
  have : IrreducibleSpace g.image := { isPreirreducible_univ := hc.2, toNonempty := ⟨hc.1.some⟩ }
  exact isIntegral_of_irreducibleSpace_of_isReduced _

theorem lbIso_factor {X Y Z : Scheme.{0}} {L : LB X} {L' : LB Y} {M : LB Z} (hL : L.IsLB) (hL' : L'.IsLB) (hM : M.IsLB)
    {F : Y ⟶ X} {a' : Z ⟶ Y} {a : Z ⟶ X} (e : a' ≫ F = a) (h' : LBIso L' (L.pull F)) (h : LBIso M (L.pull a)) :
    LBIso M (L'.pull a') :=
  LBIso.trans hM (pull_isLB hL _) (pull_isLB hL' _) h
    (LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull L' a' a' rfl) (chartPullSame L (fun _ => a) (fun _ => F) _ a' fun _ => e.symm) h').symm

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.abelianScheme_homAgreeLocus_closedSubscheme : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A B : Over S) [GrpObj A] [GrpObj B] (u v : A ⟶ B), IsAbelianScheme A → IsAbelianScheme B → IsMonHom u → IsMonHom v → ∃ (Z : Scheme.{0}) (i : Z ⟶ S), IsClosedImmersion i ∧ ∀ (T : Scheme.{0}) (t : T ⟶ S) (A' : Over T) [GrpObj A'] (φ' : A'.left ⟶ A.left), IsGrpPullback A' A t φ' → (φ' ≫ u.left = φ' ≫ v.left ↔ ∃ z : T ⟶ Z, z ≫ i = t) := by
  first | (exact @GlobalTheory.EndLoc.agreeLocus_factors_closedSubscheme) | (exact GlobalTheory.EndLoc.agreeLocus_factors_closedSubscheme) | (intros; apply GlobalTheory.EndLoc.agreeLocus_factors_closedSubscheme  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT.Hecke.PullInj

theorem _root_.GlobalTheory.T.exists_axis_unit_generators_pullback : ∀ (A₀ A₀' X X' : Scheme.{0}) (ψ : A₀ ⟶ A₀') (e : A₀ ⟶ X) (e' : A₀' ⟶ X') (π : X ⟶ X'), e ≫ π = ψ ≫ e' → ∀ (Q₁ Q₂ : LB X'), Q₁.IsLB → Q₂.IsLB → ∀ (w : LB.Iso (Q₁.pull π) (Q₂.pull π)), w.IsGen → ∀ (ρ₁ : LB.Gen (Q₁.pull e')) (ρ₂ : LB.Gen (Q₂.pull e')), ρ₁.IsGen → ρ₂.IsGen → ∃ g : Γ(A₀, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ A₀) (z : Z) (k : (PUnit → Q₂.ι) × (PUnit → Q₁.ι)), e (r z) ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U k → gm (r ≫ e) z _ (w.s k) * gm (r ≫ ψ) z _ (ρ₁.s k.2) = gm r z ⊤ g * gm (r ≫ ψ) z _ (ρ₂.s k.1) := by
  first | (exact @GlobalTheory.UPel.HT.Hecke.PullInj.axis_unit) | (exact GlobalTheory.UPel.HT.Hecke.PullInj.axis_unit) | (intros; apply GlobalTheory.UPel.HT.Hecke.PullInj.axis_unit  <;> assumption)
end
