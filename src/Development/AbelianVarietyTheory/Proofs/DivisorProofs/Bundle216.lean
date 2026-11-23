module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle085
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle005
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle133
public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.GroupTheory.Index
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle087
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.OreLocalization.Ring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle088
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle089
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.Localization.Defs
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

section

open IsLocalRing
open scoped TensorProduct

namespace GlobalTheory

theorem pow_mem_range_includeRight_of_isPurelyInseparable (k K B : Type) [Field k] [Field K]
    [Algebra k K] [IsPurelyInseparable k K] [CommRing B] [Nontrivial B] [Algebra k B]
    (q : ℕ) [ExpChar k q] (z : K ⊗[k] B) :
    ∃ n : ℕ, z ^ q ^ n ∈
      (Algebra.TensorProduct.includeRight : B →ₐ[k] K ⊗[k] B).range := by
  first
  | exact @_root_.GlobalTheory.PowerInRangeTensorRight.exists_pow_pow_mem_range_includeRight
  | exact _root_.GlobalTheory.PowerInRangeTensorRight.exists_pow_pow_mem_range_includeRight
  | (apply _root_.GlobalTheory.PowerInRangeTensorRight.exists_pow_pow_mem_range_includeRight <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowerInRangeTensorRight.exists_pow_pow_mem_range_includeRight <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowerInRangeTensorRight.exists_pow_pow_mem_range_includeRight <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowerInRangeTensorRight.exists_pow_pow_mem_range_includeRight ..)

theorem idempotent_tensor_eq_zero_or_one_of_isPurelyInseparable (k K B : Type) [Field k] [Field K]
    [Algebra k K] [IsPurelyInseparable k K] [CommRing B] [IsLocalRing B] [Algebra k B]
    (e : K ⊗[k] B) (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  have hinj : Function.Injective (Algebra.TensorProduct.includeRight : B →ₐ[k] K ⊗[k] B) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap k K).injective
  obtain ⟨n, b, hb⟩ :=
    pow_mem_range_includeRight_of_isPurelyInseparable k K B (ringExpChar k) e
  have hpos : ringExpChar k ^ n ≠ 0 := (pow_pos (expChar_pos k _) n).ne'
  have h1 : e ^ (ringExpChar k ^ n) = e := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hpos
    rw [hm]; exact he.pow_succ_eq m
  rw [h1] at hb
  have hb' : (Algebra.TensorProduct.includeRight : B →ₐ[k] K ⊗[k] B) b = e := hb
  have hbi : b * b = b := by
    apply hinj
    rw [map_mul, hb']; exact he
  rcases isUnit_or_isUnit_one_sub_self b with hu | hu
  · right
    have : b = 1 := hu.mul_left_cancel (by rw [hbi, mul_one])
    rw [← hb', this, map_one]
  · left
    have : b = 0 := hu.mul_left_cancel (by rw [sub_mul, hbi, one_mul, sub_self, mul_zero])
    rw [← hb', this, map_zero]

end GlobalTheory
end

section

open Polynomial IntermediateField

noncomputable section

namespace GlobalTheory.PrimTransc

theorem exists_separable_specialization {D : ℕ} (P : (MvPolynomial (Fin D) ℚ)[X])
    (h : (P.map (algebraMap (MvPolynomial (Fin D) ℚ) (FractionRing (MvPolynomial (Fin D) ℚ)))).Separable) :
    ∃ c : Fin D → ℚ, (P.map (MvPolynomial.eval c)).Separable := by
  set R := MvPolynomial (Fin D) ℚ
  set F := FractionRing R
  obtain ⟨a, b, hab⟩ := h
  obtain ⟨da, hda, hA⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) a
  obtain ⟨db, hdb, hB⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) b
  set A := IsLocalization.integerNormalization (nonZeroDivisors R) a
  set B := IsLocalization.integerNormalization (nonZeroDivisors R) b
  have key : (C db * A) * P + (C da * B) * derivative P = C (da * db) := by
    apply Polynomial.map_injective (algebraMap R F) (IsFractionRing.injective R F)
    have hA' : A.map (algebraMap R F) = C (algebraMap R F da) * a := by
      rw [hA, ← algebraMap_smul F da a, smul_eq_C_mul]
    have hB' : B.map (algebraMap R F) = C (algebraMap R F db) * b := by
      rw [hB, ← algebraMap_smul F db b, smul_eq_C_mul]
    simp only [Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.map_C, hA', hB',
      ← derivative_map, map_mul]
    linear_combination (C (algebraMap R F da) * C (algebraMap R F db)) * hab
  have hδ : da * db ≠ 0 := mul_ne_zero (nonZeroDivisors.ne_zero hda) (nonZeroDivisors.ne_zero hdb)
  obtain ⟨c, hc⟩ : ∃ c : Fin D → ℚ, MvPolynomial.eval c (da * db) ≠ 0 := by
    by_contra hno
    push_neg at hno
    exact hδ (MvPolynomial.funext fun c => by simpa using hno c)
  refine ⟨c, ?_⟩
  have key' := congrArg (Polynomial.map (MvPolynomial.eval c)) key
  simp only [Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.map_C, ← derivative_map] at key'
  have hinv : C (MvPolynomial.eval c (da * db))⁻¹ * C (MvPolynomial.eval c (da * db)) = 1 := by
    rw [← C_mul, inv_mul_cancel₀ hc, C_1]
  refine ⟨C (MvPolynomial.eval c (da * db))⁻¹ * (C (MvPolynomial.eval c db) * A.map (MvPolynomial.eval c)),
    C (MvPolynomial.eval c (da * db))⁻¹ * (C (MvPolynomial.eval c da) * B.map (MvPolynomial.eval c)), ?_⟩
  linear_combination C (MvPolynomial.eval c (da * db))⁻¹ * key' + hinv

theorem exists_mul_mem_adjoin {R F K : Type} [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] [Field K] [Algebra R K] [Algebra F K] [IsScalarTower R F K] (θ z : K)
    (hz : z ∈ Algebra.adjoin F {θ}) :
    ∃ d : R, d ≠ 0 ∧ algebraMap R K d * z ∈ Algebra.adjoin R {θ} := by
  first
  | (rename_i h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11; revert R F K h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 θ z hz; exact @_root_.GlobalTheory.TargetInequalityLemmas.target)
  | exact @_root_.GlobalTheory.TargetInequalityLemmas.target
  | exact _root_.GlobalTheory.TargetInequalityLemmas.target
  | (apply _root_.GlobalTheory.TargetInequalityLemmas.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.TargetInequalityLemmas.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TargetInequalityLemmas.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TargetInequalityLemmas.target ..)

theorem exists_primitive_monic_separable_specialization :
    ∀ (K : Type) [Field K] [CharZero K] (D : ℕ) (x : Fin D → K), IsTranscendenceBasis ℚ x →
      ∀ (J : Type) [Finite J] (e : J → K), ∃ (P : Polynomial (MvPolynomial (Fin D) ℚ))
        (ψ : AdjoinRoot P →ₐ[ℚ] K) (g : K) (c : Fin D → ℚ), P.Monic ∧ Function.Injective ψ ∧
        (∀ i, ψ (AdjoinRoot.of P (MvPolynomial.X i)) = x i) ∧ g ≠ 0 ∧ (∀ j, g * e j ∈ ψ.range) ∧
        (P.map (MvPolynomial.eval c)).Separable := by
  intro K _ _ D x hx J _ e
  classical
  have := Fintype.ofFinite J
  let R := MvPolynomial (Fin D) ℚ
  let F := FractionRing R
  let φ : R →ₐ[ℚ] K := MvPolynomial.aeval x
  have φinj : Function.Injective φ := hx.1
  letI : Algebra R K := φ.toRingHom.toAlgebra
  have hφ : ∀ r : R, algebraMap R K r = φ r := fun r => rfl
  haveI : IsScalarTower ℚ R K := IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  haveI : FaithfulSMul R K := (faithfulSMul_iff_algebraMap_injective R K).2 φinj
  letI : Algebra F K := FractionRing.liftAlgebra R K
  haveI : IsScalarTower R F K := FractionRing.isScalarTower_liftAlgebra R K
  haveI : CharZero F := RingHom.charZero (algebraMap F K)
  haveI : Algebra.IsAlgebraic R K :=
    haveI := hx.isAlgebraic
    ⟨fun y => (IsAlgebraic.ringHom_of_comp_eq (f := hx.1.aevalEquiv.symm.toRingHom) (g := RingHom.id K)
      (Algebra.IsAlgebraic.isAlgebraic y) hx.1.aevalEquiv.symm.injective (RingHom.ext fun z => by
        obtain ⟨p, rfl⟩ := hx.1.aevalEquiv.surjective z
        simp [RingHom.algebraMap_toAlgebra, φ]))⟩
  haveI : Algebra.IsAlgebraic F K := Algebra.IsAlgebraic.extendScalars (IsFractionRing.injective R F)

  let E := IntermediateField.adjoin F (Set.range e)
  haveI : FiniteDimensional F E := IntermediateField.finiteDimensional_adjoin
    (fun y _ => (Algebra.IsAlgebraic.isAlgebraic (R := F) y).isIntegral)
  obtain ⟨α, hα⟩ := Field.exists_primitive_element F E
  have hαE : F⟮(α : K)⟯ = E := by
    simpa only [IntermediateField.lift_adjoin_simple, IntermediateField.lift_top] using
      congrArg IntermediateField.lift hα
  obtain ⟨y, hy0, hyint⟩ := IsAlgebraic.exists_integral_multiple (Algebra.IsAlgebraic.isAlgebraic (R := R) (α : K))
  set θ : K := y • (α : K) with hθdef
  have hθF : IsIntegral F θ := (Algebra.IsAlgebraic.isAlgebraic (R := F) θ).isIntegral
  have hyF : algebraMap R F y ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R F)).2 hy0
  have hαθ : (α : K) ∈ F⟮θ⟯ := by
    have : (α : K) = algebraMap F K (algebraMap R F y)⁻¹ * θ := by
      rw [hθdef, Algebra.smul_def, IsScalarTower.algebraMap_apply R F K, ← mul_assoc, ← map_mul,
        inv_mul_cancel₀ hyF, map_one, one_mul]
    rw [this]
    exact mul_mem (IntermediateField.algebraMap_mem _ _) (IntermediateField.mem_adjoin_simple_self F θ)
  have heθ : ∀ j, e j ∈ Algebra.adjoin F {θ} := by
    intro j
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hθF.isAlgebraic]
    have h1 : E ≤ F⟮θ⟯ := hαE ▸ IntermediateField.adjoin_simple_le_iff.2 hαθ
    exact h1 (IntermediateField.subset_adjoin F _ ⟨j, rfl⟩)
  choose d hd0 hdm using fun j => exists_mul_mem_adjoin (R := R) (F := F) θ (e j) (heθ j)

  let P := minpoly R θ
  let ψ₀ : AdjoinRoot P →ₐ[R] K := AdjoinRoot.liftAlgHom P (Algebra.ofId R K) θ (minpoly.aeval R θ)
  let ψ : AdjoinRoot P →ₐ[ℚ] K := ψ₀.restrictScalars ℚ
  have hψinj : Function.Injective ψ := by
    refine (injective_iff_map_eq_zero ψ).2 fun q hq => ?_
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective q
    have hq' : Polynomial.aeval θ q = 0 := hq
    exact AdjoinRoot.mk_eq_zero.2 ((minpoly.isIntegrallyClosed_dvd_iff hyint q).1 hq')
  have hrange : Algebra.adjoin R {θ} ≤ ψ₀.range := by
    rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
    exact ⟨AdjoinRoot.root P, AdjoinRoot.liftAlgHom_root _ _ _ _⟩
  have hsep : (P.map (algebraMap R F)).Separable := by
    rw [← minpoly.isIntegrallyClosed_eq_field_fractions' F hyint]
    exact (minpoly.irreducible hθF).separable
  obtain ⟨c, hc⟩ := exists_separable_specialization P hsep
  refine ⟨P, ψ, algebraMap R K (∏ j, d j), c, minpoly.monic hyint, hψinj, fun i => ?_, ?_, fun j => ?_, hc⟩
  · show ψ₀ (AdjoinRoot.of P (MvPolynomial.X i)) = x i
    rw [← AdjoinRoot.algebraMap_eq, AlgHom.commutes, hφ]
    exact MvPolynomial.aeval_X x i
  · exact (map_ne_zero_iff _ φinj).2 (Finset.prod_ne_zero_iff.2 fun j _ => hd0 j)
  · have hm : algebraMap R K (∏ j, d j) * e j ∈ Algebra.adjoin R {θ} := by
      rw [← Finset.mul_prod_erase Finset.univ d (Finset.mem_univ j), mul_comm (d j), map_mul, mul_assoc]
      exact mul_mem (Subalgebra.algebraMap_mem _ _) (hdm j)
    obtain ⟨a, ha⟩ := hrange hm
    exact ⟨a, ha⟩

end GlobalTheory.PrimTransc
end
end

section

open IsLocalRing
open scoped TensorProduct



namespace GlobalTheory.NormFin

theorem main : ∀ (S K L D : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
    [Algebra S D] [Module.Finite S D] [FaithfulSMul S D],
    Module.Finite D (integralClosure D (TensorProduct S D L)) := by
  intro S K L D _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  classical
  let K' := FractionRing D
  haveI : IsScalarTower S D K' := inferInstance
  have hSK' : Function.Injective (algebraMap S K') :=
    by
      rw [IsScalarTower.algebraMap_eq S D K']
      exact (IsFractionRing.injective D K').comp (FaithfulSMul.algebraMap_injective S D)
  letI : Algebra K K' := (IsFractionRing.lift hSK' : K →+* K').toAlgebra
  haveI : IsScalarTower S K K' :=
    IsScalarTower.of_algebraMap_eq (fun x => (IsFractionRing.lift_algebraMap hSK' x).symm)
  haveI : SMulCommClass K D K' := ⟨fun a b c => by simp only [Algebra.smul_def]; ring⟩
  haveI : Algebra.FormallyUnramified K L := Algebra.FormallyUnramified.of_isSeparable K L
  haveI : Algebra.FormallyUnramified K' (K' ⊗[K] L) := inferInstance
  haveI : FiniteDimensional K' (K' ⊗[K] L) := inferInstance
  haveI : IsScalarTower D K' (K' ⊗[K] L) := inferInstance
  have hfinC : Module.Finite D (integralClosure D (K' ⊗[K] L)) :=
    GlobalTheory.AbhFin.finite_integralClosure_of_formallyUnramified D K' (K' ⊗[K] L)
  haveI : Module.Flat S K := IsLocalization.flat K (nonZeroDivisors S)
  haveI : Module.Flat S L := Module.Flat.trans S K L
  let f : D →ₐ[S] K' := IsScalarTower.toAlgHom S D K'
  let Φ : D ⊗[S] L →ₐ[S] K' ⊗[S] L := Algebra.TensorProduct.map f (AlgHom.id S L)
  have hΦ : Function.Injective Φ := by
    have h1 : Function.Injective (f.toLinearMap.rTensor L) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ (IsFractionRing.injective D K')
    have h2 : (Φ : D ⊗[S] L → K' ⊗[S] L) = f.toLinearMap.rTensor L := by
      funext x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => rfl
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
    rw [h2]; exact h1
  let ι : K' ⊗[S] L ≃ₐ[K] K' ⊗[K] L := (IsLocalization.algebraTensorEquiv (nonZeroDivisors S) K K' L).symm
  have hι : ∀ (a : K') (b : L), ι (a ⊗ₜ[S] b) = a ⊗ₜ[K] b := by
    intro a b
    rw [AlgEquiv.symm_apply_eq]
    rfl
  let Ψ : D ⊗[S] L →ₐ[D] K' ⊗[K] L :=
    { (ι.toRingEquiv.toRingHom.comp Φ.toRingHom) with
      commutes' := fun d => by
        show ι (Φ (d ⊗ₜ[S] 1)) = (algebraMap D K' d) ⊗ₜ[K] 1
        rw [Algebra.TensorProduct.map_tmul]
        exact hι _ _ }
  have hΨ : Function.Injective Ψ := ι.injective.comp hΦ
  let M := integralClosure D (D ⊗[S] L)
  let lin : M →ₗ[D] integralClosure D (K' ⊗[K] L) :=
    { toFun := fun x => ⟨Ψ (x : D ⊗[S] L), (show IsIntegral D (x : D ⊗[S] L) from x.2).map Ψ⟩
      map_add' := fun x y => Subtype.ext (map_add Ψ (x : D ⊗[S] L) y)
      map_smul' := fun r x => Subtype.ext (map_smul Ψ r (x : D ⊗[S] L)) }
  exact Module.Finite.of_injective lin (fun x y h => Subtype.ext (hΨ (congrArg Subtype.val h)))

end GlobalTheory.NormFin
end

section

open scoped Pointwise

theorem _root_.GlobalTheory.T.card_fiber_doubleCoset_map_eq_card_inf_conj : ∀ {G : Type} [Group G] (T Γ K' : Subgroup G) (x : G), Nat.card ((fun q : DoubleCoset.Quotient ((Γ ⊓ T : Subgroup G) : Set G) (K' : Set G) => DoubleCoset.mk T K' (Quotient.out q)) ⁻¹' {DoubleCoset.mk T K' x}) = Nat.card (DoubleCoset.Quotient ((Γ.subgroupOf T : Subgroup T) : Set T) (((T ⊓ K'.map (MulAut.conj x).toMonoidHom).subgroupOf T : Subgroup T) : Set T)) := by
  first | exact @GlobalTheory.doubleCoset_fibre_card | exact GlobalTheory.doubleCoset_fibre_card | (intros; apply GlobalTheory.doubleCoset_fibre_card <;> assumption)
end

section


theorem _root_.GlobalTheory.T.relIndex_map_conj_symm_of_relIndex_map_conj_pow_symm : ∀ (A : Type) [Group A] (K : Subgroup A) (g : A) (n : ℕ), 0 < n → (K.map (MulAut.conj g).toMonoidHom).relIndex K ≠ 0 → K.relIndex (K.map (MulAut.conj g).toMonoidHom) ≠ 0 → (K.map (MulAut.conj (g ^ n)).toMonoidHom).relIndex K = K.relIndex (K.map (MulAut.conj (g ^ n)).toMonoidHom) → (K.map (MulAut.conj g).toMonoidHom).relIndex K = K.relIndex (K.map (MulAut.conj g).toMonoidHom) := by
  first | exact @GlobalTheory.relIndex_conj_eq_of_pow_eq | exact GlobalTheory.relIndex_conj_eq_of_pow_eq | (intros; apply GlobalTheory.relIndex_conj_eq_of_pow_eq <;> assumption)
end

section


theorem _root_.GlobalTheory.T.stabilizer_relIndex_ne_zero_parabolic : ∀ (P M N : Type) [Group P] [Group M] [Group N] (s : M →* P) (π : P →* M) (u : N →* P), (∀ m, π (s m) = m) → Function.Injective u → (∀ p, π p = 1 ↔ ∃ X, u X = p) → ∀ (KP : Subgroup P) (KM : Subgroup M) (L : Subgroup N), (∀ k ∈ KM, s k ∈ KP) → (∀ k ∈ KP, π k ∈ KM) → (∀ X, u X ∈ KP ↔ X ∈ L) → ∀ TM : Subgroup M, (∀ X : N, ∃ U : Subgroup M, U ≤ KM ∧ U.relIndex KM ≠ 0 ∧ ∀ k ∈ U, (u X)⁻¹ * s k * u X ∈ KP) → ∀ (q : M) (X : N), (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM ⊓ KP.comap ((MulAut.conj (u X)⁻¹).toMonoidHom.comp s)).relIndex (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM) ≠ 0 := by
  first | exact @GlobalTheory.stab_relIndex_ne_zero | exact GlobalTheory.stab_relIndex_ne_zero | (intros; apply GlobalTheory.stab_relIndex_ne_zero <;> assumption)
end

section


theorem _root_.GlobalTheory.T.doubleCoset_relIndex_inf_conj_const : ∀ (G : Type) [Group G] (T C K : Subgroup G), (∀ q : G, T ⊓ K.map (MulAut.conj q).toMonoidHom ≤ C) → ∀ t ∈ T, ∀ k ∈ K, ∀ q : G, (T ⊓ K.map (MulAut.conj (t * q * k)).toMonoidHom).relIndex C = (T ⊓ K.map (MulAut.conj q).toMonoidHom).relIndex C := by
  first | exact @GlobalTheory.doubleCoset_relIndex_const | exact GlobalTheory.doubleCoset_relIndex_const | (intros; apply GlobalTheory.doubleCoset_relIndex_const <;> assumption)
end

section


theorem _root_.GlobalTheory.T.relIndex_unfold_semidirect_product : ∀ (P M N : Type) [Group P] [Group M] [Group N] (s : M →* P) (π : P →* M) (u : N →* P), (∀ m, π (s m) = m) → Function.Injective u → (∀ p, π p = 1 ↔ ∃ X, u X = p) → ∀ (KP : Subgroup P) (KM : Subgroup M) (L : Subgroup N), (∀ k ∈ KM, s k ∈ KP) → (∀ k ∈ KP, π k ∈ KM) → (∀ X, u X ∈ KP ↔ X ∈ L) → ∀ (TM CM : Subgroup M) (TP CP : Subgroup P), CM ≤ TM → (∀ p, p ∈ TP ↔ ∃ t ∈ TM, s t = p) → (∀ p, p ∈ CP ↔ ∃ t ∈ CM, s t = p) → (∀ q : M, TM ⊓ KM.map (MulAut.conj q).toMonoidHom ≤ CM) → ∀ (q : M) (X : N), (TP ⊓ KP.map (MulAut.conj (s q * u X)).toMonoidHom).relIndex CP = (TM ⊓ KM.map (MulAut.conj q).toMonoidHom).relIndex CM * (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM ⊓ KP.comap ((MulAut.conj (u X)⁻¹).toMonoidHom.comp s)).relIndex (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM) := by
  first | exact @GlobalTheory.relIndex_unfold_semidirect | exact GlobalTheory.relIndex_unfold_semidirect | (intros; apply GlobalTheory.relIndex_unfold_semidirect <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem algHom_eq_mul_pow_of_eq_localizationAway :
    ∀ (R' A S : Type) [CommRing R'] [CommRing A] [CommRing S] [Algebra R' A] [Algebra R' S]
    [Algebra.FiniteType R' A] (χ₁ χ₂ : A →ₐ[R'] S) (g : S),
    (∀ x, algebraMap S (Localization.Away g) (χ₁ x) = algebraMap S (Localization.Away g) (χ₂ x)) →
    ∃ N : ℕ, ∀ x, g ^ N * χ₁ x = g ^ N * χ₂ x := by
  intro R' A S _ _ _ _ _ _ χ₁ χ₂ g h
  have key : ∀ x, ∃ n : ℕ, g ^ n * χ₁ x = g ^ n * χ₂ x := by
    intro x
    obtain ⟨⟨c, hc⟩, hcx⟩ :=
      (IsLocalization.eq_iff_exists (Submonoid.powers g) (Localization.Away g)).1 (h x)
    obtain ⟨n, rfl⟩ := Submonoid.mem_powers_iff _ _ |>.1 hc
    exact ⟨n, hcx⟩
  choose n hn using key
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra R' A).FG)
  refine ⟨∑ x ∈ s, n x, fun x => ?_⟩
  set N := ∑ x ∈ s, n x
  have hx : x ∈ Algebra.adjoin R' (s : Set A) := by rw [hs]; exact Algebra.mem_top
  induction hx using Algebra.adjoin_induction with
  | mem x hxs =>
    have hle : n x ≤ N := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hxs
    rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc, mul_assoc, hn x]
  | algebraMap r => rw [AlgHom.commutes, AlgHom.commutes]
  | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _), mul_add, mul_add, hx, hy]
  | mul x y _ _ hx hy =>
    rw [map_mul, map_mul]
    calc g ^ N * (χ₁ x * χ₁ y) = χ₁ x * (g ^ N * χ₁ y) := by ring
      _ = χ₁ x * (g ^ N * χ₂ y) := by rw [hy]
      _ = (g ^ N * χ₁ x) * χ₂ y := by ring
      _ = (g ^ N * χ₂ x) * χ₂ y := by rw [hx]
      _ = g ^ N * (χ₂ x * χ₂ y) := by ring

end GlobalTheory
end

section


theorem _root_.GlobalTheory.T.localization_inverse_mod_f : ∀ (B D : Type) [CommRing B] [CommRing D] [Algebra B D] (f : B) (P : Ideal B) (Q : Ideal D) (g : D), Q.comap (algebraMap B D) = P → (∀ Q' : Ideal D, Q'.IsPrime → algebraMap B D f ∈ Q' → g ∉ Q' → Q' = Q) → ∀ s : B, s ∉ P → ∃ t : Localization.Away g, algebraMap B (Localization.Away g) s * t - 1 ∈ Ideal.span {algebraMap B (Localization.Away g) f} := by
  first | (exact @GlobalTheory.unitsMod_away_of_unique_prime) | (exact GlobalTheory.unitsMod_away_of_unique_prime) | (intros; apply GlobalTheory.unitsMod_away_of_unique_prime <;> assumption)
end

section


theorem _root_.GlobalTheory.T.localization_residue_approximation : ∀ (B D : Type) [CommRing B] [CommRing D] [Algebra B D] (P : Ideal B), P.IsMaximal → ∀ (Q : Ideal D) (g : D), g ∉ Q → Q.comap (algebraMap B D) = P → (∀ d : D, ∃ b : B, d - algebraMap B D b ∈ Q) → ∀ a : Localization.Away g, ∃ b : B, a - algebraMap B (Localization.Away g) b ∈ Q.map (algebraMap D (Localization.Away g)) := by
  first | (exact @GlobalTheory.residue_surj_localizationAway) | (exact GlobalTheory.residue_surj_localizationAway) | (intros; apply GlobalTheory.residue_surj_localizationAway <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_basicOpen_isUnit_of_notMem_map' : ∀ (S : Type) [CommRing S] (f₀ : S) (q : Ideal S), q.IsPrime → f₀ ∉ q → ∀ (J : Type) [Finite J] (m : J → Localization.Away f₀), (∀ i, m i ∉ Ideal.map (algebraMap S (Localization.Away f₀)) q) → ∃ f : S, f ∉ q ∧ ∃ φ : Localization.Away f₀ →ₐ[S] Localization.Away f, ∀ i, IsUnit (φ (m i)) := by
  first | exact @GlobalTheory.exists_basicOpen_isUnit_of_notMem_map | exact GlobalTheory.exists_basicOpen_isUnit_of_notMem_map | (intros; apply GlobalTheory.exists_basicOpen_isUnit_of_notMem_map <;> assumption)
end
