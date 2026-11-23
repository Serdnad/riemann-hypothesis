module

public import GroundTheory.ProfiniteCohomology.RestrictedRamification.Bundle009
public import GroundTheory.ProfiniteCohomology.LocalClassFormation.CupSymbolNorm
public import GroundTheory.ProfiniteCohomology.PoincareDuality.Torsion
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.Bundle002
public import GroundTheory.GlobalFields.CyclotomicCharacters.Character
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseChangePlaces
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseDefs
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseFormal
public import GroundTheory.ProfiniteCohomology.LocalTateDuality.TensorHomDualRepRootsOfUnityIsoCartierPairing
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.Finite
import GroundTheory.ProfiniteCohomology.RestrictedRamification.FiniteOpen
import GroundTheory.ProfiniteCohomology.RestrictedRamification.Bundle005
import GroundTheory.ProfiniteCohomology.RestrictedRamification.SUnits
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain IntermediateField GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.LocalField
  GroundTheory.Global.IdeleGroup Function

noncomputable section

universe u

section QZ

variable {G : Type} [Group G] [TopologicalSpace G] {n : ℕ}

def charQZ (χ : ContinuousMonoidHom G (Multiplicative (ZMod n))) : Additive G →ₜ+ QZ where
  toFun x := zmodToQZ n (Multiplicative.toAdd (χ (Additive.toMul x)))
  map_zero' := by simp
  map_add' x y := by simp [toMul_add, map_mul]
  continuous_toFun :=
    (continuous_of_discreteTopology (f := fun z : Multiplicative (ZMod n) ↦ zmodToQZ n z.toAdd)).comp
      (χ.continuous.comp continuous_toMul)

theorem charQZ_apply (χ : ContinuousMonoidHom G (Multiplicative (ZMod n))) (g : G) :
    charQZ χ (Additive.ofMul g) = zmodToQZ n (Multiplicative.toAdd (χ g)) :=
  rfl

end QZ

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω] [IsGalois K Ω]

theorem decompHom_apply_of_localArtinMap (v : HeightOneSpectrum (𝓞 K))
    (ι : Ω →ₐ[K] AlgebraicClosure (v.adicCompletion K)) (b : (v.adicCompletion K)ˣ)
    {g : Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K)}
    (hg : ∀ (y : AlgebraicClosure (v.adicCompletion K))
      (hy : y ∈ maximalAbelianExtension (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))),
      g y = (localArtinMap (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)) b ⟨y, hy⟩ :
        AlgebraicClosure (v.adicCompletion K)))
    (y : Ω) (hy : y ∈ maximalAbelianExtension K Ω) :
    decompHom (v.adicCompletion K) ι g y =
      (artinMap K Ω (IdeleClassGroup.mk K (finiteEmbedding v b)) ⟨y, hy⟩ : Ω) := by
  obtain ⟨L, _, _, hyL⟩ := exists_finite_abelian_mem hy
  have := NumberField.of_module_finite K L
  let j : L →ₐ[K] AlgebraicClosure (v.adicCompletion K) := ι.comp L.val
  have e := artinMap_finiteEmbedding_apply L v (placeOfAlgHom j) (completionEmbeddingOfAlgHom j) b
    ⟨y, hyL⟩
  have hmem : ι y ∈ maximalAbelianExtension (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)) := by
    have := apply_mem_maximalAbelianExtension (completionEmbeddingOfAlgHom j)
      (algebraMap L ((placeOfAlgHom j).1.adicCompletion L) ⟨y, hyL⟩)
    rwa [completionEmbeddingOfAlgHom_algebraMap] at this
  have e2 : (localArtinMap (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)) b ⟨ι y, hmem⟩ :
      AlgebraicClosure (v.adicCompletion K)) =
      completionEmbeddingOfAlgHom j (algebraMap L ((placeOfAlgHom j).1.adicCompletion L)
        (restrictAb L (le_maximalAbelianExtension L)
          (artinMap K Ω (IdeleClassGroup.mk K (finiteEmbedding v b))) ⟨y, hyL⟩)) := by
    rw [e]
    exact congrArg (fun z ↦ (localArtinMap (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)) b z :
      AlgebraicClosure (v.adicCompletion K)))
      (Subtype.ext (completionEmbeddingOfAlgHom_algebraMap j ⟨y, hyL⟩).symm)
  have key : ι (decompHom (v.adicCompletion K) ι g y) =
      ι (artinMap K Ω (IdeleClassGroup.mk K (finiteEmbedding v b)) ⟨y, hy⟩ : Ω) := by
    rw [decompHom_apply, hg _ hmem, e2, completionEmbeddingOfAlgHom_algebraMap]
    change ι ((restrictAb L (le_maximalAbelianExtension L)
      (artinMap K Ω (IdeleClassGroup.mk K (finiteEmbedding v b))) ⟨y, hyL⟩ : L) : Ω) = _
    rw [restrictAb_apply]
  exact ι.injective key

theorem liftNormal_localArtinMap_apply (v : HeightOneSpectrum (𝓞 K)) (b : (v.adicCompletion K)ˣ)
    (y : AlgebraicClosure (v.adicCompletion K))
    (hy : y ∈ maximalAbelianExtension (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))) :
    (localArtinMap (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)) b).liftNormal
        (AlgebraicClosure (v.adicCompletion K)) y =
      (localArtinMap (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)) b ⟨y, hy⟩ :
        AlgebraicClosure (v.adicCompletion K)) :=
  AlgEquiv.liftNormal_commutes (localArtinMap (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)) b)
    (AlgebraicClosure (v.adicCompletion K)) ⟨y, hy⟩

variable {S : Set (HeightOneSpectrum (𝓞 K))} {n : ℕ}

theorem charEquiv_finiteEmbedding [IsAlgClosure K Ω] (hS : S.Finite) [NeZero n]
    (h : Odd n ∨ IsTotallyComplex K)
    (χ : ContinuousMonoidHom (galUnramifiedOutside K Ω S) (Multiplicative (ZMod n)))
    (v : HeightOneSpectrum (𝓞 K)) (ι : Ω →ₐ[K] AlgebraicClosure (v.adicCompletion K))
    (b : (v.adicCompletion K)ˣ) {g : Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K)}
    (hg : ∀ (y : AlgebraicClosure (v.adicCompletion K))
      (hy : y ∈ maximalAbelianExtension (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))),
      g y = (localArtinMap (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)) b ⟨y, hy⟩ :
        AlgebraicClosure (v.adicCompletion K))) :
    charEquiv Ω hS h χ (SIdeleClassGroup.mk S (finiteEmbedding v b)) =
      χ (decompHomS (v.adicCompletion K) S ι g) := by
  rw [charEquiv_mk_eq hS h χ _ (decompHom (v.adicCompletion K) ι g)
    (decompHom_apply_of_localArtinMap v ι b hg), decompHomS_eq]
  rfl

section Cup

variable {K : Type} [Field K] [NumberField K] {Ω : Type} [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} {n : ℕ}

theorem brauerInvZ_galCupClass_decompHomS [IsAlgClosure K Ω] (hS : S.Finite) [NeZero n]
    (h : Odd n ∨ IsTotallyComplex K)
    (χ : ContinuousMonoidHom (galUnramifiedOutside K Ω S) (Multiplicative (ZMod n)))
    (v : HeightOneSpectrum (𝓞 K)) (ι : Ω →ₐ[K] AlgebraicClosure (v.adicCompletion K))
    (a : (v.adicCompletion K)ˣ) :
    brauerInvZOfIsSepClosure (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))
        (galCupClass (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))
          (contCharComp (charQZ χ) (decompHomS (v.adicCompletion K) S ι)
            (continuous_decompHomS (Kv := v.adicCompletion K) S ι)) a) =
      zmodToQZ n (Multiplicative.toAdd (charEquiv Ω hS h χ (SIdeleClassGroup.mk S (finiteEmbedding v a)))) := by
  rw [brauerInvZOfIsSepClosure_galCupClass _ a _ (liftNormal_localArtinMap_apply v a),
    contCharComp_apply, charEquiv_finiteEmbedding hS h χ v ι a (liftNormal_localArtinMap_apply v a)]
  rfl

local notation "ℚ̄" => AlgebraicClosure ℚ

theorem placeInv_galCupClass_decompHomS {K : FiniteSubfield} {S : Set (HeightOneSpectrum (𝓞 K.1))}
    (hS : S.Finite) [NeZero n] (h : Odd n ∨ IsTotallyComplex K.1)
    (χ : ContinuousMonoidHom (galUnramifiedOutside K.1 ℚ̄ S) (Multiplicative (ZMod n)))
    (w : HeightOneSpectrum (𝓞 K.1)) (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure (w.adicCompletion K.1))
    (a : (w.adicCompletion K.1)ˣ) :
    placeInv (K := K) (.inr w)
        (galCupClass (w.adicCompletion K.1) (AlgebraicClosure (w.adicCompletion K.1))
          (contCharComp (charQZ χ) (decompHomS (w.adicCompletion K.1) S ι)
            (continuous_decompHomS (Kv := w.adicCompletion K.1) S ι)) a) =
      zmodToQZ n (Multiplicative.toAdd (charEquiv ℚ̄ hS h χ (SIdeleClassGroup.mk S (finiteEmbedding w a)))) :=
  brauerInvZ_galCupClass_decompHomS hS h χ w ι a

end Cup

section Frobenius

variable {K : FiniteSubfield} {S : Set (HeightOneSpectrum (𝓞 K.1))} {n : ℕ}


end Frobenius

end

end GroundTheory.ProfCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField CategoryTheory GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

theorem finite_of_exact_of_finite {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [Finite A]
    [Finite C] (g : A →+ B) (f : B →+ C) (hex : ∀ b, f b = 0 → ∃ a, g a = b) : Finite B := by
  rw [f.finite_iff_finite_ker_range]
  refine ⟨?_, inferInstance⟩
  have hsub : (f.ker : Set B) ⊆ Set.range g := fun b hb => hex b hb
  exact ((Set.finite_range g).subset hsub).to_subtype

theorem exists_natCast_mem_place (K : FiniteSubfield) {ℓ : ℕ} (hℓ : ℓ.Prime) :
    ∃ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal := by
  have hnu : ¬ IsUnit ((ℓ : ℕ) : 𝓞 K.1) := by
    rintro ⟨u, hu⟩
    have h : ((ℓ : ℕ) : 𝓞 K.1) * ((u⁻¹ : (𝓞 K.1)ˣ) : 𝓞 K.1) = 1 := by
      rw [← hu]
      exact u.mul_inv
    have hK : ((ℓ : ℕ) : K.1) * (((u⁻¹ : (𝓞 K.1)ˣ) : 𝓞 K.1) : K.1) = 1 := by
      have := congrArg (algebraMap (𝓞 K.1) K.1) h
      rwa [map_mul, map_natCast, map_one] at this
    have hint : IsIntegral ℤ (((u⁻¹ : (𝓞 K.1)ˣ) : 𝓞 K.1) : K.1) :=
      NumberField.RingOfIntegers.isIntegral_coe _
    have heq : (((u⁻¹ : (𝓞 K.1)ˣ) : 𝓞 K.1) : K.1) = algebraMap ℚ K.1 (1 / ℓ) := by
      rw [eq_inv_of_mul_eq_one_right hK]
      simp
    rw [heq, isIntegral_algebraMap_iff ] at hint
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    have hℓ0 : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
    have hy' : ((ℓ * y : ℤ) : ℚ) = 1 := by
      rw [Int.cast_mul, show ((y : ℤ) : ℚ) = algebraMap ℤ ℚ y from rfl, hy]
      field_simp
      norm_cast
    have h2 : (ℓ : ℤ) * y = 1 := by exact_mod_cast hy'
    have hunit := Int.eq_one_or_neg_one_of_mul_eq_one h2
    have hℓ1 : (ℓ : ℤ) ≠ 1 := by exact_mod_cast hℓ.one_lt.ne'
    have hℓm : (ℓ : ℤ) ≠ -1 := by omega
    exact hunit.elim hℓ1 hℓm
  have hne : Ideal.span {((ℓ : ℕ) : 𝓞 K.1)} ≠ ⊤ := fun h => hnu (Ideal.span_singleton_eq_top.1 h)
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hℓM : ((ℓ : ℕ) : 𝓞 K.1) ∈ M := hle (Ideal.subset_span rfl)
  have hMbot : M ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hℓM
    have : ((ℓ : ℕ) : K.1) = 0 := by
      have := congrArg (algebraMap (𝓞 K.1) K.1) hℓM
      rwa [map_natCast, map_zero] at this
    exact hℓ.ne_zero (by exact_mod_cast this)
  exact ⟨⟨M, hM.isPrime, hMbot⟩, hℓM⟩

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1))) (n ℓ k : ℕ) (hℓ : ℓ.Prime)
  (hnk : n = ℓ ^ k) (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)


include hℓ hS in
theorem nonempty_of_natCast_mem : Nonempty S :=
  (exists_natCast_mem_place K hℓ).elim fun v hv => ⟨⟨v, hS v hv⟩⟩


include hnk hS in
theorem mem_of_natCast_pow_mem : ∀ v : HeightOneSpectrum (𝓞 K.1), ((n : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S := by
  intro v hv
  subst hnk
  rw [Nat.cast_pow] at hv
  exact hS v (v.isPrime.mem_of_pow_mem k hv)

variable [NeZero n] (hodd : Odd n ∨ IsTotallyComplex K.1)


include hnk hS hodd in
theorem subsingleton_gsRoots_three : Subsingleton (cohomology (gsRoots S n) 3) :=
  subsingleton_cohomology_of_cdp_le_two (NeZero.ne n)
    (fun _ hp hpn => cdp_galUnramifiedOutside_le_two_of_dvd K S (NeZero.ne n)
      (mem_of_natCast_pow_mem S n ℓ k hnk hS) hodd hp hpn) (gsRoots S n) (nsmul_gsRoots S n) le_rfl


include hnk hS hodd in
theorem subsingleton_zmodRep_gs_three :
    Subsingleton (cohomology (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 3) :=
  subsingleton_cohomology_of_cdp_le_two (NeZero.ne n)
    (fun _ hp hpn => cdp_galUnramifiedOutside_le_two_of_dvd K S (NeZero.ne n)
      (mem_of_natCast_pow_mem S n ℓ k hnk hS) hodd hp hpn) (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n)
    (nsmul_zmodRep_eq_zero _ n) le_rfl

omit [NeZero n] in
theorem natCard_zmodRep (G : Type) [Group G] : Nat.card (zmodRep.{0} G n) = n := by
  change Nat.card (ULift.{0} (ZMod n)) = n
  rw [Nat.card_ulift, Nat.card_zmod]

variable [Finite S]


include hnk hS in
theorem finite_zmodRep_gs_one : Finite (cohomology (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1) := by
  have : Finite (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) := inferInstanceAs (Finite (ULift.{0} (ZMod n)))
  refine finite_cohomology_gs K S _ (fun v hv => ?_) 1 (by norm_num)
  rw [natCard_zmodRep] at hv
  exact mem_of_natCast_pow_mem S n ℓ k hnk hS v hv

variable (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))


omit [Finite S] in
include hnk hS in
theorem natCard_gsRoots : Nat.card (gsRoots S n) = n := by
  change Nat.card (Additive (rootsOfUnity n (maxUnramifiedOutside K.1 ℚ̄ S))) = n
  rw [Nat.card_congr Additive.toMul]
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot ℚ̄ n
  have hmem : ζ ∈ maxUnramifiedOutside K.1 ℚ̄ S :=
    mem_maxUnramifiedOutside_of_pow_eq_one S (NeZero.ne n)
      (fun v hv h => hv (mem_of_natCast_pow_mem S n ℓ k hnk hS v h)) hζ.pow_eq_one
  have hζS : IsPrimitiveRoot (⟨ζ, hmem⟩ : maxUnramifiedOutside K.1 ℚ̄ S) n :=
    IsPrimitiveRoot.of_map_of_injective (f := (maxUnramifiedOutside K.1 ℚ̄ S).val) hζ
      Subtype.val_injective
  exact hζS.card_rootsOfUnity


omit [Finite S] in
include hnk hS in
theorem finite_gsRoots_local_one (v : S) :
    Finite (cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) 1) := by
  have : Finite (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) :=
    inferInstanceAs (Finite (Additive (rootsOfUnity n (maxUnramifiedOutside K.1 ℚ̄ S))))
  refine finite_cohomology_localField _ ?_ 1
  change ((Nat.card (gsRoots S n) : ℕ) : (v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) ≠ 0
  rw [natCard_gsRoots S n ℓ k hnk hS]
  exact Nat.cast_ne_zero.2 (NeZero.ne n)


include hnk hS in
theorem finite_gsRoots_compact_two [Fintype S] :
    Finite (compactCohomologyRes (gsFinFamily S ιs) (gsRoots S n) 2) := by
  have : ∀ v : S, Finite (cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) 1) :=
    finite_gsRoots_local_one S n ℓ k hnk hS ιs
  have hA : Finite (ModuleCat.of (ULift.{0} ℤ)
      (∀ v : S, cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) 1)) :=
    inferInstanceAs (Finite (∀ v : S, cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) 1))
  have hC : Finite (cohomology (gsRoots S n) 2) :=
    finite_cohomology_rootsOfUnity K S n (NeZero.ne n) (mem_of_natCast_pow_mem S n ℓ k hnk hS) 2 le_rfl
  exact finite_of_exact_of_finite
    (localToCompact (gsFinFamily S ιs) (gsRoots S n) (fun v => Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n))
      (fun _ => 𝟙 _) 1).hom.toAddMonoidHom
    (compactToGlobal (gsFinFamily S ιs) (gsRoots S n) (fun v => Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n))
      (fun _ => 𝟙 _) 2).hom.toAddMonoidHom
    (fun b hb => (ShortComplex.moduleCat_exact_iff_ker_sub_range _).1
      (compactCohomology_exact_compact (gsFinFamily S ιs) (gsRoots S n) _ (fun _ => 𝟙 _) 1) hb)

end

section PlacesOver

variable {K L : FiniteSubfield} [Fact (K ≤ L)] (S : Set (HeightOneSpectrum (𝓞 K.1)))

@[instance_reducible]
noncomputable def fintypePlacesOver [Finite S] : Fintype (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) :=
  (placesOver_finite (Set.toFinite S)).fintype

theorem nonempty_placesOver_of_natCast_mem {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S) :
    Nonempty (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) :=
  nonempty_of_natCast_mem (placesOver S) ℓ hℓ fun _ hw => mem_placesOver_of_natCast_mem hS hw

end PlacesOver

end GroundTheory.ProfCoh
end
