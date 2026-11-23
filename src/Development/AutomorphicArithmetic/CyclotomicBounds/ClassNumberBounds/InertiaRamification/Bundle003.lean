module

public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.Bundle001
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.Bundle002
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Algebra.Module.StablyFree.Basic
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
public import Mathlib.FieldTheory.Finite.Extension
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
public import Mathlib.NumberTheory.NumberField.Norm

@[expose] public section

section

namespace KStar.Ram

open NumberField DirichletCharacter IsCyclotomicExtension.Rat
open scoped Pointwise

variable {N : ℕ} [NeZero N] {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {N} ℚ K]

private theorem cycInertia_card_comap (l : ℕ) [hl : Fact l.Prime]
    (H : Subgroup (ZMod (ordCompl[l] N))ˣ) :
    Nat.card (H.comap (ZMod.unitsMap (Nat.ordCompl_dvd N l))) =
      Nat.totient (ordProj[l] N) * Nat.card H := by
  have hne : NeZero (ordCompl[l] N) := ⟨(Nat.ordCompl_pos l (NeZero.ne N)).ne'⟩
  have h1 := Subgroup.card_mul_index (H.comap (ZMod.unitsMap (Nat.ordCompl_dvd N l)))
  have h2 := Subgroup.card_mul_index H
  rw [Subgroup.index_comap_of_surjective _ (ZMod.unitsMap_surjective _)] at h1
  rw [Nat.card_eq_fintype_card (α := (ZMod N)ˣ), ZMod.card_units_eq_totient] at h1
  rw [Nat.card_eq_fintype_card (α := (ZMod (ordCompl[l] N))ˣ), ZMod.card_units_eq_totient] at h2
  have h3 : Nat.totient N = Nat.totient (ordProj[l] N) * Nat.totient (ordCompl[l] N) := by
    rw [← Nat.totient_mul (Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hl.out (NeZero.ne N))),
      Nat.ordProj_mul_ordCompl_eq_self]
  have h4 : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero h4)
  rw [h1, h3, ← h2, mul_assoc]

private theorem cycInertia_ef (l : ℕ) [hl : Fact l.Prime] :
    (Ideal.span {(l : ℤ)}).ramificationIdxIn (𝓞 K) = Nat.totient (ordProj[l] N) ∧
      (Ideal.span {(l : ℤ)}).inertiaDegIn (𝓞 K) = orderOf (l : ZMod (ordCompl[l] N)) := by
  have h := (Nat.ordProj_mul_ordCompl_eq_self N l).symm
  have hm : ¬ l ∣ ordCompl[l] N := Nat.not_dvd_ordCompl hl.out (NeZero.ne N)
  generalize ordCompl[l] N = m at h hm ⊢
  generalize N.factorization l = v at h ⊢
  cases v with
  | zero =>
    rw [pow_zero, one_mul] at h
    subst h
    exact ⟨by simpa using ramificationIdxIn_eq_of_not_dvd l K hm, inertiaDegIn_eq_of_not_dvd l K hm⟩
  | succ k =>
    exact ⟨by rw [ramificationIdxIn_eq N K h hm, Nat.totient_prime_pow_succ hl.out],
      inertiaDegIn_eq N K h hm⟩

private theorem cycInertia_key (l : ℕ) [hl : Fact l.Prime] (P : Ideal (𝓞 K)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(l : ℤ)})] (σ : Gal(K/ℚ)) (i : ℕ)
    (h : ∀ x : 𝓞 K, Ideal.Quotient.mk P (σ • x) = Ideal.Quotient.mk P x ^ l ^ i) :
    ZMod.unitsMap (Nat.ordCompl_dvd N l) (galEquivZMod N K σ) =
      ZMod.unitOfCoprime l (Nat.coprime_ordCompl hl.out (NeZero.ne N)) ^ i := by
  have hne : NeZero (ordCompl[l] N) := ⟨(Nat.ordCompl_pos l (NeZero.ne N)).ne'⟩
  have hζ := (IsCyclotomicExtension.zeta_spec N ℚ K).toInteger_isPrimitiveRoot
  have hη := hζ.pow (NeZero.pos N) (Nat.ordProj_mul_ordCompl_eq_self N l).symm
  set η := (IsCyclotomicExtension.zeta_spec N ℚ K).toInteger ^ (ordProj[l] N)
  have h₀ : IsPrimitiveRoot (Ideal.Quotient.mk P η) (ordCompl[l] N) := by
    refine hη.idealQuotient_mk
      (by simpa using Ideal.IsPrime.ne_top inferInstance) ?_
    rw [← Ideal.pow_inertiaDeg l]
    exact Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hl.out (NeZero.ne N))
  have hi := h η
  rw [galEquivZMod_smul_of_pow_eq N _ _
    ((hη.pow_eq_one_iff_dvd _).mpr (Nat.ordCompl_dvd N l)), map_pow,
    (h₀.isOfFinOrder (NeZero.ne _)).pow_inj_mod,
    ← h₀.eq_orderOf, ← ZMod.natCast_eq_natCast_iff', Nat.cast_pow] at hi
  ext
  rw [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, ← hi, ZMod.natCast_val]
  rfl

private theorem cycInertia_card_map (H : Subgroup Gal(K/ℚ)) :
    Nat.card (H.map (galEquivZMod N K).toMonoidHom) = Nat.card H :=
  Subgroup.card_map_of_injective (galEquivZMod N K).injective

theorem map_inertia_eq (l : ℕ) [Fact l.Prime] (P : Ideal (𝓞 K)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(l : ℤ)})] :
    (P.inertia Gal(K/ℚ)).map (galEquivZMod N K).toMonoidHom = inertiaUnits N l := by
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {N} ℚ K
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨σ, hσ, rfl⟩
    have := cycInertia_key (N := N) l P σ 0 (fun x => by
      rw [pow_zero, pow_one, Ideal.Quotient.eq]
      exact hσ x)
    rw [pow_zero] at this
    exact this
  · rw [cycInertia_card_map, Ideal.card_inertia_eq_ramificationIdxIn (Ideal.span {(l : ℤ)}),
      (cycInertia_ef (N := N) l).1, inertiaUnits, ← MonoidHom.comap_bot, cycInertia_card_comap]
    simp


attribute [local instance] Ideal.Quotient.field in
theorem map_stabilizer_eq (l : ℕ) [Fact l.Prime] (P : Ideal (𝓞 K)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(l : ℤ)})] :
    (MulAction.stabilizer Gal(K/ℚ) P).map (galEquivZMod N K).toMonoidHom = decompUnits N l := by
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {N} ℚ K
  have hP : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot (p := Ideal.span {(l : ℤ)})
    (by simpa using (Fact.out : l.Prime).ne_zero) P
  have : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨σ, hσ, rfl⟩
    let τ := IsFractionRing.stabilizerHom Gal(K/ℚ) (Ideal.span {(l : ℤ)}) P
      (ℤ ⧸ Ideal.span {(l : ℤ)}) (𝓞 K ⧸ P) ⟨σ, hσ⟩
    have : CharP (ℤ ⧸ Ideal.span {(l : ℤ)}) l := ringChar.of_eq <| Int.ringChar_idealQuot l
    have : Finite (𝓞 K ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP
    obtain ⟨i, hi⟩ :=
      FiniteField.exists_forall_apply_eq_pow (ℤ ⧸ Ideal.span {(l : ℤ)}) l (𝓞 K ⧸ P) τ
    have := cycInertia_key (N := N) l P σ i (fun x => by
      have h₁ := IsFractionRing.stabilizerHom_apply_apply_mk Gal(K/ℚ) (Ideal.span {(l : ℤ)}) P
        (ℤ ⧸ Ideal.span {(l : ℤ)}) (𝓞 K ⧸ P) ⟨σ, hσ⟩ x
      simp only [Algebra.algebraMap_self, RingHomCompTriple.comp_apply] at h₁
      have h2 := hi (Ideal.Quotient.mk P x)
      rwa [h₁, Int.card_ideal_quot] at h2)
    exact ⟨i, by simpa using this.symm⟩
  · rw [cycInertia_card_map, Ideal.card_stabilizer_eq (Ideal.span {(l : ℤ)}),
      (cycInertia_ef (N := N) l).1, (cycInertia_ef (N := N) l).2, decompUnits,
      cycInertia_card_comap, Nat.card_zpowers, ← orderOf_injective _ Units.coeHom_injective,
      Units.coeHom_apply, ZMod.coe_unitOfCoprime]

private theorem cycInertia_conj (σ : Gal(K/ℚ)) (hσ : galEquivZMod N K σ = -1) (φ : K →+* ℂ)
    (x : K) : φ (σ x) = starRingEnd ℂ (φ x) := by
  have hζ := IsCyclotomicExtension.zeta_spec N ℚ K
  have key : φ.toRatAlgHom.comp (σ : K →ₐ[ℚ] K) = ((starRingEnd ℂ).comp φ).toRatAlgHom := by
    apply (hζ.powerBasis ℚ).algHom_ext
    rw [IsPrimitiveRoot.powerBasis_gen]
    change φ (σ _) = starRingEnd ℂ (φ _)
    have h1 : ‖φ (IsCyclotomicExtension.zeta N ℚ K)‖ = 1 :=
      (hζ.map_of_injective φ.injective).norm'_eq_one (NeZero.ne N)
    rw [← Complex.inv_eq_conj h1, ← map_inv₀, galEquivZMod_apply_of_pow_eq N K σ hζ.pow_eq_one, hσ]
    congr 1
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, hζ.pow_eq_one_iff_dvd, ← ZMod.natCast_eq_zero_iff]
    simp
  exact DFunLike.congr_fun key x

theorem card_fieldChars (E : IntermediateField ℚ K) :
    Nat.card (fieldChars N E) = Module.finrank ℚ E ∧
      (IsTotallyReal E ↔ ∀ ψ ∈ fieldChars N E, ψ.Even) := by
  have : IsAbelianGalois ℚ K := IsCyclotomicExtension.isAbelianGalois {N} ℚ K
  have hmem : ∀ ψ, ψ ∈ fieldChars N E ↔
      ∀ σ ∈ E.fixingSubgroup, ψ (galEquivZMod N K σ) = 1 := by
    intro ψ
    rw [fieldChars, mem_annihilator_iff]
    constructor
    · intro h σ hσ
      exact h _ ⟨σ, hσ, rfl⟩
    · rintro h _ ⟨σ, hσ, rfl⟩
      exact h σ hσ
  have heq : fieldChars N E = intermediateFieldEquivSubgroupChar N K ℂ E := by
    ext ψ
    rw [hmem, mem_intermediateFieldEquivSubgroupChar_iff]
  refine ⟨by rw [heq, card_intermediateFieldEquivSubgroupChar], ?_⟩
  obtain ⟨σ, hσ⟩ := (galEquivZMod N K).surjective (-1)
  have heq2 : fieldChars N E = (subgroupGalEquivSubgroupChar N K ℂ E.fixingSubgroup).ofDual := by
    ext ψ
    rw [hmem, mem_subgroupGalEquivSubgroupChar_iff]
  clear hmem heq
  generalize fieldChars N E = X at heq2 ⊢
  have h1 : σ ∈ E.fixingSubgroup ↔ ∀ ψ ∈ X, ψ.Even := by
    have := mem_subgroupGalEquivSubgroupChar_symm_iff N K ℂ σ X
    rw [hσ] at this
    conv_lhs at this => rw [heq2, OrderDual.toDual_ofDual, OrderIso.symm_apply_apply]
    simpa [DirichletCharacter.Even] using this
  rw [← h1, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
    apply φ.injective
    rw [cycInertia_conj σ hσ]
    have := IsTotallyReal.complexEmbedding_isReal (φ.comp (algebraMap E K))
    rw [ComplexEmbedding.isReal_iff] at this
    exact RingHom.congr_fun this ⟨x, hx⟩
  · intro h
    refine ⟨fun w => ?_⟩
    rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq, ← ComplexEmbedding.lift_algebraMap_apply K w.embedding,
      ← cycInertia_conj σ hσ]
    congr 1
    exact h x x.2

end KStar.Ram
end

section

namespace KStar.Ram

open NumberField

private theorem rootNorm_powerBasis {F : Type*} [Field F] [Algebra ℚ F] (pb : PowerBasis ℚ F) :
    Algebra.norm ℚ (1 - pb.gen) = (minpoly ℚ pb.gen).eval 1 := by
  classical
  rw [← charpoly_leftMulMatrix, Matrix.eval_charpoly, Algebra.norm_eq_matrix_det pb.basis,
    map_sub, map_one, map_one]

private theorem rootNorm_field {K : Type*} [Field K] [NumberField K] (x : K) :
    ∃ k : ℕ, Module.finrank ℚ K = (minpoly ℚ x).natDegree * k ∧
      Algebra.norm ℚ (1 - x) = ((minpoly ℚ x).eval 1) ^ k := by
  have hx : IsIntegral ℚ x := .of_finite ℚ x
  refine ⟨Module.finrank (IntermediateField.adjoin ℚ {x}) K, ?_, ?_⟩
  · rw [← IntermediateField.adjoin.finrank hx, Module.finrank_mul_finrank]
  · have h1 : (1 - x : K) = algebraMap (IntermediateField.adjoin ℚ {x}) K
        (1 - IntermediateField.AdjoinSimple.gen ℚ x) := by
      simp
    have h2 := rootNorm_powerBasis (IntermediateField.adjoin.powerBasis hx)
    rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen] at h2
    rw [h1, ← Algebra.norm_norm (S := IntermediateField.adjoin ℚ {x}), Algebra.norm_algebraMap, map_pow]
    exact congrArg (· ^ Module.finrank (IntermediateField.adjoin ℚ {x}) K) h2

theorem padicValNat_absNorm_one_sub {K : Type*} [Field K] [NumberField K] (l : ℕ) [Fact l.Prime]
    {m : ℕ} (hm : 2 ≤ m) {η : 𝓞 K} (hη : IsPrimitiveRoot η m) :
    (padicValNat l (Ideal.absNorm (Ideal.span {1 - η})) : ℚ) =
      Module.finrank ℚ K * rootWeight l m := by
  haveI : NeZero m := ⟨by omega⟩
  have hηK : IsPrimitiveRoot (η : K) m :=
    hη.map_of_injective (FaithfulSMul.algebraMap_injective (𝓞 K) K)
  obtain ⟨k, hk, hnorm⟩ := rootNorm_field (η : K)
  rw [← Polynomial.cyclotomic_eq_minpoly_rat hηK (by omega), Polynomial.natDegree_cyclotomic] at hk
  rw [← Polynomial.cyclotomic_eq_minpoly_rat hηK (by omega)] at hnorm
  have hcQ : (Polynomial.cyclotomic m ℚ).eval 1 = (((Polynomial.cyclotomic m ℤ).eval 1 : ℤ) : ℚ) := by
    rw [← Polynomial.map_cyclotomic_int, ← Int.cast_one, Polynomial.eval_intCast_map, eq_intCast,
      Int.cast_one]
  have hnormZ : Algebra.norm ℤ (1 - η) = ((Polynomial.cyclotomic m ℤ).eval 1) ^ k := by
    apply Int.cast_injective (α := ℚ)
    rw [Algebra.coe_norm_int, Int.cast_pow, ← hcQ, ← hnorm]
    push_cast
    rfl
  have hv : (padicValNat l ((Polynomial.cyclotomic m ℤ).eval 1).natAbs : ℚ) =
      m.totient * rootWeight l m := by
    by_cases hpp : ∃ p j, p.Prime ∧ m = p ^ (j + 1)
    · obtain ⟨p, j, hp, rfl⟩ := hpp
      haveI := Fact.mk hp
      rw [Polynomial.eval_one_cyclotomic_prime_pow, Int.natAbs_natCast]
      have hne : p ^ (j + 1) ≠ 1 := fun h => by rw [h] at hm; norm_num at hm
      by_cases hpl : p = l
      · subst hpl
        rw [Nat.padicValNat_def, Nat.Prime.multiplicity_self, rootWeight,
          if_pos ⟨hne, j + 1, rfl⟩]
        have ht : ((p ^ (j + 1)).totient : ℚ) ≠ 0 := by
          exact_mod_cast (Nat.totient_pos.mpr (by positivity)).ne'
        rw [Nat.cast_one, mul_one_div, div_self ht]
      · rw [Nat.padicValNat_def, multiplicity_primes (Ne.symm hpl), rootWeight, if_neg]
        · simp
        · rintro ⟨-, s, hs⟩
          apply hpl
          rcases s with _ | s
          · rw [pow_zero] at hs
            exact absurd hs hne
          · have hd : p ∣ l ^ (s + 1) := by
              rw [← hs]
              exact dvd_pow_self p (Nat.succ_ne_zero j)
            exact (Nat.prime_dvd_prime_iff_eq hp (Fact.out : l.Prime)).mp (hp.dvd_of_dvd_pow hd)
    · have h1 : Polynomial.eval 1 (Polynomial.cyclotomic m ℤ) = 1 := by
        apply Polynomial.eval_one_cyclotomic_not_prime_pow
        intro p hp j hj
        rcases j with _ | j
        · rw [pow_zero] at hj
          omega
        · exact hpp ⟨p, j, hp, hj.symm⟩
      rw [h1, rootWeight, if_neg]
      · simp [_root_.Nat.padicValNat_def (n := 1)]
      · rintro ⟨-, s, hs⟩
        rcases s with _ | s
        · rw [pow_zero] at hs
          omega
        · exact hpp ⟨l, s, Fact.out, hs⟩
  rw [Nat.padicValNat_def] at hv
  rw [Ideal.absNorm_span_singleton, hnormZ, Int.natAbs_pow, Nat.padicValNat_def,
    Nat.multiplicity_pow, hk, Nat.cast_mul, Nat.cast_mul, hv]
  ring

end KStar.Ram
end

section

namespace KStar.Ram

open DirichletCharacter

variable {N : ℕ} [NeZero N] (l : ℕ) [Fact l.Prime]

private lemma unitsMap_eq_one_iff_modEq {d : ℕ} (h : d ∣ N) (x : (ZMod N)ˣ) :
    ZMod.unitsMap h x = 1 ↔ (x : ZMod N).val ≡ 1 [MOD d] := by
  rw [← Units.val_inj, ZMod.unitsMap_val, ← ZMod.natCast_eq_natCast_iff, ZMod.natCast_val]
  simp

private lemma crt_fst (x : ZMod N) :
    (crtEquiv N l x).1 = ZMod.castHom (Nat.ordProj_dvd N l) (ZMod (ordProj[l] N)) x :=
  RingHom.congr_fun (RingHom.ext_zmod
    ((RingHom.fst _ _).comp (crtEquiv N l).toRingHom)
    (ZMod.castHom (Nat.ordProj_dvd N l) (ZMod (ordProj[l] N)))) x

private lemma crt_snd (x : ZMod N) :
    (crtEquiv N l x).2 = ZMod.castHom (Nat.ordCompl_dvd N l) (ZMod (ordCompl[l] N)) x :=
  RingHom.congr_fun (RingHom.ext_zmod
    ((RingHom.snd _ _).comp (crtEquiv N l).toRingHom)
    (ZMod.castHom (Nat.ordCompl_dvd N l) (ZMod (ordCompl[l] N)))) x

private lemma localUnits_val (u : (ZMod (ordProj[l] N))ˣ) :
    ((localUnits N l u : (ZMod N)ˣ) : ZMod N) =
      (crtEquiv N l).symm ((u : ZMod (ordProj[l] N)), 1) := rfl

private lemma proj_localUnits (u : (ZMod (ordProj[l] N))ˣ) :
    ZMod.unitsMap (Nat.ordProj_dvd N l) (localUnits N l u) = u := by
  apply Units.ext
  have h := crt_fst l ((localUnits N l u : (ZMod N)ˣ) : ZMod N)
  rw [localUnits_val, RingEquiv.apply_symm_apply] at h
  exact h.symm

private lemma compl_localUnits (u : (ZMod (ordProj[l] N))ˣ) :
    ZMod.unitsMap (Nat.ordCompl_dvd N l) (localUnits N l u) = 1 := by
  apply Units.ext
  have h := crt_snd l ((localUnits N l u : (ZMod N)ˣ) : ZMod N)
  rw [localUnits_val, RingEquiv.apply_symm_apply] at h
  exact h.symm

private lemma localUnits_proj (x : (ZMod N)ˣ)
    (hx : ZMod.unitsMap (Nat.ordCompl_dvd N l) x = 1) :
    localUnits N l (ZMod.unitsMap (Nat.ordProj_dvd N l) x) = x := by
  apply Units.ext
  rw [localUnits_val, RingEquiv.symm_apply_eq]
  apply Prod.ext
  · rw [crt_fst]; rfl
  · rw [crt_snd]; exact (congrArg Units.val hx).symm

theorem localUnits_spec :
    Function.Injective (localUnits N l) ∧ (localUnits N l).range = inertiaUnits N l ∧
      ∀ u, ZMod.unitsMap (Nat.ordProj_dvd N l) (localUnits N l u) = u := by
  refine ⟨Function.LeftInverse.injective (proj_localUnits l), ?_, proj_localUnits l⟩
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    exact compl_localUnits l u
  · intro hx
    exact ⟨_, localUnits_proj l x hx⟩

private lemma localPart_toUnitHom (ψ : DirichletCharacter ℂ N) :
    MulChar.toUnitHom (localPart N l ψ) = (MulChar.toUnitHom ψ).comp (localUnits N l) := by
  ext u
  simp [localPart]

private lemma unitsMap_trans {a b c : ℕ} (hab : a ∣ b) (hbc : b ∣ c) (x : (ZMod c)ˣ) :
    ZMod.unitsMap hab (ZMod.unitsMap hbc x) = ZMod.unitsMap (hab.trans hbc) x := by
  rw [← ZMod.unitsMap_comp hab hbc]; rfl

private lemma conductor_localPart_dvd_iff (ψ : DirichletCharacter ℂ N) (t : ℕ)
    (ht : t ≤ N.factorization l) :
    (localPart N l ψ).conductor ∣ l ^ t ↔ condExp l ψ ≤ t := by
  have hl : l.Prime := Fact.out
  have hN : N ≠ 0 := NeZero.ne N
  have : NeZero (ordProj[l] N) := ⟨(Nat.ordProj_pos N l).ne'⟩
  have h1 : l ^ t ∣ ordProj[l] N := pow_dvd_pow l ht
  have h2 : l ^ t * ordCompl[l] N ∣ N := by
    conv_rhs => rw [← Nat.ordProj_mul_ordCompl_eq_self N l]
    exact Nat.mul_dvd_mul_right h1 _
  have hcop : (l ^ t).Coprime (ordCompl[l] N) :=
    Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hl hN)
  have hker : ∀ x : (ZMod N)ˣ, ZMod.unitsMap h2 x = 1 ↔
      ZMod.unitsMap (h1.trans (Nat.ordProj_dvd N l)) x = 1 ∧
        ZMod.unitsMap (Nat.ordCompl_dvd N l) x = 1 := by
    intro x
    simp only [unitsMap_eq_one_iff_modEq]
    exact (Nat.modEq_and_modEq_iff_modEq_mul hcop).symm
  have key : (localPart N l ψ).conductor ∣ l ^ t ↔ ψ.conductor ∣ l ^ t * ordCompl[l] N := by
    rw [← mem_conductorSet_iff_conductor_dvd _ h1, ← mem_conductorSet_iff_conductor_dvd _ h2,
      mem_conductorSet_iff, mem_conductorSet_iff, factorsThrough_iff_ker_unitsMap h1,
      factorsThrough_iff_ker_unitsMap h2, localPart_toUnitHom]
    constructor
    · intro h x hx
      rw [MonoidHom.mem_ker, hker] at hx
      have := h (x := ZMod.unitsMap (Nat.ordProj_dvd N l) x)
        (by rw [MonoidHom.mem_ker, unitsMap_trans]; exact hx.1)
      rwa [MonoidHom.mem_ker, MonoidHom.comp_apply, localUnits_proj l x hx.2] at this
    · intro h u hu
      rw [MonoidHom.mem_ker] at hu
      refine h (x := localUnits N l u) ?_
      rw [MonoidHom.mem_ker, hker]
      refine ⟨?_, compl_localUnits l u⟩
      rw [← unitsMap_trans h1 (Nat.ordProj_dvd N l), proj_localUnits, hu]
  rw [key, condExp]
  have hc : ψ.conductor ≠ 0 := conductor_ne_zero ψ
  have hcN : ψ.conductor ∣ N := conductor_dvd_level ψ
  have hN' : ordCompl[l] N ≠ 0 := (Nat.ordCompl_pos l hN).ne'
  have hlt : l ^ t ≠ 0 := pow_ne_zero _ hl.ne_zero
  constructor
  · intro h
    have := (Nat.factorization_le_iff_dvd hc (mul_ne_zero hlt hN')).2 h l
    rw [Nat.factorization_mul hlt hN', Nat.factorization_ordCompl, hl.factorization_pow] at this
    simpa using this
  · intro h
    rw [← Nat.ordProj_mul_ordCompl_eq_self ψ.conductor l]
    exact Nat.mul_dvd_mul (pow_dvd_pow l h) (Nat.ordCompl_dvd_ordCompl_of_dvd hcN l)

theorem localPart_eq_one_iff (ψ : DirichletCharacter ℂ N) :
    (localPart N l ψ = 1 ↔ ∀ u ∈ inertiaUnits N l, ψ (u : ZMod N) = 1) ∧
      (localPart N l ψ = 1 ↔ ¬ l ∣ ψ.conductor) := by
  have hl : l.Prime := Fact.out
  have : NeZero (ordProj[l] N) := ⟨(Nat.ordProj_pos N l).ne'⟩
  constructor
  · rw [← (localUnits_spec l).2.1]
    constructor
    · rintro h _ ⟨u, rfl⟩
      have := congrArg (fun χ : DirichletCharacter ℂ (ordProj[l] N) =>
        χ (u : ZMod (ordProj[l] N))) h
      simpa [localPart] using this
    · intro h
      ext u
      simpa [localPart] using h _ ⟨u, rfl⟩
  · have := conductor_localPart_dvd_iff l ψ 0 (Nat.zero_le _)
    rw [pow_zero, Nat.dvd_one, Nat.le_zero] at this
    rw [eq_one_iff_conductor_eq_one, this, condExp,
      hl.dvd_iff_one_le_factorization (conductor_ne_zero ψ)]
    omega

end KStar.Ram
end
