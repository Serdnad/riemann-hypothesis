module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IsClassFieldHilbert
public import GroundTheory.GlobalFields.IdeleGroups.LocalNorms
public import Mathlib.NumberTheory.NumberField.CMField
import GroundTheory.GlobalFields.InfiniteNormIndex.LocalSymbol
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.NumberField.Completion.Ramification
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.StickelbergerAt
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.GaloisCohomology.Statement
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

theorem UpperTheory.V.FW.conjEq :
    ∀ (M : ℕ) [NeZero M] (L : Type) [Field L] [NumberField L] [IsCyclotomicExtension {M} ℚ L] [IsCMField L], (sg M L (-1)).toRingEquiv = cE L ∧ clA M L (-1) = clMap (cE L) := by
  intro M _ L _ _ _ _
  have hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta M ℚ L) M :=
    IsCyclotomicExtension.zeta_spec M ℚ L
  set ζ := IsCyclotomicExtension.zeta M ℚ L
  have h1 : sg M L (-1) ζ = ζ⁻¹ := by
    rw [sg_apply M L _ hζ.pow_eq_one]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ, hζ.pow_eq_one_iff_dvd, ← ZMod.natCast_eq_zero_iff]
    push_cast
    simp
  have h2 : cE L ζ = ζ⁻¹ := by
    obtain ⟨φ⟩ := (inferInstance : Nonempty (L →+* ℂ))
    refine eq_inv_of_mul_eq_one_left ?_
    apply φ.injective
    have hz : ‖φ ζ‖ = 1 := (hζ.map_of_injective φ.injective).norm'_eq_one (NeZero.ne M)
    rw [map_mul, map_one, cE]
    simp only [NumberField.IsCMField.complexEmbedding_complexConj, IsCMField.complexEmbedding_complexConj,
      AlgEquiv.coe_toRingEquiv, RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv]
    rw [Complex.conj_mul', hz]
    simp
  have hc : sg M L (-1) = AlgEquiv.ofRingEquiv (f := cE L) (fun q => by simp) := by
    apply AlgEquiv.coe_algHom_injective
    apply (hζ.powerBasis ℚ).algHom_ext
    simp only [IsPrimitiveRoot.powerBasis_gen, AlgEquiv.coe_algHom]
    rw [h1]
    exact h2.symm
  have key : (sg M L (-1)).toRingEquiv = cE L := by
    rw [hc]
    ext x
    rfl
  refine ⟨key, ?_⟩
  rw [clA, ← map_inv, inv_neg_one, key]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

private theorem unrJ_prime (L : Type) [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) :
    ∃ p : ℕ, p.Prime ∧ (p : 𝓞 L) ∈ w.asIdeal := by
  have := w.isPrime
  have : Finite (𝓞 L ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  refine ⟨ringChar (𝓞 L ⧸ w.asIdeal), CharP.char_is_prime (𝓞 L ⧸ w.asIdeal) _, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact (ringChar.spec _ _).2 dvd_rfl

private theorem unrJ_arith (f n p : ℕ) (hp : p.Prime) (hf : Odd f) (h1 : 1 < f) (hn : 2 ≤ n) :
    ¬ (f * 2 ^ n - 1 ≡ 1 [MOD ordCompl[p] (f * 2 ^ n)]) := by
  intro h
  have hM : f * 2 ^ n ≠ 0 := by positivity
  have hd : ordCompl[p] (f * 2 ^ n) ∣ 2 := by
    have h2 := h.add_right 1
    rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hM)] at h2
    exact (h2.dvd_iff dvd_rfl).1 (Nat.ordCompl_dvd _ _)
  have key : ∀ d : ℕ, d ∣ f * 2 ^ n → ¬ p ∣ d → d ∣ 2 := fun d hd1 hd2 =>
    (Nat.dvd_ordCompl_of_dvd_not_dvd hd1 hd2).trans hd
  by_cases h2 : p = 2
  · subst h2
    have h3 := Nat.le_of_dvd two_pos (key f (dvd_mul_right _ _) hf.not_two_dvd_nat)
    obtain ⟨k, rfl⟩ := hf
    omega
  · have h4 : 2 ^ 2 ∣ f * 2 ^ n := (pow_dvd_pow 2 hn).mul_left f
    have h3 := key _ h4 fun h5 => h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h5))
    omega

private theorem unrJ_conj (L : Type) [Field L] [NumberField L] [IsCMField L] (M : ℕ) (hM : M ≠ 0) (ζ : L)
    (hζ : ζ ^ M = 1) : IsCMField.complexConj L ζ = ζ ^ (M - 1) := by
  let φ : L →+* ℂ := Classical.choice inferInstance
  apply φ.injective
  have h1 : (φ ζ) ^ M = 1 := by rw [← map_pow, hζ, map_one]
  have h2 : ‖φ ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one h1 hM
  rw [IsCMField.complexEmbedding_complexConj, map_pow, ← Complex.inv_eq_conj h2]
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hM), h1]

theorem UpperTheory.V.FW.unrJ :
    ∀ (f n : ℕ) [NeZero (f * 2 ^ n)] (L : Type) [Field L] [NumberField L] [IsCyclotomicExtension {f * 2 ^ n} ℚ L] [IsCMField L], Odd f → 1 < f → 2 ≤ n → UnrFin L := by
  intro f n _ L _ _ _ _ hf h1 hn w
  rw [← UpperTheory.V.CF.ineCard.1 (maximalRealSubfield L) L w, Subgroup.card_eq_one, eq_bot_iff]
  intro τ hτ
  rw [Subgroup.mem_bot]
  by_contra hne
  have hc : Nat.card Gal(L/maximalRealSubfield L) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, Algebra.IsQuadraticExtension.finrank_eq_two]
  have hτc : τ = IsCMField.complexConj L :=
    ((Nat.card_eq_two_iff' 1).1 hc).unique hne (IsCMField.complexConj_ne_one L)
  subst hτc
  obtain ⟨p, hp, hw⟩ := unrJ_prime L w
  have hζ := IsCyclotomicExtension.zeta_spec (f * 2 ^ n) ℚ L
  have h := (UpperTheory.V.CF.cycIne (f * 2 ^ n) L _ p hp hζ w hw
    (UpperTheory.V.CF.relIncl ℚ (maximalRealSubfield L) L (IsCMField.complexConj L)) (f * 2 ^ n - 1)
    (unrJ_conj L _ (NeZero.ne _) _ hζ.pow_eq_one)).1.1 (fun z => hτ z)
  exact unrJ_arith f n p hp hf h1 hn h
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

theorem UpperTheory.V.FW.locInf :
    ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (x : (maximalRealSubfield K)ˣ), (∀ φ : K →+* ℂ, 0 < (φ (algebraMap (maximalRealSubfield K) K x)).re) → ∀ v, GroundTheory.Global.IdeleGroup.infiniteProj v (GroundTheory.Global.IdeleGroup.diagonal (maximalRealSubfield K) x) ∈ (GroundTheory.Global.IdeleNorm.infiniteLocalNorm K v).range := by
  intro K _ _ _ x hx v
  classical
  obtain ⟨W, rfl⟩ := InfinitePlace.comap_surjective (k := maximalRealSubfield K) (K := K) v
  set u := W.comap (algebraMap (maximalRealSubfield K) K) with hu_def
  have hWu : W.LiesOver u := { under_eq := rfl }
  have hu : u.IsReal := IsTotallyReal.isReal u
  have hpos : 0 < InfinitePlace.Completion.ringEquivRealOfIsReal hu
      (algebraMap (maximalRealSubfield K) u.Completion (x : maximalRealSubfield K)) := by
    have h0 : InfinitePlace.Completion.ringEquivRealOfIsReal hu
        (algebraMap (maximalRealSubfield K) u.Completion (x : maximalRealSubfield K)) =
        InfinitePlace.embedding_of_isReal hu (x : maximalRealSubfield K) := by
      change InfinitePlace.Completion.extensionEmbeddingOfIsReal hu _ = _
      rw [InfinitePlace.Completion.algebraMap_apply]
      exact InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hu _
    rw [h0]
    have h1 := InfinitePlace.embedding_of_isReal_apply hu (x : maximalRealSubfield K)
    have h3 := hx W.embedding
    rcases InfinitePlace.LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq W u with h2 | h2
    · have h4 := congrArg (fun f => (f (x : maximalRealSubfield K)).re) h2
      simp only [RingHom.coe_comp, Function.comp_apply] at h4
      rw [h4, ← h1] at h3
      rwa [Complex.ofReal_re] at h3
    · have h4 := congrArg (fun f => (f (x : maximalRealSubfield K)).re) h2
      simp only [RingHom.coe_comp, Function.comp_apply, ComplexEmbedding.conjugate_coe_eq,
        Complex.conj_re] at h4
      rw [h4, ← h1] at h3
      rwa [Complex.ofReal_re] at h3
  letI : Algebra u.Completion W.Completion := AbsoluteValue.Completion.algebraOfLiesOver u.1 W.1
  set e := InfinitePlace.Completion.ringEquivRealOfIsReal hu with he
  set a := algebraMap (maximalRealSubfield K) u.Completion (x : maximalRealSubfield K) with ha
  set d := Module.finrank u.Completion W.Completion with hd_def
  have hd : 0 < d := by
    rcases W.isUnramified_or_isRamified (maximalRealSubfield K) with h | h
    · rw [hd_def, h.finrank_eq_one u]; norm_num
    · rw [hd_def, h.finrank_eq_two u]; norm_num
  set r : u.Completion := e.symm (e a ^ ((d : ℝ)⁻¹)) with hr_def
  have hr : r ^ d = a := by
    apply e.injective
    rw [map_pow, hr_def, RingEquiv.apply_symm_apply, ← Real.rpow_natCast, ← Real.rpow_mul hpos.le,
      inv_mul_cancel₀ (by exact_mod_cast hd.ne'), Real.rpow_one]
  have ha0 : a ≠ 0 := by
    rw [ha]
    exact (map_ne_zero _).mpr x.ne_zero
  have hr0 : algebraMap u.Completion W.Completion r ≠ 0 := by
    rw [map_ne_zero]
    rintro h0
    rw [h0, zero_pow hd.ne'] at hr
    exact ha0 hr.symm
  let w0 : ↑(InfinitePlace.placesOver K u) := ⟨W, hWu⟩
  refine ⟨Pi.mulSingle w0 (Units.mk0 _ hr0), ?_⟩
  apply Units.ext
  simp only [GroundTheory.Global.IdeleNorm.infiniteLocalNorm, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [Fintype.prod_eq_single w0 (fun w hw => by rw [Pi.mulSingle_eq_of_ne hw, map_one]),
    Pi.mulSingle_eq_same, Units.coe_map, Units.val_mk0]
  rw [GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal]
  rw [← InfinitePlace.Completion.algebraMap_apply]
  change Algebra.norm u.Completion (algebraMap u.Completion W.Completion r) = a
  rw [Algebra.norm_algebraMap, ← hd_def, hr]
end
