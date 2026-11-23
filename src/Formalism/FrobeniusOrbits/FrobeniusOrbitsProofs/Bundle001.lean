module

public import Formalism.FrobeniusOrbits.Bundle001
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.CoprimeTwoPow
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Galois
import Mathlib.Algebra.AffineMonoid.UniqueSums
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IntermediateField Ideal

noncomputable section

namespace Formalism.FrobeniusOrbits

open Formalism.TwoAdicCyclotomicDecomposition

namespace Misc2

theorem units_ne_one_iff (x : ℤˣ) : x ≠ 1 ↔ x = -1 := by
  rcases Int.units_eq_one_or x with rfl | rfl <;> decide

end Misc2

open Misc2

theorem hostPartner : HostPartner := by
  intro e τ hτ
  rw [mem_Psi_iff] at hτ
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [Set.mem_ofPred_eq, mem_Psi_iff, units_ne_one_iff] at hg
    show _ ∈ Psi e
    rw [mem_Psi_iff]
    simp [cc, c0, hg, hτ]
  · intro g _ g' _ hgg
    simpa using hgg
  · intro t ht
    rw [SetLike.mem_coe, mem_Psi_iff] at ht
    refine ⟨(cc e)⁻¹ * t * τ⁻¹, ?_, ?_⟩
    · simp only [Set.mem_ofPred_eq, mem_Psi_iff]
      simp [cc, c0, ht, hτ]
    · simp only
      group

namespace Misc2

def conjHom {G : Type*} [Group G] (χ : G →* ℂˣ) : G →* ℂ :=
  (starRingEnd ℂ).toMonoidHom.comp ((Units.coeHom ℂ).comp χ)

def twHom (e : ℕ) (χ : GG e →* ℂˣ) : GG e →* ℂ :=
  (Units.coeHom ℂ).comp (chC e) * conjHom χ

theorem chC_apply (e : ℕ) (g : GG e) : ((chC e g : ℂˣ) : ℂ) = (((g.1.2 : ℤˣ) : ℤ) : ℂ) := rfl

theorem conjHom_eq_one_iff {G : Type*} [Group G] (χ : G →* ℂˣ) : conjHom χ = 1 ↔ χ = 1 := by
  constructor
  · intro h
    ext g
    have := DFunLike.congr_fun h g
    simp only [conjHom, MonoidHom.coe_comp, Function.comp_apply, Units.coeHom_apply,
      RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, MonoidHom.one_apply] at this
    have := congrArg (starRingEnd ℂ) this
    simpa using this
  · rintro rfl
    ext g
    simp [conjHom]

theorem int_units_sq_C (x : ℤˣ) : (((x : ℤ) : ℂ)) * ((x : ℤ) : ℂ) = 1 := by
  rcases Int.units_eq_one_or x with rfl | rfl <;> simp

theorem twHom_eq_one_iff (e : ℕ) (χ : GG e →* ℂˣ) : twHom e χ = 1 ↔ χ = chC e := by
  constructor
  · intro h
    ext g
    have := DFunLike.congr_fun h g
    simp only [twHom, conjHom, MonoidHom.mul_apply, MonoidHom.coe_comp, Function.comp_apply,
      Units.coeHom_apply, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      MonoidHom.one_apply, chC_apply] at this
    have h2 : starRingEnd ℂ ((χ g : ℂˣ) : ℂ) = (((g.1.2 : ℤˣ) : ℤ) : ℂ) := by
      have := congrArg (fun z => (((g.1.2 : ℤˣ) : ℤ) : ℂ) * z) this
      simp only [← mul_assoc, int_units_sq_C, one_mul, mul_one] at this
      exact this
    have := congrArg (starRingEnd ℂ) h2
    rw [chC_apply]
    simpa using this
  · rintro rfl
    ext g
    simp only [twHom, conjHom, MonoidHom.mul_apply, MonoidHom.coe_comp, Function.comp_apply,
      Units.coeHom_apply, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      MonoidHom.one_apply, chC_apply]
    simp [int_units_sq_C]

theorem chC_ne_one (e : ℕ) : chC e ≠ 1 := by
  intro h
  have := DFunLike.congr_fun h (cc e)
  have h2 := congrArg (fun u : ℂˣ => (u : ℂ)) this
  simp only [chC_apply, MonoidHom.one_apply, Units.val_one] at h2
  simp [cc, c0] at h2
  norm_num at h2

theorem card_extended_galois_group (e : ℕ) [Fintype (GG e)] : (Fintype.card (GG e) : ℂ) = 2 ^ (e + 2) := by
  rw [← Nat.card_eq_fintype_card, (hostGroup e).1]
  push_cast; rfl

end Misc2

open Classical in
theorem hostCharSum : HostCharSum := by
  intro e
  refine ⟨fun χ => ?_, fun g => ?_⟩
  · have hpt : ∀ g : GG e, 2 * (if g ∉ Psi e then starRingEnd ℂ ((χ g : ℂˣ) : ℂ) else 0) =
        conjHom χ g - twHom e χ g := by
      intro g
      simp only [twHom, conjHom, MonoidHom.mul_apply, MonoidHom.coe_comp, Function.comp_apply,
        Units.coeHom_apply, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, chC_apply, mem_Psi_iff]
      rcases Int.units_eq_one_or g.1.2 with h | h <;> rw [h] <;> simp <;> ring
    have hA := sum_hom_units (conjHom χ)
    have hB := sum_hom_units (twHom e χ)
    simp only [conjHom_eq_one_iff, twHom_eq_one_iff, Nat.cast_ite, Nat.cast_zero] at hA hB
    have hS : 2 * (∑ g ∈ Finset.univ.filter (fun g : GG e => g ∉ Psi e),
        starRingEnd ℂ ((χ g : ℂˣ) : ℂ)) =
        (∑ g : GG e, conjHom χ g) - ∑ g : GG e, twHom e χ g := by
      rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun g _ => hpt g)
    rw [hA, hB, card_extended_galois_group] at hS
    have hne := chC_ne_one e
    split_ifs at hS ⊢ with h1 h2 h2
    · exact absurd (h1.symm.trans h2) (Ne.symm hne)
    · linear_combination hS / 2
    · linear_combination hS / 2
    · linear_combination hS / 2
  · simp only [chD, chQ, MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_fst,
      MonoidHom.coe_snd, Prod.ext_iff]
    rcases Int.units_eq_one_or g.1.1 with h | h <;> rcases Int.units_eq_one_or g.1.2 with h' | h' <;>
      rw [h, h'] <;> decide

end Formalism.FrobeniusOrbits
end
end

section

open Polynomial

noncomputable section

namespace Formalism.FrobeniusOrbits

namespace Orbits

lemma prim_bound {E K : Type*} [Field E] [Field K] [Algebra ℚ E] [Algebra ℚ K] [Algebra E K]
    [IsScalarTower ℚ E K] [FiniteDimensional ℚ E] [FiniteDimensional E K] (g : ℕ) (hg : g.Prime)
    (μ : K) (hμ : IsPrimitiveRoot μ g) :
    g - 1 ≤ Module.finrank ℚ E * Module.finrank E K := by
  haveI : FiniteDimensional ℚ K := Module.Finite.trans E K
  haveI : CharZero K := by
    first
    | exact algebraRat.charZero K
    | exact (algebraMap ℚ K).charZero
  rw [Module.finrank_mul_finrank ℚ E K]
  have hint : IsIntegral ℚ μ := .of_finite ℚ μ
  have h1 : Module.finrank ℚ (IntermediateField.adjoin ℚ {μ}) = g - 1 := by
    haveI : NeZero g := ⟨hg.ne_zero⟩
    have hroot : aeval μ (cyclotomic g ℚ) = 0 := by
      rw [aeval_def, ← eval_map, map_cyclotomic]
      exact (isRoot_cyclotomic_iff.mpr hμ)
    rw [IntermediateField.adjoin.finrank hint, ← minpoly.eq_of_irreducible_of_monic
      (cyclotomic.irreducible_rat hg.pos) hroot (cyclotomic.monic g ℚ),
      natDegree_cyclotomic, Nat.totient_prime hg]
  rw [← h1, ← (letI : Module.Free (IntermediateField.adjoin ℚ {μ}) K := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (IntermediateField.adjoin ℚ {μ}) K)]
  exact Nat.le_mul_of_pos_right _ Module.finrank_pos

lemma dim_bound {E : Type*} [Field E] [Algebra ℚ E] [FiniteDimensional ℚ E]
    (k g : ℕ) (hg : g.Prime) (M : Matrix (Fin k) (Fin k) E) (hM : M ^ g = 1) (hne : M ≠ 1) :
    g - 1 ≤ Module.finrank ℚ E * k := by
  classical
  haveI := Fact.mk hg
  have hint : IsIntegral E M := IsIntegral.of_finite E M
  have hm0 : minpoly E M ≠ 0 := minpoly.ne_zero hint
  have hmk : (minpoly E M).natDegree ≤ k := by
    have h1 : minpoly E M ∣ M.charpoly := minpoly.dvd E M (Matrix.aeval_self_charpoly M)
    have h2 := natDegree_le_of_dvd h1 M.charpoly_monic.ne_zero
    rwa [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at h2
  have hfac : (X ^ g - 1 : E[X]) = (X - 1) * cyclotomic g E := by
    rw [mul_comm, cyclotomic_prime_mul_X_sub_one]
  have hdvd : minpoly E M ∣ (X - 1) * cyclotomic g E := by
    rw [← hfac]
    apply minpoly.dvd
    simp [hM]
  have hnd : ¬ minpoly E M ∣ X - 1 := by
    rintro ⟨q, hq⟩
    apply hne
    have h0 : aeval M (X - 1 : E[X]) = 0 := by rw [hq, map_mul, minpoly.aeval, zero_mul]
    simpa [sub_eq_zero] using h0
  obtain ⟨f, hf, hfm, hfΦ⟩ : ∃ f : E[X], Irreducible f ∧ f ∣ minpoly E M ∧ f ∣ cyclotomic g E := by
    by_contra hcon
    push_neg at hcon
    have hcop : IsCoprime (minpoly E M) (cyclotomic g E) :=
      isCoprime_of_irreducible_dvd (fun h => hm0 h.1) (fun z hz hzm hzΦ => hcon z hz hzm hzΦ)
    exact hnd (hcop.dvd_of_dvd_mul_right hdvd)
  have hfk : f.natDegree ≤ k := (natDegree_le_of_dvd hfm hm0).trans hmk
  haveI : Fact (Irreducible f) := ⟨hf⟩
  have hf0 : f ≠ 0 := hf.ne_zero
  haveI : FiniteDimensional E (AdjoinRoot f) := (AdjoinRoot.powerBasis hf0).finite
  have hrank : Module.finrank E (AdjoinRoot f) = f.natDegree := by
    rw [(AdjoinRoot.powerBasis hf0).finrank, AdjoinRoot.powerBasis_dim]
  haveI : CharZero (AdjoinRoot f) := by
    first
    | exact algebraRat.charZero (AdjoinRoot f)
    | exact (algebraMap ℚ (AdjoinRoot f)).charZero
  haveI : NeZero g := ⟨hg.ne_zero⟩
  have hμ : IsPrimitiveRoot (AdjoinRoot.root f) g := by
    rw [← isRoot_cyclotomic_iff, ← map_cyclotomic g (algebraMap E (AdjoinRoot f)), IsRoot, eval_map]
    obtain ⟨q, hq⟩ := hfΦ
    rw [hq, eval₂_mul, AdjoinRoot.algebraMap_eq, AdjoinRoot.eval₂_root, zero_mul]
  have hb := prim_bound (E := E) (K := AdjoinRoot f) g hg _ hμ
  rw [hrank] at hb
  exact hb.trans (Nat.mul_le_mul_left _ hfk)

end Orbits

open Orbits

theorem hostOrbitsPlaces : HostOrbitsPlaces := by
  unfold HostOrbitsPlaces
  intro e φ hφ τ hτ i
  have hτ2 : τ.1.2 = 1 := by simpa [Psi, chD] using hτ
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  rcases Nat.even_or_odd i with hi | hi
  · have hc : φ.1 ^ i = 1 := by
      rcases hφ with h | h
      · rw [h, c0]; ext <;> simp [hi.neg_one_pow]
      · rw [h]; ext <;> simp [hi.neg_one_pow]
    have hp : placeOf (φ ^ i * τ) = φ ^ i * τ := by
      unfold placeOf
      rw [if_pos]
      simp [Prod.pow_fst, hc, hτ2]
    rw [hp]
    refine ⟨by simp, fun _ => by simp [hc], fun _ => by simp [hc, hi]⟩
  · have hp : placeOf (φ ^ i * τ) = cc e * (φ ^ i * τ) := by
      unfold placeOf
      rw [if_neg]
      rcases hφ with h | h
      · simp [h, c0, hi.neg_one_pow, hτ2, hne]
      · simp [h, hi.neg_one_pow, hτ2, hne]
    rw [hp]
    refine ⟨by simp [cc], fun h => ?_, fun h => ?_⟩
    · ext <;> simp [cc, c0, h, hi.neg_one_pow, hτ2]
    · have hni : ¬ Even i := Nat.not_even_iff_odd.mpr hi
      ext <;> simp [cc, c0, h, hi.neg_one_pow, hτ2, hni, sg]

theorem hostOrbitCount : HostOrbitCount := by
  unfold HostOrbitCount
  intro e φ h0 τ hτ
  have hpl : ∀ i : ℕ, placeOf (φ ^ i * τ) = (τ.1, φ.2 ^ i * τ.2) := by
    intro i
    obtain ⟨h2, h1, -⟩ := hostOrbitsPlaces e φ (Or.inl h0) τ hτ i
    exact Prod.ext (h1 h0) h2
  have hr : (Set.range fun i : ℕ => placeOf (φ ^ i * τ)) =
      (fun x : HGrp e => ((τ.1, x * τ.2) : GG e)) '' Set.range (fun i : ℕ => φ.2 ^ i) := by
    ext y
    simp [hpl]
  rw [hr, Set.ncard_image_of_injective _ (fun x y hxy => by simpa using hxy)]
  rw [show Set.range (fun i : ℕ => φ.2 ^ i) = (Submonoid.powers φ.2 : Set (HGrp e)) from
    (Submonoid.coe_powers φ.2).symm, ← Nat.card_coe_set_eq]
  exact Nat.card_submonoidPowers

theorem hostFiniteOrder : HostFiniteOrder := by
  unfold HostFiniteOrder
  intro e q d hqd L _ _ ζ a b h k g hg M hM hne
  have := dim_bound k g hg M hM hne
  rwa [Galois.finrank_cmField hqd h] at this

end Formalism.FrobeniusOrbits
end
end
