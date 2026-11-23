module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameKummerInertiaSurjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle116
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle116
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.GaloisValuations.GlobalA
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle001

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

section

variable {Ω : Type} [Field Ω] (A : ValuationSubring Ω)

private theorem val_root (x : Ω) {n : ℕ} (hn : n ≠ 0) (h : x ^ n = 1) : A.valuation x = 1 := by
  have : A.valuation x ^ n = 1 := by rw [← map_pow, h, map_one]
  exact (pow_eq_one_iff_of_nonneg zero_le' hn).1 this

private theorem val_one_sub_pow_le {ζ : Ω} (hζ : A.valuation ζ ≤ 1) (j : ℕ) :
    A.valuation (1 - ζ ^ j) ≤ A.valuation (1 - ζ) := by
  rw [← mul_neg_geom_sum, map_mul]
  have : A.valuation (∑ i ∈ Finset.range j, ζ ^ i) ≤ 1 :=
    Valuation.map_sum_le _ (fun i _ => by rw [map_pow]; exact pow_le_one' hζ i)
  exact mul_le_of_le_one_right' this

private theorem val_p {p : ℕ} (hp : p.Prime) {ζ : Ω} (hζ : IsPrimitiveRoot ζ p) :
    A.valuation (1 - ζ) ^ (p - 1) = A.valuation ((p : ℕ) : Ω) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hall : ∀ μ ∈ primitiveRoots p Ω, A.valuation (1 - μ) = A.valuation (1 - ζ) := by
    intro μ hμ
    rw [mem_primitiveRoots hp.pos] at hμ
    have hμ1 : A.valuation μ ≤ 1 := (val_root A μ hp.ne_zero hμ.pow_eq_one).le
    have hζ1 : A.valuation ζ ≤ 1 := (val_root A ζ hp.ne_zero hζ.pow_eq_one).le
    obtain ⟨k, _, hk⟩ := hμ.eq_pow_of_pow_eq_one hζ.pow_eq_one
    obtain ⟨l, _, hl⟩ := hζ.eq_pow_of_pow_eq_one hμ.pow_eq_one
    apply le_antisymm
    · rw [← hl]
      exact val_one_sub_pow_le A hζ1 l
    · rw [← hk]
      exact val_one_sub_pow_le A hμ1 k
  have hprod : ((p : ℕ) : Ω) = ∏ μ ∈ primitiveRoots p Ω, (1 - μ) := by
    have h := congrArg (Polynomial.eval (1 : Ω)) (Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ)
    rw [Polynomial.eval_one_cyclotomic_prime, Polynomial.eval_prod] at h
    simpa using h
  rw [hprod, map_prod, Finset.prod_congr rfl hall, Finset.prod_const, hζ.card_primitiveRoots,
    Nat.totient_prime hp]

private theorem val_pow_sub_pow_lt {x y : Ω} (hx : A.valuation x ≤ 1) (hy : A.valuation y ≤ 1)
    (h : A.valuation (x - y) < 1) (e : ℕ) : A.valuation (x ^ e - y ^ e) < 1 := by
  rw [← geom_sum₂_mul, map_mul]
  have : A.valuation (∑ i ∈ Finset.range e, x ^ i * y ^ (e - 1 - i)) ≤ 1 :=
    Valuation.map_sum_le _ (fun i _ => by
      rw [map_mul, map_pow, map_pow]; exact mul_le_one' (pow_le_one' hx _) (pow_le_one' hy _))
  exact lt_of_le_of_lt (mul_le_of_le_one_left' this) h

private theorem val_natCast_sub_lt {p i : ℕ} (hp : p.Prime) {ζ μ Y : Ω} (hζ : IsPrimitiveRoot ζ p)
    (hμ : μ ^ (p - 1) = 1) (hY : Y ^ (p - 1) = ((p : ℕ) : Ω)) (hp0 : ((p : ℕ) : Ω) ≠ 0)
    (hvp : A.valuation ((p : ℕ) : Ω) < 1) (f : Ω →+* Ω)
    (hf : ∀ x, A.valuation x ≤ 1 → A.valuation (f x - x) < 1)
    (hfY : f Y = μ * Y) (hfζ : f ζ = ζ ^ i) : A.valuation ((i : Ω) - μ) < 1 := by
  have hp1 : 1 ≤ p - 1 := by
    have := hp.two_le
    omega
  have hζ1 : A.valuation ζ = 1 := val_root A ζ hp.ne_zero hζ.pow_eq_one
  have hμ1 : A.valuation μ = 1 := val_root A μ (by omega) hμ
  have hμ0 : μ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hμ1
    exact zero_ne_one hμ1
  have hY0 : Y ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega)] at hY
    exact hp0 hY.symm
  have h4 := val_p A hp hζ
  have hvYpow : A.valuation Y ^ (p - 1) = A.valuation (1 - ζ) ^ (p - 1) := by
    rw [← map_pow, hY, h4]
  have hvY : A.valuation Y = A.valuation (1 - ζ) := pow_left_injective (by omega) hvYpow
  have hvπ : A.valuation (1 - ζ) < 1 := by
    by_contra hc
    have h5 := one_le_pow_of_one_le' (not_lt.mp hc) (p - 1)
    rw [h4] at h5
    exact absurd hvp (not_lt.mpr h5)
  have hvY0 : A.valuation Y ≠ 0 := by
    rw [Ne, Valuation.zero_iff]
    exact hY0
  have hw : A.valuation ((1 - ζ) / Y) = 1 := by
    rw [map_div₀, ← hvY, div_self hvY0]
  have hgeom : 1 - ζ ^ i = (1 - ζ) * ∑ k ∈ Finset.range i, ζ ^ k := (mul_neg_geom_sum ζ i).symm
  have hfw : f ((1 - ζ) / Y) = (1 - ζ) * (∑ k ∈ Finset.range i, ζ ^ k) / (μ * Y) := by
    rw [map_div₀, map_sub, map_one, hfζ, hfY, hgeom]
  have hdiff : f ((1 - ζ) / Y) - (1 - ζ) / Y
      = (1 - ζ) / Y * ((∑ k ∈ Finset.range i, ζ ^ k) - μ) * μ⁻¹ := by
    rw [hfw]
    field_simp
  have h1 := hf ((1 - ζ) / Y) hw.le
  rw [hdiff, map_mul, map_mul, hw, map_inv₀, hμ1, one_mul, inv_one, mul_one] at h1
  have h2 : A.valuation ((i : Ω) - ∑ k ∈ Finset.range i, ζ ^ k) < 1 := by
    have hsum : (i : Ω) - ∑ k ∈ Finset.range i, ζ ^ k = ∑ k ∈ Finset.range i, (1 - ζ ^ k) := by
      rw [Finset.sum_sub_distrib]
      simp
    rw [hsum]
    exact lt_of_le_of_lt (Valuation.map_sum_le _ (fun k _ => val_one_sub_pow_le A hζ1.le k)) hvπ
  have h3 : (i : Ω) - μ = ((i : Ω) - ∑ k ∈ Finset.range i, ζ ^ k) + ((∑ k ∈ Finset.range i, ζ ^ k) - μ) := by
    ring
  rw [h3]
  exact Valuation.map_add_lt _ h2 h1

end

theorem inertiaGen : InertiaGen := by
  unfold InertiaGen
  intro F Ω _ _ _ _ _ A u hA p _ hpu hpu2 ζ hζ
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hm : 0 < p - 1 := by
    have := hp.two_le
    omega
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : NeZero (((p - 1 : ℕ)) : Ω) := ⟨by exact_mod_cast hm.ne'⟩
  obtain ⟨Y, hY⟩ := IsAlgClosed.exists_pow_nat_eq ((p : ℕ) : Ω) hm
  obtain ⟨μ, hμ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (p - 1)
  have hndvd : ¬ p ∣ p - 1 := fun h => absurd (Nat.le_of_dvd hm h) (by omega)
  obtain ⟨σ, hσ, hσY⟩ :=
    GlobalTheory.TameKummerInertia.tame_kummer_surj F Ω A u hA p hpu hpu2 (p - 1) hm hndvd Y μ hY hμ.pow_eq_one
  have hσζ : IsPrimitiveRoot (σ ζ) p := hζ.map_of_injective σ.injective
  obtain ⟨i, hi_lt, hi⟩ := hζ.eq_pow_of_pow_eq_one hσζ.pow_eq_one
  have hcop : i.Coprime p := (hζ.pow_iff_coprime hp.pos i).mp (hi ▸ hσζ)
  have hi0 : i ≠ 0 := by
    rintro rfl
    exact hp.ne_one ((Nat.coprime_zero_left p).mp hcop)
  have hvp : A.valuation ((p : ℕ) : Ω) < 1 := GlobalTheory.TameCoupledEx.val_g_lt A u hA hpu
  have hp0 : ((p : ℕ) : Ω) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hσ' := mem_Ine.mp hσ
  unfold Inertia at hσ'
  have h6 : A.valuation ((i : Ω) - μ) < 1 :=
    val_natCast_sub_lt A hp hζ hμ.pow_eq_one hY hp0 hvp σ.toRingEquiv.toRingHom
      (fun x hx => hσ'.2 x hx) hσY hi.symm
  refine ⟨σ, hσ, ZMod.unitOfCoprime i hcop, ?_, ?_⟩
  · rw [orderOf_eq_iff hm]
    refine ⟨ZMod.units_pow_card_sub_one_eq_one p _, fun k hk hk0 hpow => ?_⟩
    have hzk : ((i ^ k : ℕ) : ZMod p) = 1 := by
      have h := congrArg (fun x : (ZMod p)ˣ => (x : ZMod p)) hpow
      simpa [ZMod.coe_unitOfCoprime] using h
    have hik : 1 ≤ i ^ k := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hi0)
    have hdvd : p ∣ i ^ k - 1 := by
      rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hik, hzk, Nat.cast_one, sub_self]
    obtain ⟨c, hc⟩ := hdvd
    have hv1 : A.valuation ((i : Ω) ^ k - 1) < 1 := by
      have hcast : (i : Ω) ^ k - 1 = ((p : ℕ) : Ω) * (c : Ω) := by
        have h := congrArg (Nat.cast : ℕ → Ω) hc
        push_cast [Nat.cast_sub hik] at h
        exact h
      rw [hcast, map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' (valuation_natCast_le_one A c)) hvp
    have hμv : A.valuation μ ≤ 1 := (val_root A μ hm.ne' hμ.pow_eq_one).le
    have h5 := val_pow_sub_pow_lt A (valuation_natCast_le_one A i) hμv h6 k
    have h7 : A.valuation (μ ^ k - 1) < 1 := by
      have hrw : μ ^ k - 1 = ((i : Ω) ^ k - 1) + -((i : Ω) ^ k - μ ^ k) := by ring
      rw [hrw]
      exact Valuation.map_add_lt _ hv1 (by rw [Valuation.map_neg]; exact h5)
    have hvpm : ¬ A.valuation (((p - 1 : ℕ)) : Ω) < 1 := by
      intro hlt
      have hone : (1 : Ω) = ((p : ℕ) : Ω) + -(((p - 1 : ℕ)) : Ω) := by
        rw [Nat.cast_sub hp.one_le]
        push_cast
        ring
      have h8 := Valuation.map_add_lt A.valuation hvp (by rw [Valuation.map_neg]; exact hlt)
      rw [← hone, map_one] at h8
      exact lt_irrefl _ h8
    have heq := eq_of_pow_eq_one A hvpm
      (by rw [← pow_mul, mul_comm, pow_mul, hμ.pow_eq_one, one_pow]) (one_pow _) h7
    exact hμ.pow_ne_one_of_pos_of_lt hk0.ne' hk heq
  · rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi_lt]
    exact hi.symm

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open scoped commutatorElement

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem normal_of_comm {Γ : Type} [Group Γ] (H : Subgroup Γ) (h : commutator Γ ≤ H) : H.Normal := by
  constructor
  intro n hn g
  have hc : ⁅g, n⁆ ∈ H := h (by
    rw [commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n))
  have he : g * n * g⁻¹ = ⁅g, n⁆ * n := by
    rw [commutatorElement_def]; group
  rw [he]
  exact H.mul_mem hc hn

open Polynomial in
private theorem exists_map_eq_conj_of_isAlgClosed_algebraic {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [Algebra.IsAlgebraic ℚ Ω]
    (φ : Ω →+* ℂ) (y : Ω) : ∃ z : Ω, φ z = starRingEnd ℂ (φ y) := by
  set p := minpoly ℚ y
  have hint : IsIntegral ℚ y := (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
  have hp0 : p ≠ 0 := minpoly.ne_zero hint
  set w := starRingEnd ℂ (φ y)
  have hw : aeval w p = 0 := by
    have h1 : aeval (φ.toRatAlgHom y) p = φ.toRatAlgHom (aeval y p) := Polynomial.aeval_algHom_apply _ _ _
    rw [minpoly.aeval, map_zero] at h1
    have h2 : aeval ((Complex.conjAe.toAlgHom.restrictScalars ℚ) (φ y)) p =
        (Complex.conjAe.toAlgHom.restrictScalars ℚ) (aeval (φ y) p) := Polynomial.aeval_algHom_apply _ _ _
    have h3 : aeval (φ y) p = 0 := h1
    rw [h3, map_zero] at h2
    exact h2
  set q := p.map (algebraMap ℚ Ω)
  have hq0 : q ≠ 0 := Polynomial.map_ne_zero hp0
  have hq := C_leadingCoeff_mul_prod_multiset_X_sub_C (IsAlgClosed.card_roots_eq_natDegree (p := q))
  have hmap : q.map φ = p.map (algebraMap ℚ ℂ) := by
    rw [Polynomial.map_map]
    congr 1
    exact RingHom.ext_rat _ _
  have hev := congrArg (fun P => (P.map φ).eval w) hq
  simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_multiset_prod, Multiset.map_map,
    Function.comp_def, Polynomial.map_sub, Polynomial.map_X, eval_mul, eval_C, eval_multiset_prod,
    eval_sub, eval_X] at hev
  rw [hmap, eval_map, ← aeval_def, hw] at hev
  have hlc : φ q.leadingCoeff ≠ 0 := (map_ne_zero φ).mpr (leadingCoeff_ne_zero.mpr hq0)
  have hprod := (mul_eq_zero.mp hev).resolve_left hlc
  obtain ⟨r, -, hr⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hprod)
  exact ⟨r, (sub_eq_zero.mp hr).symm⟩

private theorem exists_algEquiv_map_eq_conj_of_exists_conj {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [Algebra.IsAlgebraic F Ω]
    (φ : Ω →+* ℂ) (hc : ∀ y : Ω, ∃ z : Ω, φ z = starRingEnd ℂ (φ y))
    (hF : ∀ a : F, starRingEnd ℂ (φ (algebraMap F Ω a)) = φ (algebraMap F Ω a)) :
    ∃ c : Ω ≃ₐ[F] Ω, ∀ x, φ (c x) = starRingEnd ℂ (φ x) := by
  choose c0 hc0 using hc
  have inj : Function.Injective φ := φ.injective
  let cf : Ω →ₐ[F] Ω :=
    { toFun := c0
      map_one' := inj (by rw [hc0, map_one, map_one])
      map_mul' := fun a b => inj (by rw [hc0, map_mul, map_mul, map_mul, hc0, hc0])
      map_zero' := inj (by rw [hc0, map_zero, map_zero])
      map_add' := fun a b => inj (by rw [hc0, map_add (f := _), map_add (f := _), map_add (f := _), hc0, hc0])
      commutes' := fun a => inj (by rw [hc0, hF]) }
  exact ⟨AlgEquiv.ofBijective cf (Algebra.IsAlgebraic.algHom_bijective cf), fun x => hc0 x⟩

theorem exFld : ExFld := by
  intro E Ω _ _ _ _ _ _ H hH
  have hGE : IsGalois E Ω := inferInstance
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  haveI : Module.Finite (maximalRealSubfield E) E :=
    Module.Finite.of_restrictScalars_finite ℚ (maximalRealSubfield E) E
  haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ E Ω
  haveI : Algebra.IsAlgebraic (maximalRealSubfield E) Ω := Algebra.IsAlgebraic.trans (maximalRealSubfield E) E Ω
  haveI : IsAlgClosure (maximalRealSubfield E) Ω := ⟨IsAlgClosure.isAlgClosed E, inferInstance⟩
  have hGF : IsGalois (maximalRealSubfield E) Ω := inferInstance
  have hopen : IsOpen ((H.comap (AlgEquiv.restrictScalarsHom (maximalRealSubfield E)) : Subgroup (G E Ω)) :
      Set (G E Ω)) :=
    hH.isOpen.preimage (UpperTheory.V.Af.continuous_restrictScalarsHom (maximalRealSubfield E) E Ω)
  set H' : Subgroup (G E Ω) := H.comap (AlgEquiv.restrictScalarsHom (maximalRealSubfield E)) with hH'
  have hclosed : IsClosed (H' : Set (G E Ω)) := Subgroup.isClosed_of_isOpen H' hopen
  have hcomm : commutator (G E Ω) ≤ H' := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [hH', Subgroup.mem_comap, map_commutatorElement]
    apply hH.comm
    rw [commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  set M : IntermediateField E Ω := IntermediateField.fixedField H'
  have hfixM : M.fixingSubgroup = H' := InfiniteGalois.fixingSubgroup_fixedField ⟨H', hclosed⟩
  haveI hfin : FiniteDimensional E M :=
    (InfiniteGalois.isOpen_iff_finite M).mp (by rw [hfixM]; exact hopen)
  haveI hgal : IsGalois E M :=
    (InfiniteGalois.normal_iff_isGalois M).mp (by rw [hfixM]; exact normal_of_comm H' hcomm)
  have hab : ∀ σ τ : Gal(M/E), σ * τ = τ * σ := by
    intro σ τ
    obtain ⟨g, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (K₁ := M) Ω σ
    obtain ⟨h, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (K₁ := M) Ω τ
    have hk : ⁅g, h⁆ ∈ (AlgEquiv.restrictNormalHom (F := E) (K₁ := Ω) M).ker := by
      rw [IntermediateField.restrictNormalHom_ker, hfixM]
      apply hcomm
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at hk
    exact hk
  haveI : IsMulCommutative Gal(M/E) := ⟨⟨hab⟩⟩
  haveI : IsAbelianGalois E M := ⟨⟩
  haveI : NumberField M := { to_charZero := inferInstance, to_finiteDimensional := Module.Finite.trans E M }
  set KF : IntermediateField (maximalRealSubfield E) Ω := IntermediateField.fixedField H
  have hHclosed : IsClosed (H : Set (G (maximalRealSubfield E) Ω)) := Subgroup.isClosed_of_isOpen H hH.isOpen
  have hfixKF : KF.fixingSubgroup = H := InfiniteGalois.fixingSubgroup_fixedField ⟨H, hHclosed⟩
  have hMeq : M = IntermediateField.adjoin E (KF : Set Ω) := by
    apply le_antisymm
    · rw [← InfiniteGalois.fixedField_fixingSubgroup (IntermediateField.adjoin E (KF : Set Ω))]
      apply IntermediateField.fixedField_le
      intro g hg
      rw [hH', Subgroup.mem_comap, ← hfixKF, IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hg x (IntermediateField.subset_adjoin _ _ hx)
    · rw [IntermediateField.adjoin_le_iff]
      intro x hx
      rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
      intro g hg
      exact (IntermediateField.mem_fixedField_iff H x).mp hx _ hg
  have hreal : ∀ x ∈ (KF : Set Ω), ∀ φ : Ω →+* ℂ, (φ x).im = 0 := by
    intro x hx φ
    obtain ⟨c, hc⟩ := exists_algEquiv_map_eq_conj_of_exists_conj (F := maximalRealSubfield E) φ (exists_map_eq_conj_of_isAlgClosed_algebraic φ) (fun a =>
      (mem_maximalRealSubfield_iff (a : E)).mp a.2 (φ.comp (algebraMap E Ω)))
    have hcH : c ∈ H := hH.real φ c hc
    have hcx : c x = x := (IntermediateField.mem_fixedField_iff H x).mp hx c hcH
    rw [← Complex.conj_eq_iff_im, ← hc, hcx]
  haveI hCM : IsCMField M := (GlobalTheory.CMSub.isCMField_sup_le_adjoin Ω E).2.2 M (KF : Set Ω) hreal hMeq
  haveI : IsAlgClosure M Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.tower_top (K := E) M⟩
  refine ⟨Fld.mk M, ?_⟩
  intro g
  constructor
  · intro h
    have hg : g ∈ M.fixingSubgroup :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).mpr (fun x hx => h ⟨x, hx⟩)
    rw [hfixM] at hg
    exact hg
  · intro h x
    have hg : g ∈ M.fixingSubgroup := by rw [hfixM]; exact h
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hg x.1 x.2

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
end
end
