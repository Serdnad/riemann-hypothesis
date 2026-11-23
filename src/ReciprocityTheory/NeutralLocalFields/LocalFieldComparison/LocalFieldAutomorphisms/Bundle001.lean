module

public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.LocalFieldAutomorphisms.Kloc
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.LocalFieldAutomorphisms.ModelA
public import Mathlib.NumberTheory.Padics.PadicIntegers
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
public import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.GaloisValuations.GlobalB
import Formalism.ConjugateSelfDual.Bundle001
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

noncomputable section

namespace ReciprocityTheory.Neutral.Cmp

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
open scoped Pointwise

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime]

theorem Compat.valuation_le_one_iff {A : ValuationSubring Ω} {ι : Ω →+* PadicAlgCl p} (h : Compat p A ι) (x : Ω) :
    A.valuation x ≤ 1 ↔ ‖ι x‖ ≤ 1 := by
  rw [ValuationSubring.valuation_le_one_iff]
  exact h x

theorem Compat.valuation_lt_one_iff {A : ValuationSubring Ω} {ι : Ω →+* PadicAlgCl p} (h : Compat p A ι) (x : Ω) :
    A.valuation x < 1 ↔ ‖ι x‖ < 1 := by
  by_cases hx : x = 0
  · subst hx
    simp
  · have hx' : x⁻¹ ≠ 0 := inv_ne_zero hx
    have h1 : A.valuation x < 1 ↔ 1 < A.valuation x⁻¹ := by
      rw [Valuation.one_lt_val_iff _ hx', inv_inv]
    have hn : 0 < ‖ι x‖ := norm_pos_iff.mpr ((map_ne_zero ι).mpr hx)
    rw [h1, ← not_le, h.valuation_le_one_iff, map_inv₀, norm_inv, not_le, one_lt_inv₀ hn]

theorem valuation_intCast_lt_one_iff [CharZero Ω] (B : ValuationSubring Ω) (hp : B.valuation (p : Ω) < 1) (n : ℤ) :
    B.valuation (n : Ω) < 1 ↔ (p : ℤ) ∣ n := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  have hle : ∀ m : ℤ, B.valuation (m : Ω) ≤ 1 := fun m =>
    (B.valuation_le_one_iff _).mpr (intCast_mem B m)
  constructor
  · intro hn
    by_contra hpn
    obtain ⟨a, b, hab⟩ := (Prime.coprime_iff_not_dvd hpZ).mpr hpn
    have h1 : B.valuation ((a : Ω) * (p : Ω)) < 1 := by
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' (hle a)) hp
    have h2 : B.valuation ((b : Ω) * (n : Ω)) < 1 := by
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' (hle b)) hn
    have h3 : ((a : Ω) * (p : Ω)) + (b : Ω) * (n : Ω) = 1 := by exact_mod_cast hab
    have h4 := B.valuation.map_add ((a : Ω) * (p : Ω)) ((b : Ω) * (n : Ω))
    rw [h3, map_one] at h4
    exact absurd (lt_of_le_of_lt h4 (max_lt h1 h2)) (lt_irrefl 1)
  · rintro ⟨m, rfl⟩
    push_cast
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (hle m)) hp

def ratPrime (p : ℕ) [Fact p.Prime] : HeightOneSpectrum (𝓞 ℚ) where
  asIdeal := Ideal.comap (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ) (Ideal.span {(p : ℤ)})
  isPrime := by
    have : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime (by exact_mod_cast (Fact.out : p.Prime).ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp Fact.out)
    exact Ideal.comap_isPrime _ _
  ne_bot := by
    intro h
    have hmem : ((p : ℕ) : 𝓞 ℚ) ∈ Ideal.comap (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ) (Ideal.span {(p : ℤ)}) := by
      rw [Ideal.mem_comap, map_natCast, Ideal.mem_span_singleton]
    rw [h, Ideal.mem_bot] at hmem
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast hmem)

theorem lies_over_ratPrime [CharZero Ω] (B : ValuationSubring Ω) (hp : B.valuation (p : Ω) < 1) (x : 𝓞 ℚ) :
    B.valuation (algebraMap ℚ Ω (x : ℚ)) < 1 ↔ x ∈ (ratPrime p).asIdeal := by
  have hx : (x : ℚ) = ((Rat.ringOfIntegersEquiv x : ℤ) : ℚ) := by
    conv_lhs => rw [← Rat.ringOfIntegersEquiv.symm_apply_apply x]
    simp
  rw [hx, map_intCast, valuation_intCast_lt_one_iff B hp]
  show _ ↔ Rat.ringOfIntegersEquiv x ∈ Ideal.span {(p : ℤ)}
  rw [Ideal.mem_span_singleton]

theorem mem_comap_ball (ι : Ω →+* PadicAlgCl p) (x : Ω) :
    x ∈ ((PadicAlgCl.valued p).v.valuationSubring.comap ι) ↔ ‖ι x‖ ≤ 1 := by
  rw [ValuationSubring.mem_comap, Valuation.mem_valuationSubring_iff]
  show ‖ι x‖₊ ≤ 1 ↔ ‖ι x‖ ≤ 1
  rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]


variable (F) in
include F in
theorem exists_compat (A : ValuationSubring Ω) (hp : A.valuation (p : Ω) < 1) :
    ∃ ι : Ω →+* PadicAlgCl p, Compat p A ι := by
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ F Ω
  have : IsAlgClosure ℚ Ω := ⟨IsAlgClosure.isAlgClosed F, inferInstance⟩
  let ι0 : Ω →+* PadicAlgCl p := (IsAlgClosed.lift (R := ℚ) (S := Ω) (M := PadicAlgCl p) : Ω →ₐ[ℚ] PadicAlgCl p)
  let A0 : ValuationSubring Ω := (PadicAlgCl.valued p).v.valuationSubring.comap ι0
  have h0 : Compat p A0 ι0 := mem_comap_ball ι0
  have hp0 : A0.valuation (p : Ω) < 1 := by
    rw [h0.valuation_lt_one_iff, map_natCast]
    have : ((Valued.v (p : PadicAlgCl p) : NNReal) : ℝ) = ‖(p : PadicAlgCl p)‖ := PadicAlgCl.valuation_coe p _
    rw [← this, PadicAlgCl.valuation_p]
    push_cast
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    exact (div_lt_one (by linarith)).mpr hp1
  obtain ⟨g, hg⟩ := exists_smul_eq_of_over (F := ℚ) (lies_over_ratPrime A0 hp0) (lies_over_ratPrime A hp)
  refine ⟨ι0.comp ((g⁻¹ : Ω ≃ₐ[ℚ] Ω) : Ω →+* Ω), fun x => ?_⟩
  rw [← hg]
  have := ValuationSubring.smul_mem_pointwise_smul_iff (g := g) (S := A0) (x := g⁻¹ • x)
  rw [smul_inv_smul] at this
  rw [this, h0]
  rfl

end ReciprocityTheory.Neutral.Cmp
end
end

section

noncomputable section

namespace ReciprocityTheory.Neutral.Cmp

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain ValuativeRel

theorem card_quot_natCast_padicInt (p : ℕ) [Fact p.Prime] {n : ℕ} (hn : n ≠ 0) :
    Nat.card (ℤ_[p] ⧸ Ideal.span {(n : ℤ_[p])}) = p ^ padicValNat p n := by
  have hp := (Fact.out : p.Prime)
  have hdec : n = p ^ padicValNat p n * (n / p ^ padicValNat p n) := by
    have h1 := Nat.ordProj_mul_ordCompl_eq_self n p
    rw [Nat.factorization_def n hp, ← Nat.padicValNat_def] at h1
    exact h1.symm
  have hnd : ¬ p ∣ n / p ^ padicValNat p n := by
    have h1 := Nat.not_dvd_ordCompl hp hn
    rwa [Nat.factorization_def n hp, ← Nat.padicValNat_def] at h1
  have hu : IsUnit (((n / p ^ padicValNat p n : ℕ) : ℤ_[p])) := by
    rw [PadicInt.isUnit_iff]
    by_contra hne
    have hlt : ‖(((n / p ^ padicValNat p n : ℕ) : ℤ_[p]))‖ < 1 :=
      lt_of_le_of_ne (PadicInt.norm_le_one _) hne
    rw [PadicInt.norm_lt_one_iff_dvd] at hlt
    obtain ⟨c, hc⟩ := hlt
    have h1 := congrArg PadicInt.toZMod hc
    rw [map_natCast, map_mul, map_natCast, ZMod.natCast_self, zero_mul,
      ZMod.natCast_eq_zero_iff] at h1
    exact hnd h1
  have hspan : Ideal.span {(n : ℤ_[p])} = Ideal.span {(p : ℤ_[p]) ^ padicValNat p n} := by
    conv_lhs => rw [hdec]
    push_cast
    exact Ideal.span_singleton_mul_right_unit hu _
  rw [hspan, ← PadicInt.ker_toZModPow]
  rw [Nat.card_congr (RingHom.quotientKerEquivOfSurjective
    (ZMod.ringHom_surjective (PadicInt.toZModPow (p := p) (padicValNat p n)))).toEquiv, Nat.card_zmod]

theorem card_quot_span_algebraMap {R C ι : Type*} [CommRing R] [CommRing C] [Algebra R C] [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι R C) (r : R) :
    Nat.card (C ⧸ Ideal.span {algebraMap R C r}) = Nat.card (R ⧸ Ideal.span {r}) ^ Fintype.card ι := by
  let φ : C →ₗ[R] (ι → R ⧸ Ideal.span {r}) :=
    LinearMap.pi fun i => (Ideal.span {r}).mkQ ∘ₗ b.coord i
  have hφ : Function.Surjective φ := by
    intro y
    choose c hc using fun i => Ideal.Quotient.mk_surjective (y i)
    refine ⟨b.equivFun.symm c, ?_⟩
    funext i
    have h1 : b.repr (b.equivFun.symm c) i = c i := by
      rw [← b.equivFun_apply, LinearEquiv.apply_symm_apply]
    simp only [φ, LinearMap.pi_apply, LinearMap.comp_apply, Module.Basis.coord_apply, Submodule.mkQ_apply, h1]
    exact hc i
  have hker : LinearMap.ker φ = (Ideal.span {algebraMap R C r}).restrictScalars R := by
    ext x
    simp only [LinearMap.mem_ker, Submodule.restrictScalars_mem, Ideal.mem_span_singleton']
    constructor
    · intro hx
      have : ∀ i, ∃ a, a * r = b.repr x i := fun i => by
        rw [← Ideal.mem_span_singleton', ← Ideal.Quotient.eq_zero_iff_mem]
        simpa [φ] using congrFun hx i
      choose a ha using this
      refine ⟨b.equivFun.symm a, ?_⟩
      apply b.repr.injective
      ext i
      rw [mul_comm, ← Algebra.smul_def, map_smul, Finsupp.smul_apply, ← b.equivFun_apply,
        LinearEquiv.apply_symm_apply, ← ha, smul_eq_mul, mul_comm]
    · rintro ⟨a, rfl⟩
      funext i
      rw [mul_comm, ← Algebra.smul_def]
      simp only [φ, LinearMap.pi_apply, LinearMap.comp_apply, Module.Basis.coord_apply, map_smul,
        Submodule.mkQ_apply, Pi.zero_apply]
      exact (Submodule.Quotient.mk_eq_zero _).2 (Ideal.mem_span_singleton.2 (dvd_mul_right _ _))
  have e := ((Submodule.Quotient.restrictScalarsEquiv R (Ideal.span {algebraMap R C r})).symm.trans
    (Submodule.quotEquivOfEq _ _ hker.symm)).trans (φ.quotKerEquivOfSurjective hφ)
  rw [Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_eq_fintype_card (α := ι)]

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime]

attribute [local instance] locRel

theorem norm_algebraMap_padicInt_Kloc (ι : Ω →+* PadicAlgCl p) (x : ℤ_[p]) :
    ‖((algebraMap ℤ_[p] (Kloc F ι) x : Kloc F ι) : PadicAlgCl p)‖ ≤ 1 := by
  show ‖algebraMap ℚ_[p] (PadicAlgCl p) (x : ℚ_[p])‖ ≤ 1
  exact (PadicAlgCl.norm_extends p (x : ℚ_[p])).le.trans x.2

def zpToInteger (ι : Ω →+* PadicAlgCl p) : ℤ_[p] →+* 𝒪[Kloc F ι] :=
  (algebraMap ℤ_[p] (Kloc F ι)).codRestrict _
    fun x => (mem_integer_Kloc ι _).2 (norm_algebraMap_padicInt_Kloc ι x)

@[instance_reducible]
def zpAlgInteger (ι : Ω →+* PadicAlgCl p) : Algebra ℤ_[p] 𝒪[Kloc F ι] := (zpToInteger (F := F) ι).toAlgebra

attribute [local instance] zpAlgInteger

end ReciprocityTheory.Neutral.Cmp
end
end
