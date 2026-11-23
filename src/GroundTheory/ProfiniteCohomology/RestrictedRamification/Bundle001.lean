module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.Unramified.Locus
public import Mathlib.RingTheory.DedekindDomain.SelmerGroup
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
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.RingTheory.Henselian
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
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Ramification

@[expose] public section

section

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain

variable {F : Type*} [Field F]

section Places

variable {L : Type*} [Field L] [Algebra F L]

def placesOver (S : Set (HeightOneSpectrum (𝓞 F))) : Set (HeightOneSpectrum (𝓞 L)) :=
  {w | ∃ v ∈ S, w.asIdeal.LiesOver v.asIdeal}

end Places

variable {Ω : Type*} [Field Ω] [Algebra F Ω]

def IsUnramifiedOutside (S : Set (HeightOneSpectrum (𝓞 F))) (E : IntermediateField F Ω) : Prop :=
  ∀ v ∉ S, Algebra.IsUnramifiedIn (𝓞 E) v.asIdeal


variable (F Ω) in
noncomputable def maxUnramifiedOutside (S : Set (HeightOneSpectrum (𝓞 F))) :
    IntermediateField F Ω :=
  ⨆ (E : IntermediateField F Ω) (_ : FiniteDimensional F E) (_ : IsUnramifiedOutside S E), E


variable (F Ω) in
abbrev galUnramifiedOutside (S : Set (HeightOneSpectrum (𝓞 F))) :=
  Gal(maxUnramifiedOutside (F := F) (Ω := Ω) S / F)

end GroundTheory.ProfCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

open scoped Pointwise

theorem eq_of_forall_le_exp_iff {a b : WithZero (Multiplicative ℤ)} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (ha1 : a ≤ 1) (hb1 : b ≤ 1)
    (h : ∀ n : ℕ, a ≤ WithZero.exp (-(n : ℤ)) ↔ b ≤ WithZero.exp (-(n : ℤ))) : a = b := by
  have key : ∀ {a b : WithZero (Multiplicative ℤ)}, a ≠ 0 → a ≤ 1 →
      (∀ n : ℕ, a ≤ WithZero.exp (-(n : ℤ)) → b ≤ WithZero.exp (-(n : ℤ))) → b ≤ a := by
    intro a b ha0 ha1 h
    have hlog : WithZero.log a ≤ 0 := by
      rw [← WithZero.exp_le_exp, WithZero.exp_log ha0, WithZero.exp_zero]
      exact ha1
    have hn : ((-WithZero.log a).toNat : ℤ) = -WithZero.log a := Int.toNat_of_nonneg (by omega)
    have := h (-WithZero.log a).toNat (by rw [hn, neg_neg, WithZero.exp_log ha0])
    rwa [hn, neg_neg, WithZero.exp_log ha0] at this
  exact le_antisymm (key hb0 hb1 fun n => (h n).2) (key ha0 ha1 fun n => (h n).1)

section Conjugate

variable {B : Type*} [CommRing B] [IsDedekindDomain B] {G : Type*} [Group G]
  [MulSemiringAction G B]

def smulPlace (σ : G) (w : HeightOneSpectrum B) : HeightOneSpectrum B where
  asIdeal := σ • w.asIdeal
  isPrime := Ideal.map_isPrime_of_equiv (MulSemiringAction.toRingEquiv G B σ)
  ne_bot := by
    intro h
    apply w.ne_bot
    rw [← inv_smul_smul σ w.asIdeal, h]
    exact Ideal.map_bot

omit [IsDedekindDomain B] in
theorem smulPlace_asIdeal (σ : G) (w : HeightOneSpectrum B) :
    (smulPlace σ w).asIdeal = σ • w.asIdeal :=
  rfl

theorem intValuation_smulPlace (σ : G) (w : HeightOneSpectrum B) (r : B) :
    (smulPlace σ w).intValuation (σ • r) = w.intValuation r := by
  rcases eq_or_ne r 0 with rfl | hr
  · rw [smul_zero, map_zero, map_zero]
  have hσr : σ • r ≠ 0 := fun h => hr (by rw [← inv_smul_smul σ r, h, smul_zero])
  refine eq_of_forall_le_exp_iff (intValuation_ne_zero _ _ hσr) (intValuation_ne_zero _ _ hr)
    (intValuation_le_one _ _) (intValuation_le_one _ _) fun n => ?_
  rw [intValuation_le_pow_iff_mem, intValuation_le_pow_iff_mem, smulPlace_asIdeal, ← smul_pow']
  exact Ideal.smul_mem_pointwise_smul_iff

end Conjugate

section NumberField

variable {F M : Type*} [Field F] [Field M] [NumberField M] [Algebra F M]

theorem valuation_smulPlace (σ : Gal(M/F)) (w : HeightOneSpectrum (𝓞 M)) (x : M) :
    (smulPlace σ w).valuation M (σ x) = w.valuation M x := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 M) x
  have ha : σ (algebraMap (𝓞 M) M a) = algebraMap (𝓞 M) M (σ • a) := rfl
  have hb' : σ (algebraMap (𝓞 M) M b) = algebraMap (𝓞 M) M (σ • b) := rfl
  rw [map_div₀, ha, hb', map_div₀, map_div₀, valuation_of_algebraMap, valuation_of_algebraMap,
    valuation_of_algebraMap, valuation_of_algebraMap, intValuation_smulPlace,
    intValuation_smulPlace]

theorem valuation_smulPlace_apply (σ : Gal(M/F)) (w : HeightOneSpectrum (𝓞 M)) (x : M) :
    (smulPlace σ w).valuation M x = w.valuation M (σ⁻¹ x) := by
  rw [← valuation_smulPlace σ w (σ⁻¹ x)]
  congr 1
  exact (AlgEquiv.apply_symm_apply σ x).symm

end NumberField

section Unramified

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

theorem valuation_algebraMap_of_isUnramifiedAt (w : HeightOneSpectrum (𝓞 K))
    (W : HeightOneSpectrum (𝓞 L)) [W.asIdeal.LiesOver w.asIdeal]
    [Algebra.IsUnramifiedAt (𝓞 K) W.asIdeal] (x : K) :
    W.valuation L (algebraMap K L x) = w.valuation K x := by
  rw [← valuation_liesOver L w W x,
    Ideal.ramificationIdx_eq_one, pow_one]

end Unramified

end GroundTheory.ProfCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {F : Type*} [Field F] [NumberField F]

noncomputable def ordAt (v : HeightOneSpectrum (𝓞 F)) (x : Fˣ) : ℤ :=
  -Multiplicative.toAdd (v.valuationOfNeZero x)

theorem ordAt_mul (v : HeightOneSpectrum (𝓞 F)) (x y : Fˣ) :
    ordAt v (x * y) = ordAt v x + ordAt v y := by
  simp only [ordAt, map_mul, toAdd_mul, neg_add]

theorem ordAt_one (v : HeightOneSpectrum (𝓞 F)) : ordAt v (1 : Fˣ) = 0 := by
  simp [ordAt]

theorem ordAt_inv (v : HeightOneSpectrum (𝓞 F)) (x : Fˣ) : ordAt v x⁻¹ = -ordAt v x := by
  simp [ordAt]

theorem ordAt_eq_zero_iff (v : HeightOneSpectrum (𝓞 F)) (x : Fˣ) :
    ordAt v x = 0 ↔ v.valuation F (x : F) = 1 := by
  rw [ordAt, neg_eq_zero, ← valuationOfNeZero_eq, ← WithZero.coe_one, WithZero.coe_inj,
    ← toAdd_one]
  exact Multiplicative.toAdd.injective.eq_iff

theorem valuation_eq_exp_neg_ordAt (v : HeightOneSpectrum (𝓞 F)) (x : Fˣ) :
    v.valuation F (x : F) = WithZero.exp (-ordAt v x) := by
  rw [ordAt, neg_neg, ← valuationOfNeZero_eq]
  rfl

theorem finite_ordAt_ne_zero (x : Fˣ) : {v : HeightOneSpectrum (𝓞 F) | ordAt v x ≠ 0}.Finite := by
  refine ((Support.finite (𝓞 F) (x : F)).union (Support.finite (𝓞 F) ((x⁻¹ : Fˣ) : F))).subset ?_
  intro v hv
  have hv' : v.valuation F (x : F) ≠ 1 := fun h => hv ((ordAt_eq_zero_iff v x).2 h)
  rcases lt_or_gt_of_ne hv' with h | h
  · right
    change 1 < v.valuation F ((x⁻¹ : Fˣ) : F)
    rw [Units.val_inv_eq_inv_val, map_inv₀]
    exact one_lt_inv₀ (lt_of_le_of_ne zero_le (((map_ne_zero (v.valuation F)).2 x.ne_zero)).symm)
      |>.2 h
  · left
    exact h

variable (S : Set (HeightOneSpectrum (𝓞 F)))

abbrev sDivisor := {v : HeightOneSpectrum (𝓞 F) // v ∉ S} →₀ ℤ

noncomputable def divS : Additive Fˣ →+ sDivisor S where
  toFun x := Finsupp.ofSupportFinite (fun v => ordAt v.1 (Additive.toMul x)) (by
    refine ((finite_ordAt_ne_zero (Additive.toMul x)).preimage
      Subtype.val_injective.injOn).subset ?_
    intro v hv
    exact hv)
  map_zero' := by
    ext v
    simp [Finsupp.ofSupportFinite_coe, ordAt_one]
  map_add' x y := by
    ext v
    simp [Finsupp.ofSupportFinite_coe, toMul_add, ordAt_mul]

theorem divS_apply (x : Additive Fˣ) (v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}) :
    divS S x v = ordAt v.1 (Additive.toMul x) :=
  rfl

abbrev sPic := sDivisor S ⧸ (divS S).range

noncomputable abbrev sPicMk : sDivisor S →+ sPic S := QuotientAddGroup.mk' (divS S).range

theorem sPicMk_eq_zero_iff (D : sDivisor S) : sPicMk S D = 0 ↔ ∃ x : Fˣ, divS S (Additive.ofMul x) = D := by
  rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, AddMonoidHom.mem_range]
  exact ⟨fun ⟨x, hx⟩ => ⟨Additive.toMul x, hx⟩, fun ⟨x, hx⟩ => ⟨Additive.ofMul x, hx⟩⟩

end GroundTheory.ProfCoh
end
