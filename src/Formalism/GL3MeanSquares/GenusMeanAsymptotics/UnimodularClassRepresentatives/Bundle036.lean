module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle020
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityEleventh
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensitySixth
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.StarAlgebraMap
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.UnitaryDensityFieldBis
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle031
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle034
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

private theorem exists_mem_ideal_form_eq_of_mem_ideal_smul {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (I : Ideal (𝓞 K)) (w x : ↥L)
    (hx : x ∈ (I • ⊤ : Submodule (𝓞 K) ↥L)) :
    ∃ y ∈ I, h (w : V) (x : V) = algebraMap (𝓞 K) K y := by
  refine Submodule.smul_induction_on hx (fun r hr m _ => ?_) (fun x y hx hy => ?_)
  · obtain ⟨o, ho⟩ := Submodule.mem_one.mp (hLi (w : V) w.2 (m : V) m.2)
    refine ⟨r * o, Ideal.mul_mem_right _ _ hr, ?_⟩
    rw [Submodule.coe_smul, ← algebraMap_smul K r (m : V), map_smul, smul_eq_mul, map_mul, ho]
  · obtain ⟨u, hu, hu'⟩ := hx
    obtain ⟨v, hv, hv'⟩ := hy
    exact ⟨u + v, Ideal.add_mem _ hu hv, by rw [Submodule.coe_add, map_add (f := _), hu', hv', map_add (f := _)]⟩

private theorem exists_mem_extP_pow_form_eq_of_mem_extP_pow_smul (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (𝔭 : Ideal (𝓞 F)) (k : ℕ) (w x : ↥L)
    (hx : x ∈ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) :
    ∃ y ∈ extP K 𝔭 ^ k, h (x : V) (w : V) = algebraMap (𝓞 K) K y := by
  refine Submodule.smul_induction_on hx (fun r hr m _ => ?_) (fun x y hx hy => ?_)
  · obtain ⟨o, ho⟩ := Submodule.mem_one.mp (hLi (m : V) m.2 (w : V) w.2)
    refine ⟨conjO K r * o, Ideal.mul_mem_right _ _ (idealPowerSpanBounds.conjO_mem_pow hF 𝔭 k r hr), ?_⟩
    rw [Submodule.coe_smul, ← algebraMap_smul K r (m : V), LinearMap.map_smulₛₗ, LinearMap.smul_apply,
      smul_eq_mul, map_mul, ho]
    congr 1 <;> simp [conjO]
  · obtain ⟨u, hu, hu'⟩ := hx
    obtain ⟨v, hv, hv'⟩ := hy
    exact ⟨u + v, Ideal.add_mem _ hu hv, by
      rw [Submodule.coe_add, map_add (f := _), LinearMap.add_apply, hu', hv', map_add (f := _)]⟩

section Frame

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {m : ℕ} (z : Fin m → ↥L) (g : Fin m → 𝓞 K)

def lin (a : Fin m → 𝓞 K) : ↥L := ∑ i, a i • z i

theorem lin_sub (a b : Fin m → 𝓞 K) : lin z a - lin z b = lin z (a - b) := by
  simp only [lin, ← Finset.sum_sub_distrib, Pi.sub_apply, sub_smul]

theorem coe_lin (a : Fin m → 𝓞 K) : ((lin z a : ↥L) : V) = ∑ i, a i • (z i : V) := by
  simp [lin]

variable {z g}

theorem form_right (hzo : ∀ i j, i ≠ j → h (z i : V) (z j : V) = 0)
    (hzg : ∀ i, h (z i : V) (z i : V) = algebraMap (𝓞 K) K (g i)) (j : Fin m) (c : Fin m → 𝓞 K) :
    h (z j : V) (lin z c : V) = algebraMap (𝓞 K) K (c j * g j) := by

  rw [coe_lin, map_sum, Finset.sum_eq_single j]
  · rw [← algebraMap_smul K (c j) (z j : V), map_smul, hzg, smul_eq_mul, map_mul]
  · intro i _ hij
    rw [← algebraMap_smul K (c i) (z i : V), map_smul, hzo j i (Ne.symm hij), smul_zero]
  · simp

theorem form_lin (hzo : ∀ i j, i ≠ j → h (z i : V) (z j : V) = 0)
    (hzg : ∀ i, h (z i : V) (z i : V) = algebraMap (𝓞 K) K (g i)) (c : Fin m → 𝓞 K) :
    h (lin z c : V) (lin z c : V) = algebraMap (𝓞 K) K (∑ i, conjO K (c i) * c i * g i) := by
  nth_rewrite 1 [coe_lin]

  rw [map_sum, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← algebraMap_smul K (c i) (z i : V), LinearMap.map_smulₛₗ, LinearMap.smul_apply,
    form_right hzo hzg, smul_eq_mul, map_mul, map_mul, map_mul, ← mul_assoc]
  congr 2 <;> simp [conjO]

theorem mk_lin_eq_iff (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (𝔭 : Ideal (𝓞 F)) (k : ℕ)
    (hzo : ∀ i j, i ≠ j → h (z i : V) (z j : V) = 0)
    (hzg : ∀ i, h (z i : V) (z i : V) = algebraMap (𝓞 K) K (g i))
    (hg1 : ∀ i, g i - 1 ∈ extP K 𝔭 ^ k) (a b : Fin m → 𝓞 K) :
    (Submodule.Quotient.mk (lin z a) : ↥L ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) =
      Submodule.Quotient.mk (lin z b) ↔ ∀ i, a i - b i ∈ extP K 𝔭 ^ k := by
  rw [Submodule.Quotient.eq, lin_sub]
  constructor
  · intro hmem i
    have key : ∀ x : ↥L, x ∈ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L) →
        ∃ y ∈ extP K 𝔭 ^ k, h (z i : V) (x : V) = algebraMap (𝓞 K) K y := by
      intro x hx
      refine Submodule.smul_induction_on hx (fun r hr m _ => ?_) (fun x y hx hy => ?_)
      · obtain ⟨o, ho⟩ := Submodule.mem_one.mp (hLi (z i : V) (z i).2 (m : V) m.2)
        refine ⟨r * o, Ideal.mul_mem_right _ _ hr, ?_⟩
        rw [Submodule.coe_smul, ← algebraMap_smul K r (m : V), map_smul, smul_eq_mul, map_mul, ho]
      · obtain ⟨u, hu, hu'⟩ := hx
        obtain ⟨w, hw, hw'⟩ := hy
        exact ⟨u + w, Ideal.add_mem _ hu hw, by rw [Submodule.coe_add, map_add (f := _), hu', hw', map_add (f := _)]⟩
    obtain ⟨y, hy, hyeq⟩ := key _ hmem
    rw [form_right hzo hzg] at hyeq
    have h1 : (a - b) i * g i ∈ extP K 𝔭 ^ k := by
      rw [IsFractionRing.injective (𝓞 K) K hyeq]
      exact hy
    have h2 : (a - b) i * (g i - 1) ∈ extP K 𝔭 ^ k := Ideal.mul_mem_left _ _ (hg1 i)
    have h3 : a i - b i = (a - b) i * g i - (a - b) i * (g i - 1) := by
      simp only [Pi.sub_apply]
      ring
    rw [h3]
    exact Ideal.sub_mem _ h1 h2
  · intro hab
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hab i) Submodule.mem_top

end Frame

private theorem quotient_norm_congr_of_quotient_eq (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (𝔭 : Ideal (𝓞 F)) (k : ℕ) (y y₀ : ↥L)
    (hy : (Submodule.Quotient.mk y : ↥L ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) =
      Submodule.Quotient.mk y₀)
    (o o₀ : 𝓞 K) (ho : h (y : V) (y : V) = algebraMap (𝓞 K) K o)
    (ho₀ : h (y₀ : V) (y₀ : V) = algebraMap (𝓞 K) K o₀) :
    Ideal.Quotient.mk (extP K 𝔭 ^ k) o = Ideal.Quotient.mk (extP K 𝔭 ^ k) o₀ := by
  rw [Submodule.Quotient.eq] at hy
  obtain ⟨u1, hu1, he1⟩ := exists_mem_ideal_form_eq_of_mem_ideal_smul hLi (extP K 𝔭 ^ k) y₀ (y - y₀) hy
  obtain ⟨u2, hu2, he2⟩ := exists_mem_extP_pow_form_eq_of_mem_extP_pow_smul hF hLi 𝔭 k y₀ (y - y₀) hy
  obtain ⟨u3, hu3, he3⟩ := exists_mem_ideal_form_eq_of_mem_ideal_smul hLi (extP K 𝔭 ^ k) (y - y₀) (y - y₀) hy
  have hyx : y = y₀ + (y - y₀) := by abel
  have hsum : o = o₀ + u1 + u2 + u3 := by
    apply IsFractionRing.injective (𝓞 K) K
    rw [← ho, hyx]
    simp only [Submodule.coe_add, map_add (f := _), LinearMap.add_apply]
    rw [he1, he2, he3, ← ho₀]
    ring
  rw [Ideal.Quotient.eq, hsum, show o₀ + u1 + u2 + u3 - o₀ = u1 + u2 + u3 by ring]
  exact Ideal.add_mem _ (Ideal.add_mem _ hu1 hu2) hu3

theorem nkCount_eq_cnt (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 = 0) {k : ℕ} (hk : 1 ≤ k) (n : 𝓞 F) :
    nkCount h L 𝔭 k n = cnt hF 𝔭 k (finrank K V) (ι n) := by
  obtain ⟨z, g, hzo, hzg, hg1⟩ := exists_frame hK hF hs hd hL hLi h𝔭 hv hk
  have hint : ∀ y : ↥L, ∃ o : 𝓞 K, h (y : V) (y : V) = algebraMap (𝓞 K) K o := fun y =>
    let ⟨o, ho⟩ := Submodule.mem_one.mp (hLi (y : V) y.2 (y : V) y.2)
    ⟨o, ho.symm⟩
  have hn : algebraMap F K (n : F) = algebraMap (𝓞 K) K (ι n) := rfl
  let lift : (Fin (finrank K V) → AQ K 𝔭 k) → Fin (finrank K V) → 𝓞 K :=
    fun x i => (Ideal.Quotient.mk_surjective (x i)).choose
  have hlift : ∀ x i, Ideal.Quotient.mk (extP K 𝔭 ^ k) (lift x i) = x i :=
    fun x i => (Ideal.Quotient.mk_surjective (x i)).choose_spec
  let Φ : (Fin (finrank K V) → AQ K 𝔭 k) → ↥L ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L) :=
    fun x => Submodule.Quotient.mk (lin z (lift x))
  have hinj : Function.Injective Φ := by
    intro x x' hxx
    have hd := (mk_lin_eq_iff hLi 𝔭 k hzo hzg hg1 (lift x) (lift x')).mp hxx
    funext i
    rw [← hlift x i, ← hlift x' i, Ideal.Quotient.eq]
    exact hd i
  haveI : Fact (IsFixF K F) := ⟨hF⟩
  haveI : Finite (Fin (finrank K V) → AQ K 𝔭 k) := vectorCountBounds.finite_vec h𝔭 k
  have hcard : Nat.card (↥L ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) =
      Nat.card (Fin (finrank K V) → AQ K 𝔭 k) := by
    rw [MeanB.card_quot_extP hK hF hL h𝔭 k, vectorCountBounds.card_vec hK h𝔭 k, Fintype.card_fin]
    ring_nf
  haveI : Finite (↥L ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact Nat.card_pos.ne')
  have hbij : Function.Bijective Φ := hinj.bijective_of_nat_card_le hcard.le
  have hsum : ∀ x, Ideal.Quotient.mk (extP K 𝔭 ^ k) (∑ i, conjO K (lift x i) * lift x i * g i) =
      ∑ i, sg hF 𝔭 k (x i) * x i := by
    intro x

    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hg : Ideal.Quotient.mk (extP K 𝔭 ^ k) (g i) = 1 := by
      rw [← map_one (Ideal.Quotient.mk (extP K 𝔭 ^ k)), Ideal.Quotient.eq]
      exact hg1 i
    rw [map_mul, map_mul, hg, mul_one]
    conv_rhs => rw [← hlift x i]
    unfold sg
    rw [NormLifting.conjQ_mk]
  unfold nkCount cnt
  refine (Nat.card_congr ((Equiv.ofBijective Φ hbij).subtypeEquiv (fun x => ?_))).symm
  show _ ↔ ∃ y : ↥L, Submodule.Quotient.mk y = Φ x ∧ _
  constructor
  · intro hx
    refine ⟨lin z (lift x), rfl, ?_⟩
    rw [form_lin hzo hzg, hn, integralBasisSpans.congrP_int h𝔭, hsum x, hx]
  · rintro ⟨y, hy, hc⟩
    obtain ⟨o, ho⟩ := hint y
    have hcg := quotient_norm_congr_of_quotient_eq hF hLi 𝔭 k y (lin z (lift x)) hy o _ ho (form_lin hzo hzg (lift x))
    rw [ho, hn, integralBasisSpans.congrP_int h𝔭, hcg, hsum x] at hc
    exact hc

end Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
end
end

section

open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.HU

open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K

theorem form_cmb {h : V →ₗ⋆[K] V →ₗ[K] K} (b : Basis κ K V) {H : Matrix κ κ (𝓞 K)}
    (hH : ∀ i j, jK (H i j) = h (b i) (b j)) (c c' : κ → 𝓞 K) :
    h (cmb b c : V) (cmb b c' : V) = jK (star c ⬝ᵥ (H *ᵥ c')) := by
  have hst : ∀ r : 𝓞 K, jK (star r) = star (jK r) := fun r => rfl
  have hl : ∀ (r : 𝓞 K) (v w : V), h (r • v) w = star (jK r) * h v w := fun r v w => by
    rw [← algebraMap_smul K r v, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply]
  have hr : ∀ (r : 𝓞 K) (v w : V), h v (r • w) = jK r * h v w := fun r v w => by
    rw [← algebraMap_smul K r w, map_smul, smul_eq_mul]
  have expand : h (∑ i, c i • b i) (∑ j, c' j • b j) =
      ∑ i, ∑ j, star (jK (c i)) * (jK (c' j) * h (b i) (b j)) := by
    have h1 : ∀ w : V, h (∑ i, c i • b i) w = ∑ i, star (jK (c i)) * h (b i) w := by
      intro w

      rw [map_sum, LinearMap.sum_apply]
      exact Finset.sum_congr rfl fun i _ => hl _ _ _
    rw [h1]
    refine Finset.sum_congr rfl fun i _ => ?_

    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hr]
  have rhs : jK (star c ⬝ᵥ (H *ᵥ c')) = ∑ i, ∑ j, star (jK (c i)) * (jK (H i j) * jK (c' j)) := by

    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, map_sum, map_mul, hst, Finset.mul_sum]
  rw [coe_cmb, coe_cmb, expand, rhs]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← hH]
  ring

theorem inP_jK_iff {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) (a : 𝓞 K) :
    InP 𝔭 k (jK a) ↔ a ∈ extP K 𝔭 ^ k := by
  constructor
  · rintro ⟨t, ht, z, hz, hzt⟩
    have e1 : z = ι t * a := by
      apply IsFractionRing.injective (𝓞 K) K
      rw [hzt, map_mul]
    obtain ⟨y, i, hi, hyi⟩ := h𝔭.exists_inv ht
    obtain ⟨q, hq⟩ := sub_dvd_pow_sub_pow (1 : 𝓞 F) i k
    have e0 : (1 : 𝓞 F) - i = y * t := by linear_combination -hyi
    rw [e0, one_pow] at hq
    have e2 : (1 : 𝓞 F) = i ^ k + y * t * q := by linear_combination hq
    have h1 := congrArg ι e2
    simp only [map_one, map_add (f := _), map_mul] at h1
    have e3 : a = ι (i ^ k) * a + ι y * ι q * (ι t * a) := by linear_combination a * h1
    rw [e3]
    refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ ?_) (Ideal.mul_mem_left _ _ (by rw [← e1]; exact hz))
    rw [map_pow]
    exact Ideal.pow_mem_pow (Ideal.mem_map_of_mem _ hi) k
  · intro ha
    exact ⟨1, fun h1 => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 h1), a, ha, by simp⟩

theorem smul_mono_pow {𝔭 : Ideal (𝓞 F)} {A : Submodule (𝓞 K) V} {j k : ℕ} (hjk : j ≤ k) :
    (extP K 𝔭 ^ k • A : Submodule (𝓞 K) V) ≤ extP K 𝔭 ^ j • A := Submodule.smul_mono_left (Ideal.pow_le_pow_right hjk)

theorem aut_mem {h : V →ₗ⋆[K] V →ₗ[K] K} {A : Submodule (𝓞 K) V} {g : V ≃ₗ[K] V} (hg : g ∈ autSub h A)
    {x : V} (hx : x ∈ A) : g x ∈ A := by
  have hg' : Formalism.HermitianLatticesTheory.gmap g A = A := hg.2
  rw [← hg']
  exact Submodule.mem_map_of_mem hx

theorem aut_mem_smul {h : V →ₗ⋆[K] V →ₗ[K] K} {A : Submodule (𝓞 K) V} {g : V ≃ₗ[K] V}
    (hg : g ∈ autSub h A) (J : Ideal (𝓞 K)) {x : V} (hx : x ∈ J • A) : g x ∈ J • A := by
  have hs : ∀ (r : 𝓞 K) (v : V), g (r • v) = r • g v := fun r v => by
    rw [← algebraMap_smul K r v, map_smul, algebraMap_smul]
  refine Submodule.smul_induction_on (p := fun w => g w ∈ J • A) hx (fun r hr a ha => ?_)
    (fun u w hu hw => ?_)
  · simp only [hs]
    exact Submodule.smul_mem_smul hr (aut_mem hg ha)
  · simp only [map_add (f := _)]
    exact Submodule.add_mem _ hu hw

theorem aut_cmb {𝔭 : Ideal (𝓞 F)} (b : Basis κ K V) {g : V ≃ₗ[K] V} {Y : Matrix κ κ (𝓞 K)} {j : ℕ}
    (hgY : ∀ i, g (b i) - ∑ l, Y l i • b l ∈ (extP K 𝔭 ^ j • locF 𝔭 (spanO b) : Submodule (𝓞 K) V))
    (c : κ → 𝓞 K) :
    g (cmb b c : V) - (cmb b (Y *ᵥ c) : V) ∈ (extP K 𝔭 ^ j • locF 𝔭 (spanO b) : Submodule (𝓞 K) V) := by
  have hs : ∀ (r : 𝓞 K) (v : V), g (r • v) = r • g v := fun r v => by
    rw [← algebraMap_smul K r v, map_smul, algebraMap_smul]
  have e : ∑ l, (Y *ᵥ c) l • b l = ∑ i, c i • ∑ l, Y l i • b l := by
    simp only [Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
    rw [mul_comm]

  rw [coe_cmb, coe_cmb, map_sum, e]
  simp only [hs]
  rw [← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [← smul_sub]
  exact Submodule.smul_mem _ (c i) (hgY i)

theorem exists_matrix_of_end {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) [𝔭.IsPrime] (b : Basis κ K V) (k : ℕ)
    (X : Module.End (𝓞 K) (QA 𝔭 b k)) : ∃ Y : Matrix κ κ (𝓞 K),
      ∀ i, X (Submodule.Quotient.mk (inA 𝔭 b (cmb b (Pi.single i 1)))) =
        Submodule.Quotient.mk (inA 𝔭 b (cmb b fun l => Y l i)) := by
  choose c hc using fun i : κ =>
    exists_cmb h𝔭 b k (X (Submodule.Quotient.mk (inA 𝔭 b (cmb b (Pi.single i 1)))))
  exact ⟨Matrix.of fun l i => c i l, hc⟩

theorem exists_isom_lift_basis (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0) (b : Basis κ K V) {H : Matrix κ κ (𝓞 K)}
    (hH : ∀ i j, jK (H i j) = h (b i) (b j)) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {e k : ℕ}
    (he : IsE h (locF 𝔭 (spanO b)) 𝔭 e) (hk : e + 1 ≤ k) (X : Module.End (𝓞 K) (QA 𝔭 b k))
    (hX : ∀ x y x' y' : ↥(locF 𝔭 (spanO b)), Submodule.Quotient.mk x' = X (Submodule.Quotient.mk x) →
      Submodule.Quotient.mk y' = X (Submodule.Quotient.mk y) →
      CongrP 𝔭 k (h (x' : V) (y' : V)) (h (x : V) (y : V))) :
    ∃ g ∈ autSub h (locF 𝔭 (spanO b)), ∀ x x' : ↥(locF 𝔭 (spanO b)),
      Submodule.Quotient.mk x' = X (Submodule.Quotient.mk x) →
      g x - x' ∈ ((extP K 𝔭) ^ (k - e) • (locF 𝔭 (spanO b)) : Submodule (𝓞 K) V) := by
  have := h𝔭.isPrime
  obtain ⟨Y, hXY⟩ := exists_matrix_of_end h𝔭 b k X
  have hY : ∀ i j, (Yᴴ * H * Y - H) i j ∈ extP K 𝔭 ^ k := by
    intro i j
    have h1 := hX _ _ _ _ (hXY i).symm (hXY j).symm
    rw [congrP_iff_inP, coe_inA, coe_inA, coe_inA, coe_inA, form_cmb b hH, form_cmb b hH, ← form_col,
      form_single, ← map_sub, inP_jK_iff h𝔭] at h1
    exact h1
  have hlift : ∃ g ∈ autSub h (locF 𝔭 (spanO b)), ∀ i, g (b i) - ∑ l, Y l i • b l ∈
      (extP K 𝔭 ^ (k - e) • locF 𝔭 (spanO b) : Submodule (𝓞 K) V) := by
    exact exists_isom_matrix hK hF hs hd b hH h𝔭 he hk Y hY
  obtain ⟨g, hg, hgY⟩ := hlift
  refine ⟨g, hg, fun x x' hxx' => ?_⟩
  obtain ⟨c, hc⟩ := exists_cmb h𝔭 b k (Submodule.Quotient.mk x)
  rw [hc, end_apply_cmb b k X Y hXY c, mk_eq_iff] at hxx'
  rw [mk_eq_iff] at hc
  have e1 : g (x : V) - x' = g ((x : V) - (inA 𝔭 b (cmb b c) : V)) +
      (g (cmb b c : V) - (cmb b (Y *ᵥ c) : V)) - ((x' : V) - (inA 𝔭 b (cmb b (Y *ᵥ c)) : V)) := by
    rw [map_sub, coe_inA, coe_inA]
    abel
  rw [e1]
  exact sub_mem (add_mem (smul_mono_pow (Nat.sub_le k e) (aut_mem_smul hg _ hc)) (aut_cmb b hgY c))
    (smul_mono_pow (Nat.sub_le k e) hxx')

end Formalism.HermitianLattices.Ext.L3.HU
end
end
