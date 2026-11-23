module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle007
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle067
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle069
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Mathlib.NumberTheory.LocalField.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle068
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Mathlib.RingTheory.Norm.Basic
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005

@[expose] public section

section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory


open Polynomial in
theorem cgA_pow_of_mem_nonunits {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ)
    [hl : Fact l.Prime] (A : ValuationSubring Ω) (hlA : ((l : ℕ) : Ω) ∈ A.nonunits)
    (x : Ω) (hx : x ∈ A.nonunits) : ∃ k : ℕ, CgA A l 1 (x ^ k) 0 := by
  classical
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  have hl0 : ((l : ℕ) : Ω) ≠ 0 := by exact_mod_cast hl.out.ne_zero
  have hvl : A.valuation (l : Ω) < 1 := (A.mem_nonunits_iff).1 hlA
  have hvx : A.valuation x < 1 := (A.mem_nonunits_iff).1 hx
  have hvl0 : A.valuation (l : Ω) ≠ 0 := by simpa using hl0
  have key : ∀ k : ℕ, A.valuation x ^ k ≤ A.valuation (l : Ω) → CgA A l 1 (x ^ k) 0 := by
    intro k hk
    refine ⟨x ^ k / l, ?_, ?_⟩
    · rw [← A.valuation_le_one_iff, map_div₀, map_pow]
      exact (div_le_one₀ (zero_lt_iff.2 hvl0)).2 hk
    · rw [sub_zero, pow_one]; field_simp
  by_contra H
  push_neg at H
  have hlt : ∀ k : ℕ, A.valuation (l : Ω) < A.valuation x ^ k :=
    fun k => not_le.1 (fun h => H k (key k h))
  have hx0 : x ≠ 0 := by
    intro h
    have := hlt 1
    simp [h] at this
  have hvx0 : A.valuation x ≠ 0 := by simpa using hx0

  have hint : ∀ n : ℤ, A.valuation (n : Ω) ≤ 1 := fun n =>
    (A.valuation_le_one_iff _).2 (intCast_mem A n)
  have hdvd : ∀ n : ℤ, (l : ℤ) ∣ n → A.valuation (n : Ω) ≤ A.valuation (l : Ω) := by
    rintro n ⟨m, rfl⟩
    push_cast
    rw [map_mul]
    exact mul_le_of_le_one_right' (hint m)
  have hpl : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl.out
  have hunit : ∀ n : ℤ, ¬ (l : ℤ) ∣ n → A.valuation (n : Ω) = 1 := by
    intro n hn
    refine le_antisymm (hint n) (not_lt.1 fun h => ?_)
    obtain ⟨a, b, hab⟩ := (Prime.coprime_iff_not_dvd hpl).2 hn
    have h1 : ((a : Ω) * (l : Ω) + (b : Ω) * (n : Ω)) = 1 := by exact_mod_cast hab
    have h2 : A.valuation ((a : Ω) * (l : Ω) + (b : Ω) * (n : Ω)) < 1 := by
      apply Valuation.map_add_lt
      · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint a)) hvl
      · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint b)) h
    rw [h1, map_one] at h2
    exact lt_irrefl _ h2

  obtain ⟨p, hp0, hpx⟩ := (IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).2 (Algebra.IsAlgebraic.isAlgebraic x)
  set q := p.primPart with hqdef
  have hqprim : q.IsPrimitive := isPrimitive_primPart p
  have hqx : aeval x q = 0 := by
    have hc : p.content ≠ 0 := by
      intro h; exact hp0 ((content_eq_zero_iff).1 h)
    have h := hpx
    rw [eq_C_content_mul_primPart p, map_mul, aeval_C] at h
    rcases mul_eq_zero.1 h with h' | h'
    · exfalso; apply hc; simpa using h'
    · exact h'
  have hex : ∃ i, ¬ (l : ℤ) ∣ q.coeff i := by
    by_contra h
    push_neg at h
    have hu := hqprim (l : ℤ) ((C_dvd_iff_dvd_coeff _ _).2 h)
    exact hpl.not_unit hu
  set i0 := Nat.find hex with hi0
  have hi0spec : ¬ (l : ℤ) ∣ q.coeff i0 := Nat.find_spec hex
  have hi0min : ∀ i < i0, (l : ℤ) ∣ q.coeff i := fun i hi => by
    simpa using Nat.find_min hex hi
  have hi0deg : i0 < q.natDegree + 1 := by
    by_contra h
    apply hi0spec
    rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    exact dvd_zero _
  set f : ℕ → Ω := fun i => (q.coeff i : Ω) * x ^ i with hf
  have hsum : aeval x q = ∑ i ∈ Finset.range (q.natDegree + 1), f i := by
    rw [aeval_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [hf, zsmul_eq_mul]
  have hfi0 : A.valuation (f i0) = A.valuation x ^ i0 := by
    simp only [hf, map_mul, map_pow, hunit _ hi0spec, one_mul]
  have hg : A.valuation x ^ i0 ≠ 0 := pow_ne_zero _ hvx0
  have hrest : A.valuation (∑ i ∈ (Finset.range (q.natDegree + 1)).erase i0, f i)
      < A.valuation x ^ i0 := by
    apply Valuation.map_sum_lt _ hg
    intro i hi
    have hne : i ≠ i0 := Finset.ne_of_mem_erase hi
    simp only [hf, map_mul, map_pow]
    rcases lt_or_gt_of_ne hne with h | h
    · calc A.valuation (q.coeff i : Ω) * A.valuation x ^ i
            ≤ A.valuation (l : Ω) * 1 :=
              mul_le_mul' (hdvd _ (hi0min i h)) (pow_le_one₀ zero_le' hvx.le)
        _ = A.valuation (l : Ω) := mul_one _
        _ < A.valuation x ^ i0 := hlt i0
    · calc A.valuation (q.coeff i : Ω) * A.valuation x ^ i
            ≤ 1 * A.valuation x ^ i := mul_le_mul' (hint _) le_rfl
        _ = A.valuation x ^ i := one_mul _
        _ < A.valuation x ^ i0 := pow_lt_pow_right_of_lt_one₀ (zero_lt_iff.2 hvx0) hvx h
  have htot : A.valuation (aeval x q) = A.valuation x ^ i0 := by
    rw [hsum, ← Finset.add_sum_erase _ _ (Finset.mem_range.2 hi0deg),
      Valuation.map_add_eq_of_lt_left _ (by rw [hfi0]; exact hrest), hfi0]
  rw [hqx, map_zero] at htot
  exact hg htot.symm

end GlobalTheory
end

section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

noncomputable section

namespace GlobalTheory.DlRescale

def mulN (N : ℕ) : ℚ →+ ℚ := AddMonoidHom.mulLeft (N : ℚ)

theorem mulN_le (N : ℕ) (hN : 0 < N) (g g' : ℚ) : mulN N g ≤ mulN N g' ↔ g ≤ g' := by
  have : (0:ℚ) < N := by exact_mod_cast hN
  simp [mulN, mul_le_mul_iff_of_pos_left this]

theorem mulN_inj (N : ℕ) (hN : 0 < N) : Function.Injective (mulN N) := fun g g' h =>
  le_antisymm ((mulN_le N hN g g').1 h.le) ((mulN_le N hN g' g).1 h.ge)

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

def resc (N : ℕ) (hN : 0 < N) : HahnSeries ℚ Ω →+* HahnSeries ℚ Ω :=
  HahnSeries.embDomainRingHom (mulN N) (mulN_inj N hN) (mulN_le N hN)

theorem resc_coeff (N : ℕ) (hN : 0 < N) (ψ : HahnSeries ℚ Ω) (r : ℚ) :
    (resc N hN ψ).coeff r = ψ.coeff (r / N) := by
  have hN' : (N:ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have e : r = mulN N (r / N) := by simp [mulN]; field_simp
  conv_lhs => rw [e]
  simp only [resc, HahnSeries.embDomainRingHom_apply]
  exact HahnSeries.embDomain_coeff (f := ⟨⟨mulN N, mulN_inj N hN⟩, mulN_le N hN _ _⟩)

theorem forall_div (N : ℕ) (hN : 0 < N) (Q : ℚ → Prop) : (∀ r : ℚ, Q (r / N)) ↔ ∀ r, Q r := by
  have hN' : (N:ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  refine ⟨fun h r => ?_, fun h r => h _⟩
  have := h (N * r)
  rwa [mul_div_cancel_left₀ r hN'] at this

theorem theta_resc (N : ℕ) (hN : 0 < N) (s : ℚ) (ψ : HahnSeries ℚ Ω) :
    theta (s / N) (resc N hN ψ) = resc N hN (theta s ψ) := by
  ext r
  simp only [theta, resc_coeff]
  congr 2
  ring

theorem prim_resc (A : ValuationSubring Ω) (N : ℕ) (hN : 0 < N) (ψ : HahnSeries ℚ Ω) :
    Prim A (resc N hN ψ) ↔ Prim A ψ := by
  unfold Prim
  simp only [resc_coeff]
  rw [forall_div N hN (fun r => ψ.coeff r ∈ A)]
  constructor
  · rintro ⟨h1, r, h2, h3⟩; exact ⟨h1, r / N, h2, h3⟩
  · rintro ⟨h1, r, h2, h3⟩
    have hN' : (N:ℚ) ≠ 0 := by exact_mod_cast hN.ne'
    refine ⟨h1, N * r, ?_⟩
    rw [mul_div_cancel_left₀ r hN']; exact ⟨h2, h3⟩

theorem eOm_zero (ε : Ω →+* ℂ) : eOm ε 0 = 1 := by
  unfold eOm
  simp only [Rat.cast_zero, mul_zero, Complex.exp_zero]
  rw [← map_one ε]
  exact Function.leftInverse_invFun ε.injective 1

theorem exp_sl_diag (ε : Ω →+* ℂ) (X : Tower Ω ε) (N : ℕ) (hN : 0 < N) (u : X.K) :
    X.exp (X.sl (toGQ !![(N : ℤ), 0; 0, 1]) u) = resc N hN (X.exp u) := by
  have hdet : (0 : ℤ) < (!![(N : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det := by
    simp [Matrix.det_fin_two]; exact_mod_cast hN
  have e00 : ent (toGQ !![(N : ℤ), 0; 0, 1]) 0 0 = N := by simp [ent, toGQ, hN, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  have e01 : ent (toGQ !![(N : ℤ), 0; 0, 1]) 0 1 = 0 := by simp [ent, toGQ, hN, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  have e10 : ent (toGQ !![(N : ℤ), 0; 0, 1]) 1 0 = 0 := by simp [ent, toGQ, hN, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  have e11 : ent (toGQ !![(N : ℤ), 0; 0, 1]) 1 1 = 1 := by simp [ent, toGQ, hN, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  have hN' : (N:ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  ext r
  rw [resc_coeff]
  have h := X.exp_upper (toGQ !![(N : ℤ), 0; 0, 1]) e10 u (r / N)
  rw [e00, e01, e11, mul_zero, zero_div, eOm_zero, one_mul, div_one, div_mul_cancel₀ r hN'] at h
  exact h

end GlobalTheory.DlRescale

end

open GlobalTheory.DlRescale in
theorem GlobalTheory.Glue.isDl_rescale : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ (n N : ℕ) (s : ℚ) (f : X.K) (φ φ' : HahnSeries ℚ Ω), 0 < N → (∀ r : ℚ, φ'.coeff r = φ.coeff (r / N)) → (IsDl X A l n s f φ ↔ IsDl X A l n (s / N) (X.sl (toGQ !![(N : ℤ), 0; 0, 1]) f) φ') := by
  intro Ω _ _ _ ε X _ l _ A _ n N s f φ φ' hN hφ
  have hφ' : φ' = resc N hN φ := by ext r; rw [hφ, resc_coeff]
  subst hφ'
  have hexp := exp_sl_diag ε X N hN
  set g := toGQ !![(N : ℤ), 0; 0, 1]
  have key : ∀ a b : X.K, (∀ r, CgA A l n ((resc N hN φ * X.exp (X.sl g a) * X.exp (X.sl g b)).coeff r)
      ((theta (s / N) (X.exp (X.sl g a)) * X.exp (X.sl g b) - X.exp (X.sl g a) * theta (s / N) (X.exp (X.sl g b))).coeff r)) ↔
      ∀ r, CgA A l n ((φ * X.exp a * X.exp b).coeff r) ((theta s (X.exp a) * X.exp b - X.exp a * theta s (X.exp b)).coeff r) := by
    intro a b
    simp only [hexp, theta_resc, ← map_mul, ← map_sub, resc_coeff]
    exact forall_div N hN (fun r => CgA A l n ((φ * X.exp a * X.exp b).coeff r) ((theta s (X.exp a) * X.exp b - X.exp a * theta s (X.exp b)).coeff r))
  have hA : (∀ r, (resc N hN φ).coeff r ∈ A) ↔ ∀ r, φ.coeff r ∈ A := by
    simp only [resc_coeff]; exact forall_div N hN (fun r => φ.coeff r ∈ A)
  constructor
  · rintro ⟨h0, a, b, κ, hκ, hfb, pa, pb, hc⟩
    refine ⟨hA.2 h0, X.sl g a, X.sl g b, κ, hκ, ?_, ?_, ?_, (key a b).2 hc⟩
    · rw [← map_mul, hfb, map_mul, AlgEquiv.commutes]
    · rw [hexp]; exact (prim_resc A N hN _).2 pa
    · rw [hexp]; exact (prim_resc A N hN _).2 pb
  · rintro ⟨h0, a', b', κ, hκ, hfb, pa, pb, hc⟩
    obtain ⟨a, rfl⟩ := (X.sl g).surjective a'
    obtain ⟨b, rfl⟩ := (X.sl g).surjective b'
    refine ⟨hA.1 h0, a, b, κ, hκ, ?_, ?_, ?_, (key a b).1 hc⟩
    · apply (X.sl g).injective
      rw [map_mul, map_mul, AlgEquiv.commutes]; exact hfb
    · rw [hexp] at pa; exact (prim_resc A N hN _).1 pa
    · rw [hexp] at pb; exact (prim_resc A N hN _).1 pb
end

section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.PrimConst

open NumberField

theorem exists_dividing {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω)
    {ι : Type} (c : ι → Ω) (E : IntermediateField ℚ Ω) [FiniteDimensional ℚ E] (D : ℕ) (hD : 0 < D)
    (hc : ∀ i, c i ∈ E ∧ IsIntegral ℤ ((D : Ω) * c i))
    (hne : ∃ i, c i ≠ 0) : ∃ i0, c i0 ≠ 0 ∧ ∀ i, c i * (c i0)⁻¹ ∈ A := by
  classical
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : NumberField E := by
    refine { to_charZero := inferInstance, to_finiteDimensional := ?_ }
    convert ‹FiniteDimensional ℚ E›
    exact Subsingleton.elim _ _
  have hmem : ∀ i, (D : Ω) * c i ∈ E := fun i => E.mul_mem (E.natCast_mem D) (hc i).1
  let f : ι → 𝓞 E := fun i => ⟨⟨(D : Ω) * c i, hmem i⟩, by
      rw [mem_integralClosure_iff]
      exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ E Ω) E.val.injective).1 (hc i).2⟩
  have hf : ∀ i, algebraMap (𝓞 E) Ω (f i) = (D : Ω) * c i := fun i => rfl
  obtain ⟨s0, hs0⟩ : ∃ s0 : Finset ι, ∀ i, f i ∈ Submodule.span ℤ ((s0.image f : Finset (𝓞 E)) : Set (𝓞 E)) := by
    have hN : IsNoetherian ℤ (𝓞 E) := inferInstance
    obtain ⟨M, ⟨s0, rfl⟩, hmax⟩ := set_has_maximal_iff_noetherian.2 hN
      (Set.range fun s : Finset ι => Submodule.span ℤ ((s.image f : Finset (𝓞 E)) : Set (𝓞 E))) (Set.range_nonempty _)
    refine ⟨s0, fun i => ?_⟩
    have hle : Submodule.span ℤ ((s0.image f : Finset (𝓞 E)) : Set (𝓞 E)) ≤
        Submodule.span ℤ (((insert i s0).image f : Finset (𝓞 E)) : Set (𝓞 E)) :=
      Submodule.span_mono (by intro y hy; simp only [Finset.coe_image, Finset.coe_insert] at hy ⊢; exact Set.image_mono (Set.subset_insert _ _) hy)
    have heq := eq_of_le_of_not_lt hle (hmax _ ⟨insert i s0, rfl⟩)
    rw [heq]; exact Submodule.subset_span (by simp)
  set v := A.valuation
  have hDv : v (D : Ω) ≠ 0 := by
    rw [Valuation.ne_zero_iff]; exact Nat.cast_ne_zero.2 hD.ne'
  have hint : ∀ z : ℤ, v (z : Ω) ≤ 1 := fun z => (A.valuation_le_one_iff _).2 (intCast_mem A z)
  obtain ⟨i1, hi1⟩ := hne
  have ht : (s0.filter (fun i => c i ≠ 0)).Nonempty := by
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hcon
    have hz : ∀ y ∈ s0.image f, y = 0 := by
      intro y hy
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hy
      have := hcon hj; push_neg at this
      ext; simp [f, this]
    have h1 := hs0 i1
    rw [Submodule.mem_span_finset] at h1
    obtain ⟨g, -, hg⟩ := h1
    rw [Finset.sum_eq_zero (fun y hy => by rw [hz y hy, smul_zero])] at hg
    have := congrArg (algebraMap (𝓞 E) Ω) hg
    rw [hf, map_zero] at this
    exact hi1 ((mul_eq_zero.1 this.symm).resolve_left (Nat.cast_ne_zero.2 hD.ne'))
  obtain ⟨i0, hi0t, hmax⟩ := (s0.filter (fun i => c i ≠ 0)).exists_max_image (fun i => v (c i)) ht
  have hi0 : c i0 ≠ 0 := (Finset.mem_filter.1 hi0t).2
  have hmax' : ∀ j ∈ s0, v (c j) ≤ v (c i0) := by
    intro j hj
    by_cases hcj : c j = 0
    · rw [hcj, map_zero]; exact zero_le'
    · exact hmax j (Finset.mem_filter.2 ⟨hj, hcj⟩)
  refine ⟨i0, hi0, fun i => ?_⟩
  have h1 := hs0 i
  rw [Submodule.mem_span_finset] at h1
  obtain ⟨g, -, hg⟩ := h1
  have h2 := congrArg (algebraMap (𝓞 E) Ω) hg

  rw [hf, map_sum] at h2
  have hle : v ((D : Ω) * c i) ≤ v (D : Ω) * v (c i0) := by
    rw [← h2]
    refine Valuation.map_sum_le _ (fun y hy => ?_)
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hy
    rw [map_zsmul, hf, zsmul_eq_mul, map_mul, map_mul]
    calc v (g (f j) : Ω) * (v (D : Ω) * v (c j)) ≤ 1 * (v (D : Ω) * v (c j)) := by
          gcongr; exact hint _
      _ ≤ v (D : Ω) * v (c i0) := by rw [one_mul]; gcongr; exact hmax' j hj
  rw [map_mul] at hle
  have hle' : v (c i) ≤ v (c i0) := by
    calc v (c i) = (v (D : Ω))⁻¹ * (v (D : Ω) * v (c i)) := (inv_mul_cancel_left₀ hDv _).symm
      _ ≤ (v (D : Ω))⁻¹ * (v (D : Ω) * v (c i0)) := by gcongr
      _ = v (c i0) := inv_mul_cancel_left₀ hDv _
  have hv0 : v (c i0) ≠ 0 := (Valuation.ne_zero_iff _).2 hi0
  rw [← A.valuation_le_one_iff, map_mul, map_inv₀]
  calc v (c i) * (v (c i0))⁻¹ ≤ v (c i0) * (v (c i0))⁻¹ := by gcongr
    _ = 1 := mul_inv_cancel₀ hv0

theorem prim_of_bounded : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ a : X.K, a ≠ 0 → (∃ (S : Finset Ω) (D : ℕ), 0 < D ∧ ∀ r, (X.exp a).coeff r ∈ IntermediateField.adjoin ℚ (S : Set Ω) ∧ IsIntegral ℤ ((D : Ω) * (X.exp a).coeff r)) → ∃ κ : Ω, κ ≠ 0 ∧ Prim A (X.exp (algebraMap Ω X.K κ * a)) ∧ ∃ S : Finset Ω, ∀ r, (X.exp (algebraMap Ω X.K κ * a)).coeff r ∈ IntermediateField.adjoin ℚ (S : Set Ω) := by
  intro Ω _ _ _ ε X _ l _ A _ a ha hb
  obtain ⟨S, D, hD, hc⟩ := hb
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ (S : Set Ω)) :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  have hne : ∃ r, (X.exp a).coeff r ≠ 0 := by
    by_contra h
    push_neg at h
    have h0 : X.exp a = 0 := HahnSeries.ext (funext h)
    exact ha ((map_eq_zero_iff X.exp (RingHom.injective X.exp.toRingHom)).1 h0)
  obtain ⟨r0, h0, hA⟩ := exists_dividing A (fun r => (X.exp a).coeff r) _ D hD hc hne
  have hcoef : ∀ (κ : Ω) r, (X.exp (algebraMap Ω X.K κ * a)).coeff r = κ * (X.exp a).coeff r := by
    intro κ r
    rw [map_mul, AlgHom.commutes, HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, HahnSeries.ofPowerSeries_C, HahnSeries.C_mul_eq_smul,
      HahnSeries.coeff_smul, smul_eq_mul]
  refine ⟨((X.exp a).coeff r0)⁻¹, inv_ne_zero h0, ⟨fun r => ?_, r0, ?_⟩, S, fun r => ?_⟩
  · rw [hcoef, mul_comm]; exact hA r
  · rw [hcoef, inv_mul_cancel₀ h0, inv_one]
    exact ⟨one_ne_zero, one_mem A⟩
  · rw [hcoef]
    exact IntermediateField.mul_mem _ (IntermediateField.inv_mem _ (hc r0).1) (hc r).1

end GlobalTheory.PrimConst
end

section

open GlobalTheory.Col PowerSeries

noncomputable section

namespace GlobalTheory.Col.NormCoeff

variable {R : Type} [CommRing R]

def smapEquiv (σ : R ≃+* R) : PowerSeries R ≃+* PowerSeries R :=
  RingEquiv.ofRingHom (smap σ) (smap σ.symm)
    (by ext h n; simp [PowerSeries.coeff_map])
    (by ext h n; simp [PowerSeries.coeff_map])

theorem smapEquiv_apply (σ : R ≃+* R) (h : PowerSeries R) : smapEquiv σ h = smap σ h := rfl

theorem map_phi (p : ℕ) (hp : 0 < p) (f : R →+* R) (h : PowerSeries R) :
    PowerSeries.map f (phi (R := R) p hp h) = phi (R := R) p hp (PowerSeries.map f h) := by
  unfold phi
  rw [PowerSeries.coe_substAlgHom]
  have key := PowerSeries.map_subst (hasSubst_om (R := R) p hp) (h := f) h
  have e : (MvPowerSeries.map f) (((1 + PowerSeries.X : PowerSeries R) ^ p) - 1)
      = ((1 + PowerSeries.X : PowerSeries R) ^ p) - 1 := by
    change PowerSeries.map f _ = _
    simp
  rw [e] at key
  exact key

theorem normOp_smap (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime] (σ : R ≃+* R) (h : PowerSeries R) :
    normOp p (smap σ h) = smap σ (normOp p h) := by
  have key := @Algebra.norm_eq_of_equiv_equiv (PowerSeries R) (PowerSeries R) (PowerSeries R) (PowerSeries R)
    _ _ _ _ (phi (R := R) p hp.out.pos).toRingHom.toAlgebra (phi (R := R) p hp.out.pos).toRingHom.toAlgebra
    (smapEquiv σ) (smapEquiv σ) (by
      ext1 x
      exact (map_phi p hp.out.pos (σ : R →+* R) x).symm) h
  have key2 : normOp p h = (smapEquiv σ).symm (normOp p (smap σ h)) := key
  rw [key2, ← smapEquiv_apply, ← smapEquiv_apply, RingEquiv.apply_symm_apply]

end GlobalTheory.Col.NormCoeff
end
end

section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion

theorem _root_.GlobalTheory.T.heckeSumAtCuspHahn_coeff_of_integral_exponents : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (q : ℕ), 0 < q → ∀ φ : HahnSeries ℚ Ω,
  (∀ r : ℚ, φ.coeff r ≠ 0 → r.den = 1) → ∀ s : ℚ, (hq ε q φ).coeff s = if s.den = 1 then φ.coeff ((q : ℚ) * s) else 0 := by
  first | exact @GlobalTheory.HeckeInt.hq_coeff_of_int | exact GlobalTheory.HeckeInt.hq_coeff_of_int | (intros; apply GlobalTheory.HeckeInt.hq_coeff_of_int <;> assumption)
end

section

open GlobalTheory.K5 GlobalTheory.KumDlog

theorem _root_.GlobalTheory.T.towerGn_exponents_kummer_cochains : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], ∀ (T : Tower p Ω) (n m : ℕ), 2 * n ≤ m → ∀ lz lq : Gal p Ω → ZMod (p ^ n),
  IsKum T n (Gn T n) (T.ζ (2 * n)) lz → IsKum T n (Gn T n) (T.qq (2 * n)) lq → ∀ g ∈ Gn T n,
  ∃ (i j : ℕ) (s t : ℤ), g (T.ζ m) = T.ζ m ^ i ∧ g (T.qq m) = T.ζ m ^ j * T.qq m ∧
    (i : ℤ) = 1 + p ^ n * ((lz g).val : ℤ) + p ^ (2 * n) * s ∧ (j : ℤ) = p ^ n * ((lq g).val : ℤ) + p ^ (2 * n) * t := by
  first | exact @GlobalTheory.KumExpo.exponents | exact GlobalTheory.KumExpo.exponents | (intros; apply GlobalTheory.KumExpo.exponents <;> assumption)
end

section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

theorem _root_.GlobalTheory.T.laurentSeriesPadic_exists_pthPower_combination : ∀ (p : ℕ) [Fact p.Prime] (f : Lau p), ∃ (g : Fin p → Lau p) (h : Lau p), f = ∑ j : Fin p, HahnSeries.single ((j : ℕ) : ℤ) (1 : ℤ_[p]) * g j ^ p + (p : Lau p) * h := by
  first | exact @GlobalTheory.K5.LauZ.exists_pow_comb | exact GlobalTheory.K5.LauZ.exists_pow_comb | (intros; apply GlobalTheory.K5.LauZ.exists_pow_comb <;> assumption)
end

section

open GlobalTheory.K5

theorem _root_.GlobalTheory.T.completed_laurent_isDVR_statement : ∀ (p : ℕ) [Fact p.Prime], ∃ _ : IsDomain (O0 p), IsDiscreteValuationRing (O0 p) ∧ Irreducible (p : O0 p) := by
  first | exact @GlobalTheory.K5.completed_laurent_isDVR | exact GlobalTheory.K5.completed_laurent_isDVR | (intros; apply GlobalTheory.K5.completed_laurent_isDVR <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

theorem _root_.GlobalTheory.T.twistedJacquetKernel_twoBlock_unipotent_le_stages : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin (r + t)) k) V) (P : Submodule ℂ V), twKer π (unipRad k (two (stdSum (rfl : r + t = r + t)))) 1 ≤ P → (∀ u ∈ unipB k (Fin r), ∀ w, π (emb₂ k (stdSum (rfl : r + t = r + t)) (u, 1)) w - w ∈ P) → (∀ u ∈ unipB k (Fin t), ∀ w, π (emb₂ k (stdSum (rfl : r + t = r + t)) (1, u)) w - w ∈ P) → twKer π (unipB k (Fin (r + t))) 1 ≤ P := by
  first | exact @GlobalTheory.PsType.twKer_unipB_le_of_stages | exact GlobalTheory.PsType.twKer_unipB_le_of_stages | (intros; apply GlobalTheory.PsType.twKer_unipB_le_of_stages <;> assumption)
end
