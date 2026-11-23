module

public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Order.Interval.Finset.Box
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Order.Interval.Finset.Defs

@[expose] public section

section

open TensorProduct

namespace GlobalTheory.DualFibreRank

section
variable {O : Type} [CommRing O] (A : Type) [CommRing A] [Algebra O A]

noncomputable def cmp (M : Type) [AddCommGroup M] [Module O M] :
    A ⊗[O] Module.Dual O M →ₗ[A] Module.Dual A (A ⊗[O] M) :=
  LinearMap.liftBaseChange A (Module.Dual.baseChange A)

variable {M N : Type} [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N]

theorem cmp_natural (f : M →ₗ[O] N) :
    cmp A M ∘ₗ f.dualMap.baseChange A = (f.baseChange A).dualMap ∘ₗ cmp A N := by
  ext g x
  simp [cmp]

theorem cmp_natural_apply (f : M →ₗ[O] N) (x : A ⊗[O] Module.Dual O N) :
    cmp A M (f.dualMap.baseChange A x) = (f.baseChange A).dualMap (cmp A N x) :=
  LinearMap.congr_fun (cmp_natural A f) x

theorem cmp_bijective_of_free [Module.Free O M] [Module.Finite O M] :
    Function.Bijective (cmp A M (O := O)) := by
  have h := (TensorProduct.isBaseChange O M A)
  have : cmp A M (O := O) = h.toDualBaseChange.toLinearMap := by
    ext g x
    have := h.toDualBaseChange_tmul 1 g x
    simp only [TensorProduct.mk_apply] at this
    simp [cmp, this, Algebra.algebraMap_eq_smul_one]
  rw [this]
  exact h.toDualBaseChange.bijective

theorem cmp_bijective [Module.Projective O M] [Module.Finite O M] :
    Function.Bijective (cmp A M (O := O)) := by
  obtain ⟨n, p, i, -, -, hpi⟩ := Module.Finite.exists_comp_eq_id_of_projective O M
  have hF := cmp_bijective_of_free A (O := O) (M := Fin n → O)
  have h1 : ∀ x, i.dualMap.baseChange A (p.dualMap.baseChange A x) = x := by
    intro x
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, LinearMap.dualMap_comp_dualMap, hpi]
    simp [LinearMap.dualMap_id]
  have h2 : ∀ y, (i.baseChange A).dualMap ((p.baseChange A).dualMap y) = y := by
    intro y
    rw [← LinearMap.comp_apply, LinearMap.dualMap_comp_dualMap, ← LinearMap.baseChange_comp, hpi]
    simp [LinearMap.dualMap_id]
  constructor
  · intro x y hxy
    rw [← h1 x, ← h1 y]
    congr 1
    apply hF.1
    rw [cmp_natural_apply, cmp_natural_apply, hxy]
  · intro y
    obtain ⟨z, hz⟩ := hF.2 ((p.baseChange A).dualMap y)
    exact ⟨i.dualMap.baseChange A z, by rw [cmp_natural_apply, hz, h2]⟩

end

theorem finrank_dual_and_range_dualMap_baseChange :
    ∀ (O M N κ : Type) [CommRing O] [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N]
      [Module.Finite O M] [Module.Projective O M] [Module.Finite O N] [Module.Projective O N]
      [Field κ] [Algebra O κ] (f : M →ₗ[O] N),
      Module.finrank κ (TensorProduct O κ (Module.Dual O M)) =
          Module.finrank κ (TensorProduct O κ M) ∧
        Module.finrank κ (LinearMap.range (f.dualMap.baseChange κ)) =
          Module.finrank κ (LinearMap.range (f.baseChange κ)) := by
  intro O M N κ _ _ _ _ _ _ _ _ _ _ _ f
  let eM := LinearEquiv.ofBijective (cmp κ M (O := O)) (cmp_bijective κ)
  refine ⟨by rw [eM.finrank_eq, Subspace.dual_finrank_eq], ?_⟩
  rw [← LinearMap.finrank_range_dualMap_eq_finrank_range (f.baseChange κ),
    ← LinearEquiv.finrank_map_eq eM]
  have : (LinearMap.range (f.dualMap.baseChange κ)).map (eM : _ →ₗ[κ] _) =
      LinearMap.range (f.baseChange κ).dualMap := by
    rw [← LinearMap.range_comp]
    change LinearMap.range (cmp κ M ∘ₗ f.dualMap.baseChange κ) = _
    rw [cmp_natural, LinearMap.range_comp_of_range_eq_top]
    exact LinearMap.range_eq_top.2 (cmp_bijective κ).2
  rw [this]

end GlobalTheory.DualFibreRank
end

section

namespace GlobalTheory

theorem semilinear_fixed_span (L : Type) [Field L] (s : L ≃+* L) (r : ℕ) (hr : 0 < r)
    (hsr : ∀ x, (⇑s)^[r] x = x) (hsi : ∀ i, 0 < i → i < r → ∃ x, (⇑s)^[i] x ≠ x)
    (V : Type) [AddCommGroup V] [Module L V] [FiniteDimensional L V] (F : V →+ V)
    (hF : ∀ (a : L) (v : V), F (a • v) = s a • F v) (hFr : ∀ v, (⇑F)^[r] v = v) :
    Submodule.span L {v | F v = v} = ⊤ := by
  by_contra hne
  obtain ⟨f, hf0, hfk⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf0 (LinearMap.ext h)

  have hFi : ∀ (i : ℕ) (a : L) (w : V), (⇑F)^[i] (a • w) = (⇑s)^[i] a • (⇑F)^[i] w := by
    intro i
    induction i with
    | zero => intro a w; simp
    | succ n ih =>
      intro a w
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply',
        ih, hF]

  have htr : ∀ w : V, F (∑ i ∈ Finset.range r, (⇑F)^[i] w) = ∑ i ∈ Finset.range r, (⇑F)^[i] w := by
    intro w

    rw [map_sum]
    have h1 := Finset.sum_range_succ' (fun i => (⇑F)^[i] w) r
    have h2 := Finset.sum_range_succ (fun i => (⇑F)^[i] w) r
    simp only [Function.iterate_succ_apply'] at h1
    rw [hFr w] at h2
    rw [show (⇑F)^[0] w = w from rfl] at h1
    exact add_right_cancel (h1.symm.trans h2)

  let χ : Fin r → (L →* L) := fun i => (((s : L →+* L) ^ (i : ℕ) : L →+* L) : L →* L)
  have hχ : ∀ (i : Fin r) (a : L), χ i a = (⇑s)^[i] a := by
    intro i a
    simp [χ, RingHom.coe_pow]
  have hinj : Function.Injective χ := by
    intro i j hij
    have key : ∀ (i j : Fin r), (i : ℕ) < j → χ i = χ j → False := by
      intro i j hlt he
      obtain ⟨x, hx⟩ := hsi ((j : ℕ) - i) (Nat.sub_pos_of_lt hlt) (by omega)
      apply hx
      have h3 := congrArg (fun g : L →* L => g x) he
      simp only [hχ] at h3
      have hj : (j : ℕ) = (i : ℕ) + ((j : ℕ) - i) := by omega
      rw [hj, Function.iterate_add_apply] at h3
      exact ((s.injective.iterate _) h3).symm
    rcases lt_trichotomy (i : ℕ) j with h | h | h
    · exact (key i j h hij).elim
    · exact Fin.ext h
    · exact (key j i h hij.symm).elim
  have hli := (linearIndependent_monoidHom L L).comp χ hinj
  have hsum : ∑ i : Fin r, f ((⇑F)^[i] v) • (((fun g : L →* L => (g : L → L)) ∘ χ) i) = 0 := by
    funext a
    have hfix : (∑ i ∈ Finset.range r, (⇑F)^[i] (a • v)) ∈ Submodule.span L {v | F v = v} :=
      Submodule.subset_span (htr (a • v))
    have h0 := hfk hfix

    rw [LinearMap.mem_ker, map_sum] at h0
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, hχ,
      Pi.zero_apply]
    rw [Fin.sum_univ_eq_sum_range (fun i => f ((⇑F)^[i] v) * (⇑s)^[i] a)]
    rw [← h0]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hFi, map_smul, smul_eq_mul, mul_comm]
  exact hv ((Fintype.linearIndependent_iff.1 hli) (fun i => f ((⇑F)^[(i : ℕ)] v)) hsum ⟨0, hr⟩)

end GlobalTheory
end

section

open scoped TensorProduct Classical

namespace GlobalTheory.PadicTensorApprox

variable {E : Type} [CommRing E] [Algebra ℚ E] {ℓ : ℕ} [Fact ℓ.Prime]

theorem isIntegral_tmul (u : ℚ_[ℓ]) (hu : ‖u‖ ≤ 1) (c : E) (hc : IsIntegral ℤ c) :
    IsIntegral ℤ_[ℓ] (u ⊗ₜ[ℚ] c : ℚ_[ℓ] ⊗[ℚ] E) := by
  have h1 : IsIntegral ℤ ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] c : ℚ_[ℓ] ⊗[ℚ] E) :=
    map_isIntegral_int (Algebra.TensorProduct.includeRight (R := ℚ) (A := ℚ_[ℓ]) (B := E)) hc
  have h2 : IsIntegral ℤ_[ℓ] ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] c : ℚ_[ℓ] ⊗[ℚ] E) := by
    obtain ⟨P, hP, hP'⟩ := h1
    refine ⟨P.map (Int.castRingHom _), hP.map _, ?_⟩
    rw [Polynomial.eval₂_map, ← hP']
    congr 1
  let v : ℤ_[ℓ] := ⟨u, hu⟩
  have h3 := h2.smul v
  have e : v • ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] c : ℚ_[ℓ] ⊗[ℚ] E) = u ⊗ₜ[ℚ] c := by
    rw [TensorProduct.smul_tmul']
    congr 1
    change u * 1 = u
    exact mul_one u
  rwa [e] at h3

theorem exists_tmul_integral [FiniteDimensional ℚ E] (a : ℚ_[ℓ]) (c : E) :
    ∃ (a' : ℚ_[ℓ]) (c' : E), IsIntegral ℤ c' ∧ (a ⊗ₜ[ℚ] c : ℚ_[ℓ] ⊗[ℚ] E) = a' ⊗ₜ[ℚ] c' := by
  have hq : IsAlgebraic ℚ c := Algebra.IsAlgebraic.isAlgebraic c
  have hz : IsAlgebraic ℤ c := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 hq
  obtain ⟨m, hm, hi⟩ := hz.exists_integral_multiple
  refine ⟨((m : ℚ)⁻¹) • a, m • c, hi, ?_⟩
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  rw [TensorProduct.smul_tmul, ← Int.cast_smul_eq_zsmul ℚ, smul_smul, inv_mul_cancel₀ hm', one_smul]

theorem pow_mul_tmul (N : ℕ) (a : ℚ_[ℓ]) (c : E) :
    (ℓ : ℚ_[ℓ] ⊗[ℚ] E) ^ N * (a ⊗ₜ[ℚ] c) = ((ℓ : ℚ_[ℓ]) ^ N * a) ⊗ₜ[ℚ] c := by
  have : (ℓ : ℚ_[ℓ] ⊗[ℚ] E) ^ N = ((ℓ : ℚ_[ℓ]) ^ N) ⊗ₜ[ℚ] (1 : E) := by
    rw [← Nat.cast_pow, ← Nat.cast_pow, Algebra.TensorProduct.natCast_def]
  rw [this, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem exists_pow_mul_isIntegral [FiniteDimensional ℚ E] (x : ℚ_[ℓ] ⊗[ℚ] E) :
    ∃ N : ℕ, IsIntegral ℤ_[ℓ] ((ℓ : ℚ_[ℓ] ⊗[ℚ] E) ^ N * x) := by
  have hl : IsIntegral ℤ_[ℓ] (ℓ : ℚ_[ℓ] ⊗[ℚ] E) := by
    have := isIntegral_algebraMap (R := ℤ_[ℓ]) (A := ℚ_[ℓ] ⊗[ℚ] E) (x := (ℓ : ℤ_[ℓ]))
    rwa [map_natCast] at this
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by rw [mul_zero]; exact isIntegral_zero⟩
  | add x y hx hy =>
    obtain ⟨M, hM⟩ := hx
    obtain ⟨N, hN⟩ := hy
    refine ⟨M + N, ?_⟩
    have := ((hl.pow N).mul hM).add ((hl.pow M).mul hN)
    have e : (ℓ : ℚ_[ℓ] ⊗[ℚ] E) ^ (M + N) * (x + y) = (ℓ : ℚ_[ℓ] ⊗[ℚ] E) ^ N * ((ℓ : ℚ_[ℓ] ⊗[ℚ] E) ^ M * x) +
        (ℓ : ℚ_[ℓ] ⊗[ℚ] E) ^ M * ((ℓ : ℚ_[ℓ] ⊗[ℚ] E) ^ N * y) := by ring
    rwa [e]
  | tmul a c =>
    obtain ⟨a', c', hc, e⟩ := exists_tmul_integral a c
    have hp : (1 : ℝ) < ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).one_lt
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt ‖a'‖ hp
    refine ⟨N, ?_⟩
    rw [e, pow_mul_tmul]
    refine isIntegral_tmul _ ?_ _ hc
    rw [norm_mul, norm_pow, Padic.norm_p, inv_pow, inv_mul_le_iff₀ (by positivity), mul_one]
    exact hN.le

theorem exists_sub_eq_pow_mul [FiniteDimensional ℚ E] (N : ℕ) (x : ℚ_[ℓ] ⊗[ℚ] E) :
    ∃ (b : E) (t : ℚ_[ℓ] ⊗[ℚ] E), IsIntegral ℤ_[ℓ] t ∧
      (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] b = x + (ℓ : ℚ_[ℓ] ⊗[ℚ] E) ^ N * t := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, isIntegral_zero, by simp⟩
  | add x y hx hy =>
    obtain ⟨b, t, ht, e⟩ := hx
    obtain ⟨b', t', ht', e'⟩ := hy
    refine ⟨b + b', t + t', ht.add ht', ?_⟩
    rw [TensorProduct.tmul_add, e, e']
    ring
  | tmul a c =>
    obtain ⟨a', c', hc, e⟩ := exists_tmul_integral a c
    have hp : (0 : ℝ) < ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).pos
    have hl : (ℓ : ℚ_[ℓ]) ≠ 0 := by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
    obtain ⟨q, hq⟩ := Padic.rat_dense ℓ a' (ε := ((ℓ : ℝ) ^ N)⁻¹) (by positivity)
    refine ⟨q • c', (((q : ℚ_[ℓ]) - a') / (ℓ : ℚ_[ℓ]) ^ N) ⊗ₜ[ℚ] c', isIntegral_tmul _ ?_ _ hc, ?_⟩
    · rw [norm_div, norm_pow, Padic.norm_p, inv_pow, div_le_one (by positivity), norm_sub_rev]
      exact hq.le
    · rw [e, pow_mul_tmul, ← TensorProduct.add_tmul, ← TensorProduct.smul_tmul]
      congr 1
      rw [Rat.smul_one_eq_cast]
      field_simp
      ring

theorem exists_approx_unit (E : Type) [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E]
    (ℓ : ℕ) [Fact ℓ.Prime] (z : (ℚ_[ℓ] ⊗[ℚ] E)ˣ) :
    ∃ (b : E) (s : ℚ_[ℓ] ⊗[ℚ] E), IsIntegral ℤ_[ℓ] s ∧
      (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] b = (z : ℚ_[ℓ] ⊗[ℚ] E) * (1 + (ℓ : ℚ_[ℓ] ⊗[ℚ] E) * s) := by
  obtain ⟨N, hN⟩ := exists_pow_mul_isIntegral ((z⁻¹ : (ℚ_[ℓ] ⊗[ℚ] E)ˣ) : ℚ_[ℓ] ⊗[ℚ] E)
  obtain ⟨b, t, ht, e⟩ := exists_sub_eq_pow_mul (N + 1) (z : ℚ_[ℓ] ⊗[ℚ] E)
  refine ⟨b, _, hN.mul ht, ?_⟩
  have h := z.mul_inv
  rw [e]
  linear_combination (-((ℓ : ℚ_[ℓ] ⊗[ℚ] E) ^ (N + 1) * t)) * h

end GlobalTheory.PadicTensorApprox
end

section

namespace GlobalTheory

theorem parallelogram_zsmul {E : Type} [AddCommGroup E] (Q : E → ℤ)
    (hQ : ∀ f g, Q (f + g) + Q (f - g) = 2 * Q f + 2 * Q g) (k : ℤ) (f : E) :
    Q (k • f) = k ^ 2 * Q f := by
  have h0 : Q 0 = 0 := by
    have := hQ 0 0
    simp only [add_zero, sub_zero] at this
    omega
  have hneg : ∀ g, Q (-g) = Q g := by
    intro g
    have := hQ 0 g
    simp only [zero_add, zero_sub, h0] at this
    omega
  have hnat : ∀ n : ℕ, Q ((n : ℤ) • f) = (n : ℤ) ^ 2 * Q f ∧
      Q (((n : ℤ) + 1) • f) = ((n : ℤ) + 1) ^ 2 * Q f := by
    intro n
    induction n with
    | zero => simp [h0]
    | succ n ih =>
      refine ⟨by push_cast; exact ih.2, ?_⟩
      have h := hQ (((n : ℤ) + 1) • f) f
      have e1 : ((n : ℤ) + 1) • f + f = (((n + 1 : ℕ) : ℤ) + 1) • f := by
        push_cast; module
      have e2 : ((n : ℤ) + 1) • f - f = (n : ℤ) • f := by module
      rw [e1, e2, ih.1, ih.2] at h
      push_cast at h ⊢
      linear_combination h
  obtain ⟨n, rfl | rfl⟩ := k.eq_nat_or_neg
  · exact (hnat n).1
  · rw [neg_smul, hneg, (hnat n).1]; ring

theorem parallelogram_sum_le {E ι : Type} [AddCommGroup E] (Q : E → ℤ)
    (hQ : ∀ f g, Q (f + g) + Q (f - g) = 2 * Q f + 2 * Q g) (hpos : ∀ f, 0 ≤ Q f)
    (u : ι → E) (s : Finset ι) :
    ∃ C : ℕ, ∀ (z : ι → ℤ) (M : ℤ), (∀ i, |z i| ≤ M) →
      Q (∑ i ∈ s, z i • u i) ≤ C * M ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨0, fun z M _ => ?_⟩
    have := parallelogram_zsmul Q hQ 0 0
    simp at this
    simp [this]
  | insert a s ha ih =>
    obtain ⟨C, hC⟩ := ih
    refine ⟨2 * (Q (u a)).toNat + 2 * C, fun z M hz => ?_⟩
    rw [Finset.sum_insert ha]
    have h1 := hQ (z a • u a) (∑ i ∈ s, z i • u i)
    have h2 := hpos (z a • u a - ∑ i ∈ s, z i • u i)
    have h3 := hC z M hz
    have h4 := parallelogram_zsmul Q hQ (z a) (u a)
    have h5 : z a ^ 2 ≤ M ^ 2 := by
      rw [← sq_abs (z a)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hz a) 2
    have h6 := mul_le_mul_of_nonneg_right h5 (hpos (u a))
    push_cast
    rw [Int.toNat_of_nonneg (hpos (u a))]
    nlinarith

theorem exists_dvd_coords_of_definite_form :
    ∀ (E : Type) [AddCommGroup E] (H : AddSubgroup E) (Q : E → ℤ), (∀ f g, Q (f + g) + Q (f - g) = 2 * Q f + 2 * Q g) → (∀ f, 0 ≤ Q f) → (∀ f ∈ H, Q f = 0 → f = 0) → ∀ (n : ℕ) (u : Fin n → E), (∀ i, u i ∈ H) → LinearIndependent ℤ u → ∃ e : ℕ, 0 < e ∧ ∀ (k : ℕ) (m : Fin n → ℤ) (h : E), h ∈ H → k • h = ∑ i, m i • u i → ∀ i, (k : ℤ) ∣ e * m i := by
  intro E _ H Q hQ hpos hdef n u hu hli
  obtain ⟨C, hC⟩ := parallelogram_sum_le Q hQ hpos u Finset.univ
  rw [Fintype.linearIndependent_iff] at hli
  set R : ℕ := C + 1 with hR
  refine ⟨(R ^ n).factorial, Nat.factorial_pos _, fun k m h hh hk => ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · intro i
    have := hli m (by simpa using hk.symm) i
    simp [this]
  have hk0 : (0 : ℤ) < k := by exact_mod_cast hkpos
  have hR0 : (0 : ℤ) < R := by positivity
  obtain ⟨a, ha, b, hb, hab, hf⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range (R ^ n + 1))
    (t := Fintype.piFinset (fun _ : Fin n => Finset.Ico (0 : ℤ) R))
    (f := fun (j : ℕ) (i : Fin n) => ((R : ℤ) * (((j : ℤ) * m i) % k)) / k)
    (by simp [Fintype.card_piFinset])
    (by
      intro j _
      simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Ico]
      intro i
      have h1 := Int.emod_nonneg ((j : ℤ) * m i) hk0.ne'
      have h2 := Int.emod_lt_of_pos ((j : ℤ) * m i) hk0
      refine ⟨Int.ediv_nonneg (by positivity) hk0.le, ?_⟩
      apply Int.ediv_lt_of_lt_mul hk0
      exact mul_lt_mul_of_pos_left h2 hR0)
  set y : Fin n → ℤ := fun i => ((a : ℤ) * m i) % k - ((b : ℤ) * m i) % k with hy
  set q : Fin n → ℤ := fun i => ((a : ℤ) * m i) / k - ((b : ℤ) * m i) / k with hq
  have hyq : ∀ i, y i = ((a : ℤ) - b) * m i - k * q i := by
    intro i
    simp only [hy, hq, Int.emod_def]
    ring
  have hbound : ∀ i, |(R : ℤ) * y i| ≤ k := by
    intro i
    have e := congrFun hf i
    beta_reduce at e
    have a1 := Int.emod_nonneg ((R : ℤ) * (((a : ℤ) * m i) % k)) hk0.ne'
    have a2 := Int.emod_lt_of_pos ((R : ℤ) * (((a : ℤ) * m i) % k)) hk0
    have b1 := Int.emod_nonneg ((R : ℤ) * (((b : ℤ) * m i) % k)) hk0.ne'
    have b2 := Int.emod_lt_of_pos ((R : ℤ) * (((b : ℤ) * m i) % k)) hk0
    rw [Int.emod_def] at a1 a2 b1 b2
    rw [e] at a1 a2
    simp only [hy]
    rw [abs_le, mul_sub]
    constructor <;> linarith
  set w : E := ((a : ℤ) - b) • h - ∑ i, q i • u i with hw
  have hwH : w ∈ H := H.sub_mem (H.zsmul_mem hh _) (H.sum_mem fun i _ => H.zsmul_mem (hu i) _)
  have hkw : (k : ℤ) • w = ∑ i, y i • u i := by
    rw [hw, smul_sub, smul_comm, natCast_zsmul h k, hk, Finset.smul_sum, Finset.smul_sum,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hyq i, smul_smul, smul_smul, sub_smul]
  have hRkw : ((R : ℤ) * k) • w = ∑ i, ((R : ℤ) * y i) • u i := by
    rw [mul_smul, hkw, Finset.smul_sum]
    simp only [smul_smul]
  have hle := hC (fun i => (R : ℤ) * y i) k hbound
  rw [← hRkw, parallelogram_zsmul Q hQ] at hle
  have hQw : Q w = 0 := by
    by_contra hne
    have h1 : 1 ≤ Q w := by have := hpos w; omega
    have h2 : ((R : ℤ) * k) ^ 2 ≤ ((R : ℤ) * k) ^ 2 * Q w := le_mul_of_one_le_right (by positivity) h1
    have h3 : (C : ℤ) < (R : ℤ) ^ 2 := by
      rw [hR]; push_cast; nlinarith [Int.natCast_nonneg C]
    have h4 := mul_lt_mul_of_pos_right h3 (show (0 : ℤ) < (k : ℤ) ^ 2 by positivity)
    rw [mul_pow] at h2 hle
    linarith
  have hw0 := hdef w hwH hQw
  rw [hw0, smul_zero] at hkw
  intro i
  have hyi := hli y hkw.symm i
  have hd : (k : ℤ) ∣ ((a : ℤ) - b) * m i := ⟨q i, by have := hyq i; linarith⟩
  refine hd.trans (mul_dvd_mul_right ?_ _)
  rw [← Int.natAbs_dvd, Int.natCast_dvd_natCast]
  rw [Finset.mem_range] at ha hb
  apply Nat.dvd_factorial
  · omega
  · omega

end GlobalTheory
end
