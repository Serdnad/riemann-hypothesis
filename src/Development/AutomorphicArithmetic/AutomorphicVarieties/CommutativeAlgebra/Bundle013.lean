module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle012
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle066
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle047
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.TchPoly
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
import Mathlib.RingTheory.MvPowerSeries.Order
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private lemma lin_coeff_sq {O R K τ : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing K] [Algebra O K]
    (x : R →ₐ[O] O) (φ : R →ₐ[O] MvPowerSeries τ K)
    (hc : ∀ f, constantCoeff (φ f) = algebraMap O K (x f)) (i : τ) :
    ∀ g ∈ RingHom.ker x ^ 2, coeff (Finsupp.single i 1) (φ g) = 0 := by
  intro g hg
  rw [pow_two] at hg
  have hone : ∀ a ∈ RingHom.ker x, 1 ≤ (φ a).order := by
    intro a ha
    have hxa : x a = 0 := ha
    exact MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr (by rw [hc, hxa, map_zero])
  have hord : ((2 : ℕ) : ℕ∞) ≤ (φ g).order := by
    refine Submodule.mul_induction_on (C := fun g => ((2 : ℕ) : ℕ∞) ≤ (φ g).order) hg ?_ ?_
    · intro a ha b hb
      rw [map_mul]
      calc ((2 : ℕ) : ℕ∞) = 1 + 1 := by norm_num
        _ ≤ (φ a).order + (φ b).order := add_le_add (hone a ha) (hone b hb)
        _ ≤ (φ a * φ b).order := MvPowerSeries.le_order_mul
    · intro a b ha hb
      rw [map_add (f := _)]
      exact le_trans (le_min ha hb) MvPowerSeries.min_order_le_add
  apply MvPowerSeries.coeff_of_lt_order
  rw [Finsupp.degree_single]
  exact lt_of_lt_of_le (by norm_num) hord

theorem UpperTheory.V.Alg.chart_gr :
    ∀ (O X R : Type) [CommRing O] [IsDomain O] [AddCommGroup X] [DecidableEq X] [CommRing R] [Algebra O R] (W : WPres O X R) (h : W.HasOrigin) [Module.Free ℤ X] [Module.Finite ℤ X] (τ : Type) (wt : τ → X) (φ : R →ₐ[O] MvPowerSeries τ (FractionRing O)), IsChart W.part (W.origin h) wt φ → IsChart W.gr (W.originA h) wt (φ.comp W.A.val) := by
  intro O X R _ _ _ _ _ _ W h _ _ τ wt φ hφ
  obtain ⟨hk, hsurj⟩ := ker_pow O R X W h 2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j f hf
    exact hφ.graded j f.val hf
  · intro f
    exact hφ.const f.val
  · intro i
    obtain ⟨g, hg1, hg2⟩ := hφ.onto i
    obtain ⟨y, hy⟩ := hsurj g
    have hd : ∀ i', coeff (Finsupp.single i' 1) (φ (g - y)) = 0 :=
      fun i' => lin_coeff_sq (W.origin h) φ hφ.const i' _ hy
    have he : ∀ i', coeff (Finsupp.single i' 1) ((φ.comp W.A.val) y) =
        coeff (Finsupp.single i' 1) (φ g) := by
      intro i'
      have := hd i'
      rw [map_sub, map_sub, sub_eq_zero] at this
      exact this.symm
    refine ⟨y, ?_, ?_⟩
    · rw [he]
      exact hg1
    · intro i' hi'
      rw [he]
      exact hg2 i' hi'
  · intro f hf hco
    obtain ⟨c, hc0, hcf⟩ := hφ.inj f.val hf hco
    refine ⟨c, hc0, ?_⟩
    rw [← hk, Ideal.mem_comap]
    exact hcf
end

section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem mem_span_X {O σ : Type} [CommRing O] [Fintype σ] (f : MvPowerSeries σ O)
    (hf : constantCoeff f = 0) : f ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)) :=
  _root_.UpperTheory.Reformulated.B.MemSpanVariable.mem_span_X f hf

private theorem der_algebraMap {O A Q : Type} [CommRing O] [CommRing A] [Algebra O A] [AddCommGroup Q]
    [Module O Q] (x : A →ₐ[O] O) (D : A →ₗ[O] Q) (hD : D ∈ PtDer x Q) (c : O) : D (algebraMap O A c) = 0 := by
  have h1 : D 1 = 0 := by
    have h : D (1 * 1) = x 1 • D 1 + x 1 • D 1 := hD 1 1
    rw [mul_one, map_one x, one_smul] at h
    simpa using h
  rw [Algebra.algebraMap_eq_smul_one, map_smul, h1, smul_zero]

private theorem der_sq {O A Q : Type} [CommRing O] [CommRing A] [Algebra O A] [AddCommGroup Q]
    [Module O Q] (x : A →ₐ[O] O) (D : A →ₗ[O] Q) (hD : D ∈ PtDer x Q) (f : A) (hf : f ∈ RingHom.ker x ^ 2) :
    D f = 0 := by
  rw [pow_two] at hf
  refine Submodule.mul_induction_on hf (fun a ha b hb => ?_) (fun a b ha hb => by rw [map_add (f := _), ha, hb, add_zero])
  have h : D (a * b) = x a • D b + x b • D a := hD a b
  rw [h, (RingHom.mem_ker).1 ha, (RingHom.mem_ker).1 hb, zero_smul, zero_smul, add_zero]

theorem UpperTheory.V.Alg.der_extend :
    ∀ (O R : Type) [CommRing O] [CommRing R] [Algebra O R] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] (W : WPres O X R) (h : W.HasOrigin) (Q : Type) [AddCommGroup Q] [Module O Q],
      (∀ D ∈ PtDer (W.originA h) Q, ∃! D' : R →ₗ[O] Q, D' ∈ PtDer (W.origin h) Q ∧ D' ∘ₗ W.A.val.toLinearMap = D) ∧
      ∀ D ∈ PtDer (W.origin h) Q, (∀ s, D (W.z s) = 0) → D = 0 := by
  intro O R _ _ _ X _ _ _ _ W h Q _ _
  obtain ⟨hk, hy⟩ := UpperTheory.V.Alg.ker_pow O R X W h 2
  choose y hy using hy
  refine ⟨fun D hD => ?_, fun D hD hz => ?_⟩
  · have key : ∀ (x : R) (a : W.A), x - a ∈ RingHom.ker (W.origin h) ^ 2 → D (y x) = D a := fun x a ha => by
      rw [← sub_eq_zero, ← map_sub]
      refine der_sq _ D hD _ ?_
      rw [← hk, Ideal.mem_comap]
      have := sub_mem ha (hy x)
      convert this using 1
      simp
    have horig : ∀ x : R, W.origin h x = W.originA h (y x) := fun x => by
      have h1 : x - y x ∈ RingHom.ker (W.origin h) := Ideal.pow_le_self two_ne_zero (hy x)
      rw [RingHom.mem_ker, map_sub, sub_eq_zero] at h1
      exact h1
    let D' : R →ₗ[O] Q :=
      { toFun := fun x => D (y x)
        map_add' := fun a b => by
          rw [← map_add (f := _)]
          refine key _ _ ?_
          have := add_mem (hy a) (hy b)
          convert this using 1
          push_cast
          ring
        map_smul' := fun c a => by
          rw [RingHom.id_apply, ← map_smul]
          refine key _ _ ?_
          have := Submodule.smul_of_tower_mem _ c (hy a)
          convert this using 1
          rw [smul_sub]
          rfl }
    refine ⟨D', ⟨fun a b => ?_, ?_⟩, ?_⟩
    · have h1 : D (y a * y b) = W.originA h (y a) • D (y b) + W.originA h (y b) • D (y a) := hD _ _
      show D (y (a * b)) = W.origin h a • D (y b) + W.origin h b • D (y a)
      rw [horig a, horig b, ← h1]
      refine key _ _ ?_
      have := add_mem (Ideal.mul_mem_right b _ (hy a)) (Ideal.mul_mem_left _ (y a : R) (hy b))
      convert this using 1
      push_cast
      ring
    · ext a
      exact key _ a (by simp)
    · rintro E ⟨hE, rfl⟩
      ext x
      have := der_sq _ E hE _ (hy x)
      rw [map_sub, sub_eq_zero] at this
      exact this
  · ext x
    obtain ⟨f, rfl⟩ := W.surj x
    have hspan : ∀ g ∈ Ideal.span (Set.range (MvPowerSeries.X : W.σ → MvPowerSeries W.σ O)),
        D (W.π g) = 0 := fun g hg => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hg

      rw [map_sum, map_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      have h1 : D (W.π (c i) * W.z i) = W.origin h (W.π (c i)) • D (W.z i) + W.origin h (W.z i) • D (W.π (c i)) :=
        hD _ _
      have h2 : W.origin h (W.z i) = 0 := by
        rw [WPres.z, W.origin_π]
        simp
      rw [map_mul]
      rw [hz i, h2, smul_zero, zero_smul, add_zero] at h1
      exact h1
    have h1 := hspan (f - algebraMap O _ (constantCoeff f))
      (mem_span_X _ (by simp [MvPowerSeries.algebraMap_apply]))
    rw [map_sub, AlgHom.commutes, map_sub, der_algebraMap _ D hD, sub_zero] at h1
    exact h1
end

section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem hos_expand {O S σ : Type} [CommRing O] [CommRing S] [Algebra O S] [Finite σ]
    (N : ℕ) (D : Finset (σ →₀ ℕ)) (hD : ∀ d, d ∈ D ↔ d.degree < N)
    (g : MvPowerSeries σ O →ₐ[O] S) (J : Ideal S) (hg : ∀ s, g (MvPowerSeries.X s) ∈ J) (hJ : J ^ N = ⊥)
    (y : MvPowerSeries σ O) :
    g y = ∑ d ∈ D, algebraMap O S (coeff d y) * d.prod fun s k => g (MvPowerSeries.X s) ^ k := by
  classical
  have h1 := GlobalTheory.algHom_sub_aeval_truncTotal_mem g hg N y
  rw [hJ, Ideal.mem_bot, sub_eq_zero] at h1
  rw [h1]
  have ht : truncTotal N y = ∑ d ∈ D, MvPolynomial.monomial d (coeff d y) := by
    ext d
    rw [MvPolynomial.coeff_sum, coeff_truncTotal_eq_ite]
    simp only [MvPolynomial.coeff_monomial, Finset.sum_ite_eq', hD]

  rw [ht, map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [MvPolynomial.aeval_monomial]

private theorem hos_prod {S σ X : Type} [CommRing S] [AddCommGroup X] (wt : σ → X)
    (t : Multiplicative X →* Sˣ) (a : σ → S) (d : σ →₀ ℕ) :
    (d.prod fun s k => ((t (Multiplicative.ofAdd (wt s)) : S) * a s) ^ k) =
      t (Multiplicative.ofAdd (Finsupp.weight wt d)) * d.prod fun s k => a s ^ k := by
  classical
  unfold Finsupp.prod
  simp only [mul_pow, Finset.prod_mul_distrib]
  congr 1
  rw [Finsupp.weight_apply, Finsupp.sum, ofAdd_sum, map_prod, Units.coe_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [ofAdd_nsmul, map_pow, Units.val_pow_eq_pow_val]

private theorem hos_art {O : Type} [CommRing O] [IsLocalRing O] {X : Type} [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] {S : Type} [CommRing S] [Algebra O S] [IsCO O S] {σ : Type} [Finite σ] (wt : σ → X)
    (p : MvPowerSeries σ O →ₐ[O] S) (N : ℕ) (hJ : maximalIdeal S ^ N = ⊥)
    (hp : ∀ s, p (MvPowerSeries.X s) ∈ maximalIdeal S) (x : MvPowerSeries σ O)
    (H : ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (i : S →ₐ[O] R')
      (t : Multiplicative X →* R'ˣ), (∀ j, res O R' (t j) = 1) →
      ∀ f' : MvPowerSeries σ O →ₐ[O] R',
        (∀ s, f' (MvPowerSeries.X s) = t (Multiplicative.ofAdd (wt s)) * i (p (MvPowerSeries.X s))) → f' x = 0)
    (j : X) : p (wcomp O wt j x) = 0 := by
  classical
  obtain ⟨n, t, ht1, ht2⟩ := tchar O X
  haveI : IsCO O (MvPowerSeries (Fin n) S) := co_mvps O S (Fin n)
  let i : S →ₐ[O] MvPowerSeries (Fin n) S := IsScalarTower.toAlgHom O S (MvPowerSeries (Fin n) S)
  have hi : ∀ a, i a = MvPowerSeries.C a := fun a => rfl
  let t' : Multiplicative X →* (MvPowerSeries (Fin n) S)ˣ :=
    (Units.map (MvPowerSeries.map (algebraMap O S)).toMonoidHom).comp t
  have ht' : ∀ k, res O (MvPowerSeries (Fin n) S) (t' k) = 1 := by
    intro k
    rw [← sub_eq_zero, ← map_one (res O (MvPowerSeries (Fin n) S)), ← map_sub, res_eq_zero_iff,
      IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]
    have hc : constantCoeff ((t' k : MvPowerSeries (Fin n) S) - 1) = 0 := by
      show constantCoeff (MvPowerSeries.map (algebraMap O S) (t k : MvPowerSeries (Fin n) O) - 1) = 0
      rw [map_sub, MvPowerSeries.constantCoeff_map, ht1, map_one, map_one, sub_self]
    rw [hc]
    exact not_isUnit_zero
  have hJm : Ideal.map i (maximalIdeal S) ≤ maximalIdeal (MvPowerSeries (Fin n) S) := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap]
    show i a ∈ maximalIdeal _
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff, hi,
      MvPowerSeries.constantCoeff_C]
    exact (IsLocalRing.mem_maximalIdeal _).1 ha
  let e : σ → MvPowerSeries (Fin n) S := fun s =>
    (t' (Multiplicative.ofAdd (wt s)) : MvPowerSeries (Fin n) S) * i (p (MvPowerSeries.X s))
  have he : ∀ s, e s ∈ Ideal.map i (maximalIdeal S) := fun s =>
    Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (hp s))
  haveI : IsAdicComplete (maximalIdeal (MvPowerSeries (Fin n) S)) (MvPowerSeries (Fin n) S) :=
    IsCO.complete (O := O)
  let f' := GlobalTheory.mvEvalAdic O (maximalIdeal (MvPowerSeries (Fin n) S)) e (fun s => hJm (he s))
  have hf'X : ∀ s, f' (MvPowerSeries.X s) =
      t' (Multiplicative.ofAdd (wt s)) * i (p (MvPowerSeries.X s)) := fun s =>
    GlobalTheory.mvEvalAdic_X _ _ _ s
  have h0 : f' x = 0 := H _ i t' ht' f' hf'X
  have hJN : Ideal.map i (maximalIdeal S) ^ N = ⊥ := by
    rw [← Ideal.map_pow, hJ, Ideal.map_bot]
  have hf'J : ∀ s, f' (MvPowerSeries.X s) ∈ Ideal.map i (maximalIdeal S) := fun s => by
    rw [hf'X]
    exact he s
  let D : Finset (σ →₀ ℕ) := (Finsupp.finite_of_degree_lt N).toFinset
  have hD : ∀ d, d ∈ D ↔ d.degree < N := fun d => by simp [D]
  have E1 := hos_expand N D hD f' (Ideal.map i (maximalIdeal S)) hf'J hJN x
  let T : (σ →₀ ℕ) → S := fun d =>
    algebraMap O S (coeff d x) * d.prod fun s k => p (MvPowerSeries.X s) ^ k
  have hT : ∀ k, p (wcomp O wt k x) = ∑ d ∈ D, if Finsupp.weight wt d = k then T d else 0 := by
    intro k
    rw [hos_expand N D hD p (maximalIdeal S) hp hJ]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [coeff_wcomp]
    split_ifs <;> simp [T]
  have hE : f' x = ∑ d ∈ D,
      (t' (Multiplicative.ofAdd (Finsupp.weight wt d)) : MvPowerSeries (Fin n) S) * i (T d) := by
    rw [E1]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp only [hf'X]
    have hp' := hos_prod wt t' (fun s => i (p (MvPowerSeries.X s))) d
    beta_reduce at hp'
    rw [hp']
    simp only [T, map_mul, AlgHom.commutes, Finsupp.prod, map_prod, map_pow]
    ring
  let s : Finset X := D.image (Finsupp.weight wt)
  have hz : ∀ k ∈ s, p (wcomp O wt k x) = 0 := by
    refine ht2 S s (fun k => p (wcomp O wt k x)) ?_
    calc _ = ∑ k ∈ s, (t' (Multiplicative.ofAdd k) : MvPowerSeries (Fin n) S) *
          i (p (wcomp O wt k x)) := Finset.sum_congr rfl fun k _ => by rw [hi]; rfl
      _ = ∑ k ∈ s, ∑ d ∈ D, if Finsupp.weight wt d = k then
          (t' (Multiplicative.ofAdd k) : MvPowerSeries (Fin n) S) * i (T d) else 0 := by
          refine Finset.sum_congr rfl fun k _ => ?_

          rw [hT, map_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun d _ => ?_
          split_ifs <;> simp
      _ = ∑ d ∈ D, ∑ k ∈ s, if Finsupp.weight wt d = k then
          (t' (Multiplicative.ofAdd k) : MvPowerSeries (Fin n) S) * i (T d) else 0 :=
          Finset.sum_comm
      _ = f' x := by
          rw [hE]
          refine Finset.sum_congr rfl fun d hd => ?_
          rw [Finset.sum_ite_eq, if_pos (Finset.mem_image_of_mem _ hd)]
      _ = 0 := h0
  by_cases hj : j ∈ s
  · exact hz j hj
  · rw [hT]
    apply Finset.sum_eq_zero
    intro d hd
    rw [if_neg]
    intro h
    exact hj (h ▸ Finset.mem_image_of_mem _ hd)

theorem UpperTheory.V.Alg.homog_of_stable :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (σ : Type) [Finite σ] (wt : σ → X) (π : MvPowerSeries σ O →ₐ[O] R), (∀ s, π (MvPowerSeries.X s) ∈ maximalIdeal R) →
      (∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f : MvPowerSeries σ O →ₐ[O] R') (t : Multiplicative X →* R'ˣ), (∀ j, res O R' (t j) = 1) → (∀ x, π x = 0 → f x = 0) →
        ∀ f' : MvPowerSeries σ O →ₐ[O] R', (∀ s, f' (MvPowerSeries.X s) = t (Multiplicative.ofAdd (wt s)) * f (MvPowerSeries.X s)) → ∀ x, π x = 0 → f' x = 0) →
      IsHomog O wt (RingHom.ker π) := by
  intro O _ _ _ _ X _ _ _ R _ _ _ σ _ wt π hπ hstab
  intro x hx j
  have hx' : π x = 0 := hx
  show π (wcomp O wt j x) = 0
  haveI : IsAdicComplete (maximalIdeal R) R := IsCO.complete (O := O)
  apply GlobalTheory.eq_of_forall_sub_mem_ideal_pow (maximalIdeal R)
  intro N
  rw [sub_zero]
  refine Ideal.pow_le_pow_right (Nat.le_succ N) ?_
  obtain ⟨I, hI⟩ : ∃ I : Ideal R, I = maximalIdeal R ^ (N + 1) := ⟨_, rfl⟩
  rw [← hI]
  have hIm : I ≤ maximalIdeal R := hI ▸ Ideal.pow_le_self (Nat.succ_ne_zero N)
  have hItop : I ≠ ⊤ := fun h =>
    (maximalIdeal.isMaximal R).ne_top (top_le_iff.1 (h ▸ hIm))
  haveI : Nontrivial (R ⧸ I) := by
    refine ⟨⟨0, 1, fun h => hItop ((Ideal.eq_top_iff_one _).2 ?_)⟩⟩
    rw [← map_one (Ideal.Quotient.mk I)] at h
    exact Ideal.Quotient.eq_zero_iff_mem.1 h.symm
  let q : R →ₐ[O] R ⧸ I := Ideal.Quotient.mkₐ O I
  haveI : IsCO O (R ⧸ I) := co_quot O R (R ⧸ I) q (Ideal.Quotient.mkₐ_surjective O I)
  have hmap : ∀ r ∈ maximalIdeal R, q r ∈ maximalIdeal (R ⧸ I) := by
    intro r hr
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, hu⟩
    obtain ⟨v, hv⟩ := Ideal.Quotient.mk_surjective ((u⁻¹ : (R ⧸ I)ˣ) : R ⧸ I)
    have hrv : r * v - 1 ∈ I := by
      rw [← Ideal.Quotient.eq, map_mul, hv, map_one]
      show q r * _ = 1
      rw [← hu, Units.mul_inv]
    apply (maximalIdeal.isMaximal R).ne_top
    rw [Ideal.eq_top_iff_one]
    have h1 := Ideal.sub_mem _ (Ideal.mul_mem_right v _ hr) (hIm hrv)
    simpa using h1
  have hle : maximalIdeal (R ⧸ I) ≤ Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R) := by
    intro y hy
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    apply Ideal.mem_map_of_mem
    by_contra hr
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hr
    exact (IsLocalRing.mem_maximalIdeal _).1 hy (hr.map _)
  have hJ : maximalIdeal (R ⧸ I) ^ (N + 1) = ⊥ := by
    rw [eq_bot_iff]
    calc maximalIdeal (R ⧸ I) ^ (N + 1)
        ≤ Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R) ^ (N + 1) := Ideal.pow_right_mono hle _
      _ = Ideal.map (Ideal.Quotient.mk I) I := by rw [← Ideal.map_pow, hI]
      _ = ⊥ := Ideal.map_quotient_self I
      _ ≤ ⊥ := le_rfl
  have hp : ∀ s, (q.comp π) (MvPowerSeries.X s) ∈ maximalIdeal (R ⧸ I) := fun s =>
    hmap _ (hπ s)
  have key := hos_art wt (q.comp π) (N + 1) hJ hp x
    (fun R' _ _ _ i t ht f' hf' =>
      hstab R' ((i.comp q).comp π) t ht (fun y hy => by simp [hy]) f' (fun s => (hf' s).trans rfl) x hx') j
  rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at key
  exact key
end
