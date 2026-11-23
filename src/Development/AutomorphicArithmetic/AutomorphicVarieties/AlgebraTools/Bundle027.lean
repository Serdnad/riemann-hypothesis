module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle024
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle019
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle011
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.SwapOne
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle025
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle020
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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Ideal.GoingDown
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Vandermonde

@[expose] public section

section

open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

private theorem simple_one {R : Type} [CommRing R] {n : ℕ} {q : R} {H : Type} [Ring H] [Algebra R H]
    (b : Bern n q H) {a c : Fin n} (h : a.val + 1 = c.val) : b.T (swap a c) * b.one = q • b.one := by
  have hac : a ≠ c := fun e => by rw [e] at h; omega
  let s := swap a c
  let d (w : Perm (Fin n)) := b.T s * b.T w - q • b.T w
  have hpair (w : Perm (Fin n)) (hw : w⁻¹ a < w⁻¹ c) : d w + d (s * w) = 0 := by
    dsimp [d, s]
    rw [b.T_mul a c h w hw, ← mul_assoc, b.T_sq a c h, add_mul, smul_mul_assoc,
      smul_mul_assoc, one_mul]
    module
  have hcancel (w : Perm (Fin n)) : d w + d (s * w) = 0 := by
    rcases lt_or_gt_of_ne (show w⁻¹ a ≠ w⁻¹ c from fun e => hac (w⁻¹.injective e)) with hw | hw
    · exact hpair w hw
    · have hw' : (s * w)⁻¹ a < (s * w)⁻¹ c := by
        simpa [s, Perm.mul_apply, mul_inv_rev, swap_inv, swap_apply_left, swap_apply_right] using hw
      have e := hpair (s * w) hw'
      rw [show s * (s * w) = w by simp [s, swap_mul_self_mul], add_comm] at e
      exact e
  have hsum : ∑ w, d w = 0 := by
    refine Finset.sum_ninvolution (fun w => s * w) hcancel ?_ (fun _ => Finset.mem_univ _) ?_
    · intro w _ e
      apply hac
      have he := congrArg (fun x : Perm (Fin n) => (x * w⁻¹) a) e
      simpa [s, mul_assoc] using he.symm
    · intro w
      simp [s, swap_mul_self_mul]
  unfold Bern.one
  rw [Finset.mul_sum, Finset.smul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib]
  exact hsum

private theorem symm_of_eigen {R : Type} [CommRing R] [IsDomain R] {n : ℕ} {q : R} {H : Type} [Ring H]
    [Algebra R H] (b : Bern n q H) (hb : b.Faithful) (y : MvPolynomial (Fin n) R)
    (hy : ∀ a c : Fin n, a.val + 1 = c.val → b.T (swap a c) * (b.th y * b.one) = q • (b.th y * b.one))
    (w : Perm (Fin n)) : rename w y = y := by
  have hs : ∀ a c : Fin n, a.val + 1 = c.val → rename (swap a c) y = y := by
    intro a c h
    have hac : a ≠ c := fun e => by rw [e] at h; omega
    obtain ⟨z, hz, e⟩ := (UpperTheory.V.AlgebraTools.hkBern R n q H b).1 a c h y
    have e1 := hy a c h
    rw [← mul_assoc, e, add_mul, mul_assoc, simple_one b h, mul_smul_comm, smul_mul_assoc] at e1
    have e2 : q • rename (swap a c) y + (q - 1) • (X a * z) - q • y = 0 := by
      apply hb
      rw [map_sub, map_add (f := _), map_smul, map_smul, map_smul, sub_mul, add_mul, smul_mul_assoc, smul_mul_assoc,
        smul_mul_assoc, e1, sub_self]
    have e3 : (C q * X c - X a) * z = 0 := by
      simp only [smul_eq_C_mul, map_sub, map_one] at e2
      linear_combination e2 - C q * hz
    rcases mul_eq_zero.1 e3 with h0 | h0
    · have := congrArg (eval fun k => if k = a then (1 : R) else 0) h0
      simp [hac.symm] at this
    · rw [h0, mul_zero] at hz
      exact (sub_eq_zero.1 hz.symm).symm
  refine UpperTheory.V.AlgebraTools.hkInd n (fun w => rename w y = y) ?_ ?_ w
  · simp
  · intro a c h w _ ih
    rw [Perm.coe_mul, ← rename_rename, ih, hs a c h]

private theorem rename_rev_NN {R : Type} [CommRing R] (n : ℕ) (q : R) :
    rename (Fin.revPerm : Perm (Fin n)) (NN n q) = ∏ p ∈ pairs n, (X p.1 - C q * X p.2) := by
  rw [NN, map_prod]
  refine Finset.prod_nbij' (fun p => (p.2.rev, p.1.rev)) (fun p => (p.2.rev, p.1.rev)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simpa [pairs] using hp
  · intro p hp
    simpa [pairs] using hp
  · intro p _
    simp
  · intro p _
    simp
  · intro p _
    simp

private theorem rename_rev_De (R : Type) [CommRing R] (n : ℕ) :
    rename (Fin.revPerm : Perm (Fin n)) (De R n) = ∏ p ∈ pairs n, (X p.1 - X p.2) := by
  simpa [NN, De] using rename_rev_NN n (1 : R)

private theorem coeff_eq {R : Type} [CommRing R] [IsDomain R] {n : ℕ} {K : Type} [Field K]
    [Algebra (MvPolynomial (Fin n) R) K] [IsFractionRing (MvPolynomial (Fin n) R) K] (F : Perm (Fin n) → K)
    (hF : ∀ x : MvPolynomial (Fin n) R, ∃ y : MvPolynomial (Fin n) R, (∀ w : Perm (Fin n), rename w y = y) ∧
      algebraMap _ K y = ∑ u, F u * algebraMap _ K (rename u x))
    (N D : MvPolynomial (Fin n) R) (r : Perm (Fin n))
    (hr : F r = algebraMap _ K (rename r N) / algebraMap _ K (rename r D)) (v : Perm (Fin n)) :
    F v = algebraMap _ K (rename v N) / algebraMap _ K (rename v D) := by
  obtain ⟨σ, rfl⟩ : ∃ σ, v = σ * r := ⟨v * r⁻¹, by simp⟩
  let φ : K ≃+* K := IsFractionRing.ringEquivOfRingEquiv (renameEquiv R σ).toRingEquiv
  have hφ : ∀ x : MvPolynomial (Fin n) R, φ (algebraMap _ K x) = algebraMap _ K (rename σ x) := fun x =>
    IsFractionRing.ringEquivOfRingEquiv_algebraMap _ x
  have h0 := UpperTheory.V.AlgebraTools.hkDedekind R n K (fun u => F u - φ (F (σ⁻¹ * u))) (by
    intro x
    obtain ⟨y, hy, e⟩ := hF x
    have e' := congrArg φ e

    rw [hφ, hy, e, map_sum] at e'
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [e', sub_eq_zero]
    refine Fintype.sum_equiv (Equiv.mulLeft σ) _ _ fun u => ?_
    rw [map_mul, hφ, rename_rename, Equiv.coe_mulLeft, inv_mul_cancel_left, Perm.coe_mul])
  have h1 := congrFun h0 (σ * r)
  simp only [Pi.zero_apply, inv_mul_cancel_left, sub_eq_zero] at h1
  rw [h1, hr, map_div₀, hφ, hφ, rename_rename, rename_rename, Perm.coe_mul]

theorem UpperTheory.V.AlgebraTools.hkSandwich :
    ∀ (R : Type) [CommRing R] [IsDomain R] (n : ℕ) (q : R) (H : Type) [Ring H] [Algebra R H] (b : Bern n q H), b.Faithful → ∀ x : MvPolynomial (Fin n) R, b.one * b.th x * b.one = b.th (dd (NN n q * x)) * b.one := by
  intro R _ _ n q H _ _ b hb x
  let K := FractionRing (MvPolynomial (Fin n) R)
  choose f hf hfw hf0 using UpperTheory.V.AlgebraTools.hkAct R n q H b K
  obtain ⟨-, -, -, hrev, hlt⟩ := UpperTheory.V.AlgebraTools.hkInv n
  let V := Matrix.vandermonde fun i : Fin n => (X i : MvPolynomial (Fin n) R)
  have hdet : De R n = V.det := by
    dsimp only [V]
    rw [Matrix.det_vandermonde, De, pairs, Finset.prod_filter, Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Finset.prod_filter]
    refine Finset.prod_congr ?_ fun _ _ => rfl
    ext j
    simp
  have hD : De R n ≠ 0 := by
    rw [hdet]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr X_injective
  have hsg (w : Perm (Fin n)) : rename w (De R n) = Perm.sign w • De R n := by
    rw [hdet, AlgHom.map_det]
    have hV : (rename w : MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R).mapMatrix V =
        V.submatrix w id := by
      ext i j
      simp [V, Matrix.vandermonde_apply]
    rw [hV, Matrix.det_permute, Units.smul_def, zsmul_eq_mul]
  have hsum : ∀ x : MvPolynomial (Fin n) R, ∃ y : MvPolynomial (Fin n) R,
      b.one * b.th x * b.one = b.th y * b.one ∧
      algebraMap _ K y = ∑ u, (∑ w, f w u) * algebraMap _ K (rename u x) := by
    intro x
    choose y hy hy' using fun w => hf w x
    refine ⟨∑ w, y w, ?_, ?_⟩

    · rw [map_sum, Finset.sum_mul, ← Finset.sum_congr rfl fun w _ => hy w, ← Finset.sum_mul, ← Finset.sum_mul]
      rfl

    · simp only [map_sum, hy', Finset.sum_mul]
      exact Finset.sum_comm
  have hF := coeff_eq (K := K) (fun u => ∑ w, f w u) (by
    intro x
    obtain ⟨y, hy, e⟩ := hsum x
    refine ⟨y, symm_of_eigen b hb y fun a c h => ?_, e⟩
    rw [← hy, ← mul_assoc, ← mul_assoc, simple_one b h, smul_mul_assoc, smul_mul_assoc])
    (NN n q) (De R n) Fin.revPerm (by
    rw [Finset.sum_eq_single Fin.revPerm (fun w _ hw => hf0 w _ hw.symm (hlt w hw).le) (by simp), hfw, hrev,
      rename_rev_NN, rename_rev_De, map_prod, map_prod, Finset.prod_div_distrib])
  obtain ⟨y, hy, e⟩ := hsum x
  have hinj := IsFractionRing.injective (MvPolynomial (Fin n) R) K
  have hD' : algebraMap _ K (De R n) ≠ 0 := fun h => hD (hinj (by rw [h, map_zero]))
  have : y = dd (NN n q * x) := by
    apply mul_left_cancel₀ hD
    apply hinj

    rw [UpperTheory.V.AlgebraTools.hkDdSpec, map_mul, e, alt, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    have hu := hF u
    rw [hu, hsg, map_mul]
    rcases Int.units_eq_one_or (Perm.sign u) with h | h
    · rw [h, one_smul, one_smul, map_mul, ← mul_assoc, mul_div_cancel₀ _ hD']
    · rw [h, Units.neg_smul, Units.neg_smul, one_smul, one_smul, map_neg, map_neg, map_mul, div_neg, neg_mul,
        mul_neg, ← mul_assoc, mul_div_cancel₀ _ hD']
  rw [hy, this]
end

section

open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

private theorem X_sub_ne {R : Type} [CommRing R] [IsDomain R] {n : ℕ} (q : R) {i j : Fin n} (h : i ≠ j) :
    (X i - C q * X j : MvPolynomial (Fin n) R) ≠ 0 := by
  intro h0
  have := congrArg (AddMonoidAlgebra.coeff · (Finsupp.single i 1)) h0
  simp [MvPolynomial.coeff_X', MvPolynomial.coeff_C_mul, Finsupp.single_left_inj, h, Ne.symm h] at this

theorem UpperTheory.V.AlgebraTools.hkFaith :
    ∀ (R : Type) [CommRing R] [IsDomain R] (n : ℕ) (q : R) (H : Type) [Ring H] [Algebra R H] (b : Bern n q H), b.Faithful → ∀ c : Perm (Fin n) → MvPolynomial (Fin n) R,
      (∀ x : MvPolynomial (Fin n) R, (∑ u, b.th (c u) * b.T u) * b.th x * b.one = 0) → c = 0 := by
  classical
  intro R _ _ n q H _ _ b hfaith c hc
  let K := FractionRing (MvPolynomial (Fin n) R)
  have hinj := IsFractionRing.injective (MvPolynomial (Fin n) R) K
  choose F hF1 hF2 hF3 using fun u => UpperTheory.V.AlgebraTools.hkAct R n q H b K u
  choose Y hY1 hY2 using hF1
  have key : ∀ x : MvPolynomial (Fin n) R,
      ∑ v, (∑ u, algebraMap (MvPolynomial (Fin n) R) K (c u) * F u v) *
        algebraMap (MvPolynomial (Fin n) R) K (rename v x) = 0 := by
    intro x
    have h1 : b.th (∑ u, c u * Y u x) * b.one = 0 := by
      calc b.th (∑ u, c u * Y u x) * b.one
          = ∑ u, b.th (c u) * (b.th (Y u x) * b.one) := by

            rw [map_sum, Finset.sum_mul]; simp [map_mul, mul_assoc]
        _ = ∑ u, b.th (c u) * (b.T u * b.th x * b.one) := by simp [hY1]
        _ = (∑ u, b.th (c u) * b.T u) * b.th x * b.one := by
            rw [Finset.sum_mul, Finset.sum_mul]; simp [mul_assoc]
        _ = 0 := hc x
    have h2 := congrArg (algebraMap (MvPolynomial (Fin n) R) K) (hfaith _ h1)

    rw [map_sum, map_zero] at h2
    simp_rw [map_mul, hY2, Finset.mul_sum] at h2
    rw [Finset.sum_comm] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun u _ => ?_
    ring
  have hD := UpperTheory.V.AlgebraTools.hkDedekind R n K _ key
  by_contra hne
  obtain ⟨w0, hw0⟩ : ∃ w, c w ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hne (funext hall)
  obtain ⟨w, hwS, hmax⟩ := (Finset.univ.filter (fun u => c u ≠ 0)).exists_max_image invN
    ⟨w0, by simp [hw0]⟩
  have hcw : c w ≠ 0 := by simpa using hwS
  have hw := congrFun hD w
  simp only [Pi.zero_apply] at hw
  rw [Finset.sum_eq_single w] at hw
  · apply mul_ne_zero _ _ hw
    · exact fun h => hcw (hinj (by rw [h, map_zero]))
    · rw [hF2 w]
      refine Finset.prod_ne_zero_iff.mpr fun p hp => ?_
      have hlt : p.1 < p.2 := by
        simp [invSet, pairs] at hp
        exact hp.1
      have hpne : p.1 ≠ p.2 := ne_of_lt hlt
      refine div_ne_zero ?_ ?_
      · exact fun h => X_sub_ne q hpne (hinj (by rw [h, map_zero]))
      · intro h
        apply X_sub_ne (1 : R) hpne
        apply hinj
        simpa using h
  · intro u _ hu
    by_cases hcu : c u = 0
    · simp [hcu]
    · rw [hF3 u w (fun h => hu h.symm) (hmax u (by simp [hcu])), mul_zero]
  · simp
end

section

open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.IsCplAt.exists_prime_over :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (p : Ideal R) (B : Type) [CommRing B] [IsLocalRing B] [Algebra R B], IsCplAt R p B →
      (∀ q : Ideal R, q.IsPrime → q ≤ p → ∃ Q : Ideal B, Q.IsPrime ∧ Q.comap (algebraMap R B) = q) ∧
      (∀ a : R, algebraMap R B a = 0 → ∃ s : R, s ∉ p ∧ s * a = 0) := by
  intro R _ _ p B _ _ _ h
  haveI := h.isPrime
  haveI := IsCplAt.flat R p B h
  refine ⟨fun q hq hqp => ?_, fun a ha => ?_⟩
  · haveI := hq
    haveI : (maximalIdeal B).LiesOver p := ⟨h.comap_eq.symm⟩
    obtain ⟨P, -, hP, hlo⟩ := Ideal.exists_ideal_le_liesOver_of_le (maximalIdeal B) hqp
    exact ⟨P, hP, hlo.over.symm⟩
  · let Rp := Localization.AtPrime p
    haveI : IsNoetherianRing Rp := IsLocalization.isNoetherianRing p.primeCompl Rp inferInstance
    have hmem : ∀ n : ℕ, algebraMap R Rp a ∈ (maximalIdeal Rp) ^ n := by
      intro n
      obtain ⟨s, hs, hsa⟩ := h.strict n a (by rw [ha]; exact zero_mem _)
      have hu : IsUnit (algebraMap R Rp s) := IsLocalization.map_units Rp (⟨s, hs⟩ : p.primeCompl)
      rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]
      have := Ideal.mem_map_of_mem (algebraMap R Rp) hsa
      rw [map_mul] at this
      exact (Ideal.unit_mul_mem_iff_mem _ hu).mp this
    have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal Rp) (IsLocalRing.maximalIdeal.isMaximal Rp).ne_top
    have h0 : algebraMap R Rp a = 0 := by
      have : algebraMap R Rp a ∈ ⨅ i, (maximalIdeal Rp) ^ i := Ideal.mem_iInf.mpr hmem
      rw [hbot] at this
      exact (Ideal.mem_bot).mp this
    obtain ⟨⟨s, hs⟩, hsa⟩ := (IsLocalization.map_eq_zero_iff p.primeCompl Rp a).mp h0
    exact ⟨s, hs, hsa⟩
end

section

open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.genKer_isPrime :
    ∀ (P : Type) [CommRing P] [IsRegularLocalRing P] (ι : Type) [Fintype ι] [DecidableEq ι] (z : Matrix ι ι P) (m : ι → P),
      CotInd P (Sum.elim (fun ij : ι × ι => z ij.1 ij.2) m) →
      ∀ c : ι, (genKer z m c).IsPrime ∧ detIdeal z m ≤ genKer z m c := by
  intro P _ _ ι _ _ z m hind c
  haveI hQ : (Ideal.map (MvPolynomial.C : P →+* MvPolynomial ι P) (maximalIdeal P)).IsPrime :=
    isPrime_map_C _
  haveI hJ := chartIdeal_localization_isPrime P ι z m hind c
    (Ideal.map (MvPolynomial.C : P →+* MvPolynomial ι P) (maximalIdeal P)) le_rfl
  have key : genKer z m c = Ideal.comap
      ((algebraMap (MvPolynomial ι P) (Localization.AtPrime
        (Ideal.map (MvPolynomial.C : P →+* MvPolynomial ι P) (maximalIdeal P)))).comp MvPolynomial.C)
      (Ideal.map (algebraMap (MvPolynomial ι P) (Localization.AtPrime
        (Ideal.map (MvPolynomial.C : P →+* MvPolynomial ι P) (maximalIdeal P)))) (chartIdeal z m c)) := by
    ext f
    rw [Ideal.mem_comap, RingHom.comp_apply,
      IsLocalization.algebraMap_mem_map_algebraMap_iff
        (Ideal.map (MvPolynomial.C : P →+* MvPolynomial ι P) (maximalIdeal P)).primeCompl]
    exact Iff.rfl
  have sub : ∀ f : P, MvPolynomial.C f ∈ chartIdeal z m c → f ∈ genKer z m c := by
    intro f hf
    rw [key, Ideal.mem_comap, RingHom.comp_apply]
    exact Ideal.mem_map_of_mem _ hf
  have gen : ∀ k, chartGen z m c k ∈ chartIdeal z m c := by
    intro k
    unfold chartIdeal
    exact Ideal.subset_span ⟨k, rfl⟩
  have hinl : ∀ i, ((z.map MvPolynomial.C).mulVec (lam P c)) i ∈ chartIdeal z m c :=
    fun i => gen (Sum.inl i)
  have hinr : ∀ j (h : j ≠ c),
      MvPolynomial.C (m j) - lam P c j * MvPolynomial.C (m c) ∈ chartIdeal z m c :=
    fun j h => gen (Sum.inr ⟨j, h⟩)
  have hdet : MvPolynomial.C z.det ∈ chartIdeal z m c := by
    have e : ((z.map MvPolynomial.C).adjugate.mulVec
        ((z.map MvPolynomial.C).mulVec (lam P c))) c = MvPolynomial.C z.det := by
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec,
        RingHom.map_det]
      simp [lam]
    rw [← e]
    show (∑ i, (z.map MvPolynomial.C).adjugate c i *
      ((z.map MvPolynomial.C).mulVec (lam P c)) i) ∈ _
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hinl i)
  refine ⟨by rw [key]; infer_instance, ?_⟩
  unfold detIdeal relIdeal
  refine sup_le (Ideal.span_le.2 ?_) (Ideal.span_le.2 (Set.singleton_subset_iff.2 (sub _ hdet)))
  rintro _ ⟨i, rfl⟩
  apply sub
  have e : MvPolynomial.C ((z.mulVec m) i) =
      ((z.map MvPolynomial.C).mulVec (lam P c)) i * MvPolynomial.C (m c) +
        ∑ j, MvPolynomial.C (z i j) * (MvPolynomial.C (m j) - lam P c j * MvPolynomial.C (m c)) := by

    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, Finset.sum_mul,
    mul_sub, Finset.sum_sub_distrib, mul_assoc]
    ring
  rw [e]
  refine add_mem (Ideal.mul_mem_right _ _ (hinl i)) (Ideal.sum_mem _ fun j _ => ?_)
  by_cases h : j = c
  · simp [h, lam]
  · exact Ideal.mul_mem_left _ _ (hinr j h)
end

section

open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.regular_localization_of_regular_quotient :
    ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] (p : Ideal R) [p.IsPrime] [IsRegularLocalRing (R ⧸ p)],
      IsRegularLocalRing (Localization.AtPrime p) ∧
      ringKrullDim (Localization.AtPrime p) + ringKrullDim (R ⧸ p) = ringKrullDim R := by
  intro R _ _ p _ _
  obtain ⟨r, x, hx, hsp⟩ := exists_cotInd_of_regular_quotient R p
  obtain ⟨-, hdim, -⟩ := regular_quotient_cotInd R _ x hx
  obtain ⟨hh, hreg⟩ := regular_localization_cotInd R _ x hx p hsp.symm
  refine ⟨hreg, ?_⟩
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p), hh, add_comm]
  rw [hsp] at hdim
  rw [← hdim]
  rfl
end
