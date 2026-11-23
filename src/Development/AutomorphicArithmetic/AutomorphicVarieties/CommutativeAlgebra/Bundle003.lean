module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle066
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
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.MvPowerSeries.Evaluation
public import Mathlib.RingTheory.MvPowerSeries.Inverse
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.Filtration

@[expose] public section

section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

open Classical in
private theorem wcomp_of_mem_ite {O : Type} [CommRing O] {σ X : Type} [AddCommGroup X] (wt : σ → X) {i j : X}
    {f : MvPowerSeries σ O} (hf : f ∈ wtPart O wt i) : wcomp O wt j f = if i = j then f else 0 := by
  ext n
  rw [coeff_wcomp]
  by_cases h : i = j
  · subst h
    rw [if_pos rfl]
    split_ifs with hn
    · rfl
    · exact (hf n hn).symm
  · rw [if_neg h, map_zero]
    split_ifs with hn
    · exact hf n (fun hi => h (hi.symm.trans hn))
    · rfl

theorem UpperTheory.V.Alg.ker_coef :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (X : Type) [AddCommGroup X] (A : Type) [CommRing A] [Algebra O A] [IsCO O A] (K : Ideal A), maximalIdeal A * K = ⊥ → ∀ (W : WPres O X A) (κ : Type) [Fintype κ] (ε : κ → A) (wf : κ → X), (∀ u, ε u ∈ W.part (wf u)) → K = Ideal.span (Set.range ε) → (∀ c : κ → O, ∑ u, c u • ε u = 0 → ∀ u, c u ∈ maximalIdeal O) →
          ∃ co : κ → A → ResidueField O, (∀ u, ∀ x ∈ K, ∀ y ∈ K, co u (x + y) = co u x + co u y) ∧ (∀ u (a : A), ∀ x ∈ K, co u (a * x) = res O A a * co u x) ∧
            (∀ u j, j ≠ wf u → ∀ x ∈ K, x ∈ W.part j → co u x = 0) ∧ ∀ x ∈ K, ∃ a : κ → O, (∀ u, residue O (a u) = co u x) ∧ x = ∑ u, a u • ε u := by
  intro O _ _ X _ A _ _ _ K hK W κ _ ε wf hε hspan hrel
  classical
  have hεK : ∀ v, ε v ∈ K := fun v => by
    rw [hspan]
    exact Ideal.subset_span ⟨v, rfl⟩
  have hkill : ∀ (r : A) (y : A), r ∈ maximalIdeal A → y ∈ K → r * y = 0 := by
    intro r y hr hy
    have h1 := Ideal.mul_mem_mul hr hy
    rw [hK] at h1
    exact (Ideal.mem_bot).1 h1
  have hrep : ∀ x ∈ K, ∃ a : κ → O, x = ∑ v, a v • ε v := by
    intro x hx
    rw [hspan] at hx
    obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 hx
    choose a ha using fun v => IsCO.res_surj (O := O) (r v)
    refine ⟨a, ?_⟩
    rw [← hr]
    apply Finset.sum_congr rfl
    intro v _
    have h0 := hkill _ _ (ha v) (hεK v)
    rw [smul_eq_mul, Algebra.smul_def]
    linear_combination h0
  let co : κ → A → ResidueField O := fun u x =>
    if h : ∃ a : κ → O, x = ∑ v, a v • ε v then residue O (h.choose u) else 0
  have hco : ∀ x (a : κ → O), x = ∑ v, a v • ε v → ∀ u, co u x = residue O (a u) := by
    intro x a hx u
    have h : ∃ a : κ → O, x = ∑ v, a v • ε v := ⟨a, hx⟩
    simp only [co]
    rw [dite_eq_left h]
    have hd : ∑ v, (h.choose v - a v) • ε v = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [← h.choose_spec, ← hx, sub_self]
    rw [← sub_eq_zero, ← map_sub]
    exact (IsLocalRing.residue_eq_zero_iff _).2 (hrel _ hd u)
  refine ⟨co, ?_, ?_, ?_, ?_⟩
  · intro u x hx y hy
    obtain ⟨a, ha⟩ := hrep x hx
    obtain ⟨b, hb⟩ := hrep y hy
    have hxy : x + y = ∑ v, (a + b) v • ε v := by
      rw [ha, hb, ← Finset.sum_add_distrib]
      simp only [Pi.add_apply, add_smul]
    rw [hco _ _ hxy u, hco _ _ ha u, hco _ _ hb u, Pi.add_apply, map_add (f := _)]
  · intro u a x hx
    obtain ⟨b, hb⟩ := hrep x hx
    obtain ⟨c, hc⟩ := IsCO.res_surj (O := O) a
    have hax : a * x = ∑ v, (c * b v) • ε v := by
      have h0 := hkill _ _ hc hx
      have h1 : a * x = algebraMap O A c * x := by linear_combination h0
      rw [h1, hb, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      rw [mul_smul, ← Algebra.smul_def]
    have hr : res O A a = residue O c := by
      have h1 := (res_eq_zero_iff O A _).2 hc
      rw [map_sub, sub_eq_zero, AlgHom.commutes] at h1
      rw [h1]
      rfl
    rw [hco _ _ hax u, hco _ _ hb u, map_mul, hr]
  · intro u j hj x hxK hxP
    obtain ⟨a, ha⟩ := hrep x hxK
    rw [hco x a ha u]
    apply (IsLocalRing.residue_eq_zero_iff _).2
    have hε' : ∀ v, ε v ∈ Submodule.map W.π.toLinearMap (wtPart O W.wt (wf v)) := hε
    choose f hf hfε using fun v => Submodule.mem_map.1 (hε' v)
    have hxP' : x ∈ Submodule.map W.π.toLinearMap (wtPart O W.wt j) := hxP
    obtain ⟨g, hg, hgx⟩ := Submodule.mem_map.1 hxP'
    simp only [AlgHom.toLinearMap_apply] at hfε hgx
    have hk : g - ∑ v, a v • f v ∈ RingHom.ker W.π := by

      rw [RingHom.mem_ker, map_sub, map_sum]
      simp only [map_smul, hfε]
      rw [hgx, ← ha, sub_self]
    have hh := W.homog _ hk (wf u)
    have hfw : ∀ v, wcomp O W.wt (wf u) (f v) = if wf v = wf u then f v else 0 :=
      fun v => wcomp_of_mem_ite W.wt (hf v)

    rw [map_sub, map_sum, wcomp_of_mem_ite W.wt hg, if_neg hj] at hh
    simp only [map_smul, hfw] at hh
    have hrel0 : ∑ v, (if wf v = wf u then a v else 0) • ε v = 0 := by
      have h2 := RingHom.mem_ker.1 hh

      rw [map_sub, map_zero, map_sum, zero_sub, neg_eq_zero] at h2
      rw [← h2]
      apply Finset.sum_congr rfl
      intro v _
      split_ifs with hv
      · rw [map_smul, hfε]
      · rw [smul_zero, map_zero, zero_smul]
    have h5 := hrel _ hrel0 u
    simpa using h5
  · intro x hx
    obtain ⟨a, ha⟩ := hrep x hx
    exact ⟨a, fun u => (hco x a ha u).symm, ha⟩
end

section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem mvPowerSeries_mem_span_X_of_constantCoeff_zero {σ R : Type} [Finite σ] [CommRing R] (h : MvPowerSeries σ R)
    (h0 : MvPowerSeries.constantCoeff h = 0) :
    h ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R)) := by
  classical
  have := Fintype.ofFinite σ
  have hex : ∀ d : σ →₀ ℕ, ∃ o : Option σ, d ≠ 0 → ∃ s, o = some s ∧ d s ≠ 0 := by
    intro d
    by_cases hd : d = 0
    · exact ⟨none, fun h => (h hd).elim⟩
    · obtain ⟨s, hs⟩ : ∃ s, d s ≠ 0 := by
        by_contra H
        push_neg at H
        exact hd (Finsupp.ext H)
      exact ⟨some s, fun _ => ⟨s, rfl, hs⟩⟩
  choose sel hsel using hex
  let g : σ → MvPowerSeries σ R := fun s e =>
    if sel (e + Finsupp.single s 1) = some s then MvPowerSeries.coeff (e + Finsupp.single s 1) h
    else 0
  have key : h = ∑ s, MvPowerSeries.X s * g s := by
    ext d

    rw [map_sum]
    simp_rw [MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul, one_mul]
    by_cases hd : d = 0
    · subst hd
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h0]
      refine (Finset.sum_eq_zero fun s _ => ?_).symm
      rw [if_neg]
      simp [Finsupp.single_le_iff]
    · obtain ⟨s0, hs0, hds0⟩ := hsel d hd
      have hle0 : Finsupp.single s0 1 ≤ d := Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hds0)
      rw [Finset.sum_eq_single s0]
      · rw [if_pos hle0]
        show _ = (if sel (d - Finsupp.single s0 1 + Finsupp.single s0 1) = some s0 then
          MvPowerSeries.coeff (d - Finsupp.single s0 1 + Finsupp.single s0 1) h else 0)
        rw [tsub_add_cancel_of_le hle0, if_pos hs0]
      · intro s _ hs
        split_ifs with hle
        · show (if sel (d - Finsupp.single s 1 + Finsupp.single s 1) = some s then
            MvPowerSeries.coeff (d - Finsupp.single s 1 + Finsupp.single s 1) h else 0) = 0
          rw [tsub_add_cancel_of_le hle, hs0, if_neg]
          intro h'
          exact hs (Option.some_injective _ h').symm
        · rfl
      · simp
  rw [key]
  exact Ideal.sum_mem _ fun s _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨s, rfl⟩)

private theorem mvPowerSeries_exists_polynomial_sub_mem_span_X_pow {σ R : Type} [Finite σ] [CommRing R] (n : ℕ) (g : MvPowerSeries σ R) :
    ∃ p : MvPolynomial σ R, g - (p : MvPowerSeries σ R) ∈
      (Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R))) ^ n := by
  classical
  have := Fintype.ofFinite σ
  induction n generalizing g with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    have h1 : g - MvPowerSeries.C (MvPowerSeries.constantCoeff g) ∈
        Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R)) :=
      mvPowerSeries_mem_span_X_of_constantCoeff_zero _ (by simp)
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (MvPowerSeries σ R)).mp h1
    choose p hp using fun s => ih (c s)
    refine ⟨MvPolynomial.C (MvPowerSeries.constantCoeff g) + ∑ s, p s * MvPolynomial.X s, ?_⟩
    have hsum : ((∑ s, p s * MvPolynomial.X s : MvPolynomial σ R) : MvPowerSeries σ R) =
        ∑ s, (p s : MvPowerSeries σ R) * MvPowerSeries.X s := by

      rw [← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_sum]
      simp [MvPolynomial.coeToMvPowerSeries.ringHom_apply]
    have e : g - ((MvPolynomial.C (MvPowerSeries.constantCoeff g) + ∑ s, p s * MvPolynomial.X s :
        MvPolynomial σ R) : MvPowerSeries σ R) =
        ∑ s, (c s - (p s : MvPowerSeries σ R)) * MvPowerSeries.X s := by
      rw [MvPolynomial.coe_add, hsum, MvPolynomial.coe_C, ← sub_sub, ← hc]
      simp [sub_mul, smul_eq_mul, Finset.sum_sub_distrib]
    rw [e, pow_succ]
    exact Ideal.sum_mem _ fun s _ => Ideal.mul_mem_mul (hp s) (Ideal.subset_span ⟨s, rfl⟩)

theorem UpperTheory.V.Alg.co_ev :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (σ : Type) [Finite σ] (f : R →ₐ[O] R') (a : σ → R'), (∀ s, a s ∈ maximalIdeal R') →
      ∃! F : MvPowerSeries σ R →ₐ[O] R', (∀ x, F (C x) = f x) ∧ ∀ s, F (X s) = a s := by
  intro O _ _ R _ _ _ R' _ _ _ σ _ f a ha
  classical
  letI : WithIdeal R' := ⟨maximalIdeal R'⟩
  have hcs : CompleteSpace R' ∧ T2Space R' :=
    (IsAdic.isAdicComplete_iff (R := R') (I := maximalIdeal R') rfl).mp (IsCO.complete (O := O))
  haveI := hcs.1
  haveI := hcs.2
  have hE : MvPowerSeries.HasEval a :=
    ⟨fun s => WithIdeal.isTopologicallyNilpotent_of_mem (ha s), by simp [Filter.cofinite_eq_bot]⟩
  let E : MvPowerSeries σ R →+* R' :=
    (MvPowerSeries.aeval hE).toRingHom.comp (MvPowerSeries.map f.toRingHom)
  have hEC : ∀ x, E (C x) = f x := by
    intro x
    simp [E, MvPowerSeries.coe_aeval, MvPowerSeries.eval₂_C, MvPowerSeries.map_C]
  have hEX : ∀ s, E (X s) = a s := by
    intro s
    simp [E, MvPowerSeries.coe_aeval, MvPowerSeries.eval₂_X, MvPowerSeries.map_X]
  let F : MvPowerSeries σ R →ₐ[O] R' :=
    { E with
      commutes' := fun r => by
        change E (algebraMap O (MvPowerSeries σ R) r) = _
        rw [MvPowerSeries.algebraMap_apply, hEC]
        simp }
  refine ⟨F, ⟨hEC, hEX⟩, ?_⟩
  rintro G ⟨hGC, hGX⟩
  have hpoly : ∀ (H : MvPowerSeries σ R →ₐ[O] R'), (∀ x, H (C x) = f x) → (∀ s, H (X s) = a s) →
      ∀ p : MvPolynomial σ R, H (p : MvPowerSeries σ R) = MvPolynomial.eval₂ f.toRingHom a p := by
    intro H hC hX p
    induction p using MvPolynomial.induction_on with
    | C c => simp [MvPolynomial.coe_C, hC]
    | add p q hp hq => simp [MvPolynomial.coe_add, hp, hq]
    | mul_X p s hp => simp [MvPolynomial.coe_mul, MvPolynomial.coe_X, hp, hX]
  have hJ : ∀ (H : MvPowerSeries σ R →ₐ[O] R'), (∀ s, H (X s) = a s) → ∀ n,
      ∀ y ∈ (Ideal.span (Set.range (X : σ → MvPowerSeries σ R))) ^ n, H y ∈ maximalIdeal R' ^ n := by
    intro H hX n y hy
    have h1 : Ideal.map H (Ideal.span (Set.range (X : σ → MvPowerSeries σ R))) ≤ maximalIdeal R' := by
      rw [Ideal.map_span, Ideal.span_le]
      rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
      rw [hX]
      exact ha s
    have h2 := Ideal.mem_map_of_mem H hy
    rw [Ideal.map_pow] at h2
    exact Ideal.pow_right_mono h1 n h2
  have hH : IsHausdorff (maximalIdeal R') R' := (IsCO.complete (O := O)).toIsHausdorff
  ext g
  rw [← sub_eq_zero]
  refine hH.haus _ fun n => ?_
  obtain ⟨p, hp⟩ := mvPowerSeries_exists_polynomial_sub_mem_span_X_pow n g
  have e1 : G g - F g = G (g - p) - F (g - p) := by
    rw [map_sub, map_sub, hpoly G hGC hGX, hpoly F (fun x => hEC x) (fun s => hEX s)]
    ring
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, e1]
  exact Ideal.sub_mem _ (hJ G hGX n _ hp) (hJ F (fun s => hEX s) n _ hp)
end

section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem wcomp_mul_homog {O σ X : Type} [CommRing O] [AddCommGroup X] (wt : σ → X) {c : X}
    {a : MvPowerSeries σ O} (ha : a ∈ wtPart O wt c) (j : X) (b : MvPowerSeries σ O) :
    wcomp O wt j (b * a) = wcomp O wt (j - c) b * a := by
  classical
  ext n
  rw [coeff_wcomp, coeff_mul, coeff_mul]
  split_ifs with h
  · refine Finset.sum_congr rfl fun p hp => ?_
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    by_cases h2 : Finsupp.weight wt p.2 = c
    · rw [coeff_wcomp, if_pos]
      rw [← h, ← hp', map_add (f := _), h2, add_sub_cancel_right]
    · rw [ha _ h2, mul_zero, mul_zero]
  · refine (Finset.sum_eq_zero fun p hp => ?_).symm
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    by_cases h2 : Finsupp.weight wt p.2 = c
    · rw [coeff_wcomp, if_neg, zero_mul]
      intro h1
      exact h (by rw [← hp', map_add (f := _), h1, h2, sub_add_cancel])
    · rw [ha _ h2, mul_zero]

private theorem homog_of_span {O σ X : Type} [CommRing O] [AddCommGroup X] (wt : σ → X)
    (S : Set (MvPowerSeries σ O)) (hS : ∀ a ∈ S, ∃ c, a ∈ wtPart O wt c) :
    IsHomog O wt (Ideal.span S) := by
  intro f hf j
  have key : ∀ b : MvPowerSeries σ O, ∀ j, wcomp O wt j (b * f) ∈ Ideal.span S := by
    induction hf using Submodule.span_induction with
    | mem a ha =>
      intro b j
      obtain ⟨c, hc⟩ := hS a ha
      rw [wcomp_mul_homog wt hc]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ha)
    | zero => intro b j; simp
    | add x y _ _ hx hy =>
      intro b j
      rw [mul_add, map_add (f := _)]
      exact add_mem (hx b j) (hy b j)
    | smul r x _ hx =>
      intro b j
      rw [smul_eq_mul, ← mul_assoc]
      exact hx _ j
  simpa using key 1 j

private theorem homog_span_pow {O σ X : Type} [CommRing O] [AddCommGroup X] (wt : σ → X)
    (S : Set (MvPowerSeries σ O)) (hS : ∀ a ∈ S, ∃ c, a ∈ wtPart O wt c) (N : ℕ) :
    IsHomog O wt (Ideal.span S ^ N) := by
  have key : ∃ T : Set (MvPowerSeries σ O), (∀ a ∈ T, ∃ c, a ∈ wtPart O wt c) ∧
      Ideal.span S ^ N = Ideal.span T := by
    induction N with
    | zero =>
      refine ⟨{1}, ?_, by simp⟩
      rintro a rfl
      exact ⟨0, one_mem_wtPart O wt⟩
    | succ n ih =>
      obtain ⟨T, hT, hT'⟩ := ih
      refine ⟨_, ?_, by rw [pow_succ, hT', Ideal.span_mul_span']⟩
      rintro _ ⟨a, ha, b, hb, rfl⟩
      obtain ⟨c, hc⟩ := hT a ha
      obtain ⟨d, hd⟩ := hS b hb
      exact ⟨c + d, mul_mem_wtPart O wt hc hd⟩
  obtain ⟨T, hT, hT'⟩ := key
  rw [hT']
  exact homog_of_span wt T hT

private theorem mem_span_X {O σ : Type} [CommRing O] [Fintype σ] (f : MvPowerSeries σ O)
    (hf : constantCoeff f = 0) : f ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)) :=
  _root_.UpperTheory.Reformulated.B.MemSpanVariable.mem_span_X f hf

theorem UpperTheory.V.Alg.part_closed :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O X R), (∀ s, W.z s ∈ maximalIdeal R) → ∀ (j : X) (x : R), (∀ N : ℕ, ∃ y ∈ W.part j, x - y ∈ maximalIdeal R ^ N) → x ∈ W.part j := by
  intro O _ _ _ _ X _ _ _ _ R _ _ hR W hz j x hx
  classical
  have hl : IsLocalHom (algebraMap O R) := IsCO.isLocalHom
  have hn : IsNoetherianRing R := hR.toIsNoetherian
  let S : Set (MvPowerSeries W.σ O) :=
    Set.range MvPowerSeries.X ∪ algebraMap O _ '' (maximalIdeal O : Set O)
  have hS : ∀ a ∈ S, ∃ c, a ∈ wtPart O W.wt c := by
    rintro _ (⟨i, rfl⟩ | ⟨a, -, rfl⟩)
    · exact ⟨_, X_mem_wtPart O W.wt i⟩
    · refine ⟨0, ?_⟩
      rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ (one_mem_wtPart O W.wt)
  have hle : (Ideal.span S).map W.π ≤ maximalIdeal R := by
    rw [Ideal.map_le_iff_le_comap, Ideal.span_le]
    rintro _ (⟨i, rfl⟩ | ⟨a, ha, rfl⟩)
    · exact hz i
    · show W.π (algebraMap O _ a) ∈ maximalIdeal R
      rw [AlgHom.commutes]
      exact fun h => ha (IsLocalHom.map_nonunit a h)
  have hmap : (Ideal.span S).map W.π = maximalIdeal R := by
    refine le_antisymm hle fun r hr => ?_
    obtain ⟨f, rfl⟩ := W.surj r
    have h1 : f - algebraMap O _ (constantCoeff f) ∈ Ideal.span S := by
      refine Ideal.span_mono Set.subset_union_left (mem_span_X _ ?_)
      simp [MvPowerSeries.algebraMap_apply]
    have h2 : constantCoeff f ∈ maximalIdeal O := fun hu =>
      hr ((MvPowerSeries.isUnit_iff_constantCoeff.2 hu).map W.π)
    have h3 : algebraMap O _ (constantCoeff f) ∈ Ideal.span S :=
      Ideal.subset_span (Or.inr ⟨_, h2, rfl⟩)
    exact Ideal.mem_map_of_mem _ (by simpa using add_mem h1 h3)
  obtain ⟨f, rfl⟩ := W.surj x
  have key : ∀ N : ℕ, W.π (f - wcomp O W.wt j f) ∈ maximalIdeal R ^ N := by
    intro N
    obtain ⟨_, ⟨y, hy, rfl⟩, hxy⟩ := hx N
    rw [← hmap, ← Ideal.map_pow] at hxy ⊢
    obtain ⟨g, hg, hgxy⟩ := (Ideal.mem_map_iff_of_surjective W.π W.surj).1 hxy
    have h1 : f - y - g ∈ RingHom.ker W.π := by
      rw [RingHom.mem_ker, map_sub, map_sub, hgxy]
      exact sub_self _
    have h2 := W.homog _ h1 j
    have h3 : wcomp O W.wt j y = y := by
      ext n
      rw [coeff_wcomp]
      split_ifs with h
      · rfl
      · exact (hy n h).symm
    have h4 : g - wcomp O W.wt j g ∈ Ideal.span S ^ N :=
      sub_mem hg (homog_span_pow W.wt S hS N g hg j)
    have h5 : f - wcomp O W.wt j f =
        (f - y - g) - wcomp O W.wt j (f - y - g) + (g - wcomp O W.wt j g) := by
      rw [map_sub, map_sub, h3]; ring
    rw [h5, map_add (f := _), (RingHom.mem_ker).1 (sub_mem h1 h2), zero_add]
    exact Ideal.mem_map_of_mem _ h4
  have h0 : W.π (f - wcomp O W.wt j f) = 0 := by
    have := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal R) (maximalIdeal.isMaximal R).ne_top
    rw [← Ideal.mem_bot, ← this, Ideal.mem_iInf]
    exact key
  rw [map_sub, sub_eq_zero] at h0
  exact ⟨_, wcomp_mem O W.wt j f, h0.symm⟩
end
