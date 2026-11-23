module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle047
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle003
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Module.Torsion.Basic

@[expose] public section

section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem tact_prod {X σ S : Type} [AddCommGroup X] [CommRing S] (wt : σ → X)
    (t : Multiplicative X →* Sˣ) (x : σ → S) (d : σ →₀ ℕ) :
    (d.prod fun i k => ((t (Multiplicative.ofAdd (wt i)) : S) * x i) ^ k) =
      (t (Multiplicative.ofAdd (Finsupp.weight wt d)) : S) * d.prod fun i k => x i ^ k := by
  simp_rw [mul_pow]
  rw [Finsupp.prod_mul]
  congr 1
  rw [Finsupp.weight_apply, Finsupp.sum, ofAdd_sum, map_prod, Units.coe_prod, Finsupp.prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [ofAdd_nsmul, map_pow, Units.val_pow_eq_pow_val]

private theorem tact_aeval {O X σ S : Type} [CommRing O] [AddCommGroup X] [CommRing S] [Algebra O S]
    (wt : σ → X) (t : Multiplicative X →* Sˣ) (x : σ → S) (j : X) (p : MvPolynomial σ O)
    (hp : ∀ d, Finsupp.weight wt d ≠ j → AddMonoidAlgebra.coeff p d = 0) :
    MvPolynomial.aeval (fun i => (t (Multiplicative.ofAdd (wt i)) : S) * x i) p =
      (t (Multiplicative.ofAdd j) : S) * MvPolynomial.aeval x p := by

  rw [p.as_sum, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd' : Finsupp.weight wt d = j := by
    by_contra h
    exact MvPolynomial.mem_support_iff.1 hd (hp d h)
  rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial, tact_prod, hd']
  ring

private theorem tact_approx {O X σ : Type} [CommRing O] [AddCommGroup X] [Finite σ] (wt : σ → X)
    (F : MvPowerSeries σ O) (n : ℕ) :
    ∃ s : Finset X, (n : ℕ∞) ≤ (F - ∑ j ∈ s, wcomp O wt j F).order := by
  classical
  refine ⟨(truncTotal n F).support.image (Finsupp.weight wt), nat_le_order fun d hd => ?_⟩

  rw [map_sub, map_sum]
  simp only [coeff_wcomp]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · exact sub_self _
  · rw [sub_zero]
    by_contra h0
    refine h (Finset.mem_image_of_mem _ (MvPolynomial.mem_support_iff.2 ?_))
    rwa [coeff_truncTotal _ hd]

private theorem tact_vanish {O X σ S : Type} [CommRing O] [AddCommGroup X] [Finite σ] [CommRing S]
    [Algebra O S] (wt : σ → X) (J : Ideal S) [IsHausdorff J S] (φ : MvPowerSeries σ O →ₐ[O] S)
    (hφ : ∀ i, φ (MvPowerSeries.X i) ∈ J) (F : MvPowerSeries σ O) (h : ∀ j, φ (wcomp O wt j F) = 0) :
    φ F = 0 := by
  apply GlobalTheory.eq_of_forall_sub_mem_ideal_pow J
  intro n
  obtain ⟨s, hs⟩ := tact_approx wt F n
  have hm := GlobalTheory.algHom_mem_pow_of_le_order φ hφ hs

  rw [map_sub, map_sum] at hm
  simpa [h] using hm

theorem UpperTheory.V.Alg.tact :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (X : Type) [AddCommGroup X] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O X R), (∀ s, W.z s ∈ maximalIdeal R) → ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') (t : Multiplicative X →* R'ˣ),
      ∃! f' : R →ₐ[O] R', ∀ j, ∀ x ∈ W.part j, f' x = t (Multiplicative.ofAdd j) * f x := by
  intro O _ _ X _ R _ _ _ W hz R' _ _ _ f t
  classical
  haveI : Fintype W.σ := W.fin
  haveI : IsAdicComplete (maximalIdeal R') R' := IsCO.complete (O := O)
  have hf_max : ∀ x ∈ maximalIdeal R, f x ∈ maximalIdeal R' := by
    intro x hx
    rw [← res_eq_zero_iff O R' (f x), UpperTheory.V.Alg.res_map f x, res_eq_zero_iff O R x]
    exact hx
  let xs : W.σ → R' := fun i =>
    (t (Multiplicative.ofAdd (W.wt i)) : R') * f (W.π (MvPowerSeries.X i))
  have hxs : ∀ i, xs i ∈ maximalIdeal R' := fun i => Ideal.mul_mem_left _ _ (hf_max _ (hz i))
  obtain ⟨Ψ, hΨX, hΨtr⟩ : ∃ Ψ : MvPowerSeries W.σ O →ₐ[O] R', (∀ i, Ψ (MvPowerSeries.X i) = xs i) ∧
      ∀ (n : ℕ) (G : MvPowerSeries W.σ O),
        Ψ G - MvPolynomial.aeval xs (truncTotal n G) ∈ maximalIdeal R' ^ n :=
    ⟨_, GlobalTheory.mvEvalAdic_X _ xs hxs, GlobalTheory.mvEvalAdic_sub_aeval_truncTotal_mem _ xs hxs⟩
  have key : ∀ j, ∀ G ∈ wtPart O W.wt j,
      Ψ G = (t (Multiplicative.ofAdd j) : R') * f (W.π G) := by
    intro j G hG
    apply GlobalTheory.eq_of_forall_sub_mem_ideal_pow (maximalIdeal R')
    intro n
    have h1 := hΨtr n G
    have h2 := GlobalTheory.algHom_sub_aeval_truncTotal_mem (f.comp W.π) (J := maximalIdeal R')
      (fun i => hf_max _ (hz i)) n G
    simp only [AlgHom.coe_comp, Function.comp_apply] at h2
    have h3 : MvPolynomial.aeval xs (truncTotal n G) =
        (t (Multiplicative.ofAdd j) : R') *
          MvPolynomial.aeval (fun i => f (W.π (MvPowerSeries.X i))) (truncTotal n G) := by
      refine tact_aeval W.wt t (fun i => f (W.π (MvPowerSeries.X i))) j _ fun d hd => ?_
      rw [coeff_truncTotal_eq_ite]
      split_ifs
      · exact hG d hd
      · rfl
    have he : Ψ G - (t (Multiplicative.ofAdd j) : R') * f (W.π G) =
        (Ψ G - MvPolynomial.aeval xs (truncTotal n G)) -
          (t (Multiplicative.ofAdd j) : R') *
            (f (W.π G) - MvPolynomial.aeval (fun i => f (W.π (MvPowerSeries.X i))) (truncTotal n G)) := by
      rw [h3]
      ring
    rw [he]
    exact Ideal.sub_mem _ h1 (Ideal.mul_mem_left _ _ h2)
  have hker : ∀ F ∈ RingHom.ker W.π, Ψ F = 0 := by
    intro F hF
    refine tact_vanish W.wt (maximalIdeal R') Ψ (fun i => by rw [hΨX]; exact hxs i) F fun j => ?_
    rw [key j _ (wcomp_mem O W.wt j F)]
    have h0 : W.π (wcomp O W.wt j F) = 0 := RingHom.mem_ker.mp (W.homog F hF j)
    rw [h0, map_zero, mul_zero]
  let f' : R →ₐ[O] R' := (Ideal.Quotient.liftₐ (RingHom.ker W.π) Ψ hker).comp
    (Ideal.quotientKerAlgEquivOfSurjective W.surj).symm.toAlgHom
  have hf'π : ∀ G, f' (W.π G) = Ψ G := by
    intro G
    have hs : (Ideal.quotientKerAlgEquivOfSurjective W.surj).symm (W.π G) =
        Ideal.Quotient.mk (RingHom.ker W.π) G := by
      rw [AlgEquiv.symm_apply_eq]
      rfl
    show Ideal.Quotient.liftₐ (RingHom.ker W.π) Ψ hker
      ((Ideal.quotientKerAlgEquivOfSurjective W.surj).symm (W.π G)) = Ψ G
    rw [hs]
    rfl
  refine ⟨f', ?_, ?_⟩
  · intro j x hx
    obtain ⟨G, hG, rfl⟩ := Submodule.mem_map.mp hx
    simp only [AlgHom.toLinearMap_apply]
    rw [hf'π, key j G hG]
  · intro g hg
    have hgz : ∀ i, g (W.π (MvPowerSeries.X i)) = xs i := fun i => hg (W.wt i) (W.z i) (W.z_mem i)
    have hcomp : g.comp W.π = Ψ := by
      apply GlobalTheory.mvPowerSeries_algHom_ext_of_isHausdorff (maximalIdeal R')
      · intro i
        rw [AlgHom.comp_apply, hgz]
        exact hxs i
      · intro i
        rw [AlgHom.comp_apply, hgz, hΨX]
    ext x
    obtain ⟨G, rfl⟩ := W.surj x
    rw [hf'π, ← AlgHom.comp_apply, hcomp]
end

section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem chain_stab {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (K : Ideal R)
    (hK : maximalIdeal R * K = ⊥) (F : ℕ → Ideal R) (hF : Antitone F) (hle : ∀ n, F n ≤ K) :
    ∃ N, ∀ n, F N ≤ F n := by
  classical
  have hT : Module.IsTorsionBySet R K (maximalIdeal R : Set R) := by
    intro x a
    apply Subtype.ext
    have h1 : (a : R) * (x : R) ∈ maximalIdeal R * K := Ideal.mul_mem_mul a.2 x.2
    rw [hK] at h1
    simpa using h1
  letI : Module (R ⧸ maximalIdeal R) K := hT.module
  haveI : IsScalarTower R (R ⧸ maximalIdeal R) K := hT.isScalarTower
  haveI : Module.Finite R K := Module.Finite.iff_fg.mpr (IsNoetherian.noetherian K)
  haveI : Module.Finite (R ⧸ maximalIdeal R) K :=
    Module.Finite.of_restrictScalars_finite R _ _
  letI : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  haveI : IsArtinianRing (R ⧸ maximalIdeal R) := inferInstance
  haveI : IsArtinian (R ⧸ maximalIdeal R) K := isArtinian_of_fg_of_artinian'
  haveI : IsArtinian R K := isArtinian_of_surjective_algebraMap (R := R ⧸ maximalIdeal R)
    (Ideal.Quotient.mk_surjective (I := maximalIdeal R))
  let G : ℕ → Submodule R K := fun n => Submodule.comap (Submodule.subtype K) (F n)
  have hG : Antitone G := fun a b h => Submodule.comap_mono (hF h)
  obtain ⟨_, ⟨N, rfl⟩, hmin⟩ :=
    (wellFounded_lt (α := Submodule R K)).has_min (Set.range G) ⟨_, 0, rfl⟩
  refine ⟨N, fun n => ?_⟩
  have hle2 : G (max N n) ≤ G N := hG (le_max_left _ _)
  have heq : G (max N n) = G N := by
    by_contra hne
    exact hmin _ ⟨_, rfl⟩ (lt_of_le_of_ne hle2 hne)
  intro x hx
  have hxK : x ∈ K := hle N hx
  have h2 : (⟨x, hxK⟩ : K) ∈ G N := hx
  rw [← heq] at h2
  exact hF (le_max_right N n) h2

private theorem mul_mem_of_mem_ideal_killed_by_maximalIdeal {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R]
    [IsCO O R] (J : Ideal R) (hJ : maximalIdeal R * J = ⊥) (S : Submodule O R) (r k : R)
    (hk : k ∈ J) (hS : k ∈ S) : r * k ∈ S := by
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) r
  have h0 : (r - algebraMap O R a) * k = 0 := by
    have h1 := Ideal.mul_mem_mul ha hk
    rw [hJ] at h1
    exact (Ideal.mem_bot).1 h1
  have h2 : r * k = a • k := by
    rw [Algebra.smul_def]
    linear_combination h0
  rw [h2]
  exact S.smul_mem a hS

theorem UpperTheory.V.Alg.cont_section :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (p : R →ₐ[O] R'), Function.Surjective p → maximalIdeal R * RingHom.ker p = ⊥ → ∀ (W : WPres O X R), (∀ s, W.z s ∈ maximalIdeal R) →
      ∀ (Γ : Type) [TopologicalSpace Γ] (j : X) (x : Γ → R'), AdicCont (maximalIdeal R') x → (∀ g, x g ∈ (W.part j).map p.toLinearMap) →
      ∃ y : Γ → R, AdicCont (maximalIdeal R) y ∧ (∀ g, y g ∈ W.part j) ∧ ∀ g, p (y g) = x g := by
  intro O _ _ _ _ X _ _ _ R _ _ _ R' _ _ _ p hp hker W hz Γ _ j x hxc hxp
  classical
  have hmem : ∀ r : R, p r ∈ maximalIdeal R' ↔ r ∈ maximalIdeal R := by
    intro r
    rw [← res_eq_zero_iff O R', ← res_eq_zero_iff O R, res_map]
  have hmapm : Ideal.map p (maximalIdeal R) = maximalIdeal R' := by
    ext a
    rw [Ideal.mem_map_iff_of_surjective p hp]
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact (hmem r).2 hr
    · intro ha
      obtain ⟨r, rfl⟩ := hp a
      exact ⟨r, (hmem r).1 ha, rfl⟩
  have hlift : ∀ n (a : R'), a ∈ maximalIdeal R' ^ n → ∃ w, w ∈ maximalIdeal R ^ n ∧ p w = a := by
    intro n a ha
    rw [← hmapm, ← Ideal.map_pow] at ha
    exact (Ideal.mem_map_iff_of_surjective p hp).1 ha
  obtain ⟨N0, hN0⟩ := chain_stab (RingHom.ker p) hker (fun n => maximalIdeal R ^ n ⊓ RingHom.ker p)
    (fun a b h => inf_le_inf_right _ (Ideal.pow_le_pow_right h)) (fun n => inf_le_right)
  have hinj : ∀ u v : R, u ∈ maximalIdeal R ^ N0 → v ∈ maximalIdeal R ^ N0 → p u = p v → u = v := by
    intro u v hu hv huv
    have hk : u - v ∈ maximalIdeal R ^ N0 ⊓ RingHom.ker p :=
      ⟨Ideal.sub_mem _ hu hv, (RingHom.mem_ker).2 (by rw [map_sub, huv, sub_self])⟩
    have hall : u - v ∈ ⨅ n, maximalIdeal R ^ n := Ideal.mem_iInf.2 fun n => (hN0 n hk).1
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing (I := maximalIdeal R)
      (IsLocalRing.maximalIdeal.isMaximal R).ne_top] at hall
    exact sub_eq_zero.1 ((Ideal.mem_bot).1 hall)
  let F : ℕ → Ideal R := fun n =>
    { carrier := {k | k ∈ RingHom.ker p ∧ k ∈ W.part j ⊔ (maximalIdeal R ^ n).restrictScalars O}
      add_mem' := fun ha hb => ⟨Ideal.add_mem _ ha.1 hb.1, Submodule.add_mem _ ha.2 hb.2⟩
      zero_mem' := ⟨Ideal.zero_mem _, Submodule.zero_mem _⟩
      smul_mem' := fun r k hk =>
        ⟨Ideal.mul_mem_left _ r hk.1, mul_mem_of_mem_ideal_killed_by_maximalIdeal (O := O) _ hker _ r k hk.1 hk.2⟩ }
  have hFanti : Antitone F := by
    intro a b h k hk
    have H : (maximalIdeal R ^ b).restrictScalars O ≤ (maximalIdeal R ^ a).restrictScalars O :=
      fun z hz => Ideal.pow_le_pow_right h hz
    exact ⟨hk.1, SetLike.le_def.1 (sup_le_sup_left H (W.part j)) hk.2⟩
  obtain ⟨N1, hN1⟩ := chain_stab (RingHom.ker p) hker F hFanti (fun n k hk => hk.1)
  have hclosed : ∀ k, k ∈ RingHom.ker p →
      k ∈ W.part j ⊔ (maximalIdeal R ^ N1).restrictScalars O → k ∈ W.part j := by
    intro k hk1 hk2
    have hkF : k ∈ F N1 := ⟨hk1, hk2⟩
    apply part_closed O X R W hz j k
    intro N
    obtain ⟨y, hy, z, hz2, hyz⟩ := Submodule.mem_sup.1 (hN1 N hkF).2
    refine ⟨y, hy, ?_⟩
    rw [← hyz, add_sub_cancel_left]
    exact hz2
  have hL : ∀ a, a ∈ (W.part j).map p.toLinearMap → a ∈ maximalIdeal R' ^ (max N0 N1) →
      ∃ w, w ∈ W.part j ∧ w ∈ maximalIdeal R ^ (max N0 N1) ∧ p w = a := by
    intro a ha haM
    obtain ⟨e, he, rfl⟩ := Submodule.mem_map.1 ha
    obtain ⟨w, hw, hpw⟩ := hlift _ _ haM
    have hk1 : e - w ∈ RingHom.ker p := by
      rw [RingHom.mem_ker, map_sub, hpw, AlgHom.toLinearMap_apply, sub_self]
    have hk2 : e - w ∈ W.part j ⊔ (maximalIdeal R ^ N1).restrictScalars O := by
      rw [sub_eq_add_neg]
      exact Submodule.add_mem_sup he
        (Submodule.neg_mem _ (Ideal.pow_le_pow_right (le_max_right _ _) hw))
    have hk := hclosed _ hk1 hk2
    refine ⟨w, ?_, hw, hpw⟩
    have h3 := Submodule.sub_mem _ he hk
    rwa [sub_sub_cancel] at h3
  let base : (R' ⧸ maximalIdeal R' ^ (max N0 N1)) → R := fun c =>
    if h : ∃ e, e ∈ W.part j ∧ Ideal.Quotient.mk (maximalIdeal R' ^ (max N0 N1)) (p e) = c
    then h.choose else 0
  have hbase : ∀ g, base (Ideal.Quotient.mk _ (x g)) ∈ W.part j ∧
      x g - p (base (Ideal.Quotient.mk _ (x g))) ∈ maximalIdeal R' ^ (max N0 N1) := by
    intro g
    obtain ⟨e, he, hpe⟩ := Submodule.mem_map.1 (hxp g)
    have h : ∃ e, e ∈ W.part j ∧ Ideal.Quotient.mk (maximalIdeal R' ^ (max N0 N1)) (p e) =
        Ideal.Quotient.mk _ (x g) := ⟨e, he, by rw [← hpe]; rfl⟩
    simp only [base]
    rw [dite_eq_left h]
    refine ⟨h.choose_spec.1, ?_⟩
    rw [← Ideal.Quotient.eq]
    exact h.choose_spec.2.symm
  have hw : ∀ g, ∃ w, w ∈ W.part j ∧ w ∈ maximalIdeal R ^ (max N0 N1) ∧
      p w = x g - p (base (Ideal.Quotient.mk _ (x g))) := by
    intro g
    apply hL
    · exact Submodule.sub_mem _ (hxp g) (Submodule.mem_map_of_mem (hbase g).1)
    · exact (hbase g).2
  choose w hwP hwM hwp using hw
  refine ⟨fun g => base (Ideal.Quotient.mk _ (x g)) + w g, ?_,
    fun g => Submodule.add_mem _ (hbase g).1 (hwP g), fun g => ?_⟩
  · unfold AdicCont at hxc ⊢
    intro N
    rw [IsLocallyConstant.iff_eventually_eq]
    intro g0
    have hx0 := (IsLocallyConstant.iff_eventually_eq _).1 (hxc (max N (max N0 N1))) g0
    filter_upwards [hx0] with g hg
    have hd : x g - x g0 ∈ maximalIdeal R' ^ max N (max N0 N1) := Ideal.Quotient.eq.1 hg
    have hcls : Ideal.Quotient.mk (maximalIdeal R' ^ (max N0 N1)) (x g) =
        Ideal.Quotient.mk _ (x g0) :=
      Ideal.Quotient.eq.2 (Ideal.pow_le_pow_right (le_max_right _ _) hd)
    obtain ⟨v, hv, hpv⟩ := hlift _ _ hd
    have hM0 : maximalIdeal R ^ (max N0 N1) ≤ maximalIdeal R ^ N0 :=
      Ideal.pow_le_pow_right (le_max_left _ _)
    have heq : w g - w g0 = v := by
      apply hinj
      · exact Ideal.sub_mem _ (hM0 (hwM g)) (hM0 (hwM g0))
      · exact Ideal.pow_le_pow_right (le_trans (le_max_left _ _) (le_max_right _ _)) hv
      · rw [map_sub, hwp, hwp, hpv, hcls]
        ring
    apply Ideal.Quotient.eq.2
    show base (Ideal.Quotient.mk _ (x g)) + w g - (base (Ideal.Quotient.mk _ (x g0)) + w g0) ∈ _
    rw [hcls]
    have h4 : base (Ideal.Quotient.mk _ (x g0)) + w g -
        (base (Ideal.Quotient.mk _ (x g0)) + w g0) = v := by
      rw [← heq]
      ring
    rw [h4]
    exact Ideal.pow_le_pow_right (le_max_left _ _) hv
  · show p (base _ + w g) = x g
    rw [map_add (f := _), hwp]
    ring
end
