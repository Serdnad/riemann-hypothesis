module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Ideal.BigOperators

@[expose] public section

section

open TensorProduct

namespace GlobalTheory

theorem _root_.GlobalTheory.exists_basis_in_finite_domain_trace_mem (T C F K : Type) [CommRing T] [IsDomain T]
    [IsIntegrallyClosed T] [CommRing C] [IsDomain C] [Field F] [Field K] [Algebra T C]
    [Algebra T F] [IsFractionRing T F] [Algebra C K] [IsFractionRing C K] [Algebra T K]
    [Algebra F K] [IsScalarTower T C K] [IsScalarTower T F K] [Module.Finite T C] :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) F K),
      (∀ (i : Fin n), ∃ (c : C), (algebraMap C K : C → K) c = (b : Fin n → K) i) ∧
        ∀ (i j : Fin n), ∃ (t : T), (algebraMap T F : T → F) t =
          (Algebra.trace F K : K → F) ((b : Fin n → K) i * (b : Fin n → K) j) := by
  classical
  have hint : ∀ c : C, IsIntegral T (algebraMap C K c) := fun c =>
    (Algebra.IsIntegral.isIntegral c).map (IsScalarTower.toAlgHom T C K)
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := T) (M := C)
  have hM0 : ∀ c : C,
      algebraMap C K c ∈ Submodule.span F ((s.image (algebraMap C K) : Finset K) : Set K) := by
    intro c
    have hc : c ∈ Submodule.span T (s : Set C) := hs ▸ Submodule.mem_top
    induction hc using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (by simp only [Finset.coe_image]; exact ⟨x, hx, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul t x _ hx =>
      have : algebraMap C K (t • x) = algebraMap T F t • algebraMap C K x := by
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply T C K, Algebra.smul_def,
          ← IsScalarTower.algebraMap_apply T F K]
      rw [this]
      exact Submodule.smul_mem _ _ hx
  let M0 : Submonoid K := MonoidHom.mrange (algebraMap C K).toMonoidHom
  have hA0 : Algebra.adjoin F (M0 : Set K) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨a, d, hd, rfl⟩ := IsFractionRing.div_surjective C z
    have ha : algebraMap C K a ∈ Algebra.adjoin F (M0 : Set K) :=
      Algebra.subset_adjoin (MonoidHom.mem_mrange.2 ⟨a, rfl⟩)
    have hd' : algebraMap C K d ∈ Algebra.adjoin F (M0 : Set K) :=
      Algebra.subset_adjoin (MonoidHom.mem_mrange.2 ⟨d, rfl⟩)
    have hinv : (algebraMap C K d)⁻¹ ∈ Algebra.adjoin F (M0 : Set K) :=
      Subalgebra.inv_mem_of_algebraic _ (x := ⟨_, hd'⟩) (hint d).tower_top.isAlgebraic
    rw [div_eq_mul_inv]
    exact Subalgebra.mul_mem _ ha hinv
  have hspan : Submodule.span F (M0 : Set K) = ⊤ := by
    have h := Algebra.adjoin_eq_span F (M0 : Set K)
    rw [Submonoid.closure_eq, hA0, Algebra.top_toSubmodule] at h
    exact h.symm
  have htop : Submodule.span F ((s.image (algebraMap C K) : Finset K) : Set K) = ⊤ := by
    rw [eq_top_iff, ← hspan]
    exact Submodule.span_le.2 fun x hx => by
      obtain ⟨c, rfl⟩ := MonoidHom.mem_mrange.1 hx
      exact hM0 c
  haveI : FiniteDimensional F K := ⟨⟨s.image (algebraMap C K), htop⟩⟩
  obtain ⟨B, hBsub, hBspan, hBli⟩ :=
    exists_linearIndependent F ((s.image (algebraMap C K) : Finset K) : Set K)
  have hBfin : B.Finite := (Finset.finite_toSet _).subset hBsub
  haveI := hBfin.fintype
  let b0 : Module.Basis B F K := Module.Basis.mk hBli (by rw [Subtype.range_coe, hBspan, htop])
  let b := b0.reindex (Fintype.equivFin B)
  have hbC : ∀ i, ∃ c : C, algebraMap C K c = b i := by
    intro i
    have hmem : b i ∈ B := by simp [b, b0]
    obtain ⟨c, -, hc⟩ := Finset.mem_image.1 (hBsub hmem)
    exact ⟨c, hc⟩
  refine ⟨Fintype.card B, b, hbC, fun i j => ?_⟩
  obtain ⟨c, hc⟩ := hbC i
  obtain ⟨c', hc'⟩ := hbC j
  have hI : IsIntegral T (b i * b j) := by
    rw [← hc, ← hc', ← map_mul]
    exact hint _
  exact IsIntegrallyClosed.isIntegral_iff.1 (Algebra.isIntegral_trace hI)

end GlobalTheory
end

section

open IsLocalRing Polynomial

namespace GlobalTheory

theorem conductor_prod_fst (R S' S : Type) [CommRing R] [CommRing S'] [CommRing S]
    (e : S ≃+* R × S') (d : S)
    (hd : ∀ c : FractionRing S, IsIntegral S c →
      ∃ s : S, algebraMap S (FractionRing S) s = algebraMap S (FractionRing S) d * c) :
    ∀ c : FractionRing R, IsIntegral R c →
      ∃ s : R, algebraMap R (FractionRing R) s = algebraMap R (FractionRing R) (e d).1 * c := by
  intro c hc
  let g : S →+* FractionRing R × FractionRing S' :=
    (RingHom.prodMap (algebraMap R (FractionRing R)) (algebraMap S' (FractionRing S'))).comp
      e.toRingHom
  have hgx : ∀ x : S, g x = (algebraMap R (FractionRing R) (e x).1,
      algebraMap S' (FractionRing S') (e x).2) := fun x => rfl
  have hg : ∀ y : nonZeroDivisors S, IsUnit (g y) := by
    intro y
    rw [hgx, Prod.isUnit_iff]
    have h1 : (e y).1 ∈ nonZeroDivisors R := by
      rw [mem_nonZeroDivisors_iff_right]
      intro z hz
      have h0 : e.symm (z, 0) * (y : S) = 0 := by
        apply e.injective
        rw [map_mul, RingEquiv.apply_symm_apply, map_zero]
        ext <;> simp [hz]
      have := (mul_right_mem_nonZeroDivisors_eq_zero_iff y.2).mp h0
      have := congrArg (fun w => (e w).1) this
      simpa using this
    have h2 : (e y).2 ∈ nonZeroDivisors S' := by
      rw [mem_nonZeroDivisors_iff_right]
      intro z hz
      have h0 : e.symm (0, z) * (y : S) = 0 := by
        apply e.injective
        rw [map_mul, RingEquiv.apply_symm_apply, map_zero]
        ext <;> simp [hz]
      have := (mul_right_mem_nonZeroDivisors_eq_zero_iff y.2).mp h0
      have := congrArg (fun w => (e w).2) this
      simpa using this
    exact ⟨IsLocalization.map_units (FractionRing R) (⟨_, h1⟩ : nonZeroDivisors R),
      IsLocalization.map_units (FractionRing S') (⟨_, h2⟩ : nonZeroDivisors S')⟩
  let Θ : FractionRing S →+* FractionRing R × FractionRing S' := IsLocalization.lift hg
  have hΘ : ∀ x : S, Θ (algebraMap S (FractionRing S) x) = g x := fun x =>
    IsLocalization.lift_eq hg x
  have hΘinj : Function.Injective Θ := by
    rw [IsLocalization.lift_injective_iff]
    intro x y
    constructor
    · intro h; rw [(IsFractionRing.injective S (FractionRing S)) h]
    · intro h
      have h' : e x = e y := by
        rw [hgx, hgx] at h
        ext
        · exact IsFractionRing.injective R (FractionRing R) (congrArg Prod.fst h)
        · exact IsFractionRing.injective S' (FractionRing S') (congrArg Prod.snd h)
      rw [e.injective h']

  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) c
  have hb' : e.symm ((b : R), (1 : S')) ∈ nonZeroDivisors S := by
    rw [mem_nonZeroDivisors_iff_right]
    intro z hz
    have hz' := congrArg e hz
    rw [map_mul, RingEquiv.apply_symm_apply, map_zero] at hz'
    have h1 : (e z).1 * b = 0 := congrArg Prod.fst hz'
    have h2 : (e z).2 * 1 = 0 := congrArg Prod.snd hz'
    rw [mul_right_mem_nonZeroDivisors_eq_zero_iff b.2] at h1
    rw [mul_one] at h2
    apply e.injective
    rw [map_zero]
    ext <;> simp [h1, h2]
  set c := IsLocalization.mk' (FractionRing R) a b with hcdef
  let b' : nonZeroDivisors S := ⟨_, hb'⟩
  let c' : FractionRing S := IsLocalization.mk' (FractionRing S) (e.symm (a, 0)) b'
  have hΘc : Θ c' = (c, 0) := by
    have hs := IsLocalization.mk'_spec (FractionRing S) (e.symm (a, 0)) b'
    have hs2 := congrArg Θ hs
    rw [map_mul, hΘ, hΘ] at hs2
    have hu := hg b'
    have hcs := IsLocalization.mk'_spec (FractionRing R) a b
    rw [← hu.mul_left_inj, hs2]
    rw [hgx, hgx]
    simp only [b', RingEquiv.apply_symm_apply, Prod.mk_mul_mk, map_zero, map_one, mul_one,
      zero_mul]
    rw [hcs]
  have hf : Function.Surjective ((RingHom.fst R S').comp e.toRingHom) := by
    intro r
    exact ⟨e.symm (r, 0), by simp⟩
  have hc' : IsIntegral S c' := by
    obtain ⟨p, hpm, hp⟩ := hc
    obtain ⟨q, hqmap, -, hqm⟩ := lifts_and_natDegree_eq_and_monic
      (f := (RingHom.fst R S').comp e.toRingHom) (p := p)
      ((lifts_iff_coeff_lifts p).mpr (fun n => hf _)) hpm
    refine ⟨X * q, monic_X.mul hqm, ?_⟩
    apply hΘinj
    rw [Polynomial.hom_eval₂, map_zero, hΘc, eval₂_mul, eval₂_X]
    have hfst : (RingHom.fst (FractionRing R) (FractionRing S')).comp
        (Θ.comp (algebraMap S (FractionRing S))) =
        (algebraMap R (FractionRing R)).comp ((RingHom.fst R S').comp e.toRingHom) := by
      ext x
      simp [hΘ, hgx]
    have h1 : (eval₂ (Θ.comp (algebraMap S (FractionRing S))) (c, 0) q).1 = 0 := by
      have := Polynomial.hom_eval₂ q (Θ.comp (algebraMap S (FractionRing S)))
        (RingHom.fst (FractionRing R) (FractionRing S')) (c, 0)
      simp only [RingHom.coe_fst] at this
      rw [this, hfst, ← eval₂_map, hqmap]
      exact hp
    ext
    · simp [h1]
    · simp
  obtain ⟨s, hs⟩ := hd c' hc'
  refine ⟨(e s).1, ?_⟩
  have h := congrArg (fun z => (Θ z).1) hs
  simp only [map_mul, hΘ, hΘc, hgx, Prod.fst_mul] at h
  exact h

end GlobalTheory
end

section

open IsLocalRing

namespace GlobalTheory

private lemma mem_colon_span_range_iff {B : Type*} [CommRing B] {P : Ideal B} {ι : Type*}
    (g : ι → B) (r : B) :
    r ∈ P.colon (Ideal.span (Set.range g) : Set B) ↔ ∀ i, r * g i ∈ P := by
  rw [Ideal.colon_span, Submodule.mem_colon]
  simp only [Set.forall_mem_range, smul_eq_mul]

theorem _root_.GlobalTheory.ideal_map_colon_eq_of_flat : ∀ {A R : Type} [CommRing A] [IsNoetherianRing A] [CommRing R]
    (φ : A →+* R), φ.Flat → ∀ I J : Ideal A, (I.colon J).map φ = (I.map φ).colon (J.map φ) := by
  intro A R _ _ _ φ hφ I J
  obtain ⟨n, a, hJ⟩ := Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian J)
  obtain ⟨m, b, hI⟩ := Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian I)
  replace hJ : Ideal.span (Set.range a) = J := hJ
  replace hI : Ideal.span (Set.range b) = I := hI
  subst hJ hI
  rw [Ideal.map_span φ (Set.range a), ← Set.range_comp]
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, mem_colon_span_range_iff]
    rw [mem_colon_span_range_iff] at hr
    intro i
    simpa [map_mul] using Ideal.mem_map_of_mem φ (hr i)
  · intro s hs
    rw [mem_colon_span_range_iff] at hs
    have hmapI : (Ideal.span (Set.range b)).map φ = Ideal.span (Set.range (φ ∘ b)) := by
      rw [Ideal.map_span, ← Set.range_comp]
    choose c hc using fun i => Ideal.mem_span_range_iff_exists_fun.mp (hmapI ▸ hs i)
    letI := φ.toAlgebra
    haveI : Module.Flat A R := hφ
    let f : (Fin n → A) →ₗ[A] A × (Fin n × Fin m → A) :=
      LinearMap.prod (Fintype.linearCombination A a)
        (LinearMap.pi fun p => -(b p.2) • LinearMap.proj p.1)
    let x : A × (Fin n × Fin m → A) →ₗ[A] R :=
      LinearMap.coprod (LinearMap.toSpanSingleton A R s)
        (Fintype.linearCombination A fun p => c p.1 p.2)
    have hxf : x ∘ₗ f = 0 := by
      refine LinearMap.ext fun v => ?_

      simp [f, x, Algebra.smul_def, Fintype.sum_prod_type, Fintype.linearCombination_apply,
      LinearMap.pi_apply, map_sum, Finset.sum_mul]
      rw [← sub_eq_add_neg, sub_eq_zero]
      refine Finset.sum_congr rfl fun i _ => ?_
      have e : ∑ j, algebraMap A R (b j) * algebraMap A R (v i) * c i j
          = algebraMap A R (v i) * ∑ j, c i j * (φ ∘ b) j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [RingHom.algebraMap_toAlgebra, Function.comp_apply]
        ring
      rw [e, hc i]
      simp only [RingHom.algebraMap_toAlgebra, Function.comp_apply]
      ring
    obtain ⟨k, g, y, hxy, hgf⟩ := Module.Flat.exists_factorization_of_comp_eq_zero_of_free hxf
    have hdec : ∀ w : A × (Fin n × Fin m → A), g w = w.1 • g (1, 0) +
        ∑ p, w.2 p • g (0, fun q => if p = q then 1 else 0) := by
      intro w
      have hw : w = w.1 • ((1 : A), (0 : Fin n × Fin m → A)) + ((0 : A), w.2) := by
        ext <;> simp
      conv_lhs => rw [hw]
      rw [map_add (f := _), map_smul]
      congr 1
      exact LinearMap.pi_apply_eq_sum_univ (g ∘ₗ LinearMap.inr A A (Fin n × Fin m → A)) w.2
    have key : ∀ q, g (1, 0) q ∈
        (Ideal.span (Set.range b)).colon (Ideal.span (Set.range a) : Set A) := by
      intro q
      rw [mem_colon_span_range_iff]
      intro i
      set w := f (fun j => if i = j then 1 else 0) with hw
      have hw1 : w.1 = a i := by simp [hw, f, Fintype.linearCombination_apply]
      have hw2 : ∀ p, w.2 p ∈ Ideal.span (Set.range b) := by
        intro p
        simp only [hw, f, LinearMap.prod_apply, Function.prod, LinearMap.pi_apply, LinearMap.smul_apply,
          LinearMap.proj_apply, smul_eq_mul]
        exact Ideal.mul_mem_right _ _ (neg_mem (Ideal.subset_span ⟨p.2, rfl⟩))
      have h0 := DFunLike.congr_fun (hdec w) q
      rw [show g w = 0 from LinearMap.congr_fun hgf _] at h0
      simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_add, Pi.add_apply, Finsupp.coe_smul,
        Pi.smul_apply, smul_eq_mul, Finsupp.finsetSum_apply] at h0
      have h1 : g (1, 0) q * a i = -∑ p, w.2 p * g (0, fun q => if p = q then 1 else 0) q := by
        rw [← hw1]
        linear_combination -h0
      rw [h1]
      exact neg_mem (Ideal.sum_mem _ fun p _ => Ideal.mul_mem_right _ _ (hw2 p))
    have hs' : s = x (1, 0) := by simp [x]

    rw [hs', hxy, LinearMap.comp_apply, ← Finsupp.univ_sum_single (g (1, 0)), map_sum]
    refine Ideal.sum_mem _ fun q _ => ?_
    rw [← Finsupp.smul_single_one, map_smul, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem φ (key q))

end GlobalTheory
end

section

universe u_1

namespace GlobalTheory.PowEqOneValuation

theorem val_eq_one_of_pow_eq_one {Ω Γ : Type*} [Field Ω] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation Ω Γ) {m : ℕ} (hm : m ≠ 0) {x : Ω} (hx : x ^ m = 1) : v x = 1 := by
  have h : v x ^ m = 1 := by rw [← map_pow, hx, map_one]
  exact (pow_eq_one_iff_left hm).1 h

theorem val_one_sub_pow_lt {Ω Γ : Type*} [Field Ω] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation Ω Γ) {u : Ω} (hu : v u = 1) (h : v (1 - u) < 1) (i : ℕ) :
    v (1 - u ^ i) < 1 := by
  induction i with
  | zero => simp
  | succ i ih =>
    have e : 1 - u ^ (i + 1) = (1 - u) + u * (1 - u ^ i) := by ring
    rw [e]
    refine v.map_add_lt h ?_
    rw [map_mul, hu, one_mul]
    exact ih

theorem eq_of_pow_eq_one_of_valuation_sub_lt_one {Ω : Type u_1} [inst : Field Ω]
    (A : ValuationSubring Ω) (m : ℕ) {ζ ζ' : Ω} (h1 : ζ ^ m = 1) (h2 : ζ' ^ m = 1)
    (hm : ¬ A.valuation (m : Ω) < 1) (h : A.valuation (ζ - ζ') < 1) : ζ = ζ' := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    apply hm
    simp
  have v1 := val_eq_one_of_pow_eq_one A.valuation hm0 h1
  have v2 := val_eq_one_of_pow_eq_one A.valuation hm0 h2
  have hz : ζ ≠ 0 := by
    rintro rfl
    simp at v1
  by_contra hne
  set u : Ω := ζ' / ζ with hu
  have hu1 : u ≠ 1 := by
    intro e
    apply hne
    rw [hu, div_eq_one_iff_eq hz] at e
    exact e.symm
  have hum : u ^ m = 1 := by rw [hu, div_pow, h1, h2, div_one]
  have vu : A.valuation u = 1 := by rw [hu, map_div₀, v1, v2, div_one]
  have v1u : A.valuation (1 - u) < 1 := by
    have e : 1 - u = (ζ - ζ') / ζ := by rw [hu, sub_div, div_self hz]
    rw [e, map_div₀, v1, div_one]
    exact h
  have hs : ∑ i ∈ Finset.range m, u ^ i = 0 := by
    have g := geom_sum_mul u m
    rw [hum, sub_self] at g
    exact (mul_eq_zero.1 g).resolve_right (sub_ne_zero.2 hu1)
  have hm' : (m : Ω) = ∑ i ∈ Finset.range m, (1 - u ^ i) := by
    rw [Finset.sum_sub_distrib, hs]
    simp
  apply hm
  rw [hm']
  exact A.valuation.map_sum_lt one_ne_zero fun i _ => val_one_sub_pow_lt A.valuation vu v1u i

end GlobalTheory.PowEqOneValuation
end

section

namespace GlobalTheory.EntriesExpBound

theorem exists_nat_le_exp (x : WithZero (Multiplicative ℤ)) :
    ∃ k : ℕ, x ≤ WithZero.exp (k : ℤ) := by
  by_cases hx : x = 0
  · exact ⟨0, by rw [hx]; exact zero_le'⟩
  · refine ⟨(WithZero.log x).toNat, ?_⟩
    calc x = WithZero.exp (WithZero.log x) := (WithZero.exp_log hx).symm
      _ ≤ _ := WithZero.exp_le_exp.mpr (Int.self_le_toNat _)

theorem exists_entries_le_exp {K : Type} [inst : Field K]
    [inst_1 : Valued K (WithZero (Multiplicative ℤ))] {m : ℕ} (A : Matrix (Fin m) (Fin m) K) :
    ∃ (k : ℕ), ∀ (r s : Fin m),
      (Valued.v : K → WithZero (Multiplicative ℤ)) (A r s) ≤ WithZero.exp (↑k : ℤ) := by
  choose f hf using fun p : Fin m × Fin m =>
    exists_nat_le_exp ((Valued.v : K → WithZero (Multiplicative ℤ)) (A p.1 p.2))
  refine ⟨Finset.univ.sup f, fun r s => (hf (r, s)).trans ?_⟩
  exact WithZero.exp_le_exp.mpr
    (Int.ofNat_le.mpr (Finset.le_sup (f := f) (Finset.mem_univ (r, s))))

end GlobalTheory.EntriesExpBound
end
