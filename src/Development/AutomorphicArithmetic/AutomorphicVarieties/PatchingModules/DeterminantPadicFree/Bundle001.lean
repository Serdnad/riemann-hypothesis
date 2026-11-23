module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
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
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Ideal
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.RingTheory.Filtration

@[expose] public section

section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem adicCont_iff_eventually_sub_mem_pow {Γ R : Type} [TopologicalSpace Γ] [CommRing R] (I : Ideal R) (f : Γ → R) :
    UpperTheory.V.Alg.AdicCont I f ↔ ∀ (N : ℕ) (x : Γ), ∀ᶠ y in nhds x, f y - f x ∈ I ^ N := by
  unfold UpperTheory.V.Alg.AdicCont
  simp only [IsLocallyConstant.iff_eventually_eq, Ideal.Quotient.eq]

private theorem eventually_mul_sub_mem_pow_of_eventually_sub_mem {Γ R : Type} [TopologicalSpace Γ] [CommRing R] (I : Ideal R) (f g : Γ → R)
    (hf : ∀ (N : ℕ) (x : Γ), ∀ᶠ y in nhds x, f y - f x ∈ I ^ N)
    (hg : ∀ (N : ℕ) (x : Γ), ∀ᶠ y in nhds x, g y - g x ∈ I ^ N) :
    ∀ (N : ℕ) (x : Γ), ∀ᶠ y in nhds x, f y * g y - f x * g x ∈ I ^ N := by
  intro N x
  filter_upwards [hf N x, hg N x] with y h1 h2
  have e : f y * g y - f x * g x = f y * (g y - g x) + (f y - f x) * g x := by ring
  rw [e]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h2) (Ideal.mul_mem_right _ _ h1)

private theorem eventually_sum_sub_mem_pow_of_eventually_sub_mem {Γ R ι : Type} [TopologicalSpace Γ] [CommRing R] [Fintype ι] (I : Ideal R)
    (f : ι → Γ → R) (hf : ∀ i (N : ℕ) (x : Γ), ∀ᶠ y in nhds x, f i y - f i x ∈ I ^ N) :
    ∀ (N : ℕ) (x : Γ), ∀ᶠ y in nhds x, (∑ i, f i y) - ∑ i, f i x ∈ I ^ N := by
  intro N x
  filter_upwards [Filter.eventually_all.2 (fun i => hf i N x)] with y hy
  rw [← Finset.sum_sub_distrib]
  exact Ideal.sum_mem _ (fun i _ => hy i)

private theorem eventually_sub_mem_maxIdeal_pow_of_const_mul {Γ K' : Type} [TopologicalSpace Γ] [Field K'] (c : PowerSeries K') (hc : c ≠ 0)
    (f : Γ → PowerSeries K')
    (h : ∀ (N : ℕ) (x : Γ), ∀ᶠ y in nhds x, c * f y - c * f x ∈ maximalIdeal (PowerSeries K') ^ N) :
    ∀ (N : ℕ) (x : Γ), ∀ᶠ y in nhds x, f y - f x ∈ maximalIdeal (PowerSeries K') ^ N := by
  intro N x
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 (fun h0 => hc (PowerSeries.order_eq_top.1 h0))
  filter_upwards [h (N + k) x] with y hy
  rw [PowerSeries.maximalIdeal_eq_span_X, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hy ⊢
  rw [← mul_sub, PowerSeries.X_pow_dvd_iff] at hy
  rw [PowerSeries.X_pow_dvd_iff]
  intro m hm
  have h1 : ((N + k : ℕ) : ℕ∞) ≤ (c * (f y - f x)).order :=
    PowerSeries.le_order _ _ (fun i hi => hy i (by exact_mod_cast hi))
  rw [PowerSeries.order_mul, ← hk] at h1
  apply PowerSeries.coeff_of_lt_order
  by_cases h3 : (f y - f x).order = ⊤
  · rw [h3]
    exact ENat.coe_lt_top m
  · obtain ⟨r, hr⟩ := ENat.ne_top_iff_exists.1 h3
    rw [← hr] at h1 ⊢
    have h4 : N + k ≤ k + r := by exact_mod_cast h1
    exact_mod_cast (by omega : m < r)

theorem UpperTheory.V.Pa.Det.conjCont :
    ∀ {K K' G : Type} [Field K] [Field K'] [TopologicalSpace G] {n : ℕ} (j : PowerSeries K →+* PowerSeries K') (ρ : G → Matrix (Fin n) (Fin n) (PowerSeries K)) (Q : GL (Fin n) (FractionRing (PowerSeries K'))) (ρ' : G → Matrix (Fin n) (Fin n) (PowerSeries K')), IsLocalHom j → (∀ a b, AdicCont (maximalIdeal (PowerSeries K)) fun g => ρ g a b) → (∀ g, (ρ g).map ((algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))).comp j) * (Q : Matrix (Fin n) (Fin n) (FractionRing (PowerSeries K'))) = (Q : Matrix (Fin n) (Fin n) (FractionRing (PowerSeries K'))) * (ρ' g).map (algebraMap (PowerSeries K') (FractionRing (PowerSeries K')))) → ∀ a b, AdicCont (maximalIdeal (PowerSeries K')) fun g => ρ' g a b := by
  intro K K' G _ _ _ n j ρ Q ρ' hj hρ hQ a b
  have hX : PowerSeries.X ∈ maximalIdeal (PowerSeries K) := by
    rw [PowerSeries.maximalIdeal_eq_span_X]
    exact Ideal.mem_span_singleton_self _
  have hjX : j PowerSeries.X ∈ maximalIdeal (PowerSeries K') := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact (IsLocalRing.mem_maximalIdeal _).1 hX (isUnit_of_map_unit j _ hu)
  have hjr : ∀ k l (N : ℕ) (x : G), ∀ᶠ y in nhds x,
      j (ρ y k l) - j (ρ x k l) ∈ maximalIdeal (PowerSeries K') ^ N := by
    intro k l N x
    filter_upwards [(adicCont_iff_eventually_sub_mem_pow _ _).1 (hρ k l) N x] with y hy
    rw [PowerSeries.maximalIdeal_eq_span_X, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hy
    obtain ⟨t, ht⟩ := hy
    rw [← map_sub, ht, map_mul, map_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hjX N)
  obtain ⟨b1, hb1⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (PowerSeries K'))
    (fun p : Fin n × Fin n => (↑(Q⁻¹) : Matrix (Fin n) (Fin n) (FractionRing (PowerSeries K'))) p.1 p.2)
  obtain ⟨b2, hb2⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (PowerSeries K'))
    (fun p : Fin n × Fin n => (↑Q : Matrix (Fin n) (Fin n) (FractionRing (PowerSeries K'))) p.1 p.2)
  choose P hP using fun p => RingHom.mem_rangeS.1 (hb1 p)
  choose R hR using fun p => RingHom.mem_rangeS.1 (hb2 p)
  have hconj : ∀ g, (ρ' g).map (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) =
      (↑(Q⁻¹) : Matrix (Fin n) (Fin n) (FractionRing (PowerSeries K'))) *
        (ρ g).map ((algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))).comp j) *
        (↑Q : Matrix (Fin n) (Fin n) (FractionRing (PowerSeries K'))) := by
    intro g
    rw [Matrix.mul_assoc, hQ g, ← Matrix.mul_assoc, Q.inv_mul, Matrix.one_mul]
  have key : ∀ g, ((b1 : PowerSeries K') * (b2 : PowerSeries K')) * ρ' g a b =
      ∑ l, ∑ k, P (a, k) * j (ρ g k l) * R (l, b) := by
    intro g
    apply IsFractionRing.injective (PowerSeries K') (FractionRing (PowerSeries K'))
    have e := congrFun (congrFun (hconj g) a) b
    simp only [Matrix.map_apply, Matrix.mul_apply, RingHom.comp_apply] at e
    rw [map_mul, e]

    simp only [map_sum, map_mul, hP, hR, Algebra.smul_def, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [adicCont_iff_eventually_sub_mem_pow]
  refine eventually_sub_mem_maxIdeal_pow_of_const_mul ((b1 : PowerSeries K') * (b2 : PowerSeries K'))
    (mul_ne_zero (nonZeroDivisors.coe_ne_zero b1) (nonZeroDivisors.coe_ne_zero b2)) _ ?_
  simp only [key]
  refine eventually_sum_sub_mem_pow_of_eventually_sub_mem _ (fun l y => ∑ k, P (a, k) * j (ρ y k l) * R (l, b)) ?_
  intro l
  refine eventually_sum_sub_mem_pow_of_eventually_sub_mem _ (fun k y => P (a, k) * j (ρ y k l) * R (l, b)) ?_
  intro k
  refine eventually_mul_sub_mem_pow_of_eventually_sub_mem _ (fun y => P (a, k) * j (ρ y k l)) (fun _ => R (l, b)) ?_ (fun N x => by simp)
  exact eventually_mul_sub_mem_pow_of_eventually_sub_mem _ (fun _ => P (a, k)) (fun y => j (ρ y k l)) (fun N x => by simp) (hjr k l)
end

section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.Det.phiSub :
    ∀ (l : ℕ) {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H : Subgroup G),
      IsOpen (H : Set G) → PhiCond (Γ := G) l → PhiCond (Γ := H) l := by
  intro l G _ _ _ H hH hG
  unfold PhiCond at *
  intro K hK
  have hK' : IsOpen ((K.map H.subtype : Subgroup G) : Set G) := by
    rw [Subgroup.coe_map]
    exact hH.isOpenMap_subtype_val _ hK
  haveI := hG (K.map H.subtype) hK'
  let e := Subgroup.equivMapOfInjective K H.subtype H.subtype_injective
  have he : ∀ y : K.map H.subtype, (((e.symm y : K) : H) : G) = (y : G) := fun y =>
    congrArg Subtype.val (e.apply_symm_apply y)
  have hc : Continuous fun y : K.map H.subtype => (e.symm y : K) := by
    apply continuous_induced_rng.2
    apply continuous_induced_rng.2
    exact continuous_subtype_val.congr fun y => (he y).symm
  refine Finite.of_injective
    (β := {ψ : K.map H.subtype →* Multiplicative (ZMod l) // IsOpen (ψ.ker : Set (K.map H.subtype))})
    (fun φ => ⟨φ.1.comp e.symm.toMonoidHom, by
      show IsOpen ((fun y => (e.symm y : K)) ⁻¹' (φ.1.ker : Set K))
      exact φ.2.preimage hc⟩) ?_
  intro φ ψ h
  apply Subtype.ext
  ext k
  have h' := congrArg (fun χ : {ψ : K.map H.subtype →* Multiplicative (ZMod l) //
    IsOpen (ψ.ker : Set (K.map H.subtype))} => χ.1 (e k)) h
  simpa using h'
end

section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem eq_zero_of_forall_hom_zmod_eq_zero_of_module_zmod {l : ℕ} [Fact l.Prime] {M : Type} [AddCommGroup M] [Module (ZMod l) M] (v : M)
    (hv : ∀ f : M →+ ZMod l, f v = 0) : v = 0 := by
  rw [← Module.forall_dual_apply_eq_zero_iff (ZMod l)]
  intro f
  exact hv (LinearMap.toAddMonoidHom f)

theorem UpperTheory.V.Pa.Det.locallyConstant_cocycles_finite_of_phi :
    ∀ (l : ℕ) [Fact l.Prime] {G M : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] [AddCommGroup M] [Finite M] (ρ : G →* AddMonoid.End M), PhiCond G l → (∀ m : M, l • m = 0) → (∀ m, IsLocallyConstant fun g => ρ g m) → {z : G → M | IsLocallyConstant z ∧ ∀ g h, z (g * h) = z g + ρ g (z h)}.Finite := by
  intro l _ G M _ _ _ _ _ _ _ ρ hΦ hl hc
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  set S := {z : G → M | IsLocallyConstant z ∧ ∀ g h, z (g * h) = z g + ρ g (z h)} with hS
  have hker : IsOpen (ρ.ker : Set G) := by
    have he : (ρ.ker : Set G) = ⋂ m, {g | ρ g m = m} := by
      ext g
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_setOf_eq]
      constructor
      · intro h m
        rw [h]
        rfl
      · intro h
        ext m
        exact h m
    rw [he]
    exact isOpen_iInter_of_finite fun m => (hc m).isOpen_fiber m
  haveI : Finite (G ⧸ ρ.ker) := Subgroup.quotient_finite_of_isOpen _ hker
  haveI := hΦ ρ.ker hker
  haveI : Finite (M →+ ZMod l) :=
    Finite.of_injective (fun f : M →+ ZMod l => (⇑f : M → ZMod l))
      (fun a b hab => AddMonoidHom.ext (congrFun hab))
  have h1 : ∀ z ∈ S, z 1 = 0 := by
    intro z hz
    have h11 : z 1 = z 1 + z 1 := by
      have := hz.2 1 1
      rw [one_mul, map_one] at this
      exact this
    exact add_left_cancel (h11.symm.trans (add_zero _).symm)
  have hH : ∀ z ∈ S, ∀ a b : G, a ∈ ρ.ker → z (a * b) = z a + z b := by
    intro z hz a b ha
    rw [hz.2, MonoidHom.mem_ker.mp ha]
    rfl
  let φ : ∀ z ∈ S, (M →+ ZMod l) →
      {φ : ρ.ker →* Multiplicative (ZMod l) // IsOpen (φ.ker : Set ρ.ker)} := fun z hz f =>
    ⟨{ toFun := fun h => Multiplicative.ofAdd (f (z h))
       map_one' := by simp [h1 z hz]
       map_mul' := fun a b => by simp [hH z hz a b a.2, ofAdd_add] },
     by
       have hlc : IsLocallyConstant (fun h : ρ.ker => Multiplicative.ofAdd (f (z h))) :=
         (hz.1.comp_continuous continuous_subtype_val).comp _
       exact hlc.isOpen_fiber 1⟩
  let F : S → ((G ⧸ ρ.ker) → M) × ((M →+ ZMod l) →
      {φ : ρ.ker →* Multiplicative (ZMod l) // IsOpen (φ.ker : Set ρ.ker)}) :=
    fun z => (fun q => z.1 (Quotient.out q), φ z.1 z.2)
  have hinj : Function.Injective F := by
    rintro ⟨z, hz⟩ ⟨z', hz'⟩ hzz
    have hq : (fun q : G ⧸ ρ.ker => z (Quotient.out q)) = fun q => z' (Quotient.out q) := congrArg Prod.fst hzz
    have hf : φ z hz = φ z' hz' := congrArg Prod.snd hzz
    have hHeq : ∀ h ∈ ρ.ker, z h = z' h := by
      intro h hh
      rw [← sub_eq_zero]
      apply @eq_zero_of_forall_hom_zmod_eq_zero_of_module_zmod l _ M _ (AddCommGroup.zmodModule hl)
      intro f
      have hx := congrArg (fun p => (p.1 ⟨h, hh⟩ : Multiplicative (ZMod l))) (congrFun hf f)
      change Multiplicative.ofAdd (f (z h)) = Multiplicative.ofAdd (f (z' h)) at hx
      rw [map_sub, sub_eq_zero]
      exact Multiplicative.ofAdd.injective hx
    apply Subtype.ext
    funext g
    show z g = z' g
    obtain ⟨h0, hh0⟩ := QuotientGroup.mk_out_eq_mul ρ.ker g
    have hg : g = Quotient.out (g : G ⧸ ρ.ker) * (h0 : G)⁻¹ := by
      rw [hh0, mul_inv_cancel_right]
    have hr := congrFun hq (g : G ⧸ ρ.ker)
    rw [hg, hz.2, hz'.2, hr, hHeq _ (inv_mem h0.2)]
  exact Set.finite_coe_iff.mp (Finite.of_injective F hinj)
end

section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem char_of_padic {l : ℕ} [Fact l.Prime] {K : Type} [Field K] [Finite K] (f : ℤ_[l] →+* K) :
    (l : K) = 0 := by
  obtain ⟨p, hchar⟩ := CharP.exists K
  have hp : p.Prime := CharP.char_is_prime K p
  have hpl : p = l := by
    by_contra hne
    have hunit : IsUnit (p : ℤ_[l]) := by
      by_contra hnu
      have hlt : ‖((p : ℤ) : ℤ_[l])‖ < 1 := by
        rw [Int.cast_natCast]
        exact PadicInt.mem_nonunits.mp hnu
      rw [PadicInt.norm_int_lt_one_iff_dvd, Int.natCast_dvd_natCast] at hlt
      exact hne ((Nat.prime_dvd_prime_iff_eq (Fact.out) hp).mp hlt).symm
    have h := hunit.map f
    rw [map_natCast, CharP.cast_eq_zero] at h
    exact not_isUnit_zero h
  subst hpl
  exact CharP.cast_eq_zero K p

private theorem closed_of_comb {A G ι : Type} [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
    [TopologicalSpace G] [Fintype ι] (ρ : ι → G → A) (hρ : ∀ a, AdicCont (maximalIdeal A) (ρ a))
    (q : ι → FractionRing A) (ψ : G → A)
    (h : ∀ g, algebraMap A (FractionRing A) (ψ g) = ∑ a, q a * algebraMap A (FractionRing A) (ρ a g)) :
    IsClosed {g | ψ g = 1} := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors A) Finset.univ q
  choose c hc using fun a => hb a (Finset.mem_univ a)
  have key : ∀ g, ψ g = 1 ↔ ∑ a, c a * ρ a g - (b : A) = 0 := by
    intro g
    have h1 : algebraMap A (FractionRing A) ((b : A) * ψ g) =
        algebraMap A (FractionRing A) (∑ a, c a * ρ a g) := by

      rw [map_mul, h g, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_mul, hc a, Algebra.smul_def, mul_assoc]
    have h2 := IsFractionRing.injective A (FractionRing A) h1
    have hb0 : (b : A) ≠ 0 := nonZeroDivisors.coe_ne_zero b
    rw [sub_eq_zero, ← h2]
    constructor
    · intro h
      rw [h, mul_one]
    · intro h
      exact mul_left_cancel₀ hb0 (h.trans (mul_one _).symm)
  have hset : {g | ψ g = 1} =
      ⋂ N : ℕ, {g | Ideal.Quotient.mk (maximalIdeal A ^ N) (∑ a, c a * ρ a g - (b : A)) = 0} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Ideal.Quotient.eq_zero_iff_mem, key]
    constructor
    · intro h N
      rw [h]
      exact Ideal.zero_mem _
    · intro h
      have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal A) (maximalIdeal.isMaximal A).ne_top
      have hmem : ∑ a, c a * ρ a g - (b : A) ∈ ⨅ i, maximalIdeal A ^ i := Submodule.mem_iInf _ |>.mpr h
      rw [hbot] at hmem
      exact (Submodule.mem_bot A).mp hmem
  rw [hset]
  refine isClosed_iInter fun N => ?_
  have hF : IsLocallyConstant (fun g => fun a => Ideal.Quotient.mk (maximalIdeal A ^ N) (ρ a g)) := by
    rw [IsLocallyConstant.iff_isOpen_fiber]
    intro y
    have hy : (fun g => fun a => Ideal.Quotient.mk (maximalIdeal A ^ N) (ρ a g)) ⁻¹' {y} =
        ⋂ a, {g | Ideal.Quotient.mk (maximalIdeal A ^ N) (ρ a g) = y a} := by
      ext g
      simp [funext_iff]
    rw [hy]
    exact isOpen_iInter_of_finite fun a => (hρ a N).isOpen_fiber (y a)
  have hG := (hF.comp (fun w => ∑ a, Ideal.Quotient.mk (maximalIdeal A ^ N) (c a) * w a -
    Ideal.Quotient.mk (maximalIdeal A ^ N) (b : A))).isClopen_fiber 0
  convert hG.isClosed using 1
  ext g

  simp [map_sub, map_sum, map_mul]

theorem UpperTheory.V.Pa.Det.psiMu :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ} {r : Resid F O n} (x : Point r) (v : F.Vl) (i : Fin n) (g : F.Gv v), g ∈ F.mu v → x.ψ v i g = 1 := by
  intro l _ F O _ _ _ n r x v i g hg
  have hl : (l : x.K) = 0 := char_of_padic ((algebraMap O x.K).comp (algebraMap ℤ_[l] O))
  haveI : CharP x.K l := (CharP.charP_iff_prime_eq_zero Fact.out).mpr hl
  haveI : CharP (PowerSeries x.K) l :=
    charP_of_injective_algebraMap (algebraMap x.K (PowerSeries x.K)).injective l
  obtain ⟨P, hP⟩ := x.flag v
  have hclosed : IsClosed {s : F.Gv v | ((x.ψ v i s : (PowerSeries x.K)ˣ) : PowerSeries x.K) = 1} := by
    refine closed_of_comb (ι := Fin n × Fin n) (fun ab s => (mat x.ρ) (F.φ v s) ab.1 ab.2) ?_
      (fun ab => (P : Matrix (Fin n) (Fin n) _) i ab.1 * ((P⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) ab.2 i)
      _ ?_
    · intro ab N
      exact (x.cont ab.1 ab.2 N).comp_continuous (F.φ_cont v)
    · intro s
      have hs := (hP s).2 i
      simp only [pushCh, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe] at hs
      rw [← hs]
      simp only [pushRep, mat, MonoidHom.comp_apply, Units.coeHom_apply, Units.val_mul, Matrix.mul_apply,
        Finset.sum_mul, Fintype.sum_prod_type, Matrix.GeneralLinearGroup.map_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
  have hker : (commutator (F.Gv v)).topologicalClosure ≤ (x.ψ v i).ker := by
    apply Subgroup.topologicalClosure_minimal
    · exact Abelianization.commutator_subset_ker (x.ψ v i)
    · convert hclosed using 1
      ext s
      rw [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_setOf_eq, Units.val_eq_one]
  obtain ⟨k, hk⟩ := CommGroup.mem_primaryComponent.mp (Subgroup.mem_comap.mp hg)
  have hgk : g ^ l ^ k ∈ (commutator (F.Gv v)).topologicalClosure := by
    rw [← QuotientGroup.eq_one_iff]
    simpa using hk
  have h1 : x.ψ v i g ^ l ^ k = 1 := by
    rw [← map_pow]
    exact hker hgk
  have h2 : ((x.ψ v i g : PowerSeries x.K) - 1) ^ l ^ k = 0 := by
    rw [sub_pow_char_pow, one_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, sub_self]
  have h3 : (x.ψ v i g : PowerSeries x.K) - 1 = 0 := pow_eq_zero_iff (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) |>.mp h2
  exact Units.ext (sub_eq_zero.mp h3)
end
