module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import ReciprocityTheory.GaloisValuations.Global
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
public import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAlg
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow

@[expose] public section

section

open Formalism.BasicNotions Formalism.L2 NumberField IsDedekindDomain Module

namespace GlobalTheory

theorem projection_span_extend_scalars
    (K : Type) [Field K] [NumberField K] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (e : K →+* FractionRing O) (V V' : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V] [AddCommGroup V'] [Module (FractionRing O) V']
    [Module O V'] [IsScalarTower O (FractionRing O) V'] (iV : V →ₛₗ[e] V') (ι : Type) (b : Basis ι K V) :
    LinearIndependent (FractionRing O) (fun a => iV (b a)) →
    (∀ a : 𝓞 K, e (a : K) ∈ (algebraMap O (FractionRing O)).range) →
    ∀ (A : Submodule (𝓞 K) V) (U U' : Submodule K V), IsCompl U U' →
    Submodule.span O (iV '' ((U.restrictScalars (𝓞 K) ⊓ (A ⊔ U'.restrictScalars (𝓞 K)) :
        Submodule (𝓞 K) V) : Set V)) =
      (Submodule.span (FractionRing O) (iV '' (U : Set V))).restrictScalars O ⊓
        (Submodule.span O (iV '' (A : Set V)) ⊔
          (Submodule.span (FractionRing O) (iV '' (U' : Set V))).restrictScalars O) := by
  intro hli _ A U U' hUU'
  set F := FractionRing O

  let p : V →ₗ[K] V := U.subtype ∘ₗ U.projectionOnto U' hUU'
  have hpU : ∀ u ∈ U, p u = u := fun u hu => by
    have h := Submodule.projectionOnto_apply_left hUU' ⟨u, hu⟩
    show ((U.projectionOnto U' hUU') ((⟨u, hu⟩ : U) : V) : V) = u
    rw [h]
  have hpU' : ∀ u ∈ U', p u = 0 := fun u hu => by
    have h := Submodule.projectionOnto_apply_right hUU' ⟨u, hu⟩
    show ((U.projectionOnto U' hUU') ((⟨u, hu⟩ : U') : V) : V) = 0
    rw [h]; rfl
  have hpmem : ∀ v, p v ∈ U := fun v => by simp [p]
  have hdec : ∀ v, ∃ u ∈ U, ∃ u' ∈ U', u + u' = v := fun v => by
    have : v ∈ U ⊔ U' := by rw [hUU'.sup_eq_top]; trivial
    exact Submodule.mem_sup.mp this
  have hpdiff : ∀ v, p v - v ∈ U' := fun v => by
    obtain ⟨u, hu, u', hu', rfl⟩ := hdec v
    rw [map_add (f := _), hpU u hu, hpU' u' hu', add_zero]
    simpa using U'.neg_mem hu'

  let W : Submodule F V' := Submodule.span F (Set.range fun a => iV (b a))
  let f : W →ₗ[F] V' := (Basis.span hli).constr F (fun a => iV (p (b a)))
  obtain ⟨q, hq⟩ := LinearMap.exists_extend f
  have hqi : ∀ v, q (iV v) = iV (p v) := by
    have : (q.comp iV : V →ₛₗ[e] V') = iV.comp p := by
      refine b.ext fun a => ?_
      have hmem : iV (b a) ∈ W := Submodule.subset_span ⟨a, rfl⟩
      have h1 : q (iV (b a)) = f ⟨iV (b a), hmem⟩ := by
        rw [← hq]; rfl
      have h2 : (⟨iV (b a), hmem⟩ : W) = Basis.span hli a := by
        rw [Basis.span_apply]
      simp only [LinearMap.comp_apply]
      rw [h1, h2, Basis.constr_basis]
    intro v
    exact congrArg (fun g => g v) this
  have hqU : ∀ x ∈ Submodule.span F (iV '' (U : Set V)), q x = x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨u, hu, rfl⟩ := hy
      rw [hqi, hpU u hu]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), hx, hy]
    | smul c x _ hx => rw [map_smul, hx]
  have hqU' : ∀ x ∈ Submodule.span F (iV '' (U' : Set V)), q x = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨u, hu, rfl⟩ := hy
      rw [hqi, hpU' u hu, map_zero]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, add_zero]
    | smul c x _ hx => rw [map_smul, hx, smul_zero]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_inf, Submodule.restrictScalars_mem] at hw
    obtain ⟨hwU, hwA⟩ := hw
    obtain ⟨a, ha, u', hu', rfl⟩ := Submodule.mem_sup.mp hwA
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · exact Submodule.subset_span ⟨_, hwU, rfl⟩
    · rw [map_add (f := _)]
      refine Submodule.add_mem_sup (Submodule.subset_span ⟨a, ha, rfl⟩) ?_
      exact Submodule.subset_span ⟨u', hu', rfl⟩
  · intro x hx
    obtain ⟨hxU, hxs⟩ := Submodule.mem_inf.mp hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hxs
    have hxq : q (y + z) = y + z := hqU _ hxU
    rw [map_add (f := _), hqU' z hz, add_zero] at hxq
    rw [← hxq]
    have hmap : q y ∈ Submodule.map (q.restrictScalars O) (Submodule.span O (iV '' (A : Set V))) :=
      ⟨y, hy, rfl⟩
    rw [Submodule.map_span] at hmap
    refine Submodule.span_mono ?_ hmap
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨p a, ?_, (hqi a).symm⟩
    simp only [SetLike.mem_coe, Submodule.mem_inf, Submodule.restrictScalars_mem]
    refine ⟨hpmem a, ?_⟩
    have : p a = a + (p a - a) := by abel
    rw [this]
    exact Submodule.add_mem_sup ha (hpdiff a)

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.Per


open PowerSeries in
theorem exists_div_X_sub_C {O : Type} [CommRing O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (x : O) (hx : ¬ IsUnit x) (a : PowerSeries O) :
    ∃ (b : PowerSeries O) (c : O), a = (PowerSeries.X - PowerSeries.C x) * b + PowerSeries.C c := by
  have hres : (PowerSeries.X - PowerSeries.C x : PowerSeries O).map (IsLocalRing.residue O) =
      PowerSeries.X := by
    have hx0 : IsLocalRing.residue O x = 0 :=
      (IsLocalRing.residue_eq_zero_iff x).2 ((IsLocalRing.mem_maximalIdeal x).2 hx)
    rw [map_sub, PowerSeries.map_X, PowerSeries.map_C, hx0, map_zero, sub_zero]
  have hne : (PowerSeries.X - PowerSeries.C x : PowerSeries O).map (IsLocalRing.residue O) ≠ 0 := by
    rw [hres]; exact PowerSeries.X_ne_zero
  obtain ⟨q, r, hdeg, heq⟩ := a.exists_isWeierstrassDivision hne
  change r.degree < ((PowerSeries.X - PowerSeries.C x : PowerSeries O).map
      (IsLocalRing.residue O)).order.toNat at hdeg
  rw [hres, PowerSeries.order_X] at hdeg
  have hr : r = Polynomial.C (r.coeff 0) := by
    have h1 : r.degree < 0 + 1 := by simpa using hdeg
    exact Polynomial.eq_C_of_degree_le_zero (Order.le_of_lt_succ h1)
  refine ⟨q, r.coeff 0, ?_⟩
  rw [heq, hr, Polynomial.coe_C, Polynomial.coeff_C_zero]

section
variable {O : Type} [CommRing O] [IsLocalRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {L : Type} [Field L] [Algebra O L]

theorem ev_C (ev : PowerSeries O →ₐ[O] PowerSeries L) (c : O) :
    ev (PowerSeries.C c) = PowerSeries.C (algebraMap O L c) := by
  simpa [PowerSeries.algebraMap_apply] using ev.commutes c

theorem X_dvd_ev_iff (hinj : Function.Injective (algebraMap O L)) {x : O} (hx : ¬ IsUnit x)
    (ev : PowerSeries O →ₐ[O] PowerSeries L) {w : PowerSeries L}
    (hev : ev PowerSeries.X = PowerSeries.C (algebraMap O L x) + PowerSeries.X * w)
    (a : PowerSeries O) :
    PowerSeries.X ∣ ev a ↔ (PowerSeries.X - PowerSeries.C x) ∣ a := by
  have hXev : ev (PowerSeries.X - PowerSeries.C x) = PowerSeries.X * w := by
    rw [map_sub, hev, ev_C]; ring
  constructor
  · intro h
    obtain ⟨b, c, rfl⟩ := exists_div_X_sub_C x hx a
    rw [map_add (f := _), map_mul, hXev, ev_C] at h
    have h2 : PowerSeries.X ∣ PowerSeries.C (algebraMap O L c) :=
      (dvd_add_right (dvd_mul_of_dvd_left (dvd_mul_right _ _) _)).1 h
    rw [PowerSeries.X_dvd_iff, PowerSeries.constantCoeff_C] at h2
    have hc : c = 0 := hinj (by rw [h2, map_zero])
    subst hc
    rw [map_zero, add_zero]
    exact dvd_mul_right _ _
  · rintro ⟨b, rfl⟩
    rw [map_mul, hXev, mul_assoc]
    exact dvd_mul_right _ _

theorem X_pow_dvd_ev_iff (hinj : Function.Injective (algebraMap O L)) {x : O} (hx : ¬ IsUnit x)
    (ev : PowerSeries O →ₐ[O] PowerSeries L) {w : PowerSeries L} (hw : IsUnit w)
    (hev : ev PowerSeries.X = PowerSeries.C (algebraMap O L x) + PowerSeries.X * w)
    (m : ℕ) (a : PowerSeries O) :
    PowerSeries.X ^ m ∣ ev a ↔ (PowerSeries.X - PowerSeries.C x) ^ m ∣ a := by
  have hXev : ev (PowerSeries.X - PowerSeries.C x) = PowerSeries.X * w := by
    rw [map_sub, hev, ev_C]; ring
  induction m generalizing a with
  | zero => simp
  | succ m ih =>
    constructor
    · intro h
      have h1 : PowerSeries.X ∣ ev a := (dvd_pow_self _ (Nat.succ_ne_zero m)).trans h
      obtain ⟨b, rfl⟩ := (X_dvd_ev_iff hinj hx ev hev a).1 h1
      rw [map_mul, hXev, pow_succ', mul_assoc] at h
      have h2 : PowerSeries.X ^ m ∣ w * ev b := (mul_dvd_mul_iff_left PowerSeries.X_ne_zero).1 h
      have h3 : PowerSeries.X ^ m ∣ ev b := (IsUnit.dvd_mul_left hw).1 h2
      rw [pow_succ']
      exact mul_dvd_mul_left _ ((ih b).1 h3)
    · rintro ⟨b, rfl⟩
      rw [pow_succ' (PowerSeries.X - PowerSeries.C x), mul_assoc, map_mul, hXev,
        pow_succ' (PowerSeries.X : PowerSeries L), mul_assoc]
      exact mul_dvd_mul_left _ (dvd_mul_of_dvd_right ((ih _).2 (dvd_mul_right _ _)) _)

theorem prime_X_sub_C (hinj : Function.Injective (algebraMap O L)) {x : O} (hx : ¬ IsUnit x)
    (ev : PowerSeries O →ₐ[O] PowerSeries L) {w : PowerSeries L}
    (hev : ev PowerSeries.X = PowerSeries.C (algebraMap O L x) + PowerSeries.X * w) :
    Prime (PowerSeries.X - PowerSeries.C x : PowerSeries O) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have h1 := congrArg (PowerSeries.coeff 1) h
    simp at h1
  · rw [PowerSeries.isUnit_iff_constantCoeff]
    simpa using hx
  · intro a b h
    rw [← X_dvd_ev_iff hinj hx ev hev, map_mul] at h
    rw [← X_dvd_ev_iff hinj hx ev hev a, ← X_dvd_ev_iff hinj hx ev hev b]
    exact PowerSeries.X_prime.2.2 _ _ h

end

theorem prod_prime_pow_dvd {R ι : Type} [CommRing R] [IsDomain R] (p : ι → R) (m : ι → ℕ)
    (hp : ∀ k, Prime (p k)) (hne : ∀ j k, p j ∣ p k → j = k) (a : R)
    (h : ∀ k, p k ^ m k ∣ a) (s : Finset ι) : (∏ k ∈ s, p k ^ m k) ∣ a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi]
    obtain ⟨t, ht⟩ := ih
    have hnd : ¬ p i ∣ ∏ k ∈ s, p k ^ m k := by
      intro hd
      obtain ⟨k, hk, hdk⟩ := ((hp i).dvd_finsetProd_iff _).1 hd
      have hik := hne i k ((hp i).dvd_of_dvd_pow hdk)
      subst hik
      exact hi hk
    have hdt : p i ^ m i ∣ t :=
      (hp i).pow_dvd_of_dvd_mul_left _ hnd (by rw [← ht]; exact h i)
    rw [ht, mul_comm _ t]
    exact mul_dvd_mul_right hdt _

theorem weierstrass_test : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O], ∀ (LL : Type) [Field LL] [Algebra O LL] [IsFractionRing O LL] (ι : Type) [Fintype ι] (x : ι → O) (m : ι → ℕ), Function.Injective x → (∀ k, ¬ IsUnit (x k)) → ∀ (ev : ι → (PowerSeries O →ₐ[O] PowerSeries LL)), (∀ k, ∃ w : PowerSeries LL, IsUnit w ∧ ev k PowerSeries.X = PowerSeries.C (algebraMap O LL (x k)) + PowerSeries.X * w) → ∀ a : PowerSeries O, (∀ k, PowerSeries.X ^ m k ∣ ev k a) ↔ (∏ k, (PowerSeries.X - PowerSeries.C (x k)) ^ m k) ∣ a := by
  intro O _ _ _ _ LL _ _ _ ι _ x m hxinj hxu ev hev a
  have hinj : Function.Injective (algebraMap O LL) := IsFractionRing.injective O LL
  have key : ∀ k, PowerSeries.X ^ m k ∣ ev k a ↔
      (PowerSeries.X - PowerSeries.C (x k)) ^ m k ∣ a := by
    intro k
    obtain ⟨w, hw, hwk⟩ := hev k
    exact X_pow_dvd_ev_iff hinj (hxu k) (ev k) hw hwk (m k) a
  simp_rw [key]
  constructor
  · intro h
    refine prod_prime_pow_dvd (fun k => PowerSeries.X - PowerSeries.C (x k)) m ?_ ?_ a h
      Finset.univ
    · intro k
      obtain ⟨w, -, hwk⟩ := hev k
      exact prime_X_sub_C hinj (hxu k) (ev k) hwk
    · intro j k hjk
      obtain ⟨w, -, hwj⟩ := hev j
      have h1 := (X_dvd_ev_iff hinj (hxu j) (ev j) hwj _).2 hjk
      rw [map_sub, hwj, ev_C, PowerSeries.X_dvd_iff] at h1
      have h2 : algebraMap O LL (x j) = algebraMap O LL (x k) := by
        simpa [sub_eq_zero] using h1
      exact hxinj (hinj h2)
  · intro h k
    exact (Finset.dvd_prod_of_mem _ (Finset.mem_univ k)).trans h

end GlobalTheory.Per
end

section

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne

theorem exists_monic_base_root_near : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω), (∀ z : Ω, (∀ d ∈ Dec (F := E) A, d z = z) → ∀ r : Ω, r ≠ 0 → ∃ e : E, A.valuation (algebraMap E Ω e - z) < A.valuation r) → ∀ f : Polynomial Ω, f.Monic → (∀ d ∈ Dec (F := E) A, ∀ i, d (f.coeff i) = f.coeff i) → ∀ β : Ω, f.eval β = 0 → ∀ r : Ω, r ≠ 0 → ∃ g : Polynomial E, g.Monic ∧ g.natDegree = f.natDegree ∧ ∃ β' : Ω, aeval β' g = 0 ∧ A.valuation (β' - β) < A.valuation r := by
  intro E Ω _ _ _ _ _ A hdense f hf hfix β hβ r hr
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  set n := f.natDegree with hn
  have hvr : A.valuation r ≠ 0 := (Valuation.ne_zero_iff _).mpr hr
  have hvrn : A.valuation r ^ n ≠ 0 := pow_ne_zero _ hvr
  have happ : ∀ i, ∃ e : E,
      A.valuation (algebraMap E Ω e - f.coeff i) * A.valuation β ^ i < A.valuation r ^ n := by
    intro i
    by_cases hb : β = 0
    · rcases Nat.eq_zero_or_pos i with rfl | hi
      · obtain ⟨e, he⟩ := hdense (f.coeff 0) (fun d hd => hfix d hd 0) (r ^ n) (pow_ne_zero _ hr)
        exact ⟨e, by simpa [map_pow] using he⟩
      · refine ⟨0, ?_⟩
        simp only [hb, map_zero, zero_pow hi.ne', mul_zero]
        exact zero_lt_iff.mpr hvrn
    · have hbi : β ^ i ≠ 0 := pow_ne_zero _ hb
      obtain ⟨e, he⟩ := hdense (f.coeff i) (fun d hd => hfix d hd i) (r ^ n / β ^ i)
        (div_ne_zero (pow_ne_zero _ hr) hbi)
      refine ⟨e, ?_⟩
      have hvb : A.valuation β ^ i ≠ 0 := by
        rw [← map_pow]; exact (Valuation.ne_zero_iff _).mpr hbi
      rw [map_div₀, map_pow, map_pow] at he
      calc A.valuation (algebraMap E Ω e - f.coeff i) * A.valuation β ^ i
          < A.valuation r ^ n / A.valuation β ^ i * A.valuation β ^ i :=
            mul_lt_mul_of_pos_right he (zero_lt_iff.mpr hvb)
        _ = A.valuation r ^ n := div_mul_cancel₀ _ hvb
  choose c hc using happ
  let p : E[X] := ∑ i : Fin n, C (c i) * X ^ (i : ℕ)
  have hp : p.degree < n := degree_sum_fin_lt _
  let g : E[X] := X ^ n + p
  have hgm : g.Monic := monic_X_pow_add hp
  have hgd : g.natDegree = n := by
    show (X ^ n + p).natDegree = n
    rw [natDegree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), natDegree_X_pow]
  have h0 : f.eval β = β ^ n + ∑ i ∈ Finset.range n, f.coeff i * β ^ i := by
    conv_lhs => rw [hf.as_sum]
    simp [Polynomial.eval_finsetSum, ← hn]
  have hga : aeval β g = β ^ n + ∑ i ∈ Finset.range n, algebraMap E Ω (c i) * β ^ i := by
    show aeval β (X ^ n + ∑ i : Fin n, C (c i) * X ^ (i : ℕ)) = _

    simp only [map_add (f := _), map_pow, aeval_X, map_sum, map_mul, aeval_C]
    rw [Fin.sum_univ_eq_sum_range (fun i => algebraMap E Ω (c i) * β ^ i) n]
  have hgβ : aeval β g = ∑ i ∈ Finset.range n, (algebraMap E Ω (c i) - f.coeff i) * β ^ i := by
    have : aeval β g = aeval β g - f.eval β := by rw [hβ, sub_zero]
    rw [this, hga, h0]
    simp [sub_mul, Finset.sum_sub_distrib]
  have hvg : A.valuation (aeval β g) < A.valuation r ^ n := by
    rw [hgβ]
    refine Valuation.map_sum_lt _ hvrn fun i _ => ?_
    rw [map_mul, map_pow]; exact hc i
  set G := g.map (algebraMap E Ω) with hG
  have hGm : G.Monic := hgm.map _
  have hGd : G.natDegree = n := by rw [hG, natDegree_map, hgd]
  have hprod : (G.roots.map fun a => X - C a).prod = G :=
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq hGm IsAlgClosed.card_roots_eq_natDegree
  have hev : aeval β g = (G.roots.map fun a => β - a).prod := by
    rw [aeval_def, ← eval_map, ← hG]
    conv_lhs => rw [← hprod]
    rw [eval_multiset_prod, Multiset.map_map]
    simp [Function.comp_def]
  have hex : ∃ a ∈ G.roots, A.valuation (β - a) < A.valuation r := by
    by_contra hcon
    push_neg at hcon
    have h1 : A.valuation r ^ n ≤ A.valuation (aeval β g) := by
      rw [hev, map_multiset_prod, Multiset.map_map]
      have hcard : (G.roots.map (A.valuation ∘ fun a => β - a)).card = n := by
        rw [Multiset.card_map, IsAlgClosed.card_roots_eq_natDegree, hGd]
      calc A.valuation r ^ n = A.valuation r ^ (G.roots.map (A.valuation ∘ fun a => β - a)).card := by
            rw [hcard]
        _ ≤ _ := Multiset.pow_card_le_prod (by
            intro x hx
            obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hx
            exact hcon a ha)
    exact absurd hvg (not_lt.mpr h1)
  obtain ⟨a, ha, hva⟩ := hex
  refine ⟨g, hgm, hgd, a, ?_, ?_⟩
  · have := (mem_roots hGm.ne_zero).mp ha
    rw [aeval_def, ← eval_map]; exact this
  · rwa [Valuation.map_sub_swap]

end GlobalTheory.WeilDeligne
end

section

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory

theorem krasner_val_lt_apply_iff {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    {A : ValuationSubring Ω} {σ : G E Ω} (hσ : σ ∈ Dec (F := E) A) (a b : Ω) :
    A.valuation (σ a) < A.valuation (σ b) ↔ A.valuation a < A.valuation b := by
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  · have hb' : A.valuation b ≠ 0 := by simpa using hb
    have hsb : σ b ≠ 0 := (map_ne_zero_iff _ σ.injective).mpr hb
    have hsb' : A.valuation (σ b) ≠ 0 := by simpa using hsb
    rw [← div_lt_one₀ (zero_lt_iff.mpr hb'), ← div_lt_one₀ (zero_lt_iff.mpr hsb'),
      ← map_div₀, ← map_div₀, ← map_div₀, valuation_apply_lt_one_iff hσ]

theorem krasner_stabiliser (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (A : ValuationSubring Ω) (β β' : Ω)
    (h : ∀ d ∈ Dec (F := E) A, d β ≠ β → A.valuation (β' - β) < A.valuation (d β - β)) :
    ∀ σ ∈ Dec (F := E) A, σ β' = β' → σ β = β := by
  intro σ hσ hfix
  by_contra hne
  have hσi : σ⁻¹ ∈ Dec (F := E) A := (Dec (F := E) A).inv_mem hσ
  have hne' : (σ⁻¹ : G E Ω) β ≠ β := by
    intro he
    apply hne
    conv_lhs => rw [← he]
    exact mul_inv_apply β
  have h1 := h σ hσ hne
  have h2 := h σ⁻¹ hσi hne'
  rw [← krasner_val_lt_apply_iff hσ, map_sub σ, map_sub σ, mul_inv_apply, hfix] at h2
  have e : β - σ β = (β - β') + (β' - σ β) := by ring
  have h3 : A.valuation (β - σ β) = A.valuation (σ β - β) := Valuation.map_sub_swap _ _ _
  have h4 : A.valuation (β - β') = A.valuation (β' - β) := Valuation.map_sub_swap _ _ _
  have key : A.valuation (β - σ β) < A.valuation (β - σ β) := by
    conv_lhs => rw [e]
    refine Valuation.map_add_lt _ ?_ h2
    rw [h4, h3]; exact h1
  exact lt_irrefl _ key

end GlobalTheory
end

section

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne

theorem exists_finset_fix_subset_of_isOpen : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (M : Subgroup (Ine (F := E) A)),
    IsOpen (M : Set (Ine (F := E) A)) → ∃ s : Finset Ω, ∀ σ : Ine (F := E) A,
      (∀ x ∈ s, (σ : G E Ω) x = x) → σ ∈ M := by
  intro E Ω _ _ _ _ _ A M hM
  obtain ⟨U, hU, hUM⟩ := isOpen_induced_iff.mp hM
  have h1 : (1 : G E Ω) ∈ U := by
    have : (1 : Ine (F := E) A) ∈ (Subtype.val ⁻¹' U) := by rw [hUM]; exact M.one_mem
    simpa using this
  obtain ⟨L, hL, hLU⟩ := (krullTopology_mem_nhds_one_iff E Ω U).mp (hU.mem_nhds h1)
  have hfg : L.toSubalgebra.FG := by
    apply Subalgebra.fg_of_fg_toSubmodule
    exact Module.Finite.iff_fg.mp hL
  obtain ⟨t, ht⟩ := hfg
  refine ⟨t, fun σ hσ => ?_⟩
  have hmem : (σ : G E Ω) ∈ L.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have hx' : x ∈ Algebra.adjoin E (t : Set Ω) := by rw [ht]; exact hx
    have key : Set.EqOn ((σ : G E Ω) : Ω →ₐ[E] Ω) (AlgHom.id E Ω) (Algebra.adjoin E (t : Set Ω)) :=
      AlgHom.eqOn_adjoin_iff.mpr (fun y hy => hσ y hy)
    exact key hx'
  have : σ ∈ (Subtype.val ⁻¹' U : Set (Ine (F := E) A)) := hLU hmem
  rw [hUM] at this
  exact this

end GlobalTheory.WeilDeligne
end
