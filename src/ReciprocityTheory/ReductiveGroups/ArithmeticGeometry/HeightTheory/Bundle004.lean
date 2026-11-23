module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
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
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Ideal.UFD
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.KrullDimension.Field
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.T0

namespace ValUFD

variable {R F : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] [Field F]
  [Algebra R F] [IsFractionRing R F]

theorem heightOne_principal (p : Ideal R) [p.IsPrime] (hp : p.height = 1) :
    ∃ g : R, Prime g ∧ p = Ideal.span {g} := by
  have hpr := UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hp
  have hsp : Ideal.span {Submodule.IsPrincipal.generator p} = p :=
    Submodule.IsPrincipal.span_singleton_generator p
  have hne : Submodule.IsPrincipal.generator p ≠ 0 := fun h0 =>
    p.ne_bot_of_height_eq_one hp ((Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero p).mpr h0)
  refine ⟨_, (Ideal.span_singleton_prime hne).mp (by rw [hsp]; infer_instance), hsp.symm⟩

theorem height_span_prime {q : R} (hq : Prime q) : (Ideal.span {q}).height = 1 := by
  have _ : (Ideal.span {q}).IsPrime := (Ideal.span_singleton_prime hq.ne_zero).mpr hq
  apply le_antisymm
  · rw [← Nat.cast_one, Ideal.height_le_iff]
    intro P hPp hlt
    have hPb : P = ⊥ := by
      by_contra hne
      obtain ⟨q', hq'P, hq'⟩ := hPp.exists_mem_prime_of_ne_bot hne
      have hdvd : q ∣ q' := Ideal.mem_span_singleton.mp (hlt.le hq'P)
      have hass := hq.associated_of_dvd hq' hdvd
      have hle : Ideal.span {q} ≤ P :=
        (Ideal.span_singleton_le_iff_mem P).mpr (P.mem_of_dvd hass.symm.dvd hq'P)
      exact absurd hle (not_le_of_gt hlt)
    rw [hPb, Ideal.height_bot]
    exact_mod_cast Nat.zero_lt_one
  · rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot, Ideal.span_singleton_eq_bot]
    exact hq.ne_zero

theorem loc_dvr (p : Ideal R) [p.IsPrime] (hp : p.height = 1) (g : R) (hg : p = Ideal.span {g}) :
    IsDiscreteValuationRing (Localization.AtPrime p) ∧
      Irreducible (algebraMap R (Localization.AtPrime p) g) := by
  set O := Localization.AtPrime p
  have hg0 : g ≠ 0 := by
    rintro rfl
    exact p.ne_bot_of_height_eq_one hp (by rw [hg, Ideal.span_singleton_eq_bot])
  have hgp : Prime g := (Ideal.span_singleton_prime hg0).mp (hg ▸ inferInstance)
  have hinj : Function.Injective (algebraMap R O) :=
    IsLocalization.injective O (Ideal.primeCompl_le_nonZeroDivisors p)
  have h1 : Ideal.map (algebraMap R O) p = Ideal.span {algebraMap R O g} := by
    rw [congrArg (Ideal.map (algebraMap R O)) hg, Ideal.map_span, Set.image_singleton]
  have hspan : Ideal.span {algebraMap R O g} = IsLocalRing.maximalIdeal O :=
    h1.symm.trans (IsLocalization.AtPrime.map_eq_maximalIdeal p O)
  have hϖ0 : algebraMap R O g ≠ 0 := by rw [Ne, map_eq_zero_iff _ hinj]; exact hg0
  have hϖ : Prime (algebraMap R O g) :=
    (Ideal.span_singleton_prime hϖ0).mp (by rw [hspan]; infer_instance)
  have hdvr : IsDiscreteValuationRing O := by
    refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
      ⟨_, hϖ.irreducible, ?_⟩
    intro x hx
    obtain ⟨⟨a, s⟩, hxs⟩ := IsLocalization.mk'_surjective p.primeCompl x
    simp only at hxs
    subst hxs
    have ha : a ≠ 0 := by rintro rfl; exact hx (by simp)
    obtain ⟨n, a', hnd, rfl⟩ := WfDvdMonoid.max_power_factor ha hgp.irreducible
    have ha' : a' ∈ p.primeCompl := by
      show a' ∉ p
      rw [hg, Ideal.mem_span_singleton]; exact hnd
    refine ⟨n, ((IsLocalization.AtPrime.isUnit_mk'_iff O p a' s).mpr ha').unit, ?_⟩
    rw [IsUnit.unit_spec, ← map_pow, IsLocalization.mul_mk'_eq_mk'_of_mul]
  exact ⟨hdvr, hϖ.irreducible⟩

section Factor

variable {gen : Ideal R → R}

theorem gen_prime (hgen : ∀ p : Ideal R, p.IsPrime → p.height = 1 → p = Ideal.span {gen p})
    {p : Ideal R} (hp : p ∈ {p : Ideal R | p.IsPrime ∧ p.height = 1}) : Prime (gen p) := by
  obtain ⟨hpp, hh⟩ := hp
  have hg := hgen p hpp hh
  have hne : gen p ≠ 0 := by
    intro h0
    apply p.ne_bot_of_height_eq_one hh
    rw [hg, h0, Ideal.span_singleton_eq_bot]
  exact (Ideal.span_singleton_prime hne).mp (hg ▸ hpp)

theorem gen_dvd_iff (hgen : ∀ p : Ideal R, p.IsPrime → p.height = 1 → p = Ideal.span {gen p})
    {p : Ideal R} (hp : p ∈ {p : Ideal R | p.IsPrime ∧ p.height = 1}) {q : R} (hq : Prime q) :
    gen p ∣ q ↔ p = Ideal.span {q} := by
  constructor
  · intro h
    rw [hgen p hp.1 hp.2, Ideal.span_singleton_eq_span_singleton]
    exact (gen_prime hgen hp).associated_of_dvd hq h
  · intro h
    subst h
    have h2 := hgen _ hp.1 hp.2
    rw [Ideal.span_singleton_eq_span_singleton] at h2
    exact h2.symm.dvd

end Factor

end ValUFD

end ReciprocityTheory.ChartRestriction.G.T0
end

section

namespace ReciprocityTheory.ChartRestriction.G.T0

open scoped TensorProduct

private theorem length_baseChange_of_isSimpleModule {R S : Type*} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] [Algebra R S]
    (hm : Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal S)
    (X : Type*) [AddCommGroup X] [Module R X] [hX : IsSimpleModule R X] :
    Module.length S (S ⊗[R] X) = Module.length R X := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hX
  have hIm : I.map (algebraMap R S) = IsLocalRing.maximalIdeal S := by
    rw [IsLocalRing.eq_maximalIdeal hI, hm]
  have e2 : (S ⊗[R] X) ≃ₗ[S] (S ⧸ IsLocalRing.maximalIdeal S) :=
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S) e).trans
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I).symm.toLinearEquiv.trans
        (Submodule.quotEquivOfEq _ _ hIm))
  have : IsSimpleModule S (S ⧸ IsLocalRing.maximalIdeal S) :=
    isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp (IsLocalRing.maximalIdeal.isMaximal S))
  have : IsSimpleModule S (S ⊗[R] X) := IsSimpleModule.congr e2
  rw [Module.length_eq_one, Module.length_eq_one]

private theorem length_baseChange_of_submodule_simple_quotient {R S : Type*} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] [Algebra R S] [Module.Flat R S]
    (hm : Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal S)
    {M : Type*} [AddCommGroup M] [Module R M] (N : Submodule R M) [IsSimpleModule R (M ⧸ N)]
    (ih : Module.length S (S ⊗[R] N) = Module.length R N) :
    Module.length S (S ⊗[R] M) = Module.length R M := by
  have hinj : Function.Injective (N.subtype.baseChange S) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ N.injective_subtype
  have hsurj : Function.Surjective (N.mkQ.baseChange S) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective S N.mkQ_surjective
  have hex : Function.Exact (N.subtype.baseChange S) (N.mkQ.baseChange S) := by
    rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
    exact lTensor_exact S (LinearMap.exact_subtype_mkQ N) N.mkQ_surjective
  rw [Module.length_eq_add_of_exact _ _ hinj hsurj hex,
    Module.length_eq_add_of_exact _ _ N.injective_subtype N.mkQ_surjective
      (LinearMap.exact_subtype_mkQ N),
    ih, length_baseChange_of_isSimpleModule hm (M ⧸ N)]

private theorem length_baseChange_of_isFiniteLength {R S : Type*} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] [Algebra R S] [Module.Flat R S]
    (hm : Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal S)
    {M : Type*} [AddCommGroup M] [Module R M] (h : IsFiniteLength R M) :
    Module.length S (S ⊗[R] M) = Module.length R M := by
  induction h with
  | @of_subsingleton M' _ _ _ =>
    have : Subsingleton (S ⊗[R] M') := by
      have h0 : ∀ z : S ⊗[R] M', z = 0 := fun z => by
        induction z using TensorProduct.induction_on with
        | zero => rfl
        | tmul s m => rw [Subsingleton.elim m 0, TensorProduct.tmul_zero]
        | add x y hx hy => rw [hx, hy, add_zero]
      exact ⟨fun a b => by rw [h0 a, h0 b]⟩
    rw [Module.length_eq_zero, Module.length_eq_zero]
  | of_simple_quotient _ ih =>
    exact length_baseChange_of_submodule_simple_quotient hm _ ih

private theorem length_le_length_baseChange_of_faithfullyFlat {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] (Q : Type*) [AddCommGroup Q] [Module R Q] :
    Module.length R Q ≤ Module.length S (S ⊗[R] Q) := by
  have hmono : ∀ N N' : Submodule R Q, N ≤ N' →
      LinearMap.range (N.subtype.baseChange S) ≤ LinearMap.range (N'.subtype.baseChange S) := by
    intro N N' h x hx
    obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp hx
    refine LinearMap.mem_range.mpr ⟨(Submodule.inclusion h).baseChange S z, ?_⟩
    rw [← Submodule.subtype_comp_inclusion _ _ h, LinearMap.baseChange_comp, LinearMap.comp_apply]
  have hrefl : ∀ N N' : Submodule R Q,
      LinearMap.range (N'.subtype.baseChange S) ≤ LinearMap.range (N.subtype.baseChange S) →
        N' ≤ N := by
    intro N N' h
    have hz : ∀ w : S ⊗[R] N, (N.mkQ.baseChange S) ((N.subtype.baseChange S) w) = 0 := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => rw [map_zero, map_zero]
      | tmul s n =>
        have hn : N.mkQ (N.subtype n) = 0 := (Submodule.Quotient.mk_eq_zero N).mpr n.2
        rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, hn, TensorProduct.tmul_zero]
      | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, add_zero]
    have h0 : (N.mkQ ∘ₗ N'.subtype).lTensor S = 0 := by
      refine LinearMap.ext fun z => ?_
      obtain ⟨w, hw⟩ :=
        LinearMap.mem_range.mp (h (LinearMap.mem_range_self (N'.subtype.baseChange S) z))
      have hb : ((N.mkQ ∘ₗ N'.subtype).baseChange S) z = 0 := by
        rw [LinearMap.baseChange_comp, LinearMap.comp_apply, ← hw, hz]
      rw [LinearMap.zero_apply]
      rwa [LinearMap.baseChange_eq_ltensor] at hb
    have hf : N.mkQ ∘ₗ N'.subtype = 0 :=
      (Module.FaithfullyFlat.zero_iff_lTensor_zero R S _).mpr h0
    intro x hx
    have hx0 := LinearMap.congr_fun hf ⟨x, hx⟩
    simpa using hx0
  have hsm : StrictMono (fun N : Submodule R Q => LinearMap.range (N.subtype.baseChange S)) :=
    fun N N' hlt => lt_of_le_of_ne (hmono N N' hlt.le)
      (fun heq => hlt.ne (le_antisymm hlt.le (hrefl N N' heq.ge)))
  have h1 : (Module.length R Q : WithBot ℕ∞) ≤ (Module.length S (S ⊗[R] Q) : WithBot ℕ∞) := by
    rw [Module.coe_length, Module.coe_length]
    exact Order.krullDim_le_of_strictMono _ hsm
  exact WithBot.coe_le_coe.mp h1

theorem length_baseChange_eq {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S]
    [IsLocalRing S] [Algebra R S] [Module.Flat R S] [IsLocalHom (algebraMap R S)]
    (hm : Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal S)
    (Q : Type*) [AddCommGroup Q] [Module R Q] :
    Module.length S (S ⊗[R] Q) = Module.length R Q := by
  have : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hge := length_le_length_baseChange_of_faithfullyFlat (R := R) (S := S) Q
  by_cases hQ : Module.length R Q = ⊤
  · rw [hQ] at hge ⊢
    exact top_le_iff.mp hge
  · exact length_baseChange_of_isFiniteLength hm (Module.length_ne_top_iff.mp hQ)

end ReciprocityTheory.ChartRestriction.G.T0
end

section

namespace ReciprocityTheory.ChartRestriction.G.T0

open IsLocalRing

theorem av_no_two_chain {S : Type*} [CommRing S] [IsDomain S] {A B : Ideal S} [A.IsPrime]
    [B.IsPrime] (h1 : ⊥ < A) (h2 : A < B) (hB : B.height ≤ 1) : False := by
  have hA : 1 ≤ A.height := le_add_self.trans (Ideal.height_add_one_le_of_lt_of_isPrime h1)
  have hB₂ : (2 : ℕ∞) ≤ B.height := calc
    (2 : ℕ∞) = 1 + 1 := by norm_num
    _ ≤ A.height + 1 := add_le_add hA le_rfl
    _ ≤ B.height := Ideal.height_add_one_le_of_lt_of_isPrime h2
  exact (by norm_num : ¬ (2 : ℕ∞) ≤ 1) (hB₂.trans hB)

theorem av_key {S : Type*} [CommRing S] [IsDomain S] [IsNoetherianRing S] [IsLocalRing S] (g : S)
    (hg : g ≠ 0) (H : ∀ Q : Ideal S, Q.IsPrime → Q ≠ ⊥ → g ∈ Q) (Q : Ideal S) (hQ : Q.IsPrime)
    (hQ0 : Q ≠ ⊥) : Q.IsMaximal := by
  classical
  by_contra hQm
  set m := IsLocalRing.maximalIdeal S with hm_def
  have hQlt : Q < m := lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hQ.ne_top)
    (fun h => hQm (h ▸ IsLocalRing.maximalIdeal.isMaximal S))
  haveI : (Ideal.span {g}).IsPrincipal := ⟨⟨g, rfl⟩⟩
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing S (Ideal.span {g})

  have hmin : ∀ P ∈ (Ideal.span {g}).minimalPrimes, P.IsPrime ∧ P ≠ ⊥ ∧ P.height ≤ 1 := by
    intro P hP
    refine ⟨hP.1.1, ?_, ?_⟩
    · intro h
      apply hg
      have := hP.1.2 (Ideal.mem_span_singleton_self g)
      rw [h] at this
      exact (Submodule.mem_bot S).mp this
    · exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hP

  have hbelow : ∀ P' : Ideal S, P'.IsPrime → P' ≠ ⊥ →
      ∃ P ∈ (Ideal.span {g}).minimalPrimes, P ≤ P' := by
    intro P' hP' h0
    exact Ideal.exists_minimalPrimes_le ((Ideal.span_singleton_le_iff_mem _).mpr (H P' hP' h0))

  have hm_not : ∀ P ∈ (Ideal.span {g}).minimalPrimes, ¬ m ≤ P := by
    intro P hP hmP
    obtain ⟨P0, hP0, hP0Q⟩ := hbelow Q hQ hQ0
    obtain ⟨hPp, -, hPh⟩ := hmin P hP
    obtain ⟨hP0p, hP00, -⟩ := hmin P0 hP0
    haveI := hPp
    haveI := hP0p
    exact av_no_two_chain (bot_lt_iff_ne_bot.mpr hP00)
      (lt_of_le_of_lt hP0Q (lt_of_lt_of_le hQlt hmP)) hPh

  obtain ⟨x, hxm, hxP⟩ : ∃ x ∈ m, ∀ P ∈ (Ideal.span {g}).minimalPrimes, x ∉ P := by
    by_contra hcon
    push_neg at hcon
    have hsub : (m : Set S) ⊆ ⋃ P ∈ (hfin.toFinset : Set (Ideal S)), ((id P : Ideal S) : Set S) := by
      intro y hy
      obtain ⟨P, hP, hyP⟩ := hcon y hy
      exact Set.mem_iUnion₂.mpr ⟨P, by simpa using hP, hyP⟩
    obtain ⟨P, hP, hle⟩ := (Ideal.subset_union_prime (f := id) ⊥ ⊥
      (fun P hP _ _ => (hmin P (by simpa using hP)).1)).mp hsub
    exact hm_not P (by simpa using hP) hle
  obtain ⟨P0, hP0, -⟩ := hbelow Q hQ hQ0
  have hx0 : x ≠ 0 := by
    intro h
    apply hxP P0 hP0
    rw [h]
    exact Submodule.zero_mem _
  obtain ⟨P', hP', -⟩ := Ideal.exists_minimalPrimes_le ((Ideal.span_singleton_le_iff_mem m).mpr hxm)
  haveI := hP'.1.1
  have hxP' : x ∈ P' := hP'.1.2 (Ideal.mem_span_singleton_self x)
  have hP'0 : P' ≠ ⊥ := by
    intro h
    rw [h] at hxP'
    exact hx0 ((Submodule.mem_bot S).mp hxP')
  haveI : (Ideal.span {x}).IsPrincipal := ⟨⟨x, rfl⟩⟩
  have hP'h : P'.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P' hP'
  obtain ⟨P, hP, hPP'⟩ := hbelow P' hP'.1.1 hP'0
  obtain ⟨hPp, hP00, -⟩ := hmin P hP
  rcases lt_or_eq_of_le hPP' with hlt | heq
  · haveI := hPp
    exact av_no_two_chain (bot_lt_iff_ne_bot.mpr hP00) hlt hP'h
  · apply hxP P hP
    rw [heq]
    exact hxP'

theorem av_prime_dim_one {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
    (hdim : 1 ≤ ringKrullDim R) (h : R) (hh : h ≠ 0) :
    ∃ p : Ideal R, p.IsPrime ∧ ringKrullDim (R ⧸ p) = 1 ∧ h ∉ p := by
  classical
  set m := IsLocalRing.maximalIdeal R with hm_def
  have hm0 : m ≠ ⊥ := by
    intro e
    have hF : IsField R := (IsLocalRing.isField_iff_maximalIdeal_eq).mpr e
    rw [ringKrullDim_eq_zero_of_isField hF] at hdim
    exact absurd hdim (by norm_num)

  obtain ⟨p, ⟨hpP, hhp, hpm⟩, hpmax⟩ := set_has_maximal_iff_noetherian.mpr
    (inferInstance : IsNoetherian R R) {q : Ideal R | q.IsPrime ∧ h ∉ q ∧ q ≠ m}
    ⟨⊥, Ideal.isPrime_bot, fun h' => hh ((Submodule.mem_bot R).mp h'), fun e => hm0 e.symm⟩
  haveI := hpP
  refine ⟨p, hpP, ?_, hhp⟩
  have hplt : p < m := lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hpP.ne_top) hpm
  obtain ⟨y, hym, hyp⟩ := SetLike.exists_of_lt hplt
  set f := Ideal.Quotient.mk p with hf_def
  haveI : IsLocalRing (R ⧸ p) := IsLocalRing.of_surjective' f Ideal.Quotient.mk_surjective
  have hfz : ∀ a : R, f a = 0 ↔ a ∈ p := fun a => Ideal.Quotient.eq_zero_iff_mem
  have hg0 : f (h * y) ≠ 0 := by
    rw [Ne, hfz]
    intro hm'
    rcases hpP.mem_or_mem hm' with h1 | h1
    · exact hhp h1
    · exact hyp h1

  have hall : ∀ Q : Ideal (R ⧸ p), Q.IsPrime → Q ≠ ⊥ → f (h * y) ∈ Q := by
    intro Q hQ hQ0
    haveI := hQ
    have hq : (Q.comap f).IsPrime := inferInstance
    have hpq : p < Q.comap f := by
      refine lt_of_le_of_ne (fun a ha => ?_) (fun e => hQ0 ?_)
      · show f a ∈ Q
        rw [(hfz a).mpr ha]
        exact Q.zero_mem
      · rw [eq_bot_iff]
        intro z hz
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
        have ha : a ∈ Q.comap f := hz
        rw [← e] at ha
        exact (Submodule.mem_bot _).mpr ((hfz a).mpr ha)
    show h * y ∈ Q.comap f
    by_cases hhq : h ∈ Q.comap f
    · exact Ideal.mul_mem_right _ _ hhq
    · have hqm : Q.comap f = m := by
        by_contra hne
        exact hpmax _ ⟨hq, hhq, hne⟩ hpq
      rw [hqm]
      exact Ideal.mul_mem_left _ _ hym
  have hmax : ∀ Q : Ideal (R ⧸ p), Q.IsPrime → Q ≠ ⊥ → Q.IsMaximal :=
    fun Q hQ hQ0 => av_key (f (h * y)) hg0 hall Q hQ hQ0
  apply le_antisymm
  · unfold ringKrullDim Order.krullDim
    refine iSup_le fun s => ?_
    by_contra hlt
    have h2 : 2 ≤ s.length := by
      by_contra h2
      apply hlt
      have : s.length ≤ 1 := by omega
      exact_mod_cast this
    have a01 : s ⟨0, by omega⟩ < s ⟨1, by omega⟩ := s.strictMono (Fin.mk_lt_mk.mpr (by norm_num))
    have a12 : s ⟨1, by omega⟩ < s ⟨2, by omega⟩ := s.strictMono (Fin.mk_lt_mk.mpr (by norm_num))
    rw [← PrimeSpectrum.asIdeal_lt_asIdeal] at a01 a12
    have hne : (s ⟨1, by omega⟩).asIdeal ≠ ⊥ := fun e => not_lt_bot (e ▸ a01)
    have hM := hmax _ (s ⟨1, by omega⟩).isPrime hne
    exact a12.ne (hM.eq_of_le (s ⟨2, by omega⟩).isPrime.ne_top a12.le)
  · haveI hMp : (m.map f).IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hplt.le)
    have hlt : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (R ⧸ p)) < ⟨m.map f, hMp⟩ := by
      rw [← PrimeSpectrum.asIdeal_lt_asIdeal]
      refine bot_lt_iff_ne_bot.mpr fun e => ?_
      have hy : f y ∈ m.map f := Ideal.mem_map_of_mem f hym
      have e' : m.map f = ⊥ := e
      rw [e'] at hy
      exact hyp ((hfz y).mp ((Submodule.mem_bot _).mp hy))
    have e1 := Order.height_add_one_le hlt
    calc (1 : WithBot ℕ∞) ≤ ((Order.height (⟨m.map f, hMp⟩ : PrimeSpectrum (R ⧸ p)) : ℕ∞) :
          WithBot ℕ∞) := by exact_mod_cast (le_add_self.trans e1)
      _ ≤ ringKrullDim (R ⧸ p) := Order.height_le_krullDim _

end ReciprocityTheory.ChartRestriction.G.T0
end
