module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle500
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle263
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle409
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle407
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle511
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012

@[expose] public section

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR Opposite KaehlerDifferential

theorem _root_.GlobalTheory.T.exists_glue_functions_affineOpen_from_pairs : ∀ {R' : Type} [CommRing R'] {X X' : Scheme.{0}} (φ : X' ⟶ X) (s' : X' ⟶ Sp R') (W : X'.affineOpens) (k : ∀ p : Pair φ, p.1.1 ≤ W → (OAff s').obj (op p.1.1)), (∀ (p q : Pair φ) (hp : p.1.1 ≤ W) (hq : q.1.1 ≤ W) (hqp : q ≤ p), mp (OAff s') (homOfLE (Pair.le_fst hqp)).op (k p hp) = k q hq) → ∃ G : (OAff s').obj (op W), ∀ (p : Pair φ) (hp : p.1.1 ≤ W), mp (OAff s') (homOfLE hp).op G = k p hp := by
  first | exact @GlobalTheory.CechDR.pair_glue | exact GlobalTheory.CechDR.pair_glue | (intros; apply GlobalTheory.CechDR.pair_glue <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR Opposite KaehlerDifferential

theorem _root_.GlobalTheory.T.oneForm_eq_zero_of_vanishing_on_pairs : ∀ {R' : Type} [CommRing R'] {X X' : Scheme.{0}} (φ : X' ⟶ X) (s' : X' ⟶ Sp R') (W : X'.affineOpens) (ω : Ω[(OAff s').obj (op W)⁄R']), (∀ (p : Pair φ) (hp : p.1.1 ≤ W), p1 (OAff s') (homOfLE hp).op ω = 0) → ω = 0 := by
  first | exact @GlobalTheory.CechDR.form_eq_zero_of_pair | exact GlobalTheory.CechDR.form_eq_zero_of_pair | (intros; apply GlobalTheory.CechDR.form_eq_zero_of_pair <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.CoefSeq

variable {R : Type} [CommRing R]

end GlobalTheory.EtC.CoefSeq

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
private lemma exact_comp_injective {A B C C' : Type*} [Zero C] [Zero C'] {f : A → B} {g : B → C}
    {β : C → C'} (hfg : Function.Exact f g) (hβ : Function.Injective β) (h0 : β 0 = 0) :
    Function.Exact f (β ∘ g) := by
  intro y
  rw [← hfg y, Function.comp_apply, ← h0]
  exact hβ.eq_iff

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
private lemma exact_conj_bijection_middle {A B B' C : Type*} [Zero C] {f : A → B} {g : B → C}
    (β : B → B') (δ : B' → B) (hδβ : ∀ b, δ (β b) = b) (hβδ : ∀ b', β (δ b') = b')
    (hfg : Function.Exact f g) : Function.Exact (β ∘ f) (g ∘ δ) := by
  intro y
  rw [Function.comp_apply, hfg (δ y)]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, by rw [Function.comp_apply, hx, hβδ]⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, by rw [Function.comp_apply, hδβ]⟩

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
private lemma exact_comp_surjective {A A' B C : Type*} [Zero C] {f : A → B} {g : B → C}
    {γ : A' → A} (hfg : Function.Exact f g) (hγ : Function.Surjective γ) :
    Function.Exact (f ∘ γ) g := by
  intro y
  rw [hfg y, Set.range_comp, hγ.range_eq, Set.image_univ]


open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
theorem _root_.GlobalTheory.EtC.coefSeq_exact : _root_.GlobalTheory.EtC.A7 := by
  unfold _root_.GlobalTheory.EtC.A7
  intro R _ S hS
  obtain ⟨e, ⟨hom⟩⟩ := _root_.GlobalTheory.EtC.cone_resMap_homotopyEquiv R S hS
  refine ⟨_root_.GlobalTheory.EtC.zcomp (Cocycle.ofHom e.inv)
    (mappingCone.fst (_root_.GlobalTheory.EtC.resMap R S.f)) (zero_add 1), fun K n => ?_⟩
  obtain ⟨ex₁, ex₂, ex₃⟩ :=
    _root_.GlobalTheory.EtC.coneSeqTgt_exact R K (_root_.GlobalTheory.EtC.resMap R S.f) n
  have hinvhom : ∀ x, _root_.GlobalTheory.EtC.cpush K e.inv n (_root_.GlobalTheory.EtC.cpush K e.hom n x) = x := by
    intro x
    rw [← _root_.GlobalTheory.EtC.InjResCmp.cpush_comp, _root_.GlobalTheory.EtC.InjResCmp.cpush_homotopy K e.homotopyHomInvId,
      _root_.GlobalTheory.EtC.InjResCmp.cpush_id]
  have hhominv : ∀ x, _root_.GlobalTheory.EtC.cpush K e.hom n (_root_.GlobalTheory.EtC.cpush K e.inv n x) = x := by
    intro x
    rw [← _root_.GlobalTheory.EtC.InjResCmp.cpush_comp, _root_.GlobalTheory.EtC.InjResCmp.cpush_homotopy K e.homotopyInvHomId,
      _root_.GlobalTheory.EtC.InjResCmp.cpush_id]
  have hg : ⇑(_root_.GlobalTheory.EtC.HK.post R K S.g n) =
      ⇑(_root_.GlobalTheory.EtC.cpush K e.hom n) ∘
        ⇑(_root_.GlobalTheory.EtC.cpush K (mappingCone.inr (_root_.GlobalTheory.EtC.resMap R S.f)) n) := by
    funext x
    show _root_.GlobalTheory.EtC.cpush K (_root_.GlobalTheory.EtC.resMap R S.g) n x = _
    rw [← _root_.GlobalTheory.EtC.InjResCmp.cpush_homotopy K hom, _root_.GlobalTheory.EtC.InjResCmp.cpush_comp]
    rfl
  have hδ : ⇑(_root_.GlobalTheory.EtC.HK.ext R K
      (_root_.GlobalTheory.EtC.zcomp (Cocycle.ofHom e.inv)
        (mappingCone.fst (_root_.GlobalTheory.EtC.resMap R S.f)) (zero_add 1)) n (n + 1) rfl) =
      ⇑(_root_.GlobalTheory.EtC.cpost K (mappingCone.fst (_root_.GlobalTheory.EtC.resMap R S.f)) n (n + 1) rfl) ∘
        ⇑(_root_.GlobalTheory.EtC.cpush K e.inv n) := by
    funext y
    exact ((_root_.GlobalTheory.cocycle_comp_assoc_classes R (add_zero n) (zero_add 1) rfl rfl).2.2
      y (Cocycle.ofHom e.inv) (mappingCone.fst (_root_.GlobalTheory.EtC.resMap R S.f)))
  refine ⟨?_, ?_, ?_⟩
  · rw [hg]
    exact exact_comp_injective ex₁ (Function.LeftInverse.injective hinvhom) (map_zero _)
  · rw [hg, hδ]
    exact exact_conj_bijection_middle _ _ hinvhom hhominv ex₂
  · rw [hδ]
    exact exact_comp_surjective ex₃ (Function.LeftInverse.surjective hinvhom)
end
end

section

set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.DPSeries

section SlopeTestRemainingChoices

variable {B : Type} [CommRing B] {τ : Type}

def coeffIdeal (J : Ideal B) (τ : Type) : Ideal (MvPowerSeries τ B) where
  carrier := {f | ∀ α, coeff α f ∈ J}
  add_mem' {a b} ha hb α := by
    rw [map_add (f := _)]
    exact J.add_mem (ha α) (hb α)
  zero_mem' α := by simp
  smul_mem' c f hf α := by
    classical
    rw [smul_eq_mul, coeff_mul]
    exact J.sum_mem fun x _ => J.mul_mem_left _ (hf _)

theorem coeff_pow_congr {f g : MvPowerSeries τ B} {β : τ →₀ ℕ}
    (h : ∀ α ≤ β, coeff α f = coeff α g) : ∀ n, ∀ α ≤ β, coeff α (f ^ n) = coeff α (g ^ n) := by
  classical
  intro n
  induction n with
  | zero => intro α _; rfl
  | succ n ih =>
    intro α hα
    rw [pow_succ, pow_succ, coeff_mul, coeff_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    have h1 : x.1 ≤ β := le_trans (by rw [← hx]; exact le_self_add) hα
    have h2 : x.2 ≤ β := le_trans (by rw [← hx]; exact le_add_self) hα
    rw [ih _ h1, h _ h2]

variable (p : ℕ) (J : Ideal B)

def HasPDiv (f : MvPowerSeries τ B) : Prop :=
  f ∈ coeffIdeal J τ ∧ ∃ y ∈ coeffIdeal J τ, f ^ p = (p : MvPowerSeries τ B) * y

variable {p J}

theorem hasPDiv_add (hp : p.Prime) {a b : MvPowerSeries τ B} (ha : HasPDiv p J a)
    (hb : HasPDiv p J b) : HasPDiv p J (a + b) := by
  obtain ⟨ha, ya, hya, hpa⟩ := ha
  obtain ⟨hb, yb, hyb, hpb⟩ := hb
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp a b
  refine ⟨(coeffIdeal J τ).add_mem ha hb, ya + yb + a * b * r, ?_, ?_⟩
  · exact (coeffIdeal J τ).add_mem ((coeffIdeal J τ).add_mem hya hyb)
      ((coeffIdeal J τ).mul_mem_right _ ((coeffIdeal J τ).mul_mem_right _ ha))
  · rw [hr, hpa, hpb]; ring

theorem hasPDiv_monomial (hJ : ∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) (α : τ →₀ ℕ) {c : B}
    (hc : c ∈ J) : HasPDiv p J (monomial α c) := by
  classical
  obtain ⟨y, hy, hcy⟩ := hJ c hc
  refine ⟨fun γ => ?_, monomial (p • α) y, fun γ => ?_, ?_⟩
  · rw [coeff_monomial]; split_ifs
    · exact hc
    · exact J.zero_mem
  · rw [coeff_monomial]; split_ifs
    · exact hy
    · exact J.zero_mem
  · rw [monomial_pow, hcy]
    ext γ
    rw [coeff_monomial, ← map_natCast (C (σ := τ) (R := B)) p, coeff_C_mul, coeff_monomial]
    split_ifs <;> simp

theorem hasPDiv_sum (hp : p.Prime) (hJ : ∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y)
    (c : (τ →₀ ℕ) → B) (hc : ∀ α, c α ∈ J) (s : Finset (τ →₀ ℕ)) :
    HasPDiv p J (∑ α ∈ s, monomial α (c α)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by simpa using (coeffIdeal J τ).zero_mem, 0, (coeffIdeal J τ).zero_mem, ?_⟩
    simp [hp.ne_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact hasPDiv_add hp (hasPDiv_monomial hJ a (hc a)) ih

theorem pow_prime_eq (hp : p.Prime) (hJ : ∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y)
    {w : MvPowerSeries τ B} (hw : w ∈ coeffIdeal J τ) :
    ∃ y ∈ coeffIdeal J τ, w ^ p = (p : MvPowerSeries τ B) * y := by
  classical
  have key : ∀ β : τ →₀ ℕ, ∃ c ∈ J, coeff β (w ^ p) = p * c := by
    intro β
    set w' : MvPowerSeries τ B := ∑ α ∈ Finset.Iic β, monomial α (coeff α w) with hw'
    have hagree : ∀ α ≤ β, coeff α w = coeff α w' := by
      intro α hα

      rw [hw', map_sum]
      simp_rw [coeff_monomial]
      rw [Finset.sum_ite_eq]
      simp [Finset.mem_Iic.mpr hα]
    obtain ⟨_, y, hy, hpy⟩ := hasPDiv_sum hp hJ (fun α => coeff α w) hw (Finset.Iic β)
    refine ⟨coeff β y, hy β, ?_⟩
    have hpy' : w' ^ p = (p : MvPowerSeries τ B) * y := hpy
    rw [coeff_pow_congr hagree p β le_rfl, hpy',
      ← map_natCast (C (σ := τ) (R := B)) p, coeff_C_mul]
  choose c hcJ hc using key
  let y : MvPowerSeries τ B := fun β => c β
  have hy : ∀ β, coeff β y = c β := fun _ => rfl
  refine ⟨y, fun β => by rw [hy]; exact hcJ β, ?_⟩
  ext β
  rw [hc, ← map_natCast (C (σ := τ) (R := B)) p, coeff_C_mul, hy]

theorem pow_eq_pow_factorization_mul (hp : p.Prime) (hJ : ∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) :
    ∀ n : ℕ, 0 < n → ∀ w ∈ coeffIdeal J τ, ∃ y ∈ coeffIdeal J τ,
      w ^ n = (p : MvPowerSeries τ B) ^ (n.factorial.factorization p) * y := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn w hw
  by_cases hpn : p ∣ n
  · obtain ⟨m, rfl⟩ := hpn
    have hm : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
    have hmn : m < p * m := by nlinarith [hp.two_le]
    obtain ⟨z, hz, hwz⟩ := pow_prime_eq hp hJ hw
    obtain ⟨y, hy, hzy⟩ := ih m hmn hm z hz
    refine ⟨y, hy, ?_⟩
    rw [Nat.factorization_factorial_mul hp, pow_mul, hwz, mul_pow, hzy]
    ring
  · rcases Nat.lt_or_ge n 2 with h | h
    · have h1 : n = 1 := by omega
      subst h1
      exact ⟨w, hw, by simp⟩
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      obtain ⟨y, hy, hwy⟩ := ih k (by omega) (by omega) w hw
      refine ⟨w * y, (coeffIdeal J τ).mul_mem_left _ hy, ?_⟩
      have hv : (k + 1).factorial.factorization p = k.factorial.factorization p := by
        rw [Nat.factorial_succ, Nat.factorization_mul (Nat.succ_ne_zero k)
          (Nat.factorial_ne_zero k), Finsupp.add_apply,
          Nat.factorization_eq_zero_of_not_dvd hpn, zero_add]
      rw [hv, pow_succ, hwy]; ring

end SlopeTestRemainingChoices

theorem pow_eq_factorial_mul : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q]
    [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ J : Ideal B,
    (∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) → ∀ (τ : Type) (w : MvPowerSeries τ B),
    (∀ α, coeff α w ∈ J) → ∀ n : ℕ, 0 < n → ∃ y : MvPowerSeries τ B,
    (∀ α, coeff α y ∈ J) ∧ w ^ n = (n.factorial : MvPowerSeries τ B) * y := by
  intro p hpf B O Q _ _ _ _ θ hF J hJ τ w hw n hn
  have hp : p.Prime := hpf.out
  obtain ⟨y, hy, hwy⟩ := pow_eq_pow_factorization_mul hp hJ n hn w hw
  obtain ⟨c, hc_def⟩ : ∃ c, c = ordCompl[p] n.factorial := ⟨_, rfl⟩
  have hcop : Nat.Coprime c p := by
    rw [hc_def]; exact (Nat.coprime_ordCompl hp (Nat.factorial_ne_zero n)).symm
  obtain ⟨u, hu⟩ := hF.unit_coprime c hcop
  refine ⟨C (↑u⁻¹ : B) * y, (coeffIdeal J τ).mul_mem_left _ hy, ?_⟩
  have hnat : p ^ (n.factorial.factorization p) * c = n.factorial := by
    rw [hc_def]; exact Nat.ordProj_mul_ordCompl_eq_self _ _
  have hfac : (p : MvPowerSeries τ B) ^ (n.factorial.factorization p) * (c : MvPowerSeries τ B) =
      (n.factorial : MvPowerSeries τ B) := by
    rw [← Nat.cast_pow, ← Nat.cast_mul, hnat]
  have hcu : (c : MvPowerSeries τ B) * C (↑u⁻¹ : B) = 1 := by
    rw [← map_natCast (C (σ := τ) (R := B)) c, ← hu, ← map_mul, Units.mul_inv, map_one]
  rw [hwy, ← hfac]
  linear_combination (-((p : MvPowerSeries τ B) ^ (n.factorial.factorization p) * y)) * hcu

end GlobalTheory.DPSeries
end
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.FrameIntegers

theorem isFrame_integers : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → IsFrame p C (RingHom.id O) := by
  intro p hp C _ _ _ v O _ _ hnu _ _ hv
  have hp0 : p ≠ 0 := hp.out.ne_zero
  have hpC : (p : C) ≠ 0 := Nat.cast_ne_zero.mpr hp0
  have hmapp : algebraMap O C (p : O) = (p : C) := map_natCast _ _
  have hvp1 : v (p : C) < 1 := by
    have h1 := hv.map_le_one (p : O)
    rw [hmapp] at h1
    rcases lt_or_eq_of_le h1 with h | h
    · exact h
    · exact absurd (hv.isUnit_of_one (by rw [hmapp]; exact Ne.isUnit hpC) (by rw [hmapp]; exact h)) hnu.out
  have hint : ∀ z : ℤ, v (z : C) ≤ 1 := by
    intro z
    have := hv.map_le_one (z : O)
    rwa [map_intCast] at this
  refine ⟨Function.surjective_id, hv.hom_inj, ?_, Ne.isUnit hpC, ?_, ?_, ?_, inferInstance⟩
  · intro q
    obtain ⟨k, hk⟩ : ∃ k : ℕ, v (p : C) ^ k * v q ≤ 1 := by
      by_cases hq : v q = 0
      · exact ⟨0, by simp [hq]⟩
      · obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr (pos_iff_ne_zero.mpr hq)) hvp1
        refine ⟨k, ?_⟩
        calc v (p : C) ^ k * v q ≤ (v q)⁻¹ * v q := mul_le_mul_of_nonneg_right hk.le zero_le
          _ = 1 := inv_mul_cancel₀ hq
    have hle : v ((p : C) ^ k * q) ≤ 1 := by rw [map_mul, map_pow]; exact hk
    obtain ⟨b, hb⟩ := hv.exists_of_le_one hle
    exact ⟨k, b, hb.symm⟩
  · intro n hn
    have hB : (n : C) * (Nat.gcdA n p : C) + (p : C) * (Nat.gcdB n p : C) = 1 := by
      have h := Nat.gcd_eq_gcd_ab n p
      rw [Nat.Coprime.gcd_eq_one hn] at h
      exact_mod_cast h.symm
    have hvn : v (n : C) = 1 := by
      have h1 : v (n : C) ≤ 1 := by exact_mod_cast hint n
      by_contra hne
      have hlt : v (n : C) < 1 := lt_of_le_of_ne h1 hne
      have a1 : v ((n : C) * (Nat.gcdA n p : C)) < 1 := by
        rw [map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_right' (hint _)) hlt
      have a2 : v ((p : C) * (Nat.gcdB n p : C)) < 1 := by
        rw [map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_right' (hint _)) hvp1
      have := Valuation.map_add_lt v a1 a2
      rw [hB, map_one] at this
      exact lt_irrefl _ this
    have hnC : (n : C) ≠ 0 := by
      intro h; rw [h, map_zero] at hvn; exact zero_ne_one hvn
    have hmapn : algebraMap O C (n : O) = (n : C) := map_natCast _ _
    exact hv.isUnit_of_one (by rw [hmapn]; exact Ne.isUnit hnC) (by rw [hmapn]; exact hvn)
  · intro x hx
    simp only [RingHom.id_apply] at hx
    subst hx
    exact ⟨0, rfl, by simp [hp0]⟩
  · intro a ha
    have hpO : (p : O) ≠ 0 := by
      intro h; apply hpC; rw [← hmapp, h, map_zero]
    exact (mul_eq_zero.mp ha).resolve_left hpO

end GlobalTheory.FrameIntegers
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog.ValLin

lemma eval_map_hom {σ Q Q' : Type} [CommRing Q] [CommRing Q'] (R : Q →+* Q') (x : σ → Q)
    (P : MvPolynomial σ Q) :
    R (MvPolynomial.eval x P) = MvPolynomial.eval (fun i => R (x i)) (MvPolynomial.map R P) := by
  rw [MvPolynomial.eval_map]
  show R (MvPolynomial.eval₂ (RingHom.id Q) x P) = _
  rw [MvPolynomial.hom_eval₂, RingHom.comp_id]

theorem hasVal_add_smul_map : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (z : σ → B) (f g : MvPowerSeries σ Q) (q r : Q), HasVal p z f q → (HasVal p z g r → HasVal p z (f + g) (q + r)) ∧ (∀ c : Q, HasVal p z (c • f) (c * q)) ∧ ∀ (B' Q' : Type) [CommRing B'] [CommRing Q'] [Algebra B' Q'] (ρ : B →+* B') (R : Q →+* Q'), (∀ b, R (algebraMap B Q b) = algebraMap B' Q' (ρ b)) → HasVal p (fun i => ρ (z i)) (map R f) (R q) := by
  intro p _ B O Q _ _ _ _ θ hF σ _ _ z f g q r hf
  refine ⟨?_, ?_, ?_⟩
  · intro hg m
    obtain ⟨N₁, h₁⟩ := hf m
    obtain ⟨N₂, h₂⟩ := hg m
    refine ⟨max N₁ N₂, fun N' hN => ?_⟩
    obtain ⟨b₁, hb₁⟩ := h₁ N' (le_trans (le_max_left _ _) hN)
    obtain ⟨b₂, hb₂⟩ := h₂ N' (le_trans (le_max_right _ _) hN)
    refine ⟨b₁ + b₂, ?_⟩
    rw [map_add (f := _), map_add (f := _), mul_add, map_add (f := _), ← hb₁, ← hb₂]
    ring
  · intro c m
    obtain ⟨k, b₀, hk⟩ := hF.denom c
    obtain ⟨N, h⟩ := hf (m + k)
    refine ⟨N, fun N' hN => ?_⟩
    obtain ⟨b, hb⟩ := h N' hN
    refine ⟨b₀ * b, ?_⟩
    rw [map_smul, MvPolynomial.smul_eval]
    have e : c * q - c * MvPolynomial.eval (fun i => algebraMap B Q (z i))
        (trunc' Q (Finsupp.equivFunOnFinite.symm fun _ => N') f)
        = c * algebraMap B Q (p ^ (m + k) * b) := by rw [← hb]; ring
    rw [e]
    simp only [map_mul, map_pow, map_natCast] at hk ⊢
    rw [← hk]
    ring
  · intro B' Q' _ _ _ ρ R hR m
    obtain ⟨N, h⟩ := hf m
    refine ⟨N, fun N' hN => ?_⟩
    obtain ⟨b, hb⟩ := h N' hN
    refine ⟨ρ b, ?_⟩
    rw [trunc'_map]
    have := congrArg R hb
    rw [map_sub, eval_map_hom, hR] at this
    simp only [hR] at this
    rw [this]
    simp

end GlobalTheory.QLog.ValLin
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory

theorem eval_coe_polynomial_of_isEval {p : ℕ} {B : Type} [CommRing B] {σ : Type}
    (z : σ → B) (E : MvPowerSeries σ B →ₐ[B] B) (hE : IsEval p z E) (P : MvPolynomial σ B) :
    E (P : MvPowerSeries σ B) = MvPolynomial.eval z P := by
  have h : E.comp (MvPolynomial.coeToMvPowerSeries.algHom B) = MvPolynomial.aeval z := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [MvPolynomial.coeToMvPowerSeries.algHom_apply, hE.1 i]
  have := congrArg (fun φ => φ P) h
  simpa [MvPolynomial.coeToMvPowerSeries.algHom_apply] using this

theorem hasVal_map_of_isEval : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (z : σ → B), (∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N) → ∀ E : MvPowerSeries σ B →ₐ[B] B, IsEval p z E → ∀ s : MvPowerSeries σ B, HasVal p z (map (algebraMap B Q) s) (algebraMap B Q (E s)) := by
  intro p _ B O Q _ _ _ _ θ _ σ _ _ z _ E hE s m
  obtain ⟨N, hN⟩ := hE.2 m
  refine ⟨N, fun N' hN' => ?_⟩
  set n : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => N'
  have hdiv : (p : B) ^ m ∣ E (s - (trunc' B n s : MvPowerSeries σ B)) := by
    apply hN
    intro α hα
    have hle : α ≤ n := by
      intro i
      have h1 : α i ≤ α.degree := by
        classical
        rw [Finsupp.degree]
        by_cases hi : i ∈ α.support
        · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
        · simp [Finsupp.notMem_support_iff.1 hi]
      show α i ≤ N'
      omega
    rw [map_sub, MvPolynomial.coeff_coe, coeff_trunc', if_pos hle, sub_self]
  obtain ⟨b, hb⟩ := hdiv
  refine ⟨b, ?_⟩
  rw [map_sub, eval_coe_polynomial_of_isEval z E hE] at hb
  have key : algebraMap B Q (MvPolynomial.eval z (trunc' B n s)) =
      MvPolynomial.eval₂ (algebraMap B Q) (fun i => algebraMap B Q (z i)) (trunc' B n s) := by
    rw [MvPolynomial.eval, MvPolynomial.coe_eval₂Hom]
    exact MvPolynomial.eval₂_comp_left _ _ _ _
  rw [trunc'_map, MvPolynomial.eval_map, ← key, ← map_sub, hb]

end GlobalTheory
end
