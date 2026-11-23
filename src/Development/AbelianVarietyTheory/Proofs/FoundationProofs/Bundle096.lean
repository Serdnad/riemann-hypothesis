module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle032
public import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle062
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle064
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003

@[expose] public section

section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

noncomputable section

namespace GlobalTheory.Glue.EvRing

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]


variable (p Ω) in
def zpH : ℤ_[p] →+* Ω := (algebraMap (O0 p) Ω).comp ((algebraMap (Lau p) (O0 p)).comp HahnSeries.C)

theorem zp_eq (z : ℤ_[p]) : zp Ω z = zpH (p := p) (Ω := Ω) z := rfl

theorem thL_coeff (a : Lau p) (r : ℤ) : (thL a).coeff r = (r : ℤ_[p]) * a.coeff r := rfl

theorem thL_mul (a b : Lau p) : thL (a * b) = thL a * b + a * thL b := by
  apply HahnSeries.ext
  funext r
  have hs : (thL a).support ⊆ a.support := fun i hi h => hi (by simp [thL_coeff, h])
  have ht : (thL b).support ⊆ b.support := fun i hi h => hi (by simp [thL_coeff, h])
  rw [HahnSeries.coeff_add, HahnSeries.coeff_mul_left' a.isPWO_support hs,
    HahnSeries.coeff_mul_right' b.isPWO_support ht, thL_coeff,
    HahnSeries.coeff_mul (x := a) (y := b), Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ij hij => ?_
  rw [Finset.mem_antidiagonal] at hij
  rw [thL_coeff, thL_coeff, ← hij.2.2]
  push_cast
  ring

theorem thL_neg (a : Lau p) : thL (-a) = -thL a := by
  ext r
  simp [thL_coeff]

theorem ev_of_fintype {ι : Type} [Fintype ι] (ψ : O0 p →+* Ω) (c : ℤ → Ω) (x x' : Ω) (e : ι → Ω)
    (a : ι → Lau p) (he : ∀ t, IsInt (p := p) (e t) ∧ IsAlgZp (p := p) (e t))
    (hc : ∀ r, c r = ∑ t, e t * zp Ω ((a t).coeff r))
    (hx : x = ∑ t, e t * ψ (algebraMap (Lau p) (O0 p) (a t)))
    (hx' : x' = ∑ t, e t * ψ (algebraMap (Lau p) (O0 p) (thL (a t)))) : GlobalTheory.Glue.Ev ψ c x x' := by
  let σ := Fintype.equivFin ι
  refine ⟨Fintype.card ι, e ∘ σ.symm, a ∘ σ.symm, fun t => he _, fun r => ?_, ?_, ?_⟩
  · rw [hc r]; exact (Equiv.sum_comp σ.symm (fun t => e t * zp Ω ((a t).coeff r))).symm
  · rw [hx]; exact (Equiv.sum_comp σ.symm (fun t => e t * ψ (algebraMap (Lau p) (O0 p) (a t)))).symm
  · rw [hx']; exact (Equiv.sum_comp σ.symm (fun t => e t * ψ (algebraMap (Lau p) (O0 p) (thL (a t))))).symm

theorem repr {d : ℕ} (e : Fin d → Ω) (a : Fin d → Lau p) (C : HahnSeries ℤ Ω)
    (h : ∀ r, C.coeff r = ∑ t, e t * zp Ω ((a t).coeff r)) :
    C = ∑ t, HahnSeries.C (e t) * (a t).map (zpH (p := p) (Ω := Ω)).toNonUnitalRingHom := by
  ext r
  rw [h r, HahnSeries.coeff_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, HahnSeries.map_coeff]
  rfl

theorem isAlgZp_mul {x y : Ω} (hx : IsAlgZp (p := p) x) (hy : IsAlgZp (p := p) y) :
    IsAlgZp (p := p) (x * y) := by
  let : Algebra ℤ_[p] Ω := ((algebraMap (O0 p) Ω).comp (algebraMap ℤ_[p] (O0 p))).toAlgebra
  have : IsScalarTower ℤ_[p] (O0 p) Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have key : ∀ z : Ω, IsAlgZp (p := p) z ↔ IsAlgebraic ℤ_[p] z := by
    intro z; simp only [IsAlgZp, IsAlgebraic, Polynomial.aeval_map_algebraMap]
  rw [key] at hx hy ⊢
  exact hx.mul hy

theorem isAlgZp_gal (g : Gal p Ω) {x : Ω} (hx : IsAlgZp (p := p) x) : IsAlgZp (p := p) (g x) := by
  obtain ⟨P, hP, h⟩ := hx
  exact ⟨P, hP, by rw [Polynomial.aeval_algHom_apply, h, map_zero]⟩

end GlobalTheory.Glue.EvRing

namespace GlobalTheory.Glue.EvRing


open GlobalTheory.K5.Basic in
theorem ev_ring : ∀ (p : ℕ) [Fact p.Prime], ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ (T : GlobalTheory.K5.Tower p Ω) (n : ℕ), ∀ (ψ : O0 p →+* Ω), IsReb T n ψ →
    (∀ (C D : HahnSeries ℤ Ω) (x x' y y' : Ω),
      GlobalTheory.Glue.Ev ψ C.coeff x x' → GlobalTheory.Glue.Ev ψ D.coeff y y' →
      GlobalTheory.Glue.Ev ψ (C * D).coeff (x * y) (x' * y + x * y') ∧
      GlobalTheory.Glue.Ev ψ (C + D).coeff (x + y) (x' + y') ∧
      GlobalTheory.Glue.Ev ψ (C - D).coeff (x - y) (x' - y')) ∧
    (∀ (c : ℤ → Ω) (x x' : Ω), GlobalTheory.Glue.Ev ψ c x x' →
      IsInt (p := p) x ∧ IsInt (p := p) x' ∧ (∃ C : HahnSeries ℤ Ω, C.coeff = c) ∧
      (∃ x'', GlobalTheory.Glue.Ev ψ (fun r => (r : Ω) * c r) x' x'') ∧
      (∀ e : Ω, IsInt (p := p) e → IsAlgZp (p := p) e →
        GlobalTheory.Glue.Ev ψ (fun r => e * c r) (e * x) (e * x')) ∧
      ∀ g : Gal p Ω, g (T.qq n) = T.qq n → GlobalTheory.Glue.Ev ψ (fun r => g (c r)) (g x) (g x')) := by
  intro p hp Ω _ _ _ T n ψ hreb
  refine ⟨?_, ?_⟩
  · rintro C D x x' y y' ⟨d, e, a, he, hc, hx, hx'⟩ ⟨d', f, b, hf, hd, hy, hy'⟩
    refine ⟨?_, ?_, ?_⟩
    · refine ev_of_fintype (ι := Fin d × Fin d') ψ _ _ _ (fun ts => e ts.1 * f ts.2)
        (fun ts => a ts.1 * b ts.2) (fun ts => ⟨IsIntegral.mul (he _).1 (hf _).1, isAlgZp_mul (he _).2 (hf _).2⟩)
        (fun r => ?_) ?_ ?_
      · rw [repr e a C hc, repr f b D hd, Finset.sum_mul_sum, HahnSeries.coeff_sum, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [HahnSeries.coeff_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [show HahnSeries.C (e t) * (a t).map (zpH (p := p) (Ω := Ω)).toNonUnitalRingHom *
            (HahnSeries.C (f s) * (b s).map (zpH (p := p) (Ω := Ω)).toNonUnitalRingHom) =
            HahnSeries.C (e t * f s) * (a t * b s).map (zpH (p := p) (Ω := Ω)).toNonUnitalRingHom by
          rw [HahnSeries.map_mul, map_mul]; ring]
        rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, HahnSeries.map_coeff]
        rfl
      · rw [hx, hy, Finset.sum_mul_sum, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => ?_
        simp only [map_mul]
        ring
      · rw [hx, hx', hy, hy', Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib,
          Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun s _ => ?_
        simp only [thL_mul, map_add (f := _), map_mul]
        ring
    · refine ev_of_fintype (ι := Fin d ⊕ Fin d') ψ _ _ _ (Sum.elim e f) (Sum.elim a b)
        (by rintro (t | t) <;> simp [he, hf]) (fun r => ?_) ?_ ?_
      · simp [Fintype.sum_sum_type, hc, hd]
      · simp [Fintype.sum_sum_type, hx, hy]
      · simp [Fintype.sum_sum_type, hx', hy']
    · refine ev_of_fintype (ι := Fin d ⊕ Fin d') ψ _ _ _ (Sum.elim e f) (Sum.elim a fun s => -b s)
        (by rintro (t | t) <;> simp [he, hf]) (fun r => ?_) ?_ ?_
      · simp [Fintype.sum_sum_type, hc, hd, zp_eq, sub_eq_add_neg]
      · simp [Fintype.sum_sum_type, hx, hy, sub_eq_add_neg]
      · simp [Fintype.sum_sum_type, hx', hy', thL_neg, sub_eq_add_neg]
  · rintro c x x' ⟨d, e, a, he, hc, hx, hx'⟩
    have hpow : T.qq n ^ (p ^ n) = algebraMap (O0 p) Ω (qO p) := by
      clear hreb
      induction n with
      | zero => simp [T.q0]
      | succ n ih => rw [pow_succ', pow_mul, T.qpow, ih]
    have hq : IsIntegral (O0 p) (T.qq n) :=
      IsIntegral.of_pow (pow_pos hp.out.pos n) (hpow ▸ isIntegral_algebraMap)
    have hmem : ∀ y, ψ y ∈ Algebra.adjoin (O0 p) {T.qq n} := fun y => by
      have : ψ y ∈ ψ.range := ⟨y, rfl⟩
      rw [hreb.rng] at this
      exact this
    have hint : ∀ y, IsInt (p := p) (ψ y) := fun y => adjoin_le_integralClosure hq (hmem y)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hx]; exact IsIntegral.sum _ fun t _ => IsIntegral.mul (he t).1 (hint _)
    · rw [hx']; exact IsIntegral.sum _ fun t _ => IsIntegral.mul (he t).1 (hint _)
    · refine ⟨∑ t, HahnSeries.C (e t) * (a t).map (zpH (p := p) (Ω := Ω)).toNonUnitalRingHom, funext fun r => ?_⟩
      rw [hc r, HahnSeries.coeff_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, HahnSeries.map_coeff]
      rfl
    · refine ⟨_, ev_of_fintype ψ _ x' _ e (fun t => thL (a t)) he (fun r => ?_) hx' rfl⟩
      rw [hc r, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [thL_coeff, zp_eq, zp_eq, map_mul, map_intCast]
      ring
    · intro e0 hi ha
      refine ev_of_fintype ψ _ _ _ (fun t => e0 * e t) a
        (fun t => ⟨IsIntegral.mul hi (he t).1, isAlgZp_mul ha (he t).2⟩) (fun r => ?_) ?_ ?_
      · rw [hc r, Finset.mul_sum]
        exact Finset.sum_congr rfl fun t _ => by ring
      · rw [hx, Finset.mul_sum]
        exact Finset.sum_congr rfl fun t _ => by ring
      · rw [hx', Finset.mul_sum]
        exact Finset.sum_congr rfl fun t _ => by ring
    · intro g hg
      have hfix : ∀ y, g (ψ y) = ψ y := fun y =>
        (AlgHom.eqOn_adjoin_iff (φ := (g : Ω →ₐ[O0 p] Ω)) (ψ := AlgHom.id (O0 p) Ω) (s := {T.qq n})).2
          (by intro z hz; rw [Set.mem_singleton_iff] at hz; subst hz; exact hg) (hmem y)
      have hint_gal : ∀ t, IsInt (p := p) (g (e t)) := fun t =>
        IsIntegral.map g.toAlgHom (he t).1
      refine ev_of_fintype ψ _ _ _ (fun t => g (e t)) a
        (fun t => ⟨hint_gal t, isAlgZp_gal g (he t).2⟩) (fun r => ?_) ?_ ?_

      · rw [hc r, map_sum]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [map_mul]
        congr 1
        exact g.commutes _

      · rw [hx, map_sum]
        exact Finset.sum_congr rfl fun t _ => by rw [map_mul, hfix]

      · rw [hx', map_sum]
        exact Finset.sum_congr rfl fun t _ => by rw [map_mul, hfix]

end GlobalTheory.Glue.EvRing
end
end

section

noncomputable section

open GlobalTheory.K5 GlobalTheory.Glue

namespace GlobalTheory.GeoFix

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

def InR (ψ : O0 p →+* Ω) (y : Ω) : Prop :=
  ∃ (d : ℕ) (e : Fin d → Ω) (b : Fin d → O0 p),
    (∀ t, IsInt (p := p) (e t) ∧ IsAlgZp (p := p) (e t)) ∧
    y = ∑ t, e t * ψ (b t)

variable (p Ω) in
abbrev zpAlg : Algebra ℤ_[p] Ω := ((algebraMap (O0 p) Ω).comp (algebraMap ℤ_[p] (O0 p))).toAlgebra

theorem isAlgZp_iff (x : Ω) : IsAlgZp (p := p) x ↔ @IsAlgebraic ℤ_[p] Ω _ _ (zpAlg p Ω) x := by
  letI := zpAlg p Ω
  haveI : IsScalarTower ℤ_[p] (O0 p) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  unfold IsAlgZp IsAlgebraic
  simp only [Polynomial.aeval_map_algebraMap]

theorem isAlgZp_mul {x y : Ω} (hx : IsAlgZp (p := p) x) (hy : IsAlgZp (p := p) y) :
    IsAlgZp (p := p) (x * y) := by
  letI := zpAlg p Ω
  rw [isAlgZp_iff] at hx hy ⊢
  exact hx.mul hy

theorem isAlgZp_one : IsAlgZp (p := p) (1 : Ω) := by
  letI := zpAlg p Ω
  rw [isAlgZp_iff]
  exact isAlgebraic_one

theorem isInt_psi {T : Tower p Ω} {n : ℕ} {ψ : O0 p →+* Ω} (h : IsReb T n ψ) (b : O0 p) :
    IsInt (p := p) (ψ b) := by
  have hq : IsIntegral (O0 p) (T.qq n) := by
    refine ⟨Polynomial.X ^ (p ^ n) - Polynomial.C (qO p),
      Polynomial.monic_X_pow_sub_C _ (pow_ne_zero _ hp.out.ne_zero), ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, Basic.qq_pow, sub_self]
  have hb : ψ b ∈ ψ.range := ⟨b, rfl⟩
  rw [h.rng] at hb
  exact adjoin_le_integralClosure hq hb

theorem inR_zero (ψ : O0 p →+* Ω) : InR ψ 0 :=
  ⟨0, Fin.elim0, Fin.elim0, fun t => t.elim0, by simp⟩

theorem inR_psi (ψ : O0 p →+* Ω) (b : O0 p) : InR ψ (ψ b) :=
  ⟨1, fun _ => 1, fun _ => b, fun _ => ⟨isIntegral_one, isAlgZp_one⟩, by simp⟩

theorem inR_add {ψ : O0 p →+* Ω} {x y : Ω} (hx : InR ψ x) (hy : InR ψ y) : InR ψ (x + y) := by
  obtain ⟨d, e, b, he, rfl⟩ := hx
  obtain ⟨d', e', b', he', rfl⟩ := hy
  refine ⟨d + d', Fin.append e e', Fin.append b b', fun t => ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) t
    · simpa using he i
    · simpa using he' i
  · rw [Fin.sum_univ_add]
    simp

theorem inR_sum {ψ : O0 p →+* Ω} {ι : Type*} (s : Finset ι) (f : ι → Ω) (hf : ∀ i ∈ s, InR ψ (f i)) :
    InR ψ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using inR_zero ψ
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact inR_add (hf a (Finset.mem_insert_self a s)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem inR_mul {ψ : O0 p →+* Ω} {x y : Ω} (hx : InR ψ x) (hy : InR ψ y) : InR ψ (x * y) := by
  obtain ⟨d, e, b, he, rfl⟩ := hx
  obtain ⟨d', e', b', he', rfl⟩ := hy
  rw [Finset.sum_mul_sum]
  refine inR_sum _ _ fun i _ => inR_sum _ _ fun j _ => ?_
  refine ⟨1, fun _ => e i * e' j, fun _ => b i * b' j,
    fun _ => ⟨IsIntegral.mul (he i).1 (he' j).1, isAlgZp_mul (he i).2 (he' j).2⟩, ?_⟩
  simp only [Finset.univ_unique, Finset.sum_singleton, map_mul]
  ring

theorem inR_neg {ψ : O0 p →+* Ω} {x : Ω} (hx : InR ψ x) : InR ψ (-x) := by
  have := inR_mul (inR_psi ψ (-1)) hx
  simpa using this

theorem InR.isInt {T : Tower p Ω} {n : ℕ} {ψ : O0 p →+* Ω} (h : IsReb T n ψ) {x : Ω} (hx : InR ψ x) :
    IsInt (p := p) x := by
  obtain ⟨d, e, b, he, rfl⟩ := hx
  exact IsIntegral.sum _ fun t _ => IsIntegral.mul (he t).1 (isInt_psi h (b t))

theorem algebraMap_zp_injective : Function.Injective (algebraMap ℤ_[p] (O0 p)) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro m hm
  by_contra h0
  rw [PadicInt.unitCoeff_spec h0, map_mul, map_pow, map_natCast] at hm
  have hu : algebraMap ℤ_[p] (O0 p) ((PadicInt.unitCoeff h0 : ℤ_[p])) ≠ 0 :=
    ((Units.isUnit (PadicInt.unitCoeff h0)).map (algebraMap ℤ_[p] (O0 p))).ne_zero
  have hp0 : (p : O0 p) ^ m.valuation ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hp.out.ne_zero)
  exact mul_ne_zero hu hp0 hm

theorem exists_inR_of_isAlgZp (hc : IsClo p Ω) {T : Tower p Ω} {n : ℕ} {ψ : O0 p →+* Ω} (h : IsReb T n ψ) {x : Ω}
    (hx : IsAlgZp (p := p) x) : ∃ D : O0 p, D ≠ 0 ∧ InR ψ (x * ψ D) := by
  letI := zpAlg p Ω
  haveI : IsScalarTower ℤ_[p] (O0 p) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hx' := (isAlgZp_iff x).1 hx
  obtain ⟨y, hy0, hyi⟩ := hx'.exists_integral_multiple
  set c : O0 p := algebraMap ℤ_[p] (O0 p) y with hcdef
  have hmem : algebraMap (O0 p) Ω c ∈ ψ.range := by
    rw [h.rng]
    exact Subalgebra.algebraMap_mem _ c
  obtain ⟨D, hD⟩ := hmem
  have hc0 : c ≠ 0 := fun h0 => hy0 (algebraMap_zp_injective (by rw [← hcdef, h0, map_zero]))
  refine ⟨D, ?_, 1, fun _ => y • x, fun _ => 1, fun _ => ⟨?_, ?_⟩, ?_⟩
  · rintro rfl
    rw [map_zero] at hD
    exact hc0 (hc.inj (by rw [← hD, map_zero]))
  · exact hyi.tower_top
  · rw [isAlgZp_iff, Algebra.smul_def]
    exact (isAlgebraic_algebraMap y).mul hx'
  · simp only [Finset.univ_unique, Finset.sum_singleton, map_one, mul_one]
    rw [hD, Algebra.smul_def, IsScalarTower.algebraMap_apply ℤ_[p] (O0 p) Ω, mul_comm]

theorem algebraMap_zp_eq (m : ℤ_[p]) :
    algebraMap ℤ_[p] (O0 p) m = algebraMap (Lau p) (O0 p) (HahnSeries.C m) := by
  have hH := (o0_isAdicComplete_span_p p).toIsHausdorff
  refine sub_eq_zero.1 (hH.haus' _ fun K => ?_)
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have hs := PadicInt.appr_spec K m
  rw [Ideal.mem_span_singleton] at hs
  obtain ⟨u, hu⟩ := hs
  have hm : m = (m.appr K : ℤ_[p]) + (p : ℤ_[p]) ^ K * u := by rw [← hu]; ring
  refine ⟨algebraMap ℤ_[p] (O0 p) u - algebraMap (Lau p) (O0 p) (HahnSeries.C u), ?_⟩
  conv_lhs => rw [hm]
  simp only [map_add (f := _), map_mul, map_pow, map_natCast]
  ring

theorem isAlgZp_zp (m : ℤ_[p]) : IsAlgZp (p := p) (zp Ω m) := by
  refine ⟨Polynomial.X - Polynomial.C m, Polynomial.X_sub_C_ne_zero m, ?_⟩
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
    zp, algebraMap_zp_eq, HahnSeries.C_apply, sub_self]

theorem isAlgZp_add {x y : Ω} (hx : IsAlgZp (p := p) x) (hy : IsAlgZp (p := p) y) :
    IsAlgZp (p := p) (x + y) := by
  letI := zpAlg p Ω
  rw [isAlgZp_iff] at hx hy ⊢
  exact hx.add hy

end GlobalTheory.GeoFix
end
end

section

noncomputable section

open PowerSeries

namespace GlobalTheory.Col

theorem trace_basis_pow {B A : Type} [CommRing B] [CommRing A] [Algebra B A] (p : ℕ)
    (b : Module.Basis (Fin p) B A) (x : A) (y : B) (hb : ∀ i, b i = x ^ (i : ℕ))
    (hx : x ^ p = algebraMap B A y) (i : Fin p) :
    Algebra.trace B A (b i) = if (i : ℕ) = 0 then (p : B) else 0 := by
  rw [Algebra.trace_eq_matrix_trace b, Matrix.trace]
  have hd : ∀ j : Fin p, Algebra.leftMulMatrix b (b i) j j = if (i : ℕ) = 0 then 1 else 0 := by
    intro j
    rw [Algebra.leftMulMatrix_eq_repr_mul, hb i, hb j, ← pow_add]
    by_cases h : (i : ℕ) + j < p
    · rw [← hb ⟨_, h⟩, b.repr_self, Finsupp.single_apply]
      by_cases hi : (i : ℕ) = 0
      · rw [if_pos hi, if_pos (Fin.ext (by simp only [Fin.val_mk]; omega))]
      · rw [if_neg hi, if_neg (fun h' => hi (by have := congrArg Fin.val h'; simp only [Fin.val_mk] at this; omega))]
    · have e : x ^ ((i : ℕ) + j) = y • b ⟨(i : ℕ) + j - p, by omega⟩ := by
        rw [hb, Algebra.smul_def, ← hx, ← pow_add]
        congr 1
        simp only [Fin.val_mk]
        omega
      rw [e, map_smul, b.repr_self, Finsupp.smul_apply, Finsupp.single_apply, if_neg, smul_zero, if_neg]
      · omega
      · simp only [Fin.ext_iff]
        omega
  simp only [Matrix.diag, hd]
  split_ifs <;> simp

theorem trace_eq_p_mul {B A : Type} [CommRing B] [CommRing A] [Algebra B A] (p : ℕ) (hp : 0 < p)
    (b : Module.Basis (Fin p) B A) (x : A) (y : B) (hb : ∀ i, b i = x ^ (i : ℕ))
    (hx : x ^ p = algebraMap B A y) (s : A) :
    Algebra.trace B A s = (p : B) * b.repr s ⟨0, hp⟩ := by
  conv_lhs => rw [← b.sum_repr s]

  rw [map_sum]
  simp only [map_smul, trace_basis_pow p b x y hb hx, smul_eq_mul]
  rw [Finset.sum_eq_single ⟨0, hp⟩]
  · simp [mul_comm]
  · intro j _ hj
    rw [if_neg, mul_zero]
    intro h0
    exact hj (Fin.ext h0)
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem norm_one_add_pow_mul {B A : Type} [CommRing B] [CommRing A] [Algebra B A] (p : ℕ) (hp : 0 < p)
    (b : Module.Basis (Fin p) B A) (x : A) (y : B) (hb : ∀ i, b i = x ^ (i : ℕ))
    (hx : x ^ p = algebraMap B A y) (s : A) (k : ℕ) (hk : 1 ≤ k) :
    ∃ t : B, Algebra.norm B (1 + (p : A) ^ k * s) = 1 + (p : B) ^ (k + 1) * t := by
  have e : (p : A) ^ k * s = ((p : B) ^ k) • s := by
    rw [Algebra.smul_def, map_pow, map_natCast]
  rw [e, Algebra.norm_eq_matrix_det b, map_add (f := _), map_one, map_smul, Matrix.det_one_add_smul,
    ← Algebra.trace_eq_matrix_trace b, trace_eq_p_mul p hp b x y hb hx]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  refine ⟨b.repr s ⟨0, hp⟩ + (Matrix.det (1 + (Polynomial.X : Polynomial B) •
    (Algebra.leftMulMatrix b s).map Polynomial.C)).divX.divX.eval (((p : B)) ^ (m + 1)) * (p : B) ^ m, ?_⟩
  ring

theorem normOp_congr_of_basis (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime]
    (b : @Module.Basis (Fin p) (PowerSeries R) (PowerSeries R) _ _
      ((phi (R := R) p hp.out.pos).toRingHom.toAlgebra.toModule))
    (hb : ∀ i, b i = (1 + X : PowerSeries R) ^ (i : ℕ))
    (h₁ h₂ r : PowerSeries R) (k : ℕ) (hk : 1 ≤ k) (hu : IsUnit h₂)
    (he : h₁ = h₂ + (p : PowerSeries R) ^ k * r) :
    ∃ r' : PowerSeries R, normOp p h₁ = normOp p h₂ + (p : PowerSeries R) ^ (k + 1) * r' := by
  letI inst : Algebra (PowerSeries R) (PowerSeries R) := (phi (R := R) p hp.out.pos).toRingHom.toAlgebra
  have hx : (1 + X : PowerSeries R) ^ p = algebraMap (PowerSeries R) (PowerSeries R) (1 + X) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact (phi_one_add_X (R := R) p hp.out.pos).symm
  have hN : ∀ z, normOp p z = Algebra.norm (PowerSeries R) z := fun z => rfl
  obtain ⟨u, rfl⟩ := hu
  have h1 : h₁ = (u : PowerSeries R) * (1 + (p : PowerSeries R) ^ k * ((↑u⁻¹ : PowerSeries R) * r)) := by
    have hui := u.mul_inv
    linear_combination he - ((p : PowerSeries R) ^ k * r) * hui
  obtain ⟨t, ht⟩ := @norm_one_add_pow_mul (PowerSeries R) (PowerSeries R) _ _ inst p hp.out.pos b (1 + X) (1 + X)
    hb hx ((↑u⁻¹ : PowerSeries R) * r) k hk
  refine ⟨normOp p (u : PowerSeries R) * t, ?_⟩
  rw [h1, hN, hN, map_mul, ht]
  ring

end GlobalTheory.Col
end
end

section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion

theorem _root_.GlobalTheory.T.tower_exp_slash_upperTriangular_eq_subst : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (g : GQ), ent g 1 0 = 0 → ∀ f : X.K,
  X.exp (X.sl g f) = sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) (X.exp f) := by
  first | exact @GlobalTheory.CyclotomicQExpansion.exp_sl_upper | exact GlobalTheory.CyclotomicQExpansion.exp_sl_upper | (intros; apply GlobalTheory.CyclotomicQExpansion.exp_sl_upper <;> assumption)
end

section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion

theorem _root_.GlobalTheory.T.hahnSeriesQDerivative_substUpperTriangular : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (a b d : ℚ), 0 < a / d → ∀ φ : HahnSeries ℚ Ω,
  qD (sub ε a b d φ) = HahnSeries.C (algebraMap ℚ Ω (a / d)) * sub ε a b d (qD φ) := by
  first | exact @GlobalTheory.CyclotomicQExpansion.qD_sub | exact GlobalTheory.CyclotomicQExpansion.qD_sub | (intros; apply GlobalTheory.CyclotomicQExpansion.qD_sub <;> assumption)
end
