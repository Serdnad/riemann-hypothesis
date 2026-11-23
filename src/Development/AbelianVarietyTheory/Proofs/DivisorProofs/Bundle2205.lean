module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle058
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2176
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticChangeOfGoodModelsIntertwines
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle266

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LKGeo.LaHatMod

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped TensorProduct

theorem valued_algebraMap (w : HeightOneSpectrum ℤ) (q : ℚ) :
    Valued.v (algebraMap ℚ (w.adicCompletion ℚ) q) = w.valuation ℚ q :=
  valuedAdicCompletion_eq_valuation' w q

theorem exists_int_valued_sub_le (w : HeightOneSpectrum ℤ) {x : w.adicCompletion ℚ} (hx : Valued.v x ≤ 1)
    {c : ℚ} (hc0 : c ≠ 0) (hc : w.valuation ℚ c ≤ 1) :
    ∃ r : ℤ, Valued.v (x - (r : w.adicCompletion ℚ)) ≤ w.valuation ℚ c := by
  set c' : w.adicCompletion ℚ := algebraMap ℚ (w.adicCompletion ℚ) c
  have hc' : c' ≠ 0 := by
    simp only [c', ne_eq, map_eq_zero_iff _ (algebraMap ℚ (w.adicCompletion ℚ)).injective]; exact hc0
  have hpos : (0 : WithZero (Multiplicative ℤ)) < Valued.v c' := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hc')
  have hU : IsOpen ((fun y => (y - x) / c') ⁻¹' (w.adicCompletionIntegers ℚ : Set (w.adicCompletion ℚ))) :=
    (Valued.isOpen_valuationSubring _).preimage ((continuous_id.sub continuous_const).div_const c')
  obtain ⟨k, hk⟩ := (denseRange_algebraMap (K := ℚ) w).exists_mem_open hU
    ⟨x, by simp [SetLike.mem_coe, sub_self, zero_div]⟩
  have hk' : Valued.v (x - algebraMap ℚ (w.adicCompletion ℚ) k) ≤ w.valuation ℚ c := by
    have h : Valued.v ((algebraMap ℚ (w.adicCompletion ℚ) k - x) / c') ≤ 1 := hk
    rw [map_div₀, div_le_one₀ hpos] at h
    rw [Valuation.map_sub_swap, ← valued_algebraMap]; exact h
  have hk1 : w.valuation ℚ k ≤ 1 := by
    rw [← valued_algebraMap]
    have e : algebraMap ℚ (w.adicCompletion ℚ) k = x - (x - algebraMap ℚ (w.adicCompletion ℚ) k) := by ring
    rw [e]
    exact (Valuation.map_sub _ _ _).trans (max_le hx (hk'.trans hc))
  have hne : w.valuation ℚ c ≠ 0 := (Valuation.ne_zero_iff _).2 hc0
  obtain ⟨r, hr⟩ := exists_valuation_sub_lt_of_integer w hk1 (Units.mk0 _ hne)
  refine ⟨r, ?_⟩
  have hr' : Valued.v (algebraMap ℚ (w.adicCompletion ℚ) (k - algebraMap ℤ ℚ r)) ≤ w.valuation ℚ c := by
    rw [valued_algebraMap, Valuation.map_sub_swap]; exact hr.le
  have e : x - (r : w.adicCompletion ℚ) =
      (x - algebraMap ℚ (w.adicCompletion ℚ) k) + algebraMap ℚ (w.adicCompletion ℚ) (k - algebraMap ℤ ℚ r) := by
    rw [map_sub, algebraMap_int_eq, eq_intCast, map_intCast]; ring
  rw [e]
  exact (Valuation.map_add _ _ _).trans (max_le hk' hr')

variable {p : ℕ} [Fact p.Prime]

theorem valued_intCast (w : HeightOneSpectrum ℤ) (z : ℤ) :
    Valued.v ((z : w.adicCompletion ℚ)) ≤ 1 := by
  rw [← map_intCast (algebraMap ℚ (w.adicCompletion ℚ)), valued_algebraMap]
  have := w.valuation_le_one (K := ℚ) z
  simpa using this

theorem exists_int_add_prime_mul (l : ℕ) (hl : l.Prime) (hlp : l ≠ p) (a : AfP p) (ha : IsIntAf a) :
    ∃ (z : ℤ) (a' : AfP p), IsIntAf a' ∧ a = (z : AfP p) + (l : AfP p) * a' := by
  have hmax : (Ideal.span {(l : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hl).irreducible
  have hl0 : (l : ℤ) ≠ 0 := by exact_mod_cast hl.ne_zero
  let w0 : HeightOneSpectrum ℤ := ⟨Ideal.span {(l : ℤ)}, hmax.isPrime, by simpa using hl0⟩
  have hw0 : w0.asIdeal ≠ Ideal.span {(p : ℤ)} := by
    intro h
    have hp : (p : ℤ) ∈ Ideal.span {(l : ℤ)} := by
      change (p : ℤ) ∈ w0.asIdeal; rw [h]; exact Ideal.mem_span_singleton_self _
    rw [Ideal.mem_span_singleton] at hp
    have hd : l ∣ p := by exact_mod_cast hp
    rcases (Nat.Prime.eq_one_or_self_of_dvd (Fact.out : p.Prime) l hd) with h1 | h1
    · exact hl.ne_one h1
    · exact hlp h1
  let v0 : AwayP p := ⟨w0, hw0⟩
  have hlq0 : (l : ℚ) ≠ 0 := by exact_mod_cast hl.ne_zero
  have hlv : ∀ w : HeightOneSpectrum ℤ, w.valuation ℚ (l : ℚ) ≤ 1 := fun w => by
    have := w.valuation_le_one (K := ℚ) (l : ℤ); simpa using this
  obtain ⟨z, hz⟩ := exists_int_valued_sub_le w0 (ha v0) hlq0 (hlv w0)
  refine ⟨z, (a - (z : AfP p)) * algebraMap ℚ (AfP p) (l : ℚ)⁻¹, ?_, ?_⟩
  · intro v
    rw [mem_adicCompletionIntegers, map_mul, map_sub, map_intCast, AlgHom.commutes, Valuation.map_mul,
      valued_algebraMap, map_inv₀]
    have hne : v.1.valuation ℚ (l : ℚ) ≠ 0 := (Valuation.ne_zero_iff _).2 hlq0
    by_cases hv : v = v0
    · subst hv
      rw [mul_inv_le_iff₀ (zero_lt_iff.2 hne), _root_.one_mul]
      exact hz
    · have hnot : (l : ℤ) ∉ v.1.asIdeal := by
        intro hm
        apply hv
        have hle : Ideal.span {(l : ℤ)} ≤ v.1.asIdeal := (Ideal.span_singleton_le_iff_mem _).2 hm
        have heq := hmax.eq_of_le v.1.isPrime.ne_top hle
        exact Subtype.ext (HeightOneSpectrum.ext heq.symm)
      have h1 : v.1.valuation ℚ (l : ℚ) = 1 := by
        have := (valuation_eq_one_iff_notMem (v := v.1) (K := ℚ) (r := (l : ℤ))).2 hnot
        simpa using this
      rw [h1, inv_one, _root_.mul_one]
      exact (Valuation.map_sub _ _ _).trans (max_le (ha v) (valued_intCast v.1 z))
  · have e : (l : AfP p) * algebraMap ℚ (AfP p) (l : ℚ)⁻¹ = 1 := by
      rw [← map_natCast (algebraMap ℚ (AfP p)), ← map_mul, mul_inv_cancel₀ hlq0, map_one]
    calc a = (z : AfP p) + (a - (z : AfP p)) * ((l : AfP p) * algebraMap ℚ (AfP p) (l : ℚ)⁻¹) := by
          rw [e, _root_.mul_one]; ring
      _ = _ := by ring

theorem exists_int_add_mul (n : ℕ) (hn : 0 < n) (hnp : n.Coprime p) (a : AfP p) (ha : IsIntAf a) :
    ∃ (z : ℤ) (a' : AfP p), IsIntAf a' ∧ a = (z : AfP p) + (n : AfP p) * a' := by
  induction n using Nat.recOnMul generalizing a with
  | zero => exact absurd hn (lt_irrefl 0)
  | one => exact ⟨0, a, ha, by simp⟩
  | prime l hl =>
    exact exists_int_add_prime_mul l hl (fun h => by
      subst h; exact hl.ne_one ((Nat.coprime_self _).1 hnp)) a ha
  | mul m k ihm ihk =>
    have hm : 0 < m := Nat.pos_of_ne_zero (fun h => by simp [h] at hn)
    have hk : 0 < k := Nat.pos_of_ne_zero (fun h => by simp [h] at hn)
    obtain ⟨hmp, hkp⟩ := Nat.coprime_mul_iff_left.1 hnp
    obtain ⟨z1, a1, h1, e1⟩ := ihm hm hmp a ha
    obtain ⟨z2, a2, h2, e2⟩ := ihk hk hkp a1 h1
    exact ⟨z1 + m * z2, a2, h2, by rw [e1, e2]; push_cast; ring⟩

end GlobalTheory.LKGeo.LaHatMod

namespace GlobalTheory.LKGeo

theorem exists_inAf_add_nsmul_of_mem_laHat : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (n : ℕ), 0 < n → n.Coprime p →
    ∀ v ∈ LaHat D, ∃ (x : D.La) (w : TensorProduct ℚ (AfP p) (VQ D)), w ∈ LaHat D ∧ v = inAf D x + n • w := by
  intro p _ D n hn hnp v hv
  induction hv using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨a, x, ha, rfl⟩ := hu
    obtain ⟨z, a', ha', e⟩ := LaHatMod.exists_int_add_mul n hn hnp a ha
    refine ⟨z • x, a' ⊗ₜ ((1 : ℚ) ⊗ₜ x), AddSubgroup.subset_closure ⟨a', x, ha', rfl⟩, ?_⟩
    have h1 : ((z : AfP p)) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] x) = (1 : AfP p) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] (z • x)) := by
      rw [show (z : AfP p) = (z : ℚ) • (1 : AfP p) by rw [← Algebra.algebraMap_eq_smul_one, map_intCast],
        TensorProduct.smul_tmul, TensorProduct.smul_tmul',
        show (z : ℚ) • (1 : ℚ) = z • (1 : ℚ) by simp, TensorProduct.smul_tmul]
    have h2 : ((n : AfP p) * a') ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] x) = n • (a' ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] x)) := by
      rw [← nsmul_eq_mul, TensorProduct.smul_tmul']
    rw [e, TensorProduct.add_tmul, h1, h2, inAf]
  | zero => exact ⟨0, 0, zero_mem _, by simp [inAf]⟩
  | add u u' _ _ ih ih' =>
    obtain ⟨x, w, hw, e⟩ := ih
    obtain ⟨x', w', hw', e'⟩ := ih'
    refine ⟨x + x', w + w', add_mem hw hw', ?_⟩
    rw [e, e', inAf, inAf, inAf, TensorProduct.tmul_add, TensorProduct.tmul_add, smul_add]
    abel
  | neg u _ ih =>
    obtain ⟨x, w, hw, e⟩ := ih
    refine ⟨-x, -w, neg_mem hw, ?_⟩
    rw [e, inAf, inAf, TensorProduct.tmul_neg, TensorProduct.tmul_neg, smul_neg, neg_add]

end GlobalTheory.LKGeo
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace GlobalTheory.IntDvdAdele

theorem valued_intCast_le_iff (v : HeightOneSpectrum ℤ) (r : ℤ) (k : ℕ) :
    Valued.v ((r : v.adicCompletion ℚ)) ≤ WithZero.exp (-(k : ℤ)) ↔ r ∈ v.asIdeal ^ k := by
  have e : ((r : v.adicCompletion ℚ)) = algebraMap ℤ (v.adicCompletion ℚ) r := (eq_intCast _ r).symm
  rw [e, valuedAdicCompletion_eq_valuation, valuation_of_algebraMap, intValuation_le_pow_iff_mem]

def placeAt {p : ℕ} (l : ℕ) (hl : l.Prime) (hlp : l ≠ p) : AwayP p :=
  ⟨⟨Ideal.span {(l : ℤ)},
    (Ideal.span_singleton_prime (by exact_mod_cast hl.ne_zero)).2 (Nat.prime_iff_prime_int.mp hl),
    by simp [hl.ne_zero]⟩, by
    intro h
    have h' := Ideal.span_singleton_eq_span_singleton.1 h
    rw [Int.associated_iff_natAbs] at h'
    simp at h'
    exact hlp h'⟩

theorem placeAt_asIdeal {p : ℕ} (l : ℕ) (hl : l.Prime) (hlp : l ≠ p) :
    (placeAt (p := p) l hl hlp).1.asIdeal = Ideal.span {(l : ℤ)} := rfl

theorem dvd_of_eq_mul_int : ∀ (p : ℕ) [Fact p.Prime] (n : ℕ), 0 < n → n.Coprime p → ∀ (z : ℤ) (w : AfP p),
    IsIntAf w → (z : AfP p) = (n : AfP p) * w → (n : ℤ) ∣ z := by
  intro p _ n hn hcop z w hw hz
  rw [Int.natCast_dvd, Nat.dvd_iff_prime_pow_dvd_dvd]
  intro l k hl hlk
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hl' : l.Prime := hl
  have hln : l ∣ n := (dvd_pow_self l hk.ne').trans hlk
  have hlp : l ≠ p := by
    rintro rfl
    have h1 : Nat.Coprime l l := Nat.Coprime.coprime_dvd_left hln hcop
    exact hl'.one_lt.ne' ((Nat.coprime_self l).1 h1)
  set v := placeAt (p := p) l hl' hlp
  have hzv := congrArg (AfP.eval v) hz
  rw [map_intCast, map_mul, map_natCast] at hzv
  have hwv : Valued.v (AfP.eval v w) ≤ 1 := hw v
  have hnv : Valued.v (((n : ℤ) : v.1.adicCompletion ℚ)) ≤ WithZero.exp (-(k : ℤ)) := by
    rw [valued_intCast_le_iff, placeAt_asIdeal, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact_mod_cast hlk
  have hzle : Valued.v ((z : v.1.adicCompletion ℚ)) ≤ WithZero.exp (-(k : ℤ)) := by
    rw [hzv, map_mul]
    calc Valued.v ((n : v.1.adicCompletion ℚ)) * Valued.v (AfP.eval v w)
        ≤ Valued.v ((n : v.1.adicCompletion ℚ)) * 1 := by gcongr
      _ = Valued.v (((n : ℤ) : v.1.adicCompletion ℚ)) := by rw [_root_.mul_one, Int.cast_natCast]
      _ ≤ _ := hnv
  rw [valued_intCast_le_iff, placeAt_asIdeal, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hzle
  have : ((l ^ k : ℕ) : ℤ) ∣ z := by exact_mod_cast hzle
  exact Int.natCast_dvd.1 this

end GlobalTheory.IntDvdAdele
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
open scoped TensorProduct

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LKGeo.CommBC

theorem actOn_tmul_tmul {C V : Type} [Ring C] [Algebra ℚ C] [AddCommGroup V] [Module ℚ V]
    (rep : C →ₐ[ℚ] Module.End ℚ V) (R : Type) [CommRing R] [Algebra ℚ R] (a b : R) (c : C) (v : V) :
    actOn rep R (a ⊗ₜ c) (b ⊗ₜ v) = (a * b) ⊗ₜ rep c v := by
  have : actOn rep R (a ⊗ₜ c) = Algebra.ofId R _ a * Module.End.baseChangeHom ℚ R V (rep c) :=
    Algebra.TensorProduct.lift_tmul _ _ _ a c
  rw [this, Module.End.mul_apply]
  simp only [Algebra.ofId_apply, Module.algebraMap_end_apply]
  change a • (LinearMap.baseChange R (rep c)) (b ⊗ₜ v) = _
  rw [LinearMap.baseChange_tmul, TensorProduct.smul_tmul', smul_eq_mul]

theorem exists_actOn_eq {C V : Type} [Ring C] [Algebra ℚ C] [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    (rep : C →ₐ[ℚ] Module.End ℚ V) {ι' : Type} (S : ι' → Module.End ℚ V)
    (hrange : ∀ B : Module.End ℚ V, (∀ b, B * S b = S b * B) → ∃ x, rep x = B)
    (R : Type) [CommRing R] [Algebra ℚ R] (A : Module.End R (R ⊗[ℚ] V))
    (hA : ∀ b, A * (S b).baseChange R = (S b).baseChange R * A) : ∃ y, actOn rep R y = A := by
  classical
  let r := Module.Free.chooseBasis ℚ R
  let e : R ⊗[ℚ] V ≃ₗ[ℚ] (Module.Free.ChooseBasisIndex ℚ R →₀ V) :=
    (LinearEquiv.rTensor V r.repr).trans (TensorProduct.finsuppScalarLeft ℚ V _)
  have he : ∀ (a : R) (v : V) k, e (a ⊗ₜ v) k = r.repr a k • v := by
    intro a v k
    simp [e, TensorProduct.finsuppScalarLeft_apply_tmul_apply]
  let Ak : Module.Free.ChooseBasisIndex ℚ R → Module.End ℚ V := fun k =>
    (Finsupp.lapply k) ∘ₗ e.toLinearMap ∘ₗ (A.restrictScalars ℚ) ∘ₗ (TensorProduct.mk ℚ R V 1)
  have hAk : ∀ k v, Ak k v = e (A (1 ⊗ₜ v)) k := fun k v => rfl
  have heS : ∀ (s : Module.End ℚ V) (x : R ⊗[ℚ] V) k, e (s.baseChange R x) k = s (e x k) := by
    intro s x k
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a v => simp [he]
    | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]
  have hcomm : ∀ k b, Ak k * S b = S b * Ak k := by
    intro k b; ext v
    simp only [Module.End.mul_apply, hAk]
    have := congrArg (fun f => f ((1 : R) ⊗ₜ v)) (hA b)
    simp only [Module.End.mul_apply, LinearMap.baseChange_tmul] at this
    rw [this, heS]
  choose x hx using fun k => hrange (Ak k) (hcomm k)
  let bV := Module.finBasis ℚ V
  let F := Finset.univ.biUnion fun i => (e (A ((1 : R) ⊗ₜ bV i))).support
  have hzero : ∀ k ∉ F, Ak k = 0 := by
    intro k hk
    refine bV.ext fun i => ?_
    rw [hAk, LinearMap.zero_apply]
    by_contra h
    exact hk (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finsupp.mem_support_iff.mpr h⟩)
  refine ⟨∑ k ∈ F, r k ⊗ₜ x k, ?_⟩
  have h1 : ∀ v, actOn rep R (∑ k ∈ F, r k ⊗ₜ x k) ((1 : R) ⊗ₜ v) = A ((1 : R) ⊗ₜ v) := by
    intro v
    apply e.injective
    ext j

    rw [map_sum, LinearMap.sum_apply, map_sum, Finsupp.finsetSum_apply]
    simp_rw [actOn_tmul_tmul, _root_.mul_one, hx, he, Module.Basis.repr_self, Finsupp.single_apply, ite_smul, one_smul,
      zero_smul]
    rw [Finset.sum_ite_eq', ← hAk]
    split_ifs with hj
    · rfl
    · rw [hzero j hj, LinearMap.zero_apply]
  apply TensorProduct.AlgebraTensorModule.ext
  intro a v
  have : a ⊗ₜ[ℚ] v = a • ((1 : R) ⊗ₜ v) := by rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
  rw [this, map_smul, map_smul, h1]

theorem exists_actOn_eq_of_commute : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G)
    (A : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)),
    (∀ b : D.O, A * (actQ D b).baseChange (AfP p) = (actQ D b).baseChange (AfP p) * A) →
    ∃ y, actOn L.rep (AfP p) y = A := by
  intro p _ D G L A hA
  haveI := D.finLa
  exact exists_actOn_eq L.rep (actQ D) (fun B hB => (L.rep_range B).mpr hB) (AfP p) A hA

end GlobalTheory.LKGeo.CommBC
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LKGeo.LatDvd

variable {p : ℕ} [Fact p.Prime]

def adBasis {D : Datum p} {J : Type} (b : Module.Basis J ℤ D.La) : Module.Basis J (AfP p) (AfP p ⊗[ℚ] VQ D) :=
  (b.baseChange ℚ).baseChange (AfP p)

theorem adBasis_repr_inAf {D : Datum p} {J : Type} (b : Module.Basis J ℤ D.La) (z : D.La) (i : J) :
    (adBasis b).repr (inAf D z) i = algebraMap ℚ (AfP p) ((b.repr z i : ℤ) : ℚ) := by
  simp only [adBasis, inAf, Module.Basis.baseChange_repr_tmul]
  rw [Algebra.algebraMap_eq_smul_one]
  simp

theorem isIntAf_adBasis_repr {D : Datum p} {J : Type} (b : Module.Basis J ℤ D.La) (i : J) {w : AfP p ⊗[ℚ] VQ D}
    (hw : w ∈ LaHat D) : IsIntAf ((adBasis b).repr w i) := by
  induction hw using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨c, x, hc, rfl⟩ := hz
    have e : (adBasis b).repr (c ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] x : VQ D)) i = ((b.repr x i : ℤ) : AfP p) * c := by
      simp [adBasis, Algebra.smul_def]
    rw [e]
    intro v
    rw [map_mul, map_intCast]
    exact mul_mem (intCast_mem _ _) (hc v)
  | zero =>
    intro v
    rw [map_zero, Finsupp.zero_apply, map_zero]
    exact zero_mem _
  | add x y _ _ hx hy =>
    intro v
    rw [map_add (f := _), Finsupp.add_apply, map_add (f := _)]
    exact add_mem (hx v) (hy v)
  | neg x _ hx =>
    intro v
    rw [map_neg, Finsupp.neg_apply, map_neg]
    exact neg_mem (hx v)

theorem exists_eq_nsmul_of_inAf (p : ℕ) [Fact p.Prime] (D : Datum p) (n : ℕ) (_hn : 0 < n) (_hc : n.Coprime p)
    (h : ∀ (c : ℤ) (a : AfP p), IsIntAf a → algebraMap ℚ (AfP p) (c : ℚ) = (n : AfP p) * a → (n : ℤ) ∣ c)
    (z : D.La) (hz : ∃ w ∈ LaHat D, inAf D z = n • w) : ∃ u : D.La, z = n • u := by
  obtain ⟨w, hw, e⟩ := hz
  have := D.freeLa
  have := D.finLa
  let b := Module.Free.chooseBasis ℤ D.La
  have hd : ∀ i, (n : ℤ) ∣ b.repr z i := by
    intro i
    refine h _ _ (isIntAf_adBasis_repr b i hw) ?_
    rw [← adBasis_repr_inAf, e, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]
  choose d hd using hd
  refine ⟨∑ i, d i • b i, ?_⟩
  conv_lhs => rw [← b.sum_repr z]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hd i, mul_smul, Nat.cast_smul_eq_nsmul]

end GlobalTheory.LKGeo.LatDvd
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.LKGeo

theorem actOn_tmul_tmul' {C V : Type} [Ring C] [Algebra ℚ C] [AddCommGroup V] [Module ℚ V]
    (rep : C →ₐ[ℚ] Module.End ℚ V) (R : Type) [CommRing R] [Algebra ℚ R] (r a : R) (c : C) (v : V) :
    actOn rep R (r ⊗ₜ c) (a ⊗ₜ v) = (r * a) ⊗ₜ rep c v := by
  simp only [actOn, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, AlgHom.coe_comp, Function.comp_apply,
    Module.End.mul_apply, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply]
  change r • (rep c).baseChange R (a ⊗ₜ v) = _
  rw [LinearMap.baseChange_tmul, TensorProduct.smul_tmul', smul_eq_mul]

theorem adj_actOn_afP : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (x : AfP p ⊗[ℚ] G.C) (v w : AfP p ⊗[ℚ] VQ D), (D.EF.baseChange ℚ).baseChange (AfP p) (actOn L.rep (AfP p) x v) w = (D.EF.baseChange ℚ).baseChange (AfP p) v (actOn L.rep (AfP p) (starT G.star (AfP p) x).unop w) := by
  intro p _ D G L x v w
  induction x using TensorProduct.induction_on generalizing v w with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), LinearMap.add_apply, MulOpposite.unop_add, hx, hy]
  | tmul r c =>
    rw [starT_tmul]
    induction v using TensorProduct.induction_on generalizing w with
    | zero => simp
    | add v v' hv hv' => simp only [map_add (f := _), LinearMap.add_apply, hv, hv']
    | tmul a v₀ =>
      induction w using TensorProduct.induction_on with
      | zero => simp
      | add w w' hw hw' => simp only [map_add (f := _), hw, hw']
      | tmul a' w₀ =>
        rw [actOn_tmul_tmul', actOn_tmul_tmul', LinearMap.BilinForm.baseChange_tmul,
          LinearMap.BilinForm.baseChange_tmul, L.adj c v₀ w₀, mul_left_comm, _root_.mul_assoc]
        rfl

end GlobalTheory.LKGeo
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal

theorem _root_.GlobalTheory.T.model_evaluation_preserves_admissible : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M₁ 1 1 ∅ e → Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) →
    ∀ μ : @Measure (Fin n × Fin d → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ c : ℝ≥0∞, ∀ Φ ∈ schA F (Fin n × Fin d), ∫⁻ x, ‖e Φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := by
  first | exact @GlobalTheory.ModelTrUnit.exists_const | exact GlobalTheory.ModelTrUnit.exists_const | (intros; apply GlobalTheory.ModelTrUnit.exists_const <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Matrix

theorem _root_.GlobalTheory.T.symplectic_change_of_good_models_intertwines : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M M₁ : Model σ X W) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ → M₁.IsGood B.ψ → ∀ a : Matrix ((Fin n × Fin d) ⊕ (Fin n × Fin d)) ((Fin n × Fin d) ⊕ (Fin n × Fin d)) F, aᵀ * Matrix.fromBlocks 0 1 (-1) 0 * a = Matrix.fromBlocks 0 1 (-1) 0 → (∀ u, M₁.co.e u = ((a.map (algebraMap F (AF F)) *ᵥ Sum.elim (M.co.e u).1 (M.co.e u).2) ∘ Sum.inl, (a.map (algebraMap F (AF F)) *ᵥ Sum.elim (M.co.e u).1 (M.co.e u).2) ∘ Sum.inr)) → ∃ (e : Fn F n d →ₗ[ℂ] Fn F n d) (c : ℂ), c ≠ 0 ∧ IsEv B M M₁ 1 1 ∅ e ∧ Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) ∧ ∀ Φ ∈ schA F (Fin n × Fin d), thetaSum F (e Φ) = c * thetaSum F Φ := by
  first | exact @GlobalTheory.RatWeilOp.exists_intertwiner | exact GlobalTheory.RatWeilOp.exists_intertwiner | (intros; apply GlobalTheory.RatWeilOp.exists_intertwiner <;> assumption)
end
