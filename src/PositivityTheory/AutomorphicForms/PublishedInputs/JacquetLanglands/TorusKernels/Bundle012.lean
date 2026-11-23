module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.IsHolVOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.CharZeroAdicCompletion
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Abs
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.TypeStar
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain UpperTheory.V.Sd.Wc
open scoped NNReal

namespace UpperTheory.Esk.NormOneUnitsLemmas

theorem pow_sub (ν : Valuation ℂ ℝ≥0) {b : ℂ} (hb : ν b ≤ 1) (m : ℕ) : ν (b ^ m - 1) ≤ ν (b - 1) := by
  rw [← geom_sum_mul, Valuation.map_mul]
  refine mul_le_of_le_one_left zero_le ?_
  refine Valuation.map_sum_le _ fun i _ => ?_
  rw [Valuation.map_pow]
  exact pow_le_one₀ zero_le hb

theorem pow_l (ν : Valuation ℂ ℝ≥0) (l : ℕ) {b : ℂ} (hb : ν b ≤ 1) (hbp : ν (b - 1) ≤ ν (l : ℂ)) :
    ν (b ^ l - 1) ≤ ν (l : ℂ) * ν (b - 1) := by
  rw [← geom_sum_mul, Valuation.map_mul]
  refine mul_le_mul_of_nonneg_right ?_ zero_le
  have e : ∑ i ∈ Finset.range l, b ^ i = ∑ i ∈ Finset.range l, (b ^ i - 1) + (l : ℂ) := by
    rw [Finset.sum_sub_distrib]; simp
  rw [e]
  refine (Valuation.map_add _ _ _).trans (max_le ?_ le_rfl)
  exact Valuation.map_sum_le _ fun i _ => (pow_sub ν hb i).trans hbp

theorem pow_lN (ν : Valuation ℂ ℝ≥0) (l : ℕ) {b : ℂ} (hb : ν b ≤ 1) (hbp : ν (b - 1) ≤ ν (l : ℂ)) :
    ∀ N : ℕ, ν (b ^ (l ^ N) - 1) ≤ ν (l : ℂ) ^ N * ν (b - 1)
  | 0 => by simp
  | N + 1 => by
    have hb' : ν (b ^ (l ^ N)) ≤ 1 := by rw [Valuation.map_pow]; exact pow_le_one₀ zero_le hb
    have e : b ^ (l ^ (N + 1)) = (b ^ (l ^ N)) ^ l := by rw [pow_succ, pow_mul]
    rw [e]
    refine (pow_l ν l hb' ((pow_sub ν hb _).trans hbp)).trans ?_
    rw [pow_succ', mul_assoc]
    exact mul_le_mul_of_nonneg_left (pow_lN ν l hb hbp N) zero_le

theorem lt_one_le (a : WithZero (Multiplicative ℤ)) (h : a < 1) : a ≤ WithZero.exp (-1 : ℤ) := by
  by_cases h0 : a = 0
  · rw [h0]; exact zero_le
  · rw [← WithZero.exp_log h0] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega

end UpperTheory.Esk.NormOneUnitsLemmas

open UpperTheory.Esk.NormOneUnitsLemmas in
theorem UpperTheory.Esk.pf_GUnit : UpperTheory.Esk.GUnit := by
  intro F _ _ l _ ι D v x hx N t ht
  obtain ⟨m, rfl⟩ := ht
  set L : (D.pl v).adicCompletion F := ((l : ℕ) : (D.pl v).adicCompletion F) with hL
  have hLv : Valued.v L = WithZero.exp (-1 : ℤ) := D.unif v
  have hL0 : L ≠ 0 := fun h => by rw [h, map_zero] at hLv; exact WithZero.exp_ne_zero hLv.symm
  have hemL : D.em v L = (l : ℂ) := map_natCast _ l
  have hxle : nu ι (D.em v x) ≤ 1 := (D.le v x).2 hx.le
  set y := x ^ (l - 1) - 1 with hy
  have hemy : D.em v y = D.em v x ^ (l - 1) - 1 := by rw [hy, map_sub, map_pow, map_one]
  have hylt : Valued.v y < 1 := (D.lt v y).1 (by rw [hemy]; exact D.res v x hx)
  have hyL : Valued.v (y / L) ≤ 1 := by
    rw [map_div₀, hLv, div_le_one₀ (by simp)]
    exact lt_one_le _ hylt
  have hnuy : nu ι (D.em v y) ≤ nu ι (l : ℂ) := by
    have e : y = L * (y / L) := by field_simp
    rw [e, map_mul, map_mul, hemL]
    exact mul_le_of_le_one_right zero_le ((D.le v _).2 hyL)
  rw [hemy] at hnuy
  set a := D.em v x ^ (l - 1) with ha
  have hale : nu ι a ≤ 1 := by rw [ha, Valuation.map_pow]; exact pow_le_one₀ zero_le hxle
  have ha1 : nu ι (a - 1) ≤ 1 := by rw [← hemy]; exact ((D.lt v y).2 hylt).le
  have e : D.em v x ^ ((l - 1) * l ^ N * m) = (a ^ (l ^ N)) ^ m := by rw [ha, ← pow_mul, ← pow_mul, mul_assoc]
  rw [e]
  have hb : nu ι (a ^ (l ^ N)) ≤ 1 := by rw [Valuation.map_pow]; exact pow_le_one₀ zero_le hale
  refine (pow_sub _ hb m).trans ((pow_lN _ l hale hnuy N).trans ?_)
  exact mul_le_of_le_one_right zero_le ha1
end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped NNReal

namespace UpperTheory.Esk.ModulusCharacterLemmas

variable {F : Type} [Field F] [NumberField F]

theorem tnn {e : ℝ≥0} (he : e ≠ 0) (m : ℤ) : WithZeroMulInt.toNNReal he (WithZero.exp m) = e ^ m := by
  rw [WithZeroMulInt.toNNReal_neg_apply he WithZero.exp_ne_zero]; rfl

theorem exp_mul_pow (m : ℤ) :
    WithZero.exp m * (WithZero.exp (-1 : ℤ)) ^ m = (1 : WithZero (Multiplicative ℤ)) := by
  rw [WithZero.exp_eq_coe_ofAdd, WithZero.exp_eq_coe_ofAdd, ← WithZero.coe_zpow, ← WithZero.coe_mul,
    ← ofAdd_zsmul, ← ofAdd_add]
  simp

theorem val_exp {w : Pl F} {x : w.adicCompletion F} (hx : x ≠ 0) : ∃ m : ℤ, Valued.v x = WithZero.exp m :=
  ⟨_, (WithZero.exp_log ((Valuation.ne_zero_iff _).2 hx)).symm⟩

theorem norm_eq (w : Pl F) {x : w.adicCompletion F} {m : ℤ} (hm : Valued.v x = WithZero.exp m) :
    ‖x‖ = ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ m := by
  rw [FinitePlace.norm_def (x := x), hm, tnn, NNReal.coe_zpow, NNReal.coe_natCast]

theorem normV_eq (w : Pl F) : normV w = Ideal.absNorm w.asIdeal := by
  simp [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem nu_nat {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {n : ℕ} (h : ¬ l ∣ n) : nu ι (n : ℂ) = 1 := by
  have e : ι.symm (n : ℂ) = algebraMap ℚ_[l] (Qbar l) (n : ℚ_[l]) := by rw [map_natCast, map_natCast]
  apply NNReal.coe_injective
  rw [nu_apply, coe_nnnorm, e, norm_algebraMap',
    Padic.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 h), NNReal.coe_one]

theorem not_dvd (w : Pl F) {l : ℕ} [hl : Fact l.Prime] (h : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) : ¬ l ∣ normV w := by
  intro hd
  haveI := w.isPrime
  have hne : normV w ≠ 0 := by
    rw [normV_eq]; have := HeightOneSpectrum.one_lt_absNorm w; omega
  haveI : Finite (𝓞 F ⧸ w.asIdeal) := Nat.finite_of_card_ne_zero hne
  haveI := Fintype.ofFinite (𝓞 F ⧸ w.asIdeal)
  have hd' : l ∣ Fintype.card (𝓞 F ⧸ w.asIdeal) := by rw [Fintype.card_eq_nat_card]; exact hd
  obtain ⟨a, ha⟩ := exists_prime_addOrderOf_dvd_card l hd'
  have h1 : (l : 𝓞 F ⧸ w.asIdeal) * a = 0 := by rw [← nsmul_eq_mul, ← ha, addOrderOf_nsmul_eq_zero]
  have h2 : (l : 𝓞 F ⧸ w.asIdeal) ≠ 0 := by
    rw [← map_natCast (Ideal.Quotient.mk w.asIdeal), Ne, Ideal.Quotient.eq_zero_iff_mem]; exact h
  have h3 : a = 0 := (mul_eq_zero.1 h1).resolve_left h2
  rw [h3, addOrderOf_zero] at ha
  exact hl.out.one_lt.ne ha

theorem away {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (w : Pl F) (h : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal)
    {x : w.adicCompletion F} (hx : x ≠ 0) : nu ι (‖x‖ : ℂ) = 1 := by
  obtain ⟨m, hm⟩ := val_exp hx
  rw [norm_eq w hm, Complex.ofReal_zpow, Complex.ofReal_natCast, map_zpow₀, ← normV_eq, nu_nat ι (not_dvd w h),
    one_zpow]

theorem atL {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} (D : LDat F ι) (v : InfinitePlace F)
    {x : (D.pl v).adicCompletion F} (hx : x ≠ 0) : nu ι ((‖x‖ : ℂ) * D.em v x) = 1 := by
  obtain ⟨m, hm⟩ := val_exp hx
  set L : (D.pl v).adicCompletion F := ((l : ℕ) : (D.pl v).adicCompletion F) with hL
  have hLv : Valued.v L = WithZero.exp (-1 : ℤ) := D.unif v
  have hL0 : L ≠ 0 := fun h => by rw [h, map_zero] at hLv; exact WithZero.exp_ne_zero hLv.symm
  have hemL : D.em v L = (l : ℂ) := map_natCast _ l
  have hl0 : (l : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hy : Valued.v (x * L ^ m) = 1 := by rw [map_mul, map_zpow₀, hLv, hm, exp_mul_pow]
  have hnu : nu ι (D.em v (x * L ^ m)) = 1 :=
    le_antisymm ((D.le v _).2 hy.le) (not_lt.1 fun h => ((D.lt v _).1 h).ne hy)
  have hn : ‖x‖ = (l : ℝ) ^ m := by rw [norm_eq _ hm, ← normV_eq, D.norm v]
  have e : (‖x‖ : ℂ) * D.em v x = D.em v (x * L ^ m) := by
    rw [hn, map_mul, map_zpow₀, hemL, Complex.ofReal_zpow, Complex.ofReal_natCast]
    ring
  rw [e, hnu]

theorem nrm_unit {w : Pl F} {x : w.adicCompletion F} (h : Valued.v x = 1) : ‖x‖ = 1 :=
  le_antisymm ((Valued.toNormedField.norm_le_one_iff (x := x)).2 h.le)
    ((Valued.toNormedField.one_le_norm_iff (x := x)).2 h.ge)

theorem fin_supp (y : (Af F)ˣ) : (Function.mulSupport fun w : Pl F => ‖pLoc F w (y : Af F)‖).Finite := by
  have h1 := Filter.eventually_cofinite.1 (y : Af F).2
  have h2 := Filter.eventually_cofinite.1 ((y⁻¹ : (Af F)ˣ) : Af F).2
  refine (h1.union h2).subset fun w hw => ?_
  by_contra hc
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
  have a1 : Valued.v (pLoc F w (y : Af F)) ≤ 1 := hc.1
  have a2 : Valued.v (pLoc F w ((y⁻¹ : (Af F)ˣ) : Af F)) ≤ 1 := hc.2
  have a3 : Valued.v (pLoc F w (y : Af F)) * Valued.v (pLoc F w ((y⁻¹ : (Af F)ˣ) : Af F)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  refine hw (nrm_unit (le_antisymm a1 ?_))
  calc 1 = _ := a3.symm
    _ ≤ Valued.v (pLoc F w (y : Af F)) * 1 := mul_le_mul_right a2 _
    _ = _ := mul_one _

end UpperTheory.Esk.ModulusCharacterLemmas

open UpperTheory.Esk.ModulusCharacterLemmas in
theorem UpperTheory.Esk.pf_GMod : UpperTheory.Esk.GMod := by
  intro F _ _ l _ ι D z
  have hz : ∀ w, pLoc F w (z : Af F) ≠ 0 := fun w => (z.isUnit.map (pLoc F w)).ne_zero
  have habs : absF z = ∏ᶠ w : Pl F, ‖pLoc F w (z : Af F)‖ := rfl
  refine ⟨?_, ?_⟩
  · rw [habs]
    exact finprod_induction (fun x : ℝ => 0 < x) one_pos (fun _ _ => mul_pos) fun w => norm_pos_iff.2 (hz w)
  classical
  have hfin := fin_supp z
  set s : Finset (Pl F) := hfin.toFinset ∪ Finset.univ.image D.pl with hs_def
  have hs : absF z = ∏ w ∈ s, ‖pLoc F w (z : Af F)‖ := by
    rw [habs]
    refine finprod_eq_prod_of_mulSupport_subset _ fun w hw => ?_
    rw [hs_def, Finset.coe_union]
    exact Or.inl (hfin.mem_toFinset.2 hw)
  have hprod : ∏ v, D.ea v (z : Af F) = ∏ w ∈ s, ∏ v ∈ Finset.univ.filter (fun v => D.pl v = w), D.ea v (z : Af F) :=
    (Finset.prod_fiberwise_of_maps_to (fun v _ => by simp [hs_def]) _).symm
  rw [hs, hprod, Complex.ofReal_prod, ← Finset.prod_mul_distrib, map_prod]
  refine Finset.prod_eq_one fun w _ => ?_
  by_cases hw : ∃ v, D.pl v = w
  · obtain ⟨v, rfl⟩ := hw
    have e : Finset.univ.filter (fun u => D.pl u = D.pl v) = {v} := by
      ext u; simp [D.inj.eq_iff]
    rw [e, Finset.prod_singleton]
    exact atL D v (hz _)
  · have e : Finset.univ.filter (fun u => D.pl u = w) = ∅ := by
      ext u; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      exact fun h => hw ⟨u, h⟩
    rw [e, Finset.prod_empty, mul_one]
    exact away ι w (fun h => hw (D.surj w h)) (hz w)
end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc

namespace UpperTheory.Esk.FiniteLevelGroupLemmas

def Gm (h : HRel) (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : InfinitePlace F → ℕ) :
    (X (InfinitePlace F) × GF F → ℂ) →ₗ[ℂ] (GA F 2 → ℂ) where
  toFun f := Classical.choose ((h F k).1 f)
  map_add' f f' := by
    have e := (h F k).2.2.2.1 f f' _ _ 1 (Classical.choose_spec ((h F k).1 f)) (Classical.choose_spec ((h F k).1 f'))
    simp only [one_smul] at e
    exact (h F k).2.1 _ _ _ (Classical.choose_spec ((h F k).1 (f + f'))) e
  map_smul' s f := by
    have e := (h F k).2.2.2.1 0 f 0 _ s (h F k).2.2.2.2.1 (Classical.choose_spec ((h F k).1 f))
    simp only [zero_add] at e
    exact (h F k).2.1 _ _ _ (Classical.choose_spec ((h F k).1 (s • f))) e

theorem rel (h : HRel) (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : InfinitePlace F → ℕ)
    (f : X (InfinitePlace F) × GF F → ℂ) : Rel k f (Gm h F k f) :=
  Classical.choose_spec ((h F k).1 f)

theorem inj (h : HRel) (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : InfinitePlace F → ℕ) :
    Function.Injective (Gm h F k) := by
  intro f f' e
  have h2 := rel h F k f'
  rw [← e] at h2
  exact (h F k).2.2.1 f f' _ (rel h F k f) h2

end UpperTheory.Esk.FiniteLevelGroupLemmas

theorem UpperTheory.Esk.pf_HFin : UpperTheory.Esk.HRel → UpperTheory.Esk.H2a → UpperTheory.Esk.H2d → UpperTheory.Esk.H2e → UpperTheory.Esk.HFinC → UpperTheory.Esk.HFin := by
  intro hR h2a h2d h2e hC F _ _ _ k c hc ω χ hω hχ hS hk
  classical
  let S : Set (TR.Sm F 2) := {φ | IsHolV k c ω φ ∧ TR.IsCuspForm φ}
  have : FiniteDimensional ℂ (Submodule.span ℂ S) := hC F k c hc ω hω
  let W : Submodule ℂ (GA F 2 → ℂ) := (Submodule.span ℂ S).map (TR.Sm F 2).subtype
  have : FiniteDimensional ℂ W := inferInstance
  let p := Submodule.span ℂ {f | (mkDat c χ).IsForm k f}
  have hle : p.map (FiniteLevelGroupLemmas.Gm hR F k) ≤ W := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    have hrel := FiniteLevelGroupLemmas.rel hR F k f
    obtain ⟨hs, hhol⟩ := h2d F k c hc ω χ hω hχ hS hk f _ hf hrel
    have hb := (h2a F k c hc ω χ hω hχ hS hk f _ hf hrel).2.2.2
    have hcusp := h2e F k c ω ⟨_, hs⟩ hω hk hhol hb
    exact ⟨⟨_, hs⟩, Submodule.subset_span ⟨hhol, hcusp⟩, rfl⟩
  have : FiniteDimensional ℂ (p.map (FiniteLevelGroupLemmas.Gm hR F k)) := Submodule.finiteDimensional_of_le hle
  exact LinearEquiv.finiteDimensional (Submodule.equivMapOfInjective _ (FiniteLevelGroupLemmas.inj hR F k) p).symm
end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped ContDiff

namespace UpperTheory.Esk.ImaginaryUnitActionLemmas

open UpperTheory.Esk


open Classical in
def Fx {I : Type} (f : X I → ℂ) (w : I → ℂ) : ℂ :=
  if h : ∀ v, (w v).im ≠ 0 then f (fun v => ⟨w v, h v⟩) else 0

theorem Fx_eq {I : Type} (f : X I → ℂ) {w : I → ℂ} (h : ∀ v, (w v).im ≠ 0) :
    Fx f w = f (fun v => ⟨w v, h v⟩) := by
  rw [Fx, dite_eq_left h]

theorem Fx_val {I : Type} (f : X I → ℂ) (z : X I) : Fx f (fun v => (z v).1) = f z :=
  Fx_eq f (fun v => (z v).2)

theorem isOpen_U (I : Type) [Finite I] : IsOpen {w : I → ℂ | ∀ v, (w v).im ≠ 0} := by
  rw [Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun v =>
    isOpen_ne_fun (Complex.continuous_im.comp (continuous_apply v)) continuous_const

theorem analytic_Fx (hO : Osg) {I : Type} [Fintype I] (f : X I → ℂ) (hf : SepHol f) :
    AnalyticOnNhd ℂ (Fx f) {w : I → ℂ | ∀ v, (w v).im ≠ 0} := by
  classical
  obtain ⟨hc, hh⟩ := hf
  refine hO I _ (isOpen_U I) (Fx f) ?_ ?_
  · rw [continuousOn_iff_continuous_domRestrict]
    have e : Set.domRestrict {w : I → ℂ | ∀ v, (w v).im ≠ 0} (Fx f) = fun w => f (fun v => ⟨w.1 v, w.2 v⟩) := by
      funext w
      exact Fx_eq f w.2
    rw [e]
    refine hc.comp (continuous_pi fun v => ?_)
    exact Continuous.subtype_mk ((continuous_apply v).comp continuous_subtype_val) _
  · intro w hw v
    have hw' : ∀ u, (w u).im ≠ 0 := hw
    let z : X I := fun u => ⟨w u, hw' u⟩
    have hd := hh z v
    have hopen : IsOpen {t : ℂ | t.im ≠ 0} := isOpen_ne_fun Complex.continuous_im continuous_const
    have hmem : {t : ℂ | t.im ≠ 0} ∈ nhds (w v) := hopen.mem_nhds (hw' v)
    refine (DifferentiableOn.differentiableAt hd hmem).congr_of_eventuallyEq ?_
    filter_upwards [hmem] with t ht
    have ht' : t.im ≠ 0 := ht
    have hu : ∀ u, (Function.update w v t u).im ≠ 0 := by
      intro u
      by_cases huv : u = v
      · subst huv
        simpa using ht'
      · simpa [Function.update_of_ne huv] using hw' u
    rw [Fx_eq f hu]
    unfold ext1
    rw [dite_eq_left ht']
    congr 1
    funext u
    apply Subtype.ext
    exact (Function.apply_update (fun _ (p : P) => p.1) z v ⟨t, ht'⟩ u).symm

def dn (M : Matrix (Fin 2) (Fin 2) ℝ) : ℂ := ((M 1 0 : ℝ) : ℂ) * Complex.I + ((M 1 1 : ℝ) : ℂ)

def nm (M : Matrix (Fin 2) (Fin 2) ℝ) : ℂ := ((M 0 0 : ℝ) : ℂ) * Complex.I + ((M 0 1 : ℝ) : ℂ)

def dt (M : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := M 0 0 * M 1 1 - M 0 1 * M 1 0

def jj (k : ℕ) (M : Matrix (Fin 2) (Fin 2) ℝ) : ℂ := dn M ^ k * ((|dt M| ^ (-(k : ℝ) / 2) : ℝ) : ℂ)

theorem smul_iP (g : GL (Fin 2) ℝ) : (g • iP).1 = nm g.val * (dn g.val)⁻¹ := by
  rw [coe_smul, div_eq_mul_inv]
  rfl

theorem automorphy_factor_at_i_eq (k : ℕ) (g : GL (Fin 2) ℝ) : j1 k g iP = jj k g.val := by
  unfold j1 jj dt
  rw [det_eq]
  rfl

theorem dn_ne {M : Matrix (Fin 2) (Fin 2) ℝ} (h : dt M ≠ 0) : dn M ≠ 0 := by
  intro e
  have h1 := congrArg Complex.re e
  have h2 := congrArg Complex.im e
  simp [dn] at h1 h2
  apply h
  simp [dt, h1, h2]

theorem cd_parts {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (M : E → Matrix (Fin 2) (Fin 2) ℝ) (m0 : E)
    (hM : ∀ i j, ContDiffAt ℝ ∞ (fun m => M m i j) m0) (h0 : dt (M m0) ≠ 0) (k : ℕ) :
    ContDiffAt ℝ ∞ (fun m => nm (M m) * (dn (M m))⁻¹) m0 ∧ ContDiffAt ℝ ∞ (fun m => jj k (M m)) m0 := by
  have hC : ∀ i j, ContDiffAt ℝ ∞ (fun m => ((M m i j : ℝ) : ℂ)) m0 := fun i j =>
    Complex.ofRealCLM.contDiff.contDiffAt.comp m0 (hM i j)
  have hdn : ContDiffAt ℝ ∞ (fun m => dn (M m)) m0 := by
    unfold dn
    exact ((hC 1 0).mul contDiffAt_const).add (hC 1 1)
  have hnm : ContDiffAt ℝ ∞ (fun m => nm (M m)) m0 := by
    unfold nm
    exact ((hC 0 0).mul contDiffAt_const).add (hC 0 1)
  have hdt : ContDiffAt ℝ ∞ (fun m => dt (M m)) m0 := by
    unfold dt
    exact ((hM 0 0).mul (hM 1 1)).sub ((hM 0 1).mul (hM 1 0))
  refine ⟨hnm.mul (hdn.inv (dn_ne h0)), ?_⟩
  unfold jj
  exact (hdn.pow k).mul (Complex.ofRealCLM.contDiff.contDiffAt.comp m0
    ((hdt.abs h0).rpow_const_of_ne (p := -(k : ℝ) / 2) (abs_ne_zero.2 h0)))

theorem chart_smooth (hO : Osg) (hB : B1b) (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (k : InfinitePlace F → ℕ) (f : X (InfinitePlace F) × GF F → ℂ) (φ : GA F 2 → ℂ)
    (hf : ∀ x, SepHol fun z => f (z, x)) (hR : Rel k f φ) (g0 : GA F 2) :
    ContDiffOn ℝ ∞ (TR.chart φ g0) (TR.invSet F 2) := by
  obtain ⟨-, hj1, -⟩ := hB
  obtain ⟨y0, x0, rfl⟩ : ∃ (y0 : GL (Fin 2) (TR.Rinf F)) (x0 : GF F), g0 = TR.infGL F 2 y0 * finGL F 2 x0 :=
    ⟨_, _, (TR.infGL_mul_finGL g0).symm⟩
  have hj : ∀ g : GL (Fin 2) (TR.Rinf F), ∏ v, j1 (k v) (gv v g) iP ≠ 0 :=
    fun g => Finset.prod_ne_zero_iff.2 fun v _ => hj1 _ _ _
  have key : ∀ y : GL (Fin 2) (TR.Rinf F), TR.chart φ (TR.infGL F 2 y0 * finGL F 2 x0) (TR.toL y.val) =
      f (fun v => gv v (y0 * y) • iP, x0) * (∏ v, j1 (k v) (gv v (y0 * y)) iP)⁻¹ := by
    intro y
    have e : TR.infGL F 2 y0 * finGL F 2 x0 * TR.infGL F 2 y = TR.infGL F 2 (y0 * y) * finGL F 2 x0 := by
      rw [mul_assoc, ← TR.infGL_comm, ← mul_assoc, ← map_mul]
    rw [TR.chart_val, e, eq_mul_inv_iff_mul_eq₀ (hj _)]
    exact hR (y0 * y) x0
  let A : Matrix (Fin 2) (Fin 2) (TR.Rinf F) := y0.val
  let M : InfinitePlace F → TR.Lie F 2 → Matrix (Fin 2) (Fin 2) ℝ := fun v m i j => ∑ l, A i l v * m l j v
  have hM : ∀ (y : GL (Fin 2) (TR.Rinf F)) v, M v (TR.toL y.val) = (gv v (y0 * y)).val := by
    intro y v
    ext i j
    simp only [M, A]
    change _ = ((y0 * y).val i j) v
    rw [Units.val_mul, Matrix.mul_apply, Finset.sum_apply]
    rfl
  let G : TR.Lie F 2 → ℂ := fun m => Fx (fun z => f (z, x0)) (fun v => nm (M v m) * (dn (M v m))⁻¹) *
    (∏ v, jj (k v) (M v m))⁻¹
  have hG : ∀ y : GL (Fin 2) (TR.Rinf F),
      TR.chart φ (TR.infGL F 2 y0 * finGL F 2 x0) (TR.toL y.val) = G (TR.toL y.val) := by
    intro y
    rw [key]
    simp only [G, hM, ← smul_iP, ← automorphy_factor_at_i_eq]
    rw [Fx_val]
  have hA := analytic_Fx hO (fun z => f (z, x0)) (hf x0)
  refine ContDiffOn.congr (f := G) (fun m hm => ?_) (fun m hm => ?_)
  · obtain ⟨y, rfl⟩ := id hm
    have hE : ∀ v i j, ContDiffAt ℝ ∞ (fun m : TR.Lie F 2 => M v m i j) (TR.toL y.val) := by
      intro v i j
      have hc : ∀ l, ContDiff ℝ ∞ (fun m : TR.Lie F 2 => m l j v) := fun l =>
        (contDiff_apply ℝ (fun _ => ℝ) v).comp ((contDiff_apply ℝ _ j).comp (contDiff_apply ℝ _ l))
      exact (ContDiff.sum fun l _ => contDiff_const.mul (hc l)).contDiffAt
    have hdt : ∀ v, dt (M v (TR.toL y.val)) ≠ 0 := by
      intro v
      rw [hM]
      have h := (gv v (y0 * y)).det_ne_zero
      rw [det_eq] at h
      exact h
    have hP : ∀ v, ContDiffAt ℝ ∞ (fun m => nm (M v m) * (dn (M v m))⁻¹) (TR.toL y.val) ∧
        ContDiffAt ℝ ∞ (fun m => jj (k v) (M v m)) (TR.toL y.val) := fun v => cd_parts (M v) _ (hE v) (hdt v) (k v)
    have hw : ∀ v, (nm (M v (TR.toL y.val)) * (dn (M v (TR.toL y.val)))⁻¹).im ≠ 0 := by
      intro v
      rw [hM, ← smul_iP]
      exact (gv v (y0 * y) • iP).2
    have h1 : ContDiffAt ℝ ∞ (fun m => Fx (fun z => f (z, x0)) (fun v => nm (M v m) * (dn (M v m))⁻¹))
        (TR.toL y.val) :=
      ContDiffAt.comp (g := Fx (fun z => f (z, x0))) (TR.toL y.val)
        ((hA (fun v => nm (M v (TR.toL y.val)) * (dn (M v (TR.toL y.val)))⁻¹) hw).contDiffAt.restrict_scalars ℝ)
        ((contDiffAt_pi (Φ := fun m v => nm (M v m) * (dn (M v m))⁻¹)).2 fun v => (hP v).1)
    have h2 : ContDiffAt ℝ ∞ (fun m => ∏ v, jj (k v) (M v m)) (TR.toL y.val) :=
      contDiffAt_prod fun v _ => (hP v).2
    have h3 : (∏ v, jj (k v) (M v (TR.toL y.val))) ≠ 0 := by
      simp only [hM, ← automorphy_factor_at_i_eq]
      exact hj (y0 * y)
    exact (h1.mul (h2.inv h3)).contDiffWithinAt
  · obtain ⟨y, rfl⟩ := id hm
    exact hG y

end UpperTheory.Esk.ImaginaryUnitActionLemmas

theorem UpperTheory.Esk.hyperbolic_orbit_bound_proof : UpperTheory.Esk.Osg → UpperTheory.Esk.B1b → UpperTheory.Esk.H2b := by
  intro hO hB F _ _ _ k c _ om χ _ _ _ _ f φ hf hR g
  exact UpperTheory.Esk.ImaginaryUnitActionLemmas.chart_smooth hO hB F k f φ hf.hol hR g
end
end
