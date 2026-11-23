module

import Formalism.FormalGroupWitt.FormalGroupWittProofs.SolveV
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.Valuation.Basic
import Formalism.LocalToGlobal.CharacterGerms.RowTiePGerm
public import Formalism.LocalToGlobal.CharacterGerms.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import Formalism.LocalToGlobal.CharacterGerms.Bundle007
public import Formalism.LocalToGlobal.CharacterGerms.Bundle008
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

noncomputable section
open scoped BigOperators
open Classical
open MvPowerSeries

namespace Formalism.L2.FormalSeriesBounds.AltInv

variable {C : Type*} [Field C] (v : AddValuation C (WithTop ℝ))

def IntC (x : C) : Prop := 0 ≤ v x

def IntS {σ : Type*} (f : MvPowerSeries σ C) : Prop := ∀ μ, IntC v (coeff μ f)

variable {v}

theorem intC_zero : IntC v 0 := by
  unfold IntC
  simp
theorem intC_one : IntC v 1 := by
  unfold IntC
  simp
theorem intC_add {x y : C} (hx : IntC v x) (hy : IntC v y) : IntC v (x + y) :=
  le_trans (le_min hx hy) (v.map_add x y)
theorem intC_neg {x : C} (hx : IntC v x) : IntC v (-x) := by
  unfold IntC at *
  rwa [AddValuation.map_neg]
theorem intC_mul {x y : C} (hx : IntC v x) (hy : IntC v y) : IntC v (x * y) := by
  unfold IntC at *
  rw [AddValuation.map_mul]
  exact add_nonneg hx hy
theorem intC_sub {x y : C} (hx : IntC v x) (hy : IntC v y) : IntC v (x - y) := by
  rw [sub_eq_add_neg]
  exact intC_add hx (intC_neg hy)
theorem intC_natCast (n : ℕ) : IntC v (n : C) := by
  induction n with
  | zero =>
    rw [Nat.cast_zero]
    exact intC_zero
  | succ n ih =>
    rw [Nat.cast_succ]
    exact intC_add ih intC_one
theorem intC_intCast (n : ℤ) : IntC v (n : C) := by
  cases n with
  | ofNat n =>
    rw [Int.ofNat_eq_coe, Int.cast_natCast]
    exact intC_natCast n
  | negSucc n =>
    rw [Int.cast_negSucc]
    exact intC_neg (intC_natCast _)
theorem intC_sum {ι : Type*} (s : Finset ι) {f : ι → C} (h : ∀ i ∈ s, IntC v (f i)) :
    IntC v (∑ i ∈ s, f i) :=
  Finset.sum_induction _ (IntC v) (fun _ _ => intC_add) intC_zero h
theorem intC_prod {ι : Type*} (s : Finset ι) {f : ι → C} (h : ∀ i ∈ s, IntC v (f i)) :
    IntC v (∏ i ∈ s, f i) :=
  Finset.prod_induction _ (IntC v) (fun _ _ => intC_mul) intC_one h
theorem intC_finsum {ι : Type*} {f : ι → C} (h : ∀ i, IntC v (f i)) : IntC v (∑ᶠ i, f i) := by
  by_cases hs : (Function.support f).Finite
  · rw [finsum_eq_sum f hs]
    exact intC_sum _ fun i _ => h i
  · rw [finsum_of_infinite_support hs]
    exact intC_zero

variable {σ τ : Type*}

theorem intS_mul {f g : MvPowerSeries σ C} (hf : IntS v f) (hg : IntS v g) : IntS v (f * g) := by
  intro μ
  rw [coeff_mul]
  exact intC_sum _ fun p _ => intC_mul (hf _) (hg _)

theorem intS_one : IntS v (1 : MvPowerSeries σ C) := by
  intro μ
  rw [coeff_one]
  split_ifs
  · exact intC_one
  · exact intC_zero

theorem intS_pow {f : MvPowerSeries σ C} (hf : IntS v f) (n : ℕ) : IntS v (f ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact intS_one
  | succ n ih =>
    rw [pow_succ]
    exact intS_mul ih hf

theorem intS_prod {ι : Type*} (s : Finset ι) {f : ι → MvPowerSeries σ C} (h : ∀ i ∈ s, IntS v (f i)) :
    IntS v (∏ i ∈ s, f i) :=
  Finset.prod_induction _ (IntS v) (fun _ _ => intS_mul) intS_one h

private theorem hasSubst_lemma [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, constantCoeff (a s) = 0) :
    HasSubst a :=
  ⟨fun s => by rw [ha s]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩

theorem intS_subst [Finite σ] {a : σ → MvPowerSeries τ C} (ha0 : ∀ s, constantCoeff (a s) = 0)
    (ha : ∀ s, IntS v (a s)) {γ : MvPowerSeries σ C} (hγ : IntS v γ) : IntS v (subst a γ) := by
  have hsub : HasSubst a := hasSubst_lemma ha0
  intro μ
  rw [coeff_subst hsub]
  refine intC_finsum fun d => ?_
  rw [smul_eq_mul]
  exact intC_mul (hγ d) (intS_prod _ (fun s _ => intS_pow (ha s) _) μ)

def LowLt {σ : Type*} (K : ℕ) (f : MvPowerSeries σ C) : Prop :=
  ∀ μ : σ →₀ ℕ, μ.degree < K → IntC v (coeff μ f)

def OrdV {σ : Type*} (D : ℕ) (f : MvPowerSeries σ C) : Prop :=
  ∀ μ : σ →₀ ℕ, μ.degree < D → coeff μ f = 0

private theorem degree_add_lemma_2 (a b : σ →₀ ℕ) : (a + b).degree = a.degree + b.degree := by
  first
  | exact map_add _ a b
  | exact Finsupp.sum_add_index' (h := fun _ n => n) (fun _ => rfl) (fun _ _ _ => rfl)

theorem low_mul {E D D' : ℕ} {f g : MvPowerSeries σ C} (hf : OrdV D f) (hf' : LowLt (v := v) (E + D) f)
    (hg : OrdV D' g) (hg' : LowLt (v := v) (E + D') g) :
    OrdV (D + D') (f * g) ∧ LowLt (v := v) (E + (D + D')) (f * g) := by
  constructor
  · intro μ hμ
    rw [coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have hdeg : p.1.degree + p.2.degree = μ.degree := by rw [← hp, degree_add_lemma_2]
    by_cases h1 : p.1.degree < D
    · rw [hf p.1 h1, zero_mul]
    · rw [hg p.2 (by omega), mul_zero]
  · intro μ hμ
    rw [coeff_mul]
    refine intC_sum _ fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have hdeg : p.1.degree + p.2.degree = μ.degree := by rw [← hp, degree_add_lemma_2]
    by_cases h1 : p.1.degree < D
    · rw [hf p.1 h1, zero_mul]
      exact intC_zero
    · by_cases h2 : p.2.degree < D'
      · rw [hg p.2 h2, mul_zero]
        exact intC_zero
      · exact intC_mul (hf' p.1 (by omega)) (hg' p.2 (by omega))

theorem low_one (E : ℕ) : OrdV 0 (1 : MvPowerSeries σ C) ∧ LowLt (v := v) E (1 : MvPowerSeries σ C) :=
  ⟨fun _ hμ => absurd hμ (Nat.not_lt_zero _), fun μ _ => intS_one μ⟩

theorem low_pow {E D : ℕ} {f : MvPowerSeries σ C} (hf : OrdV D f) (hf' : LowLt (v := v) (E + D) f) (n : ℕ) :
    OrdV (n * D) (f ^ n) ∧ LowLt (v := v) (E + n * D) (f ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, Nat.zero_mul, Nat.add_zero]
    exact low_one E
  | succ n ih =>
    rw [pow_succ, Nat.add_mul, Nat.one_mul]
    exact low_mul ih.1 ih.2 hf hf'

theorem low_prod {E : ℕ} {t : σ → MvPowerSeries σ C} (ht : ∀ s, OrdV 1 (t s))
    (ht' : ∀ s, LowLt (v := v) (E + 1) (t s)) (S : Finset σ) (d : σ → ℕ) :
    OrdV (∑ s ∈ S, d s) (∏ s ∈ S, t s ^ d s) ∧ LowLt (v := v) (E + ∑ s ∈ S, d s) (∏ s ∈ S, t s ^ d s) := by
  refine Finset.induction_on S ?_ ?_
  · rw [Finset.sum_empty, Finset.prod_empty, Nat.add_zero]
    exact low_one E
  · intro a S ha ih
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have hp := low_pow (ht a) (ht' a) (d a)
    rw [Nat.mul_one] at hp
    exact low_mul hp.1 hp.2 ih.1 ih.2

theorem deg_one_single (d : σ →₀ ℕ) (h : d.degree = 1) : ∃ y, d = Finsupp.single y 1 := by
  apply Formalism.FG.SolveVAux.degree_eq_one <;> assumption

theorem intC_det {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n C) (hA : ∀ i j, IntC v (A i j)) :
    IntC v A.det := by
  rw [Matrix.det_apply]
  refine intC_sum _ fun s _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  exact intC_mul (intC_intCast _) (intC_prod _ fun i _ => hA _ _)

end Formalism.L2.FormalSeriesBounds.AltInv
end
end

section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C]

section IntSec

variable {V : VF C} {τ : Type}

theorem IntS.mul {f g : MvPowerSeries τ C} (hf : IntS V f) (hg : IntS V g) : IntS V (f * g) := by
  intro μ
  rw [MvPowerSeries.coeff_mul]
  refine VF.Ge.sum fun p _ => ?_
  have hp := (hf p.1).mul (hg p.2)
  simpa using hp

theorem IntS.one : IntS V (1 : MvPowerSeries τ C) := by
  intro μ
  rw [MvPowerSeries.coeff_one]
  split_ifs
  all_goals simp [VF.Ge]

theorem IntS.pow {f : MvPowerSeries τ C} (hf : IntS V f) (n : ℕ) : IntS V (f ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact IntS.one
  | succ n ih => rw [pow_succ]; exact ih.mul hf

theorem IntS.subst {σ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha0 : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (ha : ∀ s, IntS V (a s)) {f : MvPowerSeries σ C}
    (hf : IntS V f) : IntS V (MvPowerSeries.subst a f) := by
  apply Formalism.L2.FormalSeriesBounds.PartialDerivEval.intS_subst <;> assumption

theorem intS_ps {f : PowerSeries C} : IntS V f ↔ ∀ n, V.Ge 0 (PowerSeries.coeff n f) := by
  constructor
  · intro h n
    exact h (Finsupp.single () n)
  · intro h μ
    have hμ : μ = Finsupp.single () (μ ()) := by
      ext
      simp [Finsupp.single_apply]
    rw [hμ]
    exact h (μ ())

end IntSec

section Kill

variable {dd : ℕ}

theorem subst_ev_kill (h : PS C 2 dd) (g : Fin 2) (a : Fin 2 → Pt C 1 dd) (hag : a g = 0)
    (hao : ∀ g', g' ≠ g → a g' = pt C dd 0) :
    MvPowerSeries.subst (fun q : Fin 1 × Fin dd => (MvPowerSeries.X (1 - g, q.2) : PS C 2 dd)) (ev a h) =
      MvPowerSeries.rescale (fun s : Fin 2 × Fin dd => if s.1 = g then (0 : C) else 1) h := by
  have hbS : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => (MvPowerSeries.X (1 - g, q.2) : PS C 2 dd)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => MvPowerSeries.constantCoeff_X _
  have haS : MvPowerSeries.HasSubst (fun p : Fin 2 × Fin dd => a p.1 p.2) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero
    intro s
    by_cases hs : s.1 = g
    · rw [hs, hag]; simp
    · rw [hao _ hs]; exact MvPowerSeries.constantCoeff_X _
  unfold ev
  rw [MvPowerSeries.subst_comp_subst_apply haS hbS, MvPowerSeries.rescale_eq_subst]
  congr 1
  funext s
  by_cases hs : s.1 = g
  · have h1 : a s.1 s.2 = 0 := by rw [hs, hag]; rfl
    rw [h1, ← MvPowerSeries.coe_substAlgHom hbS, map_zero]
    simp [hs]
  · have h1 : a s.1 s.2 = MvPowerSeries.X ((0 : Fin 1), s.2) := by rw [hao _ hs]; rfl
    rw [h1, MvPowerSeries.subst_X hbS]
    have h2 : s = (1 - g, s.2) := Prod.ext (fin_two_eq_one_sub_of_ne' g s.1 hs) rfl
    simp only [Pi.smul_apply', if_neg hs, one_smul]
    rw [← h2]

theorem coeff_eval_second_zero (G : PS C 2 dd) (μ : Fin dd →₀ ℕ) :
    MvPowerSeries.coeff (μ.mapDomain fun x : Fin dd => ((0 : Fin 1), x)) (ev (n := 1) ![pt C dd 0, 0] G) =
      MvPowerSeries.coeff (μ.mapDomain fun x : Fin dd => ((0 : Fin 2), x)) G := by
  have hk := subst_ev_kill G 1 ![pt C dd 0, 0] rfl (by
    intro g' hg'
    rw [fin_two_eq_one_sub_of_ne' 1 g' hg']
    rfl)
  have hinj : Function.Injective (fun q : Fin 1 × Fin dd => (((1 : Fin 2) - 1, q.2) : Fin 2 × Fin dd)) :=
    fun a b h => snd_injective_fin_one (Prod.mk.inj (show (((1 : Fin 2) - 1, a.2) : Fin 2 × Fin dd) = ((1 : Fin 2) - 1, b.2) from h)).2
  have h1 := coeff_subst_rename_inj (C := C) (fun q : Fin 1 × Fin dd => (((1 : Fin 2) - 1, q.2) : Fin 2 × Fin dd)) hinj
    (ev (n := 1) ![pt C dd 0, 0] G) (μ.mapDomain fun x : Fin dd => ((0 : Fin 1), x))
  rw [hk, ← Finsupp.mapDomain_comp, MvPowerSeries.coeff_rescale] at h1
  rw [← h1]
  have h2 : ((fun q : Fin 1 × Fin dd => (((1 : Fin 2) - 1, q.2) : Fin 2 × Fin dd)) ∘ fun x : Fin dd => ((0 : Fin 1), x)) =
      fun x : Fin dd => ((0 : Fin 2), x) := by
    funext x
    rfl
  rw [h2]
  have h3 : ((μ.mapDomain fun x : Fin dd => ((0 : Fin 2), x)).prod
      fun s m => (if s.1 = 1 then (0 : C) else 1) ^ m) = 1 := by
    unfold Finsupp.prod
    apply Finset.prod_eq_one
    intro s hs
    have hs' := Finsupp.mapDomain_support hs
    rw [Finset.mem_image] at hs'
    obtain ⟨x, _, rfl⟩ := hs'
    show (if (0 : Fin 2) = 1 then (0 : C) else 1) ^ _ = 1
    rw [if_neg (by decide), one_pow]
  rw [h3, one_mul]

end Kill

section SgSec

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} {I : Fin 2 → Type}
  [∀ g, Fintype (I g)] (Y : FBChart C V O dd) (p : PairData Y d I)

end SgSec

section AddSec

variable {dd : ℕ}

theorem pts_eq_X : (fun p : Fin 2 × Fin dd => ![pt C (n := 2) dd 0, pt C (n := 2) dd 1] p.1 p.2) = MvPowerSeries.X := by
  funext p
  rcases p with ⟨i, j⟩
  fin_cases i <;> first | rfl | simp [pt]

theorem addOf_pts (F : Fin dd → PS C 2 dd) (j : Fin dd) :
    addOf F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1) j = F j := by
  simp only [addOf, ev]
  rw [pts_eq_X, MvPowerSeries.subst_self]
  rfl

end AddSec

end Formalism.L2.FormalSeriesBounds
end
end
