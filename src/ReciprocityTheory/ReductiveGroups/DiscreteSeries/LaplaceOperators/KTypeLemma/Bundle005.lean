module

import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.WeightVectorTensorEqDual
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.CompRevRev
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.QuotientHighestWeightTensorStandard
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.Bundle003
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.ODE.ExistUnique
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK.TwistedDualLemmas

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.LemK

variable {n : ℕ}

section Tens

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem tensV_apply' (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : Fin n → M) (c : Fin n) :
    tensV E a b f c = E a b (f c) + (if c = a then f b else 0) := by
  simp only [tensV, LinearMap.pi_apply, LinearMap.add_apply, LinearMap.comp_apply]
  split_ifs <;> simp [prj]

theorem tensVd_apply' (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : Fin n → M) (c : Fin n) :
    tensVd E a b f c = E a b (f c) - (if c = b then f a else 0) := by
  simp only [tensVd, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.comp_apply]
  split_ifs <;> simp [prj]

theorem eeV_apply' (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) (d : Fin n) :
    eeV E f d = ∑ c, E c d (f c) := by
  simp [eeV, prj, LinearMap.sum_apply]

theorem eeVd_apply' (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) (d : Fin n) :
    eeVd E f d = -∑ c, E d c (f c) := by
  simp [eeVd, prj, LinearMap.sum_apply]

def twT (ε : Fin n → Bool) : (Fin n → M) →ₗ[ℂ] (Fin n → M) :=
  LinearMap.pi fun c => sg ε (Fin.rev c) • prj (Fin.rev c)

theorem twT_apply (ε : Fin n → Bool) (f : Fin n → M) (c : Fin n) :
    twT ε f c = sg ε (Fin.rev c) • f (Fin.rev c) := by
  simp [twT, prj]

theorem twT_eq_zero {ε : Fin n → Bool} {f : Fin n → M} (h : twT ε f = 0) : f = 0 := by
  funext c
  have := congrFun h (Fin.rev c)
  rw [twT_apply, Fin.rev_rev] at this
  exact (smul_eq_zero.1 this).resolve_left (sg_ne ε c)

theorem twT_tens (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : Fin n → M) :
    tensV (twE ε E) a b (twT ε f) = twT ε (twE ε (tensVd E) a b f) := by
  funext c
  rw [tensV_apply', twT_apply, twT_apply, twE_apply, twE_apply, map_smul (twT ε), Pi.smul_apply,
    twT_apply, tensVd_apply', map_smul]
  simp only [Fin.rev_inj]
  by_cases hc : c = a
  · subst hc
    simp only [if_true]
    unfold sg; split_ifs <;> module
  · simp [hc]

theorem twT_ee (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) :
    eeV (twE ε E) (twT ε f) = twT ε (eeVd E f) := by
  funext d
  rw [eeV_apply', twT_apply, eeVd_apply', smul_neg, Finset.smul_sum,
    ← sum_rev (fun c => sg ε (Fin.rev d) • E (Fin.rev d) c (f c)), ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [twT_apply, twE_apply, map_smul, smul_smul, ← neg_smul]
  congr 1
  linear_combination (-sg ε (Fin.rev d)) * sg_sq ε (Fin.rev c)

theorem mem_Xs {A : Module.End ℂ (Fin n → M)} {S : Submodule ℂ M} {θ : ℝ} {f : Fin n → M} :
    f ∈ Xs A S θ ↔ (∀ c, f c ∈ S) ∧ A f = ((θ : ℝ) : ℂ) • f := by
  simp [Xs, Submodule.mem_inf, Submodule.mem_pi, LinearMap.mem_ker, sub_eq_zero]

theorem xs_tw {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} {S : Submodule ℂ M} {θ : ℝ}
    {f : Fin n → M} (h : f ∈ Xs (eeVd E) S θ) : twT ε f ∈ Xs (eeV (twE ε E)) S θ := by
  rw [mem_Xs] at h ⊢
  refine ⟨fun c => ?_, ?_⟩
  · rw [twT_apply]; exact S.smul_mem _ (h.1 _)
  · rw [twT_ee, h.2, map_smul]

theorem khwT_tw {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} {μ : Fin n → ℝ}
    {f : Fin n → M} (h : IsKHWVec ε (tensVd E) μ f) :
    IsKHWVec (ε ∘ Fin.rev) (tensV (twE ε E)) (fun a => -μ (Fin.rev a)) (twT ε f) := by
  have h' := khw_tw h
  exact ⟨fun a => by rw [twT_tens, h'.1, map_smul], fun a b hab he => by
    rw [twT_tens, h'.2 a b hab he, map_zero]⟩

end Tens

section Wt

theorem rhoN_tw (ε : Fin n → Bool) (a : Fin n) : rhoN (ε ∘ Fin.rev) a = -rhoN ε (Fin.rev a) := by
  apply ReciprocityTheory.ChartRestriction.DS.Lap.LemK.DualRepresentationReversal.rhoN_rev <;> assumption

theorem rhoC_tw (ε : Fin n → Bool) (a : Fin n) : rhoC (ε ∘ Fin.rev) a = -rhoC ε (Fin.rev a) := by
  apply ReciprocityTheory.ChartRestriction.DS.Lap.LemK.DualRepresentationReversal.rhoC_rev <;> assumption

theorem lowK_tw (ε : Fin n → Bool) (ν : Fin n → ℝ) :
    lowK (ε ∘ Fin.rev) (fun a => -ν (Fin.rev a)) = fun a => -lowK ε ν (Fin.rev a) := by
  funext a
  simp only [lowK, Pi.add_apply, Pi.sub_apply, rhoN_tw, rhoC_tw]
  ring

theorem casVal_tw (lam : Fin n → ℝ) : casVal (fun a => -lam (Fin.rev a)) = casVal lam := by
  unfold casVal nsq dot
  simp only [neg_mul_neg]
  rw [sum_rev (fun a => lam a * lam a)]

theorem pOf_tw (ε : Fin n → Bool) : pOf (ε ∘ Fin.rev) = pOf ε := by
  unfold pOf
  refine Finset.card_nbij' Fin.rev Fin.rev ?_ ?_ ?_ ?_ <;> intro b hb <;> simp_all

theorem qOf_tw (ε : Fin n → Bool) : qOf (ε ∘ Fin.rev) = qOf ε := by
  unfold qOf
  refine Finset.card_nbij' Fin.rev Fin.rev ?_ ?_ ?_ ?_ <;> intro b hb <;> simp_all

theorem gapLap_tw {ε : Fin n → Bool} {lam : Fin n → ℝ} {h : ℝ} (hg : GapLap ε lam h) :
    GapLap (ε ∘ Fin.rev) (fun a => -lam (Fin.rev a)) h := by
  obtain ⟨h1, h2, h3⟩ := hg
  refine ⟨fun a b hab => ?_, fun a b hab => ?_, ?_⟩
  · have := h1 (Fin.rev_lt_rev.2 hab)
    simp only; linarith
  · have := h2 (Fin.rev a) (Fin.rev b) hab
    rw [abs_sub_comm] at this
    simp only; rwa [neg_sub_neg]
  · have e : hNeed (ε ∘ Fin.rev) = hNeed ε := by unfold hNeed; rw [pOf_tw, qOf_tw]
    rw [e]; exact h3

theorem root_rev (a b x : Fin n) : root (Fin.rev b) (Fin.rev a) x = -root a b (Fin.rev x) := by
  have e : ∀ i j : Fin n, (j = Fin.rev i ↔ Fin.rev j = i) := fun i j => by
    constructor <;> rintro rfl <;> simp
  simp only [root, Pi.sub_apply, Pi.single_apply, e]
  ring

theorem cone_ev (k : Fin n → Fin n → ℕ) (y : Fin n) :
    (∑ a, ∑ b, if a < b then (k a b : ℝ) • root a b else 0) y =
      ∑ a, ∑ b, if a < b then (k a b : ℝ) * root a b y else 0 := by
  simp only [Finset.sum_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs <;> simp

theorem cone_rev {β : Fin n → ℝ} (h : InRootCone (fun a => -β (Fin.rev a))) : InRootCone β := by
  obtain ⟨m, hm⟩ := h
  refine ⟨fun a b => m (Fin.rev b) (Fin.rev a), ?_⟩
  funext x
  have hx := congrFun hm (Fin.rev x)
  simp only [Fin.rev_rev] at hx
  rw [cone_ev] at hx
  rw [cone_ev, show β x = -(-β x) by ring, hx, ← sum_rev, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← sum_rev, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Fin.rev_rev, Fin.rev_lt_rev, root_rev]
  split_ifs <;> ring

end Wt

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK.TwistedDualLemmas
end
end

section

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK.TRA

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem ode_zero {U : Type*} [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U] (A : Module.End ℂ U)
    (G : ℝ → U →ₗ[ℂ] ℂ) (hG : ∀ s y, HasDerivAt (fun s => G s y) (-(G s (A y))) s) (h0 : G 0 = 0)
    (s : ℝ) : G s = 0 := by
  let b := Module.finBasis ℂ U
  let L : (Fin (Module.finrank ℂ U) → ℂ) →L[ℂ] (Fin (Module.finrank ℂ U) → ℂ) :=
    LinearMap.toContinuousLinearMap
      (LinearMap.pi fun i => -∑ j, b.repr (A (b i)) j • LinearMap.proj j)
  have hg : ∀ t, HasDerivAt (fun s i => G s (b i)) (L fun i => G t (b i)) t := by
    intro t
    rw [hasDerivAt_pi]
    intro i
    refine (hG t (b i)).congr_deriv ?_
    have := congrArg (G t) (b.sum_repr (A (b i)))

    simp only [map_sum, map_smul, smul_eq_mul] at this
    simp [L, this]
  have hz := ODE_solution_unique_univ (v := fun _ x => L x) (s := fun _ => Set.univ) (K := ‖L‖₊)
    (t₀ := 0) (f := fun s i => G s (b i)) (g := fun _ => 0)
    (fun _ => L.lipschitz.lipschitzOnWith) (fun t => ⟨hg t, trivial⟩)
    (fun t => ⟨by simpa using hasDerivAt_const t (0 : Fin (Module.finrank ℂ U) → ℂ), trivial⟩)
    (by funext i; simp [h0])
  exact b.ext fun i => congrFun (congrFun hz s) i

def ei (X : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  NormedSpace.exp (((-s : ℝ) : ℂ) • X)

def cj (X : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (Y : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ei X s * Y * NormedSpace.exp ((s : ℂ) • X)

open scoped Matrix.Norms.Operator in
theorem deriv_entries (X Y : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (a b : Fin n) :
    HasDerivAt (fun s => ei X s a b) (-((ei X s * X) a b)) s ∧
      HasDerivAt (fun s => cj X s Y a b) (-(cj X s (X * Y - Y * X) a b)) s := by
  have h1 := hasDerivAt_exp_smul_const (𝕂 := ℝ) (-X) s
  have h2 := hasDerivAt_exp_smul_const' (𝕂 := ℝ) X s
  have e : ∀ s : ℝ, s • (-X) = ((-s : ℝ) : ℂ) • X := fun s => by
    rw [Complex.coe_smul, smul_neg, neg_smul]
  have e' : ∀ s : ℝ, s • X = (s : ℂ) • X := fun s => (Complex.coe_smul s X).symm
  simp only [e] at h1
  simp only [e'] at h2
  let P := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ a b)
  refine ⟨(P.hasFDerivAt.comp_hasDerivAt s h1).congr_deriv ?_,
    (P.hasFDerivAt.comp_hasDerivAt s ((h1.mul_const Y).mul h2)).congr_deriv ?_⟩
  · show (ei X s * -X) a b = _
    rw [Matrix.mul_neg]; rfl
  · show (ei X s * -X * Y * NormedSpace.exp ((s : ℂ) • X) +
      ei X s * Y * (X * NormedSpace.exp ((s : ℂ) • X))) a b = _
    have e2 : ei X s * -X * Y * NormedSpace.exp ((s : ℂ) • X) +
        ei X s * Y * (X * NormedSpace.exp ((s : ℂ) • X)) = -cj X s (X * Y - Y * X) := by
      simp only [cj]; noncomm_ring
    rw [e2]; rfl

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

def actL (E : Fin n → Fin n → Module.End ℂ M) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ M where
  toFun := actM E
  map_add' X Y := by simp [actM, add_smul, sum_add_distrib]
  map_smul' c X := by simp [actM, smul_sum, smul_smul]

theorem actM_single (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) :
    actM E (Matrix.single a b 1) = E a b := by
  simp [actM, Matrix.single_apply, ite_smul, ite_and]

def wB (E : Fin n → Fin n → Module.End ℂ M) (φ : M) (X : Matrix (Fin n) (Fin n) ℂ) (s : ℝ)
    (w : List (Fin n × Fin n)) : M :=
  (w.map fun p => actM E (cj X s (Matrix.single p.1 p.2 1))).prod φ

def adX (X : Matrix (Fin n) (Fin n) ℂ) (w : List (Fin n × Fin n)) : List (Fin n × Fin n) →₀ ℂ :=
  ∑ a, ∑ b, X a b • adLW a b w

theorem lc_adL (a b : Fin n) (p : Fin n × Fin n) :
    Finsupp.linearCombination ℂ (fun q : Fin n × Fin n => (Matrix.single q.1 q.2 1 : Matrix (Fin n) (Fin n) ℂ))
      (adL a b p) = Matrix.single a b 1 * Matrix.single p.1 p.2 1 -
        Matrix.single p.1 p.2 1 * Matrix.single a b 1 := by
  rw [adL, map_sub]
  congr 1
  · split_ifs with h
    · subst h; simp
    · simp [Matrix.single_mul_single_of_ne _ _ _ _ h]
  · split_ifs with h
    · subst h; simp
    · simp [Matrix.single_mul_single_of_ne _ _ _ _ h]

theorem lc_adX_cons (E : Fin n → Fin n → Module.End ℂ M) (φ : M) (X : Matrix (Fin n) (Fin n) ℂ) (s : ℝ)
    (p : Fin n × Fin n) (w : List (Fin n × Fin n)) :
    Finsupp.linearCombination ℂ (wB E φ X s) (adX X (p :: w)) =
      actM E (cj X s (X * Matrix.single p.1 p.2 1 - Matrix.single p.1 p.2 1 * X)) (wB E φ X s w) +
        actM E (cj X s (Matrix.single p.1 p.2 1))
          (Finsupp.linearCombination ℂ (wB E φ X s) (adX X w)) := by
  let C : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] M :=
    { toFun := fun Y => actM E (cj X s Y) (wB E φ X s w)
      map_add' := fun Y Y' => by
        have := (actL E).map_add (cj X s Y) (cj X s Y')
        simp only [cj, Matrix.mul_add, Matrix.add_mul]
        exact congrArg (fun A : Module.End ℂ M => A (wB E φ X s w)) this
      map_smul' := fun c Y => by
        have := (actL E).map_smul c (cj X s Y)
        simp only [cj, Matrix.mul_smul, Matrix.smul_mul]
        exact congrArg (fun A : Module.End ℂ M => A (wB E φ X s w)) this }
  have h1 : ∀ u : (Fin n × Fin n) →₀ ℂ,
      Finsupp.linearCombination ℂ (wB E φ X s) (u.mapDomain (· :: w)) =
        C (Finsupp.linearCombination ℂ
          (fun q : Fin n × Fin n => (Matrix.single q.1 q.2 1 : Matrix (Fin n) (Fin n) ℂ)) u) := fun u => by
    rw [Finsupp.linearCombination_mapDomain, Finsupp.apply_linearCombination]; rfl
  have h2 : ∀ u : List (Fin n × Fin n) →₀ ℂ,
      Finsupp.linearCombination ℂ (wB E φ X s) (u.mapDomain (p :: ·)) =
        actM E (cj X s (Matrix.single p.1 p.2 1)) (Finsupp.linearCombination ℂ (wB E φ X s) u) :=
    fun u => by rw [Finsupp.linearCombination_mapDomain, Finsupp.apply_linearCombination]; rfl
  have h3 : X * Matrix.single p.1 p.2 1 - Matrix.single p.1 p.2 1 * X =
      ∑ a, ∑ b, X a b • ((Matrix.single a b 1 : Matrix (Fin n) (Fin n) ℂ) * Matrix.single p.1 p.2 1 -
        Matrix.single p.1 p.2 1 * Matrix.single a b 1) := by
    have hX : X = ∑ a, ∑ b, X a b • (Matrix.single a b 1 : Matrix (Fin n) (Fin n) ℂ) := by
      conv_lhs => rw [Matrix.matrix_eq_sum_single X]
      simp
    conv_lhs => rw [hX]
    simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul, smul_sub,
      sum_sub_distrib]
  show _ = C _ + _
  rw [h3]

  simp only [adX, adLW, map_sum, map_smul, map_add (f := _), smul_add, sum_add_distrib, h1, h2, lc_adL]

theorem deriv_word (E : Fin n → Fin n → Module.End ℂ M) (φ : M) (X : Matrix (Fin n) (Fin n) ℂ) (s : ℝ)
    (w : List (Fin n × Fin n)) : ∀ l : M →ₗ[ℂ] ℂ, HasDerivAt (fun s => l (wB E φ X s w))
      (-(l (Finsupp.linearCombination ℂ (wB E φ X s) (adX X w)))) s := by
  induction w with
  | nil => intro l; simpa [wB, adX, adLW] using hasDerivAt_const s (l φ)
  | cons p w ih =>
    intro l
    have e : (fun s => l (wB E φ X s (p :: w))) = fun s => ∑ a, ∑ b,
        cj X s (Matrix.single p.1 p.2 1) a b * (l ∘ₗ E a b) (wB E φ X s w) := by
      funext s

      simp [wB, actM, map_sum]
    rw [e]
    refine (HasDerivAt.fun_sum fun a _ => HasDerivAt.fun_sum fun b _ =>
      ((deriv_entries X (Matrix.single p.1 p.2 1) s a b).2.mul (ih (l ∘ₗ E a b)))).congr_deriv ?_
    rw [lc_adX_cons]

    simp only [actM, LinearMap.sum_apply, LinearMap.smul_apply, map_add (f := _), map_sum, map_smul,
    smul_eq_mul, LinearMap.comp_apply, neg_add, ← sum_neg_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring

theorem adLW_length (a b : Fin n) : ∀ (w w' : List (Fin n × Fin n)), w' ∈ (adLW a b w).support →
    w'.length = w.length := by
  classical
  intro w
  induction w with
  | nil => intro w' h; simp [adLW] at h
  | cons p w ih =>
    intro w' h
    rcases mem_union.mp (Finsupp.support_add h) with h | h
    · obtain ⟨q, -, rfl⟩ := mem_image.mp (Finsupp.mapDomain_support h); rfl
    · obtain ⟨q, hq, rfl⟩ := mem_image.mp (Finsupp.mapDomain_support h)
      simp [ih q hq]

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK.TRA
end
end

section

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

theorem capelliQdet : CapelliQdetStatement := by
  refine ⟨fun 𝒰 _ _ n E x => ?_, fun n lam ω => ?_⟩
  · unfold Capelli.capelliC Capelli.cminor Formalism.REAL.qdet Formalism.REAL.qminor
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [zsmul_eq_mul]
    congr 1
    congr 1
    refine congrArg List.ofFn (funext fun j => ?_)
    simp only [Capelli.capEntry, Formalism.REAL.Tm, id, add_comm]
  · unfold Formalism.QuantumDeterminants.capP thV
    refine Finset.prod_congr rfl fun t _ => ?_
    push_cast
    ring

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end

section

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

theorem gapCentral (n : ℕ) : GapCentralStatement n := by
  intro ε lam h ⟨_, hg, hN⟩
  unfold hNeed at hN
  have hA := (le_max_left _ _).trans_lt hN
  have hB := (le_max_right _ _).trans_lt hN
  have hB1 := (le_max_left _ _).trans_lt hB
  have hB2 := (le_max_right _ _).trans_lt hB
  have hA1 : 1 + (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) ≤
      max (3 * (n : ℝ) / 2) (1 + (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ)) := le_max_right _ _
  have hM : 2 * (n : ℝ) * (min (pOf ε) (qOf ε) : ℝ) ≤
      max (2 * (n : ℝ) * (min (pOf ε) (qOf ε) : ℝ)) (2 * ((qOf ε : ℝ) - 1) * (n : ℝ) ^ 2) := le_max_left _ _
  have hs := Real.sqrt_nonneg (2 * (min (pOf ε) (qOf ε) : ℝ))
  have hn : (0 : ℝ) ≤ (n : ℝ) * (min (pOf ε) (qOf ε) : ℝ) := by positivity
  have hP := mul_nonneg hs (by linarith : (0 : ℝ) ≤
      4 * max (2 * (n : ℝ) * (min (pOf ε) (qOf ε) : ℝ)) (2 * ((qOf ε : ℝ) - 1) * (n : ℝ) ^ 2) + 1 -
        (n : ℝ) * (min (pOf ε) (qOf ε) : ℝ))
  exact ⟨hg, by linarith, by linarith, by nlinarith⟩

theorem hcV_of_centralChar (n : ℕ) (hCC : CentralCharStatement n) : HcVStatement n := by
  intro ε lam h H _ _ _ σ D E V hσ hD hV hc hVK hint hanti hgap hp hq ω y hy
  have hle : V ≤ genSub E V := le_sInf fun T hT => hT.1
  exact hCC ε lam h H σ D E V hσ hD hV hc hVK hint hanti hgap hp hq ω y (hle hy)

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end
