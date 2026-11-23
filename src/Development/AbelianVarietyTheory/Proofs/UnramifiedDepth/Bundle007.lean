module

public import Mathlib.LinearAlgebra.Matrix.Defs
public import ReciprocityTheory.DualLattices.Bundle001
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.CoeffSubstInvMemOfTwoLeOrder
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Localization.FractionRing
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.RingTheory.Localization.Module
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PtOrderProdSub
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.Order.Ring.Pow

@[expose] public section

section

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh

noncomputable section

namespace GlobalTheory.IntegralEndLimit

theorem exists_real_le (x : WithTop ℝ) : ∃ t : ℝ, (t : WithTop ℝ) ≤ x := by
  cases x with
  | top => exact ⟨0, le_top⟩
  | coe t => exact ⟨t, le_rfl⟩

theorem le_val_mul {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {x y : C} {s t u : ℝ}
    (hx : (s : WithTop ℝ) ≤ v x) (hy : (t : WithTop ℝ) ≤ v y) (h : u ≤ s + t) :
    (u : WithTop ℝ) ≤ v (x * y) := by
  rw [v.map_mul]
  refine le_trans ?_ (add_le_add hx hy)
  rw [← WithTop.coe_add]
  exact WithTop.coe_le_coe.2 h

theorem eval_close {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {ι : Type}
    (x : ι → C) (Q : MvPolynomial ι C) (s : ℝ) :
    ∃ r : ℝ, ∀ x' : ι → C, (∀ i, (r : WithTop ℝ) ≤ v (x i - x' i)) →
      (s : WithTop ℝ) ≤ v (MvPolynomial.eval x Q - MvPolynomial.eval x' Q) := by
  induction Q using MvPolynomial.induction_on generalizing s with
  | C a => exact ⟨0, fun x' _ => by simp⟩
  | add p q hp hq =>
    obtain ⟨r₁, h₁⟩ := hp s
    obtain ⟨r₂, h₂⟩ := hq s
    refine ⟨max r₁ r₂, fun x' hx' => ?_⟩
    have e : MvPolynomial.eval x (p + q) - MvPolynomial.eval x' (p + q) =
        (MvPolynomial.eval x p - MvPolynomial.eval x' p) +
          (MvPolynomial.eval x q - MvPolynomial.eval x' q) := by
      simp only [map_add (f := _)]; ring
    rw [e]
    refine le_trans (le_min (h₁ x' fun i => le_trans ?_ (hx' i))
      (h₂ x' fun i => le_trans ?_ (hx' i))) (v.map_add _ _)
    · exact WithTop.coe_le_coe.2 (le_max_left _ _)
    · exact WithTop.coe_le_coe.2 (le_max_right _ _)
  | mul_X p i hp =>
    obtain ⟨a, ha⟩ := exists_real_le (v (MvPolynomial.eval x p))
    obtain ⟨b, hb⟩ := exists_real_le (v (x i))
    obtain ⟨r, hr⟩ := hp (s - b)
    refine ⟨max r (max (s - a) b), fun x' hx' => ?_⟩
    have h1 := hr x' fun j => le_trans (WithTop.coe_le_coe.2 (le_max_left _ _)) (hx' j)
    have h2 := hx' i
    have e : MvPolynomial.eval x (p * MvPolynomial.X i) - MvPolynomial.eval x' (p * MvPolynomial.X i)
        = MvPolynomial.eval x p * (x i - x' i) +
          ((MvPolynomial.eval x p - MvPolynomial.eval x' p) * x i +
            -((MvPolynomial.eval x p - MvPolynomial.eval x' p) * (x i - x' i))) := by
      simp only [map_mul, MvPolynomial.eval_X]; ring
    have m1 : s - a ≤ max r (max (s - a) b) := le_trans (le_max_left _ _) (le_max_right _ _)
    have m2 : b ≤ max r (max (s - a) b) := le_trans (le_max_right _ _) (le_max_right _ _)
    rw [e]
    refine le_trans (le_min (le_val_mul v ha h2 (by linarith))
      (le_trans (le_min (le_val_mul v h1 hb (by linarith)) ?_) (v.map_add _ _))) (v.map_add _ _)
    rw [v.map_neg]
    exact le_val_mul v h1 h2 (by linarith)

theorem exists_poly_coeff {C : Type} [Field C] {d : ℕ} (l : Fin d → MvPowerSeries (Fin d) C)
    (hl : ∀ a, constantCoeff (l a) = 0) (f : MvPowerSeries (Fin d) C) (α : Fin d →₀ ℕ) :
    ∃ Q : MvPolynomial (Fin d × Fin d) C, ∀ A : Matrix (Fin d) (Fin d) C,
      coeff α (subst (fun a => ∑ b, A a b • l b) f) =
        MvPolynomial.eval (fun p => A p.1 p.2) Q := by
  let ι : C →+* MvPolynomial (Fin d × Fin d) C := MvPolynomial.C
  let L : Fin d → MvPowerSeries (Fin d) (MvPolynomial (Fin d × Fin d) C) :=
    fun a => ∑ b, MvPowerSeries.C (MvPolynomial.X (a, b)) * map ι (l b)
  have hL : HasSubst L := hasSubst_of_constantCoeff_zero fun a => by
    simp [L, hl]
  refine ⟨coeff α (subst L (map ι f)), fun A => ?_⟩
  have hm : ∀ g : MvPowerSeries (Fin d) C,
      map (MvPolynomial.eval fun p : Fin d × Fin d => A p.1 p.2) (map ι g) = g := by
    intro g; ext β; simp [ι]
  rw [← coeff_map, map_subst hL, hm]
  congr 2
  funext a
  simp [L, hm, smul_eq_C_mul]

theorem integral_of_limit :
  (∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (d : ℕ) (G : LogFGL v d) (A : Matrix (Fin d) (Fin d) C),
    (∀ r : ℝ, ∃ A' : Matrix (Fin d) (Fin d) C, (∀ a b, (r : WithTop ℝ) ≤ v (A a b - A' a b)) ∧ ∃ φ : Fin d → MvPowerSeries (Fin d) C, (∀ a, MvIsInt v (φ a)) ∧ (∀ a, constantCoeff (φ a) = 0) ∧ ∀ a, subst φ (G.lg a) = ∑ b, A' a b • G.lg b) →
    ∃ φ : Fin d → MvPowerSeries (Fin d) C, (∀ a, MvIsInt v (φ a)) ∧ (∀ a, constantCoeff (φ a) = 0) ∧ ∀ a, subst φ (G.lg a) = ∑ b, A a b • G.lg b) := by
  intro C _ _ v d G A hA
  obtain ⟨ex, ⟨hex0, hr, hl⟩, -⟩ := GlobalTheory.FormalInv.formal_inverse_function_theorem.1 C d G.lg
    G.lg_const (by
      have : (Matrix.of fun i j => coeff (Finsupp.single j 1) (G.lg i) :
          Matrix (Fin d) (Fin d) C) = 1 := by
        ext i j; simp [G.lg_lin, Matrix.one_apply]
      rw [this]; exact isUnit_one)
  have hex : HasSubst ex := hasSubst_of_constantCoeff_zero hex0
  have hlg : HasSubst G.lg := hasSubst_of_constantCoeff_zero G.lg_const
  have h0 : ∀ a, constantCoeff (∑ b, A a b • G.lg b) = 0 := fun a => by
    simp [G.lg_const]
  have hs : HasSubst fun a => ∑ b, A a b • G.lg b := hasSubst_of_constantCoeff_zero h0
  refine ⟨fun a => subst (fun a => ∑ b, A a b • G.lg b) (ex a), fun a α => ?_,
    fun a => constantCoeff_subst_eq_zero hs h0 (hex0 a), fun a => ?_⟩
  · obtain ⟨Q, hQ⟩ := exists_poly_coeff G.lg G.lg_const (ex a) α
    obtain ⟨r, hr'⟩ := eval_close v (fun p : Fin d × Fin d => A p.1 p.2) Q 0
    obtain ⟨A', hA', φ, hφi, hφ0, hφ⟩ := hA r
    have hφs : HasSubst φ := hasSubst_of_constantCoeff_zero hφ0
    have e : subst (fun a => ∑ b, A' a b • G.lg b) (ex a) = φ a := by
      rw [← funext hφ, ← subst_comp_subst_apply hlg hφs, hl, subst_X hφs]
    have h1 := hr' (fun p => A' p.1 p.2) fun p => hA' p.1 p.2
    have h2 : (0 : WithTop ℝ) ≤ v (MvPolynomial.eval (fun p : Fin d × Fin d => A' p.1 p.2) Q) := by
      rw [← hQ, e]; exact hφi a α
    show 0 ≤ v _
    rw [hQ, ← sub_add_cancel (MvPolynomial.eval (fun p : Fin d × Fin d => A p.1 p.2) Q)
      (MvPolynomial.eval (fun p : Fin d × Fin d => A' p.1 p.2) Q)]
    exact le_trans (le_min h1 h2) (v.map_add _ _)
  · rw [← subst_comp_subst_apply hex hs, hr, subst_X hs]

end GlobalTheory.IntegralEndLimit
end
end

section

open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField

namespace GlobalTheory

theorem exists_integral_basis_linear_coordinates :
    ∀ (V K C : Type) [CommRing V] [IsDomain V] [IsPrincipalIdealRing V] [Field K] [Algebra V K] [IsFractionRing V K] [Field C] [Algebra K C] (R : Subring C), (∀ x : V, algebraMap K C (algebraMap V K x) ∈ R) → ∀ s : Finset C, (∀ x ∈ s, x ∈ R) → ∃ (r : ℕ) (c : Fin r → C) (φ : Fin r → (C →ₗ[K] K)), (∀ j, c j ∈ R) ∧ ∀ x ∈ s, (∀ j, φ j x ∈ (algebraMap V K).range) ∧ x = ∑ j, algebraMap K C (φ j x) * c j := by
  intro V K C _ _ _ _ _ _ _ _ R hR s hs
  classical
  letI : Algebra V C := ((algebraMap K C).comp (algebraMap V K)).toAlgebra
  haveI : IsScalarTower V K C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hinj : Function.Injective (algebraMap V C) :=
    (algebraMap K C).injective.comp (IsFractionRing.injective V K)
  haveI : FaithfulSMul V C := (faithfulSMul_iff_algebraMap_injective V C).2 hinj
  let M : Submodule V C := Submodule.span V (s : Set C)
  haveI : Module.Finite V M := Module.Finite.span_of_finite V s.finite_toSet
  haveI : Module.Free V M := inferInstance
  have hMR : ∀ x ∈ M, x ∈ R := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hs x hx
    | zero => exact R.zero_mem
    | add x y _ _ hx hy => exact R.add_mem hx hy
    | smul a x _ hx =>
      rw [Algebra.smul_def]
      exact R.mul_mem (hR a) hx
  let b := Module.finBasis V M
  let c : Fin (Module.finrank V M) → C := fun j => (b j : C)
  have hcV : LinearIndependent V c :=
    b.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  have hcK : LinearIndependent K c := (LinearIndependent.iff_fractionRing V K).1 hcV
  obtain ⟨g, hg⟩ := (Fintype.linearCombination K c).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 (by
      exact hcK.fintypeLinearCombination_injective))
  refine ⟨_, c, fun j => (LinearMap.proj j).comp g, fun j => hMR _ (b j).2, ?_⟩
  intro x hx
  have hxM : x ∈ M := Submodule.subset_span hx
  have h1 : x = Fintype.linearCombination K c (fun j => algebraMap V K (b.repr ⟨x, hxM⟩ j)) := by
    have := congrArg Subtype.val (b.sum_repr ⟨x, hxM⟩)
    simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at this
    rw [Fintype.linearCombination_apply]
    simp only [algebraMap_smul]
    exact this.symm
  have h2 : g x = fun j => algebraMap V K (b.repr ⟨x, hxM⟩ j) := by
    have := LinearMap.congr_fun hg (fun j => algebraMap V K (b.repr ⟨x, hxM⟩ j))
    rw [LinearMap.comp_apply, ← h1] at this
    exact this
  refine ⟨fun j => ⟨b.repr ⟨x, hxM⟩ j, ?_⟩, ?_⟩
  · simp [h2]
  · simp only [LinearMap.comp_apply, LinearMap.proj_apply, h2, ← Algebra.smul_def]
    rw [Fintype.linearCombination_apply] at h1
    exact h1

end GlobalTheory
end

section

open ReciprocityTheory.PGsh

namespace GlobalTheory.ExpWeight

open MvPowerSeries

variable {C : Type} [Field C] {M : ℕ}

def OrdBelow (v : AddValuation C (WithTop ℝ)) (ρ : ℝ) (D : ℕ) (g : MvPowerSeries (Fin M) C)
    (r : ℝ) : Prop :=
  ∀ α : Fin M →₀ ℕ, Finsupp.degree α < D →
    (((r - ρ * (Finsupp.degree α : ℕ) : ℝ)) : WithTop ℝ) ≤ v (coeff α g)

theorem OrdBelow.mul {v : AddValuation C (WithTop ℝ)} {ρ : ℝ} {D : ℕ}
    {g h : MvPowerSeries (Fin M) C} {r s : ℝ} (hg0 : constantCoeff g = 0)
    (hh0 : constantCoeff h = 0) (hg : OrdBelow v ρ D g r) (hh : OrdBelow v ρ D h s) :
    OrdBelow v ρ (D + 1) (g * h) (r + s) := by
  classical
  intro α hα
  rw [coeff_mul]
  refine v.map_le_sum fun p hp => ?_
  have hp' : p.1 + p.2 = α := by simpa using hp
  by_cases h1 : p.1 = 0
  · rw [h1, coeff_zero_eq_constantCoeff_apply, hg0, zero_mul, v.map_zero]; exact le_top
  by_cases h2 : p.2 = 0
  · rw [h2, coeff_zero_eq_constantCoeff_apply, hh0, mul_zero, v.map_zero]; exact le_top
  have hd : Finsupp.degree p.1 + Finsupp.degree p.2 = Finsupp.degree α := by
    rw [← hp', map_add (f := _)]
  have d1 : Finsupp.degree p.1 ≠ 0 := fun e => h1 ((Finsupp.degree_eq_zero_iff _).1 e)
  have d2 : Finsupp.degree p.2 ≠ 0 := fun e => h2 ((Finsupp.degree_eq_zero_iff _).1 e)
  rw [v.map_mul]
  refine le_trans (le_of_eq ?_) (add_le_add (hg p.1 (by omega)) (hh p.2 (by omega)))
  rw [← WithTop.coe_add, ← hd]
  congr 1
  push_cast
  ring

theorem OrdBelow.pow_succ {v : AddValuation C (WithTop ℝ)} {ρ : ℝ} {D : ℕ}
    {g : MvPowerSeries (Fin M) C} {r : ℝ} (hg0 : constantCoeff g = 0)
    (hg : OrdBelow v ρ D g r) (k : ℕ) :
    OrdBelow v ρ D (g ^ (k + 1)) (((k + 1 : ℕ) : ℝ) * r) := by
  induction k with
  | zero => simpa using hg
  | succ k ih =>
    have h := OrdBelow.mul (by simp [hg0]) hg0 ih hg
    intro α hα
    have h' := h α (by omega)
    rw [_root_.pow_succ g (k + 1)]
    refine le_trans (le_of_eq ?_) h'
    congr 1
    push_cast
    ring

theorem OrdBelow.pow {v : AddValuation C (WithTop ℝ)} {ρ : ℝ} {D : ℕ}
    {g : MvPowerSeries (Fin M) C} {r : ℝ} (hg0 : constantCoeff g = 0)
    (hg : OrdBelow v ρ D g r) {N : ℕ} (hN : 2 ≤ N) :
    OrdBelow v ρ (D + 1) (g ^ N) ((N : ℝ) * r) := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 + 1 := ⟨N - 2, by omega⟩
  have h := OrdBelow.mul (by simp [hg0]) hg0 (hg.pow_succ hg0 k) hg
  rw [_root_.pow_succ g (k + 1)]
  convert h using 1
  push_cast
  ring

theorem ordGe_of_lgSum_eq_linear :
  (∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ), l.Prime → v (l : C) = 1 → ∀ (d M : ℕ) (al : Fin d → ℕ → Fin d → C) (z : Fin d → Fin M → C) (t : Fin d → MvPowerSeries (Fin M) C),
    (∀ c e, al c 0 e = if c = e then 1 else 0) → (∀ c (n : ℕ) e, ((-(n : ℝ) : ℝ) : WithTop ℝ) ≤ v (al c n e)) → (∀ c j, 0 ≤ v (z c j)) →
    (∀ c, MvPowerSeries.constantCoeff (t c) = 0) → (∀ e, lgSum l al t e = ∑ j, MvPowerSeries.C (z e j) * MvPowerSeries.X j) →
    ∀ c, OrdGe v (fun _ => 1 / ((l : ℝ) - 1)) (t c) (1 / ((l : ℝ) - 1))) := by
  intro C _ _ v l hl _ d M al z t h0 hal hz ht hlg
  classical
  set ρ : ℝ := 1 / ((l : ℝ) - 1) with hρ
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast hl.two_le
  have hρ1 : ρ * ((l : ℝ) - 1) = 1 := by
    rw [hρ]; field_simp [show (l : ℝ) - 1 ≠ 0 by linarith]
  have hρ0 : 0 < ρ := by rw [hρ]; apply one_div_pos.2; linarith
  have key : ∀ D : ℕ, ∀ c, OrdBelow v ρ D (t c) ρ := by
    intro D
    induction D with
    | zero => intro c α hα; omega
    | succ D ih =>
      intro e α hα
      have h1 : coeff α (lgSum l al t e) = coeff α (∑ j, MvPowerSeries.C (z e j) * MvPowerSeries.X j) := by
        rw [hlg e]
      have h2 : coeff α (lgSum l al t e) =
          ∑ n ∈ Finset.range (Finsupp.degree α + 1), ∑ a, al a n e * coeff α (t a ^ (l ^ n)) := rfl
      rw [h2, Finset.sum_range_succ'] at h1
      have h3 : ∑ a, al a 0 e * coeff α (t a ^ (l ^ 0)) = coeff α (t e) := by
        simp [h0]
      rw [h3] at h1
      rw [eq_sub_of_add_eq' h1]
      refine v.map_le_sub ?_ ?_
      · rw [map_sum]
        refine v.map_le_sum fun j _ => ?_
        rw [coeff_C_mul, coeff_X]
        split_ifs with hj
        · rw [hj, mul_one]
          simpa using hz e j
        · rw [mul_zero, v.map_zero]; exact le_top
      · refine v.map_le_sum fun n _ => v.map_le_sum fun a _ => ?_
        have hN : 2 ≤ l ^ (n + 1) := le_trans hl.two_le (Nat.le_self_pow (by omega) l)
        have h4 := (ih a).pow (ht a) hN α hα
        rw [v.map_mul]
        refine le_trans ?_ (add_le_add (hal a (n + 1) e) h4)
        rw [← WithTop.coe_add, WithTop.coe_le_coe]
        have hb := one_add_mul_sub_le_pow (a := (l : ℝ)) (by linarith) (n + 1)
        have hb' := mul_le_mul_of_nonneg_left hb hρ0.le
        push_cast at hb' ⊢
        have : ρ * (1 + ((n : ℝ) + 1) * (l - 1)) = ρ + (n + 1) := by
          linear_combination ((n : ℝ) + 1) * hρ1
        linarith
  intro c α
  have h := key (Finsupp.degree α + 1) c α (by omega)
  refine le_trans (le_of_eq ?_) h
  congr 2
  rw [Finsupp.degree_eq_sum, ← Finset.mul_sum]
  push_cast
  rfl

end GlobalTheory.ExpWeight
end

section

open ReciprocityTheory.PGsh

namespace GlobalTheory.WeightSubst

open MvPowerSeries

variable {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {σ : Type} [Fintype σ]
  [DecidableEq σ] (ρ : σ → ℝ)

def WtNonneg (g : MvPowerSeries σ C) : Prop :=
  ∀ α : σ →₀ ℕ, ((0 - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (coeff α g)

omit [Fintype σ] in
theorem wtNonneg_one : WtNonneg v ρ (1 : MvPowerSeries σ C) := by
  intro α
  rw [coeff_one]
  split_ifs with h
  · subst h
    simp
  · simp

omit [Fintype σ] in
theorem wtNonneg_mul {f g : MvPowerSeries σ C} (hf : WtNonneg v ρ f) (hg : WtNonneg v ρ g) :
    WtNonneg v ρ (f * g) := by
  intro α
  rw [coeff_mul]
  apply AddValuation.map_le_sum
  intro p hp
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [AddValuation.map_mul]
  have e : ((0 - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) =
      ((0 - p.1.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) +
        ((0 - p.2.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) := by
    rw [← WithTop.coe_add, ← hp, Finsupp.sum_add_index' (by simp) (by intros; push_cast; ring)]
    congr 1
    ring
  rw [e]
  exact add_le_add (hf p.1) (hg p.2)

omit [Fintype σ] in
theorem wtNonneg_prod {ι : Type*} (s : Finset ι) (f : ι → MvPowerSeries σ C)
    (h : ∀ i ∈ s, WtNonneg v ρ (f i)) : WtNonneg v ρ (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using wtNonneg_one v ρ
  | insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact wtNonneg_mul v ρ (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

omit [Fintype σ] in
theorem wtNonneg_pow {f : MvPowerSeries σ C} (hf : WtNonneg v ρ f) (n : ℕ) :
    WtNonneg v ρ (f ^ n) := by
  induction n with
  | zero => simpa using wtNonneg_one v ρ
  | succ k ih =>
    rw [pow_succ]
    exact wtNonneg_mul v ρ ih hf

theorem weight_subst_nonneg :
  (∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (σ τ : Type) [Fintype σ] [DecidableEq σ] [Fintype τ] (ρ : σ → ℝ) (K : MvPowerSeries τ C) (t : τ → MvPowerSeries σ C),
    MvIsInt v K → (∀ c, MvPowerSeries.constantCoeff (t c) = 0) → (∀ c, (∀ α, (((0) - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (t c)))) → (∀ α, (((0) - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (MvPowerSeries.subst t K)))) := by
  intro C _ v σ τ _ _ _ ρ K t hK ht0 ht α
  have hs : MvPowerSeries.HasSubst t := MvPowerSeries.hasSubst_of_constantCoeff_zero ht0
  rw [MvPowerSeries.coeff_subst hs, finsum_eq_sum _ (MvPowerSeries.coeff_subst_finite hs K α)]
  apply AddValuation.map_le_sum
  intro d _
  rw [smul_eq_mul, AddValuation.map_mul]
  have h1 : (0 : WithTop ℝ) ≤ v (MvPowerSeries.coeff d K) := hK d
  have h2 : WtNonneg v ρ (d.prod fun c e => t c ^ e) := by
    unfold Finsupp.prod
    exact wtNonneg_prod v ρ _ _ (fun c _ => wtNonneg_pow v ρ (ht c) _)
  have h3 := add_le_add h1 (h2 α)
  rwa [zero_add] at h3

end GlobalTheory.WeightSubst
end
