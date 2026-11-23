module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle009
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

@[expose] public section

section

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def InW (D : Formalism.BasicNotions.D7) (y : (VS D).V) : Prop :=
  (∀ a, (VS D).hT (D.sp.hypE a) y = 0) ∧ (∀ a, (VS D).hT (D.sp.hypF a) y = 0) ∧ (VS D).hT D.sp.zm y = 0

theorem hT_star (D : Formalism.BasicNotions.D7) (x y : (VS D).V) : star ((VS D).hT x y) = (VS D).hT y x := by
  have h := (VS D).herm
  first
  | exact h x y
  | exact h.eq x y
  | simpa using h x y
  | simpa using h.eq x y

theorem T_ne (D : Formalism.BasicNotions.D7) : (D.sp.T : D.host.E) ≠ 0 := by
  have h := D.sp.T_prime.ne_zero
  exact_mod_cast h

theorem hZE (D : Formalism.BasicNotions.D7) (i : Fin D.R.rS) : (VS D).hT D.sp.zm (D.sp.hypE i) = 0 := by exact (D.sp.hyp_orthz i).1
theorem hZF (D : Formalism.BasicNotions.D7) (i : Fin D.R.rS) : (VS D).hT D.sp.zm (D.sp.hypF i) = 0 := by exact (D.sp.hyp_orthz i).2
theorem hEZ (D : Formalism.BasicNotions.D7) (i : Fin D.R.rS) : (VS D).hT (D.sp.hypE i) D.sp.zm = 0 := by
  rw [← hT_star D D.sp.zm (D.sp.hypE i), hZE, star_zero]
theorem hFZ (D : Formalism.BasicNotions.D7) (i : Fin D.R.rS) : (VS D).hT (D.sp.hypF i) D.sp.zm = 0 := by
  rw [← hT_star D D.sp.zm (D.sp.hypF i), hZF, star_zero]

def pWL (D : Formalism.BasicNotions.D7) : (VS D).V →ₗ[D.host.E] (VS D).V :=
  LinearMap.id - ∑ a, ((VS D).hT (D.sp.hypF a)).smulRight (D.sp.hypE a)
    - ∑ a, ((VS D).hT (D.sp.hypE a)).smulRight (D.sp.hypF a)
    + ((D.sp.T : D.host.E)⁻¹) • ((VS D).hT D.sp.zm).smulRight D.sp.zm

theorem pW_eq (D : Formalism.BasicNotions.D7) (v : (VS D).V) : pW D v = pWL D v := by
  simp only [pW, pWL, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.smul_apply, smul_smul, div_eq_inv_mul]

theorem pW_sub (D : Formalism.BasicNotions.D7) (u v : (VS D).V) : pW D (u - v) = pW D u - pW D v := by simp only [pW_eq, map_sub]

private theorem hT_hypF_hypE (D : Formalism.BasicNotions.D7) (a i : Fin D.R.rS) :
    (VS D).hT (D.sp.hypF a) (D.sp.hypE i) = if a = i then 1 else 0 := by
  rw [← hT_star D (D.sp.hypE i) (D.sp.hypF a), D.sp.hyp_ef i a]
  by_cases h : a = i
  · subst h
    simp
  · simp [h, Ne.symm h]

theorem inW_pW (D : Formalism.BasicNotions.D7) (v : (VS D).V) : InW D (pW D v) := by
  have hT0 := T_ne D
  unfold InW
  refine ⟨fun b => ?_, fun b => ?_, ?_⟩

  · simp [pW, map_sum, D.sp.hyp_ee, D.sp.hyp_ef, hEZ, mul_ite, Finset.sum_ite_eq]

  · simp [pW, map_sum, hT_hypF_hypE, D.sp.hyp_ff, hFZ, mul_ite, Finset.sum_ite_eq']

  · simp [pW, map_sum, hZE, hZF, D.sp.zm_norm, div_mul_cancel₀, hT0]

def eichL (D : Formalism.BasicNotions.D7) (e y : (VS D).V) (c : D.host.E) : (VS D).V →ₗ[D.host.E] (VS D).V :=
  LinearMap.id + ((VS D).hT e).smulRight y - ((VS D).hT y).smulRight e + c • ((VS D).hT e).smulRight e

theorem eichL_apply (D : Formalism.BasicNotions.D7) (e y : (VS D).V) (c : D.host.E) (v : (VS D).V) :
    eichL D e y c v = v + (VS D).hT e v • y - (VS D).hT y v • e + (c * (VS D).hT e v) • e := by
  simp only [eichL, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.smulRight_apply, LinearMap.smul_apply, smul_smul]

theorem eich_inv (D : Formalism.BasicNotions.D7) {e y : (VS D).V} {c : D.host.E} (he : (VS D).hT e e = 0)
    (hey : (VS D).hT e y = 0) (hye : (VS D).hT y e = 0) (hc : c + c + (VS D).hT y y = 0) (v : (VS D).V) :
    eichL D e (-y) c (eichL D e y c v) = v := by
  have h1 : (VS D).hT e (eichL D e y c v) = (VS D).hT e v := by
    simp [eichL_apply, he, hey]
  have h2 : (VS D).hT y (eichL D e y c v) = (VS D).hT y v + (VS D).hT e v * (VS D).hT y y := by
    simp [eichL_apply, hye] <;> ring
  have hc' : (VS D).hT e v * (c + c + (VS D).hT y y) = 0 := by rw [hc, mul_zero]
  rw [eichL_apply D e (-y) c (eichL D e y c v), h1]
  simp only [map_neg, LinearMap.neg_apply, h2]
  rw [eichL_apply D e y c v]
  linear_combination (norm := module) hc' • e

theorem eich_isom (D : Formalism.BasicNotions.D7) {e y : (VS D).V} {c : D.host.E} (he : (VS D).hT e e = 0)
    (hey : (VS D).hT e y = 0) (hye : (VS D).hT y e = 0) (hc : c + star c + (VS D).hT y y = 0)
    (u v : (VS D).V) : (VS D).hT (eichL D e y c u) (eichL D e y c v) = (VS D).hT u v := by
  have hE : ∀ w, (VS D).hT e (eichL D e y c w) = (VS D).hT e w := fun w => by
    simp [eichL_apply, he, hey]
  have hY : ∀ w, (VS D).hT y (eichL D e y c w) = (VS D).hT y w + (VS D).hT e w * (VS D).hT y y := fun w => by
    simp [eichL_apply, hye] <;> ring
  have hU : ∀ w, (VS D).hT u (eichL D e y c w) = (VS D).hT u w + (VS D).hT e w * star ((VS D).hT y u)
      - (VS D).hT y w * star ((VS D).hT e u) + c * (VS D).hT e w * star ((VS D).hT e u) := fun w => by
    rw [hT_star D y u, hT_star D e u]
    simp [eichL_apply] <;> ring
  rw [eichL_apply D e y c u]
  simp only [map_add (f := _), map_sub, map_smulₛₗ, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, hE, hY, hU, starRingEnd_apply, star_mul']
  linear_combination (star ((VS D).hT e u) * (VS D).hT e v) * hc

end PI.UnitaryGroupMassFormula.CntFormula
end
end

section

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def skL (D : Formalism.BasicNotions.D7) (S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) :
    (VS D).V →ₗ[D.host.E] (VS D).V :=
  LinearMap.id + ∑ a, ∑ a', S a a' • ((VS D).hT (D.sp.hypE a')).smulRight (D.sp.hypE a)

theorem skL_apply (D : Formalism.BasicNotions.D7) (S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (v : (VS D).V) :
    skL D S v = v + ∑ a, (∑ a', S a a' * (VS D).hT (D.sp.hypE a') v) • D.sp.hypE a := by
  simp only [skL, LinearMap.add_apply, LinearMap.id_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.smulRight_apply, smul_smul, Finset.sum_smul]

theorem hE_skL (D : Formalism.BasicNotions.D7) (S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (b : Fin D.R.rS)
    (v : (VS D).V) : (VS D).hT (D.sp.hypE b) (skL D S v) = (VS D).hT (D.sp.hypE b) v := by

  rw [skL_apply, map_add (f := _), map_sum]
  simp [D.sp.hyp_ee]

theorem skL_inv (D : Formalism.BasicNotions.D7) (S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (v : (VS D).V) :
    skL D (-S) (skL D S v) = v := by
  rw [skL_apply D (-S) (skL D S v)]
  simp only [hE_skL]
  rw [skL_apply]
  have e : ∀ a, (∑ a', (-S) a a' * (VS D).hT (D.sp.hypE a') v) =
      -(∑ a', S a a' * (VS D).hT (D.sp.hypE a') v) := fun a => by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [Matrix.neg_apply, neg_mul]
  simp_rw [e, neg_smul, Finset.sum_neg_distrib]
  exact add_neg_cancel_right _ _

def skE (D : Formalism.BasicNotions.D7) (S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) : (VS D).V ≃ₗ[D.host.E] (VS D).V :=
  LinearEquiv.ofLinear (skL D S) (skL D (-S))
    (LinearMap.ext fun v => by
      have h := skL_inv D (-S) v
      rw [neg_neg] at h
      exact h)
    (LinearMap.ext fun v => skL_inv D S v)

theorem skE_apply (D : Formalism.BasicNotions.D7) (S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (v : (VS D).V) :
    skE D S v = skL D S v := rfl

theorem dsum_cancel {K : Type} [CommRing K] {r : ℕ} (S : Matrix (Fin r) (Fin r) K) (X Y : Fin r → K) :
    ∑ a, (∑ a', S a a' * X a') * Y a + ∑ a, (∑ a', -S a' a * Y a') * X a = 0 := by
  have e : ∑ a, (∑ a', -S a' a * Y a') * X a = -∑ a, (∑ a', S a a' * X a') * Y a := by
    simp only [Finset.sum_mul, ← Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
    ring
  rw [e, add_neg_cancel]

theorem skL_isom (D : Formalism.BasicNotions.D7) (S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)
    (hS : ∀ i j, star (S j i) = -S i j) (u v : (VS D).V) :
    (VS D).hT (skL D S u) (skL D S v) = (VS D).hT u v := by
  have hue : ∀ b, (VS D).hT u (D.sp.hypE b) = star ((VS D).hT (D.sp.hypE b) u) := fun b =>
    ((VS D).herm.eq (D.sp.hypE b) u).symm
  have key := dsum_cancel S (fun b => (VS D).hT (D.sp.hypE b) v) (fun b => star ((VS D).hT (D.sp.hypE b) u))
  beta_reduce at key
  rw [skL_apply, skL_apply]

  simp only [map_add (f := _), map_sum, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.map_smulₛₗ₂, map_smul,
  D.sp.hyp_ee, hue, smul_eq_mul, mul_zero, Finset.sum_const_zero, add_zero, starRingEnd_apply, star_sum,
  star_mul', hS]
  linear_combination key

theorem hE_int (D : Formalism.BasicNotions.D7) {T : D.host.E} {F0 : FlagG (VS D) D.R.rS T}
    {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hF : FixedOK D F0 Λ) (a : Fin D.R.rS) {v : (VS D).V}
    (hv : v ∈ Λ) : ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = (VS D).hT (D.sp.hypE a) v := by
  have he : D.sp.hypE a ∈ Λ := by
    have h1 := hF.2.2.2.1 a
    rwa [hF.2.2.1] at h1
  have hU' : Formalism.HermitianLatticesTheory.dual (VS D).hT Λ = Λ := hF.2.1
  have hv' : v ∈ Formalism.HermitianLatticesTheory.dual (VS D).hT Λ := by rw [hU']; exact hv
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply] at hv'
  obtain ⟨o, ho⟩ := Submodule.mem_one.mp (hv' _ he)
  exact ⟨o, ho⟩

theorem skL_lat (D : Formalism.BasicNotions.D7) {T : D.host.E} {F0 : FlagG (VS D) D.R.rS T}
    {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hF : FixedOK D F0 Λ) (S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)
    (hO : ∀ i j, ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = S i j) {v : (VS D).V} (hv : v ∈ Λ) :
    skL D S v ∈ Λ := by
  rw [skL_apply]
  refine Λ.add_mem hv (Λ.sum_mem fun a _ => ?_)
  have he : D.sp.hypE a ∈ Λ := by
    have h1 := hF.2.2.2.1 a
    rwa [hF.2.2.1] at h1
  have hc : (∑ a', S a a' * (VS D).hT (D.sp.hypE a') v) ∈ (algebraMap (𝓞 D.host.E) D.host.E).range :=
    sum_mem fun a' _ => mul_mem (hO a a') (hE_int D hF a' hv)
  obtain ⟨o, ho⟩ := hc
  rw [← ho, algebraMap_smul]
  exact Λ.smul_mem o he

theorem skL_X (D : Formalism.BasicNotions.D7) (S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) {x : (VS D).V}
    (hx : x ∈ Submodule.span D.host.E (Set.range D.sp.hypE)) : skL D S x = x := by
  have h0 : ∀ a', (VS D).hT (D.sp.hypE a') x = 0 := by
    intro a'
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, rfl⟩ := hy
      exact D.sp.hyp_ee a' b
    | zero => simp
    | add y z _ _ hy hz => rw [map_add (f := _), hy, hz, add_zero]
    | smul c y _ hy => rw [map_smul, hy, smul_zero]
  rw [skL_apply]
  simp [h0]

theorem skL_sub_mem (D : Formalism.BasicNotions.D7) (S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (x : (VS D).V) :
    skL D S x - x ∈ Submodule.span D.host.E (Set.range D.sp.hypE) := by
  rw [skL_apply, add_sub_cancel_left]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem skE_mem (D : Formalism.BasicNotions.D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hF : FixedOK D F0 Λ) (S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)
    (hS : ∀ i j, star (S j i) = -S i j)
    (hO : ∀ i j, ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = S i j) :
    skE D S ∈ N0 F0 Λ := by
  have hFe : F0.e = D.sp.hypE := hF.2.2.1
  have hspan : ∀ x ∈ Submodule.span D.host.E (Set.range F0.e), skE D S x = x := by
    intro x hx
    rw [hFe] at hx
    exact skL_X D S hx
  have hO' : ∀ i j, ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = (-S) i j := fun i j => by
    obtain ⟨o, ho⟩ := hO i j
    exact ⟨-o, by rw [map_neg, ho, Matrix.neg_apply]⟩
  have hzm : ∀ a', (VS D).hT (D.sp.hypE a') D.sp.zm = 0 := fun a' => by
    rw [← (VS D).herm.eq D.sp.zm (D.sp.hypE a'), (D.sp.hyp_orthz a').1, map_zero]
  simp only [N0, NLam, IsAutLam, Set.mem_setOf_eq]
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
  · intro x y
    exact skL_isom D S hS x y
  · apply le_antisymm
    · exact Submodule.map_le_iff_le_comap.mpr fun v hv => skL_lat D hF S hO hv
    · intro v hv
      refine Submodule.mem_map.mpr ⟨skL D (-S) v, skL_lat D hF (-S) hO' hv, ?_⟩
      have h1 := skL_inv D (-S) v
      rw [neg_neg] at h1
      exact h1
  · intro j x hx
    have hx' : x ∈ Submodule.span D.host.E (Set.range F0.e) :=
      Submodule.span_mono (Set.image_subset_range _ _) hx
    rw [hspan x hx', sub_self]
    exact Submodule.zero_mem _
  · intro x _
    have h1 := skL_sub_mem D S x
    rw [← hFe] at h1
    exact h1
  · intro a
    exact hspan _ (Submodule.subset_span ⟨a, rfl⟩)
  · obtain ⟨c, _, hcz⟩ := hF.2.2.2.2
    rw [hcz, map_smul]
    congr 1
    rw [skE_apply, skL_apply]
    simp [hzm]

private theorem pW_skL (D : Formalism.BasicNotions.D7) (S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)
    (w : (VS D).V) : pW D (skL D S w) = pW D w := by
  have hf : ∀ a b, (VS D).hT (D.sp.hypF b) (D.sp.hypE a) = if a = b then 1 else 0 := fun a b => by
    rw [← (VS D).herm.eq (D.sp.hypE a) (D.sp.hypF b), D.sp.hyp_ef]
    split_ifs <;> simp
  have hz : ∀ a, (VS D).hT D.sp.zm (D.sp.hypE a) = 0 := fun a => (D.sp.hyp_orthz a).1
  rw [skL_apply]

  simp only [pW, map_add (f := _), map_sum, map_smul, hf, hz, D.sp.hyp_ee, smul_eq_mul, mul_zero, add_zero,
  mul_ite, mul_one, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true, add_smul,
  Finset.sum_add_distrib, Finset.sum_const_zero, zero_smul]
  module

theorem pWf_skE (D : Formalism.BasicNotions.D7) (S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)
    (x : (Fin D.R.rS → (VS D).V) × (VS D).V) : pWf D (act D (skE D S) x) = pWf D x := by
  funext b
  have hfr : fr D (act D (skE D S) x) b = skL D S (fr D x b) := by
    simp only [fr, act]
    exact (congrFun (Fin.comp_snoc (fun w => (skE D S) w) x.1 x.2) b).symm
  simp only [pWf]
  rw [hfr, pW_skL]

theorem alM_skE (D : Formalism.BasicNotions.D7) {T : D.host.E} (T' : D.host.E) (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hF : FixedOK D F0 Λ) (Z : MatZ D)
    (S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) {x : (Fin D.R.rS → (VS D).V) × (VS D).V}
    (hx : Good D T' F0 Λ Z x) : alM D (act D (skE D S) x) = alM D x + S * betaZ D Z := by
  ext a b
  have hf : ∀ c, (VS D).hT (D.sp.hypF a) (D.sp.hypE c) = if c = a then 1 else 0 := fun c => by
    rw [← (VS D).herm.eq (D.sp.hypE c) (D.sp.hypF a), D.sp.hyp_ef]
    split_ifs <;> simp
  have hZ : ∀ c', (VS D).hT (D.sp.hypE c') (fr D x b) = Z (Fin.castSucc c') b := fun c' => by
    have h1 := hx.2.1 (Fin.castSucc c') b
    simp only [Formalism.MainNotions.S.brS, Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc, hF.2.2.1] at h1
    exact h1
  have hfr : fr D (act D (skE D S) x) b = skL D S (fr D x b) := by
    simp only [fr, act]
    exact (congrFun (Fin.comp_snoc (fun w => (skE D S) w) x.1 x.2) b).symm
  simp only [alM, Matrix.add_apply, Matrix.mul_apply, betaZ, Matrix.submatrix_apply, id]

  rw [hfr, skL_apply, map_add (f := _), map_sum]
  simp only [map_smul, smul_eq_mul, hf, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, hZ]

end PI.UnitaryGroupMassFormula.CntFormula
end
end

section

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField IsDedekindDomain ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups

theorem resCard_loc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : Loc.LocAt F E sig p) :
    Nat.card 𝓀[A.Fp] = p.asIdeal.absNorm := by
  have := A.lf
  have key : ∀ x y : F, valuation A.Fp (A.ιF x) ≤ valuation A.Fp (A.ιF y) ↔
      p.valuation F x ≤ p.valuation F y := fun x y => by
    rw [← Valuation.vle_iff_le]; exact A.val x y
  have keyle1 : ∀ x : F, valuation A.Fp (A.ιF x) ≤ 1 ↔ p.valuation F x ≤ 1 := fun x => by
    have h := key x 1
    rwa [map_one, map_one, map_one] at h
  have keylt1 : ∀ x : F, valuation A.Fp (A.ιF x) < 1 ↔ p.valuation F x < 1 := fun x => by
    have h := key 1 x
    rw [map_one, map_one, map_one] at h
    rw [← not_le, ← not_le, h]
  let f : 𝓞 F →+* 𝒪[A.Fp] :=
    { toFun := fun x => ⟨A.ιF (algebraMap (𝓞 F) F x),
        (keyle1 _).2 (p.valuation_le_one (K := F) x)⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro a b; ext; simp }
  let φ : 𝓞 F →+* 𝓀[A.Fp] := (IsLocalRing.residue 𝒪[A.Fp]).comp f
  have hmax : ∀ w : 𝒪[A.Fp], w ∈ IsLocalRing.maximalIdeal 𝒪[A.Fp] ↔ valuation A.Fp (w : A.Fp) < 1 :=
    fun w => by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact Valuation.Integer.not_isUnit_iff_valuation_lt_one
  have hker : RingHom.ker φ = p.asIdeal := by
    ext x
    rw [RingHom.mem_ker, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, hmax]
    exact (keylt1 _).trans (p.valuation_lt_one_iff_mem (K := F) x)
  have hsurj : Function.Surjective φ := by
    intro z0
    obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective z0
    have hS : {w : A.Fp | valuation A.Fp (w - z) < 1} ∈ nhds (z : A.Fp) :=
      (IsValuativeTopology.hasBasis_nhds' (z : A.Fp)).mem_of_mem one_ne_zero
    obtain ⟨w, ⟨x', rfl⟩, hw⟩ := A.dense.inter_nhds_nonempty hS
    have hw' : valuation A.Fp (A.ιF x' - z) < 1 := hw
    have hx' : p.valuation F x' ≤ 1 := by
      rw [← keyle1]
      have hz : valuation A.Fp (z : A.Fp) ≤ 1 := z.2
      have := Valuation.map_add_le (valuation A.Fp) hw'.le hz
      simpa using this
    obtain ⟨a, ha⟩ := IsDedekindDomain.HeightOneSpectrum.exists_valuation_sub_lt_of_integer
      (v := p) (K := F) hx' 1
    have ha' : p.valuation F (algebraMap (𝓞 F) F a - x') < 1 := by simpa using ha
    refine ⟨a, ?_⟩
    rw [RingHom.comp_apply, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, hmax]
    have h1 : valuation A.Fp (A.ιF (algebraMap (𝓞 F) F a - x')) < 1 := (keylt1 _).2 ha'
    have h2 := Valuation.map_add_lt (valuation A.Fp) h1 hw'
    have he : ((f a - z : 𝒪[A.Fp]) : A.Fp) =
        A.ιF (algebraMap (𝓞 F) F a - x') + (A.ιF x' - z) := by
      simp only [map_sub]
      show A.ιF (algebraMap (𝓞 F) F a) - (z : A.Fp) = _
      ring
    rw [he]
    exact h2
  rw [← hker, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (RingHom.quotientKerEquivOfSurjective hsurj).toEquiv).symm

theorem residue_field_card : ResCard := fun D p => resCard_loc _

end PI.UnitaryGroupMassFormula.CntFormula
end
end

section

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem orbitFinite_of (hA : UnipotentIntegralIsGroup) (hB : OrbitReps) : OrbitFinite := by
  intro D δ M hAg L u u' hc F0 what₂ hr Z Λ hΛ
  obtain ⟨K, hKf, hK⟩ := hB D δ M hAg L u u' hc F0 what₂ hr Z Λ hΛ
  obtain ⟨-, hsymm, htrans⟩ := hA D F0 Λ
  unfold cntE
  rw [Set.encard_ne_top_iff]
  refine (hKf.image (fun k : (Fin D.R.rS → (VS D).V) × (VS D).V =>
      {F'' : LFlag (VS D) D.R.rS (Tn u') | F'' ∈ EZ (Tn u') F0 Λ Z ∧
        ∃ n ∈ N0 F0 Λ, (∀ a, n (k.1 a) = F''.fl.e a) ∧ n k.2 = F''.fl.z})).subset ?_
  rintro O ⟨F', hF', rfl⟩
  obtain ⟨n₀, hn₀, hk⟩ := hK F' hF'
  refine ⟨_, hk, ?_⟩
  ext F''
  simp only [Set.mem_setOf_eq, NilradicalFlagMoved]
  constructor
  · rintro ⟨hE, m, hm, he, hz⟩
    refine ⟨hE, n₀.trans m, htrans _ hn₀ _ hm, fun a => ?_, ?_⟩
    · simpa using he a
    · simpa using hz
  · rintro ⟨hE, n, hn, he, hz⟩
    refine ⟨hE, n₀.symm.trans n, htrans _ (hsymm _ hn₀) _ hn, fun a => ?_, ?_⟩
    · simpa using he a
    · simpa using hz

end PI.UnitaryGroupMassFormula.CntFormula
end
end
