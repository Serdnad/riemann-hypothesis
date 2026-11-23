module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.IntegralityGoodReduction
import Aesop.Main
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.Deriv.Pow
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Calculus.Deriv.Inv

@[expose] public section

section

open Set MeasureTheory Metric Filter Topology
open scoped ContDiff

namespace UpperTheory.V.Lit.Dr

theorem paramSmooth : ParamSmooth := by
  intro P F _ _ _ _ _ _ O S g hO hS hOS hg p₀ hp₀
  apply ContDiffAt.contDiffWithinAt
  obtain ⟨u, v, hu, hv, hpu, hIv, huv⟩ := generalized_tube_lemma (isCompact_singleton (x := p₀))
    (isCompact_Icc (a := (0 : ℝ)) (b := 1)) hS ((prod_mono (singleton_subset_iff.2 hp₀) subset_rfl).trans hOS)
  have hI : Icc (0 : ℝ) 1 = closedBall (1 / 2) (1 / 2) := by
    rw [Real.closedBall_eq_Icc]; norm_num
  obtain ⟨ε, hε, hεv⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_cthickening_subset_open hv hIv
  rw [hI, cthickening_closedBall hε.le (by norm_num)] at hεv
  let b : ContDiffBump (1 / 2 : ℝ) := ⟨1 / 2, ε + 1 / 2, by norm_num, by linarith⟩
  have hbs : tsupport b = closedBall (1 / 2 : ℝ) (ε + 1 / 2) := b.tsupport_eq
  have hb0 : ∀ s, s ∉ closedBall (1 / 2 : ℝ) (ε + 1 / 2) → b s = 0 := fun s hs =>
    image_eq_zero_of_notMem_tsupport (by rwa [hbs])
  have hb1 : ∀ s ∈ Icc (0 : ℝ) 1, b s = 1 := fun s hs => b.one_of_mem_closedBall (by rwa [hI] at hs)
  let K : P × ℝ → F := fun q => b q.2 • g q
  have hK : ContDiffOn ℝ ∞ K (u ×ˢ univ) := by
    intro q hq
    apply ContDiffAt.contDiffWithinAt
    by_cases hqv : q.2 ∈ v
    · have h1 : ContDiffAt ℝ ∞ g q := hg.contDiffAt (hS.mem_nhds (huv ⟨hq.1, hqv⟩))
      have h2 : ContDiff ℝ ∞ (fun q : P × ℝ => b q.2) := b.contDiff.comp contDiff_snd
      exact h2.contDiffAt.smul h1
    · have hq2 : q.2 ∉ closedBall (1 / 2 : ℝ) (ε + 1 / 2) := fun h => hqv (hεv h)
      refine (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq ?_
      filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
        (isClosed_closedBall.isOpen_compl.mem_nhds hq2)] with q' hq'
      simp only [K, hb0 q'.2 hq', zero_smul]
  have hf : LocallyIntegrable ((Ioc (0 : ℝ) 1).indicator fun _ => (1 : ℝ)) volume :=
    ((integrable_indicator_iff measurableSet_Ioc).2 (integrableOn_const (by simp))).locallyIntegrable
  let k : Set ℝ := Neg.neg '' closedBall (1 / 2 : ℝ) (ε + 1 / 2)
  have hgs : ∀ p, ∀ x, p ∈ u → x ∉ k →
      (fun z (y : ℝ) => K (z, -y)) p x = 0 := by
    intro p x _ hx
    have := hb0 (-x) (fun h => hx ⟨-x, h, by simp⟩)
    simp only [K, this, zero_smul]
  have hg' : ContDiffOn ℝ (⊤ : ℕ∞) (↿(fun z (y : ℝ) => K (z, -y))) (u ×ˢ Set.univ) := by
    have h1 : ContDiff ℝ ∞ (fun p : P × ℝ => (p.1, -p.2)) :=
      contDiff_fst.prodMk contDiff_snd.neg
    refine hK.comp h1.contDiffOn ?_
    rintro ⟨p, x⟩ ⟨hp, -⟩
    exact ⟨hp, Set.mem_univ _⟩
  have hv0 : ContDiffOn ℝ (⊤ : ℕ∞) (fun _ : P => (0 : ℝ)) u := contDiffOn_const
  have main := contDiffOn_convolution_right_with_param_comp (μ := volume)
    (ContinuousLinearMap.lsmul ℝ ℝ) hv0 hu
    ((isCompact_closedBall _ _).image continuous_neg) hgs hf hg'
  have fin : ContDiffOn ℝ ∞ (fun p => ∫ s in (0 : ℝ)..1, g (p, s)) u := by
    refine main.congr ?_
    intro z _
    simp only [convolution_def, ContinuousLinearMap.lsmul_apply, zero_sub, neg_neg]
    rw [intervalIntegral.integral_of_le zero_le_one, ← integral_indicator measurableSet_Ioc]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    by_cases hw : w ∈ Ioc (0 : ℝ) 1
    · simp [Set.indicator_of_mem hw, K, hb1 w (Ioc_subset_Icc_self hw)]
    · simp [Set.indicator_of_notMem hw]
  exact fin.contDiffAt (hu.mem_nhds (hpu rfl))

end UpperTheory.V.Lit.Dr
end

section

noncomputable section

open ContinuousAlternatingMap

namespace UpperTheory.V.Lit.Dr

variable {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F] {q : ℕ}

theorem poinPt : PoinPt := by
  intro V F _ _ _ _ q w p₀ p t hw hd
  set d : V := p - p₀ with hdd
  set c : V := p₀ + t • d with hc
  set A := fderiv ℝ w c with hAdef
  have hA : HasFDerivAt w A c := hw.hasFDerivAt
  have hin : HasFDerivAt (fun x : V => p₀ + t • (x - p₀)) (t • ContinuousLinearMap.id ℝ V) p := by
    simpa using (((hasFDerivAt_id p).sub_const p₀).const_smul t).const_add p₀
  have hwin : HasFDerivAt (fun x : V => w (p₀ + t • (x - p₀)))
      (A.comp (t • ContinuousLinearMap.id ℝ V)) p :=
    hA.comp p hin
  set L := (curryLeftLI (𝕜 := ℝ) (E := V) (F := F) (n := q)).toContinuousLinearMap with hL
  have hg : HasFDerivAt (fun x : V => L (w (p₀ + t • (x - p₀))))
      (L.comp (A.comp (t • ContinuousLinearMap.id ℝ V))) p :=
    L.hasFDerivAt.comp p hwin
  have hφ : HasFDerivAt (fun x => t ^ q • (L (w (p₀ + t • (x - p₀)))) (x - p₀))
      (t ^ q • ((L (w c)).comp (ContinuousLinearMap.id ℝ V) +
        (L.comp (A.comp (t • ContinuousLinearMap.id ℝ V))).flip d)) p := by
    exact (hg.clm_apply ((hasFDerivAt_id p).sub_const p₀)).const_smul (t ^ q)
  have hfun : (fun x ↦ t ^ q • (w (p₀ + t • (x - p₀))).curryLeft (x - p₀)) =
      fun x => t ^ q • (L (w (p₀ + t • (x - p₀)))) (x - p₀) := by
    funext x
    simp [hL]
  have lhs : HasDerivAt (fun r ↦ r ^ (q + 1) • w (p₀ + r • d))
      ((((q + 1 : ℕ) : ℝ) * t ^ q) • w c + t ^ (q + 1) • A d) t := by
    have h1 : HasDerivAt (fun r : ℝ => p₀ + r • d) d t := by
      simpa using ((hasDerivAt_id t).smul_const d).const_add p₀
    have h2 : HasDerivAt (fun r => w (p₀ + r • d)) (A d) t := hA.comp_hasDerivAt t h1
    have h3 := (hasDerivAt_pow (q + 1) t).smul h2
    refine h3.congr_deriv ?_
    rw [show q + 1 - 1 = q from rfl]
    exact add_comm _ _
  have hK : ∀ v : Fin (q + 1) → V,
      ∑ i : Fin (q + 1), (-1 : ℤ) ^ (i : ℕ) • (A (v i)) (Matrix.vecCons d (i.removeNth v)) =
        A d v := by
    intro v
    have hrm : ∀ i : Fin (q + 1),
        Fin.removeNth i.succ (Matrix.vecCons d v) = Matrix.vecCons d (Fin.removeNth i v) := by
      intro i
      funext j
      cases j using Fin.cases <;> simp [Fin.removeNth_apply, Fin.succ_succAbove_zero, Fin.succ_succAbove_succ]
    have h0 := congrArg (fun f => f (Matrix.vecCons d v)) hd
    simp only [extDeriv, ← hAdef, alternatizeUncurryFin_apply] at h0
    rw [Fin.sum_univ_succ] at h0
    simp only [hrm, Fin.removeNth_zero, Matrix.tail_cons, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.val_zero, pow_zero, one_smul, Fin.val_succ, pow_succ, mul_neg_one, neg_smul,
      Finset.sum_neg_distrib] at h0
    have ht : Fin.tail (Matrix.vecCons d v) = v := by
      funext i
      simp [Fin.tail]
    rw [ht] at h0
    have h0' : (A d) v - ∑ i : Fin (q + 1), (-1 : ℤ) ^ (i : ℕ) •
        (A (v i)) (Matrix.vecCons d (i.removeNth v)) = 0 := by
      simpa [sub_eq_add_neg] using h0
    exact (sub_eq_zero.mp h0').symm
  convert lhs using 1
  rw [hfun, extDeriv, hφ.fderiv]
  ext v
  simp [alternatizeUncurryFin_apply, hL]
  rw [hK v]
  module

end UpperTheory.V.Lit.Dr
end
end

section

noncomputable section

open scoped ContDiff Topology

namespace UpperTheory.V.Lit.Dr

section

variable {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]

end

private theorem hasDerivAt_apply_comp_of_differentiableAt {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {q : ℕ} {w : V → V [⋀^Fin q]→L[ℝ] F}
    {c : ℝ → V} {c' : V} {s : ℝ} (m : Fin q → V) (hw : DifferentiableAt ℝ w (c s))
    (hc : HasDerivAt c c' s) :
    HasDerivAt (fun r => w (c r) m) (fderiv ℝ w (c s) c' m) s := by
  have h1 := (ContinuousAlternatingMap.apply ℝ V F m).hasFDerivAt.comp (c s) hw.hasFDerivAt
  exact h1.comp_hasDerivAt s hc

private theorem fderiv_update_add_eq_zero_of_radBasic {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {Y : Set V} (hY : IsOpen Y) {q : ℕ}
    {w : V → V [⋀^Fin q]→L[ℝ] F} (hR : RadBasic Y w) {x : V} (hx : x ∈ Y)
    (hw : DifferentiableAt ℝ w x) (v : Fin q → V) (j : Fin q) :
    fderiv ℝ w x (v j) (Function.update v j x) + w x v = 0 := by
  have hc : HasDerivAt (fun s : ℝ => x + s • v j) (v j) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (v j)).const_add x
  have hw0 : DifferentiableAt ℝ w (x + (0 : ℝ) • v j) := by simpa using hw
  have d1 := hasDerivAt_apply_comp_of_differentiableAt (Function.update v j x) hw0 hc
  have d2 := hasDerivAt_apply_comp_of_differentiableAt v hw0 hc
  have d3 := (hasDerivAt_id (0 : ℝ)).smul d2
  have dg := d1.add d3
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), x + s • v j ∈ Y := by
    have hcont : Continuous fun s : ℝ => x + s • v j := by fun_prop
    exact hcont.continuousAt (x := 0) |>.preimage_mem_nhds (by simpa using hY.mem_nhds hx)
  have heq : (fun s : ℝ => w (x + s • v j) (Function.update v j x) + id s • w (x + s • v j) v)
      =ᶠ[𝓝 0] fun _ => (0 : F) := by
    filter_upwards [hev] with s hs
    have h0 := hR (x + s • v j) hs (Function.update v j (x + s • v j)) j (by simp)
    rw [ContinuousAlternatingMap.map_update_add, ContinuousAlternatingMap.map_update_smul,
      Function.update_eq_self] at h0
    simpa using h0
  have := dg.unique ((hasDerivAt_const (0 : ℝ) (0 : F)).congr_of_eventuallyEq heq)
  simpa using this

private theorem fderiv_self_add_smul_eq_zero_of_radBasic_closed {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {Y : Set V} (hY : IsOpen Y) {q : ℕ}
    {w : V → V [⋀^Fin q]→L[ℝ] F} (hR : RadBasic Y w) {x : V} (hx : x ∈ Y)
    (hw : DifferentiableAt ℝ w x) (hd : extDeriv w x = 0) (v : Fin q → V) :
    fderiv ℝ w x x v + (q : ℝ) • w x v = 0 := by
  have h0 := congrArg (fun f => f (Fin.cons x v)) hd
  simp only [extDeriv, ContinuousAlternatingMap.alternatizeUncurryFin_apply, Fin.sum_univ_succ] at h0
  cases q with
  | zero => simpa using h0
  | succ n =>
    have hterm : ∀ j : Fin (n + 1), (-1 : ℤ) ^ ((j.succ : Fin (n + 2)) : ℕ) •
        fderiv ℝ w x ((Fin.cons x v : Fin (n + 2) → V) j.succ)
          (Fin.removeNth j.succ (Fin.cons x v : Fin (n + 2) → V)) = w x v := by
      intro j
      have hr : Fin.removeNth j.succ (Fin.cons x v : Fin (n + 2) → V) =
          Matrix.vecCons x (Fin.removeNth j v) := by
        ext i
        refine Fin.cases ?_ (fun k => ?_) i
        · simp [Fin.removeNth]
        · simp [Fin.removeNth, Fin.succ_succAbove_succ]
      rw [hr, ← ContinuousAlternatingMap.neg_one_pow_smul_map_insertNth, Fin.insertNth_removeNth,
        Fin.cons_succ, smul_smul]
      have := fderiv_update_add_eq_zero_of_radBasic hY hR hx hw v j
      rw [Fin.val_succ, pow_succ, mul_comm, ← mul_assoc, ← pow_add, Even.neg_one_pow ⟨_, rfl⟩,
        one_mul, neg_one_smul, neg_eq_iff_eq_neg, eq_neg_iff_add_eq_zero]
      exact this
    rw [Finset.sum_congr rfl (fun j _ => hterm j)] at h0
    rw [Nat.cast_smul_eq_nsmul]
    simpa [add_comm] using h0

theorem homog : Homog := by
  intro V F _ _ _ _ Y hY hC q w hw hR hd t ht p hp v
  have hdiff : ∀ x ∈ Y, DifferentiableAt ℝ w x := fun x hx =>
    (hw.contDiffAt (hY.mem_nhds hx)).differentiableAt (by simp)
  set k : ℝ → F := fun s => s ^ q • w (s • p) v with hkdef
  have hscale : ∀ s : ℝ, w (s • p) (fun i => s • v i) = k s := by
    intro s
    rw [ContinuousAlternatingMap.map_smul_univ]
    simp [k, Finset.prod_const]
  have hk : ∀ s ∈ Set.Ioi (0 : ℝ), HasDerivAt k 0 s := by
    intro s hs
    have hs0 : s ≠ 0 := ne_of_gt hs
    have hsp : s • p ∈ Y := hC s hs p hp
    have hc : HasDerivAt (fun r : ℝ => r • p) p s := by
      simpa using (hasDerivAt_id s).smul_const p
    have dg := hasDerivAt_apply_comp_of_differentiableAt v (c := fun r : ℝ => r • p) (hdiff _ hsp) hc
    have dk : HasDerivAt k _ s := (hasDerivAt_pow q s).smul dg
    have key := fderiv_self_add_smul_eq_zero_of_radBasic_closed hY hR hsp (hdiff _ hsp) (hd _ hsp) v
    have hA : s • fderiv ℝ w (s • p) p v = -((q : ℝ) • w (s • p) v) := by
      rw [eq_neg_iff_add_eq_zero, ← key]
      simp [map_smul]
    have hpow : s * ((q : ℝ) * s ^ (q - 1)) = q * s ^ q := by
      cases q with
      | zero => simp
      | succ n => simp [pow_succ]; ring
    convert dk using 1
    apply smul_right_injective F hs0
    simp only [smul_zero, smul_add]
    rw [smul_comm s (s ^ q), hA, smul_smul, hpow, smul_neg, smul_smul, mul_comm, neg_add_cancel]
  have hconst := isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
    (fun s hs => (hk s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => (hk s hs).deriv) (Set.mem_Ioi.mpr ht) (Set.mem_Ioi.mpr one_pos)
  rw [hscale, hconst]
  simp [k]

end UpperTheory.V.Lit.Dr
end
end

section

noncomputable section

open scoped ContDiff

namespace UpperTheory.V.Lit.Dr

theorem altSmooth : AltSmooth := by
  intro X _ _ V F _ _ _ _ _ _ q f x hf
  let b := Module.finBasis ℝ V
  let E : (V [⋀^Fin q]→L[ℝ] F) →ₗ[ℝ] ((Fin q → Fin (Module.finrank ℝ V)) → F) :=
    { toFun := fun a k => a fun i => b (k i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hE : Function.Injective E := by
    intro a a' h
    apply ContinuousAlternatingMap.toAlternatingMap_injective
    refine Module.Basis.ext_alternating b fun k _ => ?_
    exact congrFun h k
  obtain ⟨g, hg⟩ := E.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hE)
  have h1 : ContDiffAt ℝ ∞ (fun y => E (f y)) x := contDiffAt_pi.2 fun k => hf _
  have h2 := (LinearMap.toContinuousLinearMap g).contDiff.contDiffAt.comp x h1
  have h3 : (LinearMap.toContinuousLinearMap g) ∘ (fun y => E (f y)) = f := by
    funext y
    exact LinearMap.congr_fun hg (f y)
  rwa [h3] at h2

end UpperTheory.V.Lit.Dr
end
end

section

noncomputable section

open scoped ContDiff Topology

namespace UpperTheory.V.Lit.Dr

section

variable {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]

end

private theorem multilinear_apply_add_smul_of_vanishing {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {q : ℕ} (A : V [⋀^Fin q]→L[ℝ] F) (z : V)
    (hA : ∀ (u : Fin q → V) (i : Fin q), u i = z → A u = 0) (u : Fin q → V) (a : Fin q → ℝ) :
    A (fun i => u i + a i • z) = A u := by
  classical
  suffices key : ∀ s : Finset (Fin q),
      A (fun i => if i ∈ s then u i + a i • z else u i) = A u by
    simpa using key Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    have e1 : (fun i => if i ∈ insert j s then u i + a i • z else u i) =
        Function.update (fun i => if i ∈ s then u i + a i • z else u i) j (u j + a j • z) := by
      ext i
      by_cases h : i = j
      · subst h
        simp
      · simp [h]
    have e2 : Function.update (fun i => if i ∈ s then u i + a i • z else u i) j (u j) =
        fun i => if i ∈ s then u i + a i • z else u i := by
      ext i
      by_cases h : i = j
      · subst h
        simp [hj]
      · simp [h]
    rw [e1, ContinuousAlternatingMap.map_update_add, ContinuousAlternatingMap.map_update_smul,
      hA (Function.update (fun i => if i ∈ s then u i + a i • z else u i) j z) j (by simp),
      smul_zero, add_zero, e2, ih]

theorem pullA : PullTranslates := by
  intro V F _ _ _ _ Y hY hC l hl q w
  obtain ⟨hlc, hlpos, hlh⟩ := hl
  have hld : ∀ p ∈ Y, DifferentiableAt ℝ l p := fun p hp =>
    (hlc.contDiffAt (hY.mem_nhds hp)).differentiableAt (by simp)
  have hDr : ∀ p ∈ Y, ∀ h, fderiv ℝ (fun x => l x • x) p h = fderiv ℝ l p h • p + l p • h := by
    intro p hp h
    have hd : HasFDerivAt (fun x => l x • x) _ p := (hld p hp).hasFDerivAt.smul (hasFDerivAt_id p)
    rw [hd.fderiv]
    simp [add_comm]
  have heul : ∀ p ∈ Y, fderiv ℝ l p p = -l p := by
    intro p hp
    have hc : HasDerivAt (fun t : ℝ => t • p) p 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).smul_const p
    have h' : HasFDerivAt l (fderiv ℝ l p) ((1 : ℝ) • p) := by
      simpa using (hld p hp).hasFDerivAt
    have h1 : HasDerivAt (fun t : ℝ => l (t • p)) (fderiv ℝ l p p) 1 := h'.comp_hasDerivAt 1 hc
    have h2 : HasDerivAt (fun t : ℝ => t⁻¹ * l p) (-l p) 1 := by
      simpa using (hasDerivAt_inv (one_ne_zero (α := ℝ))).mul_const (l p)
    have heq : (fun t : ℝ => l (t • p)) =ᶠ[𝓝 1] fun t => t⁻¹ * l p := by
      filter_upwards [lt_mem_nhds one_pos] with t ht using hlh t ht p hp
    exact h1.unique (h2.congr_of_eventuallyEq heq)
  have hDrp : ∀ p ∈ Y, fderiv ℝ (fun x => l x • x) p p = 0 := by
    intro p hp
    rw [hDr p hp, heul p hp, neg_smul, neg_add_cancel]
  refine ⟨?_, ?_⟩
  · intro p hp v i hvi
    simp only [pull, ContinuousAlternatingMap.compContinuousLinearMap_apply]
    apply ContinuousAlternatingMap.map_coord_zero _ i
    simp [hvi, hDrp p hp]
  · intro hR hH p hp
    ext v
    simp only [pull, ContinuousAlternatingMap.compContinuousLinearMap_apply]
    have hc := hlpos p hp
    have hcp : l p • p ∈ Y := hC _ hc p hp
    have e1 : (fun i => fderiv ℝ (fun x => l x • x) p (v i)) =
        fun i => l p • v i + (fderiv ℝ l p (v i) / l p) • (l p • p) := by
      ext i
      rw [hDr p hp, smul_smul, div_mul_cancel₀ _ hc.ne', add_comm]
    change w (l p • p) (fun i => fderiv ℝ (fun x => l x • x) p (v i)) = w p v
    rw [e1, multilinear_apply_add_smul_of_vanishing (w (l p • p)) (l p • p) (fun u i hu => hR _ hcp u i hu)]
    exact hH _ hc p hp v

end UpperTheory.V.Lit.Dr
end
end

section

noncomputable section

open Matrix
open scoped ContDiff

namespace UpperTheory.V.Lit.Dr

theorem pullEquiv : PullEquiv := by
  intro Γ V S _ _ _ d G _ l hl q η hη γ s p hp
  have hAp : (G.ρ γ⁻¹) p ∈ G.Y := G.maps γ⁻¹ p hp
  have hBA : ∀ x, (G.ρ γ) ((G.ρ γ⁻¹) x) = x := fun x => by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      ContinuousLinearMap.one_apply]
  have hAB : ∀ x, (G.ρ γ⁻¹) ((G.ρ γ) x) = x := fun x => by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      ContinuousLinearMap.one_apply]
  have hss : (G.σ γ) ((G.σ γ⁻¹) s) = s := by
    rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one, Equiv.Perm.one_apply]
  have hlinv : ∀ x ∈ G.Y, l s x = l ((G.σ γ⁻¹) s) ((G.ρ γ⁻¹) x) := fun x hx => by
    have h := hl.2 γ ((G.σ γ⁻¹) s) ((G.ρ γ⁻¹) x) (G.maps γ⁻¹ x hx)
    rw [hss, hBA] at h
    exact h
  have hηinv : ∀ x, (η : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s x = G.tr q γ ((η : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) ((G.σ γ⁻¹) s) ((G.ρ γ⁻¹) x)) := fun x => by
    have h := congrArg (fun w : G.Om q => (w : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s x) (hη γ)
    exact h.symm
  have hloc : (fun x => l s x • x) =ᶠ[nhds p]
      fun x => (G.ρ γ) (l ((G.σ γ⁻¹) s) ((G.ρ γ⁻¹) x) • (G.ρ γ⁻¹) x) :=
    Filter.eventuallyEq_of_mem (G.isOpen.mem_nhds hp) fun x hx => by
      rw [map_smul, hBA, hlinv x hx]
  have hdl : DifferentiableAt ℝ (l ((G.σ γ⁻¹) s)) ((G.ρ γ⁻¹) p) :=
    (((hl.1 ((G.σ γ⁻¹) s)).1).contDiffAt (G.isOpen.mem_nhds hAp)).differentiableAt (by simp)
  have hD : fderiv ℝ (fun x => l s x • x) p = (G.ρ γ) ∘L
      (fderiv ℝ (fun y => l ((G.σ γ⁻¹) s) y • y) ((G.ρ γ⁻¹) p)) ∘L (G.ρ γ⁻¹) := by
    rw [hloc.fderiv_eq]
    have h1 : HasFDerivAt (fun y => l ((G.σ γ⁻¹) s) y • y)
        (fderiv ℝ (fun y => l ((G.σ γ⁻¹) s) y • y) ((G.ρ γ⁻¹) p)) ((G.ρ γ⁻¹) p) :=
      (hdl.smul differentiableAt_id).hasFDerivAt
    exact ((G.ρ γ).hasFDerivAt.comp p (h1.comp p (G.ρ γ⁻¹).hasFDerivAt)).fderiv
  rw [pull, pull, hD, hηinv, hlinv p hp, map_smul]
  refine ContinuousAlternatingMap.ext fun v => ?_
  simp [Geo.tr, Function.comp_def, hAB]

end UpperTheory.V.Lit.Dr
end
end
