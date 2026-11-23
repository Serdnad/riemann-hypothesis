module

public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle002
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle029
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle104
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle004
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle108
public import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Lemma
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
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle001
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsPowSmulMemBall
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle002

@[expose] public section

section

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

noncomputable section

namespace GlobalTheory.WigSh

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra

theorem isPolyDeg_prW {N : ℕ} (k r d : ℕ) (z : Fin (2 * r + k + 1) → ℂ)
    (v : Matrix (Fin N) (Fin N) ℂ → Fin (2 * r + k + 1) → ℂ) (hv : ∀ i, U.IsPolyDeg d (fun g => v g i))
    (i : Fin (2 * r + k + 1)) : U.IsPolyDeg d (fun g => D.prW k r z (v g) i) := by
  have hb : ∀ j : Fin (2 * r + k + 1),
      U.IsPolyDeg d (fun g => if r ≤ j.val ∧ j.val ≤ r + k then v g j else 0) := by
    intro j
    by_cases h : r ≤ j.val ∧ j.val ≤ r + k
    · simpa only [if_pos h] using hv j
    · simpa only [if_neg h] using pd_const (N := N) 0 d
  unfold D.prW
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
  refine pd_sub (hb i) (pd_mono (show d + 0 + 0 ≤ d by omega)
    (pd_mul (pd_mul ?_ (pd_const _ 0)) (pd_const _ 0)))
  unfold herm
  simp only [dotProduct, mulVec]
  refine pd_sum _ fun a _ => pd_mono (show 0 + d ≤ d by omega) (pd_mul (pd_const _ 0) ?_)
  exact pd_sum _ fun b _ => pd_mono (show 0 + d ≤ d by omega) (pd_mul (pd_const _ 0) (hb b))

theorem omg_isPolyDeg : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (i : Fin (2 * r + k + 1)),
    Formalism.FourierDecayAlt.U.IsPolyDeg (r + 1) (fun g : Mx k r => GlobalTheory.WigSh.omg k r z z' g i) := by
  intro k r z z' i
  unfold omg
  refine isPolyDeg_prW k r (r + 1) z' (fun g => (Hpk k r * gᴴ * Hpk k r) *ᵥ
    ∑ a, star ((Zhat k r z z' g).adjugate (Fin.last r) a) • fvec k r z a) (fun q => ?_) i
  simp only [dotProduct, mulVec]
  refine pd_sum _ fun s _ => pd_mono (show 1 + r ≤ r + 1 by omega) (pd_mul (P.TLC.omp_inv_pd q s) ?_)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact pd_sum _ fun a _ => pd_mono (show r + 0 ≤ r by omega)
    (pd_mul (P.TLC.omp_adj_pd z z' (Fin.last r) a) (pd_const _ 0))

end GlobalTheory.WigSh
end
end

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.RhvPoly

inductive IsPol {V : Type} [AddCommGroup V] [Module ℂ V] : (ℂ → V) → Prop
  | const (a : V) : IsPol fun _ => a
  | add {f g : ℂ → V} : IsPol f → IsPol g → IsPol fun y => f y + g y
  | xsmul {f : ℂ → V} : IsPol f → IsPol fun y => y • f y

section module

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

end module

section alg

variable {A : Type} [Ring A] [Algebra ℂ A]

end alg

open MeasureTheory in
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] in
private lemma isPol_finset_sum {ι : Type} (s : Finset ι) {f : ι → ℂ → V}
    (hf : ∀ i ∈ s, _root_.GlobalTheory.RhvPoly.IsPol (f i)) :
    _root_.GlobalTheory.RhvPoly.IsPol fun y => ∑ i ∈ s, f i y := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using _root_.GlobalTheory.RhvPoly.IsPol.const (0 : V)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

open MeasureTheory in
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] in
private lemma isPol_pow_smul (n : ℕ) (v : V) : _root_.GlobalTheory.RhvPoly.IsPol fun y : ℂ => y ^ n • v := by
  induction n with
  | zero => simpa using _root_.GlobalTheory.RhvPoly.IsPol.const v
  | succ n ih =>
    simp only [pow_succ', mul_smul]
    exact ih.xsmul

open MeasureTheory in
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] in
private lemma isPol_eval_smul (p : Polynomial ℂ) (v : V) :
    _root_.GlobalTheory.RhvPoly.IsPol fun y => p.eval y • v := by
  simp only [Polynomial.eval_eq_sum_range, Finset.sum_smul, mul_smul]
  refine isPol_finset_sum _ fun i _ => ?_
  convert isPol_pow_smul i (p.coeff i • v) using 1
  funext y
  exact smul_comm _ _ _

open MeasureTheory in
variable {A : Type} [Ring A] [Algebra ℂ A] in
private lemma isPol_linearMap_eval {ι : Type} [Fintype ι] [DecidableEq ι] (g : (ι → ℂ) →ₗ[ℂ] A)
    (p : ι → Polynomial ℂ) : _root_.GlobalTheory.RhvPoly.IsPol fun y => g (fun ρ => (p ρ).eval y) := by
  have h : ∀ y : ℂ, (fun ρ => (p ρ).eval y) = ∑ ρ, (p ρ).eval y • Pi.single ρ (1 : ℂ) := by
    intro y
    ext ρ'
    simp [Finset.sum_apply, Pi.single_apply]

  simp only [h, map_sum, map_smul]
  exact isPol_finset_sum _ fun ρ _ => isPol_eval_smul _ _

open MeasureTheory in
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] in
private lemma isPol_linearMap_comp (g : V →ₗ[ℂ] W) {f : ℂ → V} (hf : _root_.GlobalTheory.RhvPoly.IsPol f) :
    _root_.GlobalTheory.RhvPoly.IsPol fun y => g (f y) := by
  induction hf with
  | const a => exact .const _
  | add _ _ ihf ihg => simpa only [map_add (f := _)] using ihf.add ihg
  | xsmul _ ih => simpa only [map_smul] using ih.xsmul

open MeasureTheory in
variable {A : Type} [Ring A] [Algebra ℂ A] in
private lemma isPol_mul {f g : ℂ → A} (hf : _root_.GlobalTheory.RhvPoly.IsPol f) (hg : _root_.GlobalTheory.RhvPoly.IsPol g) :
    _root_.GlobalTheory.RhvPoly.IsPol fun y => f y * g y := by
  induction hf with
  | const a => exact isPol_linearMap_comp (LinearMap.mulLeft ℂ a) hg
  | add _ _ ihf ihg => simpa only [add_mul] using ihf.add ihg
  | xsmul _ ih => simpa only [smul_mul_assoc] using ih.xsmul

open MeasureTheory in
variable {A : Type} [Ring A] [Algebra ℂ A] in
private lemma isPol_algebraMap_eval (p : Polynomial ℂ) :
    _root_.GlobalTheory.RhvPoly.IsPol fun y => algebraMap ℂ A (p.eval y) := by
  simpa [Algebra.algebraMap_eq_smul_one] using isPol_eval_smul p (1 : A)

open MeasureTheory in
variable {A : Type} [Ring A] [Algebra ℂ A] in
private lemma isPol_list_prod {ι : Type} (l : List ι) {F : ι → ℂ → A}
    (hF : ∀ i, _root_.GlobalTheory.RhvPoly.IsPol (F i)) :
    _root_.GlobalTheory.RhvPoly.IsPol fun y => (l.map fun i => F i y).prod := by
  induction l with
  | nil => simpa using _root_.GlobalTheory.RhvPoly.IsPol.const (1 : A)
  | cons a l ih => simpa using isPol_mul (hF a) ih

open MeasureTheory in
variable {A : Type} [Ring A] [Algebra ℂ A] in
private lemma isPol_Tvprod' {r : ℕ} (L : _root_.Formalism.FourierDecayAlt.R.LevelData A r) :
    _root_.GlobalTheory.RhvPoly.IsPol fun y => L.Tvprod y := by
  have hT : ∀ i, _root_.GlobalTheory.RhvPoly.IsPol fun y => L.Tvl y i := by
    intro i
    have : (fun y => L.Tvl y i) =
        fun y => y • !![(1 : A), 0; 0, 0] + !![-L.pb i, -L.cb i; L.cbi i, 0] := by
      funext y
      unfold _root_.Formalism.FourierDecayAlt.R.LevelData.Tvl
      ext a b
      fin_cases a <;> fin_cases b <;> simp [Algebra.algebraMap_eq_smul_one, sub_eq_add_neg]
    rw [this]
    exact (_root_.GlobalTheory.RhvPoly.IsPol.const _).xsmul.add (.const _)
  have h : (fun y => L.Tvprod y) =
      fun y => ((List.finRange r).reverse.map fun i => L.Tvl y i).prod := by
    funext y
    unfold _root_.Formalism.FourierDecayAlt.R.LevelData.Tvprod
    simp [List.ofFn_eq_map, List.map_reverse]
  rw [h]
  exact isPol_list_prod _ hT

open MeasureTheory in
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] in
private lemma exists_polynomial_eq_functional_of_isPol {f : ℂ → V} (hf : _root_.GlobalTheory.RhvPoly.IsPol f) (φ : V →ₗ[ℂ] ℂ) :
    ∃ p : Polynomial ℂ, ∀ y, φ (f y) = p.eval y := by
  induction hf with
  | const a => exact ⟨Polynomial.C (φ a), fun y => by simp⟩
  | add _ _ ihf ihg =>
    obtain ⟨p, hp⟩ := ihf
    obtain ⟨q, hq⟩ := ihg
    exact ⟨p + q, fun y => by simp [hp, hq]⟩
  | xsmul _ ih =>
    obtain ⟨p, hp⟩ := ih
    exact ⟨Polynomial.X * p, fun y => by simp [hp]⟩

open MeasureTheory in
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] in
private lemma isPol_eq_zero_of_infinite_zeros {f : ℂ → V} (hf : _root_.GlobalTheory.RhvPoly.IsPol f) {S : Set ℂ}
    (hS : S.Infinite) (h0 : ∀ y ∈ S, f y = 0) (y : ℂ) : f y = 0 := by
  rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  obtain ⟨p, hp⟩ := exists_polynomial_eq_functional_of_isPol hf φ
  have : p = 0 := Polynomial.eq_zero_of_infinite_isRoot p
    (hS.mono fun x hx => by simp [← hp, h0 x hx])
  simp [hp, this]


open MeasureTheory in
theorem _root_.GlobalTheory.RhvPoly.rhv_mem_of_infinite : ∀ (P : _root_.Formalism.FourierDecayAlt.M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A]
    (d : _root_.Formalism.FourierDecayAlt.Q.NFData P A) (K : Submodule ℂ A) (S : Set ℂ), S.Infinite →
    (∀ y ∈ S, _root_.GlobalTheory.HatNF.rhv d y ∈ K) → ∀ y : ℂ, _root_.GlobalTheory.HatNF.rhv d y ∈ K := by
  intro P A _ _ _ d K S hS hmem y
  classical
  have hx : _root_.GlobalTheory.RhvPoly.IsPol fun y => d.x y := by
    have := isPol_linearMap_eval d.κ.toLinearMap
      (fun ρ => ∏ i ∈ Finset.Icc 1 (P.k - 1), (Polynomial.X + Polynomial.C ((_root_.Formalism.FourierDecayAlt.M.rho P ρ i : ℂ))))
    convert this using 2 with y
    unfold _root_.Formalism.FourierDecayAlt.Q.NFData.x _root_.Formalism.FourierDecayAlt.M.xC
    simp [Polynomial.eval_prod]
  have hS12 : _root_.GlobalTheory.RhvPoly.IsPol fun y => d.S12 y := by
    unfold _root_.Formalism.FourierDecayAlt.Q.NFData.S12
    refine isPol_finset_sum _ fun l _ => isPol_mul ?_ (.const _)
    have := isPol_linearMap_eval d.κ.toLinearMap
      (fun ρ => ∏ i ∈ Finset.Icc 1 (P.k - 1) \ {l}, (Polynomial.X + Polynomial.C ((_root_.Formalism.FourierDecayAlt.M.rho P ρ i : ℂ))))
    convert this using 2 with y
    unfold _root_.Formalism.FourierDecayAlt.M.xEx
    simp [Polynomial.eval_prod]
  have hm0 : _root_.GlobalTheory.RhvPoly.IsPol fun y => d.L.m0 y := by
    have := (_root_.GlobalTheory.RhvPoly.IsPol.const (-d.L.nabs)).add
      (isPol_linearMap_comp (LinearMap.mulRight ℂ (-(d.L.ζ * d.L.GGi)))
        (isPol_algebraMap_eval (A := A) (Polynomial.X - Polynomial.C (1 / 2))))
    convert this using 2 with y
    unfold _root_.Formalism.FourierDecayAlt.R.LevelData.m0
    simp [sub_eq_add_neg]
  have hTv := isPol_Tvprod' d.L
  have hentry : ∀ i j : Fin 2, _root_.GlobalTheory.RhvPoly.IsPol fun y => d.L.Tvprod y i j :=
    fun i j => isPol_linearMap_comp (Matrix.entryLinearMap ℂ A i j) hTv
  have hpol : _root_.GlobalTheory.RhvPoly.IsPol fun y => _root_.GlobalTheory.HatNF.rhv d y := by
    have h : (fun y => _root_.GlobalTheory.HatNF.rhv d y) = fun y =>
        d.L.Dr * ((d.L.GG * d.x y * d.L.m0 y + d.S12 y) * d.L.Tvprod y 0 0 +
          d.L.GG * d.x y * d.L.Tvprod y 1 0) := by
      funext y
      unfold _root_.GlobalTheory.HatNF.rhv _root_.Formalism.FourierDecayAlt.Q.NFData.QQ _root_.Formalism.FourierDecayAlt.R.LevelData.Avr _root_.Formalism.FourierDecayAlt.R.LevelData.Bvr
      simp
    rw [h]
    refine isPol_mul (.const _) (.add (isPol_mul (.add (isPol_mul (isPol_mul (.const _) hx) hm0) hS12)
      (hentry 0 0)) (isPol_mul (isPol_mul (.const _) hx) (hentry 1 0)))
  have hq := isPol_linearMap_comp K.mkQ hpol
  have := isPol_eq_zero_of_infinite_zeros hq hS
    (fun y hy => (Submodule.Quotient.mk_eq_zero K).2 (hmem y hy)) y
  exact (Submodule.Quotient.mk_eq_zero K).1 this

end GlobalTheory.RhvPoly
end

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
open scoped ContDiff

namespace GlobalTheory.HatNF.MulCoord

noncomputable section

theorem exists_fderiv_log {m : ℕ} (γ : ℝ) (hγ : 0 < γ) (c : Fin m → ℂ) (hc : c ∈ OmX m) :
    ∃ D : (Fin m → ℂ) →L[ℝ] ℝ,
      HasFDerivAt (fun x : Fin m → ℂ => Real.log (Complex.normSq (∏ a, x a) * γ)) D c ∧
      ∀ l w, D (Pi.single l w) = 2 * ((c l).re * w.re + (c l).im * w.im) / Complex.normSq (c l) := by
  classical
  have hopen : IsOpen (OmX m) := by
    have : OmX m = ⋂ l, {x : Fin m → ℂ | x l ≠ 0} := by ext x; simp [OmX]
    rw [this]
    exact isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const
  let pr : Fin m → ((Fin m → ℂ) →L[ℝ] ℂ) := fun a => ContinuousLinearMap.proj a
  let R : Fin m → ((Fin m → ℂ) →L[ℝ] ℝ) := fun a => Complex.reCLM.comp (pr a)
  let J : Fin m → ((Fin m → ℂ) →L[ℝ] ℝ) := fun a => Complex.imCLM.comp (pr a)
  have h1 : ∀ a, HasFDerivAt (fun x : Fin m → ℂ => Real.log (R a x * R a x + J a x * J a x))
      ((R a c * R a c + J a c * J a c)⁻¹ • ((R a c • R a + R a c • R a) + (J a c • J a + J a c • J a))) c := by
    intro a
    refine HasFDerivAt.log (((R a).hasFDerivAt.mul (R a).hasFDerivAt).add
      ((J a).hasFDerivAt.mul (J a).hasFDerivAt)) ?_
    have : Complex.normSq (c a) ≠ 0 := by simpa using hc a
    simpa [R, J, pr, Complex.normSq_apply] using this
  have h2 := (HasFDerivAt.fun_sum (u := Finset.univ) fun a _ => h1 a).add_const (Real.log γ)
  refine ⟨_, h2.congr_of_eventuallyEq ?_, ?_⟩
  · filter_upwards [hopen.mem_nhds hc] with x hx
    have hx' : ∀ a, Complex.normSq (x a) ≠ 0 := fun a => by simpa using hx a
    rw [map_prod, Real.log_mul (Finset.prod_ne_zero_iff.2 fun a _ => hx' a) hγ.ne',
      Real.log_prod (fun a _ => hx' a)]
    simp [R, J, pr, Complex.normSq_apply]
  · intro l w
    rw [ContinuousLinearMap.sum_apply, Finset.sum_eq_single l]
    · simp [R, J, pr, Complex.normSq_apply]
      ring
    · intro b _ hb
      simp [R, J, pr, Pi.single_eq_of_ne hb]
    · simp

theorem euler_mul {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (φ : ℝ → ℝ) (hφ : LE.SmoothLog φ)
    (q : ℕ) (γ : ℝ) (hγ : 0 < γ) (c : Fin m → ℂ) (hc : c ∈ OmX m) (f : (Fin m → ℂ) → E)
    (hf : DifferentiableAt ℝ f c) (l : Fin m) :
    pOp l (fun x => ((LE.ld q φ (Complex.normSq (∏ a, x a) * γ) : ℝ) : ℂ) • f x) c =
      ((LE.ld q φ (Complex.normSq (∏ a, c a) * γ) : ℝ) : ℂ) • pOp l f c +
        ((LE.ld (q + 1) φ (Complex.normSq (∏ a, c a) * γ) : ℝ) : ℂ) • f c ∧
    pbOp l (fun x => ((LE.ld q φ (Complex.normSq (∏ a, x a) * γ) : ℝ) : ℂ) • f x) c =
      ((LE.ld q φ (Complex.normSq (∏ a, c a) * γ) : ℝ) : ℂ) • pbOp l f c +
        ((LE.ld (q + 1) φ (Complex.normSq (∏ a, c a) * γ) : ℝ) : ℂ) • f c := by
  obtain ⟨D, hD, hDl⟩ := exists_fderiv_log γ hγ c hc
  have hh : Differentiable ℝ (iteratedDeriv q fun u : ℝ => φ (Real.exp u)) :=
    ContDiff.differentiable_iteratedDeriv q hφ (by exact_mod_cast ENat.coe_lt_top q)
  have h1 : HasDerivAt (iteratedDeriv q fun u : ℝ => φ (Real.exp u))
      (LE.ld (q + 1) φ (Complex.normSq (∏ a, c a) * γ)) (Real.log (Complex.normSq (∏ a, c a) * γ)) := by
    rw [LE.ld, iteratedDeriv_succ]
    exact (hh _).hasDerivAt
  have h2 := Complex.ofRealCLM.hasFDerivAt.comp c (h1.comp_hasFDerivAt c hD)
  have h3 : HasFDerivAt (fun x => ((LE.ld q φ (Complex.normSq (∏ a, x a) * γ) : ℝ) : ℂ) • f x) _ c :=
    HasFDerivAt.smul h2 hf.hasFDerivAt
  have key : ∀ w, fderiv ℝ (fun x => ((LE.ld q φ (Complex.normSq (∏ a, x a) * γ) : ℝ) : ℂ) • f x) c
      (Pi.single l w) = ((LE.ld q φ (Complex.normSq (∏ a, c a) * γ) : ℝ) : ℂ) • fderiv ℝ f c (Pi.single l w) +
        ((LE.ld (q + 1) φ (Complex.normSq (∏ a, c a) * γ) *
          (2 * ((c l).re * w.re + (c l).im * w.im) / Complex.normSq (c l)) : ℝ) : ℂ) • f c := by
    intro w
    rw [h3.fderiv, ← hDl]
    simp [LE.ld]
  have hn : ((Complex.normSq (c l) : ℝ) : ℂ) ≠ 0 := by simpa using hc l
  have e1 : c l * (((c l).re : ℂ) - Complex.I * (c l).im) = (Complex.normSq (c l) : ℝ) := by
    apply Complex.ext <;> simp [Complex.normSq_apply] <;> ring
  have e2 : star (c l) * (((c l).re : ℂ) + Complex.I * (c l).im) = (Complex.normSq (c l) : ℝ) := by
    apply Complex.ext <;> simp [Complex.normSq_apply] <;> ring
  constructor
  · simp only [pOp, if_pos hc, wirt, key]
    simp only [Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im]
    push_cast
    match_scalars
    · ring
    · field_simp
      linear_combination (LE.ld (q + 1) φ (Complex.normSq (∏ a, c a) * γ) : ℂ) * e1
    · ring
  · simp only [pbOp, if_pos hc, wirtBar, key]
    simp only [Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im]
    push_cast
    match_scalars
    · ring
    · field_simp
      linear_combination (LE.ld (q + 1) φ (Complex.normSq (∏ a, c a) * γ) : ℂ) * e2
    · ring

section radial

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Q.Mx k r → (Wp →L[ℂ] Wp)} {π' : Q.Mx k r → (Wq →L[ℂ] Wq)}

theorem end_ext (A B : Module.End ℂ (Q.RadSp k r z z' π π'))
    (h : ∀ Φ, ∀ c g, (c, g) ∈ Q.DomR k r z z' →
      (A Φ : Q.Fn k r (Wq →L[ℂ] Wp)) c g = (B Φ : Q.Fn k r (Wq →L[ℂ] Wp)) c g) : A = B := by
  refine LinearMap.ext fun Φ => Subtype.ext ?_
  funext c g
  by_cases hx : (c, g) ∈ Q.DomR k r z z'
  · exact h Φ c g hx
  · exact ((A Φ).2.1 (c, g) hx).trans ((B Φ).2.1 (c, g) hx).symm


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem differentiableAt_coord (Φ : Q.RadSp k r z z' π π') (c : Fin r → ℂ) (g : Q.Mx k r)
    (hx : (c, g) ∈ Q.DomR k r z z') :
    DifferentiableAt ℝ (fun c' => (Φ : Q.Fn k r (Wq →L[ℂ] Wp)) c' g) c := by
  obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := Φ.2.2.1 (c, g) hx
  have h1 : DifferentiableAt ℝ F (c, g) :=
    (hF.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)
  have h2 : DifferentiableAt ℝ (fun c' : Fin r → ℂ => F (c', g)) c :=
    h1.comp c (differentiableAt_id.prodMk (differentiableAt_const g))
  refine h2.congr_of_eventuallyEq ?_
  have hc : ContinuousAt (fun c' : Fin r → ℂ => (c', g)) c := (continuous_id.prodMk continuous_const).continuousAt
  filter_upwards [hc.preimage_mem_nhds (hU.mem_nhds hxU)] with c' hc'
  exact hΦ (c', g) hc' hx.2.1

theorem commute_of_mul (A B : Module.End ℂ (Q.RadSp k r z z' π π')) (a b : (Fin r → ℂ) → Q.Mx k r → ℂ)
    (hA : ∀ Φ, ∀ c g, (c, g) ∈ Q.DomR k r z z' →
      (A Φ : Q.Fn k r (Wq →L[ℂ] Wp)) c g = a c g • (Φ : Q.Fn k r (Wq →L[ℂ] Wp)) c g)
    (hB : P5.multiplicationOperator B b) : Commute A B := by
  refine end_ext _ _ fun Φ c g hx => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, hA _ c g hx, hB, hB, hA _ c g hx, smul_comm]

end radial

theorem mul_coord : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ (φ : ℝ → ℝ) (W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')), LE.SmoothLog φ → IsMulG P Bs φ W → ∀ q, (∀ l, X.op l 0 * W q = W q * X.op l 0 + W (q + 1) ∧ X.op l 3 * W q = W q * X.op l 3 + W (q + 1) ∧ Commute (X.op l 1) (W q) ∧ Commute (X.op l 2) (W q) ∧ Commute (X.op l 4) (W q) ∧ Commute (X.op l 5) (W q)) ∧ ∀ j, Commute (X.fn j) (W q) := by
  intro Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 d _ _ φ W hφ hW q
  refine ⟨fun l => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, fun j => ?_⟩
  · refine end_ext _ _ fun Φ c g hx => ?_
    have h := (euler_mul φ hφ q _ hx.2.2 c hx.1 _ (differentiableAt_coord Φ c g hx) l).1
    rw [LinearMap.add_apply, Module.End.mul_apply, Module.End.mul_apply, Submodule.coe_add, Pi.add_apply,
      Pi.add_apply, hW q, hW (q + 1), X.op_apply, X.op_apply]
    simp only [Q.crd, opL, hW q Φ]
    exact h
  · refine end_ext _ _ fun Φ c g hx => ?_
    have h := (euler_mul φ hφ q _ hx.2.2 c hx.1 _ (differentiableAt_coord Φ c g hx) l).2
    rw [LinearMap.add_apply, Module.End.mul_apply, Module.End.mul_apply, Submodule.coe_add, Pi.add_apply,
      Pi.add_apply, hW q, hW (q + 1), X.op_apply, X.op_apply]
    simp only [Q.crd, opL, hW q Φ]
    exact h
  · exact commute_of_mul _ _ (fun c _ => c l) _ (fun Φ c g _ => by rw [X.op_apply]; rfl) (hW q)
  · exact commute_of_mul _ _ (fun c _ => (c l)⁻¹) _ (fun Φ c g _ => by rw [X.op_apply]; rfl) (hW q)
  · exact commute_of_mul _ _ (fun c _ => star (c l)) _ (fun Φ c g _ => by rw [X.op_apply]; rfl) (hW q)
  · exact commute_of_mul _ _ (fun c _ => (star (c l))⁻¹) _ (fun Φ c g _ => by rw [X.op_apply]; rfl) (hW q)
  · exact commute_of_mul _ _ (fun _ g => Q.fnVal P.k P.r Bs.z Bs.z' j g) _
      (fun Φ c g hx => X.fn_apply j Φ (c, g) hx) (hW q)

end

end GlobalTheory.HatNF.MulCoord
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.PtTie

namespace GlobalTheory.LevelSplit

theorem splitsIn_level_prime : ∀ (D : D7) (i : Fin 2), SplitsIn D.host.E (D.host.g i) := fun D i =>
  GlobalTheory.HalfGen.factors_of_ncard_places D.host.E (D.host.g i) (D.host.g_prime i) (D.nd.g_split i)

end GlobalTheory.LevelSplit
end

section

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie
namespace GlobalTheory.PtTie

theorem barE_piG_eq_piBarO {D : D7} (EX : ErrX D) (i : Fin 2) : barE D (EX.piG i) = piBarO EX i := by
  apply IsFractionRing.injective (𝓞 D.host.E) D.host.E
  exact barE_eq_conj D (EX.piG i)

theorem halfEX_iff_oriented : ∀ (D : D7) (T : Top D), LawsP T → ∀ EX : ErrX D, HalfEX T.toCore EX ↔ Oriented T EX := by
  intro D T h EX
  rw [GlobalTheory.Survey.PiTwistNegation.halfEX_iff_le T.toCore h.toLawsCore.toLawsM EX]
  exact forall_congr' fun i => by rw [barE_piG_eq_piBarO]

end GlobalTheory.PtTie
end
end
