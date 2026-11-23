module

import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle011
public import Development.WeilBound.ThetaLifts.FrameEstimates.Bundle002
public import Development.AutomorphicSpectrum.Proofs.TwistedProofs.EqZeroOfPiInf
public import Development.WeilBound.ThetaLifts.FrameEstimates.LinDerA
public import Development.WeilBound.ThetaLifts.FrameEstimates.Bundle001
public import Development.WeilBound.ThetaLifts.FrameEstimates.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace ExponentialLineGeneration

set_option linter.unusedSectionVars false

section Banach

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

theorem exists_deriv {g : ℝ → A} (hc : Continuous g) (h0 : g 0 = 1) (ha : ∀ s t, g (s + t) = g s * g t) :
    ∃ Y : A, ∀ t, HasDerivAt g (g t * Y) t := by
  apply GlobalTheory.ExponentialIntegralUnits.exists_hasDerivAt <;> assumption

theorem exists_exp {g : ℝ → A} (hc : Continuous g) (h0 : g 0 = 1) (ha : ∀ s t, g (s + t) = g s * g t) :
    ∃ Y : A, HasDerivAt g Y 0 ∧ ∀ t, g t = NormedSpace.exp (t • Y) := by
  obtain ⟨Y, hY⟩ := exists_deriv hc h0 ha
  refine ⟨Y, by simpa [h0] using hY 0, fun t => ?_⟩
  have d : ∀ s : ℝ, HasDerivAt (fun s : ℝ => g s * NormedSpace.exp ((t - s) • Y)) 0 s := by
    intro s
    have d1 := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) Y (t - s)).scomp s ((hasDerivAt_id s).const_sub t)
    have d2 := (hY s).mul d1
    refine d2.congr_deriv ?_
    simp [mul_assoc]
  have c := is_const_of_deriv_eq_zero (fun s => (d s).differentiableAt) (fun s => (d s).deriv) t 0
  simpa [h0] using c

end Banach

set_option backward.isDefEq.respectTransparency false in
theorem mat_exp {d : ℕ} {g : ℝ → Matrix (Fin d) (Fin d) ℂ} (hc : Continuous g) (h0 : g 0 = 1)
    (ha : ∀ s t, g (s + t) = g s * g t) :
    ∃ Y : Matrix (Fin d) (Fin d) ℂ, (∀ i j, HasDerivAt (fun t => g t i j) (Y i j) 0) ∧
      ∀ t : ℝ, g t = NormedSpace.exp ((t : ℂ) • Y) := by
  open scoped Matrix.Norms.Operator in
  obtain ⟨Y, h1, h2⟩ := exists_exp (A := Matrix (Fin d) (Fin d) ℂ) hc h0 ha
  refine ⟨Y, fun i j => ?_, fun t => ?_⟩
  · exact (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j :
      Matrix (Fin d) (Fin d) ℂ →ₗ[ℝ] ℂ)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  · rw [h2 t, Complex.coe_smul]

theorem lie_of_unitary {d : ℕ} {g : ℝ → Matrix (Fin d) (Fin d) ℂ} {J Y : Matrix (Fin d) (Fin d) ℂ} (h0 : g 0 = 1)
    (hd : ∀ i j, HasDerivAt (fun t => g t i j) (Y i j) 0) (hu : ∀ t, (g t)ᵀ * J * (g t).map star = J) :
    Yᵀ * J + J * Y.map star = 0 := by
  ext i j
  have d1 : HasDerivAt (fun t => ∑ l, (∑ k, g t k i * J k l) * star (g t l j))
      (∑ l, ((∑ k, Y k i * J k l) * star (g 0 l j) + (∑ k, g 0 k i * J k l) * star (Y l j))) 0 :=
    HasDerivAt.fun_sum fun l _ => (HasDerivAt.fun_sum fun k _ => (hd k i).mul_const (J k l)).fun_mul (hd l j).star
  have e : (fun t => ∑ l, (∑ k, g t k i * J k l) * star (g t l j)) = fun _ => J i j := by
    funext t
    rw [← congrFun (congrFun (hu t) i) j]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  rw [e] at d1
  have z := d1.unique (hasDerivAt_const (0 : ℝ) (J i j))
  have e1 : (Yᵀ * J * (g 0).map star + (g 0)ᵀ * J * Y.map star) i j = 0 := by
    rw [← z, Finset.sum_add_distrib]
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  rwa [h0, Matrix.map_one _ (star_zero _) (star_one _), Matrix.mul_one, Matrix.transpose_one, Matrix.one_mul] at e1

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem piInf_tmul' {w : InfinitePlace F} (τ : EmbOver E w) (a : AF F) (x : E) :
    piInf τ (a ⊗ₜ[F] x) = InfinitePlace.Completion.extensionEmbedding w (a.1 w) * τ.1 x := by
  change infEmb τ (evInf F w a ⊗ₜ[F] x) = _
  rw [infEmb_tmul]
  rfl

theorem continuous_piInf {w : InfinitePlace F} (τ : EmbOver E w) : Continuous (piInf τ) := by
  refine IsModuleTopology.continuous_of_ringHom (R := AF F) (piInf τ) ?_
  have h : ⇑((piInf τ).comp (algebraMap (AF F) (AE F E))) =
      fun a : AF F => InfinitePlace.Completion.extensionEmbedding w (a.1 w) := by
    funext a
    change piInf τ (a ⊗ₜ[F] (1 : E)) = _
    rw [piInf_tmul', map_one, mul_one]
  rw [h]
  exact (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
    ((continuous_apply w).comp continuous_fst)

theorem piInf_cA (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) (z : AE F E) :
    piInf τ (cA σ z) = star (piInf τ z) := by
  have hw : w.IsReal := h.1.isReal w
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, star_zero]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, star_add]
  | tmul a x =>
    change piInf τ (a ⊗ₜ[F] σ x) = _
    rw [piInf_tmul', piInf_tmul', h.2.2.2, star_mul',
      ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw]
    rw [Complex.star_def, Complex.conj_ofReal]

theorem map_incM {w : InfinitePlace F} (τ : EmbOver E w) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  exact (piInf_tmul' τ 1 (J i j)).trans (by rw [show (1 : AF F).1 w = 1 from rfl, map_one, one_mul]; rfl)

end ExponentialLineGeneration

open ExponentialLineGeneration in
theorem lineGen_of : LineGen := by
  intro F E _ _ _ _ _ σ h τ d W _ γ hγ
  have main : ∀ w, ∃ Y : Matrix (Fin d) (Fin d) ℂ,
      Yᵀ * W.J.map (τ w).1 + W.J.map (τ w).1 * Y.map star = 0 ∧
      ∀ t : ℝ, (mat (γ (Multiplicative.ofAdd t))).map (piInf (τ w)) = NormedSpace.exp ((t : ℂ) • Y) := by
    intro w
    let g : ℝ → Matrix (Fin d) (Fin d) ℂ := fun t => (mat (γ (Multiplicative.ofAdd t))).map (piInf (τ w))
    have hm : Continuous (mat : UA σ W.J → Matrix (Fin d) (Fin d) (AE F E)) :=
      Units.continuous_val.comp continuous_subtype_val
    have hc : Continuous g :=
      ((hm.comp (hγ.1.comp continuous_ofAdd))).matrix_map (continuous_piInf (τ w))
    have h0 : g 0 = 1 := by
      change (mat (γ 1)).map (piInf (τ w)) = 1
      rw [map_one]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    have ha : ∀ s t, g (s + t) = g s * g t := by
      intro s t
      change (mat (γ (Multiplicative.ofAdd s * Multiplicative.ofAdd t))).map (piInf (τ w)) = _
      rw [map_mul]
      exact Matrix.map_mul
    obtain ⟨Y, h1, h2⟩ := mat_exp hc h0 ha
    refine ⟨Y, lie_of_unitary h0 h1 fun t => ?_, h2⟩
    have hu : (mat (γ (Multiplicative.ofAdd t)))ᵀ * incM F W.J * (mat (γ (Multiplicative.ofAdd t))).map (cA σ) =
        incM F W.J := (γ (Multiplicative.ofAdd t)).2
    have e : ((mat (γ (Multiplicative.ofAdd t))).map (cA σ)).map (piInf (τ w)) = (g t).map star := by
      ext i j
      exact piInf_cA h _ _
    have hv := congrArg (fun M : Matrix (Fin d) (Fin d) (AE F E) => M.map (piInf (τ w))) hu
    simp only [Matrix.map_mul] at hv
    rwa [Matrix.transpose_map, map_incM, e] at hv
  choose Y hY using main
  exact ⟨Y, fun w => (hY w).1, fun w => (hY w).2⟩

end PositivityTheory.ThKEst

end
end

section

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace LinDerPf

section Cx

variable {ι : Type} [Fintype ι] {d : ℕ}

def adj (J : ι → Matrix (Fin d) (Fin d) ℂ) : (ι → Matrix (Fin d) (Fin d) ℂ) →ₗ[ℝ] (ι → Matrix (Fin d) (Fin d) ℂ) where
  toFun x w := ((J w)⁻¹ * (x w)ᵀ * J w).map star
  map_add' x y := by
    funext w
    ext i j
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.transpose_add, Pi.add_apply, Matrix.map_apply, Matrix.add_apply,
      star_add]
  map_smul' r x := by
    funext w
    ext i j
    simp only [Matrix.transpose_smul, Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul, Matrix.map_apply,
      Matrix.smul_apply, star_smul, RingHom.id_apply, star_trivial]

omit [Fintype ι] in
theorem adj_iff {J : ι → Matrix (Fin d) (Fin d) ℂ} (hJ : ∀ w, IsUnit (J w).det) (Y : ι → Matrix (Fin d) (Fin d) ℂ) :
    adj J Y = -Y ↔ ∀ w, (Y w)ᵀ * J w + J w * (Y w).map star = 0 := by
  rw [funext_iff]
  refine forall_congr' fun w => ?_
  change ((J w)⁻¹ * (Y w)ᵀ * J w).map star = -Y w ↔ _
  have e : ((J w)⁻¹ * (Y w)ᵀ * J w).map star = -Y w ↔ (J w)⁻¹ * (Y w)ᵀ * J w = -(Y w).map star := by
    simp only [← Matrix.ext_iff, Matrix.map_apply, Matrix.neg_apply]
    refine forall_congr' fun i => forall_congr' fun j => ?_
    rw [star_eq_iff_star_eq, star_neg, eq_comm]
  rw [e, add_eq_zero_iff_eq_neg, ← Matrix.mul_neg]
  constructor
  · intro h
    rw [← h, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (hJ w)]
  · intro h
    rw [Matrix.mul_assoc, h, Matrix.nonsing_inv_mul_cancel_left _ _ (hJ w)]

set_option backward.isDefEq.respectTransparency false in
open scoped Matrix.Norms.Operator in
theorem mainM {J : ι → Matrix (Fin d) (Fin d) ℂ} (hJ : ∀ w, IsUnit (J w).det) :
    ∃ (m : ℕ) (Y : Fin m → ι → Matrix (Fin d) (Fin d) ℂ) (c : Fin m → (ι → Matrix (Fin d) (Fin d) ℂ) →ₗ[ℝ] ℝ),
      (∀ i w, (Y i w)ᵀ * J w + J w * (Y i w).map star = 0) ∧ ∀ Z Z' : ι → Matrix (Fin d) (Fin d) ℂ,
      (∀ w, (Z' w)ᵀ * J w + J w * (Z' w).map star = 0) →
      (∀ w (t : ℝ), NormedSpace.exp ((t : ℂ) • Z w) = NormedSpace.exp ((t : ℂ) • Z' w)) →
      ∃ s : Fin m → ℝ → ℝ, (∀ i, s i 0 = 0) ∧ (∀ i, HasDerivAt (s i) (c i Z) 0) ∧
        ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), ∀ w, NormedSpace.exp ((t : ℂ) • Z w) =
          (List.ofFn fun i => NormedSpace.exp ((s i t : ℂ) • Y i w)).prod := by
  let a : (ι → Matrix (Fin d) (Fin d) ℂ) →L[ℝ] (ι → Matrix (Fin d) (Fin d) ℂ) := LinearMap.toContinuousLinearMap (adj J)
  have ha : ∀ x y, a (x * y) = a y * a x := fun x y => by
    funext w
    change ((J w)⁻¹ * (x w * y w)ᵀ * J w).map (starRingEnd ℂ) =
      ((J w)⁻¹ * (y w)ᵀ * J w).map (starRingEnd ℂ) * ((J w)⁻¹ * (x w)ᵀ * J w).map (starRingEnd ℂ)
    rw [← Matrix.map_mul, Matrix.transpose_mul]
    congr 1
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (hJ w)]
  have h1 : a 1 = 1 := by
    funext w
    change ((J w)⁻¹ * (1 : Matrix (Fin d) (Fin d) ℂ)ᵀ * J w).map (starRingEnd ℂ) = 1
    rw [Matrix.transpose_one, Matrix.mul_one, Matrix.nonsing_inv_mul _ (hJ w), Matrix.map_one _ (map_zero _) (map_one _)]
  have hx : ∀ (t : ℝ) (x : ι → Matrix (Fin d) (Fin d) ℂ) w,
      NormedSpace.exp (t • x) w = NormedSpace.exp ((t : ℂ) • x w) := fun t x w => by
    rw [Pi.coe_exp, Pi.smul_apply, Complex.coe_smul]
  obtain ⟨m, Y, c, hY, h⟩ := main (a := a) ha h1
  refine ⟨m, Y, c, fun i => (adj_iff hJ _).1 (hY i), fun Z Z' hZ e => ?_⟩
  obtain ⟨s, s0, sd, se⟩ := h Z fun t => by
    have e' : NormedSpace.exp (t • Z) = NormedSpace.exp (t • Z') := funext fun w => by rw [hx, hx, e]
    rw [e']
    refine gr_exp ha h1 ?_
    rw [map_smul, ← smul_neg]
    exact congrArg _ ((adj_iff hJ _).2 hZ)
  refine ⟨s, s0, sd, se.mono fun t ht w => ?_⟩
  rw [← hx, ht, Pi.list_prod_apply, List.map_ofFn]
  congr 2
  funext i
  exact hx _ _ _

end Cx

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {d : ℕ}

omit [NumberField E] in
theorem uat_prod {W : Spc F E d} (l : List (UA σ W.J)) (hl : ∀ g ∈ l, g ∈ UAt σ W (evI F)) :
    l.prod ∈ UAt σ W (evI F) := by
  induction l with
  | nil =>
    intro c _
    change c • ((1 : Matrix (Fin d) (Fin d) (AE F E)) - 1) = 0
    rw [sub_self, smul_zero]
  | cons x l ih =>
    intro c hc
    have h1 := hl x (by simp) c hc
    have h2 := ih (fun g hg => hl g (by simp [hg])) c hc
    rw [List.prod_cons]
    change c • (mat x * mat l.prod - 1) = 0
    have e : mat x * mat l.prod - 1 = mat x * (mat l.prod - 1) + (mat x - 1) := by
      rw [Matrix.mul_sub, Matrix.mul_one, sub_add_sub_cancel]
    rw [e, smul_add, ← Matrix.mul_smul, h1, h2, Matrix.mul_zero, add_zero]

omit [NumberField E] in
theorem mat_prod {J : Matrix (Fin d) (Fin d) E} (p : AE F E →+* ℂ) (l : List (UA σ J)) :
    (mat l.prod).map p = (l.map fun g => (mat g).map p).prod := by
  induction l with
  | nil => exact Matrix.map_one _ (map_zero _) (map_one _)
  | cons x l ih =>
    rw [List.prod_cons, List.map_cons, List.prod_cons, ← ih, ← Matrix.map_mul]
    rfl

theorem uat_ext (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {W : Spc F E d} {u v : UA σ W.J}
    (hu : u ∈ UAt σ W (evI F)) (hv : v ∈ UAt σ W (evI F))
    (e : ∀ w, (mat u).map (piInf (τ w)) = (mat v).map (piInf (τ w))) : u = v := by
  refine Subtype.ext (Units.ext ?_)
  change mat u = mat v
  ext i j
  refine sub_eq_zero.1 (GlobalTheory.CompanionTheory.CMAdele.eq_zero_of_piInf σ h τ _ (fun c hc => ?_) fun w => ?_)
  · have e1 : c • (mat u - mat v) = 0 := by
      rw [← sub_sub_sub_cancel_right _ _ 1, smul_sub, hu c hc, hv c hc, sub_zero]
    exact congrFun (congrFun e1 i) j
  · rw [map_sub]
    exact sub_eq_zero.2 (congrFun (congrFun (e w) i) j)

end LinDerPf

open LinDerPf in
theorem linDer_of (hG : LineGen) (hX : LineEx) : LinDer := by
  intro F E _ _ _ _ _ σ h τ d W hW
  have hJ : ∀ w, IsUnit (W.J.map (τ w).1).det := fun w => by
    have e : (W.J.map (τ w).1).det = (τ w).1 W.J.det := (RingHom.map_det (τ w).1 W.J).symm
    rw [e]
    exact ((map_ne_zero (τ w).1).2 hW.2).isUnit
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : IsTopologicalGroup (GL (Fin d) (AE F E)) := inferInstance
  have : IsTopologicalGroup (UA σ W.J) := inferInstance
  obtain ⟨m, Y, c, hY, hm⟩ := mainM hJ
  choose β hβ hβY _ using fun i => hX F E σ h τ d W hW (Y i) (hY i)
  refine ⟨m, β, c, hβ, fun f f' hf γ hγ Z hZ g => ?_⟩
  obtain ⟨Z', hZ', hZZ⟩ := hG F E σ h τ d W hW γ hγ
  obtain ⟨s, s0, sd, se⟩ := hm Z Z' hZ' fun w t => (hZ w t).symm.trans (hZZ w t)
  have h1 := chain f m β (fun i => (hβ i).1) f' (fun i => (hf i).1) (fun i => (hf i).2) (fun _ => g)
    continuousAt_const s (fun i => c i Z) sd s0 0 (hasDerivAt_const _ _)
  rw [zero_add] at h1
  refine h1.congr_of_eventuallyEq (se.mono fun t ht => ?_)
  have e : γ (Multiplicative.ofAdd t) = (List.ofFn fun i => β i (Multiplicative.ofAdd (s i t))).prod := by
    refine uat_ext h τ (hγ.2 _) (uat_prod _ fun x hx => ?_) fun w => ?_
    · obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
      exact (hβ i).2 _
    · rw [hZ w t, ht w, mat_prod, List.map_ofFn]
      congr 2
      funext i
      exact (hβY i w _).symm
  simp only [e]

end PositivityTheory.ThKEst

end
end

section

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def umgComp (τ : ∀ w : InfinitePlace F, EmbOver E w) {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (w : InfinitePlace F) :
    UA σ J →* Matrix (Fin d) (Fin d) ℂ :=
  (piInf (τ w)).mapMatrix.toMonoidHom.comp ((Units.coeHom _).comp (Subgroup.subtype _))

theorem umg_continuousMul {d : ℕ} (J : Matrix (Fin d) (Fin d) E) : ContinuousMul (UA σ J) := by
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : IsTopologicalGroup (GL (Fin d) (AE F E)) := inferInstance
  exact (Subgroup.instIsTopologicalGroupSubtypeMem _).toContinuousMul

theorem umg_cj_mem {d : ℕ} {W : Spc F E d} {γ : Multiplicative ℝ →* UA σ W.J} (hγ : γ ∈ Lines σ W) (x : UA σ W.J) :
    UMGS.cj x γ ∈ Lines σ W := by
  have := umg_continuousMul (σ := σ) W.J
  refine ⟨((continuous_const.mul hγ.1).mul continuous_const).congr fun s => (UMGS.cj_apply x γ s).symm,
    fun t u hu => ?_⟩
  have h := hγ.2 t u hu
  have hm : ∀ a b : UA σ W.J, mat (a * b) = mat a * mat b := fun _ _ => rfl
  have h1 : mat x⁻¹ * mat x = 1 := by rw [← hm, inv_mul_cancel]; rfl
  have e : mat (UMGS.cj x γ t) - 1 = mat x⁻¹ * (mat (γ t) - 1) * mat x := by
    rw [UMGS.cj_apply, hm, hm, mul_sub, sub_mul, mul_one, h1]
  rw [e, ← Matrix.smul_mul, ← Matrix.mul_smul, h, Matrix.mul_zero, Matrix.zero_mul]

open scoped Matrix.Norms.Operator in
theorem umgSmooth_of (hL : LinDer) (hG : LineGen) : UMGSmooth := by
  intro F E _ _ _ _ _ σ hcm τ d W hW f hf k γ hγ g
  obtain ⟨r, β, c, hβ, hl⟩ := hL F E σ hcm τ d W hW
  obtain ⟨k₀, S, hfS, hS⟩ := hf
  have := umg_continuousMul (σ := σ) W.J
  have hGn : ∀ (δ : Multiplicative ℝ →* UA σ W.J) Y, UMGS.Gn (umgComp τ W.J) δ Y ↔ Gen τ W δ Y := fun δ Y =>
    forall₂_congr fun w t => by rw [Complex.coe_smul]; rfl
  refine contDiff_infty.2 fun n => ?_
  exact UMGS.contDiff_comp_pr (umgComp τ W.J) (Lines σ W) (fun _ h => h.1) (fun _ h x => umg_cj_mem h x)
    (fun δ h => (hG F E σ hcm τ d W hW δ h).imp fun Y hY => (hGn δ Y).2 hY.2) β c hβ
    (fun f f' h δ hδ Y hY => hl f f' h δ hδ Y ((hGn δ Y).1 hY)) S
    (fun f hf => ⟨(hS f hf).1, (hS f hf).2.2⟩) γ hγ g n f hfS

end PositivityTheory.ThKEst

end
end

section

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem umgLin_pow_le {x C : ℝ} {z : ℂ} (hx : 1 ≤ x) {k m : ℕ} (hk : k ≤ m) (h : ‖z‖ ≤ C * x ^ k) :
    ‖z‖ ≤ |C| * x ^ m :=
  h.trans <| mul_le_mul (le_abs_self C) (pow_le_pow_right₀ hx hk) (pow_nonneg (zero_le_one.trans hx) k) (abs_nonneg C)

theorem umgLin_of : UMGLin := by
  intro F E _ _ _ _ _ σ _ _ d W _ f f' hf hf' a b
  obtain ⟨k, S, hfS, hS⟩ := hf
  obtain ⟨k', S', hfS', hS'⟩ := hf'
  refine ⟨max k k', {g | ∃ f₁ ∈ S, ∃ f₁' ∈ S', g = a • f₁ + b • f₁'}, ⟨f, hfS, f', hfS', rfl⟩, ?_⟩
  rintro _ ⟨g, hg, g', hg', rfl⟩
  obtain ⟨hc, ⟨C, hC⟩, hd⟩ := hS g hg
  obtain ⟨hc', ⟨C', hC'⟩, hd'⟩ := hS' g' hg'
  refine ⟨(hc.const_smul a).add (hc'.const_smul b), ⟨‖a‖ * |C| + ‖b‖ * |C'|, fun h => ?_⟩, fun γ hγ => ?_⟩
  · have hx : (1 : ℝ) ≤ (ht h : ℝ) := by exact_mod_cast one_le_ht h
    have h1 := umgLin_pow_le hx (le_max_left k k') (hC h)
    have h2 := umgLin_pow_le hx (le_max_right k k') (hC' h)
    have h3 : ‖(a • g + b • g') h‖ ≤ ‖a‖ * ‖g h‖ + ‖b‖ * ‖g' h‖ := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul]
    have h4 := mul_le_mul_of_nonneg_left h1 (norm_nonneg a)
    have h5 := mul_le_mul_of_nonneg_left h2 (norm_nonneg b)
    linarith
  · obtain ⟨g₂, hg₂, e⟩ := hd γ hγ
    obtain ⟨g₂', hg₂', e'⟩ := hd' γ hγ
    exact ⟨a • g₂ + b • g₂', ⟨g₂, hg₂, g₂', hg₂', rfl⟩, fun h => ((e h).const_mul a).add ((e' h).const_mul b)⟩

end PositivityTheory.ThKEst

end
end
