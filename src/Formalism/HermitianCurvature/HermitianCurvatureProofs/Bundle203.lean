module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle193
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QxChain
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
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

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff Topology
open Filter

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.TVCrdLoc

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] {k r : ℕ}

def gam (k r : ℕ) (a : Fin r) (x : Fin r → ℂ) : ℂ := ((‖x a‖ ^ (Mdim k r a - 1) : ℝ) : ℂ)

theorem gaugeF_eq (k r : ℕ) : gaugeF k r = fun x => ∏ a : Fin r, gam k r a x := by
  funext x
  unfold gaugeF Formalism.FourierDecayAlt.Q.resG
  simp only [smul_eq_mul, mul_one, gam, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [if_pos (by simp)]

theorem gam_smooth (a : Fin r) : ContDiffOn ℝ ∞ (gam k r a) (OmX r) := by
  intro x hx
  have h1 : ContDiffAt ℝ ∞ (fun c : Fin r → ℂ => ‖c a‖) x :=
    (contDiffAt_norm ℝ (hx a)).comp x
      (ContinuousLinearMap.proj a : (Fin r → ℂ) →L[ℝ] ℂ).contDiff.contDiffAt
  have h2 := Complex.ofRealCLM.contDiff.contDiffAt.comp x (h1.pow (Mdim k r a - 1))
  exact h2.contDiffWithinAt

theorem gaugeF_smooth : ContDiffOn ℝ ∞ (gaugeF k r) (OmX r) := by
  rw [gaugeF_eq]
  exact contDiffOn_prod fun a _ => gam_smooth a

theorem gaugeF_ne {c : Fin r → ℂ} (hc : c ∈ OmX r) : gaugeF k r c ≠ 0 := by
  rw [gaugeF_eq]
  exact Finset.prod_ne_zero_iff.mpr fun a _ =>
    Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (norm_ne_zero_iff.mpr (hc a)))

theorem fderiv_zero_of_const {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {h : (Fin r → ℂ) → F}
    {x v : Fin r → ℂ} (hd : DifferentiableAt ℝ h x) (hc : ∀ t : ℝ, h (x + t • v) = h x) :
    fderiv ℝ h x v = 0 := by
  have hf : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have h1 : HasDerivAt (fun t : ℝ => h (x + t • v)) (fderiv ℝ h x v) 0 :=
    hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hf (by simp)
  have h2 : HasDerivAt (fun t : ℝ => h (x + t • v)) 0 0 := by
    simp_rw [hc]
    exact hasDerivAt_const _ _
  exact h1.unique h2

def gamO (k r : ℕ) (i : Fin r) (x : Fin r → ℂ) : ℂ := ∏ a ∈ Finset.univ.erase i, gam k r a x

theorem gamO_smooth (i : Fin r) : ContDiffOn ℝ ∞ (gamO k r i) (OmX r) := by
  unfold gamO
  exact contDiffOn_prod fun a _ => gam_smooth a

theorem gamO_line (i : Fin r) (x : Fin r → ℂ) (w : ℂ) (t : ℝ) :
    gamO k r i (x + t • (Pi.single i w : Fin r → ℂ)) = gamO k r i x := by
  unfold gamO
  refine Finset.prod_congr rfl fun a ha => ?_
  have hai : a ≠ i := Finset.ne_of_mem_erase ha
  simp only [gam, Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hai, smul_zero, add_zero]

theorem gauge_split (i : Fin r) (x : Fin r → ℂ) : gaugeF k r x = gam k r i x * gamO k r i x := by
  rw [gaugeF_eq, gamO]
  exact (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm

private theorem wbar_smul_lemma {m : ℕ} (l : Fin m) (c : (Fin m → ℂ) → ℂ) (φ : (Fin m → ℂ) → X)
    (x : Fin m → ℂ) (hc : DifferentiableAt ℝ c x) (hφ : DifferentiableAt ℝ φ x) :
    wirtBar l (fun y => c y • φ y) x = c x • wirtBar l φ x + wirtBar l c x • φ x := by
  unfold Formalism.QuantumDeterminants.wirtBar
  have e : (fun y => c y • φ y) = c • φ := rfl
  rw [e, fderiv_smul hc hφ]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  module

theorem pbOp_gauge (i : Fin r) (f : (Fin r → ℂ) → X) (hf : f ∈ WSm r X) :
    pbOp i (fun x => gaugeF k r x • f x) =
      fun x => gaugeF k r x • pbOp i f x + (((Mdim k r i - 1 : ℕ) : ℂ) / 2) • (gaugeF k r x • f x) := by
  funext x
  show pbOp i (fun x => gaugeF k r x • f x) x =
    gaugeF k r x • pbOp i f x + (((Mdim k r i - 1 : ℕ) : ℂ) / 2) • (gaugeF k r x • f x)
  by_cases hx : x ∈ OmX r
  · have hO : IsOpen (OmX r) := by
      have e : OmX r = ⋂ l, {y : Fin r → ℂ | y l ≠ 0} := by
        ext y
        simp [OmX]
      rw [e]
      exact isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const
    have hfd : DifferentiableAt ℝ f x :=
      (hf.1.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
    have hgi : DifferentiableAt ℝ (gam k r i) x := Formalism.FourierDecayAlt.P.Qx6.diff_gamma i _ hx
    have hgO : DifferentiableAt ℝ (gamO k r i) x :=
      ((gamO_smooth i).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
    have hsplit : (fun y => gaugeF k r y • f y) = fun y => gam k r i y • (gamO k r i y • f y) := by
      funext y
      rw [gauge_split, mul_smul]

    have hwO : wirtBar i (gamO k r i) x = 0 := by
      unfold Formalism.QuantumDeterminants.wirtBar
      rw [fderiv_zero_of_const hgO (gamO_line i x 1), fderiv_zero_of_const hgO (gamO_line i x Complex.I)]
      simp
    have hpg := Formalism.FourierDecayAlt.P.Qx6.pbOp_gamma i hx (Mdim k r i - 1)
    unfold pbOp at hpg
    rw [if_pos hx] at hpg
    have key : star (x i) * wirtBar i (gam k r i) x =
        ((Mdim k r i - 1 : ℕ) : ℂ) / 2 * gam k r i x := by
      rw [← smul_eq_mul]
      exact hpg
    unfold pbOp
    rw [if_pos hx, if_pos hx, hsplit, wbar_smul_lemma i (gam k r i) (fun y => gamO k r i y • f y) x hgi (hgO.smul hfd),
      wbar_smul_lemma i _ _ x hgO hfd, hwO, gauge_split]
    simp only [smul_add, zero_smul, add_zero, smul_smul]
    rw [← mul_assoc (star (x i)) (wirtBar i (gam k r i) x), key]
    congr 1 <;> congr 1 <;> ring
  · unfold pbOp
    rw [if_neg hx, if_neg hx, hf.2 x hx]
    simp

theorem loc (Φ : (Fin r → ℂ) → X) (U : Set (Fin r → ℂ)) (c : Fin r → ℂ) (hU : IsOpen U) (hUO : U ⊆ OmX r)
    (hc : c ∈ U) (hΨ : ContDiffOn ℝ ∞ (fun c' => gaugeF k r c' • Φ c') U) :
    ∃ φ : (Fin r → ℂ) → X, φ ∈ WSm r X ∧ Φ =ᶠ[𝓝 c] φ ∧
      (fun c' => gaugeF k r c' • Φ c') =ᶠ[𝓝 c] (fun c' => gaugeF k r c' • φ c') := by
  have hO : IsOpen (OmX r) := by
    have e : OmX r = ⋂ l, {y : Fin r → ℂ | y l ≠ 0} := by
      ext y
      simp [OmX]
    rw [e]
    exact isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU c hc

  let χ : ContDiffBump c := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  have hcl : Metric.closedBall c (ε / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hχ0 : ∀ z, z ∉ Metric.closedBall c (ε / 2) → χ z = 0 := by
    intro z hz
    have h1 : z ∉ Function.support χ := by
      rw [χ.support_eq]
      exact fun h => hz (Metric.ball_subset_closedBall h)
    simpa [Function.mem_support] using h1
  let φ : (Fin r → ℂ) → X := fun y => χ y • ((gaugeF k r y)⁻¹ • (gaugeF k r y • Φ y))
  have hev : Φ =ᶠ[𝓝 c] φ := by
    refine Filter.eventually_of_mem (Metric.ball_mem_nhds c (by positivity : (0 : ℝ) < ε / 4))
      fun y hy => ?_
    have hyU : y ∈ U := hball (Metric.ball_subset_ball (by linarith) hy)
    have h1 : χ y = 1 := χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)
    show Φ y = χ y • ((gaugeF k r y)⁻¹ • (gaugeF k r y • Φ y))
    rw [h1, one_smul, inv_smul_smul₀ (gaugeF_ne (hUO hyU))]
  have hsm : ∀ y ∈ OmX r, ContDiffAt ℝ ∞ φ y := by
    intro y hyO
    by_cases hyU : y ∈ U
    · have hg := (gaugeF_smooth (k := k)).contDiffAt (hO.mem_nhds hyO)
      have hgi := hg.inv (gaugeF_ne hyO)
      have hΨ' := hΨ.contDiffAt (hU.mem_nhds hyU)
      exact χ.contDiff.contDiffAt.smul (hgi.smul hΨ')
    · have hyc : y ∉ Metric.closedBall c (ε / 2) := fun h => hyU (hcl h)
      refine (contDiffAt_const (c := (0 : X))).congr_of_eventuallyEq ?_
      refine Filter.eventually_of_mem (Metric.isClosed_closedBall.isOpen_compl.mem_nhds hyc)
        fun z hz => ?_
      show χ z • ((gaugeF k r z)⁻¹ • (gaugeF k r z • Φ z)) = 0
      rw [hχ0 z hz, zero_smul]
  refine ⟨φ, ?_, hev, hev.mono fun y hy => congrArg (gaugeF k r y • ·) hy⟩
  show ContDiffOn ℝ ∞ φ (OmX r) ∧ ∀ x, x ∉ OmX r → φ x = 0
  refine ⟨fun y hy => (hsm y hy).contDiffWithinAt, fun y hy => ?_⟩
  have hyc : y ∉ Metric.closedBall c (ε / 2) := fun h => hy (hUO (hcl h))
  show χ y • ((gaugeF k r y)⁻¹ • (gaugeF k r y • Φ y)) = 0
  rw [hχ0 y hyc, zero_smul]

end Formalism.FourierDecayAlt.P.CutMP.TVCrdLoc
end
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace SymbolOperatorExtension

variable {d : ℕ}

def ext (S : SOp d) (n : ℕ) (w : Fin n → Fin d) : (Fin d → ℝ) → ℂ :=
  if h : n < S.ord + 1 then S.a ⟨n, h⟩ w else fun _ => 0

theorem ext_fin (S : SOp d) (k : Fin (S.ord + 1)) (w : Fin k → Fin d) : ext S k w = S.a k w := by
  unfold ext
  rw [dite_eq_left k.isLt]

theorem ext_last (S : SOp d) (w : Fin S.ord → Fin d) : ext S S.ord w = S.a (Fin.last S.ord) w := by
  unfold ext
  rw [dite_eq_left (Nat.lt_succ_self _)]
  rfl

theorem ext_top (S : SOp d) (w : Fin (S.ord + 1) → Fin d) : ext S (S.ord + 1) w = fun _ => 0 := by
  unfold ext
  rw [dite_eq_right (lt_irrefl _)]

theorem ext_contDiffOn (S : SOp d) {O : Set (Fin d → ℝ)} (hS : ∀ i w, ContDiffOn ℝ ∞ (S.a i w) O) (n : ℕ)
    (w : Fin n → Fin d) : ContDiffOn ℝ ∞ (ext S n w) O := by
  unfold ext
  split_ifs with h
  · exact hS _ _
  · exact contDiffOn_const

theorem app_eq (S : SOp d) (u : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) :
    S.app u x = ∑ n ∈ Finset.range (S.ord + 1), ∑ w : Fin n → Fin d, ext S n w x * pdc (List.ofFn w) u x := by
  rw [← Fin.sum_univ_eq_sum_range (fun n => ∑ w : Fin n → Fin d, ext S n w x * pdc (List.ofFn w) u x)]
  unfold SOp.app
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [ext_fin]

theorem pdc_contDiffOn {O : Set (Fin d → ℝ)} (hO : IsOpen O) {u : (Fin d → ℝ) → ℂ} {m : ℕ}
    (hu : ContDiffOn ℝ (m : WithTop ℕ∞) u O) :
    ∀ (l : List (Fin d)) (k : ℕ), l.length + k ≤ m → ContDiffOn ℝ (k : WithTop ℕ∞) (pdc l u) O
  | [], k, h => hu.of_le (by exact_mod_cast (show k ≤ m by simpa using h))
  | i :: l, k, h => by
    have ih := pdc_contDiffOn hO hu l (k + 1) (by simp at h; omega)
    have h1 : ContDiffOn ℝ (k : WithTop ℕ∞) (fderiv ℝ (pdc l u)) O :=
      ih.fderiv_of_isOpen hO (by push_cast; exact le_rfl)
    show ContDiffOn ℝ (k : WithTop ℕ∞) (fun x => fderiv ℝ (pdc l u) x (Pi.single i 1)) O
    exact h1.clm_apply contDiffOn_const

theorem pdc_diffAt {O : Set (Fin d → ℝ)} (hO : IsOpen O) {u : (Fin d → ℝ) → ℂ} {m : ℕ}
    (hu : ContDiffOn ℝ (m : WithTop ℕ∞) u O) (l : List (Fin d)) (hl : l.length + 1 ≤ m) {x : Fin d → ℝ}
    (hx : x ∈ O) : DifferentiableAt ℝ (pdc l u) x :=
  ((pdc_contDiffOn hO hu l 1 hl).differentiableOn (by norm_num)).differentiableAt (hO.mem_nhds hx)

theorem fderiv_apply_sum (f : (Fin d → ℝ) → ℂ) (x v : Fin d → ℝ) :
    fderiv ℝ f x v = ∑ i, (v i : ℂ) * fderiv ℝ f x (Pi.single i 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]

  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (Pi.single i (v i) : Fin d → ℝ) = v i • (Pi.single i 1 : Fin d → ℝ) := by
    ext j
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  rw [this, map_smul, Complex.real_smul]

theorem sum_fin_succ_fun {n : ℕ} (g : (Fin (n + 1) → Fin d) → ℂ) :
    ∑ w, g w = ∑ i : Fin d, ∑ w : Fin n → Fin d, g (Fin.cons i w) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Fin d)).sum_comp g, Fintype.sum_prod_type]
  rfl

def cD (S : SOp d) (V : (Fin d → ℝ) → (Fin d → ℝ)) (n : ℕ) (w : Fin n → Fin d) (x : Fin d → ℝ) : ℂ :=
  fderiv ℝ (ext S n w) x (V x)

def cE (S : SOp d) (V : (Fin d → ℝ) → (Fin d → ℝ)) : (n : ℕ) → (Fin n → Fin d) → (Fin d → ℝ) → ℂ
  | 0, _, _ => 0
  | n + 1, w, x => ext S n (Fin.tail w) x * ((V x (w 0) : ℝ) : ℂ)

def fieldOp (S : SOp d) (V : (Fin d → ℝ) → (Fin d → ℝ)) : SOp d :=
  ⟨S.ord + 1, fun k w x => cD S V k w x + cE S V k w x⟩

theorem cD_top (S : SOp d) (V : (Fin d → ℝ) → (Fin d → ℝ)) (w : Fin (S.ord + 1) → Fin d) (x : Fin d → ℝ) :
    cD S V (S.ord + 1) w x = 0 := by
  simp [cD, ext_top]

theorem fieldOp_app (S : SOp d) (V : (Fin d → ℝ) → (Fin d → ℝ)) (u : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) :
    (fieldOp S V).app u x = ∑ n ∈ Finset.range (S.ord + 1 + 1),
      ∑ w : Fin n → Fin d, (cD S V n w x + cE S V n w x) * pdc (List.ofFn w) u x := by
  unfold SOp.app fieldOp
  exact Fin.sum_univ_eq_sum_range
    (fun n => ∑ w : Fin n → Fin d, (cD S V n w x + cE S V n w x) * pdc (List.ofFn w) u x) (S.ord + 1 + 1)

end SymbolOperatorExtension

open SymbolOperatorExtension in
theorem symbol_operator_field_holds : SOpField := by
  intro d S V O hO hS hV
  refine ⟨fieldOp S V, rfl, ?_, ?_, ?_⟩
  · intro k w
    show ContDiffOn ℝ ∞ (fun x => cD S V k w x + cE S V k w x) O
    refine ContDiffOn.add ?_ ?_
    · exact ((ext_contDiffOn S hS k w).fderiv_of_isOpen hO (by simp)).clm_apply hV
    · rcases k with ⟨_ | n, hk⟩
      · exact contDiffOn_const
      · have hv : ContDiffOn ℝ ∞ (fun x => ((V x (w 0) : ℝ) : ℂ)) O := by
          have := Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_pi.mp hV (w 0))
          simpa [Function.comp_def] using this
        exact (ext_contDiffOn S hS n _).mul hv
  · intro u hu x hx
    have hdiff : ∀ n ∈ Finset.range (S.ord + 1), ∀ w : Fin n → Fin d,
        DifferentiableAt ℝ (ext S n w) x ∧ DifferentiableAt ℝ (pdc (List.ofFn w) u) x := by
      intro n hn w
      refine ⟨((ext_contDiffOn S hS n w).differentiableOn (by simp)).differentiableAt (hO.mem_nhds hx),
        pdc_diffAt hO hu _ ?_ hx⟩
      have := Finset.mem_range.mp hn
      simp only [List.length_ofFn]
      omega
    have key : ∀ n ∈ Finset.range (S.ord + 1),
        fderiv ℝ (fun y => ∑ w : Fin n → Fin d, ext S n w y * pdc (List.ofFn w) u y) x (V x) =
          ∑ w : Fin n → Fin d, (cD S V n w x * pdc (List.ofFn w) u x +
            ∑ i, ext S n w x * ((V x i : ℝ) : ℂ) * pdc (i :: List.ofFn w) u x) := by
      intro n hn
      rw [fderiv_fun_sum (A := fun w y => ext S n w y * pdc (List.ofFn w) u y)
        (fun w _ => (hdiff n hn w).1.mul (hdiff n hn w).2), ContinuousLinearMap.sum_apply]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [fderiv_fun_mul (hdiff n hn w).1 (hdiff n hn w).2, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, smul_eq_mul,
        fderiv_apply_sum (pdc (List.ofFn w) u), Finset.mul_sum, add_comm]
      congr 1
      · simp only [cD]; ring
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_assoc]
        rfl
    have hR : fderiv ℝ (S.app u) x (V x) = ∑ n ∈ Finset.range (S.ord + 1), ∑ w : Fin n → Fin d,
        (cD S V n w x * pdc (List.ofFn w) u x +
          ∑ i, ext S n w x * ((V x i : ℝ) : ℂ) * pdc (i :: List.ofFn w) u x) := by
      have hSu : S.app u = fun y => ∑ n ∈ Finset.range (S.ord + 1),
          ∑ w : Fin n → Fin d, ext S n w y * pdc (List.ofFn w) u y := funext (app_eq S u)
      rw [hSu, fderiv_fun_sum (A := fun n y => ∑ w : Fin n → Fin d, ext S n w y * pdc (List.ofFn w) u y)
        (fun n hn => DifferentiableAt.fun_sum (A := fun w y => ext S n w y * pdc (List.ofFn w) u y) fun w _ =>
        (hdiff n hn w).1.mul (hdiff n hn w).2), ContinuousLinearMap.sum_apply]
      exact Finset.sum_congr rfl key
    have hsplit : ∀ n, ∑ w : Fin n → Fin d, (cD S V n w x + cE S V n w x) * pdc (List.ofFn w) u x =
        ∑ w : Fin n → Fin d, cD S V n w x * pdc (List.ofFn w) u x +
          ∑ w : Fin n → Fin d, cE S V n w x * pdc (List.ofFn w) u x := by
      intro n
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun w _ => add_mul _ _ _
    have hD : ∑ n ∈ Finset.range (S.ord + 1 + 1), ∑ w : Fin n → Fin d, cD S V n w x * pdc (List.ofFn w) u x =
        ∑ n ∈ Finset.range (S.ord + 1), ∑ w : Fin n → Fin d, cD S V n w x * pdc (List.ofFn w) u x := by
      rw [Finset.sum_range_succ]
      simp [cD_top]
    have hE : ∑ n ∈ Finset.range (S.ord + 1 + 1), ∑ w : Fin n → Fin d, cE S V n w x * pdc (List.ofFn w) u x =
        ∑ n ∈ Finset.range (S.ord + 1), ∑ w : Fin n → Fin d,
          ∑ i, ext S n w x * ((V x i : ℝ) : ℂ) * pdc (i :: List.ofFn w) u x := by
      rw [Finset.sum_range_succ']
      simp only [cE, zero_mul, Finset.sum_const_zero, add_zero]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [sum_fin_succ_fun, Finset.sum_comm]
      refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun i _ => ?_
      simp only [Fin.cons_zero, Fin.tail_cons, List.ofFn_succ, Fin.cons_succ]
    rw [fieldOp_app]
    simp only [hsplit]
    rw [Finset.sum_add_distrib, hD, hE, ← Finset.sum_add_distrib]
    show _ = fderiv ℝ (S.app u) x (V x)
    rw [hR]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.sum_add_distrib]
  · intro x _ ξ
    show ∑ w : Fin (S.ord + 1) → Fin d, (∏ i, (ξ (w i) : ℂ)) * (cD S V (S.ord + 1) w x + cE S V (S.ord + 1) w x) = _
    simp only [cD_top, zero_add, cE]
    rw [sum_fin_succ_fun]
    simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.tail_cons, Fin.cons_succ]
    unfold SOp.symb
    simp only [dotProduct]
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [ext_last]
    ring

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def liftA {d o : ℕ} (a : (k : Fin (o + 1)) → (Fin k → Fin d) → (Fin d → ℝ) → ℂ) (m' : ℕ) :
    (k : Fin (m' + 1)) → (Fin k → Fin d) → (Fin d → ℝ) → ℂ :=
  fun k w x => if h : (k : ℕ) ≤ o then a ⟨k, by omega⟩ w x else 0

theorem symbol_operator_lift_holds : SOpLift := by
  intro d S m' O hle hS
  obtain ⟨o, a⟩ := S
  simp only at hle
  refine ⟨⟨m', liftA a m'⟩, rfl, ?_, ?_, ?_⟩
  · intro i w
    change ContDiffOn ℝ ∞ (liftA a m' i w) O
    by_cases h : (i : ℕ) ≤ o
    · have e : liftA a m' i w = a ⟨i, by omega⟩ w := funext fun x => dif_pos h
      rw [e]
      exact hS (⟨i, Nat.lt_succ_of_le h⟩ : Fin (o + 1)) w
    · have e : liftA a m' i w = fun _ => 0 := funext fun x => dif_neg h
      rw [e]
      exact contDiffOn_const
  · intro u x
    simp only [SOp.app]
    let F : ℕ → ℂ := fun n =>
      if h : n ≤ o then ∑ w : Fin n → Fin d, a ⟨n, by omega⟩ w x * pdc (List.ofFn w) u x else 0
    have h1 : ∑ k : Fin (m' + 1), ∑ w : Fin k → Fin d, liftA a m' k w x * pdc (List.ofFn w) u x =
        ∑ k : Fin (m' + 1), F k := by
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [F, liftA]
      split_ifs with h
      · rfl
      · simp
    have h2 : ∑ k : Fin (o + 1), ∑ w : Fin k → Fin d, a k w x * pdc (List.ofFn w) u x =
        ∑ k : Fin (o + 1), F k := by
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [F]
      rw [dif_pos (by omega)]
    rw [h1, h2, Fin.sum_univ_eq_sum_range F, Fin.sum_univ_eq_sum_range F]
    symm
    apply Finset.sum_subset
    · intro n hn
      simp only [Finset.mem_range] at hn ⊢
      omega
    · intro n hn hn'
      simp only [Finset.mem_range] at hn hn'
      simp only [F]
      rw [dif_neg (by omega)]
  · intro x ξ
    simp only [SOp.symb]
    by_cases h : o = m'
    · subst h
      rw [if_pos rfl]
      refine Finset.sum_congr rfl fun w _ => ?_
      simp only [liftA]
      rw [dif_pos (by simp)]
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun w _ => ?_
      simp only [liftA]
      rw [dif_neg (by simp; omega)]
      simp

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end
