module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.Bundle003
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PInfConv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle107
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle049
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.InfinitesimalCharacterGL.NatDegreeDefectGelf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.InfinitesimalCharacterGL.PChart
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PReproB
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.InfinitesimalCharacterGL.BridgeSt
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.MultHasCompactSupport
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.Bundle001
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.Bundle004
import GroundTheory.AutomorphicForms.RealGroups
import GroundTheory.AutomorphicForms.Bundle012
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.UniformSpace.Uniformizable

@[expose] public section

section

noncomputable section

open MeasureTheory Filter Topology
open PositivityTheory.RgBcC

namespace PositivityTheory.Rg.BcB.CG

theorem norm_cosh_le_exp (z : ℂ) : ‖Complex.cosh z‖ ≤ Real.exp ‖z‖ := by
  show ‖(Complex.exp z + Complex.exp (-z)) / 2‖ ≤ _
  have h1 : ‖Complex.exp z‖ ≤ Real.exp ‖z‖ := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.2 (le_trans (le_abs_self _) (Complex.abs_re_le_norm z))
  have h2 : ‖Complex.exp (-z)‖ ≤ Real.exp ‖z‖ := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.2 (by
      have := Complex.abs_re_le_norm z
      simp only [Complex.neg_re]
      linarith [neg_abs_le z.re])
  rw [norm_div]
  have h2' : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2']
  have := norm_add_le (Complex.exp z) (Complex.exp (-z))
  linarith

theorem sqrt_sq' (c : ℂ) : (c ^ (1 / 2 : ℂ)) ^ 2 = c := by
  have h := Complex.cpow_nat_inv_pow c (n := 2) (by norm_num)
  rw [one_div]
  push_cast at h
  exact h

theorem norm_sqrt_le (c : ℂ) : ‖c ^ (1 / 2 : ℂ)‖ ≤ 1 + ‖c‖ := by
  have h : ‖c ^ (1 / 2 : ℂ)‖ ^ 2 = ‖c‖ := by rw [← norm_pow, sqrt_sq']
  nlinarith [sq_nonneg (‖c ^ (1 / 2 : ℂ)‖ - 1), norm_nonneg (c ^ (1 / 2 : ℂ))]

theorem continuous_cosh_sqrt (t : ℂ) : Continuous fun c : ℂ => Complex.cosh (t * c ^ (1 / 2 : ℂ)) := by
  rw [Metric.continuous_iff]
  intro c₀ ε hε
  have hc : Continuous fun w : ℂ => Complex.cosh (t * w) :=
    Complex.continuous_cosh.comp (continuous_const.mul continuous_id)
  obtain ⟨δ, hδ, hδε⟩ := Metric.continuous_iff.1 hc (c₀ ^ (1 / 2 : ℂ)) ε hε
  refine ⟨δ ^ 2, by positivity, fun c hcc => ?_⟩
  have hprod : (c ^ (1 / 2 : ℂ) - c₀ ^ (1 / 2 : ℂ)) * (c ^ (1 / 2 : ℂ) + c₀ ^ (1 / 2 : ℂ)) = c - c₀ := by
    have h1 := sqrt_sq' c
    have h2 := sqrt_sq' c₀
    linear_combination h1 - h2
  have hlt : ‖c ^ (1 / 2 : ℂ) - c₀ ^ (1 / 2 : ℂ)‖ * ‖c ^ (1 / 2 : ℂ) + c₀ ^ (1 / 2 : ℂ)‖ < δ * δ := by
    rw [← norm_mul, hprod, ← dist_eq_norm, ← sq]
    exact hcc
  by_cases h : ‖c ^ (1 / 2 : ℂ) - c₀ ^ (1 / 2 : ℂ)‖ < δ
  · exact hδε _ (by rwa [dist_eq_norm])
  · have h' : ‖-c ^ (1 / 2 : ℂ) - c₀ ^ (1 / 2 : ℂ)‖ < δ := by
      push Not at h
      have he : ‖-c ^ (1 / 2 : ℂ) - c₀ ^ (1 / 2 : ℂ)‖ = ‖c ^ (1 / 2 : ℂ) + c₀ ^ (1 / 2 : ℂ)‖ := by
        rw [← norm_neg]
        ring_nf
      rw [he]
      by_contra h2
      push Not at h2
      have := mul_le_mul h h2 hδ.le (norm_nonneg _)
      linarith
    have := hδε (-c ^ (1 / 2 : ℂ)) (by rwa [dist_eq_norm])
    simpa only [mul_neg, Complex.cosh_neg] using this

theorem continuous_coshT {g : ℝ → ℝ} {T : ℝ} (hg : IsBump g T) : Continuous (coshT g) := by
  rw [continuous_iff_continuousAt]
  intro c₀
  have hgc : Continuous g := hg.1.continuous
  have hF : ∀ c : ℂ, Continuous fun t : ℝ => (g t : ℂ) * Complex.cosh (t * c ^ (1 / 2 : ℂ)) := fun c =>
    (Complex.continuous_ofReal.comp hgc).mul
      (Complex.continuous_cosh.comp (Complex.continuous_ofReal.mul continuous_const))
  have hbc : Continuous fun t : ℝ => ‖(g t : ℂ)‖ * Real.exp (|t| * (2 + ‖c₀‖)) :=
    (Complex.continuous_ofReal.comp hgc).norm.mul
      (Real.continuous_exp.comp (continuous_abs.mul continuous_const))
  have hbs : HasCompactSupport fun t : ℝ => ‖(g t : ℂ)‖ * Real.exp (|t| * (2 + ‖c₀‖)) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := -T) (b := T)) fun t ht => ?_
    have hT : T < |t| := by
      rw [Set.mem_Icc, not_and_or] at ht
      rcases ht with ht | ht
      · push Not at ht
        have := neg_abs_le t
        linarith
      · push Not at ht
        exact lt_of_lt_of_le ht (le_abs_self t)
    simp [hg.2.2 t hT]
  unfold coshT
  refine continuousAt_of_dominated (bound := fun t : ℝ => ‖(g t : ℂ)‖ * Real.exp (|t| * (2 + ‖c₀‖)))
    (Eventually.of_forall fun c => (hF c).aestronglyMeasurable) ?_ (hbc.integrable_of_hasCompactSupport hbs)
    (ae_of_all _ fun t => (continuous_const.mul (continuous_cosh_sqrt (t : ℂ))).continuousAt)
  filter_upwards [Metric.ball_mem_nhds c₀ one_pos] with c hc
  refine ae_of_all _ fun t => ?_
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine (norm_cosh_le_exp _).trans (Real.exp_le_exp.2 ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg t)
  have h1 := norm_sqrt_le c
  have h2 : ‖c‖ ≤ ‖c₀‖ + 1 := by
    have := norm_le_norm_add_norm_sub' c c₀
    rw [Metric.mem_ball, dist_eq_norm] at hc
    linarith
  linarith

theorem valCont : ValCont := by
  intro n _ μ M k val T χ χ₀ hk hχ
  obtain ⟨m, c, w, g, ks, hg, -, hval⟩ := hk
  have hv : val = fun χ => ∑ i, c i * zVal (w i) χ * coshT (g i) (cas χ) := funext hval
  rw [hv]
  have hz : ∀ l : List (Bool × ℕ), Tendsto (fun j => zVal l (χ j)) atTop (𝓝 (zVal l χ₀)) := by
    intro l
    induction l with
    | nil => simp only [zVal, List.map_nil, List.prod_nil]; exact tendsto_const_nhds
    | cons p l ih =>
      simp only [zVal, List.map_cons, List.prod_cons] at ih ⊢
      exact (hχ p.1 p.2).mul ih
  have hcas : Tendsto (fun j => cas (χ j)) atTop (𝓝 (cas χ₀)) := by
    unfold cas
    exact ((hχ true 2).add (hχ false 2)).const_mul 2
  refine tendsto_finsetSum _ fun i _ => ?_
  exact (tendsto_const_nhds.mul (hz (w i))).mul (((continuous_coshT (hg i).1).tendsto _).comp hcas)

end PositivityTheory.Rg.BcB.CG

end
end

section

noncomputable section

open Polynomial Finset NumberField GlobalTheory.CuspRep
open PositivityTheory.RgBcC.Bridge PositivityTheory.Rg.BcB.CG.InfiniteConvergence

namespace PositivityTheory.Rg.BcB.CG

namespace HeckeFubiniEvaluationDefect

theorem eval_sS (t : ℕ → ℂ) (m N : ℕ) : (sS t m N).eval (m : ℂ) = (-1) ^ N * t N := by
  rw [sS, sum_range_succ, eval_add, eval_finsetSum, sum_eq_zero]
  · simp
  · intro k hk
    have := mem_range.mp hk
    simp only [eval_mul, eval_C, eval_pow, eval_sub, eval_X, sub_self]
    rw [zero_pow (by omega), mul_zero]

theorem eq_of_defect (m : ℕ) (t t' : ℕ → ℂ) (Q : ℂ[X]) (hQ : Q.natDegree = m + 1)
    (h : ∀ N, (defect t m N Q).natDegree ≤ m) (h' : ∀ N, (defect t' m N Q).natDegree ≤ m) (k : ℕ) : t k = t' k := by
  have hQ0 : Q ≠ 0 := by intro e; rw [e, natDegree_zero] at hQ; omega
  have hS : sS t m k = sS t' m k := by
    have e : defect t m k Q - defect t' m k Q = Q * (sS t' m k - sS t m k) := by
      simp only [defect_eq]; ring
    by_contra hne
    have hD : sS t' m k - sS t m k ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have h1 : (Q * (sS t' m k - sS t m k)).natDegree ≤ m := by
      rw [← e]; exact (natDegree_sub_le _ _).trans (max_le (h k) (h' k))
    rw [natDegree_mul hQ0 hD, hQ] at h1
    omega
  have e := congrArg (fun p => p.eval (m : ℂ)) hS
  simp only [eval_sS] at e
  have hu : ((-1 : ℂ) ^ k) ≠ 0 := pow_ne_zero _ (by norm_num)
  exact mul_left_cancel₀ hu e

theorem exists_enum (s : Multiset ℂ) : ∀ n, Multiset.card s = n → ∃ r : Fin n → ℂ, Multiset.map r univ.val = s := by
  induction s using Multiset.induction_on with
  | empty =>
    intro n hn
    simp only [Multiset.card_zero] at hn
    subst hn
    exact ⟨Fin.elim0, by simp⟩
  | cons a s ih =>
    intro n hn
    rw [Multiset.card_cons] at hn
    subst hn
    obtain ⟨r, hr⟩ := ih _ rfl
    refine ⟨Fin.cons a r, ?_⟩
    conv_rhs => rw [← hr]
    simp [Fin.univ_succ, Multiset.map_map, Function.comp_def]

theorem exists_gelf (V : Type) [AddCommGroup V] [Module ℂ V] (m : ℕ) (M : Fin (m + 1) → Fin (m + 1) → Module.End ℂ V)
    (hM : Formalism.REAL.GlRel M) (v : V) (hv : v ≠ 0) (t : ℕ → ℂ) (ht : ∀ k, Formalism.REAL.etr M k v = t k • v) :
    ∃ χ : Fin (m + 1) → ℂ, ∀ k, GlobalTheory.Dec.gelfVal χ k = t k := by
  obtain ⟨f₀, hf₀⟩ : ∃ f : Module.Dual ℂ V, f v ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hv ((Module.forall_dual_apply_eq_zero_iff ℂ v).mp hc)
  set f : Module.Dual ℂ V := (f₀ v)⁻¹ • f₀ with hfd
  have hf : f v = 1 := by
    rw [hfd, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf₀]
  obtain ⟨c, hc1, hc⟩ := GlobalTheory.T.exists_monic_poly_eq_qdet (Module.End ℂ V) (m + 1) M
  set Q := GlobalTheory.CapelliNewton.polyOf (m + 1) c f v with hQd
  have hQ : ∀ u : ℂ, Q.eval u = f (Formalism.REAL.qdet M u v) := fun u => by
    rw [hQd, GlobalTheory.CapelliNewton.polyOf_eval, hc]
  have hQc : Q.coeff (m + 1) = 1 := by
    rw [hQd, GlobalTheory.CapelliNewton.polyOf_coeff, hc1]
    exact hf
  have hQn : Q.natDegree = m + 1 :=
    le_antisymm (GlobalTheory.CapelliNewton.polyOf_natDegree _ _ _ _)
      (le_natDegree_of_ne_zero (by rw [hQc]; exact one_ne_zero))
  have hQm : Q.Monic := by
    rw [Monic, leadingCoeff, hQn, hQc]
  have hcard : Multiset.card Q.roots = m + 1 := by
    rw [IsAlgClosed.card_roots_eq_natDegree, hQn]
  have hprod : (Q.roots.map fun a => X - Polynomial.C a).prod = Q :=
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq hQm (by rw [hcard, hQn])
  obtain ⟨r, hr⟩ := exists_enum Q.roots (m + 1) hcard
  refine ⟨fun s => (m : ℂ) / 2 - r s, fun k => ?_⟩
  have hcq : (∏ s, (X + Polynomial.C ((m : ℂ) / 2 - r s - (m : ℂ) / 2))) = Q := by
    conv_rhs => rw [← hprod, ← hr]
    rw [Multiset.map_map, Finset.prod_eq_multiset_prod]
    congr 1
    refine Multiset.map_congr rfl fun s _ => ?_
    simp only [Function.comp_apply, map_sub]
    ring
  have h1 : ∀ N, (defect (GlobalTheory.Dec.gelfVal fun s => (m : ℂ) / 2 - r s) m N Q).natDegree ≤ m := by
    intro N
    have := natDegree_defect_gelf m (fun s => (m : ℂ) / 2 - r s) N
    rwa [hcq] at this
  have h2 : ∀ N, (defect t m N Q).natDegree ≤ m := fun N =>
    natDegree_defect_op V m M hM v t ht f Q hQ N
  exact eq_of_defect m _ t Q hQn h1 h2 k

theorem one_mem_GLs' {a : ℕ} : (1 : Matrix (Fin a) (Fin a) ℂ) ∈ PositivityTheory.RgBcC.GLs a := by
  simp [PositivityTheory.RgBcC.GLs]

end HeckeFubiniEvaluationDefect

open HeckeFubiniEvaluationDefect in
theorem infEx : InfEx := by
  intro E _ _ _ n S v t ⟨φ, hφS, hφ0⟩ h
  have hs : ∀ s k, Formalism.REAL.etr (eopW v s) k φ = t s k • φ := by
    intro s k
    apply Subtype.ext
    funext g
    have h1 := h φ hφS g s k 1 one_mem_GLs'
    rw [gel_along v g s k φ one_mem_GLs', along_one, along_one] at h1
    rw [Submodule.coe_smul, Pi.smul_apply]
    exact h1
  rcases n with _ | m
  · refine ⟨fun _ => Fin.elim0, fun s k => ?_⟩
    have ht0 : t s k = 0 := by
      have e : t s k • φ = 0 := by rw [← hs s k]; simp [Formalism.REAL.etr]
      exact (smul_eq_zero.mp e).resolve_right hφ0
    rw [ht0]
    simp [GlobalTheory.Dec.gelfVal]
  · have hgl : ∀ s, Formalism.REAL.GlRel (eopW (E := E) (a := m + 1) v s) := by
      intro s
      unfold eopW
      split <;> exact glRel_Eop _
    choose χ hχ using fun s => exists_gelf (Sm E (m + 1)) m (eopW v s) (hgl s) φ hφ0 (t s) (hs s)
    exact ⟨χ, fun s k => hχ s k⟩

end PositivityTheory.Rg.BcB.CG

end
end

section

noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)
open scoped ContDiff ComplexConjugate InnerProductSpace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace PositivityTheory.Rg.BcB.CG.ReproL

open Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

instance scUN (N : ℕ) : SecondCountableTopology (UN N) :=
  (Topology.IsEmbedding.subtypeVal (p := fun x => x ∈ Matrix.unitaryGroup (Fin N) ℂ)).secondCountableTopology

theorem one_mem_GLs' : (1 : Mat N) ∈ GLs N := by simp [GLs]

theorem local_repro (hK : KerEx) (hM : MultAlg) (hB : Bridge.BridgeSt) (W : Submodule ℂ (Kinf E N → ℂ))
    (hW : FiniteDimensional ℂ W) (R : ℝ) (v : InfinitePlace E) [MeasurableSpace (G N)] [BorelSpace (G N)]
    (μ0 : Measure (G N)) [μ0.IsHaarMeasure] :
    ∃ a : G N → ℂ, Continuous a ∧ HasCompactSupport a ∧ ∀ φ : Sm E N,
      (∀ g, (fun k : Kinf E N => φ.1 (g * infGL E N (Unitary.toUnits k))) ∈ W) →
      PositivityTheory.Rg.BcB.SpectralAccumulation.InfBdd R (Submodule.span ℂ {φ}) →
      ∃ s : ℂ, 1 / 2 ≤ ‖s‖ ∧ ∀ g : GA E N, ∫ t, a t * φ.1 (g * infP N (Pi.mulSingle v t)) ∂μ0 = s * φ.1 g := by
  obtain ⟨g, T, hT, hg, hval⟩ := exists_bump N R
  obtain ⟨c0, hc0⟩ := hK N
  obtain ⟨k, hk⟩ := (hc0 μ0 (Mv W hW v)).1 [] g T hg
  have hmult : IsMult μ0 (Mv W hW v) k (fun χ => coshT g (cas χ)) T :=
    ⟨1, fun _ => 1, fun _ => [], fun _ => g, fun _ => k, fun _ => ⟨hg, hk⟩, fun y _ => by simp,
      fun χ => by simp [zVal]⟩
  have hact := (hM N μ0 (Mv W hW v) k k _ _ T T hmult hmult).2.2.2
  have : CompleteSpace (Mv W hW v).V := FiniteDimensional.complete ℂ _
  set b : G N → (Mv W hW v).V := fun y =>
    (InnerProductSpace.toDual ℂ (Mv W hW v).V).symm ((evL W hW v 1).comp (k y.val)) with hbdef
  have hb : ∀ y w, ⟪b y, w⟫_ℂ = toFun W v (k y.val w) 1 := fun y w => by
    rw [hbdef, InnerProductSpace.toDual_symm_apply]; rfl
  have hbc : Continuous b :=
    (InnerProductSpace.toDual ℂ (Mv W hW v).V).symm.continuous.comp
      ((ContinuousLinearMap.compL ℂ _ _ ℂ (evL W hW v 1)).continuous.comp (mult_continuous hmult))
  set c : G N → UN N → ℂ := fun y u => conj (toFun W v (b y) u) with hcdef
  have hcc : Continuous (Function.uncurry c) :=
    Complex.continuous_conj.comp ((continuous_toFun₂ W hW v).comp ((hbc.comp continuous_fst).prodMk continuous_snd))
  set Kc := tsupport fun y : G N => k y.val with hKcdef
  have hKc : IsCompact Kc := mult_hasCompactSupport hmult
  have hk0 : ∀ y, y ∉ Kc → k y.val = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport (f := fun y : G N => k y.val) hy
  have hcK : ∀ y u, y ∉ Kc → c y u = 0 := by
    intro y u hy
    have hb0 : b y = 0 := by simp [hbdef, hk0 y hy]
    have ht : toFun W v (b y) = 0 := by rw [hb0]; exact (toFun W v).map_zero
    simp [hcdef, ht]
  set ι : UN N → G N := fun u => Unitary.toUnits u with hιdef
  have hι : Continuous ι := continuous_toUnitsU N
  set Ku : Subgroup (G N) := (Unitary.toUnits (R := Mat N)).range with hKudef
  have hKu : IsCompact (Ku : Set (G N)) := by
    have : (Ku : Set (G N)) = Set.range ι := by ext x; simp [Ku, ι]
    rw [this]; exact isCompact_range hι
  have hιK : ∀ u, ι u ∈ Ku := fun u => ⟨u, rfl⟩
  obtain ⟨ha1, ha2⟩ := avg_cont_supp (nuN N) Ku hKu ι hι hιK c hcc Kc hKc hcK
  refine ⟨_, ha1, ha2, ?_⟩
  intro φ hφ hR
  obtain ⟨χ, hχb, hχ⟩ := exists_chi hB R v φ hR
  refine ⟨coshT g (cas χ), hval χ hχb, fun g0 => ?_⟩
  set F := sec W hW v φ.1 φ.2 hφ g0 with hFdef
  have hF := sec_mem_CE W hW v φ.1 φ.2 hφ g0
  have hE := sec_isEig W hW v φ.1 φ.2 hφ g0 χ (hχ g0)
  have h1 := hact χ F hF hE 1 one_mem_GLs'
  set h : G N → ℂ := fun t => φ.1 (g0 * infP N (Pi.mulSingle v t)) with hhdef
  have hh : Continuous h := continuous_along_infP v g0 φ.1 φ.2
  have hFc : Continuous fun y : G N => F y.val :=
    hF.1.continuousOn.comp_continuous Units.continuous_val val_mem_GLs
  have hint : Integrable (fun y : G N => k y.val (F (1 * y.val))) μ0 := by
    simp only [one_mul]
    refine Continuous.integrable_of_hasCompactSupport ((mult_continuous hmult).clm_apply hFc) ?_
    exact HasCompactSupport.intro hKc fun y hy => by simp [hk0 y hy]
  have h2 := congrArg (evL W hW v 1) h1
  simp only [PositivityTheory.RgBcC.act] at h2
  rw [← ContinuousLinearMap.integral_comp_comm _ hint] at h2
  have hL : ∀ y : G N, evL W hW v 1 (k y.val (F (1 * y.val))) = ∫ u, c y u * h (y * ι u) ∂nuN N := by
    intro y
    rw [one_mul, evL_apply, ← hb]
    refine (inner_eq W v (b y) (F y.val)).trans (integral_congr_ae (Filter.Eventually.of_forall fun u => ?_))
    simp only [hcdef, hhdef]
    rw [toFun_sec W hW v φ.1 φ.2 hφ g0 (val_mem_GLs y) u]
    congr 1
    rw [show y.val * u.1 = (y * ι u).val from rfl, along_val]
  have hRHS : evL W hW v 1 (coshT g (cas χ) • F 1) = coshT g (cas χ) * φ.1 g0 := by
    rw [map_smul, evL_apply, toFun_sec W hW v φ.1 φ.2 hφ g0 one_mem_GLs' 1, smul_eq_mul]
    congr 1
    simpa using along_one' v g0 φ.1
  simp_rw [hL] at h2
  rw [hRHS] at h2
  rw [← h2, swap_right μ0 (nuN N) Ku hKu ι hι hιK c hcc Kc hKc hcK h hh]

end PositivityTheory.Rg.BcB.CG.ReproL
end
end
