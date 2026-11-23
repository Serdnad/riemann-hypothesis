module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle002
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle007
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle012
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle005
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle009
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.GlobCore
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle010
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle003
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle008
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle004
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle006

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix Set Filter Topology MvPolynomial

namespace PositivityTheory.Rg.Sw.AbsSt.SDM

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.AbsSt.DF

variable {m n : ℕ}

theorem aE_eq (H : Matrix (Fin n) (Fin n) ℂ) (σ : ℝ) : aE H σ = NormedSpace.exp (σ • H) := by
  unfold aE; rw [Complex.coe_smul]

theorem hasDerivAt_aE_entry (H : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (i j : Fin n) :
    HasDerivAt (fun σ : ℝ => aE H σ i j) ((aE H s * H) i j) s := by
  simp only [aE_eq]
  open scoped Matrix.Norms.Operator in
  exact ((Matrix.entryLinearMap ℝ ℂ i j).toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt s
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) H s)

theorem mulR_mul (A B : Matrix (Fin n) (Fin n) ℂ) (y : Fin m → Fin n → ℂ) :
    mulR B (mulR A y) = mulR (A * B) y := by
  funext a j
  simp only [mulR, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

theorem mulR_one (y : Fin m → Fin n → ℂ) : mulR (1 : Matrix (Fin n) (Fin n) ℂ) y = y := by
  funext a j
  simp [mulR, Matrix.one_apply]

theorem hasDerivAt_mulR (H : Matrix (Fin n) (Fin n) ℂ) (y : Fin m → Fin n → ℂ) (s : ℝ) (a : Fin m) (j : Fin n) :
    HasDerivAt (fun σ : ℝ => mulR (aE H σ) y a j) (mulR H (mulR (aE H s) y) a j) s := by
  have h : HasDerivAt (fun σ : ℝ => ∑ i, y a i * aE H σ i j) (∑ i, y a i * (aE H s * H) i j) s :=
    HasDerivAt.fun_sum fun i _ => (hasDerivAt_aE_entry H s i j).const_mul (y a i)
  have e : ∑ i, y a i * (aE H s * H) i j = mulR H (mulR (aE H s) y) a j := by
    rw [mulR_mul]; rfl
  exact e ▸ h

theorem hasDerivAt_ept (H : Matrix (Fin n) (Fin n) ℂ) (y : Fin m → Fin n → ℂ) (s : ℝ) (k : Fin m × Fin n × Bool) :
    HasDerivAt (fun σ : ℝ => ept (mulR (aE H σ) y) k) (ept (mulR H (mulR (aE H s) y)) k) s := by
  rcases k with ⟨a, j, b⟩
  cases b
  · exact hasDerivAt_mulR H y s a j
  · exact (hasDerivAt_mulR H y s a j).star

theorem evX_eulH (H : Matrix (Fin n) (Fin n) ℂ) (R : PX m n) (z : Fin m → Fin n → ℂ) :
    evX (eulH H R) z = ∑ k, MvPolynomial.eval (ept z) (pderiv k R) * ept (mulR H z) k := by

  simp only [eulH, evX_eq, map_sum, map_add (f := _), map_mul, eval_X, eval_C]
  rw [Fintype.sum_prod_type, Finset.sum_congr rfl fun a _ => Fintype.sum_prod_type _]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool]
  simp only [ept, mulR, if_true, Bool.false_eq_true, if_false, star_sum, star_mul']
  ring_nf

def trHQ (ε : Fin m → Bool) (H : Matrix (Fin n) (Fin n) ℂ) : PX m n :=
  ∑ i, ∑ j, MvPolynomial.C (H i j) * (Qb ε true j i + Qb ε false j i)

theorem evX_Qb_add (ε : Fin m → Bool) (z : Fin m → Fin n → ℂ) (i j : Fin n) :
    evX (Qb ε true i j + Qb ε false i j) z = ∑ a, star (z a i) * z a j := by

  simp only [Qb, evX_eq, map_add (f := _), map_sum, map_mul, eval_X, ept, if_true, Bool.false_eq_true, if_false]
  convert Finset.sum_filter_add_sum_filter_not Finset.univ (fun x => ε x = true) (fun x => star (z x i) * z x j) using 3
  ext x; simp

theorem evX_trHQ (ε : Fin m → Bool) (H : Matrix (Fin n) (Fin n) ℂ) (z : Fin m → Fin n → ℂ) :
    evX (trHQ ε H) z = ∑ a, ∑ j, star (z a j) * mulR H z a j := by
  have e : evX (trHQ ε H) z = ∑ i, ∑ j, H i j * evX (Qb ε true j i + Qb ε false j i) z := by

    simp only [trHQ, evX_eq, map_sum, map_mul, eval_C]
  rw [e]
  simp only [evX_Qb_add, mulR, Finset.mul_sum]
  calc ∑ i, ∑ j, ∑ a, H i j * (star (z a j) * z a i) = ∑ j, ∑ i, ∑ a, H i j * (star (z a j) * z a i) :=
        Finset.sum_comm
    _ = ∑ j, ∑ a, ∑ i, H i j * (star (z a j) * z a i) := Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ a, ∑ j, ∑ i, H i j * (star (z a j) * z a i) := Finset.sum_comm
    _ = ∑ a, ∑ j, ∑ i, star (z a j) * (z a i * H i j) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

theorem trHQ_real (ε : Fin m → Bool) {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (z : Fin m → Fin n → ℂ) :
    (evX (trHQ ε H) z).im = 0 := by
  have hij : ∀ i j, star (H i j) = H j i := fun i j => by
    have := congrFun (congrFun hH j) i
    simpa [Matrix.conjTranspose_apply] using this
  have hconj : star (evX (trHQ ε H) z) = evX (trHQ ε H) z := by
    rw [evX_trHQ]
    simp only [mulR, star_sum, star_mul', star_star, Finset.mul_sum, hij]
    refine Finset.sum_congr rfl fun a _ => ?_
    calc ∑ j, ∑ i, z a j * (star (z a i) * H j i) = ∑ i, ∑ j, z a j * (star (z a i) * H j i) := Finset.sum_comm
      _ = ∑ i, ∑ j, star (z a i) * (z a j * H j i) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have := congrArg Complex.im hconj
  simp only [Complex.star_def, Complex.conj_im] at this
  linarith

theorem hasDerivAt_normSq (w : ℝ → ℂ) (w' : ℂ) (s : ℝ) (hw : HasDerivAt w w' s) :
    HasDerivAt (fun σ => ‖w σ‖ ^ 2) (2 * (star (w s) * w').re) s := by
  have hre : HasDerivAt (fun σ => (w σ).re) w'.re s := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hw
  have him : HasDerivAt (fun σ => (w σ).im) w'.im s := Complex.imCLM.hasFDerivAt.comp_hasDerivAt s hw
  have h := (hre.pow 2).add (him.pow 2)
  have e : ∀ σ, (w σ).re ^ 2 + (w σ).im ^ 2 = ‖w σ‖ ^ 2 := fun σ => by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun σ => (e σ).symm)).congr_deriv ?_
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  push_cast
  ring

theorem hasDerivAt_gsE (c : ℝ) (ε : Fin m → Bool) {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian)
    (y : Fin m → Fin n → ℂ) (s : ℝ) :
    HasDerivAt (fun σ => gs c (mulR (aE H σ) y))
      (gs c (mulR (aE H s) y) * (-(2 * (c : ℂ)) * evX (trHQ ε H) (mulR (aE H s) y))) s := by
  have hS : HasDerivAt (fun σ => ∑ a, ∑ j, ‖mulR (aE H σ) y a j‖ ^ 2)
      (∑ a, ∑ j, 2 * (star (mulR (aE H s) y a j) * mulR H (mulR (aE H s) y) a j).re) s :=
    HasDerivAt.fun_sum fun a _ => HasDerivAt.fun_sum fun j _ => hasDerivAt_normSq _ _ s (hasDerivAt_mulR H y s a j)
  have hg := (((hS.const_mul c).ofReal_comp).neg).cexp
  set T := evX (trHQ ε H) (mulR (aE H s) y) with hTdef
  have h0 : T.im = 0 := trHQ_real ε hH _
  have hsum : (∑ a, ∑ j, 2 * (star (mulR (aE H s) y a j) * mulR H (mulR (aE H s) y) a j).re) = 2 * T.re := by
    rw [hTdef, evX_trHQ]
    simp only [Complex.re_sum, Finset.mul_sum]
  have hT' : ((T.re : ℝ) : ℂ) = T := Complex.ext (by simp) (by simp [h0])
  unfold gs
  refine hg.congr_deriv ?_
  simp only [Pi.neg_apply]
  rw [hsum]
  push_cast
  rw [hT']
  ring

end PositivityTheory.Rg.Sw.AbsSt.SDM
end
end

section

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.Far

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {m n : ℕ} {ε : Fin m → Bool} {c t : ℝ} {p q : ℕ} {e : ℤ} {sL : PX m n →ₗ[ℂ] (GR n → ℂ)}
  {ρ : GR n → PX m n →ₗ[ℂ] PX m n}
  {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0}
  {sec I : PX m n →ₗ[ℂ] (G → ℂ)} {Λ : Set ((G → ℂ) → ℂ)}

theorem hz_bound (hD : CayleyBlocksInvertible) (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ) {Q : PX m n} {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, ‖sec Q x‖ ≤ C * ‖sec 1 x‖) {σ₁ σ₂ : ℝ} {z : ℂ} (h₁ : σ₁ ≤ z.re) (h₂ : z.re ≤ σ₂) (x : G) :
    ‖hz Ht sec s₀ z Q x‖ ≤ C * (‖hz Ht sec s₀ (σ₁ : ℂ) 1 x‖ + ‖hz Ht sec s₀ (σ₂ : ℂ) 1 x‖) := by
  rw [norm_hz hD hG, norm_hz hD hG, norm_hz hD hG, Complex.ofReal_re, Complex.ofReal_re]
  have hx := Ht_pos hD hG x
  have hr := rpow_le_add hx (show σ₁ - s₀.re ≤ z.re - s₀.re by linarith) (show z.re - s₀.re ≤ σ₂ - s₀.re by linarith)
  calc (Ht x : ℝ) ^ (z.re - s₀.re) * ‖sec Q x‖
      ≤ ((Ht x : ℝ) ^ (σ₁ - s₀.re) + (Ht x : ℝ) ^ (σ₂ - s₀.re)) * (C * ‖sec 1 x‖) :=
        mul_le_mul hr (hC x) (norm_nonneg _) (by positivity)
    _ = C * ((Ht x : ℝ) ^ (σ₁ - s₀.re) * ‖sec 1 x‖ + (Ht x : ℝ) ^ (σ₂ - s₀.re) * ‖sec 1 x‖) := by ring

theorem hz_bound0 (hD : CayleyBlocksInvertible) (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ) {Q : PX m n} {C : ℝ}
    (hC : ∀ x, ‖sec Q x‖ ≤ C * ‖sec 1 x‖) (z : ℂ) (x : G) :
    ‖hz Ht sec s₀ z Q x‖ ≤ C * ‖hz Ht sec s₀ z 1 x‖ := by
  rw [norm_hz hD hG, norm_hz hD hG]
  calc (Ht x : ℝ) ^ (z.re - s₀.re) * ‖sec Q x‖ ≤ (Ht x : ℝ) ^ (z.re - s₀.re) * (C * ‖sec 1 x‖) :=
        mul_le_mul_of_nonneg_left (hC x) (Real.rpow_nonneg (Ht_pos hD hG x).le _)
    _ = C * ((Ht x : ℝ) ^ (z.re - s₀.re) * ‖sec 1 x‖) := by ring

theorem farHol (hI : Iwa) (hM : Mult) (hD : CayleyBlocksInvertible) (hL : LocData ε c t p q e sL ρ)
    (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ) : ∃ σ : ℝ,
    (∀ Q g, DifferentiableOn ℂ (fun z => GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z Q) g) (GlobalTheory.Cont.rightOf σ)) ∧
    (∀ Q g (z : ℂ), σ < z.re → Summable fun q => GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z Q) g q) ∧
    (∀ z : ℂ, σ < z.re → ∀ C : Set G, IsCompact C → ∃ u : GlobalTheory.Eis.Cosets Pp Γ → ℝ, Summable u ∧
      ∀ g ∈ C, ∀ q', ‖GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z 1) g q'‖ ≤ u q') := by
  obtain ⟨U, d, E, σ, -, -, -, -, -, -, -, hconv⟩ := hG.eis
  have hmaj : ∀ z : ℂ, σ < z.re → ∀ C : Set G, IsCompact C → ∃ u : GlobalTheory.Eis.Cosets Pp Γ → ℝ, Summable u ∧
      ∀ g ∈ C, ∀ q', ‖GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z 1) g q'‖ ≤ u q' :=
    fun z hzr C hC => (hconv z hzr).1 C hC
  refine ⟨σ, ?_, ?_, hmaj⟩
  · intro Q g z₀ hz₀
    have hz₀' : σ < z₀.re := hz₀
    obtain ⟨C, hC0, hC⟩ := sec_bound hI hM hD hL hG Q
    set σ₁ : ℝ := (σ + z₀.re) / 2
    set σ₂ : ℝ := z₀.re + 1
    have hσ₁ : σ < ((σ₁ : ℂ)).re := by simp only [Complex.ofReal_re, σ₁]; linarith
    have hσ₂ : σ < ((σ₂ : ℂ)).re := by simp only [Complex.ofReal_re, σ₂]; linarith
    obtain ⟨u₁, hu₁, hb₁⟩ := hmaj _ hσ₁ {g} isCompact_singleton
    obtain ⟨u₂, hu₂, hb₂⟩ := hmaj _ hσ₂ {g} isCompact_singleton
    set V : Set ℂ := {z | σ₁ < z.re ∧ z.re < σ₂}
    have hV : IsOpen V := (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
    have hz₀V : z₀ ∈ V := ⟨by simp only [σ₁]; linarith, by simp only [σ₂]; linarith⟩
    have hdiff : DifferentiableOn ℂ (fun w => ∑' q', GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ w Q) g q') V := by
      refine Complex.differentiableOn_tsum_of_summable_norm ((hu₁.add hu₂).mul_left C) (fun q' => ?_) hV
        (fun q' w hw => ?_)
      · have hne : (((Ht (((q'.out : Γ) : G) * g) : ℝ) : ℂ)) ≠ 0 :=
          Complex.ofReal_ne_zero.mpr (Ht_pos hD hG _).ne'
        exact (((differentiable_id.sub_const s₀).const_cpow (Or.inl hne)).mul_const _).differentiableOn
      · have h := hz_bound hD hG hC0 hC (σ₁ := σ₁) (σ₂ := σ₂) (z := w) hw.1.le hw.2.le (((q'.out : Γ) : G) * g)
        calc ‖GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ w Q) g q'‖ ≤ C * (‖GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ (σ₁ : ℂ) 1) g q'‖ +
              ‖GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ (σ₂ : ℂ) 1) g q'‖) := h
          _ ≤ C * (u₁ q' + u₂ q') := mul_le_mul_of_nonneg_left
              (add_le_add (hb₁ g (mem_singleton g) q') (hb₂ g (mem_singleton g) q')) hC0
          _ = (fun q' => C * (u₁ q' + u₂ q')) q' := rfl
    exact (hdiff.differentiableAt (hV.mem_nhds hz₀V)).differentiableWithinAt
  · intro Q g z hzr
    obtain ⟨C, hC0, hC⟩ := sec_bound hI hM hD hL hG Q
    obtain ⟨u, hu, hb⟩ := hmaj z hzr {g} isCompact_singleton
    refine Summable.of_norm_bounded (hu.mul_left C) fun q' => ?_
    calc ‖GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z Q) g q'‖ ≤ C * ‖GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z 1) g q'‖ :=
          hz_bound0 hD hG hC z _
      _ ≤ C * u q' := mul_le_mul_of_nonneg_left (hb g (mem_singleton g) q') hC0

end PositivityTheory.Rg.Sw.AbsSt.Far
end
end

section

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.FarK

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.AbsSt.Far

variable {m n : ℕ} {ε : Fin m → Bool} {c t : ℝ} {p q : ℕ} {e : ℤ} {sL : PX m n →ₗ[ℂ] (GR n → ℂ)}
  {ρ : GR n → PX m n →ₗ[ℂ] PX m n}
  {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0}
  {sec I : PX m n →ₗ[ℂ] (G → ℂ)}

theorem hz_bound (hD : CayleyBlocksInvertible) (hG : GlobCore ε c sL ρ G Pp Γ ι s₀ Ht sec I) {Q : PX m n} {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, ‖sec Q x‖ ≤ C * ‖sec 1 x‖) {σ₁ σ₂ : ℝ} {z : ℂ} (h₁ : σ₁ ≤ z.re) (h₂ : z.re ≤ σ₂) (x : G) :
    ‖hz Ht sec s₀ z Q x‖ ≤ C * (‖hz Ht sec s₀ (σ₁ : ℂ) 1 x‖ + ‖hz Ht sec s₀ (σ₂ : ℂ) 1 x‖) := by
  rw [norm_hz hD hG, norm_hz hD hG, norm_hz hD hG, Complex.ofReal_re, Complex.ofReal_re]
  have hx := Ht_pos hD hG x
  have hr := rpow_le_add hx (show σ₁ - s₀.re ≤ z.re - s₀.re by linarith) (show z.re - s₀.re ≤ σ₂ - s₀.re by linarith)
  calc (Ht x : ℝ) ^ (z.re - s₀.re) * ‖sec Q x‖
      ≤ ((Ht x : ℝ) ^ (σ₁ - s₀.re) + (Ht x : ℝ) ^ (σ₂ - s₀.re)) * (C * ‖sec 1 x‖) :=
        mul_le_mul hr (hC x) (norm_nonneg _) (by positivity)
    _ = C * ((Ht x : ℝ) ^ (σ₁ - s₀.re) * ‖sec 1 x‖ + (Ht x : ℝ) ^ (σ₂ - s₀.re) * ‖sec 1 x‖) := by ring

theorem hz_bound0 (hD : CayleyBlocksInvertible) (hG : GlobCore ε c sL ρ G Pp Γ ι s₀ Ht sec I) {Q : PX m n} {C : ℝ}
    (hC : ∀ x, ‖sec Q x‖ ≤ C * ‖sec 1 x‖) (z : ℂ) (x : G) :
    ‖hz Ht sec s₀ z Q x‖ ≤ C * ‖hz Ht sec s₀ z 1 x‖ := by
  rw [norm_hz hD hG, norm_hz hD hG]
  calc (Ht x : ℝ) ^ (z.re - s₀.re) * ‖sec Q x‖ ≤ (Ht x : ℝ) ^ (z.re - s₀.re) * (C * ‖sec 1 x‖) :=
        mul_le_mul_of_nonneg_left (hC x) (Real.rpow_nonneg (Ht_pos hD hG x).le _)
    _ = C * ((Ht x : ℝ) ^ (z.re - s₀.re) * ‖sec 1 x‖) := by ring

theorem farHol (hI : Iwa) (hM : Mult) (hD : CayleyBlocksInvertible) (hL : LocData ε c t p q e sL ρ)
    (hG : GlobCore ε c sL ρ G Pp Γ ι s₀ Ht sec I) : ∃ σ : ℝ,
    (∀ Q g, DifferentiableOn ℂ (fun z => GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z Q) g) (GlobalTheory.Cont.rightOf σ)) ∧
    (∀ Q g (z : ℂ), σ < z.re → Summable fun q => GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z Q) g q) ∧
    (∀ z : ℂ, σ < z.re → ∀ C : Set G, IsCompact C → ∃ u : GlobalTheory.Eis.Cosets Pp Γ → ℝ, Summable u ∧
      ∀ g ∈ C, ∀ q', ‖GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z 1) g q'‖ ≤ u q') := by
  obtain ⟨U, d, E, σ, -, -, -, -, -, -, -, hconv⟩ := hG.eis
  have hmaj : ∀ z : ℂ, σ < z.re → ∀ C : Set G, IsCompact C → ∃ u : GlobalTheory.Eis.Cosets Pp Γ → ℝ, Summable u ∧
      ∀ g ∈ C, ∀ q', ‖GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z 1) g q'‖ ≤ u q' :=
    fun z hzr C hC => (hconv z hzr).1 C hC
  refine ⟨σ, ?_, ?_, hmaj⟩
  · intro Q g z₀ hz₀
    have hz₀' : σ < z₀.re := hz₀
    obtain ⟨C, hC0, hC⟩ := sec_bound hI hM hD hL hG Q
    set σ₁ : ℝ := (σ + z₀.re) / 2
    set σ₂ : ℝ := z₀.re + 1
    have hσ₁ : σ < ((σ₁ : ℂ)).re := by simp only [Complex.ofReal_re, σ₁]; linarith
    have hσ₂ : σ < ((σ₂ : ℂ)).re := by simp only [Complex.ofReal_re, σ₂]; linarith
    obtain ⟨u₁, hu₁, hb₁⟩ := hmaj _ hσ₁ {g} isCompact_singleton
    obtain ⟨u₂, hu₂, hb₂⟩ := hmaj _ hσ₂ {g} isCompact_singleton
    set V : Set ℂ := {z | σ₁ < z.re ∧ z.re < σ₂}
    have hV : IsOpen V := (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
    have hz₀V : z₀ ∈ V := ⟨by simp only [σ₁]; linarith, by simp only [σ₂]; linarith⟩
    have hdiff : DifferentiableOn ℂ (fun w => ∑' q', GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ w Q) g q') V := by
      refine Complex.differentiableOn_tsum_of_summable_norm ((hu₁.add hu₂).mul_left C) (fun q' => ?_) hV
        (fun q' w hw => ?_)
      · have hne : (((Ht (((q'.out : Γ) : G) * g) : ℝ) : ℂ)) ≠ 0 :=
          Complex.ofReal_ne_zero.mpr (Ht_pos hD hG _).ne'
        exact (((differentiable_id.sub_const s₀).const_cpow (Or.inl hne)).mul_const _).differentiableOn
      · have h := hz_bound hD hG hC0 hC (σ₁ := σ₁) (σ₂ := σ₂) (z := w) hw.1.le hw.2.le (((q'.out : Γ) : G) * g)
        calc ‖GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ w Q) g q'‖ ≤ C * (‖GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ (σ₁ : ℂ) 1) g q'‖ +
              ‖GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ (σ₂ : ℂ) 1) g q'‖) := h
          _ ≤ C * (u₁ q' + u₂ q') := mul_le_mul_of_nonneg_left
              (add_le_add (hb₁ g (mem_singleton g) q') (hb₂ g (mem_singleton g) q')) hC0
          _ = (fun q' => C * (u₁ q' + u₂ q')) q' := rfl
    exact (hdiff.differentiableAt (hV.mem_nhds hz₀V)).differentiableWithinAt
  · intro Q g z hzr
    obtain ⟨C, hC0, hC⟩ := sec_bound hI hM hD hL hG Q
    obtain ⟨u, hu, hb⟩ := hmaj z hzr {g} isCompact_singleton
    refine Summable.of_norm_bounded (hu.mul_left C) fun q' => ?_
    calc ‖GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z Q) g q'‖ ≤ C * ‖GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z 1) g q'‖ :=
          hz_bound0 hD hG hC z _
      _ ≤ C * u q' := mul_le_mul_of_nonneg_left (hb g (mem_singleton g) q') hC0

end PositivityTheory.Rg.Sw.AbsSt.FarK
end
end

section

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

theorem helpA : HelpA :=
  ⟨fun _ X => ⟨aD X, isDil_aD X⟩, fun _ X s a a' h h' => isDil_unique X s a a' h h', fun _ => isCompact_KR,
    fun _ h => ⟨automorphy_first_det_ne_zero h, automorphy_second_det_ne_zero h⟩, fun _ p q e X a ha h s => holomorphic_section_extension_eq p q e X a ha h s,
    fun _ p q e X S hS => holomorphic_section_extension_exists p q e X S hS,
    fun _ p q e => ⟨(spherical_section_continuous_ne_zero p q e).1, fun k _ => (spherical_section_continuous_ne_zero p q e).2 k⟩⟩

end PositivityTheory.Rg.Sw.AbsSt
end

section

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal ComplexOrder

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw LocOpA

variable {n : ℕ}

def fLoc (p q : ℕ) (e : ℤ) (A B : GR n) (ψ : (Fin n → Fin n → ℝ) → ℂ) (y : KR n × (Fin n → Fin n → ℝ)) (w : ℂ) : ℂ :=
  (F0 p q e (y.1 : GR n))⁻¹ * (((hLoc ((y.1 : GR n) * A * nbEl y.2 * B) : ℂ) ^ w *
    F0 p q e ((y.1 : GR n) * A * nbEl y.2 * B)) * ψ y.2)

theorem continuous_fLoc (p q : ℕ) (e : ℤ) (A B : GR n) {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψ : Continuous ψ) :
    Continuous (fun y : (KR n × (Fin n → Fin n → ℝ)) × ℂ => fLoc p q e A B ψ y.1 y.2) := by
  have hg : Continuous (fun y : (KR n × (Fin n → Fin n → ℝ)) × ℂ => ((y.1.1 : GR n) * A * nbEl y.1.2 * B)) :=
    (((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).mul continuous_const).mul
      (continuous_nbEl.comp (continuous_snd.comp continuous_fst))).mul continuous_const
  unfold fLoc
  refine (((continuous_weight_factor p q e).comp (continuous_subtype_val.comp (continuous_fst.comp continuous_fst))).inv₀
    (fun _ => weight_factor_ne_zero _ _ _ _)).mul ?_
  refine ((Continuous.cpow ?_ continuous_snd ?_).mul ((continuous_weight_factor p q e).comp hg)).mul
    (hψ.comp (continuous_snd.comp continuous_fst))
  · exact Complex.continuous_ofReal.comp (continuous_hLoc.comp hg)
  · intro y
    exact Complex.ofReal_mem_slitPlane.2 (hLoc_pos _)

theorem continuous_fLoc_w (p q : ℕ) (e : ℤ) (A B : GR n) {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψ : Continuous ψ) (w : ℂ) :
    Continuous (fun y : KR n × (Fin n → Fin n → ℝ) => fLoc p q e A B ψ y w) := by
  have h1 := continuous_fLoc p q e A B hψ
  have h2 : Continuous (fun y : KR n × (Fin n → Fin n → ℝ) => ((y, w) : (KR n × (Fin n → Fin n → ℝ)) × ℂ)) :=
    continuous_id.prodMk continuous_const
  have h3 := h1.comp h2
  exact h3

theorem cz_eq (p q : ℕ) (e : ℤ) (A B : GR n) {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψ : IsSingTest ψ)
    [MeasurableSpace (KR n)] [BorelSpace (KR n)] (μ : Measure (KR n)) [IsProbabilityMeasure μ] (w : ℂ) :
    czLoc p q e A B ψ μ w =
      ∫ y, fLoc p q e A B ψ y w ∂((μ.prod volume).restrict (univ ×ˢ tsupport ψ)) := by
  have hK : IsCompact ((univ : Set (KR n)) ×ˢ tsupport ψ) := isCompact_univ.prod hψ.2.1
  have hint : Integrable (fun y => fLoc p q e A B ψ y w) ((μ.prod volume).restrict (univ ×ˢ tsupport ψ)) :=
    ((continuous_fLoc_w p q e A B hψ.1 w).continuousOn).integrableOn_compact hK
  rw [← Measure.prod_restrict, Measure.restrict_univ] at hint ⊢
  rw [integral_prod _ hint]
  unfold czLoc jLoc
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp only [fLoc]
  rw [integral_const_mul]
  congr 1
  symm
  refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_)
  have h0 : ψ x = 0 := by
    by_contra h
    exact hx (subset_tsupport ψ (Function.mem_support.2 h))
  simp [h0]

theorem cz_diff (hH : HolParam) (p q : ℕ) (e : ℤ) (A B : GR n) {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψ : IsSingTest ψ)
    [MeasurableSpace (KR n)] [BorelSpace (KR n)] (μ : Measure (KR n)) [IsProbabilityMeasure μ] :
    Differentiable ℂ (czLoc p q e A B ψ μ) := by
  have hK : IsCompact ((univ : Set (KR n)) ×ˢ tsupport ψ) := isCompact_univ.prod hψ.2.1
  have hmeas : MeasurableSet ((univ : Set (KR n)) ×ˢ tsupport ψ) :=
    MeasurableSet.univ.prod (isClosed_tsupport ψ).measurableSet
  haveI : IsFiniteMeasure ((μ.prod volume).restrict ((univ : Set (KR n)) ×ˢ tsupport ψ)) :=
    ⟨by
      rw [Measure.restrict_apply_univ, Measure.prod_prod]
      exact ENNReal.mul_lt_top (measure_lt_top _ _) hψ.2.1.measure_lt_top⟩
  have hnull : ((μ.prod volume).restrict ((univ : Set (KR n)) ×ˢ tsupport ψ))
      ((univ : Set (KR n)) ×ˢ tsupport ψ)ᶜ = 0 := by
    rw [Measure.restrict_apply' hmeas, compl_inter_self, measure_empty]
  have hcont := (continuous_fLoc p q e A B hψ.1).continuousOn (s := ((univ : Set (KR n)) ×ˢ tsupport ψ) ×ˢ (univ : Set ℂ))
  have hdiff : ∀ y ∈ ((univ : Set (KR n)) ×ˢ tsupport ψ),
      DifferentiableOn ℂ (fun w => fLoc p q e A B ψ y w) univ := by
    intro y _
    refine Differentiable.differentiableOn ?_
    unfold fLoc
    refine Differentiable.const_mul ?_ _
    refine Differentiable.mul_const ?_ _
    refine Differentiable.mul_const ?_ _
    refine Differentiable.const_cpow differentiable_id (Or.inl ?_)
    exact_mod_cast (hLoc_pos _).ne'
  have h := (hH (KR n × (Fin n → Fin n → ℝ)) ((μ.prod volume).restrict ((univ : Set (KR n)) ×ˢ tsupport ψ))
    _ hK hnull univ (fun y w => fLoc p q e A B ψ y w) isOpen_univ hcont hdiff).1
  have heq : czLoc p q e A B ψ μ = fun w =>
      ∫ y, fLoc p q e A B ψ y w ∂((μ.prod volume).restrict (univ ×ˢ tsupport ψ)) :=
    funext (cz_eq p q e A B hψ μ)
  rw [heq]
  exact differentiableOn_univ.1 h


theorem locOp : LV → Iwa → Mult → HolParam → LocOp := by
  intro hLV hIwa hMult hHol n p q e hgood _ _ μ _ _
  let ι : KR n →* M2 n := (Units.coeHom (M2 n)).comp ((GR n).subtype.comp (KR n).subtype)
  have hι : Continuous ι := continuous_mR.comp continuous_subtype_val
  have hιs : ∀ g : M2 n, InK g ↔ ∃ k, ι k = g := by
    intro g
    constructor
    · intro hg
      exact ⟨kOf ⟨g, hg⟩, rfl⟩
    · rintro ⟨k, rfl⟩
      exact k.2
  obtain ⟨ψ, a, b, hψ, ha, hb, hne⟩ := hLV n p q hgood (KR n) μ ι hι hιs
  refine ⟨ψ, mkG a ha, mkG b hb, nbEl, czLoc p q e (mkG a ha) (mkG b hb) ψ μ, hψ, fun x => rfl, continuous_nbEl,
    cz_diff hHol p q e _ _ hψ μ, ?_, fun w y => eigen hIwa hMult p q e _ _ ψ μ w y⟩
  rw [cz_zero]
  refine mul_ne_zero (zpow_ne_zero _ (mul_ne_zero (det_mR_ne (mkG a ha)) (det_mR_ne (mkG b hb)))) ?_
  exact hne

end PositivityTheory.Rg.Sw.AbsSt
end
end
