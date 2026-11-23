module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle193
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaDecompComplexifiedMaxCompact
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle005
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle296
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FinalD
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle192
public import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
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
import Formalism.LocalToGlobal.GlobalTheory.GL6.Statement

@[expose] public section

section

open Matrix Formalism.MainNotions.S GlobalTheory.JointHarm

noncomputable section

namespace GlobalTheory.JointHarm.Sph

variable {n : ℕ} {ε : Fin n → Bool} {μ : Fin n → ℝ}

theorem entire_eq_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h : ∀ t : ℝ, f t = 0) (z : ℂ) : f z = 0 := by
  have ha : AnalyticOnNhd ℂ f Set.univ := hf.differentiableOn.analyticOnNhd isOpen_univ
  refine ha.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ (Set.mem_univ 0) ?_
    (Set.mem_univ z)
  have ht : Filter.Tendsto (fun t : ℝ => (t : ℂ)) (nhdsWithin 0 {0}ᶜ) (nhdsWithin 0 {0}ᶜ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := Complex.continuous_ofReal.tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simpa using ht
  exact ht.frequently (Filter.Eventually.of_forall h).frequently

theorem diag_mem {d : Fin n → ℂ} (hd : ∀ a, d a ≠ 0) : Matrix.diagonal d ∈ GlobalTheory.Dec.KC ε := by
  refine ⟨?_, by simp [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, mul_comm]⟩
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_diagonal, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
  exact fun a _ => hd a

theorem mul_mem {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ GlobalTheory.Dec.KC ε) (hb : b ∈ GlobalTheory.Dec.KC ε) :
    a * b ∈ GlobalTheory.Dec.KC ε :=
  ⟨ha.1.mul hb.1, by rw [Matrix.mul_assoc, hb.2, ← Matrix.mul_assoc, ha.2, Matrix.mul_assoc]⟩

theorem ct_mem {a : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ GlobalTheory.Dec.KC ε) : aᴴ ∈ GlobalTheory.Dec.KC ε := by
  refine ⟨by simpa [Matrix.star_eq_conjTranspose] using ha.1.star, ?_⟩
  have := congrArg Matrix.conjTranspose ha.2
  simp only [Matrix.conjTranspose_mul, Formalism.REAL.Jm_conjTranspose] at this
  exact this.symm

section One

variable {P : Type} [AddCommGroup P] [Module ℂ P] {B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ}
  {π : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ P}

theorem diff_curve (h : IsHolRep ε B π) {c : ℂ → Matrix (Fin n) (Fin n) ℂ}
    (hc : ∀ i j, Differentiable ℂ fun z => c z i j) (hm : ∀ z, c z ∈ GlobalTheory.Dec.KC ε) (x y : P) :
    Differentiable ℂ fun z => B x (π (c z) y) := by
  have h1 : Differentiable ℂ fun z => (fun i j => c z i j : Fin n → Fin n → ℂ) :=
    differentiable_pi.2 fun i => differentiable_pi.2 fun j => hc i j
  have := (h.2.2.2.2 x y).comp (s := Set.univ) h1.differentiableOn (fun z _ => hm z)
  exact differentiableOn_univ.1 this

theorem real_torus (h : IsHolRep ε B π) {x : P} (hx : IsBottom ε π μ x) (s : Fin n → ℝ) :
    π (Matrix.diagonal fun a => Complex.exp (s a : ℂ)) x = Complex.exp ((∑ a, μ a * s a : ℝ) : ℂ) • x := by
  rw [← sub_eq_zero]
  apply h.1
  generalize hw : π (Matrix.diagonal fun a => Complex.exp (s a : ℂ)) x -
    Complex.exp ((∑ a, μ a * s a : ℝ) : ℂ) • x = w
  have hd := diff_curve h (c := fun z => Matrix.diagonal fun a => Complex.exp (z * s a * Complex.I))
    (fun i j => by
      by_cases e : i = j
      · subst e; simp only [Matrix.diagonal_apply_eq]; fun_prop
      · simp only [Matrix.diagonal_apply_ne _ e]; fun_prop)
    (fun z => diag_mem fun a => Complex.exp_ne_zero _) w x
  have h0 := entire_eq_zero (f := fun z => B w (π (Matrix.diagonal fun a => Complex.exp (z * s a * Complex.I)) x) -
      Complex.exp (z * ((∑ a, μ a * s a : ℝ) : ℂ) * Complex.I) * B w x) (hd.sub (by fun_prop))
    (fun t => by
      have := hx.2 (fun a => t * s a)
      have e : (∑ a, μ a * (t * s a)) = t * ∑ a, μ a * s a := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => by ring
      rw [e] at this
      simp only [Complex.ofReal_mul] at this
      simp only [this, map_smul, smul_eq_mul, sub_self]) (-Complex.I)
  have e : ∀ u : ℂ, -Complex.I * u * Complex.I = u := fun u => by
    linear_combination (-u) * Complex.I_mul_I
  simp only [e] at h0
  conv_lhs => enter [2]; rw [← hw]
  rw [map_sub, map_smul, smul_eq_mul, h0]

theorem borel {b : Matrix (Fin n) (Fin n) ℂ} (hb : b ∈ GlobalTheory.Dec.KC ε) (hl : GlobalTheory.Dec.IsLo b)
    (hp : ∀ i, b i i = Complex.exp (Real.log (b i i).re : ℝ))
    (h : IsHolRep ε B π) {x : P} (hx : IsBottom ε π μ x) :
    π b x = Complex.exp ((∑ a, μ a * Real.log (b a a).re : ℝ) : ℂ) • x := by
  have hne : ∀ i, b i i ≠ 0 := fun i => by rw [hp i]; exact Complex.exp_ne_zero _
  have hu : Matrix.diagonal (fun a => (b a a)⁻¹) * b ∈ GlobalTheory.Dec.KC ε :=
    mul_mem (diag_mem fun a => inv_ne_zero (hne a)) hb
  have hlu : IsLoUni (Matrix.diagonal (fun a => (b a a)⁻¹) * b) := fun i j =>
    ⟨fun hij => by rw [Matrix.diagonal_mul, hl i j hij, mul_zero],
      fun hij => by subst hij; rw [Matrix.diagonal_mul, inv_mul_cancel₀ (hne i)]⟩
  have e : b = Matrix.diagonal (fun a => Complex.exp (Real.log (b a a).re : ℝ)) *
      (Matrix.diagonal (fun a => (b a a)⁻¹) * b) := by
    ext i j
    rw [Matrix.diagonal_mul, Matrix.diagonal_mul, ← hp i, mul_inv_cancel_left₀ (hne i)]
  conv_lhs => rw [e]
  rw [h.2.2.1 _ (diag_mem fun a => Complex.exp_ne_zero _) _ hu, Module.End.mul_apply, hx.1 _ hu hlu,
    real_torus h hx]

end One


open scoped ComplexOrder in
theorem gram {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ GlobalTheory.Dec.KC ε) (μ : Fin n → ℝ) :
    ∃ c : ℂ, ∀ (P : Type) [AddCommGroup P] [Module ℂ P] (B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ)
      (π : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ P) (x y : P), IsHolRep ε B π → IsBottom ε π μ x →
      IsBottom ε π μ y → B x (π (gᴴ * g) y) = c * B x y := by
  obtain ⟨k, b, hk, hb, hl, hp, rfl⟩ := GlobalTheory.Dec.IwKC.exists_decomp ε hg
  have hp' : ∀ i, b i i = Complex.exp (Real.log (b i i).re : ℝ) := fun i => by
    have := Complex.pos_iff.1 (hp i)
    rw [← Complex.ofReal_exp, Real.exp_log this.1]
    exact Complex.ext rfl (by simpa using this.2.symm)
  refine ⟨star (Complex.exp ((∑ a, μ a * Real.log (b a a).re : ℝ) : ℂ)) *
    Complex.exp ((∑ a, μ a * Real.log (b a a).re : ℝ) : ℂ), fun P _ _ B π x y h hx hy => ?_⟩
  rw [GlobalTheory.Dec.IwKC.gram_unitary_mul hk.1, h.2.2.1 _ (ct_mem hb) _ hb, Module.End.mul_apply,
    ← h.2.2.2.1 _ hb, borel hb hl hp' h hx, borel hb hl hp' h hy]
  simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, starRingEnd_apply]
  ring

section Exp

open scoped Matrix.Norms.Operator

theorem exp_mem {H : Matrix (Fin n) (Fin n) ℂ} (hJ : H * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * H) (z : ℂ) :
    NormedSpace.exp (z • H) ∈ GlobalTheory.Dec.KC ε := by
  refine ⟨Matrix.isUnit_exp _, ?_⟩
  have : Commute (z • H) (Formalism.REAL.Jm ε) := Commute.smul_left hJ z
  exact this.exp_left.eq

theorem exp_diff (H : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    Differentiable ℂ fun z : ℂ => NormedSpace.exp (z • H) i j := by
  have h1 : Differentiable ℂ fun z : ℂ => NormedSpace.exp (z • H) :=
    fun z => (hasDerivAt_exp_smul_const H z).differentiableAt
  exact (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ i j)).differentiable.comp h1

theorem exp_gram {H : Matrix (Fin n) (Fin n) ℂ} (hH : Hᴴ = H) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • H) =
      (NormedSpace.exp (((t : ℂ) / 2) • H))ᴴ * NormedSpace.exp (((t : ℂ) / 2) • H) := by
  rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hH]
  have e : star ((t : ℂ) / 2) = (t : ℂ) / 2 := by simp
  rw [e, ← Matrix.exp_add_of_commute _ _ (Commute.refl _), ← add_smul, add_halves]

end Exp

theorem coeff_eq (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (P : Type) [AddCommGroup P] [Module ℂ P]
    (B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ) (π : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ P) (P' : Type) [AddCommGroup P']
    [Module ℂ P'] (B' : P' →ₗ⋆[ℂ] P' →ₗ[ℂ] ℂ) (π' : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ P') (x y : P)
    (x' y' : P') (h : IsHolRep ε B π) (h' : IsHolRep ε B' π') (hx : IsBottom ε π μ x) (hy : IsBottom ε π μ y)
    (hx' : IsBottom ε π' μ x') (hy' : IsBottom ε π' μ y') :
    ∀ k ∈ Formalism.REAL.Kset ε, B x (π k y) * B' x' y' = B x y * B' x' (π' k y') := by
  intro k hk
  obtain ⟨Y, ⟨hG, hY⟩, rfl, -⟩ := Formalism.REAL.compact_exists_log_bounded ε k hk
  have hs : Yᴴ = -Y := by
    have h1 : (Yᴴ + Y) * Formalism.REAL.Jm ε = 0 := by
      rw [Matrix.add_mul, hY]; exact hG
    have h2 := congrArg (· * Formalism.REAL.Jm ε) h1
    simp only [Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.mul_one, Matrix.zero_mul] at h2
    exact eq_neg_of_add_eq_zero_left h2
  have hH : ((-Complex.I) • Y)ᴴ = (-Complex.I) • Y := by
    rw [Matrix.conjTranspose_smul, hs]; simp
  have hJ : ((-Complex.I) • Y) * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * ((-Complex.I) • Y) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hY]
  have h0 := entire_eq_zero (f := fun z => B x (π (NormedSpace.exp (z • (-Complex.I) • Y)) y) * B' x' y' -
      B x y * B' x' (π' (NormedSpace.exp (z • (-Complex.I) • Y)) y'))
    (((diff_curve h (exp_diff _) (exp_mem hJ) x y).mul_const _).sub
      ((diff_curve h' (exp_diff _) (exp_mem hJ) x' y').const_mul _))
    (fun t => by
      obtain ⟨c, hc⟩ := gram (exp_mem hJ ((t : ℂ) / 2)) μ
      simp only [exp_gram hH t, hc P B π x y h hx hy, hc P' B' π' x' y' h' hx' hy']
      ring) Complex.I
  have e : Complex.I • (-Complex.I) • Y = Y := by rw [smul_smul]; simp
  simp only [e] at h0
  exact sub_eq_zero.1 h0

end GlobalTheory.JointHarm.Sph

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.JointHarm

theorem cyc_rowAct_rowAct {k n : ℕ} (g h : Matrix (Fin k) (Fin k) ℂ) (F : MvPolynomial (Fin k × Fin n) ℂ) :
    Formalism.GradedWeylDivisibility.rowAct ℂ g (Formalism.GradedWeylDivisibility.rowAct ℂ h F) = Formalism.GradedWeylDivisibility.rowAct ℂ (h * g) F := by
  have : (Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) g).comp (Formalism.GradedWeylDivisibility.rowAct ℂ h) = Formalism.GradedWeylDivisibility.rowAct ℂ (h * g) := by
    apply MvPolynomial.algHom_ext
    intro v

    simp only [AlgHom.comp_apply, Formalism.GradedWeylDivisibility.rowAct, MvPolynomial.aeval_X, map_sum, map_mul, MvPolynomial.algHom_C,
    Matrix.mul_apply]
    simp only [MvPolynomial.algebraMap_eq, Finset.mul_sum, Finset.sum_mul, ← MvPolynomial.C_mul]
    rw [Finset.sum_comm]
    simp [MvPolynomial.C_mul, mul_assoc]
  rw [← this]; rfl

theorem cyc_rowAct_one {k n : ℕ} (F : MvPolynomial (Fin k × Fin n) ℂ) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (1 : Matrix (Fin k) (Fin k) ℂ) F = F := by
  have : Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (1 : Matrix (Fin k) (Fin k) ℂ) = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [Formalism.GradedWeylDivisibility.rowAct, MvPolynomial.aeval_X, Matrix.one_apply, AlgHom.id_apply]
    rw [Finset.sum_eq_single v.1]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  rw [this]; rfl

theorem nablaSq_le_span_unitary (n : ℕ) (mu : DomWeight n) :
    nablaSq ℂ n mu ≤ Submodule.span ℂ
      {F | ∃ u ∈ Matrix.unitaryGroup (Fin n) ℂ, F = Formalism.GradedWeylDivisibility.rowAct ℂ u (extremal ℂ n mu)} := by
  have hν : Antitone mu.natW := (factNatW n mu).1
  have hmem : extremal ℂ n mu ∈ nablaSq ℂ n mu := Formalism.GradedWeylDivisibility.hwMem ℂ n n le_rfl mu.natW hν
  set M := Submodule.span ℂ
      {F | ∃ u ∈ Matrix.unitaryGroup (Fin n) ℂ, F = Formalism.GradedWeylDivisibility.rowAct ℂ u (extremal ℂ n mu)} with hM
  have hle : M ≤ nablaSq ℂ n mu := by
    rw [hM, Submodule.span_le]
    rintro _ ⟨u, -, rfl⟩
    exact Formalism.GradedWeylDivisibility.dualWeylRowStable ℂ n n _ _ _ hmem
  have hU : ∀ u ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ f ∈ M, Formalism.GradedWeylDivisibility.rowAct ℂ u f ∈ M := by
    intro u hu f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨v, hv, rfl⟩ := hx
      rw [cyc_rowAct_rowAct]
      exact Submodule.subset_span ⟨v * u, mul_mem hv hu, rfl⟩
    | zero => rw [map_zero]; exact M.zero_mem
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact M.add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact M.smul_mem c hx
  have hne : M ≠ ⊥ := by
    intro e
    have h1 : extremal ℂ n mu ∈ M := Submodule.subset_span ⟨1, one_mem _, (cyc_rowAct_one _).symm⟩
    rw [e, Submodule.mem_bot] at h1
    exact Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl mu.natW h1
  exact GlobalTheory.Branching.dualWeyl_le_of_rowDivClosed le_rfl mu.natW hν M hle
    (GlobalTheory.Branching.rowDivClosed_of_rowAct_stable M (GlobalTheory.Branching.rowAct_mem_of_unitary_stable M hU)) hne

theorem VV_le_span_vact_extremal : ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n), VV ℂ lam ≤ Submodule.span ℂ {F | ∃ u : ι → Matrix (Fin n) (Fin n) ℂ, (∀ τ, u τ ∈ Formalism.REAL.Kset (allPos n)) ∧ F = vact lam u (ten fun τ => extremal ℂ n (lam τ))} := by
  intro ι _ n lam
  unfold _root_.Formalism.L2.DIV.VV Formalism.GradedWeylDivisibility.tensorLat
  rw [Submodule.span_le]
  rintro _ ⟨f, hf, rfl⟩
  choose m c g hg using fun τ => Submodule.mem_span_set'.1 (nablaSq_le_span_unitary n (lam τ) (hf τ))
  choose v hv hgv using fun τ i => (g τ i).2
  have e : ∏ τ, Formalism.GradedWeylDivisibility.blockEmb ℂ τ (f τ) =
      ∑ p ∈ Fintype.piFinset (fun τ => (Finset.univ : Finset (Fin (m τ)))),
        (∏ τ, c τ (p τ)) • ∏ τ, Formalism.GradedWeylDivisibility.blockEmb ℂ τ (g τ (p τ) : MvPolynomial (Fin n × Fin n) ℂ) := by

    simp only [← hg, map_sum, map_smul]
    rw [Finset.prod_univ_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.prod_smul]
  rw [e, SetLike.mem_coe]
  refine Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ ?_
  set u : ι → Matrix (Fin n) (Fin n) ℂ := fun τ => star (v τ (p τ)) with hu
  have huU : ∀ τ, u τ ∈ Matrix.unitaryGroup (Fin n) ℂ := fun τ => Unitary.star_mem (hv τ (p τ))
  have hinv : ∀ τ, (u τ)⁻¹ = v τ (p τ) := fun τ =>
    Matrix.inv_eq_right_inv (Matrix.mem_unitaryGroup_iff'.1 (hv τ (p τ)))
  have hdet : (∏ τ, (u τ).det ^ (-(lam τ).detShift)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ ?_
    exact (Matrix.UnitaryGroup.det_isUnit ⟨u τ, huU τ⟩).ne_zero
  rw [← Submodule.smul_mem_iff _ hdet]
  refine Submodule.subset_span ⟨u, fun τ => ⟨huU τ, ?_⟩, ?_⟩
  · have : Formalism.REAL.Jm (allPos n) = 1 := by
      simp [Formalism.REAL.Jm, allPos]
    rw [this, mul_one, one_mul]
  · simp only [vact, ten, LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_prod]
    congr 1
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [(Formalism.GradedWeylDivisibility.blockActTensor ℂ ℂ ι n n _).1, hinv, hgv]

end GlobalTheory.JointHarm
end

section

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

namespace GlobalTheory.LevelHecke.UpDia

section Local
variable {R V k : Type} [CommRing R] [AddCommGroup V] [Module R V] [Field k]

theorem inc_dil {res : R →+* k} (hs : Function.Surjective res) {t : R} {p q : Pr R V k} (hp : p.Ok res)
    (h : Pr.Inc res t p q) {a : k} (ha : a ≠ 0) : Pr.Inc res t (p.dil a) (q.dil a) := by
  obtain ⟨h1, h2, e, h3, h4⟩ := h
  obtain ⟨b, hb⟩ := hs a⁻¹
  have he : e ∈ q.L := by
    by_contra hn
    rw [h1.off _ hn] at h3
    exact zero_ne_one h3
  have hte : t • e ∈ p.L := by
    by_contra hn
    rw [hp.off _ hn] at h4
    exact zero_ne_one h4
  refine ⟨h1.dil ha, fun y => ?_, b • e, ?_, ?_⟩
  · show y ∈ p.L ↔ y ∈ q.L ∧ a * q.f y = 0
    rw [h2 y, mul_eq_zero, or_iff_right ha]
  · show a * q.f _ = 1
    rw [h1.smul _ _ he, h3, hb, mul_one, mul_inv_cancel₀ ha]
  · show a * p.f _ = 1
    rw [smul_comm, hp.smul _ _ hte, h4, hb, mul_one, mul_inv_cancel₀ ha]

def dilEquiv {a : k} (ha : a ≠ 0) : Pr R V k ≃ Pr R V k where
  toFun q := q.dil a
  invFun q := q.dil a⁻¹
  left_inv q := by
    show (q.dil a).dil a⁻¹ = q
    rw [Pr.dil_dil, inv_mul_cancel₀ ha, Pr.dil_one]
  right_inv q := by
    show (q.dil a⁻¹).dil a = q
    rw [Pr.dil_dil, mul_inv_cancel₀ ha, Pr.dil_one]

end Local

theorem atV_conj {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {v : HeightOneSpectrum (𝓞 F)} {η : GA σ J}
    (h : AtV v η) (δ : GA σ J) : AtV v (δ⁻¹ * η * δ) := by
  intro v' hv'
  have h1 := h v' hv'
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, h1, mul_one, inv_mul_cancel]

theorem upAd_dia : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (ι : Type) [Fintype ι] (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal) (k : Type) [Field k] (p : GA σ J → Pr (𝓞 E) (Fin n → E) k), v ∉ bad → PMap S v hv p → ∀ (res : 𝓞 E →+* k) (t : 𝓞 E), Function.Surjective res → (∀ x, (p x).Ok res) → ∀ g ∈ AdFun S emb, ∀ (v' : HeightOneSpectrum (𝓞 F)) (hv' : (T : 𝓞 F) ∈ v'.asIdeal) (a : ℤ) (δ : GA σ J), v' ∉ bad → (v' = v → (a : k) ≠ 0) → IsDia S v' hv' a δ → ∀ x, upAd res t v p (fun y => g (y * δ)) x = upAd res t v p g (x * δ) := by
  intro F E _ _ _ _ _ σ n J T f bad ι _ S emb v hv k _ p hb hP res t hs hok g hg v' hv' a δ hb' ha hδ x
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.adelicForm_values_near_point_spec F E σ n J T f bad ι S emb v hv k p hb hP g hg
  by_cases hvv : v' = v
  · subst hvv
    have ha' := ha rfl
    unfold upAd
    rw [hP.2.2 x δ a hδ, h2 x δ hδ.1]
    refine finsum_mem_eq_of_bijOn (fun q => q.dil (a : k)) ?_ (fun q _ => (h3 a δ x q ha' hδ).symm)
    refine (dilEquiv ha').bijOn' ?_ ?_
    · intro q hq
      exact inc_dil hs (hok x) hq ha'
    · intro q hq
      have := inc_dil hs ((hok x).dil ha') hq (inv_ne_zero ha')
      rw [Pr.dil_dil, inv_mul_cancel₀ ha', Pr.dil_one] at this
      exact this
  · have hp : ∀ y, p (y * δ) = p y := fun y => (hP.2.1 y δ).2 (by
      rw [hδ.1 v (Ne.symm hvv)]; exact one_mem _)
    have key : valAt v p (fun y => g (y * δ)) x = valAt v p g (x * δ) := by
      funext q
      by_cases h : ∃ η, AtV v η ∧ p (x * η) = q
      · have hc := h.choose_spec
        have e : x * δ * (δ⁻¹ * h.choose * δ) = x * h.choose * δ := by group
        have := h1 (x * δ) _ (atV_conj hc.1 δ)
        rw [e, hp, hc.2] at this
        rw [this]
        unfold valAt
        rw [dite_eq_left h]
      · have h' : ¬ ∃ η, AtV v η ∧ p (x * δ * η) = q := by
          rintro ⟨η, hη, hq⟩
          refine h ⟨δ⁻¹⁻¹ * η * δ⁻¹, atV_conj hη _, ?_⟩
          rw [← hp, ← hq]
          congr 1
          group
        unfold valAt
        rw [dite_eq_right h, dite_eq_right h']
    unfold upAd
    rw [hp, key]

end GlobalTheory.LevelHecke.UpDia
end

section

open Formalism.BasicNotions Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.Theta NumberField MeasureTheory Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ

theorem inner_eq_integral_of_ae {α : Type} [MeasurableSpace α] {m : Measure α} (f g : Lp ℂ 2 m) (f' g' : α → ℂ)
    (hf : f =ᵐ[m] f') (hg : g =ᵐ[m] g') : ⟪f, g⟫_ℂ = ∫ x, star (f' x) * g' x ∂m := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf, hg] with x h1 h2
  rw [h1, h2, RCLike.inner_apply, mul_comm]
  rfl

theorem eq_smul_of_eval {α A E V : Type} [MeasurableSpace α] {m : Measure α} [AddCommGroup E] [Module ℂ E]
    (W : Submodule ℂ (Lp ℂ 2 m)) (φ : E → V → α → ℂ) (p : V → V → ℂ)
    (hS : ∀ T T', ∃ k : ℂ, ∀ v v', ∫ x, star (φ T v x) * φ T' v' x ∂m = k * p v v')
    (v₁ v₀ : V) (hp : p v₁ v₁ = 1) (j' : E ≃ₗ[ℂ] W) (hj' : ∀ T, ((j' T : W) : Lp ℂ 2 m) =ᵐ[m] φ T v₁)
    (e : A → E) (j : A → W) (a : ℂ) (hj : ∀ F, ((j F : W) : Lp ℂ 2 m) =ᵐ[m] fun x => a * φ (e F) v₀ x) (F : A) :
    j F = (a * p v₁ v₀) • j' (e F) := by
  have hmix : ∀ T : E, ⟪j' T, j F⟫_ℂ = (a * p v₁ v₀) * ⟪j' T, j' (e F)⟫_ℂ := by
    intro T
    obtain ⟨k, hk⟩ := hS T (e F)
    have h1 := inner_eq_integral_of_ae _ _ _ _ (hj' T) (hj F)
    have h2 := inner_eq_integral_of_ae _ _ _ _ (hj' T) (hj' (e F))
    rw [hk, hp, mul_one] at h2
    have h3 : ∫ x, star (φ T v₁ x) * (a * φ (e F) v₀ x) ∂m = a * ∫ x, star (φ T v₁ x) * φ (e F) v₀ x ∂m := by
      rw [← integral_const_mul]
      congr 1
      funext x
      ring
    rw [h3, hk] at h1
    rw [Submodule.coe_inner, Submodule.coe_inner, h1, h2]
    ring
  obtain ⟨T, hT⟩ := j'.surjective (j F - (a * p v₁ v₀) • j' (e F))
  have hz : ⟪j F - (a * p v₁ v₀) • j' (e F), j F - (a * p v₁ v₀) • j' (e F)⟫_ℂ = 0 := by
    conv_lhs => enter [2]; rw [← hT]
    rw [inner_sub_right, inner_smul_right, hmix, sub_self]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hz)

theorem exists_conj_scalar {A W H : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup W] [Module ℂ W] [AddCommGroup H]
    [Module ℂ H] (s : W →ₗ⋆[ℂ] H) (j f : A →ₗ[ℂ] W) (hj : Function.Injective j) (β : ℂ) (h : ∀ F, j F = β • f F) :
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ F, s (f F) = κ • s (j F) := by
  by_cases h0 : β = 0
  · refine ⟨1, one_ne_zero, fun F => ?_⟩
    have hF : j F = 0 := by rw [h, h0, zero_smul]
    have hF0 : F = 0 := hj (hF.trans (map_zero j).symm)
    subst hF0
    simp
  · refine ⟨(starRingEnd ℂ β)⁻¹, inv_ne_zero ((map_ne_zero _).2 h0), fun F => ?_⟩
    rw [h, LinearMap.map_smulₛₗ, smul_smul, inv_mul_cancel₀ ((map_ne_zero _).2 h0), one_smul]

theorem sEEofTT_eq_smul_conjHH : ∀ (D : D7) (S : D.what₂.Tau → Formalism.BasicNotions.TH.SPar) (M : DSModel (D.sp.Y 0) S) (E : Submodule ℂ (MMap M)) (St : Formalism.L2.SG.HidaSetting.HidaSetting D) (G : GoodOp St) (μ : Measure (GA D (D.sp.Y 0))) (𝓕 : Set (GA D (D.sp.Y 0))) (ι : GA D (D.sp.Y 0) ≃* St.B.I.GA) (t : GA D (D.sp.Y 0)) (c : ℝ), (∀ T ∈ E, ∀ T' ∈ E, ∃ c : ℂ, ∀ v v' : M.Vec, ∫ x, star (T v (ι.symm x * t)) * T' v' (ι.symm x * t) ∂(muX St) = c * ∏ τ, ⟪(v τ : M.H τ), (v' τ : M.H τ)⟫_ℂ) → EvalTieT M μ 𝓕 E St G ι t c → ∀ (e : D.what₂.EE →ₗ[ℂ] E) (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC St G) (v₀ : M.Vec) (a : ℂ), (∀ F, ((j F : EEC St G) : L2X St) =ᵐ[muX St] fun x => a * ev M v₀ (e F : MMap M) (ι.symm x * t)) → ∃ κ₀ : ℂ, κ₀ ≠ 0 ∧ ∀ F, sEEofTT M μ 𝓕 E St G ι t c (e F) = κ₀ • conjHH St G (j F) := by
  intro D S M E St G μ 𝓕 ι t c hS hT e j v₀ a hj
  have hv := hT.choose_spec.1
  have hj' := fun T => (hT.choose_spec.2.choose_spec T).1
  have hp : ∏ τ, ⟪(hT.choose τ : M.H τ), (hT.choose τ : M.H τ)⟫_ℂ = 1 := by
    refine Finset.prod_eq_one fun τ _ => ?_
    rw [inner_self_eq_norm_sq_to_K, hv τ]
    simp
  have hkey := eq_smul_of_eval (m := muX St) (EEC St G) (fun (T : E) (v : M.Vec) x => (T : MMap M) v (ι.symm x * t))
    (fun v v' => ∏ τ, ⟪(v τ : M.H τ), (v' τ : M.H τ)⟫_ℂ) (fun T T' => hS T T.2 T' T'.2) hT.choose v₀ hp
    hT.choose_spec.2.choose hj' e j a hj
  have hs : sEEofTT M μ 𝓕 E St G ι t c
      = (conjHH St G).toLinearMap.comp hT.choose_spec.2.choose.toLinearMap := dif_pos hT
  rw [hs]
  exact exists_conj_scalar (conjHH St G).toLinearMap j.toLinearEquiv.toLinearMap
    (hT.choose_spec.2.choose.toLinearMap.comp e) j.injective _ hkey

end GlobalTheory.Mem.SJ
end
