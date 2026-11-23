module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle006
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle007
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.GlobCore
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.TaylorSeries
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

open Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt.DF

open PositivityTheory.Rg.Sw

variable {n : ℕ}

theorem nU_mul_nU (b b' : Matrix (Fin n) (Fin n) ℂ) : nU b * nU b' = nU (b + b') := by
  simp only [nU, fromBlocks_multiply]
  congr 1 <;> simp [add_comm]

theorem nU_zero : nU (0 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  simp [nU, fromBlocks_one]

def wU (b : Matrix (Fin n) (Fin n) ℂ) : GL (Fin n ⊕ Fin n) ℂ where
  val := JJ n * nU b
  inv := nU (-b) * -JJ n
  val_inv := by
    calc JJ n * nU b * (nU (-b) * -JJ n) = JJ n * (nU b * nU (-b)) * -JJ n := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [nU_mul_nU, add_neg_cancel, nU_zero, Matrix.mul_one, Matrix.mul_neg, JJ_mul_self, neg_neg]
  inv_val := by
    calc nU (-b) * -JJ n * (JJ n * nU b) = -(nU (-b) * (JJ n * JJ n) * nU b) := by
          simp only [Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg]
      _ = 1 := by
          rw [JJ_mul_self, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, neg_neg, nU_mul_nU, neg_add_cancel, nU_zero]

theorem wU_mem (b : Matrix (Fin n) (Fin n) ℂ) (hb : b.IsHermitian) : wU b ∈ GR n := by
  change InG (JJ n * nU b)
  have hb' : bᴴ = b := hb
  simp only [InG, JJ, nU, Matrix.conjTranspose_mul, fromBlocks_conjTranspose, fromBlocks_multiply, hb']
  congr 1 <;> simp [hb']

theorem cell_dec (y : GR n) (hc : (mR y).toBlocks₂₁.det ≠ 0) :
    ∃ (y₁ g : GR n) (b : Matrix (Fin n) (Fin n) ℂ), IsUp y₁ ∧ b.IsHermitian ∧ mR g = JJ n * nU b ∧ y = y₁ * g := by
  have hy : (mR y)ᴴ * JJ n * mR y = JJ n := y.2
  have hinv : mR y * mR y⁻¹ = 1 := congrArg mR (mul_inv_cancel y)
  have hJ : mR y * JJ n * (mR y)ᴴ = JJ n := by
    have e1 : mR y * JJ n * (mR y)ᴴ * JJ n * mR y = - mR y := by
      calc _ = mR y * JJ n * ((mR y)ᴴ * JJ n * mR y) := by simp only [Matrix.mul_assoc]
        _ = - mR y := by rw [hy, Matrix.mul_assoc, JJ_mul_self, Matrix.mul_neg, Matrix.mul_one]
    have e2 : mR y * JJ n * (mR y)ᴴ * JJ n = -1 := by
      calc _ = mR y * JJ n * (mR y)ᴴ * JJ n * (mR y * mR y⁻¹) := by rw [hinv, Matrix.mul_one]
        _ = -1 := by rw [← Matrix.mul_assoc, e1, Matrix.neg_mul, hinv]
    calc _ = mR y * JJ n * (mR y)ᴴ * (JJ n * -JJ n) := by
          rw [Matrix.mul_neg, JJ_mul_self, neg_neg, Matrix.mul_one]
      _ = JJ n := by rw [← Matrix.mul_assoc, e2, Matrix.neg_mul, Matrix.one_mul, neg_neg]
  have hrel : (mR y).toBlocks₂₁ * ((mR y).toBlocks₂₂)ᴴ = (mR y).toBlocks₂₂ * ((mR y).toBlocks₂₁)ᴴ := by
    have h22 := congrArg toBlocks₂₂ hJ
    rw [← fromBlocks_toBlocks (mR y)] at h22
    simp only [JJ, fromBlocks_conjTranspose, fromBlocks_multiply, toBlocks_fromBlocks₂₂] at h22
    simp at h22
    rw [neg_add_eq_zero] at h22
    exact h22.symm
  have hblk : toBlocks₂₁ (mR y * fromBlocks (-((mR y).toBlocks₂₁⁻¹ * (mR y).toBlocks₂₂)) (-1) 1 0) =
      -((mR y).toBlocks₂₁ * ((mR y).toBlocks₂₁⁻¹ * (mR y).toBlocks₂₂)) + (mR y).toBlocks₂₂ := by
    conv_lhs => rw [← fromBlocks_toBlocks (mR y)]
    rw [fromBlocks_multiply, toBlocks_fromBlocks₂₁]
    simp
  set C := (mR y).toBlocks₂₁ with hCdef
  set D := (mR y).toBlocks₂₂ with hDdef
  have hC : IsUnit C.det := isUnit_iff_ne_zero.mpr hc
  have hCH : IsUnit Cᴴ.det := by
    rw [det_conjTranspose]
    exact hC.star
  have hb : (C⁻¹ * D).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [conjTranspose_mul, conjTranspose_nonsing_inv]
    calc Dᴴ * (Cᴴ)⁻¹ = C⁻¹ * (C * Dᴴ) * (Cᴴ)⁻¹ := by
          rw [← Matrix.mul_assoc C⁻¹, nonsing_inv_mul _ hC, Matrix.one_mul]
      _ = C⁻¹ * (D * Cᴴ) * (Cᴴ)⁻¹ := by rw [hrel]
      _ = C⁻¹ * D := by rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hCH, Matrix.mul_one]
  let g : GR n := ⟨wU (C⁻¹ * D), wU_mem _ hb⟩
  refine ⟨y * g⁻¹, g, C⁻¹ * D, ?_, hb, rfl, (inv_mul_cancel_right y g).symm⟩
  have hk : nU (-(C⁻¹ * D)) * -JJ n = fromBlocks (-(C⁻¹ * D)) (-1) 1 0 := by
    simp only [nU, JJ, fromBlocks_neg, fromBlocks_multiply]
    congr 1 <;> simp
  have hm : mR (y * g⁻¹) = mR y * (nU (-(C⁻¹ * D)) * -JJ n) := rfl
  show toBlocks₂₁ (mR (y * g⁻¹)) = 0
  rw [hm, hk, hblk, ← Matrix.mul_assoc, mul_nonsing_inv _ hC, Matrix.one_mul, neg_add_cancel]

theorem conj_cell {X : Fin n → ℝ} {a : ℝ → GR n} (ha : ∀ s, IsDil X s (a s)) (g : GR n)
    (b : Matrix (Fin n) (Fin n) ℂ) (hg : mR g = JJ n * nU b) (h : ℝ) :
    mR (a h * g * a h) = JJ n * nU (bS X h b) := by
  have h1 := ha h
  unfold IsDil at h1
  have hm : mR (a h * g * a h) = mR (a h) * mR g * mR (a h) := rfl
  rw [hm, h1, hg]
  simp only [JJ, nU, bS, fromBlocks_multiply]
  congr 1 <;> simp [diagonal_mul_diagonal, ← Complex.ofReal_mul, ← Real.exp_add, Matrix.mul_assoc, ← Complex.exp_add]
  ext i j
  by_cases hij : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, hij]

theorem cell_mul {X : Fin n → ℝ} {a : ℝ → GR n} (ha : ∀ s, IsDil X s (a s)) (y : GR n)
    (hc : (mR y).toBlocks₂₁.det ≠ 0) (s : ℝ) : (mR (y * a s)).toBlocks₂₁.det ≠ 0 := by
  have h1 := ha s
  unfold IsDil at h1
  have hm : mR (y * a s) = mR y * mR (a s) := rfl
  rw [hm, h1, ← fromBlocks_toBlocks (mR y), fromBlocks_multiply]
  simp only [toBlocks_fromBlocks₂₁, Matrix.mul_zero, add_zero, det_mul, det_diagonal]
  refine mul_ne_zero hc (Finset.prod_ne_zero_iff.mpr fun j _ => ?_)
  exact Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'

theorem weight_factor_dilation {X : Fin n → ℝ} {a : ℝ → GR n} (ha : ∀ s, IsDil X s (a s)) (p q : ℕ) (e : ℤ) (h : ℝ) :
    F0 p q e (a (-h)) = Complex.exp (-((h * ((p + q : ℕ) * ∑ j, X j) : ℝ) : ℂ)) := by
  have hm := ha (-h)
  unfold IsDil at hm
  simp only [F0, f0, u1, u2, hm, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, smul_zero, neg_zero, zero_add,
    det_fromBlocks_zero₂₁, det_diagonal, Complex.ofReal_exp]
  rw [← Complex.exp_sum, ← Complex.exp_sum, ← Complex.exp_add, ← Complex.exp_int_mul, ← Complex.exp_int_mul,
    ← Complex.exp_int_mul, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  simp only [Finset.sum_neg_distrib, ← Finset.mul_sum, Finset.sum_add_distrib]
  ring

end PositivityTheory.Rg.Sw.AbsSt.DF
end
end

section

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.AbsSt.Proj

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

theorem shape_mul (A B A' B' : Matrix (Fin n) (Fin n) ℂ) :
    fromBlocks A B (-B) A * fromBlocks A' B' (-B') A' =
      fromBlocks (A * A' - B * B') (A * B' + B * A') (-(A * B' + B * A')) (A * A' - B * B') := by
  rw [fromBlocks_multiply]
  congr 1 <;> noncomm_ring

theorem kM_mul (a b a' b' : Matrix (Fin n) (Fin n) ℂ) : kM a b * kM a' b' = kM (a * a') (b * b') := by
  simp only [kM]
  rw [shape_mul]
  congr 1 <;>
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_sub, Matrix.sub_mul, smul_add, smul_sub, smul_neg, neg_add, neg_sub] <;>
    match_scalars <;> ring_nf <;> (try simp only [Complex.I_sq]) <;> ring

theorem kM_one : kM (1 : Matrix (Fin n) (Fin n) ℂ) 1 = 1 := by
  simp only [kM, sub_self, smul_zero, neg_zero]
  rw [← fromBlocks_one]
  congr 1 <;> rw [← two_smul ℂ (1 : Matrix (Fin n) (Fin n) ℂ), smul_smul] <;> norm_num

theorem kM_conjTranspose (a b : Matrix (Fin n) (Fin n) ℂ) : (kM a b)ᴴ = kM aᴴ bᴴ := by
  simp only [kM, fromBlocks_conjTranspose, conjTranspose_smul, conjTranspose_add, conjTranspose_sub,
    conjTranspose_neg]
  congr 1 <;> simp [Complex.conj_ofReal, map_div₀] <;> module

theorem JJ_comm_shape (A B : Matrix (Fin n) (Fin n) ℂ) :
    JJ n * fromBlocks A B (-B) A = fromBlocks A B (-B) A * JJ n := by
  simp only [JJ, fromBlocks_multiply]
  congr 1 <;> simp

theorem JJ_comm_kM (a b : Matrix (Fin n) (Fin n) ℂ) : JJ n * kM a b = kM a b * JJ n := by
  unfold kM
  exact JJ_comm_shape _ _

theorem first_unitary_block_of_pair (a b : Matrix (Fin n) (Fin n) ℂ) : u1 (kM a b) = a := by
  simp only [u1, kM, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, smul_neg, smul_smul]
  rw [show Complex.I * (Complex.I / 2) = -(1/2 : ℂ) by
    rw [mul_div_assoc', Complex.I_mul_I]; ring]
  module

theorem second_unitary_block_of_pair (a b : Matrix (Fin n) (Fin n) ℂ) : u2 (kM a b) = b := by
  simp only [u2, kM, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, smul_neg, smul_smul, neg_neg]
  rw [show Complex.I * (Complex.I / 2) = -(1/2 : ℂ) by
    rw [mul_div_assoc', Complex.I_mul_I]; ring]
  module

theorem kM_low (a : Matrix (Fin n) (Fin n) ℂ) : (kM a a).toBlocks₂₁ = 0 := by
  unfold kM
  rw [toBlocks_fromBlocks₂₁]
  simp

theorem kM_of_unitary (a b : Matrix (Fin n) (Fin n) ℂ) (ha : a ∈ unitaryGroup (Fin n) ℂ)
    (hb : b ∈ unitaryGroup (Fin n) ℂ) : ∃ k : GR n, k ∈ KR n ∧ mR k = kM a b := by
  have ha1 : aᴴ * a = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp ha
  have ha2 : a * aᴴ = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp ha
  have hb1 : bᴴ * b = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hb
  have hb2 : b * bᴴ = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hb
  let u : GL (Fin n ⊕ Fin n) ℂ :=
    ⟨kM a b, kM aᴴ bᴴ, by rw [kM_mul, ha2, hb2, kM_one], by rw [kM_mul, ha1, hb1, kM_one]⟩
  have hG : u ∈ GR n := by
    show InG (kM a b)
    unfold InG
    rw [kM_conjTranspose, Matrix.mul_assoc, JJ_comm_kM, ← Matrix.mul_assoc, kM_mul, ha1, hb1,
      kM_one, Matrix.one_mul]
  refine ⟨⟨u, hG⟩, ?_, rfl⟩
  show InK (kM a b)
  exact ⟨hG, by rw [kM_conjTranspose, kM_mul, ha1, hb1, kM_one]⟩

theorem KR_shape (k : GR n) (hk : k ∈ KR n) :
    u1 (mR k) ∈ unitaryGroup (Fin n) ℂ ∧ u2 (mR k) ∈ unitaryGroup (Fin n) ℂ ∧
      mR k = kM (u1 (mR k)) (u2 (mR k)) := by
  have hk' : InK (mR k) := hk
  obtain ⟨hG, hU⟩ := hk'
  unfold InG at hG
  set g := mR k with hg
  have hU' : g * gᴴ = 1 := mul_eq_one_comm.mp hU
  have hc : JJ n * g = g * JJ n := by
    calc JJ n * g = (g * gᴴ) * JJ n * g := by rw [hU', Matrix.one_mul]
      _ = g * (gᴴ * JJ n * g) := by simp only [Matrix.mul_assoc]
      _ = g * JJ n := by rw [hG]
  have hc' := hc
  rw [← fromBlocks_toBlocks g] at hc'
  simp only [JJ, fromBlocks_multiply, Matrix.zero_mul, Matrix.one_mul, zero_add, add_zero,
    Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_one, Matrix.mul_zero, neg_zero] at hc'
  rw [fromBlocks_inj] at hc'
  obtain ⟨h1, h2, -, -⟩ := hc'
  have hshape : g = kM (u1 g) (u2 g) := by
    conv_lhs => rw [← fromBlocks_toBlocks g]
    simp only [kM, u1, u2, h1, h2]
    congr 1 <;> match_scalars <;> ring_nf <;> (try simp only [Complex.I_sq]) <;> ring
  have hx : kM ((u1 g)ᴴ * u1 g) ((u2 g)ᴴ * u2 g) = kM 1 1 := by
    rw [← kM_mul, ← kM_conjTranspose, ← hshape, hU, kM_one]
  have e1 : (u1 g)ᴴ * u1 g = 1 := by
    have := congrArg u1 hx
    rwa [first_unitary_block_of_pair, first_unitary_block_of_pair] at this
  have e2 : (u2 g)ᴴ * u2 g = 1 := by
    have := congrArg u2 hx
    rwa [second_unitary_block_of_pair, second_unitary_block_of_pair] at this
  exact ⟨Matrix.mem_unitaryGroup_iff'.mpr e1, Matrix.mem_unitaryGroup_iff'.mpr e2, hshape⟩

theorem kIso : KIso := by
  intro n
  exact ⟨fun a b ha hb => kM_of_unitary a b ha hb, kM_mul, kM_one, fun a b => ⟨first_unitary_block_of_pair a b, second_unitary_block_of_pair a b⟩,
    kM_low, KR_shape⟩

end PositivityTheory.Rg.Sw.AbsSt.Proj
end
end

section

noncomputable section

open Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt

theorem anNhd_iter {f : ℂ → ℂ} {V : Set ℂ} (hV : IsOpen V) (hf : DifferentiableOn ℂ f V) (r : ℕ) :
    AnalyticOnNhd ℂ (iteratedDeriv r f) V := by
  rw [iteratedDeriv_eq_iterate]
  exact (hf.analyticOnNhd hV).iterated_deriv r

theorem real_iter (f : ℂ → ℂ) (V : Set ℂ) (hV : IsOpen V) (hR : ∀ s : ℝ, (s : ℂ) ∈ V)
    (hf : DifferentiableOn ℂ f V) (r : ℕ) :
    iteratedDeriv r (fun t : ℝ => f t) = fun s : ℝ => iteratedDeriv r f s := by
  induction r with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext s
    rw [iteratedDeriv_succ]
    have hd : DifferentiableAt ℂ (iteratedDeriv n f) (s : ℂ) :=
      ((anNhd_iter hV hf n) s (hR s)).differentiableAt
    exact hd.hasDerivAt.comp_ofReal.deriv

theorem helpC : HelpC := by
  refine ⟨fun f V hV hR hf r s => congrFun (real_iter f V hV hR hf r) s, ?_⟩
  intro f V hV hR hf h0 s
  have hA := hf.analyticOnNhd hV
  have h0V : (0 : ℂ) ∈ V := by simpa using hR 0
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hV 0 h0V
  have hloc : f =ᶠ[𝓝 (0 : ℂ)] 0 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hε] with z hz
    rw [← Complex.taylorSeries_eq_on_ball' hz (hf.mono hball)]
    simp [h0]
  have hpre : IsPreconnected (Set.range ((↑) : ℝ → ℂ)) :=
    (isConnected_range Complex.continuous_ofReal).isPreconnected
  have hsub := hpre.subset_connectedComponentIn (x := (0 : ℂ)) ⟨0, by simp⟩
    (by rintro _ ⟨t, rfl⟩; exact hR t)
  have hEq := (hA.mono (connectedComponentIn_subset V 0)).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_connectedComponentIn (mem_connectedComponentIn h0V) hloc
  simpa using hEq (hsub ⟨s, rfl⟩)

end PositivityTheory.Rg.Sw.AbsSt
end
end

section

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

def FarRightC : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ) (p q : ℕ) (e : ℤ) (sL : PX m n →ₗ[ℂ] (GR n → ℂ))
    (ρ : GR n → PX m n →ₗ[ℂ] PX m n), LocData ε c t p q e sL ρ →
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] (Pp Γ : Subgroup G) (ι : GR n →* G) (s₀ : ℂ) (Ht : G → ℝ≥0)
      (sec I : PX m n →ₗ[ℂ] (G → ℂ)), GlobCore ε c sL ρ G Pp Γ ι s₀ Ht sec I →
      ∃ σ : ℝ, (∀ Q g, DifferentiableOn ℂ (fun z => GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z Q) g) (GlobalTheory.Cont.rightOf σ)) ∧
        (∀ Q g (z : ℂ), σ < z.re → Summable fun q => GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z Q) g q) ∧
        ∀ [MeasurableSpace (KR n)] [BorelSpace (KR n)] (ν : Measure (KR n)) (κ : KR n → ℂ) (N : ℕ) (yy : Fin N → GR n)
          (QQ : Fin N → PX m n) (M : ℂ → Matrix (Fin N) (Fin N) ℂ), IsFiniteMeasure ν → Continuous κ →
          (∀ (w : ℂ) (i : Fin N) (y' : GR n), ∫ k, κ k * ((hLoc (y' * (k : GR n) * yy i) : ℂ) ^ w *
              F0 p q e (y' * (k : GR n) * yy i)) ∂ν = (hLoc y' : ℂ) ^ w * ∑ j, M w i j * sL (QQ j) y') →
          ∀ (z : ℂ), σ < z.re → ∀ (g : G) (i : Fin N),
            ∫ k, κ k * GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z 1) (g * ι ((k : GR n) * yy i)) ∂ν =
              ∑ j, M (z - s₀) i j * GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z (QQ j)) g

def TSGenC : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ) (p q : ℕ) (e : ℤ) (sL : PX m n →ₗ[ℂ] (GR n → ℂ))
    (ρ : GR n → PX m n →ₗ[ℂ] PX m n), LocData ε c t p q e sL ρ →
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] (Pp Γ : Subgroup G) (ι : GR n →* G) (s₀ : ℂ) (Ht : G → ℝ≥0)
      (sec I : PX m n →ₗ[ℂ] (G → ℂ)), GlobCore ε c sL ρ G Pp Γ ι s₀ Ht sec I →
      ∀ [MeasurableSpace (KR n)] [BorelSpace (KR n)] (W : Submodule ℂ (PX m n)), FiniteDimensional ℂ W →
        (∀ k : GR n, InK (mR k) → ∀ Q ∈ W, ρ k Q ∈ W) → ∀ (ν : Measure (KR n)) (κ : KR n → ℂ), IsFiniteMeasure ν →
        Continuous κ → (∀ Q ∈ W, ∀ y : GR n, ∫ k, κ k * sL Q (y * (k : GR n)) ∂ν = sL Q y) →
        (∀ (w : ℂ) (f : GR n → ℂ), Continuous f →
          (∀ (y g : GR n), (mR y).toBlocks₂₁ = 0 → f (y * g) = (hLoc y : ℂ) ^ w * F0 p q e y * f g) →
          ∃ Q ∈ W, ∀ y : GR n, ∫ k, κ k * f (y * (k : GR n)) ∂ν = (hLoc y : ℂ) ^ w * sL Q y) →
        ∀ (g : G) (y : GR n) (Q : PX m n), Q ∈ W → (∀ y', ∫ k, κ k * F0 p q e (y' * (k : GR n) * y) ∂ν = sL Q y') →
          ∫ k, κ k * I 1 (g * ι ((k : GR n) * y)) ∂ν = I Q g

def VacData {n : ℕ} {m : ℕ} {G : Type} [Group G] [TopologicalSpace G] (Pp Γ : Subgroup G) (s₀ : ℂ) (Ht : G → ℝ≥0)
    (sec I : PX m n →ₗ[ℂ] (G → ℂ)) : Prop :=
  ∃ (r : ℝ) (F : ℂ → G → ℂ), 0 < r ∧ ContinuousOn (fun y : ℂ × G => F y.1 y.2) (Metric.ball s₀ r ×ˢ univ) ∧
    (∀ g, DifferentiableOn ℂ (F · g) (Metric.ball s₀ r)) ∧ (∀ g, F s₀ g = I 1 g) ∧
    ∀ g, ∀ z ∈ Metric.ball s₀ r, GlobalTheory.Cont.HolValueAt
      (fun w => GlobalTheory.Eis.cosetSum Pp Γ (fun x => ((Ht x : ℝ) : ℂ) ^ (w - s₀) * sec 1 x) g) z (F z g)

def GenCore : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ) (p q : ℕ) (e : ℤ) (sL : PX m n →ₗ[ℂ] (GR n → ℂ))
    (ρ : GR n → PX m n →ₗ[ℂ] PX m n), LocData ε c t p q e sL ρ →
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] (Pp Γ : Subgroup G) (ι : GR n →* G) (s₀ : ℂ) (Ht : G → ℝ≥0)
      (sec I : PX m n →ₗ[ℂ] (G → ℂ)), GlobCore ε c sL ρ G Pp Γ ι s₀ Ht sec I → VacData Pp Γ s₀ Ht sec I →
      ∀ P g, GlobalTheory.Cont.HolValueAt
        (fun z => GlobalTheory.Eis.cosetSum Pp Γ (fun x => ((Ht x : ℝ) : ℂ) ^ (z - s₀) * sec P x) g) s₀ (I P g)

end PositivityTheory.Rg.Sw.AbsSt
end
end
