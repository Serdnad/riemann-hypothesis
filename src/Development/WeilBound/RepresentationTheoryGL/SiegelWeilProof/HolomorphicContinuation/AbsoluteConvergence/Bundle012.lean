module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle007
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle006
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle003
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle005
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

variable {n : ℕ}

theorem mR_dil (X : Fin n → ℝ) (s : ℝ) (a : GR n) (h : IsDil X s a) : mR a = Ac X s := by
  rw [h]
  unfold Ac
  congr 2 <;> funext j <;> push_cast [Complex.ofReal_exp] <;> (try ring_nf)

theorem det_Ac (X : Fin n → ℝ) (z : ℂ) : (Ac X z).det = 1 := by
  unfold Ac
  rw [det_fromBlocks_zero₂₁, det_diagonal, det_diagonal, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun j _ => ?_
  rw [← Complex.exp_add]
  try simp

theorem holomorphic_section_extension_eq (p q : ℕ) (e : ℤ) (X : Fin n → ℝ) (a : ℝ → GR n) (ha : ∀ s, IsDil X s (a s)) (h : GR n) (s : ℝ) :
    holomorphicSectionExtension p q e X h s = F0 p q e (h * a s) := by
  unfold holomorphicSectionExtension F0 f0
  rw [mR_mul, mR_dil X s (a s) (ha s), det_mul, det_Ac, mul_one, mul_assoc]

theorem continuous_Ac (X : Fin n → ℝ) : Continuous (Ac X) := by
  unfold Ac
  refine Continuous.matrix_fromBlocks ?_ continuous_const continuous_const ?_
  · exact Continuous.matrix_diagonal (continuous_pi fun j => by fun_prop)
  · exact Continuous.matrix_diagonal (continuous_pi fun j => by fun_prop)

theorem differentiable_Ac_entry (X : Fin n → ℝ) (a b : Fin n ⊕ Fin n) : Differentiable ℂ fun z => Ac X z a b := by
  rcases a with a | a <;> rcases b with b | b <;> by_cases hab : a = b <;>
    simp [Ac, diagonal_apply, hab] <;> fun_prop

theorem differentiable_det_entries {m : Type} [Fintype m] [DecidableEq m] (A : ℂ → Matrix m m ℂ)
    (hA : ∀ i j, Differentiable ℂ fun z => A z i j) : Differentiable ℂ fun z => (A z).det := by
  have : (fun z => (A z).det) = fun z => ∑ σ : Equiv.Perm m, ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A z (σ i) i := by
    funext z
    rw [det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
  rw [this]
  refine Differentiable.fun_sum fun σ _ => ?_
  exact (differentiable_const _).mul (Differentiable.fun_finsetProd fun i _ => hA _ _)

theorem differentiable_u_det (M : M2 n) (X : Fin n → ℝ) (w : ℂ) :
    Differentiable ℂ fun z => (w • (M * Ac X z).toBlocks₂₁ + (M * Ac X z).toBlocks₂₂).det := by
  apply differentiable_det_entries
  intro i j
  have hm : ∀ a b, Differentiable ℂ fun z => (M * Ac X z) a b := by
    intro a b
    simp only [Matrix.mul_apply]
    exact Differentiable.fun_sum fun k _ => (differentiable_const _).mul (differentiable_Ac_entry X k b)
  simp only [Matrix.add_apply, Matrix.smul_apply, toBlocks₂₁, toBlocks₂₂, of_apply, smul_eq_mul]
  exact ((differentiable_const _).mul (hm _ _)).add (hm _ _)

theorem continuous_u_det (X : Fin n → ℝ) (w : ℂ) :
    Continuous fun y : GR n × ℂ => (w • (mR y.1 * Ac X y.2).toBlocks₂₁ + (mR y.1 * Ac X y.2).toBlocks₂₂).det := by
  have hM : Continuous fun y : GR n × ℂ => mR y.1 * Ac X y.2 :=
    (continuous_mR.comp continuous_fst).matrix_mul ((continuous_Ac X).comp continuous_snd)
  have h21 : Continuous fun y : GR n × ℂ => (mR y.1 * Ac X y.2).toBlocks₂₁ :=
    hM.matrix_submatrix (fun i : Fin n => (Sum.inr i : Fin n ⊕ Fin n)) (fun j : Fin n => (Sum.inl j : Fin n ⊕ Fin n))
  have h22 : Continuous fun y : GR n × ℂ => (mR y.1 * Ac X y.2).toBlocks₂₂ :=
    hM.matrix_submatrix (fun i : Fin n => (Sum.inr i : Fin n ⊕ Fin n)) (fun j : Fin n => (Sum.inr j : Fin n ⊕ Fin n))
  exact ((h21.const_smul w).add h22).matrix_det

theorem first_cayley_block_eq (M : M2 n) : u1 M = Complex.I • M.toBlocks₂₁ + M.toBlocks₂₂ := rfl

theorem second_cayley_block_eq (M : M2 n) : u2 M = (-Complex.I) • M.toBlocks₂₁ + M.toBlocks₂₂ := by
  simp [u2, neg_smul]

theorem holomorphic_section_extension_exists (p q : ℕ) (e : ℤ) (X : Fin n → ℝ) (S : Set (GR n)) (hS : IsCompact S) :
    ∃ V : Set ℂ, IsOpen V ∧ (∀ s : ℝ, (s : ℂ) ∈ V) ∧
      ContinuousOn (fun y : GR n × ℂ => holomorphicSectionExtension p q e X y.1 y.2) (S ×ˢ V) ∧
      ∀ h ∈ S, DifferentiableOn ℂ (holomorphicSectionExtension p q e X h) V := by
  have c1 : Continuous fun y : GR n × ℂ => (u1 (mR y.1 * Ac X y.2)).det := by
    simpa only [first_cayley_block_eq] using continuous_u_det X Complex.I
  have c2 : Continuous fun y : GR n × ℂ => (u2 (mR y.1 * Ac X y.2)).det := by
    simpa only [second_cayley_block_eq] using continuous_u_det X (-Complex.I)
  set Z := {y : GR n × ℂ | (u1 (mR y.1 * Ac X y.2)).det ≠ 0 ∧ (u2 (mR y.1 * Ac X y.2)).det ≠ 0}
  have hZ : IsOpen Z := (isOpen_ne_fun c1 continuous_const).inter (isOpen_ne_fun c2 continuous_const)
  have hreal : ∀ (h : GR n) (s : ℝ), ((h, (s : ℂ)) : GR n × ℂ) ∈ Z := by
    intro h s
    have hm : mR h * Ac X s = mR (h * aD X s) := by rw [mR_mul, mR_dil X s _ (isDil_aD X s)]
    refine ⟨?_, ?_⟩
    · show (u1 (mR h * Ac X s)).det ≠ 0
      rw [hm]
      exact automorphy_first_det_ne_zero _
    · show (u2 (mR h * Ac X s)).det ≠ 0
      rw [hm]
      exact automorphy_second_det_ne_zero _
  have tube : ∀ s : ℝ, ∃ v : Set ℂ, IsOpen v ∧ (s : ℂ) ∈ v ∧ S ×ˢ v ⊆ Z := by
    intro s
    obtain ⟨u, v, -, hv, hSu, hsv, huv⟩ := generalized_tube_lemma hS (isCompact_singleton (x := (s : ℂ))) hZ
      (by
        rintro ⟨h, z⟩ ⟨-, hz⟩
        simp only [Set.mem_singleton_iff] at hz
        rw [hz]
        exact hreal h s)
    exact ⟨v, hv, hsv rfl, (Set.prod_mono hSu le_rfl).trans huv⟩
  choose v hv hsv hSv using tube
  refine ⟨⋃ s, v s, isOpen_iUnion hv, fun s => Set.mem_iUnion.mpr ⟨s, hsv s⟩, ?_, ?_⟩
  · have hsub : S ×ˢ (⋃ s, v s) ⊆ Z := by
      rintro ⟨h, z⟩ ⟨hh, hz⟩
      obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hz
      exact hSv s (Set.mk_mem_prod hh hs)
    intro y hy
    refine ContinuousAt.continuousWithinAt ?_
    have hyZ := hsub hy
    unfold holomorphicSectionExtension
    have e1 : ContinuousAt (fun y : GR n × ℂ => (mR y.1).det ^ e) y :=
      ((continuous_mR.comp continuous_fst).matrix_det.continuousAt).zpow₀ _ (Or.inl (det_mR_ne _))
    have e2 : ContinuousAt (fun y : GR n × ℂ => (u1 (mR y.1 * Ac X y.2)).det ^ (-(p : ℤ))) y :=
      c1.continuousAt.zpow₀ _ (Or.inl hyZ.1)
    have e3 : ContinuousAt (fun y : GR n × ℂ => (u2 (mR y.1 * Ac X y.2)).det ^ (-(q : ℤ))) y :=
      c2.continuousAt.zpow₀ _ (Or.inl hyZ.2)
    exact (e1.mul e2).mul e3
  · intro h hh z hz
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hz
    have hyZ := hSv s (Set.mk_mem_prod hh hs)
    have d1 : Differentiable ℂ fun z => (u1 (mR h * Ac X z)).det := by
      simpa only [first_cayley_block_eq] using differentiable_u_det (mR h) X Complex.I
    have d2 : Differentiable ℂ fun z => (u2 (mR h * Ac X z)).det := by
      simpa only [second_cayley_block_eq] using differentiable_u_det (mR h) X (-Complex.I)
    unfold holomorphicSectionExtension
    have g1 : DifferentiableAt ℂ (fun z => (u1 (mR h * Ac X z)).det ^ (-(p : ℤ))) z := (d1 z).zpow (Or.inl hyZ.1)
    have g2 : DifferentiableAt ℂ (fun z => (u2 (mR h * Ac X z)).det ^ (-(q : ℤ))) z := (d2 z).zpow (Or.inl hyZ.2)
    exact (((differentiableAt_const _).mul g1).mul g2).differentiableWithinAt

end PositivityTheory.Rg.Sw.AbsSt
end
end

section

noncomputable section

open Matrix Set Filter Topology Polynomial
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.AbsSt.DF

open PositivityTheory.Rg.Sw

variable {n : ℕ}

def nbU (l : ℝ) : GL (Fin n ⊕ Fin n) ℂ where
  val := fromBlocks 1 0 ((l : ℂ) • 1) 1
  inv := fromBlocks 1 0 (-((l : ℂ) • 1)) 1
  val_inv := by simp [fromBlocks_multiply, ← fromBlocks_one]
  inv_val := by simp [fromBlocks_multiply, ← fromBlocks_one]

theorem nbU_mem (l : ℝ) : nbU (n := n) l ∈ GR n := by
  change InG (fromBlocks 1 0 ((l : ℂ) • 1) 1)
  simp only [InG, JJ, fromBlocks_conjTranspose, fromBlocks_multiply]
  congr 1 <;> simp [Matrix.smul_eq_diagonal_mul]

def nbG (l : ℝ) : GR n := ⟨nbU l, nbU_mem l⟩

theorem nbG_zero : nbG (n := n) 0 = 1 := by
  apply ext_mR
  show fromBlocks 1 0 (((0 : ℝ) : ℂ) • 1) 1 = 1
  simp [fromBlocks_one]

theorem cont_nbG : Continuous (nbG (n := n)) := by
  apply Continuous.subtype_mk
  rw [Units.continuous_iff]
  constructor
  · show Continuous fun l : ℝ => (fromBlocks 1 0 ((l : ℂ) • 1) 1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    refine continuous_pi fun i => continuous_pi fun j => ?_
    rcases i with i | i <;> rcases j with j | j <;> simp <;> fun_prop
  · show Continuous fun l : ℝ => (fromBlocks 1 0 (-((l : ℂ) • 1)) 1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    refine continuous_pi fun i => continuous_pi fun j => ?_
    rcases i with i | i <;> rcases j with j | j <;> simp <;> fun_prop

theorem nbG_low (l : ℝ) (y : GR n) :
    (mR (nbG l * y)).toBlocks₂₁ = (l : ℂ) • (mR y).toBlocks₁₁ + (mR y).toBlocks₂₁ := by
  have hm : mR (nbG l * y) = fromBlocks 1 0 ((l : ℂ) • 1) 1 * mR y := rfl
  rw [hm]
  conv_lhs => rw [← fromBlocks_toBlocks (mR y)]
  rw [fromBlocks_multiply, toBlocks_fromBlocks₂₁]
  simp

theorem det_I (y : GR n) : (Complex.I • (mR y).toBlocks₁₁ + (mR y).toBlocks₂₁).det ≠ 0 := by
  intro hdet
  obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  let v : Fin n ⊕ Fin n → ℂ := Sum.elim x 0
  have hYv : mR y *ᵥ v = Sum.elim ((mR y).toBlocks₁₁ *ᵥ x) ((mR y).toBlocks₂₁ *ᵥ x) := by
    conv_lhs => rw [← fromBlocks_toBlocks (mR y)]
    rw [fromBlocks_mulVec]
    simp [v]
  have hCx : (mR y).toBlocks₂₁ *ᵥ x = -(Complex.I • ((mR y).toBlocks₁₁ *ᵥ x)) := by
    rw [add_mulVec, smul_mulVec] at hx
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact hx
  have hy : (mR y)ᴴ * JJ n * mR y = JJ n := y.2
  have hform : star (mR y *ᵥ v) ⬝ᵥ (JJ n *ᵥ (mR y *ᵥ v)) = 0 := by
    rw [star_mulVec, mulVec_mulVec, dotProduct_mulVec, vecMul_vecMul, ← Matrix.mul_assoc, hy,
      ← dotProduct_mulVec]
    simp [v, JJ, fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type]
  rw [hYv, hCx] at hform
  simp [JJ, fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type] at hform
  set u := (mR y).toBlocks₁₁ *ᵥ x with hu
  simp only [neg_mulVec, Pi.neg_apply] at hform
  have h3 : (-2 * Complex.I) * ∑ i, starRingEnd ℂ (u i) * u i = 0 := by
    rw [← hform, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have h2 : ∑ i, starRingEnd ℂ (u i) * u i = 0 :=
    (mul_eq_zero.mp h3).resolve_left (by simp [Complex.I_ne_zero])
  have hu0 : u = 0 := by
    rw [← dotProduct_star_self_eq_zero]
    simpa [dotProduct] using h2
  have hYv0 : mR y *ᵥ v = 0 := by
    rw [hYv, hCx, hu0]
    ext i
    rcases i with i | i <;> simp
  have hinv : mR y⁻¹ * mR y = 1 := congrArg mR (inv_mul_cancel y)
  have hv : v = 0 := by
    rw [← one_mulVec v, ← hinv, ← mulVec_mulVec, hYv0, mulVec_zero]
  apply hx0
  funext i
  exact congrFun hv (Sum.inl i)

theorem finite_bad (y : GR n) :
    {l : ℝ | ((l : ℂ) • (mR y).toBlocks₁₁ + (mR y).toBlocks₂₁).det = 0}.Finite := by
  let M : Matrix (Fin n) (Fin n) ℂ[X] :=
    (X : ℂ[X]) • (mR y).toBlocks₁₁.map (Polynomial.C : ℂ →+* ℂ[X]) + (mR y).toBlocks₂₁.map (Polynomial.C : ℂ →+* ℂ[X])
  let p : ℂ[X] := M.det
  have hev : ∀ z : ℂ, p.eval z = (z • (mR y).toBlocks₁₁ + (mR y).toBlocks₂₁).det := by
    intro z
    have h := RingHom.map_det (Polynomial.evalRingHom z) M
    rw [Polynomial.coe_evalRingHom] at h
    rw [h]
    congr 1
    ext i j
    simp [M]
    ring
  have hp : p ≠ 0 := by
    intro h0
    apply det_I y
    rw [← hev, h0, Polynomial.eval_zero]
  apply (p.roots.toFinset.finite_toSet.preimage Complex.ofReal_injective.injOn).subset
  intro l hl
  simp only [Set.mem_setOf_eq] at hl
  rw [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hp]
  exact (hev _).trans hl

theorem dense_cell : Dense {y : GR n | (mR y).toBlocks₂₁.det ≠ 0} := by
  rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro y
  have hS := finite_bad y
  set S := {l : ℝ | ((l : ℂ) • (mR y).toBlocks₁₁ + (mR y).toBlocks₂₁).det = 0} with hSdef
  have hT : (S \ {0})ᶜ ∈ 𝓝 (0 : ℝ) :=
    (hS.diff (s := S) (t := {0})).isClosed.isOpen_compl.mem_nhds (by simp)
  have hcont : Continuous fun t : ℝ => nbG (n := n) t * y := cont_nbG.mul continuous_const
  have htend : Tendsto (fun t : ℝ => nbG (n := n) t * y) (𝓝[≠] 0) (𝓝 y) := by
    have h := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
    simpa [nbG_zero] using h
  apply mem_closure_of_tendsto htend
  filter_upwards [nhdsWithin_le_nhds hT, self_mem_nhdsWithin] with t h1 h2
  simp only [Set.mem_setOf_eq, nbG_low]
  intro hdet
  exact h1 ⟨hdet, h2⟩

end PositivityTheory.Rg.Sw.AbsSt.DF
end
end
