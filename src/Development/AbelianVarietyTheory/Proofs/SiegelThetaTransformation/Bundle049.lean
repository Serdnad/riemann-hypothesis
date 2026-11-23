module

import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle001
public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle014
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FiniteClsAndStab
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle019
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SchwartzBruhatInnerProductSelfNonnegBounds
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle023
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle028
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle036
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle046
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TwistAdmissible
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UnitaryActHalfSpace
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle045
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle038
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle031
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DoubledHermitianTestFunctionSpec
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle048
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle005
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle008
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001

@[expose] public section

section

open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.TwistBound

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}


omit [IsCMField E] in
theorem abs_norm_eq (h : IsType Ψ) (t : E) :
    |((Algebra.norm ℚ t : ℚ) : ℝ)| = ∏ τ : Ψ, ‖τ.1 t‖ ^ 2 := by
  have h2 := Algebra.norm_eq_prod_embeddings ℚ ℂ t
  have h3 : ∏ σ : E →+* ℂ, σ t = ∏ σ : E →ₐ[ℚ] ℂ, σ t :=
    Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ) _ _ fun _ => rfl
  have h1 : |((Algebra.norm ℚ t : ℚ) : ℝ)| = ∏ σ : E →+* ℂ, ‖σ t‖ := by
    rw [← norm_prod, h3, ← h2, eq_ratCast, Complex.norm_ratCast]
  rw [h1, Finset.prod_coe_sort Ψ fun τ => ‖τ t‖ ^ 2, ← Finset.prod_mul_prod_compl Ψ,
    Finset.prod_pow, sq]
  congr 1
  symm
  refine Finset.prod_bij' (fun τ _ => ComplexEmbedding.conjugate τ)
    (fun τ _ => ComplexEmbedding.conjugate τ) ?_ ?_ ?_ ?_ ?_
  · intro a ha; simpa using (h a).1 ha
  · intro a ha
    have := h a
    simp only [Finset.mem_compl] at ha
    tauto
  · intro a _; exact star_star a
  · intro a _; exact star_star a
  · intro a _; simp only [ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj]

theorem isSB_of_adm {M R : ℕ} {φ : Fam E n N} (h : admitted M R φ) {Λ : Lt E n}
    (hΛ : Λ ∈ Vset E n M) : IsSB (φ Λ) := by
  obtain ⟨s, hs, -, h1, h2⟩ := hΛ.2.2
  refine ⟨s * R, Nat.mul_pos hs h.pos.2, fun x hx k a => ?_, fun x y hy => ?_⟩
  · rw [Nat.cast_mul, mul_smul]
    exact (Base.mem_stdL _).1 (h1 _ (h.supp Λ hΛ x hx a)) k
  · rw [Nat.cast_mul, mul_comm, mul_smul]
    exact h.per Λ hΛ x _ fun a => h2 _ ((Base.mem_stdL _).2 fun k => hy k a)

theorem bounded_of_adm {M R : ℕ} {φ : Fam E n N} (h : admitted M R φ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ Λ ∈ Vset E n M, ∀ x, ‖φ Λ x‖ ≤ B := by
  haveI : Finite (Cls E n M) := (finite_cls_and_stab E n M h.pos.1).1
  have h1 : ∀ c : Cls E n M, ∃ B : ℝ, ∀ x, ‖φ (Quot.out c).1 x‖ ≤ B := fun c => by
    obtain ⟨S, hS, hl⟩ := isSB_of_adm h (Quot.out c).2
    exact (ip_self_nonneg_and_bounds E _ _ S _ hS hl).2.2.2.2.1
  choose b hb using h1
  obtain ⟨B, hB⟩ := (Set.finite_range b).bddAbove
  refine ⟨max B 0, le_max_right _ _, fun Λ hΛ x => ?_⟩
  set c : Cls E n M := Quot.mk _ ⟨Λ, hΛ⟩ with hc
  obtain ⟨g, hg, hm⟩ := (Base.cls_eq_iff ⟨Λ, hΛ⟩ (Quot.out c)).1 (Quot.out_eq c).symm
  rw [← h.equiv g hg Λ hΛ _ (Quot.out c).2 hm x]
  exact ((hb c _).trans (hB ⟨c, rfl⟩)).trans (le_max_left _ _)

theorem det_ccT (a : Matrix (Fin N) (Fin N) E) : (ccT a).det = cc a.det := by
  rw [ccT, Matrix.det_transpose]
  exact ((IsCMField.complexConj E).toRingEquiv.toRingHom.map_det a).symm

theorem diag_mem_UU {a d : Matrix (Fin N) (Fin N) E} (h : ccT a * d = 1) :
    Matrix.fromBlocks a 0 0 d ∈ UU E N := by
  have h' : ccT d * a = 1 := by
    have := congrArg ccT h
    rwa [Base.ccT_mul, Base.ccT_ccT, Base.ccT_one] at this
  have e : ccT (Matrix.fromBlocks a 0 0 d : M2 E N) = Matrix.fromBlocks (ccT a) 0 0 (ccT d) := by
    ext (i | i) (j | j) <;> simp [ccT, cc]
  change ccT _ * _ * _ = _
  rw [e, Matrix.J, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [h, h']

theorem exists_moved (hΨ : IsType Ψ) (hn : Even n) (hN : 4 * N < n) {M : ℕ} (hM : 0 < M)
    {φ : Fam E n N} (hφ : ∀ Λ ∈ Vset E n M, IsSB (φ Λ)) {a : Matrix (Fin N) (Fin N) E}
    (ha : a.det ≠ 0) (hψ : ∀ Λ ∈ Vset E n M, IsSB fun x => φ Λ (x * a))
    {Z : CM Ψ N N} (hZ : Z ∈ Hn Ψ N) : ∃ Z' ∈ Hn Ψ N,
      swd Ψ M (fun Λ x => φ Λ (x * a)) Z' 0 0 = swd Ψ M φ Z 0 0 ∧
        detIm Z' = |((Algebra.norm ℚ a.det : ℚ) : ℝ)| * detIm Z := by
  have ha' : (ccT a).det ≠ 0 := by
    rw [det_ccT]; simpa [cc] using ha
  set d := (ccT a)⁻¹ with hd
  have had : ccT a * d = 1 := Matrix.mul_nonsing_inv _ ha'.isUnit
  have hdet : cc a.det * d.det = 1 := by rw [← det_ccT, ← Matrix.det_mul, had, Matrix.det_one]
  have hd0 : d.det ≠ 0 := right_ne_zero_of_mul_eq_one hdet
  set γ : M2 E N := Matrix.fromBlocks a 0 0 d with hγ
  have hU : γ ∈ UU E N := diag_mem_UU had
  obtain ⟨-, hZ', hIm, -⟩ := (unitary_act_halfSpace E Ψ N γ hU).2 Z hZ
  have hden : ∀ τ, (hDen Ψ γ Z τ).det = τ.1 d.det := fun τ => by
    simp only [hDen, hγ, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂,
      Matrix.map_zero _ (map_zero τ.1), Matrix.zero_mul, zero_add]
    exact (τ.1.map_det d).symm
  set k : ℂ := ∏ τ : Ψ, τ.1 d.det ^ n with hk
  have hk0 : k ≠ 0 := Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ (by simpa using hd0)
  have hfac : hFac Ψ γ Z (0 : CM Ψ n N) 0 = k := by
    have h : ∀ (τ : Ψ) (k : Fin n), (0 : CM Ψ n N) τ k = 0 := fun _ _ => rfl
    simp only [hFac, hden, h, zero_dotProduct, Finset.sum_const_zero, mul_zero, Complex.exp_zero,
      mul_one, hk]
  refine ⟨_, hZ', ?_, ?_⟩
  · have h1 := (GlobalTheory.T.siegelWeilDifference_automorphy_linearity E Ψ hΨ n N hn hN M φ hM hφ Z hZ).1 γ hU
    have h2 := (GlobalTheory.T.siegelWeilDifference_automorphy_linearity E Ψ hΨ n N hn hN M (fun Λ x => φ Λ (x * a)) hM hψ _ hZ').2.2.2.1 k
    apply mul_left_cancel₀ hk0
    rw [← h2, ← hfac, ← h1, hfac]
    refine Base.classSum_congr fun Λ hΛ => ?_
    have : weil Ψ γ (φ Λ) = (k • fun Λ x => φ Λ (x * a) : Fam E n N) Λ := by
      funext x
      rw [(GlobalTheory.T.hermitianWeilAction_siegelParabolic_explicit E Ψ hΨ n N hn (φ Λ) (hφ Λ hΛ)).1 γ hU rfl x]
      simp [hγ, chiH, hk]
    simp only [this]
  · rw [← hIm, abs_norm_eq hΨ, mul_left_comm, ← Finset.prod_mul_distrib,
      Finset.prod_eq_one, mul_one]
    intro τ _
    rw [hden, ← mul_pow, ← Complex.norm_conj (τ.1 a.det), ← Base.map_cc, ← norm_mul, ← map_mul,
      hdet]
    simp


omit [NumberField E] [IsCMField E] in
theorem detIm_nonneg {Z : CM Ψ N N} (hZ : Z ∈ Hn Ψ N) : 0 ≤ detIm Z :=
  Finset.prod_nonneg fun τ _ => (Complex.pos_iff.1 (hZ τ).det_pos).1.le

end GlobalTheory.SW.TwistBound

namespace GlobalTheory.SW


open TwistBound in
theorem twist_swd_bounded : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * (N + 1) < n → SWAt Ψ n N → ∀ (M R : ℕ) (φ : Fam E n (N + 1)), admitted M R φ → ∃ C : ℝ, ∀ 𝔛 : Lt E (N + 1), 𝔛.FG → Agree (R * M) 𝔛 (stdL E (N + 1)) → ∀ Z ∈ Hn Ψ (N + 1), gidx 𝔛 ^ ((n : ℝ) / 2) * ‖swd Ψ M (twist R 𝔛 φ) Z 0 0‖ * detIm Z ^ ((n : ℝ) / 2) ≤ C := by
  intro E _ _ _ Ψ hΨ n N hn hN hSW M R φ hφ
  obtain ⟨B, hB0, hB⟩ := bounded_of_adm hφ
  obtain ⟨c, C₁, -, h1⟩ := GlobalTheory.T.exists_rational_matrix_move_admissible_uniform_level E (N + 1)
  obtain ⟨C₂, h2⟩ := GlobalTheory.T.siegelWeil_difference_invariant_norm_bounded E Ψ hΨ n N hn hN hSW M (R * c)
  refine ⟨max C₁ 0 ^ ((n : ℝ) / 2) * (C₂ * B), fun 𝔛 hfg hag Z hZ => ?_⟩
  obtain ⟨a, ha, hidx, hadm⟩ := h1 n M R φ 𝔛 hφ hfg hag
  obtain ⟨-, -, -, hpos, ⟨R', hR'⟩, -⟩ := twist_admissible E n (N + 1) M R φ 𝔛 hφ hfg hag
  obtain ⟨Z', hZ', e1, e2⟩ := exists_moved hΨ hn hN hφ.pos.1 (fun Λ hΛ => isSB_of_adm hR' hΛ) ha
    (fun Λ hΛ => isSB_of_adm hadm hΛ) hZ
  have h3 := h2 _ hadm B (fun Λ hΛ x => by
    unfold twist
    split_ifs
    · exact hB Λ hΛ _
    · simpa using hB0) Z' hZ'
  have hD := detIm_nonneg hZ
  replace h3 : ‖swd Ψ M (twist R 𝔛 φ) Z 0 0‖ * detIm Z' ^ ((n : ℝ) / 2) ≤ C₂ * B := by
    rw [← e1]; exact h3
  rw [e2, Real.mul_rpow (abs_nonneg _) hD] at h3
  have h4 : gidx 𝔛 ^ ((n : ℝ) / 2) ≤
      max C₁ 0 ^ ((n : ℝ) / 2) * |((Algebra.norm ℚ a.det : ℚ) : ℝ)| ^ ((n : ℝ) / 2) := by
    rw [← Real.mul_rpow (le_max_right _ _) (abs_nonneg _)]
    exact Real.rpow_le_rpow hpos.le
      (hidx.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))) (by positivity)
  have h5 : 0 ≤ max C₁ 0 ^ ((n : ℝ) / 2) := Real.rpow_nonneg (le_max_right _ _) _
  calc _ ≤ (max C₁ 0 ^ ((n : ℝ) / 2) * |((Algebra.norm ℚ a.det : ℚ) : ℝ)| ^ ((n : ℝ) / 2)) *
        ‖swd Ψ M (twist R 𝔛 φ) Z 0 0‖ * detIm Z ^ ((n : ℝ) / 2) := by gcongr
    _ = max C₁ 0 ^ ((n : ℝ) / 2) * (‖swd Ψ M (twist R 𝔛 φ) Z 0 0‖ *
        (|((Algebra.norm ℚ a.det : ℚ) : ℝ)| ^ ((n : ℝ) / 2) * detIm Z ^ ((n : ℝ) / 2))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h3 h5

end GlobalTheory.SW
end

section

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.Ker.RealHeis

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} (X : Data E r)
  (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (x : Frame X.Ψ r)

theorem hx_add_left (z z' w : Fin g → ℂ) :
    hx X bas idx x (z + z') w = hx X bas idx x z w + hx X bas idx x z' w := by
  simp only [GlobalTheory.Dict.hx, mulVec_add, add_dotProduct]

theorem hx_add_right (z w w' : Fin g → ℂ) :
    hx X bas idx x z (w + w') = hx X bas idx x z w + hx X bas idx x z w' := by
  simp only [GlobalTheory.Dict.hx, mulVec_add, star_add, dotProduct_add]

theorem hx_smul_left (c : ℂ) (z w : Fin g → ℂ) :
    hx X bas idx x (c • z) w = c * hx X bas idx x z w := by
  simp only [GlobalTheory.Dict.hx, mulVec_smul, smul_dotProduct, smul_eq_mul]

theorem contDiff_gaussR : ContDiff ℝ (⊤ : ℕ∞) (gaussR X bas idx x : (Fin n → Fin g → ℂ) → ℂ) := by
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ => star z) := Complex.conjCLE.contDiff
  have h1 : ∀ (k : Fin n) (i : Fin g), ContDiff ℝ (⊤ : ℕ∞)
      fun z : Fin n → Fin g → ℂ => (hMat X bas idx x *ᵥ z k) i := by
    intro k i
    simp only [mulVec, dotProduct]
    fun_prop
  have h2 : ∀ k : Fin n, ContDiff ℝ (⊤ : ℕ∞)
      fun z : Fin n → Fin g → ℂ => hx X bas idx x (z k) (z k) := by
    intro k
    change ContDiff ℝ _ fun z : Fin n → Fin g → ℂ => ∑ i, (hMat X bas idx x *ᵥ z k) i *
      ∑ j, imInv X bas idx x i j * star ((hMat X bas idx x *ᵥ z k) j)
    exact ContDiff.sum fun i _ => (h1 k i).mul
      (ContDiff.sum fun j _ => contDiff_const.mul (hc.comp (h1 k j)))
  exact (contDiff_const.mul (ContDiff.sum fun k _ => h2 k)).neg.cexp

theorem gaussR_mul_factor (hsym : ∀ z w, hx X bas idx x w z = conj (hx X bas idx x z w))
    (z a : Fin n → Fin g → ℂ) :
    gaussR X bas idx x z * cexp (-(π * ∑ k, hx X bas idx x (z k + (1 / 2 : ℂ) • a k) (a k))) =
      cexp (-(π * I * ((∑ k, hx X bas idx x (z k) (a k)).im : ℝ))) * gaussR X bas idx x (z + a) := by
  have h1 : ∑ k, hx X bas idx x (a k) (z k) = conj (∑ k, hx X bas idx x (z k) (a k)) := by

    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => hsym _ _
  simp only [gaussR, ← Complex.exp_add, Pi.add_apply, hx_add_left, hx_add_right, hx_smul_left,
    Finset.sum_add_distrib, ← Finset.mul_sum, h1]
  congr 1
  generalize ∑ k, hx X bas idx x (z k) (a k) = S
  have h2 := Complex.sub_conj S
  push_cast at h2
  linear_combination (-(π : ℂ) / 2) * h2

end GlobalTheory.Ker.RealHeis

namespace GlobalTheory.Ker

theorem thR_laws : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ x ∈ X.dom, ∀ φ : TF n g, IsSB φ → ContDiff ℝ (⊤ : ℕ∞) (thR X bas idx φ x : WR X n → ℂ) ∧ (∀ (y : Matrix (Fin n) (Fin r) E) (v : WR X n), thR X bas idx (heisG X bas y φ) x v = cexp (-(π * I * (EFR X v (embR X y) : ℝ))) * thR X bas idx φ x (v + embR X y)) ∧ (∀ γ : GL (Fin r) E, IsUn X γ → ∀ v : WR X n, thR X bas idx (wG X bas idx γ φ) (lact γ x) (fun τ k => ((γ : Matrix (Fin r) (Fin r) E).map τ.1) *ᵥ v τ k) = thR X bas idx φ x v) ∧ (∀ ψ, IsSB ψ → (thR X bas idx φ x = (thR X bas idx ψ x : WR X n → ℂ) → φ = ψ) ∧ thR X bas idx (φ + ψ) x = (thR X bas idx φ x + thR X bas idx ψ x : WR X n → ℂ)) ∧ ∀ a : ℂ, thR X bas idx (a • φ) x = (a • thR X bas idx φ x : WR X n → ℂ) := by
  intro E _ _ _ r X g q0 hr bas idx n hs hn x hxd φ hφ
  obtain ⟨⟨L, hL⟩, him, -, -, hinv⟩ := GlobalTheory.T.realPeriodMap_homeomorph_riemannForm_density E r X g q0 hr bas idx n hs hn x hxd
  obtain ⟨hsym, -, -, -, -, -, -, hga⟩ := GlobalTheory.Dict.hx_laws E r X g bas idx n hs hn x hxd
  have hLf : zR X idx x = (L : WR X n → Fin n → Fin g → ℂ) := funext fun v => (hL v).symm
  refine ⟨?_, fun y v => ?_, fun γ hγ v => ?_, fun ψ hψ => ⟨fun h => ?_, ?_⟩, fun a => ?_⟩
  · have h1 : ContDiff ℝ (⊤ : ℕ∞) (thA X bas idx φ x) :=
      (AnalyticOnNhd.contDiff (𝕜 := ℂ) (SCV.analyticOnNhd_of_differentiable
        (ThetaHol.differentiable_thA idx hs hφ hxd) _)).restrict_scalars ℝ
    have h2 := ((RealHeis.contDiff_gaussR X bas idx x).mul h1).comp L.contDiff
    rw [← hLf] at h2
    exact h2
  · have h1 := ((heisG_laws E r X g bas idx n hs hn).2.2.2 y φ hφ).2.2.2.2 x hxd (zR X idx x v)
    have h2 : zR X idx x (v + embR X y) = zR X idx x v + zR X idx x (embR X y) := by
      rw [hLf, map_add (f := _)]
    have h3 := RealHeis.gaussR_mul_factor X bas idx x hsym (zR X idx x v) (zR X idx x (embR X y))
    rw [him] at h3
    rw [thR, thR, h1, h2, ← _root_.mul_assoc, ← _root_.mul_assoc, ← h3]
    rfl
  · rw [thR, thR, hinv γ hγ v, (wG_laws E r X g bas idx n hs hn γ hγ φ hφ).2.1 x hxd]
    simp only [gaussR, (hga γ hγ).2.2.2]
  · have hone : IsUn X (1 : GL (Fin r) E) := fun u w => by simp
    refine ((wG_laws E r X g bas idx n hs hn 1 hone φ hφ).2.2.1 ψ hψ).2.2 x hxd ?_
    funext z
    obtain ⟨v, rfl⟩ := L.surjective z
    have h1 := congrFun h v
    rw [thR, thR, ← hL] at h1
    exact mul_left_cancel₀ (Complex.exp_ne_zero _) h1
  · funext v
    simp only [thR, UnAct.thA_add idx hs hxd hφ hψ, Pi.add_apply, mul_add]
  · funext v
    simp only [thR, UnAct.thA_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm]

end GlobalTheory.Ker
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

theorem _root_.GlobalTheory.T.heisenbergVacuum_projection_rootOfUnity_phases : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ L : Lt E r, SelfD X L → ∀ v : TF n g, IsVac X bas w (tens (stdL E n) L) v → ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ Λ ∈ Vset E n 1, IsVac X bas w (tens Λ L) (unitv (projA X bas w (tens Λ L) v)) ∧ PV (u • unitv (projA X bas w (tens Λ L) v)) ∧ projA X bas w (tens Λ L) v = ((Real.sqrt (((stdL E n).toAddSubgroup.relIndex Λ.toAddSubgroup ^ r : ℕ) : ℝ) : ℝ) : ℂ)⁻¹ • unitv (projA X bas w (tens Λ L) v) := by
  first | exact @GlobalTheory.Phase.Proj.proj_phases | exact GlobalTheory.Phase.Proj.proj_phases | (intros; apply GlobalTheory.Phase.Proj.proj_phases <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.GPhi

theorem finite_quot {G : Type} [AddCommGroup G] {A B C : AddSubgroup G} (hC : C.FG) (hA : A ≤ C) {m : ℕ}
    (hm : 0 < m) (h : ∀ y ∈ A, m • y ∈ B) : Finite (A ⧸ B.addSubgroupOf A) := by
  have h1 : (AddSubgroup.toIntSubmodule C).FG := (Submodule.fg_iff_addSubgroup_fg _).2 hC
  have h2 : (AddSubgroup.toIntSubmodule A).FG := h1.of_le hA
  have h3 : A.FG := (Submodule.fg_iff_addSubgroup_fg _).1 h2
  have : AddGroup.FG A := (AddGroup.fg_iff_addSubgroup_fg A).2 h3
  refine AddCommGroup.finite_of_fg_isAddTorsion _ fun q => ?_
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective q
  refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨m, hm, ?_⟩
  rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
  exact h y y.2

theorem finsum_exchange {Q C V : Type} [Finite Q] [Finite C] [AddCommGroup V] [Module ℂ V] (t : ℂ) (a : C → ℂ)
    (e : C → Q → ℂ) (f : Q → V) :
    ∑ᶠ q, (t * ∑ᶠ c, a c * e c q) • f q = t • ∑ᶠ c, a c • ∑ᶠ q, e c q • f q := by
  have := Fintype.ofFinite Q
  have := Fintype.ofFinite C
  simp only [finsum_eq_sum_of_fintype, Finset.smul_sum, Finset.mul_sum, Finset.sum_smul, mul_smul]
  exact Finset.sum_comm

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem finite_levQ {H : Host E} (Dw : Datum H) (l : Geo.Tor.Level H) : Finite (LevQ Dw l) := by
  have hM : l.Mb ≠ ⊥ := by
    intro h
    have h₁ := l.prod
    rw [h, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot] at h₁
    have h₂ : l.M = 0 := by exact_mod_cast h₁
    have := l.three_le
    omega
  have := l.Mb.finiteQuotientOfFreeOfNeBot hM
  have := Dw.fin
  exact Submodule.finite_quotient_smul l.Mb (N := (⊤ : Submodule (𝓞 E) Dw.La)) Module.Finite.fg_top

theorem natCast_mem_Mfr {H : Host E} (l : Geo.Tor.Level H) : (l.M : 𝓞 E) ∈ Mfr l := by
  have h : Ideal.span {(l.M : 𝓞 E)} ≤ Mfr l := l.prod.symm.le.trans Ideal.mul_le_right
  exact h (Ideal.mem_span_singleton_self _)

theorem gphi_eq_smul_phiF : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) [Algebra c.F ℂ] [Algebra d.c₂.F ℂ], (∀ t : c.F, algebraMap d.c₂.F ℂ (d.eF t) = algebraMap c.F ℂ t) → d.IsLev → ∀ (ph : (Fin n → LaJ Xo c d) → c.F) (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ) (x₀ : Fin n → LaJ Xo c d), d.PhiPin ph ψ x₀ → ∀ (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (D : SW.Level X) (hn : r ≤ n), IsSympl X bas → Even n → r = Dw.p + Dw.q → LevTie d (algebraMap c.F ℂ) ph D hn → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ x0 : Fin n → Dw.La, ∃ (ρ : ℝ) (s : Lt E n → ℝ), 0 < ρ ∧ ∀ L ∈ D.lats, ∀ (mk mk₂ δ : Dw.La →ₗ[𝓞 E] (Fin r → E)) (v : TF n g), IsMark l L mk → IsMark d.l₂ L mk₂ → MarkOver l d.l₂ L mk mk₂ → IsDual X l (algebraMap c.F ℂ (zetaM c)) L mk δ → IsBaseClassLevelAdapted d D hn x0 δ → IsVac X bas (H.w0 : E) (tens (stdL E n) L) v → ∃ t : ℂ, ‖t‖ = ρ ∧ ∀ Λ ∈ Vset E n d.l₂.M, 0 < s Λ ∧ ∀ N : ℕ, NOK Λ N d.l₂.M → ∀ Y : (Fin n → LevQ Dw d.l₂) → Matrix (Fin n) (Fin r) E, IsRoots d.l₂ L mk₂ N Y → gphi X bas (H.w0 : E) Λ L v (fun q => algebraMap d.c₂.F ℂ (d.w x0 q)) Y = (t * (s Λ : ℂ)) • phiF bas D (Mfr l) hn v₀ L Λ := by
  intro E _ _ _ H Dw l Xo c n d _ _ hF hlev ph ψ x₀ hpin r g X bas idx D hn hs hev hr tie v₀ hv₀ x0
  have hM0 : 0 < d.l₂.M := by have := d.l₂.three_le; omega
  have hM : (d.l₂.M : 𝓞 E) ∈ D.𝔪 := tie.m ▸ natCast_mem_Mfr d.l₂
  have := finite_levQ Dw d.l₂
  obtain ⟨ρ, s, hρ, hsv⟩ := ShVac.shift_vac E r X g bas idx n hs hev D _ hM0 hM v₀ hv₀
  have hcard : 0 < Nat.card (Fin n → LevQ Dw d.l₂) := Nat.card_pos
  refine ⟨Nat.card (Fin n → LevQ Dw d.l₂) * ρ, s, mul_pos (by exact_mod_cast hcard) hρ, ?_⟩
  intro L hL mk mk₂ δ v h1 h2 h12 hd hx hv
  rw [← tie.w] at hv ⊢
  obtain ⟨t₁, ht₁, H₁⟩ := GlobalTheory.T.coverFourierCoeff_eq_finite_fourier_sum E H Dw l Xo c n d hF hlev ph ψ x₀ hpin r X D hn hr tie L hL mk mk₂ δ x0
    h1 h2 h12 hd hx
  obtain ⟨t₂, ht₂, H₂⟩ := hsv L hL v hv
  refine ⟨t₁ * (Nat.card (Fin n → LevQ Dw d.l₂) * t₂), by rw [norm_mul, norm_mul, ht₁, ht₂, Complex.norm_natCast, _root_.one_mul],
    fun Λ hΛ => ⟨(H₂ Λ hΛ).1, fun N hN Y hY => ?_⟩⟩
  obtain ⟨⟨u, hu⟩, -, hp, -⟩ := TensVac.vacua E r X g bas idx n hs hev D.w D.w_int D.w_tr L hL.1 _ Λ hΛ
  have hfg := (GlobalTheory.T.tensorLattice_selfDual_semicharacter_index E r X g bas idx n hs hev D.w D.w_int D.w_tr L hL.1 _ Λ hΛ).1
  have hfin : Finite (tens Λ ((Ideal.span {2} * conjI D.𝔪) • L) ⧸
      (tens Λ ((Ideal.span {2} * conjI D.𝔪 * D.𝔪) • L)).addSubgroupOf _) := by
    refine finite_quot hfg ?_ hM0 (ShVac.nsmul_tens_right fun x hx => ?_)
    · intro y hy
      simpa using ShVac.nsmul_tens_right (Λ := Λ) (k := 1) (L' := L)
        (fun x hx => by simpa using Submodule.smul_le_right hx) y hy
    · rw [mul_comm _ D.𝔪, Submodule.mul_smul]
      exact Submodule.smul_mem_smul hM hx
  have hP := GlobalTheory.T.fourier_translates_vacuum_roots_levelPoints E H Dw d.l₂ r g X bas idx n hs hev D.w D.w_int D.w_tr L mk₂ hL.1 h2 Λ hΛ N hN Y hY
    (projA X bas D.w (tens Λ L) v) (by rw [hp v hv.1 u hu]; exact TensVac.sb_smul _ hu.1)
    (fun y hy => by rw [hp v hv.1 u hu, TensVac.heisG_smul, smul_comm, hu.2.2 y hy])
  rw [← tie.m] at hP
  have e := (H₂ Λ hΛ).2
  rw [Level.sh] at e
  unfold gphi phiF
  simp only [H₁ Λ hΛ N hN Y hY]
  rw [finsum_exchange]
  simp only [fun cl : tens Λ ((Ideal.span {2} * conjI D.𝔪) • L) => hP cl cl.2, e, TensVac.heisG_smul]
  have := Fintype.ofFinite (tens Λ ((Ideal.span {2} * conjI D.𝔪) • L) ⧸
      (tens Λ ((Ideal.span {2} * conjI D.𝔪 * D.𝔪) • L)).addSubgroupOf _)
  simp only [finsum_eq_sum_of_fintype, Finset.smul_sum, smul_smul, Level.sh]
  refine Finset.sum_congr rfl fun cl _ => ?_
  congr 1
  ring

end GlobalTheory.Dict.GPhi
end

section

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

theorem _root_.GlobalTheory.T.doubledHermitianTestFunction_spec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ φ₁ φ₂ : TF n g, IsSB φ₁ → IsSB φ₂ → IsSB (dbl X bas idx φ₁ φ₂) ∧ IsDbl X bas idx φ₁ φ₂ (dbl X bas idx φ₁ φ₂) ∧ ∀ ψ, IsSB ψ → IsDbl X bas idx φ₁ φ₂ ψ → ψ = dbl X bas idx φ₁ φ₂ := by
  first | exact @GlobalTheory.SW.DblEx.dbl_spec | exact GlobalTheory.SW.DblEx.dbl_spec | (intros; apply GlobalTheory.SW.DblEx.dbl_spec <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.KernelCompare

variable {D : D7} {S T : HSp D}

theorem isTh_uVec (C : Ctx S T) (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) {f : WO S T → ℂ} (hf : C.IsTh f) :
    C.IsTh (C.uVec Lv hn f) := by
  obtain ⟨h0, h1, h2⟩ := GlobalTheory.ThetaSpace.theta_space_laws D S T C
  exact finsum_induction C.IsTh h0 (fun x y hx hy => (h1 x y hx hy).1)
    fun c => (h2 _ ((h2 f hf).2.1 _)).1 _

end GlobalTheory.Ker.KernelCompare
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaFunction_space_heisenberg_laws : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), C.IsTh 0 ∧ (∀ f f', C.IsTh f → C.IsTh f' → C.IsTh (f + f') ∧ ((∀ w, IsRealPt w → f w = f' w) → f = f')) ∧ ∀ f, C.IsTh f → (∀ a : ℂ, C.IsTh (a • f)) ∧ (∀ w, C.IsTh (C.rho w f)) ∧ (∀ w w', C.rho w (C.rho w' f) = C.ψ (symplOH S T w w') • C.rho (w + w') f) ∧ (∀ (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) w, IsRealPt w → C.rho (finW S T y) f w = cexp (π * I * (EFR C.X (C.realPt w) (embR C.X y) : ℝ)) * f (w - (ratW T S yᵀ - finW S T y))) ∧ (∀ γ ∈ GQ S, ∀ γ' ∈ GQ T, C.IsTh fun w => f (actO S T γ γ' w)) ∧ ∃ N : ℕ, 0 < N ∧ ∀ u ∈ hatA S T (tens (stdL D.host.E S.rank) C.X.Λ), C.rho (N • u) f = f := by
  first | exact @GlobalTheory.ThetaSpace.theta_space_laws | exact GlobalTheory.ThetaSpace.theta_space_laws | (intros; apply GlobalTheory.ThetaSpace.theta_space_laws <;> assumption)
end
