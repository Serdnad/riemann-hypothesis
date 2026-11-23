module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Flat.TorsionFree

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

private lemma sum_castLE_lemma {r k : ℕ} (hk : k ≤ r) (f : Fin r → ℂ)
    (hf : ∀ j : Fin r, k ≤ (j : ℕ) → f j = 0) : ∑ j, f j = ∑ j : Fin k, f (Fin.castLE hk j) := by
  have hr : r = k + (r - k) := (Nat.add_sub_cancel' hk).symm
  rw [← Equiv.sum_comp (finCongr hr.symm), Fin.sum_univ_add]
  have h2 : ∑ a : Fin (r - k), f (finCongr hr.symm (Fin.natAdd k a)) = 0 :=
    Finset.sum_eq_zero fun a _ => hf _ (by simp)
  rw [h2, add_zero]
  exact Finset.sum_congr rfl fun j _ => congrArg f (Fin.ext (by simp))

lemma rmul_mem_dom {z b : Frame X.Ψ r} (hz : z ∈ X.dom) (hb : b ∈ Bor X.Ψ r) : rmul z b ∈ X.dom := by
  intro τ
  obtain ⟨hz1, hz2⟩ := hz τ
  obtain ⟨hb1, hb2⟩ := hb τ
  have hmat : mat (rmul z b) τ = mat z τ * mat b τ := rfl
  have hgram : ∀ M : Matrix (Fin r) (Fin r) ℂ,
      gram τ.1 X.Gm M = Mᵀ * X.Gm.map τ.1 * M.map (starRingEnd ℂ) := by
    intro M
    ext a c
    simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hprod : gram τ.1 X.Gm (mat z τ * mat b τ) =
      (mat b τ)ᵀ * gram τ.1 X.Gm (mat z τ) * (mat b τ).map (starRingEnd ℂ) := by
    rw [hgram, hgram, Matrix.transpose_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
  have htri : ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ), (∀ a c : Fin n, c < a → M a c = 0) →
      M.det = ∏ a, M a a :=
    fun n M h => Matrix.det_of_upperTriangular (fun a c hca => h a c hca)
  have hdiag : ∀ a, mat b τ a a ≠ 0 := by
    have h0 := hb1
    rw [htri r (mat b τ) hb2] at h0
    exact fun a => Finset.prod_ne_zero_iff.mp h0 a (Finset.mem_univ a)
  refine ⟨by rw [hmat, Matrix.det_mul]; exact mul_ne_zero hz1 hb1, fun i => ?_⟩
  have hk : (i : ℕ) ≤ r := Nat.le_of_lt_succ i.isLt
  have hsub : ((mat b τ)ᵀ * gram τ.1 X.Gm (mat z τ) * (mat b τ).map (starRingEnd ℂ)).submatrix
        (Fin.castLE hk) (Fin.castLE hk) =
      ((mat b τ).submatrix (Fin.castLE hk) (Fin.castLE hk))ᵀ *
        (gram τ.1 X.Gm (mat z τ)).submatrix (Fin.castLE hk) (Fin.castLE hk) *
        ((mat b τ).submatrix (Fin.castLE hk) (Fin.castLE hk)).map (starRingEnd ℂ) := by
    ext a c
    simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
    refine (sum_castLE_lemma hk _ ?_).trans (Finset.sum_congr rfl fun l _ => ?_)
    · intro l hl
      have hc := c.isLt
      have h0 : mat b τ l (Fin.castLE hk c) = 0 :=
        hb2 l (Fin.castLE hk c) (by rw [Fin.lt_iff_val_lt_val, Fin.coe_castLE]; omega)
      exact mul_eq_zero_of_right _ ((map_eq_zero _).mpr h0)
    · refine congrArg (fun s => s * _) (sum_castLE_lemma hk _ ?_)
      intro j hj
      have ha := a.isLt
      have h0 : mat b τ j (Fin.castLE hk a) = 0 :=
        hb2 j (Fin.castLE hk a) (by rw [Fin.lt_iff_val_lt_val, Fin.coe_castLE]; omega)
      exact mul_eq_zero_of_left h0 _
  set d := ((mat b τ).submatrix (Fin.castLE hk) (Fin.castLE hk)).det with hd
  have hdne : d ≠ 0 := by
    rw [hd, htri (i : ℕ) ((mat b τ).submatrix (Fin.castLE hk) (Fin.castLE hk))
      (fun a c h => hb2 _ _ (by rw [Fin.lt_iff_val_lt_val, Fin.coe_castLE, Fin.coe_castLE]; exact h))]
    exact Finset.prod_ne_zero_iff.mpr fun a _ => hdiag (Fin.castLE hk a)
  have hdetmap : (((mat b τ).submatrix (Fin.castLE hk) (Fin.castLE hk)).map (starRingEnd ℂ)).det =
      starRingEnd ℂ d := by
    rw [hd, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  have hclaim : dmin X.Gm (rmul z b) τ i = ((Complex.normSq d : ℝ) : ℂ) * dmin X.Gm z τ i := by
    unfold dmin lminor
    rw [hmat, hprod, hsub, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdetmap, ← hd,
      mul_right_comm, Complex.mul_conj]
  rw [hclaim, Complex.re_ofReal_mul]
  have hpos : 0 < Complex.normSq d := Complex.normSq_pos.mpr hdne
  calc (0 : ℝ) < Complex.normSq d * (psgn X.p0 i * (dmin X.Gm z τ i).re) := mul_pos hpos (hz2 i)
    _ = _ := by ring

lemma opN_smul_le {m n : ℕ} (t : ℂ) (A : Matrix (Fin m) (Fin n) ℂ) :
    Data.opN (t • A) ≤ ‖t‖ * Data.opN A := by
  unfold Data.opN
  have key : ∀ v : Fin n → ℂ,
      Real.sqrt (∑ i, ‖Matrix.mulVec (t • A) v i‖ ^ 2) / Real.sqrt (∑ j, ‖v j‖ ^ 2) =
        ‖t‖ * (Real.sqrt (∑ i, ‖Matrix.mulVec A v i‖ ^ 2) / Real.sqrt (∑ j, ‖v j‖ ^ 2)) := by
    intro v
    have h1 : ∑ i, ‖Matrix.mulVec (t • A) v i‖ ^ 2 = ‖t‖ ^ 2 * ∑ i, ‖Matrix.mulVec A v i‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hmv : Matrix.mulVec (t • A) v i = t * Matrix.mulVec A v i := by
        simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
      rw [hmv, norm_mul, mul_pow]
    rw [h1, Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg t), mul_div_assoc]
  open scoped Pointwise in
  have hS : {s | ∃ v : Fin n → ℂ, v ≠ 0 ∧
        s = Real.sqrt (∑ i, ‖Matrix.mulVec (t • A) v i‖ ^ 2) / Real.sqrt (∑ j, ‖v j‖ ^ 2)} =
      ‖t‖ • {s | ∃ v : Fin n → ℂ, v ≠ 0 ∧
        s = Real.sqrt (∑ i, ‖Matrix.mulVec A v i‖ ^ 2) / Real.sqrt (∑ j, ‖v j‖ ^ 2)} := by
    ext s
    simp only [Set.mem_smul_set, Set.mem_setOf_eq]
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨_, ⟨v, hv, rfl⟩, ?_⟩
      rw [smul_eq_mul, key v]
    · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨v, hv, by rw [smul_eq_mul, key v]⟩
  refine le_of_eq ?_
  rw [hS, Real.sSup_smul_of_nonneg (norm_nonneg t), smul_eq_mul]

private lemma opN_nonneg' {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) : 0 ≤ Data.opN A := by
  unfold Data.opN
  apply Real.sSup_nonneg
  rintro s ⟨v, _, rfl⟩
  positivity

lemma zN_nonneg (Z : X.Coord) : 0 ≤ X.zN Z := by
  unfold Data.zN
  exact Real.iSup_nonneg fun τ => opN_nonneg' _

lemma zN_smul_le (t : ℂ) (Z : X.Coord) : X.zN (t • Z) ≤ ‖t‖ * X.zN Z := by
  unfold Data.zN
  refine Real.iSup_le (fun τ => ?_) (mul_nonneg (norm_nonneg t) (zN_nonneg X Z))
  have h1 : Data.opN (Matrix.of ((t • Z) τ)) ≤ ‖t‖ * Data.opN (Matrix.of (Z τ)) :=
    opN_smul_le t (Matrix.of (Z τ))
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg t))
  exact le_ciSup (f := fun τ : X.Ψ => Data.opN (Matrix.of (Z τ))) (Set.finite_range _).bddAbove τ

lemma xZ_diff (x : Frame X.Ψ r) : Differentiable ℂ fun Z : X.Coord => X.xZ x Z := by
  rw [differentiable_pi]
  intro τ
  rw [differentiable_pi]
  intro a
  rw [differentiable_pi]
  intro b
  have hL : ∀ j, Differentiable ℂ fun Z : X.Coord => X.lowBlock Z τ j b := by
    intro j
    simp only [Data.lowBlock, Matrix.of_apply]
    split_ifs <;> fun_prop
  show Differentiable ℂ fun Z : X.Coord => ∑ j, mat x τ a j * X.lowBlock Z τ j b
  first
    | exact Differentiable.fun_sum (fun j _ => (hL j).const_mul _)
    | exact Differentiable.sum (fun j _ => (hL j).const_mul _)

lemma xZ_zero (x : Frame X.Ψ r) : X.xZ x 0 = x := by
  funext τ
  have h1 : X.lowBlock 0 τ = 1 := by
    ext a b
    simp [Data.lowBlock, Matrix.one_apply]
  show mat x τ * X.lowBlock 0 τ = x τ
  rw [h1, Matrix.mul_one]
  rfl

lemma exp_small : Real.exp (1 / 25) < 3 / 2 := by
  by_contra hcon
  push_neg at hcon
  have h25 : Real.exp 1 = Real.exp (1 / 25) ^ 25 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hpow : (3 / 2 : ℝ) ^ 25 ≤ Real.exp (1 / 25) ^ 25 := pow_le_pow_left₀ (by norm_num) hcon 25
  have he := Real.exp_one_lt_d9
  norm_num at hpow
  linarith

end

end ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

namespace IsotropicCoefficientLemmas

lemma smul_O {r : ℕ} (β : 𝓞 E) (v : Fin r → E) : β • v = (β : E) • v := by
  rfl

lemma herm_add_left {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (x y z : Fin r → E) :
    herm G (x + y) z = herm G x z + herm G y z := by
  simp only [herm, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma herm_smul_left {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (e : E) (x z : Fin r → E) :
    herm G (e • x) z = e * herm G x z := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

def Mp {r : ℕ} (X : Data E r) (ξ : Fin r → E) : Submodule (𝓞 E) (Fin r → E) where
  carrier := {μ | μ ∈ X.Λ ∧ herm X.Gm μ ξ = 0}
  add_mem' := fun ha hb => ⟨X.Λ.add_mem ha.1 hb.1, by rw [herm_add_left, ha.2, hb.2, add_zero]⟩
  zero_mem' := ⟨X.Λ.zero_mem, by simp [herm]⟩
  smul_mem' := fun β μ h => ⟨X.Λ.smul_mem β h.1, by
    rw [smul_O, herm_smul_left, h.2, mul_zero]⟩

def Nx {r : ℕ} (X : Data E r) (ξ : Fin r → E) : Submodule (𝓞 E) (Mp X ξ) where
  carrier := {m | ∃ e : E, (m : Fin r → E) = e • ξ}
  add_mem' := by
    rintro m m' ⟨e, he⟩ ⟨e', he'⟩
    exact ⟨e + e', by rw [Submodule.coe_add, he, he', add_smul]⟩
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro β m ⟨e, he⟩
    exact ⟨(β : E) * e, by rw [Submodule.coe_smul, smul_O, he, smul_smul]⟩

lemma torsion_bot {r : ℕ} (X : Data E r) (ξ : Fin r → E) :
    Submodule.torsion (𝓞 E) (Mp X ξ ⧸ Nx X ξ) = ⊥ := by
  rw [eq_bot_iff]
  intro q hq
  obtain ⟨⟨a, ha⟩, haq⟩ := (Submodule.mem_torsion_iff q).1 hq
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have haq' : (a : 𝓞 E) • (Submodule.Quotient.mk m : Mp X ξ ⧸ Nx X ξ) = 0 := haq
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at haq'
  obtain ⟨e, he⟩ := haq'
  rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
  have ha0 : (a : E) ≠ 0 :=
    NumberField.RingOfIntegers.coe_ne_zero_iff.2 (nonZeroDivisors.ne_zero ha)
  rw [Submodule.coe_smul, smul_O] at he
  show ∃ e : E, (m : Fin r → E) = e • ξ
  refine ⟨e / a, ?_⟩
  rw [div_eq_inv_mul, mul_smul, ← he, smul_smul, inv_mul_cancel₀ ha0, one_smul]

end IsotropicCoefficientLemmas

open IsotropicCoefficientLemmas in
theorem isotropicCoefficientSplitting_holds : IsotropicCoefficientSplitting (E := E) := by
  intro r X ξ hξ
  classical
  have hξ0 : ξ ≠ 0 := hξ.2.2
  have hle : Mp X ξ ≤ X.Λ := fun μ h => h.1
  haveI : Module.Finite (𝓞 E) (Mp X ξ) := by
    haveI : Module.Finite (𝓞 E) X.Λ := Module.Finite.iff_fg.2 X.Λ_fg
    have h1 : ((Mp X ξ).comap X.Λ.subtype).FG := IsNoetherian.noetherian _
    have h2 := h1.map X.Λ.subtype
    rw [Submodule.map_comap_eq, Submodule.range_subtype, inf_eq_right.2 hle] at h2
    exact Module.Finite.iff_fg.2 h2
  haveI : Module.Flat (𝓞 E) (Mp X ξ ⧸ Nx X ξ) :=
    IsDedekindDomain.flat_iff_torsion_eq_bot.2 (torsion_bot X ξ)
  haveI : Module.FinitePresentation (𝓞 E) (Mp X ξ ⧸ Nx X ξ) :=
    Module.finitePresentation_of_finite _ _
  haveI : Module.Projective (𝓞 E) (Mp X ξ ⧸ Nx X ξ) := Module.Flat.projective_of_finitePresentation
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (Nx X ξ).mkQ LinearMap.id
    (Submodule.mkQ_surjective _)
  set ρ : Mp X ξ →ₗ[𝓞 E] Mp X ξ := LinearMap.id - s ∘ₗ (Nx X ξ).mkQ with hρdef
  have hρN : ∀ m, ∃ e : E, ((ρ m : Mp X ξ) : Fin r → E) = e • ξ := by
    intro m
    have h1 : (Nx X ξ).mkQ (s ((Nx X ξ).mkQ m)) = (Nx X ξ).mkQ m := LinearMap.congr_fun hs _
    have h2 : (Nx X ξ).mkQ (ρ m) = 0 := by
      rw [hρdef, LinearMap.sub_apply, map_sub, LinearMap.id_apply, LinearMap.comp_apply, h1, sub_self]
    exact (Submodule.Quotient.mk_eq_zero _).1 h2
  choose coef hcoef using hρN
  have hρid : ∀ m ∈ Nx X ξ, ρ m = m := by
    intro m hm
    have : (Nx X ξ).mkQ m = 0 := (Submodule.Quotient.mk_eq_zero _).2 hm
    simp [hρdef, this]
  have huniq : ∀ e e' : E, e • ξ = e' • ξ → e = e' := fun e e' h => smul_left_injective E hξ0 h
  have hmemMp : ∀ μ ∈ X.Λp ξ, μ ∈ Mp X ξ := fun μ h => ⟨h.1, h.2⟩
  refine ⟨fun μ => if h : μ ∈ Mp X ξ then coef ⟨μ, h⟩ else 0, ?_, ?_, ?_, ?_⟩
  · intro μ hμ
    simp only [dif_pos (hmemMp μ hμ)]
    rw [← hcoef]
    exact (ρ _).2.1
  · intro μ hμ μ' hμ'
    have hs' := (Mp X ξ).add_mem (hmemMp μ hμ) (hmemMp μ' hμ')
    simp only [dif_pos hs', dif_pos (hmemMp μ hμ), dif_pos (hmemMp μ' hμ')]
    apply huniq
    rw [← hcoef, add_smul, ← hcoef, ← hcoef]
    have : (⟨μ + μ', hs'⟩ : Mp X ξ) = ⟨μ, hmemMp μ hμ⟩ + ⟨μ', hmemMp μ' hμ'⟩ := rfl
    rw [this, map_add (f := _)]
    rfl
  · intro α μ hμ
    have hs' : (α : E) • μ ∈ Mp X ξ := by
      rw [← smul_O]
      exact (Mp X ξ).smul_mem α (hmemMp μ hμ)
    simp only [dif_pos hs', dif_pos (hmemMp μ hμ)]
    apply huniq
    rw [← hcoef, mul_smul, ← hcoef]
    have : (⟨(α : E) • μ, hs'⟩ : Mp X ξ) = α • ⟨μ, hmemMp μ hμ⟩ := Subtype.ext (smul_O α μ).symm
    rw [this, map_smul, Submodule.coe_smul, smul_O]
  · intro e he
    have hmem : e • ξ ∈ Mp X ξ := ⟨he, by rw [herm_smul_left, hξ.2.1, mul_zero]⟩
    simp only [dif_pos hmem]
    apply huniq
    rw [← hcoef, hρid _ ⟨e, rfl⟩]

end ReciprocityTheory.ChartRestriction.G.FD
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalPerpBasis

open NumberField Complex Matrix
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

variable {r : ℕ} (X : Data E r)

theorem hC_sum_right' (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {ι : Type*} (s : Finset ι)
    (u : Fin r → ℂ) (f : ι → Fin r → ℂ) : hermC τ G u (∑ i ∈ s, f i) = ∑ i ∈ s, hermC τ G u (f i) := by

  simp only [hermC, Finset.sum_apply, map_sum, Finset.mul_sum]
  calc (∑ a, ∑ b, ∑ i ∈ s, u a * τ (G a b) * conj (f i b))
      = ∑ a, ∑ i ∈ s, ∑ b, u a * τ (G a b) * conj (f i b) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ i ∈ s, ∑ a, ∑ b, u a * τ (G a b) * conj (f i b) := Finset.sum_comm

private theorem hermC_add_left_eq_add (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u u' w : Fin r → ℂ) :
    hermC τ G (u + u') w = hermC τ G u w + hermC τ G u' w := by
  simp only [hermC, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private theorem hermC_smul_left_eq_smul_mul (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (c : ℂ)
    (u w : Fin r → ℂ) : hermC τ G (c • u) w = c * hermC τ G u w := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

private theorem hermC_finset_sum_smul_left (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {ι : Type*}
    (s : Finset ι) (c : ι → ℂ) (v : ι → Fin r → ℂ) (w : Fin r → ℂ) :
    hermC τ G (∑ k ∈ s, c k • v k) w = ∑ k ∈ s, c k * hermC τ G (v k) w := by
  classical
  induction s using Finset.induction_on
  · simp [hermC]
  · rename_i a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hermC_add_left_eq_add, hermC_smul_left_eq_smul_mul, ih]

theorem comb_col {x0 : Frame X.Ψ r} (ho : X.IsOrtho x0) (τ : X.Ψ) (c : Fin r → ℂ) (b : Fin r) :
    hermC τ.1 X.Gm (∑ a, c a • col (mat x0 τ) a) (col (mat x0 τ) b) = c b * ((sgn X.p0 (b : ℕ) : ℝ) : ℂ) := by
  rw [hermC_finset_sum_smul_left]
  have hab : ∀ a, hermC τ.1 X.Gm (col (mat x0 τ) a) (col (mat x0 τ) b) =
      if a = b then ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) else 0 := by
    intro a
    have h := congrFun (congrFun (ho τ) a) b
    rw [Matrix.diagonal_apply] at h
    exact h
  simp [hab, mul_ite]

private theorem hermC_smul_right_eq_conj_mul (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (c : ℂ)
    (u v : Fin r → ℂ) : hermC τ G u (c • v) = conj c * hermC τ G u v := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem comb_comb {x0 : Frame X.Ψ r} (ho : X.IsOrtho x0) (τ : X.Ψ) (c d : Fin r → ℂ) :
    hermC τ.1 X.Gm (∑ a, c a • col (mat x0 τ) a) (∑ b, d b • col (mat x0 τ) b) =
      ∑ a, c a * conj (d a) * ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) := by
  rw [hC_sum_right']
  simp only [hermC_smul_right_eq_conj_mul, comb_col X ho τ c]
  exact Finset.sum_congr rfl fun a _ => by ring

end

end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalPerpBasis
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalPerpBasis

open NumberField Complex Matrix
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

variable {r : ℕ} (X : Data E r)

theorem ortho_h {x : Frame X.Ψ r} (ho : X.IsOrtho x) (τ : X.Ψ) (a b : Fin r) :
    hermC τ.1 X.Gm (col (mat x τ) a) (col (mat x τ) b) =
      if a = b then ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) else 0 := by
  have h := congrFun (congrFun (ho τ) a) b
  rw [Matrix.diagonal_apply] at h
  exact h

theorem span_cols {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (w : Fin r → ℂ) :
    ∃ c : Fin r → ℂ, w = ∑ a, c a • col (mat x τ) a := by
  have hdet : IsUnit (mat x τ).det := isUnit_iff_ne_zero.mpr (hx τ).1
  refine ⟨(mat x τ)⁻¹ *ᵥ w, ?_⟩
  have hBB : mat x τ *ᵥ ((mat x τ)⁻¹ *ᵥ w) = w := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  calc w = mat x τ *ᵥ ((mat x τ)⁻¹ *ᵥ w) := hBB.symm
    _ = _ := by
      funext k
      simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, col]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem sgn_mul_self (a : ℕ) : ((sgn X.p0 a : ℝ) : ℂ) * ((sgn X.p0 a : ℝ) : ℂ) = 1 := by
  unfold sgn
  split_ifs <;> simp

private theorem hermC_sum_smul_left' {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (c : Fin r → ℂ)
    (w : Fin r → Fin r → ℂ) (u : Fin r → ℂ) :
    hermC τ G (∑ i, c i • w i) u = ∑ i, c i * hermC τ G (w i) u := by
  unfold hermC
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => by ring

theorem expand {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ho : X.IsOrtho x) (τ : X.Ψ) (v : Fin r → ℂ) :
    v = ∑ a : Fin r, (((sgn X.p0 (a : ℕ) : ℝ) : ℂ) * hermC τ.1 X.Gm v (col (mat x τ) a)) • col (mat x τ) a := by
  obtain ⟨c, hc⟩ := span_cols X hx τ v
  have hcoef : ∀ a, hermC τ.1 X.Gm v (col (mat x τ) a) = c a * ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) := by
    intro a
    conv_lhs => rw [hc]
    rw [hermC_sum_smul_left']
    simp only [ortho_h X ho τ, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  conv_lhs => rw [hc]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hcoef, ← mul_assoc, mul_comm _ (c a), mul_assoc, sgn_mul_self, mul_one]

theorem ppos_ortho {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ho : X.IsOrtho x) (τ : X.Ψ) (v : Fin r → ℂ) :
    X.ppos x τ v = ∑ a : Fin X.p0, hermC τ.1 X.Gm v (col (mat x τ) (Fin.castLE X.p0_le a)) •
      col (mat x τ) (Fin.castLE X.p0_le a) := by
  have hg : X.gramPos x τ = 1 := by
    ext a b
    simp only [Data.gramPos, Matrix.submatrix_apply, ho τ, Matrix.diagonal_apply, Fin.castLE_inj,
      Matrix.one_apply]
    split_ifs with h
    · simp [sgn, Fin.coe_castLE, a.isLt]
    · rfl
  unfold Data.ppos
  rw [hg, Matrix.inv_eq_left_inv (mul_one (1 : Matrix (Fin X.p0) (Fin X.p0) ℂ))]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  simp [Matrix.one_apply]

end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalPerpBasis
end
