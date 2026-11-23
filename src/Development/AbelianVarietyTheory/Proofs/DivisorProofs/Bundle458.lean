module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle039
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle405
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle406
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.Henselian
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
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBicharPairing
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle070

@[expose] public section

section

open GlobalTheory.WeilM Matrix

noncomputable section
namespace GlobalTheory.RankChart
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model

variable {k : Type} [Field k] {R T D : Type} [Fintype R] [DecidableEq R] [Fintype T] [DecidableEq T]
  [Fintype D] [DecidableEq D]

def shear (c : Matrix T R k) (Y : Matrix (R ⊕ T) D k) : Matrix (R ⊕ T) D k :=
  fromRows Y.toRows₁ (Y.toRows₂ + c * Y.toRows₁)

def dil (t : k) (Y : Matrix (R ⊕ T) D k) : Matrix (R ⊕ T) D k := fromRows Y.toRows₁ (t • Y.toRows₂)

def stack (Y₁ : Matrix R D k) (C : Matrix T R k) : Matrix (R ⊕ T) D k := fromRows Y₁ (C * Y₁)

def shearGL (c : Matrix T R k) : GL (R ⊕ T) k :=
  ⟨fromBlocks 1 cᵀ 0 1, fromBlocks 1 (-cᵀ) 0 1, by simp [fromBlocks_multiply],
    by simp [fromBlocks_multiply]⟩

def dilGL (t : kˣ) : GL (R ⊕ T) k :=
  ⟨diagonal (Sum.elim 1 fun _ => (t : k)), diagonal (Sum.elim 1 fun _ => ((t⁻¹ : kˣ) : k)), by
    rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; rcases i with i | i <;> simp, by
    rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; rcases i with i | i <;> simp⟩

@[simp] theorem toRows₁_shear (c : Matrix T R k) (Y : Matrix (R ⊕ T) D k) : (shear c Y).toRows₁ = Y.toRows₁ := by
  simp [shear]

@[simp] theorem toRows₁_dil (t : k) (Y : Matrix (R ⊕ T) D k) : (dil t Y).toRows₁ = Y.toRows₁ := by
  simp [dil]

@[simp] theorem toRows₁_stack (Y₁ : Matrix R D k) (C : Matrix T R k) : (stack Y₁ C).toRows₁ = Y₁ := by
  simp [stack]

theorem submatrix_inl_eq (Y : Matrix (R ⊕ T) D k) (τ : R → D) :
    Y.submatrix Sum.inl τ = Y.toRows₁.submatrix id τ := rfl

theorem shear_stack (c : Matrix T R k) (Y₁ : Matrix R D k) (C : Matrix T R k) :
    shear c (stack Y₁ C) = stack Y₁ (C + c) := by
  simp [shear, stack, Matrix.add_mul]

theorem dil_stack (t : k) (Y₁ : Matrix R D k) (C : Matrix T R k) :
    dil t (stack Y₁ C) = stack Y₁ (t • C) := by
  simp [dil, stack, smul_mul]

theorem shear_sub_self (c : Matrix T R k) (Y : Matrix (R ⊕ T) D k) :
    shear c Y - Y = fromRows 0 (c * Y.toRows₁) := by
  ext (i | i) j <;> simp [shear]

theorem shearGL_transpose_mul (c : Matrix T R k) (Y : Matrix (R ⊕ T) D k) :
    (shearGL c).valᵀ * Y = shear c Y := by
  ext (i | i) j <;> simp [shearGL, shear, fromBlocks_transpose, Matrix.mul_apply, Fintype.sum_sum_type,
    Matrix.one_apply, add_comm]

theorem dilGL_transpose_mul (t : kˣ) (Y : Matrix (R ⊕ T) D k) :
    (dilGL t : GL (R ⊕ T) k).valᵀ * Y = dil (t : k) Y := by
  ext (i | i) j <;> simp [dilGL, dil, diagonal_transpose, Matrix.mul_apply, Fintype.sum_sum_type, diagonal_apply]

theorem gdet_shearGL (c : Matrix T R k) : gdet (shearGL c) = 1 := by
  ext; simp [shearGL, gdet, det_fromBlocks_zero₂₁]

theorem gdet_dilGL (t : kˣ) : gdet (dilGL t : GL (R ⊕ T) k) = t ^ Fintype.card T := by
  ext; simp [dilGL, gdet, det_diagonal, Fintype.prod_sum_type]

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem omB_shearGL (ν : kˣ →* ℂˣ) (c : Matrix T R k) (Ψ : Matrix (R ⊕ T) D k → ℂ) (Y : Matrix (R ⊕ T) D k) :
    omB ν ν (shearGL c) 1 Ψ Y = Ψ (shear c Y) := by
  simp [omB, gdet_shearGL, shearGL_transpose_mul]

theorem exists_apow_eq (x : kˣ) (n : ℕ) : ∃ r : ℝ, 0 < r ∧ apow x ((n : ℂ) / 2) = r := by
  refine ⟨GlobalTheory.SplitWeil.nabs k x ^ ((n : ℝ) / 2), Real.rpow_pos_of_pos (nabs_pos x) _, ?_⟩
  rw [apow, Complex.ofReal_cpow (nabs_pos x).le]
  push_cast; rfl

theorem omB_dilGL (ν : kˣ →* ℂˣ) (t : kˣ) (Ψ : Matrix (R ⊕ T) D k → ℂ) (Y : Matrix (R ⊕ T) D k) :
    omB ν ν (dilGL t : GL (R ⊕ T) k) 1 Ψ Y =
      (ν t : ℂ) ^ Fintype.card T * apow (t ^ Fintype.card T) ((Fintype.card D : ℂ) / 2) * Ψ (dil (t : k) Y) := by
  simp [omB, gdet_dilGL, dilGL_transpose_mul]

end GlobalTheory.RankChart

namespace GlobalTheory.RankChart
open GlobalTheory.SplitFlip GlobalTheory.LocMod.Inhab ValuativeRel

theorem out_mk_sub_mem {G : Type} [AddCommGroup G] (H L : AddSubgroup G) (x : H) :
    (((QuotientAddGroup.mk x : H ⧸ L.addSubgroupOf H).out : H) : G) - x ∈ L := by
  have h := QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' (QuotientAddGroup.mk x : H ⧸ L.addSubgroupOf H))
  rw [AddSubgroup.mem_addSubgroupOf] at h
  have := L.neg_mem h
  simpa [neg_add_eq_sub] using this

theorem mk_eq_mk_iff {G : Type} [AddCommGroup G] (H L : AddSubgroup G) (x y : H) :
    (QuotientAddGroup.mk x : H ⧸ L.addSubgroupOf H) = QuotientAddGroup.mk y ↔ (x : G) - y ∈ L := by
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, ← L.neg_mem_iff]
  simp [neg_add_eq_sub]


open scoped Classical in
open Classical in
theorem sum_shift_out {G : Type} [AddCommGroup G] (F : G → ℂ) (H L : AddSubgroup G)
    [Fintype (H ⧸ L.addSubgroupOf H)] (hL : ∀ x y, y - x ∈ L → F y = F x) (hH : ∀ x, F x ≠ 0 → x ∈ H) (x : G) :
    ∑ q : H ⧸ L.addSubgroupOf H, F (x + ((q.out : H) : G)) =
      if x ∈ H then ∑ q : H ⧸ L.addSubgroupOf H, F ((q.out : H) : G) else 0 := by
  split_ifs with hx
  · have key : ∀ q : H ⧸ L.addSubgroupOf H, F (x + ((q.out : H) : G)) =
        F ((((QuotientAddGroup.mk (⟨x, hx⟩ : H) : H ⧸ L.addSubgroupOf H) + q).out : H) : G) := by
      intro q
      have e : (QuotientAddGroup.mk (⟨x, hx⟩ : H) : H ⧸ L.addSubgroupOf H) + q =
          QuotientAddGroup.mk ((⟨x, hx⟩ : H) + q.out) := by
        rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq']
      rw [e]
      exact (hL (((⟨x, hx⟩ : H) + q.out : H) : G) _ (out_mk_sub_mem H L ((⟨x, hx⟩ : H) + q.out))).symm
    rw [Finset.sum_congr rfl fun q _ => key q]
    exact Fintype.sum_equiv (Equiv.addLeft (QuotientAddGroup.mk (⟨x, hx⟩ : H) : H ⧸ L.addSubgroupOf H))
      (fun q => F ((((QuotientAddGroup.mk (⟨x, hx⟩ : H) : H ⧸ L.addSubgroupOf H) + q).out : H) : G))
      (fun q => F ((q.out : H) : G)) fun q => rfl
  · refine Finset.sum_eq_zero fun q _ => ?_
    by_contra h
    have := H.sub_mem (hH _ h) (q.out : H).2
    rw [add_sub_cancel_right] at this
    exact hx this


open scoped Classical in
open Classical in
theorem sum_ite_out {G : Type} [AddCommGroup G] (H H' : AddSubgroup G) [Fintype (H' ⧸ H.addSubgroupOf H')]
    (hHH' : H ≤ H') (c : ℂ) (x : G) :
    ∑ q : H' ⧸ H.addSubgroupOf H', (if x + ((q.out : H') : G) ∈ H then c else 0) = if x ∈ H' then c else 0 := by
  split_ifs with hx
  · rw [Finset.sum_eq_single (QuotientAddGroup.mk (⟨-x, H'.neg_mem hx⟩ : H'))]
    · rw [if_pos]
      have := out_mk_sub_mem H' H (⟨-x, H'.neg_mem hx⟩ : H')
      rwa [sub_neg_eq_add, add_comm] at this
    · intro q _ hq
      rw [if_neg]
      intro hmem
      apply hq
      rw [← QuotientAddGroup.out_eq' q, mk_eq_mk_iff]
      rwa [sub_neg_eq_add, add_comm]
    · simp
  · refine Finset.sum_eq_zero fun q _ => ?_
    rw [if_neg]
    intro hmem
    have := H'.sub_mem (hHH' hmem) (q.out : H').2
    rw [add_sub_cancel_right] at this
    exact hx this

end GlobalTheory.RankChart
end
end

section

open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.DiagVol ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.IndexCol

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem mem_maximalIdeal_iff (a : 𝒪[k]) :
    a ∈ IsLocalRing.maximalIdeal 𝒪[k] ↔ valuation k (a : k) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one]

theorem val_sum_mul_lt_one (a b : ι → k) (ha : ∀ s, a s ∈ 𝒪[k]) (hb : ∀ s, valuation k (b s) < 1) :
    valuation k (∑ s, a s * b s) < 1 := by
  refine Valuation.map_sum_lt _ one_ne_zero fun s _ => ?_
  rw [map_mul]
  exact (mul_le_mul_of_nonneg_right (ha s) zero_le').trans_lt (by rw [one_mul]; exact hb s)

theorem col_inv_mul_iff {x : GL ι k} (hx : x ∈ KO k ι) (y : GL ι k) (t : ι) :
    (∀ s, valuation k (((x⁻¹ * y).val - 1) s t) < 1) ↔ ∀ s, valuation k ((y.val - x.val) s t) < 1 := by
  obtain ⟨hx1, hx2⟩ := (mem_KO_iff x).1 hx
  have e1 : (x⁻¹ * y).val - 1 = (x⁻¹).val * (y.val - x.val) := by
    rw [Units.val_mul, mul_sub, Units.inv_mul]
  have e2 : y.val - x.val = x.val * ((x⁻¹ * y).val - 1) := by
    rw [Units.val_mul, mul_sub, ← mul_assoc, Units.mul_inv, one_mul, mul_one]
  constructor
  · intro h s
    rw [e2, Matrix.mul_apply]
    exact val_sum_mul_lt_one _ _ (fun j => hx1 s j) h
  · intro h s
    rw [e1, Matrix.mul_apply]
    exact val_sum_mul_lt_one _ _ (fun j => hx2 s j) h

theorem conj_apply (ϖ : kˣ) (t : ι) (z : Matrix ι ι k) (r s : ι) :
    ((diagGL (Pi.mulSingle t ϖ : ι → kˣ)).val * z * ((diagGL (Pi.mulSingle t ϖ : ι → kˣ))⁻¹).val) r s =
      ((Pi.mulSingle t ϖ : ι → kˣ) r : k) * z r s * ((((Pi.mulSingle t ϖ : ι → kˣ) s)⁻¹ : kˣ) : k) := by
  have hi : ((diagGL (Pi.mulSingle t ϖ : ι → kˣ))⁻¹).val = diagonal fun i => ((((Pi.mulSingle t ϖ : ι → kˣ) i)⁻¹ : kˣ) : k) := rfl
  rw [hi, diagGL_val, mul_diagonal, diagonal_mul]

theorem conj_integral_iff {ϖ : kˣ} (hϖ : IsUnif ϖ) (t : ι) (z : Matrix ι ι k) (hz : ∀ r s, z r s ∈ 𝒪[k]) :
    (∀ r s, ((diagGL (Pi.mulSingle t ϖ : ι → kˣ)).val * z * ((diagGL (Pi.mulSingle t ϖ : ι → kˣ))⁻¹).val) r s ∈ 𝒪[k]) ↔
      ∀ r, r ≠ t → valuation k (z r t) < 1 := by
  have hv : valuation k (ϖ : k) ≠ 0 := by simp
  have hlt : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  simp only [conj_apply]
  constructor
  · intro h r hr
    have h1 := h r t
    simp only [Pi.mulSingle_apply, hr, if_false, if_true, Units.val_one, one_mul] at h1
    have h2 : valuation k (z r t * ((ϖ⁻¹ : kˣ) : k)) ≤ 1 := h1
    rw [map_mul, Units.val_inv_eq_inv_val, map_inv₀] at h2
    have h3 : valuation k (z r t) ≤ valuation k (ϖ : k) := by
      have := mul_le_mul_of_nonneg_right h2 (zero_le' (a := valuation k (ϖ : k)))
      rwa [mul_assoc, inv_mul_cancel₀ hv, mul_one, one_mul] at this
    exact h3.trans_lt hlt
  · intro h r s
    by_cases hr : r = t <;> by_cases hs : s = t
    · subst hr; subst hs
      simp only [Pi.mulSingle_eq_same]
      rw [mul_comm (ϖ : k), mul_assoc, Units.mul_inv, mul_one]; exact hz _ _
    · subst hr
      simp only [Pi.mulSingle_eq_same, Pi.mulSingle_apply, hs, if_false, inv_one, Units.val_one, mul_one]
      exact mul_mem hϖ.mem (hz _ _)
    · subst hs
      simp only [Pi.mulSingle_eq_same, Pi.mulSingle_apply, hr, if_false, Units.val_one, one_mul]
      show valuation k _ ≤ 1
      rw [map_mul, Units.val_inv_eq_inv_val, map_inv₀]
      have h3 : valuation k (z r s) ≤ valuation k (ϖ : k) := by
        rw [hϖ, le_uniformizer_iff]; exact h r hr
      calc valuation k (z r s) * (valuation k (ϖ : k))⁻¹ ≤ valuation k (ϖ : k) * (valuation k (ϖ : k))⁻¹ :=
            mul_le_mul_of_nonneg_right h3 zero_le'
        _ = 1 := mul_inv_cancel₀ hv
    · simp only [Pi.mulSingle_apply, hr, hs, if_false, inv_one, Units.val_one, one_mul, mul_one]
      exact hz _ _

theorem mem_conj_iff {ϖ : kˣ} (hϖ : IsUnif ϖ) (t : ι) {z : GL ι k} (hz : z ∈ KO k ι) :
    z ∈ (KO k ι).map (MulAut.conj ((diagGL (Pi.mulSingle t ϖ : ι → kˣ))⁻¹)).toMonoidHom ↔
      (∀ r, r ≠ t → valuation k (z.val r t) < 1) ∧ ∀ r, r ≠ t → valuation k ((z⁻¹).val r t) < 1 := by
  set g := diagGL (Pi.mulSingle t ϖ : ι → kˣ) with hg
  have e : z ∈ (KO k ι).map (MulAut.conj g⁻¹).toMonoidHom ↔ g * z * g⁻¹ ∈ KO k ι := by
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa [mul_assoc] using hw
    · intro h
      exact ⟨_, h, by simp [mul_assoc]⟩
  obtain ⟨h1, h2⟩ := (mem_KO_iff z).1 hz
  have ev : (g * z * g⁻¹).val = g.val * z.val * (g⁻¹).val := by simp only [Units.val_mul]
  have ei : ((g * z * g⁻¹)⁻¹).val = g.val * (z⁻¹).val * (g⁻¹).val := by
    rw [show (g * z * g⁻¹)⁻¹ = g * z⁻¹ * g⁻¹ by group]; simp only [Units.val_mul]
  rw [e, mem_KO_iff, ev, ei, hg, conj_integral_iff hϖ t _ h1, conj_integral_iff hϖ t _ h2]

theorem relIndex_conj_col : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {ι : Type} [Fintype ι] [DecidableEq ι] (ϖ : kˣ), IsUnif ϖ → ∀ (t : ι) (S : Finset ι), t ∉ S →
    ∀ (H : Subgroup (GL ι k)), H ≤ KO k ι → (∀ x ∈ H, ∀ r, r ∉ S → x.val r t = (1 : Matrix ι ι k) r t) →
    (∀ y : ι → k, (∀ r, y r ∈ 𝒪[k]) → (∀ r, r ∉ S → y r = 0) →
      ∃ x ∈ H, x.val = 1 + Matrix.of (fun r s => if s = t then y r else 0)) →
    ((KO k ι).map (MulAut.conj ((diagGL (Pi.mulSingle t ϖ))⁻¹)).toMonoidHom).relIndex H = resCard k ^ S.card := by
  intro k _ _ _ _ ι _ _ ϖ hϖ t S ht H hH hcol hel
  set A := (KO k ι).map (MulAut.conj ((diagGL (Pi.mulSingle t ϖ : ι → kˣ))⁻¹)).toMonoidHom with hA

  have hQ0 : ∀ z ∈ H, (∀ r, r ≠ t → valuation k (z.val r t) < 1) ↔
      ∀ s, valuation k ((z.val - 1) s t) < 1 := by
    intro z hz
    constructor
    · intro h s
      by_cases hs : s = t
      · subst hs; rw [Matrix.sub_apply, hcol z hz s ht, sub_self, map_zero]; exact zero_lt_one
      · rw [Matrix.sub_apply, Matrix.one_apply_ne hs, sub_zero]; exact h s hs
    · intro h r hr
      simpa [Matrix.sub_apply, Matrix.one_apply_ne hr] using h r
  have hQ : ∀ z ∈ H, z ∈ A ↔ ∀ s, valuation k ((z.val - 1) s t) < 1 := by
    intro z hz
    have hzi : z⁻¹ ∈ H := H.inv_mem hz
    rw [hA, mem_conj_iff hϖ t (hH hz), hQ0 z hz, hQ0 _ hzi]
    have e := col_inv_mul_iff (hH hz) 1 t
    rw [mul_one] at e
    rw [e]
    constructor
    · exact fun h => h.1
    · intro h
      refine ⟨h, fun s => ?_⟩
      have h1 := h s
      rw [Matrix.sub_apply] at h1 ⊢
      rw [← Valuation.map_neg, neg_sub, Units.val_one]; exact h1
  have hres : ∀ x y : 𝒪[k], IsLocalRing.residue 𝒪[k] x = IsLocalRing.residue 𝒪[k] y ↔
      valuation k ((x : k) - y) < 1 := fun x y => by
    have h1 := mem_maximalIdeal_iff (x - y)
    push_cast at h1
    rw [← h1]; exact Ideal.Quotient.eq
  let φ : H → (S → 𝓀[k]) := fun x r =>
    IsLocalRing.residue 𝒪[k] ⟨x.1.val r t, ((mem_KO_iff _).1 (hH x.2)).1 r t⟩
  have hφ : ∀ a b : H, φ a = φ b ↔ a⁻¹ * b ∈ A.subgroupOf H := by
    intro a b
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv,
      hQ _ (H.mul_mem (H.inv_mem a.2) b.2), col_inv_mul_iff (hH a.2), funext_iff]
    simp only [φ, hres]
    constructor
    · intro h s
      by_cases hs : s ∈ S
      · rw [Matrix.sub_apply, ← Valuation.map_neg, neg_sub]; exact h ⟨s, hs⟩
      · rw [Matrix.sub_apply, hcol b b.2 s hs, hcol a a.2 s hs, sub_self, map_zero]; exact zero_lt_one
    · intro h r
      have := h r
      rwa [Matrix.sub_apply, ← Valuation.map_neg, neg_sub] at this
  let f : H ⧸ A.subgroupOf H → (S → 𝓀[k]) :=
    Quotient.lift φ (fun a b hab => (hφ a b).2 (QuotientGroup.leftRel_apply.1 hab))
  have hf : Function.Bijective f := by
    constructor
    · intro p q
      induction p using QuotientGroup.induction_on
      induction q using QuotientGroup.induction_on
      intro h
      exact QuotientGroup.eq.2 ((hφ _ _).1 h)
    · intro c
      choose u hu using fun r : S => IsLocalRing.residue_surjective (c r)
      let y : ι → k := fun r => if h : r ∈ S then (u ⟨r, h⟩ : k) else 0
      obtain ⟨x, hxH, hx⟩ := hel y (fun r => by
          by_cases h : r ∈ S
          · simp only [y, h, dif_pos]; exact (u _).2
          · simp only [y, h, dif_neg, not_false_eq_true]; exact zero_mem _)
        (fun r hr => by simp [y, hr])
      refine ⟨QuotientGroup.mk ⟨x, hxH⟩, ?_⟩
      funext r
      have hr : (r : ι) ≠ t := fun h => ht (h ▸ r.2)
      have e : x.val r t = u r := by
        rw [hx]; simp [y, hr, r.2]
      show IsLocalRing.residue 𝒪[k] ⟨x.val r t, _⟩ = c r
      rw [← hu r]; congr 1; exact Subtype.ext e
  rw [Subgroup.relIndex, Subgroup.index, Nat.card_congr (Equiv.ofBijective f hf), Nat.card_fun,
    Nat.card_eq_fintype_card (α := S), Fintype.card_coe]
  rfl

end GlobalTheory.IndexCol
end
end

section

open MeasureTheory Matrix ValuativeRel

noncomputable section
namespace GlobalTheory.CharNormHalf

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def normTwist (d : ℕ) (χ : kˣ →* ℂˣ) : kˣ →* ℂˣ where
  toFun x := Units.mk0 (((‖(χ x : ℂ)‖ : ℝ) : ℂ) * GlobalTheory.SplitFlip.apow x (-((d : ℂ) / 2)))
    (mul_ne_zero (by exact_mod_cast (norm_ne_zero_iff.2 (χ x).ne_zero)) (GlobalTheory.SplitFlip.apow_ne_zero _ _))
  map_one' := by ext; simp
  map_mul' x y := by
    ext
    simp only [map_mul, Units.val_mul, norm_mul, Complex.ofReal_mul, Units.val_mk0, GlobalTheory.SplitFlip.apow_mul]
    ring

theorem normTwist_apply (d : ℕ) (χ : kˣ →* ℂˣ) (x : kˣ) :
    (normTwist d χ x : ℂ) = ((‖(χ x : ℂ)‖ : ℝ) : ℂ) * GlobalTheory.SplitFlip.apow x (-((d : ℂ) / 2)) := rfl

theorem norm_mul_apow_eq_one : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ) (χ : kˣ →* ℂˣ), (∀ u : kˣ, valuation k (u : k) = 1 → ‖(χ u : ℂ)‖ = 1) →
    ∀ ϖ : kˣ, GlobalTheory.SplitFlip.IsUnif ϖ → ‖(χ ϖ : ℂ)‖ ^ 2 * (GlobalTheory.SplitWeil.resCard k : ℝ) ^ d = 1 →
    ∀ x : kˣ, ‖(χ x : ℂ) * GlobalTheory.SplitFlip.apow x (-((d : ℂ) / 2))‖ = 1 := by
  intro k _ _ _ _ d χ hu ϖ hϖ hn x
  set B := normTwist d χ
  have hunr : ∀ y : kˣ, valuation k (y : k) = 1 → B y = 1 := by
    intro y hy
    ext
    rw [normTwist_apply, hu y hy, GlobalTheory.SplitFlip.apow_of_valuation_eq_one hy]
    simp
  have hq : (1 : ℝ) < (GlobalTheory.SplitWeil.resCard k : ℝ) := by exact_mod_cast GlobalTheory.SplitWeil.one_lt_resCard (k := k)
  set q : ℝ := (GlobalTheory.SplitWeil.resCard k : ℝ) with hqdef
  have hq0 : 0 < q := by linarith
  have hnabs : GlobalTheory.SplitWeil.nabs k ϖ = q⁻¹ := by
    rw [GlobalTheory.LGrp.nabs_eq_zpow, GlobalTheory.SmGL.ord_eq_one (k := k) hϖ]
    simp [hqdef]
  have hap : GlobalTheory.SplitFlip.apow ϖ (-((d : ℂ) / 2)) = ((q ^ ((d : ℝ) / 2) : ℝ) : ℂ) := by
    rw [GlobalTheory.SplitFlip.apow, hnabs, show (-((d : ℂ) / 2)) = ((-((d : ℝ) / 2) : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow (inv_nonneg.2 hq0.le), Real.inv_rpow hq0.le, ← Real.rpow_neg hq0.le, neg_neg]
  have hBϖ : B ϖ = 1 := by
    ext
    rw [normTwist_apply, hap, Units.val_one, ← Complex.ofReal_mul]
    have hb0 : 0 ≤ ‖(χ ϖ : ℂ)‖ * q ^ ((d : ℝ) / 2) := by positivity
    have hsq : (‖(χ ϖ : ℂ)‖ * q ^ ((d : ℝ) / 2)) ^ 2 = 1 := by
      rw [mul_pow, ← Real.rpow_natCast (q ^ ((d : ℝ) / 2)) 2, ← Real.rpow_mul hq0.le]
      rw [show (d : ℝ) / 2 * ((2 : ℕ) : ℝ) = ((d : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
      exact hn
    have := (pow_eq_one_iff_of_nonneg hb0 two_ne_zero).1 hsq
    rw [this]; simp
  have hB := GlobalTheory.SmGL.eq_unrChar (k := k) (χ := B) hunr hϖ
  have hx : B x = 1 := by
    rw [hB, hBϖ, GlobalTheory.SmGL.unrChar_apply, _root_.one_zpow]
  have hx' : ‖(B x : ℂ)‖ = 1 := by rw [hx]; simp
  rw [normTwist_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_norm] at hx'
  rw [norm_mul]; exact hx'

end GlobalTheory.CharNormHalf
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.etaleLocal_property_calculus_rules : (∀ (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), (∀ V g, P V g) → Loc U P) ∧ (∀ (U : Scheme.{0}) (P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), Loc U P → (∀ V g, P V g → Q V g) → Loc U Q) ∧ (∀ (U : Scheme.{0}) (P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), Loc U P → Loc U Q → Loc U fun V g => P V g ∧ Q V g) ∧ (∀ (U W : Scheme.{0}) (k : W ⟶ U) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), Loc U P → Loc W fun V g => P V (g ≫ k)) ∧ (∀ (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), Loc U (fun V g => Loc V fun W k => P W (k ≫ g)) → Loc U P) ∧ (∀ (U : Scheme.{0}) (ι : Type) [Finite ι] (P : ι → ∀ V : Scheme.{0}, (V ⟶ U) → Prop), (∀ i, Loc U (P i)) → Loc U fun V g => ∀ i, P i V g) ∧ (∀ (U : Scheme.{0}) [IsEmpty U] (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), Loc U P) := by
  first | (exact @GlobalTheory.EtC.loc_calculus) | (exact GlobalTheory.EtC.loc_calculus) | (intros; apply GlobalTheory.EtC.loc_calculus  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.etaleToSheafify_locally_bijective_and_lift : ∀ (R : Type) [CommRing R] (P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)), (∀ (U : Scheme.{0}) (y : Sec ((presheafToSheaf Scheme.etaleTopology _).obj P) U), Loc U fun V g => ∃ x, ((toSheafify Scheme.etaleTopology P).app (op V)).hom x = Sec.res g y) ∧ (∀ (U : Scheme.{0}) (x : P.obj (op U)), ((toSheafify Scheme.etaleTopology P).app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0) ∧ ∀ (F : Shv R) (φ : P ⟶ F.obj), ∃! ψ : (presheafToSheaf Scheme.etaleTopology _).obj P ⟶ F, toSheafify Scheme.etaleTopology P ≫ ψ.hom = φ := by
  first | (exact @GlobalTheory.EtC.toSheafify_loc_bij_lift) | (exact GlobalTheory.EtC.toSheafify_loc_bij_lift) | (intros; apply GlobalTheory.EtC.toSheafify_loc_bij_lift  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.exists_biproduct_chainMap_of_injective_family : ∀ (R : Type) [CommRing R] {ι : Type} [Fintype ι] (L : ι → Cx R) (C : Cx R) (g : ∀ j, L j ⟶ C) (m : ℤ), (∀ j, (L j).IsStrictlyGE m) → (∀ j n, CategoryTheory.Injective ((L j).X n)) → ∃ (D : Cx R) (f : D ⟶ C), D.IsStrictlyGE m ∧ (∀ n, CategoryTheory.Injective (D.X n)) ∧ ∀ (K : Cx R) (n : ℤ), ∃ e : (∀ j, CohomologyClass K (L j) n) ≃ CohomologyClass K D n, ∀ a, cpush K f n (e a) = ∑ j, cpush K (g j) n (a j) := by
  first | (exact @GlobalTheory.BiprodPush.biproduct_push) | (exact GlobalTheory.BiprodPush.biproduct_push) | (intros; apply GlobalTheory.BiprodPush.biproduct_push  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.isLocallyFlatEtaleSheaf_iso_and_zero : ∀ (R : Type) [CommRing R], (∀ {M N : Shv R}, (M ≅ N) → FlatS M → FlatS N) ∧ ∀ M : Shv R, IsZero M → FlatS M := by
  first | exact @GlobalTheory.EtC.flatS_iso_and_zero | exact GlobalTheory.EtC.flatS_iso_and_zero | (intros; apply GlobalTheory.EtC.flatS_iso_and_zero <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.mappingCone_locallyExact_of_component_sections : ∀ (R : Type) [CommRing R] {I J : Cx R} (f : I ⟶ J) (U : Scheme.{0}) (n : ℤ), (∀ (b₁ : Sec (I.X (n + 1)) U) (b₂ : Sec (J.X n) U), Sec.map (I.d (n + 1) (n + 2)) b₁ = 0 → Sec.map (f.f (n + 1)) b₁ + Sec.map (J.d n (n + 1)) b₂ = 0 → Loc U fun V g => ∃ (a₁ : Sec (I.X n) V) (a₂ : Sec (J.X (n - 1)) V), Sec.map (I.d n (n + 1)) a₁ = -Sec.res g b₁ ∧ Sec.map (f.f n) a₁ + Sec.map (J.d (n - 1) n) a₂ = Sec.res g b₂) → ∀ b : Sec ((mappingCone f).X n) U, Sec.map ((mappingCone f).d n (n + 1)) b = 0 → Loc U fun V g => ∃ a : Sec ((mappingCone f).X (n - 1)) V, Sec.map ((mappingCone f).d (n - 1) n) a = Sec.res g b := by
  first | exact @GlobalTheory.EtC.cone_sec_exact | exact GlobalTheory.EtC.cone_sec_exact | (intros; apply GlobalTheory.EtC.cone_sec_exact; all_goals assumption)
end
