module

import Formalism.LocalToGlobal.IndefiniteReal.MemSpanOfSmulMem
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle030
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaBlockTriangular
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle040
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentSeparation
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic
public import Mathlib.CategoryTheory.Category.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle053
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle054
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum

@[expose] public section

section

namespace GlobalTheory.TargetStatementSixOneSixtyEight

open NumberField

theorem main {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module E V]
    [Module (RingOfIntegers E) V] [IsScalarTower (RingOfIntegers E) E V]
    (L : Submodule (RingOfIntegers E) V) {y : V} (hy : y ∈ Submodule.span E (L : Set V)) :
    ∃ c : RingOfIntegers E, c ≠ 0 ∧ c • y ∈ L := by
  apply Formalism.IndefR.LatticeTransfer.Lat.exists_smul_mem <;> assumption

theorem target : ∀ {E : Type} [inst : Field E] [NumberField E] {V : Type} [inst_2 : AddCommGroup V]
    [inst_3 : Module E V] [inst_4 : Module (NumberField.RingOfIntegers E) V]
    [IsScalarTower (NumberField.RingOfIntegers E) E V]
    (L : Submodule (NumberField.RingOfIntegers E) V) {y : V},
    y ∈ Submodule.span E (↑L : Set V) →
      ∃ (c : NumberField.RingOfIntegers E), c ≠ (0 : NumberField.RingOfIntegers E) ∧ c • y ∈ L :=
  fun L _ hy => main L hy

end GlobalTheory.TargetStatementSixOneSixtyEight
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice

namespace GlobalTheory.StepData.NormalForm

section Plain
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

end Plain

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem _root_.GlobalTheory.StepData.NormalForm.exists_valuation_eq_zpow {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k)
    (d : kˣ) : ∃ e : ℤ, valuation k (d : k) = valuation k (ϖ : k) ^ e := by
  set φ := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k
  have hu0 : φ (uniformizer k) ≠ 0 := by
    rw [ne_eq, map_eq_zero]; exact (uniformizer_pos).ne'
  have hu1 : φ (uniformizer k) < 1 := by
    rw [← map_one φ]; exact φ.strictMono uniformizer_lt_one
  obtain ⟨a, ha⟩ := WithZero.ne_zero_iff_exists.mp hu0
  have ha1 : a.toAdd < 0 := by
    rw [← ha] at hu1
    exact_mod_cast hu1
  have ha2 : -1 ≤ a.toAdd := by
    have h1 : φ.symm ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ)) < 1 := by
      rw [← map_one φ.symm]
      exact φ.symm.strictMono
        (by exact_mod_cast (show (Multiplicative.ofAdd (-1 : ℤ)) < 1 by decide))
    have h2 := le_uniformizer_iff.mpr h1
    have h3 := φ.strictMono.monotone h2
    simp only [OrderMonoidIso.apply_symm_apply, ← ha] at h3
    exact_mod_cast h3
  have ha3 : a = Multiplicative.ofAdd (-1 : ℤ) := by
    apply Multiplicative.toAdd.injective; simp; omega
  have hd0 : φ (valuation k (d : k)) ≠ 0 := by
    rw [ne_eq, map_eq_zero, map_eq_zero]; exact d.ne_zero
  obtain ⟨b, hb⟩ := WithZero.ne_zero_iff_exists.mp hd0
  have hz : φ (uniformizer k ^ (-b.toAdd)) = φ (uniformizer k) ^ (-b.toAdd) := map_zpow₀ φ _ _
  have key : φ (valuation k (d : k)) = φ (valuation k (ϖ : k) ^ (-b.toAdd)) := by
    rw [hϖ, hz, ← ha, ← hb, ha3, ← WithZero.coe_zpow]
    congr 1
    apply Multiplicative.toAdd.injective
    simp
  exact ⟨-b.toAdd, φ.injective key⟩

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private lemma latOf_mul_of_mem_KO' {K : Type} [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] {Y : Type} [Fintype Y] [DecidableEq Y]
    (x w : GL Y K) (hw : w ∈ _root_.GlobalTheory.SplitWeil.KO K Y) :
    _root_.GlobalTheory.StepData.latOf (x * w) = _root_.GlobalTheory.StepData.latOf x := by
  rw [_root_.GlobalTheory.StepData.mem_KO] at hw
  apply le_antisymm
  · rw [_root_.GlobalTheory.StepData.latOf_le_iff]
    simpa [← mul_assoc] using hw.1
  · rw [_root_.GlobalTheory.StepData.latOf_le_iff]
    simpa [mul_assoc] using hw.2


open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem _root_.GlobalTheory.StepData.NormalForm.normalFormModN : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], _root_.GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice.NormalFormModN k := by
  intro k _ _ _ _ ϖ hϖ n _ _ c h
  obtain ⟨b, hbT, w, hw, rfl⟩ := _root_.GlobalTheory.SplitWeil.iwasawa_blockTriangular k (n ⊕ Fin c)
    (Sum.elim (fun _ => 0) (fun i => (i : ℕ) + 1)) h
  have hbP : (b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k).BlockTriangular
      (_root_.GlobalTheory.RootEx.lev 1) := by
    intro i j hij
    apply hbT
    unfold _root_.GlobalTheory.RootEx.lev at hij
    rcases i with i | i <;> rcases j with j | j <;> simp at hij ⊢ <;> omega
  obtain ⟨u', hu', m, hm0, hmb, hbum⟩ := _root_.GlobalTheory.RootEx.BlockLevi.exists_unip_mul_levi k n c 1 b hbP
  have h21 : (b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k).toBlocks₂₁ = 0 := by
    ext i j
    exact hbT (by simp)
  have hT : ((b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k).toBlocks₂₂).BlockTriangular id := by
    intro i j hij
    exact hbT (by simp only [Sum.elim_inr]; exact Nat.succ_lt_succ hij)
  have hdet : (b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k).det ≠ 0 := b.det_ne_zero
  have hbB := fromBlocks_toBlocks (b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
  rw [← hbB, h21, det_fromBlocks_zero₂₁, det_of_upperTriangular hT] at hdet
  have hG : (b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k).toBlocks₁₁.det ≠ 0 := left_ne_zero_of_mul hdet
  have ht : ∀ i : Fin c, (b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inr i) (Sum.inr i) ≠ 0 :=
    fun i => Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hdet) i (Finset.mem_univ i)
  set g : GL n k := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hG with hg
  have hgv : (g : Matrix n n k) = (b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k).toBlocks₁₁ := rfl
  choose e he using fun i => _root_.GlobalTheory.StepData.NormalForm.exists_valuation_eq_zpow hϖ (Units.mk0 _ (ht i))
  set z : n → k := fun r => if hc : 0 < c then
    (b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inl r) (Sum.inr ⟨0, hc⟩) *
      ((b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inr ⟨0, hc⟩) (Sum.inr ⟨0, hc⟩))⁻¹ else 0 with hz
  set εv : n ⊕ Fin c → kˣ := Sum.elim (fun _ => 1) (fun i => Units.mk0 _ (ht i) * ϖ ^ (-e i)) with hεv
  have hϖ0 : (ϖ : k) ≠ 0 := ϖ.ne_zero
  have key : m = _root_.GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice.nfBasis ϖ g e z * _root_.GlobalTheory.SplitFlip.diagGL εv := by
    clear hbum hu' hbP hdet hbB hw hT h21 hϖ he
    ext r s
    rw [Units.val_mul, _root_.GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice.nfBasis_val, _root_.GlobalTheory.SplitFlip.diagGL_val,
      mul_diagonal]
    rcases r with r | i <;> rcases s with s | j
    · rw [hmb _ _ (by simp [_root_.GlobalTheory.RootEx.lev])]
      simp [hεv, hgv, toBlocks₁₁]
    · by_cases hj : (j : ℕ) = 0
      · rw [hmb _ _ (by simp [_root_.GlobalTheory.RootEx.lev, hj])]
        have hc : 0 < c := j.pos
        have hj' : j = ⟨0, hc⟩ := Fin.ext hj
        subst hj'
        simp only [fromBlocks_apply₁₂, of_apply, hj, if_true, hz, dif_pos hc, hεv, Sum.elim_inr,
          Units.val_mul, Units.val_mk0, Units.val_zpow_eq_zpow_val, _root_.zpow_neg,
          Units.val_inv_eq_inv_val]
        have := ht ⟨0, hc⟩
        field_simp
      · rw [hm0 _ _ (by simp [_root_.GlobalTheory.RootEx.lev]; omega)]
        simp [hj]
    · by_cases hi : (i : ℕ) = 0
      · rw [hmb _ _ (by simp [_root_.GlobalTheory.RootEx.lev, hi])]
        simp only [fromBlocks_apply₂₁, Matrix.zero_apply, zero_mul]
        exact hbT (by simp)
      · rw [hm0 _ _ (by simp [_root_.GlobalTheory.RootEx.lev]; omega)]
        rw [fromBlocks_apply₂₁, Matrix.zero_apply, zero_mul]
    · by_cases hij : i = j
      · subst hij
        have := ht i
        rw [hmb _ _ rfl]
        simp only [fromBlocks_apply₂₂, diagonal_apply_eq, hεv, Sum.elim_inr,
          Units.val_mul, Units.val_mk0, Units.val_zpow_eq_zpow_val, _root_.zpow_neg,
          Units.val_inv_eq_inv_val]
        field_simp
      · rw [hm0 _ _ (by simp [_root_.GlobalTheory.RootEx.lev]; omega)]
        simp [diagonal_apply_ne _ hij]
  have hεinv : (_root_.GlobalTheory.SplitFlip.diagGL εv)⁻¹ = _root_.GlobalTheory.SplitFlip.diagGL εv⁻¹ := by
    apply inv_eq_of_mul_eq_one_right
    ext i j
    rw [Units.val_mul, _root_.GlobalTheory.SplitFlip.diagGL_val, _root_.GlobalTheory.SplitFlip.diagGL_val,
      diagonal_mul_diagonal, Units.val_one]
    simp [diagonal_apply, Matrix.one_apply]
  have hv0 : valuation k (ϖ : k) ≠ 0 := (map_ne_zero _).mpr hϖ0
  have hval : ∀ i, valuation k (εv i : k) = 1 := by
    rintro (i | i)
    · simp [hεv]
    · have hei := he i
      rw [Units.val_mk0] at hei
      simp only [hεv, Sum.elim_inr, Units.val_mul, Units.val_mk0, Units.val_zpow_eq_zpow_val,
        map_mul, map_zpow₀]
      rw [hei, ← zpow_add₀ hv0, add_neg_cancel, zpow_zero]
  have hε : _root_.GlobalTheory.SplitFlip.diagGL εv ∈ _root_.GlobalTheory.SplitWeil.KO k (n ⊕ Fin c) := by
    rw [_root_.GlobalTheory.SplitFlip.mem_KO_iff]
    constructor
    · intro i j
      rw [_root_.GlobalTheory.SplitFlip.diagGL_val, diagonal_apply]
      split_ifs
      · rw [Valuation.mem_integer_iff, hval]
      · exact zero_mem _
    · intro i j
      rw [hεinv, _root_.GlobalTheory.SplitFlip.diagGL_val, diagonal_apply]
      split_ifs
      · rw [Valuation.mem_integer_iff, Pi.inv_apply, Units.val_inv_eq_inv_val, map_inv₀, hval,
          inv_one]
      · exact zero_mem _
  refine ⟨u'⁻¹, inv_mem hu', g, e, z, ?_, ?_⟩
  · have hub : u'⁻¹ * (b * w) = _root_.GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice.nfBasis ϖ g e z * (_root_.GlobalTheory.SplitFlip.diagGL εv * w) := by
      rw [hbum, key]; group
    rw [hub, latOf_mul_of_mem_KO' _ _ (mul_mem hε hw)]
  · rw [latOf_mul_of_mem_KO' _ _ hw]
    unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice.MeetsIn
    intro y
    rw [_root_.GlobalTheory.StepData.mem_latOf, _root_.GlobalTheory.StepData.mem_latOf]
    have h1 : (b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) *ᵥ Sum.elim ((↑g⁻¹ : Matrix n n k) *ᵥ y) 0 =
        Sum.elim y 0 := by
      rw [← hbB, h21, fromBlocks_mulVec]
      simp [← hgv, mulVec_mulVec]
    have hv : (↑b⁻¹ : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) *ᵥ Sum.elim y 0 =
        Sum.elim ((↑g⁻¹ : Matrix n n k) *ᵥ y) 0 := by
      rw [← h1, mulVec_mulVec, Units.inv_mul, one_mulVec]
    rw [hv]
    constructor
    · intro H i
      simpa using H (Sum.inl i)
    · rintro H (i | i)
      · simpa using H i
      · simp

end GlobalTheory.StepData.NormalForm
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.OmegaColumnSlices

namespace GlobalTheory.IndefiniteRowSideFullHecke.OmegaColumnSlices

theorem hat_mem_SB_and_hat_omCol : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k) (ε : k), HasConductor ψ 1 → IsUnitVol ν → valuation k ε = 1 → ∀ (n : Type) [Fintype n] [DecidableEq n] (μz : kˣ →* ℂˣ) (h : GL n k), ∀ φ ∈ SB (n → k), hat ψ ν ε φ ∈ SB (n → k) ∧ hat ψ ν ε (omCol μz h φ) = omRow μz h (hat ψ ν ε φ) := by
  intro k _ _ _ _ _ _ ψ ν ε hψ hν hε n _ _ μz h φ hφ
  haveI := hν.1
  haveI := secondCountable k
  haveI := t2Space k
  have hε0 : ε ≠ 0 := by
    rintro rfl
    simp at hε
  constructor
  · have hF := FourierPi.fourier_mem_SB (Measure.pi fun _ : n => ν) hψ hφ
    have e : hat ψ ν ε φ = (fun y : n → k => ∫ x, φ x * (ψ (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ : n => ν)) ∘
        (Homeomorph.smulOfNeZero ε hε0 : (n → k) ≃ₜ (n → k)) := by
      funext η
      simp only [hat, Function.comp, Homeomorph.smulOfNeZero_apply, dotProduct_smul, smul_eq_mul,
        dotProduct_comm η]
    rw [e]
    exact ⟨hF.1.comp_continuous (Homeomorph.continuous _), hF.2.comp_homeomorph _⟩
  · funext η
    have key := integral_comp_mulVec_eq_smul ν h⁻¹ (fun y => φ y * (ψ (ε * ((η ᵥ* h.val) ⬝ᵥ y)) : ℂ))
    have e1 : ∀ y : n → k, (η ᵥ* h.val) ⬝ᵥ ((h⁻¹).val *ᵥ y) = η ⬝ᵥ y := by
      intro y
      rw [← dotProduct_mulVec, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
    simp only [e1] at key
    have hp := nabs_pos' (Matrix.GeneralLinearGroup.det h)
    have e2 : (nabs k (Matrix.GeneralLinearGroup.det h⁻¹))⁻¹ = nabs k (Matrix.GeneralLinearGroup.det h) := by
      simp [nabs]
    have e3 : nabs k (Matrix.GeneralLinearGroup.det h) ^ (-(1 : ℝ) / 2) * nabs k (Matrix.GeneralLinearGroup.det h) =
        nabs k (Matrix.GeneralLinearGroup.det h) ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_add_one hp.ne']
      norm_num
    simp only [hat, omCol, omRow, mul_assoc, integral_const_mul]
    rw [key, e2, ← e3, Complex.real_smul, Complex.ofReal_mul, mul_assoc]

end GlobalTheory.IndefiniteRowSideFullHecke.OmegaColumnSlices
end

section

open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel

theorem _root_.GlobalTheory.T.unramified_char_sums_strict_cone_vanish_each : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (r n : ℕ) (E : Fin n → Multiset ((Fin r → kˣ) →* ℂˣ)) (c : Fin n → ℂ), (∀ i, ∀ χ ∈ E i, ∀ t ∈ torusO k (Fin r), χ t = 1) → (∀ t ∈ IndefiniteRowSideFullHecke.ExponentSeparationTwistedDiscreteSeries.strictCone ϖ r, ∑ i, c i * IndefiniteRowSideFullHecke.ExponentSeparationTwistedDiscreteSeries.charSum (E i) t = 0) → ∀ [DecidableEq ((Fin r → kˣ) →* ℂˣ)] (χ : (Fin r → kˣ) →* ℂˣ), ∑ i, c i * ((E i).count χ : ℂ) = 0 := by
  first | exact @GlobalTheory.ConeCount.sum_count_eq_zero | exact GlobalTheory.ConeCount.sum_count_eq_zero | (intros; apply GlobalTheory.ConeCount.sum_count_eq_zero <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

theorem _root_.GlobalTheory.T.fourierJacobiUnipotent_eq_prod_rootExchange : ∀ (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (_ : 1 ≤ ρ) (_ : ρ < c), (∀ g, g ∈ NFJ k n c ρ ↔ ∃ x ∈ N k n c ρ, ∃ y ∈ N k n c (ρ + 1), g = x * y) ∧ (∀ g : GL (n ⊕ Fin c) k, g ∈ NFJ k n c ρ ↔ ∀ r s : n ⊕ Fin c, Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) s ≤ Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) r → g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s) ∧ ∀ g ∈ NFJ k n c ρ, ∃ u ∈ N k n c (ρ + 1), ∃ β : n → k, g = u * colE c (ρ + 1) β := by
  first | exact @GlobalTheory.RootEx.FJUnipotent.fj_unipotent | exact GlobalTheory.RootEx.FJUnipotent.fj_unipotent | (intros; apply GlobalTheory.RootEx.FJUnipotent.fj_unipotent <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

theorem _root_.GlobalTheory.T.schwartzFourierTransformPi_surjective_schwartzBruhat : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν), (∀ Φ₀ : SB (n → k), hat ψ ν Φ₀.1 ∈ SB (n → k)) ∧ ∀ g : SB (n → k), ∃ Φ₀ : SB (n → k), hat ψ ν Φ₀.1 = g.1 := by
  first | exact @GlobalTheory.SplitWeil.FourierSurj.hat_surjective | exact GlobalTheory.SplitWeil.FourierSurj.hat_surjective | (intros; apply GlobalTheory.SplitWeil.FourierSurj.hat_surjective <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

namespace GlobalTheory.RootEx.ParabolicEntries

open GlobalTheory.RootEx.Radical

variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}

def Par (L : ℕ) (b : Fin c → ℕ) (M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) : Prop :=
  ∀ r s : n ⊕ Fin c, (r.isRight ∨ s.isRight) → Sum.elim (fun _ => L) b s ≤ Sum.elim (fun _ => L) b r →
    M r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s

omit [Fintype n] in
theorem Par.blockTri {L : ℕ} {b : Fin c → ℕ} {M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k} (h : Par L b M) :
    M.BlockTriangular (Sum.elim (fun _ => L) b) := by
  intro r s hrs
  have hne : r ≠ s := by
    rintro rfl
    exact lt_irrefl _ hrs
  rw [h r s _ hrs.le, Matrix.one_apply_ne hne]
  rcases r with r | r <;> rcases s with s | s <;> simp_all

theorem Par.mul_left {L : ℕ} {b : Fin c → ℕ} {M M' : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k} (h : Par L b M)
    (h' : M'.BlockTriangular (Sum.elim (fun _ => L) b)) {r s : n ⊕ Fin c} (hr : r.isRight)
    (hrs : Sum.elim (fun _ => L) b s ≤ Sum.elim (fun _ => L) b r) : (M * M') r s = M' r s := by
  have : (M * M') r s = ((1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * M') r s := by
    simp only [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    rcases le_or_gt (Sum.elim (fun _ => L) b t) (Sum.elim (fun _ => L) b r) with ht | ht
    · rw [h r t (Or.inl hr) ht]
    · rw [h' (lt_of_le_of_lt hrs ht), mul_zero, mul_zero]
  rw [this, Matrix.one_mul]

theorem Par.mul_right {L : ℕ} {b : Fin c → ℕ} {M M' : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k} (h : Par L b M)
    (h' : M'.BlockTriangular (Sum.elim (fun _ => L) b)) {r s : n ⊕ Fin c} (hs : s.isRight)
    (hrs : Sum.elim (fun _ => L) b s ≤ Sum.elim (fun _ => L) b r) : (M' * M) r s = M' r s := by
  have : (M' * M) r s = (M' * (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)) r s := by
    simp only [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    rcases le_or_gt (Sum.elim (fun _ => L) b s) (Sum.elim (fun _ => L) b t) with ht | ht
    · rw [h t s (Or.inr hs) ht]
    · rw [h' (lt_of_lt_of_le ht hrs), zero_mul, zero_mul]
  rw [this, Matrix.mul_one]

theorem Par.blockTri_inv {L : ℕ} {b : Fin c → ℕ} {g : GL (n ⊕ Fin c) k} (h : Par L b g.val) :
    (g⁻¹).val.BlockTriangular (Sum.elim (fun _ => L) b) := by
  letI : Invertible g.val := g.invertible
  rw [Matrix.coe_units_inv]
  exact Matrix.blockTriangular_inv_of_blockTriangular h.blockTri

def parGroup (k : Type*) [Field k] (n : Type*) [Fintype n] [DecidableEq n] (L : ℕ) (b : Fin c → ℕ) :
    Subgroup (GL (n ⊕ Fin c) k) where
  carrier := {g | Par L b g.val}
  one_mem' := fun _ _ _ _ => rfl
  mul_mem' := by
    intro g h hg hh r s hor hrs
    rw [Units.val_mul]
    rcases hor with hr | hs
    · rw [Par.mul_left hg (Par.blockTri hh) hr hrs, hh r s (Or.inl hr) hrs]
    · rw [Par.mul_right hh (Par.blockTri hg) hs hrs, hg r s (Or.inr hs) hrs]
  inv_mem' := by
    intro g hg r s hor hrs
    rcases hor with hr | hs
    · rw [← Par.mul_left hg (Par.blockTri_inv hg) hr hrs, Units.mul_inv]
    · rw [← Par.mul_right hg (Par.blockTri_inv hg) hs hrs, Units.inv_mul]

theorem embX_mem (L : ℕ) (b : Fin c → ℕ) (x : GL n k) : embX c x ∈ parGroup k n L b := by
  intro r s hor _
  rw [embX_val]
  rcases r with r | r <;> rcases s with s | s <;> simp_all [Matrix.one_apply]

theorem toBlocks₁₁_mul {L : ℕ} {b : Fin c → ℕ} {g h : GL (n ⊕ Fin c) k} (hg : g ∈ parGroup k n L b)
    (hh : h ∈ parGroup k n L b) : (g * h).val.toBlocks₁₁ = g.val.toBlocks₁₁ * h.val.toBlocks₁₁ := by
  ext r s
  simp only [Units.val_mul, Matrix.toBlocks₁₁, Matrix.of_apply, Matrix.mul_apply, Fintype.sum_sum_type]
  rw [add_eq_left]
  refine Finset.sum_eq_zero fun t _ => ?_
  rcases le_total (b t) L with ht | ht
  · rw [hg (Sum.inl r) (Sum.inr t) (by simp) ht, Matrix.one_apply_ne (by simp), zero_mul]
  · rw [hh (Sum.inr t) (Sum.inl s) (by simp) ht, Matrix.one_apply_ne (by simp), mul_zero]

theorem exists_eq_embX_mul {L : ℕ} {b : Fin c → ℕ} {g : GL (n ⊕ Fin c) k} (hg : g ∈ parGroup k n L b) :
    ∃ (x : GL n k) (u : GL (n ⊕ Fin c) k), Uni (Sum.elim (fun _ => L) b) u.val ∧ g = embX c x * u := by
  have h1 : ((1 : GL (n ⊕ Fin c) k)).val.toBlocks₁₁ = 1 := by
    ext r s
    simp [Matrix.toBlocks₁₁, Matrix.one_apply]
  let x : GL n k := ⟨g.val.toBlocks₁₁, (g⁻¹).val.toBlocks₁₁,
    by rw [← toBlocks₁₁_mul hg (inv_mem hg), mul_inv_cancel, h1],
    by rw [← toBlocks₁₁_mul (inv_mem hg) hg, inv_mul_cancel, h1]⟩
  refine ⟨x, embX c x⁻¹ * g, ?_, by rw [map_inv, mul_inv_cancel_left]⟩
  have hm : embX c x⁻¹ * g ∈ parGroup k n L b := mul_mem (embX_mem L b _) hg
  have h11 : (embX c x⁻¹ * g).val.toBlocks₁₁ = 1 := by
    rw [toBlocks₁₁_mul (embX_mem L b _) hg, embX_val, Matrix.toBlocks_fromBlocks₁₁]
    exact x.inv_mul
  intro r s hrs
  by_cases hor : r.isRight ∨ s.isRight
  · exact hm r s hor hrs
  · rcases r with r | r <;> rcases s with s | s
    · have := congrFun (congrFun h11 r) s
      simp only [Matrix.toBlocks₁₁, Matrix.of_apply] at this
      rw [this]
      simp [Matrix.one_apply]
    all_goals simp at hor

theorem embX_mem_R (p : ℕ) (x : GL n k) : embX c x ∈ R k n c p :=
  Subgroup.mem_sup_left ⟨x, rfl⟩

theorem R_le {L p : ℕ} {b : Fin c → ℕ} (h : N k n c p ≤ parGroup k n L b) : R k n c p ≤ parGroup k n L b := by
  refine sup_le ?_ h
  rintro _ ⟨x, rfl⟩
  exact embX_mem L b x

theorem mem_R_iff_and_mem_RFJ_iff : ∀ (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ), (∀ g : GL (n ⊕ Fin c) k, g ∈ R k n c ρ ↔ ∀ r s : n ⊕ Fin c, (r.isRight ∨ s.isRight) → Sum.elim (fun _ => ρ) (fun i : Fin c => i.val + 1) s ≤ Sum.elim (fun _ => ρ) (fun i : Fin c => i.val + 1) r → g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s) ∧ (1 ≤ ρ → ρ < c → ∀ g : GL (n ⊕ Fin c) k, g ∈ RFJ k n c ρ ↔ ∀ r s : n ⊕ Fin c, (r.isRight ∨ s.isRight) → Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) s ≤ Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) r → g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s) := by
  intro k _ n _ _ c ρ
  refine ⟨fun g => ⟨fun hg => ?_, fun hg => ?_⟩, fun h1 hc g => ⟨fun hg => ?_, fun hg => ?_⟩⟩
  · exact R_le (L := ρ) (b := fun i : Fin c => i.val + 1)
      (fun u hu r s _ hrs => (mem_N_iff u).1 hu r s hrs) hg
  · obtain ⟨x, u, hu, rfl⟩ := exists_eq_embX_mul (L := ρ) (b := fun i : Fin c => i.val + 1) hg
    exact mul_mem (embX_mem_R ρ x) (Subgroup.mem_sup_right ((mem_N_iff u).2 hu))
  · have hN : NFJ k n c ρ ≤ parGroup k n (2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) :=
      fun u hu r s _ hrs => ((GlobalTheory.RootEx.FJUnipotent.fj_unipotent k n c ρ h1 hc).2.1 u).1 hu r s hrs
    exact sup_le (R_le (le_sup_left.trans hN)) (R_le (le_sup_right.trans hN)) hg
  · obtain ⟨x, u, hu, rfl⟩ :=
      exists_eq_embX_mul (L := 2 * ρ + 1) (b := fun i : Fin c => 2 * (i.val + 1)) hg
    have hN : NFJ k n c ρ ≤ RFJ k n c ρ := sup_le_sup le_sup_right le_sup_right
    exact mul_mem (Subgroup.mem_sup_left (embX_mem_R ρ x))
      (hN (((GlobalTheory.RootEx.FJUnipotent.fj_unipotent k n c ρ h1 hc).2.1 u).2 hu))

end GlobalTheory.RootEx.ParabolicEntries
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.ColFourier

theorem _root_.GlobalTheory.T.partialColumnFourier_inversion_schwartzBruhat : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (A C : Type) [Fintype A] [DecidableEq A] [DecidableEq C] (ψ : AddChar k Circle) (m : Measure k), HasConductor ψ 1 → IsUnitVol m → ∀ (P : Finset C), ∀ Ξ ∈ SB (Matrix A C k), fourierInt ψ⁻¹ m P (fourierInt ψ m P Ξ) = Ξ := by
  first | exact @GlobalTheory.ColFourier.fourierInt_inv_fourierInt | exact GlobalTheory.ColFourier.fourierInt_inv_fourierInt | (intros; apply GlobalTheory.ColFourier.fourierInt_inv_fourierInt <;> assumption)
end

section

open MeasureTheory GlobalTheory.FunObj

theorem _root_.GlobalTheory.T.exists_sum_pureTensor_of_isTensor_depth : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (G : GlobalTheory.SplitFlip.Grid k) (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (e : ℕ) (γ : List GlobalTheory.SplitFlip.Edge) (T : G.Args → ℂ), G.IsTensor ϖ e γ T → ∃ (n : ℕ) (x : Fin n → ℂ) (φ : Fin n → ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ), (∀ i, ∀ b ∈ γ, GlobalTheory.SplitFlip.IsNatDatum ϖ e (φ i b)) ∧ ∀ z, T z = ∑ i, x i * G.lines₂ γ (φ i) z := by
  first | exact @GlobalTheory.TensorExpansion.exists_sum_pureTensor | exact GlobalTheory.TensorExpansion.exists_sum_pureTensor | (intros; apply GlobalTheory.TensorExpansion.exists_sum_pureTensor <;> assumption)
end
