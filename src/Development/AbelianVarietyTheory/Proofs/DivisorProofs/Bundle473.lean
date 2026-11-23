module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle403
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle404
public import Formalism.DoubleCosetMeasures.Statement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle422
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle426
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.PiTensorProduct
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

open ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.RankCoinv.Decomp
open GlobalTheory.SplitFlip GlobalTheory.RankCoinv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A D : Type}

theorem val_unif_pow_le {ϖ : kˣ} (hϖ : IsUnif ϖ) {n m : ℕ} (h : n ≤ m) :
    valuation k ((ϖ ^ m : kˣ) : k) ≤ valuation k ((ϖ ^ n : kˣ) : k) := by
  simp only [Units.val_pow_eq_pow_val, map_pow]
  exact pow_le_pow_right_of_le_one' (show valuation k (ϖ : k) ≤ 1 from hϖ ▸ uniformizer_lt_one.le) h

theorem box_mono {ϖ : kˣ} (hϖ : IsUnif ϖ) (X : Matrix A D k) {n m : ℕ} (h : n ≤ m) :
    box ϖ X (fun _ => m) ⊆ box ϖ X (fun _ => n) :=
  fun _ hY i j => (hY i j).trans (val_unif_pow_le hϖ h)

theorem mem_box_self (ϖ : kˣ) (X : Matrix A D k) (e : A → ℕ) : X ∈ box ϖ X e :=
  fun i j => by simp

theorem eq_of_forall_mem_box {ϖ : kˣ} (hϖ : IsUnif ϖ) {X Y : Matrix A D k}
    (h : ∀ n : ℕ, Y ∈ box ϖ X (fun _ => n)) : Y = X := by
  ext i j
  by_contra hne
  have h0 : valuation k (Y i j - X i j) ≠ 0 := by simpa [sub_eq_zero] using hne
  obtain ⟨n, hn⟩ := exists_pow_lt₀ (show valuation k (ϖ : k) < 1 from hϖ ▸ uniformizer_lt_one) (Units.mk0 _ h0)
  have := h n i j
  simp only [Units.val_pow_eq_pow_val, map_pow] at this
  exact absurd this (not_le.2 hn)

variable [Fintype A] [Fintype D]

theorem exists_box_subset {ϖ : kˣ} (hϖ : IsUnif ϖ) {X : Matrix A D k} {U : Set (Matrix A D k)}
    (hU : U ∈ nhds X) : ∃ n : ℕ, box ϖ X (fun _ => n) ⊆ U := by
  refine exists_subset_nhds_of_isCompact' (V := fun n : ℕ => box ϖ X (fun _ => n))
    (Antitone.directed_ge fun a b h => box_mono hϖ X h) (fun n => isCompact_box ϖ X _)
    (fun n => (isClopen_box ϖ X _).isClosed) ?_
  apply mem_nhdsSet_iff_forall.2
  intro Y hY
  have hYX : Y = X := eq_of_forall_mem_box hϖ (Set.mem_iInter.1 hY)
  simpa only [hYX] using hU

theorem exists_sum_boxFn (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ) :
    ∀ Φ ∈ GlobalTheory.WeilM.SB (Matrix A D k), ∃ m₁ : ℕ, ∀ m ≥ m₁, ∃ s : Finset (Matrix A D k),
      Φ = ∑ c ∈ s, Φ c • GlobalTheory.RankCoinv.boxFn ϖ c (fun _ => m) ∧
      ∀ c ∈ s, ∀ X ∈ GlobalTheory.RankCoinv.box ϖ c (fun _ => m), Φ X = Φ c := by
  classical
  intro Φ hΦ
  obtain ⟨hlc, hcs⟩ := hΦ
  have hrad : ∀ X, ∃ n : ℕ, box ϖ X (fun _ => n) ⊆ {Y | Φ Y = Φ X} := fun X =>
    exists_box_subset hϖ ((hlc.isOpen_fiber (Φ X)).mem_nhds rfl)
  choose n hn using hrad
  obtain ⟨t, ht⟩ := IsCompact.elim_finite_subcover hcs (fun X => box ϖ X (fun _ => n X))
    (fun X => (isClopen_box ϖ X _).isOpen) (fun Y _ => Set.mem_iUnion.2 ⟨Y, mem_box_self ϖ Y _⟩)
  refine ⟨t.sup n, fun m hm => ?_⟩
  have hconst : ∀ Y ∈ tsupport Φ, ∀ Z ∈ box ϖ Y (fun _ => m), Φ Z = Φ Y := by
    intro Y hY Z hZ
    obtain ⟨X, hXt, hYX⟩ := Set.mem_iUnion₂.1 (ht hY)
    have hsub : box ϖ Y (fun _ => m) ⊆ box ϖ X (fun _ => n X) := by
      rw [← box_eq_of_mem hYX]; exact box_mono hϖ Y ((Finset.le_sup hXt).trans hm)
    have h1 : Φ Z = Φ X := hn X (hsub hZ)
    have h2 : Φ Y = Φ X := hn X (hsub (mem_box_self ϖ Y _))
    rw [h1, h2]
  let rep : Set (Matrix A D k) → Matrix A D k := fun B =>
    if h : ∃ Z, box ϖ Z (fun _ => m) = B then h.choose else 0
  have hrep : ∀ Y, box ϖ (rep (box ϖ Y (fun _ => m))) (fun _ => m) = box ϖ Y (fun _ => m) := by
    intro Y
    have h : ∃ Z, box ϖ Z (fun _ => m) = box ϖ Y (fun _ => m) := ⟨Y, rfl⟩
    rw [show rep (box ϖ Y (fun _ => m)) = h.choose from dif_pos h]
    exact h.choose_spec
  obtain ⟨s₀, hs₀⟩ := IsCompact.elim_finite_subcover hcs
    (fun Y : tsupport Φ => box ϖ (Y : Matrix A D k) (fun _ => m))
    (fun Y => (isClopen_box ϖ _ _).isOpen) (fun Y hY => Set.mem_iUnion.2 ⟨⟨Y, hY⟩, mem_box_self ϖ Y _⟩)
  let s : Finset (Matrix A D k) := s₀.image (fun Y : tsupport Φ => rep (box ϖ (Y : Matrix A D k) (fun _ => m)))
  have hs : ∀ c ∈ s, ∃ Y ∈ tsupport Φ, c = rep (box ϖ Y (fun _ => m)) := by
    intro c hc
    obtain ⟨Y, -, rfl⟩ := Finset.mem_image.1 hc
    exact ⟨Y, Y.2, rfl⟩
  have hval : ∀ c ∈ s, ∀ Z ∈ box ϖ c (fun _ => m), Φ Z = Φ c := by
    intro c hc Z hZ
    obtain ⟨Y, hY, rfl⟩ := hs c hc
    rw [hrep] at hZ
    have hcY : rep (box ϖ Y (fun _ => m)) ∈ box ϖ Y (fun _ => m) := by
      have := mem_box_self ϖ (rep (box ϖ Y (fun _ => m))) (fun _ => m)
      rwa [hrep] at this
    rw [hconst Y hY Z hZ, hconst Y hY _ hcY]
  have huniq : ∀ c ∈ s, ∀ c' ∈ s, ∀ Z, Z ∈ box ϖ c (fun _ => m) → Z ∈ box ϖ c' (fun _ => m) → c = c' := by
    intro c hc c' hc' Z hZ hZ'
    obtain ⟨Y, -, rfl⟩ := hs c hc
    obtain ⟨Y', -, rfl⟩ := hs c' hc'
    have e1 := box_eq_of_mem hZ
    have e2 := box_eq_of_mem hZ'
    rw [hrep] at e1 e2
    rw [← e1, ← e2]
  have hcov : ∀ Z, Φ Z ≠ 0 → ∃ c ∈ s, Z ∈ box ϖ c (fun _ => m) := by
    intro Z hZ
    obtain ⟨Y, hY, hZY⟩ := Set.mem_iUnion₂.1 (hs₀ (subset_tsupport Φ hZ))
    refine ⟨rep (box ϖ (Y : Matrix A D k) (fun _ => m)), Finset.mem_image_of_mem _ hY, ?_⟩
    rw [hrep]; exact hZY
  refine ⟨s, ?_, hval⟩
  funext Z
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, boxFn]
  by_cases h : ∃ c ∈ s, Z ∈ box ϖ c (fun _ => m)
  · obtain ⟨c, hc, hZ⟩ := h
    rw [Finset.sum_eq_single c]
    · rw [Set.indicator_of_mem hZ, Pi.one_apply, mul_one, hval c hc Z hZ]
    · intro c' hc' hne
      rw [Set.indicator_of_notMem (fun hZ' => hne (huniq c' hc' c hc Z hZ' hZ)), mul_zero]
    · intro hcs'; exact absurd hc hcs'
  · push_neg at h
    rw [Finset.sum_eq_zero fun c hc => by rw [Set.indicator_of_notMem (h c hc), mul_zero]]
    by_contra hZ
    obtain ⟨c, hc, hZc⟩ := hcov Z hZ
    exact h c hc hZc

end GlobalTheory.RankCoinv.Decomp
end
end

section

open ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.RankCoinv
open GlobalTheory.SplitFlip

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
def rowOpMat (i₀ : A) (w : A → k) : Matrix A A k :=
  replicateCol Unit (Pi.single i₀ (1 : k)) * replicateRow Unit w

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem rowOpMat_apply (i₀ : A) (w : A → k) (i a : A) : rowOpMat i₀ w i a = if i = i₀ then w a else 0 := by
  by_cases h : i = i₀
  · subst h; simp [rowOpMat, Matrix.mul_apply]
  · simp [rowOpMat, Matrix.mul_apply, h]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem rowOpMat_mul_self (i₀ : A) (w : A → k) (hw : w i₀ = 0) : rowOpMat i₀ w * rowOpMat i₀ w = 0 := by
  ext i j
  simp [Matrix.mul_apply, rowOpMat_apply, hw]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [DecidableEq D] in
theorem rowOpMat_mul_apply (i₀ : A) (w : A → k) (X : Matrix A D k) (i : A) (j : D) :
    (rowOpMat i₀ w * X) i j = if i = i₀ then ∑ a, w a * X a j else 0 := by
  by_cases h : i = i₀
  · simp [Matrix.mul_apply, rowOpMat_apply, h]
  · simp [Matrix.mul_apply, rowOpMat_apply, h]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem det_one_add_rowOpMat (i₀ : A) (w : A → k) (hw : w i₀ = 0) : (1 + rowOpMat i₀ w).det = 1 := by
  rw [rowOpMat, det_one_add_replicateCol_mul_replicateRow]
  simp [hw]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
def unipRowGL (i₀ : A) (w : A → k) (hw : w i₀ = 0) : GL A k :=
  ⟨1 + rowOpMat i₀ w, 1 - rowOpMat i₀ w,
    by simp [add_mul, mul_sub, rowOpMat_mul_self i₀ w hw],
    by simp [sub_mul, mul_add, rowOpMat_mul_self i₀ w hw]⟩

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem gdet_unipRowGL (i₀ : A) (w : A → k) (hw : w i₀ = 0) : gdet (unipRowGL i₀ w hw) = 1 :=
  Units.ext (det_one_add_rowOpMat i₀ w hw)

theorem valuation_rowSum_le (i₀ : A) (w : A → k) (hw0 : w i₀ = 0) (hw : ∀ a, valuation k (w a) ≤ 1)
    (Z : A → k) (b : ValueGroupWithZero k) (hZ : ∀ a, a ≠ i₀ → valuation k (Z a) ≤ b) :
    valuation k (∑ a, w a * Z a) ≤ b := by
  refine Valuation.map_sum_le _ fun a _ => ?_
  by_cases ha : a = i₀
  · subst ha; simp [hw0]
  · rw [map_mul]
    exact (mul_le_mul' (hw a) (hZ a ha)).trans (by rw [one_mul])

theorem omA_unipRowGL_boxFn (ν β : kˣ →* ℂˣ) (ϖ : kˣ) (i₀ : A) (w : A → k) (hw0 : w i₀ = 0)
    (hw : ∀ a, valuation k (w a) ≤ 1) (C : Matrix A D k) (m : ℕ) :
    omA ν β (unipRowGL i₀ w hw0) 1 (boxFn ϖ C (fun _ => m)) =
      boxFn ϖ (updateRow C i₀ (C i₀ + w ᵥ* C)) (fun _ => m) := by
  funext X
  rw [omA_one_apply, gdet_unipRowGL]
  simp only [map_one, inv_one, Units.val_one, apow_one, one_mul]
  have hinv : ((unipRowGL i₀ w hw0)⁻¹).val = 1 - rowOpMat i₀ w := rfl
  rw [hinv]
  set C' := updateRow C i₀ (C i₀ + w ᵥ* C)
  have hT : ∀ i j, ((1 - rowOpMat i₀ w : Matrix A A k) * X : Matrix A D k) i j - C i j =
      (X i j - C' i j) - (if i = i₀ then ∑ a, w a * (X a j - C a j) else 0) := by
    intro i j
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, rowOpMat_mul_apply]
    by_cases hi : i = i₀
    · subst hi
      simp only [C', updateRow_self, if_true, Pi.add_apply, vecMul, dotProduct, mul_sub, Finset.sum_sub_distrib]
      ring
    · simp [C', hi]
  have hrow : ∀ a, a ≠ i₀ → ∀ j, X a j - C' a j = X a j - C a j := fun a ha j => by simp [C', ha]
  have hbox : (1 - rowOpMat i₀ w) * X ∈ box ϖ C (fun _ => m) ↔ X ∈ box ϖ C' (fun _ => m) := by
    simp only [box, Set.mem_setOf_eq]
    constructor
    · intro h i j
      have hS : valuation k (∑ a, w a * (X a j - C a j)) ≤ valuation k ((ϖ ^ m : kˣ) : k) :=
        valuation_rowSum_le i₀ w hw0 hw _ _ fun a ha => by
          have := h a j
          rwa [hT, if_neg ha, sub_zero, hrow a ha] at this
      have := h i j
      rw [hT] at this
      rw [show X i j - C' i j = ((X i j - C' i j) - (if i = i₀ then ∑ a, w a * (X a j - C a j) else 0)) +
        (if i = i₀ then ∑ a, w a * (X a j - C a j) else 0) by ring]
      refine Valuation.map_add_le _ this ?_
      split_ifs
      · exact hS
      · simp
    · intro h i j
      have hS : valuation k (∑ a, w a * (X a j - C a j)) ≤ valuation k ((ϖ ^ m : kˣ) : k) :=
        valuation_rowSum_le i₀ w hw0 hw _ _ fun a ha => by
          have := h a j
          rwa [hrow a ha] at this
      rw [hT]
      refine Valuation.map_sub_le _ (h i j) ?_
      split_ifs
      · exact hS
      · simp
  unfold boxFn
  by_cases hX : X ∈ box ϖ C' (fun _ => m)
  · rw [Set.indicator_of_mem hX, Set.indicator_of_mem (hbox.2 hX)]; rfl
  · rw [Set.indicator_of_notMem hX, Set.indicator_of_notMem (fun h => hX (hbox.1 h))]
end GlobalTheory.RankCoinv

theorem GlobalTheory.RankCoinv.boxFn_unip_row_sub_mem_twistSpan : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (ν β : kˣ →* ℂˣ) (i₀ : A) (r c m : ℕ) (C : Matrix A D k) (H : Matrix (Fin r) A k) (t : Fin r → k), (∀ l, H l i₀ = 0) → (∀ l i, valuation k (H l i) ≤ valuation k (((ϖ ^ c)⁻¹ : kˣ) : k)) → (∀ l, valuation k (t l) ≤ valuation k ((ϖ ^ c : kˣ) : k)) → GlobalTheory.RankCoinv.boxFn ϖ (Matrix.updateRow C i₀ (C i₀ + t ᵥ* (H * C))) (fun _ => m) - GlobalTheory.RankCoinv.boxFn ϖ C (fun _ => m) ∈ GlobalTheory.RankCoinv.twistSpan ν β := by
  intro k _ _ _ _ A D _ _ _ _ ϖ ν β i₀ r c m C H t hH0 hH ht
  have hw0 : (t ᵥ* H) i₀ = 0 := by simp [vecMul, dotProduct, hH0]
  have hw : ∀ a, valuation k ((t ᵥ* H) a) ≤ 1 := fun a => by
    show valuation k (∑ l, t l * H l a) ≤ 1
    refine Valuation.map_sum_le _ fun l _ => ?_
    rw [map_mul]
    refine (mul_le_mul' (ht l) (hH l a)).trans (le_of_eq ?_)
    rw [← map_mul, Units.mul_inv, map_one]
  rw [← vecMul_vecMul, ← GlobalTheory.RankCoinv.omA_unipRowGL_boxFn ν β ϖ i₀ (t ᵥ* H) hw0 hw C m]
  exact GlobalTheory.RankCoinv.sub_mem_twistSpan ν β _ (GlobalTheory.RankCoinv.boxFn_mem_SB ϖ C _)
end
end

section

open GlobalTheory.WeilM Matrix

noncomputable section
namespace GlobalTheory.RankStrata

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {A A' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]

def rowRenum (e : A ≃ A') : Matrix A D k ≃ₜ Matrix A' D k where
  toFun Y := Y.submatrix e.symm id
  invFun Y' := Y'.submatrix e id
  left_inv Y := by ext i j; simp
  right_inv Y' := by ext i j; simp
  continuous_toFun := continuous_id.matrix_submatrix _ _
  continuous_invFun := continuous_id.matrix_submatrix _ _

theorem comp_rowRenum_mem_SB (e : A ≃ A') {f : Matrix A' D k → ℂ} (hf : f ∈ SB (Matrix A' D k)) :
    (fun Y : Matrix A D k => f (Y.submatrix e.symm id)) ∈ SB (Matrix A D k) :=
  ⟨hf.1.comp_continuous (rowRenum (k := k) (D := D) e).continuous,
    hf.2.comp_homeomorph (rowRenum (k := k) (D := D) e)⟩

def glRenum (e : A ≃ A') : GL A' k →* GL A k :=
  Units.map (Matrix.reindexAlgEquiv k k e.symm).toMonoidHom

theorem glRenum_val (e : A ≃ A') (g : GL A' k) : (glRenum e g).val = g.val.submatrix e e := rfl

theorem gdet_glRenum (e : A ≃ A') (g : GL A' k) :
    GlobalTheory.SplitFlip.gdet (glRenum e g) = GlobalTheory.SplitFlip.gdet g := by
  ext
  simp [GlobalTheory.SplitFlip.gdet, glRenum_val, Matrix.det_submatrix_equiv_self]

theorem omB_comp_rowRenum (ν : kˣ →* ℂˣ) (e : A ≃ A') (g : GL A' k) (Ψ : Matrix A' D k → ℂ) :
    (fun Y : Matrix A D k => GlobalTheory.SplitFlip.omB ν ν g 1 Ψ (Y.submatrix e.symm id)) =
      GlobalTheory.SplitFlip.omB ν ν (glRenum e g) 1 (fun Y : Matrix A D k => Ψ (Y.submatrix e.symm id)) := by
  funext Y
  simp only [GlobalTheory.SplitFlip.omB, gdet_glRenum, Units.val_one, Matrix.mul_one]
  congr 1
  · simp
  · congr 1
    rw [glRenum_val]
    have hY : Y = (Y.submatrix e.symm id).submatrix e id := by ext; simp
    conv_rhs => rw [hY]
    rw [show (g.val.submatrix e e)ᵀ = (g.valᵀ).submatrix e e from rfl, Matrix.submatrix_mul_equiv]
    ext; simp

theorem rowRenum_SB_Nsp : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A A' D : Type) [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
    (ν : kˣ →* ℂˣ) (e : A ≃ A'),
    (∀ f ∈ SB (Matrix A' D k), (fun Y : Matrix A D k => f (Y.submatrix e.symm id)) ∈ SB (Matrix A D k)) ∧
    (∀ f ∈ GlobalTheory.RankStrata.Nsp k A' D ν,
      (fun Y : Matrix A D k => f (Y.submatrix e.symm id)) ∈ GlobalTheory.RankStrata.Nsp k A D ν) := by
  intro k _ _ _ _ A A' D _ _ _ _ _ _ ν e
  refine ⟨fun f hf => comp_rowRenum_mem_SB e hf, ?_⟩
  let L : (Matrix A' D k → ℂ) →ₗ[ℂ] (Matrix A D k → ℂ) :=
    LinearMap.funLeft ℂ ℂ (fun Y : Matrix A D k => Y.submatrix e.symm id)
  have hle : Nsp k A' D ν ≤ (Nsp k A D ν).comap L := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, Ψ', hΨ', rfl⟩
    show L (GlobalTheory.SplitFlip.omB ν ν g 1 Ψ' - Ψ') ∈ Nsp k A D ν
    rw [map_sub]
    have h1 : L (GlobalTheory.SplitFlip.omB ν ν g 1 Ψ') =
        GlobalTheory.SplitFlip.omB ν ν (glRenum e g) 1 (fun Y : Matrix A D k => Ψ' (Y.submatrix e.symm id)) :=
      omB_comp_rowRenum ν e g Ψ'
    rw [h1]
    exact sub_mem_Nsp ν (glRenum e g) (comp_rowRenum_mem_SB e hΨ')
  intro f hf
  exact hle hf

end GlobalTheory.RankStrata
end
end

section

noncomputable section

open ValuativeRel
open scoped Matrix

namespace GlobalTheory.FullRankCoinv.UnitMinor

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def unitMinorSet (n d : ℕ) : Set (Matrix (Fin n) (Fin d) k) :=
  {Y | (∀ i j, Y i j ∈ 𝒪[k]) ∧ ∃ f : Fin n ↪ Fin d, valuation k (Y.submatrix id f).det = 1}

def lastCols (n d : ℕ) (h : n ≤ d) : Fin n ↪ Fin d :=
  ⟨fun i => ⟨d - n + i, by omega⟩, fun a b hab => Fin.ext (by simpa using congrArg Fin.val hab)⟩

theorem lastCols_val (n d : ℕ) (h : n ≤ d) (i : Fin n) : (lastCols n d h i : ℕ) = d - n + i := rfl

section
open MeasureTheory GlobalTheory.SplitFlip

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

variable {k}

theorem smallF_lact [MeasurableSpace k] [BorelSpace k] (n d : ℕ) (ν : kˣ →* ℂˣ) (h : GL (Fin n) k)
    (Φ : Matrix (Fin n) (Fin d) k → ℂ) (Y : Matrix (Fin n) (Fin d) k) :
    smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν (GlobalTheory.FullRankCoinv.lact ν h Φ) Y =
      smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Φ Y := by
  unfold smallF GlobalTheory.FullRankCoinv.lact
  have hI := integral_mul_left_eq_self (μ := haarVol (GlobalTheory.SplitWeil.KO k (Fin n)))
    (fun g : GL (Fin n) k => Φ (g.val * Y) * (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card (Fin d) : ℂ) / 2))
    (invT h)⁻¹
  rw [← hI]
  congr 1; funext g
  have e1 : gdet ((invT h)⁻¹ * g) = gdet h * gdet g := by
    rw [gdet_mul, show gdet (invT h)⁻¹ = (gdet (invT h))⁻¹ from map_inv _ _, gdet_invT, inv_inv]
  simp only [e1, Units.val_mul, invT_inv_val, map_mul, apow_mul, Matrix.mul_assoc, Fintype.card_fin]
  ring

end

end GlobalTheory.FullRankCoinv.UnitMinor
end
end

section

open GlobalTheory.EtC.GmStep

namespace GlobalTheory.EtC.GmStep

theorem laurentPi_bijective : ∀ (n : ℕ) (B : Fin n → Type) [∀ j, CommRing (B j)], Function.Bijective (Pi.ringHom (fun j => laurentMap (Pi.evalRingHom B j)) : LaurentPolynomial (∀ j, B j) →+* ∀ j, LaurentPolynomial (B j)) := by
  intro n B _
  have hap : ∀ (x : LaurentPolynomial (∀ j, B j)) k, (Pi.ringHom (fun j => laurentMap (Pi.evalRingHom B j)) : LaurentPolynomial (∀ j, B j) →+* ∀ j, LaurentPolynomial (B j)) x k = laurentMap (Pi.evalRingHom B k) x := fun _ _ => rfl
  constructor
  · rw [injective_iff_map_eq_zero]
    intro p hp
    have hc : p.coeff = 0 := by
      ext m j
      have h1 := congrArg (fun r : ∀ j, LaurentPolynomial (B j) => (r j).coeff m) hp
      simp only [hap, Pi.zero_apply, laurentMap_coeff, Finsupp.mapRange_apply] at h1
      simpa using h1
    exact AddMonoidAlgebra.ext hc
  · intro F
    have hsub : ∀ j (q : LaurentPolynomial (B j)), Pi.single j q ∈ (Pi.ringHom (fun j => laurentMap (Pi.evalRingHom B j)) : LaurentPolynomial (∀ j, B j) →+* ∀ j, LaurentPolynomial (B j)).range := by
      intro j q
      induction q using LaurentPolynomial.induction_on' with
      | add p r hp hr =>
        rw [Pi.single_add]; exact Subring.add_mem _ hp hr
      | C_mul_T m a =>
        refine ⟨LaurentPolynomial.C (Pi.single j a) * LaurentPolynomial.T m, ?_⟩
        funext k
        simp only [hap, map_mul, laurentMap_C, laurentMap_T, Pi.evalRingHom_apply]
        by_cases hk : k = j
        · subst hk; simp
        · simp [Pi.single_eq_of_ne hk]
    rw [← Finset.univ_sum_single F]
    obtain ⟨p, hp⟩ := Subring.sum_mem _ (fun j (_ : j ∈ Finset.univ) => hsub j (F j))
    exact ⟨p, hp⟩

end GlobalTheory.EtC.GmStep
end

section

open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v

namespace GlobalTheory.EZ

theorem fc_succ_eq_delta (n : ℕ) (i : Fin (n + 2)) : fc (n + 1) n i = SimplexCategory.δ i := by
  ext j
  have hj : (j : ℕ) < n + 1 := j.isLt
  simp only [fc, clampHom, faceFun, SimplexCategory.δ, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk]
  change min (n + 1) (if (j : ℕ) < i then (j : ℕ) else j + 1) = ((Fin.succAbove i j : Fin (n+2)) : ℕ)
  rcases lt_or_ge (j : ℕ) i with h | h
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using h)]
    simp [h] <;> omega
  · rw [Fin.succAbove_of_le_castSucc _ _ (by simpa [Fin.le_def] using h)]
    simp [show ¬ (j : ℕ) < i by omega] <;> omega

theorem ev_map_dD_eq_diagCx_d {C : Type u} [Category.{v} C] [Preadditive C]
    (Y : SimplicialObject (SimplicialObject C)) (n : ℕ) :
    (ev Y).map (dD (n + 1) n) = (diagCx Y).d (n + 1) n := by
  refine Eq.trans ?_ (AlternatingFaceMapComplex.obj_d_eq (diag.obj Y) n).symm

  rw [dD, if_pos rfl, Functor.map_sum, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Functor.map_zsmul, ev_map_bop, fc_succ_eq_delta]
  rfl

end GlobalTheory.EZ
end
