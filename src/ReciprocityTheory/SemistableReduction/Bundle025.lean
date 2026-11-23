module

public import ReciprocityTheory.SemistableReduction.Bundle017
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
public import ReciprocityTheory.SemistableReduction.SemiDegE
public import ReciprocityTheory.SemistableReduction.SemiDegDA
public import ReciprocityTheory.SemistableReduction.Bundle022

@[expose] public section

section

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiPt

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

def IsAt {K : Type} [Field K] {r : ℕ} (i : Fin r) (x : Fin r → K) : Prop :=
  ∀ a, a ≠ i → x a = 0

theorem gramC_single {K : Type} [Field K] [NumberField K] {r : ℕ} (δ : (K →+* ℂ) → Fin r → ℝ)
    (σ : K →+* ℂ) (i : Fin r) (x : Fin r → K) (hx : IsAt i x) :
    (gramC (diagMet δ σ) σ ![x]).det.re = ‖σ (x i)‖ ^ 2 * δ σ i := by
  rw [Matrix.det_unique]
  simp only [gramC, Matrix.of_apply, embVec, diagMet, Matrix.mulVec_diagonal, dotProduct,
    Pi.star_apply]
  rw [Finset.sum_eq_single i]
  · simp only [Fin.default_eq_zero, Matrix.cons_val_zero]
    rw [show star (σ (x i)) * (((δ σ i : ℝ) : ℂ) * σ (x i)) =
        ((δ σ i : ℝ) : ℂ) * (starRingEnd ℂ (σ (x i)) * σ (x i)) by
      rw [Complex.star_def]; ring]
    rw [Complex.conj_mul']
    simp only [Complex.re_ofReal_mul]
    norm_cast
    ring
  · intro a _ ha
    simp [Fin.default_eq_zero, hx a ha]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem latDeg_single {K : Type} [Field K] [NumberField K] {r : ℕ}
    (δ : (K →+* ℂ) → Fin r → ℝ) (C : Submodule (𝓞 K) (Fin r → K)) (i : Fin r) (x : Fin r → K)
    (hx : IsAt i x) :
    latDeg (diagMet δ) C ![x] = Real.log (spanIdx C ![x] : ℝ) -
      (1 / 2) * ∑ σ : K →+* ℂ, Real.log (‖σ (x i)‖ ^ 2 * δ σ i) := by
  unfold latDeg spanIdx
  congr 2
  exact Finset.sum_congr rfl fun σ _ => by rw [gramC_single δ σ i x hx]

theorem sum_log_single {K : Type} [Field K] [NumberField K] (z : K) (hz : z ≠ 0) (d : ℝ)
    (hd : 0 < d) :
    ∑ σ : K →+* ℂ, Real.log (‖σ z‖ ^ 2 * d) =
      2 * Real.log |((Algebra.norm ℚ z : ℚ) : ℝ)| + (Fintype.card (K →+* ℂ) : ℝ) * Real.log d := by
  have h1 : ∀ σ : K →+* ℂ, Real.log (‖σ z‖ ^ 2 * d) = 2 * Real.log ‖σ z‖ + Real.log d := by
    intro σ
    have : ‖σ z‖ ≠ 0 := by simpa using hz
    rw [Real.log_mul (pow_ne_zero 2 this) hd.ne', Real.log_pow]
    push_cast
    ring
  simp only [h1, Finset.sum_add_distrib, ← Finset.mul_sum, sum_log_norm_emb, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]

theorem kBasisIn_single {K : Type} [Field K] [NumberField K] {r : ℕ} (i : Fin r)
    (Gr : Submodule (𝓞 K) (Fin r → K)) (hat : ∀ x ∈ Gr, IsAt i x) (v : Fin r → K)
    (hv : v ∈ Gr) (hvi : v i ≠ 0) : IsKBasisIn Gr ![v] := by
  have hv0 : v ≠ 0 := fun h => hvi (by rw [h]; rfl)
  refine ⟨fun j => by fin_cases j; simpa using hv, ?_, ?_⟩
  · exact linearIndependent_unique_iff.2 (by simpa using hv0)
  · intro x hx
    rw [Set.range_unique, Submodule.mem_span_singleton]
    refine ⟨x i / v i, ?_⟩
    funext a
    simp only [Pi.smul_apply, smul_eq_mul, Fin.default_eq_zero, Matrix.cons_val_zero]
    by_cases ha : a = i
    · subst ha
      field_simp
    · rw [hat x hx a ha, hat v hv a ha, mul_zero]

theorem rankOne_le_zero (hB : LatDegBasisStatement) {K : Type} [Field K] [NumberField K]
    {r : ℕ} (δ : (K →+* ℂ) → Fin r → ℝ) (hδ : ∀ σ i, 0 < δ σ i) (i : Fin r)
    (Gr : Submodule (𝓞 K) (Fin r → K)) (hGr : Gr.FG) (hat : ∀ x ∈ Gr, IsAt i x)
    (x0 : Fin r → K) (hx0 : x0 ∈ Gr) (hx0i : x0 i ≠ 0)
    (hdeg : latDeg (diagMet δ) Gr ![x0] ≤ 0) (C : Submodule (𝓞 K) (Fin r → K)) (hC : C ≤ Gr)
    (k : ℕ) (c : Fin k → Fin r → K) (hc : IsKBasisIn C c) : latDeg (diagMet δ) C c ≤ 0 := by
  have hpd : ∀ σ, (diagMet δ σ).PosDef := fun σ =>
    Matrix.posDef_diagonal_iff.2 fun a => by exact_mod_cast hδ σ a
  have hci : ∀ j, c j i ≠ 0 := by
    intro j h0
    apply hc.2.1.ne_zero j
    funext a
    by_cases ha : a = i
    · subst ha; exact h0
    · exact hat _ (hC (hc.1 j)) a ha
  match k, c, hc, hci with
  | 0, c, hc, _ => exact (latDeg_zero_fam _ _ c hc).le
  | 1, c, hc, hci =>
    have hc1 : c = ![c 0] := by funext j; fin_cases j; rfl
    have hGc : IsKBasisIn Gr c := by
      rw [hc1]
      exact kBasisIn_single i Gr hat (c 0) (hC (hc.1 0)) (hci 0)
    calc latDeg (diagMet δ) C c ≤ latDeg (diagMet δ) Gr c :=
          latDeg_le_of_le _ C Gr c hC hGr hc hGc
      _ = latDeg (diagMet δ) Gr ![x0] :=
          hB K r 1 (diagMet δ) Gr c ![x0] hpd hGr hGc (kBasisIn_single i Gr hat x0 hx0 hx0i)
      _ ≤ 0 := hdeg
  | k + 2, c, hc, hci =>
    exfalso
    have hli := hc.2.1
    let t : Fin (k + 2) → K := fun j => if j = 0 then c 1 i else if j = 1 then -(c 0 i) else 0
    have ht : ∑ j, t j • c j = 0 := by
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
      have h0 : ∀ j : Fin k, t j.succ.succ = 0 := fun j => by
        simp only [t]
        rw [if_neg (Fin.succ_ne_zero _), if_neg]
        intro h
        exact Fin.succ_ne_zero j (Fin.succ_injective _ h)
      simp only [h0, zero_smul, Finset.sum_const_zero, add_zero]
      have t0 : t 0 = c 1 i := by simp [t]
      have t1 : t (Fin.succ 0) = -(c 0 i) := by
        simp only [t]
        rw [if_neg (Fin.succ_ne_zero _)]
        rfl
      rw [t0, t1]
      funext a
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      by_cases ha : a = i
      · subst ha
        simp only [Fin.succ_zero_eq_one]
        ring
      · rw [hat _ (hC (hc.1 0)) a ha, hat _ (hC (hc.1 _)) a ha]
        ring
    have := Fintype.linearIndependent_iff.1 hli t ht 1
    simp [t] at this
    exact hci 0 this

theorem relIndex_sup_proj {G : Type} [AddCommGroup G] (π : G →+ G) (A X C : AddSubgroup G)
    (hXC : X ≤ C) (hA : ∀ a ∈ A, π a = 0) (hC : ∀ x ∈ C, π x = x) :
    (A ⊔ X).relIndex (A ⊔ C) = X.relIndex C := by
  have heq : A ⊔ X = X.comap π ⊓ (A ⊔ C) := by
    apply le_antisymm
    · refine le_inf (sup_le ?_ ?_) (sup_le_sup_left hXC A)
      · intro a ha
        show π a ∈ X
        rw [hA a ha]
        exact X.zero_mem
      · intro x hx
        show π x ∈ X
        rw [hC x (hXC hx)]
        exact hx
    · rintro z ⟨hzX, hz⟩
      obtain ⟨a, ha, w, hw, rfl⟩ := AddSubgroup.mem_sup.1 hz
      have hπ : π (a + w) = w := by rw [map_add (f := _), hA a ha, hC w hw, zero_add]
      have hwX : w ∈ X := by
        have : π (a + w) ∈ X := hzX
        rwa [hπ] at this
      exact AddSubgroup.add_mem_sup ha hwX
  have hmap : (A ⊔ C).map π = C := by
    rw [AddSubgroup.map_sup]
    have h1 : A.map π = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨a, ha, rfl⟩
      rw [hA a ha]
      exact AddSubgroup.zero_mem _
    have h2 : C.map π = C := by
      apply le_antisymm
      · rintro _ ⟨x, hx, rfl⟩
        rw [hC x hx]
        exact hx
      · intro x hx
        exact ⟨x, hx, hC x hx⟩
    rw [h1, h2, bot_sup_eq]
  rw [heq, AddSubgroup.inf_relIndex_right, AddSubgroup.relIndex_comap, hmap]

end ReciprocityTheory.MultiplicativeHeights.SemiPt
end
end

section

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Module

theorem wa_witt_ker {K : Type} [Field K] (r m : ℕ) (g : Fin r → K)
    (hg : ∀ k : Fin r, m ≤ (k : ℕ) → (k : ℕ) + m < r → g k ≠ 0) (v : Fin r → K)
    (hv : ∀ p : Fin r, ∑ i, v i * wittMat r m g p i = 0) : v = 0 := by
  funext j
  have hj := j.isLt
  by_cases hmid : m ≤ (j : ℕ) ∧ (j : ℕ) + m < r
  · have h := hv j
    rw [Finset.sum_eq_single j] at h
    · simp only [wittMat, Matrix.of_apply] at h
      rw [if_neg (by omega), if_pos ⟨trivial, hmid.1, hmid.2⟩] at h
      exact (mul_eq_zero.1 h).resolve_right (hg j hmid.1 hmid.2)
    · intro i _ hij
      have hi := i.isLt
      simp only [wittMat, Matrix.of_apply]
      rw [if_neg, if_neg, mul_zero]
      · rintro ⟨h1, -⟩
        exact hij h1.symm
      · rintro ⟨h1, h2⟩
        rcases h2 with h2 | h2 <;> omega
    · intro h
      exact absurd (Finset.mem_univ j) h
  · set p : Fin r := ⟨r - 1 - j, by omega⟩ with hp
    have hpv : (p : ℕ) = r - 1 - j := rfl
    have h := hv p
    rw [Finset.sum_eq_single j] at h
    · simp only [wittMat, Matrix.of_apply] at h
      have hc : (p : ℕ) + j + 1 = r ∧ ((p : ℕ) < m ∨ (j : ℕ) < m) := by
        rw [hpv]
        omega
      rw [if_pos hc, mul_one] at h
      exact h
    · intro i _ hij
      have hi := i.isLt
      simp only [wittMat, Matrix.of_apply]
      rw [if_neg, if_neg, mul_zero]
      · rintro ⟨-, h2, h3⟩
        rw [hpv] at h2 h3
        omega
      · rintro ⟨h1, -⟩
        apply hij
        ext
        rw [hpv] at h1
        omega
    · intro h
      exact absurd (Finset.mem_univ j) h

theorem wittBasis_holds : WittBasisStatement := by
  intro K _ _ r S hdet
  have hnd : ∀ x ∈ (⊤ : Submodule K (Fin r → K)),
      (∀ y ∈ (⊤ : Submodule K (Fin r → K)), S.h x y = 0) → x = 0 := by
    intro x _ hx
    have hrow : Matrix.vecMul (fun a => S.c (x a)) S.G = 0 := by
      funext b'
      have h1 := hx (Pi.single b' 1) Submodule.mem_top
      simpa [HermForm.h, Pi.single_apply, Matrix.vecMul, dotProduct] using h1
    have h2 : (fun a => S.c (x a)) = 0 := Matrix.eq_zero_of_vecMul_eq_zero hdet hrow
    funext a
    have h3 := congrFun h2 a
    simp only [Pi.zero_apply, map_eq_zero] at h3
    exact h3
  obtain ⟨m, bb, g, -, hm, hW, hg⟩ := wa_main S r ⊤ (by rw [finrank_top, Module.finrank_fin_fun]) hnd
  have hgmid : ∀ k : Fin r, m ≤ (k : ℕ) → (k : ℕ) + m < r → g k ≠ 0 := by
    intro k hk1 hk2 hgk
    have ht := hg (Pi.single k 1) (fun i hi => by
      rw [Pi.single_apply, if_neg]
      rintro rfl
      omega) (by
      rw [Finset.sum_eq_single k]
      · simp [hgk]
      · intro i _ hik
        simp [Pi.single_eq_of_ne hik]
      · intro h
        exact absurd (Finset.mem_univ k) h)
    have := congrFun ht k
    simp at this
  have hlin : ∀ (x v : Fin r → K), S.h x (fun a => ∑ i, bb i a * v i) = ∑ i, v i * S.h x (bb i) := by
    intro x v
    simp only [HermForm.h, Finset.mul_sum]
    calc ∑ a, ∑ b', ∑ i, S.c (x a) * S.G a b' * (bb i b' * v i)
        = ∑ a, ∑ i, ∑ b', S.c (x a) * S.G a b' * (bb i b' * v i) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ i, ∑ a, ∑ b', S.c (x a) * S.G a b' * (bb i b' * v i) := Finset.sum_comm
      _ = ∑ i, ∑ a, ∑ b', v i * (S.c (x a) * S.G a b' * bb i b') :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ =>
            Finset.sum_congr rfl fun b' _ => by ring
  refine ⟨Matrix.of fun a i => bb i a, m, g, ?_, hm, ?_, hg⟩
  · intro hd
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
    apply hv0
    have hPv : Matrix.mulVec (Matrix.of fun a i => bb i a) v = fun a => ∑ i, bb i a * v i := by
      funext a
      simp [Matrix.mulVec, dotProduct]
    refine wa_witt_ker r m g hgmid v fun p => ?_
    have h1 : S.h (bb p) (fun a => ∑ i, bb i a * v i) = 0 := by
      rw [← hPv, hv]
      simp [HermForm.h]
    rw [hlin] at h1
    rw [← h1]
    exact Finset.sum_congr rfl fun i _ => by rw [hW p i]
  · ext i j
    rw [← hW i j]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, HermForm.h,
      Finset.sum_mul]
    exact Finset.sum_comm

end ReciprocityTheory.MultiplicativeHeights
end
end

section

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField
open scoped ComplexOrder

private theorem posDef_diagonal_ofReal_of_pos {r : ℕ} (d : Fin r → ℝ) (hd : ∀ l, 0 < d l) :
    (diagonal fun l => (d l : ℂ)).PosDef := by
  first
  | exact Matrix.posDef_diagonal_iff.mpr fun l => Complex.zero_lt_real.mpr (hd l)
  | exact Matrix.posDef_diagonal_iff.mpr fun l => by exact_mod_cast hd l

theorem sdd_gram_step {K : Type} [Field K] [NumberField K] {r e k₀ k₁ : ℕ} (σ : K →+* ℂ)
    (d : Fin r → ℝ) (hd : ∀ l, 0 < d l) (b₀ : Fin k₀ → Fin r → K) (c b₁ : Fin k₁ → Fin r → K)
    (hb₀cut : ∀ i, b₀ i ∈ cutSub K r e) (hb₀li : LinearIndependent K b₀)
    (hcb : ∀ j, projGe K r e (c j) = b₁ j) (hb₁li : LinearIndependent K b₁) :
    Real.log (gramC (diagonal fun l => (d l : ℂ)) σ b₁).det.re ≤
      Real.log (quotGramC (diagonal fun l => (d l : ℂ)) σ b₀ c).det.re := by

  have hcutz : ∀ i (l : Fin r), e ≤ (l : ℕ) → b₀ i l = 0 := by
    intro i l hl
    have h := hb₀cut i
    simp only [cutSub, UpperTheory.Reformulated.B.FirstCoordinatesSubmodule.cutSub] at h
    exact h l hl
  set D : Matrix (Fin r) (Fin r) ℂ := diagonal fun l => (d l : ℂ) with hDdef
  have hDpd : D.PosDef := posDef_diagonal_ofReal_of_pos d hd
  have hG0 : ((embM σ b₀)ᴴ * D * embM σ b₀).PosDef :=
    hDpd.conjTranspose_mul_mul_same (sdd_embM_inj σ b₀ hb₀li)
  have hG1 : ((embM σ b₁)ᴴ * D * embM σ b₁).PosDef :=
    hDpd.conjTranspose_mul_mul_same (sdd_embM_inj σ b₁ hb₁li)
  have hu : IsUnit ((embM σ b₀)ᴴ * D * embM σ b₀).det := by
    first
    | exact (Matrix.isUnit_iff_isUnit_det _).mp hG0.isUnit
    | exact hG0.det_pos.ne'.isUnit
  set E : Matrix (Fin r) (Fin k₁) ℂ := embM σ c - embM σ b₀ *
    (((embM σ b₀)ᴴ * D * embM σ b₀)⁻¹ * ((embM σ b₀)ᴴ * D * embM σ c)) with hE

  have hq : quotGramC D σ b₀ c = Eᴴ * D * E := by
    simp only [quotGramC, sdd_gramC_eq, sdd_gramX_eq]
    exact sdd_schur _ _ _ hDpd.1 hG0.1 hu

  have hB1 : ∀ (l : Fin r) (j : Fin k₁),
      embM σ b₁ l j = if e ≤ (l : ℕ) then E l j else 0 := by
    intro l j
    have hb1 : b₁ j l = if e ≤ (l : ℕ) then c j l else 0 := by
      rw [← hcb j]; rfl
    by_cases hl : e ≤ (l : ℕ)
    · have hz : ∀ i, b₀ i l = 0 := fun i => hcutz i l hl
      rw [if_pos hl, hE]
      simp [embM, Matrix.mul_apply, hb1, hl, hz]
    · rw [if_neg hl]
      simp [embM, hb1, hl]
  have hquad : ∀ v : Fin k₁ → ℂ, (star v ⬝ᵥ (((embM σ b₁)ᴴ * D * embM σ b₁) *ᵥ v)).re ≤
      (star v ⬝ᵥ ((Eᴴ * D * E) *ᵥ v)).re :=
    sdd_cut_quad d (fun l => (hd l).le) e E (embM σ b₁) hB1
  obtain ⟨hpos, hle⟩ := sdd_det_mono _ _ hG1 (Matrix.isHermitian_conjTranspose_mul_mul E hDpd.1) hquad
  rw [sdd_gramC_eq, hq]
  exact Real.log_le_log hpos hle

theorem gradedExt_holds (hB : LatDegBasisStatement) (hD : DegAddStatement) :
    GradedExtStatement := by
  unfold GradedExtStatement
  unfold LatDegBasisStatement at hB
  unfold DegAddStatement at hD
  intro K _ _ r e k k₀ k₁ δ B b b₀ b₁ hδ hFG hb hb₀ hb₁

  have hlift : ∀ j, ∃ y ∈ B, projGe K r e y = b₁ j := fun j => Submodule.mem_map.mp (hb₁.1 j)
  choose c hcB hcb using hlift
  have hb₀B : ∀ i, b₀ i ∈ B := fun i => (hb₀.1 i).1
  have hb₀cut : ∀ i, b₀ i ∈ cutSub K r e := fun i => (hb₀.1 i).2
  have hli : LinearIndependent K (Fin.append b₀ c) :=
    sdd_append_li b₀ c b₁ hb₀cut hb₀.2.1 hcb hb₁.2.1
  have hsp : ∀ x ∈ B, x ∈ Submodule.span K (Set.range (Fin.append b₀ c)) :=
    sdd_append_span B b₀ c b₁ hb₀ hcB hcb hb₁
  have hmem : ∀ i, Fin.append b₀ c i ∈ B := by
    intro i
    refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [hb₀B, hcB]
  have hk : k = k₀ + k₁ := sdd_card_eq B b (Fin.append b₀ c) hb hmem hli hsp
  subst hk
  have hpd : ∀ σ, (diagMet δ σ).PosDef := fun σ => by
    simp only [diagMet]
    exact posDef_diagonal_ofReal_of_pos (δ σ) (hδ σ)
  have h1 : latDeg (diagMet δ) B b = latDeg (diagMet δ) B (Fin.append b₀ c) :=
    hB K r (k₀ + k₁) (diagMet δ) B b (Fin.append b₀ c) hpd hFG hb ⟨hmem, hli, hsp⟩
  have h2 := hD K r k₀ k₁ (diagMet δ) B b₀ c hpd hFG hb₀B hcB hli hsp
  have hsat : satSub B b₀ = B ⊓ cutSub K r e := sdd_satSub_eq B b₀ hb₀
  rw [hsat] at h2
  have h3 : quotDeg (diagMet δ) B b₀ c ≤ latDeg (diagMet δ) (B.map (projGe K r e)) b₁ := by
    unfold quotDeg latDeg
    rw [sdd_index B b₀ c b₁ hsat hcB hcb]
    have hs : ∑ σ : K →+* ℂ, Real.log (gramC (diagMet δ σ) σ b₁).det.re ≤
        ∑ σ : K →+* ℂ, Real.log (quotGramC (diagMet δ σ) σ b₀ c).det.re :=
      Finset.sum_le_sum fun σ _ =>
        sdd_gram_step σ (δ σ) (hδ σ) b₀ c b₁ hb₀cut hb₀.2.1 hcb hb₁.2.1
    linarith
  linarith [h1, h2, h3]

theorem absDet_holds : AbsDetStatement := by
  intro n A C hA hC h
  exact sdd_absDet A C hA hC h

end ReciprocityTheory.MultiplicativeHeights
end
end
