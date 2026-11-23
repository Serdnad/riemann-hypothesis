module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle009
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle097
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle106
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp

theorem partialProd_inv_le (t : ℕ → ℝ) (ht : ∀ a, 0 < t a) (j : ℕ) (De : ℝ)
    (h : ∀ b ≤ j, (∏ a ∈ Finset.range b, t a)⁻¹ ≤ De ∨ (0 < b ∧ b < j ∧ t (b - 1) = t b)) :
    ∀ b ≤ j, (∏ a ∈ Finset.range b, t a)⁻¹ ≤ De := by
  have hP : ∀ b, 0 < ∏ a ∈ Finset.range b, t a := fun b => Finset.prod_pos fun a _ => ht a
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image (Finset.range (j + 1))
    (fun b => (∏ a ∈ Finset.range b, t a)⁻¹) ⟨0, by simp⟩
  have hle : ∀ b ≤ j, (∏ a ∈ Finset.range b, t a)⁻¹ ≤ (∏ a ∈ Finset.range m, t a)⁻¹ :=
    fun b hb => hmax b (Finset.mem_range.2 (Nat.lt_succ_of_le hb))

  have key : ∀ b, b ≤ j → (∏ a ∈ Finset.range b, t a)⁻¹ = (∏ a ∈ Finset.range m, t a)⁻¹ →
      (∏ a ∈ Finset.range m, t a)⁻¹ ≤ De := by
    intro b
    induction b with
    | zero =>
      intro hb h0
      rcases h 0 hb with h1 | ⟨h1, -, -⟩
      · rw [← h0]; exact h1
      · exact absurd h1 (lt_irrefl 0)
    | succ n ih =>
      intro hn heq
      rcases h (n + 1) hn with h1 | ⟨-, hlt, hteq⟩
      · rw [← heq]; exact h1
      · rw [Nat.add_sub_cancel] at hteq
        apply ih (Nat.le_of_succ_le hn)
        have hx := hP n
        have hc := ht n
        have h0 := hle n (Nat.le_of_succ_le hn)
        have h2 := hle (n + 1 + 1) (by omega)
        rw [← heq] at h0 h2 ⊢
        rw [Finset.prod_range_succ] at h0 ⊢
        rw [Finset.prod_range_succ, Finset.prod_range_succ, ← hteq] at h2
        rw [inv_le_inv₀ hx (mul_pos hx hc)] at h0
        rw [inv_le_inv₀ (mul_pos (mul_pos hx hc) hc) (mul_pos hx hc)] at h2
        have c1 : t n ≤ 1 := by nlinarith
        have c2 : 1 ≤ t n := by nlinarith [mul_pos hx hc]
        rw [le_antisymm c1 c2, mul_one]
  intro b hb
  exact (hle b hb).trans (key m (Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)) rfl)

theorem norm_leading_minor_monomial {j l : ℕ} (hl : l ≤ j) (Z : Matrix (Fin j) (Fin j) ℂ) (w : Equiv.Perm (Fin j))
    (hw : ∀ a b, Z a b ≠ 0 ↔ b = w a) (hc : ∀ a : Fin j, a.val < l → (w a).val < l) :
    ‖(Z.submatrix (Fin.castLE hl) (Fin.castLE hl)).det‖ = ∏ a : Fin l, ‖Z (Fin.castLE hl a) (w (Fin.castLE hl a))‖ := by
  set M := Z.submatrix (Fin.castLE hl) (Fin.castLE hl) with hM

  let f : Fin l → Fin l := fun a => ⟨(w (Fin.castLE hl a)).val, hc _ a.2⟩
  have hcf : ∀ a, Fin.castLE hl (f a) = w (Fin.castLE hl a) := fun a => Fin.ext rfl
  have hinj : Function.Injective f := by
    intro a b hab
    have h1 := congrArg (Fin.castLE hl) hab
    rw [hcf, hcf] at h1
    exact Fin.castLE_injective hl (w.injective h1)
  let w' : Equiv.Perm (Fin l) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj)
  have hw' : ∀ a, w' a = f a := fun a => rfl
  have hMne : ∀ a b, M a b ≠ 0 ↔ b = w' a := by
    intro a b
    rw [hM, Matrix.submatrix_apply, hw, hw', ← hcf]
    exact (Fin.castLE_injective hl).eq_iff

  rw [Matrix.det_apply', Finset.sum_eq_single w'.symm]
  · have hs : ‖((Equiv.Perm.sign w'.symm : ℤ) : ℂ)‖ = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign w'.symm) with hsg | hsg <;> simp [hsg]
    rw [norm_mul, hs, one_mul, norm_prod]
    refine Fintype.prod_equiv w'.symm _ _ fun i => ?_
    have hi : Fin.castLE hl i = w (Fin.castLE hl (w'.symm i)) := by
      rw [← hcf, ← hw', Equiv.apply_symm_apply]
    show ‖Z (Fin.castLE hl (w'.symm i)) (Fin.castLE hl i)‖ = _
    rw [hi]
  · intro σ _ hσ
    obtain ⟨i, hi⟩ : ∃ i, w' (σ i) ≠ i := by
      by_contra hne
      push_neg at hne
      exact hσ (Equiv.ext fun i => w'.eq_symm_apply.2 (hne i))
    apply mul_eq_zero_of_right
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    by_contra hz
    exact hi ((hMne (σ i) i).1 hz).symm
  · intro hn
    exact absurd (Finset.mem_univ _) hn

theorem blockAnti_perm_partialProd : ∀ (j : ℕ) (β : Fin j → ℕ) (Z : Matrix (Fin j) (Fin j) ℂ) (De : ℝ), BlockAnti β Z → 1 ≤ De → (∀ (l : ℕ) (hl : l ≤ j), (Z.submatrix (Fin.castLE hl) (Fin.castLE hl)).det ≠ 0 → ‖(Z.submatrix (Fin.castLE hl) (Fin.castLE hl)).det‖⁻¹ ≤ De) → ∃ (w : Equiv.Perm (Fin j)), (∀ a b, Z a b ≠ 0 ↔ b = w a) ∧ (∀ a, β (w a) = β a) ∧ ∀ b : ℕ, (∏ a ∈ Finset.univ.filter (fun a : Fin j => a.val < b), ‖Z a (w a)‖)⁻¹ ≤ De := by
  intro j β Z De hZ _ hminor
  unfold BlockAnti at hZ
  obtain ⟨hmono, hdet, hblk, hanti⟩ := hZ

  have hrow : ∀ a, ∃ b, Z a b ≠ 0 := by
    intro a
    by_contra hne
    push_neg at hne
    exact hdet (Matrix.det_eq_zero_of_row_eq_zero a hne)
  choose f hf using hrow
  have huniq : ∀ a b, Z a b ≠ 0 → b = f a := fun a b hab =>
    (hanti a b a (f a) hab (hf a) rfl).2.1 rfl

  have hinj : Function.Injective f := by
    intro a a' h
    have h1 := hf a
    have h2 := hf a'
    rw [← h] at h2
    have hb : β a = β a' := (hblk a (f a) h1).trans (hblk a' (f a) h2).symm
    rcases lt_trichotomy a a' with hlt | heq | hgt
    · exact absurd ((hanti a (f a) a' (f a) h1 h2 hb).2.2 hlt) (lt_irrefl _)
    · exact heq
    · exact absurd ((hanti a' (f a) a (f a) h2 h1 hb.symm).2.2 hgt) (lt_irrefl _)
  let w : Equiv.Perm (Fin j) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj)
  have hw : ∀ a b, Z a b ≠ 0 ↔ b = w a := fun a b =>
    ⟨huniq a b, fun h => by rw [h]; exact hf a⟩
  have hβ : ∀ a, β (w a) = β a := fun a => (hblk a (w a) (hf a)).symm
  refine ⟨w, hw, hβ, ?_⟩

  let t : ℕ → ℝ := fun n => if h : n < j then ‖Z ⟨n, h⟩ (w ⟨n, h⟩)‖ else 1
  have ht : ∀ n, 0 < t n := by
    intro n
    simp only [t]
    split_ifs with h
    · exact norm_pos_iff.2 (hf _)
    · exact one_pos
  have htfin : ∀ a : Fin j, t a.val = ‖Z a (w a)‖ := by
    intro a
    simp [t]
  have hconv : ∀ b, ∏ a ∈ Finset.univ.filter (fun a : Fin j => a.val < b), ‖Z a (w a)‖ =
      ∏ n ∈ Finset.range (min b j), t n := by
    intro b
    rw [Finset.prod_filter]
    simp_rw [← htfin]
    refine (Fin.prod_univ_eq_prod_range (fun n => if n < b then t n else 1) j).trans ?_
    rw [← Finset.prod_filter]
    congr 1
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, lt_min_iff]
    exact and_comm

  have hh : ∀ l ≤ j, (∏ n ∈ Finset.range l, t n)⁻¹ ≤ De ∨ (0 < l ∧ l < j ∧ t (l - 1) = t l) := by
    intro l hl
    by_cases hbd : ∀ a : Fin j, a.val < l → (w a).val < l
    · left
      have hnorm := norm_leading_minor_monomial hl Z w hw hbd
      have hprod : ∏ a : Fin l, ‖Z (Fin.castLE hl a) (w (Fin.castLE hl a))‖ = ∏ n ∈ Finset.range l, t n := by
        rw [← Fin.prod_univ_eq_prod_range]
        exact Finset.prod_congr rfl fun a _ => (htfin (Fin.castLE hl a)).symm
      have hpos : 0 < ∏ n ∈ Finset.range l, t n := Finset.prod_pos fun n _ => ht n
      have hne : (Z.submatrix (Fin.castLE hl) (Fin.castLE hl)).det ≠ 0 := by
        intro h0
        rw [h0, norm_zero, hprod] at hnorm
        linarith
      have hb := hminor l hl hne
      rw [hnorm, hprod] at hb
      exact hb
    · right
      push_neg at hbd
      obtain ⟨a, hal, hwa⟩ := hbd
      have hlj : l < j := lt_of_le_of_lt hwa (w a).2
      have hl0 : 0 < l := lt_of_le_of_lt (Nat.zero_le _) hal
      refine ⟨hl0, hlj, ?_⟩
      let p : Fin j := ⟨l - 1, by omega⟩
      let q : Fin j := ⟨l, hlj⟩
      have hβeq : β p = β q := by
        have h1 : β a ≤ β p := hmono (Fin.le_def.2 (show a.val ≤ l - 1 by omega))
        have h2 : β p ≤ β q := hmono (Fin.le_def.2 (show l - 1 ≤ l by omega))
        have h3 : β q ≤ β (w a) := hmono (Fin.le_def.2 hwa)
        rw [hβ a] at h3
        omega
      have e1 : t (l - 1) = ‖Z p (w p)‖ := htfin p
      have e2 : t l = ‖Z q (w q)‖ := htfin q
      rw [e1, e2]
      exact (hanti p (w p) q (w q) (hf p) (hf q) hβeq).1
  intro b
  rw [hconv]
  exact partialProd_inv_le t ht j De hh (min b j) (min_le_right _ _)

end GlobalTheory.Amp
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas

private theorem finrank_span_map_ringHom_eq_finrank {K : Type*} [Field K] {n : ℕ} (φ : K →+* ℂ)
    (U : Submodule K (Fin n → K)) :
    Module.finrank ℂ (Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' (U : Set (Fin n → K)))) =
      Module.finrank K U := by

  have hle : ∀ V : Submodule K (Fin n → K),
      Module.finrank ℂ (Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' (V : Set (Fin n → K)))) ≤
        Module.finrank K V := by
    intro V
    let b := Module.finBasis K V
    have hsub : (fun y : Fin n → K => fun l => φ (y l)) '' (V : Set (Fin n → K)) ⊆
        Submodule.span ℂ (Set.range fun k => fun l => φ ((b k : Fin n → K) l)) := by
      rintro _ ⟨u, hu, rfl⟩
      simp only [SetLike.mem_coe]
      have hu' : u = ∑ k, b.repr ⟨u, hu⟩ k • (b k : Fin n → K) := by
        have h := congrArg Subtype.val (b.sum_repr ⟨u, hu⟩)
        simp only [Submodule.coe_sum, SetLike.val_smul] at h
        exact h.symm
      have hφ : (fun l => φ (u l)) = ∑ k, φ (b.repr ⟨u, hu⟩ k) • fun l => φ ((b k : Fin n → K) l) := by
        conv_lhs => rw [hu']
        ext l

        simp [Finset.sum_apply, map_sum, map_mul]
      rw [hφ]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    calc Module.finrank ℂ (Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' (V : Set (Fin n → K))))
        ≤ Module.finrank ℂ (Submodule.span ℂ (Set.range fun k => fun l => φ ((b k : Fin n → K) l))) :=
          Submodule.finrank_mono (Submodule.span_le.2 hsub)
      _ ≤ Fintype.card (Fin (Module.finrank K V)) := finrank_range_le_card _
      _ = Module.finrank K V := Fintype.card_fin _
  have hsup : ∀ V V' : Submodule K (Fin n → K), V ⊔ V' = ⊤ →
      Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' (V : Set (Fin n → K))) ⊔
        Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' (V' : Set (Fin n → K))) = ⊤ := by
    intro V V' h
    rw [eq_top_iff]
    intro z _
    have hz : z = ∑ i, z i • (Pi.single i (1 : ℂ) : Fin n → ℂ) := by
      ext l
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hz]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    have hsingle : (fun l => φ ((Pi.single i (1 : K) : Fin n → K) l)) = (Pi.single i (1 : ℂ) : Fin n → ℂ) := by
      ext l
      by_cases hl : l = i
      · subst hl; simp
      · simp [Pi.single_eq_of_ne hl]
    rw [← hsingle]
    have hmem : (Pi.single i (1 : K) : Fin n → K) ∈ V ⊔ V' := by rw [h]; exact Submodule.mem_top
    obtain ⟨u, hu, u', hu', hsum⟩ := Submodule.mem_sup.1 hmem
    rw [← hsum]
    have hadd : (fun l => φ ((u + u') l)) = (fun l => φ (u l)) + fun l => φ (u' l) := by
      ext l; simp
    rw [hadd]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨u, hu, rfl⟩) (Submodule.subset_span ⟨u', hu', rfl⟩)
  obtain ⟨U', hU'⟩ := Submodule.exists_isCompl U
  have h1 := hle U
  have h2 := hle U'
  have h3 : Module.finrank K U + Module.finrank K U' = n := by
    have := Submodule.finrank_add_eq_of_isCompl hU'
    simpa using this
  have h4 := Submodule.finrank_add_le_finrank_add_finrank
    (Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' (U : Set (Fin n → K))))
    (Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' (U' : Set (Fin n → K))))
  rw [hsup U U' hU'.sup_eq_top, finrank_top, Module.finrank_fin_fun] at h4
  omega

private theorem span_map_ringHom_span_eq_span_map {K : Type*} [Field K] {n : ℕ} (φ : K →+* ℂ) (X : Set (Fin n → K)) :
    Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' (Submodule.span K X : Set (Fin n → K))) =
      Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' X) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    induction hy using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero =>
      have h0 : (fun l => φ ((0 : Fin n → K) l)) = 0 := by ext; simp
      change (fun l => φ ((0 : Fin n → K) l)) ∈ Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' X)
      rw [h0]; exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      have h : (fun l => φ ((x + y) l)) = (fun l => φ (x l)) + fun l => φ (y l) := by ext; simp
      change (fun l => φ (x l)) ∈ Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' X) at hx
      change (fun l => φ (y l)) ∈ Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' X) at hy
      change (fun l => φ ((x + y) l)) ∈ Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' X)
      rw [h]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx =>
      have h : (fun l => φ ((c • x) l)) = φ c • fun l => φ (x l) := by ext; simp
      change (fun l => φ (x l)) ∈ Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' X) at hx
      change (fun l => φ ((c • x) l)) ∈ Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' X)
      rw [h]; exact Submodule.smul_mem _ _ hx
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

theorem isIsoFlag_flagAt_of_isSatFlag :
    ∀ (I : AutInst) (Λ : Submodule (𝓞 I.E) (Fin I.n → I.E)) (a : ℕ) (j : Fin a → ℕ)
      (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)),
      IsSatFlag I Λ j S → ∀ v, IsIsoFlag (I.ε v) j (flagAt I S v) := by
  intro I Λ a j S hS v
  obtain ⟨h0, hmono, hrk, -, hiso⟩ := hS
  have hdet : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  have hPQ : I.P v * (I.P v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hinj : Function.Injective (Matrix.mulVecLin (I.P v)⁻¹) := by
    intro x y hxy
    have h := congrArg (fun z => I.P v *ᵥ z) hxy
    simpa [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hPQ] using h

  have hspan : ∀ i, flagAt I S v i =
      (Submodule.span ℂ ((fun y : Fin I.n → I.E => fun l => I.φ v (y l)) '' (S i : Set _))).map
        (Matrix.mulVecLin (I.P v)⁻¹) := by
    intro i
    rw [Submodule.map_span, Set.image_image]
    rfl
  have hfr : ∀ i, Module.finrank ℂ (flagAt I S v i) = Formalism.HN.rkK (S i) := by
    intro i
    rw [hspan i, ← (Submodule.equivMapOfInjective _ hinj _).finrank_eq]
    show _ = Module.finrank I.E (Submodule.span I.E (S i : Set (Fin I.n → I.E)))
    rw [← span_map_ringHom_span_eq_span_map, finrank_span_map_ringHom_eq_finrank]

  have hstar : ∀ x : I.E, I.φ v (starRingEnd I.E x) = starRingEnd ℂ (I.φ v x) := fun x =>
    I.cm.cmUnram.2.1 (I.φ v) x
  have hJ : ((I.P v)⁻¹)ᴴ * (Formalism.REAL.Jm (I.ε v) * (I.P v)⁻¹) = I.J.map (I.φ v) := by
    rw [← I.P_spec v]
    calc ((I.P v)⁻¹)ᴴ * ((I.P v)ᴴ * I.J.map (I.φ v) * I.P v * (I.P v)⁻¹)
        = (I.P v * (I.P v)⁻¹)ᴴ * I.J.map (I.φ v) * (I.P v * (I.P v)⁻¹) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = I.J.map (I.φ v) := by rw [hPQ]; simp
  have hgen : ∀ x y : Fin I.n → ℂ, star ((I.P v)⁻¹ *ᵥ x) ⬝ᵥ (Formalism.REAL.Jm (I.ε v) *ᵥ ((I.P v)⁻¹ *ᵥ y)) =
      star x ⬝ᵥ (I.J.map (I.φ v) *ᵥ y) := by
    intro x y
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
    simp only [Matrix.mulVec_mulVec, hJ]
  have hpair : ∀ s ∈ S (Fin.last a), ∀ t ∈ S (Fin.last a),
      star (fun l => I.φ v (s l)) ⬝ᵥ (I.J.map (I.φ v) *ᵥ fun l => I.φ v (t l)) = 0 := by
    intro s hs t ht
    have h := hiso s hs t ht
    have h' := congrArg (I.φ v) h
    rw [map_zero] at h'
    rw [← h']

    simp [Formalism.UG.hform, dotProduct, Matrix.mulVec, map_sum, map_mul, hstar, Finset.mul_sum, mul_assoc]
  refine ⟨?_, ?_, ?_, ?_⟩
  · show Submodule.span ℂ _ = ⊥
    rw [Submodule.span_eq_bot]
    rintro _ ⟨y, hy, rfl⟩
    rw [h0] at hy
    have hy0 : y = 0 := by simpa using hy
    subst hy0
    ext l
    simp [Matrix.mulVec, dotProduct]
  · intro i k hik
    exact Submodule.span_mono (Set.image_mono (SetLike.coe_subset_coe.2 (hmono hik)))
  · intro i
    rw [hfr, hfr]
    exact hrk i
  · intro x hx y hy
    rw [hspan] at hx hy
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hx
    obtain ⟨w', hw', rfl⟩ := Submodule.mem_map.1 hy
    rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, hgen]
    clear hx hy

    have hgen1 : ∀ g ∈ (fun y : Fin I.n → I.E => fun l => I.φ v (y l)) '' (S (Fin.last a) : Set (Fin I.n → I.E)),
        ∀ z ∈ Submodule.span ℂ
          ((fun y : Fin I.n → I.E => fun l => I.φ v (y l)) '' (S (Fin.last a) : Set (Fin I.n → I.E))),
          star g ⬝ᵥ (I.J.map (I.φ v) *ᵥ z) = 0 := by
      rintro _ ⟨s, hs, rfl⟩ z hz
      induction hz using Submodule.span_induction with
      | mem u hu =>
        obtain ⟨t, ht, rfl⟩ := hu
        exact hpair s hs t ht
      | zero => simp
      | add u u' _ _ hu hu' => rw [Matrix.mulVec_add, dotProduct_add, hu, hu', add_zero]
      | smul c u _ hu => rw [Matrix.mulVec_smul, dotProduct_smul, hu, smul_zero]
    induction hw using Submodule.span_induction with
    | mem u hu => exact hgen1 u hu w' hw'
    | zero => simp
    | add u u' _ _ hu hu' => rw [star_add, add_dotProduct, hu, hu', add_zero]
    | smul c u _ hu => rw [star_smul, smul_dotProduct, hu, smul_zero]

end GlobalTheory.FlagMeas
end

section

open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

namespace GlobalTheory.InflBasic

open GlobalTheory.RowLev.Inhab GlobalTheory.Mem.RowsBundle

theorem finite_of_red {I : AutInst} {g : ℕ} {Q : Type} [Group Q] (ρ : Red I g Q) (hg : 1 ≤ g) : Finite Q := by
  obtain ⟨-, hK⟩ := GlobalTheory.CongTop.congruence_normal_finite_index I
  obtain ⟨-, -, -, s, hs⟩ := hK g hg
  refine Finite.of_surjective (fun t : s => ρ.toFun t) ?_
  intro q
  obtain ⟨x, hx, rfl⟩ := ρ.surj q
  obtain ⟨t, ht, htx⟩ := hs x hx
  have hk : t⁻¹ * x ∈ I.Kset := htx.1
  have htK : t ∈ I.Kset := by
    have hmem := (Ksub I).mul_mem ((mem_Ksub I x).2 hx) ((Ksub I).inv_mem ((mem_Ksub I _).2 hk))
    rw [_root_.mul_inv_rev, inv_inv, mul_inv_cancel_left] at hmem
    exact (mem_Ksub I t).1 hmem
  refine ⟨⟨t, ht⟩, ?_⟩
  show ρ.toFun t = ρ.toFun x
  calc ρ.toFun t = ρ.toFun t * ρ.toFun (t⁻¹ * x) := by rw [(ρ.ker _ hk).2 htx, mul_one]
    _ = ρ.toFun (t * (t⁻¹ * x)) := (ρ.map_mul t htK _ hk).symm
    _ = ρ.toFun x := by rw [mul_inv_cancel_left]

theorem inflation_basic : ∀ (I : AutInst) (g : ℕ) (Q : Type) [Group Q] (ρ : Red I g Q) (μf : Measure I.Gf) [μf.IsHaarMeasure], 1 ≤ g → Finite Q ∧ 0 < (μf (I.Kg g)).toReal ∧ ρ.toFun 1 = 1 ∧ (∀ x ∈ I.Kset, ρ.toFun x⁻¹ = (ρ.toFun x)⁻¹) ∧ (∀ q : Q, μf {x | x ∈ I.Kset ∧ ρ.toFun x = q} = μf (I.Kg g) ∧ IsOpen {x | x ∈ I.Kset ∧ ρ.toFun x = q}) ∧ (∀ a, Integrable (ρ.lift μf a) μf ∧ IsLocallyConstant (ρ.lift μf a) ∧ ∀ x, ∀ k ∈ I.Kg g, ∀ k' ∈ I.Kg g, ρ.lift μf a (k * x * k') = ρ.lift μf a x) ∧ (∀ a b, ρ.lift μf (a + b) = ρ.lift μf a + ρ.lift μf b) ∧ (∀ (c : ℂ) a, ρ.lift μf (c • a) = c • ρ.lift μf a) ∧ ∀ a, ρ.lift μf a 1 = a.coeff 1 / ((μf (I.Kg g)).toReal : ℂ) := by
  intro I g Q _ ρ μf _ hg
  have hQ : Finite Q := finite_of_red ρ hg
  obtain ⟨-, hK⟩ := GlobalTheory.CongTop.congruence_normal_finite_index I
  obtain ⟨-, hopen, -, -⟩ := hK g hg
  obtain ⟨hcpt, -, -, -⟩ := GlobalTheory.adelicStab_isCompact_isOpen I
  have h1K : (1 : I.Gf) ∈ I.Kset := (mem_Ksub I 1).1 (Ksub I).one_mem
  have h1 : (1 : I.Gf) ∈ I.Kg g := (ρ.ker 1 h1K).1 ρ.map_one
  have hsub : I.Kg g ⊆ I.Kset := fun x hx => hx.1
  have hpos : 0 < (μf (I.Kg g)).toReal :=
    ENNReal.toReal_pos (hopen.measure_pos μf ⟨1, h1⟩).ne'
      ((measure_mono hsub).trans_lt hcpt.measure_lt_top).ne
  refine ⟨hQ, hpos, ρ.map_one, fun x hx => ρ.map_inv hx, ?_, ?_, ?_, ?_, ?_⟩
  · intro q
    obtain ⟨t, ht⟩ := fibre_eq ρ q
    rw [ht]
    exact ⟨measure_preimage_mul μf t _, hopen.preimage (continuous_const_mul t)⟩
  · intro a
    refine ⟨integrable_lift ρ μf hg a, ?_, fun x k hk k' hk' => lift_biinv ρ μf a x k hk k' hk'⟩
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hnhds : (fun y => x⁻¹ * y) ⁻¹' I.Kg g ∈ nhds x :=
      (hopen.preimage (continuous_const_mul x⁻¹)).mem_nhds (by
        show x⁻¹ * x ∈ I.Kg g
        rw [inv_mul_cancel]
        exact h1)
    filter_upwards [hnhds] with y hy
    have h := lift_biinv ρ μf a x 1 h1 (x⁻¹ * y) hy
    rwa [one_mul, mul_inv_cancel_left] at h
  · intro a b
    funext x
    by_cases hx : x ∈ I.Kset
    · rw [Pi.add_apply, ρ.lift_of_mem μf _ hx, ρ.lift_of_mem μf _ hx, ρ.lift_of_mem μf _ hx,
        MonoidAlgebra.coeff_add, Finsupp.add_apply, add_div]
    · rw [Pi.add_apply, ρ.lift_of_notMem μf _ hx, ρ.lift_of_notMem μf _ hx, ρ.lift_of_notMem μf _ hx,
        add_zero]
  · intro c a
    funext x
    by_cases hx : x ∈ I.Kset
    · rw [Pi.smul_apply, ρ.lift_of_mem μf _ hx, ρ.lift_of_mem μf _ hx, MonoidAlgebra.coeff_smul,
        Finsupp.smul_apply, smul_eq_mul, smul_eq_mul, mul_div_assoc]
    · rw [Pi.smul_apply, ρ.lift_of_notMem μf _ hx, ρ.lift_of_notMem μf _ hx, smul_zero]
  · intro a
    rw [ρ.lift_of_mem μf a h1K, ρ.map_one]

end GlobalTheory.InflBasic
end
