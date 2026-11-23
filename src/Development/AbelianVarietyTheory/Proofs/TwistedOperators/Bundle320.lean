module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle195
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle255
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle048
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle350
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle303
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle140
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle308
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
import Std.Tactic.BVDecide.Normalize.Prop
import Std.Tactic.BVDecide.Normalize.BitVec
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameHeight

def EntryBd {n : ℕ} (f : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ c : ℝ, ∀ g i j, ‖f g i j‖ ≤ c * (1 + Formalism.REAL.hs g)

variable {n : ℕ} {f : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ}

theorem hs_nonneg (g : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ Formalism.REAL.hs g := by
  unfold Formalism.REAL.hs; positivity

theorem entryBd_id : EntryBd (fun g : Matrix (Fin n) (Fin n) ℂ => g) := by
  refine ⟨1, fun g i j => ?_⟩
  have h1 : ‖g i j‖ ^ 2 ≤ Formalism.REAL.hs g := by
    unfold Formalism.REAL.hs
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, ‖g i j‖ ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun j => ‖g i j‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)
  nlinarith [sq_nonneg (‖g i j‖ - 1), hs_nonneg g]

theorem EntryBd.conjTranspose (h : EntryBd f) : EntryBd fun g => (f g)ᴴ := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, fun g i j => by simpa [conjTranspose_apply] using hc g j i⟩

theorem EntryBd.const_mul (h : EntryBd f) (P : Matrix (Fin n) (Fin n) ℂ) : EntryBd fun g => P * f g := by
  obtain ⟨c, hc⟩ := h
  refine ⟨(∑ i, ∑ k, ‖P i k‖) * |c|, fun g i j => ?_⟩
  have h0 := hs_nonneg g
  show ‖(P * f g) i j‖ ≤ _
  rw [Matrix.mul_apply]
  calc _ ≤ ∑ k, ‖P i k‖ * (|c| * (1 + Formalism.REAL.hs g)) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left ((hc g k j).trans
          (mul_le_mul_of_nonneg_right (le_abs_self c) (by linarith))) (norm_nonneg _)
    _ = (∑ k, ‖P i k‖) * (|c| * (1 + Formalism.REAL.hs g)) := by rw [Finset.sum_mul]
    _ ≤ (∑ i, ∑ k, ‖P i k‖) * (|c| * (1 + Formalism.REAL.hs g)) :=
        mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := fun i => ∑ k, ‖P i k‖)
          (fun _ _ => by positivity) (Finset.mem_univ i)) (by positivity)
    _ = _ := by ring

theorem EntryBd.mul_const (h : EntryBd f) (P : Matrix (Fin n) (Fin n) ℂ) : EntryBd fun g => f g * P := by
  simpa using (h.conjTranspose.const_mul Pᴴ).conjTranspose

theorem frame_mem {D : D7} {V : HSp D} (A : GlobalTheory.ChainFr.Fr V) (τ : D.what₂.Tau)
    {k : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hk : k ∈ Formalism.MainNotions.S.UJset (A.ε τ)) :
    (A.fr τ)⁻¹ * k * A.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
  have h1 : A.fr τ * (A.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ))
  have hk' : kᴴ * Formalism.REAL.Jm (A.ε τ) * k = Formalism.REAL.Jm (A.ε τ) := hk
  have h3 : ((A.fr τ)⁻¹)ᴴ * (A.fr τ)ᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  show _ᴴ * _ * _ = _
  rw [← A.fr_gram τ]
  calc _ = (A.fr τ)ᴴ * (kᴴ * (((A.fr τ)⁻¹)ᴴ * (A.fr τ)ᴴ) * Formalism.REAL.Jm (A.ε τ) * (A.fr τ * (A.fr τ)⁻¹) * k) *
        A.fr τ := by simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [h1, h3, Matrix.mul_one, Matrix.mul_one, hk']

theorem height_elt_le : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (A : GlobalTheory.ChainFr.Fr V) (τ : D.what₂.Tau), ∃ (C : ℝ) (m : ℕ), ∀ g ∈ Formalism.MainNotions.S.UJset (A.ε τ), GlobalTheory.Grow.height V (A.elt θ τ g) ≤ C * (1 + Formalism.REAL.hs g) ^ m := by
  intro D θ hθ V A τ
  obtain ⟨d, hd⟩ := GlobalTheory.Grow.height_le_normInf_pow V hθ
  have b1 := (entryBd_id.const_mul (A.fr τ)⁻¹).mul_const (A.fr τ)
  obtain ⟨c2, h2⟩ := (b1.conjTranspose.const_mul (gramAt D V τ)⁻¹).mul_const (gramAt D V τ)
  obtain ⟨c1, h1⟩ := b1
  refine ⟨(∑ _ρ : D.what₂.Tau, ∑ _i : Fin V.rank, ∑ _j : Fin V.rank, (|c1| + |c2| + 2)) ^ d, d, fun g hg => ?_⟩
  have hu := frame_mem A τ hg
  have s1 := GlobalTheory.PointAtPlaceHom.atTau_spec hθ V τ hu
  have s2 := GlobalTheory.PointAtPlaceHom.isAtTau_inv V τ hu s1
  have h0 := hs_nonneg g
  refine (hd _ s1.1).trans ?_
  rw [← mul_pow]
  refine pow_le_pow_left₀ (by unfold normInf; positivity) ?_ d
  unfold normInf
  simp only [Finset.sum_mul]
  refine Finset.sum_le_sum fun ρ _ => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  have a1 := mul_nonneg (abs_nonneg c1) h0
  have a2 := mul_nonneg (abs_nonneg c2) h0
  by_cases e : ρ = τ
  · subst e
    rw [s1.2.1, s2.2.1]
    have e1 := (h1 g i j).trans (mul_le_mul_of_nonneg_right (le_abs_self c1) (by linarith))
    have e2 := (h2 g i j).trans (mul_le_mul_of_nonneg_right (le_abs_self c2) (by linarith))
    nlinarith
  · rw [s1.2.2 ρ e, s2.2.2 ρ e]
    have : ‖(1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) i j‖ ≤ 1 := by
      rw [Matrix.one_apply]; split_ifs <;> simp
    nlinarith [abs_nonneg c1, abs_nonneg c2]

end GlobalTheory.FrameHeight
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LowerMembers

theorem kset_apply_eq_zero {n : ℕ} {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.REAL.Kset ε)
    {i j : Fin n} (hij : ε i ≠ ε j) : g i j = 0 := by
  have h := congrFun (congrFun hg.2 i) j
  simp only [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  cases hi : ε i <;> cases hj : ε j <;> simp only [hi, hj, ne_eq, not_true_eq_false] at hij h ⊢ <;>
    simp at h <;> first | linear_combination (1 / 2 : ℂ) * h | linear_combination (-1 / 2 : ℂ) * h

theorem signBlockDeterminant_mul_maximalCompact {n : ℕ} {ε : Fin n → Bool} (e : Bool) {g h : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ Formalism.REAL.Kset ε) (hh : h ∈ Formalism.REAL.Kset ε) : signBlockDeterminant ε e (g * h) = signBlockDeterminant ε e g * signBlockDeterminant ε e h := by
  classical
  unfold signBlockDeterminant
  rw [← Matrix.det_mul]
  congr 1
  ext x y
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  have key : ∀ l, ε l ≠ e → g x l * h l y = 0 := fun l hl => by
    rw [kset_apply_eq_zero hg (by rw [x.2]; exact fun h' => hl h'.symm), zero_mul]
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.filter fun l => ε l = e))
    (fun l _ hl => key l (by simpa using hl))]
  exact Finset.sum_subtype _ (by simp) (fun l => g x l * h l y)

variable {D : D7} {a b : ℕ} (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool)

theorem subst_one_X (k : Matrix (Fin b) (Fin b) ℂ) (i : Fin b) (j : Fin a) :
    subst τ ε ε' 1 k (MvPolynomial.X (τ, i, j)) =
      ∑ l, (if ε' i = ε j then k l i else star (k l i)) • MvPolynomial.X (τ, l, j) := by
  classical
  simp only [subst, MvPolynomial.aeval_X, if_true]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_eq_single j]
  · split_ifs <;> simp
  · intro m _ hm
    split_ifs <;> simp [Matrix.one_apply_ne hm]
  · simp

theorem subst_one_mul {k₁ k₂ : Matrix (Fin b) (Fin b) ℂ} (h₁ : k₁ ∈ Formalism.REAL.Kset ε') (h₂ : k₂ ∈ Formalism.REAL.Kset ε')
    (P : PolF D b a) : subst τ ε ε' 1 (k₁ * k₂) P = subst τ ε ε' 1 k₁ (subst τ ε ε' 1 k₂ P) := by
  classical
  suffices h : subst τ ε ε' 1 (k₁ * k₂) = (subst τ ε ε' 1 k₁).comp (subst τ ε ε' 1 k₂) by
    rw [h]; rfl
  refine MvPolynomial.algHom_ext fun v => ?_
  obtain ⟨ρ, i, j⟩ := v
  by_cases hρ : ρ = τ
  · subst hρ

    rw [AlgHom.comp_apply, subst_one_X, subst_one_X, map_sum]
    simp only [map_smul, subst_one_X, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l' _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    rw [Matrix.mul_apply]
    split_ifs with hij
    · refine Finset.sum_congr rfl fun l _ => ?_
      by_cases hl : ε' l = ε' i
      · rw [if_pos (hl.trans hij)]; ring
      · rw [kset_apply_eq_zero h₂ hl]; simp
    · rw [star_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      by_cases hl : ε' l = ε' i
      · rw [if_neg (fun h => hij (hl.symm.trans h)), star_mul']; ring
      · rw [kset_apply_eq_zero h₂ hl]; simp
  · simp [subst, hρ]

theorem signCard_signed (l₁ l₂ : List ℚ) (c : ℚ) (h₁ : l₁.Nodup) (h₂ : l₂.Nodup) :
    GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.signCard (signed l₁ l₂ c) true = l₁.length ∧
      GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.signCard (signed l₁ l₂ c) false = l₂.length := by
  classical
  have n₁ : (l₁.map fun x => (x + c, true)).Nodup := h₁.map fun x y h => by simpa using h
  have n₂ : (l₂.map fun x => (x + c, false)).Nodup := h₂.map fun x y h => by simpa using h
  have m₁ : ∀ x ∈ (l₁.map fun x => (x + c, true)).toFinset, x.2 = true := by
    intro x hx
    simp only [List.mem_toFinset, List.mem_map] at hx
    obtain ⟨a, -, rfl⟩ := hx
    rfl
  have m₂ : ∀ x ∈ (l₂.map fun x => (x + c, false)).toFinset, x.2 = false := by
    intro x hx
    simp only [List.mem_toFinset, List.mem_map] at hx
    obtain ⟨a, -, rfl⟩ := hx
    rfl
  unfold GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.signCard signed
  rw [Finset.filter_union, Finset.filter_union]
  constructor
  · rw [Finset.filter_true_of_mem m₁, Finset.filter_false_of_mem (fun x hx => by simp [m₂ x hx]),
      Finset.union_empty, List.card_toFinset, List.dedup_eq_self.2 n₁, List.length_map]
  · rw [Finset.filter_false_of_mem (fun x hx => by simp [m₁ x hx]), Finset.filter_true_of_mem m₂,
      Finset.empty_union, List.card_toFinset, List.dedup_eq_self.2 n₂, List.length_map]

theorem opPow_zero {ι X : Type} (A : ι → (X → ℂ) → (X → ℂ)) (h : ∀ i, A i 0 = 0) (k : ι →₀ ℕ) :
    opPow A k 0 = 0 := by
  unfold opPow
  induction (Multiset.toList (Finsupp.toMultiset k)) with
  | nil => rfl
  | cons i l ih => rw [List.foldr_cons, ih, h]

theorem ptF_zero {V W : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A : Fr V) (B : Fr W)
    (P : PolF D W.rank V.rank) : ptF ψ θ A B 0 P = 0 := by
  have hA : ∀ l, aPlusAll (heisO ψ V W) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb l 0 = 0 := by
    intro l
    funext x
    simp [aPlusAll, aPlus, crea, Formalism.IndefR.Datum.dRho, heisO]
  have e : pureTensorL (aPlusAll (heisO ψ V W) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb) 0 = 0 := by
    refine (MvPolynomial.basisMonomials _ ℂ).ext fun k => ?_
    rw [pureTensorL, Module.Basis.constr_basis, opPow_zero _ hA]
    rfl
  change pureTensorL (aPlusAll (heisO ψ V W) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb) 0 P = 0
  rw [e]
  rfl

end GlobalTheory.LowerMembers

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameExists

theorem exists_signFrame {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (hd : IsUnit H.det) :
    ∃ (ε : Fin n → Bool) (P : Matrix (Fin n) (Fin n) ℂ), IsUnit P ∧ Pᴴ * Formalism.REAL.Jm ε * P = H := by
  let U : Matrix (Fin n) (Fin n) ℂ := hH.eigenvectorUnitary
  let l := hH.eigenvalues
  let S : Matrix (Fin n) (Fin n) ℂ := diagonal fun a => ((Real.sqrt |l a| : ℝ) : ℂ)
  have hs : H = U * diagonal (fun a => ((l a : ℝ) : ℂ)) * Uᴴ := by
    have := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have hS : Sᴴ * Formalism.REAL.Jm (fun a => decide (0 < l a)) * S = diagonal (fun a => ((l a : ℝ) : ℂ)) := by
    simp only [S, Formalism.REAL.Jm, diagonal_conjTranspose, diagonal_mul_diagonal]
    congr 1
    funext a
    have h1 : ((Real.sqrt |l a| : ℝ) : ℂ) * ((Real.sqrt |l a| : ℝ) : ℂ) = ((|l a| : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (abs_nonneg _)]
    simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
    rw [mul_right_comm, h1]
    by_cases h : 0 < l a
    · simp [h, abs_of_pos h]
    · simp [h, abs_of_nonpos (not_lt.1 h)]
  have key : (S * Uᴴ)ᴴ * Formalism.REAL.Jm (fun a => decide (0 < l a)) * (S * Uᴴ) = H := by
    rw [hs, ← hS, conjTranspose_mul, conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
  refine ⟨_, S * Uᴴ, ?_, key⟩
  rw [Matrix.isUnit_iff_isUnit_det]
  rw [← key, det_mul] at hd
  exact isUnit_of_mul_isUnit_right hd

theorem exists_perm_of_card {n : ℕ} {ε η : Fin n → Bool}
    (h : Nat.card {a // ε a = true} = Nat.card {a // η a = true}) :
    ∃ σ : Fin n ≃ Fin n, ∀ a, ε (σ a) = η a := by
  have hf : ∀ b : Bool, Nonempty ({a // η a = b} ≃ {a // ε a = b}) := by
    intro b
    rw [← Finite.card_eq]
    cases b
    · have e : ∀ θ : Fin n → Bool, Nat.card {a // θ a = false} = n - Nat.card {a // θ a = true} := by
        intro θ
        have := Fintype.card_subtype_compl (fun a => θ a = true)
        simp only [Nat.card_eq_fintype_card]
        simpa using this
      rw [e, e, h]
    · exact h.symm
  exact ⟨Equiv.ofFiberEquiv fun b => (hf b).some, fun a => Equiv.ofFiberEquiv_map _ a⟩

theorem exists_signCompat {n p q : ℕ} {ε : Fin n → Bool} {P : Matrix (Fin n) (Fin n) ℂ}
    (h : Formalism.UG.HasSignature (Pᴴ * Formalism.REAL.Jm ε * P) p q) :
    ∃ e : Fin p ⊕ Fin q ≃ Fin n, GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.SignCompat ε e := by
  obtain ⟨e, Q, hQ⟩ := h
  have hc : Formalism.UG.cT (starRingEnd ℂ) (Q : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) =
      (Q : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ := rfl
  rw [hc] at hQ
  have h1 : (P * (Q : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).submatrix e e)ᴴ * Formalism.REAL.Jm ε *
      (P * (Q : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).submatrix e e) =
      Formalism.REAL.Jm fun a => (e a).isLeft := by
    have h2 := congrArg (fun M => Matrix.submatrix M e e) hQ
    simp only [← submatrix_mul_equiv _ _ _ e, reindex_apply, submatrix_submatrix, Equiv.symm_comp_self,
      submatrix_id_id] at h2
    rw [conjTranspose_mul, conjTranspose_submatrix]
    simp only [Matrix.mul_assoc] at h2 ⊢
    rw [h2]
    ext a b
    obtain ⟨x, rfl⟩ := e.symm.surjective a
    obtain ⟨y, rfl⟩ := e.symm.surjective b
    simp only [submatrix_apply, Formalism.REAL.Jm, Formalism.UG.Jpq, diagonal_apply, Equiv.apply_symm_apply]
    rcases x with i | i <;> rcases y with j | j <;> simp [Matrix.one_apply]
    split_ifs <;> simp
  obtain ⟨σ, hσ⟩ := exists_perm_of_card (GlobalTheory.SignCount.card_true_eq _ h1)
  exact ⟨e.symm.trans σ, fun a => by simp [hσ]⟩

theorem frame_exists_signCompat : ∀ (D : D7) (V : HSp D), Nonempty (GlobalTheory.ChainFr.Fr V) ∧ ∀ (A : GlobalTheory.ChainFr.Fr V) (τ : D.what₂.Tau) (p q : ℕ), Formalism.UG.HasSignature (gramAt D V τ) p q → ∃ e : Ix p q ≃ Fin V.rank, GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.SignCompat (A.ε τ) e := by
  intro D V
  refine ⟨?_, fun A τ p q h => exists_signCompat (P := A.fr τ) (by rw [A.fr_gram]; exact h)⟩
  choose ε P h1 h2 using fun τ => exists_signFrame (H := gramAt D V τ)
    (GlobalTheory.SmoothForms.RealPts.gramAt_herm V τ) (GlobalTheory.SmoothForms.RealPts.gramAt_unit V τ)
  exact ⟨⟨ε, P, h1, h2⟩⟩

end GlobalTheory.FrameExists
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grow GlobalTheory.Size GlobalTheory.Mem.AutSpace Filter
open scoped ENNReal NNReal Topology

namespace GlobalTheory.Size.DiffQuot

theorem norm_taylor_le {f f₁ f₂ : ℝ → ℂ} (d1 : ∀ s, HasDerivAt f (f₁ s) s) (d2 : ∀ s, HasDerivAt f₁ (f₂ s) s)
    {B t : ℝ} (hB0 : 0 ≤ B) (hB : ∀ s ∈ Set.Icc (-|t|) |t|, ‖f₂ s‖ ≤ B) :
    ‖f t - f 0 - (t : ℂ) * f₁ 0‖ ≤ B * |t| * |t| := by
  have hI : Convex ℝ (Set.Icc (-|t|) |t|) := convex_Icc _ _
  have h0 : (0 : ℝ) ∈ Set.Icc (-|t|) |t| := ⟨neg_nonpos.mpr (abs_nonneg t), abs_nonneg t⟩
  have ht : t ∈ Set.Icc (-|t|) |t| := ⟨neg_abs_le t, le_abs_self t⟩

  have h1 : ∀ s ∈ Set.Icc (-|t|) |t|, ‖f₁ s - f₁ 0‖ ≤ B * |t| := by
    intro s hs
    have hmv := hI.norm_image_sub_le_of_norm_hasDerivWithin_le (f := f₁) (f' := f₂)
      (fun x _ => (d2 x).hasDerivWithinAt) hB h0 hs
    refine hmv.trans ?_
    rw [sub_zero, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (abs_le.2 ⟨hs.1, hs.2⟩) hB0

  have hg : ∀ s ∈ Set.Icc (-|t|) |t|, HasDerivWithinAt (fun u : ℝ => f u - (u : ℂ) * f₁ 0) (f₁ s - f₁ 0)
      (Set.Icc (-|t|) |t|) s := by
    intro s _
    have hc : HasDerivAt (fun u : ℝ => (u : ℂ) * f₁ 0) (f₁ 0) s := by
      simpa using ((hasDerivAt_id s).ofReal_comp).mul_const (f₁ 0)
    exact ((d1 s).sub hc).hasDerivWithinAt
  have hmv := hI.norm_image_sub_le_of_norm_hasDerivWithin_le hg h1 h0 ht
  have e : f t - f 0 - (t : ℂ) * f₁ 0 = (f t - (t : ℂ) * f₁ 0) - (f 0 - ((0 : ℝ) : ℂ) * f₁ 0) := by
    push_cast; ring
  rw [e]
  refine hmv.trans (le_of_eq ?_)
  rw [sub_zero, Real.norm_eq_abs]

theorem tendsto_growthSize_diffQuot : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (τ : D.what₂.Tau) (N : ℕ), ∀ X ∈ lieAt V τ, ∀ φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V, GlobalTheory.Size.growthSob θ V 2 N φ ≠ ⊤ → Filter.Tendsto (fun t : ℝ => GlobalTheory.Size.growthSize V N (((t : ℂ)⁻¹) • (rTr V (oneP θ V τ X t) φ - φ) - Rder θ V τ X φ)) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
  intro D θ hθ V τ N X hX φ hφ hS
  have hφ1 : Rder θ V τ X φ ∈ SmFun θ V := Rder_mem hφ hX

  have hw : growthSize V N (Rder θ V τ X (Rder θ V τ X φ)) ≠ ⊤ := by
    have hl : IsLieWord V [(τ, X), (τ, X)] := by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> exact hX
    have h2 := growthSize_rWord_ne_top_of_le hθ hφ hS hl (by simp)
    simpa only [rWord, wordAct_cons, wordAct_nil] using h2
  obtain ⟨C, hC⟩ := modGrowthExp_iff.2 hw
  have hC0 : 0 ≤ C := nonneg_of_growth hC

  obtain ⟨K, hK⟩ := exists_height_le_of_isCompact V
    (isCompact_Icc.image (GlobalTheory.Mem.Lift.continuous_oneP hθ hX) :
      IsCompact (oneP θ V τ X '' Set.Icc (-1 : ℝ) 1))
  have hK1 : 1 ≤ K := (one_le_height V _).trans (hK _ ⟨0, ⟨by norm_num, by norm_num⟩, rfl⟩)
  have hK0 : 0 ≤ K := by linarith

  have key : ∀ t : ℝ, |t| ≤ 1 → t ≠ 0 → ∀ g,
      ‖(((t : ℂ)⁻¹) • (rTr V (oneP θ V τ X t) φ - φ) - Rder θ V τ X φ) g‖ ≤
        C * K ^ N * |t| * height V g ^ N := by
    intro t ht1 ht0 g
    have d1 : ∀ s, HasDerivAt (fun s => φ (g * oneP θ V τ X s)) (Rder θ V τ X φ (g * oneP θ V τ X s)) s :=
      fun s => GlobalTheory.Mem.Lift.hasDerivAt_oneP hθ hX (fun g' => GlobalTheory.Mem.Lift.hasDerivAt_Rder hφ hX g') g s
    have d2 : ∀ s, HasDerivAt (fun s => Rder θ V τ X φ (g * oneP θ V τ X s))
        (Rder θ V τ X (Rder θ V τ X φ) (g * oneP θ V τ X s)) s :=
      fun s => GlobalTheory.Mem.Lift.hasDerivAt_oneP hθ hX (fun g' => GlobalTheory.Mem.Lift.hasDerivAt_Rder hφ1 hX g') g s
    have hg0 : 0 ≤ height V g := (height_pos V g).le
    have hB0 : 0 ≤ C * (height V g * K) ^ N := mul_nonneg hC0 (pow_nonneg (mul_nonneg hg0 hK0) N)
    have hB : ∀ s ∈ Set.Icc (-|t|) |t|,
        ‖Rder θ V τ X (Rder θ V τ X φ) (g * oneP θ V τ X s)‖ ≤ C * (height V g * K) ^ N := by
      intro s hs
      have hs1 : s ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith [hs.1], by linarith [hs.2]⟩
      refine (hC _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (height_pos V _).le ?_ N) hC0)
      exact (height_mul_le V _ _).trans (mul_le_mul_of_nonneg_left (hK _ ⟨s, hs1, rfl⟩) hg0)
    have hT := norm_taylor_le d1 d2 hB0 hB
    have e0 : oneP θ V τ X 0 = 1 := GlobalTheory.Mem.Lift.oneP_zero (V := V) (τ := τ) (X := X) hθ
    have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht0
    have hval : (((t : ℂ)⁻¹) • (rTr V (oneP θ V τ X t) φ - φ) - Rder θ V τ X φ) g =
        (t : ℂ)⁻¹ * (φ (g * oneP θ V τ X t) - φ (g * oneP θ V τ X 0) -
          (t : ℂ) * Rder θ V τ X φ (g * oneP θ V τ X 0)) := by
      simp only [e0, mul_one, rTr, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
    have hta : 0 < |t| := abs_pos.mpr ht0
    rw [hval, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
    calc |t|⁻¹ * ‖φ (g * oneP θ V τ X t) - φ (g * oneP θ V τ X 0) -
          (t : ℂ) * Rder θ V τ X φ (g * oneP θ V τ X 0)‖
        ≤ |t|⁻¹ * (C * (height V g * K) ^ N * |t| * |t|) :=
          mul_le_mul_of_nonneg_left hT (inv_nonneg.mpr hta.le)
      _ = C * K ^ N * |t| * height V g ^ N := by
          field_simp
          ring

  have hev : ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) {0}ᶜ, |t| ≤ 1 ∧ t ∈ ({0}ᶜ : Set ℝ) := by
    refine (eventually_nhdsWithin_of_eventually_nhds ?_).and eventually_mem_nhdsWithin
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with t ht
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
    exact ht.le
  have hle : ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) {0}ᶜ,
      GlobalTheory.Size.growthSize V N (((t : ℂ)⁻¹) • (rTr V (oneP θ V τ X t) φ - φ) - Rder θ V τ X φ) ≤
        ENNReal.ofReal (C * K ^ N * |t|) := by
    filter_upwards [hev] with t ht
    have ht0 : t ≠ 0 := by simpa using ht.2
    exact (growthSize_le_iff (mul_nonneg (mul_nonneg hC0 (pow_nonneg hK0 N)) (abs_nonneg t))).2
      (key t ht.1 ht0)
  have hlim : Filter.Tendsto (fun t : ℝ => ENNReal.ofReal (C * K ^ N * |t|)) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    have h0 : Filter.Tendsto (fun t : ℝ => C * K ^ N * |t|) (nhds 0) (nhds 0) := by
      simpa using (continuous_abs.tendsto (0 : ℝ)).const_mul (C * K ^ N)
    simpa using (ENNReal.tendsto_ofReal h0).mono_left nhdsWithin_le_nhds
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Filter.Eventually.of_forall fun _ => zero_le) hle

end GlobalTheory.Size.DiffQuot

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.openSubgroup_translate_height_bound : ∀ (D : D7) (V W : HSp D) (r : ℕ) (P : Matrix (Fin r) (Fin V.rank) D.host.E), ∃ e : ℕ, ∀ U : AddSubgroup (WO V W), IsOpen (U : Set (WO V W)) → ∃ M : ℕ, 0 < M ∧ ∀ (g : GA D V) (h : GA D W), ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ M * (GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h) ^ e ∧ ∀ x : Matrix (Fin W.rank) (Fin r) D.host.E, (∀ a b, IsIntegral ℤ (x a b)) → ∃ u ∈ U, u.map (infPart D) = 0 ∧ actO V W g h u = HMul.hMul (finLift ((N : D.host.E) • x)) (P.map (incA D)) := by
  first | exact @GlobalTheory.LevelHeight.levelheight | exact GlobalTheory.LevelHeight.levelheight | (intros; apply GlobalTheory.LevelHeight.levelheight <;> assumption)
end
