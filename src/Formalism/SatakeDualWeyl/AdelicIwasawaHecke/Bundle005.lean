module

public import Formalism.SatakeDualWeyl.Statement
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.NumberTheory.NumberField.FiniteAdeleRing
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

namespace Formalism.UG.P

open Matrix

theorem sigex_cT_conj_eq {m p : Type} (M : Matrix m p ℂ) : Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ := by
  first
    | rfl
    | (ext i j; simp [Formalism.UG.cT, Matrix.conjTranspose_apply])

noncomputable def scal {n : Type} (ev : n → ℝ) : n → ℂ := fun i => (((Real.sqrt |ev i|)⁻¹ : ℝ) : ℂ)

theorem star_scal {n : Type} (ev : n → ℝ) : star (scal ev) = scal ev := by
  funext i
  simp only [Pi.star_apply, scal]
  exact Complex.conj_ofReal _

theorem scal_sq {n : Type} (ev : n → ℝ) (i : n) :
    scal ev i * (ev i : ℂ) * scal ev i = ((ev i / |ev i| : ℝ) : ℂ) := by
  have key : (Real.sqrt |ev i|)⁻¹ * ev i * (Real.sqrt |ev i|)⁻¹ = ev i / |ev i| := by
    set t := Real.sqrt |ev i| with ht
    have hs : t * t = |ev i| := Real.mul_self_sqrt (abs_nonneg _)
    rw [div_eq_mul_inv, ← hs]
    ring
  simp only [scal]
  rw [← key]
  push_cast
  ring

theorem herm_diag {n : Type} [Fintype n] [DecidableEq n] {J : Matrix n n ℂ}
    (hJ : J.IsHermitian) :
    ((hJ.eigenvectorUnitary : Matrix n n ℂ) * diagonal (scal hJ.eigenvalues))ᴴ * J *
        ((hJ.eigenvectorUnitary : Matrix n n ℂ) * diagonal (scal hJ.eigenvalues)) =
      diagonal (fun i => ((hJ.eigenvalues i / |hJ.eigenvalues i| : ℝ) : ℂ)) := by
  rw [Matrix.conjTranspose_mul, Matrix.diagonal_conjTranspose, star_scal]
  have hU : ((hJ.eigenvectorUnitary : Matrix n n ℂ))ᴴ * (hJ.eigenvectorUnitary : Matrix n n ℂ) = 1 := by
    have h := Unitary.star_mul_self_of_mem hJ.eigenvectorUnitary.2
    rwa [Matrix.star_eq_conjTranspose] at h
  have key : ((hJ.eigenvectorUnitary : Matrix n n ℂ))ᴴ * J * (hJ.eigenvectorUnitary : Matrix n n ℂ) =
      diagonal (RCLike.ofReal ∘ hJ.eigenvalues) := by
    have h1 := congrArg (fun M => ((hJ.eigenvectorUnitary : Matrix n n ℂ))ᴴ * M *
      (hJ.eigenvectorUnitary : Matrix n n ℂ)) hJ.spectral_theorem
    first
      | simp only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] at h1
      | simp only [Unitary.conjStarAlgAut, Matrix.star_eq_conjTranspose] at h1
    rw [h1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hU, Matrix.one_mul, Matrix.mul_assoc, hU, Matrix.mul_one]
  calc _ = diagonal (scal hJ.eigenvalues) * (((hJ.eigenvectorUnitary : Matrix n n ℂ))ᴴ * J *
          (hJ.eigenvectorUnitary : Matrix n n ℂ)) * diagonal (scal hJ.eigenvalues) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [key, diagonal_mul_diagonal, diagonal_mul_diagonal]
        congr 1
        funext i
        exact scal_sq _ i

theorem eig_ne_zero {n : Type} [Fintype n] [DecidableEq n] {J : Matrix n n ℂ}
    (hJ : J.IsHermitian) (hdet : IsUnit J.det) (i : n) : hJ.eigenvalues i ≠ 0 := by
  intro h0
  apply hdet.ne_zero
  rw [hJ.det_eq_prod_eigenvalues]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [h0])

theorem sign_pos {x : ℝ} (h : 0 < x) : x / |x| = 1 := by
  rw [abs_of_pos h, div_self h.ne']

theorem sign_neg {x : ℝ} (h : x < 0) : x / |x| = -1 := by
  rw [abs_of_neg h, div_neg, div_self h.ne]

theorem signature_exists : Formalism.UG.SigExists := by
  unfold Formalism.UG.SigExists
  intro n _ _ J hJ hdet
  unfold Formalism.UG.IsHerm at hJ
  unfold Formalism.UG.HasSignature
  unfold Formalism.UG.Jpq
  have hH : J.IsHermitian := (sigex_cT_conj_eq J).symm.trans hJ
  have hU : ((hH.eigenvectorUnitary : Matrix n n ℂ))ᴴ * (hH.eigenvectorUnitary : Matrix n n ℂ) = 1 := by
    have h := Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
    rwa [Matrix.star_eq_conjTranspose] at h
  obtain ⟨Q, hQdef⟩ : ∃ Q : Matrix n n ℂ,
      Q = (hH.eigenvectorUnitary : Matrix n n ℂ) * diagonal (scal hH.eigenvalues) := ⟨_, rfl⟩
  have hQ : Qᴴ * J * Q = diagonal (fun i => ((hH.eigenvalues i / |hH.eigenvalues i| : ℝ) : ℂ)) := by
    rw [hQdef]
    exact herm_diag hH
  obtain ⟨e, he⟩ : ∃ e : n ≃ Fin (Fintype.card {i // 0 < hH.eigenvalues i}) ⊕
      Fin (Fintype.card {i // ¬ 0 < hH.eigenvalues i}),
      e = (Equiv.sumCompl (fun i => 0 < hH.eigenvalues i)).symm.trans
        (Equiv.sumCongr (Fintype.equivFin _) (Fintype.equivFin _)) := ⟨_, rfl⟩
  have hinl : ∀ a, e.symm (Sum.inl a) =
      ((Fintype.equivFin {i // 0 < hH.eigenvalues i}).symm a : n) := by
    intro a
    rw [he]
    first | rfl | simp
  have hinr : ∀ a, e.symm (Sum.inr a) =
      ((Fintype.equivFin {i // ¬ 0 < hH.eigenvalues i}).symm a : n) := by
    intro a
    rw [he]
    first | rfl | simp
  have hdetQ : IsUnit (reindex e e Q).det := by
    rw [Matrix.det_reindex_self, hQdef, Matrix.det_mul, Matrix.det_diagonal]
    refine IsUnit.mul (Matrix.isUnit_det_of_left_inverse hU) ?_
    rw [isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
    intro i _
    have h1 : hH.eigenvalues i ≠ 0 := eig_ne_zero hH hdet i
    simp only [scal, ne_eq, Complex.ofReal_eq_zero, inv_eq_zero]
    exact (Real.sqrt_pos.mpr (abs_pos.mpr h1)).ne'
  refine ⟨_, _, e, Matrix.nonsingInvUnit _ hdetQ, ?_⟩
  change Formalism.UG.cT (starRingEnd ℂ) (reindex e e Q) * reindex e e J * reindex e e Q = _
  rw [sigex_cT_conj_eq]
  simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
  rw [hQ, Matrix.submatrix_diagonal_equiv]
  ext (a | a) (b | b)
  · simp only [Matrix.fromBlocks_apply₁₁, Matrix.diagonal_apply, Function.comp_apply, hinl,
      Sum.inl.injEq, Matrix.one_apply]
    split_ifs
    · rw [sign_pos ((Fintype.equivFin {i // 0 < hH.eigenvalues i}).symm a).2, Complex.ofReal_one]
    · rfl
  · simp [Matrix.diagonal_apply]
  · simp [Matrix.diagonal_apply]
  · simp only [Matrix.fromBlocks_apply₂₂, Matrix.diagonal_apply, Function.comp_apply, hinr,
      Sum.inr.injEq, Matrix.neg_apply, Matrix.one_apply]
    split_ifs
    · have hx := ((Fintype.equivFin {i // ¬ 0 < hH.eigenvalues i}).symm a).2
      have hneg : hH.eigenvalues ((Fintype.equivFin {i // ¬ 0 < hH.eigenvalues i}).symm a : n) < 0 :=
        lt_of_le_of_ne (not_lt.mp hx) (eig_ne_zero hH hdet _)
      rw [sign_neg hneg]
      push_cast
      ring
    · simp

end Formalism.UG.P
end

section

noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open scoped NumberField.AdeleRing

namespace Formalism.UG.P
open Formalism.UG

section Adele
variable {F : Type} [Field F] [NumberField F]

theorem afsplit_add_apply (a b : 𝔸ᶠ[F]) (w : HeightOneSpectrum (𝓞 F)) : (a + b) w = a w + b w := rfl
theorem afsplit_mul_apply (a b : 𝔸ᶠ[F]) (w : HeightOneSpectrum (𝓞 F)) : (a * b) w = a w * b w := rfl
theorem afsplit_sub_apply (a b : 𝔸ᶠ[F]) (w : HeightOneSpectrum (𝓞 F)) : (a - b) w = a w - b w := rfl
theorem afsplit_one_apply (w : HeightOneSpectrum (𝓞 F)) : (1 : 𝔸ᶠ[F]) w = 1 := rfl
theorem afsplit_zero_apply (w : HeightOneSpectrum (𝓞 F)) : (0 : 𝔸ᶠ[F]) w = 0 := rfl
theorem afsplit_smul_apply (c : F) (a : 𝔸ᶠ[F]) (w : HeightOneSpectrum (𝓞 F)) :
    (c • a) w = c • a w := by
  rw [Algebra.smul_def, afsplit_mul_apply, Algebra.smul_def]; rfl

def afsplitF (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) : 𝔸ᶠ[F] := by
  classical
  exact ⟨Pi.single v x, by
    filter_upwards [show ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F))) ∈ Filter.cofinite by simp] with w hw
    rw [Set.mem_compl_singleton_iff] at hw
    rw [Pi.single_eq_of_ne hw]
    exact zero_mem _⟩

theorem afsplitF_self (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) : afsplitF v x v = x := by
  classical
  show Pi.single v x v = x
  convert Pi.single_eq_same v x

theorem afsplitF_ne (v w : HeightOneSpectrum (𝓞 F)) (h : w ≠ v) (x : v.adicCompletion F) :
    afsplitF v x w = 0 := by
  classical
  show Pi.single v x w = 0
  convert Pi.single_eq_of_ne h x

def afsplitI (v : HeightOneSpectrum (𝓞 F)) : v.adicCompletion F →ₗ[F] 𝔸ᶠ[F] where
  toFun := afsplitF v
  map_add' x y := by
    ext w
    by_cases h : w = v
    · subst h; simp only [afsplit_add_apply, afsplitF_self]
    · simp only [afsplit_add_apply, afsplitF_ne v w h, add_zero]
  map_smul' c x := by
    ext w
    by_cases h : w = v
    · subst h; simp only [afsplit_smul_apply, afsplitF_self, RingHom.id_apply]
    · simp only [afsplit_smul_apply, afsplitF_ne v w h, smul_zero, RingHom.id_apply]

theorem afsplitI_self (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) : afsplitI v x v = x :=
  afsplitF_self v x

theorem afsplitI_ne (v w : HeightOneSpectrum (𝓞 F)) (h : w ≠ v) (x : v.adicCompletion F) :
    afsplitI v x w = 0 := afsplitF_ne v w h x

theorem afsplitI_mul (v : HeightOneSpectrum (𝓞 F)) (x y : v.adicCompletion F) :
    afsplitI v (x * y) = afsplitI v x * afsplitI v y := by
  ext w
  by_cases h : w = v
  · subst h; simp only [afsplit_mul_apply, afsplitI_self]
  · simp only [afsplit_mul_apply, afsplitI_ne v w h, mul_zero]

theorem afsplitI_eval (v : HeightOneSpectrum (𝓞 F)) (a : 𝔸ᶠ[F]) :
    afsplitI v (a v) = afsplitI v 1 * a := by
  ext w
  by_cases h : w = v
  · subst h; simp only [afsplit_mul_apply, afsplitI_self, one_mul]
  · simp only [afsplit_mul_apply, afsplitI_ne v w h, zero_mul]

theorem afsplitI_mem_intAd (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F)
    (hx : x ∈ v.adicCompletionIntegers F) : afsplitI v x ∈ intAd F := by
  intro w
  by_cases h : w = v
  · subst h; rw [afsplitI_self]; exact hx
  · rw [afsplitI_ne v w h]; exact zero_mem _

end Adele
end Formalism.UG.P
end
end
