module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle744
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HasComplementOfBasis
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsGLSubmatrix
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1261
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable

@[expose] public section

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.RealLift.HermitianFrameExistence

open Matrix
open scoped ComplexOrder

theorem map_star_trip {m k l o : Type} [Fintype k] [Fintype l] (X : Matrix k m ℂ) (Y : Matrix k l ℂ)
    (Z : Matrix l o ℂ) : (Xᵀ * Y * Z.map star).map star = Xᴴ * Y.map star * Z := by
  have h : ∀ {a b : Type} (W : Matrix a b ℂ), W.map star = W.map (starRingEnd ℂ) := fun _ => rfl
  rw [h (Xᵀ * Y * Z.map star), Matrix.map_mul, Matrix.map_mul]
  simp [Matrix.conjTranspose, Matrix.map_map, Function.comp_def]

theorem quad {n ι : Type} [Fintype n] [Fintype ι] (G : Matrix n n ℂ) (B : Matrix n ι ℂ) (w : ι → ℂ) :
    star (B *ᵥ w) ⬝ᵥ G *ᵥ (B *ᵥ w) = star w ⬝ᵥ (Bᴴ * G * B) *ᵥ w := by
  conv_rhs => rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]

theorem val_inl {p q : ℕ} (u : Fin p → ℂ) :
    star (Sum.elim u (0 : Fin q → ℂ)) ⬝ᵥ (fromBlocks 1 0 0 (-1) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) *ᵥ
      Sum.elim u 0 = star u ⬝ᵥ u := by
  simp [fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type]

theorem val_inr {p q : ℕ} (v : Fin q → ℂ) :
    star (Sum.elim (0 : Fin p → ℂ) v) ⬝ᵥ (fromBlocks 1 0 0 (-1) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) *ᵥ
      Sum.elim 0 v = -(star v ⬝ᵥ v) := by
  simp [fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type, neg_mulVec, Finset.sum_neg_distrib]

theorem inertia {n p q r s : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin p ⊕ Fin q) ℂ)
    (A : Matrix (Fin n) (Fin r ⊕ Fin s) ℂ) (hB : Bᴴ * G * B = fromBlocks 1 0 0 (-1))
    (hA : Aᴴ * G * A = fromBlocks 1 0 0 (-1)) : p + s ≤ n := by
  have key : ∀ (u : Fin p → ℂ) (v : Fin s → ℂ), B *ᵥ Sum.elim u 0 = A *ᵥ Sum.elim 0 v → u = 0 ∧ v = 0 := by
    intro u v h
    have h1 := quad G B (Sum.elim u 0)
    have h2 := quad G A (Sum.elim 0 v)
    rw [hB, val_inl] at h1
    rw [hA, val_inr, ← h, h1] at h2
    have hu := dotProduct_star_self_nonneg u
    have hv := dotProduct_star_self_nonneg v
    have h3 : star u ⬝ᵥ u = 0 := le_antisymm (by rw [h2]; exact neg_nonpos.2 hv) hu
    have h4 : star v ⬝ᵥ v = 0 := by rw [h3] at h2; exact neg_eq_zero.1 h2.symm
    exact ⟨dotProduct_star_self_eq_zero.1 h3, dotProduct_star_self_eq_zero.1 h4⟩
  let f : (Fin p → ℂ) × (Fin s → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
    B.mulVecLin ∘ₗ ((LinearEquiv.sumArrowLequivProdArrow (Fin p) (Fin q) ℂ ℂ).symm.toLinearMap ∘ₗ
        (LinearMap.inl ℂ _ _ ∘ₗ LinearMap.fst ℂ _ _)) -
      A.mulVecLin ∘ₗ ((LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin s) ℂ ℂ).symm.toLinearMap ∘ₗ
        (LinearMap.inr ℂ _ _ ∘ₗ LinearMap.snd ℂ _ _))
  have e1 : ∀ u : Fin p → ℂ, (LinearEquiv.sumArrowLequivProdArrow (Fin p) (Fin q) ℂ ℂ).symm (u, 0) = Sum.elim u 0 := by
    intro u; ext (i | i) <;> simp
  have e2 : ∀ v : Fin s → ℂ, (LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin s) ℂ ℂ).symm ((0 : Fin r → ℂ), v) = Sum.elim (0 : Fin r → ℂ) v := by
    intro v; ext (i | i) <;> simp
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨u, v⟩ huv
    have h0 : B *ᵥ Sum.elim u 0 - A *ᵥ Sum.elim 0 v = 0 := by
      simpa [f, e1, e2, Matrix.mulVecLin_apply] using huv
    obtain ⟨hu, hv⟩ := key u v (sub_eq_zero.1 h0)
    simp [hu, hv]
  have := LinearMap.finrank_le_finrank_of_injective hf
  simpa [Module.finrank_prod] using this

theorem card_le_of_mul_eq_one {m k : Type} [Fintype m] [Fintype k] [DecidableEq m] (X : Matrix m k ℂ)
    (Y : Matrix k m ℂ) (h : X * Y = 1) : Fintype.card m ≤ Fintype.card k := by
  have hi : Function.Injective Y.mulVecLin := by
    intro u v huv
    have := congrArg (fun w => X *ᵥ w) huv
    simpa [Matrix.mulVecLin_apply, mulVec_mulVec, h] using this
  simpa using LinearMap.finrank_le_finrank_of_injective hi

theorem star_form {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (v y : Fin n → ℂ) :
    star (v ⬝ᵥ M *ᵥ star y) = star v ⬝ᵥ M.map star *ᵥ y := by
  simp [dotProduct, mulVec, star_sum, Finset.mul_sum, mul_comm, mul_left_comm]

end GlobalTheory.RealLift.HermitianFrameExistence

namespace GlobalTheory.RealLift

open Matrix GlobalTheory.RealLift.HermitianFrameExistence
open scoped ComplexOrder

theorem frameEx_holds : FrameEx := by
  intro n r s M θ hSig hC
  obtain ⟨hrs, A0, hA0⟩ := hSig
  obtain ⟨hθθ, hiso, hpos⟩ := hC
  set G : Matrix (Fin n) (Fin n) ℂ := M.map star with hGdef
  have hJ : ∀ p q : ℕ, (fromBlocks 1 0 0 (-1) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).map star =
      fromBlocks 1 0 0 (-1) := by
    intro p q; ext (i | i) (j | j) <;> simp [Matrix.one_apply] <;> split_ifs <;> simp
  have hA : A0ᴴ * G * A0 = fromBlocks 1 0 0 (-1) := by
    rw [← map_star_trip, hA0, hJ]

  obtain ⟨L, hLdef⟩ : ∃ L : Matrix (Fin r ⊕ Fin s) (Fin n) ℂ,
      L = (fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ) * (A0ᴴ * G) := ⟨_, rfl⟩
  have hL : L * A0 = 1 := by
    calc L * A0 = (fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ) * (A0ᴴ * G * A0) := by
          rw [hLdef]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hA, fromBlocks_multiply]; simp
  have e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  have hR : A0 * L = 1 := (mul_eq_one_comm_of_equiv e).1 hL
  have hLc : Lᴴ * A0ᴴ = 1 := by rw [← conjTranspose_mul, hR, conjTranspose_one]
  have hJh : ((fromBlocks 1 0 0 (-1)) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ)ᴴ = fromBlocks 1 0 0 (-1) := by
    simp [fromBlocks_conjTranspose]
  have hA' : A0ᴴ * Gᴴ * A0 = A0ᴴ * G * A0 := by
    calc A0ᴴ * Gᴴ * A0 = (A0ᴴ * G * A0)ᴴ := by simp [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hA, hJh]
  have Gherm : Gᴴ = G := by
    calc Gᴴ = (Lᴴ * A0ᴴ) * Gᴴ * (A0 * L) := by rw [hLc, hR]; simp
      _ = Lᴴ * (A0ᴴ * Gᴴ * A0) * L := by simp only [Matrix.mul_assoc]
      _ = Lᴴ * (A0ᴴ * G * A0) * L := by rw [hA']
      _ = (Lᴴ * A0ᴴ) * G * (A0 * L) := by simp only [Matrix.mul_assoc]
      _ = G := by rw [hLc, hR]; simp

  have hiso' : θᴴ * G * θ = G := by rw [← map_star_trip, hiso]
  have hcomm : θᴴ * G = G * θ := by
    calc θᴴ * G = θᴴ * G * θ * θ := by rw [Matrix.mul_assoc (θᴴ * G), hθθ, Matrix.mul_one]
      _ = G * θ := by rw [hiso']
  have hherm : (G * θ).IsHermitian := by
    unfold IsHermitian; rw [conjTranspose_mul, Gherm, hcomm]
  have hPD : (G * θ).PosDef := by
    refine Matrix.posDef_iff_dotProduct_mulVec.2 ⟨hherm, fun x hx => ?_⟩
    have hval : star x ⬝ᵥ (G * θ) *ᵥ x = star ((θ *ᵥ x) ⬝ᵥ M *ᵥ star x) := by
      rw [← hcomm, star_form, ← hGdef, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]
    refine Complex.pos_iff.2 ⟨?_, (hherm.im_star_dotProduct_mulVec_self x).symm⟩
    rw [hval, Complex.star_def, Complex.conj_re]; exact hpos x hx
  obtain ⟨p, q, B, B', h1, h2, h3, h4⟩ :=
    GlobalTheory.exists_basis_adapted_to_cartan_involution n G θ hθθ hiso' hPD
  have i1 := inertia G B A0 h3 hA
  have i2 := inertia G A0 B hA h3
  have i3 := card_le_of_mul_eq_one B B' h1
  simp only [Fintype.card_fin, Fintype.card_sum] at i3
  obtain rfl : p = r := by omega
  obtain rfl : q = s := by omega
  refine ⟨B, ⟨?_, B', h1⟩, h4⟩
  calc Bᵀ * M * B.map star = ((Bᵀ * M * B.map star).map star).map star := by simp [Matrix.map_map, Function.comp_def]
    _ = _ := by rw [map_star_trip, ← hGdef, h3, hJ]; rfl

end GlobalTheory.RealLift
end
end

section

open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil

noncomputable section
namespace GlobalTheory.FockHeisQuad

variable {P Q R S : ℕ}

theorem heisOp_single (a : Ix P Q) (b : Ix R S) (z : ℂ) :
    heisOp (Matrix.single a b z) = ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) •
      (z • raiB (a, b) - (lineSign a b * star z) • lowB (a, b)) := by
  unfold heisOp
  congr 1
  rw [Fintype.sum_eq_single (a, b)]
  · simp
  · rintro ⟨a', b'⟩ h
    have : ¬ (a = a' ∧ b = b') := fun ⟨h1, h2⟩ => h (by subst h1; subst h2; rfl)
    simp [Matrix.single_apply, this]

theorem single_mul_tr_apply (a : Ix P Q) (b : Ix R S) (z : ℂ) (Y : Mat R S) (a' : Ix P Q) (b' : Ix R S) :
    (Matrix.single a b z * Yᵀ) a' b' = if a' = a then z * Y b' b else 0 := by
  by_cases h : a' = a
  · subst h; simp [Matrix.mul_apply, Matrix.single_apply]
  · simp [Matrix.mul_apply, Matrix.single_apply, Ne.symm h, h]

theorem heisOp_single_mul (a : Ix P Q) (b : Ix R S) (z : ℂ) (Y : Mat R S) :
    heisOp (Matrix.single a b z * Yᵀ) = ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) •
      ∑ b' : Ix R S, ((z * Y b' b) • raiB (a, b') - (lineSign a b' * star (z * Y b' b)) • lowB (a, b')) := by
  unfold heisOp
  congr 1
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
  · simp [single_mul_tr_apply]
  · intro a' _ h
    simp [single_mul_tr_apply, h]
  · simp

end GlobalTheory.FockHeisQuad

noncomputable section
namespace GlobalTheory.FockHeisQuad

theorem quad {A : Type} [Ring A] [Algebra ℂ A] (U V X L : A) (c p ε : ℂ) (hc : c * c = 2 * p) (hp : p ≠ 0)
    (hε : ε = 1 ∨ ε = -1) :
    (4 * p * Complex.I)⁻¹ • ((ε / 4) • (((c • (U - V)) * (c • (Complex.I • (X + ε • L))) +
        (c • (Complex.I • (X + ε • L))) * (c • (U - V))) -
      ((c • (Complex.I • (U + V))) * (c • (X - ε • L)) + (c • (X - ε • L)) * (c • (Complex.I • (U + V)))))) =
      (1 / 4 : ℂ) • ((U * L + L * U) - ε • (V * X + X * V)) := by
  have hp' : p = c * c / 2 := by linear_combination -hc / 2
  subst hp'
  have hc0 : c ≠ 0 := by rintro rfl; simp at hp
  rcases hε with rfl | rfl <;>
  · simp only [mul_add, add_mul, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, smul_smul]
    match_scalars <;> field_simp <;> ring_nf

variable {R S : ℕ}
theorem upq_entry (Y : Mat R S) (hY : Y ∈ upq R S) {P Q : ℕ} (a : Ix P Q) (b b' : Ix R S) :
    lineSign a b * (lineSign a b' * star (Y b' b)) = - Y b b' := by
  have hJ : Jm R S = Matrix.diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1)) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Jm, Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply] <;> split_ifs <;> simp
  have h := congrFun (congrFun hY b) b'
  rw [hJ] at h
  simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply,
    Matrix.zero_apply] at h
  rcases a with a | a <;> rcases b with b | b <;> rcases b' with b' | b' <;>
    simp [lineSign] at h ⊢ <;> first | linear_combination h | linear_combination -h

end GlobalTheory.FockHeisQuad

noncomputable section
namespace GlobalTheory.FockHeisQuad
variable {P Q R S : ℕ}

theorem fockAct2_expand (Y : Mat R S) :
    fockAct2 P Q R S Y = ∑ a : Ix P Q, ∑ b : Ix R S, ∑ b' : Ix R S, Y b' b • omE (a, b') (a, b) := by
  simp only [fockAct2, LinearMap.comp_apply, omAct_apply,
    Matrix.kroneckerMapBilinear_apply_apply, Matrix.kroneckerMap_apply, LinearMap.mul_apply',
    Fintype.sum_prod_type, Matrix.one_apply]
  simp [ite_smul, Finset.sum_ite_eq, -Fintype.sum_sum_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]

theorem lineSign_cases (a : Ix P Q) (b : Ix R S) : lineSign a b = 1 ∨ lineSign a b = -1 := by
  rcases a with a | a <;> rcases b with b | b <;> simp [lineSign]

theorem term_eq (Y : Mat R S) (hY : Y ∈ upq R S) (a : Ix P Q) (b : Ix R S) :
    (4 * Real.pi * Complex.I : ℂ)⁻¹ • ((lineSign a b / 4) •
      ((heisOp (Matrix.single a b (1 : ℂ) * Yᵀ) * heisOp (Matrix.single a b Complex.I) +
          heisOp (Matrix.single a b Complex.I) * heisOp (Matrix.single a b (1 : ℂ) * Yᵀ)) -
        (heisOp (Matrix.single a b Complex.I * Yᵀ) * heisOp (Matrix.single a b (1 : ℂ)) +
          heisOp (Matrix.single a b (1 : ℂ)) * heisOp (Matrix.single a b Complex.I * Yᵀ)))) =
    ∑ b' : Ix R S, ((1 / 4 : ℂ) * Y b' b) • (raiB (a, b') * lowB (a, b) + lowB (a, b) * raiB (a, b')) +
      ∑ b' : Ix R S, ((1 / 4 : ℂ) * Y b b') • (lowB (a, b') * raiB (a, b) + raiB (a, b) * lowB (a, b')) := by
  set U : Module.End ℂ (Pol P Q R S) := ∑ b' : Ix R S, Y b' b • raiB (a, b') with hU
  set V : Module.End ℂ (Pol P Q R S) := ∑ b' : Ix R S, (lineSign a b' * star (Y b' b)) • lowB (a, b') with hV
  have h1 : heisOp (Matrix.single a b (1 : ℂ) * Yᵀ) = ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) • (U - V) := by
    rw [heisOp_single_mul, hU, hV, ← Finset.sum_sub_distrib]
    simp
  have h2 : heisOp (Matrix.single a b Complex.I * Yᵀ) =
      ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) • (Complex.I • (U + V)) := by
    rw [heisOp_single_mul, hU, hV, ← Finset.sum_add_distrib]
    congr 1
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun b' _ => ?_
    simp only [star_mul', Complex.star_def, Complex.conj_I, smul_add, smul_smul]
    match_scalars <;> ring
  have h3 : heisOp (Matrix.single a b (1 : ℂ)) =
      ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) • (raiB (a, b) - lineSign a b • lowB (a, b)) := by
    rw [heisOp_single]; simp
  have h4 : heisOp (Matrix.single a b Complex.I) =
      ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) • (Complex.I • (raiB (a, b) + lineSign a b • lowB (a, b))) := by
    rw [heisOp_single]
    congr 1
    simp only [Complex.star_def, Complex.conj_I, smul_add, smul_smul]
    match_scalars <;> ring
  have hc : ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) = 2 * (Real.pi : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]; push_cast; ring
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [h1, h2, h3, h4, quad U V (raiB (a, b)) (lowB (a, b)) _ _ _ hc hπ (lineSign_cases a b)]
  simp only [hU, hV, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, ← Finset.sum_add_distrib,
    Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b' _ => ?_
  have e := upq_entry Y hY a b b'
  clear h1 h2 h3 h4 hc hπ hU hV
  simp only [smul_add, smul_sub, smul_smul]
  match_scalars <;> first | ring1 | linear_combination (-1 / 4 : ℂ) * e

end GlobalTheory.FockHeisQuad

noncomputable section
namespace GlobalTheory.FockHeisQuad

theorem fockAct2_eq_heisOp_quad : ∀ (P Q R S : ℕ) (Y : Mat R S), Y ∈ upq R S →
    fockAct2 P Q R S Y = (4 * Real.pi * Complex.I : ℂ)⁻¹ • ∑ a : Ix P Q, ∑ b : Ix R S, (lineSign a b / 4) •
      ((heisOp (Matrix.single a b (1 : ℂ) * Yᵀ) * heisOp (Matrix.single a b Complex.I) +
          heisOp (Matrix.single a b Complex.I) * heisOp (Matrix.single a b (1 : ℂ) * Yᵀ)) -
        (heisOp (Matrix.single a b Complex.I * Yᵀ) * heisOp (Matrix.single a b (1 : ℂ)) +
          heisOp (Matrix.single a b (1 : ℂ)) * heisOp (Matrix.single a b Complex.I * Yᵀ))) := by
  intro P Q R S Y hY
  rw [fockAct2_expand, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.smul_sum]
  simp only [term_eq Y hY a]
  rw [Finset.sum_add_distrib]
  conv_rhs => arg 2; rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b' _ => ?_
  rw [omE, GlobalTheory.FockCasimir.lowB_mul_raiB (a, b) (a, b')]
  by_cases h : b' = b
  · subst h
    simp only [if_true]
    module
  · have h1 : ((a, b') : Ln P Q R S) ≠ (a, b) := by simp [h]
    simp only [h1, Ne.symm h1, if_false, add_zero]
    module

end GlobalTheory.FockHeisQuad
end
end
end
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ChiGrid
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors Pointwise

namespace GlobalTheory.SignatureAddition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Generic

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem coords_gram (B : HSpace E) (x y : B.V) :
    ∑ l, (∑ k, star (B.frame.repr x k) * B.gram k l) * B.frame.repr y l = B.hT x y := by
  conv_rhs => rw [← B.frame.sum_repr x, ← B.frame.sum_repr y]

  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
  Finset.sum_mul, HSpace.gram, RingHom.id_apply, starRingEnd_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring

def middleSymmetricBasisVector (E : Type) [Field E] (c : ℕ) (p : Fin c) : Fin c → E :=
  Pi.single p (if 2 * p.1 + 1 ≤ c then 1 else -1 / 2) +
    Pi.single p.rev (if 2 * p.1 + 1 < c then 1 else if 2 * p.1 + 1 = c then 0 else 1 / 2)

theorem middleSymmetricBasisVectors_gram_antiDiagonal (c : ℕ) (neg : Bool) (p q : Fin c) :
    Examples₂.diagForm c (GlobalTheory.UnitPerp.negFrom c (if neg then c / 2 else (c + 1) / 2)) (middleSymmetricBasisVector E c p) (middleSymmetricBasisVector E c q) =
      antiDiagonalSignGramMatrix c (if neg then -1 else 1) p q := by
  have hp := p.2
  have hq := q.2
  obtain ⟨P, hP⟩ : ∃ P, P = if neg then c / 2 else (c + 1) / 2 := ⟨_, rfl⟩
  have hP1 : c / 2 ≤ P ∧ P ≤ (c + 1) / 2 := by rw [hP]; split_ifs <;> omega
  have hm : 2 * p.1 + 1 = c → (P ≤ p.1 ↔ neg = true) := by
    intro h; rw [hP]; cases neg <;> simp <;> omega
  rw [← hP]
  simp only [middleSymmetricBasisVector, map_add (f := _), LinearMap.add_apply, Examples₂.diagForm_single_left, Pi.single_apply, Pi.add_apply,
    GlobalTheory.UnitPerp.negFrom, Examples₂.sgn, antiDiagonalSignGramMatrix, Fin.ext_iff, Fin.val_rev, decide_eq_true_eq]
  generalize p.1 = a at *
  generalize q.1 = b at *
  clear hP
  have e1 : (c - (a + 1) = c - (b + 1)) = (a = b) := propext (by omega)
  have e2 : (a = c - (b + 1)) = (a + b + 1 = c) := propext (by omega)
  have e3 : (c - (a + 1) = b) = (a + b + 1 = c) := propext (by omega)
  simp only [e1, e2, e3]
  by_cases h1 : a = b <;> by_cases h2 : a + b + 1 = c
  · subst h1
    have h : 2 * a + 1 = c := by omega
    simp only [if_pos h.le, if_pos h, if_neg (show ¬ 2 * a + 1 < c by omega), hm h, if_pos h2]
    cases neg <;> simp
  · subst h1
    rcases (show 2 * a + 1 < c ∨ c < 2 * a + 1 by omega) with h | h
    · simp only [if_pos h.le, if_pos h, if_neg (show ¬ P ≤ a by omega), if_pos (show P ≤ c - (a + 1) by omega), if_neg h2]
      simp
    · simp only [if_neg h.not_ge, if_neg h.not_gt, if_neg h.ne', if_pos (show P ≤ a by omega),
        if_neg (show ¬ P ≤ c - (a + 1) by omega), if_neg h2]
      norm_num
  · rcases (show (2 * a + 1 < c ∧ c < 2 * b + 1) ∨ (2 * b + 1 < c ∧ c < 2 * a + 1) by omega) with ⟨h, h'⟩ | ⟨h', h⟩
    · simp only [if_pos h.le, if_pos h, if_neg (show ¬ P ≤ a by omega), if_pos (show P ≤ c - (a + 1) by omega),
        if_neg h'.not_ge, if_neg h'.not_gt, if_neg h'.ne', if_neg h1, if_pos h2]
      norm_num
    · simp only [if_neg h.not_ge, if_neg h.not_gt, if_neg h.ne', if_pos (show P ≤ a by omega),
        if_neg (show ¬ P ≤ c - (a + 1) by omega), if_pos h'.le, if_pos h', if_neg h1, if_pos h2]
      norm_num
  · simp only [if_neg h1, if_neg h2, add_zero, mul_zero]

end Generic

theorem exists_hermitian_space_add_signature (D : D7) (A : HSp D) (p q c : ℕ) (neg : Bool) (hA : A.SigOK) (hs : ∀ τ, A.sig τ = (p, q)) :
    ∃ B : HSp D, Nonempty (HermitianOrthogonalExtensionData A B c (if neg then -1 else 1)) ∧ B.SigOK ∧
      ∀ τ, B.sig τ = (p + (if neg then c / 2 else (c + 1) / 2), q + (if neg then (c + 1) / 2 else c / 2)) := by
  have hc : c = (if neg then c / 2 else (c + 1) / 2) + (if neg then (c + 1) / 2 else c / 2) := by
    split_ifs <;> omega
  have hW := GlobalTheory.UnitPerp.ofKind_stdSpace (E := D.host.E) hc
  set W : HSp D := Examples₂.stdSpace Examples₂.star_isIntegral c (GlobalTheory.UnitPerp.negFrom c (if neg then c / 2 else (c + 1) / 2))
    (if neg then c / 2 else (c + 1) / 2) (if neg then (c + 1) / 2 else c / 2) with hWd
  refine ⟨GlobalTheory.Doubling.hsum A W, ⟨?_⟩, GlobalTheory.Doubling.sigOK_hsum hA hW.2.1, fun τ => ?_⟩
  · refine
      { ι := LinearMap.inl _ _ _
        isom := GlobalTheory.Doubling.isIsomEmb_inl A W
        a := fun k j => (GlobalTheory.Doubling.hsum A W).frame.repr ((0, middleSymmetricBasisVector D.host.E c j) : A.V × W.V) k
        gram := Matrix.ext fun i j => ?_
        perp := Matrix.ext fun i j => ?_
        rank := rfl }
    · refine Eq.trans (coords_gram (GlobalTheory.Doubling.hsum A W) ((0, middleSymmetricBasisVector D.host.E c i) : A.V × W.V)
        ((0, middleSymmetricBasisVector D.host.E c j) : A.V × W.V)) ?_
      refine (GlobalTheory.Doubling.orthSum_apply A W _ _).trans ?_
      rw [map_zero, zero_add]
      exact middleSymmetricBasisVectors_gram_antiDiagonal c neg i j
    · refine Eq.trans ?_ ((coords_gram (GlobalTheory.Doubling.hsum A W) ((A.frame i, 0) : A.V × W.V)
        ((0, middleSymmetricBasisVector D.host.E c j) : A.V × W.V)).trans ?_)
      · have e : frameMat (GlobalTheory.Doubling.hsum A W) A (LinearMap.inl _ _ _) =
            fun k i => (GlobalTheory.Doubling.hsum A W).frame.repr ((A.frame i, 0) : A.V × W.V) k :=
          Matrix.ext fun k i => LinearMap.toMatrix_apply A.frame (GlobalTheory.Doubling.hsum A W).frame _ k i
        rw [e]
        rfl
      · refine (GlobalTheory.Doubling.orthSum_apply A W _ _).trans ?_
        rw [map_zero, map_zero, zero_add]
        rfl
  · show A.sig τ + W.sig τ = _
    rw [hs τ]
    rfl

end GlobalTheory.SignatureAddition

end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.definiteUnitaryLocalComponent_mem_integralGL_cofinite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (y : UA E n), ∀ᶠ w in cofinite, cLoc w y ∈ GlobalTheory.LFun.KGL w (n := n) := by
  first | exact @GlobalTheory.BCT.SuppFin.cLoc_mem_KGL_cofinite | exact GlobalTheory.BCT.SuppFin.cLoc_mem_KGL_cofinite | (intros; apply GlobalTheory.BCT.SuppFin.cLoc_mem_KGL_cofinite <;> assumption)
end
