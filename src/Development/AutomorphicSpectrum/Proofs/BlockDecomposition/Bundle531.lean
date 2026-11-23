module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Mathlib.Algebra.GroupWithZero.Torsion
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.MapsExist
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle500
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

@[expose] public section

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FrameComplete

open Matrix

section Abstract

variable {A : Type*} [CommRing A] [StarRing A] {ι α β ρ τ : Type*}
  [Fintype ι] [Fintype α] [Fintype β] [Fintype ρ] [Fintype τ]
  [DecidableEq ι] [DecidableEq ρ] [DecidableEq τ]

theorem gram_conj {G : Matrix ι ι A} (hG : Gᴴ = G) (M : Matrix ι α A) (N : Matrix ι β A) :
    (Mᴴ * (G * N))ᴴ = Nᴴ * (G * M) := by
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hG, Matrix.mul_assoc]

theorem orth_part {G : Matrix ι ι A} (hG : Gᴴ = G) {B Bi : Matrix ρ ρ A} (hB : B * Bi = 1)
    {e : A} {x : Matrix ι ρ A} {v : Matrix ι τ A} (hv : e • v = v)
    (hxx : xᴴ * (G * x) = e • B)
    (hq : vᴴ * (G * v) - (Bi * (xᴴ * (G * v)))ᴴ * (B * (Bi * (xᴴ * (G * v)))) = 0) :
    xᴴ * (G * (v - x * (Bi * (xᴴ * (G * v))))) = 0 ∧
      (v - x * (Bi * (xᴴ * (G * v))))ᴴ * (G * (v - x * (Bi * (xᴴ * (G * v))))) = 0 := by
  set c := xᴴ * (G * v) with hc
  set y := Bi * c with hy
  have hec : e • c = c := by
    conv_lhs => rw [hc, ← Matrix.mul_smul, ← Matrix.mul_smul, hv]
  have hBy : B * y = c := by rw [hy, ← Matrix.mul_assoc, hB, Matrix.one_mul]
  have h1 : xᴴ * (G * (v - x * y)) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_sub, ← hc, ← Matrix.mul_assoc G, ← Matrix.mul_assoc, hxx,
      Matrix.smul_mul, hBy, hec, sub_self]
  refine ⟨h1, ?_⟩
  have h2 : (v - x * y)ᴴ * (G * x) = 0 := by
    rw [← gram_conj hG, h1, conjTranspose_zero]
  have h3 : (v - x * y)ᴴ * (G * v) = vᴴ * (G * v) - yᴴ * c := by
    rw [conjTranspose_sub, Matrix.sub_mul, conjTranspose_mul, Matrix.mul_assoc, ← hc]
  rw [Matrix.mul_sub, Matrix.mul_sub, h3, ← Matrix.mul_assoc G, ← Matrix.mul_assoc _ (G * x), h2,
    Matrix.zero_mul, sub_zero, ← hBy]
  exact hq

theorem exists_dual {G Gi : Matrix ι ι A} (hG : Gᴴ = G) (hGi : G * Gi = 1)
    {e h : A} (he : e * e = e) (hse : star e = e) (hh : h + h = 1) (hsh : star h = h)
    {x : Matrix ι ρ A} {u : Matrix ι τ A} {L : Matrix τ ι A} (hu : e • u = u)
    (hxu : xᴴ * (G * u) = 0) (huu : uᴴ * (G * u) = 0) (hLx : L * x = 0) (hLu : L * u = e • 1) :
    ∃ w : Matrix ι τ A, e • w = w ∧ xᴴ * (G * w) = 0 ∧ uᴴ * (G * w) = e • 1 ∧ wᴴ * (G * w) = 0 := by
  set w₀ : Matrix ι τ A := Gi * (e • L)ᴴ with hw₀
  have hGw : G * w₀ = (e • L)ᴴ := by rw [hw₀, ← Matrix.mul_assoc, hGi, Matrix.one_mul]
  have hew : e • w₀ = w₀ := by
    rw [hw₀, ← Matrix.mul_smul, conjTranspose_smul, hse, smul_smul, he]
  have h1 : xᴴ * (G * w₀) = 0 := by
    rw [hGw, ← conjTranspose_mul, Matrix.smul_mul, hLx, smul_zero, conjTranspose_zero]
  have h2 : uᴴ * (G * w₀) = e • 1 := by
    rw [hGw, ← conjTranspose_mul, Matrix.smul_mul, hLu, smul_smul, he, conjTranspose_smul, hse,
      conjTranspose_one]
  have h3 : w₀ᴴ * (G * u) = e • 1 := by
    rw [← gram_conj hG, h2, conjTranspose_smul, hse, conjTranspose_one]
  set Q := w₀ᴴ * (G * w₀) with hQ
  have hQh : Qᴴ = Q := gram_conj hG w₀ w₀
  have heQ : e • Q = Q := by
    conv_lhs => rw [hQ, ← Matrix.mul_smul, ← Matrix.mul_smul, hew]
  have hP : (h • Q)ᴴ = h • Q := by rw [conjTranspose_smul, hsh, hQh]
  have hw : e • (w₀ - u * (h • Q)) = w₀ - u * (h • Q) := by
    rw [smul_sub, hew, ← Matrix.smul_mul, hu]
  have hxw : xᴴ * (G * (w₀ - u * (h • Q))) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_sub, h1, ← Matrix.mul_assoc G, ← Matrix.mul_assoc _ (G * u), hxu,
      Matrix.zero_mul, sub_zero]
  have huw : uᴴ * (G * (w₀ - u * (h • Q))) = e • 1 := by
    rw [Matrix.mul_sub, Matrix.mul_sub, h2, ← Matrix.mul_assoc G, ← Matrix.mul_assoc _ (G * u), huu,
      Matrix.zero_mul, sub_zero]
  refine ⟨w₀ - u * (h • Q), hw, hxw, huw, ?_⟩
  have h4 : w₀ᴴ * (G * (w₀ - u * (h • Q))) = Q - h • Q := by
    rw [Matrix.mul_sub, Matrix.mul_sub, ← hQ, ← Matrix.mul_assoc G, ← Matrix.mul_assoc _ (G * u), h3,
      Matrix.smul_mul, Matrix.one_mul, smul_comm, heQ]
  rw [conjTranspose_sub, Matrix.sub_mul, h4, conjTranspose_mul, hP, Matrix.mul_assoc, huw,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, heQ, sub_sub, ← add_smul, hh, one_smul, sub_self]

theorem gram_three {G : Matrix ι ι A} {κ₁ κ₂ κ₃ : Type*} [Fintype κ₁] [Fintype κ₂] [Fintype κ₃]
    (x : Matrix ι κ₁ A) (u : Matrix ι κ₂ A) (w : Matrix ι κ₃ A) :
    (fromCols (fromCols x u) w)ᴴ * (G * fromCols (fromCols x u) w) =
      fromBlocks (fromBlocks (xᴴ * (G * x)) (xᴴ * (G * u)) (uᴴ * (G * x)) (uᴴ * (G * u)))
        (fromRows (xᴴ * (G * w)) (uᴴ * (G * w)))
        (fromCols (wᴴ * (G * x)) (wᴴ * (G * u))) (wᴴ * (G * w)) := by
  ext (( i | i) | i) ((j | j) | j) <;> simp [Matrix.mul_apply, Fintype.sum_sum_type, conjTranspose_apply]

end Abstract

def gam {K ρ τ : Type*} [Zero K] [One K] [DecidableEq τ] (b : Matrix ρ ρ K) :
    Matrix ((ρ ⊕ τ) ⊕ τ) ((ρ ⊕ τ) ⊕ τ) K :=
  fromBlocks (fromBlocks b 0 0 0) (fromRows 0 1) (fromCols 0 1) 0

theorem gam_map {K L ρ τ : Type*} [Semiring K] [Semiring L] [DecidableEq τ] (f : K →+* L)
    (b : Matrix ρ ρ K) : (gam (τ := τ) b).map f = gam (b.map f) := by
  ext ((i | i) | i) ((j | j) | j) <;> simp [gam, Matrix.one_apply, apply_ite f]

theorem gam_det {K : Type*} [Field K] {r t : ℕ} (b : Matrix (Fin r) (Fin r) K) (hb : b.det ≠ 0) :
    (gam (τ := Fin t) b).det ≠ 0 := by
  have hinv : ∀ i j, ∑ a, b⁻¹ i a * b a j = if i = j then 1 else 0 := fun i j => by
    have := congrFun (congrFun (Matrix.nonsing_inv_mul b (isUnit_iff_ne_zero.2 hb)) i) j
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  refine Matrix.det_ne_zero_of_left_inverse (B := gam (τ := Fin t) b⁻¹) ?_
  ext ((i | i) | i) ((j | j) | j) <;>
    simp [gam, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, hinv]

section Involution

variable {A : Type} [CommRing A] {ι ρ τ : Type} [Fintype ι] [Fintype ρ] [Fintype τ]
  [DecidableEq ι] [DecidableEq ρ] [DecidableEq τ]

theorem complete_frame (σ : A →+* A) (hσ : ∀ a, σ (σ a) = a) {G Gi : Matrix ι ι A}
    (hG : (G.map σ)ᵀ = G) (hGi : G * Gi = 1) {B Bi : Matrix ρ ρ A} (hB : B * Bi = 1)
    {e h : A} (he : e * e = e) (hse : σ e = e) (hh : h + h = 1) (hsh : σ h = h)
    {x : Matrix ι ρ A} {v : Matrix ι τ A} {L : Matrix τ ι A} (hx : e • x = x) (hv : e • v = v)
    (hxx : (x.map σ)ᵀ * (G * x) = e • B)
    (hq : (v.map σ)ᵀ * (G * v) - ((Bi * ((x.map σ)ᵀ * (G * v))).map σ)ᵀ *
      (B * (Bi * ((x.map σ)ᵀ * (G * v)))) = 0)
    (hLx : L * x = 0) (hLv : L * v = e • 1) :
    ∃ N : Matrix ι ((ρ ⊕ τ) ⊕ τ) A, e • N = N ∧ (N.map σ)ᵀ * (G * N) = e • gam B ∧
      (∀ i j, N i (Sum.inl (Sum.inl j)) = x i j) ∧
      ∀ i j, N i (Sum.inl (Sum.inr j)) = (v - x * (Bi * ((x.map σ)ᵀ * (G * v)))) i j := by
  letI : StarRing A :=
    { star := σ
      star_involutive := hσ
      star_mul := fun a b => by rw [map_mul, mul_comm]
      star_add := map_add σ }
  have hmap : ∀ {α β : Type} (M : Matrix α β A), (M.map σ)ᵀ = Mᴴ := fun M => by
    ext i j; rfl
  simp only [hmap] at hG hxx hq ⊢
  obtain ⟨hxu, huu⟩ := orth_part hG hB hv hxx hq
  set u : Matrix ι τ A := v - x * (Bi * (xᴴ * (G * v))) with hu
  have heu : e • u = u := by
    have hy : e • (x * (Bi * (xᴴ * (G * v)))) = x * (Bi * (xᴴ * (G * v))) := by
      rw [← Matrix.smul_mul, hx]
    rw [hu, smul_sub, hv, hy]
  have hLu : L * u = e • 1 := by
    rw [hu, Matrix.mul_sub, hLv, ← Matrix.mul_assoc, hLx, Matrix.zero_mul, sub_zero]
  obtain ⟨w, hew, hxw, huw, hww⟩ :=
    exists_dual hG hGi he (show star e = e from hse) hh (show star h = h from hsh) heu hxu huu hLx hLu
  refine ⟨fromCols (fromCols x u) w, ?_, ?_, fun i j => rfl, fun i j => rfl⟩
  · ext i ((j | j) | j)
    · simpa using congrFun (congrFun hx i) j
    · simpa using congrFun (congrFun heu i) j
    · simpa using congrFun (congrFun hew i) j
  · have hux : uᴴ * (G * x) = 0 := by rw [← gram_conj hG, hxu, conjTranspose_zero]
    have hwx : wᴴ * (G * x) = 0 := by rw [← gram_conj hG, hxw, conjTranspose_zero]
    have hwu : wᴴ * (G * u) = e • 1 := by
      rw [← gram_conj hG, huw, conjTranspose_smul, conjTranspose_one]
      exact congrArg (· • (1 : Matrix τ τ A)) hse
    rw [gram_three, hxx, hxu, huu, hxw, huw, hww, hux, hwx, hwu]
    ext ((i | i) | i) ((j | j) | j) <;> simp [gam, Matrix.one_apply]

end Involution

theorem frame_completes : ∀ (D : D7) (r t : ℕ) (V : HSp D) (b₀ : HermE D r), b₀.1.det ≠ 0 → ∀ e : AE D, e * e = e → cA D e = e → ∃ Γ : Matrix ((Fin r ⊕ Fin t) ⊕ Fin t) ((Fin r ⊕ Fin t) ⊕ Fin t) D.host.E, Γ.det ≠ 0 ∧ ∀ z : Mx D V.rank r × Mx D V.rank t, Free e z → (e • z.1 = z.1 ∧ e • z.2 = z.2 ∧ ip V z.1 z.1 = e • rat b₀.1 ∧ qv V b₀ z = 0) → ∃ N : Matrix (Fin V.rank) ((Fin r ⊕ Fin t) ⊕ Fin t) (AE D), e • N = N ∧ (HMul.hMul (N.map (cA D))ᵀ (HMul.hMul (gA V) N : Matrix (Fin V.rank) ((Fin r ⊕ Fin t) ⊕ Fin t) (AE D)) : Matrix ((Fin r ⊕ Fin t) ⊕ Fin t) ((Fin r ⊕ Fin t) ⊕ Fin t) (AE D)) = e • Γ.map (incA D) ∧ (∀ i j, N i (Sum.inl (Sum.inl j)) = z.1 i j) ∧ ∀ i j, N i (Sum.inl (Sum.inr j)) = (z.2 - mm z.1 (yv V b₀ z)) i j := by
  intro D r t V b₀ hb e he hse
  refine ⟨gam b₀.1, gam_det _ hb, ?_⟩
  rintro ⟨x, v⟩ ⟨L₁, L₂, -, -, h21, h22⟩ ⟨hx, hv, hxx, hq⟩
  have hdet : IsUnit (HSpace.gram V).det := isUnit_iff_ne_zero.2 (isHermND_gram V).2
  have hGi : gA V * giA V = 1 := by
    have := rat_mul (D := D) (HSpace.gram V) (HSpace.gram V)⁻¹
    rw [Matrix.mul_nonsing_inv _ hdet] at this
    exact this.symm.trans (by simp [rat])
  have hB : rat (D := D) b₀.1 * rat b₀.1⁻¹ = 1 := by
    have := rat_mul (D := D) b₀.1 b₀.1⁻¹
    rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hb)] at this
    exact this.symm.trans (by simp [rat])
  have hh : incA D 2⁻¹ + incA D 2⁻¹ = 1 := by
    rw [← map_add (f := _), ← two_mul, mul_inv_cancel₀ two_ne_zero, map_one]
  have hsh : cA D (incA D 2⁻¹) = incA D 2⁻¹ := by
    rw [GlobalTheory.DualPairCheck.cA_incA, star_inv₀, star_ofNat]
  obtain ⟨N, h1, h2, h3, h4⟩ := complete_frame (cA D) cA_cA (G := gA V) (Gi := giA V) (adj_gA V) hGi
    hB he hse hh hsh (x := x) (v := v) (L := L₂) hx hv hxx hq h21 h22
  refine ⟨N, h1, ?_, h3, h4⟩
  rw [gam_map]
  exact h2

end GlobalTheory.CompanionTheory.FrameComplete
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.RCellInv

variable {D : D7} {t ρ : ℕ}

theorem block_matrix_mul {n : ℕ} (a b c d a' b' c' d' : Mx D n n) :
    (blk4 a b c d * blk4 a' b' c' d' : Mx D (n + n) (n + n)) =
      blk4 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  simp only [blk4]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem mat_mul_mat {n : ℕ} (g h : G D n) : mat (g * h) = mat g * mat h := by
  simp only [mat, map_mul, Units.val_mul]

theorem trace_adj_eq {n : ℕ} (M : Mx D n n) : Matrix.trace (adj M) = cA D (Matrix.trace M) := by
  rw [adj, Matrix.trace_transpose]
  exact (AddMonoidHom.map_trace (cA D).toAddMonoidHom M).symm

theorem adj_gram (b₀ : HermE D ρ) : adj (b₀.1.map (incA D)) = b₀.1.map (incA D) := by
  ext i j
  have h := congrFun (congrFun b₀.2 i) j
  simp only [adj, Matrix.transpose_apply, Matrix.map_apply] at h ⊢
  rw [GlobalTheory.DualPairCheck.cA_incA]
  exact congrArg (incA D) h

theorem adj_pr (b₀ : HermE D ρ) (x y : Mx D ρ t) : adj (pr b₀ x y) = pr b₀ y x := by
  have adj_mul_local {l m n : ℕ} (a : Mx D l m) (b : Mx D m n) :
      adj (a * b) = adj b * adj a := by
    unfold adj
    rw [Matrix.map_mul, Matrix.transpose_mul]
  simp only [pr, adj_mul_local, adj_adj, adj_gram, Matrix.mul_assoc]

theorem pr_neg_left (b₀ : HermE D ρ) (x y : Mx D ρ t) : pr b₀ (-x) y = -pr b₀ x y := by
  simp only [pr, adj_neg, Matrix.neg_mul]

theorem trA_trace_pr_swap (b₀ : HermE D ρ) (x y : Mx D ρ t) :
    trA (Matrix.trace (pr b₀ y x)) = trA (Matrix.trace (pr b₀ x y)) := by
  rw [← adj_pr b₀ x y, trace_adj_eq]
  exact GlobalTheory.DualPairCheck.trace_cA _

theorem conj_char {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (u : AF D.host.F) :
    conj (ψ u) = ψ (-u) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hψ.2.1 u)]

theorem det_neg_one (t : ℕ) :
    Matrix.GeneralLinearGroup.det (-1 : GL (Fin t) (AE D)) =
      Units.map (incA D).toMonoidHom ((-1 : (D.host.E)ˣ) ^ t) := by
  ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_neg]

theorem absA_det_neg_one (t : ℕ) : absA D (Matrix.GeneralLinearGroup.det (-1 : GL (Fin t) (AE D))) = 1 := by
  have h : absA D (Matrix.GeneralLinearGroup.det (-1 : GL (Fin t) (AE D))) ^ 2 = 1 := by
    rw [← map_pow, ← map_pow, neg_one_sq, map_one, map_one]
  exact (pow_eq_one_iff.1 h).resolve_right two_ne_zero

theorem weyl_sq {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) {θ : InfFam D}
    {b₀ : HermE D ρ} {μ : Measure (Mx D ρ t)} {Ω : G D t → Mx D ρ t → ℂ} (hΩ : IsTh ψ χ θ b₀ μ Ω)
    {w : G D t} (hw : IsW w) (h : G D t) (y : Mx D ρ t) : Ω (w * (w * h)) y = Ω h (-y) := by
  have hm : mat (w * w) = blk4 (-1 : GL (Fin t) (AE D)).1 0 0 (adj ((-1 : GL (Fin t) (AE D))⁻¹).1) := by
    have hi : ((-1 : GL (Fin t) (AE D))⁻¹) = -1 := by
      rw [inv_eq_iff_mul_eq_one]
      simp
    have ha : adj (-1 : Mx D t t) = -1 := by
      rw [adj_neg, adj_one]
    rw [hi, mat_mul_mat, show mat w = _ from hw, block_matrix_mul]
    simp [ha]
  have hl := hΩ.levi (w * w) (-1) hm h y
  have hc : (χ (Matrix.GeneralLinearGroup.det (-1 : GL (Fin t) (AE D))) : ℂ) = 1 := by
    rw [det_neg_one]
    have := hχ.2 ((-1 : (D.host.E)ˣ) ^ t)
    rw [this]
    simp
  rw [← mul_assoc, hl, hc, absA_det_neg_one]
  simp [npow]

end GlobalTheory.CompanionTheory.RCellInv


open GlobalTheory.CompanionTheory.RCellInv in
theorem GlobalTheory.CompanionTheory.RCellInv.fourier_inv : ∀ {D : D7} {t ρ : ℕ} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) {θ : InfFam D} {b₀ : HermE D ρ} {μ : Measure (Mx D ρ t)} {Ω : G D t → Mx D ρ t → ℂ} (hΩ : IsTh ψ χ θ b₀ μ Ω) {nb : hermA D t → G D t} (hnb : IsNMap nb) {w : G D t} (hw : IsW w) (b : hermA D t) (y₀ : Mx D ρ t), ∫ y, ψ (trA (Matrix.trace (pr b₀ y y₀))) * conj (Ω (w * nb b) y) ∂μ = conj (ψ (halfTr (Matrix.trace (mm b.1 (pr b₀ y₀ y₀)))) * Ω 1 y₀) := by
  intro D t ρ ψ hψ χ hχ θ b₀ μ Ω hΩ nb hnb w hw b y₀
  have hint : ∀ y, ψ (trA (Matrix.trace (pr b₀ y y₀))) * conj (Ω (w * nb b) y) =
      conj (Ω (w * nb b) y * ψ (trA (Matrix.trace (pr b₀ (-y₀) y)))) := by
    intro y
    have hneg : -trA (Matrix.trace (pr b₀ (-y₀) y)) = trA (Matrix.trace (pr b₀ y y₀)) := by
      rw [pr_neg_left, Matrix.trace_neg, trA_trace_pr_swap b₀ y₀ y]
      simp only [trA, map_neg, neg_neg]
    rw [map_mul, conj_char hψ, hneg, mul_comm]
  have hu := hΩ.unip (nb b) b.1 (hnb b) 1 y₀
  rw [mul_one] at hu
  simp only [hint]
  rw [integral_conj, ← hΩ.weyl w hw (w * nb b) (-y₀), weyl_sq hχ hΩ hw, neg_neg, hu]
end
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.RCellCont

theorem continuity_characters_projection : ∀ {D : D7} {t ρ : ℕ} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (V : HSp D) (b₀ : HermE D ρ) (b : hermA D t), Continuous (fun z : Mx D V.rank ρ × Mx D V.rank t => pch ψ b.1 (ip V z.2 z.2)) ∧ Continuous (fun z : Mx D V.rank ρ × Mx D V.rank t => yv V b₀ z) ∧ Continuous (fun q : Mx D ρ t × (Mx D V.rank ρ × Mx D V.rank t) => ψ (trA (Matrix.trace (pr b₀ q.1 (yv V b₀ q.2))))) ∧ Continuous (fun z : Mx D V.rank ρ × Mx D V.rank t => pch ψ b.1 (qv V b₀ z)) ∧ (∀ T, ‖pch ψ b.1 T‖ = 1) ∧ ∀ u, ‖ψ u‖ = 1 := by
  intro D t ρ ψ hψ V b₀ b
  have hψc : Continuous ψ := hψ.1
  have hψn : ∀ u, ‖ψ u‖ = 1 := hψ.2.1
  have htr : Continuous (trA (D := D)) := by unfold trA; fun_prop
  have hhalf : Continuous (halfTr (D := D)) := by
    unfold halfTr
    exact continuous_const.mul htr
  have hpch : ∀ {n : ℕ} (x : Mx D n n), Continuous (fun T : Mx D n n => pch ψ x T) := by
    intro n x
    unfold pch mm
    exact hψc.comp (hhalf.comp ((continuous_const.matrix_mul continuous_id).matrix_trace))
  have hip : ∀ {a c : ℕ} {X : Type} [TopologicalSpace X] (f : X → Mx D V.rank a) (g : X → Mx D V.rank c),
      Continuous f → Continuous g → Continuous (fun x => ip V (f x) (g x)) := by
    intro a c X _ f g hf hg
    unfold ip mm
    exact (GlobalTheory.MixModel.continuous_adj.comp hf).matrix_mul (continuous_const.matrix_mul hg)
  have hyv : Continuous (fun z : Mx D V.rank ρ × Mx D V.rank t => yv V b₀ z) := by
    unfold yv mm
    exact continuous_const.matrix_mul (hip _ _ continuous_fst continuous_snd)
  have hpr : ∀ {p : ℕ} {X : Type} [TopologicalSpace X] (f g : X → Mx D ρ p),
      Continuous f → Continuous g → Continuous (fun x => pr b₀ (f x) (g x)) := by
    intro p X _ f g hf hg
    unfold pr
    exact (GlobalTheory.MixModel.continuous_adj.comp hf).matrix_mul (continuous_const.matrix_mul hg)
  refine ⟨?_, hyv, ?_, ?_, ?_, hψn⟩
  · exact (hpch b.1).comp (hip _ _ continuous_snd continuous_snd)
  · exact hψc.comp (htr.comp (hpr _ _ continuous_fst (hyv.comp continuous_snd)).matrix_trace)
  · have hq : Continuous (fun z : Mx D V.rank ρ × Mx D V.rank t => qv V b₀ z) := by
      unfold qv
      set_option synthInstance.maxHeartbeats 200000 in
        exact (hip _ _ continuous_snd continuous_snd).sub (hpr _ _ hyv hyv)
    exact (hpch b.1).comp hq
  · intro T
    unfold pch
    exact hψn _

end GlobalTheory.CompanionTheory.RCellCont

end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FreeFrames

theorem isOpen_free_frame_pairs {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (r t a : ℕ) (e : R) (he : e * e = e) (U : Set R) (hU : IsOpen U) (h1 : (1 : R) ∈ U)
    (hb : ∀ x ∈ U, ∃ b, x * b = e) :
    IsOpen {z : Matrix (Fin a) (Fin r) R × Matrix (Fin a) (Fin t) R |
      ∃ (L₁ : Matrix (Fin r) (Fin a) R) (L₂ : Matrix (Fin t) (Fin a) R),
        L₁ * (e • z.1) = e • 1 ∧ L₁ * (e • z.2) = 0 ∧ L₂ * (e • z.1) = 0 ∧ L₂ * (e • z.2) = e • 1} := by
  classical
  rw [isOpen_iff_mem_nhds]
  rintro z₀ ⟨L₁, L₂, h11, h12, h21, h22⟩
  let L : Matrix (Fin r ⊕ Fin t) (Fin a) R := Matrix.fromRows L₁ L₂
  let Z : Matrix (Fin a) (Fin r) R × Matrix (Fin a) (Fin t) R → Matrix (Fin a) (Fin r ⊕ Fin t) R :=
    fun z => Matrix.fromCols (e • z.1) (e • z.2)
  let C : Matrix (Fin a) (Fin r) R × Matrix (Fin a) (Fin t) R → Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) R :=
    fun z => L * Z z + (1 - e) • (1 : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) R)
  have hone : (1 : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) R) = Matrix.fromBlocks 1 0 0 1 :=
    Matrix.fromBlocks_one.symm
  have hLZ : L * Z z₀ = e • (1 : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) R) := by
    simp only [L, Z]
    rw [Matrix.fromRows_mul_fromCols, h11, h12, h21, h22, hone, Matrix.fromBlocks_smul]
    simp only [smul_zero]
  have hC0 : C z₀ = 1 := by
    simp only [C]
    rw [hLZ, ← add_smul]
    simp
  have hZc : Continuous Z := by
    refine continuous_matrix fun i j => ?_
    cases j with
    | inl j =>
      have h : Continuous fun z : Matrix (Fin a) (Fin r) R × Matrix (Fin a) (Fin t) R => e * z.1 i j :=
        Continuous.mul continuous_const (continuous_fst.matrix_elem i j)
      simpa [Z] using h
    | inr j =>
      have h : Continuous fun z : Matrix (Fin a) (Fin r) R × Matrix (Fin a) (Fin t) R => e * z.2 i j :=
        Continuous.mul continuous_const (continuous_snd.matrix_elem i j)
      simpa [Z] using h
  have hCc : Continuous C := by
    exact (continuous_const.matrix_mul hZc).add continuous_const
  have hd : Continuous fun z => (C z).det := hCc.matrix_det
  have hnhds : (fun z => (C z).det) ⁻¹' U ∈ 𝓝 z₀ := by
    refine (hU.preimage hd).mem_nhds ?_
    simpa [Set.mem_preimage, hC0] using h1
  refine Filter.mem_of_superset hnhds ?_
  intro z hz
  obtain ⟨b, hb'⟩ := hb _ hz
  have hLz : L * Z z = C z - (1 - e) • (1 : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) R) := by
    simp only [C, add_sub_cancel_right]
  have hee : e * (1 - e) = 0 := by rw [mul_sub, he, mul_one, sub_self]
  have key : ((e * b) • ((C z).adjugate * L)) * Z z = e • (1 : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) R) := by
    rw [Matrix.smul_mul, Matrix.mul_assoc, hLz, Matrix.mul_sub, Matrix.adjugate_mul, Matrix.mul_smul,
      Matrix.mul_one, smul_sub, smul_smul, smul_smul]
    have h2 : e * b * (1 - e) = 0 := by
      rw [mul_right_comm, hee, zero_mul]
    have h3 : e * b * (C z).det = e := by
      rw [mul_assoc, mul_comm b, hb', he]
    rw [h2, h3, zero_smul, sub_zero]
  set L' := (e * b) • ((C z).adjugate * L) with hL'
  have key' : Matrix.fromBlocks (L'.toRows₁ * (e • z.1)) (L'.toRows₁ * (e • z.2))
      (L'.toRows₂ * (e • z.1)) (L'.toRows₂ * (e • z.2)) =
      Matrix.fromBlocks (e • 1) 0 0 (e • 1) := by
    rw [← Matrix.fromRows_mul_fromCols, Matrix.fromRows_toRows]
    have := key
    simp only [Z] at this
    rw [this, hone, Matrix.fromBlocks_smul]
    simp only [smul_zero]
  obtain ⟨a1, a2, a3, a4⟩ := Matrix.fromBlocks_inj.1 key'
  exact ⟨L'.toRows₁, L'.toRows₂, a1, a2, a3, a4⟩

theorem isOpen_free : ∀ (D : D7) (r t a : ℕ) (e : AE D), e * e = e →
    (∃ U : Set (AE D), IsOpen U ∧ 1 ∈ U ∧ ∀ x ∈ U, ∃ b, x * b = e) →
    IsOpen {z : Mx D a r × Mx D a t | Free e (e • z.1, e • z.2)} := by
  rintro D r t a e he ⟨U, hU, h1, hb⟩
  exact isOpen_free_frame_pairs r t a e he U hU h1 hb

end GlobalTheory.CompanionTheory.FreeFrames
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.centre_character_quadratic_trace : ∀ (D : D7) (ρ p : ℕ) (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (b : Mx D p p) (y : Mx D ρ p) (z₀ : hermA D ρ),
  z₀.1 = HMul.hMul (HMul.hMul y b : Mx D ρ p) (adj y) →
    chz ψ b₀ z₀ = ψ (halfTr (Matrix.trace (HMul.hMul b (pr b₀ y y) : Mx D p p))) := by
  first | exact @GlobalTheory.CompanionTheory.ChzConj.chz_conj | exact GlobalTheory.CompanionTheory.ChzConj.chz_conj | (intros; apply GlobalTheory.CompanionTheory.ChzConj.chz_conj <;> assumption)
end
