module

import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.CapelliEigenvalues.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.SmRight
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.CapelliHighestWeightConjugated
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle126
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle234
public import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle229
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameDualUnipotentGroupActsUnitriangularOnto
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle095
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairCoordinatesTransportInnerData
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesComplementUnitaryActsOnTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle096
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

open Matrix Formalism.REAL Formalism.QuantumDeterminants

noncomputable section

namespace GlobalTheory.CapelliLocality

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma exp_inUH (H K Y : Matrix (Fin n) (Fin n) ℂ) (hKH : K * H = 1) (hHK : H * K = 1)
    (hY : Yᴴ * H = -(H * Y)) : inUH H (NormedSpace.exp Y) := by
  have h1 : Yᴴ = H * (-Y) * K := by
    calc Yᴴ = Yᴴ * H * K := by rw [Matrix.mul_assoc, hHK, Matrix.mul_one]
      _ = H * (-Y) * K := by rw [hY, Matrix.mul_neg]
  unfold inUH
  rw [← Matrix.exp_conjTranspose, h1, ioh_exp_conj H K (-Y) hKH hHK]
  have h2 : NormedSpace.exp (-Y) * NormedSpace.exp Y = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.refl Y).neg_left, neg_add_cancel, NormedSpace.exp_zero]
  calc H * NormedSpace.exp (-Y) * K * H * NormedSpace.exp Y
      = H * (NormedSpace.exp (-Y) * (K * H) * NormedSpace.exp Y) := by simp only [Matrix.mul_assoc]
    _ = H := by rw [hKH, Matrix.mul_one, h2, Matrix.mul_one]

lemma inUH_mul {H a b : Matrix (Fin n) (Fin n) ℂ} (ha : inUH H a) (hb : inUH H b) : inUH H (a * b) := by
  unfold inUH at *
  calc (a * b)ᴴ * H * (a * b) = bᴴ * (aᴴ * H * a) * b := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = H := by rw [ha, hb]

lemma rdV_congr (H K X : Matrix (Fin n) (Fin n) ℂ) (hKH : K * H = 1) (hHK : H * K = 1)
    (hX : Xᴴ * H = -(H * X)) {F₁ F₂ : Matrix (Fin n) (Fin n) ℂ → E}
    (hF : ∀ x, inUH H x → F₁ x = F₂ x) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUH H g) :
    RdV X F₁ g = RdV X F₂ g := by
  unfold RdV
  congr 1
  funext t
  refine hF _ (inUH_mul hg (exp_inUH H K _ hKH hHK ?_))
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, hX, smul_neg]
  simp

lemma hpart1_mem (H Z : Matrix (Fin n) (Fin n) ℂ) (hKH : H⁻¹ * H = 1) (hHK : H * H⁻¹ = 1)
    (hH : Hᴴ = H) : (hpart1 H Z)ᴴ * H = -(H * hpart1 H Z) := by
  have hi : (H⁻¹)ᴴ = H⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hH]
  have e : H * (H⁻¹ * (Zᴴ * H)) = Zᴴ * H := by rw [← Matrix.mul_assoc, hHK, Matrix.one_mul]
  unfold hpart1
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hi, hH,
    Matrix.conjTranspose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.mul_assoc, hKH, e, Matrix.mul_one]
  rw [← smul_neg, neg_sub]
  simp

lemma hpart2_mem (H Z : Matrix (Fin n) (Fin n) ℂ) (hKH : H⁻¹ * H = 1) (hHK : H * H⁻¹ = 1)
    (hH : Hᴴ = H) : (hpart2 H Z)ᴴ * H = -(H * hpart2 H Z) := by
  have hi : (H⁻¹)ᴴ = H⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hH]
  have e : H * (H⁻¹ * (Zᴴ * H)) = Zᴴ * H := by rw [← Matrix.mul_assoc, hHK, Matrix.one_mul]
  have hs : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by
    simp
  unfold hpart2
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul, hi, hH,
    Matrix.conjTranspose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_assoc, hKH, e, Matrix.mul_one]
  rw [hs, neg_smul, add_comm]

lemma foldr_congr (H : Matrix (Fin n) (Fin n) ℂ) (hKH : H⁻¹ * H = 1) (hHK : H * H⁻¹ = 1)
    (hH : Hᴴ = H) (l : List (ℂ × Fin n × Fin n)) {F₁ F₂ : Matrix (Fin n) (Fin n) ℂ → E}
    (hF : ∀ x, inUH H x → F₁ x = F₂ x) :
    ∀ x, inUH H x →
      (l.map fun p => Formalism.QuantumDeterminants.Top (EabH H) p.1 p.2.1 p.2.2).foldr (fun T h => T h) F₁ x =
      (l.map fun p => Formalism.QuantumDeterminants.Top (EabH H) p.1 p.2.1 p.2.2).foldr (fun T h => T h) F₂ x := by
  induction l with
  | nil => simpa using hF
  | cons p l ih =>
    intro x hx
    simp only [List.map_cons, List.foldr_cons]
    generalize (l.map fun p => Formalism.QuantumDeterminants.Top (EabH H) p.1 p.2.1 p.2.2).foldr (fun T h => T h) F₁ = G₁ at ih ⊢
    generalize (l.map fun p => Formalism.QuantumDeterminants.Top (EabH H) p.1 p.2.1 p.2.2).foldr (fun T h => T h) F₂ = G₂ at ih ⊢
    unfold Formalism.QuantumDeterminants.Top EabH
    rw [ih x hx, rdV_congr H H⁻¹ _ hKH hHK (hpart1_mem H _ hKH hHK hH) ih hx,
      rdV_congr H H⁻¹ _ hKH hHK (hpart2_mem H _ hKH hHK hH) ih hx]

theorem capelliH_local : PI.UnitaryGroupMassFormula.CapelliEig.Loc := by
  apply CompanionTheory.CapEig.capelli_localization <;> assumption

end GlobalTheory.CapelliLocality

end
end

section

open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset

namespace GlobalTheory.Count.SubquotFrame

theorem map_mulVec' {n : ℕ} (σ : ℂ →+* ℂ) (M : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) :
    M.map σ *ᵥ (fun i => σ (u i)) = fun i => σ ((M *ᵥ u) i) := by
  funext i
  exact (RingHom.map_mulVec σ M u i).symm

theorem map_inv' {n : ℕ} (σ : ℂ →+* ℂ) (G : Matrix (Fin n) (Fin n) ℂ) (hG : IsUnit G.det) :
    (G.map σ)⁻¹ = G⁻¹.map σ := by
  refine Matrix.inv_eq_left_inv ?_
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hG, Matrix.map_one _ (map_zero σ) (map_one σ)]

theorem exists_invol (I : AutInst) (x : I.GA) (w : InfinitePlace I.E) :
    ∃ σ : ℂ →+* ℂ, (∀ z, σ (σ z) = z) ∧ (∀ z, ‖σ z‖ = ‖z‖) ∧
      (∀ a, w.embedding a = σ (I.φ (w.comap (algebraMap I.F I.E)) a)) ∧
      frm I x w = (I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E)))).map σ := by
  have hw : w = InfinitePlace.mk (I.φ (w.comap (algebraMap I.F I.E))) := by
    apply (GlobalTheory.Count.FrameMajorant.comap_bijective I).1
    show w.comap (algebraMap I.F I.E) =
      (InfinitePlace.mk (I.φ (w.comap (algebraMap I.F I.E)))).comap (algebraMap I.F I.E)
    rw [InfinitePlace.comap_mk]
    have hc : (I.φ (w.comap (algebraMap I.F I.E))).comp (algebraMap I.F I.E) =
        (w.comap (algebraMap I.F I.E)).embedding := by
      ext a
      simp [I.φ_over]
    rw [hc, InfinitePlace.mk_embedding]
  by_cases h : w.embedding = I.φ (w.comap (algebraMap I.F I.E))
  · refine ⟨RingHom.id ℂ, fun z => rfl, fun z => rfl, fun a => by rw [h]; rfl, ?_⟩
    unfold frm
    rw [if_pos h]
    ext i j
    simp
  · have h2 : ComplexEmbedding.conjugate w.embedding = I.φ (w.comap (algebraMap I.F I.E)) :=
      (InfinitePlace.mk_eq_iff.mp ((InfinitePlace.mk_embedding w).trans hw)).resolve_left h
    refine ⟨starRingEnd ℂ, fun z => Complex.conj_conj z, fun z => Complex.norm_conj z, fun a => ?_, ?_⟩
    · rw [← h2]
      simp [ComplexEmbedding.conjugate_coe_eq]
    · unfold frm
      rw [if_neg h]

private theorem map_conj_mulVec_map_inv_mulVec {n : ℕ} (σ : ℂ →+* ℂ) (M T : Matrix (Fin n) (Fin n) ℂ) (hM : IsUnit M.det)
    (u : Fin n → ℂ) :
    (M⁻¹ * T * M).map σ *ᵥ (fun i => σ ((M⁻¹ *ᵥ u) i)) = fun i => σ ((M⁻¹ *ᵥ (T *ᵥ u)) i) := by
  rw [map_mulVec', Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc (M⁻¹ * T),
    Matrix.mul_nonsing_inv _ hM, Matrix.mul_one]

private theorem map_mulVec_mem_span_image_of_mem_span {n : ℕ} (σ : ℂ →+* ℂ) (N : Matrix (Fin n) (Fin n) ℂ) (s : Set (Fin n → ℂ))
    (u : Fin n → ℂ) (hu : u ∈ Submodule.span ℂ s) :
    (fun i => σ ((N *ᵥ u) i)) ∈ Submodule.span ℂ ((fun u : Fin n → ℂ => fun i => σ ((N *ᵥ u) i)) '' s) := by
  induction hu using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
  | zero =>
    convert Submodule.zero_mem _ using 1
    funext i
    simp
  | add y z _ _ hy hz =>
    convert Submodule.add_mem _ hy hz using 1
    funext i
    simp [Matrix.mulVec_add]
  | smul c y _ hy =>
    convert Submodule.smul_mem _ (σ c) hy using 1
    funext i
    simp [Matrix.mulVec_smul]

private theorem isCMExt_apply_apply {n : ℕ} (σ : ℂ →+* ℂ) (hσ : ∀ z, σ (σ z) = z) (D : Matrix (Fin n) (Fin n) ℂ)
    (z r : Fin n → ℂ) (h : D *ᵥ (fun i => σ (z i)) = fun i => σ (r i)) : D.map σ *ᵥ z = r := by
  have key := map_mulVec' σ D (fun i => σ (z i))
  simp only [hσ] at key
  rw [h] at key
  simp only [hσ] at key
  exact key

private theorem inv_mul_inv_mul_conj_mul_mul_eq_self {n : ℕ} (P U Q : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P.det)
    (hU : IsUnit U.det) : U⁻¹ * P⁻¹ * (P * U * Q * (P * U)⁻¹) * P * U = Q := by
  have k1 : ∀ B : Matrix (Fin n) (Fin n) ℂ, P⁻¹ * (P * B) = B := fun B => by
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP, Matrix.one_mul]
  have k2 : ∀ B : Matrix (Fin n) (Fin n) ℂ, U⁻¹ * (U * B) = B := fun B => by
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hU, Matrix.one_mul]
  rw [Matrix.mul_inv_rev]
  simp only [Matrix.mul_assoc, k1, k2, Matrix.nonsing_inv_mul _ hU, Matrix.mul_one]

private theorem hs_map_of_norm_preserving {n : ℕ} (σ : ℂ →+* ℂ) (hσ : ∀ z, ‖σ z‖ = ‖z‖) (G : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.hs (G.map σ) = Formalism.REAL.hs G := by
  simp only [Formalism.REAL.hs, Matrix.map_apply, hσ]

theorem subquot_frame : ∀ (I : AutInst) (x : I.GA) (A S R : Submodule (𝓞 I.E) (Fin I.n → I.E)) (lo hi : ℝ), A.FG → IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) A S → R.FG → 0 < lo → 0 < hi → (∀ N, S < N → N ≤ A → lo ≤ sizeQ (bas I) (frm I x) N S) → largestSize (bas I) (frm I x) R ≤ hi → ∀ T : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ, (∀ v, ∀ y ∈ S, T v *ᵥ (fun i => I.φ v (y i)) = 0) → (∀ v, ∀ y ∈ A, T v *ᵥ (fun i => I.φ v (y i)) ∈ spanAt I R v) → ∃ Φ : Matrix (Fin I.n) (Fin I.n) I.E, (∀ y ∈ S, Φ *ᵥ y = 0) ∧ (∀ y ∈ A, Φ *ᵥ y ∈ R) ∧ ∃ D : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ, (∀ v, ∀ u ∈ spanAt I A v, D v *ᵥ u = (T v - Φ.map (I.φ v)) *ᵥ u) ∧ normAt I x D ≤ ((rkK A : ℝ) - rkK S) * rkK R * Real.sqrt I.f * I.rd * hi / (2 * lo) := by
  intro I x A S R lo hi hA hSat hR hlo hhi hsz hlg T hTS hTA
  classical
  have : IsTotallyComplex I.E := I.cm.cmUnram.1
  have hbij := GlobalTheory.Count.FrameMajorant.comap_bijective I
  have hnp : nPl I.E = I.f := by
    rw [nPl, Fintype.card_of_bijective hbij, GlobalTheory.Count.FrameMajorant.card_places]
  choose σ hσi hσn hσe hσf using fun w : InfinitePlace I.E => exists_invol I x w
  have hPu : ∀ v, IsUnit (I.P v).det := fun v => (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v)
  have hUu : ∀ v, IsUnit (uMat (x.1 v)).det := fun v =>
    (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _)
  have hMu : ∀ v, IsUnit (I.P v * uMat (x.1 v)).det := fun v => by
    rw [Matrix.det_mul]
    exact (hPu v).mul (hUu v)

  have hco : ∀ (w : InfinitePlace I.E) (y : Fin I.n → I.E),
      Formalism.HermitianLatticesTheory.fcoord (bas I) (frm I x) w y = fun i => σ w (((I.P (w.comap (algebraMap I.F I.E)) *
        uMat (x.1 (w.comap (algebraMap I.F I.E))))⁻¹ *ᵥ
          fun j => I.φ (w.comap (algebraMap I.F I.E)) (y j)) i) := by
    intro w y
    have hv : Formalism.HermitianLatticesTheory.vecAt (bas I) w y = fun i => σ w (I.φ (w.comap (algebraMap I.F I.E)) (y i)) := by
      funext i
      simp only [Formalism.HermitianLatticesTheory.vecAt, Pi.basisFun_repr]
      exact hσe w (y i)
    unfold Formalism.HermitianLatticesTheory.fcoord
    rw [hσf w, map_inv' (σ w) _ (hMu _), hv]
    exact map_mulVec' (σ w) _ _
  let T' : InfinitePlace I.E → Matrix (Fin I.n) (Fin I.n) ℂ := fun w =>
    ((I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E))))⁻¹ *
      T (w.comap (algebraMap I.F I.E)) *
      (I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E))))).map (σ w)
  have hT'S : ∀ w, ∀ y ∈ S, T' w *ᵥ Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun I.E (Fin I.n)) (frm I x) w y = 0 := by
    intro w y hy
    show T' w *ᵥ Formalism.HermitianLatticesTheory.fcoord (bas I) (frm I x) w y = 0
    rw [hco w y, map_conj_mulVec_map_inv_mulVec _ _ _ (hMu _), hTS _ y hy]
    funext i
    simp
  have hT'A : ∀ w, ∀ y ∈ A, T' w *ᵥ Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun I.E (Fin I.n)) (frm I x) w y ∈
      Submodule.span ℂ (Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun I.E (Fin I.n)) (frm I x) w '' (R : Set (Fin I.n → I.E))) := by
    intro w y hy
    show T' w *ᵥ Formalism.HermitianLatticesTheory.fcoord (bas I) (frm I x) w y ∈
      Submodule.span ℂ (Formalism.HermitianLatticesTheory.fcoord (bas I) (frm I x) w '' (R : Set (Fin I.n → I.E)))
    rw [hco w y, map_conj_mulVec_map_inv_mulVec _ _ _ (hMu _)]
    refine Submodule.span_mono ?_ (map_mulVec_mem_span_image_of_mem_span (σ w) _ _ _ (hTA _ y hy))
    rintro _ ⟨_, ⟨r, hr, rfl⟩, rfl⟩
    exact ⟨r, hr, hco w r⟩
  obtain ⟨Φ, hΦS, hΦA, D', hD', hnorm⟩ := GlobalTheory.T.coveringRadius_hom_subquotient_sublattice I.E I.n (frm I x) A S R lo hi
    (GlobalTheory.Count.FrameMajorant.frm_unit I x) hA hSat hR hlo hhi hsz hlg T' hT'S hT'A
  let wv : InfinitePlace I.F → InfinitePlace I.E := Function.surjInv hbij.2
  have hwv : ∀ w, wv (w.comap (algebraMap I.F I.E)) = w := fun w =>
    hbij.1 (Function.surjInv_eq hbij.2 _)
  refine ⟨Φ, hΦS, hΦA, fun v => (I.P v * uMat (x.1 v)) * (D' (wv v)).map (σ (wv v)) *
    (I.P v * uMat (x.1 v))⁻¹, ?_, ?_⟩
  · intro v
    obtain ⟨w, rfl⟩ := hbij.2 v
    intro u hu
    simp only [hwv]
    unfold spanAt at hu
    induction hu using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨y, hy, rfl⟩ := hz
      have e1 := hD' w y hy
      have hX : (frm I x w)⁻¹ * Φ.map w.embedding * frm I x w =
          ((I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E))))⁻¹ *
            Φ.map (I.φ (w.comap (algebraMap I.F I.E))) *
            (I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E))))).map (σ w) := by
        have hΦ : Φ.map w.embedding = (Φ.map (I.φ (w.comap (algebraMap I.F I.E)))).map (σ w) := by
          ext i j
          simp only [Matrix.map_apply]
          exact hσe w _
        rw [hσf w, map_inv' (σ w) _ (hMu _), hΦ, ← Matrix.map_mul, ← Matrix.map_mul]
      rw [hX] at e1
      change D' w *ᵥ Formalism.HermitianLatticesTheory.fcoord (bas I) (frm I x) w y = _ at e1
      have hsub : T' w - ((I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E))))⁻¹ *
            Φ.map (I.φ (w.comap (algebraMap I.F I.E))) *
            (I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E))))).map (σ w) =
          ((I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E))))⁻¹ *
            (T (w.comap (algebraMap I.F I.E)) - Φ.map (I.φ (w.comap (algebraMap I.F I.E)))) *
            (I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E))))).map (σ w) := by
        rw [Matrix.mul_sub, Matrix.sub_mul]
        ext i j
        simp only [T', Matrix.sub_apply, Matrix.map_apply, map_sub]
      rw [hsub] at e1
      rw [hco w y, map_conj_mulVec_map_inv_mulVec _ _ _ (hMu _)] at e1
      have e2 := isCMExt_apply_apply (σ w) (hσi w) _ _ _ e1
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e2, Matrix.mulVec_mulVec,
        Matrix.mul_nonsing_inv _ (hMu _), Matrix.one_mulVec]
    | zero => simp
    | add a b _ _ ha hb => rw [Matrix.mulVec_add, Matrix.mulVec_add, ha, hb]
    | smul c a _ ha => rw [Matrix.mulVec_smul, Matrix.mulVec_smul, ha]
  · have hterm : ∀ v, Formalism.REAL.hs (uMat (x.1 v)⁻¹ * (I.P v)⁻¹ * ((I.P v * uMat (x.1 v)) *
        (D' (wv v)).map (σ (wv v)) * (I.P v * uMat (x.1 v))⁻¹) * I.P v * uMat (x.1 v)) =
        Formalism.REAL.hs (D' (wv v)) := by
      intro v
      have hu : uMat (x.1 v)⁻¹ = (uMat (x.1 v))⁻¹ := by
        first
          | rfl
          | simp only [Formalism.MainNotions.S.uMat, Subgroup.coe_inv, Matrix.coe_units_inv]
      rw [hu, inv_mul_inv_mul_conj_mul_mul_eq_self _ _ _ (hPu v) (hUu v), hs_map_of_norm_preserving _ (hσn _)]
    have hsum : ∑ v, Formalism.REAL.hs (D' (wv v)) = ∑ w, Formalism.REAL.hs (D' w) :=
      (Fintype.sum_bijective _ hbij (fun w => Formalism.REAL.hs (D' w)) (fun v => Formalism.REAL.hs (D' (wv v)))
        (fun w => by rw [hwv w])).symm
    unfold normAt
    simp only [hterm]
    rw [hsum]
    rw [hnp] at hnorm
    unfold AutInst.rd
    exact hnorm

end GlobalTheory.Count.SubquotFrame
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.GaussDecay

theorem isCMFam_of_over {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (φ : InfinitePlace F → (E →+* ℂ))
    (hφ : ∀ v (a : F), φ v (algebraMap F E a) = v.embedding a) : GlobalTheory.Mem.Vol.IsCMFam φ := by
  obtain ⟨hF, hE, h2, -⟩ := h
  unfold GlobalTheory.Mem.Vol.IsCMFam
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · have key : ∀ v, (InfinitePlace.mk (φ v)).comap (algebraMap F E) = v := by
      intro v
      rw [InfinitePlace.comap_mk, show (φ v).comp (algebraMap F E) = v.embedding from RingHom.ext (hφ v),
        InfinitePlace.mk_embedding]
    intro v w hvw
    rw [← key v, ← key w]
    exact congrArg (fun x : InfinitePlace E => x.comap (algebraMap F E)) hvw
  · have a1 := IsTotallyComplex.finrank E
    have a2 := IsTotallyReal.finrank F
    have a3 := Module.finrank_mul_finrank ℚ F E
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyReal.nrComplexPlaces_eq_zero,
      IsTotallyComplex.nrRealPlaces_eq_zero E]
    rw [h2] at a3
    omega

end GlobalTheory.GaussDecay
end
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

theorem _root_.GlobalTheory.T.isTerm_localTermMove_of_isometry : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ} (g : V ≃ₗ[E] V) (t : Term V M r), IsUnitary H g → H.IsTerm t → H.IsTerm (GlobalTheory.LocOver.move g t) := by
  first | exact @GlobalTheory.LocOver.isTerm_move_of_unitary | exact GlobalTheory.LocOver.isTerm_move_of_unitary | (intros; apply GlobalTheory.LocOver.isTerm_move_of_unitary <;> assumption)
end

section

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

namespace GlobalTheory.LocOver

theorem isTerm_unitary_move {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
    (r : ℕ) (g : V ≃ₗ[E] V) (t : Term V M r) (hg : IsUnitary H g) (ht : H.IsTerm t) :
    H.IsTerm (GlobalTheory.LocOver.move g t) :=
  GlobalTheory.LocOver.MoveTerm.isTerm_move H g t hg ht

end GlobalTheory.LocOver
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

theorem _root_.GlobalTheory.T.frameDual_unipotentGroup_acts_unitriangular_onto : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ Fr : FrameD H r, Fr.T ≠ 0 → (∀ n, n ∈ Fr.N ↔ n ∈ NU H Fr.f) ∧ (∀ n ∈ Fr.N, Tri E Fr.f fun b => n (Fr.f b)) ∧ ∀ g : Fin (r + 1) → V, Tri E Fr.f g → ∃ n ∈ Fr.N, g = fun b => n (Fr.f b) := by
  first | exact @GlobalTheory.LocOver.UnipOnto.unipotent_onto | exact GlobalTheory.LocOver.UnipOnto.unipotent_onto | (intros; apply GlobalTheory.LocOver.UnipOnto.unipotent_onto <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.CoordSum

theorem tsum_reps_eq : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : Coord P S), ∀ (R : LocNG.Reps P) (d0 : LocNG.Datum P), ∃ κ : ℝ, 0 ≤ κ ∧ ∀ φ : S.Datum → ℝ≥0∞, (∀ h ∈ S.H0, ∀ δ, φ (h • δ) = φ δ) → (∀ δ, (¬ ∃ Λ, S.IsTerm δ Λ) → φ δ = 0) → (∑' d : R.RD, ENNReal.ofReal (LocNG.Datum.wt d0 d.1) * φ (c.dat d.1)) = ENNReal.ofReal κ * S.sumData φ := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P S c R d0
  have := hM.loc
  have := hM.char0
  obtain ⟨κ, hκ0, hκ⟩ := GlobalTheory.T.exists_wt_eq_mul_nu' M hM H r k P S c d0
  obtain ⟨-, -, hrel, -, -⟩ := GlobalTheory.HL.CoordDatum.transport M hM H r k P S c
  obtain ⟨-, -, hex⟩ := GlobalTheory.T.isTerm_and_om_eq_of_coord_isTermOver M hM H r k P S c
  refine ⟨κ, hκ0, fun φ hφ hφ0 => ?_⟩

  have hmove : ∀ h ∈ S.H0, ∀ δ : S.Datum, (∃ Λ, S.IsTerm δ Λ) → ∃ Λ, S.IsTerm (h • δ) Λ := by
    rintro h hh δ ⟨Λ, hΛ⟩
    exact ⟨h • Λ, (GlobalTheory.HL.ComplAct.main M.L r k S δ Λ hΛ h hh).1⟩

  have hψ0 : ∀ δ : S.Datum, (¬ ∃ Λ, S.IsTerm δ Λ) → ENNReal.ofReal (S.nu δ) * φ δ = 0 := by
    intro δ hδ
    rw [hφ0 δ hδ, mul_zero]
  have hterm : ∀ d : R.RD, ENNReal.ofReal (LocNG.Datum.wt d0 d.1) * φ (c.dat d.1) =
      ENNReal.ofReal κ * (ENNReal.ofReal (S.nu (c.dat d.1)) * φ (c.dat d.1)) := by
    intro d
    by_cases hd : ∃ Λ, S.IsTerm (c.dat d.1) Λ
    · obtain ⟨Λ, hΛ⟩ := hd
      rw [hκ d.1 Λ hΛ, ENNReal.ofReal_mul hκ0, mul_assoc]
    · rw [hφ0 _ hd, mul_zero, mul_zero, mul_zero]
  rw [tsum_congr hterm, ENNReal.tsum_mul_left]
  congr 1

  let A : Set R.RD := {a | ∃ Λ, S.IsTerm (c.dat a.1) Λ}
  have h1 : ∑' a : A, ENNReal.ofReal (S.nu (c.dat a.1.1)) * φ (c.dat a.1.1) =
      ∑' d : R.RD, ENNReal.ofReal (S.nu (c.dat d.1)) * φ (c.dat d.1) := by
    refine tsum_subtype_eq_of_support_subset (f := fun d : R.RD => ENNReal.ofReal (S.nu (c.dat d.1)) * φ (c.dat d.1)) ?_
    intro a ha
    by_contra hn
    exact ha (hψ0 _ hn)
  have hT : ∀ g : S.H0, ∀ x : S.Datum, (∃ Λ, S.IsTerm x Λ) → ∃ Λ, S.IsTerm (g • x) Λ :=
    fun g x hx => hmove g g.2 x hx
  have hι : ∀ a : A, ∃ Λ, S.IsTerm (c.dat a.1.1) Λ := fun a => a.2
  have hsurj : ∀ x : S.Datum, (∃ Λ, S.IsTerm x Λ) → ∃ a : A, ∃ g : S.H0, g • c.dat a.1.1 = x := by
    intro x hx
    obtain ⟨Λ, hΛ⟩ := hx
    obtain ⟨d, rfl⟩ := hex x Λ hΛ
    obtain ⟨y, hyR, hy⟩ := R.hRD.2.1 d (Set.mem_univ d)
    obtain ⟨h, hh, hhy⟩ := (hrel y d).1 hy
    have hTy : ∃ Λ, S.IsTerm (c.dat y) Λ := by
      have h' := hmove h⁻¹ (S.H0.inv_mem hh) _ ⟨Λ, hΛ⟩
      rwa [← hhy, inv_smul_smul] at h'
    exact ⟨⟨⟨y, hyR⟩, hTy⟩, ⟨h, hh⟩, hhy⟩
  have hinj : ∀ a b : A, (∃ g : S.H0, g • c.dat a.1.1 = c.dat b.1.1) → a = b := by
    rintro a b ⟨g, hg⟩
    have hr : LocNG.Datum.Rel a.1.1 b.1.1 := (hrel _ _).2 ⟨g, g.2, hg⟩
    exact Subtype.ext (Subtype.ext (R.hRD.2.2 _ a.1.2 _ b.1.2 hr))
  have hinv : ∀ g : S.H0, ∀ x : S.Datum, (∃ Λ, S.IsTerm x Λ) →
      ENNReal.ofReal (S.nu (g • x)) * φ (g • x) = ENNReal.ofReal (S.nu x) * φ x := by
    rintro g x ⟨Λ, hΛ⟩
    show ENNReal.ofReal (S.nu ((g : S.GLV) • x)) * φ ((g : S.GLV) • x) = _
    rw [(GlobalTheory.HL.Frames.nu_pos_and_smul M.L r k S x Λ hΛ).2 g g.2, hφ g g.2 x]
  have h2 := (GlobalTheory.tsum_transversal_eq_tsum_orbitQuotient (G := S.H0) (X := S.Datum) (A := A)
    (fun a => c.dat a.1.1) (fun x => ∃ Λ, S.IsTerm x Λ) hT hι hsurj hinj).2
    (fun x => ENNReal.ofReal (S.nu x) * φ x) hinv
  rw [← h1, h2]
  show _ = ∑' o : MulAction.orbitRel.Quotient S.H0 S.Datum, ENNReal.ofReal (S.nu o.out) * φ o.out
  refine tsum_congr fun o => ?_
  split_ifs with ho
  · rfl
  · exact (hψ0 _ ho).symm

end GlobalTheory.HL.CoordSum
end
