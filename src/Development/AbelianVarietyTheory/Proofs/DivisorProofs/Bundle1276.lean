module

public import Mathlib.Data.Matrix.Block
public import Mathlib.Tactic.Continuity
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.FieldTheory.Separable
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle014
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1187
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle093
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedCentralizerIsNormOneTorus
public import ReciprocityTheory.L2DbarEstimates.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1190
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
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle156
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.LatticeStab

variable {A O : Type} [CommRing A] [CommRing O] (ι : O →ₙ+* A) {n : ℕ}

theorem map_mul_of_nonUnital {m : Type} [Fintype m] (G H : Matrix m m O) :
    (G * H).map ι = G.map ι * H.map ι := by
  ext i j

  simp [Matrix.mul_apply, map_sum, map_mul]

theorem exists_matrix_of_keeps (P : Matrix (Fin n) (Fin n) A) (Λ : Set (Fin n → A))
    (hP : ι 1 • P = P)
    (hΛ : ∀ z, z ∈ Λ ↔ ∃ a : Fin n → O, z = P *ᵥ fun i => ι (a i))
    (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) A)
    (hM : ∀ z : Fin n ⊕ Fin n → A, z ∘ Sum.inl ∈ Λ → z ∘ Sum.inr ∈ Λ →
      (M *ᵥ z) ∘ Sum.inl ∈ Λ ∧ (M *ᵥ z) ∘ Sum.inr ∈ Λ) :
    ∃ G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O,
      M * Matrix.fromBlocks P 0 0 P = Matrix.fromBlocks P 0 0 P * G.map ι := by
  have h0 : (0 : Fin n → A) ∈ Λ :=
    (hΛ 0).2 ⟨0, by ext i; simp [Matrix.mulVec, dotProduct]⟩
  have hcol : ∀ k : Fin n, (fun r => P r k) ∈ Λ := by
    intro k
    refine (hΛ _).2 ⟨Pi.single k 1, ?_⟩
    ext r
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single k]
    · have := congrFun (congrFun hP r) k
      simp only [Matrix.smul_apply, smul_eq_mul] at this
      simp only [Pi.single_eq_same]
      rw [mul_comm]; exact this.symm
    · intro b _ hb; simp [Pi.single_eq_of_ne hb]
    · simp
  have hDcol : ∀ j, (fun k => Matrix.fromBlocks P 0 0 P k j) ∘ Sum.inl ∈ Λ ∧
      (fun k => Matrix.fromBlocks P 0 0 P k j) ∘ Sum.inr ∈ Λ := by
    intro j
    rcases j with k | k
    · have e1 : (fun k' => Matrix.fromBlocks P 0 0 P k' (Sum.inl k)) ∘ Sum.inl = fun r => P r k := by
        ext r; simp
      have e2 : (fun k' => Matrix.fromBlocks P 0 0 P k' (Sum.inl k)) ∘ Sum.inr = 0 := by
        ext r; simp
      rw [e1, e2]; exact ⟨hcol k, h0⟩
    · have e1 : (fun k' => Matrix.fromBlocks P 0 0 P k' (Sum.inr k)) ∘ Sum.inl = 0 := by
        ext r; simp
      have e2 : (fun k' => Matrix.fromBlocks P 0 0 P k' (Sum.inr k)) ∘ Sum.inr = fun r => P r k := by
        ext r; simp
      rw [e1, e2]; exact ⟨h0, hcol k⟩
  have ex : ∀ j, ∃ a b : Fin n → O,
      (M *ᵥ fun k => Matrix.fromBlocks P 0 0 P k j) ∘ Sum.inl = P *ᵥ (fun i => ι (a i)) ∧
      (M *ᵥ fun k => Matrix.fromBlocks P 0 0 P k j) ∘ Sum.inr = P *ᵥ (fun i => ι (b i)) := by
    intro j
    obtain ⟨h1, h2⟩ := hM _ (hDcol j).1 (hDcol j).2
    obtain ⟨a, ha⟩ := (hΛ _).1 h1
    obtain ⟨b, hb⟩ := (hΛ _).1 h2
    exact ⟨a, b, ha, hb⟩
  choose a b hab using ex
  refine ⟨Matrix.of fun i j => Sum.elim (a j) (b j) i, ?_⟩
  ext i j
  have hMD : (M * Matrix.fromBlocks P 0 0 P) i j = (M *ᵥ fun k => Matrix.fromBlocks P 0 0 P k j) i := rfl
  rw [hMD]
  rcases i with r | r
  · have := congrFun (hab j).1 r
    simp only [Function.comp] at this
    rw [this]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
  · have := congrFun (hab j).2 r
    simp only [Function.comp] at this
    rw [this]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]

end GlobalTheory.LatticeStab

theorem GlobalTheory.LatticeStab.matrix_in_diag_basis : ∀ (A O : Type) [CommRing A] [CommRing O] (ι : O →ₙ+* A) (n : ℕ) (P Q : Matrix (Fin n) (Fin n) A)
    (Λ : Set (Fin n → A)), Function.Injective ι → P * Q = ι 1 • (1 : Matrix (Fin n) (Fin n) A) →
    Q * P = ι 1 • (1 : Matrix (Fin n) (Fin n) A) → ι 1 • P = P → ι 1 • Q = Q →
    (∀ z, z ∈ Λ ↔ ∃ a : Fin n → O, z = P *ᵥ fun i => ι (a i)) →
    ∀ M M' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) A, M * M' = 1 →
    (∀ z : Fin n ⊕ Fin n → A, z ∘ Sum.inl ∈ Λ → z ∘ Sum.inr ∈ Λ →
      (M *ᵥ z) ∘ Sum.inl ∈ Λ ∧ (M *ᵥ z) ∘ Sum.inr ∈ Λ ∧ (M' *ᵥ z) ∘ Sum.inl ∈ Λ ∧ (M' *ᵥ z) ∘ Sum.inr ∈ Λ) →
    ∃ G G' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O, G * G' = 1 ∧
      M * Matrix.fromBlocks P 0 0 P = Matrix.fromBlocks P 0 0 P * G.map ι := by
  intro A O _ _ ι n P Q Λ hinj _hPQ hQP hP _hQ hΛ M M' hMM' hM
  obtain ⟨G, hG⟩ := GlobalTheory.LatticeStab.exists_matrix_of_keeps ι P Λ hP hΛ M
    (fun z h1 h2 => ⟨(hM z h1 h2).1, (hM z h1 h2).2.1⟩)
  obtain ⟨G', hG'⟩ := GlobalTheory.LatticeStab.exists_matrix_of_keeps ι P Λ hP hΛ M'
    (fun z h1 h2 => ⟨(hM z h1 h2).2.2.1, (hM z h1 h2).2.2.2⟩)
  refine ⟨G, G', ?_, hG⟩
  have hDD : Matrix.fromBlocks P 0 0 P * (G * G').map ι = Matrix.fromBlocks P 0 0 P := by
    rw [GlobalTheory.LatticeStab.map_mul_of_nonUnital, ← Matrix.mul_assoc, ← hG, Matrix.mul_assoc, ← hG',
      ← Matrix.mul_assoc, hMM', Matrix.one_mul]
  have hQD : Matrix.fromBlocks Q 0 0 Q * Matrix.fromBlocks P 0 0 P =
      ι 1 • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) A) := by
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, Matrix.fromBlocks_multiply]
    simp [hQP]
  have key : ι 1 • (G * G').map ι = ι 1 • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) A) := by
    have := congrArg (fun X => Matrix.fromBlocks Q 0 0 Q * X) hDD
    simp only [← Matrix.mul_assoc, hQD] at this
    rwa [Matrix.smul_mul, Matrix.one_mul] at this
  ext i j
  apply hinj
  have := congrFun (congrFun key i) j
  simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, ← map_mul, one_mul] at this
  rw [this]
  by_cases h : i = j <;> simp [Matrix.one_apply, h]
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem GlobalTheory.HermBlockChange.exists_unit_lower_block : ∀ (O : Type) [CommRing O] (c : O →+* O), IsUnit (2 : O) →
    (∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) O), (∀ i j, c (J j i) = J i j) → IsUnit J.det →
      ∀ g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O, IsUnit g.det →
        gᵀ * Matrix.fromBlocks 0 J J 0 * g.map c = Matrix.fromBlocks 0 J J 0 →
        ∃ Z : Matrix (Fin n) (Fin n) O, Zᵀ * J + J * Z.map c = 0 ∧ IsUnit (g.toBlocks₂₁ * Z + g.toBlocks₂₂).det) →
    ∀ (n : ℕ) (JL : Matrix (Fin n) (Fin n) O) (G G' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O),
    (∀ i j, c (JL j i) = JL i j) → IsUnit JL.det → G * G' = 1 →
    Gᵀ * Matrix.fromBlocks JL 0 0 (-JL) * G.map c = Matrix.fromBlocks JL 0 0 (-JL) →
    ∃ Z : Matrix (Fin n) (Fin n) O, Zᵀ * JL + JL * Z.map c = 0 ∧
      IsUnit (((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O))ᵀ : Matrix (Fin n) (Fin n ⊕ Fin n) O) * G * (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O) : Matrix (Fin n ⊕ Fin n) (Fin n) O) +
        ((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O))ᵀ : Matrix (Fin n) (Fin n ⊕ Fin n) O) * G * (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (1 : Matrix (Fin n) (Fin n) O) : Matrix (Fin n ⊕ Fin n) (Fin n) O) * Z).det := by
  intro O _ c h2 hcore n JL G G' hJL hdet hGG' hG
  obtain ⟨a, ha⟩ : ∃ a : O, a * 2 = 1 := ⟨↑(h2.unit⁻¹), by simp⟩
  have ha' : (2 : O) * a = 1 := by rw [mul_comm, ha]
  have hca : c a = a := by
    have h1 : c a * 2 = 1 := by
      have := congrArg c ha
      rwa [map_mul, map_one, map_ofNat] at this
    calc c a = c a * (2 * a) := by rw [ha', mul_one]
      _ = (c a * 2) * a := by ring
      _ = a := by rw [h1, one_mul]
  set Δ : Matrix (Fin n ⊕ Fin n) (Fin n) O := Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) 1 with hΔ
  set Nb : Matrix (Fin n ⊕ Fin n) (Fin n) O := Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1) with hNb
  set T : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O := Matrix.fromCols Δ Nb with hTdef
  have hT : T = Matrix.fromBlocks 1 1 1 (-1) := by
    ext i j; rcases i with i | i <;> rcases j with j | j <;> simp [T, Δ, Nb]
  have hTt : Tᵀ = T := by
    rw [hT, Matrix.fromBlocks_transpose]; simp
  have hTc : T.map c = T := by
    rw [hT, Matrix.fromBlocks_map]; simp
    ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]
  have hTT : T * T = (2 : O) • 1 := by
    rw [hT, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_smul]
    simp [two_smul]
  set J : Matrix (Fin n) (Fin n) O := (2 : O) • JL with hJ
  set K : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O := Matrix.fromBlocks 0 J J 0 with hK
  set D : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O := Matrix.fromBlocks JL 0 0 (-JL) with hD
  have hTKT : T * K * T = (4 : O) • D := by
    rw [hT, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_smul]
    simp [J]
    exact ⟨by rw [← add_smul]; norm_num, by rw [← neg_add, ← add_smul]; norm_num⟩
  have hTDT : T * D * T = K := by
    rw [hT, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp [K, J, two_smul]
  have h4 : a * a * 4 = (1 : O) := by linear_combination (2 * a + 1) * ha
  set g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O := a • (Tᵀ * G * T) with hg
  have hmapsmul : ∀ (b : O) (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O), (b • M).map c = c b • M.map c := by
    intro b M; ext i j; simp
  have hgt : gᵀ = a • (T * Gᵀ * T) := by
    simp only [hg, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_transpose, hTt, Matrix.mul_assoc]
  have hgc : g.map c = a • (T * G.map c * T) := by
    rw [hg, hTt, hmapsmul, Matrix.map_mul, Matrix.map_mul, hTc, hca]
  have hgK : gᵀ * K * g.map c = K := by
    rw [hgt, hgc]
    calc a • (T * Gᵀ * T) * K * a • (T * G.map c * T)
        = (a * a) • (T * Gᵀ * (T * K * T) * G.map c * T) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
      _ = (a * a * 4) • (T * (Gᵀ * D * G.map c) * T) := by
          rw [hTKT]; simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
      _ = K := by rw [hG, h4, one_smul, hTDT]
  have hgdet : g * (a • (T * G' * T)) = 1 := by
    rw [hg, hTt]
    calc a • (T * G * T) * a • (T * G' * T)
        = (a * a) • (T * G * (T * T) * G' * T) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
      _ = (a * a * 2) • (T * (G * G') * T) := by
          rw [hTT]; simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, Matrix.one_mul]
      _ = 1 := by
          rw [hGG', Matrix.mul_one, hTT, smul_smul, show a * a * 2 * 2 = (1 : O) by linear_combination (2 * a + 1) * ha, one_smul]
  have hJherm : ∀ i j, c (J j i) = J i j := by intro i j; simp only [J, Matrix.smul_apply, smul_eq_mul, map_mul, map_ofNat, hJL]
  have hJdet : IsUnit J.det := by
    rw [hJ, Matrix.det_smul]; exact (h2.pow _).mul hdet
  obtain ⟨Z, hZ1, hZ2⟩ := hcore n J hJherm hJdet g (Matrix.isUnit_det_of_right_inverse hgdet) hgK
  refine ⟨Z, ?_, ?_⟩
  · have h := congrArg (fun M => a • M) hZ1
    simp only [J, Matrix.mul_smul, Matrix.smul_mul, ← smul_add, smul_smul, ha, one_smul, smul_zero] at h
    exact h
  · have hblk : Tᵀ * G * T = Matrix.fromBlocks (Δᵀ * G * Δ) (Δᵀ * G * Nb) (Nbᵀ * G * Δ) (Nbᵀ * G * Nb) := by
      rw [hTdef, Matrix.transpose_fromCols, Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols]
    have h21 : g.toBlocks₂₁ = a • (Nbᵀ * G * Δ) := by
      rw [hg, hblk, Matrix.fromBlocks_smul, Matrix.toBlocks_fromBlocks₂₁]
    have h22 : g.toBlocks₂₂ = a • (Nbᵀ * G * Nb) := by
      rw [hg, hblk, Matrix.fromBlocks_smul, Matrix.toBlocks_fromBlocks₂₂]
    have hE : Nbᵀ * G * Nb + Nbᵀ * G * Δ * Z = (2 : O) • (g.toBlocks₂₁ * Z + g.toBlocks₂₂) := by
      rw [h21, h22, Matrix.smul_mul, ← smul_add, smul_smul, ha', one_smul, add_comm]
    rw [hE, Matrix.det_smul]; exact (h2.pow _).mul hZ2
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TraceGram

theorem det_trace_pow_gram_ne_zero {K : Type} [Field K] {n : ℕ} (g : Matrix (Fin n) (Fin n) K)
    (hg : g.charpoly.Separable) :
    (Matrix.of fun i j : Fin n => (g ^ ((i : ℕ) + j)).trace).det ≠ 0 := by
  set L := AlgebraicClosure K
  set f : K →+* L := algebraMap K L
  set M : Matrix (Fin n) (Fin n) L := g.map f
  have hMc : M.charpoly = g.charpoly.map f := Matrix.charpoly_map g f
  have hnd : M.charpoly.roots.Nodup := by
    rw [hMc]; exact nodup_roots (hg.map)
  have hcard : M.charpoly.roots.toFinset.card = n := by
    rw [Multiset.toFinset_card_of_nodup hnd, GlobalTheory.CharpolyPow.card_roots_charpoly]
  set s := M.charpoly.roots.toFinset
  let e : Fin n ≃ s := (Fin.castOrderIso hcard.symm).toEquiv.trans s.equivFin.symm
  let v : Fin n → L := fun i => (e i : L)
  have hv : Function.Injective v := fun a b h => e.injective (Subtype.ext h)
  have hsum : ∀ φ : L → L, (M.charpoly.roots.map φ).sum = ∑ i, φ (v i) := by
    intro φ
    have : M.charpoly.roots = s.val := by
      simp [s, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnd]
    rw [this, ← Finset.sum_eq_multiset_sum, ← Finset.sum_coe_sort s]
    exact (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm
  have htr : ∀ m : ℕ, f (g ^ m).trace = ∑ i, v i ^ m := by
    intro m
    have h1 : f (g ^ m).trace = (M ^ m).trace := by
      have hp : M ^ m = (g ^ m).map f := by simp [M, Matrix.map_pow]

      rw [hp]; simp [Matrix.trace, Matrix.map_apply, map_sum]
    rw [h1, Matrix.trace_eq_sum_roots_charpoly, GlobalTheory.CharpolyPow.roots_charpoly_pow, hsum]
  have hG : (Matrix.of fun i j : Fin n => (g ^ ((i : ℕ) + j)).trace).map f
      = (vandermonde v)ᵀ * vandermonde v := by
    ext i j
    rw [vandermonde_transpose_mul_vandermonde, Matrix.map_apply, Matrix.of_apply, htr]
  intro h0
  have hd := RingHom.map_det f (Matrix.of fun i j : Fin n => (g ^ ((i : ℕ) + j)).trace)
  rw [h0, map_zero] at hd
  have h2 : ((vandermonde v)ᵀ * vandermonde v).det = 0 := by
    rw [← hG]; exact hd.symm
  rw [det_mul, det_transpose, mul_self_eq_zero] at h2
  exact det_vandermonde_ne_zero_iff.mpr hv h2

end GlobalTheory.TraceGram
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SepCommutant

theorem exists_eq_sum_pow_of_commute :
    ∀ {K : Type} [Field K] {n : ℕ} (g t : Matrix (Fin n) (Fin n) K), g.charpoly.Separable →
    t * g = g * t → ∃ c : Fin n → K, t = ∑ i, c i • g ^ (i : ℕ) := by
  intro K _ n g t hs hc
  have hm := GlobalTheory.Tw.CentralizerAdjoin.mem_adjoin_of_commute g t hs hc
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hm
  obtain ⟨p, rfl⟩ := hm
  set r := p %ₘ g.charpoly with hr
  have hmon : g.charpoly.Monic := Matrix.charpoly_monic g
  have hae : aeval g p = aeval g r := by
    exact (Polynomial.aeval_modByMonic_eq_self_of_root (Matrix.aeval_self_charpoly g)).symm
  have hdeg : r.degree < n := by
    have := Polynomial.degree_modByMonic_lt p hmon
    rwa [Matrix.charpoly_degree_eq_dim, Fintype.card_fin] at this
  refine ⟨fun i => r.coeff i, ?_⟩
  change aeval g p = _
  rw [hae, aeval_def, eval₂_eq_sum, ← Polynomial.sum_fin (fun e a => algebraMap K (Matrix (Fin n) (Fin n) K) a * g ^ e) (by simp) hdeg]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def]

end GlobalTheory.SepCommutant
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem resultant_ne_zero_of_separable_mul :
    ∀ (k : Type) [Field k] (P Q : k[X]), P.Monic → Q.Monic → (P * Q).Separable →
      resultant P Q ≠ 0 := by
  intro k _ P Q _ _ h
  exact Polynomial.resultant_ne_zero P Q h.isCoprime

end GlobalTheory
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb

namespace GlobalTheory

theorem relIndex_eq_of_mulEquiv_subgroup : ∀ (G H : Type) [Group G] [Group H] (T : Subgroup G) (S : Subgroup H) (τ : T ≃* S) (A₁ A₂ : Subgroup G) (B₁ B₂ : Subgroup H), A₁ ≤ T → A₂ ≤ T → (∀ t : T, (t : G) ∈ A₁ ↔ ((τ t : S) : H) ∈ B₁) → (∀ t : T, (t : G) ∈ A₂ ↔ ((τ t : S) : H) ∈ B₂) → A₁.relIndex A₂ = (B₁ ⊓ S).relIndex (B₂ ⊓ S) := by
  intro G H _ _ T S τ A₁ A₂ B₁ B₂ h₁ h₂ e₁ e₂
  have key : ∀ (A : Subgroup G) (B : Subgroup H), (∀ t : T, (t : G) ∈ A ↔ ((τ t : S) : H) ∈ B) →
      (A.subgroupOf T).map τ.toMonoidHom = (B ⊓ S).subgroupOf S := by
    intro A B e
    ext s
    rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, e]
    simp
  rw [← Subgroup.relIndex_subgroupOf h₂, ← Subgroup.relIndex_subgroupOf (inf_le_right : B₂ ⊓ S ≤ S),
    ← key A₁ B₁ e₁, ← key A₂ B₂ e₂,
    Subgroup.relIndex_map_map_of_injective _ _ τ.injective]

end GlobalTheory
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem relIndex_ne_zero_of_isOpen_le_isCompact {H : Type} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] (K U : Subgroup H) (hK : IsCompact (K : Set H))
    (hU : IsOpen (U : Set H)) (_hUK : U ≤ K) : U.relIndex K ≠ 0 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hO : IsOpen ((U.subgroupOf K : Subgroup K) : Set K) :=
    hU.preimage continuous_subtype_val
  haveI : Finite (K ⧸ U.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ hO
  exact Subgroup.index_ne_zero_of_finite

end GlobalTheory
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

theorem _root_.GlobalTheory.T.lintegral_inv_pow_add_normSq_complexSpace : ∀ (n m : ℕ) (a : ℝ), 0 < a → ∫⁻ v : Fin n → ℂ, ENNReal.ofReal (((a + ∑ i, ‖v i‖ ^ 2) ^ (n + m + 1))⁻¹) = ENNReal.ofReal (Real.pi ^ n * m.factorial / ((n + m).factorial * a ^ (m + 1))) := by
  first | exact @GlobalTheory.ComplexSpaceIntegral.lintegral_inv_pow_add_sum_norm_sq | exact GlobalTheory.ComplexSpaceIntegral.lintegral_inv_pow_add_sum_norm_sq | (intros; apply GlobalTheory.ComplexSpaceIntegral.lintegral_inv_pow_add_sum_norm_sq <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.entry_mem_subring_of_trace_gram_unit : ∀ {K : Type} [Field K] (O : Subring K) {n : ℕ} (g x : Matrix (Fin n) (Fin n) K) (c : Fin n → K),
    x = ∑ i, c i • g ^ (i : ℕ) → (∀ i j, g i j ∈ O) → (∀ j : Fin n, (x * g ^ (j : ℕ)).trace ∈ O) →
    (Matrix.of fun i j : Fin n => (g ^ ((i : ℕ) + j)).trace).det ≠ 0 →
    ((Matrix.of fun i j : Fin n => (g ^ ((i : ℕ) + j)).trace).det)⁻¹ ∈ O → ∀ i j, x i j ∈ O := by
  first | exact @GlobalTheory.TraceGram.entry_mem_of_trace_gram | exact GlobalTheory.TraceGram.entry_mem_of_trace_gram | (intros; apply GlobalTheory.TraceGram.entry_mem_of_trace_gram <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun MeasureTheory Topology
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem haar_exists_matrix_local_field : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {a d : ℕ},
    ∃ ν : @Measure (Matrix (Fin a) (Fin d) k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν := by
  intro k _ _ _ _ a d
  letI : MeasurableSpace (Matrix (Fin a) (Fin d) k) := borel _
  haveI : BorelSpace (Matrix (Fin a) (Fin d) k) := ⟨rfl⟩
  haveI : LocallyCompactSpace (Matrix (Fin a) (Fin d) k) :=
    inferInstanceAs (LocallyCompactSpace (Fin a → Fin d → k))
  exact ⟨Measure.addHaar, inferInstance⟩

end GlobalTheory
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

theorem _root_.GlobalTheory.T.det_complexHessian_fubiniStudy_potential : ∀ (n : ℕ) (v : ReciprocityTheory.L2DbarEstimates.V n), (ReciprocityTheory.L2DbarEstimates.cHess n (fun w => (Real.log (1 + ‖w‖ ^ 2) : ℂ)) v).det.re = ((1 + ‖v‖ ^ 2) ^ (n + 1))⁻¹ := by
  first | exact @GlobalTheory.FSDet.det_fubiniStudy_hess | exact GlobalTheory.FSDet.det_fubiniStudy_hess | (intros; apply GlobalTheory.FSDet.det_fubiniStudy_hess <;> assumption)
end
