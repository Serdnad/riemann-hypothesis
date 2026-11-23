module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle008
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle018
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle022
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle020
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.BB

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

section CoordMap

theorem map_curry_symm_pi {R : Type} [MeasurableSpace R] (lam : Measure R) [SigmaFinite lam]
    (M d : ℕ) :
    (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin d => lam).map
        (MeasurableEquiv.curry (Fin M) (Fin d) R).symm =
      Measure.pi fun _ : Fin M × Fin d => lam := by
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [(MeasurableEquiv.curry (Fin M) (Fin d) R).symm.map_apply]
  have hpre : (MeasurableEquiv.curry (Fin M) (Fin d) R).symm ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ fun i : Fin M => Set.pi Set.univ fun k : Fin d => s (i, k) := by
    ext x
    simp [MeasurableEquiv.curry, Set.mem_pi, Prod.forall, Function.uncurry]
  rw [hpre, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  rw [Fintype.prod_prod_type]

theorem coordK_eq_map {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R]
    [Algebra F R] [TopologicalSpace R] [MeasurableSpace R]
    {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R)
    (e : R ⊗[F] E ≃ᵐ (Fin d → R))
    (he : ∀ y k, e y k = (Algebra.TensorProduct.basis R b).repr y k) :
    coordK R b lam = (Measure.pi fun _ => lam).map e.symm := by
  rw [MeasurableEquiv.map_symm]
  have : (e : R ⊗[F] E → Fin d → R) =
      fun (y : R ⊗[F] E) (k : Fin d) => (Algebra.TensorProduct.basis R b).repr y k := by
    funext y k; exact he y k
  rw [coordK, this]

theorem coordMap_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ M : ℕ, IsHomeomorph (fun X : Fin 1 → Fin M → R ⊗[F] E => cv R b (X 0)) ∧ MeasurableEmbedding (fun X : Fin 1 → Fin M → R ⊗[F] E => cv R b (X 0)) ∧ (coordW R b lam 1 M).map (fun X : Fin 1 → Fin M → R ⊗[F] E => cv R b (X 0)) = Measure.pi fun _ : Fin M × Fin d => lam := by
  intro F E _ _ _ _ _ σ hσ R _ _ _ _ _ _ _ _ _ d b lam hlam M
  obtain ⟨-, -, -, -, -, -, hh, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  haveI := hlam
  have hSF : SigmaFinite lam := inferInstance
  let e : R ⊗[F] E ≃ₜ (Fin d → R) := (hh d b).homeomorph _
  let em : R ⊗[F] E ≃ᵐ (Fin d → R) := e.toMeasurableEquiv
  have hem : ∀ y k, em y k = (Algebra.TensorProduct.basis R b).repr y k := fun _ _ => rfl
  have hK : coordK R b lam = (Measure.pi fun _ => lam).map em.symm := coordK_eq_map b lam em hem
  haveI : SigmaFinite (coordK R b lam) := by
    rw [hK]; exact em.symm.measurableEmbedding.sigmaFinite_map
  have hmp : MeasurePreserving em (coordK R b lam) (Measure.pi fun _ : Fin d => lam) :=
    ⟨em.measurable, by rw [hK]; exact MeasurableEquiv.map_map_symm em⟩
  let Φ : (Fin 1 → Fin M → R ⊗[F] E) ≃ᵐ (Fin M × Fin d → R) :=
    (MeasurableEquiv.funUnique (Fin 1) (Fin M → R ⊗[F] E)).trans
      ((MeasurableEquiv.piCongrRight fun _ : Fin M => em).trans
        (MeasurableEquiv.curry (Fin M) (Fin d) R).symm)
  have hΦ : (fun X : Fin 1 → Fin M → R ⊗[F] E => cv R b (X 0)) = Φ := rfl
  have hsymm : (Φ.symm : (Fin M × Fin d → R) → Fin 1 → Fin M → R ⊗[F] E) =
      fun x _ i => e.symm fun k => x (i, k) := rfl
  have hc1 : Continuous (Φ : (Fin 1 → Fin M → R ⊗[F] E) → Fin M × Fin d → R) := by
    rw [← hΦ]
    refine continuous_pi fun p => ?_
    exact (continuous_apply p.2).comp
      (e.continuous.comp ((continuous_apply p.1).comp (continuous_apply 0)))
  have hc2 : Continuous (Φ.symm : (Fin M × Fin d → R) → Fin 1 → Fin M → R ⊗[F] E) := by
    rw [hsymm]
    refine continuous_pi fun _ => continuous_pi fun i => e.symm.continuous.comp ?_
    exact continuous_pi fun k => continuous_apply _
  let Ψ : (Fin 1 → Fin M → R ⊗[F] E) ≃ₜ (Fin M × Fin d → R) :=
    { Φ.toEquiv with continuous_toFun := hc1, continuous_invFun := hc2 }
  refine ⟨Ψ.isHomeomorph, Φ.measurableEmbedding, ?_⟩
  have s1 := measurePreserving_funUnique (Measure.pi fun _ : Fin M => coordK R b lam) (Fin 1)
  have s2 := measurePreserving_pi (fun _ : Fin M => coordK R b lam)
    (fun _ : Fin M => Measure.pi fun _ : Fin d => lam) (fun _ => hmp)
  have h12 := s2.comp s1
  rw [hΦ, ← map_curry_symm_pi lam M d, ← h12.map_eq,
    Measure.map_map (MeasurableEquiv.curry (Fin M) (Fin d) R).symm.measurable h12.measurable]
  rfl

end CoordMap

end GlobalTheory.CompanionTheory.SW.BB
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.StageValue

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem one_tmul_algebraMap (t : F) :
    (1 : R) ⊗ₜ[F] (algebraMap F E t) = (algebraMap F R t) ⊗ₜ[F] (1 : E) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
    TensorProduct.smul_tmul']

theorem corner_half_trace_eq_of_pure_tensor [CharZero F] (hfr : Module.finrank F E = 2) {n : ℕ}
    (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) {x : R}
    (h : S 0 0 = x ⊗ₜ[F] (1 : E)) : s0 R S = x := by
  have hfin : Module.Finite F E := Module.finite_of_finrank_eq_succ hfr
  let b : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E hfr
  have htr : Algebra.trace R (R ⊗[F] E) (x ⊗ₜ[F] (1 : E)) = 2 * x := by
    have h1 := Algebra.trace_algebraMap_of_basis (Algebra.TensorProduct.basis R b) x
    rw [Algebra.TensorProduct.algebraMap_apply] at h1
    simpa [two_mul, two_nsmul] using h1
  have h2 : algebraMap F R (1 / 2) * 2 = 1 := by
    calc algebraMap F R (1 / 2) * 2 = algebraMap F R (1 / 2) * algebraMap F R 2 := by rw [map_ofNat]
      _ = algebraMap F R (1 / 2 * 2) := (map_mul _ _ _).symm
      _ = 1 := by rw [show (1 / 2 * 2 : F) = 1 by norm_num, map_one]
  unfold s0
  rw [h, htr, ← mul_assoc, h2, one_mul]

theorem vec_one_zero {M n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) :
    vec ((1 : R) ⊗ₜ[F] (1 : E)) (0 : Fin n → R ⊗[F] E) X = consTup X := by
  rw [← Algebra.TensorProduct.one_def]
  rfl

end Alg

section Main

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) (t : F) (a : R → Rˣ) {n : ℕ}

theorem corner_half_trace_block_one [CharZero F] (hfr : Module.finrank F E = 2) (T : Matrix (Fin n) (Fin n) E) :
    s0 R ((blockOne (algebraMap F E t) T).map (inclR (F := F) R)) = algebraMap F R t := by
  apply corner_half_trace_eq_of_pure_tensor R hfr
  rw [← one_tmul_algebraMap]
  rfl

theorem cvec_block (T : Matrix (Fin n) (Fin n) E) :
    cvec R t a ((blockOne (algebraMap F E t) T).map (inclR R)) = 0 := by
  funext j
  simp [cvec, blockOne]

theorem schurM_block (T : Matrix (Fin n) (Fin n) E) :
    schurM R σ t a ((blockOne (algebraMap F E t) T).map (inclR R)) = T.map (inclR R) := by
  ext i j
  have hc := cvec_block R t a T
  simp only [schurM, hc, Pi.zero_apply, map_zero, zero_mul, sub_zero]
  simp [blockOne]

theorem schur_block (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b)
    (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b) :
    schur R σ t a (hermOf R σ _ hT') = hermOf R σ T hT := by
  apply Subtype.ext
  have hm : schurM R σ t a ((hermOf R σ _ hT' : HermR R σ (n + 1)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ HermR R σ n := by
    show schurM R σ t a ((blockOne (algebraMap F E t) T).map (inclR R)) ∈ HermR R σ n
    rw [schurM_block]
    exact map_mem_HermR R σ T hT
  rw [schur_coe R σ t a _ hm]
  exact schurM_block R σ t a T

theorem isUnit_det_map (T : Matrix (Fin n) (Fin n) E) (hdet : T.det ≠ 0) :
    IsUnit (T.map (inclR (F := F) R)).det := by
  have h := (IsUnit.mk0 _ hdet).map (inclR (F := F) R)
  rw [RingHom.map_det] at h
  exact h

end Main

theorem family_at_block : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → ∀ (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b), hermOf R σ _ hT' ∈ (Bset R σ t a B₀ : Set (HermR R σ (n + 1))) ∧ fibS σ J t m₁ m' s B₀ a κ₁ cm (hermOf R σ _ hT') = cm 1 ^ n • ((m₁ (hermScal R σ (algebraMap F R t))).prod (m' (hermOf R σ T hT))).map (fun p => actW R σ _ (s p.1) (consTup p.2)) := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D T hT hdet hT'
  have hfr : Module.finrank F E = 2 := D.hCM.2.2.1
  have hs0 : s0 R ((hermOf R σ _ hT' : HermR R σ (n + 1)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) = algebraMap F R t :=
    corner_half_trace_block_one R t hfr T
  have hsch := schur_block R σ t a T hT hT'
  have hmem : hermOf R σ _ hT' ∈ (Bset R σ t a B₀ : Set (HermR R σ (n + 1))) := by
    refine ⟨by rw [hs0]; exact D.htB, ?_⟩
    rw [hsch]
    exact isUnit_det_map R T hdet
  refine ⟨hmem, ?_⟩
  have hc : cvec R t a ((hermOf R σ _ hT' : HermR R σ (n + 1)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) = 0 := cvec_block R t a T
  unfold fibS
  rw [Set.indicator_of_mem hmem]
  simp only [hs0, D.ha1, hsch, hc, D.hκ1, one_mul, Units.val_one, vec_one_zero]

end GlobalTheory.CompanionTheory.SW.StageValue
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂.BsetUnit

theorem det_eq_corner_mul {K : Type} [CommRing K] {n : ℕ} (S : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (w : K) (hw : S 0 0 * w = 1) :
    S.det = S 0 0 *
      (Matrix.of fun i j : Fin n => S i.succ j.succ - S i.succ 0 * w * S 0 j.succ).det := by
  let e : Unit ⊕ Fin n ≃ Fin (n + 1) :=
    { toFun := Sum.elim (fun _ => 0) Fin.succ
      invFun := fun i => Fin.cases (Sum.inl ()) Sum.inr i
      left_inv := by rintro (_ | j) <;> simp
      right_inv := by intro i; refine Fin.cases ?_ ?_ i <;> simp }
  have h1 : S.det = (S.submatrix e e).det := (Matrix.det_submatrix_equiv_self e S).symm
  let A : Matrix Unit Unit K := fun _ _ => S 0 0
  let B : Matrix Unit (Fin n) K := fun _ j => S 0 j.succ
  let C : Matrix (Fin n) Unit K := fun i _ => S i.succ 0
  let D : Matrix (Fin n) (Fin n) K := fun i j => S i.succ j.succ
  let Wm : Matrix Unit Unit K := fun _ _ => w
  have h2 : S.submatrix e e = Matrix.fromBlocks A B C D := by
    ext (_ | i) (_ | j) <;> rfl
  letI : Invertible A :=
    ⟨Wm, by ext i j; rw [Matrix.mul_apply]; simp [A, Wm]; rw [mul_comm]; exact hw,
      by ext i j; rw [Matrix.mul_apply]; simp [A, Wm, hw]⟩
  have hA : A.det = S 0 0 := by rw [Matrix.det_unique]
  have hD : D - C * ⅟A * B =
      Matrix.of fun i j : Fin n => S i.succ j.succ - S i.succ 0 * w * S 0 j.succ := by
    have hinv : ⅟A = Wm := rfl
    ext i j
    rw [hinv, Matrix.sub_apply, Matrix.mul_apply]
    simp only [Finset.univ_unique, Finset.sum_singleton, Matrix.mul_apply, Matrix.of_apply]
    simp [C, B, D, Wm]
  rw [h1, h2, Matrix.det_fromBlocks₁₁, hA, hD]

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]

theorem half_trace_tmul (h2F : (2 : F) ≠ 0) (b : Module.Basis (Fin 2) F E) (r : R) :
    algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (r ⊗ₜ[F] (1 : E)) = r := by
  have h : (r ⊗ₜ[F] (1 : E) : R ⊗[F] E) = algebraMap R (R ⊗[F] E) r := by
    simp [Algebra.TensorProduct.algebraMap_apply]
  rw [h, Algebra.trace_algebraMap_of_basis (Algebra.TensorProduct.basis R b)]
  have h2 : algebraMap F R (1 / 2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap F R) 2, ← map_mul, one_div, inv_mul_cancel₀ h2F, map_one]
  simp only [Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
  rw [← mul_assoc, h2, one_mul]

theorem corner_mul_inv {t : F} (ht : t ≠ 0) (u : Rˣ) :
    (((u : R) ^ 2 * algebraMap F R t) ⊗ₜ[F] (1 : E)) *
      ((((u⁻¹ : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t⁻¹)) * inclR R (algebraMap F E t) *
        (((u⁻¹ : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t⁻¹))) = 1 := by
  have hi : inclR R (algebraMap F E t) = (1 : R) ⊗ₜ[F] (algebraMap F E t) := rfl
  have hE : algebraMap F E t⁻¹ * algebraMap F E t = 1 := by
    rw [← map_mul, inv_mul_cancel₀ ht, map_one]
  have hu : (u : R) * ((u⁻¹ : Rˣ) : R) = 1 := u.mul_inv
  rw [hi, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.TensorProduct.tmul_mul_tmul, hE, mul_one, one_mul, one_mul]
  have e1 : (u : R) ^ 2 * algebraMap F R t * (((u⁻¹ : Rˣ) : R) * ((u⁻¹ : Rˣ) : R)) =
      algebraMap F R t := by
    calc _ = ((u : R) * ((u⁻¹ : Rˣ) : R)) ^ 2 * algebraMap F R t := by ring
      _ = _ := by rw [hu]; ring
  rw [e1, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, Algebra.smul_def t,
    ← map_mul, mul_inv_cancel₀ ht, map_one]
  rfl

theorem isUnit_det_of_mem_Bset : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ S ∈ (Bset R σ t a B₀ : Set (HermR R σ (n + 1))), IsUnit (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)).det := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D S hS
  obtain ⟨-, -, -, -, hArt, hRed, -, -⟩ := D.hR
  obtain ⟨-, -, -, -, -, hfix, -⟩ := KAlg.algebra_tensor_invol F E σ D.hCM R
  have hfr : Module.finrank F E = 2 := D.hCM.2.2.1
  have : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  let b₂ : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E hfr
  have hsig : ∀ (p : R) (e : E), sigR R σ (p ⊗ₜ[F] e) = p ⊗ₜ[F] σ e := fun _ _ => rfl
  set T : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E) := S.1 with hT
  have hH : ∀ i j, sigR R σ (T j i) = T i j := S.2
  obtain ⟨x, hx⟩ := hfix (T 0 0) (hH 0 0)
  have hs0 : s0 R T = x := by
    rw [s0, hx]; exact half_trace_tmul two_ne_zero b₂ x
  have hxB : x ∈ B₀ := by
    have h : s0 R T ∈ B₀ := hS.1
    rwa [hs0] at h
  set u : Rˣ := a x with hu
  set p : R ⊗[F] E := ((u⁻¹ : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t⁻¹) with hp
  set τ : R ⊗[F] E := inclR R (algebraMap F E t) with hτ
  have hsp : sigR R σ p = p := by rw [hp, hsig, AlgHom.commutes]
  have hsτ : sigR R σ τ = τ := by
    show sigR R σ ((1 : R) ⊗ₜ[F] (algebraMap F E t)) = (1 : R) ⊗ₜ[F] (algebraMap F E t)
    rw [hsig, AlgHom.commutes]
  have hw : T 0 0 * (p * τ * p) = 1 := by
    rw [hx]
    have := corner_mul_inv (E := E) (R := R) D.ht u
    have hq : x = (u : R) ^ 2 * algebraMap F R t := D.hsq x hxB
    rwa [← hq] at this
  have hschur : ∀ i j, schurM R σ t a T i j = T i.succ j.succ - T i.succ 0 * (p * τ * p) * T 0 j.succ := by
    intro i j
    have hc : ∀ k, cvec R t a T k = p * T 0 k.succ := by
      intro k; rw [cvec, hs0]
    simp only [schurM]
    rw [hc, hc, map_mul, hsp, hH]
    ring
  have hmem : schurM R σ t a T ∈ HermR R σ n := by
    intro i j
    rw [hschur, hschur, map_sub, map_mul, map_mul, map_mul, map_mul, hsp, hsτ, hH, hH, hH]
    ring
  have hdet := det_eq_corner_mul T _ hw
  have hU : IsUnit (T 0 0) := IsUnit.of_mul_eq_one _ hw
  have hsch : (schur R σ t a S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) =
      Matrix.of fun i j : Fin n => T i.succ j.succ - T i.succ 0 * (p * τ * p) * T 0 j.succ := by
    rw [schur_coe R σ t a S hmem]
    ext i j
    exact hschur i j
  have h2 := hS.2
  rw [hsch] at h2
  rw [hdet]
  exact hU.mul h2

end GlobalTheory.CompanionTheory.SW.PiLocalization₂.BsetUnit
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
open GlobalTheory.CompanionTheory.SW.Core.PoiLat in

theorem _root_.GlobalTheory.T.poisson_summation_gaussian :
    ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (Z : Matrix κ κ ℂ),
    Z.IsSymm → (Z.map Complex.im).PosDef → ∀ (g : Matrix κ κ ℝ), g.det ≠ 0 → ∀ a : κ → ℝ,
    let f : (κ → ℝ) → ℂ := fun x => Complex.exp ((Real.pi : ℂ) * Complex.I *
      ((fun i => (x i : ℂ)) ⬝ᵥ (Z *ᵥ fun i => (x i : ℂ))));
    let fh : (κ → ℝ) → ℂ := fun y =>
      ∫ x, f x * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((x ⬝ᵥ y : ℝ) : ℂ));
    Summable (fun n : κ → ℤ => ‖f (a + g *ᵥ fun i => (n i : ℝ))‖) ∧
      Summable (fun n : κ → ℤ => ‖fh ((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ))‖) ∧
      (∑' n : κ → ℤ, f (a + g *ᵥ fun i => (n i : ℝ))) = ((|g.det|⁻¹ : ℝ) : ℂ) *
        ∑' n : κ → ℤ, fh ((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) *
          Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) *
            ((a ⬝ᵥ ((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) : ℝ) : ℂ)) := by
  apply GlobalTheory.CompanionTheory.SW.Core.PoiLat.poisson_shifted_lattice <;> assumption
end
