module

public import Formalism.HermitianLattices.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle022
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle009
public import Formalism.PeriodIntegrals.Bundle004
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle008
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle050
public import Formalism.RealPlaceAnalysis.Bundle001
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle106
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle107
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle108
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
public import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.RealIdealCount

theorem eq_map_comap {E : Type} [Field E] [NumberField E] [StarRing E]
    (hs : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a)) {𝔫 : Ideal (𝓞 E)}
    (h : 𝔫 = Ideal.span {t | t ∈ 𝔫 ∧ star (t : E) = t}) :
    𝔫 = (𝔫.comap (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))).map
      (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) := by
  refine le_antisymm ?_ Ideal.map_comap_le
  conv_lhs => rw [h]
  refine Ideal.span_le.mpr ?_
  rintro t ⟨ht, hst⟩
  have hreal : (t : E) ∈ maximalRealSubfield E := by
    intro φ
    have key := hs φ (t : E)
    rw [hst, starRingEnd_apply] at key
    exact key.symm
  have hint : IsIntegral ℤ (⟨(t : E), hreal⟩ : maximalRealSubfield E) := by
    have ht' : IsIntegral ℤ (t : E) := t.isIntegral_coe
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ (maximalRealSubfield E) E)
      (algebraMap (maximalRealSubfield E) E).injective).mp ht'
  let s : 𝓞 (maximalRealSubfield E) := ⟨⟨(t : E), hreal⟩, hint⟩
  have hs' : algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s = t := by
    apply RingOfIntegers.ext
    rfl
  rw [← hs']
  refine Ideal.mem_map_of_mem _ ?_
  rw [Ideal.mem_comap, hs']
  exact ht

private theorem isCMField_of_star_compat {E : Type} [Field E] [NumberField E] [StarRing E]
    [hTC : _root_.NumberField.IsTotallyComplex E]
    (hs : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a)) : IsCMField E := by
  refine GlobalTheory.LeastExponentCompare.isCMField_of_conj E (fun z => star z)
    (fun φ z => by rw [hs, starRingEnd_apply]) ?_
  by_contra hne
  push_neg at hne
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace E))
  have hreal : w.IsReal := by
    rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    ext z
    simp only [ComplexEmbedding.conjugate_coe_eq]
    have := hs w.embedding z
    rw [hne z, starRingEnd_apply] at this
    exact this.symm
  exact (InfinitePlace.not_isReal_iff_isComplex.mpr (hTC.isComplex w)) hreal

private theorem finrank_maximalRealSubfield_eq_fDeg (E : Type) [Field E] [NumberField E] [IsCMField E] :
    Module.finrank ℚ (maximalRealSubfield E) = Formalism.HermitianLatticesTheory.fDeg E := by
  have h1 := (letI : Module.Free (maximalRealSubfield E) E := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E)
  rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E,
    IsTotallyComplex.finrank (K := E)] at h1
  have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := E)
  rw [IsTotallyComplex.nrRealPlaces_eq_zero E, zero_add] at h2
  unfold Formalism.HermitianLatticesTheory.fDeg
  omega

theorem ncard_real_ideals_le : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ Y : ℝ, 1 ≤ Y → {𝔫 : Ideal (𝓞 E) | 𝔫 ≠ ⊥ ∧ 𝔫 = Ideal.span {t | t ∈ 𝔫 ∧ star (t : E) = t} ∧ (Ideal.absNorm 𝔫 : ℝ) ≤ Y ^ 2}.Finite ∧ (({𝔫 : Ideal (𝓞 E) | 𝔫 ≠ ⊥ ∧ 𝔫 = Ideal.span {t | t ∈ 𝔫 ∧ star (t : E) = t} ∧ (Ideal.absNorm 𝔫 : ℝ) ≤ Y ^ 2}.ncard : ℕ) : ℝ) ≤ Y * (1 + Real.log Y) ^ Formalism.HermitianLatticesTheory.fDeg E := by
  intro E _ _ _ hE Y hY
  obtain ⟨hTC, hs, -⟩ := hE
  haveI := hTC
  haveI : IsCMField E := isCMField_of_star_compat hs
  set F := maximalRealSubfield E
  set S : Set (Ideal (𝓞 E)) := {𝔫 : Ideal (𝓞 E) | 𝔫 ≠ ⊥ ∧ 𝔫 = Ideal.span {t | t ∈ 𝔫 ∧ star (t : E) = t} ∧
    (Ideal.absNorm 𝔫 : ℝ) ≤ Y ^ 2} with hSdef
  set T : Set (Ideal (𝓞 F)) := {𝔞 : Ideal (𝓞 F) | 𝔞 ≠ ⊥ ∧ (Ideal.absNorm 𝔞 : ℝ) ≤ Y} with hTdef
  let g : Ideal (𝓞 E) → Ideal (𝓞 F) := fun 𝔫 => 𝔫.comap (algebraMap (𝓞 F) (𝓞 E))
  have hmap : ∀ 𝔫 ∈ S, 𝔫 = (g 𝔫).map (algebraMap (𝓞 F) (𝓞 E)) := fun 𝔫 h𝔫 =>
    eq_map_comap hs h𝔫.2.1
  have hdeg : Module.finrank (𝓞 F) (𝓞 E) = 2 := by
    rw [← IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E]
    exact Algebra.IsQuadraticExtension.finrank_eq_two F E
  have hinj : Set.InjOn g S := by
    intro 𝔫₁ h₁ 𝔫₂ h₂ heq
    rw [hmap 𝔫₁ h₁, hmap 𝔫₂ h₂, heq]
  have hmaps : Set.MapsTo g S T := by
    intro 𝔫 h𝔫
    have hn := hmap 𝔫 h𝔫
    refine ⟨?_, ?_⟩
    · intro hbot
      apply h𝔫.1
      rw [hn, hbot, Ideal.map_bot]
    · have hnorm : Ideal.absNorm 𝔫 = Ideal.absNorm (g 𝔫) ^ 2 := by
        conv_lhs => rw [hn]
        rw [Ideal.absNorm_algebraMap, hdeg]
      have hle := h𝔫.2.2
      rw [hnorm] at hle
      push_cast at hle
      exact (pow_le_pow_iff_left₀ (Nat.cast_nonneg _) (by linarith) two_ne_zero).mp hle
  have hT : T.Finite := GlobalTheory.IdealBoundedNorm.finite_setOf_absNorm_le F Y
  refine ⟨Set.Finite.of_injOn hmaps hinj hT, ?_⟩
  have hcard : S.ncard ≤ T.ncard := Set.ncard_le_ncard_of_injOn g hmaps hinj hT
  have hTb := GlobalTheory.IdealBoundedNorm.ncard_absNorm_le F Y hY
  rw [finrank_maximalRealSubfield_eq_fDeg E] at hTb
  calc ((S.ncard : ℕ) : ℝ) ≤ (T.ncard : ℝ) := by exact_mod_cast hcard
    _ ≤ Y * (1 + Real.log Y) ^ Formalism.HermitianLatticesTheory.fDeg E := hTb

end GlobalTheory.RealIdealCount
end

section

noncomputable section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace GlobalTheory.Tube

def Hd (k : ℕ) (η : ℝ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  Matrix.diagonal fun j : Fin (k + 1) => if j = Fin.last k then (η : ℂ) else 1

def blk {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) (b r : Fin k → ℂ) (d : ℂ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  fun i j => Fin.lastCases (motive := fun _ => ℂ) (Fin.lastCases (motive := fun _ => ℂ) d r j)
    (fun i' => Fin.lastCases (motive := fun _ => ℂ) (b i') (A i') j) i

@[simp] theorem blk_ll {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) (b r : Fin k → ℂ) (d : ℂ) :
    blk A b r d (Fin.last k) (Fin.last k) = d := by simp [blk]

@[simp] theorem blk_lc {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) (b r : Fin k → ℂ) (d : ℂ) (j : Fin k) :
    blk A b r d (Fin.last k) j.castSucc = r j := by simp [blk]

@[simp] theorem blk_cl {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) (b r : Fin k → ℂ) (d : ℂ) (i : Fin k) :
    blk A b r d i.castSucc (Fin.last k) = b i := by simp [blk]

@[simp] theorem blk_cc {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) (b r : Fin k → ℂ) (d : ℂ) (i j : Fin k) :
    blk A b r d i.castSucc j.castSucc = A i j := by simp [blk]

theorem blk_ext {k : ℕ} {M N : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (h1 : ∀ i j : Fin k, M i.castSucc j.castSucc = N i.castSucc j.castSucc)
    (h2 : ∀ i : Fin k, M i.castSucc (Fin.last k) = N i.castSucc (Fin.last k))
    (h3 : ∀ j : Fin k, M (Fin.last k) j.castSucc = N (Fin.last k) j.castSucc)
    (h4 : M (Fin.last k) (Fin.last k) = N (Fin.last k) (Fin.last k)) : M = N := by
  first
  | exact @_root_.GlobalTheory.MatrixExtLast.matrix_ext_last
  | exact _root_.GlobalTheory.MatrixExtLast.matrix_ext_last
  | (apply _root_.GlobalTheory.MatrixExtLast.matrix_ext_last <;> assumption)
  | (intros; apply _root_.GlobalTheory.MatrixExtLast.matrix_ext_last <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MatrixExtLast.matrix_ext_last <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MatrixExtLast.matrix_ext_last ..)

theorem Hd_eq (k : ℕ) (η : ℝ) : Hd k η = blk 1 0 0 (η : ℂ) := by
  refine blk_ext (fun i j => ?_) (fun i => ?_) (fun j => ?_) ?_
  · simp [Hd, Matrix.diagonal_apply, Matrix.one_apply, Fin.castSucc_ne_last]
  · simp [Hd, Matrix.diagonal_apply, Fin.castSucc_ne_last]
  · simp [Hd, Matrix.diagonal_apply, (Fin.castSucc_ne_last _).symm]
  · simp [Hd]

theorem Hd_sq (k : ℕ) {η : ℝ} (hη : η = 1 ∨ η = -1) : Hd k η * Hd k η = 1 := by
  refine GlobalTheory.GramExp.diag_sq fun i => ?_
  split_ifs
  · rcases hη with h | h <;> simp [h]
  · simp

def nsq {k : ℕ} (β : Fin k → ℂ) : ℝ := ∑ j, ‖β j‖ ^ 2

def dd {k : ℕ} (η : ℝ) (β : Fin k → ℂ) : ℝ := Real.sqrt (1 - η * nsq β)

def sec {k : ℕ} (η : ℝ) (β : Fin k → ℂ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  blk (fun i j => (1 : Matrix (Fin k) (Fin k) ℂ) i j - ((η / (1 + dd η β) : ℝ) : ℂ) * (conj (β i) * β j))
    (fun i => -(η : ℂ) * conj (β i)) β (dd η β : ℂ)

def kap {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) (u : ℂ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ := blk A 0 0 u

def row {k : ℕ} (g : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Fin k → ℂ := fun j => g (Fin.last k) j.castSucc

def ph {k : ℕ} (g : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : ℂ :=
  g (Fin.last k) (Fin.last k) / (‖g (Fin.last k) (Fin.last k)‖ : ℂ)

def bet {k : ℕ} (g : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Fin k → ℂ := fun j => conj (ph g) * row g j

def top {k : ℕ} (η : ℝ) (g : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Matrix (Fin k) (Fin k) ℂ :=
  fun i j => (g * sec η (-bet g)) i.castSucc j.castSucc

abbrev Par (k : ℕ) : Type := lieE (UH (1 : Matrix (Fin k) (Fin k) ℂ)) × ℝ × EuclideanSpace ℂ (Fin k)

def hv {k : ℕ} (w : EuclideanSpace ℂ (Fin k)) : Fin k → ℂ := fun j => w j / (Real.sqrt 2 : ℂ)

def chart {k : ℕ} (η : ℝ) (x : Par k) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  kap (NormedSpace.exp (unrealify (x.1 : EuclideanSpace ℝ _))) (Complex.exp (x.2.1 * Complex.I)) * sec η (hv x.2.2)

def tang {k : ℕ} (η : ℝ) (x : Par k) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  blk (unrealify (x.1 : EuclideanSpace ℝ _)) (fun i => -(η : ℂ) * conj (hv x.2.2 i)) (hv x.2.2) (x.2.1 * Complex.I)

def tubeO (k : ℕ) (η t : ℝ) : Set (PI.MtM (k + 1)) :=
  {g | Matrix.of g ∈ UH (Hd k η) ∧ nsq (row (Matrix.of g)) < t}

end GlobalTheory.Tube
end
end

section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.hilbertSchmidt_inUJ_le_of_sign_columns : ∀ (n : ℕ) (ε : Fin n → Bool) (s : Bool) (h : Matrix (Fin n) (Fin n) ℂ), inUJ ε h → hs h ≤ n + 4 * ∑ i, ∑ j ∈ univ.filter (fun j => ε j = s), ‖h i j‖ ^ 2 := by
  first | exact @GlobalTheory.hs_le_of_cols | exact GlobalTheory.hs_le_of_cols | (intros; apply GlobalTheory.hs_le_of_cols <;> assumption)
end

section

open Matrix Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.holomorphic_extension_compact_rep : ∀ (n : ℕ) (ε : Fin n → Bool) (B : Type) [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B] (π : Matrix (Fin n) (Fin n) ℂ → B), π 1 = 1 → (∀ a ∈ Formalism.REAL.Kset ε, ∀ b ∈ Formalism.REAL.Kset ε, π (a * b) = π a * π b) → ContinuousOn π (Formalism.REAL.Kset ε) → ∃ τ : Matrix (Fin n) (Fin n) ℂ → B, DifferentiableOn ℂ (fun y : Fin n → Fin n → ℂ => τ (Matrix.of y)) {y | IsUnit (Matrix.of y)} ∧ ∀ k ∈ Formalism.REAL.Kset ε, τ k = π k := by
  first | exact @GlobalTheory.HolExt.exists_holomorphic_extension | exact GlobalTheory.HolExt.exists_holomorphic_extension | (intros; apply GlobalTheory.HolExt.exists_holomorphic_extension <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.RealFormBasis

variable {n : ℕ} (ε : Fin n → Bool)

private theorem Jm_mul_self_eq_one' {n : ℕ} (ε : Fin n → Bool) :
    Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  rw [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

private theorem Jm_conjTransposeFlagMeasures {n : ℕ} (ε : Fin n → Bool) :
    (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
  rw [Formalism.REAL.Jm, Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  by_cases h : ε a <;> simp [h]

private theorem Jm_mul_Jm_mul' {n : ℕ} (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * M) = M := by
  rw [← Matrix.mul_assoc, Jm_mul_self_eq_one', Matrix.one_mul]

theorem inG_iff_adj (X : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.inG ε X ↔ Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε = -X := by
  unfold Formalism.REAL.inG
  constructor
  · intro h

    have h' := congrArg (fun M => Formalism.REAL.Jm ε * M) h
    simp only [Matrix.mul_add, Matrix.mul_zero, Jm_mul_Jm_mul'] at h'
    rw [← Matrix.mul_assoc] at h'
    exact eq_neg_of_add_eq_zero_left h'
  · intro h
    have h' := congrArg (fun M => Formalism.REAL.Jm ε * M) h
    simp only [Matrix.mul_assoc, Jm_mul_Jm_mul', Matrix.mul_neg] at h'
    rw [h', neg_add_cancel]

theorem adj_adj (X : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε)ᴴ * Formalism.REAL.Jm ε = X := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Jm_conjTransposeFlagMeasures]
  simp only [Matrix.mul_assoc, Jm_mul_Jm_mul', Jm_mul_self_eq_one', Matrix.mul_one]

theorem finrank_and_det (n : ℕ) (ε : Fin n → Bool) (N : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ)) (d : ℕ)
    (E : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (hN : ∀ X ∈ N, Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε ∈ N) (hE : LinearIndependent ℝ E)
    (hs : ∀ X, (X ∈ N ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) :
    Module.finrank ℂ N = d ∧ ∀ (φ : N →ₗ[ℂ] N) (L : Matrix (Fin d) (Fin d) ℝ),
      (∀ (k : Fin d) (h : E k ∈ N), ((φ ⟨E k, h⟩ : N) : Matrix (Fin n) (Fin n) ℂ) = ∑ i, L i k • E i) →
      LinearMap.det φ = ((L.det : ℝ) : ℂ) := by
  classical

  have hS_add : ∀ X Y : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.Jm ε * (X + Y)ᴴ * Formalism.REAL.Jm ε =
      Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * Yᴴ * Formalism.REAL.Jm ε := by
    intro X Y
    rw [Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
  have hS_sub : ∀ X Y : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.Jm ε * (X - Y)ᴴ * Formalism.REAL.Jm ε =
      Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε - Formalism.REAL.Jm ε * Yᴴ * Formalism.REAL.Jm ε := by
    intro X Y
    rw [Matrix.conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul]
  have hS_smul : ∀ (c : ℂ) (X : Matrix (Fin n) (Fin n) ℂ), Formalism.REAL.Jm ε * (c • X)ᴴ * Formalism.REAL.Jm ε =
      star c • (Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε) := by
    intro c X
    rw [Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul]
  have hS_sum : ∀ g : Fin d → ℂ, Formalism.REAL.Jm ε * (∑ i, g i • E i)ᴴ * Formalism.REAL.Jm ε =
      ∑ i, star (g i) • (Formalism.REAL.Jm ε * (E i)ᴴ * Formalism.REAL.Jm ε) := by
    intro g
    rw [Matrix.conjTranspose_sum, Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact hS_smul (g i) (E i)

  have hEmem : ∀ k, E k ∈ N ∧ Formalism.REAL.inG ε (E k) := fun k =>
    (hs (E k)).2 (Submodule.subset_span ⟨k, rfl⟩)
  have hEadj : ∀ k, Formalism.REAL.Jm ε * (E k)ᴴ * Formalism.REAL.Jm ε = -E k := fun k =>
    (inG_iff_adj ε (E k)).1 (hEmem k).2

  have hLI : LinearIndependent ℂ E := by
    rw [Fintype.linearIndependent_iff] at hE ⊢
    intro g hg i
    have h1 : ∑ i, star (g i) • E i = 0 := by
      have h : Formalism.REAL.Jm ε * (∑ i, g i • E i)ᴴ * Formalism.REAL.Jm ε =
          Formalism.REAL.Jm ε * (0 : Matrix (Fin n) (Fin n) ℂ)ᴴ * Formalism.REAL.Jm ε := by rw [hg]
      rw [hS_sum, Matrix.conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul] at h
      simpa only [hEadj, smul_neg, Finset.sum_neg_distrib, neg_eq_zero] using h
    have hre : ∑ i, (2 * (g i).re) • E i = 0 := by
      have h2 : ∑ i, (2 * (g i).re) • E i = (∑ i, g i • E i) + ∑ i, star (g i) • E i := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← add_smul, ← Complex.coe_smul]
        congr 1
        apply Complex.ext <;> simp <;> ring
      rw [h2, hg, h1, add_zero]
    have him : ∑ i, (2 * (g i).im) • E i = 0 := by
      have h2 : ∑ i, (2 * (g i).im) • E i =
          (-Complex.I) • ((∑ i, g i • E i) - ∑ i, star (g i) • E i) := by
        rw [← Finset.sum_sub_distrib, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← sub_smul, smul_smul, ← Complex.coe_smul]
        congr 1
        apply Complex.ext <;> simp <;> ring
      rw [h2, hg, h1, sub_zero, smul_zero]
    have a := hE _ hre i
    have b := hE _ him i
    apply Complex.ext <;> simp <;> linarith

  have hspan : N = Submodule.span ℂ (Set.range E) := by
    apply le_antisymm
    · intro X hX
      have hSX : Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε ∈ N := hN X hX
      have hSS := adj_adj ε X
      have hA : (1 / 2 : ℂ) • (X - Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε) ∈
          Submodule.span ℝ (Set.range E) := by
        refine (hs _).1 ⟨N.smul_mem _ (N.sub_mem hX hSX), ?_⟩
        rw [inG_iff_adj, hS_smul, hS_sub, hSS, ← smul_neg, neg_sub]
        congr 1
        simp
      have hB : (-Complex.I / 2) • (X + Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε) ∈
          Submodule.span ℝ (Set.range E) := by
        refine (hs _).1 ⟨N.smul_mem _ (N.add_mem hX hSX), ?_⟩
        rw [inG_iff_adj, hS_smul, hS_add, hSS, add_comm (Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε) X,
          ← neg_smul]
        congr 1
        apply Complex.ext <;> simp <;> norm_num
      have hA' := Submodule.span_le_restrictScalars ℝ ℂ (Set.range E) hA
      have hB' := Submodule.span_le_restrictScalars ℝ ℂ (Set.range E) hB
      have hX_eq : X = (1 / 2 : ℂ) • (X - Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε) +
          Complex.I • ((-Complex.I / 2) • (X + Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε)) := by
        ext i j
        simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
        ring_nf
        rw [Complex.I_sq]
        ring
      rw [hX_eq]
      exact Submodule.add_mem _ hA' (Submodule.smul_mem _ _ hB')
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact (hEmem k).1
  have hfin : Module.finrank ℂ N = d := by
    rw [hspan, finrank_span_eq_card hLI, Fintype.card_fin]
  refine ⟨hfin, ?_⟩
  intro φ L hφ

  let E' : Fin d → N := fun k => ⟨E k, (hEmem k).1⟩
  have hLI' : LinearIndependent ℂ E' := LinearIndependent.of_comp N.subtype hLI
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range E') := by
    rintro ⟨X, hX⟩ -
    have hX' : X ∈ Submodule.span ℂ (Set.range E) := by rw [← hspan]; exact hX
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hX'
    have hXc : (⟨X, hX⟩ : N) = ∑ i, c i • E' i := by
      apply Subtype.ext
      simp [E', ← hc]
    rw [hXc]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let b := Module.Basis.mk hLI' hsp
  rw [← LinearMap.det_toMatrix b]
  have hM : LinearMap.toMatrix b b φ = L.map (fun r : ℝ => (r : ℂ)) := by
    ext i k
    rw [LinearMap.toMatrix_apply, Matrix.map_apply]
    have hφk : φ (b k) = ∑ j, ((L j k : ℝ) : ℂ) • b j := by
      apply Subtype.ext
      have h := hφ k (hEmem k).1
      simp only [b, Module.Basis.mk_apply, E', Submodule.coe_sum, Submodule.coe_smul] at h ⊢
      rw [h]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Complex.coe_smul]
    rw [hφk]
    have hc : ∑ j, ((L j k : ℝ) : ℂ) • b j = b.equivFun.symm (fun j => ((L j k : ℝ) : ℂ)) := by
      rw [Module.Basis.equivFun_symm_apply]
    rw [hc, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  rw [hM]
  exact (RingHom.map_det Complex.ofRealHom L).symm

end GlobalTheory.RealFormBasis
end

section

open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.rightRegularRepresentation_unitary_mul_continuous : ∀ (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] (fund : Set I.GA), I.IsFundDom (I.muA μf) fund → ∀ R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund), I.IsRightReg μf fund R → R 1 = ContinuousLinearMap.id ℂ _ ∧ (∀ x y, R (x * y) = (R x).comp (R y)) ∧ (∀ x F, ‖R x F‖ = ‖F‖) ∧ ∀ F, Continuous fun x => R x F := by
  first | exact @GlobalTheory.RightRegProps.rightReg_unitary_mul_continuous | exact GlobalTheory.RightRegProps.rightReg_unitary_mul_continuous | (intros; apply GlobalTheory.RightRegProps.rightReg_unitary_mul_continuous <;> assumption)
end

section

open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.automorphicInstance_exists_fundamental_domain : ∀ (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf], ∃ fund, I.IsFundDom (I.muA μf) fund := by
  first | exact @GlobalTheory.FundExists.exists_isFundDom | exact GlobalTheory.FundExists.exists_isFundDom | (intros; apply GlobalTheory.FundExists.exists_isFundDom <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

theorem _root_.GlobalTheory.T.dense_compactly_supported_L2 : ∀ B : RowsAut, Dense {y : B.I.L2 B.μf B.fund | ∃ C : Set B.I.GA, IsCompact C ∧ ∀ᵐ z ∂((B.I.muA B.μf).restrict B.fund), z ∉ C → (y : B.I.GA → ℂ) z = 0} := by
  first | exact @GlobalTheory.CompactDense.dense_compact_support | exact GlobalTheory.CompactDense.dense_compact_support | (intros; apply GlobalTheory.CompactDense.dense_compact_support <;> assumption)
end
