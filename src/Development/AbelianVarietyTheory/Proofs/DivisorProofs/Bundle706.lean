module

public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryPQContinuousCharacterEqDetPowProd
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle651
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle670
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtensionOverNormalQuasiProjectiveBase
public import ReciprocityTheory.L2DbarEstimates.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle671
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open scoped Matrix
open Formalism.BasicNotions.TH

namespace GlobalTheory.KChar

open Matrix

theorem norm_eq_one_of_compact {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G] (f : G → ℂ)
    (hmul : ∀ a b, f (a * b) = f a * f b) (hc : Continuous f) (h1 : f 1 ≠ 0) : ∀ a, ‖f a‖ = 1 := by
  have hf1 : f 1 = 1 := by
    have := hmul 1 1
    rw [mul_one] at this
    have h2 : f 1 * (f 1 - 1) = 0 := by rw [mul_sub, ← this]; ring
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h h1
    · exact sub_eq_zero.mp h
  obtain ⟨M, hM⟩ := (isCompact_range hc.norm).bddAbove
  have hb : ∀ a, ‖f a‖ ≤ M := fun a => hM ⟨a, rfl⟩
  have hpow : ∀ a (n : ℕ), f (a ^ n) = f a ^ n := by
    intro a n
    induction n with
    | zero => simp [hf1]
    | succ n ih => rw [pow_succ, hmul, ih, pow_succ]
  have hle : ∀ a, ‖f a‖ ≤ 1 := by
    intro a
    by_contra h
    push_neg at h
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M h
    have := hb (a ^ n)
    rw [hpow, norm_pow] at this
    linarith
  intro a
  have hinv : ‖f a‖ * ‖f a⁻¹‖ = 1 := by
    rw [← norm_mul, ← hmul, mul_inv_cancel, hf1, norm_one]
  have h2 := hle a⁻¹
  have h3 := hle a
  have h4 : 0 ≤ ‖f a‖ := norm_nonneg _
  have h5 : 0 ≤ ‖f a⁻¹‖ := norm_nonneg _
  nlinarith

theorem fromBlocks_mem (R S : ℕ) (a : Matrix (Fin R) (Fin R) ℂ) (d : Matrix (Fin S) (Fin S) ℂ)
    (ha : aᴴ * a = 1) (hd : dᴴ * d = 1) :
    (Matrix.fromBlocks a 0 0 d)ᴴ * Jm R S * Matrix.fromBlocks a 0 0 d = Jm R S := by
  change (Matrix.fromBlocks a 0 0 d)ᴴ * Matrix.fromBlocks 1 0 0 (-1) * Matrix.fromBlocks a 0 0 d =
    Matrix.fromBlocks 1 0 0 (-1)
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [ha, hd]

theorem unitary_ch {n : ℕ} (a : Matrix.unitaryGroup (Fin n) ℂ) : (a : Matrix (Fin n) (Fin n) ℂ)ᴴ * a = 1 := by
  have := Matrix.mem_unitaryGroup_iff'.mp a.2
  simpa [Matrix.star_eq_conjTranspose] using this

theorem kchar : ∀ (R S : ℕ) (χ : Mat R S → ℂ),
    (∀ g h : Mat R S, gᴴ * Jm R S * g = Jm R S → hᴴ * Jm R S * h = Jm R S → χ (g * h) = χ g * χ h) →
    ContinuousOn χ {g : Mat R S | gᴴ * Jm R S * g = Jm R S} →
    (∀ g : Mat R S, gᴴ * Jm R S * g = Jm R S → χ g ≠ 0) →
    ∃ x y : ℤ, ∀ (a : Matrix (Fin R) (Fin R) ℂ) (d : Matrix (Fin S) (Fin S) ℂ), aᴴ * a = 1 → dᴴ * d = 1 →
      χ (Matrix.fromBlocks a 0 0 d) = a.det ^ x * d.det ^ y := by
  intro R S χ hmul hc hnz
  haveI := GlobalTheory.compactSpace_unitaryGroup (Fin R) ℂ
  haveI := GlobalTheory.compactSpace_unitaryGroup (Fin S) ℂ
  have h1R : (1 : Matrix (Fin R) (Fin R) ℂ)ᴴ * 1 = 1 := by simp
  have h1S : (1 : Matrix (Fin S) (Fin S) ℂ)ᴴ * 1 = 1 := by simp

  let fA : Matrix.unitaryGroup (Fin R) ℂ → ℂ := fun a => χ (Matrix.fromBlocks (a : Matrix (Fin R) (Fin R) ℂ) 0 0 1)
  have hmA : ∀ a b, fA (a * b) = fA a * fA b := by
    intro a b
    have e : Matrix.fromBlocks ((a * b : Matrix.unitaryGroup (Fin R) ℂ) : Matrix (Fin R) (Fin R) ℂ) 0 0
        (1 : Matrix (Fin S) (Fin S) ℂ) =
        Matrix.fromBlocks (a : Matrix (Fin R) (Fin R) ℂ) 0 0 1 * Matrix.fromBlocks (b : Matrix (Fin R) (Fin R) ℂ) 0 0 1 := by
      rw [Matrix.fromBlocks_multiply]; simp
    simp only [fA]
    rw [e]
    exact hmul _ _ (fromBlocks_mem R S _ _ (unitary_ch a) h1S) (fromBlocks_mem R S _ _ (unitary_ch b) h1S)
  have hcA : Continuous fA := by
    refine hc.comp_continuous ?_ (fun a => fromBlocks_mem R S _ _ (unitary_ch a) h1S)
    exact Continuous.matrix_fromBlocks continuous_subtype_val continuous_const continuous_const continuous_const
  have hnA : ∀ a, ‖fA a‖ = 1 :=
    norm_eq_one_of_compact fA hmA hcA (hnz _ (fromBlocks_mem R S _ _ (unitary_ch 1) h1S))
  obtain ⟨x, hx⟩ := GlobalTheory.UpqChar.char_unitary fA hmA hnA hcA

  let fD : Matrix.unitaryGroup (Fin S) ℂ → ℂ := fun d => χ (Matrix.fromBlocks (1 : Matrix (Fin R) (Fin R) ℂ) 0 0 (d : Matrix (Fin S) (Fin S) ℂ))
  have hmD : ∀ a b, fD (a * b) = fD a * fD b := by
    intro a b
    have e : Matrix.fromBlocks (1 : Matrix (Fin R) (Fin R) ℂ) 0 0
        ((a * b : Matrix.unitaryGroup (Fin S) ℂ) : Matrix (Fin S) (Fin S) ℂ) =
        Matrix.fromBlocks 1 0 0 (a : Matrix (Fin S) (Fin S) ℂ) * Matrix.fromBlocks 1 0 0 (b : Matrix (Fin S) (Fin S) ℂ) := by
      rw [Matrix.fromBlocks_multiply]; simp
    simp only [fD]
    rw [e]
    exact hmul _ _ (fromBlocks_mem R S _ _ h1R (unitary_ch a)) (fromBlocks_mem R S _ _ h1R (unitary_ch b))
  have hcD : Continuous fD := by
    refine hc.comp_continuous ?_ (fun a => fromBlocks_mem R S _ _ h1R (unitary_ch a))
    exact Continuous.matrix_fromBlocks continuous_const continuous_const continuous_const continuous_subtype_val
  have hnD : ∀ a, ‖fD a‖ = 1 :=
    norm_eq_one_of_compact fD hmD hcD (hnz _ (fromBlocks_mem R S _ _ h1R (unitary_ch 1)))
  obtain ⟨y, hy⟩ := GlobalTheory.UpqChar.char_unitary fD hmD hnD hcD
  refine ⟨x, y, fun a d ha hd => ?_⟩
  have maU : a ∈ Matrix.unitaryGroup (Fin R) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]; exact ha
  have mdU : d ∈ Matrix.unitaryGroup (Fin S) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]; exact hd
  have e : Matrix.fromBlocks a 0 0 d = Matrix.fromBlocks a 0 0 (1 : Matrix (Fin S) (Fin S) ℂ) *
      Matrix.fromBlocks (1 : Matrix (Fin R) (Fin R) ℂ) 0 0 d := by
    rw [Matrix.fromBlocks_multiply]; simp
  rw [e, hmul _ _ (fromBlocks_mem R S _ _ ha h1S) (fromBlocks_mem R S _ _ h1R hd)]
  have hA := hx ⟨a, maU⟩
  have hD := hy ⟨d, mdU⟩
  simp only [fA, fD] at hA hD
  rw [hA, hD]

end GlobalTheory.KChar
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section

namespace GlobalTheory.ThetaTransformF

open Formalism.IndefR.DatumF GlobalTheory.ThetaTransform GlobalTheory.SWQ

section Ad

variable (F : Type) [Field F] [NumberField F]

theorem fstA_pairA' (x : Ainf F) (y : Af F) : fstA F (pairA F x y) = x := rfl

theorem sndA_pairA' (x : Ainf F) (y : Af F) : sndA F (pairA F x y) = y := rfl

variable {F} in
theorem af_ext' {a b : AF F} (h1 : fstA F a = fstA F b) (h2 : sndA F a = sndA F b) : a = b :=
  Prod.ext (α := Ainf F) (β := Af F) h1 h2

theorem pairA_mul_eq_zero_iff_snd' (a : AF F) : pairA F 0 1 * a = 0 ↔ sndA F a = 0 := by
  constructor
  · intro h
    have := congrArg (sndA F) h
    rwa [map_mul, map_zero, sndA_pairA', one_mul] at this
  · intro h
    refine af_ext' ?_ ?_
    · rw [map_mul, map_zero, fstA_pairA', zero_mul]
    · rw [map_mul, map_zero, sndA_pairA', h, mul_zero]

theorem pairA_mul_eq_zero_iff_fst' (a : AF F) : pairA F 1 0 * a = 0 ↔ fstA F a = 0 := by
  constructor
  · intro h
    have := congrArg (fstA F) h
    rwa [map_mul, map_zero, fstA_pairA', one_mul] at this
  · intro h
    refine af_ext' ?_ ?_
    · rw [map_mul, map_zero, fstA_pairA', h, mul_zero]
    · rw [map_mul, map_zero, sndA_pairA', zero_mul]

def incFin : Af F →ₗ[F] AF F where
  toFun y := pairA F 0 y
  map_add' y y' := af_ext' (by rw [map_add (f := _), fstA_pairA', fstA_pairA', fstA_pairA', add_zero])
    (by rw [map_add (f := _), sndA_pairA', sndA_pairA', sndA_pairA'])
  map_smul' c y := af_ext' (by rw [map_smul, fstA_pairA', fstA_pairA', RingHom.id_apply, smul_zero])
    (by rw [map_smul, sndA_pairA', sndA_pairA', RingHom.id_apply])

def incInf : Ainf F →ₗ[F] AF F where
  toFun y := pairA F y 0
  map_add' y y' := af_ext' (by rw [map_add (f := _), fstA_pairA', fstA_pairA', fstA_pairA'])
    (by rw [map_add (f := _), sndA_pairA', sndA_pairA', sndA_pairA', add_zero])
  map_smul' c y := af_ext' (by rw [map_smul, fstA_pairA', fstA_pairA', RingHom.id_apply])
    (by rw [map_smul, sndA_pairA', sndA_pairA', RingHom.id_apply, smul_zero])

theorem incFin_sndA (a : AF F) : incFin F (sndA F a) = pairA F 0 1 * a :=
  af_ext' (by rw [map_mul, fstA_pairA', zero_mul]; rfl) (by rw [map_mul, sndA_pairA', one_mul]; rfl)

theorem incInf_fstA (a : AF F) : incInf F (fstA F a) = pairA F 1 0 * a :=
  af_ext' (by rw [map_mul, fstA_pairA', one_mul]; rfl) (by rw [map_mul, sndA_pairA', zero_mul]; rfl)

end Ad

section Coord

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def secFin : Af F ⊗[F] E →ₗ[F] AF F ⊗[F] E := TensorProduct.map (incFin F) LinearMap.id

def secInf : Ainf F ⊗[F] E →ₗ[F] AF F ⊗[F] E := TensorProduct.map (incInf F) LinearMap.id

variable {F E}

theorem secFin_finPartF (z : AF F ⊗[F] E) : secFin F E (finPartF F E z) = pairA F 0 1 • z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [(finPartF F E).map_zero, (secFin F E).map_zero, smul_zero]
  | tmul a b =>
    have h1 : finPartF F E (a ⊗ₜ b) = sndA F a ⊗ₜ b := rfl
    rw [h1, secFin, TensorProduct.map_tmul, LinearMap.id_apply, incFin_sndA, TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => rw [(finPartF F E).map_add, (secFin F E).map_add, hx, hy, smul_add]

theorem secInf_infPartF (z : AF F ⊗[F] E) : secInf F E (infPartF F E z) = pairA F 1 0 • z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [(infPartF F E).map_zero, (secInf F E).map_zero, smul_zero]
  | tmul a b =>
    have h1 : infPartF F E (a ⊗ₜ b) = fstA F a ⊗ₜ b := rfl
    rw [h1, secInf, TensorProduct.map_tmul, LinearMap.id_apply, incInf_fstA, TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => rw [(infPartF F E).map_add, (secInf F E).map_add, hx, hy, smul_add]

theorem finPartF_smul (z : AF F ⊗[F] E) : finPartF F E (pairA F 0 1 • z) = finPartF F E z := by
  rw [Algebra.smul_def, (finPartF F E).map_mul]
  have : finPartF F E (algebraMap (AF F) (AF F ⊗[F] E) (pairA F 0 1)) = 1 := by
    rw [Algebra.TensorProduct.algebraMap_apply]
    show sndA F (algebraMap (AF F) (AF F) (pairA F 0 1)) ⊗ₜ[F] (1 : E) = 1
    rw [Algebra.algebraMap_self, RingHom.id_apply, sndA_pairA']
    rfl
  rw [this, one_mul]

theorem infPartF_smul (z : AF F ⊗[F] E) : infPartF F E (pairA F 1 0 • z) = infPartF F E z := by
  rw [Algebra.smul_def, (infPartF F E).map_mul]
  have : infPartF F E (algebraMap (AF F) (AF F ⊗[F] E) (pairA F 1 0)) = 1 := by
    rw [Algebra.TensorProduct.algebraMap_apply]
    show fstA F (algebraMap (AF F) (AF F) (pairA F 1 0)) ⊗ₜ[F] (1 : E) = 1
    rw [Algebra.algebraMap_self, RingHom.id_apply, fstA_pairA']
    rfl
  rw [this, one_mul]

theorem finPartF_eq_zero_iff (z : AF F ⊗[F] E) : finPartF F E z = 0 ↔ pairA F 0 1 • z = 0 := by
  constructor
  · intro h; rw [← secFin_finPartF, h, (secFin F E).map_zero]
  · intro h; rw [← finPartF_smul, h, (finPartF F E).map_zero]

theorem infPartF_eq_zero_iff (z : AF F ⊗[F] E) : infPartF F E z = 0 ↔ pairA F 1 0 • z = 0 := by
  constructor
  · intro h; rw [← secInf_infPartF, h, (secInf F E).map_zero]
  · intro h; rw [← infPartF_smul, h, (infPartF F E).map_zero]

omit [Field E] [NumberField E] [Algebra F E] in
theorem smul_vec_fin' {N : ℕ} (u : Fin N → AF F) : pairA F 0 1 • u = 0 ↔ fin u = 0 := by
  rw [funext_iff, funext_iff]
  exact forall_congr' fun l => pairA_mul_eq_zero_iff_snd' F (u l)

omit [Field E] [NumberField E] [Algebra F E] in
theorem smul_vec_inf' {N : ℕ} (u : Fin N → AF F) : pairA F 1 0 • u = 0 ↔ inf u = 0 := by
  rw [funext_iff, funext_iff]
  exact forall_congr' fun l => pairA_mul_eq_zero_iff_fst' F (u l)

theorem coordF (m n N : ℕ) (e : Matrix (Fin m) (Fin n) (AF F ⊗[F] E) ≃ₗ[AF F] VA F N) :
    Continuous e ∧ Continuous e.symm ∧
      (∀ x, x.map (finPartF F E) = 0 ↔ fin (e x).1 = 0 ∧ fin (e x).2 = 0) ∧
      (∀ x, x.map (infPartF F E) = 0 ↔ inf (e x).1 = 0 ∧ inf (e x).2 = 0) := by
  haveI h0 : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) (AF F ⊗[F] E)
  haveI h1 : IsModuleTopology (AF F) (Fin n → AF F ⊗[F] E) := IsModuleTopology.instPi
  haveI h2 : IsModuleTopology (AF F) (Matrix (Fin m) (Fin n) (AF F ⊗[F] E)) := IsModuleTopology.instPi
  refine ⟨IsModuleTopology.continuous_of_linearMap e.toLinearMap,
    IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap, fun x => ?_, fun x => ?_⟩
  · have key : x.map (finPartF F E) = 0 ↔ pairA F 0 1 • x = 0 := by
      rw [← Matrix.ext_iff, ← Matrix.ext_iff]
      simp only [Matrix.map_apply, Matrix.zero_apply, Matrix.smul_apply]
      exact forall_congr' fun i => forall_congr' fun j => finPartF_eq_zero_iff (x i j)
    rw [key, ← smul_vec_fin', ← smul_vec_fin', ← LinearEquiv.map_eq_zero_iff e, LinearEquiv.map_smul]
    exact Prod.ext_iff
  · have key : x.map (infPartF F E) = 0 ↔ pairA F 1 0 • x = 0 := by
      rw [← Matrix.ext_iff, ← Matrix.ext_iff]
      simp only [Matrix.map_apply, Matrix.zero_apply, Matrix.smul_apply]
      exact forall_congr' fun i => forall_congr' fun j => infPartF_eq_zero_iff (x i j)
    rw [key, ← smul_vec_inf', ← smul_vec_inf', ← LinearEquiv.map_eq_zero_iff e, LinearEquiv.map_smul]
    exact Prod.ext_iff

end Coord

end GlobalTheory.ThetaTransformF

end
end

section

open Finset

namespace GlobalTheory.DSParam

open Finset in
private theorem diagonal_exp_single_two_pi_eq_one {n : ℕ} (a : Fin n) :
    (Matrix.diagonal fun b ↦
      Complex.exp (↑((Pi.single a (2 * Real.pi) : Fin n → ℝ) b) * Complex.I)) = 1 := by
  rw [← Matrix.diagonal_one]
  congr 1
  funext b
  by_cases h : b = a
  · subst h; simp [Complex.exp_two_pi_mul_I]
  · simp [Pi.single_apply, h]

open Finset in
private theorem exists_int_eq_weight_of_isWtOn {n : ℕ} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {K : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hK : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ K)
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {μ : Fin n → ℝ} {v : H} (hv0 : v ≠ 0)
    (hv : _root_.Formalism.MainNotions.S.IsWtOn K σ μ v) (a : Fin n) : ∃ m : ℤ, μ a = m := by
  unfold _root_.Formalism.MainNotions.S.IsWtOn at hv
  have h1 := hv 0 (by simpa using hK)
  have h2 := hv (Pi.single a (2 * Real.pi)) (by rw [diagonal_exp_single_two_pi_eq_one]; exact hK)
  rw [diagonal_exp_single_two_pi_eq_one] at h2
  simp only [Pi.zero_apply, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
    Matrix.diagonal_one, mul_zero, Finset.sum_const_zero, one_smul] at h1
  rw [h1] at h2
  have hsum : (∑ b, μ b * (Pi.single a (2 * Real.pi) : Fin n → ℝ) b) = μ a * (2 * Real.pi) := by
    simp [Pi.single_apply, mul_ite]
  rw [hsum] at h2
  have he : Complex.exp (↑(μ a * (2 * Real.pi)) * Complex.I) = 1 := by
    by_contra hne
    apply hv0
    have : (Complex.exp (↑(μ a * (2 * Real.pi)) * Complex.I) - 1) • v = 0 := by
      rw [sub_smul, ← h2, one_smul, sub_self]
    exact (smul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp he
  refine ⟨m, ?_⟩
  have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by simp [Real.pi_ne_zero]
  have : ((μ a : ℝ) : ℂ) = (m : ℂ) := by
    apply mul_right_cancel₀ hpi
    push_cast at hm
    linear_combination hm
  exact_mod_cast this

open Finset in
private theorem one_mem_Kset_divisor {n : ℕ} (ε : Fin n → Bool) :
    (1 : Matrix (Fin n) (Fin n) ℂ) ∈ _root_.Formalism.REAL.Kset ε := by
  unfold _root_.Formalism.REAL.Kset
  exact ⟨one_mem _, by simp⟩

open Finset in
private theorem card_same_diff_sign_lt_gt_add_one_eq {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    #{b | a < b ∧ ε b = ε a} + #{b | b < a ∧ ε b = ε a} + #{b | a < b ∧ ε b ≠ ε a}
      + #{b | b < a ∧ ε b ≠ ε a} + 1 = n := by
  simp only [Finset.card_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  have key : ∀ b, ((if a < b ∧ ε b = ε a then 1 else 0) + (if b < a ∧ ε b = ε a then 1 else 0) +
      (if a < b ∧ ε b ≠ ε a then 1 else 0) + (if b < a ∧ ε b ≠ ε a then 1 else 0) : ℕ)
      = if b = a then 0 else 1 := by
    intro b
    rcases lt_trichotomy a b with h | h | h
    · have h1 : b ≠ a := ne_of_gt h
      have h2 : ¬ b < a := not_lt.mpr h.le
      by_cases he : ε b = ε a <;> simp [h, h1, h2, he]
    · subst h; simp
    · have h1 : b ≠ a := ne_of_lt h
      have h2 : ¬ a < b := not_lt.mpr h.le
      by_cases he : ε b = ε a <;> simp [h, h1, h2, he]
  rw [Finset.sum_congr rfl (fun b _ => key b)]
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul, mul_one,
    Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ,
    Fintype.card_fin]
  have := a.isLt
  omega

open Finset in
private theorem exists_int_rhoC_sub_rhoN_sub_half {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    ∃ m : ℤ, _root_.Formalism.REAL.rhoC ε a - _root_.Formalism.REAL.rhoN ε a - ((n : ℝ) - 1) / 2 = m := by
  have h := card_same_diff_sign_lt_gt_add_one_eq ε a
  unfold _root_.Formalism.REAL.rhoC _root_.Formalism.REAL.rhoN
  refine ⟨-((#{b | b < a ∧ ε b = ε a} : ℕ) + (#{b | a < b ∧ ε b ≠ ε a} : ℕ) : ℤ), ?_⟩
  have hr : ((#{b | a < b ∧ ε b = ε a} : ℕ) : ℝ) + #{b | b < a ∧ ε b = ε a}
      + #{b | a < b ∧ ε b ≠ ε a} + #{b | b < a ∧ ε b ≠ ε a} + 1 = n := by
    exact_mod_cast h
  push_cast
  linear_combination hr / 2


open Finset in
theorem _root_.GlobalTheory.DSParam.isHCParam_of_isDS : ∀ (n : ℕ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H]
    (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    StrictAnti lam → _root_.Formalism.MainNotions.S.IsDS ε lam σ → _root_.Formalism.QuantumDeterminants.IsHCParam lam := by
  intro n H _ _ ε lam σ hlam hds
  unfold _root_.Formalism.MainNotions.S.IsDS at hds
  obtain ⟨-, -, -, -, -, ⟨S, hS⟩, -⟩ := hds
  unfold _root_.Formalism.MainNotions.S.IsKTypeOf at hS
  obtain ⟨-, -, -, ⟨v, -, hv0, hv⟩, -⟩ := hS
  unfold _root_.Formalism.QuantumDeterminants.IsHCParam
  refine ⟨hlam, fun a => ?_⟩
  obtain ⟨k, hk⟩ := exists_int_eq_weight_of_isWtOn (one_mem_Kset_divisor ε) hv0 hv a
  obtain ⟨m, hm⟩ := exists_int_rhoC_sub_rhoN_sub_half ε a
  refine ⟨k + m, ?_⟩
  have hl : _root_.Formalism.QuantumDeterminants.lowK ε lam a = lam a + _root_.Formalism.REAL.rhoN ε a - _root_.Formalism.REAL.rhoC ε a := by
    unfold _root_.Formalism.QuantumDeterminants.lowK; simp
  push_cast
  linarith

end GlobalTheory.DSParam
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem _root_.GlobalTheory.T.finite_fibre_correspondence_of_isFinite_first : ∀ (X Y₀ Y : Scheme.{0}) (s t : Y ⟶ X) (i : Y₀ ⟶ Y), IsFinite s → IsOpenImmersion i → IsDominant i → IsLocallyNoetherian Y → (∀ z : X, {u : X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ i ≫ s ∧ spMap (algebraMap V K) ≫ z' = x ≫ i ≫ t ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z}.Finite) → ∀ z : X, {y : Y | t y = z}.Finite := by
  first | (exact @GlobalTheory.FibreCrit.finite_fibre_of_isFinite) | (exact GlobalTheory.FibreCrit.finite_fibre_of_isFinite) | (intros; apply GlobalTheory.FibreCrit.finite_fibre_of_isFinite  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem _root_.GlobalTheory.T.finite_dvr_limits_correspondence_finite_snd : ∀ (X Y₀ S : Scheme.{0}) (q : X ⟶ S) (U : X.Opens) (s₀ t₀ : Y₀ ⟶ X) (gt : Y₀ ⟶ U.toScheme), IsSeparated q → IsAffine S → s₀ ≫ q = t₀ ≫ q → gt ≫ U.ι = t₀ → IsFinite gt → ∀ z : X, z ∈ U → {u : X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ s₀ ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z}.Finite := by
  first | (exact @GlobalTheory.UPel.HT.ES.finite_dvr_limits_of_finite_snd) | (exact GlobalTheory.UPel.HT.ES.finite_dvr_limits_of_finite_snd) | (intros; apply GlobalTheory.UPel.HT.ES.finite_dvr_limits_of_finite_snd  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem _root_.GlobalTheory.T.extension_over_normal_quasi_projective_base : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Y₀ Y X : Scheme.{0}) (i : Y₀ ⟶ Y) (σ : Y ⟶ Sp R) (τ : X ⟶ Sp R) (t₀ : Y₀ ⟶ X), IsOpenImmersion i → IsDominant i → IsLocallyNoetherian Y → IsReduced Y → (∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) → IsQProjOver τ → i ≫ σ = t₀ ≫ τ → (∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (y : Sp V ⟶ Y) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y = x ≫ i → ∃ z : Sp V ⟶ X, spMap (algebraMap V K) ≫ z = x ≫ t₀) → (∀ y : Y, {z : X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' : Sp V ⟶ Y) (z' : Sp V ⟶ X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ i ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧ y' (IsLocalRing.closedPoint V) = y ∧ z' (IsLocalRing.closedPoint V) = z}.Finite) → ∃ t : Y ⟶ X, i ≫ t = t₀ ∧ t ≫ τ = σ := by
  first | (exact @GlobalTheory.ExtendNormal.exists_extension) | (exact GlobalTheory.ExtendNormal.exists_extension) | (intros; apply GlobalTheory.ExtendNormal.exists_extension  <;> assumption)
end

section

open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.complexHessian_posSemidef_of_leviForm_nonneg : ∀ (n : ℕ) (φ : V n → ℝ) (z : V n), ContDiffAt ℝ 2 φ z → (∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun v => (φ v : ℂ)) z ξ).re) → (cHess n (fun v => (φ v : ℂ)) z).PosSemidef := by
  first | exact @GlobalTheory.cHess_posSemidef_of_levi_nonneg | exact GlobalTheory.cHess_posSemidef_of_levi_nonneg | (intros; apply GlobalTheory.cHess_posSemidef_of_levi_nonneg <;> assumption)
end
