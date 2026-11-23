module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle467
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWildInertiaGeneratingCyclotomicValue
public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle003
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle005
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle468
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle154
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle036
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleUniquenessCharacterisation
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle457
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle462
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle003
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle164
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle165
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
public import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SignsAndJumpSetsAtTypePrime
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
public import Formalism.SharpRestriction.ParConsts
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle469
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009

@[expose] public section

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

theorem _root_.GlobalTheory.T.maxLength_localInvariants_twisted_fractionModInteger_le : ∀ (D : D7) (i : D.nd.Loc) (col : Finset (HeightOneSpectrum (𝓞 D.host.E))), D.nd.l i ∉ D.host.small → D.nd.l i ≠ D.host.q → D.nd.l i ≠ D.host.d → (∀ u ∈ col, u ∈ placesOver D.host.E (D.nd.l i)) → ((h0 D.nd i col : ℚ) : ℝ) ≤ 2 * D.R.t := by
  first | exact @GlobalTheory.InvariantsKO.main | exact GlobalTheory.InvariantsKO.main | (intros; apply GlobalTheory.InvariantsKO.main <;> assumption)
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

theorem _root_.GlobalTheory.T.exists_wildInertia_generating_cyclotomicValue : ∀ (D : D7) (i : D.nd.Loc) (k : Fin 2), D.nd.l i = D.host.g k → ∃ g0 : GE D.nd, (∃ w ∈ placesOver D.host.E (D.nd.l i), g0 ∈ Ine (F := D.host.E) (D.nd.plOm.1 w)) ∧ (∃ u : ℤ_[D.nd.l i]ˣ, ((cycZ (F := D.host.E) (Ω := D.nd.Om) (D.nd.l i) g0 : ℤ_[D.nd.l i]ˣ) : ℤ_[D.nd.l i]) = 1 + (D.nd.l i : ℤ_[D.nd.l i]) ^ D.nd.s0 i * (u : ℤ_[D.nd.l i])) ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), g0 ∈ Ine (F := D.host.E) (D.nd.plOm.1 w) → g0 ∈ wildSet D.nd (D.nd.plOm.1 w) := by
  first | exact @GlobalTheory.WildCycGen.main | exact GlobalTheory.WildCycGen.main | (intros; apply GlobalTheory.WildCycGen.main <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary

theorem _root_.GlobalTheory.T.weightInfinitesimalCharacterParam_of_levelCompatible : ∀ (D : D7) (M : Formalism.L2.MtFam D) (tup : D.what₂.Tup → Fin D.R.m → Formalism.L2.Host.HChar D.host.E), Formalism.L2.LevelTied D M tup → (∀ t, D.naut.infG D.naut.etaT (Formalism.L2.embT D t) = {(1 / 2 : ℂ)}) → (∀ (i : D.nd.Loc) (a : Formalism.L2.NG.AlgWt D.host.E D.R.nV) (τ : D.host.E →+* ℂ) (lam : Fin D.R.nV → ℤ), (M.loc i).wt.IsDual a → a.HWAt τ lam → D.naut.infWt i τ = Formalism.L2.NG.infOf lam) → WeightParam D := by
  first | exact @GlobalTheory.WeightParamTie.weightParam_of_levelTied | exact GlobalTheory.WeightParamTie.weightParam_of_levelTied | (intros; apply GlobalTheory.WeightParamTie.weightParam_of_levelTied <;> assumption)
end

section

open Matrix Formalism.IndefR.Datum
open Classical

namespace GlobalTheory

theorem addChar_inv_isPrimitive_of_isPrimitive {k : Type} [Field k] {R : Type} [CommRing R] (ψ : AddChar k R)
    (hψ : ψ.IsPrimitive) : (ψ⁻¹).IsPrimitive := by
  intro a ha h
  apply hψ (neg_ne_zero.mpr ha)
  ext x
  have := DFunLike.congr_fun h x
  simpa [AddChar.mulShift_apply, AddChar.inv_apply, neg_mul] using this

theorem sum_addChar_trace_rectMatrix_mul {k : Type} [Field k] [Fintype k] {R : Type} [CommRing R] [IsDomain R]
    (ψ : AddChar k R) (hψ : ψ.IsPrimitive) {r t : ℕ} (m : Matrix (Fin t) (Fin r) k) :
    ∑ b : Matrix (Fin r) (Fin t) k, ψ (trace (b * m)) =
      if m = 0 then (Fintype.card k : R) ^ (r * t) else 0 := by
  split_ifs with hm
  · subst hm
    simp only [Matrix.mul_zero, trace_zero, AddChar.map_zero_eq_one, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one]
    rw [show Fintype.card (Matrix (Fin r) (Fin t) k) = Fintype.card (Fin r → Fin t → k) from rfl]
    simp [Fintype.card_fun, ← pow_mul, mul_comm]
  · obtain ⟨i, j, hij⟩ : ∃ i j, m i j ≠ 0 := by
      by_contra h; push_neg at h; exact hm (Matrix.ext h)
    have h1 := hψ hij
    obtain ⟨c, hc⟩ : ∃ c, ψ (m i j * c) ≠ 1 := by
      by_contra h; push_neg at h; apply h1; ext c; simp [AddChar.mulShift_apply, h]
    set a₀ : Matrix (Fin r) (Fin t) k := Matrix.single j i c
    have ha₀ : trace (a₀ * m) = m i j * c := by
      simp [a₀, Matrix.trace_single_mul, mul_comm]
    set S := ∑ a : Matrix (Fin r) (Fin t) k, ψ (trace (a * m))
    have hS : S = ψ (trace (a₀ * m)) * S := by
      rw [Finset.mul_sum]
      refine Fintype.sum_equiv (Equiv.subRight a₀) _ _ (fun a => ?_)
      simp only [Equiv.subRight_apply, ← AddChar.map_add_eq_mul, Matrix.sub_mul, trace_sub]
      congr 1; ring
    rw [ha₀] at hS
    have : (1 - ψ (m i j * c)) * S = 0 := by rw [sub_mul, one_mul, ← hS, sub_self]
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h).symm hc
    · exact h

variable {k : Type} [Field k] {r t : ℕ}

def squareAndRectColumnsEquivWideMatrix : Matrix (Fin r) (Fin r) k × Matrix (Fin r) (Fin t) k ≃ Matrix (Fin r) (Fin (r + t)) k where
  toFun p := fun i j => Fin.addCases (p.1 i) (p.2 i) j
  invFun y := (y.submatrix id (Fin.castAdd t), y.submatrix id (Fin.natAdd r))
  left_inv p := by
    ext i j
    · exact Fin.addCases_left (motive := fun _ => k) j
    · exact Fin.addCases_right (motive := fun _ => k) j
  right_inv y := by
    funext i j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp

theorem topLeftBlock_neg_eq_submatrix_castAdd (y : Matrix (Fin r) (Fin (r + t)) k) :
    topL r (-y) = -(y.submatrix id (Fin.castAdd t)) := by
  ext i j; simp only [topL]; rw [dite_eq_left ⟨i.2, by omega⟩]; rfl

theorem topLeftBlock_eq_submatrix_castAdd (u : Matrix (Fin (r + t)) (Fin r) k) :
    topL r u = u.submatrix (Fin.castAdd t) id := by
  ext i j; simp only [topL]; rw [dite_eq_left ⟨by omega, j.2⟩]; rfl

theorem lowZero_iff_submatrix_natAdd_eq_zero (u : Matrix (Fin (r + t)) (Fin r) k) :
    LowZero r u ↔ u.submatrix (Fin.natAdd r) id = 0 := by
  constructor
  · intro h; ext i j; exact h (Fin.natAdd r i) j (by simp) j.2
  · intro h i j hi _
    obtain ⟨i', rfl⟩ : ∃ i' : Fin t, i = Fin.natAdd r i' := ⟨⟨i.val - r, by omega⟩, Fin.ext (by simp; omega)⟩
    simpa using congr_fun (congr_fun h i') j

theorem trace_mul_split_castAdd_natAdd (y : Matrix (Fin r) (Fin (r + t)) k) (u : Matrix (Fin (r + t)) (Fin r) k) :
    trace (y * u) = trace (y.submatrix id (Fin.castAdd t) * u.submatrix (Fin.castAdd t) id) +
      trace (y.submatrix id (Fin.natAdd r) * u.submatrix (Fin.natAdd r) id) := by
  simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_add, Finset.sum_add_distrib]

theorem sum_GL_character_neg_det_addChar_trace (k : Type) [Field k] [Fintype k] (ψ : AddChar k ℂ) (ξ : kˣ →* ℂˣ) (r : ℕ)
    (w : Matrix (Fin r) (Fin r) k) :
    ∑ a : Matrix (Fin r) (Fin r) k, (if h : IsUnit (-a).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) * ψ (trace (a * w))
      = ∑ x : GL (Fin r) k, (((ξ⁻¹ (Matrix.GeneralLinearGroup.det x))⁻¹ : ℂˣ) : ℂ) *
          ψ⁻¹ (trace (w * (x : Matrix (Fin r) (Fin r) k))) := by
  symm
  refine Fintype.sum_of_injective (fun x : GL (Fin r) k => -(x : Matrix (Fin r) (Fin r) k))
    (fun x y e => Units.ext (neg_injective e)) _ _ ?_ ?_
  · intro a ha
    rw [dite_eq_right, zero_mul]
    intro h
    exact ha ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (-a) h.ne_zero, by simp⟩
  · intro x
    have hx : IsUnit (-(-(x : Matrix (Fin r) (Fin r) k))).det := by
      rw [neg_neg]; exact (Matrix.isUnit_iff_isUnit_det _).mp x.isUnit
    rw [dite_eq_left hx]
    have hu : hx.unit = Matrix.GeneralLinearGroup.det x := Units.ext (by simp)
    rw [hu, MonoidHom.inv_apply, inv_inv, AddChar.inv_apply, Matrix.trace_mul_comm w, neg_mul, trace_neg]

end GlobalTheory

namespace GlobalTheory

theorem fourier_flatDatum_finite : ∀ (k : Type) [Field k] [Fintype k] (ψ : AddChar k ℂ) (ξ : kˣ →* ℂˣ) (r n : ℕ), ψ.IsPrimitive → ξ ≠ 1 → ∃ (C : ℂ) (m : ℕ), C ≠ 0 ∧ IsIntegral ℤ C ∧ IsIntegral ℤ ((Fintype.card k : ℂ) ^ m * C⁻¹) ∧ ∀ u : Matrix (Fin n) (Fin r) k, (∑ y : Matrix (Fin r) (Fin n) k, (if h : IsUnit (topL r (-y)).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) * ψ (Matrix.trace (y * u))) = C * (if h : LowZero r u ∧ IsUnit (topL r u).det then ((ξ h.2.unit : ℂˣ) : ℂ) ^ (-1 : ℤ) else 0) := by
  intro k _ _ ψ ξ r n hψ hξ
  rcases lt_or_ge n r with hnr | hrn
  · refine ⟨1, 0, one_ne_zero, isIntegral_one, by simpa using isIntegral_one, fun u => ?_⟩
    have h1 : ∀ y : Matrix (Fin r) (Fin n) k, (topL r (-y)).det = 0 := fun y =>
      Matrix.det_eq_zero_of_column_eq_zero ⟨n, hnr⟩ (fun i => by simp [topL])
    have h2 : (topL r u).det = 0 := Matrix.det_eq_zero_of_row_eq_zero ⟨n, hnr⟩ (fun j => by simp [topL])
    rw [one_mul, dite_eq_right (by rintro ⟨-, h⟩; rw [h2] at h; exact not_isUnit_zero h)]
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [dite_eq_right (by rw [h1 y]; exact not_isUnit_zero), zero_mul]
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hrn
  have hψ' : (ψ⁻¹).IsPrimitive := addChar_inv_isPrimitive_of_isPrimitive ψ hψ
  have hξ' : ξ⁻¹ ≠ 1 := inv_ne_one.mpr hξ
  obtain ⟨hsing, hinv⟩ := GlobalTheory.matrixGaussSum_singular_and_invertible k ℂ ψ⁻¹ ξ⁻¹ r hψ' hξ'
  set G : ℂ := ∑ x : GL (Fin r) k, (((ξ⁻¹ (Matrix.GeneralLinearGroup.det x))⁻¹ : ℂˣ) : ℂ) *
    ψ⁻¹ (Matrix.trace (x : Matrix (Fin r) (Fin r) k)) with hG
  obtain ⟨hnorm, hGint, hGinv, -⟩ := GlobalTheory.T.galois_matrix_gaussSum_eq_char_pow_mul k ψ⁻¹ ξ⁻¹ r hψ' hξ' G rfl
  set q : ℂ := (Fintype.card k : ℂ) with hq
  have hq0 : q ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hG0 : G ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hnorm
    have : (0 : ℝ) < (Fintype.card k : ℝ) ^ (r ^ 2) := pow_pos (Nat.cast_pos.mpr Fintype.card_pos) _
    rw [← hnorm] at this
    norm_num at this
  refine ⟨q ^ (r * t) * G, r * t + r ^ 2, mul_ne_zero (pow_ne_zero _ hq0) hG0, ?_, ?_, fun u => ?_⟩
  · refine IsIntegral.mul (IsIntegral.pow ?_ _) hGint
    rw [hq]
    exact_mod_cast (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ ℂ (Fintype.card k : ℤ)))
  · have : q ^ (r * t + r ^ 2) * (q ^ (r * t) * G)⁻¹ = q ^ (r ^ 2) * G⁻¹ := by
      rw [pow_add, mul_inv]
      field_simp
    rw [this]
    exact hGinv

  set u₁ := u.submatrix (Fin.castAdd t) id
  set u₂ := u.submatrix (Fin.natAdd r) id
  have hsplit : ∀ p : Matrix (Fin r) (Fin r) k × Matrix (Fin r) (Fin t) k,
      ((if h : IsUnit (-p.1).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) * ψ (trace (p.1 * u₁))) *
        ψ (trace (p.2 * u₂)) =
      (if h : IsUnit (topL r (-(squareAndRectColumnsEquivWideMatrix p))).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) *
        ψ (Matrix.trace (squareAndRectColumnsEquivWideMatrix p * u)) := by
    intro p
    have e1 : (squareAndRectColumnsEquivWideMatrix p).submatrix id (Fin.castAdd t) = p.1 :=
      congrArg Prod.fst (squareAndRectColumnsEquivWideMatrix.symm_apply_apply p)
    have e2 : (squareAndRectColumnsEquivWideMatrix p).submatrix id (Fin.natAdd r) = p.2 :=
      congrArg Prod.snd (squareAndRectColumnsEquivWideMatrix.symm_apply_apply p)
    rw [mul_assoc, ← AddChar.map_add_eq_mul, trace_mul_split_castAdd_natAdd _ u, topLeftBlock_neg_eq_submatrix_castAdd, e1, e2]
  rw [← Fintype.sum_equiv squareAndRectColumnsEquivWideMatrix _ _ hsplit, Fintype.sum_prod_type]
  rw [show (∑ x : Matrix (Fin r) (Fin r) k, ∑ y : Matrix (Fin r) (Fin t) k,
      (if h : IsUnit (-(x, y).1).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) * ψ (trace ((x, y).1 * u₁)) *
        ψ (trace ((x, y).2 * u₂))) =
      (∑ x : Matrix (Fin r) (Fin r) k, (if h : IsUnit (-x).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) *
        ψ (trace (x * u₁))) * ∑ y : Matrix (Fin r) (Fin t) k, ψ (trace (y * u₂)) by
    rw [Finset.sum_mul_sum]]
  rw [sum_GL_character_neg_det_addChar_trace, sum_addChar_trace_rectMatrix_mul ψ hψ u₂]
  by_cases hu2 : u₂ = 0
  swap
  · rw [if_neg hu2, mul_zero, dite_eq_right (fun h => hu2 ((lowZero_iff_submatrix_natAdd_eq_zero u).mp h.1)), mul_zero]
  rw [if_pos hu2]
  by_cases hdet : IsUnit u₁.det
  swap
  · have h0 : u₁.det = 0 := by
      by_contra h; exact hdet (isUnit_iff_ne_zero.mpr h)
    rw [hsing u₁ h0, zero_mul, dite_eq_right, mul_zero]
    rintro ⟨-, h⟩
    rw [topLeftBlock_eq_submatrix_castAdd] at h
    exact hdet h
  have hh : LowZero r u ∧ IsUnit (topL r u).det := ⟨(lowZero_iff_submatrix_natAdd_eq_zero u).mpr hu2, by rw [topLeftBlock_eq_submatrix_castAdd]; exact hdet⟩
  rw [dite_eq_left hh]
  set a : GL (Fin r) k := Matrix.GeneralLinearGroup.mkOfDetNeZero u₁ hdet.ne_zero
  have ha := hinv a
  simp only [Matrix.one_mul] at ha
  have hau : (a : Matrix (Fin r) (Fin r) k) = u₁ := rfl
  rw [hau] at ha
  rw [ha, ← hG]
  have hunit : hh.2.unit = Matrix.GeneralLinearGroup.det a := Units.ext (by simp [hau, topLeftBlock_eq_submatrix_castAdd, u₁])
  rw [hunit, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, _root_.zpow_neg_one]
  ring

end GlobalTheory
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

theorem _root_.GlobalTheory.T.signs_and_jump_sets_at_type_prime : ∀ (D : D7) (L : SizeData₂ D) (ep : Bool), AdmissibleParameterJ.hodgeTateJumpsAtModulesForSign D ep → AdmissibleParameterJ.CloudCentreDistance L → AdmissibleParameterJ.jcCondition L → AdmissibleParameterJ.JumpAbsoluteBound L → (D.R.t : ℝ) ≤ L.sc.b → ∀ (i : D.nd.Loc) (k : Fin 2) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), D.nd.l i = D.host.g k → GoodR D.nd i r → ∃ (sg : HeightOneSpectrum (𝓞 D.host.E) → Bool) (U : HeightOneSpectrum (𝓞 D.host.E) → Finset ℤ), PairedCharacterCondition.SignOK i sg ∧ PairedCharacterCondition.HostJ i r ⌊L.etaSz⌋₊ (⌊3 * L.sc.b⌋₊ + 2) 0 sg U := by
  first | exact @GlobalTheory.HostJumpSets.main | exact GlobalTheory.HostJumpSets.main | (intros; apply GlobalTheory.HostJumpSets.main <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

theorem _root_.GlobalTheory.T.wachModule_uniqueness_characterisation : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), WachCharacterisation D HW F := by
  first | exact @GlobalTheory.NL.FrobeniusMatrixUniqueness.main | exact GlobalTheory.NL.FrobeniusMatrixUniqueness.main | (intros; apply GlobalTheory.NL.FrobeniusMatrixUniqueness.main <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.JointSix

theorem psiAt_psiW {D : D7} (C : NChoice D) (w : D.what₂.places.Pl) :
    BlochKatoReduction.Gen.psiAt (C.sd w) (KillingConditions.psiW C w) = GlobalTheory.PtCore.psiG D C w := by
  unfold KillingConditions.psiW GlobalTheory.PtCore.psiG
  cases h : C.sd w
  · ext g
    simp [BlochKatoReduction.Gen.psiAt]
  · simp [BlochKatoReduction.Gen.psiAt]

theorem main : GlobalTheory.TwSys.Cheb → ∀ (D : D7) (C : NChoice D)
    (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))),
    GlobalTheory.PtCore.PtFam D r ρ → NChTie D C → GlobalTheory.PtCore.TriplesGood D → GlobalTheory.PtCore.SameTwist D C →
    GlobalTheory.PtCore.GoodPtRow D → GlobalTheory.PtCore.ResAbsIrr D → KillingConditions.SignatureChoiceCondition ρ C := by
  intro hC D C r ρ hF hT hTr hS hG hR i _
  have hsel := GlobalTheory.PtSel.selCore hC D C hT hTr hG hR hS ρ
    (fun i π hπ => hF.pt i π (Formalism.L2.zgoodSub D i hπ))
  refine ⟨fun π hπ => ?_, ?_⟩
  · obtain ⟨s, h1, h2, h3, h4, -⟩ := hsel i π hπ
    refine ⟨s, h1, ?_⟩
    rw [h2, psiAt_psiW]
    exact ⟨h3, h4⟩
  · rw [Rat.cast_sum, ← hT.Q_eq i]
    exact Finset.sum_le_sum fun v hv => GlobalTheory.T.conductorRoot_sub_one_length_le_tameValue D C hT i v hv

end GlobalTheory.JointSix

end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.TwistLift GlobalTheory.TateTop

namespace GlobalTheory.TateTop

theorem tateH2_of_duality_loc (hT : Formalism.GaloisCohomology.LocalTateDualityK) :
    ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l), LocalTateTopDegree (P.PD K) := by
  intro l _ P K LL _ _ _ O _ _ hO L1 hL1
  obtain ⟨hΦ1, hΦ2⟩ := continuous_fixingSubgroupEquiv K.1
  set Φ := K.1.fixingSubgroupEquiv with hΦ
  have hcyc : IsCyc P.χQ := P.χQ_cyc
  let χZ : Formalism.GaloisCohomology.GK l K.1 →* ℤ_[l]ˣ := (cyclotomicCharacter (PadicAlgCl l) l).comp
      (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK l K.1) (PadicAlgCl l))
  have hχZ : ∀ g, ((χZ g : ℤ_[l]) : ℚ_[l]) = (P.χQ (Φ.symm g : GQ l) : ℚ_[l]) := fun g => by
    rw [isCyc_unique hcyc (isCyc_cycChar l)]; rfl
  have hχc : Continuous fun g => (χZ g : ℤ_[l]) := by
    rw [continuous_iff_coe]
    simp only [hχZ]
    exact hcyc.continuous.comp (continuous_subtype_val.comp hΦ1)
  obtain ⟨c, hc⟩ := exists_gen_all hχc fun r => by
    have : NeZero (l ^ (r + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    exact exists_gen hχc
      (hT l K.1 K.2 (r + 1) (ZMod (l ^ (r + 1))) (ReciprocityTheory.Gal.charRep (redChar χZ (r + 1)))
        (Nat.succ_pos _) (contAction_charRep _ ((continuous_toZModPow _).comp hχc))).1
      fun M _ _ _ _ _ rho hrho => (hT l K.1 K.2 (r + 1) M rho (Nat.succ_pos _) hrho).2.2.2.2
  have hcpt : CompactSpace (GK K) := Φ.symm.surjective.compactSpace hΦ1
  obtain ⟨ι, hι⟩ := exists_ringHom hO
  let : Module ℤ_[l] (LL ⧸ L1.T) := Module.compHom _ ι
  have : SMulCommClass ℤ_[l] O (LL ⧸ L1.T) := ⟨fun a o x => smul_comm (ι a) o x⟩
  have hs : ∀ (a : ℤ_[l]) (x : LL), a • (Submodule.Quotient.mk x : LL ⧸ L1.T) =
      Submodule.Quotient.mk (algebraMap ℚ_[l] LL a * x) := fun a x => by
    rw [← hι, ← Algebra.smul_def]
    rfl
  refine @h2_equiv_of_torsion_character l _ (GK K) _ _ _ _ _ _ hcpt _ (fun r => (hc r).transport Φ hΦ2 hΦ1)
    (fun x => ?_) O _ _ _ _ fun g x => ?_
  · obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨n, hn⟩ := exists_pow_smul_mem hO x
    refine ⟨n, ?_⟩
    rw [hs, Submodule.Quotient.mk_eq_zero, hL1]
    simpa using hn 1
  · obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [hs]
    have h1 := hχZ (Φ g)
    rw [show Φ.symm (Φ g) = g from Φ.symm_apply_apply g, ← P.PD_χ K g] at h1
    change Submodule.Quotient.mk (algebraMap ℚ_[l] LL ((P.PD K).χ g : ℚ_[l]) * x) = _
    rw [← h1]
    rfl

end GlobalTheory.TateTop
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.TateFilQuotTied

theorem tied_tate_fil_quot : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P),
    LocTied l P AI → ∀ K : FinExt l, Formalism.MainNotions.LocalSituation.TateFilteredInvariants (P.PD K) := by
  intro l _ P AI TT K LL _ _ _ O _ _ hO A hA a b z hz hg
  haveI := hO.2.1
  exact GlobalTheory.TateFilQuot.tied_invariant_mod l P AI TT K LL A.V A.ρ hA a b z hz hg

end GlobalTheory.TateFilQuotTied
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut

theorem _root_.GlobalTheory.T.exists_localPositionData_off_exceptional_primes : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ (a : Fm.Ix x), AdmissibleParameterJ.JumpConditions (Fm.L x a) → ∀ l : ℕ, l.Prime → LevelStarExponents.lStar (Fm.L x a) < (l : ℝ) → (5 ≤ l ∧ (Fm.D x a).R.t + 1 < l ∧ l ≠ (Fm.D x a).host.q ∧ l ≠ (Fm.D x a).host.d ∧ l ∉ (Fm.D x a).host.small) ∧ (l ∉ GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.Exc (Fm.L x a) → ∀ j : ℕ, 1 ≤ j → j ≤ (Fm.D x a).R.m → ∀ (n : ℕ) [NeZero n] (up : ZMod n → Bool) (τ : ZMod n → (Fm.D x a).what₂.Tau), ∃ (h w η : ZMod n → ℕ) (typ : ZMod n → Bool) (U : ZMod n → Multiset ℤ), tableLineDegreeTwo.PositionHyps l n (Fm.D x a).R.t h w η typ U ∧ ∀ (c : ZMod n) (b : ℤ), ((U c).count (b + w c) = 1 ↔ (b : ℚ) ∈ AdmissibleParameterJ.JW (Fm.D x a) (up c) j (τ c)) ∧ (U c).count (b + w c) ≤ 1) := by
  first | exact @GlobalTheory.LocalPositionData.position_data_exist | exact GlobalTheory.LocalPositionData.position_data_exist | (intros; apply GlobalTheory.LocalPositionData.position_data_exist <;> assumption)
end
