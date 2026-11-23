module

public import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle099
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Matrix.Spectrum
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle100
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalIndicesColumnRowLevelsExact
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle014
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle006
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle005
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle006
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.RealPlaceAnalysis.Bundle001
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat IsDedekindDomain

namespace GlobalTheory.FlagCoef

theorem coef_integral_of_flag {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}
    (Λ : Submodule (𝓞 E) S.V) (g : ℕ) {T : E} (F : LFlag S r T) (hc : IsFixedConv Λ g F)
    (j : ℕ) (x : S.V) (hx : x ∈ Xflag F j)
    (hP : ∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal →
      x ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal Λ)) :
    ∃ w : Fin r → E, x = ∑ c, w c • F.fl.e c ∧ (∀ c : Fin r, j ≤ c.val → w c = 0) ∧
      ∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → ∀ c, ∃ s : 𝓞 E, s ∉ P.asIdeal ∧
        ∃ o : 𝓞 E, (s : E) * w c = o := by
  classical
  have hxa : x ∈ Submodule.span E (F.fl.e '' {i | i.1 < j}) := hx
  obtain ⟨l, hl, hlx⟩ := (Finsupp.mem_span_image_iff_linearCombination E).1 hxa

  have hxw : x = ∑ i, l i • F.fl.e i := by
    rw [← hlx, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    intro i
    simp
  refine ⟨fun c => l c, hxw, ?_, ?_⟩
  · intro c hc
    by_contra h
    have hmem : c.val < j := hl (Finsupp.mem_support_iff.2 h)
    omega
  · intro P hgP c
    have := P.isPrime
    have key : ∀ {L : Submodule (𝓞 E) S.V} {y : S.V},
        y ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal L ↔ ∃ u ∈ P.asIdeal.primeCompl, u • y ∈ L := Iff.rfl

    obtain ⟨s, hs, hsx⟩ := key.1 (hP P hgP)
    have hxX : x ∈ Submodule.span E (Set.range F.fl.e) :=
      Submodule.span_mono (Set.image_subset_range _ _) hxa
    have hsX : s • x ∈ Formalism.MainNotions.S.Lat.XLam Λ F := by
      refine Submodule.mem_inf.2 ⟨hsx, ?_⟩
      exact Submodule.smul_of_tower_mem _ s hxX

    obtain ⟨cc, -, hc1, heq⟩ := hc.1 P
    have hloc : s • x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.MainNotions.S.Lat.XLam Λ F) :=
      key.2 ⟨1, P.asIdeal.primeCompl.one_mem, by rw [one_smul]; exact hsX⟩
    have hfun : (fun a => cc a • F.fl.e a) = F.fl.e :=
      funext fun a => by rw [hc1 hgP a, one_smul]
    rw [heq, hfun] at hloc
    obtain ⟨t, ht, htx⟩ := key.1 hloc
    obtain ⟨o, ho⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 htx
    have h1 : ∑ i, ((o i : 𝓞 E) : E) • F.fl.e i = t • s • x := by
      rw [← ho]
      refine Finset.sum_congr rfl fun i _ => ?_
      exact algebraMap_smul E (o i) (F.fl.e i)
    have h2 : t • s • x = ∑ i, (((t * s : 𝓞 E) : E) * l i) • F.fl.e i := by
      rw [← mul_smul, ← algebraMap_smul E (t * s) x, hxw, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_smul]
    have hsum : ∑ i, (((o i : 𝓞 E) : E) - ((t * s : 𝓞 E) : E) * l i) • F.fl.e i = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, h1, ← h2, sub_self]
    have hc0 := Fintype.linearIndependent_iff.1 F.fl.e_indep _ hsum c
    exact ⟨t * s, P.asIdeal.primeCompl.mul_mem ht hs, o c, (sub_eq_zero.1 hc0).symm⟩

end GlobalTheory.FlagCoef
end

section

noncomputable section

open MeasureTheory Matrix Formalism.MainNotions.S GlobalTheory.Ell
open scoped InnerProductSpace

namespace GlobalTheory.ConjTypeW

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

variable {k : ℕ}

theorem lowK_allPos (lam : Fin k → ℝ) (a : Fin k) :
    Formalism.QuantumDeterminants.lowK (allPos k) lam a = lam a - (((k : ℝ) - 1) / 2 - (a : ℕ)) := by
  have h1 : (Finset.univ.filter fun b : Fin k => a < b) = Finset.Ioi a := by ext b; simp
  have h2 : (Finset.univ.filter fun b : Fin k => b < a) = Finset.Iio a := by ext b; simp
  have h3 : (a : ℕ) + 1 ≤ k := a.2
  simp only [allPos, Formalism.QuantumDeterminants.lowK, Formalism.REAL.rhoN, Formalism.REAL.rhoC, Pi.sub_apply, Pi.add_apply, ne_eq, not_true_eq_false,
    and_false, and_true, Finset.filter_false, Finset.card_empty, h1, h2, Fin.card_Ioi, Fin.card_Iio]
  rw [show k - 1 - (a : ℕ) = k - ((a : ℕ) + 1) by omega, Nat.cast_sub h3]
  push_cast; ring

theorem lowK_neg_rev (u : Fin k → ℝ) :
    Formalism.QuantumDeterminants.lowK (allPos k) (fun i => -u (Fin.rev i)) = fun a => -Formalism.QuantumDeterminants.lowK (allPos k) u (Fin.rev a) := by
  funext a
  rw [lowK_allPos, lowK_allPos, Fin.val_rev, Nat.cast_sub a.2]
  push_cast
  ring

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

end GlobalTheory.ConjTypeW

namespace GlobalTheory.ConjTypeW

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

end GlobalTheory.ConjTypeW

namespace GlobalTheory.ConjTypeW

end GlobalTheory.ConjTypeW
end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory

theorem exists_kStable_of_mem_lowKSub (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (w : H)
    (hw : w ∈ lowKSub ε lam σ) :
    ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ IsKStableOn ε σ S ∧ w ∈ S := by
  classical
  obtain ⟨s, hs, hws⟩ := Submodule.mem_sSup_iff_exists_finset.1 hw
  refine ⟨⨆ i ∈ s, i, ?_, ?_, hws⟩
  · have hfg : (⨆ i ∈ s, i).FG := by
      refine Submodule.fg_biSup s (fun i => i) (fun i hi => ?_)
      obtain ⟨hfin, -⟩ := hs hi
      exact (Submodule.fg_iff_finiteDimensional i).2 hfin
    exact (Submodule.fg_iff_finiteDimensional _).1 hfg
  · intro g hg v hv
    have hle : (⨆ i ∈ s, i) ≤ (⨆ i ∈ s, i).comap ((σ g : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
      refine iSup₂_le fun i hi => ?_
      obtain ⟨-, hstab, -⟩ := hs hi
      intro x hx
      exact (le_iSup₂ (f := fun j (_ : j ∈ s) => j) i hi) (hstab g hg x hx)
    exact hle hv

theorem isKFin_of_mem_lowKSub : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (w : H), w ∈ lowKSub ε lam σ → IsKFin ε σ w := by
  intro n ε lam H _ _ σ w hw
  obtain ⟨S, hfin, hstab, hwS⟩ := exists_kStable_of_mem_lowKSub n ε lam H σ w hw
  exact ⟨S, hfin, hwS, hstab⟩

end GlobalTheory
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.LduBound

theorem norm_det_le {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (B : ℝ)
    (h : ∀ i j, ‖A i j‖ ≤ B) : ‖A.det‖ ≤ (Fintype.card ι).factorial * B ^ Fintype.card ι := by
  have := Matrix.det_le (A := A) (abv := NormedField.toAbsoluteValue ℂ) (x := B) h
  rw [nsmul_eq_mul] at this
  exact this

theorem det_minor {n : ℕ} (L R : Matrix (Fin n) (Fin n) ℂ) (hL : IsLoUni L)
    (hR : ∀ a b, b < a → R a b = 0) (i j : Fin n) :
    ((L * R).submatrix (fun a : {k : Fin n // k ≤ j} => if a.1 = j then i else a.1)
      (fun a : {k : Fin n // k ≤ j} => a.1)).det = L i j * ∏ k ∈ Finset.Iic j, R k k := by
  have hf : (L * R).submatrix (fun a : {k : Fin n // k ≤ j} => if a.1 = j then i else a.1)
      (fun a : {k : Fin n // k ≤ j} => a.1) =
      L.submatrix (fun a : {k : Fin n // k ≤ j} => if a.1 = j then i else a.1)
      (fun a : {k : Fin n // k ≤ j} => a.1) * R.submatrix (fun a : {k : Fin n // k ≤ j} => a.1)
      (fun a : {k : Fin n // k ≤ j} => a.1) := by
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.mul_apply]
    rw [← Fintype.sum_subtype_add_sum_subtype (fun k : Fin n => k ≤ j)]
    have : ∑ k : {k : Fin n // ¬ k ≤ j}, L (if a.1 = j then i else a.1) k.1 * R k.1 b.1 = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [hR k.1 b.1 (lt_of_le_of_lt b.2 (not_le.1 k.2)), mul_zero]
    rw [this, add_zero]
  rw [hf, Matrix.det_mul]
  congr 1
  · rw [Matrix.det_of_lowerTriangular]
    · rw [Finset.prod_eq_single (⟨j, le_rfl⟩ : {k : Fin n // k ≤ j})]
      · simp
      · intro b _ hb
        have : b.1 ≠ j := fun h => hb (Subtype.ext h)
        simp only [Matrix.submatrix_apply, if_neg this]
        exact (hL _ _).2 rfl
      · simp
    · intro a b hab
      have hab' : a.1 < b.1 := hab
      have : a.1 ≠ j := ne_of_lt (lt_of_lt_of_le hab' b.2)
      simp only [Matrix.submatrix_apply, if_neg this]
      exact (hL _ _).1 hab'
  · rw [Matrix.det_of_upperTriangular]
    · simp only [Matrix.submatrix_apply]
      exact (Finset.prod_subtype (Finset.Iic j) (fun k => Finset.mem_Iic) (fun k => R k k)).symm
    · intro a b hab
      exact hR _ _ hab

theorem norm_lower_le {n : ℕ} (L U : Matrix (Fin n) (Fin n) ℂ) (t : Fin n → ℂ) (B δ : ℝ)
    (hL : IsLoUni L) (hU : IsUpUni U) (hB : 1 ≤ B) (hδ : 0 < δ)
    (ht : ∀ l : Fin n, δ ≤ ‖∏ i ∈ Finset.Iic l, t i‖)
    (hZ : ∀ i j, ‖(L * Matrix.diagonal t * U) i j‖ ≤ B) (i j : Fin n) :
    ‖L i j‖ ≤ n.factorial * B ^ n / δ := by
  have h1 := det_minor L (Matrix.diagonal t * U) hL
    (fun a b hab => by rw [Matrix.diagonal_mul, (hU a b).1 hab, mul_zero]) i j
  have h2 : ∏ k ∈ Finset.Iic j, (Matrix.diagonal t * U) k k = ∏ k ∈ Finset.Iic j, t k :=
    Finset.prod_congr rfl fun k _ => by rw [Matrix.diagonal_mul, (hU k k).2 rfl, mul_one]
  rw [h2, ← Matrix.mul_assoc] at h1
  have h3 := norm_det_le ((L * Matrix.diagonal t * U).submatrix
    (fun a : {k : Fin n // k ≤ j} => if a.1 = j then i else a.1)
      (fun a : {k : Fin n // k ≤ j} => a.1)) B (fun a b => hZ _ _)
  rw [h1, norm_mul] at h3
  have hc : Fintype.card {k : Fin n // k ≤ j} ≤ n := by
    simpa using Fintype.card_subtype_le (fun k : Fin n => k ≤ j)
  have h4 : ((Fintype.card {k : Fin n // k ≤ j}).factorial : ℝ) * B ^ Fintype.card {k : Fin n // k ≤ j}
      ≤ n.factorial * B ^ n :=
    mul_le_mul (by exact_mod_cast Nat.factorial_le hc) (pow_le_pow_right₀ hB hc) (by positivity)
      (by positivity)
  rw [le_div_iff₀ hδ]
  exact (mul_le_mul_of_nonneg_left (ht j) (norm_nonneg _)).trans (h3.trans h4)

theorem norm_inv_le {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (hA : A.det = 1) (x : ℝ)
    (h : ∀ i j, ‖A i j‖ ≤ x) (i j : Fin (m + 1)) : ‖A⁻¹ i j‖ ≤ m.factorial * x ^ m := by
  rw [Matrix.inv_def, hA, Ring.inverse_one, one_smul, Matrix.adjugate_fin_succ_eq_det_submatrix,
    norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  simpa using norm_det_le (A.submatrix j.succAbove i.succAbove) x (fun a b => h _ _)

theorem ldu_bound (m : ℕ) : ∃ c : ℝ, 0 < c ∧ ∀ (L U : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (t : Fin (m + 1) → ℂ) (B δ : ℝ), IsLoUni L → IsUpUni U → 1 ≤ B → 0 < δ → δ ≤ 1 →
    (∀ l : Fin (m + 1), δ ≤ ‖∏ i ∈ Finset.Iic l, t i‖) →
    (∀ i j, ‖(L * Matrix.diagonal t * U) i j‖ ≤ B) →
    ∀ i j, ‖L i j‖ ≤ c * B ^ (m + 1) / δ ∧ ‖U i j‖ ≤ c * B ^ (m + 1) / δ ∧
      ‖L⁻¹ i j‖ ≤ c * (B ^ (m + 1) / δ) ^ m ∧ ‖U⁻¹ i j‖ ≤ c * (B ^ (m + 1) / δ) ^ m := by
  refine ⟨(m + 1).factorial + m.factorial * ((m + 1).factorial : ℝ) ^ m, by positivity, ?_⟩
  intro L U t B δ hL hU hB hδ _ ht hZ
  have hB0 : 0 < B := by linarith
  have h1 := norm_lower_le L U t B δ hL hU hB hδ ht hZ
  have h2 : ∀ i j, ‖U i j‖ ≤ (m + 1).factorial * B ^ (m + 1) / δ := fun i j =>
    norm_lower_le Uᵀ Lᵀ t B δ (fun a b => ⟨(hU b a).1, fun h => (hU b a).2 h.symm⟩)
      (fun a b => ⟨(hL b a).1, fun h => (hL b a).2 h.symm⟩) hB hδ ht
      (fun a b => by
        have : Uᵀ * Matrix.diagonal t * Lᵀ = (L * Matrix.diagonal t * U)ᵀ := by
          simp [Matrix.transpose_mul, Matrix.mul_assoc]
        rw [this]; exact hZ b a) j i
  have dL : L.det = 1 := by
    rw [Matrix.det_of_lowerTriangular L (fun a b hab => (hL a b).1 hab)]
    exact Finset.prod_eq_one fun k _ => (hL k k).2 rfl
  have dU : U.det = 1 := by
    rw [Matrix.det_of_upperTriangular (M := U) (fun a b hab => (hU a b).1 hab)]
    exact Finset.prod_eq_one fun k _ => (hU k k).2 rfl
  have e1 : ((m + 1).factorial : ℝ) * B ^ (m + 1) / δ ≤
      ((m + 1).factorial + m.factorial * ((m + 1).factorial : ℝ) ^ m) * B ^ (m + 1) / δ := by
    gcongr
    exact le_add_of_nonneg_right (by positivity)
  have e2 : (m.factorial : ℝ) * (((m + 1).factorial : ℝ) * B ^ (m + 1) / δ) ^ m ≤
      ((m + 1).factorial + m.factorial * ((m + 1).factorial : ℝ) ^ m) * (B ^ (m + 1) / δ) ^ m := by
    rw [mul_div_assoc, mul_pow, ← mul_assoc]
    gcongr
    exact le_add_of_nonneg_left (by positivity)
  exact fun i j => ⟨(h1 i j).trans e1, (h2 i j).trans e1, (norm_inv_le L dL _ h1 i j).trans e2,
    (norm_inv_le U dU _ h2 i j).trans e2⟩

end GlobalTheory.SgInf.LduBound
end

section

open MeasureTheory Formalism.MainNotions.S Formalism.BasicNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Classical

theorem _root_.GlobalTheory.T.discreteSeries_lowestKType_unit_unitary_formalDegree : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ → (∃ w, IsLowUnit ε lam σ w) ∧ (∀ (x : Formalism.REAL.UJ ε) a b, ⟪σ (uMat x) a, σ (uMat x) b⟫_ℂ = ⟪a, b⟫_ℂ) ∧ ∀ (c : NNReal) (d : ℝ) (w : H), 0 < c → ‖w‖ = 1 → IsFdeg ((c : ENNReal) • Formalism.REAL.muG ε) σ d → fdegOf (Formalism.REAL.muG ε) σ w = c * d := by
  first | exact @GlobalTheory.RowLev.isDS_lowUnit_unitary_fdegOf | exact GlobalTheory.RowLev.isDS_lowUnit_unitary_fdegOf | (intros; apply GlobalTheory.RowLev.isDS_lowUnit_unitary_fdegOf <;> assumption)
end

section

open Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S
open scoped ContDiff

theorem _root_.GlobalTheory.T.rightDerivative_smooth_on_indefinite_unitary_group : ∀ (n : ℕ) (H X : Matrix (Fin n) (Fin n) ℂ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (f : Matrix (Fin n) (Fin n) ℂ → E), Xᴴ * H + H * X = 0 → SmoothOnH H f → ContinuousOn f {g | inUH H g} ∧ SmoothOnH H (rdM X f) ∧ ∀ g, inUH H g → HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) (rdM X f g) 0 := by
  first | exact @GlobalTheory.rdM_smoothOnH | exact GlobalTheory.rdM_smoothOnH | (intros; apply GlobalTheory.rdM_smoothOnH <;> assumption)
end

section

open Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants

theorem _root_.GlobalTheory.T.leadMinor_exp_hermitian_eq_convex_exp_sum : ∀ (n : ℕ) (Y : Matrix (Fin n) (Fin n) ℂ) (hY : Y.IsHermitian) (l : ℕ) (hl : l ≤ n), ∃ w : Finset (Fin n) → ℝ, (∀ J, 0 ≤ w J) ∧ (∀ J, w J ≠ 0 → J.card = l) ∧ ∑ J, w J = 1 ∧ ∀ t : ℝ, leadMinor (NormedSpace.exp ((t : ℂ) • Y)) l hl = ((∑ J, w J * Real.exp (t * ∑ j ∈ J, hY.eigenvalues j) : ℝ) : ℂ) := by
  first | exact @GlobalTheory.LeadMinorExp.leadMinor_exp_eq_sum | exact GlobalTheory.LeadMinorExp.leadMinor_exp_eq_sum | (intros; apply GlobalTheory.LeadMinorExp.leadMinor_exp_eq_sum <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.localIndices_column_row_levels_exact : ∀ (D : D7) (i : Fin 2), StandardLattice.idxColLoc (D.host.g i) D.R.k = ∏ j ∈ Finset.Icc 1 D.R.k, ((D.host.g i : ℝ) ^ j - 1) ∧ StandardLattice.idxRowLoc (D.host.g i) D.R.k D.R.m = (∏ j ∈ Finset.range D.R.r, ((D.host.g i : ℝ) ^ D.R.r - (D.host.g i : ℝ) ^ j)) / ((D.host.g i : ℝ) ^ (D.R.rS * (2 * D.R.k + 2 * D.R.rS + 1)) * (D.host.g i : ℝ) ^ (D.R.k * (D.R.k - 1) / 2)) := by
  first | exact @GlobalTheory.idxColLoc_idxRowLoc_exact | exact GlobalTheory.idxColLoc_idxRowLoc_exact | (intros; apply GlobalTheory.idxColLoc_idxRowLoc_exact <;> assumption)
end

section

open MeasureTheory GlobalTheory.Dec
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace GlobalTheory.UniTrick

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem continuous_lin {ι : Type} [Fintype ι] (ρ : Representation ℂ G V)
    (hρ : ∀ (φ : V →ₗ[ℂ] ℂ) (v : V), Continuous fun g => φ (ρ g v))
    (f : V →ₗ[ℂ] EuclideanSpace ℂ ι) (v : V) : Continuous fun g => f (ρ g v) := by
  have h : ∀ i, Continuous fun g => (f (ρ g v)) i := fun i =>
    hρ ((EuclideanSpace.proj i : EuclideanSpace ℂ ι →L[ℂ] ℂ).toLinearMap ∘ₗ f) v
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi h)

variable [MeasurableSpace G] [BorelSpace G]

variable [CompactSpace G]

end GlobalTheory.UniTrick

namespace GlobalTheory

end GlobalTheory
end
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

theorem a_bounds_of_ge_two_n_pow_five : ∀ (k r : ℕ) (a : ℝ), 1 ≤ k → 2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 5 ≤ a → 2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 < a / 2 ∧ (2 * ((2 * (r ^ 2 + r + 1) : ℕ) : ℝ) * (2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2) + 1) + 2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + 1 ≤ a := by
  intro k r a hk ha
  have hM : ((2 * (r ^ 2 + r + 1) : ℕ) : ℝ) = 2 * ((r : ℝ) ^ 2 + r + 1) := by push_cast; ring
  rw [hM]
  generalize hN : ((2 * r + k + 1 : ℕ) : ℝ) = N at ha ⊢
  have hN' : N = 2 * (r : ℝ) + k + 1 := by rw [← hN]; push_cast; ring
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hr : (0 : ℝ) ≤ r := r.cast_nonneg
  have h2 : 2 ≤ N := by linarith
  have hrn : 2 * ((r : ℝ) + 1) ≤ N := by linarith
  have hN2 : 4 ≤ N ^ 2 := by nlinarith
  have hN3 : 8 ≤ N ^ 3 := by nlinarith
  have hN4 : 4 * N ^ 2 ≤ N ^ 4 := by nlinarith [mul_nonneg (sub_nonneg.mpr hN2) (sq_nonneg N)]
  have h5a : 8 * N ^ 2 ≤ N ^ 5 := by nlinarith [mul_nonneg (sub_nonneg.mpr hN3) (sq_nonneg N)]
  have h5b : 2 * N ^ 4 ≤ N ^ 5 := by nlinarith [mul_nonneg (sub_nonneg.mpr h2) (pow_nonneg (by linarith : (0:ℝ) ≤ N) 4)]
  have hm : 4 * ((r : ℝ) ^ 2 + r + 1) ≤ N ^ 2 := by nlinarith
  have hm2 : 4 * ((r : ℝ) ^ 2 + r + 1) * N ^ 2 ≤ N ^ 4 := by
    nlinarith [mul_le_mul_of_nonneg_right hm (sq_nonneg N)]
  constructor
  · nlinarith
  · nlinarith

end GlobalTheory.SgInf
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

theorem _root_.GlobalTheory.T.isRadical_span_prime_of_ncard_primesOver_eq_finrank : ∀ (E : Type) [Field E] [NumberField E] (p : ℕ), p.Prime → (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E → (Ideal.span {(p : 𝓞 E)}).IsRadical := by
  first | exact @GlobalTheory.SplitRadical.isRadical_span_of_ncard_primesOver | exact GlobalTheory.SplitRadical.isRadical_span_of_ncard_primesOver | (intros; apply GlobalTheory.SplitRadical.isRadical_span_of_ncard_primesOver <;> assumption)
end
