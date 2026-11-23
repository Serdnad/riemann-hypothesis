module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle250
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle216
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle077
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
import Formalism.LocalToGlobal.IndefiniteReal.Bundle009
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelSpanOverClasses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffHeckePolyOfComplex
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1917
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle216
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle226
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIso
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.LeafHypothesesConst
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1898
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOfBalanced
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1907
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle052
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle022
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle016
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import ReciprocityTheory.Automorphisms.Bundle001

@[expose] public section

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.UnitaryFactor

section Glue

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

def glue (e : A) (X Y : Matrix n n A) : Matrix n n A := e • X + (1 - e) • Y

theorem glue_apply (e : A) (X Y : Matrix n n A) (i j : n) :
    glue e X Y i j = e * X i j + (1 - e) * Y i j := by
  simp [glue, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

theorem glue_self (e : A) (X : Matrix n n A) : glue e X X = X := by
  rw [glue, ← add_smul]; simp

theorem glue_mul {e : A} (he : e * e = e) (X Y X' Y' : Matrix n n A) :
    glue e X Y * glue e X' Y' = glue e (X * X') (Y * Y') := by
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have h2 : (1 - e) * e = 0 := by rw [mul_comm, h1]
  have h3 : (1 - e) * (1 - e) = 1 - e := by linear_combination he
  simp only [glue, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, he, h1, h2, h3,
    zero_smul, add_zero, zero_add, smul_add]

theorem glue_map (f : A →+* A) (e : A) (X Y : Matrix n n A) :
    (glue e X Y).map f = glue (f e) (X.map f) (Y.map f) := by
  ext i j; simp [glue_apply, Matrix.map_apply]

theorem glue_transpose (e : A) (X Y : Matrix n n A) : (glue e X Y).transpose = glue e X.transpose Y.transpose := by
  ext i j; simp [glue_apply]

theorem prod_glue {e : A} (he : e * e = e) (s : Finset n) (f g : n → A) :
    ∏ i ∈ s, (e * f i + (1 - e) * g i) = e * ∏ i ∈ s, f i + (1 - e) * ∏ i ∈ s, g i := by
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro j s hj ih
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.prod_insert hj, ih]
    linear_combination (f j * ∏ i ∈ s, f i - g j * ∏ i ∈ s, f i - f j * ∏ i ∈ s, g i + g j * ∏ i ∈ s, g i) * he

theorem det_glue {e : A} (he : e * e = e) (X Y : Matrix n n A) :
    (glue e X Y).det = e * X.det + (1 - e) * Y.det := by
  rw [Matrix.det_apply', Matrix.det_apply', Matrix.det_apply', Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [glue_apply]
  rw [prod_glue he]
  ring

theorem exists_glue_left {e : A} (he : e * e = e) (g : GL n A) :
    ∃ U : GL n A, (U : Matrix n n A) = glue e (g : Matrix n n A) 1 ∧
      ((U⁻¹ : GL n A) : Matrix n n A) = glue e ((g⁻¹ : GL n A) : Matrix n n A) 1 :=
  ⟨⟨glue e (g : Matrix n n A) 1, glue e ((g⁻¹ : GL n A) : Matrix n n A) 1,
    by rw [glue_mul he, Units.mul_inv, Matrix.one_mul, glue_self],
    by rw [glue_mul he, Units.inv_mul, Matrix.one_mul, glue_self]⟩, rfl, rfl⟩

theorem exists_glue_right {e : A} (he : e * e = e) (g : GL n A) :
    ∃ U : GL n A, (U : Matrix n n A) = glue e 1 (g : Matrix n n A) ∧
      ((U⁻¹ : GL n A) : Matrix n n A) = glue e 1 ((g⁻¹ : GL n A) : Matrix n n A) :=
  ⟨⟨glue e 1 (g : Matrix n n A), glue e 1 ((g⁻¹ : GL n A) : Matrix n n A),
    by rw [glue_mul he, Units.mul_inv, Matrix.one_mul, glue_self],
    by rw [glue_mul he, Units.inv_mul, Matrix.one_mul, glue_self]⟩, rfl, rfl⟩

theorem glue_left_sub (e : A) (X : Matrix n n A) (i j : n) :
    glue e X 1 i j - (1 : Matrix n n A) i j = e * (X i j - (1 : Matrix n n A) i j) := by
  rw [glue_apply]; ring

theorem glue_right_sub (e : A) (X : Matrix n n A) (i j : n) :
    glue e 1 X i j - (1 : Matrix n n A) i j = (1 - e) * (X i j - (1 : Matrix n n A) i j) := by
  rw [glue_apply]; ring

theorem alg_sub_one {ε η u : A} (h2 : ε * η = 0) (h1' : η * η = η) :
    (1 - η) + η * u - 1 = (ε + η) * (η * (u - 1)) := by
  linear_combination (1 - u) * (h2 + h1')

theorem alg_norm {ε η u v : A} (h1 : ε * ε = ε) (h2 : ε * η = 0) (hu : u * v = 1) :
    (1 - η) + η * u = ((1 - (ε + η)) + (ε + η) * u) * ((1 - ε) + ε * v) := by
  linear_combination (-(1 - u - v + u * v)) * (h1 + h2) - ε * hu

theorem alg_inv {η u v : A} (h1' : η * η = η) (hu : u * v = 1) :
    ((1 - η) + η * u) * ((1 - η) + η * v) = 1 := by
  linear_combination (1 - u - v + u * v) * h1' + η * hu

end Glue

end GlobalTheory.UnitaryFactor

namespace GlobalTheory.UnitaryFactor

theorem one_mem_ohE (D : D7) {a : ℕ} (i j : Fin a) : (1 : Matrix (Fin a) (Fin a) (AE D)) i j ∈ OhE D := by
  rw [Matrix.one_apply]; split_ifs
  · exact one_mem _
  · exact zero_mem _



theorem exists_split_inert_factor : ∀ (D : D7) {a : ℕ} (k : GA D a), k ∈ intG D a → ∃ (ks ki : GA D a) (x : (AE D)ˣ), k = ks * ki ∧ ks ∈ intG D a ∧ ki ∈ intG D a ∧ SuppSplit D (ks : GL (Fin a) (AE D)) ∧ SuppInert D (ki : GL (Fin a) (AE D)) ∧ (∀ q : ℕ, q.Prime → InertQ D q → ZeroAt D q ((x : AE D) - 1)) ∧ x = Matrix.GeneralLinearGroup.det (ks : GL (Fin a) (AE D)) * sgU D x ∧ IntU D x ∧ ∃ η ∈ OhE D, (x : AE D) - 1 = η * (((Matrix.GeneralLinearGroup.det (k : GL (Fin a) (AE D)) : (AE D)ˣ) : AE D) - 1) := by
  intro D a k hk
  have hkI : IntG D (k : GL (Fin a) (AE D)) := (GlobalTheory.NormSum.mem_intG k).1 hk
  have hgu : (((k : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)).map (sgA D)).transpose *
      ((k : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)) = 1 :=
    (GlobalTheory.NormSum.PtsMem.mem_GA D _).1 k.2
  have hu : ((Matrix.GeneralLinearGroup.det (k : GL (Fin a) (AE D)) : (AE D)ˣ) : AE D) *
      sgA D ((Matrix.GeneralLinearGroup.det (k : GL (Fin a) (AE D)) : (AE D)ˣ) : AE D) = 1 :=
    GlobalTheory.NormSum.VacMove.det_norm D k
  have hum := GlobalTheory.NormSum.VacMove.det_int D _ hkI
  generalize hg : (k : GL (Fin a) (AE D)) = g at hkI hgu hu hum ⊢
  have hdg : ((Matrix.GeneralLinearGroup.det g : (AE D)ˣ) : AE D) = (g : Matrix (Fin a) (Fin a) (AE D)).det :=
    Matrix.GeneralLinearGroup.val_det_apply g
  generalize ((Matrix.GeneralLinearGroup.det g : (AE D)ˣ) : AE D) = u at hu hum hdg ⊢
  obtain ⟨ε, hε, h1, h2, h3⟩ := GlobalTheory.NormSum.VacMove.exists_half_idem D
  have hηε : sgA D (sgA D ε) = ε := GlobalTheory.NormSum.VacMove.sgA_sgA D ε
  have hηm : sgA D ε ∈ OhE D := GlobalTheory.NormSum.VacMove.sgA_mem D hε
  have h1' : sgA D ε * sgA D ε = sgA D ε := by rw [← map_mul, h1]
  generalize hη : sgA D ε = η at hηε hηm h1' h2 h3 ⊢
  have hPP : (ε + η) * (ε + η) = ε + η := by linear_combination h1 + h1' + 2 * h2
  have hPs : sgA D (ε + η) = ε + η := by rw [map_add (f := _), hη, hηε, add_comm]
  have hPm : ε + η ∈ OhE D := add_mem hε hηm
  have h1m : (1 : Matrix (Fin a) (Fin a) (AE D)).map (sgA D) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  obtain ⟨ks, hks1, hks2⟩ := exists_glue_left hPP g
  obtain ⟨ki, hki1, hki2⟩ := exists_glue_right hPP g
  have hksG : ks ∈ GA D a := by
    rw [GlobalTheory.NormSum.PtsMem.mem_GA, hks1, glue_map, hPs, h1m, glue_transpose, Matrix.transpose_one, glue_mul hPP, hgu,
      Matrix.one_mul, glue_self]
  have hkiG : ki ∈ GA D a := by
    rw [GlobalTheory.NormSum.PtsMem.mem_GA, hki1, glue_map, hPs, h1m, glue_transpose, Matrix.transpose_one, glue_mul hPP, hgu,
      Matrix.one_mul, glue_self]
  have hdet : ((Matrix.GeneralLinearGroup.det ks : (AE D)ˣ) : AE D) = (1 - (ε + η)) + (ε + η) * u := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hks1, det_glue hPP, Matrix.det_one, hdg]
    ring
  have hx : ((1 - η) + η * u) * ((1 - η) + η * sgA D u) = 1 := by
    exact alg_inv h1' hu
  obtain ⟨x, hx1, hx2⟩ : ∃ x : (AE D)ˣ, (x : AE D) = (1 - η) + η * u ∧
      ((x⁻¹ : (AE D)ˣ) : AE D) = (1 - η) + η * sgA D u :=
    ⟨⟨_, _, hx, by rw [mul_comm, hx]⟩, rfl, rfl⟩
  refine ⟨⟨ks, hksG⟩, ⟨ki, hkiG⟩, x, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Subtype.ext; apply Units.ext
    show ((k : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)) = (ks : Matrix (Fin a) (Fin a) (AE D)) * ki
    rw [hg, hks1, hki1, glue_mul hPP, Matrix.mul_one, Matrix.one_mul, glue_self]
  · exact (GlobalTheory.NormSum.mem_intG _).2 fun i j =>
      ⟨by rw [hks1, glue_apply]
          exact add_mem (mul_mem hPm (hkI i j).1) (mul_mem (sub_mem (one_mem _) hPm) (one_mem_ohE D i j)),
       by rw [hks2, glue_apply]
          exact add_mem (mul_mem hPm (hkI i j).2) (mul_mem (sub_mem (one_mem _) hPm) (one_mem_ohE D i j))⟩
  · exact (GlobalTheory.NormSum.mem_intG _).2 fun i j =>
      ⟨by rw [hki1, glue_apply]
          exact add_mem (mul_mem hPm (one_mem_ohE D i j)) (mul_mem (sub_mem (one_mem _) hPm) (hkI i j).1),
       by rw [hki2, glue_apply]
          exact add_mem (mul_mem hPm (one_mem_ohE D i j)) (mul_mem (sub_mem (one_mem _) hPm) (hkI i j).2)⟩
  · intro q hq hi i j
    show ZeroAt D q ((ks : Matrix (Fin a) (Fin a) (AE D)) i j - (1 : Matrix (Fin a) (Fin a) (AE D)) i j)
    rw [hks1, glue_left_sub]
    exact GlobalTheory.NormSum.VacMove.zeroAt_mul D hq ((h3 q hq).1 hi) _
  · intro q hq hi i j
    show ZeroAt D q ((ki : Matrix (Fin a) (Fin a) (AE D)) i j - (1 : Matrix (Fin a) (Fin a) (AE D)) i j)
    rw [hki1, glue_right_sub]
    exact GlobalTheory.NormSum.VacMove.zeroAt_mul D hq ((h3 q hq).2 hi) _
  · intro q hq hi
    have e : ((x : (AE D)ˣ) : AE D) - 1 = (ε + η) * (η * (u - 1)) := by
      rw [hx1]; exact alg_sub_one h2 h1'
    rw [e]
    exact GlobalTheory.NormSum.VacMove.zeroAt_mul D hq ((h3 q hq).1 hi) _
  · apply Units.ext
    show (x : AE D) = ((Matrix.GeneralLinearGroup.det ks : (AE D)ˣ) : AE D) * sgA D (x : AE D)
    have hs : sgA D ((1 - η) + η * u) = (1 - ε) + ε * sgA D u := by
      rw [map_add (sgA D), map_sub (sgA D), map_one (sgA D), map_mul (sgA D), hηε]
    rw [hdet, hx1, hs]
    exact alg_norm h1 h2 hu
  · refine ⟨?_, ?_⟩
    · rw [hx1]; exact add_mem (sub_mem (one_mem _) hηm) (mul_mem hηm hum)
    · rw [hx2]; exact add_mem (sub_mem (one_mem _) hηm) (mul_mem hηm (GlobalTheory.NormSum.VacMove.sgA_mem D hum))
  · refine ⟨η, hηm, ?_⟩
    rw [hx1]
    ring

end GlobalTheory.UnitaryFactor
end
end

section

open scoped Matrix GlobalTheory.VacAny ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

namespace GlobalTheory.HaarFactorOffPlace

theorem lintegral_factor {A V : Type} [AddCommGroup A] [MeasurableSpace A] [MeasurableAdd₂ A]
    [MeasurableNeg A] [AddCommGroup V] [MeasurableSpace V] [MeasurableAdd₂ V] [MeasurableNeg V]
    (μ : Measure A) (ν : Measure V) [SFinite μ] [SFinite ν] [μ.IsAddRightInvariant]
    [ν.IsAddRightInvariant] (c : A → V) (e : V → A) (hcm : Measurable c)
    (hce : ∀ y t, c (y + e t) = c y + t) (O : Set V) (hOm : MeasurableSet O)
    (hOneg : ∀ x, x ∈ O ↔ -x ∈ O) (hO : ν O = 1) (K : A → ℝ≥0∞) (hK : Measurable K)
    (hKe : ∀ y t, K (y + e t) = K y) (g : V → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ y, g (c y) * K y ∂μ = (∫⁻ t, g t ∂ν) * ∫⁻ y, O.indicator 1 (c y) * K y ∂μ := by
  have hχm : Measurable (O.indicator (1 : V → ℝ≥0∞)) := measurable_one.indicator hOm
  have hcs : ∀ y t, c (y - e t) = c y - t := fun y t => by
    have h := hce (y - e t) t
    rw [sub_add_cancel] at h
    rw [h, add_sub_cancel_right]
  have hKs : ∀ y t, K (y - e t) = K y := fun y t => by
    have h := hKe (y - e t) t
    rw [sub_add_cancel] at h
    exact h.symm
  have hχneg : ∀ x, O.indicator (1 : V → ℝ≥0∞) (-x) = O.indicator 1 x := fun x => by
    by_cases hx : x ∈ O
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((hOneg x).1 hx)]; rfl
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx ((hOneg x).2 h))]
  have hχint : ∫⁻ t, O.indicator 1 t ∂ν = 1 := by
    rw [lintegral_indicator_one hOm]; exact hO
  have hA : ∀ t, ∫⁻ y, g (c y) * K y ∂μ = ∫⁻ y, g (c y + t) * K y ∂μ := fun t => by
    rw [← lintegral_add_right_eq_self (fun y => g (c y) * K y) (e t)]
    simp only [hce, hKe]
  have hL : ∫⁻ y, g (c y) * K y ∂μ =
      ∫⁻ y, ∫⁻ s, O.indicator 1 (s - c y) * (g s * K y) ∂ν ∂μ := by
    calc ∫⁻ y, g (c y) * K y ∂μ
        = (∫⁻ t, O.indicator 1 t ∂ν) * ∫⁻ y, g (c y) * K y ∂μ := by rw [hχint, one_mul]
      _ = ∫⁻ t, O.indicator 1 t * ∫⁻ y, g (c y) * K y ∂μ ∂ν := (lintegral_mul_const _ hχm).symm
      _ = ∫⁻ t, O.indicator 1 t * ∫⁻ y, g (c y + t) * K y ∂μ ∂ν :=
          lintegral_congr fun t => by rw [← hA t]
      _ = ∫⁻ t, ∫⁻ y, O.indicator 1 t * (g (c y + t) * K y) ∂μ ∂ν :=
          lintegral_congr fun t =>
            (lintegral_const_mul _ ((hg.comp (hcm.add_const t)).mul hK)).symm
      _ = ∫⁻ y, ∫⁻ t, O.indicator 1 t * (g (c y + t) * K y) ∂ν ∂μ := by
          apply lintegral_lintegral_swap
          exact ((hχm.comp measurable_fst).mul
            ((hg.comp ((hcm.comp measurable_snd).add measurable_fst)).mul
              (hK.comp measurable_snd))).aemeasurable
      _ = ∫⁻ y, ∫⁻ s, O.indicator 1 (s - c y) * (g s * K y) ∂ν ∂μ := by
          refine lintegral_congr fun y => ?_
          rw [← lintegral_sub_right_eq_self (fun t => O.indicator 1 t * (g (c y + t) * K y)) (c y)]
          refine lintegral_congr fun s => ?_
          simp only [add_sub_cancel]
  have hM : ∀ s, ∫⁻ y, O.indicator 1 (c y) * K y ∂μ =
      ∫⁻ y, O.indicator 1 (s - c y) * K y ∂μ := fun s => by
    rw [← lintegral_sub_right_eq_self (fun y => O.indicator 1 (c y) * K y) (e s)]
    refine lintegral_congr fun y => ?_
    simp only [hcs, hKs]
    rw [← neg_sub, hχneg]
  rw [hL]
  calc ∫⁻ y, ∫⁻ s, O.indicator 1 (s - c y) * (g s * K y) ∂ν ∂μ
      = ∫⁻ s, ∫⁻ y, O.indicator 1 (s - c y) * (g s * K y) ∂μ ∂ν := by
        apply lintegral_lintegral_swap
        exact ((hχm.comp (measurable_snd.sub (hcm.comp measurable_fst))).mul
          ((hg.comp measurable_snd).mul (hK.comp measurable_fst))).aemeasurable
    _ = ∫⁻ s, g s * ∫⁻ y, O.indicator 1 (s - c y) * K y ∂μ ∂ν := by
        refine lintegral_congr fun s => ?_
        have hm : Measurable fun y => O.indicator (1 : V → ℝ≥0∞) (s - c y) * K y :=
          (hχm.comp (measurable_const.sub hcm)).mul hK
        rw [← lintegral_const_mul _ hm]
        refine lintegral_congr fun y => ?_
        ring
    _ = ∫⁻ s, g s * ∫⁻ y, O.indicator 1 (c y) * K y ∂μ ∂ν :=
        lintegral_congr fun s => by rw [← hM s]
    _ = (∫⁻ t, g t ∂ν) * ∫⁻ y, O.indicator 1 (c y) * K y ∂μ := lintegral_mul_const _ hg

end GlobalTheory.HaarFactorOffPlace

namespace GlobalTheory.HaarFactorOffPlace

theorem lintegral_evalV_mul_shiftInvariant : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [MeasurableSpace (κ → Af F)] [BorelSpace (κ → Af F)]
    (w : HeightOneSpectrum (𝓞 F)) [MeasurableSpace (κ → Fv F w)] [BorelSpace (κ → Fv F w)]
    (μf : Measure (κ → Af F)) [μf.IsAddHaarMeasure] (μw : Measure (κ → Fv F w)) [μw.IsAddHaarMeasure],
    μw {t | ∀ i, t i ∈ w.adicCompletionIntegers F} = 1 →
    ∀ (K : (κ → Af F) → ℝ≥0∞), Measurable K → (∀ (y : κ → Af F) (t : κ → Fv F w), K (fun i => y i + singleFin w (t i)) = K y) →
    ∀ (g : (κ → Fv F w) → ℝ≥0∞), Measurable g →
      ∫⁻ y, g (fun i => evalV F w (y i)) * K y ∂μf =
        (∫⁻ t, g t ∂μw) * ∫⁻ y, {t : κ → Fv F w | ∀ i, t i ∈ w.adicCompletionIntegers F}.indicator 1 (fun i => evalV F w (y i)) * K y ∂μf := by
  intro F _ _ κ _ _ _ w _ _ μf _ μw _ hO K hK hKinv g hg
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F w
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI : SecondCountableTopology (κ → Af F) := inferInstance
  haveI : SecondCountableTopology (κ → Fv F w) := inferInstance
  haveI : LocallyCompactSpace (κ → Af F) := inferInstance
  haveI : LocallyCompactSpace (κ → Fv F w) := inferInstance
  have hcont : Continuous fun (y : κ → Af F) (i : κ) => evalV F w (y i) :=
    continuous_pi fun i => (GlobalTheory.GaugeGlue.continuous_evalV w).comp (continuous_apply i)
  have hOc : IsClosed {t : κ → Fv F w | ∀ i, t i ∈ w.adicCompletionIntegers F} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun i =>
      (Valued.isClosed_integer (Fv F w)).preimage (continuous_apply i)
  refine lintegral_factor μf μw (fun y i => evalV F w (y i)) (fun t i => singleFin w (t i))
    hcont.measurable ?_ _ hOc.measurableSet ?_ hO K hK (fun y t => hKinv y t) g hg
  · intro y t
    funext i
    simp only [Pi.add_apply, map_add (f := _), evalV_singleFin_self]
  · intro x
    simp only [Set.mem_setOf_eq, Pi.neg_apply, neg_mem_iff]

end GlobalTheory.HaarFactorOffPlace
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound

namespace GlobalTheory.BaseKernelUniq

variable {D : D7}

theorem res_unique {χ : Formalism.L2.Host.HChar D.host.E} {P : Pl D.host.E} {c c' : (kP P)ˣ →* ℂˣ}
    (h : IsRes χ P c) (h' : IsRes χ P c') : c = c' := by
  refine MonoidHom.ext fun u => ?_
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : kP P)
  haveI : Nontrivial (kP P) := Ideal.Quotient.nontrivial_iff.2 P.isPrime.ne_top
  have ha0 : (a : D.host.E) ≠ 0 := by
    intro h0
    have h1 : a = 0 := RingOfIntegers.coe_eq_zero_iff.1 h0
    apply u.ne_zero
    rw [← ha, h1, map_zero]
  rw [h a (Units.mk0 _ ha0) u rfl ha.symm, h' a (Units.mk0 _ ha0) u rfl ha.symm]

theorem idemSum_unique (V : HSp D) {e e' : AE D} {P : Finset (Pl D.host.E)} (h : IsIdemSum e P)
    (h' : IsIdemSum e' P) : e = e' := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := h
  obtain ⟨⟨es', hes', rfl⟩, -⟩ := h'
  exact Finset.sum_congr rfl fun PP hP => (GlobalTheory.HeckeParts.idem_unique V (hes PP hP) (hes' PP hP)).symm

theorem omegaQ_congr {a b : ℕ} {Q : Finset (Pl D.host.E)} {ξ ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ}
    (hξ : ∀ PP ∈ Q, ξ PP = ξ' PP) (r : ℕ) (k : ℤ) (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) :
    omegaQ Q r ξ k y = omegaQ Q r ξ' k y := by
  unfold omegaQ
  split_ifs with hy
  · exact Finset.prod_congr rfl fun PP _ => by rw [hξ PP.1 PP.2]
  · rfl

theorem thPVec_unique {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Set (Fin S.rank → D.host.E)} {ΛT : Set (Fin T.rank → D.host.E)}
    {βS : GL (Fin S.rank) (Formalism.IndefR.Datum.EAf D)} {βT : GL (Fin T.rank) (Formalism.IndefR.Datum.EAf D)} {Pg Q : Finset (Pl D.host.E)}
    {ξ ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} {f₀ f f' : WO S T → ℂ}
    (h : IsThPVecOf ψ θ S T sS sT ΛS ΛT βS βT Pg Q ξ f₀ f) (h' : IsThPVecOf ψ θ S T sS sT ΛS ΛT βS βT Pg Q ξ' f₀ f')
    (hξ : ∀ PP ∈ Q, ξ PP = ξ' PP) : f = f' := by
  obtain ⟨-, e, he, hT⟩ := h
  obtain ⟨-, e', he', hT'⟩ := h'
  obtain rfl := idemSum_unique S he he'
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hT
  rw [hall Tm hTm, hT'.2 Tm hTm]
  congr 1
  funext x
  rw [omegaQ_congr hξ]

theorem baseKernelUnique : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → BaseKernelUnique R i v (ownAt D v) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F _ i v _ _ ω φ ω' φ' hk hk'
  obtain ⟨χ, ξR, hχ, hres, hω, hv⟩ := hk
  obtain ⟨χ', ξR', hχ', hres', hω', hv'⟩ := hk'
  obtain rfl : χ = χ' := (GlobalTheory.ChrEqUnique.chrEq_unique D).2.1 χ χ' _ hχ hχ'
  obtain rfl : φ = φ' := thPVec_unique hv hv' fun PP hP => res_unique (hres PP hP) (hres' PP hP)
  have hθφ := GlobalTheory.VecTheta.isThetaFunO_thPVec hv
  have hinf : IsInfFam R.θ := hv.1.2.inf
  funext h w u g
  exact congrFun (GlobalTheory.WeilUniq.weilDatum_unique D R.ψ hω.std _ _ _ _ ω ω' hω hω' (h, g) _
    (GlobalTheory.Chain.InnerSteps.theta_pureTensorO hω.std hinf _ _ _ _ hθφ _)) 0

end GlobalTheory.BaseKernelUniq

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LocLanglands GlobalTheory.WeilDeligne GlobalTheory.LocGL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TypeLawTransport

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
  {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'}
  {φ : Ω ≃+* Ω'} {j : E →+* E'} {i : w.adicCompletion E ≃+* w'.adicCompletion E'}

theorem monodromy_vanishing_iff_of_weil_deligne_rel {y : WD h} {y' : WD h'} (H : WDRel φ y y') : y.mono0 ↔ y'.mono0 := by
  obtain ⟨n, b, b', rfl, rfl, hN, -⟩ := H
  rw [WD.monodromyZero_ofWeilDeligneRepClass_iff, WD.monodromyZero_ofWeilDeligneRepClass_iff, hN]

theorem inePol_transport (P : PlaceIso A w A' w' φ j i) {y : WD h} {y' : WD h'} (H : WDRel φ y y')
    {σ : G E Ω} {σ' : G E' Ω'} (hr : ∀ z, φ (σ z) = σ' (φ z)) : y.inePol σ = y'.inePol σ' := by
  obtain ⟨c, -, -, hq, -⟩ := GlobalTheory.WeilTransport.weil_equiv E Ω A w h E' Ω' A' w' h' φ j i P
  have hmem : σ' ∈ Weil h' ↔ σ ∈ Weil h := by
    rw [mem_Weil, mem_Weil, hq]
    exact exists_congr fun a => exists_congr fun b => GlobalTheory.WeilTransport.actsAs_iff P.mem hr _ a b
  obtain ⟨n, b, b', rfl, rfl, -, hb⟩ := H
  by_cases hσ : σ ∈ Weil h
  · have hσ' := hmem.2 hσ
    rw [WD.inePol_of_mem _ hσ, WD.inePol_of_mem _ hσ', WD.charPol_mk, WD.charPol_mk, hb ⟨σ, hσ⟩ ⟨σ', hσ'⟩ hr]
  · have hσ' : σ' ∉ Weil h' := fun h1 => hσ (hmem.1 h1)
    rw [WD.inePol_of_not_mem _ hσ, WD.inePol_of_not_mem _ hσ']

end GlobalTheory.TypeLawTransport

end
end
