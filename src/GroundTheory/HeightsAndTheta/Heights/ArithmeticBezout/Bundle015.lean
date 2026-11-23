module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle014
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle011
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle009
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle013
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Lean.Meta.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodD
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar ptsIntegral ptsIntegralAt pot)

end GroundTheory.Heights₂.Heights
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix

noncomputable section

variable {n : ℕ}

def nrmGroups (h : HermNorm n) (k : ℕ) (u : Fin k × Fin n → ℂ) : Fin k × Fin n → ℂ :=
  fun ij => ((h.norm fun j => u (ij.1, j) : ℝ) : ℂ)⁻¹ * u ij

def consGroup {k : ℕ} (v : Fin n → ℂ) (w : Fin k × Fin n → ℂ) : Fin (k + 1) × Fin n → ℂ :=
  fun ij => Fin.cases (motive := fun _ => ℂ) (v ij.2) (fun i => w (i, ij.2)) ij.1

def IsAdmissible (Z : ProjCycle ℂ n) (u : Fin n → ℂ) : Prop :=
  ∀ W ∈ Z.support, linForm u ∉ W

def mahlerDefect (h : HermNorm n) (e : ℕ) (Z : ProjCycle ℂ n)
    (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (u : Fin n → ℂ) : ℝ :=
  mahler h e (specFirst f u) - cycleIntegral h Z e (fsLog h u)

structure IsChowCycleData (Z : ProjCycle ℂ n) (e δ : ℕ) (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) :
    Prop where

  prime : ∀ W ∈ Z.support, IsProjPrime W

  chow : IsChowFormCycle Z (e + 1) f

  homog : IsMultiHomog δ f

def MahlerSectionDim (e : ℕ) : Prop :=
  ∀ (n δ : ℕ) (h : HermNorm n) (Z : ProjCycle ℂ n) (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ)
    (u : Fin n → ℂ), IsChowCycleData Z e δ f → IsAdmissible Z u →
      mahler h e (specFirst f u) =
        mahler h (e + 1) f + δ * (harmonic (n - 1) : ℝ) / 2 + cycleIntegral h Z e (fsLog h u)

def DefectConstDim (e : ℕ) : Prop :=
  ∀ (n δ : ℕ) (h : HermNorm n) (Z : ProjCycle ℂ n) (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ)
    (u u' : Fin n → ℂ), IsChowCycleData Z e δ f → IsAdmissible Z u → IsAdmissible Z u' →
      mahlerDefect h e Z f u = mahlerDefect h e Z f u'

def MahlerSectionOfConst.Statement : Prop :=
  ∀ e : ℕ, DefectConstDim e → MahlerSectionDim e

def DefectAverage.Statement : Prop :=
  ∀ (n e δ : ℕ) (h : HermNorm n) (Z : ProjCycle ℂ n) (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ),
    IsChowCycleData Z e δ f →
      IntegrableOn (fun v => mahlerDefect h e Z f (nrmv h v)) (ballH h) ∧
        ⨍ v in ballH h, mahlerDefect h e Z f (nrmv h v) = mahler h (e + 1) f + δ * (harmonic (n - 1) : ℝ) / 2

def AdmissibleAE.Statement : Prop :=
  ∀ (n : ℕ) (Z : ProjCycle ℂ n), (∀ W ∈ Z.support, IsRelevant W) → ∀ᵐ u : Fin n → ℂ, IsAdmissible Z u

def AdmissibleAENrm.Statement : Prop :=
  ∀ (n : ℕ) (h : HermNorm n) (Z : ProjCycle ℂ n), (∀ W ∈ Z.support, IsRelevant W) →
    ∀ᵐ v ∂(volume.restrict (ballH h)), IsAdmissible Z (nrmv h v)

def BallVolume.Statement : Prop :=
  ∀ (n : ℕ) (h : HermNorm n), 0 < volume (ballH h) ∧ volume (ballH h) < ⊤

def MahlerAverageSplit.Statement : Prop :=
  ∀ (n e δ : ℕ) (h : HermNorm n) (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ), f ≠ 0 → IsMultiHomog δ f →
    IntegrableOn (fun v => mahler h e (specFirst f (nrmv h v))) (ballH h) ∧
      mahler h (e + 1) f = ⨍ v in ballH h, mahler h e (specFirst f (nrmv h v))

def MahlerIntegrand.Statement : Prop :=
  ∀ (n k δ : ℕ) (h : HermNorm n) (f : MvPolynomial (Fin k × Fin n) ℂ), f ≠ 0 → IsMultiHomog δ f →
    IntegrableOn (fun u => Real.log ‖eval (nrmGroups h k u) f‖) (ballProd h k)

def SphereMeanFubini.Statement : Prop :=
  ∀ (n k : ℕ) (h : HermNorm n) (G : (Fin (k + 1) × Fin n → ℂ) → ℝ),
    IntegrableOn (fun u => G (nrmGroups h (k + 1) u)) (ballProd h (k + 1)) →
      IntegrableOn (fun v => sphereMean h k (fun w => G (consGroup (nrmv h v) w))) (ballH h) ∧
        sphereMean h (k + 1) G = ⨍ v in ballH h, sphereMean h k (fun w => G (consGroup (nrmv h v) w))

def EvalSpecFirst.Statement : Prop :=
  ∀ (n k : ℕ) (f : MvPolynomial (Fin (k + 1) × Fin n) ℂ) (v : Fin n → ℂ) (w : Fin k × Fin n → ℂ),
    eval w (specFirst f v) = eval (consGroup v w) f

def CycleAverage.Statement : Prop :=
  ∀ (n e δ : ℕ) (h : HermNorm n) (Z : ProjCycle ℂ n) (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ),
    IsChowCycleData Z e δ f →
      IntegrableOn (fun v => cycleIntegral h Z e (fsLog h (nrmv h v))) (ballH h) ∧
        ⨍ v in ballH h, cycleIntegral h Z e (fsLog h (nrmv h v)) = -(δ * (harmonic (n - 1) : ℝ)) / 2

def ConeAverage.Statement : Prop :=
  ∀ (n e δ : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (g : MvPolynomial (Fin (e + 1) × Fin n) ℂ),
    IsProjPrime W → IsChowForm W (e + 1) g → IsMultiHomog δ g →
      IntegrableOn (fun v => coneIntegral h W e (fsLog h (nrmv h v))) (ballH h) ∧
        ⨍ v in ballH h, coneIntegral h W e (fsLog h (nrmv h v)) = -(δ * (harmonic (n - 1) : ℝ)) / 2

def ConeFubini.Statement : Prop :=
  ∀ (n : ℕ) (h : HermNorm n) (μ : Measure (EuclideanSpace ℂ (Fin n))) [IsFiniteMeasure μ]
    (F : (Fin n → ℂ) → EuclideanSpace ℂ (Fin n) → ℝ) (c M : ℝ),
    Measurable (Function.uncurry F) →
    (∀ᵐ y ∂μ, IntegrableOn (fun v => F v y) (ballH h) ∧ ∫ v in ballH h, |F v y| ≤ M ∧
      ⨍ v in ballH h, F v y = c) →
      IntegrableOn (fun v => ∫ y, F v y ∂μ) (ballH h) ∧
        ⨍ v in ballH h, ∫ y, F v y ∂μ = c * (μ Set.univ).toReal

def FsLogAverage.Statement : Prop :=
  ∀ (n : ℕ) (h : HermNorm n) (y : EuclideanSpace ℂ (Fin n)), y ≠ 0 →
    IntegrableOn (fun v => fsLog h (nrmv h v) (h.pointOf y)) (ballH h) ∧
      ∫ v in ballH h, |fsLog h (nrmv h v) (h.pointOf y)| =
        (harmonic (n - 1) : ℝ) / 2 * (volume (ballH h)).toReal ∧
      ⨍ v in ballH h, fsLog h (nrmv h v) (h.pointOf y) = -(harmonic (n - 1) : ℝ) / 2

def FsLogPointOf.Statement : Prop :=
  ∀ (n : ℕ) (h : HermNorm n) (v : Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n)),
    fsLog h (nrmv h v) (h.pointOf y) =
      fsLog (HermNorm.std n) (nrmv (HermNorm.std n) (h.mat *ᵥ v)) (fun i => y i)

def BallAverageLinear.Statement : Prop :=
  ∀ (n : ℕ) (h : HermNorm n) (φ : (Fin n → ℂ) → ℝ),
    (IntegrableOn (fun v => φ (h.mat *ᵥ v)) (ballH h) ↔ IntegrableOn φ (ballH (HermNorm.std n))) ∧
      ⨍ v in ballH h, φ (h.mat *ᵥ v) = ⨍ w in ballH (HermNorm.std n), φ w

def SphereMeanLinearBall.Statement : Prop :=
  ∀ (n : ℕ) (y : Fin n → ℂ), y ≠ 0 →
    IntegrableOn (fun w => fsLog (HermNorm.std n) (nrmv (HermNorm.std n) w) y) (ballH (HermNorm.std n)) ∧
      (∀ w, fsLog (HermNorm.std n) (nrmv (HermNorm.std n) w) y ≤ 0) ∧
      ⨍ w in ballH (HermNorm.std n), fsLog (HermNorm.std n) (nrmv (HermNorm.std n) w) y =
        -(harmonic (n - 1) : ℝ) / 2

def FsLogMeasurable.Statement : Prop :=
  ∀ (n : ℕ) (h : HermNorm n),
    Measurable (fun p : (Fin n → ℂ) × EuclideanSpace ℂ (Fin n) => fsLog h (nrmv h p.1) (h.pointOf p.2))

def ChowDegreePos.Statement : Prop :=
  ∀ (n k δ : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)) (g : MvPolynomial (Fin k × Fin n) ℂ),
    0 < k → IsProjPrime W → IsChowForm W k g → IsMultiHomog δ g → 1 ≤ δ

def SpecFirstHomog.Statement : Prop :=
  ∀ (n k δ : ℕ) (f : MvPolynomial (Fin (k + 1) × Fin n) ℂ) (u : Fin n → ℂ),
    IsMultiHomog δ f → IsMultiHomog δ (specFirst f u)

def ChowFormAssoc.Statement : Prop :=
  ∀ (F : Type) [Field F] (n k : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (g g' : MvPolynomial (Fin k × Fin n) F), IsChowForm I k g → IsChowForm I k g' →
      ∃ c : F, c ≠ 0 ∧ g' = C c * g

def ChowFormCycleAdd.Statement : Prop :=
  ∀ (F : Type) [Field F] (n k : ℕ) (Z₁ Z₂ : ProjCycle F n) (f₁ f₂ : MvPolynomial (Fin k × Fin n) F),
    IsChowFormCycle Z₁ k f₁ → IsChowFormCycle Z₂ k f₂ → IsChowFormCycle (Z₁ + Z₂) k (f₁ * f₂)

def ChowFormCycleSmul.Statement : Prop :=
  ∀ (F : Type) [Field F] (n k m : ℕ) (Z : ProjCycle F n) (f : MvPolynomial (Fin k × Fin n) F),
    IsChowFormCycle Z k f → IsChowFormCycle (m • Z) k (f ^ m)

namespace MahlerInhabit

end MahlerInhabit

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ChartZeroTrdeg

variable {F : Type} [Field F] {n : ℕ}

def homogAt (p : MvPolynomial (Fin n) F) (j : Fin n) (N : ℕ) : MvPolynomial (Fin n) F :=
  ∑ α ∈ p.support, monomial α (AddMonoidAlgebra.coeff p α) * X j ^ (N - α.sum fun _ e => e)

theorem aeval_homogAt {L : Type} [Field L] [Algebra F L] (p : MvPolynomial (Fin n) F) (j : Fin n)
    (N : ℕ) (hN : p.totalDegree ≤ N) (z : Fin n → L) (hz : z j ≠ 0) :
    aeval z (homogAt p j N) = z j ^ N * aeval (fun m => z m * (z j)⁻¹) p := by
  conv_rhs => rw [p.as_sum]

  rw [homogAt, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hk := (le_totalDegree hα).trans hN
  simp only [map_mul, aeval_monomial, map_pow, aeval_X, mul_pow, Finsupp.prod_mul]
  have hc : (α.prod fun a => HPow.hPow (z j)⁻¹) = (z j)⁻¹ ^ (α.sum fun _ e => e) := by
    simp only [Finsupp.prod, Finsupp.sum]
    exact Finset.prod_pow_eq_pow_sum _ _ _
  rw [hc]
  have : z j ^ N = z j ^ (N - α.sum fun _ e => e) * z j ^ (α.sum fun _ e => e) := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  rw [this, inv_pow]
  field_simp

theorem aeval_genPt_eq_zero_iff' (P : Ideal (MvPolynomial (Fin n) F)) (f : MvPolynomial (Fin n) F) :
    aeval (genPt P) f = 0 ↔ f ∈ P := by
  have h : aeval (genPt P) = (IsScalarTower.toAlgHom F (MvPolynomial (Fin n) F ⧸ P)
      (FractionRing (MvPolynomial (Fin n) F ⧸ P))).comp (Ideal.Quotient.mkₐ F P) :=
    MvPolynomial.algHom_ext fun i => by simp [genPt]
  rw [h]
  change algebraMap _ (FractionRing (MvPolynomial (Fin n) F ⧸ P)) (Ideal.Quotient.mk P f) = 0 ↔ _
  rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]

end ChartZeroTrdeg


open ChartZeroTrdeg in
theorem ChartZeroTrdeg.proof (hA : AffineChartTrdeg.Statement) : ChartZeroTrdeg.Statement := by
  intro F _ n d Q hQ hdim Ω _ _ y j hy hyj
  have := hQ.isPrime
  have hXj : X j ∉ Q := fun h => hyj (by simpa using hy _ h)
  set ξ := genPt Q
  have hξ : ξ j ≠ 0 := fun h => hXj ((aeval_genPt_eq_zero_iff' Q (X j)).1 (by simpa using h))
  set gξ := aeval (R := F) (fun m => ξ m * (ξ j)⁻¹)
  set gy := aeval (R := F) (fun m => y m * (y j)⁻¹)
  have hker : ∀ p, gξ p = 0 → gy p = 0 := by
    intro p hp
    have hH : homogAt p j p.totalDegree ∈ Q := by
      rw [← aeval_genPt_eq_zero_iff', aeval_homogAt p j _ le_rfl ξ hξ]
      simp [gξ] at hp
      simp [hp]
    have := hy _ hH
    rw [aeval_homogAt p j _ le_rfl y hyj] at this
    simpa [gy, hyj] using this
  have hAξ := hA F n d Q j hQ hdim hXj
  rw [Algebra.adjoin_range_eq_range_aeval] at hAξ ⊢
  let e := Ideal.quotientKerAlgEquivOfSurjective gξ.rangeRestrict_surjective
  let φ := Ideal.Quotient.liftₐ (RingHom.ker gξ.rangeRestrict) gy.rangeRestrict fun p hp => by
    apply Subtype.ext
    exact hker p (congrArg Subtype.val hp)
  have hφ : Function.Surjective φ := by
    intro b
    obtain ⟨p, hp⟩ := gy.rangeRestrict_surjective b
    exact ⟨Ideal.Quotient.mk _ p, hp⟩
  have := trdeg_le_of_surjective (φ.comp e.symm.toAlgHom) (hφ.comp e.symm.surjective)
  exact this.trans hAξ.le

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem localMult_map_of_flat {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] (J W : Ideal A) [W.IsPrime] (W' : Ideal B) [W'.IsPrime] [W'.LiesOver W]
    (hfib : (W.map (algebraMap A B)).map (algebraMap B (Localization.AtPrime W')) =
      IsLocalRing.maximalIdeal (Localization.AtPrime W')) :
    localMult (J.map (algebraMap A B)) W' = localMult J W := by
  let := Localization.AtPrime.algebraOfLiesOver W W'
  have : IsLocalHom (algebraMap (Localization.AtPrime W) (Localization.AtPrime W')) :=
    Localization.isLocalHom_localRingHom _ _ _ _
  have htow : (algebraMap (Localization.AtPrime W) (Localization.AtPrime W')).comp
      (algebraMap A (Localization.AtPrime W)) =
      (algebraMap B (Localization.AtPrime W')).comp (algebraMap A B) := by
    ext x
    exact Localization.localRingHom_to_map _ _ _ Ideal.LiesOver.over x
  have hmap : ∀ I : Ideal A, (I.map (algebraMap A (Localization.AtPrime W))).map
      (algebraMap (Localization.AtPrime W) (Localization.AtPrime W')) =
      (I.map (algebraMap A B)).map (algebraMap B (Localization.AtPrime W')) := by
    intro I
    rw [Ideal.map_map, Ideal.map_map, htow]
  have key := IsLocalRing.length_baseChange (Localization.AtPrime W) (Localization.AtPrime W')
    (Localization.AtPrime W ⧸ J.map (algebraMap A (Localization.AtPrime W)))
  rw [← (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (Localization.AtPrime W')
    (J.map (algebraMap A (Localization.AtPrime W)))).toLinearEquiv.length_eq, hmap,
    ← IsLocalization.AtPrime.map_eq_maximalIdeal W (Localization.AtPrime W), hmap, hfib] at key
  have : IsSimpleModule (Localization.AtPrime W')
      (Localization.AtPrime W' ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime W')) :=
    isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp (IsLocalRing.maximalIdeal.isMaximal _))
  rw [Module.length_eq_one (R := Localization.AtPrime W')
    (M := Localization.AtPrime W' ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime W')), mul_one] at key
  unfold localMult
  rw [dite_eq_left ‹W'.IsPrime›, dite_eq_left ‹W.IsPrime›, key]

section MinimalPrimes

variable {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
  (hc : ∀ I : Ideal A, I.IsPrime → ∀ P ∈ (I.map f).minimalPrimes, P.comap f = I)
include hc

theorem comap_mem_minimalPrimes {J : Ideal A} {P : Ideal B} (hP : P ∈ (J.map f).minimalPrimes) :
    P.comap f ∈ J.minimalPrimes ∧ P ∈ ((P.comap f).map f).minimalPrimes := by
  have hPp : P.IsPrime := hP.1.1
  obtain ⟨W₀, hW₀, hW₀le⟩ :=
    Ideal.exists_minimalPrimes_le (Ideal.map_le_iff_le_comap.mp hP.1.2)
  have hW₀p : W₀.IsPrime := hW₀.1.1
  obtain ⟨P₀, hP₀, hP₀le⟩ :=
    Ideal.exists_minimalPrimes_le (Ideal.map_le_iff_le_comap.mpr hW₀le)
  have hP₀p : P₀.IsPrime := hP₀.1.1
  have hEq : P₀ = P :=
    le_antisymm hP₀le (hP.2 ⟨hP₀p, (Ideal.map_mono hW₀.1.2).trans hP₀.1.2⟩ hP₀le)
  subst hEq
  rw [hc W₀ hW₀p P₀ hP₀]
  exact ⟨hW₀, hP₀⟩

theorem mem_minimalPrimes_map {J W : Ideal A} (hW : W ∈ J.minimalPrimes) {P : Ideal B}
    (hP : P ∈ (W.map f).minimalPrimes) : P ∈ (J.map f).minimalPrimes := by
  have hWp : W.IsPrime := hW.1.1
  have hPp : P.IsPrime := hP.1.1
  refine ⟨⟨hPp, (Ideal.map_mono hW.1.2).trans hP.1.2⟩, fun Q hQ hQP => ?_⟩
  have hQp : Q.IsPrime := hQ.1
  obtain ⟨Q₀, hQ₀, hQ₀le⟩ := Ideal.exists_minimalPrimes_le hQ.2
  obtain ⟨h1, -⟩ := comap_mem_minimalPrimes f hc hQ₀
  have hle : Q₀.comap f ≤ W := by
    rw [← hc W hWp P hP]
    exact Ideal.comap_mono (hQ₀le.trans hQP)
  have hWQ : W ≤ Q₀.comap f := hW.2 h1.1 hle
  have hQ₀p : Q₀.IsPrime := hQ₀.1.1
  exact (hP.2 ⟨hQ₀p, Ideal.map_le_iff_le_comap.mpr hWQ⟩ (hQ₀le.trans hQP)).trans hQ₀le

end MinimalPrimes

theorem isRelevant_comap_map_iff {K L : Type*} [CommRing K] [CommRing L] (σ : K →+* L) {n : ℕ}
    (P : Ideal (MvPolynomial (Fin n) L)) :
    IsRelevant (P.comap (MvPolynomial.map σ)) ↔ IsRelevant P := by
  simp [IsRelevant, Ideal.mem_comap, MvPolynomial.map_X]

theorem fundCycle_apply {R : Type*} [CommRing R] [IsNoetherianRing R] {n : ℕ}
    (J W : Ideal (MvPolynomial (Fin n) R)) [Decidable (W ∈ relComps J)] :
    fundCycle J W = if W ∈ relComps J then localMult J W else 0 := by
  unfold fundCycle
  rw [Finsupp.onFinset_apply]
  congr

theorem FundCycleBaseChange.proof (h : MinimalPrimeComap.Statement) : FundCycleBaseChange.Statement := by
  classical
  intro K L _ _ _ σ n J
  have hc : ∀ I : Ideal (MvPolynomial (Fin n) K), I.IsPrime →
      ∀ P ∈ (I.map (MvPolynomial.map σ)).minimalPrimes, P.comap (MvPolynomial.map σ) = I :=
    fun I hI P hP => h K L σ (Fin n) I hI P hP
  have hrad := RadicalBaseChange.proof
  let := σ.toAlgebra
  let := MvPolynomial.algebraMvPolynomial (σ := Fin n) (R := K) (S := L)
  have : Module.Flat (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) L) :=
    Module.Flat.isBaseChange (R := K) (S := MvPolynomial (Fin n) K) (M := L)
      (N := MvPolynomial (Fin n) L) (h := Algebra.IsPushout.out (R := K) (S := MvPolynomial (Fin n) K) (R' := L)
        (S' := MvPolynomial (Fin n) L))
  have hsupp : ∀ W ∈ (fundCycle J).support, W ∈ relComps J := by
    intro W hW
    by_contra hn
    exact Finsupp.mem_support_iff.mp hW (by rw [fundCycle_apply, if_neg hn])
  have hone : ∀ W : Ideal (MvPolynomial (Fin n) K), W.IsPrime → ∀ P,
      P ∈ relComps (W.map (MvPolynomial.map σ)) → localMult (W.map (MvPolynomial.map σ)) P = 1 :=
    fun W hW P hP => localMult_eq_one_of_isRadical (hrad K L σ (Fin n) W hW.isRadical) hP.1
  ext P
  rw [Finsupp.finsetSum_apply, fundCycle_apply]
  simp only [Finsupp.smul_apply, smul_eq_mul]
  split_ifs with hP
  · obtain ⟨hWmin, hPW⟩ := comap_mem_minimalPrimes _ hc hP.1
    have hWrel : P.comap (MvPolynomial.map σ) ∈ relComps J :=
      ⟨hWmin, (isRelevant_comap_map_iff σ P).mpr hP.2⟩
    have hWp : (P.comap (MvPolynomial.map σ)).IsPrime := hWmin.1.1
    have hPp : P.IsPrime := hP.1.1.1
    have : P.LiesOver (P.comap (MvPolynomial.map σ)) := ⟨rfl⟩
    have hmult : localMult (J.map (MvPolynomial.map σ)) P =
        localMult J (P.comap (MvPolynomial.map σ)) :=
      localMult_map_of_flat J _ P (map_eq_maximalIdeal_of_isRadical
        (hrad K L σ (Fin n) _ hWp.isRadical) hPW)
    rw [hmult, Finset.sum_eq_single (P.comap (MvPolynomial.map σ))]
    · rw [fundCycle_apply J, if_pos hWrel,
        fundCycle_apply (Ideal.map (MvPolynomial.map σ) (P.comap (MvPolynomial.map σ))) P,
        if_pos ⟨hPW, hP.2⟩, hone _ hWp P ⟨hPW, hP.2⟩, mul_one]
    · intro W₀ hW₀ hne
      rw [fundCycle_apply (Ideal.map (MvPolynomial.map σ) W₀) P, if_neg, mul_zero]
      intro hPW₀
      exact hne (hc W₀ (hsupp W₀ hW₀).1.1.1 P hPW₀.1).symm
    · intro hW
      rw [Finsupp.notMem_support_iff.mp hW, zero_mul]
  · refine (Finset.sum_eq_zero fun W hW => ?_).symm
    rw [fundCycle_apply (Ideal.map (MvPolynomial.map σ) W) P, if_neg, mul_zero]
    intro hPW
    exact hP ⟨mem_minimalPrimes_map _ hc (hsupp W hW).1 hPW.1, hPW.2⟩

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem ConeKrullDimLe.proof (hDim : ConeFiniteFibreDim.Statement) : ConeKrullDimLe.Statement :=
  fun n m h J hJ hm hmn hae => hDim n m h J hJ hm hmn hae

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ProjChowNonzero.Statement : Prop :=
  ∀ (n e : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)) (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ)
    (A : Matrix (Fin (e + 1)) (Fin n) ℂ),
    IsProjPrime W → IsChowForm W (e + 1) f → ComplexSets.IsFiniteProjection W A →
      eval (fun j => projPar A (.inr j))
        (Vertical.specRest (algebraMap ℂ (FractionRing (MvPolynomial (Fin (e + 1)) ℂ))) f (projPar A)) ≠ 0

end

end GroundTheory.Heights₂.Heights
end
