module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle047
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle048
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle049
public import Mathlib.Order.CompletePartialOrder
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle050
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
public import Mathlib.RingTheory.GradedAlgebra.Radical
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Finiteness.Ideal

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : ℕ}

theorem leadIdeal_isHomogeneous (J : Ideal (MvPolynomial (Fin n) ℂ)) :
    (leadIdeal J).IsHomogeneous (homogeneousSubmodule (Fin n) ℂ) :=
  Ideal.homogeneous_span _ _ (by
    rintro _ ⟨f, -, rfl⟩
    exact ⟨f.totalDegree, (mem_homogeneousSubmodule _ _).2 (homogeneousComponent_isHomogeneous _ _)⟩)

theorem linIdeal_isHomogeneous {d : ℕ} (A : Matrix (Fin d) (Fin n) ℂ) :
    (linIdeal A).IsHomogeneous (homogeneousSubmodule (Fin n) ℂ) :=
  Ideal.homogeneous_span _ _ (by
    rintro _ ⟨i, rfl⟩
    exact ⟨1, (mem_homogeneousSubmodule _ _).2
      (IsHomogeneous.sum _ _ _ (fun j _ => (isHomogeneous_X ℂ j).C_mul (A i j)))⟩)

theorem linIdeal_cons {k : ℕ} (A : Matrix (Fin k) (Fin n) ℂ) (B : Matrix (Fin 1) (Fin n) ℂ) :
    linIdeal (Matrix.of (Fin.cons (B 0) A : Fin (k + 1) → Fin n → ℂ)) = linIdeal A ⊔ linIdeal B := by
  have h : linPoly (Matrix.of (Fin.cons (B 0) A : Fin (k + 1) → Fin n → ℂ)) =
      Fin.cons (linPoly B 0) (linPoly A) := by
    funext i
    exact Fin.cases rfl (fun i => rfl) i
  have hB : Set.range (linPoly B) = {linPoly B 0} := by
    rw [Set.range_unique]
    rfl
  rw [linIdeal, linIdeal, linIdeal, h, Fin.range_cons, hB, Set.insert_eq, Ideal.span_union, sup_comm]

theorem ConeAvoidsExists.proof (hlead : LeadIdealDim.Statement) (hcut : LinearFormCut.Statement)
    (hpow : HomogDimZeroPow.Statement) : ConeAvoidsExists.Statement := by
  intro n d J _ hd
  have key : ∀ k, k ≤ d → ∃ A : Matrix (Fin k) (Fin n) ℂ,
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (leadIdeal J ⊔ linIdeal A)) ≤
        ((d - k : ℕ) : WithBot ℕ∞) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨0, ?_⟩
      have h0 : linIdeal (0 : Matrix (Fin 0) (Fin n) ℂ) = ⊥ := by
        rw [linIdeal, Set.range_eq_empty, Ideal.span_empty]
      rw [h0, sup_bot_eq, Nat.sub_zero, ← hd]
      exact hlead n J
    | succ k ih =>
      intro hk
      obtain ⟨A, hA⟩ := ih (by omega)
      have hdk : d - k = (d - (k + 1)) + 1 := by omega
      rw [hdk] at hA
      obtain ⟨B, hB⟩ := hcut n _ _ hA
      refine ⟨Matrix.of (Fin.cons (B 0) A : Fin (k + 1) → Fin n → ℂ), ?_⟩
      rw [linIdeal_cons, ← sup_assoc]
      exact hB
  obtain ⟨A, hA⟩ := key d le_rfl
  rw [Nat.sub_self, Nat.cast_zero] at hA
  obtain ⟨N, hN⟩ := hpow n _ ((leadIdeal_isHomogeneous J).sup (linIdeal_isHomogeneous A)) hA
  exact ⟨A, N, hN⟩

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets

noncomputable section

def PosPartSplit.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (E : ℕ → Set (Fin n → ℂ))
    (y : Fin d → ℂ),
    IsFiniteProjection J A → Pairwise (Function.onFun Disjoint E) →
    (∀ x ∈ fibre J A y, (∃ s, IsSheetAt J A x s) → ∃ k, x ∈ E k) →
      ENNReal.ofReal (chartPosDens J A f φ y) =
        ∑' k, ENNReal.ofReal (chartPosDens J A ((E k).indicator f) φ y)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Matrix

open scoped ENNReal

noncomputable section

def SheetImageArea.Statement : Prop :=
  ∀ (n d : ℕ) (A : Matrix (Fin d) (Fin n) ℂ) (U : Set (Fin d → ℂ)) (s : (Fin d → ℂ) → Fin n → ℂ),
    IsOpen U → DifferentiableOn ℂ s U → (∀ y ∈ U, A *ᵥ s y = y) →
    ∀ B : Set (EuclideanSpace ℂ (Fin d)), MeasurableSet B → (∀ y ∈ B, WithLp.ofLp y ∈ U) →
    ∀ g : EuclideanSpace ℂ (Fin n) → ℝ≥0∞, Measurable g →
      ∫⁻ y in B, g (WithLp.toLp 2 (s (WithLp.ofLp y))) * ENNReal.ofReal (sheetJac s (WithLp.ofLp y))
          ∂(μH[((2 * d : ℕ) : ℝ)]) =
        ∫⁻ z in (fun y => WithLp.toLp 2 (s (WithLp.ofLp y))) '' B, g z ∂(μH[((2 * d : ℕ) : ℝ)])

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Matrix

open scoped ENNReal

noncomputable section

def SheetImageAreaSet.Statement : Prop :=
  ∀ (n d : ℕ) (A : Matrix (Fin d) (Fin n) ℂ) (U : Set (Fin d → ℂ)) (s : (Fin d → ℂ) → Fin n → ℂ),
    IsOpen U → DifferentiableOn ℂ s U → (∀ y ∈ U, A *ᵥ s y = y) →
    ∀ B : Set (EuclideanSpace ℂ (Fin d)), MeasurableSet B → (∀ y ∈ B, WithLp.ofLp y ∈ U) →
      μH[((2 * d : ℕ) : ℝ)] ((fun y => WithLp.toLp 2 (s (WithLp.ofLp y))) '' B) =
        ∫⁻ y in B, ENNReal.ofReal (sheetJac s (WithLp.ofLp y)) ∂(μH[((2 * d : ℕ) : ℝ)])

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets

noncomputable section

def DivisorGoodPointBranches.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ) (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
    (q : Fin n → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    q ∈ zeroSet J → linEval u q = 0 → DivisorRegularAt J u d q → NormalDivisorChartAt M u d q →
    NormalDoublePointsOnDivisor M u q →
      ∃ (m : ℕ) (γ : Fin m → VarBranch J (d + 1) q) (ord : Fin m → ℕ)
          (π : Matrix (Fin d) (Fin n) ℂ),
          (∃ N ∈ 𝓝 q, zeroSet J ∩ N ⊆ ⋃ b, (γ b).image) ∧
          (∃ N ∈ 𝓝 q, ∀ x ∈ zeroSet J ∩ N, linEval u x = 0 → ∀ b, x ∈ (γ b).slice) ∧
          (∀ b b', b ≠ b' → (γ b).image ∩ (γ b').image ⊆ {x | linEval u x = 0}) ∧
          (∀ b, VanishesToOrder (fun t => linEval u ((γ b).toFun t)) (γ b).radius (ord b)) ∧
          ∀ b, Function.Bijective
            (fderiv ℂ (fun τ => vecCons (τ 0) (π *ᵥ (γ b).toFun τ)) (0 : Fin (d + 1) → ℂ))

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets

noncomputable section

def DivisorRegularGeneric.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
      ∃ I : Ideal (MvPolynomial (Fin n) ℂ), J ⊔ Ideal.span {linForm u} ≤ I ∧
        ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) < (d : ℕ) ∧
        ∀ q ∈ zeroSet J, linEval u q = 0 → q ∉ zeroSet I → DivisorRegularAt J u d q

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets

noncomputable section

def NormalDivisorChartGeneric.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ) (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
      ∃ I : Ideal (MvPolynomial (Fin n) ℂ), J ⊔ Ideal.span {linForm u} ≤ I ∧
        ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) < (d : ℕ) ∧
        ∀ q ∈ zeroSet J, linEval u q = 0 → q ∉ zeroSet I → NormalDivisorChartAt M u d q

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets

noncomputable section

def NormalDoublePointsGeneric.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ) (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
      ∃ I : Ideal (MvPolynomial (Fin n) ℂ), J ⊔ Ideal.span {linForm u} ≤ I ∧
        ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) < (d : ℕ) ∧
        ∀ q ∈ zeroSet J, linEval u q = 0 → q ∉ zeroSet I → NormalDoublePointsOnDivisor M u q

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

theorem le_originIdeal_of_isHomogeneous {n : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)}
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin n) ℂ)) (hne : I ≠ ⊤) : I ≤ originIdeal n := by
  intro f hf
  rw [originIdeal_eq_ker, RingHom.mem_ker]
  by_contra h0
  have h1 : homogeneousComponent 0 f ∈ I := by
    have := hI 0 hf
    rwa [show (DirectSum.decompose (homogeneousSubmodule (Fin n) ℂ) f 0 : MvPolynomial (Fin n) ℂ)
      = homogeneousComponent 0 f from decomposition.decompose'_apply _ _] at this
  rw [homogeneousComponent_zero, ← constantCoeff_eq] at h1
  exact hne (I.eq_top_of_isUnit_mem h1 (isUnit_iff_ne_zero.2 h0 |>.map C))

theorem isMaximal_of_isPrime_of_quotient_dim_le_zero {R : Type*} [CommRing R] {K Q : Ideal R}
    (hK : ringKrullDim (R ⧸ K) ≤ 0) (hQ : Q.IsPrime) (hKQ : K ≤ Q) : Q.IsMaximal := by
  have : Ring.KrullDimLE 0 (R ⧸ K) := Ring.krullDimLE_iff.2 (by exact_mod_cast hK)
  have hsurj := Ideal.Quotient.mk_surjective (I := K)
  have : (Q.map (Ideal.Quotient.mk K)).IsPrime :=
    Ideal.map_isPrime_of_surjective hsurj (by rwa [Ideal.mk_ker])
  have hmax := Ideal.isMaximal_of_isPrime (Q.map (Ideal.Quotient.mk K))
  have := Ideal.comap_isMaximal_of_surjective _ hsurj (K := Q.map (Ideal.Quotient.mk K))
  rwa [Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
    sup_eq_left.2 hKQ] at this

theorem HomogDimZeroPow.proof : HomogDimZeroPow.Statement := by
  intro n K hK hdim
  apply Ideal.exists_pow_le_of_le_radical_of_fg _ (Submodule.fg_span (Set.finite_range _))
  rw [Ideal.radical_eq_sInf]
  refine le_sInf fun P ⟨hKP, hP⟩ => ?_
  set 𝒜 := homogeneousSubmodule (Fin n) ℂ
  have hcP : (P.homogeneousCore 𝒜).toIdeal.IsPrime := hP.homogeneousCore
  have hKc : K ≤ (P.homogeneousCore 𝒜).toIdeal := by
    rw [← hK.toIdeal_homogeneousCore_eq_self]
    exact Ideal.homogeneousCore_mono 𝒜 hKP
  have hmax := isMaximal_of_isPrime_of_quotient_dim_le_zero hdim hcP hKc
  have hle := le_originIdeal_of_isHomogeneous (P.homogeneousCore 𝒜).isHomogeneous hmax.ne_top
  exact ((hmax.eq_of_le (originIdeal_isMaximal n).ne_top hle).symm.le).trans
    (Ideal.toIdeal_homogeneousCore_le 𝒜 P)

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Filter Topology
open scoped ContDiff

noncomputable section

theorem smoothTransition_eventually_const {x : ℝ} (hx : x ∉ Set.Icc (0 : ℝ) 1) :
    ∃ c : ℝ, Real.smoothTransition =ᶠ[𝓝 x] fun _ => c := by
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
  rcases hx with h | h
  · refine ⟨0, ?_⟩
    filter_upwards [Iio_mem_nhds h] with y hy
    exact Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
  · refine ⟨1, ?_⟩
    filter_upwards [Ioi_mem_nhds h] with y hy
    exact Real.smoothTransition.one_of_one_le (le_of_lt hy)

theorem smoothTransition_deriv_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |deriv Real.smoothTransition x| ≤ C ∧
      |deriv (deriv Real.smoothTransition) x| ≤ C := by
  have hsm : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  obtain ⟨-, h1⟩ := contDiff_infty_iff_deriv.1 hsm
  obtain ⟨-, h2⟩ := contDiff_infty_iff_deriv.1 h1
  obtain ⟨C1, hC1⟩ := isCompact_Icc.exists_bound_of_continuousOn (h1.continuous.continuousOn (s := Set.Icc (0 : ℝ) 1))
  obtain ⟨C2, hC2⟩ := isCompact_Icc.exists_bound_of_continuousOn (h2.continuous.continuousOn (s := Set.Icc (0 : ℝ) 1))
  refine ⟨max (max C1 C2) 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
  · have a := hC1 x hx
    have b := hC2 x hx
    rw [Real.norm_eq_abs] at a b
    exact ⟨a.trans ((le_max_left _ _).trans (le_max_left _ _)),
      b.trans ((le_max_right _ _).trans (le_max_left _ _))⟩
  · obtain ⟨c, hc⟩ := smoothTransition_eventually_const hx
    have hd := hc.deriv
    have e1 : deriv Real.smoothTransition x = 0 := by rw [hd.eq_of_nhds]; simp
    have e2 : deriv (deriv Real.smoothTransition) x = 0 := by rw [hd.deriv_eq]; simp
    rw [e1, e2, abs_zero]
    exact ⟨le_max_right _ _, le_max_right _ _⟩

theorem logLogStep_arith {C c t p q f v w : ℝ} (hC0 : 0 ≤ C) (hc : 1 ≤ c) (ht : t ≠ 0) (hp : |p| ≤ C)
    (hq : |q| ≤ C) (hf : |f| ≤ 1) (hv : v = -(2 * (t⁻¹ / c))) (hw : w = -(2 * (-(t ^ 2)⁻¹ / c))) :
    |q * v * v + p * w| ≤ (6 * C + 4 * C ^ 2) / (c * t ^ 2) ∧
      |p * v * (p * v) + f * (q * v * v + p * w)| ≤ (6 * C + 4 * C ^ 2) / (c * t ^ 2) := by
  have hc0 : 0 < c := by linarith
  have hD : 0 < c * t ^ 2 := by positivity
  have hvv : v * v ≤ 4 / (c * t ^ 2) := by
    have e : v * v = 4 / (c * t ^ 2) / c := by rw [hv]; field_simp; ring
    rw [e]; exact div_le_self (by positivity) hc
  have hvv0 : 0 ≤ v * v := mul_self_nonneg v
  have hw' : |w| = 2 / (c * t ^ 2) := by
    have e : w = 2 / (c * t ^ 2) := by rw [hw]; field_simp
    rw [e, abs_of_pos (by positivity)]
  have h1 : |q * v * v + p * w| ≤ 6 * C / (c * t ^ 2) := by
    calc |q * v * v + p * w| ≤ |q * v * v| + |p * w| := abs_add_le _ _
      _ = |q| * (v * v) + |p| * |w| := by rw [mul_assoc, abs_mul q, abs_of_nonneg hvv0, abs_mul p]
      _ ≤ C * (4 / (c * t ^ 2)) + C * (2 / (c * t ^ 2)) := by rw [hw']; gcongr
      _ = 6 * C / (c * t ^ 2) := by ring
  have h2 : p * v * (p * v) ≤ 4 * C ^ 2 / (c * t ^ 2) := by
    calc p * v * (p * v) = |p| ^ 2 * (v * v) := by rw [sq_abs]; ring
      _ ≤ C ^ 2 * (4 / (c * t ^ 2)) := by gcongr
      _ = 4 * C ^ 2 / (c * t ^ 2) := by ring
  have hK : 6 * C / (c * t ^ 2) ≤ (6 * C + 4 * C ^ 2) / (c * t ^ 2) := by
    gcongr; nlinarith
  refine ⟨h1.trans hK, ?_⟩
  calc |p * v * (p * v) + f * (q * v * v + p * w)|
      ≤ |p * v * (p * v)| + |f * (q * v * v + p * w)| := abs_add_le _ _
    _ ≤ 4 * C ^ 2 / (c * t ^ 2) + 1 * (6 * C / (c * t ^ 2)) := by
      rw [abs_of_nonneg (mul_self_nonneg (p * v)), abs_mul]; gcongr
    _ = (6 * C + 4 * C ^ 2) / (c * t ^ 2) := by ring

theorem logLogStep_deriv2_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℝ, 1 ≤ c → ∀ t : ℝ, t < 0 →
      ContDiffAt ℝ 2 (fun x => cutStep (Real.log (-x) / c)) t ∧
      ContDiffAt ℝ 2 (fun x => cutStep (Real.log (-x) / c) ^ 2 / 2) t ∧
      |deriv (deriv fun x => cutStep (Real.log (-x) / c)) t| ≤ K / (c * t ^ 2) ∧
      |deriv (deriv fun x => cutStep (Real.log (-x) / c) ^ 2 / 2) t| ≤ K / (c * t ^ 2) := by
  obtain ⟨C, hC0, hC⟩ := smoothTransition_deriv_bound
  refine ⟨6 * C + 4 * C ^ 2, by positivity, fun c hc t ht => ?_⟩
  have hc0 : 0 < c := by linarith
  set σ := Real.smoothTransition with hσdef
  have hsm : ContDiff ℝ ∞ σ := Real.smoothTransition.contDiff
  obtain ⟨hd0, h1⟩ := contDiff_infty_iff_deriv.1 hsm
  obtain ⟨hd1, -⟩ := contDiff_infty_iff_deriv.1 h1
  let u : ℝ → ℝ := fun x => 2 - 2 * (Real.log (-x) / c)
  let u' : ℝ → ℝ := fun x => -(2 * (x⁻¹ / c))
  let u'' : ℝ → ℝ := fun x => -(2 * (-(x ^ 2)⁻¹ / c))
  have hu : ∀ x, x < 0 → HasDerivAt u (u' x) x := by
    intro x hx
    have hl : HasDerivAt (fun x => Real.log (-x)) x⁻¹ x := by
      have := (hasDerivAt_neg x).log (by simpa using hx.ne)
      rwa [neg_div_neg_eq, one_div] at this
    exact ((hl.div_const c).const_mul 2).const_sub 2
  have hu' : ∀ x, x < 0 → HasDerivAt u' (u'' x) x := fun x hx =>
    (((hasDerivAt_inv hx.ne).div_const c).const_mul 2).neg
  let F : ℝ → ℝ := fun x => cutStep (Real.log (-x) / c)
  let G : ℝ → ℝ := fun x => deriv σ (u x) * u' x
  have hF : ∀ x, x < 0 → HasDerivAt F (G x) x := fun x hx =>
    (hd0 (u x)).hasDerivAt.comp x (hu x hx)
  have hG : HasDerivAt G (deriv (deriv σ) (u t) * u' t * u' t + deriv σ (u t) * u'' t) t :=
    ((hd1 (u t)).hasDerivAt.comp t (hu t ht)).mul (hu' t ht)
  have evF : deriv F =ᶠ[𝓝 t] G := by
    filter_upwards [Iio_mem_nhds ht] with x hx
    exact (hF x hx).deriv
  have hF2 : deriv (deriv F) t = deriv (deriv σ) (u t) * u' t * u' t + deriv σ (u t) * u'' t :=
    (hG.congr_of_eventuallyEq evF).deriv
  have hH : ∀ x, x < 0 → HasDerivAt (fun x => F x ^ 2 / 2) (F x * G x) x := by
    intro x hx
    have := ((hF x hx).fun_mul (hF x hx)).div_const 2
    exact (this.congr_deriv (by ring)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => by ring)
  have evH : deriv (fun x => F x ^ 2 / 2) =ᶠ[𝓝 t] fun x => F x * G x := by
    filter_upwards [Iio_mem_nhds ht] with x hx
    exact (hH x hx).deriv
  have hH2 : deriv (deriv fun x => F x ^ 2 / 2) t =
      G t * G t + F t * (deriv (deriv σ) (u t) * u' t * u' t + deriv σ (u t) * u'' t) :=
    (((hF t ht).fun_mul hG).congr_of_eventuallyEq evH).deriv
  have hucd : ContDiffAt ℝ 2 u t :=
    contDiffAt_const.sub (contDiffAt_const.mul ((contDiffAt_id.neg.log (by simpa using ht.ne)).div_const c))
  have hFcd : ContDiffAt ℝ 2 F t := (Real.smoothTransition.contDiffAt (n := 2)).comp t hucd
  have hf : |F t| ≤ 1 := by
    show |Real.smoothTransition (u t)| ≤ 1
    exact abs_le.2 ⟨by linarith [Real.smoothTransition.nonneg (u t)], Real.smoothTransition.le_one (u t)⟩
  obtain ⟨b1, b2⟩ := logLogStep_arith (p := deriv σ (u t)) (q := deriv (deriv σ) (u t)) hC0 hc ht.ne
    (hC _).1 (hC _).2 hf rfl rfl
  refine ⟨hFcd, (hFcd.pow 2).div_const 2, ?_, ?_⟩
  · rw [show deriv (deriv fun x => cutStep (Real.log (-x) / c)) t = _ from hF2]; exact b1
  · rw [show deriv (deriv fun x => cutStep (Real.log (-x) / c) ^ 2 / 2) t = _ from hH2]; exact b2

end

end GroundTheory.Heights₂.Heights
end
