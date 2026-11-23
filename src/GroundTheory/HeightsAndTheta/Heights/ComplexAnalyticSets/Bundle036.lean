module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle013
import Mathlib.Algebra.Lie.OfAssociative
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle014
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle030
public import Mathlib.Order.CompletePartialOrder
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle015
public import Mathlib.Analysis.Analytic.Order
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Analytic.ChangeOrigin
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.Uniqueness

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets

open scoped ENNReal

noncomputable section

def ChartMassCompare.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (φ : Fin d → (Fin n → ℂ) → ℝ) (R : ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A →
    (∀ k, SmoothNear (zeroSet J) (φ k)) →
      ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ g : (Fin n → ℂ) → ℝ, Measurable g →
        ∫⁻ y, ‖chartAbsDens J A ((Metric.closedBall 0 R).indicator g) φ y‖ₑ ≤
          K * ∫⁻ z in zeroSetEuc J ∩ {z | WithLp.ofLp z ∈ Metric.closedBall (0 : Fin n → ℂ) R},
            ‖g (WithLp.ofLp z)‖ₑ ∂(μH[((2 * d : ℕ) : ℝ)])

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets
open scoped ENNReal

noncomputable section

def VarWirtinger.Statement : Prop :=
  ∀ d : ℕ, ∃ c : ℝ, 0 < c ∧
    ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ),
      J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
      ∀ B : Set (EuclideanSpace ℂ (Fin n)), MeasurableSet B → Bornology.IsBounded B →
        Integrable (chartDens J A (((fun x => WithLp.toLp 2 x) ⁻¹' B).indicator fun _ => 1)
            (fun _ => euclPot)) ∧
          μH[((2 * (d + 1) : ℕ) : ℝ)] (zeroSetEuc J ∩ B) =
            ENNReal.ofReal (c * ∫ y, chartDens J A (((fun x => WithLp.toLp 2 x) ⁻¹' B).indicator fun _ => 1)
              (fun _ => euclPot) y)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

open scoped ENNReal

noncomputable section

def LocalGraphMass.Statement : Prop :=
  ∀ (n d : ℕ) (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I₀ : Finset (Fin n))
    (S : Set (EuclideanSpace ℂ (Fin n))), I₀.card = d →
    (∀ z ∈ S, ∃ (Ω : Set (I₀ → ℂ)) (V : Set (EuclideanSpace ℂ (Fin n)))
      (g : (I₀ → ℂ) → EuclideanSpace ℂ (Fin n)), IsOpen Ω ∧ IsOpen V ∧ z ∈ V ∧
        DifferentiableOn ℂ g Ω ∧ (∀ w ∈ Ω, frameProj b I₀ (g w) = w) ∧ S ∩ V = g '' Ω) →
    ∀ R : ℝ, μH[((2 * d : ℕ) : ℝ)] (S ∩ Metric.ball 0 R) ≤
      ∑ I ∈ Finset.univ.powersetCard d,
        (⨆ x : I → ℂ, frameFibreCount b I S x) *
          μH[((2 * d : ℕ) : ℝ)] (Metric.ball (0 : EuclideanSpace ℂ I) R)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

open scoped ENNReal

noncomputable section

def rowsProj {n d : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (s : Fin d → Fin n)
    (z : EuclideanSpace ℂ (Fin n)) : EuclideanSpace ℂ (Fin d) :=
  WithLp.toLp 2 ((U.submatrix s id).mulVec fun j => z j)


open Classical in
def VarietyProjectionMass.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
    ∀ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ B : Set (EuclideanSpace ℂ (Fin n)), MeasurableSet B →
      μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ B) ≤
        ∑ s ∈ Finset.univ.filter (fun s : Fin d → Fin n => StrictMono s),
          (⨆ x : EuclideanSpace ℂ (Fin d),
              (({z | z ∈ zeroSetEuc J ∩ B ∧ rowsProj U s z = x}.encard : ℕ∞) : ℝ≥0∞)) *
            μH[((2 * d : ℕ) : ℝ)] (rowsProj U s '' (zeroSetEuc J ∩ B))

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

open Polynomial IntermediateField

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

variable {F K B : Type*} [Field F] [Field K] [Algebra F K] [CommRing B] [Algebra F B]

theorem exists_isGoodPartialLift_extend (p : ℕ) [hp : Fact p.Prime] [CharP K p] {N : Ideal B}
    {u : K →ₐ[F] B ⧸ N} {ψ : K →+* B} (hψ : ∀ (z : K) (c : B), Ideal.Quotient.mk N c = u z → ψ z = c ^ p)
    {L : IntermediateField F K} {φ : L →ₐ[F] B} (hgood : IsGoodPartialLift p N u ψ ⟨L, φ⟩) {x : K}
    (hx : x ∉ L) :
    ∃ σ : Σ L : IntermediateField F K, L →ₐ[F] B,
      IsGoodPartialLift p N u ψ σ ∧ PartialLiftLE ⟨L, φ⟩ σ ∧ x ∈ σ.1 := by
  let _ : Algebra L B := φ.toRingHom.toAlgebra
  have : IsScalarTower F L B := IsScalarTower.of_algebraMap_eq fun a => (φ.commutes a).symm
  obtain ⟨hxp, hφx⟩ := hgood.1 x
  let a : L := ⟨x ^ p, hxp⟩
  have hirr : Irreducible (X ^ p - Polynomial.C a) := X_pow_sub_C_irreducible_of_prime hp.out fun b hb => hx (by
    have hb' : (b : K) ^ p = x ^ p := congrArg Subtype.val hb
    have hbx := frobenius_inj K p (show frobenius K p (b : K) = frobenius K p x by
      rw [frobenius_def, frobenius_def]; exact hb')
    rw [← hbx]
    exact b.2)
  have hmonic : (X ^ p - Polynomial.C a).Monic := monic_X_pow_sub_C a hp.out.ne_zero
  have hxroot : aeval x (X ^ p - Polynomial.C a) = 0 := by simp [a]
  have hmin : minpoly L x = X ^ p - Polynomial.C a :=
    (minpoly.eq_of_irreducible_of_monic hirr hxroot hmonic).symm
  have hint : IsIntegral L x := ⟨_, hmonic, hxroot⟩
  let pb := IntermediateField.adjoin.powerBasis hint
  obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (u x)
  have hroot : aeval c (minpoly L pb.gen) = 0 := by
    rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen, hmin, map_sub, map_pow,
      aeval_X, aeval_C, RingHom.algebraMap_toAlgebra]
    show c ^ p - φ a = 0
    rw [hφx, hψ x c hc, sub_self]
  let σ₁ := pb.lift c hroot
  let L' : IntermediateField F K := IntermediateField.restrictScalars F (L⟮x⟯)
  let σ : L' →ₐ[F] B := σ₁.restrictScalars F
  have hLL' : L ≤ L' := fun y hy => (L⟮x⟯).algebraMap_mem ⟨y, hy⟩
  have hext : ∀ y : L, σ (IntermediateField.inclusion hLL' y) = φ y := fun y => σ₁.commutes y
  have hring : (Ideal.Quotient.mk N).comp (algebraMap L B) = (u : K →+* B ⧸ N).comp (algebraMap L K) :=
    RingHom.ext fun l => hgood.2 l
  refine ⟨⟨L', σ⟩, ⟨fun z => ?_, fun y => ?_⟩, ⟨hLL', hext⟩, IntermediateField.mem_adjoin_simple_self L x⟩
  · obtain ⟨h, h'⟩ := hgood.1 z
    exact ⟨hLL' h, (hext ⟨_, h⟩).trans h'⟩
  · obtain ⟨f, hf⟩ := pb.exists_eq_aeval' ⟨y.1, y.2⟩
    have hy : (y : K) = aeval x f := by
      have h' := congrArg (algebraMap (L⟮x⟯) K) hf
      rw [← Polynomial.aeval_algebraMap_apply, IntermediateField.adjoin.powerBasis_gen,
        IntermediateField.AdjoinSimple.algebraMap_gen] at h'
      exact h'
    show Ideal.Quotient.mk N (σ₁ ⟨y.1, y.2⟩) = u y
    rw [hf, PowerBasis.lift_aeval, hy, aeval_def, aeval_def, Polynomial.hom_eval₂, hring, hc]
    exact (Polynomial.hom_eval₂ _ _ _ _).symm

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem FiniteProjectionProperBall.proof : FiniteProjectionProperBall.Statement := by
  intro σ _ X w d A hX hiso U hU
  obtain ⟨N, k, f, hNo, hwN, hf, hXN⟩ := hX
  obtain ⟨W, hW, hWiso⟩ := hiso
  have hmem : N ∩ U ∩ W ∈ 𝓝 w := Filter.inter_mem (Filter.inter_mem (hNo.mem_nhds hwN) hU) hW
  obtain ⟨ρ, hρ, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hmem
  have hBN : Metric.closedBall w ρ ⊆ N := fun x hx => (hball hx).1.1

  set C : Set (σ → ℂ) := Metric.closedBall w ρ ∩ (fun z i => f i z) ⁻¹' {0} with hCdef
  have hCX : ∀ x ∈ C, x ∈ X := by
    intro x hx
    have hxN := hBN hx.1
    have : x ∈ X ∩ N := by
      rw [hXN]
      refine ⟨hxN, fun i => ?_⟩
      have := congrFun (show (fun i => f i x) = 0 from hx.2) i
      simpa using this
    exact this.1
  have hXC : ∀ x ∈ X, x ∈ Metric.closedBall w ρ → x ∈ C := by
    intro x hxX hxB
    have : x ∈ {z | z ∈ N ∧ ∀ i, f i z = 0} := hXN ▸ ⟨hxX, hBN hxB⟩
    refine ⟨hxB, ?_⟩
    show (fun i => f i x) = 0
    funext i
    simpa using this.2 i
  have hCcl : IsClosed C := by
    refine ContinuousOn.preimage_isClosed_of_isClosed ?_ Metric.isClosed_closedBall isClosed_singleton
    exact continuousOn_pi.mpr fun i => ((hf i).continuousOn).mono hBN
  have hC : IsCompact C := (isCompact_closedBall w ρ).of_isClosed_subset hCcl Set.inter_subset_left

  set S : Set (σ → ℂ) := C ∩ Metric.sphere w ρ with hSdef
  have hS : IsCompact S := hC.inter_right Metric.isClosed_sphere
  have hT : IsCompact (A '' S) := hS.image A.continuous
  have hAw : A w ∉ A '' S := by
    rintro ⟨x, hxS, hxA⟩
    have hxw : x = w := hWiso x ⟨hCX x hxS.1, (hball hxS.1.1).2⟩ hxA
    have hd := hxS.2
    rw [hxw, Metric.mem_sphere, dist_self] at hd
    exact hρ.ne hd
  obtain ⟨r, hr, hrT⟩ := Metric.isOpen_iff.mp hT.isClosed.isOpen_compl (A w) hAw
  refine ⟨ρ, hρ, r, hr, fun x hx => (hball (Metric.ball_subset_closedBall hx)).1.2, ?_⟩
  intro K hKr hK
  have heq : {x | x ∈ X ∩ Metric.ball w ρ ∧ A x ∈ K} = C ∩ A ⁻¹' K := by
    ext x
    constructor
    · rintro ⟨⟨hxX, hxB⟩, hxK⟩
      exact ⟨hXC x hxX (Metric.ball_subset_closedBall hxB), hxK⟩
    · rintro ⟨hxC, hxK⟩
      refine ⟨⟨hCX x hxC, ?_⟩, hxK⟩
      have hle : dist x w ≤ ρ := hxC.1
      rcases hle.lt_or_eq with hlt | heq
      · exact hlt
      · exact absurd ⟨x, ⟨hxC, heq⟩, rfl⟩ (hrT (hKr hxK))
  rw [heq]
  exact hC.inter_right (hK.isClosed.preimage A.continuous)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

theorem FiniteFibreGermIntegral.proof (hWF : WeierstrassFiniteness.Statement)
    (hR : RueckertNullstellensatz.Statement) : FiniteFibreGermIntegral.Statement := by
  intro σ _ X x d A hX hiso g hg
  obtain ⟨N, k, f, hNo, hxN, hf, hXN⟩ := hX
  obtain ⟨W, hW, hWiso⟩ := hiso
  have hfx : ∀ i, AnalyticAt ℂ (f i) x := fun i => hf i x hxN
  have hAj : ∀ j : Fin d, AnalyticAt ℂ (fun z => A z j - A x j) x := fun j =>
    (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d => ℂ) j).comp A).analyticAt x).sub
      analyticAt_const

  let F : Fin (k + d) → (σ → ℂ) → ℂ := Fin.append f (fun j z => A z j - A x j)
  have hFx : ∀ i, AnalyticAt ℂ (F i) x := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simpa only [F, Fin.append_left] using hfx i
    · simpa only [F, Fin.append_right] using hAj j
  have hcoord : ∀ l : σ, ∃ (r : ℕ) (h : Fin k → (σ → ℂ) → ℂ) (h' : Fin d → (σ → ℂ) → ℂ),
      (∀ i, AnalyticAt ℂ (h i) x) ∧ (∀ j, AnalyticAt ℂ (h' j) x) ∧
      ∀ᶠ z in 𝓝 x, (z l - x l) ^ r = ∑ i, h i z * f i z + ∑ j, h' j z * (A z j - A x j) := by
    intro l
    have hl : AnalyticAt ℂ (fun z : σ → ℂ => z l - x l) x :=
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) l).analyticAt x).sub analyticAt_const
    have hvan : ∀ᶠ z in 𝓝 x, (∀ i, F i z = 0) → z l - x l = 0 := by
      filter_upwards [hNo.mem_nhds hxN, hW] with z hzN hzW h0
      have hf0 : ∀ i, f i z = 0 := fun i => by simpa only [F, Fin.append_left] using h0 (Fin.castAdd d i)
      have hA0 : A z = A x := funext fun j =>
        sub_eq_zero.1 (by simpa only [F, Fin.append_right] using h0 (Fin.natAdd k j))
      have hzX : z ∈ X := by
        have : z ∈ X ∩ N := by rw [hXN]; exact ⟨hzN, hf0⟩
        exact this.1
      rw [hWiso z ⟨hzX, hzW⟩ hA0, sub_self]
    obtain ⟨m, h, -, hh, hsum⟩ := hR σ x (k + d) F (fun z => z l - x l) hFx hl hvan
    refine ⟨m, fun i => h (Fin.castAdd d i), fun j => h (Fin.natAdd k j), fun i => hh _, fun j => hh _, ?_⟩
    filter_upwards [hsum] with z hz
    rw [hz, Fin.sum_univ_add]
    simp only [F, Fin.append_left, Fin.append_right]
  obtain ⟨n, a, h, ha, -, hrel⟩ := hWF σ x k f d A hfx hcoord g hg
  refine ⟨n, a, ha, ?_⟩
  filter_upwards [hrel, hNo.mem_nhds hxN] with z hz hzN hzX
  have hz0 : z ∈ X ∩ N := ⟨hzX, hzN⟩
  rw [hXN] at hz0
  rw [hz]
  simp [hz0.2]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem germ_eventually_zero_of_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : E → ℂ} {y : E}
    (hf : AnalyticAt ℂ f y) (hg : AnalyticAt ℂ g y) (hfg : ∀ᶠ z in 𝓝 y, f z * g z = 0) :
    (∀ᶠ z in 𝓝 y, f z = 0) ∨ (∀ᶠ z in 𝓝 y, g z = 0) := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1
    ((hf.eventually_analyticAt.and hg.eventually_analyticAt).and hfg)
  by_cases hf0 : ∀ z ∈ Metric.ball y r, f z = 0
  · exact Or.inl (Filter.mem_of_superset (Metric.ball_mem_nhds y hr) hf0)
  · right
    push Not at hf0
    obtain ⟨p, hp, hfp⟩ := hf0
    have hgp : g =ᶠ[𝓝 p] 0 := by
      filter_upwards [(hball hp).1.1.continuousAt.eventually_ne hfp, Metric.isOpen_ball.mem_nhds hp]
        with z hz1 hz2
      exact (mul_eq_zero.1 (hball hz2).2).resolve_left hz1
    have hgan : AnalyticOnNhd ℂ g (Metric.ball y r) := fun z hz => (hball hz).1.2
    have hzero := hgan.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball y r).isPreconnected hp hgp
    exact Filter.mem_of_superset (Metric.ball_mem_nhds y hr) fun z hz => by simpa using hzero hz

theorem germ_prod_eventually_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type*}
    (h : ι → E → ℂ) {y : E} (s : Finset ι) (han : ∀ i ∈ s, AnalyticAt ℂ (h i) y)
    (hprod : ∀ᶠ z in 𝓝 y, ∏ i ∈ s, h i z = 0) : ∃ i ∈ s, ∀ᶠ z in 𝓝 y, h i z = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨z, hz⟩ := hprod.exists
    simp at hz
  | insert a s ha ih =>
    have hg : AnalyticAt ℂ (fun z => ∏ i ∈ s, h i z) y :=
      Finset.analyticAt_fun_prod s fun i hi => han i (Finset.mem_insert_of_mem hi)
    have hprod' : ∀ᶠ z in 𝓝 y, h a z * ∏ i ∈ s, h i z = 0 := by
      filter_upwards [hprod] with z hz
      rwa [Finset.prod_insert ha] at hz
    rcases germ_eventually_zero_of_mul (han a (Finset.mem_insert_self a s)) hg hprod' with h1 | h1
    · exact ⟨a, Finset.mem_insert_self a s, h1⟩
    · obtain ⟨i, hi, h2⟩ := ih (fun i hi => han i (Finset.mem_insert_of_mem hi)) h1
      exact ⟨i, Finset.mem_insert_of_mem hi, h2⟩

theorem mem_of_projection_germ_injective {σ : Type} [Fintype σ] {X : Set (σ → ℂ)} {x : σ → ℂ} {d : ℕ}
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (hX : IsAnalyticNear X x)
    (hinj : ∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A x) → (∀ᶠ z in 𝓝 x, z ∈ X → h (A z) = 0) →
      ∀ᶠ y in 𝓝 (A x), h y = 0) : x ∈ X := by
  by_contra hx
  obtain ⟨N, k, f, hNo, hxN, hf, hXN⟩ := hX
  have hne : ∃ i, f i x ≠ 0 := by
    by_contra hall
    push Not at hall
    have hmem : x ∈ {z | z ∈ N ∧ ∀ i, f i z = 0} := ⟨hxN, hall⟩
    rw [← hXN] at hmem
    exact hx hmem.1
  obtain ⟨i, hi⟩ := hne
  have hev : ∀ᶠ z in 𝓝 x, z ∈ X → (fun _ : Fin d → ℂ => (1 : ℂ)) (A z) = 0 := by
    filter_upwards [(hf i x hxN).continuousAt.eventually_ne hi, hNo.mem_nhds hxN] with z hz1 hz2 hzX
    have hmem : z ∈ X ∩ N := ⟨hzX, hz2⟩
    rw [hXN] at hmem
    exact absurd (hmem.2 i) hz1
  obtain ⟨y, hy⟩ := (hinj (fun _ => 1) analyticAt_const hev).exists
  exact one_ne_zero hy

theorem FiniteGermProjectionOpenAt.proof (hcomp : AnalyticGermComponents.Statement)
    (hirr : IrreducibleFiniteGermProjectionOpenAt.Statement) : FiniteGermProjectionOpenAt.Statement := by
  classical
  intro σ _ X x d A hX hiso hinj V hV
  have hxX : x ∈ X := mem_of_projection_germ_injective A hX hinj
  obtain ⟨n, Y, hY, W, hW, hXW⟩ := hcomp σ X x hX hxX
  obtain ⟨W₀, hW₀, hisoW₀⟩ := hiso

  have hsome : ∃ i, ∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A x) →
      (∀ᶠ z in 𝓝 x, z ∈ Y i → h (A z) = 0) → ∀ᶠ y in 𝓝 (A x), h y = 0 := by
    by_contra hnone
    push Not at hnone
    choose h han hvan hne using hnone
    have hprod : ∀ᶠ y in 𝓝 (A x), ∏ i ∈ Finset.univ, h i y = 0 := by
      have hpan : AnalyticAt ℂ (fun y => ∏ i ∈ Finset.univ, h i y) (A x) :=
        Finset.analyticAt_fun_prod Finset.univ fun i _ => han i
      refine hinj (fun y => ∏ i ∈ Finset.univ, h i y) hpan ?_
      filter_upwards [Filter.eventually_all.2 hvan, hW] with z hz hzW hzX
      have hmem : z ∈ (⋃ i, Y i) ∩ W := by
        rw [← hXW]
        exact ⟨hzX, hzW⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hmem.1
      exact Finset.prod_eq_zero (Finset.mem_univ i) (hz i hi)
    obtain ⟨i, -, hi⟩ := germ_prod_eventually_zero h Finset.univ (fun i _ => han i) hprod
    exact hne i (hi.mono fun z hz => not_not.2 hz)
  obtain ⟨i, hi⟩ := hsome
  have hYX : Y i ∩ W ⊆ X := fun z hz => by
    have hmem : z ∈ (⋃ j, Y j) ∩ W := ⟨Set.mem_iUnion.2 ⟨i, hz.1⟩, hz.2⟩
    rw [← hXW] at hmem
    exact hmem.1
  have hisoY : ∃ W' ∈ 𝓝 x, ∀ x' ∈ Y i ∩ W', A x' = A x → x' = x :=
    ⟨W ∩ W₀, Filter.inter_mem hW hW₀, fun x' hx' hAx' => hisoW₀ x' ⟨hYX ⟨hx'.1, hx'.2.1⟩, hx'.2.2⟩ hAx'⟩
  have himg := hirr σ (Y i) x d A (hY i).1 (hY i).2 hisoY hi (V ∩ W) (Filter.inter_mem hV hW)
  refine Filter.mem_of_superset himg (Set.image_mono ?_)
  rintro z ⟨hzY, hzV, hzW⟩
  exact ⟨hYX ⟨hzY, hzW⟩, hzV⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

def FiniteModuloGeneralEquation.Statement : Prop :=
  ∀ (σ τ : Type) [Fintype σ] [Fintype τ] [DecidableEq τ] (x : σ → ℂ) (k : ℕ)
    (f : Fin k → (σ → ℂ) → ℂ) (L : (σ → ℂ) →L[ℂ] (τ → ℂ)) (c : τ),
    (∀ i, AnalyticAt ℂ (f i) x) → IsFiniteModuloOver x f L →
    (∃ (r : ℕ) (h : Fin k → (σ → ℂ) → ℂ) (h' : τ → (σ → ℂ) → ℂ),
      (∀ i, AnalyticAt ℂ (h i) x) ∧ (∀ c', AnalyticAt ℂ (h' c') x) ∧
      ∀ᶠ z in 𝓝 x, (L z c - L x c) ^ r =
        ∑ i, h i z * f i z + ∑ c', h' c' z * (zeroCoordinate c (L z) c' - zeroCoordinate c (L x) c')) →
    ∃ (d : ℕ) (F : (τ → ℂ) → ℂ) (h : Fin k → (σ → ℂ) → ℂ),
      AnalyticAt ℂ F (L x) ∧ (∀ i, AnalyticAt ℂ (h i) x) ∧
      (∀ᶠ z in 𝓝 x, F (L z) = ∑ i, h i z * f i z) ∧
      analyticOrderAt (fun s : ℂ => F (L x + Pi.single c s)) 0 = d

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
