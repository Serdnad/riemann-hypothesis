module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GenericBlockMatrixIsBlockDiag
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsotropicQuotientStructure
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsPlaceWeightConjInvariant
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle008
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle081
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle021
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle007
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle038
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle006
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle080
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Geometry.Manifold.ContMDiff.Basic
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.ContMDiffMap
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.ConeChartA
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.FubiniLevi

@[expose] public section

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

theorem _root_.GlobalTheory.T.minor_sum_identity_base_change : ∀ (Ω : Type) [Field Ω] [Infinite Ω] (N j : ℕ) (T : Matrix (Fin N) (Fin N) Ω) (c₀ c₁ : Ω) (coef u : Finset (Fin N) → Ω) (J : Finset (Fin N)), (∀ h : Matrix (Fin N) (Fin N) Ω, IsBlockDiag j h → c₀ * ∑ I, coef I * minorIJ (T * h) I J = c₁ * ∑ I, u I * minorIJ h I J) → ∀ (S : Type) [CommRing S] [Algebra Ω S] (h : Matrix (Fin N) (Fin N) S), IsBlockDiag j h → algebraMap Ω S c₀ * ∑ I, algebraMap Ω S (coef I) * minorIJ (T.map (algebraMap Ω S) * h) I J = algebraMap Ω S c₁ * ∑ I, algebraMap Ω S (u I) * minorIJ h I J := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.MinorAny.minor_any | exact GlobalTheory.CompanionTheory.Ar.PB.MinorAny.minor_any | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.MinorAny.minor_any <;> assumption)
end

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

theorem _root_.GlobalTheory.T.isotropic_quotient_structure : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R₀ : RiemLat E g Λ) (I : Submodule (𝓞 E) Λ), IsSaturated I → IsIsoSub R₀.form I → ∃ (g' k : ℕ) (Λ' : Type) (_ : AddCommGroup Λ') (_ : Module (𝓞 E) Λ') (e : Fin k → Λ) (form' : Λ' →ₗ[ℤ] Λ' →ₗ[ℤ] ℤ) (π : Λ → Λ'), k + g' = g ∧ (∀ x', ∃ x, (∀ y ∈ I, R₀.form x y = 0) ∧ π x = x') ∧ ∀ R : RiemLat E g Λ, R.form = R₀.form → LinearIndependent ℂ (fun i => R.P (e i)) ∧ Submodule.span ℂ (R.P '' I) = Submodule.span ℂ (Set.range fun i => R.P (e i)) ∧ ∀ q : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ), Function.Surjective q → LinearMap.ker q = Submodule.span ℂ (R.P '' I) → ∃ R' : RiemLat E g' Λ', R'.form = form' ∧ (∀ x, (∀ y ∈ I, R.form x y = 0) → R'.P (π x) = q (R.P x)) ∧ ∀ x y, (∀ v ∈ I, R.ip (R.P v) x = 0) → R'.ip (q x) (q y) = R.ip x y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Univ.QuotLat.exists_univ_quot | exact GlobalTheory.CompanionTheory.Ar.Cusp.Univ.QuotLat.exists_univ_quot | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Univ.QuotLat.exists_univ_quot <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

namespace CExt

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Flat.PlaceWeightSmooth Topology Filter Set
open scoped Manifold

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def colMap (p : (k : K) → ι k) (m : (Σ k, ι k × ι k) → ℂ) : (Σ k, ι k) → ℂ :=
  fun q => m ⟨q.1, (q.2, p q.1)⟩

theorem colMap_contDiff (p : (k : K) → ι k) {n : WithTop ℕ∞} : ContDiff ℝ n (colMap p) :=
  contDiff_pi.2 fun q => contDiff_apply ℝ (fun _ => ℂ) (⟨q.1, (q.2, p q.1)⟩ : Σ k, ι k × ι k)

theorem sameOrbit_colMap {p : (k : K) → ι k} {z : (Σ k, ι k) → ℂ} (hz : z ∈ nzBlocks K ι)
    (hp : ∀ k, z ⟨k, p k⟩ ≠ 0) : SameOrbit (colMap p (prMap z)) z := by
  refine ⟨fun k => (starRingEnd ℂ) (z ⟨k, p k⟩) / (blockSq z k : ℂ), fun k =>
    div_ne_zero ((map_ne_zero _).2 (hp k)) (Complex.ofReal_ne_zero.2 (blockSq_pos (hz k)).ne'), ?_⟩
  funext q
  simp only [colMap, prMap]
  ring

theorem prMap_diag_ne_zero {z : (Σ k, ι k) → ℂ} (hz : z ∈ nzBlocks K ι) {k : K} {i : ι k}
    (hi : z ⟨k, i⟩ ≠ 0) : prMap z ⟨k, (i, i)⟩ ≠ 0 :=
  div_ne_zero (mul_ne_zero hi ((map_ne_zero _).2 hi))
    (Complex.ofReal_ne_zero.2 (blockSq_pos (hz k)).ne')

theorem ne_zero_of_prMap_diag {z : (Σ k, ι k) → ℂ} {k : K} {i : ι k}
    (h : prMap z ⟨k, (i, i)⟩ ≠ 0) : z ⟨k, i⟩ ≠ 0 := by
  intro h0
  apply h
  simp [prMap, h0]

theorem isClosed_prMap_image {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) :
    IsClosed (prMap '' mcPts P) := by
  have hA : IsClosed {z : (Σ k, ι k) → ℂ | ∀ f ∈ P, eval z (map (Int.castRingHom ℂ) f) = 0} := by
    simp only [setOf_forall]
    exact isClosed_iInter fun f => isClosed_iInter fun _ =>
      isClosed_eq (MvPolynomial.continuous_eval _) continuous_const
  have hC := (isCompact_unitBlocks (K := K) (ι := ι)).inter_right hA
  have hcont : ContinuousOn (prMap (K := K) (ι := ι)) (unitBlocks K ι ∩
      {z | ∀ f ∈ P, eval z (map (Int.castRingHom ℂ) f) = 0}) := fun z hz =>
    (prMap_continuousAt (unitBlocks_subset hz.1)).continuousWithinAt
  convert (hC.image_of_continuousOn hcont).isClosed using 1
  ext m
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨c, hc, hu⟩ := exists_normalize (K := K) (ι := ι) hz.1
    exact ⟨_, ⟨hu, (mcPts_smul hP c hc hz).2⟩, prMap_smul c z hc⟩
  · rintro ⟨z, ⟨hu, hz⟩, rfl⟩
    exact ⟨z, ⟨unitBlocks_subset hu, hz⟩, rfl⟩

theorem exists_smooth_on_matrices {P : Ideal (MRing ι)} {u : ((Σ k, ι k) → ℂ) → ℝ}
    (hP : IsMultiHomogIdeal P) (hinv : ∀ z ∈ mcPts P, ∀ z', SameOrbit z' z → u z' = u z)
    (hloc : ∀ z ∈ mcPts P, ∃ (V : Set ((Σ k, ι k) → ℂ)) (w : ((Σ k, ι k) → ℂ) → ℝ), IsOpen V ∧ z ∈ V ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w V ∧ ∀ z' ∈ V ∩ mcPts P, w z' = u z') :
    ∃ g : ((Σ k, ι k × ι k) → ℂ) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧
      ∀ z ∈ mcPts P, g (prMap z) = u z := by
  have ht : ∀ m : (Σ k, ι k × ι k) → ℂ,
      Convex ℝ {r : ℝ | ∀ z ∈ mcPts P, prMap z = m → r = u z} := by
    intro m x hx y hy a b _ _ hab z hz hzm
    rw [smul_eq_mul, smul_eq_mul, hx z hz hzm, hy z hz hzm, ← add_mul, hab, one_mul]
  obtain ⟨g, hg⟩ := exists_contMDiffMap_forall_mem_convex_of_local (n := (⊤ : ℕ∞))
    (M := (Σ k, ι k × ι k) → ℂ) (F := ℝ) 𝓘(ℝ, (Σ k, ι k × ι k) → ℂ) ht (fun x => by
    by_cases hx : x ∈ prMap '' mcPts P
    · obtain ⟨z₀, hz₀, rfl⟩ := hx
      choose p hp using hz₀.1
      obtain ⟨V, w, hV, hmem, hw, hwu⟩ := hloc (colMap p (prMap z₀))
        (mem_mcPts_of_sameOrbit hP (sameOrbit_colMap hz₀.1 hp) hz₀)
      have hO : IsOpen (colMap p ⁻¹' V ∩ {m | ∀ k, m ⟨k, (p k, p k)⟩ ≠ 0}) := by
        refine (hV.preimage (colMap_contDiff p (n := 0)).continuous).inter ?_
        simp only [setOf_forall]
        exact isOpen_iInter_of_finite fun k => isOpen_ne_fun (continuous_apply _) continuous_const
      refine ⟨_, hO.mem_nhds ⟨hmem, fun k => prMap_diag_ne_zero hz₀.1 (hp k)⟩, w ∘ colMap p, ?_, ?_⟩
      · exact contMDiffOn_iff_contDiffOn.2
          (hw.comp (colMap_contDiff p).contDiffOn fun y hy => hy.1)
      · rintro y ⟨hy1, hy2⟩ z hz rfl
        have ho := sameOrbit_colMap hz.1 fun k => ne_zero_of_prMap_diag (hy2 k)
        show w (colMap p (prMap z)) = u z
        rw [hwu _ ⟨hy1, mem_mcPts_of_sameOrbit hP ho hz⟩]
        exact hinv z hz _ ho
    · refine ⟨_, (isClosed_prMap_image hP).isOpen_compl.mem_nhds hx, fun _ => 0, contMDiffOn_const, ?_⟩
      intro y hy z hz hzy
      exact absurd ⟨z, hz, hzy⟩ hy)
  exact ⟨g, contMDiff_iff_contDiff.1 g.contMDiff, fun z hz => hg _ z hz rfl⟩


variable (ι) in
def expLine (g : ((Σ k, ι k × ι k) → ℂ) → ℝ) : HermLine ι where
  a := 0
  h z := by
    classical
    exact if z ∈ nzBlocks K ι then Real.exp (g (prMap z)) else 1
  pos z hz := by
    split_ifs
    · exact Real.exp_pos _
    · exact one_pos
  smul c z hc := by
    classical
    have hiff : (fun p : Σ k, ι k => c p.1 * z p) ∈ nzBlocks K ι ↔ z ∈ nzBlocks K ι := by
      refine forall_congr' fun k => exists_congr fun i => ?_
      simp [hc k]
    simp only [hiff, Pi.zero_apply, zpow_zero, Finset.prod_const_one, one_mul, prMap_smul c z hc]

end CExt

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

theorem exists_hermLine_of_local_smooth : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (u : ((Σ k, ι k) → ℂ) → ℝ), IsMultiHomogIdeal P → (∀ z ∈ mcPts P, ∀ z', SameOrbit z' z → u z' = u z) → (∀ z ∈ mcPts P, ∃ (V : Set ((Σ k, ι k) → ℂ)) (w : ((Σ k, ι k) → ℂ) → ℝ), IsOpen V ∧ z ∈ V ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w V ∧ ∀ z' ∈ V ∩ mcPts P, w z' = u z') → ∃ B : HermLine ι, B.a = 0 ∧ IsSmoothHerm B ∧ ∀ z ∈ mcPts P, Real.log (B.h z) = u z := by
  intro K _ ι _ P u hP hinv hloc
  obtain ⟨g, hg, hgu⟩ := CExt.exists_smooth_on_matrices hP hinv hloc
  refine ⟨CExt.expLine ι g, rfl, ?_, fun z hz => ?_⟩
  · have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z => Real.exp (g (GlobalTheory.CompanionTheory.Ar.Flat.PlaceWeightSmooth.prMap z)))
        (GlobalTheory.CompanionTheory.Ar.Flat.PlaceWeightSmooth.nzBlocks K ι) :=
      Real.contDiff_exp.comp_contDiffOn
        (hg.comp_contDiffOn GlobalTheory.CompanionTheory.Ar.Flat.PlaceWeightSmooth.prMap_contDiffOn)
    refine h1.congr fun z hz => ?_
    exact if_pos hz
  · have h2 : (CExt.expLine ι g).h z = Real.exp (g (GlobalTheory.CompanionTheory.Ar.Flat.PlaceWeightSmooth.prMap z)) :=
      if_pos hz.1
    rw [h2, Real.log_exp, hgu z hz]

end GlobalTheory.CompanionTheory.Ar.PB
end
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Giv.Mix


theorem _root_.GlobalTheory.T.intersection_number_telescoping : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ), IsIntersectionFamily I → ∀ (P : Ideal (MRing ι)) (n : ℕ) (a a₀ A' : HermLine ι) (k : ℕ), IsArithVar P (n + 1) → IsSmoothHerm a → IsSmoothHerm a₀ → IsSmoothHerm A' → a.a = a₀.a → k ≤ n + 1 → I P (n + 1) (fun j => if (j : ℕ) < k then a else A') - I P (n + 1) (fun j => if (j : ℕ) < k then a₀ else A') = -∑ i ∈ Finset.range k, ptsIntegral P (pot (mixWord (n := n) a a₀ A' k i)) (logRatio a a₀) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.Mix.Tele.positionTelescope | exact GlobalTheory.CompanionTheory.Ar.Giv.Mix.Tele.positionTelescope | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.Mix.Tele.positionTelescope <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

theorem isGenFam_const_mul_eq_mul_upper : ∀ (Ω G : Type) [Field Ω] [Field G] [Algebra Ω G] (S : Type) [Finite S] (r : S → ℕ) (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) G) (A : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω), IsGenFam Ω G u → (∀ s, IsUnit (A s).det) → ∃ u' B : ∀ s, Matrix (Fin (r s)) (Fin (r s)) G, IsGenFam Ω G u' ∧ (∀ s, IsUnit (B s).det) ∧ (∀ s a b, b < a → B s a b = 0) ∧ ∀ s, (A s).map (algebraMap Ω G) * u s = u' s * B s :=
  @PositivityTheory.Xgp.t_c_fm_exists_flags_chgbasis

end GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt
open ReciprocityTheory.AnForm.R (conePts)
open GroundTheory.Heights₂.Heights (chartLift chartLift_segre_apply)

namespace SecNotIn

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def chartMono (i : (k : K) → ι k) : MRingOver ℂ ι := ∏ k, X ⟨k, i k⟩

theorem eval_chartMono (i : (k : K) → ι k) (x : (Σ k, ι k) → ℂ) : eval x (chartMono i) = segre x i := by
  simp [chartMono, segre]

theorem eval_scale_eq_zero {Q : Ideal (MRingOver ℂ ι)} (hQ : IsMultiHomogIdeal Q)
    (c : K → ℂ) {x : (Σ k, ι k) → ℂ} (hx : ∀ f ∈ Q, eval x f = 0) :
    ∀ f ∈ Q, eval (fun q => c q.1 * x q) f = 0 := by
  obtain ⟨S, hS, rfl⟩ := hQ
  have hle : Ideal.span S ≤ RingHom.ker (eval (fun q : Σ k, ι k => c q.1 * x q)) := by
    rw [Ideal.span_le]
    intro f hf
    obtain ⟨a, ha⟩ := hS f hf
    have h := ReciprocityTheory.AnForm.R.aeval_smul_of_isMultiHomog ha c x
    rw [SetLike.mem_coe, RingHom.mem_ker]
    have h' : eval (fun q : Σ k, ι k => c q.1 * x q) f = (∏ k, c k ^ a k) * eval x f := h
    rw [h', hx f (Ideal.subset_span hf), mul_zero]
  exact fun f hf => hle hf

theorem mem_of_eval_eq_zero {Q : Ideal (MRingOver ℂ ι)} (hQp : Q.IsPrime) {i : (k : K) → ι k}
    (hw : chartMono i ∉ Q) {g : MRingOver ℂ ι}
    (h : ∀ x : (Σ k, ι k) → ℂ, (∀ f ∈ Q, eval x f = 0) → segre x i ≠ 0 → eval x g = 0) : g ∈ Q := by
  have hrad : g * chartMono i ∈ Q.radical := by
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := ℂ), mem_vanishingIdeal_iff]
    intro x hx
    have hae : ∀ p : MvPolynomial (Σ k, ι k) ℂ, aeval x p = eval x p := fun _ => rfl
    rw [hae, map_mul, eval_chartMono]
    by_cases h0 : segre x i = 0
    · rw [h0, mul_zero]
    · rw [h x (fun f hf => by have := hx f hf; rwa [hae] at this) h0, zero_mul]
  rw [hQp.radical] at hrad
  exact (hQp.mem_or_mem hrad).resolve_right hw

def normAt (i : (k : K) → ι k) (x : (Σ k, ι k) → ℂ) : (Σ k, ι k) → ℂ :=
  fun q => (x ⟨q.1, i q.1⟩)⁻¹ * x q

theorem entry_ne_zero {i : (k : K) → ι k} {x : (Σ k, ι k) → ℂ} (h : segre x i ≠ 0) (k : K) :
    x ⟨k, i k⟩ ≠ 0 := fun h0 => h (Finset.prod_eq_zero (Finset.mem_univ k) h0)

theorem segre_normAt (i i' : (k : K) → ι k) (x : (Σ k, ι k) → ℂ) :
    segre (normAt i x) i' = segre x i' / segre x i := by
  simp only [segre, normAt, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  rw [div_eq_mul_inv, mul_comm]

theorem normAt_mem {Q : Ideal (MRingOver ℂ ι)} (hQ : IsMultiHomogIdeal Q)
    {i : (k : K) → ι k} {x : (Σ k, ι k) → ℂ} (hx : ∀ f ∈ Q, eval x f = 0) (h : segre x i ≠ 0) :
    normAt i x ∈ conePts Q :=
  ⟨fun k => ⟨i k, mul_ne_zero (inv_ne_zero (entry_ne_zero h k)) (entry_ne_zero h k)⟩,
    eval_scale_eq_zero hQ (fun k => (x ⟨k, i k⟩)⁻¹) hx⟩

theorem normAt_mem_chartSet {Q : Ideal (MRingOver ℂ ι)} (hQ : IsMultiHomogIdeal Q)
    {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) {i : (k : K) → ι k} {x : (Σ k, ι k) → ℂ}
    (hx : ∀ f ∈ Q, eval x f = 0) (h : segre x i ≠ 0) :
    (fun a => segre x (σ a) / segre x i) ∈ chartSet (conePts Q) σ i :=
  ⟨normAt i x, normAt_mem hQ hx h, by rw [segre_normAt, div_self h],
    funext fun a => (segre_normAt i (σ a) x).symm⟩

theorem exists_homogenise {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (f : MvPolynomial (Fin m) ℂ) :
    ∃ (F : MRingOver ℂ ι) (D : ℕ), ∀ x : (Σ k, ι k) → ℂ, segre x i ≠ 0 →
      eval x F = segre x i ^ D * eval (fun a => segre x (σ a) / segre x i) f := by
  induction f using MvPolynomial.induction_on with
  | C c => exact ⟨C c, 0, fun x _ => by simp⟩
  | add f g hf hg =>
    obtain ⟨F, D, hF⟩ := hf
    obtain ⟨G, E, hG⟩ := hg
    refine ⟨F * chartMono i ^ E + G * chartMono i ^ D, D + E, fun x hx => ?_⟩
    simp only [map_add (f := _), map_mul, map_pow, eval_chartMono, hF x hx, hG x hx]
    ring
  | mul_X f a hf =>
    obtain ⟨F, D, hF⟩ := hf
    refine ⟨F * chartMono (σ a), D + 1, fun x hx => ?_⟩
    simp only [map_mul, eval_chartMono, hF x hx, eval_X]
    field_simp
    ring

theorem chartIdeal_isPrime {Q : Ideal (MRingOver ℂ ι)} (hQp : Q.IsPrime)
    (hQh : IsMultiHomogIdeal Q) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    {i : (k : K) → ι k} (hw : chartMono i ∉ Q) (hne : chartIdeal (conePts Q) σ i ≠ ⊤) :
    (chartIdeal (conePts Q) σ i).IsPrime := by
  have back : ∀ (f : MvPolynomial (Fin m) ℂ) (F : MRingOver ℂ ι) (D : ℕ),
      (∀ x : (Σ k, ι k) → ℂ, segre x i ≠ 0 →
        eval x F = segre x i ^ D * eval (fun a => segre x (σ a) / segre x i) f) →
      F ∈ Q → f ∈ chartIdeal (conePts Q) σ i := by
    intro f F D hF hFQ
    rw [chartIdeal, mem_vanishingIdeal_iff]
    rintro _ ⟨z, hz, hz1, rfl⟩
    have h0 : segre z i ≠ 0 := by rw [hz1]; exact one_ne_zero
    have h := hF z h0
    rw [hz.2 F hFQ, hz1] at h
    simpa using h.symm
  refine ⟨hne, fun {f g} hfg => ?_⟩
  obtain ⟨F, D, hF⟩ := exists_homogenise σ i f
  obtain ⟨G, E, hG⟩ := exists_homogenise σ i g
  have hFG : F * G ∈ Q := mem_of_eval_eq_zero hQp hw fun x hx h0 => by
    have h1 : eval (fun a => segre x (σ a) / segre x i) (f * g) = 0 :=
      (mem_vanishingIdeal_iff.1 hfg) _ (normAt_mem_chartSet hQh σ hx h0)
    rw [map_mul] at h1
    rw [map_mul, hF x h0, hG x h0]
    linear_combination (segre x i ^ D * segre x i ^ E) * h1
  rcases hQp.mem_or_mem hFG with h | h
  · exact Or.inl (back f F D hF h)
  · exact Or.inr (back g G E hG h)

theorem eval_chartSection [DecidableEq K] {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (x : Fin m → ℂ) (s : MRingOver ℂ ι) : eval x (chartSection σ i s) = eval (chartLift σ i x) s := by
  induction s using MvPolynomial.induction_on with
  | C c => simp [chartSection]
  | add f g hf hg =>
    simp only [chartSection, map_add (f := _)] at hf hg ⊢
    rw [hf, hg]
  | mul_X f q hf =>
    simp only [chartSection, map_mul, aeval_X, eval_X] at hf ⊢
    rw [hf]
    rfl

end SecNotIn


open SecNotIn in
theorem chartSection_notMem_component : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (s : MRingOver ℂ ι) (a : K → ℕ),
    IsCxVar Q e → IsMultiHomog s a → s ∉ Q →
    ∀ J ∈ chartComponents (conePts Q) σ i, chartSection σ i s ∉ J := by
  intro K _ _ ι _ Q e m σ i s a hQ hs hsQ J hJ hmem
  obtain ⟨-, ⟨hQp, hQh, -⟩, -⟩ := hQ
  have hJmin := mem_chartComponents.1 hJ
  have hprimeJ : J.IsPrime := hJmin.1.1
  have hne : chartIdeal (conePts Q) σ i ≠ ⊤ := fun h =>
    hprimeJ.ne_top (top_le_iff.1 (h ▸ hJmin.1.2))
  have hw : chartMono i ∉ Q := by
    intro hwQ
    apply hne
    rw [Ideal.eq_top_iff_one, chartIdeal, mem_vanishingIdeal_iff]
    rintro _ ⟨z, hz, hz1, rfl⟩
    have h0 := hz.2 _ hwQ
    rw [eval_chartMono, hz1] at h0
    exact absurd h0 one_ne_zero
  have hprime := chartIdeal_isPrime hQp hQh σ hw hne
  have hJI : J ≤ chartIdeal (conePts Q) σ i := hJmin.2 ⟨hprime, le_rfl⟩ hJmin.1.2
  have hI := hJI hmem
  apply hsQ
  refine mem_of_eval_eq_zero hQp hw fun x hx h0 => ?_
  have hz1 : segre (normAt i x) i = 1 := by rw [segre_normAt, div_self h0]
  have hpt : (fun a => segre (normAt i x) (σ a)) ∈ chartSet (conePts Q) σ i :=
    ⟨normAt i x, normAt_mem hQh hx h0, hz1, rfl⟩
  have h1 : eval (fun a => segre (normAt i x) (σ a)) (chartSection σ i s) = 0 :=
    (mem_vanishingIdeal_iff.1 hI) _ hpt
  have hlift : chartLift σ i (fun a => segre (normAt i x) (σ a)) = normAt i x := by
    funext ⟨k, j⟩
    rw [chartLift_segre_apply σ i _ hz1]
    have : normAt i x ⟨k, i k⟩ = 1 := inv_mul_cancel₀ (entry_ne_zero h0 k)
    rw [this, inv_one, mul_one]
  rw [eval_chartSection, hlift] at h1
  have hsc : eval (normAt i x) s = (∏ k, ((x ⟨k, i k⟩)⁻¹) ^ a k) * eval x s :=
    ReciprocityTheory.AnForm.R.aeval_smul_of_isMultiHomog (fun d hd k => hs d hd k)
      (fun k => (x ⟨k, i k⟩)⁻¹) x
  rw [hsc] at h1
  refine (mul_eq_zero.1 h1).resolve_left ?_
  exact Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (inv_ne_zero (entry_ne_zero h0 k))

end GlobalTheory.CompanionTheory.Ar.Pub.CxChart
end
end

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

namespace GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

theorem exists_isKerProj (g : ℕ) (S : Matrix (Fin g) (Fin g) ℤ) :
    ∃ Pr : Matrix (Fin g) (Fin g) ℝ, IsKerProj S Pr := by
  classical
  set M : Matrix (Fin g) (Fin g) ℝ := S.map (fun x : ℤ => (x : ℝ)) with hM
  let K : Submodule ℝ (EuclideanSpace ℝ (Fin g)) := LinearMap.ker (Matrix.toEuclideanLin M)
  let P : EuclideanSpace ℝ (Fin g) →ₗ[ℝ] EuclideanSpace ℝ (Fin g) :=
    (K.starProjection : EuclideanSpace ℝ (Fin g) →ₗ[ℝ] EuclideanSpace ℝ (Fin g))
  let Pr : Matrix (Fin g) (Fin g) ℝ := Matrix.toEuclideanLin.symm P
  have hPr : Matrix.toEuclideanLin Pr = P := LinearEquiv.apply_symm_apply _ _
  have hmv : ∀ v : Fin g → ℝ, Pr *ᵥ v = WithLp.ofLp (P (WithLp.toLp 2 v)) := by
    intro v
    rw [← hPr, Matrix.toLpLin_apply]
  have hidem : ∀ x, P (P x) = P x := by
    intro x
    have hx : K.starProjection x ∈ K := Submodule.starProjection_apply_mem K x
    exact (Submodule.starProjection_eq_self_iff).2 hx
  refine ⟨Pr, ?_, ?_, ?_⟩
  · apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, hmv, hmv,
      WithLp.toLp_ofLp, hidem]
  · have hs : Pr.IsHermitian := by
      apply Matrix.isSymmetric_toEuclideanLin_iff.mp
      rw [hPr]
      exact Submodule.starProjection_isSymmetric K
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hs.eq
  · intro v
    rw [hmv]
    constructor
    · intro h
      have hk : WithLp.toLp 2 v ∈ K := by
        have h' : M *ᵥ v = 0 := h
        rw [LinearMap.mem_ker, Matrix.toLpLin_apply]
        simp [h']
      have : P (WithLp.toLp 2 v) = WithLp.toLp 2 v := (Submodule.starProjection_eq_self_iff).2 hk
      rw [this]
    · intro h
      have h1 : P (WithLp.toLp 2 v) = WithLp.toLp 2 v := by
        rw [← WithLp.toLp_ofLp (p := 2) (P (WithLp.toLp 2 v)), h]
      have hk : WithLp.toLp 2 v ∈ K := (Submodule.starProjection_eq_self_iff).1 h1
      rw [LinearMap.mem_ker, Matrix.toLpLin_apply] at hk
      have h' : M *ᵥ v = 0 := by simpa using hk
      exact h'

end GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder


theorem _root_.GlobalTheory.T.holomorphic_adapted_frame_on_ball : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (A₀ : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ), C.IsAdapted (F.R 0) A₀ → ∃ (Z : (Fin n → ℂ) → Fin n → ℂ) (G : (Fin n → ℂ) → ℂ), DifferentiableOn ℂ Z (ballDom F.q) ∧ DifferentiableOn ℂ G (ballDom F.q) ∧ (∀ t ∈ ballDom F.q, ∀ A, C.IsAdapted (F.R t) A → Z t = moebBall F.q (fun τ => C.cinv (A₀ τ) τ * A τ) 0) ∧ ∀ t ∈ ballDom F.q, ballPot F.q (Z t) = ballPot F.q t + (G t).re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.chart_exists | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.chart_exists | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.chart_exists <;> assumption)
end
