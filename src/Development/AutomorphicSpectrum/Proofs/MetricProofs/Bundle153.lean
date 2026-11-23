module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GenericBlockMatrixIsBlockDiag
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.XCWArith
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Weights
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle008
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle144
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle140
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle048
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle150
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBirationalModelExists
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle151
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

theorem _root_.GlobalTheory.CompanionTheory.Relay.flag_adjacent_swap_varieties_arithmetic : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (d : ℕ) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsArithVar (mCoordIdeal y) (d + 2) → IsArithVar (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) (d + 3) ∧ IsArithVar (mCoordIdeal (M.wCo (τ, a) k₀ ca cb 0)) (d + 2) ∧ mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X) ≤ mCoordIdeal (M.wCo (τ, a) k₀ ca cb 0) ∧ imageZ (fun p : (Σ k, ι k) => (⟨some p.1, p.2⟩ : Σ o : Option K, ι (o.getD k₀))) (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) = mCoordIdeal y ∧ ∀ v₁ : (Σ k, ι k) → (Σ o : Option K, ι (o.getD k₀)), (∀ p : (Σ k, ι k), p.1 ≠ k₀ → v₁ p = ⟨some p.1, p.2⟩) → (∀ m : ι k₀, v₁ ⟨k₀, m⟩ = ⟨none, m⟩) → imageZ v₁ (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) = mCoordIdeal y := by
  first | exact @PositivityTheory.Xgp.t_c_w_arith | exact PositivityTheory.Xgp.t_c_w_arith
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.CompanionTheory.Relay.vertical_factor_smooth_hermitian_metric : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W), ∀ p ∈ D.S, (∃ A : HermLine J, A.a = D.vdeg p ∧ IsSmoothHerm A ∧ IsConjInvariantH A ∧ ∀ z ∈ mcPts (mCoordIdeal D.y), A.h z = D.vertFactor p z) ∧ ∀ a, ∀ t ∈ Metric.ball (0 : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) 1, ∃ G : (Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) → ℂ, AnalyticAt ℂ G t ∧ ∀ᶠ t' in 𝓝 t, Real.log (D.vertFactor p ((D.chart a).γ t')) = (G t').re := by
  first | exact @LevelTowerAlt.vertical_factor_smooth_line | exact LevelTowerAlt.vertical_factor_smooth_line
end

section

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap)

namespace GlobalTheory.CompanionTheory.Ar.Giv

namespace ResTop

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem homog_mul {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m1 hm1 k, hg m2 hm2 k]

theorem coord_ne_zero {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (p : Σ k, ι k)
    (h : (X p : MRing ι) ∉ mCoordIdeal y) : y p ≠ 0 := by
  intro h0
  apply h
  unfold mCoordIdeal
  rw [RingHom.mem_ker]
  simp [mConeMap, h0]

theorem charZero_of_horizontal {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (h : IsHorizontal (mCoordIdeal y)) :
    CharZero Ω := by
  refine charZero_of_inj_zero fun n hn => ?_
  have h1 : (n : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := by
    rw [Ideal.mem_comap, mCoordIdeal, RingHom.mem_ker, map_natCast, map_natCast,
      ← map_natCast (C : Ω →+* MvPolynomial K Ω), hn, map_zero]
  rw [IsHorizontal] at h
  rw [h, Ideal.mem_bot] at h1
  exact_mod_cast h1

variable {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]

theorem isBlockMap_joinInl : IsBlockMap (Sum.inl : K → K ⊕ K₂) (joinInl ι ι₂) := by
  refine ⟨Sum.inl_injective, ?_, fun _ => rfl, ?_⟩
  · rintro ⟨k, i⟩ ⟨k', i'⟩ h
    have h1 : k = k' := Sum.inl_injective (congrArg Sigma.fst h)
    subst h1
    have h2 : i = i' := eq_of_heq (Sigma.mk.inj_iff.mp h).2
    rw [h2]
  · rintro ⟨k, i⟩ ⟨k', rfl⟩
    exact ⟨⟨k', i⟩, rfl⟩

theorem evC_rename_inl (z : (Σ k, joinIdx ι ι₂ k) → ℂ) (f : MRing ι) :
    evC z (rename (joinInl ι ι₂) f) = evC (z ∘ joinInl ι ι₂) f := by
  unfold evC
  rw [map_rename, eval_rename]

theorem comp_inl_mem {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (y₂ : (Σ k, ι₂ k) → Ω)
    {z : (Σ k, joinIdx ι ι₂ k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal (joinVec y y₂))) :
    z ∘ joinInl ι ι₂ ∈ mcPts (mCoordIdeal y) := by
  refine ⟨fun k => hz.1 (Sum.inl k), fun f hf => ?_⟩
  have hc : (mConeMap (joinVec y y₂)).comp (rename (joinInl ι ι₂)) =
      ((rename (Sum.inl : K → K ⊕ K₂) : MvPolynomial K Ω →ₐ[Ω] _).restrictScalars ℤ).comp (mConeMap y) := by
    refine MvPolynomial.algHom_ext fun p => ?_
    obtain ⟨k, i⟩ := p
    simp [mConeMap, joinInl, joinVec]
  have hf' : rename (joinInl ι ι₂) f ∈ mCoordIdeal (joinVec y y₂) := by
    have h1 := AlgHom.congr_fun hc f
    have h0 : mConeMap y f = 0 := hf
    simp only [AlgHom.comp_apply, h0, map_zero] at h1
    exact h1
  exact (evC_rename_inl z f).symm.trans (hz.2 _ hf')

end ResTop


open ResTop in
theorem resExists_of_resK : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ResExistsStatement := by
  intro hRes K _ ι _ P J e hP hJ hJP
  obtain ⟨Ω, _, y, rfl, -⟩ := GroundTheory.Heights₂.Heights.HilbertSamuel.BirationalModelExists.proof K ι P (e + 1) hP
  haveI : CharZero Ω := charZero_of_horizontal y hP.2.2.1
  have hprime : (mCoordIdeal y).IsPrime := hP.2.1.1
  obtain ⟨β, hβJ, ⟨b, hβ⟩, hβP⟩ : ∃ β ∈ J, (∃ b, IsMultiHomog β b) ∧ β ∉ mCoordIdeal y := by
    obtain ⟨S, hS, rfl⟩ := hJ
    by_contra hcon
    push Not at hcon
    exact hJP (Ideal.span_le.mpr fun f hf => hcon f (Ideal.subset_span hf) (hS f hf))
  obtain ⟨β', b', M, y', J₁, hβ', hβ'P, hzero, hy', hfield, hJ₁h, hJ₁, hsnc, hz, hG⟩ :=
    GlobalTheory.T.multihomogeneous_lift_to_join hRes K ι Ω y e β b hP hβ hβP
  have hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k => by
    obtain ⟨i, hi⟩ := hP.2.1.2.2 k
    exact ⟨i, coord_ne_zero y ⟨k, i⟩ hi⟩
  have hblocks : ∀ k, ∃ i, joinVec y y' ⟨k, i⟩ ≠ 0 := by
    rintro (k | u)
    · exact hy k
    · exact hy'
  have hcomp : joinVec y y' ∘ joinInl ι (fun _ : Unit => Fin M) = y := rfl
  have harith : IsArithVar (mCoordIdeal (joinVec y y')) (e + 1) := by
    refine isArithVar_of_isAlgebraic_image K ι (K ⊕ Unit) (joinIdx ι fun _ : Unit => Fin M) Sum.inl
      (joinInl ι fun _ : Unit => Fin M) Ω (joinVec y y') (e + 1) isBlockMap_joinInl hblocks ?_ ?_
    · rw [hcomp]; exact hP
    · rw [hcomp, hfield]
      intro t ht
      exact isAlgebraic_algebraMap (⟨t, ht⟩ : blockFnField y)
  obtain ⟨R, hR⟩ := GlobalTheory.T.snc_model_embedded_log_resolution (K ⊕ Unit) (joinIdx ι fun _ : Unit => Fin M) Ω (joinVec y y') e J₁
    harith hJ₁h hJ₁ hsnc
  have hγ := homog_mul hβ hβ'
  have hγP : β * β' ∉ mCoordIdeal y := fun h => (hprime.mem_or_mem h).elim hβP hβ'P
  have hmul : ∀ z : (Σ k, ι k) → ℂ, evC z (β * β') = evC z β * evC z β' := fun z => by
    simp only [evC, map_mul]
  refine ⟨Ideal.span {β * β'}, ?_, ⟨{β * β'}, ?_, rfl⟩, ?_, ?_⟩
  · rw [Ideal.span_singleton_le_iff_mem]
    exact J.mul_mem_right _ hβJ
  · rintro f rfl
    exact ⟨_, hγ⟩
  · rw [Ideal.span_singleton_le_iff_mem]
    exact hγP
  · refine GlobalTheory.T.multihomogeneous_nonvanishing_on_join K ι Ω y e M y' J₁ R (β * β') (b + b') hR hy' hy hγ hγP ?_ ?_
    · intro z hzm h0
      apply hz z hzm
      rw [evC_rename_inl] at h0 ⊢
      rw [hmul] at h0
      rcases mul_eq_zero.mp h0 with h | h
      · exact hzero _ (comp_inl_mem y y' hzm) h
      · exact h
    · intro z hzm hne
      apply hG z hzm
      rw [hmul] at hne
      exact right_ne_zero_of_mul hne

end GlobalTheory.CompanionTheory.Ar.Giv
end

section


theorem _root_.GlobalTheory.T.degree_and_coordinates_of_resolution : ReciprocityTheory.ChartRestriction.G.Geo.ResExistsStatement → ReciprocityTheory.ChartRestriction.G.AI.I4.GenDegStatement ∧ ReciprocityTheory.ChartRestriction.G.AI.I4.PFCoordStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.genDeg_and_pfCoord | exact GlobalTheory.CompanionTheory.Ar.Pub.genDeg_and_pfCoord | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.genDeg_and_pfCoord <;> assumption)
end
