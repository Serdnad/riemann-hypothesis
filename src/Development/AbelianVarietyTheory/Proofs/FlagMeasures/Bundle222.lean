module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle136
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle205
import Formalism.FormalDegreeBessel.FinalG
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle011
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnimodularLatticeFundamentalSetVolume
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle012
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFrameFixingIsometrySplitRowLattice
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle207
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle208
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryRepMatrixCoefficientBound
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle206
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle095
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle037
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle046
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle067
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle163
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalFlagExistsUniqueSemistable
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
public import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle184
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle002

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.YMeas

theorem exists_matrix_ker {n : ℕ} (Q : Submodule ℂ (Fin n → ℂ)) :
    ∃ M : Matrix (Fin n) (Fin n) ℂ, ∀ v, M *ᵥ v = 0 ↔ v ∈ Q := by
  obtain ⟨P, hP⟩ := Q.exists_isCompl
  refine ⟨LinearMap.toMatrix' (P.subtype ∘ₗ P.projectionOnto Q hP.symm), fun v => ?_⟩
  rw [LinearMap.toMatrix'_mulVec]
  simp

theorem measurable_proj {X : Type} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (Q : Submodule ℂ (Fin n → ℂ)) (g : X → Matrix (Fin n) (Fin n) ℂ)
    (v : X → EuclideanSpace ℂ (Fin n)) (hg : Continuous g) (hv : Continuous v) :
    Measurable fun x => ((LinearMap.ker (Matrix.toLin' A) ⊓ Q.comap (Matrix.toLin' (g x))).comap
      (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).toLinearMap).starProjection (v x) := by
  obtain ⟨M, hM⟩ := exists_matrix_ker Q
  let Φ : Matrix (Fin n ⊕ Fin n) (Fin n) ℂ →ₗ[ℂ]
      (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n ⊕ Fin n)) :=
    (LinearMap.toContinuousLinearMap.toLinearMap).comp Matrix.toEuclideanLin.toLinearMap
  have hΦ : Continuous Φ := Φ.continuous_of_finiteDimensional
  have hMg : Continuous fun x => M * g x := continuous_const.matrix_mul hg
  have hL : Continuous fun x => Matrix.fromRows A (M * g x) := by
    refine continuous_matrix fun i j => ?_
    rcases i with i | i
    · simpa using continuous_const
    · simpa using hMg.matrix_elem i j
  have h := GlobalTheory.measurable_starProjection_ker_clm (fun x => Φ (Matrix.fromRows A (M * g x))) v (hΦ.comp hL) hv
  have e : ∀ x, ((LinearMap.ker (Matrix.toLin' A) ⊓ Q.comap (Matrix.toLin' (g x))).comap
      (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).toLinearMap) =
      LinearMap.ker (Φ (Matrix.fromRows A (M * g x)) :
        EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n ⊕ Fin n)) := by
    intro x
    ext p
    have h1 : Φ (Matrix.fromRows A (M * g x)) p =
        WithLp.toLp 2 (Matrix.fromRows A (M * g x) *ᵥ p.ofLp) := rfl
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, h1, WithLp.toLp_eq_zero, Matrix.fromRows_mulVec,
      ← Matrix.mulVec_mulVec]
    simp only [Submodule.mem_comap, Submodule.mem_inf, LinearMap.mem_ker, Matrix.toLin'_apply, ← hM]
    constructor
    · rintro ⟨h2, h3⟩
      funext i
      rcases i with i | i
      · exact congrFun h2 i
      · exact congrFun h3 i
    · intro h2
      exact ⟨funext fun i => congrFun h2 (Sum.inl i), funext fun i => congrFun h2 (Sum.inr i)⟩
  simp only [e]
  exact h

theorem measurableSet_GG (k r : ℕ) : MeasurableSet {x : Mt k r | Matrix.of x ∈ GG k r} := by
  refine IsClosed.measurableSet ?_
  have hc : Continuous fun x : Mt k r => (Matrix.of x : Mat k r) := continuous_id
  exact isClosed_eq ((hc.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hc) continuous_const

theorem measurable_gramProj (k r j : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : Mat k r)
    (w : Fin j → Fin (2 * r + k + 1) → ℂ) :
    Measurable fun x : {x : Mt k r | Matrix.of x ∈ GG k r} =>
      gramProj (Ppos k r z z' γ (Matrix.of x.1)) (fun a : Fin j => (Matrix.of x.1 : Mat k r)⁻¹ *ᵥ w a) := by
  have hH : IsUnit (Hpk k r).det := Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1
  have hc : Continuous fun x : {x : Mt k r | Matrix.of x ∈ GG k r} => (Matrix.of x.1 : Mat k r) :=
    continuous_subtype_val
  have hinv : Continuous fun x : {x : Mt k r | Matrix.of x ∈ GG k r} => (Matrix.of x.1 : Mat k r)⁻¹ := by
    rw [continuous_iff_continuousAt]
    intro x
    have hx : IsUnit (Matrix.of x.1 : Mat k r).det := ((uHGroup _ _ hH).2.2 _ x.2).1
    have h1 : ContinuousAt (Inv.inv : Mat k r → _) (Matrix.of x.1) := by
      refine continuousAt_matrix_inv _ ?_
      obtain ⟨u, hu⟩ := hx
      rw [← hu]
      exact NormedRing.inverse_continuousAt u
    exact ContinuousAt.comp (f := fun x : {x : Mt k r | Matrix.of x ∈ GG k r} => (Matrix.of x.1 : Mat k r))
      h1 hc.continuousAt
  have hp : ∀ a : Fin j, Measurable fun x : {x : Mt k r | Matrix.of x ∈ GG k r} =>
      (Ppos k r z z' γ (Matrix.of x.1)).starProjection
        (WithLp.toLp 2 ((Matrix.of x.1 : Mat k r)⁻¹ *ᵥ w a)) := fun a =>
    measurable_proj (Hpk k r - 1) (Hcom k r z z' γ ⊔ Xsp k r) _ _ hc
      ((PiLp.continuous_toLp 2 _).comp (hinv.matrix_mulVec continuous_const))
  have hG : Continuous fun u : Fin j → EuclideanSpace ℂ (Fin (2 * r + k + 1)) =>
      Real.sqrt ‖(Matrix.gram ℂ u).det‖ := by
    refine Real.continuous_sqrt.comp (continuous_norm.comp (Continuous.matrix_det ?_))
    refine continuous_matrix fun a b => ?_
    simp only [Matrix.gram_apply]
    exact (continuous_apply a).inner (continuous_apply b)
  exact hG.measurable.comp (Measurable.of_eval hp)

theorem yj_measurable : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ γ : Mat k r, inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → γ ∈ GG k r → Measurable (Set.indicator {x : Mt k r | Matrix.of x ∈ GG k r} fun x => Yj k r hj z z' γ (Matrix.of x)) ∧ ∀ R₀ y : ℝ, MeasurableSet (Eset0 k r hj z z' γ R₀ y) := by
  intro k r j hj z z' γ hz hz' hT hT' hγ
  have hH : IsUnit (Hpk k r).det := Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1
  have hS := measurableSet_GG k r
  have hY : Measurable fun x : {x : Mt k r | Matrix.of x ∈ GG k r} => Yj k r hj z z' γ (Matrix.of x.1) :=
    (measurable_gramProj k r j z z' γ _).div_const _
  have hc : Continuous fun x : {x : Mt k r | Matrix.of x ∈ GG k r} => (Matrix.of x.1 : Mat k r) :=
    continuous_subtype_val
  have h1 : Continuous fun x : {x : Mt k r | Matrix.of x ∈ GG k r} => Sg2 k r z' (Matrix.of x.1) :=
    (TwoSided.Sg2_invariant_continuousOn_one_le_bounds k r z' hz' hT').2.2.1.comp_continuous hc fun x => x.2
  have h2 : Continuous fun x : {x : Mt k r | Matrix.of x ∈ GG k r} => Sg2 k r z (γ * Matrix.of x.1) :=
    (TwoSided.Sg2_invariant_continuousOn_one_le_bounds k r z hz hT).2.2.1.comp_continuous (continuous_const.matrix_mul hc)
      fun x => (uHGroup _ _ hH).2.1 _ hγ _ x.2
  refine ⟨?_, fun R₀ y => ?_⟩
  · refine measurable_of_restrict_of_restrict_compl hS ?_ ?_
    · convert hY using 1
      funext x
      exact Set.indicator_of_mem x.2 _
    · convert (measurable_const (a := (0 : ℝ))) using 1
      funext x
      exact Set.indicator_of_notMem x.2 _
  have e : Eset0 k r hj z z' γ R₀ y = Subtype.val '' {x : {x : Mt k r | Matrix.of x ∈ GG k r} |
      Sg2 k r z' (Matrix.of x.1) ≤ R₀ ∧ Sg2 k r z (γ * Matrix.of x.1) ≤ R₀ ∧
        y < Yj k r hj z z' γ (Matrix.of x.1) ∧ Yj k r hj z z' γ (Matrix.of x.1) ≤ 2 * y} := by
    ext x
    constructor
    · rintro ⟨hx, h⟩
      exact ⟨⟨x, hx⟩, h, rfl⟩
    · rintro ⟨⟨x, hx⟩, h, rfl⟩
      exact ⟨hx, h⟩
  rw [e]
  refine hS.subtype_image ?_
  exact (measurableSet_le h1.measurable measurable_const).inter
    ((measurableSet_le h2.measurable measurable_const).inter
      ((measurableSet_lt measurable_const hY).inter (measurableSet_le hY measurable_const)))

end GlobalTheory.Amp.YMeas
end
end

section

open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov

theorem _root_.GlobalTheory.T.realisation_mem_standard_middle_space : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V) (r : ℕ) (N : NF H r) (k : ℕ) (σ : K →+* ℂ) (ρ : ℝ) (β : Fin r → ℕ) (Φ : V → Fin (2 * r + k + 1) → ℂ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mat k r), 0 < ρ → IsFrameOf N k σ ρ β Φ z z' g → ∀ w ∈ N.Wn, inWb k r (Φ w) := by
  first | exact @GlobalTheory.DegVol.MidLift.inWb_of_mem_Wn | exact GlobalTheory.DegVol.MidLift.inWb_of_mem_Wn | (intros; apply GlobalTheory.DegVol.MidLift.inWb_of_mem_Wn <;> assumption)
end

section

open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.unimodular_lattice_fundamentalSet_volume : ∀ (K W : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (HW : HermSpace K W), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (k : ℕ) (ι : Type) [Fintype ι] (σ : ι → (K →+* ℂ)) (Ψ : ι → W → Fin (k + 1) → ℂ), IsPlaces σ → Module.finrank K W = k + 1 → (∀ v x y, Ψ v (x + y) = Ψ v x + Ψ v y) → (∀ v (c : K) x, Ψ v (c • x) = σ v c • Ψ v x) → (∀ v x y, herm (Hb k) (Ψ v x) (Ψ v y) = σ v (HW.B x y)) → ∀ (L : Submodule (𝓞 K) W) (𝔡 : Ideal (𝓞 K)) (n : ℤ) (ρ : ℝ), IsUnimod HW L → 𝔡 ≠ ⊥ → 0 < ρ → ∃ F : Set (ι → Fin (k + 1) → ℂ), MeasurableSet F ∧ (∀ a : ι → Fin (k + 1) → ℂ, ∃! x : W, x ∈ ipow 𝔡 n • L ∧ ((fun v => (ρ : ℂ) • Ψ v x) + a) ∈ F) ∧ volume F = ENNReal.ofReal ((Formalism.HermitianLatticesTheory.vInv K ^ Fintype.card ι * (Ideal.absNorm 𝔡 : ℝ) ^ n * ρ ^ (2 * Fintype.card ι)) ^ (k + 1)) := by
  first | exact @GlobalTheory.UnimodCov.unimod_fund | exact GlobalTheory.UnimodCov.unimod_fund | (intros; apply GlobalTheory.UnimodCov.unimod_fund <;> assumption)
end

section

namespace GlobalTheory.LoopC.CommonSub

section General

open NumberField

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V] [Module K V]

theorem span_eq_of_relIndex_ne_zero {P M : Submodule (𝓞 K) V} (hPM : P ≤ M)
    (h : P.toAddSubgroup.relIndex M.toAddSubgroup ≠ 0) :
    Submodule.span K (P : Set V) = Submodule.span K (M : Set V) := by
  refine le_antisymm (Submodule.span_mono hPM) ?_
  rw [Submodule.span_le]
  intro m hm

  have hn : (P.toAddSubgroup.relIndex M.toAddSubgroup) • m ∈ P :=
    AddSubgroup.nsmul_relIndex_mem P.toAddSubgroup (K := M.toAddSubgroup) hm
  have hnK : ((P.toAddSubgroup.relIndex M.toAddSubgroup : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr h
  have hm' : m = ((P.toAddSubgroup.relIndex M.toAddSubgroup : ℕ) : K)⁻¹ •
      (P.toAddSubgroup.relIndex M.toAddSubgroup • m) := by
    rw [← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ hnK, one_smul]
  rw [SetLike.mem_coe, hm']
  exact Submodule.smul_mem _ _ (Submodule.subset_span hn)

omit [NumberField K] [Module K V] in
theorem relIndex_inf_bound {M A' A'' B' B'' : Submodule (𝓞 K) V} (h1 : M ≤ A') (h2 : M ≤ A'')
    (n1 : B'.toAddSubgroup.relIndex A'.toAddSubgroup ≠ 0)
    (n2 : B''.toAddSubgroup.relIndex A''.toAddSubgroup ≠ 0) :
    ((B' ⊓ B'') ⊓ M).toAddSubgroup.relIndex M.toAddSubgroup ≠ 0 ∧
    ((B' ⊓ B'') ⊓ M).toAddSubgroup.relIndex M.toAddSubgroup ≤
      B'.toAddSubgroup.relIndex A'.toAddSubgroup * B''.toAddSubgroup.relIndex A''.toAddSubgroup := by
  have e : ((B' ⊓ B'') ⊓ M).toAddSubgroup.relIndex M.toAddSubgroup =
      (B'.toAddSubgroup ⊓ B''.toAddSubgroup).relIndex M.toAddSubgroup :=
    AddSubgroup.inf_relIndex_right (B'.toAddSubgroup ⊓ B''.toAddSubgroup) M.toAddSubgroup
  have h1' : M.toAddSubgroup ≤ A'.toAddSubgroup := fun x hx => h1 hx
  have h2' : M.toAddSubgroup ≤ A''.toAddSubgroup := fun x hx => h2 hx

  have m1 : B'.toAddSubgroup.relIndex M.toAddSubgroup ≠ 0 :=
    mt (AddSubgroup.relIndex_eq_zero_of_le_right h1') n1
  have m2 : B''.toAddSubgroup.relIndex M.toAddSubgroup ≠ 0 :=
    mt (AddSubgroup.relIndex_eq_zero_of_le_right h2') n2
  rw [e]
  refine ⟨AddSubgroup.relIndex_inf_ne_zero m1 m2, ?_⟩
  calc (B'.toAddSubgroup ⊓ B''.toAddSubgroup).relIndex M.toAddSubgroup
      ≤ B'.toAddSubgroup.relIndex M.toAddSubgroup * B''.toAddSubgroup.relIndex M.toAddSubgroup :=
        AddSubgroup.relIndex_inf_le
    _ ≤ _ := Nat.mul_le_mul (AddSubgroup.relIndex_le_of_le_right h1' n1)
        (AddSubgroup.relIndex_le_of_le_right h2' n2)

end General

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem idxW_eq (D : D7) (A B : LatW D) : idxW D A B = B.toAddSubgroup.relIndex A.toAddSubgroup := rfl

theorem main : ∀ (D : D7) (L M A' A'' B' B'' : LatW D), IsPosDef (D.sp.X 0).hT → L.FG → Formalism.HermitianLatticesTheory.IsIntegralLat (D.sp.X 0).hT L → M ≤ A' → M ≤ A'' → A' ≤ L → A'' ≤ L → B' ≤ A' → B'' ≤ A'' → rkW D B' = rkW D A' → rkW D B'' = rkW D A'' → ∃ P : LatW D, P ≤ M ∧ P ≤ B' ∧ P ≤ B'' ∧ rkW D P = rkW D M ∧ detW D P ≤ detW D M * (idxW D A' B' : ℝ) * (idxW D A'' B'' : ℝ) := by
  intro D L M A' A'' B' B'' hPD hL hI hMA' hMA'' hA'L hA''L hB' hB'' r1 r2
  have hfg : ∀ N : LatW D, N ≤ L → N.FG := fun N hN => Submodule.FG.of_le hL hN
  have hint : ∀ N : LatW D, N ≤ L → Formalism.HermitianLatticesTheory.IsIntegralLat (D.sp.X 0).hT N :=
    fun N hN x hx y hy => hI x (hN hx) y (hN hy)

  have k1 := ((GlobalTheory.LoopC.DetCard.main D A' (hfg _ hA'L) hPD (hint _ hA'L)).2.2 B' hB' r1).1
  have k2 := ((GlobalTheory.LoopC.DetCard.main D A'' (hfg _ hA''L) hPD (hint _ hA''L)).2.2 B'' hB'' r2).1
  rw [idxW_eq] at k1 k2
  obtain ⟨n0, nle⟩ := relIndex_inf_bound (K := D.host.E) hMA' hMA''
    (Nat.one_le_iff_ne_zero.mp k1) (Nat.one_le_iff_ne_zero.mp k2)
  have hrk : rkW D ((B' ⊓ B'') ⊓ M) = rkW D M := by
    unfold rkW
    rw [span_eq_of_relIndex_ne_zero (K := D.host.E) inf_le_right n0]
  have hML : M ≤ L := hMA'.trans hA'L
  have k3 := (GlobalTheory.LoopC.DetCard.main D M (hfg _ hML) hPD (hint _ hML)).2.2 _ inf_le_right hrk
  refine ⟨(B' ⊓ B'') ⊓ M, inf_le_right, fun x hx => hx.1.1, fun x hx => hx.1.2, hrk, ?_⟩
  have hd : 0 ≤ detW D M := Real.sqrt_nonneg _
  rw [k3.2, mul_assoc, idxW_eq, idxW_eq, idxW_eq]
  gcongr
  exact_mod_cast nle

end GlobalTheory.LoopC.CommonSub
end

section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_frameFixing_isometry_split_rowLattice : ∀ (D : D7) (u : D.what₂.Word) (F0 : Fb D u) (Λ : LatV D), IsBase D u F0 → IsRowLat D F0 Λ → 1 ≤ Tu D u → ∃ n : ((hS D).V ≃ₗ[D.host.E] (hS D).V), FixFr D (lf D F0) n ∧ IsSplit D F0 (Formalism.HermitianLatticesTheory.gmap n Λ) ∧ IsRowLat D F0 (Formalism.HermitianLatticesTheory.gmap n Λ) := by
  first | exact @GlobalTheory.LoopC.RowSplit.main | exact GlobalTheory.LoopC.RowSplit.main | (intros; apply GlobalTheory.LoopC.RowSplit.main <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.TermCount

theorem encard_le_mul {α β : Type} (s : Set α) (f : α → β) (t : Set β) (A B : ℝ≥0∞)
    (hf : ∀ a ∈ s, f a ∈ t) (ht : (t.encard : ℝ≥0∞) ≤ A)
    (hB : ∀ b ∈ t, (({a | a ∈ s ∧ f a = b} : Set α).encard : ℝ≥0∞) ≤ B) :
    (s.encard : ℝ≥0∞) ≤ A * B := by
  have h1 : s ⊆ ⋃ b : t, {a | a ∈ s ∧ f a = b.1} := by
    intro a ha
    exact Set.mem_iUnion.2 ⟨⟨f a, hf a ha⟩, ha, rfl⟩
  calc (s.encard : ℝ≥0∞) = ∑' _ : s, (1 : ℝ≥0∞) := (ENNReal.tsum_set_one s).symm
    _ ≤ ∑' _ : (⋃ b : t, {a | a ∈ s ∧ f a = b.1} : Set α), (1 : ℝ≥0∞) :=
        ENNReal.tsum_mono_subtype (fun _ => (1 : ℝ≥0∞)) h1
    _ ≤ ∑' b : t, ∑' _ : ({a | a ∈ s ∧ f a = b.1} : Set α), (1 : ℝ≥0∞) :=
        ENNReal.tsum_iUnion_le_tsum (fun _ => (1 : ℝ≥0∞)) _
    _ ≤ ∑' _ : t, B := by
        refine ENNReal.tsum_le_tsum fun b => ?_
        rw [ENNReal.tsum_set_one]
        exact hB b.1 b.2
    _ = (t.encard : ℝ≥0∞) * B := ENNReal.tsum_set_const t B
    _ ≤ A * B := by gcongr

theorem nT_cardI_le {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
    (L : LocE F E) (r k : ℕ) (S : Frames L r k) (d : S.Datum) (C : Set S.FrP) (j : ℕ) :
    (S.nT d C fun Λ => S.cardI d Λ = j) ≤ ENNReal.ofReal (S.Hp ^ (12 * (r + 1)) * (j : ℝ) ^ (k - 1)) := by
  unfold Frames.nT
  set s : Set (Submodule L.O S.V) := {Λ | S.IsTerm d Λ ∧ S.cardI d Λ = j ∧ S.Fr d Λ = C} with hs
  rcases s.eq_empty_or_nonempty with he | ⟨Λ₁, hΛ₁, -, hC₁⟩
  · simp [he]
  obtain ⟨ha, -, -, hq, hH1, -⟩ := GlobalTheory.T.term_exponents_nonneg_and_defect_group_bound L r k S d Λ₁ hΛ₁
  have hcls : S.IsCls C := hC₁ ▸ (GlobalTheory.HL.TermBasic.term_basic L r k S d Λ₁ hΛ₁).2.2.2.2.2.2.1.1
  have hp : (S.fr d Λ₁, S.fr' d Λ₁) ∈ C :=
    hC₁ ▸ (GlobalTheory.HL.FrameClass.frame_classes L r k S (S.fr d Λ₁) (S.fr' d Λ₁)).1
  have hM : ∀ Λ ∈ s, S.Mof (S.fr d Λ₁) (S.fr' d Λ₁) ≤ S.sat Λ := by
    rintro Λ ⟨hΛ, -, hC⟩
    have h1 := ((GlobalTheory.HL.FrameClass.frame_classes L r k S (S.fr d Λ) (S.fr' d Λ)).2.1
      (S.fr d Λ₁, S.fr' d Λ₁) (by
        have : S.frameCls (S.fr d Λ) (S.fr' d Λ) = C := hC
        rw [this]; exact hp)).2
    simp only at h1
    rw [h1]
    exact (GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hΛ).2.2.1
  have hmain : (s.encard : ℝ≥0∞) ≤ (S.q : ℝ≥0∞) ^ (2 * S.a.toNat * (2 * r + 2)) *
      (((S.q : ℝ≥0∞) ^ (S.a.toNat * (2 * r + 2)) * (j : ℝ≥0∞) ^ (k - 1)) *
        (S.q : ℝ≥0∞) ^ (2 * S.a.toNat * (2 * r + 2))) := by
    refine encard_le_mul s S.sat _ _ _ ?_ (GlobalTheory.T.lattice_count_bound_frames L r k S C hcls _ hp ha) ?_
    · intro Λ hΛ
      refine ⟨hM Λ hΛ, fun x hx => hx.2, fun x hx y hy => ?_⟩
      exact ((GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hΛ.1).1.2 y).2 hy.1 x hx.1
    · intro Mh hMh
      refine encard_le_mul _ (fun Λ : Submodule L.O S.V => Λ ⊓ S.W0.restrictScalars L.O) _ _ _ ?_
        (GlobalTheory.T.encard_gluingHom_kernels_le L r k S d C Mh j) ?_
      · rintro Λ ⟨⟨h1, h2, h3⟩, h4⟩
        exact ⟨Λ, ⟨h1, h3, h4, h2⟩, rfl⟩
      · intro Λ₀ _
        refine le_trans ?_ (GlobalTheory.T.encard_selfDual_sat_inf_W0_le_q_pow L r k S C hcls _ hp Mh Λ₀ hMh.1)
        refine ENat.toENNReal_le.2 (Set.encard_le_encard ?_)
        rintro Λ ⟨⟨⟨h1, -, -⟩, h4⟩, h5⟩
        exact ⟨(GlobalTheory.HL.TermBasic.term_basic L r k S d Λ h1).1, h4, h5⟩
  refine hmain.trans ?_
  have hq' : (S.q : ℝ) ^ S.a.toNat ≤ S.Hp := by
    have : S.a = (S.a.toNat : ℤ) := (Int.toNat_of_nonneg ha).symm
    rw [this, zpow_natCast] at hq
    exact hq
  have hreal : ((S.q : ℝ) ^ S.a.toNat) ^ (10 * (r + 1)) * (j : ℝ) ^ (k - 1) ≤
      S.Hp ^ (12 * (r + 1)) * (j : ℝ) ^ (k - 1) := by
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    calc ((S.q : ℝ) ^ S.a.toNat) ^ (10 * (r + 1)) ≤ S.Hp ^ (10 * (r + 1)) :=
          pow_le_pow_left₀ (by positivity) hq' _
      _ ≤ S.Hp ^ (12 * (r + 1)) := pow_le_pow_right₀ hH1 (by omega)
  refine le_trans (le_of_eq ?_) (ENNReal.ofReal_le_ofReal hreal)
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  ring

end GlobalTheory.HL.TermCount
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.selfDualHermitianLattice_mass_of_trace : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 2 * r + 6 ≤ k → (∃ Λ, IsSD L S.Hm Λ) → ∃ κ : ℝ, 0 < κ ∧ ∀ C, S.IsCls C → ∀ p ∈ C, ∀ Mh : Submodule L.O S.V, S.Mof p.1 p.2 ≤ Mh → (∀ x ∈ Mh, x ∈ S.ME) → (∀ x ∈ Mh, ∀ y ∈ Mh, S.h x y ∈ L.O) → ENNReal.ofReal (κ / 2 * (((S.Mof p.1 p.2).toAddSubgroup.relIndex Mh.toAddSubgroup : ℝ) ^ (k - 1))⁻¹) ≤ S.massSig Mh ∧ S.massSig Mh ≤ ENNReal.ofReal (2 * κ * (((S.Mof p.1 p.2).toAddSubgroup.relIndex Mh.toAddSubgroup : ℝ) ^ (k - 1))⁻¹) := by
  first | exact @GlobalTheory.HL.FrameMass.mass_trace | exact GlobalTheory.HL.FrameMass.mass_trace | (intros; apply GlobalTheory.HL.FrameMass.mass_trace <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.ampSq_le_of_hermitianTermTypes_cauchySchwarz : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ B : ℝ≥0∞, (∀ β, (S.ampSq fun d Λ => ¬ S.BBzero d Λ ∧ ¬ S.TypeBe d Λ ∧ S.be d Λ = β) ≤ B) → (∀ β J βJ, S.ampSq (S.InFF β J βJ) ≤ B) → (S.ampSq fun d Λ => ¬ S.BBzero d Λ) ≤ ENNReal.ofReal (S.Hp ^ (2 * (r + 2))) * B := by
  first | exact @GlobalTheory.HL.TypesCS.ampSq_le_of_types | exact GlobalTheory.HL.TypesCS.ampSq_le_of_types | (intros; apply GlobalTheory.HL.TypesCS.ampSq_le_of_types <;> assumption)
end

section

open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

theorem _root_.GlobalTheory.T.trivial_mod_chosen_primes_iff_mem_Kg : ∀ (I : AutInst) (N : ℕ) (g : Fin 2 → ℕ) (Pl : Fin 2 → Type) (w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)) (fr : ∀ k v, PlFrame I N (g k) (w k v)), I.n = N → IsChoice I g Pl w → ∀ x ∈ I.Kset, (∀ k v (y : I.Lf) (h : I.fmat x *ᵥ (y : Fin I.n → _) ∈ I.Lf), (fr k v).c ⟨_, h⟩ = (fr k v).c y) ↔ x ∈ I.Kg (g 0 * g 1) := by
  first | exact @GlobalTheory.RowLev.trivial_iff_mem_Kg | exact GlobalTheory.RowLev.trivial_iff_mem_Kg | (intros; apply GlobalTheory.RowLev.trivial_iff_mem_Kg <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

theorem _root_.GlobalTheory.T.unitary_rep_matrix_coefficient_bound : ∀ (n : ℕ) (ε : Fin n → Bool) (W : Submodule ℂ (Fin n → ℂ)) (ν : Measure (UJ ε)), IsIsoC ε W → IsHaarSub (NW ε W) ν → ∀ β : UJ ε → ENNReal, Measurable β → (∀ y, β y ≠ ⊤) → (∀ y, ∫⁻ m, β (m⁻¹ * y) ∂ν = 1) → ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (d c : ℝ) (u v v' : H), IsURepOn (UJset ε) σ → IsFdeg (muG ε) σ d → 8 * n * rkR ε < c → (∃ C : ℝ, ∀ g : UJ ε, ‖⟪v, σ (umat g) u⟫_ℂ‖ ≤ C * Real.exp (-(c * dOp (umat g)))) → (∃ C : ℝ, ∀ g : UJ ε, ‖⟪v', σ (umat g) u⟫_ℂ‖ ≤ C * Real.exp (-(c * dOp (umat g)))) → (∃ C : ℝ, ∀ g : UJ ε, ‖⟪v, σ (umat g) v'⟫_ℂ‖ ≤ C * Real.exp (-(c * dOp (umat g)))) → Continuous (fun g : UJ ε => (∫ m, ⟪v, σ (umat (m * g)) u⟫_ℂ ∂ν)) ∧ Integrable (fun g : UJ ε => ((β g).toReal : ℂ) * ((∫ m, ⟪v, σ (umat (m * g)) u⟫_ℂ ∂ν) * star (∫ m, ⟪v', σ (umat (m * g)) u⟫_ℂ ∂ν))) (muG ε) ∧ ∫ g : UJ ε, ((β g).toReal : ℂ) * ((∫ m, ⟪v, σ (umat (m * g)) u⟫_ℂ ∂ν) * star (∫ m, ⟪v', σ (umat (m * g)) u⟫_ℂ ∂ν)) ∂(muG ε) = (∫ m, ⟪v, σ (umat m) v'⟫_ℂ ∂ν) * ((‖u‖ ^ 2 / d : ℝ) : ℂ) := by
  first | exact @GlobalTheory.Dec.ConstTermNorm.constTerm_inner | exact GlobalTheory.Dec.ConstTermNorm.constTerm_inner | (intros; apply GlobalTheory.Dec.ConstTermNorm.constTerm_inner <;> assumption)
end

section

open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset

theorem _root_.GlobalTheory.T.inv_le_sizeQ_above_orthogonal_saturated : ∀ (I : AutInst) (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) (hi : ℝ), IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) R → 0 < hi → largestSize (bas I) (frm I x) R ≤ hi → ∀ N, perpIn I x R < N → N ≤ lamX I x → hi⁻¹ ≤ sizeQ (bas I) (frm I x) N (perpIn I x R) := by
  first | exact @GlobalTheory.Count.PerpSize.inv_le_sizeQ_perp | exact GlobalTheory.Count.PerpSize.inv_le_sizeQ_perp | (intros; apply GlobalTheory.Count.PerpSize.inv_le_sizeQ_perp <;> assumption)
end

section

open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset

theorem _root_.GlobalTheory.T.canonicalFlag_exists_unique_semistable : ∀ (I : AutInst) (x : I.GA), (∃ (a : ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (τ : Fin a → ℝ), HasFlag I x S τ) ∧ (∀ (a a' : ℕ) (j : Fin a → ℕ) (τ : Fin a → ℝ) (j' : Fin a' → ℕ) (τ' : Fin a' → ℝ), HasType I x j τ → HasType I x j' τ' → ∃ h : a = a', (∀ i, j i = j' (Fin.cast h i)) ∧ ∀ i, τ i = τ' (Fin.cast h i)) ∧ ∀ (a : ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (τ : Fin a → ℝ), HasFlag I x S τ → (∀ i : Fin a, S i.castSucc = stepLt I x (τ i) ∧ rkK (S i.castSucc) < rkK (S i.succ) ∧ largestSize (bas I) (frm I x) (S i.succ) = τ i ∧ (∀ N, S i.castSucc < N → N ≤ lamX I x → τ i ≤ sizeQ (bas I) (frm I x) N (S i.castSucc)) ∧ ∀ N, S i.castSucc ≤ N → IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (S i.succ) N → N ≠ S i.succ → sizeQ (bas I) (frm I x) (S i.succ) N ≤ τ i) ∧ (1 ≤ I.n → (a = 0 ↔ 1 / 2 ≤ least I x) ∧ ∀ h : 0 < a, τ ⟨0, h⟩ = least I x) := by
  first | exact @GlobalTheory.PointFlag.flag_spec | exact GlobalTheory.PointFlag.flag_spec | (intros; apply GlobalTheory.PointFlag.flag_spec <;> assumption)
end
