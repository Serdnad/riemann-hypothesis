module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle404
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Formalism.DoubleCosetMeasures.StatementZ
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle405
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle422
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle418
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle231
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle419
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle174
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle428
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Polynomial.IsIntegral
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
public import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Sheaves.Init
public import Formalism.DoubleCosetMeasures.Statement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle387
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle002

@[expose] public section

section

open MeasureTheory GlobalTheory.SplitFlip
open scoped Matrix

noncomputable section

namespace GlobalTheory.FullRankCoinv

theorem continuous_of_mul_right_inv {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
    (H : Subgroup G) (hH : IsOpen (H : Set G)) (f : G → ℂ) (hf : ∀ g, ∀ h ∈ H, f (g * h) = f g) : Continuous f := by
  refine continuous_iff_continuousAt.2 fun g => ?_
  have ho : IsOpen ((g⁻¹ * ·) ⁻¹' (H : Set G)) := hH.preimage (continuous_const.mul continuous_id)
  have hev : ∀ᶠ x in nhds g, f g = f x := by
    filter_upwards [ho.mem_nhds (by simpa using H.one_mem)] with x hx
    have := hf g (g⁻¹ * x) hx
    simpa using this.symm
  exact tendsto_const_nhds.congr' hev

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_gdet (n : ℕ) : Continuous (gdet : GL (Fin n) k → kˣ) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · convert (Units.continuous_val (M := Matrix (Fin n) (Fin n) k)).matrix_det using 1
    funext g; exact Matrix.GeneralLinearGroup.val_det_apply g
  · convert (Units.continuous_coe_inv (M := Matrix (Fin n) (Fin n) k)).matrix_det using 1
    funext g
    show (((gdet g)⁻¹ : kˣ) : k) = _
    rw [← map_inv]; exact Matrix.GeneralLinearGroup.val_det_apply _

theorem continuous_char_apow (n : ℕ) (ν : kˣ →* ℂˣ) (hν : GlobalTheory.SmGL.IsSmoothChar ν) (z : ℂ) :
    Continuous fun g : GL (Fin n) k => (ν (gdet g) : ℂ) * apow (gdet g) z := by
  let H : Subgroup (GL (Fin n) k) := GlobalTheory.SplitWeil.KO k (Fin n) ⊓ ν.ker.comap Matrix.GeneralLinearGroup.det
  have hH : IsOpen (H : Set (GL (Fin n) k)) :=
    isOpen_KO.inter (hν.preimage (continuous_gdet (k := k) n))
  refine continuous_of_mul_right_inv H hH _ fun g h hh => ?_
  have h1 : ν (gdet h) = 1 := hh.2
  have h2 : apow (gdet h) z = 1 := apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hh.1) z
  simp only [gdet_mul, map_mul, Units.val_mul, apow_mul, h1, h2, Units.val_one, mul_one]

theorem integrable_fibre (n d : ℕ) (ν : kˣ →* ℂˣ) (hν : GlobalTheory.SmGL.IsSmoothChar ν)
    [MeasurableSpace k] [BorelSpace k] (Ψ : Matrix (Fin n) (Fin d) k → ℂ) (hΨ : Ψ ∈ fullRk k n d)
    (Y : Matrix (Fin n) (Fin d) k) :
    Integrable (fun g : GL (Fin n) k =>
      Ψ (g.val * Y) * (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card (Fin d) : ℂ) / 2))
      (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) := by
  obtain ⟨⟨hlc, hcs⟩, hrk⟩ := hΨ
  by_cases hY : Y.rank = n
  swap
  · have h0 : (fun g : GL (Fin n) k =>
        Ψ (g.val * Y) * (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card (Fin d) : ℂ) / 2)) = 0 := by
      funext g
      have : (g.val * Y).rank = Y.rank :=
        Matrix.rank_mul_eq_right_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit)
      rw [hrk _ (by rw [this]; exact hY)]; simp
    rw [h0]; exact integrable_zero _ _ _

  obtain ⟨R, hR⟩ : ∃ R : Matrix (Fin d) (Fin n) k, Y * R = 1 := by
    have hsurj : LinearMap.range Y.mulVecLin = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [Module.finrank_fin_fun, Matrix.finrank_range_mulVecLin]; exact hY
    obtain ⟨f, hf⟩ := LinearMap.exists_rightInverse_of_surjective _ hsurj
    refine ⟨LinearMap.toMatrix' f, ?_⟩
    have := congrArg LinearMap.toMatrix' hf
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id,
      show LinearMap.toMatrix' Y.mulVecLin = Y from LinearMap.toMatrix'_toLin' Y] at this

  have hsupp : tsupport Ψ = Function.support Ψ := by
    refine (IsClosed.closure_eq ?_)
    convert (hlc.isOpen_fiber 0).isClosed_compl using 1
    ext x; simp [Function.support]
  have hrkS : ∀ X ∈ tsupport Ψ, X.rank = n := fun X hX => by
    by_contra h; rw [hsupp] at hX; exact hX (hrk X h)
  set K' : Set (Matrix (Fin n) (Fin d) k) := tsupport Ψ ∩ {X | X * R * Y = X}
  have hK' : IsCompact K' := hcs.inter_right
    (isClosed_eq ((continuous_id.matrix_mul continuous_const).matrix_mul continuous_const) continuous_id)
  have hunit : ∀ X ∈ K', IsUnit (X * R) := fun X hX => by
    have h1 : n ≤ (X * R).rank := by
      calc n = X.rank := (hrkS X hX.1).symm
        _ = (X * R * Y).rank := by rw [hX.2]
        _ ≤ (X * R).rank := Matrix.rank_mul_le_left _ _
    have h2 : (X * R).rank = Fintype.card (Fin n) := le_antisymm
      ((Matrix.rank_le_card_width _).trans (by simp)) (by simpa using h1)
    have hli : LinearIndependent k (X * R).row := by
      rw [linearIndependent_iff_card_eq_finrank_span]
      exact h2.symm.trans (Matrix.rank_eq_finrank_span_row _)
    exact Matrix.linearIndependent_rows_iff_isUnit.1 hli
  classical
  let φ : Matrix (Fin n) (Fin d) k → GL (Fin n) k := fun X =>
    if h : IsUnit (X * R) then h.unit else 1
  have hφ : ∀ X ∈ K', (φ X).val = X * R := fun X hX => by simp [φ, hunit X hX]
  have hφc : ContinuousOn φ K' := by
    rw [(isEmbedding_val_GL (k := k) (n := Fin n)).isInducing.continuousOn_iff]
    exact (continuous_id.matrix_mul continuous_const).continuousOn.congr fun X hX => hφ X hX
  set S : Set (GL (Fin n) k) := {g | g.val * Y ∈ tsupport Ψ}
  have hSsub : S ⊆ φ '' K' := fun g hg => by
    have hX : g.val * Y ∈ K' := ⟨hg, show g.val * Y * R * Y = g.val * Y by rw [Matrix.mul_assoc g.val Y R, hR, Matrix.mul_one]⟩
    refine ⟨_, hX, Units.ext ?_⟩
    rw [hφ _ hX, Matrix.mul_assoc, hR, Matrix.mul_one]
  have hSc : IsClosed S := (isClosed_tsupport Ψ).preimage (Units.continuous_val.matrix_mul continuous_const)
  have hS : IsCompact S := (hK'.image_of_continuousOn hφc).of_isClosed_subset hSc hSsub
  have hcont : Continuous (fun g : GL (Fin n) k =>
      Ψ (g.val * Y) * (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card (Fin d) : ℂ) / 2)) := by
    have h1 : Continuous fun g : GL (Fin n) k => Ψ (g.val * Y) :=
      hlc.continuous.comp (Units.continuous_val.matrix_mul continuous_const)
    refine (h1.mul (continuous_char_apow n ν hν ((Fintype.card (Fin d) : ℂ) / 2))).congr fun g => ?_
    simp only [Pi.mul_apply]; ring
  letI : MeasurableSpace (GL (Fin n) k) := Units.instMeasurableSpace
  haveI : BorelSpace (GL (Fin n) k) := borel_GL
  refine hcont.integrable_of_hasCompactSupport (μ := haarVol (GlobalTheory.SplitWeil.KO k (Fin n)))
    (HasCompactSupport.intro hS fun g hg => ?_)
  rw [image_eq_zero_of_notMem_tsupport hg]; simp

end GlobalTheory.FullRankCoinv

theorem GlobalTheory.FullRankCoinv.integrable_fibre_target : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (n d : ℕ) (ν : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν →
    ∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d,
    ∀ Y : Matrix (Fin n) (Fin d) k, Integrable (fun g : GL (Fin n) k =>
      Ψ (g.val * Y) * (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card (Fin d) : ℂ) / 2)) (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) :=
  fun _ _ _ _ _ _ _ n d ν hν Ψ hΨ Y => GlobalTheory.FullRankCoinv.integrable_fibre n d ν hν Ψ hΨ Y
end
end

section

noncomputable section

open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix Topology

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace GlobalTheory.FullRankCoinv.Average

theorem integral_comp_finite {G V : Type*} [MeasurableSpace G] (μ : Measure G) [IsFiniteMeasure μ] (F : G → V)
    (T : Finset V) (hT : ∀ᵐ g ∂μ, F g ∈ T) (hm : ∀ v, MeasurableSet (F ⁻¹' {v})) (φ : V → ℂ) :
    ∫ g, φ (F g) ∂μ = ∑ v ∈ T, (μ.real (F ⁻¹' {v}) : ℂ) * φ v := by
  classical
  have h1 : (fun g => φ (F g)) =ᵐ[μ] fun g => ∑ v ∈ T, (F ⁻¹' {v}).indicator (fun _ => φ v) g := by
    filter_upwards [hT] with g hg
    rw [Finset.sum_eq_single (F g)]
    · rw [Set.indicator_of_mem (by simp)]
    · intro v _ hv
      exact Set.indicator_of_notMem (by simpa using hv.symm) _
    · exact fun h => absurd hg h
  rw [integral_congr_ae h1, integral_finsetSum _ fun v _ => (integrable_const _).indicator (hm v)]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [integral_indicator_const _ (hm v), Complex.real_smul]

theorem sb_left_invariant {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n d : ℕ} (Ψ : Matrix (Fin n) (Fin d) k → ℂ) (hΨ : Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k)) :
    ∀ᶠ u in 𝓝 (1 : GL (Fin n) k), ∀ X : Matrix (Fin n) (Fin d) k, Ψ (u.val * X) = Ψ X := by
  have h1 : ∀ᶠ u in 𝓝 (1 : GL (Fin n) k), ∀ X ∈ tsupport Ψ, Ψ (u.val * X) = Ψ X := by
    refine IsCompact.eventually_forall_of_forall_eventually hΨ.2 fun y _ => ?_
    have h2 : IsLocallyConstant fun q : GL (Fin n) k × Matrix (Fin n) (Fin d) k => (Ψ (q.1.val * q.2), Ψ q.2) :=
      (hΨ.1.comp_continuous (by fun_prop)).prodMk (hΨ.1.comp_continuous continuous_snd)
    filter_upwards [h2.eventually_eq (1, y)] with q hq
    simp only [Prod.mk.injEq, Units.val_one, Matrix.one_mul] at hq
    rw [hq.1, hq.2]
  have h3 : ∀ᶠ u in 𝓝 (1 : GL (Fin n) k), ∀ X ∈ tsupport Ψ, Ψ ((u⁻¹).val * X) = Ψ X := by
    have ht : Filter.Tendsto (fun u : GL (Fin n) k => u⁻¹) (𝓝 1) (𝓝 1) := by
      simpa using (continuous_inv.tendsto (1 : GL (Fin n) k))
    exact ht.eventually h1
  filter_upwards [h1, h3] with u hu1 hu2 X
  by_cases hX : X ∈ tsupport Ψ
  · exact hu1 X hX
  by_cases hX' : u.val * X ∈ tsupport Ψ
  · have := hu2 _ hX'
    rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hX, image_eq_zero_of_notMem_tsupport hX']

theorem mem_augRk_of_smallF_eq_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (n d : ℕ) (ν : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν →
    ∀ (S : Set (Matrix (Fin n) (Fin d) k)),
    (∀ (E : GL (Fin n) k), ∀ Y ∈ S, E.val * Y ∈ S → E ∈ GlobalTheory.SplitWeil.KO k (Fin n)) →
    (∀ E ∈ GlobalTheory.SplitWeil.KO k (Fin n), ∀ Y ∈ S, E.val * Y ∈ S) →
    ∀ Φ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, (∀ Y, Y ∉ S → Φ Y = 0) →
    (∀ Y ∈ S, smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Φ Y = 0) → Φ ∈ GlobalTheory.FullRankCoinv.augRk n d ν := by
  intro k _ _ _ _ _ _ n d ν hν S hrig hst Φ hΦ hsupp h0
  have : BorelSpace (GL (Fin n) k) := borel_GL
  set K := GlobalTheory.SplitWeil.KO k (Fin n) with hK
  have hKo : IsOpen (K : Set (GL (Fin n) k)) := isOpen_KO
  have hKm : MeasurableSet (K : Set (GL (Fin n) k)) := hKo.measurableSet
  have hK1 : haarVol K K = 1 := haarVol_self isOpen_KO le_rfl
  let F : GL (Fin n) k → Matrix (Fin n) (Fin d) k → ℂ :=
    fun g Y => Φ (g.val * Y) * (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card (Fin d) : ℂ) / 2)
  have hFl : ∀ g, F g = lact ν (invT g)⁻¹ Φ := fun g => by
    funext Y
    have e1 : gdet (invT g)⁻¹ = gdet g := by
      rw [show gdet (invT g)⁻¹ = (gdet (invT g))⁻¹ from map_inv _ _, gdet_invT, inv_inv]
    simp only [F, lact, e1, invT_inv_val, Matrix.transpose_transpose, Fintype.card_fin]
    ring
  have hev : ∀ᶠ u in 𝓝 (1 : GL (Fin n) k), ∀ g, F (u * g) = F g := by
    have h2 : ∀ᶠ u in 𝓝 (1 : GL (Fin n) k), ν (gdet u) = 1 := by
      have : IsOpen ((fun u : GL (Fin n) k => Matrix.GeneralLinearGroup.det u) ⁻¹' (ν.ker : Set kˣ)) :=
        IsOpen.preimage Matrix.GeneralLinearGroup.continuous_det hν
      exact this.mem_nhds (by simp)
    filter_upwards [sb_left_invariant Φ hΦ.1, h2, hKo.mem_nhds (one_mem K)] with u h1 h2 h3 g
    funext Y
    simp only [F, gdet_mul, map_mul, h2, apow_mul, apow_of_valuation_eq_one (valuation_gdet_of_mem_KO h3),
      Units.val_mul, Matrix.mul_assoc, h1, one_mul]
  have hlc : IsLocallyConstant F := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
    have ht : Filter.Tendsto (fun y : GL (Fin n) k => y * x⁻¹) (𝓝 x) (𝓝 1) := by
      simpa using ((continuous_mul_const x⁻¹).tendsto x)
    filter_upwards [ht.eventually hev] with y hy
    simpa using hy x
  have hfin : (F '' K).Finite := by
    have : CompactSpace K := isCompact_iff_compactSpace.1 (isCompact_KO (k := k) (n := Fin n))
    have h := (hlc.comp_continuous (continuous_subtype_val (p := fun g => g ∈ K))).range_finite
    refine h.subset ?_
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩
  set μ := (haarVol K).restrict K with hμ
  have hμ1 : μ Set.univ = 1 := by rw [hμ, Measure.restrict_apply_univ, hK1]
  have : IsFiniteMeasure μ := ⟨by rw [hμ1]; exact ENNReal.one_lt_top⟩
  have hI := integral_comp_finite μ F hfin.toFinset
    (by
      filter_upwards [ae_restrict_mem hKm] with g hg
      exact hfin.mem_toFinset.2 ⟨g, hg, rfl⟩)
    (fun v => (hlc.isOpen_fiber v).measurableSet)
  have hs1 : ∑ v ∈ hfin.toFinset, (μ.real (F ⁻¹' {v}) : ℂ) = 1 := by
    have := hI fun _ => 1
    simpa [Measure.real, hμ1] using this.symm
  have hA : ∑ v ∈ hfin.toFinset, (μ.real (F ⁻¹' {v}) : ℂ) • v = 0 := by
    funext Y
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← hI fun v => v Y]
    by_cases hY : Y ∈ S
    · rw [hμ, setIntegral_eq_integral_of_forall_compl_eq_zero]
      · exact h0 Y hY
      · intro g hg
        have : g.val * Y ∉ S := fun h => hg (hrig g Y hY h)
        simp [F, hsupp _ this]
    · refine setIntegral_eq_zero_of_forall_eq_zero fun g hg => ?_
      have : g.val * Y ∉ S := fun h => hY (by
        have := hst g⁻¹ (inv_mem hg) _ h
        rwa [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul] at this)
      simp [F, hsupp _ this]
  have hΦe : Φ = -∑ v ∈ hfin.toFinset, (μ.real (F ⁻¹' {v}) : ℂ) • (v - Φ) := by
    simp only [smul_sub, Finset.sum_sub_distrib, hA, ← Finset.sum_smul, hs1, one_smul, zero_sub, neg_neg]
  rw [hΦe]
  refine neg_mem (Submodule.sum_mem _ fun v hv => Submodule.smul_mem _ _ ?_)
  obtain ⟨g, -, rfl⟩ := hfin.mem_toFinset.1 hv
  exact Submodule.subset_span ⟨(invT g)⁻¹, Φ, hΦ, by rw [hFl]⟩

end GlobalTheory.FullRankCoinv.Average
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC

namespace FactorExt

theorem intCast_surj (Q : ℕ) : Function.Surjective (Int.cast : ℤ → ULift.{1} (ZMod Q)) := by
  intro r
  obtain ⟨z, hz⟩ := ZMod.intCast_surjective r.down
  exact ⟨z, ULift.ext (by simp [hz])⟩

theorem map_smul_of_add {A B M N : Type*} [Ring A] [Ring B] (f : A →+* B)
    (hA : Function.Surjective (Int.cast : ℤ → A)) [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N]
    (g : M →+ N) (r : A) (m : M) : g (r • m) = f r • g m := by
  obtain ⟨z, rfl⟩ := hA r
  rw [Int.cast_smul_eq_zsmul, map_zsmul, map_intCast, Int.cast_smul_eq_zsmul]

variable {R S : Type} [CommRing R] [CommRing S]

theorem extSh_hom_ext (φ : R →+* S) {F : Shv R} {G : Shv S} (f g : (extSh φ).obj F ⟶ G)
    (h : ∀ (U : Scheme.{0}) (a : Sec F U), Sec.map f (extSh.sec φ F U a) = Sec.map g (extSh.sec φ F U a)) : f = g := by
  apply Sheaf.hom_ext
  refine sheafify_hom_ext (J := Scheme.etaleTopology) (P := F.obj ⋙ ModuleCat.extendScalars.{1, 1, 1} (uliftHom φ))
    f.hom g.hom G.property ?_
  ext U : 2
  apply (ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} (uliftHom φ)).homEquiv _ _ |>.injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  ext a
  exact h (unop U) a

end FactorExt

end GlobalTheory.EtC

end

noncomputable section

namespace GlobalTheory.EtC

namespace FactorExt

variable {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)
  (hR : Function.Surjective (Int.cast : ℤ → ULift.{1} R)) {I : Cx R} {K : Cx S} (ρ : SemiMap I K)
include hR

def lin (s : ℤ) (U : Scheme.{0}) :
    (I.X s).obj.obj (op U) ⟶ (ModuleCat.restrictScalars (uliftHom φ)).obj ((K.X s).obj.obj (op U)) :=
  ModuleCat.ofHom (X := (I.X s).obj.obj (op U))
    (Y := (ModuleCat.restrictScalars (uliftHom φ)).obj ((K.X s).obj.obj (op U)))
    { toFun := ρ.app U s
      map_add' := map_add _
      map_smul' := fun r a => by
        exact map_smul_of_add (uliftHom φ) hR (ρ.app U s) r a }

def pre (s : ℤ) : (I.X s).obj ⋙ ModuleCat.extendScalars.{1, 1, 1} (uliftHom φ) ⟶ (K.X s).obj where
  app U := ((ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} (uliftHom φ)).homEquiv _ _).symm (lin φ hR ρ s (unop U))
  naturality {U V} g := by
    rw [Functor.comp_map, ← Adjunction.homEquiv_naturality_left_symm, ← Adjunction.homEquiv_naturality_right_symm]
    congr 1
    ext a
    exact (ρ.nat g.unop s a).symm

def term (s : ℤ) : (extCx φ I).X s ⟶ K.X s :=
  ((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} S))).homEquiv _ _).symm (pre φ hR ρ s)

theorem term_sec (s : ℤ) (U : Scheme.{0}) (a : Sec (I.X s) U) :
    Sec.map (term φ hR ρ s) (extSh.sec φ (I.X s) U a) = ρ.app U s a := by
  have h1 : toSheafify Scheme.etaleTopology.{0} ((I.X s).obj ⋙ ModuleCat.extendScalars.{1, 1, 1} (uliftHom φ)) ≫
      (term φ hR ρ s).hom = pre φ hR ρ s := by
    have := Adjunction.homEquiv_unit (sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} S)))
      _ _ (term φ hR ρ s)
    rw [sheafificationAdjunction_unit_app] at this
    exact this.symm.trans (Equiv.apply_symm_apply _ _)
  have h2 := Adjunction.homEquiv_unit (ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} (uliftHom φ)) _ _
    ((pre φ hR ρ s).app (op U))
  have e1 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (NatTrans.congr_app h1 (op U)))
    (((ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} (uliftHom φ)).unit.app ((I.X s).obj.obj (op U))).hom a)
  have e2 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h2) a
  simp only [pre, Equiv.apply_symm_apply] at e2
  exact e1.trans e2.symm

def hom : extCx φ I ⟶ K where
  f s := term φ hR ρ s
  comm' s t _ := by
    apply FactorExt.extSh_hom_ext φ
    intro U a
    show Sec.map (K.d s t) (Sec.map (term φ hR ρ s) (extSh.sec φ (I.X s) U a)) =
      Sec.map (term φ hR ρ t) (Sec.map ((extSh φ).map (I.d s t)) (extSh.sec φ (I.X s) U a))
    rw [term_sec, extSh.sec_map, term_sec, ρ.comm]

end FactorExt

theorem SemiMap.factor_extCx : ∀ (Q q : ℕ) (hq : q ∣ Q) (I : Cx (ZMod Q)) (K : Cx (ZMod q)) (ρ : SemiMap I K),
    ∃ u : extCx (ZMod.castHom hq (ZMod q)) I ⟶ K, ∀ (U : Scheme.{0}) (s : ℤ) (a : Sec (I.X s) U),
      ρ.app U s a = Sec.map (u.f s) ((extπ (ZMod.castHom hq (ZMod q)) I).app U s a) :=
  fun Q _ hq _ _ ρ => ⟨FactorExt.hom _ (FactorExt.intCast_surj Q) ρ,
    fun U s a => (FactorExt.term_sec (ZMod.castHom hq _) (FactorExt.intCast_surj Q) ρ s U a).symm⟩

end GlobalTheory.EtC

end
end

section

open IsLocalRing Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.KeyOriginEnlarge

theorem etale_of_isZTorsor (B D : Type) [CommRing B] [IsNoetherianRing B] [CommRing D] [Algebra B D]
    (q : ℕ) (hq : 0 < q) (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D))
    (h : GlobalTheory.KeyOriginCut.IsZTorsor B D q act) : Algebra.Etale B D := by
  haveI := GlobalTheory.TorsorFieldPoint.formallyUnramified_of_isZTorsor B D q hq act h
  obtain ⟨hfin, hproj, _, _⟩ := h
  haveI := hfin
  haveI := hproj
  haveI : Algebra.FinitePresentation B D :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact Algebra.Etale.of_formallyUnramified_of_flat

theorem exists_ne_zero_closureEtaleAt : ∀ (q : ℕ) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [Algebra.EssFiniteType ℤ A]
    (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
    [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
    (QA : Ideal EA) [QA.IsPrime]
    (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
    (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    0 < q → IsUnit (q : A) →
    GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA →
    ∃ a : A, a ≠ 0 ∧ ∀ (P : Ideal (Localization.AtPrime QA)) [P.IsPrime],
      algebraMap A (Localization.AtPrime QA) a ∉ P →
      GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A (Localization.AtPrime QA) DA P := by
  intro q A _ _ _ _ _ _ EA _ _ _ _ _ QA _ DA _ _ actA hq _ htor
  haveI : IsNoetherianRing EA := Algebra.FiniteType.isNoetherianRing (Polynomial A) EA
  obtain ⟨_, _⟩ := GlobalTheory.etale_localization_atPrime_isDomain_isIntegrallyClosed (Polynomial A) EA QA
  set R := Localization.AtPrime QA
  haveI : Module.Finite (GlobalTheory.LocAcyc.GenFib A R) DA := htor.1
  haveI := etale_of_isZTorsor _ DA q hq actA htor
  letI := GlobalTheory.KeyOriginNoeth.closureAlg A R DA
  haveI : Module.Finite R (GlobalTheory.KeyOriginNoeth.closure A R DA) := GlobalTheory.T.finite_integralClosureOverGenericFibre_of_etale A R DA
  haveI : Algebra.FinitePresentation R (GlobalTheory.KeyOriginNoeth.closure A R DA) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨m, hm, hE⟩ := GlobalTheory.T.exists_etale_away_of_isEtaleAt R (GlobalTheory.KeyOriginNoeth.closure A R DA)
    (Algebra.algebraMapSubmonoid R (nonZeroDivisors A)) (fun Q _ hQ =>
      GlobalTheory.T.closure_prime_regular_height A R DA Q (fun a ha => hQ _ ⟨a, mem_nonZeroDivisors_of_ne_zero ha, rfl⟩))
  obtain ⟨a, ha, rfl⟩ := hm
  refine ⟨a, nonZeroDivisors.ne_zero ha, fun P _ hP => ?_⟩
  exact GlobalTheory.T.etale_localization_atPrime_tensor_of_etale_away' R _ _ hE P hP

end GlobalTheory.KeyOriginEnlarge
end
end

section

open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal

theorem _root_.GlobalTheory.T.matrixGroup_chart_density_at_identity : ∀ (ι : Type) [Fintype ι] (r : ℕ) (H : Subgroup (ι → GL (Fin r) ℂ)) [MeasurableSpace H] (μ : Measure H) (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W] (lam : Measure W) [lam.IsAddHaarMeasure] (Q : W → H) (D : W →L[ℝ] (ι → Fin r → Fin r → ℂ)) (h : W → ℝ≥0∞) (a : ℝ≥0∞) (ρ : ℝ), HasStrictFDerivAt (fun w => fun τ i j => ((((Q w : H) : ι → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) i j) D 0 → Q 0 = 1 → Function.Injective D → (∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ grpBall H ε, ∃ w : W, ‖w‖ < δ ∧ Q w = g) → Tendsto h (𝓝 0) (𝓝 a) → a ≠ 0 → a ≠ ⊤ → 0 < ρ → (∀ A : Set W, MeasurableSet A → A ⊆ Metric.ball 0 ρ → μ (Q '' A) = ∫⁻ w in A, h w ∂lam) → Tendsto (fun ε : ℝ => μ (grpBall H ε) / (lam.map D) (tanBall ι r ε)) (𝓝[>] 0) (𝓝 a) := by
  first | exact @GlobalTheory.SUVol.DensChart.density_at_one | exact GlobalTheory.SUVol.DensChart.density_at_one | (intros; apply GlobalTheory.SUVol.DensChart.density_at_one <;> assumption)
end
