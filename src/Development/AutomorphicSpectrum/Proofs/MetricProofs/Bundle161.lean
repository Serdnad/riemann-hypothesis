module

import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle159
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle154
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle121
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle152
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.TiedSettingSymmetricCharts
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle005
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticLiftToLogResolution
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle117
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle157
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle089
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapPullbackThird
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle103
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Weights
public import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.XAnConj
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle158
import GroundTheory.HeightsAndTheta.Heights.Intersections.PFibreLocal
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogPeriodStatement
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PConsequences
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle101
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle090
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio

@[expose] public section

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap

section Orbit

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem mCoordIdeal_le_of_sameOrbit {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    mCoordIdeal z' ≤ mCoordIdeal z := by
  apply GlobalTheory.CompanionTheory.Ar.PB.CovMap.ImgBase.mCoordIdeal_le <;> assumption

theorem mCoordIdeal_eq_of_sameOrbit {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    mCoordIdeal z = mCoordIdeal z' :=
  le_antisymm (mCoordIdeal_le_of_sameOrbit (Cj.sameOrbit_symm h)) (mCoordIdeal_le_of_sameOrbit h)

theorem coord_ne_of_X_notMem {z : (Σ k, ι k) → ℂ} {q : Σ k, ι k} (h : (X q : MRing ι) ∉ mCoordIdeal z) :
    z q ≠ 0 := fun e => h (by
  show mConeMap z (X q) = 0
  rw [mConeMap, aeval_X, e, map_zero, zero_mul])

end Orbit

section Proj

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {K' : Type} [Fintype K']
  {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Ω Ω' : Type} [Field Ω] [Field Ω']

theorem comp_mem_mcPts {κ : K → K'} {v : (Σ k, ι k) → (Σ k, ι' k)} (hv : IsBlockMap κ v) (φ : Ω →+* Ω')
    {x : (Σ k, ι k) → Ω} {x' : (Σ k, ι' k) → Ω'} (hx : ∀ q, x' (v q) = φ (x q))
    {zb : (Σ k, ι' k) → ℂ} (hz : zb ∈ mcPts (mCoordIdeal x')) : zb ∘ v ∈ mcPts (mCoordIdeal x) := by
  have key : ∀ f : MRing ι, mConeMap x' (rename v f) = rename κ (map φ (mConeMap x f)) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [mConeMap]
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
    | mul_X p i hp =>
      simp only [map_mul, hp, rename_X]
      congr 1
      simp [mConeMap, hx, hv.2.2.1 i]
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 (κ k)
    obtain ⟨p, hp⟩ := hv.2.2.2 ⟨κ k, i⟩ ⟨k, rfl⟩
    obtain ⟨k₁, i₁⟩ := p
    have e : k₁ = k := hv.1 (by rw [← hv.2.2.1 ⟨k₁, i₁⟩, hp])
    subst e
    exact ⟨i₁, by simpa [Function.comp, hp] using hi⟩
  · have hf' : mConeMap x f = 0 := hf
    have h1 : rename v f ∈ mCoordIdeal x' := by
      show mConeMap x' (rename v f) = 0
      rw [key, hf', map_zero, map_zero]
    have h2 := hz.2 _ h1
    rwa [map_rename, eval_rename] at h2

end Proj

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} {N j : ℕ}

theorem sameOrbit_of_isFlagOf (M : FlagModel y Ψ N j) {F : FrameData ι Ψ N M.Ω M.blk}
    {z z' : (Σ k, ι k) → ℂ} {h : Ψ → Matrix (Fin N) (Fin N) ℂ}
    (hb : SameOrbit (basePart M.blk z) (basePart M.blk z')) (H : M.IsFlagOf F z h) (H' : M.IsFlagOf F z' h) :
    SameOrbit z z' := by
  have hbase : basePart M.blk z = basePart M.blk z' := by
    obtain ⟨c, -, e⟩ := hb
    have hc : ∀ k, c k = 1 := fun k => by
      have := congrFun e ⟨k, F.c k⟩
      rw [H.1 k, H'.1 k, mul_one] at this
      exact this.symm
    rw [e]
    funext p
    simp [hc]
  have blockwise : ∀ k, ∃ t : ℂ, t ≠ 0 ∧ ∀ m : ι k, z ⟨k, m⟩ = t * z' ⟨k, m⟩ := by
    intro k
    by_cases hk : ∀ p, M.blk p ≠ some k
    · exact ⟨1, one_ne_zero, fun m => by
        simpa [basePart] using congrFun hbase ⟨⟨k, hk⟩, m⟩⟩
    · push_neg at hk
      obtain ⟨p, hp⟩ := hk
      obtain ⟨a, ha, ea⟩ := H.2.2 p k hp
      obtain ⟨a', ha', ea'⟩ := H'.2.2 p k hp
      refine ⟨a / a', div_ne_zero ha ha', fun m => ?_⟩
      rw [ea m, ea' m, hbase]
      field_simp
  choose t ht e using blockwise
  exact ⟨t, ht, funext fun p => e p.1 p.2⟩

theorem isImg_unique : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 2) → IsArithVar (mCoordIdeal y') (d + 2) → ∀ z ∈ mcPts (mCoordIdeal y'), ∀ w w', CovMap.IsImg Cv z w → CovMap.IsImg Cv z w' → SameOrbit w w' := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv d _ hA' z hz w w' hw hw'
  obtain ⟨-, fr, -⟩ := GlobalTheory.T.flag_model_base_projection_points K ι Φ y Ψ N j M
  obtain ⟨bs', fr', fl'⟩ := GlobalTheory.T.flag_model_base_projection_points K' ι' Φ' y' Ψ N j M'
  obtain ⟨F', hF', hG'⟩ := fr' _ (bs' z hz)
  have hne : ∀ k : NonPluckerBlocks M'.blk, basePart M'.blk z ⟨k, F'.c k⟩ ≠ 0 := fun k =>
    coord_ne_of_X_notMem (hG'.1 k)
  let c : K' → ℂ := fun k =>
    if h : ∀ p, M'.blk p ≠ some k then (basePart M'.blk z ⟨⟨k, h⟩, F'.c ⟨k, h⟩⟩)⁻¹ else 1
  have hcb : ∀ k : NonPluckerBlocks M'.blk, c k.1 = (basePart M'.blk z ⟨k, F'.c k⟩)⁻¹ := fun k => dif_pos k.2
  have hc : ∀ k, c k ≠ 0 := fun k => by
    by_cases h : ∀ p, M'.blk p ≠ some k
    · rw [hcb ⟨k, h⟩]
      exact inv_ne_zero (hne ⟨k, h⟩)
    · simp only [c, dif_neg h]
      exact one_ne_zero
  let z₁ : (Σ k, ι' k) → ℂ := fun p => c p.1 * z p
  have h1 : SameOrbit z₁ z := ⟨c, hc, rfl⟩
  have hz₁ : z₁ ∈ mcPts (mCoordIdeal y') := mcPts_smul hA'.2.1.2.1 c hc hz
  have hb1 : SameOrbit (basePart M'.blk z₁) (basePart M'.blk z) :=
    ⟨fun k => c k.1, fun k => hc k.1, rfl⟩
  have hG₁ : M'.GoodAt F' (mCoordIdeal (basePart M'.blk z₁)) := by
    rw [mCoordIdeal_eq_of_sameOrbit hb1]
    exact hG'
  have hnorm : ∀ k, basePart M'.blk z₁ ⟨k, F'.c k⟩ = 1 := fun k => by
    show c k.1 * basePart M'.blk z ⟨k, F'.c k⟩ = 1
    rw [hcb k]
    exact inv_mul_cancel₀ (hne k)
  obtain ⟨h, hh⟩ := (fl' F' hF' z₁ (bs' z₁ hz₁) hG₁ hnorm).1 hz₁
  obtain ⟨F, hF, hG⟩ := fr _ (comp_mem_mcPts Cv.block Cv.φ Cv.x_eq (bs' z₁ hz₁))
  obtain ⟨z₀, a, b, e⟩ := hw z₁ h1 F' F hF' hF hG₁ hG h hh
  obtain ⟨z₀', a', b', e'⟩ := hw' z₁ h1 F' F hF' hF hG₁ hG h hh
  exact Cj.sameOrbit_trans (Cj.sameOrbit_symm a) (Cj.sameOrbit_trans
    (sameOrbit_of_isFlagOf M (Cj.sameOrbit_trans b (Cj.sameOrbit_symm b')) e e') a')

end GlobalTheory.CompanionTheory.Ar.PB.CovMap
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.CompanionTheory.Relay.symmetric_charts_of_regularization : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (M : XModel D) (w : ((Σ k, J k) → ℂ) → ℝ) (S' : BoundedRegularisationSetting M D.Xo Hd.aMu w) (κ : Equiv.Perm (Fin S'.B.N)), S'.IsTied → SymmCharts M S'.B.toPotentialCharts κ → (∀ v, S'.ρ.toFun (star v) = S'.ρ.toFun v) → (∀ j, ∀ z ∈ mcPts (mCoordIdeal D.y), S'.η (κ j) (M.proj (conjVec z)) = S'.η j (M.proj z)) → IsConjInvariantH S'.ref → (∀ z ∈ mcPts (mCoordIdeal D.y), S'.B.ph (M.proj (conjVec z)) = S'.B.ph (M.proj z)) → ConjU S' := by
  first | exact @LevelTowerAlt.tied_setting_symmetric_charts | exact LevelTowerAlt.tied_setting_symmetric_charts
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem thmA_swap : Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N d : ℕ) (S : AnSys (d + 1) (Ψ × Fin N)) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (Re : Realis S P) (τ : Ψ) (a b : Fin N), (b : ℕ) = a + 1 → SqSys Re (τ, a) (xiCoef τ a) → ∀ lam : Ψ × Fin N → ℝ, eval lam (toWt (Re.PB II)) + eval (lam ∘ Equiv.swap (τ, a) (τ, b)) (toWt (Re.PB II)) = (tsgPoly (d + 1) kappa (linePoly (fun p => gap lam p + gap lam (τ, a) / 2 * (xiCoef τ a p : ℝ)) (xiCoef τ a) S.degPoly)).eval (gap lam (τ, a)) := by
  intro hI II hII Ψ _ _ N d S K _ ι _ P Re τ a b hb Q lam
  obtain ⟨h0, h1, h2⟩ := gap_swap_decomp Ψ N τ a b hb lam
  have key := GlobalTheory.T.height_polynomial_reflection_sum hI GroundTheory.Heights₂.Heights.Inter.FibreLocal.proof II hII K ι d (Ψ × Fin N) S P Re (τ, a) (xiCoef τ a) Q
    (fun p => gap lam p + gap lam (τ, a) / 2 * (xiCoef τ a p : ℝ)) h0 (gap lam (τ, a))
  rw [eval_toWt_gap, eval_toWt_gap, ← key]
  exact congrArg₂ (· + ·) (congrArg (fun f => eval f (Re.PB II)) (_root_.funext h1))
    (congrArg (fun f => eval f (Re.PB II)) (_root_.funext h2))

end GlobalTheory.CompanionTheory.Ar.PB
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem analyticAt_comp_of_holoOn {D e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas D X) {V : Set (Fin e → ℂ)}
    {Y : Set X} {g : X → ℂ} (hg : A.HoloOn Y g) {h : (Fin e → ℂ) → X} {z : Fin e → ℂ}
    (hV : V ∈ 𝓝 z) (hc : ContinuousOn h V)
    (ha : ∀ k, AnalyticOnNhd ℂ (A.chart k ∘ h) (V ∩ h ⁻¹' (A.chart k).source)) (hz : h z ∈ Y) :
    AnalyticAt ℂ (g ∘ h) z := by
  obtain ⟨k, hk⟩ := A.cover (h z)
  have hcz : ContinuousAt h z := hc.continuousAt hV
  have h1 : AnalyticAt ℂ (A.chart k ∘ h) z := ha k z ⟨mem_of_mem_nhds hV, hk⟩
  have h2 : AnalyticAt ℂ (g ∘ (A.chart k).symm) ((A.chart k ∘ h) z) := by
    refine hg k _ ⟨(A.chart k).map_source hk, ?_⟩
    simpa [Set.mem_preimage, (A.chart k).left_inv hk] using hz
  have h3 : AnalyticAt ℂ ((g ∘ (A.chart k).symm) ∘ (A.chart k ∘ h)) z := h2.comp h1
  refine h3.congr ?_
  filter_upwards [hcz.preimage_mem_nhds ((A.chart k).open_source.mem_nhds hk)] with u hu
  simp [(A.chart k).left_inv hu]

theorem ref_pot_along_exact_family : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (D : ℕ) (σ : Type) (S : AnSys D σ) (P : Ideal (MRing ι)) (Re : Realis S P) (a : σ) (e : ℕ) (V : Set (Fin e → ℂ)) (ΦY : (Fin e → ℂ) → S.X) (zex : (Fin e → ℂ) → (Σ k, ι k) → ℂ) (z : Fin e → ℂ), Re.J = ⊤ → Re.deg = 1 → Re.br = ∅ → IsOpen V → z ∈ V → (∀ q, AnalyticOnNhd ℂ (fun u => zex u q) V) → (∀ u ∈ V, zex u ∈ mcPts P) → (∀ u ∈ V, ∀ x₀, Re.π x₀ = ΦY u → SameOrbit (Re.R.lift x₀ x₀) (zex u)) → ∃ Hh : (Fin e → ℂ) → ℂ, AnalyticAt ℂ Hh z ∧ ∀ᶠ z' in 𝓝 z, (S.th a).φ (ΦY z) (ΦY z') = Real.log ((Re.ref a).h (zex z')) + (Hh z').re := by
  intro K _ ι _ D σ S P Re a e V ΦY zex z hJ hdeg hbr hV hzV hana hmc hex
  have hbij : Function.Bijective Re.π := realis_bijective_of_degree_one K ι D σ S P Re hdeg hbr
  set h : (Fin e → ℂ) → Re.R.X := fun u => Function.surjInv hbij.2 (ΦY u) with hdef
  have hπ : ∀ u, Re.π (h u) = ΦY u := fun u => Function.surjInv_eq hbij.2 (ΦY u)
  have hSO : ∀ u ∈ V, SameOrbit (Re.R.lift (h u) (h u)) (zex u) := fun u hu => hex u hu (h u) (hπ u)
  obtain ⟨hc, hch⟩ := holo_of_lift_orbit_top K ι P Re.J D e Re.R V zex h hJ hV hana hmc hSO
  have hVn : V ∈ 𝓝 z := hV.mem_nhds hzV
  have hcz : ContinuousAt h z := hc.continuousAt hVn
  obtain ⟨W, hW, hxW, G, hG, hGeq⟩ := Re.ref_pot a (h z) (Set.mem_univ _)
  have hGh : AnalyticAt ℂ (G ∘ h) z := analyticAt_comp_of_holoOn Re.R.A hG hVn hc hch hxW
  have hxU : h z ∈ Re.R.U (h z) := Re.R.mem_U _

  have hi : ∀ k, ∃ i, zex z ⟨k, i⟩ ≠ 0 := (hmc z hzV).1
  choose i hi using hi
  set c : K → (Fin e → ℂ) → ℂ := fun k u => Re.R.lift (h z) (h u) ⟨k, i k⟩ / zex u ⟨k, i k⟩ with hcdef
  have hcan : ∀ k, AnalyticAt ℂ (c k) z := fun k =>
    AnalyticAt.div (analyticAt_comp_of_holoOn Re.R.A (Re.R.holo (h z) ⟨k, i k⟩) hVn hc hch hxU)
      (hana _ z hzV) (hi k)
  have hcz0 : ∀ k, c k z ≠ 0 := by
    intro k
    obtain ⟨d, hd, hdz⟩ := hSO z hzV
    have : Re.R.lift (h z) (h z) ⟨k, i k⟩ = d k * zex z ⟨k, i k⟩ := congrFun hdz ⟨k, i k⟩
    simp only [hcdef, this]
    exact div_ne_zero (mul_ne_zero (hd k) (hi k)) (hi k)
  have hL : ∀ k, ∃ Lk : (Fin e → ℂ) → ℂ, AnalyticAt ℂ Lk z ∧ ∀ᶠ z' in 𝓝 z, Real.log ‖c k z'‖ = (Lk z').re :=
    fun k => log_norm_eventually_eq_re_analyticAt e (c k) z (hcan k) (hcz0 k)
  choose L hLan hLeq using hL
  refine ⟨fun u => (∑ k, (((Re.ref a).a k : ℤ) : ℂ) * L k u) - G (h u), ?_, ?_⟩
  · refine AnalyticAt.sub ?_ hGh
    exact Finset.analyticAt_fun_sum _ fun k _ => analyticAt_const.mul (hLan k)
  · have hne : ∀ᶠ u in 𝓝 z, ∀ k, zex u ⟨k, i k⟩ ≠ 0 :=
      eventually_all.2 fun k => (hana _ z hzV).continuousAt.eventually_ne (hi k)
    filter_upwards [hVn, hne, eventually_all.2 hLeq, hcz.preimage_mem_nhds (hW.mem_nhds hxW),
      hcz.preimage_mem_nhds ((Re.R.isOpen_U (h z)).mem_nhds hxU)] with u huV hune huL huW huU
    have hcompat := Re.R.compat (h z) (h u) (h u) ⟨huU, Re.R.mem_U _⟩
    obtain ⟨d₁, hd₁, e₁⟩ := hcompat
    obtain ⟨d₂, hd₂, e₂⟩ := hSO u huV
    have hlift : Re.R.lift (h z) (h u) = fun p => (d₁ p.1 * d₂ p.1) * zex u p := by
      funext p
      rw [congrFun e₁ p, congrFun e₂ p, mul_assoc]
    have hck : ∀ k, c k u = d₁ k * d₂ k := by
      intro k
      simp only [hcdef, hlift]
      field_simp [hune k]
    have hlift' : Re.R.lift (h z) (h u) = fun p => c p.1 u * zex u p := by
      rw [hlift]; funext p; rw [hck]
    have hcne : ∀ k, c k u ≠ 0 := fun k => by
      rw [hck]; exact mul_ne_zero (hd₁ k) (hd₂ k)
    have hsm := (Re.ref a).smul (fun k => c k u) (zex u) hcne
    have hpos := (Re.ref a).pos (zex u) (hmc u huV).1
    have hlog : Real.log ((Re.ref a).h (Re.R.lift (h z) (h u))) =
        (∑ k, ((Re.ref a).a k : ℝ) * Real.log ‖c k u‖) + Real.log ((Re.ref a).h (zex u)) := by
      rw [hlift', hsm, Real.log_mul (Finset.prod_ne_zero_iff.2 fun k _ =>
        zpow_ne_zero _ (norm_ne_zero_iff.2 (hcne k))) hpos.ne', Real.log_prod]
      · simp only [Real.log_zpow]
      · exact fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hcne k))
    have hG' : Real.log ((Re.ref a).h (Re.R.lift (h z) (h u))) - (S.th a).φ (ΦY z) (ΦY u) = (G (h u)).re := by
      have := hGeq (h u) huW
      simpa only [potOf, LocPot.pullback, hπ] using this
    have hre : ((∑ k, (((Re.ref a).a k : ℤ) : ℂ) * L k u) - G (h u)).re =
        (∑ k, ((Re.ref a).a k : ℝ) * Real.log ‖c k u‖) - (G (h u)).re := by
      rw [Complex.sub_re, Complex.re_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [huL k]
      simp
    rw [hre]
    linarith

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem _root_.GlobalTheory.T.realisation_bijective_degree_one : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (D : ℕ) (σ : Type) (S : AnSys D σ) (P : Ideal (MRing ι)) (Re : Realis S P), Re.deg = 1 → Re.br = ∅ → Function.Bijective Re.π := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.realis_bijective_of_degree_one | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.realis_bijective_of_degree_one | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.realis_bijective_of_degree_one <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical


theorem _root_.GlobalTheory.T.flag_gap_pullback_third : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X), IsStepHyp M BM p κ v R pr → HasStepCharts M BM p κ v R pr := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.StepW.ChartEx.hasStepCharts | exact GlobalTheory.CompanionTheory.Ar.PB.StepW.ChartEx.hasStepCharts | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.StepW.ChartEx.hasStepCharts <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.WMan

theorem sameOrbit_sqZ_of_flags : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (zb₂ : (Σ k, baseIdx ι M.blk k) → ℂ) (z : (Σ o : Option K, ι (o.getD k₀)) → ℂ) (H U : Ψ → Matrix (Fin N) (Fin N) ℂ) (V : Matrix (Fin N) (Fin N) ℂ) (t : ℂ), M.blk (τ, a) = some k₀ → baseOf M k₀ z ∈ mcPts (mCoordIdeal M.x) → M.GoodAt F (mCoordIdeal (baseOf M k₀ z)) → SameOrbit zb₂ (baseOf M k₀ z) → (∀ τ', IsBlockDiag j (U τ') ∧ (U τ').BlockTriangular id ∧ ∀ c, U τ' c c ≠ 0) → IsBlockDiag j V → V.BlockTriangular id → (∀ c ∈ stepCols N j a, V c c ≠ 0) → (∀ p k, M.blk p = some k → ∃ α : ℂ, α ≠ 0 ∧ ∀ m : ι k, fstPt k₀ z ⟨k, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) (baseOf M k₀ z) * minorIJ (H p.1 * U p.1) I (stepCols N j p.2)) → (∃ α : ℂ, α ≠ 0 ∧ ∀ m : ι k₀, sndPt k₀ z ⟨k₀, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k₀, m⟩ I) (baseOf M k₀ z) * minorIJ (H τ * (1 + Matrix.single cb ca t) * V) I (stepCols N j a)) → SameOrbit (sqZ M F zb₂ H k₀ τ ca cb t) z := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M τ a k₀ ca cb F zb₂ z H U V t hτ hz hG ho hU hV hVt hVd h1 h2
  have hval : ∀ s, valAt M.x s zb₂ = valAt M.x s (baseOf M k₀ z) := fun s =>
    CovMap.LocImg.valAt_orbit ho hz s
  have block : ∀ o : Option K, ∃ c : ℂ, c ≠ 0 ∧ ∀ m : ι (o.getD k₀),
      sqZ M F zb₂ H k₀ τ ca cb t ⟨o, m⟩ = c * z ⟨o, m⟩ := by
    rintro (_ | k)
    · have e : ∃ p, M.blk p = some k₀ := ⟨_, hτ⟩
      have hc : e.choose = (τ, a) := M.blk_inj _ _ k₀ e.choose_spec hτ
      obtain ⟨α, hα, hm⟩ := (WSq.Pts.step_mul_right M.j_le a hV hVt hVd
        (fun m : ι k₀ => sndPt k₀ z ⟨k₀, m⟩)
        (fun m I => valAt M.x (F.u ⟨k₀, m⟩ I) (baseOf M k₀ z))).1 h2
      refine ⟨α⁻¹, inv_ne_zero hα, fun m => ?_⟩
      have hs : sqZ M F zb₂ H k₀ τ ca cb t ⟨none, m⟩ =
          ∑ I, valAt M.x (F.u ⟨k₀, m⟩ I) (baseOf M k₀ z) *
            minorIJ (H τ * (1 + Matrix.single cb ca t)) I (stepCols N j a) := by
        show flagZ M F zb₂ (Function.update H τ (H τ * (1 + Matrix.single cb ca t))) ⟨k₀, m⟩ = _
        refine (dif_pos e).trans ?_
        simp only [hc, Function.update_self, hval]
      have hn : z ⟨none, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k₀, m⟩ I) (baseOf M k₀ z) *
          minorIJ (H τ * (1 + Matrix.single cb ca t)) I (stepCols N j a) :=
        (WSq.Pts.snd_self z m).symm.trans (hm m)
      rw [hs, hn, inv_mul_cancel_left₀ hα]
    · by_cases e : ∃ p, M.blk p = some k
      · obtain ⟨α, hα, hm⟩ := (WSq.Pts.step_mul_right M.j_le e.choose.2 (hU e.choose.1).1 (hU e.choose.1).2.1
          (fun c _ => (hU e.choose.1).2.2 c) (fun m : ι k => fstPt k₀ z ⟨k, m⟩)
          (fun m I => valAt M.x (F.u ⟨k, m⟩ I) (baseOf M k₀ z))).1 (h1 e.choose k e.choose_spec)
        refine ⟨α⁻¹, inv_ne_zero hα, fun m => ?_⟩
        have hs : sqZ M F zb₂ H k₀ τ ca cb t ⟨some k, m⟩ =
            ∑ I, valAt M.x (F.u ⟨k, m⟩ I) (baseOf M k₀ z) *
              minorIJ (H e.choose.1) I (stepCols N j e.choose.2) := by
          show flagZ M F zb₂ H ⟨k, m⟩ = _
          refine (dif_pos e).trans ?_
          simp only [hval]
        have hn : z ⟨some k, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) (baseOf M k₀ z) *
            minorIJ (H e.choose.1) I (stepCols N j e.choose.2) := hm m
        rw [hs, hn, inv_mul_cancel_left₀ hα]
      · obtain ⟨c, hc, hcz⟩ := ho
        have hk : ∀ p, M.blk p ≠ some k := fun p hp => e ⟨p, hp⟩
        refine ⟨c ⟨k, hk⟩, hc _, fun m => ?_⟩
        show flagZ M F zb₂ H ⟨k, m⟩ = _
        refine (dif_neg e).trans ?_
        rw [hcz]
        rfl
  choose c hc hcz using block
  exact ⟨c, hc, funext fun p => hcz p.1 p.2⟩

end GlobalTheory.CompanionTheory.Ar.PB.WMan
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

theorem _root_.GlobalTheory.T.flag_cover_arithmetic_first : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 2) → IsArithVar (mCoordIdeal y') (d + 2) → ∀ z ∈ mcPts (mCoordIdeal y'), ∃ (V : Set ((Σ k, ι' k) → ℂ)) (f : ((Σ k, ι' k) → ℂ) → (Σ k, ι k) → ℂ), IsOpen V ∧ z ∈ V ∧ AnalyticOnNhd ℂ f V ∧ ∀ z' ∈ V ∩ mcPts (mCoordIdeal y'), f z' ∈ mcPts (mCoordIdeal y) ∧ CovMap.IsImg Cv z' (f z') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.local_img | exact GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.local_img | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.local_img <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.T.posU_of_full_intersection_system : PB.Inputs → ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (M : XModel D) (w : ((Σ k, J k) → ℂ) → ℝ) (S' : BoundedRegularisationSetting M D.Xo Hd.aMu w), IsFullIntersectionSystem II → S'.IsTied → (∀ B : ℕ, 4 * D.f + 2 ≤ B → NefOnFibres (mCoordIdeal D.y) (muTwDeg Hd B)) → PosU S' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.posU_of_nefOnFibres | exact GlobalTheory.CompanionTheory.Ar.Cusp.posU_of_nefOnFibres | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.posU_of_nefOnFibres <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.T.exists_continuous_metric_ratio : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (M : XModel D) (S : LogLogRegularisationSetting M D.Xo (muLine Hd)) (B : ℕ) (Nb : HermLine J), IsSmoothHerm Nb → Nb.a = muTwDeg Hd B → ∃ κ : M.Xc → ℝ, Continuous κ ∧ ∀ z ∈ mcPts (mCoordIdeal D.y), κ (M.proj z) = Real.log (Nb.h z) - Real.log (S.ref.h z) - ∑ p ∈ D.SB B, Real.log (D.vertFactor p z) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Descent.logDiff_descends | exact GlobalTheory.CompanionTheory.Ar.Cusp.Descent.logDiff_descends | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Descent.logDiff_descends <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem an_conj_symmetrise : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (Θ : LocPot X) (L : LocPot X) (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X), IsPotential A L → IsSection A L s → IsSNC A L s m W → (∀ y, logNormSec L s y ≤ 0) → IsPotential A Θ → IsPosPot A Θ → ∀ (c : X → X), Continuous c → (∀ x, c (c x) = x) → (∀ j k, AnalyticOnNhd ℂ (fun z => star (A.chart k (c ((A.chart j).symm z)))) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (c ⁻¹' (A.chart k).source))) → (∀ y, c y ∈ bdry s ↔ y ∈ bdry s) → (∀ y, rW L s (c y) = rW L s y) → ∀ (th : LocPot X) (ph : X → ℝ) (phT : ℝ → X → ℝ) (C t₀ : ℝ), IsPotential A th → (∀ x, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ G : X → ℂ, A.HoloOn V G ∧ ∀ y ∈ V, th.φ (c x) (c y) - th.φ x y = (G y).re) → (∀ y ∉ bdry s, ph (c y) = ph y) → IsRegFamily A Θ L s th ph phT C t₀ → IsRegFamilyC2 A s ph phT → ∃ C' t₀' : ℝ, IsRegFamily A Θ L s th ph (fun t y => (phT t y + phT t (c y)) / 2) C' t₀' ∧ IsRegFamilyC2 A s ph fun t y => (phT t y + phT t (c y)) / 2 :=
  @PositivityTheory.Xgp.t_an_conj

end GlobalTheory.CompanionTheory.Ar.PB
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem ratR_of_resK :
    ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ReciprocityTheory.ChartRestriction.G.AI.I2.RatRStatement :=
  fun h => GroundTheory.Heights₂.Heights.Inter.RatR.proof (ptsIntegrable_of_resK h)

end GlobalTheory.CompanionTheory.Ar.Giv
end
