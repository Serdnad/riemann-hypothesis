module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ChartMeasApplyOfSubset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle598
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2287
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle533
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2297
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2288
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2289
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle027
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.Mean4 GlobalTheory.Mean4O
open MeasureTheory GlobalTheory.ChartGlue

namespace GlobalTheory.GlueCoverNull

open Set Topology ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.GlueCover
open scoped ENNReal

variable {n : ℕ}

theorem glueMeas_null {X ι : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (e : ι → OpenPartialHomeomorph X (V n)) (ρ : ι → X → ℝ≥0∞)
    {F : Set X} (hF : MeasurableSet F) (h0 : ∀ i, volume ((e i) '' ((e i).source ∩ F)) = 0) :
    glueMeas e ρ F = 0 := by
  have hc : ∀ i, chartMeas (e i) (ρ i) F = 0 := fun i => by
    rw [chartMeas_apply (e i) (ρ i) hF]
    exact setLIntegral_measure_zero _ _ (h0 i)
  have hle : glueMeas e ρ ≤ (glueMeas e ρ).restrict Fᶜ := by
    refine iSup_le fun i => Measure.le_iff.2 fun B hB => ?_
    rw [Measure.restrict_apply hB]
    calc chartMeas (e i) (ρ i) B ≤ chartMeas (e i) (ρ i) (B ∩ Fᶜ ∪ F) :=
          measure_mono fun y hy => by
            by_cases h : y ∈ F
            · exact Or.inr h
            · exact Or.inl ⟨hy, h⟩
      _ ≤ chartMeas (e i) (ρ i) (B ∩ Fᶜ) + chartMeas (e i) (ρ i) F := measure_union_le _ _
      _ = chartMeas (e i) (ρ i) (B ∩ Fᶜ) := by rw [hc i, add_zero]
      _ ≤ glueMeas e ρ (B ∩ Fᶜ) :=
          Measure.le_iff'.1 (le_iSup (fun i => chartMeas (e i) (ρ i)) i) _
  have h := Measure.le_iff'.1 hle F
  rw [Measure.restrict_apply hF, inter_compl_self, measure_empty] at h
  exact nonpos_iff_eq_zero.1 h

section Cover

variable {A B ι κ : Type} [TopologicalSpace A] [TopologicalSpace B] [T2Space A] [T2Space B]
  [SecondCountableTopology A] [SecondCountableTopology B] [MeasurableSpace A] [BorelSpace A]
  [MeasurableSpace B] [BorelSpace B]
  {e : ι → OpenPartialHomeomorph A (V n)} {ρ : ι → A → ℝ≥0∞}
  {e' : κ → OpenPartialHomeomorph B (V n)} {ρ' : κ → B → ℝ≥0∞} {m : B → A}

theorem exists_evenly_covered_closed
    (hd : ∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) (ovl e i j))
    (hρ : ∀ i j y, y ∈ (e i).source → y ∈ (e j).source →
      ρ i y = ENNReal.ofReal (‖transDet (e i) (e j) y‖ ^ 2) * ρ j y)
    (hd' : ∀ i j, DifferentiableOn ℂ (e' j ∘ (e' i).symm) (ovl e' i j))
    (hρ' : ∀ i j y, y ∈ (e' i).source → y ∈ (e' j).source →
      ρ' i y = ENNReal.ofReal (‖transDet (e' i) (e' j) y‖ ^ 2) * ρ' j y)
    (hm : Continuous m) {T : Set A} (hT : IsClosed T) {d : ℕ}
    (hfib : ∀ x ∉ T, (m ⁻¹' {x}).encard = d)
    (hch : ∀ z, m z ∉ T → ∃ i j, z ∈ (e' j).source ∧ m z ∈ (e i).source ∧ ∀ w ∈ (e' j).source,
      m w ∈ (e i).source → e' j w = e i (m w) ∧ ρ' j w = ρ i (m w))
    {x : A} (hx : x ∉ T) :
    ∃ W : Set A, IsOpen W ∧ x ∈ W ∧ ∀ Q : Set A, MeasurableSet Q → Q ⊆ W →
      glueMeas e' ρ' (m ⁻¹' Q) = d * glueMeas e ρ Q := by
  classical
  have hfin : ∀ y ∉ T, (m ⁻¹' {y}).Finite := fun y hy => finite_of_encard_eq_coe (hfib y hy)
  have hcard : ∀ y (hy : y ∉ T), (hfin y hy).toFinset.card = d := fun y hy => by
    have h := hfib y hy
    rw [← (hfin y hy).coe_toFinset, encard_coe_eq_coe_finsetCard] at h
    exact_mod_cast h
  obtain ⟨U, hU, hUd⟩ := (hfin x hx).t2_separation
  have hFc := hcard x hx
  have hFm : ∀ z, z ∈ (hfin x hx).toFinset ↔ m z = x := fun z => by simp
  generalize (hfin x hx).toFinset = F at hFc hFm
  have hzF : ∀ z ∈ F, m z = x := fun z hz => (hFm z).1 hz
  have hzT : ∀ z ∈ F, m z ∉ T := fun z hz => by rwa [hzF z hz]
  have hsheet : ∀ z, z ∈ F → ∃ M : Set B, M ⊆ U z ∧ IsOpen M ∧ z ∈ M ∧ IsOpen (m '' M) ∧
      ∀ Q : Set A, MeasurableSet Q → Q ⊆ m '' M →
        glueMeas e' ρ' (M ∩ m ⁻¹' Q) = glueMeas e ρ Q := fun z hz =>
    exists_sheet hd hρ hd' hρ' hm (hch z (hzT z hz)) (hU z).2 (hU z).1
  choose! M hMU hMo hzM hMi hMQ using hsheet
  refine ⟨(⋂ z ∈ F, m '' M z) ∩ Tᶜ, (isOpen_biInter_finset hMi).inter hT.isOpen_compl,
    ⟨mem_iInter₂.2 fun z hz => ⟨z, hzM z hz, hzF z hz⟩, hx⟩, fun Q hQ hQW => ?_⟩
  have hdisj : ∀ z₁ ∈ F, ∀ z₂ ∈ F, z₁ ≠ z₂ → Disjoint (M z₁) (M z₂) := fun z₁ h₁ z₂ h₂ hne =>
    Disjoint.mono (hMU z₁ h₁) (hMU z₂ h₂) (hUd (hzF z₁ h₁) (hzF z₂ h₂) hne)
  have key : m ⁻¹' Q = ⋃ z ∈ F, (M z ∩ m ⁻¹' Q) := by
    ext w
    constructor
    · intro hw
      have hWx := hQW hw
      have hpre : ∀ z ∈ F, ∃ z', z' ∈ M z ∧ m z' = m w := fun z hz => by
        obtain ⟨z', h₁, h₂⟩ := mem_iInter₂.1 hWx.1 z hz
        exact ⟨z', h₁, h₂⟩
      haveI : Nonempty B := ⟨w⟩
      choose! f hfM hfm using hpre
      have hinj : InjOn f F := fun z₁ h₁ z₂ h₂ h12 => by
        by_contra hne
        exact disjoint_left.1 (hdisj z₁ h₁ z₂ h₂ hne) (hfM z₁ h₁) (h12 ▸ hfM z₂ h₂)
      have hsub : F.image f ⊆ (hfin (m w) hWx.2).toFinset := fun v hv => by
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hv
        simpa using hfm z hz
      have heq := Finset.eq_of_subset_of_card_le hsub (by
        rw [Finset.card_image_of_injOn hinj, hcard _ hWx.2, hFc])
      have hwm : w ∈ F.image f := by
        rw [heq]
        simp
      obtain ⟨z, hz, hzw⟩ := Finset.mem_image.1 hwm
      exact mem_iUnion₂.2 ⟨z, hz, hzw ▸ hfM z hz, hw⟩
    · intro hw
      obtain ⟨z, _, _, h⟩ := mem_iUnion₂.1 hw
      exact h
  rw [key, measure_biUnion_finset
    (fun z₁ h₁ z₂ h₂ hne => Disjoint.mono inter_subset_left inter_subset_left
      (hdisj z₁ h₁ z₂ h₂ hne))
    (fun z hz => (hMo z hz).measurableSet.inter (hm.measurable hQ)),
    Finset.sum_congr rfl fun z hz => hMQ z hz Q hQ
      fun y hy => mem_iInter₂.1 (hQW hy).1 z hz,
    Finset.sum_const, nsmul_eq_mul, hFc]

theorem map_glueMeas_closed
    (hd : ∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) (ovl e i j))
    (hρ : ∀ i j y, y ∈ (e i).source → y ∈ (e j).source →
      ρ i y = ENNReal.ofReal (‖transDet (e i) (e j) y‖ ^ 2) * ρ j y)
    (hd' : ∀ i j, DifferentiableOn ℂ (e' j ∘ (e' i).symm) (ovl e' i j))
    (hρ' : ∀ i j y, y ∈ (e' i).source → y ∈ (e' j).source →
      ρ' i y = ENNReal.ofReal (‖transDet (e' i) (e' j) y‖ ^ 2) * ρ' j y)
    (hm : Continuous m) {T : Set A} (hT : IsClosed T)
    (hT0 : ∀ i, volume ((e i) '' ((e i).source ∩ T)) = 0)
    (hT0' : ∀ j, volume ((e' j) '' ((e' j).source ∩ m ⁻¹' T)) = 0) {d : ℕ}
    (hfib : ∀ x ∉ T, (m ⁻¹' {x}).encard = d)
    (hch : ∀ z, m z ∉ T → ∃ i j, z ∈ (e' j).source ∧ m z ∈ (e i).source ∧ ∀ w ∈ (e' j).source,
      m w ∈ (e i).source → e' j w = e i (m w) ∧ ρ' j w = ρ i (m w)) :
    Measure.map m (glueMeas e' ρ') = (d : ℝ≥0∞) • glueMeas e ρ := by
  have hW : ∀ x : {x // x ∉ T}, ∃ W : Set A, IsOpen W ∧ x.1 ∈ W ∧
      ∀ Q : Set A, MeasurableSet Q → Q ⊆ W →
        glueMeas e' ρ' (m ⁻¹' Q) = d * glueMeas e ρ Q := fun x =>
    exists_evenly_covered_closed hd hρ hd' hρ' hm hT hfib hch x.2
  choose W hWo hxW hWQ using hW
  obtain ⟨C, hC, hCW⟩ := TopologicalSpace.isOpen_iUnion_countable W hWo
  haveI : Countable C := hC.to_subtype
  refine Measure.ext_of_iUnion_eq_univ
    (s := fun o : Option C => o.elim T fun c => W c.1) ?_ fun o => ?_
  · refine eq_univ_of_forall fun x => ?_
    by_cases hx : x ∈ T
    · exact mem_iUnion.2 ⟨none, hx⟩
    · have hmem : x ∈ ⋃ i ∈ C, W i := by
        rw [hCW]
        exact mem_iUnion.2 ⟨⟨x, hx⟩, hxW _⟩
      obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.1 hmem
      exact mem_iUnion.2 ⟨some ⟨c, hc⟩, hxc⟩
  · cases o with
    | none =>
      show (Measure.map m (glueMeas e' ρ')).restrict T = ((d : ℝ≥0∞) • glueMeas e ρ).restrict T
      rw [Measure.restrict_eq_zero.2, Measure.restrict_eq_zero.2]
      · simp [glueMeas_null e ρ hT.measurableSet hT0]
      · rw [Measure.map_apply hm.measurable hT.measurableSet]
        exact glueMeas_null e' ρ' (hT.preimage hm).measurableSet hT0'
    | some c =>
      show (Measure.map m (glueMeas e' ρ')).restrict (W c.1) =
        ((d : ℝ≥0∞) • glueMeas e ρ).restrict (W c.1)
      ext Q hQ
      have hQW := hQ.inter (hWo c.1).measurableSet
      rw [Measure.restrict_apply hQ, Measure.restrict_apply hQ,
        Measure.map_apply hm.measurable hQW, hWQ c.1 _ hQW inter_subset_right]
      simp

end Cover

theorem map_glueMeas_of_cover : ∀ (n : ℕ) (A B ι κ : Type) [TopologicalSpace A] [TopologicalSpace B] [T2Space A] [T2Space B] [SecondCountableTopology A] [SecondCountableTopology B] [MeasurableSpace A] [BorelSpace A] [MeasurableSpace B] [BorelSpace B] (e : ι → OpenPartialHomeomorph A (ReciprocityTheory.L2DbarEstimates.V n)) (ρ : ι → A → ENNReal) (e' : κ → OpenPartialHomeomorph B (ReciprocityTheory.L2DbarEstimates.V n)) (ρ' : κ → B → ENNReal), (∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) (ReciprocityTheory.L2DbarEstimates.Y.ovl e i j)) → (∀ i j y, y ∈ (e i).source → y ∈ (e j).source → ρ i y = ENNReal.ofReal (‖GlobalTheory.ChartGlue.transDet (e i) (e j) y‖ ^ 2) * ρ j y) → (∀ i j, DifferentiableOn ℂ (e' j ∘ (e' i).symm) (ReciprocityTheory.L2DbarEstimates.Y.ovl e' i j)) → (∀ i j y, y ∈ (e' i).source → y ∈ (e' j).source → ρ' i y = ENNReal.ofReal (‖GlobalTheory.ChartGlue.transDet (e' i) (e' j) y‖ ^ 2) * ρ' j y) → ∀ (m : B → A), Continuous m → ∀ T : Set A, IsClosed T → (∀ i, MeasureTheory.volume ((e i) '' ((e i).source ∩ T)) = 0) → (∀ j, MeasureTheory.volume ((e' j) '' ((e' j).source ∩ m ⁻¹' T)) = 0) → ∀ d : ℕ, (∀ x ∉ T, (m ⁻¹' {x}).encard = d) → (∀ z, m z ∉ T → ∃ i j, z ∈ (e' j).source ∧ m z ∈ (e i).source ∧ ∀ w ∈ (e' j).source, m w ∈ (e i).source → e' j w = e i (m w) ∧ ρ' j w = ρ i (m w)) → MeasureTheory.Measure.map m (GlobalTheory.ChartGlue.glueMeas e' ρ') = (d : ENNReal) • GlobalTheory.ChartGlue.glueMeas e ρ := by
  intro n A B ι κ _ _ _ _ _ _ _ _ _ _ e ρ e' ρ' hd hρ hd' hρ' m hm T hT hT0 hT0' d hfib hch
  exact map_glueMeas_closed hd hρ hd' hρ' hm hT hT0 hT0' hfib hch

end GlobalTheory.GlueCoverNull
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

section Gen

variable {R B P : Type} [CommRing R] [CommRing B] [Algebra R B] [CommRing P] [Algebra R P]
  (v : Derivation R P P) {α : B →+* P} (h : SemiHom (RingHom.id R) α)

theorem ctr_mDR_of_kill (hv : ∀ b, v (α b) = 0) (x : DR R B) : ctr v (h.mDR x) = 0 := by
  induction x using indDR with
  | h b => rw [h.mDR_algebraMap, ctr_algebraMap]
  | hd b => rw [h.mDR_ι, h.m1_D, ctr_ι, Derivation.liftKaehlerDifferential_comp_D, hv, map_zero]
  | hm x y hx hy => rw [map_mul, ctr_mul, hx, hy, zero_mul, mul_zero, add_zero]
  | ha x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, add_zero]

theorem lie_mDR_of_kill (hv : ∀ b, v (α b) = 0) (x : DR R B) : lie v (h.mDR x) = 0 := by
  rw [lie_apply, ctr_mDR_of_kill v h hv, map_zero, zero_add, ← h.mDR_dDR, ctr_mDR_of_kill v h hv]

theorem lie_smul_mDR (hv : ∀ b, v (α b) = 0) (p : P) (x : DR R B) :
    lie v (p • h.mDR x) = v p • h.mDR x := by
  rw [Algebra.smul_def, lie_mul, lie_algebraMap, lie_mDR_of_kill v h hv, mul_zero, add_zero, ← Algebra.smul_def]

theorem lie_pow_smul_mDR (hv : ∀ b, v (α b) = 0) (e : ℕ → P) (he0 : v (e 0) = 0)
    (hs : ∀ n, v (e (n + 1)) = e n) (x : DR R B) (n k : ℕ) :
    (lie v ^ k) (e n • h.mDR x) = (if k ≤ n then e (n - k) else 0) • h.mDR x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    by_cases hk : k ≤ n
    · rw [if_pos hk, lie_smul_mDR v h hv]
      by_cases hk' : k + 1 ≤ n
      · rw [if_pos hk', show n - k = (n - (k + 1)) + 1 by omega, hs]
      · rw [if_neg hk', show n - k = 0 by omega, he0]
    · rw [if_neg hk, if_neg (by omega), zero_smul, map_zero]

end Gen

theorem alt_sum_choose_succ (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * ((n + 1).choose (k + 1) : ℤ) = 1 := by
  have h0 := Int.alternating_sum_range_choose (n := n + 1)
  rw [Finset.sum_range_succ'] at h0
  simp only [pow_succ, Nat.choose_zero_right, pow_zero, Nat.cast_one, mul_one, if_neg (Nat.succ_ne_zero n)] at h0
  have : ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * -1 * ((n + 1).choose (k + 1) : ℤ) =
      -∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * ((n + 1).choose (k + 1) : ℤ) := by
    rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun _ _ ↦ by ring
  linarith

theorem sum_e_mul {B : Type} [CommRing B] (Q : PDPoly B) (N n : ℕ) (hn : n < N) :
    ∑ k ∈ Finset.range N, ((-1) ^ k * Q.e (k + 1)) * (if k ≤ n then Q.e (n - k) else 0) = Q.e (n + 1) := by
  simp only [mul_ite, mul_zero]
  rw [← Finset.sum_filter, show (Finset.range N).filter (· ≤ n) = Finset.range (n + 1) by
    ext k; simp only [Finset.mem_filter, Finset.mem_range]; omega]
  have key : ∀ k ∈ Finset.range (n + 1), (-1 : Q.P) ^ k * Q.e (k + 1) * Q.e (n - k) =
      (((-1 : ℤ) ^ k * ((n + 1).choose (k + 1) : ℤ) : ℤ) : Q.P) * Q.e (n + 1) := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [mul_assoc, Q.e_mul, show k + 1 + (n - k) = n + 1 by omega]
    push_cast; ring
  rw [Finset.sum_congr rfl key, ← Finset.sum_mul, ← Int.cast_sum, alt_sum_choose_succ, Int.cast_one, one_mul]

theorem hot_values : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (Q : PDPoly B) [Algebra R Q.P] [IsScalarTower R B Q.P] (η : DividedPowers (Q.ext J)) (v : Derivation R Q.P Q.P) (h : SemiHom (RingHom.id R) (algebraMap B Q.P)), Q.IsStd δ η → (∀ b, v (algebraMap B Q.P b) = 0) → (∀ n, v (Q.e (n + 1)) = Q.e n) → (∀ n, ∀ a ∈ Q.ext J, v (η.dpow (n + 1) a) = η.dpow n a * v a) → ∀ (N n : ℕ) (α : DR R B), hot v Q.e N (Q.e n • h.mDR α) = 0 ∧ (n < N → hot v Q.e N (Q.e n • (ι1 (D R Q.P (Q.e 1)) * h.mDR α)) = Q.e (n + 1) • h.mDR α) := by
  intro R B _ _ _ J δ Q _ _ η v h _ hB hs _ N n α
  have he0 : v (Q.e 0) = 0 := by rw [Q.e_zero]; exact v.map_one_eq_zero
  refine ⟨?_, fun hn ↦ ?_⟩
  · unfold hot
    refine Finset.sum_eq_zero fun k _ ↦ ?_
    rw [map_smul, ctr_mDR_of_kill v h hB, smul_zero, map_zero, smul_zero]
  · have hc : ctr v (Q.e n • (ι1 (D R Q.P (Q.e 1)) * h.mDR α)) = Q.e n • h.mDR α := by
      rw [map_smul, ctr_ι_mul, Derivation.liftKaehlerDifferential_comp_D, hs 0, Q.e_zero, one_smul,
        ctr_mDR_of_kill v h hB, mul_zero, sub_zero]
    unfold hot
    simp only [hc, lie_pow_smul_mDR v h hB Q.e he0 hs, smul_smul]
    rw [← Finset.sum_smul, sum_e_mul Q N n hn]

end GlobalTheory.PDForm
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

theorem _root_.GlobalTheory.T.comparison_relations_respect_cup : ∀ (D : Data) (Λ : Lift D) a b h h', Λ.Rel1 a h → Λ.Rel1 b h' → Λ.Rel2 (cup _ a b) (cupHH D.s h h') := by
  first | exact @GlobalTheory.PDForm.Lift.lift_rel2_cup | exact GlobalTheory.PDForm.Lift.lift_rel2_cup | (intros; apply GlobalTheory.PDForm.Lift.lift_rel2_cup <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

theorem _root_.GlobalTheory.T.pdPolynomial_compatibleForms_generated_induction : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (Q : PDPoly B) [Algebra R Q.P] [IsScalarTower R B Q.P] (η : DividedPowers (Q.ext J)) (v : Derivation R Q.P Q.P) (h : SemiHom (RingHom.id R) (algebraMap B Q.P)), Q.IsStd δ η → (∀ b, v (algebraMap B Q.P b) = 0) → (∀ n, v (Q.e (n + 1)) = Q.e n) → (∀ n, ∀ a ∈ Q.ext J, v (η.dpow (n + 1) a) = η.dpow n a * v a) → ∀ (p : DR R Q.P → Prop), (∀ x ∈ rel R η, p x) → (∀ x y, p x → p y → p (x + y)) → (∀ n α, p (Q.e n • h.mDR α)) → (∀ n α, p (Q.e n • (ι1 (D R Q.P (Q.e 1)) * h.mDR α))) → ∀ x, p x := by
  first | exact @GlobalTheory.PDForm.pdPoly_forms_induction | exact GlobalTheory.PDForm.pdPoly_forms_induction | (intros; apply GlobalTheory.PDForm.pdPoly_forms_induction <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

theorem _root_.GlobalTheory.T.contraction_lieDerivative_divPowerCompat_filtration_rules : (∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (v : Derivation R B B), (∀ n, ∀ a ∈ J, v (δ.dpow (n + 1) a) = δ.dpow n a * v a) → ∀ x ∈ rel R δ, ctr v x ∈ rel R δ ∧ lie v x ∈ rel R δ) ∧ ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (v : Derivation R B B), (∀ n, ∀ a ∈ J, v (δ.dpow (n + 1) a) = δ.dpow n a * v a) → ∀ n, (∀ x ∈ filDR R δ n, ctr v x ∈ filDR R δ n) ∧ (∀ x ∈ filDR R δ (n + 1), dDR R B x ∈ filDR R δ n) ∧ ∀ x ∈ filDR R δ (n + 1), lie v x ∈ filDR R δ n := by
  first | exact @GlobalTheory.PDForm.ctr_lie_rel_filDR | exact GlobalTheory.PDForm.ctr_lie_rel_filDR | (intros; apply GlobalTheory.PDForm.ctr_lie_rel_filDR <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.SmoothLift.LiftEx

theorem isPDNilpotent_map {R A : Type} [CommRing R] [CommRing A] {I : Ideal R} {κ : DividedPowers I} (f : R →+* A)
    {δ : DividedPowers (I.map f)} (h : IsDPMorphism κ δ f) (hκ : IsNilDP κ) : IsNilDP δ := by
  obtain ⟨N, hN⟩ := (isDPNilpotent_iff_exists_isLevel κ).1 hκ
  refine (isDPNilpotent_iff_exists_isLevel δ).2 ⟨N, ?_⟩
  have := fil_le_map_fil R I κ A _ δ f h rfl N
  rw [show fil κ N = ⊥ from hN, Ideal.map_bot] at this
  exact le_bot_iff.1 this

theorem isDPMorphism_algHom {R A A' : Type} [CommRing R] [CommRing A] [CommRing A'] [Algebra R A] [Algebra R A']
    {I : Ideal R} {κ : DividedPowers I} {δ : DividedPowers (I.map (algebraMap R A))}
    {δ' : DividedPowers (I.map (algebraMap R A'))} (h : IsDPMorphism κ δ (algebraMap R A))
    (h' : IsDPMorphism κ δ' (algebraMap R A')) (φ : A →ₐ[R] A') : IsDPMorphism δ δ' (φ : A →+* A') := by
  refine IsDPMorphism.on_span δ δ' (S := algebraMap R A '' I) rfl ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩
    rw [RingHom.coe_coe, φ.commutes]
    exact Ideal.mem_map_of_mem _ ha
  · rintro n _ ⟨a, ha, rfl⟩
    rw [h.2 a ha, RingHom.coe_coe, φ.commutes, φ.commutes, h'.2 a ha]

abbrev ext (D : Data) (U : D.X.affineOpens) : Ideal (Sec D.s U.1) := D.I.map (algebraMap D.R (Sec D.s U.1))

theorem exists_pt (D : Data) (U : D.X.affineOpens) : ∃ x : Sp (Sec D.s U.1 ⧸ ext D U) ⟶ D.X₀,
    x ≫ D.i = spMap (Ideal.Quotient.mk (ext D U)) ≫ affPt D.s U ∧
    x ≫ D.t = spMap ((Ideal.Quotient.mk (ext D U)).comp (algebraMap D.R (Sec D.s U.1))) := by
  obtain ⟨s₀, hpb, ht⟩ := D.red
  let q : D.R ⧸ D.I →+* Sec D.s U.1 ⧸ ext D U :=
    Ideal.quotientMap (ext D U) (algebraMap D.R (Sec D.s U.1)) Ideal.le_comap_map
  have hq : spMap q ≫ spMap (Ideal.Quotient.mk D.I) =
      spMap ((Ideal.Quotient.mk (ext D U)).comp (algebraMap D.R (Sec D.s U.1))) := by
    rw [← Cris.spMap_comp]; rfl
  refine ⟨hpb.lift (spMap (Ideal.Quotient.mk (ext D U)) ≫ affPt D.s U) (spMap q) ?_, hpb.lift_fst _ _ _, ?_⟩
  · rw [hq, Category.assoc, affPt_w, Cris.spMap_comp]
  · rw [ht, ← Category.assoc, hpb.lift_snd, hq]

theorem exists_dp (D : Data) (U : D.X.affineOpens) :
    ∃ δ : DividedPowers (ext D U), IsDPMorphism D.κ δ (algebraMap D.R (Sec D.s U.1)) := by
  haveI := D.sec_smooth U
  exact GlobalTheory.T.exists_isDPMorphism_of_flat_algebra D.R (Sec D.s U.1) D.I D.κ

theorem thick_hom_ext {R : Type} [CommRing R] {I : Ideal R}
    {X : Scheme} {γ : DividedPowers I} {s : X ⟶ Sp R}
    {T T' : Thick γ s} {f g : T ⟶ T'}
    (h : ∀ b, f.φ b = g.φ b) : f = g := by
  rcases f with ⟨φ, φ₀, comm, dp, pt⟩
  rcases g with ⟨ψ, ψ₀, comm', dp', pt'⟩
  obtain rfl : φ = ψ := AlgHom.ext h
  obtain rfl : φ₀ = ψ₀ := RingHom.ext fun c ↦ by
    obtain ⟨b, rfl⟩ := T.surj c
    rw [comm, comm']
  rfl

theorem nonempty_lift : ∀ D : Data, Nonempty (Lift D) := by
  intro D
  choose δ hδ using exists_dp D
  choose x hx hw using exists_pt D
  haveI := D.mono_i
  let T : D.X.affineOpens → Thick D.κ D.t := fun U ↦
    { B := Sec D.s U.1
      J := ext D U
      δ := δ U
      nil := isPDNilpotent_map _ (hδ U) D.nil
      dp := hδ U
      B₀ := Sec D.s U.1 ⧸ ext D U
      π := Ideal.Quotient.mk _
      surj := Ideal.Quotient.mk_surjective
      ker := fun _ ↦ Ideal.Quotient.eq_zero_iff_mem
      x := x U
      w := hw U }
  let m : ∀ {U V : D.X.affineOpens}, V.1 ≤ U.1 → (T U ⟶ T V) := fun {U V} h ↦
    { φ := Sec.res D.s h
      φ₀ := Ideal.quotientMap (ext D V) (Sec.res D.s h : Sec D.s U.1 →+* Sec D.s V.1)
        (Ideal.map_le_iff_le_comap.1 (isDPMorphism_algHom (hδ U) (hδ V) (Sec.res D.s h)).1)
      comm := fun _ ↦ rfl
      dp := isDPMorphism_algHom (hδ U) (hδ V) (Sec.res D.s h)
      pt := by
        rw [← cancel_mono D.i, Category.assoc]
        change spMap _ ≫ x U ≫ D.i = x V ≫ D.i
        rw [hx, hx, ← affPt_res D.s h, ← Category.assoc, ← Category.assoc, ← Cris.spMap_comp, ← Cris.spMap_comp]
        rfl }
  refine ⟨{ L := { obj := fun U ↦ T U.unop
                   map := fun a ↦ m (leOfHom a.unop)
                   map_id := fun U ↦ thick_hom_ext fun b ↦ mp_id (OAff D.s) U b
                   map_comp := fun a b ↦ thick_hom_ext fun c ↦ mp_comp (OAff D.s) a b c }
            e := fun _ ↦ AlgEquiv.refl
            nat := fun _ _ ↦ rfl
            gen := fun _ ↦ rfl
            pt := fun U ↦ (hx U.unop).symm
            mem := fun U ↦ ?_ }⟩
  change ⊤ ≤ (x U.unop ≫ D.i) ⁻¹ᵁ U.unop.1
  rw [hx, Scheme.Hom.comp_preimage]
  have : affPt D.s U.unop ⁻¹ᵁ U.unop.1 = ⊤ := U.unop.2.fromSpec_preimage_self
  rw [this]
  exact le_rfl

end GlobalTheory.SmoothLift.LiftEx
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

theorem _root_.GlobalTheory.T.affinePointPairs_comma_acyclic_degree_le_two : (∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0}) (t : X ⟶ Sp R) (Y : Scheme.{0}) (i : X ⟶ Y), (∀ U V : Y.Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V)) → ∀ T : (IsSm κ t i).FullSubcategory, Desc.Sep ((IsSm κ t i).ι ⋙ Pr.fgt κ t i ⋙ O κ t) (fun S (_ : T ⟶ S) ↦ IsAffineOpen S.obj.U) ∧ Desc.Glue ((IsSm κ t i).ι ⋙ Pr.fgt κ t i ⋙ O κ t) (fun S (_ : T ⟶ S) ↦ IsAffineOpen S.obj.U) ∧ Desc.Van1 ((IsSm κ t i).ι ⋙ Pr.fgt κ t i ⋙ O κ t) (fun S (_ : T ⟶ S) ↦ IsAffineOpen S.obj.U)) ∧ ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0}) (t : X ⟶ Sp R) (Y : Scheme.{0}) (i : X ⟶ Y), (∀ U V : Y.Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V)) → ∀ T : (IsSm κ t i).FullSubcategory, Desc.Van2 ((IsSm κ t i).ι ⋙ Pr.fgt κ t i ⋙ O κ t) (fun S (_ : T ⟶ S) ↦ IsAffineOpen S.obj.U) := by
  first | exact @GlobalTheory.PDForm.isSm_acyclic_two | exact GlobalTheory.PDForm.isSm_acyclic_two | (intros; apply GlobalTheory.PDForm.isSm_acyclic_two <;> assumption)
end

section

open GlobalTheory GlobalTheory.TopForm
open scoped TensorProduct

theorem _root_.GlobalTheory.T.isFreeGen_wedgeForm_of_formallyEtale_mvPolynomial : ∀ {k A₀ A : Type} [CommRing k] [CommRing A₀] [CommRing A] (α : k →+* A₀) (β : k →+* A)
    (ρ : A₀ →+* A), ρ.comp α = β → ∀ {n r : ℕ} (z : Fin n → A₀) (b : Module.Basis (Fin n) A₀ (Omega α)),
    (∀ i, b i = dFun α (z i)) → ∀ (t : Fin r → A), (MvPolynomial.eval₂Hom ρ t).FormallyEtale →
    IsFreeGen A (dForm β (Fin.append t (fun i => ρ (z i)))) := by
  first | exact @GlobalTheory.TopFrameEt.isFreeGen_dForm_of_formallyEtale_mvPolynomial | exact GlobalTheory.TopFrameEt.isFreeGen_dForm_of_formallyEtale_mvPolynomial | (intros; apply GlobalTheory.TopFrameEt.isFreeGen_dForm_of_formallyEtale_mvPolynomial <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.dim_eq_flat_finrank_eq_deg_of_isIsogeny : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), IsIsogeny f → A.dim = B.dim ∧ Flat f.hom.left ∧ 0 < deg f ∧ ∀ y : B.X.left, f.hom.left.finrank y = deg f := by
  first | exact @GlobalTheory.AV.AbVar.isogeny_flat_finrank | exact GlobalTheory.AV.AbVar.isogeny_flat_finrank | (intros; apply GlobalTheory.AV.AbVar.isogeny_flat_finrank <;> assumption)
end
