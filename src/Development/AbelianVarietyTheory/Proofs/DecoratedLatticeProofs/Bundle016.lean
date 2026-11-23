module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ToOneSucc
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle043
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialReductionEvaluateEntryOfMulLaw
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
import Aesop.Main
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.NumberTheory.LocalField.Basic
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralCoordinateShearHaarLocalField
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.Henselian
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsEqTransposeMulMapOfIdempotent
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO

@[expose] public section

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne

noncomputable section
namespace GlobalTheory.PosOne.SrcAction

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def srcRep {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ) :
    Representation ℂ (GL a k) (SB (Matrix b a k)) where
  toFun g :=
    { toFun := fun Φ => ⟨om μ g 1 Φ.1, om_mem_SB μ g 1 Φ.2⟩
      map_add' := fun Φ Ψ => by
        apply Subtype.ext
        have := om_smul_add μ g (1 : GL b k) 1 Φ.1 Ψ.1
        simpa using this
      map_smul' := fun z Φ => by
        apply Subtype.ext
        have := om_smul_add μ g (1 : GL b k) z Φ.1 0
        have h0 : om μ g (1 : GL b k) (0 : Matrix b a k → ℂ) = 0 := by
          funext x
          simp [om]
        simpa [h0] using this }
  map_one' := LinearMap.ext fun Φ => Subtype.ext (om_one μ Φ.1)
  map_mul' g h := LinearMap.ext fun Φ => Subtype.ext (by
    show om μ (g * h) 1 Φ.1 = om μ g 1 (om μ h 1 Φ.1)
    rw [← om_mul, mul_one])

end GlobalTheory.PosOne.SrcAction

namespace GlobalTheory.PosOne
open GlobalTheory.PosOne.SrcAction

theorem isSrc_exists_isSmoothRep : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)), (∃ ρ' : Representation ℂ (GL a k) (SB (Matrix b a k)), IsSrc μ ρ') ∧ ∀ ρ' : Representation ℂ (GL a k) (SB (Matrix b a k)), IsSrc μ ρ' → IsSmoothRep ρ' := by
  intro k _ _ _ _ _ _ a b _ _ _ _ μ hμ
  refine ⟨⟨srcRep μ, fun g Φ => rfl⟩, fun ρ' hρ' Φ => ?_⟩
  have hO := (om_isSmoothRepresentation k a b μ hμ).2.2.2.2 Φ.1 Φ.2
  have hc : Continuous fun g : GL a k => ((g, 1) : GL a k × GL b k) :=
    continuous_id.prodMk continuous_const
  convert hO.preimage hc using 1
  ext g
  simp only [Set.mem_setOf_eq, Set.mem_preimage]
  rw [← hρ' g Φ]
  exact Subtype.ext_iff

end GlobalTheory.PosOne
end
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

theorem _root_.GlobalTheory.T.partialReduction_evaluate_entry_of_mul_law : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (R Q : Type) [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q] (M : Type) [AddCommGroup M] [Module ℂ M] (L : SB (Matrix R Q k) →ₗ[ℂ] M) (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k) (E I : Finset (R × Q)) (e : R × Q), e ∉ I → GlobalTheory.PartRed.Kills L ψ ν w β E I → GlobalTheory.PartRed.EvalLaw L ψ ν w β E I e → GlobalTheory.PartRed.Kills L ψ ν w β (insert e E) I := by
  first | exact @GlobalTheory.PartRedEval.kills_insert_of_evalLaw | exact GlobalTheory.PartRedEval.kills_insert_of_evalLaw | (intros; apply GlobalTheory.PartRedEval.kills_insert_of_evalLaw <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology

noncomputable section
namespace GlobalTheory.SplitWeil.FourierPi

theorem integral_eq_measureReal_box_mul_sum : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), ν.IsAddHaarMeasure → ∀ (n : Type) [Fintype n] (r R : kˣ) (S : Finset (n → k)), (∀ b ∈ S, b ∈ box n R) → (∀ a ∈ box n R, ∃! b, b ∈ S ∧ a - b ∈ box n r) → ∀ F : (n → k) → ℂ, (∀ t ∈ box n r, ∀ y, F (y + t) = F y) → (∀ y ∉ box n R, F y = 0) → ∫ y, F y ∂(Measure.pi fun _ => ν) = ((Measure.pi fun _ : n => ν).real (box n r) : ℂ) * ∑ b ∈ S, F b := by
  intro k _ _ _ _ _ _ ν hν n _ r R S hS hrep F hF hF0
  classical
  have : ν.IsAddHaarMeasure := hν
  have : SecondCountableTopology k := secondCountable k
  have : SigmaFinite ν := inferInstance
  have : (Measure.pi fun _ : n => ν).IsAddHaarMeasure := inferInstance
  set μ : Measure (n → k) := Measure.pi fun _ => ν
  have hmeas : MeasurableSet (box n r) :=
    MeasurableSet.univ_pi fun _ => (isOpen_cball r).measurableSet
  have hfin : μ (box n r) < ⊤ := (isCompact_box r).measure_lt_top

  have key : ∀ y, F y = ∑ b ∈ S, (box n r).indicator (fun _ => F b) (y - b) := by
    intro y
    by_cases hy : y ∈ box n R
    · obtain ⟨b, ⟨hbS, hb⟩, huniq⟩ := hrep y hy
      rw [Finset.sum_eq_single b]
      · rw [Set.indicator_of_mem hb]
        have h := hF (y - b) hb b
        rwa [add_sub_cancel] at h
      · intro b' hb'S hne
        have hnot : y - b' ∉ box n r := fun hmem => hne (huniq b' ⟨hb'S, hmem⟩)
        exact Set.indicator_of_notMem hnot _
      · intro hbn
        exact absurd hbS hbn
    · rw [hF0 y hy]
      symm
      refine Finset.sum_eq_zero fun b _ => ?_
      by_cases hmem : y - b ∈ box n r
      · rw [Set.indicator_of_mem hmem]
        have h := hF (y - b) hmem b
        rw [add_sub_cancel] at h
        rw [← h, hF0 y hy]
      · exact Set.indicator_of_notMem hmem _
  have hint : ∀ b ∈ S, Integrable (fun y => (box n r).indicator (fun _ => F b) (y - b)) μ := by
    intro b _
    have h1 : Integrable ((box n r).indicator fun _ : n → k => F b) μ := by
      refine (integrable_indicator_iff hmeas).2 ?_
      exact integrableOn_const hfin.ne
    exact h1.comp_sub_right b
  calc ∫ y, F y ∂μ = ∫ y, ∑ b ∈ S, (box n r).indicator (fun _ => F b) (y - b) ∂μ := by
        congr 1
        funext y
        exact key y
    _ = ∑ b ∈ S, ∫ y, (box n r).indicator (fun _ => F b) (y - b) ∂μ := integral_finsetSum S hint
    _ = ∑ b ∈ S, (μ.real (box n r) : ℂ) * F b := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [integral_sub_right_eq_self (fun y => (box n r).indicator (fun _ => F b) y) b,
          integral_indicator_const _ hmeas, Complex.real_smul]
    _ = _ := by rw [Finset.mul_sum]

end GlobalTheory.SplitWeil.FourierPi
end
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology

namespace GlobalTheory

theorem box_subset_box_of_valuation_le {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) {s t : kˣ}
    (h : valuation k (s : k) ≤ valuation k (t : k)) : box n s ⊆ box n t :=
  fun x hx i _ => show valuation k (x i) ≤ _ from le_trans (hx i trivial) h

theorem exists_box_superset_of_isCompact (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] (K : Set (n → k)) :
    IsCompact K → ∀ r : kˣ, ∃ R : kˣ, valuation k (r : k) ≤ valuation k (R : k) ∧ K ⊆ box n R := by
  intro hK r
  let ι := {s : kˣ // valuation k (r : k) ≤ valuation k (s : k)}
  haveI : Nonempty ι := ⟨⟨r, le_rfl⟩⟩
  have hcov : K ⊆ ⋃ s : ι, box n (s : kˣ) := by
    intro x _
    rw [Set.mem_iUnion]
    by_cases hn : Nonempty n
    · obtain ⟨i0, -, hi0⟩ := Finset.exists_max_image Finset.univ (fun i => valuation k (x i))
        Finset.univ_nonempty
      by_cases hle : valuation k (x i0) ≤ valuation k (r : k)
      · refine ⟨⟨r, le_rfl⟩, fun i _ => ?_⟩
        exact le_trans (hi0 i (Finset.mem_univ i)) hle
      · push_neg at hle
        have hx0 : x i0 ≠ 0 := by
          intro h0
          rw [h0, map_zero] at hle
          exact not_lt_zero' hle
        refine ⟨⟨Units.mk0 (x i0) hx0, by simpa using hle.le⟩, fun i _ => ?_⟩
        simpa [cball] using hi0 i (Finset.mem_univ i)
    · refine ⟨⟨r, le_rfl⟩, fun i _ => (hn ⟨i⟩).elim⟩
  have hdir : Directed (· ⊆ ·) (fun s : ι => box n (s : kˣ)) := by
    intro s t
    rcases le_total (valuation k ((s : kˣ) : k)) (valuation k ((t : kˣ) : k)) with h | h
    · exact ⟨t, box_subset_box_of_valuation_le n h, le_rfl⟩
    · exact ⟨s, le_rfl, box_subset_box_of_valuation_le n h⟩
  obtain ⟨s, hs⟩ := hK.elim_directed_cover (fun s : ι => box n (s : kˣ))
    (fun s => isOpen_box _) hcov hdir
  exact ⟨s, s.2, hs⟩

end GlobalTheory
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology

noncomputable section
namespace GlobalTheory.BoxReps

def boxSubgroup (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : Type) (s : kˣ) : AddSubgroup (n → k) where
  carrier := box n s
  add_mem' hx hy i _ := add_mem_cball (hx i trivial) (hy i trivial)
  zero_mem' i _ := by simp [cball]
  neg_mem' hx i _ := neg_mem_cball (hx i trivial)

theorem exists_finset_box_reps : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] (r R : kˣ), valuation k (r : k) ≤ valuation k (R : k) → ∃ S : Finset (n → k), (∀ b ∈ S, b ∈ box n R) ∧ ∀ a ∈ box n R, ∃! b, b ∈ S ∧ a - b ∈ box n r := by
  intro k _ _ _ _ n _ r R _
  classical
  set H := boxSubgroup k n r
  have hH : ∀ x, x ∈ H ↔ x ∈ box n r := fun _ => Iff.rfl
  have hq : ∀ a b : n → k, (QuotientAddGroup.mk a : (n → k) ⧸ H) = QuotientAddGroup.mk b ↔ a - b ∈ box n r := by
    intro a b
    rw [QuotientAddGroup.eq, ← hH, ← H.neg_mem_iff]
    simp [neg_add_eq_sub]
  obtain ⟨T, hTsub, hTfin, hcov⟩ := (isCompact_box (n := n) R).elim_finite_subcover_image
    (b := box n R) (c := fun a => (fun x => x - a) ⁻¹' box n r)
    (fun a _ => (isOpen_box r).preimage (continuous_id.sub continuous_const))
    (fun x hx => Set.mem_biUnion hx (show x - x ∈ box n r by rw [sub_self]; exact (boxSubgroup k n r).zero_mem))
  set π : (n → k) → (n → k) ⧸ H := QuotientAddGroup.mk
  let f : (n → k) ⧸ H → (n → k) := fun q =>
    if h : ∃ a ∈ box n R, π a = q then Classical.choose h else 0
  have hf : ∀ a ∈ box n R, f (π a) ∈ box n R ∧ π (f (π a)) = π a := by
    intro a ha
    have h : ∃ b ∈ box n R, π b = π a := ⟨a, ha, rfl⟩
    simp only [f, dif_pos h]
    exact Classical.choose_spec h
  refine ⟨(hTfin.toFinset.image π).image f, ?_, ?_⟩
  · intro b hb
    simp only [Finset.mem_image, Set.Finite.mem_toFinset] at hb
    obtain ⟨q, ⟨t, ht, rfl⟩, rfl⟩ := hb
    exact (hf t (hTsub ht)).1
  · intro a ha
    obtain ⟨t, ht, hat⟩ := Set.mem_iUnion₂.mp (hcov ha)
    have hat' : π a = π t := (hq a t).mpr hat
    refine ⟨f (π a), ⟨?_, ?_⟩, ?_⟩
    · simp only [Finset.mem_image, Set.Finite.mem_toFinset]
      exact ⟨π t, ⟨t, ht, rfl⟩, by rw [hat']⟩
    · exact (hq a _).mp (hf a ha).2.symm
    · rintro b ⟨hb, hab⟩
      simp only [Finset.mem_image, Set.Finite.mem_toFinset] at hb
      obtain ⟨q, ⟨t', ht', rfl⟩, rfl⟩ := hb
      have h1 : π a = π (f (π t')) := (hq a _).mpr hab
      rw [(hf t' (hTsub ht')).2] at h1
      rw [h1]

end GlobalTheory.BoxReps
end
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology

namespace GlobalTheory.CosetSumShift

theorem sum_shift : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] (r R : kˣ) (S : Finset (n → k)),
    (∀ b ∈ S, b ∈ box n R) → (∀ a ∈ box n R, ∃! b, b ∈ S ∧ a - b ∈ box n r) →
    ∀ F : (n → k) → ℂ, (∀ t ∈ box n r, ∀ y, F (y + t) = F y) →
    ∀ a ∈ box n R, ∑ b ∈ S, F (a + b) = ∑ b ∈ S, F b := by
  intro k _ _ _ _ n _ r R S hS huniq F hF a ha
  classical
  have hadd : ∀ {s : kˣ} {x y : n → k}, x ∈ box n s → y ∈ box n s → x + y ∈ box n s :=
    fun hx hy i _ => add_mem_cball (hx i trivial) (hy i trivial)
  have hneg : ∀ {s : kˣ} {x : n → k}, x ∈ box n s → -x ∈ box n s :=
    fun hx i _ => neg_mem_cball (hx i trivial)
  have hzero : (0 : n → k) ∈ box n r := fun i _ => by simp [cball]
  have hmem : ∀ b ∈ S, a + b ∈ box n R := fun b hb => hadd ha (hS b hb)
  choose! c hc using fun b (hb : b ∈ S) => (huniq (a + b) (hmem b hb)).exists
  have hF' : ∀ b ∈ S, F (a + b) = F (c b) := by
    intro b hb
    have := hF _ (hc b hb).2 (c b)
    rwa [add_sub_cancel] at this
  have hinj : ∀ x ∈ S, ∀ y ∈ S, c x = c y → x = y := by
    intro x hx y hy h
    have e : x - y = (a + x - c x) + -(a + y - c y) := by rw [h]; abel
    have h1 : x - y ∈ box n r := e ▸ hadd (hc x hx).2 (hneg (hc y hy).2)
    obtain ⟨z, -, huq⟩ := huniq x (hS x hx)
    exact (huq x ⟨hx, by simpa using hzero⟩).trans (huq y ⟨hy, h1⟩).symm
  have himg : S.image c = S := by
    refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
      exact (hc b hb).1
    · rw [Finset.card_image_of_injOn (fun x hx y hy h => hinj x hx y hy h)]
  rw [Finset.sum_congr rfl hF', ← Finset.sum_image hinj, himg]

end GlobalTheory.CosetSumShift
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

theorem _root_.GlobalTheory.T.integral_coordinate_shear_haar_localField : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), ν.IsAddHaarMeasure → ∀ (J : Type) [Fintype J] [DecidableEq J] (S : Finset J) (g : (J → k) → (J → k)), Continuous g → (∀ y y' : J → k, (∀ j, j ∉ S → y j = y' j) → g y = g y') → (∀ (y : J → k) j, j ∉ S → g y j = 0) → ∀ F : (J → k) → ℂ, ∫ y, F (y + g y) ∂(Measure.pi fun _ => ν) = ∫ y, F y ∂(Measure.pi fun _ => ν) := by
  first | exact @GlobalTheory.CoordShear.integral_shear | exact GlobalTheory.CoordShear.integral_shear | (intros; apply GlobalTheory.CoordShear.integral_shear <;> assumption)
end

section

open IsDedekindDomain NumberField IsLocalRing

namespace GlobalTheory.BinaryUnitForm

theorem exists_eq_of_henselian {R : Type*} [CommRing R] [IsLocalRing R]
    [HenselianRing R (maximalIdeal R)] [Finite (ResidueField R)] (t n u : R)
    (hD : IsUnit (t ^ 2 - 4 * n)) (hu : IsUnit u) :
    ∃ r s : R, r ^ 2 + t * r * s + n * s ^ 2 = u := by
  obtain ⟨r, s, hrs⟩ := GlobalTheory.UnramifiedHermitian.exists_binary_eq_of_finite
    (a := residue R t) (n := residue R n)
    (by simpa only [map_sub, map_mul, map_pow, map_ofNat] using (hD.map (residue R)).ne_zero)
    (residue R u)
  obtain ⟨r, rfl⟩ := residue_surjective r
  obtain ⟨s, rfl⟩ := residue_surjective s
  have hN : residue R (r ^ 2 + t * r * s + n * s ^ 2) = residue R u := by
    simpa only [map_add (f := _), map_mul, map_pow] using hrs
  have hNu : IsUnit (r ^ 2 + t * r * s + n * s ^ 2) := by
    rw [← residue_ne_zero_iff_isUnit, hN]
    exact (hu.map _).ne_zero
  obtain ⟨w, hw⟩ := hNu.exists_right_inv
  have he : u * w - 1 ∈ maximalIdeal R := by
    rw [← residue_eq_zero_iff, map_sub, map_mul, ← hN, ← map_mul, hw, map_one, sub_self]

  have hspan : Ideal.span {(2 : R), t} = ⊤ := by
    apply Ideal.eq_top_of_isUnit_mem _ _ hD
    rw [Ideal.mem_span_pair]
    exact ⟨-2 * n, t, by ring⟩
  obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.1
    (show (1 : R) ∈ Ideal.span {(2 : R), t} by rw [hspan]; exact Submodule.mem_top)
  obtain ⟨T, hT⟩ := GlobalTheory.UnramifiedHermitian.exists_add_mul_sq_eq (maximalIdeal R)
    (α ^ 2 + t * α * β + n * β ^ 2) he
  refine ⟨r * (1 + T * α) - n * s * (T * β), r * (T * β) + (1 + T * α) * s + t * s * (T * β), ?_⟩
  linear_combination (r ^ 2 + t * r * s + n * s ^ 2) * T * hαβ
    + (r ^ 2 + t * r * s + n * s ^ 2) * hT + u * hw

theorem exists_eq_adicCompletionIntegers : ∀ (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (t n u : v.adicCompletionIntegers F),
    IsUnit (t ^ 2 - 4 * n) → IsUnit u → ∃ r s : v.adicCompletionIntegers F,
      r ^ 2 + t * r * s + n * s ^ 2 = u := by
  intro F _ _ v t n u hD hu
  haveI := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  haveI := GlobalTheory.SelfDualGenus.finite_residueField_adicCompletionIntegers v
  exact exists_eq_of_henselian t n u hD hu

end GlobalTheory.BinaryUnitForm
end
