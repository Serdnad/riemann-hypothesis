module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle120
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle854
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1253
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle973
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle041
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Topology.MetricSpace.Ultra.Pi
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny
open MeasureTheory

noncomputable section

namespace GlobalTheory.SchrSuppFin

theorem exists_nhds_translate_eq {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [NonarchimedeanAddGroup V] {f : V → ℂ} (hf : IsLocallyConstant f) (hc : HasCompactSupport f) :
    ∃ U ∈ nhds (0 : V), ∀ u ∈ U, ∀ z, f (z + u) = f z := by
  have hW : ∀ x : V, ∃ W : OpenAddSubgroup V, ∀ w ∈ (W : Set V), f (x + w) = f x := by
    intro x
    have h1 : {w : V | f (x + w) = f x} ∈ nhds (0 : V) := by
      have h2 := (hf.comp_continuous (show Continuous (fun w : V => x + w) from continuous_const.add continuous_id)).eventually_eq 0
      simp only [Function.comp, add_zero] at h2
      exact h2
    obtain ⟨W, hW⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ h1
    exact ⟨W, fun w hw => hW hw⟩
  choose W hW using hW
  obtain ⟨t, -, ht⟩ := hc.isCompact.elim_nhds_subcover (fun x => {z : V | z - x ∈ (W x : Set V)}) (fun x _ => by
    refine (continuous_sub_right x).continuousAt.preimage_mem_nhds ?_
    simpa using (W x).isOpen.mem_nhds (W x).zero_mem)
  refine ⟨⋂ x ∈ t, (W x : Set V), (Filter.biInter_finset_mem t).2 fun x _ => (W x).isOpen.mem_nhds (W x).zero_mem,
    fun u hu z => ?_⟩
  simp only [Set.mem_iInter] at hu
  by_cases hz : ∃ x ∈ t, z - x ∈ (W x : Set V)
  · obtain ⟨x, hx, hzx⟩ := hz
    have e1 := hW x (z - x) hzx
    have e2 := hW x (z + u - x) (by
      rw [show z + u - x = (z - x) + u by abel]; exact (W x).add_mem hzx (hu x hx))
    rw [show x + (z - x) = z by abel] at e1
    rw [show x + (z + u - x) = z + u by abel] at e2
    rw [e1, e2]
  · push_neg at hz
    have h1 : z ∉ tsupport f := fun h => by
      obtain ⟨x, hx, hzx⟩ := Set.mem_iUnion₂.mp (ht h)
      exact hz x hx hzx
    have h2 : z + u ∉ tsupport f := fun h => by
      obtain ⟨x, hx, hzx⟩ := Set.mem_iUnion₂.mp (ht h)
      refine hz x hx ?_
      have := (W x).sub_mem hzx (hu x hx)
      rwa [show z + u - x - u = z - x by abel] at this
    rw [image_eq_zero_of_notMem_tsupport h1, image_eq_zero_of_notMem_tsupport h2]

theorem nhdsNE_neBot {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) : (nhdsWithin (0 : Fv F v) {0}ᶜ).NeBot := by
  refine ⟨fun h => ?_⟩
  have hopen : IsOpen ({0} : Set (Fv F v)) := (isOpen_singleton_iff_punctured_nhds _).2 h
  haveI := discreteTopology_of_isOpen_singleton_zero hopen
  haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
  have hO : IsCompact ((v.adicCompletionIntegers F : Set (Fv F v))) := isCompact_iff_compactSpace.2 inferInstance
  haveI : CharZero (Fv F v) := charZero_of_injective_algebraMap (algebraMap F (Fv F v)).injective
  have hinf : ((v.adicCompletionIntegers F : Set (Fv F v))).Infinite :=
    Set.infinite_of_injective_forall_mem (Nat.cast_injective (R := Fv F v)) fun n => natCast_mem _ n
  exact hinf (hO.finite_of_discrete)

end GlobalTheory.SchrSuppFin

namespace GlobalTheory.SchrSuppFin

theorem support_compact : ∀ {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) (ψ₀ : AddChar (Fv F v) ℂ) (κ : Type) [Fintype κ]
    [MeasurableSpace (κ → Fv F v)] [BorelSpace (κ → Fv F v)] (μ : MeasureTheory.Measure (κ → Fv F v))
    [μ.IsAddHaarMeasure], Continuous ψ₀ →
    (∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψ₀ (x * y) = 1) → x ∈ v.adicCompletionIntegers F) →
    ∀ φ ∈ SB (κ → Fv F v), ∀ g ∈ SB (κ → Fv F v),
    ∃ C : Set ((κ → Fv F v) × (κ → Fv F v)), IsCompact C ∧
      ∀ w, ∫ y, schr ψ₀ w φ y * (starRingEnd ℂ) (g y) ∂μ ≠ 0 → w ∈ C := by
  intro F _ _ v ψ₀ κ _ _ _ μ _ hψ hcond φ hφ g hg
  classical
  obtain ⟨hφl, hφc⟩ := hφ
  obtain ⟨hgl, hgc⟩ := hg
  obtain ⟨Uφ, hUφ, hφU⟩ := exists_nhds_translate_eq hφl hφc
  obtain ⟨Ug, hUg, hgU⟩ := exists_nhds_translate_eq hgl hgc
  haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
  have hO : IsCompact ((v.adicCompletionIntegers F : Set (Fv F v))) := isCompact_iff_compactSpace.2 inferInstance
  have hP : ∀ᶠ s in nhds (0 : Fv F v), ∀ y ∈ (v.adicCompletionIntegers F : Set (Fv F v)), ∀ i : κ,
      (Pi.single i (s * y) : κ → Fv F v) ∈ Uφ ∩ Ug := by
    refine hO.eventually_forall_of_forall_eventually fun y _ => ?_
    refine Filter.eventually_all.2 fun i => ?_
    have hc : Continuous fun p : Fv F v × Fv F v => (Pi.single i (p.1 * p.2) : κ → Fv F v) :=
      (continuous_single i).comp continuous_mul
    have hmem : Uφ ∩ Ug ∈ nhds ((fun p : Fv F v × Fv F v => (Pi.single i (p.1 * p.2) : κ → Fv F v)) (0, y)) := by
      simpa using Filter.inter_mem hUφ hUg
    exact hc.continuousAt.preimage_mem_nhds hmem
  haveI := nhdsNE_neBot v
  obtain ⟨t, ht, ht0⟩ := ((hP.filter_mono (nhdsWithin_le_nhds (s := {0}ᶜ))).and
    (self_mem_nhdsWithin (s := ({0}ᶜ : Set (Fv F v))))).exists
  have ht0' : t ≠ 0 := ht0
  refine ⟨((fun p : (κ → Fv F v) × (κ → Fv F v) => p.1 - p.2) '' (tsupport φ ×ˢ tsupport g)) ×ˢ
    Set.pi Set.univ (fun _ => (fun y => t⁻¹ * y) '' (v.adicCompletionIntegers F : Set (Fv F v))), ?_, ?_⟩
  · exact ((hφc.isCompact.prod hgc.isCompact).image continuous_sub).prod
      (isCompact_univ_pi fun _ => hO.image (continuous_const_mul _))
  · rintro ⟨a, b⟩ hne
    have key : ∀ u ∈ Uφ ∩ Ug, ψ₀ (u ⬝ᵥ b) = 1 := by
      intro u hu
      have hG : ∀ y, schr ψ₀ (a, b) φ (y + u) * (starRingEnd ℂ) (g (y + u)) =
          ψ₀ (u ⬝ᵥ b) * (schr ψ₀ (a, b) φ y * (starRingEnd ℂ) (g y)) := by
        intro y
        simp only [schr]
        rw [show y + u + a = (y + a) + u by abel, hφU u hu.1, hgU u hu.2, add_dotProduct,
          show y ⬝ᵥ b + u ⬝ᵥ b + ⅟(2 : Fv F v) * (a ⬝ᵥ b) = u ⬝ᵥ b + (y ⬝ᵥ b + ⅟(2 : Fv F v) * (a ⬝ᵥ b)) by ring,
          AddChar.map_add_eq_mul]
        ring
      have e := integral_add_right_eq_self (μ := μ)
        (fun y => schr ψ₀ (a, b) φ y * (starRingEnd ℂ) (g y)) u
      simp only [hG] at e
      rw [integral_const_mul] at e
      have h0 : (ψ₀ (u ⬝ᵥ b) - 1) * ∫ y, schr ψ₀ (a, b) φ y * (starRingEnd ℂ) (g y) ∂μ = 0 := by
        rw [sub_mul, e]; ring
      exact sub_eq_zero.1 ((mul_eq_zero.1 h0).resolve_right hne)
    refine ⟨?_, ?_⟩
    · have hex : ∃ y, schr ψ₀ (a, b) φ y * (starRingEnd ℂ) (g y) ≠ 0 := by
        by_contra h
        push_neg at h
        exact hne (by simp [h])
      obtain ⟨y, hy⟩ := hex
      have h1 : φ (y + a) ≠ 0 := fun h => hy (by simp [schr, h])
      have h2 : g y ≠ 0 := fun h => hy (by simp [h])
      exact ⟨(y + a, y), ⟨subset_tsupport _ h1, subset_tsupport _ h2⟩, by simp⟩
    · intro i _
      have hb : t * b i ∈ v.adicCompletionIntegers F := hcond _ fun y hy => by
        have := key _ (ht y hy i)
        rwa [single_dotProduct, show t * y * b i = t * b i * y by ring] at this
      exact ⟨t * b i, hb, by field_simp⟩

end GlobalTheory.SchrSuppFin

end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped GlobalTheory.VacAny
open Filter Topology

namespace GlobalTheory.SchrBox

theorem exists_cut {X ι : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] (χ : ι → X → ℂ)
    (hχ : ∀ i x y, χ i (x + y) = χ i x * χ i y) {B : Set X} (hB : IsOpen B) (h0 : (0 : X) ∈ B)
    (hsep : ∀ z, z ∉ B → ∃ i, χ i z ≠ 1 ∧ ∀ u ∈ B, χ i u = 1) {K : Set X} (hK : IsCompact K) (x₀ : X) :
    ∃ g ∈ Algebra.adjoin ℂ (Set.range χ), (∀ x, x - x₀ ∈ B → g x = 1) ∧ ∀ x ∈ K, x - x₀ ∉ B → g x = 0 := by
  have hop : ∀ y : X, IsOpen {x | x - y ∈ B} := fun y => hB.preimage (continuous_id.sub continuous_const)
  have key := (hK.diff (hop x₀)).induction_on
    (p := fun T => ∃ g ∈ Algebra.adjoin ℂ (Set.range χ), (∀ x, x - x₀ ∈ B → g x = 1) ∧ ∀ x ∈ T, g x = 0)
    ⟨1, one_mem _, fun _ _ => rfl, fun _ h => h.elim⟩
    (fun s t hst ⟨g, hg, h1, h2⟩ => ⟨g, hg, h1, fun x hx => h2 x (hst hx)⟩)
    (fun s t hs ht => by
      obtain ⟨g, hg, h1, h2⟩ := hs
      obtain ⟨g', hg', h1', h2'⟩ := ht
      refine ⟨g * g', mul_mem hg hg', fun x hx => by simp [h1 x hx, h1' x hx], fun x hx => ?_⟩
      rcases hx with hx | hx
      · simp [h2 x hx]
      · simp [h2' x hx])
    (fun y hy => by
      obtain ⟨i, hi, hiB⟩ := hsep (y - x₀) hy.2
      have hne : 1 - χ i (y - x₀) ≠ 0 := sub_ne_zero.2 hi.symm
      have hx0 : ∀ x, χ i (-x₀) * χ i x = χ i (x - x₀) := fun x => by
        rw [← hχ]; congr 1; abel
      refine ⟨{x | x - y ∈ B}, mem_nhdsWithin_of_mem_nhds ((hop y).mem_nhds (by simpa using h0)),
        (1 - χ i (y - x₀))⁻¹ • (χ i (-x₀) • χ i - χ i (y - x₀) • 1), ?_, fun x hx => ?_, fun x hx => ?_⟩
      · exact Subalgebra.smul_mem _ (sub_mem (Subalgebra.smul_mem _ (Algebra.subset_adjoin (Set.mem_range_self i)) _)
          (Subalgebra.smul_mem _ (one_mem _) _)) _
      · simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.one_apply, mul_one, hx0, hiB _ hx]
        exact inv_mul_cancel₀ hne
      · have : χ i (x - x₀) = χ i (y - x₀) := by
          rw [show x - x₀ = (x - y) + (y - x₀) by abel, hχ, hiB _ hx, one_mul]
        simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.one_apply, mul_one, hx0, this, sub_self, mul_zero])
  obtain ⟨g, hg, h1, h2⟩ := key
  exact ⟨g, hg, h1, fun x hx hx' => h2 x ⟨hx, hx'⟩⟩

theorem adjoin_mul_mem {X ι : Type} [AddCommGroup ι] (χ : ι → X → ℂ) (h0 : χ 0 = 1) (hχ : ∀ i j, χ (i + j) = χ i * χ j)
    (s : X → ℂ) {g : X → ℂ} (hg : g ∈ Algebra.adjoin ℂ (Set.range χ)) :
    g * s ∈ Submodule.span ℂ (Set.range fun i => χ i * s) := by
  have key : ∀ f ∈ Submodule.span ℂ (Set.range fun i => χ i * s),
      g * f ∈ Submodule.span ℂ (Set.range fun i => χ i * s) := by
    induction hg using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      intro f hf
      induction hf using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨j, rfl⟩ := hy
        exact Submodule.subset_span ⟨i + j, by simp only [hχ, mul_assoc]⟩
      | zero => simp
      | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
      | smul c a _ ha => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ ha
    | algebraMap r => intro f hf; rw [← Algebra.smul_def]; exact Submodule.smul_mem _ _ hf
    | add a b _ _ ha hb => intro f hf; rw [add_mul]; exact add_mem (ha f hf) (hb f hf)
    | mul a b _ _ ha hb => intro f hf; rw [mul_assoc]; exact ha _ (hb f hf)
  exact key s (Submodule.subset_span ⟨0, by simp [h0]⟩)

variable {F : Type} [Field F] [NumberField F] {v : Pl (F := F)}

theorem isOpen_ball (n : ℤ) : IsOpen {y : Fv F v | Valued.v y ≤ WithZero.exp n} := by
  obtain ⟨c, hc⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp n)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact WithZero.exp_ne_zero hc.symm
  have : {y : Fv F v | Valued.v y ≤ WithZero.exp n} = {y | Valued.v.restrict y ≤ Valued.v.restrict c} := by
    ext y
    simp only [Set.mem_ofPred_eq, Valuation.restrict_le_iff, hc]
  rw [this]
  exact Valued.isOpen_closedBall _ (by simp [hc0])

theorem exists_ball_subset {U : Set (Fv F v)} {x : Fv F v} (hU : U ∈ 𝓝 x) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ y, Valued.v (y - x) ≤ WithZero.exp (-(N : ℤ)) → y ∈ U := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.1 hU
  have hne : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
  refine ⟨(WithZero.log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)).natAbs + 1, fun N hN y hy => hγ ?_⟩
  simp only [Set.mem_ofPred_eq, Valuation.restrict_lt_iff_lt_embedding]
  refine hy.trans_lt ?_
  conv_rhs => rw [← WithZero.exp_log hne]
  rw [WithZero.exp_lt_exp]
  omega

theorem exists_sep {ψ : AddChar (Fv F v) ℂ}
    (hψ : ∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψ (x * y) = 1) ↔ x ∈ v.adicCompletionIntegers F)
    (n : ℤ) {z : Fv F v} (hz : ¬ Valued.v z ≤ WithZero.exp n) :
    ∃ t, ψ (z * t) ≠ 1 ∧ ∀ u, Valued.v u ≤ WithZero.exp n → ψ (u * t) = 1 := by
  obtain ⟨c, hc⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp n)
  have hmem : ∀ u : Fv F v, u / c ∈ v.adicCompletionIntegers F ↔ Valued.v u ≤ WithZero.exp n := fun u => by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀, hc, div_le_one₀ WithZero.exp_pos]
  have h1 := mt (hψ (z / c)).1 (mt (hmem z).1 hz)
  push Not at h1
  obtain ⟨y, hy, hy1⟩ := h1
  refine ⟨y / c, by rwa [show z * (y / c) = z / c * y by ring], fun u hu => ?_⟩
  rw [show u * (y / c) = u / c * y by ring]
  exact (hψ _).2 ((hmem u).2 hu) y hy

theorem indicator_box_mem_span : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (ψ : AddChar (Fv F v) ℂ), (∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψ (x * y) = 1) ↔ x ∈ v.adicCompletionIntegers F) → ∀ (κ : Type) [Fintype κ] (s : (κ → Fv F v) → ℂ), s ∈ SB (κ → Fv F v) → s ≠ 0 → ∃ (x₀ : κ → Fv F v) (N₀ : ℕ), ∀ N ≥ N₀, Set.indicator {x : κ → Fv F v | ∀ i, Valued.v (x i - x₀ i) ≤ WithZero.exp (-(N : ℤ))} (1 : (κ → Fv F v) → ℂ) ∈ Submodule.span ℂ (Set.range fun w : (κ → Fv F v) × (κ → Fv F v) => schr ψ w s) := by
  intro F _ _ v ψ hψ κ _ s hs hs0
  classical
  obtain ⟨x₀, hx₀⟩ := Function.ne_iff.1 hs0
  have hx₀ : s x₀ ≠ 0 := hx₀
  have hU : {x | s x = s x₀} ∈ 𝓝 x₀ := (hs.1.isOpen_fiber (s x₀)).mem_nhds rfl
  rw [nhds_pi, Filter.mem_pi'] at hU
  obtain ⟨I, t, ht, htU⟩ := hU
  choose M hM using fun i => exists_ball_subset (ht i)
  refine ⟨x₀, Finset.univ.sup M, fun N hN => ?_⟩
  have hconst : ∀ x : κ → Fv F v, (∀ i, Valued.v (x i - x₀ i) ≤ WithZero.exp (-(N : ℤ))) → s x = s x₀ :=
    fun x hx => htU fun i _ => hM i N ((Finset.le_sup (f := M) (Finset.mem_univ i)).trans hN) _ (hx i)
  let χ : (κ → Fv F v) → (κ → Fv F v) → ℂ := fun b x => ψ (x ⬝ᵥ b)
  have hB : IsOpen {x : κ → Fv F v | ∀ i, Valued.v (x i) ≤ WithZero.exp (-(N : ℤ))} := by
    rw [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => (isOpen_ball (v := v) (-(N : ℤ))).preimage (continuous_apply (A := fun _ : κ => Fv F v) i)
  obtain ⟨g, hg, h1, h2⟩ := exists_cut χ (fun b x y => by simp only [χ, add_dotProduct, AddChar.map_add_eq_mul]) hB
    (by simp) (fun z hz => by
      simp only [Set.mem_ofPred_eq, not_forall] at hz
      obtain ⟨i, hi⟩ := hz
      obtain ⟨t, ht1, ht2⟩ := exists_sep hψ _ hi
      exact ⟨Pi.single i t, by simpa only [χ, dotProduct_single] using ht1,
        fun u hu => by simpa only [χ, dotProduct_single] using ht2 _ (hu i)⟩) hs.2 x₀
  have hm := adjoin_mul_mem χ (by ext x; simp [χ])
    (fun i j => by ext x; simp only [χ, dotProduct_add, AddChar.map_add_eq_mul, Pi.mul_apply]) s hg
  have hle : Submodule.span ℂ (Set.range fun b => χ b * s) ≤
      Submodule.span ℂ (Set.range fun w : (κ → Fv F v) × (κ → Fv F v) => schr ψ w s) := by
    refine Submodule.span_mono ?_
    rintro _ ⟨b, rfl⟩
    exact ⟨(0, b), by ext x; simp [schr, χ]⟩
  have := Submodule.smul_mem _ (s x₀)⁻¹ (hle hm)
  convert this using 1
  ext x
  by_cases hx : ∀ i, Valued.v (x i - x₀ i) ≤ WithZero.exp (-(N : ℤ))
  · rw [Set.indicator_of_mem (by exact hx)]
    simp [h1 x hx, hconst x hx, hx₀]
  · rw [Set.indicator_of_notMem (by exact hx)]
    by_cases hxs : x ∈ tsupport s
    · simp [h2 x hxs hx]
    · simp [image_eq_zero_of_notMem_tsupport hxs]

end GlobalTheory.SchrBox
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.KummerStep

noncomputable abbrev gU (A : Type) [CommRing A] : Aˣ →* (Γ(Spec (CommRingCat.of A), ⊤))ˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom.toMonoidHom

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp]

theorem isUnit_natCast_of {k R : Type} [Field k] [CommRing R] (φ : k →+* R) {q : ℕ} (hq : IsUnit (q : k)) :
    IsUnit (q : R) := by
  simpa using hq.map φ

theorem kum_spMap (q : ℕ) [NeZero q] {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (hq : IsUnit (q : A))
    (u : Aˣ) : pull _ (spMap φ) _ _ (kum q (gU A u)) = kum q (gU B (Units.map φ.toMonoidHom u)) := by
  have hq' : IsUnit (q : Γ(Spec (CommRingCat.of A), ⊤)) := by
    simpa using hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  rw [(GlobalTheory.T.cup_chern_kummer_pullback_naturality q).2.2.2 (Spec.map (CommRingCat.ofHom φ)) (gU A u) hq']
  congr 1
  ext
  have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  have h2 : (Spec.map (CommRingCat.ofHom φ)).appTop = (Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫ CommRingCat.ofHom φ ≫
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv := by
    rw [← Category.assoc, ← h]; simp
  simp only [gU, Units.coe_map, MonoidHom.coe_coe]
  rw [h2]
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom]
  simp

theorem kum_pow_eq (q : ℕ) [NeZero q] {A : Type} [CommRing A] (hq : IsUnit (q : A)) (u v : Aˣ) :
    kum q (gU A (u * v ^ q)) = kum q (gU A u) := by
  have hq' : IsUnit (q : Γ(Spec (CommRingCat.of A), ⊤)) := by
    simpa using hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  rw [map_mul, map_pow, ((GlobalTheory.T.chernClass_kummerClass_additive q).2 (gU A u) _ hq').1, ((GlobalTheory.T.chernClass_kummerClass_additive q).2 (gU A v) (gU A v) hq').2, add_zero]

theorem kum_pow (q : ℕ) [NeZero q] {A : Type} [CommRing A] (hq : IsUnit (q : A)) (v : Aˣ) :
    kum q (gU A (v ^ q)) = 0 := by
  have := kum_pow_eq q hq 1 v
  rw [one_mul] at this
  rw [this, map_one]
  have hq' : IsUnit (q : Γ(Spec (CommRingCat.of A), ⊤)) := by
    simpa using hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  have h := ((GlobalTheory.T.chernClass_kummerClass_additive q).2 (1 : (Γ(Spec (CommRingCat.of A), ⊤))ˣ) 1 hq').1
  rw [one_mul] at h
  simpa using h

theorem of_steps (L1 : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (A' : Type) [CommRing A'] [Algebra B A'], IsExcisionNbhd B A' f → ∀ w : Ht q (sp (Localization.Away (algebraMap B A' f))) 1 1, ∃ (A₂ : Type) (_ : CommRing A₂) (_ : Algebra B A₂) (_ : Algebra A' A₂) (_ : IsScalarTower B A' A₂), IsExcisionNbhd B A₂ f ∧ ∃ c : (Γ(Spec (CommRingCat.of (Localization.Away (algebraMap B A₂ f))), ⊤))ˣ, ∀ φ : Localization.Away (algebraMap B A' f) →+* Localization.Away (algebraMap B A₂ f), φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) → pull _ (spMap φ) _ _ w = kum q c) (L2 : ∀ (q : ℕ) (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (A₂ : Type) [CommRing A₂] [Algebra B A₂], IsExcisionNbhd B A₂ f → ∀ c : (Localization.Away (algebraMap B A₂ f))ˣ, ∃ g : B, IsCoprime f g ∧ ∃ u : (Localization.Away (f * g))ˣ, (∃ (A₃ : Type) (_ : CommRing A₃) (_ : Algebra B A₃) (_ : Algebra A₂ A₃) (_ : IsScalarTower B A₂ A₃), IsExcisionNbhd B A₃ f ∧ IsUnit (algebraMap B A₃ g) ∧ ∃ v : (Localization.Away (algebraMap B A₃ f))ˣ, ∀ (φ : Localization.Away (algebraMap B A₂ f) →+* Localization.Away (algebraMap B A₃ f)) (ψ : Localization.Away (f * g) →+* Localization.Away (algebraMap B A₃ f)), φ.comp (algebraMap A₂ _) = (algebraMap A₃ _).comp (algebraMap A₂ A₃) → ψ.comp (algebraMap B _) = (algebraMap A₃ _).comp (algebraMap B A₃) → φ (c : Localization.Away (algebraMap B A₂ f)) = ψ (u : Localization.Away (f * g)) * (v : Localization.Away (algebraMap B A₃ f)) ^ q) ∧ ∃ (C : Type) (_ : CommRing C) (_ : Algebra B C), IsExcisionNbhd B C g ∧ ∃ v' : (Localization.Away (algebraMap B C (f * g)))ˣ, Localization.awayMap (algebraMap B C) (f * g) (u : Localization.Away (f * g)) = (v' : Localization.Away (algebraMap B C (f * g))) ^ q) : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (A' : Type) [CommRing A'] [Algebra B A'], IsExcisionNbhd B A' f → ∀ w : Ht q (sp (Localization.Away (algebraMap B A' f))) 1 1, ∃ g : B, IsCoprime f g ∧ ∃ (A₂ C : Type) (_ : CommRing A₂) (_ : CommRing C) (_ : Algebra B A₂) (_ : Algebra A' A₂) (_ : IsScalarTower B A' A₂) (_ : Algebra B C), IsExcisionNbhd B A₂ f ∧ IsUnit (algebraMap B A₂ g) ∧ IsExcisionNbhd B C g ∧ ∃ a : Ht q (sp (Localization.Away (f * g))) 1 1, pull _ (spMap (Localization.awayMap (algebraMap B C) (f * g))) _ _ a = 0 ∧ ∀ (φ : Localization.Away (algebraMap B A' f) →+* Localization.Away (algebraMap B A₂ f)) (ψ : Localization.Away (f * g) →+* Localization.Away (algebraMap B A₂ f)), φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) → ψ.comp (algebraMap B _) = (algebraMap A₂ _).comp (algebraMap B A₂) → pull _ (spMap φ) _ _ w = pull _ (spMap ψ) _ _ a := by
  intro q _ k B _ _ _ _ _ _ hq f hf A' _ _ hA' w
  obtain ⟨A₂, _, _, _, _, hA₂, c, hc⟩ := L1 q k B hq f hf A' hA' w
  set c₀ : (Localization.Away (algebraMap B A₂ f))ˣ :=
    Units.map (Scheme.ΓSpecIso (CommRingCat.of (Localization.Away (algebraMap B A₂ f)))).hom.hom.toMonoidHom c with hc₀
  have hcc : gU _ c₀ = c := by
    ext; simp [c₀, gU]
  obtain ⟨g, hfg, u, ⟨A₃, _, _, _, _, hA₃, hg, v, hv⟩, C, _, _, hC, v', hv'⟩ := L2 q k B hq f hf A₂ hA₂ c₀
  letI : Algebra A' A₃ := ((algebraMap A₂ A₃).comp (algebraMap A' A₂)).toAlgebra
  haveI : IsScalarTower B A' A₃ := IsScalarTower.of_algebraMap_eq (fun b => by
    show algebraMap B A₃ b = algebraMap A₂ A₃ (algebraMap A' A₂ (algebraMap B A' b))
    rw [← IsScalarTower.algebraMap_apply B A' A₂, ← IsScalarTower.algebraMap_apply B A₂ A₃])
  have hkB : ∀ (R : Type) [CommRing R] [Algebra B R], IsUnit (q : R) := fun R _ _ =>
    isUnit_natCast_of ((algebraMap B R).comp (algebraMap k B)) hq
  refine ⟨g, hfg, A₃, C, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    hA₃, hg, hC, kum q (gU _ u), ?_, ?_⟩
  · rw [kum_spMap q _ (hkB _)]
    have : Units.map (Localization.awayMap (algebraMap B C) (f * g)).toMonoidHom u = v' ^ q := by
      ext; simpa using hv'
    rw [this]
    exact kum_pow q (hkB _) v'
  · intro φ ψ hφ hψ
    have hu₁ : IsUnit (((algebraMap A₂ (Localization.Away (algebraMap B A₂ f))).comp (algebraMap A' A₂))
        (algebraMap B A' f)) := by
      rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply B A' A₂]
      exact IsLocalization.Away.algebraMap_isUnit _
    have hu₂ : IsUnit (((algebraMap A₃ (Localization.Away (algebraMap B A₃ f))).comp (algebraMap A₂ A₃))
        (algebraMap B A₂ f)) := by
      rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply B A₂ A₃]
      exact IsLocalization.Away.algebraMap_isUnit _
    set φ₁ : Localization.Away (algebraMap B A' f) →+* Localization.Away (algebraMap B A₂ f) :=
      IsLocalization.Away.lift (algebraMap B A' f) hu₁
    set φ₂ : Localization.Away (algebraMap B A₂ f) →+* Localization.Away (algebraMap B A₃ f) :=
      IsLocalization.Away.lift (algebraMap B A₂ f) hu₂
    have hφ₁ : φ₁.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) :=
      IsLocalization.Away.lift_comp (S := Localization.Away (algebraMap B A' f)) (algebraMap B A' f) hu₁
    have hφ₂ : φ₂.comp (algebraMap A₂ _) = (algebraMap A₃ _).comp (algebraMap A₂ A₃) :=
      IsLocalization.Away.lift_comp (S := Localization.Away (algebraMap B A₂ f)) (algebraMap B A₂ f) hu₂
    have hφe : φ = φ₂.comp φ₁ := by
      refine IsLocalization.ringHom_ext (Submonoid.powers (algebraMap B A' f)) ?_
      rw [hφ, RingHom.comp_assoc, hφ₁, ← RingHom.comp_assoc, hφ₂, RingHom.comp_assoc]
      rfl
    have key := hv φ₂ ψ hφ₂ hψ
    have hkey : Units.map φ₂.toMonoidHom c₀ = Units.map ψ.toMonoidHom u * v ^ q := by
      ext; simpa using key
    rw [hφe, spMap_comp', pull_comp, hc φ₁ hφ₁, ← hcc, kum_spMap q φ₂ (hkB _), hkey, kum_pow_eq q (hkB _),
      kum_spMap q ψ (hkB _)]

theorem exists_class_agreeing_near_zeros : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (A' : Type) [CommRing A'] [Algebra B A'], IsExcisionNbhd B A' f → ∀ w : Ht q (sp (Localization.Away (algebraMap B A' f))) 1 1, ∃ g : B, IsCoprime f g ∧ ∃ (A₂ C : Type) (_ : CommRing A₂) (_ : CommRing C) (_ : Algebra B A₂) (_ : Algebra A' A₂) (_ : IsScalarTower B A' A₂) (_ : Algebra B C), IsExcisionNbhd B A₂ f ∧ IsUnit (algebraMap B A₂ g) ∧ IsExcisionNbhd B C g ∧ ∃ a : Ht q (sp (Localization.Away (f * g))) 1 1, pull _ (spMap (Localization.awayMap (algebraMap B C) (f * g))) _ _ a = 0 ∧ ∀ (φ : Localization.Away (algebraMap B A' f) →+* Localization.Away (algebraMap B A₂ f)) (ψ : Localization.Away (f * g) →+* Localization.Away (algebraMap B A₂ f)), φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) → ψ.comp (algebraMap B _) = (algebraMap A₂ _).comp (algebraMap B A₂) → pull _ (spMap φ) _ _ w = pull _ (spMap ψ) _ _ a :=
  of_steps GlobalTheory.T.exists_kummerClass_on_finer_etaleNbhd_curve GlobalTheory.T.unit_localization_etaleNbhd_eq_unit_mul_pow

end GlobalTheory.EtC.KummerStep
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.TanGauge

noncomputable section
namespace GlobalTheory.MBLow.TanGauge

theorem trV_cocycle : ∀ {X : Scheme.{0}} (L : LB X), L.IsLB → ∀ {A : Type} [CommRing A] (y : Sp A ⟶ X) (a b c : L.ι) (n : ℤ),
    ⊤ ≤ y ⁻¹ᵁ L.U a → ⊤ ≤ y ⁻¹ᵁ L.U b → ⊤ ≤ y ⁻¹ᵁ L.U c →
    trV L y a b n * trV L y b c n = trV L y a c n := by
  intro X L hL A _ y a b c n ha hb hc
  have hT : ⊤ ≤ y ⁻¹ᵁ (L.U a ⊓ L.U b ⊓ L.U c) := fun q hq => ⟨⟨ha hq, hb hq⟩, hc hq⟩
  have e := congrArg (fun u => ((u ^ n : Γ(X, L.U a ⊓ L.U b ⊓ L.U c)ˣ) : Γ(X, L.U a ⊓ L.U b ⊓ L.U c))) (hL.cocycle a b c)
  simp only [mul_zpow, ← map_zpow, Units.val_mul] at e
  have e' := congrArg (valR y (L.U a ⊓ L.U b ⊓ L.U c)) e
  rw [GlobalTheory.ZH.CrdCalc.valR_mul y _ hT] at e'
  unfold trV
  rw [← GlobalTheory.ZH.CrdCalc.valR_res y (inf_le_left : L.U a ⊓ L.U b ⊓ L.U c ≤ L.U a ⊓ L.U b) hT,
    ← GlobalTheory.ZH.CrdCalc.valR_res y (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
      L.U a ⊓ L.U b ⊓ L.U c ≤ L.U b ⊓ L.U c) hT,
    ← GlobalTheory.ZH.CrdCalc.valR_res y (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
      L.U a ⊓ L.U b ⊓ L.U c ≤ L.U a ⊓ L.U c) hT]
  exact e'

end GlobalTheory.MBLow.TanGauge
end
end
