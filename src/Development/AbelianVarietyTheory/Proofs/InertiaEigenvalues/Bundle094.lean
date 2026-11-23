module

import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle001
public import Formalism.ConjugateSelfDual.Bundle001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle053
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle054
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle057
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle056
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
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.Topology.UniformSpace.Matrix
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

namespace GlobalTheory.SmallPrimeIdeal

open NumberField

theorem norm_le_one_of_isIntegral {K : Type} [NormedField K] [IsUltrametricDist K] {y : K}
    (hy : IsIntegral ℤ y) : ‖y‖ ≤ 1 := by
  apply PositivityTheory.Xgf.NI.norm_le_one_of_isIntegral <;> assumption

theorem norm_int_le_one {L K : Type} [Field L] [NormedField K] [IsUltrametricDist K]
    (a : L →+* K) (x : 𝓞 L) : ‖a (x : L)‖ ≤ 1 := by

  exact norm_le_one_of_isIntegral ((NumberField.RingOfIntegers.isIntegral_coe x).map a.toIntAlgHom)

def smallIdeal {L K : Type} [Field L] [NormedField K] [IsUltrametricDist K]
    (a : L →+* K) : Ideal (𝓞 L) where
  carrier := {x | ‖a (x : L)‖ < 1}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    have h : ‖a (x : L) + a (y : L)‖ ≤ max ‖a (x : L)‖ ‖a (y : L)‖ :=
      IsUltrametricDist.norm_add_le_max _ _
    have e : a ((x + y : 𝓞 L) : L) = a (x : L) + a (y : L) := by simp
    change ‖a ((x + y : 𝓞 L) : L)‖ < 1
    rw [e]
    exact lt_of_le_of_lt h (max_lt hx hy)
  smul_mem' := by
    intro c x hx
    have e : a ((c • x : 𝓞 L) : L) = a (c : L) * a (x : L) := by simp
    change ‖a ((c • x : 𝓞 L) : L)‖ < 1
    rw [e, norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right (norm_int_le_one a c) (norm_nonneg _) hx

theorem mem_smallIdeal {L K : Type} [Field L] [NormedField K] [IsUltrametricDist K]
    (a : L →+* K) (x : 𝓞 L) : x ∈ smallIdeal a ↔ ‖a (x : L)‖ < 1 := by
  exact Iff.rfl

theorem norm_eq_one {L K : Type} [Field L] [NormedField K] [IsUltrametricDist K]
    (a : L →+* K) (x : 𝓞 L) (h : ¬ ‖a (x : L)‖ < 1) : ‖a (x : L)‖ = 1 := by
  exact le_antisymm (norm_int_le_one a x) (not_lt.mp h)

theorem smallIdeal_isPrime {L K : Type} [Field L] [NormedField K] [IsUltrametricDist K]
    (a : L →+* K) : (smallIdeal a).IsPrime := by
  refine ⟨?_, ?_⟩
  ·
    rw [Ideal.ne_top_iff_one, mem_smallIdeal]
    simp
  · intro x y hxy
    rw [mem_smallIdeal] at hxy
    rw [mem_smallIdeal, mem_smallIdeal]
    by_contra hc
    push Not at hc
    obtain ⟨hx, hy⟩ := hc
    have e : a ((x * y : 𝓞 L) : L) = a (x : L) * a (y : L) := by simp
    rw [e, norm_mul, norm_eq_one a x (not_lt.mpr hx), norm_eq_one a y (not_lt.mpr hy)] at hxy
    norm_num at hxy

theorem exists_local_dvd {L : Type} [Field L] [NumberField L] (P : Ideal (𝓞 L)) [P.IsPrime]
    (hP : P ≠ ⊥) (u v : 𝓞 L) :
    ∃ r s : 𝓞 L, s ∉ P ∧ (u * r = v * s ∨ v * r = u * s) := by

  let Rp := Localization.AtPrime P
  have : IsDiscreteValuationRing Rp :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 L) hP Rp
  have hinj : Function.Injective (algebraMap (𝓞 L) Rp) :=
    IsLocalization.injective Rp P.primeCompl_le_nonZeroDivisors
  rcases ValuationRing.dvd_total (algebraMap (𝓞 L) Rp u) (algebraMap (𝓞 L) Rp v) with ⟨c, hc⟩ | ⟨c, hc⟩
  · obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl c
    refine ⟨r, s, s.2, Or.inl (hinj ?_)⟩
    rw [map_mul, map_mul, hc, mul_assoc, IsLocalization.mk'_spec]
  · obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl c
    refine ⟨r, s, s.2, Or.inr (hinj ?_)⟩
    rw [map_mul, map_mul, hc, mul_assoc, IsLocalization.mk'_spec]

theorem smallIdeal_ne_bot {L : Type} [Field L] [NumberField L] {l : ℕ} [Fact l.Prime]
    (a : L →+* PadicAlgCl l) : smallIdeal a ≠ ⊥ := by

  intro hbot
  have hl : ((l : 𝓞 L)) ∈ smallIdeal a := by
    rw [mem_smallIdeal]
    have e : a ((l : 𝓞 L) : L) = (l : PadicAlgCl l) := by simp
    have hext := PadicAlgCl.norm_extends (p := l) (l : ℚ_[l])
    rw [map_natCast] at hext
    rw [e, hext, Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  rw [hbot, Ideal.mem_bot] at hl
  have h0 : ((l : 𝓞 L) : L) = 0 := by rw [hl]; simp
  exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast h0)

theorem le_one_of_le_one {L : Type} [Field L] [NumberField L] {l : ℕ} [Fact l.Prime]
    (a b : L →+* PadicAlgCl l)
    (h : ∀ x : 𝓞 L, ‖a (x : L)‖ < 1 ↔ ‖b (x : L)‖ < 1) (x : L) (hx : ‖a x‖ ≤ 1) :
    ‖b x‖ ≤ 1 := by
  classical
  have hb : ∀ y : 𝓞 L, y ∈ smallIdeal a ↔ ‖b (y : L)‖ < 1 := fun y => (mem_smallIdeal a y).trans (h y)
  have := smallIdeal_isPrime a

  obtain ⟨u, w, hw, rfl⟩ := IsFractionRing.div_surjective (𝓞 L) x
  change ‖a ((u : L) / (w : L))‖ ≤ 1 at hx
  change ‖b ((u : L) / (w : L))‖ ≤ 1
  have hw0 : (w : L) ≠ 0 := by
    have := nonZeroDivisors.ne_zero hw
    exact_mod_cast this

  obtain ⟨r, s, hs, hrs⟩ := exists_local_dvd (smallIdeal a) (smallIdeal_ne_bot a) u w
  have hs0 : (s : L) ≠ 0 := by
    intro h0
    apply hs
    have : s = 0 := by exact_mod_cast h0
    rw [this]
    exact (smallIdeal a).zero_mem
  have hbs : ‖b (s : L)‖ = 1 := norm_eq_one b s (fun hlt => hs ((hb s).mpr hlt))
  have has : ‖a (s : L)‖ = 1 := norm_eq_one a s (fun hlt => hs ((mem_smallIdeal a s).mpr hlt))
  rcases hrs with h1 | h1
  ·
    have h1' : (u : L) * r = w * s := by exact_mod_cast congrArg (fun z : 𝓞 L => (z : L)) h1
    have hr0 : (r : L) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at h1'
      exact mul_ne_zero hw0 hs0 h1'.symm
    have e : (u : L) / w = s / r := by
      rw [div_eq_div_iff hw0 hr0]
      linear_combination h1'
    rw [e] at hx ⊢
    rw [map_div₀, norm_div, has] at hx
    have hpos : 0 < ‖a (r : L)‖ := norm_pos_iff.mpr ((map_ne_zero a).mpr hr0)
    have har : ¬ ‖a (r : L)‖ < 1 := by
      intro hlt
      rw [div_le_iff₀ hpos] at hx
      linarith
    have hbr : ‖b (r : L)‖ = 1 := norm_eq_one b r (fun hlt => har ((h r).mpr hlt))
    rw [map_div₀, norm_div, hbs, hbr, div_one]
  ·
    have h1' : (w : L) * r = u * s := by exact_mod_cast congrArg (fun z : 𝓞 L => (z : L)) h1
    have e : (u : L) / w = r / s := by
      rw [div_eq_div_iff hw0 hs0]
      linear_combination -h1'
    rw [e, map_div₀, norm_div, hbs, div_one]
    exact norm_int_le_one b r

theorem norm_le_one_iff {L : Type} [Field L] [NumberField L] {l : ℕ} [Fact (Nat.Prime l)]
    (a b : L →+* Formalism.ConjugateSelfDual.Qbar l)
    (h : ∀ x : 𝓞 L, ‖a (x : L)‖ < (1 : ℝ) ↔ ‖b (x : L)‖ < (1 : ℝ)) (x : L) :
    ‖a x‖ ≤ (1 : ℝ) ↔ ‖b x‖ ≤ (1 : ℝ) := by
  exact ⟨le_one_of_le_one a b h x, le_one_of_le_one b a (fun y => (h y).symm) x⟩

end GlobalTheory.SmallPrimeIdeal
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.borderedMatrixInvariantSpace_exists_compact_open_subset : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (U : Set (Inv r F)) (a₀ : Inv r F), IsOpen U → a₀ ∈ U → ∃ Ω : Set (Inv r F), IsCompact Ω ∧ IsOpen Ω ∧ a₀ ∈ Ω ∧ Ω ⊆ U := by
  first | exact @GlobalTheory.InverseCompactOpen.inv_exists_compact_open | exact GlobalTheory.InverseCompactOpen.inv_exists_compact_open | (intros; apply GlobalTheory.InverseCompactOpen.inv_exists_compact_open <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.exists_nhds_zero_translation_invariant_of_locallyConstant : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] (f : X → ℂ), IsTest f → ∃ U ∈ 𝓝 (0 : X), ∀ x : X, ∀ u ∈ U, f (x + u) = f x := by
  first | exact @GlobalTheory.isTest_nhds_inv | exact GlobalTheory.isTest_nhds_inv | (intros; apply GlobalTheory.isTest_nhds_inv <;> assumption)
end

section

open GlobalTheory.JR Matrix

theorem _root_.GlobalTheory.T.isCompact_preimage_mul_star_anisotropic_submodule : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (V : Submodule E (Matrix (Fin r) (Fin r) E)), (∀ z ∈ V, z * star z = 0 → z = 0) → ∀ B : Set (Matrix (Fin r) (Fin r) E), IsCompact B → IsCompact {z : Matrix (Fin r) (Fin r) E | z ∈ V ∧ z * star z ∈ B} := by
  first | exact @GlobalTheory.mul_star_anisotropic_proper | exact GlobalTheory.mul_star_anisotropic_proper | (intros; apply GlobalTheory.mul_star_anisotropic_proper <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.jacquetRallisUnitMatch_sizeOne : UnitMatch 0 := by
  first | exact @GlobalTheory.JR.SizeOne.unitMatch_zero | exact GlobalTheory.JR.SizeOne.unitMatch_zero | (intros; apply GlobalTheory.JR.SizeOne.unitMatch_zero <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem exists_nhds_zero_add_invariant_of_isTest {X : Type} [UniformSpace X] [AddCommGroup X] [IsUniformAddGroup X] {f : X → ℂ}
    (hf : IsTest f) : ∃ U ∈ 𝓝 (0 : X), ∀ Y : X, ∀ u ∈ U, f (Y + u) = f Y := by
  obtain ⟨hlc, hcs⟩ := hf

  have hK : IsCompact (tsupport f) := hcs
  haveI : CompactSpace (tsupport f) := isCompact_iff_compactSpace.1 hK
  have hfin0 : (Set.range fun x : tsupport f => f x).Finite :=
    (hlc.comp_continuous continuous_subtype_val).range_finite
  have hT : (Set.range f).Finite := by
    refine (hfin0.insert 0).subset ?_
    rintro _ ⟨x, rfl⟩
    by_cases hx : x ∈ tsupport f
    · exact Set.mem_insert_of_mem _ ⟨⟨x, hx⟩, rfl⟩
    · exact Set.mem_insert_iff.2 (Or.inl (image_eq_zero_of_notMem_tsupport hx))

  set D : Set ℂ := (Set.image2 (fun a b => a - b) (Set.range f) (Set.range f)) \ {0} with hD
  have hDfin : D.Finite := (hT.image2 _ hT).diff
  have hDo : Dᶜ ∈ 𝓝 (0 : ℂ) := hDfin.isClosed.isOpen_compl.mem_nhds (fun h => h.2 rfl)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hDo
  have huc := hcs.uniformContinuous_of_continuous hlc.continuous (Metric.dist_mem_uniformity hε)
  rw [uniformity_eq_comap_nhds_zero X, Filter.mem_map, Filter.mem_comap] at huc
  obtain ⟨V, hV, hVs⟩ := huc
  refine ⟨V, hV, fun Y u hu => ?_⟩
  have h1 : ((Y, Y + u) : X × X) ∈ (fun p : X × X => p.2 - p.1) ⁻¹' V := by
    simpa [add_sub_cancel_left] using hu
  have h1' := hVs h1
  simp only [Set.mem_preimage, Set.mem_setOf_eq] at h1'
  have h2 : f (Y + u) - f Y ∈ Metric.ball (0 : ℂ) ε := by
    rw [Metric.mem_ball, dist_zero_right, ← dist_eq_norm, dist_comm]; exact h1'
  have h3 := hball h2
  by_contra hne
  exact h3 ⟨⟨_, ⟨_, rfl⟩, _, ⟨_, rfl⟩, rfl⟩, fun h => hne (sub_eq_zero.1 h)⟩

theorem fourG_isTest : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ →
    ∀ f' : Gl r F → ℂ, IsTest f' → IsTest (fourG M ψ f') := by
  intro F E _ _ _ _ _ r M ψ hψ f' hf
  have hU : ∃ U ∈ 𝓝 (0 : Gl r F), ∀ Y : Gl r F, ∀ u ∈ U, f' (Y + u) = f' Y := by
    exact exists_nhds_zero_add_invariant_of_isTest (X := Gl r F) (f := f') (by exact hf)
  exact ⟨fourG_isLocallyConstant_of_invariant F E r M ψ hψ f' hf hU,
    fourG_hasCompactSupport F E r M ψ hψ f' hf hU⟩

end GlobalTheory.JR
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.OrbProper

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E] {r : ℕ}

theorem continuous_bm : Continuous (fun X : Hn r F E => Bm X.toGl) := by
  refine continuous_matrix fun i j => ?_
  simp only [Bm, Hn.toGl, Matrix.of_apply]
  exact (continuous_apply i).comp
    ((((continuous_subtype_val.comp continuous_fst).pow (j : ℕ))).matrix_mulVec (continuous_fst.comp continuous_snd))

theorem continuous_actU :
    Continuous (fun q : Matrix.unitaryGroup (Fin r) E × Hn r F E => actU q.1 q.2) := by
  haveI := ImgSec.continuousStar (E := E) F
  have hg : Continuous (fun q : Matrix.unitaryGroup (Fin r) E × Hn r F E => (q.1 : Matrix (Fin r) (Fin r) E)) :=
    continuous_subtype_val.comp continuous_fst
  have hA : Continuous (fun q : Matrix.unitaryGroup (Fin r) E × Hn r F E => (q.2.1 : Matrix (Fin r) (Fin r) E)) :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
  refine Continuous.prodMk ?_ (Continuous.prodMk ?_ ?_)
  · exact ((hg.mul hA).mul hg.star).subtype_mk _
  · exact hg.matrix_mulVec (continuous_fst.comp (continuous_snd.comp continuous_snd))
  · exact continuous_snd.comp (continuous_snd.comp continuous_snd)

theorem continuousOn_inv {X : Type} [TopologicalSpace X] {Ω : Set X} {h : X → Matrix (Fin r) (Fin r) E}
    (hh : ContinuousOn h Ω) (hu : ∀ a ∈ Ω, IsUnit (h a).det) : ContinuousOn (fun a => (h a)⁻¹) Ω := by
  have : (fun a => (h a)⁻¹) = fun a => ((h a).det)⁻¹ • (h a).adjugate := by
    funext a; rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [this]
  refine ContinuousOn.smul (f := fun a => ((h a).det)⁻¹) (g := fun a => (h a).adjugate) ?_ ?_
  · exact (continuous_id.matrix_det.comp_continuousOn hh).inv₀ fun a ha => (hu a ha).ne_zero
  · exact continuous_id.matrix_adjugate.comp_continuousOn hh

theorem isCompact_orbit (r : ℕ) (Ω : Set (Inv r F)) (s : Inv r F → Hn r F E)
    (h : Inv r F → Matrix (Fin r) (Fin r) E) (hΩ : IsCompact Ω) (hs : ContinuousOn s Ω) (hhc : ContinuousOn h Ω)
    (hb : ∀ a ∈ Ω, IsUnit (h a).det ∧ Bm (s a).toGl = h a) (C : Set (Hn r F E)) (hC : IsCompact C) :
    IsCompact {p : Matrix.unitaryGroup (Fin r) E × Inv r F | p.2 ∈ Ω ∧ actU p.1 (s p.2) ∈ C} := by
  haveI := ImgSec.continuousStar (E := E) F
  set Φ : Hn r F E × Inv r F → Matrix (Fin r) (Fin r) E := fun q => Bm q.1.toGl * (h q.2)⁻¹ with hΦ
  have hΦc : ContinuousOn Φ (C ×ˢ Ω) := by
    refine (continuous_bm.comp continuous_fst).continuousOn.mul ?_
    exact (continuousOn_inv hhc fun a ha => (hb a ha).1).comp continuous_snd.continuousOn
      (fun q hq => hq.2)
  have hM : IsCompact (Φ '' (C ×ˢ Ω)) := (hC.prod hΩ).image_of_continuousOn hΦc
  have hU : IsClosed ((Matrix.unitaryGroup (Fin r) E : Set (Matrix (Fin r) (Fin r) E))) := isClosed_unitary
  have hK : IsCompact (((↑) : Matrix.unitaryGroup (Fin r) E → Matrix (Fin r) (Fin r) E) ⁻¹' (Φ '' (C ×ˢ Ω))) :=
    (hU.isClosedEmbedding_subtypeVal).isCompact_preimage hM
  have hcl : IsClosed {p : Matrix.unitaryGroup (Fin r) E × Inv r F | p.2 ∈ Ω ∧ actU p.1 (s p.2) ∈ C} := by
    have hf : ContinuousOn (fun p : Matrix.unitaryGroup (Fin r) E × Inv r F => actU p.1 (s p.2))
        (Set.univ ×ˢ Ω) := by
      have h1 : ContinuousOn (fun p : Matrix.unitaryGroup (Fin r) E × Inv r F => (p.1, s p.2)) (Set.univ ×ˢ Ω) :=
        continuous_fst.continuousOn.prodMk (hs.comp continuous_snd.continuousOn (fun q hq => hq.2))
      have h2 := (continuous_actU (F := F) (E := E) (r := r)).comp_continuousOn h1
      exact h2
    have hC2 : IsClosed C := hC.isClosed
    have hO2 : IsClosed (Set.univ ×ˢ Ω : Set (Matrix.unitaryGroup (Fin r) E × Inv r F)) := isClosed_univ.prod hΩ.isClosed
    have h3 := hf.preimage_isClosed_of_isClosed hO2 hC2
    have heq : {p : Matrix.unitaryGroup (Fin r) E × Inv r F | p.2 ∈ Ω ∧ actU p.1 (s p.2) ∈ C} =
        (Set.univ ×ˢ Ω) ∩ (fun p : Matrix.unitaryGroup (Fin r) E × Inv r F => actU p.1 (s p.2)) ⁻¹' C := by
      ext p; simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, true_and, Set.mem_preimage]
    rw [heq]; exact h3
  refine (hK.prod hΩ).of_isClosed_subset hcl ?_
  rintro ⟨g, a⟩ ⟨ha, hC'⟩
  refine ⟨⟨(actU g (s a), a), ⟨hC', ha⟩, ?_⟩, ha⟩
  simp only [hΦ]
  rw [ImgSec.bm_actU, (hb a ha).2, Matrix.mul_nonsing_inv_cancel_right _ _ (hb a ha).1]

end GlobalTheory.JR.OrbProper

theorem GlobalTheory.JR.orbit_proper_of_columns : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (Ω : Set (Inv r F)) (s : Inv r F → Hn r F E) (h : Inv r F → Matrix (Fin r) (Fin r) E), IsCompact Ω → ContinuousOn s Ω → ContinuousOn h Ω → (∀ a ∈ Ω, IsUnit (h a).det ∧ Bm (s a).toGl = h a) → ∀ C : Set (Hn r F E), IsCompact C → IsCompact {p : Matrix.unitaryGroup (Fin r) E × Inv r F | p.2 ∈ Ω ∧ actU p.1 (s p.2) ∈ C} :=
  fun _ _ _ _ _ _ _ r Ω s h hΩ hs hh hb C hC => GlobalTheory.JR.OrbProper.isCompact_orbit r Ω s h hΩ hs hh hb C hC
end
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.partialFourierHermitianBlock_isLocallyConstant : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → (∀ y : E, algebraMap F E (Algebra.trace F E y) = y + star y) → ∀ f : Hn r F E → ℂ, IsTest f → (∃ U ∈ 𝓝 (0 : Hn r F E), ∀ X : Hn r F E, ∀ u ∈ U, f (X + u) = f X) → IsLocallyConstant (fourU M ψ f) := by
  first | exact @GlobalTheory.fourU_isLocallyConstant | exact GlobalTheory.fourU_isLocallyConstant | (intros; apply GlobalTheory.fourU_isLocallyConstant <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.unitIndicators_matchAt_of_one_lt_norm_firstMoment : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas (r + 1) F E) (a : Inv (r + 1) F), 1 < ‖a.2.1 0‖ → MatchAt M (unitG (r + 1) F) (unitU (r + 1) F E) a := by
  first | exact @GlobalTheory.JR.BigMoment.matchAt_unit_of_one_lt_norm | exact GlobalTheory.JR.BigMoment.matchAt_unit_of_one_lt_norm | (intros; apply GlobalTheory.JR.BigMoment.matchAt_unit_of_one_lt_norm <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.isLocallyConstant_partialFourierGLBlock : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ f' : Gl r F → ℂ, IsTest f' → (∃ U ∈ 𝓝 (0 : Gl r F), ∀ Y : Gl r F, ∀ u ∈ U, f' (Y + u) = f' Y) → IsLocallyConstant (fourG M ψ f') := by
  first | exact @GlobalTheory.JR.fourG_isLocallyConstant_of_invariant | exact GlobalTheory.JR.fourG_isLocallyConstant_of_invariant | (intros; apply GlobalTheory.JR.fourG_isLocallyConstant_of_invariant <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.locallyConstantCompactSupport_slices_operator_apply : ∀ {P V Q : Type} [TopologicalSpace P] [TopologicalSpace V] [TopologicalSpace Q] [T2Space P] [T2Space V] [T2Space Q] (T : (V → ℂ) → V → ℂ), (∀ φ, IsTest φ → IsTest (T φ)) → T 0 = 0 → ∀ f : P × V × Q → ℂ, IsTest f → (∀ p q, IsTest (fun v => f (p, v, q))) ∧ IsTest (fun x : P × V × Q => T (fun v => f (x.1, v, x.2.2)) x.2.1) := by
  first | exact @GlobalTheory.slices_test' | exact GlobalTheory.slices_test' | (intros; apply GlobalTheory.slices_test' <;> assumption)
end

section

open GlobalTheory.PMonE

theorem _root_.GlobalTheory.T.norm_frobeniusWindowSeriesTerm_mono : ∀ (F : Type) [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] (h : ℕ) (ϖ : F) (lam π x : Fin h → F), (∀ j, ‖x j‖ ≤ ‖π j‖) → ∀ (r j : Fin h) (n : ℤ), ‖term p ϖ lam x r j n‖ ≤ ‖term p ϖ lam π r j n‖ := by
  first | exact @GlobalTheory.PMonE.term_norm_mono | exact GlobalTheory.PMonE.term_norm_mono | (intros; apply GlobalTheory.PMonE.term_norm_mono <;> assumption)
end
