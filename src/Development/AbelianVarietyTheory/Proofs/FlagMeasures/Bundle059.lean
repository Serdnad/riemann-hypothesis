module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle015
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralFintypeProd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle001
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MemConfTOfDetNeZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle045
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Set.Finite.Lattice

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

noncomputable section
namespace GlobalTheory.SnMass.SkewVol

open NumberField.InfinitePlace

def cxPlaceEquiv (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] :
    {w : InfinitePlace E // IsComplex w} ≃ InfinitePlace E :=
  Equiv.subtypeUnivEquiv fun w => IsTotallyComplex.isComplex w

def mixedCoords (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] :
    mixedEmbedding.mixedSpace E ≃ₗ[ℝ] ((InfinitePlace E → ℝ) × (InfinitePlace E → ℝ)) where
  toFun x := (fun w => (x.2 ⟨w, IsTotallyComplex.isComplex w⟩).re,
    fun w => (x.2 ⟨w, IsTotallyComplex.isComplex w⟩).im)
  invFun y := (fun w => absurd w.2 (not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w.1)),
    fun w => ⟨y.1 w.1, y.2 w.1⟩)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp
  left_inv x := by
    refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
    · exact absurd w.2 (not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w.1))
    · apply Complex.ext <;> rfl
  right_inv y := rfl

private theorem measurePreserving_mixedSpace_snd (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] :
    MeasurePreserving (Prod.snd : mixedEmbedding.mixedSpace E → ({w : InfinitePlace E // IsComplex w} → ℂ))
      volume volume := by
  have : IsEmpty {w : InfinitePlace E // IsReal w} :=
    ⟨fun w => not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w.1) w.2⟩
  have h : (volume : Measure ({w : InfinitePlace E // IsReal w} → ℝ)) = Measure.dirac 0 := by
    rw [MeasureTheory.volume_pi, Measure.pi_of_empty]
    congr 1
    exact Subsingleton.elim _ _
  refine ⟨measurable_snd, ?_⟩
  show Measure.map Prod.snd ((volume : Measure ({w : InfinitePlace E // IsReal w} → ℝ)).prod volume) = volume
  rw [h, Measure.map_snd_prod]
  simp

theorem measurePreserving_mixedCoords (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] :
    MeasurePreserving (mixedCoords E) volume volume := by
  have h2 := measurePreserving_piCongrLeft (fun _ : InfinitePlace E => (volume : Measure ℂ))
    (cxPlaceEquiv E)
  have h3 := measurePreserving_pi (fun _ : InfinitePlace E => (volume : Measure ℂ))
    (fun _ => (volume : Measure (ℝ × ℝ))) (fun _ => Complex.volume_preserving_equiv_real_prod)
  have h4 := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (InfinitePlace E)
    (fun _ => (volume : Measure ℝ)) (fun _ => (volume : Measure ℝ))
  have key := h4.comp (h3.comp (h2.comp (measurePreserving_mixedSpace_snd E)))
  have e : (⇑(mixedCoords E)) = ⇑(MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (InfinitePlace E)) ∘
      (fun a i => Complex.measurableEquivRealProd (a i)) ∘
        ⇑(MeasurableEquiv.piCongrLeft (fun _ => ℂ) (cxPlaceEquiv E)) ∘ Prod.snd := by
    funext x
    ext w <;> rfl
  rw [e]
  exact key

theorem mixedCoords_mixedEmbedding (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]
    (x : E) : mixedCoords E (mixedEmbedding E x) = (reV x, imV x) := by
  ext w <;> simp [mixedCoords, reV, imV, mixedEmbedding.mixedEmbedding_apply_isComplex]

theorem mixedSpace_reIm_coords : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E →
    ∃ e : mixedEmbedding.mixedSpace E ≃L[ℝ] ((InfinitePlace E → ℝ) × (InfinitePlace E → ℝ)),
      MeasurePreserving e volume volume ∧ ∀ x : E, e (mixedEmbedding E x) = (reV x, imV x) := by
  intro E _ _ hE
  have := hE
  exact ⟨(mixedCoords E).toContinuousLinearEquiv, by
    simpa using measurePreserving_mixedCoords E, fun x => by
    simpa using mixedCoords_mixedEmbedding E x⟩

end GlobalTheory.SnMass.SkewVol
end
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN

theorem existsUnique_layered_fundamentalDomain :
    ∀ {G X B : Type} [Group G] [Finite B] {V : B → Type} [∀ β, AddCommGroup (V β)] (ρ : G → X → X) (NN : Set X) (o : X) (deg : B → ℕ) (c : ∀ β, X → V β) (L D : ∀ β, Set (V β)), o ∈ NN → (∀ x, ρ 1 x = x) → (∀ g h x, ρ (g * h) x = ρ g (ρ h x)) → (∀ g, ∀ x ∈ NN, ρ g x ∈ NN) → (∀ β, (0 : V β) ∈ L β) → (∀ β v, ∃! l, l ∈ L β ∧ v + l ∈ D β) → (∀ β, c β o = 0) → (∀ (d : ℕ) (g : G), (∀ β, deg β < d → c β (ρ g o) = 0) → ∀ x ∈ NN, ∀ β, deg β ≤ d → c β (ρ g x) = c β x + c β (ρ g o)) → (∀ (g : G) (β : B), (∀ β', deg β' < deg β → c β' (ρ g o) = 0) → c β (ρ g o) ∈ L β) → (∀ β, ∀ l ∈ L β, ∃ g : G, c β (ρ g o) = l ∧ ∀ β', β' ≠ β → deg β' ≤ deg β → c β' (ρ g o) = 0) → (∀ g : G, (∀ β, c β (ρ g o) = 0) → g = 1) → ∀ x ∈ NN, ∃! g : G, ∀ β, c β (ρ g x) ∈ D β := by
  intro G X B _ _ V _ ρ NN o deg c L D ho h1 hmul hst hL0 hD hco htr hL hon hinj x hx
  classical
  haveI := Fintype.ofFinite B
  have hgx : ∀ (g : G) (y : X), y ∈ NN → ρ g y ∈ NN := fun g y hy => hst g y hy

  have step : ∀ (d : ℕ) (T : Finset B), (∀ β ∈ T, deg β = d) →
      (∃ g : G, ∀ β, deg β < d → c β (ρ g x) ∈ D β) →
      ∃ g : G, ∀ β, (deg β < d ∨ β ∈ T) → c β (ρ g x) ∈ D β := by
    intro d T
    induction T using Finset.induction_on with
    | empty =>
      intro _ ⟨g, hg⟩
      refine ⟨g, fun β hβ => ?_⟩
      rcases hβ with hβ | hβ
      · exact hg β hβ
      · simp at hβ
    | insert b T hb ih =>
      intro hT h0
      obtain ⟨g, hg⟩ := ih (fun β hβ => hT β (Finset.mem_insert_of_mem hβ)) h0
      have hbd : deg b = d := hT b (Finset.mem_insert_self b T)
      obtain ⟨l, ⟨hlL, hlD⟩, -⟩ := hD b (c b (ρ g x))
      obtain ⟨h, hhl, hh0⟩ := hon b l hlL
      have hlow : ∀ β, deg β < d → c β (ρ h o) = 0 := fun β hβ =>
        hh0 β (fun e => by subst e; omega) (by omega)
      have htrans := htr d h hlow (ρ g x) (hgx g x hx)
      refine ⟨h * g, fun β hβ => ?_⟩
      rw [hmul]
      by_cases hβb : β = b
      · subst hβb
        rw [htrans β (by omega), hhl]
        exact hlD
      · have hle : deg β ≤ d := by
          rcases hβ with hβ | hβ
          · omega
          · exact (hT β hβ).le
        have hold : deg β < d ∨ β ∈ T := by
          rcases hβ with hβ | hβ
          · exact Or.inl hβ
          · exact Or.inr ((Finset.mem_insert.mp hβ).resolve_left hβb)
        rw [htrans β hle, hh0 β hβb (by omega), add_zero]
        exact hg β hold
  have exD : ∀ d : ℕ, ∃ g : G, ∀ β, deg β < d → c β (ρ g x) ∈ D β := by
    intro d
    induction d with
    | zero => exact ⟨1, fun β hβ => absurd hβ (Nat.not_lt_zero _)⟩
    | succ d ih =>
      obtain ⟨g, hg⟩ := step d (Finset.univ.filter (fun β => deg β = d))
        (fun β hβ => (Finset.mem_filter.mp hβ).2) ih
      refine ⟨g, fun β hβ => hg β ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hβ with h | h
      · exact Or.inl h
      · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  obtain ⟨M, hM⟩ := (Set.finite_range deg).bddAbove
  obtain ⟨g₀, hg₀⟩ := exD (M + 1)
  refine ⟨g₀, fun β => hg₀ β (Nat.lt_succ_of_le (hM ⟨β, rfl⟩)), ?_⟩

  intro g₂ hg₂
  have hg₁ : ∀ β, c β (ρ g₀ x) ∈ D β := fun β => hg₀ β (Nat.lt_succ_of_le (hM ⟨β, rfl⟩))
  have hy : ρ g₀ x ∈ NN := hgx g₀ x hx
  have hδy : ρ (g₂ * g₀⁻¹) (ρ g₀ x) = ρ g₂ x := by
    rw [← hmul, inv_mul_cancel_right]
  have vanish : ∀ d : ℕ, ∀ β, deg β < d → c β (ρ (g₂ * g₀⁻¹) o) = 0 := by
    intro d
    induction d with
    | zero => exact fun β hβ => absurd hβ (Nat.not_lt_zero _)
    | succ d ih =>
      intro β hβ
      rcases Nat.lt_succ_iff_lt_or_eq.mp hβ with h | h
      · exact ih β h
      · have hin : c β (ρ (g₂ * g₀⁻¹) o) ∈ L β := hL _ β (fun β' hβ' => ih β' (by omega))
        have hadd := htr d (g₂ * g₀⁻¹) ih (ρ g₀ x) hy β h.le
        rw [hδy] at hadd
        have hmem : c β (ρ g₀ x) + c β (ρ (g₂ * g₀⁻¹) o) ∈ D β := hadd ▸ hg₂ β
        have hzero : c β (ρ g₀ x) + 0 ∈ D β := by simpa using hg₁ β
        exact (hD β (c β (ρ g₀ x))).unique ⟨hin, hmem⟩ ⟨hL0 β, hzero⟩
  have hone : g₂ * g₀⁻¹ = 1 :=
    hinj _ (fun β => vanish (M + 1) β (Nat.lt_succ_of_le (hM ⟨β, rfl⟩)))
  exact mul_inv_eq_one.mp hone

end GlobalTheory.SnMass.VolN
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN

theorem strictFD_measure_eq_tsum {G X : Type} [Countable G] [MeasurableSpace X]
    (μ : Measure X) (ρ : G → X → X) (NN D D' : Set X) (hNN : MeasurableSet NN)
    (hnull : μ NNᶜ = 0) (hD : MeasurableSet D) (hD' : MeasurableSet D')
    (hmeas : ∀ g, Measurable (ρ g)) (hu' : ∀ x ∈ NN, ∃! g : G, ρ g x ∈ D') :
    μ D = ∑' g, μ (D ∩ NN ∩ (ρ g)⁻¹' D') := by
  have h1 : μ D = μ (D ∩ NN) := by
    rw [← measure_inter_add_diff D hNN]
    have : μ (D \ NN) = 0 := measure_mono_null (fun x hx => hx.2) hnull
    rw [this, add_zero]
  rw [h1]
  have hU : D ∩ NN = ⋃ g, D ∩ NN ∩ (ρ g)⁻¹' D' := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨hxD, hxN⟩
      obtain ⟨g, hg, -⟩ := hu' x hxN
      exact ⟨g, ⟨hxD, hxN⟩, hg⟩
    · rintro ⟨g, ⟨hxD, hxN⟩, -⟩
      exact ⟨hxD, hxN⟩
  conv_lhs => rw [hU]
  apply measure_iUnion
  · intro g h hgh
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨⟨-, hxN⟩, hg⟩ ⟨⟨-, -⟩, hh⟩
    exact hgh ((hu' x hxN).unique hg hh)
  · intro g
    exact (hD.inter hNN).inter (hmeas g hD')

theorem strictFD_measure_eq {G X : Type} [Group G] [Countable G] [MeasurableSpace X]
    (μ : Measure X) (ρ : G → X → X) (NN D D' : Set X) (hNN : MeasurableSet NN)
    (hnull : μ NNᶜ = 0) (hD : MeasurableSet D) (hD' : MeasurableSet D')
    (hone : ∀ x, ρ 1 x = x) (hmul : ∀ g h x, ρ (g * h) x = ρ g (ρ h x))
    (hinv : ∀ g, ∀ x ∈ NN, ρ g x ∈ NN) (hmp : ∀ g, MeasurePreserving (ρ g) μ μ)
    (hu : ∀ x ∈ NN, ∃! g : G, ρ g x ∈ D) (hu' : ∀ x ∈ NN, ∃! g : G, ρ g x ∈ D') :
    μ D = μ D' := by
  have hmeas : ∀ g, Measurable (ρ g) := fun g => (hmp g).measurable
  rw [strictFD_measure_eq_tsum μ ρ NN D D' hNN hnull hD hD' hmeas hu',
    strictFD_measure_eq_tsum μ ρ NN D' D hNN hnull hD' hD hmeas hu]
  conv_rhs => rw [← (Equiv.inv G).tsum_eq]
  refine tsum_congr fun g => ?_
  simp only [Equiv.inv_apply]
  have hS : MeasurableSet (D' ∩ NN ∩ (ρ g⁻¹)⁻¹' D) :=
    (hD'.inter hNN).inter (hmeas g⁻¹ hD)
  rw [← (hmp g).measure_preimage hS.nullMeasurableSet]
  congr 1
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage]
  have hx : ρ g⁻¹ (ρ g x) = x := by rw [← hmul, inv_mul_cancel, hone]
  rw [hx]
  constructor
  · rintro ⟨⟨hxD, hxN⟩, hgx⟩
    exact ⟨⟨hgx, hinv g x hxN⟩, hxD⟩
  · rintro ⟨⟨hgx, hgxN⟩, hxD⟩
    refine ⟨⟨hxD, ?_⟩, hgx⟩
    have := hinv g⁻¹ _ hgxN
    rwa [hx] at this

end GlobalTheory.SnMass.VolN
end

section

open MeasureTheory

namespace GlobalTheory.NMKProd

theorem lintegral_nmk {H : Type} [Mul H] [MeasurableSpace H] [MeasurableMul₂ H]
    (a b k : Measure H) [SFinite a] [SFinite b] [SFinite k] (d : H → ENNReal) (hd : Measurable d)
    (φ : H → ENNReal) (hφ : Measurable φ) :
    ∫⁻ g, φ g ∂(((a.prod (b.prod k)).withDensity fun x => d x.2.1).map
        fun x : H × H × H => x.1 * x.2.1 * x.2.2) =
      ∫⁻ u, ∫⁻ m, d m * ∫⁻ z, φ (u * m * z) ∂k ∂b ∂a := by
  have hmul : Measurable (fun x : H × H × H => x.1 * x.2.1 * x.2.2) :=
    (measurable_fst.mul measurable_snd.fst).mul measurable_snd.snd
  have hD : Measurable (fun x : H × H × H => d x.2.1) := hd.comp measurable_snd.fst
  have hφm : Measurable (fun x : H × H × H => φ (x.1 * x.2.1 * x.2.2)) := hφ.comp hmul
  rw [lintegral_map hφ hmul, lintegral_withDensity_eq_lintegral_mul _ hD hφm,
    lintegral_prod _ (hD.mul hφm).aemeasurable]
  refine lintegral_congr fun u => ?_
  have hin : Measurable (fun y : H × H => d y.1 * φ (u * y.1 * y.2)) :=
    (hd.comp measurable_fst).mul (hφ.comp ((measurable_const.mul measurable_fst).mul measurable_snd))
  simp only [Pi.mul_apply]
  rw [lintegral_prod _ hin.aemeasurable]
  refine lintegral_congr fun m => ?_
  have hz : Measurable (fun z : H => φ (u * m * z)) := hφ.comp (measurable_id.const_mul (u * m))
  exact lintegral_const_mul (d m) hz

private lemma indicator_pi_univ_eq_prod {ι : Type} [Fintype ι] {G : ι → Type} (s : ∀ i, Set (G i))
    (x : ∀ i, G i) :
    (Set.univ.pi s).indicator (1 : (∀ i, G i) → ENNReal) x =
      ∏ i, (s i).indicator (1 : G i → ENNReal) (x i) := by
  by_cases hx : x ∈ Set.univ.pi s
  · rw [Set.indicator_of_mem hx]
    rw [Set.mem_univ_pi] at hx
    simp [Set.indicator_of_mem (hx _)]
  · rw [Set.indicator_of_notMem hx]
    rw [Set.mem_univ_pi, not_forall] at hx
    obtain ⟨i, hi⟩ := hx
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm

theorem prod_formula : ∀ (ι : Type) [Fintype ι] (G : ι → Type) [∀ i, Group (G i)] [∀ i, MeasurableSpace (G i)] [∀ i, MeasurableMul₂ (G i)] (μ μN μM μK : ∀ i, Measure (G i)) [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (μN i)] [∀ i, SigmaFinite (μM i)] [∀ i, SigmaFinite (μK i)] (C c : ι → ENNReal) (δ : ∀ i, G i → ENNReal), (∀ i, C i ≠ 0) → (∀ i, C i ≠ ⊤) → (∀ i, Measurable (δ i)) → (∀ i, ∀ φ : G i → ENNReal, Measurable φ → C i * ∫⁻ g, φ g ∂(μ i) = c i * ∫⁻ u, ∫⁻ m, δ i m * ∫⁻ k, φ (u * m * k) ∂(μK i) ∂(μM i) ∂(μN i)) → ∀ φ : (∀ i, G i) → ENNReal, Measurable φ → (∏ i, C i) * ∫⁻ g, φ g ∂(Measure.pi μ) = (∏ i, c i) * ∫⁻ u, ∫⁻ m, (∏ i, δ i (m i)) * ∫⁻ k, φ (u * m * k) ∂(Measure.pi μK) ∂(Measure.pi μM) ∂(Measure.pi μN) := by
  intro ι _ G _ _ _ μ μN μM μK _ _ _ _ C c δ hC0 hCt hδ hrel φ hφ
  have hD : Measurable (fun m : ∀ i, G i => ∏ i, δ i (m i)) :=
    Finset.measurable_prod _ (fun i _ => (hδ i).comp (measurable_pi_apply i))
  have key := fun (ψ : (∀ i, G i) → ENNReal) (hψ : Measurable ψ) =>
    lintegral_nmk (Measure.pi μN) (Measure.pi μM) (Measure.pi μK)
      (fun m : ∀ i, G i => ∏ i, δ i (m i)) hD ψ hψ
  set R0 := (((Measure.pi μN).prod ((Measure.pi μM).prod (Measure.pi μK))).withDensity
      fun x => ∏ i, δ i (x.2.1 i)).map
    (fun x : (∀ i, G i) × (∀ i, G i) × (∀ i, G i) => x.1 * x.2.1 * x.2.2) with hR0
  have hC0' : (∏ i, C i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hC0 i
  have hCt' : (∏ i, C i) ≠ ⊤ := ENNReal.prod_ne_top fun i _ => hCt i
  have hpi : Measure.pi μ = (∏ i, C i)⁻¹ • ((∏ i, c i) • R0) := by
    refine Measure.pi_eq fun s hs => ?_
    have hX : ∀ i, C i * μ i (s i) = c i * ∫⁻ u, ∫⁻ m, δ i m *
        ∫⁻ k, (s i).indicator 1 (u * m * k) ∂(μK i) ∂(μM i) ∂(μN i) := by
      intro i
      have h := hrel i ((s i).indicator 1) (measurable_one.indicator (hs i))
      rwa [lintegral_indicator_one (hs i)] at h
    have hbox : R0 (Set.univ.pi s) = ∏ i, ∫⁻ u, ∫⁻ m, δ i m *
        ∫⁻ k, (s i).indicator 1 (u * m * k) ∂(μK i) ∂(μM i) ∂(μN i) := by
      rw [← lintegral_indicator_one (MeasurableSet.univ_pi hs),
        key _ (measurable_one.indicator (MeasurableSet.univ_pi hs))]
      have hK : ∀ u m : ∀ i, G i, ∫⁻ k, (Set.univ.pi s).indicator 1 (u * m * k) ∂(Measure.pi μK) =
          ∏ i, ∫⁻ k, (s i).indicator 1 (u i * m i * k) ∂(μK i) := by
        intro u m
        simp_rw [indicator_pi_univ_eq_prod]
        exact GlobalTheory.SnMass.Push.lintegral_fintype_prod (fun i k => (s i).indicator 1 (u i * m i * k))
          (fun i => (measurable_one.indicator (hs i)).comp (measurable_const.mul measurable_id))
      have hA : ∀ i (u' : G i), Measurable (fun m' : G i =>
          δ i m' * ∫⁻ k, (s i).indicator 1 (u' * m' * k) ∂(μK i)) := by
        intro i u'
        refine (hδ i).mul ?_
        exact Measurable.lintegral_prod_right' (f := fun y : G i × G i => (s i).indicator 1 (u' * y.1 * y.2))
          ((measurable_one.indicator (hs i)).comp ((measurable_const.mul measurable_fst).mul measurable_snd))
      have hB : ∀ i, Measurable (fun u' : G i => ∫⁻ m', δ i m' *
          ∫⁻ k, (s i).indicator 1 (u' * m' * k) ∂(μK i) ∂(μM i)) := by
        intro i
        refine Measurable.lintegral_prod_right' (f := fun y : G i × G i =>
          δ i y.2 * ∫⁻ k, (s i).indicator 1 (y.1 * y.2 * k) ∂(μK i)) ?_
        refine ((hδ i).comp measurable_snd).mul ?_
        exact Measurable.lintegral_prod_right' (f := fun z : (G i × G i) × G i =>
            (s i).indicator 1 (z.1.1 * z.1.2 * z.2))
          ((measurable_one.indicator (hs i)).comp
            ((measurable_fst.fst.mul measurable_fst.snd).mul measurable_snd))
      have hM : ∀ u : ∀ i, G i, ∫⁻ m, (∏ i, δ i (m i)) *
          ∫⁻ k, (Set.univ.pi s).indicator 1 (u * m * k) ∂(Measure.pi μK) ∂(Measure.pi μM) =
          ∏ i, ∫⁻ m', δ i m' * ∫⁻ k, (s i).indicator 1 (u i * m' * k) ∂(μK i) ∂(μM i) := by
        intro u
        simp_rw [hK u, ← Finset.prod_mul_distrib]
        exact GlobalTheory.SnMass.Push.lintegral_fintype_prod
          (fun i m' => δ i m' * ∫⁻ k, (s i).indicator 1 (u i * m' * k) ∂(μK i)) (fun i => hA i (u i))
      simp_rw [hM]
      exact GlobalTheory.SnMass.Push.lintegral_fintype_prod _ hB
    simp only [Measure.smul_apply, smul_eq_mul]
    rw [hbox, ← Finset.prod_mul_distrib, Finset.prod_congr rfl fun i _ => (hX i).symm,
      Finset.prod_mul_distrib, ← mul_assoc, ENNReal.inv_mul_cancel hC0' hCt', one_mul]
  rw [hpi, lintegral_smul_measure, lintegral_smul_measure, smul_eq_mul, smul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel hC0' hCt', one_mul, hR0]
  exact congrArg ((∏ i, c i) * ·) (key φ hφ)

end GlobalTheory.NMKProd
end

end

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

theorem _root_.GlobalTheory.T.exists_mixedSpace_reIm_coords_totallyComplex : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∃ e : mixedEmbedding.mixedSpace E ≃L[ℝ] ((InfinitePlace E → ℝ) × (InfinitePlace E → ℝ)), MeasurePreserving e volume volume ∧ ∀ x : E, e (mixedEmbedding E x) = (reV x, imV x) := by
  first | exact @GlobalTheory.SnMass.SkewVol.mixedSpace_reIm_coords | exact GlobalTheory.SnMass.SkewVol.mixedSpace_reIm_coords | (intros; apply GlobalTheory.SnMass.SkewVol.mixedSpace_reIm_coords <;> assumption)

end
end

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

theorem _root_.GlobalTheory.T.existsUnique_layered_strictFundamentalDomain : ∀ {G X B : Type} [Group G] [Finite B] {V : B → Type} [∀ β, AddCommGroup (V β)] (ρ : G → X → X) (NN : Set X) (o : X) (deg : B → ℕ) (c : ∀ β, X → V β) (L D : ∀ β, Set (V β)), o ∈ NN → (∀ x, ρ 1 x = x) → (∀ g h x, ρ (g * h) x = ρ g (ρ h x)) → (∀ g, ∀ x ∈ NN, ρ g x ∈ NN) → (∀ β, (0 : V β) ∈ L β) → (∀ β v, ∃! l, l ∈ L β ∧ v + l ∈ D β) → (∀ β, c β o = 0) → (∀ (d : ℕ) (g : G), (∀ β, deg β < d → c β (ρ g o) = 0) → ∀ x ∈ NN, ∀ β, deg β ≤ d → c β (ρ g x) = c β x + c β (ρ g o)) → (∀ (g : G) (β : B), (∀ β', deg β' < deg β → c β' (ρ g o) = 0) → c β (ρ g o) ∈ L β) → (∀ β, ∀ l ∈ L β, ∃ g : G, c β (ρ g o) = l ∧ ∀ β', β' ≠ β → deg β' ≤ deg β → c β' (ρ g o) = 0) → (∀ g : G, (∀ β, c β (ρ g o) = 0) → g = 1) → ∀ x ∈ NN, ∃! g : G, ∀ β, c β (ρ g x) ∈ D β := by
  first | exact @GlobalTheory.SnMass.VolN.existsUnique_layered_fundamentalDomain | exact GlobalTheory.SnMass.VolN.existsUnique_layered_fundamentalDomain | (intros; apply GlobalTheory.SnMass.VolN.existsUnique_layered_fundamentalDomain <;> assumption)

end
end

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

theorem _root_.GlobalTheory.T.strictFundamentalDomain_measure_eq : ∀ {G X : Type} [Group G] [Countable G] [MeasurableSpace X] (μ : Measure X) (ρ : G → X → X) (NN D D' : Set X), MeasurableSet NN → μ NNᶜ = 0 → MeasurableSet D → MeasurableSet D' → (∀ x, ρ 1 x = x) → (∀ g h x, ρ (g * h) x = ρ g (ρ h x)) → (∀ g, ∀ x ∈ NN, ρ g x ∈ NN) → (∀ g, MeasurePreserving (ρ g) μ μ) → (∀ x ∈ NN, ∃! g : G, ρ g x ∈ D) → (∀ x ∈ NN, ∃! g : G, ρ g x ∈ D') → μ D = μ D' := by
  first | exact @GlobalTheory.SnMass.VolN.strictFD_measure_eq | exact GlobalTheory.SnMass.VolN.strictFD_measure_eq | (intros; apply GlobalTheory.SnMass.VolN.strictFD_measure_eq <;> assumption)

end
end
