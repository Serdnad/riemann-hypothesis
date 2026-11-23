module

import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthFunctionFactsHold
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QdetTopThreeOrders
public import Development.AutomorphicSpectrum.Proofs.HermitianForms.CasOfCapelliVec
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import GroundTheory.AutomorphicForms.SmoothRep
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import GroundTheory.AutomorphicForms.InductionParabolic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusCharacterLevi
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle209
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle158
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle208
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.GroupTheory.ArchimedeanDensely
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle216
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.AltSum
import GroundTheory.AutomorphicForms.Bundle003
import GroundTheory.GlobalFields.KummerTheory.LocalIndex
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle214
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.NeutralLocalFields.Bundle001
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower

@[expose] public section

section

open MeasureTheory Matrix Finset
open scoped ContDiff
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.SobGL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.SobGL

def lgArg {n : ℕ} (p : Mat n × Mat n) : ℝ :=
  1 + ∑ a, ∑ b, (‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2)

theorem lgArg_continuous {n : ℕ} : Continuous (lgArg (n := n)) := by
  unfold lgArg
  refine continuous_const.add (continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_)
  have h1 : Continuous fun p : Mat n × Mat n => p.1 a b :=
    (continuous_id.matrix_elem a b).comp continuous_fst
  have h2 : Continuous fun p : Mat n × Mat n => p.2 a b :=
    (continuous_id.matrix_elem a b).comp continuous_snd
  exact (h1.norm.pow 2).add (h2.norm.pow 2)

theorem one_le_lgArg {n : ℕ} (p : Mat n × Mat n) : 1 ≤ lgArg p := by
  unfold lgArg
  have : 0 ≤ ∑ a, ∑ b, (‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2) :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by positivity
  linarith

theorem entry_sq_le_lgArg {n : ℕ} (p : Mat n × Mat n) (a b : Fin n) :
    ‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2 ≤ lgArg p := by
  unfold lgArg
  have h1 : ‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2 ≤ ∑ b, (‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2) :=
    Finset.single_le_sum (f := fun b => ‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2)
      (fun b _ => by positivity) (Finset.mem_univ b)
  have h2 : ∑ b, (‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2) ≤ ∑ a, ∑ b, (‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2) :=
    Finset.single_le_sum (f := fun a => ∑ b, (‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2))
      (fun a _ => Finset.sum_nonneg fun b _ => by positivity) (Finset.mem_univ a)
  linarith

theorem lg_eq_log_lgArg {n : ℕ} (y : Mat n) : lg y = Real.log (lgArg (y, y⁻¹)) := rfl

theorem continuousOn_matInv {n : ℕ} : ContinuousOn (fun y : Mat n => y⁻¹) (GLs n) := by
  have hdet : ContinuousOn (fun y : Mat n => (y.det)⁻¹) (GLs n) :=
    (continuous_id.matrix_det).continuousOn.inv₀ fun y hy => hy
  have hadj : Continuous fun y : Mat n => y.adjugate := continuous_id.matrix_adjugate
  have : (fun y : Mat n => y⁻¹) = fun y => (y.det)⁻¹ • y.adjugate := by
    funext y
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [this]
  exact hdet.smul hadj.continuousOn

theorem continuousOn_lg {n : ℕ} : ContinuousOn (lg (n := n)) (GLs n) := by
  have hp : ContinuousOn (fun y : Mat n => (y, y⁻¹)) (GLs n) :=
    continuousOn_id.prodMk continuousOn_matInv
  have h := lgArg_continuous.comp_continuousOn hp
  exact ContinuousOn.log h fun y _ => (lt_of_lt_of_le one_pos (one_le_lgArg (y, y⁻¹))).ne'

def pairOf {n : ℕ} (y : G n) : Mat n × Mat n := (y.val, (y⁻¹ : G n).val)

theorem pairOf_isInducing {n : ℕ} : Topology.IsInducing (pairOf (n := n)) := by
  have h := (Units.isEmbedding_embedProduct (M := Mat n)).isInducing
  have h2 : Topology.IsInducing (fun p : Mat n × (Mat n)ᵐᵒᵖ => (p.1, p.2.unop)) :=
    ((Homeomorph.refl (Mat n)).prodCongr MulOpposite.opHomeomorph.symm).isInducing
  exact h2.comp h

theorem isCompact_entryBox {n : ℕ} (r : ℝ) : IsCompact {m : Mat n | ∀ a b, ‖m a b‖ ≤ r} := by
  have h : IsCompact (Set.pi Set.univ fun _ : Fin n =>
      Set.pi Set.univ fun _ : Fin n => Metric.closedBall (0 : ℂ) r) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have e : {m : Fin n → Fin n → ℂ | ∀ a b, ‖m a b‖ ≤ r} = Set.pi Set.univ fun _ : Fin n =>
      Set.pi Set.univ fun _ : Fin n => Metric.closedBall (0 : ℂ) r := by
    ext m
    simp [Set.mem_pi]
  have h' : IsCompact {m : Fin n → Fin n → ℂ | ∀ a b, ‖m a b‖ ≤ r} := e ▸ h
  exact h'

theorem isCompact_lg_le {n : ℕ} (R : ℝ) : IsCompact {y : G n | lg y.val ≤ R} := by
  apply GlobalTheory.CompanionTheory.LengthGL.isCompact_G <;> assumption

theorem lg_continuousOn_and_isCompact :
    ∀ n : ℕ, ContinuousOn (lg (n := n)) (GLs n) ∧ ∀ R : ℝ, IsCompact {y : G n | lg y.val ≤ R} :=
  fun _ => ⟨continuousOn_lg, isCompact_lg_le⟩

end GlobalTheory.CompanionTheory.SobGL
end
end

section

set_option maxSynthPendingDepth 1
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.Inh.CapelliCasimir
open Finset

theorem mem_subalgebra_of_dual {A : Type} [Ring A] [Algebra ℂ A] (S : Subalgebra ℂ A) (x : A)
    (h : ∀ f : A →ₗ[ℂ] ℂ, (∀ z ∈ S, f z = 0) → f x = 0) : x ∈ S := by
  by_contra hx
  have hx' : x ∉ Subalgebra.toSubmodule S := hx
  obtain ⟨f, hf1, hf2⟩ := Submodule.exists_le_ker_of_notMem hx'
  exact hf1 (h f fun z hz => LinearMap.mem_ker.1 (hf2 hz))

theorem cas_mem_of_qdet_mem {A : Type} [Ring A] [Algebra ℂ A] (S : Subalgebra ℂ A) (n : ℕ)
    (E : Fin n → Fin n → A) (hE : Formalism.REAL.GlRel E)
    (hcap : ∀ Y : ℂ, Formalism.REAL.qdet E (Y + ((n : ℂ) - 1) / 2) ∈ S) : Formalism.REAL.Cas E ∈ S := by
  obtain ⟨Rm, hR⟩ := _root_.GlobalTheory.qdet_top_three_orders A n E
  by_cases hn : 2 ≤ n
  swap
  · have hn' : n = 0 ∨ n = 1 := by omega
    rcases hn' with rfl | rfl
    · simp [Formalism.REAL.Cas]
    · have h0 := hcap 0
      rw [hR] at h0
      have h1 : E 0 0 ∈ S := by
        simpa [Finset.filter_singleton] using h0
      have : Formalism.REAL.Cas E = E 0 0 * E 0 0 := by simp [Formalism.REAL.Cas]
      rw [this]
      exact Subalgebra.mul_mem _ h1 h1
  set ρ : Fin n → ℂ := fun l => ((n : ℂ) - 1) / 2 - ((l : ℕ) : ℂ) with hρ
  have hρ0 : ∑ l, ρ l = 0 := by
    have h1 : ∑ l, ρ l = ∑ l, ρ (Fin.rev l) := (Equiv.sum_comp Fin.revPerm ρ).symm
    have h2 : ∑ l, ρ (Fin.rev l) = - ∑ l, ρ l := by
      rw [← sum_neg_distrib]
      refine sum_congr rfl fun l _ => ?_
      have := l.2
      simp only [hρ, Fin.val_rev]
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    linear_combination (h1.trans h2) / 2
  have core := fun (f : A →ₗ[ℂ] ℂ) (hf : ∀ z ∈ S, f z = 0) =>
    scalar_core n hn ρ (fun _ => 0) (fun i => f (E i i))
      (fun i j => f (E i i * E j j - E j i * E i j)) (fun d => f (Rm d)) (f 1)
      (((n : ℂ) - 1) / 2)
      (fun Y => by
        have h1 := hf _ (hcap Y)
        rw [hR] at h1
        have e : f 1 = 0 := hf 1 (Subalgebra.one_mem _)

        simp only [map_add (f := _), map_sum, map_smul, smul_eq_mul, add_sub_assoc] at h1
        simp only [e, mul_zero] at h1 ⊢
        exact h1)
  have hT : ∑ i, E i i ∈ S := by
    refine mem_subalgebra_of_dual S _ fun f hf => ?_
    have e : f 1 = 0 := hf 1 (Subalgebra.one_mem _)
    have := (core f hf).1
    rw [hρ0, e] at this

    simp only [map_sum]
    linear_combination this
  have hW : (2 : ℂ) • ∑ i, ∑ j ∈ univ.filter (fun j => i < j), (E i i * E j j - E j i * E i j)
        - ∑ i : Fin n, ((n : ℂ) - 1 - 2 * (i : ℕ)) • E i i ∈ S := by
    refine mem_subalgebra_of_dual S _ fun f hf => ?_
    have e : f 1 = 0 := hf 1 (Subalgebra.one_mem _)
    have h2 := (core f hf).2
    rw [e] at h2
    simp only [sum_erase_eq_sub (mem_univ _), hρ0] at h2

    simp only [map_sub f, map_sum, map_smul, smul_eq_mul]
    have h5 : ∑ i : Fin n, ((n : ℂ) - 1 - 2 * (i : ℕ)) * f (E i i)
        = - (2 * ∑ i, (0 - ρ i) * f (E i i)) := by
      rw [mul_sum, ← sum_neg_distrib]
      refine sum_congr rfl fun i _ => ?_
      simp only [hρ]; ring
    rw [h5]
    simp only [map_sub f] at h2
    linear_combination h2
  have h3 := sq_sub_cas E hE
  have : Formalism.REAL.Cas E = (∑ i, E i i) * (∑ i, E i i)
      - ((2 : ℂ) • ∑ i, ∑ j ∈ univ.filter (fun j => i < j), (E i i * E j j - E j i * E i j)
        - ∑ i : Fin n, ((n : ℂ) - 1 - 2 * (i : ℕ)) • E i i) := by
    rw [← h3]; abel
  rw [this]
  exact Subalgebra.sub_mem _ (Subalgebra.mul_mem _ hT hT) hW

theorem cas_mem_Zalg : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (τ : E →+* ℂ),
    Formalism.REAL.Cas (Eop (a := a) τ) ∈ Zalg E a := by
  intro F _ _ _ n τ
  have hcap : ∀ Y : ℂ, cap (a := n) τ Y ∈ Zalg F n := fun Y =>
    Algebra.subset_adjoin (show cap (a := n) τ Y ∈ {z | ∃ τ u, z = cap τ u} from ⟨τ, Y, rfl⟩)
  exact cas_mem_of_qdet_mem (Zalg F n) n (Eop τ) (glRel_Eop τ) hcap

end GlobalTheory.CompanionTheory.Inh.CapelliCasimir
end

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal
open scoped Classical

theorem _root_.GlobalTheory.T.unique_embedding_extension : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
      GlobalTheory.Pst.Induces Bw → ∀ (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1),
      ∃! j : {j : w.adicCompletion E →+* Qbar l // Continuous j},
        IsInduced Bw (j.1.comp (algebraMap E (w.adicCompletion E))) τ' := by
  first | exact @GlobalTheory.CompanionTheory.EmbUniq.existsUnique_continuous_induced | exact GlobalTheory.CompanionTheory.EmbUniq.existsUnique_continuous_induced | (intros; apply GlobalTheory.CompanionTheory.EmbUniq.existsUnique_continuous_induced <;> assumption)
end
end

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical Topology

namespace GlobalTheory.CompanionTheory.EmbBridge

variable {E : Type} [Field E] [NumberField E] {l : ℕ} [Fact l.Prime]

theorem tendsto_pow_zero (w : HeightOneSpectrum (𝓞 E)) (x : w.adicCompletion E)
    (hx : Valued.v x < 1) : Filter.Tendsto (fun n : ℕ => x ^ n) Filter.atTop (𝓝 0) := by
  intro s hs
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hs
  have hpos : (MonoidWithZeroHom.ValueGroup₀.embedding γ.1) ≠ 0 := by simp
  have : ∃ n : ℕ, (Valued.v x) ^ n < MonoidWithZeroHom.ValueGroup₀.embedding γ.1 := by
    exact exists_pow_lt₀ hx (Units.mk0 _ hpos)
  obtain ⟨n, hn⟩ := this
  refine Filter.mem_map.2 (Filter.mem_atTop_sets.2 ⟨n, fun m hm => hγ ?_⟩)
  have e : Valued.v (x ^ m) < MonoidWithZeroHom.ValueGroup₀.embedding γ.1 := by
    rw [map_pow]
    exact (pow_le_pow_of_le_one zero_le' hx.le hm).trans_lt hn
  exact (Valuation.restrict_lt_iff_lt_embedding _).2 e

theorem norm_lt_one (w : HeightOneSpectrum (𝓞 E)) (φ : w.adicCompletion E →+* Om l) (hφ : Continuous φ)
    (x : w.adicCompletion E) (hx : Valued.v x < 1) : ‖φ x‖ < 1 := by
  have h1 : Filter.Tendsto (fun n : ℕ => φ x ^ n) Filter.atTop (𝓝 0) := by
    have := (hφ.tendsto 0).comp (tendsto_pow_zero w x hx)
    simpa [Function.comp_def, map_pow] using this
  by_contra hge
  have h2 : ∀ n : ℕ, 1 ≤ ‖φ x ^ n‖ := fun n => by
    rw [norm_pow]; exact one_le_pow₀ (not_lt.1 hge)
  have h3 := h1.norm
  rw [norm_zero] at h3
  have := ge_of_tendsto' h3 h2
  linarith

theorem v_le_one (w : HeightOneSpectrum (𝓞 E)) (φ : w.adicCompletion E →+* Om l) (hφ : Continuous φ)
    (x : w.adicCompletion E) (hx : ‖φ x‖ < 1) : Valued.v x ≤ 1 := by
  by_contra hgt
  have hgt' := not_le.1 hgt
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hgt'
  have h1 : Valued.v x⁻¹ < 1 := by
    rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hgt'
  have h2 := norm_lt_one w φ hφ _ h1
  rw [map_inv₀, norm_inv] at h2
  have hpos : 0 < ‖φ x‖ := norm_pos_iff.2 ((map_ne_zero φ).2 hx0)
  have := (one_lt_inv₀ hpos).2 hx
  linarith

theorem exists_v_lt_one (w : HeightOneSpectrum (𝓞 E)) :
    ∃ π : w.adicCompletion E, π ≠ 0 ∧ Valued.v π < 1 := by
  obtain ⟨y, hyw, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
  refine ⟨algebraMap E _ (y : E), ?_, ?_⟩
  · simpa using hy0
  · have h : w.valuation E (y : E) < 1 := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) w y).2 hyw
    have e : Valued.v (algebraMap E (w.adicCompletion E) (y : E)) = w.valuation E (y : E) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (y : E)
    rw [e]
    exact h

theorem isInducing (w : HeightOneSpectrum (𝓞 E)) (φ : w.adicCompletion E →+* Om l) (hφ : Continuous φ) :
    Topology.IsInducing φ := by
  rw [IsTopologicalAddGroup.isInducing_iff_nhds_zero]
  refine le_antisymm (by simpa using (hφ.tendsto 0).le_comap) ?_
  intro s hs
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hs
  obtain ⟨π, hπ0, hπ⟩ := exists_v_lt_one w
  have hpos : (MonoidWithZeroHom.ValueGroup₀.embedding γ.1) ≠ 0 := by simp
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (Valued.v π) ^ n < MonoidWithZeroHom.ValueGroup₀.embedding γ.1 :=
    exists_pow_lt₀ hπ (Units.mk0 _ hpos)
  have hε : 0 < ‖φ (π ^ n)‖ := norm_pos_iff.2 ((map_ne_zero φ).2 (pow_ne_zero n hπ0))
  refine Filter.mem_comap.2 ⟨Metric.ball 0 ‖φ (π ^ n)‖, Metric.ball_mem_nhds _ hε, fun x hx => hγ ?_⟩
  have hx' : ‖φ x‖ < ‖φ (π ^ n)‖ := by simpa using hx
  have h1 : ‖φ (x / π ^ n)‖ < 1 := by
    rw [map_div₀, norm_div]
    exact (div_lt_one hε).2 hx'
  have h2 := v_le_one w φ hφ _ h1
  have hv : 0 < Valued.v π ^ n := zero_lt_iff.2 (pow_ne_zero n ((Valuation.ne_zero_iff _).2 hπ0))
  rw [map_div₀, map_pow, div_le_one₀ hv] at h2
  exact (Valuation.restrict_lt_iff_lt_embedding _).2 (h2.trans_lt hn)

end GlobalTheory.CompanionTheory.EmbBridge

namespace GlobalTheory.CompanionTheory.EmbBridge

theorem embeddings_of_continuous : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime]
    (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
      GlobalTheory.Pst.Induces Bw → ∀ (LL' : FinExt l), Bw.LL.1 ≤ LL'.1 →
    ∀ (j : {j : w.adicCompletion E →+* Qbar l // Continuous j}),
    ∃ (φ : w.adicCompletion E →+* Om l) (τ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), Continuous φ ∧
      (∀ y : E, φ (algebraMap E (w.adicCompletion E) y) = Bw.j (algebraMap E Ω y)) ∧
      (∀ x, ∃ hx : φ x ∈ Bw.Kw.1, ((τ ⟨φ x, hx⟩ : ↥LL'.1) : Om l) = j.1 x) ∧
      ∀ τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1,
        IsInduced Bw (j.1.comp (algebraMap E (w.adicCompletion E))) τ' ↔ τ' = τ := by
  intro E Ω _ _ _ _ _ l _ w A hA O _ _ _ Bw hI LL' hLL j
  have hKL : Bw.Kw.1 ≤ LL'.1 := fun x hx => hLL (Bw.LL_split Bw.Kw.1.val ⟨x, hx⟩)
  obtain ⟨⟨φ, hφc⟩, hφ, -⟩ := GlobalTheory.CompanionTheory.EmbUniq.existsUnique_continuous_induced w A hA O Bw hI LL'
    (IntermediateField.inclusion hKL)
  have hφE : ∀ y : E, φ (algebraMap E (w.adicCompletion E) y) = Bw.j (algebraMap E Ω y) := fun y => hφ y
  haveI : FiniteDimensional ℚ_[l] ↥Bw.Kw.1 := Bw.Kw.2
  have hKc : IsClosed (Bw.Kw.1 : Set (Om l)) :=
    Submodule.closed_of_finiteDimensional (Subalgebra.toSubmodule Bw.Kw.1.toSubalgebra)
  have hmem : ∀ x, φ x ∈ Bw.Kw.1 := fun x =>
    (HeightOneSpectrum.denseRange_algebraMap E w).induction_on (p := fun x => φ x ∈ (Bw.Kw.1 : Set (Om l))) x
      (hKc.preimage hφc) (fun y => by
        show φ _ ∈ Bw.Kw.1
        rw [hφE]; exact Bw.j_E y)
  have hind := isInducing w φ hφc
  have hrc : IsClosed (Set.range φ) :=
    (AddMonoidHom.isUniformInducing_of_isInducing (f := φ.toAddMonoidHom) hind).isComplete_range.isClosed
  have hsurj : ∀ k : ↥Bw.Kw.1, ∃ x, φ x = k := fun k => by
    have h1 : (k : Om l) ∈ closure (Set.range fun x : E => Bw.j (algebraMap E Ω x)) := Bw.j_dense k.2
    have h2 : (Set.range fun x : E => Bw.j (algebraMap E Ω x)) ⊆ Set.range φ := by
      rintro _ ⟨y, rfl⟩
      exact ⟨_, hφE y⟩
    exact hrc.closure_subset_iff.2 h2 h1
  let φ' : w.adicCompletion E →+* ↥Bw.Kw.1 := φ.codRestrict Bw.Kw.1 hmem
  have hbij : Function.Bijective φ' := ⟨fun a b h => φ.injective (congrArg Subtype.val h), fun k => by
    obtain ⟨x, hx⟩ := hsurj k
    exact ⟨x, Subtype.ext hx⟩⟩
  let e : w.adicCompletion E ≃+* ↥Bw.Kw.1 := RingEquiv.ofBijective φ' hbij
  have hei : Topology.IsInducing e := by
    refine Topology.IsInducing.of_comp ?_ continuous_subtype_val hind
    exact hφc.subtype_mk hmem
  have hes : Continuous e.symm := (e.toEquiv.toHomeomorphOfIsInducing hei).symm.continuous
  let ψ : ↥Bw.Kw.1 →+* Om l := j.1.comp (e.symm : ↥Bw.Kw.1 →+* w.adicCompletion E)
  have hψc : Continuous ψ := j.2.comp hes
  have hlin : ∀ a : ℚ_[l], ψ (algebraMap ℚ_[l] ↥Bw.Kw.1 a) = algebraMap ℚ_[l] (Om l) a := fun a => by
    have c1 : Continuous fun a : ℚ_[l] => ψ (algebraMap ℚ_[l] ↥Bw.Kw.1 a) :=
      hψc.comp (continuous_algebraMap ℚ_[l] ↥Bw.Kw.1)
    have c2 : Continuous fun a : ℚ_[l] => algebraMap ℚ_[l] (Om l) a := continuous_algebraMap ℚ_[l] (Om l)
    refine congrFun ((Padic.denseRange_ratCast l).equalizer c1 c2 (funext fun q => ?_)) a
    simp
  let μ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] Om l := { ψ with commutes' := hlin }
  let τ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1 := μ.codRestrict LL'.1.toSubalgebra fun x => hLL (Bw.LL_split μ x)
  have hτ : ∀ x (hx : φ x ∈ Bw.Kw.1), ((τ ⟨φ x, hx⟩ : ↥LL'.1) : Om l) = j.1 x := fun x hx => by
    have : e.symm ⟨φ x, hx⟩ = x := e.symm_apply_apply x
    show j.1 (e.symm ⟨φ x, hx⟩) = j.1 x
    rw [this]
  have key : ∀ y : E, ((τ (GlobalTheory.CompanionTheory.EmbUniq.toKw Bw y) : ↥LL'.1) : Om l) = j.1 (algebraMap E _ y) := fun y => by
    have e1 : GlobalTheory.CompanionTheory.EmbUniq.toKw Bw y = ⟨φ (algebraMap E _ y), hmem _⟩ := Subtype.ext (hφE y).symm
    rw [e1]
    exact hτ _ _
  have hd : DenseRange (GlobalTheory.CompanionTheory.EmbUniq.toKw Bw) := fun k => by
    rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image, ← Set.range_comp]
    exact Bw.j_dense k.2
  have hc : ∀ t : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1, Continuous fun x => ((t x : ↥LL'.1) : Om l) := fun t => by
    refine Metric.continuous_iff.2 fun b ε hε => ⟨ε, hε, fun a h => ?_⟩
    have h' : ‖(a : Om l) - (b : Om l)‖ < ε := by rwa [← dist_eq_norm]
    rw [dist_eq_norm]
    have e2 : ((t a : ↥LL'.1) : Om l) - ((t b : ↥LL'.1) : Om l) = ((t (a - b) : ↥LL'.1) : Om l) := by
      simp
    rw [e2, GlobalTheory.CompanionTheory.EmbUniq.norm_coe_algHom]
    exact h'
  refine ⟨φ, τ, hφc, hφE, fun x => ⟨hmem x, hτ x _⟩, fun τ' => ⟨fun h => ?_, ?_⟩⟩
  · refine AlgHom.ext fun x => Subtype.ext (congrFun (hd.equalizer (hc τ') (hc τ) (funext fun y => ?_)) x)
    exact (h y).symm.trans (key y).symm
  · rintro rfl y
    exact (key y).symm

end GlobalTheory.CompanionTheory.EmbBridge
end
end

section

set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

theorem _root_.GlobalTheory.T.isSmooth_comp_continuous : ∀ {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (ψ : H →* G), Continuous ψ → ∀ {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W), GlobalTheory.PRep.IsSmooth ρ → GroundTheory.Automorphic.IsSmooth (ρ.comp ψ) := by
  first | exact @GlobalTheory.CompanionTheory.SmoothBridge.isSmooth_comp | exact GlobalTheory.CompanionTheory.SmoothBridge.isSmooth_comp | (intros; apply GlobalTheory.CompanionTheory.SmoothBridge.isSmooth_comp <;> assumption)
end

section

set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

theorem _root_.GlobalTheory.T.modulus_character_levi : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ), (∀ x y, β x < β y ↔ blk e x < blk e y) → ∀ (φ : Levi k m ≃* levi k N β), (∀ g, ((φ g : levi k N β) : GL (Fin N) k) = leviEmb k e g) → ∀ g : Levi k m, ((deltaHalf k m g : ℂˣ) : ℂ) = sqrtModular k N β (leviIncl (φ g)) := by
  first | exact @GlobalTheory.CompanionTheory.DeltaLevi.deltaHalf_eq_sqrtModular | exact GlobalTheory.CompanionTheory.DeltaLevi.deltaHalf_eq_sqrtModular | (intros; apply GlobalTheory.CompanionTheory.DeltaLevi.deltaHalf_eq_sqrtModular <;> assumption)
end

section

set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

theorem _root_.GlobalTheory.T.filtration_transport_equiv : ∀ {G H : Type} [Group G] [Group H] (ψ : H →* G) {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (ρ : Representation ℂ H V) (ρ' : Representation ℂ G V'), ρ.Equiv (ρ'.comp ψ) → ∀ (K : ℕ) (X : Fin K → Type) [∀ j, AddCommGroup (X j)] [∀ j, Module ℂ (X j)] (τ : ∀ j, Representation ℂ G (X j)) (Vf : ℕ → Submodule ℂ V'), Vf 0 = ⊥ → Vf K = ⊤ → Monotone Vf → ∀ (hV : ∀ i (g : G), Vf i ≤ (Vf i).comap (ρ' g)), (∀ j : Fin K, ∃ Ψ : Representation.IntertwiningMap (ρ'.subrepresentation (Vf (j + 1)) (hV (j + 1))) (τ j), Function.Surjective Ψ ∧ ∀ x, Ψ x = 0 ↔ (x : V') ∈ Vf j) → ∃ S : Fin (K + 1) → Subrepresentation ρ, Monotone S ∧ S 0 = ⊥ ∧ S (Fin.last K) = ⊤ ∧ ∀ t : Fin K, Nonempty ((GlobalTheory.SmGL.subQuot (S t.succ) (S t.castSucc)).Equiv ((τ t).comp ψ)) := by
  first | exact @GlobalTheory.CompanionTheory.FiltTransfer.subQuot_of_filtration | exact GlobalTheory.CompanionTheory.FiltTransfer.subQuot_of_filtration | (intros; apply GlobalTheory.CompanionTheory.FiltTransfer.subQuot_of_filtration <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.graded_form_frame : GlobalTheory.CompanionTheory.GrForm.StFrame := by
  first | exact @GlobalTheory.CompanionTheory.GrForm.stFrame | exact GlobalTheory.CompanionTheory.GrForm.stFrame | (intros; apply GlobalTheory.CompanionTheory.GrForm.stFrame <;> assumption)
end
