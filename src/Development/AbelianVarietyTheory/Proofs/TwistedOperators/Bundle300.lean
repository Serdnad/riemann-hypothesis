module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Mathlib.LinearAlgebra.Matrix.Rank
import Aesop.Main
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsCuspFunIffConstTerm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle194
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle187
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsCuspFunOnePlane
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle001
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.ExistsSmulOfMapResidueEqZero
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffHeckePolyOfComplex
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle148
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMatrixOfIsLattice
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle171
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle141
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GaussBinomMulProd
public import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Formalism.SubspaceCounting.ChoiceOfTopsRefined
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle288
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1816
public import GroundTheory.GlobalFields.TateThesis.AdelicCharDual
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle223

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped ENNReal

noncomputable section
namespace GlobalTheory.TowerCT

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem vol : ∀ (D : D7) (V : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C →
    ∀ (κ : Measure (NI V C)) (𝓝 : Set (NI V C)), κ.IsHaarMeasure → IsFundamentalDomain (NIQ V C) 𝓝 κ → κ 𝓝 ≠ ⊤ := by
  intro D V r C hC κ 𝓝 hκ h𝓝
  have hint : IntegrableOn (fun _ : NI V C => (1 : ℂ)) 𝓝 κ := by
    have key : ∀ N : Subgroup (GA D V),
        N = GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) (GlobalTheory.AutFunCompare.colSpan V C) →
        ∀ Q : Subgroup (GA D V), Q = GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.ratPts D.sp.cm V →
        ∀ (μ : Measure N) (𝓕 : Set N), μ.IsHaarMeasure → IsFundamentalDomain (Q.subgroupOf N) 𝓕 μ →
          IntegrableOn (fun _ : N => (1 : ℂ)) 𝓕 μ := by
      rintro N rfl Q rfl μ 𝓕 hμ h𝓕
      exact GlobalTheory.AutFunCompare.integrableOn_constTerm D.sp.cm V _ ((GlobalTheory.AutFunCompare.isIsoFrame_iff V C).1 hC).2
        (fun _ => 1) continuous_const (fun _ _ _ => rfl) μ hμ 𝓕 h𝓕 1
    exact key _ (GlobalTheory.AutFunCompare.NI_eq V C) _ (GlobalTheory.AutFunCompare.GQ_eq V) κ 𝓝 hκ h𝓝
  rcases (integrableOn_const_iff (C := (1 : ℂ))).1 hint with h | h
  · exact absurd h (by simp)
  · exact h.ne

theorem cusp : ∀ (D : D7) (W : HSp D) (s : ℕ) (L : Matrix (Fin W.rank) (Fin s) D.host.E), IsIsoFrame W L →
    ∀ (ν : Measure (GA D W)), ν.IsHaarMeasure → ∀ F : GA D W → ℂ, GlobalTheory.Grow.RapidDec W F → IsCuspFun W F →
    ∀ Γ : Subgroup (GA D W), Γ ≤ GQ W → (∀ γ ∈ Γ, ∀ n ∈ NI W L, γ * n * γ⁻¹ ∈ NI W L) →
    (∀ n ∈ NI W L, n ∈ GQ W → n ∈ Γ) → ∀ K : GA D W → ℂ, Measurable K → (∀ n ∈ NI W L, ∀ h, K (n * h) = K h) →
    (∀ γ ∈ Γ, ∀ h, K (γ * h) = K h) → ∀ 𝓖 : Set (GA D W), IsFundamentalDomain Γ 𝓖 ν →
    IntegrableOn (fun h => K h * F h) 𝓖 ν → ∫ h in 𝓖, K h * F h ∂ν = 0 := by
  intro D W s L hL ν hν F hF hcusp Γ hle hnorm hin K hKm hKn hKγ 𝓖 h𝓖 hint
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  have hcl := GlobalTheory.CuspDecay.Model.isClosed_NI W hL
  have : LocallyCompactSpace (NI W L) := hcl.locallyCompactSpace
  have hQ : Countable (GQ W) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig W.gram
  let i : NIQ W L → GQ W := fun x => ⟨x.1.1, x.2⟩
  have hi : Function.Injective i := fun x y h => Subtype.ext (Subtype.ext (congrArg (fun z : GQ W => z.1) h))
  have : DiscreteTopology (NIQ W L) := DiscreteTopology.of_continuous_injective (f := i)
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _) hi
  have : Countable (NIQ W L) := hi.countable
  have : SecondCountableTopology (NI W L) := TopologicalSpace.Subtype.secondCountableTopology _
  let κ : Measure (NI W L) := Measure.haar
  obtain ⟨𝓝, h𝓝⟩ := GlobalTheory.FundDomDiscrete.exists_isFundamentalDomain (NIQ W L) κ
  have hκ : κ.IsHaarMeasure := inferInstance
  have hΓ : Countable Γ := (Subgroup.inclusion_injective hle).countable
  have e : Γ.subgroupOf (NI W L) = NIQ W L := by
    ext n
    exact ⟨fun h => hle h, fun h => hin _ n.2 h⟩
  have h𝓝' : IsFundamentalDomain (Γ.subgroupOf (NI W L)) 𝓝 κ := by
    rw [e]
    exact h𝓝
  exact GlobalTheory.T.unfolding_zero_mean_normalized_subgroup (GA D W) ν Γ (NI W L) hΓ hcl hnorm κ 𝓝 hκ h𝓝' (vol D W s L hL κ 𝓝 hκ h𝓝) K F hKm
    hF.2.1.measurable hKn hKγ (fun γ hγ h => hF.1 γ (hle hγ) h) (fun h => hcusp s L hL κ 𝓝 hκ h𝓝 h) 𝓖 h𝓖 hint

theorem rankFacGen {K : Type} [Field K] {a b : ℕ} (y : Matrix (Fin a) (Fin b) K) (hy : y ≠ 0) :
    ∃ (s : ℕ) (L : Matrix (Fin a) (Fin s) K) (m : Matrix (Fin s) (Fin b) K) (m' : Matrix (Fin b) (Fin s) K),
      0 < s ∧ LinearIndependent K L.transpose ∧ m.rank = s ∧ m * m' = 1 ∧ y = L * m := by
  classical
  let U : Submodule K (Fin a → K) := Submodule.span K (Set.range y.transpose)
  let s := Module.finrank K U
  let bs : Module.Basis (Fin s) K U := Module.finBasisOfFinrankEq K U rfl
  have hcol : ∀ j, y.transpose j ∈ U := fun j => Submodule.subset_span ⟨j, rfl⟩
  let L : Matrix (Fin a) (Fin s) K := Matrix.of fun i k => (bs k : Fin a → K) i
  let m : Matrix (Fin s) (Fin b) K := Matrix.of fun k j => bs.repr ⟨y.transpose j, hcol j⟩ k
  have hym : y = L * m := by
    ext i j
    have h := bs.sum_repr ⟨y.transpose j, hcol j⟩
    have h2 := congrArg (fun u : U => (u : Fin a → K) i) h
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h2
    simp only [Matrix.mul_apply, L, m, Matrix.of_apply]
    rw [show y i j = y.transpose j i from rfl, ← h2]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hLi : LinearIndependent K L.transpose := by
    have : LinearIndependent K fun k => (bs k : Fin a → K) := bs.linearIndependent.map' U.subtype (Submodule.ker_subtype U)
    exact this
  have hrk : y.rank = s := by
    rw [← Matrix.finrank_span_range_col]
    rfl
  have hs : 0 < s := by
    refine Nat.pos_of_ne_zero fun h => hy ?_
    have hU : U = ⊥ := Submodule.finrank_eq_zero.1 h
    ext i j
    have := hcol j
    rw [hU, Submodule.mem_bot] at this
    exact congrFun this i
  have hle : s ≤ m.rank := by
    calc s = y.rank := hrk.symm
      _ = (L * m).rank := by rw [← hym]
      _ ≤ m.rank := Matrix.rank_mul_le_right _ _
  have hm : m.rank = s := le_antisymm ((Matrix.rank_le_height m)) hle
  have hsurj : Function.Surjective m.mulVecLin := by
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    have : Module.finrank K (LinearMap.range m.mulVecLin) = s := by
      rw [Matrix.finrank_range_mulVecLin]
      exact hm
    simpa using this
  obtain ⟨g, hg⟩ := m.mulVecLin.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hsurj)
  refine ⟨s, L, m, LinearMap.toMatrix' g, hs, hLi, hm, ?_, hym⟩
  have : Matrix.toLin' (m * LinearMap.toMatrix' g) = LinearMap.id := by
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
    exact hg
  apply Matrix.toLin'.injective
  rw [this, Matrix.toLin'_one]

theorem rankFac : ∀ (D : D7) (W : HSp D) (r : ℕ) (y : Matrix (Fin W.rank) (Fin r) D.host.E), y ≠ 0 →
    adj D y * W.gram * y = 0 → ∃ (s : ℕ) (L : Matrix (Fin W.rank) (Fin s) D.host.E) (m : Matrix (Fin s) (Fin r) D.host.E)
      (m' : Matrix (Fin r) (Fin s) D.host.E), IsIsoFrame W L ∧ m.rank = s ∧ m * m' = 1 ∧ y = L * m := by
  intro D W r y hy hiso
  obtain ⟨s, L, m, m', hs, hL, hm, hmm, e⟩ := rankFacGen y hy
  refine ⟨s, L, m, m', ⟨hs, hL, ?_⟩, hm, hmm, e⟩
  have hLy : L = y * m' := by rw [e, Matrix.mul_assoc, hmm, Matrix.mul_one]
  have hc : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) L = adj D m' * adj D y := by
    rw [hLy]
    simp only [adj, Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]
  rw [hc]
  calc adj D m' * adj D y * W.gram * L = adj D m' * (adj D y * W.gram * y) * m' := by
        rw [hLy]
        simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hiso, Matrix.mul_zero, Matrix.zero_mul]

theorem fub {N H Y : Type} [MeasurableSpace N] [MeasurableSpace H] [Countable Y]
    (κ : Measure N) (ν : Measure H) [SFinite κ] [SFinite ν] (𝓝 : Set N) (𝓕 : Set H)
    (T : Y → N → H → ℂ) (hT : ∀ y, Measurable (Function.uncurry (T y))) (Θ : N → H → ℂ)
    (F : H → ℂ) (hF : Measurable F) (hs : ∀ n h, HasSum (fun y => T y n h) (Θ n h))
    (hb : ∫⁻ n in 𝓝, ∫⁻ h in 𝓕, (∑' y, ‖T y n h‖ₑ) * ‖F h‖ₑ ∂ν ∂κ ≠ ⊤) :
    IntegrableOn (fun n => ∫ h in 𝓕, Θ n h * F h ∂ν) 𝓝 κ ∧
    (∑' y, ∫⁻ h in 𝓕, ‖(∫ n in 𝓝, T y n h ∂κ) * F h‖ₑ ∂ν) ≠ ⊤ ∧
    HasSum (fun y => ∫ h in 𝓕, (∫ n in 𝓝, T y n h ∂κ) * F h ∂ν)
      (∫ n in 𝓝, ∫ h in 𝓕, Θ n h * F h ∂ν ∂κ) := by
  set P := (κ.restrict 𝓝).prod (ν.restrict 𝓕) with hP
  let G : Y → N × H → ℂ := fun y p => T y p.1 p.2 * F p.2
  have hGm : ∀ y, Measurable (G y) := fun y => (hT y).mul (hF.comp measurable_snd)
  have hGe : ∀ y, Measurable fun p => ‖G y p‖ₑ := fun y => (hGm y).enorm
  have hlin : ∫⁻ p, ∑' y, ‖G y p‖ₑ ∂P ≠ ⊤ := by
    rw [hP, lintegral_prod _ (Measurable.tsum hGe).aemeasurable]
    convert hb using 6 with n _ h
    simp only [G, enorm_mul]
    rw [ENNReal.tsum_mul_right]
  have hsum : ∑' y, ∫⁻ p, ‖G y p‖ₑ ∂P ≠ ⊤ := by
    rwa [← lintegral_tsum fun y => (hGe y).aemeasurable]
  have hfin : ∀ y, ∫⁻ p, ‖G y p‖ₑ ∂P ≠ ⊤ := fun y => ENNReal.ne_top_of_tsum_ne_top hsum y
  have hGi : ∀ y, Integrable (G y) P := fun y =>
    ⟨(hGm y).aestronglyMeasurable, lt_top_iff_ne_top.2 (hfin y)⟩
  have hsp : ∀ p : N × H, HasSum (fun y => G y p) (Θ p.1 p.2 * F p.2) := fun p => (hs p.1 p.2).mul_right _
  have hΘm : Measurable fun p : N × H => Θ p.1 p.2 * F p.2 :=
    measurable_of_tendsto_metrizable' Filter.atTop (f := fun (s : Finset Y) p => ∑ y ∈ s, G y p)
      (fun s => Finset.measurable_sum _ fun y _ => hGm y) (tendsto_pi_nhds.2 hsp)
  have hle : ∀ p : N × H, ‖Θ p.1 p.2 * F p.2‖ₑ ≤ ∑' y, ‖G y p‖ₑ := fun p =>
    le_of_tendsto' ((continuous_enorm.tendsto _).comp (hsp p)) fun s =>
      (enorm_sum_le s _).trans (ENNReal.sum_le_tsum s)
  have hΘi : Integrable (fun p : N × H => Θ p.1 p.2 * F p.2) P :=
    ⟨hΘm.aestronglyMeasurable, ((lintegral_mono hle).trans_lt (lt_top_iff_ne_top.2 hlin))⟩
  have hnorm : Summable fun y => ∫ p, ‖G y p‖ ∂P := by
    have e : ∀ y, ∫ p, ‖G y p‖ ∂P = (∫⁻ p, ‖G y p‖ₑ ∂P).toReal := fun y => by
      rw [integral_norm_eq_lintegral_enorm (hGm y).aestronglyMeasurable]
    simp only [e]
    exact ENNReal.summable_toReal hsum
  have hS := hasSum_integral_of_summable_integral_norm hGi hnorm
  have eT : (fun p => ∑' y, G y p) = fun p : N × H => Θ p.1 p.2 * F p.2 := funext fun p => (hsp p).tsum_eq
  rw [eT, hP, integral_prod _ (by rw [← hP]; exact hΘi)] at hS
  refine ⟨hΘi.integral_prod_left, ?_, ?_⟩
  · refine ne_top_of_le_ne_top hsum (ENNReal.tsum_le_tsum fun y => ?_)
    rw [hP, lintegral_prod_symm _ (hGe y).aemeasurable]
    refine lintegral_mono fun h => ?_
    simp only [G, enorm_mul]
    rw [lintegral_mul_const _ ((hT y).of_uncurry_right.enorm)]
    exact mul_le_mul' (enorm_integral_le_lintegral_enorm _) le_rfl
  · have e : (fun y => ∫ h in 𝓕, (∫ n in 𝓝, T y n h ∂κ) * F h ∂ν) =
        fun y => ∫ p, G y p ∂(κ.restrict 𝓝).prod (ν.restrict 𝓕) := funext fun y => by
      rw [integral_prod_symm _ (by rw [← hP]; exact hGi y)]
      refine integral_congr_ae (.of_forall fun h => ?_)
      simp only [G]
      rw [integral_mul_const]
    rw [e]
    exact hS

end GlobalTheory.TowerCT

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField

namespace GlobalTheory.SplitCosetCount

section Grp

open Classical

variable {G : Type} [Group G]

theorem card_le_of_isDC {J : Subgroup G} {x : G} {A B : Finset G} (hA : Bridge.IsDC J x A)
    (hB : Bridge.IsDC J x B) : A.card ≤ B.card := by
  classical
  have f : ∀ a ∈ A, ∃ b, b ∈ B ∧ b⁻¹ * a ∈ J := fun a ha => (hB.2 a (hA.1 a ha)).exists
  choose! φ hφB hφJ using f
  refine Finset.card_le_card_of_injOn φ (fun a ha => hφB a ha) ?_
  intro a₁ ha₁ a₂ ha₂ he
  have h1 : a₁⁻¹ * a₂ ∈ J := by
    have h := J.mul_mem (J.inv_mem (hφJ a₁ ha₁)) (hφJ a₂ ha₂)
    have e : ((φ a₁)⁻¹ * a₁)⁻¹ * ((φ a₂)⁻¹ * a₂) = a₁⁻¹ * a₂ := by rw [he]; group
    rwa [e] at h
  exact (hA.2 a₂ (hA.1 a₂ ha₂)).unique ⟨ha₁, h1⟩ ⟨ha₂, by simp⟩

theorem card_eq_of_isDC {J : Subgroup G} {x : G} {A B : Finset G} (hA : Bridge.IsDC J x A)
    (hB : Bridge.IsDC J x B) : A.card = B.card :=
  le_antisymm (card_le_of_isDC hA hB) (card_le_of_isDC hB hA)

variable {H : Type} [Group H] {ρ : G →* H} {S : G → Prop} {K : Set G} {K' : Subgroup H}

theorem lift_isReps (hm : ∀ x y, S x → S y → S (x * y)) (hi : ∀ x, S x → S x⁻¹)
    (hinj : ∀ x y, S x → S y → ρ x = ρ y → x = y) (hK : ∀ g, S g → (g ∈ K ↔ ρ g ∈ K'))
    {g : G} (hg : S g) {R₀ : Finset H} (hR : Formalism.IndefR.Fin.HCount.IsReps K' (ρ g) R₀)
    (ψ : H → G) (hψs : ∀ a, S (ψ a)) (hψ : ∀ a, ρ (ψ a) = a) :
    (∀ γ ∈ R₀.image ψ, ∃ k₁ ∈ {k | k ∈ K ∧ S k}, ∃ k₂ ∈ {k | k ∈ K ∧ S k}, γ = k₁ * g * k₂) ∧
      ∀ x : G, (∃ k₁ ∈ {k | k ∈ K ∧ S k}, ∃ k₂ ∈ {k | k ∈ K ∧ S k}, x = k₁ * g * k₂) →
        ∃! γ, γ ∈ R₀.image ψ ∧ γ⁻¹ * x ∈ {k | k ∈ K ∧ S k} := by
  classical
  have hex : ∀ a, ∃ g, S g ∧ ρ g = a := fun a => ⟨ψ a, hψs a, hψ a⟩
  refine ⟨fun γ hγ => ?_, ?_⟩
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hγ
    exact GlobalTheory.SplitPlace.lift_dc hm hex hinj hK hg (hψs a) (by rw [hψ]; exact hR.1 a ha)
  · rintro x ⟨k₁, hk₁, k₂, hk₂, rfl⟩
    have hx := hm _ _ (hm _ _ hk₁.2 hg) hk₂.2
    have key : ∀ a, (ψ a)⁻¹ * (k₁ * g * k₂) ∈ {k | k ∈ K ∧ S k} ↔ a⁻¹ * ρ (k₁ * g * k₂) ∈ K' := by
      intro a
      have hs := hm _ _ (hi _ (hψs a)) hx
      have := hK _ hs
      rw [map_mul, map_inv, hψ] at this
      exact ⟨fun h => this.1 h.1, fun h => ⟨this.2 h, hs⟩⟩
    obtain ⟨a, ⟨ha, ha'⟩, hu⟩ := hR.2 (ρ (k₁ * g * k₂)) ⟨_, (hK _ hk₁.2).1 hk₁.1, _, (hK _ hk₂.2).1 hk₂.1,
      by rw [map_mul, map_mul]⟩
    refine ⟨ψ a, ⟨Finset.mem_image_of_mem _ ha, (key a).2 ha'⟩, ?_⟩
    rintro γ ⟨hγ, h⟩
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hγ
    rw [hu b ⟨hb, (key b).1 h⟩]

theorem card_image_section {R₀ : Finset H} (ψ : H → G) (hψ : ∀ a, ρ (ψ a) = a) :
    (R₀.image ψ).card = R₀.card := by
  classical
  refine Finset.card_image_of_injective _ fun a b h => ?_
  rw [← hψ a, ← hψ b, h]

end Grp

theorem gaussBinom_eq (κ : Type) [Field κ] [Fintype κ] (n k : ℕ) :
    Formalism.G0.gaussBinom (Fintype.card κ) n k = GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom (Fintype.card κ) n k := by
  have h1 := Formalism.G0.Top.subspaceCount (F := κ) (W := Fin n → κ) k
  have h2 := GlobalTheory.GaussCount.subspaceCount κ (Fin n → κ) k
  rw [Module.finrank_fin_fun] at h1 h2
  rw [Nat.card_eq_fintype_card (α := κ)] at h2
  rw [← h1, ← h2]
  unfold Formalism.G0.countBelow
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight fun U => by simp

end GlobalTheory.SplitCosetCount

namespace GlobalTheory.SplitCosetCount

open Classical
open Formalism.IndefR.Lev GlobalTheory.HeckeParts Formalism.L2.NTheta



theorem card_cosets : ∀ (D : D7) {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
    R.toLevCh.Is A.μ0 → R.IsFam → ∀ (i : Fin D.R.m) (P : Formalism.L2.DIV.Pl D.host.E) (k : ℕ) (α : GA D (Wc D i))
    (Rc : Finset (GA D (Wc D i))), Bridge.SplitOff P (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) → k ≤ D.R.r →
    IsHeckeAt (Wc D i) P k α → Bridge.IsDC (Lev.levG (Wc D i) (R.βW i) (R.datWp i R.triv)) α Rc →
    Rc.card = GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom (Ideal.absNorm P.asIdeal) D.R.r k := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hL hF i P k α Rc hso hk hα hRc
  obtain ⟨c, hβ⟩ := hL.βW i
  have hN : ((1 ^ c : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    rw [one_pow, Nat.cast_one]
    exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
  have hoff : ∀ PP, PP ∈ (R.datWp i R.triv).Pg ∨ PP ∈ (R.datWp i R.triv).Q → PP ≠ P ∧ ¬ Lev.IsConjPl PP P := by
    intro PP hPP
    have hPP' : PP ∈ R.Pg := hPP.elim id fun h => absurd h (Finset.notMem_empty _)
    have hS : PP ∈ (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) := hF.Sb hPP'
    refine ⟨fun h => hso.2.1 (h ▸ hS), fun h => hso.2.2 PP hS ?_⟩
    rw [Formalism.L2.Col.conjIdeal_asIdeal]
    refine PP.isMaximal.eq_of_le (Formalism.L2.Col.conjPrime₂ P).isPrime.ne_top fun a ha => ?_
    obtain ⟨a', ha', e⟩ := h a ha
    rw [Formalism.L2.Col.mem_conjP]
    have : Formalism.L2.Col.cO D.host.E a = a' := RingOfIntegers.ext e.symm
    rwa [this]
  obtain ⟨e, ϖ, he, h1, h2, hαe⟩ := hα
  obtain ⟨Lp, hLp, -, hs, hK⟩ := loc_package hβ (L := R.datWp i R.triv) ⟨hso.1, hN, hoff⟩ he
  obtain ⟨v, π, s, c1, c2, c3, c4, c5⟩ := GlobalTheory.SplitCoord.exists_coord e he.1
  obtain ⟨B, hB⟩ := GlobalTheory.SplitLatBasis.exists_basis (Wc D i) e v π s he.1.1 c2 c3 c4
    (GlobalTheory.LatDual.lamHat_selfDual_and_module (Wc D i)).2
  obtain ⟨hex, hinj⟩ := GlobalTheory.SplitPlace.comp_bij (V := Wc D i) (B := B) he.1 c1 c2
  have hKc := fun g => GlobalTheory.SplitPlace.K_iff (V := Wc D i) (g := g) he.1 c2 c3 hB
  have hu := GlobalTheory.SplitPlace.isUnif he c4 c5 ϖ h1 h2
  obtain ⟨hu0, hu1⟩ := GlobalTheory.SplitPlace.unif_facts hu
  have hH := (GlobalTheory.SplitPlace.hecke_iff he.1 c1 c2 c3 c4 hB hu0 k α).1 hαe

  obtain ⟨w, hw⟩ : ∃ w, π (finPart D (incA D (ϖ : D.host.E))) = w := ⟨_, rfl⟩
  rw [hw] at hu hu0 hu1 hH
  have hirr : Irreducible (⟨w, hu1⟩ : Formalism.UG.Ov D.host.F v) :=
    Formalism.IndefR.Fin.HCount.irreducible_of_unif D.host.F v ⟨w, hu1⟩ hu
  have hv0 : Valued.v w ≠ 0 := (Valuation.ne_zero_iff _).2 hu0
  have htype : Formalism.IndefR.Fin.HCount.IsType (Formalism.UG.Ov D.host.F v) ⟨w, hu1⟩ k
      (GlobalTheory.SplitPlace.comp (Wc D i) π B α) := by
    refine ⟨fun a b => hH.2.1 a b, fun a b => ?_, ?_⟩
    · rw [Matrix.smul_apply, smul_eq_mul]
      exact hH.2.2.1 a b
    · obtain ⟨d, hd⟩ : ∃ d, (GlobalTheory.SplitPlace.comp (Wc D i) π B α).1.det = d := ⟨_, rfl⟩
      have hdv' := hH.2.2.2
      rw [hd] at hdv'
      have hdv : Valued.v (d / w ^ k) = 1 := by
        rw [map_div₀, map_pow, hdv', div_self (pow_ne_zero _ hv0)]
      have hne : d / w ^ k ≠ 0 := fun h => by rw [h, map_zero] at hdv; exact zero_ne_one hdv
      have hm : d / w ^ k ∈ Formalism.UG.Ov D.host.F v := by show Valued.v ((d / w ^ k : v.adicCompletion D.host.F)) ≤ 1; exact le_of_eq hdv
      have hmi : (d / w ^ k)⁻¹ ∈ Formalism.UG.Ov D.host.F v := by show Valued.v ((d / w ^ k : v.adicCompletion D.host.F)⁻¹) ≤ 1; rw [map_inv₀, hdv, inv_one]
      refine ⟨⟨d / w ^ k, hm⟩, isUnit_iff_exists_inv.2 ⟨⟨_, hmi⟩, Subtype.ext (mul_inv_cancel₀ hne)⟩, ?_⟩
      show _ = w ^ k * (d / w ^ k)
      rw [hd, mul_div_cancel₀ _ (pow_ne_zero _ hu0)]

  obtain ⟨R₀, hR₀⟩ := GlobalTheory.SplitPlace.exists_reps (Formalism.UG.Final.GLintComm D.host.F v (Wc D i).rank)
    (GlobalTheory.SplitPlace.comp (Wc D i) π B α)
  have hc0 := Formalism.IndefR.Fin.HCount.card_reps (Formalism.UG.Ov D.host.F v) hirr htype (R := R₀) hR₀
  choose ψ hψs hψ using hex
  have hl := lift_isReps (ρ := GlobalTheory.SplitPlace.comp (Wc D i) π B) (S := SuppAt e (Wc D i))
    (K := (KsphC (Wc D i) ∅ : Set (GA D (Wc D i)))) (fun _ _ => GlobalTheory.SplitPlace.suppAt_mul)
    (fun _ => GlobalTheory.SplitPlace.suppAt_inv) hinj hKc hH.1 hR₀ ψ hψs hψ
  have hdc : Bridge.IsDC (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) α (R₀.image ψ) := by
    refine isDC_of_splits hs levG_le_flag ((hLp α).2 hH.1) (fun a ha => ?_) hK hl.1 hl.2
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 ha
    exact (hLp _).2 (hψs b)
  let φ : D.host.E →+* v.adicCompletion D.host.F := (π.comp (finPart D)).comp (incA D)
  have hP : ∀ x : 𝓞 D.host.E, x ∈ P.asIdeal ↔ Valued.v (φ x) < 1 := by
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · have hx0 : Valued.v (φ x) ≠ 0 := by
        rw [Valuation.ne_zero_iff, map_ne_zero]
        exact fun h => hx (Subtype.ext h)
      rw [he.2 x hx, map_mul, c4]
      show ¬ Valued.v (φ (x : D.host.E)⁻¹) ≤ 1 ↔ _
      rw [map_inv₀, map_inv₀, not_le, one_lt_inv₀ (zero_lt_iff.2 hx0)]
  have hq : Fintype.card (IsLocalRing.ResidueField (Formalism.UG.Ov D.host.F v)) = Ideal.absNorm P.asIdeal := by
    rw [← Nat.card_eq_fintype_card]
    exact GlobalTheory.SplitUnif.card_residueField v φ P c5 hP
  rw [card_eq_of_isDC hRc hdc, card_image_section ψ hψ, hc0, gaussBinom_eq, hq, rank_Wc]

end GlobalTheory.SplitCosetCount
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_latticeHom_approx_integralMatrix_mod : ∀ {D : D7} {m n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)) (β : GL (Fin n) (EAf D)) (β' : GL (Fin m) (EAf D)), Formalism.L2.DIV.IsFrame β Λ → Formalism.L2.DIV.IsFrame β' Λ' → ∀ (I : Ideal (𝓞 D.host.E)), I ≠ ⊥ → ∀ (N : Matrix (Fin m) (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E)), ∃ x₀ ∈ GlobalTheory.ChiGrid.homLat Λ Λ', ∀ i j, ∃ s ∈ Formalism.L2.DIV.idS D.host.F I, (s : EAf D) = HMul.hMul (HMul.hMul (β'⁻¹).val (x₀.map (eToEAf D))) β.val i j - (N i j : EAf D) := by
  first | exact @GlobalTheory.FunObj.HatFrame.homLat_approx_mod | exact GlobalTheory.FunObj.HatFrame.homLat_approx_mod | (intros; apply GlobalTheory.FunObj.HatFrame.homLat_approx_mod <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section

namespace GlobalTheory.SBLevel

theorem exists_int_level : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ), g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) →
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ x u : κ → FiniteAdeleRing (𝓞 F) F,
      (∀ i, ∀ v : HeightOneSpectrum (𝓞 F),
        (algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F)⁻¹) * u i) v ∈ v.adicCompletionIntegers F) →
      g (x + u) = g x := by
  intro F _ _ κ _ g hg
  classical
  obtain ⟨N, hN, hNg⟩ := GlobalTheory.SBBox.exists_nhds_zero_add_eq hg.1 hg.2
  rw [nhds_pi, Filter.mem_pi] at hN
  obtain ⟨I, -, t, ht, hIt⟩ := hN
  have hW : (⋂ i, t i) ∈ nhds (0 : FiniteAdeleRing (𝓞 F) F) := Filter.iInter_mem.2 ht
  obtain ⟨d, hd0, hd⟩ := GroundTheory.Global.exists_forall_mul_mem_of_mem_nhds hW
  refine ⟨d, hd0, fun x u hu => hNg x u (hIt fun i _ => ?_)⟩
  have hdK : (algebraMap (𝓞 F) F d) ≠ 0 := by
    rwa [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]
  have hmem := hd (algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F)⁻¹) * u i) (hu i)
  have he : algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F d) *
      (algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F)⁻¹) * u i) = u i := by
    rw [← mul_assoc, ← map_mul]
    have : algebraMap (𝓞 F) F d * (d : F)⁻¹ = 1 := mul_inv_cancel₀ hdK
    rw [this, map_one, one_mul]
  rw [he] at hmem
  exact Set.mem_iInter.1 hmem i

end GlobalTheory.SBLevel
end
end
