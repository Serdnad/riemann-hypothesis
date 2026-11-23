module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle112
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1554
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1194
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle220
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle023
public import Formalism.LocalToGlobal.Columns.RecLevelTop
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.FundamentalContinuity.AdelicIsomorphismStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1522
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle120
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1212
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1523
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1238
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1239
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1240
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1524
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1258
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1289
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1525
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle040
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LocIntSpan

theorem isIntB_of_trace_mem :
    ∀ (L : Type) [Field L] [NumberField L] (κ : Type) (bL : Module.Basis κ ℚ L),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, ∀ E : v.adicCompletion ℚ ⊗[ℚ] L,
      (∀ i, Algebra.trace (v.adicCompletion ℚ) (v.adicCompletion ℚ ⊗[ℚ] L)
          (E * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] bL i)) ∈ v.adicCompletionIntegers ℚ) →
        IsIntB v bL E := by
  intro L _ _ κ bL
  haveI : Fintype κ := FiniteDimensional.fintypeBasisIndex bL
  have hd : Algebra.discr ℚ bL ≠ 0 := Algebra.discr_not_zero_of_basis ℚ bL
  obtain ⟨S, hS⟩ := exists_finset_algebraMap_mem
    (insert (Algebra.discr ℚ bL)⁻¹
      (Finset.univ.image fun p : κ × κ => Algebra.trace ℚ L (bL p.1 * bL p.2)))
  refine ⟨S, fun v hv E hE => ?_⟩
  set Q := v.adicCompletion ℚ
  let B := Algebra.TensorProduct.basis Q bL
  have hB : ∀ i, B i = (1 : Q) ⊗ₜ[ℚ] bL i := fun i => by
    simp [B, Algebra.TensorProduct.basis_apply]
  have htr : ∀ i j, Algebra.trace Q (Q ⊗[ℚ] L) (B i * B j) =
      algebraMap ℚ Q (Algebra.trace ℚ L (bL i * bL j)) := fun i j => by
    rw [hB, hB, Algebra.TensorProduct.tmul_mul_tmul, one_mul, trace_one_tmul']
  have hTM : Algebra.traceMatrix Q B = (algebraMap ℚ Q).mapMatrix (Algebra.traceMatrix ℚ bL) := by
    refine Matrix.ext fun i j => ?_
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.traceMatrix_apply, Algebra.traceMatrix_apply,
      Algebra.traceForm_apply, Algebra.traceForm_apply]
    exact htr i j
  have hdet : (Algebra.traceMatrix Q B).det = algebraMap ℚ Q (Algebra.discr ℚ bL) := by
    rw [hTM, ← RingHom.map_det, Algebra.discr_def]
  have hG : ∀ i j, ∃ u : v.adicCompletionIntegers ℚ, algebraMap (v.adicCompletionIntegers ℚ) Q u =
      Algebra.trace Q (Q ⊗[ℚ] L) (B i * B j) := fun i j =>
    ⟨⟨_, hS v hv _ (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩))⟩,
      (htr i j).symm⟩
  have hω : ∀ i, ∃ u : v.adicCompletionIntegers ℚ, algebraMap (v.adicCompletionIntegers ℚ) Q u =
      Algebra.trace Q (Q ⊗[ℚ] L) (E * B i) := fun i => ⟨⟨_, by rw [hB]; exact hE i⟩, rfl⟩
  obtain ⟨u, hu⟩ := GlobalTheory.DiscConductor.det_smul_eq_sum (v.adicCompletionIntegers ℚ) Q (Q ⊗[ℚ] L) κ B E hG hω
  intro j
  have hrep : B.repr E j = (algebraMap ℚ Q (Algebra.discr ℚ bL))⁻¹ *
      algebraMap (v.adicCompletionIntegers ℚ) Q (u j) := by
    have h1 := congrArg (fun x => B.repr x j) hu

    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_sum, Finset.sum_apply', Module.Basis.repr_self, Finsupp.single_apply, hdet] at h1
    rw [Finset.sum_eq_single j (fun k _ hk => by simp [hk]) (by simp)] at h1
    simp only [if_true, mul_one] at h1
    have hne : algebraMap ℚ Q (Algebra.discr ℚ bL) ≠ 0 := (map_ne_zero _).2 hd
    rw [← h1, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  show B.repr E j ∈ v.adicCompletionIntegers ℚ
  rw [hrep, ← map_inv₀]
  exact mul_mem (hS v hv _ (Finset.mem_insert_self _ _)) (u j).2

end GlobalTheory.LocIntSpan
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.archSchwartz_L2Bounded_intertwiner_continuous : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (κ : Type) [Fintype κ]
    (L : ((κ → mixedEmbedding.mixedSpace D.host.F) × (κ → mixedEmbedding.mixedSpace D.host.F)) ≃ₗ[ℝ] ((κ → mixedEmbedding.mixedSpace D.host.F) × (κ → mixedEmbedding.mixedSpace D.host.F)))
    (A : SchwartzMap (κ → mixedEmbedding.mixedSpace D.host.F) ℂ →ₗ[ℂ] SchwartzMap (κ → mixedEmbedding.mixedSpace D.host.F) ℂ) (C : ℝ≥0∞), C ≠ ⊤ →
      (∀ f, ∫⁻ z, ‖A f z‖ₑ ^ 2 ≤ C * ∫⁻ z, ‖f z‖ₑ ^ 2) →
      (∀ v (f f' : SchwartzMap (κ → mixedEmbedding.mixedSpace D.host.F) ℂ), ⇑f' = GlobalTheory.WeilAdm.schrInf D.host.F ψ v ⇑f →
        ⇑(A f') = GlobalTheory.WeilAdm.schrInf D.host.F ψ (L v) ⇑(A f)) →
      Continuous A := by
  first | exact @GlobalTheory.WeilAdm.realcont | exact GlobalTheory.WeilAdm.realcont | (intros; apply GlobalTheory.WeilAdm.realcont <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilAdm

open Filter Topology

theorem fixSupp_exists_box {κ X : Type} [Fintype κ] [TopologicalSpace X] {S : Set (κ → X)} {x0 : X}
    (hS : S ∈ 𝓝 (fun _ : κ => x0)) : ∃ O ∈ 𝓝 x0, ∀ u : κ → X, (∀ i, u i ∈ O) → u ∈ S := by
  rw [nhds_pi, Filter.mem_pi] at hS
  obtain ⟨I, -, t, ht, hsub⟩ := hS
  exact ⟨⋂ i, t i, Filter.iInter_mem.2 ht, fun u hu => hsub fun i _ => Set.mem_iInter.1 (hu i) i⟩

variable {F : Type} [Field F] [NumberField F]

theorem fixSupp_finE_zero {κ : Type} : finE F (0 : κ → FiniteAdeleRing (𝓞 F) F) = 0 := by
  funext i; rfl

theorem fixSupp_finE_single {κ : Type} [DecidableEq κ] (j : κ) (t : FiniteAdeleRing (𝓞 F) F) :
    finE F (Pi.single j t : κ → FiniteAdeleRing (𝓞 F) F) = Pi.single j (pairA F 0 t) := by
  funext i
  by_cases hij : i = j
  · subst hij
    show pairA F 0 ((Pi.single i t : κ → FiniteAdeleRing (𝓞 F) F) i) = (Pi.single i (pairA F 0 t) : κ → AdeleRing (𝓞 F) F) i
    rw [Pi.single_eq_same, Pi.single_eq_same]
  · simp only [finE, Pi.single_eq_of_ne hij]; rfl

theorem fixed_schroedinger_invariant_compactSupport_bounded_annihilator (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (hann : ∀ O ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F), ∃ K : Set (FiniteAdeleRing (𝓞 F) F), IsCompact K ∧
      ∀ x : FiniteAdeleRing (𝓞 F) F, (∀ t ∈ O, ψ (pairA F 0 (t * x)) = 1) → x ∈ K)
    (κ : Type) [Fintype κ]
    (M : AddSubgroup ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)))
    (hM : IsOpen (M : Set ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)))) :
    ∃ (U : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)) (K : Set (κ → FiniteAdeleRing (𝓞 F) F)),
      IsOpen (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧ IsCompact (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧
      IsCompact K ∧ ∀ Φ : (κ → AdeleRing (𝓞 F) F) → ℂ, (∀ m ∈ M, GlobalTheory.WeilM.schr ψ (finE2 F m) Φ = Φ) →
        (∀ x, ∀ u ∈ U, Φ (x + finE F u) = Φ x) ∧ ∀ x, (fun i => (x i).2) ∉ K → Φ x = 0 := by
  classical
  have hc1 : Continuous fun u : κ → FiniteAdeleRing (𝓞 F) F => (u, (0 : κ → FiniteAdeleRing (𝓞 F) F)) :=
    continuous_id.prodMk continuous_const
  have hc2 : Continuous fun v : κ → FiniteAdeleRing (𝓞 F) F => ((0 : κ → FiniteAdeleRing (𝓞 F) F), v) :=
    continuous_const.prodMk continuous_id
  have hM1 : (fun u : κ → FiniteAdeleRing (𝓞 F) F => (u, (0 : κ → FiniteAdeleRing (𝓞 F) F))) ⁻¹'
      (M : Set _) ∈ 𝓝 (fun _ : κ => (0 : FiniteAdeleRing (𝓞 F) F)) :=
    (hM.preimage hc1).mem_nhds M.zero_mem
  have hM2 : (fun v : κ → FiniteAdeleRing (𝓞 F) F => ((0 : κ → FiniteAdeleRing (𝓞 F) F), v)) ⁻¹'
      (M : Set _) ∈ 𝓝 (fun _ : κ => (0 : FiniteAdeleRing (𝓞 F) F)) :=
    (hM.preimage hc2).mem_nhds M.zero_mem
  obtain ⟨O₁, hO₁, hbox₁⟩ := fixSupp_exists_box hM1
  obtain ⟨O₂, hO₂, hbox₂⟩ := fixSupp_exists_box hM2
  obtain ⟨N, hN, hNO⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F O₁ hO₁
  obtain ⟨K₀, hK₀, hK₀mem⟩ := hann O₂ hO₂
  let c : FiniteAdeleRing (𝓞 F) F := algebraMap F _ ((N : F)⁻¹)
  have hcN : (N : FiniteAdeleRing (𝓞 F) F) * c = 1 := by
    rw [← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)) N, ← map_mul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.2 hN.ne'), map_one]
  have hNc : c * (N : FiniteAdeleRing (𝓞 F) F) = 1 := by rw [mul_comm]; exact hcN
  let h : (κ → FiniteAdeleRing (𝓞 F) F) ≃ₜ (κ → FiniteAdeleRing (𝓞 F) F) :=
    { toFun := fun u i => c * u i
      invFun := fun u i => (N : FiniteAdeleRing (𝓞 F) F) * u i
      left_inv := fun u => funext fun i => by
        show (N : FiniteAdeleRing (𝓞 F) F) * (c * u i) = u i
        rw [← mul_assoc, hcN, one_mul]
      right_inv := fun u => funext fun i => by
        show c * ((N : FiniteAdeleRing (𝓞 F) F) * u i) = u i
        rw [← mul_assoc, hNc, one_mul]
      continuous_toFun := continuous_pi fun i => continuous_const.mul (continuous_apply i)
      continuous_invFun := continuous_pi fun i => continuous_const.mul (continuous_apply i) }
  let φ : (κ → FiniteAdeleRing (𝓞 F) F) →+ (κ → FiniteAdeleRing (𝓞 F) F) :=
    { toFun := fun u i => c * u i
      map_zero' := by funext i; exact mul_zero c
      map_add' := fun u w => by funext i; exact mul_add c (u i) (w i) }
  let U : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F) :=
    (AddSubgroup.pi Set.univ fun _ => (Formalism.UG.intAd F).toAddSubgroup).comap φ
  have hUset : (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) =
      h ⁻¹' Set.univ.pi fun _ => (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F)) := rfl
  have hint_c : IsCompact (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F)) := Formalism.L2.Col.rlt_isCompact_intAd
  have hint_o : IsOpen (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F)) := Formalism.L2.SG.Pf.top_isOpen_intAd F
  refine ⟨U, Set.univ.pi fun _ => K₀, ?_, ?_, isCompact_univ_pi fun _ => hK₀, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · rw [hUset]; exact (isOpen_set_pi Set.finite_univ fun _ _ => hint_o).preimage h.continuous
  · rw [hUset]; exact h.isCompact_preimage.2 (isCompact_univ_pi fun _ => hint_c)
  · intro x u hu
    have hu1 : ∀ i, u i ∈ O₁ := by
      intro i
      have hi : c * u i ∈ Formalism.UG.intAd F := hu i (Set.mem_univ i)
      have := hNO (c * u i) hi
      rwa [nsmul_eq_mul, ← mul_assoc, hcN, one_mul] at this
    have hm : (u, (0 : κ → FiniteAdeleRing (𝓞 F) F)) ∈ M := hbox₁ u hu1
    have := congrFun (hΦ _ hm) x
    simp only [GlobalTheory.WeilM.schr, finE2, fixSupp_finE_zero, dotProduct_zero, mul_zero, add_zero,
      AddChar.map_zero_eq_one, one_mul] at this
    exact this
  · intro x hx
    by_contra hne
    apply hx
    intro j _
    apply hK₀mem
    intro t ht
    have hv : ∀ i, (Pi.single j t : κ → FiniteAdeleRing (𝓞 F) F) i ∈ O₂ := by
      intro i
      by_cases hij : i = j
      · subst hij; rw [Pi.single_eq_same]; exact ht
      · rw [Pi.single_eq_of_ne hij]; exact mem_of_mem_nhds hO₂
    have hm : ((0 : κ → FiniteAdeleRing (𝓞 F) F), (Pi.single j t : κ → FiniteAdeleRing (𝓞 F) F)) ∈ M :=
      hbox₂ _ hv
    have h1 := congrFun (hΦ _ hm) x
    simp only [GlobalTheory.WeilM.schr, finE2, fixSupp_finE_zero, zero_dotProduct, mul_zero, add_zero] at h1
    rw [fixSupp_finE_single, dotProduct_single] at h1
    have hdot : x j * pairA F 0 t = pairA F 0 (t * (x j).2) :=
      Prod.ext (by show (x j).1 * 0 = 0; exact mul_zero _) (by show (x j).2 * t = t * (x j).2; exact mul_comm _ _)
    rw [hdot] at h1
    exact mul_right_cancel₀ hne (h1.trans (one_mul _).symm)

theorem fixed_invariant_compactSupport : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (κ : Type) [Fintype κ]
    (M : AddSubgroup ((κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F) × (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F))), IsOpen (M : Set ((κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F) × (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F))) →
      ∃ (U : AddSubgroup (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (K : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)), IsOpen (U : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ∧
        IsCompact (U : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ∧ IsCompact K ∧
        ∀ Φ : (κ → AF D.host.F) → ℂ, (∀ m ∈ M, GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilAdm.finE2 D.host.F m) Φ = Φ) →
          (∀ x, ∀ u ∈ U, Φ (x + GlobalTheory.WeilAdm.finE D.host.F u) = Φ x) ∧ ∀ x, (fun i => (x i).2) ∉ K → Φ x = 0 := by
  intro D ψ hψ κ _ M hM
  exact fixed_schroedinger_invariant_compactSupport_bounded_annihilator ψ (GlobalTheory.ScalarAnnih.exists_compact_of_annih D ψ hψ) κ M hM

end GlobalTheory.WeilAdm

end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.unitaryStabilizer_preserves_vacuumCondition_at_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (θ : 𝓞 E), (θ : E) + σ θ = 1 → ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v,
      ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        Acts (evFin F v) (om' (1, k)) φ φ₁ →
        (∀ γ ∈ latAtV G.V' G.W v, Acts (evFin F v) (G.M'.co.rho B.ψ γ) φ
          (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • φ)) →
        (∀ γ ∈ latAtV G.V' G.W v, Acts (evFin F v) (G.M'.co.rho B.ψ γ) φ₁
          (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • φ₁)) := by
  first | exact @GlobalTheory.InertSph.acts_vacCond_of_mem_KAt | exact GlobalTheory.InertSph.acts_vacCond_of_mem_KAt | (intros; apply GlobalTheory.InertSph.acts_vacCond_of_mem_KAt <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.local_theta_integral_at_inert_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ t : GL (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), (At (evFin F v) ((t : Matrix (Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1) ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, (t : Matrix (Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v ∧
        ((t⁻¹ : GL (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) →
      (adeleClass F).modu (Units.map (Algebra.norm (AF F) : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →* AF F) (Matrix.GeneralLinearGroup.det t)) = 1 := by
  first | exact @GlobalTheory.IntegralDetModule.modu_norm_det_triple | exact GlobalTheory.IntegralDetModule.modu_norm_det_triple | (intros; apply GlobalTheory.IntegralDetModule.modu_norm_det_triple <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.exists_etaleNbhd_killing_curveCohomologyClass : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (n i : ℤ), 0 < n → ∀ x : Ht q (sp B) n i, ∃ (A' : Type) (_ : CommRing A') (_ : Algebra B A'), IsExcisionNbhd B A' f ∧ pull _ (spMap (algebraMap B A')) _ _ x = 0 := by
  first | (exact @GlobalTheory.EtC.CurveNbhdExcision.main) | (exact GlobalTheory.EtC.CurveNbhdExcision.main) | (intros; apply GlobalTheory.EtC.CurveNbhdExcision.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

theorem _root_.GlobalTheory.T.cubeValueTimesThetaFrames_entire : AllC fun {R} _ _ {D} _ {N} ν => ∀ (g : ℕ) (d : AB N.toNumB g), Nonempty (Geo ν d) → ∀ x y : Fin g → ℂ, Differentiable ℂ (cubF d x y) := by
  first | exact @GlobalTheory.MBLow.Cl.CubHol.cubF_entire | exact GlobalTheory.MBLow.Cl.CubHol.cubF_entire | (intros; apply GlobalTheory.MBLow.Cl.CubHol.cubF_entire <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.twistedOrbitalIntegralPointTerm_doubleCoset_invariant : ∀ {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ), (∀ a ∈ twCent θ δ, ∀ b ∈ twCent θ δ, a * b = b * a) → (∀ y : G, (rStab fun k : K => f ((y * k)⁻¹ * δ * θ (y * k))).index ≠ 0) → ∀ t ∈ twCent θ δ, ∀ y, ∀ k ∈ K, GlobalTheory.EulerAbs.twTerm θ K δ f (t * y * k) = GlobalTheory.EulerAbs.twTerm θ K δ f y := by
  first | exact @GlobalTheory.EulerAbs.twTerm_inv | exact GlobalTheory.EulerAbs.twTerm_inv | (intros; apply GlobalTheory.EulerAbs.twTerm_inv <;> assumption)
end

section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

theorem _root_.GlobalTheory.T.exists_unitary_model_of_selfDualLatticeCount_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e → ∀ (n : ℕ) (Q : (w.adicCompletion E)[X]) (B : GlobalTheory.UnitLemma.InvAlg K) (u x : B.A), Fits w e B Q u → Q.natDegree = n → B.σ x = x → IsUnit x → B.N x ≠ 0 → ∃ γ : GLw n w, γ ∈ UL n w ∧ IsModel w e B u x γ := by
  first | exact @GlobalTheory.KapLat.exists_model_of_N_ne_zero | exact GlobalTheory.KapLat.exists_model_of_N_ne_zero | (intros; apply GlobalTheory.KapLat.exists_model_of_N_ne_zero <;> assumption)
end

section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

theorem _root_.GlobalTheory.T.exists_twistedConj_delta_of_unit_mod_norms : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A), ∀ (u : B.A) (Q : (w.adicCompletion E)[X]), Q.Separable → aeval u (Q.map e.symm.toRingHom) = 0 → Algebra.adjoin K.E {u} = ⊤ → ∀ β₀ : B.Aˣ, B.σ (β₀ : B.A) = β₀ * ((-1) ^ (m - 1) * u) → (∀ x : B.Aˣ, IsUnit (GlobalTheory.TwLat.gram e b ((β₀ : B.A) * x))) → ∀ y : GLw m w, (nrmL m w y).val.charpoly = Q → ∃ x : B.Aˣ, B.σ (x : B.A) = x ∧ ∃ g : GLw m w, y = g⁻¹ * GlobalTheory.TwLat.dlt e b ((β₀ : B.A) * x) * thL m w g := by
  first | exact @GlobalTheory.TwLat.ClSurj.exists_twConj_dlt | exact GlobalTheory.TwLat.ClSurj.exists_twConj_dlt | (intros; apply GlobalTheory.TwLat.ClSurj.exists_twConj_dlt <;> assumption)
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

theorem _root_.GlobalTheory.T.smoothing_affine_family_eq_integral_kernel : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (σ₀ : Fin n → Fin n → Cinf E) (L : Z →L[ℝ] (Fin n → Fin n → Cinf E)) (χ : Z → ℂ) (α : (Fin n → Fin n → Cinf E) → ℂ), HasCompactSupport χ → (∀ z ∈ tsupport χ, IsUnit (Matrix.of (σ₀ + L z))) → HasCompactSupport α → tsupport α ⊆ {x | IsUnit (Matrix.of x)} → ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (κ : X → ℂ) (τ : X → (Z × (Fin n → Fin n → Cinf E)) →L[ℝ] ℝ), Measurable κ → (∀ z, Measurable fun x => τ x z) → (∀ N : ℕ, Integrable (fun x => ‖κ x‖ * (1 + ‖τ x‖) ^ N) ν) → (∀ z a, χ z * ((jacInf (Matrix.of (σ₀ + L z)) : ℝ) : ℂ) * α a = ∫ x, κ x * (𝐞 (τ x (z, a)) : ℂ) ∂ν) → ∃ R : ℝ, ∀ W : GL (Fin n) (Cinf E) → ℂ, IsModGrowthInf W → ∀ q z g, χ z * smoothMatInf α W (g * (toGLInf (Matrix.of (σ₀ + L z)))⁻¹ * q) = ∫ p, secKInf R σ₀ κ τ q p * (𝐞 (secEtaInf L τ q p z) : ℂ) * W (g * toGLInf (Matrix.of p.1)) ∂((volume : Measure (Fin n → Fin n → Cinf E)).prod ν) := by
  first | exact @GlobalTheory.JSW.MirCinf.smoothMatInf_affine_eq_integral_secKInf | exact GlobalTheory.JSW.MirCinf.smoothMatInf_affine_eq_integral_secKInf | (intros; apply GlobalTheory.JSW.MirCinf.smoothMatInf_affine_eq_integral_secKInf <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DoublingEv

noncomputable section

namespace GlobalTheory.DoublingEv.PartLTame

open scoped Classical

variable {F : Type} [Field F] [NumberField F]

def reindexFun {R : Type} {ι ι' : Type} (e : ι ≃ ι') : ((ι → R) → ℂ) →ₗ[ℂ] ((ι' → R) → ℂ) :=
  LinearMap.funLeft ℂ ℂ (fun y : ι' → R => y ∘ e)

theorem reindexFun_apply {R : Type} {ι ι' : Type} (e : ι ≃ ι') (Φ : (ι → R) → ℂ) (y : ι' → R) :
    reindexFun e Φ y = Φ (y ∘ e) := rfl

theorem isTame_reindexFun {ι ι' : Type} [Fintype ι] [Fintype ι'] (e : ι ≃ ι') :
    IsTame F (reindexFun (R := AF F) e) := by
  intro g hg
  let L : (ι' → mixedEmbedding.mixedSpace F) ≃L[ℝ] (ι → mixedEmbedding.mixedSpace F) :=
    (LinearEquiv.funCongrLeft ℝ (mixedEmbedding.mixedSpace F) e).toContinuousLinearEquiv
  let H : (ι' → FiniteAdeleRing (𝓞 F) F) ≃ₜ (ι → FiniteAdeleRing (𝓞 F) F) :=
    { toFun := fun y => y ∘ e
      invFun := fun z => z ∘ e.symm
      left_inv := fun y => by funext i; simp
      right_inv := fun z => by funext i; simp
      continuous_toFun := continuous_pi fun i => continuous_apply (e i)
      continuous_invFun := continuous_pi fun i => continuous_apply (e.symm i) }
  refine ⟨Unit, inferInstance, fun _ => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L, fun _ => g ∘ H,
    fun _ => ⟨hg.1.comp_continuous H.continuous, hg.2.comp_homeomorph H⟩, fun f => ?_⟩
  funext y
  simp only [Finset.univ_unique, Finset.sum_singleton]
  rfl

theorem isTame_partL : ∀ (F : Type) [Field F] [NumberField F] (κ κ₁ κ' : Type) [Fintype κ] [Fintype κ₁] [Fintype κ']
    (T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ₁ → AF F) → ℂ)), IsTame F T → IsTame F (partL (κ' := κ') T) := by
  intro F _ _ κ κ₁ κ' _ _ _ T hT
  have h : partL (κ' := κ') T = reindexFun (Equiv.sumComm κ' κ₁) ∘ₗ partR (κ := κ') T ∘ₗ
      reindexFun (Equiv.sumComm κ κ') := by
    refine LinearMap.ext fun Φ => funext fun s => ?_
    simp only [LinearMap.comp_apply, reindexFun_apply, partR_apply, partL_apply]
    exact congrArg₂ (fun φ t => T φ t) (funext fun x => congrArg Φ (funext fun i => by cases i <;> rfl)) rfl
  rw [h]
  exact ((isTame_reindexFun _).comp (GlobalTheory.T.tame_part_right F κ' κ κ₁ T hT)).comp (isTame_reindexFun _)

end GlobalTheory.DoublingEv.PartLTame
end
end
