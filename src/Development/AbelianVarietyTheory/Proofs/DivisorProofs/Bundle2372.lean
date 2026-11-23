module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle359
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1363
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1591
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2129
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1640
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2336
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1457
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1718
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsJetsChangeSectionBasis
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantsEqDegenerationSeries
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle083
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1168
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle127
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle083
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ExistsGeneratorOfIsField
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThreeLeScaleOfPowBound
public import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle208
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle739
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1864
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPageRunRecord
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2340
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle056

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

open MeasureTheory

namespace GlobalTheory.WeilL2Words

section Core

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem schA_decomp {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ GlobalTheory.WeilM.schA F κ) :
    ∃ (n : ℕ) (f : Fin n → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : Fin n → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ),
      (∀ i, g i ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) ∧ Φ = ∑ i, GlobalTheory.WeilM.pureA F (f i) (g i) := by
  rw [GlobalTheory.WeilM.schA, Submodule.mem_span_set'] at hΦ
  obtain ⟨n, c, s, rfl⟩ := hΦ
  choose f g hg hfg using fun i => (s i).2
  refine ⟨n, fun i => c i • f i, g, hg, Finset.sum_congr rfl fun i _ => ?_⟩
  rw [hfg i]
  ext a
  simp [GlobalTheory.WeilM.pureA, mul_assoc]

theorem list_sum_ne_top {l : List ENNReal} (h : ∀ a ∈ l, a ≠ ⊤) : l.sum ≠ ⊤ := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.sum_cons]
    exact ENNReal.add_ne_top.2 ⟨h a (by simp), ih fun b hb => h b (by simp [hb])⟩

variable [Invertible (2 : AdeleRing (𝓞 F) F)] {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ}

theorem dS_mem (hψ : IsStdInf F ψ) (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ}
    (hΦ : Φ ∈ GlobalTheory.WeilM.schA F κ) : dS F ψ h Φ ∈ GlobalTheory.WeilM.schA F κ := by
  obtain ⟨n, f, g, hg, rfl⟩ := schA_decomp hΦ
  obtain ⟨f', hf'⟩ := GlobalTheory.T.archDerivative_keeps_sums_fixed_finite_parts F κ ψ hψ n g f h
  rw [hf']
  exact Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨f' i, g i, hg i, rfl⟩

theorem word_mem (hψ : IsStdInf F ψ) : ∀ (w : List ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))) {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ},
    Φ ∈ GlobalTheory.WeilM.schA F κ → word F ψ w Φ ∈ GlobalTheory.WeilM.schA F κ
  | [], _, hΦ => hΦ
  | h :: w, _, hΦ => by
    rw [word_cons]
    exact dS_mem hψ h (word_mem hψ w hΦ)

theorem word_sum (hψ : IsStdInf F ψ) {m : ℕ} (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    ∀ (w : List ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))) (f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ), ∃ f' : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      word F ψ w (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) = ∑ i, GlobalTheory.WeilM.pureA F (f' i) (g i) := by
  intro w f
  induction w with
  | nil => exact ⟨f, rfl⟩
  | cons h w ih =>
    obtain ⟨f1, e1⟩ := ih
    obtain ⟨f2, e2⟩ := GlobalTheory.T.archDerivative_keeps_sums_fixed_finite_parts F κ ψ hψ m g f1 h
    exact ⟨f2, by rw [word_cons, e1, e2]⟩

theorem word_law (hψ : IsStdInf F ψ) {G : Type} [Group G] (om : G →* Module.End ℂ ((κ → AdeleRing (𝓞 F) F) → ℂ))
    (pres : ∀ p, ∀ φ ∈ GlobalTheory.WeilM.schA F κ, om p φ ∈ GlobalTheory.WeilM.schA F κ)
    (M : G → ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ] ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)))
    (himpl : ∀ p h, ∀ φ ∈ GlobalTheory.WeilM.schA F κ,
      om p (GlobalTheory.WeilM.schr ψ (archPair F (M p h)) φ) = GlobalTheory.WeilM.schr ψ (archPair F h) (om p φ))
    (μ : @Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ)
    (hiso : ∀ p, ∀ φ ∈ GlobalTheory.WeilM.schA F κ, l2A F μ (om p φ) = l2A F μ φ) (p : G) :
    ∀ (w : List ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))) {φ : (κ → AdeleRing (𝓞 F) F) → ℂ}, φ ∈ GlobalTheory.WeilM.schA F κ →
      word F ψ w (om p φ) = om p (word F ψ (w.map (M p)) φ)
  | [], _, _ => rfl
  | h :: w, φ, hφ => by
    rw [List.map_cons, word_cons, word_cons, word_law hψ om pres M himpl μ hμ hiso p w hφ]
    exact GlobalTheory.T.weilRep_derivative_law_of_L2Isometric F κ ψ hψ om pres M himpl μ hμ hiso p h _ (word_mem hψ _ hφ)

theorem slice_l2_of (hψ : IsStdInf F ψ) {G : Type} [Group G] [TopologicalSpace G]
    (om : G →* Module.End ℂ ((κ → AdeleRing (𝓞 F) F) → ℂ))
    (pres : ∀ p, ∀ φ ∈ GlobalTheory.WeilM.schA F κ, om p φ ∈ GlobalTheory.WeilM.schA F κ)
    (M : G → ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ] ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)))
    (himpl : ∀ p h, ∀ φ ∈ GlobalTheory.WeilM.schA F κ,
      om p (GlobalTheory.WeilM.schr ψ (archPair F (M p h)) φ) = GlobalTheory.WeilM.schr ψ (archPair F h) (om p φ))
    (hM : ∀ h, Continuous fun p => M p h)
    (μ : @Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ)
    (hiso : ∀ p, ∀ φ ∈ GlobalTheory.WeilM.schA F κ, l2A F μ (om p φ) = l2A F μ φ)
    {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ GlobalTheory.WeilM.schA F κ) (p0 : G)
    (hfin : ∃ N ∈ nhds p0, ∃ (m : ℕ) (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (yy : Fin m → (κ → FiniteAdeleRing (𝓞 F) F)),
      (∀ i, g i ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) ∧ (∀ i j, g i (yy j) = if i = j then 1 else 0) ∧
      ∀ p ∈ N, ∃ f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, om p Φ = ∑ i, GlobalTheory.WeilM.pureA F (f i) (g i))
    (y : (κ → FiniteAdeleRing (𝓞 F) F)) (i j : ℕ) :
    ∃ B : ℝ, ∀ᶠ p in nhds p0,
      ∫ x, (‖x‖ ^ i * ‖iteratedFDeriv ℝ j (fun x => om p Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x‖) ^ 2 ≤ B := by
  obtain ⟨L, C, hL⟩ := GlobalTheory.T.adelic_schwartz_l2_word_bound_exists F κ ψ hψ i j
  obtain ⟨N, hN, m, g, yy, hg, hdual, hf⟩ := hfin
  obtain ⟨CG, hCG, hG⟩ := GlobalTheory.T.finite_adelic_dual_basis_integral F κ m g yy hg hdual μ hμ y
  set R : ℝ := ∑ h ∈ L.flatten.toFinset, (‖M p0 h‖ + 1) with hR
  have hev : ∀ᶠ p in nhds p0, ∀ h ∈ L.flatten.toFinset, ‖M p h‖ ≤ R := by
    refine (Filter.eventually_all_finset _).2 fun h hh => ?_
    have hc : ContinuousAt (fun p => ‖M p h‖) p0 := ((hM h).norm).continuousAt
    filter_upwards [hc.eventually_lt continuousAt_const (lt_add_one ‖M p0 h‖)] with p hp
    exact hp.le.trans (Finset.single_le_sum (f := fun h => ‖M p0 h‖ + 1) (fun _ _ => by positivity) hh)
  have hB : ∀ w ∈ L, ∃ B : ENNReal, B ≠ ⊤ ∧ ∀ ws : List ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)), ws.length = w.length →
      (∀ h ∈ ws, ‖h‖ ≤ R) → l2A F μ (word F ψ ws Φ) ≤ B :=
    fun w _ => GlobalTheory.T.exists_finite_l2A_bound_words F κ ψ hψ Φ hΦ μ hμ w.length R
  choose! B hBtop hBle using hB
  have htop : ENNReal.ofReal C * (L.map fun w => CG * B w).sum ≠ ⊤ := by
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (list_sum_ne_top fun a ha => ?_)
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 ha
    exact ENNReal.mul_ne_top hCG (hBtop w hw)
  refine ⟨(ENNReal.ofReal C * (L.map fun w => CG * B w).sum).toReal, ?_⟩
  filter_upwards [hev, hN] with p hp hpN
  have key := hL (om p Φ) (pres p Φ hΦ) y
  have hsum : (L.map fun w => ∫⁻ x, ‖word F ψ w (om p Φ) (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2).sum ≤
      (L.map fun w => CG * B w).sum := by
    refine List.sum_le_sum fun w hw => ?_
    obtain ⟨f, hfp⟩ := hf p hpN
    obtain ⟨f', hf'⟩ := word_sum hψ g w f
    have e1 : word F ψ w (om p Φ) = ∑ i, GlobalTheory.WeilM.pureA F (f' i) (g i) := by rw [hfp, hf']
    calc ∫⁻ x, ‖word F ψ w (om p Φ) (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2
        ≤ CG * l2A F μ (word F ψ w (om p Φ)) := by rw [e1]; exact hG f'
      _ = CG * l2A F μ (word F ψ (w.map (M p)) Φ) := by
          rw [word_law hψ om pres M himpl μ hμ hiso p w hΦ, hiso p _ (word_mem hψ _ hΦ)]
      _ ≤ CG * B w := by
          gcongr
          refine hBle w hw _ (List.length_map _) fun h hh => ?_
          obtain ⟨h0, h0m, rfl⟩ := List.mem_map.1 hh
          exact hp h0 (List.mem_toFinset.2 (List.mem_flatten.2 ⟨w, hw, h0m⟩))
  exact (ENNReal.ofReal_le_iff_le_toReal htop).1 (key.trans (by gcongr))

end Core

end GlobalTheory.WeilL2Words

theorem GlobalTheory.WeilL2Words.weilTransport_archimedeanSlice_sobolev_bounds_alt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
 ∀ om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ),
                       GlobalTheory.WeilSchrodinger.IsTransport ψ co ω om →
  ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ (y : κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F) p0 (i j : ℕ), ∃ B : ℝ,
      ∀ᶠ p in nhds p0, ∫ x, (‖x‖ ^ i * ‖iteratedFDeriv ℝ j (fun x => om p Φ (GlobalTheory.WeilCont.adeleJoin D.host.F x y)) x‖) ^ 2 ≤ B := by
  intro D ψ hψ S T χS χT hS hT hrS hrT JA JB ξ hA hJB κ _ co hco ω hω om hom Φ hΦ y p0 i j
  have hI := GlobalTheory.T.transportedWeil_preserves_schwartz_heisenberg_equivariant D ψ hψ S T χS χT hS hT hrS hrT JA JB ξ hA hJB κ co hco ω hω om hom
  obtain ⟨M, himpl, hM⟩ := GlobalTheory.T.transported_archHeisenbergDirections_continuous D ψ _ _ JA JB ξ κ co om hI.2
  obtain ⟨μ, hμ, hiso⟩ := GlobalTheory.T.l2A_transport_gram_transpose D ψ hψ S T χS χT hS hT hrS hrT JA JB ξ hA hJB κ co hco ω hω om hom
  exact GlobalTheory.WeilL2Words.slice_l2_of (GlobalTheory.T.isStandardArchimedeanAddChar_of_standardChar D ψ hψ) om hI.1 M himpl hM μ hμ hiso hΦ p0
    (GlobalTheory.T.exists_local_finiteDim_finiteParts_weilOperators D ψ hψ S T χS χT hS hT hrS hrT JA JB ξ hA hJB κ co hco ω hω om hom Φ hΦ p0) y i j
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.ThetaOfJet

open GlobalTheory.MBLow.JetUniq

theorem isGenSec_of_polAVSectionInverseImage {K : Type} [Field K] (x : KeyIn K)
    (th : LB.Sec (LPow x.P.A x.P.L ((1 : ℕ) : ℤ) (baseOver (Sp K))))
    (h : IsPolAVSectionInverseImage x.P (baseOver (Sp K)) x.th th) : IsGenSec x.P.A x.P.L 1 th := by
  have e : th = TrSec.thSec x.P x.th := by
    refine NormTheta.sec_ext fun j => ?_
    obtain ⟨i, rfl⟩ : ∃ i : x.P.L.ι, j = fun _ => i := ⟨j 0, funext fun k => congrArg j (Subsingleton.elim _ _)⟩
    exact (h i (TrSec.chart_le x.P _)).trans (TrSec.projectionPullbackSectionBaseProduct_isInverseImage x.P x.th i (TrSec.chart_le x.P _)).symm
  subst e
  haveI : Subsingleton (Over.mk (𝟙 (Sp K))).left := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  refine (GenSecFibre.isGenSec_iff_fibres firstFiveLaws.2.1 (Sp K) x.P K (𝟙 _) _).2 fun p => ?_
  obtain ⟨z, -, hz⟩ := x.th_ne p
  exact ⟨_, Subsingleton.elim _ _, TrSec.nonzero_thSec x.P x.th z hz⟩

theorem ptSecT_left {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] (z : baseOver (Sp R) ⟶ A) :
    (ptSecT A z).left = z.left ≫ toProd A := by
  rw [toProd, ← Over.comp_left, comp_lift, Category.comp_id, ptSecT]
  congr 2
  ext
  simpa using (Over.w z).symm

open GlobalTheory.MBLow.JetUniq

theorem fnOf_valR_id {K : Type} [Field K] (f : Γ(Sp K, ⊤)) : GlobalTheory.Ex.fnOf (valR (𝟙 (Sp K)) ⊤ f) = f := by
  have h : ⊤ ≤ (𝟙 (Sp K)) ⁻¹ᵁ ⊤ := fun _ _ => trivial
  rw [valR, dite_eq_left h]
  simp [GlobalTheory.Ex.fnOf, Scheme.Hom.appLE]
  rfl

theorem isThetaPt_of_thJet : ∀ (K : Type) [Field K] (x : KeyIn K) (g : ℕ) (hg : x.P.g = g) (m : ℕ), Odd m → (m : K) ≠ 0 → ∀ (I : Type) (pt : I → (baseOver (Sp K) ⟶ x.P.A)) (ϑ : I → K) (J : I → Fin g → K), ThJet x hg m pt ϑ J → IsThetaPt x.P m pt fun i => fnOf (ϑ i) := by
  intro K _ x g hg m hm hK I pt ϑ J hJ
  obtain ⟨th, hth, U, t, i₀, c, hUT, hi₀, H⟩ := hJ
  have hLaw : Laws := firstFiveLaws.1
  have hL := x.P.isLB
  let T : Over (Sp K) := baseOver (Sp K)
  obtain ⟨α₀, hα₀⟩ := hLaw.mulPull _ x.P m
  have e₁ : (snd T x.P.A).left ≫ (mulA x.P.A m).left = (snd T x.P.A ^ m).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  obtain ⟨α₁, hα₁, -⟩ := exists_gen hL (φ' := ![(snd T x.P.A).left, (snd T x.P.A ^ m).left])
    (ε' := ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)])
    (fun U _ f => by
      refine Finset.prod_congr rfl fun i _ => ?_
      fin_cases i
      · exact congrArg₂ (fun q n => f q ^ n) (Category.comp_id _) (Nat.cast_pow m 2).symm
      · exact congrArg (fun q => f q ^ (-1 : ℤ)) e₁)
    (LB.pullGen x.P.L ![𝟙 x.P.A.left, (mulA x.P.A m).left] ![(m : ℤ) ^ 2, -1] α₀ (snd T x.P.A).left)
    (DVR.pullGen_isGen _ _ _ _ hα₀ _)
  obtain ⟨α, hα, hn⟩ := NormTheta.exists_normalised hL x.rig_gen m _ _ (((m ^ 2 : ℕ) : ℤ) - 1) rfl α₁ hα₁
  obtain ⟨s₁, hs₁⟩ := ThetaPtExist.exists_isTwistPull hL (mulT x.P.A T m) (snd T x.P.A ^ m) (lift_snd _ _)
    ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α hα th
  choose s₂ hs₂ using fun i => ThetaPtExist.exists_isTwistPull hL (translT x.P.A (U i).pt) (translPt x.P.A (U i).pt)
    (lift_snd _ _) ((m ^ 2 : ℕ) : ℤ) ((m ^ 2 : ℕ) : ℤ) (U i).φ (U i).isGen s₁
  have ht : ∀ i, t i = s₂ i := fun i => NormTheta.sec_ext (tr_unique x.P x.rig hm (fun _ => rfl) (hUT i).1 (hUT i).1
    (hUT i).2 ⟨α, s₁, hα, hn, hs₁, hs₂ i⟩)
  let τ := rigT x.P.A x.P.L x.rig T ((m ^ 2 : ℕ) : ℤ)
  have hτ : τ.IsGen := NormTheta.rigT_isGen x.rig_gen _
  choose w hw using fun i => ThetaPtExist.exists_isValueAt hL (s₂ i) 1 τ hτ
  have k₀ : ⊤ ≤ eSec x.P.A ⁻¹ᵁ x.P.L.U i₀ := fun z hz => hi₀ hz
  let r : K := valR (𝟙 (Sp K)) ((x.P.L.pull (eSec x.P.A)).U fun _ => i₀) (x.rig.s fun _ => i₀).val
  have hr₀ : r ≠ 0 := (isUnit_valR (𝟙 (Sp K)) ((x.P.L.pull (eSec x.P.A)).U fun _ => i₀)
    (fun z hz => Set.mem_iInter.2 fun _ => k₀ hz) _).ne_zero
  let V₁ := (x.P.L.LinComb (fun _ : Fin 1 => (1 : T ⟶ x.P.A).left) fun _ => ((m ^ 2 : ℕ) : ℤ)).U fun _ => i₀
  let q : K := valR (𝟙 (Sp K)) V₁ (τ.s fun _ => i₀).val
  have hq₀ : q ≠ 0 := (isUnit_valR (𝟙 (Sp K)) V₁ (fun z hz => Set.mem_iInter.2 fun _ => k₀ hz) _).ne_zero
  have hp : (ptSecT x.P.A (1 : T ⟶ x.P.A)).left = eSec x.P.A ≫ toProd x.P.A := by
    rw [ptSecT_left, NormTheta.one_left]
    exact congrArg (· ≫ toProd x.P.A) (Category.id_comp _)
  let j₀ : Fin g := ⟨0, hg ▸ x.g_pos⟩
  have hval : ∀ i, valR (𝟙 (Sp K)) ⊤ (w i) * q = r ^ (m ^ 2) * ϑ i := fun i => by
    have e2 := GlobalTheory.ZH.TorsReg.valR_valueAt x.P.A x.P.L _ (hw i) (𝟙 (Sp K)) i₀ (by
      rintro _ ⟨z, rfl⟩; exact k₀ trivial)
    rw [Category.id_comp, hp, ← ht i] at e2
    let V := LB.wchart x.P.L (fun _ : Fin 1 => (snd (baseOver (Sp K)) x.P.A).left) fun _ => i₀
    have e : (valR (epsLift (x.v (Fin.cast hg.symm j₀))) V ((t i).f fun _ => i₀)).fst = r ^ (m ^ 2) * ϑ i := by
      have := congrArg TrivSqZeroExt.fst (H i j₀)
      simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inr,
        add_zero] at this
      exact this
    rw [epsLift_eq] at e
    erw [GlobalTheory.HolHom.valR_comp (A := DualNumber K) (x.v (Fin.cast hg.symm j₀)).left (toProd x.P.A) V] at e
    rw [fst_valR (x.basis.1 _) (le_toProd k₀)] at e
    erw [← GlobalTheory.HolHom.valR_comp (A := K) (eSec x.P.A) (toProd x.P.A) V] at e
    exact e2.symm.trans e
  have un : ∀ a : K, a ≠ 0 → IsUnit (fnOf a) := fun a ha =>
    (IsUnit.mk0 _ ha).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  have hmu : IsUnit (m : Γ(T.left, ⊤)) := by
    have := un m hK
    rwa [GlobalTheory.Ex.fnOf, map_natCast] at this
  haveI : Subsingleton T.left := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  refine ThetaSeries.isThetaPt_of_data x.P hm hmu (Nat.cast_pow m 2) th s₁ α τ U s₂ w
    (un _ (div_ne_zero hq₀ (pow_ne_zero (m ^ 2) hr₀))).unit
    ⟨isGenSec_of_polAVSectionInverseImage x th hth, hα, hτ, hs₁, fun i => (hUT i).1, hs₂, hw, fun i => ?_⟩
  rw [IsUnit.unit_spec, ← fnOf_valR_id (w i), ← map_mul]
  congr 1
  field_simp
  linear_combination (hval i).symm

end GlobalTheory.MBLow.ThetaOfJet
end
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies

namespace GlobalTheory.OntoSizeRows

theorem sizeRows_at {D : D7} {L : SizeData₂ D} {Pm : ParameterChoice' D L} (Tp : ParamsT D L Pm) (hK : DV.KapDef D)
    (S : SizesAt L) (hC : Pm.CnW = 10) (hg : ∀ j : Fin 2, ((D.host.g j : ℕ) : ℝ) ≤ Real.exp (9 * L.sc.L))
    (hn : L.sc.x ^ (2 + 8 * L.sc.eps) ≤ D.R.n ∧ (D.R.n : ℝ) ≤ 2 * L.sc.x ^ (2 + 8 * L.sc.eps))
    (hm : Real.sqrt (L.sc.x * L.sc.delta1) ≤ D.R.m)
    (h1 : L.sc.x ^ (L.sc.eps / 4) + L.sc.x ^ (L.sc.eps / 3) + 1 + 3 * Real.log L.sc.x ≤ L.sc.x ^ L.sc.eps / 5)
    (h2 : 11 ≤ L.sc.x ^ (L.sc.ez / 5)) (h6 : 8 * Real.log L.sc.x ^ 2 < L.sc.x ^ 2)
    (h8 : 2 * L.sc.x ^ (L.sc.eps / 5 + L.sc.eps / 100) ≤ Real.sqrt (L.sc.x * L.sc.delta1))
    (h11 : 44 ≤ Real.sqrt (L.sc.x * L.sc.delta1)) : GlobalTheory.IndexAssembly.SizeRows Tp hK := by
  obtain ⟨-, -, -, -, -, -, sQD, -, -, -, -, sDe2, sLw, -⟩ := S
  have hx1 := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have he := L.sc.eps_pos
  have hel := L.sc.eps_lt
  have hm0 : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (show 1 ≤ D.R.m by have := D.R.two_le_m; omega)
  have hn0 : (0 : ℝ) < D.R.n := by have : 1 ≤ D.R.n := Formalism.HC.Frame.ord_pos _; exact_mod_cast this
  refine ⟨?_, h2, GlobalTheory.T.two_pi_mul_weightLength_le_maxWeightDegree_sq D L Pm Tp hK, by rw [hC], sDe2, ?_, ?_, ?_, GlobalTheory.FinalJoin.RecordRun.k_b'_le Pm
    (GlobalTheory.IndexAssembly.three_le_scale_of_pow_bound h2), ?_, by exact_mod_cast (show (44 : ℝ) ≤ D.R.m by linarith), hn0.le⟩
  ·
    have hlogeta := Pm.logeta
    have heta := L.etaSz_pos
    have a1 : L.etaSz ≤ Real.exp (L.sc.x ^ (L.sc.eps / 4)) := (Real.log_le_iff_le_exp heta).1 hlogeta
    have a2 : (D.R.n : ℝ) ≤ Real.exp (1 + 3 * Real.log L.sc.x) := by
      have e3 : Real.exp (3 * Real.log L.sc.x) = L.sc.x ^ 3 := by
        rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul, Real.exp_log hx0]
      rw [Real.exp_add, e3]
      have b1 : L.sc.x ^ (2 + 8 * L.sc.eps) ≤ L.sc.x ^ (3 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at b1
      have b2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      have b3 : 0 ≤ L.sc.x ^ 3 := by positivity
      nlinarith [hn.2]
    have key : L.etaSz * L.sc.X' * D.R.n ≤ Real.exp (L.sc.L / 5) := by
      have hX : 0 < L.sc.X' := Real.exp_pos _
      calc L.etaSz * L.sc.X' * D.R.n
          ≤ Real.exp (L.sc.x ^ (L.sc.eps / 4)) * L.sc.X' * Real.exp (1 + 3 * Real.log L.sc.x) := by gcongr
        _ = Real.exp (L.sc.x ^ (L.sc.eps / 4) + L.sc.x ^ (L.sc.eps / 3) + (1 + 3 * Real.log L.sc.x)) := by
          unfold Scale.X'; simp only [Real.exp_add]
        _ ≤ Real.exp (L.sc.L / 5) := by
          apply Real.exp_le_exp.2
          unfold Scale.L
          linarith
    have hb45 : L.sc.b ^ ((4 : ℝ) / 5) = Real.exp (L.sc.L * (4 / 5)) := by
      unfold Scale.b; rw [← Real.exp_mul]
    have hX : 0 < L.sc.X' := Real.exp_pos _
    unfold Scale.w'' Scale.b' Scale.a
    rw [hb45, div_div, le_div_iff₀ (by positivity)]
    have e5 : Real.exp (L.sc.L / 5) * Real.exp (L.sc.L * (4 / 5)) = L.sc.b := by
      unfold Scale.b; rw [← Real.exp_add]; ring_nf
    calc L.etaSz * Real.exp (L.sc.L * (4 / 5)) * (L.sc.X' * (L.sc.x * D.R.n))
        = L.sc.x * (L.etaSz * L.sc.X' * D.R.n) * Real.exp (L.sc.L * (4 / 5)) := by ring
      _ ≤ L.sc.x * Real.exp (L.sc.L / 5) * Real.exp (L.sc.L * (4 / 5)) := by gcongr
      _ = L.sc.x * L.sc.b := by rw [mul_assoc, e5]
  · apply GlobalTheory.T.thickSet_density_le_inv_four_Lw
    have a1 : L.sc.x ^ (2 : ℝ) ≤ L.sc.x ^ (2 + 8 * L.sc.eps) :=
      Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
    rw [Real.rpow_two] at a1
    have : ((8 * D.host.Lw : ℕ) : ℝ) < D.R.n := by
      push_cast
      unfold SizeLw at sLw
      linarith
    exact_mod_cast this
  · intro i
    have e : Real.exp (9 * L.sc.L) = L.sc.b ^ 9 := by
      unfold Scale.b; rw [← Real.exp_nat_mul]; norm_num
    rw [← e]; exact hg i
  ·
    have hq : (0 : ℝ) < D.host.q := lt_trans (by positivity) Pm.qd_pow.1
    have hd : (0 : ℝ) < D.host.d := lt_trans (by positivity) Pm.qd_pow.2
    obtain ⟨-, -, q2, -, d2, -⟩ := sQD
    unfold szTh at q2 d2
    push_cast
    rw [Real.log_mul hq.ne' hd.ne']
    linarith
  ·
    have hD := Pm.Del_ge.2.2.2
    have hl := Pm.logDel
    have hN0 : (0 : ℝ) ≤ D.R.N D.R.m := Nat.cast_nonneg _
    have hm10 : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 10 := one_le_pow₀ hm0
    have a1 : (D.R.N D.R.m : ℝ) ≤ (D.s.Del : ℝ) := le_trans (le_mul_of_one_le_right hN0 hm10) hD
    have hX : 0 < L.sc.X' := Real.exp_pos _
    rcases le_or_gt (D.s.Del : ℝ) 0 with h0 | h0
    · linarith
    · have a2 : (D.s.Del : ℝ) ≤ Real.exp (L.sc.x ^ (L.sc.eps / 4) / 2) := (Real.log_le_iff_le_exp h0).1 hl
      have a3 : L.sc.x ^ (L.sc.eps / 4) ≤ L.sc.x ^ (L.sc.eps / 3) :=
        Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
      have a4 : 0 ≤ L.sc.x ^ (L.sc.eps / 4) := by positivity
      have a5 : Real.exp (L.sc.x ^ (L.sc.eps / 4) / 2) ≤ L.sc.X' := by
        unfold Scale.X'; exact Real.exp_le_exp.2 (by linarith)
      linarith

theorem sizeRows_along : Closed FamHyp fun Fm _ => ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x → ∀ ι : Fm.Ix x,
    GlobalTheory.IndexAssembly.SizeRows (Fm.parT x hx ι) (Fm.ex x hx ι).kap_def := by
  refine ⟨1 / 100, by norm_num, fun eps he hle => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH hc _ => ?_⟩⟩
  have hez : 0 < Fm.ez := by
    obtain ⟨i⟩ := Fm.Ix_zero
    rw [← Fm.L_ez 0 i]
    exact (Fm.L 0 i).sc.ez_pos
  have hev : ∀ᶠ x : ℝ in Filter.atTop, 11 ≤ x ^ (Fm.ez / 5) :=
    (tendsto_rpow_atTop (by positivity : 0 < Fm.ez / 5)).eventually_ge_atTop 11
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.1 ((GlobalTheory.T.eventually_rpow_log_inequalities eps he (by linarith)).and hev)
  refine ⟨x0, fun x hx hx0' ι => ?_⟩
  have hsx := Fm.L_x x ι hx
  have hse := Fm.L_eps x ι
  obtain ⟨⟨a1, -, a6, a8, a11⟩, a2⟩ := hx0 x hx0'
  obtain ⟨w1, w2, -⟩ := hc.2.1 x hx ι
  have hd : (Fm.L x ι).sc.delta1 = x ^ (-(eps / 8)) := by unfold Scale.delta1; rw [hsx, hse]
  refine sizeRows_at _ _ (Fm.sizes x hx ι) (Fm.fixed.2.2.2.2.2.2.2 x hx ι).1
    ((hc.1.2.2.2.2.2.2.2.2 x hx ι).2.2.1) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hsx, hse]; exact w1
  · rw [hsx]; exact w2.1
  · rw [hsx, hse]; exact a1
  · rw [hsx, Fm.L_ez x ι]; exact a2
  · rw [hsx]; exact a6
  · rw [hd, hsx, hse]; exact a8
  · rw [hd, hsx]; exact a11

end GlobalTheory.OntoSizeRows
end
end

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

theorem _root_.GlobalTheory.T.finiteCovolume_normOneLevi_wittFrameStabilizer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ (π : Measure (GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r})) (DM : Set (GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r})), π.IsHaarMeasure → IsFundamentalDomain ((ratPts σ J).subgroupOf (GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r})) DM π → π DM ≠ ⊤ := by
  first | exact @GlobalTheory.ResidueEisenstein.finCovol_leviOne_last | exact GlobalTheory.ResidueEisenstein.finCovol_leviOne_last | (intros; apply GlobalTheory.ResidueEisenstein.finCovol_leviOne_last <;> assumption)
end
