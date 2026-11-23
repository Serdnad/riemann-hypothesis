module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle020
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1692
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegrandIntegrable
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle022
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle008
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle009
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle023
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle026
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle652
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConnPhiExtensionGeneratorEqZeta
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIterateDerivative
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DecompositionInvariantsCondition
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle654
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle653
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle517
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle628

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.AdjUp

noncomputable section

namespace GlobalTheory.AdelicL2Norm

theorem adInner_eq_mul_integral {G H W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [Group H] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ν : Measure G) [ν.IsMulLeftInvariant]
    [ν.IsOpenPosMeasure] (π : G →* H) (hπ : Function.Surjective π) (Γ : Subgroup G) [Countable Γ] {𝓖 : Set G}
    (h𝓖 : IsFundamentalDomain Γ 𝓖 ν) (J₀ J : Subgroup H) (hle : J ≤ J₀) (ho : IsOpen (J.comap π : Set G))
    (h1 : ν (J₀.comap π) = 1) (ρ : G →* Module.End ℂ W) (hρ : ∀ h x y, inner ℂ (ρ h x) (ρ h y) = inner ℂ x y)
    (χ : J →* ℂˣ) (hχ : ∀ k, ‖(χ k : ℂ)‖ = 1) {I : Type} [Fintype I] (y : I → H)
    (hy : Formalism.IndefR.Bridge.IsReps (π.comp Γ.subtype) J y) :
    ∃ c : ℝ, 0 < c ∧ ∀ f ∈ Formalism.IndefR.Bridge.AdForms (π.comp Γ.subtype) (ρ.comp Γ.subtype) J χ,
      ∀ f' ∈ Formalism.IndefR.Bridge.AdForms (π.comp Γ.subtype) (ρ.comp Γ.subtype) J χ,
        IntegrableOn (fun h => inner ℂ (ρ h⁻¹ (f (π h))) (ρ h⁻¹ (f' (π h)))) 𝓖 ν ∧
        Formalism.IndefR.Bridge.adInner (π.comp Γ.subtype) J y f f' =
          (c : ℂ) * ∫ h in 𝓖, inner ℂ (ρ h⁻¹ (f (π h))) (ρ h⁻¹ (f' (π h))) ∂ν := by
  set m := ν (J.comap π) with hmdef
  have hm0 : m ≠ 0 := ho.measure_ne_zero ν ⟨1, by simp⟩
  have hmt : m ≠ ⊤ := ne_top_of_le_ne_top (h1 ▸ ENNReal.one_ne_top) (measure_mono (Subgroup.comap_mono hle))
  have h𝓖' : IsFundamentalDomain Γ 𝓖 (m⁻¹ • ν) := h𝓖.mono Measure.smul_absolutelyContinuous
  have h1' : (m⁻¹ • ν) (J.comap π) = 1 := by
    rw [Measure.smul_apply, smul_eq_mul, ← hmdef, ENNReal.inv_mul_cancel hm0 hmt]
  obtain ⟨-, key⟩ := GlobalTheory.InnerClassSum.integral_inner_eq_adInner (m⁻¹ • ν) π hπ Γ h𝓖' J ho h1' ρ hρ χ hχ y hy
  refine ⟨m.toReal⁻¹, inv_pos.2 (ENNReal.toReal_pos hm0 hmt), fun f hf f' hf' => ?_⟩
  obtain ⟨hi, he⟩ := key f hf f' hf'
  refine ⟨?_, ?_⟩
  · unfold IntegrableOn at hi ⊢
    rw [Measure.restrict_smul] at hi
    exact (integrable_smul_measure (ENNReal.inv_ne_zero.2 hmt) (ENNReal.inv_ne_top.2 hm0)).1 hi
  · rw [← he, Measure.restrict_smul, integral_smul_measure, ENNReal.toReal_inv, Complex.real_smul]

theorem integrableOn_coord {G H W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [Group H] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ν : Measure G) (π : G →* H)
    (J : Subgroup H) (ho : IsOpen (J.comap π : Set G)) (ρ : G →* Module.End ℂ W)
    (hρc : ∀ x, Continuous fun h => ρ h x) (χ : J →* ℂˣ) (hχ : ∀ k, ‖(χ k : ℂ)‖ = 1) (Γ : Subgroup G) (f f' : H → W)
    (hF : f ∈ Formalism.IndefR.Bridge.AdForms (π.comp Γ.subtype) (ρ.comp Γ.subtype) J χ)
    (hF' : f' ∈ Formalism.IndefR.Bridge.AdForms (π.comp Γ.subtype) (ρ.comp Γ.subtype) J χ)
    {𝓖 : Set G} (hi : IntegrableOn (fun h => inner ℂ (ρ h⁻¹ (f (π h))) (ρ h⁻¹ (f (π h)))) 𝓖 ν)
    (hi' : IntegrableOn (fun h => inner ℂ (ρ h⁻¹ (f' (π h))) (ρ h⁻¹ (f' (π h)))) 𝓖 ν) (a a' : W) :
    IntegrableOn (fun h => star (inner ℂ a (ρ h⁻¹ (f (π h)))) * inner ℂ a' (ρ h⁻¹ (f' (π h)))) 𝓖 ν := by
  have hr : ∀ g ∈ Formalism.IndefR.Bridge.AdForms (π.comp Γ.subtype) (ρ.comp Γ.subtype) J χ, ∀ (x : H) (k : J),
      g (x * k) = (χ k : ℂ) • g x := fun g hg x k => by
    have := hg 1 x k
    simpa using this
  have hf := hr f hF
  have hf' := hr f' hF'
  have hcont : Continuous fun h => star (inner ℂ a (ρ h⁻¹ (f (π h)))) * inner ℂ a' (ρ h⁻¹ (f' (π h))) := by
    refine continuous_iff_continuousAt.2 fun h₀ => ?_
    have hψ : Continuous fun h : G => star (inner ℂ a (ρ h⁻¹ (f (π h₀)))) * inner ℂ a' (ρ h⁻¹ (f' (π h₀))) :=
      (continuous_star.comp (continuous_const.inner ((hρc _).comp continuous_inv))).mul
        (continuous_const.inner ((hρc _).comp continuous_inv))
    refine hψ.continuousAt.congr ?_
    have hU : {h : G | h₀⁻¹ * h ∈ J.comap π} ∈ nhds h₀ :=
      (ho.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp)
    filter_upwards [hU] with h hh
    have e : π h = π h₀ * ((⟨π (h₀⁻¹ * h), hh⟩ : J) : H) := by
      simp [← map_mul]
    rw [e, hf, hf', map_smul, map_smul, inner_smul_right, inner_smul_right, star_mul']
    have hn : star ((χ ⟨π (h₀⁻¹ * h), hh⟩ : ℂˣ) : ℂ) * ((χ ⟨π (h₀⁻¹ * h), hh⟩ : ℂˣ) : ℂ) = 1 := by
      rw [show star _ = (starRingEnd ℂ) _ from rfl, Complex.conj_mul', hχ]; simp
    linear_combination -(star (inner ℂ a (ρ h⁻¹ (f (π h₀)))) * inner ℂ a' (ρ h⁻¹ (f' (π h₀)))) * hn
  have hsq : ∀ x : W, ‖inner ℂ x x‖ = ‖x‖ ^ 2 := fun x => by
    rw [inner_self_eq_norm_sq_to_K]; simp
  refine Integrable.mono' ((hi.norm.add hi'.norm).const_mul (‖a‖ * ‖a'‖)) hcont.aestronglyMeasurable.restrict ?_
  refine Filter.Eventually.of_forall fun h => ?_
  simp only [Pi.add_apply, hsq, norm_mul, norm_star]
  have h1 := norm_inner_le_norm (𝕜 := ℂ) a (ρ h⁻¹ (f (π h)))
  have h2 := norm_inner_le_norm (𝕜 := ℂ) a' (ρ h⁻¹ (f' (π h)))
  have hx := norm_nonneg (ρ h⁻¹ (f (π h)))
  have hy := norm_nonneg (ρ h⁻¹ (f' (π h)))
  have ha := norm_nonneg a
  have ha' := norm_nonneg a'
  have hxy : ‖ρ h⁻¹ (f (π h))‖ * ‖ρ h⁻¹ (f' (π h))‖ ≤ ‖ρ h⁻¹ (f (π h))‖ ^ 2 + ‖ρ h⁻¹ (f' (π h))‖ ^ 2 := by
    nlinarith [sq_nonneg (‖ρ h⁻¹ (f (π h))‖ - ‖ρ h⁻¹ (f' (π h))‖)]
  calc ‖inner ℂ a (ρ h⁻¹ (f (π h)))‖ * ‖inner ℂ a' (ρ h⁻¹ (f' (π h)))‖
      ≤ (‖a‖ * ‖ρ h⁻¹ (f (π h))‖) * (‖a'‖ * ‖ρ h⁻¹ (f' (π h))‖) := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = ‖a‖ * ‖a'‖ * (‖ρ h⁻¹ (f (π h))‖ * ‖ρ h⁻¹ (f' (π h))‖) := by ring
    _ ≤ ‖a‖ * ‖a'‖ * (‖ρ h⁻¹ (f (π h))‖ ^ 2 + ‖ρ h⁻¹ (f' (π h))‖ ^ 2) := by gcongr

end GlobalTheory.AdelicL2Norm

noncomputable section

namespace GlobalTheory.AdelicL2Norm



theorem norm_eq_integral : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ (i : Fin D.R.m) (t : T), ∃ c : ℝ, 0 < c ∧ ∀ u u' : (R.HV i t).H, ⟪u, u'⟫_ℂ = (c : ℂ) * ∫ h in R.fdV i t, ⟪R.extV i t u h, R.extV i t u' h⟫_ℂ ∂(R.νV i t) ∧ ∀ a a' : (R.cV i).W, IntegrableOn (fun h => star ⟪a, R.extV i t u h⟫_ℂ * ⟪a', R.extV i t u' h⟫_ℂ) (R.fdV i t) (R.νV i t) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL i t
  have hν := hL.models.νV i t
  have hH := hL.models.HV i t
  have hc := hL.models.cV i
  haveI : IsTopologicalGroup (GA D (Vc D i)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (GA D (Vc D i)) := ⟨rfl⟩
  haveI : Countable (GQ (Vc D i)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig (Vc D i).gram
  haveI := hν.1.1
  have ho : IsOpen (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).J.comap (finHom (Vc D i)).rangeRestrict :
      Subgroup (GA D (Vc D i))) : Set (GA D (Vc D i))) := by
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    filter_upwards [GlobalTheory.ThetaIntegrand.eventually_level (Vc D i) (R.βV i) (R.datVt i t)] with κ hκ
    exact hκ.1
  have h1 : R.νV i t ((GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (R.datVt i t)).comap (finHom (Vc D i)).rangeRestrict) = 1 :=
    GlobalTheory.Mass.Levels.measure_comap_finE hν.1
  have hle : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).J ≤ GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (R.datVt i t) := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    have e : rTup (R.βV i) (R.datVt i t) (Formalism.UG.bc (Formalism.IndefR.Lev.swapAE D) x.1) = 1 := Subgroup.mem_bot.1 hx.2
    exact e ▸ one_mem _
  have hχ : ∀ k, ‖((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ k : ℂ)‖ = 1 := fun k =>
    GlobalTheory.InnerClassSum.norm_levFn (R.βV i) (flag1L (R.datVt i t)) (Formalism.UG.bc (Formalism.IndefR.Lev.swapAE D) k.1.1)
  obtain ⟨c, hc0, hcl⟩ := adInner_eq_mul_integral (R.νV i t) (finHom (Vc D i)).rangeRestrict
    (finHom (Vc D i)).rangeRestrict_surjective (GQ (Vc D i)) hν.2 _ _ hle ho h1 (R.cV i).ρ hc.2.1
    (levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ hχ (R.B.L i t).pres.y (R.B.L i t).pres.reps
  have hmem := fun u => hH.2.1.le (LinearMap.mem_range_self (R.HV i t).e u)
  have hx : ∀ u h, R.extV i t u h = (R.cV i).ρ h⁻¹ ((R.HV i t).e u ((finHom (Vc D i)).rangeRestrict h)) :=
    fun _ _ => rfl
  refine ⟨c, hc0, fun u u' => ⟨?_, fun a a' => ?_⟩⟩
  · simp only [hx]
    exact (hH.2.2 u u').trans (hcl _ (hmem u) _ (hmem u')).2
  · simp only [hx]
    exact integrableOn_coord (R.νV i t) (finHom (Vc D i)).rangeRestrict _ ho (R.cV i).ρ hc.2.2.1 _ hχ (GQ (Vc D i)) _ _ (hmem u) (hmem u')
      (hcl _ (hmem u) _ (hmem u)).1 (hcl _ (hmem u') _ (hmem u')).1 a a'

end GlobalTheory.AdelicL2Norm
end
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

namespace GlobalTheory.DownLift

theorem typeNZ_of_nonVan_gen : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t, NonVan R i t → GenInf R i t → GenFin R i t → GoodNoChi R i t → GoodMem R i t → TypeNZ R i t := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F _ _ i t hNV hInf hFin hNo hMem h hh s hs y hy hg h0
  by_contra hne
  have hF : R.thF i t y = 0 := by
    rw [← hMem y hg, h0]
    exact map_zero _
  exact hFin y (hNo y hg) (hInf y hF) (hNV h hh s hs y hy hne)

end GlobalTheory.DownLift

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.LiftInjProof

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem hasString_of_lift (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (ok : Pl D.host.E → Prop)
    (h1 : UnrCorr R i t fun w => ¬ ok w) (h1' : UnrCorr R i t ok)
    (h2 : ParamsEx R i t) (h3 : DownEig R i t) {h} (hh : GlobalTheory.Hk3.IsOpsV R i t h) {s : Sys D} {y} (hy : IsEigV R i t h s y)
    (h0 : R.thF i t y ≠ 0) : HasString R i t s := by
  obtain ⟨c, hc⟩ := h3 h hh s
  obtain ⟨B, hB⟩ := h2.1 h hh s y hy (fun e => h0 (by rw [e, map_zero]))
  obtain ⟨B', hB', hb⟩ := h2.2 c ((Submodule.ne_bot_iff _).2 ⟨_, hc y hy, h0⟩)
  refine ⟨B, hB, fun w hw => ⟨(B' w).map (fun a : ℂˣ => ((a * valV R i t w * (valW R i t w)⁻¹ : ℂˣ) : ℂ)), ?_, fun a ha => ?_⟩⟩
  · by_cases hw' : ok w
    · exact h1' h hh s c y hy h0 (hc y hy) B B' hB hB' w hw hw'
    · exact h1 h hh s c y hy h0 (hc y hy) B B' hB hB' w hw hw'
  obtain ⟨b, hb', rfl⟩ := Multiset.mem_map.1 ha
  have e1 : ‖(valV R i t w : ℂ)‖ = 1 := GlobalTheory.LFun.norm_val _ _
  have e2 : ‖(valW R i t w : ℂ)‖ = 1 := GlobalTheory.LFun.norm_val _ _
  simpa [e1, e2] using hb w hw b hb'

theorem liftInj_of_typeNZ : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → (∀ i, TypeNZ R i A.μ0 ∧ DownEig R i A.μ0 ∧ UnrCorr R i A.μ0 (fun w => ¬ _root_.Formalism.IndefR.Lev.IsConjPl w w) ∧ UnrCorr R i A.μ0 (fun w => _root_.Formalism.IndefR.Lev.IsConjPl w w) ∧ ParamsEx R i A.μ0) → GlobalTheory.LiftRows.LiftInj R := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG _ hZ
  intro i h hops s x y hx hy hxne hyG hy0
  obtain ⟨hT, hDE, hU1, hU2, hPE⟩ := hZ i
  have hF : R.thF i A.μ0 x ≠ 0 := by
    intro h0
    apply hxne
    apply (hG.core.models.HW i (sg0 D A)).1
    rw [hG.core.thP.thG i A.μ0 x, h0, map_zero, map_zero]
  exact hT h hops s (hasString_of_lift R i A.μ0 (fun w => _root_.Formalism.IndefR.Lev.IsConjPl w w) hU1 hU2 hPE hDE hops hx hF) y hy hyG hy0

end GlobalTheory.LiftInjProof

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.DownLift.GenInfEquiv

theorem representation_inv_mul_left_translate {H W : Type} [Group H] [AddCommGroup W] [Module ℂ W] (ρ : H →* Module.End ℂ W) (γ h : H) (w : W) :
    ρ (γ * h)⁻¹ (ρ γ w) = ρ h⁻¹ w := by
  rw [← Module.End.mul_apply, ← map_mul]
  congr 2
  group

theorem representation_right_translate_inv_mul {H W : Type} [Group H] [AddCommGroup W] [Module ℂ W] (ρ : H →* Module.End ℂ W) (u h : H) (w : W) :
    ρ u (ρ (h * u)⁻¹ w) = ρ h⁻¹ w := by
  rw [← Module.End.mul_apply, ← map_mul]
  congr 2
  group

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem ext_apply' {V : HSp D} (c : CoefA V) (φ : Formalism.IndefR.Bridge.Gf V → c.W) (h : GA D V) :
    c.ext φ h = c.ρ h⁻¹ (φ ((finHom V).rangeRestrict h)) := rfl

theorem ext_left' {V : HSp D} (c : CoefA V) (J : Subgroup (Formalism.IndefR.Bridge.Gf V)) (χ : J →* ℂˣ)
    (φ : Formalism.IndefR.Bridge.Gf V → c.W)
    (hφ : φ ∈ Formalism.IndefR.Bridge.AdForms (Formalism.IndefR.Bridge.ratF V) c.coef.ρ J χ) (γ : GA D V) (hγ : γ ∈ GQ V)
    (h : GA D V) : c.ext φ (γ * h) = c.ext φ h := by
  have h1 := hφ ⟨γ, hγ⟩ ((finHom V).rangeRestrict h) 1
  simp only [map_one, Units.val_one, one_smul, OneMemClass.coe_one, mul_one] at h1
  have h2 : φ ((finHom V).rangeRestrict γ * (finHom V).rangeRestrict h) = c.ρ γ (φ ((finHom V).rangeRestrict h)) := h1
  rw [ext_apply', ext_apply', map_mul (finHom V).rangeRestrict, h2]
  exact representation_inv_mul_left_translate c.ρ γ h _

theorem ext_inf' {V : HSp D} (c : CoefA V) (φ : Formalism.IndefR.Bridge.Gf V → c.W) (u : GA D V) (hu : u ∈ GinfC V)
    (h : GA D V) : c.ρ u (c.ext φ (h * u)) = c.ext φ h := by
  have e1 : (finHom V).rangeRestrict (h * u) = (finHom V).rangeRestrict h := by
    apply Subtype.ext
    have h1 : finHom V u = 1 := hu
    show finHom V (h * u) = finHom V h
    rw [map_mul, h1, mul_one]
  rw [ext_apply', ext_apply', e1]
  exact representation_right_translate_inv_mul c.ρ u h _

theorem om_left' {ψ : AddChar (AF D.host.F) ℂ} {S T' : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T' →* Module.End ℂ (WO S T' → ℂ)} (H : IsWeilDatumO ψ S T' χS χT om) (γ : GA D S)
    (hγ : γ ∈ GQ S) (h : GA D S) (g : GA D T') (f : WO S T' → ℂ) (hf : IsThetaFunO ψ S T' f) :
    thetaKO om (γ * h) g f = thetaKO om h g f := by
  unfold thetaKO
  have e : ((γ * h, g) : GA D S × GA D T') = (γ, (1 : GA D T')) * (h, g) := by simp
  rw [e, map_mul, Module.End.mul_apply]
  exact H.om_aut _ hγ _ (Subgroup.one_mem _) _ (H.om_pres _ _ hf)

theorem om_right' {S T' : HSp D} (om : GA D S × GA D T' →* Module.End ℂ (WO S T' → ℂ)) (u h : GA D S)
    (g : GA D T') (f : WO S T' → ℂ) : thetaKO om (h * u) g f = thetaKO om h g (om (u, 1) f) := by
  unfold thetaKO
  have e : ((h * u, g) : GA D S × GA D T') = (h, g) * (u, (1 : GA D T')) := by simp
  rw [e, map_mul, Module.End.mul_apply]

theorem mem_of_hmodIs {X : Type} [AddCommGroup X] [Module ℂ X] (M : HMod X) (V : Submodule ℂ X) (ip : X → X → ℂ)
    (h : M.Is V ip) (x : M.H) : M.e x ∈ V := h.2.1 ▸ ⟨x, rfl⟩

end GlobalTheory.DownLift.GenInfEquiv


open GlobalTheory.DownLift.GenInfEquiv in
theorem GlobalTheory.DownLift.downInt_realEquiv : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (u : GA D (Vc D i)), u ∈ GinfC (Vc D i) → ∀ (f : WO (Vc D i) (Wc D i) → ℂ), IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ∀ (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)), downInt R i t y (R.ωP i t (u, 1) f) l g = downInt R i t y f (l ∘ₗ (R.cV i).ρ u) g := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hP i t y u hu f hf l g
  have hM : R.IsModels := hG.core.models
  have hν := hM.νV i t
  haveI := Formalism.IndefR.Eqv.measurableMul_GA D (Vc D i)
  haveI := Formalism.IndefR.Eqv.gQ_countable D (Vc D i)
  haveI : (R.νV i t).IsHaarMeasure := hν.1.1
  haveI : (R.νV i t).IsMulRightInvariant := Formalism.IndefR.Eqv.unimodGA_holds (Vc D i) _ hν.1.1
  have hx := mem_of_hmodIs _ _ _ (hM.HV i t) y
  have hW := (hP i t).datum
  let Ψ : GA D (Vc D i) → ℂ := fun h =>
    thetaKO (R.ωP i t) h g f * (l ∘ₗ (R.cV i).ρ u) ((R.cV i).ext ((R.HV i t).e y) h)
  have hL : ∀ γ ∈ GQ (Vc D i), ∀ h, Ψ (γ * h) = Ψ h := by
    intro γ hγ h
    exact congrArg₂ (fun a b => a * (l ∘ₗ (R.cV i).ρ u) b) (om_left' hW γ hγ h g f hf)
      (ext_left' (R.cV i) _ _ _ hx γ hγ h)
  have hR : ∀ h, thetaKO (R.ωP i t) h g (R.ωP i t (u, 1) f) * l (R.extV i t y h) = Ψ (h * u) := by
    intro h
    exact congrArg₂ (fun a b => a * l b) (om_right' (R.ωP i t) u h g f).symm
      (ext_inf' (R.cV i) ((R.HV i t).e y) u hu h).symm
  have key := (Formalism.IndefR.Eqv.rightInv_holds _ (GQ (Vc D i)) (R.νV i t) _ hν.2 Ψ hL u).2
  have e1 : downInt R i t y (R.ωP i t (u, 1) f) l g = ∫ h in R.fdV i t, Ψ (h * u) ∂(R.νV i t) := by
    unfold downInt
    exact integral_congr_ae (Filter.Eventually.of_forall hR)
  have e2 : downInt R i t y f (l ∘ₗ (R.cV i).ρ u) g = ∫ h in R.fdV i t, Ψ h ∂(R.νV i t) := rfl
  rw [e1, e2, key]

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

theorem _root_.GlobalTheory.T.coefficientMap_unique_bijective_complex_extension : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∃ c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W, ExtC R i (inC M.c') M.c0' c ∧ Function.Bijective c ∧ ∀ c', ExtC R i (inC M.c') M.c0' c' → c' = c := by
  first | exact @GlobalTheory.CoefExtC.exists_extC_bijective_unique | exact GlobalTheory.CoefExtC.exists_extC_bijective_unique | (intros; apply GlobalTheory.CoefExtC.exists_extC_bijective_unique <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.stable_and_cover_prismHom_of_pushout : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B C B' C' : Obj l R) (h : Hom B C) (k : Hom B B') (k' : Hom C C') (h' : Hom B' C'), IsPO h k k' h' → (Stable h → Stable h') ∧ (Cover h → Cover h') := by
  first | exact @GlobalTheory.BSP.stable_cover_of_isPO | exact GlobalTheory.BSP.stable_cover_of_isPO | (intros; apply GlobalTheory.BSP.stable_cover_of_isPO <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.stratifiedPhiModule_descent_finite_level : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (B C D : Obj l ↥(OL K)) (h : Hom B C) (f : Hom bk.prism C) (p q : Hom C D), Cover h → IsPO h h p q → ∀ m : ℕ, letI := (qmap h m).toAlgebra; ∃ N : Submodule (B.A ⧸ adI B ^ m) (Fin d → C.A ⧸ adI C ^ m), (∀ z, z ∈ N ↔ (fun i => qmap p m (z i)) = ((S.ε (p.comp f) (q.comp f)).map (Ideal.Quotient.mk (adI D ^ m))).mulVec fun i => qmap q m (z i)) ∧ Module.Finite (B.A ⧸ adI B ^ m) ↥N ∧ Module.Projective (B.A ⧸ adI B ^ m) ↥N ∧ IsBaseChange (C.A ⧸ adI C ^ m) N.subtype := by
  first | exact @GlobalTheory.BSP.LevH.descent_at_level | exact GlobalTheory.BSP.LevH.descent_at_level | (intros; apply GlobalTheory.BSP.LevH.descent_at_level <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_galois_elem_cyclotomic_period_not_root_of_unity : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ∃ (g : ↥(GK K)) (z : ℂ_[l]), IsZ bk g z ∧ ∀ i : ℕ, 1 ≤ i → z ^ i ≠ 1 := by
  first | exact @GlobalTheory.BKLim.exists_isZ_not_root | exact GlobalTheory.BKLim.exists_isZ_not_root | (intros; apply GlobalTheory.BKLim.exists_isZ_not_root <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix GlobalTheory.BKGal.XiFil
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.tensorBcris_frobenius_value_eq_sum_coordinates : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (w : Vec K a ι) (hwS : ∀ τ j, w τ j ∈ invL l (S O K e)) (hw : P.xiExt w ∈ P.MMl) (hd : ∀ j, P.xi (fun _ => Pi.single j 1) ∈ P.MMl), toBcris t ϖ P ⟨P.xiExt w, hw⟩ = ∑ j, ϖ.iB t K (fun τ => ⟨w τ j, hwS τ j⟩) • toBcris t ϖ P ⟨P.xi (fun _ => Pi.single j 1), hd j⟩ := by
  first | exact @GlobalTheory.XiDecomp.toBcris_xiExt_eq_sum | exact GlobalTheory.XiDecomp.toBcris_xiExt_eq_sum | (intros; apply GlobalTheory.XiDecomp.toBcris_xiExt_eq_sum <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

theorem _root_.GlobalTheory.T.torsion_exponent_kills_invariants_of_good : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := LocalSituation.sit D.loc HW l (D.locA l) K s LL h; ∀ (M0 h0 : ℕ) (T : LocLat S.G S.Qp S.LL S.O), LocalSituation.HypW S ((F l).E K s LL h).tie T M0 h0 → (∀ τ, ¬ IsJumpV S.PD T.ρ τ 0) → ∀ x : T.V ⧸ T.L.T, (∀ g, actD T.L g x = x) → ((LocalSituation.ell S : S.O) ^ GlobalTheory.HubX.invariantsCountConstant D.loc HW D.locA l K s LL h M0 h0 T) • x = 0 := by
  first | exact @GlobalTheory.HubX.InvariantsNoJump.torsion_exponent_kills_invariants_no_jump_zero | exact GlobalTheory.HubX.InvariantsNoJump.torsion_exponent_kills_invariants_no_jump_zero | (intros; apply GlobalTheory.HubX.InvariantsNoJump.torsion_exponent_kills_invariants_no_jump_zero <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.TruncationDivisibility

theorem deltaS_X (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] : (deltaS l a).δ (X : (Wq l a)⟦X⟧) = 0 := by
  have h := (deltaS l a).φ_eq X
  have h2 : (deltaS l a).φ X = X ^ l := by
    change (Delta.ofLift l (frobS l a) _ _).φ X = _
    rw [Delta.ofLift_φ, frobS_X]
  rw [h2] at h
  have h3 : (l : (Wq l a)⟦X⟧) * (deltaS l a).δ X = 0 := by linear_combination -h
  exact (mul_eq_zero.1 h3).resolve_left (l_ne_zero l a)

theorem X_pow_dvd_sub_trunc' {R : Type} [CommRing R] (x : R⟦X⟧) (n : ℕ) :
    (X : R⟦X⟧) ^ n ∣ x - (trunc n x : R⟦X⟧) := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro m hm
  rw [map_sub, Polynomial.coeff_coe, coeff_trunc, if_pos hm, sub_self]

end GlobalTheory.TruncationDivisibility

open GlobalTheory.TruncationDivisibility in
theorem GlobalTheory.sdelta_of_rank_one : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (C : Type) [CommRing C] (DC : Delta l C) (J : Ideal C), (l : C) ∈ J → IsHausdorff J C → ∀ (σ : (Wq l a)⟦X⟧ →+* C) (e : ℕ), σ X ^ e ∈ J → DC.δ (σ X) = 0 → IsδMap (deltaS l a) DC σ := by
  intro l _ a _ C _ DC J hl hH σ e he hX
  set S := δLocus (deltaS l a) DC σ with hS
  have hXS : (X : (Wq l a)⟦X⟧) ∈ S := by
    rw [mem_δLocus, deltaS_X, map_zero, hX]
  have hCS : ∀ w : Wq l a, PowerSeries.C w ∈ S := GlobalTheory.T.C_mem_deltaCommuteLocusSubring_of_isHausdorff l a C DC J hl hH σ
  have hpoly : ∀ p : Polynomial (Wq l a), ((p : (Wq l a)⟦X⟧)) ∈ S := by
    intro p
    induction p using Polynomial.induction_on with
    | C w => rw [Polynomial.coe_C]; exact hCS w
    | add p q hp hq => rw [Polynomial.coe_add]; exact S.add_mem hp hq
    | monomial n w _ =>
      rw [Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X]
      exact S.mul_mem (hCS w) (S.pow_mem hXS _)
  refine GlobalTheory.T.isDeltaRingHom_of_dense_deltaCommuteLocus l ((Wq l a)⟦X⟧) C (deltaS l a) DC (J.comap σ) J σ ?_ Ideal.map_comap_le hH ?_
  · rw [Ideal.mem_comap, map_natCast]; exact hl
  · intro x n
    refine ⟨_, hpoly (trunc (e * n) x), ?_⟩
    obtain ⟨c, hc⟩ := X_pow_dvd_sub_trunc' x (e * n)
    rw [hc, pow_mul]
    refine Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow ?_ n)
    rw [Ideal.mem_comap, map_pow]; exact he
end
