module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1857
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1990
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2185
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1294
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle202
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2125
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2039
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2083
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2186
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMulPowIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2051
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle226
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle277
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeUnitNormSqNonneg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2149
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2187
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.FibreLocality

theorem lp : ∀ {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.IsAddHaarMeasure] (P : X →+ X), Continuous P →
    (∀ x, P (P x) = P x) → ∀ (Φ Ψ : X → ℂ), Continuous Φ → Continuous Ψ → ∀ K : Set X, IsCompact K →
    (∀ x, Φ x ≠ 0 → P x ∈ K) → ∀ y : X, (∀ z, P z = z → Φ (y + z) = 0) →
    (∀ O : Set X, IsOpen O → y ∈ O → ∃ h : X → ENNReal, Measurable h ∧ (∀ x, h x ≤ 1) ∧
      (∀ x z, P z = z → h (x + z) = h x) ∧ (∀ x, h x ≠ 0 → x + (P y - P x) ∈ O) ∧
      (∃ O' : Set X, IsOpen O' ∧ y ∈ O' ∧ ∀ x ∈ O', Ψ x ≠ 0 → 1 / 2 ≤ h x) ∧
      ∫⁻ x, h x * ‖Ψ x‖ₑ ^ 2 ∂μ = ∫⁻ x, h x * ‖Φ x‖ₑ ^ 2 ∂μ) → Ψ y = 0 := GlobalTheory.T.vanishing_of_projection_support

theorem lw : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → (∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), ∃ t, GlobalTheory.LatVac.psiAt ψ w t ≠ 1) →
    ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∀ Ψ ∈ GlobalTheory.WeilM.schA F κ,
    (∀ (s : Finset (κ → AF F)) (c : (κ → AF F) → ℂ), (∀ b ∈ s, GlobalTheory.LatVac.liftV v 1 • b = 0) →
      ∫⁻ x, ‖(∑ b ∈ s, c b * ψ (x ⬝ᵥ b)) * Ψ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖(∑ b ∈ s, c b * ψ (x ⬝ᵥ b)) * Φ x‖ₑ ^ 2 ∂μ) →
    ∀ (y : κ → AF F) (O : Set (κ → AF F)), IsOpen O → y ∈ O →
    ∃ h : (κ → AF F) → ENNReal, @Measurable _ _ (borel _) _ h ∧ (∀ x, h x ≤ 1) ∧
      (∀ x z, GlobalTheory.LatVac.liftV v 1 • z = z → h (x + z) = h x) ∧
      (∀ x, h x ≠ 0 → x + (GlobalTheory.LatVac.liftV v 1 • y - GlobalTheory.LatVac.liftV v 1 • x) ∈ O) ∧
      (∃ O' : Set (κ → AF F), IsOpen O' ∧ y ∈ O' ∧ ∀ x ∈ O', Ψ x ≠ 0 → 1 / 2 ≤ h x) ∧
      ∫⁻ x, h x * ‖Ψ x‖ₑ ^ 2 ∂μ = ∫⁻ x, h x * ‖Φ x‖ₑ ^ 2 ∂μ := GlobalTheory.T.exists_localizingWeight_equal_offPlaceMasses

theorem lc : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ b : κ → AF F, ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
    (fun x => ψ (x ⬝ᵥ b) * Φ x) ∈ GlobalTheory.WeilM.schA F κ := GlobalTheory.T.addCharDotMul_mem_adelicSchwartzSpace

open scoped Classical in
theorem ls_pure {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ K : Set (κ → AF F), IsCompact K ∧ ∀ x, GlobalTheory.WeilM.pureA F f g x ≠ 0 → GlobalTheory.LatVac.liftV v 1 • x ∈ K := by
  set e := GlobalTheory.LatVac.liftV v (1 : Fv F v) with he_def
  let ι : FiniteAdeleRing (𝓞 F) F → AF F := fun a => (0, a)
  have hι : Continuous ι := continuous_const.prodMk continuous_id
  let Θ : (κ → FiniteAdeleRing (𝓞 F) F) → (κ → AF F) := fun z => e • fun i => ι (z i)
  have hΘ : Continuous Θ := by
    refine (continuous_const_smul e).comp (continuous_pi fun i => ?_)
    exact hι.comp (continuous_apply i)
  have he1 : e.1 = 0 := rfl
  refine ⟨Θ '' tsupport g, hg.2.isCompact.image hΘ, fun x hx => ⟨fun i => (x i).2, ?_, ?_⟩⟩
  · refine subset_tsupport _ ?_
    intro h0
    apply hx
    simp only [GlobalTheory.WeilM.pureA]
    rw [h0, mul_zero]
  · funext i
    show e * ι (x i).2 = e * x i
    refine Prod.ext ?_ rfl
    show e.1 * 0 = e.1 * (x i).1
    rw [he1, zero_mul, zero_mul]

theorem ls : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)),
    ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∃ K : Set (κ → AF F), IsCompact K ∧ ∀ x, Φ x ≠ 0 → GlobalTheory.LatVac.liftV v 1 • x ∈ K := by
  intro F _ _ κ _ v Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    exact ls_pure v f g hg
  | zero => exact ⟨∅, isCompact_empty, fun x hx => (hx rfl).elim⟩
  | add Φ₁ Φ₂ _ _ h1 h2 =>
    obtain ⟨K₁, hK₁, h₁⟩ := h1
    obtain ⟨K₂, hK₂, h₂⟩ := h2
    refine ⟨K₁ ∪ K₂, hK₁.union hK₂, fun x hx => ?_⟩
    by_cases hx1 : Φ₁ x = 0
    · exact Or.inr (h₂ x fun hx2 => hx (by simp [hx1, hx2]))
    · exact Or.inl (h₁ x hx1)
  | smul c Φ _ h =>
    obtain ⟨K, hK, hs⟩ := h
    exact ⟨K, hK, fun x hx => hs x fun h0 => hx (by simp [h0])⟩

theorem liftV_mul_self {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) :
    GlobalTheory.LatVac.liftV v (1 : Fv F v) * GlobalTheory.LatVac.liftV v 1 = GlobalTheory.LatVac.liftV v 1 := by
  have h := GlobalTheory.LatVac.at_liftV v (1 : Fv F v) (GlobalTheory.LatVac.liftV v 1 - 1)
    (by rw [map_sub, GlobalTheory.LatVac.evFin_liftV, map_one, sub_self])
  rw [smul_eq_mul, sub_mul, one_mul, sub_eq_zero] at h
  exact h

theorem at_iff {F : Type} [Field F] [NumberField F] {κ : Type} (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (z : κ → AF F) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z ↔ GlobalTheory.LatVac.liftV v 1 • z = z := by
  constructor
  · intro h
    have h1 := h (1 - GlobalTheory.LatVac.liftV v 1) (by rw [map_sub, GlobalTheory.LatVac.evFin_liftV, map_one, sub_self])
    rw [sub_smul, one_smul, sub_eq_zero] at h1
    exact h1.symm
  · intro h u hu
    rw [← h, smul_smul]
    have := GlobalTheory.LatVac.at_liftV v (1 : Fv F v) u hu
    rw [smul_eq_mul] at this
    rw [this, zero_smul]

theorem eq_zero_of_vanish_fibre : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (ψ : AddChar (AF F) ℂ) (T : Module.End ℂ ((κ → AF F) → ℂ)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → (∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), ∃ t, GlobalTheory.LatVac.psiAt ψ w t ≠ 1) →
    (∀ Φ ∈ GlobalTheory.WeilM.schA F κ, T Φ ∈ GlobalTheory.WeilM.schA F κ) →
    (∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∫⁻ y, ‖T Φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖Φ y‖ₑ ^ 2 ∂μ) →
    (∀ u : AF F, evFin F v u = 0 → ∀ p q : κ → AF F, ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
      T (GlobalTheory.WeilM.schr ψ (u • p, u • q) Φ) = GlobalTheory.WeilM.schr ψ (u • p, u • q) (T Φ)) →
    ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∀ y : κ → AF F, (∀ z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z → Φ (y + z) = 0) → T Φ y = 0 := by
  intro F _ _ κ _ v ψ T hstd hnt hpres hiso hcomm Φ hΦ y hy
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  set e := GlobalTheory.LatVac.liftV v (1 : Fv F v) with he_def
  have he0 : evFin F v (1 - e) = 0 := by rw [map_sub, he_def, GlobalTheory.LatVac.evFin_liftV, map_one, sub_self]
  let P : (κ → AF F) →+ (κ → AF F) := DistribSMul.toAddMonoidHom _ e
  have hPc : Continuous P := continuous_const_smul e
  have hPP : ∀ x, P (P x) = P x := fun x => by
    show e • e • x = e • x
    rw [smul_smul, he_def, liftV_mul_self]
  have hTΦ := hpres Φ hΦ
  obtain ⟨K, hK, hKs⟩ := ls v Φ hΦ
  let μ : Measure (κ → AF F) := Measure.addHaar
  refine lp μ P hPc hPP Φ (T Φ) (GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F hΦ)
    (GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F hTΦ) K hK hKs y
    (fun z hz => hy z ((at_iff v z).2 hz)) ?_
  intro O hO hyO
  have htrig : ∀ (s : Finset (κ → AF F)) (c : (κ → AF F) → ℂ), (∀ b ∈ s, e • b = 0) →
      ∫⁻ x, ‖(∑ b ∈ s, c b * ψ (x ⬝ᵥ b)) * T Φ x‖ₑ ^ 2 ∂μ =
        ∫⁻ x, ‖(∑ b ∈ s, c b * ψ (x ⬝ᵥ b)) * Φ x‖ₑ ^ 2 ∂μ := by
    intro s c hs
    have hchar : ∀ b ∈ s, ∀ Ψ ∈ schA F κ,
        T (fun x => ψ (x ⬝ᵥ b) * Ψ x) = fun x => ψ (x ⬝ᵥ b) * T Ψ x := by
      intro b hb Ψ hΨ
      have h1 := hcomm (1 - e) he0 0 b Ψ hΨ
      have hb' : (1 - e) • b = b := by rw [sub_smul, one_smul, hs b hb, sub_zero]
      have hs0 : ∀ Ψ' : (κ → AF F) → ℂ,
          schr ψ ((1 - e) • (0 : κ → AF F), (1 - e) • b) Ψ' = fun x => ψ (x ⬝ᵥ b) * Ψ' x := by
        intro Ψ'; funext x; simp [schr, hb']
      rw [hs0, hs0] at h1
      exact h1
    have hsum : ∀ G : (κ → AF F) → ℂ, (fun x => (∑ b ∈ s, c b * ψ (x ⬝ᵥ b)) * G x) =
        ∑ b ∈ s, c b • (fun x => ψ (x ⬝ᵥ b) * G x) := by
      intro G; funext x; simp [Finset.sum_mul, mul_assoc]
    have hmem : (fun x => (∑ b ∈ s, c b * ψ (x ⬝ᵥ b)) * Φ x) ∈ schA F κ := by
      rw [hsum]
      exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (lc ψ hstd b Φ hΦ)
    have hT : T (fun x => (∑ b ∈ s, c b * ψ (x ⬝ᵥ b)) * Φ x) =
        fun x => (∑ b ∈ s, c b * ψ (x ⬝ᵥ b)) * T Φ x := by

      rw [hsum, hsum, map_sum]
      refine Finset.sum_congr rfl fun b hb => ?_
      rw [map_smul, hchar b hb Φ hΦ]
    have := hiso μ inferInstance _ hmem
    rw [hT] at this
    exact this
  exact lw v ψ hstd hnt μ inferInstance Φ hΦ (T Φ) hTΦ htrig y O hO hyO

end GlobalTheory.FibreLocality
end
end

section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.weilPair_moves_phasedHeisenbergTranslate : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
  ∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g : GA D S) (h : GA D T), IsFinPt S g x → IsFinPt T h y →
  ∀ f₀ : WO S T → ℂ, IsThetaFunO ψ S T f₀ → ∀ z : Matrix (Fin d) (Fin a) D.host.E,
  ∃ n : ℕ, 0 < n ∧ ∀ z', Formalism.MainNotions.StandardLatticesGL3.CloseTo D cc n (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) z z' →
    Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) • om (g, h) (heisO ψ S T (finPt hS hT r z) f₀) =
      Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z') • heisO ψ S T (finPt hS hT r z') (om (g, h) f₀) := by
  first | exact @GlobalTheory.MovedTr.moved_translate | exact GlobalTheory.MovedTr.moved_translate | (intros; apply GlobalTheory.MovedTr.moved_translate <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SqStepArith

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Chars Base stepFac chrW eps idealVal)

theorem stepFac_ratio_core {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) {μ₀ : T} (hL : Lc.Is μ₀)
    (W : G.Weil) (S : GridChoice W Set.univ) (hN : NumbersIn D.what₂.embLL S μ₀) (i j : Fin D.R.m) (t : T)
    (Bs : Base D.host.F D.host.E) (e₁ e₂ s : ℤˣ) (𝔟 𝔠 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) (z : ℤ)
    (hB : GlobalTheory.SqStep.BaseFits G W i j t Bs) (h0 : stepFac Bs (GlobalTheory.SqStep.chs G i j t) e₁ e₂ s 𝔟 𝔠 z ≠ 0) :
    GlobalTheory.Square.StepRatio D.what₂.embLL (Qn G t) G.pl.S0 (condExp G.pl) (fun v => Ideal.absNorm v.asIdeal)
      (stepFac Bs (GlobalTheory.SqStep.chs G i j μ₀) e₁ e₂ s 𝔟 𝔠 z) (stepFac Bs (GlobalTheory.SqStep.chs G i j t) e₁ e₂ s 𝔟 𝔠 z) := by
  classical
  have hQn : 0 < Qn G t := Finset.prod_pos fun w _ => Nat.pos_of_ne_zero fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  obtain ⟨hc1, -, hcmul, hcinv, -⟩ := GlobalTheory.Square.isAwayUnit_closure D.what₂.LL (Qn G t) hQn
  have hone : GlobalTheory.Square.IsAwayUnit (Qn G t) (1 : D.what₂.LL) := GlobalTheory.Square.IsAwayUnit.one _
  have hzpow : ∀ (x : D.what₂.LL) (n : ℕ), 0 < n → x ^ n = 1 → ∀ e : ℤ, GlobalTheory.Square.IsAwayUnit (Qn G t) (x ^ e) := by
    intro x n hn hx e
    refine hc1 _ n hn ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
  have hprod : ∀ (s : Finset Bs.P) (f : Bs.P → D.what₂.LL), (∀ v ∈ s, GlobalTheory.Square.IsAwayUnit (Qn G t) (f v)) →
      GlobalTheory.Square.IsAwayUnit (Qn G t) (∏ v ∈ s, f v) := by
    intro s f hf
    induction s using Finset.induction_on with
    | empty => simpa using hone
    | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact hcmul _ _ (hf a (Finset.mem_insert_self _ _)) (ih fun v hv => hf v (Finset.mem_insert_of_mem hv))
  set σ := D.what₂.embLL with hσ
  set X₀ := GlobalTheory.SqStep.chs G i j μ₀ with hX₀
  set X := GlobalTheory.SqStep.chs G i j t with hX
  set Sz := G.pl.S0 with hS0
  set f : Chars D.host.F D.host.E → Bs.P → ℂ := fun Y v =>
    (chrW Y.ν (Bs.τ v) (Units.map (Int.castRingHom _).toMonoidHom s) : ℂ) * eps Bs.ψ (chrW Y.ν (Bs.τ v)) z with hf
  have hS0T : Sz ⊆ X.T := Finset.subset_union_left
  have hT0 : X₀.T = Sz := GlobalTheory.SqStepArith.chs_T_base G hL i j
  have hst : ∀ Y : Chars D.host.F D.host.E, stepFac Bs Y e₁ e₂ s 𝔟 𝔠 z =
      ((idealVal Y.ν 𝔟 : ℂ)) ^ (e₁ : ℤ) * ((idealVal Y.ν 𝔠 : ℂ)) ^ (e₂ : ℤ) *
        ∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ Y.T), f Y v := by
    intro Y
    simp only [stepFac, Units.val_mul, Units.val_zpow_eq_zpow_val, hf]

  have hsplit : ∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ X.T), f X v =
      (∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ Sz), f X v) *
        ∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ X.T ∧ v.1 ∉ Sz), f X v := by
    rw [← Finset.prod_filter_mul_prod_filter_not (Finset.univ.filter (fun v : Bs.P => v.1 ∈ X.T)) (fun v : Bs.P => v.1 ∈ Sz),
      Finset.filter_filter, Finset.filter_filter]
    congr 2
    · ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => h.2, fun h => ⟨hS0T h, h⟩⟩
  have hne : ∀ v : Bs.P, v.1 ∈ Sz → f X v ≠ 0 := by
    intro v hv
    rw [hst, hsplit] at h0
    have h1 := left_ne_zero_of_mul (right_ne_zero_of_mul h0)
    exact (Finset.prod_ne_zero_iff.1 h1) v (by simpa using hv)
  have hS := fun (v : Bs.P) (hv : v.1 ∈ Sz) => GlobalTheory.T.base_place_character_factor G hL W S hN i j t Bs hB v hv s z (hne v hv)
  choose bS gS gS' hbS hgS hgS' heS using hS
  have hneT : ∀ v : Bs.P, v.1 ∈ X.T → v.1 ∉ Sz → f X v ≠ 0 := by
    intro v hv hv'
    rw [hst, hsplit] at h0
    have h1 := right_ne_zero_of_mul (right_ne_zero_of_mul h0)
    exact (Finset.prod_ne_zero_iff.1 h1) v (by simpa using And.intro hv hv')
  have hTw := fun (v : Bs.P) (hv : v.1 ∈ X.T) (hv' : v.1 ∉ Sz) => GlobalTheory.T.twistPlace_stepFactor_inverse_awayUnit G hL W S hN i j t Bs hB v hv hv' s z (hneT v hv hv')
  choose bT hbT heT using hTw
  obtain ⟨b1, ⟨n1, hn1, hb1⟩, e1⟩ := GlobalTheory.T.squareStepChar_idealValue_eq_base_mul_rootOfUnity G hL W S hN i j t 𝔟
  obtain ⟨b2, ⟨n2, hn2, hb2⟩, e2⟩ := GlobalTheory.T.squareStepChar_idealValue_eq_base_mul_rootOfUnity G hL W S hN i j t 𝔠
  let bS₁ : Bs.P → D.what₂.LL := fun v => if h : v.1 ∈ Sz then bS v h else 1
  let bT₁ : Bs.P → D.what₂.LL := fun v => if h : v.1 ∈ X.T ∧ v.1 ∉ Sz then bT v h.1 h.2 else 1
  let g : HeightOneSpectrum (𝓞 D.host.F) → 𝓞 D.what₂.LL := fun v => if h : v ∈ Bs.P ∧ v ∈ Sz then gS ⟨v, h.1⟩ h.2 else 1
  let g' : HeightOneSpectrum (𝓞 D.host.F) → 𝓞 D.what₂.LL := fun v => if h : v ∈ Bs.P ∧ v ∈ Sz then gS' ⟨v, h.1⟩ h.2 else 1
  have hSP : ∀ v ∈ Sz, v ∈ Bs.P := fun v hv => hB.2.1 (hS0T hv)

  have hmap : ∀ F' : HeightOneSpectrum (𝓞 D.host.F) → D.what₂.LL,
      ∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ Sz), F' v.1 = ∏ v ∈ Sz, F' v := by
    intro F'
    rw [show (∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ Sz), F' v.1) =
        ∏ v ∈ (Finset.univ.filter (fun v : Bs.P => v.1 ∈ Sz)).map (Function.Embedding.subtype _), F' v from
      (Finset.prod_map (Finset.univ.filter (fun v : Bs.P => v.1 ∈ Sz)) (Function.Embedding.subtype _) F').symm]
    congr 1
    ext v
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Function.Embedding.coe_subtype]
    exact ⟨fun ⟨w, hw, e⟩ => e ▸ hw, fun hv => ⟨⟨v, hSP v hv⟩, hv, rfl⟩⟩
  refine ⟨b1 ^ (e₁ : ℤ) * b2 ^ (e₂ : ℤ) * (∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ Sz), bS₁ v) *
    (∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ X.T ∧ v.1 ∉ Sz), bT₁ v), g, g', ?_, ?_, ?_⟩
  · refine hcmul _ _ (hcmul _ _ (hcmul _ _ (hzpow b1 n1 hn1 hb1 _) (hzpow b2 n2 hn2 hb2 _)) ?_) ?_
    · refine hprod _ _ fun v hv => ?_
      have hv' : v.1 ∈ Sz := by simpa using hv
      simp only [bS₁, dif_pos hv']
      exact hbS v hv'
    · refine hprod _ _ fun v hv => ?_
      have hv' : v.1 ∈ X.T ∧ v.1 ∉ Sz := by simpa using hv
      simp only [bT₁, dif_pos hv']
      exact hbT v hv'.1 hv'.2
  · intro v hv
    have h : v ∈ Bs.P ∧ v ∈ Sz := ⟨hSP v hv, hv⟩
    simp only [g, g', dif_pos h]
    exact ⟨hgS _ h.2, hgS' _ h.2⟩
  · have hA : ∀ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ Sz),
        f X₀ v = σ (bS₁ v * ((g v.1 : D.what₂.LL) / (g' v.1 : D.what₂.LL))) * f X v := by
      intro v hv
      have hv' : v.1 ∈ Sz := by simpa using hv
      have h2 : v.1 ∈ Bs.P ∧ v.1 ∈ Sz := ⟨v.2, hv'⟩
      simp only [bS₁, g, g', dif_pos hv', dif_pos h2]
      exact heS v hv'
    have hTw : (∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ X.T ∧ v.1 ∉ Sz), f X v) *
        σ (∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ X.T ∧ v.1 ∉ Sz), bT₁ v) = 1 := by
      rw [map_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun v hv => ?_
      have hv' : v.1 ∈ X.T ∧ v.1 ∉ Sz := by simpa using hv
      simp only [bT₁, dif_pos hv']
      rw [mul_comm]
      exact heT v hv'.1 hv'.2
    rw [hst X₀, hst X, hsplit, hT0, Finset.prod_congr rfl hA, Finset.prod_mul_distrib, ← map_prod,
      Finset.prod_mul_distrib, hmap (fun v => (g v : D.what₂.LL) / (g' v : D.what₂.LL)), e1, e2, mul_zpow, mul_zpow]
    simp only [map_mul, map_zpow₀]
    linear_combination (-((σ b1) ^ (e₁ : ℤ) * (σ b2) ^ (e₂ : ℤ) *
      σ (∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ Sz), bS₁ v) *
      σ (∏ v ∈ Sz, (g v : D.what₂.LL) / (g' v : D.what₂.LL)) * ((idealVal X.ν 𝔟 : ℂ)) ^ (e₁ : ℤ) *
      ((idealVal X.ν 𝔠 : ℂ)) ^ (e₂ : ℤ) * ∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ Sz), f X v)) * hTw

end GlobalTheory.SqStepArith

namespace GlobalTheory.SqStepArith

theorem stepFac_ratio : GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (t : T) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (e₁ e₂ s : ℤˣ)
      (𝔟 𝔠 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) (z : ℤ), GlobalTheory.SqStep.BaseFits G W i j t Bs →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j t) e₁ e₂ s 𝔟 𝔠 z ≠ 0 →
      GlobalTheory.Square.StepRatio D.what₂.embLL (Qn G t) G.pl.S0 (condExp G.pl) (fun v => Ideal.absNorm v.asIdeal)
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j μ₀) e₁ e₂ s 𝔟 𝔠 z) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j t) e₁ e₂ s 𝔟 𝔠 z) := by
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ hL G => ?_⟩⟩
  intro W S _ hN i j t Bs e₁ e₂ s 𝔟 𝔠 z hB h0
  exact stepFac_ratio_core G hL W S hN i j t Bs e₁ e₂ s 𝔟 𝔠 z hB h0

end GlobalTheory.SqStepArith
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean

namespace GlobalTheory.ConjExtend

theorem exists_extension_of_le (M : IntermediateField ℚ ℂ) (hle : M ≤ Qbar) (ρ : M →ₐ[ℚ] ℂ) :
    ∃ ρ' : Qbar →ₐ[ℚ] ℂ, ∀ x ∈ M, ρ' (TaylorLogMetric.liftM Qbar x) = ρ (TaylorLogMetric.liftM M x) := by
  let _ : Algebra M Qbar := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  have : IsScalarTower ℚ M Qbar := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have : Algebra.IsAlgebraic ℚ Qbar := algebraicClosure.isAlgebraic ℚ ℂ
  have : Algebra.IsAlgebraic M Qbar := Algebra.IsAlgebraic.tower_top (K := ℚ) M
  obtain ⟨φ, hφ⟩ := IsAlgClosed.surjective_domRestrict_of_isAlgebraic (K := ℚ) (L := M) (M := ℂ)
    (E := Qbar) ρ
  refine ⟨φ, fun x hx => ?_⟩
  rw [← hφ]
  unfold TaylorLogMetric.liftM
  rw [dite_eq_left hx, dite_eq_left (hle hx)]
  rfl

theorem fld_le (D : D7) (hI : GlobalTheory.NormSum.Inp D) (δ t0 : ℂ) (hc : Crv D D.host.ccK δ)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D D.host.ccK δ) t0) : GlobalTheory.KerConjMean.fld D δ t0 ≤ Qbar := by
  obtain ⟨hdata, htor⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hI.g1).2 _ δ hc
  have hwp : wpF (lamOf D D.host.ccK δ) t0 ∈ Qbar := by
    refine (htor t0 ⟨2, two_pos, by exact_mod_cast ht.1⟩ fun h0 => ?_).1
    obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
    have h1 := GlobalTheory.ArchNorm.mul_mem_lamOf D _ δ a h0
    rw [ha, mul_comm] at h1
    exact ht.2.1 h1
  unfold GlobalTheory.KerConjMean.fld
  rw [IntermediateField.adjoin_le_iff]
  rintro y (⟨x, rfl⟩ | rfl | rfl | rfl)
  · exact mem_algebraicClosure_iff.2
      ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom D.what₂.embLL.toRatAlgHom)
  · exact hdata.2.1
  · exact hdata.2.2
  · exact hwp

theorem exists_extension_conj : ∀ (D : D7), GlobalTheory.NormSum.Inp D → ∀ (δ t0 : ℂ), Crv D D.host.ccK δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D D.host.ccK δ) t0 →
    ∀ (σ : D.what₂.LL →+* ℂ), ∀ ρ ∈ GlobalTheory.KerConjMean.ext D δ t0 σ, ∃ ρ' : Qbar →ₐ[ℚ] ℂ,
      (∀ x, Formalism.MainNotions.StandardLatticesGL3.cj Qbar ρ' (D.what₂.embLL x) = σ x) ∧
      lamConj Qbar ρ' (lamOf D D.host.ccK δ) = lamConj (GlobalTheory.KerConjMean.fld D δ t0) ρ (GlobalTheory.KerConjMean.lat D δ) := by
  intro D hI δ t0 hc ht σ ρ hρ
  obtain ⟨ρ', h⟩ := exists_extension_of_le _ (fld_le D hI δ t0 hc ht) ρ
  refine ⟨ρ', fun x => ?_, ?_⟩
  · unfold Formalism.MainNotions.StandardLatticesGL3.cj
    rw [h _ (GlobalTheory.KerConjMean.embLL_mem D δ t0 x), ← hρ x]
    unfold TaylorLogMetric.liftM
    rw [dite_eq_left (GlobalTheory.KerConjMean.embLL_mem D δ t0 x)]
  · have h2 : g2 (lamOf D D.host.ccK δ) ∈ GlobalTheory.KerConjMean.fld D δ t0 :=
      IntermediateField.subset_adjoin ℚ _ (Or.inr (by simp))
    have h3 : g3 (lamOf D D.host.ccK δ) ∈ GlobalTheory.KerConjMean.fld D δ t0 :=
      IntermediateField.subset_adjoin ℚ _ (Or.inr (by simp))
    unfold lamConj
    rw [h _ h2, h _ h3]

end GlobalTheory.ConjExtend
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

theorem _root_.GlobalTheory.T.morphismToProjSpace_eq_linearProjection_comp : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) (H : LB X) (m N : ℕ) (s : Fin (m + 1) → LB.Sec H) (t : Fin (N + 1) → LB.Sec H) (a : Matrix (Fin (m + 1)) (Fin (N + 1)) R), H.IsLB → ∀ (hs : ⨆ i, nonzeroLocus (s i) = ⊤) (ht : ⨆ j, nonzeroLocus (t j) = ⊤) (hst : ∀ i, s i = ∑ j, GlobalTheory.AbLaw.cst f ⊤ (a i j) • t j) (h : GlobalTheory.ProjSpace.toProj f t ht ⁻¹ᵁ GlobalTheory.SpanVA.dom a = ⊤), GlobalTheory.ProjSpace.toProj f s hs = GlobalTheory.SpanVA.liftDom a (GlobalTheory.ProjSpace.toProj f t ht) h ≫ GlobalTheory.SpanVA.proj a := by
  first | exact @GlobalTheory.SpanVA.toProj_eq_liftDom_proj | exact GlobalTheory.SpanVA.toProj_eq_liftDom_proj | (intros; apply GlobalTheory.SpanVA.toProj_eq_liftDom_proj <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

theorem _root_.GlobalTheory.T.morphismToProjSpace_preimage_nonzeroLocus_linearForm : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) (H : LB X) (m N : ℕ) (s : Fin (m + 1) → LB.Sec H) (t : Fin (N + 1) → LB.Sec H) (a : Matrix (Fin (m + 1)) (Fin (N + 1)) R), H.IsLB → ∀ (ht : ⨆ j, nonzeroLocus (t j) = ⊤), (∀ i, s i = ∑ j, GlobalTheory.AbLaw.cst f ⊤ (a i j) • t j) → ∀ i, GlobalTheory.ProjSpace.toProj f t ht ⁻¹ᵁ nonzeroLocus (GlobalTheory.SpanVA.lin a i) = nonzeroLocus (s i) := by
  first | exact @GlobalTheory.SpanVA.toProj_preimage_nonzeroLocus_lin | exact GlobalTheory.SpanVA.toProj_preimage_nonzeroLocus_lin | (intros; apply GlobalTheory.SpanVA.toProj_preimage_nonzeroLocus_lin <;> assumption)
end
