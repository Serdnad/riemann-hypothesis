module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle008
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle014
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle056
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle004
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicEisensteinSeries.IsGrowFormEvAt
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2101
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1201
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1602
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle007
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2132
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle066
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutSubstA
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1191
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle054
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle065
import Development.WeilBound.CoreStatements.LocalThetaKernels.LocrepAd
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle024
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle019
import Development.WeilBound.ThetaLifts.LatticeBasics.SkewTwo
import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.PresOfHat
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle009
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle024
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1484
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle067
import Development.WeilBound.ThetaLifts.LatticeBasics.HgtExA
public import Development.WeilBound.ThetaLifts.LatticeBasics.NormZeta
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
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
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle003

@[expose] public section

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
namespace PositivityTheory.SiegelWeilFormula.Aeis
def EisBLW_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ)
    (Y : Spc F E n), _root_.UpperTheory.TP.W.GoodK σ B → 1 ≤ n →
    ∀ χ : Chr F E, IsHecke F E χ → ∀ c : ℕ, ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ c →
    ∀ b K a, IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → ∀ s₁ f, IsSec K χ s₁ f →
      ∃ Ê : ℂ → G2 σ Y → ℂ, (∃ t : ℝ, (∀ s : ℂ, t < s.re → ∀ x, HasSum (eisTerm (flat a f s₁ s) x) (Ê s x)) ∧
          ∀ x, DifferentiableOn ℂ (Ê · x) {s | t < s.re}) ∧
        ∀ s₀, ∃ (k : ℕ) (U : Set ℂ) (H : ℂ → modFun σ Y), U ∈ 𝓝 s₀ ∧ (∀ s ∈ U, s ≠ s₀ → ∀ x, (H s).1 x = (s - s₀) ^ k * Ê s x) ∧
          ∀ μ, IsGrowForm μ → DifferentiableOn ℂ (fun s => μ (H s)) U
theorem eisBLW_k : _root_.PositivityTheory.SiegelWeilFormula.Aeis.EisBLW_k := by
  intro F E _ _ _ _ _ σ B n Y hB hn χ hχ c hc b K a hb hK ha s₁ f hf
  obtain ⟨t₀, v, hv, hvh⟩ := _root_.PositivityTheory.SiegelWeilFormula.Aeis.eisHalf_w_k hB hb hK ha χ s₁ f hf
  obtain ⟨A, H, t₁, hA, hAne, hHh, hHs⟩ := _root_.PositivityTheory.SiegelWeilFormula.Aeis.siegelMult_w_k hB hn χ hχ c hc hb hK ha s₁ f hf
  have hHv : ∀ s' : ℂ, max t₀ t₁ < s'.re → ∀ x, (H s').1 x = A s' * (v s').1 x := by
    intro s' hs' x
    have h1 := hHs s' (lt_of_le_of_lt (le_max_right _ _) hs') x
    have h2 := (hv s' (lt_of_le_of_lt (le_max_left _ _) hs') x).mul_left (A s')
    exact h1.unique h2
  let Ehat : ℂ → G2 σ Y → ℂ := fun s' x => if max t₀ t₁ < s'.re then (v s').1 x else (H s').1 x / A s'
  refine ⟨Ehat, ⟨max t₀ t₁, ?_, ?_⟩, ?_⟩
  · intro s' hs' x
    simp only [Ehat, if_pos hs']
    exact hv s' (lt_of_le_of_lt (le_max_left _ _) hs') x
  · intro x
    have hd : DifferentiableOn ℂ (fun s' => evAt x (v s')) {s' : ℂ | t₀ < s'.re} :=
      hvh (evAt x) (isGrowForm_evAt x)
    have hd' : DifferentiableOn ℂ (fun s' => (v s').1 x) {s' : ℂ | max t₀ t₁ < s'.re} :=
      (hd.mono fun s' (hs' : max t₀ t₁ < s'.re) => (show t₀ < s'.re from lt_of_le_of_lt (le_max_left _ _) hs'))
    refine hd'.congr fun s' hs' => ?_
    simp only [Ehat, if_pos (show max t₀ t₁ < s'.re from hs')]
  · intro s₀
    obtain ⟨k, U, u, hUo, hs₀U, hud, hUA⟩ := GlobalTheory.CompanionTheory.Entire.local_factorisation A hA hAne s₀
    refine ⟨k, U, fun s' => (u s')⁻¹ • H s', hUo.mem_nhds hs₀U, ?_, ?_⟩
    · intro s' hs' hne x
      obtain ⟨hu, hAs⟩ := hUA s' hs'
      have hpow : (s' - s₀) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hne)
      show (u s')⁻¹ * (H s').1 x = (s' - s₀) ^ k * Ehat s' x
      by_cases hre : max t₀ t₁ < s'.re
      · simp only [Ehat, if_pos hre]
        rw [hHv s' hre x, hAs]
        field_simp
      · simp only [Ehat, if_neg hre]
        rw [hAs]
        field_simp
    · intro μ hμ
      have h1 : DifferentiableOn ℂ (fun s' => (u s')⁻¹) U := hud.inv fun s' hs' => (hUA s' hs').1
      have h2 : DifferentiableOn ℂ (fun s' => μ (H s')) U := (hHh μ hμ).differentiableOn
      refine (h1.mul h2).congr fun s' _ => ?_
      simp [map_smul, smul_eq_mul]
end PositivityTheory.SiegelWeilFormula.Aeis
end
end
end

section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace PositivityTheory.ThKW.LagrangianProjectionFormula
open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation PositivityTheory.ThKW.PhaseFourierInjectivity
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end PositivityTheory.ThKW.LagrangianProjectionFormula
end
open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation PositivityTheory.ThKW.PhaseFourierInjectivity PositivityTheory.ThKW.LagrangianProjectionFormula in
theorem PositivityTheory.ThKW.PhaseFourierInjectivity.finj_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
    ∀ N₁ N₂ : WOF F E nS nT → ℂ, Continuous N₁ → Continuous N₂ → Integrable N₁ ν → Integrable N₂ ν →
      (∀ y, ∫ v, phase σ JS JT ξ₀ B.ψ y v * N₁ v ∂ν = ∫ v, phase σ JS JT ξ₀ B.ψ y v * N₂ v ∂ν) → N₁ = N₂ := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕 N₁ N₂ c₁ c₂ i₁ i₂ hN
  have hψ : IsStd B.ψ := hB.std
  have hψn : ∀ a, ‖B.ψ a‖ = 1 := GlobalTheory.StdCharWeilDatum.norm_psi hB.std
  have hcc : ∀ z : AF F ⊗[F] E, cAF σ (cAF σ z) = z :=
    GlobalTheory.HeisLineF.cAF_cAF σ (GlobalTheory.SplitDetCharF.sig_invol hB.cm)
  have he : Continuous (vecE F E nS nT) := by
    show Continuous fun (w : WOF F E nS nT) (k : Fin (nT * nS)) => w (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
    exact continuous_pi fun k => continuous_id.matrix_elem _ _
  have he' : Continuous (vecE F E nS nT).symm := by
    show Continuous fun (u : Fin (nT * nS) → AF F ⊗[F] E) =>
      ((fun i j => u (finProdFinEquiv (i, j))) : WOF F E nS nT)
    first
      | exact continuous_pi fun i => continuous_pi fun j => continuous_apply _
      | fun_prop
  haveI : IsTopologicalAddGroup (AF F ⊗[F] E) := IsModuleTopology.topologicalAddGroup (AF F) (AF F ⊗[F] E)
  let E' : WOF F E nS nT ≃ₜ+ (Fin (nT * nS) → AF F ⊗[F] E) :=
    { toAddEquiv := vecE F E nS nT, continuous_toFun := he, continuous_invFun := he' }
  letI : MeasurableSpace (Fin (nT * nS) → AF F ⊗[F] E) := borel _
  haveI : BorelSpace (Fin (nT * nS) → AF F ⊗[F] E) := ⟨rfl⟩
  haveI : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  let em : WOF F E nS nT ≃ᵐ (Fin (nT * nS) → AF F ⊗[F] E) := E'.toHomeomorph.toMeasurableEquiv
  haveI := hν
  have hμ : (ν.map em).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map ν E'
  have hpc : ∀ a : WOF F E nS nT, Continuous (pr σ JS ξ₀ a) := fun a => IsModuleTopology.continuous_of_linearMap _
  have hph : ∀ a, Continuous (phase σ JS JT ξ₀ B.ψ a) := by
    intro a
    have e : phase σ JS JT ξ₀ B.ψ a = fun v => B.ψ (pr σ JS ξ₀ a (vecE F E nS nT v)) :=
      funext fun v => phase_eq σ JS JT hT.2 ξ₀ B.ψ a v
    rw [e]
    exact hψ.1.comp ((hpc a).comp he)
  have hint : ∀ a (N : WOF F E nS nT → ℂ), Integrable N ν →
      Integrable (fun v => phase σ JS JT ξ₀ B.ψ a v * N v) ν := by
    intro a N hNi
    refine hNi.bdd_mul (c := 1) (hph a).aestronglyMeasurable (Filter.Eventually.of_forall fun v => ?_)
    rw [phase_eq σ JS JT hT.2, hψn]
  set N : (Fin (nT * nS) → AF F ⊗[F] E) → ℂ := fun u => N₁ ((vecE F E nS nT).symm u) - N₂ ((vecE F E nS nT).symm u)
    with hNdef
  have hNc : Continuous N := (c₁.comp he').sub (c₂.comp he')
  have hNi : Integrable N (ν.map em) := by
    rw [integrable_map_equiv em N]
    have : N ∘ em = fun v => N₁ v - N₂ v := by
      funext v
      simp only [hNdef, Function.comp_apply]
      rw [show (vecE F E nS nT).symm (em v) = v from (vecE F E nS nT).symm_apply_apply v]
    rw [this]
    exact i₁.sub i₂
  have key : ∀ a, ∫ u, B.ψ (pr σ JS ξ₀ a u) * N u ∂(ν.map em) = 0 := by
    intro a
    rw [integral_map_equiv em]
    have hx : ∀ v, B.ψ (pr σ JS ξ₀ a (em v)) * N (em v) =
        phase σ JS JT ξ₀ B.ψ a v * N₁ v - phase σ JS JT ξ₀ B.ψ a v * N₂ v := by
      intro v
      have h1 : (vecE F E nS nT).symm (em v) = v := (vecE F E nS nT).symm_apply_apply v
      have h2 : em v = vecE F E nS nT v := rfl
      simp only [hNdef, h2, AddEquiv.symm_apply_apply]
      rw [phase_eq σ JS JT hT.2]
      ring
    simp_rw [hx]
    rw [integral_sub (hint a N₁ i₁) (hint a N₂ i₂), hN a, sub_self]
  have h0 := GlobalTheory.T.eq_zero_of_adelicFourier_separatingChars_vanish F E B.ψ hψ (nT * nS) (WOF F E nS nT) (pr σ JS ξ₀) (pr_add σ JS ξ₀)
    (fun u hu => pr_sep σ hcc hψ JS hS.2 ξ₀ hξ₀ u hu) (ν.map em) hμ N hNc hNi key
  funext v
  have := congrFun h0 (vecE F E nS nT v)
  simp only [hNdef, AddEquiv.symm_apply_apply, Pi.zero_apply] at this
  exact sub_eq_zero.1 this
end
end

section



section
noncomputable section
open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
namespace PositivityTheory.ThKW
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
  {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} {hc : HeisClosedF σ JS JT ξ₀ B.ψ} {w : 𝓞 E} {lam : ℕ →* ℂ}
  {Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)}
  {s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ}
theorem rat_subst_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) {γ : GAF σ JS} (hγ : γ ∈ GQF σ JS) {γ' : GAF σ JT} (hγ' : γ' ∈ GQF σ JT)
    {f : WOF F E nS nT → ℂ} (hf : IsThetaFunOF σ JS JT ξ₀ B.ψ f) :
    IsThetaFunOF σ JS JT ξ₀ B.ψ (fun x => f (actOF σ JS JT γ⁻¹ γ'⁻¹ x)) ∧
    (∀ w₀, (fun x => heisOF σ JS JT ξ₀ B.ψ w₀ f (actOF σ JS JT γ⁻¹ γ'⁻¹ x)) =
      heisOF σ JS JT ξ₀ B.ψ (actOF σ JS JT γ γ' w₀) (fun x => f (actOF σ JS JT γ⁻¹ γ'⁻¹ x))) ∧
    ∀ (μ : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), μ.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ →
        ∫⁻ x in 𝓕, ‖f (actOF σ JS JT γ⁻¹ γ'⁻¹ x)‖ₑ ^ 2 ∂μ = ∫⁻ x in 𝓕, ‖f x‖ₑ ^ 2 ∂μ := by
  have hψ : ∀ a, ‖B.ψ a‖ = 1 := (_root_.GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood_k F E σ B C.good).1.2.1
  have hi := (GQF σ JS).inv_mem hγ
  have hi' := (GQF σ JT).inv_mem hγ'
  have hinv : ∀ x, actOF σ JS JT γ γ' (actOF σ JS JT γ⁻¹ γ'⁻¹ x) = x := fun x => by
    have := SubstA.actOF_inv_actOF (σ := σ) (JS := JS) (JT := JT) γ⁻¹ γ'⁻¹ x
    rwa [inv_inv, inv_inv] at this
  refine ⟨SubstA.isThetaFunOF_comp C.hS hf hi hi', fun w₀ => ?_, fun μ 𝓕 hμ h𝓕 => ?_⟩
  · funext x
    unfold heisOF
    beta_reduce
    rw [GlobalTheory.FinLatF.actOF_add, SubstA.actOF_inv_actOF, ← SubstA.symplOHF_actOF C.hS γ⁻¹ γ'⁻¹ x,
      SubstA.actOF_inv_actOF]
  · let e : WOF F E nS nT ≃+ WOF F E nS nT :=
      { toFun := actOF σ JS JT γ⁻¹ γ'⁻¹
        invFun := actOF σ JS JT γ γ'
        left_inv := hinv
        right_inv := SubstA.actOF_inv_actOF γ γ'
        map_add' := GlobalTheory.FinLatF.actOF_add _ _ }
    refine SubstA.setLIntegral_comp e (SubstA.continuous_actOF _ _) (SubstA.continuous_actOF _ _)
      (fun x => ⟨fun hx => ?_, SubstA.actOF_mem_ratLF hi hi'⟩) μ hμ h𝓕 (fun w => ‖f w‖ₑ ^ 2) ?_
    · rw [← hinv x]
      exact SubstA.actOF_mem_ratLF hγ hγ' hx
    · rintro _ ⟨y, rfl⟩ x
      have h7 : ‖f (ratWF y + x)‖ = ‖f x‖ := by
        rw [hf.quasi y x, norm_mul, hψ, one_mul]
      show ‖f (ratWF y + x)‖ₑ ^ 2 = ‖f x‖ₑ ^ 2
      rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, h7]
theorem schur_norm_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (M : Module.End ℂ (WOF F E nS nT → ℂ))
    (h1 : ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → IsThetaFunOF σ JS JT ξ₀ B.ψ (M f))
    (h2 : ∀ u f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → M (heisOF σ JS JT ξ₀ B.ψ u f) = heisOF σ JS JT ξ₀ B.ψ u (M f))
    (h3 : ∀ (μ : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), μ.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ → ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f →
        ∫⁻ x in 𝓕, ‖M f x‖ₑ ^ 2 ∂μ = ∫⁻ x in 𝓕, ‖f x‖ₑ ^ 2 ∂μ) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → M f = c • f := by
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.T.theta_preserving_endomorphism_scalar F E σ B C.good nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ M h1 h2 h3
  have hψ : ∀ a, ‖B.ψ a‖ = 1 := (_root_.GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood_k F E σ B C.good).1.2.1
  by_cases h0 : ∃ f y, IsThetaFunOF σ JS JT ξ₀ B.ψ f ∧ f y ≠ 0
  · obtain ⟨f, y, hf, hy⟩ := h0
    obtain ⟨μ, 𝓕, hμ, h𝓕, hI0, hIt⟩ := GlobalTheory.ThetaSchurUnitF.exists_fd_pos_fin hψ hf hy
    have h := h3 μ 𝓕 hμ h𝓕 f hf
    rw [hc f hf] at h
    simp only [Pi.smul_apply, smul_eq_mul, enorm_mul, mul_pow] at h
    rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top enorm_ne_top)] at h
    have e1 : ‖c‖ₑ ^ 2 = 1 := by
      have := congrArg (· / ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ) h
      rwa [ENNReal.mul_div_cancel_right hI0 hIt, ENNReal.div_self hI0 hIt] at this
    have e2 : (‖c‖₊ : ENNReal) ^ 2 = 1 := by rwa [enorm_eq_nnnorm] at e1
    have e3 : ‖c‖₊ ^ 2 = 1 := by exact_mod_cast e2
    have e4 : ‖c‖ ^ 2 = 1 := by
      have := congrArg (fun t : NNReal => (t : ℝ)) e3
      simpa using this
    exact ⟨c, (pow_eq_one_iff_of_nonneg (norm_nonneg c) two_ne_zero).1 e4, hc⟩
  · push_neg at h0
    refine ⟨1, norm_one, fun f hf => ?_⟩
    have : f = 0 := funext fun y => h0 f y hf
    subst this
    simp
end PositivityTheory.ThKW
end
end
end

section



section
noncomputable section
namespace GlobalTheory.ThK.Dbl.Vf2
open scoped Matrix TensorProduct GlobalTheory.VacAny
open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.LatVac
open PositivityTheory.ThK PositivityTheory.ThK.Vac PositivityTheory.ThKH.Iwas PositivityTheory.ThKH.Locrep PositivityTheory.ThKG.Loc.Cone.Vf
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {v : Pl F}
theorem _root_.GlobalTheory.ThK.Dbl.vacFix2_k : _root_.GlobalTheory.ThK.Dbl.VacFix2_k := by
  intro F E _ _ _ _ _ σ B n d X W M r s r' s' hB hX hW hM χ _ dd omd ⟨d', hd', hdd⟩ ⟨_, hsp, hrule⟩ K hK v hv g hk hg
  have hL := hX.lat
  have vd := hM.vac v
  obtain ⟨hsb, h0, -⟩ := hM.vac v
  obtain ⟨r₀, x₀, h₀, h₁⟩ := exists_base (Fin n × Fin d) v
  set Φ := tens (evFin F v) (M.vac v) r₀ with hΦ
  have hΦs : Φ ∈ schA F _ := (h₀ _ hsb).2
  obtain ⟨y₀, hy⟩ := Function.ne_iff.1 h0
  have hΦy : Φ (putA v x₀ y₀) = M.vac v y₀ := by
    change M.vac v (evA _ v (putA v x₀ y₀)) * r₀ (putA v x₀ y₀) = _
    rw [ev_put (evA_inA v), inv_putA v (h₀ _ hsb).1, h₁, mul_one]
  have hΦ0 : Φ ≠ 0 := fun e => hy (by rw [← hΦy, e]; rfl)
  have q1 : PresD v X g.1.1 := presD_of fun z z' a b => ((hK g).1 hk).2 z z' a b g (.inl rfl)
  have q2 : PresD v X (g⁻¹).1.1 := presD_of fun z z' a b => ((hK g).1 hk).2 z z' a b g⁻¹ (.inr rfl)
  obtain ⟨c, hc⟩ := _root_.PositivityTheory.ThKG.Loc.Cone.Vf.dbl_eigen_k hB hX hW vd hd' hdd hsp.toIsSplitting g hg q2
  suffices h : c = 1 by rwa [h, one_smul] at hc
  obtain ⟨g₁, m₁, g₂, m₂, g₃, m₃, g₄, m₄, eg⟩ := q1
  obtain ⟨a₁, n₁, a₂, n₂, a₃, -, a₄, -, ea⟩ := q2
  have hD : g.1.1 * (diagCols (Fin n) : Matrix _ _ (AE F E)) = Matrix.fromRows (g₁ + g₂) (g₃ + g₄) := by
    rw [eg, diagCols, Matrix.fromBlocks_mul_fromRows]; simp
  have hI : a₁ * (g₁ + g₂) + a₂ * (g₃ + g₄) = 1 := by
    have : (g⁻¹).1.1 * (g.1.1 * (diagCols (Fin n) : Matrix _ _ (AE F E))) = diagCols (Fin n) := by
      rw [← Matrix.mul_assoc, show (g⁻¹).1.1 * g.1.1 = 1 from g.1.inv_mul, Matrix.one_mul]
    rw [hD, ea, Matrix.fromBlocks_mul_fromRows, diagCols] at this
    exact (Matrix.fromRows_inj this).1
  have aD := at_mul_left (M := g.1.1 - 1) hg (diagCols (Fin n) : Matrix _ _ (AE F E))
  rw [Matrix.sub_mul, Matrix.one_mul, hD] at aD
  have ax : At (evFin F v) (g₁ + g₂ - 1) := fun u hu => congrArg Matrix.toRows₁ (aD u hu)
  have ay : At (evFin F v) (g₃ + g₄ - 1) := fun u hu => congrArg Matrix.toRows₂ (aD u hu)
  have px := add_mem m₁ m₂
  have py := add_mem m₃ m₄
  generalize g₁ + g₂ = x at *
  generalize g₃ + g₄ = y at *
  obtain ⟨b, b', t', b1, hb, pb, pt, ht⟩ := _root_.GlobalTheory.ThK.Dbl.Vf2.exists_beta_k hB hX g hD px py n₁ n₂ hI ax ay
  have hm : At (evFin F v) (y - x) := by simpa using at_sub ay ax
  have pm := sub_mem py px
  obtain ⟨s₀, n₀, p, t, ss, eg', es, en, en', hn, hp, et, et'⟩ :=
    Vf2.exists_decomp b1 hb g hD ht (ε := PositivityTheory.ThKG.Loc.Cone.Vf.eps v) eps_mul ((cA σ).commutes _) (eps_smul hm)
  have o1 := one_mem (Pres v X)
  have z0 := zero_mem (Pres v X)
  have pC : PresD v X (CC b) := ⟨_, o1, _, add_mem o1 pb, _, o1, _, pb, rfl⟩
  have pCi : PresD v X (Ci b) := ⟨_, neg_mem pb, _, add_mem o1 pb, _, o1, _, neg_mem o1, rfl⟩
  have c1 : compFin F E v (PositivityTheory.ThKG.Loc.Cone.Vf.eps v : AE F E) = 1 := by rw [PositivityTheory.ThKG.Loc.Cone.Vf.eps, comp_alg, ev_sg]; rfl
  have pe : (PositivityTheory.ThKG.Loc.Cone.Vf.eps v : AE F E) • (1 : Matrix _ _ _) ∈ Pres v X := smul_mem_Pres hL (by rw [c1]; exact one_mem _) o1
  have pe' : (1 - PositivityTheory.ThKG.Loc.Cone.Vf.eps v : AE F E) • (1 : Matrix _ _ _) ∈ Pres v X :=
    smul_mem_Pres hL (by rw [map_sub, map_one, c1, sub_self]; exact zero_mem _) o1
  have bt : boxFun Φ (star Φ) = tens (evFin F v) (boxFun (M.vac v) (star (M.vac v))) (boxFun r₀ (star r₀)) := by
    funext x
    simp only [hΦ, boxFun, tens, Pi.star_apply, star_mul']
    exact mul_mul_mul_comm _ _ _ _
  have hΦd := GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ Φ hΦs _ (star_mem_schA hΦs)
  have hd0 : boxFun Φ (star Φ) ≠ 0 := fun e => lDiag_ne hΦs hΦ0 (by rw [e, map_zero])
  have rd : Rest (evFin F v) (boxFun (M.vac v) (star (M.vac v))) (boxFun r₀ (star r₀)) := by
    refine ⟨fun x z hz => ?_, bt ▸ hΦd⟩
    have i1 := (h₀ _ hsb).1 (x ∘ Sum.inl) (z ∘ Sum.inl) fun u hu => funext fun i => congrFun (hz u hu) _
    have i2 := (h₀ _ hsb).1 (x ∘ Sum.inr) (z ∘ Sum.inr) fun u hu => funext fun i => congrFun (hz u hu) _
    change r₀ (x ∘ Sum.inl + z ∘ Sum.inl) * star (r₀ (x ∘ Sum.inr + z ∘ Sum.inr)) = _
    rw [i1, i2]; rfl
  have ev : ∀ g : UG (cA σ) (dbl (incM F X.J)), At (evFin F v) (g.1.1 - 1) → PresD v X (g⁻¹).1.1 →
      ∃ a : ℂ, omd g (boxFun Φ (star Φ)) = a • boxFun Φ (star Φ) := fun g h1 h2 => by
    obtain ⟨a, ha⟩ := _root_.PositivityTheory.ThKG.Loc.Cone.Vf.dbl_eigen_k hB hX hW vd hd' hdd hsp.toIsSplitting g h1 h2
    exact ⟨a, by rw [bt, ha _ rd, tens_smul]⟩
  obtain ⟨a, ha⟩ := ev s₀ (by
      rw [es]
      refine at_conj (CC_Ci b) fun u hu => ?_
      have : u • (PositivityTheory.ThKG.Loc.Cone.Vf.eps v : AE F E) = 0 := at_eps u hu
      rw [SS, ← Matrix.fromBlocks_one, sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add, Matrix.fromBlocks_smul]
      simp only [sub_smul, one_smul, neg_zero, add_zero, ← sub_eq_add_neg, sub_sub_cancel_left, smul_neg, ← smul_assoc, this,
        zero_smul, Matrix.fromBlocks_zero])
    (by rw [inv_eq_of_mul_eq_one_right ss, es]; exact (pC.mul ⟨_, pe', _, pe, _, pe, _, pe', rfl⟩).mul pCi)
  obtain ⟨a', ha'⟩ := ev n₀ (by
      rw [en]
      refine at_conj (CC_Ci b) fun u hu => ?_
      rw [← Matrix.fromBlocks_one, sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add, Matrix.fromBlocks_smul]
      simp only [add_neg_cancel, neg_zero, add_zero, smul_zero, smul_neg]
      rw [at_mul_left hm t' u hu, neg_zero, Matrix.fromBlocks_zero])
    (by rw [en']; exact (pC.mul ⟨_, o1, _, mul_mem pm pt, _, z0, _, o1, rfl⟩).mul pCi)
  have a1 : a' = 1 := by
    rw [rule_diag hdd hrule n₀ 1 hn (by rw [map_one, map_one]) hΦs hΦ0 ha']
    simp
  have aa : a * a = 1 := by
    have e : omd (s₀ * s₀) (boxFun Φ (star Φ)) = (a * a) • boxFun Φ (star Φ) := by
      rw [map_mul, Module.End.mul_apply, ha, map_smul, ha, smul_smul]
    rw [ss, map_one, Module.End.one_apply] at e
    exact smul_left_injective ℂ hd0 (e.symm.trans (one_smul _ _).symm)
  have e1 : omd g (boxFun Φ (star Φ)) = c • boxFun Φ (star Φ) := by rw [bt, hc _ rd, tens_smul]
  have e2 : omd p (boxFun Φ (star Φ)) = c • boxFun Φ (star Φ) := by
    have e3 : omd (s₀ * n₀ * s₀) (boxFun Φ (star Φ)) = boxFun Φ (star Φ) := by
      rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, ha, map_smul, ha', a1, one_smul, map_smul, ha, smul_smul,
        aa, one_smul]
    have : p = (s₀ * n₀ * s₀)⁻¹ * g := by rw [eg']; group
    rw [this, map_mul, Module.End.mul_apply, e1, map_smul]
    conv_lhs => rw [← e3, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  have hpos := rule_diag hdd hrule p t hp (chi_det hL χ hv t (by rw [et]; exact add_mem py (mul_mem pb pm)) (by rw [et']; exact pt)
    (by rw [et, add_sub_right_comm]; exact at_add ay (at_mul_right _ hm))) hΦs hΦ0 e2
  have n4 := Bad.norm_eig hsp.unit hsp.pres hΦd hd0 e1
  rw [hpos] at n4 ⊢
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)] at n4
  rw [n4, Complex.ofReal_one]
end GlobalTheory.ThK.Dbl.Vf2
end
end
end

section



section
namespace GlobalTheory.ThK.Dbl
theorem hgtEx_k : _root_.GlobalTheory.ThK.Dbl.HgtEx_k := _root_.GlobalTheory.ThK.Dbl.hgtEx_of_k _root_.GlobalTheory.ThK.Dbl.stab2Cpt_k
end GlobalTheory.ThK.Dbl
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl
namespace UpperTheory.TP
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {X : Spc F E n}
private theorem hgt_swap_pk (hJ : X.J.det ≠ 0) {K : Subgroup (G2 σ X)} {a : G2 σ X → ℝ} (ha : IsHgt K a)
    {e : UA σ X.J × UA σ X.J →* G2 σ X} (he : ∀ g g', IsEmb g g' (e (g, g'))) (g : UA σ X.J) :
    a (e (g, 1)) = a (e (1, g⁻¹)) := by
  have hp : IsPar (e (g, g)) (g : GL (Fin n) (AE F E)) := by
    change mat2 (e (g, g)) * diagCols (E := AE F E) (Fin n) = diagCols (E := AE F E) (Fin n) * mat g
    rw [he, diagCols, Matrix.fromRows_mul, Matrix.fromBlocks_mul_fromRows]
    simp
  have e1 : e (g, 1) = e (g, g) * e (1, g⁻¹) := by
    rw [← map_mul, Prod.mk_mul_mk, mul_one, mul_inv_cancel]
  rw [e1, ha.mul hp, GlobalTheory.WeilEx.Jac.absE_det_unitary hJ g]
  simp
end UpperTheory.TP
theorem UpperTheory.TP.hgtFst_k :
    _root_.UpperTheory.TP.Tools_k → _root_.UpperTheory.TP.HgtFst_k := by
  intro T F E _ _ _ _ _ σ B n X hB hX K a e hK ha he
  have cX := T.cpt F E σ B n X n 0 hB (.inl hX) (by simp)
  haveI := cX.lc
  haveI := cX.sc
  obtain ⟨μ₀, D, hμ₀, -⟩ := cX.ex
  obtain ⟨t₀, ht₀⟩ := _root_.GlobalTheory.ThK.Dbl.hgtInt_of_k T.stab2 F E σ B n X n 0 hB (.inl hX) K a e hK ha he μ₀ hμ₀
  refine ⟨t₀, fun μ hμ t ht => ?_⟩
  haveI := hμ
  haveI := hμ₀
  haveI := cX.right μ hμ
  have hJ : X.J.det ≠ 0 := GlobalTheory.ThK.Dbl.Hgt.det_ne (.inl hX)
  have h1 : Integrable (fun g => a (e (1, g)) ^ t) μ := by
    rw [Measure.isMulLeftInvariant_eq_smul μ μ₀]
    exact (ht₀ t ht).smul_measure ENNReal.coe_ne_top
  obtain ⟨c, -, hc⟩ := inv_scale μ
  have h2 : Integrable (fun g => ((a (e (g, 1)) ^ t : ℝ) : ℂ)) μ := (hc _).1 (by
    simp only [UpperTheory.TP.hgt_swap_pk hJ ha he, inv_inv]
    exact h1.ofReal)
  simpa using h2.re
end
end
end
