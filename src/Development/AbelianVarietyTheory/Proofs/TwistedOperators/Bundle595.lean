module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUniqueIsProdMeasureFinAway
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumThetaJointlyContinuous
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousIntegrand
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle133
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle346
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentBesselCharacterLaws
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle485
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle411
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle584
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle557
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle026
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Mathlib.Data.FunLike.Fintype
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle342
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle231
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle026
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFinWeil
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLatticeIntertwinerCoefficientAtPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle170
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLatticeVacuumStabilizerSplittingCharacters
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.HandTame

theorem integral_prod_four {α β γ δ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
    (μ₁ : Measure α) (μ₂ : Measure β) (μ₃ : Measure γ) (μ₄ : Measure δ) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    [IsFiniteMeasure μ₃] [IsFiniteMeasure μ₄]
    (F : α × β × γ × δ → ℂ) (hF : Integrable F (μ₁.prod (μ₂.prod (μ₃.prod μ₄)))) :
    ∫ y, F y ∂(μ₁.prod (μ₂.prod (μ₃.prod μ₄))) = ∫ a, ∫ b, ∫ c, ∫ d, F (a, b, c, d) ∂μ₄ ∂μ₃ ∂μ₂ ∂μ₁ := by
  rw [integral_prod _ hF]
  refine integral_congr_ae (hF.prod_right_ae.mono fun a ha => ?_)
  simp only
  rw [integral_prod _ ha]
  refine integral_congr_ae (ha.prod_right_ae.mono fun b hb => ?_)
  simp only
  rw [integral_prod _ hb]

theorem sfinite_of_finite {α : Type} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ] : SFinite μ := inferInstance

variable {D : D7}

theorem tame_congr {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {ℓ ℓ' : (WO S T → ℂ) → ℂ}
    (h : Tame ψ S T ℓ) (e : ∀ f, IsThetaFunO ψ S T f → ℓ' f = ℓ f) : Tame ψ S T ℓ' := by
  have hh : ∀ f, IsThetaFunO ψ S T f → ∀ w, ℓ' (heisO ψ S T w f) = ℓ (heisO ψ S T w f) := fun f hf w =>
    e _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf w)
  refine ⟨fun f f' hf hf' => ?_, fun c f hf => ?_, fun f hf => ?_, fun f hf => ?_, fun f hf m _ α hα hI => ?_⟩
  · rw [e _ (GlobalTheory.WeilVacMove.isTheta_add hf hf'), e _ hf, e _ hf', h.add f f' hf hf']
  · rw [e _ (GlobalTheory.WeilVacMove.isTheta_smul c hf), e _ hf, h.smul c f hf]
  · simp only [hh f hf]; exact h.cont f hf
  · simp only [hh f hf]; exact h.bdd f hf
  · simp only [hh f hf]; rw [e _ hI]; exact h.sup f hf m α hα hI

theorem rapid_core {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {G : GA D S → ℂ} (hG : RapidDec S G) (k : ℕ) :
    ∃ C : ℝ, ∀ n ∈ flagN d, ∀ h, ‖G (n * d.emb0 h)‖ * quotHeight S₀ h ^ k ≤ C := by
  obtain ⟨C, a, hC⟩ := GlobalTheory.T.unitaryQuotientHeight_comparable_wittDecomposition D S S₀ ρ d
  obtain ⟨C', hC'⟩ := hG.decay (a * k)
  refine ⟨|C| ^ k * C', fun n hn h => ?_⟩
  have h1 : quotHeight S₀ h ≤ |C| * quotHeight S (n * d.emb0 h) ^ a :=
    (hC n hn h).1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_pos (quotHeight_pos S _) a).le)
  calc ‖G (n * d.emb0 h)‖ * quotHeight S₀ h ^ k
      ≤ ‖G (n * d.emb0 h)‖ * (|C| * quotHeight S (n * d.emb0 h) ^ a) ^ k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (quotHeight_pos S₀ h).le h1 k) (norm_nonneg _)
    _ = |C| ^ k * (‖G (n * d.emb0 h)‖ * quotHeight S (n * d.emb0 h) ^ (a * k)) := by rw [mul_pow, ← pow_mul]; ring
    _ ≤ |C| ^ k * C' := mul_le_mul_of_nonneg_left (hC' _) (by positivity)

theorem rapid_theta {ψ : AddChar (AF D.host.F) ℂ} {S L : HSp D} {χ χz : (AE D)ˣ →* Circle} {om : Om S L}
    (hom : IsWeilDatumO ψ S L χ χz om) {φ : GA D S → ℂ} (hφ : RapidDec S φ) {Φ₀ : WO S L → ℂ} (hΦ : IsThetaFunO ψ S L Φ₀)
    (k : ℕ) : ∃ C : ℝ, ∀ h v, ‖φ h‖ * ‖om (h, 1) Φ₀ v‖ * quotHeight S h ^ k ≤ C := by
  obtain ⟨C, a, hC⟩ := GlobalTheory.SupThetaGrowth.om_sup_quotHeight D ψ S L χ χz om hom Φ₀ hΦ
  obtain ⟨C', hC'⟩ := hφ.decay (a + k)
  refine ⟨|C| * C', fun h v => ?_⟩
  have h1 : ‖om (h, 1) Φ₀ v‖ ≤ |C| * quotHeight S h ^ a := by
    have := hC h 1 v
    rw [quotHeight_of_mem L (one_mem _), mul_one] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_pos (quotHeight_pos S _) a).le)
  calc ‖φ h‖ * ‖om (h, 1) Φ₀ v‖ * quotHeight S h ^ k
      ≤ ‖φ h‖ * (|C| * quotHeight S h ^ a) * quotHeight S h ^ k :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)) (pow_pos (quotHeight_pos S _) k).le
    _ = |C| * (‖φ h‖ * quotHeight S h ^ (a + k)) := by ring
    _ ≤ |C| * C' := mul_le_mul_of_nonneg_left (hC' _) (abs_nonneg _)

theorem handP₂ : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B),
    ∀ (vL : VolM D B.L.rank J.W₀.rank) (χ χz : (AE D)ˣ →* Circle) (omz : Om J.W₀ B.L), IsWeilDatumO ψ J.W₀ B.L χ χz omz →
    ∀ (φ : GA D J.W₀ → ℂ) (G : GA D B.V → ℂ) (Φ₀ : WO J.W₀ B.L → ℂ), RapidDec J.W₀ φ → RapidDec B.V G →
    IsThetaFunO ψ J.W₀ B.L Φ₀ → Tame ψ J.W₀ B.V₀ fun Ξ => B.per ψ (handP s vL omz φ Φ₀ Ξ) G := by
  intro D ψ σ J B s vL χ χz omz homz φ G Φ₀ hφ hG hΦ
  have hψ := homz.std
  haveI : ∀ V : HSp D, SecondCountableTopology (GA D V) := fun V => (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V).2.1
  haveI : ∀ V : HSp D, BorelSpace (GA D V) := fun V => ⟨rfl⟩
  obtain ⟨-, -, i3, -, -, -⟩ := GlobalTheory.MixModel.lattice_Mx D B.L.rank J.W₀.rank
  haveI : SecondCountableTopology (WO J.W₀ B.L) := i3
  haveI : BorelSpace (WO J.W₀ B.L) := ⟨rfl⟩
  haveI : IsFiniteMeasure (B.vA.μ.restrict B.vA.𝓕) := isFiniteMeasure_restrict.2
    (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol B.A _ _ B.vA.haar B.vA.fund).ne
  haveI : IsFiniteMeasure (J.v0.μ.restrict J.v0.𝓕) := isFiniteMeasure_restrict.2
    (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol J.W₀ _ _ J.v0.haar J.v0.fund).ne
  haveI : IsFiniteMeasure (B.vN.ν.restrict B.vN.𝓝) := isFiniteMeasure_restrict.2 (by rw [B.vN.unit.2.2]; exact ENNReal.one_ne_top)
  haveI : IsFiniteMeasure (vL.μ.restrict vL.𝓕) := isFiniteMeasure_restrict.2 (by rw [vL.covol.2.2]; exact ENNReal.one_ne_top)
  let Y : Type := GA D B.A × flagN B.d × GA D J.W₀ × WO J.W₀ B.L
  let m : Measure Y := (B.vA.μ.restrict B.vA.𝓕).prod ((B.vN.ν.restrict B.vN.𝓝).prod
    ((J.v0.μ.restrict J.v0.𝓕).prod (vL.μ.restrict vL.𝓕)))
  haveI : IsFiniteMeasure m := by dsimp only [m]; infer_instance
  haveI : SFinite m := sfinite_of_finite m
  let c : Y → ℂ := fun y => G (y.2.1.1 * embA B.d B.o y.1) * star (psiBes ψ B.d 1 (vecB B.o B.ζ) y.2.1.1) *
    (φ y.2.2.1 * star (omz (y.2.2.1, 1) Φ₀ y.2.2.2))
  have hn : Continuous fun y : Y => (y.2.1.1 : GA D B.V) := continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
  have h0 : Continuous fun y : Y => y.2.2.1 := continuous_fst.comp (continuous_snd.comp continuous_snd)
  have hv : Continuous fun y : Y => y.2.2.2 := continuous_snd.comp (continuous_snd.comp continuous_snd)
  have he : Continuous fun y : Y => B.o.emb (y.1, 1) := B.o.continuous_emb.comp (continuous_fst.prodMk continuous_const)
  have hw : Continuous fun y : Y => (B.o.resT J.W₀).symm (0, y.2.2.2) :=
    (B.o.continuous_resT_symm J.W₀).comp (continuous_const.prodMk hv)
  haveI := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.V).2.2.2.2.1
  have hJ : Continuous fun p : (GA D J.W₀ × GA D B.L) × WO J.W₀ B.L => omz p.1 Φ₀ p.2 :=
    (@GlobalTheory.Unf.jointCont_all D) ψ _ _ χ χz omz homz Φ₀ hΦ
  have hc : Continuous c :=
    ((hG.continuous.comp (hn.mul (B.d.continuous_embed.comp he))).mul
      (continuous_star.comp ((GlobalTheory.CharLaws.continuous_psiBes ψ B.d hψ.1.1 1 _).comp hn))).mul
      ((hφ.continuous.comp h0).mul (continuous_star.comp (hJ.comp ((h0.prodMk continuous_const).prodMk hv))))
  have hint : ∀ k : ℕ, Integrable
      (fun y : Y => ‖c y‖ * (quotHeight J.W₀ y.2.2.1 * quotHeight B.V₀ (B.o.emb (y.1, 1))) ^ k) m := by
    intro k
    obtain ⟨C₁, h₁⟩ := rapid_core B.d hG k
    obtain ⟨C₂, h₂⟩ := rapid_theta homz hφ hΦ k
    have hcc : Continuous fun y : Y => ‖c y‖ * (quotHeight J.W₀ y.2.2.1 * quotHeight B.V₀ (B.o.emb (y.1, 1))) ^ k :=
      hc.norm.mul ((((continuous_quotHeight _).comp h0).mul ((continuous_quotHeight _).comp he)).pow k)
    refine Integrable.of_bound hcc.measurable.aestronglyMeasurable (C₁ * C₂) (.of_forall fun y => ?_)
    have p1 := quotHeight_pos J.W₀ y.2.2.1
    have p2 := quotHeight_pos B.V₀ (B.o.emb (y.1, 1))
    have n1 : ‖psiBes ψ B.d 1 (vecB B.o B.ζ) y.2.1.1‖ = 1 := hψ.1.2.1 _
    rw [Real.norm_of_nonneg (by positivity)]
    have a1 := h₁ _ y.2.1.2 (B.o.emb (y.1, 1))
    have a2 := h₂ y.2.2.1 y.2.2.2
    calc ‖c y‖ * (quotHeight J.W₀ y.2.2.1 * quotHeight B.V₀ (B.o.emb (y.1, 1))) ^ k
        = (‖G (y.2.1.1 * B.d.emb0 (B.o.emb (y.1, 1)))‖ * quotHeight B.V₀ (B.o.emb (y.1, 1)) ^ k) *
          (‖φ y.2.2.1‖ * ‖omz (y.2.2.1, 1) Φ₀ y.2.2.2‖ * quotHeight J.W₀ y.2.2.1 ^ k) := by
          simp only [c, norm_mul, norm_star, n1, embA_apply, mul_pow]; ring
      _ ≤ C₁ * C₂ := mul_le_mul a1 a2 (by positivity) (le_trans (by positivity) a1)
  obtain ⟨hI, hT⟩ := GlobalTheory.T.weilKernelFunctional_superposition_isTame D ψ J.W₀ B.V₀ s.χV s.χW s.om₀ s.weil₀ Y m c (fun y => y.2.2.1) (fun y => B.o.emb (y.1, 1))
    (fun y => (B.o.resT J.W₀).symm (0, y.2.2.2)) hc.measurable h0 he hw hint
  refine tame_congr hψ hT fun f hf => ?_
  refine Eq.trans ?_ (integral_prod_four _ _ _ _ _ (hI f hf)).symm
  simp only [BesL.per, besPer, GlobalTheory.MixPer.besFun, handP, contractT, thPair]
  refine integral_congr_ae (.of_forall fun a => ?_)
  refine integral_congr_ae (.of_forall fun b => ?_)
  simp only
  rw [mul_assoc, ← integral_mul_const]
  refine integral_congr_ae (.of_forall fun x => ?_)
  simp only
  rw [← integral_const_mul, ← integral_mul_const]
  refine integral_congr_ae (.of_forall fun v => ?_)
  simp only [c]
  ring

end GlobalTheory.HandTame

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.PerAllTame

variable {D : D7}

theorem tame_congr {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {ℓ ℓ' : (WO S T → ℂ) → ℂ}
    (h : Tame ψ S T ℓ) (e : ∀ f, IsThetaFunO ψ S T f → ℓ' f = ℓ f) : Tame ψ S T ℓ' := by
  have hθ : ∀ w f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (heisO ψ S T w f) :=
    fun w f hf => GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf w
  refine ⟨fun f f' hf hf' => ?_, fun c f hf => ?_, fun f hf => ?_, fun f hf => ?_, fun f hf m _ α hα hs => ?_⟩
  · rw [e _ (GlobalTheory.OrientedHeis.theta_add hf hf'), e _ hf, e _ hf', h.add f f' hf hf']
  · rw [e _ (GlobalTheory.OrientedHeis.theta_smul c hf), e _ hf, h.smul c f hf]
  · have hfun : (fun w => ℓ' (heisO ψ S T w f)) = fun w => ℓ (heisO ψ S T w f) :=
      funext fun w => e _ (hθ w f hf)
    rw [hfun]
    exact h.cont f hf
  · obtain ⟨C, hC⟩ := h.bdd f hf
    exact ⟨C, fun w => (e _ (hθ w f hf)).symm ▸ hC w⟩
  · have hfun : (fun w => α w * ℓ' (heisO ψ S T w f)) = fun w => α w * ℓ (heisO ψ S T w f) :=
      funext fun w => by rw [e _ (hθ w f hf)]
    rw [hfun, e _ hs]
    exact h.sup f hf m α hα hs

theorem decay_of_le {V : HSp D} {F : GA D V → ℂ} (hF : RapidDec V F) (C : ℝ) (a k : ℕ) :
    ∃ C' : ℝ, ∀ (g : GA D V) (t : ℝ), 0 ≤ t → t ≤ C * quotHeight V g ^ a → ‖F g‖ * t ^ k ≤ C' := by
  obtain ⟨-, -, hd⟩ := hF
  obtain ⟨C₀, hC₀⟩ := hd (a * k)
  refine ⟨|C| ^ k * max C₀ 0, fun g t ht0 htle => ?_⟩
  have hq : (0 : ℝ) ≤ quotHeight V g ^ a := pow_nonneg (le_trans zero_le_one (one_le_quotHeight V g)) a
  have ht : t ≤ |C| * quotHeight V g ^ a := htle.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hq)
  calc ‖F g‖ * t ^ k ≤ ‖F g‖ * (|C| * quotHeight V g ^ a) ^ k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht0 ht k) (norm_nonneg _)
    _ = |C| ^ k * (‖F g‖ * quotHeight V g ^ (a * k)) := by rw [mul_pow, ← pow_mul]; ring
    _ ≤ |C| ^ k * max C₀ 0 :=
        mul_le_mul_of_nonneg_left ((hC₀ g).trans (le_max_left _ _)) (pow_nonneg (abs_nonneg _) _)

theorem perAll_tame : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ σ : ℕ) (B : BesL D σ) (J : JacL D ρ) (χ χ' : (AE D)ˣ →* Circle) (om₀ : Om B.V₀ J.W₀), IsWeilDatumO ψ B.V₀ J.W₀ χ χ' om₀ → ∀ (φ : GA D B.A → ℂ) (G : GA D J.W → ℂ), RapidDec B.A φ → RapidDec J.W G → Tame ψ B.V₀ J.W₀ (J.perAll ψ B om₀ φ G) := by
  intro D ψ ρ σ B J χ χ' om₀ hW φ G hφ hG
  have hψ : IsStdChar D ψ (-1) := hW.std
  have hψc : Continuous ψ := hψ.1.1
  have hψn : ∀ x, ‖ψ x‖ = 1 := hψ.1.2.1
  have hGc : Continuous G := hG.2.1
  have hφc : Continuous φ := hφ.2.1
  haveI : SecondCountableTopology (flagN J.d) := TopologicalSpace.Subtype.secondCountableTopology _
  have hF : J.v0.μ J.v0.𝓕 < ⊤ :=
    GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol J.W₀ J.v0.μ J.v0.𝓕 J.v0.haar J.v0.fund
  have hFA : B.vA.μ B.vA.𝓕 < ⊤ :=
    GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol B.A B.vA.μ B.vA.𝓕 B.vA.haar B.vA.fund
  have hN : J.vN.ν J.vN.𝓝 = 1 := J.vN.unit.2.2
  haveI : IsFiniteMeasure (J.v0.μ.restrict J.v0.𝓕) := isFiniteMeasure_restrict.mpr hF.ne
  haveI : IsFiniteMeasure (B.vA.μ.restrict B.vA.𝓕) := isFiniteMeasure_restrict.mpr hFA.ne
  haveI : IsFiniteMeasure (J.vN.ν.restrict J.vN.𝓝) :=
    isFiniteMeasure_restrict.mpr (by rw [hN]; exact ENNReal.one_ne_top)
  have hpf : Continuous (psiFlag ψ J.d) := GlobalTheory.Unf.EvalCont.continuous_psiFlag hψc J.d
  have hcen : Continuous (cenT J.d B.L (yZero B.L ρ B.ζ)) := GlobalTheory.Unf.EvalCont.continuous_cenT J.d B.L _
  have hpt : Continuous (ptT J.d B.L (yZero B.L ρ B.ζ)) := GlobalTheory.Unf.EvalCont.continuous_ptT J.d B.L _
  have hn : Continuous fun y : (GA D J.W₀ × flagN J.d) × GA D B.A => (y.1.2 : GA D J.W) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_fst)
  have hh1 : Continuous fun y : (GA D J.W₀ × flagN J.d) × GA D B.A => y.1.1 :=
    continuous_fst.comp continuous_fst
  have hx : Continuous fun y : (GA D J.W₀ × flagN J.d) × GA D B.A => (y.1.2 : GA D J.W) * J.d.emb0 y.1.1 :=
    hn.mul (J.d.continuous_embed.comp hh1)
  have hgg : Continuous fun y : (GA D J.W₀ × flagN J.d) × GA D B.A => B.o.emb (y.2, 1) :=
    B.o.continuous_emb.comp (continuous_snd.prodMk continuous_const)
  have hww : Continuous fun y : (GA D J.W₀ × flagN J.d) × GA D B.A =>
      (B.o.resS J.W₀).symm (0, ptT J.d B.L (yZero B.L ρ B.ζ) (y.1.2 : GA D J.W)) :=
    (B.o.continuous_resS_symm J.W₀).comp (continuous_const.prodMk (hpt.comp hn))
  have hcc : Continuous fun y : (GA D J.W₀ × flagN J.d) × GA D B.A =>
      G ((y.1.2 : GA D J.W) * J.d.emb0 y.1.1) * star (psiFlag ψ J.d (y.1.2 : GA D J.W)) * φ y.2 *
        ψ (cenT J.d B.L (yZero B.L ρ B.ζ) (y.1.2 : GA D J.W)) :=
    (((hGc.comp hx).mul (hpf.comp hn).star).mul (hφc.comp continuous_snd)).mul (hψc.comp (hcen.comp hn))
  obtain ⟨C₁, a₁, hC₁⟩ := GlobalTheory.T.unitaryQuotientHeight_orthogonalSum_comparable D B.V₀ B.A B.L B.o
  obtain ⟨C₂, a₂, hC₂⟩ := GlobalTheory.T.unitaryQuotientHeight_comparable_wittDecomposition D J.W J.W₀ ρ J.d
  have key : ∀ k : ℕ, Integrable (fun y : (GA D J.W₀ × flagN J.d) × GA D B.A =>
      ‖G ((y.1.2 : GA D J.W) * J.d.emb0 y.1.1) * star (psiFlag ψ J.d (y.1.2 : GA D J.W)) * φ y.2 *
        ψ (cenT J.d B.L (yZero B.L ρ B.ζ) (y.1.2 : GA D J.W))‖ *
        (quotHeight B.V₀ (B.o.emb (y.2, 1)) * quotHeight J.W₀ y.1.1) ^ k)
      (((J.v0.μ.restrict J.v0.𝓕).prod (J.vN.ν.restrict J.vN.𝓝)).prod (B.vA.μ.restrict B.vA.𝓕)) := by
    intro k
    obtain ⟨K₁, hK₁⟩ := decay_of_le hφ C₁ a₁ k
    obtain ⟨K₂, hK₂⟩ := decay_of_le hG C₂ a₂ k
    have hq : Continuous fun y : (GA D J.W₀ × flagN J.d) × GA D B.A =>
        (quotHeight B.V₀ (B.o.emb (y.2, 1)) * quotHeight J.W₀ y.1.1) ^ k :=
      (((continuous_quotHeight B.V₀).comp hgg).mul ((continuous_quotHeight J.W₀).comp hh1)).pow k
    refine Integrable.mono' (integrable_const (K₁ * K₂)) (hcc.norm.mul hq).aestronglyMeasurable
      (ae_of_all _ fun y => ?_)
    have q1 : 0 ≤ quotHeight B.V₀ (B.o.emb (y.2, 1)) := zero_le_one.trans (one_le_quotHeight _ _)
    have q2 : 0 ≤ quotHeight J.W₀ y.1.1 := zero_le_one.trans (one_le_quotHeight _ _)
    have b1 := hK₁ y.2 _ q1 (hC₁ y.2).2
    have b2 := hK₂ _ _ q2 (hC₂ y.1.2 y.1.2.2 y.1.1).1
    have n1 : ‖star (psiFlag ψ J.d (y.1.2 : GA D J.W))‖ = 1 := by
      rw [norm_star]; unfold psiFlag psiE; exact hψn _
    have p1 : 0 ≤ ‖φ y.2‖ * quotHeight B.V₀ (B.o.emb (y.2, 1)) ^ k := by positivity
    have p2 : 0 ≤ ‖G ((y.1.2 : GA D J.W) * J.d.emb0 y.1.1)‖ * quotHeight J.W₀ y.1.1 ^ k := by positivity
    rw [Real.norm_of_nonneg (by positivity), norm_mul, norm_mul, norm_mul, n1, hψn, mul_pow]
    calc ‖G ((y.1.2 : GA D J.W) * J.d.emb0 y.1.1)‖ * 1 * ‖φ y.2‖ * 1 *
          (quotHeight B.V₀ (B.o.emb (y.2, 1)) ^ k * quotHeight J.W₀ y.1.1 ^ k)
        = (‖φ y.2‖ * quotHeight B.V₀ (B.o.emb (y.2, 1)) ^ k) *
          (‖G ((y.1.2 : GA D J.W) * J.d.emb0 y.1.1)‖ * quotHeight J.W₀ y.1.1 ^ k) := by ring
      _ ≤ K₁ * K₂ := mul_le_mul b1 b2 p2 (p1.trans b1)
  obtain ⟨hint, htame⟩ := GlobalTheory.T.weilKernelFunctional_superposition_isTame D ψ B.V₀ J.W₀ χ χ' om₀ hW ((GA D J.W₀ × flagN J.d) × GA D B.A)
    (((J.v0.μ.restrict J.v0.𝓕).prod (J.vN.ν.restrict J.vN.𝓝)).prod (B.vA.μ.restrict B.vA.𝓕))
    (fun y => G ((y.1.2 : GA D J.W) * J.d.emb0 y.1.1) * star (psiFlag ψ J.d (y.1.2 : GA D J.W)) * φ y.2 *
        ψ (cenT J.d B.L (yZero B.L ρ B.ζ) (y.1.2 : GA D J.W)))
    (fun y => B.o.emb (y.2, 1)) (fun y => y.1.1)
    (fun y => (B.o.resS J.W₀).symm (0, ptT J.d B.L (yZero B.L ρ B.ζ) (y.1.2 : GA D J.W)))
    hcc.measurable hgg hh1 hww key
  refine tame_congr hψ htame fun Ξ hΞ => ?_
  have hI := hint Ξ hΞ
  rw [MeasureTheory.integral_prod _ hI, MeasureTheory.integral_prod _ hI.integral_prod_left]
  simp only [JacL.perAll, fjAll, fjAllFun,
    GlobalTheory.Unf.fjKer_eq_om_apply D ψ J.W J.W₀ B.V₀ B.A B.L ρ J.d B.o B.ζ χ χ' om₀ hW Ξ hΞ,
    ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (ae_of_all _ fun h => ?_)
  refine MeasureTheory.integral_congr_ae (ae_of_all _ fun n => ?_)
  refine MeasureTheory.integral_congr_ae (ae_of_all _ fun h₀ => ?_)
  dsimp only
  ring

end GlobalTheory.PerAllTame

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.RealAvg

open MvPolynomial

theorem mapDomain_fst_apply {ι κ : Type} [DecidableEq ι] (k : ι × κ →₀ ℕ) (τ : ι) :
    Finsupp.mapDomain Prod.fst k τ = ∑ v ∈ k.support with v.1 = τ, k v := by
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finsupp.single_apply]

def Mon (D : D7) (m n : ℕ) (d : D.what₂.Tau →₀ ℕ) : Set (FVar D m n →₀ ℕ) := {k | Finsupp.mapDomain Prod.fst k = d}

open Classical in
theorem mon_finite (D : D7) (m n : ℕ) (d : D.what₂.Tau →₀ ℕ) : (Mon D m n d).Finite :=
  (GlobalTheory.finite_monomials_of_placeDegree D m n (fun τ => d τ)).subset fun k hk τ => by
    have e := mapDomain_fst_apply k τ
    rw [show Finsupp.mapDomain Prod.fst k = d from hk] at e
    convert e.symm

noncomputable instance (D : D7) (m n : ℕ) (d : D.what₂.Tau →₀ ℕ) : Fintype (Mon D m n d) := (mon_finite D m n d).fintype

variable {D : D7}

def substMat (θ : InfFam D) (V : HSp D) (m : ℕ) (d : D.what₂.Tau →₀ ℕ) (g : GA D V) :
    Matrix (Mon D m V.rank d) (Mon D m V.rank d) ℂ :=
  fun k' k => AddMonoidAlgebra.coeff (GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin m) (Fin m) ℂ))
    (fun τ => compAt θ τ (Formalism.L2.Theta.mt V g)) (monomial k.1 1)) k'.1

open MvPolynomial

theorem substF_one {ι : Type} {N n : ℕ} (P : MvPolynomial (ι × Fin N × Fin n) ℂ) :
    GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) P = P := by
  have key : GlobalTheory.CompactHowe.substF (ι := ι) (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ))
      (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) = AlgHom.id ℂ _ := by
    refine algHom_ext fun p => ?_
    rw [GlobalTheory.CompactHowe.substF_X, Finset.sum_eq_single p.2.1, Finset.sum_eq_single p.2.2]
    · simp
    · intro l _ hl; simp [Matrix.one_apply_ne hl]
    · simp
    · intro k _ hk; simp [Matrix.one_apply_ne hk]
    · simp
  rw [key]; rfl

theorem eq_sum_mon {D : D7} {m n : ℕ} {d : D.what₂.Tau →₀ ℕ} (P : MvPolynomial (FVar D m n) ℂ)
    (hP : ∀ k', AddMonoidAlgebra.coeff P k' ≠ 0 → k' ∈ Mon D m n d) :
    P = ∑ k : Mon D m n d, AddMonoidAlgebra.coeff P k.1 • monomial k.1 (1 : ℂ) := by
  classical
  ext k'
  rw [coeff_sum]
  simp only [MvPolynomial.coeff_smul, coeff_monomial, smul_eq_mul, mul_ite, mul_one, mul_zero]
  by_cases hk : k' ∈ Mon D m n d
  · rw [Finset.sum_eq_single ⟨k', hk⟩]
    · simp
    · intro b _ hb; rw [if_neg]; intro h; exact hb (Subtype.ext h)
    · simp
  · rw [Finset.sum_eq_zero]
    · by_contra h; exact hk (hP k' h)
    · intro b _; rw [if_neg]; rintro rfl; exact hk b.2

variable {D : D7}

theorem substMat_one (θ : InfFam D) (V : HSp D) (m : ℕ) (d : D.what₂.Tau →₀ ℕ) : substMat θ V m d 1 = 1 := by
  classical
  ext k' k
  simp only [substMat, GlobalTheory.StdUnn.CartanMove.compAt_mt_one, substF_one, coeff_monomial, Matrix.one_apply]
  by_cases h : k' = k
  · subst h; simp
  · have h' : (k.1 : FVar D m V.rank →₀ ℕ) ≠ k'.1 := fun e => h (Subtype.ext e.symm)
    simp [h, h']

theorem one_alg (m : ℕ) (i : D.what₂.Tau) (a b : Fin m) :
    IsAlgebraic ℚ ((fun _ : D.what₂.Tau => (1 : Matrix (Fin m) (Fin m) ℂ)) i a b) := by
  by_cases hab : a = b
  · subst hab; show IsAlgebraic ℚ ((1 : Matrix (Fin m) (Fin m) ℂ) a a); rw [Matrix.one_apply_eq]; exact isAlgebraic_one
  · show IsAlgebraic ℚ ((1 : Matrix (Fin m) (Fin m) ℂ) a b); rw [Matrix.one_apply_ne hab]; exact isAlgebraic_zero

section Avg

variable {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (κ : Measure K) [IsProbabilityMeasure κ] {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Group K] [IsTopologicalGroup K] [DecidableEq ι] in
theorem integral_expand (ρ : K → Matrix ι ι ℂ) (hρ : Continuous ρ) (Φ : ι → ℂ) (F : K → ℂ) (k : ι)
    (hF : ∀ g, F g = ∑ k', ρ g k' k * Φ k') : ∫ g, F g ∂κ = ∑ k', (∫ g, ρ g k' k ∂κ) * Φ k' := by
  simp_rw [hF]
  rw [integral_finsetSum]
  · exact Finset.sum_congr rfl fun k' _ => integral_mul_const _ _
  · exact fun k' _ => (GlobalTheory.HaarAlg.integrable_of_continuous κ (hρ.matrix_elem k' k)).mul_const _

theorem integral_eq_zero_of_scalar [κ.IsMulLeftInvariant] (ρ : K →* Matrix ι ι ℂ) (hρ : Continuous ρ) (z : K) (c : ℂ)
    (hc : c ≠ 1) (hz : ρ z = c • 1) (a b : ι) : ∫ g, ρ g a b ∂κ = 0 := by
  classical
  have h := GlobalTheory.HaarAlg.rho_mul_avg κ ρ hρ z
  rw [hz, Matrix.smul_mul, Matrix.one_mul] at h
  have h3 := congrFun (congrFun h a) b
  simp only [Matrix.smul_apply, smul_eq_mul, GlobalTheory.HaarAlg.avg, Matrix.of_apply] at h3
  have h2 : (c - 1) * ∫ g, ρ g a b ∂κ = 0 := by rw [sub_mul, one_mul, h3, sub_self]
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hc)

end Avg

end GlobalTheory.RealAvg
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.weil_latticeIntertwiner_coefficient_at_place : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (hψ : IsStdChar D ψ (-1)) (lam : ℕ →* ℂ) (w₀ : 𝓞 D.host.E) (Om : GA D S × GA D T →* Module.End ℂ (GlobalTheory.FinWeilO.thetaSub ψ S T)), GlobalTheory.FinWeilO.IsLatRep hψ.1 (frameLat S) (frameLat T) w₀ lam Om → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (a : Gv T v) (f₁ f₂ : GlobalTheory.FinWeilO.thetaSub ψ S T), VacFin ψ S T v f₁ → VacFin ψ S T v f₂ → l2 μ 𝓕 (Om (1, embV T v a) f₁ : WO S T → ℂ) f₂ = (lam (GlobalTheory.FinWeil.idx (GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)) ((GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).map (GlobalTheory.FinWeilO.rhoF S T (1, embV T v a)))))⁻¹ * l2 μ 𝓕 (f₁ : WO S T → ℂ) f₂ := by
  first | exact @GlobalTheory.LatCoef.latCoef | exact GlobalTheory.LatCoef.latCoef | (intros; apply GlobalTheory.LatCoef.latCoef <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.weil_latticeVacuum_stabilizer_splitting_characters : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsSelfDualC S ΛS → IsSelfDualC T ΛT → (∃ η, IsEtaTilde D η) → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), IsFrame βS ΛS → IsFrame βT ΛT → ∀ (P : Finset (Pl D.host.E)) (e : AE D) (he : e * e = e), IsIdemSum e P → UnrOff (e + cA D e) χS → UnrOff (e + cA D e) χT → ∀ g h, Stab S βS g → Stab T βT h → ∀ f, IsThetaFunO ψ S T f → IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f → om (g, h) f = ((splitFacO χS χT (detAt e he S g) (detAt e he T h) : Circle) : ℂ) • f := by
  first | exact @GlobalTheory.VecInv.Vac.stab_vacuum | exact GlobalTheory.VecInv.Vac.stab_vacuum | (intros; apply GlobalTheory.VecInv.Vac.stab_vacuum <;> assumption)
end
