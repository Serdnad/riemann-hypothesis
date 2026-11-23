module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1367
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1967
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1890
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle035
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle331
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle550
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle418
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjEqZeroOfSymplO
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle547
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle475
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
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
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical

namespace GlobalTheory.RealLieFock

theorem lie_deriv_pol : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ τ : ∀ w : InfinitePlace F, EmbOver E w, (∀ w, IsCartan (X.J.map (τ w).1) (X.θ w)) →
        (∀ w, IsCartan (Complex.I • W.J.map (τ w).1) (W.θ w)) →
        ∀ γ ∈ Lines σ W, ∀ f ∈ M.Pol ψ τ,
          (∃ f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁) ∧
          ∀ f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ → f₁ ∈ M.Pol ψ τ := by
  intro F E _ _ _ _ _ σ hcm n d X W M ψ χX χW om hψ hX hXd hW hWd hrX hrW hhX hhW hwe τ hcX hcW γ hγ
  choose T hT' using fun t : ℝ => GlobalTheory.T.exists_archimedeanOperator_weilRep_pureTensor F E σ hcm n d X W M ψ χX χW om hψ hX hXd hW hWd hrX hrW hhX hhW hwe
    (γ (Multiplicative.ofAdd t)) (hγ.2 _)
  have hvac : ∀ f₀, M.IsGauss ψ τ f₀ → f₀ ∈ M.Pol ψ τ := fun f₀ h =>
    Submodule.mem_sInf.2 fun N hN => hN.1 f₀ h
  have hstab : ∀ u, At (evI F) u → ∀ f ∈ M.Pol ψ τ, ∀ f₁ : SInf F (Fin n × Fin d),
      ActsD (evI F) (M.heisLine ψ u) f f₁ → f₁ ∈ M.Pol ψ τ := fun u hu f hf f₁ h =>
    Submodule.mem_sInf.2 fun N hN => hN.2 u hu f (Submodule.mem_sInf.1 hf N hN) f₁ h
  let N : Submodule ℂ (SInf F (Fin n × Fin d)) :=
    { carrier := {f | f ∈ M.Pol ψ τ ∧
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun p : ℝ × (Fin n × Fin d → mixedEmbedding.mixedSpace F) => T p.1 f p.2) ∧
        ∃ f' ∈ M.Pol ψ τ, ∀ x, HasDerivAt (fun t => T t f x) (f' x) 0}
      zero_mem' := ⟨zero_mem _, by simpa using contDiff_const, 0, zero_mem _, fun x => by simpa using hasDerivAt_const _ _⟩
      add_mem' := by
        rintro f g ⟨hf, hf1, f', hf', hf2⟩ ⟨hg, hg1, g', hg', hg2⟩
        refine ⟨add_mem hf hg, by simpa using hf1.add hg1, f' + g', add_mem hf' hg', fun x => ?_⟩
        show HasDerivAt (fun t => T t (f + g) x) ((f' + g') x) 0
        simp only [map_add (f := _), SchwartzMap.add_apply]
        exact (hf2 x).add (hg2 x)
      smul_mem' := by
        rintro c f ⟨hf, hf1, f', hf', hf2⟩
        refine ⟨Submodule.smul_mem _ c hf, by simpa using hf1.const_smul c, c • f', Submodule.smul_mem _ c hf', fun x => ?_⟩
        simpa using (hf2 x).const_mul c }
  have hPN : M.Pol ψ τ ≤ N := by
    refine sInf_le ⟨fun f₀ h => ?_, fun u hu f hf f₁ h => ?_⟩
    · exact ⟨hvac f₀ h, GlobalTheory.T.weilOperator_oneParam_gaussianVacuum_smooth_pair F E σ hcm n d X W M ψ χX χW om hψ hX hXd hW hWd hrX hrW hhX hhW hwe τ hcX hcW γ hγ T hT' f₀ h⟩
    · obtain ⟨hf0, hf1, hf2⟩ := hf
      exact ⟨hstab u hu f hf0 f₁ h,
        GlobalTheory.T.smooth_weilOrbit_real_passes_to_heisenbergDerivatives F E σ hcm n d X W M ψ χX χW om hψ hX hXd hW hWd hrX hrW hhX hhW hwe τ hcX hcW γ hγ T hT' u hu f hf0 hf1 hf2 f₁ h⟩
  intro f hf
  obtain ⟨-, -, f', hf', hd⟩ := hPN hf
  have hA : ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f' := by
    intro r hr x
    have h1 : ∀ t : ℝ, om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) f r) = tens (evI F) (T t f) r :=
      fun t => hT' t f r hr
    simp only [h1]
    exact (hd _).mul_const (r x)
  refine ⟨⟨f', hA⟩, fun f₁ h₁ => ?_⟩
  have e : f₁ = f' := (GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) f f₁ f').2.2.1 _ h₁ hA
  rw [e]; exact hf'

end GlobalTheory.RealLieFock
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

namespace GlobalTheory.SquareAgree


open Classical in
theorem exists_good_model : ∀ (D : D7) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig →
    ∀ {n d : ℕ} (V : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E n) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ),
    V.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
    ∀ (μ : Measure (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig V.J)) (dom : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig V.J)),
      μ.IsHaarMeasure → IsFundamentalDomain (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU D.sp.cm.sig V.J) dom μ →
    ∃ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig V Ws, M.μ = μ ∧ M.dom = dom ∧ M.IsGood Bs.ψ := by
  intro D Bs hB n d V Ws r s r' s' hV hW μ dom hμ hdom
  obtain ⟨co, hco⟩ := GlobalTheory.T.exists_rational_darboux_hermitian_tensor_adeles D.sp.cm.sig Bs V Ws r s r' s' hB hV hW
  let M0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig V Ws := ⟨co, fun _ => 0, μ, dom⟩
  have hb := GlobalTheory.T.exists_latticeVacuum_finitePlaces_rationalDarboux D.sp.cm.sig Bs V Ws r s r' s' hB hV hW M0 hco
  have hc := GlobalTheory.T.eventually_integralPointsIndicator_isVacuum D.sp.cm.sig Bs V Ws r s r' s' hB hV hW M0 hco
  let ind : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), (Fin n × Fin d → Fv D.host.F v) → ℂ := fun v =>
    Set.indicator {x : Fin n × Fin d → Fv D.host.F v | ∀ k, x k ∈ v.adicCompletionIntegers D.host.F} 1
  refine ⟨⟨co, fun v => if M0.IsVac Bs.ψ v (ind v) then ind v else (hb v).choose, μ, dom⟩, rfl, rfl, ?_⟩
  refine ⟨hco, fun v => ?_, ?_, hμ, hdom⟩
  · change M0.IsVac Bs.ψ v (if M0.IsVac Bs.ψ v (ind v) then ind v else (hb v).choose)
    split_ifs with h
    · exact h
    · exact (hb v).choose_spec
  · filter_upwards [hc] with v hv
    change (if M0.IsVac Bs.ψ v (ind v) then ind v else (hb v).choose) = ind v
    exact if_pos hv

end GlobalTheory.SquareAgree
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.exists_lieDerivative_polynomialFock_seesaw : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ γ ∈ Lines σ G.W,
    ∃ δ : SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a × Fin (a + a')), ∀ f ∈ G.M.Pol B.ψ B.emb,
      δ f ∈ G.M.Pol B.ψ B.emb ∧ ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f (δ f) := by
  first | exact @GlobalTheory.OscLie.exists_lie_deriv_pol | exact GlobalTheory.OscLie.exists_lie_deriv_pol | (intros; apply GlobalTheory.OscLie.exists_lie_deriv_pol <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MixedSeriesGrowth

theorem mixed_series_growth : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∃ A : ℕ, ∀ f, IsThetaFunO ψ V W f → ∃ c : ℝ, ∀ (g : GA D V) (h : GA D W), (∀ y : Matrix (Fin W.rank) (Fin r) D.host.E, Continuous fun p : GA D V × GA D W => res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) (ω p f)) 0) ∧ ∑' y : Matrix (Fin W.rank) (Fin r) D.host.E, ‖res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) (ω (g, h) f)) 0‖ₑ ≤ ENNReal.ofReal (c * (GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h) ^ A) := by
  intro D V V' W r C C' B hs h1 h2 h3 ψ χS χT ω hω μ 𝓨 hμ
  obtain ⟨⟨θ, hθ⟩, -, -⟩ := GlobalTheory.Ker.exists_infFam_and_stdChar D
  obtain ⟨A₁, d, hF⟩ := GlobalTheory.T.mixedModelThetaTerms_summable_heightBound D V V' W r C C' B hs h1 h2 h3 ψ hω.std θ hθ μ 𝓨 hμ
  obtain ⟨A₂, hS⟩ := GlobalTheory.T.heisenbergWords_weilOperator_supNorm_polynomialGrowth D ψ V W χS χT ω hω θ hθ d
  refine ⟨A₁ + A₂, fun f hf => ?_⟩
  obtain ⟨U, hU, hl⟩ := hf.level
  obtain ⟨K, hK⟩ := hF U hU
  obtain ⟨c, hc⟩ := hS f hf
  refine ⟨max K 0 * max c 0, fun g h => ⟨fun y => GlobalTheory.T.continuous_restrictedHeisenbergWeilTranslate_at_zero D V V' W r C B hs ψ χS χT ω hω μ 𝓨 hμ f hf _, ?_⟩⟩
  have hH : 0 ≤ GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h :=
    mul_nonneg (GlobalTheory.Grow.height_pos V g).le (GlobalTheory.Grow.height_pos W h).le
  refine (hK g h (ω (g, h) f) (hω.om_pres _ f hf) (fun u hu h0 => ?_)).trans ?_
  · rw [← hω.om_heis g h u f hf, hl u hu h0]
  · refine (mul_le_mul' (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left K 0) (pow_nonneg hH _)))
      ((hc g h).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left c 0)
        (pow_nonneg hH _))))).trans_eq ?_
    rw [← ENNReal.ofReal_mul (mul_nonneg (le_max_right K 0) (pow_nonneg hH _)), pow_add]
    congr 1; ring

end GlobalTheory.MixedSeriesGrowth

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SourceUnip

open GlobalTheory.MixModel GlobalTheory.UnipMean

variable {D : D7} {V V' W : HSp D} {r : ℕ}

theorem corner_alg {R a b c : Type} [CommRing R] [Fintype b] [Fintype c] {x1 : Matrix a b R} {m p q : Matrix b b R}
    {C' : Matrix b c R} {B : Matrix c b R} (hq : q = C' * B) (hp : x1 * p = 0)
    (r3 : m = p * m + m * q - p * m * q) : x1 * m = x1 * m * C' * B := by
  have a1 : x1 * (p * m) = 0 := by rw [← Matrix.mul_assoc, hp, Matrix.zero_mul]
  have a2 : x1 * (p * m * q) = 0 := by rw [← Matrix.mul_assoc, a1, Matrix.zero_mul]
  calc x1 * m = x1 * (p * m + m * q - p * m * q) := by rw [← r3]
    _ = x1 * (p * m) + x1 * (m * q) - x1 * (p * m * q) := by rw [Matrix.mul_sub, Matrix.mul_add]
    _ = x1 * m * C' * B := by rw [a1, a2, zero_add, sub_zero, hq]; simp only [Matrix.mul_assoc]

theorem hO_iso (C : Matrix (Fin V.rank) (Fin r) D.host.E) (x : WO V W) (y : Mx D W.rank r) :
    hO V W x (y ⬝ rat (Cᴴ * V.gram)) = (adj y ⬝ (gA W ⬝ (x ⬝ rat C))).trace := by
  rw [hO_eq_trace, rat_mul, rat_conjTranspose, adj_mul, adj_mul, adj_adj, ← gA, adj_gA]
  simp only [Matrix.mul_assoc, giA_gA_cancel]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem symplO_iso_of (C : Matrix (Fin V.rank) (Fin r) D.host.E) {x : WO V W} (hx : x ⬝ rat C = 0)
    (y : Mx D W.rank r) : symplO V W x (y ⬝ rat (Cᴴ * V.gram)) = 0 := by
  rw [symplO_eq, hO_iso, hx, Matrix.mul_zero, Matrix.mul_zero, Matrix.trace_zero, mul_zero, map_zero]

theorem mulC_eq_zero_of_symplO (C : Matrix (Fin V.rank) (Fin r) D.host.E) {x : WO V W}
    (h : ∀ y : Mx D W.rank r, symplO V W x (y ⬝ rat (Cᴴ * V.gram)) = 0) : x ⬝ rat C = 0 := by
  obtain ⟨u, hu⟩ : ∃ u : Mx D W.rank r, u = gA W ⬝ (x ⬝ rat C) := ⟨_, rfl⟩
  have hu0 : u = 0 := by
    ext i j
    have key : ∀ w : AE D, Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * u i j * w) = 0 := fun w => by
      have := h (adj (Matrix.single j i w : Mx D r W.rank))
      rw [symplO_eq, hO_iso, adj_adj, ← hu, trace_single_mul', ← mul_assoc] at this
      exact this
    have hz := eq_zero_of_trace_mul (F := D.host.F) (E := D.host.E) (R := AF D.host.F) _ key
    have hξ : incA D D.host.xi0⁻¹ * incA D D.host.xi0 = 1 := by
      rw [← map_mul, inv_mul_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), map_one]
    have := congrArg (incA D D.host.xi0⁻¹ * ·) hz
    simpa [← mul_assoc, hξ] using this
  have e : giA W ⬝ u = giA W ⬝ (gA W ⬝ (x ⬝ rat C)) := by rw [hu]
  rw [giA_gA_cancel, hu0, Matrix.mul_zero] at e
  exact e.symm

theorem iso_mulC {C : Matrix (Fin V.rank) (Fin r) D.host.E} (hC : IsIsoFrame V C) (y : Mx D W.rank r) :
    y ⬝ rat (Cᴴ * V.gram) ⬝ rat C = 0 := by
  have h : Cᴴ * V.gram * C = 0 := hC.2.2
  rw [Matrix.mul_assoc, ← rat_mul, h, rat_zero, Matrix.mul_zero]

theorem mid_mulC {C : Matrix (Fin V.rank) (Fin r) D.host.E} {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E}
    (hs : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B) (x : WO V' W) :
    x ⬝ rat (V'.gram⁻¹ * Bᴴ * V.gram) ⬝ rat C = 0 := by
  have h0 : Cᴴ * V.gram * B = 0 := hs.orth
  have h1 : Bᴴ * (V.gram * C) = 0 := by
    have := congrArg Matrix.conjTranspose h0
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, gram_conjTranspose,
      Matrix.conjTranspose_zero] at this
  rw [Matrix.mul_assoc, ← rat_mul]
  simp only [Matrix.mul_assoc, h1, Matrix.mul_zero, rat_zero]

section Gen

variable {C : Matrix (Fin V.rank) (Fin r) D.host.E} {C' : Matrix (Fin V.rank) (Fin r) D.host.E}
  {L B₀ : Matrix (Fin r) (Fin V.rank) D.host.E}

theorem gen_fix_iso (h : IsDualPair V C C' L B₀) {g : GA D V} (g2 : rat B₀ ⬝ (mt V g - 1) = 0)
    (y : Mx D W.rank r) : actO V W g 1 (y ⬝ rat (Cᴴ * V.gram)) = y ⬝ rat (Cᴴ * V.gram) := by
  have e1 : rat B₀ ⬝ mt V g = rat B₀ := by
    rwa [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at g2
  have e2 : rat B₀ ⬝ mt V g⁻¹ = rat B₀ := by
    rw [← e1, Matrix.mul_assoc, mt_mul_inv, Matrix.mul_one, e1]
  rw [actO_eq, mt_one, Matrix.one_mul, ← h.hB, Matrix.mul_assoc, e2]

theorem gen_move (h : IsDualPair V C C' L B₀) {g : GA D V} (g1 : (mt V g - 1) ⬝ rat C = 0)
    (r3 : mt V g - 1 = rat (C * L) * (mt V g - 1) + (mt V g - 1) * rat (C' * B₀) -
      rat (C * L) * (mt V g - 1) * rat (C' * B₀))
    {x : WO V W} (hx : x ⬝ rat C = 0) :
    ∃ y : Mx D W.rank r, actO V W g 1 x = x + y ⬝ rat (Cᴴ * V.gram) := by
  have e1 : mt V g ⬝ rat C = rat C := by
    rwa [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at g1
  have e2 : mt V g⁻¹ ⬝ rat C = rat C := by
    rw [← e1, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul, e1]
  obtain ⟨x1, hx1⟩ : ∃ x1 : WO V W, x1 = x ⬝ mt V g⁻¹ := ⟨_, rfl⟩
  have hx1C : x1 ⬝ rat C = 0 := by rw [hx1, Matrix.mul_assoc, e2, hx]
  have hx1p : x1 ⬝ rat (C * L) = 0 := by rw [rat_mul, ← Matrix.mul_assoc, hx1C, Matrix.zero_mul]
  have hx1g : x1 ⬝ mt V g = x := by rw [hx1, Matrix.mul_assoc, mt_inv_mul, Matrix.mul_one]
  have k : x1 ⬝ (mt V g - 1) = x1 ⬝ (mt V g - 1) ⬝ rat C' ⬝ rat B₀ :=
    corner_alg (rat_mul C' B₀) hx1p r3
  refine ⟨-(x1 ⬝ (mt V g - 1) ⬝ rat C'), ?_⟩
  rw [actO_eq, mt_one, Matrix.one_mul, ← h.hB, Matrix.neg_mul, ← k, Matrix.mul_sub, hx1g, Matrix.mul_one, ← hx1]
  abel

end Gen

section Main

variable {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle}
  {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)}

theorem weilRepresentation_source_mul (g g' : GA D V) (f : WO V W → ℂ) : ω (g * g', 1) f = ω (g, 1) (ω (g', 1) f) := by
  have : (g * g', (1 : GA D W)) = (g, 1) * (g', 1) := by simp
  rw [this, map_mul]; rfl

theorem weilRepresentation_source_one (f : WO V W → ℂ) : ω (1, 1) f = f := by
  have : ((1 : GA D V), (1 : GA D W)) = 1 := rfl
  rw [this, map_one]; rfl

theorem unit_product_rescale_disjoint_finsets {C : Matrix (Fin V.rank) (Fin r) D.host.E} {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E}
    (hs : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B) (hω : IsWeilDatumO ψ V W χS χT ω)
    {μ : Measure (Mx D W.rank r)} {𝓨 : Set (Mx D W.rank r)}
    (hcov : IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨) {g : GA D V} (hg : g ∈ NI V C) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ f, IsThetaFunO ψ V W f →
      GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (ω (g, 1) f) = c • GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f := by
  have hC := hs.frame
  obtain ⟨C', L, B₀, h⟩ := exists_dualPair hC
  have hP : (1 : Matrix (Fin W.rank) (Fin W.rank) D.host.E).rank = W.rank := by
    rw [Matrix.rank_one, Fintype.card_fin]
  have hQ : (Cᴴ * V.gram).rank = r := by
    refine le_antisymm ?_ ?_
    · simpa using Matrix.rank_le_card_height (Cᴴ * V.gram)
    · have := Matrix.rank_mul_le_left (Cᴴ * V.gram) C'
      rw [← h.hB] at this ⊢
      rwa [h.BC', Matrix.rank_one, Fintype.card_fin] at this
  have eI : ∀ y : Mx D W.rank r, (HMul.hMul (HMul.hMul ((1 : Matrix (Fin W.rank) (Fin W.rank) D.host.E).map (incA D))
      (y : Matrix (Fin W.rank) (Fin r) (AE D))) ((Cᴴ * V.gram).map (incA D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D)) =
      y ⬝ rat (Cᴴ * V.gram) := fun y => by
    show rat (1 : Matrix (Fin W.rank) (Fin W.rank) D.host.E) ⬝ y ⬝ rat (Cᴴ * V.gram) = _
    rw [rat_one, Matrix.one_mul]
  unfold NI at hg
  refine Subgroup.closure_induction (p := fun g _ => ∃ c : ℂ, c ≠ 0 ∧ ∀ f, IsThetaFunO ψ V W f →
      GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (ω (g, 1) f) = c • GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f) ?_ ?_ ?_ ?_ hg
  · rintro g ⟨g1, g2, g3⟩
    have g1' : (mt V g - 1) ⬝ rat C = 0 := g1
    obtain ⟨r1, r2, r3⟩ := gen_relations h (x := mt V g - 1) g1' (by rw [h.hB]; exact g2)
      (fun v hv => g3 v (by rw [← h.hB']; exact hv))
    have g2' : rat B₀ ⬝ (mt V g - 1) = 0 := by rw [h.hB]; exact g2
    obtain ⟨c, hc⟩ := GlobalTheory.T.isotropicMean_changes_by_scalar_of_trivial_action D V W W.rank r 1 (Cᴴ * V.gram) hP hQ
      (fun y y' => by rw [eI, eI]; exact symplO_iso_of C (iso_mulC hC y) y') ψ χS χT ω hω μ 𝓨 hcov g 1
      (fun y => by rw [eI]; exact gen_fix_iso h g2' y)
      (fun x hx => by
        obtain ⟨y, hy⟩ := gen_move h g1' r3 (mulC_eq_zero_of_symplO C fun y => by rw [← eI]; exact hx y)
        exact ⟨y, by rw [eI]; exact hy⟩)
    refine ⟨c, Circle.coe_ne_zero c, fun f hf => ?_⟩
    funext x'
    have hm := mid_mulC hs (W := W) x'
    have hh : ∀ (F : WO V W → ℂ) (y : Mx D W.rank r),
        heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W B x') F
          (HMul.hMul (HMul.hMul ((1 : Matrix (Fin W.rank) (Fin W.rank) D.host.E).map (incA D))
            (y : Matrix (Fin W.rank) (Fin r) (AE D))) ((Cᴴ * V.gram).map (incA D)) :
            Matrix (Fin W.rank) (Fin V.rank) (AE D)) =
          F (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W B x') := fun F y => by
      rw [eI]
      show ψ (symplOH V W _ _) * F _ = _
      have h0 : symplO V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W B x') (y ⬝ rat (Cᴴ * V.gram)) = 0 := symplO_iso_of C hm y
      rw [symplOH_skew]
      unfold symplOH
      rw [h0, mul_zero, neg_zero, AddChar.map_zero_eq_one, one_mul]
      rfl
    have := hc f hf (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W B x') (fun y => by rw [eI]; exact symplO_iso_of C hm y)
    simp only [hh] at this
    show ∫ y in 𝓨, ω (g, 1) f _ ∂μ = (c : ℂ) • ∫ y in 𝓨, f _ ∂μ
    rw [this, smul_eq_mul]
  · exact ⟨1, one_ne_zero, fun f _ => by rw [weilRepresentation_source_one, one_smul]⟩
  · rintro a b - - ⟨c, hc, ha⟩ ⟨d, hd, hb⟩
    exact ⟨c * d, mul_ne_zero hc hd, fun f hf => by
      rw [weilRepresentation_source_mul, ha _ (hω.om_pres _ _ hf), hb f hf, smul_smul]⟩
  · rintro a - ⟨c, hc, ha⟩
    refine ⟨c⁻¹, inv_ne_zero hc, fun f hf => ?_⟩
    have := ha _ (hω.om_pres (a⁻¹, 1) f hf)
    rw [← weilRepresentation_source_mul, mul_inv_cancel, weilRepresentation_source_one] at this
    rw [this, smul_smul, inv_mul_cancel₀ hc, one_smul]

end Main

end GlobalTheory.SourceUnip

open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

theorem GlobalTheory.SourceUnip.scal : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ g : GA D V, g ∈ NI V C → ∃ c : ℂ, ∀ f, IsThetaFunO ψ V W f → res V V' W C B μ 𝓨 (ω (g, 1) f) = c • res V V' W C B μ 𝓨 f := by
  intro D V V' W r C B hs ψ χS χT ω hω μ 𝓨 hcov g hg
  obtain ⟨c, -, hc⟩ := GlobalTheory.SourceUnip.unit_product_rescale_disjoint_finsets hs hω hcov hg
  exact ⟨c, hc⟩

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnipMean

theorem heisO_zero {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (f : WO V W → ℂ) : heisO ψ V W 0 f = f := by
  funext x
  unfold heisO symplOH symplO hO
  simp

theorem symplO_zero_left {D : D7} (V W : HSp D) (z : WO V W) : symplO V W 0 z = 0 := by
  unfold symplO hO
  simp

theorem mean_target : ∀ (D : D7) (V W : HSp D) (s : ℕ) (L : Matrix (Fin W.rank) (Fin s) D.host.E), IsIsoFrame W L → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D s V.rank)) (𝓐 : Set (Mx D s V.rank)), IsCovolOne (ratMx D s V.rank) μ 𝓐 → ∀ (n : NI W L) (f : WO V W → ℂ), IsThetaFunO ψ V W f → ∫ a in 𝓐, ω (1, (n : GA D W)) f (HMul.hMul (L.map (incA D)) (a : Matrix (Fin s) (Fin V.rank) (AE D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D)) ∂μ = ∫ a in 𝓐, f (HMul.hMul (L.map (incA D)) (a : Matrix (Fin s) (Fin V.rank) (AE D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D)) ∂μ := by
  intro D V W s L hL ψ χS χT ω hω μ 𝓐 hcov n f hf
  have hiso := iso_rat hL
  have e1 : (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (incA D) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have hm1 : Formalism.L2.Theta.mt V 1 = 1 := by
    unfold Formalism.L2.Theta.mt
    simp
  have hact : ∀ (g : GA D W) (x : WO V W), actO V W 1 g x = HMul.hMul (Formalism.L2.Theta.mt W g) x := by
    intro g x
    unfold actO
    rw [inv_one, hm1, Matrix.mul_one]
  have hrk : L.rank = s := by
    rw [← Matrix.finrank_span_range_col]
    exact (finrank_span_eq_card hL.2.1).trans (Fintype.card_fin s)
  have hsym : ∀ y y' : Mx D s V.rank, symplO V W (HMul.hMul (HMul.hMul (L.map (incA D)) y) ((1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (incA D))) (HMul.hMul (HMul.hMul (L.map (incA D)) y') ((1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (incA D))) = 0 := by
    intro y y'
    rw [e1, Matrix.mul_one, Matrix.mul_one]
    exact symplO_frame hiso y y'
  have hsc : ∀ g : GA D W,
      (∀ y : Mx D s V.rank, HMul.hMul (mt W g) (HMul.hMul (GlobalTheory.MixModel.rat L) y) = HMul.hMul (GlobalTheory.MixModel.rat L) y) →
      (∀ x : WO V W, HMul.hMul (GlobalTheory.MixModel.adj (GlobalTheory.MixModel.rat L)) (HMul.hMul (GlobalTheory.MixModel.gA W) x) = 0 →
        ∃ y : Mx D s V.rank, HMul.hMul (mt W g) x = x + HMul.hMul (GlobalTheory.MixModel.rat L) y) →
      ∃ c : ℂ, c ≠ 0 ∧ Sc ψ ω (GlobalTheory.MixModel.rat L) μ 𝓐 g c := by
    intro g hg1 hg2
    have hfix : ∀ y : Mx D s V.rank, actO V W 1 g (HMul.hMul (HMul.hMul (L.map (incA D)) y) ((1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (incA D))) = HMul.hMul (HMul.hMul (L.map (incA D)) y) ((1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (incA D)) := by
      intro y
      rw [e1, Matrix.mul_one, hact]
      exact hg1 y
    have hmov : ∀ x : WO V W, (∀ y : Mx D s V.rank, symplO V W x (HMul.hMul (HMul.hMul (L.map (incA D)) y) ((1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (incA D))) = 0) → ∃ y : Mx D s V.rank, actO V W 1 g x = x + HMul.hMul (HMul.hMul (L.map (incA D)) y) ((1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (incA D)) := by
      intro x hx
      rw [e1] at hx
      simp only [Matrix.mul_one] at hx
      obtain ⟨y, hy⟩ := hg2 x (adj_eq_zero_of_symplO (C := GlobalTheory.MixModel.rat L) hx)
      refine ⟨y, ?_⟩
      rw [e1, Matrix.mul_one, hact]
      exact hy
    obtain ⟨c, hc⟩ := GlobalTheory.T.isotropicMean_changes_by_scalar_of_trivial_action D V W s V.rank L 1 hrk (Matrix.rank_one.trans (Fintype.card_fin _)) hsym ψ χS χT ω hω μ 𝓐 hcov 1 g hfix hmov
    refine ⟨c, Circle.coe_ne_zero c, ?_⟩
    intro f' hf'
    have h0 := hc f' hf' 0 (fun y => symplO_zero_left V W _)
    simp only [heisO_zero, e1, Matrix.mul_one] at h0
    exact h0
  have key := mean_unip hL hω hcov hsc n.2 f hf
  unfold meanL at key
  rw [one_mul] at key
  exact key

end GlobalTheory.UnipMean

end
end
