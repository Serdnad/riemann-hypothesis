module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EqNegOfCommute
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle035
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle039
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle042
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle077
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittHyperbolicAnisotropicCommuteLevi
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle196
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealIntertwinerContractionOnePlace
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

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField
open scoped ENNReal

namespace GlobalTheory.Size

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.OrientedHeis GlobalTheory.FockCompare GlobalTheory.Ker.HeisDeriv

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D}
  {μ : Measure (WO V W)} {𝓕 : Set (WO V W)} {f : WO V W → ℂ}

theorem dRho_dir_linear (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (hf : IsThetaFunO ψ V W f) (τ : D.what₂.Tau) :
    (∀ z z' : Matrix (Fin W.rank) (Fin V.rank) ℂ, Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ (z + z') f =
      Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z f + Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z' f) ∧
    ∀ (t : ℝ) (z : Matrix (Fin W.rank) (Fin V.rank) ℂ), Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ ((t : ℂ) • z) f =
      (t : ℂ) • Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z f := by
  classical
  obtain ⟨σ, hσ⟩ := GlobalTheory.FockCompare.exists_chart hθ
  have hsm := GlobalTheory.OrientedHeis.theta_sm hσ hf
  have key : ∀ y : Matrix (Fin W.rank) (Fin V.rank) ℂ, Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ y f =
      GlobalTheory.FockCompare.hD (GlobalTheory.FockCompare.iotaW σ W V) (GlobalTheory.FockCompare.piW θ W V) (GlobalTheory.OrientedHeis.omO V W)
        (GlobalTheory.FockCompare.piW θ W V (lineAt θ τ y 1)) f := fun y => by
    rw [GlobalTheory.OrientedHeis.dRho_eq_dLine, GlobalTheory.OrientedHeis.dLine_eq_hD hσ hψ (GlobalTheory.OrientedHeis.isRealDir_lineAt hθ τ y)]
  have hlin_add : ∀ u u' : GlobalTheory.FockCompare.RW W V,
      GlobalTheory.FockCompare.hD (GlobalTheory.FockCompare.iotaW σ W V) (GlobalTheory.FockCompare.piW θ W V) (GlobalTheory.OrientedHeis.omO V W) (u + u') f =
        GlobalTheory.FockCompare.hD (GlobalTheory.FockCompare.iotaW σ W V) (GlobalTheory.FockCompare.piW θ W V) (GlobalTheory.OrientedHeis.omO V W) u f +
        GlobalTheory.FockCompare.hD (GlobalTheory.FockCompare.iotaW σ W V) (GlobalTheory.FockCompare.piW θ W V) (GlobalTheory.OrientedHeis.omO V W) u' f := by
    intro u u'
    funext w
    simp only [Pi.add_apply, GlobalTheory.FockCompare.hD_eq_fderiv _ _ _ f hsm, map_add (f := _)]
    push_cast
    ring
  have hlin_smul : ∀ (t : ℝ) (u : GlobalTheory.FockCompare.RW W V),
      GlobalTheory.FockCompare.hD (GlobalTheory.FockCompare.iotaW σ W V) (GlobalTheory.FockCompare.piW θ W V) (GlobalTheory.OrientedHeis.omO V W) (t • u) f =
        (t : ℂ) • GlobalTheory.FockCompare.hD (GlobalTheory.FockCompare.iotaW σ W V) (GlobalTheory.FockCompare.piW θ W V)
          (GlobalTheory.OrientedHeis.omO V W) u f := by
    intro t u
    funext w
    simp only [Pi.smul_apply, smul_eq_mul, GlobalTheory.FockCompare.hD_eq_fderiv _ _ _ f hsm, map_smul, Complex.real_smul]
    push_cast
    ring
  have hadd_u : ∀ y y' : Matrix (Fin W.rank) (Fin V.rank) ℂ, GlobalTheory.FockCompare.piW θ W V (lineAt θ τ (y + y') 1) =
      GlobalTheory.FockCompare.piW θ W V (lineAt θ τ y 1) + GlobalTheory.FockCompare.piW θ W V (lineAt θ τ y' 1) := by
    intro y y'
    rw [GlobalTheory.Ker.HeisDeriv.pi_lineAt hθ, GlobalTheory.Ker.HeisDeriv.pi_lineAt hθ, GlobalTheory.Ker.HeisDeriv.pi_lineAt hθ]
    exact Pi.single_add (f := fun _ => Matrix (Fin W.rank) (Fin V.rank) ℂ) τ y y'
  have hsmul_u : ∀ (t : ℝ) (y : Matrix (Fin W.rank) (Fin V.rank) ℂ),
      GlobalTheory.FockCompare.piW θ W V (lineAt θ τ ((t : ℂ) • y) 1) = t • GlobalTheory.FockCompare.piW θ W V (lineAt θ τ y 1) := by
    intro t y
    rw [GlobalTheory.Ker.HeisDeriv.pi_lineAt hθ, GlobalTheory.Ker.HeisDeriv.pi_lineAt hθ]
    have e : ((t : ℂ) • y) = t • y := by
      ext a b
      simp [Complex.real_smul]
    rw [e]
    exact Pi.single_smul' τ t y
  refine ⟨fun y y' => ?_, fun t y => ?_⟩
  · rw [key, key, key, hadd_u, hlin_add]
  · rw [key, key, hsmul_u, hlin_smul]

theorem matrix_eq_sum_re_im {m n : ℕ} (z : Matrix (Fin m) (Fin n) ℂ) :
    z = ∑ i, ∑ j, ((((z i j).re : ℝ) : ℂ) • Matrix.single i j (1 : ℂ) +
      (((z i j).im : ℝ) : ℂ) • Matrix.single i j Complex.I) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single z]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.smul_single, Matrix.smul_single, ← Matrix.single_add, smul_eq_mul, smul_eq_mul, mul_one,
    Complex.re_add_im]

theorem dRho_eq_sum_heisDer (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (hf : IsThetaFunO ψ V W f) (τ : D.what₂.Tau)
    (z : Matrix (Fin W.rank) (Fin V.rank) ℂ) :
    Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z f =
      ∑ i, ∑ j, ((((z i j).re : ℝ) : ℂ) • heisDer ψ θ (τ, i, j, false) f +
        (((z i j).im : ℝ) : ℂ) • heisDer ψ θ (τ, i, j, true) f) := by
  obtain ⟨hadd, hsm⟩ := dRho_dir_linear hψ hθ hf τ
  let L : Matrix (Fin W.rank) (Fin V.rank) ℂ →+ (WO V W → ℂ) :=
    AddMonoidHom.mk' (fun y => Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ y f) hadd
  have hL : ∀ y, Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ y f = L y := fun _ => rfl
  rw [hL]
  conv_lhs => rw [matrix_eq_sum_re_im z]

  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_

  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_add (f := _), ← hL, ← hL, hsm, hsm]
  simp [heisDer]

theorem theta_finsetSum {ι : Type} (s : Finset ι) {g : ι → WO V W → ℂ} (hg : ∀ i ∈ s, IsThetaFunO ψ V W (g i)) :
    IsThetaFunO ψ V W (∑ i ∈ s, g i) := by
  classical
  revert hg
  refine Finset.induction_on s (fun _ => by rw [Finset.sum_empty]; exact theta_zero) ?_
  intro a t ha ih hg
  rw [Finset.sum_insert ha]
  exact theta_add (hg a (Finset.mem_insert_self a t)) (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))

theorem sobO_sum_le (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {ι : Type} (s : Finset ι) {g : ι → WO V W → ℂ}
    (hg : ∀ i ∈ s, IsThetaFunO ψ V W (g i)) (d : ℕ) :
    sobO ψ θ μ 𝓕 d (∑ i ∈ s, g i) ≤ ∑ i ∈ s, sobO ψ θ μ 𝓕 d (g i) := by
  classical
  revert hg
  refine Finset.induction_on s (fun _ => ?_) ?_
  · have h0 := sobO_smul (ψ := ψ) (θ := θ) (μ := μ) (𝓕 := 𝓕) (f := (0 : WO V W → ℂ)) d 0
    simp only [smul_zero, enorm_zero, zero_mul] at h0
    simp [h0]
  · intro a t ha ih hg
    have ha' : IsThetaFunO ψ V W (g a) := hg a (Finset.mem_insert_self a t)
    have ht : ∀ i ∈ t, IsThetaFunO ψ V W (g i) := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (sobO_add_le hψ hθ ha' (theta_finsetSum t ht) d).trans (add_le_add le_rfl (ih ht))

theorem sobO_dRho_le (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (hf : IsThetaFunO ψ V W f) (τ : D.what₂.Tau)
    (z : Matrix (Fin W.rank) (Fin V.rank) ℂ) (d : ℕ) :
    sobO ψ θ μ 𝓕 d (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z f) ≤
      ENNReal.ofReal (∑ i, ∑ j, (|(z i j).re| + |(z i j).im|)) * sobO ψ θ μ 𝓕 (d + 1) f := by
  classical
  have hD : ∀ a, IsThetaFunO ψ V W (heisDer ψ θ a f) := fun a => by
    simpa [wordAct] using theta_word hψ hθ [a] hf
  have hT : ∀ i j, IsThetaFunO ψ V W ((((z i j).re : ℝ) : ℂ) • heisDer ψ θ (τ, i, j, false) f +
      (((z i j).im : ℝ) : ℂ) • heisDer ψ θ (τ, i, j, true) f) := fun i j =>
    theta_add (theta_smul _ (hD _)) (theta_smul _ (hD _))
  have hre : ∀ r : ℝ, ‖(r : ℂ)‖ₑ = ENNReal.ofReal |r| := fun r => by
    rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_eq_abs]
  rw [dRho_eq_sum_heisDer hψ hθ hf τ z]
  refine (sobO_sum_le hψ hθ Finset.univ (fun i _ => theta_finsetSum Finset.univ fun j _ => hT i j) d).trans ?_
  calc _ ≤ ∑ i, ∑ j, (ENNReal.ofReal |(z i j).re| + ENNReal.ofReal |(z i j).im|) *
        sobO ψ θ μ 𝓕 (d + 1) f := by
        refine Finset.sum_le_sum fun i _ => ?_
        refine (sobO_sum_le hψ hθ Finset.univ (fun j _ => hT i j) d).trans (Finset.sum_le_sum fun j _ => ?_)
        refine (sobO_add_le hψ hθ (theta_smul _ (hD _)) (theta_smul _ (hD _)) d).trans ?_
        rw [sobO_smul, sobO_smul, hre, hre, add_mul]
        gcongr <;> exact sobO_heisDer_le d _
    _ = _ := by
        simp_rw [← Finset.sum_mul]
        congr 1
        rw [ENNReal.ofReal_sum_of_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [ENNReal.ofReal_sum_of_nonneg fun j _ => by positivity]
        exact Finset.sum_congr rfl fun j _ => (ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)).symm

end GlobalTheory.Size

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.Grow GlobalTheory.Mem.AutSpace GlobalTheory.Mem.RealTranslate GlobalTheory.PointAtPlaceHom

namespace GlobalTheory.Size

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {θ : InfFam D} {V : HSp D}

theorem adAt_mem_lieAt (hθ : IsInfFam θ) (k : GA D V) {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) : adAt θ k τ X ∈ lieAt V τ := by

  have hU : Matrix.conjTranspose (infMat D.sp.cm.sig V.gram (θ τ) k) * gramAt D V τ *
      infMat D.sp.cm.sig V.gram (θ τ) k = gramAt D V τ :=
    GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V k τ
  exact skew_conj hU (GlobalTheory.Mem.AutSpace.infMat_mul_inv (θ := θ) (V := V) (τ := τ) (g := k)) hX

private theorem infMat_eq_one_of_mem_GfC {f : GA D V} (hf : f ∈ GfC V) (τ : D.what₂.Tau) :
    infMat D.sp.cm.sig V.gram (θ τ) f = 1 := by

  have h1 : infHom V f = 1 := hf
  have h2 := congrArg (fun u => (u.val).map (θ τ)) h1
  simp only [Units.val_one] at h2
  rw [Matrix.map_one (θ τ) (map_zero (θ τ)) (map_one (θ τ))] at h2
  exact h2

private theorem adAt_mul_of_mem_GfC (a : GA D V) {f : GA D V} (hf : f ∈ GfC V) (τ : D.what₂.Tau)
    (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) : adAt θ (a * f) τ X = adAt θ a τ X := by

  unfold adAt
  rw [mul_inv_rev, GlobalTheory.PointAtPlaceHom.infMat_mul, GlobalTheory.PointAtPlaceHom.infMat_mul, infMat_eq_one_of_mem_GfC hf τ,
    infMat_eq_one_of_mem_GfC (inv_mem hf) τ, one_mul, mul_one]

theorem oneP_mul_adelic (hθ : IsInfFam θ) (k : GA D V) {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) (t : ℝ) : oneP θ V τ X t * k = k * oneP θ V τ (adAt θ k τ X) t := by

  obtain ⟨a, ha, f, hf, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D V).1 k
  have hreal : IsRealPt θ a := ⟨ha, fun σ => GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V a σ⟩
  have hinf : oneP θ V τ (adAt θ a τ X) t ∈ GinfC V := atTau_mem V τ _
  rw [adAt_mul_of_mem_GfC a hf, ← mul_assoc, oneP_mul hθ hreal hX t, mul_assoc, mul_assoc,
    comm_of_mem V hinf hf]

theorem Rder_rTr_adelic (hθ : IsInfFam θ) (k : GA D V) {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) (φ : GA D V → ℂ) :
    Rder θ V τ X (rTr V k φ) = rTr V k (Rder θ V τ (adAt θ k τ X) φ) := by

  funext g
  show deriv (fun t : ℝ => φ (g * oneP θ V τ X t * k)) 0 = deriv (fun t : ℝ => φ (g * k * oneP θ V τ (adAt θ k τ X) t)) 0
  congr 1
  funext t
  rw [mul_assoc, oneP_mul_adelic hθ k hX t, ← mul_assoc]

theorem rWord_rTr_adelic (hθ : IsInfFam θ) (k : GA D V) (φ : GA D V → ℂ)
    {l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)} (hl : IsLieWord V l) :
    rWord θ V l (rTr V k φ) = rTr V k (rWord θ V (l.map fun p => (p.1, adAt θ k p.1 p.2)) φ) := by

  induction l with
  | nil => simp only [rWord, wordAct, List.foldr_nil, List.map_nil]
  | cons p l ih =>
    have hp : p.2 ∈ lieAt V p.1 := hl p List.mem_cons_self
    have hl' : IsLieWord V l := fun q hq => hl q (List.mem_cons_of_mem _ hq)
    have ih' := ih hl'
    simp only [rWord, wordAct, List.foldr_cons, List.map_cons] at ih' ⊢
    rw [ih', Rder_rTr_adelic hθ k hp]

theorem rTr_mem_smFun (hθ : IsInfFam θ) (k : GA D V) {φ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) :
    rTr V k φ ∈ SmFun θ V := by

  intro n τs Xs hXs g
  have key := hφ n τs (fun i => adAt θ k (τs i) (Xs i)) (fun i => adAt_mem_lieAt hθ k (hXs i)) (g * k)
  convert key using 1
  funext t
  show φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod * k) =
    φ (g * k * (List.ofFn fun i => oneP θ V (τs i) (adAt θ k (τs i) (Xs i)) (t i)).prod)
  rw [mul_assoc, prod_mul_eq k n (fun i => oneP θ V (τs i) (Xs i) (t i))
    (fun i => oneP θ V (τs i) (adAt θ k (τs i) (Xs i)) (t i)) (fun i => oneP_mul_adelic hθ k (hXs i) (t i)),
    ← mul_assoc]

private theorem rapidDecSm_rTr_of_mem_GinfC (hθ : IsInfFam θ) {a : GA D V} (ha : a ∈ GinfC V) {φ : GA D V → ℂ}
    (h : RapidDecSm θ V φ) : RapidDecSm θ V (Formalism.L2.Theta.rTr V a φ) := by

  have hR := h.rapidDec.mul_right a
  refine ⟨⟨hR.1, ?_, hR.2.1⟩, rTr_mem_smFun hθ a h.smooth, fun l hl => ?_⟩
  · obtain ⟨U, hU, hUφ⟩ := h.level
    refine ⟨U, hU, fun u hu huf g => ?_⟩
    show φ (g * u * a) = φ (g * a)
    rw [mul_assoc, ← comm_of_mem V ha huf, ← mul_assoc, hUφ u hu huf]
  · rw [rWord_rTr_adelic hθ a φ hl]
    refine (h.decay _ fun p hp => ?_).mul_right a
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    exact adAt_mem_lieAt hθ a (hl q hq)

theorem RapidDecSm.rTr (hθ : IsInfFam θ) {φ : GA D V → ℂ} (h : RapidDecSm θ V φ) (k : GA D V) :
    RapidDecSm θ V (Formalism.L2.Theta.rTr V k φ) := by

  obtain ⟨a, ha, f, hf, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D V).1 k
  have e : Formalism.L2.Theta.rTr V (a * f) φ = Formalism.L2.Theta.rTr V a (Formalism.L2.Theta.rTr V f φ) := by
    funext g
    simp only [Formalism.L2.Theta.rTr, mul_assoc]
  rw [e]
  exact rapidDecSm_rTr_of_mem_GinfC hθ ha (h.rTr_fin hf)

end GlobalTheory.Size

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.JacClosed

open GlobalTheory.MixModel.HypDec

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ}

def uniOnX (d : HypDec S S₀ ρ) : Set (GA D S) :=
  {g | mt S g ⬝ d.jX = d.jX ⬝ blockX d g ∧ (∀ i j : Fin ρ, j < i → blockX d g i j = 0) ∧ ∀ i, blockX d g i i = 1}

theorem t2Space_cm_host_adeles : T2Space (AE D) := by
  haveI : T2Space (Mx D 1 1) := (lattice_Mx D 1 1).2.2.2.1
  exact @T2Space.of_injective_continuous _ _ _ _ this (fun a : AE D => (Matrix.of fun _ _ => a : Mx D 1 1))
    (fun a b h => congrFun (congrFun h 0) 0) (continuous_pi fun _ => continuous_pi fun _ => continuous_id)

theorem isClosed_uniOnX (d : HypDec S S₀ ρ) : IsClosed (uniOnX d) := by
  haveI : T2Space (AE D) := t2Space_cm_host_adeles
  have hm := GlobalTheory.MixModel.continuous_mt (D := D) S
  have hb : Continuous fun g : GA D S => blockX d g := continuous_const.matrix_mul (hm.matrix_mul continuous_const)
  have e1 : {g : GA D S | ∀ i j : Fin ρ, j < i → blockX d g i j = 0} =
      ⋂ i : Fin ρ, ⋂ j : Fin ρ, ⋂ (_ : j < i), {g | blockX d g i j = 0} := by ext; simp only [Set.mem_setOf_eq, Set.mem_iInter]
  have e2 : {g : GA D S | ∀ i : Fin ρ, blockX d g i i = 1} = ⋂ i : Fin ρ, {g | blockX d g i i = 1} := by ext; simp only [Set.mem_setOf_eq, Set.mem_iInter]
  have c1 : IsClosed {g : GA D S | ∀ i j : Fin ρ, j < i → blockX d g i j = 0} := by
    rw [e1]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_eq ((continuous_apply j).comp ((continuous_apply i).comp hb)) continuous_const
  have c2 : IsClosed {g : GA D S | ∀ i : Fin ρ, blockX d g i i = 1} := by
    rw [e2]
    exact isClosed_iInter fun i => isClosed_eq ((continuous_apply i).comp ((continuous_apply i).comp hb)) continuous_const
  exact (isClosed_eq (hm.matrix_mul continuous_const) (continuous_const.matrix_mul hb)).inter (c1.inter c2)

theorem mem_uniOnX_of (d : HypDec S S₀ ρ) {g : GA D S} {u : GL (Fin ρ) (AE D)} (hu : u ∈ upperUni ρ (AE D))
    (h : mt S g ⬝ d.jX = d.jX ⬝ u.1) : g ∈ uniOnX d := by
  have hb : blockX d g = u.1 := by rw [blockX, h, ← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul]
  refine ⟨by rw [hb]; exact h, fun i j hij => ?_, fun i => ?_⟩
  · rw [hb]; exact (hu i j).1 hij
  · rw [hb]; exact (hu i i).2

def uniOnXSub (d : HypDec S S₀ ρ) : Subgroup (GA D S) where
  carrier := {g | ∃ u ∈ UX D ρ, mt S g ⬝ d.jX = d.jX ⬝ u.1}
  one_mem' := ⟨1, one_mem _, by rw [mt_one, Matrix.one_mul, Units.val_one, Matrix.mul_one]⟩
  mul_mem' := by
    rintro a b ⟨u, hu, ha⟩ ⟨v, hv, hb⟩
    exact ⟨u * v, mul_mem hu hv, by
      rw [mt_mul, Matrix.mul_assoc, hb, ← Matrix.mul_assoc, ha, Matrix.mul_assoc, Units.val_mul]⟩
  inv_mem' := by
    rintro a ⟨u, hu, ha⟩
    refine ⟨u⁻¹, inv_mem hu, ?_⟩
    have h1 : mt S a⁻¹ ⬝ d.jX ⬝ u.1 = d.jX := by
      rw [Matrix.mul_assoc, ← ha, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]
    calc mt S a⁻¹ ⬝ d.jX = mt S a⁻¹ ⬝ d.jX ⬝ (u.1 ⬝ (u⁻¹).1) := by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      _ = d.jX ⬝ (u⁻¹).1 := by rw [← Matrix.mul_assoc, h1]

def uniUnit (U : Mx D ρ ρ) (h0 : ∀ i j : Fin ρ, j < i → U i j = 0) (h1 : ∀ i, U i i = 1) : GL (Fin ρ) (AE D) :=
  Matrix.nonsingInvUnit U (by
    rw [Matrix.det_of_upperTriangular (fun i j (h : j < i) => h0 i j h)]
    simp [h1])

theorem uniUnit_val (U : Mx D ρ ρ) (h0 : ∀ i j : Fin ρ, j < i → U i j = 0) (h1 : ∀ i, U i i = 1) :
    (uniUnit U h0 h1).1 = U := rfl

theorem uniUnit_mem (U : Mx D ρ ρ) (h0 : ∀ i j : Fin ρ, j < i → U i j = 0) (h1 : ∀ i, U i i = 1) :
    uniUnit U h0 h1 ∈ upperUni ρ (AE D) := fun i j => ⟨h0 i j, h1 i⟩

theorem flagN_le (d : HypDec S S₀ ρ) : flagN d ≤ uniOnXSub d := by
  show Subgroup.closure _ ≤ _
  rw [Subgroup.closure_le]
  rintro g ⟨hX, -⟩
  choose a ha1 ha2 using hX
  let A : Mx D ρ ρ := Matrix.of fun j i => a i j
  have hcol : subOne S g ⬝ d.jX = d.jX ⬝ A := by
    ext k i
    exact congrFun (ha2 i) k
  have h0 : ∀ i j : Fin ρ, j < i → (1 + A) i j = 0 := fun i j h => by
    simp only [Matrix.add_apply, A, Matrix.of_apply, Matrix.one_apply_ne h.ne', ha1 j i h.le, add_zero]
  have h1 : ∀ i, (1 + A) i i = 1 := fun i => by
    simp only [Matrix.add_apply, A, Matrix.of_apply, Matrix.one_apply_eq, ha1 i i le_rfl, add_zero]
  refine ⟨uniUnit (1 + A) h0 h1, uniUnit_mem _ h0 h1, ?_⟩
  rw [uniUnit_val, Matrix.mul_add, Matrix.mul_one, ← hcol, GlobalTheory.MixModel.HypDec.subOne_mul, add_sub_cancel]

theorem jacGrp_le (d : HypDec S S₀ ρ) : jacGrp d ≤ uniOnXSub d := by
  refine sup_le (flagN_le d) ?_
  rintro _ ⟨h, rfl⟩
  exact ⟨1, one_mem _, by rw [wittDecomp_anisotropicEmbedding_inclX, Units.val_one, Matrix.mul_one]⟩



theorem mem_jacGrp_of_fix (d : HypDec S S₀ ρ) {g : GA D S} (hg : mt S g ⬝ d.jX = d.jX) : g ∈ jacGrp d := by
  have hU : adj (mt S g) ⬝ (gA S ⬝ (mt S g ⬝ d.j0)) = gA S ⬝ d.j0 := cancel₃ (mt_unitary S g) d.j0
  have hY : d.pY ⬝ (mt S g ⬝ d.j0) = 0 := by
    have h1 : adj d.jX ⬝ (gA S ⬝ (mt S g ⬝ d.j0)) = adj (mt S g ⬝ d.jX) ⬝ (gA S ⬝ (mt S g ⬝ d.j0)) := by rw [hg]
    rw [d.pY_eq, Matrix.mul_assoc, h1, adj_mul, Matrix.mul_assoc, hU, d.wittDecomp_gram_X_anisotropic]
  obtain ⟨b, hb⟩ : ∃ b, d.pX ⬝ (mt S g ⬝ d.j0) = b := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, d.p0 ⬝ (mt S g ⬝ d.j0) = A := ⟨_, rfl⟩
  have hdec : mt S g ⬝ d.j0 = d.jX ⬝ b + d.j0 ⬝ A := by
    have he : (d.jX ⬝ d.pX + d.j0 ⬝ d.p0 + d.jY ⬝ d.pY) ⬝ (mt S g ⬝ d.j0) = (1 : Mx D S.rank S.rank) ⬝ (mt S g ⬝ d.j0) := by rw [d.sum_eq_one]
    simp only [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hY, hb, hA, Matrix.mul_zero, add_zero] at he
    exact he.symm
  have hAu : adj A * (gA S₀ * A) = gA S₀ := by
    have h1 : adj (mt S g ⬝ d.j0) ⬝ (gA S ⬝ (mt S g ⬝ d.j0)) = gA S₀ := by
      rw [adj_mul, Matrix.mul_assoc, hU, d.gram_00]
    rw [hdec] at h1
    simp only [adj_add, adj_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, cancel₃ d.gram_XX, cancel₃ d.wittDecomp_gram_X_anisotropic,
      cancel₃ d.gram_0X, cancel₃ d.gram_00, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add] at h1
    exact h1
  obtain ⟨h, hAh⟩ : ∃ h : GA D S₀, mt S₀ h = A := ⟨ofMat S₀ A hAu, rfl⟩
  have hAi : A ⬝ mt S₀ h⁻¹ = mt S₀ 1 := by rw [← hAh, ← mt_mul, mul_inv_cancel]
  have hi : (d.emb0 h)⁻¹ = d.emb0 h⁻¹ := (map_inv d.emb0 h).symm
  have hm0 : mt S (g * d.emb0 h⁻¹) = mt S g ⬝ mt S (d.emb0 h⁻¹) := mt_mul S _ _
  have he0 : mt S (d.emb0 h⁻¹) ⬝ d.j0 = d.j0 ⬝ mt S₀ h⁻¹ := d.wittDecomp_anisotropicEmbedding_inclAnisotropic h⁻¹
  have heX : mt S (d.emb0 h⁻¹) ⬝ d.jX = d.jX := d.wittDecomp_anisotropicEmbedding_inclX h⁻¹
  have hj : d.j0 ⬝ mt S₀ (1 : GA D S₀) = d.j0 := by rw [mt_one, Matrix.mul_one]
  have hn0' : mt S (g * (d.emb0 h)⁻¹) ⬝ d.j0 = d.jX ⬝ (b ⬝ mt S₀ h⁻¹) + d.j0 := by
    have s1 : mt S (g * (d.emb0 h)⁻¹) ⬝ d.j0 = (mt S g ⬝ d.j0) ⬝ mt S₀ h⁻¹ := by
      rw [hi, hm0, Matrix.mul_assoc, he0, Matrix.mul_assoc]
    have s2 : (d.jX ⬝ b + d.j0 ⬝ A) ⬝ mt S₀ h⁻¹ = d.jX ⬝ (b ⬝ mt S₀ h⁻¹) + d.j0 ⬝ (A ⬝ mt S₀ h⁻¹) :=
      (Matrix.add_mul (d.jX ⬝ b) (d.j0 ⬝ A) (mt S₀ h⁻¹)).trans
        (congrArg₂ (· + ·) (Matrix.mul_assoc d.jX b (mt S₀ h⁻¹)) (Matrix.mul_assoc d.j0 A (mt S₀ h⁻¹)))
    have s3 : d.jX ⬝ (b ⬝ mt S₀ h⁻¹) + d.j0 ⬝ (A ⬝ mt S₀ h⁻¹) = d.jX ⬝ (b ⬝ mt S₀ h⁻¹) + d.j0 :=
      (congrArg (fun M : Mx D S₀.rank S₀.rank => d.jX ⬝ (b ⬝ mt S₀ h⁻¹) + d.j0 ⬝ M) hAi).trans (congrArg (fun M : Mx D S.rank S₀.rank => d.jX ⬝ (b ⬝ mt S₀ h⁻¹) + M) hj)
    exact s1.trans ((congrArg (fun M : Mx D S.rank S₀.rank => M ⬝ mt S₀ h⁻¹) hdec).trans (s2.trans s3))
  have hn0 : mt S (g * (d.emb0 h)⁻¹) ⬝ d.j0 = d.j0 + d.jX ⬝ (b ⬝ mt S₀ h⁻¹) := hn0'.trans (add_comm _ _)
  have hnX' : mt S (g * (d.emb0 h)⁻¹) ⬝ d.jX = d.jX := by
    rw [hi, hm0, Matrix.mul_assoc, heX, hg]
  have hnX : mt S (g * (d.emb0 h)⁻¹) ⬝ d.jX = d.jX ⬝ (1 : GL (Fin ρ) (AE D)).1 := by
    rw [Units.val_one, Matrix.mul_one]; exact hnX'
  have hn : g * (d.emb0 h)⁻¹ ∈ flagN d := d.mem_NFlag one_mem_upperUni hnX hn0
  have hm : g * (d.emb0 h)⁻¹ * d.emb0 h ∈ jacGrp d :=
    mul_mem (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right ⟨h, rfl⟩)
  rwa [inv_mul_cancel_right] at hm

theorem uniOnX_subset (d : HypDec S S₀ ρ) : uniOnX d ⊆ jacGrp d := by
  rintro g ⟨hX, h0, h1⟩
  set u := uniUnit (blockX d g) h0 h1
  have hl : d.levi u ∈ flagN d := d.levi_mem_NFlag (uniUnit_mem _ h0 h1)
  have hf : mt S ((d.levi u)⁻¹ * g) ⬝ d.jX = d.jX := by
    rw [← map_inv, mt_mul, Matrix.mul_assoc, hX, ← Matrix.mul_assoc, levi_jX, Matrix.mul_assoc,
      show (u⁻¹).1 ⬝ blockX d g = 1 from Units.inv_mul u, Matrix.mul_one]
  have := mul_mem (Subgroup.mem_sup_left (T := d.emb0.range) hl) (mem_jacGrp_of_fix d hf)
  rwa [mul_inv_cancel_left] at this

theorem jacGrp_eq (d : HypDec S S₀ ρ) : (jacGrp d : Set (GA D S)) = uniOnX d := by
  refine Set.Subset.antisymm (fun g hg => ?_) (uniOnX_subset d)
  obtain ⟨u, hu, h⟩ := jacGrp_le d hg
  exact mem_uniOnX_of d hu h

end GlobalTheory.JacClosed

namespace GlobalTheory

theorem jacGrp_isClosed : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), IsClosed (jacGrp d : Set (GA D S)) := by
  intro D S S₀ ρ d
  rw [GlobalTheory.JacClosed.jacGrp_eq]
  exact GlobalTheory.JacClosed.isClosed_uniOnX d

end GlobalTheory
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt GlobalTheory.Chain.RealLine
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_realIntertwiner_contraction_one_place : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f : WO V W → ℂ) (τ : D.what₂.Tau) (aS aT : ℚ) (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M) [DecidableEq D.what₂.Tau], IsInfFam θ → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.CompactFock ψ θ M M' ω f τ aS aT → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.LieFock ψ θ M M' ω f τ aS aT → IsItW θ M M' ω (ptOf ψ θ M M' f) It → ∀ (v : M'.Vec) (w : ∀ ρ, M.H ρ), ∃ A : PolF D W.rank V.rank →ₗ[ℂ] M'.sm τ →ₗ[ℂ] M.H τ, SemiW M M' τ aS aT A ∧ ∀ φ y u, ⟪u, A φ y⟫_ℂ = ellT M (Function.update w τ u) (inclT M (It φ (PiTensorProduct.tprod ℂ (Function.update v τ y)))) := by
  first | exact @GlobalTheory.Chain.RealLine.Semi.exists_semiW | exact GlobalTheory.Chain.RealLine.Semi.exists_semiW | (intros; apply GlobalTheory.Chain.RealLine.Semi.exists_semiW <;> assumption)
end
