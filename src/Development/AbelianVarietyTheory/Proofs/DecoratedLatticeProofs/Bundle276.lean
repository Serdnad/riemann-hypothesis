module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle012
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle035
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle258
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle199
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle254
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle202
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle255
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle212
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle064
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle257
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle143
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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle015
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SobContId
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle016
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth

@[expose] public section

section

open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

namespace GlobalTheory.ThetaDens

theorem eLpNorm_sub_tendsto_of_unif {X : Type} [MeasurableSpace X] (ν : Measure X) (hν : ν Set.univ = 1)
    (g : ℕ → X → ℂ) (f : X → ℂ) (hm : ∀ j, AEStronglyMeasurable (g j - f) ν)
    (h : TendstoUniformly g f Filter.atTop) :
    Filter.Tendsto (fun j => eLpNorm (g j - f) 2 ν) Filter.atTop (nhds 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨δ, hδ0, hδ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hε
  have hδ0' : (0 : ℝ) < δ := by exact_mod_cast hδ0
  filter_upwards [Metric.tendstoUniformly_iff.1 h δ hδ0'] with j hj
  have hb : ∀ᵐ x ∂ν, ‖(g j - f) x‖ ≤ δ := Filter.Eventually.of_forall fun x => by
    have := (hj x).le
    rwa [dist_comm, dist_eq_norm] at this
  refine (eLpNorm_le_of_ae_bound (hm j) hb).trans ?_
  simpa [hν] using hδ.le

theorem wordAct_heisDer_sub {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {θ : InfFam D}
    (hθ : IsInfFam θ) {S T : HSp D} {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g)
    (l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool)) :
    GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (f - g) =
      GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l f - GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [GlobalTheory.Size.wordAct_cons, ih, GlobalTheory.Size.wordAct_cons, GlobalTheory.Size.wordAct_cons, sub_eq_add_neg, sub_eq_add_neg,
      ← neg_one_smul ℂ, ← neg_one_smul ℂ (GlobalTheory.Size.heisDer ψ θ a _)]
    simp only [GlobalTheory.Size.heisDer]
    rw [GlobalTheory.Size.dRho_add hψ hθ a.1 _ (GlobalTheory.Size.theta_word hψ hθ l hf)
      (GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.Size.theta_word hψ hθ l hg)), GlobalTheory.Size.dRho_smul]

theorem sobO_sub_tendsto_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ S T : HSp D, ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ (u : ℕ → WO S T → ℂ) (f : WO S T → ℂ), IsThetaFunO ψ S T f → (∀ j, IsThetaFunO ψ S T (u j)) → (∀ l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool), TendstoUniformly (fun j => GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (u j)) (GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l f) Filter.atTop) → ∀ d, Filter.Tendsto (fun j => sobO ψ θ μ 𝓕 d (u j - f)) Filter.atTop (nhds 0) := by
  intro D ψ hψ θ hθ S T μ 𝓕 hμ u f hf hu hl d
  have : BorelSpace (WO S T) := ⟨rfl⟩
  have key : ∀ l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool), Filter.Tendsto
      (fun j => GlobalTheory.Size.l2O μ 𝓕 (GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (u j - f))) Filter.atTop (nhds 0) := by
    intro l
    simp only [wordAct_heisDer_sub hψ hθ (hu _) hf l, GlobalTheory.Size.l2O]
    exact eLpNorm_sub_tendsto_of_unif _ (by rw [Measure.restrict_apply_univ]; exact hμ.2.2) _ _
      (fun j => ((GlobalTheory.Size.theta_word hψ hθ l (hu j)).cont.sub
        (GlobalTheory.Size.theta_word hψ hθ l hf).cont).aestronglyMeasurable) (hl l)
  have := tendsto_finsetSum (Finset.range (d + 1)) fun k _ =>
    tendsto_finsetSum (Finset.univ : Finset (Fin k → D.what₂.Tau × Fin T.rank × Fin S.rank × Bool))
      fun a _ => key (List.ofFn a)
  simp only [Finset.sum_const_zero] at this
  exact this

end GlobalTheory.ThetaDens
end

section

open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

namespace GlobalTheory.ThetaDens


open GlobalTheory.FockCompare GlobalTheory.OrientedHeis GlobalTheory.Size in
theorem sm_of_tendstoUniformly_words {G R A : Type} [AddCommGroup G] [NormedAddCommGroup R] [NormedSpace ℝ R]
    [FiniteDimensional ℝ R] [Fintype A] (ι : R →+ G) (p : G →+ R) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ) (hp : ∀ x, p (ι x) = x)
    (v : A → R) (c : A → R →L[ℝ] ℝ) (hv : ∀ x, ∑ a, c a x • v a = x) (g : List A → ℕ → G → ℂ)
    (hg : ∀ l j, Sm ι (g l j)) (hd : ∀ a l j, g (a :: l) j = hD ι p om (v a) (g l j)) (F : List A → G → ℂ)
    (hF : ∀ l, TendstoUniformly (g l) (F l) Filter.atTop) (l : List A) : Sm ι (F l) := by
  intro w
  refine GlobalTheory.T.smooth_of_limit_class_stable_under_directional_derivs v c hv (fun φ => ∃ l, φ = fun y => F l (w + ι y)) ?_ _ ⟨l, rfl⟩
  rintro _ ⟨l, rfl⟩
  have hU : ∀ l, TendstoLocallyUniformly (fun j y => g l j (w + ι y)) (fun y => F l (w + ι y)) Filter.atTop :=
    fun l => ((hF l).comp fun y => w + ι y).tendstoLocallyUniformly
  refine ⟨fun j y => g l j (w + ι y), fun j => (hg l j w).differentiable (by simp), hU l, fun a => ?_⟩
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun x : R => (om.flip (v a) (p w + x) : ℝ) :=
    (LinearMap.toContinuousLinearMap (om.flip (v a))).contDiff.comp (contDiff_const.add contDiff_id)
  have hα : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      fun x : R => (Real.pi * Complex.I : ℂ) * ((om.flip (v a) (p w + x) : ℝ) : ℂ) :=
    contDiff_const.mul (Complex.ofRealCLM.contDiff.comp h1)
  refine ⟨_, hα, _, ⟨a :: l, rfl⟩, ?_⟩
  have hc : Continuous fun y => F l (w + ι y) :=
    (hU l).continuous (Filter.Eventually.of_forall fun j => (hg l j w).continuous).frequently
  have h0 : TendstoLocallyUniformly
      (fun (_ : ℕ) (x : R) => (Real.pi * Complex.I : ℂ) * ((om.flip (v a) (p w + x) : ℝ) : ℂ))
      (fun x : R => (Real.pi * Complex.I : ℂ) * ((om.flip (v a) (p w + x) : ℝ) : ℂ)) Filter.atTop :=
    fun U hU x => ⟨Set.univ, Filter.univ_mem, Filter.Eventually.of_forall fun _ _ _ => refl_mem_uniformity hU⟩
  have h2 := (h0.mul₀ (hU l) hα.continuous hc).add (hU (a :: l))
  have e : (fun j y => fderiv ℝ (fun y => g l j (w + ι y)) y (v a)) = fun j x =>
      (Real.pi * Complex.I : ℂ) * ((om.flip (v a) (p w + x) : ℝ) : ℂ) * g l j (w + ι x) + g (a :: l) j (w + ι x) := by
    funext j x
    rw [hd, hD_eq_fderiv ι p om _ (hg l j), map_add p, hp, LinearMap.flip_apply]
    have := fderiv_comp_add_left (𝕜 := ℝ) (f := fun y : R => g l j (w + ι y)) (x := 0) x
    rw [add_zero] at this
    have e2 : (fun y : R => g l j (w + ι x + ι y)) = fun y => g l j (w + ι (x + y)) := by
      funext y
      rw [map_add (f := _), add_assoc]
    rw [← this, e2]
    ring
  rw [e]
  exact h2

theorem sum_coord_single {τs : Type} [Fintype τs] {m n : ℕ} (x : τs → Fin m → Fin n → ℂ)
    (v : τs × Fin m × Fin n × Bool → τs → Fin m → Fin n → ℂ)
    (hv : ∀ a τ i j, v a τ i j = if τ = a.1 then
      Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1) i j else 0) :
    ∑ a : τs × Fin m × Fin n × Bool,
      (if a.2.2.2 then (x a.1 a.2.1 a.2.2.1).im else (x a.1 a.2.1 a.2.2.1).re) • v a = x := by
  funext τ i j
  simp only [Finset.sum_apply, Pi.smul_apply, hv, Fintype.sum_prod_type, Matrix.single_apply]
  rw [Finset.sum_eq_single τ (fun b _ hb => by simp [hb.symm]) (by simp),
    Finset.sum_eq_single i (fun b _ hb => by simp [hb]) (by simp),
    Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)]
  simp [add_comm]


open GlobalTheory.FockCompare GlobalTheory.OrientedHeis GlobalTheory.Size in
theorem contDiff_of_tendstoUniformly_words : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D) (u : ℕ → WO S T → ℂ), (∀ j, IsThetaFunO ψ S T (u j)) → ∀ F : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) → WO S T → ℂ, (∀ l, TendstoUniformly (fun j => GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (u j)) (F l) Filter.atTop) → ∀ (l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool)) (k : ℕ) (L : (Fin k → ℝ) →+ WO S T), Continuous L → (∀ t, (L t).map (finPart D) = 0) → ∀ w, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => F l (w + L t) := by
  intro D ψ hψ θ hθ S T u hu F hF l
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  refine ((smooth_iff_sm_and_real_lines D θ σ h T S).1 (F l)).2 ?_
  let z : D.what₂.Tau × Fin T.rank × Fin S.rank × Bool → Matrix (Fin T.rank) (Fin S.rank) ℂ := fun a =>
    Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1)
  let c : D.what₂.Tau × Fin T.rank × Fin S.rank × Bool → RW T S →L[ℝ] ℝ := fun a =>
    (if a.2.2.2 then Complex.imCLM else Complex.reCLM).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin S.rank => ℂ) a.2.2.1).comp
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin T.rank => Fin S.rank → ℂ) a.2.1).comp
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : D.what₂.Tau => Fin T.rank → Fin S.rank → ℂ) a.1)))
  refine sm_of_tendstoUniformly_words (iotaW σ T S) (piW θ T S) (omO S T) (h.pi_iota T S)
    (fun a => piW θ T S (lineAt θ a.1 (z a) 1)) c (fun x => ?_) (fun l j => wordAct (heisDer ψ θ) l (u j))
    (fun l j => theta_sm h (theta_word hψ hθ l (hu j)))
    (fun a l j => dLine_eq_hD h hψ (isRealDir_lineAt hθ a.1 (z a)) _) F hF l
  refine Eq.trans ?_ (sum_coord_single x (fun a => piW θ T S (lineAt θ a.1 (z a) 1)) fun a τ i j => ?_)
  · refine Finset.sum_congr rfl fun a _ => ?_
    congr 1
    obtain ⟨τ, i, j, b⟩ := a
    cases b <;> rfl
  · have := congrFun (congrFun ((GlobalTheory.OrientedHeis.isLineAt_lineAt hθ a.1 (z a)).2.2 1 τ) i) j
    refine Eq.trans this ?_
    split_ifs <;> simp [z, *]

end GlobalTheory.ThetaDens
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.MovesSplit

open GlobalTheory.FinPl GlobalTheory.FinPl.KSplit GlobalTheory.FinPlLoc

variable {D : D7}

theorem idem_eq_algebraMap (R : Pl D → Prop) :
    idem D R = algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (ePl D R)) := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  rfl

theorem idem_smul_mem (S : HSp D) (L : Lat S) {P : Pl D → Prop} (R : Pl D → Prop) {y : Fin S.rank → AE D}
    (hy : y ∈ latV S L P) : idem D R • y ∈ latV S L (fun p => P p ∧ R p) := by
  classical
  rw [idem_eq_algebraMap]
  exact smul_mem_latV S L (ePl D R) (ePl_int R) (fun v hv => by rw [evalV_ePl, if_neg hv]) hy

theorem idem_smul_eq (S : HSp D) (R : Pl D → Prop) {y : Fin S.rank → AE D} (hy : ∀ i, y i ∈ idAt D R) :
    idem D R • y = y :=
  funext fun i => (mem_idAt_iff R (y i)).1 (hy i)

theorem mem_latV_iff_all (S : HSp D) (L : Lat S) (R : Pl D → Prop) {y : Fin S.rank → AE D}
    (hy : ∀ i, y i ∈ idAt D R) : y ∈ latV S L R ↔ y ∈ latV S L (fun _ => True) := by
  refine ⟨fun h => latV_mono S L (fun _ _ => trivial) h, fun h => ?_⟩
  have h1 := idem_smul_mem S L R h
  rw [idem_smul_eq S R hy] at h1
  exact latV_mono S L (fun _ h => h.2) h1

theorem idem_add_idem (P : Pl D → Prop) {a : AE D} (ha : a ∈ idAt D (fun _ => True)) :
    idem D P * a + idem D (fun p => ¬ P p) * a = a := by
  classical
  rw [← sub_eq_zero]
  apply eq_zero_of_comp
  · rw [RingHom.map_sub, RingHom.map_add (f := _), RingHom.map_mul, RingHom.map_mul, infPart_of_idAt ha, mul_zero, mul_zero, add_zero, sub_zero]
  · intro w
    rw [RingHom.map_sub, RingHom.map_add (f := _), RingHom.map_mul, RingHom.map_mul, compAt_idem, compAt_idem]
    by_cases h : P w
    · simp [h]
    · simp [h]

theorem mem_latV_iff_parts (S : HSp D) (L : Lat S) (P : Pl D → Prop) {y : Fin S.rank → AE D}
    (hy : ∀ i, y i ∈ idAt D (fun _ => True)) :
    y ∈ latV S L (fun _ => True) ↔
      idem D (fun p => ¬ P p) • y ∈ latV S L (fun p => ¬ P p) ∧ idem D P • y ∈ latV S L P := by
  constructor
  · intro h
    exact ⟨latV_mono S L (fun _ h => h.2) (idem_smul_mem S L _ h), latV_mono S L (fun _ h => h.2) (idem_smul_mem S L P h)⟩
  · rintro ⟨h1, h2⟩
    have e : y = idem D P • y + idem D (fun p => ¬ P p) • y :=
      funext fun i => (idem_add_idem P (hy i)).symm
    rw [e]
    exact add_mem (latV_mono S L (fun _ _ => trivial) h2) (latV_mono S L (fun _ _ => trivial) h1)

theorem idem_smul_supp (S : HSp D) (R : Pl D → Prop) (y : Fin S.rank → AE D) (i : Fin S.rank) :
    (idem D R • y) i ∈ idAt D R :=
  Ideal.mul_mem_right _ _ (idem_mem_idAt R)

end GlobalTheory.FinPl.MovesSplit


open GlobalTheory.FinPl.MovesSplit GlobalTheory.FinPl.KSplit GlobalTheory.FinPlLoc in
theorem GlobalTheory.FinPl.moves_iff_moves_on_off : ∀ {D : D7} (S : HSp D) (g : GA D S) (L : GlobalTheory.FinPl.Lat S)
    (P : GlobalTheory.FinPl.Pl D → Prop), (GlobalTheory.FinPl.Moves S g L L (fun p => ¬ P p) ∧ GlobalTheory.FinPl.Moves S g L L P) ↔
      GlobalTheory.FinPl.Moves S g L L (fun _ => True) := by
  intro D S g L P
  constructor
  · rintro ⟨hn, hp⟩ y hy
    rw [mem_latV_iff_parts S L P hy, mem_latV_iff_parts S L P (mulVec_mem S _ hy), ← Matrix.mulVec_smul,
      ← Matrix.mulVec_smul]
    exact and_congr (hn _ (idem_smul_supp S _ y)) (hp _ (idem_smul_supp S P y))
  · intro h
    have key : ∀ R : GlobalTheory.FinPl.Pl D → Prop, GlobalTheory.FinPl.Moves S g L L R := by
      intro R y hy
      rw [mem_latV_iff_all S L R hy, mem_latV_iff_all S L R (mulVec_mem S _ hy)]
      exact h y fun i => idAt_mono (fun _ _ => trivial) (hy i)
    exact ⟨key _, key _⟩

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl IsBase onHalf phiQ rdQ)

theorem _root_.GlobalTheory.T.twistPlaceChainStepDatumSupport_eq_valuative : ∀ (D : D7) (v : FinPl D) (a b r : ℕ), GlobalTheory.NrmVol.suppQ (a := a) (b := b) v r = {x | topL r x ∈ Units.val '' (GlobalTheory.SplitWeil.KO (Fv D.host.F v) (Fin r) : Set (GL (Fin r) (Fv D.host.F v))) ∧ (∀ i j, ValuativeRel.valuation (Fv D.host.F v) (x i j) ≤ 1) ∧ ∀ i j, r ≤ i.val → j.val < r → ValuativeRel.valuation (Fv D.host.F v) (x i j) < 1} ∧ {y : Matrix (Fin b) (Fin a) (Fv D.host.F v) | ∀ i j, Valued.v (y i j) ≤ 1} = {x | ∀ i j, ValuativeRel.valuation (Fv D.host.F v) (x i j) ≤ 1} := by
  first | exact @GlobalTheory.NrmVol.suppQ_eq_valuative | exact GlobalTheory.NrmVol.suppQ_eq_valuative | (intros; apply GlobalTheory.NrmVol.suppQ_eq_valuative <;> assumption)
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
open GlobalTheory.Core.Rk.SumBox

theorem _root_.GlobalTheory.T.isCartanInvolution_orthDecBlockSumRealMat : ∀ (D : D7) (B W H : HSp D) (o : OrthDec B W H) (sW : RealMat W) (sH : RealMat H), (∀ τ, IsCartanInv (gramAt D W τ) (sW τ)) → (∀ τ, IsCartanInv (gramAt D H τ) (sH τ)) → ∀ τ, IsCartanInv (gramAt D B τ) (sumMat o sW sH τ) := by
  first | exact @GlobalTheory.Core.Rk.SumBox.isCartanInv_sumMat | exact GlobalTheory.Core.Rk.SumBox.isCartanInv_sumMat | (intros; apply GlobalTheory.Core.Rk.SumBox.isCartanInv_sumMat <;> assumption)
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
open GlobalTheory.Core.Rk.SumBox

theorem _root_.GlobalTheory.T.orthDecSumLattice_selfDual : ∀ (D : D7) (B W H : HSp D) (o : OrthDec B W H) (LW : Lat W) (LH : Lat H), IsSelfDualC W LW → IsSelfDualC H LH → IsSelfDualC B (sumLatO o LW LH) := by
  first | exact @GlobalTheory.Core.Rk.SumBox.selfDual_sumLatO | exact GlobalTheory.Core.Rk.SumBox.selfDual_sumLatO | (intros; apply GlobalTheory.Core.Rk.SumBox.selfDual_sumLatO <;> assumption)
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
open GlobalTheory.Core.Rk.SumBox

theorem _root_.GlobalTheory.T.spherical_outside_box_product_orthDecSumLattice : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B W H : HSp D) (o : OrthDec B W H) (LA : Lat A) (LW : Lat W) (LH : Lat H) (Sf : Finset (FinPl D)) (Φ : WO A W → ℂ) (Φ' : WO A H → ℂ), IsSphOff ψ A W LA LW Sf Φ → IsSphOff ψ A H LA LH Sf Φ' → IsSphOff ψ A B LA (sumLatO o LW LH) Sf (o.boxT A Φ Φ') := by
  first | exact @GlobalTheory.Core.Rk.SumBoxSph.isSphOff_boxT | exact GlobalTheory.Core.Rk.SumBoxSph.isSphOff_boxT | (intros; apply GlobalTheory.Core.Rk.SumBoxSph.isSphOff_boxT <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.ExtZeroLat

variable {D : D7}

theorem mxAt_mul_left {P : Pl D → Prop} {a b c : ℕ} (y : Mx D a b) {x : Mx D b c} (hx : MxAt P x) : MxAt P (y ⬝ x) := by
  intro i j
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hx l j)

theorem symplO_resT_symm_left {S A L T : HSp D} (o : OrthDec S A L) (a : WO T A) (t : WO T S) :
    symplO T S ((o.resT T).symm (a, 0)) t = symplO T A a (o.pA ⬝ t) := by
  rw [o.symplO_resT, AddEquiv.apply_symm_apply]
  have h0 : symplO T L 0 ((o.resT T) t).2 = 0 := by simp [symplO, hO]
  rw [h0, add_zero]; rfl

end GlobalTheory.FinPl.ExtZeroLat


open GlobalTheory.FinPl.ExtZeroLat in
theorem GlobalTheory.FinPl.ExtZero.extZero_mem_latO_target : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (ψ : AddChar (AF D.host.F) ℂ) (S A L T : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (β : Frame p T n) (LA : Lat A) (LS : Lat S) (LT : Lat T) (ΛT : Submodule 𝒪[k] (n → k)), (∀ u : WO T A, MxAt (· = p.v) u → (u ∈ latO T A (LT : Set _) (LA : Set _) (· = p.v) ↔ ∀ u' ∈ latO T A (LT : Set _) (LA : Set _) (· = p.v), ψ (symplO T A u u') = 1)) → (∀ u : WO T S, MxAt (· = p.v) u → (u ∈ latO T S (LT : Set _) (LS : Set _) (· = p.v) ↔ ∀ u' ∈ latO T S (LT : Set _) (LS : Set _) (· = p.v), ψ (symplO T S u u') = 1)) → halfInd p.e (latO T S (LT : Set _) (LS : Set _) (· = p.v)) = o.boxT T (halfInd p.e (latO T A (LT : Set _) (LA : Set _) (· = p.v))) (GlobalTheory.FinPl.ExtZero.rowFun β ζ (dualInd ΛT)) → ∀ u ∈ latO T A (LT : Set _) (LA : Set _) (· = p.v), (o.resT T).symm (u, 0) ∈ latO T S (LT : Set _) (LS : Set _) (· = p.v) := by
  intro D k _ _ _ _ p n _ _ ψ S A L T o ζ β LA LS LT ΛT hA hS hfac u hu
  classical
  set ΛA := latO T A (LT : Set _) (LA : Set _) (· = p.v) with hΛA
  set ΛS := latO T S (LT : Set _) (LS : Set _) (· = p.v) with hΛS
  have he := p.split
  have hce := GlobalTheory.SplitScalar.isSplitIdem_conj he
  obtain ⟨ε, hε, hsum⟩ := p.above
  have hact := (GlobalTheory.FinPl.placeIdem_acts D p.v ε hε).1

  have hsplit : ∀ {m n : ℕ} (x : Mx D m n), MxAt (· = p.v) x → p.e • x + cA D p.e • x = x := by
    intro m n x hx
    rw [← add_smul, hsum]
    ext i j
    rw [Matrix.smul_apply, smul_eq_mul]
    exact (hact _).1 (hx i j)

  have hrow0 : GlobalTheory.FinPl.ExtZero.rowFun β ζ (dualInd ΛT) 0 = 1 := by
    have hz : GlobalTheory.FinPl.ExtZero.zrow β ζ (0 : WO T L) = 0 := by
      simp only [GlobalTheory.FinPl.ExtZero.zrow, Matrix.vecMul_zero, Pi.zero_apply, map_zero]
      have : ((fun _ => 0 : Fin T.rank → k) ᵥ* β.b) = 0 := Matrix.zero_vecMul _
      rw [this, smul_zero]
    have h0 : IsHalf p.e (0 : WO T L) := fun i j => by simp
    have hd : InDual ΛT (0 : n → k) := fun y _ => by
      rw [zero_dotProduct]; exact zero_mem _
    simp [GlobalTheory.FinPl.ExtZero.rowFun, hz, dualInd, h0, hd]

  have hext : ∀ a ∈ ΛA, IsHalf p.e a → (o.resT T).symm (a, 0) ∈ ΛS := by
    intro a ha hah
    have h1 := congrFun hfac ((o.resT T).symm (a, 0))
    rw [OrthDec.boxT, AddEquiv.apply_symm_apply, hrow0, mul_one] at h1
    have h2 : halfInd p.e ΛA a = 1 := by simp [halfInd, ha, hah]
    rw [h2] at h1
    unfold halfInd at h1
    by_contra hn
    rw [if_neg fun h => hn h.1] at h1
    exact zero_ne_one h1

  have hres : ∀ t ∈ ΛS, IsHalf p.e t → o.pA ⬝ t ∈ ΛA := by
    intro t ht hth
    have h1 := congrFun hfac t
    have h2 : halfInd p.e ΛS t = 1 := by simp [halfInd, ht, hth]
    rw [h2, OrthDec.boxT] at h1
    by_contra hn
    have : halfInd p.e ΛA ((o.resT T) t).1 = 0 := by
      unfold halfInd; rw [if_neg fun h => hn h.1]
    rw [this, zero_mul] at h1
    exact one_ne_zero h1
  have huM : MxAt (· = p.v) u := GlobalTheory.FinPl.LatMem.latO_mxAt hu
  have heu : p.e • u ∈ ΛA := GlobalTheory.LatticeStable.smul_mem_latO D T A _ _ _ _ (finPart_idem_mem he.1) u hu
  have hι : (o.resT T).symm (p.e • u, 0) ∈ ΛS := hext _ heu (smul_isHalf he.1 u)
  have hιM : MxAt (· = p.v) ((o.resT T).symm (u, 0)) := by
    rw [OrthDec.resT_symm_apply, Matrix.mul_zero, add_zero]
    exact mxAt_mul_left _ huM
  refine (hS _ hιM).2 fun u' hu' => ?_
  have hu'M : MxAt (· = p.v) u' := GlobalTheory.FinPl.LatMem.latO_mxAt hu'
  have heu' : p.e • u' ∈ ΛS := GlobalTheory.LatticeStable.smul_mem_latO D T S _ _ _ _ (finPart_idem_mem he.1) u' hu'
  have hceu' : cA D p.e • u' ∈ ΛS := GlobalTheory.LatticeStable.smul_mem_latO D T S _ _ _ _ (finPart_idem_mem hce.1) u' hu'
  rw [symplO_resT_symm_left, ← hsplit u' hu'M, Matrix.mul_add, symplO_add_right, AddChar.map_add_eq_mul]
  have part1 : ψ (symplO T A u (o.pA ⬝ (p.e • u'))) = 1 :=
    (hA u huM).1 hu _ (hres _ heu' (smul_isHalf he.1 u'))
  have part2 : ψ (symplO T A u (o.pA ⬝ (cA D p.e • u'))) = 1 := by
    rw [← hsplit u huM, symplO_add_left, AddChar.map_add_eq_mul]
    have hz : symplO T A (cA D p.e • u) (o.pA ⬝ (cA D p.e • u')) = 0 := by
      refine symplO_conjHalf he (smul_isHalf hce.1 u) ?_
      intro i j
      rw [Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [mul_left_comm, (smul_isHalf hce.1 u') l j]
    rw [hz, AddChar.map_zero_eq_one, mul_one, ← symplO_resT_symm_left]
    exact (hS _ (GlobalTheory.FinPl.LatMem.latO_mxAt hι)).1 hι _ hceu'
  rw [part1, part2, one_mul]

end
end
