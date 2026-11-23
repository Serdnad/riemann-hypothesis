module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle157
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle146
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLineLinkGramSimilitudeBijective
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle147
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle148
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle149
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QuasiOfFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle155
import Formalism.LocalToGlobal.HilbertRowConditions.IsHilbertCF
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel ValuativeRel
open scoped Pointwise

theorem _root_.GlobalTheory.T.continuous_splitPlaceHermitianFrame_GL_embedding : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] (β : Frame p S n), Continuous β.gl := by
  first | exact @GlobalTheory.FrameCont.continuous_gl | exact GlobalTheory.FrameCont.continuous_gl | (intros; apply GlobalTheory.FrameCont.continuous_gl <;> assumption)
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.VacFlat

variable {D : D7}

theorem smul_mem_latA {S : HSp D} {L : Lat S} {P : Pl D → Prop} {a : D.host.E} (ha : a ∈ D.host.AA)
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) :
    (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * y i) ∈ latA S L P := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, c, hc, x, hx, rfl⟩ := hz
    rw [Set.mem_singleton_iff] at hc
    subst hc
    refine AddSubgroup.subset_closure ⟨β, hβi, hβ, a, ha, x, hx, ?_⟩
    funext i
    simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero =>
    have : (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (0 : Fin S.rank → AE D) i) = 0 := by
      funext i; simp
    rw [this]; exact zero_mem _
  | add z z' _ _ hz hz' =>
    have : (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (z + z') i) =
        (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * z i) + (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * z' i) := by
      funext i; simp [mul_add]
    rw [this]; exact add_mem hz hz'
  | neg z _ hz =>
    have : (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (-z) i) =
        -(fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * z i) := by
      funext i; simp
    rw [this]; exact neg_mem hz

theorem wittCoreInclusion_mem_latticeCompletionAtPlace {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) {L : Lat T} {L₀ : Lat T₀} {v : Pl D}
    (hm : MonoAt d L L₀ v) {u : Fin T₀.rank → AE D} (hu : u ∈ latV T₀ L₀ (· = v)) :
    d.j0 *ᵥ u ∈ latV T L (· = v) := by
  refine (hm _).2 ⟨fun i => ?_, fun i => ?_, ?_⟩
  · have h0 : (d.pX *ᵥ (d.j0 *ᵥ u)) i = 0 := by
      rw [Matrix.mulVec_mulVec, HypDec.pX_j0, Matrix.zero_mulVec]; rfl
    have : colMul d.jX i ((d.pX *ᵥ (d.j0 *ᵥ u)) i) = 0 := by
      funext k; simp [colMul, h0]
    rw [this]; exact zero_mem _
  · have h0 : (d.pY *ᵥ (d.j0 *ᵥ u)) i = 0 := by
      rw [Matrix.mulVec_mulVec, HypDec.pY_j0, Matrix.zero_mulVec]; rfl
    have : colMul d.jY i ((d.pY *ᵥ (d.j0 *ᵥ u)) i) = 0 := by
      funext k; simp [colMul, h0]
    rw [this]; exact zero_mem _
  · rw [Matrix.mulVec_mulVec, HypDec.p0_j0, Matrix.one_mulVec]; exact hu

theorem wittCoreInclusion_mem_latticeCompletionAAScaledAtPlace {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) {L : Lat T} {L₀ : Lat T₀} {v : Pl D}
    (hm : MonoAt d L L₀ v) {z : Fin T₀.rank → AE D} (hz : z ∈ latA T₀ L₀ (· = v)) :
    d.j0 *ᵥ z ∈ latA T L (· = v) := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, a, ha, x, hx, rfl⟩ := hz
    set u : Fin T₀.rank → AE D := fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i) with hu
    have hu' : u ∈ latV T₀ L₀ (· = v) := AddSubgroup.subset_closure ⟨β, hβi, hβ, 1, rfl, x, hx, rfl⟩
    have heq : d.j0 *ᵥ (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i)) =
        fun k => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (d.j0 *ᵥ u) k := by
      funext k
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, hu]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h1 : pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i) =
          ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul]
      rw [h1]; ring
    rw [heq]
    exact smul_mem_latA ha (wittCoreInclusion_mem_latticeCompletionAtPlace d hm hu')
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz

end GlobalTheory.FinPl.VacFlat

namespace GlobalTheory.FinPl.VacFlat

variable {D : D7}

theorem wittExt_wittInc_mem_completed_hom_lattice {S S₀ T T₀ : HSp D} {ρ σ : ℕ} (dS : HypDec S S₀ ρ) (dT : HypDec T T₀ σ) {LS : Lat S}
    {LS₀ : Lat S₀} {LT : Lat T} {LT₀ : Lat T₀} {v : Pl D} (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT)
    (hS₀ : IsSelfDualC S₀ LS₀) (hmS : MonoAt dS LS LS₀ v) (hmT : MonoAt dT LT LT₀ v) {w : WO S₀ T₀}
    (hw : w ∈ latO S₀ T₀ (LS₀ : Set _) (LT₀ : Set _) (· = v)) :
    dS.ext0 T (dT.inc0 S₀ w) ∈ latO S T (LS : Set _) (LT : Set _) (· = v) := by
  have hx := GlobalTheory.FinPl.LatMem.latO_mxAt hw
  refine (GlobalTheory.FinPl.LatMem.mem_latO_iff D S T LS LT hS hT (· = v) _).2 ⟨fun i j => ?_, fun y hy => ?_⟩
  · rw [HypDec.matrixExtendByZero_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, Matrix.mul_apply]
    refine sum_mem fun l _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine sum_mem fun k _ => ?_
    rw [mul_assoc]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (hx k l))
  · change (dT.j0 * w * dS.p0) *ᵥ y ∈ latA T LT (· = v)
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have h1 : dS.p0 *ᵥ y ∈ latV S₀ LS₀ (· = v) := ((hmS y).1 hy).2.2
    exact wittCoreInclusion_mem_latticeCompletionAAScaledAtPlace dT hmT (GlobalTheory.FinPl.LatMem.latO_maps hS₀ hw h1)

theorem wittExt_wittInc_isHalf {S S₀ T T₀ : HSp D} {ρ σ : ℕ} (dS : HypDec S S₀ ρ) (dT : HypDec T T₀ σ) {e : AE D}
    {w : WO S₀ T₀} (hw : IsHalf e w) : IsHalf e (dS.ext0 T (dT.inc0 S₀ w)) := by
  intro i j
  rw [HypDec.matrixExtendByZero_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  conv_rhs => rw [← hw k l]
  ring

end GlobalTheory.FinPl.VacFlat

namespace GlobalTheory.FinPl.VacFlat

theorem flat_vac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (LV : Lat B.V) (LV₀ : Lat B.V₀) (LW : Lat J.W) (LW₀ : Lat J.W₀) (v : Pl D), GoodBF ψ B J LV LV₀ LW LW₀ v → ∀ 𝔉, IsFlatBF s (· = v) 𝔉 → ∀ f, Vac ψ B.V J.W LV LW (· = v) f → Vac ψ B.V₀ J.W₀ LV₀ LW₀ (· = v) (𝔉 f) := by
  intro D ψ ρ B J s LV LV₀ LW LW₀ v hG 𝔉 h𝔉 f hf
  obtain ⟨hθ, h2, hh⟩ := hf
  have hmem : ∀ w ∈ latO B.V₀ J.W₀ (LV₀ : Set _) (LW₀ : Set _) (· = v),
      B.d.ext0 J.W (J.d.inc0 B.V₀ w) ∈ latO B.V J.W (LV : Set _) (LW : Set _) (· = v) := fun w hw =>
    wittExt_wittInc_mem_completed_hom_lattice B.d J.d hG.sdV hG.sdW hG.sdV₀ hG.monoV hG.monoW hw
  refine ⟨h𝔉.Heisenberg₂.theta f hθ, fun w hw => ?_, fun e he w hw hwe => ?_⟩
  · have hx : MxAt (· = v) (2 • w) := fun i j => by
      rw [Matrix.smul_apply]
      exact nsmul_mem (GlobalTheory.FinPl.LatMem.latO_mxAt hw i j) 2
    rw [← h𝔉.Heisenberg₂.core f hθ (2 • w) hx, map_nsmul, map_nsmul, h2 _ (hmem w hw)]
  · rw [← h𝔉.Heisenberg₂.core f hθ w (GlobalTheory.FinPl.LatMem.latO_mxAt hw),
      hh e he _ (hmem w hw) (wittExt_wittInc_isHalf B.d J.d hwe)]

end GlobalTheory.FinPl.VacFlat
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl Matrix

theorem _root_.GlobalTheory.T.mem_homLatticeCompletion_iff_supported_maps : ∀ (D : D7) (S T : HSp D) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ (P : Pl D → Prop) (u : WO S T), u ∈ latO S T (LS : Set _) (LT : Set _) P ↔ MxAt P u ∧ ∀ y ∈ latV S LS P, Matrix.mulVec (show Matrix (Fin T.rank) (Fin S.rank) (AE D) from u) y ∈ latA T LT P := by
  first | exact @GlobalTheory.FinPl.LatMem.mem_latO_iff | exact GlobalTheory.FinPl.LatMem.mem_latO_iff | (intros; apply GlobalTheory.FinPl.LatMem.mem_latO_iff <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.latticeCompletionAtPlaces_mem_completedHermitianLattice : ∀ (D : D7) (S : HSp D) (L : Lat S) (P : Pl D → Prop) (y : Fin S.rank → AE D), y ∈ latV S L P → (fun i => Formalism.IndefR.Lev.swapAE D (finPart D (y i))) ∈ Formalism.L2.Herm.hatL (F := D.host.F) L := by
  first | exact @GlobalTheory.LatVHat.latV_mem_hatL | exact GlobalTheory.LatVHat.latV_mem_hatL | (intros; apply GlobalTheory.LatVHat.latV_mem_hatL <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.besselLineLink_gram_similitude_bijective : ∀ (D : D7) (ρ : ℕ) (B : BesLev D ρ) (L' : HSp D) (ζ' : Fin L'.rank → D.host.E), IsLineVec L' ζ' → ∀ l : Link B L' ζ', l.τᴴ ⬝ (B.L.gram ⬝ l.τ) = (((1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L'.gram ∧ ∀ S : HSp D, Function.Bijective (l.κ S) ∧ ∀ w, l.κ S w ∈ ratMx D S.rank B.L.rank → w ∈ ratMx D L'.rank S.rank := by
  first | exact @GlobalTheory.Unf.LinkGram.link_gram | exact GlobalTheory.Unf.LinkGram.link_gram | (intros; apply GlobalTheory.Unf.LinkGram.link_gram <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.fourierJacobi_measure_unitriangular_coordinates : ∀ (D : D7) (ρ : ℕ) (J : JacLev D ρ) (vU : VolU D ρ) (ν₀ : Measure (radX J.d)) (𝓝₀ : Set (radX J.d)), ν₀.IsHaarMeasure → IsFundamentalDomain ((GQ J.W).subgroupOf (radX J.d)) 𝓝₀ ν₀ → ν₀ 𝓝₀ = 1 → IsClosed ((radX J.d ⊔ J.d.emb0.range : Subgroup (GA D J.W)) : Set (GA D J.W)) ∧ (semiMeas (radX J.d) J.d.emb0 J.v0.μ ν₀).IsHaarMeasure ∧ (semiMeas (radX J.d) J.d.emb0 J.v0.μ ν₀).IsInvInvariant ∧ J.μR.IsInvInvariant ∧ ∀ F : GA D J.W → ENNReal, Measurable F → ∫⁻ r : jacGrp J.d, F r ∂J.μR = ∫⁻ u, ∫⁻ r : (radX J.d ⊔ J.d.emb0.range : Subgroup (GA D J.W)), F (r * J.d.levi u.1) ∂(semiMeas (radX J.d) J.d.emb0 J.v0.μ ν₀) ∂vU.ν := by
  first | exact @GlobalTheory.JacMeas.jac_measure | exact GlobalTheory.JacMeas.jac_measure | (intros; apply GlobalTheory.JacMeas.jac_measure <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

namespace GlobalTheory.Unf.BesSemi

variable {D : D7}

theorem continuous_embA {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) :
    Continuous (embA d o) := by
  have h : (embA d o : GA D A → GA D S) = fun h => d.emb0 (o.emb (h, 1)) := funext fun h => embA_apply d o h
  rw [h]
  exact d.continuous_embed.comp (o.continuous_emb.comp (continuous_id.prodMk continuous_const))

theorem besselCompression_unipotent_mul_embedding {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {n : GA D S} (hn : n ∈ flagN d) (k : GA D S₀) :
    d.p0 * (mt S (n * d.emb0 k) * d.j0) = mt S₀ k := by
  have hflag := (GlobalTheory.BesselChar.mem_NFlag_iff S d.e
    (GlobalTheory.MixPer.Decomp.linInd d) n).1 hn
  have hcols : ∀ j : Fin S₀.rank, ∃ a : Fin ρ → AE D,
      mt S n *ᵥ (fun i => d.j0 i j) = (fun i => d.j0 i j) + d.jX *ᵥ a := by
    intro j
    apply hflag.2
    change d.pY *ᵥ (fun i => d.j0 i j) = 0
    funext i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using
      congrFun (congrFun d.pY_j0 i) j
  choose a ha using hcols
  have h0 : mt S n * d.j0 = d.j0 + d.jX * Matrix.of (fun i j => a j i) := by
    ext i j
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using congrFun (ha j) i
  have hproj : d.p0 * (mt S n * d.j0) = 1 := by
    rw [h0, Matrix.mul_add, d.p0_j0, ← Matrix.mul_assoc, d.p0_jX, Matrix.zero_mul, add_zero]
  rw [mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclAnisotropic,
    ← Matrix.mul_assoc (mt S n), ← Matrix.mul_assoc d.p0, hproj, Matrix.one_mul]

theorem unique {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) {n n' : GA D S}
    (hn : n ∈ flagN d) (hn' : n' ∈ flagN d) {h h' : GA D A} (e : n * embA d o h = n' * embA d o h') :
    n = n' ∧ h = h' := by
  have e0 := congrArg (fun g => d.p0 * (mt S g * d.j0)) e
  rw [embA_apply, embA_apply, besselCompression_unipotent_mul_embedding d hn,
    besselCompression_unipotent_mul_embedding d hn'] at e0
  have hh : h = h' := congrArg Prod.fst (o.emb_injective (mt_injective S₀ e0))
  subst h'
  exact ⟨mul_right_cancel e, rfl⟩

theorem rat_iff {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) {n : GA D S}
    (hn : n ∈ flagN d) (h : GA D A) : n * embA d o h ∈ GQ S ↔ n ∈ GQ S ∧ h ∈ GQ A := by
  constructor
  · intro hg
    have hk : o.emb (h, 1) ∈ GQ S₀ := by
      rw [mem_GQ_iff]
      rw [embA_apply] at hg
      rw [← besselCompression_unipotent_mul_embedding d hn]
      exact ratMx_mul (rat_mem _) (ratMx_mul ((mem_GQ_iff S _).1 hg) (rat_mem _))
    have hA : h ∈ GQ A := by
      rw [mem_GQ_iff]
      have e : o.pA * (mt S₀ (o.emb (h, 1)) * o.jA) = mt A h := by
        rw [o.emb_jA, ← Matrix.mul_assoc, o.pA_jA, Matrix.one_mul]
      rw [← e]
      exact ratMx_mul (rat_mem _) (ratMx_mul ((mem_GQ_iff S₀ _).1 hk) (rat_mem _))
    have he : embA d o h ∈ GQ S := by rw [embA_apply]; exact d.wittDecomp_anisotropicEmbedding_mem_rationalPoints hk
    refine ⟨?_, hA⟩
    have : n = n * embA d o h * (embA d o h)⁻¹ := (mul_inv_cancel_right n _).symm
    rw [this]
    exact mul_mem hg (inv_mem he)
  · rintro ⟨hn', hA⟩
    refine mul_mem hn' ?_
    rw [embA_apply]
    exact d.wittDecomp_anisotropicEmbedding_mem_rationalPoints (o.emb_mem_GQ hA (one_mem _))

end GlobalTheory.Unf.BesSemi

namespace GlobalTheory.Unf

theorem besSemi : ∀ (D : D7) (σ : ℕ) (B : BesLev D σ), Continuous (embA B.d B.o) ∧ IsClosed (flagN B.d : Set (GA D B.V)) ∧ (∀ n ∈ flagN B.d, ∀ h, embA B.d B.o h * n * (embA B.d B.o h)⁻¹ ∈ flagN B.d) ∧ (∀ n ∈ flagN B.d, ∀ n' ∈ flagN B.d, ∀ h h', n * embA B.d B.o h = n' * embA B.d B.o h' → n = n' ∧ h = h') ∧ ∀ n ∈ flagN B.d, ∀ h, n * embA B.d B.o h ∈ GQ B.V ↔ n ∈ GQ B.V ∧ h ∈ GQ B.A := by
  intro D σ B
  refine ⟨BesSemi.continuous_embA B.d B.o, GlobalTheory.Mem.TrueRecord.isClosed_NFlag B.V (isIsoSub_e B.d),
    fun n hn h => ?_, fun n hn n' hn' h h' e => BesSemi.unique B.d B.o hn hn' e,
    fun n hn h => BesSemi.rat_iff B.d B.o hn h⟩
  rw [embA_apply]
  let g := B.d.emb0 (B.o.emb (h, 1))
  have hg : mt B.V g * B.d.e.map (incA D) = B.d.e.map (incA D) :=
    B.d.wittDecomp_anisotropicEmbedding_inclX _
  have hg' := GlobalTheory.BesselChar.inv_fix_cols (mt_inv_mul B.V g) hg
  have hflag := GlobalTheory.BesselChar.mem_NFlag_iff B.V B.d.e
    (GlobalTheory.MixPer.Decomp.linInd B.d)
  change g * n * g⁻¹ ∈ flagN B.d
  apply (hflag _).2
  rw [mt_mul, mt_mul]
  exact ((hflag n).1 hn).conj hg hg' (mt_mul_inv B.V g)
    (GlobalTheory.BesselChar.perp_fixed B.d.e g⁻¹ hg')

end GlobalTheory.Unf
end

section

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop
open Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting GlobalTheory.Core.Rk

noncomputable section

namespace GlobalTheory.MiTop.BotTwo

variable {D : D7}

theorem per_smul_f {ρ : ℕ} (B : BesLev D ρ) (ψ : AddChar (AF D.host.F) ℂ) (φ : GA D B.A → ℂ) (b : ℂ) (f : GA D B.V → ℂ) :
    B.per ψ φ (b • f) = b * B.per ψ φ f := by
  simp only [BesLev.per, besPer, besFun, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext x
  rw [← integral_const_mul]
  congr 1; funext n; ring

theorem contAut_zero (V : HSp D) : IsContAut V (0 : GA D V → ℂ) :=
  ⟨fun _ _ _ => rfl, continuous_const⟩

theorem contAut_add {V : HSp D} {f g : GA D V → ℂ} (hf : IsContAut V f) (hg : IsContAut V g) :
    IsContAut V (f + g) :=
  ⟨fun γ hγ x => by simp only [Pi.add_apply, hf.1 γ hγ x, hg.1 γ hγ x], hf.2.add hg.2⟩

theorem contAut_smul {V : HSp D} {f : GA D V → ℂ} (hf : IsContAut V f) (c : ℂ) : IsContAut V (c • f) :=
  ⟨fun γ hγ x => by simp only [Pi.smul_apply, hf.1 γ hγ x], hf.2.const_smul c⟩

theorem contAut_rTrans {V : HSp D} {f : GA D V → ℂ} (h : GA D V) (hf : IsContAut V f) : IsContAut V (rTrans h f) :=
  ⟨fun γ hγ x => by simp only [rTrans, mul_assoc, hf.1 γ hγ], hf.2.comp (continuous_mul_const h)⟩

theorem contAut_multT {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {J : Set (GA D V)}
    {χ : GA D V → ℂ} {G : SmT M →ₗ[ℂ] (GA D V → ℂ)} (hG : G ∈ MultT θ M J χ) (x : SmT M) : IsContAut V (G x) := by
  obtain ⟨T, hT, rfl⟩ := hG
  induction hT using Submodule.span_induction generalizing x with
  | mem T hT =>
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      rw [map_smul, LinearEquiv.coe_coe, PiTensorProduct.lift.tprod]
      exact contAut_smul ⟨(hT.aut v).left, (hT.aut v).cont⟩ r
    | add x y hx hy => rw [map_add (f := _)]; exact contAut_add hx hy
  | zero => simpa using contAut_zero V
  | add T₁ T₂ _ _ h₁ h₂ => rw [map_add (f := _), LinearMap.add_apply]; exact contAut_add (h₁ x) (h₂ x)
  | smul c T _ h => rw [map_smul, LinearMap.smul_apply]; exact contAut_smul (h x) c

theorem lev_multT {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {J : Set (GA D V)}
    {χ : GA D V → ℂ} {G : SmT M →ₗ[ℂ] (GA D V → ℂ)} (hG : G ∈ MultT θ M J χ) (x : SmT M) {k : GA D V} (hk : k ∈ J)
    (g : GA D V) : G x (g * k) = χ k * G x g := by
  obtain ⟨T, hT, rfl⟩ := hG
  induction hT using Submodule.span_induction generalizing x g with
  | mem T hT =>
    induction x using PiTensorProduct.induction_on generalizing g with
    | smul_tprod r v =>
      rw [map_smul, LinearEquiv.coe_coe, PiTensorProduct.lift.tprod]
      simp only [Pi.smul_apply, smul_eq_mul, hT.lev v k hk g]; ring
    | add x y hx hy => simp only [map_add (f := _), Pi.add_apply, hx, hy]; ring
  | zero => simp
  | add T₁ T₂ _ _ h₁ h₂ => simp only [map_add (f := _), LinearMap.add_apply, Pi.add_apply, h₁, h₂]; ring
  | smul c T _ h => simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, h]; ring

theorem shift_swap {G A B : Type} [Group G] [Group A] [Group B] (ι : G ≃* A × B) (g w : G) (y : A) (x : B)
    (hw : (ι w).1 = 1) : ι.symm (ι g * (y, x)) * w = g * (ι.symm (1, x) * w) * ι.symm (y, 1) := by
  apply ι.injective
  simp only [map_mul, MulEquiv.apply_symm_apply]
  ext
  · simp [hw]
  · simp [mul_assoc]

theorem comb_integral {Y : Type} [MeasurableSpace Y] (ν : Measure Y) (c α α' : ℂ) (F F' : Y → ℂ)
    (h : ∀ y, α * F y + α' * F' y = 0) : α * (c * ∫ y, F y ∂ν) + α' * (c * ∫ y, F' y ∂ν) = 0 := by
  have hI : ∫ y, α * F y ∂ν = ∫ y, -(α' * F' y) ∂ν :=
    integral_congr_ae (Filter.Eventually.of_forall fun y => eq_neg_of_add_eq_zero_left (h y))
  rw [integral_neg, integral_const_mul, integral_const_mul] at hI
  linear_combination c * hI

end GlobalTheory.MiTop.BotTwo


end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.gramMatrixOfColumns_unitriangular_conj_eq : ∀ (D : D7) (W : HSp D) (ρ : ℕ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E), IsBase W x₀ → ∀ u : Matrix (Fin ρ) (Fin ρ) D.host.E, (∀ i, u i i = 1) → (∀ i k, k < i → u i k = 0) → uᴴ * gramQ W x₀ * u = gramQ W x₀ := by
  first | exact @GlobalTheory.Unf.gramQ_unitri | exact GlobalTheory.Unf.gramQ_unitri | (intros; apply GlobalTheory.Unf.gramQ_unitri <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.rational_flagUnipotent_isotropicBlock_unitriangular : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (γ : GA D V), γ ∈ GQ V → γ ∈ flagN d → ∃ u u' : Matrix (Fin ρ) (Fin ρ) D.host.E, (rat u : Mx D ρ ρ) = blockX d γ ∧ u * u' = 1 ∧ u' * u = 1 ∧ (∀ i, u i i = 1) ∧ (∀ i k, k < i → u i k = 0) ∧ ∀ j : Fin ρ, γ ∈ Nfix d j → ∀ i k, k ≤ j → u i k = if i = k then 1 else 0 := by
  exact GlobalTheory.Unf.ratBlock_unitri
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.rational_frames_same_gram_one_unitary_orbit : ∀ (D : D7) (W : HSp D) (ρ : ℕ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E), LinearIndependent D.host.E x₀.transpose → (∀ x ∈ Orb W x₀, ∃ γ ∈ GQ W, mt W γ * (rat x₀ : Mx D W.rank ρ) = rat x) ∧ ∀ γ ∈ GQ W, ∀ x ∈ Orb W x₀, ∃ x' ∈ Orb W x₀, mt W γ * (rat x : Mx D W.rank ρ) = rat x' := by
  first | exact @GlobalTheory.WittOrbit.orb_eq_orbit | exact GlobalTheory.WittOrbit.orb_eq_orbit | (intros; apply GlobalTheory.WittOrbit.orb_eq_orbit <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.unfolding_base_point_fourierJacobi_group : ∀ (D : D7) (W W₀ : HSp D) (ρ : ℕ) (d : HypDec W W₀ ρ), IsBase W d.e ∧ gramQ W d.e = 0 ∧ xZero d = rat d.e ∧ Rgrp W (rat d.e) = jacGrp d ∧ Continuous d.emb0 ∧ ∀ n ∈ flagN d, ∀ h, n * d.emb0 h ∈ GQ W ↔ n ∈ GQ W ∧ h ∈ GQ W₀ := by
  first | exact @GlobalTheory.Unf.base_point | exact GlobalTheory.Unf.base_point | (intros; apply GlobalTheory.Unf.base_point <;> assumption)
end
