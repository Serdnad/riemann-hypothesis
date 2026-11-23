module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
import Formalism.LocalToGlobal.Columns.RowForms
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle354
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1806
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1692
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle042
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle048
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
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaKernelGrowth
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto.ThetaFirstVar

open GlobalTheory.Size

variable {D : D7} {V W : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {χS χT : (AE D)ˣ →* Circle}
  {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {f : WO V W → ℂ}

theorem thetaKO_left_fst (hω : IsWeilDatumO ψ V W χS χT ω) (hf : IsThetaFunO ψ V W f) (h : GA D W) :
    ∀ γ ∈ GQ V, ∀ g, thetaKO ω (γ * g) h f = thetaKO ω g h f := fun γ hγ g => by
  have e : ((γ * g, h) : GA D V × GA D W) = (γ, 1) * (g, h) := by simp
  unfold thetaKO
  rw [e, map_mul]
  exact hω.om_aut γ hγ 1 (one_mem _) _ (hω.om_pres _ _ hf)

theorem thetaKO_continuous_fst (hω : IsWeilDatumO ψ V W χS χT ω) (hf : IsThetaFunO ψ V W f) (h : GA D W) :
    Continuous fun g => thetaKO ω g h f :=
  (hω.om_cont f hf 0).comp (Continuous.prodMk_left h)

theorem thetaKO_modGrowth_fst (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ V W χS χT ω) (hf : IsThetaFunO ψ V W f)
    (h : GA D W) : GlobalTheory.Grow.ModGrowth V fun g => thetaKO ω g h f := by
  obtain ⟨A, d, H⟩ := GlobalTheory.KernelSeminorm.thetaGrowth D V.rank W.rank
  obtain ⟨U, hU, hl⟩ := isTheta_iff_level.1 hf
  obtain ⟨μ, 𝓕, hμ⟩ := exists_isCovolOne V W
  obtain ⟨C, -, hC⟩ := (H V W rfl rfl).real ψ hθ hU
  refine ⟨C * (sobO ψ θ μ 𝓕 d f).toReal * GlobalTheory.Grow.height W h ^ A, A, fun g => ?_⟩
  rw [mul_assoc _ (GlobalTheory.Grow.height W h ^ A), ← mul_pow, mul_comm (GlobalTheory.Grow.height W h)]
  exact (hC χS χT ω hω μ 𝓕 hμ f hl).2 g h

theorem thetaKO_mul_conj_integrableOn : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → ∀ (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν → ∀ (u : WO S T → ℂ) (y : GA D S → ℂ), IsThetaFunO ψ S T u → IsAutFunSm θ S y → IsCuspFun S y → ∀ (a : GA D S) (x : GA D T), IntegrableOn (fun g => thetaKO om g x u * conj (y (g * a))) 𝓕 ν := by
  intro hP D ψ S T χS χT om hω θ hθ ν 𝓕 hν h𝓕 u y hu hy hc a x
  have : BorelSpace (GA D S) := ⟨rfl⟩
  have hR : GlobalTheory.Grow.RapidDec S fun g => conj (y (g * a)) :=
    ((GlobalTheory.Grow.rapidDec_of_cuspForm hP hθ hy hc).mul_right a).conj
  exact hR.integrableOn_modGrowth_mul hν h𝓕 (thetaKO_modGrowth_fst hθ hω hu x) (thetaKO_left_fst hω hu x)
    (thetaKO_continuous_fst hω hu x).measurable.aestronglyMeasurable

end GlobalTheory.ChainOnto.ThetaFirstVar

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto.RightMove

variable {D : D7}

theorem topL_mul {κ : Type} [CommRing κ] {a b : ℕ} (y : Matrix (Fin b) (Fin a) κ) (γ : Matrix (Fin a) (Fin a) κ) :
    topL a (y * γ) = topL a y * γ := by
  ext i j
  by_cases hi : i.val < b
  · simp [topL, Matrix.mul_apply, hi]
  · simp [topL, Matrix.mul_apply, hi]

theorem lowZero_mul {κ : Type} [CommRing κ] {a b : ℕ} {y : Matrix (Fin b) (Fin a) κ} (hy : LowZero a y)
    (γ : Matrix (Fin a) (Fin a) κ) : LowZero a (y * γ) := by
  intro i j hi _
  rw [Matrix.mul_apply]
  exact Finset.sum_eq_zero fun l _ => by rw [hy i l hi l.2, zero_mul]

abbrev Cond {a b : ℕ} (L : LevDat D.host.E ℂ a) (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) : Prop :=
  (∀ PP ∈ L.Pg, LowZero a (y PP)) ∧ ∃ g : ∀ PP : ↥L.Pg, GL (Fin a) (kP PP.1),
    (∀ PP : ↥L.Pg, ((g PP : GL (Fin a) _) : Matrix (Fin a) (Fin a) _) = topL a (y PP.1)) ∧
    (∀ PP : ↥L.Pg, g PP ∈ blockTri (blkOf L.r L.t)) ∧ (fun PP => upperLeftBlock L.hr (g PP)) ∈ L.P.H

theorem cond_mul {a b : ℕ} (L : LevDat D.host.E ℂ a) (γ : ∀ PP : Pl D.host.E, GL (Fin a) (kP PP))
    (hγ : ∀ PP ∈ L.Pg, γ PP ∈ blockTri (blkOf L.r L.t)) (hP : (fun PP : ↥L.Pg => upperLeftBlock L.hr (γ PP.1)) ∈ L.P.H)
    (y z : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) (hz : ∀ PP, z PP = y PP * (γ PP).val)
    (h : Cond L y) : Cond L z := by
  obtain ⟨h1, g, h2, h3, h4⟩ := h
  refine ⟨fun PP hP' => (hz PP).symm ▸ lowZero_mul (h1 PP hP') _, fun PP => g PP * γ PP.1, fun PP => ?_,
    fun PP => mul_mem (h3 PP) (hγ PP.1 PP.2), ?_⟩
  · rw [Units.val_mul, h2, hz, topL_mul]
  · have e : (fun PP : ↥L.Pg => upperLeftBlock L.hr (g PP * γ PP.1)) =
        (fun PP => upperLeftBlock L.hr (g PP)) * (fun PP : ↥L.Pg => upperLeftBlock L.hr (γ PP.1)) := by
      funext PP
      exact extendMatrixByIdentityAlongIndices_mul _ (blockTri_blkOf_le _ _ (h3 PP)) (blockTri_blkOf_le _ _ (hγ PP.1 PP.2))
    rw [e]
    exact mul_mem h4 hP

theorem omegaG_mul_right : ∀ (D : D7) (a b : ℕ) (L : LevDat D.host.E ℂ a) (χ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (G : ∀ PP : Pl D.host.E, GL (Fin a) (kP PP)), (∀ PP ∈ L.Pg, G PP ∈ blockTri (blkOf L.r L.t)) → ∀ hP : (fun PP : ↥L.Pg => upperLeftBlock L.hr (G PP.1)) ∈ L.P.H, ∀ y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP), omegaG L χ (fun PP => y PP * (G PP).val) = ((L.P.chi ⟨_, hP⟩ * (∏ PP ∈ L.Pg, ∏ i ∈ Finset.range L.s, L.cg (i + 1) PP (dBlk (blkOf L.r L.t) (i + 1) (G PP))) * ∏ PP ∈ L.Pg, (χ PP (Matrix.GeneralLinearGroup.det (G PP)))⁻¹ : ℂˣ) : ℂ) * omegaG L χ y := by
  intro D a b L χ G hG hP y
  have hGi : ∀ PP ∈ L.Pg, (G PP)⁻¹ ∈ blockTri (blkOf L.r L.t) := fun PP h => inv_mem (hG PP h)
  have hPi : (fun PP : ↥L.Pg => upperLeftBlock L.hr (G PP.1)⁻¹) ∈ L.P.H := by
    have e : (fun PP : ↥L.Pg => upperLeftBlock L.hr (G PP.1)⁻¹) = (fun PP : ↥L.Pg => upperLeftBlock L.hr (G PP.1))⁻¹ := by
      funext PP
      exact extendOne_inv _ (blockTri_blkOf_le _ _ (hG PP.1 PP.2))
    rw [e]
    exact inv_mem hP
  unfold omegaG
  by_cases hy : Cond L y
  · have hy' : Cond L (fun PP => y PP * (G PP).val) := cond_mul L G hG hP y _ (fun _ => rfl) hy
    rw [dite_eq_left hy', dite_eq_left hy]
    have key : ∀ PP : ↥L.Pg, hy'.2.choose PP = hy.2.choose PP * G PP.1 := fun PP => Units.ext (by
      rw [Units.val_mul, hy'.2.choose_spec.1 PP, hy.2.choose_spec.1 PP, topL_mul])
    have hc : (⟨fun PP => upperLeftBlock L.hr (hy'.2.choose PP), hy'.2.choose_spec.2.2⟩ : L.P.H) =
        ⟨fun PP => upperLeftBlock L.hr (hy.2.choose PP), hy.2.choose_spec.2.2⟩ * ⟨_, hP⟩ :=
      Subtype.ext (funext fun PP => by
        show upperLeftBlock L.hr (hy'.2.choose PP) = upperLeftBlock L.hr (hy.2.choose PP) * upperLeftBlock L.hr (G PP.1)
        rw [key]
        exact extendMatrixByIdentityAlongIndices_mul _ (blockTri_blkOf_le _ _ (hy.2.choose_spec.2.1 PP)) (blockTri_blkOf_le _ _ (hG PP.1 PP.2)))
    have hd : ∀ PP : ↥L.Pg, ∀ c : ℕ, dBlk (blkOf L.r L.t) c (hy'.2.choose PP) =
        dBlk (blkOf L.r L.t) c (hy.2.choose PP) * dBlk (blkOf L.r L.t) c (G PP.1) := fun PP c => by
      rw [key]; exact diag_block_det_mul (hy.2.choose_spec.2.1 PP) (hG PP.1 PP.2)
    rw [hc, map_mul]
    simp only [hd]
    simp only [key, map_mul, Units.val_mul, mul_inv, Finset.prod_mul_distrib, Units.val_inv_eq_inv_val, Units.coe_prod]
    rw [← Finset.prod_coe_sort L.Pg (fun PP => ((χ PP (Matrix.GeneralLinearGroup.det (G PP)) : ℂˣ) : ℂ)⁻¹),
      ← Finset.prod_coe_sort L.Pg (fun PP => ∏ i ∈ Finset.range L.s, ((L.cg (i + 1) PP (dBlk (blkOf L.r L.t) (i + 1) (G PP)) : ℂˣ) : ℂ))]
    ring
  · have hy' : ¬ Cond L (fun PP => y PP * (G PP).val) := fun h => hy (cond_mul L (fun PP => (G PP)⁻¹) hGi hPi _ y
      (fun PP => by rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]) h)
    rw [dite_eq_right hy', dite_eq_right hy, mul_zero]

end GlobalTheory.ChainOnto.RightMove
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockFiniteHeis

variable {D : D7}

theorem foldr_lin {ι X : Type} (p : (X → ℂ) → Prop) (A : ι → (X → ℂ) → (X → ℂ))
    (hp : ∀ i f, p f → p (A i f)) (hadd : ∀ i f g, p f → p g → A i (f + g) = A i f + A i g)
    (hsmul : ∀ i (c : ℂ) f, p f → A i (c • f) = c • A i f) (padd : ∀ f g, p f → p g → p (f + g))
    (psmul : ∀ (c : ℂ) f, p f → p (c • f)) (c : ℂ) {f g : X → ℂ} (hf : p f) (hg : p g) (l : List ι) :
    l.foldr (fun i h => A i h) (c • f + g) = c • l.foldr (fun i h => A i h) f + l.foldr (fun i h => A i h) g := by
  have hm : ∀ l : List ι, p (l.foldr (fun i h => A i h) f) ∧ p (l.foldr (fun i h => A i h) g) := by
    intro l
    induction l with
    | nil => exact ⟨hf, hg⟩
    | cons i l ih => exact ⟨hp i _ ih.1, hp i _ ih.2⟩
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [List.foldr_cons, List.foldr_cons, List.foldr_cons, ih, hadd i _ _ (psmul c _ (hm l).1) (hm l).2,
      hsmul i c _ (hm l).1]

theorem pureTensorO_lin (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (hψ : IsStdChar D ψ (-1))
    (hθ : IsInfFam θ) (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (c : ℂ) {f g : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) (φ : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    pureTensorO ψ θ S T sS sT BS BT (c • f + g) φ =
      c • pureTensorO ψ θ S T sS sT BS BT f φ + pureTensorO ψ θ S T sS sT BS BT g φ := by
  have theta_add {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) :
      IsThetaFunO ψ S T (f + g) := by
    refine {
        quasi γ w := by simp only [Pi.add_apply, hf.quasi, hg.quasi, mul_add]
        level := by
          obtain ⟨U, hU, h1⟩ := hf.level
          obtain ⟨U', hU', h2⟩ := hg.level
          refine ⟨U ⊓ U', hU.inter hU', fun u hu h0 => ?_⟩
          funext w
          have e1 := congrFun (h1 u hu.1 h0) w
          have e2 := congrFun (h2 u hu.2 h0) w
          unfold heisO at e1 e2 ⊢
          rw [Pi.add_apply, Pi.add_apply, mul_add, e1, e2]
        cont := hf.cont.add hg.cont
        smooth k L h1 h2 w := (hf.smooth k L h1 h2 w).add (hg.smooth k L h1 h2 w)

    }
  have theta_smul (c : ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (c • f) := by
    refine {
        quasi γ w := by
          rw [Pi.smul_apply, Pi.smul_apply, hf.quasi, smul_eq_mul, smul_eq_mul, mul_left_comm]
        level := by
          obtain ⟨U, hU, h1⟩ := hf.level
          refine ⟨U, hU, fun u hu h0 => ?_⟩
          funext w
          have e1 := congrFun (h1 u hu h0) w
          unfold heisO at e1 ⊢
          rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm, e1]
        cont := hf.cont.const_smul c
        smooth k L h1 h2 w := contDiff_const.mul (hf.smooth k L h1 h2 w)
    }
  have h : pureTensorO ψ θ S T sS sT BS BT (c • f + g) =
      c • pureTensorO ψ θ S T sS sT BS BT f + pureTensorO ψ θ S T sS sT BS BT g := by
    refine (MvPolynomial.basisMonomials _ ℂ).ext fun k => ?_
    rw [LinearMap.add_apply, LinearMap.smul_apply]
    unfold pureTensorO pureTensorL
    rw [Module.Basis.constr_basis, Module.Basis.constr_basis, Module.Basis.constr_basis]
    unfold opPow
    have A1 : ∀ k f, IsThetaFunO ψ S T f →
        IsThetaFunO ψ S T (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT k f) :=
      fun k f hf => GlobalTheory.FockIndep.aPlus_theta hψ hθ k.1 (cplxO (sS k.1) (sT k.1)) _ hf
    have A2 : ∀ k f g, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g →
        aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT k (f + g) =
          aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT k f +
            aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT k g :=
      fun k f g hf hg => GlobalTheory.FockIndep.aPlus_add hψ hθ k.1 (cplxO (sS k.1) (sT k.1)) _ hf hg
    have A3 : ∀ k (c : ℂ) f, IsThetaFunO ψ S T f →
        aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT k (c • f) =
          c • aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT k f :=
      fun k c f hf => GlobalTheory.FockIndep.aPlus_smul hψ hθ k.1 (cplxO (sS k.1) (sT k.1)) _ c hf
    exact foldr_lin (IsThetaFunO ψ S T) (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT) A1 A2 A3
      (fun _ _ hf hg => theta_add hf hg) (fun c _ hf => theta_smul c hf) c hf hg _
  rw [h, LinearMap.add_apply, LinearMap.smul_apply]

end GlobalTheory.FockFiniteHeis

namespace GlobalTheory.FockFiniteHeis

theorem pureTensorO_zero {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (hψ : IsStdChar D ψ (-1))
    (hθ : IsInfFam θ) (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (φ : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    pureTensorO ψ θ S T sS sT BS BT (0 : WO S T → ℂ) φ = 0 := by
  have theta_zero : IsThetaFunO ψ S T 0 := by
    refine {
        quasi γ w := by simp only [Pi.zero_apply, mul_zero]
        level := ⟨⊤, isOpen_univ, fun u _ _ => by funext w; simp only [heisO, Pi.zero_apply, mul_zero]⟩
        cont := continuous_const
        smooth k L _ _ w := contDiff_const

    }
  have h := pureTensorO_lin ψ θ S T hψ hθ sS BS sT BT (-1) theta_zero theta_zero φ
  rwa [smul_zero, add_zero, neg_one_smul, neg_add_cancel] at h

theorem heis_comb_pureTensorO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ sS sT BS BT (f : WO S T → ℂ), IsThetaFunO ψ S T f → ∀ (n : ℕ) (a : Fin n → ℂ) (y : Fin n → WO S T), (∀ i, (y i).map (infPart D) = 0) → ∀ φ, ∑ i, a i • heisO ψ S T (y i) (pureTensorO ψ θ S T sS sT BS BT f φ) = pureTensorO ψ θ S T sS sT BS BT (∑ i, a i • heisO ψ S T (y i) f) φ ∧ pureTensorO ψ θ S T sS sT BS BT (0 : WO S T → ℂ) φ = 0 := by
  intro D ψ θ S T hψ hθ sS sT BS BT f hf n a y hy φ
  have theta_zero : IsThetaFunO ψ S T 0 := by
    refine {
        quasi γ w := by simp only [Pi.zero_apply, mul_zero]
        level := ⟨⊤, isOpen_univ, fun u _ _ => by funext w; simp only [heisO, Pi.zero_apply, mul_zero]⟩
        cont := continuous_const
        smooth k L _ _ w := contDiff_const

    }
  have theta_add {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) :
      IsThetaFunO ψ S T (f + g) := by
    refine {
        quasi γ w := by simp only [Pi.add_apply, hf.quasi, hg.quasi, mul_add]
        level := by
          obtain ⟨U, hU, h1⟩ := hf.level
          obtain ⟨U', hU', h2⟩ := hg.level
          refine ⟨U ⊓ U', hU.inter hU', fun u hu h0 => ?_⟩
          funext w
          have e1 := congrFun (h1 u hu.1 h0) w
          have e2 := congrFun (h2 u hu.2 h0) w
          unfold heisO at e1 e2 ⊢
          rw [Pi.add_apply, Pi.add_apply, mul_add, e1, e2]
        cont := hf.cont.add hg.cont
        smooth k L h1 h2 w := (hf.smooth k L h1 h2 w).add (hg.smooth k L h1 h2 w)

    }
  have theta_smul (c : ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (c • f) := by
    refine {
        quasi γ w := by
          rw [Pi.smul_apply, Pi.smul_apply, hf.quasi, smul_eq_mul, smul_eq_mul, mul_left_comm]
        level := by
          obtain ⟨U, hU, h1⟩ := hf.level
          refine ⟨U, hU, fun u hu h0 => ?_⟩
          funext w
          have e1 := congrFun (h1 u hu h0) w
          unfold heisO at e1 ⊢
          rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm, e1]
        cont := hf.cont.const_smul c
        smooth k L h1 h2 w := contDiff_const.mul (hf.smooth k L h1 h2 w)
    }
  have ft := GlobalTheory.FinTranslate.finite_translate D ψ θ S T hψ hθ f hf
  have hth : ∀ i, IsThetaFunO ψ S T (heisO ψ S T (y i) f) := fun i => (ft.2 (y i) (hy i)).1
  have key : ∀ s : Finset (Fin n), IsThetaFunO ψ S T (∑ i ∈ s, a i • heisO ψ S T (y i) f) ∧
      pureTensorO ψ θ S T sS sT BS BT (∑ i ∈ s, a i • heisO ψ S T (y i) f) φ =
        ∑ i ∈ s, a i • pureTensorO ψ θ S T sS sT BS BT (heisO ψ S T (y i) f) φ := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      exact ⟨theta_zero, pureTensorO_zero ψ θ S T hψ hθ sS BS sT BT φ⟩
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      refine ⟨theta_add (theta_smul _ (hth i)) ih.1, ?_⟩
      rw [pureTensorO_lin ψ θ S T hψ hθ sS BS sT BT (a i) (hth i) ih.1 φ, ih.2]
  refine ⟨?_, pureTensorO_zero ψ θ S T hψ hθ sS BS sT BT φ⟩
  rw [(key Finset.univ).2]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(ft.2 (y i) (hy i)).2 sS BS sT BT φ]

end GlobalTheory.FockFiniteHeis

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto

theorem coef_zero_of_heis_relations : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (m : Measure (WO S T)) (X : Set (WO S T)), IsCovolOne (ratL T S) m X → ∀ F : WO S T → ℂ, IsThetaFunO ψ S T F → ∀ (g : GA D S) (n : ℕ) (a : Fin n → ℂ) (y : Fin n → WO S T), ∑ i, a i • heisO ψ S T (y i) F = F → ∑ i, conj (a i) • heisO ψ S T (actO S T g⁻¹ 1 (-(y i))) F = 0 → ∫ w in X, om (g, 1) F w * conj (F w) ∂m = 0 := by
  intro D ψ S T χS χT om hw m X hm F hF g n a y h1 h2
  have hψ := hw.std
  have hth := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1
  have laws := fun {u v : WO S T → ℂ} (hu : IsThetaFunO ψ S T u) (hv : IsThetaFunO ψ S T v) =>
    GlobalTheory.ThetaPairingLaws.ipO_laws D ψ S T m X hψ hm u v hu hv
  have hG : IsThetaFunO ψ S T (om (g, 1) F) := hw.om_pres _ F hF

  have key : ∀ i, (∫ x in X, om (g, 1) F x * conj (heisO ψ S T (y i) F x) ∂m) =
      ∫ x in X, om (g, 1) (heisO ψ S T (actO S T g⁻¹ 1 (-(y i))) F) x * conj (F x) ∂m := by
    intro i
    have hact : actO S T g 1 (actO S T g⁻¹ 1 (-(y i))) = -(y i) := by
      have := GlobalTheory.AdelicLatMove.actO_actO_inv S T g 1 (-(y i))
      rwa [inv_one] at this
    rw [hw.om_heis g 1 _ F hF, hact]
    have := ((laws hG hF).2.2.2.2.2.2.1 (-(y i))).2
    rw [neg_neg] at this
    exact this.symm
  have hpt : ∀ x, om (g, 1) F x * conj (F x) =
      ∑ i, conj (a i) * (om (g, 1) F x * conj (heisO ψ S T (y i) F x)) := by
    intro x
    have e := congrFun h1 x
    rw [Finset.sum_apply] at e
    conv_lhs => rw [← e]

    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    ring
  have hz : ∀ x, om (g, 1) (∑ i, conj (a i) • heisO ψ S T (actO S T g⁻¹ 1 (-(y i))) F) x * conj (F x) =
      ∑ i, conj (a i) * (om (g, 1) (heisO ψ S T (actO S T g⁻¹ 1 (-(y i))) F) x * conj (F x)) := by
    intro x

    rw [map_sum, Finset.sum_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
  calc (∫ x in X, om (g, 1) F x * conj (F x) ∂m)
      = ∫ x in X, ∑ i, conj (a i) * (om (g, 1) F x * conj (heisO ψ S T (y i) F x)) ∂m :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = ∑ i, conj (a i) * ∫ x in X, om (g, 1) F x * conj (heisO ψ S T (y i) F x) ∂m := by
        rw [integral_finsetSum _ (fun i _ => ((laws hG (hth _ F hF)).1).const_mul _)]
        exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
    _ = ∑ i, conj (a i) * ∫ x in X, om (g, 1) (heisO ψ S T (actO S T g⁻¹ 1 (-(y i))) F) x * conj (F x) ∂m :=
        Finset.sum_congr rfl fun i _ => by rw [key i]
    _ = ∫ x in X, ∑ i, conj (a i) * (om (g, 1) (heisO ψ S T (actO S T g⁻¹ 1 (-(y i))) F) x * conj (F x)) ∂m := by
        rw [integral_finsetSum _ (fun i _ => ((laws (hw.om_pres _ _ (hth _ F hF)) hF).1).const_mul _)]
        exact Finset.sum_congr rfl fun i _ => (integral_const_mul _ _).symm
    _ = ∫ x in X, om (g, 1) (∑ i, conj (a i) • heisO ψ S T (actO S T g⁻¹ 1 (-(y i))) F) x * conj (F x) ∂m :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => (hz x).symm)
    _ = 0 := by simp [h2]

end GlobalTheory.ChainOnto

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem mult_equiv_real : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (Sp : D.what₂.Tau → SPar) (M : DSModel V Sp) (J : Set (GA D V)) (χ : GA D V → ℂ), IsInfFam θ → ∀ (v : M.Vec) (b : GinfC V), ∃ w : M.Vec, (∀ τ, (w τ : M.H τ) = M.rep τ (infMat D.sp.cm.sig V.gram (θ τ) (b : GA D V)) (v τ : M.H τ)) ∧ ∀ U ∈ Mult θ M J χ, U w = rTr V (b : GA D V) (U v) := by
  intro D θ V Sp M J χ hθ v b
  classical
  let g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ := fun τ => infMat D.sp.cm.sig V.gram (θ τ) (b : GA D V)
  have hg : ∀ τ, g τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := fun τ =>
    GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V (b : GA D V) τ
  have hsm : ∀ τ, M.rep τ (g τ) (v τ : M.H τ) ∈ M.sm τ := fun τ =>
    GlobalTheory.SmoothStable.rep_mem_sm D V Sp M τ (g τ) (hg τ) _ (v τ).2
  have hb : GlobalTheory.AdelicScalar.realElt θ V g = (b : GA D V) := by
    have hR := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V
    refine hR.2.2.1 _ (GlobalTheory.RealLift.prodAt_mem θ V _ g) _ b.2 fun τ => ?_
    have e := GlobalTheory.RealLift.infMat_prodAt hθ V (u := g) hg τ _ (Finset.nodup_toList Finset.univ)
    rw [if_pos (Finset.mem_toList.2 (Finset.mem_univ _))] at e
    exact e
  refine ⟨fun τ => ⟨_, hsm τ⟩, fun τ => rfl, fun U hU => ?_⟩
  rw [GlobalTheory.RealEquiv.mult_realElt D V Sp θ M J χ U hU g hg v _ (fun τ => rfl), hb]

end GlobalTheory.ChainOnto
end
