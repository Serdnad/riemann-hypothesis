module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NegMulCCancel
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CornerBZero
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle108
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RatioBound
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSettingBis
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.WaveDiffForm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle178
public import Formalism.HermitianCurvature.StatementU
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CornerBlockActionInvariant
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormRankZeroApply
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle201
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpNormPiLe
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.StrictUpperNeg
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle034
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.SliceIntegralLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants
open Formalism.FourierDecayAlt.P.LeftFubiniLemmas

section fubini

variable {k p ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def psiH {p : ℕ} (σ : Equiv.Perm (Fin p)) (v : U.LW σ → ℂ) : ℂ := G.psi U.betaU (U.subS (lhOf σ v))

theorem volume_empty_blocks_real (p : ℕ) : (volume : Measure ((Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ))).real Set.univ = 1 := by
  rw [Measure.volume_eq_prod, measureReal_def, ← Set.univ_prod_univ, Measure.prod_prod]
  rw [volume_pi, volume_pi, Measure.pi_univ, Measure.pi_univ]
  simp [volume_pi, Measure.pi_univ]

def regroup (σ : Equiv.Perm (Fin p)) :
    XL k p ρ σ ≃ᵐ PBQ.XP k p ρ × ((Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ)) × (U.LW σ → ℂ) :=
  MeasurableEquiv.prodAssoc.symm

theorem regroup_apply (σ : Equiv.Perm (Fin p)) (x : XL k p ρ σ) : regroup σ x = ((x.1, x.2.1), x.2.2) := rfl

theorem regroup_mp (Bj : B.RealPlaceData k ρ Wp Wq) (σ : Equiv.Perm (Fin p)) :
    MeasurePreserving (regroup σ) (muL Bj σ)
      ((PBQ.muXP Bj).prod ((volume : Measure ((Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ))).prod
        (volume : Measure (U.LW σ → ℂ)))) := by
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarN
  have := Formalism.FourierDecayAlt.P.Dx2.SplitF.sf_RC (k := k) p ρ
  exact (measurePreserving_prodAssoc (Bj.μW.prod Bj.μN) (U.muRC k p ρ)
    ((volume : Measure ((Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ))).prod (volume : Measure (U.LW σ → ℂ)))).symm

def fH (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k (p + ρ) Wp Wq) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ)
    (H : B.Mat k (p + ρ) → (Wq →L[ℂ] Wp)) (g : B.Mat k ρ)
    (q : PBQ.XP k p ρ × ((Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ)) × (U.LW σ → ℂ)) : Wq →L[ℂ] Wp :=
  psiH σ q.2.2 • PBQ.pbI Bj B0 rfl H (U.mMap k p ρ (lhOf σ q.2.2 * U.hMat σ d) g) q.1

theorem ellL_eq (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k (p + ρ) Wp Wq) (σ : Equiv.Perm (Fin p))
    (d : Fin p → ℂ) (H : B.Mat k (p + ρ) → (Wq →L[ℂ] Wp)) (g : B.Mat k ρ) (x : XL k p ρ σ) (hx : GoodL Bj σ x) :
    ellL Bj σ x (PBG.Kr B0 H (sxL Bj σ x * U.mMap k p ρ (U.hMat σ d) g)) = fH Bj B0 σ d H g (regroup σ x) := by
  have hP : PBQ.GoodP Bj (x.1, x.2.1) := hx
  have hs : sxL Bj σ x * U.mMap k p ρ (U.hMat σ d) g =
      D.castM rfl (PBQ.sP Bj (x.1, x.2.1)) * U.mMap k p ρ (lhOf σ x.2.2.2 * U.hMat σ d) g := by
    rw [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl, sxL, if_pos hx, PBQ.sP, if_pos hP]
    have e := embedding_map_lower_unipotent k p ρ (lhOf σ x.2.2.2) (U.hMat σ d) 1 g (lh_unit σ x.2.2.2)
    rw [Matrix.mul_one, Formalism.FourierDecayAlt.P.PBM.muP_one, Matrix.mul_one] at e
    rw [e]
    have e2 := embedded_group_measure_preserving k p ρ ((Matrix.of x.1.1 : B.Mat k ρ)⁻¹ * (Matrix.of x.1.2 : B.Mat k ρ)⁻¹)
      ((lhOf σ x.2.2.2)ᴴ⁻¹)
    simp only [Matrix.mul_assoc] at e2 ⊢
    rw [← Matrix.mul_assoc (U.muP k p ρ _) (U.embG k p ρ _), ← e2, Matrix.mul_assoc]
  rw [hs, regroup_apply]
  unfold fH ellL PBQ.pbI cL PBQ.cP psiH
  simp only [_root_.smul_apply, ContinuousLinearMap.compL_apply, smul_smul]
  congr 1
  ring

variable [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem jfSliceInt (hp : 1 ≤ p) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0)
    (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k (p + ρ) Wp Wq) (hz' : B0.z' = liftVec k p ρ Bj.z')
    (hπ' : ∀ y : B.Mat k ρ, Bj.π' y = B0.π' (U.embG k p ρ y)) (hW' : Bj.μW' Set.univ = 1)
    (hW0' : B0.μW' = Bj.μW'.map (Formalism.FourierDecayAlt.P.PBM.levMt p ρ rfl)) (hNj : Bj.μN = D.muN k ρ)
    (hN0 : B0.μN = D.muN k (p + ρ))
    (g : B.Mat k ρ) (hg : g ∈ JF.Om k ρ Bj.z Bj.z') (H : B.Mat k (p + ρ) → (Wq →L[ℂ] Wp))
    (hHc : ContinuousOn H {x | x ∈ B.GV k (p + ρ) ∧ U.DjU k p ρ x ≠ 0}) (R : ℝ)
    (hR : ∀ x ∈ B.GV k (p + ρ), H x ≠ 0 → B.gN x ≤ R) :
    Integrable (fun v : U.LW σ → ℂ => psiH σ v • PBQ.pbF Bj B0 rfl H (U.mMap k p ρ (lhOf σ v * U.hMat σ d) g))
        volume ∧
      B.JF Bj (U.PhiFun (s := 0) k ρ σ d (liftVec k p ρ Bj.z) (liftVec k p ρ Bj.z') H (fun a => a.elim0)) g =
        ∫ v : U.LW σ → ℂ, psiH σ v • PBQ.pbF Bj B0 rfl H (U.mMap k p ρ (lhOf σ v * U.hMat σ d) g) := by
  obtain ⟨hint, hJ⟩ := core_lf hp σ d hd Bj B0 hz' hπ' hW' hW0' hNj hN0 g hg H hHc R hR
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarN
  have := Formalism.FourierDecayAlt.P.Dx2.SplitF.sf_RC (k := k) p ρ
  have hsf : SigmaFinite (PBQ.muXP (p := p) Bj) := by unfold PBQ.muXP; infer_instance
  have hae : (fun x => ellL Bj σ x (PBG.Kr B0 H (sxL Bj σ x * U.mMap k p ρ (U.hMat σ d) g))) =ᵐ[muL Bj σ]
      fun x => fH Bj B0 σ d H g (regroup σ x) := by
    filter_upwards [ae_goodL Bj σ] with x hx
    exact ellL_eq Bj B0 σ d H g x hx
  have mp := regroup_mp Bj σ
  have hint2 : Integrable (fH Bj B0 σ d H g)
      ((PBQ.muXP Bj).prod ((volume : Measure ((Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ))).prod
        (volume : Measure (U.LW σ → ℂ)))) :=
    (mp.integrable_comp_emb (regroup σ).measurableEmbedding).1 ((hint.congr hae))
  have hJ2 : B.JF Bj (U.PhiFun (s := 0) k ρ σ d (liftVec k p ρ Bj.z) (liftVec k p ρ Bj.z') H (fun a => a.elim0)) g =
      ∫ q, fH Bj B0 σ d H g q ∂((PBQ.muXP Bj).prod ((volume : Measure ((Fin 0 → Fin p → ℂ) ×
        (Fin p → Fin 0 → ℂ))).prod (volume : Measure (U.LW σ → ℂ)))) := by
    rw [hJ, integral_congr_ae hae, mp.integral_comp' (fH Bj B0 σ d H g)]
  have hin : ∀ c : ((Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ)) × (U.LW σ → ℂ),
      ∫ xP, fH Bj B0 σ d H g (xP, c) ∂(PBQ.muXP Bj) =
        psiH σ c.2 • PBQ.pbF Bj B0 rfl H (U.mMap k p ρ (lhOf σ c.2 * U.hMat σ d) g) := by
    intro c
    unfold fH PBQ.pbF
    exact integral_smul (psiH σ c.2) _
  have hR1 := hint2.integral_prod_right
  simp only [hin] at hR1
  have hR2 := hR1.integral_prod_right
  simp only [integral_const, volume_empty_blocks_real, one_smul] at hR2
  refine ⟨hR2, ?_⟩
  rw [hJ2, integral_prod_symm _ hint2]
  simp only [hin]
  rw [integral_fun_snd (fun v : U.LW σ → ℂ => psiH σ v • PBQ.pbF Bj B0 rfl H (U.mMap k p ρ (lhOf σ v * U.hMat σ d) g)),
    volume_empty_blocks_real, one_smul]

end fubini

end Formalism.FourierDecayAlt.P.SliceIntegralLemmas

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

theorem slice_integral_jacobian_factor {k p ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (hp : 1 ≤ p) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0)
    (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k (p + ρ) Wp Wq) (hz' : B0.z' = liftVec k p ρ Bj.z')
    (hπ' : ∀ y : B.Mat k ρ, Bj.π' y = B0.π' (U.embG k p ρ y)) (hW' : Bj.μW' Set.univ = 1)
    (hW0' : B0.μW' = Bj.μW'.map (Formalism.FourierDecayAlt.P.PBM.levMt p ρ rfl)) (hNj : Bj.μN = D.muN k ρ)
    (hN0 : B0.μN = D.muN k (p + ρ))
    (g : B.Mat k ρ) (hg : g ∈ JF.Om k ρ Bj.z Bj.z') (H : B.Mat k (p + ρ) → (Wq →L[ℂ] Wp))
    (hHc : ContinuousOn H {x | x ∈ B.GV k (p + ρ) ∧ U.DjU k p ρ x ≠ 0}) (R : ℝ)
    (hR : ∀ x ∈ B.GV k (p + ρ), H x ≠ 0 → B.gN x ≤ R) :
    Integrable (fun v : U.LW σ → ℂ =>
        G.psi U.betaU (U.subS (LeftFubiniLemmas.lhOf σ v)) • PBQ.pbF Bj B0 rfl H (U.mMap k p ρ (LeftFubiniLemmas.lhOf σ v * U.hMat σ d) g))
        volume ∧
      B.JF Bj (U.PhiFun (s := 0) k ρ σ d (liftVec k p ρ Bj.z) (liftVec k p ρ Bj.z') H (fun a => a.elim0)) g =
        ∫ v : U.LW σ → ℂ,
          G.psi U.betaU (U.subS (LeftFubiniLemmas.lhOf σ v)) • PBQ.pbF Bj B0 rfl H (U.mMap k p ρ (LeftFubiniLemmas.lhOf σ v * U.hMat σ d) g) :=
  SliceIntegralLemmas.jfSliceInt hp σ d hd Bj B0 hz' hπ' hW' hW0' hNj hN0 g hg H hHc R hR

end Formalism.FourierDecayAlt.P
end
end

section

namespace Formalism.FourierDecayAlt.P.LiftDegreeLemmas

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField Formalism.FourierDecayAlt.P.PBL
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

section blockL

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

def uS (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (v : Fin S.f) (ε : ℝ) (j : ℕ)
    (hj : j ≤ S.G.r) (w : List C.Letter) (Y : Finset C.LPt) (blk : ℕ × ℂ) (h : C.LPt) :
    Wd.Ix (Fin w.length) → B.Mat S.G.k (S.G.r - j) → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)) :=
  uY S p F v ε j hj w (Y.image fun h => h ++ [blk]) (h ++ [blk])

theorem uS_mem (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (v : Fin S.f) (ε : ℝ) (j : ℕ)
    (hj : j ≤ S.G.r) (w : List C.Letter) (Y : Finset C.LPt) (blk : ℕ × ℂ) (h : C.LPt) (hh : h ∈ Y) :
    uS S p F v ε j hj w Y blk h = uB S p F v ε j hj w (h ++ [blk]) :=
  uY_mem S p F v ε j hj w _ _ (Finset.mem_image_of_mem _ hh)

theorem glob_pos' (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) : 0 < S.G.g ∧ 0 < S.G.ka := by
  obtain ⟨hg1, hg2, -⟩ := hB
  refine ⟨by unfold Sz.Glob.g; exact_mod_cast Nat.mul_pos hg1 hg2, ?_⟩
  unfold Sz.Glob.ka; rw [S.hv]; exact div_pos Real.pi_pos (by linarith [PBD.rd_pos' E])

theorem prod_ofFn_map' {K : ℕ} (g0 : Fin K → ℝ) (g : ℝ → ℝ) : ((List.ofFn g0).map g).prod = ∏ c, g (g0 c) := by
  rw [List.map_ofFn, List.prod_ofFn]; rfl

end blockL

end

end Formalism.FourierDecayAlt.P.LiftDegreeLemmas
end

section

noncomputable section

namespace Formalism.FourierDecayAlt.P.StandardPairingDecay

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section one

variable {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem waveL_sub_one_ccle (Bs : B.RealPlaceData k ρ Wp Wq) (w : List C.Letter) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ σ : ℂ, ‖σ‖ ≤ 2 → ∀ (A : ℝ) (x : Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) (c : ℝ),
      (∀ e, B.CCle (A + ((m + 1 : ℕ) : ℝ)) m (x e) c) →
      ∀ e, B.CCle A m (((PBO.waveL Bs σ w - 1) x) e) (K * ‖σ‖ * c) := by
  have uInv_ccle (A : ℝ) (m : ℕ) (σ : ℂ) (hσ : ‖σ‖ ≤ 2) :
      ∀ (w : List C.Letter) (x : Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) (c : ℝ),
        (∀ e, B.CCle A m (x e) c) → ∀ e,
        B.CCle A m (KB.uInv σ w x e) (3 ^ w.length * c) ∧
        B.CCle A m (fun g => KB.uInv σ w x e g - x e g) (3 ^ w.length * ‖σ‖ * c) := by
    intro w
    induction w with
    | nil =>
      intro x c hx e
      have hc : 0 ≤ c := JCx2.pd_ccle_nonneg (hx e)
      refine ⟨by simpa [KB.uInv] using hx e, ?_⟩
      simp only [KB.uInv, sub_self, List.length_nil, pow_zero, one_mul]
      exact JCx2.pd_ccle_mono_c BetaSesquilinearity.CCle_zero (by positivity)
    | cons l w ih =>
      intro x c hx e
      have hc : 0 ≤ c := JCx2.pd_ccle_nonneg (hx e)
      have ih0 := ih (fun e' => x (Fin.cons (0 : Fin 2) e')) c (fun e' => hx _) (fun a => e a.succ)
      have ih1 := ih (fun e' => x (Fin.cons (1 : Fin 2) e')) c (fun e' => hx _) (fun a => e a.succ)
      have hs : ‖(if l.1 then σ else (starRingEnd ℂ) σ)‖ = ‖σ‖ := (by cases l.1 <;> simp)
      have h3 : (0 : ℝ) ≤ 3 ^ w.length := by positivity
      have hσ0 : 0 ≤ ‖σ‖ := norm_nonneg _
      have hlen : (l :: w).length = w.length + 1 := rfl
      have hce : e = Fin.cons (e 0) (fun a => e a.succ) := (Fin.cons_self_tail e).symm
      have hp : (3 : ℝ) ^ (l :: w).length = 3 * 3 ^ w.length := by rw [hlen, pow_succ, mul_comm]
      simp only [KB.uInv]
      by_cases he : e 0 = 0
      · rw [if_pos he]
        have hxe : x e = x (Fin.cons (0 : Fin 2) (fun a => e a.succ)) := by
          conv_lhs => rw [hce, he]
        refine ⟨JCx2.pd_ccle_mono_c ih0.1 (by rw [hp]; nlinarith), ?_⟩
        rw [hxe]
        exact JCx2.pd_ccle_mono_c ih0.2 (by rw [hp]; nlinarith [mul_nonneg h3 hσ0])
      · rw [if_neg he]
        have he1 : e 0 = 1 := by
          rcases Fin.exists_fin_two.1 ⟨e 0, rfl⟩ with h | h
          · exact absurd h he
          · exact h
        have hxe : x e = x (Fin.cons (1 : Fin 2) (fun a => e a.succ)) := by
          conv_lhs => rw [hce, he1]
        refine ⟨?_, ?_⟩
        · have := BetaSesquilinearity.CCle_add ih1.1 (BetaSesquilinearity.CCle_smul (if l.1 then σ else (starRingEnd ℂ) σ) ih0.1)
          rw [hs] at this
          exact JCx2.pd_ccle_mono_c (show B.CCle A m ((KB.uInv σ w (fun e' => x (Fin.cons (1 : Fin 2) e')) (fun a => e a.succ)) +
            (if l.1 then σ else (starRingEnd ℂ) σ) • KB.uInv σ w (fun e' => x (Fin.cons (0 : Fin 2) e')) (fun a => e a.succ)) _ from this)
            (by rw [hp]; nlinarith [mul_nonneg h3 hc])
        · have := BetaSesquilinearity.CCle_add ih1.2 (BetaSesquilinearity.CCle_smul (if l.1 then σ else (starRingEnd ℂ) σ) ih0.1)
          rw [hs] at this
          rw [hxe]
          have hf : (fun g => (KB.uInv σ w (fun e' => x (Fin.cons (1 : Fin 2) e')) (fun a => e a.succ) +
              (if l.1 then σ else (starRingEnd ℂ) σ) • KB.uInv σ w (fun e' => x (Fin.cons (0 : Fin 2) e')) (fun a => e a.succ)) g -
              x (Fin.cons (1 : Fin 2) (fun a => e a.succ)) g) =
              fun g => (KB.uInv σ w (fun e' => x (Fin.cons (1 : Fin 2) e')) (fun a => e a.succ) g -
                x (Fin.cons (1 : Fin 2) (fun a => e a.succ)) g) +
                (if l.1 then σ else (starRingEnd ℂ) σ) • KB.uInv σ w (fun e' => x (Fin.cons (0 : Fin 2) e')) (fun a => e a.succ) g := by
            funext g
            simp only [Pi.add_apply, Pi.smul_apply]
            abel
          rw [hf]
          exact JCx2.pd_ccle_mono_c this (by rw [hp]; nlinarith [mul_nonneg h3 hc, mul_nonneg (mul_nonneg h3 hσ0) hc])
  obtain ⟨K1, hK1, hmul⟩ := mult_phase (E := Wq →L[ℂ] Wp) m
    (JCx2.mnLinHerm (fvec k ρ Bs.z' 0) (fvec k ρ Bs.z 0))
  refine ⟨(K1 + 1) * 3 ^ w.length, by positivity, ?_⟩
  intro σ hσ A x c hx e
  have hc : 0 ≤ c := JCx2.pd_ccle_nonneg (hx e)
  have hu := uInv_ccle (A + ((m + 1 : ℕ) : ℝ)) m σ hσ w x c hx e
  have h1 := hmul σ hσ A (KB.uInv σ w x e) (3 ^ w.length * c) hu.1
  have h2 : B.CCle A m (fun g => KB.uInv σ w x e g - x e g) (3 ^ w.length * ‖σ‖ * c) :=
    BetaSesquilinearity.CCle_mono_A (by have : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _; linarith) hu.2
  have h3 := BetaSesquilinearity.CCle_add h1 h2
  have hf : ((PBO.waveL Bs σ w - 1) x) e = fun g =>
      (Complex.exp (PBFV.phaseL σ (JCx2.mnLinHerm (fvec k ρ Bs.z' 0) (fvec k ρ Bs.z 0)) g) - 1) •
        KB.uInv σ w x e g + (KB.uInv σ w x e g - x e g) := by
    funext g
    simp only [LinearMap.sub_apply, Module.End.one_apply, Pi.sub_apply, PBO.waveL, LinearMap.coe_mk,
      AddHom.coe_mk, KB.waveG]
    rw [PBFV.fsv_dmin_one σ Bs.z Bs.z' g (by omega), sub_smul, one_smul]
    abel
  rw [hf]
  refine JCx2.pd_ccle_mono_c h3 (le_of_eq ?_)
  ring

theorem mDiff_ccle (Bs : B.RealPlaceData k ρ Wp Wq) (w : List C.Letter) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ σ : ℂ, ‖σ‖ ≤ 2 → ∀ (A : ℝ) (x : Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) (c : ℝ),
      (∀ e, B.CCle (A + 3 * ((m + 1 : ℕ) : ℝ)) m (x e) c) →
      ∀ e, B.CCle A m ((PBO.mDiff Bs σ w x) e) (K * ‖σ‖ ^ 3 * c) := by
  obtain ⟨K, hK, h1⟩ := waveL_sub_one_ccle Bs w m
  refine ⟨K ^ 3, by positivity, ?_⟩
  intro σ hσ A x c hx
  set M : ℝ := ((m + 1 : ℕ) : ℝ) with hM
  have hx' : ∀ e, B.CCle ((A + M + M) + M) m (x e) c := fun e => by
    have : (A + M + M) + M = A + 3 * M := by ring
    rw [this]; exact hx e
  have s1 := h1 σ hσ (A + M + M) x c hx'
  have s2 := h1 σ hσ (A + M) _ _ s1
  have s3 := h1 σ hσ A _ _ s2
  intro e
  have he : PBO.mDiff Bs σ w x = (PBO.waveL Bs σ w - 1) ((PBO.waveL Bs σ w - 1) ((PBO.waveL Bs σ w - 1) x)) := by
    simp only [PBO.mDiff, pow_succ, pow_zero, one_mul]
    rfl
  rw [he]
  refine JCx2.pd_ccle_mono_c (s3 e) (le_of_eq ?_)
  ring

end one

end Formalism.FourierDecayAlt.P.StandardPairingDecay
end
end

section

noncomputable section

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutEX.MkTopBump

theorem bump_two {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (μ : Measure E) [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    (f g : E → ℂ) (hf : Continuous f) (hg : Continuous g) (hf0 : f 0 = 1) (hg0 : g 0 = 1) :
    ∃ b : E → ℝ, ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧ (∫ x, (b x : ℂ) * f x ∂μ) ≠ 0 ∧
      (∫ x, (b x : ℂ) * g x ∂μ) ≠ 0 := by
  obtain ⟨δ, hδ, hδf⟩ := Metric.continuousAt_iff.1 hf.continuousAt (1 / 2 : ℝ) (by norm_num)
  obtain ⟨δ', hδ', hδg⟩ := Metric.continuousAt_iff.1 hg.continuousAt (1 / 2 : ℝ) (by norm_num)
  have hm : 0 < min δ δ' := lt_min hδ hδ'
  let B : ContDiffBump (0 : E) := ⟨min δ δ' / 4, min δ δ' / 2, by positivity, by linarith⟩
  set b : E → ℝ := fun x => B x with hbdef
  have hbd : ContDiff ℝ ∞ b := B.contDiff
  have hbc : HasCompactSupport b := B.hasCompactSupport
  have hbnn : ∀ x, 0 ≤ b x := fun x => B.nonneg
  have hbcont : Continuous b := B.continuous
  have hbint : 0 < ∫ x, b x ∂μ := B.integral_pos
  have hbs : tsupport b ⊆ Metric.ball (0 : E) (min δ δ') := by
    rw [show tsupport b = Metric.closedBall (0 : E) (min δ δ' / 2) from B.tsupport_eq]
    exact Metric.closedBall_subset_ball (by linarith)
  have aux : ∀ h : E → ℂ, Continuous h →
      (∀ x, dist x 0 < min δ δ' → ‖h x - 1‖ < 1 / 2) → (∫ x, (b x : ℂ) * h x ∂μ) ≠ 0 := by
    intro h hh hs
    have hbC : Continuous (fun x => (b x : ℂ)) := Complex.continuous_ofReal.comp hbcont
    have hbcC : HasCompactSupport (fun x => (b x : ℂ)) := hbc.comp_left Complex.ofReal_zero
    have hi1 : Integrable (fun x => (b x : ℂ)) μ := hbC.integrable_of_hasCompactSupport hbcC
    have hi2 : Integrable (fun x => (b x : ℂ) * (h x - 1)) μ :=
      (hbC.mul (hh.sub continuous_const)).integrable_of_hasCompactSupport (hbcC.mul_right)
    have hi3 : Integrable (fun x => b x * (1 / 2 : ℝ)) μ :=
      (hbcont.integrable_of_hasCompactSupport hbc).mul_const _
    have split : (∫ x, (b x : ℂ) * h x ∂μ) = (∫ x, (b x : ℂ) ∂μ) + ∫ x, (b x : ℂ) * (h x - 1) ∂μ := by
      rw [← integral_add hi1 hi2]
      congr 1
      funext x
      ring
    have hbound : ‖∫ x, (b x : ℂ) * (h x - 1) ∂μ‖ ≤ ∫ x, b x * (1 / 2 : ℝ) ∂μ := by
      refine norm_integral_le_of_norm_le hi3 (Filter.Eventually.of_forall fun x => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hbnn x)]
      by_cases hbx : b x = 0
      · rw [hbx]; simp
      · have hx : x ∈ Metric.ball (0 : E) (min δ δ') := hbs (subset_tsupport _ hbx)
        exact mul_le_mul_of_nonneg_left (hs x hx).le (hbnn x)
    have hreal : (∫ x, (b x : ℂ) ∂μ) = ((∫ x, b x ∂μ : ℝ) : ℂ) := integral_ofReal
    rw [integral_mul_const] at hbound
    intro h0
    rw [split, hreal] at h0
    have e1 : ((∫ x, b x ∂μ : ℝ) : ℂ) = -∫ x, (b x : ℂ) * (h x - 1) ∂μ := eq_neg_of_add_eq_zero_left h0
    have e2 : ‖((∫ x, b x ∂μ : ℝ) : ℂ)‖ = ‖∫ x, (b x : ℂ) * (h x - 1) ∂μ‖ := by rw [e1, norm_neg]
    rw [Complex.norm_real, Real.norm_of_nonneg hbint.le] at e2
    linarith
  refine ⟨b, hbd, hbc, aux f hf fun x hx => ?_, aux g hg fun x hx => ?_⟩
  · have := hδf (lt_of_lt_of_le hx (min_le_left _ _))
    rwa [hf0, dist_eq_norm] at this
  · have := hδg (lt_of_lt_of_le hx (min_le_right _ _))
    rwa [hg0, dist_eq_norm] at this

local instance bsS {p : ℕ} : BorelSpace ((G.UT p → ℂ) × (Fin p → ℝ)) := Prod.borelSpace
local instance bsRC {k p ρ : ℕ} : BorelSpace (U.RC k p ρ) := Prod.borelSpace

theorem piHaar {n p : ℕ} : (volume : Measure (Fin n → Fin p → ℂ)).IsAddHaarMeasure :=
  Measure.pi.isAddHaarMeasure (fun _ => volume)

theorem rcHaar {k p ρ : ℕ} : (volume : Measure (U.RC k p ρ)).IsAddHaarMeasure := by
  have := @piHaar (2 * ρ + k + 1) p
  rw [Measure.volume_eq_prod]
  exact Measure.prod.instIsAddHaarMeasure _ _

theorem bump_exists {k p ρ : ℕ} (z z' : Fin (2 * ρ + k + 1) → ℂ) (hz : inWb k ρ z) (hz' : inWb k ρ z') :
    ∃ b : U.RC k p ρ → ℝ, ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧
      (∫ x, (b x : ℂ) * psi k (p + ρ) (liftVec k p ρ z) cStd (U.Rn k p ρ x) ∂(U.muRC k p ρ)) ≠ 0 ∧
      (∫ x, (b x : ℂ) * star (psi k (p + ρ) (liftVec k p ρ z') cStd (U.Rn k p ρ x)) ∂(U.muRC k p ρ)) ≠ 0 := by
  have hc : Continuous (fun x : U.RC k p ρ => psi k (p + ρ) (liftVec k p ρ z) cStd (U.Rn k p ρ x)) :=
    (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.psi_cont _ _).comp (Formalism.FourierDecayAlt.P.Dx2.SplitF.rn_cont p ρ)
  have hc' : Continuous (fun x : U.RC k p ρ => star (psi k (p + ρ) (liftVec k p ρ z') cStd (U.Rn k p ρ x))) :=
    ((Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.psi_cont _ _).comp (Formalism.FourierDecayAlt.P.Dx2.SplitF.rn_cont p ρ)).star
  have h0 : psi k (p + ρ) (liftVec k p ρ z) cStd (U.Rn k p ρ 0) = 1 := by
    rw [Formalism.FourierDecayAlt.P.LeftFubiniLemmas.rn_zero]
    exact Formalism.FourierDecayAlt.P.Qx5.psi_one (Formalism.FourierDecayAlt.P.LeftFubiniLemmas.inWb_liftVec hz) _
  have h0' : star (psi k (p + ρ) (liftVec k p ρ z') cStd (U.Rn k p ρ 0)) = 1 := by
    rw [Formalism.FourierDecayAlt.P.LeftFubiniLemmas.rn_zero, Formalism.FourierDecayAlt.P.Qx5.psi_one (Formalism.FourierDecayAlt.P.LeftFubiniLemmas.inWb_liftVec hz') _, star_one]
  have := @rcHaar k p ρ
  unfold U.muRC
  exact bump_two volume _ _ hc hc' h0 h0'

end Formalism.FourierDecayAlt.P.CutEX.MkTopBump
end
end
