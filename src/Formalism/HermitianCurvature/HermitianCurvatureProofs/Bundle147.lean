module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HsRealSmulRight
public import Formalism.HermitianCurvature.CompositeFormulaLevelZero
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle098
public import Formalism.HermitianCurvature.StatementD
public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeisenbergLeviConjugationMeasure
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormFactor
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixMul
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
public import Formalism.HermitianCurvature.Bundle008
public import Formalism.FormalDegreeBessel.Bundle002
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle097
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle026
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.VectorVanishesBigCell
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WittOrthonormalBasis
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelLiftBasics.LevelGroupUnitaryHermitian
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle130

@[expose] public section

section

open MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerB

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem update_mem_OmX {c : Fin r → ℂ} (hc : c ∈ OmX r) (l : Fin r) {t : ℂ} (ht : t ≠ 0) :
    Function.update c l t ∈ OmX r := by
  intro j
  by_cases hj : j = l
  · subst hj; simpa using ht
  · rw [Function.update_of_ne hj]; exact hc j

theorem cslice_contDiffAt (Φ : RadSp k r z z' π π') (g : Mx k r) {x : Fin r → ℂ} (hx : x ∈ OmX r) :
    ContDiffAt ℝ ∞ (fun c' => (Φ : Fn k r (Wq →L[ℂ] Wp)) c' g) x := by
  by_cases hg : g ∈ Glev k r (Fin.last r) ∧ 0 < GGl k r z z' g
  · obtain ⟨-, hs, -⟩ := Φ.2
    obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := hs (x, g) ⟨hx, hg.1, hg.2⟩
    have hcont : Continuous (fun c' : Fin r → ℂ => (c', g)) := continuous_id.prodMk continuous_const
    have hV : IsOpen ((fun c' : Fin r → ℂ => (c', g)) ⁻¹' U) := hU.preimage hcont
    have hFx : ContDiffAt ℝ ∞ (fun c' : Fin r → ℂ => F (c', g)) x :=
      (hF.contDiffAt (hU.mem_nhds hxU)).comp x (contDiff_id.prodMk contDiff_const).contDiffAt
    refine hFx.congr_of_eventuallyEq ?_
    filter_upwards [hV.mem_nhds hxU] with c' hc'
    exact hΦ (c', g) hc' hg.1
  · have h0 : (fun c' => (Φ : Fn k r (Wq →L[ℂ] Wp)) c' g) = fun _ => 0 := by
      funext c'
      exact radSp_zero_off Φ (x := (c', g)) (fun h => hg ⟨h.2.1, h.2.2⟩)
    rw [h0]; exact contDiffAt_const

theorem dZv_update {f : (Fin r → ℂ) → (Wq →L[ℂ] Wp)} (c : Fin r → ℂ) (l : Fin r) (t : ℂ)
    (hf : DifferentiableAt ℝ f (Function.update c l t)) :
    dZv (fun s => f (Function.update c l s)) t = wirt l f (Function.update c l t) ∧
      dZbv (fun s => f (Function.update c l s)) t = wirtBar l f (Function.update c l t) := by
  have hu := hasFDerivAt_update (𝕜 := ℝ) c (i := l) t
  have h := hf.hasFDerivAt.comp t hu
  have hd : ∀ v : ℂ, fderiv ℝ (fun s => f (Function.update c l s)) t v =
      fderiv ℝ f (Function.update c l t) (Pi.single l v) := by
    intro v
    rw [show (fun s => f (Function.update c l s)) = f ∘ Function.update c l from rfl, h.fderiv]
    simp only [ContinuousLinearMap.comp_apply]
    congr 1
    funext j
    by_cases hj : j = l
    · subst hj; simp
    · simp [hj]
  constructor
  · unfold dZv wirt; rw [hd, hd]
  · unfold dZbv wirtBar; rw [hd, hd]

theorem site_p_adj_g (X : ActualOps k r z z' π π') (Φ Ψ : RadSp k r z z' π π') (l : Fin r) (c : Fin r → ℂ)
    (hc : c ∈ OmX r) (g : Mx k r)
    (h0 : Integrable (fun t : ℂ => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g)
      ((Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g) / ((‖t‖ ^ 2 : ℝ) : ℂ)))
    (h1 : Integrable (fun t : ℂ => B.hsInner ((X.op l 0 Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g)
      ((Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g) / ((‖t‖ ^ 2 : ℝ) : ℂ)))
    (h2 : Integrable (fun t : ℂ => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g)
      ((X.op l 3 Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g) / ((‖t‖ ^ 2 : ℝ) : ℂ))) :
    ∫ t : ℂ, B.hsInner ((X.op l 0 Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g)
      ((Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g) / ((‖t‖ ^ 2 : ℝ) : ℂ) =
    -∫ t : ℂ, B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g)
      ((X.op l 3 Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g) / ((‖t‖ ^ 2 : ℝ) : ℂ) := by
  set fΦ : (Fin r → ℂ) → (Wq →L[ℂ] Wp) := fun c' => (Φ : Fn k r (Wq →L[ℂ] Wp)) c' g with hfΦ
  set fΨ : (Fin r → ℂ) → (Wq →L[ℂ] Wp) := fun c' => (Ψ : Fn k r (Wq →L[ℂ] Wp)) c' g with hfΨ
  set A : ℂ → (Wq →L[ℂ] Wp) := fun t => fΦ (Function.update c l t) with hA
  set Bf : ℂ → (Wq →L[ℂ] Wp) := fun t => fΨ (Function.update c l t) with hB
  have hupd : ContDiff ℝ ∞ (fun t : ℂ => Function.update c l t) :=
    contDiff_pi.mpr fun j => by
      by_cases hj : j = l
      · subst hj; simp only [Function.update_self]; exact contDiff_id
      · simpa [Function.update_of_ne hj] using contDiff_const
  have hAc : ContDiffOn ℝ 1 A {t | t ≠ 0} := fun t ht =>
    (((cslice_contDiffAt Φ g (update_mem_OmX hc l ht)).comp t hupd.contDiffAt).of_le (by simp)).contDiffWithinAt
  have hBc : ContDiffOn ℝ 1 Bf {t | t ≠ 0} := fun t ht =>
    (((cslice_contDiffAt Ψ g (update_mem_OmX hc l ht)).comp t hupd.contDiffAt).of_le (by simp)).contDiffWithinAt
  have hpΦ : ∀ t : ℂ, t ≠ 0 → (X.op l 0 Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g = t • dZv A t := by
    intro t ht
    have hd := dZv_update (f := fΦ) c l t
      ((cslice_contDiffAt Φ g (update_mem_OmX hc l ht)).differentiableAt (by simp))
    rw [X.op_apply, hd.1]
    show pOp l fΦ (Function.update c l t) = _
    unfold pOp
    rw [if_pos (update_mem_OmX hc l ht), Function.update_self]
  have hpΨ : ∀ t : ℂ, t ≠ 0 → (X.op l 3 Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g =
      conj t • dZbv Bf t := by
    intro t ht
    have hd := dZv_update (f := fΨ) c l t
      ((cslice_contDiffAt Ψ g (update_mem_OmX hc l ht)).differentiableAt (by simp))
    rw [X.op_apply, hd.2]
    show pbOp l fΨ (Function.update c l t) = _
    unfold pbOp
    rw [if_pos (update_mem_OmX hc l ht), Function.update_self]
    rfl
  have e1 : (fun t : ℂ => B.hsInner ((X.op l 0 Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g)
      ((Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g) / ((‖t‖ ^ 2 : ℝ) : ℂ)) =
      fun t => B.hsInner (t • dZv A t) (Bf t) / ((‖t‖ ^ 2 : ℝ) : ℂ) := by
    funext t
    by_cases ht : t = 0
    · subst ht; simp
    · rw [hpΦ t ht]
  have e2 : (fun t : ℂ => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g)
      ((X.op l 3 Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l t) g) / ((‖t‖ ^ 2 : ℝ) : ℂ)) =
      fun t => B.hsInner (A t) (conj t • dZbv Bf t) / ((‖t‖ ^ 2 : ℝ) : ℂ) := by
    funext t
    by_cases ht : t = 0
    · subst ht; simp
    · rw [hpΨ t ht]
  have h1' := e1 ▸ h1
  have h2' := e2 ▸ h2
  rw [e1, e2]
  exact pLogAdjHS A Bf hAc hBc h0 h1' h2'

theorem site_p_adj (X : ActualOps k r z z' π π') (μ : Measure (Mt k r)) [SFinite μ] (Φ Ψ : RadSp k r z z' π π')
    (l : Fin r) (c : Fin r → ℂ) (hc : c ∈ OmX r)
    (h0 : Integrable (fun q : ℂ × Mt k r => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l q.1)
      (Matrix.of q.2)) ((Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l q.1) (Matrix.of q.2)) /
        ((‖q.1‖ ^ 2 : ℝ) : ℂ)) (volume.prod μ))
    (h1 : Integrable (fun q : ℂ × Mt k r => B.hsInner ((X.op l 0 Φ : Fn k r (Wq →L[ℂ] Wp))
      (Function.update c l q.1) (Matrix.of q.2)) ((Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l q.1)
        (Matrix.of q.2)) / ((‖q.1‖ ^ 2 : ℝ) : ℂ)) (volume.prod μ))
    (h2 : Integrable (fun q : ℂ × Mt k r => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l q.1)
      (Matrix.of q.2)) ((X.op l 3 Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update c l q.1) (Matrix.of q.2)) /
        ((‖q.1‖ ^ 2 : ℝ) : ℂ)) (volume.prod μ)) :
    ∫ t : ℂ, pairAt μ (X.op l 0 Φ) Ψ (Function.update c l t) / ((‖t‖ ^ 2 : ℝ) : ℂ) =
      -∫ t : ℂ, pairAt μ Φ (X.op l 3 Ψ) (Function.update c l t) / ((‖t‖ ^ 2 : ℝ) : ℂ) := by
  unfold pairAt
  simp only [← integral_div]
  rw [integral_integral_swap h1]
  conv_rhs => rw [integral_integral_swap h2]
  rw [← integral_neg]
  refine integral_congr_ae ?_
  filter_upwards [h0.prod_left_ae, h1.prod_left_ae, h2.prod_left_ae] with x hx0 hx1 hx2
  exact site_p_adj_g X Φ Ψ l c hc (Matrix.of x) hx0 hx1 hx2

end Formalism.FourierDecayAlt.P5.HerB
end
end

section

namespace Formalism.FourierDecayAlt.P.CutBP.TNM

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory Matrix

noncomputable section

section vec

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}

def gd (p : KB.Pl P Wp Wq) (d : Fin (P.r + 1) → ℂ) : B.Mat P.k P.r :=
  bigCell P.k P.r (fun i => d i.castSucc) (p.T.base.μsec (d (Fin.last P.r)))

def wq (p : KB.Pl P Wp Wq) (d : Fin (P.r + 1) → ℂ) : Fin (2 * P.r + P.k + 1) → ℂ :=
  D.prW P.k P.r p.T.base.z (D.cofR p.T.base (gd p d))

theorem vDecomp (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (d : Fin (P.r + 1) → ℂ)
    (hd : ∀ a, d a ≠ 0) (hG : 0 < TBB.Gp p (TBB.bigPt P.r d)) :
    ∃ hA ∈ UWset P.k P.r p.T.base.z, ∃ hB ∈ UWset P.k P.r p.T.base.z', ∃ l : ℂ,
      p.V F (TBB.bigPt P.r d) = Formalism.FourierDecayAlt.P.Dx2.VV.CinL p.T.base hA hB (B.JF p.T.base F (gd p d)) ∧
      hA *ᵥ wq p d = l • (p.m₀ *ᵥ p.ν') ∧ l ≠ 0 := by
  have hl : D.IsLocPt (Formalism.FourierDecayAlt.P.PBJ.bigPt d) (P.r + 1) := Formalism.FourierDecayAlt.P.PBJ.Dens.isLocPt_bigPt d hd
  have hG' : 0 < D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r (Formalism.FourierDecayAlt.P.PBJ.bigPt d) := hG
  have h' := Formalism.FourierDecayAlt.P.exists_isotropic_frame P.k P.r Wp Wq p.T.base p.ν' p.m₀ _ p.hF hl hG'
  have hV : p.V F (TBB.bigPt P.r d) = D.orbJ p.T.base h'.choose
      (D.muR p.T.base h'.choose (hl.2 ▸ D.ptPerm (Formalism.FourierDecayAlt.P.PBJ.bigPt d))) F := by
    show D.vecV p.T.base p.ν' p.m₀ F (Formalism.FourierDecayAlt.P.PBJ.bigPt d) = _
    unfold D.vecV
    rw [dite_eq_left ⟨hl, hG'⟩, dite_eq_left h']
  obtain ⟨hγ, hZγ, hDγ⟩ := h'.choose_spec
  have hζ : Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' < Complex.normSq (d (Fin.last P.r)) :=
    Formalism.FourierDecayAlt.P.PBM.zeta_big _ d hG'
  have hc : ∀ a : Fin P.r, d a.castSucc ≠ 0 := fun a => hd _
  have hsec := p.T.base.sec.2 _ hζ
  have hγ' : gd p d ∈ B.GV P.k P.r := bigCellMem P.k P.r _ _ hc hsec.1
  have hZγ' : Zhat P.k P.r p.T.base.z p.T.base.z' (gd p d) = D.ptMatN (Formalism.FourierDecayAlt.P.PBJ.bigPt d) (P.r + 1) :=
    Formalism.FourierDecayAlt.P.PBM.zhat_bigCell_pt p.T.base d hζ
  have hpos : 0 < Gf P.k P.r p.T.base.z p.T.base.z' h'.choose := by
    rw [← Formalism.FourierDecayAlt.P.ptG_spec P.k P.r _ _ (Formalism.FourierDecayAlt.P.PBJ.bigPt d) _ hl hZγ]; exact hG'
  have hpos' : 0 < Gf P.k P.r p.T.base.z p.T.base.z' (gd p d) := by
    rw [← Formalism.FourierDecayAlt.P.ptG_spec P.k P.r _ _ (Formalism.FourierDecayAlt.P.PBJ.bigPt d) _ hl hZγ']; exact hG'
  obtain ⟨s, hs, s', hs', hγs⟩ := Formalism.FourierDecayAlt.P.fibre_orbit_description P.k P.r p.T.base.z p.T.base.z'
    ⟨p.T.base.k_pos, Formalism.FourierDecayAlt.P.Dx2.VV.std_vector_z p.T.base, Formalism.FourierDecayAlt.P.Dx2.VV.std_vector_z_prime p.T.base⟩
    _ hγ _ hγ' hpos (hZγ.trans hZγ'.symm)
  obtain ⟨hA, hhA, nA, hnA, hfA, rfl⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.stabilizer_decomp_unitary_mul_unipotent (Formalism.FourierDecayAlt.P.Dx2.VV.std_vector_z p.T.base) hs
  obtain ⟨hB, hhB, nB, hnB, hfB, rfl⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.stabilizer_decomp_unitary_mul_unipotent (Formalism.FourierDecayAlt.P.Dx2.VV.std_vector_z_prime p.T.base) hs'
  have hlaw := Formalism.FourierDecayAlt.P.Dx2.VV.orbJ_pt p.T.base (Formalism.FourierDecayAlt.P.PBJ.bigPt d) hl hγ hZγ hpos hhA hnA hfA hhB hnB
    hfB F
  have hw : (hl.2 ▸ D.ptPerm (Formalism.FourierDecayAlt.P.PBJ.bigPt d) : Equiv.Perm (Fin (P.r + 1))) = 1 :=
    Formalism.FourierDecayAlt.P.PBM.cast_perm_eq_one _ _ (Formalism.FourierDecayAlt.P.PBM.ptPerm_bigPt d hd)
  obtain ⟨hmono, hnz⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.ptMatN_monoP' (Formalism.FourierDecayAlt.P.PBJ.bigPt d) (P.r + 1) hl.2 hl.1
  rw [hw] at hmono
  obtain ⟨a, ha, hpr⟩ := hDγ.1
  have hdet : (Zhat P.k P.r p.T.base.z p.T.base.z' h'.choose).det ≠ 0 :=
    Formalism.FourierDecayAlt.P.determinant_nonzero P.k P.r p.T.base.z p.T.base.z' (Formalism.FourierDecayAlt.P.Dx2.VV.std_vector_z p.T.base)
      (Formalism.FourierDecayAlt.P.Dx2.VV.std_vector_z_prime p.T.base) _ hpos
  refine ⟨hA, hhA, hB, hhB, (a : ℂ) * (Zhat P.k P.r p.T.base.z p.T.base.z' h'.choose).det, ?_, ?_,
    mul_ne_zero (by exact_mod_cast ha.ne') hdet⟩
  · rw [hV, ← hlaw]
    show _ = Formalism.FourierDecayAlt.P.Dx2.VV.CinL p.T.base hA hB (B.JF p.T.base F (gd p d))
    rw [← hγs, hw, Formalism.FourierDecayAlt.P.PBM.orbJ_one_eq p.T.base hγ' hpos' hnz (hZγ'.trans hmono) F]
  · have hZ1 := Formalism.FourierDecayAlt.P.Dx2.VV.zhat_conj p.T.base hhA hnA hfA hhB hnB hfB h'.choose
    have hcof := Formalism.FourierDecayAlt.P.Dx2.VV.cofR_conj p.T.base (sA := hA * nA)
      (Formalism.FourierDecayAlt.P.Dx2.VV.mul_fix hhB hfB) hZ1
    have hzz : herm (Hpk P.k P.r) p.T.base.z p.T.base.z ≠ 0 := by
      rw [Formalism.FourierDecayAlt.P.Dx2.DF.herm_self_alt]
      have := p.T.base.T_pos
      intro h
      have h2 := congrArg Complex.re h
      simp at h2; linarith
    have hsinv := Formalism.FourierDecayAlt.P.Dx2.VV.prW_sinv p.T.base.z_mem hzz hhA hnA
      (Formalism.FourierDecayAlt.P.Dx2.VV.cofR_free p.T.base h'.choose)
    unfold wq
    rw [hγs, hcof, hsinv, hpr, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_G hhA.1),
      Matrix.one_mulVec]

end vec

end

end Formalism.FourierDecayAlt.P.CutBP.TNM
end

section

open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

variable {k : ℕ}

theorem castM_inv' {a b : ℕ} (h : a = b) (g : B.Mat k a) : D.castM h g⁻¹ = (D.castM h g)⁻¹ := by
  subst h
  simp [D.castM]

private theorem castV_rfl' {a : ℕ} (h : a = a) (v : Fin (2 * a + k + 1) → ℂ) : D.castV h v = v := by
  funext i
  rfl

theorem psi_castM {a b : ℕ} (h : a = b) (v : Fin (2 * a + k + 1) → ℂ) (c : ℂ) (g : B.Mat k a) :
    psi k b (D.castV h v) c (D.castM h g) = psi k a v c g := by
  subst h
  simp [D.castM, castV_rfl']

theorem castM_N {a b : ℕ} (h : a = b) {g : B.Mat k a} (hg : g ∈ Nset k a) : D.castM h g ∈ Nset k b := by
  subst h
  simpa [D.castM] using hg

theorem castM_UWv {a b : ℕ} (h : a = b) {v : Fin (2 * a + k + 1) → ℂ} {g : B.Mat k a} (hg : g ∈ UWset k a v) :
    D.castM h g ∈ UWset k b (D.castV h v) := by
  subst h
  simpa [D.castM, castV_rfl'] using hg

theorem castM_cont {a b : ℕ} (h : a = b) : Continuous (D.castM (k := k) h) := by
  subst h
  have e : (D.castM (k := k) (rfl : a = a)) = fun g => g := by
    funext g
    simp [D.castM]
  rw [e]
  exact continuous_id

theorem inWb_castV {a b : ℕ} (h : a = b) {v : Fin (2 * a + k + 1) → ℂ} (hv : inWb k a v) : inWb k b (D.castV h v) := by
  subst h
  rw [castV_rfl']
  exact hv

theorem uw_closedSubgroup (r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : B2.IsClosedSubgroup (UWset k r z) :=
  ⟨Dx2.Rad.one_UW z, fun _ ha _ hb => WeylGroupFacts.uw_mul ha hb, fun _ ha => WeylGroupFacts.uw_inv ha,
    fun _ ha => HermitianFormFactor.UH_unit (Ux3.hpk_det k r) ha.1, B6.isClosed_UWset k r z⟩

def levA (ρ : ℕ) (x : Mt k ρ) : Mt k (ρ + 1) :=
  Matrix.of.symm (D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ (Matrix.of x)))

private theorem continuous_ιLev_apply (ρ : ℕ) (p q : Fin (2 * (1 + ρ) + k + 1)) :
    Continuous fun x : Mt k ρ => ιLev k 1 ρ (Matrix.of x) p q := by
  simp only [Formalism.QuantumDeterminants.ιLev]
  by_cases hp : 1 ≤ p.val ∧ p.val < 2 * ρ + k + 1 + 1
  · by_cases hq : 1 ≤ q.val ∧ q.val < 2 * ρ + k + 1 + 1
    · simp only [dif_pos hp, dif_pos hq, Matrix.of_apply]
      exact (continuous_apply _).comp (continuous_apply _)
    · simp only [dif_pos hp, dif_neg hq]
      exact continuous_const
  · simp only [dif_neg hp]
    exact continuous_const

theorem levA_cont (ρ : ℕ) : Continuous (levA (k := k) ρ) := by
  apply continuous_pi
  intro p
  apply continuous_pi
  intro q
  simp only [levA, Matrix.of_symm_apply, D.castM, Matrix.reindex_apply, Matrix.submatrix_apply]
  exact continuous_ιLev_apply ρ _ _

private theorem castM_mul_hermitian_curvature {a b : ℕ} (h : a = b) (g g' : B.Mat k a) :
    D.castM h (g * g') = D.castM h g * D.castM h g' := by
  subst h
  simp [D.castM]

theorem lev_mul' (ρ : ℕ) (a b : B.Mat k ρ) :
    D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ (a * b)) =
      D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ a) * D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ b) := by
  have hL := PI.QnLevBasicsW.level_group_homomorphism
  unfold Formalism.QuantumDeterminants.LevHom at hL
  rw [(hL k 1 ρ).2 a b]
  exact castM_mul_hermitian_curvature _ _ _

theorem castM_back {a b : ℕ} (h : a = b) (g : B.Mat k b) : D.castM h (D.castM h.symm g) = g := by
  subst h
  simp [D.castM]

theorem castV_back {a b : ℕ} (h : a = b) (v : Fin (2 * b + k + 1) → ℂ) : D.castV h (D.castV h.symm v) = v := by
  subst h
  rw [castV_rfl', castV_rfl']

theorem levA_apply (ρ : ℕ) (x : Mt k ρ) :
    (Matrix.of (levA ρ x) : B.Mat k (ρ + 1)) = D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ (Matrix.of x)) := rfl

theorem lev_onto {ρ : ℕ} (z0 : Fin (2 * ρ + k + 1) → ℂ) (a : B.Mat k (ρ + 1))
    (ha : a ∈ UWset k (ρ + 1) (D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ z0))) :
    ∃ a0 ∈ UWset k ρ z0, D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ a0) = a := by
  have ha' : D.castM (Nat.add_comm 1 ρ).symm a ∈ UWset k (1 + ρ) (liftVec k 1 ρ z0) := by
    have := castM_UWv (Nat.add_comm 1 ρ).symm ha
    have e : D.castV (Nat.add_comm 1 ρ).symm (D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ z0)) = liftVec k 1 ρ z0 := by
      have := castV_back (k := k) (Nat.add_comm 1 ρ).symm (liftVec k 1 ρ z0)
      simpa using this
    rwa [e] at this
  obtain ⟨y, hy, hy'⟩ := JCTx5.uw_onto (k := k) (i := 1) (r' := ρ) z0 _ ha'
  exact ⟨y, hy, by rw [hy']; exact castM_back _ a⟩

theorem muW_lev {ρ : ℕ} (z0 : Fin (2 * ρ + k + 1) → ℂ)
    (μ0 : Measure (Mt k ρ)) (μ1 : Measure (Mt k (ρ + 1)))
    (h0 : B.IsHaarOn (UWset k ρ z0) μ0)
    (h1 : B.IsHaarOn (UWset k (ρ + 1) (D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ z0))) μ1)
    (n0 : μ0 Set.univ = 1) (n1 : μ1 Set.univ = 1) :
    μ1 = μ0.map (levA ρ) := by
  set U1 := UWset k (ρ + 1) (D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ z0)) with hU1
  have hm : Measurable (levA (k := k) ρ) := (levA_cont ρ).measurable
  have hmem : ∀ y ∈ UWset k ρ z0, (Matrix.of (levA ρ y) : B.Mat k (ρ + 1)) ∈ U1 := fun y hy =>
    castM_UWv _ (Dx2.Tower.lev_UW 1 ρ z0 (Matrix.of y) hy)
  set ν := μ0.map (levA (k := k) ρ) with hν
  have hνu : ν Set.univ = 1 := by rw [hν, Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ, n0]
  have hconc : ν U1ᶜ = 0 := by
    have hcl : IsClosed {x : Mt k (ρ + 1) | Matrix.of x ∈ U1} := B7.isClosed_UW _
    show ν {x : Mt k (ρ + 1) | Matrix.of x ∈ U1}ᶜ = 0
    rw [hν, Measure.map_apply hm hcl.measurableSet.compl]
    apply measure_mono_null _ h0.conc
    intro y hy hyU
    exact hy (hmem y hyU)
  have hleft : ∀ a ∈ U1, ν.map (lmulM a) = ν := by
    intro a ha
    obtain ⟨a0, ha0, rfl⟩ := lev_onto z0 a ha
    have hl : Measurable (lmulM (k := k) (r := ρ + 1) (D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ a0))) :=
      B2x5.measurable_lmulM _
    have hl0 : Measurable (lmulM (k := k) (r := ρ) a0) := B2x5.measurable_lmulM _
    have e : lmulM (D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ a0)) ∘ levA (k := k) ρ = levA ρ ∘ lmulM a0 := by
      funext x
      show (D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ a0) * D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ (Matrix.of x)) :
          B.Mat k (ρ + 1)) = D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ (a0 * Matrix.of x))
      rw [lev_mul']
    rw [hν, Measure.map_map hl hm, e, ← Measure.map_map hm hl0, h0.left a0 ha0]
  have hfin : ∀ K : Set (Mt k (ρ + 1)), IsCompact K → ν K < ⊤ := by
    intro K _
    calc ν K ≤ ν Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := hνu
      _ < ⊤ := ENNReal.one_lt_top
  obtain ⟨c, hc⟩ := Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar k (ρ + 1) U1 μ1 ν (uw_closedSubgroup (ρ + 1) _) h1 hconc hleft hfin
  have hc1 : (c : ENNReal) = 1 := by
    have := congrArg (fun μ : Measure (Mt k (ρ + 1)) => μ Set.univ) hc
    simp only [Measure.smul_apply, n1, hνu, smul_eq_mul, mul_one, ENNReal.smul_def] at this
    exact this.symm
  have hc1' : c = 1 := by exact_mod_cast hc1
  rw [hc, hc1', one_smul]

def Qm (ρ : ℕ) (p : Mt k (1 + ρ) × Mt k ρ) : Mt k (ρ + 1) :=
  Matrix.of.symm (D.castM (Nat.add_comm 1 ρ) (Matrix.of p.1 * ιLev k 1 ρ (Matrix.of p.2)))

theorem Qm_cont (ρ : ℕ) : Continuous (Qm (k := k) ρ) := by
  have hI : Continuous fun p : Mt k (1 + ρ) × Mt k ρ => ιLev k 1 ρ (Matrix.of p.2) :=
    continuous_pi fun a => continuous_pi fun b => (continuous_ιLev_apply ρ a b).comp continuous_snd
  have h1 : Continuous fun p : Mt k (1 + ρ) × Mt k ρ => (Matrix.of p.1 : B.Mat k (1 + ρ)) := continuous_fst
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp only [Qm, Matrix.of_symm_apply, D.castM, Matrix.reindex_apply, Matrix.submatrix_apply]
  exact (continuous_apply _).comp ((continuous_apply _).comp (h1.matrix_mul hI))

theorem sf_heis (ρ : ℕ) : SigmaFinite (B2.μHeis k ρ) :=
  Dx2.MN.sigma_of_haar (Formalism.FourierDecayAlt.P.heisenberg_haar_measure k ρ)

theorem sf_muN (ρ : ℕ) : SigmaFinite (D.muN k ρ) := Dx2.MN.sigma_of_haar (Dx2.MN.haar ρ)

theorem muN_succ' (ρ : ℕ) : D.muN k (ρ + 1) = ((B2.μHeis k ρ).prod (D.muN k ρ)).map (Qm ρ) := by
  have := sf_heis (k := k) ρ
  have := sf_muN (k := k) ρ
  have hl : Measurable (B2.levM k ρ) := (B2x2.levM_cont k ρ).measurable
  have hmu : Measurable (B2.mulM : Mt k (1 + ρ) × Mt k (1 + ρ) → Mt k (1 + ρ)) := B2x2.mulM_cont.measurable
  have hc : Measurable (Dx2.MN.castMt (k := k) (Nat.add_comm 1 ρ)) := (Dx2.MN.castMt_cont _).measurable
  have e1 : (B2.μHeis k ρ).prod ((D.muN k ρ).map (B2.levM k ρ)) =
      ((B2.μHeis k ρ).prod (D.muN k ρ)).map (Prod.map id (B2.levM k ρ)) := by
    rw [← Measure.map_prod_map _ _ measurable_id hl, Measure.map_id]
  rw [Dx2.MN.muN_succ, e1, Measure.map_map hmu (measurable_id.prodMap hl), Measure.map_map hc (hmu.comp (measurable_id.prodMap hl))]
  rfl

end Formalism.FourierDecayAlt.P.PBH
end
end
