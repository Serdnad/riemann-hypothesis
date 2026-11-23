module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle057
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ReflectionTransposeEntriesMem
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagonalTransferAction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle136
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle128
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle034
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle062
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle045
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FiniteSumLocalExpansion
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedLocSec
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle068
import Aesop.Main
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle135
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationUnipotentWeylMeasure
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfBetaAdjCOfLemmaBNorm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentLevelZeroEqOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle134
public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AutomorphicInSphericalLevel
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsMeasurableSection
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle130
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.VectorVanishesBigCell
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle090

@[expose] public section

section

open MeasureTheory Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutFP

def GoodFnLeaf : Prop :=
  ∀ (k ρ : ℕ) (z z' : Fin (2 * ρ + k + 1) → ℂ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (π : Q.Mx k ρ → (Wp →L[ℂ] Wp)) (π' : Q.Mx k ρ → (Wq →L[ℂ] Wq)),
    0 ≤ Tz k ρ z * Tz k ρ z' → ∀ (X : Q.ActualOps k ρ z z' π π') (j : Fin 6), ParameterFamilyAlgebra.Good z z' π π' (X.fn j)

def GoodTLeaf : Prop :=
  ∀ (k ρ : ℕ) (z z' : Fin (2 * ρ + k + 1) → ℂ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (π : Q.Mx k ρ → (Wp →L[ℂ] Wp)) (π' : Q.Mx k ρ → (Wq →L[ℂ] Wq)),
    (∀ c : Fin ρ → ℂ, c ∈ OmX ρ) → (∀ c c' : Fin ρ → ℂ, c = c') →
    ∀ (X : Q.ActualOps k ρ z z' π π') (Y : ℂ) (a b : Fin 2), ParameterFamilyAlgebra.Good z z' π π' (X.t Y a b)

section Asm

open Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Fr

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem gens_good (hfn : GoodFnLeaf) (ht : GoodTLeaf) (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ)
    (π : Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π')
    (μ : Measure (Mt P.k P.r)) (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r)
    (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ) (hD : IsData P z z' π π' X μ L st l0)
    (hOm : ∀ c : Fin P.r → ℂ, c ∈ OmX P.r) (hS : ∀ c c' : Fin P.r → ℂ, c = c') :
    HerA.Gens (ParameterFamilyAlgebra.goodAlg z z' π π') L st := by
  obtain ⟨κ, hx, hxi, -⟩ :=
    xKappaOfNF Formalism.FourierDecayAlt.P.normal_form_actual kappaFibrePos Wp Wq P z z' π π' X μ L st l0 hD
  have hT : 0 ≤ Tz P.k P.r z * Tz P.k P.r z' := Formalism.FourierDecayAlt.P.Qx5.place_alt_alt hD.1
  obtain ⟨-, -, hAL, hQQ, -, -, -, hst⟩ := hD
  have hF : ∀ i j, Q.mkP (X.fn i) (X.fn j) ∈ ParameterFamilyAlgebra.goodAlg z z' π π' := fun i j =>
    ParameterFamilyAlgebra.good_mkP (hfn P.k P.r z z' Wp Wq π π' hT X i) (hfn P.k P.r z z' Wp Wq π π' hT X j)
  have hz : ∀ g ∈ zfns L, g ∈ ParameterFamilyAlgebra.goodAlg z z' π π' := by
    obtain ⟨-, -, -, -, -, -, h1, h2, h3, h4, h5, h6, -⟩ := hAL
    intro g hg
    simp only [zfns, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h1]; exact hF _ _
    · rw [h2]; exact hF _ _
    · rw [h3]; exact hF _ _
    · rw [h4]; exact hF _ _
    · rw [h5]; exact hF _ _
    · rw [h6]; exact hF _ _
  have hQ : ∀ Y : ℂ, star Y = Y → ∀ i j, st.QQ Y i j ∈ ParameterFamilyAlgebra.goodAlg z z' π π' := by
    intro Y _ i j
    rw [hQQ Y, Matrix.smul_apply]
    refine (ParameterFamilyAlgebra.goodAlg z z' π π').smul_mem ?_ _
    exact ParameterFamilyAlgebra.good_mkP (ht P.k P.r z z' Wp Wq π π' hOm hS X Y i j) (ht P.k P.r z z' Wp Wq π π' hOm hS X _ j i)
  exact HerA.gens_of _ L st hst κ _ hx hxi hz hQ

theorem frameParam_of (hfn : GoodFnLeaf) (ht : GoodTLeaf) : PBI.FrameParam := by
  intro Wp Wq _ _ _ _ _ _ P p X μ L st hD w hA Par _ _ _ _ _ U₀ hU₀ hUpos Ψ Ψf hR hF
  have hr0 : ∀ l : Fin (JC.parLev P P.r).r, False := fun l => by
    have := l.isLt
    simp only [JC.parLev, Nat.sub_self] at this
    omega
  have hOm : ∀ c : Fin (JC.parLev P P.r).r → ℂ, c ∈ OmX (JC.parLev P P.r).r := fun c l => (hr0 l).elim
  have hS : ∀ c c' : Fin (JC.parLev P P.r).r → ℂ, c = c' := fun c c' => funext fun l => (hr0 l).elim
  have hg := gens_good hfn ht (JC.parLev P P.r) _ _ _ _ X μ L st p.l0 hD hOm hS
  have hent : ∀ e e', ParameterFamilyAlgebra.Good _ _ _ _ ((Fr.ofWord L st (D.positionted w)).F e e').1 := fun e e' =>
    ((HerA.frameAlg L st hD.2.2.2.2.2.2.1 hD.2.2.2.2.2.2.2 hg (D.positionted w) hA e e').1).1
  have key := fun e b => hent e b Par U₀ hU₀ hUpos (fun Z => Ψ Z b) (fun Z y => Ψf Z b y)
    (fun Z c y hy => hR Z b c y hy) (hF b)
  choose Φ hΦR hΦF hΦS hΦW using key
  refine ⟨fun Z e y => ∑ b, Φ e b Z y, ?_, ?_, ?_, ?_⟩
  · intro Z e c y hy
    simp only [P5.act, Submodule.coe_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun b _ => hΦR e b Z c y hy
  · intro e
    exact ParameterFamilyAlgebra.parFam_sum _ fun b _ => hΦF e b
  · intro K hK e q hq hG hqK
    exact Finset.sum_eq_zero fun b _ => hΦS e b K (fun q' hG' hq' => hK b q' hG' hq') q hq hG hqK
  · intro ν _ Kp hKp hν Ψi y V hV hyV hyG hKV hi e c
    simp only [P5.act, Submodule.coe_sum, Finset.sum_apply]
    rw [integral_finsetSum _ (fun b _ => ParameterFamilyAlgebra.parFam_integrable (hΦF e b) hKp hν hyG
      (fun Z hZ => hKV ⟨hZ, hyV⟩))]
    exact Finset.sum_congr rfl fun b _ => hΦW e b ν Kp hKp hν (Ψi b) y V hV hyV hyG hKV
      (fun c' y' hy' hG' => hi b c' y' hy' hG') c

end Asm

end Formalism.FourierDecayAlt.P.CutFP
end
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt MeasureTheory

namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem sgs_of_invP (p : B.SS k r) (hp1 : IsUnit (Matrix.of p.1.1 : B.Mat k r).det)
    (hp2 : IsUnit (Matrix.of p.1.2 : B.Mat k r).det) (hp3 : IsUnit (Matrix.of p.2.1 : B.Mat k r).det)
    (hp4 : IsUnit (Matrix.of p.2.2 : B.Mat k r).det) (x : B.Mat k r) :
    B.sgs p (B.sgs (Formalism.FourierDecayAlt.P.BigCellInversePair.invP p) x) = x := by
  set h : B.Mat k r := Matrix.of p.1.1
  set n : B.Mat k r := Matrix.of p.1.2
  set h' : B.Mat k r := Matrix.of p.2.1
  set n' : B.Mat k r := Matrix.of p.2.2
  have e1 : (Matrix.of (Formalism.FourierDecayAlt.P.BigCellInversePair.invP p).1.1 : B.Mat k r) = h⁻¹ := rfl
  have e2 : (Matrix.of (Formalism.FourierDecayAlt.P.BigCellInversePair.invP p).1.2 : B.Mat k r) = h⁻¹ * n⁻¹ * h := rfl
  have e3 : (Matrix.of (Formalism.FourierDecayAlt.P.BigCellInversePair.invP p).2.1 : B.Mat k r) = h'⁻¹ := rfl
  have e4 : (Matrix.of (Formalism.FourierDecayAlt.P.BigCellInversePair.invP p).2.2 : B.Mat k r) = h'⁻¹ * n'⁻¹ * h' := rfl
  unfold B.sgs
  rw [e1, e2, e3, e4]
  show h⁻¹ * n⁻¹ * (h⁻¹⁻¹ * (h⁻¹ * n⁻¹ * h)⁻¹ * x * (h'⁻¹ * n'⁻¹ * h') * h'⁻¹) * n' * h' = x
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hp1,
    Matrix.nonsing_inv_nonsing_inv _ hp2]
  simp only [Matrix.mul_assoc]
  simp only [Matrix.mul_nonsing_inv_cancel_left _ _ hp1, Matrix.nonsing_inv_mul_cancel_left _ _ hp1,
    Matrix.nonsing_inv_mul_cancel_left _ _ hp2, Matrix.mul_nonsing_inv_cancel_left _ _ hp3,
    Matrix.nonsing_inv_mul_cancel_left _ _ hp4, Matrix.nonsing_inv_mul _ hp3, Matrix.mul_one]

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem hs_uni (D : B.RealPlaceData k r Wp Wq) {h h' : B.Mat k r} (hh : h ∈ UWset k r D.z) (hh' : h' ∈ UWset k r D.z')
    (A C : Wq →L[ℂ] Wp) :
    B.hsInner ((D.π h).comp (A.comp (D.π' h'⁻¹))) C =
      B.hsInner A ((D.π h⁻¹).comp (C.comp (D.π' h'⁻¹⁻¹))) := by
  have hi := Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh
  have hi' := Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh'
  have hii' := Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hi'
  have e1 : (D.π h).comp (D.π h⁻¹) = 1 := by
    rw [← D.π_rep.2 h hh h⁻¹ hi, (Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.gv_inv hh.1).1, D.π_rep.1]
  have e2 : (D.π' h'⁻¹⁻¹).comp (D.π' h'⁻¹) = 1 := by
    rw [← D.π'_rep.2 _ hii' _ hi', (Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.gv_inv hi'.1).2, D.π'_rep.1]
  have e1v : ∀ w, D.π h (D.π h⁻¹ w) = w := fun w => by
    have := congrArg (fun T : Wp →L[ℂ] Wp => T w) e1
    simpa using this
  have e2v : ∀ w, D.π' h'⁻¹⁻¹ (D.π' h'⁻¹ w) = w := fun w => by
    have := congrArg (fun T : Wq →L[ℂ] Wq => T w) e2
    simpa using this
  set Z : Wq →L[ℂ] Wp := (D.π h⁻¹).comp (C.comp (D.π' h'⁻¹⁻¹))
  have hC : C = (D.π h).comp (Z.comp (D.π' h'⁻¹)) := by
    ext v
    simp only [Z, ContinuousLinearMap.comp_apply, e2v, e1v]
  calc B.hsInner ((D.π h).comp (A.comp (D.π' h'⁻¹))) C
      = B.hsInner ((D.π h).comp (A.comp (D.π' h'⁻¹))) ((D.π h).comp (Z.comp (D.π' h'⁻¹))) := by rw [← hC]
    _ = B.hsInner (A.comp (D.π' h'⁻¹)) (Z.comp (D.π' h'⁻¹)) :=
        Formalism.FourierDecayAlt.P.PBI.hsInner_comp_left _ (D.π_unitary h hh) _ _
    _ = B.hsInner A Z := Formalism.FourierDecayAlt.P.PBI.hsInner_comp_right _ (D.π'_unitary _ hi') _ _

omit [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] in
theorem sgsM_eq_comp (q : B.SS k r) : Formalism.FourierDecayAlt.P.B7.sgsM q =
    lmulM (k := k) (r := r) (Matrix.of q.1.2 * Matrix.of q.1.1 : B.Mat k r)⁻¹ ∘
      B.rmulF (Matrix.of q.2.2 * Matrix.of q.2.1 : B.Mat k r) := by
  funext x
  have e : B.sgs q (Matrix.of x) = (Matrix.of q.1.2 * Matrix.of q.1.1 : B.Mat k r)⁻¹ *
      (Matrix.of x * (Matrix.of q.2.2 * Matrix.of q.2.1 : B.Mat k r)) := by
    rw [Formalism.FourierDecayAlt.P.B5.sgs_eq, Matrix.mul_assoc]
  exact e

omit [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] in
theorem measurable_rmulF (C : B.Mat k r) : Measurable (B.rmulF C) := by
  have : Continuous (B.rmulF C) := (continuous_id.matrix_mul continuous_const : Continuous fun x : B.Mat k r => x * C)
  exact this.measurable

omit [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] in
theorem measurable_section_inverse (q : B.SS k r) : Measurable (Formalism.FourierDecayAlt.P.B7.sgsM q) := by
  rw [sgsM_eq_comp]
  exact (Formalism.QuantumDeterminants.BesselUnitaryEquiv.continuous_lmulM _).measurable.comp (measurable_rmulF _)

theorem map_sgs (D : B.RealPlaceData k r Wp Wq) {q : B.SS k r} (hq : D.inSS q) :
    D.μG.map (Formalism.FourierDecayAlt.P.B7.sgsM q) = D.μG := by
  have hA := Formalism.FourierDecayAlt.P.NFRadRedLocSec.uh_inv_mem (Formalism.FourierDecayAlt.P.B5.inSS_left D hq)
  have hC := Formalism.FourierDecayAlt.P.B5.inSS_right D hq
  have hmr := measurable_rmulF (k := k) (r := r) (Matrix.of q.2.2 * Matrix.of q.2.1 : B.Mat k r)
  rw [sgsM_eq_comp, ← Measure.map_map (Formalism.QuantumDeterminants.BesselUnitaryEquiv.continuous_lmulM _).measurable hmr, D.haarG.right _ hC,
    D.haarG.left _ hA]

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AC

namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem sgsM_left (p : B.SS k r) (hp1 : IsUnit (Matrix.of p.1.1 : B.Mat k r).det)
    (hp2 : IsUnit (Matrix.of p.1.2 : B.Mat k r).det) (hp3 : IsUnit (Matrix.of p.2.1 : B.Mat k r).det)
    (hp4 : IsUnit (Matrix.of p.2.2 : B.Mat k r).det) (x : Mt k r) :
    Formalism.FourierDecayAlt.P.B7.sgsM p (Formalism.FourierDecayAlt.P.B7.sgsM (Formalism.FourierDecayAlt.P.BigCellInversePair.invP p) x) = x := by
  have := sgs_of_invP p hp1 hp2 hp3 hp4 (Matrix.of x)
  exact this

theorem sgsM_right (p : B.SS k r) (hp1 : IsUnit (Matrix.of p.1.1 : B.Mat k r).det)
    (hp2 : IsUnit (Matrix.of p.1.2 : B.Mat k r).det) (hp3 : IsUnit (Matrix.of p.2.1 : B.Mat k r).det)
    (hp4 : IsUnit (Matrix.of p.2.2 : B.Mat k r).det) (x : Mt k r) :
    Formalism.FourierDecayAlt.P.B7.sgsM (Formalism.FourierDecayAlt.P.BigCellInversePair.invP p) (Formalism.FourierDecayAlt.P.B7.sgsM p x) = x := by
  have := Formalism.FourierDecayAlt.P.BigCellInversePair.sgs_invP p hp1 hp2 hp3 hp4 (Matrix.of x)
  exact this

noncomputable def sgsE (p : B.SS k r) (hp1 : IsUnit (Matrix.of p.1.1 : B.Mat k r).det)
    (hp2 : IsUnit (Matrix.of p.1.2 : B.Mat k r).det) (hp3 : IsUnit (Matrix.of p.2.1 : B.Mat k r).det)
    (hp4 : IsUnit (Matrix.of p.2.2 : B.Mat k r).det) : Mt k r ≃ᵐ Mt k r where
  toFun := Formalism.FourierDecayAlt.P.B7.sgsM (Formalism.FourierDecayAlt.P.BigCellInversePair.invP p)
  invFun := Formalism.FourierDecayAlt.P.B7.sgsM p
  left_inv := sgsM_left p hp1 hp2 hp3 hp4
  right_inv := sgsM_right p hp1 hp2 hp3 hp4
  measurable_toFun := measurable_section_inverse _
  measurable_invFun := measurable_section_inverse _

theorem sgsE_coe (p : B.SS k r) (hp1 hp2 hp3 hp4) :
    ⇑(sgsE (k := k) (r := r) p hp1 hp2 hp3 hp4) = Formalism.FourierDecayAlt.P.B7.sgsM (Formalism.FourierDecayAlt.P.BigCellInversePair.invP p) := rfl

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AC

namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS

open Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem unitary_rho_holds : RhoUni := by
  intro k r Wp Wq _ _ _ _ _ _ D p hp
  refine ⟨Formalism.FourierDecayAlt.P.BigCellInversePair.invP p, Formalism.FourierDecayAlt.P.BigCellInversePair.invP_inSS D hp, fun X Y => ?_⟩
  have hq := Formalism.FourierDecayAlt.P.BigCellInversePair.invP_inSS D hp
  have u1 := WeylGroupFacts.isUnit_of_uh hp.1.1
  have u2 := WeylGroupFacts.isUnit_of_uh hp.2.1.1
  have u3 := WeylGroupFacts.isUnit_of_uh hp.2.2.1.1
  have u4 := WeylGroupFacts.isUnit_of_uh hp.2.2.2.1
  have hmp : MeasurePreserving (sgsE p u1 u2 u3 u4) D.μG D.μG :=
    ⟨(sgsE p u1 u2 u3 u4).measurable, by rw [sgsE_coe]; exact map_sgs D hq⟩
  rw [← hmp.integral_comp' (fun y : Mt k r => B.hsInner (B.rho D p X (Matrix.of y)) (Y (Matrix.of y)))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show B.hsInner (B.rho D p X (B.sgs (Formalism.FourierDecayAlt.P.BigCellInversePair.invP p) (Matrix.of x)))
      (Y (B.sgs (Formalism.FourierDecayAlt.P.BigCellInversePair.invP p) (Matrix.of x))) =
    B.hsInner (X (Matrix.of x)) (B.rho D (Formalism.FourierDecayAlt.P.BigCellInversePair.invP p) Y (Matrix.of x))
  unfold B.rho
  rw [sgs_of_invP p u1 u2 u3 u4]
  exact hs_uni D hp.1 hp.2.2.1 _ _

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS
end

section

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CompactSupportClassLemmas

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.JFxG

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem compact_support_in_class_general (D : RealPlaceData k r Wp Wq) (Θ : DiffOp k r Wp Wq) (hS : SmoothCoef (GPos D) Θ)
    (hC : Commutes D (GPos D) Θ) (F F' : Mat k r → (Wq →L[ℂ] Wp))
    (hF : CkOn ⊤ (GV k r) F) (hFc : HasCompactSupport F) (hFO : ∀ g ∈ tsupport F, g ∈ GV k r → g ∈ GPos D)
    (hF' : CkOn ⊤ (GV k r) F') (hF'c : HasCompactSupport F') (hF'O : ∀ g ∈ tsupport F', g ∈ GV k r → g ∈ GPos D) :
    InCC (AB k r) 5 F ∧ InCC (AB k r) 5 F' ∧ InCC (AB k r) 5 (opApply Θ F) ∧ InCC (AB k r) 5 (opAdj Θ F') ∧
      beta D (opApply Θ F) F' = beta D F (opAdj Θ F') := by
  set C : Set (Mat k r) := tsupport F with hCdef
  set C' : Set (Mat k r) := tsupport F' with hC'def
  have hCc : IsCompact C := hFc
  have hC'c : IsCompact C' := hF'c
  obtain ⟨_, _, _, _, _, hL3, _⟩ := Formalism.FourierDecayAlt.P.b_any_of_xi k r Wp Wq D (AB k r) le_rfl
  have supp : ∀ {φ : Mat k r → (Wq →L[ℂ] Wp)} {K : Set (Mat k r)}, IsCompact K →
      (∀ g ∈ K, g ∈ GV k r → g ∈ GPos D) →
      (∀ g ∈ GV k r, g ∉ K → φ g = 0) → closure {g | g ∈ GV k r ∧ φ g ≠ 0} ⊆ GPos D :=
    by
    intro φ K hK hKO hz
    exact (closure_minimal (s := {g | g ∈ GV k r ∧ φ g ≠ 0}) (t := K ∩ GV k r) (fun g hg => by
      refine ⟨?_, hg.1⟩
      by_contra hgK
      exact hg.2 (hz g hg.1 hgK)) (hK.isClosed.inter Formalism.FourierDecayAlt.P.B5.GV_closed)).trans (fun g hg => hKO g hg.1 hg.2)
  have rwz : ∀ {φ : Mat k r → (Wq →L[ℂ] Wp)} {K : Set (Mat k r)}, IsCompact K →
      (∀ g ∈ GV k r, g ∉ K → φ g = 0) → ∀ w : List (Mat k r), (∀ X ∈ w, inLie k r X) →
        ∀ g ∈ GV k r, g ∉ K → Rw w φ g = 0 :=
    fun hK hz w hw g hg hgK => Formalism.FourierDecayAlt.P.BetaSesquilinearity.Rw_vanish hK.isClosed.isOpen_compl hw (fun x hx hxK => hz x hx hxK) g hg hgK
  have hFz : ∀ g ∈ GV k r, g ∉ C → F g = 0 := fun g _ h => image_eq_zero_of_notMem_tsupport h
  have hF'z : ∀ g ∈ GV k r, g ∉ C' → F' g = 0 := fun g _ h => image_eq_zero_of_notMem_tsupport h
  have hap : ∀ T ∈ Θ, CkOn ⊤ (GV k r) (fun x => T.coefAdj x (F' x)) ∧
      ∀ g ∈ GV k r, g ∉ C' → T.coefAdj g (F' g) = 0 := fun T hT =>
    ⟨Formalism.FourierDecayAlt.P.B5.ckOn_coef (hS T hT).2 hF' (supp hC'c hF'O hF'z), fun g hg hgK => by rw [hF'z g hg hgK, map_zero]⟩
  have hrev : ∀ T ∈ Θ, ∀ X ∈ T.word.reverse, inLie k r X := fun T _ X hX => T.word_lie X (List.mem_reverse.1 hX)
  have hΘF : InCC (AB k r) 5 (opApply Θ F) := by
    show InCC _ 5 (fun g => (Θ.map fun T => T.coef g (Rw T.word F g)).sum)
    refine Formalism.FourierDecayAlt.P.BetaSesquilinearity.InCC_opsum Θ (fun T g => T.coef g (Rw T.word F g)) fun T hT => ?_
    exact cptInCC_G (Formalism.FourierDecayAlt.P.B5.ckOn_coef (hS T hT).1 (ckOn_Rw_top hF T.word T.word_lie)
        (supp hCc hFO (rwz hCc hFz T.word T.word_lie))) hCc
      (fun g hg hgK => by
        show T.coef g (Rw T.word F g) = 0
        rw [rwz hCc hFz T.word T.word_lie g hg hgK, map_zero]) _ 5
  have hΘF' : InCC (AB k r) 5 (opAdj Θ F') := by
    show InCC _ 5 (fun g => (Θ.map fun T =>
      ((-1 : ℂ) ^ T.word.length) • Rw T.word.reverse (fun x => T.coefAdj x (F' x)) g).sum)
    refine Formalism.FourierDecayAlt.P.BetaSesquilinearity.InCC_opsum Θ
      (fun T g => ((-1 : ℂ) ^ T.word.length) • Rw T.word.reverse (fun x => T.coefAdj x (F' x)) g) fun T hT => ?_
    exact cptInCC_G (ckOn_smul ((-1 : ℂ) ^ T.word.length) (ckOn_Rw_top (hap T hT).1 _ (hrev T hT))) hC'c
      (fun g hg hgK => by
        show ((-1 : ℂ) ^ T.word.length) • Rw T.word.reverse (fun x => T.coefAdj x (F' x)) g = 0
        rw [rwz hC'c (hap T hT).2 _ (hrev T hT) g hg hgK, smul_zero]) _ 5
  have hIC : IntClause D Θ F F' := by
    intro p hp T hT i j hij hj
    have hlie1 : ∀ X ∈ (T.word.take i).reverse, inLie k r X := fun X hX =>
      T.word_lie X (List.mem_of_mem_take (List.mem_reverse.mp hX))
    have hlie2 : ∀ X ∈ T.word.drop j, inLie k r X := fun X hX => T.word_lie X (List.mem_of_mem_drop hX)
    set f₁ : Mat k r → (Wq →L[ℂ] Wp) := Rw (T.word.take i).reverse (fun x => T.coefAdj x (F' x)) with hf₁
    set f₂ : Mat k r → (Wq →L[ℂ] Wp) := Rw (T.word.drop j) (rho D p F) with hf₂
    have hf₁c : CkOn ⊤ (GV k r) f₁ := ckOn_Rw_top (hap T hT).1 _ hlie1
    have hf₁z : ∀ g ∈ GV k r, g ∉ C' → f₁ g = 0 := rwz hC'c (hap T hT).2 _ hlie1
    obtain ⟨K₁, hK₁⟩ := cptInCC_G hf₁c hC'c hf₁z 0 0
    have hb₁ : ∀ g ∈ GV k r, ‖f₁ g‖ ≤ K₁ := by
      intro g hg
      have := hK₁.2 [] [] (by simp) (by simp) (by simp) g hg
      simpa [Real.rpow_zero, dLR, Rw] using this
    have hf₂c : ContinuousOn f₂ (GV k r) :=
      Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_cont subset_rfl (Formalism.FourierDecayAlt.P.B5.ckOn_mono bot_le
        (ckOn_Rw_top (Formalism.FourierDecayAlt.P.B5.ckOn_rho D hp hF) _ hlie2))
    have hf₁cont : ContinuousOn f₁ (GV k r) :=
      Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_cont subset_rfl (Formalism.FourierDecayAlt.P.B5.ckOn_mono bot_le hf₁c)
    obtain ⟨K₂, hK₂⟩ := (hC'c.inter_right Formalism.FourierDecayAlt.P.B5.GV_closed).exists_bound_of_continuousOn
      (hf₂c.mono Set.inter_subset_right)
    set G : Mat k r → (Wq →L[ℂ] Wp) := fun g => ((‖f₂ g‖ : ℝ) : ℂ) • f₁ g with hG
    have hGn : ∀ g, ‖G g‖ = ‖f₁ g‖ * ‖f₂ g‖ := by
      intro g
      simp only [hG, norm_smul, Complex.norm_real, norm_norm]
      ring
    have hGc : ContinuousOn G (GV k r) := (Complex.continuous_ofReal.comp_continuousOn hf₂c.norm).smul hf₁cont
    have hGm := Formalism.FourierDecayAlt.P.BetaSesquilinearity.aesm_of_continuousOn D hGc
    have hfin : D.μG (C' : Set (Mt k r)) ≠ ⊤ := (D.haarG.finite_compact C' hC'c).ne
    have hind : Integrable ((C' : Set (Mt k r)).indicator fun _ => K₁ * K₂) D.μG :=
      (integrableOn_const hfin).integrable_indicator (IsClosed.measurableSet (α := Mt k r) hC'c.isClosed)
    have hint : Integrable (fun g : Mt k r => G (Matrix.of g)) D.μG := by
      refine hind.mono' hGm ?_
      filter_upwards [Formalism.FourierDecayAlt.P.B5.haar_ae D.haarG] with x hx
      by_cases hxC : x ∈ (C' : Set (Mt k r))
      · rw [Set.indicator_of_mem hxC, hGn]
        have h1 := hb₁ (Matrix.of x) hx
        have h2 := hK₂ (Matrix.of x) ⟨hxC, hx⟩
        exact mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
      · rw [Set.indicator_of_notMem hxC, hGn, hf₁z (Matrix.of x) hx hxC, norm_zero, zero_mul]
    exact hint.norm.congr (Filter.Eventually.of_forall fun g => hGn _)
  have hIF := cptInCC_G hF hCc hFz (AB k r) 5
  have hIF' := cptInCC_G hF' hC'c hF'z (AB k r) 5
  exact ⟨hIF, hIF', hΘF, hΘF', hL3 (GPos D) Θ (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gPos_stable D) hS hC F F'
    (Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top hF) (Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top hF')
    (supp hCc hFO hFz) (supp hC'c hF'O hF'z) hIF hIF' hΘF hΘF' hIC⟩

end Formalism.FourierDecayAlt.P.CompactSupportClassLemmas

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

theorem compact_support_lemma_three : CompactSupportClassMembership := by
  refine ⟨0, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ _hB v Θ hΘ F F' hF hFc hFO hF' hF'c hF'O
  exact Formalism.FourierDecayAlt.P.CompactSupportClassLemmas.compact_support_in_class_general (T v).base Θ hΘ.1 hΘ.2 F F' hF hFc
    (fun g hg hgG => ⟨hgG, (hFO hg).1⟩) hF' hF'c (fun g hg hgG => ⟨hgG, (hF'O hg).1⟩)

end Formalism.FourierDecayAlt.P.CutMP.JA.SA

end
end

section

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.LevelPointCoordinates

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

theorem kapJ_eq (P : M.Par) (j : ℕ) : kapJ P j = levelZeroKernel P.k P.r j := rfl

theorem headJ_of (hW : WordInd) (hB : HeadBridge) : HeadJ := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj w h hh γ hF hw hγ hγ' φ hφ t ht e
  obtain ⟨X, _, μ, ℓ, Zx, Fx, Dm, φx, hDm, hDmsub, hR, hZ, hφx, hL, hRt⟩ :=
    hB Wp Wq P p F j hj w h hh γ hF hw hγ hγ' φ hφ t ht e
  have ht0 : t ≠ 0 := (ht.1 (1, t) (by simp)).2
  rw [hL, hRt]
  congr 1
  funext x
  rw [hW P.k P.r j hj _ _ (Wq →L[ℂ] Wp) Dm (Fx x) p.T.base.z_mem p.T.base.z'_mem hDm hDmsub (hR x) (Zx x) γ
    (hZ x).1 hγ (hZ x).2 w (φx x) (hφx x) t ht0 e, kapJ_eq]

end Formalism.FourierDecayAlt.P.LevelPointCoordinates
end
end

section

namespace Formalism.FourierDecayAlt.P

theorem phi_zero_hermitian_curvature : Formalism.FourierDecayAlt.KB.PhiZero :=
  phi_zero_of_parts pbi_sectionExists_proof fibre_integral_smooth fibre_integral_cells

theorem density_constant : Formalism.FourierDecayAlt.KB.DensC :=
  pb_densC_of phi_zero_hermitian_curvature vector_vanishes_big_cell

end Formalism.FourierDecayAlt.P
end
