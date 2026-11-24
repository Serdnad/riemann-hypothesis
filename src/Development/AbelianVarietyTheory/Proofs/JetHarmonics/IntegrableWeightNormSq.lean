module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableOfDecay4
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGWave
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActOneVariableSmul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BXiAsm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHLFinal
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadGermSmoothExtension
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadJacquetOfLetterAndHead
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ModuleFormEqRadialFormOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PbRadHeadOf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositiveDensityModerateGrowth
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.FormsFromXi

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P

variable (hXi : B.XiExists)
include hXi

section beta

open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.JCx2 Formalism.FourierDecayAlt.P.JCx4
open scoped ComplexConjugate

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section
variable {k r : ℕ}
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem beta_sesq (D : RealPlaceData k r Wp Wq) {A : ℝ} (hA : AB k r ≤ A) {F F' G : Mat k r → (Wq →L[ℂ] Wp)}
    (hF : InCC A 5 F) (hF' : InCC A 5 F') (hG : InCC A 5 G) (c : ℂ) :
    beta D (F + c • F') G = beta D F G + c * beta D F' G ∧
      beta D G (F + c • F') = beta D G F + conj c * beta D G F' := by
  apply _root_.Formalism.FourierDecayAlt.P.JCx2.sq_beta_sesq <;> assumption

theorem integrable_weight_normSq (D : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (hF : ∀ (A : ℝ) (m : ℕ), B.InCC A m F) :
    Integrable (fun q => bcWeight k r (Tz k r D.z) (Tz k r D.z') q * ‖B.hsVec (B.JF D F (B.gq D q))‖ ^ 2) := by
  apply _root_.Formalism.FourierDecayAlt.P.JCx2.rb_int_sq <;> assumption

theorem integrable_weight_pair (D : B.RealPlaceData k r Wp Wq) (F F' : B.Mat k r → (Wq →L[ℂ] Wp))
    (hF : ∀ (A : ℝ) (m : ℕ), B.InCC A m F) (hF' : ∀ (A : ℝ) (m : ℕ), B.InCC A m F') :
    Integrable (fun q => (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) *
      inner ℂ (B.hsVec (B.JF D F' (B.gq D q))) (B.hsVec (B.JF D F (B.gq D q)))) := by
  apply _root_.Formalism.FourierDecayAlt.P.JCx2.rb_int_pair <;> assumption

theorem form_eq_sum_beta (D : B.RealPlaceData k r Wp Wq) (μ : Measure (Mt k r)) (C1 : ℝ)
    (hpair : ∀ (F F' : B.Mat k r → (Wq →L[ℂ] Wp)) (Φ Φ' : Q.RadSp k r D.z D.z' D.π D.π'),
      (∀ y ∈ Q.DomR k r D.z D.z',
        (Φ : Q.Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 = Q.resG k r (Fin.last r) (B.JF D F) y.1 y.2) →
      (∀ y ∈ Q.DomR k r D.z D.z',
        (Φ' : Q.Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 = Q.resG k r (Fin.last r) (B.JF D F') y.1 y.2) →
      ∀ c ∈ OmX r, P5.pairAt μ Φ Φ' c = (C1 : ℂ) * ∫ ζ, (B2.zWeight k (Tz k r D.z) (Tz k r D.z') ζ : ℂ) *
        (((rbGauge k r c ^ 2 : ℝ) : ℂ) * B.hsInner (B.JF D F (B.gq D (c, ζ))) (B.JF D F' (B.gq D (c, ζ)))))
    {n : ℕ} (x x' : Wd.Ix (Fin n) → B.Mat k r → (Wq →L[ℂ] Wp)) (Φ Φ' : Wd.Ix (Fin n) → Q.RadSp k r D.z D.z' D.π D.π')
    (hx : ∀ a, ∀ (A : ℝ) (m : ℕ), B.InCC A m (x a)) (hx' : ∀ a, ∀ (A : ℝ) (m : ℕ), B.InCC A m (x' a))
    (hΦ : ∀ a, ∀ y ∈ Q.DomR k r D.z D.z',
      (Φ a : Q.Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 = Q.resG k r (Fin.last r) (B.JF D (x a)) y.1 y.2)
    (hΦ' : ∀ a, ∀ y ∈ Q.DomR k r D.z D.z',
      (Φ' a : Q.Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 = Q.resG k r (Fin.last r) (B.JF D (x' a)) y.1 y.2) :
    P5.form μ 0 Φ Φ' 0 = (C1 : ℂ) * ∑ a, B.beta D (x a) (x' a) := by
  apply _root_.Formalism.FourierDecayAlt.P.JCx2.rb_main <;> assumption

end

theorem formLev_sesq {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P0 : M.Par)
    (T : D.LevTower P0.k P0.r Wp Wq) (s : ℂ) (j : Fin (P0.r + 1)) (w : List C.Letter) (A : ℝ) (mm : ℕ)
    (hA : P5.Auser P0 w.length + 1 ≤ A) (hmm : P5.mmUser P0 w.length ≤ mm)
    (x x' y : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ)
    (hx : ∀ a, InCC A mm (x a)) (hx' : ∀ a, InCC A mm (x' a)) (hy : ∀ a, InCC A mm (y a)) :
    D.formLev T s j w (x + c • x') y = D.formLev T s j w x y + c * D.formLev T s j w x' y ∧
      D.formLev T s j w y (x + c • x') = D.formLev T s j w y x + starRingEnd ℂ c * D.formLev T s j w y x' := by
  apply _root_.Formalism.FourierDecayAlt.P.JCx4.formLev_sesq_core <;> assumption

end beta

section one

open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.JCx2 Formalism.FourierDecayAlt.P.PBF
open scoped ENNReal NNReal Matrix

theorem form_const_one : Formalism.FourierDecayAlt.P.PBO.FormOne := by
  apply _root_.Formalism.FourierDecayAlt.P.PBF.formOne <;> assumption

end one

theorem radHead : KB.RadHead :=
  pb_radHead_of (form_const_one hXi) exists_zeta_normalized_haar
    (PBP.headPic_of (head_jacquet_of_letter_and_head head_letter_identity head_germ_smooth_extension))

section wave

open Matrix Finset Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.PBG
open scoped ComplexConjugate

section pairing

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  (P0 : M.Par) (T : D.LevTower P0.k P0.r Wp Wq) (s : ℂ) (j : Fin (P0.r + 1)) (w : List C.Letter)

theorem formLev_add_smul_left (x₁ x₂ y : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ)
    (h₁ : DecV x₁) (h₂ : DecV x₂) (hy : DecV y) :
    D.formLev T s j w (x₁ + c • x₂) y = D.formLev T s j w x₁ y + c * D.formLev T s j w x₂ y :=
  (formLev_sesq hXi P0 T s j w _ _ le_rfl le_rfl x₁ x₂ y c (fun a => h₁ a _ _)
    (fun a => h₂ a _ _) (fun a => hy a _ _)).1

theorem formLev_add_smul_right (x y₁ y₂ : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ)
    (hx : DecV x) (h₁ : DecV y₁) (h₂ : DecV y₂) :
    D.formLev T s j w x (y₁ + c • y₂) = D.formLev T s j w x y₁ + conj c * D.formLev T s j w x y₂ :=
  (formLev_sesq hXi P0 T s j w _ _ le_rfl le_rfl y₁ y₂ x c (fun a => h₁ a _ _)
    (fun a => h₂ a _ _) (fun a => hx a _ _)).2

theorem pairing_add_smul_left : ∀ (ys : List ℝ) (x₁ x₂ : Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp))
    (y : Wd.Ix (Fin (KB.minusW ys w).length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ),
    DecV x₁ → DecV x₂ → DecV y →
    KB.pairJ (D.formLev T s j w) ys (x₁ + c • x₂) y =
      KB.pairJ (D.formLev T s j w) ys x₁ y + c * KB.pairJ (D.formLev T s j w) ys x₂ y
  | [], x₁, x₂, y, c, h₁, h₂, hy => formLev_add_smul_left hXi P0 T s j w x₁ x₂ y c h₁ h₂ hy
  | _ :: ys, x₁, x₂, y, c, h₁, h₂, hy => by
    simp only [KB.pairJ]
    have e1 := pairing_add_smul_left ys (fun e => x₁ (Fin.cons 1 e)) (fun e => x₂ (Fin.cons 1 e)) (fun e => y (Fin.cons 0 e))
      c (decV_restrict h₁ 1) (decV_restrict h₂ 1) (decV_restrict hy 0)
    have e0 := pairing_add_smul_left ys (fun e => x₁ (Fin.cons 0 e)) (fun e => x₂ (Fin.cons 0 e)) (fun e => y (Fin.cons 1 e))
      c (decV_restrict h₁ 0) (decV_restrict h₂ 0) (decV_restrict hy 1)
    have r1 : (fun e => (x₁ + c • x₂) (Fin.cons 1 e)) = (fun e => x₁ (Fin.cons 1 e)) + c • (fun e => x₂ (Fin.cons 1 e)) := rfl
    have r0 : (fun e => (x₁ + c • x₂) (Fin.cons 0 e)) = (fun e => x₁ (Fin.cons 0 e)) + c • (fun e => x₂ (Fin.cons 0 e)) := rfl
    rw [r1, r0, e1, e0]
    ring

theorem pairing_add_smul_right : ∀ (ys : List ℝ) (x : Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp))
    (y₁ y₂ : Wd.Ix (Fin (KB.minusW ys w).length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ),
    DecV x → DecV y₁ → DecV y₂ →
    KB.pairJ (D.formLev T s j w) ys x (y₁ + c • y₂) =
      KB.pairJ (D.formLev T s j w) ys x y₁ + conj c * KB.pairJ (D.formLev T s j w) ys x y₂
  | [], x, y₁, y₂, c, hx, h₁, h₂ => formLev_add_smul_right hXi P0 T s j w x y₁ y₂ c hx h₁ h₂
  | _ :: ys, x, y₁, y₂, c, hx, h₁, h₂ => by
    simp only [KB.pairJ]
    have e1 := pairing_add_smul_right ys (fun e => x (Fin.cons 1 e)) (fun e => y₁ (Fin.cons 0 e)) (fun e => y₂ (Fin.cons 0 e))
      c (decV_restrict hx 1) (decV_restrict h₁ 0) (decV_restrict h₂ 0)
    have e0 := pairing_add_smul_right ys (fun e => x (Fin.cons 0 e)) (fun e => y₁ (Fin.cons 1 e)) (fun e => y₂ (Fin.cons 1 e))
      c (decV_restrict hx 0) (decV_restrict h₁ 1) (decV_restrict h₂ 1)
    have r0 : (fun e => (y₁ + c • y₂) (Fin.cons 0 e)) = (fun e => y₁ (Fin.cons 0 e)) + c • (fun e => y₂ (Fin.cons 0 e)) := rfl
    have r1 : (fun e => (y₁ + c • y₂) (Fin.cons 1 e)) = (fun e => y₁ (Fin.cons 1 e)) + c • (fun e => y₂ (Fin.cons 1 e)) := rfl
    rw [r1, r0, e1, e0]
    ring

theorem pairing_sum_sum (ys : List ℝ) {ι ι' : Type} (S : Finset ι) (S' : Finset ι') (a : ι → ℂ) (b : ι' → ℂ)
    (v : ι → Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp))
    (u : ι' → Wd.Ix (Fin (KB.minusW ys w).length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp))
    (hv : ∀ i, DecV (v i)) (hu : ∀ i, DecV (u i)) :
    KB.pairJ (D.formLev T s j w) ys (∑ i ∈ S, a i • v i) (∑ i ∈ S', b i • u i) =
      ∑ i ∈ S, ∑ i' ∈ S', a i * conj (b i') * KB.pairJ (D.formLev T s j w) ys (v i) (u i') := by
  apply _root_.Formalism.FourierDecayAlt.P.PBG.pairJ_sum_sum <;> assumption

end pairing

section deg

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
variable {P : M.Par} (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (j : ℕ) (hj : j ≤ P.r)
  (w : List C.Letter) (h h' : C.LPt) (hh : D.ptSize h = j) (hh' : D.ptSize h' = j) (s : ℂ)
  (Mo : (Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) →ₗ[ℂ]
      (Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)))

end deg

end wave

end GlobalTheory.FormsFromXi

end
