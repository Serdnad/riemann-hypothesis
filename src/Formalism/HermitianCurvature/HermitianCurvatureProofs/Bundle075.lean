module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle072
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CvRhoOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RepIntCastMul
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle004
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGerm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TendstoRatioPow
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HasDerivAtInvpow
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentComposition.HasDerivAtInvpow
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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

open Matrix Finset
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity Formalism.FourierDecayAlt.P.JFxB

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem dx_repF {X : Mat k r} (hX : inLie k r X) {φ F : Mat k r → E} {F' : Mat k r →L[ℝ] E} {U : Set (Mat k r)}
    {g : Mat k r} (hU : IsOpen U) (hgU : g ∈ U) (hg : g ∈ GV k r) (hF : HasFDerivAt F F' g)
    (hff : ∀ h ∈ U, h ∈ GV k r → φ h = F h) : Dx (false, X) φ g = F' (g * X) := by
  rw [← dx_false]
  have hc := Formalism.REAL.hasDerivAt_mul_exp_smul_zero g X
  have hF0 : HasFDerivAt F F' (g * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) := by simpa using hF
  have hcomp : HasDerivAt (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X))) (F' (g * X)) 0 :=
    hF0.comp_hasDerivAt (0 : ℝ) hc
  have hU0 : U ∈ nhds (g * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) := by simpa using hU.mem_nhds hgU
  have hev : (fun t : ℝ => φ (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[nhds 0]
      fun t => F (g * NormedSpace.exp ((t : ℂ) • X)) := by
    filter_upwards [hc.continuousAt.preimage_mem_nhds hU0] with t ht
    exact hff _ ht (Formalism.FourierDecayAlt.P.B5.curve_mem hg hX t)
  exact (hcomp.congr_of_eventuallyEq hev).deriv

theorem EH_psi {φ F : Mat k r → E} {F' : Mat k r →L[ℝ] E} {U : Set (Mat k r)}
    {g : Mat k r} (hU : IsOpen U) (hgU : g ∈ U) (hg : g ∈ GV k r) (hF : HasFDerivAt F F' g)
    (hff : ∀ h ∈ U, h ∈ GV k r → φ h = F h) (a b : Fin (2 * r + k + 1)) :
    Q.EH k r a b φ g = Psi F' g (Matrix.single a b 1) := by
  have h1 : RdV (Xa k r a b) φ g = F' (g * Xa k r a b) := dx_repF (Xa_lie a b) hU hgU hg hF hff
  have h2 : RdV (Xb k r a b) φ g = F' (g * Xb k r a b) := dx_repF (Xb_lie a b) hU hgU hg hF hff
  show RdV (Xa k r a b) φ g + Complex.I • RdV (Xb k r a b) φ g =
    F' (g * Xa k r a b) + Complex.I • F' (g * Xb k r a b)
  rw [h1, h2]

private theorem inLie_conj_of_mem_GV' {y X : Mat k r} (hy : y ∈ GV k r) (hX : inLie k r X) :
    inLie k r (y⁻¹ * X * y) := by
  have hu : IsUnit y.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hy
  have hy' : yᴴ * Hpk k r * y = Hpk k r := hy
  have h1 : Hpk k r * y⁻¹ = yᴴ * Hpk k r := by
    calc Hpk k r * y⁻¹ = yᴴ * Hpk k r * y * y⁻¹ := by rw [hy']
      _ = yᴴ * Hpk k r := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
  have h2 : (y⁻¹)ᴴ * Hpk k r = Hpk k r * y := by
    calc (y⁻¹)ᴴ * Hpk k r = (y⁻¹)ᴴ * (yᴴ * Hpk k r * y) := by rw [hy']
      _ = (y * y⁻¹)ᴴ * Hpk k r * y := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = Hpk k r * y := by rw [Matrix.mul_nonsing_inv _ hu, Matrix.conjTranspose_one, Matrix.one_mul]
  unfold inLie at hX ⊢
  have e1 : (y⁻¹ * X * y)ᴴ * Hpk k r = yᴴ * (Xᴴ * Hpk k r) * y := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc, h2]
  have e2 : Hpk k r * (y⁻¹ * X * y) = yᴴ * (Hpk k r * X) * y := by
    simp only [← Matrix.mul_assoc]
    rw [h1]
  rw [e1, e2, ← Matrix.add_mul, ← Matrix.mul_add, hX, Matrix.mul_zero, Matrix.zero_mul]

theorem EHc_psi {y : Mat k r} (hy : y ∈ GV k r) {φ F : Mat k r → E} {F' : Mat k r →L[ℝ] E} {U : Set (Mat k r)}
    {g : Mat k r} (hU : IsOpen U) (hgU : g ∈ U) (hg : g ∈ GV k r) (hF : HasFDerivAt F F' g)
    (hff : ∀ h ∈ U, h ∈ GV k r → φ h = F h) (c d : Fin (2 * r + k + 1)) :
    EHc k r y c d φ g = Psi F' g (y⁻¹ * Matrix.single c d 1 * y) := by
  rw [EHc_eq]
  beta_reduce
  rw [dx_repF (inLie_conj_of_mem_GV' hy (Xa_lie c d)) hU hgU hg hF hff,
    dx_repF (inLie_conj_of_mem_GV' hy (Xb_lie c d)) hU hgU hg hF hff]
  have hZ : y⁻¹ * Matrix.single c d 1 * y = y⁻¹ * Xa k r c d * y + Complex.I • (y⁻¹ * Xb k r c d * y) := by
    conv_lhs => rw [← hp_decomp (Matrix.single c d 1)]
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
    all_goals rfl
  obtain ⟨h1, h2⟩ := hp_of_parts (inLie_conj_of_mem_GV' hy (Xa_lie c d)) (inLie_conj_of_mem_GV' hy (Xb_lie c d))
  unfold Psi
  rw [hZ, h1, h2]

theorem conj_single (P Q : Mat k r) (c d : Fin (2 * r + k + 1)) :
    P * Matrix.single c d 1 * Q = ∑ a, ∑ b, (P a c * Q d b) • Matrix.single a b 1 := by
  ext i j
  simp [Matrix.mul_apply, Matrix.single_apply, Matrix.sum_apply, ite_and, mul_ite, ite_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq']

private theorem psi_add_hermitian_curvature (D : Mat k r →L[ℝ] E) (g A B : Mat k r) :
    Psi D g (A + B) = Psi D g A + Psi D g B := by
  have h1 : hpart1 (Hpk k r) (A + B) = hpart1 (Hpk k r) A + hpart1 (Hpk k r) B := by
    simp only [hpart1, Matrix.conjTranspose_add, mul_add, add_mul]
    rw [← smul_add]
    congr 1
    abel
  have h2 : hpart2 (Hpk k r) (A + B) = hpart2 (Hpk k r) A + hpart2 (Hpk k r) B := by
    simp only [hpart2, Matrix.conjTranspose_add, mul_add, add_mul]
    rw [← smul_add]
    congr 1
    abel
  simp only [Psi, h1, h2, mul_add, map_add (f := _), smul_add]
  abel

theorem Psi_sum {ι : Type*} (s : Finset ι) (D : Mat k r →L[ℝ] E) (g : Mat k r) (Z : ι → Mat k r) :
    Psi D g (∑ i ∈ s, Z i) = ∑ i ∈ s, Psi D g (Z i) := by
  exact map_sum (AddMonoidHom.mk' (Psi D g) (psi_add_hermitian_curvature D g)) Z s

theorem rep1 {φ : Mat k r → E} (hφ : CkOn 1 (GV k r) φ) {g : Mat k r} (hg : g ∈ GV k r) :
    ∃ (U : Set (Mat k r)) (F : Mat k r → E), IsOpen U ∧ g ∈ U ∧ HasFDerivAt F (fderiv ℝ F g) g ∧
      ∀ h ∈ U, h ∈ GV k r → φ h = F h := by
  obtain ⟨U, f', hU, hgU, hf', hff⟩ := hφ g hg
  have hd : DifferentiableAt ℝ f' g :=
    (hf'.differentiableOn (by first | exact le_rfl | simp)).differentiableAt (hU.mem_nhds hgU)
  exact ⟨U, f', hU, hgU, hd.hasFDerivAt, hff⟩

theorem EH_HC : HC (Q.EH (E := E) k r) := by
  intro a b m f hf
  have h := EHc_ck (Formalism.QuantumDeterminants.WeylGroupFacts.uh_one (k := k) (r := r)) a b m f hf
  rwa [EHc_one] at h

theorem EH_HL : HL (Q.EH (E := E) k r) := by
  intro a b f f₂ h
  exact EH_congr a b f f₂ h

theorem EH_HA : HA (Q.EH (E := E) k r) := by
  intro a b f f₂ hf hf₂ g hg
  obtain ⟨U, F, hU, hgU, hF, hff⟩ := rep1 hf hg
  obtain ⟨U₂, F₂, hU₂, hgU₂, hF₂, hff₂⟩ := rep1 hf₂ hg
  rw [EH_psi (φ := fun x => f x + f₂ x) (hU.inter hU₂) ⟨hgU, hgU₂⟩ hg (hF.add hF₂)
      (fun h hh hG => by simp only [hff h hh.1 hG, hff₂ h hh.2 hG, Pi.add_apply]) a b,
    EH_psi hU hgU hg hF hff a b, EH_psi hU₂ hgU₂ hg hF₂ hff₂ a b]
  simp only [Psi]
  show fderiv ℝ F g (g * hpart1 (Hpk k r) (Matrix.single a b 1)) +
      fderiv ℝ F₂ g (g * hpart1 (Hpk k r) (Matrix.single a b 1)) +
      Complex.I • (fderiv ℝ F g (g * hpart2 (Hpk k r) (Matrix.single a b 1)) +
        fderiv ℝ F₂ g (g * hpart2 (Hpk k r) (Matrix.single a b 1))) = _
  rw [smul_add]
  abel

theorem EH_HS : HS (Q.EH (E := E) k r) := by
  intro a b c f hf g hg
  obtain ⟨U, F, hU, hgU, hF, hff⟩ := rep1 hf hg
  rw [EH_psi (φ := fun x => c • f x) hU hgU hg (hF.const_smul c)
      (fun h hh hG => by simp only [hff h hh hG, Pi.smul_apply]) a b,
    EH_psi hU hgU hg hF hff a b]
  simp only [Psi]
  show c • fderiv ℝ F g (g * hpart1 (Hpk k r) (Matrix.single a b 1)) +
      Complex.I • c • fderiv ℝ F g (g * hpart2 (Hpk k r) (Matrix.single a b 1)) = _
  rw [smul_add, smul_comm Complex.I c]

theorem EHc_HL {y : Mat k r} (hy : y ∈ GV k r) : HL (EHc (E := E) k r y) := by
  intro a b f f₂ h g hg
  rw [EHc_eq, EHc_eq]
  beta_reduce
  rw [Dx_congr (x := (false, y⁻¹ * Xa k r a b * y)) (inLie_conj_of_mem_GV' hy (Xa_lie a b)) h g hg,
    Dx_congr (x := (false, y⁻¹ * Xb k r a b * y)) (inLie_conj_of_mem_GV' hy (Xb_lie a b)) h g hg]

theorem EHc_change {y : Mat k r} (hy : y ∈ GV k r) (c d : Fin (2 * r + k + 1)) (φ : Mat k r → E)
    (hφ : CkOn 1 (GV k r) φ) : ∀ g ∈ GV k r,
      EHc k r y c d φ g = ∑ a, ∑ b, (y⁻¹ a c * y d b) • Q.EH k r a b φ g := by
  intro g hg
  obtain ⟨U, F, hU, hgU, hF, hff⟩ := rep1 hφ hg
  rw [EHc_psi hy hU hgU hg hF hff c d, conj_single, Psi_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Psi_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Psi_smul, EH_psi hU hgU hg hF hff a b]

end Formalism.FourierDecayAlt.P.JFxE
end
end

section

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate ENNReal InnerProductSpace

noncomputable section

open Classical

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def GermContAt (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (K N : ℕ) :
    Prop :=
  ∀ b s : ℕ, 1 ≤ b → 2 ≤ s → b + s - 1 ≤ P.r + 1 → ∀ h : C.LPt, D.IsLocPt h (b - 1) → ∀ w, TBB.AdmW P p.l0 Y w →
    w.length + K ≤ N → ContinuousOn (fun z : ℂ => TBB.Ew p nn F (b + s - 1) w (h ++ [(s, z)])) {0}ᶜ

def GermDataAt (lev : ℕ → Prop) (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (Y : Finset ℝ) (K N : ℕ) : Prop :=
  ∀ b s : ℕ, 1 ≤ b → 2 ≤ s → b + s - 1 ≤ P.r + 1 → lev (b + s - 1) → ∀ h : C.LPt, D.IsLocPt h (b - 1) →
    ∀ w, TBB.AdmW P p.l0 Y w → w.length + K ≤ N →
    (∀ w', TBB.IsExt P p.l0 Y N K w w' →
      BddAbove (Set.range fun t : {t : ℂ // t ≠ 0} => TBB.Ew p nn F (b + s - 2) w' (h ++ [(s - 1, t.1)]))) →
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (ut : ℂ → ℂ → H) (bt : ℂ → H) (β ε' η : ℂ) (SS κ₁ κ₂ : ℝ),
      0 ≤ κ₂ ∧ κ₂ ≤ Real.pi * κ₁ ∧ (η = 1 ∨ η = -1) ∧
      PBK.GermD s β ε' ({()} : Finset Unit) (fun _ => ut) (fun _ => bt) SS ∧
      (∀ σ z : ℂ, P5.fsv σ z = G.psi β (η * σ * z)) ∧
      (∀ t t' : ℂ, t ≠ 0 → t' ≠ 0 →
        ‖TBB.NP p nn F (b + s - 2) w (h ++ [(s - 1, t)]) (h ++ [(s - 1, t')])‖ =
          κ₁ * ‖PBK.gramL volume (PBK.Uc s fun _ => ut) (PBK.Uc s fun _ => ut) ((), t⁻¹) ((), t'⁻¹)‖) ∧
      ∀ z : ℂ, z ≠ 0 → TBB.Ew p nn F (b + s - 1) w (h ++ [(s, z)]) = κ₂ * ‖PBK.bz s bt z‖ ^ 2

end place

def GermContAll : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (K N : ℕ) (Cb : ℝ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base F → (∀ y, 0 < nn y) → GermContAt p nn F Y K N

def PropGMean : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (s : ℕ) (β ε' η : ℂ)
    (ut : ℂ → ℂ → H) (bt : ℂ → H) (SS κ₁ κ₂ : ℝ) (E : ℂ → ℝ) (Nk : ℂ → ℂ → ℂ),
    2 ≤ s → 0 ≤ κ₂ → κ₂ ≤ Real.pi * κ₁ → (η = 1 ∨ η = -1) →
    PBK.GermD s β ε' ({()} : Finset Unit) (fun _ => ut) (fun _ => bt) SS →
    (∀ σ z : ℂ, P5.fsv σ z = G.psi β (η * σ * z)) →
    (∀ t t' : ℂ, t ≠ 0 → t' ≠ 0 →
      ‖Nk t t'‖ = κ₁ * ‖PBK.gramL volume (PBK.Uc s fun _ => ut) (PBK.Uc s fun _ => ut) ((), t⁻¹) ((), t'⁻¹)‖) →
    (∀ z : ℂ, z ≠ 0 → E z = κ₂ * ‖PBK.bz s bt z‖ ^ 2) →
    Integrable E ∧
      ∀ ω₁ ω₂ : ℂ, (conj ω₁ * ω₂).im ≠ 0 → ∃ A : ℂ → ℂ, PDDual ω₁ ω₂ A ∧
        ∀ σ : ℂ, TBB.InDual ω₁ ω₂ σ →
          (‖(Real.pi⁻¹ : ℂ) * (∫ z : ℂ, P5.fsv σ z * (E z : ℂ)) + A σ‖₊ : ℝ≥0∞) ≤
            limsup (fun t : ℂ => (‖Nk t (t⁻¹ + σ)⁻¹‖₊ : ℝ≥0∞)) (𝓝[≠] 0)

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem germAtPD_of_parts (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ)
    (K N : ℕ) (hC : GermContAt p nn F Y K N) (hL : GermDataAt (fun i => i ≤ P.r) p nn F Y K N)
    (hT : GermDataAt (fun i => i = P.r + 1) p nn F Y K N) (hM : PropGMean) : GermAtPD p nn F Y K N := by
  intro b s hb hs hbs h hh w hw hN hBdd
  have hcont := hC b s hb hs hbs h hh w hw hN
  have hdata : ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (ut : ℂ → ℂ → H) (bt : ℂ → H) (β ε' η : ℂ) (SS κ₁ κ₂ : ℝ),
      0 ≤ κ₂ ∧ κ₂ ≤ Real.pi * κ₁ ∧ (η = 1 ∨ η = -1) ∧
      PBK.GermD s β ε' ({()} : Finset Unit) (fun _ => ut) (fun _ => bt) SS ∧
      (∀ σ z : ℂ, P5.fsv σ z = G.psi β (η * σ * z)) ∧
      (∀ t t' : ℂ, t ≠ 0 → t' ≠ 0 →
        ‖TBB.NP p nn F (b + s - 2) w (h ++ [(s - 1, t)]) (h ++ [(s - 1, t')])‖ =
          κ₁ * ‖PBK.gramL volume (PBK.Uc s fun _ => ut) (PBK.Uc s fun _ => ut) ((), t⁻¹) ((), t'⁻¹)‖) ∧
      ∀ z : ℂ, z ≠ 0 → TBB.Ew p nn F (b + s - 1) w (h ++ [(s, z)]) = κ₂ * ‖PBK.bz s bt z‖ ^ 2 := by
    rcases Nat.lt_or_ge (b + s - 1) (P.r + 1) with hlt | hge
    · exact hL b s hb hs hbs (by omega) h hh w hw hN hBdd
    · exact hT b s hb hs hbs (by omega) h hh w hw hN hBdd
  obtain ⟨H, _, _, _, ut, bt, β, ε', η, SS, κ₁, κ₂, hκ₂, hκ, hη, hGD, hpsi, hNk, hE⟩ := hdata
  obtain ⟨hint, hlat⟩ := hM H s β ε' η ut bt SS κ₁ κ₂
    (fun z => TBB.Ew p nn F (b + s - 1) w (h ++ [(s, z)]))
    (fun t t' => TBB.NP p nn F (b + s - 2) w (h ++ [(s - 1, t)]) (h ++ [(s - 1, t')]))
    hs hκ₂ hκ hη hGD hpsi hNk hE
  exact ⟨hcont, hint, hlat⟩

end place

end

end Formalism.FourierDecayAlt.P.CutBP

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt

end Formalism.FourierDecayAlt.P.CutBP
end

section

open Matrix MvPolynomial
open scoped ComplexConjugate ContDiff Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.MinorPolynomials

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def fct (z z' : Fin (2 * r + k + 1) → ℂ) (a b : Fin (r + 2) → ℕ) (g : Mat k r) (l : Fin (r + 2)) : ℂ :=
  (Dmin k r z z' g l)⁻¹ ^ a l * (star (Dmin k r z z' g l))⁻¹ ^ b l

lemma monoM_eq (D : RealPlaceData k r Wp Wq) (a b : Fin (r + 2) → ℕ) (c : ℕ) (g : Mat k r) :
    C6.monoM D a b c g = (∏ l, fct D.z D.z' a b g l) * ((Gf k r D.z D.z' g : ℝ) : ℂ)⁻¹ ^ c := rfl

lemma prod_update_a (z z' : Fin (2 * r + k + 1) → ℂ) (a b : Fin (r + 2) → ℕ) (g : Mat k r) (l : Fin (r + 2)) :
    (∏ j ∈ Finset.univ.erase l, fct z z' a b g j) *
      ((Dmin k r z z' g l)⁻¹ ^ (a l + 1) * (star (Dmin k r z z' g l))⁻¹ ^ b l) =
      ∏ j, fct z z' (a + Pi.single l 1) b g j := by
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ l)]
  congr 1
  · apply Finset.prod_congr rfl
    intro j hj
    have hjl : j ≠ l := Finset.ne_of_mem_erase hj
    simp [fct, Pi.single_apply, hjl]
  · simp [fct]

lemma prod_update_b (z z' : Fin (2 * r + k + 1) → ℂ) (a b : Fin (r + 2) → ℕ) (g : Mat k r) (l : Fin (r + 2)) :
    (∏ j ∈ Finset.univ.erase l, fct z z' a b g j) *
      ((Dmin k r z z' g l)⁻¹ ^ a l * (star (Dmin k r z z' g l))⁻¹ ^ (b l + 1)) =
      ∏ j, fct z z' a (b + Pi.single l 1) g j := by
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ l)]
  congr 1
  · apply Finset.prod_congr rfl
    intro j hj
    have hjl : j ≠ l := Finset.ne_of_mem_erase hj
    simp [fct, Pi.single_apply, hjl]
  · simp [fct]

theorem hasDerivAt_cvs (D : RealPlaceData k r Wp Wq) {nf : ℕ} (X g : Mat k r) (t : CT k r nf)
    (hnz : ∀ l, (t.a l ≠ 0 ∨ t.b l ≠ 0) → Dmin k r D.z D.z' g l ≠ 0)
    (hG : t.c ≠ 0 → ((Gf k r D.z D.z' g : ℝ) : ℂ) ≠ 0) :
    HasDerivAt (fun s => cvs D t (crv (false, X) g s)) (((dscal D X t).map fun t' => cvs D t' g).sum) 0 := by

  have hF : ∀ l ∈ (Finset.univ : Finset (Fin (r + 2))), HasDerivAt (fun s => fct D.z D.z' t.a t.b (crv (false, X) g s) l)
      ((-(t.a l : ℂ) * eval (vars g) (dP X (qDl D.z D.z' l)) * (Dmin k r D.z D.z' g l)⁻¹ ^ (t.a l + 1)) *
          (star (Dmin k r D.z D.z' g l))⁻¹ ^ t.b l +
        (Dmin k r D.z D.z' g l)⁻¹ ^ t.a l *
          (-(t.b l : ℂ) * eval (vars g) (dP X (qDbl D.z D.z' l)) * (star (Dmin k r D.z D.z' g l))⁻¹ ^ (t.b l + 1)))
      0 := by
    intro l _
    have ha : t.a l = 0 ∨ Dmin k r D.z D.z' (crv (false, X) g 0) l ≠ 0 := by
      rw [crv_zero]; by_cases h : t.a l = 0
      · exact Or.inl h
      · exact Or.inr (hnz l (Or.inl h))
    have hb : t.b l = 0 ∨ star (Dmin k r D.z D.z' (crv (false, X) g 0) l) ≠ 0 := by
      rw [crv_zero]; by_cases h : t.b l = 0
      · exact Or.inl h
      · exact Or.inr (star_ne_zero.2 (hnz l (Or.inr h)))
    have h1 := hasDerivAt_invpow' (hasDerivAt_polyD X g D.z D.z' l) ha
    have h2 := hasDerivAt_invpow' (hasDerivAt_polyDb X g D.z D.z' l) hb
    have := h1.fun_mul h2
    simpa only [fct, crv_zero] using this
  have hprod := HasDerivAt.fun_finsetProd hF
  have hGd := hasDerivAt_invpow' (hasDerivAt_polyG X g D.z D.z') (a := t.c) (by
    rw [crv_zero]; by_cases h : t.c = 0
    · exact Or.inl h
    · exact Or.inr (hG h))
  have hP := hasDerivAt_poly X g t.q
  have hall := hP.fun_mul (hprod.fun_mul hGd)
  have hfun : (fun s => cvs D t (crv (false, X) g s)) = fun s => eval (vars (crv (false, X) g s)) t.q *
      ((∏ l ∈ Finset.univ, fct D.z D.z' t.a t.b (crv (false, X) g s) l) * ((Gf k r D.z D.z' (crv (false, X) g s) : ℝ) : ℂ)⁻¹ ^ t.c) := by
    funext s; simp [cvs, monoM_eq]
  rw [hfun]
  refine hall.congr_deriv ?_

  simp only [crv_zero]
  set P0 := eval (vars g) t.q
  set G0 := ((Gf k r D.z D.z' g : ℝ) : ℂ)
  set dG := eval (vars g) (dP X (qGf D.z D.z'))
  have hsum : ∑ l ∈ (Finset.univ : Finset (Fin (r + 2))), (∏ j ∈ Finset.univ.erase l, fct D.z D.z' t.a t.b g j) •
      ((-(t.a l : ℂ) * eval (vars g) (dP X (qDl D.z D.z' l)) * (Dmin k r D.z D.z' g l)⁻¹ ^ (t.a l + 1)) *
          (star (Dmin k r D.z D.z' g l))⁻¹ ^ t.b l +
        (Dmin k r D.z D.z' g l)⁻¹ ^ t.a l *
          (-(t.b l : ℂ) * eval (vars g) (dP X (qDbl D.z D.z' l)) * (star (Dmin k r D.z D.z' g l))⁻¹ ^ (t.b l + 1))) =
      ∑ l, (-(t.a l : ℂ) * eval (vars g) (dP X (qDl D.z D.z' l)) * ∏ j, fct D.z D.z' (t.a + Pi.single l 1) t.b g j) +
      ∑ l, (-(t.b l : ℂ) * eval (vars g) (dP X (qDbl D.z D.z' l)) * ∏ j, fct D.z D.z' t.a (t.b + Pi.single l 1) g j) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro l _
    rw [← prod_update_a, ← prod_update_b, smul_eq_mul]
    ring
  have hcq : cvs D { t with q := dP X t.q } g =
      eval (vars g) (dP X t.q) * ((∏ l, fct D.z D.z' t.a t.b g l) * G0⁻¹ ^ t.c) := by
    simp [cvs, monoM_eq, G0]
  have hca : ∀ l, cvs D (if t.a l = 0 then { t with q := 0 } else
      { t with q := C (-(t.a l : ℂ)) * t.q * dP X (qDl D.z D.z' l), a := t.a + Pi.single l 1 }) g =
      -(t.a l : ℂ) * P0 * eval (vars g) (dP X (qDl D.z D.z' l)) *
        ((∏ j, fct D.z D.z' (t.a + Pi.single l 1) t.b g j) * G0⁻¹ ^ t.c) := by
    intro l
    split_ifs with h
    · simp [cvs, h]
    · simp [cvs, monoM_eq, P0, G0]; try ring
  have hcb : ∀ l, cvs D (if t.b l = 0 then { t with q := 0 } else
      { t with q := C (-(t.b l : ℂ)) * t.q * dP X (qDbl D.z D.z' l), b := t.b + Pi.single l 1 }) g =
      -(t.b l : ℂ) * P0 * eval (vars g) (dP X (qDbl D.z D.z' l)) *
        ((∏ j, fct D.z D.z' t.a (t.b + Pi.single l 1) g j) * G0⁻¹ ^ t.c) := by
    intro l
    split_ifs with h
    · simp [cvs, h]
    · simp [cvs, monoM_eq, P0, G0]; try ring
  have hcc : cvs D (if t.c = 0 then { t with q := 0 } else
      { t with q := C (-(t.c : ℂ)) * t.q * dP X (qGf D.z D.z'), c := t.c + 1 }) g =
      -(t.c : ℂ) * P0 * dG * ((∏ l, fct D.z D.z' t.a t.b g l) * G0⁻¹ ^ (t.c + 1)) := by
    split_ifs with h
    · simp [cvs, h]
    · simp [cvs, monoM_eq, P0, G0, dG]; try ring
  have hlist : ((dscal D X t).map fun t' => cvs D t' g).sum =
      eval (vars g) (dP X t.q) * ((∏ l, fct D.z D.z' t.a t.b g l) * G0⁻¹ ^ t.c) +
      ∑ l, (-(t.a l : ℂ) * P0 * eval (vars g) (dP X (qDl D.z D.z' l)) *
        ((∏ j, fct D.z D.z' (t.a + Pi.single l 1) t.b g j) * G0⁻¹ ^ t.c)) +
      ∑ l, (-(t.b l : ℂ) * P0 * eval (vars g) (dP X (qDbl D.z D.z' l)) *
        ((∏ j, fct D.z D.z' t.a (t.b + Pi.single l 1) g j) * G0⁻¹ ^ t.c)) +
      (-(t.c : ℂ) * P0 * dG * ((∏ l, fct D.z D.z' t.a t.b g l) * G0⁻¹ ^ (t.c + 1))) := by
    simp only [dscal, List.map_append, List.map_cons, List.map_nil, List.map_ofFn, List.sum_append,
      List.sum_cons, List.sum_nil, List.sum_ofFn, add_zero, Function.comp_def, hcq, hca, hcb, hcc]
    try ring
  rw [hlist, hsum]
  have eA : P0 * (∑ l, (-(t.a l : ℂ) * eval (vars g) (dP X (qDl D.z D.z' l)) *
      ∏ j, fct D.z D.z' (t.a + Pi.single l 1) t.b g j)) * G0⁻¹ ^ t.c =
      ∑ l, (-(t.a l : ℂ) * P0 * eval (vars g) (dP X (qDl D.z D.z' l)) *
        ((∏ j, fct D.z D.z' (t.a + Pi.single l 1) t.b g j) * G0⁻¹ ^ t.c)) := by
    rw [Finset.mul_sum, Finset.sum_mul]; apply Finset.sum_congr rfl; intro l _; ring
  have eB : P0 * (∑ l, (-(t.b l : ℂ) * eval (vars g) (dP X (qDbl D.z D.z' l)) *
      ∏ j, fct D.z D.z' t.a (t.b + Pi.single l 1) g j)) * G0⁻¹ ^ t.c =
      ∑ l, (-(t.b l : ℂ) * P0 * eval (vars g) (dP X (qDbl D.z D.z' l)) *
        ((∏ j, fct D.z D.z' t.a (t.b + Pi.single l 1) g j) * G0⁻¹ ^ t.c)) := by
    rw [Finset.mul_sum, Finset.sum_mul]; apply Finset.sum_congr rfl; intro l _; ring
  linear_combination eA + eB

end Formalism.FourierDecayAlt.P.MinorPolynomials
end
end
