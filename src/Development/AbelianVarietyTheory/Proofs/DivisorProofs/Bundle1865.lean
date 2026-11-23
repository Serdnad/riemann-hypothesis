module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1624
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle148
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle364
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1756
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1758
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1848
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1761
import Formalism.PadicSubsetSums.StableGradedCounts.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1850
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle651
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle701
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle147
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle052
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.TrKer

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

instance finiteDimensional_wsp (lam : InfinitePlace E → DomWeight n) : FiniteDimensional ℂ (Wsp lam) :=
  Module.Finite.of_basis (Basis.piTensorProduct fun v => Module.finBasis ℂ _)


variable (E n) in
def splitFin : UA E n →* finU (E := E) (n := n) := (GlobalTheory.UnitarySplit.dense_and_split E n).2.2.2.choose


variable (E n) in
def splitInf : UA E n →* infU E n := (GlobalTheory.UnitarySplit.dense_and_split E n).2.2.2.choose_spec.choose

theorem continuous_splitFin : Continuous (splitFin E n) :=
  (GlobalTheory.UnitarySplit.dense_and_split E n).2.2.2.choose_spec.choose_spec.1

theorem eq_splitFin_mul_splitInf (x : UA E n) : x = (splitFin E n x).1 * (splitInf E n x).1 :=
  (GlobalTheory.UnitarySplit.dense_and_split E n).2.2.2.choose_spec.choose_spec.2.2.1 x

theorem splitFin_mul (g : finU (E := E) (n := n)) (k : infU E n) : splitFin E n (g.1 * k.1) = g :=
  ((GlobalTheory.UnitarySplit.dense_and_split E n).2.2.2.choose_spec.choose_spec.2.2.2 g k).1

theorem splitInf_mul (g : finU (E := E) (n := n)) (k : infU E n) : splitInf E n (g.1 * k.1) = k :=
  ((GlobalTheory.UnitarySplit.dense_and_split E n).2.2.2.choose_spec.choose_spec.2.2.2 g k).2

theorem splitFin_fin (g : finU (E := E) (n := n)) : splitFin E n g.1 = g := by
  simpa using splitFin_mul g 1

theorem splitFin_inf (k : infU E n) : splitFin E n k.1 = 1 := by
  simpa using splitFin_mul 1 k

def wInf (lam : InfinitePlace E → DomWeight n) : Representation ℂ (UA E n) (Wsp lam) where
  toFun g := PiTensorProduct.map fun v => GlobalTheory.Branching.sqRep ℂ n (lam v) (cEmb v.embedding g)
  map_one' := by
    simp only [map_one]
    exact PiTensorProduct.map_id
  map_mul' a b := by
    simp only [map_mul]
    exact PiTensorProduct.map_mul _ _

def phiFun (lam : InfinitePlace E → DomWeight n) :
    (finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam)) →ₗ[ℂ] Wsp lam →ₗ[ℂ] (UA E n → ℂ) :=
  LinearMap.mk₂ ℂ (fun F w g => F (splitFin E n g) (wInf lam g w))
    (fun F F' w => by funext g; simp)
    (fun c F w => by funext g; simp)
    (fun F w w' => by funext g; simp)
    (fun c F w => by funext g; simp)

@[simp] theorem phiFun_apply (lam : InfinitePlace E → DomWeight n) (F : finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam))
    (w : Wsp lam) (g : UA E n) : phiFun lam F w g = F (splitFin E n g) (wInf lam g w) := rfl

def Phi (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)) :
    vecM S lam K' ⊗[ℂ] Wsp lam →ₗ[ℂ] (UA E n → ℂ) :=
  TensorProduct.lift ((phiFun lam).comp (vecM S lam K').subtype)

@[simp] theorem Phi_tmul (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w))
    (F : vecM S lam K') (w : Wsp lam) : Phi S lam K' (F ⊗ₜ w) = phiFun lam F.1 w := by
  simp [Phi]

theorem cEmb_fin (τ : E →+* ℂ) (k : finU (E := E) (n := n)) : cEmb τ k.1 = 1 := by
  have hk : cInf k.1 = 1 := MonoidHom.mem_ker.1 k.2
  simp only [cEmb, MonoidHom.comp_apply, hk, map_one]

theorem wInf_fin (lam : InfinitePlace E → DomWeight n) (k : finU (E := E) (n := n)) : wInf lam k.1 = 1 := by
  have h : ∀ v : InfinitePlace E, cEmb v.embedding k.1 = 1 := fun v => cEmb_fin _ k
  change PiTensorProduct.map (fun v => GlobalTheory.Branching.sqRep ℂ n (lam v) (cEmb v.embedding k.1)) = 1
  simp only [h, map_one]
  exact PiTensorProduct.map_id

theorem splitFin_mul_fin (g : UA E n) (k : finU (E := E) (n := n)) : splitFin E n (g * k.1) = splitFin E n g * k := by
  rw [map_mul, splitFin_fin]

theorem phiFun_mul_fin (lam : InfinitePlace E → DomWeight n) (F : finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam)) (w : Wsp lam)
    (g : UA E n) (k : finU (E := E) (n := n)) :
    phiFun lam F w (g * k.1) = phiFun lam (rightReg ℂ (finU (E := E) (n := n)) (Module.Dual ℂ (Wsp lam)) k F) w g := by
  rw [phiFun_apply, phiFun_apply, splitFin_mul_fin, map_mul, wInf_fin, mul_one]
  rfl

end GlobalTheory.BCT.TrKer
end
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovTop.VolUp.UpBall

theorem isIdent_det {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {κ : Type} {p q : κ → ℕ}
    {Ψ : Finset (E →+* ℂ)} {G : Matrix (Fin r) (Fin r) E} {x : Frame Ψ r} {σ : κ ≃ Ψ}
    {A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ} {e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r}
    (h : IsIdent p q Ψ G x σ A e) (τ : Ψ) : (mat x τ).det ≠ 0 ∧ G.det ≠ 0 := by
  obtain ⟨h1, h2⟩ := h (σ.symm τ)
  rw [Equiv.apply_symm_apply] at h1 h2
  set P := permM (e (σ.symm τ))
  set J := Formalism.UG.Jpq (p (σ.symm τ)) (q (σ.symm τ))
  set N := Pᵀ * A (σ.symm τ)
  have hN : N * mat x τ = 1 := by rw [Matrix.mul_assoc, h2, transpose_mul_permM]
  have hN' : mat x τ * N = 1 := mul_eq_one_comm.1 hN
  refine ⟨Matrix.det_ne_zero_of_left_inverse hN, ?_⟩
  have hA : A (σ.symm τ) = P * N := by
    calc A (σ.symm τ) = A (σ.symm τ) * (mat x τ * N) := by rw [hN', Matrix.mul_one]
      _ = P * N := by rw [← Matrix.mul_assoc, h2]
  have hJ : J * J = 1 := by
    simp [J, Formalism.UG.Jpq, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
  have hPc : Pᴴ = Pᵀ := by
    ext i j; simp only [P, permM, Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.of_apply]
    split_ifs <;> simp
  set D := Pᵀ * J * P
  have hD : D * D = 1 := by
    calc D * D = Pᵀ * J * (P * Pᵀ) * J * P := by simp only [D, Matrix.mul_assoc]
      _ = Pᵀ * (J * J) * P := by rw [permM_mul_transpose]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by rw [hJ, Matrix.mul_one, transpose_mul_permM]
  have hDdet : D.det ≠ 0 := Matrix.det_ne_zero_of_left_inverse hD
  have hNdet : N.det ≠ 0 := Matrix.det_ne_zero_of_left_inverse hN'
  have key : -(G.map τ.1)ᵀ = Nᴴ * D * N := by
    rw [← h1, hA, Matrix.conjTranspose_mul, hPc]
    simp only [D, Matrix.mul_assoc]
  have hdet : (-(G.map τ.1)ᵀ).det ≠ 0 := by
    rw [key, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
    exact mul_ne_zero (mul_ne_zero (star_ne_zero.2 hNdet) hDdet) hNdet
  intro hG
  apply hdet
  rw [Matrix.det_neg, Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hG, map_zero, mul_zero]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem exists_lam (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r)
    (hx : ∀ τ, (mat x τ).det ≠ 0) :
    ∃ lam : Measure (realLie Ψ G), lam.IsAddHaarMeasure ∧ lam.map Subtype.val = riemLie Ψ G x := by
  set W := (realLie Ψ G).comap (fromFrame x)
  let Φ : W →ₗ[ℝ] realLie Ψ G :=
    ((fromFrame x).comp W.subtype).codRestrict (realLie Ψ G) (fun v => v.2)
  have key2 : ∀ τ (A : Matrix (Fin r) (Fin r) ℂ),
      mat x τ * ((mat x τ)⁻¹ * A * mat x τ) * (mat x τ)⁻¹ = A := fun τ A => by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ (hx τ).isUnit,
      Matrix.mul_nonsing_inv_cancel_left _ _ (hx τ).isUnit]
  have hsurj : Function.Surjective Φ := by
    intro X
    let Y : EuclideanSpace ℂ (Ψ × Fin r × Fin r) := WithLp.toLp 2 (fun p : Ψ × Fin r × Fin r =>
      ((mat x p.1)⁻¹ * Matrix.of (X.1 p.1) * mat x p.1) p.2.1 p.2.2)
    have hY : fromFrame x Y = X.1 := by
      funext τ
      have e : Matrix.of (fun a b => Y (τ, a, b)) = (mat x τ)⁻¹ * Matrix.of (X.1 τ) * mat x τ := by
        ext a b; simp [Y]
      change (mat x τ * Matrix.of _ * (mat x τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) = X.1 τ
      rw [e, key2]; rfl
    exact ⟨⟨Y, show fromFrame x Y ∈ realLie Ψ G by rw [hY]; exact X.2⟩, Subtype.ext hY⟩
  have key1 : ∀ τ (A : Matrix (Fin r) (Fin r) ℂ),
      (mat x τ)⁻¹ * (mat x τ * A * (mat x τ)⁻¹) * mat x τ = A := fun τ A => by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_right _ _ (hx τ).isUnit,
      Matrix.nonsing_inv_mul_cancel_left _ _ (hx τ).isUnit]
  have hinj : Function.Injective Φ := by
    intro Y Z h
    have h' : fromFrame x Y.1 = fromFrame x Z.1 := congrArg Subtype.val h
    have hτ : ∀ τ, Matrix.of (fun a b => Y.1 (τ, a, b)) = Matrix.of (fun a b => Z.1 (τ, a, b)) := by
      intro τ
      have h1 : mat x τ * Matrix.of (fun a b => Y.1 (τ, a, b)) * (mat x τ)⁻¹ =
          mat x τ * Matrix.of (fun a b => Z.1 (τ, a, b)) * (mat x τ)⁻¹ := congrFun h' τ
      rw [← key1 τ (Matrix.of (fun a b => Y.1 (τ, a, b))), h1, key1]
    refine Subtype.ext (PiLp.ext fun p => ?_)
    obtain ⟨τ, a, b⟩ := p
    exact congrFun (congrFun (hτ τ) a) b
  let φ : W ≃L[ℝ] realLie Ψ G := (LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩).toContinuousLinearEquiv
  refine ⟨(stdOrthonormalBasis ℝ W).toBasis.addHaar.map φ, φ.isAddHaarMeasure_map _, ?_⟩
  rw [Measure.map_map measurable_subtype_coe φ.continuous.measurable]
  rfl

theorem riemHaar_frBall_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (κ : Type) (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (σ : κ ≃ Ψ) (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r), 1 ≤ r → IsIdent p q Ψ G x σ A e → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → riemHaar Ψ G x (frBall Ψ G x ε) ≤ ENNReal.ofReal ((8 * ε) ^ (Ψ.card * (r ^ 2 - 1))) := by
  intro E _ _ _ r κ p q Ψ G x σ A e hr hI
  have hx : ∀ τ, (mat x τ).det ≠ 0 := fun τ => (isIdent_det hI τ).1
  by_cases hd : Ψ.card * (r ^ 2 - 1) = 0
  · refine ⟨1, one_pos, fun ε _ _ => ?_⟩
    rw [hd, pow_zero, ENNReal.ofReal_one]
    exact GlobalTheory.T.riemannianHaar_le_one_of_dim_zero E r Ψ G x hr hx hd _
  have hΨ : 0 < Ψ.card := Nat.pos_of_ne_zero fun h => hd (by rw [h, zero_mul])
  obtain ⟨τ₀, hτ₀⟩ := Finset.card_pos.1 hΨ
  have hG : G.det ≠ 0 := (isIdent_det hI ⟨τ₀, hτ₀⟩).2
  have hr2 : 3 ≤ r ^ 2 - 1 := by
    have : r ≠ 1 := fun h => hd (by rw [h]; simp)
    have : 2 ≤ r := by omega
    have : 4 ≤ r ^ 2 := by nlinarith
    omega
  have hd3 : 3 ≤ Ψ.card * (r ^ 2 - 1) := le_trans hr2 (Nat.le_mul_of_pos_left _ hΨ)
  obtain ⟨lam, hlam, hmap⟩ := exists_lam Ψ G x hx
  obtain ⟨δ, hδ, hup⟩ := GlobalTheory.T.tangentNormalizedHaar_le_two_mul_lieHaar E r Ψ G hG lam
  obtain ⟨ε₀, hε₀, hcov⟩ := GlobalTheory.T.frameBall_subset_expChart_image_frameBox E r Ψ G x hG hx δ hδ
  refine ⟨ε₀, hε₀, fun ε hε hεε => ?_⟩
  set S : Set (Ψ → Fin r → Fin r → ℂ) :=
    {X | ∀ τ a b, ‖((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ) a b‖ < 2 * ε} with hS
  have hcont : ∀ τ a b, Continuous (fun X : Ψ → Fin r → Fin r → ℂ =>
      ((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ) a b) := by
    intro τ a b
    exact ((continuous_const.matrix_mul (continuous_apply τ)).matrix_mul continuous_const).matrix_elem a b
  have hSm : MeasurableSet S := by
    simp only [hS, Set.setOf_forall]
    exact MeasurableSet.iInter fun τ => MeasurableSet.iInter fun a => MeasurableSet.iInter fun b =>
      measurableSet_lt (hcont τ a b).norm.measurable measurable_const
  set s : Set (realLie Ψ G) := {X : realLie Ψ G | ‖X‖ < δ ∧ ∀ τ a b,
    ‖((mat x τ)⁻¹ * Matrix.of (X.1 τ) * mat x τ) a b‖ < 2 * ε} with hs
  have hs' : s = Metric.ball 0 δ ∩ Subtype.val ⁻¹' S := by
    ext X; simp [hs, hS, mem_ball_zero_iff]
  have hsm : MeasurableSet s := by
    rw [hs']; exact measurableSet_ball.inter (measurable_subtype_coe hSm)
  have hsb : s ⊆ Metric.ball 0 δ := by rw [hs']; exact Set.inter_subset_left
  have h1 : riemHaar Ψ G x (frBall Ψ G x ε) ≤ 2 * lam s := by
    calc riemHaar Ψ G x (frBall Ψ G x ε)
        ≤ tangentHaar (realSU Ψ G) (lam.map Subtype.val) (GlobalTheory.SUVol.DensOne.chartExp Ψ G hG '' s) := by
          unfold riemHaar; rw [← hmap]; exact measure_mono (hcov ε hε hεε)
      _ ≤ 2 * lam s := hup s hsm hsb
  have h2 : lam s ≤ riemLie Ψ G x S := by
    rw [← hmap, Measure.map_apply measurable_subtype_coe hSm, hs']
    exact measure_mono Set.inter_subset_right
  have h3 := GlobalTheory.T.riemannianLieMeasure_frameBox_le E r κ p q Ψ G x σ A e hr hI (2 * ε) (by positivity)
  have h4 : 2 * lam s ≤ 2 * ENNReal.ofReal ((3 * (2 * ε)) ^ (Ψ.card * (r ^ 2 - 1))) := by
    gcongr; exact h2.trans h3
  refine h1.trans (h4.trans ?_)
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
  refine ENNReal.ofReal_le_ofReal ?_
  set d := Ψ.card * (r ^ 2 - 1)
  have e1 : (8 * ε) ^ d = (4 / 3 : ℝ) ^ d * (3 * (2 * ε)) ^ d := by rw [← mul_pow]; ring_nf
  have e2 : (2 : ℝ) ≤ (4 / 3 : ℝ) ^ d := by
    calc (2 : ℝ) ≤ (4 / 3) ^ 3 := by norm_num
      _ ≤ (4 / 3) ^ d := pow_le_pow_right₀ (by norm_num) hd3
  rw [e1]
  exact mul_le_mul_of_nonneg_right e2 (by positivity)

end GlobalTheory.CovTop.VolUp.UpBall
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory ValuativeRel
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV

noncomputable section
namespace GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
variable {D : D7} {a b : ℕ}

theorem frAt_sub_reps (w : Pl D.host.E) (β' : GL (Fin b) (Lev.EAf D)) (β : GL (Fin a) (Lev.EAf D))
    (x y : Mx D b a) : frAt w β' β (x - y) = frAt w β' β x - frAt w β' β y := by
  unfold frAt
  rw [Matrix.map_sub _ (map_sub (toEAf D)), Comparison₂.fr_sub, Matrix.map_sub _ (map_sub (cpt (D := D) w))]

theorem isOpen_valBall_reps {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (γ : ValueGroupWithZero k) (hγ : γ ≠ 0) :
    IsOpen {x : k | valuation k x ≤ γ} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [IsValuativeTopology.mem_nhds_iff']
  refine ⟨Units.mk0 γ hγ, fun y hy => ?_⟩
  simp only [Set.mem_ofPred_eq, Units.val_mk0] at hx hy ⊢
  have h := (valuation k).map_add (y - x) x
  rw [sub_add_cancel] at h
  exact h.trans (max_le hy.le hx)

theorem exists_finset_cosetReps : ∀ {D : D7} {a b : ℕ} (β' : GL (Fin b) (Lev.EAf D)) (β : GL (Fin a) (Lev.EAf D))
    (P : Finset (Pl D.host.E)) (e : AE D) (n : ℕ), IsIdemSum e P → ∃ R : Finset (Mx D b a),
    (∀ r ∈ R, IsHalf e r ∧ IsSmall P β' β (-(n : ℤ)) r) ∧
    (∀ t, IsHalf e t → IsSmall P β' β (-(n : ℤ)) t → ∃ r ∈ R, IsSmall P β' β n (t - r)) ∧
    ∀ r ∈ R, ∀ r' ∈ R, IsSmall P β' β n (r - r') → r = r' := by
  intro D a b β' β P e n _
  classical
  let V := (w : P) → Fin b → Fin a → Kw w.1
  let φ : Mx D b a → V := fun t w r s => frAt w.1 β' β t r s
  have hφ : ∀ x y, φ (x - y) = φ x - φ y := by
    intro x y; funext w r s
    show frAt _ β' β (x - y) r s = frAt _ β' β x r s - frAt _ β' β y r s
    rw [frAt_sub_reps]; rfl
  let ρ : ∀ w : P, ValueGroupWithZero (Kw w.1) := fun w =>
    valuation (Kw w.1) ((unifAt w.1 ^ (n : ℤ) : (Kw w.1)ˣ) : Kw w.1)
  have hρ : ∀ w, ρ w ≠ 0 := fun w => by simp [ρ]
  let H : AddSubgroup V :=
    { carrier := {x | ∀ w r s, valuation (Kw w.1) (x w r s) ≤ ρ w}
      add_mem' := fun {x y} hx hy w r s =>
        ((valuation (Kw w.1)).map_add _ _).trans (max_le (hx w r s) (hy w r s))
      zero_mem' := fun w r s => by
        show valuation _ (0 : Kw w.1) ≤ _
        rw [map_zero]; exact zero_le'
      neg_mem' := fun {x} hx w r s => by
        show valuation _ (-(x w r s)) ≤ _
        rw [Valuation.map_neg]; exact hx w r s }
  have hH : ∀ x : V, x ∈ H ↔ ∀ w r s, valuation (Kw w.1) (x w r s) ≤ ρ w := fun x => Iff.rfl
  have hHset : (H : Set V) = Set.univ.pi fun w => Set.univ.pi fun r => Set.univ.pi fun s =>
      {z : Kw w.1 | valuation (Kw w.1) z ≤ ρ w} := by
    ext x
    rw [SetLike.mem_coe, hH]
    constructor
    · intro h
      exact Set.mem_univ_pi.2 fun w => Set.mem_univ_pi.2 fun r => Set.mem_univ_pi.2 fun s => h w r s
    · intro h w r s
      exact Set.mem_univ_pi.1 (Set.mem_univ_pi.1 (Set.mem_univ_pi.1 h w) r) s
  have hHo : IsOpen (H : Set V) := by
    rw [hHset]
    exact isOpen_set_pi Set.finite_univ fun w _ => isOpen_set_pi Set.finite_univ fun r _ =>
      isOpen_set_pi Set.finite_univ fun s _ => isOpen_valBall_reps _ (hρ w)
  let K : Set V := Set.univ.pi fun w => Set.univ.pi fun r => Set.univ.pi fun s =>
      {z : Kw w.1 | valuation (Kw w.1) z ≤
        valuation (Kw w.1) ((unifAt w.1 ^ (-(n : ℤ)) : (Kw w.1)ˣ) : Kw w.1)}
  have hK : IsCompact K := isCompact_univ_pi fun w => isCompact_univ_pi fun r => isCompact_univ_pi fun s =>
    IsNonarchimedeanLocalField.isCompact_closedBall _ _
  let U : V → Set V := fun x => (fun y => y - x) ⁻¹' (H : Set V)
  have hUo : ∀ x, IsOpen (U x) := fun x => hHo.preimage (continuous_id.sub continuous_const)
  obtain ⟨F, hF⟩ := hK.elim_finite_subcover U hUo (fun y _ => Set.mem_iUnion.2 ⟨y, by
    simp [U, H.zero_mem]⟩)
  have hsmall : ∀ (m : ℤ) t, IsSmall P β' β m t ↔ ∀ (w : P) r s,
      valuation (Kw w.1) (φ t w r s) ≤ valuation (Kw w.1) ((unifAt w.1 ^ m : (Kw w.1)ˣ) : Kw w.1) := by
    intro m t
    exact ⟨fun h w r s => h w.1 w.2 r s, fun h w hw r s => h ⟨w, hw⟩ r s⟩
  let S : Set (Mx D b a) := {t | IsHalf e t ∧ IsSmall P β' β (-(n : ℤ)) t}
  have hSK : ∀ t ∈ S, φ t ∈ K := fun t ht => by
    have h := (hsmall _ t).1 ht.2
    exact Set.mem_univ_pi.2 fun w => Set.mem_univ_pi.2 fun r => Set.mem_univ_pi.2 fun s => h w r s
  have hSmallH : ∀ t, IsSmall P β' β n t ↔ φ t ∈ H := fun t => hsmall _ t
  let C : Finset (V ⧸ H) := (Finset.image (fun x : V => (QuotientAddGroup.mk x : V ⧸ H)) F).filter
    (fun c => ∃ t, t ∈ S ∧ ((φ t : V) : V ⧸ H) = c)
  let rep : V ⧸ H → Mx D b a := fun c =>
    if h : ∃ t, t ∈ S ∧ ((φ t : V) : V ⧸ H) = c then h.choose else 0
  have hrep : ∀ c ∈ C, rep c ∈ S ∧ ((φ (rep c) : V) : V ⧸ H) = c := by
    intro c hc
    have h : ∃ t, t ∈ S ∧ ((φ t : V) : V ⧸ H) = c := (Finset.mem_filter.1 hc).2
    simp only [rep, dif_pos h]
    exact h.choose_spec
  refine ⟨C.image rep, ?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hr
    exact (hrep c hc).1
  · intro t ht1 ht2
    have ht : t ∈ S := ⟨ht1, ht2⟩
    obtain ⟨x, hxF, hx⟩ := Set.mem_iUnion₂.1 (hF (hSK t ht))
    have hc : ((φ t : V) : V ⧸ H) ∈ C := by
      have heq : ((x : V) : V ⧸ H) = ((φ t : V) : V ⧸ H) :=
        (QuotientAddGroup.eq_iff_sub_mem).2 (by
          have : φ t - x ∈ H := hx
          simpa using H.neg_mem this)
      have hmem : ((φ t : V) : V ⧸ H) ∈ Finset.image (fun x : V => (QuotientAddGroup.mk x : V ⧸ H)) F :=
        Finset.mem_image.2 ⟨x, hxF, heq⟩
      exact Finset.mem_filter.2 ⟨hmem, t, ht, rfl⟩
    refine ⟨rep _, Finset.mem_image.2 ⟨_, hc, rfl⟩, ?_⟩
    rw [hSmallH, hφ]
    exact (QuotientAddGroup.eq_iff_sub_mem).1 (hrep _ hc).2.symm
  · intro r hr r' hr' hs
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hr
    obtain ⟨c', hc', rfl⟩ := Finset.mem_image.1 hr'
    rw [hSmallH, hφ] at hs
    have : c = c' := by
      rw [← (hrep c hc).2, ← (hrep c' hc').2]
      exact (QuotientAddGroup.eq_iff_sub_mem).2 hs
    rw [this]

end GlobalTheory.FunObj

end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

namespace GlobalTheory.ThetaTransform

theorem thV_invV_eq : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)), Ctx ψ lam ν (half F N) → ∀ 𝓓 : Set (Fin N → AF F), IsAddFundamentalDomain (ratSub F N) 𝓓 (muV N ν) → muV N ν 𝓓 = 1 → ∀ f : VA F N → ℂ, Continuous f → QuasiV ψ f → Decay (invV ψ ν 𝓓 f) → thV ψ (invV ψ ν 𝓓 f) = f := by
  intro F _ _ N _ ψ lam ν hC 𝓓 hD hD1 f hf hq hdec
  have hC' := hC
  obtain ⟨hTR, ⟨hψc, hψn, hψF, -⟩, -, -, -⟩ := hC'
  funext w
  obtain ⟨x, y⟩ := w
  let P : (Fin N → AF F) → ℂ := fun u => f (x, u) * ψ (-(⅟(2 : AF F) * (x ⬝ᵥ u)))
  have hPc : Continuous P := by
    refine (hf.comp (Continuous.prodMk continuous_const continuous_id)).mul (hψc.comp ?_)
    refine (continuous_const.mul ?_).neg
    fun_prop
  have hPper : ∀ (ξ : Fin N → F) u, P (rat ξ + u) = P u := fun ξ u => integrand_periodic hq x u ξ
  have hcoef : ∀ ξ : Fin N → F, ∫ u in 𝓓, P u * ψ (-(Bd (AF F) (half F N) u (rat ξ))) ∂(muV N ν) =
      invV ψ ν 𝓓 f (rat ξ + x) := by
    intro ξ
    unfold invV
    congr 1
    funext u
    have h0 : (rat (0 : Fin N → F) : Fin N → AF F) = 0 := by funext l; simp [rat]
    have h := hq ξ 0 (x, u)
    rw [h0, Prod.mk_add_mk, zero_add] at h
    rw [h, Bd_half]
    simp only [P]
    rw [mul_assoc, ← AddChar.map_add_eq_mul, mul_comm (ψ _) (f _), mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    simp only [symV, add_dotProduct, dotProduct_zero, sub_zero, dotProduct_comm u (rat ξ)]
    linear_combination two_mul_invOf (rat ξ ⬝ᵥ u)
  have hsum : Summable (fun ξ : Fin N → F => ‖invV ψ ν 𝓓 f (rat ξ + x)‖) :=
    (GlobalTheory.decay_integrable_periodise F N hTR _ hdec).2.1 x
  have hser := GlobalTheory.SWQ.FourierSeries.fourier_series F N ψ lam ν (half F N) hC 𝓓 hD hD1 P
    (fun ξ => invV ψ ν 𝓓 f (rat ξ + x)) hPc hPper hcoef hsum y
  have hfxy : f (x, y) = P y * ψ (⅟(2 : AF F) * (x ⬝ᵥ y)) := by
    simp only [P, mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, mul_one]
  rw [hfxy, hser, ← tsum_mul_right]
  simp only [thV, GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.schr]
  refine tsum_congr fun ξ => ?_
  show ψ (rat ξ ⬝ᵥ y + ⅟(2 : AF F) * (x ⬝ᵥ y)) * invV ψ ν 𝓓 f (rat ξ + x) = _
  rw [Bd_half, AddChar.map_add_eq_mul, dotProduct_comm y (rat ξ)]
  ring

end GlobalTheory.ThetaTransform
end
