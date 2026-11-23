module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLimitOfChart
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle131
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicLeviEmbeddingHomomorphismProperties
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicStabilizerRadicalStructure
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Formalism.HermitianCurvature.StatementQ
public import Formalism.PeriodIntegrals.Bundle024
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.HermitianLattices.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle112
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.LinearAlgebra.Charpoly.Basic
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle009
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

noncomputable section

namespace GlobalTheory.GaugeSubLip

open Formalism.REAL GlobalTheory.GaugeSubLoc

variable {n d : ℕ}

def trForm (n : ℕ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun X Y => ((X * Yᴴ).trace).re)
    (fun X X' Y => by rw [Matrix.add_mul, Matrix.trace_add, Complex.add_re])
    (fun c X Y => by rw [Matrix.smul_mul, Matrix.trace_smul, Complex.smul_re])
    (fun X Y Y' => by
      rw [Matrix.conjTranspose_add, Matrix.mul_add, Matrix.trace_add, Complex.add_re])
    (fun c X Y => by
      rw [Matrix.conjTranspose_smul, star_trivial, Matrix.mul_smul, Matrix.trace_smul,
        Complex.smul_re])

theorem trForm_apply (X Y : Matrix (Fin n) (Fin n) ℂ) : trForm n X Y = ((X * Yᴴ).trace).re := rfl

theorem trForm_comm (X Y : Matrix (Fin n) (Fin n) ℂ) : trForm n X Y = trForm n Y X := by
  have : Y * Xᴴ = (X * Yᴴ)ᴴ := by rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [trForm_apply, trForm_apply, this, Matrix.trace_conjTranspose, Complex.star_def,
    Complex.conj_re]

theorem hs_eq (g : Matrix (Fin n) (Fin n) ℂ) : hs g = trForm n g g := by
  simp only [trForm_apply, hs, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  norm_cast

theorem hs_nonneg (g : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hs g := by
  unfold hs; positivity

def coord (E : Fin d → Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] EuclideanSpace ℝ (Fin d) where
  toFun X := WithLp.toLp 2 (fun i => trForm n X (E i))
  map_add' X Y := by ext i; simp
  map_smul' c X := by ext i; simp

theorem norm_coord (E : Fin d → Matrix (Fin n) (Fin n) ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    ‖coord E X‖ = Real.sqrt (∑ i, trForm n X (E i) ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  simp [coord]

theorem trForm_sum (E : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (hE : ∀ i k, trForm n (E i) (E k) = if i = k then 1 else 0) (a : Fin d → ℝ) (k : Fin d) :
    trForm n (∑ i, a i • E i) (E k) = a k := by

  simp [map_sum, LinearMap.sum_apply, hE]

theorem hs_sum (E : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (hE : ∀ i k, trForm n (E i) (E k) = if i = k then 1 else 0) (a : Fin d → ℝ) :
    hs (∑ i, a i • E i) = ∑ i, a i ^ 2 := by

  rw [hs_eq, map_sum (trForm n (∑ i, a i • E i))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, trForm_sum E hE, smul_eq_mul, sq]

theorem bessel (E : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (hE : ∀ i k, trForm n (E i) (E k) = if i = k then 1 else 0) (X : Matrix (Fin n) (Fin n) ℂ) :
    ‖coord E X‖ ≤ Real.sqrt (hs X) := by
  rw [norm_coord]
  apply Real.sqrt_le_sqrt
  set S := ∑ i, trForm n X (E i) • E i with hS
  have h1 : trForm n S S = ∑ i, trForm n X (E i) ^ 2 := by rw [← hs_eq, hS, hs_sum E hE]
  have h2 : trForm n X S = ∑ i, trForm n X (E i) ^ 2 := by

    rw [hS, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, smul_eq_mul, sq]
  have h3 := hs_nonneg (X - S)
  rw [hs_eq, map_sub, LinearMap.map_sub₂, LinearMap.map_sub₂, trForm_comm S X, h1, h2] at h3
  rw [hs_eq]
  linarith

theorem norm_coord_span (E : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (hE : ∀ i k, trForm n (E i) (E k) = if i = k then 1 else 0) (X : Matrix (Fin n) (Fin n) ℂ)
    (hX : X ∈ Submodule.span ℝ (Set.range E)) : ‖coord E X‖ = Real.sqrt (hs X) := by
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hX
  rw [norm_coord, hs_sum E hE]
  simp only [trForm_sum E hE]

variable {ε : Fin n → Bool}

theorem uMat_inv (g : UJ ε) : uMat g⁻¹ = Jm ε * (uMat g)ᴴ * Jm ε := by
  have hu : (uMat g)ᴴ * Jm ε * uMat g = Jm ε := g.2
  calc uMat g⁻¹ = Jm ε * Jm ε * uMat g⁻¹ := by rw [Jm_mul_self, Matrix.one_mul]
    _ = Jm ε * ((uMat g)ᴴ * Jm ε * uMat g) * uMat g⁻¹ := by rw [hu]
    _ = Jm ε * (uMat g)ᴴ * Jm ε * (uMat g * uMat g⁻¹) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [uMat_mul_inv, Matrix.mul_one]

theorem hs_inv_sub_one (g : UJ ε) : hs (uMat g⁻¹ - 1) = hs (uMat g - 1) := by
  have h1 : uMat g⁻¹ - 1 = Jm ε * (uMat g - 1)ᴴ * Jm ε := by
    rw [uMat_inv, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_one, Jm_mul_self]
  rw [h1, hs_eq, hs_eq, trForm_apply, trForm_apply]
  set X := uMat g - 1
  have h2 : Jm ε * Xᴴ * Jm ε * (Jm ε * Xᴴ * Jm ε)ᴴ = Jm ε * (Xᴴ * (Jm ε * Jm ε) * X * Jm ε) := by
    simp only [Matrix.conjTranspose_mul, Jm_conjTranspose, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  rw [h2, Jm_mul_self, Matrix.mul_one, Matrix.trace_mul_comm, Matrix.mul_assoc, Jm_mul_self,
    Matrix.mul_one, Matrix.trace_mul_comm]

theorem sub_inv_mem_lie (g : UJ ε) : uMat g - uMat g⁻¹ ∈ GlobalTheory.GaugeConst.lieJ ε := by
  rw [GlobalTheory.GaugeConst.mem_lieJ, uMat_inv]
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Jm_conjTranspose,
    Matrix.conjTranspose_conjTranspose, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc,
    Jm_mul_self, Matrix.mul_one]
  rw [← Matrix.mul_assoc (Jm ε) (Jm ε), Jm_mul_self, Matrix.one_mul]
  abel

open scoped Matrix.Norms.Frobenius in
theorem lower (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (E : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A)
    (hE : ∀ i k, trForm n (E i) (E k) = if i = k then 1 else 0)
    (hsp : ∀ X, (X ∈ A ∧ inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) (δ : ℝ) (hδ : δ ≤ 1)
    (g h : UJ ε) (hg : uMat g - 1 ∈ A) (hh : uMat h - 1 ∈ A)
    (hg' : Real.sqrt (hs (uMat g - 1)) < δ) (hh' : Real.sqrt (hs (uMat h - 1)) < δ) :
    (1 - 3 * δ) * Real.sqrt (hs (uMat g - uMat h)) ≤ ‖coord E (uMat g - uMat h)‖ := by
  have key : ∀ g : UJ ε, uMat g - 1 ∈ A →
      uMat g - uMat g⁻¹ ∈ Submodule.span ℝ (Set.range E) := by
    intro g hg
    refine (hsp _).1 ⟨?_, sub_inv_mem_lie g⟩
    have := A.sub_mem hg (inv_sub_one_mem A hA g hg)
    rwa [sub_sub_sub_cancel_right] at this
  have hv := Submodule.sub_mem _ (key g hg) (key h hh)
  rw [← hs_inv_sub_one, GlobalTheory.GaugeConst.sqrt_hs] at hg' hh'
  have e1 : uMat g⁻¹ * (uMat g - uMat h) * uMat h⁻¹ = uMat h⁻¹ - uMat g⁻¹ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, uMat_inv_mul, Matrix.one_mul, Matrix.mul_assoc,
      uMat_mul_inv, Matrix.mul_one]
  set v := uMat g - uMat g⁻¹ - (uMat h - uMat h⁻¹) with hvdef
  set D := uMat g - uMat h with hD
  set a := uMat g⁻¹ - 1 with ha
  set b := uMat h⁻¹ - 1 with hb
  have e2 : v = (2 : ℝ) • D + (a * D * b + a * D + D * b) := by
    have : a * D * b + a * D + D * b = uMat g⁻¹ * D * uMat h⁻¹ - D := by
      rw [ha, hb]; noncomm_ring
    rw [this, e1, hvdef, hD, two_smul]; abel
  set R := a * D * b + a * D + D * b with hR
  have ha0 := norm_nonneg a
  have hb0 := norm_nonneg b
  have hD0 := norm_nonneg D
  have n1 : ‖a * D‖ ≤ δ * ‖D‖ :=
    (Matrix.frobenius_norm_mul a D).trans (mul_le_mul_of_nonneg_right hg'.le hD0)
  have n2 : ‖D * b‖ ≤ ‖D‖ * δ :=
    (Matrix.frobenius_norm_mul D b).trans (mul_le_mul_of_nonneg_left hh'.le hD0)
  have n3 : ‖a * D * b‖ ≤ δ * ‖D‖ :=
    (Matrix.frobenius_norm_mul _ b).trans
      ((mul_le_of_le_one_right (norm_nonneg _) (hh'.le.trans hδ)).trans n1)
  have n4 : ‖R‖ ≤ 3 * δ * ‖D‖ := by
    have := norm_add₃_le (a := a * D * b) (b := a * D) (c := D * b)
    linarith
  have p1 := norm_coord_span E hE v hv
  have p2 := bessel E hE R
  rw [GlobalTheory.GaugeConst.sqrt_hs] at p1 p2 ⊢
  have p3 : ‖coord E v‖ ≤ 2 * ‖coord E D‖ + ‖coord E R‖ := by
    rw [e2, map_add (f := _), map_smul]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_two]
  have p4 : 2 * ‖D‖ ≤ ‖v‖ + ‖R‖ := by
    have : (2 : ℝ) • D = v - R := by rw [e2, add_sub_cancel_right]
    have h5 := norm_sub_le v R
    rwa [← this, norm_smul, Real.norm_two] at h5
  linarith

theorem chart_almost_isometric : ∀ (n : ℕ) (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) → (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) → (∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) → ∀ κ : ℝ, 1 < κ → ∃ δ : ℝ, 0 < δ ∧ ∀ g h : Formalism.REAL.UJ ε, uMat g - 1 ∈ A → uMat h - 1 ∈ A → Real.sqrt (Formalism.REAL.hs (uMat g - 1)) < δ → Real.sqrt (Formalism.REAL.hs (uMat h - 1)) < δ → ‖(WithLp.toLp 2 (fun i => (((uMat g - 1) * (E i)ᴴ).trace).re) : EuclideanSpace ℝ (Fin d)) - (WithLp.toLp 2 (fun i => (((uMat h - 1) * (E i)ᴴ).trace).re) : EuclideanSpace ℝ (Fin d))‖ ≤ Real.sqrt (Formalism.REAL.hs (uMat g - uMat h)) ∧ Real.sqrt (Formalism.REAL.hs (uMat g - uMat h)) ≤ κ * ‖(WithLp.toLp 2 (fun i => (((uMat g - 1) * (E i)ᴴ).trace).re) : EuclideanSpace ℝ (Fin d)) - (WithLp.toLp 2 (fun i => (((uMat h - 1) * (E i)ᴴ).trace).re) : EuclideanSpace ℝ (Fin d))‖ := by
  intro n ε A d E hA hE hsp κ hκ
  have hk : κ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hκ
  have hk0 : 0 < κ⁻¹ := inv_pos.2 (by linarith)
  refine ⟨(1 - κ⁻¹) / 3, by linarith, fun g h hg hh hg' hh' => ?_⟩
  have e : (WithLp.toLp 2 (fun i => (((uMat g - 1) * (E i)ᴴ).trace).re) : EuclideanSpace ℝ (Fin d)) - (WithLp.toLp 2 (fun i => (((uMat h - 1) * (E i)ᴴ).trace).re) : EuclideanSpace ℝ (Fin d)) = coord E (uMat g - uMat h) := by
    change coord E (uMat g - 1) - coord E (uMat h - 1) = _
    rw [← map_sub, sub_sub_sub_cancel_right]
  rw [e]
  refine ⟨bessel E hE _, ?_⟩
  have h1 := lower A E hA hE hsp _ (by linarith) g h hg hh hg' hh'
  have h2 : 1 - 3 * ((1 - κ⁻¹) / 3) = κ⁻¹ := by ring
  rw [h2] at h1
  exact (inv_mul_le_iff₀ (by linarith)).1 h1

end GlobalTheory.GaugeSubLip
end
end

section

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.Swap

open GlobalTheory.Amp.Rad GlobalTheory.Amp.UEmb

variable {k r : ℕ}

theorem mI_eq (j : Fin (k + 1)) : mI k r j = wI k r j := rfl

def rowAct (u : Matrix (Fin r) (Fin r) ℂ) (B : Fin r → Fin (k + 1) → ℂ) : Fin r → Fin (k + 1) → ℂ :=
  fun a j => ∑ c, star (u a c) * B c j

theorem herm_rowAct (u : Matrix (Fin r) (Fin r) ℂ) (B : Fin r → Fin (k + 1) → ℂ) :
    (Matrix.of fun a b => herm (Hb k) (rowAct u B b) (rowAct u B a)) =
      u * (Matrix.of fun a b => herm (Hb k) (B b) (B a)) * uᴴ := by
  ext a b
  simp only [Matrix.of_apply, Matrix.mul_apply, herm_Hb, rowAct, star_sum, star_mul', star_star,
    Matrix.conjTranspose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => by ring

theorem uEmb_mul_pEl (u : Matrix (Fin r) (Fin r) ℂ) (hu : IsUnit u.det) (B : Fin r → Fin (k + 1) → ℂ)
    (S : Matrix (Fin r) (Fin r) ℂ) :
    uEmb k r u * pEl k r B S = pEl k r (rowAct u B) (u * S * uᴴ) * uEmb k r u := by
  have h1 : ∀ a b, ∑ c, u⁻¹ a c * u c b = if a = b then 1 else 0 := fun a b => by
    rw [← Matrix.mul_apply, Matrix.nonsing_inv_mul u hu, Matrix.one_apply]
  have h2 : uᴴ * (u⁻¹)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.nonsing_inv_mul u hu, Matrix.conjTranspose_one]
  ext x y
  rw [Matrix.mul_apply, Matrix.mul_apply, sum3, sum3]
  induction x using cases3 <;> induction y using cases3 <;>
    simp only [pEl_ee, pEl_ew, pEl_es, pEl_we, pEl_ww, pEl_ws, pEl_se, pEl_sw, pEl_ss, ← mI_eq,
      u_ee, u_em, u_es, u_me, u_mm, u_ms, u_se, u_sm, u_ss] <;> simp only [mI_eq] <;>
    simp [pEl_ee, pEl_ew, pEl_es, pEl_we, pEl_ww, pEl_ws, pEl_se, pEl_sw, pEl_ss]
  · simp [rowAct, Finset.sum_mul, mul_assoc]
  · rename_i a b
    set G : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun a b => herm (Hb k) (B b) (B a) with hG
    have h3 : ∀ a c, herm (Hb k) (rowAct u B c) (rowAct u B a) = (u * G * uᴴ) a c := fun a c =>
      congrFun (congrFun (herm_rowAct u B) a) c
    have h4 : u * (S - (1 / 2 : ℂ) • G) = (u * S * uᴴ - (1 / 2 : ℂ) • (u * G * uᴴ)) * (u⁻¹)ᴴ := by
      rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_assoc _ uᴴ, Matrix.mul_assoc _ uᴴ, h2, Matrix.mul_one,
        Matrix.mul_one, Matrix.mul_sub, Matrix.mul_smul]
    have h5 := congrFun (congrFun h4 a) b
    rw [Matrix.mul_apply, Matrix.mul_apply] at h5
    simp only [h3]
    convert h5 using 2 with c _ c _
    · simp [hG, div_eq_inv_mul]
    · simp [div_eq_inv_mul]
  · rename_i i b
    simp only [rowAct, Finset.sum_mul]
    rw [Finset.sum_comm]
    have : ∀ d, ∑ c, star (u c d) * B d i * (starRingEnd ℂ) (u⁻¹ b c) = star (∑ c, u⁻¹ b c * u c d) * B d i := by
      intro d
      rw [star_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun c _ => by simp; ring
    simp only [this, h1]
    simp [apply_ite (starRingEnd ℂ)]

theorem det_eq_one {V W : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] [AddCommGroup W] [Module ℝ W]
    (ι : V →ₗ[ℝ] W) (hι : Function.Injective ι) (L : Module.End ℝ V) (T : Module.End ℝ W)
    (h : ∀ v, ι (L v) = T (ι v)) (hT : IsNilpotent (T - 1)) : LinearMap.det L = 1 := by
  have hL : IsNilpotent (L - 1) := by
    obtain ⟨n, hn⟩ := hT
    have : ∀ (m : ℕ) (v : V), ι (((L - 1) ^ m) v) = ((T - 1) ^ m) (ι v) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => intro v; simp [pow_succ, ih, h]
    refine ⟨n, LinearMap.ext fun v => hι ?_⟩
    rw [this, hn]; simp
  have hc := hL.neg.charpoly_eq_X_pow_finrank
  have he := LinearMap.eval_charpoly (-(L - 1)) 1
  rw [hc] at he
  simpa using he.symm

theorem nil_mul {R : Type*} [Ring R] {a b : R} (h : Commute a b) (ha : IsNilpotent (a - 1)) (hb : IsNilpotent (b - 1)) :
    IsNilpotent (a * b - 1) := by
  have e : a * b - 1 = (a - 1) * b + (b - 1) := by noncomm_ring
  have c1 : Commute (a - 1) b := h.sub_left (Commute.one_left b)
  rw [e]
  refine Commute.isNilpotent_add ?_ (c1.isNilpotent_mul_right ha) hb
  exact Commute.mul_left (c1.sub_right (Commute.one_right _)) ((Commute.refl b).sub_right (Commute.one_right _))

theorem nil_upper (x : UT r → ℂ) : IsNilpotent (upper x - 1) := by
  have hc : (upper x - 1).charpoly = Polynomial.X ^ r := by
    rw [Matrix.charpoly_of_upperTriangular]
    · simp [upper]
    · intro a b h
      have h : b < a := h
      simp [upper, h.not_gt, h.ne']
  have := Matrix.aeval_self_charpoly (upper x - 1)
  rw [hc] at this
  exact ⟨r, by simpa using this⟩

def rowLin (k : ℕ) (u : Matrix (Fin r) (Fin r) ℂ) : Module.End ℝ (Fin r → Fin (k + 1) → ℂ) where
  toFun := rowAct u
  map_add' B B' := by ext a j; simp [rowAct, mul_add, Finset.sum_add_distrib]
  map_smul' c B := by
    ext a j; simp only [rowAct, Pi.smul_apply, RingHom.id_apply, Finset.smul_sum, mul_smul_comm]

def skewLin (r : ℕ) : ((UT r → ℂ) × (Fin r → ℝ)) →ₗ[ℝ] Matrix (Fin r) (Fin r) ℂ where
  toFun p := skewM p.1 p.2
  map_add' p q := by
    ext a b; simp only [skewM, Matrix.add_apply, Prod.fst_add, Prod.snd_add, Pi.add_apply]
    split_ifs <;> simp <;> ring
  map_smul' c p := by
    ext a b; simp only [skewM, Matrix.smul_apply, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp <;> ring

def coordLin (r : ℕ) : Matrix (Fin r) (Fin r) ℂ →ₗ[ℝ] ((UT r → ℂ) × (Fin r → ℝ)) where
  toFun S := (fun q => S q.1.1 q.1.2, fun a => (S a a).im)
  map_add' S T := by ext <;> simp
  map_smul' c S := by ext <;> simp

theorem coord_skew (p : (UT r → ℂ) × (Fin r → ℝ)) : coordLin r (skewLin r p) = p := by
  ext q
  · simp [coordLin, skewLin, skewM, q.2]
  · simp [coordLin, skewLin, skewM]

theorem skew_coord (S : Matrix (Fin r) (Fin r) ℂ) (hS : Sᴴ = -S) : skewLin r (coordLin r S) = S := by
  obtain ⟨p, hp, -⟩ := skewM_unique S hS
  have : S = skewLin r p := hp
  rw [this, coord_skew]

def conjLin (u : Matrix (Fin r) (Fin r) ℂ) : Module.End ℝ (Matrix (Fin r) (Fin r) ℂ) :=
  LinearMap.mulLeft ℝ u * LinearMap.mulRight ℝ uᴴ

def skewAct (u : Matrix (Fin r) (Fin r) ℂ) : Module.End ℝ ((UT r → ℂ) × (Fin r → ℝ)) :=
  coordLin r ∘ₗ conjLin u ∘ₗ skewLin r

theorem skew_skewAct (u : Matrix (Fin r) (Fin r) ℂ) (p : (UT r → ℂ) × (Fin r → ℝ)) :
    skewLin r (skewAct u p) = u * skewLin r p * uᴴ := by
  have h : (skewLin r p)ᴴ = -skewLin r p := skewM_skew p.1 p.2
  have e : skewAct u p = coordLin r (u * skewLin r p * uᴴ) := by
    simp [skewAct, conjLin, Matrix.mul_assoc]
  rw [e, skew_coord]
  simp [Matrix.conjTranspose_mul, h, Matrix.mul_assoc]

theorem mp_of_det {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure] (L : E →ₗ[ℝ] E) (h : LinearMap.det L = 1) :
    MeasurePreserving L μ μ :=
  ⟨L.continuous_of_finiteDimensional.measurable, by
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar μ (by rw [h]; exact one_ne_zero), h]; simp⟩

def parAct (u : Matrix (Fin r) (Fin r) ℂ) (q : PPar k r) : PPar k r := (rowLin k u q.1, skewAct u q.2)

theorem uEmb_mul_pOf (u : Matrix (Fin r) (Fin r) ℂ) (hu : IsUnit u.det) (q : PPar k r) :
    uEmb k r u * pOf k r q = pOf k r (parAct u q) * uEmb k r u := by
  have h := skew_skewAct u q.2
  unfold pOf
  rw [uEmb_mul_pEl u hu]
  congr 2
  exact h.symm

theorem cont_upper (r : ℕ) : Continuous (upper : (UT r → ℂ) → Matrix (Fin r) (Fin r) ℂ) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  unfold upper
  split_ifs <;> fun_prop

theorem cont_uEmb (k r : ℕ) : Continuous fun x : UT r → ℂ => uEmb k r (upper x) := by
  have hi : Continuous fun x : UT r → ℂ => (upper x)⁻¹ := by
    have : (fun x : UT r → ℂ => (upper x)⁻¹) = fun x => (upper x).adjugate := by
      funext x; rw [Matrix.inv_def, det_upper]; simp
    rw [this]; exact (cont_upper r).matrix_adjugate
  refine continuous_pi fun i => continuous_pi fun j => ?_
  unfold uEmb
  split_ifs
  · exact (cont_upper r).matrix_elem _ _
  · exact (hi.matrix_elem _ _).star
  all_goals exact continuous_const

theorem cont_pOf (k r : ℕ) : Continuous (pOf k r) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  unfold pOf pEl skewM herm Matrix.mulVec dotProduct
  simp only [Pi.star_apply]
  split_ifs <;> fun_prop

theorem cont_parAct (k r : ℕ) : Continuous fun q : (UT r → ℂ) × PPar k r => parAct (upper q.1) q.2 := by
  have hu : Continuous fun q : (UT r → ℂ) × PPar k r => upper q.1 := (cont_upper r).comp continuous_fst
  refine Continuous.prodMk ?_ ?_
  · refine continuous_pi fun a => continuous_pi fun j => ?_
    change Continuous fun q : (UT r → ℂ) × PPar k r => ∑ c, star (upper q.1 a c) * q.2.1 c j
    exact continuous_finsetSum _ fun c _ => (hu.matrix_elem a c).star.mul (by fun_prop)
  · have hs : Continuous fun q : (UT r → ℂ) × PPar k r => skewLin r q.2.2 :=
      (skewLin r).continuous_of_finiteDimensional.comp (by fun_prop)
    exact (coordLin r).continuous_of_finiteDimensional.comp (hu.matrix_mul (hs.matrix_mul hu.matrix_conjTranspose))

end GlobalTheory.Amp.Swap
end
end

section

open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace

namespace GlobalTheory.ThA

theorem qminorOp_eq_qdetOp_of_val {n t : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E))
    (h : t = n) (p : Fin t → Fin n) (hp : ∀ j, (p j).val = j.val) (u : ℂ)
    (f : Matrix (Fin n) (Fin n) ℂ → E) : qminorOp Eop p p u f = qdetOp Eop u f := by
  subst h
  have e : p = id := funext fun j => Fin.ext (hp j)
  rw [e]
  rfl

theorem centredCapelli_forms_agree :
    ∀ (k r : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (Y : ℂ) (F : B.Mat k r → V),
      Q.CV k r Y F = PI.CapelliEig.capC (k := k) (r := r) Y F ∧
        Q.CV k r Y F = Formalism.MainNotions.S.capC (k := k) (r := r) Y F := by
  intro k r V _ _ Y F
  have hm : Q.mdim k r 0 = 2 * r + k + 1 := by simp [Q.mdim]
  have hu : Q.uC k r 0 Y = Y + ((2 * r + k : ℕ) : ℂ) / 2 := by
    unfold Q.uC
    rw [hm]
    push_cast
    ring
  have key : Q.CV k r Y F = capelliH (Hpk k r) (Y + ((2 * r + k : ℕ) : ℂ) / 2) F := by
    unfold Q.CV Q.capL capelliH
    rw [hu]
    exact qminorOp_eq_qdetOp_of_val _ hm _ (fun j => by simp [Q.posL]) _ _
  exact ⟨key, key⟩

end GlobalTheory.ThA
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.neg_log_prod_lValEta_le_and_pos : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ n₀ n : ℕ, 2 ≤ n₀ → -Real.log (∏ M ∈ Finset.Ioc n₀ n, Formalism.HermitianLatticesTheory.lValEta E M) ≤ Formalism.HermitianLatticesTheory.fDeg E * (2 : ℝ) ^ ((1 : ℤ) - n₀) ∧ 0 < ∏ M ∈ Finset.Ioc n₀ n, Formalism.HermitianLatticesTheory.lValEta E M := by
  first | exact @GlobalTheory.FlagMeas.LProd.neg_log_prod_le | exact GlobalTheory.FlagMeas.LProd.neg_log_prod_le | (intros; apply GlobalTheory.FlagMeas.LProd.neg_log_prod_le <;> assumption)
end
