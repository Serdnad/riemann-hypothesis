module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
public import Mathlib.RingTheory.SimpleRing.Principal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle070
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle072
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.LandherrStIffLandherr
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsCongrIffTraceFormsIsometricCm
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsZeroCoordNeZero
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle073
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsOrthogonalBasisDotProductApplyEq
import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.AlgebraMapNormOfBasisOneSqrt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle015
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Lemma
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle003
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1

@[expose] public section

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.UTrans

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.UTrans.herm_diagonal_self {r : ℕ} (g u : Fin r → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.herm (Matrix.diagonal g) u u = ∑ i, u i * g i * _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (u i) := by
  simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.herm, diagonal_apply, mul_ite, ite_mul]


open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.UTrans.exists_isotropic_diagonal {n : ℕ} (hn : 3 ≤ n) {g : Fin n → E}
    (hg : ∀ i, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (g i) = g i) (hg0 : ∀ i, g i ≠ 0)
    (hs : ∀ τ : E →+* ℂ, (∃ i, 0 < (τ (g i)).re) ∧ ∃ j, (τ (g j)).re < 0) :
    ∃ z : Fin n → E, z ≠ 0 ∧ _root_.ReciprocityTheory.ChartRestriction.G.FD.herm (Matrix.diagonal g) z z = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hiso : _root_.GlobalTheory.LocalQuad.HermClass.Isotropy := fun F _ _ ι _ a h5 ha hsgn =>
    _root_.GlobalTheory.LocalQuad.isotropic_of_indefinite _root_.GlobalTheory.QNorm.hasseNormSt F a h5 ha hsgn
  have hsign : ∀ τ : E →+* ℂ, ∃ k : Fin m, 0 < (τ (g k.succ)).re ↔ 0 < (τ (-g 0)).re := by
    intro τ
    obtain ⟨⟨i, hi⟩, j, hj⟩ := hs τ
    have h0 : (τ (g 0)).re ≠ 0 := _root_.GlobalTheory.LocalQuad.HermClass.re_ne_zero τ (hg 0) (hg0 0)
    rw [map_neg, Complex.neg_re]
    by_cases hpos : 0 < (τ (g 0)).re
    · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨k, rfl⟩
      · exact absurd hj (not_lt.2 hpos.le)
      · exact ⟨k, iff_of_false (not_lt.2 hj.le) (by linarith)⟩
    · have hneg : (τ (g 0)).re < 0 := lt_of_le_of_ne (not_lt.1 hpos) h0
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨k, rfl⟩
      · exact absurd hi hpos
      · exact ⟨k, iff_of_true hi (by linarith)⟩
  have hc : _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (-g 0) = -g 0 := by
    show IsCMField.complexConj E (-g 0) = -g 0
    rw [map_neg]
    exact congrArg Neg.neg (hg 0)
  obtain ⟨w, hw⟩ := _root_.GlobalTheory.LocalQuad.HermClass.exists_represent hiso (r := m) (by omega)
    (g := fun k => g k.succ) (fun k => hg _) (fun k => hg0 _) hc (neg_ne_zero.2 (hg0 0)) hsign
  refine ⟨Fin.cons 1 w, fun h => one_ne_zero (α := E) (by simpa using congr_fun h 0), ?_⟩
  rw [_root_.GlobalTheory.UTrans.herm_diagonal_self] at hw ⊢
  rw [Fin.sum_univ_succ]
  have h1 : _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (1 : E) = 1 := map_one (IsCMField.complexConj E)
  simp only [Fin.cons_zero, Fin.cons_succ, one_mul, h1, mul_one]
  rw [hw]
  ring

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma herm_eq_dotProduct_mulVec_cc {r : ℕ} (H : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.herm H x y = x ⬝ᵥ (H *ᵥ fun b => _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (y b)) := by
  simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.herm, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma herm_mulVec_mulVec' {r : ℕ} (G P : Matrix (Fin r) (Fin r) E) (u v : Fin r → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G (P *ᵥ u) (P *ᵥ v) = _root_.ReciprocityTheory.ChartRestriction.G.FD.herm (Pᵀ * G * P.map _root_.ReciprocityTheory.ChartRestriction.G.FD.cc) u v := by
  have hc : (fun b => _root_.ReciprocityTheory.ChartRestriction.G.FD.cc ((P *ᵥ v) b)) = P.map _root_.ReciprocityTheory.ChartRestriction.G.FD.cc *ᵥ fun b => _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (v b) := by
    ext b

    simp [mulVec, dotProduct, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc, map_sum, map_mul]
  rw [herm_eq_dotProduct_mulVec_cc, herm_eq_dotProduct_mulVec_cc, hc, ← mulVec_mulVec, ← mulVec_mulVec,
    dotProduct_mulVec u, vecMul_transpose]

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma re_mul_cc_eq_normSq_mul_re (τ : E →+* ℂ) (y d : E) :
    (τ (y * d * _root_.ReciprocityTheory.ChartRestriction.G.FD.cc y)).re = Complex.normSq (τ y) * (τ d).re := by
  rw [map_mul, map_mul, _root_.GlobalTheory.Published.embedding_cc, mul_right_comm, Complex.mul_conj,
    Complex.re_ofReal_mul]

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma exists_re_pos_of_herm_diagonal_re_pos {r : ℕ} (τ : E →+* ℂ) (d y : Fin r → E)
    (hy : 0 < (τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm (Matrix.diagonal d) y y)).re) : ∃ i, 0 < (τ (d i)).re := by
  by_contra h
  push_neg at h

  rw [_root_.GlobalTheory.UTrans.herm_diagonal_self, map_sum, Complex.re_sum] at hy
  refine absurd hy (not_lt.2 (Finset.sum_nonpos fun i _ => ?_))
  rw [re_mul_cc_eq_normSq_mul_re]
  exact mul_nonpos_of_nonneg_of_nonpos (Complex.normSq_nonneg _) (h i)

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma exists_re_neg_of_herm_diagonal_re_neg {r : ℕ} (τ : E →+* ℂ) (d y : Fin r → E)
    (hy : (τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm (Matrix.diagonal d) y y)).re < 0) : ∃ i, (τ (d i)).re < 0 := by
  by_contra h
  push_neg at h

  rw [_root_.GlobalTheory.UTrans.herm_diagonal_self, map_sum, Complex.re_sum] at hy
  refine absurd hy (not_lt.2 (Finset.sum_nonneg fun i _ => ?_))
  rw [re_mul_cc_eq_normSq_mul_re]
  exact mul_nonneg (Complex.normSq_nonneg _) (h i)


open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.UTrans.exists_isotropic_of_indefinite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E), (∀ a, σ a = IsCMField.complexConj E a) → _root_.GlobalTheory.UTrans.IsHerm σ G → 3 ≤ n → (∀ τ : E →+* ℂ, (∃ x, 0 < (τ (_root_.GlobalTheory.UTrans.hf σ G x x)).re) ∧ ∃ y, (τ (_root_.GlobalTheory.UTrans.hf σ G y y)).re < 0) → ∃ z : Fin n → E, z ≠ 0 ∧ _root_.GlobalTheory.UTrans.hf σ G z z = 0 := by
  intro E _ _ _ n σ G hσ hG hn hs
  have hf : ∀ x y, _root_.GlobalTheory.UTrans.hf σ G x y = _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G x y := by
    intro x y
    simp only [_root_.GlobalTheory.UTrans.hf, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm, hσ]
    rfl
  have hGc : ∀ a b, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (G a b) = G b a := fun a b => by
    rw [← hG.herm a b, hσ]
    rfl
  obtain ⟨P, d, hP, hPd, hd, -⟩ := _root_.GlobalTheory.HermDiag.exists_congr_diagonal_herm hGc
  have hPinv : ∀ x, P *ᵥ (P⁻¹ *ᵥ x) = x := fun x => by
    rw [mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hP), one_mulVec]
  have hform : ∀ y, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G (P *ᵥ y) (P *ᵥ y) = _root_.ReciprocityTheory.ChartRestriction.G.FD.herm (Matrix.diagonal d) y y := fun y => by
    rw [herm_mulVec_mulVec', hPd]
  suffices ∃ y, y ≠ 0 ∧ _root_.ReciprocityTheory.ChartRestriction.G.FD.herm (Matrix.diagonal d) y y = 0 by
    obtain ⟨y, hy, hy0⟩ := this
    exact ⟨P *ᵥ y, fun h => hy (eq_zero_of_mulVec_eq_zero hP h), by rw [hf, hform, hy0]⟩
  by_cases hd0 : ∃ i, d i = 0
  · obtain ⟨i, hi⟩ := hd0
    refine ⟨Pi.single i 1, fun h => one_ne_zero (α := E) (by simpa using congr_fun h i), ?_⟩
    rw [_root_.GlobalTheory.UTrans.herm_diagonal_self, Finset.sum_eq_single i]
    · simp [hi]
    · intro j _ hj
      simp [Pi.single_apply, hj]
    · simp
  · push_neg at hd0
    refine _root_.GlobalTheory.UTrans.exists_isotropic_diagonal hn hd hd0 fun τ => ?_
    obtain ⟨⟨x, hx⟩, y, hy⟩ := hs τ
    rw [hf, ← hPinv x, hform] at hx
    rw [hf, ← hPinv y, hform] at hy
    exact ⟨exists_re_pos_of_herm_diagonal_re_pos τ d _ hx, exists_re_neg_of_herm_diagonal_re_neg τ d _ hy⟩

end GlobalTheory.UTrans
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem exists_basis_one_sqrt_of_finrank_two {F E : Type} [Field F] [CharZero F] [Field E]
    [Algebra F E] (h : Module.finrank F E = 2) :
    ∃ (e : Module.Basis (Fin 2) F E) (δ : F), δ ≠ 0 ∧ e 0 = 1 ∧ e 1 * e 1 = algebraMap F E δ := by
  have : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  have hr : 1 < Module.rank F E := by
    rw [← Module.finrank_eq_rank, h]; norm_num
  obtain ⟨s, hs⟩ := exists_linearIndependent_pair_of_one_lt_rank hr (one_ne_zero (α := E))
  let b := basisOfLinearIndependentOfCardEqFinrank hs (by simp [h])
  have hb0 : b 0 = 1 := by simp [b]
  have hb1 : b 1 = s := by simp [b]
  obtain ⟨p, q, hpq⟩ : ∃ p q : F, s * s = algebraMap F E p + algebraMap F E q * s := by
    refine ⟨b.repr (s * s) 0, b.repr (s * s) 1, ?_⟩
    conv_lhs => rw [← b.sum_repr (s * s), Fin.sum_univ_two, hb0, hb1, Algebra.smul_def,
      Algebra.smul_def, mul_one]
  have ht : LinearIndependent F ![(1 : E), s - algebraMap F E (q / 2)] := by
    rw [LinearIndependent.pair_iff] at hs ⊢
    intro x y hxy
    have := hs (x - y * (q / 2)) y (by
      rw [← hxy]; simp only [Algebra.smul_def, map_sub, map_mul]; ring)
    obtain ⟨h1, rfl⟩ := this
    exact ⟨by simpa using h1, rfl⟩
  have hsq : (s - algebraMap F E (q / 2)) * (s - algebraMap F E (q / 2))
      = algebraMap F E (p + (q / 2) ^ 2) := by
    have hq : algebraMap F E q = 2 * algebraMap F E (q / 2) := by
      rw [← map_ofNat (algebraMap F E) 2, ← map_mul]; congr 1; ring
    rw [map_add (f := _), map_pow]
    rw [hq] at hpq
    linear_combination hpq
  refine ⟨basisOfLinearIndependentOfCardEqFinrank ht (by simp [h]), p + (q / 2) ^ 2, ?_,
    by simp, by simpa using hsq⟩
  intro h0
  rw [h0, map_zero, mul_self_eq_zero] at hsq
  exact ht.ne_zero 1 (by simpa using hsq)

theorem TNorm.exists_sq_sub {F E : Type} [Field F] [Field E] [Algebra F E]
    (e : Module.Basis (Fin 2) F E) (h0 : e 0 = 1) {δ : F} (h1 : e 1 * e 1 = algebraMap F E δ)
    (L : Type) [Field L] [Algebra F L] {x : F} (h : TNorm F E L x) :
    ∃ a b : L, algebraMap F L x = a ^ 2 - algebraMap F L δ * b ^ 2 := by
  obtain ⟨z, hz⟩ := h
  let e' := Algebra.TensorProduct.basis L e
  refine ⟨e'.repr z 0, e'.repr z 1, ?_⟩
  rw [← hz, ← GlobalTheory.Published.norm_of_basis_one_sqrt e'
    (by rw [Algebra.TensorProduct.basis_apply, h0]; rfl) (algebraMap F L δ)
    (by
      rw [Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, h1,
        ← IsScalarTower.algebraMap_apply]
      exact (Algebra.TensorProduct.algebraMap_apply' δ).symm)]
  congr 1
  conv_lhs => rw [← e'.sum_repr z, Fin.sum_univ_two]

theorem np_of_finrank_two : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Module.finrank F E = 2 → NP F E := by
  intro F E _ _ _ _ _ h x hx hloc
  obtain ⟨e, δ, hδ, h0, h1⟩ := exists_basis_one_sqrt_of_finrank_two h
  obtain ⟨a, b, hab⟩ := GlobalTheory.QNorm.hasseNormSt F δ x hδ hx
    (fun σ => @TNorm.exists_sq_sub F E _ _ _ e h0 δ h1 ℝ _ σ.toAlgebra x (hloc.2 σ.toAlgebra))
    (fun v => TNorm.exists_sq_sub e h0 h1 _ (hloc.1 v))
  exact ⟨_, (GlobalTheory.Published.norm_of_basis_one_sqrt e h0 δ h1 a b).trans hab.symm⟩

end GlobalTheory.CNorm
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockCompare GlobalTheory.VacUnique

noncomputable section

namespace GlobalTheory.RatSelfDual

variable {D : D7}

def symplB (S T : HSp D) : WO S T →+ WO S T →+ AF D.host.F :=
  AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun y => symplO S T x y) ((GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt D S T).2.1 x))
    (fun x x' => AddMonoidHom.ext fun y => (GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt D S T).1 x x' y)

theorem symplO_nsmul (S T : HSp D) (N : ℕ) (x y : WO S T) :
    symplO S T x (N • y) = symplO S T (N • x) y := by
  have h1 : symplO S T x (N • y) = N • symplO S T x y := (symplB S T x).map_nsmul N y
  have h2 : symplO S T (N • x) y = N • symplO S T x y := ((symplB S T).flip y).map_nsmul N x
  rw [h1, h2]

theorem symplO_eq_add (S T : HSp D) (x y : WO S T) : symplO S T x y = symplOH S T x y + symplOH S T x y := by
  unfold symplOH
  rw [← add_mul, ← RingHom.map_add (f := _), add_halves, RingHom.map_one, one_mul]

theorem psi_real {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ} (hθ : IsInfFam θ) (hψ : IsStdChar D ψ (-1))
    (S T : HSp D) (x y : WO S T) (h : x.map (finPart D) = 0 ∨ y.map (finPart D) = 0) :
    ψ (symplO S T x y) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (omO S T (piW θ T S x) (piW θ T S y) : ℂ)) := by
  rw [symplO_eq_add, AddChar.map_add_eq_mul, GlobalTheory.OrientedChar.char_symplOH D θ ψ hθ hψ S T x y h, ← Complex.exp_add]
  congr 1
  ring

theorem psi_fin_mul {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D)
    (x y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    ψ (symplO S T (finRat S T x) (finRat S T y)) *
      Complex.exp (-(2 * Real.pi * Complex.I) * (omO S T (infRat S T x) (infRat S T y) : ℂ)) = 1 := by
  obtain ⟨θ, hθ⟩ := hψ.2.1
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨a, ha⟩ := (GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt D S T).2.2.2.2 x y
  have h1 : ψ (symplO S T (ratW T S x) (ratW T S y)) = 1 := by rw [ha]; exact hψ.1.2.2.1 a
  have hx : (iotaW σ T S (infRat S T x) : WO S T).map (finPart D) = 0 := hσ.real_iota T S _
  have hy : (iotaW σ T S (infRat S T y) : WO S T).map (finPart D) = 0 := hσ.real_iota T S _
  have e1 := psi_real hθ hψ S T (iotaW σ T S (infRat S T x)) (ratW T S y) (Or.inl hx)
  have e2 := psi_real hθ hψ S T (finRat S T x) (iotaW σ T S (infRat S T y)) (Or.inr hy)
  rw [hσ.pi_iota, piW_ratW hθ] at e1
  rw [piW_of_inf θ (finRat_inf S T x), LinearMap.map_zero, LinearMap.zero_apply, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero] at e2
  have d1 : symplO S T (ratW T S x) (ratW T S y) =
      symplO S T (iotaW σ T S (infRat S T x)) (ratW T S y) + symplO S T (finRat S T x) (ratW T S y) :=
    (congrArg (fun w => symplO S T w (ratW T S y)) (ratW_eq hσ S T x)).trans ((GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt D S T).1 _ _ _)
  have d2 : symplO S T (finRat S T x) (ratW T S y) =
      symplO S T (finRat S T x) (iotaW σ T S (infRat S T y)) + symplO S T (finRat S T x) (finRat S T y) :=
    (congrArg (fun w => symplO S T (finRat S T x) w) (ratW_eq hσ S T y)).trans ((GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt D S T).2.1 _ _ _)
  rw [d1, d2, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, e1, e2, one_mul, mul_comm] at h1
  exact h1

theorem psi_fin_iff {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D)
    (x y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    ψ (symplO S T (finRat S T x) (finRat S T y)) = 1 ↔ ∃ k : ℤ, omO S T (infRat S T x) (infRat S T y) = k := by
  have h := psi_fin_mul hψ S T x y
  constructor
  · intro h1
    rw [h1, one_mul, Complex.exp_eq_one_iff] at h
    obtain ⟨n, hn⟩ := h
    refine ⟨-n, ?_⟩
    have h2 : ((omO S T (infRat S T x) (infRat S T y) : ℝ) : ℂ) = ((-n : ℤ) : ℂ) := by
      apply mul_left_cancel₀ (neg_ne_zero.2 Complex.two_pi_I_ne_zero)
      rw [hn]; push_cast; ring
    exact_mod_cast h2
  · rintro ⟨k, hk⟩
    have h2 : Complex.exp (-(2 * Real.pi * Complex.I) * (omO S T (infRat S T x) (infRat S T y) : ℂ)) = 1 := by
      rw [hk, Complex.exp_eq_one_iff]
      exact ⟨-k, by push_cast; ring⟩
    rwa [h2, mul_one] at h

theorem eq_zero_of_parts {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D} {z : WO S T}
    (hf : z.map (finPart D) = 0) (hi : z.map (infPart D) = 0) : z = 0 := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  funext i j
  refine hσ.ext _ (congrFun (congrFun hf i) j) fun τ => ?_
  have : infPart D (z i j) = 0 := congrFun (congrFun hi i) j
  rw [this, RingHom.map_zero]

theorem exists_div {S T : HSp D} {u : WO S T} (hu : u.map (infPart D) = 0) {N : ℕ} (hN : 0 < N) :
    ∃ γ : WO S T, γ.map (infPart D) = 0 ∧ N • γ = u := by
  refine ⟨Matrix.of fun i j => incA D ((N : D.host.E)⁻¹) * u i j, ?_, ?_⟩
  · funext i j
    have : infPart D (u i j) = 0 := congrFun (congrFun hu i) j
    show infPart D (incA D ((N : D.host.E)⁻¹) * u i j) = 0
    rw [RingHom.map_mul, this, mul_zero]
  · funext i j
    show N • (incA D ((N : D.host.E)⁻¹) * u i j) = u i j
    have h1 : (N : AE D) = incA D (N : D.host.E) := (map_natCast (incA D) N).symm
    have h2 : (N : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    rw [nsmul_eq_mul, ← mul_assoc, h1, ← map_mul, mul_inv_cancel₀ h2, map_one, one_mul]

theorem finRat_mem_iff : ∀ (D : D7) (S T : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (Λ : AddSubgroup (WO S T)), IsStdChar D ψ (-1) → (∀ u ∈ Λ, u.map (infPart D) = 0) → (∀ u : WO S T, u.map (infPart D) = 0 → (u ∈ Λ ↔ ∀ u' ∈ Λ, ψ (symplO S T u u') = 1)) → (∀ γ : WO S T, γ.map (infPart D) = 0 → ∃ ρ ∈ ratL T S, ∃ u ∈ Λ, (γ - ρ - u).map (finPart D) = 0) → (∀ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ N : ℕ, 0 < N ∧ N • finRat S T γ ∈ Λ) → ∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, finRat S T x ∈ Λ ↔ ∀ y : Matrix (Fin T.rank) (Fin S.rank) D.host.E, finRat S T y ∈ Λ → ∃ k : ℤ, omO S T (infRat S T x) (infRat S T y) = k := by
  intro D S T ψ Λ hψ hinf hdual happ hden x
  constructor
  · intro hx y hy
    exact (psi_fin_iff hψ S T x y).1 ((hdual _ (finRat_inf S T x)).1 hx _ hy)
  · intro h
    refine (hdual _ (finRat_inf S T x)).2 fun u' hu' => ?_
    obtain ⟨θ, hθ⟩ := hψ.2.1
    obtain ⟨N, hN, hNx⟩ := hden x
    obtain ⟨γ, hγ, hNγ⟩ := exists_div (hinf u' hu') hN
    obtain ⟨ρ, ⟨y₀, hy₀⟩, u, hu, hz⟩ := happ γ hγ
    have hz0 : γ - finRat S T y₀ - u = 0 := by
      refine eq_zero_of_parts hθ ?_ ?_
      · funext i j
        have e0 : finPart D (γ i j - ρ i j - u i j) = 0 := congrFun (congrFun hz i) j
        have e1 : finPart D (finRat S T y₀ i j) = finPart D (ρ i j) := by rw [← hy₀]; rfl
        show finPart D (γ i j - finRat S T y₀ i j - u i j) = 0
        rw [RingHom.map_sub, RingHom.map_sub] at e0 ⊢
        rw [e1, e0]
      · funext i j
        have e0 : infPart D (γ i j) = 0 := congrFun (congrFun hγ i) j
        have e1 : infPart D (finRat S T y₀ i j) = 0 := congrFun (congrFun (finRat_inf S T y₀) i) j
        have e2 : infPart D (u i j) = 0 := congrFun (congrFun (hinf u hu) i) j
        show infPart D (γ i j - finRat S T y₀ i j - u i j) = 0
        rw [RingHom.map_sub, RingHom.map_sub, e0, e1, e2, sub_zero, sub_zero]
    have hγe : γ = finRat S T y₀ + u := by
      rw [sub_sub] at hz0
      exact sub_eq_zero.1 hz0
    have hu'e : u' = finRat S T (N • y₀) + N • u := by
      rw [← hNγ, hγe, nsmul_add, (finRat S T).map_nsmul]
    have hmem : finRat S T (N • y₀) ∈ Λ := by
      have : finRat S T (N • y₀) = u' - N • u := (sub_eq_of_eq_add hu'e).symm
      rw [this]
      exact Λ.sub_mem hu' (Λ.nsmul_mem hu N)
    rw [hu'e, (GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt D S T).2.1, AddChar.map_add_eq_mul, (psi_fin_iff hψ S T x _).2 (h _ hmem), one_mul,
      symplO_nsmul]
    exact (hdual _ (hinf _ hNx)).1 hNx u hu

end GlobalTheory.RatSelfDual

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_realPlace_symplecticForm_positiveComplexStructure : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), IsStdChar D ψ (-1) → IsInfFam θ → (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∃ (om : GlobalTheory.FockCompare.RW T S →ₗ[ℝ] GlobalTheory.FockCompare.RW T S →ₗ[ℝ] ℝ) (J : GlobalTheory.FockCompare.RW T S →ₗ[ℝ] GlobalTheory.FockCompare.RW T S), (∀ x y : WO S T, y.map (finPart D) = 0 → ψ (symplOH S T x y) = Complex.exp (-(Real.pi * Complex.I) * (om (GlobalTheory.FockCompare.piW θ T S x) (GlobalTheory.FockCompare.piW θ T S y) : ℝ))) ∧ (∀ z τ, J z τ = cplxO (sS τ) (sT τ) (z τ)) ∧ (∀ v, om v v = 0) ∧ (∀ v, J (J v) = -v) ∧ (∀ x y, om x (J y) = om y (J x)) ∧ ∀ v, v ≠ 0 → 0 < om v (J v) := by
  first | exact @GlobalTheory.OrientedRealForm.exists_real_form | exact GlobalTheory.OrientedRealForm.exists_real_form | (intros; apply GlobalTheory.OrientedRealForm.exists_real_form <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

theorem _root_.GlobalTheory.T.hasse_norm_theorem_quadratic_extension : GlobalTheory.Published.HasseNormSt := by
  first | exact @GlobalTheory.QNorm.hasseNormSt | exact GlobalTheory.QNorm.hasseNormSt | (intros; apply GlobalTheory.QNorm.hasseNormSt <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm


open NumberField IsDedekindDomain in
open scoped WithZero in
theorem _root_.GlobalTheory.QNorm.landherr_and_landherrSt :
    _root_.GlobalTheory.Published.Landherr ∧ _root_.GlobalTheory.Published.LandherrSt :=
  ⟨_root_.GlobalTheory.LocalQuad.landherr_of_hasseNormSt _root_.GlobalTheory.QNorm.hasseNormSt,
    _root_.GlobalTheory.LocalQuad.landherrSt_of_hasseNormSt _root_.GlobalTheory.QNorm.hasseNormSt⟩

end GlobalTheory.QNorm
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.continuous_character_finite_order_integral_units : ∀ (D : D7) (χ : (AE D)ˣ →* Circle), Continuous χ → ∃ N : ℕ, 0 < N ∧ (∀ x, FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = N • y) → χ x = 1) ∧ ∃ m : ℕ, 0 < m ∧ ∀ x, FinUnit x → χ x ^ m = 1 := by
  first | exact @GlobalTheory.CharFin.char_finUnit_finite_order | exact GlobalTheory.CharFin.char_finUnit_finite_order | (intros; apply GlobalTheory.CharFin.char_finUnit_finite_order <;> assumption)
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.classNumber_finite_integralLevel_closedSubgroupGL : ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F)), (∀ (B : Type) [CommRing B] [Algebra F B], (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((1 : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) ∧ (∀ g h : GL (Fin n) B, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((h : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g * h : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0)) ∧ ∀ g : GL (Fin n) B, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g⁻¹ : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0)) → ∃ T : Finset (GL (Fin n) (FiniteAdeleRing (𝓞 F) F)), (∀ s ∈ T, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((s : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) ij.1 ij.2) P = 0)) ∧ ∀ x : GL (Fin n) (FiniteAdeleRing (𝓞 F) F), (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((x : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) ij.1 ij.2) P = 0) → ∃ γ : GL (Fin n) F, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((γ : GL (Fin n) (F)) : Matrix (Fin n) (Fin n) (F)) ij.1 ij.2) P = 0) ∧ ∃ s ∈ T, ∃ u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F), (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) ij.1 ij.2) P = 0) ∧ (∀ i j, (∀ v, (((u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) i j : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧ (∀ v, ((((u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F))⁻¹ : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) i j : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v)) ∧ x = Units.map (RingHom.mapMatrix (algebraMap F (FiniteAdeleRing (𝓞 F) F))).toMonoidHom γ * s * u := by
  first | exact @GlobalTheory.ClassFin.classFinite_integralLevel | exact GlobalTheory.ClassFin.classFinite_integralLevel | (intros; apply GlobalTheory.ClassFin.classFinite_integralLevel <;> assumption)
end
