module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1398
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle559
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle543
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle544
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle729
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle642
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1623
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1340
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle464
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle272
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1681
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1624
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1682
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1629
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1571
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1680
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle306
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1639
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1684
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1651
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuumRealRestrictionGaussianEntire
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1665
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Development.AbelianVarietyTheory.Definitions.Foundations.StrictInterlaceIffDescEnum
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

noncomputable section

namespace GlobalTheory.KSp.GaussMain

section Scalar

variable {F : Type} [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {E : Type} [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E]
  (c : E →ₐ[F] E) {δ : E} (hE : IsQuad c δ)

def sgnHom : Fˣ →* ℂ where
  toFun := sgn E
  map_one' := by simp only [sgn]; exact if_pos (one_mem _)
  map_mul' s t := GlobalTheory.T.localNormResidueSign_mul F E c δ hE s t

theorem sgn_inv (t : Fˣ) : sgn E t⁻¹ = sgn E t := by
  have h := (Units.map (Algebra.norm F : E →* F)).range.inv_mem_iff (x := t)
  unfold sgn
  by_cases ht : t ∈ (Units.map (Algebra.norm F : E →* F)).range
  · rw [if_pos ht, if_pos (h.mpr ht)]
  · rw [if_neg ht, if_neg (mt h.mp ht)]

variable {ν : Type} [Fintype ν] [DecidableEq ν]

theorem det_herm (a : GL ν E) (D : ν → Fˣ) :
    ((a : Matrix ν ν E) * diagonal (fun j => algebraMap F E (D j)) * ((a : Matrix ν ν E).map c)ᵀ).det =
      (Matrix.GeneralLinearGroup.det a : E) * c (Matrix.GeneralLinearGroup.det a : E) *
        algebraMap F E ((∏ j, D j : Fˣ) : F) := by
  have hm : ((a : Matrix ν ν E).map c).det = c (a : Matrix ν ν E).det := (RingHom.map_det (c : E →+* E) _).symm
  rw [det_mul, det_mul, det_transpose, det_diagonal, hm]
  simp only [Matrix.GeneralLinearGroup.val_det_apply, Units.coe_prod, map_prod]
  ring


include hE in
theorem sc_det_inv (χ : Eˣ →* Circle) (m : ℕ) (hχ : ResEtaPow (R := F) ⊥ χ m) (a : GL ν E) (D : ν → Fˣ) :
    sc F χ m ((a : Matrix ν ν E) * diagonal (fun j => algebraMap F E (D j)) * ((a : Matrix ν ν E).map c)ᵀ).det⁻¹ =
      (((distribHaarChar F (Units.map (Algebra.norm F : E →* F) (Matrix.GeneralLinearGroup.det a)) : ℝ)⁻¹ ^ m : ℝ) : ℂ) *
        (∏ j, (sgn E (D j) * ((nabs F (D j))⁻¹ : ℝ))) ^ m := by
  obtain ⟨-, hmul, -, -, -, halg, hzc⟩ := GlobalTheory.T.unitaryCharacterAbsScalar_basic_properties F E c δ hE m χ hχ
  set d : Eˣ := Matrix.GeneralLinearGroup.det a with hd
  have hdet : ((a : Matrix ν ν E) * diagonal (fun j => algebraMap F E (D j)) * ((a : Matrix ν ν E).map c)ᵀ).det⁻¹ =
      ((d⁻¹ : Eˣ) : E) * c ((d⁻¹ : Eˣ) : E) * algebraMap F E (((∏ j, D j)⁻¹ : Fˣ) : F) := by
    rw [det_herm c a D]
    simp only [hd, Units.val_inv_eq_inv_val, map_inv₀, mul_inv]
  have e1 : nabs F (Units.map (Algebra.norm F : E →* F) d⁻¹) =
      ((distribHaarChar F (Units.map (Algebra.norm F : E →* F) d)) : ℝ)⁻¹ := by
    simp [nabs, map_inv]
  have e2 : sgn E (∏ j, D j)⁻¹ = ∏ j, sgn E (D j) := by
    rw [sgn_inv]; exact map_prod (sgnHom c hE) D Finset.univ
  have e3 : nabs F (∏ j, D j)⁻¹ = ∏ j, (nabs F (D j))⁻¹ := by
    simp [nabs, map_prod, map_inv]
  rw [hdet, hmul, hzc, halg, e1, e2, e3, Finset.prod_mul_distrib]
  push_cast
  ring

end Scalar

section Equiv

variable {E : Type} [Field E] [TopologicalSpace E] [IsTopologicalRing E]
  {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]

def glT (u : GL α E) : GL α E :=
  ⟨(u : Matrix α α E)ᵀ, ((u⁻¹ : GL α E) : Matrix α α E)ᵀ,
    by rw [← transpose_mul, Units.inv_mul, transpose_one], by rw [← transpose_mul, Units.mul_inv, transpose_one]⟩

def sandwich (U : GL α E) (A : GL ν E) : Matrix α ν E ≃ₜ+ Matrix α ν E where
  toFun x := (U : Matrix α α E) * x * (A : Matrix ν ν E)
  invFun y := ((U⁻¹ : GL α E) : Matrix α α E) * y * ((A⁻¹ : GL ν E) : Matrix ν ν E)
  left_inv x := by
    simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  right_inv y := by
    simp only [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  map_add' x y := by simp only [Matrix.mul_add, Matrix.add_mul]
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

end Equiv

theorem hasGauss_herm : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure], ∃ γ₀ : ℂ, ∀ b : Matrix ν ν E, (b.map c)ᵀ = b → b.det ≠ 0 → HasGauss μ (fun x => ψ (2⁻¹ * pr c Q x (x * b))) (γ₀ * sc F χ (Fintype.card α) b.det⁻¹) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ hψ hψ1 hψ0 χ hχc hχ _ _ μ _
  haveI : IsTopologicalRing E := (GlobalTheory.T.quadExt_topological_properties F E c δ hE).2.1
  obtain ⟨u, D', hQd⟩ := GlobalTheory.T.exists_GL_diagonal_congruent_hermitian F E c δ hE α Q (Matrix.ext fun i j => hQ.1 i j) hQ.2.ne_zero
  obtain ⟨g0, hg0⟩ := GlobalTheory.T.gaussIntegral_diagonal_hermitianForm_matrices F E c δ hE α ν ψ hψ hψ1 hψ0 μ
  let s : α → Fˣ := fun i =>
    Units.mk0 (2⁻¹ * (D' i : F)) (mul_ne_zero (inv_ne_zero two_ne_zero) (D' i).ne_zero)
  let U : GL α E := glT u
  refine ⟨g0 * (((distribHaarChar F (Units.map (Algebra.norm F : E →* F) (Matrix.GeneralLinearGroup.det U)) : ℝ)⁻¹ ^
    Fintype.card ν : ℝ) : ℂ) * (∏ i, (sgn E (s i) * ((nabs F (s i))⁻¹ : ℝ))) ^ Fintype.card ν, ?_⟩
  intro b hb hdet
  obtain ⟨a, D, rfl⟩ := GlobalTheory.T.exists_GL_diagonal_congruent_hermitian F E c δ hE ν b hb hdet
  let t : α → ν → Fˣ := fun i j => s i * D j
  have hfun : (fun x : Matrix α ν E => ψ (2⁻¹ * pr c Q x (x * ((a : Matrix ν ν E) *
      diagonal (fun j => algebraMap F E (D j)) * ((a : Matrix ν ν E).map c)ᵀ)))) =
      fun x => (fun y : Matrix α ν E => ψ (∑ i, ∑ j, (t i j : F) * Algebra.norm F (y i j))) (sandwich U a x) := by
    funext x
    rw [GlobalTheory.T.hermitianMatrixColumnPairing_diagonal_norm F E c δ hE α ν Q hQ (u : Matrix α α E) (fun i => (D' i : F)) (a : Matrix ν ν E)
      (fun j => (D j : F)) hQd x]
    congr 1
  have key := GlobalTheory.T.hasGaussIntegral_comp_addEquiv_rescale (Matrix α ν E) (Matrix α ν E) μ μ (sandwich U a) _ _ _
    (GlobalTheory.T.map_twoSided_mul_haar_matrix_quadraticExt F E c δ hE α ν μ U a) (hg0 t)
  rw [hfun]
  convert key using 1
  rw [sc_det_inv c hE χ _ hχ a D]
  have ht : ∀ i j, sgn E (t i j) * (((nabs F (t i j))⁻¹ : ℝ) : ℂ) =
      (sgn E (s i) * (((nabs F (s i))⁻¹ : ℝ) : ℂ)) * (sgn E (D j) * (((nabs F (D j))⁻¹ : ℝ) : ℂ)) := by
    intro i j
    simp only [t]
    rw [GlobalTheory.T.localNormResidueSign_mul F E c δ hE, GlobalTheory.SplitWeil.nabs_mul F, mul_inv]
    push_cast
    ring
  rw [Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ht i j]
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Finset.prod_pow]
  push_cast
  ring

end GlobalTheory.KSp.GaussMain
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.LeviDesc.OrbFin
open GlobalTheory.LeviDesc.Krylov

theorem exists_cyclic {F : Type} [Field F] {r : ℕ} (y : Matrix (Fin r) (Fin r) F) (hy : y.charpoly.Separable) :
    ∃ e : Fin r → F, IsUnit (krylov y e).det :=
  GlobalTheory.T.exists_isUnit_det_krylovMatrix_of_separable y hy

theorem krylov_conj_eq {F : Type} [Field F] {r : ℕ} (y y' : Matrix (Fin r) (Fin r) F) (e e' : Fin r → F)
    (hc : y.charpoly = y'.charpoly) (he : IsUnit (krylov y e).det) (he' : IsUnit (krylov y' e').det) :
    (krylov y e)⁻¹ * y * krylov y e = (krylov y' e')⁻¹ * y' * krylov y' e' :=
  GlobalTheory.T.krylovMatrix_conj_eq_of_charpoly_eq y y' e e' hc he he'

theorem isClosed_charpoly_eq (E : Type) [Field E] [NumberField E] (w : Pl E) (r : ℕ)
    (χ : (w.adicCompletion E)[X]) : IsClosed {y : GLw r w | y.val.charpoly = χ} := by
  haveI : CharZero (w.adicCompletion E) :=
    charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective
  haveI : Infinite (w.adicCompletion E) := Infinite.of_injective Nat.cast Nat.cast_injective
  have hset : {y : GLw r w | y.val.charpoly = χ} =
      ⋂ t : w.adicCompletion E, {y : GLw r w | ((Matrix.scalar (Fin r) t) - y.val).det = χ.eval t} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro hy t; rw [← Matrix.eval_charpoly, hy]
    · intro hy; exact Polynomial.funext fun t => by rw [Matrix.eval_charpoly]; exact hy t
  rw [hset]
  refine isClosed_iInter fun t => isClosed_eq ?_ continuous_const
  exact (continuous_const.sub Units.continuous_val).matrix_det

theorem exists_compact_krylov (E : Type) [Field E] [NumberField E] (w : Pl E) (r : ℕ) (Ω : Set (GLw r w))
    (hΩ : IsCompact Ω) (h : ∀ y ∈ Ω, ∃ e, IsUnit (krylov y.val e).det) :
    ∃ C : Set (GLw r w), IsCompact C ∧ ∀ y ∈ Ω, ∃ e, ∃ c ∈ C, c.val = krylov y.val e :=
  GlobalTheory.T.exists_compact_invertible_krylovMatrices E w r Ω hΩ h

theorem isOpen_KGL (E : Type) [Field E] [NumberField E] (w : Pl E) (r : ℕ) :
    IsOpen (GlobalTheory.LFun.KGL w (n := r) : Set (GLw r w)) :=
  GlobalTheory.LFun.IntPtsUnitary.isOpen_GLint _ (Valued.isOpen_integer (w.adicCompletion E))

theorem orbit_fin (E : Type) [Field E] [NumberField E] (w : Pl E) (r : ℕ) (γ : GLw r w)
    (hs : γ.val.charpoly.Separable) (Ω : Set (GLw r w)) (hΩ : IsCompact Ω) :
    ∃ T : Set (GLw r w), T.Finite ∧ ∀ q : GLw r w, q⁻¹ * γ * q ∈ Ω →
      ∃ z : GLw r w, z * γ = γ * z ∧ ∃ t ∈ T, ∃ k ∈ GlobalTheory.LFun.KGL w (n := r), q = z * t * k := by
  set Ωχ := Ω ∩ {y : GLw r w | y.val.charpoly = γ.val.charpoly} with hΩχ
  have hcpt : IsCompact Ωχ := hΩ.inter_right (isClosed_charpoly_eq E w r _)
  have hcyc : ∀ y ∈ Ωχ, ∃ e, IsUnit (krylov y.val e).det := fun y hy =>
    exists_cyclic _ (by rw [hy.2]; exact hs)
  obtain ⟨C, hC, hCy⟩ := exists_compact_krylov E w r Ωχ hcpt hcyc
  obtain ⟨f, hf⟩ := exists_cyclic γ.val hs
  have hfu : IsUnit (krylov γ.val f) := (Matrix.isUnit_iff_isUnit_det _).2 hf
  set Bf : GLw r w := hfu.unit with hBf
  set D : Set (GLw r w) := (fun c => Bf * c⁻¹) '' C with hD
  have hDc : IsCompact D := hC.image (continuous_const.mul continuous_inv)
  have hKo := isOpen_KGL E w r
  obtain ⟨T, hT⟩ := hDc.elim_finite_subcover (fun c : GLw r w => (fun x => c⁻¹ * x) ⁻¹' (GlobalTheory.LFun.KGL w (n := r) : Set (GLw r w)))
    (fun c => hKo.preimage (continuous_const.mul continuous_id)) (fun x _ => Set.mem_iUnion.2 ⟨x, by simp⟩)
  refine ⟨(T : Set (GLw r w)), T.finite_toSet, fun q hq => ?_⟩
  have hy : q⁻¹ * γ * q ∈ Ωχ := by
    refine ⟨hq, ?_⟩
    show ((q⁻¹ * γ * q : GLw r w) : Matrix (Fin r) (Fin r) (w.adicCompletion E)).charpoly = γ.val.charpoly
    have := Matrix.charpoly_units_conj (q⁻¹) γ.val
    simpa [Matrix.coe_units_inv] using this
  obtain ⟨e, c, hcC, hce⟩ := hCy _ hy
  have he : IsUnit (krylov (q⁻¹ * γ * q : GLw r w).val e).det := by
    rw [← hce, ← Matrix.isUnit_iff_isUnit_det]; exact c.isUnit
  have hconj := krylov_conj_eq _ _ e f (hy.2) he hf
  have h1 : c⁻¹ * (q⁻¹ * γ * q) * c = Bf⁻¹ * γ * Bf := by
    ext1
    rw [Units.val_mul (c⁻¹ * (q⁻¹ * γ * q)) c, Units.val_mul c⁻¹ (q⁻¹ * γ * q), Units.val_mul (Bf⁻¹ * γ) Bf,
      Units.val_mul Bf⁻¹ γ, Matrix.coe_units_inv c, Matrix.coe_units_inv Bf, hce, hBf, IsUnit.unit_spec]
    exact hconj
  have hxD : Bf * c⁻¹ ∈ D := ⟨c, hcC, rfl⟩
  obtain ⟨t, htT, ht⟩ := Set.mem_iUnion₂.1 (hT hxD)
  refine ⟨q * c * Bf⁻¹, ?_, t, htT, t⁻¹ * (Bf * c⁻¹), ht, by group⟩
  calc q * c * Bf⁻¹ * γ = q * c * (Bf⁻¹ * γ * Bf) * Bf⁻¹ := by group
    _ = q * c * (c⁻¹ * (q⁻¹ * γ * q) * c) * Bf⁻¹ := by rw [h1]
    _ = γ * (q * c * Bf⁻¹) := by group

theorem avg_ne_zero_exists {H : Type} [Group H] (u : H → ℂ) (h : avg u ≠ 0) : ∃ x, u x ≠ 0 := by
  by_contra hc
  push_neg at hc
  apply h
  simp [avg, hc]

theorem charpoly_blk_separable (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E)
    (m : GLw a w × GLw b w) (hs : (m.1.val.charpoly * m.2.val.charpoly).Separable) :
    (blk h w m 0 : GLw n w).val.charpoly.Separable := by
  have hM : IsUnit (Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
      (Matrix.fromBlocks m.1.val (m.1.val * (0 : Matrix (Fin a) (Fin b) (w.adicCompletion E))) 0 m.2.val)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_reindex_self, Matrix.mul_zero, Matrix.det_fromBlocks_zero₁₂]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp m.1.isUnit).mul ((Matrix.isUnit_iff_isUnit_det _).mp m.2.isUnit)
  have hval : ((blk h w m 0 : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
      Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
        (Matrix.fromBlocks m.1.val (m.1.val * (0 : Matrix (Fin a) (Fin b) (w.adicCompletion E))) 0 m.2.val) := by
    simp only [blk]
    rw [dif_pos hM]
    rfl
  rw [hval, Matrix.charpoly_reindex, Matrix.mul_zero, Matrix.charpoly_fromBlocks_zero₁₂]
  exact hs

theorem fin_doubleCosets : ∀ (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (f : GLw n w → ℂ), (∃ K' : Subgroup (GLw n w), IsOpen (K' : Set (GLw n w)) ∧ IsHecke K' f) → ∀ m : GLw a w × GLw b w, (m.1.val.charpoly * m.2.val.charpoly).Separable → ∀ hγ : blk h w m 0 ∈ GlobalTheory.LeviDesc.parP a n w, {d : DoubleCoset.Quotient (twCent (MonoidHom.id _) (⟨blk h w m 0, hγ⟩ : GlobalTheory.LeviDesc.parP a n w) : Set (GlobalTheory.LeviDesc.parP a n w)) (((GlobalTheory.LFun.KGL w (n := n)).subgroupOf (GlobalTheory.LeviDesc.parP a n w) : Subgroup _) : Set (GlobalTheory.LeviDesc.parP a n w)) | GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w (n := n)) f (((Quotient.out d)⁻¹ * ⟨blk h w m 0, hγ⟩ * Quotient.out d : GlobalTheory.LeviDesc.parP a n w) : GLw n w) ≠ 0}.Finite := by
  intro E _ _ n a b h w f hf m hs hγ
  obtain ⟨K', -, hsupp, -⟩ := hf
  set γ : GLw n w := blk h w m 0 with hγdef
  set P := GlobalTheory.LeviDesc.parP a n w
  set K := GlobalTheory.LFun.KGL w (n := n)
  set γP : P := ⟨γ, hγ⟩
  obtain ⟨T, hT, hTq⟩ := orbit_fin E w n γ (charpoly_blk_separable E n a b h w m hs) (tsupport f) hsupp
  have hcent : ∀ z : GLw n w, z * γ = γ * z → z ∈ P := fun z hz =>
    GlobalTheory.LeviDesc.twCent_blk_le_parP E n a b h w m hs (show z * γ = γ * MonoidHom.id _ z from hz)
  let Q : DoubleCoset.Quotient (twCent (MonoidHom.id _) γP : Set P) ((K.subgroupOf P : Subgroup P) : Set P) → GLw n w → Prop :=
    fun d t => t ∈ T ∧ ∃ z : GLw n w, z * γ = γ * z ∧ ∃ k ∈ K, ((Quotient.out d : P) : GLw n w) = z * t * k
  have hex : ∀ d ∈ {d : DoubleCoset.Quotient (twCent (MonoidHom.id _) γP : Set P) ((K.subgroupOf P : Subgroup P) : Set P) |
      GlobalTheory.LeviDesc.cavg K f (((Quotient.out d)⁻¹ * γP * Quotient.out d : P) : GLw n w) ≠ 0}, ∃ t, Q d t := by
    intro d hd
    obtain ⟨k, hk⟩ := avg_ne_zero_exists _ hd
    set p : GLw n w := ((Quotient.out d : P) : GLw n w)
    have hmem : (p * k)⁻¹ * γ * (p * k) ∈ tsupport f := by
      apply subset_tsupport
      have : (p * k)⁻¹ * γ * (p * k) = (k : GLw n w)⁻¹ * (((Quotient.out d)⁻¹ * γP * Quotient.out d : P) : GLw n w) * k := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, p, γP]; group
      rw [this]; exact hk
    obtain ⟨z, hz, t, ht, k₁, hk₁, hq⟩ := hTq _ hmem
    refine ⟨t, ht, z, hz, k₁ * (k : GLw n w)⁻¹, K.mul_mem hk₁ (K.inv_mem k.2), ?_⟩
    rw [← mul_assoc, ← hq, mul_inv_cancel_right]
  refine Set.Finite.of_injOn (f := fun d => if hd : ∃ t, Q d t then hd.choose else 1) (t := T) ?_ ?_ hT
  · intro d hd
    simp only [dif_pos (hex d hd)]
    exact (hex d hd).choose_spec.1
  · intro d₁ hd₁ d₂ hd₂ heq
    simp only [dif_pos (hex d₁ hd₁), dif_pos (hex d₂ hd₂)] at heq
    obtain ⟨-, z₁, hz₁, k₁, hk₁, hp₁⟩ := (hex d₁ hd₁).choose_spec
    obtain ⟨-, z₂, hz₂, k₂, hk₂, hp₂⟩ := (hex d₂ hd₂).choose_spec
    rw [heq] at hp₁
    set t := (hex d₂ hd₂).choose
    have hzP : z₂ * z₁⁻¹ ∈ P := hcent _ (by
      calc z₂ * z₁⁻¹ * γ = z₂ * (z₁⁻¹ * (γ * z₁)) * z₁⁻¹ := by group
        _ = z₂ * (z₁⁻¹ * (z₁ * γ)) * z₁⁻¹ := by rw [hz₁]
        _ = (z₂ * γ) * z₁⁻¹ := by group
        _ = (γ * z₂) * z₁⁻¹ := by rw [hz₂]
        _ = γ * (z₂ * z₁⁻¹) := by group)
    set hP : P := ⟨z₂ * z₁⁻¹, hzP⟩
    have hcP : hP ∈ twCent (MonoidHom.id _) γP := by
      show hP * γP = γP * MonoidHom.id _ hP
      apply Subtype.ext
      simp only [Subgroup.coe_mul, MonoidHom.id_apply, hP, γP]
      calc z₂ * z₁⁻¹ * γ = z₂ * (z₁⁻¹ * (γ * z₁)) * z₁⁻¹ := by group
        _ = z₂ * (z₁⁻¹ * (z₁ * γ)) * z₁⁻¹ := by rw [hz₁]
        _ = (z₂ * γ) * z₁⁻¹ := by group
        _ = (γ * z₂) * z₁⁻¹ := by rw [hz₂]
        _ = γ * (z₂ * z₁⁻¹) := by group
    set kP : P := (Quotient.out d₁)⁻¹ * hP⁻¹ * Quotient.out d₂
    have hkv : (kP : GLw n w) = k₁⁻¹ * k₂ := by
      simp only [kP, hP, Subgroup.coe_mul, Subgroup.coe_inv, hp₁, hp₂]; group
    have hkK : kP ∈ K.subgroupOf P := by
      rw [Subgroup.mem_subgroupOf, hkv]; exact K.mul_mem (K.inv_mem hk₁) hk₂
    rw [← DoubleCoset.out_eq' d₁, ← DoubleCoset.out_eq' d₂, DoubleCoset.eq]
    exact ⟨hP, hcP, kP, hkK, by simp only [kP]; group⟩

end GlobalTheory.LeviDesc.OrbFin
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.isLevel_blockLevels_splitPlace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b n : ℕ) (h : a + b = n) (w : Pl E)
    (N : Subgroup (GLw n w)) (μ : (w.adicCompletion E)ˣ →* ℂˣ), IsSplitAt w → IsOpen (N : Set (GLw n w)) →
    IsOpen {x | μ x = 1} →
    IsLevel (thL a w) (GlobalTheory.LFun.KGL w (n := a)) (lev₁ h w N μ) ∧ IsLevel (thL b w) (GlobalTheory.LFun.KGL w (n := b)) (lev₂ h w N μ) := by
  first | exact @GlobalTheory.BCT.CtLevel.isLevel_lev_split | exact GlobalTheory.BCT.CtLevel.isLevel_lev_split | (intros; apply GlobalTheory.BCT.CtLevel.isLevel_lev_split <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.orbitalIntegral_eq_closedSubgroup_conjAverage : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K P : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) → IsClosed (P : Set G) → (∀ g : G, ∃ p ∈ P, ∃ k ∈ K, g = p * k) → ∀ (δ : G) (hδ : δ ∈ P), twCent (MonoidHom.id G) δ ≤ P → ∀ f : G → ℂ, (∃ K' : Subgroup G, IsOpen (K' : Set G) ∧ IsHecke K' f) → twOrb (MonoidHom.id G) K δ f = twOrb (MonoidHom.id P) (K.subgroupOf P) ⟨δ, hδ⟩ (fun p => GlobalTheory.LeviDesc.cavg K f (p : G)) := by
  first | exact @GlobalTheory.IwRed.twOrb_sub | exact GlobalTheory.IwRed.twOrb_sub | (intros; apply GlobalTheory.IwRed.twOrb_sub <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.conjAverage_unipotent_locallyConstant_compactSupport : ∀ (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (f : GLw n w → ℂ), (∃ K' : Subgroup (GLw n w), IsOpen (K' : Set (GLw n w)) ∧ IsHecke K' f) → ∀ m : GLw a w × GLw b w, (∃ U : AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E)), IsOpen (U : Set (Matrix (Fin a) (Fin b) (w.adicCompletion E))) ∧ ∀ x, ∀ y ∈ U, GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w (n := n)) f (blk h w m (x + y)) = GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w (n := n)) f (blk h w m x)) ∧ HasCompactSupport (fun X => GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w (n := n)) f (blk h w m X)) := by
  first | exact @GlobalTheory.LeviDesc.UnipMean.cavg_blk_locConst_compactSupport | exact GlobalTheory.LeviDesc.UnipMean.cavg_blk_locConst_compactSupport | (intros; apply GlobalTheory.LeviDesc.UnipMean.cavg_blk_locConst_compactSupport <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_blockUpperParabolic_mul_integralGL : ∀ (E : Type) [Field E] [NumberField E] (a n : ℕ) (w : Pl E) (g : GLw n w), ∃ p ∈ GlobalTheory.LeviDesc.parP a n w, ∃ k ∈ GlobalTheory.LFun.KGL w (n := n), g = p * k := by
  first | exact @GlobalTheory.LeviDesc.exists_parabolic_mul_maximalCompact | exact GlobalTheory.LeviDesc.exists_parabolic_mul_maximalCompact | (intros; apply GlobalTheory.LeviDesc.exists_parabolic_mul_maximalCompact <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.unitaryHeckeOperatorVector_mem_levelFunctions : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → ∀ F ∈ vecM S lam K', hopM S lam K' f F ∈ vecM S lam K' := by
  first | exact @GlobalTheory.BCT.TrKer.HopStab.hopM_mem_vecM | exact GlobalTheory.BCT.TrKer.HopStab.hopM_mem_vecM | (intros; apply GlobalTheory.BCT.TrKer.HopStab.hopM_mem_vecM <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.TorCls
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.similitudeCentraliser_classNumber_finite_borel : ∀ (D : Type) [Ring D] [Algebra ℚ D] [FiniteDimensional ℚ D] (σ : D →+* Dᵐᵒᵖ) (β y : D) (p : ℕ) [Fact p.Prime], letI : TopologicalSpace (AfP p ⊗[ℚ] D) := moduleTopology (AfP p) (AfP p ⊗[ℚ] D); letI : TopologicalSpace (ℚ_[p] ⊗[ℚ] D) := moduleTopology ℚ_[p] (ℚ_[p] ⊗[ℚ] D); ∀ U : Subgroup (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)), (∃ O : Set (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)), IsOpen O ∧ 1 ∈ O ∧ ∀ z ∈ O, GlobalTheory.CentCls.TC D σ β y (AfP p) z.1 → GlobalTheory.CentCls.TC D σ β y ℚ_[p] z.2 → z ∈ U) → ∃ S : Finset (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)), ∀ z : ((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ), GlobalTheory.CentCls.TC D σ β y (AfP p) z.1 → GlobalTheory.CentCls.TC D σ β y ℚ_[p] z.2 → ∃ γ : Dˣ × ℚˣ, (γ.1 : D) * β * (σ (γ.1 : D)).unop = algebraMap ℚ D (γ.2 : ℚ) * β ∧ Commute (γ.1 : D) y ∧ ∃ s ∈ S, ∃ u ∈ U, z = GlobalTheory.TorCls.dg D p γ * s * u := by
  first | (exact @GlobalTheory.CentCls.Fin.classes_finite) | (exact GlobalTheory.CentCls.Fin.classes_finite) | (intros; apply GlobalTheory.CentCls.Fin.classes_finite  <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.eventually_integralCoords_scalarTensorInclusion : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (c : G.C), ∀ᶠ w : AwayP p in Filter.cofinite,
    IntC G w (inC G (w.1.adicCompletion ℚ) c) := by
  first | (exact @GlobalTheory.FinClsLoc.intC_inC_eventually) | (exact GlobalTheory.FinClsLoc.intC_inC_eventually) | (intros; apply GlobalTheory.FinClsLoc.intC_inC_eventually  <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.fockVacuum_real_restriction_gaussian_entire : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → ∀ f : WO S T → ℂ, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) LS LT f → ∃ Φ : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ, Differentiable ℂ Φ ∧ ∀ w : WO S T, w.map (finPart D) = 0 → f w = GlobalTheory.FockPos.gaussO θ frS frT w * Φ (GlobalTheory.FockPos.zCo θ frS frT w) := by
  first | exact @GlobalTheory.FockPos.vacuum_real_entire | exact GlobalTheory.FockPos.vacuum_real_entire | (intros; apply GlobalTheory.FockPos.vacuum_real_entire <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LeviFubini

theorem levH_fst_entry {E : Type} [Field E] [NumberField E] [IsCMField E] {a b n : ℕ} (h : a + b = n) (w : Pl E)
    (p : parB h w) (i j : Fin a) :
    ((levH h w p).1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j =
      ((p : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E))
        (GlobalTheory.SmGL.stdSum h (Sum.inl i)) (GlobalTheory.SmGL.stdSum h (Sum.inl j)) := rfl

theorem levH_snd_entry {E : Type} [Field E] [NumberField E] [IsCMField E] {a b n : ℕ} (h : a + b = n) (w : Pl E)
    (p : parB h w) (i j : Fin b) :
    ((levH h w p).2 : Matrix (Fin b) (Fin b) (w.adicCompletion E)) i j =
      ((p : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E))
        (GlobalTheory.SmGL.stdSum h (Sum.inr i)) (GlobalTheory.SmGL.stdSum h (Sum.inr j)) := rfl

theorem levH_mem_KGL_of_mem : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b n : ℕ) (h : a + b = n) (w : Pl E)
    (p : GlobalTheory.LeviFubini.parB h w), (p : GLw n w) ∈ GlobalTheory.LFun.KGL w (n := n) →
      (GlobalTheory.LeviFubini.levH h w p).1 ∈ GlobalTheory.LFun.KGL w (n := a) ∧ (GlobalTheory.LeviFubini.levH h w p).2 ∈ GlobalTheory.LFun.KGL w (n := b) := by
  intro E _ _ _ a b n h w p hp
  have hp' := GlobalTheory.AdelicU.mem_GLint_iff.1 hp
  have hinv1 : ((levH h w p).1)⁻¹ = (levH h w p⁻¹).1 := by rw [map_inv, Prod.fst_inv]
  have hinv2 : ((levH h w p).2)⁻¹ = (levH h w p⁻¹).2 := by rw [map_inv, Prod.snd_inv]
  refine ⟨GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩,
    GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩⟩
  · rw [levH_fst_entry]; exact hp'.1 _ _
  · rw [hinv1, levH_fst_entry]; exact hp'.2 _ _
  · rw [levH_snd_entry]; exact hp'.1 _ _
  · rw [hinv2, levH_snd_entry]; exact hp'.2 _ _

end GlobalTheory.LeviFubini
end
