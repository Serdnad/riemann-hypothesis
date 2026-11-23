module

public import Mathlib.Basic.Complex.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle022
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfD
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle007
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle878
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle006
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullFOfGenRel
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle041
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle876
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsHolFormConst
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfH
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle862
import Development.AbelianVarietyTheory.Definitions.Divisors.FderivFnCongr
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle001

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionLocal

lemma comp_pow_overScheme_grpObj {A T : Over (Sp ℂ)} [GrpObj A] (f : T ⟶ A) (g : A ⟶ A) :
    ∀ n : ℕ, f ≫ g ^ n = (f ≫ g) ^ n
  | 0 => by simp [MonObj.comp_one]
  | n + 1 => by rw [pow_succ, pow_succ, MonObj.comp_mul, comp_pow_overScheme_grpObj f g n]

theorem locally_eq_const_of_pow_eq_one : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (N : ℕ), 1 ≤ N →
    ∀ (T : Over (Sp ℂ)) (x : T ⟶ A), x ^ N = 1 →
    ∀ t : T.left, ∃ (U : T.left.Opens) (y : 𝟙_ (Over (Sp ℂ)) ⟶ A), t ∈ U ∧ U.ι ≫ x.left = U.ι ≫ T.hom ≫ y.left := by
  intro A _ hA N hN T x hx t
  have hunit : IsUnit ((N : ℕ) : Γ(Sp ℂ, ⊤)) := by
    have h : IsUnit ((N : ℂ)) := (Nat.cast_ne_zero.mpr (by omega)).isUnit
    simpa using h.map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  obtain ⟨-, hfin, het, -⟩ := abelianScheme_id_pow_finite_etale_surjective (Sp ℂ) A N hA hunit
  set f : A ⟶ A := (𝟙 A) ^ N with hf
  have hTu : (toUnit T).left = T.hom := by simpa using Over.w (toUnit T)
  have hxf : x.left ≫ f.left = T.hom ≫ η[A].left := by
    have h1 : x ≫ f = toUnit T ≫ η[A] := by
      rw [hf, comp_pow_overScheme_grpObj, Category.comp_id, hx]; rfl
    have h2 := congrArg (fun h => h.left) h1
    simpa [hTu] using h2
  haveI : IsFinite f.left := hfin
  haveI : Etale f.left := het
  haveI := hA.smooth
  have hη : η[A].left ≫ A.hom = 𝟙 _ := by simpa using Over.w η[A]
  have hfw : f.left ≫ A.hom = A.hom := Over.w f
  have hpt : T.hom t = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
  set a := x.left t with ha_def
  have hfa : f.left a = η[A].left (IsLocalRing.closedPoint ℂ) := by
    rw [ha_def, ← Scheme.Hom.comp_apply, hxf, Scheme.Hom.comp_apply, hpt]
  have he : IsClosed ({η[A].left (IsLocalRing.closedPoint ℂ)} : Set A.left) :=
    ((pointEquivClosedPoint A.hom) ⟨η[A].left, hη⟩).2
  haveI : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  have ha : IsClosed ({a} : Set A.left) := by
    rw [isClosed_singleton_iff_locallyOfFiniteType]
    have h1 : LocallyOfFiniteType (A.left.fromSpecResidueField (f.left a)) :=
      isClosed_singleton_iff_locallyOfFiniteType.mp (hfa ▸ he)
    have h2 : LocallyOfFiniteType (Spec.map (f.left.residueFieldMap a)) := by
      rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
      exact RingHom.FiniteType.of_finite (residueFieldMap_finite_of_locallyQuasiFinite f.left a)
    have h3 : LocallyOfFiniteType (A.left.fromSpecResidueField a ≫ f.left) := by
      rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]; infer_instance
    exact locallyOfFiniteType_of_comp _ f.left
  let y0 : Sp ℂ ⟶ A.left := pointOfClosedPoint A.hom a ha
  have hy0 : y0 ≫ A.hom = 𝟙 _ := pointOfClosedPoint_comp A.hom a ha
  let y : 𝟙_ (Over (Sp ℂ)) ⟶ A := Over.homMk y0 (by simpa using hy0)
  have hy0f : y0 ≫ f.left = η[A].left := by
    refine ext_of_apply_closedPoint_eq A.hom ?_ hη ?_
    · rw [Category.assoc, hfw, hy0]
    · show f.left (pointOfClosedPoint A.hom a ha (IsLocalRing.closedPoint ℂ)) = _
      exact (congrArg f.left (pointOfClosedPoint_apply A.hom a ha _)).trans hfa
  have hg : x.left ≫ f.left = (T.hom ≫ y0) ≫ f.left := by
    rw [hxf, Category.assoc, hy0f]
  have hψ := Spec.map_preimage (T.left.fromSpecResidueField t ≫ T.hom)
  set ψ := Spec.preimage (T.left.fromSpecResidueField t ≫ T.hom)
  have hr : (residueFieldIsoBase A.hom a ha).inv ≫ x.left.residueFieldMap t = ψ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ, SpecMap_residueFieldIsoBase_inv]
    erw [Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc]
    rw [Over.w x]
  have k : T.left.fromSpecResidueField t ≫ x.left = T.left.fromSpecResidueField t ≫ T.hom ≫ y0 := by
    rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc, ← hψ]
    simp only [y0, pointOfClosedPoint, ← Category.assoc, ← Spec.map_comp]
    rw [← hr, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  let g : T.left ⟶ pullback f.left f.left := pullback.lift x.left (T.hom ≫ y0) hg
  have kg : T.left.fromSpecResidueField t ≫ g =
      (T.left.fromSpecResidueField t ≫ x.left) ≫ pullback.diagonal f.left := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, pullback.lift_fst, pullback.diagonal_fst, Category.comp_id]
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.diagonal_snd, Category.comp_id, k]
  refine ⟨g ⁻¹ᵁ (pullback.diagonal f.left).opensRange, y, ?_, ?_⟩
  · show g t ∈ Set.range (pullback.diagonal f.left)
    have hk := congrArg (fun h => h (IsLocalRing.closedPoint (T.left.residueField t))) kg
    refine ⟨_, ((Scheme.Hom.comp_apply _ _ _).symm.trans hk.symm).trans
      ((Scheme.Hom.comp_apply _ _ _).trans ?_)⟩
    exact congrArg g (Scheme.fromSpecResidueField_apply t _)
  · set U := g ⁻¹ᵁ (pullback.diagonal f.left).opensRange
    have hle : Set.range (U.ι ≫ g) ⊆ Set.range (pullback.diagonal f.left) := by
      rintro _ ⟨u, rfl⟩
      rw [Scheme.Hom.comp_apply]
      exact u.2
    have hl := IsOpenImmersion.lift_fac (pullback.diagonal f.left) (U.ι ≫ g) hle
    have h1 := congrArg (· ≫ pullback.fst f.left f.left) hl
    have h2 := congrArg (· ≫ pullback.snd f.left f.left) hl
    simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id, g,
      pullback.lift_fst, pullback.lift_snd] at h1 h2
    show U.ι ≫ x.left = U.ι ≫ T.hom ≫ y0
    rw [← h1, h2]

end GlobalTheory.TorsionLocal
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates

namespace GlobalTheory.GramChartNear

open scoped Matrix ComplexConjugate

theorem gw_sub_jd_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (w : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (τ : X.Ψ) (a b : Fin r), (r : ℝ) * ‖w‖ ≤ 1 → ‖ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.Gw X w τ a b - ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.Jd X a b‖ ≤ 3 * ‖w‖ := by
  intro E _ _ _ r X w τ a b hrw
  set L : Matrix (Fin r) (Fin r) ℂ := mat (nmat X w) τ - 1 with hLdef
  have hL : ∀ i j, ‖L i j‖ ≤ ‖w‖ := fun i j => PoinPf.nmat_entry X w τ i j
  have hs : ∀ c : Fin r, ‖((sgn X.p0 (c : ℕ) : ℝ) : ℂ)‖ = 1 := fun c => by
    rw [Complex.norm_real, Real.norm_eq_abs, PoinPf.abs_sgn]
  have h1 : mat (nmat X w) τ = 1 + L := by rw [hLdef]; abel
  have key : PoinPf.Gw X w τ - PoinPf.Jd X =
      Lᵀ * PoinPf.Jd X + PoinPf.Jd X * L.map (starRingEnd ℂ) + Lᵀ * PoinPf.Jd X * L.map (starRingEnd ℂ) := by
    rw [PoinPf.Gw, h1, Matrix.transpose_add, Matrix.transpose_one,
      Matrix.map_add _ (map_add (starRingEnd ℂ)), Matrix.map_one _ (map_zero _) (map_one _)]
    noncomm_ring
  rw [← Matrix.sub_apply, key, Matrix.add_apply, Matrix.add_apply, PoinPf.Jd, Matrix.mul_diagonal,
    Matrix.diagonal_mul, Matrix.mul_apply]
  simp_rw [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.map_apply]
  have t1 : ‖L b a * ((sgn X.p0 (b : ℕ) : ℝ) : ℂ)‖ ≤ ‖w‖ := by
    rw [norm_mul, hs, mul_one]; exact hL b a
  have t2 : ‖((sgn X.p0 (a : ℕ) : ℝ) : ℂ) * (starRingEnd ℂ) (L a b)‖ ≤ ‖w‖ := by
    rw [norm_mul, hs, one_mul, Complex.norm_conj]; exact hL a b
  have t3 : ‖∑ c, L c a * ((sgn X.p0 (c : ℕ) : ℝ) : ℂ) * (starRingEnd ℂ) (L c b)‖ ≤ ‖w‖ := by
    calc _ ≤ ∑ c : Fin r, ‖L c a * ((sgn X.p0 (c : ℕ) : ℝ) : ℂ) * (starRingEnd ℂ) (L c b)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _c : Fin r, ‖w‖ * ‖w‖ := by
          refine Finset.sum_le_sum fun c _ => ?_
          rw [norm_mul, norm_mul, hs, mul_one, Complex.norm_conj]
          exact mul_le_mul (hL c a) (hL c b) (norm_nonneg _) (norm_nonneg _)
      _ = ‖w‖ * ((r : ℝ) * ‖w‖) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      _ ≤ ‖w‖ * 1 := mul_le_mul_of_nonneg_left hrw (norm_nonneg _)
      _ = ‖w‖ := mul_one _
  calc _ ≤ _ := norm_add₃_le
    _ ≤ ‖w‖ + ‖w‖ + ‖w‖ := add_le_add (add_le_add t1 t2) t3
    _ = 3 * ‖w‖ := by ring

end GlobalTheory.GramChartNear
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SemicharShift

def imForm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) :
    (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun y w => (hermForm Hm y w).im)
    (fun a b w => by simp [hermForm, add_dotProduct])
    (fun c a w => by simp [hermForm, smul_dotProduct, Complex.smul_im])
    (fun y a b => by simp [hermForm, Matrix.mulVec_add, dotProduct_add])
    (fun c y a => by
      simp [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, Complex.smul_im])

theorem imForm_apply {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (y w : Fin g → ℂ) :
    imForm Hm y w = (hermForm Hm y w).im := rfl

theorem imForm_surjective {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) :
    Function.Surjective (imForm Hm) := by
  have hinj : Function.Injective (imForm Hm) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    by_contra hz0
    have h1 : imForm Hm z (Complex.I • z) = 0 := by rw [hz]; rfl
    have h2 : imForm Hm z (Complex.I • z) = -(hermForm Hm z z).re := by
      rw [imForm_apply]
      simp [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, Matrix.mulVec_neg,
        dotProduct_neg, smul_eq_mul, Complex.mul_im]
    have := hpos z hz0
    linarith
  have hdim : Module.finrank ℝ (Fin g → ℂ) = Module.finrank ℝ ((Fin g → ℂ) →ₗ[ℝ] ℝ) :=
    (Subspace.dual_finrank_eq).symm
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj

end GlobalTheory.SemicharShift

namespace GlobalTheory.SemicharShift

theorem exists_linear_of_char {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (hsp : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) (ρ : Λ → ℂ) (hn : ∀ l, ‖ρ l‖ = 1)
    (hmul : ∀ l m, ρ (l + m) = ρ l * ρ m) :
    ∃ φ : (Fin g → ℂ) →ₗ[ℝ] ℝ, ∀ l : Λ,
      ρ l = Complex.exp (2 * Real.pi * Complex.I * (φ (l : Fin g → ℂ) : ℂ)) := by
  haveI : IsZLattice ℝ Λ := ⟨hsp⟩
  let b := Module.Free.chooseBasis ℤ Λ
  let B := b.ofZLatticeBasis ℝ Λ
  let φ : (Fin g → ℂ) →ₗ[ℝ] ℝ := B.constr ℝ (fun j => Complex.arg (ρ (b j)) / (2 * Real.pi))
  refine ⟨φ, ?_⟩
  have hφb : ∀ j, φ (b j : Fin g → ℂ) = Complex.arg (ρ (b j)) / (2 * Real.pi) := by
    intro j
    have : (b j : Fin g → ℂ) = B j := by simp [B, Module.Basis.ofZLatticeBasis_apply]
    rw [this]
    exact B.constr_basis ℝ _ j
  have hne : ∀ l, ρ l ≠ 0 := fun l h => by simpa [h] using hn l
  have h0 : ρ 0 = 1 := by
    have := hmul 0 0
    rw [add_zero] at this
    have h := hne 0
    field_simp at this
    exact this.symm
  let S : AddSubgroup Λ :=
    { carrier := {l | ρ l = Complex.exp (2 * Real.pi * Complex.I * (φ (l : Fin g → ℂ) : ℂ))}
      add_mem' := by
        intro l m hl hm
        simp only [Set.mem_setOf_eq] at hl hm ⊢
        rw [hmul, hl, hm, ← Complex.exp_add]
        congr 1
        simp only [Submodule.coe_add, map_add (f := _)]
        push_cast; ring
      zero_mem' := by
        simp only [Set.mem_setOf_eq, ZeroMemClass.coe_zero, map_zero]
        simp [h0]
      neg_mem' := by
        intro l hl
        simp only [Set.mem_setOf_eq] at hl ⊢
        have h1 : ρ (-l) * ρ l = 1 := by rw [← hmul, neg_add_cancel, h0]
        have h2 : ρ (-l) = (ρ l)⁻¹ := eq_inv_of_mul_eq_one_left h1
        rw [h2, hl, ← Complex.exp_neg]
        congr 1
        simp only [Submodule.coe_neg, map_neg]
        push_cast; ring }
  have htop : (⊤ : Submodule ℤ Λ) ≤ S.toIntSubmodule := by
    rw [← b.span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    show ρ (b j) = Complex.exp (2 * Real.pi * Complex.I * (φ (b j : Fin g → ℂ) : ℂ))
    rw [hφb]
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have : 2 * (Real.pi : ℂ) * Complex.I * ((Complex.arg (ρ (b j)) / (2 * Real.pi) : ℝ) : ℂ)
        = (Complex.arg (ρ (b j)) : ℂ) * Complex.I := by
      push_cast; field_simp
    rw [this]
    have h := Complex.norm_mul_exp_arg_mul_I (ρ (b j))
    rw [hn, Complex.ofReal_one, _root_.one_mul] at h
    exact h.symm
  intro l
  exact htop (Submodule.mem_top : l ∈ ⊤)

end GlobalTheory.SemicharShift

namespace GlobalTheory.SemicharShift

theorem exists_shift_of_semichar : ∀ (g : ℕ) (Λ Λ₁ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ) (χ₁ : Λ₁ → ℂ)
    (h : Λ ≤ Λ₁), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → Hm.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → (∀ l, ‖χ l‖ = 1) → (∀ l, ‖χ₁ l‖ = 1) →
    (∀ l m : Λ, χ (l + m) = χ l * χ m * Complex.exp (Real.pi * Complex.I * (hermForm Hm l m).im)) →
    (∀ l m : Λ₁, χ₁ (l + m) = χ₁ l * χ₁ m * Complex.exp (Real.pi * Complex.I * (hermForm Hm l m).im)) →
    ∃ a : Fin g → ℂ, ∀ l : Λ,
      χ l = χ₁ (Submodule.inclusion h l) * Complex.exp (2 * Real.pi * Complex.I * (hermForm Hm a l).im) := by
  intro g Λ Λ₁ Hm χ χ₁ h hdisc hsp _hH hpos hχ hχ₁ hc hc₁
  haveI := hdisc
  have hne : ∀ l, χ₁ l ≠ 0 := fun l e => by simpa [e] using hχ₁ l
  have hne' : ∀ l, χ l ≠ 0 := fun l e => by simpa [e] using hχ l
  let ρ : Λ → ℂ := fun l => χ l / χ₁ (Submodule.inclusion h l)
  have hn : ∀ l, ‖ρ l‖ = 1 := fun l => by simp [ρ, norm_div, hχ, hχ₁]
  have hmul : ∀ l m, ρ (l + m) = ρ l * ρ m := by
    intro l m
    simp only [ρ]
    rw [map_add (f := _), hc, hc₁]
    simp only [Submodule.coe_inclusion]
    have e1 := hne (Submodule.inclusion h l)
    have e2 := hne (Submodule.inclusion h m)
    have e3 : Complex.exp (Real.pi * Complex.I * (hermForm Hm l m).im) ≠ 0 := Complex.exp_ne_zero _
    field_simp
  obtain ⟨φ, hφ⟩ := exists_linear_of_char Λ hsp ρ hn hmul
  obtain ⟨a, ha⟩ := imForm_surjective Hm hpos φ
  refine ⟨a, fun l => ?_⟩
  have h1 := hφ l
  rw [← ha, imForm_apply] at h1
  rw [← h1]
  simp only [ρ]
  field_simp [hne (Submodule.inclusion h l)]

end GlobalTheory.SemicharShift
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PureLift
open scoped CategoryTheory.Obj

namespace GlobalTheory.TorsionReduction

theorem eq_of_residue_eq : ∀ (S : Type) [CommRing S] (P : Out.PolAV (Sp S)) (T : Type) [CommRing T] [IsLocalRing T] (b : S →+* T) (n : ℕ), IsUnit (n : T) → ∀ x y : Over.mk (spMap b) ⟶ P.A, x ^ n = 1 → y ^ n = 1 → spMap (IsLocalRing.residue T) ≫ x.left = spMap (IsLocalRing.residue T) ≫ y.left → x = y := by
  intro S _ P T _ _ b n hn x y hx hy hr
  letI := P.isAb.comm
  haveI : Smooth P.A.hom := P.isAb.smooth
  let j : Sp T ⟶ Sp S := spMap b
  let G : Over (Sp T) := (Over.pullback j).obj P.A
  letI : (Over.pullback j).Monoidal := (Over.instBraidedPullback (f := j)).toMonoidal
  letI : GrpObj G := Functor.grpObjObj (F := Over.pullback j)
  have hn' : IsUnit (n : Γ(Sp T, ⊤)) := by
    simpa using hn.map (Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom
  let m : G.left ⟶ G.left := (Out.mulA G n).left
  have hw : m ≫ G.hom = G.hom := Over.w (Out.mulA G n)
  have h₁ : FormallyUnramified m := formallyUnramified_mulA (Sp T) G n hn'
  have h₂ : LocallyOfFiniteType (m ≫ G.hom) := by
    rw [hw]; dsimp [G]; infer_instance
  have h₃ : LocallyOfFiniteType m := locallyOfFiniteType_of_comp _ G.hom
  have e : (Over.pullback j).map (Out.mulA P.A n) = Out.mulA G n :=
    (map_pow (Over.pullback j).homMonoidHom (𝟙 P.A) n).trans
      (congrArg (· ^ n) (CategoryTheory.Functor.map_id (Over.pullback j) P.A))
  have mf : m ≫ pullback.fst P.A.hom j = pullback.fst P.A.hom j ≫ (Out.mulA P.A n).left := by
    change (Out.mulA G n).left ≫ _ = _
    rw [← e]; exact pullback.lift_fst _ _ _
  have kx : ∀ z : Over.mk (spMap b) ⟶ P.A, z ^ n = 1 → z.left ≫ (Out.mulA P.A n).left = j ≫ (η[P.A]).left := by
    intro z hz
    rw [← Over.comp_left, Out.mulA, MonObj.comp_pow, Category.comp_id, hz, Hom.one_def]
    simp [j]
  let x' : Sp T ⟶ G.left := pullback.lift x.left (𝟙 _) (by simpa [j] using Over.w x)
  let y' : Sp T ⟶ G.left := pullback.lift y.left (𝟙 _) (by simpa [j] using Over.w y)
  have x₁ : x' ≫ pullback.fst P.A.hom j = x.left := pullback.lift_fst _ _ _
  have y₁ : y' ≫ pullback.fst P.A.hom j = y.left := pullback.lift_fst _ _ _
  have x₂ : x' ≫ pullback.snd P.A.hom j = 𝟙 _ := pullback.lift_snd _ _ _
  have y₂ : y' ≫ pullback.snd P.A.hom j = 𝟙 _ := pullback.lift_snd _ _ _
  have hab : x' ≫ m = y' ≫ m := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, mf, pullback.lift_fst_assoc, pullback.lift_fst_assoc, kx x hx, kx y hy]
    · rw [Category.assoc, Category.assoc]
      change x' ≫ m ≫ G.hom = y' ≫ m ≫ G.hom
      rw [hw]
      exact (pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm
  have hc : spMap (IsLocalRing.residue T) ≫ x' = spMap (IsLocalRing.residue T) ≫ y' := by
    apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) x₁).trans
        (hr.trans ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) y₁)).symm))
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (x₂.trans y₂.symm)).trans (Category.assoc _ _ _).symm)
  have hopen := isOpenImmersion_equalizer_ι_of_unramified m hab
  have hsub := range_subset_range_equalizer_ι _ hc
  have hcl : IsLocalRing.closedPoint T ∈ Set.range (equalizer.ι x' y') :=
    hsub ⟨IsLocalRing.closedPoint _, IsLocalRing.comap_closedPoint (IsLocalRing.residue T)⟩
  have hall : Set.range (equalizer.ι x' y') = Set.univ :=
    Set.eq_univ_of_forall fun p =>
      (IsLocalRing.specializes_closedPoint p).mem_open (equalizer.ι x' y').isOpenEmbedding.isOpen_range hcl
  have hxy : x' = y' := eq_of_range_equalizer_ι_eq_univ m hab hall
  apply Over.OverMorphism.ext
  exact x₁.symm.trans ((congrArg (· ≫ pullback.fst P.A.hom j) hxy).trans y₁)

end GlobalTheory.TorsionReduction
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelianScheme_isSeparated_of_affine_base : ∀ {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → A.left.IsSeparated := by
  first | exact @GlobalTheory.abelianScheme_left_isSeparated_of_affine | exact GlobalTheory.abelianScheme_left_isSeparated_of_affine | (intros; apply GlobalTheory.abelianScheme_left_isSeparated_of_affine <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PullDegWhole

theorem exists_isPullDeg_top : ∀ {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {i : R →+* R'} {D : DegPre R} {D' : DegPre R'} (p : IsPullDeg i D D'), Nonempty (PsiOn D ⊤) → ∃ p' : IsPullDeg i D D', p'.W = ⊤ ∧ p'.e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) = p.e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) ∧ ∀ x, p'.xe x = p.xe x := by
  intro R R' _ _ _ _ i D D' p ⟨ψ⟩
  obtain ⟨g, hg⟩ : ∃ g : (TK R').left ⟶ (⊤ : (Spec (CommRingCat.of R)).Opens).toScheme,
      g ≫ (⊤ : (Spec (CommRingCat.of R)).Opens).ι = jK R' ≫ specOf i :=
    ⟨IsOpenImmersion.lift _ _ (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      trivial), IsOpenImmersion.lift_fac _ _ _⟩
  refine ⟨{ p with W := ⊤, psiW := ψ, g := g, g_comm := hg, psi_pr := fun x => ?_ }, rfl, rfl, fun _ => rfl⟩
  obtain ⟨b, hb, hc⟩ := p.psi_pr x
  refine ⟨b, hb, corr_of_val D.P.isLB fun y J hJ => (val_corr hJ hc _).trans (by
    refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
    exact GlobalTheory.ArcSpecialise.psiOn_agree p.psiW ψ _ _ _
      (by rw [Category.assoc, Category.assoc]; exact congrArg _ (p.g_comm.trans hg.symm)) hJ)⟩

end GlobalTheory.PullDegWhole
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.Et
open scoped TensorProduct DirectSum
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.AbFieldDim

theorem exists_smoothOfRelativeDimension : ∀ (k : Type) [Field k] (A : Over (Spec (CommRingCat.of k))) [GrpObj A],
    IsAbelianScheme A → ∃ g : ℕ, SmoothOfRelativeDimension g A.hom := by
  intro k _ A _ hA
  exact GlobalTheory.AbelianDim.exists_relDim k A hA

end GlobalTheory.AbFieldDim
end
