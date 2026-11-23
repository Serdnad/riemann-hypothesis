module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle463
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle511
public import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle499
public import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.NumberField.CMField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle501
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle500
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.GrpTangentPt

variable {S : Scheme.{0}} {R' : Type} [CommRing R'] (x : Sp R' ⟶ S)

def sqZeroMapPt {M N : Type} [AddCommGroup M] [Module R' M] [Module R'ᵐᵒᵖ M] [IsCentralScalar R' M]
    [AddCommGroup N] [Module R' N] [Module R'ᵐᵒᵖ N] [IsCentralScalar R' N] (l : M →ₗ[R'] N) :
    Over.mk (spMap (algebraMap R' (TrivSqZeroExt R' N)) ≫ x) ⟶
      Over.mk (spMap (algebraMap R' (TrivSqZeroExt R' M)) ≫ x) :=
  Over.homMk (spMap (TrivSqZeroExt.map l).toRingHom) (by
    change Spec.map _ ≫ Spec.map _ ≫ x = Spec.map _ ≫ x
    rw [← Category.assoc, ← Spec.map_comp]
    congr 2
    exact CommRingCat.hom_ext (TrivSqZeroExt.map l).comp_algebraMap)

lemma sqZeroMapPt_comp {M N P : Type} [AddCommGroup M] [Module R' M] [Module R'ᵐᵒᵖ M] [IsCentralScalar R' M]
    [AddCommGroup N] [Module R' N] [Module R'ᵐᵒᵖ N] [IsCentralScalar R' N]
    [AddCommGroup P] [Module R' P] [Module R'ᵐᵒᵖ P] [IsCentralScalar R' P]
    (l : M →ₗ[R'] N) (l' : N →ₗ[R'] P) :
    sqZeroMapPt x l' ≫ sqZeroMapPt x l = sqZeroMapPt x (l' ∘ₗ l) := by
  ext1
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun z => ?_)
  ext <;> simp

abbrev epsScalePt (c : R') : epsPtR x ⟶ epsPtR x := sqZeroMapPt x (c • (LinearMap.id : R' →ₗ[R'] R'))

lemma epsScalePt_left (c : R') : (epsScalePt x c).left = spMap (epsScaleR c) := rfl

lemma sqZeroMapPt_comp_eq {M : Type} [AddCommGroup M] [Module R' M] [Module R'ᵐᵒᵖ M]
    [IsCentralScalar R' M] (l : R' →ₗ[R'] M) (l' : M →ₗ[R'] R') :
    sqZeroMapPt x l' ≫ sqZeroMapPt x l = epsScalePt x (l' (l 1)) := by
  rw [sqZeroMapPt_comp]
  congr 1
  refine LinearMap.ext_ring ?_
  simp

lemma epsScalePt_one : epsScalePt x (1 : R') = 𝟙 _ := by
  ext1
  change Spec.map _ = 𝟙 _
  rw [← Spec.map_id]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun z => ?_)
  ext <;> simp

variable {G : Over S} [GrpObj G]

lemma epsScalePt_zero_comp {w : epsPtR x ⟶ G}
    (hw : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ w.left = (1 : Over.mk x ⟶ G).left) :
    epsScalePt x 0 ≫ w = 1 := by
  let π : epsPtR x ⟶ Over.mk x := Over.homMk (spMap (algebraMap R' (DualNumber R'))) rfl
  have e : (1 : epsPtR x ⟶ G) = π ≫ (1 : Over.mk x ⟶ G) := (comp_one π).symm
  rw [e]
  ext1
  rw [Over.comp_left, Over.comp_left, ← hw, ← Category.assoc]
  congr 1
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun z => ?_)
  ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem epsScalePt_add_comp (a b : R') {w : epsPtR x ⟶ G}
    (hw : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ w.left = (1 : Over.mk x ⟶ G).left) :
    epsScalePt x (a + b) ≫ w = (epsScalePt x a ≫ w) * (epsScalePt x b ≫ w) := by
  let i₁ := LinearMap.inl R' R' R'
  let i₂ := LinearMap.inr R' R' R'
  have key : sqZeroMapPt x (i₁ + i₂) ≫ w = (sqZeroMapPt x i₁ ≫ w) * (sqZeroMapPt x i₂ ≫ w) := by
    ext1
    refine GlobalTheory.TangentCrit.hom_ext_of_ker_inf
      (CommRingCat.ofHom (TrivSqZeroExt.map (LinearMap.fst R' R' R')).toRingHom)
      (CommRingCat.ofHom (TrivSqZeroExt.map (LinearMap.snd R' R' R')).toRingHom) ?_ ?_ ?_ ?_
    · refine (PrimeSpectrum.isHomeomorph_comap (TrivSqZeroExt.map (LinearMap.fst R' R' R')).toRingHom
        (fun z => ⟨1, one_pos, TrivSqZeroExt.map i₁ z, by ext <;> simp [i₁]⟩) fun d hd => ?_).surjective
      have h : d.fst = 0 := by simpa using congrArg TrivSqZeroExt.fst hd
      exact ⟨2, by ext1 <;> simp [pow_two, h]⟩
    · intro d h₁ h₂
      have h₃ : d.fst = 0 := by simpa using congrArg TrivSqZeroExt.fst h₁
      have h₄ : d.snd.1 = 0 := by simpa using congrArg TrivSqZeroExt.snd h₁
      have h₅ : d.snd.2 = 0 := by simpa using congrArg TrivSqZeroExt.snd h₂
      exact TrivSqZeroExt.ext h₃ (Prod.ext h₄ h₅)
    · refine congrArg Over.Hom.left
        (?_ : sqZeroMapPt x (LinearMap.fst R' R' R') ≫ _ = sqZeroMapPt x (LinearMap.fst R' R' R') ≫ _)
      rw [comp_mul]
      simp only [← Category.assoc, sqZeroMapPt_comp_eq]
      simp [i₁, i₂, epsScalePt_zero_comp x hw, epsScalePt_one]
    · refine congrArg Over.Hom.left
        (?_ : sqZeroMapPt x (LinearMap.snd R' R' R') ≫ _ = sqZeroMapPt x (LinearMap.snd R' R' R') ≫ _)
      rw [comp_mul]
      simp only [← Category.assoc, sqZeroMapPt_comp_eq]
      simp [i₁, i₂, epsScalePt_zero_comp x hw, epsScalePt_one]
  have := congrArg (sqZeroMapPt x (a • LinearMap.fst R' R' R' + b • LinearMap.snd R' R' R') ≫ ·) key
  simp only [comp_mul, ← Category.assoc, sqZeroMapPt_comp_eq] at this
  simpa [i₁, i₂] using this

theorem tanadd : ∀ {S : Scheme.{0}} (G : Over S) [GrpObj G] {R' : Type} [CommRing R'] (x : Sp R' ⟶ S)
    (w : epsPtR x ⟶ G), spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ w.left = (1 : Over.mk x ⟶ G).left →
    ∀ (a b : R') (wa wb : epsPtR x ⟶ G), wa.left = spMap (epsScaleR a) ≫ w.left →
      wb.left = spMap (epsScaleR b) ≫ w.left → (wa * wb).left = spMap (epsScaleR (a + b)) ≫ w.left := by
  intro S G _ R' _ x w hw a b wa wb ha hb
  have ea : wa = epsScalePt x a ≫ w := Over.OverMorphism.ext ha
  have eb : wb = epsScalePt x b ≫ w := Over.OverMorphism.ext hb
  rw [ea, eb, ← epsScalePt_add_comp x a b hw]
  rfl

end GlobalTheory.GrpTangentPt
end
end

section

open NumberField
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.HTOrderTrace

theorem trace_tmul_padic {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [Module.Free ℤ R] [Module.Finite ℤ R]
    (z : ℤ_[p]) (a : R) :
    Algebra.trace ℤ_[p] (ℤ_[p] ⊗[ℤ] R) (z ⊗ₜ a) = (Algebra.trace ℤ R a : ℤ_[p]) * z := by
  have h1 : (z ⊗ₜ a : ℤ_[p] ⊗[ℤ] R) = z • (1 ⊗ₜ a) := by simp [TensorProduct.smul_tmul']
  have h2 : Algebra.lmul ℤ_[p] (ℤ_[p] ⊗[ℤ] R) (1 ⊗ₜ a) =
      (Algebra.lmul ℤ R a).baseChange ℤ_[p] := by
    ext c
    simp
  rw [h1, map_smul, Algebra.trace_apply, h2, LinearMap.trace_baseChange, smul_eq_mul, mul_comm]
  rfl

theorem trace_form_padic_eq_zero : ∀ (E : Type) [Field E] [NumberField E] (p : ℕ) [Fact p.Prime] (u : ℤ_[p] ⊗[ℤ] 𝓞 E),
    (∀ w, Algebra.trace ℤ_[p] (ℤ_[p] ⊗[ℤ] 𝓞 E) (u * w) = 0) → u = 0 := by
  intro E _ _ p _ u hu
  classical
  let b0 := RingOfIntegers.basis E
  let b1 := b0.baseChange ℤ_[p]
  have h1 : Algebra.discr ℤ_[p] b1 = (NumberField.discr E : ℤ_[p]) := by
    rw [NumberField.discr, Algebra.discr_def, Algebra.discr_def]
    rw [show ((Algebra.traceMatrix ℤ (RingOfIntegers.basis E)).det : ℤ_[p]) =
      Int.castRingHom ℤ_[p] (Algebra.traceMatrix ℤ (RingOfIntegers.basis E)).det from rfl,
      RingHom.map_det]
    congr 1
    ext i j
    simp [b1, b0, Algebra.traceForm_apply, trace_tmul_padic]
  have h0 : (NumberField.discr E : ℤ_[p]) ≠ 0 := Int.cast_ne_zero.2 (discr_ne_zero E)
  have hnd : (Algebra.traceForm ℤ_[p] (ℤ_[p] ⊗[ℤ] 𝓞 E)).Nondegenerate := by
    rw [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b1]
    have : LinearMap.BilinForm.toMatrix b1 (Algebra.traceForm ℤ_[p] (ℤ_[p] ⊗[ℤ] 𝓞 E)) =
        Algebra.traceMatrix ℤ_[p] b1 := by
      ext i j; simp [Algebra.traceMatrix_apply]
    rw [this, ← Algebra.discr_def, h1]; exact h0
  exact hnd.1 u (fun w => by simpa [Algebra.traceForm_apply] using hu w)

theorem ringHom_padic_eq_algebraMap : ∀ (p : ℕ) [Fact p.Prime] (B : Type) [Ring B] [Algebra ℤ_[p] B] [Module.Free ℤ_[p] B]
    (f : ℤ_[p] →+* B), f = algebraMap ℤ_[p] B := by
  intro p _ B _ _ _ f
  ext c
  rw [← sub_eq_zero]
  set b := Module.Free.chooseBasis ℤ_[p] B
  have hdiv : ∀ n : ℕ, ∃ v : B, f c - algebraMap ℤ_[p] B c = (p : ℤ_[p]) ^ n • v := by
    intro n
    obtain ⟨μ, hμ⟩ := Ideal.mem_span_singleton.1 (PadicInt.appr_spec n c)
    have hc : c = (c.appr n : ℤ_[p]) + (p : ℤ_[p]) ^ n * μ := by rw [← hμ]; ring
    refine ⟨f μ - algebraMap ℤ_[p] B μ, ?_⟩
    conv_lhs => rw [hc]
    rw [smul_sub, Algebra.smul_def, Algebra.smul_def, map_add (f := _), map_add (f := _), map_mul, map_mul, map_pow, map_pow,
      map_natCast, map_natCast, map_natCast, map_natCast]
    noncomm_ring
  apply b.repr.injective
  ext i
  simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
  by_contra hne
  obtain ⟨v, hv⟩ := hdiv ((b.repr (f c - algebraMap ℤ_[p] B c) i).valuation + 1)
  have hmem : b.repr (f c - algebraMap ℤ_[p] B c) i ∈
      Ideal.span {(p : ℤ_[p]) ^ ((b.repr (f c - algebraMap ℤ_[p] B c) i).valuation + 1)} := by
    rw [Ideal.mem_span_singleton]
    conv_rhs => rw [hv]
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact dvd_mul_right _ _
  have hne' : b.repr (f c - algebraMap ℤ_[p] B c) i ≠ 0 := by
    intro h
    apply hne
    rw [h]
  have := (PadicInt.mem_span_pow_iff_le_valuation _ hne' _).1 hmem
  omega

theorem matrix_basis_repr {ι R A : Type} [CommRing R] [AddCommGroup A] [Module R A] (m : ℕ) (b : Module.Basis ι R A)
    (M : Matrix (Fin m) (Fin m) A) (i j : Fin m) (k : ι) :
    (b.matrix (Fin m) (Fin m)).repr M (i, j, k) = b.repr (M i j) k := by
  simp only [Module.Basis.matrix, Module.Basis.map_repr, Module.Basis.repr_reindex_apply, LinearEquiv.trans_apply]
  rfl

theorem trace_mulLeft_matrix_eq : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Module.Free R A] [Module.Finite R A]
    (m : ℕ) (Z : Matrix (Fin m) (Fin m) A),
    LinearMap.trace R (Matrix (Fin m) (Fin m) A) (LinearMap.mulLeft R Z) = (m : R) * Algebra.trace R A Z.trace := by
  intro R A _ _ _ _ _ m Z
  classical
  let b := Module.Free.chooseBasis R A

  rw [LinearMap.trace_eq_matrix_trace R (b.matrix (Fin m) (Fin m)), Matrix.trace, Matrix.trace, map_sum,
  Finset.mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type, Algebra.trace_eq_matrix_trace b, Matrix.trace]
  have key : ∀ j : Fin m, ∑ k, ((LinearMap.toMatrix (b.matrix (Fin m) (Fin m)) (b.matrix (Fin m) (Fin m)))
      (LinearMap.mulLeft R Z)).diag (i, j, k) = ∑ k, ((Algebra.leftMulMatrix b) (Z.diag i)).diag k := by
    intro j
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [LinearMap.toMatrix_apply, matrix_basis_repr, Algebra.leftMulMatrix_eq_repr_mul, Matrix.mul_apply, Matrix.single_apply]
  rw [Finset.sum_congr rfl fun j _ => key j, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem trace_mulLeft_baseChange_eq_zero : ∀ (O : Type) [Ring O] [Module.Free ℤ O] [Module.Finite ℤ O] (R : Type) [CommRing R] (x : O),
    (∀ y, LinearMap.trace ℤ O (LinearMap.mulLeft ℤ (x * y)) = 0) →
    ∀ Y : R ⊗[ℤ] O, LinearMap.trace R (R ⊗[ℤ] O) (LinearMap.mulLeft R ((1 ⊗ₜ x) * Y)) = 0 := by
  intro O _ _ _ R _ x hx Y
  have hb : ∀ z : O, LinearMap.mulLeft R ((1 : R) ⊗ₜ[ℤ] z) = (LinearMap.mulLeft ℤ z).baseChange R := by
    intro z; ext c w; simp
  induction Y using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb' =>
    rw [mul_add, show LinearMap.mulLeft R ((1 ⊗ₜ x) * a + (1 ⊗ₜ x) * b) =
      LinearMap.mulLeft R ((1 ⊗ₜ x) * a) + LinearMap.mulLeft R ((1 ⊗ₜ x) * b) from
      map_add (LinearMap.mul R (R ⊗[ℤ] O)) _ _, map_add, ha, hb', add_zero]
  | tmul r y =>
    have h1 : ((1 : R) ⊗ₜ[ℤ] x) * (r ⊗ₜ y) = r • ((1 : R) ⊗ₜ[ℤ] (x * y)) := by
      simp [TensorProduct.smul_tmul']
    rw [h1, show LinearMap.mulLeft R (r • ((1 : R) ⊗ₜ[ℤ] (x * y))) =
      r • LinearMap.mulLeft R ((1 : R) ⊗ₜ[ℤ] (x * y)) from
      map_smul (LinearMap.mul R (R ⊗[ℤ] O)) _ _, map_smul, hb, LinearMap.trace_baseChange, hx, map_zero, smul_zero]

theorem inj_tmul (p : ℕ) [Fact p.Prime] (O : Type) [Ring O] [Module.Free ℤ O] (x : O)
    (h : (1 : ℤ_[p]) ⊗ₜ[ℤ] x = 0) : x = 0 := by
  have hinj := Module.Flat.rTensor_preserves_injective_linearMap (M := O)
    (Algebra.linearMap ℤ ℤ_[p]) (RingHom.injective_int (algebraMap ℤ ℤ_[p]))
  have h1 : (Algebra.linearMap ℤ ℤ_[p]).rTensor O ((1 : ℤ) ⊗ₜ x) = 0 := by simpa using h
  have h2 := hinj (h1.trans (map_zero _).symm)
  simpa using congrArg (TensorProduct.lid ℤ O) h2

theorem trace_order_nondeg : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (x : D.O),
    (∀ y : D.O, LinearMap.trace ℤ D.O (LinearMap.mulLeft ℤ (x * y)) = 0) → x = 0 := by
  intro p _ D x hx
  haveI := D.freeO
  haveI := D.finO
  obtain ⟨φ⟩ := D.splitP
  set A' := ℤ_[p] ⊗[ℤ] 𝓞 D.F
  let Φ : (ℤ_[p] ⊗[ℤ] D.O) ≃+* Matrix (Fin D.m) (Fin D.m) A' :=
    (Algebra.TensorProduct.comm ℤ ℤ_[p] D.O).toRingEquiv.trans
      (φ.toRingEquiv.trans (Algebra.TensorProduct.comm ℤ (𝓞 D.F) ℤ_[p]).toRingEquiv.mapMatrix)
  have hψ : Φ.toRingHom.comp (algebraMap ℤ_[p] (ℤ_[p] ⊗[ℤ] D.O)) =
      algebraMap ℤ_[p] (Matrix (Fin D.m) (Fin D.m) A') := ringHom_padic_eq_algebraMap p _ _
  have hΦs : ∀ (c : ℤ_[p]) (X : ℤ_[p] ⊗[ℤ] D.O), Φ (c • X) = c • Φ X := by
    intro c X
    rw [Algebra.smul_def, map_mul, Algebra.smul_def]
    congr 1
    exact congrArg (fun f => f c) hψ
  let e : (ℤ_[p] ⊗[ℤ] D.O) ≃ₗ[ℤ_[p]] Matrix (Fin D.m) (Fin D.m) A' :=
    { Φ.toAddEquiv with map_smul' := hΦs }
  have hconj : ∀ W : ℤ_[p] ⊗[ℤ] D.O, LinearMap.mulLeft ℤ_[p] (Φ W) = e.conj (LinearMap.mulLeft ℤ_[p] W) := by
    intro W
    ext V
    simp [LinearEquiv.conj_apply, e]
  set Z := Φ (1 ⊗ₜ x)
  have hZ : ∀ Y, Algebra.trace ℤ_[p] A' (Z * Y).trace = 0 := by
    intro Y
    have h1 := trace_mulLeft_baseChange_eq_zero D.O ℤ_[p] x hx (Φ.symm Y)
    rw [← LinearMap.trace_conj' _ e, ← hconj, map_mul, RingEquiv.apply_symm_apply, trace_mulLeft_matrix_eq] at h1
    have hm : (D.m : ℤ_[p]) ≠ 0 := Nat.cast_ne_zero.2 D.m_pos.ne'
    exact (mul_eq_zero.1 h1).resolve_left hm
  have hZ0 : Z = 0 := by
    ext i j
    apply trace_form_padic_eq_zero D.F p
    intro a
    have := hZ (Matrix.single j i a)
    rwa [Matrix.trace_mul_single, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op] at this
  have h1 : (1 : ℤ_[p]) ⊗ₜ[ℤ] x = 0 := by
    rw [← map_eq_zero_iff Φ Φ.injective]; exact hZ0
  exact inj_tmul p D.O x h1

end GlobalTheory.HTOrderTrace
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR Opposite

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechDR

theorem form_pow_smul_eq_zero_of_res_basicOpen {R' : Type} [CommRing R'] {X' : Scheme.{0}}
    (s' : X' ⟶ Sp R') (W : X'.affineOpens) (f : Γ(X', W.1)) (hU : IsAffineOpen (X'.basicOpen f))
    (hle : (⟨X'.basicOpen f, hU⟩ : X'.affineOpens) ≤ W) (ω : Ω[(OAff s').obj (op W)⁄R'])
    (h : p1 (OAff s') (homOfLE hle).op ω = 0) :
    ∃ n : ℕ, ((show (OAff s').obj (op W) from f) ^ n) • ω = 0 := by
  apply _root_.GlobalTheory.CechDR.form_pow_smul_eq_zero_of_basicOpen <;> assumption

theorem form_eq_zero_of_basis_cover : ∀ {R' : Type} [CommRing R'] {X' : Scheme.{0}} (s' : X' ⟶ Sp R') {C' : Type} [Category.{0} C'], ∀ (G : C' ⥤ AffOp X'), (∀ T : AffOp X', ∃ (n : ℕ) (b : Fin n → (OAff s').obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp X') (u : T ⟶ S), IsUnit (mp (OAff s') u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (T : AffOp X') (ω : Ω[(OAff s').obj T⁄R']), (∀ t (u : T ⟶ G.obj t), p1 (OAff s') u ω = 0) → ω = 0) := by
  intro R' _ X' s' C' _ G hcov T ω hω
  obtain ⟨n, b, hspan, hb⟩ := hcov T
  let A := (OAff s').obj T
  let J : Ideal A := (Submodule.span A {ω}).annihilator
  have hpow : ∀ i, ∃ m : ℕ, b i ^ m ∈ J := by
    intro i
    have hU : IsAffineOpen (X'.basicOpen (show Γ(X', T.unop.1) from b i)) :=
      T.unop.2.basicOpen _
    have hle : (⟨X'.basicOpen (show Γ(X', T.unop.1) from b i), hU⟩ : X'.affineOpens) ≤ T.unop :=
      X'.basicOpen_le _
    have hunit : IsUnit (mp (OAff s') (homOfLE hle).op (b i)) :=
      X'.toRingedSpace.isUnit_res_basicOpen (show Γ(X', T.unop.1) from b i)
    obtain ⟨t, v, w, hvw⟩ := hb i _ (homOfLE hle).op hunit
    have h0 : p1 (OAff s') (homOfLE hle).op ω = 0 := by
      rw [← hvw, oneFormsMapOfFunctorMorphism_comp, hω t v, map_zero]
    obtain ⟨m, hm⟩ := form_pow_smul_eq_zero_of_res_basicOpen s' T.unop _ hU hle ω h0
    exact ⟨m, (Submodule.mem_annihilator_span_singleton ω _).2 hm⟩
  choose m hm using hpow
  have hJ : J = ⊤ := by
    rw [eq_top_iff, ← Ideal.span_pow_eq_top _ hspan (∑ i, m i), Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    have hmi : m i ≤ ∑ j, m j :=
      Finset.single_le_sum (f := m) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    change b i ^ (∑ j, m j) ∈ J
    rw [← Nat.add_sub_cancel' hmi, pow_add]
    exact J.mul_mem_right _ (hm i)
  have h1 : (1 : A) ∈ J := hJ ▸ Submodule.mem_top
  simpa using (Submodule.mem_annihilator_span_singleton _ _).1 h1

end GlobalTheory.CechDR
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Obs

theorem sq_abelian_and_affine_H1 : ∀ (R : Type) [CommRing R], (∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → IsAbelianScheme (A ⊗ A) ∧ SmoothOfRelativeDimension (g + g) (A ⊗ A).hom) ∧ ∀ (X : Scheme.{0}) [IsAffine X] (s : X ⟶ Sp R) (c : HO1 s), c = 0 := by
  intro R _
  refine ⟨fun A _ g hA hg ↦ ⟨ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA, ?_⟩, fun X _ s c ↦ ?_⟩
  · haveI := hg
    haveI : SmoothOfRelativeDimension g (Limits.pullback.fst A.hom A.hom) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
        (IsPullback.of_hasPullback _ _).flip hg
    exact inferInstanceAs (SmoothOfRelativeDimension (g + g) (Limits.pullback.fst A.hom A.hom ≫ A.hom))
  · let T₀ : AffOp X := Opposite.op ⟨⊤, isAffineOpen_top X⟩
    have h : Limits.IsInitial T₀ := Limits.IsInitial.ofUniqueHom
      (fun U ↦ (homOfLE (show U.unop ≤ ⟨⊤, isAffineOpen_top X⟩ from le_top (a := U.unop.1))).op) fun _ _ ↦ rfl
    exact H1.eq_zero_of_isInitial _ h c

end GlobalTheory.Obs
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem quasiIso_hypercohomology_bijective' : A1 := by
  intro R _ K L f _ F n
  haveI : (res R F).IsKInjective := (GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R F).1
  exact GlobalTheory.T.hypercohomologyPullback_bijective_of_quasiIso R f (res R F) n

end GlobalTheory.EtC
end

section

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace

theorem _root_.GlobalTheory.T.periodClass_injective_of_rich_charts : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F), K.Rich → ∀ per per' : Λ →+ Hol F.V, K.perCl per = K.perCl per' → per = per' := by
  first | exact @GlobalTheory.AnPer.Charts.perCl_injective | exact GlobalTheory.AnPer.Charts.perCl_injective | (intros; apply GlobalTheory.AnPer.Charts.perCl_injective <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal

theorem _root_.GlobalTheory.T.norm_heckeLFunction_le_zeta_three_halves_pow : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (Λ : ℂ → ℂ) (S : ℂ), IsUnitary χ → IsHeckeL χ Λ → 3 / 2 ≤ S.re → ‖Λ S‖ ≤ ‖riemannZeta (3 / 2)‖ ^ Module.finrank ℚ E := by
  first | exact @GlobalTheory.HeckeLBound.norm_heckeL_le | exact GlobalTheory.HeckeLBound.norm_heckeL_le | (intros; apply GlobalTheory.HeckeLBound.norm_heckeL_le <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal

theorem _root_.GlobalTheory.T.idelicRingClassLattice_one_eq_order : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → lattice c 1 = (orderC c : Set E) := by
  first | exact @GlobalTheory.CMVal.HatCap.lattice_one | exact GlobalTheory.CMVal.HatCap.lattice_one | (intros; apply GlobalTheory.CMVal.HatCap.lattice_one <;> assumption)
end
