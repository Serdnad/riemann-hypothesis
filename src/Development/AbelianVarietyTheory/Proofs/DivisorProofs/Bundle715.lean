module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle590
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle676
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle394
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle592
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle332
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle341
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle709
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplementaryModuleEqTopFormsOfFiniteCover
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle679
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle680
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
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle001
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003

@[expose] public section

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.RelLin

theorem main : ∀ (N : ℕ) [NeZero N] (R : (Fin 2 → ZMod N) → (Fin 2 → ZMod N) → Prop),
    (∀ x, ∃ y, R x y) → (∀ x y x' y', R x y → R x' y' → R (x - x') (y - y')) →
    (∀ x y, R x y → (x = 0 ↔ y = 0)) → ∃ A : GL (Fin 2) (ZMod N), ∀ x, R x (vmul x A) := by
  intro N _ R h1 h2 h3
  choose f hf using h1
  have huniq : ∀ x y y', R x y → R x y' → y = y' := by
    intro x y y' hy hy'
    have h := h3 _ _ (h2 x y x y' hy hy')
    exact sub_eq_zero.mp (h.mp (sub_self x))
  have hsub : ∀ x x', f (x - x') = f x - f x' :=
    fun x x' => huniq _ _ _ (hf (x - x')) (h2 _ _ _ _ (hf x) (hf x'))
  let g : (Fin 2 → ZMod N) →+ (Fin 2 → ZMod N) := AddMonoidHom.ofMapSub f hsub
  let L : (Fin 2 → ZMod N) →ₗ[ZMod N] (Fin 2 → ZMod N) := g.toZModLinearMap N
  have hL : ∀ x, L x = f x := fun x => rfl
  have hinj : Function.Injective f := by
    intro x x' hxx
    have : f (x - x') = 0 := by rw [hsub, hxx, sub_self]
    exact sub_eq_zero.mp ((h3 _ _ (hf (x - x'))).mpr this)
  let M : Matrix (Fin 2) (Fin 2) (ZMod N) := LinearMap.toMatrixRight' L
  have hM : ∀ x, x ᵥ* M = f x := by
    intro x
    rw [← hL, ← Matrix.toLinearMapRight'_apply]
    simp [M]
  have hU : IsUnit M := by
    rw [← Matrix.vecMul_surjective_iff_isUnit]
    have hsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hinj
    intro y
    obtain ⟨x, rfl⟩ := hsurj y
    exact ⟨x, hM x⟩
  refine ⟨hU.unit, fun x => ?_⟩
  have : vmul x hU.unit = f x := by
    simp [vmul, hM]
  rw [this]
  exact hf x

end GlobalTheory.RelLin
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam

theorem isAlgebraic_of_isIntegral_natCast_mul (n : ℕ) (hn : n ≠ 0) (z : ℂ)
    (h : IsIntegral ℤ ((n : ℂ) * z)) : IsAlgebraic ℚ z := by
  have h1 : IsIntegral ℚ ((n : ℂ) * z) := h.tower_top
  have h2 : IsIntegral ℚ (algebraMap ℚ ℂ ((n : ℚ)⁻¹)) := isIntegral_algebraMap
  have h3 := h2.mul h1
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have : algebraMap ℚ ℂ ((n : ℚ)⁻¹) * ((n : ℂ) * z) = z := by
    rw [map_inv₀, map_natCast, ← mul_assoc, inv_mul_cancel₀ hn', one_mul]
  rw [this] at h3
  exact h3.isAlgebraic

theorem qAll_isAlgebraic_torsion : ∀ (N : ℕ) [NeZero N] (x : Fin 2 → ZMod N),
    QAll (IsAlgebraic ℚ) N (wp N x) ∧ QAll (IsAlgebraic ℚ) N (wpd N x) ∧
      (x ≠ 0 → QAll (IsAlgebraic ℚ) N (wB N x)) := by
  intro N _ x
  have hN : N ≠ 0 := NeZero.ne N
  have hx : N • x = 0 := by
    funext i
    simp [nsmul_eq_mul]
  have hc := fun k => GlobalTheory.T.isIntegral_weierstrassTorsion_qCoefficients N N x k (Nat.pos_of_ne_zero hN) hx
  refine ⟨⟨cP N x, GlobalTheory.T.hasQExpansion_normalizedWeierstrassPTorsion N x, fun k => ?_⟩, ⟨cD N x, GlobalTheory.T.hasQExpansion_normalizedDerivWeierstrassPTorsion N x, fun k => ?_⟩,
    fun h0 => ⟨cB N x, GlobalTheory.T.weierstrass_division_value_q_expansion N x h0, fun k => ?_⟩⟩
  · refine isAlgebraic_of_isIntegral_natCast_mul (12 * N ^ 2) (by positivity) _ ?_
    have := (hc k).2.2.1
    push_cast
    exact this
  · refine isAlgebraic_of_isIntegral_natCast_mul (N ^ 3) (by positivity) _ ?_
    have := (hc k).2.1
    push_cast
    exact this
  · refine isAlgebraic_of_isIntegral_natCast_mul (N ^ 2) (by positivity) _ ?_
    have := (hc k).1
    push_cast
    exact this

end GlobalTheory.WpFam
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem hc_congr_deg {F : Type} [Field F] (a b b' : ℕ) (α : GL (Fin a) F → ℂ)
    (β : (m : ℕ) → GL (Fin m) F → ℂ) (n : ℕ) (h : b = b') :
    hc a b α (β b) n = hc a b' α (β b') n := by
  subst h; rfl

theorem deg_map_mul (L : List (ℕ × ℕ)) (c : ℕ) :
    deg (L.map fun p => (p.1, p.2 * c)) = deg L := by
  unfold deg
  rw [List.map_map]
  rfl

theorem J_gal : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (t : F ≃+* F) (j : ℕ),
    (∀ x, t x = x ^ (ringChar F ^ j)) → ∀ (L : List (ℕ × ℕ)) (n : ℕ) (x : GL (Fin n) F),
    J θ L n (gal (t : F →+* F) n x) = J θ (L.map fun p => (p.1, p.2 * ringChar F ^ j)) n x := by
  intro F _ _ θ t j ht L
  induction L with
  | nil => intro n x; rfl
  | cons p L ih =>
    intro n x
    rw [List.map_cons, J_cons, J_cons, GlobalTheory.T.harishChandraInductionGL_fieldAutomorphism F t]
    have h1 : (fun y => cusp θ p.1 p.2 (gal (t : F →+* F) p.1 y)) = cusp θ p.1 (p.2 * ringChar F ^ j) := by
      funext y; exact GlobalTheory.T.cuspidalCharacterGLFiniteField_frobenius_pow F θ t j ht p.1 p.2 y
    have h2 : (fun y => J θ L (deg L) (gal (t : F →+* F) (deg L) y)) =
        J θ (L.map fun p => (p.1, p.2 * ringChar F ^ j)) (deg L) := by
      funext y; exact ih (deg L) y
    rw [h1, h2]
    exact congrFun (hc_congr_deg p.1 (deg L) _ _ (J θ (L.map fun p => (p.1, p.2 * ringChar F ^ j))) n
      (deg_map_mul L _).symm) x

end GlobalTheory.Shin
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh GlobalTheory.AbTan
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbTan.Transl

variable {R : Type} [CommRing R]

abbrev ovT (R : Type) [CommRing R] (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] : Over (Sp R) :=
  Over.mk (spMap ((TrivSqZeroExt.inlHom B M).comp (algebraMap R B)))

abbrev ovB (R : Type) [CommRing R] (B : Type) [CommRing B] [Algebra R B] : Over (Sp R) :=
  Over.mk (spMap (algebraMap R B))

theorem one_left (A : Over (Sp R)) [GrpObj A] (T : Over (Sp R)) : (1 : T ⟶ A).left = T.hom ≫ η[A].left := rfl

theorem inl_w (A : Over (Sp R)) {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (P : Sp B ⟶ A.left) (hP : P ≫ A.hom = spMap (algebraMap R B)) :
    (spMap (TrivSqZeroExt.inlHom B M) ≫ P) ≫ A.hom = (ovT R B M).hom := by
  rw [Category.assoc, hP]
  exact (GlobalTheory.Cris.spMap_comp _ _).symm

theorem fst_w (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] :
    spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ (ovT R B M).hom = (ovB R B).hom := by
  show _ ≫ spMap _ = spMap _
  rw [← GlobalTheory.Cris.spMap_comp]
  congr 1 <;> ext r <;> simp

theorem fst_inl (B M : Type) [CommRing B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] :
    spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ spMap (TrivSqZeroExt.inlHom B M) = 𝟙 (Sp B) := by
  rw [← GlobalTheory.Cris.spMap_comp, ← GlobalTheory.Cris.spMap_id]
  congr 1 <;> ext r <;> simp

def eFst (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] : ovB R B ⟶ ovT R B M :=
  Over.homMk (spMap (TrivSqZeroExt.fstHom B B M).toRingHom) (fst_w B M)


open Classical in
def tau (A : Over (Sp R)) [GrpObj A] (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (P : Sp B ⟶ A.left) (z : Sp (TrivSqZeroExt B M) ⟶ A.left) :
    Sp (TrivSqZeroExt B M) ⟶ A.left :=
  if h : P ≫ A.hom = spMap (algebraMap R B) ∧ z ≫ A.hom = (ovT R B M).hom then
    ((Over.homMk (U := ovT R B M) (V := A) (spMap (TrivSqZeroExt.inlHom B M) ≫ P) (inl_w A P h.1) *
      Over.homMk (U := ovT R B M) (V := A) z h.2 : ovT R B M ⟶ A)).left
  else z

theorem tau_eq (A : Over (Sp R)) [GrpObj A] {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (P : Sp B ⟶ A.left) (hP : P ≫ A.hom = spMap (algebraMap R B))
    (z : Sp (TrivSqZeroExt B M) ⟶ A.left) (hz : z ≫ A.hom = (ovT R B M).hom) :
    tau A B M P z = ((Over.homMk (U := ovT R B M) (V := A) (spMap (TrivSqZeroExt.inlHom B M) ≫ P) (inl_w A P hP) *
      Over.homMk (U := ovT R B M) (V := A) z hz : ovT R B M ⟶ A)).left := by
  rw [tau, dite_eq_left ⟨hP, hz⟩]

theorem red_iff (A : Over (Sp R)) [GrpObj A] {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (g : ovT R B M ⟶ A) (P : Sp B ⟶ A.left)
    (hP : P ≫ A.hom = spMap (algebraMap R B)) :
    spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ g.left = P ↔
      eFst B M ≫ g = Over.homMk (U := ovB R B) (V := A) P hP := by
  constructor
  · intro h; ext; simpa [eFst] using h
  · intro h; have := congrArg CommaMorphism.left h; simpa [eFst] using this

theorem unit_eq (A : Over (Sp R)) [GrpObj A] (B : Type) [CommRing B] [Algebra R B]
    (h : unitPt A B ≫ A.hom = spMap (algebraMap R B)) :
    Over.homMk (U := ovB R B) (V := A) (unitPt A B) h = 1 := by
  ext; rw [one_left]; rfl

end GlobalTheory.AbTan.Transl

namespace GlobalTheory.AbTan.Transl

variable {R : Type} [CommRing R]

theorem unit_w (A : Over (Sp R)) [GrpObj A] (B : Type) [CommRing B] [Algebra R B] :
    unitPt A B ≫ A.hom = spMap (algebraMap R B) := by
  rw [unitPt, Category.assoc, Over.w η[A]]
  exact Category.comp_id _

theorem bijOn_tau (A : Over (Sp R)) [GrpObj A] {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M]
    [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (P : Sp B ⟶ A.left)
    (hP : P ≫ A.hom = spMap (algebraMap R B)) :
    Set.BijOn (tau A B M P) {z | Lifts A.hom (unitPt A B) z} {z | Lifts A.hom P z} := by
  set Q : ovT R B M ⟶ A := Over.homMk (spMap (TrivSqZeroExt.inlHom B M) ≫ P) (inl_w A P hP) with hQ
  have hU := unit_w A B
  have keyQ : eFst B M ≫ Q = Over.homMk (U := ovB R B) (V := A) P hP := by
    ext
    simp only [eFst, Q, Over.comp_left, Over.homMk_left]
    rw [← Category.assoc, fst_inl]
    exact Category.id_comp _
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨h1, h2⟩ := hz
    show Lifts A.hom P (tau A B M P z)
    rw [tau_eq A P hP z h1]
    refine ⟨Over.w _, ?_⟩
    rw [red_iff A _ P hP, MonObj.comp_mul, keyQ,
      (red_iff A (Over.homMk (U := ovT R B M) (V := A) z h1) (unitPt A B) hU).1 h2, unit_eq, _root_.mul_one]
  · intro z1 hz1 z2 hz2 he
    obtain ⟨h11, -⟩ := hz1
    obtain ⟨h21, -⟩ := hz2
    rw [tau_eq A P hP z1 h11, tau_eq A P hP z2 h21] at he
    have := mul_left_cancel (Over.OverMorphism.ext he)
    exact congrArg CommaMorphism.left this
  · intro z' hz'
    obtain ⟨h1, h2⟩ := hz'
    set Z : ovT R B M ⟶ A := Q⁻¹ * Over.homMk (U := ovT R B M) (V := A) z' h1 with hZ
    refine ⟨Z.left, ⟨Over.w Z, ?_⟩, ?_⟩
    · rw [red_iff A Z (unitPt A B) hU, unit_eq, hZ, MonObj.comp_mul, GrpObj.comp_inv, keyQ,
        (red_iff A (Over.homMk (U := ovT R B M) (V := A) z' h1) P hP).1 h2, inv_mul_cancel]
    · show tau A B M P Z.left = z'
      rw [tau_eq A P hP Z.left (Over.w Z)]
      have e : Over.homMk (U := ovT R B M) (V := A) Z.left (Over.w Z) = Z := by ext; rfl
      rw [← hQ, e, hZ, mul_inv_cancel_left]
      rfl

theorem tau_natural (A : Over (Sp R)) [GrpObj A] {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M]
    [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] {B' M' : Type} [CommRing B'] [Algebra R B']
    [AddCommGroup M'] [Module B' M'] [Module B'ᵐᵒᵖ M'] [IsCentralScalar B' M'] (α : B →ₐ[R] B') (f : M → M')
    (β : TrivSqZeroExt B M →+* TrivSqZeroExt B' M') (hβ : IsSum β α f) (P : Sp B ⟶ A.left)
    (hP : P ≫ A.hom = spMap (algebraMap R B)) (z : Sp (TrivSqZeroExt B M) ⟶ A.left)
    (hz : Lifts A.hom (unitPt A B) z) :
    Lifts A.hom (unitPt A B') (spMap β ≫ z) ∧
      tau A B' M' (spMap (α : B →+* B') ≫ P) (spMap β ≫ z) = spMap β ≫ tau A B M P z := by
  obtain ⟨hz1, hz2⟩ := hz
  have hβinl : β.comp (TrivSqZeroExt.inlHom B M) = (TrivSqZeroExt.inlHom B' M').comp (α : B →+* B') :=
    RingHom.ext fun b => hβ.1 b
  have hβT : β.comp ((TrivSqZeroExt.inlHom B M).comp (algebraMap R B)) =
      (TrivSqZeroExt.inlHom B' M').comp (algebraMap R B') := by
    rw [← RingHom.comp_assoc, hβinl, RingHom.comp_assoc, AlgHom.comp_algebraMap]
  have hβfst : (TrivSqZeroExt.fstHom B' B' M').toRingHom.comp β =
      (α : B →+* B').comp (TrivSqZeroExt.fstHom B B M).toRingHom := by
    ext x
    conv_lhs => rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq x]
    simp [map_add (f := _), hβ.1, hβ.2]
  let b : ovT R B' M' ⟶ ovT R B M := Over.homMk (spMap β) (by
    show spMap β ≫ spMap _ = spMap _
    rw [← GlobalTheory.Cris.spMap_comp, hβT])
  set Z : ovT R B M ⟶ A := Over.homMk z hz1 with hZ
  have hz' : (spMap β ≫ z) ≫ A.hom = (ovT R B' M').hom := Over.w (b ≫ Z)
  have hP' : (spMap (α : B →+* B') ≫ P) ≫ A.hom = spMap (algebraMap R B') := by
    rw [Category.assoc, hP, ← GlobalTheory.Cris.spMap_comp, AlgHom.comp_algebraMap]
  refine ⟨⟨hz', ?_⟩, ?_⟩
  · rw [← Category.assoc, ← GlobalTheory.Cris.spMap_comp, hβfst, GlobalTheory.Cris.spMap_comp, Category.assoc, hz2, unitPt,
      unitPt, ← Category.assoc, ← GlobalTheory.Cris.spMap_comp, AlgHom.comp_algebraMap]
  · rw [tau_eq A _ hP' _ hz', tau_eq A P hP z hz1]
    have e1 : b ≫ (Over.homMk (U := ovT R B M) (V := A) (spMap (TrivSqZeroExt.inlHom B M) ≫ P) (inl_w A P hP)) =
        Over.homMk (U := ovT R B' M') (V := A) (spMap (TrivSqZeroExt.inlHom B' M') ≫ spMap (α : B →+* B') ≫ P)
          (inl_w A _ hP') := by
      ext
      simp only [b, Over.comp_left, Over.homMk_left]
      rw [← Category.assoc, ← Category.assoc, ← GlobalTheory.Cris.spMap_comp, ← GlobalTheory.Cris.spMap_comp, hβinl]
    have e2 : b ≫ Z = Over.homMk (U := ovT R B' M') (V := A) (spMap β ≫ z) hz' := by ext; rfl
    show _ = (b ≫ (_ * Z)).left
    rw [MonObj.comp_mul, e1, e2]

end GlobalTheory.AbTan.Transl


open GlobalTheory.AbTan.Transl in
theorem GlobalTheory.AbTan.exists_translation : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], ∃ τ : ∀ (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M], (Sp B ⟶ A.left) → (Sp (TrivSqZeroExt B M) ⟶ A.left) → (Sp (TrivSqZeroExt B M) ⟶ A.left), (∀ (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (P : Sp B ⟶ A.left), P ≫ A.hom = spMap (algebraMap R B) → Set.BijOn (τ B M P) {z | Lifts A.hom (unitPt A B) z} {z | Lifts A.hom P z}) ∧ ∀ (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (B' M' : Type) [CommRing B'] [Algebra R B'] [AddCommGroup M'] [Module B' M'] [Module B'ᵐᵒᵖ M'] [IsCentralScalar B' M'] (α : B →ₐ[R] B') (f : M → M') (β : TrivSqZeroExt B M →+* TrivSqZeroExt B' M'), IsSum β α f → ∀ (P : Sp B ⟶ A.left), P ≫ A.hom = spMap (algebraMap R B) → ∀ z, Lifts A.hom (unitPt A B) z → Lifts A.hom (unitPt A B') (spMap β ≫ z) ∧ τ B' M' (spMap (α : B →+* B') ≫ P) (spMap β ≫ z) = spMap β ≫ τ B M P z := by
  intro R _ A _
  refine ⟨fun B M => tau A B M, ?_, ?_⟩
  · intro B M _ _ _ _ _ _ P hP
    exact bijOn_tau A P hP
  · intro B M _ _ _ _ _ _ B' M' _ _ _ _ _ _ α f β hβ P hP z hz
    exact tau_natural A α f β hβ P hP z hz
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.exists_simplicialCochain_representing_class_acyclicLevels :
    ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc) (n : ℕ),
      (∀ k m : ℕ, 0 < m → k + m = n →
        ∀ y : H R (disc.obj (E.obj (op (SimplexCategory.mk k)))) F m, y = 0) →
      ∀ x : H R E F n, ∃ s : (free R).obj (E.obj (op (SimplexCategory.mk n))) ⟶ F,
        GlobalTheory.EtC.cobd (R := R) s = 0 ∧ GlobalTheory.EtC.IsCls (R := R) s x := by
  intro R _ F E n hyp x
  obtain ⟨z, rfl, hv⟩ := GlobalTheory.EtC.LeraySurj.reduce F E n hyp x n le_rfl
  obtain ⟨-, hneg, hmono, ⟨w, hex⟩, -, -⟩ :=
    GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_basic_properties R F
  have hcl : z.1.v (-(n : ℤ)) 0 (by omega) ≫ (res R F).d 0 1 = 0 := by
    have h := Cochain.congr_v (Cocycle.δ_eq_zero z ((n : ℤ) + 1)) (-(n : ℤ)) 1 (by omega)
    rw [δ_v (n : ℤ) ((n : ℤ) + 1) rfl _ _ _ _ 0 (-(n : ℤ) + 1) (by omega) rfl,
      hv (-(n : ℤ) + 1) _ _ (by omega)] at h
    simpa using h
  obtain ⟨u, hu⟩ := hex.lift' ((chainsXIso R E n).inv ≫ z.1.v (-(n : ℤ)) 0 (by omega))
    (by change _ ≫ (res R F).d 0 1 = 0; rw [Category.assoc, hcl, Limits.comp_zero])
  change u ≫ resι R F = _ at hu
  have hz : z.1.v (-(n : ℤ)) 0 (by omega) = (chainsXIso R E n).hom ≫ u ≫ resι R F := by
    rw [hu, Iso.hom_inv_id_assoc]
  have hcobd : GlobalTheory.EtC.cobd (R := R) u =
      (chainsXIso R E (n + 1)).inv ≫ ((chains R).obj E).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) ≫
        (chainsXIso R E n).hom ≫ u := by
    rw [GlobalTheory.EtC.LeraySurj.chains_d_eq]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Preadditive.sum_comp, Preadditive.zsmul_comp]
    rfl
  refine ⟨u, ?_, z, rfl, ?_⟩
  · rw [hcobd]
    have h := Cochain.congr_v (Cocycle.δ_eq_zero z ((n : ℤ) + 1)) (-((n + 1 : ℕ) : ℤ)) 0 (by omega)
    rw [δ_v (n : ℤ) ((n : ℤ) + 1) rfl _ _ _ _ (-1) (-(n : ℤ)) (by omega) (by omega), hz,
      (hneg (-1) (by omega)).eq_of_tgt (z.1.v _ (-1) _) 0] at h
    simp only [Limits.zero_comp, zero_add, Cochain.zero_v] at h
    have h' := (smul_eq_zero_iff_eq _).1 h
    have h'' : (((chains R).obj E).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) ≫ (chainsXIso R E n).hom ≫ u) ≫
        resι R F = 0 ≫ resι R F := by
      simpa [Category.assoc] using h'
    rw [cancel_mono] at h''
    rw [h'', Limits.comp_zero]
  · refine Cochain.ext _ _ (fun p q hpq => ?_)
    rcases lt_trichotomy p (-(n : ℤ)) with h | h | h
    · exact (hneg q (by omega)).eq_of_tgt _ _
    · subst h
      obtain rfl : q = 0 := by omega
      rw [Cochain.single_v, hz]
    · rw [hv p q hpq h, Cochain.single_v_eq_zero _ _ _ _ _ (by omega)]
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.leray_simplicialCocycle_coboundary_of_acyclicLevels : ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc) (n : ℕ), (∀ k m : ℕ, 0 < m → k + m = n → ∀ y : H R (disc.obj (E.obj (op (SimplexCategory.mk (k))))) F m, y = 0) → (∀ s : (free R).obj (E.obj (op (SimplexCategory.mk (0)))) ⟶ F, IsCls s 0 → s = 0) ∧ ∀ s : (free R).obj (E.obj (op (SimplexCategory.mk (n + 1)))) ⟶ F, IsCls s 0 → ∃ t : (free R).obj (E.obj (op (SimplexCategory.mk (n)))) ⟶ F, cobd t = s := by
  first | (exact @GlobalTheory.EtC.leray_inj) | (exact GlobalTheory.EtC.leray_inj) | (intros; apply GlobalTheory.EtC.leray_inj <;> assumption)
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.dbar_glueSectionByPartition_eq : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (la : La) (u : Fin C.m → V n → ℂ) (i : ι) (v : V n) (w : ℂ) (j : Fin n), (∀ a, DifferentiableOn ℂ (u a) (ball (C.c a) (C.r a))) → v ∈ (A.chart i).target → wdb n j (glue C la u i ∘ (A.chart i).symm) v = ∑ a, wdb n j (fun x => (C.chi a ((A.chart i).symm x) : ℂ)) v * (A.g (A.kap + la) i (C.idx a) ((A.chart i).symm v) * u a (A.chart (C.idx a) ((A.chart i).symm v)) - w) := by
  first | exact @GlobalTheory.glue_wdb_eq | exact GlobalTheory.glue_wdb_eq | (intros; apply GlobalTheory.glue_wdb_eq <;> assumption)
end

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.pulledBackForms_intersection_eq_chart_localization : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (p : ℕ) (W : Type) [AddCommGroup W] [Module K W] [Module F W] [Module k W] [IsScalarTower F K W] [IsScalarTower k F W] [IsScalarTower k K W] (e : W →ₗ[K] DR k K) (I : Finset (Fin (d + 1))) (i : Fin (d + 1)), i ∈ I → (omB k K (rB k K x I) p).comap (e.restrictScalars k) = (Submodule.span (rA k x I) ((omB k K (rB k K x {i}) p).comap (e.restrictScalars k) : Set W)).restrictScalars k := by
  first | (exact @GlobalTheory.PD.omB_comap_loc) | (exact GlobalTheory.PD.omB_comap_loc) | (intros; apply GlobalTheory.PD.omB_comap_loc  <;> assumption)
end

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.integralClosure_projective_over_standardOpenRing : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ i, Module.Projective (rA k x {i}) (integralClosure (rA k x {i}) K) := by
  first | (exact @GlobalTheory.integralClosure_projective_rA) | (exact GlobalTheory.integralClosure_projective_rA) | (intros; apply GlobalTheory.integralClosure_projective_rA  <;> assumption)
end

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.complementaryModule_eq_topForms_of_finiteCover : ∀ (k F K : Type) [Field k] [CharZero k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] [FiniteDimensional F K] (d : ℕ) (u : Fin d → F), AlgebraicIndependent k u → ∀ (A : Subalgebra k F) [IsFractionRing A F], A = Algebra.adjoin k (Set.range u) → ∀ (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → Algebra.Smooth k B → ∀ τ : DR k K →ₗ[K] K, τ (ExteriorAlgebra.ιMulti K d fun j => D k K (algebraMap F K (u j))) = 1 → ∀ z : K, (∀ b : B, Algebra.trace F K (z * b) ∈ A) ↔ ∃ y ∈ omB k K B d, τ y = z := by
  first | (exact @GlobalTheory.ComplementaryForms.complementary_eq_topForms) | (exact GlobalTheory.ComplementaryForms.complementary_eq_topForms) | (intros; apply GlobalTheory.ComplementaryForms.complementary_eq_topForms  <;> assumption)
end

section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

theorem _root_.GlobalTheory.T.siegelParabolic_preserves_schwartzBruhat : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) (p : UG c (stdJ ν E)), p ∈ sieg c ν → ∀ φ ∈ SB (Matrix α ν E), parFun c ψ χ Q (mat c p) φ ∈ SB (Matrix α ν E) := by
  first | exact @GlobalTheory.KSp.parFun_mem | exact GlobalTheory.KSp.parFun_mem | (intros; apply GlobalTheory.KSp.parFun_mem <;> assumption)
end

section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

theorem _root_.GlobalTheory.T.fourier_hermitianMultiplier_braid_relation : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (b : Matrix ν ν E) (γ : ℂ), (b.map c)ᵀ = b → b.det ≠ 0 → HasGauss μ (fun x => ψ (2⁻¹ * pr c Q x (x * b))) γ → ∀ φ ∈ SB (Matrix α ν E), sc F χ (Fintype.card α) (-b⁻¹).det • fou c ψ Q μ (parFun c ψ χ Q (fromBlocks 1 b 0 1) (fou c ψ Q μ φ)) = γ • parFun c ψ χ Q (fromBlocks (-b⁻¹) 1 0 (-b)) (fou c ψ Q μ (parFun c ψ χ Q (fromBlocks 1 (-b⁻¹) 0 1) φ)) := by
  first | exact @GlobalTheory.KSp.braid_relation | exact GlobalTheory.KSp.braid_relation | (intros; apply GlobalTheory.KSp.braid_relation <;> assumption)
end
