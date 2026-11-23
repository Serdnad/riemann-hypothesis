module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1167
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1146
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1165
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1169
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1186
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1187
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1156
public import Formalism.LocalToGlobal.CMDeterminantIdeals.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorValueOfTriangularLaw
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1168
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001

@[expose] public section

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_dualNumberGenerator_of_torsorCoboundary : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left), P.IsLB → ∀ v : epsR R ⟶ B, IsTangent v → ∀ (j : ∀ (D : Type) [CommRing D] [Algebra R D], Pt A D → P.ι), IsChoice P j → ∀ s, IsPtGen P (AbDual.inl A B) s → ∀ k : Fn0 A, IsCob (chartsA P) (tanCoc P j v) k → ∃ T, IsEpsGen P v T := by
  first | exact @GlobalTheory.PtExt.exists_isEpsGen_of_isCob | exact GlobalTheory.PtExt.exists_isEpsGen_of_isCob | (intros; apply GlobalTheory.PtExt.exists_isEpsGen_of_isCob <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem lift_counit_pullTwo {R D D' : Type} [CommRing R] [CommRing D] [Bialgebra R D] [CommRing D']
    [Bialgebra R D'] (f : D →ₐc[R] D') (c : D ⊗[R] D) :
    Algebra.TensorProduct.lift (Bialgebra.counitAlgHom R D') (Bialgebra.counitAlgHom R D')
        (fun _ _ ↦ Commute.all _ _) (pullbackTwo f c) =
      Algebra.TensorProduct.lift (Bialgebra.counitAlgHom R D) (Bialgebra.counitAlgHom R D)
        (fun _ _ ↦ Commute.all _ _) c := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [pullbackTwo]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem diagSum_one (R D : Type) [CommRing R] [CommRing D] [Bialgebra R D] [Coalgebra.IsCocomm R D] (m : ℕ) :
    diagSum R D m 1 = (m : D) := by
  rw [Algebra.TensorProduct.one_def, diagSum_tmul]
  simp

theorem cocycle_mem_range_cob_of_diagSum_eq_zero :
    ∀ (p : ℕ) [Fact p.Prime]  (R : Type) [CommRing R] (N : ℕ), (p : R) ^ N = 0 →
      ∀ (G : PDivGroup p R) (z : G.cocycles), diagSum R (G.A N) (p ^ N) (z.1 N) = 0 →
        z ∈ LinearMap.range G.cob := by
  intro p _ R _ N hp G z hz
  have hq : ((p ^ N : ℕ) : R) = 0 := by rw [Nat.cast_pow, hp]
  let ε : ∀ n, G.A n ⊗[R] G.A n →ₐ[R] R := fun n =>
    Algebra.TensorProduct.lift (Bialgebra.counitAlgHom R (G.A n)) (Bialgebra.counitAlgHom R (G.A n))
      (fun _ _ ↦ Commute.all _ _)
  have hr : ∀ n, ε n (z.1 n) = ε 0 (z.1 0) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [← ih, ← (z.2 n).2]; exact (lift_counit_pullTwo _ _).symm
  let o : G.funs := ⟨fun _ => 1, fun n => map_one (G.res n)⟩
  let z' : G.cocycles := z + ε 0 (z.1 0) • G.cob o
  have hz' : ∀ n, z'.1 n = z.1 n - ε 0 (z.1 0) • (1 : G.A n ⊗[R] G.A n) := by
    intro n
    change z.1 n + ε 0 (z.1 0) • cobOne R (G.A n) 1 = _
    rw [cobOne_apply, Bialgebra.comul_one, ← Algebra.TensorProduct.one_def, sub_self, zero_sub, smul_neg,
      sub_eq_add_neg]
  have h0 : ∀ n, ε n (z'.1 n) = 0 := by
    intro n
    rw [hz', map_sub, map_smul, map_one, hr, smul_eq_mul, _root_.mul_one, sub_self]
  have hmem : z' ∈ LinearMap.range G.cob := by
    refine cocycle_mem_range_cob_of_pullback_mulBy_pow p R G N z'
      (fun n => diagSum R (G.A n) (p ^ N) (z'.1 n)) (fun n => ?_) (fun n => ?_) ?_
    · rw [diagSum_pullTwo, (z'.2 n).2]
    · rw [cobOne_diagSum_eq p R G n (p ^ N) hq _ (z'.2 n).1]
      have := h0 n
      simp only [ε] at this
      rw [this, zero_smul, sub_zero]
    · change diagSum R (G.A N) (p ^ N) (z'.1 N) = 0
      rw [hz', map_sub, map_smul, hz, diagSum_one, ← map_natCast (algebraMap R (G.A N)), hq, map_zero,
        smul_zero, sub_zero]
  have : z = z' - ε 0 (z.1 0) • G.cob o := by simp [z']
  rw [this]
  exact Submodule.sub_mem _ hmem (Submodule.smul_mem _ _ ⟨o, rfl⟩)

end GlobalTheory.PtExt
end
end

section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem Dat.diagSum_coc : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R) (t : G.TorsionTower A) (c : primDR A) (d : Dat t c) (N : ℕ), (p : R) ^ N = 0 → diagSum R (G.A N) (p ^ N) (d.coc N) = chi (p ^ N) d.g (G.A N) (t.y N) := by
  intro R _ A _ p G t c d N hN
  let e : ℕ → (G.A N →ₐ[R] G.A N) := fun j ↦ (toConv (AlgHom.id R (G.A N)) ^ j).ofConv
  let K : ℕ → G.A N := fun j ↦ fv d.f (G.A N) (G.A N) (e j) (t.y N) + e j (d.h N)
  have hm : ∀ j, (mulBy R (G.A N) j : G.A N →ₐ[R] G.A N) = e j := fun j ↦ by
    have h := comp_mulBy_pts (AlgHom.id R (G.A N)) j
    rwa [AlgHom.id_comp] at h
  have hy : ∀ j, spOver (e j) ≫ t.y N = t.y N ^ j := fun j ↦ by
    rw [← hm]; exact t.mulBy_y N j
  have he1 : e 1 = AlgHom.id R (G.A N) := by simp only [e, pow_one, ofConv_toConv]
  have hes : ∀ i, (toConv (e i) * toConv (AlgHom.id R (G.A N))).ofConv = e (i + 1) := fun i ↦ by
    simp only [e, toConv_ofConv, pow_succ]
  have hterm : ∀ i, Algebra.TensorProduct.lift (mulBy R (G.A N) i : G.A N →ₐ[R] G.A N) (AlgHom.id R (G.A N))
      (fun _ _ ↦ Commute.all _ _) (d.coc N) = d.g (G.A N) (t.y N ^ i) (t.y N) - (K (i + 1) - K i - K 1) := by
    intro i
    rw [hm i, Dat.lift_coc R A p G t c d N (G.A N) (e i) (AlgHom.id R _), hy, spOver_id, Category.id_comp, hes]
    simp only [K, he1]
  have hq : e (p ^ N) = e 0 := t.inj N (G.A N) _ _ (by rw [hy, hy, t.y_pow, pow_zero])
  have hz : ((p ^ N : ℕ) : G.A N) = 0 := by
    rw [Nat.cast_pow, ← map_natCast (algebraMap R (G.A N)), ← map_pow, hN, map_zero]
  rw [diagSum, LinearMap.sum_apply]
  simp only [AlgHom.toLinearMap_apply, hterm]
  rw [chi, Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_range_sub (fun j ↦ K j), Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, hz, zero_mul, sub_zero]
  have : K (p ^ N) = K 0 := by simp only [K, hq]
  rw [this, sub_self, sub_zero]

end GlobalTheory.PtExt
end

section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

namespace GlobalTheory.OnMatGram

theorem norm_evalAt_intVec_le {n : ℕ} (la : Fin n → ℕ) (j : Idx la) (g : UN n) :
    ‖evalAt g.1 (map (Int.castRingHom ℂ) (intVec la j))‖ ≤ 1 := by
  obtain ⟨-, -, K, sz, hsz, I, -, -, hb⟩ := (Formalism.GradedWeylDivisibility.sSBasis ℤ n n la).choose_spec.2 j
  have hv : intVec la j = Formalism.GradedWeylDivisibility.bideterminant ℤ sz hsz I := hb
  rw [hv, Formalism.GradedWeylDivisibility.ldlat_map_bidet]
  unfold Formalism.GradedWeylDivisibility.bideterminant
  rw [map_prod, norm_prod]
  refine Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun k _ => ?_
  unfold Formalism.GradedWeylDivisibility.initMinor
  rw [Formalism.GradedWeylDivisibility.algHom_det_of]
  have h : (Matrix.of fun p q : Fin (sz k) => evalAt g.1 (X (I k p, Fin.castLE (hsz k) q) : Pol n ℂ)) =
      g.1.submatrix (I k) (Fin.castLE (hsz k)) := by
    ext p q
    simp
  rw [h]
  exact GlobalTheory.T.unitary_minor_le_one_and_hadamard_columns.1 n (sz k) g (I k) (Fin.castLE (hsz k))

theorem normSq_basis_le {n : ℕ} (la : Fin n → ℕ) (j : Idx la) :
    normSq la (basis la ℂ j).1 ≤ dim la := by
  refine normSq_le_dim fun g => ?_
  rw [coe_basis]
  exact norm_evalAt_intVec_le la j g

theorem sum_norm_sq_onMat {n : ℕ} (la : Fin n → ℕ) (j : Idx la) :
    ∑ i, ‖onMat la i j‖ ^ 2 = normSq la (basis la ℂ j).1 := by
  rw [← norm_toSpace_sq, ← (onBasis la).repr.norm_map, EuclideanSpace.norm_sq_eq]
  rfl

theorem det_onMat_ne_zero {n : ℕ} (la : Fin n → ℕ) : (onMat la).det ≠ 0 := by
  let c : Module.Basis (Idx la) ℂ (Space la) := (basis la ℂ).map (toSpace la)
  have hc : onMat la = (onBasis la).toBasis.toMatrix c := by
    ext i j
    simp [onMat, c, Module.Basis.toMatrix_apply]
  rw [hc]
  exact (Matrix.isUnit_det_of_left_inverse (Module.Basis.toMatrix_mul_toMatrix_flip c _)).ne_zero

end GlobalTheory.OnMatGram

namespace GlobalTheory.OnMatGram

theorem norm_det_onMat_sq_le : ∀ (n : ℕ) (la : Fin n → ℕ), Antitone la → (onMat la).det ≠ 0 ∧ ‖(onMat la).det‖ ^ 2 ≤ (dim la : ℝ) ^ dim la := by
  intro n la _
  refine ⟨det_onMat_ne_zero la, ?_⟩
  refine (GlobalTheory.T.unitary_minor_le_one_and_hadamard_columns.2 (Idx la) (onMat la)).trans ?_
  calc ∏ j, ∑ i, ‖onMat la i j‖ ^ 2 ≤ ∏ _j : Idx la, (dim la : ℝ) :=
        Finset.prod_le_prod₀ (fun j _ => Finset.sum_nonneg fun _ _ => by positivity)
          fun j _ => (sum_norm_sq_onMat la j).trans_le (normSq_basis_le la j)
    _ = (dim la : ℝ) ^ dim la := by rw [Finset.prod_const, Finset.card_univ, ← dim_eq_card]

end GlobalTheory.OnMatGram
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtExt.PushSec

variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] [IsCommMonObj A]

theorem injective_of_ff {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D']
    (ψ : D →ₐ[R] D') (h : (ψ : D →+* D').FaithfullyFlat) : Function.Injective ψ := by
  letI : Algebra D D' := (ψ : D →+* D').toAlgebra
  haveI : Module.FaithfullyFlat D D' := h
  exact FaithfulSMul.algebraMap_injective D D'

theorem root_map {n : ℕ} {D D' E : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] [CommRing E]
    [Algebra R E] (φ : D →ₐ[R] D') (ρ : D' →ₐ[R] E) (x : Pt A D) (z : Pt A D')
    (hz : (z ^ n : Pt A D') = spOver φ ≫ x) :
    ((spOver ρ ≫ z) ^ n : Pt A E) = spOver (ρ.comp φ) ≫ x := by
  rw [← MonObj.comp_pow z n (spOver ρ), hz, ← Category.assoc, spOver_comp]

theorem pow_mul_inv_eq_one {n : ℕ} {E : Type} [CommRing E] [Algebra R E] {y w u : Pt A E} (hy : y ^ n = u)
    (hw : w ^ n = u) : (y * w⁻¹) ^ n = 1 := by
  rw [mul_pow, inv_pow, hy, hw, mul_inv_cancel]

section Fixed

variable {n : ℕ} {b : Fn0 A} {D D₁ : Type} [CommRing D] [Algebra R D] [CommRing D₁] [Algebra R D₁]

def val (b : Fn0 A) (z₀ : Pt A D₁) (a : D₁) {D' F : Type} [CommRing D'] [Algebra R D'] [CommRing F] [Algebra R F]
    (ρ : D' →ₐ[R] F) (φ' : D₁ →ₐ[R] F) (z : Pt A D') : F :=
  φ' a + b F ((spOver ρ ≫ z) * (spOver φ' ≫ z₀)⁻¹)

variable (hb : IsTorsChar n b) (ψ : D →ₐ[R] D₁) (x : Pt A D) (z₀ : Pt A D₁)
  (hz₀ : (z₀ ^ n : Pt A D₁) = spOver ψ ≫ x)
  (a : D₁)
  (ha : ∀ (E : Type) [CommRing E] [Algebra R E] (α β : D₁ →ₐ[R] E), α.comp ψ = β.comp ψ →
    b E ((spOver β ≫ z₀) * (spOver α ≫ z₀)⁻¹) = β a - α a)


include hz₀ in
theorem val_tors {D' F : Type} [CommRing D'] [Algebra R D'] [CommRing F] [Algebra R F] (φ : D →ₐ[R] D')
    (z : Pt A D') (hz : (z ^ n : Pt A D') = spOver φ ≫ x) (ρ : D' →ₐ[R] F) (φ' : D₁ →ₐ[R] F)
    (h : ρ.comp φ = φ'.comp ψ) :
    ((spOver ρ ≫ z) * (spOver φ' ≫ z₀)⁻¹) ^ n = 1 :=
  pow_mul_inv_eq_one (root_map φ ρ x z hz) (by rw [root_map ψ φ' x z₀ hz₀, h])


include hb hz₀ in
theorem map_val {D' F G : Type} [CommRing D'] [Algebra R D'] [CommRing F] [Algebra R F] [CommRing G] [Algebra R G]
    (φ : D →ₐ[R] D') (z : Pt A D') (hz : (z ^ n : Pt A D') = spOver φ ≫ x) (ρ : D' →ₐ[R] F) (φ' : D₁ →ₐ[R] F)
    (h : ρ.comp φ = φ'.comp ψ) (g₁ : F →ₐ[R] G) :
    g₁ (val b z₀ a ρ φ' z) = val b z₀ a (g₁.comp ρ) (g₁.comp φ') z := by
  unfold val
  rw [map_add (f := _), ← hb.1 F G g₁ _ (val_tors ψ x z₀ hz₀ φ z hz ρ φ' h), MonObj.comp_mul, GrpObj.comp_inv,
    ← Category.assoc, ← Category.assoc, spOver_comp, spOver_comp]
  rfl


include hb hz₀ ha in
theorem val_indep {D' F : Type} [CommRing D'] [Algebra R D'] [CommRing F] [Algebra R F] (φ : D →ₐ[R] D')
    (z : Pt A D') (hz : (z ^ n : Pt A D') = spOver φ ≫ x) (ρ : D' →ₐ[R] F) (α β : D₁ →ₐ[R] F)
    (hα : ρ.comp φ = α.comp ψ)
    (hβ : ρ.comp φ = β.comp ψ) : val b z₀ a ρ α z = val b z₀ a ρ β z := by
  unfold val
  have t1 := val_tors ψ x z₀ hz₀ φ z hz ρ β hβ
  have t2 : ((spOver β ≫ z₀) * (spOver α ≫ z₀)⁻¹) ^ n = 1 :=
    pow_mul_inv_eq_one (by rw [root_map ψ β x z₀ hz₀, ← hβ]) (by rw [root_map ψ α x z₀ hz₀, ← hα])
  have e : (spOver ρ ≫ z) * (spOver α ≫ z₀)⁻¹ =
      ((spOver ρ ≫ z) * (spOver β ≫ z₀)⁻¹) * ((spOver β ≫ z₀) * (spOver α ≫ z₀)⁻¹) := by
    rw [_root_.mul_assoc, _root_.inv_mul_cancel_left]
  rw [e, hb.2 F _ _ t1 t2, ha F α β (hα.symm.trans hβ)]
  abel

def IsVal {D' : Type} [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (z : Pt A D') (e : D') : Prop :=
  ∀ (F : Type) [CommRing F] [Algebra R F] (ρ : D' →ₐ[R] F) (φ' : D₁ →ₐ[R] F), ρ.comp φ = φ'.comp ψ →
    ρ e = val b z₀ a ρ φ' z


include hb hz₀ ha in
theorem exists_isVal (hψ : (ψ : D →+* D₁).FaithfullyFlat) {D' : Type} [CommRing D'] [Algebra R D']
    (φ : D →ₐ[R] D') (z : Pt A D') (hz : (z ^ n : Pt A D') = spOver φ ≫ x) :
    ∃ e : D', IsVal (b := b) ψ z₀ a φ z e := by
  obtain ⟨E', _, _, ρ₀, φ₀, hff, hsq⟩ := GlobalTheory.exists_pushout_faithfullyFlat R D D₁ D' ψ φ hψ
  obtain ⟨e, he, -⟩ := GlobalTheory.ff_descent_pairs R D' E' ρ₀ hff (val b z₀ a ρ₀ φ₀ z) (by
    intro G _ _ g₁ g₂ hg₁g₂
    rw [map_val hb ψ x z₀ hz₀ a φ z hz ρ₀ φ₀ hsq g₁, map_val hb ψ x z₀ hz₀ a φ z hz ρ₀ φ₀ hsq g₂, ← hg₁g₂]
    refine val_indep hb ψ x z₀ hz₀ a ha φ z hz _ _ _ ?_ ?_
    · rw [AlgHom.comp_assoc, hsq, AlgHom.comp_assoc]
    · rw [hg₁g₂, AlgHom.comp_assoc, hsq, AlgHom.comp_assoc])
  refine ⟨e, fun F _ _ ρ φ' h ↦ ?_⟩
  obtain ⟨G, _, _, ρ₀', ρ', hff', hsq'⟩ := GlobalTheory.exists_pushout_faithfullyFlat R D' E' F ρ₀ ρ hff
  apply injective_of_ff ρ₀' hff'
  rw [map_val hb ψ x z₀ hz₀ a φ z hz ρ φ' h ρ₀']
  change (ρ₀'.comp ρ) e = _
  rw [hsq', AlgHom.comp_apply, he, map_val hb ψ x z₀ hz₀ a φ z hz ρ₀ φ₀ hsq ρ']
  refine val_indep hb ψ x z₀ hz₀ a ha φ z hz _ _ _ ?_ ?_
  · rw [AlgHom.comp_assoc, hsq, AlgHom.comp_assoc]
  · rw [← hsq', AlgHom.comp_assoc, h, AlgHom.comp_assoc]

theorem isVal_unique (hψ : (ψ : D →+* D₁).FaithfullyFlat) {D' : Type} [CommRing D'] [Algebra R D']
    (φ : D →ₐ[R] D') (z : Pt A D') {e e' : D'} (he : IsVal (b := b) ψ z₀ a φ z e) (he' : IsVal (b := b) ψ z₀ a φ z e') : e = e' := by
  obtain ⟨E', _, _, ρ₀, φ₀, hff, hsq⟩ := GlobalTheory.exists_pushout_faithfullyFlat R D D₁ D' ψ φ hψ
  exact injective_of_ff ρ₀ hff ((he E' ρ₀ φ₀ hsq).trans (he' E' ρ₀ φ₀ hsq).symm)

end Fixed

section Sec

variable {n : ℕ} {b : Fn0 A} {D D₁ : Type} [CommRing D] [Algebra R D] [CommRing D₁] [Algebra R D₁]
  (hb : IsTorsChar n b) (ψ : D →ₐ[R] D₁) (x : Pt A D) (z₀ : Pt A D₁)
  (hz₀ : (z₀ ^ n : Pt A D₁) = spOver ψ ≫ x)
  (a : D₁)
  (ha : ∀ (E : Type) [CommRing E] [Algebra R E] (α β : D₁ →ₐ[R] E), α.comp ψ = β.comp ψ →
    b E ((spOver β ≫ z₀) * (spOver α ≫ z₀)⁻¹) = β a - α a)
  (hψ : (ψ : D →+* D₁).FaithfullyFlat)


open Classical in
def sec : RootFn A D := fun D' _ _ φ z ↦
  if h : (z ^ n : Pt A D') = spOver φ ≫ x then Classical.choose (exists_isVal hb ψ x z₀ hz₀ a ha hψ φ z h) else 0

theorem sec_spec {D' : Type} [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (z : Pt A D')
    (hz : (z ^ n : Pt A D') = spOver φ ≫ x) : IsVal (b := b) ψ z₀ a φ z (sec hb ψ x z₀ hz₀ a ha hψ D' φ z) := by
  unfold sec
  rw [dite_eq_left hz]
  exact Classical.choose_spec (exists_isVal hb ψ x z₀ hz₀ a ha hψ φ z hz)

theorem isSec_sec : IsSec n b x (sec hb ψ x z₀ hz₀ a ha hψ) := by
  refine ⟨fun D' _ _ D'' _ _ φ ψ₂ z hz ↦ ?_, fun D' _ _ φ z w hz hw ↦ ?_⟩
  · have hz' := root_map φ ψ₂ x z hz
    refine isVal_unique ψ z₀ a hψ (ψ₂.comp φ) _ (sec_spec hb ψ x z₀ hz₀ a ha hψ _ _ hz') ?_
    intro F _ _ ρ φ' h
    change (ρ.comp ψ₂) _ = _
    rw [sec_spec hb ψ x z₀ hz₀ a ha hψ φ z hz F (ρ.comp ψ₂) φ' (by rw [AlgHom.comp_assoc]; exact h)]
    unfold val
    rw [← Category.assoc, spOver_comp]
  · have hzw : ((z * w) ^ n : Pt A D') = spOver φ ≫ x := by rw [mul_pow, hz, hw, _root_.mul_one]
    refine isVal_unique ψ z₀ a hψ φ _ (sec_spec hb ψ x z₀ hz₀ a ha hψ _ _ hzw) ?_
    intro F _ _ ρ φ' h
    have tw : (spOver ρ ≫ w) ^ n = 1 := by rw [← MonObj.comp_pow, hw, MonObj.comp_one]
    rw [map_add (f := _), sec_spec hb ψ x z₀ hz₀ a ha hψ φ z hz F ρ φ' h, ← hb.1 D' F ρ w hw]
    unfold val
    rw [add_assoc, ← hb.2 F _ _ (val_tors ψ x z₀ hz₀ φ z hz ρ φ' h) tw, MonObj.comp_mul, _root_.mul_right_comm]

end Sec

theorem exists_isSec : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (n : ℕ), HasRoots A n →
    ∀ b : Fn0 A, IsTorsChar n b → ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D),
      ∃ s : RootFn A D, IsSec n b x s := by
  intro R _ A _ _ n hR b hb D _ _ x
  obtain ⟨D₁, _, _, ψ, z₀, hψ, hz₀⟩ := hR D x
  obtain ⟨a, ha⟩ := GlobalTheory.FlatDescent.cocycle_descends R D D₁ ψ hψ
    (fun E _ _ α β ↦ b E ((spOver β ≫ z₀) * (spOver α ≫ z₀)⁻¹)) (by
      intro E _ _ E' _ _ α β g hαβ
      have t : ((spOver β ≫ z₀) * (spOver α ≫ z₀)⁻¹) ^ n = 1 :=
        pow_mul_inv_eq_one (root_map ψ β x z₀ hz₀) (by rw [root_map ψ α x z₀ hz₀, hαβ])
      show b E' _ = g (b E _)
      rw [← hb.1 E E' g _ t, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, ← Category.assoc, spOver_comp,
        spOver_comp]) (by
      intro E _ _ f₁ f₂ f₃ h12 h23
      have t1 : ((spOver f₂ ≫ z₀) * (spOver f₁ ≫ z₀)⁻¹) ^ n = 1 :=
        pow_mul_inv_eq_one (root_map ψ f₂ x z₀ hz₀) (by rw [root_map ψ f₁ x z₀ hz₀, h12])
      have t2 : ((spOver f₃ ≫ z₀) * (spOver f₂ ≫ z₀)⁻¹) ^ n = 1 :=
        pow_mul_inv_eq_one (root_map ψ f₃ x z₀ hz₀) (by rw [root_map ψ f₂ x z₀ hz₀, h23])
      have e : (spOver f₃ ≫ z₀) * (spOver f₁ ≫ z₀)⁻¹ =
          ((spOver f₂ ≫ z₀) * (spOver f₁ ≫ z₀)⁻¹) * ((spOver f₃ ≫ z₀) * (spOver f₂ ≫ z₀)⁻¹) := by
        rw [_root_.mul_comm ((spOver f₂ ≫ z₀) * _), _root_.mul_assoc, _root_.inv_mul_cancel_left]
      show b E _ = b E _ + b E _
      rw [e, hb.2 E _ _ t1 t2])
  exact ⟨_, isSec_sec hb ψ x z₀ hz₀ a (fun E _ _ α β h ↦ ha E α β h) hψ⟩

end GlobalTheory.PtExt.PushSec
end
end

section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

theorem _root_.GlobalTheory.T.exists_tensor_value_of_triangular_law : ∀ (T : Type) [Fintype T] [DecidableEq T] (N : T → ℕ) (la : ∀ t, Fin (N t) → ℕ) (K : Type) [Field K] [CharZero K] (G : MvPolynomial (Formalism.L2.LamCM.FrVar N) K), (∀ y b : ∀ t, Matrix (Fin (N t)) (Fin (N t)) K, (∀ t, (y t).det ≠ 0) → (∀ t, (b t).BlockTriangular id ∧ ∀ i, b t i i ≠ 0) → Formalism.L2.LamCM.evalFr G (fun t => y t * b t) = (∏ t, diagChar (la t) (b t)) * Formalism.L2.LamCM.evalFr G y) → ∃ x : TIdx la → K, ∀ (S : Type) [CommRing S] (φ : K →+* S) (y : ∀ t, Matrix (Fin (N t)) (Fin (N t)) S), Formalism.L2.LamCM.evalFr (MvPolynomial.map φ G) y = tval la (fun I => φ (x I)) y := by
  first | exact @GlobalTheory.TensorValue.exists_tval_of_triangular | exact GlobalTheory.TensorValue.exists_tval_of_triangular | (intros; apply GlobalTheory.TensorValue.exists_tval_of_triangular <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc


theorem _root_.GlobalTheory.T.curve_closedPoint_isCentreOfPlace : ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ c : C, c ≠ x (IsLocalRing.closedPoint K) → ∃ (v : Place k K) (b : Sp v.O ⟶ C), spMap v.O.subtype ≫ b = x ∧ b (IsLocalRing.closedPoint v.O) = c := by
  first | exact @GlobalTheory.Nef.centre_place | exact GlobalTheory.Nef.centre_place | (intros; apply GlobalTheory.Nef.centre_place <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

namespace GlobalTheory.MBLow.Cl

theorem tangent_lift_of_pullback : ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] (D : DegPre R) (x : KeyIn ℂ)
    (φ : x.P.A.left ⟶ D.P.A.left), IsGrpPullback x.P.A D.P.A (spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) φ →
    eSec x.P.A ≫ φ = spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R))) ≫ eSec D.P.A →
    ∀ b : TE R ℂ ⟶ D.P.A, redE ℂ ≫ b.left = (DegPre.zeroF D ℂ).left →
      ∃ b' : epsR ℂ ⟶ x.P.A, IsTangent b' ∧ b'.left ≫ φ = b.left := by
  intro R _ _ _ D x φ hφ he b hb
  have hTF : (TF (R := R) ℂ).hom = spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R))) := by
    simp only [TF, Over.mk_hom, jFK, jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hw : b.left ≫ D.P.A.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫
      spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R))) := by
    rw [Over.w b, ← hTF]; rfl
  let l := hφ.1.lift b.left (spMap (algebraMap ℂ (DualNumber ℂ))) hw
  have hl1 : l ≫ φ = b.left := hφ.1.lift_fst _ _ _
  have hl2 : l ≫ x.P.A.hom = spMap (algebraMap ℂ (DualNumber ℂ)) := hφ.1.lift_snd _ _ _
  refine ⟨Over.homMk l hl2, ?_, hl1⟩
  show spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ l = eSec x.P.A
  apply hφ.1.hom_ext
  · rw [Category.assoc, hl1, he]
    change redE ℂ ≫ b.left = _
    rw [hb, DegPre.zeroF, Over.comp_left, ← hTF]
    congr 1
  · rw [Category.assoc, hl2]
    have h1 : eSec x.P.A ≫ x.P.A.hom = 𝟙 _ := by
      simp only [eSec]
      rw [Over.w η[x.P.A]]; rfl
    rw [h1]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp (algebraMap ℂ (DualNumber ℂ)) = RingHom.id ℂ := by
      ext z; simp
    rw [this, CommRingCat.ofHom_id, Spec.map_id]; rfl

end GlobalTheory.MBLow.Cl
end
