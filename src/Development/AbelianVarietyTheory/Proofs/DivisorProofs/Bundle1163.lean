module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1129
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1130
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle033
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle211
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Valuation.AlgebraInstances
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff

@[expose] public section

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem _root_.GlobalTheory.T.exists_sqrtNegPrimeKernelDatum_of_integersLattice : ∀ (p : ℕ) (L₀ : PeriodPair), p.Prime → p % 4 = 3 → 3 < p → IsIntegersLattice p L₀ → ∃ (L : PeriodPair) (t : ℂ), Datum p ℚ⟮(latticeCurve L₀).j⟯ L t ∧ (latticeCurve L).j = (latticeCurve L₀).j := by
  first | exact @GlobalTheory.CMModel.exists_datum_of_isIntegersLattice | exact GlobalTheory.CMModel.exists_datum_of_isIntegersLattice | (intros; apply GlobalTheory.CMModel.exists_datum_of_isIntegersLattice <;> assumption)
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem _root_.GlobalTheory.T.stable_sum_elim_of_isKerReps_add_sub_sqrtNegNat : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (a : ℤ) (S S' : Finset ℂ), L.g₂ ∈ F → L.g₃ ∈ F → MulStable L (sqrtNegNat p) → IsKerReps L (a + sqrtNegNat p) S → IsKerReps L (a - sqrtNegNat p) S' → Stable L F (Sum.elim (fun t : S => (t : ℂ)) (fun t : S' => (t : ℂ))) := by
  first | exact @GlobalTheory.CMModel.stable_kerReps_add_sub | exact GlobalTheory.CMModel.stable_kerReps_add_sub | (intros; apply GlobalTheory.CMModel.stable_kerReps_add_sub <;> assumption)
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem _root_.GlobalTheory.T.torsion_weierstrass_coords_mem_of_intV : ∀ (L : PeriodPair) (β u : ℂ) (V : ValuationSubring ℂ) (N : ℕ), MulStable L β → β.im ≠ 0 → V.valuation u ^ 12 = V.valuation (latticeCurve L).Δ → V.valuation (N : ℂ) = 1 → Odd N → ∀ (hu : u ≠ 0) (r s t : ℂ), IntV V ((⟨Units.mk0 u hu, r, s, t⟩ : VariableChange ℂ) • latticeCurve L) → ∀ z, z ∉ L.lattice → (N : ℂ) * z ∈ L.lattice → (L.weierstrassP z - r) / u ^ 2 ∈ V ∧ (L.derivWeierstrassP z / 2 - t - s * (L.weierstrassP z - r)) / u ^ 3 ∈ V := by
  first | exact @GlobalTheory.CMModel.torsion_coords_mem_of_odd | exact GlobalTheory.CMModel.torsion_coords_mem_of_odd | (intros; apply GlobalTheory.CMModel.torsion_coords_mem_of_odd <;> assumption)
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem _root_.GlobalTheory.T.weierstrassCoeffs_integral_average_change_of_variables : ∀ (V : ValuationSubring ℂ) (a₄ a₆ r s t : ℂ) (u : ℂˣ) (ι : Type) [Fintype ι] (X Y : ι → ℂ), IntV V ((⟨u, r, s, t⟩ : VariableChange ℂ) • (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve ℂ)) → V.valuation (Fintype.card ι : ℂ) = 1 → (∀ i, (X i - r) / (u : ℂ) ^ 2 ∈ V) → (∀ i, (Y i - t - s * (X i - r)) / (u : ℂ) ^ 3 ∈ V) → (∀ i, V.valuation (2 * Y i) = V.valuation (u : ℂ) ^ 3) → IntV V ((⟨u, (∑ i, X i) / Fintype.card ι, (∑ i, (3 * X i ^ 2 + a₄) / (2 * Y i)) / Fintype.card ι, (∑ i, Y i) / Fintype.card ι⟩ : VariableChange ℂ) • (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve ℂ)) := by
  first | exact @GlobalTheory.CMModel.intV_average | exact GlobalTheory.CMModel.intV_average | (intros; apply GlobalTheory.CMModel.intV_average <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.sections_flat_baseChange_affineMilnorSquare_open : ∀ (S : Scheme.{0}) (A T T₁ T₂ T₀ : Over S) [Flat A.hom] (j₁ : T₁ ⟶ T) (j₂ : T₂ ⟶ T) (k₁ : T₀ ⟶ T₁) (k₂ : T₀ ⟶ T₂), Milnor j₁.left j₂.left k₁.left k₂.left → ∀ W : (A ⊗ T).left.Opens, (∀ a b : Γ((A ⊗ T).left, W), (A ◁ j₁).left.app W a = (A ◁ j₁).left.app W b → (A ◁ j₂).left.app W a = (A ◁ j₂).left.app W b → a = b) ∧ ∀ (V : (A ⊗ T₀).left.Opens) (h₁ : V ≤ (A ◁ k₁).left ⁻¹ᵁ ((A ◁ j₁).left ⁻¹ᵁ W)) (h₂ : V ≤ (A ◁ k₂).left ⁻¹ᵁ ((A ◁ j₂).left ⁻¹ᵁ W)), (A ◁ k₁).left ⁻¹ᵁ ((A ◁ j₁).left ⁻¹ᵁ W) ≤ V → ∀ (a₁ : Γ((A ⊗ T₁).left, (A ◁ j₁).left ⁻¹ᵁ W)) (a₂ : Γ((A ⊗ T₂).left, (A ◁ j₂).left ⁻¹ᵁ W)), (A ◁ k₁).left.appLE _ V h₁ a₁ = (A ◁ k₂).left.appLE _ V h₂ a₂ → ∃ a : Γ((A ⊗ T).left, W), (A ◁ j₁).left.app W a = a₁ ∧ (A ◁ j₂).left.app W a = a₂ := by
  first | exact @GlobalTheory.DualOpen.sections_milnor | exact GlobalTheory.DualOpen.sections_milnor | (intros; apply GlobalTheory.DualOpen.sections_milnor <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Published
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.semiNegative_descends_fieldExtension_curve : ∀ (k : Type) [Field k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)], IsCurve k C →
    ∀ (k' : Type) [Field k'] [Algebra k k'], ∃ (C' : Scheme.{0}) (_ : Algebra k' Γ(C', ⊤)) (π : C' ⟶ C), IsCurve k' C' ∧
      ∀ F : C.Modules, SemiNeg k' ((Scheme.Modules.pullback π).obj F) → SemiNeg k F := by
  first | exact @GlobalTheory.SemiNegFieldChange.semiNeg_descends_baseChange | exact GlobalTheory.SemiNegFieldChange.semiNeg_descends_baseChange | (intros; apply GlobalTheory.SemiNegFieldChange.semiNeg_descends_baseChange <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef

theorem existsUnique_centre : ∀ (k K E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] [Field E] [Algebra k E] [Algebra K E] [IsScalarTower k K E] [FiniteDimensional K E] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ p : Place k E, ∃! b : Sp p.O ⟶ C, spMap p.O.subtype ≫ b = spMap (algebraMap K E) ≫ x := by
  intro k K E _ _ _ _ _ _ _ _ _ _ C _ x hx p
  obtain ⟨⟨-, hproj, -⟩, -, hxs⟩ := hx
  have hprop : IsProper (strHom k (X := C)) := (isProper_and_exists_isAmpleLB_of_isProjOver hproj).1
  have hk : ∀ c : k, algebraMap k E c ∈ p.O := by
    intro c
    rw [Valuation.mem_valuationSubring_iff]
    by_cases hc : c = 0
    · simp [hc]
    · rw [p.2.2 c hc]
  let ik : k →+* p.O := (algebraMap k E).codRestrict p.O hk
  have hik : p.O.subtype.comp ik = algebraMap k E := RingHom.ext fun _ => rfl
  have hsq : (spMap (algebraMap K E) ≫ x) ≫ strHom k C = spMap (algebraMap p.O E) ≫ spMap ik := by
    rw [Category.assoc, hxs, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq]
    rfl
  have hv : ValuativeCriterion (strHom k C) := by
    rw [IsProper.eq_valuativeCriterion] at hprop
    exact hprop.1.1.1
  let S : ValuativeCommSq (strHom k C) :=
    { R := p.O, K := E, i₁ := spMap (algebraMap K E) ≫ x, i₂ := spMap ik, commSq := ⟨hsq⟩ }
  obtain ⟨U⟩ := hv S

  have hover : ∀ b : Sp p.O ⟶ C, spMap p.O.subtype ≫ b = spMap (algebraMap K E) ≫ x → b ≫ strHom k C = spMap ik := by
    intro b hb
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (b ≫ strHom k C)
    have e : Spec.map (φ ≫ CommRingCat.ofHom p.O.subtype) = Spec.map (CommRingCat.ofHom (algebraMap k E)) := by
      rw [Spec.map_comp, hφ, ← Category.assoc, hb, Category.assoc, hxs, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← IsScalarTower.algebraMap_eq]
    have e2 := Spec.map_injective e
    rw [← hφ]
    congr 1
    ext c
    exact congrArg (fun f => (CommRingCat.Hom.hom f) c) e2
  refine ⟨U.default.l, U.default.fac_left, fun b hb => ?_⟩
  let L : S.commSq.LiftStruct := { l := b, fac_left := hb, fac_right := hover b hb }
  exact congrArg CommSq.LiftStruct.l (U.uniq L)

end GlobalTheory.Nef
end
end

section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

noncomputable section
namespace GlobalTheory.DefPt

theorem evalAt_mul_intVec {n : ℕ} (la : Fin n → ℕ) {K S : Type} [Field K] [CharZero K] [CommRing S] (φ : K →+* S)
    (g : Matrix (Fin n) (Fin n) K) (y : Matrix (Fin n) (Fin n) S) (j : Idx la) :
    GlobalTheory.DualWeyl.evalAt (g.map φ * y) (map (Int.castRingHom S) (intVec la j)) =
      ∑ i, φ (rhoMat la g i j) * GlobalTheory.DualWeyl.evalAt y (map (Int.castRingHom S) (intVec la i)) := by
  have h1 : (rho la K gᵀ (basis la K j) : Pol n K) = ∑ i, rhoMat la g i j • (basis la K i : Pol n K) := by
    have h := (basis la K).sum_repr (rho la K gᵀ (basis la K j))
    conv_lhs => rw [← h]
    simp only [Submodule.coe_sum, Submodule.coe_smul, rhoMat, LinearMap.toMatrix_apply]
  have hmap : ∀ i, map φ (basis la K i : Pol n K) = map (Int.castRingHom S) (intVec la i) := by
    intro i
    rw [coe_basis, map_map, RingHom.ext_int (φ.comp (Int.castRingHom K)) (Int.castRingHom S)]
  rw [coe_rho, Matrix.transpose_transpose] at h1
  rw [← hmap j, ← evalAt_rowAct, ← GlobalTheory.NabStab.map_rowAct, coe_basis, ← coe_basis, h1]

  simp only [map_sum, map_smul, smul_eq_C_mul, map_mul, map_C]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hmap i]
  simp [GlobalTheory.DualWeyl.evalAt]

theorem tval_translate : ∀ (T : Type) [Fintype T] [DecidableEq T] (N : T → ℕ) (la : ∀ t, Fin (N t) → ℕ) (K S : Type) [Field K] [CharZero K] [CommRing S] (φ : K →+* S) (x : TIdx la → K) (g : ∀ t, Matrix (Fin (N t)) (Fin (N t)) K) (y : ∀ t, Matrix (Fin (N t)) (Fin (N t)) S), tval la (fun I => φ (x I)) (fun t => (g t).map φ * y t) = tval la (fun I => φ (((kron fun t => rhoMat (la t) (g t)) *ᵥ x) I)) y := by
  intro T _ _ N la K S _ _ _ φ x g y
  unfold tval
  simp only [evalAt_mul_intVec, Finset.prod_univ_sum]

  simp only [Matrix.mulVec, dotProduct, kron, Matrix.of_apply, map_sum, map_mul, map_prod, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun J _ => Finset.sum_congr rfl fun I _ => ?_
  rw [Finset.prod_mul_distrib]
  ring

end GlobalTheory.DefPt
end
end

section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

noncomputable section
namespace GlobalTheory.DefPt

theorem intVec_mem_nabla {n : ℕ} (la : Fin n → ℕ) (i : Idx la) : intVec la i ∈ nabla la ℤ := by
  have h := (Formalism.GradedWeylDivisibility.sSBasis ℤ n n la).choose_spec.1.2.1
  rw [nabla, ← h]
  exact Submodule.subset_span ⟨i, rfl⟩

def genUpperTri (n : ℕ) : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) ℤ) :=
  Matrix.of fun i j => if i ≤ j then X (i, j) else 0

theorem genUpperTri_blockTriangular (n : ℕ) : (genUpperTri n).BlockTriangular id := by
  intro i j hij
  simp only [genUpperTri, Matrix.of_apply]
  rw [if_neg (not_le.mpr (show j < i from hij))]

theorem colAct_intCast_of_mem {n : ℕ} {la : Fin n → ℕ} {f : Pol n ℤ} (hf : f ∈ nabla la ℤ)
    {S : Type} [CommRing S] (b : Matrix (Fin n) (Fin n) S) (hb : b.BlockTriangular id) :
    colAct b (map (Int.castRingHom S) f) = diagChar la b • map (Int.castRingHom S) f := by
  let ψ : MvPolynomial (Fin n × Fin n) ℤ →+* S := (aeval (R := ℤ) fun v : Fin n × Fin n => b v.1 v.2).toRingHom
  have hB : (genUpperTri n).map ψ = b := by
    ext i j
    simp only [Matrix.map_apply, genUpperTri, Matrix.of_apply]
    split_ifs with h
    · simp [ψ]
    · rw [map_zero, hb (show id j < id i from not_le.mp h)]
  have hgen := colAct_map_of_mem (Int.castRingHom (MvPolynomial (Fin n × Fin n) ℤ)) hf (genUpperTri n)
    (genUpperTri_blockTriangular n)
  have h2 := congrArg (map ψ) hgen
  rw [map_colAct, hB, map_map] at h2
  have hc : ψ.comp (Int.castRingHom (MvPolynomial (Fin n × Fin n) ℤ)) = Int.castRingHom S :=
    RingHom.ext_int _ _
  rw [hc] at h2
  rw [h2, smul_eq_C_mul, map_mul, map_C, map_map, hc, smul_eq_C_mul]
  congr 2
  simp only [diagChar, map_prod, map_pow, ← hB, Matrix.map_apply]

theorem evalAt_mul_triangular_intVec {n : ℕ} (la : Fin n → ℕ) (i : Idx la) {S : Type} [CommRing S]
    (y b : Matrix (Fin n) (Fin n) S) (hb : b.BlockTriangular id) :
    DualWeyl.evalAt (y * b) (map (Int.castRingHom S) (intVec la i)) =
      diagChar la b * DualWeyl.evalAt y (map (Int.castRingHom S) (intVec la i)) := by
  rw [← evalAt_colAct, colAct_intCast_of_mem (intVec_mem_nabla la i) b hb, smul_eq_C_mul, map_mul]
  simp [DualWeyl.evalAt]

theorem tval_mul_triangular : ∀ (T : Type) [Fintype T] [DecidableEq T] (N : T → ℕ) (la : ∀ t, Fin (N t) → ℕ) (S : Type) [CommRing S] (x : TIdx la → S) (y b : ∀ t, Matrix (Fin (N t)) (Fin (N t)) S), (∀ t, (b t).BlockTriangular id) → tval la x (fun t => y t * b t) = (∏ t, diagChar (la t) (b t)) * tval la x y := by
  intro T _ _ N la S _ x y b hb
  unfold tval
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  simp only [evalAt_mul_triangular_intVec _ _ _ _ (hb _), Finset.prod_mul_distrib]
  ring

end GlobalTheory.DefPt
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Nef

theorem evAt_eq_comp {R : Type} [CommRing R] {X : Scheme.{0}} (b : Sp R ⟶ X) {U : X.Opens} (h : ⊤ ≤ b ⁻¹ᵁ U) :
    CommRingCat.ofHom (evAt b h) = b.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom := rfl

theorem evAt_spMap_comp (R R' : Type) [CommRing R] [CommRing R'] (X : Scheme.{0}) (φ : R →+* R') (b : Sp R ⟶ X)
    (U : X.Opens) (h : ⊤ ≤ b ⁻¹ᵁ U) (h' : ⊤ ≤ (spMap φ ≫ b) ⁻¹ᵁ U) (f : Γ(X, U)) :
    evAt (spMap φ ≫ b) h' f = φ (evAt b h f) := by
  have e2 := Scheme.Hom.appLE_comp_appLE (spMap φ) b U ⊤ ⊤ h le_rfl
  have e3 : (spMap φ).appLE ⊤ ⊤ le_rfl = (spMap φ).appTop := (Scheme.Hom.app_eq_appLE _).symm
  have e4 : (spMap φ ≫ b).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of R')).hom =
      b.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ CommRingCat.ofHom φ := by
    rw [← e2, e3, Category.assoc]
    erw [Scheme.ΓSpecIso_naturality]
  exact congrArg (fun ψ => ψ.hom f) e4

theorem evAt_comp (R : Type) [CommRing R] (X Y : Scheme.{0}) (b : Sp R ⟶ X) (g : X ⟶ Y) (U : X.Opens) (V : Y.Opens)
    (h : ⊤ ≤ b ⁻¹ᵁ U) (h' : ⊤ ≤ (b ≫ g) ⁻¹ᵁ V) (e : U ≤ g ⁻¹ᵁ V) (f : Γ(Y, V)) :
    evAt (b ≫ g) h' f = evAt b h (g.appLE V U e f) := by
  have e2 := Scheme.Hom.appLE_comp_appLE b g V U ⊤ e h
  have e4 : (b ≫ g).appLE V ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom =
      g.appLE V U e ≫ b.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom := by
    rw [← Category.assoc, e2]
  exact congrArg (fun ψ => ψ.hom f) e4

theorem evAt_res (R : Type) [CommRing R] (X : Scheme.{0}) (b : Sp R ⟶ X) (U U' : X.Opens) (e : U' ≤ U)
    (h : ⊤ ≤ b ⁻¹ᵁ U) (h' : ⊤ ≤ b ⁻¹ᵁ U') (f : Γ(X, U)) :
    evAt b h' (X.presheaf.map (homOfLE e).op f) = evAt b h f := by
  have e2 := Scheme.Hom.map_appLE b h' (homOfLE e).op
  have e4 : X.presheaf.map (homOfLE e).op ≫ b.appLE U' ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom =
      b.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom := by
    rw [← Category.assoc, e2]
  exact congrArg (fun ψ => ψ.hom f) e4

theorem top_le_iff_closedPoint_mem (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) (b : Sp R ⟶ X)
    (U : X.Opens) : ⊤ ≤ b ⁻¹ᵁ U ↔ b (IsLocalRing.closedPoint R) ∈ U := by
  refine ⟨fun h => h (Set.mem_univ _), fun hb q _ => ?_⟩
  exact ((IsLocalRing.specializes_closedPoint (q : PrimeSpectrum R)).map b.continuous).mem_open U.2 hb

theorem eq_of_evAt_eq (R : Type) [CommRing R] (X : Scheme.{0}) (b b' : Sp R ⟶ X) (U : X.Opens) (hU : IsAffineOpen U)
    (h : ⊤ ≤ b ⁻¹ᵁ U) (h' : ⊤ ≤ b' ⁻¹ᵁ U) (he : evAt b h = evAt b' h') : b = b' := by
  have k0 : b.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom =
      b'.appLE U ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom := by
    rw [← evAt_eq_comp, ← evAt_eq_comp, he]
  have k : b.appLE U ⊤ h = b'.appLE U ⊤ h' := (cancel_mono _).1 k0
  have e1 := IsAffineOpen.SpecMap_appLE_fromSpec b hU (isAffineOpen_top (Sp R)) h
  have e2 := IsAffineOpen.SpecMap_appLE_fromSpec b' hU (isAffineOpen_top (Sp R)) h'
  rw [k] at e1
  have e3 := e1.symm.trans e2
  rw [IsAffineOpen.fromSpec_top] at e3
  exact (cancel_epi _).1 e3

theorem exists_evAt_eq (R : Type) [CommRing R] (X : Scheme.{0}) (U : X.Opens) (hU : IsAffineOpen U)
    (φ : Γ(X, U) →+* R) : ∃ (b : Sp R ⟶ X) (h : ⊤ ≤ b ⁻¹ᵁ U), evAt b h = φ := by
  have hfs : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := by rw [hU.fromSpec_preimage_self]
  have h : ⊤ ≤ (Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec : Sp R ⟶ X) ⁻¹ᵁ U :=
    fun _ _ => hU.range_fromSpec.subset ⟨_, rfl⟩
  refine ⟨Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec, h, ?_⟩
  have e1 : hU.fromSpec.appLE U ⊤ hfs = (Scheme.ΓSpecIso Γ(X, U)).inv := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    convert Category.comp_id _
    exact (Spec Γ(X, U)).presheaf.map_id _
  have e2 := Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom φ)) hU.fromSpec U ⊤ ⊤ hfs le_rfl
  have e3 : (Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ le_rfl = (Spec.map (CommRingCat.ofHom φ)).appTop :=
    (Scheme.Hom.app_eq_appLE _).symm
  have e4 : CommRingCat.ofHom (evAt (Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec : Sp R ⟶ X) h) =
      CommRingCat.ofHom φ := by
    rw [evAt_eq_comp, ← e2, e1, e3, Category.assoc]
    erw [Scheme.ΓSpecIso_naturality]
    exact (Scheme.ΓSpecIso Γ(X, U)).inv_hom_id_assoc _
  exact congrArg CommRingCat.Hom.hom e4

theorem evAt_fromSpecStalk' (R : Type) [CommRing R] (X : Scheme.{0}) (p : X) (φ : X.presheaf.stalk p →+* R)
    (U : X.Opens) (hp : p ∈ U) :
    ∃ h : ⊤ ≤ (Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk p : Sp R ⟶ X) ⁻¹ᵁ U,
      ∀ f, evAt (Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk p : Sp R ⟶ X) h f =
        φ (X.presheaf.germ U p hp f) := by
  have h0 : ⊤ ≤ X.fromSpecStalk p ⁻¹ᵁ U := fun q _ =>
    ((IsLocalRing.specializes_closedPoint (q : PrimeSpectrum _)).map (X.fromSpecStalk p).continuous).mem_open U.2
      (by rw [Scheme.fromSpecStalk_closedPoint]; exact hp)
  refine ⟨fun q _ => h0 (Set.mem_univ _), fun s => ?_⟩
  have e1 : (X.fromSpecStalk p).appLE U ⊤ h0 = X.presheaf.germ U p hp ≫ (Scheme.ΓSpecIso _).inv := by
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hp, Category.assoc, Category.assoc, ← Functor.map_comp]
    exact congrArg (_ ≫ ·) ((congrArg (_ ≫ ·) ((Spec (X.presheaf.stalk p)).presheaf.map_id _)).trans (Category.comp_id _))
  have e2 := Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom φ)) (X.fromSpecStalk p) U ⊤ ⊤ h0 le_rfl
  have e3 : (Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ le_rfl = (Spec.map (CommRingCat.ofHom φ)).appTop :=
    (Scheme.Hom.app_eq_appLE _).symm
  have e4 : (Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk p).appLE U ⊤ (fun q _ => h0 (Set.mem_univ _)) ≫
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom = X.presheaf.germ U p hp ≫ CommRingCat.ofHom φ := by
    rw [← e2, e1, e3, Category.assoc, Category.assoc]
    erw [Scheme.ΓSpecIso_naturality]
    exact congrArg (_ ≫ ·) ((Scheme.ΓSpecIso (X.presheaf.stalk p)).inv_hom_id_assoc _)
  exact congrArg (fun ψ => ψ.hom s) e4

theorem evAt_calculus : (∀ (R R' : Type) [CommRing R] [CommRing R'] (X : Scheme.{0}) (φ : R →+* R') (b : Sp R ⟶ X) (U : X.Opens) (h : ⊤ ≤ b ⁻¹ᵁ U) (h' : ⊤ ≤ (spMap φ ≫ b) ⁻¹ᵁ U) (f : Γ(X, U)), evAt (spMap φ ≫ b) h' f = φ (evAt b h f)) ∧ (∀ (R : Type) [CommRing R] (X Y : Scheme.{0}) (b : Sp R ⟶ X) (g : X ⟶ Y) (U : X.Opens) (V : Y.Opens) (h : ⊤ ≤ b ⁻¹ᵁ U) (h' : ⊤ ≤ (b ≫ g) ⁻¹ᵁ V) (e : U ≤ g ⁻¹ᵁ V) (f : Γ(Y, V)), evAt (b ≫ g) h' f = evAt b h (g.appLE V U e f)) ∧ (∀ (R : Type) [CommRing R] (X : Scheme.{0}) (b : Sp R ⟶ X) (U U' : X.Opens) (e : U' ≤ U) (h : ⊤ ≤ b ⁻¹ᵁ U) (h' : ⊤ ≤ b ⁻¹ᵁ U') (f : Γ(X, U)), evAt b h' (X.presheaf.map (homOfLE e).op f) = evAt b h f) ∧ (∀ (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) (b : Sp R ⟶ X) (U : X.Opens), ⊤ ≤ b ⁻¹ᵁ U ↔ b (IsLocalRing.closedPoint R) ∈ U) ∧ (∀ (R : Type) [CommRing R] (X : Scheme.{0}) (b b' : Sp R ⟶ X) (U : X.Opens), IsAffineOpen U → ∀ (h : ⊤ ≤ b ⁻¹ᵁ U) (h' : ⊤ ≤ b' ⁻¹ᵁ U), evAt b h = evAt b' h' → b = b') ∧ (∀ (R : Type) [CommRing R] (X : Scheme.{0}) (U : X.Opens), IsAffineOpen U → ∀ φ : Γ(X, U) →+* R, ∃ (b : Sp R ⟶ X) (h : ⊤ ≤ b ⁻¹ᵁ U), evAt b h = φ) ∧ (∀ (R : Type) [CommRing R] (X : Scheme.{0}) (p : X) (φ : X.presheaf.stalk p →+* R) (U : X.Opens) (hp : p ∈ U), ∃ h : ⊤ ≤ (Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk p : Sp R ⟶ X) ⁻¹ᵁ U, ∀ f, evAt (Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk p : Sp R ⟶ X) h f = φ (X.presheaf.germ U p hp f)) :=
  ⟨evAt_spMap_comp, evAt_comp, evAt_res, top_le_iff_closedPoint_mem, eq_of_evAt_eq, exists_evAt_eq,
    evAt_fromSpecStalk'⟩

end GlobalTheory.Nef
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem injective_ringHom_genericStalk_integralScheme (C : Scheme.{0}) [IsIntegral C] (q : C) (hq : q = genericPoint C)
    {A : Type} [CommRing A] [Nontrivial A] (φ : C.presheaf.stalk q →+* A) : Function.Injective φ := by
  subst hq
  exact RingHom.injective (φ : C.functionField →+* A)

theorem exists_fraction_genericStalk_germ_affineOpen (C : Scheme.{0}) [IsIntegral C] (V : C.Opens) (hV : IsAffineOpen V)
    (q : C) (hq : q = genericPoint C) (hqV : q ∈ V) (s : C.presheaf.stalk q) :
    ∃ a b : Γ(C, V), b ≠ 0 ∧ s * C.presheaf.germ V q hqV b = C.presheaf.germ V q hqV a := by
  subst hq
  haveI : Nonempty V := ⟨⟨_, hqV⟩⟩
  haveI := functionField_isFractionRing_of_isAffineOpen (X := C) V hV
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.mk'_surjective (S := C.functionField) (nonZeroDivisors Γ(C, V)) s
  refine ⟨a, b, nonZeroDivisors.ne_zero b.2, ?_⟩
  have := IsLocalization.mk'_spec (S := C.functionField) a b
  rw [← hab]
  exact this

theorem germ_appLE_eq_stalkMap_germ_specField {K : Type} [Field K] (C : Scheme.{0}) (x : Sp K ⟶ C) (V : C.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V)
    (p : Sp K) (hp : x p ∈ V) (c : Γ(C, V)) :
    (Sp K).presheaf.germ ⊤ p (by simp) (x.appLE V ⊤ h c) = x.stalkMap p (C.presheaf.germ V (x p) hp c) := by
  rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appLE]
  simp

end GlobalTheory.Nef

namespace GlobalTheory.Nef

theorem isGen_evAt_frac : ∀ (K : Type) [Field K] (C : Scheme.{0}) [IsIntegral C] (x : Sp K ⟶ C), IsGen x →
    ∀ V : C.Opens, (V : Set C).Nonempty → ∃ h : ⊤ ≤ x ⁻¹ᵁ V, Function.Injective (evAt x h) ∧
      (IsAffineOpen V → ∀ z : K, ∃ a b : Γ(C, V), b ≠ 0 ∧ z * evAt x h b = evAt x h a) := by
  intro K _ C _ x hx V hV
  haveI : IsDominant x := hx.1
  haveI : IsPreimmersion x := hx.2
  have hsub : ∀ p q : Sp K, p = q := fun p q => Subsingleton.elim (α := PrimeSpectrum K) p q
  have hgen : ∀ p : Sp K, x p = genericPoint C := by
    intro p
    apply ((genericPoint_spec C).eq _).symm
    rw [isGenericPoint_def]
    have hr : Set.range x = {x p} := by
      ext y
      constructor
      · rintro ⟨q, rfl⟩
        rw [hsub q p]
        rfl
      · rintro rfl
        exact ⟨p, rfl⟩
    rw [← hr]
    exact x.denseRange.closure_range
  have hmem : genericPoint C ∈ V :=
    ((genericPoint_spec C).mem_open_set_iff V.isOpen).mpr (by simpa using hV)
  have h : ⊤ ≤ x ⁻¹ᵁ V := by
    intro p _
    show x p ∈ V
    rw [hgen p]
    exact hmem
  obtain ⟨p⟩ : Nonempty (Sp K) := ⟨(⊥ : PrimeSpectrum K)⟩
  have hp : x p ∈ V := by rw [hgen p]; exact hmem
  refine ⟨h, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro c hc
    have h1 : x.appLE V ⊤ h c = 0 := by
      have := congrArg (Scheme.ΓSpecIso (.of K)).inv.hom hc
      simpa [evAt] using this
    have h2 := germ_appLE_eq_stalkMap_germ_specField C x V h p hp c
    rw [h1, map_zero] at h2
    have h3 : C.presheaf.germ V (x p) hp c = 0 :=
      injective_ringHom_genericStalk_integralScheme C (x p) (hgen p) (x.stalkMap p).hom (by rw [← h2, map_zero])
    exact germ_injective_of_isIntegral (X := C) (x p) hp (by rw [h3, map_zero])
  · intro hA z
    obtain ⟨s, hs⟩ := x.stalkMap_surjective p
      ((Sp K).presheaf.germ ⊤ p (by simp) ((Scheme.ΓSpecIso (.of K)).inv.hom z))
    obtain ⟨a, b, hb, hab⟩ := exists_fraction_genericStalk_germ_affineOpen C V hA (x p) (hgen p) hp s
    refine ⟨a, b, hb, ?_⟩
    have e := congrArg (x.stalkMap p).hom hab
    rw [map_mul, hs, ← germ_appLE_eq_stalkMap_germ_specField C x V h p hp, ← germ_appLE_eq_stalkMap_germ_specField C x V h p hp, ← map_mul] at e
    have e2 := germ_injective_of_isIntegral (X := Sp K) p (by simp) e
    have e3 := congrArg (Scheme.ΓSpecIso (.of K)).hom.hom e2
    simpa [evAt] using e3

end GlobalTheory.Nef
end
