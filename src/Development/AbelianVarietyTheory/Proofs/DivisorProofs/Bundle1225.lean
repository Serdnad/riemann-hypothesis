module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1168
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1170
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1132
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1169
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTwoPointFunctionMultiplesNaturalCharPStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1151
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
public import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight
import Mathlib.Tactic.Basify
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical

@[expose] public section

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem convMul_includeLeft_includeRight {R : Type} [CommRing R] {D : Type} [CommRing D] [Bialgebra R D] :
    (toConv (Algebra.TensorProduct.includeLeft : D →ₐ[R] D ⊗[R] D) *
      toConv (Algebra.TensorProduct.includeRight : D →ₐ[R] D ⊗[R] D)).ofConv = Bialgebra.comulAlgHom R D := by
  ext a
  rw [AlgHom.convMul_apply]
  simp only [Bialgebra.comulAlgHom_apply]
  induction (Coalgebra.comul (R := R) a) with
  | add u v hu hv => simp only [map_add (f := _), hu, hv]
  | tmul u v => simp

theorem cobOne_algebraMap {R : Type} [CommRing R] {D : Type} [CommRing D] [Bialgebra R D] (r : R) :
    cobOne R D (algebraMap R D r) = -algebraMap R (D ⊗[R] D) r := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, cobOne_apply, Algebra.algebraMap_eq_smul_one]
  simp [Algebra.TensorProduct.one_def]

end GlobalTheory.PtExt

namespace GlobalTheory.PtExt

theorem isCan_unique (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R)
    (t : G.TorsionTower A) (c : primDR A) (hA : IsAbelianScheme A) (x x' : G.RigExt)
    (hx : IsCan t c x) (hx' : IsCan t c x') : x = x' := by
  obtain ⟨d, z, w, hz, hw, rfl⟩ := hx
  obtain ⟨d', z', w', hz', hw', rfl⟩ := hx'
  obtain ⟨k, hk⟩ := H1.mk_eq_mk.1 (d.cl.trans d'.cl.symm)
  let κ : Fn0 A := fun D _ _ y ↦ k (trivAt y)
  have hκ : ∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D')
      (y : Pt A D), fv d.f D D' φ y - fv d'.f D D' φ y = κ D' (spOver φ ≫ y) - φ (κ D y) := by
    intro D _ _ D' _ _ φ y
    have := congrFun (congrFun (congrFun hk (trivAt y)) (trivAt (spOver φ ≫ y))) (trivMap φ y)
    exact this.symm
  let e : Fn0 (A ⊗ A) := fun D _ _ u ↦
    d.g D (u ≫ fst A A) (u ≫ snd A A) - d'.g D (u ≫ fst A A) (u ≫ snd A A) -
      (κ D ((u ≫ fst A A) * (u ≫ snd A A)) - κ D (u ≫ fst A A) - κ D (u ≫ snd A A))
  have hcob : IsCob (whole (A ⊗ A)) (Fn1.zero _) e := by
    intro D _ _ D' _ _ φ u _
    have h1 := d.add D D' φ (u ≫ fst A A) (u ≫ snd A A)
    have h2 := d'.add D D' φ (u ≫ fst A A) (u ≫ snd A A)
    have h3 := hκ D D' φ ((u ≫ fst A A) * (u ≫ snd A A))
    have h4 := hκ D D' φ (u ≫ fst A A)
    have h5 := hκ D D' φ (u ≫ snd A A)
    rw [comp_mul] at h3
    simp only [e, Fn1.zero, Category.assoc, map_sub]
    linear_combination -h1 + h2 - h3 + h4 + h5
  obtain ⟨r, hr⟩ := GlobalTheory.T.natural_pointwiseCochain_const_of_globalSections_base R (A ⊗ A) Unit (whole _) (by simp [whole]) (globalFns_holds _ (A ⊗ A)
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA)).2 e hcob
  have he : ∀ (D : Type) [CommRing D] [Algebra R D] (y y' : Pt A D),
      d.g D y y' - d'.g D y y' - (κ D (y * y') - κ D y - κ D y') = algebraMap R D r := by
    intro D _ _ y y'
    have := hr D (lift y y') (sm_whole _)
    simpa [e] using this
  let b : ∀ n, G.A n := fun n ↦ d.h n - d'.h n - κ _ (t.y n) + algebraMap R (G.A n) r
  have hb : b ∈ G.funs := by
    intro n
    have h1 := d.res n
    have h2 := d'.res n
    have h3 := hκ _ _ (G.res n : G.A (n + 1) →ₐ[R] G.A n) (t.y (n + 1))
    rw [t.res] at h3
    have h4 : (G.res n : G.A (n + 1) →ₐ[R] G.A n) (algebraMap R _ r) = algebraMap R _ r := AlgHom.commutes _ _
    change (G.res n : G.A (n + 1) →ₐ[R] G.A n) (b (n + 1)) = b n
    have e1 : ∀ a, (G.res n : G.A (n + 1) →ₐ[R] G.A n) a = G.res n a := fun _ ↦ rfl
    simp only [b, map_sub, map_add (f := _), e1] at h3 h4 ⊢
    linear_combination h1 - h2 - h3 + h4
  refine (Submodule.Quotient.eq _).2 ⟨-⟨b, hb⟩, Prod.ext (Subtype.ext (funext fun n ↦ ?_))
    (Subtype.ext (funext fun n ↦ ?_))⟩
  · change cobOne R _ (-b n) = z.1 n - z'.1 n
    rw [hz, hz']
    have hXY := t.mul n (G.A n ⊗[R] G.A n) (toConv Algebra.TensorProduct.includeLeft)
      (toConv Algebra.TensorProduct.includeRight)
    rw [convMul_includeLeft_includeRight] at hXY
    have h0 := he _ (spOver (Algebra.TensorProduct.includeLeft : G.A n →ₐ[R] G.A n ⊗[R] G.A n) ≫ t.y n)
      (spOver (Algebra.TensorProduct.includeRight : G.A n →ₐ[R] G.A n ⊗[R] G.A n) ≫ t.y n)
    rw [← hXY] at h0
    have hc := hκ _ _ (Bialgebra.comulAlgHom R (G.A n)) (t.y n)
    have hL := hκ _ _ (Algebra.TensorProduct.includeLeft : G.A n →ₐ[R] G.A n ⊗[R] G.A n) (t.y n)
    have hR := hκ _ _ (Algebra.TensorProduct.includeRight : G.A n →ₐ[R] G.A n ⊗[R] G.A n) (t.y n)
    have hk1 := cobOne_apply (O := R) (κ _ (t.y n))
    have hk2 := cobOne_algebraMap (R := R) (D := G.A n) r
    simp only [Bialgebra.comulAlgHom_apply, Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.includeRight_apply] at hc hL hR
    simp only [Dat.coc, b, map_neg, map_add (f := _), map_sub]
    linear_combination hk1 - hk2 - h0 + hc - hL - hR
  · change dUnit (R := R) (-b n) = w.1 n - w'.1 n
    rw [hw, hw']
    have h0 := GlobalTheory.T.cotVal_sub_eq_dUnit_of_d0_eq_sub R A (G.A n) (t.y n) d.f d'.f k hk
    have h1 : dUnit (R := R) (algebraMap R (G.A n) r) = 0 := AugCot.d_algebraMap _ r
    simp only [Dat.om, b]
    change AugCot.d _ _ = _
    simp only [map_neg, map_add (f := _), map_sub]
    change -(dUnit (R := R) _ - dUnit (R := R) _ - dUnit (R := R) _ + dUnit (R := R) _) = _
    rw [h1]
    change _ = cotVal d.f (t.y n) - dUnit (R := R) _ - (cotVal d'.f (t.y n) - dUnit (R := R) _)
    rw [show cotVal d.f (t.y n) - dUnit (R := R) (d.h n) - (cotVal d'.f (t.y n) - dUnit (R := R) (d'.h n)) =
      (cotVal d.f (t.y n) - cotVal d'.f (t.y n)) - dUnit (R := R) (d.h n) + dUnit (R := R) (d'.h n) by abel, h0]
    abel

end GlobalTheory.PtExt
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.PtExt

theorem isSymCoc_of_isAdd : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A →
    ∀ (f : Fn1 A) (g : Fn2 A), IsAdd f g → IsSymCoc g := by
  intro R _ A _ hA f g hfg
  have hc : IsCommMonObj A := hA.comm
  unfold IsSymCoc
  unfold IsAdd at hfg
  intro D _ _
  constructor
  · let k : Fn0 (A ⊗ A) := fun E _ _ w ↦
      g E (w ≫ fst A A) (w ≫ snd A A) - g E (w ≫ snd A A) (w ≫ fst A A)
    have hk : IsCob (whole (A ⊗ A)) (Fn1.zero (A ⊗ A)) k := by
      unfold IsCob
      intro E _ _ E' _ _ φ w _
      have h1 := hfg E E' φ (w ≫ fst A A) (w ≫ snd A A)
      have h2 := hfg E E' φ (w ≫ snd A A) (w ≫ fst A A)
      rw [mul_comm (w ≫ snd A A) (w ≫ fst A A)] at h2
      simp only [k, Fn1.zero, Category.assoc, map_sub]
      linear_combination h2 - h1
    obtain ⟨r, hr⟩ := GlobalTheory.T.natural_pointwiseCochain_const_of_globalSections_base R (A ⊗ A) Unit (whole (A ⊗ A)) (by simp [whole])
      (GlobalTheory.globalFns_holds (Sp R) (A ⊗ A)
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA)).2 k hk
    intro x y
    have e1 := hr D (lift x y) (sm_whole _)
    have e0 := hr D (lift 1 1) (sm_whole _)
    simp only [k, lift_fst, lift_snd, sub_self] at e0 e1
    exact sub_eq_zero.mp (e1.trans e0.symm)
  · let k : Fn0 (A ⊗ (A ⊗ A)) := fun E _ _ w ↦
      g E (w ≫ snd _ _ ≫ fst A A) (w ≫ snd _ _ ≫ snd A A)
        - g E ((w ≫ fst _ _) * (w ≫ snd _ _ ≫ fst A A)) (w ≫ snd _ _ ≫ snd A A)
        + g E (w ≫ fst _ _) ((w ≫ snd _ _ ≫ fst A A) * (w ≫ snd _ _ ≫ snd A A))
        - g E (w ≫ fst _ _) (w ≫ snd _ _ ≫ fst A A)
    have hk : IsCob (whole (A ⊗ (A ⊗ A))) (Fn1.zero _) k := by
      unfold IsCob
      intro E _ _ E' _ _ φ w _
      have h1 := hfg E E' φ (w ≫ snd _ _ ≫ fst A A) (w ≫ snd _ _ ≫ snd A A)
      have h2 := hfg E E' φ ((w ≫ fst _ _) * (w ≫ snd _ _ ≫ fst A A)) (w ≫ snd _ _ ≫ snd A A)
      have h3 := hfg E E' φ (w ≫ fst _ _) ((w ≫ snd _ _ ≫ fst A A) * (w ≫ snd _ _ ≫ snd A A))
      have h4 := hfg E E' φ (w ≫ fst _ _) (w ≫ snd _ _ ≫ fst A A)
      rw [_root_.mul_assoc] at h2
      simp only [MonObj.comp_mul] at h2 h3
      simp only [k, Fn1.zero, Category.assoc, map_sub, map_add (f := _), MonObj.comp_mul]
      linear_combination h2 - h1 - h3 + h4
    obtain ⟨r, hr⟩ := GlobalTheory.T.natural_pointwiseCochain_const_of_globalSections_base R (A ⊗ (A ⊗ A)) Unit (whole _) (by simp [whole])
      (GlobalTheory.globalFns_holds (Sp R) (A ⊗ (A ⊗ A))
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor A (A ⊗ A) hA
          (ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA))).2 k hk
    intro x y z
    have e1 := hr D (lift x (lift y z)) (sm_whole _)
    have e0 := hr D (lift 1 (lift 1 1)) (sm_whole _)
    simp only [k, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc, _root_.mul_one, sub_self, add_sub_cancel_right,
      sub_add_cancel] at e0 e1
    rw [← e0] at e1
    exact e1

end GlobalTheory.PtExt
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.PtExt

variable {R : Type} [CommRing R]

theorem snd_epsHom {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D')
    (z : DualNumber D) : (epsHom φ z).snd = φ z.snd := by
  simp only [epsHom, DualNumber.lift_apply_apply, AlgHom.comp_apply,
    TrivSqZeroExt.inlAlgHom_apply, TrivSqZeroExt.snd_add, DualNumber.snd_mul,
    TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, DualNumber.fst_eps, DualNumber.snd_eps,
    _root_.mul_one, mul_zero, add_zero, zero_add]

theorem epsHom_comp_inl {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') :
    (epsHom φ).comp (TrivSqZeroExt.inlAlgHom R D D) = (TrivSqZeroExt.inlAlgHom R D' D').comp φ := by
  exact DualNumber.lift_comp_inlHom _

theorem epsHom_comp_epsMap {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') :
    (epsHom φ).comp (EpsWeil.epsMap R D) = EpsWeil.epsMap R D' := by
  apply DualNumber.algHom_ext
  simp only [AlgHom.comp_apply, epsHom, EpsWeil.epsMap, DualNumber.lift_apply_eps]

theorem ptV_eq {A B : Over (Sp R)} [GrpObj A] [GrpObj B] (v : epsR R ⟶ B) {D : Type} [CommRing D] [Algebra R D]
    (x : Pt A D) : ptV v x =
      (spOver (TrivSqZeroExt.inlAlgHom R D D) ≫ pt0 B x : Pt (A ⊗ B) (DualNumber D)) *
      (spOver (EpsWeil.epsMap R D) ≫ CartesianMonoidalCategory.lift 1 v) := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp [ptV, pt0, MonObj.mul_comp, comp_lift, MonObj.comp_one]

theorem specOverOfAlgHom_comp_pointWithZeroSecondCoord {A B : Over (Sp R)} [GrpObj A] [GrpObj B] {D D' : Type} [CommRing D] [Algebra R D] [CommRing D']
    [Algebra R D'] (φ : D →ₐ[R] D') (x : Pt A D) :
    (spOver φ ≫ pt0 B x : Pt (A ⊗ B) D') = pt0 B (spOver φ ≫ x : Pt A D') := by
  simp [pt0, comp_lift]

theorem cohom_sndPull_zero : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B]
    (f : Z1 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _))), CatCoh.H1.mk _ f ∈ primDR (A ⊗ B) →
    ∀ v : epsR R ⟶ B, Cohom (whole A) (sndPull (fv f) v) (Fn1.zero A) := by
  intro R _ A B _ _ f hf v
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_additiveStructure_of_primitiveDeRhamClass R (A ⊗ B) f hf
  have hc := (fv_isCoc_and_ev_eq R (A ⊗ B) f).1
  let V1 : Pt (A ⊗ B) (DualNumber R) := CartesianMonoidalCategory.lift 1 v
  refine ⟨fun D _ _ x ↦ (g (DualNumber D) (spOver (TrivSqZeroExt.inlAlgHom R D D) ≫ pt0 B x)
      (spOver (EpsWeil.epsMap R D) ≫ V1) +
      fv f D (DualNumber D) (TrivSqZeroExt.inlAlgHom R D D) (pt0 B x) +
      fv f (DualNumber R) (DualNumber D) (EpsWeil.epsMap R D) V1).snd, ?_⟩
  intro D _ _ D' _ _ φ x _
  have e1 := hg (DualNumber D) (DualNumber D') (epsHom φ) (spOver (TrivSqZeroExt.inlAlgHom R D D) ≫ pt0 B x)
    (spOver (EpsWeil.epsMap R D) ≫ V1)
  rw [← ptV_eq] at e1
  have hX : (spOver (epsHom φ) ≫ spOver (TrivSqZeroExt.inlAlgHom R D D) ≫ pt0 B x :
      Pt (A ⊗ B) (DualNumber D')) =
      spOver (TrivSqZeroExt.inlAlgHom R D' D') ≫ pt0 B (spOver φ ≫ x : Pt A D') := by
    rw [← Category.assoc, spOver_comp, epsHom_comp_inl, ← spOver_comp, Category.assoc, specOverOfAlgHom_comp_pointWithZeroSecondCoord]
  have hV : (spOver (epsHom φ) ≫ spOver (EpsWeil.epsMap R D) ≫ V1 :
      Pt (A ⊗ B) (DualNumber D')) = spOver (EpsWeil.epsMap R D') ≫ V1 := by
    rw [← Category.assoc, spOver_comp, epsHom_comp_epsMap]
  rw [hX, hV] at e1
  have c1 := hc D (DualNumber D) (DualNumber D') (TrivSqZeroExt.inlAlgHom R D D) (epsHom φ) (pt0 B x)
    (sm_whole _)
  have c2 := hc D D' (DualNumber D') φ (TrivSqZeroExt.inlAlgHom R D' D') (pt0 B x) (sm_whole _)
  rw [epsHom_comp_inl, c2, specOverOfAlgHom_comp_pointWithZeroSecondCoord] at c1
  have c3 := hc (DualNumber R) (DualNumber D) (DualNumber D') (EpsWeil.epsMap R D) (epsHom φ) V1 (sm_whole _)
  rw [epsHom_comp_epsMap] at c3
  have s1 := congrArg TrivSqZeroExt.snd e1
  have s2 := congrArg TrivSqZeroExt.snd c1
  have s3 := congrArg TrivSqZeroExt.snd c3
  simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_sub, snd_epsHom,
    TrivSqZeroExt.inlAlgHom_apply, TrivSqZeroExt.snd_inl, zero_add] at s1 s2 s3
  simp only [Fn1.add, Fn1.neg, Fn1.zero, sndPull, neg_zero, add_zero, TrivSqZeroExt.snd_add, map_add (f := _)]
  linear_combination -s1 - s2 - s3

end GlobalTheory.PtExt
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt.Descent

variable {R : Type} [CommRing R]

theorem descend {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (ψ : D →ₐ[R] D')
    (hψ : (ψ : D →+* D').FaithfullyFlat) (s : D')
    (hs : ∀ (E : Type) [CommRing E] [Algebra R E] (α β : D' →ₐ[R] E), α.comp ψ = β.comp ψ → α s = β s) :
    ∃ k, ψ k = s := by
  letI : Algebra D D' := (ψ : D →+* D').toAlgebra
  haveI : Module.FaithfullyFlat D D' := hψ
  haveI : IsScalarTower R D D' := IsScalarTower.of_algebraMap_eq fun r ↦ (ψ.commutes r).symm
  refine (Algebra.IsEffective.of_faithfullyFlat D D' s).1 ?_
  have h := hs (D' ⊗[D] D') ((Algebra.TensorProduct.includeLeft : D' →ₐ[D] D' ⊗[D] D').restrictScalars R)
    ((Algebra.TensorProduct.includeRight : D' →ₐ[D] D' ⊗[D] D').restrictScalars R) (by
      ext d
      exact ((Algebra.TensorProduct.includeLeft : D' →ₐ[D] D' ⊗[D] D').commutes d).trans
        ((Algebra.TensorProduct.includeRight : D' →ₐ[D] D' ⊗[D] D').commutes d).symm)
  simpa [sub_eq_zero] using h

theorem exists_square {D D' D₂ : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] [CommRing D₂]
    [Algebra R D₂] (ψ : D →ₐ[R] D') (hψ : (ψ : D →+* D').FaithfullyFlat) (ψ₂ : D →ₐ[R] D₂) :
    ∃ (E : Type) (_ : CommRing E) (_ : Algebra R E) (α : D' →ₐ[R] E) (β : D₂ →ₐ[R] E),
      α.comp ψ = β.comp ψ₂ ∧ Function.Injective β := by
  letI : Algebra D D' := (ψ : D →+* D').toAlgebra
  haveI : Module.FaithfullyFlat D D' := hψ
  haveI : IsScalarTower R D D' := IsScalarTower.of_algebraMap_eq fun r ↦ (ψ.commutes r).symm
  letI : Algebra D D₂ := (ψ₂ : D →+* D₂).toAlgebra
  haveI : IsScalarTower R D D₂ := IsScalarTower.of_algebraMap_eq fun r ↦ (ψ₂.commutes r).symm
  refine ⟨D₂ ⊗[D] D', inferInstance, inferInstance,
    (Algebra.TensorProduct.includeRight : D' →ₐ[D] D₂ ⊗[D] D').restrictScalars R,
    (Algebra.TensorProduct.includeLeft : D₂ →ₐ[D] D₂ ⊗[D] D').restrictScalars R, ?_, ?_⟩
  · ext d
    exact ((Algebra.TensorProduct.includeRight : D' →ₐ[D] D₂ ⊗[D] D').commutes d).trans
        ((Algebra.TensorProduct.includeLeft : D₂ →ₐ[D] D₂ ⊗[D] D').commutes d).symm
  · exact FaithfulSMul.algebraMap_injective D₂ (D₂ ⊗[D] D')

variable {A : Over (Sp R)} [GrpObj A]

def sig (p : ℕ) (f : Fn1 A) (g : Fn2 A) {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D']
    (ψ : D →ₐ[R] D') (x : Pt A D) (z : Pt A D') : D' :=
  PtExt.chi p g D' z + f R D' (Algebra.ofId R D') (1 : Pt A R) - f D D' ψ x

theorem sig_nat {p : ℕ} (hp : (p : R) = 0) {f : Fn1 A} {g : Fn2 A} (hf : IsCoc (whole A) f) (hfg : IsAdd f g)
    {D D' D'' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] [CommRing D''] [Algebra R D'']
    (ψ : D →ₐ[R] D') (θ : D' →ₐ[R] D'') (x : Pt A D) (z : Pt A D') (hz : (z ^ p : Pt A D') = spOver ψ ≫ x) :
    θ (sig p f g ψ x z) = sig p f g (θ.comp ψ) x (spOver θ ≫ z) := by
  have h1 := GlobalTheory.T.sumTwoPointFunction_multiples_natural_charP p R hp A f g hfg D' D'' θ z
  have h2 := hf D D' D'' ψ θ x (sm_whole _)
  have h3 := hf R D' D'' (Algebra.ofId R D') θ (1 : Pt A R) (sm_whole _)
  have e : θ.comp (Algebra.ofId R D') = Algebra.ofId R D'' := Subsingleton.elim _ _
  rw [e, MonObj.comp_one] at h3
  rw [hz] at h1
  simp only [sig, map_add θ, map_sub θ]
  linear_combination -h1 + h2 - h3

theorem chi_indep [IsCommMonObj A] {p : ℕ} (hp : (p : R) = 0) {g : Fn2 A} (hg : IsSymCoc g)
    (h0 : ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), x ^ p = 1 → PtExt.chi p g D x = 0)
    {D : Type} [CommRing D] [Algebra R D] (z z' : Pt A D) (h : z ^ p = z' ^ p) :
    PtExt.chi p g D z = PtExt.chi p g D z' := by
  obtain ⟨t, rfl⟩ : ∃ t, z = z' * t := ⟨z'⁻¹ * z, by simp⟩
  have ht : t ^ p = 1 := by rwa [mul_pow, mul_eq_left] at h
  have h1 := GlobalTheory.T.symmetric_two_cocycle_sum_pow_mul (Pt A D) D (g D) (hg D).1 (hg D).2 p z' t
  have h2 := (hg D).2 (z' ^ p) 1 1
  have h3 := h0 D t ht
  have h4 : (p : D) = 0 := by rw [← map_natCast (algebraMap R D), hp, map_zero]
  rw [ht, nsmul_eq_mul, h4] at h1
  simp only [_root_.mul_one] at h2
  simp only [PtExt.chi] at h3 ⊢
  linear_combination h1 - h2 + h3

theorem pow_comp {p : ℕ} {D D' D'' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] [CommRing D'']
    [Algebra R D''] (ψ : D →ₐ[R] D') (θ : D' →ₐ[R] D'') (x : Pt A D) (z : Pt A D')
    (hz : (z ^ p : Pt A D') = spOver ψ ≫ x) :
    ((spOver θ ≫ z) ^ p : Pt A D'') = spOver (θ.comp ψ) ≫ x := by
  rw [← MonObj.comp_pow, hz, ← Category.assoc, spOver_comp]

theorem exists_isCob (p : ℕ) (R : Type) [CommRing R] (hp : (p : R) = 0) (A : Over (Sp R)) [GrpObj A]
    [IsCommMonObj A] (f : Fn1 A) (g : Fn2 A) (hf : IsCoc (whole A) f) (hfg : IsAdd f g) (hg : IsSymCoc g)
    (h0 : ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), x ^ p = 1 → PtExt.chi p g D x = 0)
    (hr : ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), ∃ (D' : Type) (_ : CommRing D') (_ : Algebra R D')
      (ψ : D →ₐ[R] D') (z : Pt A D'), (ψ : D →+* D').FaithfullyFlat ∧ (z ^ p : Pt A D') = spOver ψ ≫ x) :
    ∃ k : Fn0 A, IsCob (whole A) f k := by
  have key : ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), ∃ k : D,
      ∀ (D₂ : Type) [CommRing D₂] [Algebra R D₂] (ψ₂ : D →ₐ[R] D₂) (z₂ : Pt A D₂),
        (z₂ ^ p : Pt A D₂) = spOver ψ₂ ≫ x → ψ₂ k = sig p f g ψ₂ x z₂ := by
    intro D _ _ x
    obtain ⟨D', _, _, ψ, z, hψ, hz⟩ := hr D x
    have cmp : ∀ (D₂ : Type) [CommRing D₂] [Algebra R D₂] (ψ₂ : D →ₐ[R] D₂) (z₂ : Pt A D₂),
        (z₂ ^ p : Pt A D₂) = spOver ψ₂ ≫ x →
        ∀ (E : Type) [CommRing E] [Algebra R E] (α : D' →ₐ[R] E) (β : D₂ →ₐ[R] E),
          α.comp ψ = β.comp ψ₂ → α (sig p f g ψ x z) = β (sig p f g ψ₂ x z₂) := by
      intro D₂ _ _ ψ₂ z₂ hz₂ E _ _ α β e
      rw [sig_nat hp hf hfg ψ α x z hz, sig_nat hp hf hfg ψ₂ β x z₂ hz₂, sig, sig, e,
        chi_indep hp hg h0 (spOver α ≫ z) (spOver β ≫ z₂)
          (by rw [pow_comp ψ α x z hz, pow_comp ψ₂ β x z₂ hz₂, e])]
    obtain ⟨k, hk⟩ := descend ψ hψ (sig p f g ψ x z) (fun E _ _ α β e ↦ cmp D' ψ z hz E α β e)
    refine ⟨k, fun D₂ _ _ ψ₂ z₂ hz₂ ↦ ?_⟩
    obtain ⟨E, _, _, α, β, e, hβ⟩ := exists_square ψ hψ ψ₂
    apply hβ
    rw [← cmp D₂ ψ₂ z₂ hz₂ E α β e, ← hk]
    exact (DFunLike.congr_fun e k).symm
  choose k hk using key
  refine ⟨k, fun D _ _ D₁ _ _ φ x _ ↦ ?_⟩
  obtain ⟨D', _, _, ψ, z, hψ, hz⟩ := hr D₁ (spOver φ ≫ x)
  have hi : Function.Injective ψ := hψ.injective
  apply hi
  have h1 := hk D₁ (spOver φ ≫ x) D' ψ z hz
  have h2 := hk D x D' (ψ.comp φ) z (by rw [hz, ← Category.assoc, spOver_comp])
  have h3 := hf D D₁ D' φ ψ x (sm_whole _)
  simp only [sig, AlgHom.comp_apply] at h1 h2
  rw [map_sub ψ]
  linear_combination h2 - h1 - h3

end GlobalTheory.PtExt.Descent
end
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CoefBound

theorem cartierDivisor_mult_nsmul_eq_natCast_mul {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] (D : CartierDiv X)
    (n : ℕ) (z : X) : (n • D).mult z = n * D.mult z := by
  induction n with
  | zero =>
    have h := CartierDiv.mult_add (0 : CartierDiv X) 0 z
    rw [add_zero] at h
    rw [zero_nsmul]; push_cast; omega
  | succ n ih => rw [succ_nsmul, CartierDiv.mult_add, ih]; push_cast; ring

theorem coef_lt_of_large : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] [CompactSpace Y] (R Fd : CartierDiv Y) (m r a : ℕ), 0 < r → (∀ z, R.mult z < m) → ∃ b : ℕ, a ≤ b ∧ ∀ z, ((r * b) • R + m • Fd).mult z < (m * r * b : ℕ) := by
  intro Y _ _ _ R Fd m r a hr hR
  classical
  have hfin := Fd.finite_support_mult
  set S : ℕ := ∑ z ∈ hfin.toFinset, ((m : ℤ) * Fd.mult z).toNat with hS
  refine ⟨a + 1 + S, by omega, fun z => ?_⟩
  have hF : (m : ℤ) * Fd.mult z < ((a + 1 + S : ℕ) : ℤ) := by
    by_cases hz : Fd.mult z = 0
    · rw [hz]; push_cast; omega
    · have hmem : z ∈ hfin.toFinset := by simpa using hz
      have h1 : ((m : ℤ) * Fd.mult z).toNat ≤ S :=
        Finset.single_le_sum (f := fun z => ((m : ℤ) * Fd.mult z).toNat) (fun _ _ => Nat.zero_le _) hmem
      have h2 : (m : ℤ) * Fd.mult z ≤ (((m : ℤ) * Fd.mult z).toNat : ℤ) := Int.self_le_toNat _
      have h3 : ((((m : ℤ) * Fd.mult z).toNat : ℕ) : ℤ) ≤ (S : ℤ) := by exact_mod_cast h1
      push_cast; omega
  rw [CartierDiv.mult_add, cartierDivisor_mult_nsmul_eq_natCast_mul, cartierDivisor_mult_nsmul_eq_natCast_mul]
  set b : ℕ := a + 1 + S
  have hRz : R.mult z ≤ (m : ℤ) - 1 := by have := hR z; omega
  have hrb : (0 : ℤ) ≤ ((r * b : ℕ) : ℤ) := by positivity
  have key : ((r * b : ℕ) : ℤ) * R.mult z ≤ ((r * b : ℕ) : ℤ) * ((m : ℤ) - 1) :=
    mul_le_mul_of_nonneg_left hRz hrb
  have hb : ((b : ℕ) : ℤ) ≤ ((r * b : ℕ) : ℤ) := by
    have : b ≤ r * b := Nat.le_mul_of_pos_left b hr
    exact_mod_cast this
  have e : (((m * r * b : ℕ)) : ℤ) = ((r * b : ℕ) : ℤ) * (m : ℤ) := by push_cast; ring
  rw [e]
  nlinarith

end GlobalTheory.CoefBound
end
end
