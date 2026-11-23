module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle033
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtExt

theorem fv_pullbackOneCocycle_eq_bcPull_of_changeOfBase : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (X : Over (Sp R)) (X' : Over (Sp R')) (q : X'.left ⟶ X.left) (w : q ≫ X.hom = X'.hom ≫ spMap σ) (m : IsMor (dp0 R) (X.hom ≫ 𝟙 _) (dp0 R') (X'.hom ≫ 𝟙 _) σ q) (f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))), fv (m.coef.pullbackOneCocycle f) = bcPull w (fv f) := by
  intro R R' _ _ σ X X' q w m f
  unfold fv bcPull
  rfl

end GlobalTheory.PtExt
end
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem diagSum_pullTwo : ∀ (R : Type) [CommRing R] (D D' : Type) [CommRing D] [Bialgebra R D]
    [Coalgebra.IsCocomm R D] [CommRing D'] [Bialgebra R D'] [Coalgebra.IsCocomm R D'] (f : D →ₐc[R] D')
    (m : ℕ) (c : D ⊗[R] D), f (diagSum R D m c) = diagSum R D' m (pullbackTwo f c) := by
  intro R _ D D' _ _ _ _ _ _ f m c
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>

    simp only [diagSum_tmul, pullbackTwo, TensorProduct.map_tmul, map_sum, map_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mulBy]
    rfl
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _)]

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

theorem isAdd_of_isSecDiff_isSecAdd : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (n : ℕ), HasRoots A n → ∀ b : Fn0 A, IsTorsChar n b → ∀ S : SecFam A, (∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), IsSec n b x (S D x)) → ∀ (u : Fn1 A) (g : Fn2 A), IsSecDiff n S u → IsSecAdd n S g → IsAdd u g := by
  intro R _ A _ _ n hR b _ S _ u g hu hg D _ _ D' _ _ φ x y
  let x' : Pt A D' := spOver φ ≫ x
  let y' : Pt A D' := spOver φ ≫ y
  obtain ⟨D1, _, _, ψ1, z1, h1, hz1⟩ := hR D' x'
  obtain ⟨E, _, _, ψ2, w, h2, hw⟩ := hR D1 (spOver ψ1 ≫ y')
  let ψ : D' →ₐ[R] E := ψ2.comp ψ1
  let z : Pt A E := spOver ψ2 ≫ z1
  have hψ : spOver ψ = spOver ψ2 ≫ spOver ψ1 := (spOver_comp ψ1 ψ2).symm
  have hz : z ^ n = spOver ψ ≫ x' := by
    rw [show z = spOver ψ2 ≫ z1 from rfl, ← comp_pow, hz1, hψ, Category.assoc]
  have hw' : w ^ n = spOver ψ ≫ y' := by rw [hw, hψ, Category.assoc]
  have hmul : spOver φ ≫ (x * y) = (spOver φ ≫ x) * (spOver φ ≫ y) := comp_mul _ _ _
  have hzw : (z * w) ^ n = spOver ψ ≫ spOver φ ≫ (x * y) := by
    rw [mul_pow, hz, hw', hmul, comp_mul]
  have hc (t : Pt A D) : spOver ψ ≫ spOver φ ≫ t = spOver (ψ.comp φ) ≫ t := by
    rw [← Category.assoc, spOver_comp]
  have hinj : Function.Injective ψ := fun _ _ h ↦ h1.injective (h2.injective h)
  apply hinj
  have e1 := hg D' x' y' E ψ z w hz hw'
  have e2 := hg D x y E (ψ.comp φ) z w (hz.trans (hc x)) (hw'.trans (hc y))
  rw [AlgHom.comp_apply] at e2
  have e3 := hu D D' φ (x * y) E ψ (z * w) hzw
  rw [hmul] at e3
  have e4 := hu D D' φ x E ψ z hz
  have e5 := hu D D' φ y E ψ w hw'
  simp only [map_sub]
  linear_combination e1 - e2 - e3 + e4 + e5

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

theorem isCoc_of_isSecDiff : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A]
    [IsCommMonObj A] (n : ℕ), HasRoots A n → ∀ b : Fn0 A, IsTorsChar n b → ∀ S : SecFam A,
    (∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), IsSec n b x (S D x)) →
    ∀ u : Fn1 A, IsSecDiff n S u → IsCoc (whole A) u := by
  intro R _ A _ _ n hR b _ S _ u hu
  unfold IsCoc
  intro D _ _ D' _ _ D'' _ _ φ ψ x _
  obtain ⟨E, _, _, χ, z, hχ, hz⟩ := hR D'' (spOver ψ ≫ spOver φ ≫ x)
  apply (show Function.Injective χ from hχ.injective)
  have h1 := hu D D'' (ψ.comp φ) x E χ z (by rw [hz, ← spOver_comp, Category.assoc])
  have h2 := hu D D' φ x E (χ.comp ψ) z (by rw [hz, ← spOver_comp, Category.assoc])
  have h3 := hu D' D'' ψ (spOver φ ≫ x) E χ z hz
  rw [AlgHom.comp_apply] at h2
  rw [map_add χ, h1, h2, h3, ← spOver_comp, Category.assoc, AlgHom.comp_assoc]
  abel

end GlobalTheory.PtExt
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtExt

namespace BcIso

variable {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {X : Over (Sp R)} {X' : Over (Sp R')}
  {q : X'.left ⟶ X.left}

def ringOf {E : Type} [CommRing E] (g : Sp E ⟶ X'.left) : R' →+* E :=
  (Spec.preimage (R := CommRingCat.of R') (S := CommRingCat.of E) (g ≫ X'.hom)).hom

theorem spMap_ringOf {E : Type} [CommRing E] (g : Sp E ⟶ X'.left) : spMap (ringOf g) = g ≫ X'.hom := by
  unfold ringOf
  exact Spec.map_preimage _

theorem ringOf_eq_of_spMap {E : Type} [CommRing E] (g : Sp E ⟶ X'.left) (τ : R' →+* E)
    (h : spMap τ = g ≫ X'.hom) : ringOf g = τ := by
  have h1 : spMap (ringOf g) = spMap τ := by rw [spMap_ringOf, h]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)

def ptBack [IsIso q] {E : Type} [CommRing E] (g : Sp E ⟶ X.left) :
    @Pt R' _ X' E _ (ringOf (X' := X') (g ≫ inv q)).toAlgebra := by
  letI : Algebra R' E := (ringOf (X' := X') (g ≫ inv q)).toAlgebra
  exact Over.homMk (U := SpAlg R' E) (V := X') (g ≫ inv q)
    (spMap_ringOf (X' := X') (g ≫ inv q)).symm

theorem ringOf_comp (w : q ≫ X.hom = X'.hom ≫ spMap σ) [IsIso q] {E : Type} [CommRing E] [Algebra R E]
    (z : Pt X E) : (ringOf (X' := X') (z.left ≫ inv q)).comp σ = algebraMap R E := by
  have h1 : spMap ((ringOf (X' := X') (z.left ≫ inv q)).comp σ) = spMap (algebraMap R E) := by
    rw [spMap_comp, spMap_ringOf]
    simp only [Category.assoc, ← w, IsIso.inv_hom_id_assoc]
    exact Over.w z
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)

theorem bcPull_transport (w : q ≫ X.hom = X'.hom ≫ spMap σ) (u : Fn1 X) (E E' : Type) [CommRing E] [CommRing E']
    (A : Algebra R' E) (A' : Algebra R' E') (i : Algebra R E) (i' : Algebra R E') (h : i = algVia σ E)
    (h' : i' = algVia σ E') (φ : @AlgHom R E E' _ _ _ i i') (z : @Pt R _ X E _ i) (ψ : E →ₐ[R'] E')
    (y : Pt X' E) (hψ : ∀ e, ψ e = φ e) (hy : y.left ≫ q = z.left) :
    @u E _ i E' _ i' φ z = bcPull w u E E' ψ y := by
  subst h h'
  letI := algVia σ E
  letI := algVia σ E'
  have e1 : homVia σ ψ = φ := AlgHom.ext hψ
  have e2 : ptVia w y = z := by
    apply Over.OverMorphism.ext
    exact hy
  rw [← e1, ← e2]
  rfl

end BcIso

open BcIso

theorem isCob_of_bcPull_isIso : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (X : Over (Sp R))
    (X' : Over (Sp R')) (q : X'.left ⟶ X.left) (w : q ≫ X.hom = X'.hom ≫ spMap σ), IsIso q → ∀ u : Fn1 X,
    IsCoc (whole X) u → (∃ k, IsCob (whole X') (bcPull w u) k) → ∃ k, IsCob (whole X) u k := by
  intro R R' _ _ σ X X' q w hq u _ hk
  obtain ⟨k', hk'⟩ := hk
  refine ⟨fun E _ _ z ↦ @k' E _ (ringOf (X' := X') (z.left ≫ inv q)).toAlgebra (ptBack z.left), ?_⟩
  intro E _ i E' _ i' φ z _
  let τ := ringOf (X' := X') (z.left ≫ inv q)
  let τ' := ringOf (X' := X') ((spOver φ ≫ z).left ≫ inv q)
  letI A : Algebra R' E := τ.toAlgebra
  letI A' : Algebra R' E' := τ'.toAlgebra
  have hτ : τ' = (φ : E →+* E').comp τ := by
    apply ringOf_eq_of_spMap
    rw [spMap_comp, spMap_ringOf]
    simp only [Over.comp_left, Category.assoc]
    rfl
  have hc : ∀ r, φ (τ r) = τ' r := fun r ↦ by rw [hτ]; rfl
  let ψ : E →ₐ[R'] E' := { (φ : E →+* E') with commutes' := hc }
  have h : i = algVia σ E := Algebra.algebra_ext _ _ fun r ↦ (congrArg (fun f ↦ f r) (ringOf_comp w z)).symm
  have h' : i' = algVia σ E' :=
    Algebra.algebra_ext _ _ fun r ↦ (congrArg (fun f ↦ f r) (ringOf_comp w (spOver φ ≫ z))).symm
  have e1 := bcPull_transport w u E E' A A' i i' h h' φ z ψ (ptBack z.left) (fun _ ↦ rfl)
    (by simp [ptBack])
  have e2 := hk' E E' ψ (ptBack z.left) (sm_whole _)
  have e3 : spOver ψ ≫ ptBack (X' := X') z.left = ptBack (spOver φ ≫ z).left :=
    Over.OverMorphism.ext (by simp [ptBack]; rfl)
  rw [e1, e2, e3]
  rfl

end GlobalTheory.PtExt
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open GlobalTheory GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

variable {p : ℕ} {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {G : PDivGroup p R}
  (t : PDivGroup.TorsionTower G A) (N : ℕ)


open Classical in
def torsVal (b : G.A N) : Fn0 A := fun _ _ _ x ↦
  if h : x ^ p ^ N = 1 then t.lift N x h b else 0

theorem lift_spOver {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D']
    (φ : D →ₐ[R] D') (w : Pt A D) (hw : w ^ p ^ N = 1) (hw' : (spOver φ ≫ w) ^ p ^ N = 1) :
    t.lift N (spOver φ ≫ w) hw' = φ.comp (t.lift N w hw) :=
  t.inj N D' _ _ (by rw [t.lift_y, ← spOver_comp, Category.assoc, t.lift_y])

theorem lift_mul {D : Type} [CommRing D] [Algebra R D] (w w' : Pt A D) (hw : w ^ p ^ N = 1)
    (hw' : w' ^ p ^ N = 1) (h : (w * w') ^ p ^ N = 1) :
    t.lift N (w * w') h = (toConv (t.lift N w hw) * toConv (t.lift N w' hw')).ofConv :=
  t.inj N D _ _ (by rw [t.lift_y, t.mul, ofConv_toConv, ofConv_toConv, t.lift_y, t.lift_y])

theorem isTorsChar_torsVal (b : G.A N) (hb : cobOne R (G.A N) b = 0) :
    IsTorsChar (p ^ N) (torsVal t N b) := by
  have hc : Coalgebra.comul (R := R) b = b ⊗ₜ 1 + 1 ⊗ₜ b := by
    rw [cobOne_apply, sub_sub, sub_eq_zero] at hb; exact hb
  refine ⟨fun D _ _ D' _ _ φ w hw ↦ ?_, fun D _ _ w w' hw hw' ↦ ?_⟩
  · have hw2 : (spOver φ ≫ w) ^ p ^ N = 1 := by rw [← MonObj.comp_pow, hw, MonObj.comp_one]
    simp only [torsVal, dite_eq_left hw, dite_eq_left hw2, lift_spOver t N φ w hw hw2,
      AlgHom.comp_apply]
  · have h : (w * w') ^ p ^ N = 1 := (t.exists_iff N _).1
      ⟨(toConv (t.lift N w hw) * toConv (t.lift N w' hw')).ofConv, by
        rw [t.mul, ofConv_toConv, ofConv_toConv, t.lift_y, t.lift_y]⟩
    simp only [torsVal, dite_eq_left hw, dite_eq_left hw', dite_eq_left h, lift_mul t N w w' hw hw' h]
    change (toConv (t.lift N w hw) * toConv (t.lift N w' hw')) b = _
    simp only [AlgHom.convMul_apply, hc, map_add, Algebra.TensorProduct.lift_tmul, map_one,
      _root_.mul_one, _root_.one_mul]

theorem exists_isTorsChar :
    ∀ (p : ℕ) (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (G : PDivGroup p R)
      (t : PDivGroup.TorsionTower G A) (N : ℕ) (b : G.A N),
      cobOne R (G.A N) b = 0 → ∃ β : Fn0 A, IsTorsChar (p ^ N) β ∧
        ∀ (D : Type) [CommRing D] [Algebra R D] (φ : G.A N →ₐ[R] D), β D (spOver φ ≫ t.y N) = φ b := by
  intro p R _ A _ G t N b hb
  refine ⟨torsVal t N b, isTorsChar_torsVal t N b hb, fun D _ _ φ ↦ ?_⟩
  have h : (spOver φ ≫ t.y N) ^ p ^ N = 1 := (t.exists_iff N _).1 ⟨φ, rfl⟩
  have e : t.lift N (spOver φ ≫ t.y N) h = φ := t.inj N D _ _ (t.lift_y N _ h)
  simp only [torsVal, dite_eq_left h, e]

end GlobalTheory.PtExt
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

variable {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {X : Over (Sp R)} {X' : Over (Sp R')}
  {q : X'.left ⟶ X.left}

theorem ptVia_spOver (w : q ≫ X.hom = X'.hom ≫ spMap σ) {E E' : Type} [CommRing E] [Algebra R' E]
    [CommRing E'] [Algebra R' E'] (φ : E →ₐ[R'] E') (y : Pt X' E) :
    ptVia w (spOver φ ≫ y) =
      @spOver R _ E E' _ (algVia σ E) _ (algVia σ E') (homVia σ φ) ≫ ptVia w y := by
  apply Over.OverMorphism.ext
  change (spMap (φ : E →+* E') ≫ y.left) ≫ q = spMap (φ : E →+* E') ≫ (y.left ≫ q)
  exact Category.assoc _ _ _

theorem bcPull_coc_cob (w : q ≫ X.hom = X'.hom ≫ spMap σ) (u : Fn1 X) :
    (IsCoc (whole X) u → IsCoc (whole X') (bcPull w u)) ∧
      ((∃ k, IsCob (whole X) u k) → ∃ k, IsCob (whole X') (bcPull w u) k) := by
  constructor
  · intro h
    unfold IsCoc at h ⊢
    intro E _ _ E' _ _ E'' _ _ φ ψ y _
    let _ : Algebra R E := algVia σ E
    let _ : Algebra R E' := algVia σ E'
    let _ : Algebra R E'' := algVia σ E''
    have hc : (homVia σ ψ).comp (homVia σ φ) = homVia σ (ψ.comp φ) := AlgHom.ext fun _ ↦ rfl
    simp only [bcPull, ptVia_spOver, ← hc]
    exact h E E' E'' (homVia σ φ) (homVia σ ψ) (ptVia w y) (sm_whole _)
  · rintro ⟨k, hk⟩
    refine ⟨fun E _ _ y ↦ @k E _ (algVia σ E) (ptVia w y), ?_⟩
    unfold IsCob at hk ⊢
    intro E _ _ E' _ _ φ y _
    let _ : Algebra R E := algVia σ E
    let _ : Algebra R E' := algVia σ E'
    simp only [bcPull, ptVia_spOver]
    exact hk E E' (homVia σ φ) (ptVia w y) (sm_whole _)

theorem bcPull_keeps : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (X : Over (Sp R)) (X' : Over (Sp R')) (q : X'.left ⟶ X.left) (w : q ≫ X.hom = X'.hom ≫ spMap σ) (u : Fn1 X), (IsCoc (whole X) u → IsCoc (whole X') (bcPull w u)) ∧ ((∃ k, IsCob (whole X) u k) → ∃ k, IsCob (whole X') (bcPull w u) k) :=
  fun _ _ _ _ _ _ _ _ w u ↦ bcPull_coc_cob w u

end GlobalTheory.PtExt
end
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt.SumMulFacts

theorem ptAlg_comp_right {R D D' E : Type} [CommRing R] [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D']
    [CommRing E] [Algebra R E] (φ : D →ₐ[R] D') (y : Pt (SpAlg R D') E) :
    ptAlg (R := R) (D := D) (E := E) (y ≫ spOver φ) = (ptAlg y).comp φ := by
  conv_lhs => rw [← spOver_ptAlg y, spOver_comp]
  exact ptAlg_spOver _

theorem main : ∀ (R D : Type) [CommRing R] [CommRing D] [Algebra R D] (B : Over (Sp R))
    (J : Type) [Fintype J] (d : J → D) (b : J → Fn1 B),
    ((∀ i, IsCoc (whole B) (b i)) → IsCoc (whole _) (sumMul d b)) ∧
      ∀ (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D'),
        (sumMul d b).pull (spOver φ ▷ B) = sumMul (fun i ↦ φ (d i)) b := by
  intro R D _ _ _ B J _ d b
  refine ⟨fun hb ↦ ?_, fun D' _ _ φ ↦ ?_⟩
  · unfold IsCoc at hb ⊢
    intro E _ _ E' _ _ E'' _ _ φ ψ z _
    have hα := ptAlg_comp (D := D) φ (z ≫ fst (SpAlg R D) B)

    simp only [sumMul, hα, map_sum, map_mul, AlgHom.comp_apply, Category.assoc]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have h := hb i E E' E'' φ ψ (z ≫ snd _ _) (sm_whole _)
    rw [h]
    ring
  · unfold Fn1
    funext E _ _ E' _ _ ψ y
    simp only [Fn1.pull, sumMul, Category.assoc, whiskerRight_fst, whiskerRight_snd]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [← Category.assoc, ptAlg_comp_right, AlgHom.comp_apply]

end GlobalTheory.PtExt.SumMulFacts
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem tensorLift_mulByNatConvPower_comul_eq_succ {R : Type} [CommRing R] {D : Type} [CommRing D] [Bialgebra R D]
    [Coalgebra.IsCocomm R D] (i : ℕ) (a : D) :
    (Algebra.TensorProduct.lift (mulBy R D i : D →ₐ[R] D) (AlgHom.id R D) fun _ _ ↦ Commute.all _ _)
      (Coalgebra.comul a) = mulBy R D (i + 1) a := by
  have h1 := comp_mulBy_pts (AlgHom.id R D) i
  have h2 := comp_mulBy_pts (AlgHom.id R D) (i + 1)
  rw [AlgHom.id_comp] at h1 h2
  have h3 : mulBy R D (i + 1) a = (toConv (AlgHom.id R D) ^ (i + 1)).ofConv a := DFunLike.congr_fun h2 a
  rw [h3, pow_succ]
  have h4 := AlgHom.convMul_apply (toConv (AlgHom.id R D) ^ i) (toConv (AlgHom.id R D)) a
  refine Eq.trans ?_ h4.symm
  rw [← h1]

theorem diagSum_cobOne_eq {R : Type} [CommRing R] {D : Type} [CommRing D] [Bialgebra R D]
    [Coalgebra.IsCocomm R D] (m : ℕ) (a : D) :
    diagSum R D m (cobOne R D a) = mulBy R D m a - algebraMap R D (Coalgebra.counit a) - m • a := by
  induction m with
  | zero =>
    have h := DFunLike.congr_fun (comp_mulBy_pts (AlgHom.id R D) 0) a
    rw [AlgHom.id_comp, pow_zero] at h
    have h' : mulBy R D 0 a = algebraMap R D (Coalgebra.counit a) := h
    simp [diagSum, h']
  | succ m ih =>
    have e : diagSum R D (m + 1) (cobOne R D a) = diagSum R D m (cobOne R D a) +
        (Algebra.TensorProduct.lift (mulBy R D m : D →ₐ[R] D) (AlgHom.id R D) fun _ _ ↦ Commute.all _ _)
          (cobOne R D a) := by
      simp [diagSum, Finset.sum_range_succ, LinearMap.add_apply]
    rw [e, ih, cobOne_apply, map_sub, map_sub, tensorLift_mulByNatConvPower_comul_eq_succ, Algebra.TensorProduct.lift_tmul,
      Algebra.TensorProduct.lift_tmul, map_one, map_one, _root_.mul_one, _root_.one_mul, AlgHom.id_apply, succ_nsmul]
    have hc : ((mulBy R D m : D →ₐ[R] D) a) = mulBy R D m a := rfl
    rw [hc]
    abel

end GlobalTheory.PtExt

theorem GlobalTheory.PtExt.diagSum_cobOne_eq_zero : ∀ (p : ℕ)  (R : Type) [CommRing R] (G : PDivGroup p R) (N : ℕ), (p : R) ^ N = 0 → ∀ a : G.A N, diagSum R (G.A N) (p ^ N) (cobOne R (G.A N) a) = 0 := by
  intro p R _ G N hN a
  rw [GlobalTheory.PtExt.diagSum_cobOne_eq, G.mulBy_pow_self N a, sub_self, zero_sub, neg_eq_zero,
    ← Nat.cast_smul_eq_nsmul R, Nat.cast_pow, hN, zero_smul]
end

section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

namespace GlobalTheory.DefPt

theorem isGram_matNorm : ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] [DecidableEq ι] (Y : (K →+* ℂ) → Matrix ι ι ℂ), (∀ σ, (Y σ).det ≠ 0) → IsGram (Pi.basisFun K ι) (fun v => (Y v.embedding)⁻¹) (matNorm Y) ∧ HasGram (matNorm Y) := by
  intro K _ _ ι _ _ Y hY
  have h : IsGram (Pi.basisFun K ι) (fun v => (Y v.embedding)⁻¹) (matNorm Y) := by
    intro v
    have hu : IsUnit (Y v.embedding).det := (hY _).isUnit
    refine ⟨Matrix.isUnit_nonsing_inv_det _ hu, fun x => ?_⟩
    have hv : Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K ι) v x = fun j => v.embedding (x j) := by
      funext j
      simp [Formalism.HermitianLatticesTheory.vecAt]
    simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm, Formalism.HermitianLatticesTheory.fcoord, matNorm, Matrix.nonsing_inv_nonsing_inv _ hu, hv]
  exact ⟨h, h.hasGram⟩

end GlobalTheory.DefPt
end
