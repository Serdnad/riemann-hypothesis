module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
public import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle682
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh.Vanish

theorem commAlgFunctorCohomologyTwo_eq_zero_of_isInitial {R : Type} [CommRing R] {C : Type} [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) {T₀ : C} (h : IsInitial T₀) (c : CatCoh.H2 F) : c = 0 := by
  obtain ⟨z, rfl⟩ := H2.mk_surjective F c
  refine H2.mk_eq_zero.2 ⟨fun T T' φ ↦ z.1 T₀ T T' (h.to T) φ, ?_⟩
  funext T T' T'' φ ψ
  have := z.2 (h.to T) φ ψ
  rw [h.to_comp φ] at this
  rw [d1_apply]
  linear_combination this

theorem glob_sub {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {T₀ : C}
    (h : IsInitial T₀) [Subsingleton Ω[F.obj T₀⁄R]] : Subsingleton (Glob1 F) :=
  subsingleton_of_forall_eq 0 fun ω ↦ Subtype.ext (funext fun T ↦ by
    rw [ω.2 (h.to T), Subsingleton.elim (ω.1 T₀) 0, map_zero]; rfl)

def topInit {X : Scheme.{0}} (hX : IsAffineOpen (⊤ : X.Opens)) : IsInitial (op ⟨⊤, hX⟩ : AffOp X) :=
  IsInitial.ofUniqueHom (fun U ↦ (homOfLE (show U.unop ≤ ⟨⊤, hX⟩ from le_top (a := U.unop.1))).op)
    fun _ _ ↦ rfl

theorem omega_sub {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) [IsIso s] :
    Subsingleton Ω[Sec s ⊤⁄R] := by
  refine KaehlerDifferential.subsingleton_of_surjective R _ ?_
  have : IsIso (secMap s ⊤) := by
    unfold secMap
    haveI h1 : IsIso s.appTop := inferInstanceAs (IsIso (s.app ⊤))
    haveI h2 : IsIso (X.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op) := by
      rw [show (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op = 𝟙 _ from rfl]
      infer_instance
    exact IsIso.comp_isIso' (f := (Scheme.ΓSpecIso (CommRingCat.of R)).inv) inferInstance
      (IsIso.comp_isIso' h1 h2)
  exact (ConcreteCategory.bijective_of_isIso (secMap s ⊤)).2

theorem main :
    (∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsAffine X → Subsingleton (HO1 s) ∧ Subsingleton (HO2 s)) ∧
      ∀ (R : Type) [CommRing R], Subsingleton (GlobForm (𝟙_ (Over (Sp R))).hom) ∧
        Subsingleton (HH1 (𝟙_ (Over (Sp R))).hom) := by
  refine ⟨fun R _ X s hX ↦ ?_, fun R _ ↦ ?_⟩
  · have h := topInit (isAffineOpen_top X)
    exact ⟨subsingleton_of_forall_eq 0 (H1.eq_zero_of_isInitial _ h),
      subsingleton_of_forall_eq 0 (commAlgFunctorCohomologyTwo_eq_zero_of_isInitial _ h)⟩
  · haveI : IsIso (𝟙_ (Over (Sp R))).hom := inferInstanceAs (IsIso (𝟙 (Sp R)))
    have h := topInit (isAffineOpen_top (Sp R))
    haveI : Subsingleton Ω[(OAff (𝟙_ (Over (Sp R))).hom).obj (op ⟨⊤, isAffineOpen_top (Sp R)⟩)⁄R] :=
      omega_sub (𝟙_ (Over (Sp R))).hom
    haveI hg : Subsingleton (GlobForm (𝟙_ (Over (Sp R))).hom) := glob_sub _ h
    refine ⟨hg, subsingleton_of_forall_eq 0 fun c ↦ ?_⟩
    have hc : c ∈ Fil1 (OAff (𝟙_ (Over (Sp R))).hom) := H1.eq_zero_of_isInitial _ h _
    rw [Fil1_eq_range] at hc
    obtain ⟨ω, rfl⟩ := hc
    have : ω = 0 := Subtype.ext (Subsingleton.elim (α := GlobForm (𝟙_ (Over (Sp R))).hom) _ _)
    rw [this, map_zero]

end GlobalTheory.AbCoh.Vanish
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.AbCoh.rel_add : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), (∀ (x x' : GlobalTheory.CatCoh.H1 F) (n n' : ℕ) (y : Fin n → GlobalTheory.CatCoh.H1 F) (w : Fin n → Glob1 F) (y' : Fin n' → GlobalTheory.CatCoh.H1 F) (w' : Fin n' → Glob1 F), DRel F x y w → DRel F x' y' w' → DRel F (x + x') (Fin.append y y') (Fin.append w w')) ∧ (∀ (x x' : GlobalTheory.CatCoh.H1 F) (n n' : ℕ) (u v : Fin n → Glob1 F) (u' v' : Fin n' → Glob1 F), ObRel F x u v → ObRel F x' u' v' → ObRel F (x + x') (Fin.append u u') (Fin.append v v')) ∧ ∀ (w w' : Glob1 F) (n n' : ℕ) (u v : Fin n → Glob1 F) (u' v' : Fin n' → Glob1 F), ClRel F w u v → ClRel F w' u' v' → ClRel F (w + w') (Fin.append u u') (Fin.append v v') := by
  intro R _ C _ F
  have hw : ∀ {n n' : ℕ} (u v : Fin n → Glob1 F) (u' v' : Fin n' → Glob1 F) (T : C),
      wsum F (Fin.append u u') (Fin.append v v') T = wsum F u v T + wsum F u' v' T := by
    intro n n' u v u' v' T
    simp only [wsum, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
  refine ⟨?_, ?_, ?_⟩
  · rintro x x' n n' y w y' w' ⟨f, g, ω, hf, hg, he⟩ ⟨f', g', ω', hf', hg', he'⟩
    refine ⟨f + f', Fin.append g g', ω + ω', by rw [map_add (f := _), hf, hf'], ?_, ?_⟩
    · intro k
      refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) k
      · simp only [Fin.append_left]; exact hg i
      · simp only [Fin.append_right]; exact hg' i
    · intro T T' φ
      have e1 := he φ
      have e2 := he' φ
      simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, Submodule.coe_add, Pi.add_apply, map_add (f := _)]
      rw [e1, e2]; abel
  · rintro x x' n n' u v u' v' ⟨f, ω, hf, hc, hd⟩ ⟨f', ω', hf', hc', hd'⟩
    refine ⟨f + f', ω + ω', by rw [map_add (f := _), hf, hf'], ?_, ?_⟩
    · intro T T' φ
      simp only [Submodule.coe_add, Pi.add_apply, map_add (f := _)]
      rw [hc φ, hc' φ]; abel
    · intro T
      simp only [Pi.add_apply, map_add (f := _), hw, hd T, hd' T]
  · intro w w' n n' u v u' v' h h' T
    simp only [Submodule.coe_add, Pi.add_apply, map_add (f := _), hw, h T, h' T]
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem fp_prod (R : Type) [CommRing R] (W H : Type) [AddCommGroup W] [Module R W]
    [AddCommGroup H] [Module R H] (a b : ℕ) (hW : FP R W a) (hH : FP R H b) :
    FP R (W × H) (a + b) := by
  obtain ⟨hWf, hWp, hWr⟩ := hW
  obtain ⟨hHf, hHp, hHr⟩ := hH
  refine ⟨inferInstance, inferInstance, fun p => ?_⟩
  have := Module.rankAtStalk_prod (R := R) W H
  rw [congrFun this p, Pi.add_apply, hWr p, hHr p]

theorem fp_ext (R : Type) [CommRing R] (W M H : Type) [AddCommGroup W] [Module R W]
    [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H] (a b : ℕ)
    (i : W →ₗ[R] M) (p : M →ₗ[R] H) (hi : Function.Injective i) (hp : Function.Surjective p)
    (hex : Function.Exact i p) (hW : FP R W a) (hH : FP R H b) : FP R M (a + b) := by
  have hWH := fp_prod R W H a b hW hH
  obtain ⟨-, hHp, -⟩ := hH
  obtain ⟨s, hs⟩ := Module.projective_lifting_property p (LinearMap.id : H →ₗ[R] H) hp
  obtain ⟨e, -⟩ := hex.splitSurjectiveEquiv hi ⟨s, hs⟩
  obtain ⟨hf, hpr, hr⟩ := hWH
  refine ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv e.symm, fun q => ?_⟩
  rw [congrFun (Module.rankAtStalk_eq_of_equiv e) q, hr q]

theorem fp_ext_prod : (∀ (R : Type) [CommRing R] (W M H : Type) [AddCommGroup W] [Module R W] [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H] (a b : ℕ) (i : W →ₗ[R] M) (p : M →ₗ[R] H), Function.Injective i → Function.Surjective p → Function.Exact i p → FP R W a → FP R H b → FP R M (a + b)) ∧ ∀ (R : Type) [CommRing R] (W H : Type) [AddCommGroup W] [Module R W] [AddCommGroup H] [Module R H] (a b : ℕ), FP R W a → FP R H b → FP R (W × H) (a + b) :=
  ⟨fun R _ W M H _ _ _ _ _ _ a b i p hi hp hex hW hH => fp_ext R W M H a b i p hi hp hex hW hH,
   fun R _ W H _ _ _ _ a b hW hH => fp_prod R W H a b hW hH⟩

end GlobalTheory.AbCoh
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

theorem frame_coord : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R),
    CohomZeroIsConstants F → ∀ (n : ℕ) (Φ : Frame F n), ∃ l : Fin n → (Glob1 F →ₗ[R] R),
      (∀ i (w : Glob1 F) T, Φ.δ i T (w.1 T) = algebraMap R (F.obj T) (l i w)) ∧
        ∀ w, w = ∑ i, l i w • Φ.w i := by
  intro R _ C _ F hF n Φ
  have hd : ∀ i (w : Glob1 F), d0 F (fun T ↦ Φ.δ i T (w.1 T)) = 0 := by
    intro i w
    funext T T' φ
    rw [amitsur_d0_apply, w.2 φ, Φ.nat]
    exact sub_self _
  let c : Fin n → Glob1 F → R := fun i w ↦ (hF _ (hd i w)).exists.choose
  have hc : ∀ i w T, Φ.δ i T (w.1 T) = algebraMap R (F.obj T) (c i w) :=
    fun i w ↦ (hF _ (hd i w)).exists.choose_spec
  have uniq : ∀ i w (r : R), (∀ T, Φ.δ i T (w.1 T) = algebraMap R (F.obj T) r) → c i w = r :=
    fun i w r hr ↦ (hF _ (hd i w)).unique (hc i w) hr
  refine ⟨fun i ↦
    { toFun := c i
      map_add' := fun w w' ↦ uniq i (w + w') _ (fun T ↦ by
        rw [Submodule.coe_add, Pi.add_apply, map_add (f := _), hc, hc, map_add (f := _)])
      map_smul' := fun r w ↦ uniq i (r • w) _ (fun T ↦ by
        rw [Submodule.coe_smul, Pi.smul_apply, ← algebraMap_smul (F.obj T) r (w.1 T), map_smul, hc,
          RingHom.id_apply, smul_eq_mul, smul_eq_mul, map_mul]) },
    fun i w T ↦ hc i w T, fun w ↦ ?_⟩
  apply Subtype.ext
  funext T
  rw [Submodule.coe_sum, Finset.sum_apply]
  conv_lhs => rw [Φ.sum T (w.1 T)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hc, Submodule.coe_smul, Pi.smul_apply, algebraMap_smul]
  rfl

end GlobalTheory.AbCoh
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem Bock_add : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : φ ≫ s = s' ≫ spMap σ) (h₀ : φ₀ ≫ s = s₀ ≫ spMap σ₀) (x x' : HO1 s') (z z' : HO2 s₀), Bock h h₀ t x z → Bock h h₀ t x' z' → Bock h h₀ t (x + x') (z + z') := by
  intro R R' R₀ _ _ _ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ x x' z z'
  rintro ⟨f, w, hd, ⟨c, hc, hcx⟩, ⟨e, he, hez⟩⟩ ⟨f', w', hd', ⟨c', hc', hcx'⟩, ⟨e', he', hez'⟩⟩
  refine ⟨f + f', w + w', by rw [map_add (f := _), hd, hd', smul_add], ⟨c + c', fun p q a ↦ ?_, ?_⟩,
    ⟨e + e', fun p q r a b ↦ ?_, ?_⟩⟩
  · simp only [Submodule.coe_add, Pi.add_apply, hc, hc', map_add (f := _)]
  · rw [map_add (f := _), hcx, hcx', map_add (f := _)]
  · simp only [Submodule.coe_add, Pi.add_apply, he, he', map_add (f := _)]
  · rw [map_add (f := _), hez, hez', map_add (f := _)]

end GlobalTheory.AbCoh
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem ofForm_injective_of_H0Const (R : Type) [CommRing R] (C : Type) [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) (hF : CohomZeroIsConstants F) : Function.Injective (ofForm F) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro ω hω
  obtain ⟨g, hg, hD⟩ := (ofForm_eq_zero (F := F)).1 hω
  have h0 : d0 F g = 0 := by
    funext T T' φ
    have e : d0 F g T T' φ = g T' - mp F φ (g T) := rfl
    rw [e, ← hg φ, sub_self]; rfl
  obtain ⟨r, hr, -⟩ := hF g h0
  refine Subtype.ext (Subtype.ext (funext fun T ↦ ?_))
  rw [← hD T, hr T]
  exact (D R (F.obj T)).map_algebraMap r

end GlobalTheory.AbCoh
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem pullHH1_clAll : ∀ (R R' : Type) [CommRing R] [CommRing R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (σ : R →+* R') (φ : X' ⟶ X) (h : φ ≫ s = s' ≫ spMap σ) (hc : Closed1 (OAff s) = ⊤) (hc' : Closed1 (OAff s') = ⊤) (w : GlobForm s), pullHH1 h (clAll (OAff s) hc w) = clAll (OAff s') hc' (GlobalTheory.CechDR.pullForm h w) := by
  intro R R' _ _ X X' s s' σ φ h hc hc' w
  let ω : ClosedForm s := ⟨w, by rw [show ClosedForm s = ⊤ from hc]; exact Submodule.mem_top⟩
  let ω' : ClosedForm s' := ⟨GlobalTheory.CechDR.pullForm h w, by rw [show ClosedForm s' = ⊤ from hc']; exact Submodule.mem_top⟩
  have e : IsPull1 h (clForm s ω) (clForm s' ω') := IsPullForm.cl (isPullForm_pullForm h w)
  have k : clAll (OAff s) hc w = clForm s ω := rfl
  have k' : clAll (OAff s') hc' (GlobalTheory.CechDR.pullForm h w) = clForm s' ω' := rfl
  rw [k, k']
  exact e.eq_pullHH1.symm

end GlobalTheory.AbCoh
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

namespace GlobalTheory.BadCount

noncomputable def twistAlg {K Γ : Type} [Field K] [Group Γ] (H : Subgroup Γ) (χ : Γ →* Kˣ) :
    MonoidAlgebra K H →ₐ[K] MonoidAlgebra K H :=
  MonoidAlgebra.lift K (MonoidAlgebra K H) H
    { toFun := fun h => MonoidAlgebra.single h (((χ (h : Γ))⁻¹ : Kˣ) : K)
      map_one' := by simp [MonoidAlgebra.one_def]
      map_mul' := by
        intro a b
        simp [MonoidAlgebra.single_mul_single, mul_comm] }

theorem twistAlg_single {K Γ : Type} [Field K] [Group Γ] (H : Subgroup Γ) (χ : Γ →* Kˣ) (h : H) (c : K) :
    twistAlg H χ (MonoidAlgebra.single h c) = MonoidAlgebra.single h (c * (((χ (h : Γ))⁻¹ : Kˣ) : K)) := by
  simp [twistAlg, MonoidAlgebra.lift_single, MonoidAlgebra.smul_single]

theorem twistAlg_inv_twistAlg {K Γ : Type} [Field K] [Group Γ] (H : Subgroup Γ) (χ : Γ →* Kˣ)
    (x : MonoidAlgebra K H) : twistAlg H χ⁻¹ (twistAlg H χ x) = x := by
  induction x using MonoidAlgebra.induction_on with
  | of m =>
    simp only [MonoidAlgebra.of_apply, twistAlg_single]
    congr 1
    simp
  | add x y hx hy => simp [map_add (f := _), hx, hy]
  | smul r x hx => simp [map_smul, hx]

theorem twistAlg_injective {K Γ : Type} [Field K] [Group Γ] (H : Subgroup Γ) (χ : Γ →* Kˣ) :
    Function.Injective (twistAlg H χ) := fun x y hxy => by
  rw [← twistAlg_inv_twistAlg H χ x, ← twistAlg_inv_twistAlg H χ y, hxy]

theorem embReg_twist : ∀ (K Γ V : Type) [Field K] [Group Γ] [AddCommGroup V] [Module K V] (ρ ρ' : Representation K Γ V)
    (χ : Γ →* Kˣ), (∀ g v, ρ' g v = ((χ g : Kˣ) : K) • ρ g v) → ∀ (H : Subgroup Γ) (n : ℕ), EmbReg ρ H n → EmbReg ρ' H n := by
  intro K Γ V _ _ _ _ ρ ρ' χ hρ H n ⟨j, hj, hjeq⟩
  refine ⟨LinearMap.pi fun i => (twistAlg H χ).toLinearMap.comp ((LinearMap.proj i).comp j), ?_, ?_⟩
  · intro v w hvw
    apply hj
    funext i
    have := congrFun hvw i
    simp only [LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.coe_proj, Function.eval,
      AlgHom.toLinearMap_apply] at this
    exact twistAlg_injective H χ this
  · intro h v i
    simp only [LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.coe_proj, Function.eval,
      AlgHom.toLinearMap_apply]
    rw [hρ, map_smul, Pi.smul_apply, hjeq, map_smul, map_mul, twistAlg_single, ← smul_mul_assoc,
      MonoidAlgebra.smul_single]
    congr 2
    simp

end GlobalTheory.BadCount
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

noncomputable section

namespace GlobalTheory.BadCount.Inh

variable {A : Type} [CommRing A] {n : ℕ}

theorem isUniUp_one : IsUniUp (1 : Matrix (Fin n) (Fin n) A) := by
  intro a b
  refine ⟨fun h => Matrix.one_apply_ne (ne_of_gt h), fun h => ?_⟩
  subst h; exact Matrix.one_apply_eq a

theorem diag_mul_of_tri {M N : Matrix (Fin n) (Fin n) A} (hM : ∀ a c : Fin n, c < a → M a c = 0)
    (hN : ∀ a c : Fin n, c < a → N a c = 0) (a : Fin n) : (M * N) a a = M a a * N a a := by
  rw [Matrix.mul_apply, Finset.sum_eq_single a]
  · intro c _ hca
    rcases lt_or_gt_of_ne hca with h | h
    · rw [hM a c h, zero_mul]
    · rw [hN c a h, mul_zero]
  · intro h; exact absurd (Finset.mem_univ a) h

theorem isUniUp_mul {M N : Matrix (Fin n) (Fin n) A} (hM : IsUniUp M) (hN : IsUniUp N) : IsUniUp (M * N) := by
  intro a b
  constructor
  · intro hba
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases lt_or_ge c a with h | h
    · rw [(hM a c).1 h, zero_mul]
    · rw [(hN c b).1 (lt_of_lt_of_le hba h), mul_zero]
  · rintro rfl
    rw [diag_mul_of_tri (fun a c h => (hM a c).1 h) (fun a c h => (hN a c).1 h), (hM a a).2 rfl, (hN a a).2 rfl, one_mul]

theorem isUniUp_inv (u : GL (Fin n) A) (hu : IsUniUp (u : Matrix (Fin n) (Fin n) A)) :
    IsUniUp ((u⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) := by
  have hb : Matrix.BlockTriangular (u : Matrix (Fin n) (Fin n) A) id := fun i j h => (hu i j).1 h
  have hinv : Matrix.BlockTriangular ((u⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) id := by
    rw [Matrix.coe_units_inv]; exact Matrix.blockTriangular_inv_of_blockTriangular hb
  intro a b
  refine ⟨fun h => hinv h, ?_⟩
  rintro rfl
  have h1 : (((u⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) * (u : Matrix (Fin n) (Fin n) A)) a a = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_apply_eq]
  rw [diag_mul_of_tri (fun a c h => hinv h) (fun a c h => hb h), (hu a a).2 rfl, mul_one] at h1
  exact h1

def uniUpGL : Subgroup (GL (Fin n) A) where
  carrier := {u | IsUniUp (u : Matrix (Fin n) (Fin n) A)}
  mul_mem' := fun {a b} ha hb => by
    rw [Set.mem_setOf_eq, Units.val_mul]; exact isUniUp_mul ha hb
  one_mem' := by rw [Set.mem_setOf_eq, Units.val_one]; exact isUniUp_one
  inv_mem' := fun {u} hu => isUniUp_inv u hu

theorem mem_uniUpGL (u : GL (Fin n) A) : u ∈ (uniUpGL : Subgroup (GL (Fin n) A)) ↔ IsUniUp (u : Matrix (Fin n) (Fin n) A) :=
  Iff.rfl

def sd (M : Matrix (Fin n) (Fin n) A) : A := ∑ i ∈ Finset.range (n - 1), entN M i (i + 1)

theorem entN_mul_super {M N : Matrix (Fin n) (Fin n) A} (hM : IsUniUp M) (hN : IsUniUp N) {i : ℕ} (hi : i + 1 < n) :
    entN (M * N) i (i + 1) = entN M i (i + 1) + entN N i (i + 1) := by
  have h0 : i < n := by omega
  simp only [entN, dif_pos (And.intro h0 hi)]
  rw [Matrix.mul_apply, Fintype.sum_eq_add (⟨i, h0⟩ : Fin n) ⟨i + 1, hi⟩]
  · rw [(hM _ _).2 rfl, (hN _ _).2 rfl, one_mul, mul_one, add_comm]
  · simp [Fin.ext_iff]
  · rintro c ⟨h1, h2⟩
    have h1' : c.val ≠ i := fun h => h1 (Fin.ext h)
    have h2' : c.val ≠ i + 1 := fun h => h2 (Fin.ext h)
    rcases Nat.lt_or_gt_of_ne h1' with h | h
    · rw [(hM ⟨i, h0⟩ c).1 (by change c.val < i; omega), zero_mul]
    · rw [(hN c ⟨i + 1, hi⟩).1 (by change i + 1 < c.val; omega), mul_zero]

theorem sd_mul {M N : Matrix (Fin n) (Fin n) A} (hM : IsUniUp M) (hN : IsUniUp N) : sd (M * N) = sd M + sd N := by
  unfold sd
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i hi => entN_mul_super hM hN ?_
  have := Finset.mem_range.1 hi; omega

theorem sd_one : sd (1 : Matrix (Fin n) (Fin n) A) = 0 := by
  unfold sd
  refine Finset.sum_eq_zero fun i _ => ?_
  unfold entN
  split_ifs with h
  · exact Matrix.one_apply_ne (fun e => by simpa using congrArg Fin.val e)
  · rfl

variable (D : D7)

def whitP : Subgroup (G0g D.nd) := Subgroup.pi Set.univ fun _ => uniUpGL

theorem mem_whitP (g : G0g D.nd) :
    g ∈ whitP D ↔ ∀ kv, IsUniUp (g kv : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) := by
  rw [whitP, Subgroup.mem_pi]
  simp only [Set.mem_univ, true_implies, mem_uniUpGL]

def whitChar (ψ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ) : whitP D →* ℂ where
  toFun g := ∏ kv, ψ kv (sd ((g : G0g D.nd) kv : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))))
  map_one' := by
    refine Finset.prod_eq_one fun kv _ => ?_
    simp [sd_one]
  map_mul' g h := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun kv _ => ?_
    rw [← AddChar.map_add_eq_mul, ← sd_mul ((mem_whitP D _).1 g.2 kv) ((mem_whitP D _).1 h.2 kv)]
    rfl

def halfH (k : Fin 2) : Subgroup (G0g D.nd) := Subgroup.pi {kv | kv.1 ≠ k} fun _ => uniUpGL

theorem isHalf_halfH (k : Fin 2) : IsHalf D k (halfH D k) := by
  intro g
  rw [halfH, Subgroup.mem_pi]
  simp only [Set.mem_setOf_eq, mem_uniUpGL]

theorem isWhit_whitP (ψ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ) (hψ : ∀ kv, ψ kv ≠ 1) :
    IsWhit D (whitP D) (whitChar D ψ).toHomUnits ψ :=
  ⟨hψ, mem_whitP D, fun _ => rfl⟩

theorem exists_whit_half : ∀ (D : D7) (ψ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ),
    (∀ kv, ψ kv ≠ 1) → (∃ (P : Subgroup (G0g D.nd)) (lam : P →* ℂˣ), IsWhit D P lam ψ) ∧ ∀ k, ∃ H, IsHalf D k H :=
  fun D ψ hψ => ⟨⟨whitP D, _, isWhit_whitP D ψ hψ⟩, fun k => ⟨halfH D k, isHalf_halfH D k⟩⟩

end GlobalTheory.BadCount.Inh
end
end

section

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace

theorem _root_.GlobalTheory.T.exists_period_cohomologyClass_of_rich_based : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F), K.Rich → K.Based → ∀ c : H1 K.Oc, ∃ per : Λ →+ Hol F.V, c = K.perCl per := by
  first | exact @GlobalTheory.AnPer.Charts.exists_perCl | exact GlobalTheory.AnPer.Charts.exists_perCl | (intros; apply GlobalTheory.AnPer.Charts.exists_perCl <;> assumption)
end
