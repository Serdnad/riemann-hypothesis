module

public import GroundTheory.ArithmeticGeometry.SchemeCohomology.InvertibleSheaf
public import Mathlib.Tactic.ENatToNat
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Bundle002
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Bundle001
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
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MonoidalCategory TensorProduct

universe u

noncomputable section

variable {X : Scheme.{u}}

lemma bijective_app_of_factor {A B : X.Modules} (φ : A ⟶ B) {P : PMod X}
    (p : (preMod X).obj A ⟶ P) (q : P ⟶ (preMod X).obj B)
    (hq : ModulesTensor.W (Opens.grothendieckTopology X) X.sheaf.obj q)
    (hφ : (preMod X).map φ = p ≫ q) {W : X.Opens}
    (hp : ∀ V ≤ W, Function.Bijective (p.app (op V))) :
    ∀ V ≤ W, Function.Bijective (φ.app V) := by
  obtain ⟨hq₁, hq₂⟩ := (ModulesTensor.W_toPresheaf_iff q).1 hq
  have hφapp : ∀ (V : X.Opens) (a : Γ(A, V)), φ.app V a = q.app (op V) (p.app (op V) a) :=
    fun V a => congrArg (fun g => g.app (op V) a) hφ |>.trans rfl
  have nat : ∀ {V V' : X.Opens} (i : V' ≤ V) (σ : Γ(A, V)),
      φ.app V' (A.presheaf.map (homOfLE i).op σ) = B.presheaf.map (homOfLE i).op (φ.app V σ) :=
    fun i σ => NatTrans.naturality_apply φ.mapPresheaf (homOfLE i).op σ
  have inj : ∀ V ≤ W, Function.Injective (φ.app V) := by
    intro V hV
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    rw [hφapp] at ha
    have hS := hq₁ (op V) _ ha
    rw [Opens.mem_grothendieckTopology] at hS
    apply sheaf_eq_of_locally ⟨A.presheaf, A.isSheaf⟩ (V := V)
    intro x hx
    obtain ⟨V', i, hi, hxV'⟩ := hS x hx
    refine ⟨V', i.le, hxV', ?_⟩
    have h0 : p.app (op V') (A.presheaf.map (homOfLE i.le).op a) = 0 := by
      have := PresheafOfModules.naturality_apply p (homOfLE i.le).op a
      exact this.trans hi
    apply (hp V' (i.le.trans hV)).1
    exact h0.trans (map_zero _).symm |>.trans (congrArg _ (map_zero _).symm)
  intro V hV
  refine ⟨inj V hV, fun b => ?_⟩
  have hS := hq₂ (op V) b
  rw [Opens.mem_grothendieckTopology] at hS
  choose V' i hi hxV' using hS
  choose w hw using hi
  choose a₀ ha using fun x (hx : x ∈ V) => (hp (V' x hx) ((i x hx).le.trans hV)).2 (w x hx)
  let a : ∀ x (hx : x ∈ V), Γ(A, V' x hx) := fun x hx => a₀ x hx
  have key : ∀ x hx, φ.app (V' x hx) (a x hx) = B.presheaf.map (homOfLE (i x hx).le).op b :=
    fun x hx => (hφapp _ (a x hx)).trans ((congrArg _ (ha x hx)).trans (hw x hx))
  obtain ⟨g, hg⟩ := sheaf_exists_glue ⟨A.presheaf, A.isSheaf⟩ (V := V) (ι := {x : X // x ∈ V})
    (fun c => V' c.1 c.2) (fun c => (i c.1 c.2).le) (fun x hx => ⟨⟨x, hx⟩, hxV' x hx⟩)
    (fun c => a c.1 c.2) (by
      intro c d
      apply inj _ (inf_le_left.trans ((i c.1 c.2).le.trans hV))
      change φ.app _ (A.presheaf.map _ (a c.1 c.2)) = φ.app _ (A.presheaf.map _ (a d.1 d.2))
      rw [nat, nat, key, key]
      change ((B.presheaf.map _ ≫ B.presheaf.map _) b) = ((B.presheaf.map _ ≫ B.presheaf.map _) b)
      rw [← B.presheaf.map_comp, ← B.presheaf.map_comp]
      rfl)
  refine ⟨g, ?_⟩
  apply sheaf_eq_of_locally ⟨B.presheaf, B.isSheaf⟩ (V := V)
  intro x hx
  refine ⟨V' x hx, (i x hx).le, hxV' x hx, ?_⟩
  change B.presheaf.map _ (φ.app V g) = _
  rw [← nat]
  have := hg ⟨x, hx⟩
  simp only at this
  rw [this]
  exact key x hx

def homOfPreMod {M S : X.Modules} (g : (preMod X).obj M ⟶ (preMod X).obj S) : M ⟶ S :=
  inv ((sheafifyModAdj X).counit.app M) ≫ ((sheafifyModAdj X).homEquiv _ _).symm g

lemma preMod_map_homOfPreMod {M S : X.Modules} (g : (preMod X).obj M ⟶ (preMod X).obj S) :
    (preMod X).map (homOfPreMod g) = g := by
  have h1 : (preMod X).map (inv ((sheafifyModAdj X).counit.app M)) =
      (sheafifyModAdj X).unit.app ((preMod X).obj M) := by
    rw [Functor.map_inv]
    exact (IsIso.eq_inv_of_inv_hom_id ((sheafifyModAdj X).right_triangle_components M)).symm
  rw [homOfPreMod, Functor.map_comp, h1, Adjunction.homEquiv_counit, Functor.map_comp,
    ← Category.assoc]
  erw [← (sheafifyModAdj X).unit.naturality g]
  rw [Category.assoc]
  erw [(sheafifyModAdj X).right_triangle_components S]
  exact Category.comp_id g

variable (M L : X.Modules) (s : Γ(L, ⊤))

def tensorSection : (preMod X).obj M ⟶ (preMod X).obj M ⊗ (preMod X).obj L :=
  PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom
        { toFun := fun m => (m : ((preMod X).obj M).obj U) ⊗ₜ
            resM ((preMod X).obj L) (le_top : U.unop ≤ ⊤) s
          map_zero' := zero_tmul _ _
          map_add' := fun a b => add_tmul _ _ _ }
      naturality := fun U V g => by
        ext m
        change (((preMod X).obj M).map g m) ⊗ₜ resM ((preMod X).obj L) (le_top : V.unop ≤ ⊤) s =
          (((preMod X).obj M).map g m) ⊗ₜ ((preMod X).obj L).map g
            (resM ((preMod X).obj L) (le_top : U.unop ≤ ⊤) s)
        congr 1
        change ((preMod X).obj L).map (homOfLE (le_top : V.unop ≤ ⊤)).op s =
          ((preMod X).obj L).map g (((preMod X).obj L).map (homOfLE (le_top : U.unop ≤ ⊤)).op s)
        exact PresheafOfModules.map_comp_apply ((preMod X).obj L) (homOfLE (le_top : U.unop ≤ ⊤)).op g s }
    (fun _ _ _ => rfl)

def mulSection : M ⟶ M ⊗ L :=
  homOfPreMod (tensorSection M L s ≫ tensorToSheaf M L)

lemma preMod_map_mulSection :
    (preMod X).map (mulSection M L s) = tensorSection M L s ≫ tensorToSheaf M L :=
  preMod_map_homOfPreMod _

theorem bijective_mulSection_app {W : X.Opens}
    (hs : IsBasisOn ((preMod X).obj L) W (resM ((preMod X).obj L) le_top s)) :
    ∀ V ≤ W, Function.Bijective ((mulSection M L s).app V) := by
  refine bijective_app_of_factor _ (tensorSection M L s) (tensorToSheaf M L) (W_tensorToSheaf M L)
    (preMod_map_mulSection M L s) ?_
  intro V hV
  have e0 : resM ((preMod X).obj L) hV (resM ((preMod X).obj L) le_top s) =
      resM ((preMod X).obj L) (le_top : V ≤ ⊤) s := resM_resM _ le_top hV s
  let R := X.sheaf.obj.obj (op V)
  let e : R ≃ₗ[R] ((preMod X).obj L).obj (op V) :=
    LinearEquiv.ofBijective (LinearMap.toSpanSingleton R _
      (resM ((preMod X).obj L) hV (resM ((preMod X).obj L) le_top s))) (hs V hV)
  let E := (TensorProduct.rid R (((preMod X).obj M).obj (op V))).symm ≪≫ₗ
    e.lTensor (((preMod X).obj M).obj (op V))
  have hE : ∀ m, E m = (tensorSection M L s).app (op V) m := by
    intro m
    change m ⊗ₜ e 1 = m ⊗ₜ resM ((preMod X).obj L) (le_top : V ≤ ⊤) s
    congr 1
    exact (one_smul R _).trans e0
  have : ⇑((tensorSection M L s).app (op V)) = E := funext fun m => (hE m).symm
  rw [this]
  exact E.bijective

end

end GroundTheory.Arith.SchemeCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Limits Opposite

universe u

noncomputable section

variable {A : Type u} [CommRing A] {I : Ideal A} {X : Scheme.{u}} [X.Over (Spec (.of A))]
  {V : X.Opens}

abbrev polyRing (I : Ideal A) (V : X.Opens) : CommRingCat.{u} :=
  Γ(reesPolyScheme I X, reesPolyMap I X ⁻¹ᵁ (reesPr I X ⁻¹ᵁ V))

abbrev polyInl (I : Ideal A) (V : X.Opens) : Γ(X, V) ⟶ polyRing I V :=
  (reesPr I X).app V ≫ (reesPolyMap I X).app _

lemma polyDesc_w : CommRingCat.ofHom (algV (A := A) X V) ≫ CommRingCat.ofHom Polynomial.C =
    CommRingCat.ofHom (Polynomial.C (R := A)) ≫
      CommRingCat.ofHom (Polynomial.mapRingHom (algV (A := A) X V)) := by
  ext a
  simp

def polyRingHom (hV : IsAffineOpen V) : polyRing I V →+* Polynomial Γ(X, V) :=
  ((isPushout_reesPoly (I := I) hV).desc (CommRingCat.ofHom Polynomial.C)
    (CommRingCat.ofHom (Polynomial.mapRingHom (algV (A := A) X V))) polyDesc_w).hom

lemma polyRingHom_inl (hV : IsAffineOpen V) (c : Γ(X, V)) :
    polyRingHom hV (polyInl I V c) = Polynomial.C c := by
  have := congrArg (fun f : Γ(X, V) ⟶ CommRingCat.of (Polynomial Γ(X, V)) => f.hom c)
    (IsPushout.inl_desc (isPushout_reesPoly (I := I) hV) _ _ polyDesc_w)
  exact this

lemma polyRingHom_inr (hV : IsAffineOpen V) (p : Polynomial A) :
    polyRingHom hV (polyInr (I := I) V p) = p.map (algV (A := A) X V) := by
  have := congrArg
    (fun f : CommRingCat.of (Polynomial A) ⟶ CommRingCat.of (Polynomial Γ(X, V)) => f.hom p)
    (IsPushout.inr_desc (isPushout_reesPoly (I := I) hV) _ _ polyDesc_w)
  exact this

def polyRingInv : Polynomial Γ(X, V) →+* polyRing I V :=
  Polynomial.eval₂RingHom (polyInl I V).hom (polyInr (I := I) V Polynomial.X)

lemma polyInr_eq_eval₂ (hV : IsAffineOpen V) (p : Polynomial A) :
    polyInr (I := I) V p =
      p.eval₂ ((polyInl I V).hom.comp (algV (A := A) X V)) (polyInr (I := I) V Polynomial.X) := by
  have hw := (isPushout_reesPoly (I := I) hV).w
  have h : (polyInr (I := I) V).hom =
      Polynomial.eval₂RingHom ((polyInl I V).hom.comp (algV (A := A) X V))
        (polyInr (I := I) V Polynomial.X) := by
    apply Polynomial.ringHom_ext
    · intro a
      have := congrArg (fun f => f.hom a) hw
      simpa using this.symm
    · simp
  exact congrArg (fun f => f p) h

def polyRingEquiv (hV : IsAffineOpen V) : polyRing I V ≃+* Polynomial Γ(X, V) :=
  RingEquiv.ofRingHom (polyRingHom hV) (polyRingInv (I := I) (V := V))
    (by
      apply Polynomial.ringHom_ext
      · intro c
        change polyRingHom hV ((polyRingInv (I := I) (V := V)) (Polynomial.C c)) = Polynomial.C c
        rw [polyRingInv, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
        exact polyRingHom_inl hV c
      · change polyRingHom hV ((polyRingInv (I := I) (V := V)) Polynomial.X) = Polynomial.X
        rw [polyRingInv, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, polyRingHom_inr,
          Polynomial.map_X])
    (by
      have h := (isPushout_reesPoly (I := I) hV).hom_ext
        (k := CommRingCat.ofHom ((polyRingInv (I := I) (V := V)).comp (polyRingHom hV)))
        (l := 𝟙 _) (by
          ext c
          change (polyRingInv (I := I) (V := V)) (polyRingHom hV (polyInl I V c)) = polyInl I V c
          rw [polyRingHom_inl, polyRingInv, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]) (by
          refine CommRingCat.hom_ext (RingHom.ext fun p => ?_)
          change (polyRingInv (I := I) (V := V)) (polyRingHom hV (polyInr (I := I) V p)) =
            polyInr (I := I) V p
          rw [polyRingHom_inr, polyRingInv, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_map]
          exact (polyInr_eq_eval₂ hV p).symm)
      exact congrArg CommRingCat.Hom.hom h)


lemma reesInr_comp (hV : IsAffineOpen V) :
    reesInr (I := I) V ≫ (reesPolyMap I X).app _ =
      CommRingCat.ofHom (algebraMap (reesAlgebra I) (Polynomial A)) ≫ polyInr (I := I) V := by
  have hw := (isPushout_app_of_isPullback (isPullback_reesPoly I X) (hV.preimage (reesPr I X))).w
  rw [reesInr, polyInr, Category.assoc, hw, ← Category.assoc, ← Category.assoc,
    Scheme.ΓSpecIso_inv_naturality]

def reesRingHom (hV : IsAffineOpen V) : Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V) →+* Polynomial Γ(X, V) :=
  (polyRingHom hV).comp ((reesPolyMap I X).app (reesPr I X ⁻¹ᵁ V)).hom

lemma reesRingHom_inl (hV : IsAffineOpen V) (c : Γ(X, V)) :
    reesRingHom hV ((reesPr I X).app V c) = Polynomial.C c :=
  polyRingHom_inl hV c

lemma reesRingHom_inr (hV : IsAffineOpen V) (r : reesAlgebra I) :
    reesRingHom hV (reesInr (I := I) V r) = (r : Polynomial A).map (algV (A := A) X V) := by
  have := congrArg (fun f : CommRingCat.of (reesAlgebra I) ⟶ polyRing I V => f.hom r)
    (reesInr_comp (I := I) hV)
  change polyRingHom hV (((reesInr (I := I) V ≫ (reesPolyMap I X).app _)).hom r) = _
  rw [this]
  exact polyRingHom_inr hV _


variable (I X V) in
def reesCoeffRing : Subring (Polynomial Γ(X, V)) where
  carrier := {p | ∀ n, p.coeff n ∈ (I.map (algV (A := A) X V)) ^ n}
  one_mem' n := by
    change _root_.AddMonoidAlgebra.coeff (M := ℕ) 1 n ∈ _
    rw [Polynomial.coeff_one]
    split_ifs with h
    · subst h
      simp
    · exact zero_mem _
  mul_mem' {p q} hp hq n := by
    change (p * q).coeff n ∈ _
    rw [Polynomial.coeff_mul]
    refine Ideal.sum_mem _ fun x hx => ?_
    have hx : x.1 + x.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
    rw [← hx, pow_add]
    exact Ideal.mul_mem_mul (hp x.1) (hq x.2)
  zero_mem' n := by simp
  add_mem' {p q} hp hq n := by
    change (p + q).coeff n ∈ _
    rw [Polynomial.coeff_add]
    exact add_mem (hp n) (hq n)
  neg_mem' {p} hp n := by
    change (-p).coeff n ∈ _
    rw [Polynomial.coeff_neg]
    exact neg_mem (hp n)

lemma C_mem_reesCoeffRing (c : Γ(X, V)) : Polynomial.C c ∈ reesCoeffRing I X V := by
  intro n
  rw [Polynomial.coeff_C]
  split_ifs with h
  · subst h
    simp
  · exact zero_mem _

lemma map_mem_reesCoeffRing (r : reesAlgebra I) :
    (r : Polynomial A).map (algV (A := A) X V) ∈ reesCoeffRing I X V := by
  intro n
  rw [Polynomial.coeff_map, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ ((mem_reesAlgebra_iff I _).1 r.2 n)

theorem reesRingHom_mem (hV : IsAffineOpen V) (s : Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V)) :
    reesRingHom hV s ∈ reesCoeffRing I X V := by
  let l : Γ(X, V) ⟶ CommRingCat.of (reesCoeffRing I X V) :=
    CommRingCat.ofHom ((Polynomial.C).codRestrict (reesCoeffRing I X V) C_mem_reesCoeffRing)
  let r : CommRingCat.of (reesAlgebra I) ⟶ CommRingCat.of (reesCoeffRing I X V) :=
    CommRingCat.ofHom (((Polynomial.mapRingHom (algV (A := A) X V)).comp (reesAlgebra I).val.toRingHom)
      |>.codRestrict (reesCoeffRing I X V) map_mem_reesCoeffRing)
  have hw' : CommRingCat.ofHom (algV (A := A) X V) ≫ l =
      CommRingCat.ofHom (algebraMap A (reesAlgebra I)) ≫ r := by
    refine CommRingCat.hom_ext (RingHom.ext fun a => Subtype.ext ?_)
    simp [l, r]
  let d := (isPushout_rees (I := I) hV).desc l r hw'
  have h : (CommRingCat.ofHom (reesRingHom hV) :
      Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V) ⟶ CommRingCat.of (Polynomial Γ(X, V))) =
      d ≫ CommRingCat.ofHom (reesCoeffRing I X V).subtype := by
    apply (isPushout_rees (I := I) hV).hom_ext
    · refine CommRingCat.hom_ext (RingHom.ext fun c => ?_)
      have := congrArg (fun f : Γ(X, V) ⟶ CommRingCat.of (reesCoeffRing I X V) =>
        (f.hom c : Polynomial Γ(X, V))) (IsPushout.inl_desc (isPushout_rees (I := I) hV) l r hw')
      exact (reesRingHom_inl hV c).trans this.symm
    · refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
      have := congrArg (fun f : CommRingCat.of (reesAlgebra I) ⟶ CommRingCat.of (reesCoeffRing I X V) =>
        (f.hom x : Polynomial Γ(X, V))) (IsPushout.inr_desc (isPushout_rees (I := I) hV) l r hw')
      exact (reesRingHom_inr hV x).trans this.symm
  have := congrArg (fun f : Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V) ⟶
    CommRingCat.of (Polynomial Γ(X, V)) => f.hom s) h
  change reesRingHom hV s ∈ _
  rw [show reesRingHom hV s = ((d.hom s : reesCoeffRing I X V) : Polynomial Γ(X, V)) from this]
  exact (d.hom s).2

end

end GroundTheory.Arith.SchemeCoh
end
