module

public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.PullbackBaseChange
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.Bundle001
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Bundle003
public import Mathlib.Algebra.Polynomial.Module.Basic
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Bundle009
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FormalLimit
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe c236Ext c236Scheme

private noncomputable def H.linearMapV436 {X : Scheme.{c236Scheme}}
    [HasExt.{c236Ext} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{c236Scheme})]
    (A : Type*) [CommRing A] [Algebra A Γ(X, ⊤)]
    {F G : X.Modules} (φ : F ⟶ G) (n : ℕ) :
    Sheaf.H.{c236Ext} (modulesAb F) n →ₗ[A] Sheaf.H.{c236Ext} (modulesAb G) n where
  toFun := Sheaf.H.map.{c236Ext} (modulesAbMap φ) n
  map_add' := map_add _
  map_smul' a x := by
    change Sheaf.H.map.{c236Ext} (modulesAbMap φ) n (a • x) =
      a • Sheaf.H.map.{c236Ext} (modulesAbMap φ) n x
    rw [H.smul_def, H.smul_def, ← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply,
      ← modulesAbMap_comp, ← modulesAbMap_comp, smulHom_comp]

end

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe u

noncomputable section

attribute [local instance] algebraOfOver

private lemma mem_range_of_comm {R M M' N N' : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
    (δ' : M' →ₗ[R] N') (δ : M →ₗ[R] N) (f : M' →ₗ[R] M) (g : N' →ₗ[R] N)
    (comm : ∀ x, δ (f x) = g (δ' x)) {y : N'} (hy : y ∈ δ'.range) : g y ∈ δ.range := by
  obtain ⟨x, rfl⟩ := hy
  exact ⟨f x, comm x⟩

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
  [X.Over (Spec (.of A))] (F : X.Modules) (q : ℕ)

lemma formalτ_mem_formalQ (n : ℕ) (y : Sheaf.H.{u} (modulesAb (idealPow I F (n + 2))) (q + 1))
    (hy : y ∈ formalQ I F q (n + 1)) :
    H.linearMap A (idealPowSucc I F (n + 1)) (q + 1) y ∈ formalQ I F q n :=
  mem_range_of_comm (formalδ I F q (n + 1)) (formalδ I F q n) (formalτE I F q n)
    (H.linearMap A (idealPowSucc I F (n + 1)) (q + 1)) (formalδ_naturality I F q n) hy

def formalτQ (n : ℕ) : formalQ I F q (n + 1) →ₗ[A] formalQ I F q n :=
  (H.linearMap A (idealPowSucc I F (n + 1)) (q + 1)).restrict (formalτ_mem_formalQ I F q n)

abbrev formalτP : ∀ n, (Sheaf.H.{u} (modulesAb F) q ⧸ formalK I F q (n + 1)) →ₗ[A]
    (Sheaf.H.{u} (modulesAb F) q ⧸ formalK I F q n) :=
  quotTower (formalK I F q) (formalK_antitone I F q)

lemma formalι_comm (n : ℕ) :
    (formalτE I F q n).comp (formalι I F q (n + 1)) = (formalι I F q n).comp (formalτP I F q n) := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨h, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change Sheaf.H.map.{u} (modulesAbMap (quotPowMap I F n)) q
      (Sheaf.H.map.{u} (modulesAbMap (quotPowπ I F (n + 1))) q h) =
    Sheaf.H.map.{u} (modulesAbMap (quotPowπ I F n)) q h
  rw [← Sheaf.H.map_comp_apply, ← modulesAbMap_comp, quotPowπ_map]

lemma formalπ_comm (n : ℕ) :
    (formalτQ I F q n).comp (formalπ I F q (n + 1)) = (formalπ I F q n).comp (formalτE I F q n) := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  exact (formalδ_naturality I F q n x).symm

private lemma mem_range_of_towerLimit {R : Type u} [CommRing R]
    {M : Type u} [AddCommGroup M] [Module R M]
    {E Q : ℕ → Type u} [∀ n, AddCommGroup (E n)] [∀ n, Module R (E n)]
    [∀ n, AddCommGroup (Q n)] [∀ n, Module R (Q n)]
    (τE : ∀ n, E (n + 1) →ₗ[R] E n) (τQ : ∀ n, Q (n + 1) →ₗ[R] Q n)
    (π : ∀ n, E n →ₗ[R] Q n) (comm : ∀ n, (τQ n).comp (π (n + 1)) = (π n).comp (τE n))
    {n c : ℕ} (hQ : towerComp τQ n c = 0) {x : ∀ n, E n} (hx : x ∈ towerLimit τE)
    (β : M →ₗ[R] E n) (hβ : β.range = (π n).ker) : x n ∈ β.range := by
  let y (m : ℕ) : Q m := π m (x m)
  have hy : y ∈ towerLimit τQ := fun m =>
    (LinearMap.congr_fun (comm m) (x (m + 1))).trans (congrArg (π m) (hx m))
  have hz : x n ∈ (π n).ker :=
    (towerComp_apply_of_mem τQ hy n c).symm.trans
      ((LinearMap.congr_fun hQ (y (n + c))).trans (LinearMap.zero_apply _))
  exact hβ.symm ▸ hz

variable {I F q}

theorem mem_range_formalβ_of_mem_towerLimit {c : ℕ}
    (hQ : ∀ n, towerComp (E := fun m => formalQ I F q m) (formalτQ I F q) n c = 0)
    {x : ∀ n, Sheaf.H.{u} (modulesAb (quotPow I F n)) q} (hx : x ∈ towerLimit (E := fun m => Sheaf.H.{u} (modulesAb (quotPow I F m)) q) (formalτE I F q))
    (n : ℕ) : x n ∈ LinearMap.range (formalβ I F q n) := by
  have hβ : (formalβ I F q n).range = (formalπ I F q n).ker :=
    (Submodule.range_liftQ (formalK I F q n) (formalβ I F q n) (ker_formalβ I F q n).ge).symm.trans
      (range_formalι I F q n)
  exact mem_range_of_towerLimit
    (E := fun m => Sheaf.H.{u} (modulesAb (quotPow I F m)) q) (Q := fun m => formalQ I F q m)
    (n := n) (c := c) (x := x) (formalτE I F q) (formalτQ I F q) (formalπ I F q)
    (formalπ_comm I F q) (hQ n) hx (formalβ I F q n) hβ

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
  {F : X.Modules} {V : X.Opens}


variable (I F V) in
abbrev unitPr : Γ(F, V) →+ Γ((Scheme.Modules.pullback (reesPr I X)).obj F, reesPr I X ⁻¹ᵁ V) :=
  Etale.pullbackUnitApp (reesPr I X) F V


variable (I F V) in
abbrev unitB : Γ((Scheme.Modules.pullback (reesPr I X)).obj F, reesPr I X ⁻¹ᵁ V) →+
    Γ((Scheme.Modules.pullback (reesPolyMap I X)).obj
      ((Scheme.Modules.pullback (reesPr I X)).obj F), reesPolyMap I X ⁻¹ᵁ (reesPr I X ⁻¹ᵁ V)) :=
  Etale.pullbackUnitApp (reesPolyMap I X) ((Scheme.Modules.pullback (reesPr I X)).obj F)
    (reesPr I X ⁻¹ᵁ V)

variable (hF : IsCoherent F) (hV : IsAffineOpen V)

include hF hV in
lemma isBaseChangeAt_reesPr : IsBaseChangeAt (reesPr I X) F V := by
  have := hF.1
  exact isBaseChangeAt_of_isAffineOpen _ F hV (hV.preimage _)

include hF hV in
lemma isBaseChangeAt_reesPolyMap :
    IsBaseChangeAt (reesPolyMap I X) ((Scheme.Modules.pullback (reesPr I X)).obj F)
      (reesPr I X ⁻¹ᵁ V) := by
  have := (isCoherent_pullback_reesPr (I := I) hF).1
  exact isBaseChangeAt_of_isAffineOpen _ _ (hV.preimage _) ((hV.preimage _).preimage _)

lemma single_zero_smul_compat (a : Γ(X, V)) (m : Γ(F, V)) :
    PolynomialModule.single Γ(X, V) 0 (a • m) =
      reesRingHom (I := I) hV ((reesPr I X).app V a) • PolynomialModule.single Γ(X, V) 0 m := by
  rw [reesRingHom_inl, ← Polynomial.monomial_zero_left, PolynomialModule.monomial_smul_single,
    zero_add]

include hF in
lemma exists_theta₁ : ∃ θ : Γ((Scheme.Modules.pullback (reesPr I X)).obj F, reesPr I X ⁻¹ᵁ V) →+
    PolynomialModule Γ(X, V) Γ(F, V),
    (∀ m, θ (unitPr I F V m) = PolynomialModule.single Γ(X, V) 0 m) ∧
    (∀ (s : Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V)) y, θ (s • y) = reesRingHom (I := I) hV s • θ y) := by
  let _ : Module Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V) (PolynomialModule Γ(X, V) Γ(F, V)) :=
    Module.compHom _ (reesRingHom (I := I) hV)
  obtain ⟨θ, hθ, -⟩ := isBaseChangeAt_reesPr (I := I) hF hV _
    (PolynomialModule.lsingle Γ(X, V) 0 : Γ(F, V) →ₗ[Γ(X, V)] _).toAddMonoidHom
    (fun a m => single_zero_smul_compat hV a m)
  exact ⟨θ.toAddMonoidHom, hθ, fun s y => θ.map_smul s y⟩

def theta₁ : Γ((Scheme.Modules.pullback (reesPr I X)).obj F, reesPr I X ⁻¹ᵁ V) →+
    PolynomialModule Γ(X, V) Γ(F, V) :=
  (exists_theta₁ hF hV).choose

lemma theta₁_unitPr (m : Γ(F, V)) :
    theta₁ hF hV (unitPr I F V m) = PolynomialModule.single Γ(X, V) 0 m :=
  (exists_theta₁ hF hV).choose_spec.1 m

lemma theta₁_smul (s : Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V))
    (y : Γ((Scheme.Modules.pullback (reesPr I X)).obj F, reesPr I X ⁻¹ᵁ V)) :
    theta₁ hF hV (s • y) = reesRingHom (I := I) hV s • theta₁ hF hV y :=
  (exists_theta₁ hF hV).choose_spec.2 s y

include hF in
lemma exists_theta : ∃ θ : Γ((Scheme.Modules.pullback (reesPolyMap I X)).obj
      ((Scheme.Modules.pullback (reesPr I X)).obj F), reesPolyMap I X ⁻¹ᵁ (reesPr I X ⁻¹ᵁ V)) →+
    PolynomialModule Γ(X, V) Γ(F, V),
    (∀ y, θ (unitB I F V y) = theta₁ hF hV y) ∧
    (∀ (s : polyRing I V) x, θ (s • x) = polyRingHom (I := I) hV s • θ x) := by
  let _ : Module (polyRing I V) (PolynomialModule Γ(X, V) Γ(F, V)) :=
    Module.compHom _ (polyRingHom (I := I) hV)
  obtain ⟨θ, hθ, -⟩ := isBaseChangeAt_reesPolyMap (I := I) hF hV _ (theta₁ hF hV)
    (fun s y => theta₁_smul hF hV s y)
  exact ⟨θ.toAddMonoidHom, hθ, fun s x => θ.map_smul s x⟩

def thetaMap : Γ((Scheme.Modules.pullback (reesPolyMap I X)).obj
      ((Scheme.Modules.pullback (reesPr I X)).obj F), reesPolyMap I X ⁻¹ᵁ (reesPr I X ⁻¹ᵁ V)) →+
    PolynomialModule Γ(X, V) Γ(F, V) :=
  (exists_theta hF hV).choose

lemma thetaMap_unitB (y : Γ((Scheme.Modules.pullback (reesPr I X)).obj F, reesPr I X ⁻¹ᵁ V)) :
    thetaMap hF hV (unitB I F V y) = theta₁ hF hV y :=
  (exists_theta hF hV).choose_spec.1 y

lemma polyRingInv_polyRingHom (s : polyRing I V) :
    polyRingInv (I := I) (V := V) (polyRingHom hV s) = s :=
  (polyRingEquiv hV).symm_apply_apply s

lemma thetaMap_smul (s : polyRing I V) (x : Γ((Scheme.Modules.pullback (reesPolyMap I X)).obj
      ((Scheme.Modules.pullback (reesPr I X)).obj F), reesPolyMap I X ⁻¹ᵁ (reesPr I X ⁻¹ᵁ V))) :
    thetaMap hF hV (s • x) = polyRingHom (I := I) hV s • thetaMap hF hV x :=
  (exists_theta hF hV).choose_spec.2 s x


variable (I F V) in
abbrev polySec := Γ((Scheme.Modules.pullback (reesPolyMap I X)).obj
      ((Scheme.Modules.pullback (reesPr I X)).obj F), reesPolyMap I X ⁻¹ᵁ (reesPr I X ⁻¹ᵁ V))


variable (I F V) in
def lambdaMap : PolynomialModule Γ(X, V) Γ(F, V) →+ polySec I F V where
  toFun q := q.coeff.sum fun n m =>
    (polyRingInv (I := I) (V := V) (Polynomial.X ^ n)) • unitB I F V (unitPr I F V m)
  map_zero' := by simp
  map_add' q q' := by
    simp only [PolynomialModule.coeff_add]
    rw [Finsupp.sum_add_index']
    · intro n
      simp
    · intro n m m'
      rw [map_add (f := _), map_add (f := _), smul_add]

lemma lambdaMap_single (n : ℕ) (m : Γ(F, V)) :
    lambdaMap I F V (PolynomialModule.single Γ(X, V) n m) =
      (polyRingInv (I := I) (V := V) (Polynomial.X ^ n)) • unitB I F V (unitPr I F V m) := by
  simp [lambdaMap, Finsupp.sum_single_index]

lemma unitB_unitPr_smul (c : Γ(X, V)) (m : Γ(F, V)) :
    unitB I F V (unitPr I F V (c • m)) = polyInl I V c • unitB I F V (unitPr I F V m) := by
  rw [unitPr, pullbackUnitApp_smul_at, unitB, pullbackUnitApp_smul_at]
  rfl

lemma lambdaMap_smul (p : Polynomial Γ(X, V)) (q : PolynomialModule Γ(X, V) Γ(F, V)) :
    lambdaMap I F V (p • q) = polyRingInv (I := I) (V := V) p • lambdaMap I F V q := by
  induction p using Polynomial.induction_on' with
  | add p p' hp hp' => rw [add_smul, map_add (f := _), hp, hp', map_add (f := _), add_smul]
  | monomial i c =>
    induction q using PolynomialModule.induction_linear with
    | zero => simp
    | add q q' h h' => rw [smul_add, map_add (f := _), h, h', map_add (f := _), smul_add]
    | single j m =>
      rw [PolynomialModule.monomial_smul_single, lambdaMap_single, lambdaMap_single,
        unitB_unitPr_smul, smul_smul, smul_smul, polyRingInv, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_X_pow,
        Polynomial.eval₂_X_pow, Polynomial.eval₂_monomial, pow_add]
      congr 1
      ring

include hF hV in
lemma lambdaMap_theta₁ (y : Γ((Scheme.Modules.pullback (reesPr I X)).obj F, reesPr I X ⁻¹ᵁ V)) :
    lambdaMap I F V (theta₁ hF hV y) = unitB I F V y := by
  let _ : Module Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V) (polySec I F V) :=
    Module.compHom _ ((reesPolyMap I X).app (reesPr I X ⁻¹ᵁ V)).hom
  let L1 : Γ((Scheme.Modules.pullback (reesPr I X)).obj F, reesPr I X ⁻¹ᵁ V) →ₗ[
      Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V)] polySec I F V :=
    { toFun := fun y => lambdaMap I F V (theta₁ hF hV y)
      map_add' := fun y y' => by rw [map_add (f := _), map_add (f := _)]
      map_smul' := fun s y => by
        rw [theta₁_smul, lambdaMap_smul, reesRingHom, RingHom.comp_apply,
          polyRingInv_polyRingHom]
        rfl }
  let L2 : Γ((Scheme.Modules.pullback (reesPr I X)).obj F, reesPr I X ⁻¹ᵁ V) →ₗ[
      Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V)] polySec I F V :=
    { toFun := unitB I F V
      map_add' := map_add _
      map_smul' := fun s y => pullbackUnitApp_smul_at _ _ _ s y }
  obtain ⟨ψ, -, huniq⟩ := isBaseChangeAt_reesPr (I := I) hF hV (polySec I F V)
    ((unitB I F V).comp (unitPr I F V)) (fun a m => unitB_unitPr_smul a m)
  have e1 := huniq L1 (fun m => by
    change lambdaMap I F V (theta₁ hF hV (unitPr I F V m)) = _
    rw [theta₁_unitPr, lambdaMap_single, pow_zero, map_one, one_smul]
    rfl)
  have e2 := huniq L2 (fun m => rfl)
  exact congrArg (fun L : _ →ₗ[Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V)] polySec I F V => L y)
    (e1.trans e2.symm)


include hF hV in
theorem lambdaMap_thetaMap (x : polySec I F V) : lambdaMap I F V (thetaMap hF hV x) = x := by
  let L3 : polySec I F V →ₗ[polyRing I V] polySec I F V :=
    { toFun := fun x => lambdaMap I F V (thetaMap hF hV x)
      map_add' := fun x x' => by rw [map_add (f := _), map_add (f := _)]
      map_smul' := fun s x => by
        rw [thetaMap_smul, lambdaMap_smul, polyRingInv_polyRingHom]
        rfl }
  obtain ⟨ψ, -, huniq⟩ := isBaseChangeAt_reesPolyMap (I := I) hF hV (polySec I F V)
    (unitB I F V) (fun s y => pullbackUnitApp_smul_at _ _ _ s y)
  have e1 := huniq L3 (fun y => by
    change lambdaMap I F V (thetaMap hF hV (unitB I F V y)) = _
    rw [thetaMap_unitB, lambdaMap_theta₁])
  have e2 := huniq LinearMap.id (fun y => rfl)
  exact congrArg (fun L : polySec I F V →ₗ[polyRing I V] polySec I F V => L x) (e1.trans e2.symm)

include hF hV in
lemma thetaMap_injective : Function.Injective (thetaMap (I := I) hF hV) :=
  Function.LeftInverse.injective (lambdaMap_thetaMap hF hV)

end

end GroundTheory.Arith.SchemeCoh
end
