module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle016
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle020
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionLinCombFiberProductSeparated
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIsoAppTopOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle004
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle018
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SecLifts

theorem mk_mem_ker_factor {R : Type} [CommRing R] {I J : Ideal R} (h : I ≤ J) (x : R) :
    Ideal.Quotient.mk I x ∈ RingHom.ker (Ideal.Quotient.factor h) ↔ x ∈ J := by
  rw [RingHom.mem_ker, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]

theorem exists_closedFibre (V : Type) [CommRing V] (I : Ideal V)
    (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (V ⧸ I ^ (e + 1)))))
    (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left)
    (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans V I e))
    (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e)))
    (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen) (e : ℕ) :
    ∃ j : (Y 0).left ⟶ (Y (e + 1)).left,
      IsPullback j (Y 0).hom (Y (e + 1)).hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (by omega) : I ^ (e + 1 + 1) ≤ I ^ (0 + 1))))) ∧
      ∃ w : LB.Iso (N 0) ((N (e + 1)).pull j), w.IsGen := by
  induction e with
  | zero => exact ⟨β 0, hβ 0, v 0, (hN 0).2⟩
  | succ e ih =>
    obtain ⟨j, hj, w, hw⟩ := ih
    have g := (isGen_iff _).1 (hN (e + 1)).2
    have g' := (isGen_iff _).1 hw
    obtain ⟨w'', T⟩ := exists_comp (hN (e + 1)).1 (v (e + 1)) w g g' (hN (e + 1 + 1)).1 (hN 0).1
    refine ⟨j ≫ β (e + 1), ?_, w'', (isGen_iff _).2 (T.pgen_comp (hN (e + 1)).1 g g')⟩
    have h := hj.paste_horiz (hβ (e + 1))
    rw [thickTrans, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.factor_comp] at h
    exact h

theorem exists_compatible_sections : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans V (IsLocalRing.maximalIdeal V) e)) → (∀ e, Flat (Y e).hom) → ∀ (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))), (∀ e, (N e).IsLB ∧ (v e).IsGen) → FirstCohomologyVanishes (N 0) → ∀ s₀ : LB.Sec (N 0), ∃ s : ∀ e, LB.Sec (N e), s 0 = s₀ ∧ ∀ e, (∀ z (k : (N (e + 1)).ι) (k' : (N e).ι), (β e) z ∈ (N (e + 1)).U k → z ∈ (N e).U k' → gs (β e) z _ ((s (e + 1)).f k) = (Geo.Tor.gw (v e) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s e).f k')) := by
  intro V _ _ _ Y β hβ hfl N v hN h1 s₀
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hm : IsLocalRing.maximalIdeal V = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  have hmem : ∀ (n : ℕ) (x : V), x ∈ IsLocalRing.maximalIdeal V ^ n ↔ ϖ ^ n ∣ x := fun n x => by
    rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have step : ∀ e (s' : LB.Sec (N e)), ∃ s : LB.Sec (N (e + 1)),
      ∀ z (k : (N (e + 1)).ι) (k' : (N e).ι), (β e) z ∈ (N (e + 1)).U k → z ∈ (N e).U k' →
        gs (β e) z _ (s.f k) = (Geo.Tor.gw (v e) (𝟙 _) z k k').val * gs (𝟙 _) z _ (s'.f k') := by
    intro e s'
    obtain ⟨j, hj, w, hw⟩ := exists_closedFibre V _ Y β hβ N v hN e
    refine GlobalTheory.T.exists_sec_lift_alt _ _ _ _ _ (Ideal.Quotient.mk _ (ϖ ^ (e + 1))) (Ideal.Quotient.factor_surjective _)
      (Ideal.Quotient.factor_surjective _) ?_ ?_ ?_ ?_ _ _ _ _ _ _ j (β e) (hfl (e + 1)) hj (hβ e)
      (N (e + 1)) (N 0) w (hN (e + 1)).1 (hN 0).1 hw h1 (N e) (v e) (hN e).1 (hN e).2 s'
    · refine ⟨e + 1 + 1, ?_⟩
      have hle : RingHom.ker (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (by omega) : IsLocalRing.maximalIdeal V ^ (e + 1 + 1) ≤
          IsLocalRing.maximalIdeal V ^ (0 + 1))) ≤ (IsLocalRing.maximalIdeal V).map (Ideal.Quotient.mk _) := by
        intro x hx
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
        rw [mk_mem_ker_factor, zero_add, pow_one] at hx
        exact Ideal.mem_map_of_mem _ hx
      refine le_bot_iff.1 ((Ideal.pow_right_mono hle _).trans ?_)
      rw [← Ideal.map_pow, Ideal.map_quotient_self]
    · ext x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [mk_mem_ker_factor, hmem, Ideal.mem_span_singleton]
      refine ⟨fun h => map_dvd _ h, fun ⟨y, hy⟩ => ?_⟩
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [← map_mul, Ideal.Quotient.eq, hmem] at hy
      have h₁ : ϖ ^ (e + 1) ∣ x - ϖ ^ (e + 1) * y := (pow_dvd_pow ϖ (Nat.le_succ _)).trans hy
      simpa using h₁.add (dvd_mul_right (ϖ ^ (e + 1)) y)
    · rw [mk_mem_ker_factor, hmem]
      exact pow_dvd_pow ϖ (by omega)
    · intro x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [mk_mem_ker_factor, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, hmem, hmem, zero_add, pow_one, pow_succ,
        mul_dvd_mul_iff_left (pow_ne_zero _ hϖ.ne_zero)]
  choose L hL using step
  exact ⟨fun e => Nat.rec (motive := fun e => LB.Sec (N e)) s₀ L e, rfl, fun e => hL e _⟩

end GlobalTheory.SecLifts
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.FiniteCover

variable {X X' : Scheme.{0}} [IsIntegral X] [IsIntegral X']

abbrev toField {U : X.Opens} (h : genericPoint X ∈ U) : Γ(X, U) →+* X.functionField :=
  (X.presheaf.germ U (genericPoint X) h).hom

theorem generic_mem {U : X.Opens} {x : X} (h : x ∈ U) : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr ⟨x, trivial, h⟩

theorem generic_inf {U V : X.Opens} (hU : genericPoint X ∈ U) (hV : genericPoint X ∈ V) :
    genericPoint X ∈ U ⊓ V := ⟨hU, hV⟩

theorem generic_top : genericPoint X ∈ (⊤ : X.Opens) := trivial

theorem toField_rs {U V : X.Opens} (h : V ≤ U) (hV : genericPoint X ∈ V) (a : Γ(X, U)) :
    toField hV (rs X h a) = toField (h hV) a :=
  X.presheaf.germ_res_apply (homOfLE h) _ hV a

theorem toField_injective {U : X.Opens} (h : genericPoint X ∈ U) :
    Function.Injective (toField h) := germ_injective_of_isIntegral X _ h

theorem exists_toField_eq {D : X.Opens} (hD : genericPoint X ∈ D) {I : Type} (O : I → X.Opens)
    (hO : ∀ a, O a ≤ D) (hc : D ≤ ⨆ a, O a) (hη : ∀ a, genericPoint X ∈ O a) (x : X.functionField)
    (hx : ∀ a, ∃ y, toField (hη a) y = x) : ∃ y, toField hD y = x := by
  choose y hy using hx
  obtain ⟨z, hz, -⟩ := X.sheaf.existsUnique_gluing' O D (fun a => homOfLE (hO a)) hc y
    fun a b => toField_injective (U := O a ⊓ O b) (generic_inf (hη a) (hη b))
      (((toField_rs inf_le_left _ _).trans (hy a)).trans ((toField_rs inf_le_right _ _).trans (hy b)).symm)
  obtain ⟨a, -⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc hD)
  exact ⟨z, (toField_rs (hO a) (hη a) z).symm.trans ((congrArg _ (hz a)).trans (hy a))⟩

theorem toField_appLE (φ : X' ⟶ X) [IsDominant φ] {U : X.Opens} {V : X'.Opens} (e : V ≤ φ ⁻¹ᵁ U)
    (hU : genericPoint X ∈ U) (hV : genericPoint X' ∈ V) (a : Γ(X, U)) :
    toField hV ((φ.appLE U V e).hom a) = functionFieldMap φ (toField hU a) := by
  have h₁ : toField hV ((φ.appLE U V e).hom a) = toField (e hV) ((φ.app U).hom a) :=
    toField_rs e hV _
  rw [h₁, functionFieldMap, CommRingCat.hom_comp, RingHom.comp_apply]
  erw [TopCat.Presheaf.germ_stalkSpecializes_apply]
  exact (Scheme.Hom.germ_stalkMap_apply φ U (genericPoint X') (e hV) a).symm

variable {M : LB X} {k₀ : M.ι} (h₀ : genericPoint X ∈ M.U k₀)

def secVal {V : X.Opens} (hV : genericPoint X ∈ V) (σ : SecOn M V) : X.functionField :=
  toField (U := V ⊓ M.U k₀) (generic_inf (hV) (h₀)) (GlobalTheory.LB.coord σ k₀)

theorem toField_coord {V : X.Opens} (hV : genericPoint X ∈ V) (σ : SecOn M V) {k : M.ι}
    (hk : genericPoint X ∈ M.U k) :
    toField (U := V ⊓ M.U k) (generic_inf (hV) (hk)) (GlobalTheory.LB.coord σ k) =
      toField (U := M.U k ⊓ M.U k₀) (generic_inf (hk) (h₀)) (M.g k k₀).val * secVal h₀ hV σ := by
  have e := congrArg (toField (U := V ⊓ M.U k ⊓ M.U k₀) (generic_inf (generic_inf hV hk) h₀))
    (SecOn.compat σ k k₀ (O := V ⊓ M.U k ⊓ M.U k₀) inf_le_left (inf_le_inf_right _ inf_le_left)
      (inf_le_inf_right _ inf_le_right))
  rw [map_mul, toField_rs, toField_rs, toField_rs] at e
  exact e

theorem secVal_injective {V : X.Opens} (hV : genericPoint X ∈ V) :
    Function.Injective (secVal h₀ hV) := fun σ τ h => GlobalTheory.LB.sec_ext fun k => by
  by_cases hk : genericPoint X ∈ M.U k
  · refine toField_injective (U := V ⊓ M.U k) (generic_inf (hV) (hk)) ?_
    rw [toField_coord h₀ hV σ hk, toField_coord h₀ hV τ hk, h]
  · have : V ⊓ M.U k = ⊥ := eq_bot_iff.2 fun x hx => (hk (generic_mem hx.2)).elim
    have : Subsingleton Γ(X, V ⊓ M.U k) := this ▸ inferInstance
    exact Subsingleton.elim _ _

theorem secVal_restrict {V W : X.Opens} (h : W ≤ V) (hW : genericPoint X ∈ W) (σ : SecOn M V) :
    secVal h₀ hW (SecOn.restrict M h σ) = secVal h₀ (h hW) σ :=
  toField_rs (inf_le_inf_right _ h) _ _

theorem secVal_smul {V : X.Opens} (hV : genericPoint X ∈ V) (a : Γ(X, V)) (σ : SecOn M V) :
    secVal h₀ hV (a • σ) = toField hV a * secVal h₀ hV σ :=
  (map_mul (toField (U := V ⊓ M.U k₀) (generic_inf (hV) (h₀))) (rs X inf_le_left a) _).trans
    (congrArg (· * secVal h₀ hV σ) (toField_rs _ _ _))

theorem secVal_add {V : X.Opens} (hV : genericPoint X ∈ V) (σ τ : SecOn M V) :
    secVal h₀ hV (σ + τ) = secVal h₀ hV σ + secVal h₀ hV τ :=
  map_add (toField (U := V ⊓ M.U k₀) (generic_inf (hV) (h₀))) _ _

theorem exists_secVal_eq_iff (hM : M.IsLB) {I : Type} (D : I → X.Opens) (hc : ⊤ ≤ ⨆ i, D i)
    (hη : ∀ i, genericPoint X ∈ D i) (τ : ∀ i, SecOn M (D i))
    (hτ : ∀ i k, IsUnit (GlobalTheory.LB.coord (τ i) k)) (x : X.functionField) :
    (∃ σ : SecOn M ⊤, secVal h₀ generic_top σ = x) ↔
      ∀ i, ∃ a ∈ (toField (hη i)).range, x = a * secVal h₀ (hη i) (τ i) := by
  constructor
  · rintro ⟨σ, rfl⟩ i
    have hne : secVal h₀ (hη i) (τ i) ≠ 0 := ((hτ i k₀).map _).ne_zero
    refine ⟨secVal h₀ generic_top σ / secVal h₀ (hη i) (τ i), ?_, (div_mul_cancel₀ _ hne).symm⟩
    refine exists_toField_eq (hη i) (fun k : {k // genericPoint X ∈ M.U k} => D i ⊓ M.U k.1)
      (fun _ => inf_le_left) (fun y hy => ?_) (fun k => (generic_inf (hη i) (k.2))) _ fun k => ?_
    · obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 (hM.cover.ge (trivial : y ∈ ⊤))
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨k, generic_mem hk⟩, hy, hk⟩
    · obtain ⟨u, hu⟩ := hτ i k.1
      refine ⟨GlobalTheory.LB.coord (SecOn.restrict M le_top σ) k.1 * u⁻¹.val, ?_⟩
      have e₁ := toField_coord h₀ (hη i) (τ i) k.2
      have e₂ := toField_coord h₀ (hη i) (SecOn.restrict M le_top σ) k.2
      have hg : toField (U := M.U k.1 ⊓ M.U k₀) (generic_inf (k.2) (h₀)) (M.g k.1 k₀).val ≠ 0 :=
        ((M.g k.1 k₀).isUnit.map _).ne_zero
      rw [map_mul, map_units_inv, hu, e₁, e₂, secVal_restrict]
      field_simp
  · intro h
    choose a ha hx using h
    choose b hb using ha
    have hv : ∀ i, secVal h₀ (hη i) (b i • τ i) = x := fun i => by
      rw [secVal_smul, hb, hx i]
    obtain ⟨σ, hσ, -⟩ := SecOn.existsUnique_glue D (fun _ => le_top) hc (fun i => b i • τ i)
      fun i j => secVal_injective h₀ (V := D i ⊓ D j) (generic_inf (hη i) (hη j)) (by
        rw [secVal_restrict, secVal_restrict, hv, hv])
    obtain ⟨i, -⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc generic_top)
    exact ⟨σ, by rw [← hv i, ← hσ i, secVal_restrict]⟩

def secValLin {K : Type} [Field K] (f : X ⟶ Spec (CommRingCat.of K)) [Algebra K X.functionField]
    (hK : ∀ r, algebraMap K X.functionField r = toField generic_top (cst f ⊤ r)) :
    SecOnR f M ⊤ →ₗ[K] X.functionField where
  toFun σ := secVal h₀ generic_top σ
  map_add' σ τ := secVal_add h₀ generic_top σ τ
  map_smul' r σ := (secVal_smul h₀ generic_top (cst f ⊤ r) σ).trans (by
    rw [RingHom.id_apply, Algebra.smul_def, hK])

theorem secVal_pull (φ : X' ⟶ X) [IsDominant φ] {V : X.Opens} (hV : genericPoint X ∈ V)
    (h₀' : genericPoint X' ∈ (M.pull φ).U fun _ => k₀) (hV' : genericPoint X' ∈ φ ⁻¹ᵁ V)
    (σ : SecOn M V) :
    secVal h₀' hV' (SecOn.pull M φ V σ) = functionFieldMap φ (secVal h₀ hV σ) :=
  toField_appLE φ _ _ _ _

end GlobalTheory.FiniteCover
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem sec_relation_descends : ∀ (S : Scheme.{0}) (B T T' : Over S) [Flat B.hom] [IsAffine T.left] [IsAffine T'.left] (ψ : T' ⟶ T), Function.Injective ψ.left.appTop.hom → ∀ (X Y₂ : Scheme.{0}) (L : LB X), L.IsLB → ∀ (K K' K'' : Type) [Fintype K] [Fintype K'] [Fintype K''] (φ : K → (Y₂ ⟶ X)) (ε : K → ℤ) (φ' : K' → ((T ⊗ B).left ⟶ X)) (ε' : K' → ℤ) (φu : K'' → ((T ⊗ B).left ⟶ X)) (εu : K'' → ℤ) (τ : (T ⊗ B).left ⟶ Y₂) (s : LB.Sec (LB.LinComb L φ ε)) (s' : LB.Sec (LB.LinComb L φ' ε')) (u : LB.Gen (LB.LinComb L φu εu)) (c c' : Γ((T ⊗ B).left, ⊤)), u.IsGen → FormEq φ' ε' (Sum.elim (fun k => τ ≫ φ k) φu) (Sum.elim ε εu) → (∀ (z : (T' ⊗ B).left) (J), Good L z J → gs (ψ ▷ B).left z ⊤ c' * sval s' (ψ ▷ B).left z J = gs (ψ ▷ B).left z ⊤ c * (sval s ((ψ ▷ B).left ≫ τ) z J * (val u (ψ ▷ B).left z J).val)) → ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ B).left), (∀ (z : Z) (J), Good L z J → gs r z ⊤ c' * sval s' r z J = gs r z ⊤ c * (sval s (r ≫ τ) z J * (val u r z J).val)) := by
  intro S B T T' _ _ _ ψ hψ X Y₂ L hL K K' K'' _ _ _ φ ε φ' ε' φu εu τ s s' u c c' hu hF h Z r z J hJ
  obtain ⟨d, hd⟩ := exists_sec_relation_defect _ X Y₂ L hL K K' K'' φ ε φ' ε' φu εu τ s s' u c c' hu hF
  have h0 := GlobalTheory.T.sec_eq_zero_of_sval_whiskerRight_zero S B T T' ψ hψ X L hL K' φ' ε' d
    (fun z J hJ => (hd _ _ z J hJ).trans (sub_eq_zero.2 (h z J hJ)))
  refine sub_eq_zero.1 ((hd Z r z J hJ).symm.trans ?_)
  refine (congrArg (gs r z _) (h0 _)).trans ((gs_eq r z _ (hJ.mem φ' r) _).trans ?_)
  exact (congrArg _ (map_zero _)).trans (map_zero _)

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem relation_of_finite_levels : ∀ (R : Type) [CommRing R] (I : Ideal R) (T B : Over (Spec (CommRingCat.of R))) [IsAffine T.left] [IsNoetherianRing Γ(T.left, ⊤)] [GrpObj B] [Smooth B.hom] [GeometricallyConnected B.hom], (∀ r ∈ I, scal T.hom r ∈ Ideal.jacobson (⊥ : Ideal Γ(T.left, ⊤))) → ∀ (X Y₂ : Scheme.{0}) (L : LB X), L.IsLB → ∀ (K K' K'' : Type) [Fintype K] [Fintype K'] [Fintype K''] (φ : K → (Y₂ ⟶ X)) (ε : K → ℤ) (φ' : K' → ((T ⊗ B).left ⟶ X)) (ε' : K' → ℤ) (φu : K'' → ((T ⊗ B).left ⟶ X)) (εu : K'' → ℤ) (τ : (T ⊗ B).left ⟶ Y₂) (s : LB.Sec (LB.LinComb L φ ε)) (s' : LB.Sec (LB.LinComb L φ' ε')) (u : LB.Gen (LB.LinComb L φu εu)) (c c' : Γ((T ⊗ B).left, ⊤)), u.IsGen → FormEq φ' ε' (Sum.elim (fun k => τ ≫ φ k) φu) (Sum.elim ε εu) → (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ B).left), (∃ ρ : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))), ρ ≫ thick R I e = r ≫ (T ⊗ B).hom) → (∀ (z : Z) (J), Good L z J → gs r z ⊤ c' * sval s' r z J = gs r z ⊤ c * (sval s (r ≫ τ) z J * (val u r z J).val))) → ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ B).left), (∀ (z : Z) (J), Good L z J → gs r z ⊤ c' * sval s' r z J = gs r z ⊤ c * (sval s (r ≫ τ) z J * (val u r z J).val)) := by
  intro R _ I T B _ _ _ _ _ hI X Y₂ L hL K K' K'' _ _ _ φ ε φ' ε' φu εu τ s s' u c c' hu hF h Z r z J hJ
  obtain ⟨d, hd⟩ := exists_sec_relation_defect _ X Y₂ L hL K K' K'' φ ε φ' ε' φu εu τ s s' u c c' hu hF
  have h0 := sec_eq_zero_of_sval_finite_level R I T B hI X L hL K' φ' ε' d (fun e Z r hr z J hJ => by
    rw [hd Z r z J hJ, h e Z r hr z J hJ, sub_self])
  rw [← sub_eq_zero, ← hd Z r z J hJ]
  exact (congrArg (gs r z _) (h0 _)).trans ((gs_eq r z _ (hJ.mem φ' r) _).trans ((congrArg _ (map_zero _)).trans (map_zero _)))

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.section_lin_comb_fiber_product_separated : ∀ (F : Type) [Field F] (Z : Scheme.{0}) (L : LB Z), L.IsLB → ∀ (Y₁ Y₂ : Over (Spec (CommRingCat.of F))) [QuasiCompact Y₁.hom] [IsSeparated Y₁.hom] [QuasiCompact Y₂.hom] [IsSeparated Y₂.hom] (K₁ K₂ : Type) [Fintype K₁] [Fintype K₂] (φ₁ : K₁ → (Y₁.left ⟶ Z)) (ε₁ : K₁ → ℤ) (φ₂ : K₂ → (Y₂.left ⟶ Z)) (ε₂ : K₂ → ℤ), (∀ v : LB.Sec (LB.LinComb L (K := K₁ ⊕ K₂) (Sum.elim (fun k => (fst Y₁ Y₂).left ≫ φ₁ k) (fun k => (snd Y₁ Y₂).left ≫ φ₂ k)) (Sum.elim ε₁ ε₂)), ∃ (n : ℕ) (a : Fin n → LB.Sec (LB.LinComb L φ₁ ε₁)) (b : Fin n → LB.Sec (LB.LinComb L φ₂ ε₂)), ∀ (T : Scheme.{0}) (r : T ⟶ (Y₁ ⊗ Y₂).left) (z : T) (J), Good L z J → sval v r z J = ∑ i, sval (a i) (r ≫ (fst Y₁ Y₂).left) z J * sval (b i) (r ≫ (snd Y₁ Y₂).left) z J) ∧ ∀ (n : ℕ) (a : Fin n → LB.Sec (LB.LinComb L φ₁ ε₁)) (b : Fin n → LB.Sec (LB.LinComb L φ₂ ε₂)), (∀ c : Fin n → F, (∀ j, ∑ i, resTop _ (scal Y₁.hom (c i)) * (a i).f j = 0) → c = 0) → (∀ (z : (Y₁ ⊗ Y₂).left) (J), Good L z J → ∑ i, sval (a i) (fst Y₁ Y₂).left z J * sval (b i) (snd Y₁ Y₂).left z J = 0) → ∀ i j, (b i).f j = 0 := by
  first | exact @GlobalTheory.SectionsProduct.main | exact GlobalTheory.SectionsProduct.main | (intros; apply GlobalTheory.SectionsProduct.main <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ExpansionTotal

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange

theorem globalFns : GlobalFnsSt :=
  GlobalFunctions.globalFns_of forall_geometricallyIntegral_of_smooth_of_geometricallyConnected
    FlatFibreInjective.injective_baseChange exists_noetherian_model_of_smooth

variable {R : Type} [CommRing R] [IsDomain R] {F F' : Type} [Field F] [Algebra (FractionRing R) F]
  [Field F'] [Algebra (FractionRing R) F'] (θ : TF (R := R) F ⟶ TF (R := R) F') (D : DegPre R)

def toBK : DegPre.BF D F ⟶ DegPre.BF D F' := lift (fst _ _ ≫ θ) (snd _ _)

theorem toBK_fst : toBK θ D ≫ fst _ _ = fst _ _ ≫ θ := lift_fst _ _

theorem toBK_prB : toBK θ D ≫ DegPre.prB D F' = DegPre.prB D F := lift_snd _ _

theorem famφ_eq (α : D.X) (i : Fin 4) :
    DegPre.famφ D F α i = (toBK θ D).left ≫ DegPre.famφ D F' α i := by
  have e₀ := toBK_prB θ D
  have e₂ := comp_cP D (toBK θ D) α
  fin_cases i
  · exact congrArg (fun q => q.left) e₀.symm
  · exact congrArg (fun q => q.left) ((MonObj.comp_mul (toBK θ D) (DegPre.prB D _) (cP D _ α)).trans
      (congrArg₂ (· * ·) e₀ e₂)).symm
  · exact congrArg (fun q => q.left) e₂.symm
  · exact congrArg (fun q : DegPre.BF D F ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) (toBK θ D)).symm

theorem trF_toBK (mu : D.X) :
    DegPre.trF D F mu ≫ toBK θ D = toBK θ D ≫ DegPre.trF D F' mu := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, toBK_fst, Category.assoc, trF_eq, trF_eq, tr_fst, toBK_fst, ← Category.assoc, tr_fst]
  · refine (Category.assoc _ _ _).trans ((congrArg _ (toBK_prB θ D)).trans (Eq.trans ?_ (Category.assoc _ _ _).symm))
    rw [trF_eq, trF_eq, tr_pr]
    refine Eq.trans ?_ (congrArg (toBK θ D ≫ ·) (tr_pr D F' (cP D _ mu))).symm
    rw [MonObj.comp_mul, toBK_prB, comp_cP, comp_cP, comp_cP]

theorem exists_famPull (hθ : θ.left ≫ jFK (R := R) F' = jFK (R := R) F) (k : ℕ) (S : Fam D F' k) : ∃ S' : Fam D F k,
    ∀ (α : D.X) (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J), Good D.P.L z J →
      sval (S'.s α) r z J = sval (S.s α) (r ≫ (toBK θ D).left) z J := by
  have hp : (toBK θ D).left ≫ (DegPre.BF D F').hom =
      (DegPre.BF D F).hom ≫ Spec.map (CommRingCat.ofHom (RingHom.id R)) :=
    (Over.w _).trans ((Category.comp_id _).symm.trans (congrArg _ (Spec.map_id _).symm))
  let s : ∀ α : D.X, LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k)) := fun α =>
    pullOver D.P.L (DegPre.famε k) hp (famφ_eq θ D α) (S.s α)
  have hs : ∀ (α : D.X) (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J), Good D.P.L z J →
      sval (s α) r z J = sval (S.s α) (r ≫ (toBK θ D).left) z J := fun α Z r z J hJ =>
    sval_pullOver hp (famφ_eq θ D α) (S.s α) r hJ
  refine ⟨⟨s, fun mu α u hu hc => (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).2 fun y J hJ => ?_⟩, hs⟩
  have e₁ := (gen_fe globalFns k mu α).2 u hu hc _ (𝟙 _) y J hJ
  obtain ⟨⟨u', hu', hc'⟩, hv'⟩ := gen_fe (D := D) (F := F') globalFns k mu α
  have e₂ := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u').1 (S.fe mu α u' hu' hc') _ (toBK θ D).left y J hJ
  rw [hv' u' hu' hc' _ (toBK θ D) y J hJ, ← Over.comp_left, ← trF_toBK, Over.comp_left] at e₂
  rw [Over.id_left] at e₁
  rw [hs _ _ _ y J hJ, hs _ _ _ y J hJ, Category.id_comp, Category.id_comp, e₂, e₁]
  have a : (toBK θ D ≫ fst _ _).left ≫ jFK (R := R) F' =
      (𝟙 (DegPre.BF D F) ≫ fst _ _).left ≫ jFK (R := R) F := by
    rw [toBK_fst, Category.id_comp, Over.comp_left, Category.assoc, hθ]
  rw [val_famMult _ hJ, val_famMult _ hJ, a, uVal, uVal, toBK_prB, comp_cP, comp_cP, comp_cP, comp_cP,
    Category.id_comp (DegPre.prB D F)]




end GlobalTheory.ExpansionTotal
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem eq_of_isGen_transl : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (b b' : TF (R := R) F ⟶ D.P.A) (r : LB.Gen (LB.LinComb D.P.L (K := Fin 2) ![(DegPre.trPt D F b ≫ DegPre.prB D F).left, (DegPre.trPt D F b' ≫ DegPre.prB D F).left] ![1, -1])), r.IsGen → b = b' := by
  intro R _ _ D F _ _ b b' r hr
  have key : b * b'⁻¹ = 1 := by
    refine D.P.ktriv F (TF (R := R) F).hom (b * b'⁻¹) fun p => ⟨⊤, trivial, ?_⟩
    have h3 : (fun i => (DegPre.trPt D F b'⁻¹).left ≫ ![(DegPre.trPt D F b ≫ DegPre.prB D F).left, (DegPre.trPt D F b' ≫ DegPre.prB D F).left] i) =
        ![(lift (fst (TF (R := R) F) D.P.A ≫ (b * b'⁻¹)) (snd (TF (R := R) F) D.P.A) ≫ μ[D.P.A]).left, (snd (TF (R := R) F) D.P.A).left] := by
      have g : ∀ m : TF (R := R) F ⟶ D.P.A, DegPre.trPt D F b'⁻¹ ≫ DegPre.trPt D F m ≫ DegPre.prB D F =
          (fst (TF (R := R) F) D.P.A ≫ (m * b'⁻¹)) * DegPre.prB D F := fun m => by
        rw [DVR.tr_pr, MonObj.comp_mul, DVR.tr_pr, ← Category.assoc, DVR.tr_fst, MonObj.comp_mul]
        exact (_root_.mul_comm _ _).trans ((congrArg _ (_root_.mul_comm _ _)).trans (_root_.mul_assoc _ _ _).symm)
      funext i
      fin_cases i
      · exact congrArg (fun q => q.left) (g b)
      · refine congrArg (fun q => q.left) ((g b').trans ?_)
        rw [mul_inv_cancel, MonObj.comp_one, _root_.one_mul]
    have h4 : ∃ w : LB.Gen (LB.LinComb D.P.L (fun i => (DegPre.trPt D F b'⁻¹).left ≫ ![(DegPre.trPt D F b ≫ DegPre.prB D F).left, (DegPre.trPt D F b' ≫ DegPre.prB D F).left] i) ![1, -1]), w.IsGen :=
      ⟨_, DVR.pullGen_isGen _ _ _ r hr _⟩
    rw [h3] at h4
    obtain ⟨w, hw⟩ := h4
    exact exists_isGen_pull (translDiff D.P.A D.P.L (b * b'⁻¹)) w hw _
  exact mul_inv_eq_one.1 key

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.kTriv_external_tensor_power_lineBundle : ∀ (S : Scheme.{0}) (G' G : Over S) [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] (j : ℕ) (p : IsPowGrp G' G j) (L : LB G.left), L.IsLB → KTriv G L → KTriv G' (boxLB L p.pr) := by
  first | exact @GlobalTheory.kTriv_boxLB | exact GlobalTheory.kTriv_boxLB | (intros; apply GlobalTheory.kTriv_boxLB <;> assumption)
end
