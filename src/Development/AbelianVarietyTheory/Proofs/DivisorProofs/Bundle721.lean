module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle450
public import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle675
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle683
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
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle637
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

namespace GlobalTheory.BadCount

theorem embReg_of_free_permuted_summands : ∀ (K Γ V X : Type) [Field K] [Group Γ] [Finite Γ] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype X] [DecidableEq X] (ρ : Representation K Γ V) (H : Subgroup Γ) [MulAction H X], (∀ (h : H) (x : X), h • x = x → h = 1) → ∀ (A : X → Submodule K V), DirectSum.IsInternal A → (∀ (h : H) (x : X), ∀ v ∈ A x, ρ h v ∈ A (h • x)) → ∃ n : ℕ, EmbReg ρ H n ∧ n * Nat.card H = finrank K V := by
  intro K Γ V X _ _ _ _ _ _ _ _ ρ H _ hfree A hA hmap
  classical
  haveI : Fintype H := Fintype.ofFinite H
  have hinv : ∀ (g : Γ) (v : V), ρ g⁻¹ (ρ g v) = v := by
    intro g v
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  let E := LinearEquiv.ofBijective (DirectSum.coeLinearMap A) hA
  let comp : ∀ x : X, V →ₗ[K] A x := fun x =>
    (DirectSum.component K X (fun y => A y) x) ∘ₗ E.symm.toLinearMap
  have comp_apply : ∀ x v, comp x v = E.symm v x := fun x v => rfl

  have htr : ∀ (h : H) (x : X) (v : V), (comp (h • x) (ρ h v) : V) = ρ h (comp x v) := by
    intro h x v
    obtain ⟨w, rfl⟩ : ∃ w, v = E w := ⟨E.symm v, (E.apply_symm_apply v).symm⟩
    rw [comp_apply, comp_apply, E.symm_apply_apply]
    induction w using DirectSum.induction_on with
    | zero => simp
    | of y a =>
      have hE : E (DirectSum.of (fun y => A y) y a) = (a : V) := DirectSum.coeLinearMap_of A y a
      rw [hE]
      by_cases hxy : y = x
      · subst hxy
        rw [DirectSum.IsInternal.ofBijective_coeLinearMap_of_mem hA (hmap h y a a.2), DirectSum.of_eq_same]
      · have hne : h • y ≠ h • x := fun he => hxy (smul_left_cancel h he)
        rw [DirectSum.IsInternal.ofBijective_coeLinearMap_of_mem_ne hA hne (hmap h y a a.2),
          DirectSum.of_eq_of_ne (β := fun i => A i) y x a (Ne.symm hxy)]
        simp
    | add w₁ w₂ h₁ h₂ =>
      rw [map_add (f := _), map_add (f := _), map_add (f := _), DirectSum.add_apply, Submodule.coe_add, h₁, h₂,
        DirectSum.add_apply, Submodule.coe_add, map_add]
  have hzero : ∀ v : V, (∀ x, comp x v = 0) → v = 0 := by
    intro v hv
    have : E.symm v = 0 := DFinsupp.ext fun x => by rw [← comp_apply, hv]; rfl
    rw [← E.apply_symm_apply v, this, map_zero]

  let d : X → ℕ := fun x => finrank K (A x)
  have hdle : ∀ (h : H) (x : X), d x ≤ d (h • x) := by
    intro h x
    let φ : A x →ₗ[K] A (h • x) :=
      LinearMap.codRestrict (A (h • x)) ((ρ h).comp (A x).subtype) (fun a => hmap h x a a.2)
    refine LinearMap.finrank_le_finrank_of_injective (f := φ) fun a b hab => ?_
    have := congrArg (fun c : A (h • x) => ρ (h : Γ)⁻¹ (c : V)) hab
    have ha : ((φ a : A (h • x)) : V) = ρ h a := rfl
    have hb : ((φ b : A (h • x)) : V) = ρ h b := rfl
    simp only [ha, hb, hinv] at this
    exact Subtype.ext this
  have hdeq : ∀ (h : H) (x : X), d (h • x) = d x := by
    intro h x
    refine le_antisymm ?_ (hdle h x)
    have := hdle h⁻¹ (h • x)
    rwa [inv_smul_smul] at this

  let O := MulAction.orbitRel.Quotient H X
  haveI : Fintype O := Fintype.ofFinite O
  let β : H × O → X := fun p => p.1 • p.2.out
  have hβ : Function.Bijective β := by
    constructor
    · rintro ⟨h, o⟩ ⟨h', o'⟩ he
      simp only [β] at he
      have ho : o = o' := by
        have e1 : (Quotient.mk _ (h • o.out) : O) = o := by
          conv_rhs => rw [← Quotient.out_eq o]
          exact Quotient.sound (MulAction.mem_orbit _ h)
        have e2 : (Quotient.mk _ (h' • o'.out) : O) = o' := by
          conv_rhs => rw [← Quotient.out_eq o']
          exact Quotient.sound (MulAction.mem_orbit _ h')
        rw [← e1, ← e2, he]
      subst ho
      have : (h'⁻¹ * h) • o.out = o.out := by rw [mul_smul, he, inv_smul_smul]
      have := hfree _ _ this
      rw [inv_mul_eq_one] at this
      rw [this]
    · intro x
      let o : O := Quotient.mk _ x
      have hrel : o.out ∈ MulAction.orbit H x := by
        have := Quotient.exact (Quotient.out_eq o)
        exact this
      obtain ⟨g, hg⟩ := hrel
      exact ⟨(g⁻¹, o), by simp only [β, ← hg, inv_smul_smul]⟩

  let n : ℕ := ∑ o : O, d o.out
  have hdimV : finrank K V = ∑ x, d x := by
    rw [Module.finrank_eq_card_basis (hA.collectedBasis fun x => Module.finBasis K (A x)), Fintype.card_sigma]
    simp [d]
  have hcount : n * Nat.card H = finrank K V := by
    rw [hdimV, ← hβ.sum_comp d, Fintype.sum_prod_type_right]
    simp only [β, hdeq, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card, n, Finset.sum_mul]
    exact Finset.sum_congr rfl fun o _ => by ring

  let I := Σ o : O, Fin (d o.out)
  have hcard : Fintype.card I = n := by simp [I, Fintype.card_sigma, n]
  let e : Fin n ≃ I := (Fintype.equivFinOfCardEq hcard).symm
  let b : ∀ o : O, Basis (Fin (d o.out)) K (A o.out) := fun o => Module.finBasis K (A o.out)
  let fo : I → V →ₗ[K] K := fun p => (b p.1).coord p.2 ∘ₗ comp p.1.out
  let T : (V →ₗ[K] K) → V →ₗ[K] MonoidAlgebra K H := fun f =>
    ∑ h : H, (f ∘ₗ ρ (h : Γ)⁻¹).smulRight (MonoidAlgebra.single h (1 : K))
  have hT : ∀ f v, T f v = ∑ h : H, f (ρ (h : Γ)⁻¹ v) • MonoidAlgebra.single h (1 : K) := by
    intro f v; simp [T]
  have hTc : ∀ f v (h : H), (T f v).coeff h = f (ρ (h : Γ)⁻¹ v) := by
    intro f v h
    rw [hT, MonoidAlgebra.coeff_sum]
    simp [MonoidAlgebra.coeff_smul, MonoidAlgebra.coeff_single, Finsupp.single_apply]
  have hTeq : ∀ f (g : H) v, T f (ρ g v) = MonoidAlgebra.single g 1 * T f v := by
    intro f g v
    rw [hT, hT, Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft g⁻¹) _ _ fun h => ?_
    simp only [Equiv.coe_mulLeft]
    rw [mul_smul_comm, MonoidAlgebra.single_mul_single, one_mul, mul_inv_cancel_left]
    have hc : ρ (h : Γ)⁻¹ (ρ g v) = ρ ((g⁻¹ * h : H) : Γ)⁻¹ v := by
      rw [← Module.End.mul_apply, ← map_mul]
      simp [mul_assoc]
    rw [hc]
  let j : V →ₗ[K] (Fin n → MonoidAlgebra K H) := LinearMap.pi fun k => T (fo (e k))
  refine ⟨n, ⟨j, ?_, ?_⟩, hcount⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    apply hzero
    intro x
    obtain ⟨⟨h, o⟩, rfl⟩ := hβ.2 x
    have h1 : comp o.out (ρ (h : Γ)⁻¹ v) = 0 := by
      rw [← (b o).forall_coord_eq_zero_iff]
      intro i
      have hk : e (e.symm ⟨o, i⟩) = ⟨o, i⟩ := e.apply_symm_apply _
      have h5 : T (fo (e (e.symm ⟨o, i⟩))) v = 0 := congrFun hv (e.symm ⟨o, i⟩)
      rw [hk] at h5
      have h6 := congrArg (fun a => MonoidAlgebra.coeff a h) h5
      simp only [hTc] at h6
      simpa [fo] using h6
    have h2 := htr h⁻¹ (h • o.out) v
    rw [inv_smul_smul] at h2
    simp only [Subgroup.coe_inv] at h2
    rw [h1, Submodule.coe_zero] at h2
    have h3 := congrArg (ρ (h : Γ)) h2
    have h4 := hinv ((h : Γ)⁻¹) (comp (h • o.out) v : V)
    rw [inv_inv] at h4
    rw [map_zero, h4] at h3
    exact Subtype.ext h3.symm
  · intro h v i
    simp only [j, LinearMap.pi_apply]
    exact hTeq _ h v

end GlobalTheory.BadCount
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

namespace GlobalTheory.BadCount

theorem embReg_of_isBaseChange : ∀ (K L Γ V W : Type) [Field K] [Field L] [Algebra K L] [Group Γ] [Finite Γ] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] [Module L W] [IsScalarTower K L W] (f : V →ₗ[K] W), IsBaseChange L f → ∀ (ρ : Representation K Γ V) (ρ' : Representation L Γ W), (∀ g v, ρ' g (f v) = f (ρ g v)) → ∀ (H : Subgroup Γ) (n : ℕ), EmbReg ρ H n → EmbReg ρ' H n := by
  intro K L Γ V W _ _ _ _ _ _ _ _ _ _ _ f hf ρ ρ' hρ H n hE
  obtain ⟨j, hj, hje⟩ := hE
  let eK : MonoidAlgebra K H ≃ₗ[K] (H →₀ K) := MonoidAlgebra.coeffLinearEquiv K
  let eL : MonoidAlgebra L H ≃ₗ[L] (H →₀ L) := MonoidAlgebra.coeffLinearEquiv L
  let m0 : (H →₀ K) →ₗ[K] (H →₀ L) := Finsupp.mapRange.linearMap (Algebra.linearMap K L)
  let φ0 : MonoidAlgebra K H →ₗ[K] MonoidAlgebra L H :=
    (eL.restrictScalars K).symm.toLinearMap ∘ₗ m0 ∘ₗ eK.toLinearMap
  have h0 : IsBaseChange L φ0 := by
    refine (IsBaseChange.iff_of_equiv_comm eK eL (f' := m0) ?_).mpr
      (IsBaseChange.finsuppPow H (IsBaseChange.linearMap K L))
    exact LinearMap.ext fun x => (eL.apply_symm_apply (m0 (eK x))).symm
  have hφ0 : ∀ x, φ0 x = MonoidAlgebra.mapRingHom H (algebraMap K L) x := by
    intro x
    ext g
    simp [φ0, eK, eL, m0]
  let φ : (Fin n → MonoidAlgebra K H) →ₗ[K] (Fin n → MonoidAlgebra L H) := φ0.compLeft (Fin n)
  have hφ : IsBaseChange L φ := IsBaseChange.finitePow (Fin n) h0
  obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective j (LinearMap.ker_eq_bot.mpr hj)
  let j' : W →ₗ[L] (Fin n → MonoidAlgebra L H) := hf.lift (φ ∘ₗ j)
  have hj'f : ∀ v, j' (f v) = φ (j v) := fun v => hf.lift_eq _ v
  let P : (Fin n → MonoidAlgebra L H) →ₗ[L] W := hφ.lift (f ∘ₗ p)
  have hPj : ∀ w, P (j' w) = w := by
    intro w
    have : P ∘ₗ j' = LinearMap.id := hf.algHom_ext _ _ (fun v => by
      rw [LinearMap.comp_apply, hj'f]
      change hφ.lift (f ∘ₗ p) (φ (j v)) = f v
      rw [hφ.lift_eq, LinearMap.comp_apply, ← LinearMap.comp_apply p j, hp, LinearMap.id_apply])
    exact LinearMap.congr_fun this w
  refine ⟨j', fun a b hab => by rw [← hPj a, ← hPj b, hab], ?_⟩
  intro h w i
  have key : (LinearMap.proj i ∘ₗ j' ∘ₗ (ρ' h)) =
      (LinearMap.mulLeft L (MonoidAlgebra.single h (1 : L)) ∘ₗ LinearMap.proj i ∘ₗ j') := by
    refine hf.algHom_ext _ _ (fun v => ?_)
    simp only [LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.mulLeft_apply, hρ, hj'f]
    change φ0 (j (ρ h v) i) = MonoidAlgebra.single h 1 * φ0 (j v i)
    rw [hje, hφ0, hφ0, map_mul, MonoidAlgebra.mapRingHom_single, map_one]
  exact LinearMap.congr_fun key w

end GlobalTheory.BadCount
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

section Pre

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}} (φ : X' ⟶ X) [IsAffineHom φ]

def preToPair : AffOp X ⥤ (Pair φ)ᵒᵖ :=
  (Monotone.functor (f := fun U : X.affineOpens ↦ prePair φ U) fun _ _ h ↦
    (show prePair φ _ ≤ prePair φ _ from ⟨preU_mono φ h, h⟩)).op

def pairToPre (s' : X' ⟶ Sp R') : CoefMap (RingHom.id R') (OPair φ s') (OPre φ s') where
  G := preToPair φ
  α _ := RingHom.id _
  naturality _ _ := rfl
  smul _ _ _ := rfl

def preToPairRes (s' : X' ⟶ Sp R') : CoefMap (RingHom.id R') (OPre φ s') (OPair φ s') where
  G := pairSnd φ
  α p := (Sec.res s' p.unop.2 : Sec s' (preU φ p.unop.1.2).1 →ₐ[R'] Sec s' p.unop.1.1.1).toRingHom
  naturality {p q} a b := by
    exact (Sec.res_res s' (U := (preU φ p.unop.1.2).1) _ _ b).symm.trans (Sec.res_res s' _ _ b)
  smul p r b := map_smul (Sec.res s' p.unop.2) r b

end Pre

section Lemmas

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}} {φ : X' ⟶ X} [IsAffineHom φ]
  {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {σ : R →+* R'}

theorem pairToPre_pull1_pairRes (x : HO1 s') :
    (pairToPre φ s').pull1 ((pairRes φ s').pull1 x) = (preRes φ s').pull1 x := by
  rw [← CoefMap.pullCohomologyOne_comp]
  exact CoefMap.pullCohomologyOne_eq_of_natTrans _ _ { app U := 𝟙 _ } (fun U b ↦ mp_id (OAff s') _ b) x

theorem pairToPre_pull2_pairRes (x : HO2 s') :
    (pairToPre φ s').pull2 ((pairRes φ s').pull2 x) = (preRes φ s').pull2 x := by
  rw [← CoefMap.pullCohomologyTwo_comp]
  exact CoefMap.pullCohomologyTwo_eq_of_natTrans _ _ { app U := 𝟙 _ } (fun U b ↦ mp_id (OAff s') _ b) x

def preIncl : pairSnd φ ⋙ preAff φ ⟶ pairFst φ where
  app p := (homOfLE p.unop.2).op

theorem preToPairRes_pull1_preRes (x : HO1 s') :
    (preToPairRes φ s').pull1 ((preRes φ s').pull1 x) = (pairRes φ s').pull1 x := by
  rw [← CoefMap.pullCohomologyOne_comp]
  exact CoefMap.pullCohomologyOne_eq_of_natTrans _ _ preIncl (fun _ _ ↦ rfl) x

theorem preToPairRes_pull2_preRes (x : HO2 s') :
    (preToPairRes φ s').pull2 ((preRes φ s').pull2 x) = (pairRes φ s').pull2 x := by
  rw [← CoefMap.pullCohomologyTwo_comp]
  exact CoefMap.pullCohomologyTwo_eq_of_natTrans _ _ preIncl (fun _ _ ↦ rfl) x

variable (h : φ ≫ s = s' ≫ spMap σ)

theorem pairToPre_pull1_pairPull (y : HO1 s) :
    (pairToPre φ s').pull1 ((pairPull h).pull1 y) = (preCoef h).pull1 y := by
  rw [← CoefMap.pullCohomologyOne_comp]
  exact CoefMap.pullCohomologyOne_eq_of_natTrans _ _ { app U := 𝟙 _ } (fun U b ↦ congrArg _ (mp_id (OAff s) _ b)) y

theorem pairToPre_pull2_pairPull (y : HO2 s) :
    (pairToPre φ s').pull2 ((pairPull h).pull2 y) = (preCoef h).pull2 y := by
  rw [← CoefMap.pullCohomologyTwo_comp]
  exact CoefMap.pullCohomologyTwo_eq_of_natTrans _ _ { app U := 𝟙 _ } (fun U b ↦ congrArg _ (mp_id (OAff s) _ b)) y

theorem preToPairRes_preα (q : (Pair φ)ᵒᵖ) (b : (OAff s).obj ((pairSnd φ).obj q)) :
    (preToPairRes φ s').α q (preα φ s s' ((pairSnd φ).obj q) b) = (pairPull h).α q b :=
  congrArg (fun t ↦ t.hom b) (φ.appLE_map _ (homOfLE q.unop.2).op)

end Lemmas

theorem red_iff_pre : ∀ (R R' : Type) [CommRing R] [CommRing R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (σ : R →+* R') (φ : X' ⟶ X) (h : φ ≫ s = s' ≫ spMap σ) [IsAffineHom φ], (∀ (f : C1 (OAff s)) (x : HO1 s'), Red1 h f x ↔ ∃ c : Z1 (OPre φ s'), (∀ U V (a : U ⟶ V), c.1 U V a = preα φ s s' V (f U V a)) ∧ GlobalTheory.CatCoh.H1.mk _ c = (preRes φ s').pull1 x) ∧ (∀ (v : C2 (OAff s)) (z : HO2 s'), Red2 h v z ↔ ∃ c : Z2 (OPre φ s'), (∀ U V W (a : U ⟶ V) (b : V ⟶ W), c.1 U V W a b = preα φ s s' W (v U V W a b)) ∧ GlobalTheory.CatCoh.H2.mk _ c = (preRes φ s').pull2 z) ∧ (∀ y, (preRes φ s').pull1 (pullHO1 h y) = (preCoef h).pull1 y) ∧ ∀ y, (preRes φ s').pull2 (pullHO2 h y) = (preCoef h).pull2 y := by
  intro R R' _ _ X X' s s' σ φ h _
  refine ⟨fun f x ↦ ⟨?_, ?_⟩, fun v z ↦ ⟨?_, ?_⟩, fun y ↦ ?_, fun y ↦ ?_⟩
  · rintro ⟨c, hc, hx⟩
    refine ⟨(pairToPre φ s').pullbackOneCocycle c, fun U V a ↦ hc _ _ _, ?_⟩
    rw [← CoefMap.pullCohomologyOne_class, hx, pairToPre_pull1_pairRes]
  · rintro ⟨c, hc, hx⟩
    refine ⟨(preToPairRes φ s').pullbackOneCocycle c, fun p q a ↦ ?_, ?_⟩
    · rw [CoefMap.pullCocycleOne_apply, hc]
      exact preToPairRes_preα h q _
    · rw [← CoefMap.pullCohomologyOne_class, hx, preToPairRes_pull1_preRes]
  · rintro ⟨c, hc, hx⟩
    refine ⟨(pairToPre φ s').pullbackTwoCocycle c, fun U V W a b ↦ hc _ _ _ _ _, ?_⟩
    rw [← CoefMap.pullCohomologyTwo_class, hx, pairToPre_pull2_pairRes]
  · rintro ⟨c, hc, hx⟩
    refine ⟨(preToPairRes φ s').pullbackTwoCocycle c, fun p q r a b ↦ ?_, ?_⟩
    · rw [CoefMap.pullCocycleTwo_apply, hc]
      exact preToPairRes_preα h r _
    · rw [← CoefMap.pullCohomologyTwo_class, hx, preToPairRes_pull2_preRes]
  · have e := congrArg (pairToPre φ s').pull1 (isPullO_pullHO1 h y)
    rw [pairToPre_pull1_pairPull, pairToPre_pull1_pairRes] at e
    exact e.symm
  · have e : (pairRes φ s').pull2 (pullHO2 h y) = (pairPull h).pull2 y :=
      (LinearEquiv.ofBijective (pairRes φ s').pull2 (pairRes_pull2_bijective φ s')).apply_symm_apply _
    have e' := congrArg (pairToPre φ s').pull2 e
    rw [pairToPre_pull2_pairPull, pairToPre_pull2_pairRes] at e'
    exact e'

end GlobalTheory.AbCoh
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

theorem mem_map_of_smul_eq_zero_of_flat {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S] (t : R) (J : Ideal R) (hJ : ∀ a, a ∈ J ↔ a * t = 0) (b : S) (hb : t • b = 0) :
    b ∈ J.map (algebraMap R S) := by
  let f : J →ₗ[R] R := J.subtype
  let g : R →ₗ[R] R := LinearMap.mulLeft R t
  have ex : Function.Exact f g := by
    intro y
    change t * y = 0 ↔ y ∈ Set.range f
    rw [_root_.mul_comm, ← hJ]
    exact ⟨fun hy ↦ ⟨⟨y, hy⟩, rfl⟩, fun ⟨x, hx⟩ ↦ hx ▸ x.2⟩
  have ex' := Module.Flat.lTensor_exact S ex
  have h0 : g.lTensor S (b ⊗ₜ[R] (1 : R)) = 0 := by
    rw [LinearMap.lTensor_tmul]
    change b ⊗ₜ[R] (t * 1) = 0
    rw [_root_.mul_one, ← _root_.mul_one t, ← smul_eq_mul, ← TensorProduct.smul_tmul, hb,
      TensorProduct.zero_tmul]
  obtain ⟨y, hy⟩ := (ex' _).1 h0
  have key : ∀ y : S ⊗[R] J, TensorProduct.rid R S (f.lTensor S y) ∈ J.map (algebraMap R S) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul s j =>
      rw [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, Algebra.smul_def]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ j.2)
    | add x z hx hz => rw [map_add (f := _), map_add (f := _)]; exact add_mem hx hz
  have := key y
  rwa [hy, TensorProduct.rid_tmul, _root_.one_smul] at this

theorem mem_map_ann_iff {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    (t : R) (J : Ideal R) (hJ : ∀ a, a ∈ J ↔ a * t = 0) (b : S) :
    b ∈ J.map (algebraMap R S) ↔ t • b = 0 := by
  refine ⟨fun hb ↦ ?_, mem_map_of_smul_eq_zero_of_flat t J hJ b⟩
  rw [Algebra.smul_def]
  induction hb using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    rw [← map_mul, _root_.mul_comm, (hJ a).1 ha, map_zero]
  | zero => exact MulZeroClass.mul_zero _
  | add x y _ _ hx hy => rw [_root_.mul_add, hx, hy, _root_.add_zero]
  | smul a x _ hx => rw [smul_eq_mul, _root_.mul_left_comm, hx, MulZeroClass.mul_zero]

theorem mem_map_span_singleton_iff {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (t : R) (b : S) :
    b ∈ (Ideal.span {t}).map (algebraMap R S) ↔ ∃ c : S, b = t • c := by
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨a, rfl⟩; exact ⟨a, by rw [Algebra.smul_def, _root_.mul_comm]⟩
  · rintro ⟨c, rfl⟩; exact ⟨c, by rw [Algebra.smul_def, _root_.mul_comm]⟩

end GlobalTheory.AbCoh

namespace GlobalTheory.AbCoh

theorem preα_surjective_and_ker : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : IsPullback φ s' s (spMap σ)) (h₀ : IsPullback φ₀ s₀ s (spMap σ₀)) [IsAffineHom φ] [IsAffineHom φ₀], SmallExt t σ σ₀ → Flat s → ∀ U : AffOp X, Function.Surjective (preα φ s s' U) ∧ (∀ b, preα φ s s' U b = 0 ↔ ∃ c, b = t • c) ∧ Function.Surjective (preα φ₀ s s₀ U) ∧ ∀ b : (OAff s).obj U, preα φ₀ s s₀ U b = 0 ↔ t • b = 0 := by
  intro R R' R₀ _ _ _ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ _ _ hE hF U
  obtain ⟨hσ, hk, hσ₀, hk₀⟩ := hE
  have A := secPull_surjective_and_ker R R' (Ideal.span {t}) σ hσ hk X' X s' s φ h (prePair φ U.unop) rfl
  have B := secPull_surjective_and_ker R R₀ (RingHom.ker σ₀) σ₀ hσ₀ rfl X₀ X s₀ s φ₀ h₀
    (prePair φ₀ U.unop) rfl
  haveI : Flat s := hF
  have hfl : (algebraMap R (Sec s U.unop.1)).Flat := by
    change ((s.appLE ⊤ U.unop.1 le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).Flat
    exact RingHom.Flat.comp (RingHom.Flat.of_bijective
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv))
      (Flat.flat_appLE s (isAffineOpen_top _) U.unop.2 le_top)
  haveI : Module.Flat R (Sec s U.unop.1) := hfl
  exact ⟨A.1, fun b ↦ (A.2 b).trans (mem_map_span_singleton_iff t b), B.1,
    fun b ↦ (B.2 b).trans (mem_map_ann_iff t _ (fun a ↦ RingHom.mem_ker.trans (hk₀ a)) b)⟩

end GlobalTheory.AbCoh
end
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors

namespace GlobalTheory.CMVal.ModFRat

theorem modF_rat : ∀ {E : Type} [Field E] [NumberField E] (y : (Af E)ˣ), ∃ q : ℚ, modF y = q := by
  intro E _ _ y
  refine ⟨∏ᶠ v : HeightOneSpectrum (𝓞 E), ((Ideal.absNorm v.asIdeal : ℕ) : ℚ) ^ (WithZero.log (Valued.v ((y : Af E) v))), ?_⟩
  have h := MonoidHom.map_finprod_of_injective ((Rat.castHom ℝ : ℚ →+* ℝ) : ℚ →* ℝ) Rat.cast_injective
    (fun v : HeightOneSpectrum (𝓞 E) => ((Ideal.absNorm v.asIdeal : ℕ) : ℚ) ^ (WithZero.log (Valued.v ((y : Af E) v))))
  simp only [MonoidHom.coe_coe, Rat.coe_castHom, Rat.cast_zpow, Rat.cast_natCast] at h
  rw [h]
  rfl

end GlobalTheory.CMVal.ModFRat
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.ainfSquareZeroFrame_invariant_eq_zero_of_tau_dvd : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k h : ℕ) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B), IsUnit U → IsNil F.θ F.σ (U.transpose⁻¹ * blk d k 1 (p : F.B)) → IsNil F.θ F.σ (U * blk d k (p : F.B) 1) → (∀ Y : Matrix (Fin d ⊕ Fin k) (Fin h) F.B, Y.map F.σ = blk d k (p : F.B) 1 * U.transpose * Y → (∀ i m, F.τ ∣ Y i m) → Y = 0) ∧ ∀ g : Fin d ⊕ Fin k → F.B, Matrix.mulVec (U * blk d k (p : F.B) 1) (fun i => F.σ (g i)) = (p : F.B) • g → (∀ i, F.τ ∣ g i) → g = 0 := by
  first | exact @GlobalTheory.TauUniq.eq_zero_of_tau_dvd | exact GlobalTheory.TauUniq.eq_zero_of_tau_dvd | (intros; apply GlobalTheory.TauUniq.eq_zero_of_tau_dvd <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.exists_ainf_frame_lift_twisted_frobenius : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ u : F.B, F.τ ∣ u - 1 → ∃ l : F.B, F.τ ∣ l - 1 ∧ F.σ l = u * l := by
  first | exact @GlobalTheory.FLam.exists_lam | exact GlobalTheory.FLam.exists_lam | (intros; apply GlobalTheory.FLam.exists_lam <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.quasiLog_first_block_small_of_frobenius : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), IsBasis μ' e → IsAdapted F.θ μ' e → ∀ U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B, (∀ i, In (⊤ : Ideal F.B) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e) ∧ ∀ i', i = Sum.inl i' → In (Ideal.span {(p : F.B)}) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e)) → ∀ w : Fin d ⊕ Fin k → F.B, (∀ l, ¬IsUnit (F.θ (U.mulVec (fun j => F.σ (w j)) l))) → ∀ i, ¬IsUnit (F.θ (w (Sum.inl i))) := by
  first | exact @GlobalTheory.QLog.small_first_of_frob | exact GlobalTheory.QLog.small_first_of_frob | (intros; apply GlobalTheory.QLog.small_first_of_frob <;> assumption)
end
