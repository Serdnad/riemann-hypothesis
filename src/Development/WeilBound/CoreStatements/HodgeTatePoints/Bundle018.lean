module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinitePartLePreimageOfClosedFibreSubset
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle015
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle037
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle010
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.FunctionField
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.HtPt.Twhopf

theorem finite_part : ∀ (R : Type) [CommRing R] [HenselianLocalRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) [LocallyQuasiFinite f] [LocallyOfFiniteType f] [IsSeparated f] [QuasiCompact f], ∃ U : X.Opens, IsFinite (U.ι ≫ f) ∧ ∀ x : X, f x = IsLocalRing.closedPoint R → x ∈ U := by
  intro R _ _ X f _ _ _ _
  exact ⟨GlobalTheory.finitePart f, GlobalTheory.isFinite_finitePart (R := CommRingCat.of R) f,
    GlobalTheory.mem_finitePart_of_eq_closedPoint (R := CommRingCat.of R) f⟩

theorem finite_le : ∀ (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (U U' : X.Opens), IsFinite (U.ι ≫ f) → (∀ x : X, f x = IsLocalRing.closedPoint R → x ∈ U') → U ≤ U' := by
  intro R _ _ X f U U' hU hU' x hx
  exact (GlobalTheory.preimage_eq_top_of_closedFibre_subset (R := CommRingCat.of R) f U' hU' U.ι).ge
    (Set.mem_univ ⟨x, hx⟩)

theorem mem_of_finite {R : Type} [CommRing R] [IsLocalRing R]
    {X : Over (Spec (CommRingCat.of R))} (W : X.left.Opens)
    (hW : ∀ x : X.left, X.hom x = IsLocalRing.closedPoint R → x ∈ W)
    (Y : Over (Spec (CommRingCat.of R))) (hY : IsFinite Y.hom) (h : Y ⟶ X) (z : Y.left) :
    h.left z ∈ W := by
  haveI : IsFinite (h.left ≫ X.hom) := by rw [Over.w h]; exact hY
  exact (GlobalTheory.preimage_eq_top_of_closedFibre_subset (R := CommRingCat.of R) X.hom W hW h.left).ge
    (Set.mem_univ z)

theorem finite_sub : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (T : Type) [CommGroup T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), IsFinite (U.ι ≫ Γ.G.hom) → (∀ x : Γ.G.left, Γ.G.hom x = IsLocalRing.closedPoint R → x ∈ U) → Γ.IsFinOpenSub U := by
  apply GlobalTheory.CompanionTheory.Ar.BT.QFGroup.isFinOpenSub_of_closedFibre <;> assumption

theorem mem_iff_section : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsLocalRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), IsFinite (U.ι ≫ Γ.G.hom) → (∀ g : Γ.G.left, Γ.G.hom g = IsLocalRing.closedPoint R → g ∈ U) → ∀ t, (⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U ↔ ∃ σ : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ Γ.G, toUnit (genPt R) ≫ σ = Γ.pt t) := by
  intro R _ _ _ _ T _ _ Γ U hfin hU t
  constructor
  · intro ht
    obtain ⟨σ, -, hσ⟩ := exists_section_of_generic_point R T Γ U hfin t ht
    exact ⟨σ, hσ⟩
  · rintro ⟨σ, hσ⟩ z _
    have key := mem_of_finite U hU (𝟙_ _) (show IsFinite (𝟙 _) from inferInstance) σ
      ((toUnit (genPt R)).left z)
    rw [← hσ]
    simpa using key


open Polynomial in
theorem exists_root_near (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [IsAlgClosed (FractionRing V)]
    (a₀ : V) (n : ℕ) : ∀ f : V[X], f.Monic → f.natDegree = n → f.eval a₀ ∈ IsLocalRing.maximalIdeal V →
      ∃ a, f.IsRoot a ∧ a - a₀ ∈ IsLocalRing.maximalIdeal V := by
  induction n with
  | zero =>
    intro f hf hn h
    rw [hf.natDegree_eq_zero.1 hn, eval_one] at h
    exact absurd ((Ideal.eq_top_iff_one _).2 h) (IsLocalRing.maximalIdeal.isMaximal V).ne_top
  | succ n ih =>
    intro f hf hn h
    have hinj := IsFractionRing.injective V (FractionRing V)
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_aeval_eq_zero_of_injective (FractionRing V) hinj f
      (by rw [degree_eq_natDegree hf.ne_zero, hn]; exact_mod_cast n.succ_ne_zero)
    obtain ⟨r, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 (⟨f, hf, by rwa [← aeval_def]⟩ : IsIntegral V x)
    have hr : f.IsRoot r := hinj (by rw [map_zero, ← hx, aeval_algebraMap_apply_eq_algebraMap_eval])
    obtain ⟨g, rfl⟩ := dvd_iff_isRoot.2 hr
    have hg : g.Monic := (monic_X_sub_C r).of_mul_monic_left hf
    rw [eval_mul] at h
    rcases (IsLocalRing.maximalIdeal.isMaximal V).isPrime.mem_or_mem h with h | h
    · refine ⟨r, hr, ?_⟩
      have := neg_mem h
      simpa using this
    · have hd : g.natDegree = n := by
        rw [(monic_X_sub_C r).natDegree_mul hg, natDegree_X_sub_C] at hn
        omega
      obtain ⟨a, ha, ha'⟩ := ih g hg hd h
      exact ⟨a, ha.dvd (dvd_mul_left _ _), ha'⟩

theorem henselian_of_algClosed : ∀ (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [IsAlgClosed (FractionRing V)], HenselianLocalRing V := by
  intro V _ _ _ _
  exact ⟨fun f hf a₀ h _ => exists_root_near V a₀ _ f hf rfl h⟩

theorem padic_alg : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O), Nonempty (Algebra ℤ_[p] O) ∧ HenselianLocalRing O ∧ IsIntegrallyClosed O ∧ ValuationRing O ∧ IsAlgClosed (FractionRing O) ∧ IsFractionRing O C := by
  intro p _ C _ _ _ v O _ _ _ hv _ hO
  haveI := hO
  haveI hval : ValuationRing O := ValuationRing.of_integers v hv
  haveI hfr : IsFractionRing O C := hv.isFractionRing
  haveI hac : IsAlgClosed (FractionRing O) :=
    IsAlgClosed.of_ringEquiv C _ (FractionRing.algEquiv O C).symm.toRingEquiv
  exact ⟨(GlobalTheory.ChF.padicInt_algebra_of_isAdicComplete_and_matrix_unique p O).1,
    henselian_of_algClosed O, inferInstance, hval, hac, hfr⟩

theorem prime_eq_bot_or_max : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] [IsLocalRing O], v.Integers O → ∀ P : Ideal O, P.IsPrime → P = ⊥ ∨ P = IsLocalRing.maximalIdeal O := by
  intro C _ v O _ _ _ _ hv P hP
  by_cases h0 : P = ⊥
  · exact .inl h0
  right
  refine le_antisymm (IsLocalRing.le_maximalIdeal hP.ne_top) fun x hx => ?_
  obtain ⟨a, haP, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  have hx1 : v (algebraMap O C x) < 1 :=
    lt_of_le_of_ne (hv.map_le_one x) fun h => hx (hv.isUnit_of_one' h)
  have ha : 0 < v (algebraMap O C a) :=
    zero_lt_iff.2 ((Valuation.ne_zero_iff v).2 ((map_ne_zero_iff _ hv.hom_inj).2 ha0))
  obtain ⟨n, hn⟩ := NNReal.exists_pow_lt_of_lt_one ha hx1
  have hd : a ∣ x ^ n := hv.dvd_of_le (by rw [map_pow, map_pow]; exact hn.le)
  exact hP.mem_of_pow_mem n (P.mem_of_dvd hd haP)

end PositivityTheory.HtPt.Twhopf
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj

noncomputable section

namespace PositivityTheory.HtPt.Mf



theorem xr_normal : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X), IsCptGen ξ → (∀ q : X, GlobalTheory.CompanionTheory.Ar.genPt ξ ⤳ q) → IsIntegral X ∧ (Flat.NormalCpt ξ ↔ IsNormalScheme X) := by
  intro X Ω _ ξ hgen hall
  have hdom : ∀ x : X, IsDomain (X.presheaf.stalk x) := fun x =>
    Function.Injective.isDomain (genMap ξ ⟨x, hall x⟩) (hgen.inj ⟨x, hall x⟩)
  haveI : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    haveI := hdom x
    infer_instance
  haveI : AlgebraicGeometry.IsReduced X := isReduced_of_isReduced_stalk X
  haveI : IrreducibleSpace X := by
    rw [irreducibleSpace_def]
    have hcl : closure {GlobalTheory.CompanionTheory.Ar.genPt ξ} = (Set.univ : Set X) :=
      Set.eq_univ_of_forall fun q => specializes_iff_mem_closure.mp (hall q)
    rw [Set.top_eq_univ, ← hcl]
    exact isIrreducible_singleton.closure
  haveI hI : AlgebraicGeometry.IsIntegral X := isIntegral_of_irreducibleSpace_of_isReduced X
  refine ⟨hI, ?_⟩
  have key : ∀ p : Cpt ξ, IsIntegrallyClosedIn (regAt ξ p) Ω ↔ IsIntegrallyClosed (X.presheaf.stalk p.1) := by
    intro p
    let ψ : X.functionField →+* Ω :=
      (X.presheaf.stalkSpecializes (hall (genericPoint X)) ≫ Scheme.stalkClosedPointTo ξ).hom
    letI : Algebra (X.presheaf.stalk p.1) Ω := (genMap ξ p).toAlgebra
    have hcomm : ∀ r : X.presheaf.stalk p.1, ψ (algebraMap _ X.functionField r) = algebraMap _ Ω r := by
      intro r
      have hc : X.presheaf.stalkSpecializes (genericPoint_specializes p.1) ≫
          X.presheaf.stalkSpecializes (hall (genericPoint X)) = X.presheaf.stalkSpecializes p.2 :=
        TopCat.Presheaf.stalkSpecializes_comp _ _ _
      have h1 : algebraMap (X.presheaf.stalk p.1) X.functionField r =
          (X.presheaf.stalkSpecializes (genericPoint_specializes p.1)).hom r := rfl
      have h2 : algebraMap (X.presheaf.stalk p.1) Ω r =
          (X.presheaf.stalkSpecializes p.2 ≫ Scheme.stalkClosedPointTo ξ).hom r := rfl
      rw [h1, h2]
      have h3 := congrArg (fun φ => (φ ≫ Scheme.stalkClosedPointTo ξ).hom r) hc
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h3
      simp only [ψ, CommRingCat.hom_comp, RingHom.comp_apply]
      exact h3
    have hsurj : Function.Surjective ψ := by
      intro a
      obtain ⟨g, rfl⟩ := hgen.bij.2 a
      refine ⟨(X.presheaf.stalkSpecializes (genericPoint_specializes (GlobalTheory.CompanionTheory.Ar.genPt ξ))).hom g, ?_⟩
      have hc2 : X.presheaf.stalkSpecializes (genericPoint_specializes (GlobalTheory.CompanionTheory.Ar.genPt ξ)) ≫
          X.presheaf.stalkSpecializes (hall (genericPoint X)) = 𝟙 _ :=
        (TopCat.Presheaf.stalkSpecializes_comp _ _ _).trans (TopCat.Presheaf.stalkSpecializes_refl _ _)
      have h3 := congrArg (fun φ => (φ ≫ Scheme.stalkClosedPointTo ξ).hom g) hc2
      simp only [Category.id_comp, CommRingCat.hom_comp, RingHom.comp_apply] at h3
      simp only [ψ, CommRingCat.hom_comp, RingHom.comp_apply]
      exact h3
    let e : X.functionField ≃ₐ[X.presheaf.stalk p.1] Ω :=
      AlgEquiv.ofBijective { ψ with commutes' := hcomm } ⟨ψ.injective, hsurj⟩
    rw [isIntegrallyClosed_iff_isIntegrallyClosedIn X.functionField, e.isIntegrallyClosedIn]
    letI : Algebra (X.presheaf.stalk p.1) (regAt ξ p) := (genMap ξ p).rangeRestrict.toAlgebra
    haveI : IsScalarTower (X.presheaf.stalk p.1) (regAt ξ p) Ω :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    haveI : Algebra.IsIntegral (X.presheaf.stalk p.1) (regAt ξ p) :=
      Algebra.isIntegral_of_surjective (genMap ξ p).rangeRestrict_surjective
    rw [Subring.isIntegrallyClosedIn_iff, isIntegrallyClosedIn_iff]
    constructor
    · intro h
      refine ⟨hgen.inj p, fun {x} hx => ?_⟩
      exact RingHom.mem_range.mp (h hx.tower_top)
    · rintro ⟨-, h⟩ x hx
      exact RingHom.mem_range.mpr (h (isIntegral_trans x hx))
  constructor
  · intro h x
    exact ⟨inferInstance, (key ⟨x, hall x⟩).mp
      (Subring.isIntegrallyClosedIn_iff.mpr (fun a ha => h ⟨x, hall x⟩ a ha))⟩
  · intro h p a ha
    exact Subring.isIntegrallyClosedIn_iff.mp ((key p).mpr (h p.1).2) ha

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem bijective_iff_isIso_stalkMap (ξ : Sp Ω ⟶ X) (x : Sp Ω) :
    Function.Bijective (Scheme.stalkClosedPointTo ξ).hom ↔ IsIso (ξ.stalkMap x) := by
  obtain rfl : x = IsLocalRing.closedPoint Ω := Subsingleton.elim _ _
  rw [← isIso_comp_right_iff (ξ.stalkMap _) (AlgebraicGeometry.stalkClosedPointIso (CommRingCat.of Ω)).hom]
  exact (ConcreteCategory.isIso_iff_bijective _).symm

def push {W : Scheme.{0}} (ξ : Sp Ω ⟶ W) (f : W ⟶ X) (q : Cpt ξ) : Cpt (ξ ≫ f) :=
  ⟨f q.1, q.2.map f.continuous⟩

theorem genMap_push {W : Scheme.{0}} (ξ : Sp Ω ⟶ W) (f : W ⟶ X) (q : Cpt ξ) :
    genMap (ξ ≫ f) (push ξ f q) = (genMap ξ q).comp (f.stalkMap q.1).hom := by
  show (X.presheaf.stalkSpecializes _ ≫ Scheme.stalkClosedPointTo (ξ ≫ f)).hom =
    (W.presheaf.stalkSpecializes q.2 ≫ Scheme.stalkClosedPointTo ξ).hom.comp (f.stalkMap q.1).hom
  rw [← CommRingCat.hom_comp]
  congr 1
  rw [Scheme.stalkClosedPointTo_comp]
  exact Scheme.Hom.stalkSpecializes_stalkMap_assoc f _ q.1 q.2 _

theorem regAt_push {W : Scheme.{0}} (ξ : Sp Ω ⟶ W) (f : W ⟶ X) [SurjectiveOnStalks f] (q : Cpt ξ) :
    regAt (ξ ≫ f) (push ξ f q) = regAt ξ q := by
  ext a
  simp only [regAt, genMap_push, RingHom.mem_range, RingHom.comp_apply]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := f.stalkMap_surjective q.1 y
    exact ⟨x, rfl⟩

theorem isCptGen_of_comp {W : Scheme.{0}} (ξ : Sp Ω ⟶ W) (f : W ⟶ X) [SurjectiveOnStalks f]
    (h : IsCptGen (ξ ≫ f)) : IsCptGen ξ := by
  have key : ∀ {A B C : Type} (g : B → C) (s : A → B), Function.Injective (g ∘ s) →
      Function.Surjective s → Function.Injective g := by
    intro A B C g s hi hs y y' hy
    obtain ⟨x, rfl⟩ := hs y
    obtain ⟨x', rfl⟩ := hs y'
    exact congrArg s (hi hy)
  have hb : Function.Bijective ((Scheme.stalkClosedPointTo ξ).hom ∘ (f.stalkMap (ξ (closedPoint Ω))).hom) := by
    have hb0 := h.bij
    rw [Scheme.stalkClosedPointTo_comp] at hb0
    exact hb0
  refine ⟨⟨key _ _ hb.1 (f.stalkMap_surjective _), Function.Surjective.of_comp hb.2⟩, fun p => ?_⟩
  have hi : Function.Injective ((genMap ξ p) ∘ (f.stalkMap p.1).hom) := by
    have hi0 := h.inj (push ξ f p)
    rw [genMap_push] at hi0
    exact hi0
  exact key _ _ hi (f.stalkMap_surjective p.1)

end PositivityTheory.HtPt.Mf
end
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace PositivityTheory.HtPt.Mb.LNormChart.ChNorm

theorem mem_of_isIntegral_of_inv_mem {Ω : Type} [Field Ω] (R : Subring Ω) {v : Ω} (hv : IsIntegral R v)
    (hv0 : v ≠ 0) (hu : v⁻¹ ∈ R) : v ∈ R := by
  obtain ⟨p, hp, hpv⟩ := hv
  have huv : v * v⁻¹ = 1 := mul_inv_cancel₀ hv0
  have key : ∀ i m : ℕ, i ≤ m → v ^ i * v⁻¹ ^ m = v⁻¹ ^ (m - i) := by
    intro i m him
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le him
    rw [pow_add, ← mul_assoc, ← mul_pow, huv, one_pow, one_mul, Nat.add_sub_cancel_left]
  rw [hp.as_sum] at hpv
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_X_pow] at hpv
  generalize p.natDegree = n at hpv
  cases n with
  | zero => simp at hpv
  | succ m =>
    have h2 := congrArg (· * v⁻¹ ^ m) hpv
    simp only [add_mul, Finset.sum_mul, zero_mul] at h2
    rw [pow_succ, mul_comm (v ^ m) v, mul_assoc, key m m le_rfl, Nat.sub_self, pow_zero, mul_one] at h2
    have e : v = -∑ i ∈ Finset.range (m + 1), algebraMap R Ω (p.coeff i) * v⁻¹ ^ (m - i) := by
      rw [eq_neg_iff_add_eq_zero, ← h2]
      congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [mul_assoc, key i m (by simp at hi; omega)]
    rw [e]
    refine neg_mem (sum_mem fun i _ => mul_mem ?_ (pow_mem hu _))
    exact (p.coeff i).2

end PositivityTheory.HtPt.Mb.LNormChart.ChNorm

namespace PositivityTheory.HtPt.Mb.LNormChart.ChNorm

theorem chRing_join_iff {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} (x : κ → Ω)
    {d n : ℕ} (z : κ ⊕ Fin n → Ω) (hz : ∀ c, z (Sum.inl c) = x c ^ d) (c : κ) (hc : x c ≠ 0) (a : Ω) :
    a ∈ chRing o (joinCo (RingHom.id Ω) x z) (c, Sum.inl c) ↔
      a ∈ Algebra.adjoin o (Set.range (fun j => x j / x c) ∪ Set.range (fun k => z k / x c ^ d)) := by
  have hd : x c ^ d ≠ 0 := pow_ne_zero _ hc
  have hrat : ∀ q : κ × (κ ⊕ Fin n), joinCo (RingHom.id Ω) x z q / joinCo (RingHom.id Ω) x z (c, Sum.inl c) =
      x q.1 / x c * (z q.2 / x c ^ d) := by
    intro q
    simp only [joinCo, RingHom.id_apply, hz c]
    exact mul_div_mul_comm _ _ _ _
  have hT : chRing o (joinCo (RingHom.id Ω) x z) (c, Sum.inl c) =
      Algebra.adjoin o (Set.range (fun j => x j / x c) ∪ Set.range (fun k => z k / x c ^ d)) := by
    apply le_antisymm
    · apply Algebra.adjoin_le
      rintro _ ⟨q, rfl⟩
      dsimp only
      rw [hrat]
      exact mul_mem (Algebra.subset_adjoin (Or.inl ⟨q.1, rfl⟩)) (Algebra.subset_adjoin (Or.inr ⟨q.2, rfl⟩))
    · apply Algebra.adjoin_le
      rintro _ (⟨j, rfl⟩ | ⟨k, rfl⟩)
      · have h1 : joinCo (RingHom.id Ω) x z (j, Sum.inl c) / joinCo (RingHom.id Ω) x z (c, Sum.inl c) ∈
            chRing o (joinCo (RingHom.id Ω) x z) (c, Sum.inl c) :=
          Algebra.subset_adjoin (Set.mem_range_self (j, Sum.inl c))
        rw [hrat, hz c, div_self hd, mul_one] at h1
        exact h1
      · have h1 : joinCo (RingHom.id Ω) x z (c, k) / joinCo (RingHom.id Ω) x z (c, Sum.inl c) ∈
            chRing o (joinCo (RingHom.id Ω) x z) (c, Sum.inl c) :=
          Algebra.subset_adjoin (Set.mem_range_self (c, k))
        rw [hrat, div_self hc, one_mul] at h1
        exact h1
  rw [hT]

end PositivityTheory.HtPt.Mb.LNormChart.ChNorm

namespace PositivityTheory.HtPt.Mb.LNormChart.ChNorm

theorem joinCo_div {Ω : Type} [Field Ω] {κ : Type} (x : κ → Ω) {d n : ℕ} (z : κ ⊕ Fin n → Ω)
    (hz : ∀ c, z (Sum.inl c) = x c ^ d) (c : κ) (q : κ × (κ ⊕ Fin n)) :
    joinCo (RingHom.id Ω) x z q / joinCo (RingHom.id Ω) x z (c, Sum.inl c) = x q.1 / x c * (z q.2 / x c ^ d) := by
  simp only [joinCo, RingHom.id_apply, hz c]
  exact mul_div_mul_comm _ _ _ _

theorem join_chart_normalisation : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (d n : ℕ) (z : κ ⊕ Fin n → Ω) (M' : PModel o (joinCo (RingHom.id Ω) x z)), (∀ c, z (Sum.inl c) = x c ^ d) → (∀ c, x c ≠ 0 → ∀ a : Ω, IsIntegral (chRing o x c) a ↔ a ∈ Submodule.span (chRing o x c) (Set.range fun k => z k / x c ^ d)) → ∀ c, x c ≠ 0 → (∀ a : Ω, a ∈ chRing o (joinCo (RingHom.id Ω) x z) (c, Sum.inl c) ↔ IsIntegral (chRing o x c) a) ∧ ∀ p' : Cpt M'.ξ, (∀ j, x j / x c ∈ regAt M'.ξ p') → InChart M'.ξ (joinCo (RingHom.id Ω) x z) (c, Sum.inl c) p' := by
  intro o _ Ω _ _ κ _ x d n z M' hz hspan c hc
  have hd : x c ^ d ≠ 0 := pow_ne_zero _ hc
  have hyS : ∀ k, IsIntegral (chRing o x c) (z k / x c ^ d) := fun k =>
    (hspan c hc _).2 (Submodule.subset_span ⟨k, rfl⟩)
  have hxS : ∀ j, x j / x c ∈ chRing o x c := fun j => Algebra.subset_adjoin ⟨j, rfl⟩
  refine ⟨fun a => ?_, fun p' hp' => ?_⟩
  · rw [chRing_join_iff x z hz c hc a]
    constructor
    · intro ha
      have hle : Algebra.adjoin o (Set.range (fun j => x j / x c) ∪ Set.range (fun k => z k / x c ^ d)) ≤
          (integralClosure (chRing o x c) Ω).restrictScalars o := by
        apply Algebra.adjoin_le
        rintro _ (⟨j, rfl⟩ | ⟨k, rfl⟩)
        · exact (Subalgebra.mem_restrictScalars o).2 ((mem_integralClosure_iff _ _).2
            (isIntegral_algebraMap (x := (⟨_, hxS j⟩ : chRing o x c))))
        · exact (Subalgebra.mem_restrictScalars o).2 ((mem_integralClosure_iff _ _).2 (hyS k))
      exact (mem_integralClosure_iff _ _).1 ((Subalgebra.mem_restrictScalars o).1 (hle ha))
    · intro ha
      have hSle : chRing o x c ≤
          Algebra.adjoin o (Set.range (fun j => x j / x c) ∪ Set.range (fun k => z k / x c ^ d)) :=
        Algebra.adjoin_mono Set.subset_union_left
      refine Submodule.span_induction
        (p := fun b _ => b ∈ Algebra.adjoin o (Set.range (fun j => x j / x c) ∪ Set.range (fun k => z k / x c ^ d)))
        ?_ ?_ ?_ ?_ ((hspan c hc a).1 ha)
      · rintro _ ⟨k, rfl⟩
        exact Algebra.subset_adjoin (Or.inr ⟨k, rfl⟩)
      · exact zero_mem _
      · intro a b _ _ ha hb
        exact add_mem ha hb
      · intro s b _ hb
        rw [Subalgebra.smul_def]
        exact mul_mem (hSle s.2) hb
  · obtain ⟨hctr, l, hl⟩ :=
      PositivityTheory.HtPt.Mb.join_charts o Ω κ (κ ⊕ Fin n) x Ω (RingHom.id Ω) z M' (fun _ => rfl) p'
    obtain ⟨c', -, hc'⟩ := hctr
    have ho : ∀ r : o, algebraMap o Ω r ∈ regAt M'.ξ p' := fun r =>
      hc' _ (Subalgebra.algebraMap_mem _ r)
    have hSle : ∀ a ∈ chRing o x c, a ∈ regAt M'.ξ p' := by
      intro a ha
      have h1 : a ∈ (chRing o x c).toSubring := ha
      rw [chRing, Algebra.adjoin_eq_ring_closure] at h1
      exact (Subring.closure_le.2 (Set.union_subset (by rintro _ ⟨r, rfl⟩; exact ho r)
        (by rintro _ ⟨j, rfl⟩; exact hp' j))) h1
    let φ : chRing o x c →+* regAt M'.ξ p' :=
      { toFun := fun s => ⟨s, hSle s s.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    have hvint : IsIntegral (regAt M'.ξ p') (z l / x c ^ d) :=
      IsIntegral.map_of_comp_eq φ (RingHom.id Ω) (by ext; rfl) (hyS l)
    obtain ⟨hzl, hzr⟩ := hl
    have hv : z l / x c ^ d ∈ regAt M'.ξ p' :=
      mem_of_isIntegral_of_inv_mem _ hvint (div_ne_zero hzl hd) (by rw [inv_div, ← hz c]; exact hzr _)
    have hy : ∀ k, z k / x c ^ d ∈ regAt M'.ξ p' := fun k => by
      have e : z k / x c ^ d = z k / z l * (z l / x c ^ d) := by field_simp
      rw [e]
      exact mul_mem (hzr k) hv
    refine ⟨?_, fun q => ?_⟩
    · simp only [joinCo, RingHom.id_apply, hz c]
      exact mul_ne_zero hc hd
    · rw [joinCo_div x z hz c q]
      exact mul_mem (hp' q.1) (hy q.2)

end PositivityTheory.HtPt.Mb.LNormChart.ChNorm


open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField in
theorem PositivityTheory.HtPt.Mb.norm_chart : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (d n : ℕ) (z : κ ⊕ Fin n → Ω) (M' : PModel o (joinCo (RingHom.id Ω) x z)), (∀ c, z (Sum.inl c) = x c ^ d) → (∀ c, x c ≠ 0 → ∀ a : Ω, IsIntegral (chRing o x c) a ↔ a ∈ Submodule.span (chRing o x c) (Set.range fun k => z k / x c ^ d)) → ∀ c, x c ≠ 0 → (∀ a : Ω, a ∈ chRing o (joinCo (RingHom.id Ω) x z) (c, Sum.inl c) ↔ IsIntegral (chRing o x c) a) ∧ ∀ p' : Cpt M'.ξ, (∀ j, x j / x c ∈ regAt M'.ξ p') → InChart M'.ξ (joinCo (RingHom.id Ω) x z) (c, Sum.inl c) p' :=
  @PositivityTheory.HtPt.Mb.LNormChart.ChNorm.join_chart_normalisation
end
