module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle079
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle081
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.RatTors


open Polynomial in
theorem exists_split_ext (K : Type) [Field K] (C : Type) [CommRing C] (φ : K →+* C) (hφ : φ.Finite) :
    ∃ E : IntermediateField K (AlgebraicClosure K), FiniteDimensional K E ∧
      ∀ (K₂ Ω : Type) [Field K₂] [Field Ω] (e : E →+* K₂) (j : K₂ →+* Ω) (ψ : C →+* Ω),
        ψ.comp φ = j.comp (e.comp (algebraMap K E)) → ∃ ψ₀ : C →+* K₂, j.comp ψ₀ = ψ := by
  first
  | exact @_root_.GlobalTheory.FiniteFieldOfPoints.exists_finite_field_of_points
  | exact _root_.GlobalTheory.FiniteFieldOfPoints.exists_finite_field_of_points
  | (apply _root_.GlobalTheory.FiniteFieldOfPoints.exists_finite_field_of_points <;> assumption)
  | (intros; apply _root_.GlobalTheory.FiniteFieldOfPoints.exists_finite_field_of_points <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FiniteFieldOfPoints.exists_finite_field_of_points <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FiniteFieldOfPoints.exists_finite_field_of_points ..)

end GlobalTheory.Mum.RatTors

namespace GlobalTheory.Mum.RatTors

theorem exists_finite_tors (K : Type) [Field K] (A : PolAV (Sp K)) (n : ℕ) (hn : 1 ≤ n) :
    ∃ (C : Type) (_ : CommRing C) (φ : K →+* C) (p : Sp C ⟶ A.A.left), φ.Finite ∧ p ≫ A.A.hom = spMap φ ∧
      ∀ (Ω : Type) [Field Ω] (y : Sp Ω ⟶ A.A.left),
        y ≫ (mulA A.A n).left = y ≫ A.A.hom ≫ (η[A.A]).left → ∃ ψ : C →+* Ω, y = spMap ψ ≫ p := by
  have hF : IsFinite (mulA A.A n).left := (GlobalTheory.firstFiveLaws.1.mulN (Sp K) A n hn).1
  haveI : IsAffine ((𝟙_ (Over (Sp K))).left) := (inferInstance : IsAffine (Sp K))
  let f := (mulA A.A n).left
  let g := (η[A.A]).left
  haveI : IsFinite f := hF
  haveI hY : IsFinite (pullback.snd f g) := inferInstance
  haveI : IsAffine (pullback f g) := isAffine_of_isAffineHom (pullback.snd f g)
  let Y := pullback f g
  let q : Sp Γ(Y, ⊤) ⟶ Sp K := Y.isoSpec.inv ≫ pullback.snd f g
  let φ₀ := Spec.preimage q
  have hq : spMap φ₀.hom = q := Spec.map_preimage q
  have hfst : pullback.fst f g ≫ A.A.hom = pullback.snd f g := by
    have h1 : f ≫ A.A.hom = A.A.hom := Over.w (mulA A.A n)
    have h2 : g ≫ A.A.hom = 𝟙 _ := Over.w (η[A.A])
    rw [← h1, ← Category.assoc, pullback.condition, Category.assoc, h2, Category.comp_id]
  refine ⟨Γ(Y, ⊤), inferInstance, φ₀.hom, Y.isoSpec.inv ≫ pullback.fst f g, ?_, ?_, ?_⟩
  · rw [← IsFinite.SpecMap_iff]
    change IsFinite (spMap φ₀.hom)
    rw [hq]
    infer_instance
  · rw [hq, Category.assoc, hfst]
  · intro Ω _ y hy
    let z : Sp Ω ⟶ Y := pullback.lift y (y ≫ A.A.hom) (by rw [hy, Category.assoc])
    let w : Sp Ω ⟶ Sp Γ(Y, ⊤) := z ≫ Y.isoSpec.hom
    refine ⟨(Spec.preimage w).hom, ?_⟩
    change y = Spec.map (Spec.preimage w) ≫ _
    rw [Spec.map_preimage, Category.assoc, Iso.hom_inv_id_assoc, pullback.lift_fst]

end GlobalTheory.Mum.RatTors

namespace GlobalTheory.Mum.RatTors

section Push
variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

theorem mulA_push (h : IsGrpPullback G' G f φ) (n : ℕ) : (mulA G' n).left ≫ φ = φ ≫ (mulA G n).left := by
  have e := congrArg (fun z => z.left) (map_pow (pushHom h G') (𝟙 G') n)
  have e2 : (pushHom h G' (𝟙 G')) ^ n = pushHom h G' (𝟙 G') ≫ mulA G n := by
    rw [MonObj.comp_pow, Category.comp_id]
  rw [e2] at e
  calc (mulA G' n).left ≫ φ = (pushHom h G' (𝟙 G' ^ n)).left := rfl
    _ = (pushHom h G' (𝟙 G') ≫ mulA G n).left := e
    _ = (𝟙 G'.left ≫ φ) ≫ (mulA G n).left := rfl
    _ = _ := by rw [Category.id_comp]

theorem eta_push (h : IsGrpPullback G' G f φ) : (η[G']).left ≫ φ = f ≫ (η[G]).left := by
  have e := congrArg (fun z => z.left) (map_one (pushHom h (Over.mk (𝟙 S'))))
  have e' : (𝟙 S' ≫ (η[G']).left) ≫ φ = (𝟙 S' ≫ f) ≫ (η[G]).left := e
  rwa [Category.id_comp, Category.id_comp] at e'

end Push

end GlobalTheory.Mum.RatTors

namespace GlobalTheory.Mum.RatTors

theorem spMap_inj {P Q : Type} [CommRing P] [CommRing Q] {u v : P →+* Q} (h : spMap u = spMap v) : u = v :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem torsion_rational : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁], Base R₁ → ∀ (A : PolAV (Sp (FractionRing R₁))) (n : ℕ), 1 ≤ n → ∃ E : IntermediateField (FractionRing R₁) (Kb R₁), FiniteDimensional (FractionRing R₁) E ∧ ∀ (R₂ : Type) [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂] (i₁₂ : R₁ →+* R₂) (e : E →+* FractionRing R₂), Function.Injective i₁₂ → (∀ r : R₁, e (algebraMap (FractionRing R₁) E (algebraMap R₁ (FractionRing R₁) r)) = algebraMap R₂ (FractionRing R₂) (i₁₂ r)) → ∀ (A₂ : PolAV (Sp (FractionRing R₂))) (a : A₂.A.left ⟶ A.A.left), IsFib i₁₂ A A₂ a → ∀ x : TFK (R := R₂) (Kb R₂) ⟶ A₂.A, x ^ n = 1 → ∃ x₀ : Sp (FractionRing R₂) ⟶ A₂.A.left, x.left = spMap (algebraMap (FractionRing R₂) (Kb R₂)) ≫ x₀ := by
  intro R₁ _ _ _ _ A n hn
  obtain ⟨C, _, φ, p, hφ, hp, hpt⟩ := exists_finite_tors _ A n hn
  obtain ⟨E, hE, hEs⟩ := exists_split_ext (FractionRing R₁) C φ hφ
  refine ⟨E, hE, ?_⟩
  rintro R₂ _ _ _ i₁₂ e _ he A₂ a ⟨ga, hga, hpb, -⟩ x hx
  let j := algebraMap (FractionRing R₂) (Kb R₂)
  have hge : ga = e.comp (algebraMap (FractionRing R₁) E) :=
    IsLocalization.ringHom_ext (nonZeroDivisors R₁) (RingHom.ext fun r => by
      rw [RingHom.comp_apply, RingHom.comp_apply, hga, RingHom.comp_apply, he])
  let y := x.left ≫ a
  have hxh : x.left ≫ A₂.A.hom = spMap j := Over.w x
  have hyh : y ≫ A.A.hom = spMap j ≫ spMap ga := by
    change (x.left ≫ a) ≫ A.A.hom = _
    rw [Category.assoc, hpb.1.w, ← Category.assoc, hxh]
  have h1 : x.left ≫ (mulA A₂.A n).left = spMap j ≫ (η[A₂.A]).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id, hx]
    rfl
  have htors : y ≫ (mulA A.A n).left = y ≫ A.A.hom ≫ (η[A.A]).left := by
    change (x.left ≫ a) ≫ _ = (x.left ≫ a) ≫ _
    rw [Category.assoc, ← mulA_push hpb, ← Category.assoc, h1, Category.assoc, eta_push hpb,
      ← Category.assoc (x.left ≫ a), hyh, Category.assoc]
  obtain ⟨ψ, hψ⟩ := hpt (Kb R₂) y htors
  have hψφ : ψ.comp φ = j.comp ga := by
    refine spMap_inj ?_
    rw [GlobalTheory.Ex.spMap_comp', GlobalTheory.Ex.spMap_comp', ← hp, ← Category.assoc, ← hψ, hyh]
  obtain ⟨ψ₀, hψ₀⟩ := hEs (FractionRing R₂) (Kb R₂) e j ψ (by rw [hψφ, hge])
  have hψ₀φ : ψ₀.comp φ = ga := by
    refine RingHom.ext fun r => j.injective ?_
    have := RingHom.congr_fun hψφ r
    rw [← hψ₀] at this
    exact this
  let y₀ : Sp (FractionRing R₂) ⟶ A.A.left := spMap ψ₀ ≫ p
  have hy₀ : y₀ ≫ A.A.hom = 𝟙 _ ≫ spMap ga := by
    change (spMap ψ₀ ≫ p) ≫ _ = _
    rw [Category.assoc, hp, ← GlobalTheory.Ex.spMap_comp', hψ₀φ, Category.id_comp]
  refine ⟨hpb.1.lift y₀ (𝟙 _) hy₀, hpb.1.hom_ext ?_ ?_⟩
  · rw [Category.assoc, hpb.1.lift_fst]
    change y = _
    rw [hψ, ← hψ₀, GlobalTheory.Ex.spMap_comp', Category.assoc]
  · rw [Category.assoc, hpb.1.lift_snd, Category.comp_id, hxh]

end GlobalTheory.Mum.RatTors
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section
namespace GlobalTheory.Poinc.LabIndex

theorem pow_left_congr {S X : Scheme.{0}} {G : Over S} [GrpObj G] {a b : X ⟶ S} (h : a = b)
    (x : Over.mk a ⟶ G) (x' : Over.mk b ⟶ G) (hx : x.left = x'.left) (n : ℕ) :
    (x ^ n).left = (x' ^ n).left := by
  subst h
  rw [Over.OverMorphism.ext hx]

theorem eq_of_comp_fst {P X Y Z T : Scheme.{0}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) [Mono g] {a b : T ⟶ P} (e : a ≫ fst = b ≫ fst) : a = b :=
  h.hom_ext e ((cancel_mono g).1 (by rw [Category.assoc, Category.assoc, ← h.w, ← Category.assoc, e, Category.assoc]))

theorem isDominant_of_generic {R : Type} [CommRing R] [IsDomain R] (W : (Sp R).Opens) {K : Type} [Field K]
    (eg : Sp K ⟶ W.toScheme) (heg : ∀ w, W.ι (eg w) = genericPoint (Sp R)) : IsDominant eg := by
  refine ⟨fun w => ?_⟩
  let w0 : Sp K := genericPoint (Sp K)
  have h1 : eg w0 ⤳ w := by
    rw [← W.ι.isOpenEmbedding.isInducing.specializes_iff, heg w0]
    exact genericPoint_specializes _
  exact closure_mono (Set.singleton_subset_iff.2 (Set.mem_range_self w0)) (specializes_iff_mem_closure.1 h1)

theorem spMap_generic (R : Type) [CommRing R] [IsDomain R] (w : Sp (AlgebraicClosure (FractionRing R))) :
    spMap ((algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))).comp (algebraMap R (FractionRing R))) w =
      genericPoint (Sp R) := by
  have hw : w = genericPoint (Sp (AlgebraicClosure (FractionRing R))) := Subsingleton.elim _ _
  subst hw
  rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
  apply PrimeSpectrum.ext
  show Ideal.comap ((algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))).comp
    (algebraMap R (FractionRing R))) ⊥ = ⊥
  exact Ideal.comap_bot_of_injective _
    ((algebraMap (FractionRing R) _).injective.comp (IsFractionRing.injective R (FractionRing R)))

end GlobalTheory.Poinc.LabIndex

namespace GlobalTheory.Poinc.LabIndex

theorem one_left_congr {S X : Scheme.{0}} {G : Over S} [GrpObj G] {a b : X ⟶ S} (h : a = b) :
    (1 : Over.mk a ⟶ G).left = (1 : Over.mk b ⟶ G).left := by
  subst h
  rfl

theorem torsion_section_label : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real), S.Big → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.admitted M U₀ → S.IsEE M U₀ EE → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), GlobalTheory.Mum.Base R → IsCpl j → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ FinalForm.G.left), IsGrpPullback G FinalForm.G (spMap j ≫ M.Z.fromSpecStalk x) gm → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso U.LG.L (FinalForm.L.L.pull gm) → (∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G)) → ∀ s : 𝟙_ (Over (Sp R)) ⟶ G, s ^ (S.r * S.N) = 1 → ∃ b : S.Gam, ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (ev : R →+* OO p), M.Cen U₀ x y → spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y → ∀ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ → ∀ t : Sp (PadicAlgCl p) ⟶ pullback ρ.P.A.hom FinalForm.u₀, t ≫ FinalForm.φ = spMap ((OO p).subtype.comp ev) ≫ s.left ≫ gm → t ≫ pullback.fst _ _ = spMap y₀ ≫ (ρ.pt b).left := by
  intro o' Ω _ _ _ _ S ρ hBig M U₀ EE FinalForm hAdm hEE x hx R _ _ _ j hBase hcpl G _ _ gm hgm D A U hLB hpsi s hs
  set ξ : Sp R ⟶ M.Z := spMap j ≫ M.Z.fromSpecStalk x with hξdef
  let W : (Sp R).Opens := ξ ⁻¹ᵁ U₀
  have hrW : Set.range (W.ι ≫ ξ) ⊆ Set.range U₀.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact w.2
  let w₀ : W.toScheme ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι (W.ι ≫ ξ) hrW
  have hw₀ : w₀ ≫ U₀.ι = W.ι ≫ ξ := IsOpenImmersion.lift_fac _ _ _
  have hsG : s.left ≫ G.hom = 𝟙 _ := Over.w s
  have hσw : (W.ι ≫ s.left ≫ gm) ≫ FinalForm.G.hom = w₀ ≫ U₀.ι := by
    rw [hw₀, Category.assoc, Category.assoc, hgm.1.w, ← Category.assoc s.left, hsG, Category.id_comp]
  let σ : W.toScheme ⟶ pullback ρ.P.A.hom FinalForm.u₀ := FinalForm.cart.1.lift _ _ hσw
  have hσ1 : σ ≫ FinalForm.φ = W.ι ≫ s.left ≫ gm := FinalForm.cart.1.lift_fst _ _ _
  have hσ2 : σ ≫ pullback.snd ρ.P.A.hom FinalForm.u₀ = w₀ := FinalForm.cart.1.lift_snd _ _ _
  have key : (W : Set (Sp R)).Nonempty →
      ∃ b : S.Gam, σ ≫ pullback.fst ρ.P.A.hom FinalForm.u₀ = (w₀ ≫ FinalForm.u₀) ≫ (ρ.pt b).left := by
    intro hWne
    let K := AlgebraicClosure (FractionRing R)
    let e0 : Sp K ⟶ Sp R := spMap ((algebraMap (FractionRing R) K).comp (algebraMap R (FractionRing R)))
    have he0 : ∀ w, e0 w = genericPoint (Sp R) := spMap_generic R
    have hgW : genericPoint (Sp R) ∈ W := by
      obtain ⟨w, hw⟩ := hWne
      exact (genericPoint_specializes w).mem_open W.isOpen hw
    have hr : Set.range e0 ⊆ Set.range W.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨w, rfl⟩
      rw [he0]
      exact hgW
    let eg : Sp K ⟶ W.toScheme := IsOpenImmersion.lift W.ι e0 hr
    have heg : eg ≫ W.ι = e0 := IsOpenImmersion.lift_fac _ _ _
    haveI : IsDominant eg := isDominant_of_generic W eg (fun w => by rw [← Scheme.Hom.comp_apply, heg, he0])
    haveI : IsSeparated ρ.P.A.hom := by haveI := ρ.P.isAb.proper; infer_instance
    let T : Over (Sp R) := Over.mk e0
    have htu : (toUnit T).left = e0 := (Category.comp_id _).symm.trans (Over.w (toUnit T))
    let x1 : T ⟶ G := toUnit T ≫ s
    have hx1 : x1 ^ (S.r * S.N) = 1 := by
      show ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom (toUnit T) s ^ (S.r * S.N) = 1
      rw [← map_pow, hs, map_one]
    let x2 := pushHom hgm T x1
    have hx2 : x2 ^ (S.r * S.N) = 1 := by
      show pushHom hgm T x1 ^ (S.r * S.N) = 1
      rw [← map_pow, hx1, map_one]
    let T' : Over U₀.toScheme := Over.mk (eg ≫ w₀)
    let x3 : T' ⟶ (Over.pullback FinalForm.u₀).obj ρ.P.A := Over.homMk (eg ≫ σ) (by
      show (eg ≫ σ) ≫ pullback.snd _ _ = eg ≫ w₀
      rw [Category.assoc, hσ2])
    have hbase : T'.hom ≫ U₀.ι = T.hom ≫ ξ := by
      show (eg ≫ w₀) ≫ U₀.ι = e0 ≫ ξ
      rw [Category.assoc, hw₀, ← Category.assoc, heg]
    have hx3 : x3 ^ (S.r * S.N) = 1 := by
      apply Over.OverMorphism.ext
      apply eq_of_comp_fst FinalForm.cart.1
      have a1 : ((pushHom FinalForm.cart T') (x3 ^ (S.r * S.N))).left = ((pushHom FinalForm.cart T' x3) ^ (S.r * S.N)).left := by
        rw [map_pow]
      have a2 : ((pushHom FinalForm.cart T') 1).left = (1 : Over.mk (T'.hom ≫ U₀.ι) ⟶ FinalForm.G).left := by
        rw [map_one]
      have a3 := pow_left_congr hbase (pushHom FinalForm.cart T' x3) x2 (by
        show (eg ≫ σ) ≫ FinalForm.φ = (toUnit T ≫ s).left ≫ gm
        rw [Over.comp_left, htu, Category.assoc, hσ1, ← Category.assoc eg, heg]
        simp only [Category.assoc]) (S.r * S.N)
      have a4 := one_left_congr (G := FinalForm.G) hbase
      refine a1.trans (a3.trans ?_)
      rw [hx2, ← a4, ← a2]
      rfl
    let x4 := pushHom (isGrpPullback_pullback ρ.P.A FinalForm.u₀) T' x3
    have hx4 : x4 ^ (S.r * S.N) = 1 := by
      show pushHom (isGrpPullback_pullback ρ.P.A FinalForm.u₀) T' x3 ^ (S.r * S.N) = 1
      rw [← map_pow, hx3, map_one]
    obtain ⟨b, hb, -⟩ := ρ.pt_bij K (T'.hom ≫ FinalForm.u₀) x4 hx4
    refine ⟨b, ext_of_isDominant_of_isSeparated ρ.P.A.hom ?_ eg ?_⟩
    · have e1 : (ρ.pt b).left ≫ ρ.P.A.hom = 𝟙 _ := Over.w (ρ.pt b)
      rw [Category.assoc, pullback.condition, ← Category.assoc, hσ2, Category.assoc, e1]
      exact (Category.comp_id _).symm
    · have e2 := congrArg (fun z => z.left) hb
      simp only [Over.comp_left, Over.homMk_left] at e2
      rw [← Category.assoc, ← Category.assoc]
      exact (e2.trans rfl).symm
  by_cases hWne : (W : Set (Sp R)).Nonempty
  · obtain ⟨b, hb⟩ := key hWne
    refine ⟨b, fun p _ y ev hCen hev y₀ hAt t ht => ?_⟩
    let c : Sp (PadicAlgCl p) ⟶ Sp R := spMap ((OO p).subtype.comp ev)
    have hc : c ≫ ξ = gPt p ≫ y := by
      rw [← hev]
      simp only [c, gPt, spMap, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hcW : Set.range c ⊆ Set.range W.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨w, rfl⟩
      show ξ (c w) ∈ U₀
      rw [← Scheme.Hom.comp_apply, hc]
      exact hCen.2 ⟨w, rfl⟩
    let c' : Sp (PadicAlgCl p) ⟶ W.toScheme := IsOpenImmersion.lift W.ι c hcW
    have hc' : c' ≫ W.ι = c := IsOpenImmersion.lift_fac _ _ _
    have htc : t = c' ≫ σ := eq_of_comp_fst FinalForm.cart.1 (by
      rw [ht, Category.assoc, hσ1, ← Category.assoc c', hc'])
    have hq : (c' ≫ w₀) ≫ U₀.ι = gPt p ≫ y := by
      rw [Category.assoc, hw₀, ← Category.assoc, hc', hc]
    have hu : (c' ≫ w₀) ≫ FinalForm.u₀ = spMap y₀ := by
      rw [← Spec.map_preimage ((c' ≫ w₀) ≫ FinalForm.u₀)]
      congr 1
      ext a
      rw [GlobalTheory.ZH.preimage_comp_eq_val M U₀ hAdm.1.ne S.R FinalForm.u₀ FinalForm.u₀_gen, hq, ← hAt a]
      rfl
    rw [htc, Category.assoc, hb, ← Category.assoc, ← Category.assoc, hu]
  · refine ⟨0, fun p _ y ev hCen hev y₀ hAt t ht => absurd ?_ hWne⟩
    let c : Sp (PadicAlgCl p) ⟶ Sp R := spMap ((OO p).subtype.comp ev)
    have hc : c ≫ ξ = gPt p ≫ y := by
      rw [← hev]
      simp only [c, gPt, spMap, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    refine ⟨c (genericPoint _), ?_⟩
    show ξ (c (genericPoint _)) ∈ U₀
    rw [← Scheme.Hom.comp_apply, hc]
    exact hCen.2 ⟨_, rfl⟩

end GlobalTheory.Poinc.LabIndex
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc

theorem endChar_act : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (a : 𝓞 E), EndChar P.U (t.act.act a) (DistribSMul.toAddMonoidHom P.D.toPre.X (H.bar a)) := by
  intro E _ _ _ H R _ _ _ _ t P a κ _ ρ hρ G₀ _ φ h f₀ hf
  letI := H.starRing
  obtain ⟨τ, hτ, hi⟩ := P.lin.i_lin 0 a
  have e : τ = GlobalTheory.SplitTorus.torusMap _ (DistribSMul.toAddMonoidHom P.D.toPre.X (H.bar a)) :=
    (GlobalTheory.SplitTorus.eq_torusMap_iff _ _).2 fun x =>
      (GlobalTheory.SplitTorus.res_pullU_charUnit τ x _).symm.trans
        ((congrArg Units.val (hτ x)).trans (GlobalTheory.SplitTorus.charUnit_val _))
  have k := GlobalTheory.TorusPart.isGrpPullback_thickLift hρ h
  have c : f₀.left ≫ GlobalTheory.TorusPart.thickLift hρ h =
      GlobalTheory.TorusPart.thickLift hρ h ≫
        ((Over.pullback (Out.thick R (maximalIdeal R) 0)).map (t.act.act a)).left := by
    apply pullback.hom_ext
    · refine (Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) (GlobalTheory.TorusPart.thickLift_fst _ _)).trans (hf.trans ?_))
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      refine Eq.trans ?_ (congrArg (_ ≫ ·) (GlobalTheory.ExtUnique.pullback_map_left_fst _ _).symm)
      exact (congrArg (· ≫ _) (GlobalTheory.TorusPart.thickLift_fst _ _).symm).trans (Category.assoc _ _ _)
    · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) k.1.w).trans ?_)
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      refine Eq.trans ?_ (congrArg (_ ≫ ·)
        (Over.w ((Over.pullback (Out.thick R (maximalIdeal R) 0)).map (t.act.act a))).symm)
      refine Eq.trans ?_ k.1.w.symm
      rw [← Category.assoc, Over.w]
  exact (GlobalTheory.TorusPart.pullTorus_comp k k _ _ c (P.U.gt 0).i).symm.trans
    ((congrArg (GlobalTheory.TorusPart.pullTorus k) (hi.trans (congrArg (· ≫ _) e))).trans
      (GlobalTheory.TorusPart.pullTorus_torusMap_comp k _ _))

end GlobalTheory.UPoinc
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

namespace ClosedInj

theorem epi_spMap_field {Ω Ω' : Type} [Field Ω] [Field Ω'] (io : Ω →+* Ω') : Epi (spMap io) := by
  have : Flat (spMap io) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    letI := io.toAlgebra
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  have : Surjective (spMap io) := ⟨fun t ↦ ⟨IsLocalRing.closedPoint Ω', Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem exists_residue_factor {R Ω : Type} [CommRing R] [IsLocalRing R] [Field Ω] (y : Sp Ω ⟶ Sp R)
    (hy : ∀ t, y t = closedPoint R) : ∃ κ : ResidueField R →+* Ω, y = spMap (κ.comp (residue R)) := by
  set φ : R →+* Ω := (Spec.preimage y).hom with hφ
  have hyφ : y = spMap φ := (Spec.map_preimage y).symm
  have hker : ∀ a : R, a ∈ maximalIdeal R → φ a = 0 := by
    intro a ha
    have h1 := hy (IsLocalRing.closedPoint Ω)
    rw [hyφ] at h1
    have h2 : (PrimeSpectrum.comap φ (IsLocalRing.closedPoint Ω)).asIdeal = maximalIdeal R := by
      exact congrArg PrimeSpectrum.asIdeal h1
    rw [← h2] at ha
    have : φ a ∈ maximalIdeal Ω := ha
    rwa [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at this
  have : IsLocalHom φ := ⟨fun a ha => by
    by_contra h
    have := hker a ((IsLocalRing.mem_maximalIdeal a).2 h)
    rw [this] at ha
    exact not_isUnit_zero ha⟩
  exact ⟨ResidueField.lift φ, by rw [ResidueField.lift_comp_residue]; exact hyφ⟩

end ClosedInj


open ClosedInj in
theorem Emb.eq_of_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (M : Modif R) (G' : Over M.S) [GrpObj G'] (E : Emb M.π G') (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ E.H.toScheme), (∀ t, M.π (G'.hom (E.H.ι (p t))) = closedPoint R) → p ≫ E.H.ι ≫ G'.hom = p' ≫ E.H.ι ≫ G'.hom → p ≫ E.f = p' ≫ E.f → p = p' := by
  intro R _ _ _ M G' _ E Ω _ p p' hcl hs hf
  set s : Sp Ω ⟶ M.S := p ≫ E.H.ι ≫ G'.hom with hsdef
  obtain ⟨κ, hκ⟩ := exists_residue_factor (s ≫ M.π) (fun t => by simpa [s] using hcl t)
  obtain ⟨Ω', _, io, e, l, -, hl, hlf⟩ := E.fib Ω s κ hκ
  let q : Sp Ω' ⟶ pullback G'.hom (spMap io ≫ s) :=
    pullback.lift (spMap io ≫ p ≫ E.H.ι) (𝟙 _) (by simp [s])
  let q' : Sp Ω' ⟶ pullback G'.hom (spMap io ≫ s) :=
    pullback.lift (spMap io ≫ p' ≫ E.H.ι) (𝟙 _) (by simp [s, hs])
  have hq : q ≫ l = spMap io ≫ p := by
    rw [← cancel_mono E.H.ι]
    simp only [Category.assoc]
    erw [hl]
    exact pullback.lift_fst _ _ _
  have hq' : q' ≫ l = spMap io ≫ p' := by
    rw [← cancel_mono E.H.ι]
    simp only [Category.assoc]
    erw [hl]
    exact pullback.lift_fst _ _ _
  have hfst : q ≫ e.hom.left ≫ pullback.fst E.Y.hom (spMap (io.comp κ)) =
      q' ≫ e.hom.left ≫ pullback.fst E.Y.hom (spMap (io.comp κ)) := by
    have := E.imm
    rw [← cancel_mono E.j]
    simp only [Category.assoc]
    rw [← hlf, ← Category.assoc q, hq, ← Category.assoc q', hq', Category.assoc, Category.assoc, hf]
  have hw : e.hom.left ≫ pullback.snd E.Y.hom (spMap (io.comp κ)) = pullback.snd G'.hom (spMap io ≫ s) :=
    Over.w e.hom
  have hqe : q ≫ e.hom.left = q' ≫ e.hom.left := by
    apply pullback.hom_ext
    · simpa only [Category.assoc] using hfst
    · simp only [Category.assoc]
      rw [hw]
      exact (pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm
  have hqq : q = q' := by
    have := congrArg (· ≫ e.inv.left) hqe
    simpa [← Over.comp_left] using this
  have h2 : spMap io ≫ p = spMap io ≫ p' := by rw [← hq, ← hq', hqq]
  have := epi_spMap_field io
  exact (cancel_epi (spMap io)).1 h2

end GlobalTheory.Mum
end
