module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle003
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle017
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle020
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle016
public import Mathlib.Tactic.ENatToNat
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.PsiInt

theorem gs_scal {R : Type} [CommRing R] {Y Z : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ Y) (z : Z)
    (c : R) : gs r z ⊤ (scal p c) = gs (𝟙 _) z ⊤ (scal (r ≫ p) c) :=
  calc gs r z ⊤ (scal p c) = gs (𝟙 _ ≫ r) z ⊤ (scal p c) := by rw [Category.id_comp]
    _ = gs (𝟙 _) z (r ⁻¹ᵁ ⊤) ((r.app ⊤).hom (scal p c)) := (gs_pull (𝟙 _) r z ⊤ (by trivial) _).symm
    _ = gs (𝟙 _) z ⊤ (scal (r ≫ p) c) := rfl

theorem scal_jK {R : Type} [CommRing R] [IsDomain R] {Y : Scheme.{0}}
    (p : Y ⟶ Spec (CommRingCat.of (FractionRing R))) (c : R) :
    scal (p ≫ jK R) c = scal p (algebraMap R (FractionRing R) c) := by
  have e := congrArg (fun q => q.hom c)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  unfold scal
  rw [e]
  rfl

theorem jK_appTop_injective (R : Type) [CommRing R] [IsDomain R] : Function.Injective (jK R).appTop.hom := by
  have hs := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).2
  have hi := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv).1
  intro x y h
  obtain ⟨a, rfl⟩ := hs x
  obtain ⟨b, rfl⟩ := hs y
  have e := fun c => congrArg (fun q => q.hom c)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  have := hi ((e a).trans (h.trans (e b).symm))
  rw [IsFractionRing.injective R (FractionRing R) this]

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem cT_zero (T : Over (Spec (CommRingCat.of R))) : cT D T 0 = 1 := by
  have h : D.c 0 = D.c 0 * D.c 0 := by
    have := D.c_add 0 0
    rwa [add_zero] at this
  have h1 : D.c 0 = 1 := left_eq_mul.1 h
  rw [cT, h1, MonObj.comp_one]

theorem exists_defect
    (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)))
    (f : ∀ α, SecBT D (𝟙_ _) 1 α) (χ : D.X) (hg : (ga χ).IsGen) (p q : R) :
    ∃ d : SecBT D (𝟙_ _) 1 χ, ∀ (T : Over (Spec (CommRingCat.of R))) (y : T ⟶ D.P.A) (z : T.left) (J),
      Good D.P.L z J → sval d (lift (toUnit T) y).left z J =
        gs (𝟙 _) z ⊤ (scal T.hom q) * sval (f χ) (lift (toUnit T) y).left z J -
        gs (𝟙 _) z ⊤ (scal T.hom p) * ((val (ga χ) (toUnit T).left z J * rigV D z J).val *
          sval (f 0) (lift (toUnit T) (y * cT D T χ)).left z J) := by
  let Y : Over (Spec (CommRingCat.of R)) := 𝟙_ _ ⊗ D.P.A
  let τ : Y ⟶ Y := lift (toUnit Y) (snd _ _ * cT D Y χ)
  have hF : FormEq (famφT D (𝟙_ _) χ) (DegPre.famε 1)
      (Sum.elim (fun k => τ.left ≫ famφT D (𝟙_ _) 0 k)
        (fun k => (toUnit Y).left ≫ Sum.elim (fun _ : PUnit => (D.c χ).left) (fun _ : PUnit => eSec D.P.A) k))
      (Sum.elim (DegPre.famε 1) (Sum.elim (fun _ => -1) (fun _ => 1))) := by
    intro U _ h
    have e₁ : τ.left ≫ famφT D (𝟙_ _) 0 1 = famφT D (𝟙_ _) χ 1 := by
      change (τ ≫ (snd _ _ * cT D Y 0)).left = (snd _ _ * cT D Y χ).left
      rw [cT_zero, _root_.mul_one, lift_snd]
    have e₂ : τ.left ≫ famφT D (𝟙_ _) 0 2 = famφT D (𝟙_ _) χ 3 := by
      change (τ ≫ cT D Y 0).left = (1 : Y ⟶ D.P.A).left
      rw [cT_zero, MonObj.comp_one]
    have e₃ : τ.left ≫ famφT D (𝟙_ _) 0 3 = famφT D (𝟙_ _) χ 3 := by
      change (τ ≫ (1 : Y ⟶ D.P.A)).left = (1 : Y ⟶ D.P.A).left
      rw [MonObj.comp_one]
    have e₄ : (toUnit Y).left ≫ (D.c χ).left = famφT D (𝟙_ _) χ 2 := rfl
    have e₅ : (toUnit Y).left ≫ eSec D.P.A = famφT D (𝟙_ _) χ 3 := rfl
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, Fin.prod_univ_four,
      e₁, e₂, e₃, e₄, e₅]
    simp [DegPre.famε, _root_.mul_assoc]
  obtain ⟨d, hd⟩ := exists_sec_relation_defect Y.left D.P.A.left Y.left D.P.L D.P.isLB _ _ _ _ _ _ _ _ _ τ.left
    (f 0) (f χ) (LB.pullGen D.P.L _ _ (LB.mulGen D.P.L _ _ _ _ (ga χ) D.rig) (toUnit Y).left)
    (scal Y.hom p) (scal Y.hom q)
    (DVR.pullGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ hg D.rig_gen) _) hF
  refine ⟨d, fun T y z J hJ => ?_⟩
  have e₁ : (lift (toUnit T) y).left ≫ Y.hom = T.hom := Over.w _
  have e₂ : (lift (toUnit T) y).left ≫ τ.left = (lift (toUnit T) (y * cT D T χ)).left := by
    rw [← Over.comp_left]
    congr 1
    simp only [τ, comp_lift, MonObj.comp_mul, lift_snd, cT, ← Category.assoc]
    congr 2
    · exact toUnit_unique _ _
    · congr 1
      exact toUnit_unique _ _
  have e₃ : (lift (toUnit T) y).left ≫ (toUnit Y).left = (toUnit T).left := by
    rw [← Over.comp_left]
    exact congrArg _ (toUnit_unique _ _)
  rw [hd _ _ z J hJ, gs_scal, gs_scal Y.hom _ z p, e₁, e₂, val_pull hJ, e₃, val_mul hJ, mul_comm (sval (f 0) _ z J)]
  congr 5

theorem psiRel_integral : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (a : D.X → (FractionRing R)ˣ) (f : ∀ α, SecBT D (𝟙_ _) 1 α), PsiScal D ga a → PsiRel D (𝟙_ _) f → ∀ (χ : D.X) (p q : R), algebraMap R (FractionRing R) q * (a χ).val = algebraMap R (FractionRing R) p → ∀ (T : Over (Spec (CommRingCat.of R))) (y : T ⟶ D.P.A) (z : T.left) (J), Good D.P.L z J → gs (𝟙 _) z ⊤ (scal T.hom q) * sval (f χ) (lift (toUnit T) y).left z J = gs (𝟙 _) z ⊤ (scal T.hom p) * ((val (ga χ) (toUnit T).left z J * rigV D z J).val * sval (f 0) (lift (toUnit T) (y * cT D T χ)).left z J) := by
  intro R _ _ D ga a f hS hR χ p q hpq T y z J hJ
  obtain ⟨d, hd⟩ := exists_defect D ga f χ (hS χ).1 p q
  haveI : Flat D.P.A.hom := by
    haveI := D.P.smoothDim
    haveI : Smooth D.P.A.hom := SmoothOfRelativeDimension.smooth D.P.g _
    infer_instance
  haveI : IsAffine (𝟙_ (Over (Spec (CommRingCat.of R)))).left := inferInstanceAs (IsAffine (Spec _))
  haveI : IsAffine (TK R).left := inferInstanceAs (IsAffine (Spec _))
  have hinj : Function.Injective (toUnit (TK R)).left.appTop.hom := by
    have e : (toUnit (TK R)).left = jK R := by simp
    rw [e]
    exact jK_appTop_injective R
  have h0 := sec_eq_zero_of_sval_whiskerRight_eq_zero _ D.P.A (𝟙_ _) (TK R) (toUnit _) hinj _ D.P.L D.P.isLB _ _ _ d
    (fun w I hI => by
      have e : toUnit (TK R) ▷ D.P.A = lift (toUnit (TK R ⊗ D.P.A)) (snd _ _) := by
        ext1
        · exact toUnit_unique _ _
        · simp
      have e' : (TK R ⊗ D.P.A).hom = (fst (TK R) D.P.A).left ≫ jK R := (Over.w (fst (TK R) D.P.A)).symm
      have e₁ := hR χ _ (toUnit _) (fst (TK R) D.P.A) (snd _ _) w I hI
      have e₂ := (hS χ).2 _ (fst (TK R) D.P.A) w I hI
      have e₃ : gs (𝟙 _) w ⊤ (scal (TK R ⊗ D.P.A).hom q) * gs (𝟙 _) w ⊤ (scal (fst (TK R) D.P.A).left (a χ).val) =
          gs (𝟙 _) w ⊤ (scal (TK R ⊗ D.P.A).hom p) := by
        rw [← gs_mul _ w ⊤ trivial, e']
        congr 1
        refine (congrArg (· * _) (scal_jK _ q)).trans (Eq.trans ?_ (scal_jK _ p).symm)
        rw [← hpq]
        unfold scal
        rw [map_mul, map_mul]
      rw [e, hd _ _ w I hI, e₁, Units.val_mul, Units.val_mul, e₂, ← e₃]
      ring)
  refine sub_eq_zero.1 ((hd T y z J hJ).symm.trans ?_)
  refine (congrArg (gs _ z _) (h0 _)).trans ((gs_eq _ z _ (hJ.mem _ _) _).trans ?_)
  exact (congrArg _ (map_zero _)).trans (map_zero _)

end GlobalTheory.PsiInt
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.LevelVanishing

theorem fromSpecStalk_comp {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) (z : Y) :
    Y.fromSpecStalk z ≫ p =
      Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appTop ≫ Y.presheaf.germ ⊤ z trivial) := by
  rw [Spec.map_comp, Spec.map_comp, ← Scheme.fromSpecStalk_toSpecΓ, Category.assoc, Category.assoc,
    ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

theorem sval_mem_map {R : Type} [CommRing R] (I : Ideal R) {X Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R))
    {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (d : LB.Sec (LB.LinComb L φ ε))
    (H : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y), (∃ ρ : Z ⟶ Spec (CommRingCat.of (R ⧸ I)),
      ρ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = r ≫ p) → ∀ (z : Z) (J), Good L z J → sval d r z J = 0)
    (z : Y) (J) (hJ : Good L z J) :
    sval d (𝟙 _) z J ∈ I.map ((Y.presheaf.germ ⊤ z trivial).hom.comp
      ((p.appTop.hom).comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)) := by
  set ψ := (Y.presheaf.germ ⊤ z trivial).hom.comp
      ((p.appTop.hom).comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) with hψ
  by_cases htop : I.map ψ = ⊤
  · rw [htop]; trivial
  have : Nontrivial (Y.presheaf.stalk z ⧸ I.map ψ) := Ideal.Quotient.nontrivial_iff.2 htop
  have : IsLocalRing (Y.presheaf.stalk z ⧸ I.map ψ) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  let Q : CommRingCat.{0} := CommRingCat.of (Y.presheaf.stalk z ⧸ I.map ψ)
  let q : Y.presheaf.stalk z ⟶ Q := CommRingCat.ofHom (R := Y.presheaf.stalk z) (Ideal.Quotient.mk (I.map ψ))
  have : IsLocalHom q.hom := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  let r : Spec Q ⟶ Y := Spec.map q ≫ Y.fromSpecStalk z
  let w : Spec Q := IsLocalRing.closedPoint Q
  have hw : r w = z := by
    rw [Scheme.Hom.comp_apply, Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
  have hl : ∃ ρ : Spec Q ⟶ Spec (CommRingCat.of (R ⧸ I)),
      ρ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = r ≫ p := by
    refine ⟨Spec.map (CommRingCat.ofHom (Ideal.quotientMap (I.map ψ) ψ Ideal.le_comap_map)), ?_⟩
    rw [Category.assoc, fromSpecStalk_comp, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
  choose I' hI' using fun χ : Spec Q ⟶ X => exists_chart hL (χ w)
  have hz : z ∈ LB.wchart L φ (fun k => J (𝟙 _ ≫ φ k)) := hJ.mem φ (𝟙 _)
  have hm : r w ∈ LB.wchart L φ (fun k => J (𝟙 _ ≫ φ k)) := hw ▸ hz
  have e := sec_trans d r w (j := fun k => J (𝟙 _ ≫ φ k)) hm (Good.mem hI' φ r)
  have e0 : gs r w (LB.wchart L φ (fun k => I' (r ≫ φ k))) (d.f (fun k => I' (r ≫ φ k))) = 0 := H _ r hl w I' hI'
  rw [e0, mul_zero] at e
  replace e := (Scheme.Hom.germ_stalkMap_apply r _ w hm _).trans ((gs_eq r w _ hm _).symm.trans e)
  have e1 := congrArg (fun t => t.hom (d.f (fun k => J (𝟙 _ ≫ φ k))))
    (Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk q _ hm)
  simp only [Scheme.stalkClosedPointTo, CommRingCat.hom_comp, RingHom.comp_apply] at e1
  refine Ideal.Quotient.eq_zero_iff_mem.1 ((congrArg _ (gs_eq (𝟙 Y) z _ hz _)).trans ?_)
  exact e1.symm.trans ((congrArg (stalkClosedPointIso Q).hom.hom e).trans (map_zero _))

theorem main : (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (k : ℕ) (σ : U.SecGT (𝟙_ _) k) f, U.ExpT (𝟙_ _) k σ f → ∀ e : ℕ, ∃ s : Finset D.X, ∀ α ∉ s, ∀ (z : (𝟙_ _ ⊗ D.P.A).left) (J), Good D.P.L z J → sval (f α) (𝟙 _) z J ∈ (IsLocalRing.maximalIdeal V ^ (e + 1)).map (((𝟙_ _ ⊗ D.P.A).left.presheaf.germ ⊤ z trivial).hom.comp (((𝟙_ _ ⊗ D.P.A).hom.appTop.hom).comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom))) := by
  intro V _ _ _ _ D A G _ _ U k σ f h e
  obtain ⟨s, hs⟩ := h e
  refine ⟨s, fun α hα z J hJ => sval_mem_map _ (𝟙_ _ ⊗ D.P.A).hom D.P.isLB (f α) ?_ z J hJ⟩
  refine GlobalTheory.LiftTest.main V _ D e G (U.gt e) (𝟙_ _ ⊗ D.P.A) (snd _ _) _ D.P.L D.P.isLB _ _ _ (f α) ?_
  intro Z x r hr z J hJ
  choose JG hJG using fun χ : Z ⟶ G.left => exists_chart U.P.L.isLB (χ z)
  have hb : r ≫ (𝟙_ _ ⊗ D.P.A).hom = x ≫ (fstG (IsLocalRing.maximalIdeal V) e G).left ≫ G.hom := by
    rw [← Over.w (snd (𝟙_ _) D.P.A), ← Category.assoc, hr, Category.assoc, Over.w, Over.w]
  let xG : Over.mk (r ≫ (𝟙_ _ ⊗ D.P.A).hom) ⟶ G :=
    Over.homMk (x ≫ (fstG (IsLocalRing.maximalIdeal V) e G).left) (by rw [Category.assoc]; exact hb.symm)
  let rB : Over.mk (r ≫ (𝟙_ _ ⊗ D.P.A).hom) ⟶ 𝟙_ _ ⊗ D.P.A := Over.homMk r
  refine (hs Z x (lift (rB ≫ fst _ _) xG).left r ?_ hr ?_ z JG J hJG hJ).1 α hα
  · exact congrArg CommaMorphism.left (lift_snd (rB ≫ fst _ _) xG)
  · exact (congrArg CommaMorphism.left (lift_fst (rB ≫ fst _ _) xG)).symm

end GlobalTheory.LevelVanishing
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.TauValues

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem val_tau {Z : Scheme.{0}} (r : Z ⟶ (TK R).left) {z : Z} {J} (hJ : Good D.P.L z J) (a b : D.X) :
    val (D.tau a b) r z J =
      val (D.psi (a + b)) r z J * (val (D.psi a) r z J)⁻¹ * (val (D.psi b) r z J)⁻¹ * (val D.rigK r z J)⁻¹ :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))

theorem comp_cT {T : Over (Spec (CommRingCat.of R))} (κ : T ⟶ TK R) (χ : D.X) :
    κ ≫ toUnit (TK R) ≫ D.c χ = cT D T χ := by
  rw [← Category.assoc, comp_toUnit]

theorem val_rigK {T : Over (Spec (CommRingCat.of R))} (κ : T ⟶ TK R) {z : T.left} {J} (hJ : Good D.P.L z J) :
    val D.rigK κ.left z J = rigV D z J := by
  refine (val_pull hJ _ _ _).trans ?_
  have e : κ.left ≫ (toUnit (TK R)).left = T.hom := by
    rw [← Over.comp_left, comp_toUnit]; rfl
  exact congrArg (fun q : T.left ⟶ Spec (CommRingCat.of R) =>
    val (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig q z J) e

theorem bimult_iff {T : Over (Spec (CommRingCat.of R))} (κ : T ⟶ TK R) {z : T.left} {J} (hJ : Good D.P.L z J)
    (a b m : D.X) :
    val (D.psi (a + b + m)) κ.left z J * val (D.psi a) κ.left z J * val (D.psi b) κ.left z J *
        val (D.psi m) κ.left z J * rigV D z J * cubV D.cub z J (cT D T a) (cT D T b) (cT D T m) =
      val (D.psi (a + b)) κ.left z J * val (D.psi (a + m)) κ.left z J * val (D.psi (b + m)) κ.left z J ↔
    val (LB.mulGen D.P.L _ _ _ _ (D.tau (a + b) m)
        (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a b m))) κ.left z J =
      val (LB.mulGen D.P.L _ _ _ _ (D.tau a m) (D.tau b m)) κ.left z J := by
  have c : val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a b m)) κ.left z J =
      cubV D.cub z J (cT D T a) (cT D T b) (cT D T m) := by
    refine (val_cub D.cub κ hJ (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c b) (toUnit (TK R) ≫ D.c m)).trans ?_
    rw [comp_cT, comp_cT, comp_cT]
  have l := (val_mul hJ (D.tau (a + b) m)
    (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a b m)) κ.left).trans
    (congrArg₂ (· * ·) (val_tau D κ.left hJ _ _) c)
  have r := (val_mul hJ (D.tau a m) (D.tau b m) κ.left).trans
    (congrArg₂ (· * ·) (val_tau D κ.left hJ _ _) (val_tau D κ.left hJ _ _))
  rw [val_rigK D κ hJ] at l r
  rw [l, r]
  constructor <;> intro h <;> apply Additive.ofMul.injective <;> have e := congrArg Additive.ofMul h <;>
    simp only [ofMul_mul, ofMul_inv] at e ⊢ <;> linear_combination (norm := abel) e

theorem val_even {T : Over (Spec (CommRingCat.of R))} (κ : T ⟶ TK R) {z : T.left} {J} (hJ : Good D.P.L z J)
    (m : D.X) :
    val (LB.mulGen D.P.L _ _ _ _ (D.psi (-m)) (LB.pullGen D.P.L _ _ D.sym (D.xK m))) κ.left z J =
      val (D.psi (-m)) κ.left z J * val D.sym (cT D T m).left z J := by
  refine (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ((val_pull hJ _ _ _).trans ?_))
  have e : κ.left ≫ D.xK m = (cT D T m).left := by
    rw [← comp_cT D κ m]; rfl
  rw [e]

theorem bimult_iff' {T : Over (Spec (CommRingCat.of R))} (κ : T ⟶ TK R) [Flat κ.left] [Surjective κ.left] :
    (∀ (z : T.left) J, Good D.P.L z J → ∀ a b m : D.X,
      val (D.psi (a + b + m)) κ.left z J * val (D.psi a) κ.left z J * val (D.psi b) κ.left z J *
        val (D.psi m) κ.left z J * rigV D z J * cubV D.cub z J (cT D T a) (cT D T b) (cT D T m) =
      val (D.psi (a + b)) κ.left z J * val (D.psi (a + m)) κ.left z J * val (D.psi (b + m)) κ.left z J) ↔
    D.TauBimult :=
  ⟨fun h a b m => corr_of_val_flat_surjective κ.left D.P.isLB fun z J hJ => (bimult_iff D κ hJ a b m).1 (h z J hJ a b m),
    fun h _ _ hJ a b m => (bimult_iff D κ hJ a b m).2 (val_corr hJ (h a b m) κ.left)⟩

theorem even_iff {T : Over (Spec (CommRingCat.of R))} (κ : T ⟶ TK R) [Flat κ.left] [Surjective κ.left] :
    (∀ (z : T.left) J, Good D.P.L z J → ∀ m : D.X,
      val (D.psi (-m)) κ.left z J * val D.sym (cT D T m).left z J = val (D.psi m) κ.left z J) ↔ D.PsiEven :=
  ⟨fun h m => corr_of_val_flat_surjective κ.left D.P.isLB fun z J hJ => (val_even D κ hJ m).trans (h z J hJ m),
    fun h _ _ hJ m => (val_even D κ hJ m).symm.trans (val_corr hJ (h m) κ.left)⟩

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F], ((∀ (z : (TF (R := R) F).left) J, Good D.P.L z J → ∀ a b m : D.X, val (Z := (TF (R := R) F).left) (D.psi (a + b + m)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (a)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (b)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (m)) (jFK (R := R) F) z J * rigV D z J * cubV D.cub z J (cT D _ a) (cT D _ b) (cT D _ m) = val (Z := (TF (R := R) F).left) (D.psi (a + b)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (a + m)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (b + m)) (jFK (R := R) F) z J) ↔ D.TauBimult) ∧ ((∀ (z : (TF (R := R) F).left) J, Good D.P.L z J → ∀ m : D.X, val (Z := (TF (R := R) F).left) (D.psi (-m)) (jFK (R := R) F) z J * val D.sym (cT D (TF (R := R) F) m).left z J = val (Z := (TF (R := R) F).left) (D.psi (m)) (jFK (R := R) F) z J) ↔ D.PsiEven) := by
  intro R _ _ D F _ _
  let κ : TF (R := R) F ⟶ TK R := Over.homMk (jFK (R := R) F) rfl
  have hκ : κ.left = Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) F)) := rfl
  have : Flat κ.left := by
    rw [hκ]
    exact (HasRingHomProperty.Spec_iff (P := @Flat)).2 (RingHom.Flat.of_isField (Field.toIsField (FractionRing R)) _)
  have : Surjective κ.left := by
    have : Subsingleton (TK R).left := inferInstanceAs (Subsingleton (PrimeSpectrum (FractionRing R)))
    exact ⟨fun y => ⟨(default : PrimeSpectrum F), Subsingleton.elim _ _⟩⟩
  exact ⟨bimult_iff' D κ, even_iff D κ⟩

end GlobalTheory.TauValues
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory

theorem stalkMap_mem_map_base {R : Type} [CommRing R] (I : Ideal R) {Z Z' : Scheme.{0}}
    (p : Z ⟶ Spec (CommRingCat.of R)) (p' : Z' ⟶ Spec (CommRingCat.of R)) (ρ : Z' ⟶ Z) (h : ρ ≫ p = p') (z : Z')
    (a : Z.presheaf.stalk (ρ z))
    (ha : a ∈ I.map ((Z.presheaf.germ ⊤ (ρ z) trivial).hom.comp
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom))) :
    (ρ.stalkMap z).hom a ∈ I.map ((Z'.presheaf.germ ⊤ z trivial).hom.comp
      (p'.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)) := by
  subst h
  have := Ideal.mem_map_of_mem (ρ.stalkMap z).hom ha
  rw [Ideal.map_map] at this
  convert this using 2
  ext r
  exact (Scheme.Hom.germ_stalkMap_apply ρ ⊤ z trivial _).symm

theorem map_base_eq_bot {R : Type} [CommRing R] (I : Ideal R) {Z : Scheme.{0}}
    (ρ : Z ⟶ Spec (CommRingCat.of (R ⧸ I))) (z : Z) :
    I.map ((Z.presheaf.germ ⊤ z trivial).hom.comp
      ((ρ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).appTop.hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)) = ⊥ := by
  rw [Ideal.map_eq_bot_iff_le_ker]
  intro r hr
  have e := congrArg (fun q => q.hom r)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk I)))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
    Ideal.Quotient.eq_zero_iff_mem.2 hr, map_zero] at e
  rw [RingHom.mem_ker, Scheme.Hom.comp_appTop]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply]
  erw [← e]
  simp only [map_zero]

theorem exists_order_translates : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (D : DegPre V) (k : ℕ) (f₀ : SecBT D (𝟙_ _) k 0), (∃ j, f₀.f j ≠ 0) → ∃ m : ℕ, ∀ χ : D.X, ∃ (z : (𝟙_ _ ⊗ D.P.A).left) (J : _), Good D.P.L z J ∧ sval f₀ (lift (fst (𝟙_ _) D.P.A) (snd (𝟙_ _) D.P.A * cT D _ χ)).left z J ∉ (IsLocalRing.maximalIdeal V ^ (m + 1)).map (((𝟙_ _ ⊗ D.P.A).left.presheaf.germ ⊤ z trivial).hom.comp (((𝟙_ _ ⊗ D.P.A).hom.appTop.hom).comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom)) := by
  intro V _ _ _ hV D k f₀ ⟨j, hj⟩
  haveI := hV.1
  haveI := D.P.isAb.smooth
  haveI := D.P.isAb.geomConnected
  haveI : IsAffine (𝟙_ (Over (Spec (CommRingCat.of V)))).left :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of V)))
  haveI : IsNoetherianRing Γ((𝟙_ (Over (Spec (CommRingCat.of V)))).left, ⊤) :=
    isNoetherianRing_of_ringEquiv V (Scheme.ΓSpecIso (CommRingCat.of V)).commRingCatIsoToRingEquiv.symm
  obtain ⟨m, z₀, J₀, hJ₀, h₀⟩ : ∃ (m : ℕ) (z : (𝟙_ _ ⊗ D.P.A).left) (J : _), Good D.P.L z J ∧
      sval f₀ (𝟙 _) z J ∉ (IsLocalRing.maximalIdeal V ^ (m + 1)).map (((𝟙_ _ ⊗ D.P.A).left.presheaf.germ ⊤ z trivial).hom.comp (((𝟙_ _ ⊗ D.P.A).hom.appTop.hom).comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom)) := by
    by_contra hc
    push Not at hc
    refine hj (sec_eq_zero_of_sval_finite_level V (IsLocalRing.maximalIdeal V) (𝟙_ _) D.P.A ?_ _ D.P.L D.P.isLB
      _ _ _ f₀ ?_ j)
    · intro r hr
      let e : V ≃+* Γ(Spec (CommRingCat.of V), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of V)).commRingCatIsoToRingEquiv.symm
      have h1 : r ∈ Ideal.jacobson (⊥ : Ideal V) := by
        rwa [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
      have h2 := Ideal.mem_map_of_mem e.toRingHom h1
      rw [Ideal.map_jacobson_of_bijective (f := e.toRingHom) e.bijective, Ideal.map_bot] at h2
      exact h2
    · rintro e Z r ⟨ρ, hρ⟩ z J hJ
      obtain ⟨g, hs, -⟩ := values_natural _ _ _ _ D.P.L _ (famφT D (𝟙_ _) 0) (DegPre.famε k) (𝟙 _) r z J hJ
      have h1 := stalkMap_mem_map_base _ _ _ r hρ.symm z _ (hc e _ _ g)
      rw [← hs f₀, Category.comp_id, map_base_eq_bot] at h1
      exact h1
  refine ⟨m, fun χ => ?_⟩
  let σ : 𝟙_ _ ⊗ D.P.A ⟶ 𝟙_ _ ⊗ D.P.A := lift (fst (𝟙_ _) D.P.A) (snd (𝟙_ _) D.P.A * (cT D _ χ)⁻¹)
  let τ : 𝟙_ _ ⊗ D.P.A ⟶ 𝟙_ _ ⊗ D.P.A := lift (fst (𝟙_ _) D.P.A) (snd (𝟙_ _) D.P.A * cT D _ χ)
  have hστ : σ ≫ τ = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · exact toUnit_unique _ _
    · have : σ ≫ cT D _ χ = cT D _ χ := by
        rw [cT, ← Category.assoc, toUnit_unique (σ ≫ toUnit _) (toUnit _)]
      rw [Category.assoc, lift_snd, MonObj.comp_mul, this, lift_snd, inv_mul_cancel_right, Category.id_comp]
  obtain ⟨g, hs, -⟩ := values_natural _ _ _ _ D.P.L _ (famφT D (𝟙_ _) 0) (DegPre.famε k) τ.left σ.left z₀ J₀ hJ₀
  refine ⟨_, _, g, fun hm => h₀ ?_⟩
  have h1 := stalkMap_mem_map_base _ _ _ σ.left (Over.w σ) z₀ _ hm
  have h2 : σ.left ≫ τ.left = 𝟙 _ := congrArg CommaMorphism.left hστ
  rw [← hs f₀, h2] at h1
  exact h1

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.UU.ExpLin

theorem sval_comb {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {t t' t'' : LB.Sec (LB.LinComb L φ ε)} (a : Γ(Y, ⊤))
    (h : ∀ j, t''.f j = (Y.presheaf.map (homOfLE le_top).op).hom a * t.f j + t'.f j)
    (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    sval t'' r z J = gs r z ⊤ a * sval t r z J + sval t' r z J := by
  have hm := hJ.mem φ r
  refine (congrArg (gs r z _) (h _)).trans ?_
  refine (gs_add _ _ _ hm _ _).trans (congrArg (· + _) ((gs_mul _ _ _ hm _ _).trans (congrArg (· * _) ?_)))
  exact gs_res r z le_top hm a

theorem gs_scal_mul {R : Type} [CommRing R] {Y Z : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ Y) (z : Z)
    (a b : R) : gs r z ⊤ (scal p (a * b)) = gs r z ⊤ (scal p a) * gs r z ⊤ (scal p b) := by
  rw [← gs_mul r z ⊤ trivial]
  simp only [scal, map_mul]

theorem sum_append {α β M : Type*} [AddCommMonoid M] {n m : ℕ} (g : α → β → M) (c : Fin n → α) (c' : Fin m → α)
    (s : Fin n → β) (s' : Fin m → β) :
    ∑ i, g (Fin.append c c' i) (Fin.append s s' i) = ∑ i, g (c i) (s i) + ∑ i, g (c' i) (s' i) := by
  simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right]

theorem expF_linear : (AllPre fun {V} _ _ _ {D} {A} {_} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ) t t' t'' s s' s'' (c : F), U.ExpF F k t s → U.ExpF F k t' s' → (∀ j, t''.f j = liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * t.f j + t'.f j) → (∀ α j, (s'' α).f j = DegPre.constBF D F c _ * (s α).f j + (s' α).f j) → U.ExpF F k t'' s'') := by
  intro V _ _ _ _ D A G _ _ U F _ _ k t t' t'' s s' s'' c ⟨n, a, σ, f, h1, h2, h3⟩ ⟨m, a', σ', f', h1', h2', h3'⟩ ht hs
  refine ⟨n + m, Fin.append (fun i => c * a i) a', Fin.append σ σ', Fin.append f f', fun i => ?_,
    fun Z rA y rG e1 e2 z JA JG hA hG => ?_, fun α Z rF rB e z J hJ => ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_left]; exact h1 i
    · simp only [Fin.append_right]; exact h1' i
  · rw [sum_append (fun x y => gs rA z ⊤ (scal (fst (TFK (R := V) F) A.A).left x) * sval y rG z JG),
      ← h2' Z rA y rG e1 e2 z JA JG hA hG]
    simp only [gs_scal_mul, _root_.mul_assoc]
    rw [← Finset.mul_sum, ← h2 Z rA y rG e1 e2 z JA JG hA hG,
      sval_comb (L := A.L) (φ := fun _ : Fin 1 => (snd (TFK (R := V) F) A.A).left) (ε := fun _ => (k : ℤ))
        (scal (fst (TFK (R := V) F) A.A).left c) ht rA z hA]
    ring
  · rw [sum_append (fun x (y : ∀ α, SecBT D (𝟙_ _) k α) =>
      gs rF z ⊤ (scal (fst (TF (R := V) F) D.P.A).left x) * sval (y α) rB z J), ← h3' α Z rF rB e z J hJ]
    simp only [gs_scal_mul, _root_.mul_assoc]
    rw [← Finset.mul_sum, ← h3 α Z rF rB e z J hJ]
    exact sval_comb (scal (fst (TF (R := V) F) D.P.A).left c) (hs α) rF z hJ

end GlobalTheory.UU.ExpLin
end
end
