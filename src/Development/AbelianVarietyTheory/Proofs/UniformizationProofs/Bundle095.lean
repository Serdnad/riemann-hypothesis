module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.SvalTwistOne
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle089
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle067
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle021
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle016
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsFiniteProjectiveComplexQuasiIso
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle021
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechLBHomologyFiniteOfAffineCover
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle011
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle046
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.AppCompatGeneric
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory
namespace FieldChange

theorem sval_extend {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {φ₁ : K → (Y' ⟶ X)} {ε : K → ℤ} (h : Y' ⟶ Y) (hφ : φ₁ = fun k => h ≫ φ k)
    (s : LB.Sec (LB.LinComb L φ₁ ε)) (f : LB.Sec (LB.LinComb L φ ε))
    (H : ∀ y J, Good L y J → sval s (𝟙 _) y J = sval f h y J) {Z : Scheme.{0}} (r : Z ⟶ Y') (z : Z) (J)
    (hJ : Good L z J) : sval s r z J = sval f (r ≫ h) z J := by
  subst hφ
  have e := sec_ext_val hL (s := s) (s' := DVR.pullSec L φ ε f h) (fun y J hJ => by
    rw [DVR.SectionScalarValuation.sval_pullSec φ ε f h _ y hJ, Category.id_comp]; exact H y J hJ)
  rw [← DVR.SectionScalarValuation.sval_pullSec φ ε f h r z hJ]
  exact congrArg (gs r z _) (e _)

theorem gs_scal_comp {R : Type} [CommRing R] {Y Y' Z : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) (h : Y' ⟶ Y)
    (r : Z ⟶ Y') (z : Z) (c : R) : gs (r ≫ h) z ⊤ (scal p c) = gs r z ⊤ (scal (h ≫ p) c) :=
  (gs_pull r h z ⊤ (by trivial) _).symm

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {T : Over (Spec (CommRingCat.of R))}
  {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem fam_comp (φ : TF (R := R) F ⟶ T) (α : D.X) :
    DegPre.famφ D F α = fun i => (φ ▷ D.P.A).left ≫ famφT D T α i := by
  have e₀ : φ ▷ D.P.A ≫ snd T D.P.A = snd _ _ := whiskerRight_snd _ _
  have e₂ : φ ▷ D.P.A ≫ DVR.cP D _ α = DVR.cP D _ α := DVR.comp_cP D _ α
  funext i
  fin_cases i
  · exact (congrArg (fun q => q.left) e₀).symm
  · refine (congrArg (fun q : DegPre.BF D F ⟶ D.P.A => q.left)
      ((MonObj.comp_mul (φ ▷ D.P.A) (snd T D.P.A) (DVR.cP D _ α)).trans ?_)).symm
    rw [e₀, e₂]; rfl
  · exact (congrArg (fun q => q.left) e₂).symm
  · exact (congrArg (fun q : DegPre.BF D F ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) (φ ▷ D.P.A))).symm

theorem tr_comp (φ : TF (R := R) F ⟶ T) (mu : D.X) :
    φ ▷ D.P.A ≫ trT D (toUnit T ≫ D.c mu) = DegPre.trF D F mu ≫ φ ▷ D.P.A := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [trT, DegPre.trF]
  · rw [Category.assoc, Category.assoc, whiskerRight_snd, trT, DegPre.trF, lift_snd, lift_snd]
    refine (MonObj.comp_mul (φ ▷ D.P.A) (snd T D.P.A) (fst _ _ ≫ DVR.cP D _ mu)).trans ?_
    rw [whiskerRight_snd, DVR.comp_cP, DVR.comp_cP]; rfl

theorem pullB_all {φ : TF (R := R) F ⟶ T} {k : ℕ} {f : ∀ α, SecBT D T k α} {s : Raw D F k} (H : PullB D F φ k f s)
    (α : D.X) {Z : Scheme.{0}} (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J) (hJ : Good D.P.L z J) :
    sval (s α) r z J = sval (f α) (r ≫ (φ ▷ D.P.A).left) z J :=
  sval_extend D.P.isLB _ (fam_comp D φ α) (s α) (f α) (H α) r z J hJ

theorem isUnit_scal {c : R} (hc : c ≠ 0) {Z : Scheme.{0}} (r : Z ⟶ (DegPre.BF D F).left) (z : Z) :
    IsUnit (gs r z ⊤ (scal (DegPre.BF D F).hom c)) := by
  have e : (DegPre.BF D F).hom = ((fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F) ≫ jK R := by
    rw [Category.assoc]; exact (Over.w (fst (TF (R := R) F) D.P.A)).symm
  have hu : IsUnit (scal (jK R) c) := by
    have n := congrArg (fun q => q.hom c)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at n
    have hc' : IsUnit (algebraMap R (FractionRing R) c) :=
      IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hc)
    exact (congrArg IsUnit n).mp (hc'.map _)
  rw [e, gs_eq _ _ ⊤ (by trivial)]
  exact ((hu.map ((fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F).appTop.hom).map _).map _

end FieldChange


open FieldChange in
theorem famFE_field_change : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (T : Over (Spec (CommRingCat.of R))) [IsAffine T.left] (k : ℕ) (f : ∀ α, SecBT D T k α) (F F' : Type) [Field F] [Algebra (FractionRing R) F] [Field F'] [Algebra (FractionRing R) F'] (φ : TF (R := R) F ⟶ T) (φ' : TF (R := R) F' ⟶ T) (s : Raw D F k) (s' : Raw D F' k), Function.Injective φ.left.appTop.hom → PullB D F φ k f s → PullB D F' φ' k f s' → DegPre.FamFE D F k s → DegPre.FamFE D F' k s' := by
  intro hG R _ _ _ D T _ k f F F' _ _ _ _ φ φ' s s' hinj hs hs' hfe mu α u' hu' hc'
  obtain ⟨u₀, r₁, r₂, hu₀, -, h₂, hv⟩ := GlobalTheory.UU.IntGen.main hG R D T k α mu
  obtain ⟨⟨u, hu, hc⟩, -⟩ := DVR.gen_fe (D := D) (F := F) hG k mu α
  have : Smooth D.P.A.hom := D.P.isAb.smooth
  have : IsAffine (TF (R := R) F).left := inferInstanceAs (IsAffine (Spec _))
  have sc : ∀ {E : Type} [Field E] [Algebra (FractionRing R) E] (ψ : TF (R := R) E ⟶ T) (c : R)
      (y : (DegPre.BF D E).left), gs (ψ ▷ D.P.A).left y ⊤ (scal (T ⊗ D.P.A).hom c) =
        gs (𝟙 _) y ⊤ (scal (DegPre.BF D E).hom c) := fun ψ c y => by
    rw [← Over.w (ψ ▷ D.P.A), ← gs_scal_comp, Category.id_comp]
  have tr : ∀ {E : Type} [Field E] [Algebra (FractionRing R) E] (ψ : TF (R := R) E ⟶ T),
      (ψ ▷ D.P.A).left ≫ (trT D (toUnit T ≫ D.c mu)).left = (𝟙 _ ≫ (DegPre.trF D E mu).left) ≫ (ψ ▷ D.P.A).left :=
    fun ψ => by rw [Category.id_comp]; exact congrArg (fun q => q.left) (tr_comp D ψ mu)
  have key := sec_relation_descends _ D.P.A T (TF (R := R) F) φ hinj _ _ D.P.L D.P.isLB _ _ _
    (famφT D T α) (DegPre.famε k) (famφT D T (α + k • mu)) (DegPre.famε k)
    (deltaφT D (α + k • mu) α (toUnit T ≫ D.c mu)) (DegPre.deltaε k) (trT D (toUnit T ≫ D.c mu)).left
    (f α) (f (α + k • mu)) u₀ (scal (T ⊗ D.P.A).hom r₁) (scal (T ⊗ D.P.A).hom r₂) hu₀
    (fun U _ h => by
      refine Eq.symm (Eq.trans (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4 ⊕ Fin 4) (U := U) _
          (c := ∏ i, h ((trT D (toUnit T ≫ D.c mu)).left ≫ famφT D T α i) ^ DegPre.famε k i) rfl
          (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _
            (c := ∏ i, h (famφT D T (α + k • mu) i) ^ DegPre.famε k i) rfl (DVR.prod_neg _ _ rfl))) ?_)
      exact (mul_comm _ _).trans (inv_mul_cancel_right _ _))
    (fun y J hJ => by
      have e₁ := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (hfe mu α u hu hc) _ (𝟙 _) y J hJ
      have e₂ := hv F φ u hu hc _ (𝟙 _) y J hJ
      rw [Category.id_comp] at e₂
      rw [sc, sc, tr, ← pullB_all D hs α _ y J hJ, ← hs _ y J hJ, e₁, mul_left_comm, e₂, mul_left_comm])
  refine (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u').2 fun y J hJ => ?_
  have e₁ := key _ (φ' ▷ D.P.A).left y J hJ
  have e₂ := hv F' φ' u' hu' hc' _ (𝟙 _) y J hJ
  rw [Category.id_comp] at e₂
  rw [sc, sc, tr, ← pullB_all D hs' α _ y J hJ, ← hs' _ y J hJ, mul_left_comm, ← e₂, mul_left_comm] at e₁
  exact (isUnit_scal D h₂ _ y).mul_left_cancel e₁

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.ConvFE
open ReciprocityTheory.ChartRestriction.G.DVR

def cst {R : Type} [CommRing R] {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of R)) (z : Z) : R →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ ⊤ z trivial).hom.comp (q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

theorem gs_scal {R : Type} [CommRing R] {Y Z : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ Y) (z : Z) (c : R) :
    gs r z ⊤ (scal p c) = cst (r ≫ p) z c :=
  (gs_pull r p z ⊤ trivial _).trans (gs_eq _ z ⊤ trivial _)

theorem cst_specMap {A R : Type} [CommRing A] [CommRing R] {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of R)) (z : Z)
    (f : A →+* R) (c : A) : cst (q ≫ Spec.map (CommRingCat.ofHom f)) z c = cst q z (f c) := by
  have e := congrArg (fun t => t.hom c) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  simp only [cst, RingHom.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
  rw [e]

theorem sval_secScale {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (c : Γ(Y, ⊤)) (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    sval (SecOps.secScale c s) r z J = gs r z ⊤ c * sval s r z J :=
  (gs_mul r z _ (hJ.mem φ r) _ _).trans (congrArg (· * _) (gs_res r z le_top (hJ.mem φ r) c))

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem pullB_val {T : Over (Spec (CommRingCat.of R))} {φ : TF (R := R) F ⟶ T} {k : ℕ} {f : ∀ α, SecBT D T k α}
    {s : Raw D F k} (h : PullB D F φ k f s) (α : D.X) {Z : Scheme.{0}} (r : Z ⟶ (DegPre.BF D F).left) (z : Z) {J}
    (hJ : Good D.P.L z J) : sval (s α) r z J = sval (f α) (r ≫ (φ ▷ D.P.A).left) z J := by
  have a := (values_natural _ _ _ _ D.P.L (Fin 4) _ _ (𝟙 (DegPre.BF D F).left) r z J hJ).2.1 (s α)
  have b := (values_natural _ _ _ _ D.P.L (Fin 4) _ _ (φ ▷ D.P.A).left r z J hJ).2.1 (f α)
  have hJ' : Good D.P.L (r z) (fun ψ => J (r ≫ ψ)) := fun ψ => hJ _
  rw [Category.comp_id] at a
  exact a.trans ((congrArg _ (h α _ _ hJ')).trans b.symm)

theorem whisker_trT {T : Over (Spec (CommRingCat.of R))} (φ : TF (R := R) F ⟶ T) (mu : D.X) :
    φ ▷ D.P.A ≫ trT D (toUnit T ≫ D.c mu) = DegPre.trF D F mu ≫ φ ▷ D.P.A := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [trT, DegPre.trF]
  · rw [Category.assoc, Category.assoc, whiskerRight_snd, trT, DegPre.trF, lift_snd, lift_snd]
    refine (MonObj.comp_mul (φ ▷ D.P.A) (snd T D.P.A) (fst T D.P.A ≫ cP D T mu)).trans ?_
    rw [whiskerRight_snd, comp_cP, comp_cP]
    rfl

theorem cst_unit {r : R} (hr : r ≠ 0) (z : (DegPre.BF D F).left) : IsUnit (cst (DegPre.BF D F).hom z r) := by
  have e : (DegPre.BF D F).hom = ((fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F) ≫ jK R :=
    (Over.w (fst (TF (R := R) F) D.P.A)).symm.trans (Category.assoc _ _ _).symm
  rw [e]
  refine (congrArg IsUnit ((cst_specMap _ z (algebraMap R (FractionRing R)) r).trans (cst_specMap _ z _ _))).mpr
    (IsUnit.map _ (IsUnit.map _ (Ne.isUnit ?_)))
  exact fun h => hr (IsFractionRing.injective R (FractionRing R) (h.trans (map_zero _).symm))

theorem form_delta {T : Over (Spec (CommRingCat.of R))} (k : ℕ) (α' α : D.X) (b : T ⟶ D.P.A) :
    FormEq (famφT D T α') (DegPre.famε k) (Sum.elim (fun i => (trT D b).left ≫ famφT D T α i) (deltaφT D α' α b))
      (Sum.elim (DegPre.famε k) (DegPre.deltaε k)) := fun U _ h => by
  refine Eq.symm (Eq.trans (prod_sum₂ (K := Fin 4) (K' := Fin 4 ⊕ Fin 4) (U := U) _
    (c := ∏ i, h ((trT D b).left ≫ famφT D T α i) ^ DegPre.famε k i) rfl
    (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _
      (c := ∏ i, h (famφT D T α' i) ^ DegPre.famε k i) rfl (prod_neg _ _ rfl))) ?_)
  exact (mul_comm _ _).trans (inv_mul_cancel_right _ _)

theorem noeth (V W : Type) [CommRing V] [IsNoetherianRing V] [CommRing W] [Algebra V W] [Module.Finite V W] :
    IsNoetherianRing Γ((TA V W).left, ⊤) := by
  haveI : IsNoetherianRing W := isNoetherian_of_tower V inferInstance
  exact isNoetherianRing_of_ringEquiv W (Scheme.ΓSpecIso (CommRingCat.of W)).commRingCatIsoToRingEquiv.symm

theorem jac (V W : Type) [CommRing V] [IsLocalRing V] [CommRing W] [IsLocalRing W] [Algebra V W]
    [IsLocalHom (algebraMap V W)] (r : V) (hr : r ∈ IsLocalRing.maximalIdeal V) :
    scal (TA V W).hom r ∈ Ideal.jacobson (⊥ : Ideal Γ((TA V W).left, ⊤)) := by
  let E : W ≃+* Γ((TA V W).left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of W)).commRingCatIsoToRingEquiv.symm
  have e : scal (TA V W).hom r = E (algebraMap V W r) :=
    (congrArg (fun t => t.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap V W)))).symm
  have hw : algebraMap V W r ∈ Ideal.jacobson (⊥ : Ideal W) := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact map_nonunit (algebraMap V W) r hr
  rw [e, Ideal.mem_jacobson_bot]
  intro y
  have := (Ideal.mem_jacobson_bot.1 hw (E.symm y)).map E
  simpa using this

theorem sval_twist {W : Type} [CommRing W] [Algebra R W] {k : ℕ} (a : Multiplicative D.X →* Wˣ)
    (f : ∀ α, SecBT D (TA R W) k α) (α : D.X) {Z : Scheme.{0}} (r : Z ⟶ (TA R W ⊗ D.P.A).left) (z : Z) {J}
    (hJ : Good D.P.L z J) : sval (GlobalTheory.UU.twist a f α) r z J =
      cst (R := W) (r ≫ (fst (TA R W) D.P.A).left) z (a (Multiplicative.ofAdd α)).val * sval (f α) r z J :=
  (sval_secScale _ _ r z hJ).trans (congrArg (· * _) (gs_scal (R := W) _ r z _))

theorem term_val {W : Type} [CommRing W] [Algebra R W] {φ : TF (R := R) F ⟶ TA R W} {k l : ℕ}
    {f : ∀ α, SecBT D (TA R W) k α} {g : ∀ α, SecBT D (TA R W) l α} {s : Raw D F k} {s' : Raw D F l}
    (hf : PullB D F φ k f s) (hg : PullB D F φ l g s') (a a' : Multiplicative D.X →* Wˣ) {β ga α : D.X}
    {p : SecBT D (TA R W) (k + l) α} (hp : IsProdB (GlobalTheory.UU.twist a f β) (GlobalTheory.UU.twist a' g ga) p)
    {Z : Over (Spec (CommRingCat.of R))} (r : Z ⟶ DegPre.BF D F) (z : Z.left) {J} (hJ : Good D.P.L z J) :
    sval p (r ≫ φ ▷ D.P.A).left z J =
      cst (R := W) (r ≫ fst _ _ ≫ φ).left z (a (Multiplicative.ofAdd β) * a' (Multiplicative.ofAdd ga)).val *
        (sval (s β) r.left z J * sval (s' ga) r.left z J *
          (cubV D.cub z J (toUnit Z ≫ D.c β) (toUnit Z ≫ D.c ga) (r ≫ snd _ _)).val) := by
  have e : (r ≫ φ ▷ D.P.A).left ≫ (fst (TA R W) D.P.A).left = (r ≫ fst _ _ ≫ φ).left := by
    rw [← Over.comp_left, Category.assoc, whiskerRight_fst]
  rw [hp Z _ z J hJ, sval_twist a f β _ z hJ, sval_twist a' g ga _ z hJ, e, pullB_val hf β _ z hJ,
    pullB_val hg ga _ z hJ, Category.assoc, whiskerRight_snd, Units.val_mul, map_mul, Over.comp_left _ _ _ r (φ ▷ D.P.A)]
  ring

theorem term_rel (hG : GlobalFnsSt) (hB : D.TauBimult) {W : Type} [CommRing W] [Algebra R W]
    {φ : TF (R := R) F ⟶ TA R W} {k l : ℕ}
    {f : ∀ α, SecBT D (TA R W) k α} {g : ∀ α, SecBT D (TA R W) l α} {s : Raw D F k} {s' : Raw D F l}
    (hf : PullB D F φ k f s) (hg : PullB D F φ l g s') (hs : DegPre.FamFE D F k s) (hs' : DegPre.FamFE D F l s')
    (a a' : Multiplicative D.X →* Wˣ) (mu α β : D.X)
    (ha : a (Multiplicative.ofAdd (k • mu)) * a' (Multiplicative.ofAdd (l • mu)) = 1)
    {p : SecBT D (TA R W) (k + l) α} (hp : IsProdB (GlobalTheory.UU.twist a f β) (GlobalTheory.UU.twist a' g (α - β)) p)
    {p' : SecBT D (TA R W) (k + l) (α + (k + l) • mu)}
    (hp' : IsProdB (GlobalTheory.UU.twist a f (β + k • mu)) (GlobalTheory.UU.twist a' g (α + (k + l) • mu - (β + k • mu))) p')
    (u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F (k + l) α mu) (DegPre.deltaε (k + l)))) (hu : u.IsGen)
    (hc : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (DegPre.famMult D F (k + l) mu α))
    (z : (DegPre.BF D F).left) {J} (hJ : Good D.P.L z J) :
    sval p' (φ ▷ D.P.A).left z J =
      sval p ((φ ▷ D.P.A).left ≫ (trT D (toUnit _ ≫ D.c mu)).left) z J * (val u (𝟙 _) z J).val := by
  have hγ : α + (k + l) • mu - (β + k • mu) = α - β + l • mu := by rw [add_nsmul]; abel
  have e₁ := term_val hf hg a a' hp' (𝟙 (DegPre.BF D F)) z hJ
  have e₂ := term_val hf hg a a' hp (𝟙 (DegPre.BF D F) ≫ DegPre.trF D F mu) z hJ
  have e₃ := ConvTermFE.conv_term_fe hG R D hB F k l s s' hs hs' mu α β (α - β) _ _ (add_sub_cancel _ _) rfl hγ u hu hc
    _ (𝟙 (DegPre.BF D F)) z J hJ
  have e₄ : (𝟙 (DegPre.BF D F) ≫ DegPre.trF D F mu) ≫ fst _ _ ≫ φ = 𝟙 (DegPre.BF D F) ≫ fst _ _ ≫ φ := by
    rw [Category.id_comp, Category.id_comp, DegPre.trF, lift_fst_assoc]
  have e₅ : a (Multiplicative.ofAdd (β + k • mu)) * a' (Multiplicative.ofAdd (α + (k + l) • mu - (β + k • mu))) =
      a (Multiplicative.ofAdd β) * a' (Multiplicative.ofAdd (α - β)) := by
    rw [hγ, ofAdd_add, ofAdd_add, map_mul, map_mul, _root_.mul_mul_mul_comm, ha, _root_.mul_one]
  have e₆ : (φ ▷ D.P.A).left ≫ (trT D (toUnit _ ≫ D.c mu)).left =
      ((𝟙 (DegPre.BF D F) ≫ DegPre.trF D F mu) ≫ φ ▷ D.P.A).left := by
    rw [Category.id_comp, ← whisker_trT, Over.comp_left]
  rw [e₅, e₃, Category.id_comp (φ ▷ D.P.A)] at e₁
  rw [e₄] at e₂
  rw [e₆, e₁, e₂]
  exact (_root_.mul_assoc _ _ _).symm

theorem conv_famFE : GlobalFnsSt → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (D : DegPre V), D.TauBimult → ∀ (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], FinExt V W → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (φ : TF (R := V) F ⟶ TA V W), Function.Injective φ.left.appTop.hom → ∀ (k l : ℕ) (f : ∀ α, SecBT D (TA V W) k α) (g : ∀ α, SecBT D (TA V W) l α) (h : ∀ α, SecBT D (TA V W) (k + l) α) (s : Raw D F k) (s' : Raw D F l) (s'' : Raw D F (k + l)) (a a' : Multiplicative D.X →* Wˣ), (∀ mu : D.X, a (Multiplicative.ofAdd (k • mu)) * a' (Multiplicative.ofAdd (l • mu)) = 1) → PullB D F φ k f s → PullB D F φ l g s' → PullB D F φ (k + l) h s'' → DegPre.FamFE D F k s → DegPre.FamFE D F l s' → ConvT (IsLocalRing.maximalIdeal V) (GlobalTheory.UU.twist a f) (GlobalTheory.UU.twist a' g) h → DegPre.FamFE D F (k + l) s'' := by
  intro hG V _ _ _ hV D hB W _ _ _ hW F _ _ φ hφ k l f g h s s' s'' a a' ha hf hg hh hs hs' hconv mu α u hu hc
  obtain ⟨u₀, r₁, r₂, hu₀, -, hr₂, hrel⟩ := GlobalTheory.UU.IntGen.main hG V D (TA V W) (k + l) α mu
  obtain ⟨p, hp, hS⟩ := hconv α
  obtain ⟨p', hp', hS'⟩ := hconv (α + (k + l) • mu)
  haveI := hV.1
  haveI := hW.1
  haveI := hW.2.2.2.1
  haveI := noeth V W
  haveI := D.P.isAb.smooth
  haveI := D.P.isAb.geomConnected
  haveI : IsAffine (TA V W).left := inferInstanceAs (IsAffine (Spec _))
  haveI : IsAffine (TF (R := V) F).left := inferInstanceAs (IsAffine (Spec _))
  have hcs : ∀ (z : (DegPre.BF D F).left) (c : V),
      gs (φ ▷ D.P.A).left z ⊤ (scal (TA V W ⊗ D.P.A).hom c) = cst (DegPre.BF D F).hom z c := fun z c => by
    rw [gs_scal, Over.w]
  have hu' : ∀ (z : (DegPre.BF D F).left) (J), Good D.P.L z J →
      cst (DegPre.BF D F).hom z r₂ * (val u (𝟙 _) z J).val =
        cst (DegPre.BF D F).hom z r₁ * (val u₀ (φ ▷ D.P.A).left z J).val := fun z J hJ => by
    have := hrel F φ u hu hc _ (𝟙 _) z J hJ
    rwa [gs_scal, gs_scal, Category.id_comp, Category.id_comp] at this
  have H := relation_of_finite_levels V (IsLocalRing.maximalIdeal V) (TA V W) D.P.A (jac V W) _ _ D.P.L D.P.isLB _ _ _
    _ _ _ _ _ _ (trT D (toUnit _ ≫ D.c mu)).left (h α) (h (α + (k + l) • mu)) u₀ (scal (TA V W ⊗ D.P.A).hom r₁)
    (scal (TA V W ⊗ D.P.A).hom r₂) hu₀ (form_delta _ _ _ _)
    (adicSum_rel V (IsLocalRing.maximalIdeal V) _ _ (trT D (toUnit _ ≫ D.c mu)) _ D.P.L _ _ _ _ _ _ _ _ _ u₀ _ _ _ _
      (Equiv.addRight (k • mu)) p p' _ _ hS hS' fun β =>
      sec_relation_descends _ D.P.A (TA V W) (TF (R := V) F) φ hφ _ _ D.P.L D.P.isLB _ _ _ _ _ _ _ _ _ _ (p β)
        (p' (β + k • mu)) u₀ _ _ hu₀ (form_delta _ _ _ _) fun z J hJ => by
          rw [hcs, hcs, term_rel hG hB hf hg hs hs' a a' mu α β (ha mu) (hp β) (hp' _) u hu hc z hJ, mul_left_comm,
            hu' z J hJ, mul_left_comm])
  refine (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).2 fun z J hJ => ?_
  have e := H _ (φ ▷ D.P.A).left z J hJ
  rw [hcs, hcs, mul_left_comm, ← hu' z J hJ, mul_left_comm, ← Over.comp_left, whisker_trT, Over.comp_left] at e
  rw [pullB_val hh _ _ z hJ, pullB_val hh _ _ z hJ, Category.id_comp, Category.id_comp]
  exact (cst_unit hr₂ z).mul_left_cancel e

end GlobalTheory.ConvFE
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLaw


set_option backward.isDefEq.respectTransparency false in
theorem acyclic_extendScalars_of_flat {R S : Type} [CommRing R] [CommRing S] (g : R →+* S)
    (C : CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) (hn : ∀ p, n < p → IsZero (C.X p))
    (hflat : ∀ p, Module.Flat R (C.X p)) (hC : C.Acyclic) :
    (((ModuleCat.extendScalars.{0, 0, 0} g).mapHomologicalComplex _).obj C).Acyclic := by
  have : QuasiIso (0 : C ⟶ C) := ⟨fun p => (quasiIsoAt_iff_exactAt _ p (hC p)).2 (hC p)⟩
  have h := GlobalTheory.quasiIso_extendScalars_of_flat (0 : C ⟶ C) hflat hflat n hn hn g
  rw [Functor.map_zero] at h
  intro p
  have h' := (quasiIsoAt_iff_isIso_homologyMap _ p).1 (h.1 p)
  rw [HomologicalComplex.homologyMap_zero] at h'
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (isIsoZero_iff_source_target_isZero _ _).1 h' |>.1

theorem subsingleton_of_forall_isMaximal_smul_eq_zero {R M : Type} [CommRing R] [AddCommGroup M]
    [Module R M] (h : ∀ P : Ideal R, P.IsMaximal → ∃ r, r ∉ P ∧ ∀ z : M, r • z = 0) :
    Subsingleton M := by
  rw [← Module.annihilator_eq_top_iff (R := R)]
  by_contra hne
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨r, hr, hz⟩ := h P hP
  exact hr (hle (Module.mem_annihilator.2 hz))

theorem cechLB_acyclic_iff_fibres : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)), Flat f → IsProjBy f → ∀ F : LB Y, F.IsLB → ((∀ P : Ideal R, P.IsMaximal → ∃ (K : Type) (_ : Field K) (χ : R →+* K), RingHom.ker χ = P ∧ ∀ (Y₀ : Scheme.{0}) (π : Y₀ ⟶ Y) (f₀ : Y₀ ⟶ Spec (CommRingCat.of K)), IsPullback π f₀ f (Spec.map (CommRingCat.ofHom χ)) → (∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (Y₀).Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB (f₀) (F.pull π) D).Acyclic)) → (∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (Y).Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB (f) (F) D).Acyclic)) ∧ ((∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (Y).Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB (f) (F) D).Acyclic) → ∀ (K : Type) [Field K] (χ : R →+* K), ∀ (Y₀ : Scheme.{0}) (π : Y₀ ⟶ Y) (f₀ : Y₀ ⟶ Spec (CommRingCat.of K)), IsPullback π f₀ f (Spec.map (CommRingCat.ofHom χ)) → (∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (Y₀).Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB (f₀) (F.pull π) D).Acyclic)) := by
  intro R _ _ Y f hf hproj F hF
  have := isProper_of_isProjBy R Y f hproj
  have : Y.IsSeparated := by
    rw [Scheme.isSeparated_iff, ← terminal.comp_from f]
    infer_instance
  have hI : ∀ {κ : Type} {D : κ → Y.Opens}, (∀ i, IsAffineOpen (D i)) → ∀ s : Finset κ,
      s.Nonempty → IsAffineOpen (⨅ i ∈ s, D i) := fun hD s hs =>
    IsAffineOpen.biInf _ (Finset.finite_toSet _) (by exact_mod_cast hs) fun i _ => hD i
  refine ⟨fun H κ _ _ D hD hc p => ?_, fun H K _ χ Y₀ π f₀ h κ _ _ D hD hc p => ?_⟩
  · rw [HomologicalComplex.exactAt_iff_isZero_homology, ModuleCat.isZero_iff_subsingleton]
    refine subsingleton_of_forall_isMaximal_smul_eq_zero (R := R) fun P hP => ?_
    obtain ⟨K, _, χ, rfl, HK⟩ := H P hP
    have h' := IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom χ))
    have hac := HK _ _ _ h' κ
      (fun i => pullback.fst f (Spec.map (CommRingCat.ofHom χ)) ⁻¹ᵁ D i)
      (fun i => isAffineOpen_preimage_of_isPullback h' (hD i))
      (by rw [← Scheme.Hom.preimage_iSup, hc]; rfl)
    exact GlobalTheory.exists_smul_homology_eq_zero_of_acyclic_fibre R K χ _ (Fintype.card κ)
      (fun p hp => isZero_cechLB_X _ _ _ hp.le) (flat_cechLB_X f hF (hI hD))
      (cechLB_homology_finite_of_affine_cover R Y f F κ D hF inferInstance hproj hD hc)
      (fun q => (hac q).of_iso (cechLBBaseChangeIso hF h' (hI hD)).symm) p
  · obtain ⟨L, -, m, s, hc', hs⟩ := hproj
    have hD' : ∀ i, IsAffineOpen (nonzeroLocus (s i)) := fun i => (hs i).1
    have hac := acyclic_extendScalars_of_flat χ _ (Fintype.card (Fin (m + 1)))
      (fun p hp => isZero_cechLB_X _ _ _ hp.le) (flat_cechLB_X f hF (hI hD')) (H _ _ hD' hc')
    have h₁ := (hac p).of_iso (cechLBBaseChangeIso hF h (hI hD'))
    have : IsSeparated f₀ := MorphismProperty.of_isPullback (P := @IsSeparated) h inferInstance
    obtain ⟨e⟩ := cechLB_homology_equiv_of_affine_covers K Y₀ f₀ (F.pull π) κ D _
      (fun i => π ⁻¹ᵁ nonzeroLocus (s i)) (LB.isLB_pull hF π) inferInstance hD hc
      (fun i => isAffineOpen_preimage_of_isPullback h (hD' i))
      (by rw [← Scheme.Hom.preimage_iSup, hc']; rfl) p
    rw [HomologicalComplex.exactAt_iff_isZero_homology, ModuleCat.isZero_iff_subsingleton] at h₁ ⊢
    exact e.subsingleton

end GlobalTheory.AbLaw
end
