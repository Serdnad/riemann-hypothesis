module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle003
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.BoxProductLinearIndependent
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle044
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalEqZeroOfWeightSum
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle067
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle035
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle076
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle004
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle078
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle070
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle080
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle071
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing

@[expose] public section

open AlgebraicGeometry CategoryTheory
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable local instance (priority := high) grpObjUniformizationPullback086
    {S T : Scheme.{0}} (f : T ⟶ S) (G : Over S) [GrpObj G] : GrpObj ((Over.pullback f).obj G) :=
  letI : (Over.pullback f).Monoidal := (Over.instBraidedPullback (f := f)).toMonoidal
  Functor.grpObjObj (F := Over.pullback f)

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU.ExpFUniq

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.BoxIndep GlobalTheory.ExpansionSingleValued

theorem split_iff {R F : Type} [CommRing R] [CommRing F] [Algebra R F] {X X₀ : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of R)) [Flat p] {L : LB X₀} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (X ⟶ X₀)}
    {ε : K → ℤ} {Λ κ : Type} [Fintype Λ] [Fintype κ] (b : κ → F) (hb : LinearIndependent R b) (a : Λ → κ → R)
    (σ : Λ → LB.Sec (LB.LinComb L φ ε)) (τ : κ → LB.Sec (LB.LinComb L φ ε)) (τ₀ : LB.Sec (LB.LinComb L φ ε))
    (hτ : ∀ l (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (J), Good L z J → sval (τ l) r z J =
      ∑ i, gs (r ≫ p) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (a i l)) * sval (σ i) r z J)
    (h₀ : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (J), Good L z J → sval τ₀ r z J = 0) :
    (∀ l, τ l = τ₀) ↔ ∀ (Z : Scheme.{0}) (q : Z ⟶ Spec (CommRingCat.of F)) (r : Z ⟶ X),
      r ≫ p = q ≫ Spec.map (CommRingCat.ofHom (algebraMap R F)) → ∀ (z : Z) (J), Good L z J →
        ∑ i, germOf q z (∑ l, a i l • b l) * sval (σ i) r z J = 0 := by
  replace hτ : ∀ l (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (J), Good L z J → sval (τ l) r z J =
      ∑ i, germOf (r ≫ p) z (a i l) * sval (σ i) r z J := fun l Z r z J hJ =>
    (hτ l Z r z J hJ).trans (Finset.sum_congr rfl fun i _ => congrArg (· * _) (germOf_apply _ _ _).symm)
  constructor
  · intro h Z q r e z J hJ

    simp only [map_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun l _ => ?_
    have h₁ := (hτ l Z r z J hJ).symm.trans ((congrArg (fun s => sval s r z J) (h l)).trans (h₀ Z r z J hJ))
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) ((Finset.mul_sum _ _ (germOf q z (b l))).symm.trans
      ((congrArg _ h₁).trans (mul_zero _)))
    rw [Algebra.smul_def, map_mul, e, germOf_map, mul_comm (germOf q z _), _root_.mul_assoc]
    rfl
  · intro H l
    refine SecOps.sec_ext (sec_ext_val hL fun y J hJ => ?_)
    rw [h₀ _ _ y J hJ, hτ l _ _ y J hJ, Category.id_comp]
    refine split_relation p y (hJ.mem φ (𝟙 X)) b hb a (fun i => (σ i).f fun k => J (𝟙 X ≫ φ k))
      (fun Z q r e z hz => ?_) l
    obtain ⟨J', hJ'⟩ := exists_good_pt hL z
    have h₁ := congrArg ((trF φ ε r z (fun k => J (𝟙 X ≫ φ k)) (fun k => J' (r ≫ φ k))).val * ·) (H Z q r e z J' hJ')
    simp only [mul_zero, Finset.mul_sum] at h₁
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h₁
    rw [mul_left_comm]
    exact congrArg _ (sec_trans (σ i) r z hz (hJ'.mem φ r))

theorem expT_unit_iff : AllPre fun {_} _ _ _ {_} {_} {_} _ _ U => ∀ k σ σ' f f',
    U.ExpT (𝟙_ _) k σ f → U.ExpT (𝟙_ _) k σ' f' → (σ = σ' ↔ f = f') := by
  intro V _ _ _ hV D A G _ _ U
  have key : ∀ T, TA V V = T → ∀ k σ σ' f f', U.ExpT T k σ f → U.ExpT T k σ' f' → (σ = σ' ↔ f = f') := by
    rintro _ rfl
    refine GlobalTheory.expT_eq_iff V hV D A G U V ⟨inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
    rw [Algebra.algebraMap_self, Ideal.map_id]
    exact hV.2.1
  exact key _ (congrArg Over.mk (Spec.map_id _))



theorem main : (AllPre fun {V} _ _ _ {_} {_} {_} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ) t t' s s', U.ExpF F k t s → U.ExpF F k t' s' → (t = t' ↔ s = s')) := by
  intro V _ _ _ hV D A G _ _ U F _ _ k t t' s s' ⟨n, c, σ, f, hE, hG, hB⟩ ⟨n', c', σ', f', hE', hG', hB'⟩
  classical
  let : Algebra V F := ((algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))).toAlgebra
  have : IsScalarTower V (FractionRing V) F := IsScalarTower.of_algebraMap_eq' rfl
  have hj : jFK (R := V) F ≫ jK V = Spec.map (CommRingCat.ofHom (algebraMap V F)) :=
    (Spec.map_comp _ _).symm
  obtain ⟨κ, _, b, a, hb, ha⟩ := exists_indep_coords V F (Fin.append c (-c'))
  have hEE : ∀ i, U.ExpT (𝟙_ _) k (Fin.append σ σ' i) (Fin.append f f' i) := fun i => by
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa only [Fin.append_left] using hE i
    · simpa only [Fin.append_right] using hE' i
  choose τ g hτg hτ hg using fun l => ExpLin.expT_linear V _ D A G U (𝟙_ _) k _
    (fun i => (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom (a i l)) _ _ hEE
  obtain ⟨τ₀, g₀, h₀, hτ₀, hg₀⟩ := ExpLin.expT_linear V _ D A G U (𝟙_ _) k 0 Fin.elim0 Fin.elim0 Fin.elim0
    (fun i => i.elim0)
  simp only [Finset.univ_eq_empty, Finset.sum_empty] at hτ₀ hg₀
  have := U.semi.smooth
  have := D.P.isAb.smooth
  let pG : (𝟙_ _ ⊗ G).left ⟶ Spec (CommRingCat.of V) := (fst (𝟙_ _) G).left
  let pB : (𝟙_ _ ⊗ D.P.A).left ⟶ Spec (CommRingCat.of V) := (fst (𝟙_ _) D.P.A).left
  have : Flat pG := inferInstanceAs (Flat (pullback.fst _ G.hom))
  have : Flat pB := inferInstanceAs (Flat (pullback.fst _ D.P.A.hom))
  have eG : (snd (𝟙_ _) G).left ≫ G.hom = pG :=
    (Over.w (snd (𝟙_ _) G)).trans ((Over.w (fst (𝟙_ _) G)).symm.trans (Category.comp_id _))
  have eB : (snd (𝟙_ _) D.P.A).left ≫ D.P.A.hom = pB :=
    (Over.w (snd (𝟙_ _) D.P.A)).trans ((Over.w (fst (𝟙_ _) D.P.A)).symm.trans (Category.comp_id _))
  have SG := split_iff pG U.P.L.isLB b hb a (Fin.append σ σ') τ τ₀ hτ hτ₀
  have SB := fun α => split_iff pB D.P.isLB b hb a (fun i => Fin.append f f' i α) (fun l => g l α) (g₀ α)
    (fun l => hg l α) (hg₀ α)
  simp only [← ha] at SG SB
  simp only [gs_scal] at hG hG' hB hB'
  have M : (∀ l, τ l = τ₀) ↔ ∀ α l, g l α = g₀ α := by
    rw [forall_comm]
    exact forall_congr' fun l => (expT_unit_iff V hV D A G U k _ _ _ _ (hτg l) h₀).trans funext_iff
  have NG : t = t' ↔ ∀ l, τ l = τ₀ := by
    rw [SG]
    constructor
    · rintro rfl Z q r e z J hJ
      let y : Z ⟶ pullback G.hom (jK V) := pullback.lift (r ≫ (snd (𝟙_ _) G).left) (q ≫ jFK (R := V) F)
        (by rw [Category.assoc, eG, e, Category.assoc, hj])
      let rA : Z ⟶ (TFK (R := V) F ⊗ A.A).left := pullback.lift q (y ≫ U.gen.hom.left)
        ((pullback.lift_snd _ _ _).symm.trans ((congrArg (y ≫ ·) (Over.w U.gen.hom).symm).trans
          (Category.assoc _ _ _).symm))
      have e₁ : rA ≫ (fst (TFK (R := V) F) A.A).left = q := pullback.lift_fst _ _ _
      obtain ⟨JA, hJA⟩ := exists_good_pt A.isLB z
      have h₁ := hG Z rA y r (pullback.lift_snd _ _ _) (pullback.lift_fst _ _ _).symm z JA J hJA hJ
      have h₂ := hG' Z rA y r (pullback.lift_snd _ _ _) (pullback.lift_fst _ _ _).symm z JA J hJA hJ
      refine (sum_append (germOf q z) c c' σ σ' (fun t => sval t r z J)).trans (sub_eq_zero.2 ?_)
      rw [← e₁]
      exact h₁.symm.trans h₂
    · intro H
      refine SecOps.sec_ext (sec_ext_val (φ := fun _ : Fin 1 => (snd (TFK (R := V) F) A.A).left)
        (ε := fun _ => (k : ℤ)) A.isLB fun z JA hJA => ?_)
      let y : (TFK (R := V) F ⊗ A.A).left ⟶ pullback G.hom (jK V) := (snd (TFK (R := V) F) A.A).left ≫ U.gen.inv.left
      let r : (TFK (R := V) F ⊗ A.A).left ⟶ (𝟙_ _ ⊗ G).left :=
        pullback.lift ((y ≫ pullback.fst G.hom (jK V)) ≫ G.hom) (y ≫ pullback.fst G.hom (jK V)) (Category.comp_id _)
      have e₁ : r ≫ (snd (𝟙_ _) G).left = y ≫ pullback.fst G.hom (jK V) := pullback.lift_snd _ _ _
      have e₂ : 𝟙 _ ≫ (snd (TFK (R := V) F) A.A).left = y ≫ U.gen.hom.left :=
        (Category.id_comp _).trans ((Category.comp_id _).symm.trans ((congrArg (_ ≫ ·)
          (congrArg CommaMorphism.left U.gen.inv_hom_id).symm).trans (Category.assoc _ _ _).symm))
      obtain ⟨J, hJ⟩ := exists_good_pt U.P.L.isLB z
      have h₁ := hG _ (𝟙 _) y r e₂ e₁ z JA J hJA hJ
      have h₂ := hG' _ (𝟙 _) y r e₂ e₁ z JA J hJA hJ
      have e₃ : y ≫ pullback.snd G.hom (jK V) = (𝟙 _ ≫ (fst (TFK (R := V) F) A.A).left) ≫ jFK (R := V) F :=
        (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Over.w U.gen.inv)).trans
          ((Over.w (snd (TFK (R := V) F) A.A)).trans ((Over.w (fst (TFK (R := V) F) A.A)).symm.trans
            (congrArg (· ≫ _) (Category.id_comp _).symm))))
      have h₃ := H _ (𝟙 _ ≫ (fst (TFK (R := V) F) A.A).left) r (by
        rw [← eG, ← Category.assoc, e₁, Category.assoc, pullback.condition, ← Category.assoc, e₃, ← hj]
        exact Category.assoc _ _ _) z J hJ
      have h₄ := sub_eq_zero.1 ((sum_append (germOf (B := CommRingCat.of F) (𝟙 _ ≫ (fst (TFK (R := V) F) A.A).left) z)
        c c' σ σ' (fun t => sval t r z J)).symm.trans h₃)
      exact (IsUnit.mul_right_inj ((Units.isUnit _).pow k)).1 (h₁.trans (h₄.trans h₂.symm))
  have NB : s = s' ↔ ∀ α l, g l α = g₀ α := by
    rw [funext_iff]
    refine forall_congr' fun α => ?_
    rw [SB α]
    constructor
    · intro h Z q r e z J hJ
      let rF : Z ⟶ (DegPre.BF D F).left := pullback.lift q (r ≫ (snd (𝟙_ _) D.P.A).left)
        (by rw [Category.assoc, eB, e, ← hj]; rfl)
      have e₁ : rF ≫ (fst (TF (R := V) F) D.P.A).left = q := pullback.lift_fst _ _ _
      have h₁ := hB α Z rF r (pullback.lift_snd _ _ _).symm z J hJ
      have h₂ := hB' α Z rF r (pullback.lift_snd _ _ _).symm z J hJ
      refine (sum_append (germOf q z) c c' f f' (fun t => sval (t α) r z J)).trans (sub_eq_zero.2 ?_)
      rw [← e₁]
      exact h₁.symm.trans ((congrArg (fun u => sval u rF z J) h).trans h₂)
    · intro H
      refine SecOps.sec_ext (sec_ext_val D.P.isLB fun z J hJ => ?_)
      let r : (DegPre.BF D F).left ⟶ (𝟙_ _ ⊗ D.P.A).left :=
        pullback.lift ((DegPre.prB D F).left ≫ D.P.A.hom) (DegPre.prB D F).left (Category.comp_id _)
      have e₁ : r ≫ (snd (𝟙_ _) D.P.A).left = 𝟙 _ ≫ (DegPre.prB D F).left :=
        (pullback.lift_snd _ _ _).trans (Category.id_comp _).symm
      have h₃ := H _ (𝟙 _ ≫ (fst (TF (R := V) F) D.P.A).left) r (by
        rw [← eB, ← Category.assoc, e₁, Category.assoc, Category.assoc, Over.w, ← hj]
        exact congrArg _ (Over.w (fst (TF (R := V) F) D.P.A)).symm) z J hJ
      have h₄ := sub_eq_zero.1 ((sum_append (germOf (B := CommRingCat.of F) (𝟙 _ ≫ (fst (TF (R := V) F) D.P.A).left) z)
        c c' f f' (fun t => sval (t α) r z J)).symm.trans h₃)
      exact (hB α _ (𝟙 _) r e₁ z J hJ).trans (h₄.trans (hB' α _ (𝟙 _) r e₁ z J hJ).symm)
  exact NG.trans (M.trans NB.symm)

end GlobalTheory.UU.ExpFUniq
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.UU.RedAdd

open GlobalTheory.FormalPoint GlobalTheory.TorusCoord ReciprocityTheory.ChartRestriction.G.DVR

section Level

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : PreU I D A G)
  {T : Over (Spec (CommRingCat.of R))}

theorem red_iff_over (x : T ⟶ G) (g : GtPt D T) :
    U.Red x g ↔ ∀ (e : ℕ) (Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
      (r : (Over.map (thick R I e)).obj Z ⟶ T) (a : Z ⟶ thickObj R I e G),
      (Over.map (thick R I e)).map a ≫ fstG I e G = r ≫ x → im (U.gt e) a = r ≫ g.b ∧
        ∀ χ z J, Good D.P.L z J →
          val ((U.gt e).t χ) ((Over.map (thick R I e)).map a).left z J = val (g.s χ) r.left z J := by
  constructor
  · intro h e Z r a ha
    obtain ⟨h₁, h₂⟩ := h e _ r.left ((Over.map (thick R I e)).map a).left (congrArg (fun q => q.left) ha)
    exact ⟨Over.OverMorphism.ext h₁, h₂⟩
  · intro h e Z r y hy
    have w : r ≫ T.hom = (y ≫ (thickObj R I e G).hom) ≫ thick R I e := by
      rw [← Over.w x, ← Category.assoc, ← hy, Category.assoc, Over.w (fstG I e G), Category.assoc]; rfl
    obtain ⟨h₁, h₂⟩ := h e (Over.mk (y ≫ (thickObj R I e G).hom)) (Over.homMk r w) (Over.homMk y rfl)
      (Over.OverMorphism.ext hy)
    exact ⟨congrArg (fun q => q.left) h₁, h₂⟩

theorem map_one_fstG {e : ℕ} {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} :
    (Over.map (thick R I e)).map (1 : Z ⟶ thickObj R I e G) ≫ fstG I e G = 1 := by
  have := map_mul_fstG (1 : Z ⟶ thickObj R I e G) 1
  rw [_root_.mul_one] at this
  exact mul_eq_left.1 this.symm

theorem red_one {g : GtPt D T} (h : g.IsZero) : U.Red 1 g := by
  rw [red_iff_over]
  intro e Z r a ha
  obtain rfl : a = 1 := eq_of_map_fstG (by rw [ha, map_one_fstG, MonObj.comp_one])
  refine ⟨by rw [im_one, h.1]; exact (MonObj.comp_one r).symm, fun χ z J hJ => ?_⟩
  have t₁ := val_unit (U.gt e) χ (Z := Z) (z := z) hJ
  exact t₁.trans ((val_corr hJ (h.2 χ) r.left).trans (val_one _)).symm


variable {U} in
theorem red_mul (hG : GlobalFnsSt) {g g' g'' : GtPt D T} {x x' : T ⟶ G} (hx : U.Red x g)
    (hx' : U.Red x' g') (h : g.IsAdd g' g'') : U.Red (x * x') g'' := by
  rw [red_iff_over] at hx hx' ⊢
  intro e Z r y hy
  obtain ⟨a, ha⟩ := exists_lift_fstG (r ≫ x)
  obtain ⟨b, hb⟩ := exists_lift_fstG (r ≫ x')
  obtain rfl : y = a * b := eq_of_map_fstG (by rw [hy, map_mul_fstG, ha, hb, MonObj.comp_mul])
  obtain ⟨a₁, a₂⟩ := hx e Z r a ha
  obtain ⟨b₁, b₂⟩ := hx' e Z r b hb
  refine ⟨by rw [im_mul, a₁, b₁, h.1]; exact (MonObj.comp_mul _ _ _).symm, fun χ z J hJ => ?_⟩
  have e₁ : val ((U.gt e).t χ) ((Over.map (thick R I e)).map (a * b)).left z J *
      th D z J (cP D _ χ) (im (U.gt e) a) (im (U.gt e) b) =
      val ((U.gt e).t χ) ((Over.map (thick R I e)).map a).left z J *
        val ((U.gt e).t χ) ((Over.map (thick R I e)).map b).left z J :=
    val_t_mul_points (U.gt e) hG χ a b z J hJ
  have e₂ : val (g''.s χ) r.left z J * th D z J (r ≫ cP D T χ) (r ≫ g.b) (r ≫ g'.b) =
      val (g.s χ) r.left z J * val (g'.s χ) r.left z J :=
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cub D.cub r hJ _ _ _))).symm.trans
      ((val_corr hJ (h.2 χ) r.left).trans (val_mul hJ _ _ _))
  rw [a₁, b₁, a₂ χ z J hJ, b₂ χ z J hJ] at e₁
  rw [comp_cP] at e₂
  exact mul_right_cancel (e₁.trans e₂.symm)

end Level

section Complete

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {S : Type} [CommRing S] {φ : R →+* S} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {U : PreU I D A G}


variable (I φ) in
abbrev lev (e : ℕ) : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (levelMap I φ e)


variable (I φ) in
def levι (e : ℕ) : (Over.map (thick R I e)).obj (lev I φ e) ⟶ Over.mk (spMap φ) :=
  Over.homMk (thick S (I.map φ) e) (levelMap_thick I φ e).symm

variable [IsLocalRing S] [IsHausdorff (I.map φ) S]


omit [IsDomain R] in
theorem pt_ext {B : Over (Spec (CommRingCat.of R))} {b b' : Over.mk (spMap φ) ⟶ B}
    (h : ∀ e, levι I φ e ≫ b = levι I φ e ≫ b') : b = b' :=
  Over.OverMorphism.ext (hom_ext_of_isHausdorff (I.map φ) fun e => congrArg (·.left) (h e))

variable [IsNoetherianRing S]

theorem isAdd_of_red (hG : GlobalFnsSt) {x x' : Over.mk (spMap φ) ⟶ G} {g g' g'' : GtPt D (Over.mk (spMap φ))}
    (h : U.Red x g) (h' : U.Red x' g') (h'' : U.Red (x * x') g'') : GtPt.IsAdd g g' g'' := by
  rw [red_iff_over] at h h' h''
  choose a ha using fun e => exists_lift_fstG (levι I φ e ≫ x)
  choose a' ha' using fun e => exists_lift_fstG (levι I φ e ≫ x')
  have k := fun e => h e _ _ _ (ha e)
  have k' := fun e => h' e _ _ _ (ha' e)
  have k'' := fun e => h'' e _ (levι I φ e) (a e * a' e) (by rw [map_mul_fstG, ha, ha', MonObj.comp_mul])
  have hb : g''.b = g.b * g'.b := pt_ext (I := I) fun e => by
    rw [MonObj.comp_mul, ← (k e).1, ← (k' e).1, ← (k'' e).1, im_mul]
  refine ⟨hb, fun χ => CoordAdd.corr_of_thick (ne_top_of_isHausdorff (I.map φ)) D.P.isLB (fun U _ h => ?_)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (g''.isGen χ) (DVR.pullGen_isGen _ _ _ _ D.cub.isGen _))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (g.isGen χ) (g'.isGen χ)) fun e z J hJ => ?_⟩
  · refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_sum_type _).symm)
    refine (congrArg₂ (· * ·) (CoordAdd.prod_gtφT g''.b χ h) (prod_cub (DegPre.cT D _ χ) g.b g'.b h)).trans
      (Eq.trans ?_ (congrArg₂ (· * ·) (CoordAdd.prod_gtφT g.b χ h) (CoordAdd.prod_gtφT g'.b χ h)).symm)
    rw [hb, _root_.mul_assoc (DegPre.cT D _ χ)]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · have e₁ : val ((U.gt e).t χ) ((Over.map (thick R I e)).map (a e * a' e)).left z J *
        th D (T := (Over.map (thick R I e)).obj (lev I φ e)) z J (cP D _ χ) (im (U.gt e) (a e)) (im (U.gt e) (a' e)) =
        val ((U.gt e).t χ) ((Over.map (thick R I e)).map (a e)).left z J *
          val ((U.gt e).t χ) ((Over.map (thick R I e)).map (a' e)).left z J :=
      val_t_mul_points (U.gt e) hG χ (a e) (a' e) z J hJ
    rw [(k e).1, (k' e).1, (k e).2 χ z J hJ, (k' e).2 χ z J hJ, (k'' e).2 χ z J hJ,
      ← comp_cP D (levι I φ e)] at e₁
    exact ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cub D.cub (levι I φ e) hJ _ _ _))).trans
      (e₁.trans (val_mul hJ _ _ _).symm)

theorem isZero_of_red {g : GtPt D (Over.mk (spMap φ))} (h : U.Red 1 g) : g.IsZero := by
  rw [red_iff_over] at h
  have k := fun e => h e _ (levι I φ e) 1 (by rw [map_one_fstG, MonObj.comp_one])
  have hb : g.b = 1 := pt_ext (I := I) fun e => by rw [MonObj.comp_one, ← (k e).1, im_one]
  refine ⟨hb, fun χ => CoordAdd.corr_of_thick (ne_top_of_isHausdorff (I.map φ)) D.P.isLB (fun U _ h => ?_)
    (g.isGen χ) (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans
      (_root_.mul_one _)).symm) fun e z J hJ => ?_⟩
  · refine (CoordAdd.prod_gtφT g.b χ h).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
    rw [hb, _root_.mul_one, inv_mul_cancel, _root_.one_mul, mul_inv_cancel]
  · exact ((k e).2 χ z J hJ).symm.trans
      ((val_unit (U.gt e) χ (Z := lev I φ e) (z := z) hJ).trans (val_one _).symm)

end Complete

theorem main : GlobalFnsSt → (AllPre fun {V} _ _ _ {D} {_} {G} _ _ U => ∀ (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], FinExt V W → ∀ (x x' x'' : TA V W ⟶ G) (g g' g'' : GtPt D (TA V W)), U.Red x g → U.Red x' g' → U.Red x'' g'' → (x'' = x * x' ↔ GtPt.IsAdd g g' g'') ∧ (x = 1 ↔ g.IsZero)) := by
  intro hG V _ _ _ hV D A G _ _ U W _ _ _ hW x x' x'' g g' g'' h h' h''
  have := hV.1
  have := hW.1
  have := hW.2.2.2.2
  have : IsNoetherianRing W := IsNoetherianRing.of_finite V W
  refine ⟨⟨fun e => ?_, fun e => ?_⟩, ⟨fun e => ?_, fun e => ?_⟩⟩
  · exact isAdd_of_red (φ := algebraMap V W) hG h h' (e ▸ h'')
  · exact RedOnto.red_unique (φ := algebraMap V W) h'' (red_mul hG h h' e)
  · exact isZero_of_red (φ := algebraMap V W) (e ▸ h)
  · exact RedOnto.red_unique (φ := algebraMap V W) h (red_one U e)

end GlobalTheory.UU.RedAdd

end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory

theorem psi_tendsto_zero : (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → (∃ j, (f 0).f j ≠ 0) → PsiRel D (𝟙_ _) f → ∀ n : ℕ, {χ : D.X | ¬ D.PsiIn χ (IsLocalRing.maximalIdeal V ^ n)}.Finite) := by
  intro V _ _ _ hV D A G _ _ U θ f hθ h0 hR n
  haveI := hV.1
  obtain ⟨ga, a, hS⟩ := exists_psiScal V D
  obtain ⟨m, hm⟩ := exists_order_translates V hV D 1 (f 0) h0
  obtain ⟨s, hs⟩ := LevelVanishing.main V hV D A G U 1 θ f hθ.1 (m + n)
  refine s.finite_toSet.subset fun χ hχ => ?_
  by_contra hn
  apply hχ
  have hne : IsLocalRing.maximalIdeal V ^ n ≠ ⊥ := pow_ne_zero n (IsDiscreteValuationRing.not_a_field V)
  refine (psiIn_iff_scalar_mem V D ga a hS χ _ hne).2 ?_
  obtain ⟨⟨p, q⟩, hpq⟩ := IsLocalization.surj (nonZeroDivisors V) (a χ).val
  obtain ⟨z, J, hJ, hz⟩ := hm χ
  have hq : (q : V) ≠ 0 := nonZeroDivisors.coe_ne_zero q
  have e := PsiInt.psiRel_integral V D ga a f hS hR χ p q (by rw [mul_comm]; exact hpq) (𝟙_ _ ⊗ D.P.A) (snd _ _) z J hJ
  have e₁ : lift (toUnit (𝟙_ _ ⊗ D.P.A)) (snd (𝟙_ _) D.P.A) = 𝟙 _ := by
    ext1
    · exact toUnit_unique _ _
    · simp
  have e₂ : toUnit (𝟙_ _ ⊗ D.P.A) = fst (𝟙_ _) D.P.A := toUnit_unique _ _
  haveI : Flat D.P.A.hom := by
    haveI := D.P.isAb.smooth
    infer_instance
  haveI : Flat (𝟙_ _ ⊗ D.P.A).hom := by
    have h : (𝟙_ _ ⊗ D.P.A).hom = (λ_ D.P.A).hom.left ≫ D.P.A.hom := (Over.w _).symm
    haveI : IsIso (λ_ D.P.A).hom.left := inferInstanceAs (IsIso ((Over.forget _).map (λ_ D.P.A).hom))
    rw [h]
    infer_instance
  let io := (((𝟙_ _ ⊗ D.P.A).left.presheaf.germ ⊤ z trivial).hom.comp (((𝟙_ _ ⊗ D.P.A).hom.appTop.hom).comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom))
  have hio : ∀ v : V, gs (𝟙 _) z ⊤ (scal (𝟙_ _ ⊗ D.P.A).hom v) = io v := fun v => gs_eq _ _ ⊤ trivial _
  have hio' : ∀ v : V, cst (𝟙_ _ ⊗ D.P.A).hom z v = io v := fun v => gs_eq _ _ ⊤ trivial _
  rw [hio, hio, e₁] at e
  have hf := hs χ hn z J hJ
  have hf' := Ideal.map_mono (f := io) (Ideal.pow_le_pow_right (Nat.le_succ (m + n))) hf
  obtain ⟨r, hr, hp⟩ := exists_mem_pow_of_ratio_of_torsionFree V _ io
    (fun v hv x hx => by
      have := cst_regular (𝟙_ _ ⊗ D.P.A).hom z hv
      rw [hio'] at this
      exact this (hx.trans (mul_zero _).symm))
    _ _ p q m n hq e hf' (fun h => hz (by
      rw [← e₂]
      exact (Ideal.unit_mul_mem_iff_mem _ (Units.isUnit _)).1 h))
  refine ⟨r, hr, ?_⟩
  have hq' : algebraMap V (FractionRing V) q ≠ 0 := (IsLocalization.map_units _ q).ne_zero
  apply mul_right_cancel₀ hq'
  rw [← map_mul, ← hp]
  exact hpq.symm

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.mumfordTower_repWt_mul_add : AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg) (χ χ' : s.X) (c c' : 𝟙_ _ ⟶ a.B) (e : ℕ), a.RepWt c χ e → a.RepWt c' χ' e → a.RepWt (c * c') (χ + χ') e := by
  first | exact @GlobalTheory.UU.repWt_add | exact GlobalTheory.UU.repWt_add | (intros; apply GlobalTheory.UU.repWt_add <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory

theorem expF_of_pull : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (I : Ideal R) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (σ : U.SecGT (𝟙_ _) k) (f : ∀ α, SecBT D (𝟙_ _) k α) (t : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F))) (s : Raw D F k), U.ExpT (𝟙_ _) k σ f → U.PullG F (toUnit _) k σ t → PullB D F (toUnit _) k f s → U.ExpF F k t s :=
  fun R _ _ D I A G _ _ U F _ _ k σ f t s hE hG hB =>
    GlobalTheory.UU.IntExp.expF_of_expT R I D A G U F k σ f t s hE hG hB

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.abelianPart_image_eq_one_iff_torus_point : AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg) (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], IsAdicComplete ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) W → IsLocalHom (algebraMap V W) → ∀ x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x).left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ ((1 : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ a.B)).left) ↔ ∃ c : Multiplicative s.X →* Wˣ, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (τ : Z ⟶ (splitTorus _ s.X).left), τ ≫ (splitTorus (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1)))) s.X).hom ≫ thick V _ e = r ≫ (Spec.map (CommRingCat.ofHom (algebraMap V W))) → (∀ χ, τ.appTop.hom (charUnit _ s.X χ).val = scal r (c (Multiplicative.ofAdd χ)).val) → τ ≫ (t.l e).Q.i.left ≫ (fstG _ e G).left = r ≫ (x).left) := by
  first | exact @GlobalTheory.UU.image_eq_one_iff_torus_point | exact GlobalTheory.UU.image_eq_one_iff_torus_point | (intros; apply GlobalTheory.UU.image_eq_one_iff_torus_point <;> assumption)
end
