module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle022
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle023
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle096
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsCommVOfLe
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle026
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2749
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2668
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyFamOne
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.BrData
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2734
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2698
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2173
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2735
public import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.NefLineBundleNumericalTheoremsProof
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle003
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1409
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle017

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

noncomputable section

namespace GlobalTheory.TwFam

theorem exists_iota_of_rosati {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (a a' : D.P.A ⟶ D.P.A)
    [IsMonHom a] [IsMonHom a'] (hr : RosatiAdj D.P.A D.P.L a a') (α δ : D.X) (hc : D.c δ = D.c α ≫ a') :
    ∃ u : LB.Gen (IotaLB D a α δ), IsIota u := by
  have hG := GlobalTheory.globalFns_holds
  obtain ⟨u, hu, u₀⟩ := exists_ros hG D.P.isAb D.P.isLB a a' hr
  have cf : ∀ T, DVR.cP D T δ = DVR.cP D T α ≫ a' := fun T => by
    rw [DVR.cP, hc, ← Category.assoc]; rfl
  obtain ⟨v, hv, vv⟩ := exists_gen D.P.isLB
    (φ' := Sum.elim (D.Oφ (𝟙 _) δ) (D.Oφ a α)) (ε' := Sum.elim Oε Oinvε)
    (fun U _ h => by
      refine (DVR.prod_neg _ _ (prod_ros a a' (𝟙 D.P.A) (DVR.cP D _ α) h)).trans (Eq.symm ?_)
      refine (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ (GlobalTheory.UT.OLinEnd.prod_Oφ D (𝟙 _) δ h)
        (GlobalTheory.UT.OLinEnd.prod_Oφ_inv D a α h)).trans ?_
      rw [cf, Category.id_comp, _root_.mul_comm (DVR.cP D _ α) a, _root_.mul_comm (DVR.cP D _ α ≫ a') (𝟙 _)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    (LB.invGen D.P.L _ _ (LB.pullGen D.P.L _ _ u (lift (𝟙 D.P.A) (DVR.cP D D.P.A α)).left))
    (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu _))
  refine ⟨v, hv, fun Z r z J hJ => ?_⟩
  let T : Over (Spec (CommRingCat.of R)) := Over.mk r
  have C : IsCub (cubV D.cub (T := T) z J) := isCub_cubV D.cub hJ
  have e := (ros_add D.cub hG D.P.isAb a a' u hu u₀ (T := T) hJ 1 1 (DVR.cP D _ α)).1
  rw [_root_.mul_one, MonObj.one_comp, C.face, C.face, _root_.mul_one, _root_.one_mul] at e
  have e' : val₂ u (T := T) z J 1 (DVR.cP D _ α) = 1 := mul_eq_left.1 e.symm
  have o : (1 : T ⟶ D.P.A).left = r ≫ eSec D.P.A := rfl
  have k : (r ≫ eSec D.P.A) ≫ (lift (𝟙 D.P.A) (DVR.cP D D.P.A α)).left = (lift (1 : T ⟶ D.P.A) (DVR.cP D T α)).left := by
    rw [← o, ← Over.comp_left, comp_lift, DVR.comp_cP, Category.comp_id]
  rw [vv Z _ z J hJ, val_inv, val_pull hJ, k]
  exact inv_eq_one.2 e'

theorem exists_iota : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ α : D.toPre.X, ∃ u : LB.Gen (IotaLB D.toPre a α (h' α)), IsIota u := by
  intro R _ _ _ _ D a a' h h' hE α
  obtain ⟨h₁, h₂, hr, -, hc, -⟩ := hE
  exact exists_iota_of_rosati D.toPre a a' hr α (h' α) (hc α)

end GlobalTheory.TwFam
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

namespace GlobalTheory.TwFam.AdicSum

variable {R : Type} [CommRing R] [IsDomain R]

theorem exists_finsum {D : DegPre R} {a : D.P.A ⟶ D.P.A} {n j : ℤ} {Ix : Type} {w : Ix → D.X}
    (s : ∀ i, SecT D a n j (w i)) (β : D.X) (T : Finset Ix) (hT : ∀ i ∈ T, w i = β) :
    ∃ g : SecT D a n j β, ∀ (Z : Scheme.{0}) (r : Z ⟶ D.P.A.left) (z : Z) (J), Good D.P.L z J →
      sval g r z J = ∑ i ∈ T, sval (s i) r z J := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨zeroT D a n j β, fun Z r z J hJ => by rw [sval_zeroT _ _ _ _ _ _ z J hJ, Finset.sum_empty]⟩
  | insert i T hi ih =>
    obtain ⟨g, hg⟩ := ih fun k hk => hT k (Finset.mem_insert_of_mem hk)
    obtain rfl := hT i (Finset.mem_insert_self _ _)
    refine ⟨H1.SectionArithmetic.secAdd (s i) g, fun Z r z J hJ => ?_⟩
    rw [Finset.sum_insert hi, ← hg Z r z J hJ]
    exact gs_add r z _ (hJ.mem _ r) _ _


open Classical in
theorem sum_indep (I : Ideal R) {D : DegPre R} {a : D.P.A ⟶ D.P.A} {n j : ℤ} {Ix : Type} {w : Ix → D.X}
    (s : ∀ i, SecT D a n j (w i)) (e : ℕ) (S S' : Finset Ix) (hS : ∀ i ∉ S, Van I (s i) e)
    (hS' : ∀ i ∉ S', Van I (s i) e) (δ : D.X) {Z : Scheme.{0}} (x : Z ⟶ (thickObj R I e D.P.A).left) (z : Z) (J)
    (hJ : Good D.P.L z J) :
    ∑ i ∈ S.filter (fun i => w i = δ), sval (s i) (x ≫ pullback.fst D.P.A.hom (thick R I e)) z J =
      ∑ i ∈ S'.filter (fun i => w i = δ), sval (s i) (x ≫ pullback.fst D.P.A.hom (thick R I e)) z J := by
  have key : ∀ T T' : Finset Ix, (∀ i ∉ T, Van I (s i) e) → T ⊆ T' →
      ∑ i ∈ T.filter (fun i => w i = δ), sval (s i) (x ≫ pullback.fst D.P.A.hom (thick R I e)) z J =
      ∑ i ∈ T'.filter (fun i => w i = δ), sval (s i) (x ≫ pullback.fst D.P.A.hom (thick R I e)) z J :=
    fun T T' hT h => Finset.sum_subset (Finset.filter_subset_filter _ h) fun i hi hi' =>
      hT i (fun hm => hi' (Finset.mem_filter.2 ⟨hm, (Finset.mem_filter.1 hi).2⟩)) Z x z J hJ
  exact (key S (S ∪ S') hS Finset.subset_union_left).trans (key S' (S ∪ S') hS' Finset.subset_union_right).symm

omit [IsDomain R] in
theorem thickMap_fst (I : Ideal R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) :
    thickMap R I e G ≫ pullback.fst G.hom (thick R I (e + 1)) = pullback.fst G.hom (thick R I e) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

theorem van_of_succ (I : Ideal R) {D : DegPre R} {K : Type} [Fintype K] {φ : K → (D.P.A.left ⟶ D.P.A.left)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb D.P.L φ ε)) (e : ℕ) (h : Van I s (e + 1)) : Van I s e := fun Z x z J hJ => by
  have := h Z (x ≫ thickMap R I e D.P.A) z J hJ
  rwa [Category.assoc, thickMap_fst] at this

theorem exists_isSum : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (n j : ℤ) (Ix : Type) (w : Ix → D.toPre.X) (s : ∀ i, SecT D.toPre a n j (w i)), Small (maximalIdeal R) s → ∃ F : ∀ β, SecT D.toPre a n j β, IsSum (maximalIdeal R) s F ∧ Small (maximalIdeal R) (w := id) F := by
  intro R _ _ _ hR D a n j Ix w s hs
  classical
  have hC := hR.2.2.2
  have hS : ∀ e, ∀ i ∉ (hs e).toFinset, Van (maximalIdeal R) (s i) e := fun e i hi => by
    by_contra h
    exact hi ((Set.Finite.mem_toFinset _).2 h)
  choose g hg using fun e β => exists_finsum s β ((hs e).toFinset.filter (fun i => w i = β))
    (fun i hi => (Finset.mem_filter.1 hi).2)
  choose F hF using fun β => GlobalTheory.SecAlgLinComb.exists_sec_linComb R (maximalIdeal R) hC D.toPre.P.A
    D.toPre.P.isAb.smooth (AbProj.isProjBy_of_isPullback D.toPre.P (IsPullback.id_horiz _)) _ D.toPre.P.L (Fin 5)
    (tφ D.toPre a β) (tε n j) _ D.toPre.P.isLB (fun _ _ => rfl)
    (fun e => H1.SectionArithmetic.pullSec (g e β) (pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e)))
    (fun e z J hJ => by
      refine (H1.SectionArithmetic.sval_pullSec _ _ _ z hJ).trans (Eq.trans ?_ (H1.SectionArithmetic.sval_pullSec _ _ _ z hJ).symm)
      rw [thickMap_fst, hg _ _ _ _ z J hJ, hg _ _ _ _ z J hJ]
      refine Eq.trans ?_ (sum_indep (maximalIdeal R) s e _ _ (fun i hi => van_of_succ _ _ e (hS (e + 1) i hi)) (hS e) β
        (𝟙 _) z J hJ)
      rw [Category.id_comp])
  have hsum : IsSum (maximalIdeal R) s F := fun e S hS' δ Z x z J hJ => by
    refine (hF δ e Z x z J hJ).trans ((H1.SectionArithmetic.sval_pullSec _ _ _ z hJ).trans ((hg _ _ _ _ z J hJ).trans ?_))
    convert sum_indep (maximalIdeal R) s e _ _ (hS e) hS' δ x z J hJ
  refine ⟨F, hsum, fun e => ((hs e).image w).subset fun β hβ => ?_⟩
  by_contra hn
  refine hβ fun Z x z J hJ => (hsum e _ (hS e) β Z x z J hJ).trans (Finset.sum_eq_zero fun i hi => ?_)
  obtain ⟨h₁, h₂⟩ := Finset.mem_filter.1 hi
  exact (hn ⟨i, (Set.Finite.mem_toFinset _).1 h₁, h₂⟩).elim

end GlobalTheory.TwFam.AdicSum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

noncomputable section

namespace GlobalTheory.TwFac

theorem exists_zpow {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (n : ℤ) :
    ∃ t' : LB.Gen (LB.LinComb L φ (fun k => ε k * n)), t'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J, val t' r z J = val t r z J ^ n := by
  refine ⟨⟨fun j => (show Γ(Y, LB.wchart L φ j)ˣ from t.s j) ^ n⟩, fun i j => ?_, fun Z r z J => map_zpow _ _ _⟩
  refine ((map_zpow _ _ _).trans ((congrArg (· ^ n) (ht i j)).trans (mul_zpow _ _ _))).trans
    (congrArg₂ (· * ·) ?_ (map_zpow _ _ _).symm)
  exact (Finset.prod_zpow _ _ _).symm.trans (Finset.prod_congr rfl fun k _ => (zpow_mul _ _ _).symm)

theorem exists_norm {X Y S₀ : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (S₀ ⟶ X)} {ε' : K' → ℤ}
    (p : Y ⟶ S₀) (e : S₀ ⟶ Y) (he : e ≫ p = 𝟙 _) (hF : FormEq (fun k => e ≫ φ k) ε φ' ε')
    (w : LB.Gen (LB.LinComb M φ ε)) (hw : w.IsGen) (v : LB.Gen (LB.LinComb M φ' ε')) (hv : v.IsGen) :
    ∃ u : LB.Gen (LB.LinComb M φ ε), u.IsGen ∧ ∀ y J, Good M y J → val u e y J = val v (𝟙 _) y J := by
  obtain ⟨u, hu, vu⟩ := exists_gen hM (φ' := φ) (ε' := ε) (fun U _ h => by
      have q := hF U (fun g => h (p ≫ g))
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
      rw [q, mul_inv_cancel, _root_.mul_one])
    (LB.mulGen M _ _ _ _ w (LB.pullGen M _ _ (LB.mulGen M _ _ _ _ v (LB.invGen M _ _ (LB.pullGen M _ _ w e))) p))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hw (DVR.pullGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ hv
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hw _))) _))
  refine ⟨u, hu, fun y J hJ => ?_⟩
  rw [vu _ _ y J hJ, val_mul hJ, val_pull hJ, he, val_mul hJ, val_inv, val_pull hJ, Category.id_comp, mul_comm,
    inv_mul_cancel_right]

variable {R : Type} [CommRing R] [IsDomain R]

theorem tr_left (D : DegPre R) (mu : D.X) :
    (DegPre.trF D (FractionRing R) mu).left ≫ (DegPre.prB D (FractionRing R)).left =
      (DegPre.prB D (FractionRing R)).left ≫ (padd D.P.A (𝟙 _) (toUnit _ ≫ D.c mu)).left := by
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  refine (lift_snd _ _).trans ?_
  refine Eq.trans ?_ (MonObj.comp_mul _ _ _).symm
  rw [Category.comp_id]
  exact congrArg (DegPre.prB D (FractionRing R) * ·) (DVR.comp_cP D _ mu).symm

theorem prod_t (D : DegPre R) (a : D.P.A ⟶ D.P.A) (β : D.X) (n j : ℤ) {T : Over (Sp R)} (y : T ⟶ D.P.A)
    {U : Type} [CommGroup U] (g : (T.left ⟶ D.P.A.left) → U) :
    ∏ k, g (y.left ≫ tφ D a β k) ^ tε n j k = g y.left ^ (n - 1) * g (y * DVR.cP D T β).left *
      (g (DVR.cP D T β).left)⁻¹ * g (1 : T ⟶ D.P.A).left * g (y ≫ a).left ^ j := by
  have e₀ : y.left ≫ tφ D a β 0 = y.left := Category.comp_id _
  have e₁ : y.left ≫ tφ D a β 1 = (y * DVR.cP D T β).left :=
    congrArg (fun q => q.left) ((MonObj.comp_mul y (𝟙 _) (DVR.cP D _ β)).trans (by rw [DVR.comp_cP, Category.comp_id]))
  have e₂ : y.left ≫ tφ D a β 2 = (DVR.cP D T β).left := congrArg (fun q => q.left) (DVR.comp_cP D y β)
  have e₃ : y.left ≫ tφ D a β 3 = (1 : T ⟶ D.P.A).left :=
    congrArg (fun q : T ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) y)
  have e₄ : y.left ≫ tφ D a β 4 = (y ≫ a).left := rfl
  rw [Fin.prod_univ_five, e₀, e₁, e₂, e₃, e₄]
  show _ ^ (n - 1) * _ ^ (1 : ℤ) * _ ^ (-1 : ℤ) * _ ^ (1 : ℤ) * _ ^ j = _
  rw [zpow_one, zpow_one, zpow_neg_one]

theorem exists_fac (D : DegPre R) (a : D.P.A ⟶ D.P.A) (h : D.X →+ D.X) [IsMonHom a] (hh : ∀ y, D.c (h y) = D.c y ≫ a)
    (n j : ℤ) (mu β β' : D.X) (w : LB.Gen (LB.LinComb D.P.L (dφ D a mu β β') (dε n j))) (hw : w.IsGen) :
    ∃ u, IsFac D a h n j mu β β' u := by
  obtain ⟨p₁, h₁, v₁⟩ := exists_zpow (D.psi mu) (D.psi_gen mu) n
  obtain ⟨p₂, h₂, v₂⟩ := exists_zpow (D.psi (h mu)) (D.psi_gen _) j
  obtain ⟨p₃, h₃, v₃⟩ := exists_zpow D.rigK (DVR.pullGen_isGen _ _ _ _ D.rig_gen _) (n + j)
  have z₁ : DegPre.zF D (FractionRing R) ≫ fst _ _ = 𝟙 _ := lift_fst _ _
  have z₂ : DegPre.zF D (FractionRing R) ≫ DegPre.prB D (FractionRing R) = 1 := lift_snd _ _
  have z₃ : DegPre.zF D (FractionRing R) ≫ DegPre.trF D (FractionRing R) mu ≫ DegPre.prB D (FractionRing R) =
      DVR.cP D _ mu := by
    rw [DVR.trF_eq, DVR.tr_pr, MonObj.comp_mul, z₂, ← Category.assoc, z₁, Category.id_comp, _root_.one_mul]
  obtain ⟨u, hu, vu⟩ := exists_norm D.P.isLB (fst (TF (R := R) (FractionRing R)) D.P.A).left
    (DegPre.zF D (FractionRing R)).left (congrArg (fun q => q.left) z₁) (fun U _ g => by
      have a₁ : ∀ χ, jFK (R := R) (FractionRing R) ≫ ptK (D.c χ) = (DVR.cP D (TF (R := R) (FractionRing R)) χ).left :=
        fun χ => (Category.assoc _ _ _).symm
      have a₂ : jFK (R := R) (FractionRing R) ≫ (toUnit (TK R)).left ≫ eSec D.P.A =
          (1 : TF (R := R) (FractionRing R) ⟶ D.P.A).left := (Category.assoc _ _ _).symm
      have q₁ := prod_t D a β' n j (DegPre.zF D (FractionRing R) ≫ DegPre.prB D (FractionRing R)) g
      have q₂ := prod_t D a β n j
        (DegPre.zF D (FractionRing R) ≫ DegPre.trF D (FractionRing R) mu ≫ DegPre.prB D (FractionRing R)) g
      have b₁ : (1 : TF (R := R) (FractionRing R) ⟶ D.P.A) ≫ a = 1 := MonObj.one_comp _
      have b₂ : DVR.cP D (TF (R := R) (FractionRing R)) mu ≫ a = DVR.cP D _ (h mu) := by
        rw [DVR.cP, DVR.cP, hh, Category.assoc]
      conv_rhs at q₁ => rw [z₂, b₁, _root_.one_mul]
      conv_rhs at q₂ => rw [z₃, b₂, ← DVR.cPoint_add]
      simp only [Over.comp_left, Category.assoc] at q₁ q₂
      refine (DVR.prod_sum₂ (K := Fin 5) (K' := Fin 5) (U := U) _ q₁ (DVR.prod_neg _ _ q₂)).trans ?_
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, a₁, a₂]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    w hw (LB.pullGen D.P.L _ _ (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ p₁ p₂)
      (D.tau mu β)) p₃) (jFK (R := R) (FractionRing R)))
    (DVR.pullGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ h₁ h₂) (DVR.tau_isGen D mu β)) h₃) _)
  refine ⟨u, hu, fun z J hJ => (vu z J hJ).trans ((val_pull hJ _ _ _).trans ?_)⟩
  rw [Category.id_comp]
  exact (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (v₁ _ _ _ _) (v₂ _ _ _ _))) rfl)) (v₃ _ _ _ _))

theorem fac_exists_unique_const : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (h : D.toPre.X →+ D.toPre.X), IsMonHom a → (∀ y, D.toPre.c (h y) = D.toPre.c y ≫ a) → ∀ (n j : ℤ) (mu β β' : D.toPre.X) (u₀ : LB.Gen (LB.LinComb D.toPre.P.L (Sum.elim (tφ D.toPre a β') (fun k => (padd D.toPre.P.A (𝟙 _) (toUnit _ ≫ D.toPre.c mu)).left ≫ tφ D.toPre a β k)) (dε n j))), u₀.IsGen → (∃ u, IsFac D.toPre a h n j mu β β' u) ∧ (∀ u u', IsFac D.toPre a h n j mu β β' u → IsFac D.toPre a h n j mu β β' u' → ∀ (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF D.toPre (FractionRing R)).left) (z : Z) (J), Good D.toPre.P.L z J → val u x z J = val u' x z J) ∧ ∀ u : LB.Gen (LB.LinComb D.toPre.P.L (dφ D.toPre a mu β β') (dε n j)), u.IsGen → ∃ c : (FractionRing R), ∀ (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF D.toPre (FractionRing R)).left) (z : Z) (J), Good D.toPre.P.L z J → (val u x z J).val = gs x z ⊤ (scal ((fst _ _ : DegPre.BF D.toPre (FractionRing R) ⟶ TF (R := R) (FractionRing R)).left : (DegPre.BF D.toPre (FractionRing R)).left ⟶ Sp (FractionRing R)) c) * (val u₀ (x ≫ (DegPre.prB D.toPre (FractionRing R)).left) z J).val := by
  intro R _ _ _ _ D a h ha hh n j mu β β' u₀ hu₀
  have hL := D.toPre.P.isLB
  have hs := DVR.surj_appTop D.toPre (FractionRing R) GlobalTheory.globalFns_holds
  obtain ⟨w, hw, vw⟩ := exists_gen hL (φ' := dφ D.toPre a mu β β') (ε' := dε n j) (fun U _ g => by
      refine Finset.prod_congr rfl ?_
      rintro (k | k) -
      · rfl
      · simp only [dφ, Sum.elim_inr]
        rw [← Category.assoc, ← tr_left, Category.assoc])
    (LB.pullGen D.toPre.P.L _ _ u₀ (DegPre.prB D.toPre (FractionRing R)).left) (DVR.pullGen_isGen _ _ _ _ hu₀ _)
  refine ⟨exists_fac D.toPre a h hh n j mu β β' w hw, fun u u' hu hu' => ?_, fun u hu => ?_⟩
  · have z₁ : DegPre.zF D.toPre (FractionRing R) ≫ fst _ _ = 𝟙 _ := lift_fst _ _
    exact gen_unique hL (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left (DegPre.zF D.toPre (FractionRing R)).left
      (congrArg (fun q => q.left) z₁) hs hu.1 hu'.1 (fun y J hJ => (hu.2 y J hJ).trans (hu'.2 y J hJ).symm)
  · obtain ⟨c, hc⟩ := GlobalTheory.WeilMul.exists_ratio hL (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left hs hu hw
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom c, fun Z x z J hJ => ?_⟩
    have e : (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom c) = c := Iso.hom_inv_id_apply _ c
    have e₂ := (hc Z x z J hJ).trans ((gs_pull x (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left z ⊤ trivial c).symm)
    rw [vw _ _ z J hJ, val_pull hJ] at e₂
    refine Eq.trans ?_ (congrArg₂ (· * ·) (e₂.trans (congrArg (fun q => gs x z ⊤
      ((fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left.appTop.hom q)) e.symm)) rfl)
    rw [← Units.val_mul, inv_mul_cancel_right]

end GlobalTheory.TwFac
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatValZero

section Gen

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions
  GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.FlatCore GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}

theorem nonempty_keySec (hL : Laws U x) : Nonempty (KeySec Xo c) := by
  obtain ⟨κ, k₁, k₂, -, k₄, -, k₆, -, -⟩ := GlobalTheory.KeyFamClosing.keyFam_one
  let e : Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ))) ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ) :=
    (Fintype.equivFin _).symm
  obtain ⟨K, hKmem, hKval⟩ := GlobalTheory.T.exists_unit_section_thetaKeyRule_weightFour κ k₁ k₂ k₆ E H Dw l Xo c _ e hL.pos
  have hσ0 := goodEmb_goodOf c c.F.val.toRingHom
  obtain ⟨ρ, -⟩ := GlobalTheory.T.exists_keySection_fourthRoot_perComponent κ k₁ k₂ k₆ k₄ E H Dw l Xo c _ e _ r (U _) K hσ0 (hL.unf _ hσ0) hL.geo hL.pos
    hKmem hKval
  exact ⟨ρ⟩

def unitsV (T : CDVR) : Submonoid T.Fr where
  carrier := {z | z ≠ 0 ∧ vV T.V z = 0}
  one_mem' := ⟨one_ne_zero, by simp [vV]⟩
  mul_mem' := fun {a b} ha hb => ⟨mul_ne_zero ha.1 hb.1, by rw [vV_mul ha.1 hb.1, ha.2, hb.2, add_zero]⟩

end Gen

end GlobalTheory.FlatValZero

open GlobalTheory.FlatValZero


end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.MBLow.TRank

theorem main : ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (x : KeyIn K) (g : ℕ) (hg : x.P.g = g) (m : ℕ), Odd m → 3 ≤ m → ∀ (I : Type) (pt : I → (baseOver (Sp K) ⟶ x.P.A)), (∀ z : baseOver (Sp K) ⟶ x.P.A, z ^ (m ^ 2) = 1 → ∃ i, pt i = z) → ∀ ϑ J, ThJet x hg m pt ϑ J → ∀ (c₀ : K) (c : Fin g → K), (∀ i, c₀ * ϑ i + ∑ j, c j * J i j = 0) → c₀ = 0 ∧ c = 0 := by
  intro K _ _ _ x g hg m hm hm3 I pt hpt ϑ J hTJ c₀ c hrel
  obtain ⟨th, hth, U, t, i₀, c', hUt, hi₀, hval⟩ := hTJ
  have hg1 : 1 ≤ g := hg ▸ x.g_pos
  let j₀ : Fin g := ⟨0, hg1⟩
  have hy : ∀ j : Fin g, epsLift (x.v (j.cast hg.symm)) ≫ (fst (baseOver (Sp K)) x.P.A).left =
      spMap (algebraMap K (DualNumber K)) := fun j => by
    rw [epsLift, ← Over.comp_left, lift_fst]; rfl
  choose f hf using fun j : Fin g => GlobalTheory.T.exists_linear_sectionValue_abelianPower K x (m ^ 2) (fun _ => i₀) (DualNumber K) _ (hy j)
  set a := c₀ - ∑ j, c j * c' j with ha
  let Φ : EA x.P (𝟙 (Sp K)) (m ^ 2) →ₗ[K] K :=
    a • ((TrivSqZeroExt.fstHom K K K).toLinearMap ∘ₗ f j₀) + ∑ j, c j • (TrivSqZeroExt.sndHom K K ∘ₗ f j)
  have hΦ : ∀ s, Φ s = a * (f j₀ s).fst + ∑ j, c j * (f j s).snd := fun s => by
    rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul]
    rfl
  have hft : ∀ j i, f j (SecMod.mk (fst (baseOver (Sp K)) x.P.A).left (t i)) =
      valR (epsLift (x.v (j.cast hg.symm))) ((LPow x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (baseOver (Sp K))).U fun _ => i₀)
        ((t i).f fun _ => i₀) := fun j i => hf j _
  have hΦt : ∀ i, Φ (SecMod.mk (fst (baseOver (Sp K)) x.P.A).left (t i)) = 0 := fun i => by
    rw [hΦ]
    simp only [hft, hval]
    set r := valR (𝟙 (Sp K)) ((x.P.L.pull (eSec x.P.A)).U fun _ => i₀) (x.rig.s fun _ => i₀).val ^ (m ^ 2)
    simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl,
      TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr, smul_eq_mul,
      MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, add_zero, zero_add, mul_zero, zero_mul]
    have e1 : ∑ j, c j * (r * (J i j + c' j * ϑ i)) = r * ∑ j, c j * J i j + r * ϑ i * ∑ j, c j * c' j := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e1, ha]
    linear_combination r * hrel i
  have hspan := GlobalTheory.T.span_thetaTranslates_torsion_eq_top K x m hm hm3 I pt hpt th hth U t hUt
  have hΦ0 : Φ = 0 := LinearMap.ext_on_range hspan fun i => by rw [hΦt i, LinearMap.zero_apply]
  have hsep := GlobalTheory.T.sections_lineBundlePow_separate_firstJets_origin K x g hg (m ^ 2) (by nlinarith) i₀ hi₀ j₀ a c fun s => by
    have h := congrArg (fun F => F (SecMod.mk (fst (baseOver (Sp K)) x.P.A).left s)) hΦ0
    simp only [LinearMap.zero_apply, hΦ] at h
    rw [hf j₀, Finset.sum_congr rfl fun j _ => by rw [hf j]] at h
    exact h
  obtain ⟨h1, h2⟩ := hsep
  refine ⟨?_, h2⟩
  subst h2
  simpa [ha] using h1

end GlobalTheory.MBLow.TRank
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.VertHeight

theorem charZero_residueField_genericPoint (Z : Scheme.{0}) [IsIntegral Z] (hc : CharZero Γ(Z, ⊤)) :
    CharZero (Z.residueField (genericPoint Z)) := by
  have h₁ : CharZero Z.functionField :=
    (RingHom.charZero_iff (Z.germToFunctionField_injective ⊤)).1 hc
  exact (RingHom.charZero_iff (Z.residue (genericPoint Z)).hom.injective).1 h₁

theorem height_nonneg_of_vertical : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (C : HermLB p) (h : X → ℝ), NefFib C →
    C.IsArithHeight h → ∀ z : X, ¬ CharZero (X.residueField z) → 0 ≤ h z := by
  intro k _ X _ p D hX C h hC H z hz
  obtain ⟨Z, i, _, _, rfl⟩ := exists_isClosedImmersion_genericPoint z
  rcases hX.vertical_or_horizontal i with ⟨ℓ, _, ⟨a⟩⟩ | ⟨hc, -⟩
  · letI := a
    haveI := hX.finite
    obtain ⟨d, hd⟩ := hX.exists_dim_eq i
    rw [H.vertical Z i (ZMod ℓ) d hd, Nat.card_zmod]
    refine mul_nonneg ?_ (Real.log_nonneg (by exact_mod_cast (Fact.out : ℓ.Prime).one_le))
    have hN := GlobalTheory.FibreNef.isNef_pull_of_nefOver ℓ i C
      ((GlobalTheory.VertForm.nefFib_iff C).1 hC ℓ Fact.out)
    rw [topSelf_def]
    exact_mod_cast GlobalTheory.nefNumerics_outright.1.interNum_nonneg
      (GlobalTheory.FibreNef.isProjOver_fibre hX.isProjOver ℓ i) hd fun _ => hN
  · haveI := charZero_residueField_genericPoint Z hc
    exact absurd ((i.residueFieldMap (genericPoint Z)).hom.charZero) hz

end GlobalTheory.VertHeight
end
