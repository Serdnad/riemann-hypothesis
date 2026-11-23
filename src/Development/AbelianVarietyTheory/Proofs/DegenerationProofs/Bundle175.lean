module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle169
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralDegenerationFamilyBaseChangeExtensionFie
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle028
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsFOfIntegral
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueGeneratorExtendDiscreteValuationRing
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle089
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CardTorsionTranslateZerosLt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle054
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle067
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle104
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle103
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
import Mathlib.RingTheory.Radical.NatInt
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle075
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBCorr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory.UT GlobalTheory.ZH.ClassWeight

noncomputable section
namespace GlobalTheory.ZH.IntegralCarry
open GlobalTheory.FieldBaseChange GlobalTheory.ThetaScalar ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ZH.ParTranslate GlobalTheory.ThetaSpecialise

section
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G] (U : UnifPre I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ)

theorem expandsG_extend
    (σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))))
    (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (hE : ∀ e, U.ExpandsAt e k σ f) (s : Fam D.toPre F k)
    (hs : FamOf D.toPre F f s) : U.ExpandsG F k (extendSec U F k (genericSec U k σ)) s := by
  have one : ∀ {Y : Scheme.{0}} (π : Y ⟶ Spec (CommRingCat.of F)) (y : Y), gs (𝟙 Y) y ⊤ (scal π (1 : F)) = 1 :=
    fun π y => by simp only [gs_eq _ y ⊤ trivial, scal, map_one]
  refine ⟨1, fun _ => 1, fun _ => σ, fun _ => f, fun _ => hE,
    (secLin_iff_val U.LG.isLB _ _ _ _).2 fun y J hJ => ?_,
    fun α => (secLin_iff_val D.toPre.P.isLB _ _ _ _).2 fun y J hJ => ?_⟩
  · rw [Fin.sum_univ_one, one, _root_.one_mul]
    exact (sval_pullOver _ _ _ _ hJ).trans ((sval_pullOver _ _ _ _ hJ).trans
      (congrArg (fun q => sval σ q y J) (Category.assoc _ _ _)))
  · rw [Fin.sum_univ_one, one, _root_.one_mul]
    exact (SectionScalarValuation.secScal_sval (hs α) _ y hJ).symm

theorem famOf_zero (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (s : Fam D.toPre F k)
    (hs : FamOf D.toPre F f s) (α : D.toPre.X) (h : ∀ j, (f α).f j = 0) (j) : (s.s α).f j = 0 := by
  refine sec_ext_val (s' := (0 : Fam D.toPre F k).s α) D.toPre.P.isLB (fun y J hJ => ?_) j
  refine (SectionScalarValuation.secScal_sval (hs α) _ y hJ).symm.trans (Eq.trans ?_ (sval_zero' (π := famBase D.toPre F) hJ _).symm)
  exact (gs_eq _ _ _ (hJ.mem _ _) _).trans ((congrArg _ ((congrArg _ (h _)).trans (map_zero _))).trans (map_zero _))

theorem crd_carries (w : W0 U) {J : Type}
    (σ : J → LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))))
    (t : J → SecA A F k) (ht : ∀ i, Carries U F k w (t i) (extendSec U F k (genericSec U k (σ i))))
    (a : TFK (R := R) F ⟶ (Over.pullback (jK R)).obj G) (v : J → F)
    (h : Crd _ σ (show Sp F ⟶ G.left from a.left ≫ pullback.fst G.hom (jK R)) v) :
    Crd (LPow A.A A.L (k : ℤ) (TFK (R := R) F)) t (show Sp F ⟶ _ from (ptSecT A.A (a ≫ U.gen.hom)).left) v := by
  obtain ⟨l', c, hl', hv⟩ := h
  obtain ⟨l, rfl⟩ : ∃ l : U.LG.L.ι, l' = fun _ : Fin 1 => l := ⟨l' 0, funext fun i => congrArg l' (Subsingleton.elim _ _)⟩
  let y : Sp F := IsLocalRing.closedPoint F
  let x : Sp F ⟶ G.left := a.left ≫ pullback.fst G.hom (jK R)
  have m : x y ∈ LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => l) := (top_le_iff_mem _ _ y).1 hl'
  have m₀ : x y ∈ U.LG.L.U l := mem_wchart.1 m 0
  obtain ⟨J₀, hJ⟩ := GlobalTheory.UT.CoefBasic.exists_good' A.isLB y
  obtain ⟨d, hd⟩ := exists_unit_carries U F k w a l ((top_le_iff_mem x _ y).2 m₀) y J₀ hJ
  obtain ⟨d₀, hd₀⟩ := toStk_onto y d.val
  have hd₁ : d₀ ≠ 0 := fun h0 => by
    have : Nontrivial ((Sp F).presheaf.stalk y) := inferInstance
    rw [h0, map_zero] at hd₀
    exact Units.ne_zero _ hd₀.symm
  let r : Sp F ⟶ (UnifPre.GF (G := G) F).left := (lift (𝟙 (TFK (R := R) F)) a).left
  let r' : Sp F ⟶ (TFK (R := R) F ⊗ A.A).left := (ptSecT A.A (a ≫ U.gen.hom)).left
  have e₀ : r ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left = a.left :=
    congrArg (fun q => q.left) (lift_snd (𝟙 (TFK (R := R) F)) a)
  have e₁ : (r ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left) ≫ pullback.fst G.hom (jK R) = x := by
    rw [e₀]
  have m₂ : ((r ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left) ≫ pullback.fst G.hom (jK R)) y ∈
      U.LG.L.U l := e₁ ▸ m₀
  have m' := hJ.mem (fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) r'
  refine ⟨fun _ : Fin 1 => J₀ (r' ≫ (snd (TFK (R := R) F) A.A).left), c * Units.mk0 d₀ hd₁,
    (top_le_iff_mem r' _ y).2 m', fun i => ?_⟩
  rw [hv i, Units.val_mul, _root_.mul_assoc, Units.val_mk0]
  refine congrArg _ ((toStk y).injective ?_)
  rw [map_mul, hd₀]
  refine (toStk_valF_gs x _ y m _).trans (Eq.trans ?_ ((hd _ _ (ht i)).trans
    (congrArg _ (toStk_valF_gs r' _ y m' _).symm)))
  refine Eq.symm ((toStk_valF_gs r _ y (mem_wchart.2 fun _ => m₂) _).trans ?_)
  rw [← e₁]
  exact (gs_pullOver (isPullback_groupBase F).w (fun _ => rfl) (genericSec U k (σ i)) r y (fun _ => l)
      (fun _ => m₂)).trans (gs_pullOver (p := pullback.fst G.hom (jK R)) pullback.condition
        (fun _ => (Category.comp_id _).symm) (σ i) _ y (fun _ => l) (fun _ => m₂))

end

theorem exists_carry : LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (k : ℕ) (J : Type) (σ : J → (u.H k).Sec) (f : J → ∀ α, u.D.toPre.SecB k α), (∀ i e, u.U.toUnifPre.ExpandsAt e k (σ i) (f i)) → (∀ i, ∃ s : Fam u.D.toPre (FractionRing u.V) k, FamOf u.D.toPre _ (f i) s) → ∀ w₀ : W0 u.U.toUnifPre, w₀.IsGen → ∃ (t : J → SecA u.A (PadicAlgCl p) k) (s : J → Fam u.D.toPre (PadicAlgCl p) k), (∀ i, u.U.toUnifPre.ExpandsF (PadicAlgCl p) k w₀ (t i) (s i)) ∧ (∀ i α, (∀ j, (f i α).f j = 0) → ∀ j, ((s i).s α).f j = 0) ∧ ∀ (a : u.PtC) (v : J → PadicAlgCl p), Crd (u.H k) σ (u.toG a) v → Crd (LPow u.A.A u.A.L (k : ℤ) (TFK (R := u.V) (PadicAlgCl p))) t (show Sp (PadicAlgCl p) ⟶ _ from (ptSecT u.A.A (a ≫ u.U.gen.hom)).left) v := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u k J σ f hE hf w₀ hw₀
  have hs : ∀ i, ∃ s : Fam u.D.toPre (PadicAlgCl p) k, FamOf u.D.toPre _ (f i) s := fun i => by
    obtain ⟨s, hs⟩ := hf i
    exact GlobalTheory.FamBaseChange.main hL.1.globalFns u.V _ u.D k s (f i) hs (PadicAlgCl p)
  choose s hs using hs
  choose t ht using fun i => exists_carries u.U.toUnifPre (PadicAlgCl p) k w₀ hw₀
    (extendSec u.U.toUnifPre (PadicAlgCl p) k (genericSec u.U.toUnifPre k (σ i)))
  exact ⟨t, s, fun i => ⟨_, ht i, expandsG_extend _ _ k (σ i) (f i) (hE i) (s i) (hs i)⟩,
    fun i α h j => famOf_zero _ k (f i) (s i) (hs i) α h j,
    fun a v h => crd_carries u.U.toUnifPre _ k w₀ σ t ht a v h⟩

end GlobalTheory.ZH.IntegralCarry
end
end

section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.FewAtTest

open GlobalTheory.CechPic

theorem pic_eq_zero_of_generic {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {H : Scheme.{0}}
    (p : H ⟶ Sp V) (e : Sp V ⟶ H) (hs : Smooth p) (hi : GeometricallyIntegral p) (he : e ≫ p = 𝟙 _) (c : Pic H)
    (h₁ : pull (pullback.fst p (Out.jK V)) c = 0) (h₂ : pull e c = 0) : c = 0 := by
  obtain ⟨M, hM, rfl⟩ := cls_surj c
  let eK : Sp (FractionRing V) ⟶ pullback p (Out.jK V) := pullback.lift (Out.jK V ≫ e) (𝟙 _) (by
    rw [Category.assoc, he, Category.id_comp]; exact Category.comp_id _)
  have heK : eK ≫ pullback.fst p (Out.jK V) = Out.jK V ≫ e := pullback.lift_fst _ _ _
  obtain ⟨t, ht⟩ := (cls_eq_zero_iff (pull_isLB hM (pullback.fst p (Out.jK V) ≫ 𝟙 H))).1 (by
    rw [cls_pull hM, pull_comp, pull_id, h₁])
  obtain ⟨ρ, hρ⟩ := (cls_eq_zero_iff (pull_isLB hM (e ≫ 𝟙 H))).1 (by
    rw [cls_pull hM, pull_comp, pull_id, h₂])
  obtain ⟨u, hu, cu⟩ := DVR.exists_normalized_to hM _ _ t ht (pullback.snd p (Out.jK V)) eK
    (pullback.lift_snd _ _ _) _ _ (LB.pullGen M _ _ ρ (Out.jK V)) (DVR.pullGen_isGen _ _ _ _ hρ _) (by
      congr 1
      funext k
      rw [← Category.assoc, heK, Category.assoc])
  obtain ⟨s, ⟨hs₁, -⟩, -⟩ := GenExtend.existsUnique_gen_extend V (FractionRing V) H H p e hs hi he eK heK M hM
    PUnit (fun _ => 𝟙 H) (fun _ => 1) u ρ hu hρ cu
  have := (cls_eq_zero_iff (pull_isLB hM (𝟙 H))).2 ⟨s, hs₁⟩
  rwa [cls_pull hM, pull_id] at this

theorem lbIso_of_generic {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {G : Over (Sp V)}
    [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (L M : RigLB G)
    (h : LBIso (L.L.pull (pullback.fst G.hom (Out.jK V))) (M.L.pull (pullback.fst G.hom (Out.jK V)))) :
    LBIso L.L M.L := by
  refine (cls_eq_iff L.isLB M.isLB).1 (sub_eq_zero.1 (pic_eq_zero_of_generic G.hom (eSec G) hG.smooth
    (forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hG.smooth hG.geomConnected)
    (Over.w η[G]) _ ?_ ?_))
  · rw [map_sub, sub_eq_zero]
    exact (cls_eq_iff (pull_isLB L.isLB _) (pull_isLB M.isLB _)).2 h
  · have a := (cls_eq_zero_iff (pull_isLB L.isLB (eSec G))).2 ⟨L.rig, L.rigGen⟩
    have b := (cls_eq_zero_iff (pull_isLB M.isLB (eSec G))).2 ⟨M.rig, M.rigGen⟩
    rw [cls_pull L.isLB] at a
    rw [cls_pull M.isLB] at b
    exact (map_sub _ _ _).trans (sub_eq_zero.2 (a.trans b.symm))

theorem natCast_ne_zero_of_isUnit {Z : Scheme.{0}} {K : Type} [Field K] (x : Sp K ⟶ Z) {n : ℕ}
    (h : IsUnit (n : Γ(Z, ⊤))) : (n : K) ≠ 0 := by
  have := (h.map x.appTop.hom).map (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
  rw [map_natCast, map_natCast] at this
  exact this.ne_zero

theorem range_rPt {p : ℕ} [Fact p.Prime] {V : Type} [CommRing V] [IsLocalRing V] (j : V →+* OO p) [IsLocalHom j] :
    Set.range (rPt p ≫ spMap j : Sp (kb p) ⟶ Sp V) = {IsLocalRing.closedPoint V} := by
  have key : ∀ x : Sp (kb p), (rPt p ≫ spMap j : Sp (kb p) ⟶ Sp V) x = IsLocalRing.closedPoint V := fun x => by
    have hx : x = IsLocalRing.closedPoint (kb p) := Subsingleton.elim (α := PrimeSpectrum (kb p)) _ _
    subst hx
    exact (congrArg (PrimeSpectrum.comap j) (IsLocalRing.comap_closedPoint (IsLocalRing.residue (OO p)))).trans
      (IsLocalRing.comap_closedPoint j)
  ext x
  exact ⟨fun ⟨a, ha⟩ => ha ▸ key a, fun h => ⟨IsLocalRing.closedPoint (kb p), (key _).trans h.symm⟩⟩

end GlobalTheory.FewAtTest

namespace GlobalTheory.ZJ

open GlobalTheory.FewAtTest

theorem theta_few : GlobalTheory.ZH.ThmUSt → Out.Laws → Out.Laws2 → ∀ (C : Core) (T : C.Theta), Out.RelAmple C.A T.L.L → Out.KTriv C.A T.L.L → T.L.IsSymmetric → GlobalTheory.ZH.HypS C.A T.L.L → ∀ N n : ℕ, 4 ≤ N → IsUnit (n : Γ(C.Z, ⊤)) → 6 * (N ^ C.g * C.g.factorial) < n ^ 2 → T.Few n := by
  intro hU laws laws₂ C T hA hK hs hS N n hN hn hlt p _ y τ E c
  obtain ⟨-, h0, hG⟩ := (core_basic C).2.2.2.2.2.2.2.2.2.2.2.2 p y τ
  have hL := pull_isLB T.L.isLB τ.φ
  have hi := PolBaseChange.lbIso_refl hL
  obtain ⟨hab, hamp, hkt⟩ := pol_pull _ _ C.A ((Over.pullback (Out.jK τ.V)).obj τ.H) τ.yK τ.φ T.L.L (T.L.L.pull τ.φ)
    T.L.isLB hL C.ab τ.φ_cart hi
  let A : Out.PolAV (Sp (FractionRing τ.V)) :=
    { A := (Over.pullback (Out.jK τ.V)).obj τ.H
      isAb := hab
      g := C.g
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback τ.φ_cart.1 C.dim
      L := T.L.L.pull τ.φ
      isLB := hL
      rigid := PolBaseChange.rigidified_pull τ.φ_cart ⟨T.L.rig, T.L.rigGen⟩
      sym := PolBaseChange.sym_pull τ.φ_cart (CechPic.sym_of_isSymmetric T.L hs)
      ample := hamp hA
      ktriv := hkt hK }
  have := hab.comm
  have hS' := SymBaseChange.hypS_baseChange _ _ C.A ((Over.pullback (Out.jK τ.V)).obj τ.H) τ.yK τ.φ T.L.L
    (T.L.L.pull τ.φ) T.L.isLB hL τ.φ_cart hi hS
  obtain ⟨D, U, hgen⟩ := hU τ.V τ.complete A τ.H hG τ.split hS' (Iso.refl _)
    (inferInstanceAs (IsMonHom (𝟙 ((Over.pullback (Out.jK τ.V)).obj τ.H))))
  have e₁ : LBIso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst τ.H.hom (Out.jK τ.V))) := U.ext
  rw [hgen] at e₁
  have e₂ : LBIso (E.L.L.pull (pullback.fst τ.H.hom (Out.jK τ.V))) (A.L.pull (𝟙 _)) :=
    LBIso.trans (pull_isLB E.L.isLB _) hL (pull_isLB hL _) (LBIso.symm ⟨E.w, E.w_gen⟩)
      (CechPic.iso_of_chart hL (Geo.Tor.chartPullPull _ _ _ rfl)).symm
  have e := lbIso_of_generic hG E.L U.LG
    (LBIso.trans (pull_isLB E.L.isLB _) (pull_isLB hL _) (pull_isLB U.LG.isLB _) e₂ e₁)
  have := isAlgClosed_kb (p := p)
  have := τ.j_loc
  exact GlobalTheory.FewZeros.card_torsion_translate_zeros_lt laws laws₂ τ.V τ.complete D A τ.H U E.L.L E.θ E.L.isLB e E.θ_ne (kb p) (rPt p ≫ spMap τ.j) N n
    (range_rPt τ.j) hN (natCast_ne_zero_of_isUnit (rPt p ≫ y) hn) hlt c

end GlobalTheory.ZJ
end
end
