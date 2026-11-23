module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Mathlib.Tactic.ENatToNat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle001
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGenOfSection
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle034
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle010
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle027
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle031
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle039
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle035
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle038
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle012

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLaw.VeryAmplePull

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}

theorem cst_eq_appLE (f : X ⟶ Spec (CommRingCat.of R)) (W : X.Opens) (r : R) :
    cst f W r = (f.appLE ⊤ W le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) := rfl

theorem appLE_cst {f : X ⟶ Spec (CommRingCat.of R)} {g : R →+* R'} {f' : X' ⟶ Spec (CommRingCat.of R')}
    {φ : X' ⟶ X} (h : φ ≫ f = f' ≫ Spec.map (CommRingCat.ofHom g)) (D : X.Opens) (W : X'.Opens)
    (e : W ≤ φ ⁻¹ᵁ D) (r : R) : (φ.appLE D W e).hom (cst f D r) = cst f' W (g r) := by
  have e₁ : f.appLE ⊤ D le_top ≫ φ.appLE D W e =
      (Spec.map (CommRingCat.ofHom g)).appLE ⊤ ⊤ le_top ≫ f'.appLE ⊤ W le_top := by
    refine (Scheme.Hom.appLE_comp_appLE φ f ⊤ D W le_top e).trans (Eq.trans ?_
      (Scheme.Hom.appLE_comp_appLE f' (Spec.map (CommRingCat.ofHom g)) ⊤ ⊤ W le_top le_top).symm)
    simp only [h]
  have e₂ := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g)
  have e₃ : (Spec.map (CommRingCat.ofHom g)).appLE ⊤ ⊤ le_top = (Spec.map (CommRingCat.ofHom g)).appTop :=
    (Scheme.Hom.app_eq_appLE (Spec.map (CommRingCat.ofHom g)) (U := ⊤)).symm
  rw [cst_eq_appLE, cst_eq_appLE]
  refine (congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) e₁).trans ?_
  rw [e₃]
  exact congrArg (f'.appLE ⊤ W le_top).hom (congrArg (fun q => q.hom r) e₂).symm

theorem closure_eq_top {f : X ⟶ Spec (CommRingCat.of R)} {g : R →+* R'} {f' : X' ⟶ Spec (CommRingCat.of R')}
    {φ : X' ⟶ X} (h : φ ≫ f = f' ≫ Spec.map (CommRingCat.ofHom g)) [IsClosedImmersion (pullback.lift φ f' h)]
    {D : X.Opens} (hD : IsAffineOpen D) {W : X'.Opens} (e : W = φ ⁻¹ᵁ D) (T : Subring Γ(X', W))
    (h₁ : ∀ a, (φ.appLE D W e.le).hom a ∈ T) (h₂ : ∀ c, cst f' W c ∈ T) (x : Γ(X', W)) : x ∈ T := by
  have H := IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom g))
  set p := pullback.fst f (Spec.map (CommRingCat.ofHom g)) with hp
  set q := pullback.snd f (Spec.map (CommRingCat.ofHom g)) with hq
  set u := pullback.lift φ f' h with hu
  have up : u ≫ p = φ := pullback.lift_fst _ _ _
  have uq : u ≫ q = f' := pullback.lift_snd _ _ _
  have : IsAffineHom p := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
  have e' : W = u ⁻¹ᵁ (p ⁻¹ᵁ D) := by rw [e, ← up]; rfl
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := D) le_top le_top
      (UY := p ⁻¹ᵁ D) (by simp)).1
      (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) hD)
  have hs : Function.Surjective (u.appLE (p ⁻¹ᵁ D) W e'.le).hom := by
    subst e'
    rw [← Scheme.Hom.app_eq_appLE]
    exact u.app_surjective _ (hD.preimage p)
  obtain ⟨y, rfl⟩ := hs x
  change y ∈ T.comap (u.appLE (p ⁻¹ᵁ D) W e'.le).hom
  refine (show ⊤ ≤ T.comap (u.appLE (p ⁻¹ᵁ D) W e'.le).hom from ?_) trivial
  rw [← CommRingCat.closure_range_union_range_eq_top_of_isPushout po, Subring.closure_le]
  rintro _ (⟨d, rfl⟩ | ⟨c, rfl⟩)
  · have e₁ := congrArg (fun k => k.hom d) (Scheme.Hom.appLE_comp_appLE u p D (p ⁻¹ᵁ D) W le_rfl e'.le)
    simp only [up] at e₁
    exact (congrArg (· ∈ T) e₁).mpr (h₁ d)
  · have e₁ := congrArg (fun k => k.hom c) (Scheme.Hom.appLE_comp_appLE u q ⊤ (p ⁻¹ᵁ D) W le_top e'.le)
    simp only [uq] at e₁
    obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R')).inv).2 c
    exact (congrArg (· ∈ T) e₁).mpr (h₂ c)

theorem veryAmpleBy_pull : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (f' : X' ⟶ Spec (CommRingCat.of R')) (φ : X' ⟶ X) (h : φ ≫ f = f' ≫ (Spec.map (CommRingCat.ofHom g))), IsClosedImmersion (pullback.lift φ f' h) → ∀ (H' : LB X') (w : LB.Iso H' (H.pull φ)) (s' : Fin (n + 1) → LB.Sec H'), H'.IsLB → w.IsGen → (∀ j, (∀ z (k : (H).ι) (k' : (H').ι), (φ) z ∈ (H).U k → z ∈ (H').U k' → gs (φ) z _ ((s j).f k) = (Geo.Tor.gw (w) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s' j).f k'))) → VeryAmpleBy f' H' s' := by
  intro R _ X f H n s hP ⟨hcov, hs⟩ R' _ g X' f' φ h hcl H' W s' hP' _ hs'
  have : IsAffineHom φ := by
    have : IsAffineHom (pullback.fst f (Spec.map (CommRingCat.ofHom g))) :=
      MorphismProperty.of_isPullback (P := @IsAffineHom)
        (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom g))).flip inferInstance
    rw [← pullback.lift_fst φ f' h]
    infer_instance
  have loc : ∀ i, nonzeroLocus (s' i) = φ ⁻¹ᵁ nonzeroLocus (s i) := fun i => by
    ext y
    refine (mem_nonzeroLocus _ y).trans
      (Iff.trans ⟨fun ⟨k, hk, u⟩ => ?_, fun ⟨j, hj, u⟩ => ?_⟩ (mem_nonzeroLocus _ (φ y)).symm)
    · obtain ⟨j, hj⟩ := exists_chart hP (φ y)
      have e := hs' i y j k hj hk
      rw [gs_stalkMap φ y _ hj] at e
      exact ⟨j, hj, (isUnit_map_iff (φ.stalkMap y).hom _).1 ((congrArg IsUnit e).mpr ((Units.isUnit _).mul u))⟩
    · obtain ⟨k, hk⟩ := exists_chart hP' y
      have e := hs' i y j k hj hk
      exact ⟨k, hk, isUnit_of_mul_isUnit_right
        ((congrArg IsUnit ((gs_stalkMap φ y _ hj _).symm.trans e)).mp (u.map _))⟩
  refine ⟨?_, fun i => ?_⟩
  · refine top_le_iff.1 fun y _ => ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (show φ y ∈ ⨆ i, nonzeroLocus (s i) by rw [hcov]; trivial)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, by rw [loc]; exact hi⟩
  obtain ⟨haff, r, hr, hsurj⟩ := hs i
  refine ⟨by rw [loc]; exact haff.preimage φ, fun j => (φ.appLE _ _ (loc i).le).hom (r j),
    fun j k => fn_ext fun y hy => ?_, ?_⟩
  · obtain ⟨l, hl⟩ := exists_chart hP (φ y)
    have hm : φ y ∈ nonzeroLocus (s i) ⊓ H.U l := ⟨(loc i).le hy.1, hl⟩
    have e := congrArg (gs φ y _) (hr j l)
    rw [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm] at e
    have e₁ := hs' j y l k hl hy.2
    have e₂ := hs' i y l k hl hy.2
    have e₃ := (Geo.Tor.gw W (𝟙 _) y l k).mul_right_inj.1
      (e₁.symm.trans (e.trans ((congrArg _ e₂).trans (mul_left_comm _ _ _))))
    refine (gs_res _ y _ hy _).trans (e₃.trans (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_res _ y _ hy _).trans ((gs_appLE φ _ _ _ (𝟙 _) y hy.1 _).trans (by rw [Category.id_comp])))
      (gs_res _ y _ hy _)))))
  · intro x
    refine closure_eq_top h haff (loc i) (RingHom.range _) (fun d => ?_) (fun c => ?_) x
    · obtain ⟨p, rfl⟩ := hsurj d
      refine ⟨MvPolynomial.map g p, ?_⟩
      rw [MvPolynomial.eval₂Hom_map_hom, MvPolynomial.map_eval₂Hom]
      exact congrArg (fun q => MvPolynomial.eval₂Hom q _ p) (RingHom.ext fun c => (appLE_cst h _ _ _ c).symm)
    · exact ⟨MvPolynomial.C c, MvPolynomial.eval₂Hom_C _ _ _⟩

end GlobalTheory.AbLaw.VeryAmplePull
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.EvalLevel
open GlobalTheory.UT.CoefBasic

section
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S}

theorem powFrame_isGen (z : T ⟶ A)
    (e : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => 1)))
    (he : e.IsGen) (k : ℤ) : (powFrame A L z e k).IsGen := by
  intro i j
  have h := congrArg (· ^ k) (he i j)
  simp only [mul_zpow, ← map_zpow] at h
  refine h.trans (congrArg₂ (· * ·) ?_ rfl)
  simp only [LB.LinComb, Fintype.prod_unique, zpow_one]
  rfl

theorem rigT_isGen {ρ : LB.Gen (L.pull (eSec A))} (hρ : ρ.IsGen) (k : ℤ) : (rigT A L ρ T k).IsGen := by
  intro i j
  refine unit_ext fun y hy => ?_
  have v : ∀ i : Fin 1 → L.ι, y ∈ LB.wchart L (fun _ : Fin 1 => T.hom ≫ eSec A) i →
      gm (𝟙 T.left) y (LB.wchart L (fun _ : Fin 1 => T.hom ≫ eSec A) i) ((rigT A L ρ T k).s i) =
        gm T.hom y (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => i 0)) (ρ.s fun _ => i 0) ^ k := fun i hi =>
    (map_zpow _ _ _).trans (congrArg (· ^ k) (gm_rp₁ T.hom y _ _ (rigT_le A L i) hi _))
  have e := gen_trans (L := L) (φ := fun _ : PUnit.{1} => eSec A) (ε := fun _ => 1) hρ T.hom y
    (j := fun _ => i 0) (j' := fun _ => j 0) (rigT_le A L (T := T) i hy.1) (rigT_le A L (T := T) j hy.2)
  rw [trF, Fintype.prod_unique, zpow_one] at e
  refine ((gm_res (𝟙 _) y _ hy _).trans (v i hy.1)).trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_linComb L (fun _ : Fin 1 => T.hom ≫ eSec A) (fun _ => k) (𝟙 _) y i j hy.1 hy.2)
    ((gm_res (𝟙 _) y _ hy _).trans (v j hy.2)))).symm)
  rw [Fin.prod_univ_one, Category.id_comp, ← mul_zpow]
  exact congrArg (· ^ k) e

theorem ptSec_translPt (x : T ⟶ A) : ptSecT A (1 : T ⟶ A) ≫ translPt A x = x := by
  rw [ptSecT, translPt, comp_lift_assoc, lift_fst_assoc, lift_snd, Category.id_comp, ← Hom.mul_def, _root_.mul_one]

theorem ptSec_translT (x : T ⟶ A) : (ptSecT A (1 : T ⟶ A)).left ≫ (translT A x).left = (ptSecT A x).left := by
  rw [← Over.comp_left, translT, comp_lift, ptSec_translPt, ptSecT, lift_fst]; rfl

end

theorem sumV_mul {F : Type} [Field F] {v : AddValuation F (WithTop ℚ)} {Ix : Type} {x : Ix → F} {s c : F}
    (h : SumV v x s) (hc : c ≠ 0) : SumV v (fun i => c * x i) (c * s) := by
  intro q
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 (v.ne_top_iff.2 hc)
  obtain ⟨S, hS⟩ := h (q - r)
  refine ⟨S, fun T hT => ?_⟩
  rw [← Finset.mul_sum, ← mul_sub, v.map_mul, ← hr, show q = r + (q - r) by ring, WithTop.coe_add]
  exact add_le_add le_rfl (hS T hT)

theorem sumV_equiv {F : Type} [Field F] {v : AddValuation F (WithTop ℚ)} {Ix Ix' : Type} (e : Ix' ≃ Ix) {x : Ix → F} {s : F}
    (h : SumV v x s) : SumV v (fun i => x (e i)) s := by
  intro q
  obtain ⟨S, hS⟩ := h q
  refine ⟨S.map e.symm.toEmbedding, fun T hT => ?_⟩
  have := hS (T.map e.toEmbedding) fun i hi => by
    simpa using hT (Finset.mem_map_of_mem e.symm.toEmbedding hi)
  rwa [Finset.sum_map] at this

theorem exists_act_value {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {F : Type} [Field F] [Algebra (FractionRing R) F] {ρ : LB.Gen (A.L.pull (eSec A.A))} (hρ : ρ.IsGen) (N : ℕ)
    (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F))
    (e : LB.Gen (LB.LinComb A.L (Y := (TFK (R := R) F).left) (K := Fin 1) (fun _ => θ.pt.left) (fun _ => 1)))
    (he : e.IsGen) : ∃ u : F, u ≠ 0 ∧ ∀ (t t' : SecA A F N) (c : F), IsActOf A.A A.L (N : ℤ) θ t t' →
      (∀ z J, Good A.L z J → sA t (ptSecT A.A θ.pt).left z J = @id ((TFK (R := R) F).left.presheaf.stalk z)
        (cst (R := R) F z c) * (val (powFrame A.A A.L θ.pt e N) (𝟙 _) z J).val) →
      ∀ z J, Good A.L z J → sA t' (ptSecT A.A 1).left z J = @id ((TFK (R := R) F).left.presheaf.stalk z)
        (cst (R := R) F z (u * c)) * (val (rigT A.A A.L ρ (TFK (R := R) F) (N : ℤ)) (𝟙 _) z J).val := by
  have e₀ : (ptSecT A.A (1 : TFK (R := R) F ⟶ A.A)).left ≫ (snd (TFK (R := R) F) A.A).left =
      (TFK (R := R) F).hom ≫ eSec A.A := by
    rw [← Over.comp_left, ptSecT, lift_snd]; rfl
  have e₁ : (ptSecT A.A (1 : TFK (R := R) F ⟶ A.A)).left ≫ (translPt A.A θ.pt).left = θ.pt.left := by
    rw [← Over.comp_left, ptSec_translPt]
  obtain ⟨u, hu, hv⟩ := TWM.exists_ratio (F := F) A.isLB
    (LB.mulGen A.L _ _ _ _ (LB.pullGen A.L _ _ θ.φ (ptSecT A.A 1).left) (powFrame A.A A.L θ.pt e N))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ θ.isGen _) (powFrame_isGen θ.pt e he N))
    (rigT A.A A.L ρ (TFK (R := R) F) (N : ℤ)) (rigT_isGen hρ N) (fun U _ h => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg]
      exact (congrArg₂ (fun a b => h a ^ (N : ℤ) * (h b ^ (N : ℤ))⁻¹ * h θ.pt.left ^ (N : ℤ)) e₀ e₁).trans
        (inv_mul_cancel_right _ _))
  refine ⟨u, hu, fun t t' c ha ht z J hJ => ?_⟩
  have a₁ := GlobalTheory.BoxTheta.act_val θ t t' ha (ptSecT A.A 1).left z hJ
  rw [ptSec_translT] at a₁
  have a₀ := (val_pull (L := A.L) (K := Fin 2) (φ := ![(snd (TFK (R := R) F) A.A).left, (translPt A.A θ.pt).left])
    (ε := ![(N : ℤ), -(N : ℤ)]) hJ θ.φ (ptSecT A.A 1).left (𝟙 _)).trans
    (congrArg (fun r => val (L := A.L) (K := Fin 2) (φ := ![(snd (TFK (R := R) F) A.A).left, (translPt A.A θ.pt).left])
      (ε := ![(N : ℤ), -(N : ℤ)]) θ.φ r z J) (Category.id_comp _))
  have a₂ := ((Units.val_mul _ _).symm.trans (congrArg Units.val ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) a₀ rfl)).symm)).trans (hv _ (𝟙 _) z J hJ)
  have a₃ := ht z J hJ
  have a₄ : cst (R := R) F z (u * c) = cst (R := R) F z u * cst (R := R) F z c := by
    rw [cst_eq, cst_eq, cst_eq, map_mul]
  refine a₁.trans ((congrArg _ a₃).trans ?_)
  rw [a₄]
  refine (mul_left_comm _ _ _).trans ((congrArg _ a₂).trans ?_)
  exact (_root_.mul_assoc _ _ _).symm.trans (congrArg₂ (fun a b : (TFK (R := R) F).left.presheaf.stalk z => a * b) (_root_.mul_comm _ _) rfl)

theorem value_at_level : LL → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (N : ℕ), 1 ≤ N → ∀ (q : QkPt D.toPre F N) (x : TFK (R := V) F ⟶ A.A), QkToAkU U.toUnifPre F N q x → ∀ e : LB.Gen (LB.LinComb A.L (Y := (TFK (R := V) F).left) (K := Fin 1) (fun _ => x.left) (fun _ => 1)), e.IsGen → ∀ w : Frm D.toPre F N q.g.b, w.IsGen → ∃ κ : F, κ ≠ 0 ∧ ∀ (t : SecA A F N) s (c : F), U.ExpandsF F N w₀ t s → (∀ z J, Good A.L z J → sA t (ptSecT A.A x).left z J = @id ((TFK (R := V) F).left.presheaf.stalk z) (cst (R := V) F z c) * (val (powFrame A.A A.L x e N) (𝟙 _) z J).val) → SumV v (coef s q.g w) (κ * c) := by
  intro hL V _ _ _ _ hcpl ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ ρ hN N hN1 q x hx e he w hw
  have hB : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hcpl⟩
  haveI : Subsingleton (TFK (R := V) F).left := inferInstanceAs (Subsingleton (Spec (CommRingCat.of F)))
  haveI : Nonempty (TFK (R := V) F).left := inferInstanceAs (Nonempty (Spec (CommRingCat.of F)))
  obtain ⟨hxN, hθ⟩ := hx w₀ hN.1
  obtain ⟨θ, rfl⟩ := GlobalTheory.BoxTheta.exists_theta hL.1.kerPow A hN1 (T := TFK (R := V) F) x hxN
  obtain ⟨w', hw', hΦ⟩ := hθ θ rfl
  obtain ⟨u, hu, hval⟩ := exists_act_value hN.2.1 N θ e he
  obtain ⟨o, ho⟩ := exists_zero_gt (D := D.toPre) (F := F)
  obtain ⟨w₁, hw₁⟩ := (coef_basic V D.toPre F N o).2.1 ho.1
  have hadd : o.IsAdd q.g q.g := by
    rw [GlobalTheory.TorusExt.isZero_unique ho GlobalTheory.TorusExt.isZero_gtZero]
    have := GlobalTheory.TorusExt.isAdd_gtAdd (GlobalTheory.TorusExt.gtZero D.toPre F) q.g
    rwa [GlobalTheory.TorusExt.gtZero_add] at this
  obtain ⟨ω, hω, -, hc⟩ := GlobalTheory.UT.CoefPhi.coef_phi hL V _ hB D F N hN1 q w' hw' o q.g hadd w₁ hw₁.1
  obtain ⟨d, hd, -, hdc⟩ := ((coef_basic V D.toPre F N q.g).2.2 ω hω).2.2.1 w hw
  refine ⟨d * u, mul_ne_zero hd hu, fun t s c hts hc' => ?_⟩
  obtain ⟨t', ht'⟩ := GlobalTheory.VVRank.exists_isTwistPull A.A (ψ := translT A.A θ.pt) (m := translPt A.A θ.pt)
    (hm := lift_snd _ _) (a := N) (b := N) (α := θ.φ) A.isLB θ.isGen t
  obtain ⟨s', hs', -⟩ := ((GlobalTheory.UT.expBijF_and_expandsF_lin hL V _ hB D A G hG U).1 F N hN1 w₀ hN.1).1 t'
  have h₁ := (GlobalTheory.UT.EvalZero.value_at_origin hL V _ hB D A G hG U F).2.2 w₀ ρ hN N t' s' hs' o w₁ ho hw₁ (u * c)
    (hval t t' c ht' hc')
  have h₂ := sumV_equiv (Equiv.addRight q.y) (GlobalTheory.UT.AdicValSum.main V ϖ hϖ F v hv _ _ _ h₁).1
  have h₃ := hc 1 N le_rfl (Nat.mul_one N).symm q (one_nsmul _).symm rfl w' w₁ ω ⟨hw', fun _ _ _ => (pow_one _).symm⟩
    ⟨hw₁.1, fun _ _ _ => (pow_one _).symm⟩ ⟨hω, fun _ _ _ => (pow_one _).symm⟩ s s' (hΦ t t' s s' hts hs' ht')
  have h₄ := sumV_mul h₂ hd
  simp only [Equiv.coe_addRight, h₃, ← hdc] at h₄
  rw [_root_.mul_assoc]
  exact h₄

end GlobalTheory.UT.EvalLevel
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory

namespace EndConst

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

def Acts (g : GtCoord I D e G) (a : (thickObj R I e G).left ⟶ (thickObj R I e G).left)
    (f : D.X → D.X) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι),
    Good D.P.L z J → r ≫ g.pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D.P.A →
    ∀ x, val (g.t x) (r ≫ a) z J = val (g.t (f x)) r z J

theorem acts_of_torusEndOf (g : GtCoord I D e G) (a : thickObj R I e G ⟶ thickObj R I e G)
    {f : D.X → D.X} {t : splitTorus _ D.X ⟶ splitTorus _ D.X} (ht : TorusEndOf D.X f t)
    (hi : g.i ≫ a = t ≫ g.i) : Acts g a.left f := by
  intro Z r z J hJ h x
  let FinalForm : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) :=
    Over.mk (r ≫ (thickObj R I e G).hom)
  let b : FinalForm ⟶ thickObj R I e G := Over.homMk r rfl
  let τ := g.isKernel.lift b (toUnit _) ((CharAgree.comp_q_eq_one_iff g b).2 h)
  have hτ : τ ≫ g.i = b := g.isKernel.lift_fst _ _ _
  have hτ' : (τ ≫ t) ≫ g.i = b ≫ a := by rw [Category.assoc, ← hi, ← Category.assoc, hτ]
  have k := (TorusCoord.val_torus_point_and_translate R I D e G g FinalForm (τ ≫ t) 1 z J hJ x).1
  have k' := (TorusCoord.val_torus_point_and_translate R I D e G g FinalForm τ 1 z J hJ (f x)).1
  rw [hτ'] at k
  rw [hτ] at k'
  refine k.trans (Eq.trans (Units.ext ?_) k'.symm)
  rw [gm_val _ _ ⊤ trivial, gm_val _ _ ⊤ trivial]
  refine congrArg (FinalForm.left.presheaf.germ ⊤ z trivial).hom ?_
  exact (SplitTorusHom.appTop_comp τ t _).trans
    (congrArg τ.left.appTop.hom ((EndTorus.torusEndOf_iff_appTop _ _).1 ht x))

theorem acts_unique [IsAdicComplete I R] (g : GtCoord I D e G)
    {a : (thickObj R I e G).left ⟶ (thickObj R I e G).left} {f f' : D.X → D.X}
    (h : Acts g a f) (h' : Acts g a f') : f = f' := by
  funext x
  have := EndTorus.connectedSpace_thickening I e
  refine SplitTorusHom.charUnit_injective (S := Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))
    (congrArg Units.val (unit_ext fun z _ => ?_))
  choose J hJ using fun ψ : (splitTorus _ D.X).left ⟶ D.P.A.left => exists_chart D.P.isLB (ψ z)
  have c := (CharAgree.comp_q_eq_one_iff g g.i).1 g.isKernel.w
  have k := fun χ =>
    (TorusCoord.val_torus_point_and_translate R I D e G g _ (𝟙 _) 1 z J hJ χ).1
  simp only [Category.id_comp] at k
  exact (k _).symm.trans (((h _ _ z J hJ c x).symm.trans (h' _ _ z J hJ c x)).trans (k _))


omit [IsDomain R] [GrpObj G] [IsCommMonObj G] in
theorem thickMap_comm (aG : G ⟶ G) (e : ℕ) :
    thickMap R I e G ≫ ((Over.pullback (thick R I (e + 1))).map aG).left =
      ((Over.pullback (thick R I e)).map aG).left ≫ thickMap R I e G := by
  apply pullback.hom_ext <;>
    simp [thickMap, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
      pullback.lift_snd_assoc]

theorem acts_down {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    (U : UnifPre I D A G) (aG : G ⟶ G) {f : D.toPre.X → D.toPre.X}
    (h : Acts (U.gt (e + 1)) ((Over.pullback (thick R I (e + 1))).map aG).left f) :
    Acts (U.gt e) ((Over.pullback (thick R I e)).map aG).left f := by
  intro Z r z J hJ c x
  have t : thickMap R I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have up : (r ≫ thickMap R I e G) ≫ (U.gt (e + 1)).pG.left =
      (r ≫ thickMap R I e G) ≫ (fstG I (e + 1) G).left ≫ G.hom ≫ eSec D.toPre.P.A := by
    refine (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) (U.gt_q e)).trans (c.trans ?_))
    refine Eq.trans (congrArg (r ≫ ·) ?_) (Category.assoc _ _ _).symm
    exact (congrArg (· ≫ G.hom ≫ eSec D.toPre.P.A) t.symm).trans (Category.assoc _ _ _)
  have k := h Z (r ≫ thickMap R I e G) z J hJ up x
  have sq : (r ≫ thickMap R I e G) ≫ ((Over.pullback (thick R I (e + 1))).map aG).left =
      (r ≫ ((Over.pullback (thick R I e)).map aG).left) ≫ thickMap R I e G := by
    rw [Category.assoc, Category.assoc, thickMap_comm]
  rw [sq] at k
  exact (val_corr hJ (U.gt_t e x) _).symm.trans ((val_pull hJ _ _ _).trans (k.trans
    ((val_pull hJ _ _ _).symm.trans (val_corr hJ (U.gt_t e (f x)) r))))

end EndConst


open EndConst in
theorem unifPre_end_character_const : LL → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (aG : G ⟶ G), IsMonHom aG → ∃ h : D.toPre.X →+ D.toPre.X, ∀ e, ∃ t : splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.toPre.X ⟶ splitTorus _ D.toPre.X, TorusEndOf D.toPre.X h t ∧ (U.gt e).i ≫ (Over.pullback (thick R I e)).map aG = t ≫ (U.gt e).i := by
  intro hL R _ _ I hR D A G _ _ U aG haG
  have ex := fun e => (gtCoord_end_torus_abelian hL R I hR D.toPre e G (U.gt e)
    ((Over.pullback (thick R I e)).map aG) inferInstance).1.exists
  choose h t ht hi using ex
  obtain ⟨-, -, -, hC⟩ := hR
  have down : ∀ (e : ℕ) (f : D.toPre.X → D.toPre.X),
      Acts (U.gt e) ((Over.pullback (thick R I e)).map aG).left f →
      Acts (U.gt 0) ((Over.pullback (thick R I 0)).map aG).left f := by
    intro e f
    induction e with
    | zero => exact id
    | succ e ih => exact fun k => ih (acts_down U aG k)
  refine ⟨h 0, fun e => ⟨t e, ?_, hi e⟩⟩
  rw [← acts_unique _ (down e _ (acts_of_torusEndOf _ _ (ht e) (hi e)))
    (acts_of_torusEndOf _ _ (ht 0) (hi 0))]
  exact ht e

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT
open GlobalTheory.TorusExt

theorem isTor_iff {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    (t : Multiplicative D.X →* Fˣ) (g : GtPtF D F) :
    IsTor t g ↔ IsTorusPtF g fun χ => t (Multiplicative.ofAdd χ) := by
  rw [isTorusPtF_iff_val]
  refine and_congr Iff.rfl (forall_congr' fun χ => forall_congr' fun y => forall_congr' fun J => forall_congr' fun _ => ?_)
  have e : ∀ x : F, cst (R := R) F y x = stalkConst (F := F) y x := fun x =>
    gs_eq (𝟙 _) y ⊤ trivial _
  rw [e]

theorem gt_onto_divisible_kernel : LL → AllD fun {R} _ _ {I} D F _ _ => (∀ b : TF (R := R) F ⟶ D.toPre.P.A, ∃ g : GtPtF D.toPre F, g.b = b) ∧ (∀ n, 1 ≤ n → ∀ g : GtPtF D.toPre F, ∃ g', GtPtF.IsNsmul n g' g) ∧ (∀ t, ∃! g : GtPtF D.toPre F, IsTor t g) ∧ (∀ g : GtPtF D.toPre F, g.b = 1 → ∃! t, IsTor t g) ∧ ∀ t t' (g g' g'' : GtPtF D.toPre F), IsTor t g → IsTor t' g' → (g.IsAdd g' g'' ↔ IsTor (t * t') g'') := by
  intro hL R _ _ _ I hA D F _ _ _
  refine ⟨exists_lift, fun n hn g => ?_, fun t => ?_, fun g hb => ?_, fun t t' g g' g'' h h' => ?_⟩
  · letI := gtGroup D.toPre F
    exact (exists_nsmul_eq hL.1.mulN (Or.inl hA.1) (by omega) g).imp fun _ e => (isNsmul_iff_eq _ _ _).2 e.symm
  · exact ⟨_, (isTor_iff _ _).2 (isTorusPtF_torusPt t), fun g h => (isTorusPtF_iff_eq g t).1 ((isTor_iff _ _).1 h)⟩
  · obtain ⟨t, ht⟩ := exists_isTorusPtF_of_b hb
    refine ⟨t, (isTor_iff _ _).2 ht, fun t' ht' => MonoidHom.ext fun χ => Units.ext ?_⟩
    exact congrFun (((isTor_iff _ _).1 ht').fun_unique ht) χ.toAdd
  · letI := gtGroup D.toPre F
    have a := ((isTor_iff _ _).1 h).add ((isTor_iff _ _).1 h')
    rw [isTor_iff]
    exact (isAdd_iff_eq _ _ _).trans ⟨fun e => e ▸ a, fun e => e.unique a⟩

end GlobalTheory.UT
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
theorem _root_.GlobalTheory.T.inducesFrobeniusOnSections_translation_iff_image : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (N : ℕ), 1 ≤ N → ∀ (p : QkPt D.toPre F N) (x : TFK (R := R) F ⟶ A.A), IndAt U.toUnifPre F N p (translT A.A x) ↔ QkToAkU U.toUnifPre F N p x := by
  first | exact @GlobalTheory.UT.indAt_translT_iff | exact GlobalTheory.UT.indAt_translT_iff | (intros; apply GlobalTheory.UT.indAt_translT_iff <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
theorem _root_.GlobalTheory.T.weilQkIs_iff_commutatorPairing_torsion : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (k : ℕ), 1 ≤ k → ∀ (p p' : QkPt D.toPre F k) x x', QkToAkU U.toUnifPre F k p x → QkToAkU U.toUnifPre F k p' x' → ∀ ζ : Fˣ, WeilQkIs D.toPre F k p p' ζ ↔ WeilIs A.A A.L k x x' (unitOn ζ) := by
  first | exact @GlobalTheory.UT.weilQkIs_iff_weilIs | exact GlobalTheory.UT.weilQkIs_iff_weilIs | (intros; apply GlobalTheory.UT.weilQkIs_iff_weilIs <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

theorem _root_.GlobalTheory.T.qkToAkU_iff_galois_equivariant : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (F' : Type) [Field F'] [IsAlgClosed F'] [Algebra (FractionRing R) F'] (σ : F →ₐ[FractionRing R] F') (k : ℕ), 1 ≤ k → ∀ (p : QkPt D.toPre F k) (p' : QkPt D.toPre F' k) (x : TFK (R := R) F ⟶ A.A) (x' : TFK (R := R) F' ⟶ A.A), QkExt σ.toRingHom p p' → x'.left = spMap σ.toRingHom ≫ x.left → (QkToAkU U.toUnifPre F k p x ↔ QkToAkU U.toUnifPre F' k p' x') := by
  first | exact @GlobalTheory.TorsionExt.qkToAkU_iff_of_qkExt | exact GlobalTheory.TorsionExt.qkToAkU_iff_of_qkExt | (intros; apply GlobalTheory.TorsionExt.qkToAkU_iff_of_qkExt <;> assumption)
end
