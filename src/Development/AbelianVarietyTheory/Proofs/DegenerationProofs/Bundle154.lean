module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstOfNormPeriodic
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle006
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle133
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionOfIsPushout
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch GlobalTheory.ArcPull GlobalTheory.FrameValue

noncomputable section
namespace GlobalTheory.Ex.Arch.FibRos

theorem exists_ros_down {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] [IsCommMonObj A]
    [IsCommMonObj A'] {f : S' ⟶ S} {Φ : A'.left ⟶ A.left} {L : LB A.left} {L' : LB A'.left}
    (gp : IsGrpPullback A' A f Φ) (hL : L.IsLB) (hL' : L'.IsLB)
    {w : LB.Iso L' (L.pull Φ)} (hw : w.IsGen) {a b : A ⟶ A} {a' b' : A' ⟶ A'}
    (a₁ : (1 : 𝟙_ (Over S') ⟶ A') ≫ a' = 1) (b₁ : (1 : 𝟙_ (Over S') ⟶ A') ≫ b' = 1)
    (ha : a'.left ≫ Φ = Φ ≫ a.left) (hb : b'.left ≫ Φ = Φ ≫ b.left)
    {r : LB.Gen (LB.LinComb L (rosatiφ A a b) rosatiε)} (hr : TorusExt.IsRos L a b r) :
    ∃ t : LB.Gen (LB.LinComb L' (rosatiφ A' a' b') rosatiε), TorusExt.IsRos L' a' b' t ∧
      ∀ {T' : Over S'} (x' y' : T' ⟶ A') (m : T'.left ⟶ (A ⊗ A).left), x'.left ≫ Φ = m ≫ (fst A A).left →
        y'.left ≫ Φ = m ≫ (snd A A).left → ∀ (z : T'.left) J J', Good L z J → Good L' z J' →
        val r m z J = (∏ k, om w z J J' ((lift x' y').left ≫ rosatiφ A' a' b' k) ^ rosatiε k) *
          val t (lift x' y').left z J' := by
  let Φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left := (lift (pushPt gp.1.w (fst A' A')) (pushPt gp.1.w (snd A' A'))).left
  have f₁ : (fst A' A').left ≫ Φ = Φ₂ ≫ (fst A A).left :=
    (congrArg (fun q => q.left) (lift_fst (pushPt gp.1.w (fst A' A')) (pushPt gp.1.w (snd A' A')))).symm
  have f₂ : (snd A' A').left ≫ Φ = Φ₂ ≫ (snd A A).left :=
    (congrArg (fun q => q.left) (lift_snd (pushPt gp.1.w (fst A' A')) (pushPt gp.1.w (snd A' A')))).symm
  have f₃ : (fst A' A' ≫ a').left ≫ Φ = Φ₂ ≫ (fst A A ≫ a).left := by
    rw [Over.comp_left, Over.comp_left, Category.assoc, ha, ← Category.assoc, f₁, Category.assoc]
  have f₄ : (snd A' A' ≫ b').left ≫ Φ = Φ₂ ≫ (snd A A ≫ b).left := by
    rw [Over.comp_left, Over.comp_left, Category.assoc, hb, ← Category.assoc, f₂, Category.assoc]
  have hψ : ∀ i, rosatiφ A' a' b' i ≫ Φ = Φ₂ ≫ rosatiφ A a b i := fun i => by
    fin_cases i
    exacts [mul_push gp Φ₂ f₃ f₂, f₃, f₂, mul_push gp Φ₂ f₁ f₄, f₁, f₄]
  have cmp : ∀ {T' : Over S'} (x' y' : T' ⟶ A') (m : T'.left ⟶ (A ⊗ A).left), x'.left ≫ Φ = m ≫ (fst A A).left →
      y'.left ≫ Φ = m ≫ (snd A A).left → (lift x' y').left ≫ Φ₂ = m := fun x' y' m hx hy => by
    apply pullback.hom_ext
    · refine Eq.trans ?_ hx
      refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) f₁.symm).trans ?_)
      rw [← Category.assoc, ← Over.comp_left, lift_fst]
    · refine Eq.trans ?_ hy
      refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) f₂.symm).trans ?_)
      rw [← Category.assoc, ← Over.comp_left, lift_snd]
  obtain ⟨t, ht, vt⟩ := exists_down_om hw hL hL' Φ₂ hψ r hr.1
  refine ⟨t, ⟨ht, corr_of_val hL' fun y I' hI' => ?_⟩, fun x' y' m hx hy z J J' hJ hJ' => ?_⟩
  · obtain ⟨I, hI⟩ := DegPull.exists_good' hL y
    have o : lift (1 : 𝟙_ (Over S') ⟶ A') (1 : 𝟙_ (Over S') ⟶ A') = lift η[A'] η[A'] := by simp [Hom.one_def]
    have he : eSec A' ≫ Φ = f ≫ eSec A := (cubeMapOf gp).e_comm
    have o₁ : (1 : 𝟙_ (Over S') ⟶ A').left = eSec A' := Category.id_comp _
    have e := vt _ (lift (1 : 𝟙_ (Over S') ⟶ A') (1 : 𝟙_ (Over S') ⟶ A')).left y I I' hI hI'
    rw [prod_ros, cmp 1 1 (f ≫ zero2 A) (by
        rw [o₁, he, Category.assoc, ← Over.comp_left, lift_fst]; rfl) (by
        rw [o₁, he, Category.assoc, ← Over.comp_left, lift_snd]; rfl),
      a₁, b₁, _root_.mul_one, o] at e
    have e₁ := (val_pull hI _ _ _).symm.trans ((val_corr hI hr.2 f).trans (val_one _))
    rw [e₁] at e
    rw [val_pull hI', val_one, Category.id_comp]
    simpa using e.symm
  · have e := vt _ (lift x' y').left z J J' hJ hJ'
    rwa [cmp x' y' m hx hy] at e

theorem stalkUnits_symm_gm {F : Type} [Field F] {X : Scheme.{0}} (x : Sp F ⟶ X) (U : X.Opens) (z : Sp F) (h : x z ∈ U)
    (a : Γ(X, U)ˣ) : (((TorusExt.stalkUnits z).symm (gm x z U a) : Fˣ) : F) = valF x U a.val := by
  refine (TorusExt.stalkConst z).injective ?_
  rw [← TorusExt.stalkUnits_val, MulEquiv.apply_symm_apply]
  exact (toStk_valF x U z h a).symm

theorem vF_eq_genVal {X Y Y' : Scheme.{0}} {L : LB X} {A : Over (Sp ℂ)} [GrpObj A] {L' : LB A.left} {g : ℕ}
    {u : HolUnif A L' g} (hL' : L'.IsLB) {Φ : A.left ⟶ X} {w : LB.Iso L' (L.pull Φ)} {J : (Sp ℂ ⟶ X) → L.ι}
    (hJ : ∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ)) {fr : (Fin g → ℂ) → ℂˣ}
    (hfr : ∀ z i, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L'.U i →
      (fr z : ℂ) = valAt' (u.ex z).left _ (w.s (fun _ => J ((u.ex z).left ≫ Φ), i)).val * u.fr i z)
    {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ A.left)} {ε : K → ℤ}
    (r : LB.Gen (LB.LinComb L φ ε)) {t : LB.Gen (LB.LinComb L' φ' ε)} (ht : t.IsGen) (m : Sp ℂ ⟶ Y) {y : Sp ℂ ⟶ Y'}
    {z : K → Fin g → ℂ} (hz : IsLift u φ' y z)
    (h : ∀ (p : Sp ℂ) J', Good L' p J' → val r m p J = (∏ k, om w p J J' (y ≫ φ' k) ^ ε k) * val t y p J') :
    vF r m J = genVal u hL' t y z * ((∏ k, fr (z k) ^ ε k : ℂˣ) : ℂ) := by
  let p : Sp ℂ := IsLocalRing.closedPoint ℂ
  have gJ : Good L p J := fun ψ => hJ ψ trivial
  have gJ' : Good L' p (chartAt hL') := fun ψ => le_chartAt hL' ψ trivial
  have e := congrArg (fun q => (((TorusExt.stalkUnits p).symm q : ℂˣ) : ℂ)) (h p _ gJ')
  simp only [map_mul, map_prod, map_zpow, Units.val_mul, Units.coe_prod, Units.val_zpow_eq_zpow_val] at e ⊢
  have e₁ : (((TorusExt.stalkUnits p).symm (val r m p J) : ℂˣ) : ℂ) = vF r m J :=
    stalkUnits_symm_gm _ _ p (gJ.mem φ m) _
  have e₂ : (((TorusExt.stalkUnits p).symm (val t y p (chartAt hL')) : ℂˣ) : ℂ) =
      genVal u hL' t y z * GlobalTheory.FrameValue.frameProd u ε z fun k => GlobalTheory.FrameValue.chartAt hL' (y ≫ φ' k) :=
    (stalkUnits_symm_gm _ _ p (gJ'.mem φ' y) _).trans (valAt'_gen hL' ht hz (le_wchart_chartAt hL' φ' y))
  rw [e₁, e₂, mul_left_comm, GlobalTheory.FrameValue.frameProd, ← Finset.prod_mul_distrib] at e
  refine e.trans (congrArg _ (Finset.prod_congr rfl fun k _ => ?_))
  rw [← mul_zpow, hz k, hfr _ _ (le_chartAt hL' _)]
  refine congrArg (fun q => (q * _) ^ ε k) ?_
  have hm : (u.ex (z k)).left p ∈ (L.pull Φ).U (fun _ => J ((u.ex (z k)).left ≫ Φ)) ⊓
      L'.U (chartAt hL' (u.ex (z k)).left) := ⟨mem_pull.2 (gJ ((u.ex (z k)).left ≫ Φ)), gJ' _⟩
  exact stalkUnits_symm_gm _ _ p hm _

theorem fibRosSt : Laws → FibRosSt := by
  rintro - R _ _ _ D J g Λ Hm χ ex fr ⟨hJ, P', φ, w, u, hΛ, gp, hw, hAH, -, -, -, hex, hfr⟩ f f' - - F G hF hG r hr
  have down : ∀ (a : D.P.A ⟶ D.P.A) (H : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ z, ex (H z) = ex z ≫ a) →
      ∃ a' : P'.A ⟶ P'.A, a'.left ≫ φ = φ ≫ a.left ∧ (∀ z, u.ex (H z) = u.ex z ≫ a') ∧
        (1 : 𝟙_ (Over (Sp ℂ)) ⟶ P'.A) ≫ a' = 1 := fun a H hH => by
    let a' : P'.A ⟶ P'.A := Over.homMk (gp.1.lift (φ ≫ a.left) P'.A.hom
      (by rw [Category.assoc, Over.w, gp.1.w])) (gp.1.lift_snd _ _ _)
    have ha : a'.left ≫ φ = φ ≫ a.left := gp.1.lift_fst _ _ _
    have hu : ∀ z, u.ex (H z) = u.ex z ≫ a' := fun z =>
      Over.OverMorphism.ext (gp.1.hom_ext (by
        rw [← hex, hH, Over.comp_left, Over.comp_left, hex, Category.assoc, Category.assoc, ha]) (by rw [Over.w, Over.w]))
    refine ⟨a', ha, hu, ?_⟩
    have h0 : u.ex 0 = 1 := (u.ker 0).2 (zero_mem _)
    rw [← h0, ← hu, map_zero]
  obtain ⟨a, ha, ua, a₁⟩ := down f F hF
  obtain ⟨b, hb, ub, b₁⟩ := down f' G hG
  obtain ⟨t, ht, vt⟩ := exists_ros_down gp D.P.isLB P'.isLB hw a₁ b₁ ha hb (r := r) hr
  obtain ⟨adj, one⟩ := genVal_rosati P'.isLB hAH ua ub t ht.1 ht.2
  refine ⟨adj, fun x z => ?_⟩
  have e := vF_eq_genVal P'.isLB hJ (fun z i hi => by rw [← hex]; exact hfr z i hi) r ht.1 (lift (ex x) (ex z)).left
    (isLift_rosati ua ub x z) (fun p J' hJ' => vt (u.ex x) (u.ex z) _
      ((hex x).symm.trans (congrArg (fun q => q.left) (lift_fst (ex x) (ex z)).symm))
      ((hex z).symm.trans (congrArg (fun q => q.left) (lift_snd (ex x) (ex z)).symm)) p J J'
      (fun ψ => hJ ψ trivial) hJ')
  rw [e, one, _root_.one_mul]
  simp only [Fin.prod_univ_six, rosatiLift, rosatiε, Matrix.cons_val, zpow_neg, zpow_one, Units.val_mul,
    Units.val_inv_eq_inv_val]
  field_simp

end GlobalTheory.Ex.Arch.FibRos
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

namespace GlobalTheory.FiniteDVRValuation

section
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)}


open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing in
open scoped CategoryTheory.Obj BigOperators in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)} in
theorem _root_.GlobalTheory.FiniteDVRValuation.exists_nat_val (hϖ : Irreducible ϖ) (hv : _root_.ReciprocityTheory.ChartRestriction.G.DVR.ValOver ϖ F v) {c : V}
    (hc : c ≠ 0) :
    ∃ n : ℕ, v (algebraMap (FractionRing V) F (algebraMap V (FractionRing V) c)) =
        ((n : ℚ) : WithTop ℚ) ∧ (n = 0 → IsUnit c) := by
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
  refine ⟨n, ?_, fun hn => by subst hn; simp⟩
  rw [hv _ n ⟨u, by rw [zpow_natCast, map_mul, map_pow, mul_comm]⟩]
  norm_cast

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing in
open scoped CategoryTheory.Obj BigOperators in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)} in
theorem _root_.GlobalTheory.FiniteDVRValuation.val_nonneg (hϖ : Irreducible ϖ) (hv : _root_.ReciprocityTheory.ChartRestriction.G.DVR.ValOver ϖ F v) (c : V) :
    0 ≤ v (algebraMap (FractionRing V) F (algebraMap V (FractionRing V) c)) := by
  by_cases hc : c = 0
  · subst hc
    simp
  · obtain ⟨n, hn, -⟩ := _root_.GlobalTheory.FiniteDVRValuation.exists_nat_val hϖ hv hc
    rw [hn]
    exact_mod_cast n.cast_nonneg

end

def nonnegSubring {F K : Type} [Field F] [Field K] (v : AddValuation F (WithTop ℚ)) (e : K →+* F) :
    ValuationSubring K where
  carrier := {x | 0 ≤ v (e x)}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_mul, AddValuation.map_mul] at *
    exact add_nonneg ha hb
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_add (f := _)] at *
    exact v.map_le_add ha hb
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, map_neg, AddValuation.map_neg] at *
    exact ha
  mem_or_inv_mem' := by
    intro x
    simp only [Set.mem_setOf_eq]
    by_cases hx : x = 0
    · left; simp [hx]
    by_contra hcon
    push_neg at hcon
    have h1 : v (e x) + v (e x⁻¹) = 0 := by
      rw [← AddValuation.map_mul, ← map_mul, mul_inv_cancel₀ hx, map_one, AddValuation.map_one]
    have h2 : v (e x) + v (e x⁻¹) < 0 := by
      calc v (e x) + v (e x⁻¹) ≤ 0 + v (e x⁻¹) := by gcongr; exact hcon.1.le
        _ = v (e x⁻¹) := zero_add _
        _ < 0 := hcon.2
    exact h2.ne h1

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing in
open scoped CategoryTheory.Obj BigOperators in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.FiniteDVRValuation.main :
    ∀ (W W' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CommRing W']
      [IsDomain W'] [IsDiscreteValuationRing W'] (i : W →+* W'), Function.Injective i →
      i.Finite → ∀ (ϖ : W'), Irreducible ϖ → ∀ (F : Type) [Field F]
      [Algebra (FractionRing W') F] (v : AddValuation F (WithTop ℚ)), _root_.ReciprocityTheory.ChartRestriction.G.DVR.ValOver ϖ F v →
      (∀ r : W', 0 ≤ v (algebraMap (FractionRing W') F (algebraMap W' _ r))) ∧
      (∃ i' : FractionRing W →+* FractionRing W',
        (∀ r, i' (algebraMap W _ r) = algebraMap W' _ (i r)) ∧
        ∀ a : FractionRing W, v (algebraMap (FractionRing W') F (i' a)) = 0 →
          ∃ u : Wˣ, algebraMap W (FractionRing W) u = a) ∧
      ∀ (K : Type) [Field K] (e : K →+* F), ∃ S : ValuationSubring K,
        ∀ x, (x ∈ S ↔ 0 ≤ v (e x)) ∧ (S.valuation x = 1 → v (e x) = 0) := by
  intro W W' _ _ _ _ _ _ i hi hfin ϖ hϖ F _ _ v hv
  refine ⟨fun r => _root_.GlobalTheory.FiniteDVRValuation.val_nonneg hϖ hv r, ?_,
    fun K _ e => ⟨_root_.GlobalTheory.FiniteDVRValuation.nonnegSubring v e, fun x => ⟨Iff.rfl, fun h => ?_⟩⟩⟩
  · have hinj : Function.Injective ((algebraMap W' (FractionRing W')).comp i) :=
      (IsFractionRing.injective W' (FractionRing W')).comp hi
    have hunit : ∀ x : W,
        v (algebraMap (FractionRing W') F (algebraMap W' _ (i x))) = 0 → IsUnit x := by
      intro x hx
      by_contra hxu
      have hx0 : x ≠ 0 := by
        rintro rfl
        simp at hx
      have hmax := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' i hfin.to_isIntegral
        (IsLocalRing.maximalIdeal W')
      have hcomap : (IsLocalRing.maximalIdeal W').comap i = IsLocalRing.maximalIdeal W :=
        IsLocalRing.eq_maximalIdeal hmax
      have hmem : x ∈ (IsLocalRing.maximalIdeal W').comap i := by
        rw [hcomap]
        exact (IsLocalRing.mem_maximalIdeal x).2 hxu
      have hix : ¬IsUnit (i x) := (IsLocalRing.mem_maximalIdeal _).1 (Ideal.mem_comap.1 hmem)
      have hle := (_root_.ReciprocityTheory.ChartRestriction.G.DVR.TWO.v_of_V v hϖ hv (i x)).2 hix ((map_ne_zero_iff i hi).2 hx0)
      have hle' : (1 : WithTop ℚ) ≤ 0 := by
        rw [← hx]
        exact hle
      exact absurd hle' (by norm_num)
    refine ⟨IsFractionRing.lift hinj, fun r => IsFractionRing.lift_algebraMap hinj r,
      fun a ha => ?_⟩
    by_cases ha0 : a = 0
    · subst ha0
      simp at ha
    rcases ValuationRing.isInteger_or_isInteger W a with ⟨x, hx⟩ | ⟨x, hx⟩
    · subst hx
      rw [IsFractionRing.lift_algebraMap, RingHom.comp_apply] at ha
      exact ⟨(hunit x ha).unit, rfl⟩
    · have hinv : v (algebraMap (FractionRing W') F (IsFractionRing.lift hinj a⁻¹)) = 0 := by
        have hsum : v (algebraMap (FractionRing W') F (IsFractionRing.lift hinj a)) +
            v (algebraMap (FractionRing W') F (IsFractionRing.lift hinj a⁻¹)) = 0 := by
          rw [← AddValuation.map_mul, ← map_mul, ← map_mul, mul_inv_cancel₀ ha0, map_one, map_one,
            AddValuation.map_one]
        rwa [ha, zero_add] at hsum
      rw [← hx, IsFractionRing.lift_algebraMap, RingHom.comp_apply] at hinv
      refine ⟨(hunit x hinv).unit⁻¹, ?_⟩
      rw [← inv_inv a, ← hx, map_units_inv, IsUnit.unit_spec]
  · have hx0 : x ≠ 0 := by
      rintro rfl
      simp at h
    have h1 : x ∈ _root_.GlobalTheory.FiniteDVRValuation.nonnegSubring v e := (ValuationSubring.valuation_le_one_iff _ _).1 h.le
    have h2 : x⁻¹ ∈ _root_.GlobalTheory.FiniteDVRValuation.nonnegSubring v e :=
      (ValuationSubring.valuation_le_one_iff _ _).1 (by rw [map_inv₀, h, inv_one])
    change 0 ≤ v (e x) at h1
    change 0 ≤ v (e x⁻¹) at h2
    have hsum : v (e x) + v (e x⁻¹) = 0 := by
      rw [← AddValuation.map_mul, ← map_mul, mul_inv_cancel₀ hx0, map_one, AddValuation.map_one]
    exact le_antisymm (le_add_of_nonneg_right h2 |>.trans_eq hsum) h1

end GlobalTheory.FiniteDVRValuation
end
