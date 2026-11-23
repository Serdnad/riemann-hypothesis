module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle049
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SymmetricLiftOddOrderExistsUnique
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ThetaGrpActsLinearly
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle067
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.ThetaReal

open CommPairing GlobalLift VVRank ThetaCoord

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S}

theorem exists_symLift_one (hL : L.IsLB) {k : ℤ} {ν : LB.Gen (negLB A L k T)} (hν : ν.IsGen) :
    ∃ θ : ThetaGrp A L k T, SymLift A L k 1 1 θ ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J → tval θ r z J = 1 := by
  have h1 : (LB.oneGen L (Y := (T ⊗ A).left)).IsGen := SymLiftOdd.isGen_of_gm fun y j j' _ _ => by
    rw [trF, Fintype.prod_empty, _root_.one_mul]
    exact (map_one _).trans (map_one _).symm
  obtain ⟨t, ht, hv⟩ := exists_gen hL (φ' := ![(snd T A).left, (translPt A (1 : T ⟶ A)).left]) (ε' := ![k, -k])
    (fun U _ f => by
      rw [Fintype.prod_empty, Fin.prod_univ_two, ThetaAct.translPt_one]
      simp) (LB.oneGen L) h1
  have hv' : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J →
      tval (⟨1, t, ht⟩ : ThetaGrp A L k T) r z J = 1 := fun Z r z J hJ => (hv Z r z J hJ).trans (val_one _)
  refine ⟨⟨1, t, ht⟩, symLift_of_tval hL rfl hν (fun T' π z J hJ p => ?_) (fun T' π z J hJ p => ?_), hv'⟩
  · exact Finset.prod_eq_one fun _ _ => hv' _ _ _ _ hJ
  · rw [hv' _ _ _ _ hJ, hv' _ _ _ _ hJ, MonObj.comp_one, inv_one, _root_.one_mul, _root_.one_mul, _root_.one_mul,
      mul_inv_cancel]

theorem isActOf_self (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB)
    {ν : LB.Gen (negLB A L 1 T)} (hν : ν.IsGen) {a : ℤ} {m q : ℕ} (hq : Odd q)
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ m).left] ![a, -1])} (hα : α.IsGen)
    {th : LB.Sec (LPow A L 1 T)} {s : LB.Sec (LPow A L a T)}
    (hs : IsTwistPull A L (mulT A T m) (snd T A ^ m) (lift_snd _ _) a 1 α th s)
    {y : T ⟶ A} (hm : y ^ m = 1) (hy : y ^ q = 1) {θ : ThetaGrp A L a T} (H : SymLift A L a q y θ) :
    IsActOf A L a θ s s := by
  have := hA.comm
  obtain ⟨θ₁, h₁, v₁⟩ := exists_symLift_one hL hν
  obtain ⟨θ', h', v'⟩ := exists_symLift_mulPull hA hL (one_dvd q) hα hy (hm.symm ▸ h₁)
  have hc := SymLiftOdd.symLift_unique hG hA hL hq θ θ' H h'
  refine isTwistPull_of_sv A hL θ.isGen fun z J hJ => ?_
  have e : tval θ (𝟙 _) z J = tval θ' (𝟙 _) z J := val_corr hJ hc _
  have e₁ := sv_mulPull hs (fst T A) hJ (snd T A)
  have e₂ := sv_mulPull hs (fst T A) hJ ((fst T A ≫ y) * snd T A)
  have e₃ := v' _ (fst T A) z J hJ (snd T A)
  rw [v₁ _ _ _ _ hJ, _root_.mul_one] at e₃
  rw [mul_pow, ← MonObj.comp_pow, hm, MonObj.comp_one, _root_.one_mul] at e₂
  change _ = (tval θ (𝟙 _) z J).val * _
  rw [e, SymLiftOdd.id_eq_lift, ThetaCoord.lift_translT, H.pt_eq, e₃, e₁, e₂, Units.val_mul, _root_.mul_assoc,
    Units.inv_mul_cancel_left]

theorem act_act (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {k : ℤ} {q : ℕ} (hq : Odd q) {x y : T ⟶ A}
    (hy : y ^ q = 1) {θx θy θ : ThetaGrp A L k T} (Hx : SymLift A L k q x θx) (Hy : SymLift A L k q y θy)
    (H : SymLift A L k q (y * x) θ) {c : Γ(T.left, ⊤)ˣ} (hc : WeilIs A L k x y c)
    {s s' s'' t : LB.Sec (LPow A L k T)} (h₁ : IsActOf A L k θy s s') (h₂ : IsActOf A L k θx s' s'')
    (h₃ : IsActOf A L k θ s t) :
    (SecM.ofSec A s'' : SecM A L k T) = ((c ^ ((q + 1) / 2) : Γ(T.left, ⊤)ˣ) : Γ(T.left, ⊤)) • SecM.ofSec A t := by
  refine ThetaAct.sv_ext hL fun z J hJ => ?_
  have e₁ := sv_act Hx.pt_eq h₂ (fst T A) hJ (snd T A)
  have e₂ := sv_act Hy.pt_eq h₁ (fst T A) hJ ((fst T A ≫ x) * snd T A)
  have e₃ := sv_act H.pt_eq h₃ (fst T A) hJ (snd T A)
  have e₄ := tval_mul hG hA hL hq hy Hx Hy H hc (fst T A) hJ (snd T A)
  rw [← _root_.mul_assoc, ← MonObj.comp_mul] at e₂
  rw [ThetaAct.sv_smul _ _ _ _ hJ, Category.id_comp, gs_unit _ _ ⊤ trivial, map_pow, SymLiftOdd.id_eq_lift]
  refine e₁.trans ?_
  rw [e₂, ← _root_.mul_assoc, ← Units.val_mul, e₄, Units.val_mul, _root_.mul_assoc, ← e₃]
  rfl

theorem sum_iff {k : ℤ} {κ : Type} [Fintype κ] (σ : LB.Sec (LPow A L k T)) (s : κ → SecM A L k T)
    (c : κ → Γ(T.left, ⊤)) :
    (∀ j, σ.f j = ∑ i, liftFun A _ (c i) * (SecM.toSec A (s i)).f j) ↔ SecM.ofSec A σ = ∑ i, c i • s i := by
  have e : ∀ j, (∑ i, c i • s i : SecM A L k T).1 j = ∑ i, liftFun A _ (c i) * (SecM.toSec A (s i)).f j := fun j => by
    rw [Submodule.coe_sum, Finset.sum_apply]
    rfl
  exact ⟨fun h => Subtype.ext (funext fun j => (h j).trans (e j).symm),
    fun h j => (congrArg (fun q => q.1 j) h).trans (e j)⟩

theorem existsUnique_of_basis {k : ℤ} {κ : Type} [Fintype κ] (s : Module.Basis κ Γ(T.left, ⊤) (SecM A L k T))
    (σ : LB.Sec (LPow A L k T)) :
    ∃! c : κ → Γ(T.left, ⊤), ∀ j, σ.f j = ∑ i, liftFun A _ (c i) * (SecM.toSec A (s i)).f j := by
  simp only [sum_iff]
  exact ⟨s.equivFun (SecM.ofSec A σ), (s.sum_equivFun _).symm, fun c hc => by
    rw [hc, ← s.equivFun_symm_apply, LinearEquiv.apply_symm_apply]⟩

theorem UnivBasis.exists_basis {P : PolAV S} [IsAffine T.left] {n : ℤ} {κ : Type} {b : κ → SecM P.A P.L n T}
    (h : UnivBasis P n b) : ∃ c : Module.Basis κ Γ(T.left, ⊤) (SecM P.A P.L n T), ∀ i, c i = b i := by
  obtain ⟨c, hc⟩ := h T (𝟙 T)
  exact ⟨c, fun i => (hc i).trans (pullM_id P.A P.isLB n _)⟩

theorem UnivBasis.unique {P : PolAV S} {n : ℤ} {κ : Type} [Unique κ] {b : κ → SecM P.A P.L n T}
    (h : UnivBasis P n b) : UnivBasis P n (fun _ : Fin 1 => b default) := fun T' _ u => by
  obtain ⟨c, hc⟩ := h T' u
  refine ⟨c.reindex (Equiv.ofUnique κ (Fin 1)), fun i => ?_⟩
  rw [Module.Basis.reindex_apply, hc, Subsingleton.elim ((Equiv.ofUnique κ (Fin 1)).symm i) default]

end GlobalTheory.ThetaReal
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ZH GlobalTheory.UT
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.NormValuation

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing in
open scoped CategoryTheory.Obj in
open Classical in
attribute [local instance] Over.cartesianMonoidalCategory in
private lemma exists_rat_norm_eq_rpow {p : ℕ} [Fact p.Prime] {x : PadicAlgCl p} (hx : x ≠ 0) :
    ∃ t : ℚ, ‖x‖ = (p : ℝ) ^ (t : ℝ) := by
  have hint : IsIntegral ℚ_[p] x := Algebra.IsIntegral.isIntegral x
  have hc := minpoly.coeff_zero_ne_zero hint hx
  refine ⟨(-((minpoly ℚ_[p] x).coeff 0).valuation : ℚ) / (minpoly ℚ_[p] x).natDegree, ?_⟩
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow,
    Padic.norm_eq_zpow_neg_valuation hc, ← Real.rpow_intCast,
    ← Real.rpow_mul (Nat.cast_nonneg _)]
  congr 1
  push_cast
  ring


open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing in
open scoped CategoryTheory.Obj in
open Classical in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.NormValuation.main : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra (FractionRing V) (PadicAlgCl p)], (∀ x : FractionRing V, ‖algebraMap _ (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) → ∀ ϖ : V, Irreducible ϖ → ∃ v : AddValuation (PadicAlgCl p) (WithTop ℚ), _root_.ReciprocityTheory.ChartRestriction.G.DVR.ValOver ϖ (PadicAlgCl p) v ∧ _root_.GlobalTheory.ZH.NormVal (algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V (FractionRing V) ϖ)) v ∧ ∀ x : PadicAlgCl p, (0 ≤ v x ↔ ‖x‖ ≤ 1) ∧ (v x = 0 ↔ ‖x‖ = 1) := by
  intro p _ V _ _ _ _ hV ϖ hϖ
  set π : PadicAlgCl p :=
    algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V (FractionRing V) ϖ) with hπ
  have hinjV := IsFractionRing.injective V (FractionRing V)
  have hπne : π ≠ 0 := by
    rw [hπ, map_ne_zero]
    exact fun h => hϖ.ne_zero (hinjV (by rw [h, map_zero]))
  have hπle : ‖π‖ ≤ 1 := (hV _).2 ⟨ϖ, rfl⟩
  have hπlt : ‖π‖ < 1 := by
    refine lt_of_le_of_ne hπle fun h1 => hϖ.not_isUnit ?_
    have hle : ‖algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V (FractionRing V) ϖ)⁻¹‖ ≤ 1 := by
      rw [map_inv₀, norm_inv, ← hπ, h1, inv_one]
    obtain ⟨a, ha⟩ := (hV _).1 hle
    refine isUnit_iff_exists_inv.2 ⟨a, hinjV ?_⟩
    rw [map_mul, ha, map_one]
    exact mul_inv_cancel₀ fun h => hϖ.ne_zero (hinjV (by rw [h, map_zero]))
  have hb0 : 0 < ‖π‖ := norm_pos_iff.2 hπne
  have hle : ∀ s t : ℝ, ‖π‖ ^ s ≤ ‖π‖ ^ t ↔ t ≤ s := fun s t =>
    Real.rpow_le_rpow_left_iff_of_base_lt_one hb0 hπlt
  have hinj : ∀ s t : ℝ, ‖π‖ ^ s = ‖π‖ ^ t → s = t := fun s t h =>
    le_antisymm ((hle t s).1 h.ge) ((hle s t).1 h.le)
  obtain ⟨s, hs⟩ := exists_rat_norm_eq_rpow hπne
  have hs0 : (s : ℝ) ≠ 0 := by
    intro h0
    rw [h0, Real.rpow_zero] at hs
    exact hπlt.ne hs
  obtain ⟨r, hexp⟩ : ∃ r : PadicAlgCl p → ℚ, ∀ x, x ≠ 0 → ‖x‖ = ‖π‖ ^ (r x : ℝ) := by
    refine ⟨fun x => if h : x = 0 then 0 else (exists_rat_norm_eq_rpow h).choose / s, ?_⟩
    intro x hx
    simp only [dif_neg hx]
    rw [hs, ← Real.rpow_mul (Nat.cast_nonneg _)]
    push_cast
    rw [mul_div_cancel₀ _ hs0]
    exact (exists_rat_norm_eq_rpow hx).choose_spec
  have hr_one : r 1 = 0 := by
    have h := hexp 1 one_ne_zero
    rw [norm_one, ← Real.rpow_zero ‖π‖] at h
    exact_mod_cast (hinj _ _ h).symm
  have hr_mul : ∀ x y : PadicAlgCl p, x ≠ 0 → y ≠ 0 → r (x * y) = r x + r y := by
    intro x y hx hy
    have h := hexp (x * y) (mul_ne_zero hx hy)
    rw [norm_mul, hexp x hx, hexp y hy, ← Real.rpow_add hb0] at h
    exact_mod_cast (hinj _ _ h).symm
  have hr_add : ∀ x y : PadicAlgCl p, x ≠ 0 → y ≠ 0 → x + y ≠ 0 →
      min (r x) (r y) ≤ r (x + y) := by
    intro x y hx hy hxy
    have h := (PadicAlgCl.isNonarchimedean p) x y
    rw [hexp x hx, hexp y hy, hexp _ hxy] at h
    rcases le_total (r x) (r y) with hxy' | hxy'
    · rw [min_eq_left hxy']
      have hm : max (‖π‖ ^ (r x : ℝ)) (‖π‖ ^ (r y : ℝ)) = ‖π‖ ^ (r x : ℝ) :=
        max_eq_left ((hle _ _).2 (by exact_mod_cast hxy'))
      rw [hm, hle] at h
      exact_mod_cast h
    · rw [min_eq_right hxy']
      have hm : max (‖π‖ ^ (r x : ℝ)) (‖π‖ ^ (r y : ℝ)) = ‖π‖ ^ (r y : ℝ) :=
        max_eq_right ((hle _ _).2 (by exact_mod_cast hxy'))
      rw [hm, hle] at h
      exact_mod_cast h
  set w : PadicAlgCl p → WithTop ℚ := fun x => if x = 0 then ⊤ else (r x : WithTop ℚ) with hw
  have hw0 : w 0 = ⊤ := by simp [hw]
  have hw1 : w 1 = 0 := by simp [hw, hr_one]
  have hwadd : ∀ x y, min (w x) (w y) ≤ w (x + y) := by
    intro x y
    by_cases hx : x = 0
    · simp [hw, hx]
    by_cases hy : y = 0
    · simp [hw, hy]
    by_cases hxy : x + y = 0
    · simp [hw, hxy]
    simp only [hw, if_neg hx, if_neg hy, if_neg hxy]
    rw [← WithTop.coe_min, WithTop.coe_le_coe]
    exact hr_add x y hx hy hxy
  have hwmul : ∀ x y, w (x * y) = w x + w y := by
    intro x y
    by_cases hx : x = 0
    · simp [hw, hx]
    by_cases hy : y = 0
    · simp [hw, hy]
    simp only [hw, if_neg hx, if_neg hy, if_neg (mul_ne_zero hx hy)]
    rw [hr_mul x y hx hy, WithTop.coe_add]
  let v : AddValuation (PadicAlgCl p) (WithTop ℚ) := AddValuation.of w hw0 hw1 hwadd hwmul
  have hv : ∀ x, v x = w x := fun x => rfl
  have hunit : ∀ u : Vˣ,
      ‖algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V (FractionRing V) u)‖ = 1 := by
    intro u
    have h1 := (hV (algebraMap V (FractionRing V) u)).2 ⟨u, rfl⟩
    have h2 := (hV (algebraMap V (FractionRing V) (u⁻¹ : Vˣ))).2 ⟨_, rfl⟩
    have h3 : ‖algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V (FractionRing V) u)‖ *
        ‖algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V (FractionRing V) (u⁻¹ : Vˣ))‖
          = 1 := by
      rw [← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
    nlinarith [norm_nonneg (algebraMap (FractionRing V) (PadicAlgCl p)
      (algebraMap V (FractionRing V) u)), norm_nonneg (algebraMap (FractionRing V) (PadicAlgCl p)
      (algebraMap V (FractionRing V) (u⁻¹ : Vˣ)))]
  refine ⟨v, ?_, ?_, ?_⟩
  · unfold _root_.ReciprocityTheory.ChartRestriction.G.DVR.ValOver
    intro c n hc
    unfold _root_.ReciprocityTheory.ChartRestriction.G.DVR.HasVal at hc
    obtain ⟨u, rfl⟩ := hc
    have hne : algebraMap (FractionRing V) (PadicAlgCl p)
        ((algebraMap V (FractionRing V)) ϖ ^ n * (algebraMap V (FractionRing V)) u) ≠ 0 := by
      rw [map_mul, map_zpow₀]
      refine mul_ne_zero (zpow_ne_zero _ hπne) ?_
      intro h
      have := hunit u
      rw [h, norm_zero] at this
      exact zero_ne_one this
    rw [hv]
    simp only [hw, if_neg hne]
    have h2 : ‖algebraMap (FractionRing V) (PadicAlgCl p)
        ((algebraMap V (FractionRing V)) ϖ ^ n * (algebraMap V (FractionRing V)) u)‖ =
          ‖π‖ ^ (n : ℝ) := by
      rw [map_mul, map_zpow₀, norm_mul, norm_zpow, hunit u, _root_.mul_one, ← hπ,
        Real.rpow_intCast]
    have := hinj _ _ ((hexp _ hne).symm.trans h2)
    rw [WithTop.coe_eq_coe]
    exact_mod_cast this
  · unfold _root_.GlobalTheory.ZH.NormVal
    refine ⟨hb0, hπlt, fun x q => ?_⟩
    by_cases hx : x = 0
    · subst hx
      rw [hv, hw0, norm_zero]
      constructor
      · intro h; exact absurd h WithTop.top_ne_coe
      · intro h; exact absurd h.symm (Real.rpow_pos_of_pos hb0 _).ne'
    rw [hv]
    simp only [hw, if_neg hx, WithTop.coe_eq_coe]
    rw [hexp x hx]
    constructor
    · rintro rfl; rfl
    · intro h; exact_mod_cast hinj _ _ h
  · intro x
    by_cases hx : x = 0
    · subst hx
      simp [hv, hw0]
    rw [hv]
    simp only [hw, if_neg hx]
    rw [hexp x hx]
    have h1 := hle (r x : ℝ) 0
    rw [Real.rpow_zero] at h1
    refine ⟨?_, ?_⟩
    · rw [h1, WithTop.coe_nonneg]
      exact_mod_cast Iff.rfl
    · rw [WithTop.coe_eq_zero]
      constructor
      · rintro h; rw [h]; simp
      · intro h
        have := hinj (r x : ℝ) 0 (by rw [Real.rpow_zero]; exact h)
        exact_mod_cast this

end GlobalTheory.NormValuation
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.ClassWeight
open GlobalTheory.UT

def kf (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F] :
    F →+* Γ((TFK (R := R) F).left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom

theorem kf_bijective (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F] :
    Function.Bijective (kf R F) :=
  ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ} [Fact p.Prime]
  {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀)

theorem base_eq : (show (TFK (R := u.V) (PadicAlgCl p)).left ⟶ (baseOver (Sp S.R)).left from spMap y₀) ≫
    (baseOver (Sp S.R)).hom = (TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK := by
  refine (Category.comp_id _).trans ?_
  exact (congrArg spMap u.fac.symm).trans
    (Spec.map_comp (CommRingCat.ofHom u.yK) (CommRingCat.ofHom (algebraMap (FractionRing u.V) (PadicAlgCl p))))

def Moved (w : LB.Iso u.A.L (ρ.P.L.pull u.φ)) {k : ℕ} (t : SecA u.A (PadicAlgCl p) k)
    (s : LB.Sec (LPow ρ.P.A ρ.P.L (k : ℤ) (baseOver (Sp S.R)))) : Prop :=
  ThetaPtMove.SecRel u.cart (T := TFK (R := u.V) (PadicAlgCl p)) (T₀ := baseOver (Sp S.R)) (spMap y₀) (base_eq u) w t s

theorem exists_moved {w : LB.Iso u.A.L (ρ.P.L.pull u.φ)} (hw : w.IsGen) {k : ℕ}
    (s : LB.Sec (LPow ρ.P.A ρ.P.L (k : ℤ) (baseOver (Sp S.R)))) : ∃ t, Moved u w t s :=
  ThetaPtMove.exists_secRel u.cart _ _ hw ρ.P.isLB u.A.isLB s

end GlobalTheory.ZH.ClassWeight
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

noncomputable section
namespace GlobalTheory.FieldPull
open GlobalTheory.ArcPull GlobalTheory.PsiEvenPull

theorem nonempty_psiOn_field {K : Type} [Field K] (D : DegPre K) : Nonempty (PsiOn D ⊤) := by
  refine nonempty_psiOn_top D fun χ => (psiUnitOn_univ_iff D χ).2 ?_
  let σ : FractionRing K ≃+* K := (FractionRing.algEquiv K K).toRingEquiv
  let s : Sp K ⟶ (TK K).left := spMap σ.toRingHom
  have h₁ : s ≫ jK K = 𝟙 _ := by
    refine (spMap_comp _ _).symm.trans ((congrArg spMap (RingHom.ext fun x => ?_)).trans (Spec.map_id (CommRingCat.of K)))
    exact (FractionRing.algEquiv K K).commutes x
  have h₂ : jK K ≫ s = 𝟙 _ := by
    refine (spMap_comp _ _).symm.trans ((congrArg spMap (RingHom.ext fun x => ?_)).trans (Spec.map_id (CommRingCat.of (FractionRing K))))
    exact (FractionRing.algEquiv K K).injective ((FractionRing.algEquiv K K).commutes _)
  obtain ⟨t, ht, vt⟩ := exists_gen D.P.isLB (K' := PUnit) (φ' := fun _ => ((D.c χ).left : Sp K ⟶ _)) (ε' := fun _ => -1)
    (fun U _ h => Finset.prod_congr rfl fun _ _ => congrArg (fun q => h q ^ (-1 : ℤ)) (by
      show s ≫ jK K ≫ (D.c χ).left = _
      rw [← Category.assoc, h₁, Category.id_comp]))
    (LB.pullGen D.P.L _ _ (D.psi χ) s) (DVR.pullGen_isGen _ _ _ _ (D.psi_gen χ) s)
  refine ⟨t, ht, corr_of_val D.P.isLB fun y J hJ => ?_⟩
  refine (val_pull hJ _ _ _).trans ((vt _ _ y J hJ).trans ((val_pull hJ _ _ _).trans ?_))
  exact congrArg (fun q => val (D.psi χ) q y J) ((Category.assoc _ _ _).trans
    ((congrArg (𝟙 _ ≫ ·) h₂).trans (Category.id_comp _)))

theorem exists_isPullDeg_of_val {K₀ K : Type} [Field K₀] [Field K] (i : K₀ →+* K) (D : DegPre K₀) (D' : DegPre K)
    {Φ : D'.P.A.left ⟶ D.P.A.left} (gp : IsGrpPullback D'.P.A D.P.A (spMap i) Φ)
    (w : LB.Iso D'.P.L (D.P.L.pull Φ)) (hw : PGen w)
    (hr : PMaps w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => eSec D.P.A) (fun _ => 1) D'.rig D.rig (spMap i))
    (xe : D'.X ≃+ D.X) (hc : ∀ x, (D'.c x).left ≫ Φ = spMap i ≫ (D.c (xe x)).left)
    (hψ : ∀ (x : D'.X) (z : (TK K).left) J J', Good D.P.L z J → Good D'.P.L z J' →
      val (D.psi (xe x)) (genMap i.injective) z J = (om w z J J' (D'.xK x))⁻¹ * val (D'.psi x) (𝟙 _) z J') :
    ∃ hD : IsPullDeg i D D', proj hD = Φ ∧ hD.xe = xe ∧ HEq hD.w w := by
  obtain ⟨ψW⟩ := nonempty_psiOn_field D
  obtain ⟨e, e_hom, he⟩ := grpPullback_iso gp (isGrpPullback_pullback D.P.A (specOf i))
  subst he
  have hE : eSec D'.P.A ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) = specOf i ≫ eSec D.P.A :=
    (cubeMapOf gp).e_comm
  obtain ⟨g, hg⟩ : ∃ g : (TK K).left ⟶ (TW (⊤ : (Sp K₀).Opens)).left, g ≫ (⊤ : (Sp K₀).Opens).ι = jK K ≫ specOf i :=
    ⟨IsOpenImmersion.lift (⊤ : (Sp K₀).Opens).ι (jK K ≫ specOf i) (by
      rw [Scheme.Opens.range_ι]; exact Set.subset_univ _), IsOpenImmersion.lift_fac _ _ _⟩
  have sq : g ≫ (⊤ : (Sp K₀).Opens).ι = genMap i.injective ≫ jK K₀ :=
    hg.trans ((Category.id_comp _).symm.trans (fracMap_sq i.injective))
  obtain ⟨lam, l₁, l₂⟩ : ∃ lam : (TK K).left ⟶ (jK K₀ ⁻¹ᵁ ⊤).toScheme, lam ≫ (jK K₀ ⁻¹ᵁ ⊤).ι = genMap i.injective ∧
      lam ≫ (jK K₀ ∣_ ⊤) = g :=
    ⟨(isPullback_morphismRestrict (jK K₀) ⊤).lift _ _ sq,
      (isPullback_morphismRestrict (jK K₀) ⊤).lift_snd _ _ _,
      (isPullback_morphismRestrict (jK K₀) ⊤).lift_fst _ _ _⟩
  have hx : ∀ x, g ≫ (toUnit (TW ⊤) ≫ D.c (xe x)).left =
      D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) := fun x => by
    show g ≫ (⊤ : (Sp K₀).Opens).ι ≫ (D.c (xe x)).left = (jK K ≫ (D'.c x).left) ≫ _
    rw [Category.assoc, hc, ← Category.assoc, hg, Category.assoc]
  choose b hb vb using fun x => exists_gen D.P.isLB (K' := PUnit)
    (φ' := fun _ => D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i)) (ε' := fun _ => -1)
    (fun U _ h => Finset.prod_congr rfl fun _ _ => congrArg (fun q => h q ^ (-1 : ℤ)) (hx x))
    (LB.pullGen D.P.L _ _ (ψW.psi (xe x)) g) (DVR.pullGen_isGen _ _ _ _ (ψW.psi_gen _) g)
  choose psi hpsi vpsi using fun x => DegPull.exists_down_val hw D.P.isLB D'.P.isLB (K := PUnit)
    (φ' := fun _ => D'.xK x) (ε := fun _ => -1) (fun _ => rfl) (b x) (hb x)
  have eψ : ∀ x, psi x = D'.psi x := fun x => TorusExt.gen_ext_val D'.P.isLB (hpsi x) (D'.psi_gen x) fun y J' hJ' => by
    obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB y
    have v := vpsi x _ (𝟙 _) y _ _ (hJ.mem _ (𝟙 _)) (hJ'.mem _ (𝟙 _))
    have u := (val_pull hJ _ _ _).symm.trans ((val_corr hJ (ψW.psi_eq (xe x)) lam).trans (val_pull hJ _ _ _))
    rw [l₁, l₂, hψ x y J J' hJ hJ'] at u
    have v₁ : val (b x) (𝟙 _) y J = val (ψW.psi (xe x)) g y J :=
      (vb x _ _ y J hJ).trans ((val_pull hJ _ _ _).trans (by rw [Category.id_comp]))
    have v₂ : val (b x) (𝟙 _) y J = (om w y J J' (D'.xK x))⁻¹ * val (psi x) (𝟙 _) y J' := by
      refine v.trans (congrArg₂ (· * ·) ?_ rfl)
      rw [pw, Fintype.prod_unique, zpow_neg_one]
      simp only [om, Category.id_comp]
    exact mul_left_cancel (v₂.symm.trans (v₁.trans u))
  refine ⟨⟨e, e_hom, w, (isGen_iff w).2 hw, hE, ?_, xe, hc, ⊤, ψW, g, hg, fun x => ⟨b x, fun jN jL => ?_,
      corr_of_val D.P.isLB fun y J hJ => vb x _ _ y J hJ⟩⟩, rfl, rfl, HEq.rfl⟩
  · exact (maps_iff w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf i) _
      (rigPull_le (G' := D'.P.A) (G := D.P.A) _ (specOf i) hE D.P.L) (fun _ => rfl)).2 hr
  · rw [← eψ]
    refine unit_ext fun y hy => ?_
    have v := vpsi x _ (𝟙 _) y jN (fun _ => jL) (GeneratorPullback.mapsAt_le_b _ _ _ _ jN jL hy) (GeneratorPullback.mapsAt_le_a _ _ _ _ jN jL hy)
    refine (gm_res _ y _ hy _).trans (v.trans (Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_
      (gm_res _ y _ hy _)))))
    rw [pw, Fintype.prod_unique]
    exact (map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ)) (gm_pull (𝟙 _) _ y _ hy _))

theorem pmaps_rig {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
    {D' : DegPre R'} (hD : IsPullDeg φ D D') :
    PMaps hD.w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => eSec D.P.A) (fun _ => 1) D'.rig D.rig (spMap φ) :=
  (maps_iff hD.w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf φ) _
    (rigPull_le (proj hD) (specOf φ) hD.he D.P.L) (fun _ => rfl)).1 hD.w_rig

end GlobalTheory.FieldPull
end
end
