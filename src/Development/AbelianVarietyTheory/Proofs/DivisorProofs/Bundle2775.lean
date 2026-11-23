module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsoFreePerpLabelKernelWeights
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2640
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle081
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle129
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle070
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2692
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.CoeNonzeroLocusCanonicalEqComplRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2695
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.PicardGroup
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
import Mathlib.Tactic.Linter.HaveILetI
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNumberFieldQkPointsComplexDegeneration
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle003

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.TorusExt GlobalTheory.ZH.TorusPerp GlobalTheory.QkNumberField GlobalTheory.TorsionExt

namespace GlobalTheory.Poinc.UTestLabel

theorem char_eq_weil_of_label : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real), ∃ sg : ℤˣ, ∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (τ' : Multiplicative u.D.toPre.X →* (PadicAlgCl p)ˣ) (b : S.Gam), τ' ^ (S.r * S.N) = 1 → (∀ (q : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), q.y = 0 → GlobalTheory.UT.IsTor τ' q.g → QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) q x → x.left ≫ u.φ = spMap y₀ ≫ (ρ.pt b).left) → ∀ (a : S.Gam) (β : u.D.toPre.X), l.yy a = QuotientAddGroup.mk β → ((τ' (Multiplicative.ofAdd β) : (PadicAlgCl p)ˣ) : PadicAlgCl p) = y₀ (algebraMap o S.R (S.ζ ^ (S.r * S.N * ((sg : ℤ) • eStd S.g _ b a).val))) := by
  intro o Ω _ _ _ S ρ
  refine ⟨1, ?_⟩
  intro p _ y₀ u l τ' b hτ hb a β hβ
  have hL : LL := GlobalTheory.firstFiveLaws
  have hG : GlobalFnsSt := hL.1.globalFns
  have hk : 1 ≤ S.r * S.N :=
    Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega))
  haveI : CharZero u.V := CharZero.mk (fun m n hmn => by
    have e0 := congrArg ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V))) hmn
    simpa only [map_natCast, Nat.cast_inj] using e0)
  obtain ⟨f, hf1, -, -, -, hfW⟩ := GlobalTheory.ZH.uTors_closed u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) (S.r * S.N) hk
  obtain ⟨pk, x, hpkx, hxo⟩ := GlobalTheory.Poinc.exists_qkPt_of_utest o Ω S ρ p y₀ u a
  obtain ⟨q, hqy, hqt⟩ := exists_qkPt_tor u.D.tau_bimult τ' hτ
  have hqx : QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) q (f q) := (hf1 q (f q)).2 rfl
  have hqo := hb q (f q) hqy hqt hqx
  have hpk : x = f pk := (hf1 pk x).1 hpkx
  have W₁ := weilQkIs_tor hG q pk hqy hqt
  have W₂ := (hfW q pk (τ' (Multiplicative.ofAdd pk.y))).1 W₁
  have := ρ.P.isAb.comm
  have hy : (TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK = spMap y₀ := by
    have e1 : (TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK =
        spMap ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp u.yK) := (spMap_comp _ _).symm
    rw [e1, u.fac]
  let h : Over.mk ((TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK) ⟶ baseOver (Sp S.R) :=
    Over.homMk ((TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK) (by simp)
  have hh : h.left = spMap y₀ := hy
  have hζ : IsPrimitiveRoot (S.ζ ^ (S.r * S.N)) (S.r * S.N) :=
    S.prim.pow (pow_pos hk 2) (pow_two _)
  let c₀ : (S.R)ˣ := Units.map (algebraMap o S.R).toMonoidHom (hζ.isUnit (by omega)).unit
  have w := GlobalTheory.CommPairing.weilIs_pull hG ρ.P.isAb ρ.P.isLB h
    (ρ.weil b a (c₀ ^ (eStd S.g _ b a).val) (by rw [pow_mul, map_pow]; rfl))
  have W₃ := (GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ _ _ _ _ _ _ ρ.P.isLB u.A.isLB u.cart u.lb
    (TFK (R := u.V) (PadicAlgCl p)) _ (f q) (f pk) (h ≫ ρ.pt b) (h ≫ ρ.pt a) _ ?_ ?_).2 w
  · rw [hh, map_unitOn] at W₃
    have e := unitOn_injective (GlobalTheory.CommutatorPairing.weilIs_unique hG u.A.isAb u.A.isLB W₂ W₃)
    have e' := congrArg Units.val e
    simp only [MonoidHom.coe_coe, Units.coe_map, Units.val_pow_eq_pow_val, c₀, IsUnit.unit_spec,
      RingHom.toMonoidHom_eq_coe] at e'
    have hq : (QuotientAddGroup.mk β : u.D.toPre.X ⧸ (nsmulAddMonoidHom (S.r * S.N) : u.D.toPre.X →+ u.D.toPre.X).range) =
        QuotientAddGroup.mk pk.y := hβ.symm.trans (l.yy_eq a pk x hpkx hxo)
    obtain ⟨m, hm⟩ := AddMonoidHom.mem_range.1 (QuotientAddGroup.eq.1 hq)
    have hpy : pk.y = β + (S.r * S.N) • m := by
      rw [nsmulAddMonoidHom_apply] at hm
      rw [hm]; abel
    have hτm : τ' (Multiplicative.ofAdd ((S.r * S.N) • m)) = 1 := by
      rw [ofAdd_nsmul, map_pow, ← MonoidHom.pow_apply, hτ, MonoidHom.one_apply]
    rw [hpy, ofAdd_add, map_mul, hτm, _root_.mul_one] at e'
    rw [e', Units.val_one, one_smul, ← map_pow, ← pow_mul]
  · show h.left ≫ (ρ.pt b).left = _
    rw [hh, hqo]
  · show h.left ≫ (ρ.pt a).left = _
    rw [hh, ← hxo, hpk]

end GlobalTheory.Poinc.UTestLabel
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section
open Classical

namespace GlobalTheory.Poinc

theorem labelHom_of_comp_eq : ∀ {o₁ Ω₁ o₂ Ω₂ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] (S₁ : ThetaSys o₁ Ω₁) (S₂ : ThetaSys o₂ Ω₂) (ρ₁ : S₁.Real) (ρ₂ : S₂.Real) (om : S₁.R →+* S₂.R) (φ : ρ₂.P.A.left ⟶ ρ₁.P.A.left), IsGrpPullback ρ₂.P.A ρ₁.P.A (spMap om) φ → ∀ τ : S₂.R →+* S₂.R, τ.comp om = om → ∃ gl : S₂.Gam →+ S₂.Gam, ∀ a, (ρ₂.pt (gl a)).left ≫ φ = spMap τ ≫ (ρ₂.pt a).left ≫ φ := by
  intro o₁ Ω₁ o₂ Ω₂ _ _ _ _ _ _ S₁ S₂ ρ₁ ρ₂ om φ hφ τ hτ
  have hsp : spMap τ ≫ spMap om = spMap om := by
    show Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    conv_rhs => rw [← hτ]
    rfl
  let B := baseOver (Sp S₂.R)
  let push : (B ⟶ ρ₂.P.A) → (Over.mk (B.hom ≫ spMap om) ⟶ ρ₁.P.A) := fun x =>
    Over.homMk (x.left ≫ φ) (by rw [Category.assoc, hφ.1.w, ← Category.assoc, Over.w x]; rfl)
  have push_mul : ∀ x y, push (x * y) = push x * push y := fun x y =>
    Over.OverMorphism.ext (hφ.2 B x y (push x) (push y) rfl rfl).symm
  have push_inj : ∀ x y, push x = push y → x = y := fun x y e =>
    Over.OverMorphism.ext (hφ.1.hom_ext (congrArg (fun z => z.left) e) (by rw [Over.w x, Over.w y]))
  let V : Over.mk (B.hom ≫ spMap om) ⟶ Over.mk (B.hom ≫ spMap om) :=
    Over.homMk (spMap τ) (by show spMap τ ≫ 𝟙 _ ≫ spMap om = 𝟙 _ ≫ spMap om; rw [Category.id_comp, hsp])
  have wa : ∀ a, (spMap τ ≫ (ρ₂.pt a).left ≫ φ) ≫ ρ₁.P.A.hom = 𝟙 _ ≫ spMap om := fun a => by
    rw [Category.assoc, Category.assoc, hφ.1.w, ← Category.assoc (ρ₂.pt a).left, Over.w (ρ₂.pt a)]
    show spMap τ ≫ 𝟙 _ ≫ spMap om = _
    simp only [Category.id_comp]; exact hsp
  let s : S₂.Gam → (B ⟶ ρ₂.P.A) := fun a =>
    Over.homMk (hφ.1.lift (spMap τ ≫ (ρ₂.pt a).left ≫ φ) (𝟙 _) (wa a)) (hφ.1.lift_snd _ _ _)
  have hs : ∀ a, (s a).left ≫ φ = spMap τ ≫ (ρ₂.pt a).left ≫ φ := fun a => hφ.1.lift_fst _ _ _
  have push_s : ∀ a, push (s a) = V ≫ push (ρ₂.pt a) := fun a => Over.OverMorphism.ext (hs a)
  have s_add : ∀ a b, s (a + b) = s a * s b := fun a b => push_inj _ _ (by
    rw [push_s, ρ₂.pt_add, push_mul, MonObj.comp_mul, push_mul, push_s, push_s])
  let sH : Multiplicative S₂.Gam →* (B ⟶ ρ₂.P.A) := MonoidHom.mk' (fun a => s a.toAdd) (fun a b => s_add _ _)
  let ptH : Multiplicative S₂.Gam →* (B ⟶ ρ₂.P.A) := MonoidHom.mk' (fun a => ρ₂.pt a.toAdd) (fun a b => ρ₂.pt_add _ _)
  have hn : ∀ a : S₂.Gam, (S₂.r * S₂.N) • a = 0 := fun a => funext fun i => by
    rw [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul]; rfl
  have tors : ∀ (F : Multiplicative S₂.Gam →* (B ⟶ ρ₂.P.A)) (a : S₂.Gam),
      F (Multiplicative.ofAdd a) ^ (S₂.r * S₂.N) = 1 := fun F a => by
    rw [← map_pow, ← ofAdd_nsmul, hn, ofAdd_zero, map_one]
  have ex : ∀ a, ∃ b, ρ₂.pt b = s a := fun a =>
    GlobalTheory.torsionSection_eq_labelled_of_isDomain S₂.R ρ₂.P (S₂.r * S₂.N) S₂.Gam ρ₂.pt
      (fun K _ _ x z hz => (ρ₂.pt_bij K x z hz).exists) (s a) (tors sH a)
  let K := AlgebraicClosure Ω₂
  let j : S₂.R →+* K := (algebraMap Ω₂ K).comp S₂.R.val.toRingHom
  have inj : ∀ b b', ρ₂.pt b = ρ₂.pt b' → b = b' := by
    intro b b' e
    obtain ⟨c, -, hc⟩ := ρ₂.pt_bij K (spMap j)
      ((Over.homMk (spMap j) (by simp) : Over.mk (spMap j) ⟶ baseOver (Sp S₂.R)) ≫ ρ₂.pt b)
      (by rw [← MonObj.comp_pow, show ρ₂.pt b ^ (S₂.r * S₂.N) = 1 from tors ptH b, MonObj.comp_one])
    exact (hc b rfl).trans (hc b' (by rw [e])).symm
  refine ⟨AddMonoidHom.mk' (fun a => Classical.choose (ex a)) (fun a b => inj _ _ ?_), fun a => ?_⟩
  · rw [ρ₂.pt_add, Classical.choose_spec (ex (a + b)), Classical.choose_spec (ex a), Classical.choose_spec (ex b),
      s_add]
  · show (ρ₂.pt (Classical.choose (ex a))).left ≫ φ = _
    rw [Classical.choose_spec (ex a)]
    exact hs a

end GlobalTheory.Poinc
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.PullNonzero

theorem eq_zero_of_dominant {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {ψ : K → (Y ⟶ X)}
    {ε : K → ℤ} (s : LB.Sec (LB.LinComb L ψ ε)) (h : Y' ⟶ Y) [IsSchemeTheoreticallyDominant h] [QuasiCompact h]
    (h0 : ∀ y J, Good L y J → sval s h y J = 0) (j : K → L.ι) : s.f j = 0 := by
  refine h.app_injective (LB.wchart L ψ j) (Eq.trans ?_ (map_zero (h.app (LB.wchart L ψ j)).hom).symm)
  refine fn_ext fun y hy => ?_
  choose I hI using fun χ : Y' ⟶ X => exists_chart hL (χ y)
  have e₁ := gs_pull (𝟙 Y') h y (LB.wchart L ψ j) hy (s.f j)
  rw [Category.id_comp] at e₁
  have e₂ := sec_trans s h y (j := j) hy (Good.mem hI ψ h)
  have e₃ : gs h y _ _ = 0 := h0 y I hI
  rw [e₃, MulZeroClass.mul_zero] at e₂
  refine (e₁.trans e₂).trans ?_
  rw [gs_eq _ y _ hy, map_zero, map_zero]

theorem sval_zero {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {ψ : K → (Y ⟶ X)}
    {ε : K → ℤ} (s : LB.Sec (LB.LinComb L ψ ε)) (h0 : ∀ j, s.f j = 0) (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    sval s r z J = 0 := by
  refine (congrArg (gs r z (LB.wchart L ψ (fun k => J (r ≫ ψ k)))) (h0 _)).trans ((gs_eq r z _ (hJ.mem ψ r) _).trans ?_)
  exact (congrArg _ (map_zero _)).trans (map_zero _)

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (φ : R →+* V) (D' : DegPre V) (A' : PolAV (Sp (FractionRing V))) (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'] (U' : GlobalTheory.UU.PreU (maximalIdeal V) D' A' G') (F : G'.left ⟶ G.left) (C : GlobalTheory.LN.Cmp φ U U' F), GlobalTheory.LN.CDvr V → Function.Injective φ → ∀ (σ : U.SecGT (𝟙_ _) 1) (σ' : U'.SecGT (𝟙_ _) 1), (∀ (Z : Scheme.{0}) (r' : Z ⟶ (𝟙_ _ ⊗ G').left) (r : Z ⟶ (𝟙_ _ ⊗ G).left), r ≫ (snd _ G).left = r' ≫ (snd _ G').left ≫ F → ∀ z J J', Good U.P.L.L z J → Good U'.P.L.L z J' → sval σ r z J = (gw C.wL (r' ≫ (snd _ G').left) z (J (r ≫ (snd _ G).left)) (J' (r' ≫ (snd _ G').left))).val ^ 1 * sval σ' r' z J') → (∃ j, σ.f j ≠ 0) → ∃ j, σ'.f j ≠ 0 := by
  intro R _ _ _ _ D A G _ _ U V _ _ _ φ D' A' G' _ _ U' F C _ hφ σ σ' H ⟨j, hj⟩
  by_contra h0
  push Not at h0
  have hs := U.semi.smooth
  have : Flat G.hom := inferInstance
  have : IsDominant (spMap φ) := by
    refine ⟨?_⟩
    exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical φ).2
      (by rw [(RingHom.injective_iff_ker_eq_bot φ).1 hφ]; exact bot_le)
  have := IsSchemeTheoreticallyDominant.of_isDominant (spMap φ)
  have : IsSchemeTheoreticallyDominant F := IsSchemeTheoreticallyDominant.of_isPullback C.pb.1.flip
  have : QuasiCompact F := MorphismProperty.of_isPullback (P := @QuasiCompact) C.pb.1.flip inferInstance
  have e : ∀ {S : Scheme.{0}} (B : Over S), (λ_ B).inv.left ≫ (snd _ B).left = 𝟙 _ := fun B =>
    congrArg (fun q => q.left) (leftUnitor_inv_snd B)
  have : IsIso (λ_ G).inv.left := inferInstanceAs (IsIso ((Over.forget _).map (λ_ G).inv))
  refine hj (eq_zero_of_dominant U.P.L.isLB σ (F ≫ (λ_ G).inv.left) (fun y J hJ => ?_) j)
  choose J' hJ' using fun χ : G'.left ⟶ G'.left => exists_chart U'.P.L.isLB (χ y)
  have e₁ := H _ (λ_ G').inv.left (F ≫ (λ_ G).inv.left)
    (by rw [Category.assoc, e, ← Category.assoc, e, Category.id_comp, Category.comp_id]) y J J' hJ hJ'
  rw [sval_zero σ' h0 _ y hJ', MulZeroClass.mul_zero] at e₁
  exact e₁

end GlobalTheory.PullNonzero
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.exists_degenerationData_values_ultrametric : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (D : DegData V (IsLocalRing.maximalIdeal V)), ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∃ (N : NumD C) (ν : NumOf D.toPre C N), ν.IntN := by
  first | exact @GlobalTheory.IntGauge.exists_intN | exact GlobalTheory.IntGauge.exists_intN | (intros; apply GlobalTheory.IntGauge.exists_intN <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.exists_unit_of_norm_one_fractionRing_dvr : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (C : Type) [NormedField C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∀ a : FractionRing V, ‖algebraMap (FractionRing V) C a‖ = 1 → ∃ u : Vˣ, a = algebraMap V (FractionRing V) u := by
  first | exact @GlobalTheory.KeyEven.fractionRing_norm_one_unit | exact GlobalTheory.KeyEven.fractionRing_norm_one_unit | (intros; apply GlobalTheory.KeyEven.fractionRing_norm_one_unit <;> assumption)
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

namespace GlobalTheory.AdicExt

def ballIdeal {R K : Type} [CommRing R] [NormedField K] [IsUltrametricDist K] (φ : R →+* K)
    (hφ : ∀ x, ‖φ x‖ ≤ 1) (c : ℝ) (hc : 0 ≤ c) : Ideal R where
  carrier := {x | ‖φ x‖ ≤ c}
  zero_mem' := by simpa using hc
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_ofPred_eq, map_add (f := _)] at *
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  smul_mem' := fun a b hb => by
    simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul, norm_mul] at *
    exact (mul_le_of_le_one_left (norm_nonneg _) (hφ a)).trans hb

theorem mem_ballIdeal {R K : Type} [CommRing R] [NormedField K] [IsUltrametricDist K] {φ : R →+* K}
    {hφ : ∀ x, ‖φ x‖ ≤ 1} {c : ℝ} {hc : 0 ≤ c} {x : R} : x ∈ ballIdeal φ hφ c hc ↔ ‖φ x‖ ≤ c := Iff.rfl

theorem exists_bound {R K : Type} [CommRing R] [NormedField K] [IsUltrametricDist K] (φ : R →+* K)
    (hφ : ∀ x, ‖φ x‖ ≤ 1) (I : Ideal R) (hI : I.FG) (h : ∀ x ∈ I, ‖φ x‖ < 1) :
    ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ ∀ n : ℕ, ∀ x ∈ I ^ n, ‖φ x‖ ≤ c ^ n := by
  obtain ⟨s, rfl⟩ := hI
  obtain ⟨c, hc0, hc1, hs⟩ : ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ ∀ x ∈ s, ‖φ x‖ ≤ c := by
    refine ⟨(s.sup fun x => ‖φ x‖₊ : NNReal), NNReal.coe_nonneg _, ?_, fun x hx => ?_⟩
    · have : (s.sup fun x => ‖φ x‖₊ : NNReal) < 1 :=
        (Finset.sup_lt_iff (by simp)).2 fun x hx => h x (Ideal.subset_span hx)
      exact_mod_cast this
    · have : ‖φ x‖₊ ≤ (s.sup fun x => ‖φ x‖₊ : NNReal) := Finset.le_sup (f := fun x => ‖φ x‖₊) hx
      exact_mod_cast this
  have h1 : Ideal.span (s : Set R) ≤ ballIdeal φ hφ c hc0 := Ideal.span_le.2 fun x hx => hs x hx
  refine ⟨c, hc0, hc1, fun n => ?_⟩
  induction n with
  | zero => intro x _; simpa using hφ x
  | succ n ih =>
    have : Ideal.span (s : Set R) ^ (n + 1) ≤ ballIdeal φ hφ (c ^ (n + 1)) (pow_nonneg hc0 _) := by
      rw [pow_succ, Ideal.mul_le]
      intro a ha b hb
      rw [mem_ballIdeal, map_mul, norm_mul, pow_succ]
      exact mul_le_mul (ih a ha) (h1 hb) (norm_nonneg _) (pow_nonneg hc0 _)
    exact fun x hx => this hx

theorem norm_le_of_mem_smul_top {R A K : Type} [CommRing R] [CommRing A] [Algebra R A] [NormedField K]
    [IsUltrametricDist K] (F : A →+* K) (hF : ∀ x, ‖F x‖ ≤ 1) (J : Ideal R) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ x ∈ J, ‖F (algebraMap R A x)‖ ≤ c) (y : A) (hy : y ∈ J • (⊤ : Submodule R A)) :
    ‖F y‖ ≤ c := by
  refine Submodule.smul_induction_on (p := fun y => ‖F y‖ ≤ c) hy (fun a ha w _ => ?_) (fun a b ha hb => ?_)
  · rw [Algebra.smul_def, map_mul, norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (hF w)).trans (h a ha)
  · rw [map_add (f := _)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)

theorem ringHom_ext_of_norm {R K : Type} [CommRing R] [NormedField K] [IsUltrametricDist K]
    (I : Ideal R) (hI : I.FG) (F G : AdicCompletion I R →+* K) (hF : ∀ x, ‖F x‖ ≤ 1) (hG : ∀ x, ‖G x‖ ≤ 1)
    (h : ∀ x ∈ I, ‖F (algebraMap R _ x)‖ < 1) (e : ∀ a, F (algebraMap R _ a) = G (algebraMap R _ a)) :
    F = G := by
  obtain ⟨c, hc0, hc1, hc⟩ := exists_bound (F.comp (algebraMap R _)) (fun x => hF _) I hI h
  ext r
  have key : ∀ n : ℕ, ‖F r - G r‖ ≤ c ^ n := by
    intro n
    obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval I R n r)
    have hm : r - algebraMap R _ a ∈ I ^ n • (⊤ : Submodule R (AdicCompletion I R)) := by
      rw [AdicCompletion.pow_smul_top_eq_ker_eval hI, LinearMap.mem_ker, map_sub, ← ha, sub_eq_zero]
      rfl
    have h1 := norm_le_of_mem_smul_top F hF _ _ (pow_nonneg hc0 n) (hc n) _ hm
    have h2 := norm_le_of_mem_smul_top G hG _ _ (pow_nonneg hc0 n)
      (fun x hx => by rw [← e]; exact hc n x hx) _ hm
    have : F r - G r = F (r - algebraMap R _ a) + - G (r - algebraMap R _ a) := by
      rw [map_sub, map_sub, e]; ring
    rw [this]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 (by rwa [norm_neg]))
  have := ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1) key
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

theorem completion_ringHom_ext : ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] (p : ℕ) [Fact p.Prime] (f g : AdicCompletion (maximalIdeal O) O →+* OO p), IsLocalHom (f.comp (algebraMap O _)) → (∀ a, f (algebraMap O _ a) = g (algebraMap O _ a)) → f = g := by
  intro O _ _ _ p _ f g hf e
  have := ringHom_ext_of_norm (maximalIdeal O) (maximalIdeal O).fg_of_isNoetherianRing
    ((OO p).subtype.comp f) ((OO p).subtype.comp g)
    (fun x => (mem_OO_iff _).1 (f x).2) (fun x => (mem_OO_iff _).1 (g x).2)
    (fun x hx => (not_isUnit_OO_iff _).1 fun hu =>
      (IsLocalRing.mem_maximalIdeal x).1 hx (hf.map_nonunit x hu))
    (fun a => congrArg Subtype.val (e a))
  ext r
  exact RingHom.congr_fun this r

end GlobalTheory.AdicExt
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.ModelAt

open GlobalTheory.Points GlobalTheory.ZH.RatModel

theorem isIntegral_valMap {C : Type} [CommRing C] {Z : Scheme.{0}} {V : Z.Opens} (hV : IsAffineOpen V)
    (f : Sp C ⟶ V) [IsFinite f] (h : ⊤ ≤ (f ≫ V.ι) ⁻¹ᵁ V) : (valMap (f ≫ V.ι) V h).hom.IsIntegral := by
  have e := specMap_valMap_fromSpec hV (f ≫ V.ι) h
  have e2 : Spec.map (valMap (f ≫ V.ι) V h) = f ≫ hV.isoSpec.hom := by
    rw [← cancel_mono hV.fromSpec, e, Category.assoc, ← hV.isoSpec_inv_ι, Iso.hom_inv_id_assoc]
  have : IsFinite (Spec.map (valMap (f ≫ V.ι) V h)) := by rw [e2]; infer_instance
  exact ((IsFinite.SpecMap_iff _).1 this).to_isIntegral

theorem mem_of_isIntegralElem {o Ω A : Type} [CommRing o] [Field Ω] [Algebra o Ω] [CommRing A]
    (S : Subalgebra o Ω) [IsFractionRing S Ω] [IsIntegrallyClosed S] (σ : A →+* Ω) (hσ : ∀ a, σ a ∈ S) {x : Ω}
    (hx : σ.IsIntegralElem x) : x ∈ S := by
  have h1 : (algebraMap S Ω).IsIntegralElem x := by
    obtain ⟨p, hp, h0⟩ := hx
    refine ⟨p.map (σ.codRestrict S hσ), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    exact h0
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 (show IsIntegral S x from h1)
  exact hy ▸ y.2

theorem exists_map_model : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (Z : Scheme.{0}) (π : M.Z ⟶ Z), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → IsFinite π → ∀ (R : Subalgebra o Ω), (∀ z : Ω, ∃ a ∈ R, ∃ c ∈ R, z = a / c) → IsIntegrallyClosed R → ∀ (V : Z.Opens) (f : Sp R ⟶ V), IsAffineOpen V → IsFinite f → M.pt ≫ π = spMap R.val.toRingHom ≫ f ≫ V.ι → ∃ φ : Sp R ⟶ M.Z, φ ≫ π = f ≫ V.ι ∧ ∀ (P : Sp R) (a b : R), b ∉ P.asIdeal → (a : Ω) / (b : Ω) ∈ M.O (φ P) := by
  intro o Ω _ _ _ M Z π hn hπ R hR hic V f hV hf hpt
  have hg : ⊤ ≤ (f ≫ V.ι) ⁻¹ᵁ V := fun w _ => (f w).2
  have hpV : ⊤ ≤ (M.pt ≫ π) ⁻¹ᵁ V := by
    rw [hpt]
    exact fun w _ => hg (x := _) trivial
  have hW : IsAffineOpen (π ⁻¹ᵁ V) := hV.preimage π
  have hne : ((π ⁻¹ᵁ V : M.Z.Opens) : Set M.Z).Nonempty :=
    ⟨M.pt (IsLocalRing.closedPoint Ω), hpV (x := IsLocalRing.closedPoint Ω) trivial⟩
  haveI : IsFractionRing R Ω := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨a, ha, c, hc, h⟩ := hR z
    exact ⟨⟨a, ha⟩, ⟨c, hc⟩, h⟩
  have hα := isIntegral_valMap hV f hg
  have hβ : (π.app V).hom.IsIntegral := (π.finite_app V hV).to_isIntegral
  have hcomm : ∀ a, M.res _ hne ((π.app V).hom a) = (((valMap (f ≫ V.ι) V hg).hom a : R) : Ω) := fun a => by
    rw [res_apply, valF_eq_valR, ← valR_comp, hpt, valR_spMap_comp _ _ _ hg, valR_eq _ _ hg]
    rfl
  have hσ : (M.res _ hne).comp (π.app V).hom = R.val.toRingHom.comp (valMap (f ≫ V.ι) V hg).hom :=
    RingHom.ext hcomm
  have h1 : ∀ c, M.res _ hne c ∈ R := fun c =>
    mem_of_isIntegralElem R ((M.res _ hne).comp (π.app V).hom) (fun a => by
      rw [RingHom.comp_apply, hcomm]; exact Subtype.prop _) (by
      obtain ⟨p, hp, h0⟩ := hβ c
      exact ⟨p, hp, by rw [← Polynomial.hom_eval₂, h0, map_zero]⟩)
  have h2 : ∀ r : R, ∃ c, M.res _ hne c = r := fun r => by
    have : (r : Ω) ∈ M.ringOn (π ⁻¹ᵁ V : M.Z.Opens) := mem_ringOn.2 fun z hz => by
      have := isIntegrallyClosed_O hn z
      refine mem_of_isIntegralElem (M.O z) ((M.res _ hne).comp (π.app V).hom) (fun a => by
        rw [RingHom.comp_apply, res_apply]; exact valF_mem_O hz _) ?_
      obtain ⟨p, hp, h0⟩ := hα r
      refine ⟨p, hp, ?_⟩
      rw [hσ]
      exact (Polynomial.hom_eval₂ p _ R.val.toRingHom r).symm.trans (by rw [h0, map_zero])
    obtain ⟨c, hc⟩ := (mem_ringOn_iff_exists hne).1 this
    exact ⟨c, (M.res_apply _ hne c).trans hc⟩
  let ψ : Γ(M.Z, π ⁻¹ᵁ V) ⟶ CommRingCat.of R := CommRingCat.ofHom ((M.res _ hne).codRestrict R h1)
  have hφ := le_preimage_specMap_fromSpec hW ψ
  refine ⟨Spec.map ψ ≫ hW.fromSpec, ?_, fun P a b hb => ?_⟩
  · refine ext_of_valR hV hφ hg fun a => ?_
    rw [valR_comp, valR_eq _ _ hφ, valMap_specMap_fromSpec, valR_eq _ _ hg]
    exact Subtype.ext (hcomm a)
  · have hz : (Spec.map ψ ≫ hW.fromSpec) P ∈ π ⁻¹ᵁ V := hφ (x := P) trivial
    obtain ⟨a', ha'⟩ := h2 a
    obtain ⟨b', hb'⟩ := h2 b
    have hbz : (Spec.map ψ ≫ hW.fromSpec) P ∈ M.Z.basicOpen b' := by
      change Spec.map ψ P ∈ hW.fromSpec ⁻¹ᵁ M.Z.basicOpen b'
      rw [hW.fromSpec_preimage_basicOpen]
      change ψ.hom b' ∉ P.asIdeal
      rwa [show ψ.hom b' = b from Subtype.ext hb']
    have hu := ((isUnit_O_iff _).1 ((isUnit_valF_iff hz b').2 hbz)).2
    rw [← ha', ← hb', res_apply, res_apply, div_eq_mul_inv]
    exact mul_mem (valF_mem_O hz a') hu

end GlobalTheory.Poinc.ModelAt
end

section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

theorem _root_.GlobalTheory.T.localEquation_mem_comap_map_idealSheaf_near_point : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M₁ M : RatModel o Ω) (π : M.Z ⟶ M₁.Z), M₁.IsHom M (AlgHom.id o Ω) π → ∀ (D : EffCartierData M.Z) (V : M₁.Z.affineOpens) (g : Γ(M₁.Z, V.1)) (x : M.Z) (i : D.ι), π x ∈ V.1 → x ∈ D.U i → g ∈ (D.idealSheaf.map π).ideal V → valF M₁.pt V.1 g ≠ 0 → valF M.pt (D.U i) (D.f i) / valF M₁.pt V.1 g ∈ M.O x → ∃ (W : M.Z.affineOpens) (h : W.1 ≤ D.U i), x ∈ W.1 ∧ resG M.Z h (D.f i) ∈ ((D.idealSheaf.map π).comap π).ideal W := by
  first | exact @GlobalTheory.Poinc.resG_f_mem_comap_map_ideal | exact GlobalTheory.Poinc.resG_f_mem_comap_map_ideal | (intros; apply GlobalTheory.Poinc.resG_f_mem_comap_map_ideal <;> assumption)
end
