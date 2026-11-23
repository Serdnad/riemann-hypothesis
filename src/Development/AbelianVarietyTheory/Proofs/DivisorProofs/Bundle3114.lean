module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle002
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRootStalk
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaPtEqUnitMulTh
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle935
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2065
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle015
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle004
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle040
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle120
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3045
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3044
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2635
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2942
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1009
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3046
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle070
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle031
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep.Labels

theorem comp_pow_overScheme_grpObj {S : Scheme.{0}} {A T T' : Over S} [GrpObj A] (ρ : T' ⟶ T) (x : T ⟶ A) (n : ℕ) :
    ρ ≫ x ^ n = (ρ ≫ x) ^ n := by
  induction n with
  | zero => simp only [pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, MonObj.comp_mul, ih, pow_succ]


open GlobalTheory.TorusExt in
attribute [local instance] gtGroup in
theorem yy_hom : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), (∀ a, ∃ mu, 𝔪.YY a mu) ∧ (∀ mu, ∃ a, 𝔪.YY a mu) ∧ (∀ a mu mu', 𝔪.YY a mu → (𝔪.YY a mu' ↔ ∀ v, CongMod (X₁.S.r * X₁.S.N) (mu' v) (mu v))) ∧ (∀ a a' mu mu', 𝔪.YY a mu → 𝔪.YY a' mu' → 𝔪.YY (a + a') (mu + mu')) := by
  intro g n F W Z i X₁ z₁ act V _ _ _ ev X _ m t δ 𝔪
  haveI : CharZero V := 𝔪.cn.2.2.2
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  have hB := 𝔪.D.tau_bimult
  have hk : 1 ≤ X₁.S.r * X₁.S.N := by
    have := X₁.S.r_pos; have := X₁.S.N_ge
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  obtain ⟨x, hx, xadd, -, xonto⟩ := GlobalTheory.ThetaDvr.torsion_points 𝔪.yK 𝔪.cart
  obtain ⟨rig, e, -, he, -⟩ := GlobalTheory.ThetaDvr.frames 𝔪.yK 𝔪.cart ⟨𝔪.wl, 𝔪.wl_gen⟩ x hx
  obtain ⟨f, f₁, f₂, f₃, f₄, -⟩ := GlobalTheory.TorsionIso.torsion_eq hL V (maximalIdeal V) hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U
    (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) hk
  have tor : ∀ p y, QkToAkU 𝔪.U.toUnifPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) p y →
      y ^ (X₁.S.r * X₁.S.N) = 1 := fun p y h => by
    obtain ⟨w, hw⟩ := 𝔪.U.ext
    exact (h w hw).1
  have uniq : ∀ a (y : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ 𝔪.A.A), y ^ (X₁.S.r * X₁.S.N) = 1 →
      y.left ≫ 𝔪.φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) ≫
        (X₁.ρ.pt a).left → y = x a := by
    intro a y hy hya
    obtain ⟨b, rfl⟩ := xonto y hy
    obtain ⟨c, -, hc⟩ := X₁.ρ.pt_bij (AlgebraicClosure (FractionRing V))
      (spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK))
      ((Over.homMk (spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK)) (by simp) :
        Over.mk (spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK)) ⟶
          baseOver (Sp X₁.S.R)) ≫ X₁.ρ.pt a)
      (by rw [← comp_pow_overScheme_grpObj, (X₁.ρ.fr_tors a).1, MonObj.comp_one])
    have h1 := hc a rfl
    have h2 := hc b (by
      ext1
      simp only [Over.comp_left, Over.homMk_left]
      rw [← hx b, hya])
    rw [h1.trans h2.symm]
  have ex : ∀ a, ∃ p, QkToAkU 𝔪.U.toUnifPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) p (x a) :=
    fun a => by
      obtain ⟨p, hp⟩ := f₂ (x a) (he a).1
      exact ⟨p, (f₁ _ _).2 hp.symm⟩
  have yyI : ∀ a mu, 𝔪.YY a mu ↔ ∃ p : QkPt 𝔪.D.toPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N),
      p.y = 𝔪.e₈ mu ∧ QkToAkU 𝔪.U.toUnifPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) p (x a) := by
    intro a mu
    constructor
    · rintro ⟨p, y, hpy, hq, hov⟩
      obtain rfl := uniq a y (tor p y hq) hov
      exact ⟨p, hpy, hq⟩
    · rintro ⟨p, hpy, hq⟩
      exact ⟨p, x a, hpy, hq, hx a⟩
  refine ⟨fun a => ?_, fun mu => ?_, fun a mu mu' h => ?_, fun a a' mu mu' h h' => ?_⟩
  · obtain ⟨p, hp⟩ := ex a
    exact ⟨𝔪.e₈.symm p.y, (yyI a _).2 ⟨p, by simp, hp⟩⟩
  · obtain ⟨p, hp⟩ := exists_qkPt (F := AlgebraicClosure (FractionRing V)) hL.1.mulN (Or.inr hL.1.polBaseChange) hB
      (n := X₁.S.r * X₁.S.N) (by omega) (𝔪.e₈ mu)
    obtain ⟨a, ha⟩ := xonto (f p) (tor p _ ((f₁ _ _).2 rfl))
    exact ⟨a, (yyI a mu).2 ⟨p, hp, (f₁ _ _).2 ha.symm⟩⟩
  · obtain ⟨p, hpy, hq⟩ := (yyI a mu).1 h
    rw [yyI]
    constructor
    · rintro ⟨p', hpy', hq'⟩
      have hpp : QkPt.Equiv _ _ p p' := (f₃ p p').1 (((f₁ _ _).1 hq).symm.trans ((f₁ _ _).1 hq'))
      obtain ⟨z, hz, -⟩ := (equiv_iff hB _ _).1 hpp
      have e' : mu' = mu + (X₁.S.r * X₁.S.N) • 𝔪.e₈.symm z := 𝔪.e₈.injective (by
        rw [map_add (f := _), map_nsmul, AddEquiv.apply_symm_apply, ← hpy, ← hpy', hz])
      intro v
      exact ⟨𝔪.e₈.symm z v, by rw [e']; rfl⟩
    · intro hc
      choose w hw using hc
      refine ⟨qkShift hB p (𝔪.e₈ w), ?_, (f₁ _ _).2 (((f₁ _ _).1 hq).trans ((f₃ _ _).2 (equiv_qkShift hB p _)))⟩
      show p.y + (X₁.S.r * X₁.S.N) • 𝔪.e₈ w = 𝔪.e₈ mu'
      rw [hpy, ← map_nsmul, ← map_add (f := _)]
      congr 1
      funext v
      exact (hw v).symm
  · obtain ⟨p, hpy, hq⟩ := (yyI a mu).1 h
    obtain ⟨p', hpy', hq'⟩ := (yyI a' mu').1 h'
    refine (yyI _ _).2 ⟨qkAdd hB p p', ?_, ?_⟩
    · show p.y + p'.y = 𝔪.e₈ (mu + mu')
      rw [map_add (f := _), hpy, hpy']
    · rw [f₁, f₄ _ _ _ (qkAdd_qkAdd hB p p'), ← (f₁ _ _).1 hq, ← (f₁ _ _).1 hq', xadd]

end GlobalTheory.Poinc.Sep.Labels
end
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

namespace GlobalTheory.Poinc.IntTerm.DvrScale

open GlobalTheory.TorusExt GlobalTheory.ZH.TestVal GlobalTheory.ThetaDvr.Scale
open Classical

theorem hasVal_of_unit_mul {V : Type} [CommRing V] [IsDomain V] {ϖ : V} (u : Vˣ) {r : V} {n : ℤ}
    (h : HasVal ϖ (algebraMap V (FractionRing V) ((u : V) * r)) n) :
    HasVal ϖ (algebraMap V (FractionRing V) r) n := by
  obtain ⟨u', hu'⟩ := h
  refine ⟨u' * u⁻¹, ?_⟩
  have e1 : algebraMap V (FractionRing V) r =
      algebraMap V (FractionRing V) ((u⁻¹ : Vˣ) : V) * algebraMap V (FractionRing V) ((u : V) * r) := by
    rw [← map_mul, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]
  rw [e1, hu', Units.val_mul, map_mul]
  ring


attribute [local instance] gtGroup in
theorem exists_dvd_pow : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsDiscreteValuationRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), ∃ b, ∀ a, ∃ (w : Fin 8 → X) (r : V), 𝔪.YY a w ∧ 𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩ ^ ((X₁.S.r * X₁.S.N) ^ 2) = algebraMap V (FractionRing V) r * 𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩ ^ ((X₁.S.r * X₁.S.N) ^ 2) * algebraMap V (FractionRing V) (mono W t δ w) := by
  intro g n F W Z i X₁ z₁ act V _ _ _ _ ev X _ m t δ 𝔪
  haveI : CharZero V := 𝔪.cn.2.2.2
  have hc : IsAdicComplete (maximalIdeal V) V := 𝔪.cn.2.2.1
  obtain ⟨hL, hL₂⟩ := abelianSchemeLaws_all
  obtain ⟨H, h₁, h₂, h₃, h₄⟩ := hyps hL hL₂
  have hm := odd_level' X₁.ρ
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, hc⟩
  have hB := 𝔪.D.tau_bimult
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  choose Q hQ using QForm.exists_QVal hϖ 𝔪.D
  obtain ⟨v, hv, -⟩ := GlobalTheory.ValClosure.exists_valuation_closure V ϖ hϖ
  have hu : IsUnit ((X₁.S.r * X₁.S.N : ℕ) : V) := by
    have := X₁.S.unit.map (ev.comp ((X₁.M.stalkEquiv z₁).symm.toRingHom.comp (algebraMap X₁.o₁ (X₁.M.O z₁))))
    rwa [map_natCast] at this
  obtain ⟨x, hx, xadd, xinj, xonto⟩ := GlobalTheory.ThetaDvr.torsion_points 𝔪.yK 𝔪.cart
  obtain ⟨rig, e, hrig, he, hsec⟩ := GlobalTheory.ThetaDvr.frames 𝔪.yK 𝔪.cart ⟨𝔪.wl, 𝔪.wl_gen⟩ x hx
  obtain ⟨t', ht⟩ := hsec 1 X₁.ρ.th₁
  obtain ⟨w₀, hw₀⟩ := EvalZero.exists_normW 𝔪.U.toUnifPre rig hrig
  obtain ⟨th, ϑ, hE, hP, hgen⟩ := exists_prim_generator H h₁ h₂ h₃ h₄ V hc ϖ hϖ 𝔪.D Q hQ _ v hv 𝔪.A 𝔪.G
    𝔪.semi 𝔪.U w₀ hw₀.1
  have key := val_theta H h₁ h₂ h₃ h₄ V hc ϖ hϖ 𝔪.D Q hQ _ v hv 𝔪.A 𝔪.G 𝔪.semi 𝔪.U w₀ rig hw₀ th ϑ hE hP
    _ hm hu
  obtain ⟨f, f₁, f₂, f₃, -⟩ := GlobalTheory.TorsionIso.torsion_eq H V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U
    (AlgebraicClosure (FractionRing V)) _ hm.pos
  obtain ⟨r, hr⟩ := hgen t'
  obtain ⟨sc, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure (FractionRing V)))).inv).2 r
  set Fc := AlgebraicClosure (FractionRing V) with hF
  set y₀ : X₁.S.R →+* Fc := (algebraMap (FractionRing V) Fc).comp 𝔪.yK with hy₀
  have tv : ∀ a z J, Good 𝔪.A.L z J → cst (R := V) Fc z sc *
      @id ((TF (R := V) Fc).left.presheaf.stalk z) (sA th (ptSecT 𝔪.A.A (x a)).left z J) =
      cst (R := V) Fc z (y₀ ⟨X₁.S.th a, X₁.S.th_mem a⟩) * @id ((TF (R := V) Fc).left.presheaf.stalk z)
        (val (powFrame 𝔪.A.A 𝔪.A.L (x a) (e a) ((1 : ℕ) : ℤ)) (𝟙 _) z J).val := fun a z J hJ =>
    (ThetaCompare.sval_smul hr (x a) hJ).symm.trans (ht a _ (by
      have b := X₁.ρ.th_val a
      rw [← powFrame_one' (X₁.ρ.pt a) (X₁.ρ.fr a)] at b
      exact b) z J hJ)
  have ex : ∀ a, ∃ q, QkToAkU 𝔪.U.toUnifPre Fc (X₁.S.r * X₁.S.N) q (x a) := fun a => by
    obtain ⟨q, hq⟩ := f₂ (x a) (he a).1
    exact ⟨q, (f₁ _ _).2 hq.symm⟩
  have yyOf : ∀ a q (χ : 𝔪.D.toPre.X), QkToAkU 𝔪.U.toUnifPre Fc (X₁.S.r * X₁.S.N) q (x a) →
      𝔪.YY a (𝔪.e₈.symm ((X₁.S.r * X₁.S.N) • χ + q.y)) := fun a q χ hq =>
    ⟨qkShift hB q χ, x a, by
      rw [AddEquiv.apply_symm_apply]
      show q.y + (X₁.S.r * X₁.S.N) • χ = _
      rw [add_comm],
      (f₁ _ _).2 (((f₁ _ _).1 hq).trans ((f₃ _ _).2 (equiv_qkShift hB q _))), hx a⟩
  have hM2 : (X₁.S.r * X₁.S.N) ^ 2 ≠ 0 := pow_ne_zero _ hm.pos.ne'
  by_cases h0 : sc = 0
  · have z0 : ∀ a, y₀ ⟨X₁.S.th a, X₁.S.th_mem a⟩ = 0 := fun a => by
      obtain ⟨z⟩ := CoefBasic.exists_pt (R := V) (F := Fc)
      obtain ⟨J, hJ⟩ := CoefBasic.exists_good' (Z := (TFK (R := V) Fc).left) 𝔪.A.isLB z
      have := tv a z J hJ
      rw [h0, CoefBasic.cst_eq, CoefBasic.cst_eq, map_zero, zero_mul] at this
      exact CoefBasic.cstH_inj (R := V) z (((Units.mul_left_eq_zero _).1 this.symm).trans (map_zero _).symm)
    have z1 : ∀ a, 𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩ = 0 := fun a =>
      (map_eq_zero_iff _ (algebraMap (FractionRing V) Fc).injective).1 (z0 a)
    refine ⟨0, fun a => ?_⟩
    obtain ⟨q, hq⟩ := ex a
    refine ⟨_, 0, yyOf a q 0 hq, ?_⟩
    rw [z1 a, zero_pow hM2, map_zero, zero_mul, zero_mul]

  have tv' : ∀ a z J, Good 𝔪.A.L z J → sA th (ptSecT 𝔪.A.A (x a)).left z J =
      @id ((TFK (R := V) Fc).left.presheaf.stalk z)
        (cst (R := V) Fc z (sc⁻¹ * y₀ ⟨X₁.S.th a, X₁.S.th_mem a⟩)) *
        (val (powFrame 𝔪.A.A 𝔪.A.L (x a) (e a) ((1 : ℕ) : ℤ)) (𝟙 _) z J).val := fun a z J hJ => by
    have b := congrArg (CoefBasic.cstH (R := V) z sc⁻¹ * ·) (tv a z J hJ)
    simp only [CoefBasic.cst_eq, ← _root_.mul_assoc, ← map_mul, inv_mul_cancel₀ h0, map_one, _root_.one_mul] at b
    rw [CoefBasic.cst_eq]
    exact b
  have hvs : v sc ≠ ⊤ := v.ne_top_iff.2 h0
  have split : ∀ a, v (y₀ ⟨X₁.S.th a, X₁.S.th_mem a⟩) = v sc + v (sc⁻¹ * y₀ ⟨X₁.S.th a, X₁.S.th_mem a⟩) := fun a => by
    rw [← v.map_mul, ← _root_.mul_assoc, mul_inv_cancel₀ h0, _root_.one_mul]
  have nz : ∀ a, v (sc⁻¹ * y₀ ⟨X₁.S.th a, X₁.S.th_mem a⟩) = 0 → v (y₀ ⟨X₁.S.th a, X₁.S.th_mem a⟩) = v sc :=
    fun a h => by rw [split a, h, add_zero]
  have h2 : 2 ≤ X₁.S.r * X₁.S.N := X₁.S.N_ge.trans (Nat.le_mul_of_pos_left _ X₁.S.r_pos)
  obtain ⟨b, hb⟩ : ∃ b, v (y₀ ⟨X₁.S.th b, X₁.S.th_mem b⟩) = v sc := by
    obtain ⟨p₀, hp₀⟩ := exists_qkPt (F := Fc) H.1.mulN (Or.inr H.1.polBaseChange) hB
      (n := X₁.S.r * X₁.S.N) hm.pos.ne' 0
    obtain ⟨q', x', -, hx', -, hval⟩ := (key p₀ (f p₀) ((f₁ _ _).2 rfl)).2 (X₁.S.r * X₁.S.N) h2 dvd_rfl hp₀
    obtain ⟨a', rfl⟩ := xonto x' (hx' w₀ hw₀.1).1
    exact ⟨a', nz a' (hval _ _ (he a') (tv' a'))⟩
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 hvs
  refine ⟨b, fun a => ?_⟩
  obtain ⟨q, hq₁⟩ := ex a
  obtain ⟨_, ⟨χ, rfl⟩, hχ⟩ := Int.exists_least_of_bdd (P := fun k => ∃ χ, Q ((X₁.S.r * X₁.S.N) • χ + q.y) = k)
    ⟨0, by
      rintro _ ⟨χ, rfl⟩
      by_cases c : (X₁.S.r * X₁.S.N) • χ + q.y = 0
      · rw [c, QForm.Q_zero hϖ 𝔪.D hQ]
      · exact zero_le_one.trans (QForm.Q_pos hϖ 𝔪.D hQ c)⟩ ⟨_, 0, rfl⟩
  have hk := ((key q _ hq₁).1 _ _ (he a) (tv' a)).1
    ((Q ((X₁.S.r * X₁.S.N) • χ + q.y) : ℚ) / ((X₁.S.r * X₁.S.N) ^ 2 : ℕ)) fun χ' =>
      div_le_div_of_nonneg_right (Int.cast_le.2 (hχ _ ⟨χ', rfl⟩)) (Nat.cast_nonneg _)
  set w := 𝔪.e₈.symm ((X₁.S.r * X₁.S.N) • χ + q.y) with hw
  have hew : 𝔪.e₈ w = (X₁.S.r * X₁.S.N) • χ + q.y := AddEquiv.apply_symm_apply _ _
  have hmono : v (algebraMap (FractionRing V) Fc (algebraMap V (FractionRing V) (mono W t δ w))) =
      (((Q ((X₁.S.r * X₁.S.N) • χ + q.y) : ℤ) : ℚ) : WithTop ℚ) := by
    obtain ⟨u, hpc⟩ := 𝔪.psi w
    rw [hew] at hpc
    exact hv _ _ (hasVal_of_unit_mul u (GlobalTheory.ValForm.hasVal_coord (hQ _) hpc))
  have hb0 : 𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩ ≠ 0 := fun h => hvs (by
    rw [← hb]; show v (algebraMap (FractionRing V) Fc (𝔪.yK _)) = ⊤; rw [h, map_zero, AddValuation.map_zero])
  have hne : 𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩ ^ ((X₁.S.r * X₁.S.N) ^ 2) *
      algebraMap V (FractionRing V) (mono W t δ w) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hb0)
      ((map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 (𝔪.mono_ne_zero w))
  have hle : v (algebraMap (FractionRing V) Fc (𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩ ^ ((X₁.S.r * X₁.S.N) ^ 2) *
      algebraMap V (FractionRing V) (mono W t δ w))) ≤
      v (algebraMap (FractionRing V) Fc (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩ ^ ((X₁.S.r * X₁.S.N) ^ 2))) := by
    rw [map_mul, map_pow, map_pow, v.map_mul, v.map_pow, v.map_pow, hmono]
    change (X₁.S.r * X₁.S.N) ^ 2 • v (y₀ ⟨X₁.S.th b, X₁.S.th_mem b⟩) + _ ≤
      (X₁.S.r * X₁.S.N) ^ 2 • v (y₀ ⟨X₁.S.th a, X₁.S.th_mem a⟩)
    rw [hb, split a, ← hs]

    have hN : (((X₁.S.r * X₁.S.N) ^ 2 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hM2
    have e : (((X₁.S.r * X₁.S.N) ^ 2 • (s : WithTop ℚ)) + (((Q ((X₁.S.r * X₁.S.N) • χ + q.y) : ℤ) : ℚ) : WithTop ℚ)) =
        (X₁.S.r * X₁.S.N) ^ 2 • ((s : WithTop ℚ) +
          (((Q ((X₁.S.r * X₁.S.N) • χ + q.y) : ℚ) / ((X₁.S.r * X₁.S.N) ^ 2 : ℕ) : ℚ) : WithTop ℚ)) := by
      rw [← WithTop.coe_add, ← WithTop.coe_nsmul, ← WithTop.coe_nsmul, ← WithTop.coe_add, WithTop.coe_eq_coe,
        nsmul_eq_mul, nsmul_eq_mul, mul_add, mul_div_cancel₀ _ hN]
    rw [e]
    exact nsmul_le_nsmul_right (add_le_add le_rfl hk) _
  obtain ⟨r', hr', -⟩ := GlobalTheory.ThetaDvr.exists_mul_of_val_le hϖ hv hne hle
  refine ⟨w, r', yyOf a q χ hq₁, ?_⟩
  rw [hr', _root_.mul_assoc]

end GlobalTheory.Poinc.IntTerm.DvrScale
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChartCubExt

theorem cube_pull_of_chart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {k : Type} [Field k] {m n : ℕ} (tC : SAB H (Sp (ChartRing k m n))) {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (ξ : Sp (ChartRing k m n) ⟶ S) (πC : tC.G.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback tC.G G ξ πC → ∀ (PP : RigLB G) (cub : CubicalStr G PP) {X' : Scheme.{0}} (tF : SAB H X') (j : X' ⟶ S) (e : tF.G.left ⟶ G.left) (cm : CubeMap tF.G G), cm.F = e → cm.e = j → cm.IsPullCubical tF.cub cub → ∀ (y : Sp (FractionRing (ChartRing k m n)) ⟶ X'), y ≫ j = jK _ ≫ ξ → ∀ (tK : SAB H (Sp (FractionRing (ChartRing k m n)))) (a : SABMap tK tC (jK _)) (b : SABMap tK tF y), a.φ ≫ πC = b.φ ≫ e → ∃ cm' : CubeMap tC.G G, cm'.F = πC ∧ cm'.e = ξ ∧ cm'.IsPullCubical tC.cub cub := by
  intro E _ _ _ H k _ m n tC S G _ _ ξ πC hG hπ PP cub X' tF j e cm hcF hce hcm y hy tK a b hab
  refine ⟨cubeMapOf hπ, rfl, rfl, ?_⟩
  let c2 : CubeMap tK.G G :=
    { F := b.cm.F ≫ cm.F, F3 := b.cm.F3 ≫ cm.F3, e := b.cm.e ≫ cm.e
      e_comm := by rw [← Category.assoc, b.cm.e_comm, Category.assoc, cm.e_comm, Category.assoc]
      psum_comm := fun I => by
        rw [← Category.assoc, b.cm.psum_comm, Category.assoc, cm.psum_comm, Category.assoc] }
  let c3 : CubeMap tK.G G :=
    { F := a.cm.F ≫ (cubeMapOf hπ).F, F3 := a.cm.F3 ≫ (cubeMapOf hπ).F3, e := a.cm.e ≫ (cubeMapOf hπ).e
      e_comm := by rw [← Category.assoc, a.cm.e_comm, Category.assoc, (cubeMapOf hπ).e_comm, Category.assoc]
      psum_comm := fun I => by
        rw [← Category.assoc, a.cm.psum_comm, Category.assoc, (cubeMapOf hπ).psum_comm, Category.assoc] }
  have H2 : c2.IsPullCubical tK.cub cub :=
    pullCubComp _ _ _ _ _ _ cm b.cm c2 _ _ _ _ _ _ rfl rfl rfl hcm b.lin
  have h₁ : c2.F = a.cm.F ≫ (cubeMapOf hπ).F := by
    show b.cm.F ≫ cm.F = a.cm.F ≫ πC
    rw [hcF]; exact hab.symm
  have h₂ : c2.F3 = a.cm.F3 ≫ (cubeMapOf hπ).F3 := by
    show c2.F3 = c3.F3
    refine hom_ext_triple _ fun i => ?_
    rw [cubeMap_comp_proj_three c2 i, cubeMap_comp_proj_three c3 i]
    exact congrArg (fun z => (x3 tK.G i).left ≫ z) h₁
  have h₃ : c2.e = a.cm.e ≫ (cubeMapOf hπ).e := by
    show b.cm.e ≫ cm.e = a.cm.e ≫ ξ
    rw [b.base, hce, a.base, hy]
  exact GlobalTheory.ChartCubExt.isPullCubical_of_generic_of_ext (GlobalTheory.T.extendsGenericRigidifiedGenerator_toricChartPowerSeriesRing k m n) tC.semi cub tC.cub tK.cub
    (cubeMapOf hπ) a.cm c2 a.cart.1 a.base h₁ h₂ h₃ a.lin H2

end GlobalTheory.ChartCubExt
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_etaleCompletion_with_residueField_equiv : ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [IsIntegrallyClosed O] [CharZero O] [Algebra.EssFiniteType ℤ O] (M : Type) [Field M] (m : ResidueField O →+* M), m.Finite → m.FormallyUnramified → ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : IsLocalRing A) (ψ : O →+* A) (_ : IsLocalHom ψ) (E : M ≃+* ResidueField A), IsCN A ∧ IsEtaleCompletion ψ ∧ ((residue A).comp ψ).FormallyUnramified ∧ (E : M →+* ResidueField A).comp m = ResidueField.map ψ := by
  first | exact @GlobalTheory.EtaleCompletionResidue.exists_etaleCompletion_residue_equiv | exact GlobalTheory.EtaleCompletionResidue.exists_etaleCompletion_residue_equiv | (intros; apply GlobalTheory.EtaleCompletionResidue.exists_etaleCompletion_residue_equiv <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.symmetric_balanced_tensors_finite_projective_rank_dim : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → ∀ (U : Y.X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → (∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left)) → Module.Finite Γ(Y.X, U.1) (balanced H.bar A) ∧ Module.Projective Γ(Y.X, U.1) (balanced H.bar A) ∧ ∀ m : Ideal Γ(Y.X, U.1), m.IsMaximal → Module.finrank (Γ(Y.X, U.1) ⧸ m) ((Γ(Y.X, U.1) ⧸ m) ⊗[Γ(Y.X, U.1)] (balanced H.bar A)) = Dw.dim := by
  first | exact @GlobalTheory.BalProj.balanced_finite_projective_rank | exact GlobalTheory.BalProj.balanced_finite_projective_rank | (intros; apply GlobalTheory.BalProj.balanced_finite_projective_rank <;> assumption)
end

section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem polFn_cell_eq_min_integral : ∀ (g : ℕ) (φ : InvFun ℤ), IsPolFan id g φ → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), PosW W → ∀ (N : ℕ) [NeZero N], 3 ≤ N → (∃ ε : Fin 8 → ℤ, Nat.Coprime N (2 * (∑ u, ∑ v, W u v * ε u * ε v).natAbs)) → ∀ r : ℕ, r ≤ g → ∀ μ : ((Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ)), (∀ c u i, ((μ c u i : ℤ) : ZMod N) = c u i) → ∀ b₀ : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ x y, b₀ x y = b₀ y x) → (∀ x, x ≠ 0 → 0 < b₀ x x) → (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W b₀ (μ c) ≤ qW W b₀ α) → ∃ (ι : ℕ) (L : Finset ((Fin 8 → Fin r → ZMod N) → ℤ)), 1 ≤ ι ∧ ∀ (b' : LinearMap.BilinForm ℤ (Fin r → ℤ)), (∀ x y, b' x y = b' y x) → (∀ x, 0 ≤ b' x x) → (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W b' (μ c) ≤ qW W b' α) → (∀ ν ∈ L, (ι * N : ℝ) * φ.evalZ b' ≤ ∑ c, (ν c : ℝ) * qW W b' (μ c)) ∧ ∃ ν ∈ L, (ι * N : ℝ) * φ.evalZ b' = ∑ c, (ν c : ℝ) * qW W b' (μ c) := by
  classical
  intro g φ hφ W hW N _ hN3 hε r hr μ hμ b₀ hsym hpos hmin
  obtain ⟨p, m, γ, hcone, hcov⟩ := GlobalTheory.T.exists_finite_cones_siegel_level_structure g φ hφ W hW N hN3 r hr μ hμ b₀ hsym hpos hmin
  obtain ⟨Nℓ, ℓ, hNℓ, hℓ⟩ := polFn_eq_min_linear g φ hφ r hr p m γ hcone
  choose D ν hD hν using fun i : Fin p => GlobalTheory.T.linForm_bilinForms_eq_sum_minimiser_values W hW N hN3 hε r μ hμ (ℓ i)
  obtain ⟨E, hDE⟩ : ∃ E : Fin p → ℕ, ∀ i, D i * E i = ∏ j, D j :=
    ⟨fun i => ∏ j ∈ Finset.univ.erase i, D j, fun i => Finset.mul_prod_erase _ _ (Finset.mem_univ i)⟩
  have hDp : 0 < ∏ j, D j := Finset.prod_pos (fun j _ => hD j)
  refine ⟨Nℓ * ∏ j, D j, Finset.univ.image (fun i c => (N : ℤ) * (E i : ℤ) * ν i c), ?_, ?_⟩
  · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hNℓ.ne' hDp.ne')
  intro b' hs hp hm
  obtain ⟨i0, k, cf, hk, hkb⟩ := hcov b' hs hp hm
  obtain ⟨hle, i1, heq⟩ := hℓ b' hs hp ⟨i0, k, cf, hk, hkb⟩
  have key : ∀ i, ∑ c, ((((N : ℤ) * (E i : ℤ) * ν i c : ℤ)) : ℝ) * ((qW W b' (μ c) : ℤ) : ℝ)
      = ((N : ℝ) * (E i : ℝ) * (D i : ℝ)) * ((ℓ i b' : ℤ) : ℝ) := by
    intro i
    have h' : (((∑ c, ν i c * qW W b' (μ c) : ℤ)) : ℝ) = (((D i : ℤ) * ℓ i b' : ℤ) : ℝ) := by
      rw [hν i b' hs]
    push_cast at h' ⊢
    calc ∑ c, (N : ℝ) * (E i : ℝ) * (ν i c : ℝ) * (qW W b' (μ c) : ℝ)
        = (N : ℝ) * (E i : ℝ) * ∑ c, (ν i c : ℝ) * (qW W b' (μ c) : ℝ) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun c _ => ?_); ring
      _ = _ := by rw [h']; ring
  have hι : ∀ i, ((Nℓ * ∏ j, D j : ℕ) : ℝ) * (N : ℝ)
      = ((N : ℝ) * (E i : ℝ) * (D i : ℝ)) * (Nℓ : ℝ) := by
    intro i; rw [← hDE i]; push_cast; ring
  refine ⟨fun ν' hν' => ?_, ?_⟩
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hν'
    have hc : (0 : ℝ) ≤ (N : ℝ) * (E i : ℝ) * (D i : ℝ) := by positivity
    calc ((Nℓ * ∏ j, D j : ℕ) : ℝ) * (N : ℝ) * φ.evalZ b'
        = ((N : ℝ) * (E i : ℝ) * (D i : ℝ)) * ((Nℓ : ℝ) * φ.evalZ b') := by rw [hι i]; ring
      _ ≤ ((N : ℝ) * (E i : ℝ) * (D i : ℝ)) * ((ℓ i b' : ℤ) : ℝ) := mul_le_mul_of_nonneg_left (hle i) hc
      _ = _ := (key i).symm
  · refine ⟨_, Finset.mem_image.mpr ⟨i1, Finset.mem_univ _, rfl⟩, ?_⟩
    calc ((Nℓ * ∏ j, D j : ℕ) : ℝ) * (N : ℝ) * φ.evalZ b'
        = ((N : ℝ) * (E i1 : ℝ) * (D i1 : ℝ)) * ((Nℓ : ℝ) * φ.evalZ b') := by rw [hι i1]; ring
      _ = ((N : ℝ) * (E i1 : ℝ) * (D i1 : ℝ)) * ((ℓ i1 b' : ℤ) : ℝ) := by rw [heq]
      _ = _ := (key i1).symm

end GlobalTheory.Poinc
end

section

open NumberField Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CovTop

theorem _root_.GlobalTheory.T.existsUnique_cuspForm_pullback_goodCover : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), LawsJ T → InR D j → Y.Good e o → (∀ σ, GoodEmb Y.d.c₂ σ → ∀ g τ k, ‖dmin ((Y.U σ).X (Y.dict σ g).1).Gm (Y.dict σ g).2 τ k‖ = 1) → (∀ σ, GoodEmb Y.d.c₂ σ → ∃ hr : (D.sp.W j).rank = D.R.r, ∀ k, ModelW (D.sp.W j) hr ((Y.U σ).X k)) → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ f ∈ cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n), ∃! g, g ∈ Y.V (wtZ a n) ∧ Y.Pull f g := by
  first | exact @GlobalTheory.CoverPull.cusp_pullback_existsUnique | exact GlobalTheory.CoverPull.cusp_pullback_existsUnique | (intros; apply GlobalTheory.CoverPull.cusp_pullback_existsUnique <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_finiteExtension_splitClosedFibre_rationalTwoTorsion : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R'), GlobalTheory.LN.CDvr R' ∧ FinExt ρ ∧ ∀ (G₁ : Over (Sp R')) [GrpObj G₁] [IsCommMonObj G₁] (β : G₁.left ⟶ G.left), IsGrpPullback G₁ G (spMap ρ) β → SplitClosed G₁ ∧ TwoTorsRat G₁ := by
  first | exact @GlobalTheory.Mum.exists_finExt_splitClosed_twoTorsRat | exact GlobalTheory.Mum.exists_finExt_splitClosed_twoTorsRat | (intros; apply GlobalTheory.Mum.exists_finExt_splitClosed_twoTorsRat <;> assumption)
end
