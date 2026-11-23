module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle022
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle073
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle026
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2997
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2527
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1206
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2593
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle932
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1090
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle033
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1132
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1424
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2911
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1135
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGt
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

namespace GlobalTheory.TwFam

theorem formEq_pull {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (a : D.P.A ⟶ D.P.A) (k : ℕ) (α δ : D.X) :
    FormEq (Sum.elim (fun i => a.left ≫ D.famφB α i) (Sum.elim (D.Oφ (𝟙 D.P.A) δ) (D.Oφ a α)))
      (Sum.elim (DegPre.famε k) (Sum.elim Oε Oinvε)) (tφ D a δ) (tε 0 k) := by
  intro U _ h
  have e₁ : a.left ≫ (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c α)).left = (padd D.P.A a (toUnit _ ≫ D.c α)).left := by
    rw [← Over.comp_left, padd, padd, ← Category.assoc, comp_lift, Category.comp_id, ← Category.assoc, comp_toUnit]
  have e₂ : a.left ≫ (toUnit D.P.A ≫ D.c α).left = (toUnit D.P.A ≫ D.c α).left := by
    rw [← Over.comp_left, ← Category.assoc, comp_toUnit]
  have e₃ : a.left ≫ (toUnit D.P.A ≫ η[D.P.A]).left = (toUnit D.P.A ≫ η[D.P.A]).left := by
    rw [← Over.comp_left, ← Category.assoc, comp_toUnit]
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ, Fin.prod_univ_zero, DegPre.famφB,
    DegPre.Oφ, tφ, tε, DegPre.famε, Oε, Oinvε, Matrix.cons_val_zero, Matrix.cons_val_succ, e₁, e₂, e₃,
    Category.comp_id, Over.id_left]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, ofMul_one]
  module

theorem exists_isPullT : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (k : ℕ) (α δ : D.toPre.X) (u : LB.Gen (IotaLB D.toPre a α δ)) (f : D.toPre.SecB k α), u.IsGen → ∃ s : SecT D.toPre a 0 k δ, IsPullT u f s ∧ ∀ e, VanMod (maximalIdeal R) f e → Van (maximalIdeal R) s e := by
  intro R _ _ _ _ D a k α δ u f hu
  obtain ⟨s, hs⟩ := exists_sec D.toPre.P.isLB (formEq_pull D.toPre a k α δ) (pullMulSec f a.left u hu)
  have hp : IsPullT u f s := fun Z x z J hJ => (hs Z x z J hJ).trans (sval_pullMulSec f a.left u hu x z hJ)
  refine ⟨s, hp, fun e hb Z x z J hJ => ?_⟩
  obtain ⟨h, hh⟩ : ∃ h : Z ⟶ pullback D.toPre.P.A.hom (thick R (maximalIdeal R) e),
      h ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e) =
        (x ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e)) ≫ a.left :=
    ⟨pullback.lift _ (x ≫ pullback.snd D.toPre.P.A.hom (thick R (maximalIdeal R) e)) (by
      rw [Category.assoc, Over.w, Category.assoc, Category.assoc, pullback.condition]), pullback.lift_fst _ _ _⟩
  have z₁ : sval f ((x ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e)) ≫ a.left) z J = 0 := by
    rw [← hh]
    have hm := hJ.mem (D.toPre.famφB α) (h ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e))
    exact (gs_pull h _ z _ hm _).symm.trans ((congrArg (gs h z _) (hb _)).trans (DVR.gs_zero h z _ hm))
  rw [hp Z _ z J hJ, z₁, zero_mul]

end GlobalTheory.TwFam
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

noncomputable section

namespace GlobalTheory.TwFam.PullRel

variable {R : Type} [CommRing R] [IsDomain R]

theorem prod_tφ (D : DegPre R) (a : D.P.A ⟶ D.P.A) {T : Over (Sp R)} (ρ : T ⟶ D.P.A) (β : D.X) (n j : ℤ)
    {U : Type} [CommGroup U] (hh : (T.left ⟶ D.P.A.left) → U) :
    ∏ i, hh (ρ.left ≫ tφ D a β i) ^ tε n j i = hh ρ.left ^ (n - 1) * hh (DVR.cP D T β * ρ).left *
      (hh (DVR.cP D T β).left)⁻¹ * hh (1 : T ⟶ D.P.A).left * hh (ρ ≫ a).left ^ j := by
  have e₁ : ρ.left ≫ tφ D a β 1 = (DVR.cP D T β * ρ).left :=
    congrArg (fun q => q.left) ((MonObj.comp_mul ρ (𝟙 D.P.A) (toUnit _ ≫ D.c β)).trans (by
      rw [Category.comp_id, ← DVR.cP, DVR.comp_cP, mul_comm]))
  have e₂ : ρ.left ≫ tφ D a β 2 = (DVR.cP D T β).left := congrArg (fun q => q.left) (DVR.comp_cP D ρ β)
  have e₃ : ρ.left ≫ tφ D a β 3 = (1 : T ⟶ D.P.A).left :=
    congrArg (fun q : T ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) ρ)
  have e₀ : ρ.left ≫ tφ D a β 0 = ρ.left := Category.comp_id _
  have e₄ : ρ.left ≫ tφ D a β 4 = (ρ ≫ a).left := rfl
  rw [Fin.prod_univ_five, e₀, e₁, e₂, e₃, e₄]
  show _ ^ (n - 1) * _ ^ (1 : ℤ) * _ ^ (-1 : ℤ) * _ ^ (1 : ℤ) * _ ^ j = _
  rw [zpow_one, zpow_one, zpow_neg_one]

end GlobalTheory.TwFam.PullRel

namespace GlobalTheory.TwFam.PullRel

variable {R : Type} [CommRing R] [IsDomain R]

theorem iota_c (D : DegPre R) (a a' : D.P.A ⟶ D.P.A) (h h' : D.X →+ D.X) (hE : EndData D a a' h h') (α mu : D.X)
    (u : LB.Gen (IotaLB D a α (h' α))) (hu : IsIota u) (Z : Scheme.{0}) (r : Z ⟶ (TK R).left) (z : Z) (J)
    (hJ : Good D.P.L z J) :
    val (D.tau (h mu) α) r z J = val (D.tau mu (h' α)) r z J * val u (r ≫ D.xK mu) z J := by
  have hG := GlobalTheory.globalFns_holds
  obtain ⟨hma, hma', hr, -, hc, hB⟩ := hE
  obtain ⟨t, ht, t₀⟩ := exists_ros hG D.P.isAb D.P.isLB a a' hr
  have cf : ∀ T, DVR.cP D T (h' α) = DVR.cP D T α ≫ a' := fun T => by
    rw [DVR.cP, hc, ← Category.assoc]; rfl
  have key := gen_unique' D.P.isLB (φ := Sum.elim (D.Oφ (𝟙 _) (h' α)) (D.Oφ a α)) (ε := Sum.elim Oε Oinvε)
    (u' := LB.invGen D.P.L _ _ (LB.pullGen D.P.L _ _ t (lift (𝟙 D.P.A) (DVR.cP D D.P.A α)).left))
    (fun U _ h => by
      refine (DVR.prod_neg _ _ (prod_ros a a' (𝟙 D.P.A) (DVR.cP D _ α) h)).trans (Eq.symm ?_)
      refine (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ (GlobalTheory.UT.OLinEnd.prod_Oφ D (𝟙 _) _ h)
        (GlobalTheory.UT.OLinEnd.prod_Oφ_inv D a α h)).trans ?_
      rw [cf, Category.id_comp, _root_.mul_comm (DVR.cP D _ α) a, _root_.mul_comm (DVR.cP D _ α ≫ a') (𝟙 _)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    D.P.A.hom (eSec D.P.A) (Over.w η[D.P.A]) (hG _ _ D.P.isAb).2 hu.1
    (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _)) (fun y I hI => by
      let T : Over (Spec (CommRingCat.of R)) := Over.mk (𝟙 _)
      have C : IsCub (cubV D.cub (T := T) y I) := isCub_cubV D.cub hI
      have e := (ros_add D.cub hG D.P.isAb a a' t ht t₀ (T := T) hI 1 1 (DVR.cP D _ α)).1
      rw [_root_.mul_one, MonObj.one_comp, C.face, C.face, _root_.mul_one, _root_.one_mul] at e
      have e' : val₂ t (T := T) y I 1 (DVR.cP D _ α) = 1 := mul_eq_left.1 e.symm
      have o : (1 : T ⟶ D.P.A).left = eSec D.P.A := Category.id_comp _
      have k : eSec D.P.A ≫ (lift (𝟙 D.P.A) (DVR.cP D D.P.A α)).left = (lift (1 : T ⟶ D.P.A) (DVR.cP D T α)).left := by
        rw [← o, ← Over.comp_left, comp_lift, DVR.comp_cP, Category.comp_id]
      have n := hu.2 _ (𝟙 _) y I hI
      rw [Category.id_comp] at n
      rw [val_inv, val_pull hI, k]
      exact n.trans (inv_eq_one.2 e').symm) Z (r ≫ D.xK mu) z J hJ
  have m : D.xK mu ≫ (lift (𝟙 D.P.A) (DVR.cP D D.P.A α)).left = D.pt2 mu α := by
    rw [← Over.comp_left, comp_lift, DVR.comp_cP, Category.comp_id]; rfl
  have b := (val_mul hJ _ _ _).symm.trans (val_corr hJ (hB t ht t₀ mu α) r)
  rw [val_pull hJ] at b
  rw [val_inv, val_pull hJ, Category.assoc, m] at key
  rw [key, ← b, mul_inv_cancel_right]

end GlobalTheory.TwFam.PullRel

namespace GlobalTheory.TwFam.PullRel

variable {R : Type} [CommRing R] [IsDomain R]

theorem formEq_pull (D : DegPre R) (a : D.P.A ⟶ D.P.A) (k : ℕ) (mu ν α β β' : D.X)
    (aK : DegPre.BF D (FractionRing R) ⟶ DegPre.BF D (FractionRing R))
    (h₁ : aK ≫ DegPre.prB D (FractionRing R) = DegPre.prB D (FractionRing R) ≫ a)
    (h₂ : aK ≫ DegPre.trF D (FractionRing R) ν ≫ DegPre.prB D (FractionRing R) =
      DegPre.trF D (FractionRing R) mu ≫ DegPre.prB D (FractionRing R) ≫ a) :
    FormEq (Sum.elim (Sum.elim (fun i => aK.left ≫ DegPre.deltaφ D (FractionRing R) k α ν i)
        (fun i => (DegPre.prB D (FractionRing R)).left ≫
          Sum.elim (D.Oφ (𝟙 D.P.A) β') (D.Oφ a (α + k • ν)) i))
        (fun i => (DegPre.trF D (FractionRing R) mu ≫ DegPre.prB D (FractionRing R)).left ≫
          Sum.elim (D.Oφ (𝟙 D.P.A) β) (D.Oφ a α) i))
      (Sum.elim (Sum.elim (DegPre.deltaε k) (Sum.elim Oε Oinvε)) (fun i => - Sum.elim Oε Oinvε i))
      (dφ D a mu β β') (dε 0 k) := by
  intro U _ hh
  have io : ∀ (ρ : DegPre.BF D (FractionRing R) ⟶ D.P.A) (ξ δ : D.X),
      ∏ i, hh (ρ.left ≫ Sum.elim (D.Oφ (𝟙 D.P.A) δ) (D.Oφ a ξ) i) ^ Sum.elim Oε Oinvε i =
        (hh (DVR.cP D _ δ * ρ).left * (hh (DVR.cP D _ δ).left)⁻¹ * (hh ρ.left)⁻¹ *
          hh (1 : DegPre.BF D (FractionRing R) ⟶ D.P.A).left) *
        ((hh (DVR.cP D _ ξ * (ρ ≫ a)).left)⁻¹ * hh (DVR.cP D _ ξ).left * hh (ρ ≫ a).left *
          (hh (1 : DegPre.BF D (FractionRing R) ⟶ D.P.A).left)⁻¹) := fun ρ ξ δ => by
    refine DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ ?_ ?_
    · simp only [Sum.elim_inl, WeightPf.Oφ_comp, Category.comp_id]
      exact GlobalTheory.UT.OLinEnd.prod_Oφ D ρ δ hh
    · simp only [Sum.elim_inr, WeightPf.Oφ_comp]
      exact GlobalTheory.UT.OLinEnd.prod_Oφ_inv D (ρ ≫ a) ξ hh
  have p₁ := DVR.prod_fam D (FractionRing R) aK (α + k • ν) k hh
  have p₂ := DVR.prod_fam D (FractionRing R) (aK ≫ DegPre.trF D (FractionRing R) ν) α k hh
  have q₁ := prod_tφ D a (DegPre.prB D (FractionRing R)) β' 0 k hh
  have q₂ := prod_tφ D a (DegPre.trF D (FractionRing R) mu ≫ DegPre.prB D (FractionRing R)) β 0 k hh
  rw [h₁] at p₁
  rw [Category.assoc, h₂, ← Category.assoc] at p₂
  simp only [Over.comp_left, Category.assoc] at p₂ q₂
  refine (DVR.prod_sum₂ (K := (Fin 4 ⊕ Fin 4) ⊕ (Fin 4 ⊕ Fin 4)) (K' := Fin 4 ⊕ Fin 4) (U := U) _
    (DVR.prod_sum₂ (K := Fin 4 ⊕ Fin 4) (K' := Fin 4 ⊕ Fin 4) (U := U) _
      (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ p₁ (DVR.prod_neg _ _ p₂)) (io _ _ _))
    (DVR.prod_neg _ _ (io _ _ _))).trans
    (Eq.trans ?_ (DVR.prod_sum₂ (K := Fin 5) (K' := Fin 5) (U := U) _ q₁ (DVR.prod_neg _ _ q₂)).symm)
  simp only [Over.comp_left, Category.assoc]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  module

end GlobalTheory.TwFam.PullRel

namespace GlobalTheory.TwFam.PullRel

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (k : ℕ) (F : IntFam (maximalIdeal R) D.toPre k) (mu α : D.toPre.X) (u : LB.Gen (IotaLB D.toPre a α (h' α))) (u' : LB.Gen (IotaLB D.toPre a (α + k • h mu) (h' (α + k • h mu)))) (s : SecT D.toPre a 0 k (h' α)) (s' : SecT D.toPre a 0 k (h' (α + k • h mu))), IsIota u → IsIota u' → IsPullT u (F.f α) s → IsPullT u' (F.f (α + k • h mu)) s' → TRel h mu s s' := by
  intro R _ _ _ _ D a a' h h' hE k F mu α u u' s s' hu hu' hs hs'
  have hG := GlobalTheory.globalFns_holds
  obtain ⟨hma, -, -, hch, -, -⟩ := id hE
  have hL := D.toPre.P.isLB
  obtain ⟨⟨uF, huF, hcF⟩, -⟩ := DVR.gen_fe (D := D.toPre) (F := FractionRing R) hG k (h mu) α
  have feF := (secRel_iff hL _ _ _ _ _ _ _ _ _ uF).1 (F.F.fe (h mu) α uF huF hcF)
  have h1 : scal (DegPre.BF D.toPre (FractionRing R)).hom (1 : R) = 1 := by unfold scal; rw [map_one, map_one]
  have ext : ∀ β (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D.toPre (FractionRing R)).left) (z : Z) (J), Good D.toPre.P.L z J →
      sval (F.F.s β) r z J = sval (F.f β) (r ≫ (DegPre.prB D.toPre (FractionRing R)).left) z J := by
    intro β Z r z J hJ
    have e := F.ext β
    rw [h1] at e
    exact (DVR.SectionScalarValuation.secScal_sval e r z hJ).symm
  let aK : DegPre.BF D.toPre (FractionRing R) ⟶ DegPre.BF D.toPre (FractionRing R) :=
    lift (fst _ _) (DegPre.prB D.toPre (FractionRing R) ≫ a)
  have aK_pr : aK ≫ DegPre.prB D.toPre (FractionRing R) = DegPre.prB D.toPre (FractionRing R) ≫ a := lift_snd _ _
  have aK_fst : aK ≫ fst _ _ = fst _ _ := lift_fst _ _
  have cPh : ∀ T, DVR.cP D.toPre T (h mu) = DVR.cP D.toPre T mu ≫ a := fun T => by
    rw [DVR.cP, hch, ← Category.assoc]; rfl
  have trpr : ∀ ν, DegPre.trF D.toPre (FractionRing R) ν ≫ DegPre.prB D.toPre (FractionRing R) =
      DegPre.prB D.toPre (FractionRing R) * DVR.cP D.toPre _ ν := fun ν => by
    rw [DVR.trF_eq, DVR.tr_pr, DVR.comp_cP]
  have M1 : aK ≫ DegPre.trF D.toPre (FractionRing R) (h mu) ≫ DegPre.prB D.toPre (FractionRing R) =
      DegPre.trF D.toPre (FractionRing R) mu ≫ DegPre.prB D.toPre (FractionRing R) ≫ a := by
    haveI := hma
    rw [trpr, MonObj.comp_mul, aK_pr, DVR.comp_cP, ← Category.assoc, trpr, MonObj.mul_comp, cPh]
  haveI := hma
  have z₁ : DegPre.zF D.toPre (FractionRing R) ≫ fst _ _ = 𝟙 _ := lift_fst _ _
  have z₂ : DegPre.zF D.toPre (FractionRing R) ≫ DegPre.prB D.toPre (FractionRing R) = 1 := lift_snd _ _
  have M2 : DegPre.zF D.toPre (FractionRing R) ≫ aK = DegPre.zF D.toPre (FractionRing R) := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, aK_fst]
    · rw [Category.assoc, aK_pr, ← Category.assoc, z₂, MonObj.one_comp]
  have M3 : DegPre.zF D.toPre (FractionRing R) ≫ DegPre.trF D.toPre (FractionRing R) mu ≫
      DegPre.prB D.toPre (FractionRing R) = DVR.cP D.toPre _ mu := by
    rw [trpr, MonObj.comp_mul, z₂, DVR.comp_cP, _root_.one_mul]
  intro v hv Z x z J hJ
  have wv : ∀ (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF D.toPre (FractionRing R)).left) (z : Z) (J), Good D.toPre.P.L z J →
      val (LB.mulGen _ _ _ _ _ (LB.mulGen _ _ _ _ _ (LB.pullGen _ _ _ uF aK.left)
        (LB.pullGen _ _ _ u' (DegPre.prB D.toPre (FractionRing R)).left)) (LB.invGen _ _ _ (LB.pullGen _ _ _ u
          (DegPre.trF D.toPre (FractionRing R) mu ≫ DegPre.prB D.toPre (FractionRing R)).left))) x z J =
      val uF (x ≫ aK.left) z J * val u' (x ≫ (DegPre.prB D.toPre (FractionRing R)).left) z J *
        (val u (x ≫ (DegPre.trF D.toPre (FractionRing R) mu ≫ DegPre.prB D.toPre (FractionRing R)).left) z J)⁻¹ :=
    fun Z x z J hJ => by rw [val_mul hJ, val_mul hJ, val_inv, val_pull hJ, val_pull hJ, val_pull hJ]
  have key := (gen_unique' hL (formEq_pull D.toPre a k mu (h mu) α (h' α) (h' (α + k • h mu)) aK aK_pr M1)
    (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left (DegPre.zF D.toPre (FractionRing R)).left
    (congrArg (fun q => q.left) z₁) (DVR.surj_appTop D.toPre _ hG) hv.1
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ huF _)
      (DVR.pullGen_isGen _ _ _ _ hu'.1 _)) (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu.1 _)))
    (fun y I hI => by
      have e₁ := val_corr hI hcF (𝟙 _)
      rw [val_pull hI, Category.id_comp] at e₁
      have e₂ := DVR.val_famMult (D := D.toPre) (F := FractionRing R) (𝟙 _) hI k (h mu) α
      rw [Over.id_left, Category.id_comp, DVR.TWM.val_powGen, DVR.TWM.val_powGen] at e₂
      have e₃ : val u' (1 : TF (R := R) (FractionRing R) ⟶ D.toPre.P.A).left y I = 1 :=
        hu'.2 _ (TF (R := R) (FractionRing R)).hom y I hI
      have e₄ := iota_c D.toPre a a' h h' hE α mu u hu _ (jFK (R := R) (FractionRing R)) y I hI
      have e₅ : jFK (R := R) (FractionRing R) ≫ D.toPre.xK mu = (DVR.cP D.toPre (TF (R := R) (FractionRing R)) mu).left :=
        (Category.assoc _ _ _).symm
      rw [wv _ _ y I hI, hv.2 y I hI, ← Over.comp_left, ← Over.comp_left, ← Over.comp_left, M2, z₂, M3, e₁, e₂, e₃, e₄, e₅]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one]
      module) Z x z J hJ).trans (wv Z x z J hJ)
  have f₁ : (x ≫ (DegPre.prB D.toPre (FractionRing R)).left) ≫ a.left =
      (x ≫ aK.left) ≫ (DegPre.prB D.toPre (FractionRing R)).left := by
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, aK_pr]
  have f₂ : ((x ≫ aK.left) ≫ (DegPre.trF D.toPre (FractionRing R) (h mu)).left) ≫ (DegPre.prB D.toPre (FractionRing R)).left =
      (x ≫ (DegPre.trF D.toPre (FractionRing R) mu).left ≫ (DegPre.prB D.toPre (FractionRing R)).left) ≫ a.left := by
    have := congrArg (fun q => x ≫ q.left) M1
    simpa only [Over.comp_left, Category.assoc] using this
  rw [hs' _ _ z J hJ, hs _ _ z J hJ, key, f₁, ← ext _ _ _ z J hJ, feF _ _ z J hJ, ext _ _ _ z J hJ, f₂, Over.comp_left,
    _root_.mul_assoc, _root_.mul_assoc, ← Units.val_mul, ← Units.val_mul, mul_comm (val u _ z J), inv_mul_cancel_right]

end GlobalTheory.TwFam.PullRel
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualConStep

def conductor (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] : Ideal R where
  carrier := {x | ∀ r : R', ∃ y : R, algebraMap R R' y = algebraMap R R' x * r}
  add_mem' {x x'} hx hx' r := by
    obtain ⟨y, hy⟩ := hx r
    obtain ⟨y', hy'⟩ := hx' r
    exact ⟨y + y', by rw [map_add (f := _), map_add (f := _), hy, hy', add_mul]⟩
  zero_mem' r := ⟨0, by simp⟩
  smul_mem' b {x} hx r := by
    obtain ⟨y, hy⟩ := hx r
    exact ⟨b * y, by rw [smul_eq_mul, map_mul, map_mul, hy, _root_.mul_assoc]⟩

theorem conductor_mul {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] :
    ∀ x ∈ conductor R R', ∀ r : R', ∃ y ∈ conductor R R', algebraMap R R' y = algebraMap R R' x * r := by
  intro x hx r
  obtain ⟨y, hy⟩ := hx r
  refine ⟨y, fun r' ↦ ?_, hy⟩
  obtain ⟨z, hz⟩ := hx (r * r')
  exact ⟨z, by rw [hz, hy, _root_.mul_assoc]⟩

theorem hasRepAF_factor (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) (V : A.left.Opens) (hV : IsAffineOpen V)
    (hVs : ∀ s : Sp R, ∃ x ∈ V, A.hom x = s) (D : Type) [CommRing D] [Algebra R D] [IsNoetherianRing D]
    [IsDomain D] [IsIntegrallyClosed D] :
    HasRepAF A g (Over.mk (spMap (algebraMap R D))) := by
  set f := algebraMap R D
  have hP := isGrpPullback_pullback A (spMap f)
  obtain ⟨hA', hg'⟩ := GlobalTheory.AbBaseChange.isAbelianScheme_and_relDim_of_isGrpPullback f A
    ((Over.pullback (spMap f)).obj A) _ g hP hA hg
  haveI : IsAffineHom (pullback.fst A.hom (spMap f)) :=
    (AlgebraicGeometry.isAffineHom_isStableUnderBaseChange.{0}).of_isPullback (IsPullback.of_hasPullback _ _).flip
      (inferInstance : IsAffineHom (spMap f))
  have hV' : IsAffineOpen (pullback.fst A.hom (spMap f) ⁻¹ᵁ V) := hV.preimage _
  have hVs' : ∀ s : Sp D, ∃ x ∈ pullback.fst A.hom (spMap f) ⁻¹ᵁ V,
      ((Over.pullback (spMap f)).obj A).hom x = s := by
    intro s
    obtain ⟨x, hx, hxs⟩ := hVs (spMap f s)
    obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback x s hxs
    exact ⟨z, by simpa [hz1] using hx, hz2⟩
  obtain ⟨L, hL, hLa⟩ := GlobalTheory.T.exists_relAmple_of_affineOpen_meets_fibres D _ hA' _ hV' hVs'
  have h1 := GlobalTheory.T.hasDualRepresentative_of_relAmple_noetherian D _ g hA' hg' L hL hLa
  have h2 := ((GlobalTheory.T.hasProperSmoothDualRepresentative_grpPullback_iff _ _ (spMap f) A _ _ hP g (𝟙_ _)).2).1 h1
  simpa using h2

theorem step : ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R] [IsReduced R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ V : A.left.Opens, IsAffineOpen V → (∀ s : Sp R, ∃ x ∈ V, A.hom x = s) → (∀ J : Ideal R, J ≠ ⊥ → HasRep A g (Over.mk (spMap (Ideal.Quotient.mk J)))) → HasRep A g (𝟙_ _) := by
  intro R _ _ _ A _ g hA hg V hV hVs hJ
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  rcases subsingleton_or_nontrivial R with hR | hR
  · haveI : IsEmpty (𝟙_ (Over (Sp R))).left := inferInstanceAs (IsEmpty (PrimeSpectrum R))
    obtain ⟨B, b, P, hP, hG, -⟩ := GlobalTheory.T.hasProperSmoothDualRepresentativeFinAffine_of_isEmpty _ A (𝟙_ _) g this
    exact ⟨B, b, P, hP, hG⟩
  obtain ⟨n, D, iR, iA, hD, hinj, a, ha0, ha⟩ := GlobalTheory.T.reduced_finiteType_int_exists_finite_prod_normalDomains_nonzero_conductor R
  have hfac : ∀ i, HasRepAF A g (Over.mk (spMap (algebraMap R (D i)))) := by
    intro i
    obtain ⟨h1, h2, h3⟩ := hD i
    haveI : IsNoetherianRing (D i) := by
      haveI : Algebra.FiniteType R (D i) := inferInstance
      exact Algebra.FiniteType.isNoetherianRing R (D i)
    exact hasRepAF_factor R A g hA hg V hV hVs (D i)
  haveI : ∀ i, Module.Finite R (D i) := fun i ↦ (hD i).2.2
  have hprod := GlobalTheory.T.hasProperSmoothDualRep_of_finite_product_algebras R A g hA n D hfac
  have hac : a ∈ conductor R (∀ i, D i) := ha
  have hc : conductor R (∀ i, D i) ≠ ⊥ := fun h ↦ ha0 (by rw [h] at hac; exact (Submodule.mem_bot R).1 hac)
  exact GlobalTheory.T.hasRepresentingScheme_pinchedBase R A g hA hg (∀ i, D i) hinj _ conductor_mul hprod (hJ _ hc)

end GlobalTheory.DualConStep
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt.HodgeOrth

theorem fv_sum {R : Type} [CommRing R] {X : Over (Sp R)} {J : Type} (s : Finset J) (c : J → R)
    (α : J → Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))) (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D']
    [Algebra R D'] (φ : D →ₐ[R] D') (x : Pt X D) :
    fv (∑ i ∈ s, c i • α i) D D' φ x = ∑ i ∈ s, fv (α i) D D' φ x * algebraMap R D' (c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; rfl
  | insert i s hi ih =>
    obtain ⟨hadd, hsmul, _⟩ := GlobalTheory.T.crystallineCocycleOnTrivialThickenings_additive_linear R X
    rw [Finset.sum_insert hi, Finset.sum_insert hi, hadd, Fn1.add, hsmul, ih,
      mul_comm (algebraMap R D' (c i))]

theorem commAlgFunctorCocyclesTwo_finsetSum_apply {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {J : Type}
    (s : Finset J) (w : J → Z2 F) (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T'') :
    (∑ i ∈ s, w i).1 T T' T'' φ ψ = ∑ i ∈ s, (w i).1 T T' T'' φ ψ := by
  simp only [Submodule.coe_sum, Finset.sum_apply]

theorem sum_cup_eq_mk {R : Type} [CommRing R] {A B : Over (Sp R)} {N : ℕ}
    (m₁ : IsMor (dp0 R) (A.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (fst A B).left)
    (m₂ : IsMor (dp0 R) (B.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (snd A B).left)
    (α : Fin N → Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))) (β : Fin N → Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))) :
    (∑ k, cup _ (pullOver (dp0 R) (𝟙 _) (fst A B) (CatCoh.H1.mk _ (α k)))
      (pullOver (dp0 R) (𝟙 _) (snd A B) (CatCoh.H1.mk _ (β k)))) =
      CatCoh.H2.mk _ (∑ k, cupZ _ (m₁.coef.pullbackOneCocycle (α k)) (m₂.coef.pullbackOneCocycle (β k))) := by

  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [← cup_mk]
  rfl

theorem exists_isCupCob {R : Type} [CommRing R] {A B : Over (Sp R)} {N : ℕ} (P : LB (A ⊗ B).left)
    (α : Fin N → Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))) (β : Fin N → Z1 (O (dp0 R) (B.hom ≫ 𝟙 _)))
    (hc : IsChern (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) P
      (∑ k, cup _ (pullOver (dp0 R) (𝟙 _) (fst A B) (CatCoh.H1.mk _ (α k)))
        (pullOver (dp0 R) (𝟙 _) (snd A B) (CatCoh.H1.mk _ (β k))))) :
    ∃ n, IsCupCob P.U (fun i ↦ fv (α i)) (fun i ↦ fv (β i)) n := by
  have m₁ : IsMor (dp0 R) (A.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (fst A B).left :=
    IsMor.of_over _ (by rw [← Category.assoc, Over.w])
  have m₂ : IsMor (dp0 R) (B.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (snd A B).left :=
    IsMor.of_over _ (by rw [← Category.assoc, Over.w])
  rw [sum_cup_eq_mk m₁ m₂] at hc
  obtain ⟨n, hn⟩ := GlobalTheory.PtExt.exists_pointwiseCochain_coboundary_eq_chernCocycle R (A ⊗ B) P _ hc
  refine ⟨n, ?_⟩
  intro E _ _ E' _ _ E'' _ _ φ ψ z hz
  rw [hn E E' E'' φ ψ z hz, commAlgFunctorCocyclesTwo_finsetSum_apply]
  exact Finset.sum_congr rfl fun k _ ↦ GlobalTheory.T.cup_pullback_cocycles_pointValue R A B m₁ m₂ _ _ E E' E'' φ ψ z

theorem sum_mem_F1prim {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {N : ℕ} (a : Fin N → primDR A)
    (α : Fin N → Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))) (hα : ∀ i, CatCoh.H1.mk _ (α i) = (a i).1) (c : Fin N → R)
    (k : Fn0 A)
    (hk : IsCob (whole A) (fun D _ _ D' _ _ φ x ↦ ∑ i, fv (α i) D D' φ x * algebraMap R D' (c i)) k) :
    ∑ i, c i • a i ∈ PrimitiveSubmodule A := by
  have hF : CatCoh.H1.mk _ (∑ i, c i • α i) ∈ F1 (A.hom ≫ 𝟙 _) := by
    have hfv : fv (∑ i, c i • α i) =
        ((fun D _ _ D' _ _ φ x ↦ ∑ i, fv (α i) D D' φ x * algebraMap R D' (c i)) : Fn1 A) := by
      funext D _ _ D' _ _ φ x
      exact fv_sum Finset.univ c α D D' φ x
    apply (mem_hodgeFiltration_iff_pointwiseCoboundary R A _).2
    rw [hfv]
    exact ⟨k, hk⟩

  rw [map_sum] at hF
  simp only [map_smul, hα] at hF

  rw [PrimitiveSubmodule, Submodule.mem_comap, map_sum]
  exact hF

theorem fil_orthogonal : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ P : LB (A ⊗ B).left, P.IsLB → ∀ φ : HdR A →ₗ[R] HdR B →ₗ[R] R, AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ → ∀ x ∈ Fil A, ∀ y ∈ Fil B, φ x y = 0 := by
  intro H R _ A B _ _ g _ hB _ gB P hP φ hP' x hx y hy
  obtain ⟨N, a, b, hc, hφ⟩ := hP'
  choose α hα using fun k ↦ CatCoh.H1.mk_surjective _ (a k).1
  choose β hβ using fun k ↦ CatCoh.H1.mk_surjective _ (b k).1
  obtain ⟨n, hcup⟩ := exists_isCupCob P α β (by simp only [hα, hβ]; exact hc)
  have hβ' : ∀ i, CatCoh.H1.mk _ (β i) ∈ primDR B := fun i ↦ by rw [hβ]; exact (b i).2
  obtain ⟨k, hk⟩ := GlobalTheory.PtExt.OrthPt.exists_isCob_of_mem_fil H R A B g hB gB _ P.U hP.cover (Fin N) _ β hβ' n
    (fun i ↦ (fv_isCoc_and_ev_eq R A (α i)).1) hcup y hy
  have eb : ∀ i, (⟨_, hβ' i⟩ : primDR B) = b i := fun i ↦ Subtype.ext (hβ i)
  have h0 := (Submodule.mem_dualAnnihilator _).1 hx _ (sum_mem_F1prim a α hα _ k hk)

  rw [hφ, ← h0, map_sum]
  exact Finset.sum_congr rfl fun k _ ↦ by rw [map_smul, smul_eq_mul, mul_comm, eb]

end GlobalTheory.PtExt.HodgeOrth
end
end
