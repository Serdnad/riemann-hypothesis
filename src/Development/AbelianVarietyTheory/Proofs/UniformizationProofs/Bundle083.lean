module

import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle042
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle001
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle016
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle070
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ExistsGeneratorOfIsField
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle081
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle007
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Tactic.ENatToNat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNeZeroClosedFibre
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle060
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle076
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle045
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle016
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle021
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsAbelianSchemeOfAbelianThickenings

@[expose] public section

open AlgebraicGeometry CategoryTheory
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable local instance (priority := high) grpObjUniformizationPullback083
    {S T : Scheme.{0}} (f : T ⟶ S) (G : Over S) [GrpObj G] : GrpObj ((Over.pullback f).obj G) :=
  letI : (Over.pullback f).Monoidal := (Over.instBraidedPullback (f := f)).toMonoidal
  Functor.grpObjObj (F := Over.pullback f)

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section

namespace GlobalTheory.NormTheta

section General

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S}

theorem rigT_isGen {ρ : LB.Gen (L.pull (eSec A))} (hρ : ρ.IsGen) (k : ℤ) : (rigT A L ρ T k).IsGen := by
  apply _root_.GlobalTheory.UT.EvalLevel.rigT_isGen <;> assumption

theorem ptSec_fst : (ptSecT A (1 : T ⟶ A)).left ≫ (fst T A).left = 𝟙 T.left := by
  rw [← Over.comp_left, ptSecT, lift_fst]; rfl

theorem one_left : (1 : T ⟶ A).left = T.hom ≫ eSec A := rfl

theorem ptSec_snd : (ptSecT A (1 : T ⟶ A)).left ≫ (snd T A).left = T.hom ≫ eSec A := by
  rw [← Over.comp_left, ptSecT, lift_snd, one_left]

theorem ptSec_snd_pow (m : ℕ) : (ptSecT A (1 : T ⟶ A)).left ≫ (snd T A ^ m).left = T.hom ≫ eSec A := by
  rw [← Over.comp_left, MonObj.comp_pow, ptSecT, lift_snd, one_pow, one_left]

theorem exists_normalised (hL : L.IsLB) {ρ : LB.Gen (L.pull (eSec A))} (hρ : ρ.IsGen) (m : ℕ) (a b c : ℤ)
    (hc : c = a - b)
    (α₀ : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ m).left] ![a, -b])) (h₀ : α₀.IsGen) :
    ∃ α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ m).left] ![a, -b]), α.IsGen ∧
      LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ α (ptSecT A 1).left) (rigT A L ρ T c) := by
  obtain ⟨α, hα, hv⟩ := exists_gen hL (φ' := ![(snd T A).left, (snd T A ^ m).left]) (ε' := ![a, -b])
    (fun U _ f => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, ptSec_snd, ptSec_snd_pow, hc]
      rw [← zpow_add, ← zpow_add, show -a + - -b + (a - b) = 0 by ring, zpow_zero, _root_.mul_one])
    (LB.mulGen L _ _ _ _ α₀ (LB.pullGen L _ _ (LB.mulGen L _ _ _ _
      (LB.invGen L _ _ (LB.pullGen L _ _ α₀ (ptSecT A 1).left)) (rigT A L ρ T c)) (fst T A).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ h₀ (DVR.pullGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ h₀ _)) (rigT_isGen hρ c)) _))
  refine ⟨α, hα, corr_of_val hL fun y J hJ => ?_⟩
  rw [val_pull hJ, hv _ _ y J hJ, val_mul hJ, val_pull hJ, Category.assoc, ptSec_fst, Category.comp_id,
    val_mul hJ, val_inv, val_pull hJ, mul_inv_cancel_left]

theorem exists_value (hL : L.IsLB) {ρ : LB.Gen (L.pull (eSec A))} (hρ : ρ.IsGen) (k : ℤ)
    (t : LB.Sec (LPow A L k T)) : ∃ c : Γ(T.left, ⊤), ∀ z J, Good L z J →
      sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) t (ptSecT A 1).left z J =
        gs (𝟙 _) z ⊤ c * (val (rigT A L ρ T k) (𝟙 _) z J).val := by
  obtain ⟨s, hs⟩ := exists_sec hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim)
    (fun U _ f => by
      refine Eq.trans ?_ (Fintype.prod_empty _).symm
      simp only [Fintype.prod_sum_type, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr, ptSec_snd, zpow_neg,
        mul_inv_cancel])
    (pullMulSec (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) t (ptSecT A 1).left
      (LB.invGen L _ _ (rigT A L ρ T k)) (DVR.invGen_isGen _ _ _ _ (rigT_isGen hρ k)))
  have le : (⊤ : T.left.Opens) ≤ LB.wchart L (PEmpty.elim : PEmpty → (T.left ⟶ A.left)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨(T.left.presheaf.map (homOfLE le).op).hom (s.f PEmpty.elim), fun z J hJ => ?_⟩
  have e := (hs _ (𝟙 _) z J hJ).trans (sval_pullMulSec _ _ _ _ _ z hJ)
  rw [val_inv, Category.id_comp,
    sval_of s (𝟙 _) z J PEmpty.elim (fun k => k.elim)] at e
  exact (Units.inv_mul_cancel_right _ _).symm.trans
    (congrArg (· * _) ((gs_res (𝟙 _) z le trivial _).trans e).symm)

theorem sec_ext {Y : Scheme.{0}} {M : LB Y} {s s' : LB.Sec M} (h : ∀ j, s.f j = s'.f j) : s = s' := by
  cases s; cases s'
  congr
  exact funext h

end General

end GlobalTheory.NormTheta

namespace GlobalTheory


open NormTheta in
theorem existsUnique_thetaConst : LL → ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (ρ : LB.Gen (A.L.pull (eSec A.A))), ρ.IsGen → ∀ (m : ℕ), Odd m → ∀ (th : SecA A F 1) (x : TFK (R := R) F ⟶ A.A), x ^ (m ^ 2) = 1 → (∃! q : SecA A F (m ^ 2) × F, ThC A ρ m th x q.1 q.2) := by
  intro hLL R _ _ _ A F _ _ ρ hρ m hm th x hx
  have hLaw : Laws := hLL.1
  have hL := A.isLB
  let T := TFK (R := R) F
  have : Subsingleton T.left := inferInstanceAs (Subsingleton (PrimeSpectrum F))
  obtain ⟨p⟩ : Nonempty T.left := inferInstanceAs (Nonempty (PrimeSpectrum F))
  have hu : IsUnit ((m ^ 2 : ℕ) : Γ(Spec (CommRingCat.of (FractionRing R)), ⊤)) := by
    let e := (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).commRingCatIsoToRingEquiv.symm
    rw [← map_natCast e]
    refine (IsUnit.mk0 _ ?_).map e
    rw [← map_natCast (algebraMap R (FractionRing R))]
    exact (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2
      (Nat.cast_ne_zero.2 (pow_ne_zero 2 hm.pos.ne'))
  obtain ⟨hex, huniq⟩ := hLaw.symLift _ A (m ^ 2) hm.pow hu T x hx
  refine existsUnique_of_exists_of_unique ?_ ?_
  · obtain ⟨α₀, hα₀⟩ := hLaw.mulPull _ A m
    have e₁ : (snd T A.A).left ≫ (mulA A.A m).left = (snd T A.A ^ m).left := by
      rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
    obtain ⟨α₁, hα₁, -⟩ := exists_gen hL (φ' := ![(snd T A.A).left, (snd T A.A ^ m).left])
      (ε' := ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)])
      (fun U _ f => by
        refine Finset.prod_congr rfl fun i _ => ?_
        fin_cases i
        · exact congrArg₂ (fun q n => f q ^ n) (Category.comp_id _) (Nat.cast_pow m 2).symm
        · exact congrArg (fun q => f q ^ (-1 : ℤ)) e₁)
      (LB.pullGen A.L ![𝟙 A.A.left, (mulA A.A m).left] ![(m : ℤ) ^ 2, -1] α₀ (snd T A.A).left)
      (DVR.pullGen_isGen _ _ _ _ hα₀ _)
    obtain ⟨α, hα, hn⟩ := exists_normalised hL hρ m _ _ (((m ^ 2 : ℕ) : ℤ) - 1) rfl α₁ hα₁
    obtain ⟨s₁, hs₁⟩ := ThetaPtExist.exists_isTwistPull hL (mulT A.A T m) (snd T A.A ^ m) (lift_snd _ _)
      ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α hα th
    obtain ⟨V, hV, θ₀, hθ₀⟩ := hex p
    obtain ⟨h, hh⟩ := GlobalLift.exists_section (T := T) hV
    obtain ⟨θ, hθ⟩ := GlobalLift.exists_symLift_pull hL h hθ₀
    rw [← Category.assoc, hh, Category.id_comp] at hθ
    obtain ⟨t, ht⟩ := ThetaPtExist.exists_isTwistPull hL (translT A.A θ.pt) (translPt A.A θ.pt) (lift_snd _ _)
      ((m ^ 2 : ℕ) : ℤ) ((m ^ 2 : ℕ) : ℤ) θ.φ θ.isGen s₁
    obtain ⟨c₀, hc₀⟩ := exists_value hL hρ _ t
    obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 c₀
    exact ⟨(t, c), α, s₁, θ, hα, hn, hs₁, hθ, ht, hc₀⟩
  · rintro ⟨t, c⟩ ⟨t', c'⟩ ⟨α, s₁, θ, hα, hn, hs₁, hθ, ht, hc⟩ ⟨α', s₁', θ', hα', hn', hs₁', hθ', ht', hc'⟩
    have ea := gen_unique hL (fst T A.A).left (ptSecT A.A 1).left ptSec_fst
      (CommPairing.surj_fst hLaw.globalFns A.isAb T) hα hα' (fun y J hJ => by
        have a := (val_corr hJ hn (𝟙 _)).trans (val_corr hJ hn' (𝟙 _)).symm
        rwa [val_pull hJ, val_pull hJ, Category.id_comp] at a)
    obtain rfl : s₁ = s₁' := sec_ext (sec_ext_val hL fun y J hJ =>
      (ThetaLin.sval_of_isTwistPull A.A hs₁ _ y hJ).trans
        (Eq.trans (by rw [ea _ _ y J hJ]) (ThetaLin.sval_of_isTwistPull A.A hs₁' _ y hJ).symm))
    have eθ := huniq θ θ' hθ hθ'
    have ept : θ.pt = θ'.pt := hθ.pt_eq.trans hθ'.pt_eq.symm
    obtain rfl : t = t' := sec_ext (sec_ext_val hL fun y J hJ =>
      (ThetaLin.sval_of_isTwistPull A.A ht _ y hJ).trans
        (Eq.trans (by rw [val_corr hJ eθ, ept]) (ThetaLin.sval_of_isTwistPull A.A ht' _ y hJ).symm))
    refine Prod.ext rfl ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).1
      (fn_ext (V := ⊤) fun y _ => ?_))
    choose J hJ using fun χ : T.left ⟶ A.A.left => exists_chart hL (χ y)
    exact (Units.mul_left_inj _).1 ((hc y J hJ).symm.trans (hc' y J hJ))

end GlobalTheory
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

set_option autoImplicit false

noncomputable section
namespace GlobalTheory.UU

theorem exists_cubical_addition_factor_generator {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (P : CP G) {Y : Over S}
    (a b : Y ⟶ G) :
    ∃ κ : LB.Gen (LB.LinComb P.L.L (K := Fin 4) ![a.left, b.left, (a * b).left, (a * b⁻¹).left] ![2, 2, -1, -1]),
      κ.IsGen ∧ ∀ (T : Over S) (ρ : T ⟶ Y) (z : T.left) (J), Good P.L.L z J →
        val κ ρ.left z J = kap0 P.c P.sym z J (ρ ≫ a) (ρ ≫ b) := by
  apply GlobalTheory.AddGeneric.exists_additionFactor_generator_value <;> assumption

theorem exists_addSec : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : CP G) (T₀ : Over S) (θ : LB.Sec (LB.LinComb P.L.L (K := Fin 1) (fun _ => (snd T₀ G).left) (fun _ => ((1 : ℕ) : ℤ)))) (ρ₀ : G ⊗ G ⟶ T₀), ∃ v : LB.Sec (LB.LinComb P.L.L (K := Fin 1 ⊕ Fin 1) (Sum.elim (fun _ => (fst G G).left) (fun _ => (snd G G).left)) (Sum.elim (fun _ => ((2 : ℕ) : ℤ)) (fun _ => ((2 : ℕ) : ℤ)))), ∀ (T : Over S) (x y : T ⟶ G) (z : T.left) (J), Good P.L.L z J → sval v (lift x y).left z J = (kap0 P.c P.sym z J x y).val * (sval θ (lift (lift x y ≫ ρ₀) (x * y)).left z J * sval θ (lift (lift x y ≫ ρ₀) (x * y⁻¹)).left z J) := by
  intro S G _ _ P T₀ θ ρ₀
  obtain ⟨κ, hκ, hv⟩ := exists_cubical_addition_factor_generator P (fst G G) (snd G G)
  obtain ⟨v, hs⟩ := exists_sec P.L.isLB (K' := Fin 1 ⊕ Fin 1)
    (φ' := Sum.elim (fun _ => (fst G G).left) (fun _ => (snd G G).left))
    (ε' := Sum.elim (fun _ => ((2 : ℕ) : ℤ)) (fun _ => ((2 : ℕ) : ℤ))) (fun U _ h => by
      have e : ∀ p : G ⊗ G ⟶ G, ∏ _k : Fin 1, h ((lift ρ₀ p).left ≫ (snd T₀ G).left) ^ ((1 : ℕ) : ℤ) = h p.left :=
        fun p => by rw [Fintype.prod_unique, ← Over.comp_left, lift_snd, Nat.cast_one, zpow_one]
      refine ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) rfl ((Fintype.prod_sum_type _).trans
        (congrArg₂ (· * ·) (e _) (e _))))).trans ?_
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (H1.SectionArithmetic.mulSec (genSec κ hκ) (H1.SectionArithmetic.mulSec (H1.SectionArithmetic.pullSec θ (lift ρ₀ (fst G G * snd G G)).left)
      (H1.SectionArithmetic.pullSec θ (lift ρ₀ (fst G G * (snd G G)⁻¹)).left)))
  refine ⟨v, fun T x y z J hJ => (hs _ _ z J hJ).trans ?_⟩
  rw [H1.SectionArithmetic.sval_mulSec _ _ _ z hJ, H1.SectionArithmetic.sval_mulSec _ _ _ z hJ, H1.SectionArithmetic.sval_pullSec _ _ _ z hJ,
    H1.SectionArithmetic.sval_pullSec _ _ _ z hJ, sval_genSec _ _ _ z hJ, hv T _ z J hJ, ← Over.comp_left, ← Over.comp_left,
    comp_lift, comp_lift, MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, lift_fst, lift_snd]

end GlobalTheory.UU
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UU.EffSpecial

theorem exists_sec_of_lbIso {Y : Scheme.{0}} {A B : LB Y} (hA : A.IsLB) (hB : B.IsLB) (h : LBIso A B)
    (hs : ∃ s : LB.Sec B, ∃ j, s.f j ≠ 0) : ∃ s : LB.Sec A, ∃ j, s.f j ≠ 0 := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨t, b, hb⟩ := hs
  refine ⟨DVR.secOfIso t hu hA hB, ?_⟩
  by_contra hn
  push_neg at hn
  refine hb (fn_ext fun y hy => ?_)
  obtain ⟨a, ha⟩ := exists_chart hA y
  have e := (DVR.secOfIso_spec t hu hA hB a b).symm
  rw [hn a] at e
  have e' := (DVR.isoCand_rs u t a b le_rfl).symm.trans ((congrArg (DVR.rs le_rfl) (e.trans (map_zero _))).trans
    (map_zero _))
  have e'' := (Units.mul_right_eq_zero _).1 e'
  have hm : (𝟙 Y : Y ⟶ Y) y ∈ A.U a ⊓ B.U b := ⟨ha, hy⟩
  refine (gs_res (𝟙 Y) y inf_le_right hm _).symm.trans ((congrArg (gs (𝟙 Y) y _) e'').trans ?_)
  rw [gs_eq _ y _ hm, gs_eq _ y _ hy, map_zero, map_zero, map_zero, map_zero]

theorem lbIso_pw {Y : Scheme.{0}} {A B : LB Y} (h : LBIso A B) (t : ℤ) : LBIso (AbLaw.pw A t) (AbLaw.pw B t) := by
  obtain ⟨w, hw⟩ := h
  refine ⟨⟨fun p => w.s p ^ t⟩, fun p q => ?_⟩
  have e := congrArg (· ^ t) (hw p q)
  simp only [mul_zpow, ← map_zpow] at e
  refine e.trans (congrArg₂ (· * ·) ?_ rfl)
  exact (mul_zpow _ _ t).trans (congrArg₂ (· * ·) (map_zpow _ _ t).symm
    ((inv_zpow _ t).trans (congrArg (·⁻¹) (map_zpow _ _ t).symm)))

theorem ne_zero_of_mem {Y : Scheme.{0}} {M : LB Y} (s : LB.Sec M) {y : Y} (hy : y ∈ nonzeroLocus s) :
    ∃ j, s.f j ≠ 0 := by
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  refine ⟨j, fun e => ?_⟩
  rw [e, Scheme.basicOpen_zero] at hj
  exact hj

theorem isIntegral_special {V : Type} [CommRing V] [IsLocalRing V]
    (B : Over (Spec (CommRingCat.of (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1))))) [GrpObj B]
    (hB : IsAbelianScheme B) : IsIntegral B.left := by
  have hm : (IsLocalRing.maximalIdeal V ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  letI := Ideal.Quotient.field (IsLocalRing.maximalIdeal V ^ (0 + 1))
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ B.hom hB.smooth hB.geomConnected
  exact GeometricallyIntegral.geometrically_isIntegral (f := B.hom) _ _ _ (IsPullback.of_id_fst (f := B.hom))

theorem exists_sec_special : Laws → AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ t : Tower s, ∃ (k : ℕ) (σ : LB.Sec (pw (t.l 0).D.M.L.L k)), 1 ≤ k ∧ ∃ j, σ.f j ≠ 0 := by
  intro hL V _ _ _ A G _ _ s t
  have := s.cdvr.1
  have := s.semi.smooth
  have := s.semi.separated
  have := s.semi.quasiCompact
  have := s.semi.geomConnected
  obtain ⟨d, hd, n, a, ha, -⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy _ A.A A.L A.isLB).1 A.ample
  have hP := s.P.L.isLB

  have h₁ : ∃ σ : LB.Sec ((AbLaw.pw s.P.L.L d).pull (pullback.fst G.hom (jK V))), ∃ j, σ.f j ≠ 0 := by
    have iso : LBIso ((AbLaw.pw s.P.L.L d).pull (pullback.fst G.hom (jK V)))
        ((AbLaw.pw A.L d).pull s.gen.hom.left) := by
      rw [TrivLocus.pull_pw, TrivLocus.pull_pw]
      exact lbIso_pw (LBIso.symm ⟨s.wA, s.wA_gen⟩) d
    obtain ⟨w, hw⟩ := iso
    let y : ((Over.pullback (jK V)).obj G).left :=
      s.gen.inv.left (eSec A.A (IsLocalRing.closedPoint (FractionRing V)))
    have hy : s.gen.hom.left y ∈ ⨆ i, nonzeroLocus (a i) := by rw [ha]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    obtain ⟨⟨σ, hσ, -⟩, H⟩ := SecPullIso.section_pull _ _ s.gen.hom.left _ _ w (isLB_pw A.isLB d)
      (pull_isLB (isLB_pw hP d) _) hw (a i)
    exact ⟨σ, ne_zero_of_mem σ (y := y) (by rw [H σ hσ]; exact hi)⟩

  have h₂ := GlobalTheory.SpreadSec.exists_ne_zero_closed_fibre V G _ (isLB_pw hP d) h₁
  obtain ⟨w, hw⟩ := (t.l 0).lev
  have hM := (t.l 0).D.M.L.isLB
  have hE := (t.l 0).Pe.L.isLB
  have h₃ : ∃ σ : LB.Sec ((AbLaw.pw (t.l 0).D.M.L.L d).pull (t.l 0).Q.q.left), ∃ j, σ.f j ≠ 0 := by
    refine exists_sec_of_lbIso (pull_isLB (isLB_pw hM d) _) (pull_isLB (isLB_pw hP d) _) ?_ h₂
    rw [TrivLocus.pull_pw, TrivLocus.pull_pw]
    exact lbIso_pw (LBIso.trans (pull_isLB hM _) hE (pull_isLB hP _)
      (LBIso.symm ⟨_, (t.l 0).D.map.gen⟩) ⟨w, hw.gen⟩) d

  have hm : (IsLocalRing.maximalIdeal V ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  have : IsLocalRing (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)) :=
    letI := Ideal.Quotient.field (IsLocalRing.maximalIdeal V ^ (0 + 1))
    inferInstance
  obtain ⟨O, hO, hu, h₄⟩ := GlobalTheory.T.exists_section_primitive_twist_torus_extension hL.globalFns _ _ _ (t.l 0).Q _ (isLB_pw hM d) h₃
  have := isIntegral_special (t.l 0).Q.B (t.l 0).Q.isAb
  obtain ⟨σ, hσ⟩ := SymSec.exists_sec_sq _ (t.l 0).Q.B (t.l 0).D.M d O hO hu h₄
  exact ⟨2 * d, σ, by omega, hσ⟩

end GlobalTheory.UU.EffSpecial
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ConnFibre

open GlobalTheory.AbLaw.Seesaw

theorem preconnectedSpace_of_functions (Y : Scheme.{0})
    (H : ∀ s : Γ(Y, ⊤), Y.basicOpen s = ⊥ ∨ Y.basicOpen s = ⊤) : PreconnectedSpace Y := by
  apply _root_.GlobalTheory.AlgGroup.preconnectedSpace_of_functions <;> assumption

theorem surjective_appTop {k : Type} [Field k] [IsAlgClosed k] {X : Scheme.{0}}
    (p : X ⟶ Spec (.of k)) [IsIntegral X] [UniversallyClosed p] :
    Function.Surjective p.appTop.hom := by
  let F := (Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop
  have hF : F.hom.IsIntegral := by
    apply RingHom.isIntegral_respectsIso.2 (e := (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv)
    exact isIntegral_appTop_of_universallyClosed p
  algebraize [F.hom]
  have h : Function.Surjective F.hom :=
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := Γ(X, ⊤))).2
  intro s
  obtain ⟨c, hc⟩ := h s
  exact ⟨_, hc⟩

variable {X X' : Scheme.{0}}

def fnSec (π : X' ⟶ X) (s : Γ(X', ⊤)) : LB.Sec ((Inh.trivLB X).pull π) where
  f := fun _ => rs X' le_top s
  compat := fun i j => by
    rw [Inh.linComb_triv_g, Units.val_one, _root_.one_mul]
    exact (rs_rs _ _ s).trans (rs_rs _ _ s).symm

theorem triv_pull (π : X' ⟶ X) : Triv ((Inh.trivLB X).pull π) :=
  ⟨⟨fun _ => 1⟩, fun i j => by
    erw [Inh.linComb_triv_g, _root_.one_mul]
    exact (map_one _).trans (map_one _).symm⟩

theorem preconnectedSpace_of_line {R F : Type} [CommRing R] [Field F]
    {f : X ⟶ Spec (CommRingCat.of R)} (P : Perf f (Inh.trivLB X)) {g : R →+* F} {π : X' ⟶ X}
    {f' : X' ⟶ Spec (CommRingCat.of F)} (h : IsPullback π f' f (Spec.map (CommRingCat.ofHom g)))
    (v : Fin P.a → F) (hv : ∀ w, (P.D₀.map g).mulVec w = 0 → ∃ c : F, w = c • v) :
    PreconnectedSpace X' := by
  obtain ⟨E, hE⟩ := P.sec F g X' π f' h
  have key : ∀ s : Γ(X', ⊤), ∃ c : F, ∀ i,
      rs X' (le_top : π ⁻¹ᵁ P.W i ≤ ⊤) s = AbLaw.cst f' _ c * loc P π f' v i := fun s => by
    obtain ⟨w, hw⟩ := E.surjective (fnSec π s)
    obtain ⟨c, hc⟩ := hv w.1 w.2
    refine ⟨c, fun i => ?_⟩
    have e := hE w i
    rw [hw] at e
    refine ((rs_rs _ _ s).symm.trans e).trans ?_
    rw [← loc_smul, ← hc]
    rfl
  obtain ⟨c₁, h₁⟩ := key 1
  have hu : ∀ i, IsUnit (loc P π f' v i) := fun i =>
    isUnit_of_mul_isUnit_right (by rw [← h₁ i, map_one]; exact isUnit_one)
  refine preconnectedSpace_of_functions X' fun s => ?_
  obtain ⟨c, hc⟩ := key s
  by_cases h0 : c = 0
  · refine Or.inl (le_bot_iff.1 fun y hy => ?_)
    obtain ⟨i, hi⟩ := exists_mem P (π y)
    have := (mem_basicOpen_rs (le_top : π ⁻¹ᵁ P.W i ≤ ⊤) s hi).2 hy
    rwa [hc, h0, map_zero, zero_mul, Scheme.basicOpen_zero] at this
  · refine Or.inr (top_unique fun y _ => ?_)
    obtain ⟨i, hi⟩ := exists_mem P (π y)
    refine (mem_basicOpen_rs (le_top : π ⁻¹ᵁ P.W i ≤ ⊤) s hi).1 ?_
    rw [hc]
    exact mem_of_isUnit (((IsUnit.mk0 c h0).map _).mul (hu i)) hi

theorem geometricallyConnected_of_closedFibre : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (B : Over (Spec (CommRingCat.of V))), Smooth B.hom → IsProjBy B.hom → ∀ (Y₀ : Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (0 + 1))))) (b : Y₀.left ⟶ B.left), IsPullback b Y₀.hom B.hom (thick V (IsLocalRing.maximalIdeal V) 0) → GeometricallyConnected Y₀.hom → GeometricallyConnected B.hom := by
  intro V _ _ _ B hs hp Y₀ b hb hc
  obtain ⟨P⟩ := GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj V B.left B.hom hs hp _ (Inh.trivLB_isLB _)
  have hpr : IsProper B.hom := GlobalTheory.AbLaw.isProper_of_isProjBy V B.left B.hom hp
  let L := AlgebraicClosure (IsLocalRing.ResidueField V)
  let g₀ : V →+* L := (algebraMap (IsLocalRing.ResidueField V) L).comp (IsLocalRing.residue V)
  have hg₀ : ∀ a, g₀ a = 0 ↔ a ∈ IsLocalRing.maximalIdeal V := fun a =>
    (map_eq_zero (algebraMap (IsLocalRing.ResidueField V) L)).trans (IsLocalRing.residue_eq_zero_iff a)
  let q : V ⧸ (IsLocalRing.maximalIdeal V) ^ (0 + 1) →+* L :=
    Ideal.Quotient.lift _ g₀ fun a ha => (hg₀ a).2 (by simpa using ha)
  let y₀ : Spec (CommRingCat.of L) ⟶ _ := Spec.map (CommRingCat.ofHom q)
  have h₀ : IsPullback (pullback.fst Y₀.hom y₀ ≫ b) (pullback.snd Y₀.hom y₀) B.hom
      (Spec.map (CommRingCat.ofHom g₀)) := by
    have := (IsPullback.of_hasPullback Y₀.hom y₀).paste_horiz hb
    rwa [← Spec.map_comp] at this
  have hs₀ : Smooth Y₀.hom := MorphismProperty.of_isPullback hb hs
  have hi := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ Y₀.hom hs₀ hc
  have hint : IsIntegral (pullback Y₀.hom y₀) :=
    GeometricallyIntegral.geometrically_isIntegral _ _ _ (.of_hasPullback Y₀.hom y₀)
  have hpr₀ : IsProper (pullback.snd Y₀.hom y₀) := MorphismProperty.of_isPullback h₀ hpr
  obtain ⟨v, -, hu, hline⟩ := loc_of_triv P h₀ (Inh.trivLB_isLB _) (triv_pull _)
  obtain ⟨x₀⟩ : Nonempty ↥(pullback Y₀.hom y₀) := inferInstance
  have hv0 : v ≠ 0 := by
    rintro rfl
    obtain ⟨i, hi⟩ := exists_mem P ((pullback.fst Y₀.hom y₀ ≫ b) x₀)
    have h₁ := mem_of_isUnit (hu i) (y := x₀) hi
    rw [← zero_smul L (0 : Fin P.a → L), loc_smul, map_zero, zero_mul, Scheme.basicOpen_zero] at h₁
    exact h₁
  obtain ⟨δ, v₀, hδ, hker⟩ := exists_kernel_vector g₀ P.D₀ v hv0 (hline (surjective_appTop _))
  have hδ' : IsUnit δ := by
    by_contra hn
    exact hδ ((hg₀ δ).2 hn)
  have hsurj : Surjective B.hom := by
    let O : (Spec (CommRingCat.of V)).Opens := ⟨Set.range B.hom, B.hom.isOpenMap.isOpen_range⟩
    have hO : O = ⊤ := by
      refine (IsLocalRing.closedPoint_mem_iff O).1 ⟨(pullback.fst Y₀.hom y₀ ≫ b) x₀, ?_⟩
      have e : B.hom ((pullback.fst Y₀.hom y₀ ≫ b) x₀) =
          Spec.map (CommRingCat.ofHom g₀) (pullback.snd Y₀.hom y₀ x₀) := congrArg (fun t => t x₀) h₀.w
      refine e.trans (PrimeSpectrum.ext ?_)
      refine ((IsLocalRing.maximalIdeal.isMaximal V).eq_of_le (PrimeSpectrum.isPrime _).ne_top
        fun a ha => ?_).symm
      change g₀ a ∈ (pullback.snd Y₀.hom y₀ x₀).asIdeal
      rw [(hg₀ a).2 ha]
      exact zero_mem _
    exact ⟨fun z => hO.ge (Set.mem_univ z)⟩
  refine ⟨geometrically_iff_of_commRing.2 fun F _ _ Z fst snd h => ?_⟩
  have : Surjective snd := MorphismProperty.of_isPullback h hsurj
  obtain ⟨z, -⟩ := snd.surjective (⊥ : PrimeSpectrum F)
  have := preconnectedSpace_of_line P h _ (hker F _ (hδ'.map _))
  exact ⟨⟨z⟩⟩

end GlobalTheory.ConnFibre
end
end
