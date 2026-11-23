module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle075
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle107
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2938
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2993
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2659
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitIntCastStalkIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSymmetryHypothesisExtendsNormalAffineC
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2682
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2918
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2641
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupExtendsNormalAffineChartAfterRescaling
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle189
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsFinsetRepresentatives
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle126
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3036
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.UPoinc.exists_tie_of_uOver : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (wi : UWit X) (R : Subalgebra X.o₁ X.Ω₁) (P' : PolAV (Sp R)) (u' : Sp (ratHull R) ⟶ Xo.XF cf), spMap (ratHull R).val.toRingHom ≫ u' = X.uΩ → UOver Xo cf P' (toRat R) u' → ∃ (G : Over (Sp (ratHull R))) (_ : GrpObj G) (α : G.left ⟶ P'.A.left) (β : G.left ⟶ Xo.univ.t.G.left) (m : wi.G.left ⟶ G.left) (P₀ : PolAV (Sp X.Ω₁)) (e : P₀.A.left ⟶ wi.G.left), IsGrpPullback G P'.A (spMap (toRat R)) α ∧ IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β ∧ LBIso (P'.L.pull α) (Xo.univ.t.PP.L.pull β) ∧ IsGrpPullback wi.G G (spMap (ratHull R).val.toRingHom) m ∧ m ≫ β = wi.β ∧ IsGrpPullback P₀.A X.ρ.P.A (spMap X.S.R.val.toRingHom) (e ≫ wi.α) ∧ IsGrpPullback P₀.A P'.A (spMap R.val.toRingHom) (e ≫ m ≫ α) ∧ LBIso P₀.L (X.ρ.P.L.pull (e ≫ wi.α)) ∧ LBIso P₀.L (P'.L.pull (e ≫ m ≫ α)) := by
  intro E _ _ _ H Dw l Xo cf C X wi R P' u' hc h
  obtain ⟨G, _, α, β, hα, hβ, hL⟩ := h
  have hb : IsGrpPullback wi.G Xo.univ.t.G (spMap (ratHull R).val.toRingHom ≫ u' ≫ pullback.fst _ _) wi.β :=
    wi.hβ.congr (by rw [← hc, Category.assoc]) rfl
  have w₁ : wi.β ≫ Xo.univ.t.G.hom = (wi.G.hom ≫ spMap (ratHull R).val.toRingHom) ≫ u' ≫ pullback.fst _ _ := by
    rw [Category.assoc]; exact hb.1.w
  have em := hβ.1.lift_fst _ _ w₁
  have hm := hβ.cancel (hb.congr rfl em.symm) (hβ.1.lift_snd _ _ w₁)
  generalize hβ.1.lift _ _ w₁ = m at em hm
  obtain ⟨P₀, φ, hφ, hφL⟩ := exists_pol_baseChange X.ρ.P (spMap X.S.R.val.toRingHom)
  have w₂ : φ ≫ X.ρ.P.A.hom = (P₀.A.hom ≫ 𝟙 _) ≫ spMap X.S.R.val.toRingHom := by
    rw [Category.comp_id]; exact hφ.1.w
  have ee := wi.hα.1.lift_fst _ _ w₂
  have he := wi.hα.cancel (hφ.congr (Category.id_comp _).symm ee.symm) (wi.hα.1.lift_snd _ _ w₂)
  generalize wi.hα.1.lift _ _ w₂ = e at ee he
  subst ee
  have hU := Xo.univ.t.PP.isLB
  refine ⟨G, _, α, β, m, P₀, e, hα, hβ, hL, hm, em, hφ,
    (he.comp (hm.comp hα)).congr ((Category.id_comp _).trans (spMap_val_toRat R)) rfl, hφL, ?_⟩
  have l₁ : LBIso (X.ρ.P.L.pull (e ≫ wi.α)) (Xo.univ.t.PP.L.pull (e ≫ wi.β)) :=
    GenSpread.lbIso_pull_comp _ rfl rfl wi.hL
  have l₂ : LBIso (P'.L.pull (m ≫ α)) (Xo.univ.t.PP.L.pull (m ≫ β)) := GenSpread.lbIso_pull_comp _ rfl rfl hL
  rw [em] at l₂
  have l₃ : LBIso (P'.L.pull (e ≫ m ≫ α)) (Xo.univ.t.PP.L.pull (e ≫ wi.β)) := GenSpread.lbIso_pull_comp _ rfl rfl l₂
  exact LBIso.trans P₀.isLB (pull_isLB X.ρ.P.isLB _) (pull_isLB P'.isLB _) hφL
    (LBIso.trans (pull_isLB X.ρ.P.isLB _) (pull_isLB hU _) (pull_isLB P'.isLB _) l₁ l₃.symm)



theorem GlobalTheory.UPoinc.exists_urechart_affine : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (wi : UWit X) (w : X.M.Z), X.π w ∈ Set.range C.i → ∃ (U : X.M.Z.Opens) (c₀ : X.Ω₁) (hc : c₀ ≠ 0) (fg : (X.M.ringOn U).FG) (frac : ∀ x : X.Ω₁, ∃ a ∈ X.M.ringOn U, ∃ b ∈ X.M.ringOn U, x = a / b) (hth : ∀ x, c₀ * X.S.th x ∈ X.M.ringOn U) (hev : ∀ x k, c₀ * X.S.ev x k ∈ X.M.ringOn U) (ρ' : (X.S.rechart c₀ hc (X.M.ringOn U) fg frac hth hev).Real) (u' : Sp (ratHull (X.M.ringOn U)) ⟶ Xo.XF cf), IsAffineOpen U ∧ w ∈ U ∧ USame X.ρ ρ' (fun x => x) (RingHom.id _) ∧ ρ'.i₀ = X.ρ.i₀ ∧ (∃ (G : Over (Sp (ratHull (X.M.ringOn U)))) (_ : GrpObj G) (α : G.left ⟶ ρ'.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left), IsGrpPullback G ρ'.P.A (spMap (toRat (X.M.ringOn U))) α ∧ IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β ∧ LBIso (ρ'.P.L.pull α) (Xo.univ.t.PP.L.pull β) ∧ (∃ m : wi.G.left ⟶ G.left, IsGrpPullback wi.G G (spMap (ratHull (X.M.ringOn U)).val.toRingHom) m ∧ m ≫ β = wi.β ∧ ∀ x, ∃ w : Sp X.Ω₁ ⟶ wi.G.left, w ≫ wi.α = spMap X.S.R.val.toRingHom ≫ (X.ρ.pt x).left ∧ w ≫ m ≫ α = spMap (Subalgebra.val (X.M.ringOn U)).toRingHom ≫ (ρ'.pt x).left)) ∧ spMap (ratHull (X.M.ringOn U)).val.toRingHom ≫ u' = X.uΩ := by
  intro E _ _ _ H Dw _hpq l Xo cf C X wi w hw
  obtain ⟨U₀, u₀, hU₀a, hwU₀, hu₀⟩ := GlobalTheory.UPoinc.ChartAt.exists_affine_chart_ratLift E H Dw l Xo cf C X w hw
  obtain ⟨U₁, h₁, P₁, _hU₁₀, hU₁a, hwU₁, hP₁⟩ := GlobalTheory.UPoinc.LocSpread.exists_uOver_ringOn E H Dw l Xo cf C X U₀ u₀ w hU₀a hwU₀ hw
  have hN : 1 ≤ X.S.N := by have := X.S.N_ge; omega
  obtain ⟨U, h, P', φ, _hUU₁, hUa, hwU, hφ, hφL, _hgφ, ⟨th, hth⟩, b, hb⟩ :=
    GlobalTheory.Poinc.exists_univBasis_affineChart X.o₁ X.Ω₁ X.M U₁ w hU₁a hwU₁ P₁ X.S.N hN
  have hne : ((U : X.M.Z.Opens) : Set X.M.Z).Nonempty := ⟨w, hwU⟩
  let u' : Sp (ratHull (X.M.ringOn U)) ⟶ Xo.XF cf :=
    spMap (Subalgebra.inclusion (ratHull_mono (h₁.trans h))).toRingHom ≫ u₀
  have hP' : UOver Xo cf P' (toRat (X.M.ringOn U)) u' := by
    refine (uOver_baseChange_iff hφ hφL (toRat _)).2 ?_
    have := hP₁.comp (Subalgebra.inclusion (ratHull_mono h)).toRingHom
    have e : spMap (Subalgebra.inclusion (ratHull_mono h)).toRingHom ≫
        spMap (Subalgebra.inclusion (ratHull_mono h₁)).toRingHom ≫ u₀ = u' := by
      rw [← Category.assoc, ← Spec.map_comp]; rfl
    rw [e] at this
    exact this
  have hcomp : spMap (ratHull (X.M.ringOn U)).val.toRingHom ≫ u' = X.uΩ := by
    rw [← hu₀, ← Category.assoc, ← Spec.map_comp]; rfl
  obtain ⟨G, _, α, β, m, P₀, e, hα, hβ, hαβ, hm, hmβ, ha, ha', hL, hL'⟩ :=
    GlobalTheory.UPoinc.exists_tie_of_uOver E H Dw l Xo cf C X wi (X.M.ringOn U) P' u' hcomp hP'
  have hg' : P'.g = X.S.g :=
    (GlobalTheory.polAV_g_eq_of_isGrpPullback X.Ω₁ _ P' P₀ _ _ ha').symm.trans
      ((GlobalTheory.polAV_g_eq_of_isGrpPullback X.Ω₁ _ X.ρ.P P₀ _ _ ha).trans X.ρ.g_eq)
  have hyp : HypS P'.A P'.L :=
    GlobalTheory.Poinc.hypS_of_generic_ringOn X.o₁ X.Ω₁ X.M U hUa hne X.normal X.S.R X.ρ.P P' P₀ _ _ _ ha ha' hL hL' X.ρ.hypS

  obtain ⟨⟨hLw, -⟩, -⟩ := GlobalTheory.lawsAndExpansions
  haveI := RatModel.isFractionRing_ringOn hUa hne
  haveI := TorsExtend.isIntegrallyClosed_ringOn X.M ((isNormalScheme_iff_pred _).1 X.normal) hUa hne
  haveI := ArithBase.ded (o := X.o₁) (Ω := X.Ω₁)
  have fg : (X.M.ringOn U).FG := GlobalTheory.Poinc.fg_ringOn_of_isAffineOpen _ _ X.M U hUa hne
  haveI : IsNoetherianRing (X.M.ringOn U) := isNoetherianRing_of_fg fg
  have hn : 1 ≤ X.S.r * X.S.N := Nat.mul_pos X.S.r_pos (le_trans one_le_two X.S.N_ge)
  have hu : IsUnit ((X.S.r * X.S.N : ℕ) : X.M.ringOn U) := by
    have := X.S.unit.map (algebraMap X.o₁ (X.M.ringOn U))
    rwa [map_natCast] at this
  obtain ⟨pt', hadd, hbij, h₃, hw0⟩ := TorsExtend.exists_labelled hLw X.S.R.val.toRingHom X.ρ.P P' P₀ _ _ ha ha' hL hL'
    hn hu (M := X.S.Gam) (fun x => by ext k; simp [nsmul_eq_mul, -Nat.cast_mul]) X.ρ.pt X.ρ.pt_add X.ρ.pt_bij
  have hweil : ∀ x y (c : (X.M.ringOn U)ˣ), (c : (X.M.ringOn U)) = algebraMap X.o₁ (X.M.ringOn U)
      (X.S.ζ ^ (X.S.r * X.S.N * (eStd X.S.g _ x y).val)) →
      WeilIs P'.A P'.L (X.S.r * X.S.N : ℕ) (pt' x) (pt' y) (unitOn c) := fun x y c hc => by
    obtain ⟨c₀, hc₀⟩ := ((X.S.prim.isUnit (by positivity)).pow (X.S.r * X.S.N * (eStd X.S.g _ x y).val)).map
      (algebraMap X.o₁ X.S.R)
    refine h₃ x y c₀ c ?_ (X.ρ.weil x y c₀ hc₀)
    rw [hc₀, hc]
    rfl
  have frac : ∀ x : X.Ω₁, ∃ a ∈ X.M.ringOn U, ∃ b ∈ X.M.ringOn U, x = a / b := fun x => by
    obtain ⟨p, q, -, e⟩ := RatModel.exists_eq_div hUa hne x
    exact ⟨_, (RatModel.mem_ringOn_iff_exists hne).2 ⟨p, rfl⟩, _, (RatModel.mem_ringOn_iff_exists hne).2 ⟨q, rfl⟩, e⟩
  have hQ : (∃ (G : Over (Sp (ratHull (X.M.ringOn U)))) (_ : GrpObj G) (α : G.left ⟶ P'.A.left)
      (β : G.left ⟶ Xo.univ.t.G.left), IsGrpPullback G P'.A (spMap (toRat (X.M.ringOn U))) α ∧
        IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β ∧ LBIso (P'.L.pull α) (Xo.univ.t.PP.L.pull β) ∧
        (∃ m : wi.G.left ⟶ G.left, IsGrpPullback wi.G G (spMap (ratHull (X.M.ringOn U)).val.toRingHom) m ∧
          m ≫ β = wi.β ∧ ∀ x, ∃ w : Sp X.Ω₁ ⟶ wi.G.left,
            w ≫ wi.α = spMap X.S.R.val.toRingHom ≫ (X.ρ.pt x).left ∧
            w ≫ m ≫ α = spMap (Subalgebra.val (X.M.ringOn U)).toRingHom ≫ (pt' x).left)) ∧
      ∃ a'' : P₀.A.left ⟶ P'.A.left, IsGrpPullback P₀.A P'.A (spMap (X.M.ringOn U).val.toRingHom) a'' ∧
        LBIso P₀.L (P'.L.pull a'') ∧
        ∀ x, ∃ w0 : Sp X.Ω₁ ⟶ P₀.A.left, w0 ≫ e ≫ wi.α = spMap X.S.R.val.toRingHom ≫ (X.ρ.pt x).left ∧
          w0 ≫ a'' = spMap (X.M.ringOn U).val.toRingHom ≫ (pt' x).left := by
    refine ⟨⟨G, inferInstance, α, β, hα, hβ, hαβ, m, hm, hmβ, fun x => ?_⟩, _, ha', hL', hw0⟩
    obtain ⟨w0, h₁, h₂⟩ := hw0 x
    exact ⟨w0 ≫ e, by rw [Category.assoc]; exact h₁, by rw [Category.assoc]; exact h₂⟩
  obtain ⟨c₀, hc, hthm, hevm, ρ', ⟨hU', a'', q₂, q₃, q₅⟩, hi₀⟩ := GlobalTheory.ThetaExtend.exists_real_rechart
    GlobalTheory.abelianSchemeLaws_all.1 X.S X.ρ (X.M.ringOn U) fg frac P' P₀ _ _ pt' th b ha ha' hL hL' hg' hyp hadd hbij hweil
    hw0 hth hb
    (fun P pt => (∃ (G : Over (Sp (ratHull (X.M.ringOn U)))) (_ : GrpObj G) (α : G.left ⟶ P.A.left)
      (β : G.left ⟶ Xo.univ.t.G.left), IsGrpPullback G P.A (spMap (toRat (X.M.ringOn U))) α ∧
        IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β ∧ LBIso (P.L.pull α) (Xo.univ.t.PP.L.pull β) ∧
        (∃ m : wi.G.left ⟶ G.left, IsGrpPullback wi.G G (spMap (ratHull (X.M.ringOn U)).val.toRingHom) m ∧
          m ≫ β = wi.β ∧ ∀ x, ∃ w : Sp X.Ω₁ ⟶ wi.G.left,
            w ≫ wi.α = spMap X.S.R.val.toRingHom ≫ (X.ρ.pt x).left ∧
            w ≫ m ≫ α = spMap (Subalgebra.val (X.M.ringOn U)).toRingHom ≫ (pt x).left)) ∧
      ∃ a'' : P₀.A.left ⟶ P.A.left, IsGrpPullback P₀.A P.A (spMap (X.M.ringOn U).val.toRingHom) a'' ∧
        LBIso P₀.L (P.L.pull a'') ∧
        ∀ x, ∃ w0 : Sp X.Ω₁ ⟶ P₀.A.left, w0 ≫ e ≫ wi.α = spMap X.S.R.val.toRingHom ≫ (X.ρ.pt x).left ∧
          w0 ≫ a'' = spMap (X.M.ringOn U).val.toRingHom ≫ (pt x).left) hQ
  exact ⟨U, c₀, hc, fg, frac, hthm, hevm, ρ', u', hUa, hwU, ⟨P₀, e ≫ wi.α, a'', ha, q₂, hL, q₃, q₅⟩, hi₀, hU', hcomp⟩
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc

theorem UDeep.exists_tie (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (_hpq : 1 ≤ Dw.p + Dw.q) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf)
    (X₁ : USetup C) (D : UDeep X₁) (w₁ : UWit X₁) : ∃ w₂ : UWit D.X, D.Comparison₂ w₁ w₂ := by
  obtain ⟨P₀, a, a', ha, ha', hL, hL', hpt⟩ := D.same
  have e : spMap (algebraMap X₁.Ω₁ D.X.Ω₁) ≫ spMap X₁.S.R.val.toRingHom =
      spMap ((algebraMap X₁.Ω₁ D.X.Ω₁).comp X₁.S.R.val.toRingHom) := by
    rw [← Spec.map_comp]; rfl
  have w : a ≫ X₁.ρ.P.A.hom = (P₀.A.hom ≫ spMap (algebraMap X₁.Ω₁ D.X.Ω₁)) ≫ spMap X₁.S.R.val.toRingHom := by
    rw [Category.assoc, e]; exact ha.1.w
  have e₁ := w₁.hα.1.lift_fst _ _ w
  let m : P₀.A.left ⟶ w₁.G.left := w₁.hα.1.lift _ _ w
  have hm : IsGrpPullback P₀.A w₁.G (spMap (algebraMap X₁.Ω₁ D.X.Ω₁)) m :=
    w₁.hα.cancel (ha.congr e.symm e₁.symm) (w₁.hα.1.lift_snd _ _ w)
  have hβ : IsGrpPullback P₀.A Xo.univ.t.G (D.X.uΩ ≫ pullback.fst _ _) (m ≫ w₁.β) :=
    (hm.comp w₁.hβ).congr (by rw [D.pt]; simp only [USetup.uΩ, Category.assoc]) rfl
  have hLβ : LBIso (D.X.ρ.P.L.pull a') (Xo.univ.t.PP.L.pull (m ≫ w₁.β)) :=
    LBIso.trans (pull_isLB D.X.ρ.P.isLB _) P₀.isLB (pull_isLB Xo.univ.t.PP.isLB _) hL'.symm
      (LBIso.trans P₀.isLB (pull_isLB X₁.ρ.P.isLB _) (pull_isLB Xo.univ.t.PP.isLB _) hL
        (GenSpread.lbIso_pull_comp m e₁.symm rfl w₁.hL))
  refine ⟨{ G := P₀.A, α := a', β := m ≫ w₁.β, hα := ha', hβ := hβ, hL := hLβ }, m, hm, rfl, fun x => ?_⟩
  obtain ⟨v, hv, hv'⟩ := hpt x
  refine ⟨v, ?_, hv'⟩
  show v ≫ m ≫ w₁.α = _
  rw [e₁, hv, ← Category.assoc, e]

end GlobalTheory.UPoinc
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory



theorem GlobalTheory.UPoinc.exists_rechart_wit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (wi : UWit X) (w₀ : X.M.Z), X.π w₀ ∈ Set.range C.i → ∃ (U : X.M.Z.Opens) (c₀ : X.Ω₁) (hc : c₀ ≠ 0) (fg : (X.M.ringOn U).FG) (frac : ∀ x : X.Ω₁, ∃ a ∈ X.M.ringOn U, ∃ b ∈ X.M.ringOn U, x = a / b) (hth : ∀ x, c₀ * X.S.th x ∈ X.M.ringOn U) (hev : ∀ x k, c₀ * X.S.ev x k ∈ X.M.ringOn U) (ρ' : (X.S.rechart c₀ hc (X.M.ringOn U) fg frac hth hev).Real) (u' : Sp (ratHull (X.M.ringOn U)) ⟶ Xo.XF cf), IsAffineOpen U ∧ w₀ ∈ U ∧ USame X.ρ ρ' (fun x => x) (RingHom.id _) ∧ ρ'.i₀ = X.ρ.i₀ ∧ spMap (ratHull (X.M.ringOn U)).val.toRingHom ≫ u' = X.uΩ ∧ ∃ (G : Over (Sp (ratHull (X.M.ringOn U)))) (_ : GrpObj G) (α : G.left ⟶ ρ'.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left), IsGrpPullback G ρ'.P.A (spMap (toRat (X.M.ringOn U))) α ∧ IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β ∧ LBIso (ρ'.P.L.pull α) (Xo.univ.t.PP.L.pull β) ∧ ∃ m : wi.G.left ⟶ G.left, IsGrpPullback wi.G G (spMap (ratHull (X.M.ringOn U)).val.toRingHom) m ∧ m ≫ β = wi.β ∧ ∀ x, ∃ w : Sp X.Ω₁ ⟶ wi.G.left, w ≫ wi.α = spMap X.S.R.val.toRingHom ≫ (X.ρ.pt x).left ∧ w ≫ m ≫ α = spMap (X.M.ringOn U).val.toRingHom ≫ (ρ'.pt x).left := by
  intro E _ _ _ H Dw hpq l Xo cf C X wi w₀ hw₀
  obtain ⟨⟨hL, -⟩, -⟩ := GlobalTheory.lawsAndExpansions
  obtain ⟨U₀, u₀, hU₀a, hwU₀, hu₀⟩ := GlobalTheory.UPoinc.ChartAt.exists_affine_chart_ratHull_lift E H Dw hpq l Xo cf C X w₀ hw₀
  obtain ⟨U₁, h₁, P₁, hU₁₀, hU₁a, hwU₁, hP₁⟩ := GlobalTheory.UPoinc.USetup.exists_polAV_ringOn_near E H Dw hpq l Xo cf C X w₀ hw₀ U₀ u₀ hU₀a hwU₀ hu₀
  have hN : 1 ≤ X.S.N := by have := X.S.N_ge; omega
  obtain ⟨U, h, P', φ, hUU₁, hUa, hwU, hφ, hφL, _hgφ, ⟨th, hth⟩, b, hb⟩ :=
    GlobalTheory.Poinc.exists_univBasis_affineChart X.o₁ X.Ω₁ X.M U₁ w₀ hU₁a hwU₁ P₁ X.S.N hN
  let u' : Sp (ratHull (X.M.ringOn U)) ⟶ Xo.XF cf := spMap (Subalgebra.inclusion (ratHull_mono (h₁.trans h))).toRingHom ≫ u₀
  have hu' : spMap (ratHull (X.M.ringOn U)).val.toRingHom ≫ u' = X.uΩ := by
    rw [← hu₀, ← Category.assoc, ← Spec.map_comp]
    rfl
  have hUO : UOver Xo cf P' (toRat (X.M.ringOn U)) u' := by
    refine (uOver_baseChange_iff hφ hφL (toRat (X.M.ringOn U))).2 ?_
    have h2 := hP₁.comp (Subalgebra.inclusion (ratHull_mono h)).toRingHom
    have e1 : (Subalgebra.inclusion (ratHull_mono h)).toRingHom.comp (toRat (X.M.ringOn U₁)) =
        (toRat (X.M.ringOn U)).comp (Subalgebra.inclusion h).toRingHom := RingHom.ext fun _ => rfl
    have e2 : spMap (Subalgebra.inclusion (ratHull_mono h)).toRingHom ≫
        spMap (Subalgebra.inclusion (ratHull_mono h₁)).toRingHom ≫ u₀ = u' := by
      rw [← Category.assoc, ← Spec.map_comp]
      rfl
    rw [e1, e2] at h2
    exact h2
  obtain ⟨G, _, α, β, hα, hβ, hLG⟩ := hUO
  have wβ : wi.β ≫ Xo.univ.t.G.hom = (wi.G.hom ≫ spMap (ratHull (X.M.ringOn U)).val.toRingHom) ≫ u' ≫ pullback.fst _ _ := by
    rw [wi.hβ.1.w, ← hu']
    simp only [Category.assoc]
  let m : wi.G.left ⟶ G.left := hβ.1.lift wi.β (wi.G.hom ≫ spMap (ratHull (X.M.ringOn U)).val.toRingHom) wβ
  have hm₁ : m ≫ β = wi.β := hβ.1.lift_fst _ _ _
  have hm₂ : m ≫ G.hom = wi.G.hom ≫ spMap (ratHull (X.M.ringOn U)).val.toRingHom := hβ.1.lift_snd _ _ _
  have hm : IsGrpPullback wi.G G (spMap (ratHull (X.M.ringOn U)).val.toRingHom) m :=
    hβ.cancel (wi.hβ.congr (by rw [← hu']; simp only [Category.assoc]) hm₁.symm) hm₂
  have hmα : IsGrpPullback wi.G P'.A (spMap (X.M.ringOn U).val.toRingHom) (m ≫ α) :=
    (hm.comp hα).congr (spMap_val_toRat (X.M.ringOn U)) rfl
  have hLU := Xo.univ.t.PP.isLB
  have hLρ := X.ρ.P.isLB
  have hLP := P'.isLB
  have hLw : LBIso (X.ρ.P.L.pull wi.α) (P'.L.pull (m ≫ α)) :=
    LBIso.trans (pull_isLB hLρ _) (pull_isLB hLU _) (pull_isLB hLP _) wi.hL
      (LBIso.trans (pull_isLB hLU _) (pull_isLB (pull_isLB hLU _) _) (pull_isLB hLP _)
        (GenSpread.lbIso_pull_pull hLU m hm₁.symm)
        (LBIso.trans (pull_isLB (pull_isLB hLU _) _) (pull_isLB (pull_isLB hLP _) _) (pull_isLB hLP _)
          (GenSpread.lbIso_pullback hLG.symm m) (GenSpread.lbIso_pull_pull hLP m rfl).symm))
  obtain ⟨P₀, a, a', e, he, hea, hea', ha, ha', hl, hl'⟩ :=
    GlobalTheory.UPoinc.exists_polAV_common_pullback X.Ω₁ (Sp X.S.R) (Sp (X.M.ringOn U)) X.ρ.P P' (spMap X.S.R.val.toRingHom) (spMap (X.M.ringOn U).val.toRingHom) wi.G wi.α (m ≫ α)
      wi.hα hmα hLw
  have hne : ((U : Set X.M.Z)).Nonempty := ⟨w₀, hwU⟩
  have hyp : HypS P'.A P'.L :=
    GlobalTheory.Poinc.hypS_of_generic_ringOn X.o₁ X.Ω₁ X.M U hUa hne X.normal X.S.R X.ρ.P P' P₀ _ a a' ha ha' hl hl' X.ρ.hypS
  have hg : P'.g = X.S.g :=
    (GlobalTheory.polAV_g_eq_of_isGrpPullback X.Ω₁ _ P' P₀ _ a' ha').symm.trans
      ((GlobalTheory.polAV_g_eq_of_isGrpPullback X.Ω₁ _ X.ρ.P P₀ _ a ha).trans X.ρ.g_eq)
  have fg : (X.M.ringOn U).FG := GlobalTheory.Poinc.fg_ringOn_of_isAffineOpen _ _ X.M U hUa hne
  have frac : ∀ x : X.Ω₁, ∃ a ∈ (X.M.ringOn U), ∃ b ∈ (X.M.ringOn U), x = a / b := fun x => by
    obtain ⟨p, q, -, e⟩ := RatModel.exists_eq_div hUa hne x
    exact ⟨_, (RatModel.mem_ringOn_iff_exists hne).2 ⟨p, rfl⟩, _, (RatModel.mem_ringOn_iff_exists hne).2 ⟨q, rfl⟩, e⟩
  haveI := RatModel.isFractionRing_ringOn hUa hne
  haveI : IsIntegrallyClosed (X.M.ringOn U) :=
    TorsExtend.isIntegrallyClosed_ringOn X.M ((isNormalScheme_iff_pred _).1 X.normal) hUa hne
  haveI := ArithBase.ded (o := X.o₁) (Ω := X.Ω₁)
  haveI : IsNoetherianRing (X.M.ringOn U) := isNoetherianRing_of_fg fg
  have hn : 1 ≤ X.S.r * X.S.N := Nat.mul_pos X.S.r_pos (le_trans one_le_two X.S.N_ge)
  have hu : IsUnit ((X.S.r * X.S.N : ℕ) : (X.M.ringOn U)) := by
    have := X.S.unit.map (algebraMap X.o₁ (X.M.ringOn U))
    rwa [map_natCast] at this
  obtain ⟨pt', hadd, hbij, h₃, hw0⟩ := TorsExtend.exists_labelled hL X.S.R.val.toRingHom X.ρ.P P' P₀ a a' ha ha' hl hl' hn hu
    (M := X.S.Gam) (fun x => by ext k; simp [nsmul_eq_mul, -Nat.cast_mul]) X.ρ.pt X.ρ.pt_add X.ρ.pt_bij
  have hweil : ∀ x y (c : (X.M.ringOn U)ˣ), (c : (X.M.ringOn U)) = algebraMap X.o₁ (X.M.ringOn U) (X.S.ζ ^ (X.S.r * X.S.N * (eStd X.S.g _ x y).val)) →
      WeilIs P'.A P'.L (X.S.r * X.S.N : ℕ) (pt' x) (pt' y) (unitOn c) := fun x y c hc => by
    obtain ⟨c₀, hc₀⟩ := ((X.S.prim.isUnit (by positivity)).pow (X.S.r * X.S.N * (eStd X.S.g _ x y).val)).map
      (algebraMap X.o₁ X.S.R)
    refine h₃ x y c₀ c ?_ (X.ρ.weil x y c₀ hc₀)
    rw [hc₀, hc]
    rfl
  let Q : (P : PolAV (Sp (X.M.ringOn U))) → (X.S.Gam → (baseOver (Sp (X.M.ringOn U)) ⟶ P.A)) → Prop := fun P pt =>
    (∃ (P₀ : PolAV (Sp X.Ω₁)) (a : P₀.A.left ⟶ X.ρ.P.A.left) (a' : P₀.A.left ⟶ P.A.left),
      IsGrpPullback P₀.A X.ρ.P.A (spMap ((RingHom.id _).comp X.S.R.val.toRingHom)) a ∧
      IsGrpPullback P₀.A P.A (spMap (X.M.ringOn U).val.toRingHom) a' ∧ LBIso P₀.L (X.ρ.P.L.pull a) ∧ LBIso P₀.L (P.L.pull a') ∧
      ∀ x, ∃ w : Sp X.Ω₁ ⟶ P₀.A.left, w ≫ a = spMap ((RingHom.id _).comp X.S.R.val.toRingHom) ≫ (X.ρ.pt x).left ∧
        w ≫ a' = spMap (X.M.ringOn U).val.toRingHom ≫ (pt x).left) ∧
    (∃ (G : Over (Sp (ratHull (X.M.ringOn U)))) (_ : GrpObj G) (α : G.left ⟶ P.A.left) (β : G.left ⟶ Xo.univ.t.G.left),
      IsGrpPullback G P.A (spMap (toRat (X.M.ringOn U))) α ∧ IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β ∧
      LBIso (P.L.pull α) (Xo.univ.t.PP.L.pull β) ∧
      ∃ m : wi.G.left ⟶ G.left, IsGrpPullback wi.G G (spMap (ratHull (X.M.ringOn U)).val.toRingHom) m ∧ m ≫ β = wi.β ∧
        ∀ x, ∃ w : Sp X.Ω₁ ⟶ wi.G.left, w ≫ wi.α = spMap X.S.R.val.toRingHom ≫ (X.ρ.pt x).left ∧
          w ≫ m ≫ α = spMap (X.M.ringOn U).val.toRingHom ≫ (pt x).left)
  have hQ : Q P' pt' := by
    refine ⟨⟨P₀, a, a', ha, ha', hl, hl', hw0⟩, G, inferInstance, α, β, hα, hβ, hLG, m, hm, hm₁, fun x => ?_⟩
    obtain ⟨w0, h₁, h₂⟩ := hw0 x
    refine ⟨w0 ≫ inv e, ?_, ?_⟩
    · rw [← hea, Category.assoc, IsIso.inv_hom_id_assoc, h₁]
    · rw [← hea', Category.assoc, IsIso.inv_hom_id_assoc]
      exact h₂
  obtain ⟨c₀, hc, hthm, hevm, ρ', ⟨hS₁, G', _, α', β', hα', hβ', hL', m', hm', hm₁', hpt'⟩, hi₀⟩ :=
    GlobalTheory.ThetaExtend.exists_real_rechart hL X.S X.ρ (X.M.ringOn U) fg frac P' P₀ a a' pt' th b ha ha' hl hl' hg hyp hadd hbij hweil
      hw0 hth hb Q hQ
  exact ⟨U, c₀, hc, fg, frac, hthm, hevm, ρ', u', hUa, hwU, hS₁, hi₀, hu', G', inferInstance, α', β', hα', hβ', hL', m',
    hm', hm₁', hpt'⟩
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

open GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR

theorem IntFam.existsUnique_over : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (k : ℕ)
    (F₀ : IntFam I D k) (F : Type) [Field F] [Algebra (FractionRing R) F], ∃! s : Fam D F k, F₀.Over s := by
  intro R _ _ I D k F₀ F _ _
  have hG : GlobalFnsSt := GlobalTheory.allSixLaws.1.globalFns
  have hL := D.P.isLB
  have hext : ∀ α, GeneratorPullback.SecScal D.P.L (DegPre.famφ D (FractionRing R) α) (DegPre.famε k) (F₀.F.s α)
      (D.famφB α) (DegPre.famε k) (F₀.f α) (DegPre.prB D (FractionRing R)).left 1 := fun α => by
    have h := F₀.ext α
    have e : scal (DegPre.BF D (FractionRing R)).hom (1 : R) = 1 := by
      unfold scal
      rw [map_one, map_one]
    rwa [e] at h
  have hov : F₀.Over (famPull D (FractionRing R) F hG k F₀.F) := fun α => by
    refine SectionScalarValuation.secScal_of_sval hL fun y J hJ => ?_
    refine Eq.trans ?_ (sval_pullOver _ _ _ _ hJ).symm
    refine Eq.trans ?_ (SectionScalarValuation.secScal_sval (hext α) _ y hJ)
    congr 1
    rw [Category.assoc, ← Over.comp_left, famMap_snd]
  refine ⟨_, hov, fun s hs => fam_ext fun α j => congrArg (fun q => LB.Sec.f q j)
    (sec_ext' hL fun y J hJ => ?_)⟩
  rw [← SectionScalarValuation.secScal_sval (hs α) (𝟙 _) y hJ, SectionScalarValuation.secScal_sval (hov α) (𝟙 _) y hJ]

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.RatConst

open scoped TensorProduct

theorem mem_range_of_tmul_eq {K F O : Type} [Field K] [Field F] [Algebra K F] [AddCommGroup O] [Module K O]
    {t u : O} {c : F} (ht : t ≠ 0) (h : (1 : F) ⊗ₜ[K] t = c ⊗ₜ[K] u) : ∃ x : K, algebraMap K F x = c := by
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one K ht
  have e := congrArg (fun v => TensorProduct.rid K F (LinearMap.lTensor F l v)) h
  simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, hl, one_smul, Algebra.smul_def] at e
  refine ⟨(l u)⁻¹, ?_⟩
  rw [map_inv₀]
  exact inv_eq_of_mul_eq_one_right (by simpa using e.symm)

theorem gs_spec {A B : CommRingCat.{0}} (h : A ⟶ B) (y : Spec B) (x : A) :
    gs (Spec.map h) y ⊤ ((Scheme.ΓSpecIso A).inv.hom x) = gs (𝟙 _) y ⊤ ((Scheme.ΓSpecIso B).inv.hom (h.hom x)) := by
  have e := congrArg (fun q => q.hom x) (Scheme.ΓSpecIso_inv_naturality h)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  rw [e]
  exact ((gs_pull (𝟙 _) (Spec.map h) y ⊤ trivial _).trans (by rw [Category.id_comp])).symm

theorem mem_of_stalk {X Z : Scheme.{0}} (f : Z ⟶ X) (z : Z) (U : X.Opens) (hz : f z ∈ U) (y : Spec (Z.presheaf.stalk z)) :
    f (Z.fromSpecStalk z y) ∈ U := by
  have : Z.fromSpecStalk z y ⤳ z := by
    have := Set.mem_range_self (f := Z.fromSpecStalk z) y
    rwa [Scheme.range_fromSpecStalk] at this
  exact (this.map f.continuous).mem_open U.isOpen hz

theorem gs_stalk {X Z : Scheme.{0}} (f : Z ⟶ X) (z : Z) (U : X.Opens) (hz : f z ∈ U) (a : Γ(X, U)) {B : CommRingCat.{0}}
    (h : Z.presheaf.stalk z ⟶ B) (y : Spec B) :
    gs (Spec.map h ≫ Z.fromSpecStalk z ≫ f) y U a = gs (𝟙 _) y ⊤ ((Scheme.ΓSpecIso B).inv.hom (h.hom (gs f z U a))) := by
  have m := mem_of_stalk f z U hz (Spec.map h y)
  rw [← gs_spec, ← Category.assoc, ← gs_pull _ f y U m, ← gs_pull _ (Z.fromSpecStalk z) y _ m,
    Scheme.fromSpecStalk_app (U := f ⁻¹ᵁ U) hz, gs_eq f z U hz]
  exact gs_res (Spec.map h) y le_top m _

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F], (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ (σ : SecK C.P.L.L T.β k) (s : SecK C.P.L.L C.α k) (c : F), (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left), p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ (fnF F c) * sval s (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z J) → (∃ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left) (_ : p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α) (_ : p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _))) (z : Z) (J : (Z ⟶ C.G.left) → C.P.L.L.ι), Good C.P.L.L z J ∧ sval σ p z J ≠ 0) → ∃ x : FractionRing W, algebraMap (FractionRing W) F x = c := by
  intro R _ _ _ _ D C k W _ _ _ T F _ _ _ hF σ s c H ⟨Z, p, p', h₁, h₂, z, J, hJ, hne⟩
  let O := Z.presheaf.stalk z
  obtain ⟨ρ, hρ⟩ : ∃ ρ : CommRingCat.of F ⟶ O,
      Spec.map ρ = Z.fromSpecStalk z ≫ p' ≫ (fst (TFK (R := R) F) C.A.A).left := ⟨Spec.preimage _, Spec.map_preimage _⟩
  letI : Algebra (FractionRing W) O := (ρ.hom.comp (algebraMap (FractionRing W) F)).toAlgebra
  let B := CommRingCat.of (F ⊗[FractionRing W] O)
  let iL : CommRingCat.of F ⟶ B := CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom
  let iR : O ⟶ B := CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := FractionRing W) (A := F) (B := O)).toRingHom
  have hK : ∀ x : FractionRing W, iR.hom (ρ.hom (algebraMap _ F x)) = iL.hom (algebraMap _ F x) := fun x =>
    ((Algebra.TensorProduct.includeRight (R := FractionRing W) (A := F) (B := O)).commutes x).trans rfl
  let g : Spec B ⟶ Z := Spec.map iR ≫ Z.fromSpecStalk z
  have hg : g ≫ p' ≫ (fst (TFK (R := R) F) C.A.A).left = Spec.map (ρ ≫ iR) := by
    rw [Spec.map_comp, hρ, Category.assoc]
  have w : (g ≫ p' ≫ (snd (TFK (R := R) F) C.A.A).left) ≫ C.A.A.hom = Spec.map iL ≫ jFK (R := R) F := by
    have e : (snd (TFK (R := R) F) C.A.A).left ≫ C.A.A.hom = (fst (TFK (R := R) F) C.A.A).left ≫ jFK (R := R) F :=
      (Over.w _).trans (Over.w (fst (TFK (R := R) F) C.A.A)).symm
    have e' : (g ≫ p' ≫ (snd (TFK (R := R) F) C.A.A).left) ≫ C.A.A.hom =
        (g ≫ p' ≫ (fst (TFK (R := R) F) C.A.A).left) ≫ jFK (R := R) F := by simp only [Category.assoc, e]
    rw [e', hg]
    refine (Spec.map_comp _ _).symm.trans (Eq.trans (congrArg Spec.map ?_) (Spec.map_comp _ _))
    refine CommRingCat.hom_ext (IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => ?_))
    exact (congrArg (fun q => iR.hom (ρ.hom q)) (hF r)).trans ((hK _).trans (congrArg iL.hom (hF r).symm))
  obtain ⟨q, q₁, q₂⟩ : ∃ q : Spec B ⟶ (TFK (R := R) F ⊗ C.A.A).left,
      q ≫ (fst (TFK (R := R) F) C.A.A).left = Spec.map iL ∧
      q ≫ (snd (TFK (R := R) F) C.A.A).left = g ≫ p' ≫ (snd (TFK (R := R) F) C.A.A).left := by
    let T' : Over (Sp (FractionRing R)) := Over.mk (Spec.map iL ≫ jFK (R := R) F)
    let a : T' ⟶ TFK (R := R) F := Over.homMk (Spec.map iL) rfl
    let b : T' ⟶ C.A.A := Over.homMk (g ≫ p' ≫ (snd (TFK (R := R) F) C.A.A).left) w
    exact ⟨(lift a b).left, congrArg (·.left) (lift_fst a b), congrArg (·.left) (lift_snd a b)⟩
  have k₁ : (g ≫ p) ≫ T.β = q ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α := by
    rw [← Category.assoc q, q₂, Category.assoc, h₁]; simp only [Category.assoc]
  have k₂ : (g ≫ p) ≫ T.G.hom = q ≫ (fst (TFK (R := R) F) C.A.A).left ≫
      spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) := by
    rw [← Category.assoc q, q₁, Category.assoc, h₂, ← Category.assoc p', ← Category.assoc g, hg]
    refine (Spec.map_comp _ _).symm.trans (Eq.trans (congrArg Spec.map ?_) (Spec.map_comp _ _))
    exact CommRingCat.hom_ext (RingHom.ext fun r => hK _)
  let u : O := sval s (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z J
  let t : O := sval σ p z J
  have key : iR.hom t = iL.hom c * iR.hom u := by
    apply (Scheme.ΓSpecIso B).symm.commRingCatIsoToRingEquiv.injective
    refine fn_ext (V := ⊤) fun y _ => ?_
    obtain ⟨J', hJ', e⟩ := exists_good C.P.L.L C.P.L.isLB y (K := Unit) (fun _ => (g ≫ p) ≫ T.β) (fun _ => J (p ≫ T.β))
      (fun _ _ _ => rfl) (fun _ => mem_of_stalk (p ≫ T.β) z _ (hJ _) (Spec.map iR y))
    have e := e ()
    have := H _ (g ≫ p) q k₁ k₂ y J' hJ'
    rw [sval_of σ _ y J' (fun _ => J (p ≫ T.β)) (fun _ => e),
      sval_of s _ y J' (fun _ => J ((p' ≫ (snd (TFK (R := R) F) C.A.A).left) ≫ C.α)) (fun _ => by
        rw [Category.assoc, ← k₁, Category.assoc p', ← h₁]; exact e), q₁, q₂] at this
    have a₁ := gs_stalk p z _ (hJ.mem (fun _ : Fin 1 => T.β) p) (σ.f fun _ => J (p ≫ T.β)) iR y
    have a₂ := gs_stalk (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z _
      (hJ.mem (fun _ : Fin 1 => C.α) (p' ≫ (snd (TFK (R := R) F) C.A.A).left))
      (s.f fun _ => J ((p' ≫ (snd (TFK (R := R) F) C.A.A).left) ≫ C.α)) iR y
    have a₃ := gs_spec iL y c
    simp only [g, Category.assoc] at this a₁ a₂
    refine a₁.symm.trans (this.trans (Eq.trans (congrArg₂ (· * ·) a₃ a₂) ?_))
    refine (gs_mul _ y ⊤ trivial _ _).symm.trans (congrArg _ ?_)
    simp only [u, sval, Category.assoc]
    exact (map_mul _ _ _).symm
  refine mem_range_of_tmul_eq (O := O) (t := t) (u := u) hne (key.trans ?_)
  exact (Algebra.TensorProduct.tmul_mul_tmul c 1 1 u).trans (by rw [_root_.mul_one, _root_.one_mul])

end GlobalTheory.Mum.RatConst
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.effectiveDivisor_pos_degree_ampleClass : ∀ (K : Type) [Field K] (A : AbVar K) (n : ℕ), A.dim = n + 1 → ∀ (c : Pic A.X.left), IsAmpleCls c → ∀ (M : LB A.X.left) (hM : M.IsLB) (s : LB.Sec M), Out.nonzeroLocus s ≠ ⊥ → Out.nonzeroLocus s ≠ ⊤ → 0 < inter A (Fin.cons (cls M hM) (fun _ : Fin n => c) : Fin (n + 1) → Pic A.X.left) := by
  first | exact @GlobalTheory.AV.EffPos.inter_cons_pos | exact GlobalTheory.AV.EffPos.inter_cons_pos | (intros; apply GlobalTheory.AV.EffPos.inter_cons_pos <;> assumption)
end
