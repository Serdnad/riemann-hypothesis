module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2929
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGlobalGenerators
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle183
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UnitThetaConstantsGenerateIntegralTorsion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WeightSpaceValuesIntegralTorsionBoundShortestVec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2926
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapInverseNatCast
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3388
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle129
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3132
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2932
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle070
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3254
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2862
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3389
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFineInvariantFan
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3391
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
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Poinc.PartLe

theorem ubound {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] {S : ThetaSys o Ω} {ρ : S.Real}
    {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀) (l : u.Lab)
    (hint : ∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) {m : ℕ} (hm : S.N = m ^ 2) {a : S.Gam} {χ : u.D.toPre.X}
    (ha : l.yy a = QuotientAddGroup.mk χ) (hmin : ∀ v, l.q χ ≤ l.q (χ + m • v)) {T : AddSubgroup S.Gam}
    (hT : T = S.perp l.yy.ker) (w : T →+ ZMod S.N)
    (hw : ∀ t : T, w t = ZMod.castHom (dvd_mul_left S.N S.r) (ZMod S.N) (eStd S.g _ (t : S.Gam) (m • a)))
    {h : S.Gam} (hh : h ∈ l.yy.ker) (i : S.J) :
    ‖y₀ (∑ j, algebraMap o S.R (S.proj T w j i) * ⟨S.ev h j, S.ev_mem h j⟩)‖ ≤ S.delta y₀ * Real.exp (-l.q χ) := by
  subst hT
  have hsc : ∀ x, l.q (m • x) = (m : ℝ) ^ 2 * l.q x := fun x => by
    rw [← natCast_zsmul, QuadraticMap.map_smul, zsmul_eq_mul]
    push_cast
    ring
  have hm0 : (m : ℝ) ^ 2 ≠ 0 := by
    have := GlobalTheory.ZH.GlobalGen.N_pos S
    rw [hm] at this
    exact_mod_cast this.ne'
  have hlab : l.yy (m • a) = QuotientAddGroup.mk (m • χ) := by
    rw [map_nsmul, ha, QuotientAddGroup.mk_nsmul]
  have hwt : w = l.wt (m • χ) := AddMonoidHom.ext fun t => (hw t).trans (l.wt_eq _ _ hlab t).symm
  have key := GlobalTheory.ZH.WeightBound.main GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2 GlobalTheory.ZH.uTors_closed o Ω S ρ p
    y₀ u l hint (m • χ) (fun v => by
      have e : m • χ + S.N • v = m • (χ + m • v) := by rw [hm, smul_add, smul_smul, sq]
      rw [e, hsc, hsc]
      exact mul_le_mul_of_nonneg_left (hmin v) (sq_nonneg _)) h hh i
  have e : l.q (m • χ) / S.N = l.q χ := by
    rw [hsc, hm, Nat.cast_pow, mul_div_cancel_left₀ _ hm0]
  rw [e, ← hwt] at key

  simpa only [map_sum, map_mul] using key



theorem main : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (z₁ : X₁.M.Z) (z₂ : D.X.M.Z), D.q z₂ = z₁ → ∀ (p : ℕ) [Fact p.Prime] (c : CTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X₁ ε₁ c yy₁ → ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y), y (cPt p) = z₂ → ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X), IsLab D.X D.ε (D.lift c y h) yy → D.Compat yy₁ yy → ∀ a ν κ, yy a = QuotientAddGroup.mk ν → (∀ χ, CongMod D.m χ ν → qW W c.T.β ν ≤ qW W c.T.β χ) → ‖D.X.M.val (gPt p ≫ y) (GSum.part D z₁ z₂ a κ)‖ ≤ Real.exp (-(c.sc * (qW W c.T.β ν : ℤ))) := by
  intro g n F W Z i X₁ h1 h2 h3 h4 h5 h6 h7 ε₁ h8 D z₁ z₂ hz p _ c yy₁ _ y h hy yy hl _ a ν κ hν hmin
  subst hy
  obtain ⟨-, hHH⟩ := GlobalTheory.Poinc.isLab_onto_and_ker g n F W Z i D.X h1 h2 h3 h4 h5 h6 D.proj D.ε D.diag p _ (D.lift c y h) yy hl
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', ε', -, -, hR', y₀, hy₀, u, l, j, hq, hyy, -⟩ := hl
  have hlift : ∀ (b : D.X.S.Gam) μ, yy b = QuotientAddGroup.mk μ → l.yy b = QuotientAddGroup.mk (j.symm μ) := by
    intro b μ hb
    obtain ⟨χ, hχ⟩ := QuotientAddGroup.mk_surjective (l.yy b)
    have e1 := hyy b χ hχ.symm
    rw [hb, QuotientAddGroup.eq] at e1
    obtain ⟨w, hw⟩ := e1
    rw [← hχ, eq_comm, QuotientAddGroup.eq]
    refine ⟨j.symm w, ?_⟩
    simp only [nsmulAddMonoidHom_apply] at hw ⊢
    rw [← map_nsmul, hw, map_add (f := _), map_neg, j.symm_apply_apply]
  have hker : yy.ker = l.yy.ker := by
    ext b
    simp only [AddMonoidHom.mem_ker]
    constructor
    · intro hb
      have := hlift b 0 hb
      rwa [map_zero] at this
    · intro hb
      have := hyy b 0 hb
      rwa [map_zero] at this
  have hint : ∀ a : D.X.o₁, ‖y₀ (algebraMap D.X.o₁ R' a)‖ ≤ 1 := fun a => by
    rw [hy₀]
    exact RatModel.norm_val_le_one rfl ((D.X.M.O _).algebraMap_mem a)
  have hδ0 := (GlobalTheory.UnitTheta.closure_unit_theta GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2
    GlobalTheory.ZH.uTors_closed _ _ _ ρ' p y₀ u l hint).1
  have hb : GSum.base X₁ z₁ ∈ X₁.S.supI X₁.M z₁ := by
    have hne : (X₁.S.supI X₁.M z₁).Nonempty := X₁.div z₁
    rw [GSum.base, dite_eq_left hne]
    exact hne.some_mem
  have hx₀ := GlobalTheory.T.thetaSetup_dividingLabel_persists_deeperLevel g n F W Z i X₁ h1 h2 h3 h4 h5 h6 h7 ε₁ h8 D z₁ _ hb _ hz
  have hmem : GSum.lift D (y (cPt p)) (κ : X₁.S.Gam) ∈ l.yy.ker := by
    rw [← hker, hHH, GSum.lift]
    split_ifs with hex
    · exact hex.choose_spec.1
    · exact zero_mem _
  have key := ubound (S := D.X.S.rechart c₀ hc R' fg frac hth hev) u l hint (m := D.m) D.sq (hlift a ν hν) (fun v => by
      rw [hq, hq, map_add (f := _), map_nsmul, j.apply_symm_apply]
      exact mul_le_mul_of_nonneg_left (Int.cast_le.2 (hmin _ ⟨j v, rfl⟩)) c.scale_pos.le)
    (T := D.X.S.TT D.X.M (y (cPt p))) (by rw [← hker, hHH]; rfl) (GSum.wtChar D _ a) (fun _ => rfl) hmem D.X.ρ.i₀
  rw [hq, j.apply_symm_apply, hy₀] at key
  unfold GSum.part
  generalize D.lab (GSum.base X₁ z₁) = x₀ at hx₀
  set Sg := ∑ j, algebraMap D.X.o₁ D.X.Ω₁ (D.X.S.proj (D.X.S.TT D.X.M (y (cPt p))) (GSum.wtChar D _ a) j D.X.ρ.i₀) *
      D.X.S.ev (GSum.lift D (y (cPt p)) (κ : X₁.S.Gam)) j with hSg
  have hsp : ∀ w, (gPt p ≫ y) w ⤳ (gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p)) :=
    RatModel.specializes_of_range_eq (RatModel.range_eq_singleton _ _)
  have hgz : (gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p)) ⤳ y (cPt p) := RatModel.gPt_specializes rfl _
  have hle : (D.X.S.rechart c₀ hc R' fg frac hth hev).delta y₀ ≤ ‖D.X.M.val (gPt p ≫ y) (c₀ * D.X.S.th x₀)‖ := by
    refine ciSup_le fun x => (congrArg norm (hy₀ _)).trans_le ?_
    show ‖D.X.M.val (gPt p ≫ y) (c₀ * D.X.S.th x)‖ ≤ _
    have e : c₀ * D.X.S.th x = D.X.S.th x / D.X.S.th x₀ * (c₀ * D.X.S.th x₀) := by
      have := hx₀.1
      field_simp
    rw [e, RatModel.val_mul hsp (RatModel.O_le_of_specializes hgz (hx₀.2 x)) (hR' (hth _)), norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (RatModel.norm_val_le_one rfl (hx₀.2 x))
  have hpos := hδ0.trans_le hle
  have hSR : c₀ * Sg ∈ R' := by
    rw [hSg, Finset.mul_sum]
    refine sum_mem fun k _ => ?_
    rw [mul_left_comm]
    exact mul_mem (R'.algebraMap_mem _) (hev _ _)
  have key' : ‖D.X.M.val (gPt p ≫ y) (c₀ * Sg)‖ ≤ ‖D.X.M.val (gPt p ≫ y) (c₀ * D.X.S.th x₀)‖ *
      Real.exp (-(c.sc * (qW W c.T.β ν : ℤ))) := by
    refine le_trans (le_of_eq ?_) (key.trans (mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le))
    congr 2
    rw [hSg, Finset.mul_sum, AddSubmonoidClass.coe_finsetSum]
    exact Finset.sum_congr rfl fun k _ => mul_left_comm _ _ _
  have hO : Sg / D.X.S.th x₀ ∈ D.X.M.O ((gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p))) := by
    obtain ⟨v, hv⟩ := ((RatModel.val_ne_zero_iff (RatModel.range_eq_singleton (gPt p ≫ y) _)
      ⟨c₀ * D.X.S.th x₀, hR' (hth x₀)⟩).1 (norm_pos_iff.1 hpos)).exists_right_inv
    have hv' : c₀ * D.X.S.th x₀ * (v : D.X.Ω₁) = 1 := congrArg Subtype.val hv
    have e : Sg / D.X.S.th x₀ = c₀ * Sg * v := by
      rw [div_eq_iff hx₀.1]
      linear_combination (-Sg) * hv'
    rw [e]
    exact mul_mem (hR' hSR) v.2
  have e : c₀ * Sg = Sg / D.X.S.th x₀ * (c₀ * D.X.S.th x₀) := by
    have := hx₀.1
    field_simp
  rw [e, RatModel.val_mul hsp hO (hR' (hth _)), norm_mul, mul_comm] at key'
  exact le_of_mul_le_mul_left key' hpos

end GlobalTheory.Poinc.PartLe
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.GalPart

open GlobalTheory.UPoinc.USum

section General

open MonObj

variable {o Ω o' Ω' : Type} [CommRing o] [Field Ω] [Algebra o Ω] [CommRing o'] [Field Ω'] [Algebra o' Ω']
  {S : ThetaSys o Ω} {S' : ThetaSys o' Ω'} {ρ : S.Real} {ρ' : S'.Real} {lab : S.Gam → S'.Gam} {φ : Ω →+* Ω'}
  {P₀ : PolAV (Sp Ω')} {a : P₀.A.left ⟶ ρ.P.A.left} {a' : P₀.A.left ⟶ ρ'.P.A.left}

theorem exists_isGenLab_of (h₁ : IsGrpPullback P₀.A ρ.P.A (spMap (φ.comp S.R.val.toRingHom)) a)
    (h₂ : IsGrpPullback P₀.A ρ'.P.A (spMap S'.R.val.toRingHom) a') (l₁ : LBIso P₀.L (ρ.P.L.pull a))
    (l₂ : LBIso P₀.L (ρ'.P.L.pull a'))
    (hpt : ∀ x, ∃ w : Sp Ω' ⟶ P₀.A.left, w ≫ a = spMap (φ.comp S.R.val.toRingHom) ≫ (ρ.pt x).left ∧
      w ≫ a' = spMap S'.R.val.toRingHom ≫ (ρ'.pt (lab x)).left) :
    ∃ x, IsGenLab ρ ρ' lab φ P₀ a a' x ∧ ∀ b b', x (b + b') = x b * x b' := by
  obtain ⟨w, hw, hadd, -⟩ := GalAct.exists_generic_labels ρ' h₂
  obtain ⟨e, he⟩ := GalAct.exists_mulEquiv_points h₁ (𝟙 _) _ (Category.id_comp _)
  have := GalTrans.mono_val S'.R S'.frac
  have : Mono a' := (MorphismProperty.monomorphisms Scheme).of_isPullback h₂.1.flip (.infer_property _)
  refine ⟨fun b => e (w b), ⟨h₁, h₂, l₁, l₂, fun b => ⟨(w b).left, Over.w (w b), (he _).symm, hw b⟩,
    fun k => ?_⟩, fun b b' => by simp only [hadd, map_mul]⟩
  obtain ⟨v, hv, hv'⟩ := hpt k
  obtain rfl : v = (w (lab k)).left := (cancel_mono a').1 (hv'.trans (hw _).symm)
  exact Over.OverMorphism.ext ((he _).trans hv)

variable {x : S'.Gam → (genPt (φ.comp S.R.val.toRingHom) ⟶ ρ.P.A)}

theorem exists_conj_over (hx : IsGenLab ρ ρ' lab φ P₀ a a' x) (σ : Ω' →+* Ω') (hσ : Function.Surjective σ)
    (hφ : σ.comp φ = φ) : ∃ (g : S'.Gam ≃+ S'.Gam)
      (s : genPt (φ.comp S.R.val.toRingHom) ⟶ genPt (φ.comp S.R.val.toRingHom)) (t : P₀.A.left ⟶ P₀.A.left),
      s.left = spMap σ ∧ (∀ b, x (g b) = s ≫ x b) ∧ (∀ k, g (lab k) = lab k) ∧ t ≫ a = a ∧
      IsGrpPullback P₀.A P₀.A (spMap σ) t ∧ LBIso P₀.L (P₀.L.pull t) ∧
      ∀ y (w w' : Sp Ω' ⟶ P₀.A.left), w ≫ a' = spMap S'.R.val.toRingHom ≫ (ρ'.pt y).left →
        w' ≫ t = spMap σ ≫ w → w' ≫ a' = spMap S'.R.val.toRingHom ≫ (ρ'.pt (g y)).left := by
  obtain ⟨h₁, h₂, l₁, l₂, hw, hlab⟩ := hx
  have hs : spMap σ ≫ spMap (φ.comp S.R.val.toRingHom) = spMap (φ.comp S.R.val.toRingHom) :=
    GalTrans.sp_comp (by rw [← RingHom.comp_assoc, hφ])
  obtain ⟨t, ht₁, ht₂⟩ : ∃ t : P₀.A.left ⟶ P₀.A.left, t ≫ a = a ∧ t ≫ P₀.A.hom = P₀.A.hom ≫ spMap σ :=
    ⟨h₁.1.lift a (P₀.A.hom ≫ spMap σ) (by rw [Category.assoc, hs, h₁.1.w]), h₁.1.lift_fst _ _ _, h₁.1.lift_snd _ _ _⟩
  have ht : IsGrpPullback P₀.A P₀.A (spMap σ) t := h₁.cancel (h₁.congr hs.symm ht₁.symm) ht₂
  have lt : LBIso (P₀.L.pull t) (ρ.P.L.pull a) :=
    l₁.chartPull (Geo.Tor.chartPullPull P₀.L t t rfl)
      (chartPullSame ρ.P.L (fun _ => a) (fun _ => a) _ t fun _ => ht₁.symm)
  obtain ⟨g, hg, hg'⟩ := GalAct.exists_label_action ρ' h₂ σ hσ ht
  have := GalTrans.mono_val S'.R S'.frac
  have : Mono a' := (MorphismProperty.monomorphisms Scheme).of_isPullback h₂.1.flip (.infer_property _)
  refine ⟨g, Over.homMk (spMap σ) hs, t, rfl, fun b => Over.OverMorphism.ext ?_, fun k => ?_, ht₁, ht,
    LBIso.trans P₀.isLB (pull_isLB ρ.P.isLB _) (pull_isLB P₀.isLB _) l₁ lt.symm, hg⟩
  · obtain ⟨w, e₀, e₁, e₂⟩ := hw b
    obtain ⟨w', -, e₁', e₂'⟩ := hw (g b)
    have c : (spMap σ ≫ w) ≫ P₀.A.hom = 𝟙 _ ≫ spMap σ := by rw [Category.assoc, e₀]; simp
    have k := ht.1.lift_fst _ _ c
    obtain rfl : w' = ht.1.lift _ _ c := (cancel_mono a').1 (e₂'.trans (hg b w _ e₂ k).symm)
    rw [← e₁', ← ht₁, reassoc_of% k, e₁]
    rfl
  · obtain ⟨w, e₀, e₁, e₂⟩ := hw (lab k)
    refine hg' _ w e₂ (h₁.1.hom_ext ?_ ?_)
    · rw [Category.assoc, Category.assoc, ht₁, e₁, hlab]
      exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hs)).symm
    · rw [Category.assoc, Category.assoc, ht₂, reassoc_of% e₀, e₀, Category.comp_id]


open Classical in
theorem exists_root_conj [ArithBase o Ω] [ArithBase o' Ω'] (hx : IsGenLab ρ ρ' lab φ P₀ a a' x)
    (hadd : ∀ b b', x (b + b') = x b * x b') {m : ℕ} (hm : S'.N = m ^ 2) (H : AddSubgroup S'.Gam) (x₀ : S.Gam)
    (h₀ : S.th x₀ ≠ 0) (h₀' : S'.th (lab x₀) ≠ 0) {κ : S.Gam} {h : S'.Gam} (hh : h ∈ H) (e : m • h = lab κ) :
    ∃ ξ : Ω', (∃ k : ℕ, 0 < k ∧ ξ ^ k = 1) ∧ ∀ (σ : Ω' →+* Ω'), σ.comp φ = φ →
      ∀ (s : genPt (φ.comp S.R.val.toRingHom) ⟶ genPt (φ.comp S.R.val.toRingHom)), s.left = spMap σ →
      ∀ g : S'.Gam ≃+ S'.Gam, (∀ b, x (g b) = s ≫ x b) → (∀ k, g (lab k) = lab k) → (∀ y, g y ∈ H ↔ y ∈ H) →
      ∀ b, σ (ξ * (partV S' H ρ'.i₀ b h / S'.th (lab x₀))) = ξ * (partV S' H ρ'.i₀ (g b) h / S'.th (lab x₀)) := by
  have := Fintype.ofFinite (S'.perp H)
  choose V hV₁ using fun t : S'.perp H => TV.ex hx hadd hm t e
  have hV : ∀ h' ∈ H, m • h' = lab κ → ∀ t : S'.perp H, TV ρ x m t h' κ (V t) := fun h' hh' e' t => by
    have := (hV₁ t).transl hx hadd hm (k := h' - h) (by rw [smul_sub, e, e', sub_self]) (t.2 _ (sub_mem hh' hh))
    rwa [add_sub_cancel] at this
  have hφ₀ : φ (S.th x₀) ≠ 0 := (map_ne_zero φ).2 h₀
  obtain ⟨ξ, hξ, hc⟩ := GlobalTheory.T.twistedThetaValue_eq_root_mul_thetaOperatorValue ρ ρ' lab φ P₀ a a' x hx m hm κ x₀ h e
  have hf : ∀ b, ξ * (partV S' H ρ'.i₀ b h / S'.th (lab x₀)) =
      algebraMap o' Ω' (Ring.inverse (Nat.card (S'.perp H) : o')) *
        (∑ t : S'.perp H, algebraMap o' Ω' (S'.ζN ^ (-(wtChar S' _ b t)).val) * V t) / φ (S.th x₀) := fun b => by
    have hv : ∀ t : S'.perp H, V t =
        (ξ * φ (S.th x₀) / S'.th (lab x₀)) * ∑ j, algebraMap o' Ω' (S'.ρ t j ρ'.i₀) * S'.ev h j := fun t => by
      rw [div_mul_eq_mul_div, eq_div_iff h₀']
      exact hc t _ (hV₁ t)
    simp only [hv, partV_eq, mul_left_comm _ (ξ * φ (S.th x₀) / S'.th (lab x₀)), ← Finset.mul_sum]
    field_simp
  refine ⟨ξ, hξ, fun σ hφ s hs g hg hl hH b => ?_⟩
  have hw := hx.weil_conj σ s hs hg
  have h0 : ∀ y y', eStd S'.g _ y y' = 0 ↔ eStd S'.g _ (g y) (g y') = 0 := fun y y' => by
    rw [← zeta_pow_eq_one_iff, ← zeta_pow_eq_one_iff, ← hw, map_eq_one_iff σ σ.injective]
  have hT : ∀ t, t ∈ S'.perp H ↔ g t ∈ S'.perp H := fun t =>
    ⟨fun ht y hy => by
      obtain ⟨y, rfl⟩ := g.surjective y
      exact (h0 _ _).1 (ht y ((hH y).1 hy)), fun ht y hy => (h0 _ _).2 (ht _ ((hH y).2 hy))⟩
  let e' : S'.perp H ≃ S'.perp H := g.toEquiv.subtypeEquiv hT
  have hζ : ∀ t : S'.perp H, σ (algebraMap o' Ω' (S'.ζN ^ (-(wtChar S' _ b t)).val)) =
      algebraMap o' Ω' (S'.ζN ^ (-(wtChar S' _ (g b) (e' t))).val) := fun t => by
    have e₁ : σ (algebraMap o' Ω' (S'.ζN ^ (wtChar S' _ b t).val)) =
        algebraMap o' Ω' (S'.ζN ^ (wtChar S' _ (g b) (e' t)).val) := by
      refine (congrArg (fun q => σ (algebraMap o' Ω' q)) (zetaN_pow_cast _)).trans
        (Eq.trans ?_ (congrArg (algebraMap o' Ω') (zetaN_pow_cast _)).symm)
      rw [map_pow, map_pow, hw, ← map_pow]
      rfl
    have e₂ := congrArg (fun q => σ (algebraMap o' Ω' q)) (zetaN_neg_mul (wtChar S' _ b t))
    have e₃ := congrArg (algebraMap o' Ω') (zetaN_neg_mul (wtChar S' _ (g b) (e' t)))
    simp only [map_mul, map_one] at e₂ e₃
    rw [e₁] at e₂
    exact (eq_inv_of_mul_eq_one_left e₂).trans (eq_inv_of_mul_eq_one_left e₃).symm
  have hσV : ∀ t : S'.perp H, σ (V t) = V (e' t) := fun t =>
    ((hV₁ t).conj σ s hs g.toAddMonoidHom hg).unique ρ'
      (hV (g h) ((hH h).2 hh) (by rw [← map_nsmul, e, hl]) (e' t))

  rw [hf, hf, map_div₀, map_mul, map_inverse_natCast, map_sum,
  show σ (φ (S.th x₀)) = φ (S.th x₀) from RingHom.congr_fun hφ _,
  ← Equiv.sum_comp e' fun t => algebraMap o' Ω' (S'.ζN ^ (-(wtChar S' _ (g b) t)).val) * V t]
  simp only [map_mul, hζ, hσV]

end General

theorem exists_root_galois : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (z₁ : X₁.M.Z) (z₂ : D.X.M.Z), D.q z₂ = z₁ → ∃ U : X₁.S.HH X₁.M z₁ → D.X.Ω₁, (∀ κ, ∃ k : ℕ, 0 < k ∧ U κ ^ k = 1) ∧ ∀ σ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁, ∃ a : D.X.S.Gam ≃+ D.X.S.Gam, D.GalLab σ a ∧ (∀ x, a (D.lab x) = D.lab x) ∧ ((∀ x, a x ∈ D.X.S.HH D.X.M z₂ ↔ x ∈ D.X.S.HH D.X.M z₂) → ∀ b κ, σ (U κ * GSum.part D z₁ z₂ b κ) = U κ * GSum.part D z₁ z₂ (a b) κ) := by
  intro g n F W Z i X₁ hg hn hodd hi hE hT hP ε₁ hε₁ D z₁ z₂ hq
  obtain ⟨P₀, a₁, a₂, ε₀, h₁, h₂, l₁, l₂, hε, hpt⟩ := D.same
  obtain ⟨x, hx, hadd⟩ := exists_isGenLab_of h₁ h₂ l₁ l₂ hpt
  have hb : GSum.base X₁ z₁ ∈ X₁.S.supI X₁.M z₁ := by
    have hne : (X₁.S.supI X₁.M z₁).Nonempty := X₁.div z₁
    rw [GSum.base, dite_eq_left hne]
    exact hne.some_mem
  have hb' := GlobalTheory.T.thetaSetup_dividingLabel_persists_deeperLevel g n F W Z i X₁ hg hn hodd hi hE hT hP ε₁ hε₁ D z₁ _ hb z₂ hq
  have hl : ∀ κ : X₁.S.Gam, GSum.lift D z₂ κ ∈ D.X.S.HH D.X.M z₂ ∧ ∃ κ', D.m • GSum.lift D z₂ κ = D.lab κ' := fun κ => by
    by_cases h : ∃ h' ∈ D.X.S.HH D.X.M z₂, D.m • h' = D.lab κ
    · rw [GSum.lift, dite_eq_left h]
      exact ⟨h.choose_spec.1, κ, h.choose_spec.2⟩
    · rw [GSum.lift, dite_eq_right h]
      exact ⟨zero_mem _, 0, by rw [smul_zero, map_zero]⟩
  choose U hU hσU using fun κ : X₁.S.HH X₁.M z₁ =>
    exists_root_conj hx hadd D.sq (D.X.S.HH D.X.M z₂) _ hb.1 hb'.1 (hl κ).1 (hl κ).2.choose_spec
  refine ⟨U, hU, fun σ => ?_⟩
  have hφ : (σ : D.X.Ω₁ →+* D.X.Ω₁).comp (algebraMap X₁.Ω₁ D.X.Ω₁) = algebraMap X₁.Ω₁ D.X.Ω₁ :=
    RingHom.ext fun y => σ.commutes y
  obtain ⟨a, s, t, hs, ha, hlab, ht₁, ht, lt, hpt'⟩ := exists_conj_over hx (σ : D.X.Ω₁ →+* D.X.Ω₁) σ.surjective hφ
  refine ⟨a, ⟨P₀, a₂, t, ε₀, h₂, ht, l₂, lt, fun E => ⟨(hε E).2, ?_⟩, hpt'⟩, hlab, fun hH b κ => ?_⟩
  · have ht₂ := ht.1.w
    refine h₁.1.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, ht₁, (hε E).1, ← Category.assoc, ht₁]
    · rw [Category.assoc, Category.assoc, ht₂, Over.w (ε₀ E), ← Category.assoc, Over.w (ε₀ E), ht₂]
  · have key := hσU κ _ hφ s hs a ha hlab hH (D.m • b)
    rw [map_nsmul] at key
    exact key

end GlobalTheory.Poinc.GalPart
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum GlobalTheory.MumFam

namespace GlobalTheory.MumIsoAdj

section

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
  {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

theorem linHom_unique (hR : Base R) (hG : IsSemiAbelian G) {U : Unif (maximalIdeal R) D A G} {a a' k k' g g'}
    (h : LinHom U.toUnifPre U.toUnifPre a k g) (h' : LinHom U.toUnifPre U.toUnifPre a' k' g') (ha : a = a')
    (hk : ∀ y, k y = k' y) : g = g' := by
  obtain rfl := ha
  obtain rfl : k = k' := AddMonoidHom.ext hk
  obtain ⟨u₁, u₂⟩ := GlobalTheory.MumUniq.main R hR.1 D A G hG U a k
  exact u₂ g g' (congrFun (u₁ _ _ (linHom_iff_linEnd.1 h).2 (linHom_iff_linEnd.1 h').2))

end

theorem iso_of_factor_adj : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre), F.Alg → ∀ (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ (A₀ : PolAV (Sp (FractionRing R))) (G₀ : Over (Sp R)) [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G₀ → ∀ U₀ : Unif (maximalIdeal R) D A₀ G₀, ∃ (ε : G ≅ G₀) (u : G' ⟶ G₀) (u' : G₀ ⟶ G'), IsMonHom ε.hom ∧ IsMonHom u ∧ IsMonHom u' ∧ ε.hom = inc ≫ u ∧ u ≫ u' = oG.act (Star.star F.e * F.f * F.e) ∧ GAdj U'.LG.L U₀.LG.L u u' := by
  intro R _ _ _ hR D D' F hF A' G' _ _ hG' U' oA oG hlin G _ _ hG inc pr hinc hpr hip hpi A₀ G₀ _ _ hG₀ U₀
  obtain ⟨-, hsym, g, hg⟩ := hF
  obtain ⟨u, u', hu, hu', hadj⟩ :=
    GlobalTheory.T.uniformisedGroups_adjointHomPair_closedForm R hR D' A' G' hG' U' D A₀ G₀ hG₀ U₀ _ _ _ _ (GlobalTheory.T.idempotentFactor_projection_adjointPair R _ D D' F)
  have hO : ∀ a : F.O, LinHom U'.toUnifPre U'.toUnifPre (F.o.onB.act a)
      (DistribSMul.toAddMonoidHom D'.toPre.X (Star.star a)) (oG.act a) := fun a =>
    ⟨oG.hom a, fun e => hlin.q_lin e a, fun e => by
      obtain ⟨t, ht, hi⟩ := hlin.i_lin e a
      exact ⟨t, ht, hi⟩⟩
  have hu1 := hu.1
  have hu1' := hu'.1
  have hee : Star.star F.e * Star.star F.e = Star.star F.e := by rw [← star_mul, F.idem]
  have hsS : Star.star (Star.star F.e * F.f * F.e) = Star.star F.e * F.f * F.e := by
    rw [star_mul, star_mul, star_star, ← _root_.mul_assoc, ← hsym]
  have hsg : (Star.star F.e * F.f * F.e) * Star.star g = Star.star F.e := by
    have := congrArg Star.star hg
    rwa [star_mul, hsS] at this
  have hkey : F.e * Star.star g * (Star.star F.e * F.f * F.e) = F.e := by
    calc F.e * Star.star g * (Star.star F.e * F.f * F.e)
        = g * ((Star.star F.e * F.f * F.e) * Star.star g) * (Star.star F.e * F.f * F.e) := by
          nth_rewrite 1 [← hg]; simp only [_root_.mul_assoc]
      _ = g * (Star.star F.e * (Star.star F.e * F.f * F.e)) := by rw [hsg, _root_.mul_assoc]
      _ = F.e := by
          rw [← _root_.mul_assoc (Star.star F.e) (Star.star F.e * F.f) F.e,
            ← _root_.mul_assoc (Star.star F.e) (Star.star F.e) F.f, hee, hg]
  have hxi : ∀ y, F.xi y = F.e • F.xi y := fun y => by rw [← F.xi_xp, F.xp_xi]
  have hincE : F.inc ≫ F.o.onB.act F.e = F.inc := by
    rw [← F.pr_inc, ← Category.assoc, F.inc_pr, Category.id_comp]
  have h1 : u ≫ u' = oG.act (Star.star F.e * F.f * F.e) :=
    GlobalTheory.MumIsoAdj.linHom_unique hR hG' (hu.comp hu') (hO _)
      (by rw [F.o.onB.map_mul (Star.star F.e * F.f) F.e, ← F.pr_inc]; exact (Category.assoc _ _ _).symm)
      (fun y => by
        change (Star.star F.e * F.f) • F.xi (F.xp y) = Star.star (Star.star F.e * F.f * F.e) • y
        rw [hsS, F.xi_xp, smul_smul])
  have h2 : u' ≫ oG.act (F.e * g) ≫ u = 𝟙 G₀ :=
    GlobalTheory.MumIsoAdj.linHom_unique hR hG₀ ((hu'.comp (hO _)).comp hu) (LinHom.id _)
      (by
        calc ((F.inc ≫ F.o.onB.act (Star.star F.e * F.f)) ≫ F.o.onB.act (F.e * g)) ≫ F.pr
            = F.inc ≫ F.o.onB.act ((F.e * g) * (Star.star F.e * F.f * F.e)) ≫ F.pr := by
              rw [F.o.onB.map_mul (F.e * g) (Star.star F.e * F.f * F.e),
                F.o.onB.map_mul (Star.star F.e * F.f) F.e]
              conv_lhs => rw [← hincE]
              simp only [Category.assoc]
          _ = 𝟙 _ := by
              rw [_root_.mul_assoc F.e g, hg, F.idem, ← F.pr_inc]
              simp only [← Category.assoc, F.inc_pr, Category.id_comp])
      (fun y => by
        change F.xp (Star.star (F.e * g) • ((Star.star F.e * F.f) • F.xi y)) = y
        have hw : Star.star (F.e * g) • ((Star.star F.e * F.f) • F.xi y) =
            (Star.star g * (Star.star F.e * F.f * F.e)) • F.xi y := by
          conv_lhs => rw [hxi y]
          rw [smul_smul, smul_smul, star_mul]
          congr 1
          simp only [_root_.mul_assoc]
          rw [← _root_.mul_assoc (Star.star F.e) (Star.star F.e), hee]
        have h3 : F.xi (F.xp (Star.star (F.e * g) • ((Star.star F.e * F.f) • F.xi y))) = F.xi y := by
          rw [F.xi_xp, hw, smul_smul, ← _root_.mul_assoc, hkey, ← hxi]
        have := congrArg F.xp h3
        rwa [F.xp_xi, F.xp_xi] at this)
  refine ⟨⟨inc ≫ u, u' ≫ oG.act g ≫ pr, ?_, ?_⟩, u, u', inferInstance, hu.1, hu'.1, rfl, h1, hadj⟩
  · calc (inc ≫ u) ≫ u' ≫ oG.act g ≫ pr = inc ≫ ((u ≫ u') ≫ oG.act g) ≫ pr := by simp only [Category.assoc]
      _ = 𝟙 G := by
          rw [h1, ← oG.map_mul, hg, ← hpi]
          simp only [← Category.assoc, hip, Category.id_comp]
  · calc (u' ≫ oG.act g ≫ pr) ≫ inc ≫ u = u' ≫ (oG.act g ≫ pr ≫ inc) ≫ u := by simp only [Category.assoc]
      _ = 𝟙 G₀ := by rw [hpi, ← oG.map_mul, h2]

end GlobalTheory.MumIsoAdj
end

section

namespace GlobalTheory.Published

theorem toroidalCharts_of_siegel_of_forFan (hS : GlobalTheory.Published.SiegelToroidalIntegral) (hF : GlobalTheory.Published.ToroidalChartsForFan) :
    GlobalTheory.Published.ToroidalCharts := by
  refine hF.toroidalCharts fun E _ _ _ H q => ?_
  obtain ⟨φs, hφ, -⟩ := hS (Module.finrank ℚ E * q + 1) (Nat.le_add_left _ _)
  obtain ⟨φ, h₁, h₂, -⟩ := GlobalTheory.PolFan.exists_fine_invariant_fan H hφ (Nat.le_succ _) ∅ (by simp)
  exact ⟨φ, h₁, h₂⟩

end GlobalTheory.Published
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CechPic GlobalTheory.AbDual

theorem _root_.GlobalTheory.T.flat_of_dual_homomorphism_kernel_killed : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (Q : LB (A ⊗ B).left) (la : A ⟶ B) (d : ℕ), IsAbelianScheme A → IsAbelianScheme B → IsDual A B Q → IsDual B A (swap Q) → IsMonHom la → 0 < d → (∀ (T : Over S) (x : T ⟶ A), x ≫ la = 1 → x ^ d = 1) → Flat la.left := by
  first | (exact @GlobalTheory.DualHomFlat.main) | (exact GlobalTheory.DualHomFlat.main) | (intros; apply GlobalTheory.DualHomFlat.main  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CechPic GlobalTheory.AbDual

theorem _root_.GlobalTheory.T.surjective_of_dual_homomorphism_kernel_killed : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (Q : LB (A ⊗ B).left) (la : A ⟶ B) (d : ℕ), IsAbelianScheme A → IsAbelianScheme B → IsDual A B Q → IsDual B A (swap Q) → IsMonHom la → 0 < d → (∀ (T : Over S) (x : T ⟶ A), x ≫ la = 1 → x ^ d = 1) → Surjective la.left := by
  first | (exact @GlobalTheory.DualHomSurj.surjective_of_ker_killed) | (exact GlobalTheory.DualHomSurj.surjective_of_ker_killed) | (intros; apply GlobalTheory.DualHomSurj.surjective_of_ker_killed  <;> assumption)
end
