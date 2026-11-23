module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2939
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.DeltaIsGreatest
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3085
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2640
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3184
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle129
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3128
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3130
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiGeneratorComponentsTorusExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3129
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3127
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2924
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2802
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3105
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3187
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterLatticeUnitaryClassicalTraitCentre
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UPoinc.ULabUniq

section Cong
variable {Y : Type} [AddCommGroup Y]

theorem cm_trans {N : ℕ} {x y z : Y} (h : CongMod N x y) (h' : CongMod N y z) : CongMod N x z := by
  obtain ⟨w, rfl⟩ := h
  obtain ⟨w', rfl⟩ := h'
  exact ⟨w' + w, by rw [smul_add]; abel⟩

theorem cm_symm {N : ℕ} {x y : Y} (h : CongMod N x y) : CongMod N y x := by
  obtain ⟨w, rfl⟩ := h
  exact ⟨-w, by rw [smul_neg]; abel⟩

theorem cm_map {Y' : Type} [AddCommGroup Y'] (f : Y →+ Y') {N : ℕ} {x y : Y} (h : CongMod N x y) :
    CongMod N (f x) (f y) := by
  obtain ⟨w, rfl⟩ := h
  exact ⟨f w, by rw [map_add (f := _), map_nsmul]⟩

theorem cm_of_mk {N : ℕ} {x y : Y}
    (h : (QuotientAddGroup.mk x : Y ⧸ (nsmulAddMonoidHom N : Y →+ Y).range) = QuotientAddGroup.mk y) :
    CongMod N x y := by
  rw [QuotientAddGroup.eq] at h
  obtain ⟨w, hw⟩ := h
  have hw' : N • w = -x + y := hw
  exact ⟨-w, by rw [smul_neg, hw']; abel⟩

theorem cm_mk {N : ℕ} {x y : Y} (h : CongMod N x y) :
    (QuotientAddGroup.mk x : Y ⧸ (nsmulAddMonoidHom N : Y →+ Y).range) = QuotientAddGroup.mk y := by
  rw [QuotientAddGroup.eq]
  obtain ⟨w, rfl⟩ := h
  exact ⟨-w, by change N • (-w) = -(y + N • w) + y; rw [smul_neg]; abel⟩

end Cong

theorem sc_pos {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
    {Xo : Moduli D l} {cf : Coeff l} {C : UCompact Xo cf} {X : USetup C} {p : ℕ} [Fact p.Prime] {z : X.M.Z}
    (c : UCTrait X p z) : 0 < c.sc := by
  set x := algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ with hx
  have h0 : x ≠ 0 := fun h =>
    c.T.irr.ne_zero ((map_eq_zero_iff _ (IsFractionRing.injective _ _)).1 h)
  have h1 : 0 < ‖c.ι x‖ := norm_pos_iff.2 ((map_ne_zero c.ι).2 h0)
  have h2 : ‖c.ι x‖ < 1 := by
    by_contra h
    have : ‖c.ι x⁻¹‖ ≤ 1 := by
      rw [map_inv₀, norm_inv]; exact inv_le_one_of_one_le₀ (not_lt.1 h)
    obtain ⟨v, hv⟩ := (c.int _).1 this
    refine c.T.irr.not_isUnit (IsUnit.of_mul_eq_one v (IsFractionRing.injective _ (FractionRing c.T.V) ?_))
    rw [map_mul, map_one, hv, ← hx, mul_inv_cancel₀ h0]
  exact neg_pos.2 (Real.log_neg h1 h2)


open MonObj in
theorem core : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (p : ℕ) [Fact p.Prime] (z : X.M.Z) (ct : UCTrait X p z) (yy yy' : X.S.Gam →+ ModN (X.S.r * X.S.N) ct.T.P.D.toPre.X), UIsLab X ct yy → UIsLab X ct yy' → ∃ κ : ct.T.P.D.toPre.X ≃+ ct.T.P.D.toPre.X, (∀ x, ct.T.be (κ x) (κ x) = ct.T.be x x) ∧ ∀ a ν, yy a = QuotientAddGroup.mk ν → yy' a = QuotientAddGroup.mk (κ ν) := by
  intro E _ _ _ H Dw _ l Xo cf C X p _ z ct yy yy' h1 h2
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', -, hS, -, -, hR, -, -, -, -, -, -, -, y₀, hy₀, u, lb, j, hq, hyy, -⟩ := h1
  obtain ⟨c₁, hc₁, R'', fg₁, frac₁, hth₁, hev₁, ρ'', -, hS₁, -, -, hR₁, -, -, -, -, -, -, -, y₁, hy₁, u', lb', j', hq',
    hyy', -⟩ := h2
  obtain ⟨P₀, a, a', ha, ha', hL, hL', hlab⟩ := GlobalTheory.T.unitaryRecharting_classicalTrait_same_geometric_fibre E H Dw l Xo cf C X p z ct c₀ hc R' fg frac hth hev ρ' hS hR
    y₀ hy₀ c₁ hc₁ R'' fg₁ frac₁ hth₁ hev₁ ρ'' hS₁ hR₁ y₁ hy₁ u u'
  obtain ⟨e, hψ, htor⟩ := GlobalTheory.T.exists_latticeIso_of_two_padicAlgCl_uniformisations _ _ ρ' ρ'' p y₀ y₁ u u' P₀ a a' ha ha' hL hL'
  haveI : CharZero (FractionRing u.V) :=
    (algebraMap (FractionRing u.V) (PadicAlgCl p)).charZero
  haveI : CharZero u.V := (algebraMap u.V (FractionRing u.V)).charZero
  haveI : CharZero (FractionRing u'.V) :=
    (algebraMap (FractionRing u'.V) (PadicAlgCl p)).charZero
  haveI : CharZero u'.V := (algebraMap u'.V (FractionRing u'.V)).charZero
  have hrN : 1 ≤ X.S.r * X.S.N := Nat.mul_pos X.S.r_pos (by have := X.S.N_ge; omega)
  have tors : ∀ m, 1 ≤ m → ∀ x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A, x ^ m = 1 →
      ∃ pk, QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x := fun m hm x hx => by
    obtain ⟨f, hf1, hf2, -⟩ := uTors_closed u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) m hm
    obtain ⟨pk, hpk⟩ := hf2 x hx
    exact ⟨pk, (hf1 pk x).2 hpk.symm⟩
  have tors' : ∀ m, 1 ≤ m → ∀ x : TFK (R := u'.V) (PadicAlgCl p) ⟶ u'.A.A, x ^ m = 1 →
      ∃ pk, QkToAkU u'.U.toUnifPre (PadicAlgCl p) m pk x := fun m hm x hx => by
    obtain ⟨f, hf1, hf2, -⟩ := uTors_closed u'.V u'.complete u'.A u'.G u'.D u'.U (PadicAlgCl p) m hm
    obtain ⟨pk, hpk⟩ := hf2 x hx
    exact ⟨pk, (hf1 pk x).2 hpk.symm⟩
  have hqe : ∀ χ, lb'.q (e χ) = lb.q χ := fun χ => by
    have h2 := (hψ χ _).1 (lb.q_eq χ)
    have h3 := GlobalTheory.ZH.RealCase.psiNorm_unique u' (e χ) h2 (lb'.q_eq (e χ))
    exact (neg_injective (Real.exp_injective h3)).symm
  have hlabe : ∀ b (χ : u.D.toPre.X) (χ' : u'.D.toPre.X), lb.yy b = QuotientAddGroup.mk χ →
      lb'.yy b = QuotientAddGroup.mk χ' → CongMod (X.S.r * X.S.N) χ' (e χ) := fun b χ χ' h h' => by
    obtain ⟨w, x, x', hw, hwa, hwa', hx, hx'⟩ := hlab b
    obtain ⟨pk, hpk⟩ := tors _ hrN x (GlobalTheory.LabelTorsion.pow_eq_one_of_over_label _ ρ' p y₀ u b x hx)
    obtain ⟨pk', hpk'⟩ := tors' _ hrN x' (GlobalTheory.LabelTorsion.pow_eq_one_of_over_label _ ρ'' p y₁ u' b x' hx')
    have e1 := lb.yy_eq b pk x hpk hx
    have e2 := lb'.yy_eq b pk' x' hpk' hx'
    have t := htor _ pk pk' x x' w hrN hpk hpk' hw hwa hwa'
    have c1 : CongMod (X.S.r * X.S.N) χ pk.y := cm_of_mk (h.symm.trans e1)
    have c2 : CongMod (X.S.r * X.S.N) χ' pk'.y := cm_of_mk (h'.symm.trans e2)
    exact cm_trans c2 (cm_trans t (cm_symm (cm_map e.toAddMonoidHom c1)))
  refine ⟨(j.symm.trans e).trans j', ?_, ?_⟩
  · intro v
    obtain ⟨χ, rfl⟩ := j.surjective v
    simp only [AddEquiv.trans_apply, AddEquiv.symm_apply_apply]
    have e1 := hq χ
    have e2 := hq' (e χ)
    rw [hqe] at e2
    have hs := sc_pos ct
    have h4 : ((ct.T.be (j' (e χ)) (j' (e χ)) : ℤ) : ℝ) = ((ct.T.be (j χ) (j χ) : ℤ) : ℝ) := by
      have := e2.symm.trans e1
      have h5 : ct.sc * (ct.T.be (j' (e χ)) (j' (e χ)) : ℝ) = ct.sc * (ct.T.be (j χ) (j χ) : ℝ) := by linarith
      exact mul_left_cancel₀ hs.ne' h5
    exact_mod_cast h4
  · intro b ν hν
    obtain ⟨χ, hχ⟩ := QuotientAddGroup.mk_surjective (lb.yy b)
    obtain ⟨χ', hχ'⟩ := QuotientAddGroup.mk_surjective (lb'.yy b)
    have e1 := hyy b χ hχ.symm
    have e2 := hyy' b χ' hχ'.symm
    rw [e2]
    apply cm_mk
    have c0 : CongMod (X.S.r * X.S.N) ν (j χ) := cm_of_mk (hν.symm.trans e1)
    have c3 := hlabe b χ χ' hχ.symm hχ'.symm
    have c4 : CongMod (X.S.r * X.S.N) (j.symm ν) χ := by simpa using cm_map j.symm.toAddMonoidHom c0
    exact cm_trans (cm_map j'.toAddMonoidHom c3) (cm_symm (cm_map j'.toAddMonoidHom (cm_map e.toAddMonoidHom c4)))

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (p : ℕ) [Fact p.Prime] (z : X.M.Z) (ct : UCTrait X p z) (yy yy' : X.S.Gam →+ ModN (X.S.r * X.S.N) ct.T.P.D.toPre.X), UIsLab X ct yy → UIsLab X ct yy' → ∃ κ : ct.T.P.D.toPre.X ≃+ ct.T.P.D.toPre.X, (∀ x, ct.T.be (κ x) (κ x) = ct.T.be x x) ∧ ∀ a μ, yy a = QuotientAddGroup.mk μ → yy' a = QuotientAddGroup.mk (κ μ) := core

end GlobalTheory.UPoinc.ULabUniq
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.PrimCocycle
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PullFrom

theorem exists_cart_of_pullDeg : ∀ {V V₁ V₂ : Type} [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [CommRing V₂] [IsDomain V₂] (D : DegPre V) (f₁ : V →+* V₁) (f₂ : V₁ →+* V₂) (B' : Over (Sp V₁)) [GrpObj B'] (β' : B'.left ⟶ D.P.A.left) (D' : DegPre V₂) (hD : IsPullDeg (f₂.comp f₁) D D'), IsGrpPullback B' D.P.A (spMap f₁) β' → ∃ Φ : D'.P.A.left ⟶ B'.left, IsGrpPullback D'.P.A B' (spMap f₂) Φ ∧ Φ ≫ β' = hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf (f₂.comp f₁)) ∧ ∀ (a : D'.X) (y : 𝟙_ (Over (Sp V₁)) ⟶ B'), y.left ≫ β' = spMap f₁ ≫ (D.c (hD.xe a)).left → (D'.c a).left ≫ Φ = spMap f₂ ≫ y.left := by
  intro V V₁ V₂ _ _ _ _ _ _ D f₁ f₂ B' _ β' D' hD gp'
  have gp := pull_grp hD
  have hsp : spMap f₂ ≫ spMap f₁ = spMap (f₂.comp f₁) := GlobalTheory.HalfBC.spMap_comp_spMap' f₁ f₂
  have w₀ : (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf (f₂.comp f₁))) ≫ D.P.A.hom =
      (D'.P.A.hom ≫ spMap f₂) ≫ spMap f₁ := by
    rw [gp.1.w, Category.assoc, hsp]
  refine ⟨gp'.1.lift _ _ w₀, ?_, gp'.1.lift_fst _ _ w₀, fun a y hy => ?_⟩
  · exact IsGrpPullback.cancel gp' (gp.congr hsp.symm (gp'.1.lift_fst _ _ w₀).symm) (gp'.1.lift_snd _ _ w₀)
  · apply gp'.1.hom_ext
    · rw [Category.assoc, gp'.1.lift_fst, Category.assoc, hy, ← Category.assoc (spMap f₂), hsp]
      exact hD.c_pr a
    · rw [Category.assoc, gp'.1.lift_snd, Category.assoc, Over.w y, ← Category.assoc, Over.w (D'.c a)]
      rfl

theorem degFrom_of_periodRel : ∀ (n : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegData V (maximalIdeal V)) (r : ℕ) (e₀ : (Fin r → ℤ) ≃+ D.toPre.X) (L : LowBase (zetaAway n) n) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (f₁ : V →+* V₁) (κ₁ : L.W →+* V₁) (e : (Fin L.T.r → ℤ) ≃+ (Fin r → ℤ)) (B' : Over (Sp V₁)) [GrpObj B'] (β' : B'.left ⟶ D.toPre.P.A.left) (β'' : B'.left ⟶ L.T.B.left) (β₂ : (G2 B').left ⟶ (G2 D.toPre.P.A).left) (β₂' : (G2 B').left ⟶ (G2 L.T.B).left), IsCN V → IsDiscreteValuationRing V → IsCN V₁ → IsDiscreteValuationRing V₁ → Function.Injective f₁ → f₁.Finite → IsLocalHom f₁ → IsLocalHom κ₁ → IsGrpPullback B' D.toPre.P.A (spMap f₁) β' → IsGrpPullback B' L.T.B (spMap κ₁) β'' → IsSquare β' β₂ → IsSquare β'' β₂' → ∀ (x : (Fin L.T.r → ℤ) → (𝟙_ (Over (Sp V₁)) ⟶ B')), (∀ a, (x a).left ≫ β' = spMap f₁ ≫ (D.toPre.c (e₀ (e a))).left ∧ (x a).left ≫ β'' = spMap κ₁ ≫ (L.T.c₀ ((n : ℤ) • a)).left) → ∀ (w₁ : LB.Iso ((abelian₂ D.toPre.P.A D.toPre.P.L).pull β₂) ((abelian₂ L.T.B L.T.M.L).pull β₂')) (q : (Fin L.T.r → ℤ) → (Fin L.T.r → ℤ) → (FractionRing V₁)ˣ), w₁.IsGen → PeriodRel D.toPre L.T f₁ κ₁ w₁ (e.trans e₀) x n q → ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂] (f₂ : V₁ →+* V₂) (fK : FractionRing V₁ →+* FractionRing V₂) {I : Type} [Fintype I] (s : I → V₂) (ε : I → LinearMap.BilinForm ℤ (Fin L.T.r → ℤ)), IsCN V₂ → Function.Injective f₂ → f₂.Finite → IsLocalHom f₂ → (∀ a, fK (algebraMap V₁ _ a) = algebraMap V₂ _ (f₂ a)) → (∀ a b, fK (q a b : FractionRing V₁) = ∏ k, algebraMap V₂ _ (s k) ^ ((n : ℤ) * ε k a b)) → ∀ (D' : DegData V₂ (maximalIdeal V₂)) (hD : IsPullDeg (f₂.comp f₁) D.toPre D'.toPre), DegFrom L.T (f₂.comp κ₁) s ε n D'.toPre (hD.xe.trans (e₀.symm.trans e.symm)) := by
  intro n V _ _ _ D r e₀ L V₁ _ _ _ f₁ κ₁ e B' _ β' β'' β₂ β₂' hV hVd hV₁ hV₁d hf₁i hf₁f hf₁l hκ₁l gp' gp'' sq' sq'' x hx w₁ q hw₁ hPR V₂ _ _ _ f₂ fK I _ s ε hV₂ hf₂i hf₂f hf₂l hfK hq D' hD
  obtain ⟨Φ, gΦ, hΦ, hc₀⟩ := exists_cart_of_pullDeg D.toPre f₁ f₂ B' β' D'.toPre hD gp'
  have hc : ∀ a, (D'.toPre.c a).left ≫ Φ = spMap f₂ ≫ (x (hD.xe.trans (e₀.symm.trans e.symm) a)).left := fun a =>
    hc₀ a _ (by
      have := (hx (hD.xe.trans (e₀.symm.trans e.symm) a)).1
      simpa using this)
  have hΛD : (abelian₂ D.toPre.P.A D.toPre.P.L).IsLB := DVR.linComb_isLB _ D.toPre.P.isLB _ _
  obtain ⟨w, hw, hval⟩ := GlobalTheory.T.mumfordBundleIso_comp_group_pullback_iso D.toPre.P.A B' D'.toPre.P.A L.T.B (spMap f₁) (spMap f₂) β' Φ (GlobalTheory.PsiEvenPull.proj hD) β₂ β₂'
    D.toPre.P.L D'.toPre.P.L L.T.M.L gp' gΦ sq' hΦ D.toPre.P.isLB D'.toPre.P.isLB L.T.M.isLB hD.w w₁ hD.w_gen hw₁
  have hsp : spMap f₂ ≫ spMap κ₁ = spMap (f₂.comp κ₁) := GlobalTheory.HalfBC.spMap_comp_spMap' κ₁ f₂
  refine ⟨Wit.ofDeg D'.toPre D'.tau_bimult, AddEquiv.refl _, Wit.refines_ofDeg _ _, Φ ≫ β'', GlobalTheory.HalfBC.sqOf gΦ ≫ β₂', w,
    (IsGrpPullback.comp gΦ gp'').congr hsp rfl, ⟨?_, ?_⟩, hw, fun a => ?_, fun a b => ?_⟩
  · have e₁ : GlobalTheory.HalfBC.sqOf gΦ ≫ (fst B' B').left = (fst D'.toPre.P.A D'.toPre.P.A).left ≫ Φ :=
      congrArg (fun z => z.left) (lift_fst (pushPt gΦ.1.w (fst D'.toPre.P.A D'.toPre.P.A)) (pushPt gΦ.1.w (snd D'.toPre.P.A D'.toPre.P.A)))
    show (GlobalTheory.HalfBC.sqOf gΦ ≫ β₂') ≫ (fst L.T.B L.T.B).left = (fst D'.toPre.P.A D'.toPre.P.A).left ≫ Φ ≫ β''
    rw [Category.assoc, sq''.1, ← Category.assoc, e₁, Category.assoc]
  · have e₂ : GlobalTheory.HalfBC.sqOf gΦ ≫ (snd B' B').left = (snd D'.toPre.P.A D'.toPre.P.A).left ≫ Φ :=
      congrArg (fun z => z.left) (lift_snd (pushPt gΦ.1.w (fst D'.toPre.P.A D'.toPre.P.A)) (pushPt gΦ.1.w (snd D'.toPre.P.A D'.toPre.P.A)))
    show (GlobalTheory.HalfBC.sqOf gΦ ≫ β₂') ≫ (snd L.T.B L.T.B).left = (snd D'.toPre.P.A D'.toPre.P.A).left ≫ Φ ≫ β''
    rw [Category.assoc, sq''.2, ← Category.assoc, e₂, Category.assoc]
  · refine (congrArg (· ≫ β'') (hc a)).trans ?_
    rw [Category.assoc, (hx _).2, ← Category.assoc, hsp]
    rfl
  · obtain ⟨k, hk, hk'⟩ := GlobalTheory.T.period_relation_pullback_monomial_constants n V D.toPre r e₀ L.T V₁ f₁ κ₁ e B' β₂ β₂' x w₁ q hf₁i hPR V₂ f₂ fK s ε hfK hq D'.toPre hD Φ gΦ hc w hval a b
    refine ⟨k, hk, fun z J J' hJ hJ' => ?_⟩
    refine ((Wit.exists_tau D'.toPre a b).choose_spec.2 _ _ z J' hJ').trans ?_
    exact hk' z J J' hJ hJ'

end GlobalTheory.PullFrom
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem mem_valuationSubring_of_image : ∀ (F : Type) [Field F] (V : ValuationSubring F) (T : Type) [CommRing T] [IsLocalRing T] (g : V →+* T), IsLocalHom g → ∀ (W' : Type) [CommRing W'] [IsDomain W'] [IsLocalRing W'] (io : T →+* W'), Function.Injective io → io.Finite → ∀ (Ω : Type) [Field Ω] (iF : F →+* Ω) (e : W' →+* Ω), Function.Injective e → (∀ v : V, iF v = e (io (g v))) → ∀ (y : F) (w : W'), iF y = e w → y ∈ V := by
  intro F _ V T _ _ g hg W' _ _ _ io hioi hiof Ω _ iF e he hi y w hy
  haveI : IsLocalHom io := RingHom.IsIntegral.isLocalHom hiof.to_isIntegral hioi
  by_contra hyV
  have hy0 : y ≠ 0 := fun h => hyV (h ▸ V.zero_mem)
  have hinv : y⁻¹ ∈ V := (V.mem_or_inv_mem y).resolve_left hyV
  let u : V := ⟨y⁻¹, hinv⟩
  have hu : ¬ IsUnit u := by
    intro hu
    obtain ⟨v, hv⟩ := hu.exists_right_inv
    have h' : y⁻¹ * (v : F) = 1 := by simpa [u] using congrArg Subtype.val hv
    have hv' : (v : F) = y := by
      calc (v : F) = y * (y⁻¹ * v) := by rw [← _root_.mul_assoc, mul_inv_cancel₀ hy0, _root_.one_mul]
        _ = y := by rw [h', _root_.mul_one]
    exact hyV (hv' ▸ v.2)
  have hprod : io (g u) * w = 1 := by
    apply he
    rw [map_mul, map_one, ← hi u, ← hy, ← map_mul]
    simp [u, inv_mul_cancel₀ hy0]
  exact hu ((isUnit_map_iff g u).1 ((isUnit_map_iff io (g u)).1 (IsUnit.of_mul_eq_one _ hprod)))

theorem chartVal_mem_of_dominates : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R] (M : Modif R) (G : Over M.S), Smooth G.hom → QuasiCompact G.hom → GeometricallyIrreducible G.hom → ∀ (L : LB G.left), L.IsLB → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), IsPullback α t G.hom M.gp → ∀ (k : ℕ) (s : SecK L α k), TraitReg M G L s → ∀ (j : L.ι) (U : M.S.Opens) (W : G.left.Opens) (hW : W ≤ L.U j), W ≤ G.hom ⁻¹ᵁ U → IsAffineOpen W → IsAffineOpen U → ∀ (x : G.left) (hx : x ∈ W), M.π (G.hom x) = closedPoint R → ∀ (F : Type) [Field F] (β : Γ(Y, α ⁻¹ᵁ W) →+* F) (V : ValuationSubring F), IsDiscreteValuationRing V → (∀ c, β ((α.app W).hom c) ∈ V) → (∀ c, (G.left.residue x).hom ((G.left.presheaf.germ W x hx).hom c) = 0 → β ((α.app W).hom c) ∈ V.nonunits) → β (chartVal L α s j W hW) ∈ V := by
  intro R _ _ _ _ _ M G hsm hqc hgi L hL Y α t hpb k s hs j U W hW hWU hWa hUa x hx hcl F _ β V hV h1 h2
  obtain ⟨T, _, _, _, lam, g, φ, hT, hgi', hgl, hgl', hφi, hφl, hξ⟩ :=
    GlobalTheory.T.completed_dominating_dvr_closedFibre_point_is_trait R M G Y α t hpb.w W hWa x hx hcl F β V hV h1 h2
  obtain ⟨W', _, _, _, io, σ, hW', hioi, hiof, hag⟩ := hs T hT φ (Spec.map (CommRingCat.ofHom lam) ≫ hWa.fromSpec ≫ G.hom) hφi hφl hξ
  let e : W' →+* FractionRing W' := algebraMap W' (FractionRing W')
  have he : Function.Injective e := IsFractionRing.injective W' (FractionRing W')
  have hgg : Function.Injective ((e.comp io).comp g) := he.comp (hioi.comp hgi')
  let iF : F →+* FractionRing W' := IsFractionRing.lift hgg
  have hi : ∀ v : V, iF v = e (io (g v)) := fun v => IsFractionRing.lift_algebraMap hgg v
  have hαW := GlobalTheory.Mum.isAffineOpen_preimage_genericBaseChange R M G Y α t hpb W hWa
  obtain ⟨w, hw⟩ := GlobalTheory.T.chartValue_mem_range_of_agree_traitExtension G.left M.S Y G.hom L hL α k s j W hW hWa hαW T lam W' io σ hag (FractionRing W') (iF.comp β) e
    (fun c => (hi ⟨_, h1 c⟩).trans (by rw [hgl' c]))
  have hw' : iF (β (chartVal L α s j W hW)) = e w := hw
  exact mem_valuationSubring_of_image F V T g hgl W' io hioi hiof (FractionRing W') iF e he hi (β (chartVal L α s j W hW)) w hw'

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.TensRos
open GlobalTheory.TensBal GlobalTheory.TensAct
variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

theorem vecHom_add (T : Tens D D' W) (u v : Vec r) : vecHom T (u + v) = vecHom T u * vecHom T v := by
  simp only [vecHom, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]
  exact mul_mul_mul_comm _ _ _ _

theorem vecHom_zero (T : Tens D D' W) : vecHom T 0 = 1 := by
  simp [vecHom]

theorem prod_single {G : Type} [CommGroup G] (f : Fin r → G) (i : Fin r) :
    ∏ k, f k ^ (Pi.single i (1 : ℤ) : Fin r → ℤ) k = f i := by
  rw [Fintype.prod_eq_single i (fun k hk => by rw [Pi.single_eq_of_ne hk, zpow_zero])]
  rw [Pi.single_eq_same, zpow_one]

theorem vecHom_xv (T : Tens D D' W) (i : Fin r) : vecHom T (xv i) = fst D'.P.A D'.P.A ≫ T.pr i := by
  simp only [vecHom, xv, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zpow_zero, Finset.prod_const_one, _root_.mul_one]
  exact prod_single _ i

theorem vecHom_zv (T : Tens D D' W) (i : Fin r) : vecHom T (zv i) = snd D'.P.A D'.P.A ≫ T.pr i := by
  simp only [vecHom, zv, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zpow_zero, Finset.prod_const_one, _root_.one_mul]
  exact prod_single _ i

theorem vecHom_axv (T : Tens D D' W) (A : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) :
    vecHom T (axv A i) = fst D'.P.A D'.P.A ≫ matAct T A ≫ T.pr i := by
  simp only [vecHom, axv, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zpow_zero, Finset.prod_const_one, _root_.mul_one]
  rw [matAct_pr, GlobalTheory.MatrixAction.comp_finsetProd]
  exact Finset.prod_congr rfl fun k _ => (GrpObj.comp_zpow _ _ _).symm

theorem vecHom_azv (T : Tens D D' W) (A : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) :
    vecHom T (azv A i) = snd D'.P.A D'.P.A ≫ matAct T A ≫ T.pr i := by
  simp only [vecHom, azv, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zpow_zero, Finset.prod_const_one, _root_.one_mul]
  rw [matAct_pr, GlobalTheory.MatrixAction.comp_finsetProd]
  exact Finset.prod_congr rfl fun k _ => (GrpObj.comp_zpow _ _ _).symm

theorem ros_pr (T : Tens D D' W) (A A' : Matrix (Fin r) (Fin r) ℤ) (a : Fin 6) :
    ∃ q : D'.P.A ⊗ D'.P.A ⟶ D'.P.A, rosatiφ D'.P.A (matAct T A) (matAct T A') a = q.left ∧
      ∀ k, q ≫ T.pr k = vecHom T (rosVec A A' a k) := by
  have hp := T.pr_hom
  fin_cases a
  · refine ⟨(fst D'.P.A D'.P.A ≫ matAct T A) * snd D'.P.A D'.P.A, rfl, fun k => ?_⟩
    show _ = vecHom T (axv A k + zv k)
    rw [MonObj.mul_comp, Category.assoc, vecHom_add, vecHom_axv, vecHom_zv]
  · refine ⟨fst D'.P.A D'.P.A ≫ matAct T A, rfl, fun k => ?_⟩
    show _ = vecHom T (axv A k)
    rw [vecHom_axv, Category.assoc]
  · refine ⟨snd D'.P.A D'.P.A, rfl, fun k => ?_⟩
    show _ = vecHom T (zv k)
    rw [vecHom_zv]
  · refine ⟨fst D'.P.A D'.P.A * (snd D'.P.A D'.P.A ≫ matAct T A'), rfl, fun k => ?_⟩
    show _ = vecHom T (xv k + azv A' k)
    rw [MonObj.mul_comp, Category.assoc, vecHom_add, vecHom_xv, vecHom_azv]
  · refine ⟨fst D'.P.A D'.P.A, rfl, fun k => ?_⟩
    show _ = vecHom T (xv k)
    rw [vecHom_xv]
  · refine ⟨snd D'.P.A D'.P.A ≫ matAct T A', rfl, fun k => ?_⟩
    show _ = vecHom T (azv A' k)
    rw [vecHom_azv, Category.assoc]

def lamV (u v : Vec r) : Fin 4 → Vec r := ![u + v, u, v, 0]

theorem ros_lam (T : Tens D D' W) (A A' : Matrix (Fin r) (Fin r) ℤ) (a : Fin 6) (i j : Fin r) (s : Fin 4) :
    rosatiφ D'.P.A (matAct T A) (matAct T A') a ≫ GlobalTheory.PolDeg.lamPts (T.pr i) (T.pr j) s =
      (vecHom T (lamV (rosVec A A' a i) (rosVec A A' a j) s)).left := by
  obtain ⟨q, hq, hk⟩ := ros_pr T A A' a
  rw [hq]
  fin_cases s
  · show q.left ≫ (T.pr i * T.pr j).left = _
    rw [← Over.comp_left, MonObj.comp_mul, hk, hk]
    show _ = (vecHom T (rosVec A A' a i + rosVec A A' a j)).left
    rw [vecHom_add]
  · show q.left ≫ (T.pr i).left = _
    rw [← Over.comp_left, hk]; rfl
  · show q.left ≫ (T.pr j).left = _
    rw [← Over.comp_left, hk]; rfl
  · show q.left ≫ (1 : D'.P.A ⟶ D.P.A).left = _
    rw [← Over.comp_left, MonObj.comp_one]
    show _ = (vecHom T 0).left
    rw [vecHom_zero]
theorem formEq_sig (T : Tens D D' W) (A A' : Matrix (Fin r) (Fin r) ℤ) :
    FormEq (fun p : Fin 6 × ((Fin r × Fin r) × Fin 4) =>
        rosatiφ D'.P.A (matAct T A) (matAct T A') p.1 ≫ tensφ T.pr p.2)
      (fun p => rosatiε p.1 * tensε W p.2)
      (fun v : (sig W A A').support => (vecHom T v.1).left) (fun v => sig W A A' v.1) := by
  intro U _ h
  let H : Vec r → Additive U := fun v => Additive.ofMul (h (vecHom T v).left)
  let F : (Vec r →₀ ℤ) →+ Additive U := Finsupp.liftAddHom fun v => zmultiplesHom (Additive U) (H v)
  have hF1 : ∀ x, F (Finsupp.single x 1) = H x := fun x => by
    simp only [F, Finsupp.liftAddHom_apply_single, zmultiplesHom_apply, one_zsmul]
  have hlam : ∀ u v, F (lam u v) = ∑ s : Fin 4, Oε s • H (lamV u v s) := fun u v => by
    simp only [lam, map_add (f := _), map_sub, hF1, Fin.sum_univ_four]
    simp [Oε, lamV]
    abel
  have hR : Additive.ofMul (∏ v : (sig W A A').support, h (vecHom T v.1).left ^ sig W A A' v.1) =
      F (sig W A A') := by
    rw [ofMul_prod]
    simp only [ofMul_zpow]
    rw [Finset.sum_coe_sort (sig W A A').support (fun v => sig W A A' v • H v)]
    simp only [F, Finsupp.liftAddHom_apply, zmultiplesHom_apply]
    rfl
  apply Additive.ofMul.injective
  rw [hR]

  simp only [ofMul_prod, ofMul_zpow, sig, map_sum, map_zsmul, hlam]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  show (rosatiε a * (W i j * Oε s)) • Additive.ofMul (h (rosatiφ D'.P.A (matAct T A) (matAct T A') a ≫
    GlobalTheory.PolDeg.lamPts (T.pr i) (T.pr j) s)) = _
  rw [ros_lam, ← _root_.mul_assoc, mul_smul]

theorem ros_sig : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W) (A A' : Matrix (Fin r) (Fin r) ℤ) (u' : LB.Gen (LB.LinComb D'.P.L (rosatiφ D'.P.A (GlobalTheory.TensAct.matAct T A) (GlobalTheory.TensAct.matAct T A')) rosatiε)), u'.IsGen → LB.Gen.Corr D'.P.L _ _ _ _ (LB.pullGen D'.P.L _ _ u' (zero2 D'.P.A)) (LB.oneGen D'.P.L) → ∀ (Ξ : LB.Gen (LB.LinComb D.P.L (fun v : (GlobalTheory.TensBal.sig W A A').support => (GlobalTheory.TensBal.vecHom T v.1).left) (fun v => GlobalTheory.TensBal.sig W A A' v.1))), Ξ.IsGen → (∀ (z : (𝟙_ (Over (Spec (CommRingCat.of R)))).left) (J : ((𝟙_ (Over (Spec (CommRingCat.of R)))).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → val Ξ (zero2 D'.P.A) z J = 1) → ∀ (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι) (J' : ((TK R).left ⟶ D'.P.A.left) → D'.P.L.ι), Good D.P.L z J → Good D'.P.L z J' → ∀ y y' : D'.X, (∏ a, GlobalTheory.TensBal.isoV T.w z J J' (D'.pt2 y y' ≫ rosatiφ D'.P.A (GlobalTheory.TensAct.matAct T A) (GlobalTheory.TensAct.matAct T A') a) ^ rosatiε a) * val u' (D'.pt2 y y') z J' = val Ξ (D'.pt2 y y') z J := by
  intro R _ _ D D' r W T A A' u' hu' hn' Ξ hΞ hΞ0 z J J' hJ hJ' y y'
  have hG : GlobalFnsSt := GlobalTheory.SemiRigid.globalFns
  haveI := matAct_hom T A
  haveI := matAct_hom T A'
  have sj : Function.Surjective ((snd D'.P.A D'.P.A).left ≫ D'.P.A.hom).appTop.hom :=
    surj_comp (surj_snd hG D'.P.isAb _) (hG _ _ D'.P.isAb).2
  have he : zero2 D'.P.A ≫ (snd D'.P.A D'.P.A).left ≫ D'.P.A.hom = 𝟙 _ := by
    rw [Over.w]; exact Over.w (lift η[D'.P.A] η[D'.P.A])
  refine GlobalTheory.T.transported_generator_unique_globalFunctions_base D.P.isLB D'.P.isLB T.w T.w_gen (formEq_sig T A A') hu' hΞ _ (zero2 D'.P.A) he sj
    (fun s I I' hI hI' => ?_) _ (D'.pt2 y y') z J J' hJ hJ'
  have o : (η[D'.P.A] : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D'.P.A) = 1 := by simp [Hom.one_def]
  have p := prod_ros (matAct T A) (matAct T A') η[D'.P.A] η[D'.P.A] (fun q => isoV T.w s I I' q)
  rw [IsMonHom.one_hom, IsMonHom.one_hom, show η[D'.P.A] * η[D'.P.A] = η[D'.P.A] by rw [o, _root_.mul_one]] at p
  have v' := val_corr hI' hn' (𝟙 _)
  rw [val_pull hI', Category.id_comp, val_one] at v'
  rw [hΞ0 s I hI]
  refine (congrArg₂ (· * ·) p v').trans (by simp)

end GlobalTheory.TensRos
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

theorem _root_.GlobalTheory.T.descendsAbelianPart_of_isPullDeg : ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] (ρ : V →+* V₁) (Q : DegPre V) (D : DegPre V₁), IsPullDeg ρ Q D → D.P.g = Q.P.g ∧ ∀ (K : Type) [Field K] (ev : V₁ →+* K) (k₀ : Subfield K), DescAt D ev k₀ → DescAt Q (ev.comp ρ) k₀ := by
  first | exact @GlobalTheory.USep.descAt_of_isPullDeg | exact GlobalTheory.USep.descAt_of_isPullDeg | (intros; apply GlobalTheory.USep.descAt_of_isPullDeg <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.FibLat
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.unitaryEndomorphisms_torsion_extend_semiAbelian : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (wi : UWit X) (Y : RatModel X.o₁ X.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X.S.J) (FinalForm : ZHOut X.ρ Y U₀ EE) (q : Y.Z ⟶ X.M.Z), X.S.Over₀ Y U₀ → X.S.IsEE Y U₀ EE → Y.pt ≫ q = X.M.pt → ∀ z : X.M.Z, X.S.TT X.M z ≤ X.S.HH X.M z → ∃ (f : 𝓞 E → (FinalForm.G ⟶ FinalForm.G)) (gγ : X.S.TT X.M z → (Over.mk Y.pt ⟶ FinalForm.G)), GlobalTheory.UPoinc.GFib.IsEndoExt X wi FinalForm f ∧ GlobalTheory.UPoinc.GFib.IsTorsExt X wi FinalForm q z gγ := by
  first | exact @GlobalTheory.UPoinc.GFib.endo_torsion_ext | exact GlobalTheory.UPoinc.GFib.endo_torsion_ext | (intros; apply GlobalTheory.UPoinc.GFib.endo_torsion_ext <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.FibLat
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.characterLattice_unitaryClassicalTrait_centre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (wi : UWit X) (Y : RatModel X.o₁ X.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X.S.J) (FinalForm : ZHOut X.ρ Y U₀ EE) (q : Y.Z ⟶ X.M.Z), X.S.Over₀ Y U₀ → X.S.IsEE Y U₀ EE → IsProper q → Y.pt ≫ q = X.M.pt → ∀ (p : ℕ) [Fact p.Prime] (z : X.M.Z) (f : 𝓞 E → (FinalForm.G ⟶ FinalForm.G)) (gγ : X.S.TT X.M z → (Over.mk Y.pt ⟶ FinalForm.G)), GlobalTheory.UPoinc.GFib.IsEndoExt X wi FinalForm f → GlobalTheory.UPoinc.GFib.IsTorsExt X wi FinalForm q z gγ → ∀ ζ : X.o₁ˣ, IsPrimitiveRoot (ζ : X.o₁) (X.S.r * X.S.N) → ∃ (s : ZMod (X.S.r * X.S.N)) (σ : 𝓞 E → 𝓞 E), IsUnit s ∧ Function.Surjective σ ∧ ∀ (ct : UCTrait X p z) (y : Sp (OO p) ⟶ Y.Z), y ≫ q = ct.y → ∀ (yy : X.S.Gam →+ ModN (X.S.r * X.S.N) ct.T.P.D.toPre.X), UIsLabW X wi ct yy → ∃ c : X.S.TT X.M z → ct.T.P.D.toPre.X →+ ZMod (X.S.r * X.S.N), LatAt f gγ ζ (X.S.r * X.S.N) (fun a => DistribSMul.toAddMonoidHom ct.T.P.D.toPre.X (σ a)) c (y (cPt p)) ∧ ∀ (a : X.S.Gam) (v : ct.T.P.D.toPre.X) (t : X.S.TT X.M z), yy a = QuotientAddGroup.mk v → c t v = s * eStd X.S.g _ (t : X.S.Gam) a := by
  first | exact @GlobalTheory.UPoinc.GFibCentre.latAt_centre | exact GlobalTheory.UPoinc.GFibCentre.latAt_centre | (intros; apply GlobalTheory.UPoinc.GFibCentre.latAt_centre <;> assumption)
end
