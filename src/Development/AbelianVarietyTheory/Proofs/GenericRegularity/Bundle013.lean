module

import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CombinedBoundAtTrivialValuationsOfCharts
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.SCharts
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle017
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle010
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Bundle001
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GlobalBasisAlgebra
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle039
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle012
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LiePush
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

noncomputable section

namespace GlobalTheory.Reg.ChartInt

open IsLocalRing Formalism.L2.PjFree

section Values
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

theorem vV_nonneg (w : V) (hw : w ≠ 0) : 0 ≤ vV V (algebraMap V (FractionRing V) w) := by
  have hw' : algebraMap V (FractionRing V) w ≠ 0 := by
    intro h; apply hw; exact IsFractionRing.injective V (FractionRing V) (by rw [h, map_zero])
  have h1 := IsDedekindDomain.HeightOneSpectrum.valuation_le_one
    (IsDiscreteValuationRing.maximalIdeal V) (K := FractionRing V) w
  have h0 : valV V (algebraMap V (FractionRing V) w) ≠ 0 := valV_ne_zero hw'
  have h2 : WithZero.log (valV V (algebraMap V (FractionRing V) w)) ≤ WithZero.log (1 : WithZero (Multiplicative ℤ)) :=
    (WithZero.log_le_log h0 one_ne_zero).2 h1
  rw [WithZero.log_one] at h2
  unfold vV
  omega

theorem vV_unit (u : V) (hu : u ∉ maximalIdeal V) : vV V (algebraMap V (FractionRing V) u) = 0 := by
  have h1 : (IsDiscreteValuationRing.maximalIdeal V).valuation (FractionRing V) (algebraMap V _ u) = 1 :=
    (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem (K := FractionRing V)
      (IsDiscreteValuationRing.maximalIdeal V)).2 hu
  unfold vV valV
  rw [h1, WithZero.log_one, neg_zero]

theorem mem_of_vV_nonneg (y : FractionRing V) (hy : y ≠ 0) (h : 0 ≤ vV V y) :
    ∃ w : V, algebraMap V (FractionRing V) w = y := by
  have h0 : valV V y ≠ 0 := valV_ne_zero hy
  have hle : valV V y ≤ 1 := by
    rw [← WithZero.log_le_log h0 one_ne_zero, WithZero.log_one]
    unfold vV at h
    omega
  obtain ⟨w, hw⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one (R := V)
    (K := FractionRing V) y (fun v => by
      have hv : v = IsDiscreteValuationRing.maximalIdeal V := by
        have hm : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
        ext1
        exact IsLocalRing.eq_maximalIdeal hm
      rw [hv]
      exact hle)
  exact ⟨w, hw⟩

theorem nval_nonneg (e : ℕ) (w : V) : 0 ≤ nval V e (algebraMap V (FractionRing V) w) := by
  by_cases hw : w = 0
  · rw [hw, map_zero, nval_zero]
    exact le_top
  · have hw' : algebraMap V (FractionRing V) w ≠ 0 := by
      intro h; apply hw; exact IsFractionRing.injective V (FractionRing V) (by rw [h, map_zero])
    rw [nval_of_ne hw']
    exact EReal.coe_nonneg.2 (div_nonneg (by exact_mod_cast vV_nonneg w hw) (Nat.cast_nonneg e))

theorem nval_unit (e : ℕ) (u : V) (hu : u ∉ maximalIdeal V) : nval V e (algebraMap V (FractionRing V) u) = 0 := by
  have hu0 : u ≠ 0 := fun h => hu (h ▸ (maximalIdeal V).zero_mem)
  have hu' : algebraMap V (FractionRing V) u ≠ 0 := by
    intro h; apply hu0; exact IsFractionRing.injective V (FractionRing V) (by rw [h, map_zero])
  rw [nval_of_ne hu', vV_unit u hu]
  simp

theorem ne_zero_map {x : V} (hx : x ≠ 0) : algebraMap V (FractionRing V) x ≠ 0 := by
  intro h; apply hx; exact IsFractionRing.injective V (FractionRing V) (by rw [h, map_zero])

variable {A : Type} [CommRing A] [IsDomain A]

theorem chval_eq (φ : A →+* V) (e : ℕ) (f : FractionRing A) (r : EReal) (h : ChV φ e f r) (a b : A)
    (hab : f * algebraMap A (FractionRing A) b = algebraMap A (FractionRing A) a) (hb : φ b ≠ 0) :
    r = nval V e (algebraMap V (FractionRing V) (φ a)) - nval V e (algebraMap V (FractionRing V) (φ b)) := by
  apply GlobalTheory.Reg.TrivBound.chval_eq <;> assumption

theorem chval_div (φ : A →+* V) (e : ℕ) (he : 0 < e) (f : FractionRing A) (r : EReal) (h : ChV φ e f r)
    (hr : 0 ≤ r) (a b : A) (hab : f * algebraMap A (FractionRing A) b = algebraMap A (FractionRing A) a)
    (hb : φ b ≠ 0) : ∃ w : V, φ a = w * φ b := by
  apply GlobalTheory.Reg.TrivBound.chval_div <;> assumption

theorem chval_nonneg (φ : A →+* V) (e : ℕ) (f : FractionRing A) (r : EReal) (h : ChV φ e f r) (a s : A)
    (hfs : f * algebraMap A (FractionRing A) s = algebraMap A (FractionRing A) a) (hs : φ s ∉ maximalIdeal V) :
    0 ≤ r := by
  have hs0 : φ s ≠ 0 := fun h0 => hs (h0 ▸ (maximalIdeal V).zero_mem)
  rw [chval_eq φ e f r h a s hfs hs0, nval_unit e _ hs, sub_zero]
  exact nval_nonneg e _

end Values

section Charts
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem transfer {la : HeightOneSpectrum (𝓞 c.F)}
    (S : SCharts Xo c la) (j : S.J) (g : FractionRing (S.A j)) (x : S.A j) (hx0 : x ≠ 0)
    (hpts : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra S.O V]
      [Module.Finite S.O V] (φ : S.A j →ₐ[S.O] V), φ x ≠ 0 →
        ∃ (e : ℕ) (r : EReal), 0 < e ∧ ChV φ.toRingHom e g r ∧ 0 ≤ r)
    (qq : Ideal (S.A j)) [qq.IsPrime]
    (hqq : qq ⊔ Ideal.map (algebraMap S.O (S.A j)) (maximalIdeal S.O) ≠ ⊤) :
    ∃ a s : S.A j, s ∉ qq ∧ g * algebraMap (S.A j) (FractionRing (S.A j)) s =
      algebraMap (S.A j) (FractionRing (S.A j)) a := by
  refine Formalism.L2.Pj.RegC.key_centre g x hx0 (fun V _ _ _ _ _ φ a b hab hb hφx => ?_) qq hqq
  obtain ⟨e, r, he, hr, hr0⟩ := hpts V φ hφx
  exact chval_div φ.toRingHom e he g r hr hr0 a b hab hb

theorem nonneg_at {la : HeightOneSpectrum (𝓞 c.F)}
    (S : SCharts Xo c la) {a n} {F : Rul Xo c} (hF : F ∈ sec Xo c a n)
    (h0 : ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v F) (j : S.J) (x : S.A j) (hxE : x ∈ S.Eb j)
    (hx0 : x ≠ 0) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra S.O V]
    (φ : S.A j →ₐ[S.O] V) (e : ℕ) (rr : EReal) (hch : ChV φ.toRingHom e (S.ch j F) rr)
    (hqq : (maximalIdeal V).comap φ.toRingHom ⊔ Ideal.map (algebraMap S.O (S.A j)) (maximalIdeal S.O) ≠ ⊤) :
    0 ≤ rr := by
  obtain ⟨a', s', hs', hfs'⟩ := transfer S j (S.ch j F) x hx0 (fun V _ _ _ _ _ φ hφx => by
    obtain ⟨ioV, e', hov, -, v, hv, hChV⟩ := S.pts j V φ ⟨x, hxE, hφx⟩
    exact ⟨e', v F, hov.1, hChV a n F hF, h0 v hv⟩) ((maximalIdeal V).comap φ.toRingHom) hqq
  exact chval_nonneg φ.toRingHom e (S.ch j F) rr hch a' s' hfs' hs'

theorem nonneg_at_all_points {la : HeightOneSpectrum (𝓞 c.F)}
    (S : SCharts Xo c la) {a n} {F : Rul Xo c} (hF : F ∈ sec Xo c a n)
    (h0 : ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v F) : ∀ v ∈ valSet Xo c (trivialClassCondition Xo c) la, 0 ≤ v F := by
  intro v hv
  obtain ⟨j, V, _, _, _, _, φ, ioV, e, hov, ⟨x, hxE, hφx⟩, -, hmap, hChV⟩ := S.cover v hv
  have hx0 : x ≠ 0 := fun h => hφx (by rw [h, map_zero])
  refine nonneg_at S hF h0 j x hxE hx0 V φ e (v F) (hChV a n F hF) ?_
  rw [sup_eq_left.2 hmap]
  exact (Ideal.IsPrime.ne_top inferInstance)

theorem nonneg_at_trivial {la : HeightOneSpectrum (𝓞 c.F)}
    (S : SCharts Xo c la) (hQ : S.CovQ) {a n} {F : Rul Xo c} (hF : F ∈ sec Xo c a n)
    (h0 : ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v F) : ∀ q ∈ trivSet Xo c, 0 ≤ q F := by
  intro q hq
  obtain ⟨j, V, _, _, _, _, φ, hcen, -, ⟨x, hxE, hφx⟩, hChV⟩ := hQ q hq
  have hx0 : x ≠ 0 := fun h => hφx (by rw [h, map_zero])
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S.O
  refine nonneg_at S hF h0 j x hxE hx0 V φ 1 (q F) (hChV a n F hF) ?_
  have hm : maximalIdeal S.O = Ideal.span {ϖ} := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  rw [hm, Ideal.map_span, Set.image_singleton, sup_comm]
  exact hcen ϖ hϖ

theorem qpt_mem_trivSet (q : QPt Xo c) : (fun f => ordQ Xo c q f) ∈ trivSet Xo c := by
  refine ⟨q.T, q.ι, q.y, fun a ha => ?_, rfl⟩
  obtain ⟨u, hu⟩ := q.triv a ha
  rw [← hu]
  exact vV_unit (u : q.T.V) (fun h => h u.isUnit)

end Charts

end GlobalTheory.Reg.ChartInt

namespace GlobalTheory

theorem integrality_at_trivial_valuations_of_charts :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), (∀ la : HeightOneSpectrum (𝓞 c.F), (∃ S : SCharts Xo c la, S.CovQ) ∧ ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n m : ℕ) (ws : Fin m → Rul Xo c), (∀ i, ws i ∈ sec Xo c a n) → Formalism.L2.PjFree.NoCommonZero Xo c ws → ∃ S : SCharts Xo c la, S.FamW ws ∧ S.CovQ) → ∀ C : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c), (∀ a n, C a n ≤ sec Xo c a n) → Formalism.L2.PjFree.RegularityR1Quotient Xo c C ∧ ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ C a n, ∀ la, (∀ v ∈ Formalism.L2.PjFree.valSet Xo c (Formalism.L2.PjFree.algCls Xo c) la, 0 ≤ v f) → ∀ v ∈ Formalism.L2.PjFree.valSet Xo c (Formalism.L2.PjFree.trivialClassCondition Xo c) la, 0 ≤ v f := by
  intro E _ _ _ H Dw l Xo c hS C hC
  refine ⟨?_, ?_⟩
  · rintro a n f hf ⟨la, h0⟩ q
    obtain ⟨S, hQ⟩ := (hS la).1
    exact GlobalTheory.Reg.ChartInt.nonneg_at_trivial S hQ (hC a n hf) h0 _ (GlobalTheory.Reg.ChartInt.qpt_mem_trivSet q)
  · intro a n f hf la h0
    obtain ⟨S, -⟩ := (hS la).1
    exact GlobalTheory.Reg.ChartInt.nonneg_at_all_points S (hC a n hf) h0

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg

theorem evR_eq_map_of_test_point {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (hL : EvLaws Xo c) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    {g : Rul Xo c} (hg : g ∈ sec Xo c a n) {S : Type} [CommRing S] [Algebra c.F S] (p : TRing c.F)
    (φ : p.R →ₐ[c.F] S) (y : FrPt Xo c p.R) (w : FrPt Xo c S) (hw : FrMap φ y w) :
    evR Xo c g w = φ (g p y) := by
  have h : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) w := ⟨p, φ, y, hw⟩
  unfold evR evalAt
  rw [dite_eq_left h]
  exact hL.wd g hg.1 S _ p _ φ _ y w h.choose_spec.choose_spec.choose_spec hw

theorem sec_eq_zero_of_generic_values :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → ∀ h : GenFrEx Xo c, Atlas h → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ g ∈ sec Xo c a n, (∀ Z, evC h Z g = 0) → g = 0 := by
  intro E _ _ _ H Dw l Xo c hL h hA a n g hg h0
  have hfield : ∀ (L : Type) [Field L] [Algebra c.F L] (w : FrPt Xo c L), evR Xo c g w = 0 := by
    intro L _ _ w
    obtain ⟨C, ψ, z, t', hz, hb⟩ := hA L w
    letI : Algebra c.F C.R := C.R.algebra
    obtain ⟨q, χ, y₀, hy₀⟩ := hL.test C.R C.y
    have h1 : evR Xo c g C.yg = 0 := by
      rw [hL.wt a n g hg _ C.t _ _ (hL.test _ _) (hL.test _ _) C.bor]
      have := h0 C.Z
      unfold evC at this
      rw [this, mul_zero]
    have h2 : χ (g q y₀) = 0 := by
      rw [evR_eq_map_of_test_point hL hg q (C.R.val.comp χ) y₀ C.yg
        (frMap_trans _ _ _ _ _ _ _ _ hy₀ C.gen)] at h1
      exact Subtype.ext h1
    have h3 : evR Xo c g z = 0 := by
      rw [evR_eq_map_of_test_point hL hg q (ψ.comp χ) y₀ z (frMap_trans _ _ _ _ _ _ _ _ hy₀ hz), AlgHom.comp_apply,
        h2, map_zero]
    rw [hL.wt a n g hg _ t' _ _ (hL.test _ _) (hL.test _ _) hb, h3, mul_zero]
  funext p y
  have hred : IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced _).1 p.rad
  show g p y = 0
  refine IsNilpotent.eq_zero ?_
  rw [nilpotent_iff_mem_prime]
  intro P hP
  let φ : p.R →ₐ[c.F] P.ResidueField := IsScalarTower.toAlgHom c.F p.R P.ResidueField
  obtain ⟨w, hw⟩ := hL.bc _ _ φ y
  have h4 := hfield _ w
  rw [evR_eq_map_of_test_point hL hg p φ y w hw] at h4
  exact Ideal.algebraMap_residueField_eq_zero.1 h4

end GlobalTheory.Reg
end

section

noncomputable section

namespace GlobalTheory.Reg.ReframeEx

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FrameTangent

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S]

def toM {x : Sp S ⟶ Xo.X} {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsTanAt x v) :
    TanM x Xo.univ.t.G :=
  mkT (ovT (t := Xo.univ.t) hv) (smT_zero_ovT (t := Xo.univ.t) hv)

theorem comb_iff {x : Sp S ⟶ Xo.X} {m : ℕ} {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)}
    (hv : ∀ j, IsTanAt x (v j)) (cf : Fin m → S) (w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left) :
    IsCombAt x v cf w ↔ (tv (∑ i, cf i • toM (hv i))).left = w := by
  have e := isCombAtG_iff Xo.univ.t x (fun j => ovT (t := Xo.univ.t) (hv j)) cf w
  refine e.trans ?_
  rw [tv_comb]
  rfl

theorem comb_unique {x : Sp S ⟶ Xo.X} {m : ℕ} {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)}
    (hv : ∀ j, IsTanAt x (v j)) {cf : Fin m → S} {w w' : Sp (DualNumber S) ⟶ Xo.univ.t.G.left}
    (h : IsCombAt x v cf w) (h' : IsCombAt x v cf w') : w = w' :=
  ((comb_iff hv cf w).1 h).symm.trans ((comb_iff hv cf w').1 h')

theorem comb_single {x : Sp S ⟶ Xo.X} {m : ℕ} {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)}
    (hv : ∀ j, IsTanAt x (v j)) (i : Fin m) : IsCombAt x v (Pi.single i 1) (v i) := by
  rw [comb_iff hv]
  have : ∑ j, (Pi.single i (1 : S) : Fin m → S) j • toM (hv j) = toM (hv i) := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [hj]
    · simp
  rw [this]
  rfl

theorem comb_exists [Algebra c.F S] {x : Sp S ⟶ Xo.X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} (τ : E →+* ℂ)
    (hv : ∀ j, IsTanAt x (v j)) (he : ∀ j, IsEigAt c τ (v j)) (cf : Fin m → S) :
    ∃ w, IsCombAt x v cf w ∧ IsTanAt x w ∧ IsEigAt c τ w := by
  refine ⟨_, (comb_iff hv cf _).2 rfl, isTanAtG_of (t := Xo.univ.t) _ (tv_zero' _), ?_⟩
  refine (isEigAt_iff τ (tv (∑ i, cf i • toM (hv i)))).2 fun a => ?_
  have hU : ∀ i, actL (x0 := x) Xo.univ.t.act a (toM (hv i)) = algebraMap c.F S (embK c τ a) • toM (hv i) :=
    fun i => tv_injective ((isEigAt_iff τ (ovT (t := Xo.univ.t) (hv i))).1 (he i) a)
  have : actL (x0 := x) Xo.univ.t.act a (∑ i, cf i • toM (hv i)) =
      algebraMap c.F S (embK c τ a) • ∑ i, cf i • toM (hv i) := by

    rw [map_sum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, hU, smul_comm]
  exact congrArg tv this

theorem exists_reframe [Algebra c.F S] (y : FrPt Xo c S)
    (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) (hg : ∀ τ, IsUnit (g τ).det) :
    ∃ y', Reframe g y y' := by
  choose u hu ht he using fun τ i => comb_exists τ (y.tan τ) (y.eig τ) (fun j => g τ j i)
  refine ⟨⟨y.x, y.x_over, u, ht, he, fun τ w hw hw' => ?_, y.s, y.gen⟩, rfl, hu⟩
  obtain ⟨a, ha, hua⟩ := y.basis τ w hw hw'
  have key : ∀ b w', IsCombAt y.x (u τ) b w' → IsCombAt y.x (y.u τ) ((g τ).mulVec b) w' := fun b w' h =>
    GlobalTheory.TangentLinear.isCombAt_mulVec E H Dw l Xo S y.x (y.u τ) (y.tan τ) (u τ) (g τ) b w' (hu τ) h
  refine ⟨(g τ)⁻¹.mulVec a, ?_, fun b hb => ?_⟩
  · obtain ⟨w', h1, -, -⟩ := comb_exists τ (ht τ) (he τ) ((g τ)⁻¹.mulVec a)
    have h2 := key _ _ h1
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hg τ), Matrix.one_mulVec] at h2
    show IsCombAt y.x (u τ) ((g τ)⁻¹.mulVec a) w
    rw [comb_unique (y.tan τ) ha h2]
    exact h1
  · rw [← hua _ (key b w hb), Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (hg τ), Matrix.one_mulVec]

theorem existsUnique_reframe [Algebra c.F S] (y y' : FrPt Xo c S) (hx : y'.x = y.x) :
    ∃! g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S,
      (∀ τ, IsUnit (g τ).det) ∧ Reframe g y y' := by
  have ht' : ∀ τ i, IsTanAt y.x (y'.u τ i) := fun τ i => hx ▸ y'.tan τ i
  have hb' : ∀ τ w, IsTanAt y.x w → IsEigAt c τ w → ∃! a : Fin (Dw.mult τ) → S, IsCombAt y.x (y'.u τ) a w := by
    rw [← hx]; exact y'.basis
  choose a ha hua using fun τ i => y.basis τ (y'.u τ i) (ht' τ i) (y'.eig τ i)
  choose b hb _ using fun τ i => hb' τ (y.u τ i) (y.tan τ i) (y.eig τ i)
  refine ⟨fun τ => Matrix.of fun j i => a τ i j, ⟨fun τ => ?_, hx, ha⟩, fun g hg => ?_⟩
  · have hm : (Matrix.of fun j i => a τ i j) * (Matrix.of fun j i => b τ i j) = 1 := by
      ext j i
      have h1 := GlobalTheory.TangentLinear.isCombAt_mulVec E H Dw l Xo S y.x (y.u τ) (y.tan τ) (y'.u τ)
        (Matrix.of fun j i => a τ i j) (b τ i) (y.u τ i) (ha τ) (hb τ i)
      have h2 := (y.basis τ (y.u τ i) (y.tan τ i) (y.eig τ i)).unique h1 (comb_single (y.tan τ) i)
      have h3 := congrFun h2 j
      rw [Pi.single_apply] at h3
      rw [Matrix.one_apply, ← h3]
      rfl
    exact Matrix.isUnit_det_of_right_inverse hm
  · funext τ
    ext j i
    exact congrFun (hua τ i _ (hg.2.2 τ i)) j

theorem reframe_exists_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), (∀ g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S, (∀ τ, IsUnit (g τ).det) → ∃ y', Reframe g y y') ∧ ∀ y' : FrPt Xo c S, y'.x = y.x → ∃! g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S, (∀ τ, IsUnit (g τ).det) ∧ Reframe g y y' :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ y => ⟨exists_reframe y, existsUnique_reframe y⟩

end GlobalTheory.Reg.ReframeEx
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem _root_.GlobalTheory.T.framedPoint_vectors_integral_in_cell : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (T : CDVR) (io : c.F →+* T.Fr) (f₀ : Γ(Y.X, M.U) →+* T.V) (ix : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) ↪ Fin M.n) (u₀ : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) T.V), (∀ τ, InCell (ix τ) (u₀ τ)) → letI := io.toAlgebra; ∀ (z : FrPt Xo c T.Fr) (Λ : M.Lift ((algebraMap T.V T.Fr).comp f₀) z.x), Λ.LieTie (fun τ => (u₀ τ).map (algebraMap T.V T.Fr)) z.u → ∀ (G : SAB H (Sp T.V)) (m : SABMap G Y.t (spMap f₀ ≫ M.hU.fromSpec)) (m2 : SABMap Λ.t' G (spMap (algebraMap T.V T.Fr))), m2.φ ≫ m.φ = Λ.m2.φ → ∃ ub : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (epsOver T.V T.V ⟶ G.G), (∀ τ i, IsTan (ub τ i)) ∧ (∀ τ i, IsEigV c io G τ (ub τ i)) ∧ (∀ τ (w : epsOver T.V T.V ⟶ G.G), IsTan w → IsEigV c io G τ w → ∃! a : Fin (Dw.mult τ) → T.V, IsComb (ub τ) a w) ∧ ∀ τ i, ∃ u' : Sp (DualNumber T.Fr) ⟶ Λ.t'.G.left, u' ≫ Λ.m1.φ = z.u τ i ∧ u' ≫ m2.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ (ub τ i).left := by
  first | exact @GlobalTheory.Reg.tie_vectors_integral | exact GlobalTheory.Reg.tie_vectors_integral | (intros; apply GlobalTheory.Reg.tie_vectors_integral <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.Reg.VecComb

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {M : MChart Y}
  {R : Type} [CommRing R]

theorem comb_unique {x : Sp R ⟶ Xo.X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber R) ⟶ Xo.univ.t.G.left)} {a : Fin m → R}
    {w w' : Sp (DualNumber R) ⟶ Xo.univ.t.G.left} (h : IsCombAt x v a w) (h' : IsCombAt x v a w') : w = w' := by
  obtain ⟨u, hu1, hu2⟩ := h
  obtain ⟨u', hu1', hu2'⟩ := h'
  have e : u = u' := funext fun i => Over.OverMorphism.ext ((hu1 i).trans (hu1' i).symm)
  rw [← hu2, ← hu2', e]

theorem comb_exists {x : Sp R ⟶ Xo.X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber R) ⟶ Xo.univ.t.G.left)}
    (hv : ∀ j, v j ≫ Xo.univ.t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x) (a : Fin m → R) :
    ∃ w, IsCombAt x v a w := by
  refine ⟨_, fun i => Over.homMk (spMap (epsMul (a i)) ≫ v i) ?_, fun i => rfl, rfl⟩
  show (spMap (epsMul (a i)) ≫ v i) ≫ Xo.univ.t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x
  have e : (epsMul (a i)).comp (algebraMap R (DualNumber R)) = algebraMap R (DualNumber R) :=
    RingHom.ext fun r => by simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]
  rw [Category.assoc, hv i, ← Category.assoc, ← spMap_comp, e]

variable [Algebra c.F R] {f : Γ(Y.X, M.U) →+* R} {x : Sp R ⟶ Xo.X}

theorem exists_frame (Λ : M.Lift f x) : ∃ V : Fin M.n → (Sp (DualNumber R) ⟶ Xo.univ.t.G.left),
    (∀ j, IsTanAt x (V j)) ∧ ∀ cv w, Λ.Vec cv w ↔ IsCombAt x V cv w := by
  obtain ⟨v', hv1, ⟨htan, -⟩, -⟩ := M.lie R f Λ.t' Λ.m2
  have p1 : IsGrpPullback Λ.t'.G Xo.univ.t.G x Λ.m1.φ := Λ.m1.2
  have p2 : IsGrpPullback Λ.t'.G Y.t.G (spMap f ≫ M.hU.fromSpec) Λ.m2.φ := Λ.m2.2
  refine ⟨fun j => (v' j).left ≫ Λ.m1.φ, fun j => ?_, fun cv w => ?_⟩
  · unfold IsTanAt
    constructor
    · rw [Category.assoc, p1.1.w, ← Category.assoc, Over.w (v' j)]
      rfl
    · exact (Chart.tan_push p1 (v' j)).1 (htan j)
  · unfold MChart.Lift.Vec IsCombAt
    constructor
    · rintro ⟨v'', u', hv'', hc, hw⟩
      have e : v'' = v' := funext fun j => Chart.inj_over p2 ((hv'' j).trans (hv1 j).symm)
      rw [e] at hc
      obtain ⟨u, hu1, hu2⟩ := (Chart.comb_push p1 cv v' u').1 hc
      exact ⟨u, fun i => hu1 i, hu2.trans hw⟩
    · rintro ⟨u, hu1, hu2⟩
      have hw : w ≫ Xo.univ.t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x := by
        rw [← hu2]
        exact Over.w (List.ofFn u).prod
      let u' : epsR R ⟶ Λ.t'.G :=
        Over.homMk (p1.1.lift w (spMap (algebraMap R (DualNumber R))) hw) (p1.1.lift_snd _ _ _)
      have hl : u'.left ≫ Λ.m1.φ = w := p1.1.lift_fst _ _ _
      exact ⟨v', u', hv1, (Chart.comb_push p1 cv v' u').2 ⟨u, fun i => hu1 i, hu2.trans hl.symm⟩, hl⟩

theorem isCombAt_iff_vec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (R : Type) [CommRing R] [Algebra c.F R] (f : Γ(Y.X, M.U) →+* R) (x : Sp R ⟶ Xo.X) (Λ : M.Lift f x), ∀ (m : ℕ) (cv : Fin m → Fin M.n → R) (w : Fin m → (Sp (DualNumber R) ⟶ Xo.univ.t.G.left)) (a : Fin m → R) (w' : Sp (DualNumber R) ⟶ Xo.univ.t.G.left), (∀ i, Λ.Vec (cv i) (w i)) → (IsCombAt x w a w' ↔ Λ.Vec (∑ i, a i • cv i) w') := by
  intro E _ _ _ H Dw l Xo c O _ β Y M R _ _ f x Λ m cv w a w' hw
  obtain ⟨V, hV, hVec⟩ := exists_frame Λ
  have hwc : ∀ i, IsCombAt x V (cv i) (w i) := fun i => (hVec _ _).1 (hw i)
  have e : (∑ i, a i • cv i) = (Matrix.of fun j i => cv i j).mulVec a := by
    funext j
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have key : ∀ w'', IsCombAt x w a w'' → IsCombAt x V (∑ i, a i • cv i) w'' := by
    intro w'' h
    rw [e]
    exact GlobalTheory.TangentLinear.isCombAt_mulVec E H Dw l Xo R x V hV w _ a w'' (fun i => hwc i) h
  have hov : ∀ {k : Fin M.n → R} {w0}, IsCombAt x V k w0 →
      w0 ≫ Xo.univ.t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x := by
    rintro k w0 ⟨u, -, hu⟩
    rw [← hu]
    exact Over.w (List.ofFn u).prod
  rw [hVec]
  constructor
  · exact key w'
  · intro h
    obtain ⟨w'', h''⟩ := comb_exists (fun i => hov (hwc i)) a
    exact comb_unique (key w'' h'') h ▸ h''

end GlobalTheory.Reg.VecComb
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem GlobalTheory.Reg.evR_baseChange_of_isReduced :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n → ∀ (S T : Type) [CommRing S] [IsReduced S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S) (z : FrPt Xo c T), FrMap φ y z → evR Xo c f z = φ (evR Xo c f y) := by
  intro E _ _ _ H Dw l Xo c hL a n f hf S T _ _ _ _ _ φ y z hm
  have hT1 : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y := hL.test S y
  have hT2 : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) z := by
    obtain ⟨p, ψ, y', hy'⟩ := hT1
    exact ⟨p, φ.comp ψ, y', frMap_trans (Xo := Xo) (c := c) _ _ _ ψ φ y' y z hy' hm⟩
  unfold evR evalAt
  rw [dite_eq_left hT2, dite_eq_left hT1]
  exact hL.wd f hf.1 T _ _ _ _ _ _ z hT2.choose_spec.choose_spec.choose_spec
    (frMap_trans (Xo := Xo) (c := c) _ _ _ _ φ _ y z hT1.choose_spec.choose_spec.choose_spec hm)
end
