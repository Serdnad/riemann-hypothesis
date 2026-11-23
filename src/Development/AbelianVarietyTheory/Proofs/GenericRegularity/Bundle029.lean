module

public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Bundle001
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.SCharts
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle017
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle028
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle017
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle022
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle034
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle002
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle068
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle047
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle039
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle027
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle008
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
import Mathlib.RingTheory.Valuation.AlgebraInstances
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

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

attribute [local instance 1100] Subalgebra.algebra in
attribute [local instance 100] IntermediateField.instAlgebraSubtypeMem in
theorem _root_.GlobalTheory.T.values_eq_of_common_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → ∀ h : GenFrEx Xo c, ∀ (C C' : FChart h) (L : Type) [Field L] [Algebra c.F L] (ψ : C.R →ₐ[c.F] L) (ψ' : C'.R →ₐ[c.F] L) (z z' : FrPt Xo c L) (t : Ix Dw → Lˣ), FrMap ψ C.y z → FrMap ψ' C'.y z' → FrBor t z z' → C.Z = C'.Z ∧ ∀ (e : Ix Dw → ℕ) (b : ∀ Z : Comp Xo c, Om Z) (hb : wchar e C.t * b C.Z ∈ C.R) (hb' : wchar e C'.t * b C'.Z ∈ C'.R), ψ' ⟨_, hb'⟩ = wchar e t * ψ ⟨_, hb⟩ := by
  first | exact @GlobalTheory.Reg.FChart.compat | exact GlobalTheory.Reg.FChart.compat | (intros; apply GlobalTheory.Reg.FChart.compat <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg

theorem isDiscreteValuationRing_valuationSubring_place {K : Type} [Field K] [NumberField K]
    (la : HeightOneSpectrum (𝓞 K)) : IsDiscreteValuationRing (la.valuation K).valuationSubring :=
  (la.valuation K).valuationSubring_isDiscreteValuationRing

theorem exists_sCharts : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → IntDiagUnit Xo c → ∀ la : HeightOneSpectrum (𝓞 c.F), ModelAt Xo c la → (∃ S : SCharts Xo c la, S.CovQ) ∧ ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n m : ℕ) (ws : Fin m → Rul Xo c), (∀ i, ws i ∈ sec Xo c a n) → Formalism.L2.PjFree.NoCommonZero Xo c ws → ∃ S : SCharts Xo c la, S.FamW ws ∧ S.CovQ := by
  intro hST E _ _ _ H Dw l Xo c hEv hDiag la hM
  obtain ⟨Y, hY⟩ := hM
  have := isDiscreteValuationRing_valuationSubring_place la

  obtain ⟨J, hJ, P, hP⟩ := GlobalTheory.T.exists_finite_integral_chart_cover_flagSpace hST E H Dw l Xo c hEv.bc (la.valuation c.F).valuationSubring Y hY
  have := hJ
  obtain ⟨S, hS, -⟩ := GlobalTheory.T.exists_normal_charts_of_covering_charts E H Dw l Xo c hEv hDiag la J P hP
  refine ⟨⟨S, hS⟩, fun a n m ws hws hnz => ?_⟩

  obtain ⟨J', hJ', P', hP', hF⟩ := GlobalTheory.T.exists_refined_covering_chart_family E H Dw l Xo c hEv _ _ J P hP a n m ws hws hnz
  have := hJ'
  obtain ⟨S', hS', hW⟩ := GlobalTheory.T.exists_normal_charts_of_covering_charts E H Dw l Xo c hEv hDiag la J' P' hP'
  exact ⟨S', hW m ws hF, hS'⟩

end GlobalTheory.Reg
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem _root_.GlobalTheory.T.noCommonZero_of_exists_finite_value : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → ∀ la : HeightOneSpectrum (𝓞 c.F), ModelAt Xo c la → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n m : ℕ) (ws : Fin m → Rul Xo c), (∀ i, ws i ∈ sec Xo c a n) → (∀ v ∈ Formalism.L2.PjFree.valSet Xo c (Formalism.L2.PjFree.algCls Xo c) la, ∃ i, v (ws i) ≠ ⊤) → Formalism.L2.PjFree.NoCommonZero Xo c ws := by
  first | exact @GlobalTheory.Reg.noCommonZero_of_finite_values | exact GlobalTheory.Reg.noCommonZero_of_finite_values | (intros; apply GlobalTheory.Reg.noCommonZero_of_finite_values <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField Topology ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace GlobalTheory.Reg.GenericFlagInj

theorem unitri_eq_of_lower {S : Type} [CommRing S] {n : ℕ} (A A' L : Matrix (Fin n) (Fin n) S)
    (hA : ∀ i j, j < i → A i j = 0) (hAd : ∀ i, A i i = 1)
    (hA' : ∀ i j, j < i → A' i j = 0) (hAd' : ∀ i, A' i i = 1)
    (hL : ∀ i j, i < j → L i j = 0) (e : A' = L * A) : A' = A := by
  first
  | exact @_root_.GlobalTheory.UnitriangularLowerMulEq.eq_of_unitriangular_of_eq_lower_mul
  | exact _root_.GlobalTheory.UnitriangularLowerMulEq.eq_of_unitriangular_of_eq_lower_mul
  | (apply _root_.GlobalTheory.UnitriangularLowerMulEq.eq_of_unitriangular_of_eq_lower_mul <;> assumption)
  | (intros; apply _root_.GlobalTheory.UnitriangularLowerMulEq.eq_of_unitriangular_of_eq_lower_mul <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UnitriangularLowerMulEq.eq_of_unitriangular_of_eq_lower_mul <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UnitriangularLowerMulEq.eq_of_unitriangular_of_eq_lower_mul ..)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem genPt_inj {Z Z' : Comp Xo c} (h : genPt Z = genPt Z') : Z = Z' := by
  have g : ∀ W : Comp Xo c, IsGenericPoint (genPt W) (W : Set (Xo.XF c)) := fun W =>
    W.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ W.2)
  exact Subtype.ext (by rw [← (g Z).def, ← (g Z').def, h])

theorem genSp_strK (Z : Comp Xo c) : genSp Z ≫ strK = spMap (algebraMap c.F (kap Z)) := by
  symm
  show Spec.map (CommRingCat.ofHom (Spec.preimage (genSp Z ≫ strK)).hom) = _
  rw [CommRingCat.ofHom_hom, Spec.map_preimage]

theorem genSp_eq {T : Type} [CommRing T] [Algebra c.F T] {Z Z' : Comp Xo c} (ψ : kap Z →ₐ[c.F] T)
    (ψ' : kap Z' →ₐ[c.F] T) (h : spMap ψ.toRingHom ≫ xGen Z = spMap ψ'.toRingHom ≫ xGen Z') :
    spMap ψ.toRingHom ≫ genSp Z = spMap ψ'.toRingHom ≫ genSp Z' := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc]
    exact h
  · have e := genSp_strK Z
    have e' := genSp_strK Z'
    rw [Category.assoc, Category.assoc]
    erw [e, e']
    rw [spMap_comp_ring, spMap_comp_ring]
    congr 1
    ext r
    exact (ψ.commutes r).trans (ψ'.commutes r).symm

theorem comp_eq {T : Type} [CommRing T] [Nontrivial T] [Algebra c.F T] {Z Z' : Comp Xo c} (ψ : kap Z →ₐ[c.F] T)
    (ψ' : kap Z' →ₐ[c.F] T) (h : spMap ψ.toRingHom ≫ xGen Z = spMap ψ'.toRingHom ≫ xGen Z') : Z = Z' := by
  obtain ⟨p⟩ : Nonempty (Sp T) := inferInstanceAs (Nonempty (PrimeSpectrum T))
  have e := congrArg (fun f : Sp T ⟶ Xo.XF c => f p) (genSp_eq ψ ψ' h)
  simp only [Scheme.Hom.comp_apply, genSp] at e
  apply genPt_inj
  exact (Scheme.fromSpecResidueField_apply _ _).symm.trans (e.trans (Scheme.fromSpecResidueField_apply _ _))

theorem emb_eq {T : Type} [CommRing T] [Algebra c.F T] {Z : Comp Xo c} (ψ ψ' : kap Z →ₐ[c.F] T)
    (h : spMap ψ.toRingHom ≫ xGen Z = spMap ψ'.toRingHom ≫ xGen Z) : ψ = ψ' := by
  have e := genSp_eq ψ ψ' h
  haveI : Mono (genSp Z) := by unfold genSp; infer_instance
  have e2 : spMap ψ.toRingHom = spMap ψ'.toRingHom := (cancel_mono (genSp Z)).1 e
  have e3 := congrArg CommRingCat.Hom.hom (Spec.map_injective e2)
  exact AlgHom.coe_ringHom_injective e3

noncomputable def resKap {T : Type} [CommRing T] [Algebra c.F T] {Z : Comp Xo c} (φ : Om Z →ₐ[c.F] T) : kap Z →ₐ[c.F] T :=
  { φ.toRingHom.comp (algebraMap (kap Z) (Om Z)) with
    commutes' := fun r => by
      have := φ.commutes r
      rw [gfp_tower] at this
      exact this }

theorem x_eq {T : Type} [CommRing T] [Algebra c.F T] (h : GenFrEx Xo c) {Z : Comp Xo c} (φ : Om Z →ₐ[c.F] T)
    {y : FrPt Xo c T} (hy : FrMap φ (genFr h Z) y) : y.x = spMap (resKap φ).toRingHom ≫ xGen Z := by
  rw [hy.1, (isGenFr_genFr h Z).1, ← Category.assoc, spMap_comp_ring]
  rfl

theorem eq_of_frBor {T : Type} [CommRing T] [Nontrivial T] [Algebra c.F T] (h : GenFrEx Xo c) (Z Z' : Comp Xo c)
    (φ : Om Z →ₐ[c.F] T) (φ' : Om Z' →ₐ[c.F] T) (y y' : FrPt Xo c T) (t : Ix Dw → Tˣ)
    (hy : FrMap φ (genFr h Z) y) (hy' : FrMap φ' (genFr h Z') y') (hb : FrBor t y y') : Z = Z' ∧ HEq φ φ' := by
  have hx := x_eq h φ hy
  have hx' := x_eq h φ' hy'
  have hxx := hx.symm.trans (hb.1.symm.trans hx')
  obtain rfl : Z = Z' := comp_eq _ _ hxx
  refine ⟨rfl, heq_of_eq ?_⟩
  have hψ : resKap φ = resKap φ' := emb_eq _ _ hxx
  obtain ⟨y₀, hy₀, hc⟩ := (isGenFr_genFr h Z).2
  have pull : ∀ (χ : Om Z →ₐ[c.F] T) (w : FrPt Xo c T), FrMap χ (genFr h Z) w → ∀ τ i,
      IsCombAt w.x (fun j => spMap (dualMap (resKap χ).toRingHom) ≫ y₀.u τ j) (fun j => χ (genCoef Z τ i j))
        (w.u τ i) := by
    intro χ w hw τ i
    refine isCombAt_pull χ.toRingHom hw.1 (fun j => ?_) (hw.2.1 τ i) (hc τ i)
    rw [← Category.assoc, spMap_comp_ring, ← dualMap_comp]
    rfl
  have hcoef : ∀ τ i j, φ' (genCoef Z τ i j) = φ (genCoef Z τ i j) := by
    intro τ
    choose cf hd hz hcf using hb.2.1 τ
    have hyx : y.x = spMap (resKap φ).toRingHom ≫ y₀.x := by rw [hx, hy₀]
    have key := unitri_eq_of_lower (Matrix.of fun i j => φ (genCoef Z τ i j))
      (Matrix.of fun i j => φ' (genCoef Z τ i j)) (Matrix.of cf)
      (fun i j hij => by simp [genCoef, not_lt.2 hij.le, hij.ne'])
      (fun i => by simp [genCoef])
      (fun i j hij => by simp [genCoef, not_lt.2 hij.le, hij.ne'])
      (fun i => by simp [genCoef]) (fun i j hij => hz i j hij) ?_
    · intro i j
      exact congrFun (congrFun key i) j
    · ext i j
      have h1 := pull φ' y' hy' τ i
      rw [← hψ, hb.1] at h1
      have h2 := GlobalTheory.TangentLinear.isCombAt_mulVec E H Dw l Xo T y.x
        (fun j => spMap (dualMap (resKap φ).toRingHom) ≫ y₀.u τ j)
        (fun j => hyx ▸ GlobalTheory.Frames.FramedBaseChange.tan_bc (resKap φ).toRingHom (y₀.tan τ j)) (y.u τ)
        (Matrix.of fun j i => φ (genCoef Z τ i j)) (cf i) (y'.u τ i) (pull φ y hy τ) (hcf i)
      have ht : IsTanAt y.x (y'.u τ i) := hb.1 ▸ y'.tan τ i
      rw [hyx] at h1 h2 ht
      have h3 := (GlobalTheory.Frames.eigenbasis_baseChange E H Dw l Xo c _ T (resKap φ) y₀ τ _ ht (y'.eig τ i)).unique h1 h2
      have h4 := congrFun h3 j
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply] at h4
      simp only [Matrix.mul_apply, Matrix.of_apply]
      rw [h4]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  apply AlgHom.coe_ringHom_injective
  refine IsLocalization.ringHom_ext (nonZeroDivisors (MvPolynomial (FlagVar Dw) (kap Z))) ?_
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun v => ?_)
  · exact AlgHom.congr_fun hψ r
  · obtain ⟨τ, ⟨i, j⟩, hij⟩ := v
    have := hcoef τ i j
    simp only [genCoef, dif_pos (show i < j from hij)] at this
    exact this.symm

end GlobalTheory.Reg.GenericFlagInj
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

namespace GlobalTheory.PinNum

theorem goodAt_of_two_primes {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (l : Level H) {a b : ℕ} (ha : a.Prime) (hb : b.Prime) (hab : a ≠ b)
    (hM : l.M = a * b) (p : ℕ) : l.GoodAt p := by
  have hodd := l.odd
  rw [hM, Nat.odd_mul] at hodd
  have ha3 : 3 ≤ a := by
    have := ha.two_le
    obtain ⟨k, hk⟩ := hodd.1
    omega
  have hb3 : 3 ≤ b := by
    have := hb.two_le
    obtain ⟨k, hk⟩ := hodd.2
    omega
  unfold Level.GoodAt
  have hM0 : l.M ≠ 0 := by have := l.three_le; omega
  by_cases hp : p.Prime
  swap
  · simpa [Nat.factorization_eq_zero_of_not_prime _ hp] using l.three_le
  have key : ∀ c, 3 ≤ c → c ∣ l.M → ¬ p ∣ c → 3 ≤ l.M / p ^ l.M.factorization p := fun c hc hd hn =>
    hc.trans (Nat.le_of_dvd (Nat.ordCompl_pos p hM0) (Nat.dvd_ordCompl_of_dvd_not_dvd hd hn))
  by_cases h : p ∣ a
  · refine key b hb3 (hM ▸ dvd_mul_left _ _) fun h' => hp.one_lt.ne' ?_
    exact Nat.eq_one_of_dvd_coprimes ((Nat.coprime_primes ha hb).2 hab) h h'
  · exact key a ha3 (hM ▸ dvd_mul_right _ _) h

theorem finrank_host (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  have h : (Module.finrank ℚ D.host.E : ℝ) = 2 * (D.R.f : ℝ) := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    push_cast
    ring
  exact_mod_cast h

theorem xiR_pos_le_one (D : D7) (Q : Par D) (h : Q.PinHost) : 0 < xiR D ∧ xiR D ≤ 1 := by
  obtain ⟨-, -, h3, -⟩ := h
  have hsq := Q.H.sqrt_neg_disc_sq
  rw [h3] at hsq
  have hd : (1 : ℝ) ≤ Q.H.d := by exact_mod_cast Q.H.d_prime.one_le
  have hn : ‖D.host.φ₀ D.host.sqrtMinusD‖ ^ 2 = Q.H.d := by
    rw [← norm_pow, hsq, norm_neg, Complex.norm_natCast]
  have h1 : 1 ≤ ‖D.host.φ₀ D.host.sqrtMinusD‖ := by
    by_contra hc
    push Not at hc
    nlinarith [norm_nonneg (D.host.φ₀ D.host.sqrtMinusD)]
  have hN : (1 : ℝ) ≤ (Ideal.absNorm D.host.ccK : ℝ) := by
    have : Ideal.absNorm D.host.ccK ≠ 0 := fun h0 => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact_mod_cast Nat.one_le_iff_ne_zero.2 this
  have hx : xiR D = 1 / ((Ideal.absNorm D.host.ccK : ℝ) * ‖D.host.φ₀ D.host.sqrtMinusD‖) := by
    unfold xiR Formalism.BasicNotions.Host.xi0
    rw [map_div₀, map_mul, map_natCast, map_neg, map_one, norm_div, norm_neg, norm_one, norm_mul,
      Complex.norm_natCast]
  have h2 : (1 : ℝ) ≤ (Ideal.absNorm D.host.ccK : ℝ) * ‖D.host.φ₀ D.host.sqrtMinusD‖ :=
    one_le_mul_of_one_le_of_one_le hN h1
  rw [hx]
  exact ⟨by positivity, (div_le_one (by positivity)).2 h2⟩

theorem numerics_of_pins : ∀ (D : D7) (Q : Par D), Q.Pins → (∀ p : ℕ, p.Prime → Q.l.GoodAt p) ∧ Q.l.A = 1 ∧ Q.l.M' = Q.l.M ∧ 0 < xiR D ∧ xiR D ≤ 1 ∧ Module.finrank ℚ D.host.E = 2 * D.R.f ∧ ∀ j, InR D j → (Q.Dw j).p + (Q.Dw j).q = D.R.r ∧ 1 ≤ D.R.r ∧ (Q.Dw j).dim + Nat.card (FlagVar (Q.Dw j)) = WeightFamilies.dimY D j := by
  intro D Q ⟨hH, ⟨hM, hA⟩, _, hD⟩
  have hx := xiR_pos_le_one D Q hH
  refine ⟨fun p _ => goodAt_of_two_primes Q.l (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne hM p, hA, ?_,
    hx.1, hx.2, finrank_host D, fun j hj => ?_⟩
  · rw [Level.M', hA, Nat.lcm_one_right]
  · obtain ⟨hp, hq, -⟩ := hD j hj
    have hk := D.R.m_add_three_le_k
    obtain ⟨hj1, hj2⟩ := hj
    refine ⟨?_, ?_, ?_⟩
    · rw [hp, hq]
      simp only [Ranks.sigW, Ranks.r]
      omega
    · unfold Ranks.r
      omega
    · rw [GlobalTheory.FlagDim.dim_add_card_flagVar, finrank_host, Nat.mul_div_cancel_left _ two_pos, hp, hq]
      rfl

end GlobalTheory.PinNum
end
