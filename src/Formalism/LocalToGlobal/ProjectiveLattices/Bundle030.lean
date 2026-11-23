module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle029
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle026
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle007
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section



noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

def PartIAt (Xo : Moduli Dw l) (c : Coeff l) : Prop :=
  ∀ (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → l.GoodAt p →
    ∃ Y : Model Xo c (c.V W).subtype, Y.N3 ∧ PushInvertible Y.t.G Y.t.PP.L

theorem exists_lieElement_middleBlockPart (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F)) :
    ∃ W : ValuationSubring ℂ, (∀ x : 𝓞 c.F, x ∈ la.asIdeal → (((algebraMap (𝓞 c.F) c.F x : c.F) : ℂ)) ∈ W.nonunits) ∧
      ∀ x : c.F, (x : ℂ) ∈ W → la.valuation c.F x ≤ 1 := by
  set V := (la.valuation c.F).valuationSubring with hVdef
  let g : V →+* ℂ := c.F.val.toRingHom.comp V.subtype
  have hg : Function.Injective g := fun a b h => Subtype.ext (c.F.val.injective h)
  let e : V ≃+* g.range := RingEquiv.ofBijective g.rangeRestrict ⟨fun a b h => hg (congrArg (fun z : g.range => (z : ℂ)) h),
    g.rangeRestrict_surjective⟩
  have hmax : ((IsLocalRing.maximalIdeal V).map e).IsMaximal := Ideal.map_isMaximal_of_equiv e
  obtain ⟨W, hAW, hIW⟩ := Ideal.image_subset_nonunits_valuationSubring _ hmax.ne_top
  have hnon : ∀ y : V, y ∈ IsLocalRing.maximalIdeal V → g y ∈ W.nonunits := fun y hy =>
    hIW ⟨e y, Ideal.mem_map_of_mem _ hy, rfl⟩
  refine ⟨W, fun x hx => ?_, fun x hx => ?_⟩
  · have hxV : algebraMap (𝓞 c.F) c.F x ∈ V := by
      rw [hVdef, Valuation.mem_valuationSubring_iff, HeightOneSpectrum.valuation_of_algebraMap]
      exact la.intValuation_le_one x
    have hxm : (⟨_, hxV⟩ : V) ∈ IsLocalRing.maximalIdeal V := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.1 hu
      have h1 : la.valuation c.F (algebraMap (𝓞 c.F) c.F x) < 1 := by
        rw [HeightOneSpectrum.valuation_of_algebraMap]; exact (la.intValuation_lt_one_iff_mem x).2 hx
      have h2 : la.valuation c.F ((w : V) : c.F) ≤ 1 := w.2
      have h3 := congrArg (fun z : V => la.valuation c.F (z : c.F)) hw
      simp only [MulMemClass.coe_mul, OneMemClass.coe_one, map_mul, map_one] at h3
      have h4 : la.valuation c.F (algebraMap (𝓞 c.F) c.F x) * la.valuation c.F ((w : V) : c.F) < 1 :=
        lt_of_lt_of_le (mul_lt_one_of_nonneg_of_lt_one_left zero_le h1 h2) le_rfl
      rw [h3] at h4
      exact lt_irrefl _ h4
    exact hnon _ hxm
  · by_contra hv
    push_neg at hv
    have hx0 : x ≠ 0 := by rintro rfl; simp at hv
    have hiV : x⁻¹ ∈ V := by
      rw [hVdef, Valuation.mem_valuationSubring_iff, map_inv₀]
      exact (inv_lt_one_of_one_lt₀ hv).le
    have him : (⟨x⁻¹, hiV⟩ : V) ∈ IsLocalRing.maximalIdeal V := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.1 hu
      have h1 : (w : c.F) = x := by
        have := congrArg (fun z : V => (z : c.F)) hw
        simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at this
        field_simp at this
        exact this
      have h2 : la.valuation c.F ((w : V) : c.F) ≤ 1 := w.2
      rw [h1] at h2
      exact absurd h2 (not_le.2 hv)
    have h5 := hnon _ him
    rw [ValuationSubring.mem_nonunits_iff] at h5
    have h6 := (ValuationSubring.valuation_le_one_iff W _).2 hx
    have h7 : g ⟨x⁻¹, hiV⟩ = ((x : ℂ))⁻¹ := by
      show ((x⁻¹ : c.F) : ℂ) = _
      exact map_inv₀ c.F.val x
    rw [h7, map_inv₀] at h5
    have hW0 : W.valuation (x : ℂ) ≠ 0 := by
      rw [Valuation.ne_zero_iff]; exact_mod_cast hx0
    exact absurd ((inv_lt_one₀ (zero_lt_iff.2 hW0)).1 h5) (not_lt.2 h6)

theorem modelAtSt_of {Xo : Moduli Dw l} {c : Coeff l} (hI : PartIAt Xo c) (hgood : ∀ p : ℕ, p.Prime → l.GoodAt p)
    (la : HeightOneSpectrum (𝓞 c.F)) : ModelAtSt Xo c la := by
  obtain ⟨W, hWnon, hWkey⟩ := exists_lieElement_middleBlockPart c la
  have hp : (Formalism.MainNotions.WeightAlgebra.resCh la).Prime := resCh_prime la
  have hmem : ((Formalism.MainNotions.WeightAlgebra.resCh la : ℕ) : 𝓞 c.F) ∈ la.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact ringChar.Nat.cast_ringChar
  have hpW : ((Formalism.MainNotions.WeightAlgebra.resCh la : ℕ) : ℂ) ∈ W.nonunits := by
    have := hWnon _ hmem
    simpa using this
  obtain ⟨Y, hN3, hPI⟩ := hI _ W hp hpW (hgood _ hp)
  refine ⟨c.V W, inferInstance, (c.V W).subtype, Y, hN3, hPI, fun Tc io e ho => ?_⟩
  have hint : ∀ x : c.V W, io (x : c.F) ∈ (algebraMap Tc.V Tc.Fr).range := by
    intro x
    have hx : la.valuation c.F (x : c.F) ≤ 1 := hWkey _ x.2
    apply HeightOneSpectrum.mem_integers_of_valuation_le_one
    intro v
    have hv : v = IsDiscreteValuationRing.maximalIdeal Tc.V :=
      HeightOneSpectrum.ext (IsLocalRing.eq_maximalIdeal v.isMaximal)
    subst hv
    by_cases hx0 : (x : c.F) = 0
    · rw [hx0, map_zero, map_zero]; exact zero_le
    have hvx0 : la.valuation c.F (x : c.F) ≠ 0 := (Valuation.ne_zero_iff _).2 hx0
    have hla : 0 ≤ vLa la (x : c.F) := by
      unfold vLa
      rw [← WithZero.exp_log hvx0, ← WithZero.exp_zero, WithZero.exp_le_exp] at hx
      linarith
    have hvV : 0 ≤ vV Tc.V (io (x : c.F)) := by
      rw [ho.2 (x : c.F)]
      positivity
    have hio0 : io (x : c.F) ≠ 0 := (map_ne_zero io).2 hx0
    have hval0 : valV Tc.V (io (x : c.F)) ≠ 0 := valV_ne_zero hio0
    show valV Tc.V (io (x : c.F)) ≤ 1
    unfold vV at hvV
    rw [← WithZero.exp_log hval0, ← WithZero.exp_zero, WithZero.exp_le_exp]
    linarith
  let f : c.V W →+* (algebraMap Tc.V Tc.Fr).range := (io.comp (c.V W).subtype).codRestrict _ hint
  let eq : Tc.V ≃+* (algebraMap Tc.V Tc.Fr).range := RingEquiv.ofBijective (algebraMap Tc.V Tc.Fr).rangeRestrict
    ⟨fun a b h => IsFractionRing.injective Tc.V Tc.Fr (congrArg (fun z : (algebraMap Tc.V Tc.Fr).range => (z : Tc.Fr)) h),
      (algebraMap Tc.V Tc.Fr).rangeRestrict_surjective⟩
  refine ⟨eq.symm.toRingHom.comp f, ?_⟩
  ext x
  have := congrArg (fun z : (algebraMap Tc.V Tc.Fr).range => (z : Tc.Fr)) (eq.apply_symm_apply (f x))
  exact this

theorem goodAt_of_two_primes {g0 g1 : ℕ} (hM : l.M = g0 * g1) (h0 : g0.Prime) (h1 : g1.Prime)
    (hne : g0 ≠ g1) (p : ℕ) (hp : p.Prime) : l.GoodAt p := by
  unfold Level.GoodAt
  have hodd : Odd (g0 * g1) := hM ▸ l.odd
  have h3 : 3 ≤ g0 * g1 := hM ▸ l.three_le
  have o0 : Odd g0 := (Nat.odd_mul.1 hodd).1
  have o1 : Odd g1 := (Nat.odd_mul.1 hodd).2
  have t0 : 3 ≤ g0 := by
    have := h0.two_le
    have := Nat.odd_iff.1 o0
    omega
  have t1 : 3 ≤ g1 := by
    have := h1.two_le
    have := Nat.odd_iff.1 o1
    omega
  rw [hM, Nat.factorization_mul h0.ne_zero h1.ne_zero, Finsupp.add_apply, h0.factorization, h1.factorization]
  by_cases e0 : p = g0
  · have e : (Finsupp.single g0 1 : ℕ →₀ ℕ) p + (Finsupp.single g1 1 : ℕ →₀ ℕ) p = 1 := by
      simp [Finsupp.single_apply, e0, hne, hne.symm]
    rw [e, pow_one, e0, Nat.mul_div_cancel_left g1 h0.pos]
    exact t1
  · by_cases e1 : p = g1
    · have e : (Finsupp.single g0 1 : ℕ →₀ ℕ) p + (Finsupp.single g1 1 : ℕ →₀ ℕ) p = 1 := by
        simp [Finsupp.single_apply, e1, hne, hne.symm]
      rw [e, pow_one, e1, Nat.mul_div_cancel g0 h1.pos]
      exact t0
    · have e : (Finsupp.single g0 1 : ℕ →₀ ℕ) p + (Finsupp.single g1 1 : ℕ →₀ ℕ) p = 0 := by
        simp [Finsupp.single_apply, e0, e1, Ne.symm e0, Ne.symm e1]
      rw [e, pow_zero, Nat.div_one]
      exact h3

theorem partIAt_of (hP : PartI) (hN : N1ab) (Xo : Moduli Dw l) (c : Coeff l) (hpq : 1 ≤ Dw.p + Dw.q) : PartIAt Xo c := by
  classical
  obtain ⟨-, hI⟩ := hP
  let Xf : ∀ l' : Level H, Moduli Dw l' := fun l' =>
    if h : l' = l then h ▸ Xo else Classical.choice (hN E H Dw l' hpq)
  obtain ⟨Y, hY, -⟩ := hI E H Dw hpq Xf
  intro p W hp hW hg
  obtain ⟨hN2, hrest⟩ := hY p W hp hW
  let i : Idx H p := ⟨l, c, hg⟩
  have hPIi := (hN2.1 i).2.2.1
  have hN3 := (hrest i).2.1
  have hX : Xf l = Xo := by simp [Xf]
  have key : ∀ (X' : Moduli Dw l), X' = Xo → ∀ Y' : Model X' c (c.V W).subtype, Y'.N3 →
      PushInvertible Y'.t.G Y'.t.PP.L → ∃ Y : Model Xo c (c.V W).subtype, Y.N3 ∧ PushInvertible Y.t.G Y.t.PP.L := by
    rintro X' rfl Y' h1 h2
    exact ⟨Y', h1, h2⟩
  exact key (Xf l) hX (Y p W hp hW i) hN3 hPIi

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra NumberField IsDedekindDomain Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

def RegularityR2 (X : PJ D B P j) (E : PtExt X)
    (NoZero : ∀ {wL : WeightFamilies.Wt D j} {n : ℕ}, (Fin n → B.Cusp j wL) → Prop) : Prop :=
  (∀ (wL wE : WeightFamilies.Wt D j) (n : ℕ) (gens : Fin n → B.Cusp j wL) (et : B.Cusp j wE)
    (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) (c : ℝ), 0 ≤ c → NoZero gens →
    (∀ la (y : X.Pt la), 0 ≤ X.vAt la y (X.inc wE et) ∧ (X.vAt la y (X.inc wE et) ≠ ⊤ →
      (⨅ k, X.vAt la y (X.inc wL (gens k))) ≤
        (((nus la : ℝ) + c * (X.vAt la y (X.inc wE et)).toReal : ℝ) : EReal))) →
    ∀ la (y' : E.Pt' la), 0 ≤ E.vAt' la y' (X.inc wE et) ∧ (E.vAt' la y' (X.inc wE et) ≠ ⊤ →
      (⨅ k, E.vAt' la y' (X.inc wL (gens k))) ≤
        (((nus la : ℝ) + c * (E.vAt' la y' (X.inc wE et)).toReal : ℝ) : EReal))) ∧
  (∀ (wL : WeightFamilies.Wt D j) (n : ℕ) (gens : Fin n → B.Cusp j wL) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ),
    NoZero gens →
    (∀ la (y : X.Pt la), (⨅ k, X.vAt la y (X.inc wL (gens k))) ≤ ((nus la : ℝ) : EReal)) →
    ∀ la (y' : E.Pt' la), (⨅ k, E.vAt' la y' (X.inc wL (gens k))) ≤ ((nus la : ℝ) : EReal))

theorem iInf_span_eq {X : PJ D B P j} {wL : WeightFamilies.Wt D j} {n : ℕ} (g : Fin n → B.Cusp j wL)
    (la : HeightOneSpectrum (𝓞 B.KO)) (v : X.Forms → EReal) (hv0 : v 0 = ⊤)
    (hadd : ∀ F G, min (v F) (v G) ≤ v (F + G))
    (hsmul : ∀ (a : B.KO) F, a ≠ 0 → v (a • F) = (((vAdd la a : ℤ) : ℝ) : EReal) + v F)
    (hint : ∀ a : 𝓞 B.KO, (a : B.KO) ≠ 0 → 0 ≤ vAdd la (a : B.KO)) :
    (⨅ F ∈ Submodule.span (𝓞 B.KO) (Set.range g), v (X.inc wL F)) = ⨅ k, v (X.inc wL (g k)) := by
  apply le_antisymm
  · exact le_iInf fun k => iInf₂_le (g k) (Submodule.subset_span (Set.mem_range_self k))
  · refine le_iInf₂ fun F hF => ?_
    induction hF using Submodule.span_induction with
    | mem x hx => obtain ⟨k, rfl⟩ := hx; exact iInf_le _ k
    | zero => simp [hv0]
    | add x y _ _ hx hy =>
      rw [map_add (f := _)]; exact le_trans (le_min hx hy) (hadd _ _)
    | smul a x _ hx =>
      by_cases ha : (a : B.KO) = 0
      · have : a = 0 := by exact_mod_cast ha
        subst this; simp [hv0]
      · have hsm : X.inc wL (a • x) = (a : B.KO) • X.inc wL x := by
          rw [← map_smul]; congr 1; exact (algebraMap_smul B.KO a x).symm
        rw [hsm, hsmul _ _ ha]
        have h0 : (0 : EReal) ≤ (((vAdd la (a : B.KO) : ℤ) : ℝ) : EReal) := by
          exact_mod_cast hint a ha
        calc (⨅ k, v (X.inc wL (g k))) = 0 + ⨅ k, v (X.inc wL (g k)) := (zero_add _).symm
          _ ≤ _ := add_le_add h0 hx

def gd2Xplus {ka wL wF : WeightFamilies.Wt D j} {X : PJ D B P j} (G : GlobalFamilyData X ka wL wF) (E : PtExt X)
    (hM : IntAtExt X E) : GlobalFamilyData (xplus X E hM) ka wL wF :=
  ⟨G.N, G.w, G.del, G.th', G.rz, G.alz, G.th0, G.zc, G.rq, G.th, G.iet, G.et, G.mx⟩

theorem combBound_xplus {ka wL wF : WeightFamilies.Wt D j} (X : PJ D B P j) (E : PtExt X) (hM : IntAtExt X E)
    (NoZero : ∀ {wL : WeightFamilies.Wt D j} {n : ℕ}, (Fin n → B.Cusp j wL) → Prop)
    (G : GlobalFamilyData X ka wL wF) (S : Scal B) (c : ℝ) (hc : 0 ≤ c) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ)
    (hspan : Submodule.span (𝓞 B.KO) (Set.range G.w) = X.WWc S.sW wL) (hNZ : NoZero G.w)
    (hint : ∀ (la : HeightOneSpectrum (𝓞 B.KO)) (a : 𝓞 B.KO), (a : B.KO) ≠ 0 → 0 ≤ vAdd la (a : B.KO))
    (hX : CombBound G S c nus) (hR2 : RegularityR2 X E NoZero) :
    CombBound (gd2Xplus G E hM) S c nus := by
  have dX : ∀ la (y : X.Pt la), X.depth S.sW wL la y = ⨅ k, X.vAt la y (X.inc wL (G.w k)) := by
    intro la y
    unfold PJ.depth
    rw [← hspan]
    exact iInf_span_eq G.w la (X.vAt la y) (X.vAt_zero la y) (X.vAt_add la y) (X.vAt_smul la y) (hint la)
  have dE : ∀ la (y : E.Pt' la), (⨅ F ∈ X.WWc S.sW wL, E.vAt' la y (X.inc wL F)) =
      ⨅ k, E.vAt' la y (X.inc wL (G.w k)) := by
    intro la y
    rw [← hspan]
    exact iInf_span_eq G.w la (E.vAt' la y) (E.vAt'_zero la y) (E.vAt'_add la y) (E.vAt'_smul la y) (hint la)
  intro la y
  cases y with
  | inl y0 => exact hX la y0
  | inr y1 =>
    refine ⟨fun hj => ?_, fun hj => ?_⟩
    · have hc' : 0 ≤ c / (2 * (G.iet : ℝ)) := by positivity
      have := hR2.1 wL _ G.N G.w G.et nus _ hc' hNZ
        (fun la' y => by have h := (hX la' y).1 hj; rw [dX] at h; exact h) la y1
      show 0 ≤ E.vAt' la y1 (X.inc _ G.et) ∧ (E.vAt' la y1 (X.inc _ G.et) ≠ ⊤ →
        (⨅ F ∈ X.WWc S.sW wL, E.vAt' la y1 (X.inc wL F)) ≤ _)
      rw [dE]; exact this
    · have := hR2.2 wL G.N G.w nus hNZ (fun la' y => by have h := (hX la' y).2 hj; rw [dX] at h; exact h) la y1
      show (⨅ F ∈ X.WWc S.sW wL, E.vAt' la y1 (X.inc wL F)) ≤ _
      rw [dE]; exact this

section l2NormAlt

variable (N : ∀ j ka, (B.KO →+* ℂ) → B.Cusp j ka → ℝ)
    (h0 : ∀ j ka σ F, 0 ≤ N j ka σ F) (h1 : ∀ j ka σ F, N j ka σ F = 0 ↔ F = 0)
    (h2 : ∀ j ka σ (a : B.KO) F, N j ka σ (a • F) = ‖σ a‖ * N j ka σ F)
    (h3 : ∀ j ka σ F G, N j ka σ (F + G) ≤ N j ka σ F + N j ka σ G)
    (h4 : ∀ j ka σ F, N j ka σ F ≤ B.supN j ka σ F)

end l2NormAlt

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open Formalism.BasicNotions Formalism.MainNotions NumberField

section Pull

variable {E : Type} [Field E] [NumberField E] {Y Y' : Type} [AddCommGroup Y] [Module (𝓞 E) Y]
  [AddCommGroup Y'] [Module (𝓞 E) Y']

def pullF (e : Y ≃ₗ[𝓞 E] Y') : (Y' →ₗ[ℤ] Y' →ₗ[ℤ] ℝ) →ₗ[ℝ] (Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) where
  toFun β := β.compl₁₂ (e.toAddEquiv.toIntLinearEquiv : Y →ₗ[ℤ] Y') (e.toAddEquiv.toIntLinearEquiv : Y →ₗ[ℤ] Y')
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

@[simp] theorem pullF_apply (e : Y ≃ₗ[𝓞 E] Y') (β : Y' →ₗ[ℤ] Y' →ₗ[ℤ] ℝ) (a b : Y) :
    pullF e β a b = β (e a) (e b) := by
  simp [pullF]

def pullS (cj : E → E) (e : Y ≃ₗ[𝓞 E] Y') : ModuliIntegralCharts.SymB cj Y' →ₗ[ℝ] ModuliIntegralCharts.SymB cj Y :=
  (pullF e).restrict fun β hβ => by
    refine ⟨fun a b => ?_, fun c c' h a b => ?_⟩
    · simp only [pullF_apply]; exact hβ.1 _ _
    · simp only [pullF_apply, LinearEquiv.map_smul]; exact hβ.2 c c' h _ _

@[simp] theorem pullS_apply (cj : E → E) (e : Y ≃ₗ[𝓞 E] Y') (β : ModuliIntegralCharts.SymB cj Y') (a b : Y) :
    (pullS cj e β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a b = (β : Y' →ₗ[ℤ] Y' →ₗ[ℤ] ℝ) (e a) (e b) :=
  pullF_apply e _ a b

theorem pullS_symm (cj : E → E) (e : Y ≃ₗ[𝓞 E] Y') (β : ModuliIntegralCharts.SymB cj Y') :
    pullS cj e.symm (pullS cj e β) = β := by
  apply Subtype.ext; ext a b; simp

def phiSet (cj : E → E) {Z : Type} [AddCommGroup Z] [Module (𝓞 E) Z] (b : ModuliIntegralCharts.SymB cj Z) : Set ℝ :=
  {x | ∃ l : ModuliIntegralCharts.SymB cj Z →ₗ[ℝ] ℝ,
    (∀ β : ModuliIntegralCharts.SymB cj Z, (∀ a c, ∃ z : ℤ, (β : Z →ₗ[ℤ] Z →ₗ[ℤ] ℝ) a c = z) → ∃ z : ℤ, l β = z) ∧
    (∀ β : ModuliIntegralCharts.SymB cj Z, (∀ a, 0 ≤ (β : Z →ₗ[ℤ] Z →ₗ[ℤ] ℝ) a a) → β ≠ 0 → 0 < l β) ∧ x = l b}

theorem phiC_eq_sInf (cj : E → E) {Z : Type} [AddCommGroup Z] [Module (𝓞 E) Z] (b : ModuliIntegralCharts.SymB cj Z) :
    ModuliIntegralCharts.phiC cj b = sInf (phiSet cj b) := rfl

theorem phiSet_pull_sub (cj : E → E) (e : Y ≃ₗ[𝓞 E] Y') (b : ModuliIntegralCharts.SymB cj Y') :
    phiSet cj (pullS cj e b) ⊆ phiSet cj b := by
  rintro x ⟨l, hI, hP, rfl⟩
  refine ⟨l.comp (pullS cj e), fun β hβ => hI _ fun a c => ?_, fun β hβ hne => hP _ (fun a => ?_) ?_, rfl⟩
  · obtain ⟨z, hz⟩ := hβ (e a) (e c); exact ⟨z, by simpa using hz⟩
  · simpa using hβ (e a)
  · intro h0; apply hne
    have h1 := congrArg (pullS cj e.symm) h0
    rw [pullS_symm, map_zero] at h1; exact h1

theorem phiC_pull (cj : E → E) (e : Y ≃ₗ[𝓞 E] Y') (b : ModuliIntegralCharts.SymB cj Y') :
    ModuliIntegralCharts.phiC cj (pullS cj e b) = ModuliIntegralCharts.phiC cj b := by
  rw [phiC_eq_sInf, phiC_eq_sInf]; congr 1
  refine (phiSet_pull_sub cj e b).antisymm ?_
  have h := phiSet_pull_sub cj e.symm (pullS cj e b)
  rwa [pullS_symm] at h

end Pull

namespace LocView

variable {D : D7} {r j p : ℕ} (L : ModuliIntegralCharts.Loc D r j p) {Z : L.Mdl} (y : L.Pt Z) {Y' : Type} [AddCommGroup Y']
  [Module (𝓞 D.host.E) Y']

theorem phiCy_of (e : L.Ylat y ≃ₗ[𝓞 D.host.E] Y') (bA : ModuliIntegralCharts.SymB (fun x : D.host.E => D.host.conj x) Y')
    (h : ∀ a b, (bA : Y' →ₗ[ℤ] Y' →ₗ[ℤ] ℝ) (e a) (e b) = L.be y a b) :
    L.phiCy y = ModuliIntegralCharts.phiC (fun x : D.host.E => D.host.conj x) bA := by
  have hS : L.beS y = pullS _ e bA := by
    apply Subtype.ext; apply LinearMap.ext₂; intro a b
    show L.be y a b = _
    rw [pullS_apply, h]
  show ModuliIntegralCharts.phiC _ (L.beS y) = _
  rw [hS, phiC_pull]

end LocView

namespace In66

variable {D : D7} {Q : Par D} (G : In66 Q)

theorem phiCy_eq (hL : G.PinLat) {j : ℕ} (hj : 1 ≤ j) (hm : j < D.R.m) {la : IsDedekindDomain.HeightOneSpectrum (𝓞 Q.c.F)}
    {z : PointsOfFlagModel.Pt (G.Tw j (WeightAlgebra.resCh la)) .yy} (hz : G.IsAlgPt j la z) {η} (hr : G.rel j (WeightAlgebra.resCh la) η z)
    (A : DatAt ((G.Tw j (WeightAlgebra.resCh la)).Y z.1) z.2.2.1)
    (bA : ModuliIntegralCharts.SymB (fun x : D.host.E => D.host.conj x) A.Ylat)
    (hb : ∀ a b, (bA : A.Ylat →ₗ[ℤ] A.Ylat →ₗ[ℤ] ℝ) a b = A.beta a b) :
    (G.P.loc (G.dat j) (WeightAlgebra.resCh la)).phiCy η = ModuliIntegralCharts.phiC (fun x : D.host.E => D.host.conj x) bA := by
  have h := hL j hj hm la z hz η hr A
  exact h.elim fun e he => LocView.phiCy_of _ η e bA fun a b => (hb _ _).trans (he a b)

end In66

end Formalism.L2.Pj
end
end

section



noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

def RdIndep (σ : c.F →+* ℂ) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (k : ℕ), Dom a k → ∀ (n : ℕ) (b : Fin n → Rul Xo c), (∀ i, b i ∈ sec Xo c a k) →
    LinearIndependent c.F b → LinearIndependent ℂ (fun i => rdU (U σ) (b i))

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

def cusp (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Submodule c.F (Rul Xo c) :=
  sec Xo c a n ⊓ ⨅ (σ : c.F →+* ℂ) (_ : GoodEmb c σ), (holSub (U σ).X (laU (U σ) a n)).comap (rdU (U σ))

theorem cusp_le_sec (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : cusp Xo c U a n ≤ sec Xo c a n := inf_le_left

theorem mem_cusp (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c) :
    f ∈ cusp Xo c U a n ↔ f ∈ sec Xo c a n ∧ ∀ σ : c.F →+* ℂ, GoodEmb c σ → rdU (U σ) f ∈ holSub (U σ).X (laU (U σ) a n) := by
  unfold cusp
  simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap]

def mulC (f g : Rul Xo c) : Rul Xo c := f * g

theorem mulC_mem_sec (a a' : (E →+* ℂ) × ℕ → ℕ) (n n' : ℕ) {f g : Rul Xo c} (hf : f ∈ sec Xo c a n)
    (hg : g ∈ sec Xo c a' n') : mulC Xo c f g ∈ sec Xo c (a + a') (n + n') := by
  unfold mulC
  exact sec_mul Xo c a a' n n' hf hg

def CuspMul : Prop :=
  ∀ (a a' : (E →+* ℂ) × ℕ → ℕ) (n n' : ℕ) (f g : Rul Xo c), Dom a n → Dom a' n' → f ∈ cusp Xo c U a n →
    g ∈ cusp Xo c U a' n' → mulC Xo c f g ∈ cusp Xo c U (a + a') (n + n')

set_option maxSynthPendingDepth 1 in
def CuspFD : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → FiniteDimensional c.F (cusp Xo c U a n)

end Formalism.L2.Pj
end
end
