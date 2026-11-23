module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle034
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle035
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle021
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle020
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.NotOverAndTriv
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsFrameShiftFrShFin
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle014
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle029
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle073
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle080
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AlgebraicLawsModuliSchemeGoodLevel
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle093
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle089
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle120
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle085
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle019
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle090
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt

@[expose] public section

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.HeightTop.Ties

section

open ReciprocityTheory.ChartRestriction.G.T0 GlobalTheory.Height.OrderTieGuards

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem ordTieOn_of_valued {h : GenFrEx Xo c} {δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ}
    {PY : HeightOneSpectrum (𝓞 c.F) → Type}
    {lies : ∀ la (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → PY la → Prop}
    (hl : LiesTotal Xo c (trivialClassCondition Xo c) PY lies)
    (hv : ∀ (Z : Comp Xo c) (v : AddValuation (Om Z) (WithTop ℤ)), IsNormDiscrete v →
      ((∃ la, IsOver (K := c.F) v la) ∨ IsTrivOn c.F v) →
      ∃ (T : CDVR) (ψ : Om Z →+* T.Fr) (y : IntFr Xo c T (ψ.comp (algebraMap c.F (Om Z)))),
        (∀ a : Om Z, a ≠ 0 → ((vV T.V (ψ a) : ℤ) : WithTop ℤ) = v a) ∧
        ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n → (evI y f = 0 ↔ evC h Z f = 0) ∧
          (evC h Z f ≠ 0 → ordC (δ Z v) v (wtZ a n) (valC h a n f Z) = vV T.V (evI y f))) :
    OrdTieOn h δ (trivialClassCondition Xo c) PY lies := by
  intro Z v la hd ho
  obtain ⟨T, ψ, y, hψ, hy⟩ := hv Z v hd (Or.inl ⟨la, ho⟩)
  obtain ⟨hpos, hres⟩ := restrict_eq hd ho
  obtain ⟨e, he⟩ := Int.eq_ofNat_of_zero_le hpos.le
  have he0 : 0 < e := by omega
  have hO : OverLa la T.V (ψ.comp (algebraMap c.F (Om Z))) e := by
    refine ⟨he0, fun a => ?_⟩
    by_cases ha : a = 0
    · subst ha; simp [vV, vLa]
    · have := (hψ _ ((map_ne_zero (algebraMap c.F (Om Z))).2 ha)).trans (hres a ha)
      rw [he] at this
      exact_mod_cast this
  obtain ⟨η, hη⟩ := hl la T _ e hO y trivial
  refine ⟨PtV.mk la hO y trivial η hη, fun a n f hf h0 => ?_, fun a n f hf h0 _ => ?_⟩
  · change _ = _ * nval T.V e (evI y f)
    rw [nval_of_ne (fun hz => h0 ((hy a n f hf).1.1 hz)), (hy a n f hf).2 h0, he, ← EReal.coe_mul,
      EReal.coe_eq_coe_iff]
    have : (e : ℝ) ≠ 0 := by exact_mod_cast he0.ne'
    push_cast
    field_simp
  · change nval T.V e (evI y f) = ⊤
    rw [(hy a n f hf).1.2 h0, nval_zero]

end

theorem exists_unit_of_vV_eq_zero (T : CDVR) {x : T.Fr} (hx : x ≠ 0) (h0 : vV T.V x = 0) :
    ∃ u : T.Vˣ, algebraMap T.V T.Fr (u : T.V) = x := by
  have hne : valV T.V x ≠ 0 := valV_ne_zero hx
  have h1 : valV T.V x = 1 := by
    have h2 : WithZero.log (valV T.V x) = 0 := by simpa [vV] using h0
    rw [← WithZero.exp_log hne, h2, WithZero.exp_zero]
  obtain ⟨z, hz⟩ : ∃ z : T.V, algebraMap T.V T.Fr z = x := by
    obtain ⟨z, hz | hz⟩ := ValuationRing.isInteger_or_isInteger T.V x |>.elim
      (fun ⟨z, hz⟩ => (⟨z, Or.inl hz⟩ : ∃ z : T.V, algebraMap T.V T.Fr z = x ∨ algebraMap T.V T.Fr z = x⁻¹))
      (fun ⟨z, hz⟩ => ⟨z, Or.inr hz⟩)
    · exact ⟨z, hz⟩
    · have hz1 : (IsDiscreteValuationRing.maximalIdeal T.V).valuation T.Fr (algebraMap T.V T.Fr z) = 1 := by
        rw [hz, map_inv₀]
        change (valV T.V x)⁻¹ = 1
        rw [h1, inv_one]
      have hzn := (HeightOneSpectrum.valuation_eq_one_iff_notMem _).1 hz1
      have hu : IsUnit z := by
        by_contra hn
        exact hzn ((IsLocalRing.mem_maximalIdeal z).2 hn)
      obtain ⟨u, rfl⟩ := hu
      refine ⟨(u⁻¹ : T.Vˣ), ?_⟩
      rw [map_units_inv, hz, inv_inv]
  have hz1 : (IsDiscreteValuationRing.maximalIdeal T.V).valuation T.Fr (algebraMap T.V T.Fr z) = 1 := by
    rw [hz]; exact h1
  have hzn := (HeightOneSpectrum.valuation_eq_one_iff_notMem _).1 hz1
  have hu : IsUnit z := by
    by_contra hn
    exact hzn ((IsLocalRing.mem_maximalIdeal z).2 hn)
  obtain ⟨u, rfl⟩ := hu
  exact ⟨u, hz⟩

theorem exists_frameShift_ordTies : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → l.A = 1 → ∀ [Fintype (Comp Xo c)] (h : GenFrEx Xo c), ∃ δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ, OrdTieQ h δ ∧ OrdTieQZ h δ ∧ (∀ (PY : HeightOneSpectrum (𝓞 c.F) → Type) (lies : ∀ la (T' : CDVR) (ι : c.F →+* T'.Fr), IntFr Xo c T' ι → PY la → Prop), LiesTotal Xo c (trivialClassCondition Xo c) PY lies → OrdTieOn h δ (trivialClassCondition Xo c) PY lies ∧ OrdTie h δ (trivialClassCondition Xo c) PY lies) ∧ ∀ d : ReciprocityTheory.ChartRestriction.G.T0.Data c.F (Comp Xo c) (fun Z => Om Z) (WTZ E) (fun Z => AC Z), DivFin d → FrShFin d δ := by
  intro E _ _ _ H Dw l Xo c hpq hgood hA _ h
  obtain ⟨δ, hv, hfin⟩ := exists_frameShift_frShFin E H Dw l Xo c hpq hgood hA h
  have hQZ : OrdTieQZ h δ := by
    intro Z v hd ht
    obtain ⟨T, ψ, y, hψ, hy⟩ := hv Z v hd (Or.inr ht)
    have htriv : trivCls Xo c T _ y := by
      intro a ha
      have ha' : algebraMap c.F (Om Z) a ≠ 0 := (map_ne_zero _).2 ha
      refine exists_unit_of_vV_eq_zero T ((map_ne_zero _).2 ha) ?_
      have := (hψ _ ha').trans (ht a ha)
      exact_mod_cast this
    refine ⟨⟨T, _, y, htriv⟩, fun a n f hf h0 => ?_, fun a n f hf h0 => ?_⟩
    · change _ = nval T.V 1 (evI y f)
      rw [nval_of_ne (fun hz => h0 ((hy a n f hf).1.1 hz)), (hy a n f hf).2 h0]
      simp
    · change nval T.V 1 (evI y f) = ⊤
      rw [(hy a n f hf).1.2 h0, nval_zero]
  refine ⟨δ, fun Z v hd ht => ?_, hQZ, fun PY lies hl => ?_, fun d hD => hfin d hD⟩
  · obtain ⟨q, hq, -⟩ := hQZ Z v hd ht
    exact ⟨q, hq⟩
  · have hOn := ordTieOn_of_valued hl hv
    exact ⟨hOn, hOn.ordTie⟩

theorem ordTies_of_pins : ∀ (D : D7) (Q : Par D), Q.Pins → ∀ j, InR D j → ∀ [Fintype (Comp (Q.Xo j) Q.c)] (h : GenFrEx (Q.Xo j) Q.c), KapFG (Q.Xo j) Q.c ∧ (∃ d, KapTrdeg (Q.Xo j) Q.c d ∧ d + Nat.card (FlagVar (Q.Dw j)) = WeightFamilies.dimY D j) ∧ FnTrdeg (Q.Xo j) Q.c (WeightFamilies.dimY D j) ∧ CompNe (Q.Xo j) Q.c ∧ ∃ δ : ∀ Z : Comp (Q.Xo j) Q.c, AddValuation (Om Z) (WithTop ℤ) → Ix (Q.Dw j) → ℤ, OrdTieQ h δ ∧ OrdTieQZ h δ ∧ OrdTieOn h δ (trivialClassCondition (Q.Xo j) Q.c) (fun _ => Unit) (fun _ _ _ _ _ => True) ∧ OrdTie h δ (trivialClassCondition (Q.Xo j) Q.c) (fun _ => Unit) (fun _ _ _ _ _ => True) ∧ ∀ d : ReciprocityTheory.ChartRestriction.G.T0.Data Q.c.F (Comp (Q.Xo j) Q.c) (fun Z => Om Z) (WTZ D.host.E) (fun Z => AC Z), DivFin d → FrShFin d δ := by
  intro D Q hP j hj _ h
  obtain ⟨hgood, hA, -, -, -, -, hrk⟩ := GlobalTheory.PinNum.numerics_of_pins D Q hP
  obtain ⟨hr, hr1, hdim⟩ := hrk j hj
  have h1 : 1 ≤ (Q.Dw j).p + (Q.Dw j).q := hr ▸ hr1
  obtain ⟨hfg, htr⟩ := kap_fg_trdeg _ _ (Q.Dw j) Q.l (Q.Xo j) Q.c
  obtain ⟨δ, hq, hqz, hon, hfin⟩ := exists_frameShift_ordTies _ _ (Q.Dw j) Q.l (Q.Xo j) Q.c h1 hgood hA h
  have hl : LiesTotal (Q.Xo j) Q.c (trivialClassCondition (Q.Xo j) Q.c) (fun _ => Unit) (fun _ _ _ _ _ => True) := by
    unfold LiesTotal
    intros
    exact ⟨(), trivial⟩
  obtain ⟨ho, ht⟩ := hon _ _ hl
  exact ⟨hfg, ⟨_, htr, hdim⟩, hdim ▸ fnTrdeg_of _ _ _ htr,
    (GlobalTheory.GeomIrr.compNe_and_exists_fnAlgClosed _ _ (Q.Dw j) Q.l (Q.Xo j) Q.c h1).1, δ, hq, hqz, ho, ht, hfin⟩

end GlobalTheory.HeightTop.Ties
end

section

noncomputable section

namespace GlobalTheory.HeightDefinite.Ties

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0 Formalism.L2.Pj GlobalTheory.Height.OrderTieGuards

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem ordTieOn_of_valued {h : GenFrEx Xo c} {δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ}
    {PY : HeightOneSpectrum (𝓞 c.F) → Type}
    {lies : ∀ la (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → PY la → Prop}
    (hl : LiesTotal Xo c (trivialClassCondition Xo c) PY lies)
    (hv : ∀ (Z : Comp Xo c) (v : AddValuation (Om Z) (WithTop ℤ)), IsNormDiscrete v →
      ((∃ la, IsOver (K := c.F) v la) ∨ IsTrivOn c.F v) →
      ∃ (T : CDVR) (ψ : Om Z →+* T.Fr) (y : IntFr Xo c T (ψ.comp (algebraMap c.F (Om Z)))),
        (∀ a : Om Z, a ≠ 0 → ((vV T.V (ψ a) : ℤ) : WithTop ℤ) = v a) ∧
        ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n → (evI y f = 0 ↔ evC h Z f = 0) ∧
          (evC h Z f ≠ 0 → ordC (δ Z v) v (wtZ a n) (valC h a n f Z) = vV T.V (evI y f))) :
    OrdTieOn h δ (trivialClassCondition Xo c) PY lies := by
  intro Z v la hd ho
  obtain ⟨T, ψ, y, hψ, hy⟩ := hv Z v hd (Or.inl ⟨la, ho⟩)
  obtain ⟨hpos, hres⟩ := restrict_eq hd ho
  obtain ⟨e, he⟩ := Int.eq_ofNat_of_zero_le hpos.le
  have he0 : 0 < e := by omega
  have hO : OverLa la T.V (ψ.comp (algebraMap c.F (Om Z))) e := by
    refine ⟨he0, fun a => ?_⟩
    by_cases ha : a = 0
    · subst ha; simp [vV, vLa]
    · have := (hψ _ ((map_ne_zero (algebraMap c.F (Om Z))).2 ha)).trans (hres a ha)
      rw [he] at this
      exact_mod_cast this
  obtain ⟨η, hη⟩ := hl la T _ e hO y trivial
  refine ⟨PtV.mk la hO y trivial η hη, fun a n f hf h0 => ?_, fun a n f hf h0 _ => ?_⟩
  · change _ = _ * nval T.V e (evI y f)
    rw [nval_of_ne (fun hz => h0 ((hy a n f hf).1.1 hz)), (hy a n f hf).2 h0, he, ← EReal.coe_mul,
      EReal.coe_eq_coe_iff]
    have : (e : ℝ) ≠ 0 := by exact_mod_cast he0.ne'
    push_cast
    field_simp
  · change nval T.V e (evI y f) = ⊤
    rw [(hy a n f hf).1.2 h0, nval_zero]

end

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

theorem exists_unit_of_vV_eq_zero (T : CDVR) {x : T.Fr} (hx : x ≠ 0) (h0 : vV T.V x = 0) :
    ∃ u : T.Vˣ, algebraMap T.V T.Fr (u : T.V) = x := by
  have hne : valV T.V x ≠ 0 := valV_ne_zero hx
  have h1 : valV T.V x = 1 := by
    have h2 : WithZero.log (valV T.V x) = 0 := by simpa [vV] using h0
    rw [← WithZero.exp_log hne, h2, WithZero.exp_zero]
  obtain ⟨z, hz⟩ : ∃ z : T.V, algebraMap T.V T.Fr z = x := by
    obtain ⟨z, hz | hz⟩ := ValuationRing.isInteger_or_isInteger T.V x |>.elim
      (fun ⟨z, hz⟩ => (⟨z, Or.inl hz⟩ : ∃ z : T.V, algebraMap T.V T.Fr z = x ∨ algebraMap T.V T.Fr z = x⁻¹))
      (fun ⟨z, hz⟩ => ⟨z, Or.inr hz⟩)
    · exact ⟨z, hz⟩
    · have hz1 : (IsDiscreteValuationRing.maximalIdeal T.V).valuation T.Fr (algebraMap T.V T.Fr z) = 1 := by
        rw [hz, map_inv₀]
        change (valV T.V x)⁻¹ = 1
        rw [h1, inv_one]
      have hzn := (HeightOneSpectrum.valuation_eq_one_iff_notMem _).1 hz1
      have hu : IsUnit z := by
        by_contra hn
        exact hzn ((IsLocalRing.mem_maximalIdeal z).2 hn)
      obtain ⟨u, rfl⟩ := hu
      refine ⟨(u⁻¹ : T.Vˣ), ?_⟩
      rw [map_units_inv, hz, inv_inv]
  have hz1 : (IsDiscreteValuationRing.maximalIdeal T.V).valuation T.Fr (algebraMap T.V T.Fr z) = 1 := by
    rw [hz]; exact h1
  have hzn := (HeightOneSpectrum.valuation_eq_one_iff_notMem _).1 hz1
  have hu : IsUnit z := by
    by_contra hn
    exact hzn ((IsLocalRing.mem_maximalIdeal z).2 hn)
  obtain ⟨u, rfl⟩ := hu
  exact ⟨u, hz⟩

theorem exists_frameShift_ordTies : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → l.A = 1 → ∀ [Fintype (Comp Xo c)] (h : GenFrEx Xo c), ∃ δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ, OrdTieQ h δ ∧ OrdTieQZ h δ ∧ (∀ (PY : HeightOneSpectrum (𝓞 c.F) → Type) (lies : ∀ la (T' : CDVR) (ι : c.F →+* T'.Fr), IntFr Xo c T' ι → PY la → Prop), LiesTotal Xo c (trivialClassCondition Xo c) PY lies → OrdTieOn h δ (trivialClassCondition Xo c) PY lies ∧ OrdTie h δ (trivialClassCondition Xo c) PY lies) ∧ ∀ d : ReciprocityTheory.ChartRestriction.G.T0.Data c.F (Comp Xo c) (fun Z => Om Z) (WTZ E) (fun Z => AC Z), DivFin d → FrShFin d δ := by
  intro E _ _ _ H Dw l Xo c hpq hgood hA _ h
  obtain ⟨δ, hv, hfin⟩ := GlobalTheory.Reg.exists_frameShift_frShFin E H Dw l Xo c hpq hgood hA h
  have hQZ : OrdTieQZ h δ := by
    intro Z v hd ht
    obtain ⟨T, ψ, y, hψ, hy⟩ := hv Z v hd (Or.inr ht)
    have htriv : trivCls Xo c T _ y := by
      intro a ha
      have ha' : algebraMap c.F (Om Z) a ≠ 0 := (map_ne_zero _).2 ha
      refine exists_unit_of_vV_eq_zero T ((map_ne_zero _).2 ha) ?_
      have := (hψ _ ha').trans (ht a ha)
      exact_mod_cast this
    refine ⟨⟨T, _, y, htriv⟩, fun a n f hf h0 => ?_, fun a n f hf h0 => ?_⟩
    · change _ = nval T.V 1 (evI y f)
      rw [nval_of_ne (fun hz => h0 ((hy a n f hf).1.1 hz)), (hy a n f hf).2 h0]
      simp
    · change nval T.V 1 (evI y f) = ⊤
      rw [(hy a n f hf).1.2 h0, nval_zero]
  refine ⟨δ, fun Z v hd ht => ?_, hQZ, fun PY lies hl => ?_, fun d hD => hfin d hD⟩
  · obtain ⟨q, hq, -⟩ := hQZ Z v hd ht
    exact ⟨q, hq⟩
  · have hOn := ordTieOn_of_valued hl hv
    exact ⟨hOn, hOn.ordTie⟩

theorem ordTies_of_pins : ∀ (D : D7) (Q : Par D), Q.Pins → ∀ j, InR D j → ∀ [Fintype (Comp (Q.Xo j) Q.c)] (h : GenFrEx (Q.Xo j) Q.c), KapFG (Q.Xo j) Q.c ∧ (∃ d, KapTrdeg (Q.Xo j) Q.c d ∧ d + Nat.card (FlagVar (Q.Dw j)) = WeightFamilies.dimY D j) ∧ FnTrdeg (Q.Xo j) Q.c (WeightFamilies.dimY D j) ∧ CompNe (Q.Xo j) Q.c ∧ ∃ δ : ∀ Z : Comp (Q.Xo j) Q.c, AddValuation (Om Z) (WithTop ℤ) → Ix (Q.Dw j) → ℤ, OrdTieQ h δ ∧ OrdTieQZ h δ ∧ OrdTieOn h δ (trivialClassCondition (Q.Xo j) Q.c) (fun _ => Unit) (fun _ _ _ _ _ => True) ∧ OrdTie h δ (trivialClassCondition (Q.Xo j) Q.c) (fun _ => Unit) (fun _ _ _ _ _ => True) ∧ ∀ d : ReciprocityTheory.ChartRestriction.G.T0.Data Q.c.F (Comp (Q.Xo j) Q.c) (fun Z => Om Z) (WTZ D.host.E) (fun Z => AC Z), DivFin d → FrShFin d δ := by
  intro D Q hP j hj _ h
  obtain ⟨hgood, hA, -, -, -, -, hrk⟩ := GlobalTheory.PinNum.numerics_of_pins D Q hP
  obtain ⟨hr, hr1, hdim⟩ := hrk j hj
  have h1 : 1 ≤ (Q.Dw j).p + (Q.Dw j).q := hr ▸ hr1
  obtain ⟨hfg, htr⟩ := GlobalTheory.Reg.kap_fg_trdeg _ _ (Q.Dw j) Q.l (Q.Xo j) Q.c
  obtain ⟨δ, hq, hqz, hon, hfin⟩ := exists_frameShift_ordTies _ _ (Q.Dw j) Q.l (Q.Xo j) Q.c h1 hgood hA h
  have hl : LiesTotal (Q.Xo j) Q.c (trivialClassCondition (Q.Xo j) Q.c) (fun _ => Unit) (fun _ _ _ _ _ => True) := by
    unfold LiesTotal
    intros
    exact ⟨(), trivial⟩
  obtain ⟨ho, ht⟩ := hon _ _ hl
  exact ⟨hfg, ⟨_, htr, hdim⟩, hdim ▸ fnTrdeg_of _ _ _ htr,
    (GlobalTheory.GeomIrr.compNe_and_exists_fnAlgClosed _ _ (Q.Dw j) Q.l (Q.Xo j) Q.c h1).1, δ, hq, hqz, ho, ht, hfin⟩

end GlobalTheory.HeightDefinite.Ties
end
end

section

noncomputable section

namespace GlobalTheory.FinalJoin2

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.CompRat GlobalTheory.Member
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_coreJ_noVol : ∀ (D : D7) (Q : Par D), Q.Pins → (∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q) → ∀ pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K), (∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (pb k).asIdeal) → Q.l.Mb = ∏ k, (pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) → ∀ chiW : ℕ → (Q.c.F →+* ℂ) → (AE D)ˣ →* Circle, (∀ j, InR D j → ∀ σ, GoodEmb Q.c σ → IsHeckeChar D (chiW j σ) ∧ (∀ a, chiW j σ (idF D a) = 1) ∧ MuConj Q.c.F.val.toRingHom σ (chiW j Q.c.F.val.toRingHom) (chiW j σ)) → ∃ T : CoreJ D, LawsJ T ∧ LawsCore T.toCore ∧ T.pb = pb ∧ T.Q = Q ∧ HEq T.chiW chiW := by
  intro D Q hQ hpq pb hpb hMb chiW hchi
  have hM : Q.l.M = D.host.g 0 * D.host.g 1 := hQ.2.1.1
  choose iota hiota using exists_iotaAll Q hQ
  choose Kf hKf using fun j => (GlobalTheory.T.exists_principalLevel_subgroup_open D (D.sp.W j) Q.l.M).1
  choose U dict mu x₀ hS using fun j σ => exists_pkgAll Q hQ hpq j σ (iota j) (hiota j) (Kf j) (hKf j) (chiW j σ)
    (fun hj hσ => ⟨(hchi j hj σ hσ).1, (hchi j hj σ hσ).2.1⟩)
  have hgood := (GlobalTheory.T.level_good_and_half_eq_prime_product D Q.H Q.l hQ.1.2.1 hM).1
  have hB := fun j => GlobalTheory.T.algebraic_laws_moduli_scheme_good_level D.host.E Q.H (Q.Dw j) Q.l (Q.Xo j) Q.c (hpq j) hgood
  have hF := fun j (hj : InR D j) => ((hB j).2.2.2.2.2 D.R.r (U j)).2.2 fun σ hσ => (hS j σ hj hσ).2.unf
  have hL := fun j (hj : InR D j) σ (hσ : GoodEmb Q.c σ) =>
    GlobalTheory.T.finVol_and_exists_L2DefiniteCuspForms_of_pkgLaws D Q.H (Q.Dw j) Q.l (Q.Xo j) Q.c D.R.r (U j) σ (D.sp.W j) _ _ _ _ (dict j σ) (mu j σ) (x₀ j σ)
      (D.sp.W_sig j) hσ (hF j hj).2 (hS j σ hj hσ).2
  let T : CoreJ D :=
    { Q := Q, U := U, V := fun j _ => D.sp.W j, dict := dict, mu := mu, Kf := fun j _ => Kf j, pb := pb,
      cE := fun _ _ _ => 1, chiW := chiW, x₀ := x₀, iota := iota }
  have h0 : GoodEmb Q.c T.toCore.σ₀ := T.toCore.good_σ₀
  have hLM : LawsM T.toCore :=
    { pins := hQ
      half := ⟨hpb, hMb⟩
      evalWD := fun j _ => (hB j).1
      unf := fun j hj σ hσ => (hS j σ hj hσ).2.unf
      unTest := fun j hj σ hσ => (hS j σ hj hσ).2.unTest
      chiTriv := fun j hj σ hσ _ _ _ k γ _ => (hS j σ hj hσ).2.chi1 k _ γ
      dictU := fun j hj σ hσ => by
        obtain ⟨g, e, F, ik, φ, th, h1, h2, -⟩ := (hS j σ hj hσ).2.dictLaws
        exact ⟨th, _, h1, h2⟩
      spaceW := fun _ _ _ _ => rfl
      levelK := fun j _ _ _ => hM ▸ hKf j
      xiAbs := fun j hj σ hσ => (hL j hj σ hσ).2.1
      muUnit := fun j hj σ hσ => (hS j σ hj hσ).2.muUnit
      muCont := fun j hj σ hσ => (hS j σ hj hσ).2.muCont
      finVol := fun j hj σ hσ => (hL j hj σ hσ).1
      cuspFD := fun j hj => (hF j hj).1
      supDef := fun j hj => (hF j hj).2
      cuspidalL2Subspace := fun j hj σ hσ => (hL j hj σ hσ).2.2.choose
      l2Def := fun j hj σ hσ => (hL j hj σ hσ).2.2.choose_spec
      unitIndep := fun j _ => (hB j).2.1
      ptNe := fun j _ => (hB j).2.2.1 }
  refine ⟨T, ?_, ?_, rfl, rfl, HEq.rfl⟩
  · exact
      { toLawsM := hLM
        cUnit := fun _ _ _ _ _ => norm_one
        muVal := fun j hj σ hσ => (hS j σ hj hσ).2.muVal
        muConj := fun j hj σ hσ => (hchi j hj σ hσ).2.2
        intAll := fun j _ => (hB j).2.2.2.1
        modelW := fun j hj σ hσ => ⟨_, (hS j σ hj hσ).2.modelW⟩
        familyUniformisationBasePointOrthogonal := fun j hj σ hσ => (hS j σ hj hσ).2.familyUniformisationBasePointOrthogonal
        kfHalf := fun j _ _ _ => (GlobalTheory.T.principalLevel_eq_halfMarking_stabilizer D Q.H Q.l (D.sp.W j)).2 (Kf j) (hKf j)
        adPin := fun j hj σ hσ => by
          obtain ⟨g, e, F, ik, φ, th, h1, -, h3⟩ := (hS j σ hj hσ).2.dictLaws
          have hi := hiota j hj (D.sp.W_rank j hj.1 hj.2)
          refine ⟨D.sp.W_rank j hj.1 hj.2, g, e, F, ik, φ, th, hi.emb, ⟨1, fun x y => ?_⟩, h1, h3⟩
          rw [Units.val_one, Int.cast_one, one_mul]
          exact hi.isom x y }
  · exact
      { toLawsM := hLM
        cuspMul := fun j _ => ((hB j).2.2.2.2.2 D.R.r (U j)).2.1
        latZ := fun j hj => ((hS j _ hj h0).2.expo _).1
        cuNe := fun j hj k => by
          obtain ⟨-, h1, h2, h3⟩ := GlobalTheory.T.exists_latticeEmbedding_liftDatum_hermitianSpace D Q hQ j hj
          have hp : (T.toCore.X₀ j k).p0 = (Q.Dw j).q := (hS j _ hj h0).1 k
          exact GlobalTheory.CuspExist.nonempty_cuspFD GlobalTheory.QNorm.hasseNormSt _ _ _ _ (by omega) (by omega) (by omega)
        expo := fun j hj => hM ▸ ((hS j _ hj h0).2.expo _).2 }

end GlobalTheory.FinalJoin2
end
end
