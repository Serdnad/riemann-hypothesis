module

public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle032
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle033
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle016
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle017
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle029
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

noncomputable section

namespace Formalism.L2.Pj

open scoped TensorProduct
open MeasureTheory
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem pnorm_of_eq_zero (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) (h : P x = 0) :
    X.pnorm la P x = 0 := by
  unfold Data.pnorm
  rw [h, norm_zero, zero_mul]

end Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

variable {Xo c}

variable {D : D7} (σ : c.F →+* ℂ) (V : HSp D) (dict : GA D V → Σ k, Frame ((U σ).X k).Ψ r) (mu : GA D V → ℂ)

def AdelMeas : Prop :=
  ∀ (la : ∀ k, Wt ((U σ).X k).Ψ r) (P : FDSec (U σ).X), IsHolCusp (U σ).X la P →
    AEStronglyMeasurable (onQ V (adel V dict mu P)) (muQ1 V)

def AeDom : Prop :=
  ∀ (la : ∀ k, Wt ((U σ).X k).Ψ r) (P : FDSec (U σ).X), P ∈ holSub (U σ).X la →
    onQ V (adel V dict mu P) =ᵐ[muQ1 V] 0 → ∀ k, ∀ x ∈ ((U σ).X k).dom, P k x = 0

variable {U σ V dict mu}

theorem aesm_of_holSub (hm : AdelMeas U σ V dict mu) (la : ∀ k, Wt ((U σ).X k).Ψ r) {P : FDSec (U σ).X}
    (hP : P ∈ holSub (U σ).X la) : AEStronglyMeasurable (onQ V (adel V dict mu P)) (muQ1 V) := by
  induction hP using Submodule.span_induction with
  | mem P hP => exact hm la P hP
  | zero => rw [map_zero, map_zero]; exact aestronglyMeasurable_const
  | add P Q _ _ h1 h2 => rw [map_add (f := _), map_add (f := _)]; exact h1.add h2
  | smul a P _ h1 => rw [map_smul, map_smul]; exact h1.const_smul a

theorem cusp_L2_of_measurable (hσ : GoodEmb c σ) (hd : ∀ g, (dict g).2 ∈ ((U σ).X (dict g).1).dom)
    (hmu : MuUnit V dict mu) (hm : AdelMeas U σ V dict mu) : CuspL2 U σ V dict mu := by
  intro a n _ f
  have hhol : rdU (U σ) (f : Rul Xo c) ∈ holSub (U σ).X (laU (U σ) a n) :=
    ((mem_cusp Xo c U a n f).1 f.2).2 σ hσ
  have hfin := supE_cusp_ne_top hσ f.2
  show MemLp (onQ V (adel V dict mu (rdU (U σ) (f : Rul Xo c)))) 2 (muQ1 V)
  refine MemLp.of_bound (aesm_of_holSub hm _ hhol) (supN (U σ).X (laU (U σ) a n) (rdU (U σ) (f : Rul Xo c)))
    (Filter.Eventually.of_forall fun q => ?_)
  set g := q.out
  show ‖mu g * rdU (U σ) (f : Rul Xo c) (dict g).1 (dict g).2‖ ≤ _
  rw [norm_mul, hmu.2.1 g, one_mul, ← pnorm_eq_of_unit ((U σ).X (dict g).1) (laU (U σ) a n (dict g).1)
    (rdU (U σ) (f : Rul Xo c) (dict g).1) (dict g).2 (hmu.2.2.2 g)]
  show _ ≤ (supE (U σ).X (laU (U σ) a n) (rdU (U σ) (f : Rul Xo c))).toReal
  rw [← ENNReal.ofReal_le_iff_le_toReal hfin]
  exact le_iSup (fun p : FPt (U σ).X => ENNReal.ofReal (((U σ).X p.1).pnorm (laU (U σ) a n p.1)
    (rdU (U σ) (f : Rul Xo c) p.1) p.2)) ⟨(dict g).1, ⟨(dict g).2, hd g⟩⟩

theorem l2Def_of_cusp (hσ : GoodEmb c σ) (hsup : SupDef Xo c U) (hae : AeDom U σ V dict mu)
    (h : CuspL2 U σ V dict mu) : L2DefiniteCuspForms U σ V dict mu h := by
  set_option synthInstance.maxHeartbeats 200000 in
    intro a n hdom f h0
    have hhol : rdU (U σ) (f : Rul Xo c) ∈ holSub (U σ).X (laU (U σ) a n) :=
      ((mem_cusp Xo c U a n f).1 f.2).2 σ hσ
    have hz : (h a n hdom f).toLp _ = 0 := norm_eq_zero.1 h0
    have hz' : jFn V σ (rdC U σ a n) dict mu f =ᵐ[muQ1 V] 0 :=
      (MemLp.coeFn_toLp (h a n hdom f)).symm.trans (Lp.eq_zero_iff_ae_eq_zero.1 hz)
    have hv := hae (laU (U σ) a n) (rdU (U σ) (f : Rul Xo c)) hhol hz'
    have hE : supE (U σ).X (laU (U σ) a n) (rdU (U σ) (f : Rul Xo c)) = 0 := by
      refine le_antisymm (iSup_le fun p => ?_) zero_le
      rw [pnorm_of_eq_zero _ _ _ _ (hv p.1 p.2 p.2.2), ENNReal.ofReal_zero]
    have hN : supN (U σ).X (laU (U σ) a n) (rdU (U σ) (f : Rul Xo c)) = 0 := by
      unfold supN
      rw [hE, ENNReal.toReal_zero]
    exact Subtype.ext (hsup a n hdom σ hσ f f.2 hN)

theorem dict_dom_of {Comp : Type} {X : Comp → Data E r} {V : HSp D} {dict : GA D V → Σ k, Frame (X k).Ψ r}
    {Kf : Subgroup (GA D V)} {th} {hr}
    (h : DictIsUnif V dict Kf th hr) : ∀ g, (dict g).2 ∈ (X (dict g).1).dom :=
  h.2.2.2.1

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.PjFree

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

section Sections

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}

end Sections

section Unif

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

def Unf.ofPj (U : Formalism.L2.Pj.Unf Xo c σ r) : Unf Xo c σ r :=
  { Comp := U.Comp, fin := U.fin, X := U.X, un := U.un }

def Unf.toPj (U : Unf Xo c σ r) : Formalism.L2.Pj.Unf Xo c σ r :=
  { Comp := U.Comp, fin := U.fin, X := U.X, un := U.un }

theorem rdU_ofPj (U : Formalism.L2.Pj.Unf Xo c σ r) (f : Formalism.L2.Pj.Rul Xo c) : rdU (Unf.ofPj U) f = Formalism.L2.Pj.rdU U f := rfl

theorem laU_ofPj (U : Formalism.L2.Pj.Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (k : U.Comp) :
    laU (Unf.ofPj U) a n k = Formalism.L2.Pj.laU U a n k := rfl

theorem isUnf_ofPj (U : Formalism.L2.Pj.Unf Xo c σ r) : IsUnf (Unf.ofPj U) ↔ Formalism.L2.Pj.IsUnf U := by rfl

theorem goodEmb_iff (σ : c.F →+* ℂ) : GoodEmb c σ ↔ Formalism.L2.Pj.GoodEmb c σ := by rfl

variable (U : ∀ σ : c.F →+* ℂ, Formalism.L2.Pj.Unf Xo c σ r)

theorem cusp_ofPj (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    cusp Xo c (fun σ => Unf.ofPj (U σ)) a n = Formalism.L2.Pj.cusp Xo c U a n := rfl

theorem cuspMul_ofPj : CuspMul Xo c (fun σ => Unf.ofPj (U σ)) ↔ Formalism.L2.Pj.CuspMul Xo c U := by rfl

theorem cuspFD_ofPj : CuspFD Xo c (fun σ => Unf.ofPj (U σ)) ↔ Formalism.L2.Pj.CuspFD Xo c U := by rfl

theorem supDef_ofPj : SupDef Xo c (fun σ => Unf.ofPj (U σ)) ↔ Formalism.L2.Pj.SupDef Xo c U := by rfl

theorem regP_ofPj : regular₂ Xo c (fun σ => Unf.ofPj (U σ)) ↔ Formalism.L2.Pj.regular₂ Xo c U := by rfl

end Unif

section Points

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l) (cls : ∀ (T : Formalism.L2.Pj.CDVR) (ι : c.F →+* T.Fr), Formalism.L2.Pj.IntFr Xo c T ι → Prop)

end Points

section Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} {r : ℕ}

end Frames

end Formalism.L2.PjFree
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [Fintype (Comp Xo c)]

theorem extVal_unit_zero (T : CDVR) (u : T.Vˣ) : vV T.V (algebraMap T.V T.Fr (u : T.V)) = 0 := by
  have h1 : valV T.V (algebraMap T.V T.Fr (u : T.V)) = 1 := by
    apply le_antisymm ((IsDiscreteValuationRing.maximalIdeal T.V).valuation_le_one _)
    have h2 := (IsDiscreteValuationRing.maximalIdeal T.V).valuation_le_one (R := T.V) (K := T.Fr) ((u⁻¹ : T.Vˣ) : T.V)
    have h3 : valV T.V (algebraMap T.V T.Fr (u : T.V)) * valV T.V (algebraMap T.V T.Fr ((u⁻¹ : T.Vˣ) : T.V)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    by_contra hlt
    rw [not_le] at hlt
    have : valV T.V (algebraMap T.V T.Fr (u : T.V)) * valV T.V (algebraMap T.V T.Fr ((u⁻¹ : T.Vˣ) : T.V)) < 1 :=
      mul_lt_one_of_lt_of_le hlt h2
    rw [h3] at this
    exact lt_irrefl _ this
  simp [vV, h1]

def OrdTieQZ (h : GenFrEx Xo c) (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ) : Prop :=
  ∀ (Z : Comp Xo c) (v : AddValuation (Om Z) (WithTop ℤ)), IsNormDiscrete v → IsTrivOn c.F v →
    ∃ q : QPt Xo c,
      (∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n → evC h Z f ≠ 0 →
        (((ordC (δ Z v) v (wtZ a n) (valC h a n f Z) : ℤ) : ℝ) : EReal) = ordQ Xo c q f) ∧
      ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n → evC h Z f = 0 → ordQ Xo c q f = ⊤

theorem height_F1_of_data (h : GenFrEx Xo c)
    (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))
    (Dd N T i g0 : ℕ) (cc : ℝ) (uL uF uka ude uet uta1 uta2 : WtR E)
    (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1))
    (np : ℕ) (thpR : Fin np → Rul Xo c) (n0 : ℕ) (th0R : Fin n0 → Rul Xo c) (uF0 : WtR E)
    (nk : ℕ) (thkR : Fin nk → Rul Xo c) (MR : Set (Rul Xo c)) (etR ta1R ta2R : Rul Xo c)
    (nu : IsDedekindDomain.HeightOneSpectrum (𝓞 c.F) → ℝ)
    (ip : (c.F →+* ℂ) → (∀ Z : Comp Xo c, AC Z) → (∀ Z : Comp Xo c, AC Z) → ℂ)
    (wsize : WTZ E → ℝ) (DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r : ℝ)
    {rU : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ rU)
    (hreg : regular₂ Xo c U) (htie : OrdTieQZ h δ)
    (hdL : Dom uL.1 uL.2) (hdE : Dom uet.1 uet.2)
    (hws : ∀ k, wR k ∈ cusp Xo c U uL.1 uL.2) (het : etR ∈ cusp Xo c U uet.1 uet.2)
    (hnz : NoCommonZero Xo c wR) (hnzet : NZAt h etR)
    (huet : wtZ uet.1 uet.2 = (i * g0) • wtZ ude.1 ude.2) (hcc : 0 ≤ cc)
    (nuA : HeightOneSpectrum (𝓞 c.F) → ℝ)
    (halg : ∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v etR ∧
      (v etR ≠ ⊤ → (⨅ k, v (wR k)) ≤ (nuA la : EReal) + ((cc / (2 * i) : ℝ) : EReal) * v etR)) :
    (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).TrivialPlaceHyp := by
  classical
  have hc' : (0 : ℝ) ≤ cc / (2 * i) := div_nonneg hcc (by positivity)

  have hR2 := (hreg.1.2 ⟨uL, hdL⟩ ⟨uet, hdE⟩ (N + 1) (fun k => ⟨wR k, hws k⟩) ⟨etR, het⟩ nuA (cc / (2 * i)) hc'
    hnz (fun la y => halg la y.1 y.2)).2
  unfold Data.TrivialPlaceHyp
  intro Z v hAdm hTv
  obtain ⟨q, hq1, hq0⟩ := htie Z v hAdm.1 hTv

  have hqT : (fun f => ordQ Xo c q f) ∈ trivSet Xo c := by
    refine ⟨q.T, q.ι, q.y, fun a ha => ?_, rfl⟩
    obtain ⟨u, hu⟩ := q.triv a ha
    rw [← hu]
    exact extVal_unit_zero q.T u
  obtain ⟨hE0, hEb⟩ := hR2 ⟨_, hqT⟩
  dsimp only [dataOf, Data.n1] at *
  rw [← huet]
  have hEq : (((ordC (δ Z v) v (wtZ uet.1 uet.2) (valC h uet.1 uet.2 etR Z) : ℤ) : ℝ) : EReal) = ordQ Xo c q etR :=
    hq1 uet.1 uet.2 etR (cusp_le_sec Xo c U _ _ het) (hnzet Z)
  have hEne : ordQ Xo c q etR ≠ ⊤ := by rw [← hEq]; exact EReal.coe_ne_top _
  have hb := hEb hEne
  obtain ⟨k0, hk0⟩ := exists_eq_ciInf_of_finite (f := fun k : Fin (N + 1) => ordQ Xo c q (wR k))
  have hk0le : ordQ Xo c q (wR k0) ≤ ((cc / (2 * i) : ℝ) : EReal) * ordQ Xo c q etR := by
    rw [hk0]; exact hb
  have hev : evC h Z (wR k0) ≠ 0 := by
    intro h0
    rw [hq0 uL.1 uL.2 (wR k0) (cusp_le_sec Xo c U _ _ (hws k0)) h0, ← hEq, ← EReal.coe_mul] at hk0le
    exact EReal.coe_ne_top _ (top_le_iff.1 hk0le)
  have hval : valC h uL.1 uL.2 (wR k0) Z ≠ 0 := valC_ne_zero hev
  have hk0' := hq1 uL.1 uL.2 (wR k0) (cusp_le_sec Xo c U _ _ (hws k0)) hev
  rw [← hk0', ← hEq, ← EReal.coe_mul, EReal.coe_le_coe_iff] at hk0le
  have hle : (⨅ j : {j // valC h uL.1 uL.2 (wR j) Z ≠ 0}, ordC (δ Z v) v (wtZ uL.1 uL.2) (valC h uL.1 uL.2 (wR j) Z)) ≤
      ordC (δ Z v) v (wtZ uL.1 uL.2) (valC h uL.1 uL.2 (wR k0) Z) :=
    ciInf_le (Set.finite_range _).bddBelow (⟨k0, hval⟩ : {j // valC h uL.1 uL.2 (wR j) Z ≠ 0})
  have hle' : ((⨅ j : {j // valC h uL.1 uL.2 (wR j) Z ≠ 0}, ordC (δ Z v) v (wtZ uL.1 uL.2)
      (valC h uL.1 uL.2 (wR j) Z) : ℤ) : ℝ) ≤ (ordC (δ Z v) v (wtZ uL.1 uL.2) (valC h uL.1 uL.2 (wR k0) Z) : ℝ) := by
    exact_mod_cast hle
  exact hle'.trans hk0le

end Formalism.L2.Pj
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD NumberField
open MvPolynomial Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

def thLaValAt (nab : NabV Xo c) {n : ℕ} (w : (Fin n → LevQ Dw l) → c.F) (La : GenLat E n) (N : ℕ)
    (P : MvPolynomial (LtN Dw n) c.F) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : S) : Prop :=
  ShortValAt Xo c nab w La 1 N P y v

abbrev LevQc (Dw : Datum H) (l : Level H) : Type := Dw.La ⧸ (Mfr l • ⊤ : Submodule (𝓞 E) Dw.La)

def phiHat {n : ℕ} (φ : (Fin n → LevQc Dw l) → c.F) : (Fin n → LevQ Dw l) → c.F :=
  fun q => ∑ᶠ x : Fin n → LevQc Dw l, φ x * zetaM c ^ pairL (l := l) (fun b => qRep (x b)) (fun b => levRep (q b))

def indPhi {n : ℕ} (x0 : Fin n → LevQc Dw l) : (Fin n → LevQc Dw l) → c.F :=
  open Classical in fun x => if x = x0 then 1 else 0

section Cls

variable {n : ℕ} {Cl : Type} [Fintype Cl] {Vs : Type} [AddCommGroup Vs] [Module c.F Vs]

def ThClsValAt (nab : NabV Xo c) (w : Cl → (Fin n → LevQ Dw l) → c.F) (La : Cl → GenLat E n) (Nc : Cl → ℕ)
    (gam : Cl → ℕ) (vol : c.F) (ep : Cl → c.F) (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (xi : Rul Xo c) (x : Cl → Vs)
    {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : S) : Prop :=
  ∃ vc : Cl → S, (∀ k, thLaValAt Xo c nab (w k) (La k) (Nc k) (io (x k)) y (vc k)) ∧
    v = evR Xo c xi y * ∑ k, algebraMap c.F S (vol * ((gam k : c.F))⁻¹ * ep k) * vc k

def GenLat.SplitSupp (H : Host E) (Λ : GenLat E n) : Prop :=
  ∃ m : 𝓞 E, m ≠ 0 ∧ Ideal.span {m} • Λ.La ≤ stdLat E n ∧ Ideal.span {m} • stdLat E n ≤ Λ.La ∧
    ∀ P : Ideal (𝓞 E), P.IsPrime → m ∈ P → P.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ P

def RepsOK (bad : ℕ) (La : Cl → GenLat E n) (Nc : Cl → ℕ) (gam : Cl → ℕ) : Prop :=
  ∀ k, (La k).Unimod ∧ (La k).TrivAt bad ∧ (La k).TrivAt l.M ∧ (La k).LevOK (Nc k) l.M ∧ 0 < gam k ∧
    GenLat.SplitSupp H (La k)

end Cls

def gaStar {n : ℕ} (ga : Matrix (Fin n) (Fin n) E) : MvPolynomial (LtN Dw n) c.F →ₐ[c.F] MvPolynomial (LtN Dw n) c.F :=
  aeval fun ℓ => letB (Dw := Dw) c ℓ.1 ℓ.2.1 (fun j => ga j ℓ.2.2)

def minorPolynomial {n : ℕ} (σ : E →+* ℂ) (i : ℕ) (hi : i < Dw.mult σ) (col : Fin (i + 1) → Fin n) :
    MvPolynomial (LtN Dw n) c.F :=
  Matrix.det (Matrix.of fun s b : Fin (i + 1) => X (⟨σ, ⟨s.val, by omega⟩, col b⟩ : LtN Dw n))

def aStep (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (σ : E →+* ℂ) (i : ℕ) : ℕ :=
  a (σ, i) - (if i + 1 < Dw.mult σ then a (σ, i + 1) else 0)


open Classical in
def pG (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : MvPolynomial (LtN Dw n) c.F :=
  ∏ σ : E →+* ℂ, ∏ i : Fin (Dw.mult σ),
    (if h : i.val + 1 ≤ n then
      (if InPsi H σ then minorPolynomial c σ i.val i.isLt (Fin.castLE h)
        else minorPolynomial c σ i.val i.isLt (fun b => Fin.cast (by omega) (Fin.natAdd (n - (i.val + 1)) b)))
      else 0) ^ aStep Dw a σ i.val

def idlE (I : Ideal (𝓞 E)) : Submodule (𝓞 E) E := Submodule.map (Algebra.linearMap (𝓞 E) E) I

def EpIs {n : ℕ} (bad : ℕ) (B : Ideal (𝓞 E) → c.F) (epF : Submodule (𝓞 E) (Fin n → E) → c.F) : Prop :=
  ∀ (L : Submodule (𝓞 E) (Fin n → E)) (cc : Ideal (𝓞 E)),
    (⟨L⟩ : GenLat E n).Unimod → (⟨L⟩ : GenLat E n).TrivAt bad → GenLat.SplitSupp H (⟨L⟩ : GenLat E n) →
    cc ⊔ cc.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ →
    Submodule.span (𝓞 E) (detSet L) * idlE (cc.map (H.bar : 𝓞 E →+* 𝓞 E)) = idlE cc →
    ∃ q : ℚ, 0 < q ∧
      q ^ 2 * (((L ⊓ stdLat E n).toAddSubgroup.addSubgroupOf L.toAddSubgroup).index : ℚ) ^ (Dw.p + Dw.q) =
        (Ideal.absNorm cc : ℚ) ∧
      epF L = (B cc)⁻¹ * (q : c.F)

section Io

variable {n : ℕ} {Vs : Type} [AddCommGroup Vs] [Module c.F Vs] [Module (𝓞 c.F) Vs] [IsScalarTower (𝓞 c.F) c.F Vs]

def IoLF (a : (E →+* ℂ) × ℕ → ℕ) (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F)
    (rho : Matrix (Fin n) (Fin n) E → Vs →ₗ[c.F] Vs) (cga : Matrix (Fin n) (Fin n) E → c.F)
    (nab0 : Submodule (𝓞 c.F) Vs) (hw : Vs) (pG : MvPolynomial (LtN Dw n) c.F) : Prop :=
  Dw.p + Dw.q ≤ n ∧ Function.Injective io ∧
  LinearMap.range io = Submodule.span c.F (HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H)
    (fun τ i => a (τ, i))) ∧
  (∀ ga : Matrix (Fin n) (Fin n) E, ga.conjTranspose * ga = 1 → ∀ v, io (rho ga v) = cga ga • gaStar c (ga.map (IsCMField.complexConj E)) (io v)) ∧
  hw ∈ nab0 ∧ (∀ s : c.F, s • hw ∈ nab0 → ∃ o : 𝓞 c.F, s = (o : c.F)) ∧ io hw = pG ∧
  harmA (Dw := Dw) c a n ⊆ io '' (nab0 : Set Vs)

def LatPin {Cl : Type} (Lh : Cl → Submodule (𝓞 E) (Fin n → E)) (La : Cl → GenLat E n) : Prop :=
  ∀ k (v : Fin n → E), v ∈ (La k).La ↔ (fun j => IsCMField.complexConj E (v j)) ∈ Lh k

end Io

section Ep

variable {n : ℕ} {Cl : Type}

end Ep

section Row

variable {n : ℕ} {Cl : Type} [Fintype Cl] {Vs : Type} [AddCommGroup Vs] [Module c.F Vs]

def OneMod {n : ℕ} (lev : ℕ) (ga : Matrix (Fin n) (Fin n) E) : Prop :=
  ∃ k : ℕ, Nat.Coprime k lev ∧ ∀ i j, ∃ o : 𝓞 E, (k : E) * (ga - 1) i j = (lev : E) * (o : E)

def IsThClsD (dδ : DeltaDat Xo c n) (w : Cl → (Fin n → LevQ Dw dδ.l₂) → c.F) (La : Cl → GenLat E n) (Nc : Cl → ℕ)
    (gam : Cl → ℕ) (vol : c.F) (ep : Cl → c.F) (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (x : Cl → Vs)
    (f : Rul Xo c) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra dδ.c₂.F k],
    (∀ a : c.F, algebraMap dδ.c₂.F k (dδ.eF a) = algebraMap c.F k a) →
    ∀ (y : FrPt Xo c k) (y₂ : FrPt dδ.Xo₂ dδ.c₂ k), FrOver dδ y₂ y →
      ∃ vc : Cl → k, (∀ cl, thLaValAt dδ.Xo₂ dδ.c₂ dδ.nab₂ (fun q => dδ.eF (w cl q)) (La cl) (Nc cl)
          (MvPolynomial.map (dδ.eF : c.F →+* dδ.c₂.F) (io (x cl))) y₂ (vc cl)) ∧
        evR Xo c f y = evR dδ.Xo₂ dδ.c₂ dδ.cδ y₂ *
          ∑ cl, algebraMap c.F k (vol * ((gam cl : c.F))⁻¹ * ep cl) * vc cl

def OneMapRow {D : D7} (V : HSp D) {σ0 : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ0 r)
    (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (mu : GA D V → ℂ) (xr : ℝ) (a : (E →+* ℂ) × ℕ → ℕ)
    {G : Type} [Group G] (act : G → Rul Xo c →ₗ[c.F] Rul Xo c) {Tup : Type*} (dδ : Tup → DeltaDat Xo c n)
    (Cl' : Tup → Type) [∀ t, Fintype (Cl' t)]
    (w : ∀ t, Cl' t → (Fin n → LevQ Dw (dδ t).l₂) → c.F) (La : ∀ t, Cl' t → GenLat E n) (Nc : ∀ t, Cl' t → ℕ)
    (gam : ∀ t, Cl' t → ℕ) (vol : Tup → c.F) (ep : ∀ t, Cl' t → c.F) (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F)
    (thAd : ∀ t, (Cl' t → Vs) → (AutQ V → ℂ)) (Pl : ∀ t, (Cl' t → Vs) → Prop) (LL : IntermediateField ℚ ℂ)
    (Cu : Submodule c.F (Rul Xo c)) (cc : U.Comp → ℂ) (ph : ℂ) : Prop :=
  (∀ k, ‖cc k‖ = 1) ∧ ‖ph‖ = 1 ∧ ∃ z : G, z ∈ Subgroup.center G ∧
    ∀ t : Tup, ∃ ze : ℂ, ze ∈ LL ∧ (∃ m : ℕ, 0 < m ∧ ze ^ m = 1) ∧ ∀ x : Cl' t → Vs, Pl t x →
      (∃ f ∈ Cu, IsThClsD Xo c (dδ t) (w t) (La t) (Nc t) (gam t) (vol t) (ep t) io x f) ∧
      (∀ f ∈ sec Xo c a n, IsThClsD Xo c (dδ t) (w t) (La t) (Nc t) (gam t) (vol t) (ep t) io x f →
        ∀ q : AutQ V, ph * thAd t x q =
          ze * cc (dict q.out).1 * (lieFac Dw xr a : ℂ) * jFn V σ0 (rdU U) dict mu (act z f) q)

end Row

end Formalism.L2.Pj
end
end
