module

public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle044
public import Formalism.LocalToGlobal.ProjectiveLattices.SecPtOrd
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle031
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle015
public import Formalism.LocalToGlobal.ProjectiveLattices.CurveLoc
import Formalism.LocalToGlobal.ProjectiveLattices.CurveCountA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle014
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle042
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtMain
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.CMDeterminantIdeals.DetIdeal
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle034
import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LinkNum
import Formalism.SharpRestriction.Divisibility.WeightAlgebra
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsPowSmulMemBall
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
import Mathlib.Tactic.TypeStar

@[expose] public section

section

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Weights

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

theorem wchar_nsmul {S : Type} [CommRing S] (e : Ix Dw → ℕ) (t : Ix Dw → Sˣ) (k : ℕ) :
    wchar (k • e) t = wchar e t ^ k := by
  unfold wchar
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, mul_comm, pow_mul]

theorem wchar_ne_zero {S : Type} [Field S] (e : Ix Dw → ℕ) (t : Ix Dw → Sˣ) : wchar e t ≠ 0 := by
  unfold wchar
  exact Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (t i).ne_zero

end Weights

variable {D : D7} {T : Top D}

theorem exponent_base_weight_zero (j : ℕ) : ex (T.Q.Dw j) (wtA (wt0 D j)) (wt0 D j).n = 0 := by
  funext i
  cases i <;> simp [ex, wtA, wt0, wscalar, ext0]

theorem ex_addL {j : ℕ} (wL : WeightFamilies.Wt D j) (k : ℕ) :
    ex (T.Q.Dw j) (wtA (addL (wt0 D j) wL k)) (addL (wt0 D j) wL k).n = k • ex (T.Q.Dw j) (wtA wL) wL.n := by
  induction k with
  | zero => rw [addL_zero, exponent_base_weight_zero, zero_smul]
  | succ k ih => rw [← wadd_addL, wtA_wadd, n_wadd, ex_add, ih, succ_nsmul, add_comm]

variable (j : ℕ)

def evIHom {Tc : CDVR} {io : T.Q.c.F →+* Tc.Fr} (y : IntFr (T.Q.Xo j) T.Q.c Tc io) : T.R j →+* Tc.Fr where
  toFun := evI y
  map_one' := by
    letI := io.toAlgebra
    exact evalAt_one _ _ y.1 y.2.1
  map_mul' := evI_mul y
  map_zero' := by
    letI := io.toAlgebra
    exact evalAt_zero _ _ y.1
  map_add' := evI_add y

def chiI {Tc : CDVR} {io : T.Q.c.F →+* Tc.Fr} (y : IntFr (T.Q.Xo j) T.Q.c Tc io) :
    AddMonoidAlgebra (T.R j) (Deg D j) →+* Tc.Fr :=
  AddMonoidAlgebra.liftNCRingHom (evIHom j y) (1 : Multiplicative (Deg D j) →* Tc.Fr) (fun _ _ => Commute.all _ _)

theorem chiI_single {Tc : CDVR} {io : T.Q.c.F →+* Tc.Fr} (y : IntFr (T.Q.Xo j) T.Q.c Tc io) (d : Deg D j) (r : T.R j) :
    chiI j y (AddMonoidAlgebra.single d r) = evI y r := by
  unfold chiI
  rw [AddMonoidAlgebra.liftNCRingHom_single]
  simp only [MonoidHom.one_apply, mul_one]
  rfl

theorem chiI_smul {Tc : CDVR} {io : T.Q.c.F →+* Tc.Fr} (y : IntFr (T.Q.Xo j) T.Q.c Tc io) (a : T.Q.c.F)
    (f : AddMonoidAlgebra (T.R j) (Deg D j)) : chiI j y (a • f) = io a * chiI j y f := by
  refine AddMonoidAlgebra.induction_linear f ?_ ?_ ?_
  · rw [smul_zero, map_zero, mul_zero]
  · intro f g hf hg
    rw [smul_add, map_add (f := _), map_add (f := _), hf, hg, mul_add]
  · intro d r
    rw [show a • AddMonoidAlgebra.single d r = AddMonoidAlgebra.single d (a • r) from AddMonoidAlgebra.smul_single a d r,
      chiI_single, chiI_single, evI_smul]

theorem chiI_inc (h : LawsP T) {Tc : CDVR} {io : T.Q.c.F →+* Tc.Fr} (y : IntFr (T.Q.Xo j) T.Q.c Tc io) (w : WeightFamilies.Wt D j)
    (F : (recB h.toLawsCore).Cusp j w) : chiI j y (incG deg (cutR T.C j) w F) = evI y (F : T.R j) := by
  rw [incG_apply, chiI_single]

section Main

variable {D : D7} {T : Top D}

theorem evR_eq_of_map {j : ℕ}
    (hWD : EvalWD (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z))
    {f : T.R j} (hf : IsNatural (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z) f)
    {S : Type} [CommRing S] [Algebra T.Q.c.F S] (w : FrPt (T.Q.Xo j) T.Q.c S) (p : TRing T.Q.c.F)
    (φ : p.R →ₐ[T.Q.c.F] S) (y : FrPt (T.Q.Xo j) T.Q.c p.R) (h : FrMap φ y w) :
    evR (T.Q.Xo j) T.Q.c f w = φ (f p y) := by
  have hT : FromTest (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z) w := ⟨p, φ, y, h⟩
  unfold evR evalAt
  rw [dite_eq_left hT]
  exact hWD f hf S _ _ _ _ _ _ w hT.choose_spec.choose_spec.choose_spec h

def RealPtNZSt (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO))
    (hU : IsUnif (OsK (recPlus h j hj) la G.w) (unifO (recPlus h j hj) la G.N)) [∀ ζ : PtsG G la, IsDVRAt ζ] : Prop :=
  ∀ ζ : PtsG G la, ∃ (y : (extAll h j hj).Pt' la) (Tc : CDVR) (ι : Loc ζ →+* Tc.V) (_ : IsLocalHom ι)
    (hunr : ∃ ϖ : Loc ζ, Irreducible ϖ ∧ Irreducible (ι ϖ)) (ev : Rp (recPlus h j hj) la G.N →+* Tc.Fr)
    (hu : IsUnit (ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (recPlus h j hj) la G.w 0))),
    (∀ (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w), (extAll h j hj).vAt' la y ((recPJ h j hj).inc w F) =
      nval Tc.V (ep (unifO (recPlus h j hj) la G.N) ζ) (ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F)))) ∧
    (∀ x : ↥(Frac0 (recPlus h j hj) la G.w),
      IsLocalization.Away.lift (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (recPlus h j hj) la G.w 0) hu (x : Lw (recPlus h j hj) la G.w) =
        phiAt ζ Tc.Fr ι hU (addVal_map_of_unr ι hunr) (toOsK (recPlus h j hj) la G.w x)) ∧
    ∀ (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w), NZAt hG (F : T.R j) →
      ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F)) ≠ 0

end Main

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [Fintype (Comp Xo c)]

theorem htConcl_dataOf (h : GenFrEx Xo c)
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
    (hne : CompNe Xo c) (hfg : FnFG Xo c) (htr : FnTrdeg Xo c Dd) (hac : FnAlgClosed (Xo := Xo) (c := c))
    (hwb : ∀ Z, evC h Z (wR (jc Z)) ≠ 0) (het : NZAt h etR) (hta1 : NZAt h ta1R) (hta2 : NZAt h ta2R)
    (huet : wtZ uet.1 uet.2 = (i * g0) • wtZ ude.1 ude.2)
    (huta1 : wtZ uta1.1 uta1.2 = (2 : ℕ) • (wtZ uL.1 uL.2 - wtZ ude.1 ude.2))
    (huta2 : wtZ uta2.1 uta2.2 = (Dd + 4 : ℕ) • wtZ uL.1 uL.2 - wtZ uF.1 uF.2)
    (hfn : FnNe Xo c fn) (hconj : FnConj Xo c fn yP)
    (hbdd : LawBdd (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r))
    (ha1 : A1Bigness (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r))
    (ha2 : A2RegularityOrders (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r))
    (ha3' : LawA3' (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r))
    (sel : Fin (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).del → Fin np)
    (ha4 : A4Selection (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r) sel)
    (hnum : NumOK (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r))
    (ha13 : A13Measurable (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r))
    (hH1 : (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).FinitePlaceHyp) (hF1d : (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).TrivialPlaceHyp)
    (hLAM : (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).HtLAM) (hSup : (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).HtSup)
    (hI2et : (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).HeightIntegralEstimateTrivialPlace) (hI2be : (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).HeightIntegralBoundEstimate) :
    Formalism.MainNotions.Gaps.HeightData.HtConcl ((dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).htOf (axHOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r hne hfg htr hac hwb het hta1 hta2 huet huta1 huta2 hfn hconj hbdd ha1 ha2 ha3' sel ha4 hnum ha13)
      ((dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).genericSection_of_axioms (axHOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r hne hfg htr hac hwb het hta1 hta2 huet huta1 huta2 hfn hconj hbdd ha1 ha2 ha3' sel ha4 hnum ha13))) :=
  (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).heights (axHOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r hne hfg htr hac hwb het hta1 hta2 huet huta1 huta2 hfn hconj hbdd ha1 ha2 ha3' sel ha4 hnum ha13)
    ((dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).genericSection_of_axioms (axHOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r hne hfg htr hac hwb het hta1 hta2 huet huta1 huta2 hfn hconj hbdd ha1 ha2 ha3' sel ha4 hnum ha13)) hH1 hF1d hLAM hSup hI2et hI2be

section Of

open IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj.abelian₂ Formalism.L2.LamCM ReciprocityTheory.ChartRestriction.G.FD

variable {D : D7} {Tc : Core D}

end Of

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor MvPolynomial

namespace CurveCount

variable {K : Type*} [Field K] {N : ℕ}

def homog (a : Fin N) (Q : MvPolynomial (Fin N) K) : MvPolynomial (Fin N) K :=
  ∑ m ∈ Q.support, monomial (m + Finsupp.single a (Q.totalDegree - m.degree)) (Q.coeff m)

theorem homog_isHomogeneous (a : Fin N) (Q : MvPolynomial (Fin N) K) :
    (homog a Q).IsHomogeneous Q.totalDegree := by
  classical
  refine IsHomogeneous.sum _ _ _ fun m hm => isHomogeneous_monomial _ ?_
  have hle : m.degree ≤ Q.totalDegree := le_totalDegree hm
  rw [map_add (f := _), Finsupp.degree_single]
  omega

theorem aeval_homog {L : Type*} [Field L] [Algebra K L] (a : Fin N) (Q : MvPolynomial (Fin N) K) (y : Fin N → L)
    (hy : y a ≠ 0) : aeval y (homog a Q) = y a ^ Q.totalDegree * aeval (fun i => y i / y a) Q := by
  classical
  have hQ : aeval (fun i => y i / y a) Q =
      ∑ m ∈ Q.support, aeval (fun i => y i / y a) (monomial m (Q.coeff m)) := by
    conv_lhs => rw [Q.as_sum]

    rw [map_sum]

  rw [hQ, homog, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hle : m.degree ≤ Q.totalDegree := le_totalDegree hm
  rw [aeval_monomial, aeval_monomial, Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
    Finsupp.prod_single_index (by simp)]
  simp only [Finsupp.prod, div_pow, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
  have hd : m.degree = ∑ i ∈ m.support, m i := rfl
  rw [← hd]
  have e : y a ^ Q.totalDegree = y a ^ (Q.totalDegree - m.degree) * y a ^ m.degree := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  rw [e]
  field_simp

theorem adjoin_ratio_eq {L : Type*} [Field L] [Algebra K L] (v : Fin N → L) {a b : Fin N} (ha : v a ≠ 0)
    (hb : v b ≠ 0) :
    IntermediateField.adjoin K (Set.range fun i => v i / v a) = IntermediateField.adjoin K (Set.range fun i => v i / v b) := by
  have key : ∀ a b : Fin N, v a ≠ 0 → v b ≠ 0 →
      IntermediateField.adjoin K (Set.range fun i => v i / v a) ≤ IntermediateField.adjoin K (Set.range fun i => v i / v b) := by
    intro a b ha hb
    rw [IntermediateField.adjoin_le_iff, Set.range_subset_iff]
    intro i
    have e : v i / v a = (v i / v b) / (v a / v b) := by field_simp
    rw [SetLike.mem_coe, e]
    exact IntermediateField.div_mem _ (IntermediateField.subset_adjoin K _ ⟨i, rfl⟩)
      (IntermediateField.subset_adjoin K _ ⟨a, rfl⟩)
  exact le_antisymm (key a b ha hb) (key b a hb ha)

end CurveCount

namespace CurveLoc

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO))
  (N : ℕ) {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)

theorem tv_indep :
    AlgebraicIndependent (X.Kl la) (fun p : Idx D j N => @algebraMap (Op X la N) (Kp X la N) _ _ _ (Tv X la N p)) := by
  have h0 := MvPolynomial.algebraicIndependent_X (Idx D j N) (X.Ol la)
  have hinj1 : Function.Injective (algebraMap (Pol X la N) (Op X la N)) :=
    IsLocalization.injective (Op X la N) (Ideal.primeCompl_le_nonZeroDivisors (gI X la N))
  have hinj2 : Function.Injective (@algebraMap (Op X la N) (Kp X la N) _ _ _) := IsFractionRing.injective _ _
  let g : Pol X la N →ₐ[X.Ol la] Kp X la N :=
    (IsScalarTower.toAlgHom (X.Ol la) (Op X la N) (Kp X la N)).comp
      (IsScalarTower.toAlgHom (X.Ol la) (Pol X la N) (Op X la N))
  have h1 : AlgebraicIndependent (X.Ol la)
      (fun p : Idx D j N => @algebraMap (Op X la N) (Kp X la N) _ _ _ (Tv X la N p)) :=
    h0.map' (f := g) (hinj2.comp hinj1)
  have : Algebra.IsAlgebraic (X.Ol la) (X.Kl la) := IsLocalization.isAlgebraic (X.Kl la) (nonZeroDivisors (X.Ol la))
  exact h1.extendScalars (X.Kl la)

theorem sfr_eq (i : Fin (WeightFamilies.dimY D j + 1)) :
    sfr X la w i = ∑ k, algebraMap (Kp X la N) ↥(Frac0 X la w)
      (@algebraMap (Op X la N) (Kp X la N) _ _ _ (Tv X la N (i, k))) * xw X la N w k := by
  apply Subtype.ext

  rw [coe_sfr, Formalism.MainNotions.Gaps.EtaleWeightGaps.sec, map_sum]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, Algebra.smul_def]
  rfl

theorem sfr_zero : sfr X la w 0 = 1 := by
  apply Subtype.ext
  rw [coe_sfr, frac_apply, pow_one, section_mul_inverse_eq_one]
  rfl

variable {Ω : Type} [Field Ω] [Algebra B.KO Ω] (gF : X.Forms →ₐ[B.KO] Ω)


set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in
theorem countQAt_of (v : Fin N → Ω) (hv : ∀ i, gF (X.inc wL (w i)) = v i)
    (htr : ∃ a₀, v a₀ ≠ 0 ∧
      Algebra.trdeg B.KO (IntermediateField.adjoin B.KO (Set.range fun i => v i / v a₀)) ≤ WeightFamilies.dimY D j) :
    CountQAt X la N w gF := by
  classical
  intro 𝔮 h𝔮 hJ hK Pw k hPw hne hmem
  have : 𝔮.IsPrime := h𝔮
  have hvf : (fun i => gF (X.inc wL (w i))) = v := funext hv
  rw [hvf] at hne
  let Fr := ↥(Frac0 X la w)
  let κ := FractionRing (Fr ⧸ 𝔮)
  let ρ : Fr →+* κ := (algebraMap (Fr ⧸ 𝔮) κ).comp (Ideal.Quotient.mk 𝔮)
  have hρ : ∀ f, ρ f = 0 ↔ f ∈ 𝔮 := fun f => by
    rw [RingHom.comp_apply, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  let ρK : Kp X la N →+* κ := ρ.comp (algebraMap (Kp X la N) Fr)
  let algKl : Algebra (X.Kl la) κ := (ρK.comp (algebraMap (X.Kl la) (Kp X la N))).toAlgebra
  let algK : Algebra B.KO κ :=
    ((ρK.comp (algebraMap (X.Kl la) (Kp X la N))).comp (algebraMap B.KO (X.Kl la))).toAlgebra
  let _ := algKl
  let _ := algK
  have : IsScalarTower B.KO (X.Kl la) κ :=
    @IsScalarTower.of_algebraMap_eq B.KO (X.Kl la) κ _ _ _ _ algKl algK (fun _ => rfl)
  let x : Fin N → κ := fun i => ρ (xw X la N w i)
  let t : Fin (WeightFamilies.dimY D j + 1) × Fin N → κ :=
    fun p => ρK (@algebraMap (Op X la N) (Kp X la N) _ _ _ (Tv X la N p))
  have ht : AlgebraicIndependent B.KO t := by
    let g : Kp X la N →ₐ[X.Kl la] κ := { ρK with commutes' := fun _ => rfl }
    have h1 := (tv_indep X la N).map' (f := g) ρK.injective
    exact h1.restrictScalars (algebraMap B.KO (X.Kl la)).injective
  have hρpol : ∀ Q : MvPolynomial (Fin N) B.KO, ρ (polX X la N w Q) = aeval x Q := fun Q => by
    rw [polX, MvPolynomial.eval₂_comp_left, aeval_def]
    rfl
  have hlin : ∀ i : Fin (WeightFamilies.dimY D j), ∑ k, t (i.succ, k) * x k = 0 := by
    intro i
    have h := congrArg ρ (sfr_eq X la N w i.succ)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at h
    simp only [map_mul] at h
    rw [← (hρ _).mpr (hJ (sfr_succ_mem_Jid X la w i)), h]
    rfl
  have hlin0 : ∑ k, t (0, k) * x k = 1 := by
    have h := congrArg ρ (sfr_eq X la N w 0)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, sfr_zero, map_one] at h
    simp only [map_mul] at h
    rw [h]
    rfl
  obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hlin0.symm ▸ one_ne_zero : ∑ k, t (0, k) * x k ≠ 0)
  have hxa : x a ≠ 0 := right_ne_zero_of_mul ha
  have hva : v a ≠ 0 := by
    intro h0
    apply hxa
    refine (hρ _).mpr (hK ?_)
    rw [RingHom.mem_ker, phiZ_xw, hv, h0, map_zero, zero_mul]
  obtain ⟨a₀, ha₀, htr₀⟩ := htr
  have htra : Algebra.trdeg B.KO (IntermediateField.adjoin B.KO (Set.range fun i => v i / v a)) ≤ WeightFamilies.dimY D j := by
    rw [CurveCount.adjoin_ratio_eq v hva ha₀]
    exact htr₀
  have htrans : ∀ Q : MvPolynomial (Fin N) B.KO, aeval (fun i => v i / v a) Q = 0 →
      aeval (fun i => x i / x a) Q = 0 := by
    intro Q hQ
    have hH := CurveCount.homog_isHomogeneous a Q
    have hv0 : aeval v (CurveCount.homog a Q) = 0 := by rw [CurveCount.aeval_homog a Q v hva, hQ, mul_zero]
    have hq : polX X la N w (CurveCount.homog a Q) ∈ 𝔮 := hK (by
      rw [RingHom.mem_ker, phiZ_polX X la N w gF hH, hvf, hv0, map_zero, mul_zero])
    have hx0 : aeval x (CurveCount.homog a Q) = 0 := by rw [← hρpol]; exact (hρ _).mpr hq
    rw [CurveCount.aeval_homog a Q x hxa] at hx0
    exact (mul_eq_zero.mp hx0).resolve_left (pow_ne_zero _ hxa)
  exact CurveCount.countCore v x a hva hxa htra htrans t ht hlin hlin0 Pw hPw hne
    (by rw [← hρpol]; exact (hρ _).mpr hmem)

end CurveLoc

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

variable {D : D7} {T : Top D}

def RatAt (h : LawsP T) (j : ℕ) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (κ : Comp (T.Q.Xo j) T.Q.c → (T.U j T.σ₀).Comp)
    (Z : Comp (T.Q.Xo j) T.Q.c) (x : Frame ((T.U j T.σ₀).X (κ Z)).Ψ D.R.r) (P : Om Z →+* ℂ) : Prop :=
  ∀ (u : WeightFamilies.Wt D j) (F G' : (recB h.toLawsCore).Cusp j u), Even u.n →
    valC hG (wtA u) u.n G'.1 Z ≠ 0 →
    rdR h j F (κ Z) x = P (ReciprocityTheory.ChartRestriction.G.T0.ratio (Ω := Om Z) (valC hG (wtA u) u.n F.1 Z)
      (valC hG (wtA u) u.n G'.1 Z)) * rdR h j G' (κ Z) x


end Formalism.L2.Pj
end
end
