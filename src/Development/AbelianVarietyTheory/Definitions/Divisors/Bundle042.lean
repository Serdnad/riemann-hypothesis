module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LinearIndependentPullChart
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecondCountableTopologyOfIsProjOver
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1270
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle014
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle118
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField MeasureTheory Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CxPts GlobalTheory.TopForm GlobalTheory.ChartGlue
open scoped ENNReal

namespace GlobalTheory

section General

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {B L : LB Y} {O : Y.Opens}

theorem CompHS.cval_mem_fibSec (f : H0 p B O) : cval σ f ∈ fibSec p σ B := by
  refine ⟨fun i j y hi hj => ?_, fun i y h => ev_of_notMem (fun e => h (mem_ptsIn_inf.1 e).2) _⟩
  by_cases hO : y ∈ ptsIn p σ O
  · rw [cval_eq_val σ f i y hO hi, cval_eq_val σ f j y hO hj, H0.val_change y.1 i j hO hi hj]
    exact congrArg (· * _) (ev_eq (mem_ptsIn_inf.2 ⟨hi, hj⟩) _).symm
  · exact (ev_of_notMem (fun e => hO (mem_ptsIn_inf.1 e).1) _).trans
      ((mul_zero _).symm.trans (congrArg _ (ev_of_notMem (fun e => hO (mem_ptsIn_inf.1 e).1) _).symm))

namespace CompHS

def divVal (σ : k →+* ℂ) (ω : H0 p (LB.div B L) O) : (tens B (dual L)).ι → CxPts p σ → ℂ := cval σ ω

theorem divVal_mem (ω : H0 p (LB.div B L) O) : divVal σ ω ∈ fibSec p σ (tens B (dual L)) := by
  have h := cval_mem_fibSec (σ := σ) ω
  refine ⟨fun i j y hi hj => (h.1 i j y hi hj).trans (congrArg (· * _) ?_), h.2⟩
  have hy := mem_ptsIn_inf.2 ⟨hi, hj⟩
  exact (ev_mul _ _ y).trans (Eq.trans (congrArg (_ * ·) ((ev_inv hy _).trans (Eq.symm ((ev_res _ hy _).trans
    ((ev_inv (mem_ptsIn_inf.2 ⟨(mem_ptsIn_inf.1 hi).2, (mem_ptsIn_inf.1 hj).2⟩) _).trans
      (congrArg (·⁻¹) (ev_res _ hy _).symm)))))) (ev_mul _ _ y).symm)

variable {D : ℕ} [SmoothOfRelativeDimension D p] (K : CanonLB p D) (φ φ' : Weight p σ L)
  (ω : H0 p (LB.div K.bundle L) O)

def volDens (a : AlgChart p σ D) (y : CxPts p σ) : ℝ := a.topDens K φ.dual (divVal σ ω) y

def volMeasure : Measure (CxPts p σ) :=
  ((AnRead.all p σ D).topMeasure K φ.dual (divVal σ ω)).restrict (ptsIn p σ O)

variable {φ φ'}

theorem volDens_eq (a : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ a.e.source) {i : K.bundle.ι} {j : L.ι}
    (hi : y ∈ ptsIn p σ (K.bundle.U i)) (hj : y ∈ ptsIn p σ (L.U j)) : volDens K φ ω a y =
      2 ^ D * (‖rv σ a.isFrame (K.isFrame i) y * cval σ ω (i, j) y‖ ^ 2 / Real.exp (-φ.φ j y)) := by
  rw [volDens, a.topDens_eq K φ.dual (divVal_mem ω) hy hi (b := j) hj, div_eq_mul_inv, ← Real.exp_neg]
  rfl

theorem volDens_pos (hω : NowhereZero ω) (a : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ a.e.source)
    (hO : y ∈ ptsIn p σ O) : 0 < volDens K φ ω a y := by
  have hi := mem_pick K.isLB y
  have hj := mem_pick φ.isLB y
  have hm : y ∈ ptsIn p σ (O ⊓ (LB.div K.bundle L).U (_, _)) := mem_ptsIn_inf.2 ⟨hO, mem_ptsIn_inf.2 ⟨hi, hj⟩⟩
  have h₁ : cval σ ω (_, _) y ≠ 0 := (mem_ptsIn_basicOpen hm _).1 (mem_ptsIn.2
    ((Y.mem_basicOpen _ _ (mem_ptsIn.1 hm)).2 (hω _ (mem_ptsIn.1 hm).1 _ (mem_ptsIn.1 hm).2)))
  have h₂ := mul_ne_zero (rv_ne_zero a.isFrame (K.isFrame _) (a.source_subset hy) hi) h₁
  rw [volDens_eq K ω a hy hi hj]
  exact mul_pos (by positivity) (div_pos (pow_pos (norm_pos_iff.2 h₂) _) (Real.exp_pos _))

variable [SecondCountableTopology (CxPts p σ)]

theorem volMeasure_apply (a : AlgChart p σ D) {A : Set (CxPts p σ)} (hA : MeasurableSet A) (h : A ⊆ a.e.source) :
    volMeasure K φ ω A = ∫⁻ v in a.e '' (A ∩ ptsIn p σ O), ENNReal.ofReal (volDens K φ ω a (a.e.symm v)) := by
  rw [volMeasure, Measure.restrict_apply hA]
  exact (AnRead.all p σ D).topMeasure_apply K _ _ a (hA.inter (isOpen_ptsIn O).measurableSet) (inter_subset_left.trans h)

theorem volMeasure_of_add {s : ℝ} (h : ∀ j, ∀ y ∈ ptsIn p σ O, y ∈ ptsIn p σ (L.U j) → φ'.φ j y = φ.φ j y + s) :
    volMeasure K φ' ω = ENNReal.ofReal (Real.exp s) • volMeasure K φ ω := by
  refine ext_of_cover _ (fun a : AlgChart p σ D => a.e.open_source) AlgChart.exists_mem_source fun a A hA hs => ?_
  have hA' := hA.inter (isOpen_ptsIn (p := p) (σ := σ) O).measurableSet
  rw [smul_apply, volMeasure_apply K ω a hA hs, volMeasure_apply K ω a hA hs, smul_eq_mul,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun (measurableSet_image a.e hA' (inter_subset_left.trans hs)) ?_
  rintro _ ⟨y, hy, rfl⟩
  have hi := mem_pick K.isLB y
  have hj := mem_pick φ.isLB y
  simp only [a.e.left_inv (hs hy.1)]
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, volDens_eq K ω a (hs hy.1) hi hj, volDens_eq K ω a (hs hy.1) hi hj,
    h _ y hy.2 hj, neg_add, Real.exp_add, Real.exp_neg s]
  congr 1
  field_simp

theorem volMeasure_pos (hω : NowhereZero ω) (hφ : ∀ j, ContinuousOn (φ.φ j) (ptsIn p σ O ∩ ptsIn p σ (L.U j)))
    {y : CxPts p σ} (hy : y ∈ ptsIn p σ O) : 0 < volMeasure K φ ω univ := by
  obtain ⟨a, ha⟩ := AlgChart.exists_mem_source (D := D) y
  have hi := mem_pick K.isLB y
  have hj := mem_pick φ.isLB y
  set i := pick K.isLB y
  set j := pick φ.isLB y
  let S := a.e.source ∩ (ptsIn p σ (a.U ⊓ K.bundle.U i) ∩ ptsIn p σ (O ⊓ (LB.div K.bundle L).U (i, j)))
  have hS : IsOpen S := a.e.open_source.inter ((isOpen_ptsIn _).inter (isOpen_ptsIn _))
  have hO : S ⊆ ptsIn p σ O := fun z hz => (mem_ptsIn_inf.1 hz.2.2).1
  have hL : S ⊆ ptsIn p σ (L.U j) := fun z hz => (mem_ptsIn_inf.1 (mem_ptsIn_inf.1 hz.2.2).2).2
  have hc : ContinuousOn (volDens K φ ω a) S := (continuousOn_const.mul
    (((((continuousOn_ev _).mono (t := S) fun _ hz => hz.2.1).mul
      ((continuousOn_ev _).mono (t := S) fun _ hz => hz.2.2)).norm.pow 2).div
      ((hφ j).mono (subset_inter hO hL)).neg.rexp fun _ _ => (Real.exp_pos _).ne')).congr
    fun z hz => volDens_eq K ω a hz.1 (mem_ptsIn_inf.1 hz.2.1).2 (hL hz)
  have ho := a.e.isOpen_image_of_subset_source hS inter_subset_left
  have hm : MapsTo a.e.symm (a.e '' S) S := by
    rintro _ ⟨z, hz, rfl⟩
    rwa [a.e.left_inv hz.1]
  have hc' := ENNReal.continuous_ofReal.comp_continuousOn (hc.comp (a.e.continuousOn_symm.mono (t := a.e '' S)
    (image_subset_iff.2 fun _ hz => a.e.map_source hz.1)) hm)
  refine lt_of_lt_of_le ?_ (measure_mono (subset_univ S))
  rw [volMeasure_apply K ω a hS.measurableSet inter_subset_left, inter_eq_left.2 hO, pos_iff_ne_zero]
  intro h
  have h₁ := (ae_restrict_iff' ho.measurableSet).1 ((lintegral_eq_zero_iff' (hc'.aemeasurable ho.measurableSet)).1 h)
  refine (ho.measure_pos volume ⟨_, y, ⟨ha, mem_ptsIn_inf.2 ⟨a.source_subset ha, hi⟩,
    mem_ptsIn_inf.2 ⟨hy, mem_ptsIn_inf.2 ⟨hi, hj⟩⟩⟩, rfl⟩).ne' (measure_mono_null ?_ (ae_iff.1 h₁))
  exact fun v hv hh => (ENNReal.ofReal_pos.2 (volDens_pos K ω hω a (hm hv).1 (hO (hm hv)))).ne' (hh hv)

end CompHS

end General

namespace CompHS

open ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.AllWt (exOf wtOf lieFacZ modelWt homN)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

section Good

variable {Y T : Scheme.{0}} {p : Y ⟶ Sp c.F} {σ σ' : c.F →+* ℂ} {B : LB Y}


end Good

section Fac

variable {r : ℕ} {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (x : ℝ)


open Classical in
def diagChar (e : Ix Dw → ℤ) (t : Ix Dw → (CAt σ)ˣ) : ℂ := toC (∏ ix, t ix ^ e ix).val

def homFac (la : AllWt.Weight Dw) (k : U.Comp) (w : (U.X k).dom) : ℝ :=
  lieFacZ Dw x (wtOf Dw la 0) * (U.X k).nfac (modelWt U (wtOf Dw la 0) k) w.1

theorem homN_eq_homFac (la : AllWt.Weight Dw) (f : Rul Xo c) (k : U.Comp) (w : (U.X k).dom) :
    homN U x (wtOf Dw la 0) f ⟨k, w.1⟩ = homFac U x la k w * ‖toC (evR Xo c f (U.un k w))‖ := by
  have e : rdU U f k w.1 = toC (evR Xo c f (U.un k w)) := dite_eq_left w.2
  change _ * (‖rdU U f k w.1‖ * (U.X k).nfac _ _) = _
  rw [e, homFac]
  ring

variable {U}

end Fac

end CompHS

end GlobalTheory
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt

namespace GlobalTheory.MixHt

variable {k : Type} [CommRing k] {X Y : Scheme.{0}}

structure IsAmb (p : X ⟶ Sp k) : Prop where

  isDomain : IsDomain k

  finite : Module.Finite ℤ k

  isProjOver : IsProjOver p

theorem isAmb_of_isArithVar {p : X ⟶ Sp k} {D : ℕ} (h : IsArithVar p D) : IsAmb p :=
  ⟨h.isDomain, h.finite, h.isProjOver⟩

theorem IsAmb.sub {p : X ⟶ Sp k} (h : IsAmb p) (i : Y ⟶ X) [IsClosedImmersion i] : IsAmb (i ≫ p) :=
  ⟨h.isDomain, h.finite, GlobalTheory.isProjOver_comp_of_finite k X Y i p inferInstance h.isProjOver⟩

theorem IsAmb.isNoetherian {p : X ⟶ Sp k} (h : IsAmb p) : IsNoetherian X := by

  haveI := h.finite
  haveI : IsNoetherianRing k := isNoetherian_of_tower ℤ (inferInstance : IsNoetherian ℤ k)
  exact GlobalTheory.isNoetherian_of_isProjOver h.isProjOver

def HasDim (x : X) (d : ℕ) : Prop := topologicalKrullDim (closure ({x} : Set X)) = d

def clo (x : X) : Scheme.{0} := (exists_isClosedImmersion_genericPoint x).choose

def cloι (x : X) : clo x ⟶ X := (exists_isClosedImmersion_genericPoint x).choose_spec.choose

instance (x : X) : IsClosedImmersion (cloι x) :=
  (exists_isClosedImmersion_genericPoint x).choose_spec.choose_spec.choose

instance (x : X) : IsIntegral (clo x) :=
  (exists_isClosedImmersion_genericPoint x).choose_spec.choose_spec.choose_spec.choose

instance [IsLocallyNoetherian X] (x : X) : IsLocallyNoetherian (clo x) :=
  LocallyOfFiniteType.isLocallyNoetherian (cloι x)

theorem cloι_genericPoint (x : X) : cloι x (genericPoint (clo x)) = x :=
  (exists_isClosedImmersion_genericPoint x).choose_spec.choose_spec.choose_spec.choose_spec

section Val

variable [IsIntegral Y] {q : Y ⟶ Sp k} {e : ℕ}

def mixArch (L : Fin e → HermLB q) (M : HermLB q) {r : M.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r) : ℝ :=
  FibreProj.pol (fun n => (comb L n).archInt M e hr) / e.factorial

variable [IsLocallyNoetherian Y]

def recVal (h : Y → ℝ) (L : Fin e → HermLB q) (M : HermLB q) {r : M.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r) : ℝ :=
  ∑ᶠ z, ((M.div hr).mult z : ℝ) * h z - mixArch L M hr

end Val


open Classical in
def resArch {q : Y ⟶ Sp k} {e : ℕ} (L : Fin e → HermLB q) (N : HermLB q) (t : N.B.Sec) (z : Y) : ℝ :=
  if h : genericPoint (clo z) ∈ nonzeroLocus (secPull t (cloι z)) then
    mixArch (fun a => (L a).restr (cloι z)) (N.restr (cloι z)) (isRatSec_ratOfSec _ h) else 0


open Classical in
def resCyc [IsLocallyNoetherian Y] {B : LB Y} (hB : B.IsLB) (t : B.Sec) (g : Y → ℝ) (z : Y) : ℝ :=
  if h : genericPoint (clo z) ∈ nonzeroLocus (secPull t (cloι z)) then
    ∑ᶠ w, ((divOfSec (LB.isLB_pull hB (cloι z)) _ h).mult w : ℝ) * g (cloι z w) else 0

structure IsMix (p : X ⟶ Sp k) (m : ℕ) (T : ∀ d : ℕ, (Fin d → HermLB p) → X → ℝ) : Prop where

  iso : ∀ (d : ℕ) (L M : Fin d → HermLB p) (x : X), d ≤ m → HasDim x d → (∀ a, (L a).Isometric (M a)) → T d L x = T d M x

  symm : ∀ (d : ℕ) (L : Fin d → HermLB p) (e : Equiv.Perm (Fin d)) (x : X), d ≤ m → HasDim x d →
    T d (fun a => L (e a)) x = T d L x

  add : ∀ (d : ℕ) (A B : HermLB p) (L : Fin d → HermLB p) (x : X), d + 1 ≤ m → HasDim x (d + 1) →
    T (d + 1) (Fin.cons (A.tens B) L) x = T (d + 1) (Fin.cons A L) x + T (d + 1) (Fin.cons B L) x

  zero : ∀ (L : Fin 0 → HermLB p) (x : X), HasDim x 0 → T 0 L x = Real.log (Nat.card (X.residueField x))

  recur : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (i : Y ⟶ X) [IsClosedImmersion i]
    (hi : i ≫ p = q) (e : ℕ), e + 1 ≤ m → topologicalKrullDim Y = (e + 1 : ℕ) →
    ∀ (M : HermLB p) (L : Fin e → HermLB p) (M' : HermLB q) (L' : Fin e → HermLB q), (M.pull i hi).Isometric M' →
    (∀ a, ((L a).pull i hi).Isometric (L' a)) → ∀ (r : M'.B.ι → Y.functionFieldˣ) (hr : IsRatSec M'.B r),
      T (e + 1) (Fin.cons M L) (i (genericPoint Y)) = recVal (fun z => T e L (i z)) L' M' hr

theorem isMix_zero (p : X ⟶ Sp k) : IsMix p 0 (fun _ _ x => Real.log (Nat.card (X.residueField x))) := by
  refine ⟨fun _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl, ?_, fun _ _ _ => rfl, ?_⟩
  · intros
    omega
  · intros
    omega

def ArchInteg : Prop := ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k) (e : ℕ), IsArithVar q e →
  ∀ (M N : HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r), N.ArchIntegrable M e hr

def ArchRecip : Prop := ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k)
  (e : ℕ), IsArithVar q (e + 1) → ∀ (M N : HermLB q) (L : Fin e → HermLB q) (s : M.B.Sec) (t : N.B.Sec)
  (hs : genericPoint Y ∈ nonzeroLocus s) (ht : genericPoint Y ∈ nonzeroLocus t),
  (∀ z : Y, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) →
    mixArch (Fin.cons N L : Fin (e + 1) → HermLB q) M (isRatSec_ratOfSec s hs) +
        ∑ᶠ z, ((divOfSec M.isLB s hs).mult z : ℝ) * resArch L N t z =
      mixArch (Fin.cons M L : Fin (e + 1) → HermLB q) N (isRatSec_ratOfSec t ht) +
        ∑ᶠ z, ((divOfSec N.isLB t ht).mult z : ℝ) * resArch L M s z

end GlobalTheory.MixHt
end
end

section

noncomputable section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift

namespace GlobalTheory.HoweR

section Gl

variable {ι M : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M]

def IsGl (F : ι → ι → Module.End ℂ M) : Prop :=
  ∀ a b c d, F a b * F c d - F c d * F a b = (if b = c then F a d else 0) - (if d = a then F c b else 0)

def negT (F : ι → ι → Module.End ℂ M) : ι → ι → Module.End ℂ M := fun a b => -F b a

def cas (s : ι → Bool) (F : ι → ι → Module.End ℂ M) : Module.End ℂ M :=
  ∑ a, ∑ b, if s a = s b then F a b * F b a else 0

def qop (F : ι → ι → Module.End ℂ M) (α β : ℂ) (a b : ι) : Module.End ℂ M :=
  ∑ c, F a c * F c b - α • F a b - if a = b then β • 1 else 0

def UnitOn (s : ι → Bool) (F : ι → ι → Module.End ℂ M) (U : Submodule ℂ M) : Prop :=
  FiniteDimensional ℂ U ∧ (∀ a b, s a = s b → ∀ u ∈ U, F a b u ∈ U) ∧
    ∃ ip : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ, (∀ x ∈ U, ∀ y ∈ U, star (ip x y) = ip y x) ∧ (∀ x ∈ U, x ≠ 0 → 0 < (ip x x).re) ∧
      ∀ a b, s a = s b → ∀ x ∈ U, ∀ y ∈ U, ip (F a b x) y = ip x (F b a y)

def LocU (s : ι → Bool) (F : ι → ι → Module.End ℂ M) : Prop :=
  ∀ t : Finset M, ∃ U : Submodule ℂ M, (∀ x ∈ t, x ∈ U) ∧ UnitOn s F U

end Gl

section Act

variable {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def units (act : Mat p q →ₗ[ℂ] Module.End ℂ V) : Ix p q → Ix p q → Module.End ℂ V := fun a b => act (Eab a b)

def Stab (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V) : Prop := ∀ Z, ∀ y ∈ N, act Z y ∈ N

def Good (act : Mat p q →ₗ[ℂ] Module.End ℂ V) : Prop :=
  IsLieAct act ∧ (∀ v, v ∈ ⨆ μ : Ix p q → ℚ, wtSub act μ) ∧ LocU (fun a : Ix p q => a.isLeft) (units act)

def QuadMod (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (α β α' β' : ℂ) (N N' : Submodule ℂ V) : Prop :=
  ∀ a b, ∀ v ∈ N', qop (units act) α β a b v ∈ N ∧ qop (negT (units act)) α' β' a b v ∈ N

def AdmMod (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (C : Submodule ℂ V) : Prop :=
  ∀ B : ℚ, ∃ U : Submodule ℂ V, FiniteDimensional ℂ U ∧ ∀ μ : Ix p q → ℚ, (∀ a, |μ a| ≤ B) → hwSub act μ ≤ U ⊔ C

def CycMod (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (C : Submodule ℂ V) : Prop :=
  ∃ (μ : Ix p q → ℚ) (v : V), v ∈ hwSub act μ ∧ genSub act {v} ⊔ C = ⊤ ∧ hwSub act μ ≤ Submodule.span ℂ {v} ⊔ C

def Pack (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (C : Submodule ℂ V) : Prop :=
  Good act ∧ Stab act C ∧ (∃ α β α' β' : ℂ, QuadMod act α β α' β' C ⊤) ∧ AdmMod act C ∧ CycMod act C

end Act

def coinv (P Q R S : ℕ) (x : ℂ) : Submodule ℂ (Formalism.BasicNotions.TH.Pol P Q R S) :=
  Submodule.span ℂ {g | ∃ (X : Mat P Q) (f : Formalism.BasicNotions.TH.Pol P Q R S), g = fockAct1 P Q R S X f - (x * X.trace) • f}

section Tensor

variable {T : Type} [Fintype T] [DecidableEq T] {V : T → Type} [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)]

def actAt {p q : ℕ} (w : T) (a : Mat p q →ₗ[ℂ] Module.End ℂ (V w)) : Mat p q →ₗ[ℂ] Module.End ℂ (⨂[ℂ] i, V i) :=
  ((PiTensorProduct.mapMultilinear ℂ V V).toLinearMap (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w) ∘ₗ a

theorem actAt_apply {p q : ℕ} (w : T) (a : Mat p q →ₗ[ℂ] Module.End ℂ (V w)) (Z : Mat p q) :
    actAt w a Z = atPl w (a Z) := rfl

def tensAll (H : ∀ w, Submodule ℂ (V w)) : Submodule ℂ (⨂[ℂ] i, V i) :=
  Submodule.span ℂ {y | ∃ f : ∀ w, V w, (∀ w, f w ∈ H w) ∧ y = PiTensorProduct.tprod ℂ f}

def tensAny (C : ∀ w, Submodule ℂ (V w)) : Submodule ℂ (⨂[ℂ] i, V i) :=
  Submodule.span ℂ {y | ∃ f : ∀ w, V w, (∃ w, f w ∈ C w) ∧ y = PiTensorProduct.tprod ℂ f}

end Tensor

def HoweAlg {T : Type} {R S : T → ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (a : ∀ w, Mat (R w) (S w) →ₗ[ℂ] Module.End ℂ V) (C : Submodule ℂ V) : Prop :=
  (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ V), StrictMono N → (∀ k, (∀ w, Stab (a w) (N k)) ∧ C ≤ N k) → m ≤ L) ∧
  ∀ N N' : Submodule ℂ V, (∀ w, Stab (a w) N) → C ≤ N → N ≠ ⊤ → (∀ w, Stab (a w) N') → C ≤ N' → N' ≠ ⊤ → N ⊔ N' ≠ ⊤

end GlobalTheory.HoweR

end
end

section

noncomputable section

open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.HoweD

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] {P Q R S : InfinitePlace F → ℕ}


variable (F) in
abbrev TensD (P Q R S : InfinitePlace F → ℕ) : Type := ⨂[ℂ] w : InfinitePlace F, Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)

def FramedD (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E)) (a b : ℂ)
    (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ) (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ) : Prop :=
  a * b = Complex.I ∧ (∀ w, IsFrame (a • JA.map (piInf (τ w))) (A w)) ∧ ∀ w, IsFrame (b • JB.map (piInf (τ w))) (C w)

def IsFockMapD (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {JA : Matrix α α (AE F E)}
    {JB : Matrix β β (AE F E)} (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ)
    (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ) (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ)
    (Φ : TensD F P Q R S →ₗ[ℂ] SInf F κ) : Prop :=
  Function.Injective Φ ∧ ∀ u : Matrix α β (AE F E), At (evI F) u →
    ∀ c : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ,
    (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) →
      ∀ T, SD (fun t => d.rho ψ (realAd F t • u)) (Φ T) (Φ (sumPl (fun w => heisOp (c w)) T))

def IsGenD (τ : ∀ w : InfinitePlace F, EmbOver E w) {J : Matrix β β (AE F E)}
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ)
    (γ : Multiplicative ℝ →* UG (cA σ) J) (Y : ∀ w : InfinitePlace F, Mat (R w) (S w)) : Prop :=
  ∀ (t : ℝ) w, ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)).map (piInf (τ w)) * C w =
    C w * NormedSpace.exp (t • Y w)

def ActsByD (τ : ∀ w : InfinitePlace F, EmbOver E w) {J : Matrix β β (AE F E)} {r s : InfinitePlace F → ℕ}
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (r w) (s w)) ℂ) (om : UG (cA σ) J →* Module.End ℂ ((κ → AF F) → ℂ))
    (Φ : TensD F P Q R S →ₗ[ℂ] SInf F κ)
    (act : ∀ w, Mat (r w) (s w) →ₗ[ℂ] Module.End ℂ (Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)))
    (c : InfinitePlace F → ℂ) : Prop :=
  ∀ γ ∈ RLines (σ := σ) J, ∀ Y, IsGenD τ C γ Y → ∀ T, SD (fun t => om (γ (Multiplicative.ofAdd t))) (Φ T)
    (Φ (sumPl (fun w => act w (Y w) + (c w * (Y w).trace) • 1) T))

end Adelic

end GlobalTheory.HoweD

end
end
