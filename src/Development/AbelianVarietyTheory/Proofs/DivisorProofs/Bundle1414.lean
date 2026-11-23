module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1222
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle237
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle186
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle188
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle235
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
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
public import Mathlib.Topology.PartitionOfUnity
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

namespace GlobalTheory.HSAmp

theorem ringChar_residueField_eq {X Y : Scheme.{0}} (f : X ⟶ Y) (x : X) :
    ringChar (X.residueField x) = ringChar (Y.residueField (f x)) := by
  haveI := (RingHom.charP_iff_charP (f.residueFieldMap x).hom (ringChar (Y.residueField (f x)))).1
    (ringChar.charP _)
  exact ringChar.eq _ _

theorem closeds_finite_int : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (T : Closeds X), (∀ ℓ : ℕ, ((T : Set X) ∩ fib X ℓ).Finite) →
    IsAffine (Scheme.IdealSheafData.vanishingIdeal T).subscheme ∧
      Module.Finite ℤ Γ((Scheme.IdealSheafData.vanishingIdeal T).subscheme, ⊤) := by
  intro k _ X _ p D hX T hT
  set I := Scheme.IdealSheafData.vanishingIdeal T with hI
  have hr : Set.range I.subschemeι = (T : Set X) := by
    rw [Scheme.IdealSheafData.range_subschemeι, hI, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  obtain ⟨N, j, _, hj⟩ := hX.isProjOver
  have := isProper_str k N
  have : IsProper p := hj ▸ inferInstance
  have : IsFinite (spMap (Int.castRingHom k)) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 hX.finite)
  set q := I.subschemeι ≫ p ≫ spMap (Int.castRingHom k) with hq
  have : IsProper q := by rw [hq]; infer_instance
  have : LocallyQuasiFinite q := by
    refine LocallyQuasiFinite.of_finite_preimage_singleton _ fun y => ?_
    have hfin := hT (ringChar ((Sp ℤ).residueField y))
    refine Set.Finite.of_finite_image (f := I.subschemeι) (hfin.subset ?_)
      (I.subschemeι.isClosedEmbedding.injective.injOn)
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨hr.le ⟨z, rfl⟩, ?_⟩
    show ringChar _ = _
    rw [ringChar_residueField_eq (p ≫ spMap (Int.castRingHom k)) (I.subschemeι z)]
    have e : (p ≫ spMap (Int.castRingHom k)) (I.subschemeι z) = y := by
      rw [← hz, hq]; rfl
    rw [e]
  have : IsFinite q := IsFinite.of_isProper_of_locallyQuasiFinite q
  have hA : IsAffine I.subscheme := isAffine_of_isAffineHom q
  refine ⟨hA, ?_⟩
  have hf : (q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv.hom).Finite :=
    q.finite_appTop.comp (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv).2)
  rw [RingHom.ext_int (q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv.hom)
    (algebraMap ℤ Γ(I.subscheme, ⊤)), RingHom.finite_algebraMap] at hf
  exact hf

end GlobalTheory.HSAmp
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp

theorem exists_volDens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → GenSmooth p D → ∀ σ : k →+* ℂ, Nonempty (VolDens p σ D) := by
  intro k _ X _ p D hX hS σ
  haveI := hX.compactSpace σ
  haveI := CxPts.t2Space_cxPts_of_isProjOver σ hX.isProjOver
  obtain ⟨R⟩ := hS σ
  obtain ⟨s, hs⟩ := R.exists_finite
  obtain ⟨f, hf⟩ := PartitionOfUnity.exists_isSubordinate (X := CxPts p σ) (ι := s) isClosed_univ
    (fun i => (R.chart i.1).e.source) (fun i => (R.chart i.1).e.open_source)
    (fun y _ => by
      obtain ⟨i, hi, hy⟩ := hs y
      exact Set.mem_iUnion.2 ⟨⟨i, hi⟩, hy⟩)
  have hsrc : ∀ (i : s) (y : CxPts p σ), f i y ≠ 0 → y ∈ (R.chart i.1).e.source := fun i y h =>
    hf i (subset_tsupport _ h)
  refine ⟨{ dens := fun c y => ∑ i : s, f i y * ‖ChartGlue.transDet c.e (R.chart i.1).e y‖ ^ 2
            cont := fun c => ?_
            pos := fun c y hy => ?_
            trans := fun c c' y hy hy' => ?_ }⟩
  · refine continuousOn_finsetSum _ fun i _ => fun y hy => ContinuousAt.continuousWithinAt ?_
    by_cases h : y ∈ tsupport (f i)
    · exact (f i).continuous.continuousAt.mul
        ((CurveDens.continuousAt_transDet_chart c _ hy (hf i h)).norm.pow 2)
    · refine (continuousAt_const (y := (0 : ℝ))).congr ?_
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 h] with z hz
      rw [hz, Pi.zero_apply, zero_mul]
  · obtain ⟨i, hi⟩ := f.exists_pos (Set.mem_univ y)
    refine Finset.sum_pos' (fun j _ => mul_nonneg (f.nonneg j y) (sq_nonneg _))
      ⟨i, Finset.mem_univ _, mul_pos hi (pow_pos (norm_pos_iff.2 ?_) 2)⟩
    exact CurveDens.transDet_chart_ne_zero c _ hy (hsrc i y hi.ne')
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : f i y = 0
    · simp [h]
    · rw [CurveDens.transDet_trans_chart c c' _ hy hy' (hsrc i y h), norm_mul, mul_pow]
      ring

end GlobalTheory.HSAmp
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp.CanSmooth

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {y : CxPts p σ}

theorem cInfAt_log {f : CxPts p σ → ℝ} (h : CInfAt f y) (hpos : 0 < f y) :
    CInfAt (fun z => Real.log (f z)) y := by
  obtain ⟨W, ι, _, g, F, O, h₁, h₂, h₃, h₄, h₅⟩ := h
  have hFy : 0 < F (fun a => ev p σ W (g a) y) := h₅.eq_of_nhds ▸ hpos
  refine ⟨W, ι, inferInstance, g, fun v => Real.log (F v), O ∩ F ⁻¹' Set.Ioi 0, h₁,
    h₄.continuousOn.isOpen_inter_preimage h₂ isOpen_Ioi, ⟨h₃, hFy⟩,
    (h₄.mono Set.inter_subset_left).log fun v hv => (ne_of_gt hv.2), ?_⟩
  filter_upwards [h₅] with z hz
  rw [hz]

theorem cInfAt_sum {ι : Type} [DecidableEq ι] (s : Finset ι) {f : ι → CxPts p σ → ℝ}
    (h : ∀ l ∈ s, CInfAt (f l) y) : CInfAt (fun z => ∑ l ∈ s, f l z) y := by
  induction s using Finset.induction_on with
  | empty => simpa using cInfAt_const (p := p) (0 : ℝ) y
  | insert a s ha ih =>
    have e : (fun z => ∑ l ∈ insert a s, f l z) = fun z => f a z + ∑ l ∈ s, f l z :=
      funext fun z => Finset.sum_insert ha
    rw [e]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun l hl => h l (Finset.mem_insert_of_mem hl))

theorem cInfAt_normSq_ratVal [IsIntegral X] {g : X.functionField} (hg : RegAt (under y) g) :
    CInfAt (fun z : CxPts p σ => ‖ratVal g z‖ ^ 2) y := by
  obtain ⟨U, hU, a, rfl⟩ := hg.exists_fnOf
  have hyU : y ∈ ptsIn p σ U := mem_ptsIn.2 hU
  have h₁ : CInfAt (fun z => ‖ev p σ U a z‖ ^ 2) y :=
    ⟨U, Unit, inferInstance, fun _ => a, fun v => ‖v ()‖ ^ 2, Set.univ, hyU, isOpen_univ, trivial,
      ((contDiff_apply ℝ (fun _ => ℂ) ()).norm_sq ℂ).contDiffOn, EventuallyEq.rfl⟩
  refine h₁.congr ?_
  filter_upwards [(isOpen_ptsIn U).mem_nhds hyU] with z hz
  rw [ratVal_fnOf hz]

end GlobalTheory.HSAmp.CanSmooth

namespace GlobalTheory.HSAmp


open CanSmooth in
theorem cInfAt_canWeight : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p) (D e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∀ n : ℕ, 1 ≤ n → ∀ (σ : k →+* ℂ) (y : CxPts p σ), CInfAt (fun z : CxPts p σ => ((e : ℝ) * n)⁻¹ * Real.log (∑ l, P.nu e 0 σ z (x l) ^ (2 * n))) y := by
  intro k _ X _ p P D e x hx n _ σ y
  set i := pick (P.L.φ σ).isLB y
  set j := pick (P.A.φ σ).isLB y
  have hi : y ∈ ptsIn p σ (P.L.B.U i) := mem_pick _ y
  have hj : y ∈ ptsIn p σ (P.A.B.U j) := mem_pick _ y
  have hφ : CInfAt ((P.L.φ σ).φ i) y := P.L.cInf σ i y hi
  have hterm : ∀ l, CInfAt (fun z => P.nu e 0 σ z (x l) ^ (2 * n)) y := by
    intro l
    have hreg : RegAt (under y) (P.loc e 0 (x l) i j) := hx.mem l _ i j (mem_ptsIn.1 hi) (mem_ptsIn.1 hj)
    have h₂ := (cInfAt_normSq_ratVal hreg).comp₂ hφ
      (G := fun w => w.1 ^ n * Real.exp (-((e : ℝ) * n) * w.2))
      ((contDiff_fst.pow n).mul ((contDiff_const.mul contDiff_snd).exp))
    refine h₂.congr ?_
    filter_upwards [(isOpen_ptsIn _).mem_nhds hi, (isOpen_ptsIn _).mem_nhds hj] with z hzi hzj
    rw [nu_eq k X p P e 0 (x l) (hx.mem l) σ z i j hzi hzj, mul_pow, pow_mul, ← Real.exp_nat_mul]
    congr 2
    push_cast
    ring
  have hsum : CInfAt (fun z => ∑ l, P.nu e 0 σ z (x l) ^ (2 * n)) y :=
    cInfAt_sum Finset.univ fun l _ => hterm l
  obtain ⟨l₀, hl₀⟩ := hx.cover (under y)
  have hpos₀ : 0 < P.nu e 0 σ y (x l₀) :=
    mul_pos (norm_pos_iff.2 (ratVal_ne_zero (hl₀ _ _ (mem_ptsIn.1 hi) (mem_ptsIn.1 hj)))) (Real.exp_pos _)
  have hpos : 0 < ∑ l, P.nu e 0 σ y (x l) ^ (2 * n) :=
    lt_of_lt_of_le (pow_pos hpos₀ _)
      (Finset.single_le_sum (f := fun l => P.nu e 0 σ y (x l) ^ (2 * n))
        (fun l _ => (even_two_mul n).pow_nonneg _) (Finset.mem_univ l₀))
  exact (cInfAt_log hsum hpos).const_mul _

end GlobalTheory.HSAmp
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp


open GlobalTheory.VolBr.NuEq in
theorem val_frame : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) i j, y ∈ ptsIn p σ (P.L.B.U i) → y ∈ ptsIn p σ (P.A.B.U j) → ∃ θ : ℂ, ‖θ‖ = 1 ∧ ∀ f ∈ P.H a b, val P a b σ y f = θ * (ratVal (P.loc a b f i j) y * (Real.exp (-(a * (P.L.φ σ).φ i y + b * (P.A.φ σ).φ j y) / 2) : ℝ)) := by
  intro k _ X _ p P a b σ y i j hi hj
  have hi₀ : y ∈ ptsIn p σ (P.L.B.U (pick (P.L.φ σ).isLB y)) := mem_pick _ y
  have hj₀ : y ∈ ptsIn p σ (P.A.B.U (pick (P.A.φ σ).isLB y)) := mem_pick _ y
  have hii := mem_ptsIn_inf.2 ⟨hi, hi₀⟩
  have hjj := mem_ptsIn_inf.2 ⟨hj, hj₀⟩
  have gi := gen_mem (mem_ptsIn.1 hii)
  have gj := gen_mem (mem_ptsIn.1 hjj)
  have uG := unitAt_fnOf (mem_ptsIn.1 hii) gi (P.L.B.g i (pick (P.L.φ σ).isLB y))
  have uG' := unitAt_fnOf (mem_ptsIn.1 hjj) gj (P.A.B.g j (pick (P.A.φ σ).isLB y))
  have uGa := unitAt_zpow uG a
  have uGb := unitAt_zpow uG' b
  have eG := ratVal_fnOf hii gi (P.L.B.g i (pick (P.L.φ σ).isLB y) : Γ(X, _))
  have eG' := ratVal_fnOf hjj gj (P.A.B.g j (pick (P.A.φ σ).isLB y) : Γ(X, _))
  have hL : CxPts.gv p σ P.L.B i (pick (P.L.φ σ).isLB y) y ≠ 0 := by
    rw [CxPts.gv, ← eG]; exact ratVal_ne_zero uG
  have hA : CxPts.gv p σ P.A.B j (pick (P.A.φ σ).isLB y) y ≠ 0 := by
    rw [CxPts.gv, ← eG']; exact ratVal_ne_zero uG'
  set gL := CxPts.gv p σ P.L.B i (pick (P.L.φ σ).isLB y) y with hgL
  set gA := CxPts.gv p σ P.A.B j (pick (P.A.φ σ).isLB y) y with hgA
  have hG : gL ^ a * gA ^ b ≠ 0 := mul_ne_zero (zpow_ne_zero _ hL) (zpow_ne_zero _ hA)
  have hGn : (‖gL ^ a * gA ^ b‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hG)
  refine ⟨(‖gL ^ a * gA ^ b‖ : ℂ) / (gL ^ a * gA ^ b), ?_, ?_⟩
  · rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 hG)]
  intro f hf
  have hreg : RegAt (under y) (P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y)) :=
    hf _ _ _ (mem_ptsIn.1 hi₀) (mem_ptsIn.1 hj₀)
  have hloc : P.loc a b f i j =
      ((fnOf _ gi (P.L.B.g i (pick (P.L.φ σ).isLB y) : Γ(X, _))) ^ a *
        (fnOf _ gj (P.A.B.g j (pick (P.A.φ σ).isLB y) : Γ(X, _))) ^ b) *
        P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y) := by
    simp only [Pair.loc]
    rw [P.hr i _ gi, P.hr' j _ gj, mul_zpow, mul_zpow]
    ring
  have hrv : ratVal (P.loc a b f i j) y =
      gL ^ a * gA ^ b * ratVal (P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y)) y := by
    rw [hloc, ratVal_mul (uGa.mul uGb).regAt hreg, ratVal_mul uGa.regAt uGb.regAt,
      ratVal_zpow' uG, ratVal_zpow' uG', eG, eG']
    rfl
  have c0 : 0 < ‖gL‖ := norm_pos_iff.2 hL
  have c0' : 0 < ‖gA‖ := norm_pos_iff.2 hA
  have hexp : Real.exp (-(a * (P.L.φ σ).φ i y + b * (P.A.φ σ).φ j y) / 2) =
      ‖gL ^ a * gA ^ b‖⁻¹ * Real.exp (-(a * (P.L.φ σ).φ (pick (P.L.φ σ).isLB y) y +
        b * (P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y) / 2) := by
    rw [(P.L.φ σ).trans i _ y hi hi₀, (P.A.φ σ).trans j _ y hj hj₀, norm_mul, norm_zpow, norm_zpow,
      ← Real.rpow_intCast, ← Real.rpow_intCast, Real.rpow_def_of_pos c0, Real.rpow_def_of_pos c0',
      Real.log_pow, Real.log_pow, ← hgL, ← hgA, ← Real.exp_add, ← Real.exp_neg, ← Real.exp_add]
    congr 1
    push_cast
    ring
  rw [val, hrv, hexp]
  push_cast
  field_simp

end GlobalTheory.HSAmp
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false
noncomputable section

theorem GlobalTheory.HSAmp.pow_sec_dict : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ e : ℕ, (∀ u : (lbPow P.L.B e).Sec, ∃ f ∈ P.H e 0, NV P e 0 f = ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u) ∧ ∀ f ∈ P.H e 0, ∃ u : (lbPow P.L.B e).Sec, NV P e 0 f = ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u := by
  intro k _ X _ p P e
  have hR : P.Rep ((e : ℤ) * 1) ((e : ℤ) * 0) (P.L.pow e) :=
    GlobalTheory.VolBr.Pair.rep_pow k X p P 1 0 P.L e (GlobalTheory.VolBr.Pair.rep_base k X p P).1
  rw [mul_one, mul_zero] at hR
  obtain ⟨g, -, hrange, -, hloc⟩ := GlobalTheory.VolBr.RepDict.rep_dict k X p P (e : ℤ) 0 (P.L.pow e) hR
  have hcov {B : LB X} (hB : B.IsLB) (x : X) : ∃ c, x ∈ B.U c :=
    Opens.mem_iSup.1 (hB.cover.ge (Opens.mem_top _))
  have key : ∀ u : (lbPow P.L.B e).Sec, NV P e 0 (g u) = (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u : Set X) := by
    intro u
    ext x
    obtain ⟨i, hi⟩ := hcov P.L.isLB x
    obtain ⟨j, hj⟩ := hcov P.A.isLB x
    constructor
    · intro h
      exact (hloc u x i j hi hj).2 (h i j hi hj)
    · intro h i' j' hi' hj'
      exact (hloc u x i' j' hi' hj').1 h
  refine ⟨fun u => ⟨g u, ?_, key u⟩, fun f hf => ?_⟩
  · have : g u ∈ Set.range g := ⟨u, rfl⟩
    rw [hrange] at this
    exact this
  · have : f ∈ Set.range g := by rw [hrange]; exact hf
    obtain ⟨u, rfl⟩ := this
    exact ⟨u, key u⟩
end
end

section

open Filter Topology MvPolynomial GlobalTheory.HSAmp

set_option autoImplicit false

namespace GlobalTheory.HSAmp.TraceHom

theorem trace_homog : ∀ (K : Type) [Field K] [CharZero K] (D : ℕ) (x : Fin (D + 1) → K), (∀ j, x j ≠ 0) →
    AlgebraicIndependent ℤ (fun j : Fin D => x j.succ / x 0) → FiniteDimensional (ratF x) K →
    ∀ (q : ℕ) (w : K), (∀ l, IsIntegral (ratR x l) (w / x l ^ q)) →
    ∃ T : MvPolynomial (Fin (D + 1)) ℤ, T.IsHomogeneous q ∧
      (Algebra.trace (ratF x) K (w / x 0 ^ q) : K) = aeval (fun l => x l / x 0) T := by
  intro K _ _ D x hx hind hfd q w hint
  set y : Fin D → K := fun j => x j.succ / x 0 with hydef
  have hyF : ∀ j, y j ∈ ratF x := fun j => Subfield.subset_closure ⟨j, rfl⟩
  have hzF : ∀ l k, x k / x l ∈ ratF x := by
    intro l k
    have e : ∀ k, x k / x 0 ∈ ratF x := by
      intro k
      refine Fin.cases ?_ (fun i => hyF i) k
      rw [div_self (hx 0)]; exact one_mem _
    have : x k / x l = (x k / x 0) / (x l / x 0) := by field_simp [hx 0, hx l]
    rw [this]; exact div_mem (e k) (e l)
  set t : K := (Algebra.trace (ratF x) K (w / x 0 ^ q) : K) with htdef

  obtain ⟨f₀, hf₀, hft₀⟩ := GlobalTheory.T.exists_monic_root_trace_of_isIntegral_closure (ratF x) (fun k => x k / x 0) (hzF 0) _ (hint 0)
  have hz0 : ∀ k, ∃ p : MvPolynomial (Fin D) ℤ, aeval y p = x k / x 0 := by
    intro k
    refine Fin.cases ⟨1, ?_⟩ (fun i => ⟨X i, by simp [y]⟩) k
    rw [map_one, div_self (hx 0)]
  obtain ⟨T₀, hT₀⟩ := GlobalTheory.T.mem_polyring_of_integral_closure_range' y hind t (Algebra.trace (ratF x) K (w / x 0 ^ q)).2 _ hz0 f₀ hf₀ hft₀

  have hdeg : T₀.totalDegree ≤ q := by
    rcases Nat.eq_zero_or_pos D with hD | hD
    · subst hD
      rw [MvPolynomial.eq_C_of_isEmpty T₀, totalDegree_C]; exact Nat.zero_le _
    · set j : Fin D := ⟨0, hD⟩
      have hyj : y j ≠ 0 := div_ne_zero (hx _) (hx 0)
      obtain ⟨f₁, hf₁, hft₁⟩ := GlobalTheory.T.exists_monic_root_trace_of_isIntegral_closure (ratF x) (fun k => x k / x j.succ) (hzF j.succ) _ (hint j.succ)
      have hc : (⟨(x 0 / x j.succ) ^ q, pow_mem (hzF _ 0) q⟩ : ratF x) • (w / x 0 ^ q) = w / x j.succ ^ q := by
        rw [Subfield.smul_def]; simp only [smul_eq_mul, div_pow]; field_simp [hx 0, hx j.succ] <;> ring
      have htr : (Algebra.trace (ratF x) K (w / x j.succ ^ q) : K) = aeval y T₀ / y j ^ q := by
        rw [← hc, LinearMap.map_smul, smul_eq_mul, Subfield.coe_mul, ← htdef, hT₀]
        simp only [y, j, div_pow]; field_simp [hx 0, hx _] <;> ring
      rw [htr] at hft₁
      refine GlobalTheory.T.totalDegree_le_of_root_of_monic_eval y hind j hyj T₀ q _ ?_ f₁ hf₁ hft₁
      intro k
      refine Fin.cases ⟨1, 1, by simp, ?_⟩ (fun i => ⟨1, X i, ?_, ?_⟩) k
      · simp only [y, pow_one, map_one]; field_simp [hx 0, hx _]
      · simp [totalDegree_X]
      · simp only [y, pow_one, aeval_X]; field_simp [hx 0, hx _]
  obtain ⟨T, hT, hTa⟩ := GlobalTheory.T.exists_isHomogeneous_aeval_eq_of_first_eq_one T₀ q hdeg
  refine ⟨T, hT, ?_⟩
  rw [hTa K _ (div_self (hx 0)), ← hT₀]

end GlobalTheory.HSAmp.TraceHom
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

namespace GlobalTheory.FnInt

theorem main : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∀ (l : Fin (D + 1)) (w : X.functionField), x l ≠ 0 → (∀ z ∈ NV P e 0 (x l), RegAt z w) → IsIntegral (ratR x l) w := by
  intro k _ X _ p D hA P e x hG l w hl hw
  have : IsProper p := by
    obtain ⟨m, i, hi, rfl⟩ := hA.isProjOver
    have := isProper_str k m
    infer_instance
  have hmem : w ∈ (integralClosure (Subring.closure (Set.range fun j => x j / x l)) X.functionField).toSubring := by
    rw [← iInf_valuationSubring_superset, Subring.mem_iInf]
    rintro ⟨V, hV⟩
    change w ∈ V
    have hk : ∀ a : k, toFunctionField p a ∈ V := by
      intro a
      have := hA.finite
      have h1 : IsIntegral ℤ (toFunctionField p a) :=
        (Algebra.IsIntegral.isIntegral (R := ℤ) a).map (toFunctionField p).toIntAlgHom
      have h2 : IsIntegral V (toFunctionField p a) := h1.tower_top
      obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
      rw [← hy]; exact y.2
    have hd := dominatesStalk_centre p V hk
    obtain ⟨j, hj⟩ := hG.cover (centre p V hk)
    have hz : centre p V hk ∈ NV P e 0 (x l) := by
      intro i i' hi hi'
      have hu := hj i i' hi hi'
      have hr := hG.mem l (centre p V hk) i i' hi hi'
      have hne := hu.ne_zero
      have hxj : x j ≠ 0 := fun h0 => hne (by simp [Pair.loc, h0])
      have hloc : P.loc (e : ℤ) 0 (x l) i i' = x l / x j * P.loc (e : ℤ) 0 (x j) i i' := by
        simp only [Pair.loc]; field_simp
      have hg : RegAt (centre p V hk) (x l / x j) := by
        have : x l / x j = P.loc (e : ℤ) 0 (x l) i i' * (P.loc (e : ℤ) 0 (x j) i i')⁻¹ := by
          rw [hloc, mul_assoc, mul_inv_cancel₀ hne, mul_one]
        rw [this]; exact hr.mul hu.inv.regAt
      have hgu : UnitAt (centre p V hk) (x l / x j) := by
        by_contra hn
        obtain ⟨a, ha, hag⟩ := zeroAt_iff.2 ⟨hg, hn⟩
        have h1 := hd.2 a ha
        rw [hag] at h1
        have hgV : x l / x j ∈ V := by rw [← hag]; exact hd.1 a
        have h2 : (x l / x j)⁻¹ ∈ V := by
          rw [inv_div]; exact hV ⟨j, rfl⟩
        have hgne : x l / x j ≠ 0 := div_ne_zero hl hxj
        have hu' : IsUnit (⟨x l / x j, hgV⟩ : V) := by
          refine ⟨⟨⟨_, hgV⟩, ⟨_, h2⟩, Subtype.ext (mul_inv_cancel₀ hgne), Subtype.ext (inv_mul_cancel₀ hgne)⟩, rfl⟩
        exact (V.coe_mem_nonunits_iff (a := ⟨_, hgV⟩)).mp h1 hu'
      rw [hloc]; exact hgu.mul hu
    obtain ⟨a, ha⟩ := hw _ hz
    rw [← ha]; exact hd.1 a
  exact hmem

end GlobalTheory.FnInt
end

end

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

theorem _root_.GlobalTheory.T.closedSubset_finiteFibres_isAffine_finite_int : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (T : Closeds X), (∀ ℓ : ℕ, ((T : Set X) ∩ fib X ℓ).Finite) → IsAffine (Scheme.IdealSheafData.vanishingIdeal T).subscheme ∧ Module.Finite ℤ Γ((Scheme.IdealSheafData.vanishingIdeal T).subscheme, ⊤) := by
  first | exact @GlobalTheory.HSAmp.closeds_finite_int | exact GlobalTheory.HSAmp.closeds_finite_int | (intros; apply GlobalTheory.HSAmp.closeds_finite_int <;> assumption)

end
end

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

theorem _root_.GlobalTheory.T.complexPointsSmoothAt_fubiniStudy_log_sum_weight : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p) (D e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∀ n : ℕ, 1 ≤ n → ∀ (σ : k →+* ℂ) (y : CxPts p σ), CInfAt (fun z : CxPts p σ => ((e : ℝ) * n)⁻¹ * Real.log (∑ l, P.nu e 0 σ z (x l) ^ (2 * n))) y := by
  first | exact @GlobalTheory.HSAmp.cInfAt_canWeight | exact GlobalTheory.HSAmp.cInfAt_canWeight | (intros; apply GlobalTheory.HSAmp.cInfAt_canWeight <;> assumption)

end
end
