module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle009

@[expose] public section

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial ReciprocityTheory.AnForm.M Filter Topology MeasureTheory
open scoped ContDiff

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def HermLine.inv (B : HermLine ι) : HermLine ι where
  a := -B.a
  h z := (B.h z)⁻¹
  pos z hz := inv_pos.mpr (B.pos z hz)
  smul c z hc := by
    rw [B.smul c z hc, mul_inv, ← Finset.prod_inv_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Pi.neg_apply, zpow_neg]

theorem logNorm_inv_one (B : HermLine ι) (z : (Σ k, ι k) → ℂ) :
    logNorm B.inv 1 z = Real.log (B.h z) := by
  simp [logNorm, HermLine.inv]

theorem isSmoothHerm_inv {B : HermLine ι} (hB : IsSmoothHerm B) : IsSmoothHerm B.inv := (show ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) B.h {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} from hB).inv
  fun z hz => (B.pos z hz).ne'

theorem isSectionOn_inv_one {P : Ideal (MRing ι)} (hP : P.IsPrime) {B : HermLine ι}
    (hB : B.a = 0) : IsSectionOn P B.inv 1 := by
  classical
  refine ⟨0, fun k => ?_, ?_, ?_⟩
  · simp [HermLine.inv, hB]
  · intro m hm k
    have hm0 : m = 0 := by
      by_contra h
      exact (MvPolynomial.mem_support_iff.1 hm) (by rw [MvPolynomial.coeff_one, if_neg (Ne.symm h)])
    subst hm0
    simp
  · intro h
    exact hP.ne_top ((Ideal.eq_top_iff_one P).2 h)

theorem h_eq_of_sameOrbit {B : HermLine ι} (hB : B.a = 0) {z z' : (Σ k, ι k) → ℂ}
    (h : SameOrbit z z') : B.h z = B.h z' := by
  obtain ⟨c, hc, rfl⟩ := h
  rw [B.smul c z' hc, hB]
  simp

theorem maDens_congr {D : ℕ} {φ ψ : Fin D → (Fin D → ℂ) → ℝ} {z : Fin D → ℂ}
    (h : ∀ i, φ i =ᶠ[𝓝 z] ψ i) : ReciprocityTheory.AnForm.maDens φ z = ReciprocityTheory.AnForm.maDens ψ z := by
  have hH : ∀ i, ReciprocityTheory.AnForm.hessC (φ i) z = ReciprocityTheory.AnForm.hessC (ψ i) z := by
    intro i
    have h2 : fderiv ℝ (fderiv ℝ (φ i)) z = fderiv ℝ (fderiv ℝ (ψ i)) z :=
      ((h i).fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
    unfold ReciprocityTheory.AnForm.hessC
    rw [h2]
  simp only [ReciprocityTheory.AnForm.maDens, hH]

theorem mInt_congr {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    {Φ Φ' : Fin e → LocPot X} {g g' : X → ℝ}
    (hΦ : ∀ j, ∀ y ∈ (A.chart j).target, locDens A Φ j y = locDens A Φ' j y)
    (hg : ∀ x, g x = g' x) : mInt A Φ g = mInt A Φ' g' := by
  unfold ReciprocityTheory.AnForm.M.mInt
  by_cases h : Nonempty (ChartPartition A)
  · rw [dite_eq_left h, dite_eq_left h]
    unfold ReciprocityTheory.AnForm.M.integralWith
    refine Finset.sum_congr rfl fun j _ => ?_
    refine MeasureTheory.setIntegral_congr_fun (A.chart j).open_target.measurableSet fun y hy => ?_
    simp only [hg, hΦ j y hy]
  · rw [dite_eq_right h, dite_eq_right h]

theorem locDens_cons_congr {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas (e + 1) X)
    {Q Q' : LocPot X} (Φ : Fin e → LocPot X)
    (h : ∀ j, ∀ y ∈ (A.chart j).target, (fun y' => Q.φ ((A.chart j).symm y) ((A.chart j).symm y'))
      =ᶠ[𝓝 y] fun y' => Q'.φ ((A.chart j).symm y) ((A.chart j).symm y')) :
    ∀ j, ∀ y ∈ (A.chart j).target,
      locDens A (Fin.cons Q Φ) j y = locDens A (Fin.cons Q' Φ) j y := by
  intro j y hy
  unfold ReciprocityTheory.AnForm.M.locDens
  apply maDens_congr
  intro i
  induction i using Fin.cases with
  | zero =>
    simp only [Fin.cons_zero]
    exact h j y hy
  | succ i =>
    simp only [Fin.cons_succ]
    exact Filter.EventuallyEq.rfl

variable {P J : Ideal (MRing ι)} {e : ℕ}

theorem contDiffOn_lift (R : AnLogRes P J e) (x : R.X) (j : Fin R.A.n) :
    ContDiffOn ℝ ∞ (fun y => R.lift x ((R.A.chart j).symm y))
      ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x) := by
  have hopen : IsOpen ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x) :=
    (R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x)
  rw [contDiffOn_pi]
  intro p
  exact ((R.holo x p j).contDiffOn hopen.uniqueDiffOn).restrict_scalars ℝ

theorem contDiffOn_potOf (R : AnLogRes P J e) {L : HermLine ι} (hL : IsSmoothHerm L) (x : R.X)
    (j : Fin R.A.n) :
    ContDiffOn ℝ ∞ (fun y => Real.log (L.h (R.lift x ((R.A.chart j).symm y))))
      ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x) := by
  have hl := contDiffOn_lift R x j
  have hmaps : Set.MapsTo (fun y => R.lift x ((R.A.chart j).symm y))
      ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
    fun y hy => (R.mem x _ hy.2).1
  have hL' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) L.h {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := hL
  exact (hL'.comp hl hmaps).log fun y hy => (L.pos _ (hmaps hy)).ne'

theorem smoothOn_potOf (R : AnLogRes P J e) {L : HermLine ι} (hL : IsSmoothHerm L) (x : R.X) :
    R.A.SmoothOn ((potOf R L).U x) ((potOf R L).φ x) := fun j => contDiffOn_potOf R hL x j

theorem smooth_diag (R : AnLogRes P J e) {B : HermLine ι} (hB : IsSmoothHerm B) (hB0 : B.a = 0) :
    R.A.Smooth (fun x => Real.log (B.h (R.lift x x))) := by
  intro j
  apply contDiffOn_of_locally_contDiffOn
  intro y hy
  have hyt : y ∈ (R.A.chart j).target := hy.1
  refine ⟨(R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U ((R.A.chart j).symm y),
    (R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U _), ⟨hyt, R.mem_U _⟩, ?_⟩
  have hc := contDiffOn_potOf R hB ((R.A.chart j).symm y) j
  refine (hc.mono Set.inter_subset_right).congr fun y' hy' => ?_
  change Real.log (B.h (R.lift ((R.A.chart j).symm y') ((R.A.chart j).symm y'))) =
    Real.log (B.h (R.lift ((R.A.chart j).symm y) ((R.A.chart j).symm y')))
  rw [h_eq_of_sameOrbit hB0 (R.compat _ _ _ ⟨R.mem_U _, hy'.2.2⟩)]

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial ReciprocityTheory.AnForm.M

theorem isMultiHomog_X {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    (q : Σ k, ι k) :
    IsMultiHomog (X q : MRing ι) (fun k => ∑ i, (Finsupp.single q 1 : (Σ k, ι k) →₀ ℕ) ⟨k, i⟩) := by
  intro m hm k
  rw [MvPolynomial.support_X, Finset.mem_singleton] at hm
  subst hm
  rfl

theorem isMultiHomogIdeal_span_X {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    (q : Σ k, ι k) : IsMultiHomogIdeal (Ideal.span {(X q : MRing ι)}) := by
  refine ⟨{X q}, ?_, rfl⟩
  rintro f rfl
  exact ⟨_, isMultiHomog_X q⟩

theorem exists_anLogRes (hE : ResExistsStatement) {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {e : ℕ} (hP : IsArithVar P (e + 1)) :
    ∃ J : Ideal (MRing ι), Nonempty (AnLogRes P J e) := by
  obtain ⟨⟨k⟩, ⟨-, -, hrel⟩, -, -⟩ := id hP
  obtain ⟨i, hi⟩ := hrel k
  obtain ⟨J', -, -, -, hR⟩ := hE K ι P (Ideal.span {(X ⟨k, i⟩ : MRing ι)}) e hP
    (isMultiHomogIdeal_span_X _) (fun h => hi (h (Ideal.mem_span_singleton_self _)))
  exact ⟨J', hR⟩

theorem ptsIndep_of (hE : ResExistsStatement) (hB : ResBridgeStatement) : PtsIndepStatement := by
  intro K _ ι _ P e Ψ Ψ' L A s hP hΨ hΨ' hL hA hs
  obtain ⟨J, ⟨R⟩⟩ := exists_anLogRes hE hP
  rw [hB K ι P J e R Ψ L A s hP hΨ hL hA hs, hB K ι P J e R Ψ' L A s hP hΨ' hL hA hs]

theorem ptsIntegral_eq_at (hE : ResExistsStatement) (hB : ResBridgeStatement) {K : Type}
    [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {e : ℕ}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {L : Fin e → HermLine ι}
    {A : HermLine ι} {s : MRing ι} (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ)
    (hL : ∀ j, IsSmoothHerm (L j)) (hA : IsSmoothHerm A) (hs : IsSectionOn P A s) :
    ptsIntegral P (pot L) (logNorm A s) = ptsIntegralAt P Ψ (pot L) (logNorm A s) := by
  have hex : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P Ψ := ⟨Ψ, hΨ⟩
  unfold ptsIntegral
  rw [dite_eq_left hex]
  exact ptsIndep_of hE hB K ι P e _ _ L A s hP hex.choose_spec hΨ hL hA hs

theorem ptsIntegral_eq_mInt (hE : ResExistsStatement) (hB : ResBridgeStatement)
    (hG : GoodProjExistsStatement) {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e) {L : Fin e → HermLine ι}
    {A : HermLine ι} {s : MRing ι} (hP : IsArithVar P (e + 1)) (hL : ∀ j, IsSmoothHerm (L j))
    (hA : IsSmoothHerm A) (hs : IsSectionOn P A s) :
    ptsIntegral P (pot L) (logNorm A s) =
      mInt R.A (fun j => potOf R (L j)) (fun x => logNorm A s (R.lift x x)) := by
  obtain ⟨Ψ, hΨ⟩ := hG K ι P e hP
  rw [ptsIntegral_eq_at hE hB hP hΨ hL hA hs]
  exact hB K ι P J e R Ψ L A s hP hΨ hL hA hs

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

noncomputable section

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

def scaleBlock (k0 : K) (c : ℂ) (z : (Σ k, ι k) → ℂ) : (Σ k, ι k) → ℂ :=
  fun p => (if p.1 = k0 then c else 1) * z p

theorem eval_scaleBlock (k0 : K) (c : ℂ) (z : (Σ k, ι k) → ℂ) (f : MRing ι) (a : K → ℕ)
    (hf : IsMultiHomog f a) :
    eval (scaleBlock k0 c z) (map (Int.castRingHom ℂ) f) =
      c ^ a k0 * eval z (map (Int.castRingHom ℂ) f) := by
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' : m ∈ f.support := MvPolynomial.support_map_subset _ _ hm
  have hdeg := hf m hm' k0
  simp only [scaleBlock, mul_pow, Finset.prod_mul_distrib]
  have hc : ∏ x : (Σ k, ι k), (if x.1 = k0 then c else 1) ^ m x = c ^ a k0 := by
    rw [Fintype.prod_sigma, Finset.prod_eq_single k0]
    · simp [hdeg, Finset.prod_pow_eq_pow_sum]
    · intro k _ hk
      simp [hk]
    · simp
  rw [hc]
  ring

theorem scaleBlock_mem_zeroLocus (P : Ideal (MRing ι)) (hP : IsMultiHomogIdeal P) (k0 : K) {c : ℂ} (hc : c ≠ 0)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) : scaleBlock k0 c z ∈ mcPts P := by
  obtain ⟨S, hS, rfl⟩ := hP
  show (∀ k, ∃ i, scaleBlock k0 c z ⟨k, i⟩ ≠ 0) ∧
    ∀ f ∈ Ideal.span S, eval (scaleBlock k0 c z) (map (Int.castRingHom ℂ) f) = 0
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 k
    refine ⟨i, ?_⟩
    simp only [scaleBlock]
    split_ifs <;> simp [hc, hi]
  · have hle : Ideal.span S ≤ RingHom.ker ((eval (scaleBlock k0 c z)).comp (map (Int.castRingHom ℂ))) := by
      rw [Ideal.span_le]
      intro s hs
      obtain ⟨a, ha⟩ := hS s hs
      simp only [SetLike.mem_coe, RingHom.mem_ker, RingHom.comp_apply]
      rw [eval_scaleBlock k0 c z s a ha, hz.2 s (Ideal.subset_span hs), mul_zero]
    exact (RingHom.mem_ker).mp (hle hf)

def evQ (P : Ideal (MRing ι)) (z : (Σ k, ι k) → ℂ) (hz : z ∈ mcPts P) :
    MvPolynomial (Σ k, ι k) ℚ ⧸ qIdeal P →+* ℂ :=
  Ideal.Quotient.lift (qIdeal P) (eval₂Hom (algebraMap ℚ ℂ) z) fun a ha => by
    have hle : qIdeal P ≤ RingHom.ker (eval₂Hom (algebraMap ℚ ℂ) z) := by
      refine Ideal.map_le_iff_le_comap.mpr fun f hf => ?_
      rw [Ideal.mem_comap, RingHom.mem_ker, coe_eval₂Hom, eval₂_map]
      have h := hz.2 f hf
      rw [eval_map] at h
      convert h using 2
      exact RingHom.ext_int _ _
    exact hle ha

theorem evQ_mk (P : Ideal (MRing ι)) (z : (Σ k, ι k) → ℂ) (hz : z ∈ mcPts P)
    (q : MvPolynomial (Σ k, ι k) ℚ) :
    evQ P z hz (Ideal.Quotient.mk _ q) = eval₂ (algebraMap ℚ ℂ) z q := rfl

theorem goodProjExists : GoodProjExistsStatement := by
  intro K _ ι _ P e hP
  classical
  obtain ⟨r, hr, L, hL⟩ := exists_linear_normalization (k := ℚ) (segQ P) (e + 1)
    (fun r L hr => forms_not_algebraicIndependent P e hP hr L)
  have hint : ∀ t, ∃ p : Polynomial (MvPolynomial (Fin r) ℚ), p.Monic ∧
      Polynomial.eval₂ (aeval (forms (segQ P) L)).toRingHom (segQ P t) p = 0 := hL
  choose p hpm hpe using hint
  let Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ) :=
    { toFun := fun w j => if h : j.val < r then ∑ t, algebraMap ℚ ℂ (L ⟨j.val, h⟩ t) * w t else 0
      map_add' := by
        intro w w'
        funext j
        simp only [Pi.add_apply]
        split_ifs <;> simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro a w
        funext j
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        split_ifs <;> simp [Finset.mul_sum, mul_left_comm] }
  have hΨ : ∀ w (j : Fin r), Ψ w ⟨j.1, lt_of_lt_of_le j.2 hr⟩ = ∑ t, algebraMap ℚ ℂ (L j t) * w t := by
    intro w j
    simp only [Ψ, LinearMap.coe_mk, AddHom.coe_mk, dif_pos j.2, Fin.eta]
  have hA : ∀ z' (hz' : z' ∈ mcPts P), Ψ (segre z') = 0 →
      ∀ t, ((p t).map ((algebraMap ℚ ℂ).comp MvPolynomial.constantCoeff)).IsRoot (segre z' t) := by
    intro z' hz' h0 t
    have hφs : ∀ t', evQ P z' hz' (segQ P t') = segre z' t' := by
      intro t'
      show evQ P z' hz' (Ideal.Quotient.mk _ (segMon t')) = _
      rw [evQ_mk]
      simp [segMon, segre, eval₂_prod]
    have hφf : ∀ j, evQ P z' hz' (forms (segQ P) L j) = 0 := by
      intro j
      have h1 := congrFun h0 ⟨j.1, lt_of_lt_of_le j.2 hr⟩
      rw [hΨ] at h1

      simp only [forms, map_sum, Algebra.smul_def, map_mul, RingHom.map_rat_algebraMap, hφs]
      simpa using h1
    have hcomp : (evQ P z' hz').comp (aeval (forms (segQ P) L)).toRingHom =
        (algebraMap ℚ ℂ).comp MvPolynomial.constantCoeff := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp [RingHom.map_rat_algebraMap]
      · intro j
        simp [hφf]
    show Polynomial.eval (segre z' t) ((p t).map ((algebraMap ℚ ℂ).comp MvPolynomial.constantCoeff)) = 0
    rw [Polynomial.eval_map, ← hcomp, ← hφs, ← Polynomial.hom_eval₂, hpe t, map_zero]
  refine ⟨Ψ, fun z hz h0 => ?_⟩
  obtain ⟨k0⟩ := hP.1
  have hhom : IsMultiHomogIdeal P := hP.2.1.2.1
  choose t0 ht0 using hz.1
  have hs : segre z t0 ≠ 0 := by
    simp only [segre]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => ht0 k
  have hsegA : ∀ c : ℂ, segre (scaleBlock k0 c z) = c • segre z := by
    intro c
    funext t
    simp only [segre, scaleBlock, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_ite_eq' Finset.univ k0 (fun _ => c)]
    simp
  have hroot : ∀ n : ℕ, ((p t0).map ((algebraMap ℚ ℂ).comp MvPolynomial.constantCoeff)).IsRoot
      (((n : ℂ) + 1) * segre z t0) := by
    intro n
    have hcn : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
    have hmem : scaleBlock k0 ((n : ℂ) + 1) z ∈ mcPts P := scaleBlock_mem_zeroLocus P hhom k0 hcn hz
    have h0' : Ψ (segre (scaleBlock k0 ((n : ℂ) + 1) z)) = 0 := by
      rw [hsegA, map_smul, h0, smul_zero]
    have h5 := hA (scaleBlock k0 ((n : ℂ) + 1) z) hmem h0' t0
    have h7 : segre (scaleBlock k0 ((n : ℂ) + 1) z) t0 = ((n : ℂ) + 1) * segre z t0 := by
      rw [hsegA, Pi.smul_apply, smul_eq_mul]
    rw [h7] at h5
    exact h5
  have hinf := Set.infinite_of_injective_forall_mem
    (s := {x | ((p t0).map ((algebraMap ℚ ℂ).comp MvPolynomial.constantCoeff)).IsRoot x})
    (f := fun n : ℕ => ((n : ℂ) + 1) * segre z t0)
    (by
      intro a b hab
      simp only at hab
      have h6 := mul_right_cancel₀ hs hab
      exact_mod_cast add_right_cancel h6) hroot
  exact hinf (Polynomial.finite_setOf_isRoot ((hpm t0).map _).ne_zero)

end

end ReciprocityTheory.ChartRestriction.G.Geo
end
