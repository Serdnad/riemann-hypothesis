module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle022
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle025
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle029
public import Mathlib.FieldTheory.Relrank
public import Mathlib.Order.CompletePartialOrder
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle030
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle013
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle001
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CycDim

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

namespace ThmIUnique

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem recR_congr {I J : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ} (P : Ideal (MRing ι))
    {n : ℕ} (L : Fin n → HermLine ι) (A : HermLine ι) (s : MRing ι)
    (h : ∀ W ∈ divSupp P s, IsHorizontal W → I W n L = J W n L) :
    recR I P L A s = recR J P L A s := by
  classical
  unfold recR
  congr 1
  refine finsum_mem_congr rfl fun W hW => ?_
  by_cases hh : IsHorizontal W
  · rw [if_pos hh, if_pos hh, h W hW hh]
  · rw [if_neg hh, if_neg hh]

theorem isMultiHomog_one' : IsMultiHomog (1 : MRing ι) 0 := by
  classical
  intro m hm k
  rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
  subst hm
  simp

theorem isMultiHomog_mul' {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a)
    (hg : IsMultiHomog g b) : IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m1 hm1 k, hg m2 hm2 k]


open Classical in
theorem isMultiHomog_X' (k : K) (i : ι k) :
    IsMultiHomog (X ⟨k, i⟩ : MRing ι) (Pi.single k 1) := by
  classical
  intro m hm k'
  rw [MvPolynomial.support_X, Finset.mem_singleton] at hm
  subst hm
  by_cases h : k' = k
  · subst h
    simp [Finsupp.single_apply]
  · have : ∀ j : ι k', (⟨k, i⟩ : Σ k, ι k) ≠ ⟨k', j⟩ := fun j e => h (congrArg Sigma.fst e).symm
    simp [Finsupp.single_apply, this, h, Pi.single_apply]

theorem isMultiHomog_pow' {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (n : ℕ) :
    IsMultiHomog (f ^ n) (n • a) := by
  induction n with
  | zero => simpa using (isMultiHomog_one' (ι := ι))
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact isMultiHomog_mul' ih hf

theorem isMultiHomog_coordMonomial (c : ∀ k, ι k) (d : K → ℕ) :
    IsMultiHomog (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ d k) d := by
  classical
  have key : ∀ s : Finset K, IsMultiHomog (∏ k ∈ s, (X ⟨k, c k⟩ : MRing ι) ^ d k)
      (∑ k ∈ s, d k • Pi.single k 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (isMultiHomog_one' (ι := ι))
    | insert k s hk ih =>
      rw [Finset.prod_insert hk, Finset.sum_insert hk]
      exact isMultiHomog_mul' (isMultiHomog_pow' (isMultiHomog_X' k (c k)) _) ih
  have e : (∑ k, d k • (Pi.single k 1 : K → ℕ)) = d := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  have := key Finset.univ
  rwa [e] at this

theorem coordMonomial_not_mem {P : Ideal (MRing ι)} (hP : P.IsPrime) (c : ∀ k, ι k)
    (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ P) (d : K → ℕ) :
    (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ d k) ∉ P := by
  intro h
  obtain ⟨k, -, hk⟩ := (hP.prod_mem_iff).mp h
  exact hc k (hP.mem_of_pow_mem _ hk)

theorem eq_of_lower {I J : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ}
    (hI : IsRFamily I) (hJ : IsRFamily J) {P : Ideal (MRing ι)} {m : ℕ}
    (L : Fin m → HermLine ι) (A : HermLine ι) (hP : IsArithVar P (m + 1))
    (hL : ∀ j, IsSmoothHerm (L j)) (hA : IsSmoothHerm A)
    (hlow : ∀ W, IsArithVar W m → I W m L = J W m L) :
    I P (m + 1) (Fin.snoc L A) = J P (m + 1) (Fin.snoc L A) := by
  classical
  have hPp : P.IsPrime := hP.2.1.1
  choose c hc using hP.2.1.2.2

  let b : K → ℕ := fun k => (-A.a k).toNat
  let e : K → ℕ := fun k => (A.a k + (b k : ℤ)).toNat
  let B : HermLine ι := HermLine.sqMetric b
  have hB : IsSmoothHerm B := isSmoothHerm_sqMetric b
  have hC : IsSmoothHerm (A.tensor B) := isSmoothHerm_tensor hA hB
  have hBa : ∀ k, B.a k = (b k : ℤ) := fun k => rfl
  have hCa : ∀ k, (A.tensor B).a k = (e k : ℤ) := by
    intro k
    have h0 : (0 : ℤ) ≤ A.a k + ((-A.a k).toNat : ℤ) := by
      rw [Int.toNat_eq_max]
      omega
    exact (Int.toNat_of_nonneg h0).symm
  let sB : MRing ι := ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ b k
  let sC : MRing ι := ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ e k
  have hsB : IsMultiHomog sB b := isMultiHomog_coordMonomial c b
  have hsC : IsMultiHomog sC e := isMultiHomog_coordMonomial c e
  have hsBP : sB ∉ P := coordMonomial_not_mem hPp c hc b
  have hsCP : sC ∉ P := coordMonomial_not_mem hPp c hc e

  have diff : ∀ F : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ, IsRFamily F →
      F P (m + 1) (Fin.snoc L A) = recR F P L (A.tensor B) sC - recR F P L B sB := by
    intro F hF
    have h1 := hF.1 P m L A B hP hL hA hB
    rw [hF.2 P m L (A.tensor B) sC e hP hL hC hCa hsC hsCP,
      hF.2 P m L B sB b hP hL hB hBa hsB hsBP] at h1
    linarith
  have hor : ∀ (X' : HermLine ι) (s : MRing ι), IsSectionOn P X' s →
      ∀ W ∈ divSupp P s, IsHorizontal W → I W m L = J W m L := fun X' s hs W hW hh =>
    hlow W ((divSuppArith K ι P m X' s W hP hs hW).1 hh)
  rw [diff I hI, diff J hJ,
    recR_congr P L (A.tensor B) sC (hor _ sC ⟨e, hCa, hsC, hsCP⟩),
    recR_congr P L B sB (hor _ sB ⟨b, hBa, hsB, hsBP⟩)]

end ThmIUnique

theorem ThmIUnique.proof (h₀ : ArithVarZeroStatement) : ThmIUnique.Statement := by
  unfold ThmIUnique.Statement UniqueStatement
  intro K _ ι _ I J hI hJ
  have key : ∀ (m : ℕ) (P : Ideal (MRing ι)) (L : Fin (m + 1) → HermLine ι), IsArithVar P (m + 1) →
      (∀ j, IsSmoothHerm (L j)) → I P (m + 1) L = J P (m + 1) L := by
    intro m
    induction m with
    | zero =>
      intro P L hP hL
      rw [← Fin.snoc_init_self L]
      exact ThmIUnique.eq_of_lower hI hJ _ _ hP (fun j => hL j.castSucc) (hL _)
        fun W hW => absurd hW (h₀ K ι W)
    | succ m ih =>
      intro P L hP hL
      rw [← Fin.snoc_init_self L]
      exact ThmIUnique.eq_of_lower hI hJ _ _ hP (fun j => hL j.castSucc) (hL _)
        fun W hW => ih W _ hW fun j => hL j.castSucc
  intro P n L hn hP hL
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact key m P L hP hL

end

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory Filter
open scoped Topology ContDiff

noncomputable section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [∀ k, Fintype (ι k)] in
theorem isOpen_blockNonzero : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have e : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0} := by
    ext z; simp
  rw [e]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem contDiffAt_log_metric {D : ℕ} {A : HermLine ι} (hA : IsSmoothHerm A)
    {γ : (Fin D → ℂ) → (Σ k, ι k) → ℂ} {y : Fin D → ℂ}
    (hγ : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ γ y') (hy : ∀ k, ∃ i, γ y ⟨k, i⟩ ≠ 0) :
    ContDiffAt ℝ 2 (fun y' => Real.log (A.h (γ y'))) y := by
  obtain ⟨U, hU, hUo, hyU⟩ := eventually_nhds_iff.mp hγ
  have hdU : DifferentiableOn ℂ γ U := fun y' h => (hU y' h).differentiableWithinAt
  have hc : ContDiffAt ℝ ∞ γ y :=
    ((ReciprocityTheory.ChartRestriction.DS.S7.cca_contDiffOn hUo hdU).contDiffAt (hUo.mem_nhds hyU)).restrict_scalars ℝ
  have hρ : ContDiffAt ℝ ∞ A.h (γ y) := hA.contDiffAt (isOpen_blockNonzero.mem_nhds hy)
  exact_mod_cast (contDiffAt_infty.mp ((hρ.comp y hc).log (A.pos _ hy).ne')) 2

theorem cxHessian_pot_snoc {n : ℕ} (L : Fin n → HermLine ι) (A X : HermLine ι)
    (γ : (Fin (n + 1) → ℂ) → (Σ k, ι k) → ℂ) (y : Fin (n + 1) → ℂ) :
    (fun k => cxHessian (fun y' => pot (Fin.snoc L X) k (γ y')) y) =
      Function.update (fun k => cxHessian (fun y' => pot (Fin.snoc L A) k (γ y')) y) (Fin.last n)
        (cxHessian (fun y' => Real.log (X.h (γ y'))) y) := by
  funext k
  rcases Fin.eq_castSucc_or_eq_last k with ⟨j, rfl⟩ | rfl
  · rw [Function.update_of_ne (Fin.castSucc_ne_last j)]
    simp only [pot, Fin.snoc_castSucc]
  · rw [Function.update_self]
    simp only [pot, Fin.snoc_last]

theorem maDensity_snoc_tensor {n : ℕ} (L : Fin n → HermLine ι) {A C : HermLine ι}
    (hA : IsSmoothHerm A) (hC : IsSmoothHerm C) {γ : (Fin (n + 1) → ℂ) → (Σ k, ι k) → ℂ}
    {y : Fin (n + 1) → ℂ}
    (hγ : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ γ y' ∧ ∀ k, ∃ i, γ y' ⟨k, i⟩ ≠ 0) :
    maDensity (fun j y' => pot (Fin.snoc L (A.tensor C)) j (γ y')) y =
      maDensity (fun j y' => pot (Fin.snoc L A) j (γ y')) y +
        maDensity (fun j y' => pot (Fin.snoc L C) j (γ y')) y := by
  have hev := hγ.eventually_nhds
  have ha : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 (fun y'' => Real.log (A.h (γ y''))) y' := by
    filter_upwards [hev] with y' hy'
    exact contDiffAt_log_metric hA (hy'.mono fun _ h => h.1) hy'.self_of_nhds.2
  have hc : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 (fun y'' => Real.log (C.h (γ y''))) y' := by
    filter_upwards [hev] with y' hy'
    exact contDiffAt_log_metric hC (hy'.mono fun _ h => h.1) hy'.self_of_nhds.2
  have hψ : (fun y' => Real.log ((A.tensor C).h (γ y'))) =ᶠ[𝓝 y]
      fun y' => 1 * Real.log (A.h (γ y')) + 1 * Real.log (C.h (γ y')) := by
    filter_upwards [hγ] with y' hy'
    rw [one_mul, one_mul]
    exact Real.log_mul (A.pos _ hy'.2).ne' (C.pos _ hy'.2).ne'
  have hH := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gaamix_cxHessian_comb 1 1 ha hc hψ
  simp only [Complex.ofReal_one, one_smul] at hH
  unfold maDensity
  rw [cxHessian_pot_snoc L A (A.tensor C), cxHessian_pot_snoc L A C, hH]
  have hm := ReciprocityTheory.AnForm.A.mdisc_update_add
    (fun k => cxHessian (fun y' => pot (Fin.snoc L A) k (γ y')) y) (Fin.last n)
    (cxHessian (fun y' => Real.log (A.h (γ y'))) y) (cxHessian (fun y' => Real.log (C.h (γ y'))) y)
  change mixedDisc _ = mixedDisc _ + mixedDisc _ at hm
  rw [← cxHessian_pot_snoc L A A γ y] at hm
  rw [hm, Complex.add_re, mul_add]

theorem sheetDensity_snoc_tensor (P : Ideal (MRing ι)) {n : ℕ}
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1 + 1) → ℂ)) (L : Fin n → HermLine ι)
    {A C : HermLine ι} (hA : IsSmoothHerm A) (hC : IsSmoothHerm C) (g : ((Σ k, ι k) → ℂ) → ℝ)
    (y : Fin (n + 1) → ℂ) (w : ((k : K) → ι k) → ℂ) :
    sheetDensity P Ψ (pot (Fin.snoc L (A.tensor C))) g y w =
      sheetDensity P Ψ (pot (Fin.snoc L A)) g y w + sheetDensity P Ψ (pot (Fin.snoc L C)) g y w := by
  unfold sheetDensity
  by_cases h : ∃ γ, IsSheet P Ψ y w γ
  · simp only [dif_pos h]
    have hγ : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ h.choose y' ∧ ∀ k, ∃ i, h.choose y' ⟨k, i⟩ ≠ 0 := by
      filter_upwards [h.choose_spec.2] with y' hy'
      exact ⟨hy'.1, hy'.2.1.1⟩
    rw [maDensity_snoc_tensor L hA hC hγ, mul_add]
  · simp only [dif_neg h, add_zero]

theorem arInt_snoc_tensor (hFF : FibreFiniteStatement) (hInt : PtsIntegrableStatement)
    {P : Ideal (MRing ι)} {n : ℕ} (L : Fin n → HermLine ι) {A C B : HermLine ι} {s : MRing ι}
    (hP : IsArithVar P (n + 2)) (hL : ∀ j, IsSmoothHerm (L j)) (hA : IsSmoothHerm A)
    (hC : IsSmoothHerm C) (hB : IsSmoothHerm B) (hs : IsSectionOn P B s) :
    arInt P s B (Fin.snoc L (A.tensor C)) =
      arInt P s B (Fin.snoc L A) + arInt P s B (Fin.snoc L C) := by
  change ptsIntegral P (pot (Fin.snoc L (A.tensor C))) (logNorm B s) =
    ptsIntegral P (pot (Fin.snoc L A)) (logNorm B s) + ptsIntegral P (pot (Fin.snoc L C)) (logNorm B s)
  unfold ptsIntegral
  by_cases hΨ : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1 + 1) → ℂ), IsGoodProj P Ψ
  · rw [dif_pos hΨ, dif_pos hΨ, dif_pos hΨ]
    have hsm : ∀ X : HermLine ι, IsSmoothHerm X →
        ∀ j, IsSmoothHerm ((Fin.snoc L X : Fin (n + 1) → HermLine ι) j) := by
      intro X hX j
      rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
      · simpa only [Fin.snoc_castSucc] using hL j
      · simpa only [Fin.snoc_last] using hX
    have iA := hInt K ι P (n + 1) hΨ.choose (Fin.snoc L A) B s hP hΨ.choose_spec (hsm A hA) hB hs
    have iC := hInt K ι P (n + 1) hΨ.choose (Fin.snoc L C) B s hP hΨ.choose_spec (hsm C hC) hB hs
    unfold ptsIntegralAt
    rw [← integral_add iA iC]
    congr 1
    funext y
    rw [← finsum_mem_add_distrib (hFF K ι P (n + 1) hΨ.choose hP hΨ.choose_spec y)]
    exact finsum_mem_congr rfl fun w _ => sheetDensity_snoc_tensor P hΨ.choose L hA hC _ y w
  · rw [dif_neg hΨ, dif_neg hΨ, dif_neg hΨ, add_zero]


omit [∀ k, Fintype (ι k)] in
theorem geoNum_snoc_tensor {n : ℕ} (L : Fin n → HermLine ι) (A C : HermLine ι) (W : Ideal (MRing ι)) :
    geoNum (n + 1) W (fun j => ((Fin.snoc L (A.tensor C) : Fin (n + 1) → HermLine ι) j).a) =
      geoNum (n + 1) W (fun j => ((Fin.snoc L A : Fin (n + 1) → HermLine ι) j).a) + geoNum (n + 1) W (fun j => ((Fin.snoc L C : Fin (n + 1) → HermLine ι) j).a) := by
  have hi : ∀ X : HermLine ι, Fin.init (fun j => ((Fin.snoc L X : Fin (n + 1) → HermLine ι) j).a) = fun j => (L j).a := by
    intro X; funext j; simp only [Fin.init, Fin.snoc_castSucc]
  simp only [geoNum]
  split_ifs with h
  · simp only [hi, Fin.snoc_last, HermLine.tensor, Pi.add_apply, ← Finset.sum_add_distrib, add_mul]
  · simp


open Classical in
theorem RPositionAdd.proof (hFF : FibreFiniteStatement) (hInt : PtsIntegrableStatement) :
    RPositionAdd.Statement := by
  intro K _ ι _ I P n L A C B s hI hP hL hA hC hB hs
  let term : HermLine ι → Ideal (MRing ι) → ℝ := fun X W =>
    (multAt (P ⊔ Ideal.span {s}) W : ℝ) *
      (if IsHorizontal W then I W (n + 1) (Fin.snoc L X)
        else (geoNum (n + 1) W (fun j => ((Fin.snoc L X : Fin (n + 1) → HermLine ι) j).a) : ℝ) * Real.log (charOf W))
  have e : ∀ X, recR I P (Fin.snoc L X) B s =
      (∑ᶠ W ∈ divSupp P s, term X W) - arInt P s B (Fin.snoc L X) := fun X => rfl
  have key : ∀ W ∈ divSupp P s, term (A.tensor C) W = term A W + term C W := by
    intro W hW
    simp only [term]
    split_ifs with hh
    · rw [hI W L A C ((divSuppArith K ι P (n + 1) B s W hP hs hW).1 hh) hL hA hC]; ring
    · rw [geoNum_snoc_tensor L A C W]; push_cast; ring
  rw [e, e, e, finsum_mem_congr rfl key, finsum_mem_add_distrib (divSupp_finite P s),
    arInt_snoc_tensor hFF hInt L hP hL hA hC hB hs]
  ring

end

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

theorem primeSubfield_exists_div {E : Type*} [Field E] (c : (⊥ : Subfield E)) :
    ∃ a b : ℤ, (b : (⊥ : Subfield E)) ≠ 0 ∧ c = a / b := by
  have hc : (c : E) ∈ Subfield.closure (∅ : Set E) := by
    rw [Subfield.closure_empty]
    exact c.2
  obtain ⟨y, hy, z, hz, h⟩ := Subfield.mem_closure_iff.1 hc
  rw [Subring.closure_empty, Subring.mem_bot] at hy hz
  obtain ⟨a, rfl⟩ := hy
  obtain ⟨b, rfl⟩ := hz
  by_cases hb : (b : E) = 0
  · refine ⟨0, 1, by simp, Subtype.ext ?_⟩
    simp [← h, hb]
  · refine ⟨a, b, fun h0 => hb ?_, Subtype.ext ?_⟩
    · simpa using congrArg Subtype.val h0
    · simp [← h]

def SemilocResidueFrac.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ) (s : MRing ι) (α : K → ℕ)
    (W : Ideal (MRing ι)) (hv : IsBlockMap κ v) (hP' : IsArithVar P' (n + 1)),
    IsArithVar (imageZ v P') (n + 1) → IsMultiHomog s α → s ∉ imageZ v P' → W ∈ divSupp (imageZ v P') s →
    ∀ (W' : Ideal (MRing ι')) (hW' : W' ∈ fibreOver v P' W) [IsLocalRing (locRing P' W')]
      (G' : GenFibre v W') (i' : ∀ k', ι' k'), (∀ k', (X ⟨k', i' k'⟩ : MRing ι') ∉ W') →
    ∀ (F : Type) [Field F] [Algebra F G'.Φ'], (∀ c : F, ∃ a b : ℤ, (b : F) ≠ 0 ∧ c = a / b) →
    haveI := hP'.2.1.1
    letI := (locToSemiloc hv P' W).toAlgebra
    Module.length (locRing (imageZ v P') W)
        (semiLocRing P' (fibreOver v P' W) ⧸ semiMaxIdeal P' (fibreOver v P' W) W' hW') =
      (IntermediateField.relfinrank
        (IntermediateField.adjoin F
          (Set.range ((fun q : Σ k', ι' k' => G'.x' q / G'.x' ⟨q.1, i' q.1⟩) ∘ v)))
        (IntermediateField.adjoin F (Set.range fun q : Σ k', ι' k' => G'.x' q / G'.x' ⟨q.1, i' q.1⟩)) : ℕ∞)

end GroundTheory.Heights₂.Heights.Inter
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem FibreDivSupp.proof (h : FibreIncomp.Statement) : FibreDivSupp.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n s α W hv hP' hQ hs hsQ hW W'
  have hmin : ∀ Q ∈ (P' ⊔ Ideal.span {rename v s}).minimalPrimes, IsRelevant Q → IsMultiProjPrime Q :=
    fun Q hQm hQr => ⟨hQm.1.1, cyc_isMultiHomogIdeal_of_mem_minimalPrimes hP'.2.1.2.1
      (rename_isMultiHomog hv hs) hQm, hQr⟩
  have hmem : ∀ Q ∈ (P' ⊔ Ideal.span {rename v s}).minimalPrimes, P' ≤ Q ∧ rename v s ∈ Q :=
    fun Q hQm => ⟨le_sup_left.trans hQm.1.2,
      hQm.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))⟩
  constructor
  · rintro ⟨⟨hW'p, hPW', himg⟩, hsW'⟩
    have := hW'p.1
    obtain ⟨Q, hQm, hQW'⟩ := Ideal.exists_minimalPrimes_le
      (sup_le hPW' ((Ideal.span_singleton_le_iff_mem _).2 hsW'))
    have hQr : IsRelevant Q := fun k => (hW'p.2.2 k).imp fun _ hi hq => hi (hQW' hq)
    obtain ⟨hPQ, hsQ'⟩ := hmem Q hQm
    have hQi : imageZ v Q = W := by
      have := hQm.1.1
      have hpr : (imageZ v Q).IsPrime := Ideal.comap_isPrime _ _
      have hle : imageZ v P' ⊔ Ideal.span {s} ≤ imageZ v Q :=
        sup_le (Ideal.comap_mono hPQ) ((Ideal.span_singleton_le_iff_mem _).2 hsQ')
      have hle2 : imageZ v Q ≤ W := himg ▸ Ideal.comap_mono hQW'
      exact le_antisymm hle2 (hW.1.2 ⟨hpr, hle⟩ hle2)
    have hQe := h K ι K' ι' κ v P' n s α W hv hP' hQ hs hsQ hW Q W' ⟨hmin Q hQm hQr, hPQ, hQi⟩
      ⟨hW'p, hPW', himg⟩ hQW'
    subst hQe
    exact ⟨⟨hQm, hQr⟩, hQi⟩
  · rintro ⟨⟨hW'm, hW'r⟩, himg⟩
    exact ⟨⟨hmin W' hW'm hW'r, (hmem W' hW'm).1, himg⟩, (hmem W' hW'm).2⟩

end GroundTheory.Heights₂.Heights.Inter
end
end
