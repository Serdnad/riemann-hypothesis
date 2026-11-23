module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCocycleCoboundaryCommaLocalBasis
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle018
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle296
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LSeries.Nonvanishing
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
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Mathlib.Topology.Sheaves.Presheaf
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation

@[expose] public section

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CatCoh.Desc.Basis

theorem oneCocycle_invertibleLocus_isCoboundary : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ T : C, ∃ (n : ℕ) (b : Fin n → F.obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (mp F u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → ∀ (T : C) (e : F.obj T) (y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → F.obj (G.obj t')), (∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), IsUnit (mp F u e) → y t t'' u (a ≫ b) = mp F (G.map b) (y t t' u a) + y t' t'' (u ≫ G.map a) b) → ∃ g : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t), ∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), IsUnit (mp F u e) → g t' (u ≫ G.map a) - mp F (G.map a) (g t u) = y t t' u a := by
  intro R _ C _ C' _ F G _ _ H hcov hdir T e y hy
  obtain ⟨L, l, hl, -, -, huniv⟩ := H T e
  have hunit : ∀ t (w : L ⟶ G.obj t), IsUnit (mp F (l ≫ w) e) := by
    intro t w
    rw [mp_comp]
    exact hl.map _
  obtain ⟨gL, hgL⟩ := oneCocycle_coboundary_comma_localBasis F G H hcov hdir L (fun t t' w a ↦ y t t' (l ≫ w) a)
    (fun t t' t'' w a b ↦ by
      have h := hy t t' t'' (l ≫ w) a b (hunit t w)
      rw [Category.assoc] at h
      exact h)
  classical
  refine ⟨fun t u ↦ if h : ∃ w : L ⟶ G.obj t, l ≫ w = u then gL t h.choose else 0, ?_⟩
  have hg : ∀ t (u : T ⟶ G.obj t) (w : L ⟶ G.obj t), l ≫ w = u →
      (if h : ∃ w : L ⟶ G.obj t, l ≫ w = u then gL t h.choose else 0) = gL t w := by
    intro t u w hw
    have h : ∃ w : L ⟶ G.obj t, l ≫ w = u := ⟨w, hw⟩
    rw [dite_eq_left h]
    exact congrArg (gL t) (Subsingleton.elim _ _)
  intro t t' u a hu
  obtain ⟨w, hw, -⟩ := huniv (G.obj t) u hu
  have hw' : l ≫ (w ≫ G.map a) = u ≫ G.map a := by rw [← Category.assoc, hw]
  simp only []
  rw [hg t u w hw, hg t' (u ≫ G.map a) (w ≫ G.map a) hw', hgL t t' w a, hw]

end GlobalTheory.CatCoh.Desc.Basis
end
end

section

noncomputable section

open Complex DirichletCharacter

namespace GlobalTheory.LogDerOneProof

theorem logDerOne_holds : GlobalTheory.Mem.An.LogDerOne := by
  classical
  obtain ⟨C, hC, H⟩ := GlobalTheory.LWide.logDeriv_LFunction_strip
  refine ⟨2 * C, fun q _ χ hq hp => ?_⟩
  have hne : χ ≠ 1 := by
    intro h
    have h1 : χ.conductor = q := hp
    rw [h, DirichletCharacter.conductor_one] at h1
    omega
  have hL : LFunction χ 1 ≠ 0 := LFunction_ne_zero_of_one_le_re χ (Or.inl hne) (by simp)
  obtain ⟨hfin, hcount, hmain⟩ := H q χ hne 1 (by norm_num) (by norm_num) hL
  simp only [Complex.one_im, abs_zero, zero_add, Complex.ofReal_zero, zero_mul, add_zero] at hfin hcount hmain
  set D : Set ℂ := {w : ℂ | ‖w - 2‖ ≤ 7 / 2 ∧ LFunction χ w = 0} with hD
  set Z : Set ℂ := GlobalTheory.Mem.An.zerosIn χ 0 1 with hZ
  have hsub : Z ⊆ D := by
    rintro w ⟨h0, h1, h2, h3⟩
    refine ⟨?_, h3⟩
    have h4 := Complex.norm_le_abs_re_add_abs_im (w - 2)
    simp only [Complex.sub_re, Complex.sub_im, Complex.re_ofNat, Complex.im_ofNat, sub_zero] at h4 h2
    have h5 : |w.re - 2| ≤ 2 := abs_le.2 ⟨by linarith, by linarith⟩
    linarith
  have hZfin : Z.Finite := hfin.subset hsub
  have hsub' : hZfin.toFinset ⊆ hfin.toFinset := by
    intro w hw
    simp only [Set.Finite.mem_toFinset] at hw ⊢
    exact hsub hw
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at hcount hmain
  have hz : GlobalTheory.Mem.An.zsum χ 0 1 (fun ρ => 1 / (1 - ρ)) =
      ∑ w ∈ hZfin.toFinset, (analyticOrderNatAt (LFunction χ) w : ℂ) / (1 - w) := by
    unfold GlobalTheory.Mem.An.zsum
    rw [← hZ, finsum_mem_eq_finite_toFinset_sum _ hZfin]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [GlobalTheory.Mem.An.zmult]
    ring
  rw [hz]
  rw [← Finset.sum_sdiff hsub'] at hmain
  have hrest : ‖∑ w ∈ hfin.toFinset \ hZfin.toFinset, (analyticOrderNatAt (LFunction χ) w : ℂ) / (1 - w)‖ ≤
      ∑ w ∈ hfin.toFinset, (analyticOrderNatAt (LFunction χ) w : ℝ) := by
    refine (norm_sum_le _ _).trans (le_trans (Finset.sum_le_sum fun w hw => ?_)
      (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset fun _ _ _ => Nat.cast_nonneg _))
    simp only [Finset.mem_sdiff, Set.Finite.mem_toFinset] at hw
    obtain ⟨⟨_, hw0⟩, hwn⟩ := hw
    have hre : w.re < 1 := by
      by_contra h
      exact LFunction_ne_zero_of_one_le_re χ (Or.inl hne) (not_lt.1 h) hw0
    have h1 : 1 ≤ ‖1 - w‖ := by
      by_cases h0 : 0 < w.re
      · have him : 1 < |w.im| := by
          by_contra h
          exact hwn ⟨h0, hre, by simpa using not_lt.1 h, hw0⟩
        have h4 := Complex.abs_im_le_norm (1 - w)
        simp only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] at h4
        linarith
      · have h4 := Complex.re_le_norm (1 - w)
        simp only [Complex.sub_re, Complex.one_re] at h4
        linarith [not_lt.1 h0]
    rw [norm_div, Complex.norm_natCast]
    exact div_le_self (Nat.cast_nonneg _) h1
  have hq' : (1 : ℝ) < q := by exact_mod_cast hq
  have hlog : Real.log (q * 2) ≤ Real.log (3 * q) := Real.log_le_log (by linarith) (by linarith)
  have hl2 : C * Real.log (q * 2) ≤ C * Real.log (3 * q) := mul_le_mul_of_nonneg_left hlog hC.le
  set A := deriv (LFunction χ) 1 / LFunction χ 1
  set R := ∑ w ∈ hfin.toFinset \ hZfin.toFinset, (analyticOrderNatAt (LFunction χ) w : ℂ) / (1 - w)
  set S := ∑ w ∈ hZfin.toFinset, (analyticOrderNatAt (LFunction χ) w : ℂ) / (1 - w)
  have e : A - S = (A - (R + S)) + R := by ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  linarith

end GlobalTheory.LogDerOneProof
end
end

section

namespace GlobalTheory.OTY.TwEst

open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y

noncomputable section

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

def wt (A : WeightedAtlas n Y ι La) (E : La) (β : ι → Y → ℂ) (z : Y → V n) (y : Y) : ℝ :=
  -Real.log (A.nsq (A.kap + E) β y) + Real.log (A.nsq A.kap (jdet A z) y)

def quot (A : WeightedAtlas n Y ι La) (h β : ι → Y → ℂ) (y : Y) : ℂ :=
  h (A.pick y) y / β (A.pick y) y


open scoped Classical in
def ext0 {Y : Type*} (U : Set Y) (f : U → ℂ) (y : Y) : ℂ :=
  if hy : y ∈ U then f ⟨y, hy⟩ else 0

theorem extendByZeroOnSubset_apply_coe {Y : Type*} (U : Set Y) (f : U → ℂ) (y : U) : ext0 U f y = f y := by
  simp [ext0, y.2]

end

end GlobalTheory.OTY.TwEst

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem GlobalTheory.OTY.TwEst.nz_facts {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La] (A : WeightedAtlas n Y ι La)
    (L Λ : La) (s : Fin n → ι → Y → ℂ) (τ : ι → Y → ℂ) (C : ℝ) (hC0 : 0 < C)
    (hsq : ∀ y, A.sqn L s y ≤ 1) (hC : ∀ y, A.nsq Λ τ y ≤ C * A.sqn L s y) (y : Y) (hy : y ∈ nz A τ) :
    y ∉ A.zeroSet s ∧ psi A L s y ≤ 0 ∧
      -psi A L s y ≤ (n : ℝ) * (-Real.log (A.nsq Λ τ y)) + (n : ℝ) * Real.log C := by
  have hτy : τ (A.pick y) y ≠ 0 := hy
  have hτ0 : 0 < A.nsq Λ τ y := by
    unfold WeightedAtlas.nsq
    exact mul_pos (pow_pos (norm_pos_iff.mpr hτy) 2) (Real.exp_pos _)
  have hs0 : 0 < A.sqn L s y := by
    by_contra hle
    push_neg at hle
    have := hC y
    nlinarith
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  refine ⟨?_, ?_, ?_⟩
  · intro hz
    have hz' : ∀ k, s k (A.pick y) y = 0 := hz
    have : A.sqn L s y = 0 := by
      unfold WeightedAtlas.sqn WeightedAtlas.nsq
      simp [hz']
    linarith
  · unfold psi
    have := Real.log_nonpos hs0.le (hsq y)
    nlinarith
  · unfold psi
    have h1 : Real.log (A.nsq Λ τ y) ≤ Real.log C + Real.log (A.sqn L s y) := by
      rw [← Real.log_mul hC0.ne' hs0.ne']
      exact Real.log_le_log hτ0 (hC y)
    have := mul_le_mul_of_nonneg_left h1 hn
    nlinarith
end

section

noncomputable section

namespace GlobalTheory.LieDisc

open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def endLat (Λ : Submodule (𝓞 E) (Fin r → E)) : AddSubgroup (Matrix (Fin r) (Fin r) E) where
  carrier := {Y | ∀ x ∈ Λ, Y *ᵥ x ∈ Λ}
  zero_mem' x _ := by simp
  add_mem' {Y Z} hY hZ x hx := by rw [add_mulVec]; exact Λ.add_mem (hY x hx) (hZ x hx)
  neg_mem' {Y} hY x hx := by rw [neg_mulVec]; exact Λ.neg_mem (hY x hx)

theorem mem_endLat {Λ : Submodule (𝓞 E) (Fin r → E)} {Y : Matrix (Fin r) (Fin r) E} :
    Y ∈ endLat Λ ↔ ∀ x ∈ Λ, Y *ᵥ x ∈ Λ := Iff.rfl

def IsSkew (G Y : Matrix (Fin r) (Fin r) E) : Prop :=
  ∀ u w, herm G (Y *ᵥ u) w + herm G u (Y *ᵥ w) = 0

def skewLat (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) :
    AddSubgroup (Matrix (Fin r) (Fin r) E) where
  carrier := {Y | IsSkew G Y ∧ Y ∈ endLat Λ}
  zero_mem' := ⟨fun u w => by simp [herm, cc], (endLat Λ).zero_mem⟩
  add_mem' {Y Z} hY hZ := by
    refine ⟨fun u w => ?_, (endLat Λ).add_mem hY.2 hZ.2⟩
    have h1 := hY.1 u w
    have h2 := hZ.1 u w
    simp only [herm, cc, add_mulVec, Pi.add_apply, map_add (f := _), add_mul, mul_add, Finset.sum_add_distrib] at h1 h2 ⊢
    linear_combination h1 + h2
  neg_mem' {Y} hY := by
    refine ⟨fun u w => ?_, (endLat Λ).neg_mem hY.2⟩
    have h1 := hY.1 u w
    simp only [herm, cc, neg_mulVec, Pi.neg_apply, map_neg, neg_mul, mul_neg, Finset.sum_neg_distrib] at h1 ⊢
    linear_combination -h1

def hAdj (G Y : Matrix (Fin r) (Fin r) E) : Matrix (Fin r) (Fin r) E := (G⁻¹ * Yᵀ * G).map cc

def imLat (E : Type) [Field E] [NumberField E] [IsCMField E] : AddSubgroup E where
  carrier := {a | IsIntegral ℤ a ∧ cc a = -a}
  zero_mem' := ⟨isIntegral_zero, by simp [cc]⟩
  add_mem' {a b} ha hb := ⟨ha.1.add hb.1, by simp only [cc, map_add (f := _)] at ha hb ⊢; rw [ha.2, hb.2, neg_add]⟩
  neg_mem' {a} ha := ⟨ha.1.neg, by simp only [cc, map_neg] at ha ⊢; rw [ha.2]⟩

def trProj (Y : Matrix (Fin r) (Fin r) E) : Matrix (Fin r) (Fin r) E :=
  Y - (Y.trace / r) • (1 : Matrix (Fin r) (Fin r) E)

def dualLie (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) :
    AddSubgroup (Matrix (Fin r) (Fin r) E) where
  carrier := {Y | Y.trace = 0 ∧ (∀ u w, herm G (Y *ᵥ u) w + herm G u (Y *ᵥ w) = 0) ∧
    ∀ X ∈ lieLat G Λ, IsIntegral ℤ (Matrix.trace (X * Y))}
  zero_mem' := ⟨by simp, fun u w => by simp [herm, cc], fun X _ => by simpa using isIntegral_zero⟩
  add_mem' {Y Z} hY hZ := by
    refine ⟨by rw [trace_add, hY.1, hZ.1, add_zero], fun u w => ?_, fun X hX => ?_⟩
    · have h1 := hY.2.1 u w
      have h2 := hZ.2.1 u w
      simp only [herm, cc, add_mulVec, Pi.add_apply, map_add (f := _), add_mul, mul_add, Finset.sum_add_distrib] at h1 h2 ⊢
      linear_combination h1 + h2
    · rw [Matrix.mul_add, trace_add]; exact (hY.2.2 X hX).add (hZ.2.2 X hX)
  neg_mem' {Y} hY := by
    refine ⟨by rw [trace_neg, hY.1, neg_zero], fun u w => ?_, fun X hX => ?_⟩
    · have h1 := hY.2.1 u w
      simp only [herm, cc, neg_mulVec, Pi.neg_apply, map_neg, neg_mul, mul_neg, Finset.sum_neg_distrib] at h1 ⊢
      linear_combination -h1
    · rw [Matrix.mul_neg, trace_neg]; exact (hY.2.2 X hX).neg

theorem closure_dualLie (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) :
    AddSubgroup.closure {Y : Matrix (Fin r) (Fin r) E | Y.trace = 0 ∧
      (∀ u w, herm G (Y *ᵥ u) w + herm G u (Y *ᵥ w) = 0) ∧
      ∀ X ∈ lieLat G Λ, IsIntegral ℤ (Matrix.trace (X * Y))} = dualLie G Λ :=
  AddSubgroup.closure_eq (dualLie G Λ)

theorem cc_cc (a : E) : cc (cc a) = a := by simp [cc]

theorem smul_mem_of_isIntegral {Λ : Submodule (𝓞 E) (Fin r → E)} {c : E} (hc : IsIntegral ℤ c)
    {x : Fin r → E} (hx : x ∈ Λ) : c • x ∈ Λ := by
  have h := Λ.smul_mem (⟨c, hc⟩ : 𝓞 E) hx
  convert h using 1
  ext i
  simp only [Pi.smul_apply, smul_eq_mul, Algebra.smul_def]
  rfl

theorem smul_mem_endLat {Λ : Submodule (𝓞 E) (Fin r → E)} {c : E} (hc : IsIntegral ℤ c)
    {Y : Matrix (Fin r) (Fin r) E} (hY : Y ∈ endLat Λ) : c • Y ∈ endLat Λ := fun x hx => by
  have : (c • Y) *ᵥ x = c • (Y *ᵥ x) := by
    ext i; simp [mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  rw [this]; exact smul_mem_of_isIntegral hc (hY x hx)

theorem mul_mem_endLat {Λ : Submodule (𝓞 E) (Fin r → E)} {Y Z : Matrix (Fin r) (Fin r) E}
    (hY : Y ∈ endLat Λ) (hZ : Z ∈ endLat Λ) : Y * Z ∈ endLat Λ := fun x hx => by
  rw [← mulVec_mulVec]; exact hY _ (hZ x hx)

theorem one_mem_endLat {Λ : Submodule (𝓞 E) (Fin r → E)} : (1 : Matrix (Fin r) (Fin r) E) ∈ endLat Λ :=
  fun x hx => by rw [one_mulVec]; exact hx

end GlobalTheory.LieDisc
end
end

section

open NumberField Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.DenClear

variable {E : Type} [Field E] [NumberField E]

theorem exists_natMul_isIntegral (c : E) : ∃ m : ℕ, 0 < m ∧ IsIntegral ℤ ((m : E) * c) := by
  obtain ⟨y, hy, hi⟩ := IsAlgebraic.exists_integral_multiple (R := ℤ) ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic c))
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩
  rcases Int.natAbs_eq y with h | h
  · rw [h, zsmul_eq_mul] at hi
    simpa using hi
  · rw [h, zsmul_eq_mul] at hi
    have := hi.neg
    simpa using this

theorem intSmul_eq {r : ℕ} (a : 𝓞 E) (w : Fin r → E) : a • w = (a : E) • w := by
  rw [← algebraMap_smul E a w]

theorem exists_natSmul_mem {r : ℕ} (Λ : Submodule (𝓞 E) (Fin r → E)) (v : Fin r → E)
    (hv : v ∈ Submodule.span E (Λ : Set (Fin r → E))) : ∃ n : ℕ, 0 < n ∧ (n : E) • v ∈ Λ := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨m, hm, hmy⟩ := hy
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    have e : ((n * m : ℕ) : E) • (x + y) = m • ((n : E) • x) + n • ((m : E) • y) := by
      simp only [Nat.cast_mul, smul_add, ← Nat.cast_smul_eq_nsmul E, smul_smul]
      congr 1 <;> congr 1 <;> ring
    rw [e]
    exact Λ.add_mem (Λ.nsmul_mem hnx m) (Λ.nsmul_mem hmy n)
  | smul c x _ hx =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨m, hm, hc⟩ := exists_natMul_isIntegral c
    refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
    obtain ⟨a, ha⟩ : ∃ a : 𝓞 E, (a : E) = (m : E) * c := ⟨⟨_, (mem_integralClosure_iff ℤ E).2 hc⟩, rfl⟩
    have e : ((m * n : ℕ) : E) • (c • x) = a • ((n : E) • x) := by
      rw [intSmul_eq, ha, smul_smul, smul_smul]
      congr 1
      push_cast
      ring
    rw [e]
    exact Λ.smul_mem _ hnx

variable [IsCMField E]

theorem exists_natSmul_mem_lieLat : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)), Λ.FG →
    Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → ∀ X : Matrix (Fin r) (Fin r) E, X.trace = 0 →
    (∀ x y, herm G (X *ᵥ x) y + herm G x (X *ᵥ y) = 0) → ∃ N : ℕ, 0 < N ∧ (N : E) • X ∈ lieLat G Λ := by
  intro E _ _ _ r G Λ hfg hspan X htr hskew
  obtain ⟨S, hS⟩ := hfg
  have hv : ∀ s : Fin r → E, ∃ n : ℕ, 0 < n ∧ (n : E) • (X *ᵥ s) ∈ Λ := fun s =>
    exists_natSmul_mem Λ _ (by rw [hspan]; trivial)
  choose n hn hnX using hv
  refine ⟨∏ s ∈ S, n s, Finset.prod_pos fun s _ => hn s, ?_, ?_, ?_⟩
  · rw [trace_smul, htr, smul_zero]
  · intro x y
    have h := hskew x y
    simp only [herm, cc, smul_mulVec, Pi.smul_apply, smul_eq_mul, map_mul, map_natCast] at h ⊢
    have e1 : ∀ a b, (↑(∏ s ∈ S, n s) * (X *ᵥ x) a) * G a b * (IsCMField.complexConj E) (y b) =
        (↑(∏ s ∈ S, n s) : E) * ((X *ᵥ x) a * G a b * (IsCMField.complexConj E) (y b)) := fun a b => by ring
    have e2 : ∀ a b, x a * G a b * ((↑(∏ s ∈ S, n s) : E) * (IsCMField.complexConj E) ((X *ᵥ y) b)) =
        (↑(∏ s ∈ S, n s) : E) * (x a * G a b * (IsCMField.complexConj E) ((X *ᵥ y) b)) := fun a b => by ring
    simp only [e1, e2, ← Finset.mul_sum]
    rw [← mul_add, h, mul_zero]
  · intro x hx
    rw [← hS] at hx
    induction hx using Submodule.span_induction with
    | mem s hs =>
      rw [smul_mulVec]
      obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem n hs
      rw [hk, Nat.cast_mul, mul_comm, ← smul_smul, Nat.cast_smul_eq_nsmul]
      exact Λ.nsmul_mem (hnX s) k
    | zero => simp
    | add x y _ _ hx hy => rw [mulVec_add]; exact Λ.add_mem hx hy
    | smul a x _ hx =>
      rw [intSmul_eq, mulVec_smul, ← intSmul_eq]
      exact Λ.smul_mem a hx

end GlobalTheory.DenClear
end

section

open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate

namespace GlobalTheory

theorem holPart_eq_and_gaussian_of_orthogonal_symplectic (l : Type) [Fintype l] [DecidableEq l]
    (s : Matrix (l ⊕ l) (l ⊕ l) ℝ) (P Q : Matrix l l ℂ)
    (hP : ∀ a b, P a b = (s (.inl a) (.inl b) : ℂ) - I * (s (.inl a) (.inr b) : ℂ))
    (hQ : ∀ a b, Q a b = (s (.inr a) (.inl b) : ℂ) - I * (s (.inr a) (.inr b) : ℂ))
    (hs : s ∈ Matrix.symplecticGroup l ℝ) (ho : sᵀ * s = 1) (hd : P.det ≠ 0) :
    GlobalTheory.Published.Metaplectic.holPart s = P ∧ ∀ x : l → ℝ,
      cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ (-(Q * P⁻¹)) *ᵥ fun i => (x i : ℂ))) =
        cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)) := by
  have hJ : s * J l ℝ = J l ℝ * s := by
    have h2 : s * J l ℝ * sᵀ = J l ℝ := SymplecticGroup.mem_iff.mp hs
    calc s * J l ℝ = s * J l ℝ * (sᵀ * s) := by rw [ho, Matrix.mul_one]
      _ = (s * J l ℝ * sᵀ) * s := by simp only [Matrix.mul_assoc]
      _ = J l ℝ * s := by rw [h2]
  have e1 : ∀ a b, s (.inl a) (.inr b) = - s (.inr a) (.inl b) := by
    intro a b
    have := congrFun (congrFun hJ (.inl a)) (.inl b)
    simpa [J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply] using this
  have e2 : ∀ a b, s (.inr a) (.inr b) = s (.inl a) (.inl b) := by
    intro a b
    have := congrFun (congrFun hJ (.inl a)) (.inr b)
    simp [J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply] at this
    linarith
  have hh : GlobalTheory.Published.Metaplectic.holPart s = P := by
    ext a b
    simp only [GlobalTheory.Published.Metaplectic.holPart, hP, e2, e1]
    push_cast; ring
  have hQP : Q = (-I) • P := by
    ext a b
    simp only [hP, hQ, e2, e1, Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring_nf; rw [I_sq]; ring
  have hinv : -(Q * P⁻¹) = I • (1 : Matrix l l ℂ) := by
    rw [hQP, Matrix.smul_mul, mul_nonsing_inv P (isUnit_iff_ne_zero.mpr hd), neg_smul, neg_neg]
  refine ⟨hh, fun x => ?_⟩
  rw [hinv, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
  congr 1
  simp only [dotProduct]
  push_cast
  ring_nf; rw [I_sq]; ring

end GlobalTheory
end

section

open TensorProduct

theorem _root_.GlobalTheory.T.exists_ringHom_pair_eq_on_subfield_ne_of_not_mem_range : ∀ (L Ω : Type) [Field L] [Field Ω] [Algebra L Ω] [CharZero L] (a : Ω), a ∉ Set.range (algebraMap L Ω) → ∃ (F : Type) (_ : Field F) (i₁ i₂ : Ω →+* F), i₁.comp (algebraMap L Ω) = i₂.comp (algebraMap L Ω) ∧ i₁ a ≠ i₂ a := by
  first | exact @GlobalTheory.exists_embeddings_agree_on_subfield_ne | exact GlobalTheory.exists_embeddings_agree_on_subfield_ne | (intros; apply GlobalTheory.exists_embeddings_agree_on_subfield_ne <;> assumption)
end
