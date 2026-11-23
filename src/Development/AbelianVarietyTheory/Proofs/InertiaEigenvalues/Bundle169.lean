module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle151
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConnPhiExtensionGeneratorEqZeta
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InstTameDescentExponentDataPadicThree
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle140
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle057
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle128
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle129
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle119
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle141
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle095
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle080
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle058
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle059
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle065
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle146
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle147
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle149
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.etaleHermitianPair_structure_facts : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), (∀ y : A.L, algebraMap A.K A.L (A.NL y) = y * star y) ∧ (∀ y : A.L, algebraMap A.K A.L (Algebra.trace A.K A.L y) = y + star y) ∧ (Algebra.traceForm F A.K).Nondegenerate ∧ (∀ y : A.L, IsUnit y → A.etaK (A.NL y) = 1) ∧ A.etaK (-1) = 1 ∧ (∀ᶠ v in 𝓝 (1 : A.K), ∃ s : A.K, s ^ 2 = v) ∧ (∃ S : Set A.Kˣ, S.Finite ∧ A.IsReps S) ∧ (∀ S : Set A.Kˣ, A.IsReps S → S.Finite) ∧ (∀ μ : Measure A.K, μ.IsAddHaarMeasure → μ {t | ¬ IsUnit t} = 0) ∧ IsOpen A.OK ∧ IsCompact A.OK ∧ ∃ R : Subring A.K, (R : Set A.K) = A.OK := by
  first | exact @GlobalTheory.JR.EtFacts.main | exact GlobalTheory.JR.EtFacts.main | (intros; apply GlobalTheory.JR.EtFacts.main <;> assumption)
end

section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.breuilKisin_xiExt_mem_rigidTensor_iff : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] (P : PhiMod O K l e a ι) (k : ℝ), 1 / ((e : ℝ) * l) < k → ∀ w : Vec K a ι, P.xiExt w ∈ P.Lk k ↔ w ∈ P.Mext (R O K l k) := by
  first | exact @GlobalTheory.BK.xiExt_mem_Lk_iff | exact GlobalTheory.BK.xiExt_mem_Lk_iff | (intros; apply GlobalTheory.BK.xiExt_mem_Lk_iff <;> assumption)
end

section

open PowerSeries GlobalTheory.BK Function Finset

namespace GlobalTheory.BK.OrbitBound

variable {e : ℕ} (u : ZMod e)

theorem iter_mul (n : ℕ) (x : ZMod e) : (fun y => u * y)^[n] x = u ^ n * x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => rw [iterate_succ_apply, ih, pow_succ, mul_assoc]

noncomputable def orb (x : ZMod e) : Finset (ZMod e) :=
  (range (minimalPeriod (fun y => u * y) x)).image fun k => u ^ k * x

variable {a : ℕ} (ha : 0 < a) (hu : u ^ a = 1)
include ha hu

theorem mp_pos (x : ZMod e) : 0 < minimalPeriod (fun y => u * y) x :=
  IsPeriodicPt.minimalPeriod_pos ha (by
    change (fun y => u * y)^[a] x = x
    rw [iter_mul, hu, one_mul])

theorem pow_mp_mul (x : ZMod e) : u ^ minimalPeriod (fun y => u * y) x * x = x := by
  rw [← iter_mul]; exact iterate_minimalPeriod

theorem pow_mp_mul_mul (x : ZMod e) (k : ℕ) :
    u ^ (minimalPeriod (fun y => u * y) x * k) * x = x := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ, pow_add, mul_assoc, pow_mp_mul u ha hu x, ih]

theorem mp_sub_dvd (x y : ZMod e) : minimalPeriod (fun z => u * z) (x - y) ∣
    minimalPeriod (fun z => u * z) x * minimalPeriod (fun z => u * z) y := by
  apply IsPeriodicPt.minimalPeriod_dvd
  change (fun z => u * z)^[_] (x - y) = x - y
  rw [iter_mul, mul_sub, pow_mp_mul_mul u ha hu x, mul_comm (minimalPeriod _ x),
    pow_mp_mul_mul u ha hu y]

theorem mp_sub_pow_dvd (x : ZMod e) (k : ℕ) : minimalPeriod (fun z => u * z) (x - u ^ k * x) ∣
    minimalPeriod (fun z => u * z) x := by
  apply IsPeriodicPt.minimalPeriod_dvd
  change (fun z => u * z)^[_] (x - u ^ k * x) = x - u ^ k * x
  rw [iter_mul, mul_sub, mul_left_comm, pow_mp_mul u ha hu x]

theorem isUnit_u : IsUnit u :=
  have h : u * u ^ (a - 1) = 1 := by rw [← pow_succ', Nat.sub_add_cancel ha, hu]
  ⟨⟨u, u ^ (a - 1), h, by rw [mul_comm]; exact h⟩, rfl⟩

theorem card_orb (x : ZMod e) : (orb u x).card = minimalPeriod (fun y => u * y) x := by
  rw [orb, card_image_of_injOn, card_range]
  rw [coe_range]
  intro i hi j hj h
  refine iterate_injOn_Iio_minimalPeriod hi hj ?_
  simp only [iter_mul]
  exact h

theorem mem_orb (x : ZMod e) (n : ℕ) : u ^ n * x ∈ orb u x := by
  refine mem_image.2 ⟨n % minimalPeriod (fun y => u * y) x, mem_range.2 (Nat.mod_lt _ (mp_pos u ha hu x)), ?_⟩
  show u ^ (n % _) * x = u ^ n * x
  rw [← iter_mul, ← iter_mul]
  exact iterate_mod_minimalPeriod_eq

omit ha hu in
theorem orb_subset {Sig : Finset (ZMod e)} (hcl : ∀ c ∈ Sig, u * c ∈ Sig) {x : ZMod e}
    (hx : x ∈ Sig) : orb u x ⊆ Sig := by
  have key : ∀ k : ℕ, u ^ k * x ∈ Sig := by
    intro k
    induction k with
    | zero => simpa using hx
    | succ k ih => rw [pow_succ', mul_assoc]; exact hcl _ ih
  intro z hz
  obtain ⟨k, -, rfl⟩ := mem_image.1 hz
  exact key k

theorem four_mp_le (Sig : Finset (ZMod e)) (N : ℕ) (hcl : ∀ c ∈ Sig, u * c ∈ Sig) (h0 : (0 : ZMod e) ∈ Sig)
    (hN : Sig.card ≤ N) (h2 : 2 ≤ N) {x y : ZMod e} (hx : x ∈ Sig) (hy : y ∈ Sig) :
    4 * minimalPeriod (fun z => u * z) (x - y) ≤ N ^ 2 := by
  classical
  by_cases hyo : y ∈ orb u x
  · obtain ⟨k, -, rfl⟩ := mem_image.1 hyo
    have hle := Nat.le_of_dvd (mp_pos u ha hu x) (mp_sub_pow_dvd u ha hu x k)
    by_cases hx0 : x = 0
    · have h1 : minimalPeriod (fun y => u * y) x = 1 :=
        minimalPeriod_eq_one_iff_isFixedPt.2 (by simp [IsFixedPt, hx0])
      nlinarith
    · have hn0 : (0 : ZMod e) ∉ orb u x := by
        intro h
        obtain ⟨j, -, hj⟩ := mem_image.1 h
        exact hx0 (((isUnit_u u ha hu).pow j).mul_right_eq_zero.1 hj)
      have hsub : insert 0 (orb u x) ⊆ Sig := insert_subset h0 (orb_subset u hcl hx)
      have hc := card_le_card hsub
      rw [card_insert_of_notMem hn0, card_orb u ha hu] at hc
      nlinarith
  · have hdisj : Disjoint (orb u x) (orb u y) := by
      rw [disjoint_left]
      intro z hz1 hz2
      obtain ⟨i, -, rfl⟩ := mem_image.1 hz1
      obtain ⟨j, hj, hji⟩ := mem_image.1 hz2
      apply hyo
      have hy' : y = u ^ (minimalPeriod (fun z => u * z) y - j + i) * x := by
        rw [pow_add, mul_assoc, ← hji, ← mul_assoc, ← pow_add,
          Nat.sub_add_cancel (le_of_lt (mem_range.1 hj)), pow_mp_mul u ha hu y]
      rw [hy']
      exact mem_orb u ha hu x _
    have hsub : orb u x ∪ orb u y ⊆ Sig := union_subset (orb_subset u hcl hx) (orb_subset u hcl hy)
    have hc := card_le_card hsub
    rw [card_union_of_disjoint hdisj, card_orb u ha hu, card_orb u ha hu] at hc
    have hle := Nat.le_of_dvd (Nat.mul_pos (mp_pos u ha hu x) (mp_pos u ha hu y)) (mp_sub_dvd u ha hu x y)
    set m1 := minimalPeriod (fun z => u * z) x
    set m2 := minimalPeriod (fun z => u * z) y
    have h4 : 4 * (m1 * m2) ≤ (m1 + m2) ^ 2 := by
      zify; nlinarith [sq_nonneg ((m1 : ℤ) - m2)]
    have h5 : (m1 + m2) ^ 2 ≤ N ^ 2 := Nat.pow_le_pow_left (hc.trans hN) 2
    omega

end GlobalTheory.BK.OrbitBound

namespace GlobalTheory.BK


open OrbitBound in
theorem maxPeriod_bounds : ∀ (l e a : ℕ), l.Prime → 1 ≤ a → e + 1 = l ^ a → ∀ (Sig : Finset (ZMod e)) (N : ℕ),
    (∀ c ∈ Sig, (l : ZMod e) * c ∈ Sig) → (0 : ZMod e) ∈ Sig → Sig.card ≤ N → 2 ≤ N →
    1 ≤ maxPeriod l Sig ∧ 4 * maxPeriod l Sig ≤ N ^ 2 ∧ ∀ c ∈ Sig, frobPeriod l c ≤ maxPeriod l Sig := by
  intro l e a _ ha hea Sig N hcl h0 hN h2
  have hu : (l : ZMod e) ^ a = 1 := by
    rw [← Nat.cast_pow, ← hea]
    push_cast
    rw [ZMod.natCast_self, zero_add]
  have h00 : ((0 : ZMod e), (0 : ZMod e)) ∈ Sig ×ˢ Sig := mem_product.2 ⟨h0, h0⟩
  refine ⟨?_, ?_, ?_⟩
  · exact le_trans (Nat.succ_le_of_lt (mp_pos (l : ZMod e) ha hu ((0 : ZMod e) - 0)))
      (Finset.le_sup (f := fun p : ZMod e × ZMod e => frobPeriod l (p.1 - p.2)) h00)
  · obtain ⟨p, hp, hpe⟩ := Finset.exists_mem_eq_sup (Sig ×ˢ Sig) ⟨_, h00⟩
      (fun p : ZMod e × ZMod e => frobPeriod l (p.1 - p.2))
    unfold maxPeriod
    rw [hpe]
    exact four_mp_le (l : ZMod e) ha hu Sig N hcl h0 hN h2 (mem_product.1 hp).1 (mem_product.1 hp).2
  · intro c hc
    have := Finset.le_sup (f := fun p : ZMod e × ZMod e => frobPeriod l (p.1 - p.2))
      (mem_product.2 ⟨hc, h0⟩ : (c, (0 : ZMod e)) ∈ Sig ×ˢ Sig)
    simp only [sub_zero] at this
    exact this

end GlobalTheory.BK
end

section

noncomputable section

namespace GlobalTheory.BK

open PowerSeries Matrix

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero a] [TameDescentExponentData K l e a]

namespace Descent

variable {P : PhiMod O K l e a ι} (Δ : Descent P)

end Descent

open PowerSeries Matrix in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero a] [_root_.GlobalTheory.BK.TameDescentExponentData K l e a] in
private lemma actD_apply_shift_eq_zero_of_apply_eq_zero {P : _root_.GlobalTheory.BK.PhiMod O K l e a ι}
    (Δ : _root_.GlobalTheory.BK.Descent P) (g : _root_.GlobalTheory.BK.TameGal K l e a) {x : P.D} {σ : ZMod a}
    (hx : x σ = 0) : Δ.actD g x (σ + g.shift) = 0 := by
  classical
  set f : ZMod a → K⟦X⟧ := fun ρ => if ρ = σ then 0 else 1 with hf
  have hfx : f • _root_.GlobalTheory.BK.cst x = _root_.GlobalTheory.BK.cst x := by
    apply funext; intro ρ; apply funext; intro i
    show f ρ * PowerSeries.C (x ρ i) = PowerSeries.C (x ρ i)
    by_cases h : ρ = σ
    · simp [h, hx]
    · simp [hf, h]
  have key : Δ.actD g x = _root_.GlobalTheory.BK.red (Δ.act g (_root_.GlobalTheory.BK.cst x)) := rfl
  rw [key, ← hfx, _root_.GlobalTheory.BK.Descent.act_smul_tot]
  funext i
  show constantCoeff ((_root_.GlobalTheory.BK.ringAct g f (σ + g.shift)) *
    (Δ.act g (_root_.GlobalTheory.BK.cst x)) (σ + g.shift) i) = 0
  rw [_root_.GlobalTheory.BK.ringAct_apply]
  simp [hf]

open PowerSeries Matrix in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero a] [_root_.GlobalTheory.BK.TameDescentExponentData K l e a] in
private lemma actD_apply_shift_eq_of_apply_eq {P : _root_.GlobalTheory.BK.PhiMod O K l e a ι}
    (Δ : _root_.GlobalTheory.BK.Descent P) (g : _root_.GlobalTheory.BK.TameGal K l e a) {x y : P.D} {σ : ZMod a}
    (h : x σ = y σ) : Δ.actD g x (σ + g.shift) = Δ.actD g y (σ + g.shift) := by
  have hxy := actD_apply_shift_eq_zero_of_apply_eq_zero Δ g (x := x - y) (σ := σ) (by simp [h])
  rwa [map_sub, Pi.sub_apply, sub_eq_zero] at hxy

open PowerSeries Matrix in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero a] [_root_.GlobalTheory.BK.TameDescentExponentData K l e a] in
private lemma tameGal_inertia_root_pow (ζ : rootsOfUnity e K) (n : ℕ) (τ : ZMod a) :
    (_root_.GlobalTheory.BK.TameGal.inertia (l := l) (ζ ^ n)).root τ =
      (_root_.GlobalTheory.BK.TameGal.inertia (l := l) ζ).root τ ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, map_one, pow_zero]
    exact _root_.GlobalTheory.BK.TameGal.root_one τ
  | succ n ih =>
    rw [pow_succ, map_mul, _root_.GlobalTheory.BK.TameGal.root_mul,
      _root_.GlobalTheory.BK.TameGal.shift_inertia, sub_zero, ih, pow_succ]

open PowerSeries Matrix in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero a] [_root_.GlobalTheory.BK.TameDescentExponentData K l e a] in
private lemma chars_succ_subset_chars {P : _root_.GlobalTheory.BK.PhiMod O K l e a ι}
    (Δ : _root_.GlobalTheory.BK.Descent P) (τ : ZMod a) :
    Δ.chars (τ + 1) ⊆ Δ.chars τ := by
  rintro c ⟨x, hx0, hx⟩
  set F : _root_.GlobalTheory.BK.TameGal K l e a := _root_.GlobalTheory.BK.TameGal.fr with hF
  have hFs : F.shift = 1 := _root_.GlobalTheory.BK.TameGal.shift_fr
  have hFis : (F⁻¹).shift = -1 := by
    have hs := _root_.GlobalTheory.BK.TameGal.shift_mul F⁻¹ F
    rw [inv_mul_cancel, _root_.GlobalTheory.BK.TameGal.shift_one, hFs] at hs
    linear_combination -hs
  refine ⟨Δ.actD F⁻¹ x, fun h => hx0 ?_, fun ζ => ?_⟩
  · have hb := actD_apply_shift_eq_of_apply_eq Δ F (x := Δ.actD F⁻¹ x) (y := 0) (σ := τ)
      (by rw [h]; rfl)
    rwa [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply,
      map_zero, hFs] at hb
  · have hcomm : _root_.GlobalTheory.BK.TameGal.inertia ζ * F⁻¹ =
        F⁻¹ * _root_.GlobalTheory.BK.TameGal.inertia (ζ ^ l) := by
      rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, hF,
        _root_.GlobalTheory.BK.TameGal.fr_mul_inertia, mul_assoc, mul_inv_cancel, mul_one]
    have hroot : (_root_.GlobalTheory.BK.TameGal.inertia (l := l) (ζ ^ l)).root (τ + 1) ^ c.val =
        (_root_.GlobalTheory.BK.TameGal.inertia (l := l) ζ).root τ ^ c.val := by
      rw [tameGal_inertia_root_pow, ← _root_.GlobalTheory.BK.TameGal.root_sub_one, add_sub_cancel_right]
    have hb := actD_apply_shift_eq_of_apply_eq Δ F⁻¹ (σ := τ + 1)
      (x := Δ.actD (_root_.GlobalTheory.BK.TameGal.inertia (ζ ^ l)) x)
      (y := (_root_.GlobalTheory.BK.TameGal.inertia (l := l) ζ).root τ ^ c.val • x)
      (by rw [hx, hroot]; rfl)
    rw [hFis, add_neg_cancel_right, map_smul] at hb
    rw [← Module.End.mul_apply, ← map_mul, hcomm, map_mul, Module.End.mul_apply, hb,
      Pi.smul_apply]

open PowerSeries Matrix in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero a] [_root_.GlobalTheory.BK.TameDescentExponentData K l e a] in
private lemma prime_mul_mem_chars_succ_of_mem [NeZero e] {P : _root_.GlobalTheory.BK.PhiMod O K l e a ι}
    (Δ : _root_.GlobalTheory.BK.Descent P) {τ : ZMod a} {c : ZMod e}
    (hc : c ∈ Δ.chars τ) :
    (l : ZMod e) * c ∈ Δ.chars (τ + 1) := by
  obtain ⟨d, hd0, hd⟩ := hc
  refine ⟨P.phiD d, fun h => hd0 ?_, fun ζ => ?_⟩
  · have heq : P.phiD (Function.update (0 : P.D) τ (d τ)) = P.phiD 0 := by
      funext σ
      rw [_root_.GlobalTheory.BK.PhiMod.phiD_apply, map_zero]
      by_cases hσ : σ - 1 = τ
      · obtain rfl := eq_add_of_sub_eq hσ
        rw [add_sub_cancel_right, Function.update_self, Pi.zero_apply]
        rw [_root_.GlobalTheory.BK.PhiMod.phiD_apply, add_sub_cancel_right] at h
        exact h
      · simp [Function.update_of_ne hσ]
    simpa using congrFun (P.phiD.injective heq) τ
  · rw [_root_.GlobalTheory.BK.Descent.actD_phiD, _root_.GlobalTheory.BK.PhiMod.phiD_apply,
      _root_.GlobalTheory.BK.PhiMod.phiD_apply, add_sub_cancel_right, hd, mulVec_smul]
    congr 1
    have hr : (_root_.GlobalTheory.BK.TameGal.inertia (l := l) ζ).root τ =
        (_root_.GlobalTheory.BK.TameGal.inertia (l := l) ζ).root (τ + 1) ^ l := by
      rw [← _root_.GlobalTheory.BK.TameGal.root_sub_one, add_sub_cancel_right]
    have he := _root_.GlobalTheory.BK.TameGal.root_pow
      (_root_.GlobalTheory.BK.TameGal.inertia (l := l) ζ) (τ + 1)
    rw [hr, ← pow_mul, pow_eq_pow_mod _ he, pow_eq_pow_mod ((l : ZMod e) * c).val he,
      ZMod.val_mul, ZMod.val_natCast, Nat.mod_mod, Nat.mod_mul_mod]


open PowerSeries Matrix in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero a] [_root_.GlobalTheory.BK.TameDescentExponentData K l e a] in
theorem _root_.GlobalTheory.BK.chars_eq_and_mul_mem (O K : Type) [CommRing O] [NormedField K]
    [IsUltrametricDist K] [Algebra O K]
    [_root_.GlobalTheory.BK.IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [_root_.GlobalTheory.BK.TameDescentExponentData K l e a]
    (P : _root_.GlobalTheory.BK.PhiMod O K l e a ι) (Δ : _root_.GlobalTheory.BK.Descent P) :
    (∀ τ σ, Δ.chars τ = Δ.chars σ) ∧
      ∀ τ, ∀ c ∈ Δ.chars τ,
        (l : ZMod e) * c ∈ Δ.chars τ := by
  have hle : ∀ (τ : ZMod a) (n : ℕ),
      Δ.chars (τ + n) ⊆ Δ.chars τ := by
    intro τ n
    induction n with
    | zero => simp
    | succ n ih =>
      push_cast
      rw [← add_assoc]
      exact (chars_succ_subset_chars Δ _).trans ih
  have hsub : ∀ τ σ : ZMod a,
      Δ.chars τ ⊆ Δ.chars σ := by
    intro τ σ
    have hs := hle σ (τ - σ).val
    rwa [ZMod.natCast_zmod_val, add_sub_cancel] at hs
  exact ⟨fun τ σ => (hsub τ σ).antisymm (hsub σ τ),
    fun τ c hc => hsub (τ + 1) τ (prime_mul_mem_chars_succ_of_mem Δ hc)⟩

end GlobalTheory.BK
end
end

section

open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.senMultiplicity_lattice_count_relation : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (g : V →ₗ[k] V), Semi R.γ g → ∀ P Q : Submodule k⟦X⟧ V, IsLat P → IsLat Q → Q ≤ P → CondC g P → CondC g Q → ∀ s : ℕ, P ≤ sh (-s) Q → ∀ x : k, sen g P x + qmult g P Q (x + 1) = sen g Q x + qmult g P Q x ∧ (qmult g P Q x ≠ 0 → ∃ j : ℕ, 1 ≤ j ∧ j ≤ s ∧ sen g Q (x - j) ≠ 0) := by
  first | exact @GlobalTheory.PhiGam.Count.sen_count | exact GlobalTheory.PhiGam.Count.sen_count | (intros; apply GlobalTheory.PhiGam.Count.sen_count <;> assumption)
end

section

open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.genEigenMultiplicity_laurentShift_eq_sum_sen : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (g : V →ₗ[k] V), Semi R.γ g → ∀ N : Submodule k⟦X⟧ V, IsLat N → CondC g N → ∀ (a : ℤ) (m : ℕ) (x : k), qmult g (sh a N) (sh (a + m) N) x = ∑ j ∈ Finset.range m, sen g N (x + (a + j : ℤ)) := by
  first | exact @GlobalTheory.PhiGam.Range.qmult_sh_range | exact GlobalTheory.PhiGam.Range.qmult_sh_range | (intros; apply GlobalTheory.PhiGam.Range.qmult_sh_range <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.GLift

theorem act_mul' {k : Type} [CommRing k] {n : ℕ} (g h : GL (Fin n) k) (Y : Gl n k) :
    act (g * h) Y = act g (act h Y) := by
  simp only [act, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc, Matrix.mulVec_mulVec, Matrix.vecMul_vecMul]

theorem omega_lift {F : Type} [NontriviallyNormedField F] (r : ℕ) (Z : Gl r F) (μ l : F) :
    omega (GlobalTheory.JR.Step.lift Z μ l) = omega Z := by
  have h := (GlobalTheory.JR.transfer_factor_lemma F (r + 1)).1 (GlobalTheory.JR.Step.lift Z μ l)
  have hc : (Cm (GlobalTheory.JR.Step.lift Z μ l)).det = lastDet Z := rfl
  unfold omega eta
  rw [h, hc, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]

theorem orbG_lift : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (M : Meas (r + 1) F E) (M' : Meas r F E) (Z : Gl r F) (μ l : F), ‖μ‖ = 1 →
    Delta (inv (GlobalTheory.JR.Step.lift Z μ l)) ≠ 0 →
    orbG M (unitG (r + 1) F) (GlobalTheory.JR.Step.lift Z μ l) = (if ‖l‖ ≤ 1 then 1 else 0) * orbG M' (unitG r F) Z := by
  intro F E _ _ _ _ hU r M M' Z μ l hμ hΔ
  haveI := hU.ultraF
  haveI := hU.lcF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  obtain ⟨lc1, sc1⟩ := gl_lc_sc F (r + 1)
  letI := M.mG
  haveI := M.bG
  letI := M'.mG
  haveI := M'.bG
  haveI := M.haarG
  haveI := M'.haarG
  haveI := gl_unimodular F E (r + 1) M
  haveI := gl_unimodular F E r M'
  obtain ⟨hO, hC⟩ := GlobalTheory.T.integralGLSet_isOpen_and_isCompact F (r + 1)
  have hemb := GlobalTheory.T.isClosedEmbedding_diagOneGeneralLinearEmbedding F r
  have key := GlobalTheory.CosetIntegral.integral_eq_of_coset_support (GL (Fin (r + 1)) F) (GL (Fin r) F)
    (GlobalTheory.JR.Step.emb r F) hemb M.μG M'.μG (glOSub (r + 1) F) hO hC M.volG
    (by rw [coe_glOSub, GlobalTheory.T.preimage_diagOneGeneralLinearEmbedding_integralGLSet F r]; exact M'.volG)
    (fun g => unitG (r + 1) F (act g (GlobalTheory.JR.Step.lift Z μ l)) * omega (act g (GlobalTheory.JR.Step.lift Z μ l)))
    (fun k hk g => by
      simp only [act_mul', GlobalTheory.T.unitIndicatorGLBlock_glBorderedConjugationAction_integral F (r + 1) k hk, GlobalTheory.T.jacquetRallisTransferFactor_glBorderedConjugationAction_integral F (r + 1) k hk])
    (fun g hg => GlobalTheory.T.exists_integralGL_mul_diagOne_of_unitIndicator_lift_ne_zero F E r Z μ l hμ g (left_ne_zero_of_mul hg))
    ((GlobalTheory.T.hasCompactSupport_jacquetRallisOrbitalIntegrand F (r + 1) _ hΔ).comp_isClosedEmbedding hemb)
  unfold orbG
  rw [key]
  simp only [GlobalTheory.T.borderedConjugation_diagOne_liftBlockMatrix, GlobalTheory.T.unitIndicatorGLBlock_liftBlockMatrixWithLastBasis F r _ μ l hμ.le, omega_lift, mul_assoc]
  exact integral_const_mul _ _

end GlobalTheory.JR.GLift
end
end

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

theorem _root_.GlobalTheory.T.exists_integerMap_isIntegral_unramifiedInvolutionExt : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∃ φO : K.O →+* K'.O, (∀ x, algebraMap K'.O K'.E (φO x) = φ (algebraMap K.O K.E x)) ∧ @Algebra.IsIntegral K.O K'.O _ _ φO.toAlgebra := by
  first | exact @GlobalTheory.UnitLemma.Unr.intMap_isIntegral_of_unr | exact GlobalTheory.UnitLemma.Unr.intMap_isIntegral_of_unr | (intros; apply GlobalTheory.UnitLemma.Unr.intMap_isIntegral_of_unr <;> assumption)
end

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial IsLocalRing

theorem _root_.GlobalTheory.T.isIntegral_integers_unramifiedInvolutionExt : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → d ≠ 0 → ∀ y : K'.O, @IsIntegral K.O K'.E _ _ (φ.comp (algebraMap K.O K.E)).toAlgebra (algebraMap K'.O K'.E y) := by
  first | exact @GlobalTheory.UnitLemma.Unr.intO | exact GlobalTheory.UnitLemma.Unr.intO | (intros; apply GlobalTheory.UnitLemma.Unr.intO <;> assumption)
end

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

theorem _root_.GlobalTheory.T.exists_unit_trace_unramifiedInvolutionFieldExt : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∃ y : K'.O, ∃ a : K.O, IsUnit a ∧ @Algebra.trace K.E K'.E _ _ φ.toAlgebra (algebraMap K'.O K'.E y) = algebraMap K.O K.E a := by
  first | exact @GlobalTheory.UnitLemma.Unr.exists_trace_unit | exact GlobalTheory.UnitLemma.Unr.exists_trace_unit | (intros; apply GlobalTheory.UnitLemma.Unr.exists_trace_unit <;> assumption)
end
