module

public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle002
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CoarseDegreeAlternative
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.ThresholdLowerBounds
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle003
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

theorem le_and_half_le_prod_one_sub_exp_neg_of_bounds {a b' k Q Y La N1 A0 m M : ℝ} (hk : 5 ≤ k) (hQ : 1 ≤ Q) (hY : 1 ≤ Y) (hN1 : 1 ≤ N1) (hLa : 24 ≤ La)
    (hb : 0 < b') (hab : k * Y * La * b' ≤ a) (hkQ : k ^ 3 * Q ≤ b') (hA0 : a / (2 * Q) ≤ A0) (hm0 : 0 ≤ m)
    (hm : m ≤ b' / (k * Q * Y)) (hM0 : 0 ≤ M) (hM : M < m + 1) :
    M ≤ A0 * N1 * La / k ∧
      1 / 2 ≤ (1 - Real.exp (-La / 8)) * (1 - Real.exp (-La / 3)) * (1 - (k - 1) * M / A0) := by
  have hk0 : 0 < k := by linarith
  have hQ0 : 0 < Q := by linarith
  have hY0 : 0 < Y := by linarith
  have hkQ0 : 0 < k * Q := mul_pos hk0 hQ0

  have h1 : m * (k * Q * Y) ≤ b' := (le_div_iff₀ (mul_pos hkQ0 hY0)).mp hm
  have h2 : m * (k * Q) ≤ b' := by
    have : m * (k * Q) * 1 ≤ m * (k * Q) * Y := mul_le_mul_of_nonneg_left hY (mul_nonneg hm0 hkQ0.le)
    nlinarith

  have h3 : k * Q ≤ b' := by
    have hk2 : 1 ≤ k ^ 2 := by nlinarith
    have : k * Q * 1 ≤ k * Q * k ^ 2 := mul_le_mul_of_nonneg_left hk2 hkQ0.le
    nlinarith
  have h4 : M * (k * Q) ≤ 2 * b' := by
    have : M * (k * Q) ≤ (m + 1) * (k * Q) := mul_le_mul_of_nonneg_right hM.le hkQ0.le
    linarith

  have h5 : 120 * b' ≤ a := by
    have e1 : 5 ≤ k * Y := by nlinarith
    have e2 : 120 ≤ k * Y * La := by nlinarith
    have : 120 * b' ≤ k * Y * La * b' := mul_le_mul_of_nonneg_right e2 hb.le
    linarith
  have h6 : a ≤ A0 * (2 * Q) := (div_le_iff₀ (by linarith)).mp hA0
  have hA0pos : 0 < A0 := by
    have : 0 < A0 * (2 * Q) := by linarith
    by_contra hneg
    have hle : A0 ≤ 0 := not_lt.mp hneg
    have : A0 * (2 * Q) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hle (by linarith)
    linarith
  constructor
  · rw [le_div_iff₀ hk0]
    have e1 : 24 ≤ N1 * La := by nlinarith
    have e2 : A0 * 24 ≤ A0 * (N1 * La) := mul_le_mul_of_nonneg_left e1 hA0pos.le
    have e3 : (M * k) * Q ≤ (A0 * N1 * La) * Q := by
      have : A0 * 24 * Q ≤ A0 * (N1 * La) * Q := mul_le_mul_of_nonneg_right e2 hQ0.le
      nlinarith
    exact le_of_mul_le_mul_right e3 hQ0
  · have hx : (k - 1) * M / A0 ≤ 1 / 30 := by
      rw [div_le_iff₀ hA0pos]
      have e1 : (k - 1) * M ≤ k * M := by nlinarith
      have e3 : (k * M) * Q ≤ (1 / 30 * A0) * Q := by nlinarith
      have := le_of_mul_le_mul_right e3 hQ0
      linarith
    have he1 : Real.exp (-La / 8) ≤ 1 / 4 := by
      have a1 : Real.exp (-La / 8) ≤ Real.exp (-3) := Real.exp_le_exp.mpr (by linarith)
      have a2 : (4 : ℝ) ≤ Real.exp 3 := by have := Real.add_one_le_exp (3 : ℝ); linarith
      have a3 : Real.exp (-3) = (Real.exp 3)⁻¹ := Real.exp_neg 3
      have a4 : (Real.exp 3)⁻¹ ≤ (4 : ℝ)⁻¹ := inv_anti₀ (by norm_num) a2
      rw [a3] at a1
      linarith [a1, a4, (by norm_num : (4 : ℝ)⁻¹ = 1 / 4)]
    have he2 : Real.exp (-La / 3) ≤ 1 / 9 := by
      have a1 : Real.exp (-La / 3) ≤ Real.exp (-8) := Real.exp_le_exp.mpr (by linarith)
      have a2 : (9 : ℝ) ≤ Real.exp 8 := by have := Real.add_one_le_exp (8 : ℝ); linarith
      have a3 : Real.exp (-8) = (Real.exp 8)⁻¹ := Real.exp_neg 8
      have a4 : (Real.exp 8)⁻¹ ≤ (9 : ℝ)⁻¹ := inv_anti₀ (by norm_num) a2
      rw [a3] at a1
      linarith [a1, a4, (by norm_num : (9 : ℝ)⁻¹ = 1 / 9)]
    have u1 : 3 / 4 ≤ 1 - Real.exp (-La / 8) := by linarith
    have u2 : 8 / 9 ≤ 1 - Real.exp (-La / 3) := by linarith
    have u3 : 29 / 30 ≤ 1 - (k - 1) * M / A0 := by linarith
    have v1 : (3 / 4 : ℝ) * (8 / 9) ≤ (1 - Real.exp (-La / 8)) * (1 - Real.exp (-La / 3)) :=
      mul_le_mul u1 u2 (by norm_num) (by linarith)
    have v2 : (3 / 4 : ℝ) * (8 / 9) * (29 / 30) ≤
        (1 - Real.exp (-La / 8)) * (1 - Real.exp (-La / 3)) * (1 - (k - 1) * M / A0) :=
      mul_le_mul v1 u3 (by norm_num) (by linarith)
    linarith [v2, (by norm_num : (1 / 2 : ℝ) ≤ (3 / 4 : ℝ) * (8 / 9) * (29 / 30))]

section Plug

variable {C0 Cde CE1 CE2 H : ℝ} {X : Loc}

theorem Std.half_ratio_le_segment_base_of_std (h : Std C0 Cde CE1 CE2 H X) (j : Fin (numSeg X.TT)) :
    (X.a : ℝ) / (2 * X.Q) ≤ ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) := by
  have hA : (X.seg C0 CE1 CE2 j).A0 X.p =
      ⌊((X.a : ℝ) - X.E0 C0 CE1 CE2) / ((X.p ^ segG X.TT j : ℕ) : ℝ)⌋ := rfl
  rw [hA]
  have hp1 := h.p1
  have ha := h.apos
  have hQ1 := h.Q1
  have hQ0 : 0 < X.Q := by linarith
  have hQj1 : (1 : ℝ) ≤ ((X.p ^ segG X.TT j : ℕ) : ℝ) := by
    push_cast
    exact one_le_pow₀ hp1
  have hQj0 : (0 : ℝ) < ((X.p ^ segG X.TT j : ℕ) : ℝ) := by linarith
  have hQjQ : ((X.p ^ segG X.TT j : ℕ) : ℝ) ≤ X.Q := by
    push_cast
    exact pow_le_pow_right₀ hp1 (h.segB j).1
  have hε : (X.N1 : ℝ) * X.La C0 / X.k ≤ 1 / 240 := by
    have h1 := h.LaK
    have h2 := h.de6
    have : 40 * (X.N1 : ℝ) * X.La C0 / X.k = 40 * ((X.N1 : ℝ) * X.La C0 / X.k) := by ring
    rw [this] at h1
    linarith
  have hN5 : X.E0 C0 CE1 CE2 + X.Q ≤ (X.a : ℝ) / 240 := by
    have h1 := h.N5
    have h2 : X.E0 C0 CE1 CE2 / X.a + X.Q / X.a = (X.E0 C0 CE1 CE2 + X.Q) / X.a := by ring
    rw [h2] at h1
    have h3 : (X.E0 C0 CE1 CE2 + X.Q) / X.a ≤ 1 / 240 := le_trans h1 hε
    have := (div_le_iff₀ ha).mp h3
    linarith
  have hnum : 0 ≤ (X.a : ℝ) - X.E0 C0 CE1 CE2 := by linarith
  have h1 : ((X.a : ℝ) - X.E0 C0 CE1 CE2) / X.Q ≤
      ((X.a : ℝ) - X.E0 C0 CE1 CE2) / ((X.p ^ segG X.TT j : ℕ) : ℝ) :=
    div_le_div_of_nonneg_left hnum hQj0 hQjQ
  have h2 := Int.sub_one_lt_floor (((X.a : ℝ) - X.E0 C0 CE1 CE2) / ((X.p ^ segG X.TT j : ℕ) : ℝ))
  have h3 : (X.a : ℝ) / (2 * X.Q) ≤ ((X.a : ℝ) - X.E0 C0 CE1 CE2) / X.Q - 1 := by
    rw [div_le_iff₀ (by linarith)]
    have : (((X.a : ℝ) - X.E0 C0 CE1 CE2) / X.Q - 1) * (2 * X.Q) =
        2 * ((X.a : ℝ) - X.E0 C0 CE1 CE2 - X.Q) := by
      field_simp
    rw [this]
    linarith
  linarith

theorem Std.La_ge (h : Std C0 Cde CE1 CE2 H X) (hC0 : 0 ≤ C0) : C0 ≤ X.La C0 := by
  have h1 := h.loga
  have h2 := h.one_le_level_alt
  unfold Loc.La lambdaScale
  have h3 : (1 : ℝ) ≤ (X.N1 : ℝ) ^ 2 := by nlinarith
  have h4 : C0 * 1 ≤ C0 * (X.N1 : ℝ) ^ 2 := mul_le_mul_of_nonneg_left h3 hC0
  have h5 : C0 * (X.N1 : ℝ) ^ 2 * 1 ≤ C0 * (X.N1 : ℝ) ^ 2 * Real.log X.a :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  linarith

end Plug

theorem one_segment_of_upper_lower {D : Formalism.BasicNotions.D7} (hU : RestUp) (hL : RestLow) : RootMultiplicityTwoBeyond D := by
  have hS : TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => 24 ≤ C0 ∧
      ∀ X : Loc, D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X → Std C0 Cde CE1 CE2 1 X :=
    TransportedAlt.of_explicit (fun _ => 24) (fun _ _ => 1) (fun Cc _ CE1 CE2 _ => T2 CE1 CE2 Cc 1)
      fun _ _ _ _ _ _ _ _ _ _ hCc hC0 h24 h1 h2 _ _ _ _ _ _ _ _ _ t1 t2 t3 t4 t5 =>
        ⟨h24, fun _ hD hI hc => std_of hCc hC0 h1 h2 le_rfl t1 t2 t3 t4 t5 hD hI hc⟩
  refine TransportedAlt.mono ?_ ((hS.and hU).and hL)
  rintro C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc ⟨⟨⟨h24, hstd⟩, up⟩, low⟩
  intro X _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ jO w hSet hH hc j m hm0 hmM rz ry hd
  have hD1 : D1num X := ⟨hSet.1.prime, hSet.1.five_le, hSet.1.two_le, hSet.1.even⟩
  have hs := hstd X hD1 hH hc
  have hLa : 24 ≤ X.La C0 := le_trans h24 (hs.La_ge (by linarith))
  have hcore := le_and_half_le_prod_one_sub_exp_neg_of_bounds (M := ((⌈m⌉₊ : ℕ) : ℝ)) hs.k5 hs.Q1 hs.Y1 hs.one_le_level_alt hLa hs.bpos hs.kYLab (hs.kQ le_rfl) (hs.half_ratio_le_segment_base_of_std j)
    hm0 hmM (Nat.cast_nonneg _) (Nat.ceil_lt_add_one hm0)
  refine ⟨?_, up X W Qq O Kf ι σ jO w hSet hH hc j m hm0 rz ry hd⟩
  have hlow := low X W Qq O Kf ι σ jO w hSet hH hc j m hm0 hcore.1 rz ry hd
  have hfac : 1 / 2 ≤ lowFac C0 CE1 CE2 X j ⌈m⌉₊ := by
    have hkm : (X.m : ℝ) = X.k - 1 := by unfold Loc.k; ring
    unfold lowFac
    rw [hkm]
    exact hcore.2
  have hmm : (0 : ℝ) ≤ (mmB C0 CE1 CE2 X j rz ry : ℝ) := Nat.cast_nonneg _
  have h1 : 1 / 2 * (mmB C0 CE1 CE2 X j rz ry : ℝ) ≤ lowFac C0 CE1 CE2 X j ⌈m⌉₊ * (mmB C0 CE1 CE2 X j rz ry : ℝ) :=
    mul_le_mul_of_nonneg_right hfac hmm
  have h2 : (mmB C0 CE1 CE2 X j rz ry : ℝ) / 2 ≤ (rankOnDigits O C0 CE1 CE2 X j m rz ry : ℝ) := by linarith
  exact h2

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

theorem ycond_mono' {K : Type*} [CommRing K] {N r : ℕ} [NeZero r] (LL : ChainLetters N) (j : ℕ) {M M' : WithTop ℤ}
    (h : M' ≤ M) : YCond K (r := r) LL j M' ≤ YCond K (r := r) LL j M := by
  unfold YCond
  apply sSup_le_sSup
  rintro S ⟨hS1, hS2⟩
  refine ⟨le_trans hS1 ?_, hS2⟩
  intro x hx
  rw [MvPolynomial.mem_restrictSupport_iff] at hx ⊢
  exact fun m hm => le_trans (hx hm) h

theorem yjt_mono' {K : Type*} [CommRing K] {N r : ℕ} [NeZero r] (LL : ChainLetters N) {q : ℕ} (J : Fin q → ℕ)
    {M M' : Fin q → WithTop ℤ} (h : ∀ k, M' k ≤ M k) : Yjt K (r := r) LL J M' ≤ Yjt K (r := r) LL J M :=
  inf_le_inf_left _ (iInf_mono fun k => ycond_mono' (K := K) (r := r) LL (J k) (h k))

theorem map_floor_mono (x : WithTop ℤ) {m m' : ℝ} (h : m ≤ m') :
    x.map (fun y : ℤ => ⌊(y : ℝ) - m'⌋) ≤ x.map (fun y : ℤ => ⌊(y : ℝ) - m⌋) := by
  cases x with
  | top => simp
  | coe y =>
    simp only [WithTop.map_coe, WithTop.coe_le_coe]
    exact Int.floor_mono (by linarith)

theorem monoAt : MonoAt := by
  intro O _ _ p r _ s S aTop aPlus b m m' hmm
  unfold BlockData.SSZ
  apply Submodule.span_mono
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨j, jp, hL, hx⟩ := hx
  obtain ⟨y, hy, g0, hg0, rfl⟩ := hx
  exact Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨jp, Set.mem_iUnion.2 ⟨hL,
    ⟨y, ⟨yjt_mono' _ _ (fun k => map_floor_mono _ hmm) hy.1, hy.2⟩, g0, hg0, rfl⟩⟩⟩⟩

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

abbrev IntAlg (O : Type) [CommRing O] [IsDomain O] (σ : Type*) : Subalgebra O (MvPolynomial σ (KK O)) :=
  (MvPolynomial.mapAlgHom (Algebra.ofId O (KK O)) : MvPolynomial σ O →ₐ[O] MvPolynomial σ (KK O)).range

theorem X_mem_intAlg (O : Type) [CommRing O] [IsDomain O] {σ : Type*} (v : σ) : (X v : MvPolynomial σ (KK O)) ∈ IntAlg O σ := by
  exact (AlgHom.mem_range _).mpr ⟨MvPolynomial.X v, by simp⟩

theorem intPol_le (O : Type) [CommRing O] [IsDomain O] {σ : Type*} {P : MvPolynomial σ (KK O)} (h : P ∈ IntPol O σ) :
    P ∈ IntAlg O σ := by
  obtain ⟨Q, hQ⟩ := LinearMap.mem_range.mp h
  exact (AlgHom.mem_range _).mpr ⟨Q, hQ⟩

theorem inA_of_mem (O : Type) [CommRing O] [IsDomain O] {σ : Type*} {P : MvPolynomial σ (KK O)} (h : P ∈ IntAlg O σ) :
    InA (O := O) P := by
  obtain ⟨Q, rfl⟩ := (AlgHom.mem_range _).mp h
  unfold InA
  intro m
  exact ⟨Q.coeff m, by simp [MvPolynomial.mapAlgHom_apply, MvPolynomial.coeff_map]⟩

theorem rename_mem_intAlg (O : Type) [CommRing O] [IsDomain O] {σ τ : Type*} (f : σ → τ) {P : MvPolynomial σ (KK O)}
    (h : P ∈ IntAlg O σ) : rename f P ∈ IntAlg O τ := by
  obtain ⟨Q, rfl⟩ := (AlgHom.mem_range _).mp h
  exact (AlgHom.mem_range _).mpr ⟨rename f Q, by simp [MvPolynomial.mapAlgHom_apply, MvPolynomial.map_rename]⟩

theorem aeval_mem_intAlg (O : Type) [CommRing O] [IsDomain O] {σ τ : Type*} (f : σ → MvPolynomial τ (KK O))
    (hf : ∀ v, f v ∈ IntAlg O τ) {P : MvPolynomial σ (KK O)} (h : P ∈ IntAlg O σ) : aeval f P ∈ IntAlg O τ := by
  obtain ⟨Q, rfl⟩ := (AlgHom.mem_range _).mp h
  have e : (MvPolynomial.mapAlgHom (Algebra.ofId O (KK O)) : MvPolynomial σ O →ₐ[O] MvPolynomial σ (KK O)) Q =
      MvPolynomial.map (algebraMap O (KK O)) Q := rfl
  rw [e, MvPolynomial.aeval_map_algebraMap]
  clear h e
  induction Q using MvPolynomial.induction_on with
  | C a => rw [MvPolynomial.aeval_C]; exact Subalgebra.algebraMap_mem _ a
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p v hp => rw [map_mul, MvPolynomial.aeval_X]; exact mul_mem hp (hf v)

theorem ssz_le_intAlg (O : Type) [CommRing O] [IsDomain O] {N r : ℕ} [NeZero r] (D : BlockData N) :
    ∀ x ∈ D.SSZ O (r := r), x ∈ IntAlg O (BVar N r D.T.t) := by
  intro x hx
  unfold BlockData.SSZ at hx
  refine Submodule.span_induction (p := fun x _ => x ∈ IntAlg O (BVar N r D.T.t)) ?_ ?_ ?_ ?_ hx
  · intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨j, jp, _, y, hy, g0, hg0, rfl⟩ := hx
    have hX := fun v => X_mem_intAlg O (σ := BVar N r D.T.t) v
    have hE : ∀ i, D.Ehat O (r := r) i ∈ IntAlg O (BVar N r D.T.t) := fun i => by
      unfold BlockData.Ehat
      exact (IntAlg O _).add_mem ((IntAlg O _).mul_mem (hX _) (hX _))
        ((IntAlg O _).sum_mem fun c _ => (IntAlg O _).mul_mem (hX _) (hX _))
    have hP : D.Eplus O (r := r) ∈ IntAlg O (BVar N r D.T.t) := by
      unfold BlockData.Eplus
      exact (IntAlg O _).add_mem ((IntAlg O _).mul_mem (hX _) (hX _))
        ((IntAlg O _).sum_mem fun c _ => (IntAlg O _).mul_mem (hX _) (hX _))
    refine (IntAlg O _).mul_mem ((IntAlg O _).mul_mem ((IntAlg O _).mul_mem ((IntAlg O _).mul_mem
      ((IntAlg O _).mul_mem ((IntAlg O _).prod_mem fun i _ => (IntAlg O _).pow_mem (hE i) _)
        ((IntAlg O _).pow_mem hP _)) ((IntAlg O _).prod_mem fun i _ => (IntAlg O _).pow_mem (hX _) _))
      ((IntAlg O _).pow_mem (hX _) _)) (rename_mem_intAlg O _ (intPol_le O hy.2))) (intPol_le O hg0.2)
  · exact (IntAlg O _).zero_mem
  · intro x y _ _ hx hy; exact (IntAlg O _).add_mem hx hy
  · intro a x _ hx; exact (IntAlg O _).smul_mem hx a

theorem symIntAt (C0 CE1 CE2 : ℝ) : SymIntAt C0 CE1 CE2 := by
  intro X _ O _ _ mm β s hs
  apply inA_of_mem
  unfold symFam
  refine (IntAlg O _).prod_mem fun j _ => ?_
  unfold ioBlock
  have hX := fun v => X_mem_intAlg O (σ := (X.TT × Bool) × Fin (X.m + 1)) v
  refine (IntAlg O _).mul_mem ((IntAlg O _).mul_mem ?_ ?_) ?_
  · unfold digitMon
    exact (IntAlg O _).prod_mem fun i _ => (IntAlg O _).prod_mem fun c _ =>
      (IntAlg O _).mul_mem ((IntAlg O _).pow_mem (hX _) _) ((IntAlg O _).pow_mem (hX _) _)
  · unfold sTopMon
    refine (IntAlg O _).prod_mem fun i _ => ?_
    split_ifs
    · exact (IntAlg O _).mul_mem ((IntAlg O _).pow_mem (hX _) _) ((IntAlg O _).pow_mem (hX _) _)
    · exact (IntAlg O _).one_mem
  · have hsj : s j ∈ IntAlg O (BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) :=
      ssz_le_intAlg O (r := X.m)
        (blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) mm (β j)) (s j) (hs j)
    exact aeval_mem_intAlg O _ (fun v => (IntAlg O _).pow_mem (hX _) _) hsj

end Formalism.MainNotions.ColumnSystems.Pf
end
end
