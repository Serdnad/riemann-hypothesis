module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial
public import Mathlib.RingTheory.FiniteLength
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle070
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle069
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NabBijectiveWindow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle071
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle068
public import Mathlib.RingTheory.Finiteness.Nakayama
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteAlgebraLocalCompletion
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open PowerSeries GlobalTheory.BK Matrix GlobalTheory.LiftCoker

namespace GlobalTheory.UPow

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]

theorem isUnit_one_add_mul_uIn (f : A O K) : IsUnit (1 + f * uIn (A O K)) := by
  set g := (equivA O K).symm (1 + f * uIn (A O K))
  have hg : equivA O K g = 1 + f * uIn (A O K) := by simp [g]
  have hc : constantCoeff g = 1 := by
    apply IsUnitBall.inj (O := O) (K := K)
    have h1 := congrArg (fun x : A O K => constantCoeff (x : K⟦X⟧)) hg
    simp only [coe_equivA] at h1
    rw [map_one]
    have h2 : algebraMap O K (constantCoeff g) = constantCoeff ((PowerSeries.map (algebraMap O K)) g) := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        PowerSeries.coeff_map]
    rw [h2, h1]
    simp
  have hu : IsUnit g := by
    rw [PowerSeries.isUnit_iff_constantCoeff, hc]
    exact isUnit_one
  rw [← hg]
  exact hu.map (equivA O K)

theorem exists_uIn_pow_smul_eq_zero : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] (M : Type) [AddCommGroup M] [Module (A O K) M], IsFiniteLength (A O K) M →
    ∃ n : ℕ, ∀ x : M, (uIn (A O K)) ^ n • x = 0 := by
  intro O K _ _ _ _ _ M _ _ hM
  obtain ⟨hN, hA⟩ := isFiniteLength_iff_isNoetherian_isArtinian.1 hM
  set I : Ideal (A O K) := Ideal.span {uIn (A O K)}
  let F : ℕ →o (Submodule (A O K) M)ᵒᵈ :=
    ⟨fun k => OrderDual.toDual (I ^ k • (⊤ : Submodule (A O K) M)), fun i j hij =>
      Submodule.smul_mono_left (Ideal.pow_le_pow_right hij)⟩
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes F
  have hstab : I ^ n • (⊤ : Submodule (A O K) M) = I • (I ^ n • (⊤ : Submodule (A O K) M)) := by
    have : I ^ n • (⊤ : Submodule (A O K) M) = I ^ (n + 1) • (⊤ : Submodule (A O K) M) :=
      OrderDual.toDual_inj.1 (hn (n + 1) (Nat.le_succ n))
    rw [← Submodule.mul_smul, ← pow_succ', ← this]
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I
    (I ^ n • (⊤ : Submodule (A O K) M)) (IsNoetherian.noetherian _) hstab.le
  obtain ⟨f, hf⟩ := Ideal.mem_span_singleton'.1 hr
  have hru : IsUnit r := by
    have : r = 1 + f * uIn (A O K) := by rw [hf]; ring
    rw [this]
    exact isUnit_one_add_mul_uIn f
  refine ⟨n, fun x => ?_⟩
  have hmem : (uIn (A O K)) ^ n • x ∈ I ^ n • (⊤ : Submodule (A O K) M) :=
    Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) n) trivial
  have h0 := hr0 _ hmem
  obtain ⟨v, rfl⟩ := hru
  have := congrArg (fun y => ((v⁻¹ : (A O K)ˣ) : A O K) • y) h0
  simpa [smul_smul] using this

end GlobalTheory.UPow
end

section

noncomputable section
namespace GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

theorem sub_id_bij_of_contracting {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (I : Ideal A)
    [IsPrecomplete I M] [IsHausdorff I M] (T : M →+ M)
    (hT : ∀ (j : ℕ) (m : M), m ∈ (I ^ j • ⊤ : Submodule A M) → T m ∈ (I ^ (j + 1) • ⊤ : Submodule A M)) :
    (∀ b : M, ∃ m, T m - m = b) ∧ ∀ m : M, T m = m → m = 0 := by
  have hmem0 : ∀ m : M, m ∈ (I ^ 0 • ⊤ : Submodule A M) := by intro m; simp

  have hTpow : ∀ (j k : ℕ) (m : M), m ∈ (I ^ j • ⊤ : Submodule A M) →
      T^[k] m ∈ (I ^ (j + k) • ⊤ : Submodule A M) := by
    intro j k
    induction k with
    | zero => intro m hm; simpa using hm
    | succ k ih =>
      intro m hm
      rw [Function.iterate_succ_apply', ← add_assoc]
      exact hT _ _ (ih m hm)
  have hhaus : ∀ m : M, (∀ j, m ∈ (I ^ j • ⊤ : Submodule A M)) → m = 0 := fun m hm =>
    IsHausdorff.haus ‹IsHausdorff I M› m fun j => by rw [SModEq.zero]; exact hm j
  have hle : ∀ {j k : ℕ}, j ≤ k → (I ^ k • ⊤ : Submodule A M) ≤ I ^ j • ⊤ :=
    fun h => Submodule.smul_mono_left (Ideal.pow_le_pow_right h)
  refine ⟨fun b => ?_, fun m hm => hhaus m fun j => ?_⟩
  · have hiter : ∀ k, T^[k] b ∈ (I ^ k • ⊤ : Submodule A M) := fun k => by
      simpa using hTpow 0 k b (hmem0 b)

    have hcauchy : ∀ {m n : ℕ}, m ≤ n →
        (fun n => -(∑ k ∈ Finset.range n, T^[k] b)) m ≡
          (fun n => -(∑ k ∈ Finset.range n, T^[k] b)) n [SMOD (I ^ m • ⊤ : Submodule A M)] := by
      intro m n hmn
      rw [SModEq.sub_mem]
      have hd : -(∑ k ∈ Finset.range m, T^[k] b) - -(∑ k ∈ Finset.range n, T^[k] b) =
          ∑ k ∈ Finset.Ico m n, T^[k] b := by
        rw [Finset.sum_Ico_eq_sub _ hmn]
        abel
      simp only
      rw [hd]
      exact Submodule.sum_mem _ fun k hk => hle (Finset.mem_Ico.mp hk).1 (hiter k)
    obtain ⟨L, hL⟩ := IsPrecomplete.prec ‹IsPrecomplete I M› hcauchy
    refine ⟨L, sub_eq_zero.mp (hhaus _ fun j => ?_)⟩
    have h1 : L - -(∑ k ∈ Finset.range j, T^[k] b) ∈ (I ^ j • ⊤ : Submodule A M) := by
      have h := SModEq.sub_mem.mp (hL j)
      rw [← neg_sub]
      exact Submodule.neg_mem _ h
    have htel := Finset.sum_range_sub' (fun k => T^[k] b) j
    rw [Finset.sum_sub_distrib] at htel
    simp only [Function.iterate_zero_apply] at htel
    have hsucc : ∀ k, T (T^[k] b) = T^[k + 1] b := fun k => (Function.iterate_succ_apply' T k b).symm
    have h2 : T (-(∑ k ∈ Finset.range j, T^[k] b)) - -(∑ k ∈ Finset.range j, T^[k] b) - b =
        -(T^[j] b) := by

      rw [map_neg, map_sum]
      simp only [hsucc]
      have e : -(∑ k ∈ Finset.range j, T^[k + 1] b) - -(∑ k ∈ Finset.range j, T^[k] b) - b =
          ((∑ k ∈ Finset.range j, T^[k] b) - ∑ k ∈ Finset.range j, T^[k + 1] b) - b := by abel
      rw [e, htel]
      abel
    have h3 : T (L - -(∑ k ∈ Finset.range j, T^[k] b)) ∈ (I ^ j • ⊤ : Submodule A M) :=
      hle (Nat.le_succ j) (hT j _ h1)
    have hsplit : T L - L - b = (T (L - -(∑ k ∈ Finset.range j, T^[k] b)) -
        (L - -(∑ k ∈ Finset.range j, T^[k] b))) +
        (T (-(∑ k ∈ Finset.range j, T^[k] b)) - -(∑ k ∈ Finset.range j, T^[k] b) - b) := by
      rw [map_sub]
      abel
    rw [hsplit, h2]
    exact Submodule.add_mem _ (Submodule.sub_mem _ h3 h1) (Submodule.neg_mem _ (hiter j))
  · induction j with
    | zero => exact hmem0 m
    | succ j ih =>
      have h := hT j m ih
      rwa [hm] at h

theorem mem_span_pow_smul_top {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (x : A) (j : ℕ) (m : M) :
    m ∈ (Ideal.span {x} ^ j • ⊤ : Submodule A M) ↔ ∃ y, x ^ j • y = m := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  simp only [Submodule.mem_top, true_and]

theorem contracting_of_semi {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (x c : A) (T : M →+ M)
    (h1 : ∀ m, T (x • m) = (c * x) • T m) (h2 : ∀ m, ∃ y, x • y = T m) (j : ℕ) (m : M)
    (hm : m ∈ (Ideal.span {x} ^ j • ⊤ : Submodule A M)) :
    T m ∈ (Ideal.span {x} ^ (j + 1) • ⊤ : Submodule A M) := by
  rw [mem_span_pow_smul_top] at hm ⊢
  obtain ⟨y, rfl⟩ := hm
  obtain ⟨z, hz⟩ := h2 y
  have hpow : ∀ (i : ℕ) (m : M), T (x ^ i • m) = (c * x) ^ i • T m := by
    intro i
    induction i with
    | zero => intro m; simp
    | succ i ih => intro m; rw [pow_succ, mul_smul, ih, h1, smul_smul, ← pow_succ]
  refine ⟨c ^ j • z, ?_⟩
  rw [hpow, ← hz, smul_smul, smul_smul]
  congr 1
  ring

theorem one_sub_frob_bij : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {n : ℕ} [NeZero n] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (D : ModPG R n V), ∀ (P : ZMod n → Submodule k⟦X⟧ V), (∀ i, IsLat (P i)) → (∀ i, ∀ x ∈ P (i - 1), D.φ i x ∈ sh 1 (P i)) → (∀ b : ZMod n → V, (∀ i, b i ∈ P i) → ∃ m : ZMod n → V, (∀ i, m i ∈ P i) ∧ ∀ i, D.φ i (m (i - 1)) - m i = b i) ∧ ∀ m : ZMod n → V, (∀ i, m i ∈ P i) → (∀ i, D.φ i (m (i - 1)) = m i) → m = 0 := by
  intro k _ l _ _ R n _ V _ _ _ _ _ _ _ _ D P hP hφ

  have hcoe : ∀ (a : k⟦X⟧) (y : V), a • y = ((a : k⟦X⟧) : k⸨X⸩) • y := by
    intro a y
    rw [← algebraMap_smul k⸨X⸩ a y]
    rfl
  have hφP : ∀ i, ∀ x ∈ P (i - 1), ∃ y ∈ P i, (PowerSeries.X : k⟦X⟧) • y = D.φ i x := by
    intro i x hx
    obtain ⟨y, hy, hyx⟩ := mem_sh_iff_exists.mp (hφ i x hx)
    exact ⟨y, hy, by rw [hcoe, ← vv_eq_coe_X, ← hyx, zpow_one]⟩
  have hφmem : ∀ i, ∀ x ∈ P (i - 1), D.φ i x ∈ P i := by
    intro i x hx
    obtain ⟨y, hy, hyx⟩ := hφP i x hx
    rw [← hyx]
    exact (P i).smul_mem _ hy

  let T : ((i : ZMod n) → P i) →+ ((i : ZMod n) → P i) :=
    { toFun := fun m i => ⟨D.φ i (m (i - 1)), hφmem i _ (m (i - 1)).2⟩
      map_zero' := by
        funext i
        apply Subtype.ext
        simp
      map_add' := by
        intro a b
        funext i
        apply Subtype.ext
        simp [map_add (f := _)] }
  have : ∀ i, Module.Finite k⟦X⟧ (P i) := fun i => Module.Finite.iff_fg.mpr (hP i).1
  have hXtop : Ideal.span {(PowerSeries.X : k⟦X⟧)} ≠ ⊤ := by
    intro h
    have h1 := (Ideal.span_singleton_eq_top.mp h).map (PowerSeries.constantCoeff (R := k))
    simp at h1
  have : IsHausdorff (Ideal.span {(PowerSeries.X : k⟦X⟧)}) ((i : ZMod n) → P i) :=
    IsHausdorff.of_isLocalRing _ _ hXtop
  have : IsPrecomplete (Ideal.span {(PowerSeries.X : k⟦X⟧)}) ((i : ZMod n) → P i) :=
    ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isPrecomplete_finite_module _ _

  obtain ⟨u, hu⟩ := R.φ_v
  have hl : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have h1 : ∀ m : ((i : ZMod n) → P i), T ((PowerSeries.X : k⟦X⟧) • m) =
      (((u : k⟦X⟧) * PowerSeries.X ^ (l - 1)) * PowerSeries.X) • T m := by
    intro m
    funext i
    apply Subtype.ext
    simp only [T, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.smul_apply, Submodule.coe_smul]
    rw [hcoe, hcoe, ← vv_eq_coe_X, D.φ_semi, hu, PowerSeries.coe_mul, PowerSeries.coe_mul,
      PowerSeries.coe_pow, ← vv_eq_coe_X, mul_assoc, pow_sub_one_mul hl]
  have h2 : ∀ m : ((i : ZMod n) → P i), ∃ y : ((i : ZMod n) → P i),
      (PowerSeries.X : k⟦X⟧) • y = T m := by
    intro m
    choose y hy hyx using fun i => hφP i _ (m (i - 1)).2
    exact ⟨fun i => ⟨y i, hy i⟩, funext fun i => Subtype.ext (hyx i)⟩
  obtain ⟨hsurj, hinj⟩ := sub_id_bij_of_contracting (Ideal.span {(PowerSeries.X : k⟦X⟧)}) T
    (fun j m hm => contracting_of_semi _ _ T h1 h2 j m hm)
  refine ⟨fun b hb => ?_, fun m hm hfix => ?_⟩
  · obtain ⟨m, hm⟩ := hsurj (fun i => ⟨b i, hb i⟩)
    refine ⟨fun i => (m i : V), fun i => (m i).2, fun i => ?_⟩
    have h := congrArg (fun z => ((z i : P i) : V)) hm
    simpa [T] using h
  · have h := hinj (fun i => ⟨m i, hm i⟩) (funext fun i => Subtype.ext (hfix i))
    funext i
    have hi := congrArg (fun z => ((z i : P i) : V)) h
    simpa using hi

end GlobalTheory.PhiGam
end
end

section

open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.phiGammaLatticeFamily_image_of_surjective :
    ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l)
      {n : ℕ} [NeZero n]
      {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
      [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]
      [FiniteDimensional k⸨X⸩ V]
      {W : Type} [AddCommGroup W] [Module k⸨X⸩ W] [Module k⟦X⟧ W] [Module k W]
      [IsScalarTower k⟦X⟧ k⸨X⸩ W] [IsScalarTower k k⸨X⸩ W] [IsScalarTower k k⟦X⟧ W]
      [FiniteDimensional k⸨X⸩ W] (D : ModPG R n V) (D' : ModPG R n W)
      (f : ZMod n → V →ₗ[k⸨X⸩] W),
      (∀ i, Function.Surjective (f i)) →
      (∀ i x, f i (D.φ i x) = D'.φ i (f (i - 1) x)) →
      (∀ i x, f i (D.γ i x) = D'.γ i (f i x)) →
      ∀ (w w' : ZMod n → ℤ) (N : ZMod n → Submodule k⟦X⟧ V),
        (∀ i, IsLat (N i)) → CondAB D.φ w w' N → (∀ i, CondC (D.γ i) (N i)) →
        (let N' := fun i => (N i).map ((f i).restrictScalars k⟦X⟧)
         (∀ i, IsLat (N' i)) ∧ CondAB D'.φ w w' N' ∧ ∀ i, CondC (D'.γ i) (N' i)) := by
  intro k _ l _ _ R n _ V _ _ _ _ _ _ _ _ W _ _ _ _ _ _ _ _ D D' f hf hφ hγ w w' N hN hAB hC N'
  refine ⟨fun i => Img.isLat_map (f i) (hf i) (hN i), fun i => ?_, fun i => ?_⟩
  · simp only [N']
    rw [← Img.map_pull (f i) (f (i - 1)) (D.φ i) (D'.φ i) (hφ i), ← Img.map_sh, ← Img.map_sh]
    exact ⟨Submodule.map_mono (hAB i).1, Submodule.map_mono (hAB i).2⟩
  · rintro _ ⟨x, hx, rfl⟩
    simp only [N']
    rw [← Img.map_sh]
    refine ⟨_, hC i x hx, ?_⟩
    change f i _ = D'.γ i (f i x) - f i x
    rw [map_sub, hγ]
end

section

noncomputable section
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.PhiGam.Sat
variable {k : Type} [Field k]

section
variable {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k V] {l n : ℕ} {R : RingPG k l}

end

variable {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [IsScalarTower k⟦X⟧ k⸨X⸩ V]
  {W : Type} [AddCommGroup W] [Module k⸨X⸩ W] [Module k⟦X⟧ W] [IsScalarTower k⟦X⟧ k⸨X⸩ W]

theorem comap_sh (f : W →ₗ[k⸨X⸩] V) (a : ℤ) (N : Submodule k⟦X⟧ V) :
    (sh a N).comap (f.restrictScalars k⟦X⟧) = sh a (N.comap (f.restrictScalars k⟦X⟧)) := by
  ext x
  simp [mem_sh_iff_smul_mem]

theorem isLat_comap (f : W →ₗ[k⸨X⸩] V) (hf : Function.Injective f) {N : Submodule k⟦X⟧ V} (hN : IsLat N) :
    IsLat (N.comap (f.restrictScalars k⟦X⟧)) :=
  _root_.GlobalTheory.LatticeComap.main f hf hN

variable [Module k V] [Module k W] {l n : ℕ} {R : RingPG k l}

theorem comap_pull (D : ModPG R n V) (D' : ModPG R n W) (i : ZMod n) (f g : W →ₗ[k⸨X⸩] V)
    (hf : Function.Injective f) (hg : Function.Injective g) (hφ : ∀ x, g (D'.φ i x) = D.φ i (f x))
    {N : Submodule k⟦X⟧ V} (hN : N.FG) :
    (pull (D.φ i) N).comap (g.restrictScalars k⟦X⟧) = pull (D'.φ i) (N.comap (f.restrictScalars k⟦X⟧)) :=
  _root_.GlobalTheory.IndependentSpanDual.comap_pull D D' i f g hf hg hφ hN

theorem main : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l)
    {n : ℕ} [NeZero n]
    {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
    [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]
    [FiniteDimensional k⸨X⸩ V]
    {W : Type} [AddCommGroup W] [Module k⸨X⸩ W] [Module k⟦X⟧ W] [Module k W]
    [IsScalarTower k⟦X⟧ k⸨X⸩ W] [IsScalarTower k k⸨X⸩ W] [IsScalarTower k k⟦X⟧ W]
    [FiniteDimensional k⸨X⸩ W]
    (D : ModPG R n V) (D' : ModPG R n W) (f : ZMod n → W →ₗ[k⸨X⸩] V),
    (∀ i, Function.Injective (f i)) →
    (∀ i x, f i (D'.φ i x) = D.φ i (f (i - 1) x)) →
    (∀ i x, f i (D'.γ i x) = D.γ i (f i x)) →
    ∀ (w w' : ZMod n → ℤ) (N : ZMod n → Submodule k⟦X⟧ V),
      (∀ i, IsLat (N i)) → CondAB D.φ w w' N → (∀ i, CondC (D.γ i) (N i)) →
      (∀ i, IsLat ((N i).comap ((f i).restrictScalars k⟦X⟧))) ∧
      CondAB D'.φ w w' (fun i => (N i).comap ((f i).restrictScalars k⟦X⟧)) ∧
      ∀ i, CondC (D'.γ i) ((N i).comap ((f i).restrictScalars k⟦X⟧)) := by
  intro k _ l _ _ R n _ V _ _ _ _ _ _ _ _ W _ _ _ _ _ _ _ _ D D' f hf hφ hγ w w' N hN hAB hC
  refine ⟨fun i => isLat_comap _ (hf i) (hN i), fun i => ?_, fun i x hx => ?_⟩
  · have h := comap_pull D D' i (f (i - 1)) (f i) (hf _) (hf _) (hφ i) (hN (i - 1)).1
    rw [← h, ← comap_sh, ← comap_sh]
    exact ⟨Submodule.comap_mono (hAB i).1, Submodule.comap_mono (hAB i).2⟩
  · rw [← comap_sh]
    change f i _ ∈ sh 1 (N i)
    rw [map_sub, hγ]
    exact hC i _ hx

end GlobalTheory.PhiGam.Sat
end
end

section

noncomputable section
namespace GlobalTheory.PhiGam.SenShift
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

theorem mem_iSup_comap_pow {k U : Type} [Field k] [AddCommGroup U] [Module k U] (S : Module.End k U)
    (Q : Submodule k U) (hQ : ∀ p ∈ Q, S p ∈ Q) (u : U) :
    u ∈ (⨆ m : ℕ, Q.comap (S ^ m)) ↔ ∃ m : ℕ, (S ^ m) u ∈ Q := by
  have hmono : Monotone fun m : ℕ => Q.comap (S ^ m) := by
    refine monotone_nat_of_le_succ fun m p hp => ?_
    rw [Submodule.mem_comap] at hp ⊢
    rw [pow_succ', Module.End.mul_apply]
    exact hQ _ hp
  exact Submodule.mem_iSup_of_directed _ hmono.directed_le

theorem gmult_transport {k U : Type} [Field k] [AddCommGroup U] [Module k U] (T T' : Module.End k U)
    (P Q P' Q' : Submodule k U) (e : U ≃ₗ[k] U) (x y : k)
    (heP : ∀ u, e u ∈ P' ↔ u ∈ P) (heQ : ∀ u, e u ∈ Q' ↔ u ∈ Q)
    (hP : ∀ p ∈ P, T p ∈ P) (hQ : ∀ p ∈ Q, T p ∈ Q) (hQ' : ∀ p ∈ Q', T' p ∈ Q')
    (h : ∀ p ∈ P, T' (e p) - x • e p - e (T p - y • p) ∈ Q') :
    gmult T' P' Q' x = gmult T P Q y := by
  unfold gmult
  set S := T - algebraMap k (Module.End k U) y with hSdef
  set S' := T' - algebraMap k (Module.End k U) x with hS'def
  have hS : ∀ u, S u = T u - y • u := fun u => by simp [hSdef, Module.algebraMap_end_apply]
  have hS' : ∀ u, S' u = T' u - x • u := fun u => by simp [hS'def, Module.algebraMap_end_apply]
  have hSP : ∀ p ∈ P, S p ∈ P := fun p hp => by rw [hS]; exact P.sub_mem (hP p hp) (P.smul_mem _ hp)
  have hSQ : ∀ p ∈ Q, S p ∈ Q := fun p hp => by rw [hS]; exact Q.sub_mem (hQ p hp) (Q.smul_mem _ hp)
  have hSQ' : ∀ p ∈ Q', S' p ∈ Q' := fun p hp => by
    rw [hS']; exact Q'.sub_mem (hQ' p hp) (Q'.smul_mem _ hp)
  have hpow : ∀ m : ℕ, ∀ p ∈ P, (S ^ m) p ∈ P ∧ (S' ^ m) (e p) - e ((S ^ m) p) ∈ Q' := by
    intro m p hp
    induction m with
    | zero => simpa using hp
    | succ m ih =>
      obtain ⟨h1, h2⟩ := ih
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]
      refine ⟨hSP _ h1, ?_⟩
      have h3 := h _ h1
      rw [← hS, ← hS'] at h3
      have h4 := Q'.add_mem (hSQ' _ h2) h3
      rw [map_sub] at h4
      simpa using h4
  set A := P ⊓ ⨆ m : ℕ, Q.comap (S ^ m) with hA
  set A' := P' ⊓ ⨆ m : ℕ, Q'.comap (S' ^ m) with hA'
  have heA : ∀ u, e u ∈ A' ↔ u ∈ A := by
    intro u
    rw [hA, hA', Submodule.mem_inf, Submodule.mem_inf, heP, mem_iSup_comap_pow S Q hSQ,
      mem_iSup_comap_pow S' Q' hSQ']
    refine and_congr_right fun hu => exists_congr fun m => ?_
    rw [← heQ]
    have h2 := (hpow m u hu).2
    constructor
    · intro h1; simpa using Q'.sub_mem h1 h2
    · intro h1; simpa using Q'.add_mem h2 h1
  have hmap : A.map (e : U →ₗ[k] U) = A' := by
    ext u
    obtain ⟨u, rfl⟩ := e.surjective u
    rw [heA]
    exact Submodule.mem_map_equiv A |>.trans (by simp)
  let E : A ≃ₗ[k] A' := e.ofSubmodules A A' hmap
  have hE : ∀ z : A, ((E z : A') : U) = e z := fun z => rfl
  refine (Submodule.Quotient.equiv (Q.submoduleOf A) (Q'.submoduleOf A') E ?_).finrank_eq.symm
  ext z
  obtain ⟨z, rfl⟩ := E.surjective z
  refine (Submodule.mem_map_equiv _).trans ?_
  rw [LinearEquiv.symm_apply_apply]
  change (z : U) ∈ Q ↔ ((E z : A') : U) ∈ Q'
  rw [hE, heQ]

theorem sen_sh : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (g : V →ₗ[k] V), Semi R.γ g → ∀ N : Submodule k⟦X⟧ V, IsLat N → CondC g N → ∀ (a : ℤ) (x : k), sen g (sh a N) x = sen g N (x + a) := by
  intro k _ l _ _ R V _ _ _ _ _ _ _ _ g hg N _ hC a x
  have hv : vv k ≠ 0 := vv_ne_zero k
  let e : V ≃ₗ[k] V :=
    (LinearEquiv.smulOfNeZero k⸨X⸩ V (vv k ^ a) (zpow_ne_zero a hv)).restrictScalars k
  have he : ∀ u, e u = vv k ^ a • u := fun u => rfl
  have hmem : ∀ (M : Submodule k⟦X⟧ V) (u : V), e u ∈ sh a M ↔ u ∈ M := fun M u => by
    rw [he, mem_sh_iff_smul_mem, smul_smul, ← zpow_add₀ hv, neg_add_cancel, zpow_zero, one_smul]
  have hsh : sh 1 (sh a N) = sh a (sh 1 N) := by rw [sh_sh_eq, sh_sh_eq, add_comm]
  unfold sen qmult
  refine gmult_transport (nab g) (nab g) _ _ _ _ e x (x + a) (fun u => hmem N u) (fun u => ?_)
    (fun p hp => Window.nab_mem hC hp) (fun p hp => Window.nab_mem_sh R hg hC 1 hp) (fun p hp => ?_)
    (fun p hp => ?_)
  · rw [hsh]; exact hmem _ u
  · rw [sh_sh_eq] at hp ⊢
    exact Window.nab_mem_sh R hg hC _ hp
  · obtain ⟨n', hn', h⟩ := Window.nab_shift R hg hC a hp
    rw [← he, ← he] at h
    rw [hsh, h, ← map_smul, ← map_sub, ← map_sub]
    refine (hmem _ _).2 (mem_sh_iff_exists.2 ⟨n', hn', ?_⟩)
    rw [zpow_one, add_smul]
    abel

end GlobalTheory.PhiGam.SenShift
end
end

section

open GlobalTheory.UnitLemma GlobalTheory.StableLatCount Polynomial

theorem _root_.GlobalTheory.T.lattice_hom_submodule_fg_and_span_eq_top : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (E : Type) [Field E] [Algebra O E] [IsFractionRing O E] (A₁ A₂ : Type) [CommRing A₁] [CommRing A₂] [Algebra E A₁] [Algebra E A₂] [Algebra O A₁] [Algebra O A₂] [IsScalarTower O E A₁] [IsScalarTower O E A₂] [Module.Finite E A₁] [Module.Finite E A₂] (M₁ : Submodule O A₁) (M₂ : Submodule O A₂), IsLat O E M₁ → IsLat O E M₂ → (homLat E M₁ M₂).FG ∧ Submodule.span E (homLat E M₁ M₂ : Set (A₂ →ₗ[E] A₁)) = ⊤ := by
  first | exact @GlobalTheory.StableLatCount.homLat_fg_and_span_eq_top | exact GlobalTheory.StableLatCount.homLat_fg_and_span_eq_top | (intros; apply GlobalTheory.StableLatCount.homLat_fg_and_span_eq_top <;> assumption)
end
