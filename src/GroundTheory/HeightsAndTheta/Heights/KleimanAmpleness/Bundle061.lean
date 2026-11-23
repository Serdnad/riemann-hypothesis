module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle055
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle045
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle056
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle046
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle051
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsSumEqOneOfMulEqOne
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle044
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle014
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle050
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle047
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle026
public import Mathlib.Algebra.MvPolynomial.Funext
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mConeMapOver mIdealOver chartRingOver)

noncomputable section

theorem exists_form_div_of_mem_chartRing {k : Type} [Field k] {N : ℕ} {Ω : Type} [Field Ω] [Algebra k Ω]
    {x : Fin (N + 1) → Ω} {i : Fin (N + 1)} (hi : x i ≠ 0) {a : Ω}
    (ha : a ∈ Kleiman.chartRing k x (Kleiman.singleChart hi)) :
    ∃ (e : ℕ) (f : Kleiman.Poly k N), f.IsHomogeneous e ∧ a = aeval x f / x i ^ e := by
  obtain ⟨f, t, e, ht, hf, hte, rfl⟩ := ha
  have ht' : t ∈ Submonoid.closure {(X i : Kleiman.Poly k N)} := by
    have : ((fun l => (X l : Kleiman.Poly k N)) '' ((({i} : Finset (Fin (N + 1))) : Set (Fin (N + 1))))) =
        {X i} := by simp
    rw [← this]; exact ht
  obtain ⟨p, rfl⟩ := Submonoid.mem_closure_singleton.mp ht'
  have hpe : e = p := hte.inj_right (isHomogeneous_X_pow i p) (by
    rw [X_pow_eq_monomial, Ne, monomial_eq_zero]; exact one_ne_zero)
  subst hpe
  exact ⟨e, f, hf, by rw [map_pow, aeval_X]⟩

theorem exists_common_form_div {k : Type} [Field k] {N : ℕ} {Ω : Type} [Field Ω] [Algebra k Ω]
    {x : Fin (N + 1) → Ω} {ι : Type} [Fintype ι] {i : Fin (N + 1)} (hi : x i ≠ 0) (a : ι → Ω)
    (ha : ∀ t, a t ∈ Kleiman.chartRing k x (Kleiman.singleChart hi)) :
    ∃ (D : ℕ) (E : ι → Kleiman.Poly k N), (∀ t, (E t).IsHomogeneous D) ∧
      ∀ t, a t = aeval x (E t) / x i ^ D := by
  classical
  choose e f hf hfa using fun t => exists_form_div_of_mem_chartRing hi (ha t)
  have hle : ∀ t, e t ≤ ∑ t, e t := fun t =>
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
  refine ⟨∑ t, e t, fun t => f t * X i ^ (∑ t, e t - e t), fun t => ?_, fun t => ?_⟩
  · have h := (hf t).mul (isHomogeneous_X_pow i (∑ t, e t - e t))
    rwa [Nat.add_sub_cancel' (hle t)] at h
  · have hD : x i ^ (∑ t, e t) = x i ^ e t * x i ^ (∑ t, e t - e t) := by
      rw [← pow_add, Nat.add_sub_cancel' (hle t)]
    rw [hfa t, map_mul, map_pow, aeval_X, hD, mul_div_mul_right _ _ (pow_ne_zero _ hi)]

theorem mConeMapOver_rename_base {k : Type} [Field k] {N : ℕ} {Ω : Type} [Field Ω] [Algebra k Ω]
    (x : Fin (N + 1) → Ω) {m : ℕ} (s : Fin m → Ω) {F : Kleiman.Poly k N} {D : ℕ} (hF : F.IsHomogeneous D) :
    mConeMapOver k (graphVec x s) (rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) F) =
      C (aeval x F) * X baseBlock ^ D := by
  have h := congrArg (fun φ => φ F) (mConeMapOver_graph_comp_base (S := k) x s)
  simp only [AlgHom.comp_apply] at h
  rw [h, Kleiman.cone_eq, Kleiman.coneGen_of_isHomogeneous x hF]
  simp only [AlgHom.restrictScalars_apply, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X,
    MvPolynomial.algebraMap_eq]

theorem mConeMapOver_X' {k : Type} [Field k] {N : ℕ} {Ω : Type} [Field Ω] [Algebra k Ω] {m : ℕ}
    (y : (Σ c, graphIdx N m c) → Ω) (v : Σ c, graphIdx N m c) :
    mConeMapOver k y (X v) = C (y v) * X v.1 := by
  simp [mConeMapOver]

theorem SectionRatio.full : SectionRatio.Statement := by
  intro k _ N Ω _ _ x Q n m s hx hgen W hW hle j b hYj
  have hmem : ∀ P, mConeMapOver k (graphVec x s) P = 0 → P ∈ W := fun P hP => hle (RingHom.mem_ker.mpr hP)
  obtain ⟨i, hXi⟩ : ∃ i : Fin (N + 1), (X ⟨baseBlock, i⟩ : NumbersDVR.MRing (graphIdx N m) k) ∉ W :=
    hW.relevant baseBlock
  have hi : x i ≠ 0 := fun h0 => hXi (hmem _ (by
    rw [mConeMapOver_X', show graphVec x s ⟨baseBlock, i⟩ = 0 from h0, map_zero, zero_mul]))
  obtain ⟨w, hw, hsum⟩ := exists_graph_inverse Q n s hgen hi
  have hw' : ∀ p : Fin m × Fin m,
      x i ^ (-n) * s p.1 * w p.2 ∈ Kleiman.chartRing k x (Kleiman.singleChart hi) := fun p => by
    rw [← chartRingOver_oneBlock x (fun _ => i) hi]; exact hw p.1 p.2
  obtain ⟨D, E, hE, hEq⟩ := exists_common_form_div hi _ hw'
  have hval : ∀ a c, aeval x (E (a, c)) = x i ^ D * (x i ^ (-n) * s a * w c) := fun a c => by
    have h := hEq (a, c)
    dsimp only at h
    rw [h]; field_simp
  obtain ⟨b0, hb0⟩ : ∃ b0, rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) (E (j, b0)) ∉ W := by
    by_contra h
    push Not at h
    have key : ∑ c, aeval x (E (j, c)) * s c = x i ^ D * s j := by
      simp only [hval]
      calc ∑ c, x i ^ D * (x i ^ (-n) * s j * w c) * s c
          = x i ^ D * s j * ∑ c, x i ^ (-n) * s c * w c := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c _ => by ring
        _ = x i ^ D * s j := by rw [hsum, mul_one]
    have hrel : ∑ c, rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) (E (j, c)) *
          X ⟨Sum.inr (), c⟩ -
        rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) (X i ^ D) *
          X ⟨Sum.inr (), j⟩ ∈ W := by
      apply hmem

      rw [map_sub, map_sum, map_mul, mConeMapOver_rename_base x s (isHomogeneous_X_pow i D), mConeMapOver_X']
      have hc : ∀ c, mConeMapOver k (graphVec x s)
          (rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) (E (j, c)) *
            X ⟨Sum.inr (), c⟩) = C (aeval x (E (j, c)) * s c) * (X baseBlock ^ D * X (Sum.inr ())) := fun c => by
        rw [map_mul, mConeMapOver_rename_base x s (hE _), mConeMapOver_X', graphVec_inr, map_mul]
        ring

      rw [Finset.sum_congr rfl fun c _ => hc c, ← Finset.sum_mul, ← map_sum, key, graphVec_inr]
      simp only [map_pow, aeval_X, map_mul]
      ring
    have hsumW : ∑ c, rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) (E (j, c)) *
        X ⟨Sum.inr (), c⟩ ∈ W := W.sum_mem fun c _ => W.mul_mem_right _ (h c)
    have hXY := W.sub_mem hsumW hrel
    rw [sub_sub_cancel, map_pow, rename_X] at hXY
    rcases hW.isPrime.mem_or_mem hXY with h1 | h1
    · exact hXi (hW.isPrime.mem_of_pow_mem _ h1)
    · exact hYj h1
  refine ⟨D, E (b, b0), E (j, b0), hE _, hE _, hb0, hmem _ ?_⟩
  rw [map_sub, map_mul, map_mul, mConeMapOver_rename_base x s (hE _), mConeMapOver_rename_base x s (hE _),
    mConeMapOver_X', mConeMapOver_X', graphVec_inr, graphVec_inr, hval, hval]
  dsimp only
  simp only [map_mul]
  ring

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open scoped Pointwise
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver)

section Charts

variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem PowRealises.twist_sub (G Q : Kleiman.SubSystem F x Ω) (I : Kleiman.Chart x) :
    (G.twist Q).sub I = Q.sub I * G.sub I := by
  rw [Submodule.mul_eq_span_mul_set]
  show Submodule.span _ _ = _
  congr 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_mul, SetLike.mem_coe, smul_eq_mul]
  constructor
  · rintro ⟨q, hq, g, hg, rfl⟩; exact ⟨q, hq, g, hg, rfl⟩
  · rintro ⟨q, hq, g, hg, rfl⟩; exact ⟨q, hq, g, hg, rfl⟩

theorem PowRealises.twistSys_sub (c : ℤ) (I : Kleiman.Chart x) :
    (Kleiman.twistSys F x c).sub I = Kleiman.twistMod F x c I := rfl

theorem PowRealises.twistMod_mul (a b : ℤ) (I : Kleiman.Chart x) :
    Kleiman.twistMod F x a I * Kleiman.twistMod F x b I = Kleiman.twistMod F x (a + b) I := by
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (Kleiman.mem_support x).mp (I.2.2 hi)
  rw [Kleiman.twistMod_eq_span a I hi, Kleiman.twistMod_eq_span b I hi, Kleiman.twistMod_eq_span (a + b) I hi,
    Submodule.span_mul_span, Set.singleton_mul_singleton, ← zpow_add₀ hxi]

theorem PowRealises.twistMod_zero (I : Kleiman.Chart x) : Kleiman.twistMod F x 0 I = 1 := by
  obtain ⟨i, hi⟩ := I.2.1
  rw [Kleiman.twistMod_eq_span 0 I hi, zpow_zero, Submodule.one_eq_span]

theorem PowRealises.twistMod_nat_mul (c : ℤ) (I : Kleiman.Chart x) :
    ∀ p : ℕ, Kleiman.twistMod F x ((p : ℤ) * c) I = Kleiman.twistMod F x c I ^ p
  | 0 => by rw [Nat.cast_zero, zero_mul, pow_zero]; exact PowRealises.twistMod_zero I
  | p + 1 => by
    rw [pow_succ', ← PowRealises.twistMod_nat_mul c I p, PowRealises.twistMod_mul]
    congr 1
    push_cast
    ring

theorem PowRealises.pow_sub (Q : Kleiman.SubSystem F x Ω) (I : Kleiman.Chart x) :
    ∀ p : ℕ, (Q.pow p).sub I = Q.sub I ^ p
  | 0 => by rw [pow_zero]; exact PowRealises.twistMod_zero I
  | p + 1 => by
    show ((Q.pow p).twist Q).sub I = _
    rw [PowRealises.twist_sub, PowRealises.pow_sub Q I p, pow_succ']

end Charts

section Model

variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω]

theorem PowRealises.mem_span_inv_iff (A : Subalgebra F Ω) {u z : Ω} (hu : u ≠ 0) :
    z ∈ Submodule.span A {u⁻¹} ↔ z * u ∈ A := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    rw [Subalgebra.smul_def, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hu, mul_one]
    exact a.2
  · intro h
    refine ⟨⟨z * u, h⟩, ?_⟩
    rw [Subalgebra.smul_def, smul_eq_mul]
    exact mul_inv_cancel_right₀ hu z

variable {K : Type} [Fintype K] {ι : K → Type}

theorem PowRealises.mem_secOver (y : (Σ k, ι k) → Ω) (n : K → ℤ) (s : Ω) :
    s ∈ secOver F y n ↔ ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
      s * ∏ k, y ⟨k, c k⟩ ^ (-n k) ∈ chartRingOver F y c := by
  simp only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply,
    Subalgebra.mem_toSubmodule]

theorem PowRealises.span_secOver_eq (y : (Σ k, ι k) → Ω) (n : K → ℤ) (hg : IndefiniteRowSideFullHecke.Kleiman2.IsGenerated F y n)
    (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    Submodule.span (chartRingOver F y c) (secOver F y n : Set Ω) =
      Submodule.span (chartRingOver F y c) {(∏ k, y ⟨k, c k⟩ ^ (-n k))⁻¹} := by
  have hu : (∏ k, y ⟨k, c k⟩ ^ (-n k)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
  apply le_antisymm
  · rw [Submodule.span_le]
    intro t ht
    exact (PowRealises.mem_span_inv_iff _ hu).mpr ((PowRealises.mem_secOver y n t).mp ht c hc)
  · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
    obtain ⟨m, s, hs, hgen⟩ := hg
    obtain ⟨u, hu', hsum⟩ := hgen c hc
    have key : (∏ k, y ⟨k, c k⟩ ^ (-n k))⁻¹ =
        ∑ j, (⟨u j, hu' j⟩ : chartRingOver F y c) • s j := by
      rw [← one_mul (_⁻¹), ← hsum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Subalgebra.smul_def, smul_eq_mul, mul_assoc, mul_inv_cancel_right₀ hu]
    rw [key]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span (hs j))

theorem PowRealises.prod_exp [DecidableEq K] (y : (Σ k, ι k) → Ω) (k₀ : K) (β : K → ℤ) (p : ℕ) (c d : ℤ)
    (cc : ∀ k, ι k) (hc : ∀ k, y ⟨k, cc k⟩ ≠ 0) :
    y ⟨k₀, cc k₀⟩ ^ (-d) * (∏ k, y ⟨k, cc k⟩ ^ (-(β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k)) ^ p =
      ∏ k, y ⟨k, cc k⟩ ^ (-(p • β + ((p : ℤ) * c + d) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k) := by
  have h0 : y ⟨k₀, cc k₀⟩ ^ (-d) = ∏ k, y ⟨k, cc k⟩ ^ (-(d • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k) := by
    rw [Finset.prod_eq_single k₀]
    · simp [IndefiniteRowSideFullHecke.Kleiman2.baseDeg]
    · intro k _ hk
      simp [IndefiniteRowSideFullHecke.Kleiman2.baseDeg, hk]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [h0, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_natCast, ← zpow_mul, ← zpow_add₀ (hc k)]
  congr 1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]
  ring

end Model

theorem PowRealises.proof (hG : ModelGenerated.Statement) (hS : SpanSecs.Statement) : PowRealises.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e x hx hmod Q β hQ p ct
  obtain ⟨c₀, hc₀⟩ := Kleiman.Generated.full F Ω N x Q
  obtain ⟨c₁, hc₁⟩ := hG F K ι Ω y k₀ hmod β
  obtain ⟨c, hc0, hc1⟩ : ∃ c, c₀ ≤ c ∧ c₁ ≤ c := ⟨max c₀ c₁, le_max_left _ _, le_max_right _ _⟩
  have hgenQ := hc₀ c hc0
  have hgenY := hc₁ c hc1
  obtain ⟨d, rfl⟩ : ∃ d, ct = (p : ℤ) * c + d := ⟨ct - (p : ℤ) * c, by ring⟩
  have hchart : ∀ I : Kleiman.Chart x, (Kleiman.twistMul Q.toSubSystem p ((p : ℤ) * c + d)).sub I =
      Submodule.span (Kleiman.chartRing F x I)
          ((secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) : Set Ω) ^ p) * Kleiman.twistMod F x d I := by
    intro I
    have h1 : (Q.toSubSystem.twist (Kleiman.twistSys F x c)).sub I =
        Submodule.span (Kleiman.chartRing F x I) (secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) : Set Ω) := by
      rw [← hgenQ I, hQ c]
    rw [PowRealises.twist_sub, PowRealises.twistSys_sub] at h1
    show ((Q.toSubSystem.pow p).twist (Kleiman.twistSys F x ((p : ℤ) * c + d))).sub I = _
    rw [PowRealises.twist_sub, PowRealises.twistSys_sub, PowRealises.pow_sub, ← PowRealises.twistMod_mul,
      PowRealises.twistMod_nat_mul, ← Submodule.span_pow, ← h1, mul_pow]
    ring
  have hsecs : (Kleiman.twistMul Q.toSubSystem p ((p : ℤ) * c + d)).secs = ⨅ I : Kleiman.Chart x,
      (Submodule.span (Kleiman.chartRing F x I)
          ((secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) : Set Ω) ^ p) *
        Kleiman.twistMod F x d I).restrictScalars F := by
    simp only [Kleiman.SubSystem.secs, hchart]
  ext s
  rw [hsecs, hS F K ι Ω y k₀ N e x hx hmod _ d s, PowRealises.mem_secOver]
  refine forall_congr' fun cc => forall_congr' fun hc => ?_
  have hu : (∏ k, y ⟨k, cc k⟩ ^ (-(β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
  rw [← Submodule.span_pow, PowRealises.span_secOver_eq y _ hgenY cc hc, Submodule.span_pow, Set.singleton_pow,
    inv_pow, PowRealises.mem_span_inv_iff _ (pow_ne_zero _ hu), mul_assoc, PowRealises.prod_exp y k₀ β p c d cc hc]

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial Filter
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver mIdealOver)

noncomputable section

section Poly

variable {K : Type}

theorem eval_bind₁_shift (p : MvPolynomial K ℚ) (a z : K → ℚ) :
    eval z (bind₁ (fun k => X k - C (a k)) p) = eval (z - a) p := by
  show eval₂Hom (RingHom.id ℚ) z _ = _
  rw [eval₂Hom_bind₁]
  have hfun : (fun i => eval₂Hom (RingHom.id ℚ) z (X i - C (a i))) = z - a := funext fun k => by simp
  rw [hfun]
  rfl

theorem altSum_eq_of_eventually (p : MvPolynomial K ℚ) {n : ℕ} (δ : Fin n → K → ℤ) (D : ℚ)
    (h : ∀ᶠ m : K → ℤ in atTop,
      ∑ T : Finset (Fin n), (-1 : ℚ) ^ T.card * eval (fun k => (((m - ∑ i ∈ T, δ i) k : ℤ) : ℚ)) p = D)
    (z : K → ℤ) :
    ∑ T : Finset (Fin n), (-1 : ℚ) ^ T.card * eval (fun k => (((z - ∑ i ∈ T, δ i) k : ℤ) : ℚ)) p = D := by
  classical
  let q : MvPolynomial K ℚ := ∑ T : Finset (Fin n),
    C ((-1 : ℚ) ^ T.card) * bind₁ (fun k => X k - C (((∑ i ∈ T, δ i) k : ℤ) : ℚ)) p
  have hq : ∀ w : K → ℤ, eval (fun k => (w k : ℚ)) q =
      ∑ T : Finset (Fin n), (-1 : ℚ) ^ T.card * eval (fun k => (((w - ∑ i ∈ T, δ i) k : ℤ) : ℚ)) p := by
    intro w

    simp only [q, map_sum, map_mul, eval_C, eval_bind₁_shift]
    refine Finset.sum_congr rfl fun T _ => ?_
    congr 3
    funext k
    simp only [Pi.sub_apply, Int.cast_sub]
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.mp h
  let s : K → Set ℚ := fun k => (fun t : ℤ => (t : ℚ)) '' Set.Ici (m₀ k)
  have hs : ∀ k, (s k).Infinite := fun k =>
    (Set.Ici_infinite (m₀ k)).image (fun a _ b _ hab => Int.cast_injective hab)
  have hqD : q = C D := by
    refine funext_set s hs fun w hw => ?_
    have hw' : ∀ k, ∃ t : ℤ, m₀ k ≤ t ∧ (t : ℚ) = w k := fun k => hw k (Set.mem_univ k)
    choose m hm1 hm2 using hw'
    have hwm : w = fun k => (m k : ℚ) := funext fun k => (hm2 k).symm
    rw [hwm, hq, eval_C]
    exact hm₀ m hm1
  rw [← hq, hqD, eval_C]

end Poly

theorem NumModel.proof (hT : TensorRealise.Statement) (hS : SectionsPoly.Statement) (hD : ModelDim.Statement) :
    NumModel.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e x hx hmod n L δ hL hsub
  classical
  obtain ⟨i₀, hi₀⟩ := hmod.1 k₀
  have hj : x (e i₀) ≠ 0 := by
    rw [hx]
    simpa [IndefiniteRowSideFullHecke.Kleiman2.blockVec] using hi₀
  have hP := isMultiProjPrime_mIdealOver (S := F) y hmod.1
  have hdim := (hD F K ι Ω y k₀ N e x hx hmod n).mp hsub
  obtain ⟨p, hpH, hpS⟩ := hS F K ι Ω y k₀ hmod
  have hMD := (FieldNumbers.MixedDiffConst.full F K ι (mIdealOver F y) hP.multiHomog hP.relevant n hdim).1 δ
  set D := NumbersDVR.intNum F (mIdealOver F y) δ with hD_def

  have hev : ∀ᶠ m : K → ℤ in atTop, ∑ T : Finset (Fin n),
      (-1 : ℚ) ^ T.card * eval (fun k => (((m - ∑ i ∈ T, δ i) k : ℤ) : ℚ)) p = D := by
    have h2 : ∀ T : Finset (Fin n), ∀ᶠ m : K → ℤ in atTop,
        (NumbersDVR.hilbFn (mIdealOver F y) (m - ∑ i ∈ T, δ i) : ℚ) =
          eval (fun k => (((m - ∑ i ∈ T, δ i) k : ℤ) : ℚ)) p := fun T =>
      ((tendsto_atTop_add_const_right atTop (-(∑ i ∈ T, δ i)) tendsto_id).eventually hpH).mono
        fun m hm => by simpa only [id, sub_eq_add_neg] using hm
    filter_upwards [hMD, eventually_all.mpr h2] with m h1 h2
    rw [mixedDiff_eq_sum] at h1
    have h1' := congrArg (Int.cast : ℤ → ℚ) h1
    push_cast at h1'
    rw [← h1']
    exact Finset.sum_congr rfl fun T _ => by rw [h2 T]
  have hall := altSum_eq_of_eventually p δ (D : ℚ) hev

  have hsecs : ∀ T : Finset (Fin n), ∀ᶠ c : ℕ in atTop,
      ((restrLen (primeOf (S := F) x)
          ((tensorSub (fun i => (L i).toSubSystem) T).twist (twistSys F x (c : ℤ))) : ℤ) : ℚ) =
        eval (fun k => (((∑ i ∈ T, δ i + (c : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k : ℤ) : ℚ)) p := fun T => by
    filter_upwards [hT F K ι Ω y k₀ N e x hx hmod n L δ hL T, hpS (∑ i ∈ T, δ i)] with c h1 h2
    rw [restrLen_primeOf_eq_finrank x hj, h1, ← h2]
    simp
  have hfin : ∀ᶠ c : ℕ in atTop, interSum (primeOf (S := F) x) (fun i => (L i).toSubSystem) c = D := by
    filter_upwards [eventually_all.mpr hsecs] with c hc
    apply Int.cast_injective (α := ℚ)
    rw [interSum, ← hall (∑ i, δ i + (c : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)]
    push_cast
    refine Fintype.sum_bijective compl compl_involutive.bijective _ _ fun T => ?_
    have hcard : Tᶜ.card = n - T.card := by rw [Finset.card_compl, Fintype.card_fin]
    have hvec : (∑ i, δ i + (c : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) - ∑ i ∈ Tᶜ, δ i =
        ∑ i ∈ T, δ i + (c : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀ := by
      rw [← Finset.sum_add_sum_compl T δ]
      abel
    rw [hc T, hcard, hvec]
  unfold interNum
  exact (tendsto_const_nhds.congr' (hfin.mono fun c h => h.symm)).limUnder_eq

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end
