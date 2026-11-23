module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.Bundle006
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.ConjugatePreservesWeightFiltration
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.Bundle008
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle075
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Integer

@[expose] public section

section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia.Abs

theorem UpperTheory.smoothPt_weightedGradedAlgebra_basePoint :
    ∀ (O : Type) [CommRing O] [IsDomain O] (σ : Type) [Fintype σ] (wt : σ → ℤ),
        SmoothPt (Fgr O wt) (x0 O wt) (fun j => Nat.card {i // wt i = j}) := by
  intro O _ _ σ hσ wt
  classical
  have hinj : Function.Injective (algebraMap O (FractionRing O)) := IsFractionRing.injective O _
  let φ : FA O wt →ₐ[O] MvPowerSeries σ (FractionRing O) :=
    (MvPowerSeries.mapAlgHom (Algebra.ofId O (FractionRing O))).comp (WPres.free O wt).A.val
  have hφ : ∀ (f : FA O wt) (d : σ →₀ ℕ),
      coeff d (φ f) = algebraMap O (FractionRing O) (coeff d (ser f)) := fun f d => rfl
  refine ⟨σ, hσ, wt, φ, ⟨?_, ?_, ?_, ?_⟩, fun j => rfl⟩
  · intro j f hf d hd
    rw [hφ, mem_Fgr.1 hf d hd, map_zero]
  · intro f
    rw [weightedSeriesOrigin_apply]
    exact hφ f 0
  · intro i
    have hz : ser ((WPres.free O wt).zA i) = MvPowerSeries.X i := rfl
    refine ⟨(WPres.free O wt).zA i, ?_, fun i' hi => ?_⟩
    · rw [hφ, hz, coeff_index_single_self_X, map_one]
      exact one_ne_zero
    · rw [hφ, hz, coeff_index_single_X, if_neg hi, map_zero]
  · intro f h0 h1
    refine (UpperTheory.mem_satSq_iff_constantCoeff_and_linearCoeff_eq_zero O σ wt f).2 ⟨by rw [← weightedSeriesOrigin_apply, h0], fun i => hinj ?_⟩
    rw [← hφ, h1, map_zero]
end

section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia.Abs

private theorem span_of_ann {O : Type} [CommRing O] [IsDomain O] {σ : Type} [Fintype σ] (p : σ → Prop)
    {κ : Type} [Fintype κ] (v : κ → σ → O) (hv : ∀ k i, ¬ p i → v k i = 0)
    (h : ∀ d : σ → O, (∀ i, ¬ p i → d i = 0) → (∀ k, ∑ i, v k i * d i = 0) → d = 0)
    (w : σ → O) (hw : ∀ i, ¬ p i → w i = 0) :
    ∃ c : O, c ≠ 0 ∧ ∃ a : κ → O, ∀ i, c * w i = ∑ k, a k * v k i := by
  classical
  let ι : O →+* FractionRing O := algebraMap O (FractionRing O)
  have hinj : Function.Injective ι := IsFractionRing.injective O (FractionRing O)
  let V : Submodule (FractionRing O) (σ → FractionRing O) :=
    Submodule.span (FractionRing O) (Set.range fun k => fun i => ι (v k i))
  have hmem : (fun i => ι (w i)) ∈ V := by
    by_contra hw'
    obtain ⟨f, hfw, hfV⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hw' inferInstance
    let e : σ → FractionRing O := fun i => if p i then f (fun j => if i = j then 1 else 0) else 0
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O) Finset.univ e
    choose d hd using fun i => hb i (Finset.mem_univ i)
    have hd0 : d = 0 := by
      apply h d
      · intro i hi
        apply hinj
        rw [hd i, map_zero]
        simp [e, hi]
      · intro k
        apply hinj
        have hvk : f (fun i => ι (v k i)) = 0 := by
          have h1 : (fun i => ι (v k i)) ∈ V := Submodule.subset_span ⟨k, rfl⟩
          have h2 := Submodule.mem_map_of_mem (f := f) h1
          rw [hfV] at h2
          exact (Submodule.mem_bot _).mp h2
        rw [LinearMap.pi_apply_eq_sum_univ] at hvk

        rw [map_zero, map_sum]
        calc ∑ i, ι (v k i * d i) = ∑ i, (b : O) • (ι (v k i) * e i) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [map_mul, hd i, mul_smul_comm]
          _ = (b : O) • ∑ i, ι (v k i) • f (fun j => if i = j then 1 else 0) := by
              rw [← Finset.smul_sum]
              congr 1
              refine Finset.sum_congr rfl fun i _ => ?_
              by_cases hi : p i
              · simp [e, hi, smul_eq_mul]
              · simp [e, hi, hv k i hi]
          _ = 0 := by rw [hvk, smul_zero]
    have he : ∀ i, e i = 0 := by
      intro i
      have h1 : (b : O) • e i = 0 := by
        rw [← hd i, hd0]
        simp
      rw [Algebra.smul_def] at h1
      rcases mul_eq_zero.mp h1 with h2 | h2
      · exfalso
        exact nonZeroDivisors.coe_ne_zero b (hinj (by rw [map_zero]; exact h2))
      · exact h2
    apply hfw
    rw [LinearMap.pi_apply_eq_sum_univ]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : p i
    · have h3 := he i
      simp only [e, hi, if_true] at h3
      rw [h3, smul_zero]
    · rw [hw i hi, map_zero, zero_smul]
  rw [Submodule.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨c, hc⟩ := hmem
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O) Finset.univ c
  choose a ha using fun k => hb k (Finset.mem_univ k)
  refine ⟨b, nonZeroDivisors.coe_ne_zero b, a, fun i => hinj ?_⟩
  have hi := congrFun hc i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hi

  rw [map_mul, map_sum, ← hi, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, ha k, Algebra.smul_def]
  ring

private theorem weight_single_one {σ : Type} (wt : σ → ℤ) (i : σ) :
    Finsupp.weight wt (Finsupp.single i 1) = wt i := by
  rw [Finsupp.weight_apply, Finsupp.sum_single_index] <;> simp

theorem UpperTheory.spansCot_of_linear_terms_nondegenerate :
    ∀ (O : Type) [CommRing O] [IsDomain O] (σ : Type) [Fintype σ] (wt : σ → ℤ) (j : ℤ) (κ : Type) [Finite κ] (F : κ → FA O wt),
        (∀ k, F k ∈ Fgr O wt j) → (∀ k, x0 O wt (F k) = 0) →
        (∀ d : σ → O, (∀ i, wt i ≠ j → d i = 0) → (∀ k, ∑ i, coeff (Finsupp.single i 1) (ser (F k)) * d i = 0) → d = 0) →
        SpansCot (x0 O wt) (Fgr O wt) j F := by
  intro O _ _ σ _ wt j κ _ F hF hx hd
  classical
  haveI := Fintype.ofFinite κ
  have hco : ∀ f ∈ Fgr O wt j, ∀ i, ¬ (wt i = j) → coeff (Finsupp.single i 1) (ser f) = 0 := by
    intro f hf i hi
    rw [mem_Fgr] at hf
    exact hf (Finsupp.single i 1) (by rw [weight_single_one]; exact hi)
  unfold SpansCot
  intro q hq
  unfold cotLat at hq
  obtain ⟨g, ⟨hgj, hg0⟩, rfl⟩ := Submodule.mem_map.mp hq
  have hg0' : x0 O wt g = 0 := hg0
  obtain ⟨c, hc, a, ha⟩ := span_of_ann (fun i => wt i = j)
    (fun k i => coeff (Finsupp.single i 1) (ser (F k))) (fun k i hi => hco _ (hF k) i hi) hd
    (fun i => coeff (Finsupp.single i 1) (ser g)) (fun i hi => hco _ hgj i hi)
  refine ⟨c, hc, ?_⟩
  have hsat : c • g - ∑ k, a k • F k ∈ satSq (x0 O wt) := by
    rw [mem_satSq_iff_constantCoeff_and_linearCoeff_eq_zero]
    constructor
    · rw [← weightedSeriesOrigin_apply]

      simp [map_sub, map_sum, map_smul, hg0', hx]
    · intro i
      have hser : ser (c • g - ∑ k, a k • F k) = c • ser g - ∑ k, a k • ser (F k) := by
        simp [ser]

      rw [hser, map_sub, map_sum]
      simp only [map_smul, smul_eq_mul]
      exact sub_eq_zero.mpr (ha i)
  have heq : (satSq (x0 O wt)).mkQ (c • g) = (satSq (x0 O wt)).mkQ (∑ k, a k • F k) := by
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    exact hsat
  unfold cotSpan

  rw [← map_smul, heq, map_sum]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
end

section

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem coeff_single_mul {O σ : Type} [CommRing O] (f g : MvPowerSeries σ O) (i : σ) :
    MvPowerSeries.coeff (Finsupp.single i 1) (f * g) =
      MvPowerSeries.constantCoeff f * MvPowerSeries.coeff (Finsupp.single i 1) g +
        MvPowerSeries.coeff (Finsupp.single i 1) f * MvPowerSeries.constantCoeff g := by
  classical
  rw [MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single, Finset.sum_map, Finset.Nat.antidiagonal_succ]
  simp

private noncomputable def tan0 {O σ : Type} [CommRing O] [Fintype σ] (d : σ → O) :
    MvPowerSeries σ O →ₐ[O] DualNumber O where
  toFun f := TrivSqZeroExt.inl (MvPowerSeries.constantCoeff f) +
    TrivSqZeroExt.inr (∑ i, MvPowerSeries.coeff (Finsupp.single i 1) f * d i)
  map_one' := by
    classical
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp [MvPowerSeries.coeff_one]
  map_mul' f g := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp only [DualNumber.snd_mul, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl,
        TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, add_zero, coeff_single_mul,
        Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
  map_zero' := by
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp
  map_add' f g := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp [add_mul, Finset.sum_add_distrib]
  commutes' a := by
    classical
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [MvPowerSeries.algebraMap_apply, TrivSqZeroExt.algebraMap_eq_inl]
    · simp [MvPowerSeries.algebraMap_apply, TrivSqZeroExt.algebraMap_eq_inl, MvPowerSeries.coeff_C]

private theorem tangent_point_fst {O σ : Type} [CommRing O] [Fintype σ] (d : σ → O) (f : MvPowerSeries σ O) :
    (tan0 d f).fst = MvPowerSeries.constantCoeff f := by
  simp [tan0]

private theorem tangent_point_snd {O σ : Type} [CommRing O] [Fintype σ] (d : σ → O) (f : MvPowerSeries σ O) :
    (tan0 d f).snd = ∑ i, MvPowerSeries.coeff (Finsupp.single i 1) f * d i := by
  simp [tan0]

private theorem dual_local {O : Type} [CommRing O] [IsLocalRing O] : IsLocalRing (DualNumber O) := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.isUnit_iff_isUnit_fst]
  simpa using IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst

private theorem exists_tan {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (W : WPres O ℤ R)
    (h0 : W.HasOrigin) (d : W.σ → O)
    (hd : ∀ f, W.π f = 0 → ∑ i, MvPowerSeries.coeff (Finsupp.single i 1) f * d i = 0) :
    ∃ τ : R →ₐ[O] DualNumber O, ∀ f, τ (W.π f) = tan0 d f := by
  refine ⟨(Ideal.Quotient.liftₐ (RingHom.ker W.π) (tan0 d) fun f hf => ?_).comp
    (Ideal.quotientKerAlgEquivOfSurjective W.surj).symm.toAlgHom, fun f => ?_⟩
  · exact TrivSqZeroExt.ext ((tangent_point_fst d f).trans (h0 f hf)) ((tangent_point_snd d f).trans (hd f hf))
  · have : (Ideal.quotientKerAlgEquivOfSurjective W.surj).symm (W.π f) = Ideal.Quotient.mk _ f := by
      rw [AlgEquiv.symm_apply_eq]; rfl
    simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom]
    erw [this]
    rfl

theorem UpperTheory.V.UnitaryThreeInertia.tangent_coord_eq_zero_of_nonpos_weight :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    F.VanE → ∀ (g₁ : Γ), F.Marked g₁ → ∀ {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (u : Γ →* GG (m := 3) (R := R)), F.IsUniv g₁ u →
    ∀ (W : WPres O ℤ R), F.Adapted u W → ∀ j : ℤ, j ≤ 0 → ∀ d : W.σ → O, (∀ i, W.wt i ≠ j → d i = 0) →
      (∀ f, W.π f = 0 → ∑ i, MvPowerSeries.coeff (Finsupp.single i 1) f * d i = 0) → d = 0 := by
  intro O _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hF hV g₁ hg R _ _ _ u hu W hW j hj d hdw hd
  classical
  obtain ⟨h0, hor⟩ := hasOrigin F hF g₁ hg u hu W hW
  obtain ⟨τ, hτ⟩ := exists_tan W h0 d hd
  haveI : IsLocalRing (DualNumber O) := dual_local
  have hfst : ∀ x, (τ x).fst = W.origin h0 x := fun x => by
    obtain ⟨f, rfl⟩ := W.surj x
    rw [hτ, tangent_point_fst, WPres.origin_π]
  haveI : IsLocalHom τ := ⟨fun x hx => by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, hfst] at hx
    by_contra hn
    have h1 : res O O (W.origin h0 x) = 0 := by
      rw [res_map, res_eq_zero_iff]; exact hn
    exact (res_eq_zero_iff O O _).1 h1 hx⟩
  have hr : push τ u = F.rz (DualNumber O) := by
    refine eq_rz_of_vanE F hF hV g₁ hg j hj _ (isPt_push F τ g₁ u hu.pt) (fun g a b => ?_) (fun g a b _ hab => ?_)
    · rw [← hor]
      exact hfst _
    · have hm : (u g).mat a b ∈ W.part (wt a b) := by
        rw [hW.part]; exact entry_mem u g a b
      obtain ⟨f, hf, e⟩ := hm
      have e' : W.π f = (u g).mat a b := e
      show (τ ((u g).mat a b)).snd = 0
      rw [← e', hτ, tangent_point_snd]
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases hi : W.wt i = j
      · rw [hf _ (by rw [Finsupp.weight_single, one_smul, hi]; exact hab.symm), zero_mul]
      · rw [hdw i hi, mul_zero]
  funext i
  obtain ⟨g, a, b, -, -, hz⟩ := hW.var i
  have h1 : τ (W.z i) = 0 := by
    have h2 : τ ((u g).mat a b) = (F.rz (DualNumber O) g).mat a b := by rw [← hr]; rfl
    rw [hz, map_sub, h2, sub_eq_zero]
    exact (τ.commutes _).symm
  have h3 : (τ (W.z i)).snd = d i := by
    rw [WPres.z, hτ, tangent_point_snd, Finset.sum_eq_single i]
    · simp [MvPowerSeries.coeff_X]
    · intro k _ hk
      rw [MvPowerSeries.coeff_X, if_neg, zero_mul]
      intro e
      exact hk (Finsupp.single_left_injective one_ne_zero e)
    · simp
  rw [← h3, h1]
  rfl
end

section

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem unit_of_res {R : Type} [CommRing R] [IsLocalRing R] {x : R} (h : IsUnit (residue R x)) :
    IsUnit x :=
  (residue_ne_zero_iff_isUnit x).1 h.ne_zero

theorem UpperTheory.V.UnitaryThreeInertia.exists_canon :
    ∀ {R : Type} [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] (X : Matrix (Fin 3) (Fin 3) R), (∀ a b, a ≠ b → IsUnit (X a a - X b b)) → (∀ a b, a ≠ b → X a b ∈ maximalIdeal R) → ∃ h, Canon X h :=
  _root_.UpperTheory.Reformulated.B.Qf19.exists_canon
end
