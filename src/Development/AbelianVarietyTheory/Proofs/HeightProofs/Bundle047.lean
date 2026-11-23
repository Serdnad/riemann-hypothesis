module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryGroupSecondKindCoordinatesNearOne
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Formalism.LocalToGlobal.ProjectiveLattices.CurveLoc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle007
public import Development.AbelianVarietyTheory.Proofs.AlgebraicCurves.ExistsMulEqMapOfIsAlgebraic
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

noncomputable section

open Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped Topology

namespace GlobalTheory.TypeSum.DerFamCont

theorem exists_chart {E : Type} [NormedRing E] [NormedAlgebra ℝ E] [FiniteDimensional ℝ E] (σ : E →ₗ[ℝ] E)
    (hσ : ∀ a, σ (σ a) = a) (hm : ∀ a b, σ (a * b) = σ b * σ a) (h1 : σ 1 = 1) :
    ∃ (N : ℕ) (Y : Fin N → E) (Ψ : E → Fin N → ℝ), (∀ i, σ (Y i) = -Y i) ∧ Tendsto Ψ (𝓝 1) (𝓝 0) ∧
      ∀ᶠ a in 𝓝 (1 : E), σ a * a = 1 → (List.ofFn fun i => NormedSpace.exp (Ψ a i • Y i)).prod = a := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : NormedAlgebra ℚ E := NormedAlgebra.restrictScalars ℚ ℝ E
  let S : Submodule ℝ E := LinearMap.ker (σ + LinearMap.id)
  have hS : ∀ X, X ∈ S ↔ σ X = -X := fun X => by simp [S, add_eq_zero_iff_eq_neg]
  let b := Module.finBasis ℝ S
  let e : Fin (Module.finrank ℝ S) → E := fun i => b i
  have hli : LinearIndependent ℝ e := b.linearIndependent.map' S.subtype S.ker_subtype
  have he : ∀ i, σ (e i) = -e i := fun i => (hS _).1 (b i).2
  have hsp : ∀ X, σ X = -X → X ∈ Submodule.span ℝ (Set.range e) := fun X hX => by
    have h := congrArg S.subtype (b.sum_repr ⟨X, (hS X).2 hX⟩)

    rw [map_sum] at h
    simp only [map_smul, Submodule.subtype_apply] at h
    rw [← h]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hexp : ∀ a, σ (NormedSpace.exp a) = NormedSpace.exp (σ a) := fun a => by
    have hp : ∀ n : ℕ, σ (a ^ n) = σ a ^ n := fun n => by
      induction n with
      | zero => simpa using h1
      | succ n ih => rw [pow_succ, hm, ih, pow_succ']
    have h2 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) a).map σ.toAddMonoidHom σ.continuous_of_finiteDimensional
    refine h2.unique ?_
    convert NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (σ a) using 1
    funext n
    simp [hp]
  set Θ : (Fin _ → ℝ) → E := fun t => (List.ofFn fun i => NormedSpace.exp (t i • e i)).prod with hΘ
  have hU : ∀ t, σ (Θ t) * Θ t = 1 ∧ Θ t * σ (Θ t) = 1 := fun t =>
    GlobalTheory.UnitaryChart.unitary_list_prod σ hm h1 _ (fun u hu => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hu
      rw [hexp, map_smul, he, smul_neg, ← NormedSpace.exp_add_of_commute (Commute.refl _).neg_left,
        ← NormedSpace.exp_add_of_commute (Commute.refl _).neg_right]
      simp)
  let T : (Fin _ → ℝ) →L[ℝ] E :=
    ∑ i, (ContinuousLinearMap.toSpanSingleton ℝ (e i)).comp (ContinuousLinearMap.proj i)
  have hT : ∀ t, T t = ∑ i, t i • e i := fun t => by simp [T]
  obtain ⟨h0, hD⟩ : Θ 0 = 1 ∧ HasStrictFDerivAt Θ T 0 :=
    GlobalTheory.UnitaryChart.hasStrictFDerivAt_ofFn_prod _ (fun i (t : Fin _ → ℝ) => NormedSpace.exp (t i • e i)) _ (fun i =>
      ⟨by simp, HasStrictFDerivAt.comp (0 : Fin _ → ℝ) (g := fun s : ℝ => NormedSpace.exp (s • e i))
        (by simpa using (hasStrictDerivAt_exp_smul_const (𝕂 := ℝ) (e i) 0).hasStrictFDerivAt)
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin _ => ℝ) i).hasStrictFDerivAt⟩)
  obtain ⟨P, hP1, hP2, hP3⟩ := GlobalTheory.UnitaryChart.exists_skew_coord σ e hσ hli he hsp
  have hΦ : HasStrictFDerivAt (fun t => P (Θ t))
      ((ContinuousLinearEquiv.refl ℝ (Fin (Module.finrank ℝ S) → ℝ) :
        (Fin (Module.finrank ℝ S) → ℝ) →L[ℝ] (Fin (Module.finrank ℝ S) → ℝ))) 0 := by
    refine (P.hasStrictFDerivAt.comp 0 hD).congr_fderiv ?_
    ext1 t
    simp [hT, hP1]
  have hP0 : P 1 = 0 := hP2 _ h1
  have hΦ0 : P (Θ 0) = 0 := by rw [h0, hP0]
  have p1 := hΦ.localInverse_tendsto
  have p3 := hΦ.eventually_right_inverse
  simp only [hΦ0] at p1 p3
  set Ψ := hΦ.localInverse _ _ _
  have hσc : Continuous σ := σ.continuous_of_finiteDimensional
  have hnear : ∀ᶠ m in 𝓝 (1 : E), ‖1 - σ m‖ ≤ 1 / 2 := by
    have : ContinuousAt (fun m => ‖1 - σ m‖) 1 := by fun_prop
    exact this.eventually_le_const (by simp [h1])
  have hPt : Tendsto P (𝓝 1) (𝓝 0) := hP0 ▸ P.continuous.tendsto 1
  have ht : Tendsto (fun a => Θ (Ψ (P a))) (𝓝 1) (𝓝 1) := by
    have := hD.continuousAt.tendsto.comp p1
    rw [h0] at this
    exact this.comp hPt
  refine ⟨_, e, fun a => Ψ (P a), he, p1.comp hPt, ?_⟩
  filter_upwards [hPt.eventually p3, hnear, ht.eventually hnear] with a q1 q2 q3 ha
  haveI : IsArtinianRing E := IsArtinianRing.of_finite ℝ E
  exact GlobalTheory.UnitaryChart.eq_of_skew_eq (hU _).1 (mul_eq_one_comm.1 ha) (hP3 _ _ q1) q3 q2

variable {n : ℕ} {ε : Fin n → Bool}

theorem exists_chart_UJ (ε : Fin n → Bool) :
    ∃ (N : ℕ) (Y : Fin N → Mx n) (Ψ : Mx n → Fin N → ℝ), (∀ i, Y i ∈ lieSet ε) ∧ Tendsto Ψ (𝓝 1) (𝓝 0) ∧
      ∀ᶠ a in 𝓝 (1 : Mx n), a ∈ UJset ε → (List.ofFn fun i => NormedSpace.exp (Ψ a i • Y i)).prod = a := by
  letI : NormedRing (Mx n) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Mx n) := Matrix.linftyOpNormedAlgebra
  have h2 := Jm_mul_self ε
  have hH : (Jm ε)ᴴ = Jm ε := by
    have h : (Jm ε)ᴴ * Jm ε = 1 := (maximal_compact_facts n ε).2.2.1.1.1
    rw [← Matrix.inv_eq_left_inv h, Matrix.inv_eq_left_inv h2]
  set J := Jm ε with hJdef
  let s : Mx n →ₗ[ℝ] Mx n :=
    { toFun := fun x => J * xᴴ * J
      map_add' := fun x y => by rw [conjTranspose_add, mul_add, add_mul]
      map_smul' := fun c x => by simp [conjTranspose_smul] }
  have hs : ∀ x, s x = J * xᴴ * J := fun _ => rfl
  have hJJ : ∀ x : Mx n, J * (J * x) = x := fun x => by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  obtain ⟨N, Y, Ψ, hY, hΨ, hE⟩ := exists_chart s
    (fun a => by simp only [hs, conjTranspose_mul, conjTranspose_conjTranspose, hH, Matrix.mul_assoc, hJJ, h2,
      Matrix.mul_one])
    (fun a b => by simp only [hs, conjTranspose_mul, Matrix.mul_assoc, hJJ]) (by simp [hs, h2])
  refine ⟨N, Y, Ψ, fun i => ?_, hΨ, hE.mono fun g q hg => q ?_⟩
  · have := congrArg (J * ·) (hY i)
    simp only [hs, Matrix.mul_assoc, hJJ, Matrix.mul_neg] at this
    show (Y i)ᴴ * J + J * Y i = 0
    rw [this, neg_add_cancel]
  · have hg' : gᴴ * J * g = J := hg
    rw [hs, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg', h2]

theorem exists_step_bound {f f' : Mx n → ℂ} {X : Mx n} (hX : X ∈ lieSet ε) {C : ℝ} {N : ℕ}
    (hd : ∀ g ∈ UJset ε, HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp (t • X))) (f' g) 0)
    (hb : ∀ g ∈ UJset ε, ‖f' g‖ ≤ C * (1 + hs g) ^ N) :
    ∃ B : ℝ, ∀ a ∈ UJset ε, ∀ s ∈ Metric.closedBall (0 : ℝ) 1,
      ‖f (a * NormedSpace.exp (s • X)) - f a‖ ≤ |C| * ((1 + hs a) * B) ^ N * ‖s‖ := by
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℝ) 1).bddAbove_image
    (f := fun u : ℝ => 1 + hs (NormedSpace.exp (u • X)))
    (continuous_const.add (continuous_hs.comp (continuous_exp_smul X))).continuousOn
  refine ⟨B, fun a ha s hs1 => ?_⟩
  have := (convex_closedBall (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun t : ℝ => f (a * NormedSpace.exp (t • X))) (f' := fun t => f' (a * NormedSpace.exp (t • X)))
    (C := |C| * ((1 + hs a) * B) ^ N) (x := 0) (y := s) (fun t _ => ?_) (fun t ht => ?_)
    (Metric.mem_closedBall_self zero_le_one) hs1
  · simpa using this
  · have k := hd _ (mul_mem_UJ ha (exp_mem_UJ hX t))
    have k2 := HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact k)
    refine (k2.congr_of_eventuallyEq (Eventually.of_forall fun u => ?_)).hasDerivWithinAt
    beta_reduce
    rw [Matrix.mul_assoc, ← exp_add_smul, add_sub_cancel]
  · refine (hb _ (mul_mem_UJ ha (exp_mem_UJ hX t))).trans ?_
    have h0 := hs_nonneg (a * NormedSpace.exp (t • X))
    have h1 := hs_nonneg a
    refine mul_le_mul (le_abs_self C) (pow_le_pow_left₀ (by positivity) ?_ N) (by positivity) (abs_nonneg C)
    exact (one_add_hs_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hB ⟨t, ht, rfl⟩) (by positivity))

theorem tendsto_prod {f : Mx n → ℂ} {α : Type} {L : Filter α} {g₀ : Mx n} {c : ℂ} {N : ℕ}
    (hf : ∀ X ∈ lieSet ε, ∃ (f' : Mx n → ℂ) (C : ℝ),
      (∀ g ∈ UJset ε, HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp (t • X))) (f' g) 0) ∧
      ∀ g ∈ UJset ε, ‖f' g‖ ≤ C * (1 + hs g) ^ N) :
    ∀ (d : ℕ) (Y : Fin d → Mx n) (t : α → Fin d → ℝ) (a : α → Mx n), (∀ i, Y i ∈ lieSet ε) →
      (∀ i, Tendsto (fun p => t p i) L (𝓝 0)) → (∀ p, a p ∈ UJset ε) → Tendsto a L (𝓝 g₀) →
      Tendsto (fun p => f (a p)) L (𝓝 c) →
      Tendsto (fun p => f (a p * (List.ofFn fun i => NormedSpace.exp (t p i • Y i)).prod)) L (𝓝 c) := by
  intro d
  induction d with
  | zero => intro Y t a _ _ _ _ h; simpa using h
  | succ d ih =>
    intro Y t a hY ht ha hag hc
    simp only [List.ofFn_succ, List.prod_cons, ← Matrix.mul_assoc]
    refine ih (fun i => Y i.succ) (fun p i => t p i.succ) (fun p => a p * NormedSpace.exp (t p 0 • Y 0))
      (fun i => hY _) (fun i => ht _) (fun p => mul_mem_UJ (ha p) (exp_mem_UJ (hY 0) _)) ?_ ?_
    · have := hag.mul (((continuous_exp_smul (Y 0)).tendsto 0).comp (ht 0))
      simpa using this
    · obtain ⟨f', C, h1, h2⟩ := hf _ (hY 0)
      obtain ⟨B, hB⟩ := exists_step_bound (hY 0) h1 h2
      have h3 : Tendsto (fun p => f (a p * NormedSpace.exp (t p 0 • Y 0)) - f (a p)) L (𝓝 0) := by
        refine squeeze_zero_norm' (a := fun p => |C| * ((1 + hs (a p)) * B) ^ N * ‖t p 0‖) ?_ ?_
        · filter_upwards [(ht 0).eventually (Metric.closedBall_mem_nhds (0 : ℝ) one_pos)] with p hp
          exact hB _ (ha p) _ hp
        · have := (((((continuous_hs.tendsto g₀).comp hag).const_add 1).mul_const B).pow N |>.const_mul |C|).mul
            (ht 0).norm
          simpa using this
      simpa using h3.add hc

theorem continuousOn_of_isDerFam : ∀ (n : ℕ) (ε : Fin n → Bool) (N : ℕ) (F : List (Mx n) → Mx n → ℂ),
    IsDerFam ε F → FamGrowth ε N F →
    ∀ l : List (Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ContinuousOn (F l) (UJset ε) := by
  intro n ε N F hF hG l hl g₀ hg₀
  obtain ⟨d, Y, Ψ, hY, hΨ, hE⟩ := exists_chart_UJ ε
  have ht : Tendsto (fun g => g₀⁻¹ * g) (𝓝[UJset ε] g₀) (𝓝 1) := by
    have := ((continuous_const (y := g₀⁻¹)).matrix_mul continuous_id).tendsto g₀
    rw [id, inv_mul_UJ hg₀] at this
    exact this.mono_left nhdsWithin_le_nhds
  have key := tendsto_prod (ε := ε) (f := F l) (L := 𝓝[UJset ε] g₀) (g₀ := g₀) (c := F l g₀) (N := N)
    (fun X hX => by
      obtain ⟨C, hC⟩ := hG (X :: l) (List.forall_mem_cons.2 ⟨hX, hl⟩)
      exact ⟨F (X :: l), C, hF l hl X hX, hC⟩)
    d Y (fun g => Ψ (g₀⁻¹ * g)) (fun _ => g₀) hY (fun i => tendsto_pi_nhds.1 (hΨ.comp ht) i) (fun _ => hg₀)
    tendsto_const_nhds tendsto_const_nhds
  refine key.congr' ?_
  filter_upwards [ht.eventually hE, self_mem_nhdsWithin] with g q hg
  rw [q (mul_mem_UJ (inv_mem_UJ hg₀) hg), ← Matrix.mul_assoc, mul_inv_UJ hg₀, Matrix.one_mul]

end GlobalTheory.TypeSum.DerFamCont

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
open scoped TensorProduct

namespace GlobalTheory

theorem exists_away_algHom_ker {K R Q : Type*} [CommRing K] [CommRing R] [CommRing Q] [Algebra K R] [Algebra K Q]
    {n : ℕ} (Ψ : R →ₐ[K] Q) (a : Fin (n + 1) → R) (hs : Function.Surjective Ψ)
    (hk : RingHom.ker Ψ = Ideal.span (Set.range fun i : Fin n => a i.succ)) (hu : IsUnit (Ψ (a 0))) :
    ∃ χ : Localization.Away (a 0) →ₐ[K] Q, Function.Surjective χ ∧
      RingHom.ker χ = Ideal.span (Set.range fun i : Fin n =>
        algebraMap R (Localization.Away (a 0)) (a i.succ) * IsLocalization.Away.invSelf (a 0)) ∧
      ∀ r, χ (algebraMap R (Localization.Away (a 0)) r) = Ψ r := by
  have hunit : ∀ y : Submonoid.powers (a 0), IsUnit (Ψ y) := by
    rintro ⟨_, m, rfl⟩
    simpa using hu.pow m
  let χ : Localization.Away (a 0) →ₐ[K] Q := IsLocalization.liftAlgHom (M := Submonoid.powers (a 0)) hunit
  have hχ : ∀ r, χ (algebraMap R (Localization.Away (a 0)) r) = Ψ r := fun r => by
    simp [χ]
  refine ⟨χ, fun q => ?_, le_antisymm ?_ ?_, hχ⟩
  · obtain ⟨r, rfl⟩ := hs q
    exact ⟨_, hχ r⟩
  · intro z hz
    obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (Submonoid.powers (a 0)) z
    have hr : r ∈ RingHom.ker Ψ := by
      rw [RingHom.mem_ker] at hz ⊢
      have := congrArg χ hrs
      rw [map_mul, hz, zero_mul, hχ] at this
      exact this.symm
    rw [hk] at hr
    have hle : Ideal.span (Set.range fun i : Fin n => a i.succ) ≤
        (Ideal.span (Set.range fun i : Fin n =>
          algebraMap R (Localization.Away (a 0)) (a i.succ) * IsLocalization.Away.invSelf (a 0))).comap
          (algebraMap R (Localization.Away (a 0))) := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      have e : algebraMap R (Localization.Away (a 0)) (a i.succ) =
          algebraMap R (Localization.Away (a 0)) (a 0) *
            (algebraMap R (Localization.Away (a 0)) (a i.succ) * IsLocalization.Away.invSelf (a 0)) := by
        rw [mul_left_comm, IsLocalization.Away.mul_invSelf, mul_one]
      show algebraMap R (Localization.Away (a 0)) (a i.succ) ∈ Ideal.span _
      rw [e]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
    have h2 := hle hr
    rw [Ideal.mem_comap] at h2
    simp only at hrs
    rw [← hrs] at h2
    exact (Ideal.mul_unit_mem_iff_mem _ (IsLocalization.map_units _ s)).1 h2
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    have : Ψ (a i.succ) = 0 := by
      rw [← RingHom.mem_ker, hk]
      exact Ideal.subset_span ⟨i, rfl⟩
    show χ _ = 0
    rw [map_mul, hχ, this, zero_mul]


open ReciprocityTheory.ChartRestriction.G.T0 in
theorem genericSection_away_quotient {K Ω Kl K' : Type} [Field K] [Field Ω] [Algebra K Ω] [Field Kl] [Field K']
    [Algebra K Kl] [Algebra Kl K'] {Dd m D' N' : ℕ} (hD : D' + 1 = Dd + 1) (eN : Fin (N' + 1) ≃ Fin m)
    (j₀ : Fin (N' + 1)) (x : Fin N' → Ω) [Algebra (KTf K D' N') (OmS Ω D' N')]
    [FiniteDimensional (KTf K D' N') (OmS Ω D' N')] [Algebra (KTf K D' N') K']
    (t : Fin (Dd + 1) × Fin m → K') (v : Fin m → Ω)
    (hs : ∀ p : KTp K D' N', algebraMap (KTf K D' N') (OmS Ω D' N') (algebraMap (KTp K D' N') (KTf K D' N') p) =
      sHom j₀ x p)
    (hK : ∀ a : K, algebraMap (KTf K D' N') K' (algebraMap K (KTf K D' N') a) = algebraMap Kl K' (algebraMap K Kl a))
    (ht : ∀ q : TVar D' N', algebraMap (KTf K D' N') K' (algebraMap (KTp K D' N') (KTf K D' N') (MvPolynomial.X q)) =
      t (Fin.cast hD q.1, eN q.2))
    (hv : v (eN j₀) ≠ 0) (hx : ∀ k, x k * v (eN j₀) = v (eN (j₀.succAbove k)))
    (a : Fin (Dd + 1) → K' ⊗[Kl] (Kl ⊗[K] Ω)) (ha : ∀ i, a i = ∑ k, t (i, k) ⊗ₜ[Kl] ((1 : Kl) ⊗ₜ[K] v k)) :
    ∃ χ : Localization.Away (a 0) →ₐ[K'] K' ⊗[KTf K D' N'] OmS Ω D' N', Function.Surjective χ ∧
      RingHom.ker χ = Ideal.span (Set.range fun i : Fin Dd =>
        algebraMap _ (Localization.Away (a 0)) (a i.succ) * IsLocalization.Away.invSelf (a 0)) ∧
      ∀ ω : Ω, χ (algebraMap (K' ⊗[Kl] (Kl ⊗[K] Ω)) (Localization.Away (a 0)) ((1 : K') ⊗ₜ[Kl] ((1 : Kl) ⊗ₜ[K] ω))) =
        (1 : K') ⊗ₜ[KTf K D' N'] algebraMap Ω (OmS Ω D' N') ω := by
  obtain rfl : D' = Dd := by omega
  letI : Algebra K K' := ((algebraMap Kl K').comp (algebraMap K Kl)).toAlgebra
  haveI : IsScalarTower K Kl K' := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower K (KTf K D' N') K' := IsScalarTower.of_algebraMap_eq fun c => (hK c).symm
  obtain ⟨Φ, hΦ, hsurj, hker, hunit⟩ := genericSection_quotient K Ω K' D' N' j₀ x
    (fun q => t (q.1, eN q.2)) (fun k => v (eN k) / v (eN j₀)) hs (fun q => (ht q).symm) (div_self hv)
    (fun k => by rw [div_eq_iff hv, hx])
  let Φ' : K' ⊗[K] Ω →ₐ[K'] K' ⊗[KTf K D' N'] OmS Ω D' N' :=
    { Φ with
      commutes' := fun c => by
        show Φ (c ⊗ₜ[K] 1) = c ⊗ₜ 1
        rw [hΦ, map_one] }
  let e : K' ⊗[Kl] (Kl ⊗[K] Ω) ≃ₐ[K'] K' ⊗[K] Ω := Algebra.TensorProduct.cancelBaseChange K Kl K' K' Ω
  have he : ∀ (c : K') (ω : Ω), e (c ⊗ₜ[Kl] ((1 : Kl) ⊗ₜ[K] ω)) = c ⊗ₜ[K] ω := fun c ω => by
    simp [e]
  let u : K' ⊗[K] Ω := (1 : K') ⊗ₜ[K] v (eN j₀)
  have hu : IsUnit u :=
    (IsUnit.mk0 _ hv).map (Algebra.TensorProduct.includeRight (R := K) (A := K') (B := Ω))
  have hea : ∀ i, e (a i) = u * ∑ k, t (i, eN k) ⊗ₜ[K] (v (eN k) / v (eN j₀)) := fun i => by

    rw [ha, map_sum, Finset.mul_sum, ← Equiv.sum_comp eN]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [he, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_div_cancel₀ _ hv]
  have hΨ : ∀ r, (Φ'.comp e.toAlgHom) r = Φ (e r) := fun _ => rfl
  obtain ⟨χ, h1, h2, h3⟩ := exists_away_algHom_ker (Φ'.comp e.toAlgHom) a (hsurj.comp e.surjective)
    (by
      apply le_antisymm
      · intro r hr
        have hr' : e r ∈ RingHom.ker Φ := hr
        rw [hker] at hr'
        have hle : Ideal.span (Set.range fun i : Fin D' =>
            (∑ k, t (i.succ, eN k) ⊗ₜ[K] (v (eN k) / v (eN j₀)) : K' ⊗[K] Ω)) ≤
            (Ideal.span (Set.range fun i : Fin D' => a i.succ)).comap e.symm := by
          rw [Ideal.span_le]
          rintro _ ⟨i, rfl⟩
          have h0 : a i.succ ∈ Ideal.span (Set.range fun i : Fin D' => a i.succ) := Ideal.subset_span ⟨i, rfl⟩
          rw [← e.symm_apply_apply (a i.succ), hea, map_mul,
            Ideal.unit_mul_mem_iff_mem _ (hu.map e.symm)] at h0
          exact h0
        have := hle hr'
        rwa [Ideal.mem_comap, AlgEquiv.symm_apply_apply] at this
      · rw [Ideal.span_le]
        rintro _ ⟨i, rfl⟩
        show Φ (e (a i.succ)) = 0
        have : Φ (∑ k, t (i.succ, eN k) ⊗ₜ[K] (v (eN k) / v (eN j₀))) = 0 := by
          rw [← RingHom.mem_ker, hker]
          exact Ideal.subset_span ⟨i, rfl⟩
        rw [hea, map_mul, this, mul_zero])
    (by rw [hΨ, hea, map_mul]; exact (hu.map Φ).mul hunit)
  exact ⟨χ, h1, h2, fun ω => by rw [h3, hΨ, he, hΦ]⟩

section Rec

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO))
  (N : ℕ) (Ω : Type) [Field Ω] [Algebra B.KO Ω] (gF : X.Forms →ₐ[B.KO] Ω) {wL : WeightFamilies.Wt D j}
  (w : Fin N → B.Cusp j wL)

theorem componentRing_sec_eq_sum (i : Fin (WeightFamilies.dimY D j + 1)) :
    rzMap X la N Ω gF (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w i) =
      ∑ k, @algebraMap (Op X la N) (Kp X la N) _ _ _ (Tv X la N (i, k)) ⊗ₜ[X.Kl la]
        ((1 : X.Kl la) ⊗ₜ[B.KO] gF (X.inc wL (w k))) := by

  rw [Formalism.MainNotions.Gaps.EtaleWeightGaps.sec, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, rzMap_emb, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem componentRing_map_sectionIdeal : Ideal.map (phiZ X la N Ω gF w) (Jid X la w) =
    Ideal.span (Set.range fun i : Fin (WeightFamilies.dimY D j) =>
      algebraMap (RZ X la N Ω) (RZs X la N Ω gF w) (rzMap X la N Ω gF (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w i.succ)) *
        IsLocalization.Away.invSelf (rzMap X la N Ω gF (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0))) := by
  have key : ∀ {R : Type} [CommRing R] {a b c : R}, a * b = 1 → a * c = 1 → b = c :=
    fun {_} _ {_} {b} {c} h1 h2 => by linear_combination c * h1 - b * h2
  rw [Jid, Ideal.map_span, ← Set.range_comp]
  refine congrArg Ideal.span (congrArg Set.range (funext fun i => ?_))
  show phiZ X la N Ω gF w (sfr X la w i.succ) = _
  rw [phiZ_apply, coe_sfr, frac_apply, pow_one, map_mul, lwZ_alg]
  congr 1
  have h1 := congrArg (lwZ X la N Ω gF w) (section_mul_inverse_eq_one X la w)
  rw [map_mul, lwZ_alg, map_one] at h1
  exact key h1 (IsLocalization.Away.mul_invSelf _)

end Rec

theorem componentRing_away_quotient :
    ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (wL : WeightFamilies.Wt D j) (w : Fin N → B.Cusp j wL) (Ω : Type) [Field Ω] [Algebra B.KO Ω] (gF : X.Forms →ₐ[B.KO] Ω) (D' N' : ℕ) (hD : D' + 1 = WeightFamilies.dimY D j + 1) (eN : Fin (N' + 1) ≃ Fin N) (j₀ : Fin (N' + 1)) (x : Fin N' → Ω) [Algebra (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D' N')] [FiniteDimensional (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D' N')] [Algebra (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (Kp X la N)], (∀ p : ReciprocityTheory.ChartRestriction.G.T0.KTp B.KO D' N', algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D' N') (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp B.KO D' N') (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') p) = ReciprocityTheory.ChartRestriction.G.T0.sHom j₀ x p) → (∀ a : B.KO, algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (Kp X la N) (algebraMap B.KO (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') a) = algebraMap (X.Kl la) (Kp X la N) (algebraMap B.KO (X.Kl la) a)) → (∀ q : ReciprocityTheory.ChartRestriction.G.T0.TVar D' N', algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (Kp X la N) (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp B.KO D' N') (ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N') (MvPolynomial.X q)) = @algebraMap (Op X la N) (Kp X la N) _ _ _ (Tv X la N (Fin.cast hD q.1, eN q.2))) → gF (X.inc wL (w (eN j₀))) ≠ 0 → (∀ k, x k * gF (X.inc wL (w (eN j₀))) = gF (X.inc wL (w (eN (j₀.succAbove k))))) → ∃ χ : RZs X la N Ω gF w →ₐ[Kp X la N] Kp X la N ⊗[ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N'] ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D' N', Function.Surjective χ ∧ RingHom.ker χ = Ideal.map (phiZ X la N Ω gF w) (Jid X la w) ∧ ∀ ω : Ω, χ (CurveLoc.psiZ X la N w gF ω) = (1 : Kp X la N) ⊗ₜ[ReciprocityTheory.ChartRestriction.G.T0.KTf B.KO D' N'] algebraMap Ω (ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D' N') ω := by
  intro D B P j X la N wL w Ω _ _ gF D' N' hD eN j₀ x _ _ _ hs hK ht hv hx
  rw [componentRing_map_sectionIdeal]
  exact genericSection_away_quotient (Kl := X.Kl la) hD eN j₀ x
    (fun p => @algebraMap (Op X la N) (Kp X la N) _ _ _ (Tv X la N p)) (fun k => gF (X.inc wL (w k))) hs hK ht hv hx
    (fun i => rzMap X la N Ω gF (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w i))
    (fun i => componentRing_sec_eq_sum X la N Ω gF w i)

end GlobalTheory
end
