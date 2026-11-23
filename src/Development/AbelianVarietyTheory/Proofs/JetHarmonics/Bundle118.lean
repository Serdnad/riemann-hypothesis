module

public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle002
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameExistsAndVectorEqSmulTranslate
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle004
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle111
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle112
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HarmonicValueNormalisedPullbackChainRule
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HatLettersPassDiGIBoundedFactors
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowPullbackSecModelUniversalBijective
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle021
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle105
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ImagQuadraticMaximalOrderArithmeticAtSplitPrime
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle110
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GoodPlaceDepthBoundProof
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle007
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle013
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle017
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle002
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory.WigSh

theorem norm_adjoint_apply_of_norm_preserving {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (P : V →L[ℂ] V) (hP : ∀ v, ‖P v‖ = ‖v‖) (v : V) :
    ‖ContinuousLinearMap.adjoint P v‖ = ‖v‖ := by
  let L : V →ₗᵢ[ℂ] V := ⟨(P : V →ₗ[ℂ] V), hP⟩
  have hsurj : Function.Surjective (P : V →ₗ[ℂ] V) :=
    LinearMap.surjective_of_injective (f := (P : V →ₗ[ℂ] V)) L.injective
  obtain ⟨u, rfl⟩ := hsurj v
  have h1 : ContinuousLinearMap.adjoint P (P u) = u := by
    apply ext_inner_right ℂ
    intro w
    rw [ContinuousLinearMap.adjoint_inner_left]
    exact L.inner_map_map u w
  change ‖ContinuousLinearMap.adjoint P (P u)‖ = ‖P u‖
  rw [h1, hP]

theorem norm_adjoint_of_intertwine {V U : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [NormedAddCommGroup U] [InnerProductSpace ℂ U] [FiniteDimensional ℂ U]
    (P : V →L[ℂ] V) (Q : U →L[ℂ] U) (A A' : U →L[ℂ] V) (hQ : ∀ v, ‖Q v‖ = ‖v‖)
    (h : A'.comp Q = P.comp A) (v : V) :
    ‖ContinuousLinearMap.adjoint A' v‖ = ‖ContinuousLinearMap.adjoint A (ContinuousLinearMap.adjoint P v)‖ := by
  rw [← norm_adjoint_apply_of_norm_preserving Q hQ]
  have h1 := congrArg (fun T : U →L[ℂ] V => ContinuousLinearMap.adjoint T v) h
  simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply] at h1
  rw [h1]

theorem norm_adjoint_real_pow_smul {V U : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [NormedAddCommGroup U] [InnerProductSpace ℂ U] [FiniteDimensional ℂ U]
    (A : U →L[ℂ] V) (t : ℝ) (d : ℕ) (v : V) :
    ‖ContinuousLinearMap.adjoint (((t : ℂ) ^ d) • A) v‖ ^ 2 =
      (t ^ 2) ^ d * ‖ContinuousLinearMap.adjoint A v‖ ^ 2 := by
  rw [LinearIsometryEquiv.map_smulₛₗ, ContinuousLinearMap.smul_apply, norm_smul, mul_pow]
  congr 1
  rw [RCLike.norm_conj, norm_pow, Complex.norm_real, Real.norm_eq_abs, ← pow_mul, mul_comm, pow_mul, sq_abs]

theorem lower_bound_spreads :
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp] (Vm : Type) [NormedAddCommGroup Vm] [InnerProductSpace ℂ Vm] [FiniteDimensional ℂ Vm] (n r : ℕ) (z : (Fin (2 * r + (n + 1) + 1) → ℂ)) (π : Mx (n + 1) r → (V →L[ℂ] V)) (πp : Mx (n + 1) r → (Vp →L[ℂ] Vp)) (πm : Mx (n + 1) r → (Vm →L[ℂ] Vm)) (B : Fin (n + 1) → (Fin (2 * r + (n + 1) + 1) → ℂ)) (Ap : (Fin (2 * r + (n + 1) + 1) → ℂ) → (Vp →L[ℂ] V)) (Am : (Fin (2 * r + (n + 1) + 1) → ℂ) → (Vm →L[ℂ] V)) (n₀ : ℕ) (b : ℝ), inWb (n + 1) r z → 0 < Tz (n + 1) r z → (∀ h ∈ UWset (n + 1) r z, ∀ v, ‖π h v‖ = ‖v‖) → (∀ h ∈ UWset (n + 1) r z, ∀ v, ‖πp h v‖ = ‖v‖) → (∀ h ∈ UWset (n + 1) r z, ∀ v, ‖πm h v‖ = ‖v‖) → IsFrameOf (n + 1) r [z] B → GlobalTheory.WigSh.WigMap (n + 1) r z πp π n₀ Ap → GlobalTheory.WigSh.WigMap (n + 1) r z πm π n₀ Am → (∀ v : V, ‖v‖ ^ 2 ≤ (3 * b) ^ (2 * n₀) * (‖ContinuousLinearMap.adjoint (Ap (B (Fin.last n))) v‖ ^ 2 + ‖ContinuousLinearMap.adjoint (Am (B (Fin.last n))) v‖ ^ 2)) → ∀ ω, inWb (n + 1) r ω → herm (Hpk (n + 1) r) ω z = 0 → ∀ v : V, (herm (Hpk (n + 1) r) ω ω).re ^ n₀ * ‖v‖ ^ 2 ≤ (3 * b) ^ (2 * n₀) * (‖ContinuousLinearMap.adjoint (Ap ω) v‖ ^ 2 + ‖ContinuousLinearMap.adjoint (Am ω) v‖ ^ 2) := by
  intro V _ _ _ Vp _ _ _ Vm _ _ _ n r z π πp πm B Ap Am n₀ b hz hT hπ hπp hπm hB hAp hAm hlow ω hω hωz v
  obtain ⟨t, h, hh, -, hre, rfl⟩ :=
    (GlobalTheory.frame_exists_and_vector_eq_smul_translate n r z hz hT).2 B hB ω hω hωz
  rw [hre, hAp.2.2.1, hAm.2.2.1, norm_adjoint_real_pow_smul, norm_adjoint_real_pow_smul,
    norm_adjoint_of_intertwine (π h) (πp h) _ _ (hπp h hh) (hAp.2.1 h hh _),
    norm_adjoint_of_intertwine (π h) (πm h) _ _ (hπm h hh) (hAm.2.1 h hh _)]
  have h1 := hlow (ContinuousLinearMap.adjoint (π h) v)
  rw [norm_adjoint_apply_of_norm_preserving (π h) (hπ h hh)] at h1
  have h2 : (0 : ℝ) ≤ (t ^ 2) ^ n₀ := by positivity
  calc _ ≤ _ := mul_le_mul_of_nonneg_left h1 h2
    _ = _ := by ring

end GlobalTheory.WigSh
end

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF

open MeasureTheory in
private theorem exists_hat_mul_m_eq_double_sum {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ}
    (L : _root_.Formalism.FourierDecayAlt.R.LevelData A r) (h : A) (Z : ℂ → A) (Xc : ℕ → A)
    (hZ : ∀ s : ℂ, Z s = ∑ j ∈ Finset.range (r + 2), s ^ j • Xc j)
    (hrule : ∀ m : ℕ → A, _root_.GlobalTheory.HatNF.MulRel L m → ∀ q,
      h * m q = ∑ j ∈ Finset.range (r + 2), m (q + j) * Xc j)
    (hmem : ∀ s, Z s ∈ _root_.GlobalTheory.HatNF.hats L) :
    ∃ (d : Fin (r + 2) → Fin (r + 2) → ℂ) (g : Fin (r + 2) → A),
      (∀ i, g i ∈ _root_.GlobalTheory.HatNF.hats L) ∧ ∀ m : ℕ → A, _root_.GlobalTheory.HatNF.MulRel L m → ∀ q,
        h * m q = ∑ j : Fin (r + 2), ∑ i : Fin (r + 2), d j i • (m (q + j) * g i) := by
  have hν : Function.Injective (fun i : Fin (r + 2) => ((i : ℕ) : ℂ)) :=
    fun i j hij => Fin.ext (by simpa using hij)
  have hspan := (_root_.GlobalTheory.vecPoly_mem_span_values A (r + 2) Z Xc _ hν hZ).1
  have hcoef : ∀ j : Fin (r + 2), ∃ c : Fin (r + 2) → ℂ,
      ∑ i, c i • Z ((i : ℕ) : ℂ) = Xc j :=
    fun j => (Submodule.mem_span_range_iff_exists_fun ℂ).mp (hspan j j.2)
  choose d hd using hcoef
  refine ⟨d, fun i => Z ((i : ℕ) : ℂ), fun i => hmem _, fun m hm q => ?_⟩
  rw [hrule m hm q, Finset.sum_range (fun j => m (q + j) * Xc j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← hd j, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul_comm]

open MeasureTheory in
private theorem exists_hat_mul_multiplier_expansion {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ}
    (L : _root_.Formalism.FourierDecayAlt.R.LevelData A r) {h : A} (hh : h ∈ _root_.GlobalTheory.HatNF.hats L) :
    ∃ (d : Fin (r + 2) → Fin (r + 2) → ℂ) (g : Fin (r + 2) → A),
      (∀ i, g i ∈ _root_.GlobalTheory.HatNF.hats L) ∧ ∀ m : ℕ → A, _root_.GlobalTheory.HatNF.MulRel L m → ∀ q,
        h * m q = ∑ j : Fin (r + 2), ∑ i : Fin (r + 2), d j i • (m (q + j) * g i) := by
  unfold _root_.GlobalTheory.HatNF.hats at hh
  rcases hh with ((⟨Y, rfl⟩ | ⟨Y, rfl⟩) | ⟨Y, rfl⟩) | ⟨Y, rfl⟩
  · obtain ⟨Xa, Xr, hXa, hXr, hrel⟩ := _root_.GlobalTheory.HatTaylorPlus.taylor_plus A r L Y
    exact exists_hat_mul_m_eq_double_sum L _ (fun s => L.Ahat (Y + s)) Xa hXa
      (fun m hm q => (hrel m hm q).1)
      (fun s => by unfold _root_.GlobalTheory.HatNF.hats; exact Or.inl (Or.inl (Or.inl ⟨_, rfl⟩)))
  · obtain ⟨Xa, Xr, hXa, hXr, hrel⟩ := _root_.GlobalTheory.HatTaylorPlus.taylor_plus A r L Y
    exact exists_hat_mul_m_eq_double_sum L _ (fun s => L.R0 (Y + s)) Xr hXr
      (fun m hm q => (hrel m hm q).2)
      (fun s => by unfold _root_.GlobalTheory.HatNF.hats; exact Or.inl (Or.inl (Or.inr ⟨_, rfl⟩)))
  · obtain ⟨Xa, Xr, hXa, hXr, hrel⟩ := _root_.GlobalTheory.HatNF.TaylorMinus.taylor_minus A r L Y
    exact exists_hat_mul_m_eq_double_sum L _ (fun s => L.Ahatv (Y - s)) Xa hXa
      (fun m hm q => (hrel m hm q).1)
      (fun s => by unfold _root_.GlobalTheory.HatNF.hats; exact Or.inl (Or.inr ⟨_, rfl⟩))
  · obtain ⟨Xa, Xr, hXa, hXr, hrel⟩ := _root_.GlobalTheory.HatNF.TaylorMinus.taylor_minus A r L Y
    exact exists_hat_mul_m_eq_double_sum L _ (fun s => L.R0v (Y - s)) Xr hXr
      (fun m hm q => (hrel m hm q).2)
      (fun s => by unfold _root_.GlobalTheory.HatNF.hats; exact Or.inr ⟨_, rfl⟩)

open MeasureTheory in
private theorem exists_hatWord_mul_multiplier_expansion {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ}
    (L : _root_.Formalism.FourierDecayAlt.R.LevelData A r) (H : List A) (hH : ∀ h ∈ H, h ∈ _root_.GlobalTheory.HatNF.hats L) :
    ∃ (ι : Type) (_ : Fintype ι) (a : ι → ℕ) (c : ι → ℂ) (P : ι → List A),
      (∀ i, a i ≤ H.length * (r + 1) ∧ (P i).length = H.length ∧
        ∀ h ∈ P i, h ∈ _root_.GlobalTheory.HatNF.hats L) ∧
      ∀ m : ℕ → A, _root_.GlobalTheory.HatNF.MulRel L m → ∀ q,
        H.prod * m q = ∑ i, c i • (m (q + a i) * (P i).prod) := by
  induction H with
  | nil =>
    exact ⟨Unit, inferInstance, fun _ => 0, fun _ => 1, fun _ => [],
      fun _ => ⟨by simp, rfl, by simp⟩, fun m _ q => by simp⟩
  | cons h H ih =>
    obtain ⟨ι, _, a, c, P, hP, hrep⟩ := ih fun x hx => hH x (List.mem_cons_of_mem _ hx)
    obtain ⟨d, g, hg, hrel⟩ := exists_hat_mul_multiplier_expansion L (hH h List.mem_cons_self)
    refine ⟨ι × Fin (r + 2) × Fin (r + 2), inferInstance, fun x => a x.1 + x.2.1,
      fun x => c x.1 * d x.2.1 x.2.2, fun x => g x.2.2 :: P x.1, fun x => ⟨?_, ?_, ?_⟩,
      fun m hm q => ?_⟩
    · have h1 := (hP x.1).1
      have h2 : (x.2.1 : ℕ) ≤ r + 1 := Nat.lt_succ_iff.mp x.2.1.isLt
      rw [List.length_cons, Nat.succ_mul]
      linarith
    · simp [(hP x.1).2.1]
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hg _
      · exact (hP x.1).2.2 y hy
    · rw [List.prod_cons, mul_assoc, hrep m hm q, Finset.mul_sum, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fintype.sum_prod_type, mul_smul_comm, ← mul_assoc, hrel m hm (q + a i), Finset.sum_mul,
        Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_mul, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [List.prod_cons, smul_mul_assoc, smul_smul, add_assoc, mul_assoc]


open MeasureTheory in
theorem _root_.GlobalTheory.HatNF.prod_hats_mul_multiplier : ∀ (A : Type) [Ring A] [Algebra ℂ A] (r : ℕ) (L : _root_.Formalism.FourierDecayAlt.R.LevelData A r), ∀ H : List A, (∀ h ∈ H, h ∈ _root_.GlobalTheory.HatNF.hats L) → ∃ ts : List (ℕ × ℂ × List A), (∀ t ∈ ts, t.1 ≤ H.length * (r + 1) ∧ t.2.2.length = H.length ∧ ∀ h ∈ t.2.2, h ∈ _root_.GlobalTheory.HatNF.hats L) ∧ ∀ m : ℕ → A, _root_.GlobalTheory.HatNF.MulRel L m → ∀ q, H.prod * m q = (ts.map fun t => t.2.1 • (m (q + t.1) * t.2.2.prod)).sum := by
  intro A _ _ r L H hH
  obtain ⟨ι, _, a, c, P, hP, hrep⟩ := exists_hatWord_mul_multiplier_expansion L H hH
  refine ⟨(Finset.univ : Finset ι).toList.map fun i => (a i, c i, P i), ?_, fun m hm q => ?_⟩
  · intro t ht
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp ht
    exact hP i
  · rw [hrep m hm q, List.map_map, Finset.sum_map_toList]
    rfl

end GlobalTheory.HatNF
end

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem _root_.GlobalTheory.T.connection_mulRel_of_entry_relations : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ m : ℕ → A, (∀ q, (∀ f ∈ d.L.fns, Commute f (m q)) ∧ (∀ l, d.L.p l * m q = m q * d.L.p l + m (q + 1)) ∧ (∀ l, d.L.pb l * m q = m q * d.L.pb l + m (q + 1)) ∧ (∀ f : M.Ty P → ℂ, Commute (d.κ f) (m q)) ∧ star (m q) = m q ∧ ∀ Y : ℝ, d.QQ Y 1 0 * m q = m q * d.QQ Y 1 0 - d.L.ζb * d.L.GGi * m (q + 1) * d.QQ Y 1 1) → MulRel d.L m := by
  first | exact @GlobalTheory.HatNF.MulRelAlg.mulRel_of_entries | exact GlobalTheory.HatNF.MulRelAlg.mulRel_of_entries | (intros; apply GlobalTheory.HatNF.MulRelAlg.mulRel_of_entries <;> assumption)
end

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem _root_.GlobalTheory.T.R0_and_R0v_mem_nfSpan_basics_of_xC_ne_zero : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ y : ℝ, (∀ ρ : M.Ty P, M.xC P ρ (y : ℂ) ≠ 0 ∧ M.xC P ρ ((y : ℂ) - 1) ≠ 0 ∧ M.xC P ρ ((y : ℂ) + 1) ≠ 0) → d.L.R0 y ∈ nfSpan d (basics d) 0 0 1 ∧ d.L.R0v y ∈ nfSpan d (basics d) 0 0 1 := by
  first | exact @GlobalTheory.HatNF.r0_mem_nfSpan_basics | exact GlobalTheory.HatNF.r0_mem_nfSpan_basics | (intros; apply GlobalTheory.HatNF.r0_mem_nfSpan_basics <;> assumption)
end

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem _root_.GlobalTheory.T.frameStart_constants_normalForm_empty_word : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ (L : LevelData A P.r) (st : Start A) (s : ℂ), Comparison₂ d L st s → (∀ x ∈ TL.kAlg st, x ∈ Set.range d.κ) ∧ ∀ Y ∈ st.inv, ∃ E ∈ nfSpan d ∅ 0 0 0, L.l0 Y + L.ζb * L.ζi * L.GGi * st.ee Y = d.L.l0 Y + d.L.ζb * d.L.ζi * d.L.GGi * E := by
  first | exact @GlobalTheory.HatNF.start_normalForm | exact GlobalTheory.HatNF.start_normalForm | (intros; apply GlobalTheory.HatNF.start_normalForm <;> assumption)
end

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem _root_.GlobalTheory.T.normalForm_entries_commutator_multiplier : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ (φ : ℝ → ℝ) (W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')), LE.SmoothLog φ → IsMulG P Bs φ W → ∀ (q : ℕ) (Y : ℂ), X.t Y 1 0 * W q = W q * X.t Y 1 0 - X.fn 2 * X.fn 5 * W (q + 1) * X.t Y 1 1 ∧ X.t Y 1 1 * W q = W q * X.t Y 1 1 ∧ X.t Y 0 1 * W q = W q * X.t Y 0 1 + X.fn 0 * X.fn 5 * W (q + 1) * X.t Y 1 1 := by
  first | exact @GlobalTheory.HatNF.nf_t_mul_mulG | exact GlobalTheory.HatNF.nf_t_mul_mulG | (intros; apply GlobalTheory.HatNF.nf_t_mul_mulG <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

theorem _root_.GlobalTheory.T.harmonic_value_normalised_pullback_chain_rule : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (F : Type) [Field F] [Algebra c.F F] (yF : FrPt Xo c F) (β : 𝓞 E) (N k : ℕ) (z : ℤ), β * star β = (N : 𝓞 E) → z = ((k * N : ℕ) : ℤ) → ∀ (n : ℕ) (hh : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) (ptO Xo yF.x))) (hh' : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L z (ptO Xo yF.x))), (∀ i, IsNormPull Xo.univ.t.G Xo.univ.t.PP (Xo.univ.t.act.act β) z (k : ℤ) (hh i) (hh' i)) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (Pp : MvPolynomial (LtN Dw n) c.F), Pp ∈ harmA c a n → ∑ m ∈ Pp.support, algebraMap c.F F (Pp.coeff m) * ∏ i, nab yF z (hh' i) (colOf m i) = algebraMap c.F F (nrm Dw c a β) * ∑ m ∈ Pp.support, algebraMap c.F F (Pp.coeff m) * ∏ i, nab yF (k : ℤ) (hh i) (colOf m i) := by
  first | exact @GlobalTheory.ChainRule.harmonic_value_normPull | exact GlobalTheory.ChainRule.harmonic_value_normPull | (intros; apply GlobalTheory.ChainRule.harmonic_value_normPull <;> assumption)
end

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem _root_.GlobalTheory.T.hatLetters_pass_Di_gI_boundedFactors : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → (∀ X ∈ hats d.L, X * d.L.Di ∈ nfSpan d (hats d.L) 1 0 1 ∧ X * TL.gI d.L ∈ nfSpan d (hats d.L) 0 1 1) ∧ (∀ b ∈ bmon d, (∀ f ∈ d.L.fns, Commute b f) ∧ Commute b d.L.Di ∧ Commute b (TL.gI d.L) ∧ star b ∈ bmon d) ∧ Commute d.L.Di (TL.gI d.L) := by
  first | exact @GlobalTheory.HatNF.Den.hat_den | exact GlobalTheory.HatNF.Den.hat_den | (intros; apply GlobalTheory.HatNF.Den.hat_den <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

theorem _root_.GlobalTheory.T.powPullbackSec_modelUniversal_bijective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : letI := io.toAlgebra; FrPt Xo c T.Fr) (I : IntData Xo c T io y) (P : PELUnif (maximalIdeal T.V) I.G) (F : Type) [Field F] [Algebra T.Fr F] (xF : Sp F ⟶ Xo.X), xF = spMap (algebraMap T.Fr F) ≫ (letI := io.toAlgebra; y.x) → ∀ q : ℕ, (∀ σ, ∃! hh, SecTieF I P F xF q σ hh) ∧ (∀ hh, ∃! σ, SecTieF I P F xF q σ hh) ∧ ∀ (u : F) (σ σ' : P.U.toUnifPre.SecGF F q) (hh hh' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L (q : ℤ) (ptO Xo xF))), SecTieF I P F xF q σ hh → (∀ jj, σ'.f jj = resTop _ (scal (fst (TFK (R := T.V) F) ((Over.pullback (jK T.V)).obj I.G.G)).left u) * σ.f jj) → (∀ jj, hh'.f jj = liftFun Xo.univ.t.G _ (toΓ F u) * hh.f jj) → SecTieF I P F xF q σ' hh' := by
  first | exact @GlobalTheory.SecTie.secTie_bijective | exact GlobalTheory.SecTie.secTie_bijective | (intros; apply GlobalTheory.SecTie.secTie_bijective <;> assumption)
end

section

namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory Filter Topology

theorem cutoff_comp_exp_iteratedDeriv_bounded (χ : ℝ → ℝ) (hχ : C6.IsCut0 χ) (p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, |iteratedDeriv p (fun t => χ (Real.exp t)) t| ≤ C := by
  obtain ⟨hs, ⟨δ, hδ, h0⟩, h1⟩ := hχ
  set h : ℝ → ℝ := fun t => χ (Real.exp t) with hh
  have hc : ∀ k t : ℝ, iteratedDeriv p (fun _ : ℝ => k) t = if p = 0 then k else 0 := by
    intro k t
    cases p with
    | zero => simp
    | succ n => simp [iteratedDeriv_succ']
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h := hs.comp Real.contDiff_exp
  have hcont : Continuous (iteratedDeriv p h) := hsm.continuous_iteratedDeriv p (by exact_mod_cast le_top)
  have hlow : ∀ t, t < Real.log δ → iteratedDeriv p h t = 0 := by
    intro t ht
    have : h =ᶠ[𝓝 t] fun _ => (0:ℝ) := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      have := Real.exp_lt_exp.mpr hs
      rw [Real.exp_log hδ] at this
      simp only [hh, h0 _ this]
    rw [this.iteratedDeriv_eq p, hc]; simp
  have hhigh : ∀ t, 0 < t → iteratedDeriv p h t = if p = 0 then 1 else 0 := by
    intro t ht
    have : h =ᶠ[𝓝 t] fun _ => (1:ℝ) := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      have : 1 ≤ Real.exp s := Real.one_le_exp (le_of_lt hs)
      simp [hh, h1 _ this]
    rw [this.iteratedDeriv_eq p, hc]
  obtain ⟨C0, hC0⟩ := (isCompact_Icc (a := Real.log δ) (b := 0)).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max C0 1, le_trans zero_le_one (le_max_right _ _), fun t => ?_⟩
  rcases lt_or_ge t (Real.log δ) with h1 | h1
  · rw [hlow t h1]; simp
  · rcases lt_or_ge 0 t with h2 | h2
    · rw [hhigh t h2]; split_ifs <;> simp
    · exact (hC0 t ⟨h1, h2⟩).trans (le_max_left _ _)

theorem ld_cut_pow_bound (χ : ℝ → ℝ) (hχ : C6.IsCut0 χ) (e j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε x : ℝ, 0 < ε → 0 < x → |LE.ld j (fun y => χ (y / ε) * y ^ e) x| ≤ C * x ^ e := by
  choose B hB0 hB using cutoff_comp_exp_iteratedDeriv_bounded χ hχ
  refine ⟨∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * B i * (e : ℝ) ^ (j - i),
    Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (by positivity) (hB0 i)) (by positivity), ?_⟩
  intro ε x hε hx
  set h : ℝ → ℝ := fun t => χ (Real.exp t) with hh
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h := hχ.1.comp Real.contDiff_exp
  unfold LE.ld
  have e1 : (fun u : ℝ => χ (Real.exp u / ε) * Real.exp u ^ e) =
      fun u : ℝ => h (u - Real.log ε) * Real.exp ((e : ℝ) * u) := by
    funext u
    simp only [hh]
    rw [Real.exp_sub, Real.exp_log hε, Real.exp_nat_mul]
  have c1 : ContDiff ℝ j (fun u : ℝ => h (u - Real.log ε)) :=
    (hsm.of_le (by exact_mod_cast le_top)).comp (contDiff_id.sub contDiff_const)
  have c2 : ContDiff ℝ j (fun u : ℝ => Real.exp ((e : ℝ) * u)) :=
    Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  beta_reduce
  rw [e1, iteratedDeriv_fun_mul c1.contDiffAt c2.contDiffAt, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [iteratedDeriv_comp_sub_const, iteratedDeriv_exp_const_mul]
  beta_reduce
  rw [Real.exp_nat_mul, Real.exp_log hx, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (j.choose i : ℝ)),
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (e : ℝ) ^ (j - i) * x ^ e), ← mul_assoc]
  have := hB i (Real.log x - Real.log ε)
  gcongr

theorem ld_cut_pow : ∀ (χ : ℝ → ℝ) (e J : ℕ), C6.IsCut0 χ →
    (∀ ε : ℝ, 0 < ε → CutPow e fun y => χ (y / ε) * y ^ e) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ε x : ℝ, 0 < ε → 0 < x → ∀ j, j ≤ J →
        |LE.ld j (fun y => χ (y / ε) * y ^ e) x| ≤ C * x ^ e := by
  intro χ e J hχ
  constructor
  · intro ε hε
    obtain ⟨hs, ⟨δ, hδ, h0⟩, h1⟩ := hχ
    refine ⟨(hs.comp (contDiff_id.div_const ε)).mul (contDiff_id.pow e), ⟨δ * ε, by positivity, fun x hx => ?_⟩,
      1, ε, fun x hx => ?_⟩
    · have : x / ε < δ := by rwa [div_lt_iff₀ hε]
      simp [h0 _ this]
    · have : 1 ≤ x / ε := by rwa [le_div_iff₀ hε, one_mul]
      simp [h1 _ this]
  · choose C hC0 hC using ld_cut_pow_bound χ hχ e
    refine ⟨∑ j ∈ Finset.range (J + 1), C j, Finset.sum_nonneg fun j _ => hC0 j, fun ε x hε hx j hj => ?_⟩
    refine (hC j ε x hε hx).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    exact Finset.single_le_sum (f := C) (fun i _ => hC0 i) (Finset.mem_range.mpr (by omega))

end GlobalTheory.HatNF
end

section

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.ScaledQuot

theorem not_inOK_neg_half (d : ℕ) (hd : 0 < d) : ¬ InOK d ((0 : ℂ) - 1 / 2) := by
  rintro ⟨u, v, h⟩
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp [wK] at him hre
  have hv : v = 0 := by
    rcases him with h | h
    · exact h
    · exact absurd h hd.ne'
  subst hv
  have h2 : (2 * u : ℝ) = -1 := by
    simp at hre
    linarith
  have h3 : (2 * u : ℤ) = -1 := by exact_mod_cast h2
  omega

theorem inOK_nat_mul (d s : ℕ) {l : ℂ} (hl : InOK d l) : InOK d ((s : ℂ) * l) := by
  obtain ⟨u, v, rfl⟩ := hl
  exact ⟨s * u, s * v, by push_cast; ring⟩

theorem inOK_nat (d s : ℕ) : InOK d (s : ℂ) := ⟨s, 0, by simp⟩

theorem zero_iff_of_fixed {d : ℕ} {θ : ℂ → ℂ} {x : ℂ} (h : W1 d x θ = θ) (z : ℂ) :
    θ (z + x) = 0 ↔ θ z = 0 := by
  have := congrFun h z
  rw [← this]
  simp [W1, U1, Complex.exp_ne_zero]

theorem scaled_quotient_elliptic : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]) (θ : ℂ → ℂ), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → IsTh d θ → ∀ (t : ℂ) (s : ℕ), 0 < s → Nat.Coprime s q → InOK d ((s : ℂ) * t) → let φ : ℂ → ℂ := fun z => U1 d t θ ((s : ℂ) * z) / θ ((s : ℂ) * z); Ell M.L φ ∧ AnalyticAt ℂ φ 0 ∧ (∀ p, θ ((s : ℂ) * p) ≠ 0 → AnalyticAt ℂ φ p) ∧ (∀ p r, PrimeTo d q r → ¬ InOK d (r - 1 / 2) → θ ((s : ℂ) * p + r) = 0 → ¬ M.Small p) ∧ Bdd (hat M.ι (C ω * logS) φ) := by
  intro d q _ M ω θ hd hd7 hsp hL hch hθ t s hs hsq hst φ
  obtain ⟨hdiff, h0, -, hW, hz⟩ := hθ
  obtain ⟨-, -, hUd, -, -, hper, -, -⟩ := GlobalTheory.T.cmLattice_heisenberg_relations_one_variable d hd.pos
  obtain ⟨-, -, -, -, -, hint, -⟩ := GlobalTheory.MomOne.okArith d q M.ι hd hd7 hsp
  obtain ⟨-, -, -, hsm⟩ := GlobalTheory.T.smallTorsion_killed_by_prime_powers d q M ω hd hd7 hsp hL hch
  have hlin : Differentiable ℂ (fun z : ℂ => (s : ℂ) * z) := by fun_prop
  have hN : ∀ p, AnalyticAt ℂ (fun z => U1 d t θ ((s : ℂ) * z)) p := fun p =>
    ((hUd t θ hdiff).1.comp hlin).analyticAt p
  have hD : ∀ p, AnalyticAt ℂ (fun z => θ ((s : ℂ) * z)) p := fun p =>
    (hdiff.comp hlin).analyticAt p
  have han : ∀ p, θ ((s : ℂ) * p) ≠ 0 → AnalyticAt ℂ φ p := fun p hp =>
    (hN p).div (hD p) hp
  have hE : Ell M.L φ := by
    refine ⟨fun p => (hN p).meromorphicAt.div (hD p).meromorphicAt, ?_⟩
    intro l hl z
    have hl' : InOK d l := (hL l).1 hl
    have hWl := hW _ (inOK_nat_mul d s hl')
    have hk : kap1 d ((s : ℂ) * l) t = 1 := by
      obtain ⟨k, hk⟩ := hint l _ hl' hst
      have e : h1 d ((s : ℂ) * l) t = h1 d l ((s : ℂ) * t) := by
        simp only [h1, map_mul, Complex.conj_natCast]; ring
      rw [kap1, e, hk]
      have := Complex.exp_int_mul_two_pi_mul_I (-k)
      rw [← this]
      congr 1
      push_cast; ring
    have hp := hper θ t ((s : ℂ) * l) ((s : ℂ) * z) hWl
    rw [hk, one_mul] at hp
    show U1 d t θ ((s : ℂ) * (z + l)) / θ ((s : ℂ) * (z + l)) = U1 d t θ ((s : ℂ) * z) / θ ((s : ℂ) * z)
    rw [mul_add]
    by_cases hz0 : θ ((s : ℂ) * z) = 0
    · rw [hz0, (zero_iff_of_fixed hWl _).2 hz0, div_zero, div_zero]
    · have hz1 : θ ((s : ℂ) * z + (s : ℂ) * l) ≠ 0 := fun h => hz0 ((zero_iff_of_fixed hWl _).1 h)
      rw [div_eq_div_iff hz1 hz0]
      exact hp
  have hA0 : AnalyticAt ℂ φ 0 := han 0 (by rw [mul_zero, h0]; exact one_ne_zero)
  have hpole : ∀ p r, PrimeTo d q r → ¬ InOK d (r - 1 / 2) → θ ((s : ℂ) * p + r) = 0 → ¬ M.Small p := by
    intro p r hr hr2 hθ0 hsmall
    exact hr2 (hsm p s r (inOK_nat d s) (by exact_mod_cast hs.ne') hr (hz _ hθ0) hsmall).2
  refine ⟨hE, hA0, han, hpole, GlobalTheory.T.cpSeriesCoeffBounded_taylor_elliptic_of_poles q M _ φ hch hE hA0 ?_⟩
  intro p hp
  have hθp : θ ((s : ℂ) * p) = 0 := by
    by_contra hne
    exact absurd hp (not_lt.mpr (han p hne).meromorphicOrderAt_nonneg)
  exact hpole p 0 ⟨1, one_pos, Nat.coprime_one_left q, ⟨0, 0, by simp⟩⟩ (not_inOK_neg_half d hd.pos) (by rw [add_zero]; exact hθp)

end GlobalTheory.MomOne.ScaledQuot
end

section

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.GoodDepth NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.goodPlaceDepthBound_proof : NuGoodSt := by
  first | exact @GlobalTheory.GoodDepth.nuGood | exact GlobalTheory.GoodDepth.nuGood | (intros; apply GlobalTheory.GoodDepth.nuGood <;> assumption)
end
