module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle017
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle009
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.NumberTheory.LSeries.Basic

@[expose] public section

section

noncomputable section

namespace PI.VolStabS

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW

def ResAA : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J), SWa1 F E σ M J → Formalism.L2.SG.Pf.NcWeil.StabilizerFirstChernCompatibility F E σ M J →
    ∀ (a : ℕ), 1 ≤ a → 2 * a < M → ∀ (X0 : Fin a → Fin M → E)
    (hT : ∀ i j, σ (gramE σ J X0 j i) = gramE σ J X0 i j), (gramE σ J X0).det ≠ 0 →
    ∀ ψ, IsCharAF F ψ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E),
    ∀ᶠ v in cofinite,
    ∀ μv, SdW F E σ M J (Fv F v) (psiV F ψ v) a μv →
    ∀ νv, SdHerm F E σ (Fv F v) (psiV F ψ v) a νv →
    ∃ (L : AddSubgroup (Fin a → Fin M → Fv F v ⊗[F] E))
      (Λ : ℕ → AddSubgroup (Fin a → Fin M → Fv F v ⊗[F] E))
      (H : ℕ → AddSubgroup (HermR (Fv F v) σ a)),
      (L : Set (Fin a → Fin M → Fv F v ⊗[F] E)) = latV b v ∧
      IsOpen (L : Set (Fin a → Fin M → Fv F v ⊗[F] E)) ∧
      IsCompact (L : Set (Fin a → Fin M → Fv F v ⊗[F] E)) ∧ Λ 0 ≤ L ∧
      (∀ n, IsOpen (Λ n : Set (Fin a → Fin M → Fv F v ⊗[F] E))) ∧
      (∀ n, IsCompact (Λ n : Set (Fin a → Fin M → Fv F v ⊗[F] E))) ∧ Antitone Λ ∧
      (∀ n, IsOpen (H n : Set (HermR (Fv F v) σ a))) ∧
      (∀ n, IsCompact (H n : Set (HermR (Fv F v) σ a))) ∧
      (∀ N' ∈ 𝓝 (0 : HermR (Fv F v) σ a), ∃ n, (H n : Set (HermR (Fv F v) σ a)) ⊆ N') ∧
      (∀ y ∈ L, gramH (Fv F v) σ (sigma_invol σ hCM.2.2.2) J hJ.1 y - hermOf (Fv F v) σ (gramE σ J X0) hT ∈ H 0 →
        ∃ D : (Fin a → Fin M → Fv F v ⊗[F] E) →+ HermR (Fv F v) σ a,
          (∀ n, (Λ n).map D = H n) ∧ ∀ n, ∀ Z ∈ Λ 0, ∀ W ∈ Λ n,
            gramH (Fv F v) σ (sigma_invol σ hCM.2.2.2) J hJ.1 (y + Z + W) - gramH (Fv F v) σ (sigma_invol σ hCM.2.2.2) J hJ.1 (y + Z) - D W ∈
              H (n + 1)) ∧
      ∃ (k K : Type) (_ : Field k) (_ : Finite k) (_ : CommRing K) (_ : Algebra k K)
        (σ' : K ≃ₐ[k] K) (J' : Matrix (Fin M) (Fin M) K) (T' : Matrix (Fin a) (Fin a) K),
        IsQuadInv k K σ' ∧ (2 : k) ≠ 0 ∧ (∀ i j, σ' (J' j i) = J' i j) ∧ IsUnit J'.det ∧
        (∀ i j, σ' (T' j i) = T' i j) ∧ IsUnit T'.det ∧ (Nat.card k : ℝ) = qV v ∧
        ((μv ((L : Set (Fin a → Fin M → Fv F v ⊗[F] E)) ∩
            gramH (Fv F v) σ (sigma_invol σ hCM.2.2.2) J hJ.1 ⁻¹' {z | z - hermOf (Fv F v) σ (gramE σ J X0) hT ∈ H 0})) /
            νv (H 0)).toReal =
          (Nat.card {X : Fin a → Fin M → K // ffGram (σ' : K →+* K) J' X = T'} : ℝ) /
            (Nat.card k : ℝ) ^ (2 * M * a - a ^ 2)

theorem densAA_of (hFL : FibLat) (hFF : FFCount) (hR : ResAA) : DensAA := by
  intro F E _ _ _ _ _ σ hCM M J hJ hSa hSc a ha1 ha2 X0 hT hdet ψ hψ d b
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hσ : ∀ x, σ (σ x) = x := sigma_invol σ hCM.2.2.2
  obtain ⟨C, hC⟩ := hFF M
  refine ⟨C, ?_⟩
  filter_upwards [hR F E σ hCM M J hJ hSa hSc a ha1 ha2 X0 hT hdet ψ hψ d b] with v hv
  intro μv hμv νv hνv fibV hfib
  have := secondCountable_Fv F v
  have := locallyCompact_Fv F v
  have := hμv.1
  have := hνv.1
  obtain ⟨L, Λ, H, hL, hLo, hLc, hΛL, hΛo, hΛc, hΛa, hHo, hHc, hHb, hyp, k, K, _, _, _, _, σ', J',
    T', hQ, h2, hJ', hJu, hT', hTu, hq, hcnt⟩ := hv μv hμv νv hνv
  have : SecondCountableTopology (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin a → Fin a → Fv F v ⊗[F] E))
  have : T2Space (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (T2Space (Fin a → Fin a → Fv F v ⊗[F] E))
  have : LocallyCompactSpace (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin a → Fin a → Fv F v ⊗[F] E))
  have : SecondCountableTopology (HermR (Fv F v) σ a) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have hN := isOpen_unitHerm (Fv F v) (isOpen_units_Fv F v) σ a
  have e := hFL _ _ _ μv νv hμv.1 hνv.1 (gramR (Fv F v) σ J) Subtype.val Subtype.val_injective
    (gramH (Fv F v) σ (sigma_invol σ hCM.2.2.2) J hJ.1) (continuous_gramH (Fv F v) σ (sigma_invol σ hCM.2.2.2) J hJ.1) (fun _ => rfl) _ _ fibV hfib
    (hermOf (Fv F v) σ (gramE σ J X0) hT) Filter.univ_mem _
    (hN.mem_nhds (isUnit_det_hermOf (Fv F v) σ _ hT hdet))
    (fun X hX => linIndep_of_isUnit_det (Fv F v) σ J X hX) L hLo hLc Λ H hΛL hΛo hΛc hΛa hHo hHc
    hHb hyp
  rw [hcnt, hL] at e
  rw [e]
  have hb := hC k K σ' hQ h2 J' hJ' hJu a (by omega) T' hT' hTu
  rw [← hq]
  have : ((((Nat.card {X : Fin a → Fin M → K // ffGram (σ' : K →+* K) J' X = T'} : ℝ) /
      (Nat.card k : ℝ) ^ (2 * M * a - a ^ 2) : ℝ) : ℂ) - 1) =
      (((Nat.card {X : Fin a → Fin M → K // ffGram (σ' : K →+* K) J' X = T'} : ℝ) /
      (Nat.card k : ℝ) ^ (2 * M * a - a ^ 2) - 1 : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.norm_real, Real.norm_eq_abs]
  exact hb

end PI.VolStabS
end
end

section

noncomputable section

namespace PI.VolStabS

open NumberField IsDedekindDomain Filter Asymptotics
open scoped nonZeroDivisors

namespace LocalCountingSum

variable (K : Type) [Field K] [NumberField K]

def cnt (n : ℕ) : ℝ := (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ)

theorem sum_cnt (n : ℕ) : ∑ k ∈ Finset.Icc 1 n, cnt K k =
    (Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ n} : ℝ) := by
  induction n with
  | zero =>
    have hE : IsEmpty {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ 0} := by
      constructor
      rintro ⟨I, hI⟩
      have h0 : Ideal.absNorm (I : Ideal (𝓞 K)) = 0 := Nat.le_zero.1 hI
      rw [Ideal.absNorm_eq_zero_iff] at h0
      exact (mem_nonZeroDivisors_iff_ne_zero.1 I.2) (by rw [h0]; rfl)
    rw [Nat.card_of_isEmpty]
    simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    haveI : Finite {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ n} := (Ideal.finite_setOf_absNorm_le₀ (S := 𝓞 K) n).to_subtype
    haveI : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = n + 1} :=
      (Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) (n + 1)).to_subtype
    have hnz : ∀ I : Ideal (𝓞 K), Ideal.absNorm I = n + 1 → I ∈ (Ideal (𝓞 K))⁰ := by
      intro I hI
      refine mem_nonZeroDivisors_iff_ne_zero.2 (fun h => ?_)
      rw [h] at hI
      simp at hI
    let e : {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ n + 1} ≃ {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ n} ⊕ {I : Ideal (𝓞 K) // Ideal.absNorm I = n + 1} :=
      { toFun := fun x => if h : Ideal.absNorm (x.1 : Ideal (𝓞 K)) ≤ n then Sum.inl ⟨x.1, h⟩
          else Sum.inr ⟨x.1.1, by have := x.2; omega⟩
        invFun := fun y => match y with
          | Sum.inl z => ⟨z.1, Nat.le_succ_of_le z.2⟩
          | Sum.inr z => ⟨⟨z.1, hnz z.1 z.2⟩, z.2.le⟩
        left_inv := by
          intro x
          by_cases h : Ideal.absNorm (x.1 : Ideal (𝓞 K)) ≤ n
          · simp only [dif_pos h]
          · simp only [dif_neg h]
        right_inv := by
          intro y
          rcases y with z | z
          · simp only [dif_pos z.2]
          · have hz : ¬ Ideal.absNorm z.1 ≤ n := by have := z.2; omega
            simp only [dif_neg hz] }
    rw [Nat.card_congr e, Nat.card_sum]
    unfold cnt
    push_cast
    ring

theorem sum_cnt_bigO :
    (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, cnt K k) =O[atTop] fun n ↦ (n : ℝ) ^ (1 : ℝ) := by
  have h2 := (NumberField.Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop
  have hc : ∀ n : ℕ, (Nat.card {I : (Ideal (𝓞 K))⁰ // (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ (n : ℝ)} : ℝ) =
      (Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ n} : ℝ) := by
    intro n
    congr 1
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun I => Nat.cast_le))
  simp only [Real.rpow_one]
  obtain ⟨L, hL⟩ : ∃ L, Tendsto ((fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, cnt K k) / fun n : ℕ => (n : ℝ))
      atTop (nhds L) :=
    ⟨_, h2.congr (fun n => by simp only [Function.comp_apply, Pi.div_apply, hc n, sum_cnt K n])⟩
  exact Asymptotics.isBigO_of_div_tendsto_nhds
    (Filter.eventually_atTop.2 ⟨1, fun n hn h0 => absurd h0 (by positivity)⟩) L hL

theorem cnt_summable : Summable fun n : ℕ ↦ cnt K n / (n : ℝ) ^ 2 := by
  have h := LSeriesSummable_of_sum_norm_bigO_and_nonneg (f := cnt K) (r := 1) (s := 2) (sum_cnt_bigO K)
    (fun n => by unfold cnt; positivity) zero_le_one (by norm_num)
  unfold LSeriesSummable at h
  have e : LSeries.term (fun n => ((cnt K n : ℝ) : ℂ)) 2 = fun n => ((cnt K n / (n : ℝ) ^ 2 : ℝ) : ℂ) := by
    funext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [LSeries.term]
    · rw [LSeries.term_of_ne_zero hn.ne']
      push_cast
      congr 1
      exact_mod_cast Complex.cpow_natCast (n : ℂ) 2
  rw [e] at h
  exact Complex.summable_ofReal.1 h

end LocalCountingSum

theorem qV_eq {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    qV v = (Ideal.absNorm v.asIdeal : ℝ) := by
  unfold qV
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem qvSum_holds : QvSum := by
  intro F _ _
  haveI hfin : ∀ n : ℕ, Finite {I : Ideal (𝓞 F) // Ideal.absNorm I = n} :=
    fun n => (Ideal.finite_setOf_absNorm_eq (S := 𝓞 F) n).to_subtype
  let f : Ideal (𝓞 F) → ℝ := fun I => ((Ideal.absNorm I : ℝ))⁻¹ ^ 2
  have hf0 : ∀ I, 0 ≤ f I := fun I => by positivity
  have hsig : Summable (fun x : Σ n : ℕ, {I : Ideal (𝓞 F) // Ideal.absNorm I = n} => f x.2.1) := by
    rw [summable_sigma_of_nonneg (fun x => hf0 _)]
    refine ⟨fun n => Summable.of_finite, ?_⟩
    have e2 : (fun n : ℕ => ∑' I : {I : Ideal (𝓞 F) // Ideal.absNorm I = n}, f I.1) =
        fun n => LocalCountingSum.cnt F n / (n : ℝ) ^ 2 := by
      funext n
      have hc : ∀ I : {I : Ideal (𝓞 F) // Ideal.absNorm I = n}, f I.1 = ((n : ℝ))⁻¹ ^ 2 := by
        intro I
        simp only [f, I.2]
      rw [tsum_congr hc, tsum_const, nsmul_eq_mul]
      unfold LocalCountingSum.cnt
      rw [inv_pow, div_eq_mul_inv]
    rw [e2]
    exact LocalCountingSum.cnt_summable F
  have hI : Summable f := (Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 F) => Ideal.absNorm I)).summable_iff.1 hsig
  have hinj : Function.Injective (fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal) :=
    fun v w h => HeightOneSpectrum.ext h
  refine (hI.comp_injective hinj).congr (fun v => ?_)
  simp only [Function.comp_apply, f, qV_eq]

end PI.VolStabS
end
end
