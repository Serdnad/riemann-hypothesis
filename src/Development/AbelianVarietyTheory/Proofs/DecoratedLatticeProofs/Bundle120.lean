module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle178
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.AlternatingFormStandardHermitian
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.IsSemiChar
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralDensEqZero
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.SharpRestriction.Bundle001
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RecHeightSWith
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Formalism.LocalRingCardinality.Bundle002
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsDiscriminantTwelfthRootOfIdealLatticeIffDelta1
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.HalfTmul

theorem exists_prime_to_dvd_away {R : Type} [CommRing R] [IsDedekindDomain R] (SS : Finset (HeightOneSpectrum R))
    (m : R) (hm : m ≠ 0) : ∃ t : R, t ≠ 0 ∧ (∀ Q ∈ SS, t ∉ Q.asIdeal) ∧
      ∀ Q : HeightOneSpectrum R, Q ∉ SS → ∃ u : R, u ∉ Q.asIdeal ∧ ∃ w : R, u * t = m * w := by
  classical
  have hI : Ideal.span {m} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hm
  have hfac : ∀ Q : HeightOneSpectrum R, ∃ n : ℕ, ∃ J : Ideal R, ¬ Q.asIdeal ∣ J ∧ Ideal.span {m} = Q.asIdeal ^ n * J :=
    fun Q => WfDvdMonoid.max_power_factor hI Q.prime.irreducible
  choose n J hJ using hfac
  have hT := Ideal.finite_factors hI
  obtain ⟨t0, ht0⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := SS ∪ hT.toFinset) (fun Q => Q.asIdeal)
    (fun Q => if Q ∈ SS then 1 else n Q) (fun Q _ => Q.prime) (fun Q _ Q' _ h e => h (HeightOneSpectrum.ext e))
    (fun Q => if (Q : HeightOneSpectrum R) ∈ SS then 1 else 0)
  have hone : ∀ Q : HeightOneSpectrum R, (1 : R) ∉ Q.asIdeal := fun Q h1 =>
    Q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  have hSS : ∀ Q ∈ SS, t0 ∉ Q.asIdeal := by
    intro Q hQ hmem
    have h := ht0 Q (Finset.mem_union_left _ hQ)
    simp only [if_pos hQ, pow_one] at h
    exact hone Q (by simpa using Q.asIdeal.sub_mem hmem h)
  have hgood : ∀ Q : HeightOneSpectrum R, Q ∉ SS → ∃ u : R, u ∉ Q.asIdeal ∧ ∃ w : R, u * t0 = m * w := by
    intro Q hQ
    by_cases hQT : Q.asIdeal ∣ Ideal.span {m}
    · have h := ht0 Q (Finset.mem_union_right _ (hT.mem_toFinset.2 hQT))
      simp only [if_neg hQ, sub_zero] at h
      obtain ⟨hnd, hEq⟩ := hJ Q
      rw [Ideal.dvd_iff_le] at hnd
      obtain ⟨u, huJ, huQ⟩ := SetLike.not_le_iff_exists.1 hnd
      refine ⟨u, huQ, ?_⟩
      have hmem : t0 * u ∈ Ideal.span {m} := by
        rw [hEq]; exact Ideal.mul_mem_mul h huJ
      obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.1 hmem
      exact ⟨w, by rw [mul_comm u, hw]⟩
    · refine ⟨m, ?_, t0, rfl⟩
      intro hmem
      exact hQT (Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hmem))
  by_cases h0 : t0 = 0
  · refine ⟨m, hm, ?_, fun Q _ => ⟨1, hone Q, 1, by ring⟩⟩
    intro Q hQ
    exact absurd (h0 ▸ Q.asIdeal.zero_mem) (hSS Q hQ)
  · exact ⟨t0, h0, hSS, hgood⟩

theorem tmul_mem_of {E : Type} [Field E] [NumberField E] [StarRing E] {W : Type} [AddCommGroup W] [Module E W]
    [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W] (M : Submodule (𝓞 E) W) (SS : Finset (HeightOneSpectrum (𝓞 E)))
    (c : ℕ) (hc : 0 < c) (y : W) (hy : y ∈ twist₂ M c (expS SS)) (t : 𝓞 E)
    (ht : ∀ Q : HeightOneSpectrum (𝓞 E), Q ∉ SS → ∃ u : 𝓞 E, u ∉ Q.asIdeal ∧ ∃ w : 𝓞 E, u * t = (c : 𝓞 E) ^ 2 * w) :
    ((t : E) * (c : E)⁻¹) • y ∈ M := by
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  have hcast : ∀ (r : 𝓞 E) (z : W), (r : E) • z = r • z := fun r z => IsScalarTower.algebraMap_smul E r z
  have hcy : (c : E) • y ∈ M := by
    have h := (GlobalTheory.CommonReps.mem_twO_zero M c _).1 (GlobalTheory.CommonReps.natsmul_mem_twO M c _ _ (fun Q => by
      rcases expS_cases SS Q with h | h | h <;> rw [h] <;> norm_num) hy)
    rwa [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E] at h
  apply Formalism.L2.Ker.mem_of_forall_locP M
  intro Q
  by_cases hQ : Q ∈ SS
  · have h1 := (Formalism.L2.Ker.mem_twO M c _ y).1 hy Q
    simp only [expS, if_pos hQ, zpow_one] at h1
    obtain ⟨s, hs, hsy⟩ := h1
    refine ⟨s, hs, ?_⟩
    have e : s • (((t : E) * (c : E)⁻¹) • y) = t • (s • ((c : E)⁻¹ • y)) := by
      rw [← hcast s, ← hcast t, ← hcast s]
      simp only [smul_smul]
      congr 1; ring
    rw [e]; exact M.smul_mem t hsy
  · obtain ⟨u, hu, w, huw⟩ := ht Q hQ
    refine ⟨u, hu, ?_⟩
    have huwE : (u : E) * (t : E) = (c : E) ^ 2 * (w : E) := by
      have := congrArg (fun r : 𝓞 E => (r : E)) huw
      simpa using this
    have e : u • (((t : E) * (c : E)⁻¹) • y) = w • ((c : E) • y) := by
      rw [← hcast u, ← hcast w]
      simp only [smul_smul]
      congr 1
      field_simp
      linear_combination huwE
    rw [e]; exact M.smul_mem w hcy

theorem exists_tmul_mem_perO : ∀ (D : D7) (a b : ℕ) (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (c : ℕ), 0 < c → ∀ y ∈ halfBO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, ∃ t : 𝓞 D.host.E, t ≠ 0 ∧ (∀ Q ∈ SS, t ∉ Q.asIdeal) ∧ ((t : D.host.E) * (c : D.host.E)⁻¹) • y ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' := by
  intro D a b N N' SS c hc y hy
  obtain ⟨t, ht0, hSS, hgood⟩ := exists_prime_to_dvd_away SS ((c : 𝓞 D.host.E) ^ 2)
    (pow_ne_zero _ (by exact_mod_cast hc.ne'))
  exact ⟨t, ht0, hSS, tmul_mem_of _ SS c hc y hy t hgood⟩

end GlobalTheory.HalfTmul
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfBCMul

theorem cmul_mem_perO_of_mem_halfBO : ∀ (D : D7) (a b : ℕ) (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (c : ℕ), 0 < c → ∀ y ∈ halfBO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, (c : D.host.E) • y ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' := by
  intro D a b N N' SS c hc y hy
  have h1 := GlobalTheory.CommonReps.natsmul_mem_twO _ c (expS SS) (fun _ => 0) (fun Q => by
    unfold expS; split_ifs <;> omega) hy
  rw [GlobalTheory.CommonReps.mem_twO_zero] at h1
  have e : ((c : 𝓞 D.host.E) • y) = (c : D.host.E) • y := by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  rwa [e] at h1

end GlobalTheory.HalfBCMul
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OffDen

theorem exists_den_avoid : ∀ (E : Type) [Field E] [NumberField E] (a b : ℕ) (M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b)) (G : HeightOneSpectrum (𝓞 E) → Prop) (c : ℕ), 0 < c → ∀ x : Formalism.L2.Col.HomE E a b, (c : E) • x ∈ M → (∀ Q : HeightOneSpectrum (𝓞 E), ¬ G Q → x ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M) → ∃ d : 𝓞 E, d ≠ 0 ∧ (d : E) • x ∈ M ∧ ∀ Q : HeightOneSpectrum (𝓞 E), (c : 𝓞 E) ∈ Q.asIdeal → d ∈ Q.asIdeal → G Q := by
  intro E _ _ a b M G c hc x hcx hloc
  classical
  have hsm : ∀ d : 𝓞 E, (d : E) • x = d • x := fun d => by
    rw [← algebraMap_smul E d x]
  set J : Ideal (𝓞 E) := M.comap (LinearMap.toSpanSingleton (𝓞 E) _ x) with hJ
  have memJ : ∀ d : 𝓞 E, d ∈ J ↔ d • x ∈ M := fun d => by simp [hJ]
  have hc0 : (c : 𝓞 E) ≠ 0 := by exact_mod_cast hc.ne'
  have hcx' : (c : 𝓞 E) • x ∈ M := by
    have hcE : ((c : 𝓞 E) : E) = (c : E) := by simp
    rw [← hsm, hcE]; exact hcx
  have hfin : {Q : HeightOneSpectrum (𝓞 E) | (c : 𝓞 E) ∈ Q.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {(c : 𝓞 E)}) (by simpa using hc0)).subset ?_
    intro Q hQ
    exact Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hQ)
  set S : Set (HeightOneSpectrum (𝓞 E)) := {Q | (c : 𝓞 E) ∈ Q.asIdeal ∧ ¬ G Q} with hS
  have hSfin : S.Finite := hfin.subset fun Q hQ => hQ.1
  have hnot : ¬ ((J : Set (𝓞 E)) ⊆ ⋃ Q ∈ S, (Q.asIdeal : Set (𝓞 E))) := by
    intro hsub
    rcases S.eq_empty_or_nonempty with h0 | ⟨Q₀, _⟩
    · have hm := hsub ((memJ _).2 hcx')
      simp [h0] at hm
    obtain ⟨Q, hQ, hle⟩ := (Ideal.subset_union_prime_finite hSfin (f := fun Q => Q.asIdeal) Q₀ Q₀
      (fun Q _ _ _ => Q.isPrime)).1 hsub
    obtain ⟨s, hs, hsx⟩ := hloc Q hQ.2
    exact hs (hle ((memJ s).2 hsx))
  obtain ⟨d, hdJ, hdS⟩ := Set.not_subset.1 hnot
  simp only [Set.mem_iUnion, SetLike.mem_coe, not_exists] at hdS
  have key : ∀ Q : HeightOneSpectrum (𝓞 E), (c : 𝓞 E) ∈ Q.asIdeal → d ∈ Q.asIdeal → G Q :=
    fun Q hcQ hdQ => by_contra fun hG => hdS Q ⟨hcQ, hG⟩ hdQ
  by_cases hd0 : d = 0
  · refine ⟨c, hc0, ?_, fun Q hcQ _ => key Q hcQ (hd0 ▸ Q.asIdeal.zero_mem)⟩
    rw [hsm]; exact hcx'
  · exact ⟨d, hd0, by rw [hsm]; exact (memJ d).1 hdJ, key⟩

end GlobalTheory.OffDen
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaInter

open Formalism.L2.Th1.H

theorem reps_bijective {V : Type} [AddCommGroup V] (A₁ A₂ : AddSubgroup V) {ι : Type} (s : Finset ι) (z : ι → V)
    (hz : ∀ i ∈ s, z i ∈ A₂) (hinj : ∀ i ∈ s, ∀ j ∈ s, z i - z j ∈ A₁ → i = j)
    (hsurj : ∀ y ∈ A₂, ∃ i ∈ s, y - z i ∈ A₁) :
    Function.Bijective (fun i : s => ((⟨z i, hz i i.2⟩ : A₂) : A₂ ⧸ A₁.addSubgroupOf A₂)) := by
  constructor
  · rintro ⟨i, hi⟩ ⟨j, hj⟩ h
    simp only at h
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h
    have : z j - z i ∈ A₁ := by simpa [neg_add_eq_sub] using h
    exact Subtype.ext (hinj j hj i hi this).symm
  · intro c
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientAddGroup.mk_surjective c
    obtain ⟨i, hi, hyi⟩ := hsurj y hy
    refine ⟨⟨i, hi⟩, ?_⟩
    simp only
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    simpa [neg_add_eq_sub] using hyi

theorem inter_eq_sum_reps : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (H : Formalism.L2.Th1.H.Sesq V) (α : V → ℂ)
    (A₁ A₂ : AddSubgroup V), Formalism.L2.Th1.H.IsHerm H → Formalism.L2.Th1.H.IsSelfDual H A₂ →
    Formalism.L2.Th1.H.IsSemiChar H A₁ α → Formalism.L2.Th1.H.IsSemiChar H A₂ α → ∀ {ι : Type} (s : Finset ι) (z : ι → V),
    (∀ i ∈ s, z i ∈ A₂) → (∀ i ∈ s, ∀ j ∈ s, z i - z j ∈ A₁ → i = j) → (∀ y ∈ A₂, ∃ i ∈ s, y - z i ∈ A₁) →
    ∀ F ∈ Formalism.L2.Th1.H.fixedBy H α A₁, ∀ w, Formalism.L2.Th1.H.inter H α A₁ A₂ F w =
      ((Real.sqrt (s.card : ℝ) : ℝ) : ℂ)⁻¹ * ∑ i ∈ s, α (z i) * Formalism.L2.Th1.H.opU H (z i) F w := by
  intro V _ _ H α A₁ A₂ hH hd₂ hs₁ hs₂ ι s z hz hinj hsurj F hF w
  classical
  have hφ := reps_bijective A₁ A₂ s z hz hinj hsurj
  have : Finite (A₂ ⧸ A₁.addSubgroupOf A₂) := Finite.of_surjective _ hφ.2
  have := Fintype.ofFinite (A₂ ⧸ A₁.addSubgroupOf A₂)
  have hcard : Fintype.card (A₂ ⧸ A₁.addSubgroupOf A₂) = s.card := by
    rw [← Fintype.card_of_bijective hφ, Fintype.card_coe]
  have hinv : ∀ (a : A₂), ∀ t ∈ A₁.addSubgroupOf A₂,
      α ((a + t : A₂) : V) * opU H ((a + t : A₂) : V) F w = α (a : V) * opU H (a : V) F w := by
    intro a t ht
    rw [AddSubgroup.coe_add, alpha_opU_add hH hd₂ hs₂ a.2 t.2,
      opU_of_fixed hs₁ hF (AddSubgroup.mem_addSubgroupOf.1 ht), opU_mul, ← mul_assoc (α t), alpha_sq hs₂ t.2, one_mul]
  rw [congrFun (inter_eq (H := H) (α := α) A₁ A₂ F) w, hcard]
  congr 1
  rw [← Finset.sum_coe_sort s]
  refine (Fintype.sum_bijective _ hφ _ _ fun i => ?_).symm
  have ht : -(⟨z i, hz i i.2⟩ : A₂) + Quotient.out (((⟨z i, hz i i.2⟩ : A₂) : A₂ ⧸ A₁.addSubgroupOf A₂)) ∈
      A₁.addSubgroupOf A₂ := by
    rw [← QuotientAddGroup.eq]
    exact (QuotientAddGroup.out_eq' _).symm
  have := hinv ⟨z i, hz i i.2⟩ _ ht
  rw [add_neg_cancel_left] at this
  exact this.symm

end GlobalTheory.ThetaInter
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2 GlobalTheory.CoreHt
open GlobalTheory.ColumnNormCompare (numDatumOfParameters codeRec plRec)
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.CoreHt.RowsOfDesign

theorem two_le_of_log_pos' (n : ℕ) (h : 0 < Real.log (n : ℝ)) : 2 ≤ n := by
  by_contra hn
  have h1 : n = 0 ∨ n = 1 := by omega
  rcases h1 with rfl | rfl <;> simp at h

theorem two_le_rdE' (D : D7) (hq : 2 ≤ D.host.q) (hd : 2 ≤ D.host.d) : 2 ≤ D.host.rdE := by
  have h := (factRd D.R D.host).2.2
  have hf : (2 : ℝ) ≤ D.R.f := by
    have := D.host.four_le_n'
    have h2 : D.R.f = 2 * D.R.n := rfl
    exact_mod_cast (by omega : 2 ≤ D.R.f)
  have h0 : 0 ≤ D.host.rdE := by unfold Host.rdE; positivity
  nlinarith

theorem rows_of_design : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L), Formalism.MainNotions.SizesAt L → Real.log (4 * L.sc.x) ≤ L.sc.L →
    DelNat D → ThickUp L → HtRowsS L P.CYL := by
  intro D L P hS hx4 hDN hTU
  obtain ⟨-, -, -, -, hT, hCond, hQD, -, hLa, hRho, hBot, -, -, hEta, hNodes, -, hDel, -⟩ := hS
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have hL1 : 1 ≤ L.sc.L := by unfold Scale.L; exact Real.one_le_rpow hx1.le L.sc.eps_pos.le
  have hq2 : 2 ≤ D.host.q := two_le_of_log_pos' _ (lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hQD.1)
  have hd2 : 2 ≤ D.host.d := two_le_of_log_pos' _ (lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hQD.2.2.2.1)
  have hq' : (2 : ℝ) ≤ D.host.q := by exact_mod_cast hq2
  have hd' : (2 : ℝ) ≤ D.host.d := by exact_mod_cast hd2
  have hrd2 := two_le_rdE' D hq2 hd2
  have hn1 : (1 : ℝ) ≤ D.R.n := by
    have : 1 ≤ D.R.n := by have := D.host.four_le_n'; omega
    exact_mod_cast this
  have ht1 : (1 : ℝ) ≤ D.R.t := hT.1
  have hm1 : (1 : ℝ) ≤ D.R.m := by
    have : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
    exact_mod_cast this
  have hk0 : (0 : ℝ) < D.R.k := by
    have : 0 < D.R.k := by have := D.R.m_add_three_le_k; omega
    exact_mod_cast this
  have hb1 : 1 ≤ L.sc.b := by unfold Scale.b; exact Real.one_le_exp (by linarith)
  refine ⟨⟨P⟩, ⟨?_, hQD.2.2.2.2.2.1, hx4⟩, ?_, ⟨?_, hEta.1, hEta.2.2.2.2.1, hDel.2.2.2.1, ?_⟩, hDN, hTU⟩
  ·
    have hqd : (1 : ℝ) ≤ (D.host.q : ℝ) * D.host.d := by nlinarith
    have hs : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ (D.host.q : ℝ) * D.host.d :=
      Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
    have hc : D.host.rdE ≤ Formalism.MainNotions.szCond L := by
      refine hQD.2.2.2.2.2.2.2.trans ?_
      unfold Formalism.MainNotions.szCond
      have : (D.host.QS : ℝ) / 2 * Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤
          (D.host.QS : ℝ) / 2 * ((D.host.q : ℝ) * D.host.d) := mul_le_mul_of_nonneg_left hs (by positivity)
      have h0 : 0 ≤ (D.host.QS : ℝ) * ((D.host.q : ℝ) * D.host.d) := by positivity
      nlinarith
    have hc1 : 1 ≤ Formalism.MainNotions.szCond L := by linarith
    have h36 : Formalism.MainNotions.szCond L ≤ Formalism.MainNotions.szCond L ^ 36 := le_self_pow₀ hc1 (by norm_num)
    have h150 : Formalism.MainNotions.szCond L ^ 36 ≤ Formalism.MainNotions.szCond L ^ 36 * (D.R.t : ℝ) ^ 150 :=
      le_mul_of_one_le_right (by positivity) (one_le_pow₀ ht1)
    have hsb : Real.sqrt L.sc.b ≤ L.sc.b := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
    have hfin : D.host.rdE ≤ L.sc.b := hc.trans (h36.trans (h150.trans (hCond.trans hsb)))
    have := Real.log_le_log (by linarith) hfin
    rwa [show Real.log L.sc.b = L.sc.L by unfold Scale.b; exact Real.log_exp _] at this
  · intro i
    obtain ⟨Y, hY1, -, hY3, hY4⟩ := P.g_Y
    have hY0 : 0 < Y := lt_of_lt_of_le (by positivity) hY1
    have hg0 : (0 : ℝ) < D.host.g i := lt_of_lt_of_le hY0 (hY4 i).1
    have h1 := Real.log_le_log hg0 (hY4 i).2
    rw [Real.log_mul (by norm_num) hY0.ne'] at h1
    have h2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
    linarith
  · have h1 := hNodes.2.2.2.1
    have h2 : L.etaSz / D.R.m ≤ L.etaSz := div_le_self L.etaSz_pos.le hm1
    have h3 : (0 : ℝ) ≤ D.R.t := by linarith
    linarith
  · intro t
    have h1 := hBot t
    have hLa0 : 0 ≤ L.LaG := le_trans (Real.rpow_pos_of_pos hx0 _).le hLa.1
    have h2 : 0 ≤ L.sc.x ^ Formalism.MainNotions.szTh L * Real.log L.sc.x * L.LaG / D.R.k :=
      div_nonneg (mul_nonneg (mul_nonneg (Real.rpow_pos_of_pos hx0 _).le (Real.log_nonneg hx1.le)) hLa0) hk0.le
    have h3 : L.sc.x ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1.le (by norm_num)
    have hb' : 0 ≤ L.sc.b' := by
      unfold Scale.b' Scale.a Scale.X' Scale.b
      positivity
    have hR : 4 * Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k +
        L.sc.x ^ Formalism.MainNotions.szTh L * Real.log L.sc.x * L.LaG / D.R.k ≤ L.sc.x ^ (-2 : ℝ) := hRho
    have h4 : Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k ≤ 1 := by
      have : 4 * Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k =
          4 * (Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) := by ring
      have h0 : 0 ≤ Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k := by
        unfold Formalism.MainNotions.szNst Scale.delta1
        have := Real.rpow_pos_of_pos hx0 (-(L.sc.eps / 8))
        have := Real.rpow_pos_of_pos hx0 L.sc.eps
        positivity
      linarith
    have h5 : Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k =
        Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k * L.sc.b' := by ring
    rw [h5] at h1
    nlinarith

end GlobalTheory.CoreHt.RowsOfDesign
end
