module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle579
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import GroundTheory.GlobalFields.TateThesis.AdelicCharLocal
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaDistributionHeisenbergInvariant
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle001
public import Formalism.ConjugateSelfDual.Bundle001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle594
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle087
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle088
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle110
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTopOfSpanImage
public import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle596
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle023
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.TraceConjugationCover

open scoped BigOperators

def trBound {l : ℕ} [Fact l.Prime] {a m : ℕ} (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l))) : ℝ :=
  ∑ k, ∑ x ∈ t k, ‖x.trace‖

theorem trBound_nonneg {l : ℕ} [Fact l.Prime] {a m : ℕ} (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l))) :
    0 ≤ trBound t :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem le_trBound {l : ℕ} [Fact l.Prime] {a m : ℕ} (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l)))
    (k : Fin m) {x : Matrix (Fin a) (Fin a) (Om l)} (hx : x ∈ t k) : ‖x.trace‖ ≤ trBound t := by
  unfold trBound
  refine le_trans ?_ (Finset.single_le_sum (f := fun k => ∑ x ∈ t k, ‖x.trace‖)
    (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ k))
  exact Finset.single_le_sum (f := fun x => ‖x.trace‖) (fun _ _ => norm_nonneg _) hx

theorem norm_trace_latL {l : ℕ} [Fact l.Prime] {a m : ℕ} (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l)))
    (M : ℕ) (y : Fin m → Matrix (Fin a) (Fin a) (Om l)) (hy : y ∈ latL t M) (k : Fin m) :
    ‖(y k).trace‖ ≤ ((l : ℝ)⁻¹) ^ M * trBound t := by
  have h0 : 0 ≤ ((l : ℝ)⁻¹) ^ M * trBound t := mul_nonneg (pow_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) _) (trBound_nonneg t)
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hx
    obtain ⟨z, hz, rfl⟩ := hj
    dsimp only
    by_cases hjk : k = j
    · subst hjk
      rw [Pi.single_eq_same, Matrix.trace_smul, smul_eq_mul, norm_mul, norm_pow, norm_l]
      exact mul_le_mul_of_nonneg_left (le_trBound t k hz) (pow_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) _)
    · rw [Pi.single_eq_of_ne hjk, Matrix.trace_zero, norm_zero]
      exact h0
  | zero => simpa using h0
  | add x y _ _ hx hy =>
    rw [Pi.add_apply, Matrix.trace_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
  | smul c x _ hx =>
    rw [Pi.smul_apply, Matrix.trace_smul, ← zOm_smul, smul_eq_mul, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_zOm_le c)).trans hx

end GlobalTheory.TraceConjugationCover

namespace GlobalTheory

theorem trace_estimate_latL : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (a : ℕ) (r : Γ →* GL (Fin a) (Om l)) (m : ℕ) (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l))) (c N n : ℕ) (cs : Fin m → Om l), n ≤ N → (∀ g, ‖trc r g - ∑ k, cs k * trc (ρs k) g‖ ≤ ((l : ℝ)⁻¹) ^ (N + c)) → ∃ M₁ : ℕ, ∀ M, M₁ ≤ M → ∀ (F : Γ →₀ ℤ_[l]) (y : Fin m → Matrix (Fin a) (Fin a) (Om l)), y ∈ GlobalTheory.TraceConjugationCover.latL t M → ‖(F.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))).trace - ∑ k, cs k * (((F.sum fun g c => zOm l c • GlobalTheory.TraceConjugationCover.tup ρs g) + y) k).trace‖ ≤ ((l : ℝ) ^ n)⁻¹ := by
  intro l _ Γ _ a r m ρs t c N n cs hnN hr
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := zero_lt_one.trans hl1
  set C : ℝ := TraceConjugationCover.trBound t * ∑ k, ‖cs k‖ with hC
  have hC0 : 0 ≤ C := mul_nonneg (TraceConjugationCover.trBound_nonneg t) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt C hl1
  refine ⟨n + K, fun M hM F y hy => ?_⟩
  have hinv : ((l : ℝ)⁻¹) ^ n = ((l : ℝ) ^ n)⁻¹ := inv_pow _ _
  have hle1 : (l : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hl1.le
  have hinv0 : (0 : ℝ) ≤ (l : ℝ)⁻¹ := inv_nonneg.2 hl0.le

  have hsplit : (F.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))).trace - ∑ k, cs k * (((F.sum fun g c => zOm l c • GlobalTheory.TraceConjugationCover.tup ρs g) + y) k).trace
      = (F.sum fun h c => zOm l c * (trc r h - ∑ k, cs k * trc (ρs k) h)) - ∑ k, cs k * (y k).trace := by
    simp only [Finsupp.sum, Pi.add_apply, Finset.sum_apply, Matrix.trace_add, Matrix.trace_sum, Pi.smul_apply,
      Matrix.trace_smul, smul_eq_mul, TraceConjugationCover.tup, trc, mul_add, Finset.sum_add_distrib, mul_sub, Finset.mul_sum]
    rw [Finset.sum_sub_distrib, Finset.sum_comm (s := (Finset.univ : Finset (Fin m)))]
    simp only [mul_left_comm (cs _)]
    ring
  rw [hsplit]
  have h1 : ‖F.sum fun h c => zOm l c * (trc r h - ∑ k, cs k * trc (ρs k) h)‖ ≤ ((l : ℝ) ^ n)⁻¹ := by
    rw [← hinv]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg hinv0 _) fun h _ => ?_
    rw [norm_mul]
    refine (mul_le_of_le_one_left (norm_nonneg _) (TraceConjugationCover.norm_zOm_le _)).trans ((hr h).trans ?_)
    exact pow_le_pow_of_le_one hinv0 hle1 (by omega)
  have h2 : ‖∑ k, cs k * (y k).trace‖ ≤ ((l : ℝ) ^ n)⁻¹ := by
    calc ‖∑ k, cs k * (y k).trace‖ ≤ ∑ k, ‖cs k‖ * (((l : ℝ)⁻¹) ^ M * TraceConjugationCover.trBound t) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (TraceConjugationCover.norm_trace_latL t M y hy k) (norm_nonneg _)
      _ = ((l : ℝ)⁻¹) ^ M * C := by rw [hC, ← Finset.sum_mul]; ring
      _ ≤ ((l : ℝ)⁻¹) ^ (n + K) * (l : ℝ) ^ K :=
          mul_le_mul (pow_le_pow_of_le_one hinv0 hle1 hM) hK.le hC0 (pow_nonneg hinv0 _)
      _ = ((l : ℝ) ^ n)⁻¹ := by
          rw [pow_add, inv_pow, inv_pow, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hl0.ne'), mul_one]
  rw [sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 ?_)
  rwa [norm_neg]

end GlobalTheory

end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.CovKer

theorem kerB : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (a : ℕ) (r : Γ →* GL (Fin a) (Om l)) (m : ℕ) (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (c N : ℕ) (cs : Fin m → Om l), (∀ (n : ℕ) (f : Γ →₀ ℤ_[l]), (∀ g, ‖((f.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) * ((r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))).trace‖ ≤ ((l : ℝ)⁻¹) ^ (n + c)) → ∃ f' : Γ →₀ ℤ_[l], (f.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) = (l : Om l) ^ n • (f'.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)))) → (∀ g, ‖trc r g - ∑ k, cs k * trc (ρs k) g‖ ≤ ((l : ℝ)⁻¹) ^ (N + c)) → ∀ G : Γ →₀ ℤ_[l], (G.sum fun g c => zOm l c • GlobalTheory.TraceConjugationCover.tup ρs g) = 0 → ∃ f' : Γ →₀ ℤ_[l], (G.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) = (l : Om l) ^ N • (f'.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) := by
  intro l _ Γ _ a r m ρs c N cs hdiv happ G hG
  apply hdiv N G
  intro g

  have hk : ∀ k, ∑ h ∈ G.support, zOm l (G h) * trc (ρs k) (h * g) = 0 := by
    intro k
    have h0 := congrFun hG k
    simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, GlobalTheory.TraceConjugationCover.tup, Pi.zero_apply] at h0
    have h1 := congrArg (fun M : Matrix (Fin a) (Fin a) (Om l) =>
      (M * ((ρs k g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))).trace) h0
    simp only [Finset.sum_mul, Matrix.trace_sum, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
      Matrix.zero_mul, Matrix.trace_zero] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun h _ => ?_
    simp [trc, map_mul, Units.val_mul]
  have htr : ((G.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) *
      ((r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))).trace =
      ∑ h ∈ G.support, zOm l (G h) * (trc r (h * g) - ∑ k, cs k * trc (ρs k) (h * g)) := by
    have e2 : ∑ h ∈ G.support, zOm l (G h) * (∑ k, cs k * trc (ρs k) (h * g)) = 0 := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun k _ => ?_
      have := congrArg (fun x => cs k * x) (hk k)
      simp only [mul_zero, Finset.mul_sum] at this
      rw [← this]
      refine Finset.sum_congr rfl fun h _ => by ring
    simp only [mul_sub, Finset.sum_sub_distrib, e2, sub_zero]
    simp only [Finsupp.sum, Finset.sum_mul, Matrix.trace_sum, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    refine Finset.sum_congr rfl fun h _ => ?_
    simp [trc, map_mul, Units.val_mul]
  rw [htr]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun h _ => ?_
  rw [norm_mul]
  calc ‖zOm l (G h)‖ * ‖trc r (h * g) - ∑ k, cs k * trc (ρs k) (h * g)‖
      ≤ 1 * ((l : ℝ)⁻¹) ^ (N + c) :=
        mul_le_mul (GlobalTheory.TraceConjugationCover.norm_zOm_le _) (happ (h * g)) (norm_nonneg _) zero_le_one
    _ = ((l : ℝ)⁻¹) ^ (N + c) := one_mul _

end GlobalTheory.CovKer
end

section

noncomputable section

open NumberField IsDedekindDomain Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep Formalism.UG

namespace GlobalTheory.StdCharConductor

variable (E : Type) [Field E] [NumberField E]

def psi : AddChar (Ad E) ℂ := Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar E)

theorem psi_apply (x : Ad E) : psi E x = (GroundTheory.Global.adelicChar E x : ℂ) := rfl

variable {E}

theorem psi_loc (w : HeightOneSpectrum (𝓞 E)) (y : w.adicCompletion E) :
    psi E (sFin E (sLoc E w y)) = (GroundTheory.Global.localAdelicChar E w y : ℂ) := by
  classical
  rw [psi_apply, GroundTheory.Global.localAdelicChar_apply]
  congr 2

theorem psi_loc_eq_one_iff (w : HeightOneSpectrum (𝓞 E)) (y : w.adicCompletion E) :
    psi E (sFin E (sLoc E w y)) = 1 ↔ GroundTheory.Global.localAdelicChar E w y = 1 := by
  rw [psi_loc]
  exact Circle.coe_eq_one

theorem exists_psi_loc_ne_one (w : HeightOneSpectrum (𝓞 E)) :
    ∃ y : w.adicCompletion E, psi E (sFin E (sLoc E w y)) ≠ 1 := by
  by_contra h
  push Not at h
  refine GroundTheory.Global.localAdelicChar_ne_one (K := E) w (DFunLike.ext _ _ fun y => ?_)
  rw [AddChar.one_apply]
  exact (psi_loc_eq_one_iff w y).1 (h y)


variable (E) in
theorem stdPsi_psi : StdPsi (psi E) := by
  have hc : Continuous (psi E) := continuous_subtype_val.comp (GroundTheory.Global.continuous_adelicChar (K := E))
  have hr : ∀ c : E, psi E (algebraMap E (Ad E) c) = 1 := fun c => by
    rw [psi_apply, GroundTheory.Global.adelicChar_algebraMap]
    rfl
  have hne : psi E ≠ 1 := fun h => GroundTheory.Global.adelicChar_ne_one (K := E) (DFunLike.ext _ _ fun x => by
    have := DFunLike.congr_fun h x
    rw [psi_apply, AddChar.one_apply] at this
    rw [AddChar.one_apply]
    exact Circle.coe_eq_one.1 this)
  letI : Invertible (2 : E) := invertibleOfNonzero two_ne_zero
  letI : Invertible (2 : Ad E) := (Invertible.map (algebraMap E (Ad E)) 2).copy 2 (map_ofNat _ 2).symm
  have h := GlobalTheory.CompanionTheory.AdeleAnn.unitary_and_annihilator_eq E (psi E) hc hne hr
  exact ⟨hc, h.1, hr, h.2, exists_psi_loc_ne_one⟩

end GlobalTheory.StdCharConductor

end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.ChevalleyUnitsProof

theorem normFacts (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (b : ℕ)
    (hb : ((b : ℕ) : 𝓞 F) ∉ v.asIdeal) :
    0 < normV v ∧ ((normV v : ℕ) : 𝓞 F) ∈ v.asIdeal ∧ (normV v).Coprime b := by
  classical
  have hN : normV v = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  have hne : v.asIdeal ≠ ⊥ := v.ne_bot
  refine ⟨?_, ?_, ?_⟩
  · rw [hN]; exact Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hne)
  · rw [hN]; exact Ideal.absNorm_mem _
  · haveI : v.asIdeal.IsMaximal := v.isMaximal
    letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field _
    haveI : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
    letI : Fintype (𝓞 F ⧸ v.asIdeal) := Fintype.ofFinite _
    obtain ⟨p, hp⟩ := CharP.exists (𝓞 F ⧸ v.asIdeal)
    haveI := hp
    haveI : Fact p.Prime := ⟨CharP.char_is_prime (𝓞 F ⧸ v.asIdeal) p⟩
    obtain ⟨n, hp', hcard⟩ := FiniteField.card (𝓞 F ⧸ v.asIdeal) p
    have hNv : normV v = p ^ (n : ℕ) := by
      unfold normV; rw [Nat.card_eq_fintype_card, hcard]
    apply Nat.coprime_of_dvd
    intro q hq hqN hqb
    rw [hNv] at hqN
    have hqp : q = p := (Nat.prime_dvd_prime_iff_eq hq hp').1 (hq.dvd_of_dvd_pow hqN)
    subst hqp
    apply hb
    obtain ⟨e, rfl⟩ := hqb
    rw [Nat.cast_mul]
    apply Ideal.mul_mem_right
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero _ _

theorem core (E : Type) [Field E] [NumberField E] (l r b : ℕ) (hl : l.Prime) (hb : 0 < b) :
    ∃ a : ℕ, 0 < a ∧ a.Coprime b ∧ ∀ u : (𝓞 E)ˣ, (a : 𝓞 E) ∣ (u : 𝓞 E) - 1 → ∃ v : (𝓞 E)ˣ, u = v ^ (l ^ r) := by
  classical
  have hm : 0 < l ^ r := pow_pos hl.pos r
  set m := l ^ r with hmdef
  obtain ⟨M, hM0, hmM, hD⟩ := GlobalTheory.T.exists_pow_descent_cyclotomic' E l r hl
  let Ω := AlgebraicClosure E
  haveI : NeZero (M : Ω) := ⟨by exact_mod_cast hM0.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω M
  let K : IntermediateField E Ω := IntermediateField.adjoin E {ζ}
  haveI : FiniteDimensional E K :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ)
  haveI : NumberField K := NumberField.of_module_finite E K
  haveI : Algebra.IsAlgebraic K Ω := Algebra.IsAlgebraic.tower_top (K := E) K
  haveI : IsAlgClosure K Ω := ⟨inferInstance, inferInstance⟩
  let ζK : K := ⟨ζ, IntermediateField.mem_adjoin_simple_self E ζ⟩
  have hζK : IsPrimitiveRoot ζK M :=
    (show IsPrimitiveRoot (algebraMap K Ω ζK) M from hζ).of_map_of_injective (algebraMap K Ω).injective
  obtain ⟨L, hLfin, hLgal, hLroots⟩ := GlobalTheory.T.exists_finite_galois_contains_roots_of_units E K Ω M hM0 ⟨ζK, hζK⟩
  let S : Set (HeightOneSpectrum (𝓞 K)) := {v | ((M * b : ℕ) : 𝓞 K) ∈ v.asIdeal}
  have hS : S.Finite := by
    have hne : Ideal.span {((M * b : ℕ) : 𝓞 K)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast (Nat.mul_pos hM0 hb).ne'
    refine (Ideal.finite_factors hne).subset ?_
    intro v hv
    exact Ideal.dvd_span_singleton.2 hv
  have hchoice : ∀ g : L ≃ₐ[K] L, ∃ v : HeightOneSpectrum (𝓞 K), v ∉ S ∧ ∃ B : ValuationSubring Ω,
      IsPlaceOver B v ∧ ∃ σ : G K Ω, IsFrob B (normV v) σ ∧ AlgEquiv.restrictNormalHom L σ = g := by
    intro g
    obtain ⟨v, hv, -, B, hB, -, σ, hσ, hg⟩ := GlobalTheory.Published.chebotarevDegreeOne' K Ω L g S hS
    exact ⟨v, hv, B, hB, σ, hσ, hg⟩
  choose v hvS B hB σ hσ hg using hchoice
  have hvb : ∀ g, ((b : ℕ) : 𝓞 K) ∉ (v g).asIdeal := fun g h =>
    hvS g (by simp only [S, Set.mem_setOf_eq, Nat.cast_mul]; exact Ideal.mul_mem_left _ _ h)
  have hvM : ∀ g, ((M : ℕ) : 𝓞 K) ∉ (v g).asIdeal := fun g h =>
    hvS g (by simp only [S, Set.mem_setOf_eq, Nat.cast_mul]; exact Ideal.mul_mem_right _ _ h)
  have hnf := fun g => normFacts K (v g) b (hvb g)
  let a : ℕ := ∏ g : L ≃ₐ[K] L, normV (v g)
  refine ⟨a, Finset.prod_pos fun g _ => (hnf g).1, Nat.Coprime.prod_left fun g _ => (hnf g).2.2, ?_⟩
  intro u hu
  obtain ⟨c, hc⟩ := hu
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap E Ω ((u : 𝓞 E) : E)) hM0
  have hwL := hLroots u w hw
  let x : 𝓞 K := ⟨algebraMap E K ((u : 𝓞 E) : E), ((u : 𝓞 E).2).map (IsScalarTower.toAlgHom ℤ E K)⟩
  let c' : 𝓞 K := ⟨algebraMap E K (c : E), (c.2).map (IsScalarTower.toAlgHom ℤ E K)⟩
  have hx1 : ∀ g, x - 1 ∈ (v g).asIdeal := by
    intro g
    have hxc : x - 1 = ((a : ℕ) : 𝓞 K) * c' := by
      apply RingOfIntegers.ext
      change algebraMap E K ((u : 𝓞 E) : E) - 1 = ((a : ℕ) : K) * algebraMap E K ((c : 𝓞 E) : E)
      have h2 := congrArg (fun t : 𝓞 E => algebraMap E K (t : E)) hc
      simpa using h2
    rw [hxc]
    apply Ideal.mul_mem_right
    have hdvd : normV (v g) ∣ a := Finset.dvd_prod_of_mem _ (Finset.mem_univ g)
    obtain ⟨e, he⟩ := hdvd
    rw [he, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (hnf g).2.1
  have hwx : w ^ M = algebraMap K Ω (x : K) := by
    rw [hw]; rfl
  have hfix : ∀ g : L ≃ₐ[K] L, g ⟨w, hwL⟩ = ⟨w, hwL⟩ := by
    intro g
    have h1 := GlobalTheory.T.isFrob_fixes_root_of_one_mod_place K Ω M ζK hζK (v g) (hvM g) (B g) (hB g) (σ g) (hσ g) x (hx1 g) w hwx
    rw [← hg g]
    apply Subtype.ext
    rw [AlgEquiv.restrictNormalHom_apply]
    exact h1
  have hwK : (⟨w, hwL⟩ : L) ∈ (⊥ : IntermediateField K L) := (IsGalois.mem_bot_iff_fixed _).2 hfix
  obtain ⟨k, hk⟩ := IntermediateField.mem_bot.1 hwK
  have hwK' : w ∈ K := by
    have : algebraMap K Ω k = w := congrArg Subtype.val hk
    rw [← this]; exact k.2
  obtain ⟨y, hy⟩ := hD Ω ζ hζ _ w hwK' hw
  have hu0 : ((u : 𝓞 E) : E) ≠ 0 := by
    intro h0
    have : ((u : 𝓞 E)) = 0 := RingOfIntegers.ext (by simpa using h0)
    exact u.ne_zero this
  have hy0 : y ≠ 0 := by
    rintro rfl; exact hu0 (by rw [← hy, zero_pow hm.ne'])
  have hyi : IsIntegral ℤ y := IsIntegral.of_pow hm (by rw [hy]; exact (u : 𝓞 E).2)
  have hyi' : IsIntegral ℤ y⁻¹ := IsIntegral.of_pow hm (by
    rw [inv_pow, hy]
    have : (((u⁻¹ : (𝓞 E)ˣ) : 𝓞 E) : E) = ((u : 𝓞 E) : E)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      have h3 := congrArg (fun t : 𝓞 E => (t : E)) u.inv_mul
      simpa using h3
    rw [← this]; exact ((u⁻¹ : (𝓞 E)ˣ) : 𝓞 E).2)
  refine ⟨⟨⟨y, hyi⟩, ⟨y⁻¹, hyi'⟩, RingOfIntegers.ext (by change y * y⁻¹ = 1; exact mul_inv_cancel₀ hy0), RingOfIntegers.ext (by change y⁻¹ * y = 1; exact inv_mul_cancel₀ hy0)⟩, ?_⟩
  apply Units.ext
  apply RingOfIntegers.ext
  rw [Units.val_pow_eq_pow_val]
  change ((u : 𝓞 E) : E) = y ^ m
  rw [hy]

theorem combine (E : Type) [Field E] [NumberField E] (b m₁ m₂ : ℕ) (hcop : m₁.Coprime m₂)
    (h₁ : ∃ a : ℕ, 0 < a ∧ a.Coprime b ∧ ∀ u : (𝓞 E)ˣ, (a : 𝓞 E) ∣ (u : 𝓞 E) - 1 → ∃ v : (𝓞 E)ˣ, u = v ^ m₁)
    (h₂ : ∃ a : ℕ, 0 < a ∧ a.Coprime b ∧ ∀ u : (𝓞 E)ˣ, (a : 𝓞 E) ∣ (u : 𝓞 E) - 1 → ∃ v : (𝓞 E)ˣ, u = v ^ m₂) :
    ∃ a : ℕ, 0 < a ∧ a.Coprime b ∧ ∀ u : (𝓞 E)ˣ, (a : 𝓞 E) ∣ (u : 𝓞 E) - 1 →
      ∃ v : (𝓞 E)ˣ, u = v ^ (m₁ * m₂) := by
  obtain ⟨a₁, ha₁, hc₁, hu₁⟩ := h₁
  obtain ⟨a₂, ha₂, hc₂, hu₂⟩ := h₂
  refine ⟨a₁ * a₂, Nat.mul_pos ha₁ ha₂, Nat.Coprime.mul_left hc₁ hc₂, ?_⟩
  intro u hu
  have hd₁ : (a₁ : 𝓞 E) ∣ (u : 𝓞 E) - 1 := dvd_trans ⟨(a₂ : 𝓞 E), by push_cast; ring⟩ hu
  have hd₂ : (a₂ : 𝓞 E) ∣ (u : 𝓞 E) - 1 := dvd_trans ⟨(a₁ : 𝓞 E), by push_cast; ring⟩ hu
  obtain ⟨v₁, hv₁⟩ := hu₁ u hd₁
  obtain ⟨v₂, hv₂⟩ := hu₂ u hd₂
  set s := Nat.gcdA m₁ m₂
  set t := Nat.gcdB m₁ m₂
  have hg : ((1 : ℕ) : ℤ) = (m₁ : ℤ) * s + (m₂ : ℤ) * t := by
    rw [← hcop.gcd_eq_one]; exact Nat.gcd_eq_gcd_ab m₁ m₂
  have key : u = u ^ ((m₁ : ℤ) * s + (m₂ : ℤ) * t) := by
    rw [← hg]; simp
  have e1 : u ^ ((m₁ : ℤ) * s) = v₂ ^ (s * ((m₁ * m₂ : ℕ) : ℤ)) := by
    conv_lhs => rw [hv₂]
    rw [← zpow_natCast, ← zpow_mul]; congr 1; push_cast; ring
  have e2 : u ^ ((m₂ : ℤ) * t) = v₁ ^ (t * ((m₁ * m₂ : ℕ) : ℤ)) := by
    conv_lhs => rw [hv₁]
    rw [← zpow_natCast, ← zpow_mul]; congr 1; push_cast; ring
  refine ⟨v₂ ^ s * v₁ ^ t, ?_⟩
  calc u = u ^ ((m₁ : ℤ) * s + (m₂ : ℤ) * t) := key
    _ = u ^ ((m₁ : ℤ) * s) * u ^ ((m₂ : ℤ) * t) := zpow_add _ _ _
    _ = (v₂ ^ s * v₁ ^ t) ^ (m₁ * m₂) := by
      rw [e1, e2, zpow_mul, zpow_mul, ← mul_zpow, zpow_natCast]

end GlobalTheory.ChevalleyUnitsProof

theorem GlobalTheory.Published.chevalleyUnits' : GlobalTheory.Published.ChevalleyUnits := by
  intro E _ _ m b hm hb
  induction m using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp hn => exact GlobalTheory.ChevalleyUnitsProof.core E p n b hp hb
  | zero => exact absurd hm (lt_irrefl 0)
  | one => exact ⟨1, one_pos, Nat.coprime_one_left b, fun u _ => ⟨u, (pow_one u).symm⟩⟩
  | coprime a b' ha hb' hab iha ihb => exact GlobalTheory.ChevalleyUnitsProof.combine E b a b' hab (iha (by omega)) (ihb (by omega))

end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.LatExact

theorem W_exact : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T₀ T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsSESLat (Qp := ℚ_[l]) (O := ↥(OL LL)) ι π → Function.Injective (W.map ι) ∧ Function.Surjective (W.map π) ∧ ∀ x, W.map π x = 0 ↔ ∃ y, W.map ι y = x := by
  intro D HW F l _ K s LL h W T₀ T₁ T₂ ι π hses
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.EtaleExact.DD_exact D HW F (GlobalTheory.Decompl.fontaine_and_decompletion D HW F) l K s LL h T₀ T₁ T₂ ι π hses
  exact ⟨h1, h3, fun x => h2 x⟩

end GlobalTheory.LatExact
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

theorem _root_.GlobalTheory.T.heckeCharacter_value_at_conjugatePlace_pow : ∀ (D : D7) (PP : Pl D.host.E) (e : AE D) (ϖ : 𝓞 D.host.E) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (n : ℕ) (y : (AE D)ˣ), Formalism.L2.NTheta.IsIdemAt e PP → ϖ ∈ PP.asIdeal → ϖ ∉ PP.asIdeal ^ 2 → ChrEq c χ → χ.UnrAt (Formalism.L2.DIV.conjPl PP) → (y : AE D) = 1 + cA D e * (incA D (star (ϖ : D.host.E)) ^ n - 1) → ((c y : Circle) : ℂ) = ((χ.val (Formalism.L2.DIV.conjPl PP) : ℂˣ) : ℂ) ^ n := by
  first | exact @GlobalTheory.ConjLocVal.value_at_conj_place | exact GlobalTheory.ConjLocVal.value_at_conj_place | (intros; apply GlobalTheory.ConjLocVal.value_at_conj_place <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory.HerrFull

theorem herr_part_a_every_record :
    ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW),
      Formalism.MainNotions.LocalSituation.ClassMapInjectiveBijectiveNorms D HW F :=
  fun D HW F => herr_a_and_natural D HW F

end GlobalTheory.HerrFull
end
