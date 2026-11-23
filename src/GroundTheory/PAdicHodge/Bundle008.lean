module

public import GroundTheory.LocalFields.Bundle001
public import GroundTheory.LocalFields.SeparableClosure
public import GroundTheory.PAdicHodge.Bundle004
public import GroundTheory.LocalFields.UnramifiedHensel
public import GroundTheory.PAdicHodge.Bundle007
public import GroundTheory.PAdicHodge.BdRSeries
public import GroundTheory.PAdicHodge.AInfXi
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Ring.Ultra
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
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace GroundTheory.PAdicHodge

open GroundTheory.LocalField ValuativeRel Filter Topology

section Nrm

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]

def nrm (x : Ω) : ℝ :=
  letI := normedField K
  spectralNorm K Ω x

variable {K}

theorem nrm_nonneg (x : Ω) : 0 ≤ nrm K x := by
  letI := algebraicNormedField K Ω
  change 0 ≤ ‖x‖
  exact norm_nonneg x

@[simp]
theorem nrm_zero : nrm K (0 : Ω) = 0 := by
  letI := algebraicNormedField K Ω
  change ‖(0 : Ω)‖ = 0
  exact norm_zero

@[simp]
theorem nrm_one : nrm K (1 : Ω) = 1 := by
  letI := algebraicNormedField K Ω
  change ‖(1 : Ω)‖ = 1
  exact norm_one

theorem nrm_mul (x y : Ω) : nrm K (x * y) = nrm K x * nrm K y := by
  letI := algebraicNormedField K Ω
  change ‖x * y‖ = ‖x‖ * ‖y‖
  exact norm_mul x y

theorem nrm_pow (x : Ω) (n : ℕ) : nrm K (x ^ n) = nrm K x ^ n := by
  letI := algebraicNormedField K Ω
  change ‖x ^ n‖ = ‖x‖ ^ n
  exact norm_pow x n

@[simp]
theorem nrm_neg (x : Ω) : nrm K (-x) = nrm K x := by
  letI := algebraicNormedField K Ω
  change ‖-x‖ = ‖x‖
  exact norm_neg x

theorem nrm_pos {x : Ω} : 0 < nrm K x ↔ x ≠ 0 := by
  letI := algebraicNormedField K Ω
  change 0 < ‖x‖ ↔ x ≠ 0
  exact norm_pos_iff

theorem nrm_inv (x : Ω) : nrm K x⁻¹ = (nrm K x)⁻¹ := by
  letI := algebraicNormedField K Ω
  change ‖x⁻¹‖ = ‖x‖⁻¹
  exact norm_inv x

theorem nrm_div (x y : Ω) : nrm K (x / y) = nrm K x / nrm K y := by
  letI := algebraicNormedField K Ω
  change ‖x / y‖ = ‖x‖ / ‖y‖
  exact norm_div x y

theorem nrm_add_le_max (x y : Ω) : nrm K (x + y) ≤ max (nrm K x) (nrm K y) := by
  letI := algebraicNormedField K Ω
  haveI := algebraicNormedField_isUltrametricDist K Ω
  change ‖x + y‖ ≤ max ‖x‖ ‖y‖
  exact IsUltrametricDist.norm_add_le_max x y

theorem nrm_add_le_of_le {x y : Ω} {r : ℝ} (hx : nrm K x ≤ r) (hy : nrm K y ≤ r) :
    nrm K (x + y) ≤ r :=
  (nrm_add_le_max x y).trans (max_le hx hy)

theorem nrm_sum_le {ι : Type*} {s : Finset ι} {f : ι → Ω} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i ∈ s, nrm K (f i) ≤ C) : nrm K (∑ i ∈ s, f i) ≤ C := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hC
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact nrm_add_le_of_le (h j (Finset.mem_insert_self _ _))
      (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

theorem nrm_natCast_le_one (n : ℕ) : nrm K (n : Ω) ≤ 1 := by
  letI := algebraicNormedField K Ω
  haveI := algebraicNormedField_isUltrametricDist K Ω
  change ‖(n : Ω)‖ ≤ 1
  exact IsUltrametricDist.norm_natCast_le_one Ω n

theorem nrm_algEquiv (σ : Ω ≃ₐ[K] Ω) (x : Ω) : nrm K (σ x) = nrm K x := by
  letI := normedField K
  exact (spectralNorm_eq_of_equiv σ x).symm


variable [ValuativeRel Ω] [ValuativeExtension K Ω]

theorem nrm_le_nrm_iff (x y : Ω) : nrm K x ≤ nrm K y ↔ x ≤ᵥ y :=
  (vle_iff_spectralNorm_le (K := K) x y).symm

variable [TopologicalSpace Ω] [IsValuativeTopology Ω]


end Nrm

section Estimates

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]

variable {p : ℕ}

end Estimates

section Tower

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type*) [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] (p : ℕ)

structure NormTower where

  E : ℕ → IntermediateField K Ω
  mono : Monotone E
  finiteDimensional : ∀ n, FiniteDimensional K (E n)

  T : ℕ → Finset Gal(Ω/K)
  fix : ∀ n, ∀ σ ∈ T n, ∀ x ∈ E n, σ x = x
  prod_mem : ∀ n, ∀ y ∈ E (n + 1), (∏ σ ∈ T n, σ y) ∈ E n

  k : ℕ → ℕ
  card_alt : ∀ n, (T n).card = p ^ k n
  frequently_ne_zero : ∀ n, ∃ m, n ≤ m ∧ k m ≠ 0

  c : ℝ
  c_nonneg : 0 ≤ c
  c_lt_one : c < 1
  step : ∀ n, ∀ σ ∈ T n, ∀ x ∈ E (n + 1), nrm K (σ x - x) ≤ c * nrm K x
  prime : p.Prime
  nrm_p_lt_one : nrm K (p : Ω) < 1

  value : ℕ → ℝ
  value_pos : ∀ n, 0 < value n
  value_lt_one : ∀ n, value n < 1
  exists_value : ∀ n, ∃ π ∈ E n, nrm K π = value n
  value_zpow : ∀ n, ∀ y ∈ E n, y ≠ 0 → ∃ j : ℤ, nrm K y = value n ^ j
  value_succ : ∀ n, value (n + 1) ^ (p ^ k n) = value n

namespace NormTower

variable {K Ω p} (t : NormTower K Ω p)

end NormTower

end Tower

end GroundTheory.PAdicHodge
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open ValuativeRel IsLocalRing

namespace UnramifiedACris

variable {p : ℕ} [hp : Fact p.Prime]


variable (K₀ : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K₀]


omit [FiniteDimensional ℚ_[p] K₀] in
theorem mem_integer_iff (x : K₀) : x ∈ 𝒪[K₀] ↔ ‖(x : PadicAlgCl p)‖ ≤ 1 := by
  rw [integer_eq_normInteger, mem_normInteger]
  rfl

theorem natCast_p_mem_maximalIdeal : (p : 𝒪[K₀]) ∈ 𝓂[K₀] := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have h1 : ((((p : 𝒪[K₀]) * v : 𝒪[K₀]) : K₀) : PadicAlgCl p) = 1 := by rw [hv]; rfl
  have hv1 : ‖(((v : 𝒪[K₀]) : K₀) : PadicAlgCl p)‖ ≤ 1 := (mem_integer_iff K₀ _).1 v.2
  have h2 : ‖((((p : 𝒪[K₀]) * v : 𝒪[K₀]) : K₀) : PadicAlgCl p)‖ < 1 := by
    have : ((((p : 𝒪[K₀]) * v : 𝒪[K₀]) : K₀) : PadicAlgCl p) =
        (p : PadicAlgCl p) * (((v : 𝒪[K₀]) : K₀) : PadicAlgCl p) := by
      simp
    rw [this, norm_mul]
    calc ‖(p : PadicAlgCl p)‖ * ‖(((v : 𝒪[K₀]) : K₀) : PadicAlgCl p)‖
        ≤ ‖(p : PadicAlgCl p)‖ * 1 := by gcongr
      _ < 1 := by
        rw [mul_one, ← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)) p, PadicAlgCl.norm_extends]
        exact Padic.norm_p_lt_one
  rw [h1, norm_one] at h2
  exact lt_irrefl _ h2

instance charP_residueField : CharP 𝓀[K₀] p :=
  (CharP.charP_iff_prime_eq_zero hp.out).mpr (by
    rw [← map_natCast (residue 𝒪[K₀]), residue_eq_zero_iff]
    exact natCast_p_mem_maximalIdeal K₀)

variable [GroundTheory.LocalField.IsUnramified ℚ_[p] K₀]

end UnramifiedACris

end GroundTheory.PAdicHodge
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

open Ideal WittVector IsLocalRing

namespace GroundTheory.PAdicHodge

namespace IsPerfectoidField

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [CharZero K]

instance instIsAdicCompleteMaximalIdealBdR :
    IsAdicComplete (maximalIdeal (BDeRhamPlus (normInteger K) p)) (BDeRhamPlus (normInteger K) p) :=
  isAdicComplete_maximalIdeal_bDeRhamPlus

end IsPerfectoidField

section Cp

open PowerSeries

variable {p : ℕ} [Fact p.Prime]

local notation "𝒪" => normInteger ℂ_[p]
local notation "𝒪♭" => PreTilt 𝒪 p
local notation "𝔹" => BDeRhamPlus 𝒪 p
local notation "𝔪" => maximalIdeal 𝔹
local notation "φi" => RingEquiv.symm (_root_.frobeniusEquiv 𝒪♭ p)

variable (p) in
def muBdR (ε : PreTilt (normInteger ℂ_[p]) p) : BDeRhamPlus (normInteger ℂ_[p]) p :=
  wittToBDeRhamPlus 𝒪 p (AInf.mu ε)

theorem muBdR_eq (ε : 𝒪♭) : muBdR p ε = wittToBDeRhamPlus 𝒪 p (teichmuller p ε) - 1 := by
  rw [muBdR, AInf.mu, map_sub, map_one]

theorem muBdR_mem {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) : muBdR p ε ∈ 𝔪 := by
  rw [IsPerfectoidField.maximalIdeal_bDeRhamPlus, RingHom.mem_ker, muBdR,
    IsPerfectoidField.thetaBDeRhamPlusField_wittToBDeRhamPlus, AInf.fontaineTheta_mu hε]
  rfl

def fontaineT (ε : PreTilt (normInteger ℂ_[p]) p) (hε : PreTilt.untilt ε = 1) :
    BDeRhamPlus (normInteger ℂ_[p]) p :=
  logOnePlus 𝔪 (muBdR p ε) (muBdR_mem hε)

theorem fontaineT_sub_sum_mem {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) (n : ℕ) :
    fontaineT ε hε - ∑ i ∈ Finset.Ico 1 n, algebraMap ℚ 𝔹 ((-1) ^ (i + 1) / i) * muBdR p ε ^ i ∈
      𝔪 ^ n := by
  have hs : ∑ i ∈ Finset.Ico 1 n, algebraMap ℚ 𝔹 ((-1) ^ (i + 1) / i) * muBdR p ε ^ i =
      ∑ i ∈ Finset.range n, algebraMap ℚ 𝔹 (coeff i (log ℚ)) * muBdR p ε ^ i := by
    rcases n with _ | n
    · simp
    · rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos n), coeff_log,
        ite_eq_left rfl, map_zero, zero_mul, zero_add]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [coeff_log, ite_eq_right (Nat.ne_of_gt (Finset.mem_Ico.1 hi).1), Algebra.algebraMap_self,
        RingHom.id_apply]
  rw [hs]
  exact seriesEval_sub_sum_mem (muBdR_mem hε) (log ℚ) n

theorem isUnit_of_sub_one_mem {u : 𝔹} (hu : u - 1 ∈ 𝔪) : IsUnit u := by
  by_contra h
  have h1 : u ∈ 𝔪 := (IsLocalRing.mem_maximalIdeal u).2 h
  have h2 : (1 : 𝔹) ∈ 𝔪 := by
    have := sub_mem h1 hu
    rwa [sub_sub_cancel] at this
  exact (IsLocalRing.maximalIdeal.isMaximal 𝔹).ne_top ((Ideal.eq_top_iff_one _).2 h2)

theorem maximalIdeal_eq_span_fontaineT {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt (φi ε) ≠ 1) : 𝔪 = span {fontaineT ε hε} := by
  have hξ := AInf.ker_fontaineTheta_eq_span_xi hε hζ
  have h1 := IsPerfectoidField.maximalIdeal_bDeRhamPlus_eq_span hξ
  have hv : IsUnit (wittToBDeRhamPlus 𝒪 p ((WittVector.frobeniusEquiv p 𝒪♭).symm (AInf.mu ε))) := by
    by_contra h
    have h2 := (IsLocalRing.mem_maximalIdeal _).2 h
    rw [IsPerfectoidField.maximalIdeal_bDeRhamPlus, RingHom.mem_ker,
      IsPerfectoidField.thetaBDeRhamPlusField_wittToBDeRhamPlus] at h2
    have h3 := AInf.fontaineTheta_frobeniusEquiv_symm_pow_mu ε 1
    rw [pow_one, pow_one] at h3
    rw [h3] at h2
    exact hζ (sub_eq_zero.1 (Subtype.ext h2))
  let tail : ℚ⟦X⟧ := PowerSeries.mk fun n => coeff (n + 1) (log ℚ)
  have hlog : log ℚ = X * tail := by
    conv_lhs => rw [eq_X_mul_shift_add_const (log ℚ)]
    rw [constantCoeff_log, map_zero, add_zero]
  let u := seriesEval 𝔪 (muBdR p ε) (muBdR_mem hε) tail
  have hu1 : u - 1 ∈ 𝔪 := by
    have hcoeff : coeff 0 tail = 1 := by
      dsimp only [tail]
      rw [PowerSeries.coeff_mk, zero_add, coeff_one_log]
    have h := seriesEval_sub_sum_mem (muBdR_mem hε) tail 1
    rwa [Finset.sum_range_one, pow_zero, mul_one, pow_one, hcoeff, map_one] at h
  have ht : logOnePlus 𝔪 (muBdR p ε) (muBdR_mem hε) = muBdR p ε * u := by
    rw [logOnePlus, hlog, map_mul, seriesEval_X]
  have hu := isUnit_of_sub_one_mem hu1
  have hμ : muBdR p ε = wittToBDeRhamPlus 𝒪 p (AInf.xi ε) *
      wittToBDeRhamPlus 𝒪 p ((WittVector.frobeniusEquiv p 𝒪♭).symm (AInf.mu ε)) := by
    rw [muBdR, ← map_mul, ← AInf.mu_eq_xi_mul]
  rw [fontaineT, ht, hμ, mul_assoc, Ideal.span_singleton_mul_right_unit (hv.mul hu), h1]

theorem fontaineT_ne_zero {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt (φi ε) ≠ 1) : fontaineT ε hε ≠ 0 := by
  intro h
  have h1 := maximalIdeal_eq_span_fontaineT hε hζ
  rw [h, Ideal.span_singleton_eq_bot.2 rfl] at h1
  exact IsDiscreteValuationRing.not_a_field 𝔹 h1

theorem exists_isPrimitiveRoot_p : ∃ ζ : ℂ_[p], IsPrimitiveRoot ζ p := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  exact HasEnoughRootsOfUnity.exists_isPrimitiveRoot ℂ_[p] p


variable (p) in
def rootSeq : ℕ → ℂ_[p]
  | 0 => 1
  | 1 => (exists_isPrimitiveRoot_p (p := p)).choose
  | (n + 2) => (IsAlgClosed.exists_pow_nat_eq (rootSeq (n + 1)) (Fact.out : p.Prime).pos).choose

theorem rootSeq_succ_pow (n : ℕ) : rootSeq p (n + 1) ^ p = rootSeq p n := by
  rcases n with _ | n
  · exact (exists_isPrimitiveRoot_p (p := p)).choose_spec.pow_eq_one
  · exact (IsAlgClosed.exists_pow_nat_eq (rootSeq p (n + 1)) (Fact.out : p.Prime).pos).choose_spec

theorem rootSeq_pow (n : ℕ) : rootSeq p n ^ p ^ n = 1 := by
  induction n with
  | zero => simp [rootSeq]
  | succ n ih => rw [pow_succ, pow_mul', rootSeq_succ_pow, ih]

theorem rootSeq_one_ne_one : rootSeq p 1 ≠ 1 :=
  (exists_isPrimitiveRoot_p (p := p)).choose_spec.ne_one (Fact.out : p.Prime).one_lt

theorem norm_rootSeq (n : ℕ) : ‖rootSeq p n‖ = 1 := by
  have h := congrArg norm (rootSeq_pow (p := p) n)
  rw [norm_pow, norm_one] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)).1 h


variable (p) in
def rootSeqInt (n : ℕ) : normInteger ℂ_[p] :=
  ⟨rootSeq p n, mem_normInteger.2 (norm_rootSeq n).le⟩

theorem rootSeqInt_succ_pow (n : ℕ) : rootSeqInt p (n + 1) ^ p = rootSeqInt p n :=
  Subtype.ext (by simp [rootSeqInt, rootSeq_succ_pow])


variable (p) in
def epsilon : PreTilt (normInteger ℂ_[p]) p :=
  IsPerfectoidField.ofCompatible p (rootSeqInt p) rootSeqInt_succ_pow

theorem untilt_epsilon : PreTilt.untilt (epsilon p) = 1 := by
  rw [epsilon, IsPerfectoidField.untilt_ofCompatible]
  exact Subtype.ext (by simp [rootSeqInt, rootSeq])

theorem untilt_frobeniusEquiv_symm_epsilon_ne_one : PreTilt.untilt (φi (epsilon p)) ≠ 1 := by
  rw [epsilon, AInf.frobeniusEquiv_symm_ofCompatible, IsPerfectoidField.untilt_ofCompatible]
  intro h
  exact rootSeq_one_ne_one (congrArg Subtype.val h)


variable (p) in
def tBdR : BDeRhamPlus (normInteger ℂ_[p]) p := fontaineT (epsilon p) untilt_epsilon

theorem maximalIdeal_eq_span_tBdR : 𝔪 = span {tBdR p} :=
  maximalIdeal_eq_span_fontaineT untilt_epsilon untilt_frobeniusEquiv_symm_epsilon_ne_one

theorem irreducible_tBdR : Irreducible (tBdR p) := by
  exact (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 maximalIdeal_eq_span_tBdR

end Cp

end GroundTheory.PAdicHodge
end
end
