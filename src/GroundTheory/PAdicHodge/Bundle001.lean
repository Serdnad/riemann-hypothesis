module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Order.Int.ConditionallyCompleteOrder
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
public import Lean.Elab.MutualDef
public import Mathlib.Topology.Order.LiminfLimsup
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.LinearAlgebra.Dimension.Finite

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Filter Topology

namespace Laurent

set_option linter.unusedSectionVars false

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

def ConvergesAt (a : ℤ → K) (ρ : ℝ) : Prop :=
  Tendsto (fun n : ℤ => ‖a n‖ * ρ ^ n) cofinite (𝓝 0)

def gaussNorm (a : ℤ → K) (ρ : ℝ) : ℝ := ⨆ n, ‖a n‖ * ρ ^ n

def domSet (a : ℤ → K) (ρ : ℝ) : Set ℤ := {n | ‖a n‖ * ρ ^ n = gaussNorm a ρ}

def lowIndex (a : ℤ → K) (ρ : ℝ) : ℤ := sInf (domSet a ρ)

def highIndex (a : ℤ → K) (ρ : ℝ) : ℤ := sSup (domSet a ρ)

variable {a b c : ℤ → K} {ρ : ℝ}

section Basic

theorem ConvergesAt.bddAbove (h : ConvergesAt a ρ) :
    BddAbove (Set.range fun n : ℤ => ‖a n‖ * ρ ^ n) :=
  h.bddAbove_range_of_cofinite

theorem ConvergesAt.le_gaussNorm (h : ConvergesAt a ρ) (n : ℤ) :
    ‖a n‖ * ρ ^ n ≤ gaussNorm a ρ :=
  le_ciSup h.bddAbove n

theorem gaussNorm_le {C : ℝ} (h : ∀ n, ‖a n‖ * ρ ^ n ≤ C) : gaussNorm a ρ ≤ C :=
  ciSup_le h

theorem gaussNorm_nonneg (hρ : 0 < ρ) : 0 ≤ gaussNorm a ρ :=
  Real.iSup_nonneg fun n => by positivity

theorem ConvergesAt.finite_le (h : ConvergesAt a ρ) {ε : ℝ} (hε : 0 < ε) :
    {n | ε ≤ ‖a n‖ * ρ ^ n}.Finite := by
  have := Filter.eventually_cofinite.1 (h.eventually (gt_mem_nhds hε))
  simpa only [not_lt] using this

end Basic

section Product

variable [CompleteSpace K]

end Product

section Dominant

section Attained

variable (hρ : 0 < ρ) (h : ConvergesAt a ρ) (ha : a ≠ 0)
include hρ h ha

theorem ConvergesAt.exists_eq_gaussNorm : ∃ n, ‖a n‖ * ρ ^ n = gaussNorm a ρ := by
  obtain ⟨n0, hn0⟩ := Function.ne_iff.1 ha
  have hε : 0 < ‖a n0‖ * ρ ^ n0 := by have := norm_pos_iff.2 hn0; positivity
  set S := (h.finite_le hε).toFinset
  have hn0S : n0 ∈ S := by simp [S]
  obtain ⟨m, hmS, hm⟩ := S.exists_max_image (fun n => ‖a n‖ * ρ ^ n) ⟨n0, hn0S⟩
  refine ⟨m, le_antisymm (h.le_gaussNorm m) (gaussNorm_le fun n => ?_)⟩
  by_cases hn : n ∈ S
  · exact hm n hn
  · simp only [S, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_le] at hn
    exact hn.le.trans (hm n0 hn0S)

theorem gaussNorm_pos : 0 < gaussNorm a ρ := by
  obtain ⟨n0, hn0⟩ := Function.ne_iff.1 ha
  have := norm_pos_iff.2 hn0
  exact lt_of_lt_of_le (by positivity) (h.le_gaussNorm n0)

theorem domSet_finite : (domSet a ρ).Finite :=
  (h.finite_le (gaussNorm_pos hρ h ha)).subset fun n hn => le_of_eq (Eq.symm hn)

theorem domSet_nonempty : (domSet a ρ).Nonempty :=
  h.exists_eq_gaussNorm hρ ha

theorem lowIndex_mem : lowIndex a ρ ∈ domSet a ρ :=
  Int.csInf_mem (domSet_nonempty hρ h ha) (domSet_finite hρ h ha).bddBelow

theorem highIndex_mem : highIndex a ρ ∈ domSet a ρ :=
  Int.csSup_mem (domSet_nonempty hρ h ha) (domSet_finite hρ h ha).bddAbove

theorem lowIndex_le {n : ℤ} (hn : n ∈ domSet a ρ) : lowIndex a ρ ≤ n :=
  csInf_le (domSet_finite hρ h ha).bddBelow hn

theorem le_highIndex {n : ℤ} (hn : n ∈ domSet a ρ) : n ≤ highIndex a ρ :=
  le_csSup (domSet_finite hρ h ha).bddAbove hn

theorem weight_lt_of_lt_lowIndex {n : ℤ} (hn : n < lowIndex a ρ) :
    ‖a n‖ * ρ ^ n < gaussNorm a ρ :=
  lt_of_le_of_ne (h.le_gaussNorm n) fun heq => absurd (lowIndex_le hρ h ha heq) (not_le.2 hn)

theorem weight_lt_of_highIndex_lt {n : ℤ} (hn : highIndex a ρ < n) :
    ‖a n‖ * ρ ^ n < gaussNorm a ρ :=
  lt_of_le_of_ne (h.le_gaussNorm n) fun heq => absurd (le_highIndex hρ h ha heq) (not_le.2 hn)

theorem ne_zero_of_mem_domSet {n : ℤ} (hn : n ∈ domSet a ρ) : a n ≠ 0 := by
  intro h0
  have := gaussNorm_pos hρ h ha
  simp only [domSet, Set.mem_setOf_eq, h0, norm_zero, zero_mul] at hn
  linarith

end Attained

section Multiplicative

variable [CompleteSpace K]

variable (hρ : 0 < ρ) (ha : ConvergesAt a ρ) (hb : ConvergesAt b ρ) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
include hρ ha hb ha0 hb0

end Multiplicative

end Dominant

end Laurent

end GroundTheory.PAdicHodge
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

open UniformSpace Topology Filter

noncomputable section

theorem continuousSMul_of_isometry_of_dense {G X : Type*} [Monoid G] [TopologicalSpace G]
    [PseudoMetricSpace X] [MulAction G X] (D : Set X) (hD : Dense D)
    (hiso : ∀ g : G, Isometry fun x : X => g • x)
    (horb : ∀ d ∈ D, Continuous fun g : G => g • d) : ContinuousSMul G X := by
  refine ⟨continuous_iff_continuousAt.2 fun ⟨g₀, x₀⟩ => ?_⟩
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨d, hd, hxd⟩ := Metric.mem_closure_iff.1 (hD x₀) (ε / 4) (by positivity)
  have h1 : ∀ᶠ g in 𝓝 g₀, dist (g • d) (g₀ • d) < ε / 4 :=
    Metric.tendsto_nhds.1 ((horb d hd).tendsto g₀) _ (by positivity)
  have h2 : ∀ᶠ x in 𝓝 x₀, dist x x₀ < ε / 4 := Metric.ball_mem_nhds _ (by positivity)
  filter_upwards [h1.prod_nhds h2] with q hq
  obtain ⟨hg, hx⟩ := hq
  have e1 : dist (q.1 • q.2) (q.1 • d) = dist q.2 d := (hiso q.1).dist_eq q.2 d
  have e2 : dist (g₀ • d) (g₀ • x₀) = dist d x₀ := (hiso g₀).dist_eq d x₀
  have e3 : dist q.2 d ≤ dist q.2 x₀ + dist x₀ d := dist_triangle _ _ _
  have e4 : dist d x₀ = dist x₀ d := dist_comm _ _
  calc dist (q.1 • q.2) (g₀ • x₀)
      ≤ dist (q.1 • q.2) (q.1 • d) + dist (q.1 • d) (g₀ • d) + dist (g₀ • d) (g₀ • x₀) :=
        dist_triangle4 _ _ _ _
    _ < ε := by rw [e1, e2, e4]; linarith

variable {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem spectralNorm_gal_apply (σ : Gal(PadicAlgCl p/K)) (x : PadicAlgCl p) :
    spectralNorm ℚ_[p] (PadicAlgCl p) (σ x) = spectralNorm ℚ_[p] (PadicAlgCl p) x :=
  (spectralNorm_eq_of_equiv (σ.restrictScalars ℚ_[p]) x).symm

theorem norm_gal_apply (σ : Gal(PadicAlgCl p/K)) (x : PadicAlgCl p) : ‖σ x‖ = ‖x‖ :=
  spectralNorm_gal_apply σ x

theorem isometry_gal (σ : Gal(PadicAlgCl p/K)) : Isometry σ :=
  AddMonoidHomClass.isometry_of_norm σ (norm_gal_apply σ)

instance : UniformContinuousConstSMul Gal(PadicAlgCl p/K) (PadicAlgCl p) :=
  ⟨fun σ => (isometry_gal σ).uniformContinuous⟩

instance : Algebra.IsIntegral K (PadicAlgCl p) := Algebra.IsIntegral.tower_top ℚ_[p]

theorem continuous_gal_apply (y : PadicAlgCl p) :
    Continuous fun σ : Gal(PadicAlgCl p/K) => σ • y := by
  refine continuous_iff_continuousAt.2 fun σ₀ => tendsto_nhds_of_eventually_eq ?_
  let S := MulAction.stabilizer Gal(PadicAlgCl p/K) y
  have hS : (S : Set Gal(PadicAlgCl p/K)) ∈ 𝓝 (σ₀⁻¹ * σ₀) := by
    rw [inv_mul_cancel]
    exact (stabilizer_isOpen_of_isIntegral y).mem_nhds S.one_mem
  filter_upwards [(continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds hS]
    with σ hσ
  have h : (σ₀⁻¹ * σ) • y = y := hσ
  rw [mul_smul, inv_smul_eq_iff] at h
  exact h

theorem gal_smul_coe (σ : Gal(PadicAlgCl p/K)) (y : PadicAlgCl p) :
    σ • (y : ℂ_[p]) = ((σ y : PadicAlgCl p) : ℂ_[p]) :=
  (Completion.coe_smul σ y).symm

instance instMulSemiringActionCp : MulSemiringAction Gal(PadicAlgCl p/K) ℂ_[p] :=
  { (inferInstance : DistribMulAction Gal(PadicAlgCl p/K) ℂ_[p]) with
    smul_one := fun σ => by
      rw [← Completion.coe_one, gal_smul_coe, map_one]
    smul_mul := fun σ x y => by
      refine Completion.induction_on₂ x y (isClosed_eq ?_ ?_) fun a b => ?_
      · exact (continuous_const_smul σ).comp (continuous_fst.mul continuous_snd)
      · exact ((continuous_const_smul σ).comp continuous_fst).mul
          ((continuous_const_smul σ).comp continuous_snd)
      · rw [← Completion.coe_mul, gal_smul_coe, gal_smul_coe, gal_smul_coe, map_mul,
          Completion.coe_mul] }

theorem norm_smul_gal (σ : Gal(PadicAlgCl p/K)) (x : ℂ_[p]) : ‖σ • x‖ = ‖x‖ := by
  refine Completion.induction_on x
    (isClosed_eq (continuous_norm.comp (continuous_const_smul σ)) continuous_norm) fun a => ?_
  rw [gal_smul_coe, PadicComplex.norm_extends, PadicComplex.norm_extends, norm_gal_apply]

theorem isometry_smul_gal (σ : Gal(PadicAlgCl p/K)) : Isometry fun x : ℂ_[p] => σ • x :=
  Isometry.of_dist_eq fun x y => by
    rw [dist_eq_norm, dist_eq_norm, ← smul_sub, norm_smul_gal]

instance : ContinuousSMul Gal(PadicAlgCl p/K) ℂ_[p] :=
  continuousSMul_of_isometry_of_dense (Set.range ((↑) : PadicAlgCl p → ℂ_[p]))
    Completion.denseRange_coe isometry_smul_gal (by
      rintro _ ⟨y, rfl⟩
      simp_rw [gal_smul_coe]
      exact (Completion.continuous_coe _).comp (continuous_gal_apply y))

theorem gal_smul_coe_of_mem (σ : Gal(PadicAlgCl p/K)) (k : K) :
    σ • ((k : PadicAlgCl p) : ℂ_[p]) = ((k : PadicAlgCl p) : ℂ_[p]) := by
  rw [gal_smul_coe]
  exact congrArg _ (σ.commutes k)

theorem gal_smul_algebraMap (σ : Gal(PadicAlgCl p/K)) (q : ℚ_[p]) :
    σ • algebraMap ℚ_[p] ℂ_[p] q = algebraMap ℚ_[p] ℂ_[p] q := by
  rw [IsScalarTower.algebraMap_apply ℚ_[p] (PadicAlgCl p) ℂ_[p]]
  change σ • ((algebraMap ℚ_[p] (PadicAlgCl p) q : PadicAlgCl p) : ℂ_[p]) = _
  rw [gal_smul_coe]
  exact congrArg _ ((σ.restrictScalars ℚ_[p]).commutes q)

def galCp (σ : Gal(PadicAlgCl p/K)) : ℂ_[p] ≃+* ℂ_[p] :=
  MulSemiringAction.toRingEquiv _ ℂ_[p] σ

theorem galCp_apply (σ : Gal(PadicAlgCl p/K)) (x : ℂ_[p]) : galCp σ x = σ • x := rfl

theorem galCp_coe (σ : Gal(PadicAlgCl p/K)) (y : PadicAlgCl p) :
    galCp σ (y : ℂ_[p]) = ((σ y : PadicAlgCl p) : ℂ_[p]) :=
  gal_smul_coe σ y

theorem norm_galCp (σ : Gal(PadicAlgCl p/K)) (x : ℂ_[p]) : ‖galCp σ x‖ = ‖x‖ :=
  norm_smul_gal σ x

theorem isometry_galCp (σ : Gal(PadicAlgCl p/K)) : Isometry (galCp σ) :=
  isometry_smul_gal σ

theorem continuous_galCp (σ : Gal(PadicAlgCl p/K)) : Continuous (galCp σ) :=
  (isometry_galCp σ).continuous

theorem eq_galCp_of_continuous (σ : Gal(PadicAlgCl p/K)) (f : ℂ_[p] → ℂ_[p])
    (hf : Continuous f) (h : ∀ y : PadicAlgCl p, f y = ((σ y : PadicAlgCl p) : ℂ_[p])) :
    f = galCp σ :=
  Completion.ext hf (continuous_galCp σ) fun y => by rw [h, galCp_coe]

def galCpHom : Gal(PadicAlgCl p/K) →* RingAut ℂ_[p] :=
  MulSemiringAction.toRingAut _ ℂ_[p]

theorem galCp_mul (σ τ : Gal(PadicAlgCl p/K)) : galCp (σ * τ) = (galCp τ).trans (galCp σ) :=
  map_mul galCpHom σ τ

theorem galCp_one : galCp (1 : Gal(PadicAlgCl p/K)) = RingEquiv.refl ℂ_[p] :=
  map_one galCpHom

theorem mem_padicComplexInt_iff (x : ℂ_[p]) : x ∈ 𝓞_ℂ_[p] ↔ ‖x‖ ≤ 1 := by
  rw [PadicComplex.norm_eq_norm, Valuation.norm_def, ← NNReal.coe_one, NNReal.coe_le_coe,
    ← map_one (Valuation.RankOne.hom (PadicComplex.valued p).v),
    (Valuation.RankOne.strictMono _).le_iff_le, Valuation.restrict_le_one_iff]
  rfl

end

end GroundTheory.PAdicHodge
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

open Polynomial Module Finset

namespace SemilinearResidue

section Poly

variable {k : Type*} [Field k] {p : ℕ} [hp : Fact p.Prime] [CharP k p]


omit [CharP k p] in
include hp in
theorem two_le_pow {e : ℕ} (he : 0 < e) : 2 ≤ p ^ e :=
  calc 2 ≤ p := hp.out.two_le
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ e := Nat.pow_le_pow_right hp.out.pos he

variable {e : ℕ}

end Poly

section Vec

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

theorem linearIndependent_of_notMem_span (v : ℕ → V) : ∀ m : ℕ,
    (∀ j < m, v j ∉ Submodule.span k (Set.range (fun i : Fin j => v i))) →
      LinearIndependent k (fun i : Fin m => v i) := by
  intro m
  induction m with
  | zero => exact fun _ => linearIndependent_empty_type
  | succ m ih =>
    intro h
    exact linearIndependent_finSucc'.mpr
      ⟨ih (fun j hj => h j (Nat.lt_succ_of_lt hj)), h m (Nat.lt_succ_self m)⟩


variable (k) in
theorem exists_rel [FiniteDimensional k V] (v : ℕ → V) :
    ∃ m, (∃ c : ℕ → k, v m = ∑ i ∈ range m, c i • v i) ∧
      LinearIndependent k (fun i : Fin m => v i) := by
  classical
  let P : ℕ → Prop := fun j => v j ∈ Submodule.span k (Set.range (fun i : Fin j => v i))
  have hex : ∃ j, P j := by
    by_contra hcon
    push Not at hcon
    have li := linearIndependent_of_notMem_span v (finrank k V + 1) (fun j _ => hcon j)
    have := li.fintype_card_le_finrank
    simp at this
  refine ⟨Nat.find hex, ?_, linearIndependent_of_notMem_span v _ (fun j hj => Nat.find_min hex hj)⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).mp (Nat.find_spec hex)
  refine ⟨fun i => if h : i < Nat.find hex then c ⟨i, h⟩ else 0, ?_⟩
  rw [← hc, Finset.sum_range]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [i.2]

variable {p : ℕ} [hp : Fact p.Prime] [CharP k p] {e : ℕ} {φ : V →+ V}


end Vec

end SemilinearResidue

end GroundTheory.PAdicHodge
end
