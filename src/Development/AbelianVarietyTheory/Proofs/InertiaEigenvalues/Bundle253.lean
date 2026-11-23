module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle230
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle217
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import GroundTheory.LocalFields.Bundle002
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle088
public import GroundTheory.LocalFields.Bundle004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle231
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle007

@[expose] public section

section

open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

namespace GlobalTheory.SmallTrace

theorem exists_ball_sub_image {l : ℕ} [Fact l.Prime] {ι F : Type} [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace ℚ_[l] F] (S : (ι → ℚ_[l]) →ₗ[ℚ_[l]] F) :
    ∃ ε > 0, ∀ w ∈ LinearMap.range S, ‖w‖ < ε → ∃ x : ι → ℚ_[l], ‖x‖ < 1 ∧ S x = w := by
  have hS' : Function.Surjective S.rangeRestrict := LinearMap.surjective_rangeRestrict S
  have ho : IsOpenMap S.rangeRestrict := LinearMap.isOpenMap_of_finiteDimensional _ hS'
  have hU : IsOpen (S.rangeRestrict '' Metric.ball 0 1) := ho _ Metric.isOpen_ball
  have h0 : (0 : LinearMap.range S) ∈ S.rangeRestrict '' Metric.ball 0 1 := ⟨0, by simp, by simp⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU 0 h0
  refine ⟨ε, hε, fun w hw hwε => ?_⟩
  have hmem : (⟨w, hw⟩ : LinearMap.range S) ∈ Metric.ball 0 ε := by
    rw [Metric.mem_ball, dist_zero_right]; exact hwε
  obtain ⟨x, hx, hxw⟩ := hball hmem
  refine ⟨x, by simpa using hx, ?_⟩
  have := congrArg Subtype.val hxw
  simpa using this

variable {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] {a : ℕ}

noncomputable def matOf (r : Γ →* GL (Fin a) (PadicAlgCl l)) (f : Γ →₀ ℤ_[l]) :
    Matrix (Fin a) (Fin a) (PadicAlgCl l) :=
  f.sum fun h c => ((algebraMap ℚ_[l] (PadicAlgCl l)) (c : ℚ_[l])) •
    ((r h : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))

theorem matOf_eq_lc (r : Γ →* GL (Fin a) (PadicAlgCl l)) (t : Finset Γ) (f : Γ →₀ ℤ_[l])
    (hf : f.support ⊆ t) :
    matOf r f = Fintype.linearCombination ℚ_[l]
      (fun i : t => ((r i : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)))
      (fun i => (f i : ℚ_[l])) := by
  rw [Fintype.linearCombination_apply, matOf, Finsupp.sum_of_support_subset f hf _ (by simp)]
  rw [← Finset.sum_coe_sort t]
  simp [algebraMap_smul]

theorem exists_matOf_eq (r : Γ →* GL (Fin a) (PadicAlgCl l)) (t : Finset Γ) (y : t → ℤ_[l]) :
    ∃ f' : Γ →₀ ℤ_[l], matOf r f' = Fintype.linearCombination ℚ_[l]
      (fun i : t => ((r i : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)))
      (fun i => (y i : ℚ_[l])) := by
  classical
  let f' : Γ →₀ ℤ_[l] := Finsupp.onFinset t (fun g => if h : g ∈ t then y ⟨g, h⟩ else 0)
    (by intro g hg; by_contra h; simp [h] at hg)
  refine ⟨f', ?_⟩
  rw [matOf_eq_lc r t f' (Finsupp.support_onFinset_subset)]
  congr 1
  funext i
  simp [f', Finsupp.onFinset_apply, i.2]

end GlobalTheory.SmallTrace

namespace GlobalTheory.SmallTrace
variable {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] {a : ℕ}

theorem matOf_single (r : Γ →* GL (Fin a) (PadicAlgCl l)) (g : Γ) :
    matOf r (Finsupp.single g 1) =
      ((r g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)) := by
  rw [matOf, Finsupp.sum_single_index (by simp)]
  simp

theorem matOf_mem_span (r : Γ →* GL (Fin a) (PadicAlgCl l)) (f : Γ →₀ ℤ_[l]) :
    matOf r f ∈ Submodule.span (PadicAlgCl l) (Set.range fun g =>
      ((r g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))) := by
  rw [matOf]
  exact Submodule.sum_mem _ fun h _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨h, rfl⟩)

theorem trace_zero_of_finset (r : Γ →* GL (Fin a) (PadicAlgCl l)) (t : Finset Γ)
    (ht : ∀ f : Γ →₀ ℤ_[l], ∃ f' : Γ →₀ ℤ_[l], f'.support ⊆ t ∧ matOf r f = matOf r f')
    (D : Matrix (Fin a) (Fin a) (PadicAlgCl l))
    (hD : ∀ i : t, (D * ((r i : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))).trace = 0)
    (g : Γ) : (D * ((r g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))).trace = 0 := by
  obtain ⟨f', hf't, hf'⟩ := ht (Finsupp.single g 1)
  rw [matOf_single, matOf_eq_lc r t f' hf't, Fintype.linearCombination_apply] at hf'
  rw [hf', Matrix.mul_sum, Matrix.trace_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Matrix.mul_smul, Matrix.trace_smul, hD i, smul_zero]

end GlobalTheory.SmallTrace

namespace GlobalTheory.SmallTrace
variable {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] {a : ℕ}

theorem finiteRing_sq_sub_mul_sq_eq_of_card [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    (r : Γ →* GL (Fin a) (PadicAlgCl l)) (hr : Continuous r) (hss : IsSSRep r) :
    ∃ c : ℕ, ∀ (n : ℕ) (f : Γ →₀ ℤ_[l]),
      (∀ g, ‖(matOf r f * ((r g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))).trace‖
        ≤ ((l : ℝ)⁻¹) ^ (n + c)) →
      ∃ f' : Γ →₀ ℤ_[l], matOf r f = ((l : PadicAlgCl l) ^ n) • matOf r f' := by
  obtain ⟨t, ht⟩ := GlobalTheory.T.zlSpan_image_continuous_rep_finite l Γ a r hr
  have ht' : ∀ f : Γ →₀ ℤ_[l], ∃ f' : Γ →₀ ℤ_[l], f'.support ⊆ t ∧ matOf r f = matOf r f' := ht
  let v : t → Matrix (Fin a) (Fin a) (PadicAlgCl l) := fun i =>
    ((r i : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))
  let Φ : Matrix (Fin a) (Fin a) (PadicAlgCl l) →ₗ[ℚ_[l]] (t → PadicAlgCl l) :=
    { toFun := fun M i => (M * v i).trace
      map_add' := by intro M N; funext i; simp [Matrix.add_mul, Matrix.trace_add]
      map_smul' := by intro c M; funext i; simp [Matrix.smul_mul, Matrix.trace_smul] }
  let S : (t → ℚ_[l]) →ₗ[ℚ_[l]] (t → PadicAlgCl l) := Φ ∘ₗ Fintype.linearCombination ℚ_[l] v
  obtain ⟨ε, hε, hball⟩ := exists_ball_sub_image S
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  obtain ⟨c, hc⟩ : ∃ c : ℕ, ((l : ℝ)⁻¹) ^ c < ε :=
    exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hl1)
  refine ⟨c, fun n f hf => ?_⟩
  obtain ⟨f0, hf0t, hf0⟩ := ht' f
  set x0 : t → ℚ_[l] := fun i => (f0 i : ℚ_[l]) with hx0
  have hMf : matOf r f = Fintype.linearCombination ℚ_[l] v x0 := by
    rw [hf0]; exact matOf_eq_lc r t f0 hf0t
  have hΦf : ‖Φ (matOf r f)‖ ≤ ((l : ℝ)⁻¹) ^ (n + c) :=
    (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => hf i
  set q : ℚ_[l] := ((l : ℚ_[l]) ^ n)⁻¹ with hq
  have hlQ : (l : ℚ_[l]) ^ n ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
  have hqn : ‖q‖ = (l : ℝ) ^ n := by
    rw [hq, norm_inv, norm_pow, Padic.norm_p, inv_pow, inv_inv]
  set w : t → PadicAlgCl l := q • Φ (matOf r f) with hw
  have hwS : w = S (q • x0) := by
    rw [hw, map_smul, hMf]; rfl
  have hwε : ‖w‖ < ε := by
    rw [hw, norm_smul, hqn]
    calc (l : ℝ) ^ n * ‖Φ (matOf r f)‖ ≤ (l : ℝ) ^ n * ((l : ℝ)⁻¹) ^ (n + c) :=
          mul_le_mul_of_nonneg_left hΦf (by positivity)
      _ = ((l : ℝ)⁻¹) ^ c := by
          rw [pow_add, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hl0.ne', one_pow, one_mul]
      _ < ε := hc
  obtain ⟨y, hy1, hy⟩ := hball w ⟨_, hwS.symm⟩ hwε
  have hyi : ∀ i, ‖y i‖ ≤ 1 := fun i => (norm_le_pi_norm y i).trans hy1.le
  let yz : t → ℤ_[l] := fun i => ⟨y i, hyi i⟩
  obtain ⟨f', hf'⟩ := exists_matOf_eq r t yz
  refine ⟨f', ?_⟩
  have hlK : ((l : PadicAlgCl l) ^ n) = algebraMap ℚ_[l] (PadicAlgCl l) ((l : ℚ_[l]) ^ n) := by simp
  rw [← sub_eq_zero]
  apply GlobalTheory.T.eq_zero_of_trace_mul_eq_zero_semisimple_rep (PadicAlgCl l) Γ a r hss
  · exact Submodule.sub_mem _ (matOf_mem_span r f)
      (Submodule.smul_mem _ _ (matOf_mem_span r f'))
  · apply trace_zero_of_finset r t ht'
    intro i
    have hy' : Fintype.linearCombination ℚ_[l] v (fun i => (yz i : ℚ_[l])) = Fintype.linearCombination ℚ_[l] v y := rfl
    have key : Φ (matOf r f - ((l : PadicAlgCl l) ^ n) • matOf r f') = 0 := by
      rw [hf', hy', hlK, algebraMap_smul, map_sub, map_smul]
      have : Φ (Fintype.linearCombination ℚ_[l] v y) = w := hy
      rw [this, hw, smul_smul, hq, mul_inv_cancel₀ hlQ, one_smul, sub_self]
    exact congrFun key i

end GlobalTheory.SmallTrace

theorem GlobalTheory.smallTrace_dvd_span : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (a : ℕ) (r : Γ →* GL (Fin a) (PadicAlgCl l)), Continuous r → IsSSRep r → ∃ c : ℕ, ∀ (n : ℕ) (f : Γ →₀ ℤ_[l]), (∀ g, ‖((f.sum fun h c => ((algebraMap ℚ_[l] (PadicAlgCl l)) (c : ℚ_[l])) • ((r h : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))) * ((r g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))).trace‖ ≤ ((l : ℝ)⁻¹) ^ (n + c)) → ∃ f' : Γ →₀ ℤ_[l], (f.sum fun h c => ((algebraMap ℚ_[l] (PadicAlgCl l)) (c : ℚ_[l])) • ((r h : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))) = ((l : PadicAlgCl l) ^ n) • (f'.sum fun h c => ((algebraMap ℚ_[l] (PadicAlgCl l)) (c : ℚ_[l])) • ((r h : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))) := by
  intro l _ Γ _ _ _ _ a r hr hss
  exact GlobalTheory.SmallTrace.finiteRing_sq_sub_mul_sq_eq_of_card r hr hss
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open scoped TensorProduct

namespace GlobalTheory.EigenCoord

theorem exists_basis_mem_iff {O L V : Type} [CommRing O] [IsDomain O] [Field L] [Algebra O L]
    [IsFractionRing O L] [AddCommGroup V] [Module L V] [Module O V] [IsScalarTower O L V]
    (T : Submodule O V) (hfg : T.FG) (hfree : Module.Free O T)
    (hspan : Submodule.span L (T : Set V) = ⊤) :
    ∃ (ρ : ℕ) (t : Module.Basis (Fin ρ) L V),
      ∀ v, v ∈ T ↔ ∀ i, ∃ o : O, algebraMap O L o = t.repr v i := by
  haveI : Module.Finite O T := Module.Finite.iff_fg.mpr hfg
  let c := Module.finBasis O T
  have hli : LinearIndependent O (fun i => (c i : V)) :=
    c.linearIndependent.map' T.subtype (Submodule.ker_subtype T)
  have hli' : LinearIndependent L (fun i => (c i : V)) :=
    (LinearIndependent.iff_fractionRing O L).mp hli
  have hsum : ∀ x : T, (x : V) = ∑ i, algebraMap O L (c.repr x i) • (c i : V) := by
    intro x
    have h := congrArg T.subtype (c.sum_repr x)

    rw [map_sum] at h
    simp only [map_smul, Submodule.subtype_apply] at h
    simp only [algebraMap_smul]
    exact h.symm
  have hsp : ⊤ ≤ Submodule.span L (Set.range fun i => (c i : V)) := by
    rw [← hspan, Submodule.span_le]
    intro x hx
    rw [SetLike.mem_coe, show x = ((⟨x, hx⟩ : T) : V) from rfl, hsum]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let t := Module.Basis.mk hli' hsp
  have ht : ∀ i, t i = (c i : V) := fun i => Module.Basis.mk_apply hli' hsp i
  refine ⟨_, t, fun v => ⟨fun hv i => ⟨c.repr ⟨v, hv⟩ i, ?_⟩, fun h => ?_⟩⟩
  · have h1 : v = ∑ j, algebraMap O L (c.repr ⟨v, hv⟩ j) • t j := by
      simp only [ht]
      exact hsum ⟨v, hv⟩
    have h2 := congrFun (t.repr_sum_self (fun j => algebraMap O L (c.repr ⟨v, hv⟩ j))) i
    rw [← h1] at h2
    exact h2.symm
  · choose o ho using h
    rw [← t.sum_repr v]
    refine T.sum_mem fun i _ => ?_
    rw [← ho, algebraMap_smul, ht]
    exact T.smul_mem _ (c i).2

theorem norm_coe_aut_le_one_iff {l : ℕ} [Fact l.Prime] (ι : GQ l) (x : Om l) :
    ‖((ι x : Om l) : PadicComplex l)‖ ≤ 1 ↔ ‖x‖ ≤ 1 := by
  rw [PadicComplex.norm_extends, ← isIntegral_padicInt_iff_norm_le_one,
    ← isIntegral_padicInt_iff_norm_le_one]
  exact isIntegral_algHom_iff (ι.toAlgHom.restrictScalars ℤ_[l]) ι.injective

theorem exists_matrix_of_basis {F L C V : Type} [NormedField F] [Field L] [NormedField C]
    [Algebra F L] [Algebra F C] [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V]
    (S : Set V) {d ρ : ℕ} (b : Module.Basis (Fin d) F V) (t : Module.Basis (Fin ρ) L V)
    (φ : L →ₐ[F] C) (hb : ∀ v, v ∈ S ↔ ∀ i, ‖b.repr v i‖ ≤ 1)
    (hmem : ∀ v, v ∈ S ↔ ∀ i, ‖φ (t.repr v i)‖ ≤ 1) :
    ∃ Pr : Matrix (Fin ρ) (Fin d) C, (∀ i j, ‖Pr i j‖ ≤ 1) ∧
      (∀ a : L, Pr * Matrix.of (fun i k : Fin d => algebraMap F C (b.repr (a • b k) i)) =
        φ a • Pr) ∧
      ∀ y : Fin d → F, (∀ i, ‖Pr.mulVec (fun a => algebraMap F C (y a)) i‖ ≤ 1) →
        ∀ a, ‖y a‖ ≤ 1 := by
  have key : ∀ (y : Fin d → F) (i : Fin ρ),
      ∑ j, φ (t.repr (b j) i) * algebraMap F C (y j) = φ (t.repr (∑ j, y j • b j) i) := by
    intro y i

    rw [map_sum, Finsupp.finsetSum_apply, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← algebraMap_smul L (y j), map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul,
      AlgHom.commutes, mul_comm]
  refine ⟨Matrix.of fun i j => φ (t.repr (b j) i), fun i j => ?_, fun a => ?_, fun y hy a => ?_⟩
  · refine (hmem _).mp ((hb _).mpr fun k => ?_) i
    rw [b.repr_self, Finsupp.single_apply]
    split_ifs <;> simp
  · ext i k
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply, Matrix.smul_apply]
    rw [key, b.sum_repr, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, smul_eq_mul]
  · have hv : (∑ j, y j • b j) ∈ S := by
      refine (hmem _).mpr fun i => ?_
      rw [← key]
      exact hy i
    have := (hb _).mp hv a
    rwa [congrFun (b.repr_sum_self y) a] at this

theorem exists_matrix : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (d : ℕ) (b : Module.Basis (Fin d) ℚ_[l] T.V), (∀ v : T.V, v ∈ T.L.T ↔ ∀ i, ‖b.repr v i‖ ≤ 1) → ∀ ι : GQ l, ∃ (ρ : ℕ) (Pr : Matrix (Fin ρ) (Fin d) (PadicComplex l)), (∀ i j, ‖Pr i j‖ ≤ 1) ∧ (∀ a : ↥LL.1, Pr * Matrix.of (fun i k : Fin d => algebraMap ℚ_[l] (PadicComplex l) (b.repr (a • b k) i)) = ((ι (a : Om l) : Om l) : PadicComplex l) • Pr) ∧ ∀ y : Fin d → ℚ_[l], (∀ i, ‖Pr.mulVec (fun a => algebraMap ℚ_[l] (PadicComplex l) (y a)) i‖ ≤ 1) → ∀ a, ‖y a‖ ≤ 1 := by
  intro l _ K LL T d b hb ι
  haveI := LL.2
  haveI : IsFractionRing (OL LL) LL.1 := isFractionRing_integralClosure_padicInt l LL.1
  obtain ⟨ρ, t, ht⟩ := exists_basis_mem_iff (L := LL.1) T.L.T T.L.fg T.L.free T.L.span
  let φ : LL.1 →ₐ[ℚ_[l]] PadicComplex l :=
    (IsScalarTower.toAlgHom ℚ_[l] (Om l) (PadicComplex l)).comp (ι.toAlgHom.comp LL.1.val)
  have hφ : ∀ x : LL.1, φ x = ((ι (x : Om l) : Om l) : PadicComplex l) := fun _ => rfl
  have hmem : ∀ v, v ∈ T.L.T ↔ ∀ i, ‖φ (t.repr v i)‖ ≤ 1 := by
    intro v
    rw [ht]
    refine forall_congr' fun i => ?_
    rw [hφ, norm_coe_aut_le_one_iff, ← mem_integralClosure_padicInt_iff]
    exact ⟨fun ⟨o, ho⟩ => ho ▸ o.2, fun h => ⟨⟨_, h⟩, rfl⟩⟩
  exact ⟨ρ, exists_matrix_of_basis (T.L.T : Set T.V) b t φ hb hmem⟩

end GlobalTheory.EigenCoord
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.Cyc

open IsLocalRing

theorem modEq_of_pow_modEq_pow_sub_one (l n a b : ℕ) (hl : 2 ≤ l) (hn : 0 < n)
    (h : l ^ a ≡ l ^ b [MOD l ^ n - 1]) : a ≡ b [MOD n] := by
  rcases Nat.lt_or_ge 1 n with h1 | h1
  · have hpos : 1 ≤ l ^ n := Nat.one_le_pow _ _ (by omega)
    have hone : l ^ n ≡ 1 [MOD l ^ n - 1] :=
      ((Nat.modEq_iff_dvd' hpos).2 dvd_rfl).symm
    have hred : ∀ c : ℕ, l ^ c ≡ l ^ (c % n) [MOD l ^ n - 1] := by
      intro c
      conv_lhs => rw [← Nat.div_add_mod c n, pow_add, pow_mul]
      have := (hone.pow (c / n)).mul_right (l ^ (c % n))
      simpa using this
    have hlt : ∀ c : ℕ, l ^ (c % n) < l ^ n - 1 := by
      intro c
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      have h2 : l ^ (c % (k + 1)) ≤ l ^ k :=
        Nat.pow_le_pow_right (by omega) (Nat.lt_succ_iff.1 (Nat.mod_lt _ hn))
      have h3 : l ^ 1 ≤ l ^ k := Nat.pow_le_pow_right (by omega) (by omega)
      have h4 : l ^ k * 2 ≤ l ^ k * l := Nat.mul_le_mul_left _ hl
      rw [pow_one] at h3
      rw [pow_succ]
      omega
    have h5 : l ^ (a % n) ≡ l ^ (b % n) [MOD l ^ n - 1] :=
      ((hred a).symm.trans h).trans (hred b)
    have h6 := Nat.ModEq.eq_of_lt_of_lt h5 (hlt a) (hlt b)
    exact Nat.pow_right_injective hl h6
  · obtain rfl : n = 1 := by omega
    exact Nat.modEq_one

theorem exists_frobenius_and_exponent_modEq (l : ℕ) [Fact l.Prime] :
    (∃ φ : GQ l, ∀ n : ℕ, 0 < n → ∀ x : Om l, x ^ l ^ n = x → φ x = x ^ l) ∧
    ∀ n a b : ℕ, 0 < n → (∀ x : Om l, x ^ l ^ n = x → x ^ l ^ a = x ^ l ^ b) →
      a ≡ b [MOD n] := by
  have hp : l.Prime := Fact.out
  have hgt : ∀ n : ℕ, 0 < n → 1 < l ^ n := fun n hn => Nat.one_lt_pow hn.ne' hp.one_lt
  constructor
  · have e : (ℤ_[l] ⧸ maximalIdeal ℤ_[l]) ≃+* ZMod l := PadicInt.residueField
    have : NeZero l := ⟨hp.ne_zero⟩
    have hcard : Nat.card (ℤ_[l] ⧸ maximalIdeal ℤ_[l]) = l := by
      rw [Nat.card_congr e.toEquiv, Nat.card_zmod]
    obtain ⟨φ, hφ⟩ := GlobalTheory.MemLoc.exists_algEquiv_rootOfUnity_eq_pow ℤ_[l] ℚ_[l]
      (Finite.of_equiv _ e.symm.toEquiv) (Om l)
    rw [hcard] at hφ
    refine ⟨φ, fun n hn x hx => ?_⟩
    by_cases h0 : x = 0
    · rw [h0, map_zero, zero_pow hp.ne_zero]
    have h1 := hgt n hn
    refine hφ x (l ^ n - 1) (fun h => ?_) ?_
    · rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_natCast, ZMod.natCast_eq_zero_iff] at h
      have h2 : l ∣ l ^ n := dvd_pow_self l hn.ne'
      have h3 : l ∣ l ^ n - (l ^ n - 1) := Nat.dvd_sub h2 h
      have h4 : l ^ n - (l ^ n - 1) = 1 := by omega
      rw [h4] at h3
      exact hp.one_lt.ne' (Nat.dvd_one.1 h3)
    · apply mul_right_cancel₀ h0
      rw [← pow_succ, one_mul, Nat.sub_add_cancel h1.le, hx]
  · intro n a b hn h
    have h1 := hgt n hn
    have : NeZero (l ^ n - 1) := ⟨by omega⟩
    have : NeZero ((l ^ n - 1 : ℕ) : Om l) := inferInstance
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) (l ^ n - 1)
    have h2 : ζ ^ l ^ n = ζ := by
      conv_lhs => rw [← Nat.sub_add_cancel h1.le, pow_succ, hζ.pow_eq_one, one_mul]
    have h3 := h ζ h2
    apply modEq_of_pow_modEq_pow_sub_one l n a b hp.two_le hn
    have hfin : IsOfFinOrder ζ := hζ.isOfFinOrder (by omega)
    rw [hζ.eq_orderOf]
    exact hfin.pow_eq_pow_iff_modEq.1 h3

end GlobalTheory.Cyc
end

section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.DecompForms

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π ↔ ∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t := D.R.t) (r π) (ρ π) (D.nd.chi i) e := by
  intro D i r ρ π
  constructor
  · rintro ⟨e, he⟩
    exact ⟨e, fun g u => he g u⟩
  · rintro ⟨e, he⟩
    exact ⟨e, fun g u => he g u⟩

end GlobalTheory.DecompForms
end

section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory
open Formalism.MainNotions.SumRepresentations.At

section Tw
variable {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ}

theorem twGL_val (ρ : Γ →* GL (Fin a) k) (χ : Γ →* GL (Fin 1) k) (g : Γ) :
    ((twGL ρ (Matrix.GeneralLinearGroup.det.comp χ) g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) =
      ((χ g : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k).det • ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) := by
  simp only [twGL, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mul, Units.coe_map]
  simp [Algebra.algebraMap_eq_smul_one, Matrix.GeneralLinearGroup.val_det_apply]

theorem isInv_twGL_iff (ρ : Γ →* GL (Fin a) k) (χ : Γ →* GL (Fin 1) k) (W : Submodule k (Fin a → k)) :
    IsInv (twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) W ↔ IsInv ρ W := by
  constructor
  · intro h g v hv
    have hu : ((χ g : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k).det ≠ 0 :=
      (Matrix.isUnit_iff_isUnit_det _).1 (χ g).isUnit |>.ne_zero
    have := W.smul_mem (((χ g : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k).det)⁻¹ (h g v hv)
    rw [twGL_val, Matrix.smul_mulVec, smul_smul, inv_mul_cancel₀ hu, one_smul] at this
    exact this
  · intro h g v hv
    rw [twGL_val, Matrix.smul_mulVec]
    exact W.smul_mem _ (h g v hv)

theorem isSSRep_twGL (ρ : Γ →* GL (Fin a) k) (χ : Γ →* GL (Fin 1) k) (h : IsSSRep ρ) :
    IsSSRep (twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) := by
  intro W hW
  obtain ⟨W', hW', hc⟩ := h W ((isInv_twGL_iff ρ χ W).1 hW)
  exact ⟨W', (isInv_twGL_iff ρ χ W').2 hW', hc⟩

end Tw

theorem contQ_twGL (D : D7) (i : D.nd.Loc) {a : ℕ} (ρ : GE D.nd →* GL (Fin a) (Qbar (D.nd.l i)))
    (χ : GE D.nd →* GL (Fin 1) (Qbar (D.nd.l i))) (hρ : ContQ D.nd i ρ) (hχ : ContQ D.nd i χ) :
    ContQ D.nd i (twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) := by
  unfold ContQ at *
  simp only [twGL_val]
  exact (hχ.matrix_det).smul hρ

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem restrictNormalHom_mem_lowerRamificationGroup_zero : ∀ (l : ℕ) [Fact l.Prime] (L : Type) [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra ℚ_[l] L] [ValuativeExtension ℚ_[l] L] [FiniteDimensional ℚ_[l] L] [IsGalois ℚ_[l] L] [Algebra L (Om l)] [IsScalarTower ℚ_[l] L (Om l)] (σ : GQ l), (∀ x : Om l, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1) → AlgEquiv.restrictNormalHom L σ ∈ lowerRamificationGroup ℚ_[l] L 0 := by
  intro l _ L _ _ _ _ _ _ _ _ _ _ σ hσ
  rw [mem_lowerRamificationGroup_iff]
  intro x
  have h01 : ((0 : ℤ) + 1).toNat = 1 := rfl
  rw [h01, pow_one]
  have hx : ‖algebraMap L (Om l) (x : L)‖ ≤ 1 := ((GlobalTheory.T.localFieldInteger_iff_algebraicClosureNorm l L (x : L)).1).1 x.2
  have hc : algebraMap L (Om l) (AlgEquiv.restrictNormalHom L σ (x : L)) = σ (algebraMap L (Om l) (x : L)) :=
    AlgEquiv.restrictNormal_commutes σ L (x : L)
  have hlt : valuation L (AlgEquiv.restrictNormalHom L σ (x : L) - (x : L)) < 1 := by
    rw [(GlobalTheory.T.localFieldInteger_iff_algebraicClosureNorm l L _).2, map_sub, hc]
    exact hσ _ hx
  intro hu
  have h1 := (Valuation.integer.integers (valuation L)).isUnit_iff_valuation_eq_one.1 hu
  have h2 : ((((integerAlgEquiv ℚ_[l] L) ((AlgEquiv.restrictNormalHom L) σ)) x - x : 𝒪[L]) : L) =
      AlgEquiv.restrictNormalHom L σ (x : L) - (x : L) := rfl
  change valuation L ((((integerAlgEquiv ℚ_[l] L) ((AlgEquiv.restrictNormalHom L) σ)) x - x : 𝒪[L]) : L) = 1 at h1
  rw [h2] at h1
  exact hlt.ne h1

end GlobalTheory.PMon.Ram
end
