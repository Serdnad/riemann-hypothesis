module

public import Formalism.LatticeSlopes.CovolAntiSameRank
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Formalism.LatticeSlopes.LatticeSlopesProofs.Bundle001
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
public import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Module Submodule

noncomputable section

namespace Formalism.F

universe u

private theorem finrank_int_eq_finrank_span_real {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] :
    Module.finrank ℤ L = Module.finrank ℝ (span ℝ (L : Set E)) := by

  let V := span ℝ (L : Set E)
  let L' : Submodule ℤ V := L.comap (V.subtype.restrictScalars ℤ)
  let φ : L' ≃ₗ[ℤ] L :=
    { toFun := fun x => ⟨((x : V) : E), x.2⟩
      invFun := fun y => ⟨⟨y, Submodule.subset_span y.2⟩, y.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  haveI : DiscreteTopology L' :=
    DiscreteTopology.of_continuous_injective
      (f := fun x : L' => (⟨((x : V) : E), x.2⟩ : L))
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
      (fun a b h => by
        have h' := congrArg Subtype.val h
        simp only at h'
        exact Subtype.ext (Subtype.ext h'))
  haveI : IsZLattice ℝ L' := ⟨Submodule.span_span_coe_preimage⟩
  exact φ.finrank_eq.symm.trans (ZLattice.rank ℝ L')

theorem linearIndependent_coe_basis' {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [hL : DiscreteTopology L] {ι : Type*} [Fintype ι]
    (e : Basis ι ℤ L) : LinearIndependent ℝ (fun i => (e i : E)) := by
  have hspanZ : span ℤ (Set.range fun i => (e i : E)) = L := by
    have : (Set.range fun i => (e i : E)) = L.subtype '' Set.range e := Set.range_comp _ _
    rw [this, ← Submodule.map_span, e.span_eq, Submodule.map_subtype_top]
  have hspanR : span ℝ (Set.range fun i => (e i : E)) = span ℝ (L : Set E) := by
    rw [← Submodule.span_span_of_tower ℤ ℝ (Set.range fun i => (e i : E)), hspanZ]
  rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, hspanR, ← finrank_int_eq_finrank_span_real L,
    Module.finrank_eq_card_basis e]

theorem gram_intMatrix_eq_map {m : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ] (M : Matrix (Fin m) κ ℤ) :
    Matrix.gram ℝ (fun j => (WithLp.toLp 2 (fun i => (M i j : ℝ)) : EuclideanSpace ℝ (Fin m)))
      = (Int.castRingHom ℝ).mapMatrix (M.transpose * M) := by
  ext i j
  simp [Matrix.gram, Matrix.mul_apply, PiLp.inner_apply, RingHom.mapMatrix_apply, Matrix.map_apply]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

theorem slopesBdd_of (hG : GramDetLe.{u, 0, 0}) : SlopesBdd.{u} := by
  intro E _ _ _ L hL
  haveI := hL
  let e := Module.finBasis ℤ L
  have he : LinearIndependent ℝ (fun i => (e i : E)) := linearIndependent_coe_basis' L e

  let S : EuclideanSpace ℝ (Fin (Module.finrank ℤ L)) →ₗ[ℝ] E :=
    { toFun := fun x => ∑ i, WithLp.ofLp x i • (e i : E)
      map_add' := fun x y => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c x => by simp [Finset.smul_sum, smul_smul] }
  have hSinj : LinearMap.ker S = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    have h0 := Fintype.linearIndependent_iff.mp he (fun i => WithLp.ofLp x i) hx
    have h1 : WithLp.ofLp x = 0 := funext h0
    simpa using congrArg (WithLp.toLp 2) h1
  obtain ⟨K, hK0, hK⟩ := S.exists_antilipschitzWith hSinj
  have hKpos : (0 : ℝ) < K := hK0
  refine ⟨Real.log K, ?_⟩
  rintro t ⟨N, hNL, hN0, rfl⟩
  haveI hN : DiscreteTopology N := DiscreteTopology.of_subset (s := (L : Set E)) hL hNL
  let f := Module.finBasis ℤ N
  let M : Matrix (Fin (Module.finrank ℤ L)) (Fin (Module.finrank ℤ N)) ℤ :=
    fun i j => e.repr ⟨(f j : E), hNL (f j).2⟩ i
  have hfj : ∀ j, (f j : E) = ∑ i, (M i j : ℝ) • (e i : E) := by
    intro j
    have h := congrArg Subtype.val (e.sum_repr ⟨(f j : E), hNL (f j).2⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    simp only [M, Int.cast_smul_eq_zsmul]
    exact h.symm
  let w : Fin (Module.finrank ℤ N) → EuclideanSpace ℝ (Fin (Module.finrank ℤ L)) :=
    fun j => WithLp.toLp 2 (fun i => (M i j : ℝ))
  have hSw : ∀ j, S (w j) = (f j : E) := by
    intro j
    rw [hfj j]
    simp [S, w]
  have hcomp : ∀ c : Fin (Module.finrank ℤ N) → ℝ,
      ‖∑ j, c j • w j‖ ≤ (K : ℝ) * ‖∑ j, c j • (f j : E)‖ := by
    intro c
    have h1 : S (∑ j, c j • w j) = ∑ j, c j • (f j : E) := by

      simp only [map_sum, map_smul, hSw]
    rw [← h1]
    simpa [dist_eq_norm] using hK.le_mul_dist (∑ j, c j • w j) 0
  have hdet := hG E (EuclideanSpace ℝ (Fin (Module.finrank ℤ L))) (Fin (Module.finrank ℤ N))
    (fun j => (f j : E)) w K hcomp
  rw [gram_intMatrix_eq_map M, ← RingHom.map_det, Fintype.card_fin] at hdet

  have hwli : LinearIndependent ℝ w := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have h2 : ∑ j, c j • (f j : E) = 0 := by
      rw [← map_zero S, ← hc]

      simp only [map_sum, map_smul, hSw]
    exact Fintype.linearIndependent_iff.mp (linearIndependent_coe_basis' N f) c h2
  have hwpos : 0 < (Matrix.gram ℝ w).det := (Matrix.posDef_gram_of_linearIndependent hwli).det_pos
  rw [gram_intMatrix_eq_map M, ← RingHom.map_det] at hwpos
  have hd1 : (1 : ℝ) ≤ (Int.castRingHom ℝ) (M.transpose * M).det := by
    simp only [eq_intCast] at hwpos ⊢
    have : (0 : ℤ) < (M.transpose * M).det := by exact_mod_cast hwpos
    exact_mod_cast this
  have hk : (0 : ℝ) < (Module.finrank ℤ N : ℝ) := by
    haveI : Nontrivial N := Submodule.nontrivial_iff_ne_bot.mpr hN0
    exact_mod_cast Module.finrank_pos
  set g := (Matrix.gram ℝ (fun j => (f j : E))).det with hg
  have hgK : 1 ≤ (K : ℝ) ^ (2 * Module.finrank ℤ N) * g := hd1.trans hdet
  have hgpos : 0 < g := by
    by_contra hneg
    push_neg at hneg
    have : (K : ℝ) ^ (2 * Module.finrank ℤ N) * g ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg
    linarith
  have hlog : -(2 * (Module.finrank ℤ N : ℝ)) * Real.log K ≤ Real.log g := by
    have h1 : Real.log 1 ≤ Real.log ((K : ℝ) ^ (2 * Module.finrank ℤ N) * g) :=
      Real.log_le_log one_pos hgK
    rw [Real.log_one, Real.log_mul (by positivity) hgpos.ne', Real.log_pow] at h1
    push_cast at h1
    linarith
  have hcov : covol N = Real.sqrt g := by rw [covol, dite_eq_left hN]
  show -Real.log (covol N) / (Module.finrank ℤ N : ℝ) ≤ Real.log K
  rw [hcov, Real.log_sqrt hgpos.le, div_le_iff₀ hk]
  nlinarith

end Formalism.F
end
end

section

namespace Formalism.F

universe u

theorem slopeLeMuMax_of (h : SlopesBdd.{u}) : SlopeLeMuMax.{u} := by
  intro E _ _ _ L N hL hNL hN
  exact le_csSup (h E L hL) (show slope N ∈ slopes L from ⟨N, hNL, hN, rfl⟩)

theorem muMaxMono_of (h : SlopesBdd.{u}) : MuMaxMono.{u} := by
  intro E _ _ _ L N hL hNL hN
  apply csSup_le_csSup (h E L hL) (show (slopes N).Nonempty from ⟨slope N, N, le_rfl, hN, rfl⟩)
  rintro t ⟨M, hMN, hM, rfl⟩
  exact ⟨M, hMN.trans hNL, hM, rfl⟩

end Formalism.F
end

section

open Module Submodule MeasureTheory

noncomputable section

namespace Formalism.F

universe u

theorem covol_eq_of_linearEquiv_inner {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (L : Submodule ℤ E) (M : Submodule ℤ F) [DiscreteTopology L] [DiscreteTopology M]
    (f : L ≃ₗ[ℤ] M)
    (hf : ∀ x y : L, inner ℝ ((f x : M) : F) ((f y : M) : F) = inner ℝ (x : E) (y : E)) :
    covol M = covol L := by
  classical
  let b := Module.finBasis ℤ L
  rw [covol_eq_gram F M (Fin (Module.finrank ℤ L)) (b.map f), covol_eq_gram E L _ b]
  congr 2
  ext i j
  simp only [Matrix.gram, Matrix.of_apply, Basis.map_apply]
  exact hf (b i) (b j)

theorem exists_short_vector_of_isZLattice (hC : CovolEqCovolume.{u}) {W : Type u} [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W]
    (L : Submodule ℤ W) [DiscreteTopology L] [IsZLattice ℝ L] (hn : 0 < finrank ℝ W) :
    ∃ x ∈ L, x ≠ 0 ∧
      ‖x‖ ≤ Real.sqrt (finrank ℝ W : ℝ) * covol L ^ ((1 : ℝ) / (finrank ℝ W : ℝ)) := by
  classical
  set n := finrank ℝ W with hn_def
  let b := Module.finBasis ℤ L
  have hfund := ZLattice.isAddFundamentalDomain b MeasureTheory.volume
  have hcov : ZLattice.covolume L = MeasureTheory.volume.real
      (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L)) :=
    ZLattice.covolume_eq_measure_fundamentalDomain L _ hfund
  have hFfin : MeasureTheory.volume (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L)) ≠ ⊤ :=
    (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
  have hc : 0 < covol L := by
    rw [hC W L]
    exact ZLattice.covolume_pos L _
  have hF : MeasureTheory.volume (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L)) =
      ENNReal.ofReal (covol L) := by
    rw [hC W L, hcov, MeasureTheory.measureReal_def, ENNReal.ofReal_toReal hFfin]

  set t := covol L ^ ((1 : ℝ) / (n : ℝ)) with ht_def
  have ht : 0 ≤ t := Real.rpow_nonneg hc.le _
  have htn : t ^ n = covol L := by
    rw [ht_def, ← Real.rpow_natCast, ← Real.rpow_mul hc.le, one_div,
      inv_mul_cancel₀ (by exact_mod_cast hn.ne'), Real.rpow_one]
  let o := stdOrthonormalBasis ℝ W
  set S : Set W := {x | ∀ i, |o.repr x i| ≤ t} with hS
  have hnorm : ∀ x ∈ S, ‖x‖ ≤ Real.sqrt (n : ℝ) * t := by
    intro x hx
    rw [← o.repr.norm_map x, EuclideanSpace.norm_eq]
    calc Real.sqrt (∑ i, ‖o.repr x i‖ ^ 2) ≤ Real.sqrt (∑ _i : Fin n, t ^ 2) := by
          apply Real.sqrt_le_sqrt
          refine Finset.sum_le_sum fun i _ => ?_
          rw [Real.norm_eq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hx i) 2
      _ = Real.sqrt (n : ℝ) * t := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq ht]
  have hsymm : ∀ x ∈ S, -x ∈ S := by
    intro x hx i
    simpa [map_neg] using hx i
  have hconv : Convex ℝ S := by
    intro x hx y hy a c ha hc hac i
    simp only [map_add (f := _), map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    calc |a * o.repr x i + c * o.repr y i| ≤ |a * o.repr x i| + |c * o.repr y i| := abs_add_le _ _
      _ = a * |o.repr x i| + c * |o.repr y i| := by
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hc]
      _ ≤ a * t + c * t := by
          gcongr
          · exact hx i
          · exact hy i
      _ = t := by rw [← add_mul, hac, one_mul]
  have hclosed : IsClosed S := by
    rw [hS, Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const
  have hcpt : IsCompact S := by
    refine Metric.isCompact_of_isClosed_isBounded hclosed ?_
    refine (Metric.isBounded_closedBall (x := (0 : W)) (r := Real.sqrt (n : ℝ) * t)).subset ?_
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hnorm x hx
  have hSeq : S = (WithLp.ofLp ∘ o.measurableEquiv) ⁻¹'
      Set.Icc (fun _ => -t) (fun _ => t) := by
    ext x
    simp only [hS, Set.mem_setOf_eq, Set.mem_preimage, Function.comp_apply, Set.mem_Icc,
      Pi.le_def, abs_le, forall_and]
    rfl
  have hvolS : MeasureTheory.volume S = ENNReal.ofReal (t - -t) ^ n := by
    rw [hSeq, ((PiLp.volume_preserving_ofLp (Fin n)).comp
      o.measurePreserving_measurableEquiv).measure_preimage measurableSet_Icc.nullMeasurableSet,
      Real.volume_Icc_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hmeas : MeasureTheory.volume (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L)) *
      2 ^ n ≤ MeasureTheory.volume S := by
    rw [hF, hvolS, ← ENNReal.ofReal_pow (by linarith),
      show (2 : ENNReal) ^ n = ENNReal.ofReal (2 ^ n) by simp,
      ← ENNReal.ofReal_mul hc.le]
    apply le_of_eq
    congr 1
    rw [show t - -t = 2 * t by ring, mul_pow, htn, mul_comm]
  haveI : Nontrivial W := Module.nontrivial_of_finrank_pos hn
  haveI hLc : Countable L := b.equivFun.injective.countable
  haveI : Countable L.toAddSubgroup := hLc
  obtain ⟨x, hx0, hxS⟩ :=
    MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
      (L := L.toAddSubgroup) hfund hsymm hconv hcpt hmeas
  refine ⟨(x : W), x.2, ?_, hnorm _ hxS⟩
  intro h0
  exact hx0 (Subtype.ext h0)

theorem shortVector_of (hC : CovolEqCovolume.{u}) : ShortVector.{u} := by
  intro E _ _ _ L hL hne
  classical
  haveI : DiscreteTopology L := hL

  have hsub : ∀ x ∈ L, x ∈ Submodule.span ℝ (L : Set E) := fun x hx => Submodule.subset_span hx
  let L₀ : Submodule ℤ (Submodule.span ℝ (L : Set E)) :=
    L.comap ((Submodule.span ℝ (L : Set E)).subtype.restrictScalars ℤ)
  let e : L ≃ₗ[ℤ] L₀ :=
    { toFun := fun y => ⟨⟨y, hsub y y.2⟩, y.2⟩
      invFun := fun x => ⟨((x : Submodule.span ℝ (L : Set E)) : E), x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  haveI : DiscreteTopology L₀ := by
    refine DiscreteTopology.of_continuous_injective (f := e.symm) ?_ e.symm.injective
    exact Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
  have himg : (Submodule.span ℝ (L : Set E)).subtype '' (L₀ : Set _) = (L : Set E) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hsub x hx⟩, hx, rfl⟩
  haveI : IsZLattice ℝ L₀ := by
    refine ⟨?_⟩
    apply Submodule.map_injective_of_injective (Submodule.span ℝ (L : Set E)).injective_subtype
    rw [Submodule.map_span, himg, Submodule.map_top, Submodule.range_subtype]
  letI : MeasurableSpace (Submodule.span ℝ (L : Set E)) := borel _
  haveI : BorelSpace (Submodule.span ℝ (L : Set E)) := ⟨rfl⟩
  have hcov : covol L₀ = covol L :=
    covol_eq_of_linearEquiv_inner L L₀ e (fun _ _ => rfl)
  have hrk : finrank ℝ (Submodule.span ℝ (L : Set E)) = rk L := by
    rw [← ZLattice.rank ℝ L₀]
    exact e.finrank_eq.symm
  haveI : Nontrivial L := Submodule.nontrivial_iff_ne_bot.mpr hne
  have hpos : 0 < finrank ℝ (Submodule.span ℝ (L : Set E)) := by
    rw [hrk]
    exact Module.finrank_pos
  obtain ⟨x, hx, hx0, hxn⟩ := exists_short_vector_of_isZLattice hC L₀ hpos
  refine ⟨(x : E), hx, ?_, ?_⟩
  · intro h0
    exact hx0 (Subtype.ext h0)
  · rw [hrk, hcov] at hxn
    exact hxn

end Formalism.F
end
end
