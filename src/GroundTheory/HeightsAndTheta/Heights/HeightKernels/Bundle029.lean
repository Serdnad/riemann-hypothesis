module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle017
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle027
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.FieldChange
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionBounded
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle022
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle026
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField

noncomputable section

namespace SectionIndexNormAlt

variable {T : Type} {K' : Type} [Field K'] {y : (Σ _ : Unit, T) → K'}

theorem ratio_mem (p : Σ _ : Unit, T) (t : T) :
    y p / y ⟨(), t⟩ ∈ chartRingZ y (fun _ => t) :=
  Algebra.subset_adjoin ⟨p, rfl⟩

theorem mem_curveRing_iff {b : K'} :
    b ∈ curveRing y ↔ ∀ t : T, y ⟨(), t⟩ ≠ 0 → b ∈ chartRingZ y (fun _ => t) := by
  rw [mem_curveRing]
  refine ⟨fun h t ht => h (fun _ => t) (fun _ => ht), fun h c hc => ?_⟩
  have hc' : c = fun _ => c () := funext fun u => by cases u; rfl
  rw [hc']
  exact h (c ()) (hc ())

theorem mem_chartLat_iff [Fintype T] {z : K'} :
    z ∈ chartLat y (fun _ => 1) 1 ↔ ∀ t : T, y ⟨(), t⟩ ≠ 0 → z / y ⟨(), t⟩ ∈ chartRingZ y (fun _ => t) := by
  change (∀ c : Unit → T, _ → _) ↔ _
  refine ⟨fun h t ht => ?_, fun h c hc => ?_⟩
  · have := h (fun _ => t) (fun _ => ht)
    simpa [div_eq_mul_inv] using this
  · have hc' : c = fun _ => c () := funext fun u => by cases u; rfl
    rw [hc']
    simpa [div_eq_mul_inv] using h (c ()) (hc ())

theorem aeval_div_mem [Fintype T] {s : MRing (fun _ : Unit => T)} (hs : IsMultiHomog s (fun _ => 1))
    (t : T) : aeval y s / y ⟨(), t⟩ ∈ chartRingZ y (fun _ => t) := by
  classical

  rw [s.as_sum, map_sum, Finset.sum_div]
  refine Subalgebra.sum_mem _ fun m hm => ?_
  rw [aeval_monomial, mul_div_assoc]
  refine Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) ?_
  have hsum : ∑ p, m p = 1 := by
    rw [Fintype.sum_sigma, Fintype.sum_unique]
    exact hs m hm ()
  have key : m.prod (fun p e => y p ^ e) / y ⟨(), t⟩ = ∏ p, (y p / y ⟨(), t⟩) ^ m p := by
    rw [Finsupp.prod_fintype _ _ (by simp)]
    simp only [div_pow]
    rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, hsum, pow_one]
  rw [key]
  exact Subalgebra.prod_mem _ fun p _ => Subalgebra.pow_mem _ (ratio_mem p t) _

theorem exists_mul_mem {m : Ideal (curveRing y)} (hm : m.IsPrime) {t : T}
    (ht : ∀ u, ∃ a b : curveRing y, b ∉ m ∧ (b : K') * (y ⟨(), u⟩ / y ⟨(), t⟩) = a) {z : K'}
    (hz : z ∈ chartRingZ y (fun _ => t)) : ∃ b : curveRing y, b ∉ m ∧ (b : K') * z ∈ curveRing y := by
  have h1 : (1 : curveRing y) ∉ m := fun h => hm.ne_top ((Ideal.eq_top_iff_one _).mpr h)
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨⟨⟨⟩, u⟩, rfl⟩ := hx
    obtain ⟨a, b, hb, hab⟩ := ht u
    exact ⟨b, hb, by convert a.2 using 1⟩
  | algebraMap r =>
    exact ⟨1, h1, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨b1, hb1, h1'⟩ := hx
    obtain ⟨b2, hb2, h2'⟩ := hz
    refine ⟨b1 * b2, fun h => (hm.mem_or_mem h).elim hb1 hb2, ?_⟩
    have e : ((b1 * b2 : curveRing y) : K') * (x + z) = b2 * (b1 * x) + b1 * (b2 * z) := by
      push_cast; ring
    rw [e]
    exact add_mem (mul_mem b2.2 h1') (mul_mem b1.2 h2')
  | mul x z _ _ hx hz =>
    obtain ⟨b1, hb1, h1'⟩ := hx
    obtain ⟨b2, hb2, h2'⟩ := hz
    refine ⟨b1 * b2, fun h => (hm.mem_or_mem h).elim hb1 hb2, ?_⟩
    have e : ((b1 * b2 : curveRing y) : K') * (x * z) = (b1 * x) * (b2 * z) := by
      push_cast; ring
    rw [e]
    exact mul_mem h1' h2'

theorem coe_ne_zero_of_notMem {m : Ideal (curveRing y)} {b : curveRing y} (hb : b ∉ m) : (b : K') ≠ 0 :=
  fun h => hb (by rw [show b = 0 from Subtype.ext h]; exact m.zero_mem)

theorem genIndex_span_div [NumberField K'] [Fintype T] (hy : y ≠ 0) {x : K'} (hx : x ≠ 0) :
    genIndex (Submodule.span (𝓞 K') (Set.range fun p => y p / x)).toAddSubgroup
        (1 : Submodule (𝓞 K') K').toAddSubgroup =
      genIndex (Submodule.span (𝓞 K') (Set.range y)).toAddSubgroup (1 : Submodule (𝓞 K') K').toAddSubgroup *
        |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
  have hy' : (fun p => y p / x) ≠ 0 := by
    obtain ⟨p, hp⟩ := Function.ne_iff.mp hy
    exact Function.ne_iff.mpr ⟨p, div_ne_zero hp hx⟩
  rw [DualLineIndexAlt.genIndex_span_eq_finprod hy', DualLineIndexAlt.genIndex_span_eq_finprod hy]
  have e : ∀ w : FinitePlace K', ⨆ p, w (y p / x) = (⨆ p, w (y p)) * w x⁻¹ := by
    intro w
    simp only [div_eq_mul_inv, map_mul]
    exact (Real.iSup_mul_of_nonneg (apply_nonneg w _) _).symm
  simp_rw [e]
  rw [finprod_mul_distrib (hasFiniteMulSupport_iSup_place hy)
    (FinitePlace.hasFiniteMulSupport (inv_ne_zero hx)), FinitePlace.prod_eq_inv_abs_norm (inv_ne_zero hx)]
  have hN : Algebra.norm ℚ x⁻¹ = (Algebra.norm ℚ x)⁻¹ :=
    eq_inv_of_mul_eq_one_right (by rw [← map_mul, mul_inv_cancel₀ hx, map_one])
  rw [hN]
  push_cast
  rw [abs_inv, inv_inv]

theorem genIndex_span_pos [NumberField K'] [Fintype T] {p0 : Σ _ : Unit, T} (hp0 : y p0 ≠ 0) :
    0 < genIndex (Submodule.span (𝓞 K') (Set.range y)).toAddSubgroup
      (1 : Submodule (𝓞 K') K').toAddSubgroup := by
  have hy : y ≠ 0 := fun h => hp0 (by rw [h, Pi.zero_apply])
  rw [DualLineIndexAlt.genIndex_span_eq_finprod hy,
    finprod_eq_prod _ (hasFiniteMulSupport_iSup_place hy)]
  refine Finset.prod_pos fun w _ => ?_
  exact lt_of_lt_of_le (FinitePlace.pos_iff.mpr hp0) (le_ciSup (f := fun p => w (y p)) (Finite.bddAbove_range _) p0)

end SectionIndexNormAlt


open SectionIndexNormAlt in
theorem SectionIndexNorm.proof (hC : CurveCharts.Statement) (hI : InvertibleIdealIndex.Statement) :
    SectionIndexNorm.Statement := by
  intro T _ K' _ _ y s hP hs hsP
  obtain ⟨hfin, hrank, hloc⟩ := hC T K' y hP
  set x := aeval y s with hxdef
  have hx0 : x ≠ 0 := by
    intro h0
    apply hsP
    change s ∈ RingHom.ker (mConeMap y)
    rw [RingHom.mem_ker]
    erw [HilbertSamuel.SectionBounded.mConeMap_homog y hs]
    rw [← hxdef, h0, map_zero, zero_mul]
  obtain ⟨m0, hm0⟩ := Ideal.exists_maximal (curveRing y)
  obtain ⟨t1, ht1, hl1⟩ := hloc m0 hm0
  let f : K' →+ K' := AddMonoidHom.mulLeft x⁻¹
  have hf : ∀ z, f z = x⁻¹ * z := fun _ => rfl
  let a : (Σ _ : Unit, T) → K' := fun p => y p / x
  have key := hI K' (curveRing y) ((chartLat y (fun _ => 1) 1).map f) (Σ _ : Unit, T) a hfin ?_ ?_ ?_ ?_
  ·
    have hB : (curveRing y).toAddSubgroup = (curveMul y x).map f := by
      rw [curveMul, AddSubgroup.map_map]
      ext z
      simp [hf, hx0]
    have hinj : Function.Injective f := fun u v h => mul_left_cancel₀ (inv_ne_zero hx0) h
    rw [hB, KLinesLineDegree.genIndex_map_of_injective f hinj, genIndex_span_div ?_ hx0,
      Real.log_mul (genIndex_span_pos (p0 := ⟨(), t1⟩) ht1).ne'
        (abs_pos.mpr (by exact_mod_cast Algebra.norm_ne_zero_iff.mpr hx0)).ne',
      hrank, ← (letI : Module.Free (blockFnField y) K' := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (blockFnField y) K')] at key
    · have hF : (0 : ℝ) < Module.finrank ℚ (blockFnField y) := Nat.cast_pos.mpr Module.finrank_pos
      apply mul_left_cancel₀ hF.ne'
      push_cast at key
      linear_combination key
    · exact fun h => ht1 (by rw [h, Pi.zero_apply])
  ·
    intro b hb z hz
    obtain ⟨w, hw, rfl⟩ := AddSubgroup.mem_map.mp hz
    refine AddSubgroup.mem_map.mpr ⟨b * w, ?_, by rw [hf, hf]; ring⟩
    rw [mem_chartLat_iff] at hw ⊢
    intro t ht
    rw [mul_div_assoc]
    exact mul_mem (mem_curveRing_iff.mp hb t ht) (hw t ht)
  ·
    intro p
    refine AddSubgroup.mem_map.mpr ⟨y p, ?_, by rw [hf]; simp [a, div_eq_inv_mul]⟩
    exact mem_chartLat_iff.mpr fun t _ => ratio_mem p t
  ·
    rintro ⟨⟨⟩, u⟩
    obtain ⟨β, hβ, hβx⟩ := exists_mul_mem hm0.isPrime hl1 (aeval_div_mem hs t1)
    obtain ⟨c, b, hb, hbc⟩ := hl1 u
    refine ⟨(β : K') * (x / y ⟨(), t1⟩) * b, mul_mem hβx b.2, ?_, ?_⟩
    · exact mul_ne_zero (mul_ne_zero (coe_ne_zero_of_notMem hβ) (div_ne_zero hx0 ht1))
        (coe_ne_zero_of_notMem hb)
    · have e : (β : K') * (x / y ⟨(), t1⟩) * b * a ⟨(), u⟩ = β * c := by
        rw [← hbc]
        simp only [a]
        field_simp
      rw [e]
      exact mul_mem β.2 c.2
  ·
    intro m hm
    obtain ⟨t, ht, hl⟩ := hloc m hm
    refine ⟨⟨(), t⟩, fun z hz => ?_⟩
    obtain ⟨w, hw, rfl⟩ := AddSubgroup.mem_map.mp hz
    obtain ⟨b, hb, hbw⟩ := exists_mul_mem hm.isPrime hl (mem_chartLat_iff.mp hw t ht)
    refine ⟨b, ⟨_, hbw⟩, hb, ?_⟩
    simp only [hf, a]
    field_simp

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField Matrix

noncomputable section

namespace StandardDualBasePointFree

open DualPointsOnPlane

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T] [DecidableEq T]


omit [Fintype T] [DecidableEq T] in
theorem coord_integral (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) (c : T) (j : Fin i) :
    ∃ α : 𝓞 K, (α : K) = (b c : Fin i → K) j := by
  obtain ⟨α, hα⟩ := (b c).2 (Pi.single j 1) (Submodule.subset_span ⟨j, rfl⟩)
  exact ⟨α, hα.trans (dotProduct_single_one _ _)⟩


omit [DecidableEq T] in
theorem mConeMap_lin {Ω : Type} [Field Ω] (y : (Σ _ : Unit, T) → Ω) (a : T → ℤ) :
    mConeMap y (∑ t, C (a t) * X ⟨(), t⟩ : MRing (dualBlocks T)) =
      MvPolynomial.C (∑ t, (a t : Ω) * y ⟨(), t⟩) * MvPolynomial.X () := by

  rw [map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [mConeMap, aeval_X, map_mul, map_intCast, eq_intCast]
  ring

end StandardDualBasePointFree


open StandardDualBasePointFree DualPointsOnPlane in
theorem DualStdBasePtFree.proof : DualStdBasePtFree.Statement := by
  intro K _ _ i T _ _ b k₂ c
  cases k₂
  refine ⟨2, ?_⟩
  have hprod : (∏ k : Unit, (X ⟨k, c k⟩ : MRing (dualBlocks T))) = X ⟨(), c ()⟩ := Fintype.prod_unique _
  rw [hprod]
  choose α hα using coord_integral b (c ())
  let am := algebraMap (MvPolynomial (Fin i) K) (ProjField K i)
  let y := dualLatticeCoord b
  let L : Fin i → MRing (dualBlocks T) := fun j => ∑ s, C (mulMat b (α j) (c ()) s) * X ⟨(), s⟩

  have hA : ∀ j, ∑ t, (dualStdCoordMat b () j t : ProjField K i) * y ⟨(), t⟩ = am (X j) := by
    intro j
    have hpoly : ∑ t, (dualStdCoordMat b () j t : MvPolynomial (Fin i) K) *
        ∑ l, C ((b t : Fin i → K) l) * X l = X j := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      have hc : ∀ l, ∑ t, (dualStdCoordMat b () j t : K) * (b t : Fin i → K) l = (Pi.single j (1 : K) : Fin i → K) l := by
        intro l
        have h := congrFun (dualStdCoordMat_sum b j) l
        simpa only [Finset.sum_apply, Pi.smul_apply, Pi.mul_apply, Pi.intCast_apply, zsmul_eq_mul] using h
      have hc' : ∀ l, ∑ t, (dualStdCoordMat b () j t : MvPolynomial (Fin i) K) * (C ((b t : Fin i → K) l) * X l) =
          C ((Pi.single j (1 : K) : Fin i → K) l) * X l := by
        intro l

        rw [← hc l, map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun t _ => ?_
        simp only [map_mul, map_intCast]
        ring
      simp only [hc']
      rw [Finset.sum_eq_single j (fun l _ hl => by simp [hl]) (by simp)]
      simp
    have h := congrArg am hpoly

    simpa only [am, y, dualLatticeCoord, map_sum, map_mul, map_intCast] using h

  have hS : ∀ j, ∑ s, (mulMat b (α j) (c ()) s : ProjField K i) * y ⟨(), s⟩ =
      am (C (α j : K)) * y ⟨(), c ()⟩ := by
    intro j
    have hlin : ∑ t, (mulMat b (α j) (c ()) t : MvPolynomial (Fin i) K) *
        ∑ l, C ((b t : Fin i → K) l) * X l = C (α j : K) * ∑ l, C ((b (c ()) : Fin i → K) l) * X l := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => ?_
      have h := congrArg (C : K → MvPolynomial (Fin i) K) (mulMat_sum b (α j) (c ()) l)

      simp only [map_sum, map_mul, map_intCast] at h
      rw [← mul_assoc, ← h, Finset.sum_mul]
      refine Finset.sum_congr rfl fun t _ => ?_
      ring
    have h := congrArg am hlin

    simpa only [am, y, dualLatticeCoord, map_sum, map_mul, map_intCast] using h

  have hy : y ⟨(), c ()⟩ = ∑ j, am (C (α j : K)) * am (X j) := by

    simp only [y, am, dualLatticeCoord, map_sum, map_mul, hα]
  have key : X ⟨(), c ()⟩ ^ 2 - ∑ j, linForm (ι₂ := PBlk i) (dualStdCoordMat b) ⟨(), j⟩ * L j ∈ dualIdeal b := by
    show _ ∈ RingHom.ker (mConeMap (dualLatticeCoord b))

    rw [RingHom.mem_ker, map_sub, sub_eq_zero, map_sum]
    have hl : ∀ j, mConeMap (dualLatticeCoord b) (linForm (ι₂ := PBlk i) (dualStdCoordMat b) ⟨(), j⟩) =
        MvPolynomial.C (am (X j)) * MvPolynomial.X () := by
      intro j
      rw [← hA j]
      exact mConeMap_lin _ _
    have hL : ∀ j, mConeMap (dualLatticeCoord b) (L j) =
        MvPolynomial.C (am (C (α j : K)) * y ⟨(), c ()⟩) * MvPolynomial.X () := by
      intro j
      rw [← hS j]
      exact mConeMap_lin _ _
    have hX : mConeMap (dualLatticeCoord b) (X ⟨(), c ()⟩ : MRing (dualBlocks T)) =
        MvPolynomial.C (y ⟨(), c ()⟩) * MvPolynomial.X () := by
      simp only [mConeMap, aeval_X, y]
    simp only [map_mul, map_pow, hl, hL, hX]
    symm
    calc ∑ j, MvPolynomial.C (am (X j)) * MvPolynomial.X () *
          (MvPolynomial.C (am (C (α j : K))) * MvPolynomial.C (y ⟨(), c ()⟩) * MvPolynomial.X ())
        = MvPolynomial.C ((∑ j, am (C (α j : K)) * am (X j)) * y ⟨(), c ()⟩) * MvPolynomial.X () ^ 2 := by

          rw [Finset.sum_mul, map_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [map_mul]
          ring
      _ = _ := by
          rw [← hy, map_mul]
          ring
  have hQ : ∑ j, linForm (ι₂ := PBlk i) (dualStdCoordMat b) ⟨(), j⟩ * L j ∈
      Ideal.span (Set.range fun j : PBlk i () => linForm (ι₂ := PBlk i) (dualStdCoordMat b) ⟨(), j⟩) :=
    Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨j, rfl⟩)
  have h := Ideal.add_mem _ (Ideal.mem_sup_left key) (Ideal.mem_sup_right hQ)
  rwa [sub_add_cancel] at h

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 NumberField Matrix

noncomputable section

namespace StandardDualMetricPullback

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T] [DecidableEq T]


omit [DecidableEq T] in
theorem linApply_eq (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i)))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (z : (Σ _ : Unit, T) → ℂ) (j : Fin i) :
    linApply (ι₂ := PBlk i) (dualStdCoordMat b) z ⟨(), j⟩ =
      ∑ τ : K →+* ℂ, dualRecover b hb (fun t => z ⟨(), t⟩) (τ, j) := by
  classical
  set W := dualRecover b hb (fun t => z ⟨(), t⟩)
  have hMW : dualEmbMatrix b *ᵥ W = fun t => z ⟨(), t⟩ :=
    (LinearEquiv.ofBijective _ hb).apply_symm_apply _
  have hA : ∀ p : (K →+* ℂ) × Fin i,
      ∑ t, (dualStdCoordMat b () j t : ℂ) * dualEmbMatrix b t p = p.1 ((Pi.single j 1 : Fin i → K) p.2) := by
    intro p

    rw [← dualStdCoordMat_sum b j, Finset.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp [dualEmbMatrix, Pi.smul_apply, zsmul_eq_mul]
  calc linApply (ι₂ := PBlk i) (dualStdCoordMat b) z ⟨(), j⟩
      = ∑ t, (dualStdCoordMat b () j t : ℂ) * ∑ p, dualEmbMatrix b t p * W p := by
        simp only [linApply]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [← congrFun hMW t]
        rfl
    _ = ∑ p, (∑ t, (dualStdCoordMat b () j t : ℂ) * dualEmbMatrix b t p) * W p := by
        simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
        exact Finset.sum_comm
    _ = ∑ τ : K →+* ℂ, W (τ, j) := by
        simp only [hA, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [Finset.sum_eq_single j (fun j' _ hj' => by simp [Ne.symm hj']) (by simp)]
        simp

end StandardDualMetricPullback


open StandardDualMetricPullback in
theorem DualStdMetricPull.proof : DualStdMetricPull.Statement := by
  intro K _ _ i T _ _ b hb z hz
  set W := dualRecover b hb (fun t => z ⟨(), t⟩)
  obtain ⟨σ, hσ⟩ := DualPtsOnPlane.proof K i _ T b hb z hz
  have hy : ∀ j, linApply (ι₂ := PBlk i) (dualStdCoordMat b) z ⟨(), j⟩ = W (σ, j) := fun j => by
    rw [linApply_eq b hb z j]
    exact Finset.sum_eq_single σ (fun τ _ hτ => hσ τ hτ j) (by simp)
  have hterm : ∀ τ, ((star fun j => W (τ, j)) ⬝ᵥ
      ((HermLattice.standard K i).metric τ *ᵥ fun j => W (τ, j))).re = ∑ j, ‖W (τ, j)‖ ^ 2 := by
    intro τ
    simp only [HermLattice.standard, one_mulVec, dotProduct, Pi.star_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [RCLike.star_def, Complex.conj_mul']
    norm_cast
  show Real.sqrt (dualNormSq b hb fun t => z ⟨(), t⟩) = _
  rw [show dualNormSq b hb (fun t => z ⟨(), t⟩) = ∑ τ, ∑ j, ‖W (τ, j)‖ ^ 2 from
    Finset.sum_congr rfl fun τ _ => hterm τ]
  simp only [fsMulti, HermLine.ofMetrics, fsMetric, Finset.univ_unique, Finset.prod_singleton, zpow_one,
    EuclideanSpace.norm_eq]
  congr 1
  rw [Finset.sum_eq_single σ (fun τ _ hτ => by simp [W, hσ τ hτ]) (by simp)]
  exact Finset.sum_congr rfl fun j _ => by rw [← hy j]

end

end GroundTheory.Heights₂.Heights
end
