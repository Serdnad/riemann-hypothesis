module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLineDegreeDual
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeight
public import Mathlib.RingTheory.SimpleRing.Principal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

noncomputable section

def DualLatticeModPrime.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (𝔭 : Ideal (𝓞 K)), 𝔭.IsMaximal →
    ∃ σ : dualLattice F →+ (Fin i → 𝓞 K ⧸ 𝔭), Function.Surjective σ ∧
      ∀ (μ : 𝓞 K) (φ ψ : dualLattice F), (ψ : Fin i → K) = algebraMap (𝓞 K) K μ • (φ : Fin i → K) →
        σ ψ = Ideal.Quotient.mk 𝔭 μ • σ φ

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField
open scoped ComplexOrder

noncomputable section

def DualTopBasisChange.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T T₂ : Type) [Fintype T]
    [DecidableEq T] [Fintype T₂] [DecidableEq T₂] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)))
    (b₂ : Module.Basis T₂ ℤ (dualLattice F))
    (hb₂ : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b₂))) (II : IntersectionSystem),
    1 ≤ i → IsIntersectionSystem II →
    II Unit (dualBlocks T₂) (dualIdeal b₂) i (fun _ => dualLine F b₂ hb₂) =
      II Unit (dualBlocks T) (dualIdeal b) i (fun _ => dualLine F b hb)

def dualBasisStandardNeg : Module.Basis (Fin 1) ℤ (dualLattice (HermLattice.standard ℚ 1)) :=
  (dualBasisStandard.map (LinearEquiv.neg ℤ)).reindex (Equiv.ofUnique Unit (Fin 1))

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField
open scoped ComplexOrder

noncomputable section

def HermLattice.withStdMetric {K : Type} [Field K] [NumberField K] {i : ℕ} (F : HermLattice K i) :
    HermLattice K i where
  lattice := F.lattice
  fg := F.fg
  span_eq := F.span_eq
  metric := fun _ => 1
  posDef := fun _ => Matrix.PosDef.one
  conj := fun _ => by simp

def DualTopMetricChange.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (II : IntersectionSystem),
    1 ≤ i → IsIntersectionSystem II →
    II Unit (dualBlocks T) (dualIdeal b) i (fun _ => dualLine F b hb) =
      II Unit (dualBlocks T) (dualIdeal b) i (fun _ => dualLine F.withStdMetric b hb) +
        (F.withStdMetric.degree - F.degree) *
          geomDeg (grassIdeal 1 1 (i - 1)) (fsMulti (plBlocks 1 1 (i - 1))) (1 * 1 * (i - 1))

def DualTopLatticeChange.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T T' : Type) [Fintype T]
    [DecidableEq T] [Fintype T'] [DecidableEq T'] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)))
    (b' : Module.Basis T' ℤ (dualLattice (HermLattice.standard K i)))
    (hb' : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b'))) (II : IntersectionSystem),
    1 ≤ i → IsIntersectionSystem II →
    II Unit (dualBlocks T) (dualIdeal b) i (fun _ => dualLine F.withStdMetric b hb) =
      II Unit (dualBlocks T') (dualIdeal b') i (fun _ => dualLine (HermLattice.standard K i) b' hb') -
        F.withStdMetric.degree *
          geomDeg (grassIdeal 1 1 (i - 1)) (fsMulti (plBlocks 1 1 (i - 1))) (1 * 1 * (i - 1))

def DualTopStandard.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (T : Type) [Fintype T] [DecidableEq T]
    (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i)))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (II : IntersectionSystem),
    1 ≤ i → IsIntersectionSystem II →
    II Unit (dualBlocks T) (dualIdeal b) i (fun _ => dualLine (HermLattice.standard K i) b hb) =
      (Module.finrank ℚ K : ℝ) *
        II (Fin 1) (plBlocks 1 1 (i - 1)) (grassIdeal 1 1 (i - 1)) (1 * 1 * (i - 1) + 1)
          (fun _ => fsMulti (plBlocks 1 1 (i - 1)))

def DualGeomDegStandard.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))), 1 ≤ i →
    geomDeg (dualIdeal b) (dualLine F b hb) (i - 1) =
      (Module.finrank ℚ K : ℝ) *
        geomDeg (grassIdeal 1 1 (i - 1)) (fsMulti (plBlocks 1 1 (i - 1))) (1 * 1 * (i - 1))

def HermLattice.scaledExample : HermLattice ℚ 1 where
  lattice := (HermLattice.standard ℚ 1).lattice
  fg := (HermLattice.standard ℚ 1).fg
  span_eq := (HermLattice.standard ℚ 1).span_eq
  metric := fun _ => Matrix.diagonal fun _ => (4 : ℂ)
  posDef := fun _ => Matrix.PosDef.diagonal fun _ => by norm_num
  conj := fun _ => by
    ext a c
    by_cases h : a = c <;> simp [h, map_ofNat]

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo

theorem LineOfLargeDegreeFromZ.proofDual (hBasis : DualLatticeBasisExists.Statement)
    (hBij : DualEmbBijective.Statement) (hArith : DualArithVar.Statement)
    (hSemi : DualLineSemipositive.Statement) (hNef : NefOfNonneg.Statement)
    (hConj : DualLineConj.Statement) (hPt : DualPointLineDegree.Statement)
    (hTop : DualTopBound.Statement) (hPos : DualGeomDegPos.Statement) :
    LineOfLargeDegreeFromZ.Statement := by
  intro hZ1 hZ2 hEx K _ _ i hi F ε hε
  obtain ⟨II, hII⟩ := hEx
  obtain ⟨T, _, _, ⟨b⟩⟩ := hBasis K i F
  have hb := hBij K i F T b
  set A := dualLine F b hb with hA
  set e : ℝ := -F.slope + 1 / 2 * Real.log i + ε with he
  by_contra hne
  push Not at hne
  have hW : ∀ W : Ideal (MRing (dualBlocks T)), IsArithVar W 1 → dualIdeal b ≤ W →
      e * degC W ≤ II Unit (dualBlocks T) W 1 ![A] := by
    intro W hW1 hPW
    obtain ⟨hdeg, K', iF, iN, iA, v, hv, hline⟩ := hPt K i F T b hb II hII W hW1 hPW
    have hlt := hne K' iF iN iA v hv
    rw [hline] at hlt
    have hd : (0 : ℝ) < degC W := by exact_mod_cast hdeg
    have h1 : e < II Unit (dualBlocks T) W 1 ![A] / degC W := by
      rw [neg_div] at hlt
      linarith
    exact ((lt_div_iff₀ hd).mp h1).le
  have hV : IsArithVar (dualIdeal b) (i - 1 + 1) := by
    rw [Nat.sub_add_cancel hi]; exact hArith K i F T b hi
  have hZ := hZ1 Unit (dualBlocks T) (dualIdeal b) ⊥ (i - 1) A e II hII hV
    bot_le (hSemi K i F T b hb) (hNef _ _ _ _ fun _ => zero_le_one) (hConj K i F T b hb) hW
  rw [Nat.sub_add_cancel hi] at hZ
  have hT := hTop hZ2 K i F T b hb II hi hII
  have hG := hPos K i F T b hb hi
  have hi' : (0 : ℝ) < i := by exact_mod_cast hi
  have key : (i : ℝ) * e * geomDeg (dualIdeal b) A (i - 1) ≤
      (i : ℝ) * (-F.slope + 1 / 2 * Real.log i) * geomDeg (dualIdeal b) A (i - 1) := hZ.trans hT
  have : (i : ℝ) * ε * geomDeg (dualIdeal b) A (i - 1) ≤ 0 := by
    rw [he] at key
    nlinarith
  have : 0 < (i : ℝ) * ε * geomDeg (dualIdeal b) A (i - 1) :=
    mul_pos (mul_pos hi' hε) hG
  linarith

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix NumberField

noncomputable section

namespace DualArithmeticVariety

variable {K : Type} [Field K]

def evalForm (m : ℕ) : (Fin m → K) →ₗ[K] ProjField K m :=
  Fintype.linearCombination K fun j => algebraMap (MvPolynomial (Fin m) K) (ProjField K m) (X j)

theorem algebraicIndependent_gen (m : ℕ) :
    AlgebraicIndependent K fun j : Fin m =>
      algebraMap (MvPolynomial (Fin m) K) (ProjField K m) (X j) :=
  (MvPolynomial.algebraicIndependent_X (Fin m) K).map'
    (f := IsScalarTower.toAlgHom K (MvPolynomial (Fin m) K) (ProjField K m))
    (IsFractionRing.injective _ _)

theorem evalForm_ne_zero {m : ℕ} {φ : Fin m → K} (hφ : φ ≠ 0) : evalForm m φ ≠ 0 := by
  intro h0
  apply hφ
  apply (algebraicIndependent_gen m).linearIndependent.fintypeLinearCombination_injective
  simpa only [evalForm, map_zero] using h0

theorem mem_of_gen_mem {m : ℕ} (E : IntermediateField K (ProjField K m))
    (h : ∀ j, algebraMap (MvPolynomial (Fin m) K) (ProjField K m) (X j) ∈ E) (z : ProjField K m) :
    z ∈ E := by
  have hp : ∀ p : MvPolynomial (Fin m) K, algebraMap _ (ProjField K m) p ∈ E := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C c =>
      rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
      exact E.algebraMap_mem c
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p j hp => rw [map_mul]; exact mul_mem hp (h j)
  obtain ⟨p, q, -, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial (Fin m) K) z
  exact div_mem (hp p) (hp q)

theorem isAlgebraic_of_adjoin {m : ℕ} (S : Set (ProjField K m))
    (h : ∀ z, z ∈ IntermediateField.adjoin K S) :
    Algebra.IsAlgebraic (Algebra.adjoin K S) (ProjField K m) := by
  rw [← IntermediateField.isAlgebraic_adjoin_iff_top]
  exact ⟨fun z => isAlgebraic_algebraMap (⟨z, h z⟩ : IntermediateField.adjoin K S)⟩

theorem trdeg_eq (m : ℕ) : Cardinal.mk (Fin m) = Algebra.trdeg K (ProjField K m) :=
  ((algebraicIndependent_gen m).isTranscendenceBasis_iff_isAlgebraic.mpr
    (isAlgebraic_of_adjoin _ (mem_of_gen_mem _ fun j =>
      IntermediateField.subset_adjoin _ _ ⟨j, rfl⟩))).cardinalMk_eq_trdeg

variable [NumberField K] {i : ℕ}

theorem span_dualLattice (F : HermLattice K i) :
    Submodule.span K (dualLattice F : Set (Fin i → K)) = ⊤ := by
  classical
  refine Submodule.eq_top_iff'.mpr fun v => ?_
  obtain ⟨S, hS⟩ := F.fg
  obtain ⟨N, hN, hint⟩ := exists_integral_multiples ℤ ℚ (S.image fun g => v ⬝ᵥ g)
  have hmem : (N : K) • v ∈ dualLattice F := by
    intro x hx
    rw [← hS] at hx
    induction hx using Submodule.span_induction with
    | mem g hg =>
      have hg' := hint _ (Finset.mem_image_of_mem _ hg)
      rw [smul_dotProduct, Int.cast_smul_eq_zsmul]
      exact RingHom.mem_range.mpr ((IsIntegralClosure.isIntegral_iff (A := 𝓞 K)).mp hg')
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨c, hc⟩ := hy
      exact ⟨a + c, by rw [dotProduct_add, map_add (f := _), ha, hc]⟩
    | smul r x _ hx =>
      obtain ⟨a, ha⟩ := hx
      refine ⟨r * a, ?_⟩
      rw [dotProduct_smul, map_mul, ha]
      rfl
  have hN' : (N : K) ≠ 0 := Int.cast_ne_zero.mpr hN
  have := Submodule.smul_mem (Submodule.span K (dualLattice F : Set (Fin i → K))) (N : K)⁻¹
    (Submodule.subset_span hmem)
  rwa [inv_smul_smul₀ hN'] at this

variable {F : HermLattice K i} {T : Type}

theorem span_basis [Fintype T] (b : Module.Basis T ℤ (dualLattice F)) :
    Submodule.span K (Set.range fun t => (b t : Fin i → K)) = ⊤ := by
  refine eq_top_iff.mpr ((span_dualLattice F).symm.le.trans (Submodule.span_le.mpr fun φ hφ => ?_))
  have h := congrArg Subtype.val (b.sum_repr ⟨φ, hφ⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at h
  rw [← h]
  exact Submodule.sum_mem _ fun t _ => zsmul_mem (Submodule.subset_span (Set.mem_range_self t)) _

theorem dualLatticeCoord_eq (b : Module.Basis T ℤ (dualLattice F)) (t : T) :
    dualLatticeCoord b ⟨(), t⟩ = evalForm i (b t : Fin i → K) := by

  rw [dualLatticeCoord, evalForm, Fintype.linearCombination_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, Algebra.smul_def, IsScalarTower.algebraMap_apply K (MvPolynomial (Fin i) K),
    MvPolynomial.algebraMap_eq]

end DualArithmeticVariety


open DualArithmeticVariety in
theorem DualArithVar.proof (h : CoordConeArithVar.Statement) : DualArithVar.Statement := by
  intro K _ _ i F T _ _ b hi
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  obtain ⟨κ, a, -, hsp, hli⟩ := exists_linearIndependent' K fun t => (b t : Fin (n + 1) → K)
  rw [span_basis b] at hsp
  let B : Module.Basis κ K (Fin (n + 1) → K) := Module.Basis.mk hli hsp.ge
  let e : Fin (n + 1) ≃ κ := (B.indexEquiv (Pi.basisFun K (Fin (n + 1)))).symm
  let u : Fin (n + 1) → T := a ∘ e
  let w : Fin (n + 1) → ProjField K (n + 1) := fun l => evalForm (n + 1) (b (u l) : Fin (n + 1) → K)
  let s : Fin n → ProjField K (n + 1) := fun l => w l.succ / w 0
  let v : Fin (n + 1) → ProjField K (n + 1) := Fin.cons (w 0) s
  have hy := dualLatticeCoord_eq b
  have hw0 : w 0 ≠ 0 := evalForm_ne_zero (hli.ne_zero (e 0))
  have hspw : ∀ ψ, evalForm (n + 1) ψ ∈ Submodule.span K (Set.range w) := by
    intro ψ
    have hψ : ψ ∈ Submodule.span K (Set.range (((fun t => (b t : Fin (n + 1) → K)) ∘ a) ∘ e)) := by
      rw [EquivLike.range_comp, hsp]
      exact Submodule.mem_top
    have := Submodule.mem_map_of_mem (f := evalForm (n + 1)) hψ
    rw [Submodule.map_span, ← Set.range_comp] at this
    exact this
  have hwE : ∀ l, w l ∈ IntermediateField.adjoin K (Set.range v) := by
    intro l
    have hv : ∀ l, v l ∈ IntermediateField.adjoin K (Set.range v) :=
      fun l => IntermediateField.subset_adjoin _ _ ⟨l, rfl⟩
    induction l using Fin.cases with
    | zero => exact hv 0
    | succ m =>
      have := mul_mem (hv m.succ) (hv 0)
      simpa [v, s, div_mul_cancel₀ _ hw0] using this
  have hall : ∀ z, z ∈ IntermediateField.adjoin K (Set.range v) := by
    refine mem_of_gen_mem _ fun j => ?_
    have hX : algebraMap (MvPolynomial (Fin (n + 1)) K) (ProjField K (n + 1)) (X j) =
        evalForm (n + 1) (Pi.single j 1) := by
      rw [evalForm, Fintype.linearCombination_apply_single, one_smul]
    rw [hX]
    exact (Submodule.span_le (p := (IntermediateField.adjoin K (Set.range v)).toSubalgebra.toSubmodule)).mpr
      (by rintro _ ⟨l, rfl⟩; exact hwE l) (hspw _)
  have hv : AlgebraicIndependent K v := by
    have := isAlgebraic_of_adjoin _ hall
    exact (Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite K v (trdeg_eq (n + 1)).le).1
  have hs : AlgebraicIndependent ℚ s :=
    (hv.comp Fin.succ (Fin.succ_injective _)).restrictScalars (algebraMap ℚ K).injective
  have hint : ∀ z ∈ Submodule.span K (Set.range w),
      IsIntegral (IntermediateField.adjoin ℚ (Set.range s)) (z / w 0) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨l, rfl⟩ := hz
      induction l using Fin.cases with
      | zero => rw [div_self hw0]; exact isIntegral_one
      | succ m =>
        exact isIntegral_algebraMap (x := (⟨s m, IntermediateField.subset_adjoin _ _ ⟨m, rfl⟩⟩ :
          IntermediateField.adjoin ℚ (Set.range s)))
    | zero => rw [zero_div]; exact isIntegral_zero
    | add x y _ _ hx hy => rw [add_div]; exact hx.add hy
    | smul c x _ hx =>
      rw [Algebra.smul_def, mul_div_assoc]
      set_option synthInstance.maxHeartbeats 200000 in
        exact ((Algebra.IsIntegral.isIntegral (R := ℚ) c).map
          (IsScalarTower.toAlgHom ℚ K (ProjField K (n + 1)))).tower_top.mul hx
  refine h Unit (dualBlocks T) (ProjField K (n + 1)) (dualLatticeCoord b) (fun _ => u 0) n s ⟨()⟩
    (fun _ => by rw [hy]; exact hw0) hs (fun l => IntermediateField.subset_adjoin _ _ ⟨⟨(), u l.succ⟩, ?_⟩) ?_
  · show dualLatticeCoord b ⟨(), u l.succ⟩ / dualLatticeCoord b ⟨(), u 0⟩ = w l.succ / w 0
    rw [hy, hy]
  · rintro r ⟨⟨⟨⟩, t⟩, rfl⟩
    show IsAlgebraic _ (dualLatticeCoord b ⟨(), t⟩ / dualLatticeCoord b ⟨(), u 0⟩)
    rw [hy, hy]
    exact (hint _ (hspw _)).isAlgebraic

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField

noncomputable section

def stackedDiag {T : Type} [DecidableEq T] (a : T → ℤ) : ∀ _ : Unit, T → T → ℤ :=
  fun _ t s => if t = s then a t else 0

abbrev stackedBlocks (T : Type) : Unit ⊕ Unit → Type := Sum.elim (dualBlocks T) (dualBlocks T)

def stackedGraph {K : Type} [Field K] [NumberField K] {i : ℕ} {F' : HermLattice K i} {T : Type} [Fintype T]
    [DecidableEq T] (b' : Module.Basis T ℤ (dualLattice F')) (a : T → ℤ) : Ideal (MRing (stackedBlocks T)) :=
  graphIdeal (dualIdeal b') (linForm (stackedDiag a))

def graphFirst {T : Type} (t : T) : MRing (stackedBlocks T) := X ⟨Sum.inl (), t⟩

def graphSecond {T : Type} (t : T) : MRing (stackedBlocks T) := X ⟨Sum.inr (), t⟩

def degFirst : Unit ⊕ Unit → ℤ := pullDeg (Sum.inl : Unit → Unit ⊕ Unit) fun _ => 1

def degSecond : Unit ⊕ Unit → ℤ := pullDeg (Sum.inr : Unit → Unit ⊕ Unit) fun _ => 1

def DualStackedGraphImage.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    1 ≤ i → (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    imageZ inrV (stackedGraph b' a) = dualIdeal b ∧
      ∀ (G : GenFibre inrV (stackedGraph b' a))
        (J : IFamily G.Φ (fibreIdx (stackedBlocks T) (Sum.inr : Unit → Unit ⊕ Unit))),
        IsFieldIntersection J → J (fibreIdeal Sum.inr G) 0 Fin.elim0 = 1

def DualStackedGraphHorizontal.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    1 ≤ i → (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    ∀ (t : T) (W : Ideal (MRing (stackedBlocks T))), IsHorizontal W →
      (W ∈ divSupp (stackedGraph b' a) (graphSecond t) ↔
        W ∈ divSupp (stackedGraph b' a) (C (a t) * graphFirst t)) ∧
      (W ∈ divSupp (stackedGraph b' a) (graphSecond t) →
        multAt (stackedGraph b' a ⊔ Ideal.span {graphSecond t}) W =
          multAt (stackedGraph b' a ⊔ Ideal.span {C (a t) * graphFirst t}) W)

def DualStackedGraphFibre.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    1 ≤ i → F'.lattice < F.lattice →
    (∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice) →
    (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    ∀ (t : T) (L : Fin (i - 1) → HermLine (stackedBlocks T)),
      (∀ j, (L j).a = degFirst ∨ (L j).a = degSecond) →
      ((∀ j, (L j).a = degSecond) →
        vertR (stackedGraph b' a) L (graphSecond t) - vertR (stackedGraph b' a) L (C (a t) * graphFirst t) =
          -∑ s, Real.log |(a s : ℝ)|) ∧
      ((∃ j, (L j).a = degFirst) →
        vertR (stackedGraph b' a) L (graphSecond t) - vertR (stackedGraph b' a) L (C (a t) * graphFirst t) = 0)

theorem degFirst_inr : degFirst (Sum.inr ()) = 0 := by
  rw [degFirst, pullDeg, Function.extend_apply' _ _ _ (by rintro ⟨u, hu⟩; exact Sum.inl_ne_inr hu)]
  rfl

theorem degSecond_inr : degSecond (Sum.inr ()) = 1 := by
  rw [degSecond, pullDeg, Sum.inr_injective.extend_apply]

end

end GroundTheory.Heights₂.Heights
end
