module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle041
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle018
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle017
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle016
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle014
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle020
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle011
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PFlagRatioTrdeg
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle013
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Assembly
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle016
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle006

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights MvPolynomial Matrix

noncomputable section

namespace GrassHeightEAux

theorem log_block (j m : ℕ) (e : ℝ) (he : UnitDetBound m j e) (Z : Matrix (Fin j) (Fin m) ℂ)
    (hZ : ∀ a b, ‖Z a b‖ = 1) (a : ℂ) (ha : a ≠ 0) (v : PlIdx j m → ℂ)
    (hv : ∀ I, v I = a * (colsOf (onePipe Z) I).det) :
    -e ≤ Real.log (‖a‖ / ‖WithLp.toLp 2 v‖) := by
  set S : ℝ := ∑ I : PlIdx j m, ‖(colsOf (onePipe Z) I).det‖ ^ 2 with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hnorm : ‖WithLp.toLp 2 v‖ = ‖a‖ * Real.sqrt S := by
    rw [EuclideanSpace.norm_eq]
    have hs : ∑ I, ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (PlIdx j m)) I‖ ^ 2 = ‖a‖ ^ 2 * S := by
      rw [hSdef, Finset.mul_sum]
      refine Finset.sum_congr rfl fun I _ => ?_
      simp [hv, mul_pow]
    rw [hs, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hdet : S = (1 + Z * Zᴴ).det.re := by
    rw [← PlueckerNormSq.full j m Z, Complex.ofReal_re]
  have hb := he Zᴴ fun a b => by rw [conjTranspose_apply, norm_star, hZ b a]
  rw [conjTranspose_conjTranspose, det_one_add_mul_comm, ← hdet] at hb
  rw [hnorm, div_mul_cancel_left₀ ha'.ne', Real.log_inv, Real.log_sqrt hS0]
  linarith

end GrassHeightEAux


open GrassHeightEAux in
theorem RootLogNormBoundE.full : RootLogNormBoundE.Statement := by
  intro f j m e ζ he hζ z hz
  have h₁ := RootAnchorNonzero.proof
  have hpos : ∀ τ : Fin f, 0 < ‖WithLp.toLp 2 (fun I : PlIdx j m => z ⟨τ, I⟩)‖ := fun τ =>
    (fsMetric (ι := PlIdx j m)).pos _ fun h0 => by
      obtain ⟨i, hi⟩ := hz.1 τ
      exact hi (congrFun h0 i)
  have key : ∀ τ : Fin f, -e ≤
      Real.log (‖z ⟨τ, plAnchor j m⟩‖ / ‖WithLp.toLp 2 (fun I : PlIdx j m => z ⟨τ, I⟩)‖) := by
    intro τ
    obtain ⟨ζ', hζ', hz'⟩ := RootPointConj.full f j m ζ hζ z hz τ
    exact log_block j m e he ζ' (fun a b => by
        obtain ⟨k, hk, h⟩ := hζ' a b
        exact Complex.norm_eq_one_of_pow_eq_one h hk.ne')
      _ (h₁ f j m ζ hζ z hz τ) _ hz'
  have hne : ∀ τ ∈ (Finset.univ : Finset (Fin f)),
      ‖z ⟨τ, plAnchor j m⟩‖ / ‖WithLp.toLp 2 (fun I : PlIdx j m => z ⟨τ, I⟩)‖ ≠ 0 := fun τ _ =>
    div_ne_zero (norm_ne_zero_iff.mpr (h₁ f j m ζ hζ z hz τ)) (hpos τ).ne'
  have e' : logNorm (fsMulti (plBlocks f j m)) (rootAnchorSection f j m) z =
      ∑ τ, Real.log (‖z ⟨τ, plAnchor j m⟩‖ / ‖WithLp.toLp 2 (fun I : PlIdx j m => z ⟨τ, I⟩)‖) := by
    rw [← Real.log_prod hne]
    simp [logNorm, fsMulti, HermLine.ofMetrics, fsMetric, rootAnchorSection, Finset.prod_div_distrib]
  rw [e']
  calc -((f : ℝ) * e) = ∑ _τ : Fin f, -e := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    _ ≤ _ := Finset.sum_le_sum fun τ _ => key τ

theorem RootHeightE.full : RootHeightE.Statement := by
  intro f j m e ζ hf he hζ II hII
  have : Nonempty (Fin f) := ⟨⟨0, hf⟩⟩
  have hV := RootArithVar.full f j m ζ hf hζ
  have hmem : rootAnchorSection f j m ∉ rootPointIdeal ζ := by
    rw [rootPointIdeal, MultiHomogMemCoord.proof (Fin f) (plBlocks f j m) ℂ (rootCoord ζ) _ _ (anchor_homog f j m)]
    simp [rootAnchorSection, rootCoord, anchor_minor]
  have hsm : IsSmoothHerm (fsMulti (plBlocks f j m)) := FsLineSmooth.proof _ _
  have hR := (hII (Fin f) (plBlocks f j m)).2.2 (rootPointIdeal ζ) 0 Fin.elim0
    (fsMulti (plBlocks f j m)) (rootAnchorSection f j m) (fun _ => 1) hV (fun j => j.elim0) hsm
    (fun _ => by simp [fsMulti, HermLine.ofMetrics]) (anchor_homog f j m) hmem
  have e1 : (Fin.snoc (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine (plBlocks f j m)) (fsMulti (plBlocks f j m)) :
      Fin (0 + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine (plBlocks f j m)) = ![fsMulti (plBlocks f j m)] := by
    funext i; fin_cases i; rfl
  rw [e1] at hR
  have hlow := PtsIntegralZeroLowerNE.proof (Fin f) (plBlocks f j m) (rootPointIdeal ζ)
    (fun i z => Real.log (((Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine (plBlocks f j m)) i).h z))
    (logNorm (fsMulti (plBlocks f j m)) (rootAnchorSection f j m)) (-((f : ℝ) * e))
    hV.2.1.2.1 (RootPointsFinite.full f j m ζ hζ) ?_ (RootLogNormBoundE.full f j m e ζ he hζ)
  · have : recR (II (Fin f) (plBlocks f j m)) (rootPointIdeal ζ)
        (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine (plBlocks f j m)) (fsMulti (plBlocks f j m)) (rootAnchorSection f j m) =
        - arInt (rootPointIdeal ζ) (rootAnchorSection f j m) (fsMulti (plBlocks f j m)) Fin.elim0 := by
      simp [recR, RootDivSuppEmpty.proof f j m ζ hζ]
    rw [this] at hR
    show II _ _ _ 1 _ ≤ _
    rw [hR]
    simp only [arInt]
    have := hlow
    nlinarith
  · intro u z hu hz
    have hh := (fsMulti (plBlocks f j m)).smul u z hu
    have hfa : (fsMulti (plBlocks f j m)).a = fun _ => 1 := rfl
    simp only [logNorm, hh, hfa, zpow_one]
    have hs : eval (fun p : (Σ _ : Fin f, PlIdx j m) => u p.1 * z p)
        (map (Int.castRingHom ℂ) (rootAnchorSection f j m))
        = (∏ k, u k) * eval z (map (Int.castRingHom ℂ) (rootAnchorSection f j m)) := by
      simp [rootAnchorSection, Finset.prod_mul_distrib]
    have hu0 : (∏ k, ‖u k‖) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => norm_ne_zero_iff.mpr (hu k)
    congr 1
    erw [hs]
    rw [norm_mul, norm_prod]
    field_simp

theorem GrassHeightE.full : GrassHeightE.Statement := by
  intro hZ2 f j m e hf he II hII
  refine hZ2 (Fin f) (plBlocks f j m) (grassIdeal f j m) ⊥ (f * j * m) (fsMulti (plBlocks f j m))
    ((f : ℝ) * e) (rootFamily f j m) II hII (GrassArithVar.full f j m hf) bot_le
    (FsLineSemipositive.full _ _ _) (NefOfNonneg.proof _ _ _ _ fun _ => ?_) (FsConjInvariant.proof _ _) ?_
    (RootDense.full f j m)
  · show (0 : ℤ) ≤ 1
    exact zero_le_one
  · rintro W ⟨ζ, hζ, rfl⟩
    exact ⟨RootArithVar.full f j m ζ hf hζ, GrassLeRoot.proof f j m ζ, RootHeightE.full f j m e ζ hf he hζ II hII⟩

end

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def RegAboveWeight.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt),
    ∃ t₂ : ℝ, 0 < t₂ ∧ ∃ N : Set ((Σ k, ι k) → ℂ), IsPtsNull (mCoordIdeal D.y) D.n N ∧
      ∀ t : ℝ, 0 < t → t ≤ t₂ → ∀ z ∈ mcPts (mCoordIdeal D.y), z ∉ N →
        phMu X.H z ≤ Real.log (X.S.ref.h z) + X.S.regWeight t (X.M.proj z)

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter GroundTheory.Heights₂.Heights.CoordinateConeArithVar

namespace FlagArithVar

variable (Ψ : Type) (N : ℕ)

theorem yFl_eq (q : FlBlock Ψ N) (A : FlIdx Ψ N q) :
    yFl Ψ N ⟨q, A⟩ = ((genMatFr ℚ Ψ N q.1).submatrix (Fin.castLE (step_le q.2)) A.1).det := by
  rw [yFl, RingHom.map_det]
  congr 1

def leadIdx (q : FlBlock Ψ N) : FlIdx Ψ N q := ⟨Fin.castLE (step_le q.2), Fin.strictMono_castLE _⟩

theorem yFl_lead (q : FlBlock Ψ N) : yFl Ψ N ⟨q, leadIdx Ψ N q⟩ = _root_.GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.leadMinor (genMatFr ℚ Ψ N q.1) q.2 := by
  rw [yFl_eq, _root_.GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.leadMinor, pivotMinor]
  congr 2
  funext c
  apply Fin.ext
  have := c.isLt
  simp only [leadIdx, Fin.val_castLE, pivotCols]
  split_ifs with h
  · rfl
  · simp only [Fin.val_castLE]; omega

theorem yFl_eq_flagMinor (q : FlBlock Ψ N) (A : FlIdx Ψ N q) :
    yFl Ψ N ⟨q, A⟩ = flagMinor (genMatFr ℚ Ψ N q.1) q.2
      ⟨Finset.univ.image A.1, by rw [Finset.card_image_of_injective _ A.2.injective, Finset.card_fin]⟩ := by
  rw [yFl_eq, flagMinor]
  congr 2
  exact Finset.orderEmbOfFin_unique _ (fun x => Finset.mem_image_of_mem _ (Finset.mem_univ x)) A.2

theorem flagMinor_eq_yFl (τ : Ψ) (i : Fin (N - 1)) (S : PluckerBlocks N N i) :
    flagMinor (genMatFr ℚ Ψ N τ) i S = yFl Ψ N ⟨(τ, i), ⟨S.1.orderEmbOfFin S.2, (S.1.orderEmbOfFin S.2).strictMono⟩⟩ := by
  rw [yFl_eq, flagMinor]

theorem coneRatios_eq : coneRatios (yFl Ψ N) (leadIdx Ψ N) = Set.range (flagMinorRatio ℚ Ψ N) := by
  ext x
  constructor
  · rintro ⟨⟨q, A⟩, rfl⟩
    refine ⟨(q.1, ⟨q.2, ⟨Finset.univ.image A.1,
      by rw [Finset.card_image_of_injective _ A.2.injective, Finset.card_fin]⟩⟩), ?_⟩
    show flagMinor _ _ _ / _root_.GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.leadMinor _ _ = yFl Ψ N ⟨q, A⟩ / yFl Ψ N ⟨q, leadIdx Ψ N q⟩
    rw [yFl_lead, yFl_eq_flagMinor]
  · rintro ⟨⟨τ, i, S⟩, rfl⟩
    refine ⟨⟨(τ, i), ⟨S.1.orderEmbOfFin S.2, (S.1.orderEmbOfFin S.2).strictMono⟩⟩, ?_⟩
    show yFl Ψ N _ / yFl Ψ N ⟨(τ, i), leadIdx Ψ N (τ, i)⟩ = flagMinor _ _ _ / _root_.GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.leadMinor _ _
    rw [yFl_lead, flagMinor_eq_yFl]

theorem toSubfield_adjoin_rat {E : Type} [Field E] [Algebra ℚ E] (s : Set E) :
    (IntermediateField.adjoin ℚ s).toSubfield = Subfield.closure s := by
  rw [IntermediateField.adjoin_toSubfield]
  refine le_antisymm (Subfield.closure_le.2 (Set.union_subset ?_ Subfield.subset_closure))
    (Subfield.closure_mono Set.subset_union_right)
  rintro _ ⟨q, rfl⟩
  rw [eq_ratCast]
  exact SubfieldClass.ratCast_mem _ q

theorem trdeg_int_adjoin {E : Type} [Field E] [Algebra ℚ E] (s : Set E) :
    Algebra.trdeg ℤ (IntermediateField.adjoin ℚ s) = Algebra.trdeg ℤ (Subfield.closure s) := by
  rw [← (RingEquiv.subfieldCongr (toSubfield_adjoin_rat s)).toIntAlgEquiv.trdeg_eq]
  exact AlgEquiv.trdeg_eq (RingEquiv.refl _).toIntAlgEquiv

theorem trdeg_int_eq_rat {L : Type} [Field L] (I : Algebra ℚ L) :
    Algebra.trdeg ℤ L = @Algebra.trdeg ℚ L _ _ I := by
  have : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic _ (nonZeroDivisors ℤ)
  have : FaithfulSMul ℤ ℚ := (faithfulSMul_iff_algebraMap_injective ℤ ℚ).mpr Int.cast_injective
  have : FaithfulSMul ℚ L := (faithfulSMul_iff_algebraMap_injective ℚ L).mpr (algebraMap ℚ L).injective
  rw [← trdeg_add_eq ℤ ℚ (A := L), trdeg_eq_zero, zero_add]

theorem trdeg_closure_of_rat {E : Type} [Field E] {iQ : Algebra ℚ E} (s : Set E) {c : Cardinal}
    (h : @Algebra.trdeg ℚ (IntermediateField.adjoin ℚ s) _ _ (IntermediateField.adjoin ℚ s).algebra' = c) :
    Algebra.trdeg ℤ (Subfield.closure s) = c := by
  rw [← trdeg_int_adjoin, trdeg_int_eq_rat (IntermediateField.adjoin ℚ s).algebra']
  exact h

end FlagArithVar


open FlagArithVar in
theorem FlagArithVar.proof : FlagArithVar.Statement := by
  intro Ψ _ _ _ N hN
  have hc : ∀ q, yFl Ψ N ⟨q, leadIdx Ψ N q⟩ ≠ 0 := fun q => by
    rw [yFl_lead]; exact GenLeadMinorNeZero.full ℚ Ψ N q.1 q.2
  have hK : Nonempty (FlBlock Ψ N) := ⟨(Classical.arbitrary Ψ, ⟨0, by omega⟩)⟩
  have hhor : IsHorizontal (PFl Ψ N) := horizontal (yFl Ψ N)
  refine ⟨hK, ⟨RingHom.ker_isPrime _, isMultiHomogIdeal (yFl Ψ N), relevant (yFl Ψ N) _ hc⟩, hhor, ?_⟩
  have htr := ConeTrdeg.full _ (FlIdx Ψ N) (_root_.GroundTheory.Heights₂.Heights.CoordinateConeArithVar.ratioField (yFl Ψ N) (leadIdx Ψ N))
    (ratioPtL (yFl Ψ N) (leadIdx Ψ N)) (birational (yFl Ψ N) _ hc)
    (fun k ↦ ⟨leadIdx Ψ N k, fun h0 ↦ by
      have h1 := congrArg Subtype.val h0
      simp [ratioPtL, ratioPt, hc] at h1⟩)
    (by rw [mCoordIdeal_ratioPtL (yFl Ψ N) _ hc]; exact hhor)
  have hL : Algebra.trdeg ℤ (_root_.GroundTheory.Heights₂.Heights.CoordinateConeArithVar.ratioField (yFl Ψ N) (leadIdx Ψ N)) = ((dimFl Ψ N : ℕ) : Cardinal) := by
    have h := trdeg_closure_of_rat _ (FlagRatioTrdeg.full ℚ Ψ N)
    rw [_root_.GroundTheory.Heights₂.Heights.CoordinateConeArithVar.ratioField, coneRatios_eq, trdeg_int_adjoin]
    exact h
  rw [mCoordIdeal_ratioPtL (yFl Ψ N) _ hc, hL] at htr
  have : (PFl Ψ N).IsPrime := RingHom.ker_isPrime _
  have hA := IntDomainDim.full (MRing (FlIdx Ψ N) ⧸ PFl Ψ N) (algebraMap_injective _ hhor)
  rw [hA]
  unfold PFl
  rw [htr, ← Nat.cast_add, Cardinal.toENat_nat]
  push_cast
  ring

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open ReciprocityTheory.AnForm (levi)

def APrimeChartLevi.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (k : Fin X.S.R.N),
    ∃ Q : (Fin D.n → ℂ) → (Fin D.n → ℂ) → ℝ,
      ContinuousOn (fun p : (Fin D.n → ℂ) × (Fin D.n → ℂ) => Q p.1 p.2)
        ((X.S.R.chart k).target ×ˢ Set.univ) ∧
      ∀ z ∈ mcPts (mCoordIdeal D.y), X.M.proj z ∈ (X.S.R.chart k).source → ∀ w v,
        IsChartVel X.M (X.S.R.chart k) z w v →
          levi (fun y => Real.log (D.A'.h y)) z w = Q (X.S.R.chart k (X.M.proj z)) v

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open ReciprocityTheory.AnForm (levi)
open scoped ContDiff

def APrimeChartLeviLocal.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (k : Fin X.S.R.N),
    ∀ y₀ ∈ (X.S.R.chart k).target, ∃ W : Set (Fin D.n → ℂ), IsOpen W ∧ y₀ ∈ W ∧
      ∃ f : (Fin D.n → ℂ) → ℝ, ContDiffOn ℝ ∞ f W ∧
        ∀ z ∈ mcPts (mCoordIdeal D.y), X.M.proj z ∈ (X.S.R.chart k).source →
          X.S.R.chart k (X.M.proj z) ∈ W → ∀ w v, IsChartVel X.M (X.S.R.chart k) z w v →
            levi (fun y => Real.log (D.A'.h y)) z w = levi f (X.S.R.chart k (X.M.proj z)) v

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open ReciprocityTheory.AnForm (levi)

def APrimeChartMargin.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt),
    ∃ c : ℝ, 0 < c ∧ ∀ z ∈ mcPts (mCoordIdeal D.y), ∀ w, ∀ k : Fin X.S.R.N, X.M.proj z ∈ X.S.R.mid k →
      ∀ v : Fin D.n → ℂ, IsChartVel X.M (X.S.R.chart k) z w v →
        c * ‖v‖ ^ 2 ≤ levi (fun y => Real.log (D.A'.h y)) z w

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def ChartVelLift.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (k : Fin X.S.R.N),
    ∀ y ∈ (X.S.R.chart k).target, ∀ v : Fin D.n → ℂ, v ≠ 0 →
      ∃ z ∈ mcPts (mCoordIdeal D.y), X.M.proj z = (X.S.R.chart k).symm y ∧ ∃ w,
        IsChartVel X.M (X.S.R.chart k) z w v ∧ IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal D.y) z w ∧
          ∀ c : K → ℂ, w ≠ torusSmul c z

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

theorem genMat0Fr_eq_map (F : Type) [Field F] (Ψ : Type) (n j : ℕ) (τ : Ψ) :
    genMat0Fr F Ψ n j τ = (algebraMap (MvPolynomial (Ψ × Fin n × Fin n) F) (GenFrac F Ψ n)).mapMatrix
      (Matrix.of fun (p q : Fin n) => if (p : ℕ) < j ∧ j ≤ (q : ℕ) then 0 else
        (X (τ, p, q) : MvPolynomial (Ψ × Fin n × Fin n) F)) := by
  ext p q
  simp only [genMat0Fr, genMatFr, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> simp

theorem GenLeadMinor0NeZero.full : GenLeadMinor0NeZero.Statement := by
  intro F _ Ψ n j τ a
  rw [genMat0Fr_eq_map, ← leadMinor_map]
  refine (map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial (Ψ × Fin n × Fin n) F) (GenFrac F Ψ n))).2 ?_
  intro h0
  have h1 := congrArg (MvPolynomial.eval (fun q : Ψ × Fin n × Fin n => if q.2.1 = q.2.2 then (1 : F) else 0)) h0
  rw [leadMinor_map, map_zero] at h1
  have hP : (MvPolynomial.eval (fun q : Ψ × Fin n × Fin n => if q.2.1 = q.2.2 then (1 : F) else 0)).mapMatrix
      (Matrix.of fun (p q : Fin n) => if (p : ℕ) < j ∧ j ≤ (q : ℕ) then 0 else
        (X (τ, p, q) : MvPolynomial (Ψ × Fin n × Fin n) F)) = 1 := by
    ext p q
    by_cases hc : (p : ℕ) < j ∧ j ≤ (q : ℕ)
    · have hpq : p ≠ q := by
        rintro rfl
        obtain ⟨hc₁, hc₂⟩ := hc
        omega
      simp [hc, hpq]
    · simp [hc, Matrix.one_apply]
  rw [hP, leadMinor_one] at h1
  exact one_ne_zero h1

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end
