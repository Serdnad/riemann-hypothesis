module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle025
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle027
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle024
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle028
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle026
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle023
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

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial

noncomputable section

namespace StandardDualModelTranscendence

variable {L : Type} [Field L]

def scaleHom (a : L) :
    MvPolynomial Unit (MvPolynomial Unit L) →+* MvPolynomial Unit (MvPolynomial Unit L) :=
  eval₂Hom ((C : MvPolynomial Unit L →+* MvPolynomial Unit (MvPolynomial Unit L)).comp
      (aeval fun _ : Unit => C a * X ()).toRingHom) fun _ => C (C a⁻¹) * X ()

theorem scaleHom_CC (a c : L) : scaleHom a (C (C c)) = C (C c) := by simp [scaleHom]

theorem scaleHom_S (a : L) : scaleHom a (C (X ())) = C (C a) * C (X ()) := by simp [scaleHom]

theorem scaleHom_alt (a : L) : scaleHom a (X ()) = C (C a⁻¹) * X () := by simp [scaleHom]

theorem scaleHom_comp {a : L} (ha : a ≠ 0) : (scaleHom a⁻¹).comp (scaleHom a) = RingHom.id _ := by
  have hC : ((scaleHom a⁻¹).comp (scaleHom a)).comp C =
      (C : MvPolynomial Unit L →+* MvPolynomial Unit (MvPolynomial Unit L)) := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun v => ?_)
    · simp only [RingHom.comp_apply, scaleHom_CC]
    · cases v
      simp only [RingHom.comp_apply, scaleHom_S, map_mul, scaleHom_CC]
      rw [← mul_assoc, ← map_mul, ← map_mul, ← C_mul, mul_inv_cancel₀ ha, C_1, one_mul]
  refine MvPolynomial.ringHom_ext (fun p => ?_) (fun u => ?_)
  · exact RingHom.congr_fun hC p
  · cases u
    simp only [RingHom.comp_apply, scaleHom_alt, map_mul, scaleHom_CC, RingHom.id_apply]
    rw [← mul_assoc, ← map_mul, ← map_mul, inv_inv, inv_mul_cancel₀ ha, map_one, map_one, one_mul]

theorem scaleHom_injective {a : L} (ha : a ≠ 0) : Function.Injective (scaleHom a) :=
  Function.LeftInverse.injective (g := scaleHom a⁻¹) fun p => RingHom.congr_fun (scaleHom_comp ha) p

def scale {a : L} (ha : a ≠ 0) :
    FractionRing (MvPolynomial Unit (MvPolynomial Unit L)) →+*
      FractionRing (MvPolynomial Unit (MvPolynomial Unit L)) :=
  IsFractionRing.lift (A := MvPolynomial Unit (MvPolynomial Unit L))
    (g := (algebraMap _ (FractionRing (MvPolynomial Unit (MvPolynomial Unit L)))).comp (scaleHom a))
    ((IsFractionRing.injective _ _).comp (scaleHom_injective ha))

theorem scale_algebraMap {a : L} (ha : a ≠ 0) (p : MvPolynomial Unit (MvPolynomial Unit L)) :
    scale ha (algebraMap _ _ p) = algebraMap _ _ (scaleHom a p) :=
  IsFractionRing.lift_algebraMap _ p

theorem transcendental_of_scale {R Ω : Type} [CommRing R] [Field Ω] [CharZero Ω] [Algebra R Ω]
    (A : Subalgebra R Ω) {z : Ω} (hz : z ≠ 0)
    (h : ∀ n : ℕ, ∃ σ : Ω →+* Ω, (∀ y ∈ A, σ y = y) ∧ σ z = ((n : Ω) + 1) * z) : Transcendental A z := by
  rintro ⟨p, hp0, hp⟩
  rw [Polynomial.aeval_def] at hp
  have hroot : ∀ n : ℕ, Polynomial.eval₂ (algebraMap A Ω) (((n : Ω) + 1) * z) p = 0 := by
    intro n
    obtain ⟨σ, hfix, hσz⟩ := h n
    have hcomp : σ.comp (algebraMap A Ω) = algebraMap A Ω := RingHom.ext fun y => hfix y y.2
    have h' := Polynomial.hom_eval₂ p (algebraMap A Ω) σ z
    rw [hp, map_zero, hcomp, hσz] at h'
    exact h'.symm
  have hq : p.map (algebraMap A Ω) ≠ 0 := (Polynomial.map_ne_zero_iff fun x y h => Subtype.ext h).mpr hp0
  refine hq (Polynomial.eq_zero_of_infinite_isRoot _ ?_)
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => ((n : Ω) + 1) * z) (fun n m hnm => ?_) fun n => ?_
  · exact Nat.cast_injective (add_right_cancel (mul_right_cancel₀ hz hnm))
  · change Polynomial.IsRoot _ _
    rw [Polynomial.IsRoot, Polynomial.eval_map]
    exact hroot n

variable {K : Type} [Field K] {i : ℕ}

theorem scale_emb {a : ProjField K i} (ha : a ≠ 0) (x : ProjField K i) :
    scale ha (dualStdModelEmb K i x) = dualStdModelEmb K i x := by
  simp only [dualStdModelEmb, RingHom.comp_apply, scale_algebraMap, scaleHom_CC]

theorem scale_S {a : ProjField K i} (ha : a ≠ 0) :
    scale ha (dualStdModelS K i) = dualStdModelEmb K i a * dualStdModelS K i := by
  simp only [dualStdModelS, dualStdModelEmb, RingHom.comp_apply, scale_algebraMap, scaleHom_S, map_mul]

theorem scale_alt {a : ProjField K i} (ha : a ≠ 0) :
    scale ha (dualStdModelT K i) = dualStdModelEmb K i a⁻¹ * dualStdModelT K i := by
  simp only [dualStdModelT, dualStdModelEmb, RingHom.comp_apply, scale_algebraMap, scaleHom_alt, map_mul]

variable [NumberField K] {F : HermLattice K i} {T : Type} (b : Module.Basis T ℤ (dualLattice F))

theorem scale_inl {a : ProjField K i} (ha : a ≠ 0) (t : T) :
    scale ha (dualStdModelPt b (⟨Sum.inl (), t⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k)) =
      dualStdModelEmb K i a * dualStdModelPt b (⟨Sum.inl (), t⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k) := by
  simp only [dualStdModelPt, map_mul, scale_emb, scale_S]
  ring

theorem scale_inr {a : ProjField K i} (ha : a ≠ 0) (j : PBlk i ()) :
    scale ha (dualStdModelPt b (⟨Sum.inr (), j⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k)) =
      dualStdModelPt b (⟨Sum.inr (), j⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k) := by
  have h : dualStdModelEmb K i a * dualStdModelEmb K i a⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ ha, map_one]
  simp only [dualStdModelPt, map_mul, scale_emb, scale_S, scale_alt]
  linear_combination
    (dualStdModelEmb K i (algebraMap (MvPolynomial (Fin i) K) (ProjField K i) (X j)) * dualStdModelS K i *
      dualStdModelT K i) * h

end StandardDualModelTranscendence


open DualArithmeticVariety StandardDualModelTranscendence in
theorem DualStdModelTransc.proof : DualStdModelTransc.Statement := by
  intro K _ _ i T _ _ b Φ₀ _ _ hΦ _ c
  have hy : dualLatticeCoord b ⟨(), c⟩ ≠ 0 := by
    rw [dualLatticeCoord_eq]
    exact evalForm_ne_zero fun h => b.ne_zero c (Subtype.ext h)
  have hS : dualStdModelS K i ≠ 0 := by
    intro h
    have h' := IsFractionRing.injective (MvPolynomial Unit (MvPolynomial Unit (ProjField K i)))
      (dualStdModelField K i) (h.trans (map_zero _).symm)
    simp at h'
  refine transcendental_of_scale _ (mul_ne_zero ((map_ne_zero _).mpr hy) hS) fun n => ?_
  have ha : ((n : ProjField K i) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
  have hΦfix : ∀ x : Φ₀, scale ha (algebraMap Φ₀ _ x) = algebraMap Φ₀ _ x := by
    intro x
    have hx : algebraMap Φ₀ (dualStdModelField K i) x ∈
        Subfield.closure (Set.range (dualStdModelPt b ∘ inrV (ι := dualBlocks T) (ι₂ := PBlk i))) :=
      hΦ ▸ RingHom.mem_fieldRange.mpr ⟨x, rfl⟩
    refine RingHom.eqOn_field_closure (g := RingHom.id _) ?_ hx
    rintro _ ⟨⟨u, j⟩, rfl⟩
    cases u
    exact scale_inr b ha j
  let σ : dualStdModelField K i →ₐ[Φ₀] dualStdModelField K i := { scale ha with commutes' := hΦfix }
  refine ⟨scale ha, fun y hyA => AlgHom.adjoin_le_equalizer σ (AlgHom.id Φ₀ _) ?_ hyA, ?_⟩
  · rintro _ ⟨t, rfl⟩
    change scale ha _ = _
    rw [map_div₀, scale_inl b ha, scale_inl b ha, mul_div_mul_left _ _ ((map_ne_zero _).mpr ha)]
    rfl
  · rw [scale_inl b ha]
    simp

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial

noncomputable section

namespace StandardDualGraphModel

open StandardDualImageBottom

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T]

theorem mConeMap_linForm (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i)))
    (q : Σ _ : Unit, Fin i) :
    mConeMap (dualLatticeCoord b) (linForm (ι₂ := PBlk i) (dualStdCoordMat b) q) =
      C (aeval (dualLatticeCoord b) (linForm (ι₂ := PBlk i) (dualStdCoordMat b) q)) * X () := by

  simp only [linForm, map_sum, map_mul, Finset.sum_mul, mConeMap, aeval_X, eq_intCast, map_intCast]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [mul_assoc]

def coneLift (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) :
    MRing (dualBlocks T) ⧸ dualIdeal b →+* MvPolynomial Unit (ProjField K i) :=
  Ideal.Quotient.lift (dualIdeal b)
    (mConeMap (dualLatticeCoord b) : MRing (dualBlocks T) →+* MvPolynomial Unit (ProjField K i)) fun _ ha => ha

omit [Fintype T] in
theorem coneLift_mk (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) (f : MRing (dualBlocks T)) :
    coneLift b (Ideal.Quotient.mk _ f) = mConeMap (dualLatticeCoord b) f :=
  rfl

omit [Fintype T] in
theorem coneLift_injective (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) :
    Function.Injective (coneLift b) :=
  RingHom.lift_injective_of_ker_le_ideal _ _ fun _ ha => ha

def modelMap (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) :
    MvPolynomial Unit (MRing (dualBlocks T) ⧸ dualIdeal b) →+* dualStdModelField K i :=
  (algebraMap (MvPolynomial Unit (MvPolynomial Unit (ProjField K i))) _).comp (MvPolynomial.map (coneLift b))

omit [Fintype T] in
theorem modelMap_injective (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) :
    Function.Injective (modelMap b) :=
  (IsFractionRing.injective (MvPolynomial Unit (MvPolynomial Unit (ProjField K i))) (dualStdModelField K i)).comp
    (MvPolynomial.map_injective _ (coneLift_injective b))

theorem modelMap_comp_graphMap [DecidableEq T]
    (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) :
    (modelMap b).comp (graphMap (dualIdeal b) (linForm (ι₂ := PBlk i) (dualStdCoordMat b))) =
      (eval₂Hom (Int.castRingHom (dualStdModelField K i)) (dualStdModelPt b) :
        MRing (Sum.elim (dualBlocks T) (PBlk i)) →+* dualStdModelField K i) := by
  refine MvPolynomial.ringHom_ext (fun r => by simp) ?_
  rintro ⟨(u | u), j⟩ <;> cases u
  · simp [graphMap, modelMap, coneLift_mk, dualStdModelPt, dualStdModelEmb, dualStdModelS,
      mConeMap]
  · have h := mConeMap_linForm b ⟨(), j⟩
    rw [aeval_linForm] at h
    simp only [RingHom.comp_apply, graphMap, eval₂Hom_X', modelMap, map_mul, map_C, map_X, coneLift_mk, h,
      dualStdModelPt, dualStdModelEmb, dualStdModelS, dualStdModelT, genPt]

end StandardDualGraphModel


open StandardDualGraphModel in
theorem DualStdGraphModel.proof : DualStdGraphModel.Statement := by
  intro K _ _ i T _ _ b
  rw [← modelMap_comp_graphMap b]
  ext f
  rw [graphIdeal, RingHom.mem_ker, RingHom.mem_ker, RingHom.comp_apply, map_eq_zero_iff _ (modelMap_injective b)]

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField Matrix
open scoped ComplexOrder

noncomputable section

namespace TopDualLatticeChange

variable {K : Type} [Field K] [NumberField K] {i : ℕ}

def supStandard (F : HermLattice K i) : HermLattice K i where
  lattice := F.lattice ⊔ (HermLattice.standard K i).lattice
  fg := F.fg.sup (HermLattice.standard K i).fg
  span_eq := eq_top_iff.mpr (F.span_eq ▸ Submodule.span_mono
    (SetLike.coe_subset_coe.mpr le_sup_left))
  metric := fun _ => 1
  posDef := fun _ => Matrix.PosDef.one
  conj := fun _ => by simp


omit [NumberField K] in
theorem gramAt_one_single (σ : K →+* ℂ) :
    gramAt (1 : Matrix (Fin i) (Fin i) ℂ) σ (fun j : Fin i => (Pi.single j 1 : Fin i → K)) = 1 := by
  ext a c
  simp only [gramAt, embVec, Matrix.one_mulVec, dotProduct, Pi.star_apply, Pi.single_apply,
    apply_ite σ, map_one, map_zero, Matrix.one_apply]
  by_cases h : a = c
  · subst h
    simp
  · simp [h, Ne.symm h]

theorem standard_degree : (HermLattice.standard K i).degree = 0 := by
  have hinf : (HermLattice.standard K i).lattice ⊓
      (Submodule.span K (Set.range fun j : Fin i => (Pi.single j 1 : Fin i → K))).restrictScalars (𝓞 K) =
      (HermLattice.standard K i).lattice :=
    inf_eq_left.mpr (Submodule.span_le_restrictScalars (𝓞 K) K _)
  simp only [HermLattice.degree, subDegree, hinf]
  have hstd : (HermLattice.standard K i).metric = fun _ => 1 := rfl
  simp only [hstd, gramAt_one_single, Matrix.det_one, Complex.one_re, Real.log_one,
    Finset.sum_const_zero, mul_zero, sub_zero, genIndex]
  show Real.log (((HermLattice.standard K i).lattice.toAddSubgroup.relIndex
    (HermLattice.standard K i).lattice.toAddSubgroup : ℝ) /
      ((HermLattice.standard K i).lattice.toAddSubgroup.relIndex
        (HermLattice.standard K i).lattice.toAddSubgroup : ℝ)) = 0
  simp [AddSubgroup.relIndex_self]

end TopDualLatticeChange


open TopDualLatticeChange in
theorem DualTopLatticeChange.proof (hSub : DualTopSubLattice.Statement) :
    DualTopLatticeChange.Statement := by
  intro K _ _ i F T T' _ _ _ _ b hb b' hb' II hi hII
  obtain ⟨TG, hTG, hdTG, ⟨bG⟩⟩ := DualLatticeBasisExists.proof K i (supStandard F)
  have hbG := DualEmbBijective.proof K i (supStandard F) TG bG
  have h1 := hSub K i (supStandard F) F TG T bG hbG b hb II hi hII le_sup_left
  have h2 := hSub K i (supStandard F) (HermLattice.standard K i) TG T' bG hbG b' hb' II hi hII
    le_sup_right
  have hstd : (HermLattice.standard K i).withStdMetric.degree = 0 := standard_degree
  have hline : dualLine (HermLattice.standard K i).withStdMetric b' hb' =
      dualLine (HermLattice.standard K i) b' hb' := rfl
  rw [hline, hstd] at h2
  rw [h1, h2]
  ring

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField

noncomputable section

theorem DualTopSubLattice.proof (hBasis : DualTopBasisChange.Statement)
    (hStacked : DualTopStacked.Statement) (hDeg : DualStackedDegree.Statement) :
    DualTopSubLattice.Statement := by
  intro K _ _ i F F' T T' _ _ _ _ b hb b' hb' II hi hII hle
  have hcard : Fintype.card T = Fintype.card T' := by
    rw [DualTopStackedExistence.card_eq_of_bijective b hb, DualTopStackedExistence.card_eq_of_bijective b' hb']
  obtain ⟨b₁, b₁', a, hab⟩ := DualTopStackedExistence.exists_stacked hle b b' hcard
  have hb₁ := DualEmbBijective.proof K i F T' b₁
  have hb₁' := DualEmbBijective.proof K i F' T' b₁'

  have h1 : II Unit (dualBlocks T') (dualIdeal b') i (fun _ => dualLine F'.withStdMetric b' hb') =
      II Unit (dualBlocks T') (dualIdeal b₁') i (fun _ => dualLine F'.withStdMetric b₁' hb₁') :=
    hBasis K i F'.withStdMetric T' T' b₁' hb₁' b' hb' II hi hII
  have h2 : II Unit (dualBlocks T') (dualIdeal b₁) i (fun _ => dualLine F.withStdMetric b₁ hb₁) =
      II Unit (dualBlocks T) (dualIdeal b) i (fun _ => dualLine F.withStdMetric b hb) :=
    hBasis K i F.withStdMetric T T' b hb b₁ hb₁ II hi hII

  have h3 := hStacked K i F F' T' b₁ hb₁ b₁' hb₁' a II hi hII hle hab
  have h4 := hDeg K i F F' T' b₁ b₁' a hle hab
  rw [h1, h3, h2, h4]

end

end GroundTheory.Heights₂.Heights
end
