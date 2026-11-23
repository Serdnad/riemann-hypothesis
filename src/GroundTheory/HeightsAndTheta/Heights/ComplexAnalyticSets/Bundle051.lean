module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle029
public import Mathlib.Analysis.Analytic.Basic
public import ReciprocityTheory.AnalyticForms.MaIntEmpty
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle001
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsSt
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle030
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
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
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Bundle002
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Analysis.Calculus.FDeriv.Prod

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Matrix

theorem GenericProjectionFinite.equiv :
    GroundTheory.Heights₂.Heights.ComplexSets.GenericProjectionFinite.Statement ↔
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.GenericProjectionFinite.Statement := by
  unfold GroundTheory.Heights₂.Heights.ComplexSets.GenericProjectionFinite.Statement
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.GenericProjectionFinite.Statement
  refine forall_congr' fun n => forall_congr' fun d => forall_congr' fun J =>
    imp_congr_right fun _ => imp_congr_right fun _ => ?_
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))
  · constructor
    · rintro ⟨U, ⟨S, rfl⟩, ⟨A, hA⟩, hU⟩
      exact ⟨S, ⟨A, hA⟩, fun M hM => (Objects.isFiniteProjection_iff J M).mp (hU M hM)⟩
    · rintro ⟨S, ⟨A, hA⟩, hS⟩
      exact ⟨{M | ∃ f ∈ S, eval (fun p : Fin d × Fin n => M p.1 p.2) f ≠ 0}, ⟨S, rfl⟩, ⟨A, hA⟩,
        fun M hM => (Objects.isFiniteProjection_iff J M).mpr (hS M hM)⟩
  · simp only [Set.Nonempty, Set.mem_ofPred_eq, Objects.isFiniteProjection_iff]
  · simp only [Objects.orthoRows_eq, Objects.isFiniteProjection_iff]
  · constructor
    · intro h m F hF
      obtain ⟨U, hU, hk⟩ := h m fun k => ⟨(F k)ᴴ, by
        simpa [Matrix.star_eq_conjTranspose] using Unitary.star_mem (hF k)⟩
      refine ⟨Uᴴ, by simpa [Matrix.star_eq_conjTranspose] using Unitary.star_mem hU,
        fun k s => ?_⟩
      rw [← Objects.isFiniteProjection_iff]
      simpa [Matrix.conjTranspose_mul] using hk k s
    · intro h m F
      obtain ⟨U, hU, hk⟩ := h m (fun k => (F k : Matrix (Fin n) (Fin n) ℂ)ᴴ) fun k => by
        simpa [Matrix.star_eq_conjTranspose] using Unitary.star_mem (F k).2
      refine ⟨Uᴴ, by simpa [Matrix.star_eq_conjTranspose] using Unitary.star_mem hU,
        fun k s => ?_⟩
      rw [Objects.isFiniteProjection_iff]
      simpa [Matrix.conjTranspose_mul] using hk k s

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial MeasureTheory Filter Topology Matrix

noncomputable section

variable {n d : ℕ}

theorem analyticOnNhd_of_differentiableOn {U : Set (Fin d → ℂ)} {s : (Fin d → ℂ) → Fin n → ℂ}
    (hU : IsOpen U) (hs : DifferentiableOn ℂ s U) : AnalyticOnNhd ℂ s U := by
  have h : ∀ j, AnalyticOnNhd ℂ (fun y => s y j) U := fun j =>
    ReciprocityTheory.AnForm.Osgood.osgood d U _ hU (differentiableOn_pi.mp hs j)
  exact AnalyticOnNhd.pi h

variable {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ} {x : Fin n → ℂ}

theorem maDens_congr_of_eventuallyEq {D : ℕ} {φ ψ : Fin D → (Fin D → ℂ) → ℝ} {z : Fin D → ℂ}
    (h : ∀ k, φ k =ᶠ[𝓝 z] ψ k) :
    ReciprocityTheory.AnForm.maDens φ z = ReciprocityTheory.AnForm.maDens ψ z := by
  have hH : ∀ k, ReciprocityTheory.AnForm.hessC (φ k) z = ReciprocityTheory.AnForm.hessC (ψ k) z := by
    intro k
    have h2 : fderiv ℝ (fderiv ℝ (φ k)) z = fderiv ℝ (fderiv ℝ (ψ k)) z :=
      ((h k).fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
    unfold ReciprocityTheory.AnForm.hessC
    rw [h2]
  unfold ReciprocityTheory.AnForm.maDens
  simp only [hH]


end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing Ideal

universe u

theorem spanFinrank_maximalIdeal_le_quotient_of_le_sq {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {I : Ideal R} (hI : I ≤ maximalIdeal R ^ 2) [IsLocalRing (R ⧸ I)] :
    (maximalIdeal R).spanFinrank ≤ (maximalIdeal (R ⧸ I)).spanFinrank := by
  classical
  obtain ⟨t, htc, hts⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank
    (IsNoetherian.noetherian (maximalIdeal (R ⧸ I)))
  choose g hg using fun y : R ⧸ I => Ideal.Quotient.mk_surjective y
  set s : Finset R := t.image g with hs
  have hmk : ∀ a ∈ maximalIdeal R, Ideal.Quotient.mk I a ∈ maximalIdeal (R ⧸ I) := by
    intro a ha
    have h := Ideal.mem_map_of_mem (Ideal.Quotient.mk I) ha
    rwa [map_maximalIdeal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective] at h
  have hsm : (s : Set R) ⊆ maximalIdeal R := by
    intro a ha
    simp only [hs, Finset.coe_image, Set.mem_image, Finset.mem_coe] at ha
    obtain ⟨y, hy, rfl⟩ := ha
    have hy' : y ∈ maximalIdeal (R ⧸ I) := hts ▸ Submodule.subset_span hy
    by_contra hn
    have hu : IsUnit (g y) := not_not.mp fun h => hn ((mem_maximalIdeal _).mpr h)
    exact (mem_maximalIdeal _).mp hy' (hg y ▸ hu.map (Ideal.Quotient.mk I))
  have hmap : (Ideal.span (s : Set R)).map (Ideal.Quotient.mk I) = maximalIdeal (R ⧸ I) := by
    rw [Ideal.map_span, hs, Finset.coe_image, ← Set.image_comp,
      show (Ideal.Quotient.mk I) ∘ g = id from funext hg, Set.image_id]
    exact hts
  have hle : maximalIdeal R ≤ Ideal.span (s : Set R) ⊔ maximalIdeal R • maximalIdeal R := by
    intro a ha
    have h1 : Ideal.Quotient.mk I a ∈ (Ideal.span (s : Set R)).map (Ideal.Quotient.mk I) :=
      hmap ▸ hmk a ha
    rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective,
      Ideal.mk_ker] at h1
    exact sup_le_sup_left (hI.trans (le_of_eq (by rw [pow_two, Ideal.smul_eq_mul]))) _ h1
  have hm : maximalIdeal R = Ideal.span (s : Set R) :=
    le_antisymm (Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
      (jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge hle) (Ideal.span_le.mpr hsm)
  rw [hm, ← htc]
  refine (Submodule.spanFinrank_span_le_ncard_of_finite s.finite_toSet).trans ?_
  rw [Set.ncard_coe_finset]
  exact Finset.card_image_le

theorem exists_span_eq_of_isRegularLocalRing_quotient (n : ℕ) :
    ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R] (I : Ideal R) [IsRegularLocalRing (R ⧸ I)],
      ringKrullDim R = ringKrullDim (R ⧸ I) + n →
        ∃ f : Fin n → R, (∀ j, f j ∈ I) ∧ I = Ideal.span (Set.range f) := by
  induction n with
  | zero =>
    intro R _ _ I _ hd
    refine ⟨Fin.elim0, fun j => j.elim0, ?_⟩
    rw [Set.range_eq_empty, Ideal.span_empty]
    have := GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.isDomain (R := R)
    by_contra hI
    obtain ⟨y, hyI, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hy0)
    have h2 : ringKrullDim (R ⧸ I) ≤ ringKrullDim (R ⧸ Ideal.span {y}) :=
      ringKrullDim_le_of_surjective (Ideal.Quotient.factor ((Ideal.span_singleton_le_iff_mem I).mpr hyI))
        (Ideal.Quotient.factor_surjective _)
    have hR : ringKrullDim R = ((maximalIdeal R).spanFinrank : WithBot ℕ∞) :=
      ((isRegularLocalRing_iff R).mp inferInstance).symm
    rw [Nat.cast_zero, add_zero] at hd
    have h3 : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) + 1 ≤ (maximalIdeal R).spanFinrank := by
      rw [← hR]
      calc ringKrullDim R + 1 = ringKrullDim (R ⧸ I) + 1 := by rw [hd]
        _ ≤ ringKrullDim (R ⧸ Ideal.span {y}) + 1 := by gcongr
        _ ≤ ringKrullDim R := h1
    have h4 : (maximalIdeal R).spanFinrank + 1 ≤ (maximalIdeal R).spanFinrank := by exact_mod_cast h3
    omega
  | succ n ih =>
    intro R _ _ I _ hd
    have hR : ringKrullDim R = ((maximalIdeal R).spanFinrank : WithBot ℕ∞) :=
      ((isRegularLocalRing_iff R).mp inferInstance).symm
    have hRI : ringKrullDim (R ⧸ I) = ((maximalIdeal (R ⧸ I)).spanFinrank : WithBot ℕ∞) :=
      ((isRegularLocalRing_iff (R ⧸ I)).mp inferInstance).symm
    have hdd : (maximalIdeal R).spanFinrank = (maximalIdeal (R ⧸ I)).spanFinrank + (n + 1) := by
      rw [hR, hRI] at hd
      exact_mod_cast hd
    have hItop : I ≠ ⊤ := Ideal.Quotient.nontrivial_iff.mp inferInstance
    have hIm : I ≤ maximalIdeal R := le_maximalIdeal hItop
    obtain ⟨x, hxI, hx2⟩ : ∃ x ∈ I, x ∉ maximalIdeal R ^ 2 := by
      by_contra h
      push Not at h
      have := spanFinrank_maximalIdeal_le_quotient_of_le_sq (I := I) h
      omega
    have hxm : x ∈ maximalIdeal R := hIm hxI
    have hxI' : Ideal.span {x} ≤ I := (Ideal.span_singleton_le_iff_mem I).mpr hxI
    have hne : Ideal.span {x} ≠ ⊤ := fun h => hItop (top_le_iff.mp (h ▸ hxI'))
    have : Nontrivial (R ⧸ Ideal.span {x}) := Ideal.Quotient.nontrivial_iff.mpr hne
    have : IsLocalRing (R ⧸ Ideal.span {x}) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    obtain ⟨hreg, hdim⟩ := GroundTheory.Arith.SchemeCoh.isRegularLocalRing_quotient hxm hx2
    have := hreg
    let e := DoubleQuot.quotQuotEquivQuotOfLE hxI'
    have : IsRegularLocalRing ((R ⧸ Ideal.span {x}) ⧸ I.map (Ideal.Quotient.mk (Ideal.span {x}))) :=
      IsRegularLocalRing.of_ringEquiv e.symm
    have hR' : ringKrullDim (R ⧸ Ideal.span {x}) =
        ((maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank : WithBot ℕ∞) :=
      ((isRegularLocalRing_iff _).mp inferInstance).symm
    have hd' : ringKrullDim (R ⧸ Ideal.span {x}) =
        ringKrullDim ((R ⧸ Ideal.span {x}) ⧸ I.map (Ideal.Quotient.mk (Ideal.span {x}))) + n := by
      rw [ringKrullDim_eq_of_ringEquiv e, hRI, hR']
      rw [hR, hR'] at hdim
      have h5 : (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 = (maximalIdeal R).spanFinrank := by
        exact_mod_cast hdim
      have h6 : (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank = (maximalIdeal (R ⧸ I)).spanFinrank + n := by
        omega
      rw [h6]
      push_cast
      rfl
    obtain ⟨f', hf'I, hf'⟩ := ih _ _ hd'
    have hlift : ∀ j, ∃ a ∈ I, Ideal.Quotient.mk (Ideal.span {x}) a = f' j := fun j =>
      (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp (hf'I j)
    choose g hgI hg using hlift
    refine ⟨(Fin.cons x g : Fin (n + 1) → R), Fin.forall_fin_succ.mpr ⟨by simpa using hxI, fun i => by simpa using hgI i⟩, ?_⟩
    rw [Fin.range_cons, Ideal.span_insert]
    have hcomap : I = (I.map (Ideal.Quotient.mk (Ideal.span {x}))).comap (Ideal.Quotient.mk (Ideal.span {x})) := by
      rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker, sup_eq_left.mpr hxI']
    have hrange : Set.range f' = Ideal.Quotient.mk (Ideal.span {x}) '' Set.range g := by
      rw [← Set.range_comp]
      exact congrArg Set.range (funext hg).symm
    rw [hcomap, hf', hrange, ← Ideal.map_span, Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective,
      Ideal.mk_ker, sup_comm]

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def SliceBranchInt.Statement : Prop :=
  ∀ (n d : ℕ) (J W : Ideal (MvPolynomial (Fin n) ℂ)) (u q : Fin n → ℂ) (m : ℕ)
    (γ : Fin m → VarBranch J (d + 1) q) (ord : Fin m → ℕ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes → q ∈ zeroSet W →
    (∃ N ∈ 𝓝 q, ∀ x ∈ zeroSet J ∩ N, linEval u x = 0 → x ∈ zeroSet W) →
    (∃ N ∈ 𝓝 q, zeroSet J ∩ N ⊆ ⋃ b, (γ b).image) →
    (∃ N ∈ 𝓝 q, ∀ b, zeroSet W ∩ N ⊆ (γ b).slice) →
    (∀ b b', b ≠ b' → (γ b).image ∩ (γ b').image ⊆ {x | linEval u x = 0}) →
    (∀ b, VanishesToOrder (fun t => linEval u ((γ b).toFun t)) (γ b).radius (ord b)) →
      ∃ N ∈ 𝓝 q, ∀ (b : Fin m) (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ),
        ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ N →
        (∀ i, SmoothNear (zeroSet J) (φ i)) →
          varInt W d f φ =
            ∫ w in Metric.ball (0 : Fin d → ℂ) (γ b).radius,
              f ((γ b).toFun (ReciprocityTheory.AnForm.A.hypIncl w)) *
                ReciprocityTheory.AnForm.A.densHyp (fun k => φ k ∘ (γ b).toFun) w

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory ComplexSets ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open scoped ContDiff

noncomputable section

def MaDensLeibniz.Statement : Prop :=
  ∀ (D : ℕ) (φ : Fin D → (Fin (D + 1) → ℂ) → ℝ) (f g : (Fin (D + 1) → ℂ) → ℝ) (z : Fin (D + 1) → ℂ),
    ContDiffAt ℝ 2 f z → ContDiffAt ℝ 2 g z →
      maDens (Fin.cons (fun y => f y * g y) φ) z =
          f z * maDens (Fin.cons g φ) z + g z * maDens (Fin.cons f φ) z + gradDens φ f g z +
            gradDens φ g f z ∧
        maDens (Fin.cons (fun y => f y ^ 2 / 2) φ) z =
          f z * maDens (Fin.cons f φ) z + gradDens φ f f z

def EnergyDensNonneg.Statement : Prop :=
  ∀ (n d : ℕ) (s : (Fin (d + 1) → ℂ) → Fin n → ℂ) (y : Fin (d + 1) → ℂ) (v : (Fin (d + 1) → ℂ) → ℝ),
    AnalyticAt ℂ s y → 0 ≤ gradDens (fun _ : Fin d => euclPot ∘ s) v v y

def GradDensSheetBound.Statement : Prop :=
  ∀ (n d : ℕ) (φ : Fin d → (Fin n → ℂ) → ℝ) (U K : Set (Fin n → ℂ)),
    IsOpen U → IsCompact K → K ⊆ U → (∀ i, ContDiffOn ℝ 2 (φ i) U) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : (Fin (d + 1) → ℂ) → Fin n → ℂ) (y : Fin (d + 1) → ℂ)
        (v w : (Fin (d + 1) → ℂ) → ℝ), AnalyticAt ℂ s y → s y ∈ K →
          |gradDens (fun i => φ i ∘ s) v w y| ≤
            C * Real.sqrt (gradDens (fun _ : Fin d => euclPot ∘ s) v v y) *
              Real.sqrt (gradDens (fun _ : Fin d => euclPot ∘ s) w w y)

end

end GroundTheory.Heights₂.Heights
end
