module

public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.Intersections.JacMinorC
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle045
public import Mathlib.Algebra.Field.Shrink
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PHilbertPoint
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle019
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle028
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle009
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle020
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle038
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle053
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle060
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle057
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle059
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle023
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle002
import Std.Tactic.BVDecide.Normalize.Prop
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

open MvPolynomial
open scoped Matrix

theorem frame_matrix_det_ne_zero {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) :
    (Matrix.of fun j l : Fin n => b j l).det ≠ 0 := by
  intro h
  obtain ⟨v, hv, hvM⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h
  apply hv
  have hsum : ∑ j, v j • b j = 0 := by
    ext l
    have := congrFun hvM l
    simpa [Matrix.vecMul, dotProduct, mul_comm] using this
  have hli := Fintype.linearIndependent_iff.mp b.toBasis.linearIndependent v (by simpa using hsum)
  funext j
  exact hli j

theorem FrameJacobianGeneric.proof (hR : JacobianRankGeneric.Statement)
    (hC : ConormalGenerationGeneric.Statement) : FrameJacobianGeneric.Statement := by
  classical
  intro n d J hJ hd b
  have := hJ
  set K := FractionRing (MvPolynomial (Fin n) ℂ ⧸ J)
  let π : MvPolynomial (Fin n) ℂ →+* K :=
    (algebraMap (MvPolynomial (Fin n) ℂ ⧸ J) K).comp (Ideal.Quotient.mk J)
  have hπ : ∀ f, π f = 0 ↔ f ∈ J := by
    intro f
    simp only [π, RingHom.comp_apply]
    rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  have hdn : d ≤ n := by
    have h1 := ringKrullDim_quotient_le J
    rw [hd, MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field, zero_add,
      Nat.card_eq_fintype_card, Fintype.card_fin] at h1
    exact_mod_cast h1
  obtain ⟨t, G, hG⟩ := Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian J)
  set r := Fintype.card (Fin n) - d with hr
  obtain ⟨a, c, hac⟩ := IndefiniteRowSideFullHecke.Inter.exists_jacobian_minor_not_mem_charZero J G hG d hd
  have hrn : r = n - d := by rw [hr, Fintype.card_fin]
  have hGJ : ∀ i, G i ∈ J := fun i => hG ▸ Ideal.subset_span ⟨i, rfl⟩
  let V : Matrix (Fin r) (Fin n) K := Matrix.of fun i l => π (pderiv l (G (a i)))
  let N : Matrix (Fin n) (Fin n) K := Matrix.of fun l j => π (C (b j l))
  let W : Matrix (Fin r) (Fin n) K := Matrix.of fun i j => π (frameDeriv b j (G (a i)))
  have hW : W = V * N := by
    ext i j

    simp [W, V, N, frameDeriv, Matrix.mul_apply, map_sum, mul_comm]
  have hVc : (V.submatrix id c).det ≠ 0 := by
    have : V.submatrix id c = π.mapMatrix (Matrix.of fun i j => pderiv (c j) (G (a i))) := by
      ext i j
      rfl
    rw [this, ← RingHom.map_det]
    exact fun h => hac ((hπ _).mp h)
  have hN : N.det ≠ 0 := by
    have : N = π.mapMatrix ((C : ℂ →+* MvPolynomial (Fin n) ℂ).mapMatrix
        (Matrix.of fun j l : Fin n => b j l)ᵀ) := by
      ext l j
      rfl
    rw [this, ← RingHom.map_det, ← RingHom.map_det, Matrix.det_transpose]
    intro h
    rw [hπ] at h
    have hu : IsUnit (C (Matrix.of fun j l : Fin n => b j l).det : MvPolynomial (Fin n) ℂ) :=
      (isUnit_iff_ne_zero.mpr (frame_matrix_det_ne_zero b)).map C
    exact hJ.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)
  have hVinj : ∀ x : Fin r → K, x ᵥ* V = 0 → x = 0 := by
    intro x hx
    apply Matrix.eq_zero_of_vecMul_eq_zero hVc
    ext j
    simpa [Matrix.vecMul, dotProduct] using congrFun hx (c j)
  have hWinj : ∀ x : Fin r → K, Wᵀ *ᵥ x = 0 → x = 0 := by
    intro x hx
    rw [Matrix.mulVec_transpose, hW, ← Matrix.vecMul_vecMul] at hx
    exact hVinj x (Matrix.eq_zero_of_vecMul_eq_zero hN hx)
  obtain ⟨col, hcol⟩ := ReciprocityTheory.AnForm.R.gs_exists_rows_det_ne_zero Wᵀ hWinj
  have hcol' : (W.submatrix id col).det ≠ 0 := by
    rwa [← Matrix.det_transpose, Matrix.transpose_submatrix]
  have hinj : Function.Injective col := by
    intro i i' h
    by_contra hne
    apply hcol
    apply Matrix.det_zero_of_row_eq hne
    funext k
    simp [h]
  let I₀ : Finset (Fin n) := (Finset.univ.image col)ᶜ
  have hmem : ∀ j, j ∈ Set.range col ↔ j ∉ I₀ := by
    intro j
    simp [I₀]
  let e : Fin r ≃ {j // j ∉ I₀} :=
    (Equiv.ofInjective col hinj).trans (Equiv.subtypeEquivRight hmem)
  have he : ∀ i, (e i : Fin n) = col i := fun i => rfl
  let f : {j // j ∉ I₀} → MvPolynomial (Fin n) ℂ := fun k => G (a (e.symm k))
  have hli : LinearIndependent K (fun i => genericGradient J (G (a i))) := by
    rw [Fintype.linearIndependent_iff]
    intro x hx
    have : x ᵥ* V = 0 := by
      rw [Matrix.vecMul_eq_sum]
      exact hx
    simpa using congrFun (hVinj x this)
  have hspan : Submodule.span K (Set.range (genericGradient J ∘ f)) =
      Submodule.span K (genericGradient J '' (J : Set _)) := by
    have hrange : Set.range (genericGradient J ∘ f) =
        Set.range (fun i => genericGradient J (G (a i))) := by
      ext v
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨e.symm k, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨e i, by simp [f]⟩
    rw [hrange]
    apply Submodule.eq_of_le_of_finrank_le
    · apply Submodule.span_mono
      rintro _ ⟨i, rfl⟩
      exact ⟨G (a i), hGJ _, rfl⟩
    · rw [finrank_span_eq_card hli, Fintype.card_fin]
      exact (hR n d J hd).trans (by simp)
  obtain ⟨s, hsJ, hs⟩ := hC n J {j // j ∉ I₀} f (fun k => hGJ _) hspan
  refine ⟨I₀, f, s, ?_, fun k => hGJ _, hsJ, ?_, hs⟩
  · rw [Finset.card_compl, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin,
      Fintype.card_fin]
    omega
  · intro hdet
    rw [← hπ, frameJacobianDet, RingHom.map_det, ← Matrix.det_submatrix_equiv_self e] at hdet
    apply hcol'
    convert hdet using 2
    ext i i'
    simp [f, W, he]

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

namespace InterNumPointDeg

variable {k : Type u} [Field k] {N : ℕ}

abbrev OneRing (k : Type u) [Field k] (N : ℕ) : Type u := NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) k

abbrev coneField (P : Ideal (OneRing k N)) [P.IsPrime] : Type u := FractionRing (OneRing k N ⧸ P)

instance small_coneField [Small.{w} k] (P : Ideal (OneRing k N)) [P.IsPrime] : Small.{w} (coneField P) := by
  have : Small.{w} (OneRing k N ⧸ P) := small_of_surjective Ideal.Quotient.mk_surjective
  refine small_of_surjective (α := (OneRing k N ⧸ P) × nonZeroDivisors (OneRing k N ⧸ P))
    (f := fun z => IsLocalization.mk' (coneField P) z.1 z.2) fun z => ?_
  obtain ⟨q, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors (OneRing k N ⧸ P)) z
  exact ⟨q, rfl⟩

variable [Small.{w} k] (pp : Ideal (Poly k N)) [pp.IsPrime]

def coneHom : OneRing k N →ₐ[k] Shrink.{w} (coneField (pp.comap (oneBlock (S := k) (N := N)).toRingHom)) :=
  (Shrink.algEquiv k _).symm.toAlgHom.comp
    ((IsScalarTower.toAlgHom k (OneRing k N ⧸ pp.comap (oneBlock (S := k) (N := N)).toRingHom) _).comp
      (Ideal.Quotient.mkₐ k (pp.comap (oneBlock (S := k) (N := N)).toRingHom)))

def pt : Fin (N + 1) → Shrink.{w} (coneField (pp.comap (oneBlock (S := k) (N := N)).toRingHom)) :=
  fun i => coneHom pp (X ⟨(), i⟩)

theorem coneHom_eq_zero_iff (f : OneRing k N) :
    coneHom.{u, w} pp f = 0 ↔ oneBlock (S := k) (N := N) f ∈ pp := by
  show (Shrink.algEquiv k (coneField (pp.comap (oneBlock (S := k) (N := N)).toRingHom))).symm
    (algebraMap _ (coneField (pp.comap (oneBlock (S := k) (N := N)).toRingHom)) (Ideal.Quotient.mk (pp.comap (oneBlock (S := k) (N := N)).toRingHom) f)) = 0 ↔ _
  rw [map_eq_zero_iff _ (AlgEquiv.injective _), IsFractionRing.to_map_eq_zero_iff,
    Ideal.Quotient.eq_zero_iff_mem]
  rfl

theorem aeval_pt_oneBlock (f : OneRing k N) :
    aeval (pt.{u, w} pp) (oneBlock (S := k) (N := N) f) = coneHom pp f := by
  rw [← AlgHom.comp_apply]
  refine congrFun (congrArg DFunLike.coe (MvPolynomial.algHom_ext fun v => ?_)) f
  rcases v with ⟨⟨⟩, i⟩
  rw [AlgHom.comp_apply]
  show aeval (pt.{u, w} pp) (rename (fun v : Σ _ : Unit, Fin (N + 1) => v.2) (X ⟨(), i⟩)) = _
  rw [rename_X, aeval_X]
  rfl

theorem oneBlock_surjective (f : Poly k N) :
    oneBlock (S := k) (N := N) (rename (HilbertPositive.blockEquiv N).symm f) = f := by
  rw [oneBlock, rename_rename]
  exact (congrArg (fun g => rename g f) (HilbertPositive.blockEquiv N).self_comp_symm).trans (rename_id_apply f)

theorem aeval_pt_eq_zero_iff (f : Poly k N) : aeval (pt.{u, w} pp) f = 0 ↔ f ∈ pp := by
  rw [← oneBlock_surjective f, aeval_pt_oneBlock, coneHom_eq_zero_iff]

theorem primeOf_pt (hh : ∀ p ∈ pp, ∀ d : ℕ, homogeneousComponent d p ∈ pp) :
    primeOf (S := k) (pt.{u, w} pp) = pp := by
  ext f
  constructor
  · intro hf
    rw [← sum_homogeneousComponent f]
    refine Ideal.sum_mem _ fun d _ => ?_
    exact (aeval_pt_eq_zero_iff pp _).1 ((mem_primeOf_of_isHomogeneous _
      (homogeneousComponent_isHomogeneous d f)).1 (homogeneousComponent_mem_primeOf _ hf d))
  · intro hf
    rw [← sum_homogeneousComponent f]
    exact Ideal.sum_mem _ fun d _ => (mem_primeOf_of_isHomogeneous _
      (homogeneousComponent_isHomogeneous d f)).2 ((aeval_pt_eq_zero_iff pp _).2 (hh f hf d))

theorem isHomogeneous_oneBlock {f : OneRing k N} {b : Unit → ℕ} (hf : NumbersDVR.IsMultiHomog f b) :
    (oneBlock (S := k) (N := N) f).IsHomogeneous (b ()) := by
  have h1 : f.IsHomogeneous (b ()) := by
    intro d hd
    have := congrFun (hf hd) ()
    rw [HilbertPositive.weight_blockWeight_one] at this
    show Finsupp.weight (fun _ => 1) d = b ()
    rw [← Finsupp.degree_eq_weight_one]
    exact this
  exact h1.rename_isHomogeneous

theorem finrank_funField_pt (hrel : ∃ i, (X i : Poly k N) ∉ pp) :
    Module.finrank k (funField (k := k) (pt.{u, w} pp)) =
      FieldNumbers.resDeg (pp.comap (oneBlock (S := k) (N := N)).toRingHom) := by
  set P := pp.comap (oneBlock (S := k) (N := N)).toRingHom
  have hΦ : ∀ f : OneRing k N, (Shrink.algEquiv k (coneField P)).symm
      (algebraMap (OneRing k N ⧸ P) (coneField P) (Ideal.Quotient.mk P f)) =
        aeval (pt.{u, w} pp) (oneBlock (S := k) (N := N) f) := fun f => by
    rw [aeval_pt_oneBlock]; rfl
  obtain ⟨i, hi⟩ := hrel
  have hyi : pt.{u, w} pp i ≠ 0 := by
    rw [← aeval_X (R := k) (pt.{u, w} pp) i, Ne, aeval_pt_eq_zero_iff]; exact hi
  have hmap : (FieldNumbers.homFracDegZero P).map (Shrink.algEquiv k (coneField P)).symm.toAlgHom =
      funField (k := k) (pt.{u, w} pp) := by
    rw [FieldNumbers.homFracDegZero, IntermediateField.adjoin_map]
    refine le_antisymm (IntermediateField.adjoin_le_iff.mpr ?_) (IntermediateField.adjoin_le_iff.mpr ?_)
    · rintro _ ⟨_, ⟨b, f, g, hf, hg, hgP, rfl⟩, rfl⟩
      have hF := isHomogeneous_oneBlock hf
      have hG := isHomogeneous_oneBlock hg
      have hchart : ∀ (F : Poly k N), F.IsHomogeneous (b ()) →
          aeval (pt.{u, w} pp) F / pt.{u, w} pp i ^ b () ∈ funField (k := k) (pt.{u, w} pp) := fun F hF' =>
        VeryAmpleDim.mem_funField_of_mem_chartRing hyi ⟨F, X i ^ b (), b (), pow_mem (X_mem_monos
          (Finset.mem_singleton_self i)) _, hF', isHomogeneous_X_pow _ _, by rw [map_pow, aeval_X]⟩
      convert IntermediateField.div_mem _ (hchart _ hF) (hchart _ hG) using 1
      rw [div_div_div_cancel_right₀ (pow_ne_zero (b ()) hyi), ← hΦ, ← hΦ, map_div₀]
      rfl
    · rintro _ ⟨j, l, hj, rfl⟩
      apply IntermediateField.subset_adjoin
      have hjP : (X (⟨(), j⟩ : Σ _ : Unit, Fin (N + 1)) : OneRing k N) ∉ P := by
        change oneBlock (S := k) (N := N) (X (⟨(), j⟩ : Σ _ : Unit, Fin (N + 1))) ∉ pp
        rw [← aeval_pt_eq_zero_iff, aeval_pt_oneBlock]; exact hj
      refine ⟨_, ⟨NumbersDVR.blockWeight (fun _ : Unit => Fin (N + 1)) ⟨(), l⟩, X ⟨(), l⟩, X ⟨(), j⟩,
        isWeightedHomogeneous_X k _ _,
        isWeightedHomogeneous_X k _ _, hjP, rfl⟩, ?_⟩
      simp only [AlgEquiv.coe_toAlgHom, AlgHom.coe_coe, map_div₀, hΦ, aeval_pt_oneBlock]
      rfl
  unfold FieldNumbers.resDeg
  rw [dite_eq_left (inferInstance : P.IsPrime), ← hmap]
  exact ((FieldNumbers.homFracDegZero P).equivMap _).toLinearEquiv.finrank_eq.symm

end InterNumPointDeg

theorem InterNumPointDeg.proof (hIR : InterNumRestrict.Statement.{u, w}) : InterNumPointDeg.Statement.{u, w} := by
  intro k _ Ω _ _ N x pp h
  haveI : Small.{w} k := small_of_injective (algebraMap k Ω).injective
  haveI := h.isPrime
  have hpt := InterNumPointDeg.primeOf_pt.{u, w} pp h.homog
  have hsub : IsSubvar (InterNumPointDeg.pt.{u, w} pp) pp 0 := ⟨h.isPrime, h.homog, hpt.le, h.relevant, h.dim⟩
  have hxy : ∀ i, InterNumPointDeg.pt.{u, w} pp i ≠ 0 → x i ≠ 0 := by
    intro i hi hx
    apply hi
    rw [← aeval_X (R := k) (InterNumPointDeg.pt.{u, w} pp) i, InterNumPointDeg.aeval_pt_eq_zero_iff]
    exact h.le ((mem_primeOf_of_isHomogeneous x (isHomogeneous_X k i)).2 (by rw [aeval_X, hx]))
  have h1 := hIR k Ω N x _ (InterNumPointDeg.pt.{u, w} pp) hxy (hpt.symm ▸ h.le) pp 0 hsub
    Fin.elim0 Fin.elim0 Fin.elim0 (fun i => i.elim0)
  have h2 := InterNumPoint.proof HilbertPoint.proof k _ N (InterNumPointDeg.pt.{u, w} pp)
    (hpt.symm ▸ hsub) ![]
  rw [hpt] at h2
  calc interNum pp (![] : Fin 0 → SubSystem k x Ω)
      = interNum pp (fun i : Fin 0 => (Fin.elim0 i : LineBundle k x).toSubSystem) :=
        congrArg _ (Subsingleton.elim _ _)
    _ = _ := h1.symm
    _ = interNum pp (![] : Fin 0 → SubSystem k (InterNumPointDeg.pt.{u, w} pp) _) :=
        congrArg _ (Subsingleton.elim _ _)
    _ = _ := h2
    _ = _ := by rw [InterNumPointDeg.finrank_funField_pt pp h.relevant]

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

namespace NefBigCountAlongMultiples

theorem two_zcomb_sub_one {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (M : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι)
    (q k : ℕ) (hkq : k < q) :
    ((2 : ℕ) • (HermLine.zcomb M (fsH ι) ((q : ℤ) - k * ((1 : ℕ) : ℤ)) ((1 : ℕ) : ℤ)).a - fun _ => (1 : ℤ)) =
      ((2 * (q - k) : ℕ) : ℤ) • M.a + fun _ => ((1 : ℕ) : ℤ) := by
  funext j
  have hfs : (fsH ι).a j = 1 := rfl
  simp only [HermLine.zcomb, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hfs]
  rw [Nat.cast_mul, Nat.cast_sub hkq.le]
  push_cast
  ring

theorem along_of_shift (hAC : AmpleCountAlongMultiples.StatementAmple) (hGD : GenDegGeomDeg.Statement)
    (hPk : PackingStatement)
    {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω} {D : ℕ} {A N : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι}
    {P0 : Ideal (MRing ι)} {II : IntersectionSystem} {e : Ω} {C T ε : ℝ} {p q : ℕ}
    (hD : 1 ≤ D) (hII : IsIntersectionSystem II) (har : IsArithVar (mCoordIdeal y) (D + 1)) (hb : Birational y)
    (hP0 : P0 ≤ mCoordIdeal y) (hsA : IsSmoothHerm A) (hq : 1 ≤ q) (hε : 0 < ε)
    (hsp : IsSemipositiveRel P0 (mCoordIdeal y) N) (hci : IsConjInvariantH N)
    (hamp : KH.AmpleV ℚ (KH.genIdeal y) N.a)
    (hamp2 : ∃ c : ℕ, 1 ≤ c ∧ KH.AmpleV ℚ (KH.genIdeal y) (c • N.a - fun _ => 1))
    (hampl : ∀ ℓ : ℕ, ℓ.Prime → KH.AmpleV (ZMod ℓ) (GroundTheory.Heights₂.Heights.HilbertSamuel.fibreIdeal ℓ y) N.a) (he0 : e ≠ 0)
    (hmap : ∀ (n : ℕ) (s : Ω), s ∈ chartLat y N.a n → s * e ^ (p * n) ∈ chartLat y A.a (q * n) ∧
      ∀ c : ℝ, IsBoundedH (mCoordIdeal y) y N n c s →
        IsBoundedH (mCoordIdeal y) y A (q * n) (c * Real.exp (((p * n : ℕ) : ℝ) * C)) (s * e ^ (p * n)))
    (hnum : (T - ε) * (q : ℝ) ^ (D + 1) + ε / 4 * (q : ℝ) ^ (D + 1) ≤
      II K ι (mCoordIdeal y) (D + 1) (fun _ => N) -
        ((D : ℝ) + 1) * ((p : ℝ) * C) * (genDeg (mCoordIdeal y) D N.a : ℝ)) :
    ∃ a : ℕ, 1 ≤ a ∧ ∀ᶠ k : ℕ in atTop,
      (T - ε) * (((a * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) ≤
        smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) (a * k) := by
  obtain ⟨b, hb1, hev⟩ := hAC K ι Ω y D (HermLine.constShift N ((p : ℝ) * C)) P0 II hD hII har hb hP0
    (isSemipositiveRel_constShift hsp _) (isConjInvariantH_constShift hci _)
    (by rw [constShift_a]; exact hamp) (by rw [constShift_a]; exact hamp2) (by rw [constShift_a]; exact hampl)
    (ε / 4 * (q : ℝ) ^ (D + 1)) (by positivity)
  have htop : II K ι (mCoordIdeal y) (D + 1) (fun _ => HermLine.constShift N ((p : ℝ) * C)) =
      II K ι (mCoordIdeal y) (D + 1) (fun _ => N) -
        ((D : ℝ) + 1) * ((p : ℝ) * C) * (genDeg (mCoordIdeal y) D N.a : ℝ) := by
    rw [ConstantShift.proof K ι (II K ι) (mCoordIdeal y) D N _ (hII K ι) har hsp.1, hGD K ι Ω y D N har hsp.1]
  have hfin := (hPk K ι Ω y D A (chartLat y A.a) har hb hsA
    (fun τ _ hs' c hc' => isIntegral_algebraMap (x := (⟨_, hs' c hc'⟩ : chartRingZ y c)))).1
  refine ⟨q * b, Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩
  filter_upwards [hev] with j hj
  have hX : (0 : ℝ) ≤ ((b * j : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ) := by positivity
  calc (T - ε) * (((q * b * j : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ))
      = ((T - ε) * (q : ℝ) ^ (D + 1)) * (((b * j : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) := by
        push_cast
        ring
    _ ≤ (II K ι (mCoordIdeal y) (D + 1) (fun _ => HermLine.constShift N ((p : ℝ) * C)) -
          ε / 4 * (q : ℝ) ^ (D + 1)) * (((b * j : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) :=
        mul_le_mul_of_nonneg_right (by rw [htop]; linarith) hX
    _ ≤ _ := hj
    _ ≤ smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) (q * (b * j)) :=
        NefCountAlongMultiples.count_shift_le he0 (hmap (b * j)) (hfin _)
    _ = _ := by rw [mul_assoc]

theorem proof (hG2 : G2.Statement) (hAC : AmpleCountAlongMultiples.StatementAmple)
    (hNA : NefAmpleGeneric.Statement) (hGD : GenDegGeomDeg.Statement) (hPk : PackingStatement) :
    NefBigCountAlongMultiples.Statement := by
  intro K _ ι _ Ω _ y D A P0 II hD hII har hb hA ε hε
  have : CharZero Ω := ArithmeticVolumeDegreeZero.charZero_of_horizontal y har.2.2.1
  let _ : LinearOrder K := LinearOrder.lift' _ (Fintype.equivFin K).injective
  let _ : ∀ k, LinearOrder (ι k) := fun k => LinearOrder.lift' _ (Fintype.equivFin (ι k)).injective
  obtain ⟨k, e, C, -, hC, he0, -, -, hpq, hconv⟩ := hG2 K ι Ω y D A P0 II hD hII har hb hA
  obtain ⟨δ, hδ, hδc⟩ := hconv (ε / 4) (by linarith)
  have hg0 : (0 : ℝ) < (genDeg (mCoordIdeal y) D A.a : ℝ) := by exact_mod_cast hA.big
  obtain ⟨q, hq⟩ := exists_nat_gt ((k : ℝ) + 1 / δ +
    4 * (((D : ℝ) + 1) * C * ((genDeg (mCoordIdeal y) D A.a : ℝ) + ε / 4)) / ε)
  have hX0 : 0 ≤ 4 * (((D : ℝ) + 1) * C * ((genDeg (mCoordIdeal y) D A.a : ℝ) + ε / 4)) / ε := by
    positivity
  have hδ' : 0 < 1 / δ := by positivity
  have hkq : k * 1 < q := by
    have : (k : ℝ) < q := by linarith
    rw [mul_one]
    exact_mod_cast this
  have hq1 : 1 ≤ q := by omega
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq1
  have hpqδ : ((1 : ℕ) : ℝ) / q < δ := by
    have h1 : 1 / δ < q := by linarith
    rw [div_lt_iff₀ hδ] at h1
    rw [Nat.cast_one, div_lt_iff₀ hqpos]
    linarith
  have hqC : ((D : ℝ) + 1) * C * ((genDeg (mCoordIdeal y) D A.a : ℝ) + ε / 4) < q * (ε / 4) := by
    have h1 : 4 * (((D : ℝ) + 1) * C * ((genDeg (mCoordIdeal y) D A.a : ℝ) + ε / 4)) / ε < q := by linarith
    rw [div_lt_iff₀ hε] at h1
    linarith
  obtain ⟨hsp, hci, hamp, hampl, hmap⟩ := hpq 1 q one_pos hkq
  obtain ⟨htop, hdeg⟩ := hδc 1 q one_pos (by omega) hpqδ
  have hamp2 : ∃ c : ℕ, 1 ≤ c ∧ KH.AmpleV ℚ (KH.genIdeal y)
      (c • (HermLine.zcomb A (fsH ι) ((q : ℤ) - k * ((1 : ℕ) : ℤ)) ((1 : ℕ) : ℤ)).a - fun _ => 1) := by
    refine ⟨2, by norm_num, ?_⟩
    rw [two_zcomb_sub_one A q k (by omega)]
    exact hNA K ι Ω y D A P0 (2 * (q - k)) 1 har hA.normalForm_baseLattice_le_dualSpan_sup_line hA.semipos (by omega) le_rfl
  exact along_of_shift hAC hGD hPk hD hII har hb hA.normalForm_baseLattice_le_dualSpan_sup_line hA.semipos.1 hq1 hε hsp hci hamp hamp2 hampl he0 hmap
    (NefCountAlongMultiples.num_bound hε hqpos hC htop hdeg hqC)

end NefBigCountAlongMultiples

end

end GroundTheory.Heights₂.Heights.Targets
end
