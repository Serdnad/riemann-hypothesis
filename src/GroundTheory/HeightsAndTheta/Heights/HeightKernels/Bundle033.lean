module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle019
public import GroundTheory.HeightsAndTheta.Heights.Intersections.NotLtLtOfMemMinimalPrimes
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle016
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PIntDomainDim
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle021
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle029
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionBounded
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle030
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
public import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

namespace ChartEnergySymmetry

theorem cxHessian_sub {D : ℕ} {f g : (Fin D → ℂ) → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (y : Fin D → ℂ) : cxHessian (fun y' => f y' - g y') y = cxHessian f y - cxHessian g y := by
  have h1 : fderiv ℝ (fun y' => f y' - g y') = fun z => fderiv ℝ f z - fderiv ℝ g z := by
    funext z
    exact fderiv_sub (hf.differentiable (by norm_num) z) (hg.differentiable (by norm_num) z)
  have hf' : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hg' : Differentiable ℝ (fderiv ℝ g) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have h2 : fderiv ℝ (fderiv ℝ (fun y' => f y' - g y')) y =
      fderiv ℝ (fderiv ℝ f) y - fderiv ℝ (fderiv ℝ g) y := by
    rw [h1]
    exact fderiv_sub (hf' y) (hg' y)
  ext i j
  simp only [cxHessian, h2, _root_.sub_apply, Matrix.sub_apply]
  push_cast
  ring

theorem mixedDisc_update_sub {D : ℕ} (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (k : Fin D)
    (X Y : Matrix (Fin D) (Fin D) ℂ) :
    mixedDisc (Function.update A k (X - Y)) =
      mixedDisc (Function.update A k X) - mixedDisc (Function.update A k Y) := by
  obtain ⟨M, hM⟩ := (by
    show ∃ F : MultilinearMap (RingHom.id ℂ)
        (fun _ : Fin D => Matrix (Fin D) (Fin D) ℂ) ℂ,
        ⇑F = _root_.ReciprocityTheory.AnForm.mdisc
    refine ⟨MultilinearMap.mk' _root_.ReciprocityTheory.AnForm.mdisc
      _root_.ReciprocityTheory.AnForm.A.mdisc_update_add ?_, rfl⟩
    intro A k c B
    simpa only [RingHom.id_apply, smul_eq_mul] using
      (_root_.ReciprocityTheory.AnForm.A.mdisc_update_smul A k c B))
  have e : ∀ C, mixedDisc (Function.update A k C) = M.toLinearMap A k C := fun C => by
    rw [MultilinearMap.toLinearMap_apply, hM]
    rfl
  simp only [e, map_sub]

theorem maDensity_update_sub {D : ℕ} (Φ : Fin D → (Fin D → ℂ) → ℝ) (p : Fin D) {f g : (Fin D → ℂ) → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (y : Fin D → ℂ) :
    maDensity (Function.update Φ p f) y - maDensity (Function.update Φ p g) y =
      maDensity (Function.update Φ p fun y' => f y' - g y') y := by
  have key : ∀ h : (Fin D → ℂ) → ℝ, (fun k => cxHessian (Function.update Φ p h k) y) =
      Function.update (fun k => cxHessian (Φ k) y) p (cxHessian h y) := fun h => by
    funext k
    exact Function.apply_update (fun _ h' => cxHessian h' y) Φ p h k
  simp only [maDensity, key, cxHessian_sub hf hg y, mixedDisc_update_sub, Complex.sub_re]
  ring

theorem update_comp_swap {α : Type*} {n : ℕ} (Φ : Fin (n + 1) → α) (p : Fin (n + 1)) (f : α) :
    Function.update Φ p f ∘ Equiv.swap 0 p = Fin.cons f (fun i => Φ (Equiv.swap 0 p i.succ)) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp
  · simp only [Function.comp_apply, Fin.cons_succ]
    rw [Function.update_of_ne]
    intro h
    have h' := congrArg (Equiv.swap 0 p) h
    rw [Equiv.swap_apply_self, Equiv.swap_apply_right] at h'
    exact Fin.succ_ne_zero i h'

end ChartEnergySymmetry


open ChartEnergySymmetry in
theorem ChartEnergySymm.proof (hI : ChartIbpSymm.Statement) : ChartEnergySymm.Statement := by
  intro e A B C D T p hA hB hC hD hT
  obtain ⟨n, rfl⟩ : ∃ n, e = n + 1 := ⟨e - 1, by have := p.pos; omega⟩
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 p with hσ
  set T' : Fin n → Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ := fun i => T (σ i.succ) with hT'def
  have hT' : ∀ i, (T' i).PosDef := fun i => hT _
  have hpot : ∀ X, (fun j => hermChartPot (Function.update T p X j)) =
      Function.update (fun j => hermChartPot (T j)) p (hermChartPot X) := fun X => by
    funext j
    exact Function.apply_update (fun _ M => hermChartPot M) T p X j
  have hdiff : ∀ X Y : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ, X.PosDef → Y.PosDef → ∀ y,
      maDensity (fun j => hermChartPot (Function.update T p X j)) y -
          maDensity (fun j => hermChartPot (Function.update T p Y j)) y =
        maDensity (Fin.cons (fun y' => hermChartPot X y' - hermChartPot Y y')
          fun i => hermChartPot (T' i)) y := by
    intro X Y hX hY y
    rw [hpot, hpot, maDensity_update_sub _ _ (ChartEnergySwapHessian.contDiff_hermChartPot X hX)
      (ChartEnergySwapHessian.contDiff_hermChartPot Y hY), ← Inter.maDensity_comp_perm _ σ, update_comp_swap]
  simp_rw [hdiff C D hC hD, hdiff A B hA hB]
  exact hI n A B C D T' hA hB hC hD hT'

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial

noncomputable section

namespace GrassmannianLinesProjective

def single (m : ℕ) (c : Fin (m + 1)) : PlIdx 1 m :=
  ⟨{Fin.cast (Nat.add_comm m 1) c}, Finset.card_singleton _⟩

theorem single_injective (m : ℕ) : Function.Injective (single m) := by
  intro c c' h
  have := congrArg Subtype.val h
  simpa [single] using this

theorem single_surjective (m : ℕ) : Function.Surjective (single m) := by
  rintro ⟨I, hI⟩
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hI
  exact ⟨Fin.cast (Nat.add_comm 1 m) a, Subtype.ext (by simp [single])⟩

def blk : Unit → Fin 1 := fun _ => 0

def coordMap (m : ℕ) : (Σ _ : Unit, Fin (m + 1)) → (Σ _ : Fin 1, PlIdx 1 m) :=
  fun p => ⟨0, single m p.2⟩

theorem coordMap_surjective (m : ℕ) : Function.Surjective (coordMap m) := by
  rintro ⟨k, I⟩
  obtain ⟨c, rfl⟩ := single_surjective m I
  refine ⟨⟨(), c⟩, ?_⟩
  rw [Subsingleton.elim k 0]
  rfl

theorem isBlockMap (m : ℕ) : IsBlockMap blk (coordMap m) := by
  refine ⟨fun _ _ _ => Subsingleton.elim _ _, ?_, fun _ => rfl, fun q _ => coordMap_surjective m q⟩
  rintro ⟨⟨⟩, c⟩ ⟨⟨⟩, c'⟩ h
  simp only [coordMap, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h
  rw [single_injective m h]

theorem card_plIdx (m : ℕ) : Fintype.card (PlIdx 1 m) = m + 1 := by
  rw [Fintype.card_subtype, ← Finset.powerset_univ, ← Finset.powersetCard_eq_filter, Finset.card_powersetCard,
    Finset.card_univ, Fintype.card_fin, Nat.choose_one_right, add_comm]

theorem ringKrullDim_mring {K : Type} [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] :
    ringKrullDim (MRing ι) = ((1 + Fintype.card (Σ k, ι k) : ℕ) : WithBot ℕ∞) := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField,
    Nat.card_eq_fintype_card]
  push_cast
  rfl

theorem grassIdeal_eq_bot (m : ℕ) : grassIdeal 1 1 m = ⊥ := by
  have hA := GrassArithVar.proof (CoordConeArithVar.proof IntDomainDim.proof) 1 1 m le_rfl
  by_contra hne
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hle := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk (grassIdeal 1 1 m))
    Ideal.Quotient.mk_surjective (mem_nonZeroDivisors_of_ne_zero hx0) (Ideal.Quotient.eq_zero_iff_mem.mpr hx)
  rw [hA.2.2.2, ringKrullDim_mring, Fintype.card_sigma] at hle
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, card_plIdx, smul_eq_mul] at hle
  have h' : ((1 * 1 * m + 1 + 1 + 1 : ℕ) : WithBot ℕ∞) ≤ ((1 + 1 * (m + 1) : ℕ) : WithBot ℕ∞) := by
    exact_mod_cast hle
  have h'' : 1 * 1 * m + 1 + 1 + 1 ≤ 1 + 1 * (m + 1) := by exact_mod_cast h'
  omega

theorem isArithVar_bot (m : ℕ) : IsArithVar (⊥ : Ideal (MRing (PBlk (m + 1)))) (m + 1) := by
  refine ⟨⟨()⟩, ⟨Ideal.isPrime_bot, ⟨∅, by simp, by simp⟩, fun _ => ⟨0, ?_⟩⟩, ?_, ?_⟩
  · rw [Ideal.mem_bot]
    exact X_ne_zero _
  · exact Ideal.comap_bot_of_injective _ (C_injective _ _)
  · rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _), ringKrullDim_mring]
    congr 1
    simp
    omega

theorem isPullHerm (m : ℕ) :
    IsPullHerm blk (coordMap m) (fsMulti (PBlk (m + 1))) (fsMulti (plBlocks 1 1 m)) := by
  refine ⟨?_, fun z => ?_⟩
  · funext k
    rw [Subsingleton.elim k (blk ())]
    show (1 : ℤ) = Function.extend blk (fun _ => (1 : ℤ)) 0 (blk ())
    exact (Function.Injective.extend_apply (f := blk) (fun _ _ _ => Subsingleton.elim _ _)
      (fun _ => (1 : ℤ)) (0 : Fin 1 → ℤ) ()).symm
  · simp only [fsMulti, HermLine.ofMetrics, fsMetric, Fintype.prod_unique, zpow_one, coordMap]
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    exact ((Equiv.ofBijective _ ⟨single_injective m, single_surjective m⟩).sum_comp
      (fun i => ‖z ⟨0, i⟩‖ ^ 2)).symm

theorem blockFnField_le (m : ℕ) :
    blockFnField (grassCoord 1 1 m) ≤ blockFnField (grassCoord 1 1 m ∘ coordMap m) := by
  refine IntermediateField.adjoin_le_iff.mpr ?_
  rintro t ⟨p, q, -, rfl⟩
  obtain ⟨p', rfl⟩ := coordMap_surjective m p
  obtain ⟨q', rfl⟩ := coordMap_surjective m q
  exact IntermediateField.subset_adjoin _ _ ⟨p', q', Subsingleton.elim _ _, rfl⟩

end GrassmannianLinesProjective


open GrassmannianLinesProjective in
theorem GrassLinesProj.proof (hPF : PFCoordStatement) : GrassLinesProj.Statement := by
  intro m II hII
  have hd : 1 * 1 * m + 1 = m + 1 := by ring
  have hA : IsArithVar (grassIdeal 1 1 m) (m + 1) := by
    rw [← hd]
    exact GrassArithVar.proof (CoordConeArithVar.proof IntDomainDim.proof) 1 1 m le_rfl
  have himg : imageZ (coordMap m) (grassIdeal 1 1 m) = ⊥ := by
    rw [grassIdeal_eq_bot]
    exact Ideal.comap_bot_of_injective _ (rename_injective _ (isBlockMap m).2.1)
  have hB : IsArithVar (imageZ (coordMap m) (grassIdeal 1 1 m)) (m + 1) := by
    rw [himg]
    exact isArithVar_bot m
  have h := hPF II hII Unit (PBlk (m + 1)) (Fin 1) (plBlocks 1 1 m) blk (coordMap m) (GrassField 1 1 m)
    (grassCoord 1 1 m) (m + 1) (fun _ => fsMulti (PBlk (m + 1))) (fun _ => fsMulti (plBlocks 1 1 m))
    (isBlockMap m) hA hB (fun _ => FsLineSmooth.proof _ _) (fun _ => isPullHerm m)
  rw [IntermediateField.relfinrank_eq_one_iff.mpr (blockFnField_le m),
    show mCoordIdeal (grassCoord 1 1 m) = grassIdeal 1 1 m from rfl, himg, Nat.cast_one, one_mul] at h
  rw [hd]
  exact h

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField IsDedekindDomain

noncomputable section

namespace SectionQuotientFinite

variable {T : Type} [Fintype T] {K' : Type} [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K')


omit [Fintype T] in
theorem mem_blockFnField_of_mem_chartRingZ (t : T) {b : K'} (hb : b ∈ chartRingZ y (fun _ => t)) :
    b ∈ blockFnField y := by
  induction hb using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    exact IntermediateField.subset_adjoin _ _ ⟨p, ⟨(), t⟩, rfl, rfl⟩
  | algebraMap r => rw [eq_intCast]; exact intCast_mem _ r
  | add x z _ _ hx hz => exact add_mem hx hz
  | mul x z _ _ hx hz => exact mul_mem hx hz

theorem exists_int_mul_coord_mem : ∃ D : ℤ, D ≠ 0 ∧ ∀ t : T, (D : K') * y ⟨(), t⟩ ∈ integralClosure ℤ K' := by
  classical
  obtain ⟨D, hD0, hD⟩ := exists_integral_multiples ℤ ℚ (L := K') (Finset.univ.image fun t => y ⟨(), t⟩)
  refine ⟨D, hD0, fun t => ?_⟩
  have h := hD (y ⟨(), t⟩) (Finset.mem_image_of_mem _ (Finset.mem_univ t))
  rw [zsmul_eq_mul] at h
  exact h

theorem int_mul_mem_of_mem_sectionMod (hy : IsArithVar (mCoordIdeal y) 1) {D : ℤ}
    (hD : ∀ t : T, (D : K') * y ⟨(), t⟩ ∈ integralClosure ℤ K') {m : K'} (hm : m ∈ sectionMod y) :
    (D : K') * m ∈ integralClosure ℤ K' := by
  obtain ⟨t0, ht0⟩ := CurveAffineCharts.exists_chart y hy
  suffices hv : ∀ v : HeightOneSpectrum (𝓞 K'), v.valuation K' ((D : K') * m) ≤ 1 by
    obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 K') K' _ hv
    rw [← hr]
    exact r.2
  intro v
  obtain ⟨t, -, ht⟩ := Finset.exists_max_image Finset.univ (fun u => v.valuation K' (y ⟨(), u⟩))
    ⟨t0, Finset.mem_univ _⟩
  have hyt : y ⟨(), t⟩ ≠ 0 := by
    intro h0
    have h1 := ht t0 (Finset.mem_univ _)
    rw [h0, map_zero] at h1
    exact ht0 ((Valuation.zero_iff _).mp (le_antisymm h1 zero_le))
  have hmt : m / y ⟨(), t⟩ ∈ chartRingZ y (fun _ => t) :=
    SectionIndexNormAlt.mem_chartLat_iff.mp hm t hyt
  have h1 : v.valuation K' (m / y ⟨(), t⟩) ≤ 1 :=
    (Valuation.mem_integer_iff _ _).mp
      (CurveAffineCharts.mem_integer_of_mem_chartRingZ y v t (fun u => ht u (Finset.mem_univ _)) hmt)
  have h2 : v.valuation K' ((D : K') * y ⟨(), t⟩) ≤ 1 := by
    obtain ⟨r, hr⟩ : ∃ r : 𝓞 K', algebraMap (𝓞 K') K' r = (D : K') * y ⟨(), t⟩ :=
      ⟨⟨_, hD t⟩, rfl⟩
    rw [← hr]
    exact HeightOneSpectrum.valuation_le_one v r
  have e : (D : K') * m = m / y ⟨(), t⟩ * ((D : K') * y ⟨(), t⟩) := by
    field_simp
  rw [e, map_mul]
  exact mul_le_one' h1 h2

theorem fg_sectionMod (hy : IsArithVar (mCoordIdeal y) 1) : AddGroup.FG (sectionMod y) := by
  obtain ⟨D, hD0, hD⟩ := exists_int_mul_coord_mem y
  have : Module.Finite ℤ (integralClosure ℤ K') := inferInstanceAs (Module.Finite ℤ (𝓞 K'))
  let f : sectionMod y →+ integralClosure ℤ K' :=
    { toFun := fun m => ⟨(D : K') * m, int_mul_mem_of_mem_sectionMod y hy hD m.2⟩
      map_zero' := Subtype.ext (mul_zero _)
      map_add' := fun a b => Subtype.ext (mul_add _ _ _) }
  have hinj : Function.Injective f := fun a b h => by
    have h' : (D : K') * a = (D : K') * b := congrArg (fun z : integralClosure ℤ K' => (z : K')) h
    exact Subtype.ext (mul_left_cancel₀ (Int.cast_ne_zero.mpr hD0) h')
  have hfin : Module.Finite ℤ (sectionMod y) := Module.Finite.of_injective f.toIntLinearMap hinj
  exact Module.Finite.iff_addGroup_fg.mp hfin


omit [NumberField K'] in
theorem aeval_ne_zero {s : MRing (fun _ : Unit => T)} (hs : IsMultiHomog s (fun _ => 1))
    (hsP : s ∉ mCoordIdeal y) : aeval y s ≠ 0 := by
  intro h0
  apply hsP
  change s ∈ RingHom.ker (mConeMap y)
  rw [RingHom.mem_ker]
  erw [HilbertSamuel.SectionBounded.mConeMap_homog y hs]
  rw [h0, map_zero, zero_mul]

theorem exists_nat_mul_mem_span (hy : IsArithVar (mCoordIdeal y) 1) {s : MRing (fun _ : Unit => T)}
    (hs : IsMultiHomog s (fun _ => 1)) (hsP : s ∉ mCoordIdeal y) {m : K'} (hm : m ∈ sectionMod y) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : K') * m ∈ Submodule.span (curveRing y) {aeval y s} := by
  set x := aeval y s with hxdef
  have hx0 : x ≠ 0 := aeval_ne_zero y hs hsP
  obtain ⟨t, ht⟩ := CurveAffineCharts.exists_chart y hy
  have hmt : m / y ⟨(), t⟩ ∈ blockFnField y :=
    mem_blockFnField_of_mem_chartRingZ y t (SectionIndexNormAlt.mem_chartLat_iff.mp hm t ht)
  have hxt : x / y ⟨(), t⟩ ∈ blockFnField y :=
    mem_blockFnField_of_mem_chartRingZ y t (SectionIndexNormAlt.aeval_div_mem hs t)
  have hq : m / x ∈ blockFnField y := by
    have e : m / x = (m / y ⟨(), t⟩) / (x / y ⟨(), t⟩) := by
      field_simp
    rw [e]
    exact div_mem hmt hxt
  obtain ⟨n, hn, hnq⟩ := CurveAffineCharts.exists_nat_mul_mem_curveRing y hq
  refine ⟨n, hn, Submodule.mem_span_singleton.mpr ⟨⟨_, hnq⟩, ?_⟩⟩
  rw [Subring.smul_def, smul_eq_mul]
  field_simp

theorem isTorsion (hy : IsArithVar (mCoordIdeal y) 1) {s : MRing (fun _ : Unit => T)}
    (hs : IsMultiHomog s (fun _ => 1)) (hsP : s ∉ mCoordIdeal y) (q : sectionQuot y (aeval y s)) :
    ∃ n : ℕ, n ≠ 0 ∧ n • q = 0 := by
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨n, hn, hnm⟩ := exists_nat_mul_mem_span y hy hs hsP m.2
  refine ⟨n, hn, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  rw [Submodule.subtype_apply]
  simpa [nsmul_eq_mul] using hnm

end SectionQuotientFinite


open SectionQuotientFinite in
theorem SectionQuotFinite.closed : SectionQuotFinite.Statement := by
  intro T _ K' _ _ y s hy hs hsP
  have hfg : AddGroup.FG (sectionQuot y (aeval y s)) :=
    AddGroup.fg_of_surjective (f := (Submodule.mkQ _).toAddMonoidHom) (Submodule.mkQ_surjective _)
      (hG := fg_sectionMod y hy)
  let _ : Module ℤ (sectionQuot y (aeval y s)) := AddCommGroup.toIntModule _
  have hfin : Module.Finite ℤ (sectionQuot y (aeval y s)) := Module.Finite.iff_addGroup_fg.mpr hfg
  refine Module.finite_of_fg_torsion _ fun q => ?_
  obtain ⟨n, hn, hnq⟩ := isTorsion y hy hs hsP q
  refine ⟨⟨(n : ℤ), mem_nonZeroDivisors_of_ne_zero (Int.natCast_ne_zero.mpr hn)⟩, ?_⟩
  change ((n : ℤ)) • q = 0
  rw [natCast_zsmul]
  exact hnq

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField

noncomputable section

def DualStackedExcReduced.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    1 ≤ i → F'.lattice < F.lattice →
    (∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice) →
    (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    ∃ E : Ideal (MRing (stackedBlocks T)), IsStackedExc b' a E ∧
      (∀ W : Ideal (MRing (stackedBlocks T)), IsStackedExc b' a W → W = E) ∧
      multAt (stackedBase b' a) E = 1

end

end GroundTheory.Heights₂.Heights
end
