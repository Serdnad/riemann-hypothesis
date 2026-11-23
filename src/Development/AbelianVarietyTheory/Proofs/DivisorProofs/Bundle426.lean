module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle387
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClmSupBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle293
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle375
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnHeckeEisensteinFourierTerm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle365
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanRangeMulVecLe
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Tactic.Bound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle156
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle366
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle367
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle005
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Mathlib.Topology.Sheaves.Presheaf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006

@[expose] public section

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory.IntBall

noncomputable section

theorem measurePreserving_curry_lowCoord (ι κ : Type) [Fintype ι] [Fintype κ] :
    MeasurePreserving (MeasurableEquiv.curry ι κ ℂ) volume volume := by
  have h : (volume : Measure (ι × κ → ℂ)) =
      (volume : Measure (ι → κ → ℂ)).map (MeasurableEquiv.curry ι κ ℂ).symm := by
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.map_apply (MeasurableEquiv.measurable _) (MeasurableSet.univ_pi hs)]
    have e : (MeasurableEquiv.curry ι κ ℂ).symm ⁻¹' Set.univ.pi s =
        Set.univ.pi (fun i => Set.univ.pi (fun j => s (i, j))) := by
      ext f; simp [MeasurableEquiv.coe_curry_symm, Function.uncurry]
    rw [e, volume_pi, Measure.pi_pi]
    simp_rw [volume_pi, Measure.pi_pi]
    rw [Fintype.prod_prod_type]
  refine ⟨(MeasurableEquiv.curry ι κ ℂ).measurable, ?_⟩
  rw [h, Measure.map_map (MeasurableEquiv.measurable _) (MeasurableEquiv.measurable _)]
  simp

theorem lintegral_prod_zOf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (h : (Low r → ℂ) → ℝ≥0∞), Measurable h → ∫⁻ z, ∏ τ, h (zOf X z τ) = ∏ _τ : X.Ψ, ∫⁻ w, h w := by
  intro E _ _ _ r X h hh
  set e := Fintype.equivFin (Ent X) with he
  set G : (Fin (nd X) → ℂ) → ℝ≥0∞ := fun y => ∏ τ, h (fun p => y (e ⟨τ, p⟩)) with hG
  have hGm : Measurable G :=
    Finset.measurable_prod _ fun τ _ => hh.comp (Measurable.of_eval fun p => measurable_pi_apply _)
  have s1 : ∫⁻ z : V (nd X), ∏ τ, h (zOf X z τ) = ∫⁻ y, G y :=
    (GlobalTheory.volume_preserving_ofLp_complex (Fin (nd X))).lintegral_comp hGm
  set K : (X.Ψ → Low r → ℂ) → ℝ≥0∞ := fun g => ∏ τ, h (g τ) with hK
  have hKm : Measurable K := Finset.measurable_prod _ fun τ _ => hh.comp (measurable_pi_apply τ)
  have s2 : ∫⁻ y, G y = ∫⁻ f : Ent X → ℂ, K (MeasurableEquiv.curry X.Ψ (Low r) ℂ f) := by
    refine ((volume_measurePreserving_piCongrLeft (fun _ => ℂ) e).lintegral_comp hGm).symm.trans
      (lintegral_congr fun f => ?_)
    simp only [hG, hK, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
    rfl
  have s3 : ∫⁻ f : Ent X → ℂ, K (MeasurableEquiv.curry X.Ψ (Low r) ℂ f) = ∫⁻ g, K g :=
    (measurePreserving_curry_lowCoord X.Ψ (Low r)).lintegral_comp hKm
  rw [s1, s2, s3, hK, volume_pi]
  exact GlobalTheory.RestrMeas.lintegral_fintype_prod_eq_prod fun _ => hh.aemeasurable

end

end GlobalTheory.IntBall
end

section

open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp
open scoped ContDiff

noncomputable section
namespace GlobalTheory.SliceOpCont

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem norm_padL_le {κ κ' : Type} [Fintype κ] [Fintype κ'] (h : κ → V) :
    ‖(padL (κ' := κ') h : κ ⊕ κ' → V)‖ ≤ ‖h‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  cases i with
  | inl i => simpa [padL] using norm_le_pi_norm h i
  | inr j => simp [padL]

theorem sliceR_sub_eq {κ κ' : Type} [Fintype κ] [Fintype κ'] (f : SchwartzMap (κ ⊕ κ' → V) ℂ)
    (x x₀ : κ → V) :
    sliceR f x - sliceR f x₀
      = sliceR (SchwartzMap.compSubConstCLM ℂ (-(padL (κ' := κ') (x - x₀))) f - f) x₀ := by
  ext y
  have he : (Sum.elim x₀ y : κ ⊕ κ' → V) + padL (x - x₀) = Sum.elim x y := by
    funext i
    cases i with
    | inl i => simp [padL]
    | inr j => simp [padL]
  simp [SchwartzMap.compSubConstCLM_apply, he]

theorem seminorm_sliceR_le (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {κ κ' : Type} [Fintype κ] [Fintype κ'] (g : SchwartzMap (κ ⊕ κ' → V) ℂ) (x : κ → V) (k n : ℕ) :
    SchwartzMap.seminorm ℂ k n (sliceR g x) ≤ SchwartzMap.seminorm ℂ k n g := by
  have := GlobalTheory.SliceWeight.pow_norm_mul_seminorm_sliceR_le V κ κ' g 0 k n x
  simpa using this

theorem continuous_sliceR (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {κ κ' : Type} [Fintype κ] [Fintype κ'] (f : SchwartzMap (κ ⊕ κ' → V) ℂ) :
    Continuous (fun x : κ → V => sliceR f x) := by
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  refine ((schwartz_withSeminorms ℂ (κ' → V) ℂ).tendsto_nhds _ _).2 fun i ε hε => ?_
  obtain ⟨k, n⟩ := i
  set C : ℝ := 2 ^ k * ((Finset.Iic (k, n + 1)).sup fun m ↦ SchwartzMap.seminorm ℂ m.1 m.2) f
  have hcont : Continuous (fun x : κ → V => ‖x - x₀‖ * (1 + ‖x - x₀‖) ^ k * C) := by fun_prop
  have h0 : ‖x₀ - x₀‖ * (1 + ‖x₀ - x₀‖) ^ k * C = 0 := by simp
  have hev : ∀ᶠ x in nhds x₀, ‖x - x₀‖ * (1 + ‖x - x₀‖) ^ k * C < ε := by
    have := hcont.continuousAt (x := x₀)
    rw [ContinuousAt, h0] at this
    exact this (Iio_mem_nhds hε)
  filter_upwards [hev] with x hx
  refine lt_of_le_of_lt ?_ hx
  change SchwartzMap.seminorm ℂ k n (sliceR f x - sliceR f x₀) ≤ _
  rw [sliceR_sub_eq]
  refine (seminorm_sliceR_le V _ x₀ k n).trans ?_
  refine (GlobalTheory.SchwartzTranslateLip.seminorm_translate_sub_le k n k n le_rfl le_rfl _ f).trans ?_
  have hC : 0 ≤ C := by positivity
  have hp := norm_padL_le (κ' := κ') (x - x₀)
  gcongr

end GlobalTheory.SliceOpCont

open GlobalTheory.SliceOpCont in
theorem GlobalTheory.SliceOp.continuous_qOp (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (κ κ' κ₁' : Type) [Fintype κ] [Fintype κ'] [Fintype κ₁']
    (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ) (f : SchwartzMap (κ ⊕ κ' → V) ℂ) :
    Continuous (qOp P f) := by
  have hinl : Continuous (fun s : κ ⊕ κ₁' → V => s ∘ Sum.inl) := by fun_prop
  have hinr : Continuous (fun s : κ ⊕ κ₁' → V => s ∘ Sum.inr) := by fun_prop
  have hG : Continuous (fun s : κ ⊕ κ₁' → V =>
      SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ₁' → V) ℂ (P (sliceR f (s ∘ Sum.inl)))) :=
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ₁' → V) ℂ).continuous.comp
      (P.continuous.comp ((continuous_sliceR V f).comp hinl))
  have hq : qOp P f = fun s => (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ₁' → V) ℂ
      (P (sliceR f (s ∘ Sum.inl)))) (s ∘ Sum.inr) := by
    funext s; rfl
  rw [hq]
  exact continuous_eval.comp (hG.prodMk hinr)
end
end

section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

theorem _root_.GlobalTheory.T.iteratedDeriv_heckePhiFourierTransform_bound : (∀ j : ℕ, ∃ (S : Finset (ℕ × ℕ × ℕ)) (P : ℕ × ℕ × ℕ → Polynomial ℂ),
    (∀ p ∈ S, 2 ≤ p.1 + 2 * p.2.1 ∧ p.1 + 2 * p.2.1 = p.2.2 + 2 + j) ∧
    ∀ σ ∈ halfPlane, ∀ ν y : ℝ, y ≠ 0 →
      iteratedDeriv j (hTrans σ ν) y = ∑ p ∈ S, (P p).eval σ * GlobalTheory.HeckeTwo.TermSmooth.intT σ ν p.1 p.2.1 p.2.2 y) → (∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ a b m : ℕ, 2 ≤ a + 2 * b → ∀ N : ℕ, ∃ C : ℝ,
    ∀ σ ∈ K, ∀ ν y : ℝ, ν ≠ 0 → y ≠ 0 →
      ‖GlobalTheory.HeckeTwo.TermSmooth.intT σ ν a b m y‖ ≤ C * |y| ^ ((m : ℝ) + 1 - a - 2 * b - 2 * σ.re) / (1 + |ν * y|) ^ N) →
  ∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ j : ℕ, ∃ s : ℕ, ∀ N : ℕ, ∃ C : ℝ,
    ∀ σ ∈ K, ∀ ν y : ℝ, ν ≠ 0 → y ≠ 0 →
      ‖iteratedDeriv j (hTrans σ ν) y‖ ≤ C * (|y| + |y|⁻¹) ^ s / (1 + |ν * y|) ^ N := by
  first | exact @GlobalTheory.HeckeTwo.TermBoundDeriv.iteratedDeriv_hTrans_bound | exact GlobalTheory.HeckeTwo.TermBoundDeriv.iteratedDeriv_hTrans_bound | (intros; apply GlobalTheory.HeckeTwo.TermBoundDeriv.iteratedDeriv_hTrans_bound <;> assumption)
end

section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

theorem _root_.GlobalTheory.T.iteratedDeriv_heckePhiFourierTransform_repr : ∀ j : ℕ, ∃ (S : Finset (ℕ × ℕ × ℕ)) (P : ℕ × ℕ × ℕ → Polynomial ℂ),
    (∀ p ∈ S, 2 ≤ p.1 + 2 * p.2.1 ∧ p.1 + 2 * p.2.1 = p.2.2 + 2 + j) ∧
    ∀ σ ∈ halfPlane, ∀ ν y : ℝ, y ≠ 0 →
      iteratedDeriv j (hTrans σ ν) y = ∑ p ∈ S, (P p).eval σ * GlobalTheory.HeckeTwo.TermSmooth.intT σ ν p.1 p.2.1 p.2.2 y := by
  first | exact @GlobalTheory.HeckeTwo.TermSmooth.iteratedDeriv_hTrans_repr | exact GlobalTheory.HeckeTwo.TermSmooth.iteratedDeriv_hTrans_repr | (intros; apply GlobalTheory.HeckeTwo.TermSmooth.iteratedDeriv_hTrans_repr <;> assumption)
end

section

noncomputable section
open CategoryTheory Limits Opposite AlgebraicTopology

namespace GlobalTheory.EZ

abbrev BOp : Type := Free ℤ (SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ)

def bo (n m : ℕ) : BOp := Free.of ℤ (op (SimplexCategory.mk n), op (SimplexCategory.mk m))

def bop {n m p q : ℕ} (α : SimplexCategory.mk p ⟶ SimplexCategory.mk n)
    (β : SimplexCategory.mk q ⟶ SimplexCategory.mk m) : bo n m ⟶ bo p q :=
  Finsupp.single (show (op (SimplexCategory.mk n), op (SimplexCategory.mk m)) ⟶
    (op (SimplexCategory.mk p), op (SimplexCategory.mk q)) from (α.op, β.op)) 1

def clampHom (n m : ℕ) (f : ℕ → ℕ) (hf : Monotone f) : SimplexCategory.mk m ⟶ SimplexCategory.mk n :=
  SimplexCategory.mkHom ⟨fun j => ⟨min n (f j), Nat.lt_succ_of_le (min_le_left _ _)⟩,
    fun i j h => by
      change min n (f i) ≤ min n (f j)
      exact min_le_min_left n (hf (show (i : ℕ) ≤ j from h))⟩

def faceFun (i : ℕ) (j : ℕ) : ℕ := if j < i then j else j + 1

theorem faceFun_mono (i : ℕ) : Monotone (faceFun i) := by
  intro a b h
  unfold faceFun
  split_ifs <;> omega

def fc (n m i : ℕ) : SimplexCategory.mk m ⟶ SimplexCategory.mk n := clampHom n m (faceFun i) (faceFun_mono i)

def idc (n m : ℕ) : SimplexCategory.mk m ⟶ SimplexCategory.mk n := clampHom n m id monotone_id

def backc (n a b : ℕ) : SimplexCategory.mk b ⟶ SimplexCategory.mk n :=
  clampHom n b (a + ·) (fun _ _ h => Nat.add_le_add_left h a)

def dH (a b a' b' : ℕ) : bo a b ⟶ bo a' b' :=
  if a = a' + 1 ∧ b = b' then ∑ i ∈ Finset.range (a + 1), ((-1 : ℤ) ^ i) • bop (fc a a' i) (idc b b') else 0

def dV (a b a' b' : ℕ) : bo a b ⟶ bo a' b' :=
  if a = a' ∧ b = b' + 1 then ∑ j ∈ Finset.range (b + 1), ((-1 : ℤ) ^ j) • bop (idc a a') (fc b b' j) else 0

def dT (a b a' b' : ℕ) : bo a b ⟶ bo a' b' := dH a b a' b' + ((-1 : ℤ) ^ a) • dV a b a' b'

def dD (n m : ℕ) : bo n n ⟶ bo m m :=
  if n = m + 1 then ∑ i ∈ Finset.range (n + 1), ((-1 : ℤ) ^ i) • bop (fc n m i) (fc n m i) else 0

def awO (n a b : ℕ) : bo n n ⟶ bo a b := if a + b = n then bop (idc n a) (backc n a b) else 0

def idO (a b a' b' : ℕ) : bo a b ⟶ bo a' b' := if a = a' ∧ b = b' then bop (idc a a') (idc b b') else 0

section Ev

variable {C : Type*} [Category* C] [Preadditive C]


set_option backward.isDefEq.respectTransparency false in
def ev (Y : SimplicialObject (SimplicialObject C)) : BOp ⥤ C where
  obj X := (Functor.uncurry.obj Y).obj X
  map {_ _} f := f.sum fun f' (r : ℤ) => r • (Functor.uncurry.obj Y).map f'
  map_id := by
    dsimp +instances [CategoryTheory.categoryFree]
    simp
  map_comp {X Y' Z} f g := by
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f₁ f₂ w₁ w₂ =>
      rw [Preadditive.add_comp]
      rw [Finsupp.sum_add_index', Finsupp.sum_add_index']
      · simp only [w₁, w₂, Preadditive.add_comp]
      · intros; rw [zero_smul]
      · intros; simp only [add_smul]
      · intros; rw [zero_smul]
      · intros; simp only [add_smul]
    | single f' r =>
      induction g using Finsupp.induction_linear with
      | zero => simp
      | add f₁ f₂ w₁ w₂ =>
        rw [Preadditive.comp_add]
        rw [Finsupp.sum_add_index', Finsupp.sum_add_index']
        · simp only [w₁, w₂, Preadditive.comp_add]
        · intros; rw [zero_smul]
        · intros; simp only [add_smul]
        · intros; rw [zero_smul]
        · intros; simp only [add_smul]
      | single g' s =>
        rw [Free.single_comp_single _ _ f' g' r s]
        simp only [Finsupp.sum_single_index, zero_smul, Functor.map_comp, Preadditive.zsmul_comp,
          Preadditive.comp_zsmul, smul_smul, mul_comm]

set_option backward.isDefEq.respectTransparency false in
theorem ev_map_bop (Y : SimplicialObject (SimplicialObject C)) {n m p q : ℕ}
    (α : SimplexCategory.mk p ⟶ SimplexCategory.mk n) (β : SimplexCategory.mk q ⟶ SimplexCategory.mk m) :
    (ev Y).map (bop α β) =
      (Y.map α.op).app (op (SimplexCategory.mk m)) ≫ (Y.obj (op (SimplexCategory.mk p))).map β.op := by
  simp [ev, bop]
  rfl

set_option backward.isDefEq.respectTransparency false in
instance (Y : SimplicialObject (SimplicialObject C)) : (ev Y).Additive where
  map_add {X Z f g} := by
    dsimp [ev]
    rw [Finsupp.sum_add_index'] <;> simp [add_smul]

end Ev

section Cx

variable {C : Type*} [Category* C] [Preadditive C]

def diag : SimplicialObject (SimplicialObject C) ⥤ SimplicialObject C :=
  Functor.uncurry ⋙ (Functor.whiskeringLeft _ _ C).obj (Functor.diag SimplexCategoryᵒᵖ)

def diagCx (Y : SimplicialObject (SimplicialObject C)) : ChainComplex C ℕ :=
  (alternatingFaceMapComplex C).obj (diag.obj Y)

def dbl (Y : SimplicialObject (SimplicialObject C)) :
    HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  (alternatingFaceMapComplex (ChainComplex C ℕ)).obj
    (((SimplicialObject.whiskering _ _).obj (alternatingFaceMapComplex C)).obj Y)

variable [HasFiniteCoproducts C]

instance hasTotal_down (K : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ)) :
    K.HasTotal (ComplexShape.down ℕ) := fun n => by
  haveI : Finite ((ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)) ⁻¹' {n}) := by
    refine Set.Finite.to_subtype ((Set.finite_Iic n).prod (Set.finite_Iic n) |>.subset ?_)
    rintro ⟨a, b⟩ h
    simp only [Set.mem_preimage, Set.mem_singleton_iff, ComplexShape.π_def] at h
    simp only [Set.mem_prod, Set.mem_Iic]
    omega
  infer_instance

def tot (Y : SimplicialObject (SimplicialObject C)) : ChainComplex C ℕ := (dbl Y).total (ComplexShape.down ℕ)

def awF (Y : SimplicialObject (SimplicialObject C)) (n : ℕ) : (diagCx Y).X n ⟶ (tot Y).X n :=
  ∑ a : Fin (n + 1), (ev Y).map (awO n a (n - a)) ≫
    (dbl Y).ιTotal (ComplexShape.down ℕ) a (n - a) n (by simp only [ComplexShape.π_def] ; omega)

end Cx

section Sheaves

open GlobalTheory.EtC

variable (R : Type) [CommRing R]

def freeBi : SimplicialObject Spc ⥤ SimplicialObject (SimplicialObject (Shv R)) :=
  (SimplicialObject.whiskering _ _).obj ((SimplicialObject.whiskering _ _).obj (free R))

def dblF : SimplicialObject (SimplicialObject (Shv R)) ⥤
    HomologicalComplex₂ (Shv R) (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  (SimplicialObject.whiskering _ _).obj (alternatingFaceMapComplex (Shv R)) ⋙
    alternatingFaceMapComplex (ChainComplex (Shv R) ℕ)

def biChainsF : SimplicialObject Spc ⥤ HomologicalComplex₂ (Shv R) (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  freeBi R ⋙ dblF R ⋙
    (ComplexShape.embeddingDownNat.extendFunctor (Shv R)).mapHomologicalComplex (ComplexShape.down ℕ) ⋙
    ComplexShape.embeddingDownNat.extendFunctor (CochainComplex (Shv R) ℤ)

abbrev biChains (X : SimplicialObject Spc) : HomologicalComplex₂ (Shv R) (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (biChainsF R).obj X

instance hasTotal_biChains (X : SimplicialObject Spc) : (biChains R X).HasTotal (ComplexShape.up ℤ) := fun _ => by
  haveI : HasColimitsOfSize.{0, 0} (ModuleCat.{1} (ULift.{1} R)) := inferInstance
  haveI : HasColimitsOfSize.{0, 0} (Shv R) := inferInstanceAs (HasColimitsOfSize.{0, 0} (Sheaf _ _))
  haveI h := this
  exact @HasColimitsOfShape.has_colimit _ _ _ _ (HasColimitsOfSize.has_colimits_of_shape _) _

abbrev totChains (X : SimplicialObject Spc) : Cx R := (biChains R X).total (ComplexShape.up ℤ)

def biChainsXIso (X : SimplicialObject Spc) (a b : ℕ) :
    ((biChains R X).X (-(a : ℤ))).X (-(b : ℤ)) ≅
      (free R).obj ((X.obj (op (SimplexCategory.mk a))).obj (op (SimplexCategory.mk b))) :=
  (HomologicalComplex.eval _ _ (-(b : ℤ))).mapIso
      (HomologicalComplex.extendXIso _ ComplexShape.embeddingDownNat (i := a) rfl) ≪≫
    HomologicalComplex.extendXIso _ ComplexShape.embeddingDownNat (i := b) rfl

def awP (X : SimplicialObject Spc) (n a b : ℕ) :
    (bidiag.obj X).obj (op (SimplexCategory.mk n)) ⟶ (X.obj (op (SimplexCategory.mk a))).obj (op (SimplexCategory.mk b)) :=
  (X.map (idc n a).op).app (op (SimplexCategory.mk n)) ≫ (X.obj (op (SimplexCategory.mk a))).map (backc n a b).op

def awZ (X : SimplicialObject Spc) (n : ℕ) :
    ((chains R).obj (bidiag.obj X)).X (-(n : ℤ)) ⟶ (totChains R X).X (-(n : ℤ)) :=
  (chainsXIso R (bidiag.obj X) n).hom ≫
    ∑ a : Fin (n + 1), (free R).map (awP X n a (n - a)) ≫ (biChainsXIso R X a (n - a)).inv ≫
      (biChains R X).ιTotal (ComplexShape.up ℤ) (-(a : ℤ)) (-((n - a : ℕ) : ℤ)) (-(n : ℤ))
        (by simp only [ComplexShape.π_def]; omega)

end Sheaves

end GlobalTheory.EZ
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

theorem _root_.GlobalTheory.T.basisObjects_unitLoci_cover_above : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ T : C, ∃ (n : ℕ) (b : Fin n → F.obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (mp F u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → ∀ (T : C) (n : ℕ) (d : Fin n → F.obj T), Ideal.span (Set.range d) = ⊤ → ∀ (t : C') (u : T ⟶ G.obj t), Desc.VandermondeTwoBasis.CovBy F (fun S ↦ ∃ (t' : C') (a : t ⟶ t'), (∃ i, IsUnit (mp F (u ≫ G.map a) (d i))) ∧ Nonempty (G.obj t' ⟶ S)) (G.obj t) := by
  first | exact @GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.covBy_unit_above | exact GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.covBy_unit_above | (intros; apply GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.covBy_unit_above <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

theorem _root_.GlobalTheory.T.exists_glued_section_upwardFamily_standardCover : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → ∀ (t : C') (Sg : ∀ t', (t ⟶ t') → Prop), (∀ t' t'' (a : t ⟶ t') (b : t' ⟶ t''), Sg t' a → Sg t'' (a ≫ b)) → Desc.VandermondeTwoBasis.CovBy F (fun S ↦ ∃ (t' : C') (a : t ⟶ t'), Sg t' a ∧ Nonempty (G.obj t' ⟶ S)) (G.obj t) → Desc.Glue (G ⋙ F) Sg := by
  first | exact @GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.glue_upward_of_cov | exact GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.glue_upward_of_cov | (intros; apply GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.glue_upward_of_cov <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

theorem _root_.GlobalTheory.T.van1_of_covBy_upward_sieve : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → ∀ (t : C') (Sg : ∀ t', (t ⟶ t') → Prop), (∀ t' t'' (a : t ⟶ t') (b : t' ⟶ t''), Sg t' a → Sg t'' (a ≫ b)) → Desc.VandermondeTwoBasis.CovBy F (fun S ↦ ∃ (t' : C') (a : t ⟶ t'), Sg t' a ∧ Nonempty (G.obj t' ⟶ S)) (G.obj t) → Desc.Van1 (G ⋙ F) Sg := by
  first | exact @GlobalTheory.CatCoh.Desc.Basis.oneCocycle_upwardFamily_isCoboundary | exact GlobalTheory.CatCoh.Desc.Basis.oneCocycle_upwardFamily_isCoboundary | (intros; apply GlobalTheory.CatCoh.Desc.Basis.oneCocycle_upwardFamily_isCoboundary <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

theorem _root_.GlobalTheory.T.oneCocycle_invertibleLocus_isCoboundary_alt : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ T : C, ∃ (n : ℕ) (b : Fin n → F.obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (mp F u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → ∀ (T : C) (e : F.obj T) (y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → F.obj (G.obj t')), (∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), IsUnit (mp F u e) → y t t'' u (a ≫ b) = mp F (G.map b) (y t t' u a) + y t' t'' (u ≫ G.map a) b) → ∃ g : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t), ∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), IsUnit (mp F u e) → g t' (u ≫ G.map a) - mp F (G.map a) (g t u) = y t t' u a := by
  first | exact @GlobalTheory.CatCoh.Desc.Basis.oneCocycle_invertibleLocus_isCoboundary | exact GlobalTheory.CatCoh.Desc.Basis.oneCocycle_invertibleLocus_isCoboundary | (intros; apply GlobalTheory.CatCoh.Desc.Basis.oneCocycle_invertibleLocus_isCoboundary <;> assumption)
end

section

theorem GlobalTheory.FourClauses.adm : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.IrreducibleAdmissibleGL :=
  fun h k _ _ _ _ n V _ _ π hs hi => (h k).1 (Fin n) V π hs hi
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.measurable_nsq_and_psi_of_isSecOn : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (la : La) (Ω : Set Y) (h : ι → Y → ℂ), IsOpen Ω → A.IsSecOn la Ω h → (∀ i y, y ∉ Ω → h i y = 0) → Measurable (A.nsq la h) ∧ ∀ (L : La) (s : Fin n → ι → Y → ℂ), (∀ k, A.IsSec L (s k)) → Measurable (psi A L s) := by
  first | exact @GlobalTheory.OTY.measurable_nsq_extend_and_psi | exact GlobalTheory.OTY.measurable_nsq_extend_and_psi | (intros; apply GlobalTheory.OTY.measurable_nsq_extend_and_psi <;> assumption)
end

section

open NumberField Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD

theorem _root_.GlobalTheory.T.integral_multiple_in_lie_lattice : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)), Λ.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → ∀ X : Matrix (Fin r) (Fin r) E, X.trace = 0 → (∀ x y, herm G (X *ᵥ x) y + herm G x (X *ᵥ y) = 0) → ∃ N : ℕ, 0 < N ∧ (N : E) • X ∈ lieLat G Λ := by
  first | exact @GlobalTheory.DenClear.exists_natSmul_mem_lieLat | exact GlobalTheory.DenClear.exists_natSmul_mem_lieLat | (intros; apply GlobalTheory.DenClear.exists_natSmul_mem_lieLat <;> assumption)
end
