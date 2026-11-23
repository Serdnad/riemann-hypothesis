module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsOrthFull
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle001
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle004
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle009
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle029
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsHorizontalTwist
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistHeightIntegralDecomposition
public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle030
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Matrix.Hermitian
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
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
import ReciprocityTheory.AnalyticForms.MaIntEmpty
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.InFlagDomainOne

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.HmCont

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

variable {g : ℕ}

def cvec (z : Fin g → ℂ) : Fin g ⊕ Fin g → ℝ :=
  Sum.elim (fun k => (z k).re) (fun k => (z k).im)

def realBlock (H : Matrix (Fin g) (Fin g) ℂ) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ :=
  Matrix.fromBlocks (H.map Complex.im) (-(H.map Complex.re)) (H.map Complex.re) (H.map Complex.im)

theorem cvec_dot_realBlock (H : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    cvec z ⬝ᵥ realBlock H *ᵥ cvec w = (z ⬝ᵥ H *ᵥ star w).im := by
  simp only [GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.cvec, GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.realBlock, dotProduct, Matrix.mulVec, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.map_apply, Matrix.neg_apply,
    Complex.im_sum, Complex.re_sum, Complex.mul_im, Complex.mul_re, Pi.star_apply, Complex.star_def,
    Complex.conj_re, Complex.conj_im, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem gram_det_ne_zero {Λ ι : Type} [AddCommGroup Λ] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ Λ) (form : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ) (inj : Function.Injective form) :
    (Matrix.of fun i j => form (b i) (b j)).det ≠ 0 := by
  intro hdet
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
  have hform : form (∑ i, c i • b i) = 0 := by
    refine b.ext fun j => ?_
    have hj := congrFun hc j
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Pi.zero_apply] at hj

    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    LinearMap.zero_apply]
    exact hj
  have hsum : ∑ i, c i • b i = 0 := inj (by rw [hform, map_zero])
  exact hc0 (funext (Fintype.linearIndependent_iff.mp b.linearIndependent c hsum))

theorem continuous_of_congruence {ι X : Type} [Fintype ι] [DecidableEq ι] [TopologicalSpace X]
    (T G : X → Matrix ι ι ℝ) (W : Matrix ι ι ℝ) (hT : Continuous T) (hW : W.det ≠ 0)
    (h : ∀ x, (T x)ᵀ * G x * T x = W) : Continuous G := by
  have hdet : ∀ x, (T x).det ≠ 0 := by
    intro x h0
    apply hW
    rw [← h x, Matrix.det_mul, Matrix.det_mul, h0, mul_zero]
  have hG : ∀ x, G x = ((T x).det ^ 2)⁻¹ • ((T x).adjugateᵀ * W * (T x).adjugate) := by
    intro x
    have h1 : (T x).adjugateᵀ * ((T x)ᵀ * G x * T x) * (T x).adjugate = (T x).det ^ 2 • G x := by
      calc (T x).adjugateᵀ * ((T x)ᵀ * G x * T x) * (T x).adjugate
          = (T x * (T x).adjugate)ᵀ * G x * (T x * (T x).adjugate) := by
            rw [Matrix.transpose_mul]
            simp only [Matrix.mul_assoc]
        _ = (T x).det ^ 2 • G x := by
            simp only [Matrix.mul_adjugate, Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul,
              Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul, sq]
    rw [h x] at h1
    rw [h1, smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 (hdet x)), one_smul]
  have hcont : Continuous fun x => ((T x).det ^ 2)⁻¹ • ((T x).adjugateᵀ * W * (T x).adjugate) := by
    have hd : Continuous fun x => (T x).det := hT.matrix_det
    have ha : Continuous fun x => (T x).adjugate := hT.matrix_adjugate
    exact ((hd.pow 2).inv₀ fun x => pow_ne_zero 2 (hdet x)).smul
      ((ha.matrix_transpose.matrix_mul continuous_const).matrix_mul ha)
  rw [show G = fun x => ((T x).det ^ 2)⁻¹ • ((T x).adjugateᵀ * W * (T x).adjugate) from funext hG]
  exact hcont

theorem continuous_Hm (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type)
    [AddCommGroup Λ] [Module (𝓞 E) Λ] (X : Type) [TopologicalSpace X] (R : X → RiemLat E g Λ)
    (form : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ) (hform : ∀ x, (R x).form = form)
    (hP : ∀ v, Continuous fun x => (R x).P v) : Continuous fun x => (R x).Hm := by
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · exact continuous_of_const fun x => isEmptyElim x
  have hlat : ∀ S : GlobalTheory.CompanionTheory.Ar.Cusp.RiemLat E g Λ,
      Module.Free ℤ Λ ∧ Module.Finite ℤ Λ ∧ Module.finrank ℤ Λ = 2 * g ∧ Function.Bijective S.form := by
    intro S
    obtain ⟨h1, h2, h3, _, _, h4, _, _, _, _, _, _, _, _⟩ := S
    exact ⟨h1, h2, h3, h4⟩
  have hIm : ∀ (S : GlobalTheory.CompanionTheory.Ar.Cusp.RiemLat E g Λ) (u v : Λ),
      ((S.P u) ⬝ᵥ S.Hm *ᵥ star (S.P v)).im = S.form u v := by
    intro S u v
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, h, _, _⟩ := S
    exact h u v
  obtain ⟨hfree, hfin, hrank, hbij⟩ := hlat (R x₀)
  have hinj : Function.Injective form := by
    rw [← hform x₀]
    exact hbij.1
  obtain ⟨b⟩ : Nonempty (Module.Basis (Fin g ⊕ Fin g) ℤ Λ) :=
    ⟨(Module.finBasisOfFinrankEq ℤ Λ (hrank.trans (two_mul g))).reindex finSumFinEquiv.symm⟩
  obtain ⟨W, hWdef⟩ : ∃ W : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ,
      W = Matrix.of fun i j => ((form (b i) (b j) : ℤ) : ℝ) := ⟨_, rfl⟩
  have hW : W.det ≠ 0 := by
    have h0 := GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.gram_det_ne_zero b form hinj
    have hmap : W = (Int.castRingHom ℝ).mapMatrix (Matrix.of fun i j => form (b i) (b j)) := by
      ext i j
      rw [hWdef, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.of_apply]
      simp
    rw [hmap, ← RingHom.map_det]
    simpa using h0
  have hT : Continuous fun x =>
      (Matrix.of fun a i => GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.cvec ((R x).P (b i)) a : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ) := by
    refine continuous_matrix fun a i => ?_
    rcases a with k | k
    · exact Complex.continuous_re.comp ((continuous_apply k).comp (hP (b i)))
    · exact Complex.continuous_im.comp ((continuous_apply k).comp (hP (b i)))
  have hTGT : ∀ x,
      (Matrix.of fun a i => GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.cvec ((R x).P (b i)) a : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ)ᵀ *
        GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.realBlock (R x).Hm *
        (Matrix.of fun a i => GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.cvec ((R x).P (b i)) a : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ) = W := by
    intro x
    ext i j
    rw [Matrix.mul_assoc]
    calc _ = GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.cvec ((R x).P (b i)) ⬝ᵥ
            GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.realBlock (R x).Hm *ᵥ GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.cvec ((R x).P (b j)) := rfl
      _ = (((R x).P (b i)) ⬝ᵥ (R x).Hm *ᵥ star ((R x).P (b j))).im :=
          GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.cvec_dot_realBlock _ _ _
      _ = (R x).form (b i) (b j) := hIm (R x) (b i) (b j)
      _ = W i j := by rw [hform x, hWdef, Matrix.of_apply]
  have hG : Continuous fun x => GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.realBlock (R x).Hm :=
    GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.continuous_of_congruence
      (fun x => (Matrix.of fun a i => GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.cvec ((R x).P (b i)) a :
        Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ))
      (fun x => GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.realBlock (R x).Hm) W hT hW hTGT
  refine continuous_matrix fun k l => ?_
  have hre : Continuous fun x => ((R x).Hm k l).re := by
    have h := hG.matrix_elem (Sum.inr k) (Sum.inl l)
    simp only [GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.realBlock, Matrix.fromBlocks_apply₂₁, Matrix.map_apply] at h
    exact h
  have him : Continuous fun x => ((R x).Hm k l).im := by
    have h := hG.matrix_elem (Sum.inl k) (Sum.inl l)
    simp only [GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.realBlock, Matrix.fromBlocks_apply₁₁, Matrix.map_apply] at h
    exact h
  have heq : (fun x => (R x).Hm k l) =
      fun x => (((R x).Hm k l).re : ℂ) + (((R x).Hm k l).im : ℂ) * Complex.I :=
    funext fun x => (Complex.re_add_im _).symm
  show Continuous fun x => (R x).Hm k l
  rw [heq]
  exact (Complex.continuous_ofReal.comp hre).add ((Complex.continuous_ofReal.comp him).mul continuous_const)

end GlobalTheory.CompanionTheory.Ar.Cusp.HmCont
end
end

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

theorem _root_.GlobalTheory.T.measurable_cusp_weight_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (X : Type) [MeasurableSpace X] (R : X → RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (form : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ), (∀ x, (R x).form = form) → (∀ I, Measurable fun x => (R x).nz σ I) → (∀ x, BddAbove {y | ∃ I, (R x).IsCusp I ∧ y = -Real.log ((R x).nz σ I)}) → Measurable fun x => (R x).cuspW σ := by
  intro E _ _ _ g Λ _ _ Ψ _ X _ R σ form hform hnz _
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · exact measurable_of_empty _
  have : Module.Free ℤ Λ := (R x₀).free
  have : Module.Finite ℤ Λ := (R x₀).fin
  have : Countable (Submodule (𝓞 E) Λ) := by
    have : Countable Λ :=
      (Module.finBasis ℤ Λ).equivFun.toEquiv.injective.countable
    have : Countable (Submodule ℤ Λ) := by
      have hspan : Function.Surjective (fun s : Finset Λ => Submodule.span ℤ (s : Set Λ)) := by
        intro N
        obtain ⟨s, hs⟩ := (IsNoetherian.noetherian N : N.FG)
        exact ⟨s, hs⟩
      exact hspan.countable
    exact (Submodule.restrictScalars_injective ℤ (𝓞 E) Λ).countable
  let C : Submodule (𝓞 E) Λ → Prop := fun I =>
    I ≠ ⊥ ∧ GroundTheory.Heights₂.Heights.LowerBoundFree.IsSaturated I ∧
      GroundTheory.Heights₂.Heights.LowerBoundFree.IsIsoSub form I
  have hC (x : X) (I : Submodule (𝓞 E) Λ) : (R x).IsCusp I ↔ C I := by
    simp only [RiemLat.IsCusp, C, hform x]
  have hset (x : X) : {y | ∃ I, (R x).IsCusp I ∧ y = -Real.log ((R x).nz σ I)} =
      Set.range fun I : {I // C I} => -Real.log ((R x).nz σ I.1) := by
    ext y
    constructor
    · rintro ⟨I, hI, rfl⟩
      exact ⟨⟨I, (hC x I).1 hI⟩, rfl⟩
    · rintro ⟨I, rfl⟩
      exact ⟨I.1, (hC x I.1).2 I.2, rfl⟩
  have hsup : Measurable fun x => ⨆ I : {I // C I}, -Real.log ((R x).nz σ I.1) :=
    Measurable.iSup fun I => (Real.measurable_log.comp (hnz I.1)).neg
  have heq : (fun x => (R x).cuspW σ) =
      fun x => max 0 (⨆ I : {I // C I}, -Real.log ((R x).nz σ I.1)) := by
    funext x
    simp only [RiemLat.cuspW, hset x, iSup]
  rw [heq]
  exact measurable_const.max hsup
end

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

namespace GlobalTheory.CompanionTheory.Ar.Cusp

theorem riemLat_assemble_of_quot : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g g' : ℕ) (Λ Λ' : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] [AddCommGroup Λ'] [Module (𝓞 E) Λ'] (R : RiemLat E g Λ) (R₁ : RiemLat E g' Λ') (D : AddSubgroup Λ) (π : Λ → Λ') (q : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (Hm' : Matrix (Fin g') (Fin g') ℂ) (B' : 𝓞 E →+* Module.End ℂ (Fin g' → ℂ)), (∀ x', ∃ x ∈ D, π x = x') → (∀ x ∈ D, ∀ y ∈ D, π (x + y) = π x + π y) → (∀ (a : 𝓞 E), ∀ x ∈ D, a • x ∈ D ∧ π (a • x) = a • π x) → (∀ x ∈ D, π x = 0 → q (R.P x) = 0) → (∀ a z, B' a (q z) = q (R.B a z)) → Hm'.IsHermitian → (∀ z : Fin g' → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm' *ᵥ star z).re) → (∀ x ∈ D, ∀ y ∈ D, (q (R.P x) ⬝ᵥ Hm' *ᵥ star (q (R.P y))).im = R₁.form (π x) (π y)) → ∃ R' : RiemLat E g' Λ', R'.form = R₁.form ∧ R'.Hm = Hm' ∧ ∀ x ∈ D, R'.P (π x) = q (R.P x) := by
  intro E _ _ _ g g' Λ Λ' _ _ _ _ R R₁ D π q Hm' B' hsurj hadd hsmul hker hB hHm hpos hform
  choose s hsD hs using hsurj
  have hwd : ∀ x ∈ D, ∀ y ∈ D, π x = π y → q (R.P x) = q (R.P y) := by
    intro x hx y hy hxy
    have hxy' : x - y ∈ D := D.sub_mem hx hy
    have h1 := hadd (x - y) hxy' y hy
    rw [sub_add_cancel, hxy] at h1
    have h2 : π (x - y) = 0 :=
      calc π (x - y) = π (x - y) + π y - π y := (add_sub_cancel_right _ _).symm
        _ = π y - π y := by rw [← h1]
        _ = 0 := sub_self _
    have h3 := hker _ hxy' h2
    rwa [map_sub, map_sub, sub_eq_zero] at h3
  let P' : Λ' →+ (Fin g' → ℂ) := AddMonoidHom.mk' (fun x' => q (R.P (s x'))) (fun x' y' => by
    show q (R.P (s (x' + y'))) = q (R.P (s x')) + q (R.P (s y'))
    have hD : s x' + s y' ∈ D := D.add_mem (hsD x') (hsD y')
    have h := hwd _ (hsD (x' + y')) _ hD (by rw [hs, hadd _ (hsD x') _ (hsD y'), hs, hs])
    rw [h, map_add (f := _), map_add (f := _)])
  have hP' : ∀ x ∈ D, P' (π x) = q (R.P x) := fun x hx => hwd _ (hsD (π x)) _ hx (hs (π x))
  refine ⟨⟨R₁.1, R₁.2, R₁.3, R₁.form, R₁.5, R₁.6, R₁.7, P', Hm', hHm, hpos, ?_, B', ?_⟩, rfl, rfl, hP'⟩
  · intro x' y'
    have h := hform _ (hsD x') _ (hsD y')
    rw [hs, hs] at h
    exact h
  · intro a x'
    have hax : a • s x' ∈ D := (hsmul a _ (hsD x')).1
    have h1 : π (a • s x') = a • x' := by rw [(hsmul a _ (hsD x')).2, hs]
    calc P' (a • x') = P' (π (a • s x')) := by rw [h1]
      _ = q (R.P (a • s x')) := hP' _ hax
      _ = q (R.B a (R.P (s x'))) := by rw [R.14]
      _ = B' a (q (R.P (s x'))) := (hB a _).symm

end GlobalTheory.CompanionTheory.Ar.Cusp
end

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

namespace GlobalTheory.CompanionTheory.Ar.Cusp.GramPos

open scoped ComplexOrder

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ]
  [Module (𝓞 E) Λ]

theorem posDef_Hm_transpose (R : RiemLat E g Λ) : (R.Hmᵀ).PosDef := by
  have hH : (R.Hmᵀ).IsHermitian := by
    ext i j
    exact R.herm.apply j i
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hH fun x hx => ?_
  have h1 := R.pos x hx
  have e : star x ⬝ᵥ (R.Hmᵀ *ᵥ x) = x ⬝ᵥ R.Hm *ᵥ star x := by
    rw [Matrix.mulVec_transpose, dotProduct_comm, ← Matrix.dotProduct_mulVec]
  have him : (star x ⬝ᵥ (R.Hmᵀ *ᵥ x)).im = 0 := hH.im_star_dotProduct_mulVec_self x
  rw [Complex.pos_iff]
  exact ⟨by rw [e]; exact h1, him.symm⟩

theorem gram_eq_mul (R : RiemLat E g Λ) {m : ℕ} (u : Fin m → Fin g → ℂ) :
    R.gram u = ((Matrix.of u)ᵀ)ᴴ * R.Hmᵀ * (Matrix.of u)ᵀ := by
  ext a b
  simp only [RiemLat.gram, RiemLat.ip, Matrix.of_apply, Matrix.mul_apply, dotProduct, Matrix.mulVec,
    Matrix.conjTranspose_apply, Matrix.transpose_apply, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem det_pos_of_linearIndependent (R : RiemLat E g Λ) {m : ℕ} (u : Fin m → Fin g → ℂ)
    (hu : LinearIndependent ℂ u) : 0 < (R.gram u).det := by
  have hC : Function.Injective ((Matrix.of u)ᵀ).mulVec := Matrix.mulVec_injective_iff.2 hu
  rw [gram_eq_mul]
  exact ((posDef_Hm_transpose R).conjTranspose_mul_mul_same hC).det_pos

theorem linearIndependent_of_det_ne_zero (R : RiemLat E g Λ) {m : ℕ} (u : Fin m → Fin g → ℂ)
    (hd : (R.gram u).det ≠ 0) : LinearIndependent ℂ u := by
  have hinj : Function.Injective (R.gram u).mulVec :=
    Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hd))
  have hC : Function.Injective ((Matrix.of u)ᵀ).mulVec := by
    intro x y hxy
    apply hinj
    have hxy' : (Matrix.of u)ᵀ *ᵥ x = (Matrix.of u)ᵀ *ᵥ y := hxy
    simp only [gram_eq_mul, ← Matrix.mulVec_mulVec, hxy']
  exact Matrix.mulVec_injective_iff.1 hC

theorem gram_det_pos_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ) (m : ℕ) (u : Fin m → Fin g → ℂ), (LinearIndependent ℂ u → 0 < (R.gram u).det.re ∧ (R.gram u).det.im = 0) ∧ ((R.gram u).det ≠ 0 → LinearIndependent ℂ u) := by
  intro E _ _ _ g Λ _ _ R m u
  refine ⟨fun hu => ?_, linearIndependent_of_det_ne_zero R u⟩
  have h := Complex.pos_iff.1 (det_pos_of_linearIndependent R u hu)
  exact ⟨h.1, h.2.symm⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.GramPos
end

section

open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder

theorem _root_.GlobalTheory.T.weighted_flag_degree_lower_bound : ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (Ψ : Type) [Fintype Ψ] (j k : ℕ) (A : FlagPair E Ψ (j + 1) (k + 1)) (lam : Ψ → Fin (j + 1 + (k + 1)) → ℝ) (Λ μ C : ℝ), (∀ τ, Antitone (lam τ)) → (∀ τ i, |lam τ i| ≤ Λ) → 0 ≤ μ → E.slopeMax ≤ (μ : EReal) → (∀ τ, |A.flatDeg τ| ≤ C) → -(Fintype.card Ψ * (2 * Λ * (j + 1 + (k + 1)) * μ + Λ * C)) ≤ A.lamDeg lam := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LowerAny.lamDeg_lower | exact GlobalTheory.CompanionTheory.Ar.LowerAny.lamDeg_lower | (intros; apply GlobalTheory.CompanionTheory.Ar.LowerAny.lamDeg_lower <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem pb_indep_cover : ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (D : ℕ) (σ : Type) [Fintype σ] (S : AnSys D σ) (P : Ideal (MRing ι)) (Re : Realis S P) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k', ι' k') → Ω) (S' : AnSys D σ) (Re' : Realis S' (mCoordIdeal y)) (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')), IsBlockMap κ v → imageZ v (mCoordIdeal y) = P → (∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ a, IsPullHerm κ v (Re.line a t) (Re'.line a t)) → Re'.deg = IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y) * Re.deg → Re'.PB II = Re.PB II := by
  intro II hII K _ ι _ D σ _ S P Re K' _ ι' _ Ω _ _ y S' Re' κ v hbl hP hpull hdeg
  have hr0 : IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y) ≠ 0 := by
    intro h
    have hd := Re'.deg_pos
    rw [hdeg, h, zero_mul] at hd
    exact lt_irrefl 0 hd
  have hr : ((IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y) : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast hr0
  have harith : IsArithVar (imageZ v (mCoordIdeal y)) (D + 1) := by
    rw [hP]
    exact Re.arith
  have key : ∀ w : Fin (D + 1) → σ, Re'.limNum II w = Re.limNum II w := by
    intro w
    have ht0 : 0 < S.t₀ := (S.reg (w 0)).1
    have hle : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ≤ S.t₀ := by
      filter_upwards [Ioo_mem_nhdsGT ht0] with t ht using ht.2.le
    have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
    have heq : (fun t => Re'.num II t w) =ᶠ[𝓝[>] (0 : ℝ)] (fun t => Re.num II t w) := by
      filter_upwards [hpull, hle, hpos] with t hpt hle' hpos'
      have hPF := hII.2.2.1 K ι K' ι' κ v Ω y (D + 1) (fun j => Re.line (w j) t)
        (fun j => Re'.line (w j) t) hbl Re'.arith harith
        (fun j => Re.line_smooth (w j) t hpos' hle') (fun j => hpt (w j))
      rw [hP] at hPF
      show (II K' ι' (mCoordIdeal y) (D + 1) fun j => Re'.line (w j) t) / (Re'.deg : ℝ)
        = (II K ι P (D + 1) fun j => Re.line (w j) t) / (Re.deg : ℝ)
      rw [hPF, hdeg]
      push_cast
      exact mul_div_mul_left _ _ hr
    unfold Realis.limNum Filter.limUnder
    rw [Filter.map_congr heq]
  unfold Realis.PB
  rw [show Re'.limNum II = Re.limNum II from funext key]

end GlobalTheory.CompanionTheory.Ar.PB
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem tsgPoly_linePoly_smul_toWt_injective :
    (∀ (D : ℕ) (κ : ℕ → ℝ) (v : ℝ) (Q : Polynomial ℝ), tsgPoly D κ (Polynomial.C v * Q) = Polynomial.C v * tsgPoly D κ Q) ∧ (∀ (σ : Type) (c : σ → ℝ) (e : σ → ℤ) (v : ℝ) (Q : MvPolynomial σ ℝ), linePoly c e (C v * Q) = Polynomial.C v * linePoly c e Q) ∧ ∀ (Ψ : Type) (N : ℕ), Function.Injective (toWt : MvPolynomial (Ψ × Fin N) ℝ → MvPolynomial (Ψ × Fin N) ℝ) :=
  PositivityTheory.Xgp.t_tsg_smul

end GlobalTheory.CompanionTheory.Ar.PB
end

section

open MeasureTheory Filter Topology Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.mobius_pair_analytic_det_jacobian_eq : ∀ (d : ℕ) (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ), (∀ p q, Differentiable ℂ fun y' => g y' p q) → ∀ (y : Fin d → ℂ) (a₀ a₁ : ℂ), GlobalTheory.CompanionTheory.Ar.PB.FibPt.den (g y) a₀ ≠ 0 → GlobalTheory.CompanionTheory.Ar.PB.FibPt.den (g y) a₁ ≠ 0 → AnalyticAt ℂ (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob2 g) (Fin.cons a₀ (Fin.cons a₁ y)) ∧ (ReciprocityTheory.AnForm.A.jacC (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob2 g) (Fin.cons a₀ (Fin.cons a₁ y))).det = GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD (g y) a₀ * GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD (g y) a₁ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobius_pair_analyticAt_and_det_jacobian | exact GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobius_pair_analyticAt_and_det_jacobian | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobius_pair_analyticAt_and_det_jacobian <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw

theorem _root_.GlobalTheory.T.fibre_twist_eq_union_embeddings : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ) (Q : Ideal (MRing ι)) (e : ℕ) (Ψ : (((o : Option K) → Tb ι o) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (y : Fin e → ℂ), p ≠ 0 → Nonempty K → IsMultiHomogIdeal Q → fibre (twist p Q) Ψ y = embL (vPlus p) '' fibre Q (pj (vPlus p) Ψ) y ∪ embL (vMinus p) '' fibre Q (pj (vMinus p) Ψ) y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Tw.Fib.fibre_twist | exact GlobalTheory.CompanionTheory.Ar.Tw.Fib.fibre_twist | (intros; apply GlobalTheory.CompanionTheory.Ar.Tw.Fib.fibre_twist <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw

theorem _root_.GlobalTheory.T.twist_height_integral_decomposition : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ) (Q : Ideal (MRing ι)) (e : ℕ) (Ψ : (((o : Option K) → Tb ι o) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (L' : Fin e → HermLine (Tb ι)) (A' : HermLine (Tb ι)) (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRing ι) (v : Fin 2 → ℂ), p ≠ 0 → IsArithVar Q (e + 1) → IsArithVar (twist p Q) (e + 1) → IsGoodProj (twist p Q) Ψ → (∀ j, IsSmoothHerm (L' j)) → IsSmoothHerm A' → IsSectionOn (twist p Q) A' (inc s) → (v = vPlus p ∨ v = vMinus p) → (∀ j, ∀ z ∈ mcPts Q, (L' j).h (glue z v) = (L j).h z) → (∀ z ∈ mcPts Q, A'.h (glue z v) = A.h z) → ∀ᵐ y, ∀ w, sheetDensity (twist p Q) Ψ (pot L') (logNorm A' (inc s)) y (embL v w) = sheetDensity Q (pj v Ψ) (pot L) (logNorm A s) y w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Tw.SheetD.density_twist | exact GlobalTheory.CompanionTheory.Ar.Tw.SheetD.density_twist | (intros; apply GlobalTheory.CompanionTheory.Ar.Tw.SheetD.density_twist <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxComp

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt
open ReciprocityTheory.AnForm.R (conePts)

abbrev cxIdeal {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) :
    Ideal (MRingOver ℂ ι) :=
  P.map (map (Int.castRingHom ℂ) : MRing ι →+* MRingOver ℂ ι)

def cxPosDens {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}
    (S : Set ((Σ k, ι k) → ℂ)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ) (y : Fin e → ℂ) : ℝ :=
  ∑ᶠ w ∈ setFibre S Ψ y, max (setSheetDensity S Ψ φ g y w) 0

end GlobalTheory.CompanionTheory.Ar.Pub.CxComp
end
end

section

open Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.log_det_comparable_gram_bound : ∀ (n k : ℕ) (G G₀ : Matrix (Fin n) (Fin n) ℂ) (V : Matrix (Fin n) (Fin k) ℂ) (m : ℝ), 1 ≤ m → G₀.PosDef → G.PosDef → ((m : ℂ) • G₀ - G).PosSemidef → ((m : ℂ) • G - G₀).PosSemidef → LinearIndependent ℂ Vᵀ → |Real.log (Vᴴ * G * V).det.re - Real.log (Vᴴ * G₀ * V).det.re| ≤ k * Real.log m := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.gram_det_log_size | exact GlobalTheory.CompanionTheory.Ar.PB.gram_det_log_size | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.gram_det_log_size <;> assumption)
end
