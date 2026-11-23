module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle011
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CycDim
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.MemDivSuppOfDivCycleNeZero
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def RegularityLocalProduct.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (f g : MRing ι) (a : K → ℕ) (x : funField P) (t : Ideal (MRing ι) → MRing ι)
    (yf yg : Ideal (MRing ι) → FractionRing (MRing ι ⧸ P)),
    IsArithVar P 1 → IsMultiHomog f a → IsMultiHomog g a → f ∉ P → g ∉ P →
    (x : FractionRing (MRing ι ⧸ P)) *
        algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P g) =
      algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P f) →
    (∀ W ∈ divSupp P f ∪ divSupp P g, IsMultiHomog (t W) a ∧ t W ∉ W ∧
      yf W * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P (t W)) =
        algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P f) ∧
      yg W * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P (t W)) =
        algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P g)) →
    ∑ᶠ W ∈ divSupp P f, Real.log (Nat.card (locRing P W ⧸ locIdeal P W (yf W))) -
        ∑ᶠ W ∈ divSupp P g, Real.log (Nat.card (locRing P W ⧸ locIdeal P W (yg W))) =
      ∑ᶠ σ : funField P →+* ℂ, Real.log ‖σ x‖

end

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem LocRingChartLoc.proof : LocRingChartLoc.Statement := by
  classical
  intro K _ ι _ P W hP hW hPW hrel
  let L := FractionRing (MRing ι ⧸ P)
  let q : MRing ι →+* L := (algebraMap (MRing ι ⧸ P) L).comp (Ideal.Quotient.mk P)
  have hq : ∀ f, f ∉ W → q f ≠ 0 := fun f hf h => hf (hPW (by
    rwa [RingHom.comp_apply, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at h))
  have hnz : ∀ v, v ∉ W → Ideal.Quotient.mk P v ∈ nonZeroDivisors (MRing ι ⧸ P) := fun v hv =>
    mem_nonZeroDivisors_of_ne_zero fun h => hv (hPW (Ideal.Quotient.eq_zero_iff_mem.mp h))

  have hfrac : ∀ u v a, IsMultiHomog u a → IsMultiHomog v a → v ∉ W → q u / q v ∈ locRing P W := by
    intro u v a hu hv hvW
    refine Subring.subset_closure ⟨u, v, a, hnz v hvW, hvW, hu, hv, ?_⟩
    rw [IsFractionRing.mk'_eq_div]
    rfl
  choose c hc using hrel

  let g : (Σ k, ι k) → L := fun p => q (X p) / q (X ⟨p.1, c p.1⟩)
  let B : Subring L := Subring.closure (Set.range g)
  have hTB : Subring.closure ((Finset.univ.image g : Finset L) : Set L) = B := by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  have hBS : B ≤ locRing P W := Subring.closure_le.mpr (by
    rintro _ ⟨p, rfl⟩
    exact hfrac _ _ _ (AvoidRing.isMultiHomog_X p.1 p.2) (AvoidRing.isMultiHomog_X p.1 (c p.1)) (hc p.1))
  let θ : MRing ι →+* L := eval₂Hom (Int.castRingHom L) g
  have hθB : ∀ f, θ f ∈ B := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C r => rw [eval₂Hom_C, eq_intCast]; exact intCast_mem _ r
    | add f₁ f₂ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
    | mul_X f p hf => rw [map_mul, eval₂Hom_X']; exact mul_mem hf (Subring.subset_closure ⟨p, rfl⟩)

  have hkey : ∀ u a, IsMultiHomog u a → q u = θ u * q (∏ k, X ⟨k, c k⟩ ^ a k) := by
    intro u a hu
    conv_lhs => rw [u.as_sum]
    conv_rhs => rw [u.as_sum]

    rw [map_sum, map_sum, Finset.sum_mul, map_prod]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hT : ∏ k, q (X ⟨k, c k⟩ ^ a k) = ∏ p : Σ k, ι k, q (X ⟨p.1, c p.1⟩) ^ m p := by
      rw [Fintype.prod_sigma]
      refine Finset.prod_congr rfl fun k _ => ?_
      show q (X ⟨k, c k⟩ ^ a k) = ∏ y, q (X ⟨k, c k⟩) ^ m ⟨k, y⟩
      rw [map_pow, Finset.prod_pow_eq_pow_sum, hu m hm k]
    have hθm : θ (monomial m (AddMonoidAlgebra.coeff u m)) = ((AddMonoidAlgebra.coeff u m : ℤ) : L) * ∏ p, g p ^ m p := by
      rw [show θ _ = eval₂ (Int.castRingHom L) g _ from rfl, eval₂_monomial, eq_intCast,
        Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    have hqm : q (monomial m (AddMonoidAlgebra.coeff u m)) = ((AddMonoidAlgebra.coeff u m : ℤ) : L) * ∏ p, q (X p) ^ m p := by
      rw [monomial_eq, map_mul, map_finsuppProd, Finsupp.prod_fintype _ _ (fun _ => by simp)]
      simp only [map_pow]
      congr 1
      exact eq_intCast (q.comp C) _
    rw [hT, hθm, hqm, mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← mul_pow]
    congr 1
    exact (div_mul_cancel₀ _ (hq _ (hc p.1))).symm
  refine ⟨Finset.univ.image g, hTB ▸ hBS, fun z hz => ?_⟩
  rw [hTB]
  obtain ⟨u, v, a, hu, hv, hvW, hzv⟩ := LocRingFrac.proof K ι P W hP hW hPW z hz
  have hTW := AvoidRing.coordProd_not_mem hW c hc a
  have hu' := hkey u a hu
  have hv' := hkey v a hv
  have hinv := hfrac _ v a (AvoidRing.isMultiHomog_coordProd c a) hv hvW
  have hθv : θ v ≠ 0 := fun h => hq v hvW (by rw [hv', h, zero_mul])
  refine ⟨θ u, hθB u, θ v, hθB v, hθv, ?_, ?_⟩
  · have he : (θ v)⁻¹ = q (∏ k, X ⟨k, c k⟩ ^ a k) / q v := by
      rw [eq_div_iff (hq v hvW), hv', ← mul_assoc, inv_mul_cancel₀ hθv, one_mul]
    rw [he]
    exact hinv
  · apply mul_right_cancel₀ (hq _ hTW)
    rw [mul_assoc, ← hv', ← hu']
    exact hzv

end

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo

theorem PtsAddFirst.cxHessian_add {D : ℕ} {a b ψ : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ}
    (ha : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 a y') (hb : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 b y')
    (hψ : ψ =ᶠ[𝓝 y] fun y' => a y' + b y') :
    cxHessian ψ y = cxHessian a y + cxHessian b y := by
  have h1 : fderiv ℝ ψ =ᶠ[𝓝 y] fun y' => fderiv ℝ a y' + fderiv ℝ b y' := by
    filter_upwards [hψ.fderiv (𝕜 := ℝ), ha, hb] with y' h1 h2 h3
    rw [h1]
    exact ((h2.differentiableAt (by norm_num)).hasFDerivAt.add
      (h3.differentiableAt (by norm_num)).hasFDerivAt).fderiv
  have da2 : DifferentiableAt ℝ (fderiv ℝ a) y :=
    (ha.self_of_nhds.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have db2 : DifferentiableAt ℝ (fderiv ℝ b) y :=
    (hb.self_of_nhds.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hH : fderiv ℝ (fderiv ℝ ψ) y = fderiv ℝ (fderiv ℝ a) y + fderiv ℝ (fderiv ℝ b) y := by
    rw [h1.fderiv_eq]
    exact (da2.hasFDerivAt.add db2.hasFDerivAt).fderiv
  ext i j
  simp only [cxHessian, hH, Matrix.add_apply, add_apply]
  push_cast
  ring

theorem PtsAddFirst.mixedDisc_cons_add {D : ℕ} (A B : Matrix (Fin (D + 1)) (Fin (D + 1)) ℂ)
    (C : Fin D → Matrix (Fin (D + 1)) (Fin (D + 1)) ℂ) :
    mixedDisc (Fin.cons (A + B) C : Fin (D + 1) → _) =
      mixedDisc (Fin.cons A C : Fin (D + 1) → _) + mixedDisc (Fin.cons B C : Fin (D + 1) → _) := by
  have h := ReciprocityTheory.AnForm.A.mdisc_update_add (Fin.cons A C : Fin (D + 1) → _) 0 A B
  simp only [Fin.update_cons_zero] at h
  exact h

theorem PtsAddFirst.maDensity_cons_add {D : ℕ} (f g h : (Fin (D + 1) → ℂ) → ℝ)
    (ψ : Fin D → (Fin (D + 1) → ℂ) → ℝ) (y : Fin (D + 1) → ℂ)
    (hH : cxHessian h y = cxHessian f y + cxHessian g y) :
    maDensity (Fin.cons h ψ) y = maDensity (Fin.cons f ψ) y + maDensity (Fin.cons g ψ) y := by
  have hc : ∀ u : (Fin (D + 1) → ℂ) → ℝ, (fun k => cxHessian ((Fin.cons u ψ : Fin (D + 1) → _) k) y) =
      Fin.cons (cxHessian u y) (fun k => cxHessian (ψ k) y) := by
    intro u
    funext k
    refine Fin.cases ?_ (fun i => ?_) k <;> simp
  simp only [maDensity, hc, hH, PtsAddFirst.mixedDisc_cons_add, Complex.add_re]
  ring

theorem PtsAddFirst.pot_cons {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}
    (M : HermLine ι) (L : Fin e → HermLine ι) :
    pot (Fin.cons M L : Fin (e + 1) → HermLine ι) = Fin.cons (fun z => Real.log (M.h z)) (pot L) := by
  funext j z
  refine Fin.cases ?_ (fun i => ?_) j <;> simp [pot]

theorem PtsAddFirst.sheetDensity_add {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {e : ℕ} (Q : Ideal (MRing ι)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1 + 1) → ℂ))
    (L : Fin e → HermLine ι) (M N : HermLine ι) (hM : IsSmoothHerm M) (hN : IsSmoothHerm N)
    (g : ((Σ k, ι k) → ℂ) → ℝ) (y : Fin (e + 1) → ℂ) (w : ((k : K) → ι k) → ℂ) :
    sheetDensity Q Ψ (Fin.cons (fun z => Real.log ((M.tensor N).h z)) (pot L)) g y w =
      sheetDensity Q Ψ (Fin.cons (fun z => Real.log (M.h z)) (pot L)) g y w +
        sheetDensity Q Ψ (Fin.cons (fun z => Real.log (N.h z)) (pot L)) g y w := by
  by_cases hγ : ∃ γ, IsSheet Q Ψ y w γ
  · simp only [sheetDensity, dif_pos hγ]
    set γ := hγ.choose
    have hs : IsSheet Q Ψ y w γ := hγ.choose_spec
    have han : ∀ᶠ y' in 𝓝 y, AnalyticAt ℂ γ y' := (sheet_analyticAt osgood hs).eventually_analyticAt
    have hmc : ∀ᶠ y' in 𝓝 y, γ y' ∈ mcPts Q := hs.2.mono fun _ h => h.2.1
    have hcd : ∀ {A : HermLine ι}, IsSmoothHerm A →
        ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 (fun y'' => Real.log (A.h (γ y''))) y' := fun hA =>
      (han.and hmc).mono fun y' h => pot_contDiffAt hA h.1 h.2.1
    have hsum : (fun y' => Real.log ((M.tensor N).h (γ y'))) =ᶠ[𝓝 y]
        fun y' => Real.log (M.h (γ y')) + Real.log (N.h (γ y')) := hmc.mono fun y' h =>
      Real.log_mul (M.pos _ h.1).ne' (N.pos _ h.1).ne'
    have hcons : ∀ u : ((Σ k, ι k) → ℂ) → ℝ,
        (fun j y' => (Fin.cons u (pot L) : Fin (e + 1) → _) j (γ y')) =
          Fin.cons (fun y' => u (γ y')) (fun j y' => pot L j (γ y')) := by
      intro u
      funext j y'
      refine Fin.cases ?_ (fun i => ?_) j <;> simp
    rw [hcons, hcons, hcons, PtsAddFirst.maDensity_cons_add _ _ _ _ _
      (PtsAddFirst.cxHessian_add (hcd hM) (hcd hN) hsum), mul_add]
  · simp only [sheetDensity, dif_neg hγ, add_zero]

theorem PtsAddFirst.proof (hInt : PtsIntegrableStatement) : PtsAddFirst.Statement := by
  intro K _ ι _ Q e L M N E t hQ hL hM hN hE ht
  have hL' : ∀ A : HermLine ι, IsSmoothHerm A → ∀ j, IsSmoothHerm ((Fin.cons A L : Fin (e + 1) → _) j) :=
    fun A hA j => Fin.cases hA (fun i => hL i) j
  have hMN : IsSmoothHerm (M.tensor N) := hM.mul hN
  by_cases hΨ : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1 + 1) → ℂ), IsGoodProj Q Ψ
  · simp only [ptsIntegral, dif_pos hΨ, ptsIntegralAt]
    have hI : ∀ A : HermLine ι, IsSmoothHerm A → Integrable (fun y => ∑ᶠ w ∈ fibre Q hΨ.choose y,
        sheetDensity Q hΨ.choose (Fin.cons (fun z => Real.log (A.h z)) (pot L)) (logNorm E t) y w) := by
      intro A hA
      have h := hInt K ι Q (e + 1) hΨ.choose (Fin.cons A L) E t hQ hΨ.choose_spec (hL' A hA) hE ht
      rwa [PtsAddFirst.pot_cons] at h
    rw [← integral_add (hI M hM) (hI N hN)]
    congr 1
    funext y
    rw [← finsum_mem_add_distrib (fibreFinite K ι Q (e + 1) hΨ.choose hQ hΨ.choose_spec y)]
    exact finsum_mem_congr rfl fun w _ => PtsAddFirst.sheetDensity_add Q _ L M N hM hN _ y w
  · simp only [ptsIntegral, dif_neg hΨ, add_zero]

end GroundTheory.Heights₂.Heights.Inter
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

section Helpers

variable {F : Type} [Field F]

theorem linearForm_fin_one_eq {g : MvPolynomial (Fin 1) F} (hg : g.IsHomogeneous 1) :
    g = C (AddMonoidAlgebra.coeff g (Finsupp.single 0 1)) * X 0 := by
  ext d
  rw [coeff_C_mul, coeff_X]
  by_cases h : Finsupp.single 0 1 = d
  · subst h
    simp
  · rw [if_neg h, mul_zero]
    by_contra hne
    apply h
    have hw := hg hne
    refine Finsupp.ext fun i => ?_
    fin_cases i
    simp [Finsupp.weight_apply, Finsupp.sum_fintype] at hw ⊢
    omega

theorem isHomogeneous_of_isMultiHomog_one {K₀ : Type} [Fintype K₀] {ι₀ : K₀ → Type}
    [∀ k, Fintype (ι₀ k)] (hK : Fintype.card K₀ = 1) {f : MRingOver F ι₀}
    (hf : IsMultiHomog f fun _ => 1) : f.IsHomogeneous 1 := by
  intro d hd
  have h := hf d (mem_support_iff.mpr hd)
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [Pi.one_apply, smul_eq_mul, mul_one]
  rw [Fintype.sum_sigma]
  simp [h, hK]

end Helpers

theorem LineFibreBlocks.proof (hLin : LinearQuotient.Statement) : LineFibreBlocks.Statement := by
  intro F _ K₀ _ ι₀ _ k₀ Q J hk hQ ⟨S, hS, hQS⟩ hJ m
  classical
  have hK : Fintype.card K₀ = 1 := Fintype.card_eq_one_iff.mpr ⟨k₀, hk⟩
  have hQp : Q.IsPrime := hQ.1.1
  obtain ⟨i₀, hi₀⟩ := hQ.1.2.2 k₀
  set ℓ : MRingOver F ι₀ := X ⟨k₀, i₀⟩ with hℓdef
  obtain ⟨r, φ, hφs, hφk, hφX⟩ := hLin F (Σ k, ι₀ k) (insert ℓ S) (by
    rintro f (rfl | hf)
    · exact isHomogeneous_X F _
    · exact isHomogeneous_of_isMultiHomog_one hK (hS f hf))
  set W : Ideal (MRingOver F ι₀) := RingHom.ker φ with hWdef
  have hQW : Q ⊔ Ideal.span {ℓ} = W := by
    rw [hφk, Ideal.span_insert, hQS, sup_comm]
  have hWp : W.IsPrime := RingHom.ker_isPrime φ
  have hWmin : W ∈ (Q ⊔ Ideal.span {ℓ}).minimalPrimes := by
    rw [hQW, Ideal.minimalPrimes_eq_subsingleton_self]
    rfl

  have hdim := cyc_dim_quot_minimal_add_one hi₀ hWmin (fun h => by
    rw [hQ.2] at h
    exact ENat.natCast_ne_top _ (WithBot.coe_injective h))
  have hdimW : ringKrullDim (MRingOver F ι₀ ⧸ W) = ((1 : ℕ) : WithBot ℕ∞) :=
    cyc_withBot_eq_of_add_one (by rw [hdim, hQ.2, hK])
  rw [hWdef, ringKrullDim_eq_of_ringEquiv (Ideal.quotientKerAlgEquivOfSurjective hφs).toRingEquiv,
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add] at hdimW
  have hr : r = 1 := by
    have h : ENat.card (Fin r) = (1 : ℕ∞) := WithBot.coe_injective hdimW
    rw [ENat.card_eq_coe_natCard] at h
    have h2 : Nat.card (Fin r) = 1 := by exact_mod_cast h
    simpa using h2
  subst hr

  have hex : ∃ s, (X s : MRingOver F ι₀) ∉ W := by
    by_contra hno
    simp only [not_exists, not_not] at hno
    have hφ0 : φ = (Algebra.ofId F _).comp (aeval fun _ => (0 : F)) := by
      apply MvPolynomial.algHom_ext
      intro s
      have h0 := hno s
      rw [hWdef, RingHom.mem_ker] at h0
      simp [h0]
    obtain ⟨f, hf⟩ := hφs (X 0)
    rw [hφ0] at hf
    have := congrArg (AddMonoidAlgebra.coeff · (Finsupp.single 0 1)) hf
    simp [Algebra.ofId_apply, coeff_X, algebraMap_eq, coeff_C] at this
    rw [if_neg (Finsupp.single_ne_zero.mpr one_ne_zero).symm] at this
    exact zero_ne_one this
  obtain ⟨s₁, hs₁⟩ := hex
  have hWrel : IsRelevant W := fun k => by
    obtain rfl : k = s₁.1 := (hk k).trans (hk s₁.1).symm
    exact ⟨s₁.2, hs₁⟩

  have hdivℓ : divCycle Q ℓ = Finsupp.single W 1 := inh_divCycle_prime Q ℓ W hQW hWrel
  have hℓpow : ∀ n : ℕ, ℓ ^ n ∉ Q := fun n h => hi₀ (hQp.mem_of_pow_mem n h)
  have hdivpow : ∀ n : ℕ, divCycle Q (ℓ ^ n) = Finsupp.single W n := by
    intro n
    induction n with
    | zero => simp [divCycle_one]
    | succ n ih =>
      rw [pow_succ, divCycle_mul hQp (hℓpow n) hi₀, ih, hdivℓ, ← Finsupp.single_add]

  have hWpv : IsProjVarF W 0 :=
    isProjVarF_of_mem_divSupp (n := 0) hQ (isMultiHomog_X k₀ i₀) hi₀ ⟨hWmin, hWrel⟩
  set j : ∀ k, ι₀ k := fun k => (hWrel k).choose with hjdef
  have hj : IsChart W j := fun k => (hWrel k).choose_spec
  set p₁ : Σ k, ι₀ k := ⟨k₀, j k₀⟩ with hp₁
  set a : (Σ k, ι₀ k) → F := fun s => AddMonoidAlgebra.coeff (φ (X s)) (Finsupp.single 0 1) with hadef
  have hφXs : ∀ s, φ (X s) = C (a s) * X 0 := fun s => linearForm_fin_one_eq (hφX s)
  have ha1 : a p₁ ≠ 0 := by
    intro h0
    apply hj k₀
    rw [hWdef, RingHom.mem_ker, hφXs, h0, C_0, zero_mul]
  set c : (Σ k, ι₀ k) → F := fun s => a s / a p₁ with hcdef
  have hev : aeval c = (aeval fun _ : Fin 1 => (a p₁)⁻¹).comp φ := by
    apply MvPolynomial.algHom_ext
    intro s
    simp [hφXs, hcdef, div_eq_mul_inv]
  have hpt : ∀ L : Fin 0 → K₀ → ℤ, J W 0 L = 1 := by
    intro L
    rw [hJ.1 W L j hWpv hj]
    unfold ptDeg chartIdeal
    rw [inh_finrank_quot _ c]
    · rfl
    · apply sup_le
      · intro f hf
        rw [RingHom.mem_ker, ← coe_aeval_eq_eval, hev]
        rw [hWdef, RingHom.mem_ker] at hf
        simp [hf]
      · rw [Ideal.span_le]
        rintro _ ⟨k, rfl⟩
        obtain rfl : k = k₀ := hk k
        rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, eval_X, map_one]
        exact sub_eq_zero.mpr (div_self ha1)
    · intro s
      have h1 : X s - C (c s) * X p₁ ∈ W := by
        rw [hWdef, RingHom.mem_ker, map_sub, map_mul, algHom_C, hφXs, hφXs, ← mul_assoc,
          algebraMap_eq, ← C_mul, hcdef, div_mul_cancel₀ _ ha1, sub_self]
      have h2 : C (c s) * (X p₁ - 1) ∈
          Ideal.span (Set.range fun k => (X ⟨k, j k⟩ : MRingOver F ι₀) - 1) :=
        Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨k₀, rfl⟩)
      have e : X s - C (c s) = (X s - C (c s) * X p₁) + C (c s) * (X p₁ - 1) := by ring
      rw [e]
      exact Ideal.add_mem _ (Ideal.mem_sup_left h1) (Ideal.mem_sup_right h2)

  have e1 : (![m] : Fin 1 → K₀ → ℤ) = Fin.snoc (α := fun _ => K₀ → ℤ) Fin.elim0 m := by
    funext i
    fin_cases i
    rfl
  have hmk : ∀ k, m k = m k₀ := fun k => by rw [hk k]
  have hhomℓ : ∀ n : ℕ, IsMultiHomog (ℓ ^ n) (fun _ => n) := fun n => by
    have := isMultiHomog_pow (isMultiHomog_X (F := F) (ι := ι₀) k₀ i₀) n
    convert this using 1
    funext k
    rw [hk k]
    simp
  have h1Q : (1 : MRingOver F ι₀) ∉ Q := fun h => hQp.ne_top ((Ideal.eq_top_iff_one _).mpr h)
  rw [e1]
  obtain ⟨n, hn | hn⟩ := Int.eq_nat_or_neg (m k₀)
  · rw [hJ.2 Q 0 Fin.elim0 m (ℓ ^ n) 1 hQ ⟨fun _ => n, 0, hhomℓ n, isMultiHomog_one, hℓpow n, h1Q,
      fun k => by simp [hmk k, hn]⟩, ratDiv, hdivpow, divCycle_one]
    simp [inh_cycEval_single, hpt, hn]
  · rw [hJ.2 Q 0 Fin.elim0 m 1 (ℓ ^ n) hQ ⟨0, fun _ => n, isMultiHomog_one, hhomℓ n, h1Q, hℓpow n,
      fun k => by simp [hmk k, hn]⟩, ratDiv, hdivpow, divCycle_one]
    simp only [Finsupp.mapRange_zero, Finsupp.mapRange_single, zero_sub]
    rw [← Finsupp.single_neg, inh_cycEval_single, hpt, hn]
    simp

end GroundTheory.Heights₂.Heights.Inter
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def RegularityFunctionFieldNumber.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)),
    IsArithVar P 1 → ∃ hF : IsField (funField P), @NumberField (funField P) hF.toField

end

end GroundTheory.Heights₂.Heights.Inter
end
