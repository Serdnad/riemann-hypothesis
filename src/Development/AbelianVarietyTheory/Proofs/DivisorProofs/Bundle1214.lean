module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle010
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.CmpbHessAtAddConst
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle002
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mix.ChartChange

section
variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

def colSum (H : Fin D → Matrix (Fin D) (Fin D) ℂ) : ℂ :=
  ∑ τ : Equiv.Perm (Fin D), (Matrix.of fun j l => H (τ l) j l).det

theorem colSum_mul_left (A : Matrix (Fin D) (Fin D) ℂ) (H : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    colSum (fun a => A * H a) = A.det * colSum H := by
  simp only [colSum, Finset.mul_sum, ← Matrix.det_mul]
  refine Finset.sum_congr rfl fun τ _ => congrArg _ ?_
  ext j l
  simp [Matrix.mul_apply]

theorem colSum_transpose (H : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    colSum (fun a => (H a).transpose) = colSum H := by
  simp only [colSum, Matrix.det_apply', Matrix.of_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun (τ ρ : Equiv.Perm (Fin D)) => ((Equiv.Perm.sign ρ : ℤ) : ℂ) * ∏ i, H (τ i) (ρ i) i)]
  refine Fintype.sum_equiv (Equiv.inv _) _ _ fun ρ => ?_
  refine Fintype.sum_equiv (Equiv.mulRight ρ⁻¹) _ _ fun τ => ?_
  simp only [Equiv.inv_apply, Equiv.Perm.sign_inv, Equiv.coe_mulRight]
  congr 1
  refine Fintype.prod_equiv ρ _ _ fun i => ?_
  simp

theorem colSum_mul (A B : Matrix (Fin D) (Fin D) ℂ) (H : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    colSum (fun a => A * H a * B) = A.det * B.det * colSum H := by
  have e : colSum (fun a => H a * B) = B.det * colSum H := by
    rw [← colSum_transpose, ← colSum_transpose H, ← Matrix.det_transpose B, ← colSum_mul_left]
    simp only [Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]
  rw [colSum_mul_left A fun a => H a * B, e, mul_assoc]

theorem dens_eq (L : Fin D → MLine p σ) (c : AlgChart p σ D) (y : CxPts p σ) :
    dens L c y = (Real.pi ^ D)⁻¹ * (colSum fun a => c.hess (L a).φ (pick (L a).φ.isLB y) y).re := rfl

theorem dens_trans (L : Fin D → MLine p σ) (c c' : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source)
    (hy' : y ∈ c'.e.source) : dens L c y = ‖transDet c.e c'.e y‖ ^ 2 * dens L c' y := by
  have ho := isOpen_over c.e c'.e.open_source
  have hm := mem_over c.e hy hy'
  have e₂ : (c'.e ∘ c.e.symm) (c.e y) = c'.e y := congrArg c'.e (c.e.left_inv hy)
  let J : Matrix (Fin D) (Fin D) ℂ :=
    Matrix.of fun l j => (fderiv ℂ (c'.e ∘ c.e.symm) (c.e y) (ReciprocityTheory.L2DbarEstimates.bas D j)) l
  have h (a) : c.hess (L a).φ (pick (L a).φ.isLB y) y =
      J.transpose * c'.hess (L a).φ (pick (L a).φ.isLB y) y * J.map (starRingEnd ℂ) := by
    have e : (fun v => ((L a).φ.φ (pick (L a).φ.isLB y) (c.e.symm v) : ℂ)) =ᶠ[𝓝 (c.e y)]
        (fun v => ((L a).φ.φ (pick (L a).φ.isLB y) (c'.e.symm v) : ℂ)) ∘ c'.e ∘ c.e.symm :=
      eventually_of_mem (ho.mem_nhds hm) fun v hv => by
        simp only [Function.comp_apply, c'.e.left_inv hv.2]
    rw [AlgChart.hess, AlgChart.hess, ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr e,
      ReciprocityTheory.L2DbarEstimates.Y.cmpa_cHess_comp ho hm (c.holo_trans c') (e₂ ▸
        Complex.ofRealCLM.contDiff.contDiffAt.comp _ ((L a).cInf.contDiffAt c' hy' (mem_pick _ y))), e₂]
  have hJ : J.det = transDet c.e c'.e y := ReciprocityTheory.L2DbarEstimates.Y.cmpa_det_jac _
  have hd : J.transpose.det * (J.map (starRingEnd ℂ)).det = ((‖transDet c.e c'.e y‖ ^ 2 : ℝ) : ℂ) := by
    have hm' : (J.map (starRingEnd ℂ)).det = starRingEnd ℂ J.det := (RingHom.map_det (starRingEnd ℂ) J).symm
    rw [hm', Matrix.det_transpose, hJ, Complex.mul_conj']
    push_cast
    rfl
  rw [dens_eq, dens_eq]
  simp only [h]
  rw [colSum_mul, hd, Complex.re_ofReal_mul]
  ring

end

theorem dens_change_chart : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (L : Fin D → MLine p σ) (c c' : AlgChart p σ D) (y : CxPts p σ), y ∈ c.e.source → y ∈ c'.e.source → dens L c y = ‖transDet c.e c'.e y‖ ^ 2 * dens L c' y :=
  fun _ _ _ _ _ _ L c c' _ hy hy' => dens_trans L c c' hy hy'

end GlobalTheory.Mix.ChartChange
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace GlobalTheory.Mix

theorem continuousOn_dens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ)
    (D : ℕ) (L : Fin D → MLine p σ) (c : AlgChart p σ D), ContinuousOn (dens L c) c.e.source := by
  intro k _ X p σ D L c y₀ hy₀
  let i : ∀ a, (L a).B.ι := fun a => pick (L a).φ.isLB y₀
  let S : Set (CxPts p σ) := c.e.source ∩ ⋂ a, ptsIn p σ ((L a).B.U (i a))
  have hSo : IsOpen S := c.e.open_source.inter (isOpen_iInter_of_finite fun a => isOpen_ptsIn _)
  have hy₀S : y₀ ∈ S := ⟨hy₀, mem_iInter.2 fun a => mem_pick _ y₀⟩
  have hH : ∀ (a : Fin D) (j l : Fin D),
      ContinuousOn (fun y => c.hess (L a).φ (i a) y j l) S := by
    intro a j l
    have hO : IsOpen (c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ ((L a).B.U (i a))) :=
      isOpen_over c.e (isOpen_ptsIn _)
    have hg : ContDiffOn ℝ ∞ (fun v => ((L a).φ.φ (i a) (c.e.symm v) : ℂ))
        (c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ ((L a).B.U (i a))) :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_chart ((L a).cInf (i a)) c)
    have hw := ReciprocityTheory.L2DbarEstimates.Y.continuousOn_wd_wdb hO hg j l
    exact hw.comp (c.e.continuousOn.mono inter_subset_left) fun y hy =>
      ⟨c.e.map_source hy.1, by
        simpa only [mem_preimage, c.e.left_inv hy.1] using mem_iInter.1 hy.2 a⟩
  let F : CxPts p σ → ℝ := fun y => (Real.pi ^ D)⁻¹ * (∑ τ : Equiv.Perm (Fin D),
    (Matrix.of fun j l => c.hess (L (τ l)).φ (i (τ l)) y j l).det).re
  have hF : ContinuousOn F S := by
    refine continuousOn_const.mul (Complex.continuous_re.comp_continuousOn
      (continuousOn_finsetSum _ fun τ _ => ?_))
    refine (continuous_id.matrix_det).comp_continuousOn ?_
    exact continuousOn_pi.2 fun j => continuousOn_pi.2 fun l => hH (τ l) j l
  have he : ∀ y ∈ S, dens L c y = F y := by
    intro y hy
    have hm : ∀ τ : Equiv.Perm (Fin D),
        (Matrix.of fun j l => c.hess (L (τ l)).φ (pick (L (τ l)).φ.isLB y) y j l) =
          Matrix.of fun j l => c.hess (L (τ l)).φ (i (τ l)) y j l := fun τ => by
      ext j l
      simp only [Matrix.of_apply]
      rw [c.hess_eq (L (τ l)).cInf hy.1 (mem_iInter.1 hy.2 (τ l)) (mem_pick _ y)]
    simp only [dens, F, hm]
  refine ContinuousAt.continuousWithinAt ?_
  refine (hF.continuousAt (hSo.mem_nhds hy₀S)).congr ?_
  filter_upwards [hSo.mem_nhds hy₀S] with y hy
  exact (he y hy).symm

end GlobalTheory.Mix
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.Cl.PsiFrame

theorem char_ext {X G : Type} [AddCommGroup X] [CommGroup G] {r : ℕ} (bX : Module.Basis (Fin r) ℤ X) (f g : X → G)
    (hf : ∀ a b, f (a + b) = f a * f b) (hg : ∀ a b, g (a + b) = g a * g b) (h : ∀ l, f (bX l) = g (bX l)) (χ : X) :
    f χ = g χ := by
  let F : X →+ Additive G := AddMonoidHom.mk' (fun x => Additive.ofMul (f x)) (fun a b => by simp [hf])
  let G' : X →+ Additive G := AddMonoidHom.mk' (fun x => Additive.ofMul (g x)) (fun a b => by simp [hg])
  have : F.toIntLinearMap = G'.toIntLinearMap := bX.ext fun l => by simp [F, G', h]
  have := LinearMap.congr_fun this χ
  simpa [F, G'] using this

def eu (z : ℂ) : ℂˣ := Units.mk0 (Complex.exp z) (Complex.exp_ne_zero z)

theorem eu_add (z w : ℂ) : eu (z + w) = eu z * eu w := by
  ext; simp [eu, Complex.exp_add]

theorem co_add {X : Type} [AddCommGroup X] {r : ℕ} (bX : Module.Basis (Fin r) ℤ X) (a b : X) :
    co bX (a + b) = co bX a + co bX b := by
  ext l; simp [co]

theorem co_neg {X : Type} [AddCommGroup X] {r : ℕ} (bX : Module.Basis (Fin r) ℤ X) (a : X) :
    co bX (-a) = - co bX a := by
  ext l; simp [co]

theorem co_basis {X : Type} [AddCommGroup X] {r : ℕ} (bX : Module.Basis (Fin r) ℤ X) (l : Fin r) :
    co bX (bX l) = Pi.single l 1 := by
  ext l'
  by_cases h : l' = l
  · subst h; simp [co]
  · simp [co, h, Finsupp.single_apply, Ne.symm h]

theorem exists_quad {X : Type} [AddCommGroup X] {r : ℕ} (bX : Module.Basis (Fin r) ℤ X) (Ψ : X → ℂˣ)
    (hev : ∀ a, Ψ (-a) = Ψ a)
    (hb : ∀ a a' b, Ψ (a + a' + b) / Ψ (a + a') / Ψ b = (Ψ (a + b) / Ψ a / Ψ b) * (Ψ (a' + b) / Ψ a' / Ψ b)) :
    ∃ (t : Matrix (Fin r) (Fin r) ℂ) (b2 : Fin r → ℂ), t.IsSymm ∧ Half b2 ∧ ∀ χ, (Ψ χ : ℂ) =
      Complex.exp (Real.pi * Complex.I * (co bX χ ⬝ᵥ t *ᵥ co bX χ) + 2 * Real.pi * Complex.I * (co bX χ ⬝ᵥ b2)) := by
  classical
  set T : X → X → ℂˣ := fun a b => Ψ (a + b) / Ψ a / Ψ b with hT
  have Ts : ∀ a b, T a b = T b a := fun a b => by simp only [hT, add_comm a b, div_right_comm]
  have Tl : ∀ a a' b, T (a + a') b = T a b * T a' b := hb
  have Tr : ∀ a b b', T a (b + b') = T a b * T a b' := fun a b b' => by rw [Ts, Tl, Ts b, Ts b']
  have hc : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  let t : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun l l' => Complex.log (T (bX l) (bX l')) / (2 * Real.pi * Complex.I)
  have ts : t.IsSymm := by
    ext l l'; simp [t, Ts (bX l)]
  have hs : ∀ u v : Fin r → ℂ, u ⬝ᵥ t *ᵥ v = v ⬝ᵥ t *ᵥ u := fun u v => by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, ts.eq, dotProduct_comm]
  have TQ : ∀ a b, T a b = eu (2 * Real.pi * Complex.I * (co bX a ⬝ᵥ t *ᵥ co bX b)) := by
    intro a b
    refine char_ext bX (fun a => T a b) (fun a => eu (2 * Real.pi * Complex.I * (co bX a ⬝ᵥ t *ᵥ co bX b)))
      (fun _ _ => Tl _ _ _) (fun _ _ => by rw [co_add, add_dotProduct, mul_add, eu_add]) (fun l => ?_) a
    refine char_ext bX (fun b => T (bX l) b) (fun b => eu (2 * Real.pi * Complex.I * (co bX (bX l) ⬝ᵥ t *ᵥ co bX b)))
      (fun _ _ => Tr _ _ _) (fun _ _ => by rw [co_add, Matrix.mulVec_add, dotProduct_add, mul_add, eu_add])
      (fun l' => ?_) b
    ext
    have : Pi.single l 1 ⬝ᵥ t *ᵥ Pi.single l' 1 = t l l' := by simp
    simp only [co_basis, this, eu, Units.val_mk0, t, Matrix.of_apply]
    rw [mul_div_cancel₀ _ hc, Complex.exp_log (Units.ne_zero _)]
  let φ : X → ℂˣ := fun χ => Ψ χ / eu (Real.pi * Complex.I * (co bX χ ⬝ᵥ t *ᵥ co bX χ))
  have φadd : ∀ a b, φ (a + b) = φ a * φ b := by
    intro a b
    have h1 : Ψ (a + b) = T a b * Ψ a * Ψ b := by
      simp only [hT]; rw [mul_right_comm, div_mul_cancel, div_mul_cancel]
    have h2 : (Real.pi * Complex.I * (co bX (a + b) ⬝ᵥ t *ᵥ co bX (a + b)) : ℂ) =
        2 * Real.pi * Complex.I * (co bX a ⬝ᵥ t *ᵥ co bX b) + Real.pi * Complex.I * (co bX a ⬝ᵥ t *ᵥ co bX a) +
          Real.pi * Complex.I * (co bX b ⬝ᵥ t *ᵥ co bX b) := by
      rw [co_add, Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, hs (co bX b) (co bX a)]
      ring
    simp only [φ]
    rw [h1, h2, eu_add, eu_add, ← TQ, _root_.mul_assoc, _root_.mul_assoc, mul_div_mul_left_eq_div, div_mul_div_comm]
  have φev : ∀ a, φ (-a) = φ a := fun a => by
    simp only [φ, hev, co_neg, Matrix.mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]
  have φ0 : φ 0 = 1 := by
    have := φadd 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have φsq : ∀ a, (φ a : ℂ) = 1 ∨ (φ a : ℂ) = -1 := fun a => by
    have := φadd a (-a)
    rw [add_neg_cancel, φ0, φev] at this
    have h2 : (φ a : ℂ) * φ a = 1 := by rw [← Units.val_mul, ← this, Units.val_one]
    exact mul_self_eq_one_iff.1 h2
  let b2 : Fin r → ℂ := fun l => if (φ (bX l) : ℂ) = 1 then 0 else 1 / 2
  refine ⟨t, b2, ts, fun l => ?_, fun χ => ?_⟩
  · simp only [b2]; split_ifs <;> simp
  · have : φ χ = eu (2 * Real.pi * Complex.I * (co bX χ ⬝ᵥ b2)) := by
      refine char_ext bX φ (fun χ => eu (2 * Real.pi * Complex.I * (co bX χ ⬝ᵥ b2))) φadd
        (fun _ _ => by rw [co_add, add_dotProduct, mul_add, eu_add]) (fun l => ?_) χ
      ext
      simp only [co_basis, single_dotProduct, _root_.one_mul, eu, Units.val_mk0, b2]
      split_ifs with h
      · simp [h]
      · rw [(φsq _).resolve_left h, show (2 * Real.pi * Complex.I * (1 / 2) : ℂ) = Real.pi * Complex.I by ring,
          Complex.exp_pi_mul_I]
    have h2 : Ψ χ = eu (Real.pi * Complex.I * (co bX χ ⬝ᵥ t *ᵥ co bX χ) + 2 * Real.pi * Complex.I * (co bX χ ⬝ᵥ b2)) := by
      rw [eu_add, ← this]; simp only [φ]; rw [mul_div_cancel]
    rw [h2]; rfl

theorem exists_cd (N : NumD ℂ) (g' r : ℕ) (bX : Module.Basis (Fin r) ℤ N.X) (e : AB N.toNumB g') (hc : e.Cub) (hs : e.Sym) :
    ∃ d : CD N g' r bX, d.toAB = e := by
  classical
  choose z hz using fun l => e.onto (N.c (bX l))
  let t12 : Matrix (Fin g') (Fin r) ℂ := Matrix.of fun i l => z l i
  let w : N.X → Fin g' → ℂ := fun χ => t12 *ᵥ co bX χ
  have wadd : ∀ a b, w (a + b) = w a + w b := fun a b => by simp only [w, co_add, Matrix.mulVec_add]
  have wneg : ∀ a, w (-a) = - w a := fun a => by simp only [w, co_neg, Matrix.mulVec_neg]
  have ceq : ∀ χ, N.c χ = e.ex (w χ) := by
    refine char_ext bX N.c (fun χ => e.ex (w χ)) N.c_add (fun a b => by rw [wadd, e.ex_add]) (fun l => ?_)
    rw [← hz]; congr 1
    ext i; simp [w, co_basis, t12]
  obtain ⟨t, b2, ht, hb2, h⟩ := exists_quad bX (fun χ => N.ψ χ * e.fr (w χ))
    (fun a => by
      have h1 := N.even a
      have h2 := hs (w a)
      rw [wneg, ← h2, ← h1, ceq, _root_.mul_assoc])
    (fun a a' b => by
      have h1 := congrArg Additive.ofMul (N.bimult a a' b)
      have h2 := congrArg Additive.ofMul (hc (w a) (w a') (w b))
      apply Additive.ofMul.injective
      simp only [ceq, wadd, ofMul_mul, ofMul_div] at h1 h2 ⊢
      linear_combination (norm := abel) h1 - h2)
  exact ⟨{ toAB := e, cub := hc, sym := hs, t12 := t12, t22 := t, b2 := b2, toricPeriodBlock_isSymm := ht, hb2 := hb2, c_eq := ceq,
           ψ_eq := fun χ => by simpa using h χ }, rfl⟩

end GlobalTheory.MBLow.Cl.PsiFrame

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow

theorem dualMap_comp_dualMapR {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    (dualMap g).comp (Chart.dualMapR f) = dualMap (g.comp f) := by
  ext a <;> simp [dualMap, Chart.dualMapR]

theorem dualMap_comp_algebraMap {R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R') :
    (dualMap g).comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp g := by
  ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem isPullback_gen {V : Type} [CommRing V] [IsDomain V] {I : Ideal V} {D : DegData V I}
    {A : PolAV (Sp (FractionRing V))} {G : Over (Sp V)} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) :
    IsPullback (U.gen.inv.left ≫ pullback.fst G.hom (jK V)) A.A.hom G.hom (spMap (algebraMap V (FractionRing V))) := by
  haveI : IsIso U.gen.inv.left := inferInstanceAs (IsIso ((Over.forget _).map U.gen.inv))
  have sq : IsPullback U.gen.inv.left A.A.hom (pullback.snd G.hom (jK V)) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by simpa using Over.w U.gen.inv⟩
  simpa using sq.paste_horiz (IsPullback.of_hasPullback G.hom (jK V))

theorem vecAt_genFibre : AllV fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (y : epsR V ⟶ G),
    (∃! yA, VecAt U.toUnifPre F y yA) ∧
    (∃! v : epsR (FractionRing V) ⟶ A.A, IsVecOver (algebraMap V (FractionRing V)) (U.gen.inv.left ≫ pullback.fst G.hom (jK V)) y v) ∧
    ∀ (v : epsR (FractionRing V) ⟶ A.A) yA, IsVecOver (algebraMap V (FractionRing V)) (U.gen.inv.left ≫ pullback.fst G.hom (jK V)) y v →
      VecAt U.toUnifPre F y yA → yA ≫ (snd (TFK (R := V) F) A.A).left = spMap (dualMap (algebraMap (FractionRing V) F)) ≫ v.left := by
  intro V _ _ _ _ _ D A G _ _ _ U F _ _ y
  have hφ := isPullback_gen U.toUnifPre
  have hT : IsPullback (fst (TFK (R := V) F) A.A).left (snd (TFK (R := V) F) A.A).left (TFK (R := V) F).hom A.A.hom :=
    IsPullback.of_hasPullback _ _
  have key : ∀ (v : epsR (FractionRing V) ⟶ A.A) yA,
      IsVecOver (algebraMap V (FractionRing V)) (U.gen.inv.left ≫ pullback.fst G.hom (jK V)) y v →
      VecAt U.toUnifPre F y yA →
      yA ≫ (snd (TFK (R := V) F) A.A).left = spMap (dualMap (algebraMap (FractionRing V) F)) ≫ v.left := by
    intro v yA hv hy
    refine hφ.hom_ext ?_ ?_
    · rw [Category.assoc, hy.2, Category.assoc]
      unfold IsVecOver at hv
      rw [hv, ← Category.assoc, spMap_comp_spMap, dualMap_comp_dualMapR]
    · rw [Category.assoc, Over.w (snd _ _), ← Over.w (fst _ _), ← Category.assoc, hy.1, Category.assoc, Over.w v]
      show spMap _ ≫ spMap _ = spMap _ ≫ spMap _
      rw [spMap_comp_spMap, spMap_comp_spMap, dualMap_comp_algebraMap]
  obtain ⟨v, hv, hvu⟩ := existsUnique_isVecOver hφ y
  refine ⟨?_, ⟨v, hv, hvu⟩, key⟩
  have w : (spMap (algebraMap F (DualNumber F)) ≫ (TFK (R := V) F).hom) =
      (spMap (dualMap (algebraMap (FractionRing V) F)) ≫ v.left) ≫ A.A.hom := by
    rw [Category.assoc, Over.w v]
    show spMap _ ≫ spMap _ = spMap _ ≫ spMap _
    rw [spMap_comp_spMap, spMap_comp_spMap, dualMap_comp_algebraMap]
  have hy : VecAt U.toUnifPre F y (hT.lift _ _ w) := by
    refine ⟨hT.lift_fst _ _ w, ?_⟩
    rw [← Category.assoc, hT.lift_snd _ _ w, Category.assoc]
    unfold IsVecOver at hv
    rw [hv, ← Category.assoc, spMap_comp_spMap, dualMap_comp_dualMapR]
  refine ⟨hT.lift _ _ w, hy, fun yA h => ?_⟩
  exact hT.hom_ext ((h.1).trans (hT.lift_fst _ _ w).symm) ((key v yA hv h).trans (hT.lift_snd _ _ w).symm)

end GlobalTheory.MBLow
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Ex GlobalTheory.MBLow
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.Cl.CubHol

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}

def pt3 (ν : NumOf D ℂ N) (d : AB N.toNumB g) (x y z : Fin g → ℂ) : Sp ℂ ⟶ (G3 D.P.A).left :=
  (lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z)))).left

def wI (x y z : Fin g → ℂ) (I : thK) : Fin g → ℂ := ∑ a ∈ I.down, ![x, y, z] a

abbrev cubW (D : DegPre R) (j : thK → D.P.L.ι) : (G3 D.P.A).left.Opens :=
  LB.wchart D.P.L (thφ D.P.A (x3 D.P.A)) j

theorem psum_eA (ν : NumOf D ℂ N) (d : AB N.toNumB g) {n : ℕ} (w : Fin n → Fin g → ℂ) (I : Finset (Fin n)) :
    psum D.P.A (fun k => ν.eA (d.ex (w k))) I = ν.eA (d.ex (∑ i ∈ I, w i)) := by
  have e0 : ν.eA (d.ex 0) = 1 := by
    have h := d.ex_add 0 0
    rw [add_zero] at h
    have h1 : d.ex 0 = 1 := left_eq_mul.mp h
    rw [h1, map_one]
  have hl : ∀ l : List (Fin n),
      l.foldr (fun k acc => padd D.P.A (ν.eA (d.ex (w k))) acc) (pzero D.P.A _) = ν.eA (d.ex (l.map w).sum) := by
    intro l
    induction l with
    | nil =>
      rw [List.foldr_nil, List.map_nil, List.sum_nil, e0, CategoryTheory.Hom.one_def]
      rfl
    | cons k l ih =>
      rw [List.foldr_cons, ih, List.map_cons, List.sum_cons, d.ex_add, map_mul, padd, CategoryTheory.Hom.mul_def]
  have hI : ((List.finRange n).filter (· ∈ I)).toFinset = I := by
    ext i
    simp
  unfold psum
  rw [hl, ← List.sum_toFinset w ((List.nodup_finRange n).filter _), hI]

theorem complexCubeAbelianPoint_thetaFace_eq_partialSum (ν : NumOf D ℂ N) (d : AB N.toNumB g) (x y z : Fin g → ℂ) (I : thK) :
    pt3 ν d x y z ≫ thφ D.P.A (x3 D.P.A) I = (ν.eA (d.ex (wI x y z I))).left := by
  have e := psum_hom (preHom (lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z))))) (x3 D.P.A) I.down
  have e' : psum D.P.A (fun i => preHom (lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z)))) (x3 D.P.A i))
      I.down = psum D.P.A (fun k => ν.eA (d.ex (![x, y, z] k))) I.down :=
    congrArg (fun q => psum D.P.A q I.down) (funext fun i => by fin_cases i <;> simp [preHom, x3])
  rw [e', psum_eA] at e
  rw [pt3, thφ, ← Over.comp_left]
  exact congrArg (fun q => q.left) e

end GlobalTheory.MBLow.Cl.CubHol

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

namespace GlobalTheory.MBLow.Cl

theorem det_eq_det_block : ∀ (g' r g : ℕ) (σ : Fin g ≃ Fin g' ⊕ Fin r) (Mx : Matrix (Fin g) (Fin g) ℂ) (MB : Matrix (Fin g') (Fin g') ℂ), (∀ i, zP σ (Mx (σ.symm (Sum.inl i))) = MB i) → (∀ l, zP σ (Mx (σ.symm (Sum.inr l))) = 0 ∧ tP σ (Mx (σ.symm (Sum.inr l))) = Pi.single l 1) → Mx.det = MB.det := by
  intro g' r g σ Mx MB h1 h2
  have key : Mx.submatrix σ.symm σ.symm =
      Matrix.fromBlocks MB (Matrix.of fun i l => Mx (σ.symm (Sum.inl i)) (σ.symm (Sum.inr l))) 0 1 := by
    ext (i | i) (j | j)
    · exact congrFun (h1 i) j
    · rfl
    · exact congrFun (h2 i).1 j
    · have := congrFun (h2 i).2 j
      simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂, Matrix.one_apply]
      rw [Pi.single_apply] at this
      simp only [eq_comm (a := i)]
      exact this
  rw [← Matrix.det_submatrix_equiv_self σ.symm Mx, key, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, _root_.mul_one]

end GlobalTheory.MBLow.Cl
end
