module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1212
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecBaseChangeOfPerf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1177
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1255
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle027
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle039
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

set_option autoImplicit false

namespace GlobalTheory.FlagPush

theorem perm_submonoid_eq_top_of_adj (k : ℕ) (T : Submonoid (Equiv.Perm (Fin k)))
    (h : ∀ a b : Fin k, (b : ℕ) = a + 1 → Equiv.swap a b ∈ T) : T = ⊤ := by
  cases k with
  | zero =>
    rw [eq_top_iff]
    intro x _
    have : x = 1 := Subsingleton.elim _ _
    rw [this]; exact T.one_mem
  | succ n =>
    rw [eq_top_iff, ← Equiv.Perm.mclosure_swap_castSucc_succ, Submonoid.closure_le]
    rintro _ ⟨i, rfl⟩
    exact h _ _ (by simp)

theorem alternating_of_adjacent_swap (ι : Type) [Fintype ι] (m : ι → ℕ)
    (L : MvPolynomial (Root m) ℝ →ₗ[ℝ] ℝ)
    (hL : ∀ (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 → ∀ Q,
      L (rename (Equiv.swap (⟨τ, a⟩ : Root m) ⟨τ, b⟩) Q) = - L Q)
    (w : ∀ τ, Equiv.Perm (Fin (m τ))) (Q : MvPolynomial (Root m) ℝ) :
    L (rename (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) Q) =
      (((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) : ℝ) * L Q := by
  let S : Submonoid (∀ τ, Equiv.Perm (Fin (m τ))) :=
    { carrier := {w | ∀ Q, L (rename (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) Q) =
        (((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) : ℝ) * L Q}
      one_mem' := by
        intro Q
        have : (fun x : Root m => (⟨x.1, (1 : ∀ τ, Equiv.Perm (Fin (m τ))) x.1 x.2⟩ : Root m)) = id := by
          funext x; rfl
        rw [this, rename_id]
        simp
      mul_mem' := by
        intro v w hv hw Q
        have : (fun x : Root m => (⟨x.1, (v * w) x.1 x.2⟩ : Root m)) =
            (fun x : Root m => (⟨x.1, v x.1 x.2⟩ : Root m)) ∘
              (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) := by
          funext x; rfl
        simp only [Set.mem_setOf_eq] at hv hw ⊢
        rw [this, ← rename_rename, hv, hw]
        simp only [Pi.mul_apply, map_mul, Finset.prod_mul_distrib, Units.val_mul, Int.cast_mul]
        ring }
  have hS : S = ⊤ := by
    have htop : (⊤ : Submonoid (∀ τ, Equiv.Perm (Fin (m τ)))) =
        Submonoid.pi Set.univ (fun τ => (⊤ : Submonoid (Equiv.Perm (Fin (m τ))))) := by
      ext x; simp [Submonoid.mem_pi]
    rw [eq_top_iff, htop, ← Submonoid.iSup_map_mulSingle, iSup_le_iff]
    intro τ
    rw [Submonoid.map_le_iff_le_comap]
    rw [perm_submonoid_eq_top_of_adj (m τ) (Submonoid.comap (MonoidHom.mulSingle (fun τ => Equiv.Perm (Fin (m τ))) τ) S) ?_]
    intro a b hab Q
    have hf : (fun x : Root m => (⟨x.1, (MonoidHom.mulSingle (fun τ => Equiv.Perm (Fin (m τ))) τ
        (Equiv.swap a b)) x.1 x.2⟩ : Root m)) = Equiv.swap (⟨τ, a⟩ : Root m) ⟨τ, b⟩ := by
      funext ⟨σ, c⟩
      by_cases h : σ = τ
      · subst h
        simp only [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same]
        rw [Equiv.swap_apply_def, Equiv.swap_apply_def]
        by_cases h1 : c = a
        · subst h1; simp
        · by_cases h2 : c = b
          · subst h2; simp [h1]
          · simp [h1, h2]
      · simp only [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne h, Equiv.Perm.coe_one, id]
        rw [Equiv.swap_apply_of_ne_of_ne]
        · intro e; exact h (congrArg Sigma.fst e)
        · intro e; exact h (congrArg Sigma.fst e)
    have hab' : a ≠ b := by
      intro e; subst e; omega
    have hs : (∏ σ, Equiv.Perm.sign ((MonoidHom.mulSingle (fun τ => Equiv.Perm (Fin (m τ))) τ
        (Equiv.swap a b)) σ)) = -1 := by
      have : ∀ σ, Equiv.Perm.sign ((MonoidHom.mulSingle (fun τ => Equiv.Perm (Fin (m τ))) τ
          (Equiv.swap a b)) σ) = (Pi.mulSingle τ (Equiv.Perm.sign (Equiv.swap a b)) : ι → ℤˣ) σ := by
        intro σ
        by_cases h : σ = τ
        · subst h; simp
        · simp [Pi.mulSingle_eq_of_ne h]
      simp only [this, Finset.prod_pi_mulSingle', Finset.mem_univ, if_true]
      exact Equiv.Perm.sign_swap hab'
    show L _ = _
    rw [hf, hs, hL τ a b hab Q]
    simp
  have hw : w ∈ S := by rw [hS]; trivial
  exact hw Q

end GlobalTheory.FlagPush
end

section

open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.TrueGeo GlobalTheory.Mean4O
open ReciprocityTheory.L2DbarEstimates (V)
open scoped Classical

open Filter Topology AlgebraicGeometry CategoryTheory
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.ChernWeilLine

theorem cInfAt_eventually {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
    {f : CxPts p σ → ℝ} {y : CxPts p σ} (h : CInfAt f y) : ∀ᶠ z in 𝓝 y, CInfAt f z := by
  obtain ⟨W, ι, i, g, F, O, h₁, h₂, h₃, h₄, h₅⟩ := h
  have hW := (isOpen_ptsIn (p := p) (σ := σ) W).mem_nhds h₁
  have hc : ContinuousAt (fun z a => ev p σ W (g a) z) y :=
    continuousAt_pi.2 fun a => (continuousOn_ev (g a)).continuousAt hW
  filter_upwards [hW, hc.preimage_mem_nhds (h₂.mem_nhds h₃), h₅.eventuallyEq_nhds] with z hz hzO hz5
  exact ⟨W, ι, i, g, F, O, hz, h₂, hzO, h₄, hz5⟩

theorem chernTop_congr {n : ℕ} {ι : Type} {m : ι → ℕ} (R : MvPolynomial (ι × ℕ) ℝ)
    {G G' : V n → Mat m ℂ} {v : V n} (h : G =ᶠ[𝓝 v] G') : chernTop R G v = chernTop R G' v := by
  have hc : ∀ x : ι × ℕ, chernPoly (fun u => G u x.1) v x.2 = chernPoly (fun u => G' u x.1) v x.2 := by
    intro x
    unfold chernPoly curvPoly
    simp only [curv_congr (h.mono fun u hu => congrFun hu x.1)]
  simp only [chernTop, hc]

end GlobalTheory.ChernWeilLine
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

set_option autoImplicit false

namespace GlobalTheory.FlagPush

theorem mul_diag_of_par {ι : Type} {m : ι → ℕ} {K : Type} [Field K] {O O' : Subring K} {S T : Mat m K}
    (hS : Par m O S) (hT : Par m O' T) (τ : ι) (i : Fin (m τ)) :
    (S * T) τ i i = S τ i i * T τ i i := by
  rw [Pi.mul_apply, Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun l _ hl => ?_) (fun h => absurd (Finset.mem_univ i) h)
  rcases lt_or_gt_of_ne hl with h | h
  · rw [(hT τ).2.2.2 l i l.isLt h, mul_zero]
  · rw [(hS τ).2.2.2 i l i.isLt h, zero_mul]

theorem diag_of_par : ∀ (ι : Type) (m : ι → ℕ) (K : Type) [Field K] (O : Subring K) (S : Mat m K), Par m O S →
    ∀ x : Root m, S x.1 x.2 x.2 ≠ 0 ∧ (S x.1 x.2 x.2)⁻¹ ∈ O ∧ S⁻¹ x.1 x.2 x.2 = (S x.1 x.2 x.2)⁻¹ ∧
      ∀ T : Mat m K, Par m ⊤ T → (S * T) x.1 x.2 x.2 = S x.1 x.2 x.2 * T x.1 x.2 x.2 := by
  intro ι m K _ O S hS x
  have hSi : Par m O S⁻¹ := hS.inv
  have h1 : S x.1 x.2 x.2 * S⁻¹ x.1 x.2 x.2 = 1 := by
    rw [← mul_diag_of_par hS hSi, Mat.mul_inv hS.det_ne]
    exact Matrix.one_apply_eq _
  have hne : S x.1 x.2 x.2 ≠ 0 := left_ne_zero_of_mul_eq_one h1
  have hinv : S⁻¹ x.1 x.2 x.2 = (S x.1 x.2 x.2)⁻¹ := eq_inv_of_mul_eq_one_right h1
  refine ⟨hne, ?_, hinv, fun T hT => mul_diag_of_par hS hT x.1 x.2⟩
  rw [← hinv]
  exact (hSi x.1).1 x.2 x.2

end GlobalTheory.FlagPush
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem poinWt_mem_Icc_and_pos : ∀ {n : ℕ} (S : Finset (Fin n)) (v : V n), (∀ a ∈ S, ‖v a‖ ≤ 1 / 2) →
    (∀ a, 0 ≤ poinWt S v a ∧ poinWt S v a ≤ 1) ∧ ((∀ a ∈ S, v a ≠ 0) → ∀ a, 0 < poinWt S v a) := by
  intro n S v hS
  refine ⟨fun a => ?_, fun hne a => ?_⟩
  · unfold poinWt
    split_ifs with ha
    · refine ⟨mul_nonneg (norm_nonneg _) (abs_nonneg _), ?_⟩
      rcases (norm_nonneg (v a)).eq_or_lt with h0 | hpos
      · rw [← h0]; simp
      · have h1 : ‖v a‖ ≤ 1 := (hS a ha).trans (by norm_num)
        have := Real.abs_log_mul_self_lt _ hpos h1
        rw [abs_mul, abs_of_pos hpos] at this
        linarith
    · exact ⟨zero_le_one, le_rfl⟩
  · unfold poinWt
    split_ifs with ha
    · have hpos : 0 < ‖v a‖ := norm_pos_iff.mpr (hne a ha)
      have hlt : ‖v a‖ < 1 := (hS a ha).trans_lt (by norm_num)
      have hlog : Real.log ‖v a‖ < 0 := Real.log_neg hpos hlt
      exact mul_pos hpos (abs_pos.mpr hlog.ne)
    · exact zero_lt_one

end GlobalTheory.GoodTop
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.ProjVar.Var

theorem interPoly_eq_zero_of_isHomogeneous (F : Type) [Field F] (Y : Var F) (κ : Type) (gr : κ → Y.Dv) (k : ℕ)
    (P : MvPolynomial κ ℝ) (hP : P.IsHomogeneous k) (hk : k ≠ Y.dim) : Y.interPoly gr P = 0 := by

  rw [P.as_sum, map_sum]
  refine Finset.sum_eq_zero fun d hd => ?_
  have hw : Finsupp.weight 1 d = k := hP (mem_support_iff.mp hd)
  have e : monomial d (AddMonoidAlgebra.coeff P d) = AddMonoidAlgebra.coeff P d • basisMonomials κ ℝ d := by
    rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [e, map_smul, interPoly, Module.Basis.constr_basis, dite_eq_right, smul_zero]
  rintro ⟨s, hs⟩
  apply hk

  rw [← hw, ← hs, map_sum]
  simp [Finsupp.weight_apply, Finsupp.sum_single_index]

end GlobalTheory.ProjVar.Var
end

section

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem contDiffAt_holoChart : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)}, IsHoloChart e → ∀ {f : CxPts X.str σ → ℝ} {y : CxPts X.str σ}, y ∈ e.source → CInfAt f y → ContDiffAt ℝ ∞ (fun v => f (e.symm v)) (e y) := by
  intro F _ σ X e he f y hy hf
  obtain ⟨W, ι, hι, g, Φ, O, hyW, hO, hgO, hΦ, hfeq⟩ := hf

  have hU : IsOpen (e.target ∩ e.symm ⁻¹' ptsIn X.str σ W) :=
    e.isOpen_inter_preimage_symm (GlobalTheory.CxPts.isOpen_ptsIn W)
  have hyU : e y ∈ e.target ∩ e.symm ⁻¹' ptsIn X.str σ W :=
    ⟨e.map_source hy, by rw [Set.mem_preimage, e.left_inv hy]; exact hyW⟩

  have hGc : ContDiffAt ℂ ∞ (fun v a => GlobalTheory.CxPts.ev X.str σ W (g a) (e.symm v)) (e y) := by
    rw [contDiffAt_pi]
    intro a
    exact (ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn _ _ _ hU (he W (g a))).contDiffAt
      (hU.mem_nhds hyU)

  have hΦc : ContDiffAt ℝ ∞ Φ (fun a => GlobalTheory.CxPts.ev X.str σ W (g a) (e.symm (e y))) := by
    rw [e.left_inv hy]
    exact hΦ.contDiffAt (hO.mem_nhds hgO)
  have hcomp : ContDiffAt ℝ ∞ (fun v => Φ fun a => GlobalTheory.CxPts.ev X.str σ W (g a) (e.symm v)) (e y) :=
    hΦc.comp (e y) (hGc.restrict_scalars ℝ)
  refine hcomp.congr_of_eventuallyEq ?_

  have ht : Filter.Tendsto e.symm (𝓝 (e y)) (𝓝 y) := by
    have h := e.continuousAt_symm (e.map_source hy)
    rw [ContinuousAt, e.left_inv hy] at h
    exact h
  exact ht.eventually hfeq

end GlobalTheory.GoodTop
end
end

section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.NefShift

theorem isNef_shift_mono : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (M : HermLB p) (t t' : ℝ), t ≤ t' →
    (M.shift (fun _ => t) fun _ => rfl).IsNef D → (M.shift (fun _ => t') fun _ => rfl).IsNef D := by
  intro _ k _ X _ p D hX M t t' htt h
  refine ⟨fun σ => ?_, h.vertical, ?_⟩
  · have := (h.semiPos σ).addFn_const (2 * (t' - t))
    have e : (((M.shift (fun _ => t) fun _ => rfl).φ σ).addFn fun _ => 2 * (t' - t)) =
        (M.shift (fun _ => t') fun _ => rfl).φ σ := by
      simp only [HermLB.shift, Weight.addFn]
      congr 1
      funext a b
      ring
    exact e ▸ this
  · intro Z i _ _ _ hc hd
    obtain ⟨r, hr, h0⟩ := h.horizontal Z i hc hd
    refine ⟨r, hr, ?_⟩
    have e₁ := HtSelfInter.curveDeg_shift hX M t i hc hd (r := r) hr
    have e₂ := HtSelfInter.curveDeg_shift hX M t' i hc hd (r := r) hr
    rw [e₂]
    rw [e₁] at h0
    nlinarith [(Nat.cast_nonneg _ : (0:ℝ) ≤ Nat.card (X.residueField (i (genericPoint Z)) →+* ℂ))]

end GlobalTheory.NefShift
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PoincareDescent

theorem descend_torsor : ∀ (K : Type) [Field K] [IsAlgClosed K] (A A' B N : Over (Sp K)) [GrpObj A] [GrpObj A'] [GrpObj B] [GrpObj N] (P : LB (A ⊗ B).left) (i : N ⟶ A) (q : A ⟶ A'), IsAbelianScheme A → IsAbelianScheme A' → IsAbelianScheme B → P.IsLB → IsAdditive P → Triv (ev P (𝟙 A) (1 : A ⟶ B)) → IsMonHom i → IsMonHom q → IsFinite q.left → Flat q.left → Surjective q.left → IsPullback (fst A N) (fst A N * (snd A N ≫ i)) q q → Triv (ev P (fst N B ≫ i) (snd N B)) → ∃ P₀ : LB (A' ⊗ B).left, P₀.IsLB ∧ LBIso (ev P₀ (fst A B ≫ q) (snd A B)) P := by
  intro K _ _ A A' B N _ _ _ _ P i q hA hA' hB hP hadd hzero hi hq hfin hflat hsurj hsq hN
  haveI : IsFinite q.left := hfin
  haveI : Flat q.left := hflat
  haveI : Surjective q.left := hsurj
  have hpb := GlobalTheory.AbLaw.SecBC.isPullback_whisker (A := B) q
  haveI : IsFinite (q ▷ B).left := MorphismProperty.of_isPullback hpb.flip hfin
  haveI : Flat (q ▷ B).left := MorphismProperty.of_isPullback hpb.flip hflat
  haveI : Surjective (q ▷ B).left := MorphismProperty.of_isPullback hpb.flip hsurj
  haveI : IsLocallyNoetherian (A' ⊗ B).left := by
    haveI := hA'.smooth
    haveI := hB.smooth
    haveI : LocallyOfFiniteType (A' ⊗ B).hom := by
      show LocallyOfFiniteType (pullback.fst A'.hom B.hom ≫ A'.hom)
      infer_instance
    exact LocallyOfFiniteType.isLocallyNoetherian (A' ⊗ B).hom
  have hker : ∀ (T : Over (Sp K)) (x : T ⟶ A), x ≫ q = 1 → Triv (ev P (fst T B ≫ x) (snd T B)) := by
    intro T x hx
    have e : (1 : T ⟶ A) ≫ q = x ≫ q := by rw [hx, MonObj.one_comp]
    have hx' : x = (hsq.lift 1 x e ≫ snd A N) ≫ i := by
      have h2 := hsq.lift_snd 1 x e
      rw [MonObj.comp_mul, hsq.lift_fst, _root_.one_mul, ← Category.assoc] at h2
      exact h2.symm
    obtain ⟨n, rfl⟩ : ∃ n : T ⟶ N, x = n ≫ i := ⟨_, hx'⟩
    rw [triv_ev_iff hP]
    have z := congrArg (CechPic.pull (lift (fst T B ≫ n) (snd T B)).left) ((triv_ev_iff hP _ _).1 hN)
    rw [pull_evc, map_zero, lift_fst_assoc, lift_snd, Category.assoc] at z
    exact z
  obtain ⟨φ, hc, hco⟩ := GlobalTheory.T.exists_descentDatum_additive_lineBundle_isogeny K A A' B q P hA hA' hB hq hfin hflat hsurj hP hadd hzero hker
  obtain ⟨P₀, hP₀, hiso⟩ := GlobalTheory.T.exists_lineBundle_descent_finiteFlat _ _ (q ▷ B).left P hP φ hc hco
  refine ⟨P₀, hP₀, (cls_eq_iff (pull_isLB hP₀ _) hP).1 ?_⟩
  refine Eq.trans ?_ ((cls_eq_iff hP (pull_isLB hP₀ _)).2 hiso).symm
  rw [cls_ev hP₀, evc, cls_pull hP₀, ← lift_whiskerRight, lift_fst_snd, Category.id_comp]

end GlobalTheory.PoincareDescent
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem divOver_ord_zpow {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    (E : DivOver p) (f : X.functionFieldˣ) (r : ℤ) : E.ord (f ^ r) = r * E.ord f := by
  rcases Int.eq_nat_or_neg r with ⟨s, rfl | rfl⟩
  · rw [zpow_natCast, E.ord_pow]
  · rw [zpow_neg, zpow_natCast, E.ord_inv, E.ord_pow]
    ring

theorem isLogEqn_add_smul : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), ∀ (Γ D : X → ℚ) (η : RatForms p n) (x : X) (m m' : ℕ) (g f : X.functionFieldˣ) (c : ℚ), 0 < m → 0 < m' → IsLogEqn p Γ η x m g → (∀ z, z ⤳ x → ∀ E : DivOver p, E.IsAt z → D z = (E.ord f : ℚ) / m') → ∃ (m'' : ℕ) (g'' : X.functionFieldˣ), 0 < m'' ∧ IsLogEqn p (Γ + c • D) η x m'' g'' ∧ ∀ E : DivOver p, discrep E η m'' g'' = discrep E η m g - c * ((E.ord f : ℚ) / m') := by
  intro X _ _ p n Γ D η x m m' g f c hm hm' hg hD
  have hb : 0 < c.den := c.den_pos
  have hc : c * (c.den : ℚ) = c.num := Rat.mul_den_eq_num c
  have h₁ : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have h₂ : (m' : ℚ) ≠ 0 := by exact_mod_cast hm'.ne'
  have h₃ : (c.den : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  refine ⟨m * m' * c.den, g ^ (m' * c.den) * f ^ (c.num * m), Nat.mul_pos (Nat.mul_pos hm hm') hb,
    fun z hz E hE => ?_, fun E => ?_⟩
  · have e₁ := hg z hz E hE
    have e₂ := hD z hz E hE
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [E.ord_mul, E.ord_pow, divOver_ord_zpow, e₂]
    push_cast
    rw [← e₁]
    field_simp
    linear_combination (E.ord f : ℚ) * hc
  · simp only [discrep]
    rw [E.ord_mul, E.ord_pow, divOver_ord_zpow]
    push_cast
    field_simp
    linear_combination ((m : ℚ) * (E.ord f : ℚ)) * hc

end GlobalTheory.PairStep
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory

theorem isLogCanonicalMultiple_add_qWeil : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), ∀ (Δ : X → ℚ) (m m' : ℕ) (G D₀ : CartierDiv X), 0 < m → 0 < m' → IsLogCanonicalMultiple p n Δ m G → IsLogCanonicalMultiple p n (Δ + qWeil D₀ m') (m * m') (m' • G + m • D₀) := by
  intro X _ _ p n Δ m m' G D₀ hm hm' hG
  obtain ⟨η, hη, hG⟩ := hG
  refine ⟨η, hη, fun x g hg z hz E hE => ?_⟩
  obtain ⟨V, hV, hgV⟩ := hg.exists_nhds
  obtain ⟨a, ha⟩ := G.exists_isEqn z
  obtain ⟨d, hd⟩ := D₀.exists_isEqn z
  have h3 := ((hgV z (hz.mem_open V.isOpen hV)).mult_eq.symm.trans
    ((ha.nsmul m').add (hd.nsmul m)).mult_eq)
  rw [← hE.ord_eq, ← hE.ord_eq, E.ord_mul, E.ord_pow, E.ord_pow] at h3
  have h4 := hG z a ha z specializes_rfl E hE
  have hd' := hd.mult_eq
  rw [← hE.ord_eq] at hd'
  have h1 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have h2 : (m' : ℚ) ≠ 0 := by exact_mod_cast hm'.ne'
  rw [Pi.add_apply, qWeil, hd', h3]
  push_cast
  rw [← h4]
  field_simp
  ring

end GlobalTheory
end
