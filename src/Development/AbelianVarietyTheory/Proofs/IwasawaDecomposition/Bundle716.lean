module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle682
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle631
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle102
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle109
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle672
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricUniformisationSmoothOnInterior
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle638
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle433
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle220
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle700
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle703
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle699
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle667
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle630
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle685
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle032
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle691
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle456
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle450
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle496
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.TotallySplit
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle005
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle206
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ArcQ GlobalTheory.FrameNormLie GlobalTheory.HodgeSmooth
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.HodgeInteriorGram

theorem isDerivAt0_comp_equiv {g g' : ℕ} {X : Scheme.{0}} (L : (Fin g' → ℂ) ≃L[ℂ] (Fin g → ℂ))
    (y : (Fin g → ℂ) → (Sp ℂ ⟶ X)) (w : Fin g' → ℂ) (v : Sp (DualNumber ℂ) ⟶ X) :
    IsDerivAt0 (fun z => y (L z)) w v ↔ IsDerivAt0 y (L w) v := by
  unfold IsDerivAt0
  simp only [map_zero]
  refine and_congr Iff.rfl (forall_congr' fun U => forall_congr' fun h => forall_congr' fun f => ?_)
  rw [show (fun z => valAt' (y (L z)) U f) = (fun z => valAt' (y z) U f) ∘ L from rfl, L.comp_right_fderiv,
    map_zero]
  rfl

theorem int_eq_of_exp_eq (m n : ℤ) (h : ∀ k : ℕ, 0 < k →
    Complex.exp (-(2 * Real.pi * Complex.I) * (m : ℂ) / k) = Complex.exp (-(2 * Real.pi * Complex.I) * (n : ℂ) / k)) :
    m = n := by
  have hI : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have key : ∀ K : ℕ, 0 < K → (K : ℤ) ∣ n - m := by
    intro K hK
    obtain ⟨N, hN⟩ := Complex.exp_eq_exp_iff_exists_int.1 (h K hK)
    have hkC : (K : ℂ) ≠ 0 := by exact_mod_cast hK.ne'
    have e : ((n - m : ℤ) : ℂ) = ((K * N : ℤ) : ℂ) := by
      push_cast
      linear_combination (norm := skip) ((K : ℂ) / (2 * Real.pi * Complex.I)) * hN
      field_simp
      ring
    exact ⟨N, by exact_mod_cast e⟩
  have hz : n - m = 0 := by
    refine Int.eq_zero_of_abs_lt_dvd (key ((n - m).natAbs + 1) (Nat.succ_pos _)) ?_
    rw [Int.abs_eq_natAbs]
    push_cast
    omega
  omega

theorem hermForm_pull' {g g' : ℕ} (M : Matrix (Fin g') (Fin g) ℂ) (Hm : Matrix (Fin g') (Fin g') ℂ)
    (z w : Fin g → ℂ) : hermForm (Mᵀ * Hm * Mᵀᴴ) z w = hermForm Hm (M *ᵥ z) (M *ᵥ w) := by
  have : Mᵀᴴ *ᵥ (star w) = star (M *ᵥ w) := by
    rw [Matrix.star_mulVec, ← Matrix.mulVec_transpose]
    rfl
  rw [hermForm, hermForm, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, this, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

end GlobalTheory.HodgeInteriorGram

theorem GlobalTheory.HodgeInteriorGram.gram_eq_riem : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (W : UnfWit (unfFam U σ)), Function.Injective W.ik → ∀ (d : (unfFam U σ).Comp → (E →+* ℂ) → ℝ), (∀ (k : (unfFam U σ).Comp) (x : ((unfFam U σ).X k).dom), IsOrth ((unfFam U σ).X k) x.1 → ∀ τ : E →+* ℂ, 0 < Dw.mult τ → 0 < d k τ) → (∀ (k : (unfFam U σ).Comp) (x : ((unfFam U σ).X k).dom), IsOrth ((unfFam U σ).X k) x.1 → ∀ (i : Fin W.F.n) (P : (W.F.Di i).La →+ (Fin W.g → ℂ)), IsPeriod (W.F.Di i) (fun j => Formalism.L2.PjFree.relab c σ (W.e j).1) P → ∀ (Hm : Matrix (Fin W.g) (Fin W.g) ℂ), (∀ v w, (hermForm Hm (P v) (P w)).im = (W.F.Di i).EF v w) → W.F.u i P = ((unfFam U σ).un k x).x → ∀ (τ τ' : E →+* ℂ) (zz : Fin (Dw.mult τ) → (Fin W.g → ℂ)) (zz' : Fin (Dw.mult τ') → (Fin W.g → ℂ)) (uu : Fin (Dw.mult τ) → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)) (uu' : Fin (Dw.mult τ') → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)) (T : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ) (T' : Matrix (Fin (Dw.mult τ')) (Fin (Dw.mult τ')) ℂ), (∀ b, IsDerivAt0 (fun w => (W.F.ex i P w).left) (zz b) (uu b)) → (∀ b, IsDerivAt0 (fun w => (W.F.ex i P w).left) (zz' b) (uu' b)) → (∀ b, IsCombAt ((unfFam U σ).un k x).x (((unfFam U σ).un k x).u τ) (show Fin (Dw.mult τ) → CAt σ from fun b' => T b' b) (uu b)) → (∀ b, IsCombAt ((unfFam U σ).un k x).x (((unfFam U σ).un k x).u τ') (show Fin (Dw.mult τ') → CAt σ from fun b' => T' b' b) (uu' b)) → (of fun b b' => hermForm Hm (zz b') (zz b)) = ((d k τ : ℝ) : ℂ) • (Tᴴ * T) ∧ (τ' ≠ τ → ∀ b b', hermForm Hm (zz' b') (zz b) = 0)) → ∀ (g : ℕ) (x : GlobalTheory.CxPts (genStr Z) σ) (exx : (Fin g → ℂ) → (Over.mk (x.1 ≫ genι Z) ⟶ Z.t.G)), Inner x → IsExpAt Z.t (x.1 ≫ genι Z) exx → IsHolTo Set.univ (fun w => (exx w).left) → ∀ (k : (unfFam U σ).Comp) (x' : ((unfFam U σ).X k).dom), IsOrth ((unfFam U σ).X k) x'.1 → cxPt Z ((unfFam U σ).un k x') = x → ∀ (Hm : Matrix (Fin g) (Fin g) ℂ), (∀ v w : Fin g → ℂ, exx v = 1 → exx w = 1 → ∃ m : ℤ, (hermForm Hm v w).im = m) → (∀ (k : ℕ) (v w : Fin g → ℂ) (ζ : ℂˣ), 0 < k → exx v = 1 → exx w = 1 → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm Hm v w).im : ℂ) / k) → GlobalTheory.UU.CubWeil Z.t.cub k (exx ((k : ℂ)⁻¹ • v)) (exx ((k : ℂ)⁻¹ • w)) (unitOn ζ)) → ∀ (f : EigFrame Z σ (x.1 ≫ genι Z)) (Wd : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) → Fin g → ℂ), Dirs ⟨x, f⟩ (fun w => (exx w).left) Wd → (∀ τ, (hodgeMet Z U).gram x f τ = (((2 * Real.pi / d k τ : ℝ)) : ℂ) • Matrix.of fun b b' => hermForm Hm (Wd ⟨τ, b'⟩) (Wd ⟨τ, b⟩)) ∧ ∀ p q : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), p.1 ≠ q.1 → hermForm Hm (Wd p) (Wd q) = 0 := by
  classical
  intro E _ _ _ H Dw l Xo c O _ β Z σ U hσ hU W hinj d hdpos hd g x exx hin hex hhol k x' hx' hkx Hm hint hweil f Wd hdirs
  have hexf : ∃ g₀, IsHodgeFrame (unfFam U) x g₀ := by
    rw [← hkx]; exact ⟨_, isHodgeFrame_cxFrame (U := unfFam U) hσ hx'⟩
  have hg : ∀ τ, (hodgeMet Z U).gram x f τ =
      ((2 * Real.pi : ℝ) : ℂ) • ((hexf.choose.co f τ)ᴴ * hexf.choose.co f τ) := fun τ => dif_pos hexf
  obtain ⟨k'', x'', hx'', hkx'', hv⟩ := GlobalTheory.HodgeSmooth.hodgeFrame_comp hσ hexf.choose_spec
  have hk : k'' = k := by
    apply hinj
    have e := x_eq_of_cxPt (congrArg Subtype.val (hkx''.trans hkx.symm))
    exact W.F.disj _ _ _ _ (W.period k'' x'') (W.period k x')
      ((W.lie k'' x'').1.symm.trans (e.trans (W.lie k x').1))
  subst hk
  have hu : W.F.u (W.ik k'') (W.Pm k'' x'') =
      (GlobalTheory.AllWt.ptF (S := CAt σ) ((unfFam U σ).un k'' x'') : Sp ℂ ⟶ Xo.XF c) ≫
        pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) :=
    (W.lie k'' x'').1.symm.trans (ptF_fst _).symm
  have hp : (GlobalTheory.AllWt.ptF (S := CAt σ) ((unfFam U σ).un k'' x'') : Sp ℂ ⟶ Xo.XF c) ≫ Z.jQ ≫
      pullback.fst Z.s (spMap β) = x.1 ≫ genι Z := by
    rw [← hkx'']
    exact (Category.assoc _ _ _).symm
  have hper := W.period k'' x''
  have he' := isExpAt_pushEx E H Dw l Xo c O β Z W.g _ _ W.F _ _ _ _ hu hp hper
  have hhol' := pushEx_hol E H Dw l Xo c O β Z W.g _ _ W.F _ _ _ _ hu hp hper
  have hker := pushEx_eq_one_iff E H Dw l Xo c O β Z W.g _ _ W.F _ _ _ _ hu hp hper
  have hcw := pushEx_cubWeil E H Dw l Xo c O β Z W.g _ _ W.F _ _ _ _ hu hp hper
  obtain ⟨L, hL⟩ := exp_eq_comp_linearEquiv E H Z.X Z.t (x.1 ≫ genι Z) g W.g exx _ hex hhol he' hhol'
  set A : Matrix (Fin g) (Fin W.g) ℂ := LinearMap.toMatrix' L.toLinearMap with hA
  have hAv : ∀ z, A *ᵥ z = L z := fun z => LinearMap.toMatrix'_mulVec _ z
  set Hm' : Matrix (Fin W.g) (Fin W.g) ℂ := Aᵀ * Hm * Aᵀᴴ with hHm'
  have hpull : ∀ z w, hermForm Hm' z w = hermForm Hm (L z) (L w) := fun z w => by
    rw [hHm', GlobalTheory.HodgeInteriorGram.hermForm_pull', hAv, hAv]
  have hIm : ∀ a b, (hermForm Hm' (W.Pm k'' x'' a) (W.Pm k'' x'' b)).im = (W.F.Di (W.ik k'')).EF a b := by
    intro a b
    rw [hpull]
    have h1 : exx (L (W.Pm k'' x'' a)) = 1 := by rw [← hL]; exact (hker _).2 ⟨a, rfl⟩
    have h2 : exx (L (W.Pm k'' x'' b)) = 1 := by rw [← hL]; exact (hker _).2 ⟨b, rfl⟩
    obtain ⟨m, hm⟩ := hint _ _ h1 h2
    rw [hm]
    congr 1
    refine GlobalTheory.HodgeInteriorGram.int_eq_of_exp_eq _ _ fun K hK => ?_
    have w1 := hweil K _ _ (Units.mk0 _ (Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) * (m : ℂ) / K))) hK h1 h2
      (by rw [hm, Complex.ofReal_intCast]; rfl)
    have w2 := hcw K a b (Units.mk0 _ (Complex.exp_ne_zero
      (-(2 * Real.pi * Complex.I) * ((W.F.Di (W.ik k'')).EF a b : ℂ) / K))) hK rfl
    rw [hL, hL, L.map_smul, L.map_smul] at w2
    exact congrArg Units.val (ReciprocityTheory.ChartRestriction.G.H1.unitOn_injective (w1.unique w2))
  set Lc := L.toContinuousLinearEquiv with hLc
  have hLc' : ∀ z, Lc z = L z := fun z => rfl
  choose w hwt hwm hwc using fun (τ : E →+* ℂ) (b : Fin (Dw.mult τ)) =>
    GlobalTheory.HodgeSmooth.exists_lift_comb ((unfFam U σ).un k'' x'') hkx'' hexf.choose f hv τ b
  have hder : ∀ τ (b : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (W.F.ex (W.ik k'') (W.Pm k'' x'') z).left)
      (Lc.symm (Wd ⟨τ, b⟩)) (w τ b ≫ Z.m0.toSABMap.φ) := by
    intro τ b
    refine isDerivAt0_ex_of_push Z W.F _ _ _ hper hu (hwt τ b).1 ?_
    rw [hwm τ b]
    have e1 : (fun z => liftEx Z W.F _ (W.ik k'') (W.Pm k'' x'') hu z ≫ Z.m.φ) =
        fun z => (exx (Lc z)).left := funext fun z => by
      rw [hLc', ← hL]
      rfl
    rw [e1]
    refine (GlobalTheory.HodgeInteriorGram.isDerivAt0_comp_equiv Lc (fun v => (exx v).left) _ _).2 ?_
    rw [Lc.apply_symm_apply]
    exact hdirs ⟨τ, b⟩
  have hmat := fun τ τ' => hd k'' x'' hx'' (W.ik k'') (W.Pm k'' x'') hper Hm' hIm (W.lie k'' x'').1.symm τ τ'
    (fun b => Lc.symm (Wd ⟨τ, b⟩)) (fun b => Lc.symm (Wd ⟨τ', b⟩)) (fun b => w τ b ≫ Z.m0.toSABMap.φ)
    (fun b => w τ' b ≫ Z.m0.toSABMap.φ) (hexf.choose.co f τ) (hexf.choose.co f τ') (hder τ) (hder τ') (hwc τ) (hwc τ')
  refine ⟨fun τ => ?_, fun p q hpq => ?_⟩
  · obtain ⟨h1, -⟩ := hmat τ τ
    rw [hg τ]
    have e2 : (of fun b b' : Fin (Dw.mult τ) => hermForm Hm (Wd ⟨τ, b'⟩) (Wd ⟨τ, b⟩)) =
        of fun b b' => hermForm Hm' (Lc.symm (Wd ⟨τ, b'⟩)) (Lc.symm (Wd ⟨τ, b⟩)) := by
      ext b b'
      simp only [of_apply, hpull, ← hLc', Lc.apply_symm_apply]
    rw [e2, h1]
    rcases Nat.eq_zero_or_pos (Dw.mult τ) with h0 | h0
    · ext b
      exact absurd b.2 (by omega)
    · have hdp := hdpos k'' x'' hx'' τ h0
      rw [smul_smul, ← Complex.ofReal_mul]
      congr 2
      field_simp
  · have h2 := (hmat q.1 p.1).2 hpq q.2 p.2
    rw [hpull, ← hLc', ← hLc', Lc.apply_symm_apply, Lc.apply_symm_apply] at h2
    exact h2
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx


theorem _root_.GlobalTheory.T.flagSpaceComponent_base_dim_eq_cmType_card_mul_pq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p)) = X.dim := by
  first | exact @GlobalTheory.BaseDim.card_eq_dim | exact GlobalTheory.BaseDim.card_eq_dim | (intros; apply GlobalTheory.BaseDim.card_eq_dim <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix


theorem _root_.GlobalTheory.T.algebraicChart_lift_holomorphic_periodMaps : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (X : Var F) (j : X.X ⟶ gen T.Z) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsOpenImmersion j → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∃ (i : Fin Fu.n) (B : Set (ReciprocityTheory.L2DbarEstimates.V X.dim)) (P : ReciprocityTheory.L2DbarEstimates.V X.dim → ((Fu.Di i).La →+ (Fin g → ℂ))), IsOpen B ∧ c'.e y ∈ B ∧ B ⊆ c'.e.target ∧ (∀ b ∈ B, IsPeriod (Fu.Di i) ty (P b)) ∧ (∀ x, DifferentiableOn ℂ (fun b => P b x) B) ∧ ∀ b ∈ B, ∃ q : FrPt Xo c (Formalism.L2.Pj.CAt σ), cxPt T.Z q = cxOf e σ hj (c'.e.symm b) ∧ Fu.u i (P b) = q.x := by
  first | exact @GlobalTheory.ShFam.chart_lift_periods_of_openPart | exact GlobalTheory.ShFam.chart_lift_periods_of_openPart | (intros; apply GlobalTheory.ShFam.chart_lift_periods_of_openPart <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix


theorem _root_.GlobalTheory.T.flagComponent_dim_and_base_dim : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → (Φ.C k).Y.dim = Fintype.card (GlobalTheory.AllWt.Psi H) * ((Dw.p + Dw.q) * (Dw.p + Dw.q - 1) / 2) ∧ X.dim = Fintype.card (GlobalTheory.AllWt.Psi H) * (Dw.p * Dw.q) := by
  first | exact @GlobalTheory.FlagBaseDim.dims | exact GlobalTheory.FlagBaseDim.dims | (intros; apply GlobalTheory.FlagBaseDim.dims <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open scoped ComplexOrder Topology
open ReciprocityTheory.L2DbarEstimates (V)
open ReciprocityTheory.ChartRestriction.G.FD (Frame mat)


theorem _root_.GlobalTheory.T.dim_openly_immersed_variety_eq_cmType_card_mul_pq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (X : Var F) (j : X.X ⟶ gen T.Z), IsOpenImmersion j → ∀ (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), (∃ y, y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j)) → ∀ k : U.Comp, X.dim = (U.X k).Ψ.card * (Dw.p * Dw.q) := by
  first | exact @GlobalTheory.OpenBaseDim.dim_eq | exact GlobalTheory.OpenBaseDim.dim_eq | (intros; apply GlobalTheory.OpenBaseDim.dim_eq <;> assumption)
end

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolCell

namespace GlobalTheory.PolFan

section Depth

variable {O : Type} [CommRing O] (bar : O → O) (ψ w : InvFun O)

def IsStarDepth {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) (t : ℝ) : Prop :=
  0 ≤ t ∧ ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (v : LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧
    v ∈ balForms bar X ∧ (∀ y, 0 ≤ v y y) ∧ w.evalZ v = 1 ∧ InRCone γ v ∧ B ∈ rcone γ ∧ B - t • toReal v ∈ rcone γ

def depthSet (n : ℕ) (B : (Fin n → O) → (Fin n → O) → ℝ) : Set ℝ :=
  {t | ∃ (X₁ : Type) (_ : AddCommGroup X₁) (_ : Module O X₁) (_ : Module.Finite O X₁) (r : (Fin n → O) →ₗ[O] X₁)
    (B₁ : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ), Function.Surjective r ∧ (∀ x, (∀ y, B₁ x y = 0) → x = 0) ∧
    (∀ a b, B a b = B₁ (r a) (r b)) ∧ IsStarDepth bar ψ w B₁ t}

variable {bar ψ w}

theorem depthSet_comp {n m : ℕ} {r : (Fin n → O) →ₗ[O] (Fin m → O)} (hr : Function.Surjective r)
    (B : (Fin m → O) → (Fin m → O) → ℝ) : depthSet bar ψ w n (fun a b => B (r a) (r b)) = depthSet bar ψ w m B := by
  ext t
  constructor
  · rintro ⟨X₁, i1, i2, i3, ρ, B₁, hρ, hrad, hB, hd⟩
    have hker : LinearMap.ker r ≤ LinearMap.ker ρ := by
      intro x hx
      rw [LinearMap.mem_ker] at hx ⊢
      refine hrad _ fun y => ?_
      obtain ⟨y', rfl⟩ := hρ y
      have h1 := hB x y'
      have h2 := hB 0 y'
      simp only [hx, map_zero, LinearMap.zero_apply] at h1 h2
      rw [← h1, h2]
    let ρ' : (Fin m → O) →ₗ[O] X₁ :=
      (LinearMap.ker r).liftQ ρ hker ∘ₗ (r.quotKerEquivOfSurjective hr).symm.toLinearMap
    have hρ' : ∀ a, ρ' (r a) = ρ a := fun a => by
      have : (r.quotKerEquivOfSurjective hr).symm (r a) = Submodule.Quotient.mk a := by
        rw [LinearEquiv.symm_apply_eq]; rfl
      simp only [ρ', LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply]
    refine ⟨X₁, i1, i2, i3, ρ', B₁, fun x => ?_, hrad, fun a b => ?_, hd⟩
    · obtain ⟨a, rfl⟩ := hρ x
      exact ⟨r a, hρ' a⟩
    · obtain ⟨a, rfl⟩ := hr a
      obtain ⟨b, rfl⟩ := hr b
      rw [hρ', hρ']
      exact hB a b
  · rintro ⟨X₁, i1, i2, i3, ρ, B₁, hρ, hrad, hB, hd⟩
    exact ⟨X₁, i1, i2, i3, ρ ∘ₗ r, B₁, hρ.comp hr, hrad, fun a b => hB (r a) (r b), hd⟩

theorem depthSet_zero (B : (Fin 0 → O) → (Fin 0 → O) → ℝ) : depthSet bar ψ w 0 B = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun t ⟨X₁, i1, i2, i3, ρ, B₁, hρ, _, _, _, _, _, v, _, _, _, hv, _⟩ => ?_
  haveI : Subsingleton X₁ := ⟨fun x y => by
    obtain ⟨a, rfl⟩ := hρ x
    obtain ⟨b, rfl⟩ := hρ y
    rw [Subsingleton.elim a b]⟩
  rw [InvFun.evalZ, w.eval_of_subsingleton] at hv
  exact zero_ne_one hv

variable (bar ψ w)

def starDepth : InvFun O where
  toFun n B := sSup (depthSet bar ψ w n B)
  inv n m r hr B := by rw [depthSet_comp hr]
  zero B := by rw [depthSet_zero, Real.sSup_empty]

def starFun (K D : ℕ) : InvFun O where
  toFun n B := D * (K * ψ.toFun n B + (starDepth bar ψ w).toFun n B)
  inv n m r hr B := by simp only [InvFun.inv _ _ _ r hr]
  zero B := by simp only [InvFun.zero, mul_zero, add_zero]

variable {bar ψ w}

theorem starDepth_toFun_nonneg (n : ℕ) (B : (Fin n → O) → (Fin n → O) → ℝ) : 0 ≤ (starDepth bar ψ w).toFun n B :=
  Real.sSup_nonneg fun _ h => h.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.2.2.1

theorem starDepth_eval_nonneg {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] (B : X → X → ℝ) :
    0 ≤ (starDepth bar ψ w).eval X B := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' O X
  rw [InvFun.eval_eq _ hr]
  exact starDepth_toFun_nonneg n _

theorem starFun_eval {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] (K D : ℕ) (B : X → X → ℝ) :
    (starFun bar ψ w K D).eval X B = D * (K * ψ.eval X B + (starDepth bar ψ w).eval X B) := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' O X
  rw [InvFun.eval_eq _ hr, InvFun.eval_eq _ hr, InvFun.eval_eq _ hr]
  rfl

theorem starFun_evalZ {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] (K D : ℕ)
    (β : LinearMap.BilinForm ℤ X) :
    (starFun bar ψ w K D).evalZ β = D * (K * ψ.evalZ β + (starDepth bar ψ w).evalZ β) :=
  starFun_eval K D _

theorem starFun_evalR {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] (K D : ℕ)
    (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) :
    evalR (starFun bar ψ w K D) B = D * (K * evalR ψ B + evalR (starDepth bar ψ w) B) :=
  starFun_eval K D _

theorem starDepth_zeroFun (n : ℕ) (B : (Fin n → O) → (Fin n → O) → ℝ) : (starDepth bar ψ (zeroFun O)).toFun n B = 0 := by
  have : depthSet bar ψ (zeroFun O) n B = ∅ :=
    Set.eq_empty_of_forall_notMem fun t ⟨X₁, i1, i2, i3, ρ, B₁, _, _, _, _, _, _, v, _, _, _, hv, _⟩ => by
      rw [zeroFun_evalZ] at hv
      exact zero_ne_one hv
  show sSup _ = 0
  rw [this, Real.sSup_empty]

end Depth

section Twist

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E)

theorem isTwInv_starFun {ψ w : InvFun (𝓞 E)} (hψ : IsTwInv H ψ) (hd : IsTwInv H (starDepth H.bar ψ w)) (K D : ℕ) :
    IsTwInv H (starFun H.bar ψ w K D) := fun σ hσ n B => by
  show _ * (_ * _ + _) = _ * (_ * _ + _)
  rw [hψ σ hσ n B, hd σ hσ n B]

end Twist

end GlobalTheory.PolFan
end
end

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem genRank_le_sq (E : Type) [Field E] [NumberField E] (q : ℕ) (X : Type) [AddCommGroup X] [Module (𝓞 E) X]
    [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X] (hX : Module.finrank (𝓞 E) X ≤ q) {m : ℕ}
    (γ : Fin m → LinearMap.BilinForm ℤ X) : genRank γ ≤ (q * Module.finrank ℚ E) ^ 2 := by
  have : Module.Finite ℤ X := Module.Finite.trans (𝓞 E) X
  have : Module.Free ℤ X := free_int_of_projective E
  have h1 : genRank γ ≤ Module.finrank ℤ (LinearMap.BilinForm ℤ X) :=
    Submodule.finrank_le _
  have h2 : Module.finrank ℤ (LinearMap.BilinForm ℤ X) = Module.finrank ℤ X * Module.finrank ℤ X := by
    unfold LinearMap.BilinForm
    rw [Module.finrank_linearMap, Module.finrank_linearMap_self]
  have h3 : Module.finrank ℤ X ≤ q * Module.finrank ℚ E := by
    rw [finrank_int_eq_finrank_mul E X, mul_comm]
    exact Nat.mul_le_mul_right _ hX
  calc genRank γ ≤ Module.finrank ℤ X * Module.finrank ℤ X := h2 ▸ h1
    _ ≤ (q * Module.finrank ℚ E) * (q * Module.finrank ℚ E) := Nat.mul_le_mul h3 h3
    _ = (q * Module.finrank ℚ E) ^ 2 := (sq _).symm

theorem carrierDim_bounded : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ)
    (ψ lab : InvFun (𝓞 E)), IsCarrierDim H.bar q ψ lab → ∃ N : ℕ, ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X]
    [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q →
    ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → lab.evalZ β ≤ N := by
  intro E _ _ _ H q ψ lab hlab
  refine ⟨(q * Module.finrank ℚ E) ^ 2, fun X _ _ _ _ hX β hβ hpos => ?_⟩
  rw [hlab X hX β hβ hpos]
  exact_mod_cast (by
    rcases Set.eq_empty_or_nonempty {k : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ ∧
        InRCone γ β ∧ genRank γ = k} with he | hne
    · rw [he, Nat.sInf_empty]; exact Nat.zero_le _
    · obtain ⟨m, γ, -, -, hk⟩ := Nat.sInf_mem hne
      rw [← hk]; exact genRank_le_sq E q X hX γ :
    sInf {k : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ ∧ InRCone γ β ∧ genRank γ = k} ≤
      (q * Module.finrank ℚ E) ^ 2)

end GlobalTheory.PolFan
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl.MemberEx2

theorem step_start (h2b : StandardLattice.SiegelMassRatioCM) :
    Step KPx (fun _ B _ T => T = TwDat.untw B T.pl) (fun K B f T => ∃ w : ColW B f T, Start K B f T w) :=
  (Step.and (Step.of_all fun _ _ _ _ _ _ _ h => h)
      ((Step.of_all fun _ _ _ _ _ _ _ _ => trivial).trans (PinW.step_pinned h2b))).trans
    (Step.of_all fun _ _ _ _ _ _ _ H =>
      let ⟨w, hw⟩ := H.2
      ⟨w, hw, supp_of_untw w H.1, coh_of_untw H.1⟩)

theorem stepW_builtE {𝒮 : Slots} {p : WP} (hp : ∀ K B f T w, p K B f T w → Pinned K B f T w)
    (h4 : StepW (pinAnd (Has3 𝒮)) (Has4 𝒮)) (hc : StepW (pinAnd (Has4 𝒮)) (HasC (BuiltE 𝒮)))
    (h3 : StepW p (Has3 𝒮)) : StepW p (HasC (BuiltE 𝒮)) :=
  have q : StepW p Pinned := StepW.of_all fun _ _ _ _ _ _ _ h => hp _ _ _ _ _ h
  (q.and ((q.and h3).trans h4)).trans hc

end GlobalTheory.Mem.Top.Bl.MemberEx2

namespace GlobalTheory.Mem.Top.Bl

theorem memberE_of_steps2 : GlobalTheory.NT.RayField → GlobalTheory.Published.PrincipalIdealSt → GlobalTheory.Published.CMCurveGoodOutsidePrimeSt → StandardLattice.SiegelMassRatioCM →
    ∀ 𝒮 𝒮' : Slots, StepW Start (Has3 𝒮) → StepW (pinAnd (Has3 𝒮)) (Has4 𝒮) → AmbEx 𝒮 → DivEx 𝒮 → ThEx 𝒮 →
      ExportF KPx (IsBuiltE 𝒮) →
      Pass KPx (IsBuiltE 𝒮) (fun K B f T => ∃ w : ColW B f T, Start K B f T w ∧ Has3 𝒮' K B f T w) →
      StepW (pinAnd (Has3 𝒮')) (Has4 𝒮') → AmbEx 𝒮' → DivEx 𝒮' → ThEx 𝒮' →
      (∀ K B f T w Z c, BuiltE 𝒮' K B f T w Z c → GoodE 𝒮 K B f T w Z c ∧ DQ.TwAllAt (w.D Z) c.O.nch c.O.xd) → MemberE 𝒮 := by
  intro hR hP hC h2b 𝒮 𝒮' h3 h4 hA hD hT hE hPass h4' hA' hD' hT' hL
  have hB : BaseCond KPx := KPxCond.baseCond_KPx hR hP hC h2b
  have h1 : FirstG KPx (IsBuiltE 𝒮) :=
    step_hasCore (MemberEx2.step_start h2b)
      (MemberEx2.stepW_builtE (fun _ _ _ _ _ h => h.1) h4 (GlobalTheory.T.exists_constructedCore_of_all_construction_stages h2b 𝒮 hA hD hT) h3)
  have hW : StepW (fun K B f T w => Start K B f T w ∧ Has3 𝒮' K B f T w)
      (HasC fun K B f T w Z c => GoodE 𝒮 K B f T w Z c ∧ DQ.TwAllAt (w.D Z) c.O.nch c.O.xd) :=
    (MemberEx2.stepW_builtE (fun _ _ _ _ _ h => h.1.1) h4' (GlobalTheory.T.exists_constructedCore_of_all_construction_stages h2b 𝒮' hA' hD' hT')
      (StepW.of_all fun _ _ _ _ _ _ _ h => h.2)).trans
      (StepW.of_all fun _ _ _ _ _ _ _ H => let ⟨Z, c, hc⟩ := H; ⟨Z, c, hL _ _ _ _ _ _ _ hc⟩)
  have hS := step_hasCore (admitted := fun K B f T => ∃ w : ColW B f T, Start K B f T w ∧ Has3 𝒮' K B f T w)
    (Step.of_all fun _ _ _ _ _ _ _ h => h) hW
  have h2 : SecondG KPx (IsBuiltE 𝒮) (IsGoodE 𝒮) :=
    GlobalTheory.Mem.Top.GroupRetwisting.pass_step KPx _ _ _ hB hPass (hS.trans (Step.of_all fun _ _ _ _ _ _ _ H =>
      let ⟨C, W, V, S, N, G, c, hc⟩ := H
      ⟨C, W, V, S, N, G, c, positionOf_ind (R := fun K X f T c => IsBuiltE 𝒮 K X f T c ∧ DQ.TwAllAt X.toD7 c.O.nch c.O.xd ∧
        IsGoodE 𝒮 K X f T c) (fun _ _ _ _ _ _ _ h => ⟨positionOf_intro h.1.1, h.2, positionOf_intro h.1⟩) hc⟩))
  exact ⟨hB, h1, hE, h2⟩

end GlobalTheory.Mem.Top.Bl

end
end
