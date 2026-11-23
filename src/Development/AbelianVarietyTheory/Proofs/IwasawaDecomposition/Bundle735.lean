module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle682
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle040
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle666
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle651
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle724
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle699
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle727
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle388
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtOfFrameEqOfPointEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle531
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle028
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle039
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle726
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionBarycentreCellNextStage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle716
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle728
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle669
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullLinInjective
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KaUnfoldPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle206
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle668
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle667

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LieBase
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.FramePairGram GlobalTheory.TrueCx Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.HodgeOnDomain

namespace GlobalTheory.HodgeGenUnf

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {σ : c.F →+* ℂ} {r : ℕ}

theorem relab_mem {U : Formalism.L2.PjFree.Unf Xo c σ r} (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U)
    (k : U.Comp) (τ : GlobalTheory.AllWt.Psi H) : Formalism.L2.PjFree.relab c σ τ.1 ∈ (U.X k).Ψ :=
  ((hU.2.1 k).2 _).2 (((GlobalTheory.Relab.relab_good E H l c σ hσ).2.1 τ.1).2 τ.2)

theorem comb_unitary {U : Formalism.L2.PjFree.Unf Xo c σ r} (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U)
    (k : U.Comp) (x x₁ : (U.X k).dom) (hx : IsOrth (U.X k) x.1) (hx₁ : IsOrth (U.X k) x₁.1)
    (e : (U.un k x₁).x = (U.un k x).x) (τ : E →+* ℂ) (T : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ)
    (hT : ∀ b, Formalism.L2.Pj.IsCombAt (U.un k x).x ((U.un k x).u τ)
      (show Fin (Dw.mult τ) → CAt σ from fun b' => T b' b) ((U.un k x₁).u τ b)) :
    Tᴴ * T = 1 :=
  GlobalTheory.T.orthonormalFrames_lie_coordinates_unitary hσ hU k x x₁ hx hx₁ e τ T hT

theorem uniformisation_component_eq_of_same_modulusPoint {U : Formalism.L2.PjFree.Unf Xo c σ r} (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U)
    {k k' : U.Comp} (x : (U.X k).dom) (x' : (U.X k').dom) (h : (U.un k x).x = (U.un k' x').x) : k' = k := by
  obtain ⟨b, -, -, hb, t, ht⟩ := GlobalTheory.PointOfFrames.exists_frBor U hU hσ k x (U.un k' x') h
  obtain ⟨g0, -, b', -, e⟩ := (hU.2.2.2.1 k k' ⟨_, hb⟩ x').1 ⟨t, ht⟩
  exact congrArg Sigma.fst e

theorem unitary_of_single {Uf : ∀ σ' : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ' r}
    (hE : ∀ σ', σ' ≠ σ → IsEmpty (Uf σ').Comp) (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf (Uf σ))
    {y : CxPts (genStr Z) σ} {f g : EigFrame Z σ (y.1 ≫ genι Z)} (hf : IsHodgeFrame Uf y f) (hg : IsHodgeFrame Uf y g)
    (τ : E →+* ℂ) : (f.co g τ)ᴴ * f.co g τ = 1 := by
  classical
  obtain ⟨ψ, σ', k, x, h1, h2, h3, h4, h5, h6⟩ := hf
  obtain ⟨ψ₁, σ₁, k₁, x₁, g1, g2, g3, g4, g5, g6⟩ := hg
  have e1 : σ = σ' := by_contra fun h => (hE σ' (Ne.symm h)).false k
  have e2 : σ = σ₁ := by_contra fun h => (hE σ₁ (Ne.symm h)).false k₁
  subst e1 e2
  have hid : ∀ {ψ : ℂ →+* ℂ}, (ψ = RingHom.id ℂ ∨ ψ = starRingEnd ℂ) → σ = ψ.comp σ → ψ = RingHom.id ℂ := by
    intro ψ h h'
    rcases h with rfl | rfl
    · rfl
    · exact (not_good_conj c (σ := σ) hσ (h' ▸ hσ)).elim
  obtain rfl := hid h1 h2
  obtain rfl := hid g1 g2
  have hx : (cxPt Z ((Uf σ).un k x)).1 ≫ genι Z = spMap (RingHom.id ℂ) ≫ y.1 ≫ genι Z := by rw [h5, Category.assoc]
  obtain ⟨g', hg'⟩ := g.exists_isMap (RingHom.id ℂ) h2 hx
  have e := x_eq_of_cxPt (g5.trans h5.symm)
  obtain rfl : k = k₁ := (uniformisation_component_eq_of_same_modulusPoint hσ hU x x₁ e.symm).symm
  have key := comb_unitary hσ hU k x x₁ h4 g4 e τ _ (isCombAt_co e (fun τ i => (hg' τ i).trans (g6 τ i).symm) τ)
  rw [h6.co τ hg' hx] at key
  convert key using 2 <;> ext <;> simp

theorem gram_eq_of_single {Uf : ∀ σ' : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ' r}
    (hE : ∀ σ', σ' ≠ σ → IsEmpty (Uf σ').Comp) (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf (Uf σ))
    {b : ℝ} {hb : 0 < b} {G₀ : EigMet Z σ} {y : CxPts (genStr Z) σ} {f : EigFrame Z σ (y.1 ≫ genι Z)}
    (hf : IsHodgeFrame Uf y f) (g : EigFrame Z σ (y.1 ≫ genι Z)) (τ : E →+* ℂ) :
    (EigMet.hodge Uf b hb G₀).gram y g τ = (b : ℂ) • ((f.co g τ)ᴴ * f.co g τ) := by
  have h : ∃ f, IsHodgeFrame Uf y f := ⟨f, hf⟩
  refine (dif_pos h).trans (congrArg _ ?_)
  rw [← h.choose.co_mul f g, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ _ (f.co g τ),
    unitary_of_single hE hσ hU h.choose_spec hf, Matrix.one_mul]

theorem unfFam_empty (U : Formalism.L2.PjFree.Unf Xo c σ r) (σ' : c.F →+* ℂ) (h : σ' ≠ σ) :
    IsEmpty (unfFam U σ').Comp := by
  unfold unfFam
  rw [dite_eq_right (Ne.symm h)]
  exact ⟨Empty.elim⟩

theorem unfFam_self (U : Formalism.L2.PjFree.Unf Xo c σ r) : unfFam U σ = U := dif_pos rfl

theorem isHodgeFrame_of_eq {Uf : ∀ σ' : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ' r} {U : Formalism.L2.PjFree.Unf Xo c σ r}
    (hq : Uf σ = U) (hσ : Formalism.L2.PjFree.GoodEmb c σ) {k : U.Comp} {x : (U.X k).dom} (hx : IsOrth (U.X k) x.1) :
    IsHodgeFrame (Z := Z) Uf (cxPt Z (U.un k x)) (cxFrame Z (U.un k x)) := by
  subst hq
  exact isHodgeFrame_cxFrame hσ hx


variable (Z) in
theorem hodgeMet_gram_orth {U : Formalism.L2.PjFree.Unf Xo c σ r} (hσ : Formalism.L2.PjFree.GoodEmb c σ)
    (hU : Formalism.L2.PjFree.IsUnf U) {k : U.Comp} {x : (U.X k).dom} (hx : IsOrth (U.X k) x.1) (τ : E →+* ℂ) :
    (hodgeMet Z U).gram (cxPt Z (U.un k x)) (cxFrame Z (U.un k x)) τ = ((2 * Real.pi : ℝ) : ℂ) • 1 := by
  rw [hodgeMet, gram_eq_of_single (unfFam_empty U) hσ ((unfFam_self U).symm ▸ hU)
    (isHodgeFrame_of_eq (unfFam_self U) hσ hx), EigFrame.co_self, conjTranspose_one, Matrix.mul_one]

end GlobalTheory.HodgeGenUnf

namespace GlobalTheory.HodgeGenUnf

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {σ : c.F →+* ℂ}

def letter {U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)} (hσ : Formalism.L2.PjFree.GoodEmb c σ)
    (hU : Formalism.L2.PjFree.IsUnf U) (k : U.Comp) (τ : GlobalTheory.AllWt.Psi H) : (U.X k).Ψ :=
  ⟨Formalism.L2.PjFree.relab c σ τ.1, relab_mem hσ hU k τ⟩

theorem mult_psi (τ : GlobalTheory.AllWt.Psi H) : Dw.mult τ.1 = Dw.p := if_pos τ.2


variable (Z) in
theorem hodgeMet_gram_frame {U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)} (hσ : Formalism.L2.PjFree.GoodEmb c σ)
    (hU : Formalism.L2.PjFree.IsUnf U) (k : U.Comp) (f : (U.X k).dom) (τ : GlobalTheory.AllWt.Psi H) (τ' : (U.X k).Ψ)
    (hτ : τ'.1 = Formalism.L2.PjFree.relab c σ τ.1) (hj : Dw.p ≤ Dw.p + Dw.q) :
    ((hodgeMet Z U).gram (cxPt Z (U.un k f)) (cxFrame Z (U.un k f)) τ.1).submatrix
        (Fin.cast (mult_psi τ).symm) (Fin.cast (mult_psi τ).symm) =
      ((2 * Real.pi : ℝ) : ℂ) • ((coW (U.X k) hj f.1 τ')ᴴ * (hP (moeb (frameCo (U.X k) hj f.1 τ') 0))⁻¹ *
        coW (U.X k) hj f.1 τ') := by
  have hp : (U.X k).p0 = Dw.p + Dw.q - Dw.p := by rw [(hU.2.1 k).1]; omega
  obtain ⟨x1, h1, b, hb, ef⟩ := ortho_holds (Dw.p + Dw.q) (U.X k) f.1 f.2
  let f' : (U.X k).dom := ⟨x1, KU.orth_dom _ h1⟩
  have hz : domPt (U.X k) hj (Equiv.refl (U.X k).Ψ) f.1 = domPt (U.X k) hj (Equiv.refl (U.X k).Ψ) f'.1 := by
    show domPt _ _ _ f.1 = domPt _ _ _ x1
    rw [ef, domPt_rmul _ _ _ hb]
  have hmo : ∀ ρ : (U.X k).Ψ, moeb (frameCo (U.X k) hj f.1 ρ) 0 = moeb (frameCo (U.X k) hj f'.1 ρ) 0 :=
    fun ρ => congrFun hz ρ
  have h1' := fun ρ => PointWell.block_of_moeb_eq _ hj hp f.2 f'.2 ρ (hmo ρ)
  have h2' := fun ρ => PointWell.block_of_moeb_eq _ hj hp f'.2 f.2 ρ (hmo ρ).symm
  have hx : (U.un k f).x = (U.un k f').x := PointWell.pt_eq_of_block hU hσ k f f' h1' h2'
  have hg : (hodgeMet Z U).gram (cxPt Z (U.un k f)) (cxFrame Z (U.un k f)) τ.1 =
      (Matrix.of fun b i : Fin (Dw.mult τ.1) => coef (U.X k) f.1 f'.1 (Formalism.L2.PjFree.relab c σ τ.1) b i)ᴴ *
        (hodgeMet Z U).gram (cxPt Z (U.un k f')) (cxFrame Z (U.un k f')) τ.1 *
        Matrix.of fun b i : Fin (Dw.mult τ.1) => coef (U.X k) f.1 f'.1 (Formalism.L2.PjFree.relab c σ τ.1) b i :=
    eigGram_of_comb (hodgeMet Z U) _ _ hx τ.1 _ (fun i => lie_comb_of_block hU hσ k f f' h1' h2' τ.1 i)
  rw [hg, hodgeMet_gram_orth Z hσ hU (x := f') h1, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, smul_submatrix_sq]
  set e := Fin.cast (mult_psi τ).symm
  have he : Function.Bijective e := (finCongr (mult_psi τ).symm).bijective
  rw [Matrix.submatrix_mul _ _ _ _ _ he, ← conjTranspose_submatrix]
  have hKe : (Matrix.of fun b i : Fin (Dw.mult τ.1) =>
      coef (U.X k) f.1 f'.1 (Formalism.L2.PjFree.relab c σ τ.1) b i).submatrix e e =
      Matrix.of fun b i : Fin Dw.p => coef (U.X k) f.1 f'.1 τ'.1 b i := by
    ext b i; rw [hτ]; rfl
  obtain ⟨hco1, -⟩ := hodge_co (U.X k) hj hp h1 τ'
  rw [hKe, coef_eq_coW_change (U.X k) hj hp f.2 f'.2 τ' (hmo τ'), hmo τ',
    eq_of_conj_eq_one (isUnit_coW _ _ hp f'.2 _) hco1]
  congr 1
  simp only [conjTranspose_mul, Matrix.mul_assoc]

end GlobalTheory.HodgeGenUnf
end
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix


theorem _root_.GlobalTheory.T.exists_analytic_flagDomain_frame_lift_algebraicChart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsOpenImmersion j → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∃ (k' : U.Comp) (s : ReciprocityTheory.L2DbarEstimates.V X.dim → ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k').Ψ (Dw.p + Dw.q)), AnalyticAt ℂ s (c'.e y) ∧ ∀ᶠ w in 𝓝 (c'.e y), ∃ hs : s w ∈ (U.X k').dom, cxPt T.Z (U.un k' ⟨s w, hs⟩) = cxOf e σ hj (c'.e.symm w) := by
  first | exact @GlobalTheory.LieBase.exists_analytic_frame_lift | exact GlobalTheory.LieBase.exists_analytic_frame_lift | (intros; apply GlobalTheory.LieBase.exists_analytic_frame_lift <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix


theorem _root_.GlobalTheory.T.exists_holomorphic_invertible_frame_coordinates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsOpenImmersion j → Tied e X j f₀ Eb A₀ → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∀ A ∈ Eb.S (under y), ∀ (k' : U.Comp) (s : ReciprocityTheory.L2DbarEstimates.V X.dim → ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k').Ψ (Dw.p + Dw.q)), AnalyticAt ℂ s (c'.e y) → (∀ᶠ w in 𝓝 (c'.e y), ∃ hs : s w ∈ (U.X k').dom, cxPt T.Z (U.un k' ⟨s w, hs⟩) = cxOf e σ hj (c'.e.symm w)) → ∃ K : ReciprocityTheory.L2DbarEstimates.V X.dim → Mat Dw.mult ℂ, (∀ τ a b, AnalyticAt ℂ (fun w => K w τ a b) (c'.e y)) ∧ (∀ τ, IsUnit (K (c'.e y) τ).det) ∧ ∀ᶠ w in 𝓝 (c'.e y), (∃ g : EigFrame T.Z σ ((cxOf e σ hj (c'.e.symm w)).1 ≫ genι T.Z), FrameAt e f₀ A₀ A (c'.e.symm w) g) ∧ ∀ (hs : s w ∈ (U.X k').dom) (g : EigFrame T.Z σ ((cxOf e σ hj (c'.e.symm w)).1 ≫ genι T.Z)), FrameAt e f₀ A₀ A (c'.e.symm w) g → ∀ (M : EigMet T.Z σ) (τ : E →+* ℂ), M.gram (cxOf e σ hj (c'.e.symm w)) g τ = (K w τ)ᴴ * M.gram (cxPt T.Z (U.un k' ⟨s w, hs⟩)) (cxFrame T.Z (U.un k' ⟨s w, hs⟩)) τ * K w τ := by
  first | exact @GlobalTheory.FrameLift.exists_holomorphic_frame_coords | exact GlobalTheory.FrameLift.exists_holomorphic_frame_coords | (intros; apply GlobalTheory.FrameLift.exists_holomorphic_frame_coords <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

theorem _root_.GlobalTheory.T.inRealCone_generators_of_linForm_eq_zero : ∀ {X : Type} [AddCommGroup X] {m p : ℕ} (δ : Fin m → LinearMap.BilinForm ℤ X) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ)
    (e : Fin p ↪ Fin m) (β : LinearMap.BilinForm ℤ X), (∀ i, 0 ≤ h (δ i)) → (∀ i, h (δ i) = 0 → i ∈ Set.range e) →
    InRCone δ β → h β = 0 → InRCone (fun k => δ (e k)) β := by
  first | exact @GlobalTheory.PolFan.inRCone_of_apply_eq_zero | exact GlobalTheory.PolFan.inRCone_of_apply_eq_zero | (intros; apply GlobalTheory.PolFan.inRCone_of_apply_eq_zero <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark


theorem _root_.GlobalTheory.T.inRealCone_summands_of_evalZ_additive_cell : ∀ (O : Type) [CommRing O] (bar : O → O) (ψ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ → ∀ (k : ℕ) (u : Fin k → LinearMap.BilinForm ℤ X), (∀ j, u j ∈ balForms bar X) → (∀ j y, 0 ≤ u j y y) → InRCone γ (∑ j, u j) → ψ.evalZ (∑ j, u j) ≤ ∑ j, ψ.evalZ (u j) → ∀ j, InRCone γ (u j) := by
  first | exact @GlobalTheory.PolFan.Mark.inRCone_of_evalZ_sum_le | exact GlobalTheory.PolFan.Mark.inRCone_of_evalZ_sum_le | (intros; apply GlobalTheory.PolFan.Mark.inRCone_of_evalZ_sum_le <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

noncomputable section

namespace GlobalTheory.PolFan.Mark

theorem exists_zsmul_mem_of_finrank_le_of_le {M : Type} [AddCommGroup M] {N L : Submodule ℤ M}
    [Module.Finite ℤ L] (hNL : N ≤ L) (hr : Module.finrank ℤ L ≤ Module.finrank ℤ N) {x : M} (hx : x ∈ L) :
    ∃ n : ℤ, n ≠ 0 ∧ n • x ∈ N := by
  have h1 := Submodule.finrank_quotient_add_finrank (N.comap L.subtype)
  have h2 : Module.finrank ℤ (N.comap L.subtype) = Module.finrank ℤ N :=
    (Submodule.comapSubtypeEquivOfLe hNL).finrank_eq
  have h0 : Module.finrank ℤ (L ⧸ N.comap L.subtype) = 0 := by omega
  obtain ⟨a, ha, hax⟩ := (Module.finrank_eq_zero_iff.1 h0) (Submodule.Quotient.mk ⟨x, hx⟩)
  refine ⟨a, ha, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hax
  exact hax

theorem vanish_of_inRCone_of_genRank_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ lab : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → IsCarrierDim H.bar q ψ lab → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → Dominates H.bar X → ∀ (m : ℕ) (τ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ τ → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone τ β → (genRank τ : ℝ) ≤ lab.evalZ β → ∀ j y, β y y = 0 → τ j y y = 0 := by
  intro E _ _ _ H q ψ lab hψ hlab X _ _ _ _ hX hdom m τ hτ β hβ hβp hβc hrk j y hy
  classical
  let P : Fin m → Prop := fun j => ∀ y, β y y = 0 → τ j y y = 0
  have hw : ∀ j, ∃ y, β y y = 0 ∧ (¬ P j → 0 < τ j y y) := by
    intro j
    by_cases hj : P j
    · exact ⟨0, by simp, fun h => (h hj).elim⟩
    · simp only [P, not_forall] at hj
      obtain ⟨y, hy, hne⟩ := hj
      exact ⟨y, hy, fun _ => lt_of_le_of_ne (hτ.nonneg j y) (Ne.symm hne)⟩
  choose w hw0 hwpos using hw
  let T : Finset (Fin m) := Finset.univ.filter P
  let s : Fin T.card ↪ Fin m := (T.orderEmbOfFin rfl).toEmbedding
  have hsr : Set.range s = ↑T := Finset.range_orderEmbOfFin T rfl
  have hP : ∀ k, P k ↔ k ∈ Set.range s := fun k => by rw [hsr]; simp [T]
  let hf : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ := ∑ i, LinearMap.applyₗ (w i) ∘ₗ LinearMap.applyₗ (w i)
  have hfa : ∀ x : LinearMap.BilinForm ℤ X, hf x = ∑ i, x (w i) (w i) := fun x => by
    simp [hf, LinearMap.sum_apply]
  have hcut : IsFaceCut τ s hf := by
    refine ⟨fun k => ?_, fun k => ?_⟩
    · rw [hfa]; exact Finset.sum_nonneg fun i _ => hτ.nonneg k (w i)
    · rw [← hP, hfa]
      constructor
      · intro h0
        by_contra hk
        have h1 : τ k (w k) (w k) ≤ ∑ i, τ k (w i) (w i) :=
          Finset.single_le_sum (f := fun i => τ k (w i) (w i)) (fun i _ => hτ.nonneg k (w i)) (Finset.mem_univ k)
        have h2 := hwpos k hk
        omega
      · intro hk
        exact Finset.sum_eq_zero fun i _ => hk _ (hw0 i)
  have hcell : IsCell H.bar ψ (fun k => τ (s k)) :=
    isCell_face_of_isFaceCut E H q ψ hψ X hX hdom m τ hτ _ s hf hcut
  obtain ⟨c, hc, hce⟩ := hβc
  have hc0 : ∀ i, ¬ P i → c i = 0 := by
    intro i hi
    have e : (β (w i) (w i) : ℝ) = ∑ k, c k * (τ k (w i) (w i) : ℝ) := by
      have := LinearMap.congr_fun₂ hce (w i) (w i)
      simpa [LinearMap.sum_apply] using this
    rw [hw0 i, Int.cast_zero] at e
    have h1 : c i * (τ i (w i) (w i) : ℝ) ≤ ∑ k, c k * (τ k (w i) (w i) : ℝ) :=
      Finset.single_le_sum (f := fun k => c k * (τ k (w i) (w i) : ℝ))
        (fun k _ => mul_nonneg (hc k) (by exact_mod_cast hτ.nonneg k (w i))) (Finset.mem_univ i)
    have h2 : (0 : ℝ) < τ i (w i) (w i) := by exact_mod_cast hwpos i hi
    rw [← e] at h1
    nlinarith [hc i]
  have hmap : Finset.univ.map s = T := by
    ext i
    simp only [Finset.mem_map, Finset.mem_univ, true_and]
    rw [← Set.mem_range, ← hP]
    simp [T]
  have hcone : InRCone (fun k => τ (s k)) β := by
    refine ⟨fun k => c (s k), fun k => hc _, ?_⟩
    rw [hce]
    have e1 := Finset.sum_map Finset.univ s (fun i => c i • toReal (τ i))
    rw [hmap] at e1
    rw [← e1]
    refine (Finset.sum_subset (Finset.subset_univ T) fun i _ hi => ?_).symm
    rw [hc0 i (by simpa [T] using hi), zero_smul]
  have hl := hlab X hX β hβ hβp
  have hle : sInf {k : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ ∧ InRCone γ β ∧
      genRank γ = k} ≤ genRank (fun k => τ (s k)) := Nat.sInf_le ⟨_, _, hcell, hcone, rfl⟩
  have hrk' : genRank τ ≤ genRank (fun k => τ (s k)) := by
    rw [hl] at hrk
    have h4 : ((genRank τ : ℕ) : ℝ) ≤ ((genRank (fun k => τ (s k)) : ℕ) : ℝ) := hrk.trans (Nat.cast_le.2 hle)
    exact_mod_cast h4
  haveI : Module.Finite ℤ (Submodule.span ℤ (Set.range τ)) := Module.Finite.span_of_finite ℤ (Set.finite_range τ)
  have hNL : Submodule.span ℤ (Set.range fun k => τ (s k)) ≤ Submodule.span ℤ (Set.range τ) :=
    Submodule.span_mono (Set.range_comp_subset_range s τ)
  obtain ⟨n, hn, hnmem⟩ := exists_zsmul_mem_of_finrank_le_of_le hNL hrk' (Submodule.subset_span ⟨j, rfl⟩)
  have key : ∀ x ∈ Submodule.span ℤ (Set.range fun k => τ (s k)), x y y = 0 := fun x hx => by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact (hP (s k)).2 ⟨k, rfl⟩ y hy
    | zero => simp
    | add x z _ _ h1 h2 => simp [h1, h2]
    | smul a x _ h => simp [h]
  have h3 := key _ hnmem
  simp only [LinearMap.smul_apply, smul_eq_mul] at h3
  exact (mul_eq_zero.1 h3).resolve_left hn

end GlobalTheory.PolFan.Mark
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

theorem _root_.GlobalTheory.T.polyFan_face_cut_by_intLinearForm_isCell : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → Dominates H.bar X → ∀ (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ v → ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut v s h → IsCell H.bar ψ (fun j => v (s j)) := by
  first | exact @GlobalTheory.PolFan.isCell_face_of_isFaceCut | exact GlobalTheory.PolFan.isCell_face_of_isFaceCut | (intros; apply GlobalTheory.PolFan.isCell_face_of_isFaceCut <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

theorem _root_.GlobalTheory.T.starSubdivision_subordinate_to_fan : ∀ (O : Type) [CommRing O] (bar : O → O) (q : ℕ) (ψ w ψ' : InvFun O), IsStarOf bar q ψ w ψ' → Subordinate bar q ψ' ψ := by
  first | exact @GlobalTheory.PolFan.subordinate_of_isStarOf | exact GlobalTheory.PolFan.subordinate_of_isStarOf | (intros; apply GlobalTheory.PolFan.subordinate_of_isStarOf <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

theorem _root_.GlobalTheory.T.starSubdivision_barycentre_cell_next_stage : ∀ (O : Type) [CommRing O] (bar : O → O) (ψ lab φ' w : InvFun O) (i : ℕ) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (b a : ℕ) (v : Fin b → LinearMap.BilinForm ℤ X) (u : Fin a → LinearMap.BilinForm ℤ X), IsCell bar ψ v → Function.Injective (fun j => lab.evalZ (u j)) → (∀ j, ((i + 1 : ℕ) : ℝ) < lab.evalZ (u j)) → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v β → lab.evalZ β ≤ ((i + 1 : ℕ) : ℝ)) → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone (Fin.append v u) β → ¬ InRCone v β → ((i + 1 : ℕ) : ℝ) < lab.evalZ β) → (∀ (d : Fin b → ℤ) (c : Fin a → ℤ), ∑ j, c j • u j = ∑ k, d k • v k → c = 0) → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∃ n : ℕ, lab.evalZ β = n) → (∀ (m' : ℕ) (s : Fin m' ↪ Fin b) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut v s h → IsCell bar ψ (fun j => v (s j))) → (∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → lab.evalZ β = ((i + 1 : ℕ) : ℝ) → ∃ β₁ ∈ balForms bar X, (∀ y, 0 ≤ β₁ y y) ∧ w.evalZ β₁ = 1 ∧ InRCone γ β₁) → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∀ β' ∈ balForms bar X, (∀ y, 0 ≤ β' y y) → w.evalZ β = 1 → w.evalZ β' = 1 → InRCone (Fin.append v u) β → InRCone (Fin.append v u) β' → β = β') → (∀ β₀ ∈ balForms bar X, (∀ y, 0 ≤ β₀ y y) → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v β₀ → ∀ (c₀ : ℝ) (c : Fin b → ℝ), 0 < c₀ → (∀ k, 0 ≤ c k) → toReal β = c₀ • toReal β₀ + ∑ k, c k • toReal (v k) → lab.evalZ β₀ ≤ lab.evalZ β) → ∀ β₀ ∈ balForms bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → lab.evalZ β₀ = ((i + 1 : ℕ) : ℝ) → InRCone (Fin.append v u) β₀ → (∀ (m' : ℕ) (s : Fin m' ↪ Fin (b + a)) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut (Fin.append v u) s h → 0 < h β₀ → IsCell bar φ' (Fin.cons β₀ fun j => Fin.append v u (s j))) → ∀ (m' : ℕ) (s : Fin m' ↪ Fin (b + a)) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut (Fin.append v u) s h → 0 < h β₀ → ∃ (b' a' : ℕ) (v' : Fin b' → LinearMap.BilinForm ℤ X) (u' : Fin a' → LinearMap.BilinForm ℤ X), IsCell bar φ' (Fin.append v' u') ∧ IsCell bar ψ v' ∧ (∀ k, InRCone (Fin.append v' u') ((Fin.cons β₀ fun j => Fin.append v u (s j) : Fin (m' + 1) → LinearMap.BilinForm ℤ X) k)) ∧ Function.Injective (fun j => lab.evalZ (u' j)) ∧ (∀ j, (i : ℝ) < lab.evalZ (u' j)) ∧ (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v' β → lab.evalZ β ≤ i) ∧ (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone (Fin.append v' u') β → ¬ InRCone v' β → (i : ℝ) < lab.evalZ β) ∧ ∀ (d : Fin b' → ℤ) (c : Fin a' → ℤ), ∑ j, c j • u' j = ∑ k, d k • v' k → c = 0 := by
  first | exact @GlobalTheory.PolFan.star_cell_bary_step | exact GlobalTheory.PolFan.star_cell_bary_step | (intros; apply GlobalTheory.PolFan.star_cell_bary_step <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

theorem _root_.GlobalTheory.T.evalR_starDepth_le_of_centre_bound : ∀ (O : Type) [CommRing O] (bar : O → O) (ψ w : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) (s : ℝ), IsCell bar ψ γ → B ∈ rcone γ → 0 ≤ s → (∀ v ∈ balForms bar X, (∀ y, 0 ≤ v y y) → w.evalZ v = 1 → InRCone γ v → ∀ t : ℝ, 0 < t → B - t • toReal v ∈ rcone γ → t ≤ s) → evalR (starDepth bar ψ w) B ≤ s := by
  first | exact @GlobalTheory.PolFan.evalR_starDepth_le | exact GlobalTheory.PolFan.evalR_starDepth_le | (intros; apply GlobalTheory.PolFan.evalR_starDepth_le <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell


theorem _root_.GlobalTheory.T.starDepthSet_bddAbove_of_unique_centre : ∀ (O : Type) [CommRing O] (bar : O → O) (ψ w : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) (v : LinearMap.BilinForm ℤ X), IsCell bar ψ γ → B ∈ rcone γ → v ∈ balForms bar X → (∀ y, 0 ≤ v y y) → v ≠ 0 → (∀ v' ∈ balForms bar X, (∀ y, 0 ≤ v' y y) → w.evalZ v' = 1 → InRCone γ v' → v' = v) → ∀ (n : ℕ) (π : (Fin n → O) →ₗ[O] X), Function.Surjective π → BddAbove (depthSet bar ψ w n (fun a b => B (π a) (π b))) := by
  first | exact @GlobalTheory.PolFan.depthSet_bddAbove_of_unique_centre | exact GlobalTheory.PolFan.depthSet_bddAbove_of_unique_centre | (intros; apply GlobalTheory.PolFan.depthSet_bddAbove_of_unique_centre <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan.StarGap

theorem gap_eq_sum {O : Type} [CommRing O] {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} (N : ℕ) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ)
    (hlin : φ.LinearOn γ) {β : LinearMap.BilinForm ℤ X} {c : Fin m → ℝ} (hc : ∀ i, 0 ≤ c i)
    (hsum : toReal β = ∑ i, c i • toReal (γ i)) :
    (ℓ β : ℝ) - N * φ.evalZ β = ∑ i, c i * ((ℓ (γ i) : ℝ) - N * φ.evalZ (γ i)) := by
  have h1 : ∑ i : Fin (m + 1), (Fin.cons (-1) c : Fin (m + 1) → ℝ) i •
      toReal ((LinearMap.id : LinearMap.BilinForm ℤ X →ₗ[ℤ] LinearMap.BilinForm ℤ X)
        ((Fin.cons β γ : Fin (m + 1) → LinearMap.BilinForm ℤ X) i)) = 0 := by
    simp [Fin.sum_univ_succ, hsum]
  have h2 := sum_mul_eq_zero_of_sum_toReal (j := LinearMap.id) (fun _ _ h => h) ℓ h1
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] at h2
  have h3 : φ.evalZ β = ∑ i, c i * φ.evalZ (γ i) := by
    rw [← evalR_toReal, hsum]; exact (linearOn_iff φ γ).1 hlin c hc
  have h4 : (ℓ β : ℝ) = ∑ i, c i * ℓ (γ i) := by simp at h2; linarith
  rw [h4, h3, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem starDepth_le_gap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → IsCentreSet H.bar q ψ w → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (N : ℕ) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsCell H.bar ψ γ → (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) → 0 < N → StrictWith H.bar ψ N ℓ γ → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → (starDepth H.bar ψ w).evalZ β ≤ ℓ β - N * ψ.evalZ β := by
  intro E _ _ _ H q ψ w hψ _ X _ _ _ _ hX m γ N ℓ _ hno _ hsw β hβ hp
  have hfan := hψ X hX
  obtain ⟨-, hge, heq⟩ := hsw

  have hmem : toReal β ∈ psdCone (bar := H.bar) (X := X) := by
    have := ConeSub.sum_smul_toReal_mem_psdCone (𝓞 E) H.bar X 1 ![β] ![1] (fun i => by fin_cases i; exact hβ)
      (fun i y => by fin_cases i; exact hp y) (fun i => by fin_cases i; norm_num)
    simpa using this
  obtain ⟨S, -, hS⟩ := hfan.finite
  obtain ⟨e, m', δ₀, c, hδ₀, -, hc, he⟩ := hS _ hmem
  set δ : Fin m' → LinearMap.BilinForm ℤ X := fun i => pull e.symm.toLinearMap (δ₀ i) with hδdef
  have hδ : IsCell H.bar ψ δ := CarDim.isCell_pull_equiv hδ₀ e.symm
  have hβc : toReal β = ∑ i, c i • toReal (δ i) := LinearMap.ext₂ fun a b => by
    have := LinearMap.congr_fun₂ he (e.symm a) (e.symm b)
    simpa [hδdef, LinearMap.sum_apply] using this
  rw [← evalR_toReal]
  refine evalR_starDepth_le _ H.bar ψ w X m' δ (toReal β) _ hδ ⟨c, hc, hβc⟩ (sub_nonneg.2 (hge β hβ hp)) ?_
  rintro v hv hvp hwv ⟨b, hb, hvb⟩ t ht ⟨d, hd, hdt⟩

  have hv1 : (1 : ℝ) ≤ (ℓ v : ℝ) - N * ψ.evalZ v := by
    obtain ⟨n, hn⟩ := hfan.integral v hv hvp
    have h0 := hge v hv hvp
    have hne : (N : ℝ) * ψ.evalZ v ≠ ℓ v := fun h => by
      obtain ⟨k, a, hk, hka⟩ := heq v hv hvp h
      obtain ⟨g, hg, hgs⟩ := StarUpper.sum_mem_rcone (δ := ![v]) (γ := γ) ![1] (fun i => by fin_cases i; norm_num)
        (fun i _ => by fin_cases i; exact ⟨k, a, hk, hka⟩)
      have := hno v hv hvp ⟨g, hg, by simpa using hgs⟩
      rw [hwv] at this
      exact one_ne_zero this
    have hlt := lt_of_le_of_ne h0 hne
    rw [hn] at hlt ⊢
    have h1 : (N : ℤ) * n < ℓ v := by exact_mod_cast hlt
    have h2 : (1 : ℤ) ≤ ℓ v - N * n := by omega
    exact_mod_cast h2
  have hβ' : toReal β = ∑ i, (t * b i + d i) • toReal (δ i) := by
    have : toReal β = t • toReal v + (toReal β - t • toReal v) := by abel
    rw [this, hdt, hvb, Finset.smul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [add_smul, smul_smul]
  have e1 := gap_eq_sum N ℓ hδ.linear (fun i => add_nonneg (mul_nonneg ht.le (hb i)) (hd i)) hβ'
  have e2 := gap_eq_sum N ℓ hδ.linear hb hvb
  have e3 : 0 ≤ ∑ i, d i * ((ℓ (δ i) : ℝ) - N * ψ.evalZ (δ i)) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hd i) (sub_nonneg.2 (hge _ (hδ.mem i) (hδ.nonneg i)))
  have e4 : (ℓ β : ℝ) - N * ψ.evalZ β = t * ((ℓ v : ℝ) - N * ψ.evalZ v) +
      ∑ i, d i * ((ℓ (δ i) : ℝ) - N * ψ.evalZ (δ i)) := by
    rw [e1, e2, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e4]
  nlinarith [mul_le_mul_of_nonneg_left hv1 ht.le]

end GlobalTheory.PolFan.StarGap
end
