module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1304
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1306
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1307
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1354
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle225
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle231
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1309
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1310
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
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle041
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.hermLineBundleGeometricDegree_nonneg_of_semiPos : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ L : HermLB p, L.SemiPos D → 0 ≤ gdeg L D := by
  first | exact @GlobalTheory.HSNef.gdeg_nonneg_of_semiPos | exact GlobalTheory.HSNef.gdeg_nonneg_of_semiPos | (intros; apply GlobalTheory.HSNef.gdeg_nonneg_of_semiPos <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

theorem _root_.GlobalTheory.T.cubeValue_complexPoints_eq_frameAlternatingProduct : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}
    (ν : NumOf D ℂ N) (d : AB N.toNumB g), d.Cub → ∀ (G : Geo ν d) (x y z : Fin g → ℂ) (j : thK.{0} → D.P.L.ι),
    (∀ I : thK.{0}, ⊤ ≤ (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, z] i))).left ⁻¹ᵁ D.P.L.U (j I)) →
    valF (lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z)))).left (LB.wchart D.P.L (thφ D.P.A (x3 D.P.A)) j)
      (D.cub.t.s j).val = ∏ I : thK.{0}, G.frG (j I) (∑ i ∈ I.down, ![x, y, z] i) ^ thε I := by
  first | exact @GlobalTheory.MBLow.Cl.cube_val_frame | exact GlobalTheory.MBLow.Cl.cube_val_frame | (intros; apply GlobalTheory.MBLow.Cl.cube_val_frame <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.torusExtensionTangent_pullback_complexDualNumbers : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (C : Type) [Field C] [Algebra (FractionRing V) C] (N : NumD C) (ν : NumOf D C N) (gm₀ : GtPt D (epsR V)), GtTan gm₀ → ∃ gm : GtPt D (TE V C), GtPt.IsPull (spMap (dualMap (toF V C))) gm₀ gm ∧ (∃ o : GtPtF D C, o.IsZero ∧ GtPt.IsPullF C (redE C) gm o) ∧ (gm₀.b = DegPre.zeroT D (epsR V) → gm.b = DegPre.zeroT D (TE V C)) ∧ ∀ (a : V) (χ : D.X), (∀ (Z : Scheme.{0}) (q : Z ⟶ (epsR V).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good D.P.L z J → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val (gm₀.s χ) q z J).val = ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber V))).inv.hom (1 + TrivSqZeroExt.inr a))) → vE (gm.s χ) (𝟙 _) ν.J = 1 + TrivSqZeroExt.inr (toF V C a) := by
  first | exact @GlobalTheory.MBLow.TanPull.main | exact GlobalTheory.MBLow.TanPull.main | (intros; apply GlobalTheory.MBLow.TanPull.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

theorem _root_.GlobalTheory.T.weilPairing_degenerationTorsion_classical : AllCD fun {N} {g'} {r} {g} {bX} d σ => ∀ k : ℕ, 0 < k → ∀ M Nn M' Nn' p p', d.Rep σ k M Nn p → d.Rep σ k M' Nn' p' → (N.wp p p' : ℂ) = Complex.exp ((2 * Real.pi * Complex.I : ℂ) * (cv M ⬝ᵥ cv Nn' - cv Nn ⬝ᵥ cv M') / k) := by
  first | exact @GlobalTheory.MBLow.Cl.wp_classical | exact GlobalTheory.MBLow.Cl.wp_classical | (intros; apply GlobalTheory.MBLow.Cl.wp_classical <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

theorem _root_.GlobalTheory.T.degenerationTorsion_eq_periodLattice_mod_level : AllCD fun {N} {g'} {r} {g} {bX} d σ => ∀ k : ℕ, 0 < k → (∀ p, ∃ M Nn, d.Rep σ k M Nn p) ∧ (∀ M Nn, ∃! p, d.Rep σ k M Nn p) ∧ (∀ M Nn M' Nn' p p', d.Rep σ k M Nn p → d.Rep σ k M' Nn' p' → d.Rep σ k (M + M') (Nn + Nn') (p * p')) ∧ ∀ M Nn M' Nn' p p', d.Rep σ k M Nn p → d.Rep σ k M' Nn' p' → (N.QEq p p' ↔ ∃ M₁ N₁, M' = M + (k : ℤ) • M₁ ∧ Nn' = Nn + (k : ℤ) • N₁) := by
  first | exact @GlobalTheory.MBLow.Cl.torsion_eq_periods_mod | exact GlobalTheory.MBLow.Cl.torsion_eq_periods_mod | (intros; apply GlobalTheory.MBLow.Cl.torsion_eq_periods_mod <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

theorem _root_.GlobalTheory.T.fourierJacobiExpansion_fderiv_termwise : AllCD fun {N} {g'} {r} {g} {bX} d σ => ∀ S : Matrix (Fin r) (Fin r) ℂ, S.IsSymm → ((d.full σ S).map Complex.im).PosDef → (∀ χ, Differentiable ℂ (d.fj σ S χ)) ∧ ∀ Z W, (Summable fun χ => ‖fderiv ℂ (d.fj σ S χ) Z W‖) ∧ ∑' χ, fderiv ℂ (d.fj σ S χ) Z W = fderiv ℂ (thetaChar (d.full σ S) (d.aF σ) (d.bF σ)) Z W := by
  first | exact @GlobalTheory.MBLow.Cl.fj_expansion_fderiv | exact GlobalTheory.MBLow.Cl.fj_expansion_fderiv | (intros; apply GlobalTheory.MBLow.Cl.fj_expansion_fderiv <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix.IsomCalc

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {σ : k →+* ℂ}
variable {L M : MLine p σ}

theorem isom_of_local {J : Type} (W : J → X.Opens) (hW : ∀ x, ∃ j, x ∈ W j) (a : J → M.B.ι)
    (b : J → L.B.ι) (ha : ∀ j, W j ≤ M.B.U (a j)) (hb : ∀ j, W j ≤ L.B.U (b j)) (u : ∀ j, Γ(X, W j)ˣ)
    (hu : ∀ (x : X) j j', x ∈ W j → x ∈ W j' → gm (𝟙 X) x (W j) (u j) =
      gm (𝟙 X) x _ (M.B.g (a j) (a j')) * (gm (𝟙 X) x _ (L.B.g (b j) (b j')))⁻¹ * gm (𝟙 X) x (W j') (u j'))
    (hφ : ∀ j (y : CxPts p σ), y ∈ ptsIn p σ (W j) →
      M.φ.φ (a j) y = L.φ.φ (b j) y + logSq y (W j) (u j)) : L.Isom M := by
  let v (c : M.B.ι × L.B.ι) (j : J) : Γ(X, M.B.U c.1 ⊓ L.B.U c.2 ⊓ W j)ˣ :=
    res (inf_le_inf inf_le_left (ha j)) (M.B.g c.1 (a j)) *
      (res (inf_le_inf inf_le_right (hb j)) (L.B.g c.2 (b j)))⁻¹ * res inf_le_right (u j)
  have hv (c j) (x : X) (hx : x ∈ M.B.U c.1 ⊓ L.B.U c.2 ⊓ W j) : gm (𝟙 X) x _ (v c j) =
      gm (𝟙 X) x _ (M.B.g c.1 (a j)) * (gm (𝟙 X) x _ (L.B.g c.2 (b j)))⁻¹ * gm (𝟙 X) x _ (u j) := by
    simp only [v, map_mul, map_inv, gm_res (𝟙 X) x _ hx]
  have key : ∀ {G : Type} [CommGroup G] (a b c d e : G), a * b * (c * d)⁻¹ * e = a * c⁻¹ * (b * d⁻¹ * e) := by
    intro G _ a b c d e
    simp only [mul_inv]
    ac_rfl
  have hg (c : M.B.ι × L.B.ι) : ∃ s : Γ(X, M.B.U c.1 ⊓ L.B.U c.2)ˣ, ∀ j, res inf_le_left s = v c j := by
    refine glue_unit _ _ _ (fun x hx => ?_) (v c) fun j j' x hx => ?_
    · obtain ⟨j, hj⟩ := hW x
      exact Opens.mem_iSup.2 ⟨j, hx, hj⟩
    · rw [hv c j x hx.1, hv c j' x hx.2, hu x j j' hx.1.2 hx.2.2,
        ← gm_cocycle M.φ.isLB (𝟙 X) x hx.1.1.1 (ha j hx.1.2) (ha j' hx.2.2),
        ← gm_cocycle L.φ.isLB (𝟙 X) x hx.1.1.2 (hb j hx.1.2) (hb j' hx.2.2), key]
  choose s hs using hg
  have hs' (c j) (x : X) (hx : x ∈ M.B.U c.1 ⊓ L.B.U c.2 ⊓ W j) : gm (𝟙 X) x _ (s c) =
      gm (𝟙 X) x _ (M.B.g c.1 (a j)) * (gm (𝟙 X) x _ (L.B.g c.2 (b j)))⁻¹ * gm (𝟙 X) x _ (u j) := by
    rw [← hv c j x hx, ← hs, gm_res (𝟙 X) x _ hx]
  refine ⟨⟨s⟩, (isGen_iff_germ _).2 fun x c c' hc hc' => ?_, fun a₀ b₀ y h₁ h₂ => ?_⟩
  · obtain ⟨j, hj⟩ := hW x
    refine (hs' c j x ⟨hc, hj⟩).trans (Eq.trans ?_ (congrArg₂ (· * ·)
      (gm_div' M.B L.B (𝟙 X) x c c' hc hc') (hs' c' j x ⟨hc', hj⟩)).symm)
    rw [← gm_cocycle M.φ.isLB (𝟙 X) x hc.1 hc'.1 (ha j hj),
      ← gm_cocycle L.φ.isLB (𝟙 X) x hc.2 hc'.2 (hb j hj), key]
  · obtain ⟨j, hj⟩ := hW (under y)
    have hj' : y ∈ ptsIn p σ (W j) := mem_ptsIn.2 hj
    have hy : y ∈ ptsIn p σ (M.B.U a₀ ⊓ L.B.U b₀ ⊓ W j) := by simp [*]
    have e : logSq y _ (s (a₀, b₀)) = logSq y _ (M.B.g a₀ (a j)) + -logSq y _ (L.B.g b₀ (b j)) +
        logSq y _ (u j) := by
      rw [← logSq_res inf_le_left hy, hs (a₀, b₀) j]
      simp only [v, logSq_mul hy, logSq_inv hy, logSq_res _ hy]
    have e₁ : _ = _ - logSq y _ (M.B.g a₀ (a j)) := M.φ.trans a₀ (a j) y h₁ (ptsIn_mono (ha j) hj')
    have e₂ : _ = _ - logSq y _ (L.B.g b₀ (b j)) := L.φ.trans b₀ (b j) y h₂ (ptsIn_mono (hb j) hj')
    have e₃ := hφ j y hj'
    change _ = _ + logSq y _ (s (a₀, b₀))
    linarith

theorem isom_of_chart (a : L.B.ι → M.B.ι) (ha : ∀ j, L.B.U j ≤ M.B.U (a j))
    (hg : ∀ (x : X) j j', x ∈ L.B.U j → x ∈ L.B.U j' →
      gm (𝟙 X) x _ (L.B.g j j') = gm (𝟙 X) x _ (M.B.g (a j) (a j')))
    (hφ : ∀ j (y : CxPts p σ), y ∈ ptsIn p σ (L.B.U j) → M.φ.φ (a j) y = L.φ.φ j y) : L.Isom M :=
  isom_of_local L.B.U (exists_chart L.φ.isLB) a id ha (fun _ => le_rfl) (fun _ => 1)
    (fun x j j' h h' => by rw [map_one, map_one, ← hg x j j' h h', mul_one]; exact (mul_inv_cancel _).symm)
    fun j y h => by rw [logSq_one h, add_zero]; exact hφ j y h

theorem isom_refl (L : MLine p σ) : L.Isom L :=
  isom_of_chart id (fun _ => le_rfl) (fun _ _ _ _ _ => rfl) fun _ _ _ => rfl

theorem isom_pull (h : L.Isom M) (π : Y ⟶ X) (hπ : π ≫ p = q) :
    (L.pull π hπ).Isom (M.pull π hπ) := by
  obtain ⟨w, hw, h⟩ := h
  refine isom_of_local (fun c : M.B.ι × L.B.ι => π ⁻¹ᵁ (M.B.U c.1 ⊓ L.B.U c.2))
    (fun x => ?_) (fun c _ => c.1) (fun c _ => c.2) (fun _ _ h => mem_pull.2 h.1)
    (fun _ _ h => mem_pull.2 h.2) (fun c => pullU π _ (w.s (c.1, c.2))) (fun x c c' hc hc' => ?_)
    fun c y hy => ?_
  · obtain ⟨a, ha⟩ := exists_chart M.φ.isLB (π x)
    obtain ⟨b, hb⟩ := exists_chart L.φ.isLB (π x)
    exact ⟨(a, b), ha, hb⟩
  · refine Eq.trans ?_ (congrArg (· * _) (congrArg₂ (fun a b => a * b⁻¹)
      (gm_pull_g M.B π (𝟙 Y) x (fun _ => c.1) (fun _ => c'.1) (mem_pull.2 hc.1) (mem_pull.2 hc'.1))
      (gm_pull_g L.B π (𝟙 Y) x (fun _ => c.2) (fun _ => c'.2) (mem_pull.2 hc.2) (mem_pull.2 hc'.2)))).symm
    exact (gm_pull (U := M.B.U c.1 ⊓ L.B.U c.2) (𝟙 Y) π x hc (w.s (c.1, c.2))).trans
      ((gm_isGen hw (𝟙 Y ≫ π) x _ _ _ _ hc.1 hc'.1 hc.2 hc'.2).trans (congrArg (_ * ·)
        (gm_pull (U := M.B.U c'.1 ⊓ L.B.U c'.2) (𝟙 Y) π x hc' (w.s (c'.1, c'.2))).symm))
  · have hy' : PtsOver.map π hπ _ y ∈ ptsIn p σ (M.B.U c.1 ⊓ L.B.U c.2) := hy
    refine (M.φ.pull_φ π hπ _ y).trans ((h _ _ _ (mem_ptsIn_inf.1 hy').1 (mem_ptsIn_inf.1 hy').2).trans
      (congrArg₂ (· + ·) (L.φ.pull_φ π hπ (fun _ => c.2) y).symm ?_))
    exact congrArg (fun z => Real.log (‖z‖ ^ 2)) (ev_app π hπ _ _ y).symm

theorem isom_pull_tens (L M : MLine p σ) (π : Y ⟶ X) (hπ : π ≫ p = q) :
    ((L.tens M).pull π hπ).Isom ((L.pull π hπ).tens (M.pull π hπ)) :=
  isom_of_chart (fun j => (fun _ => (j PUnit.unit).1, fun _ => (j PUnit.unit).2))
    (fun _ _ h => ⟨mem_pull.2 (mem_pull.1 h).1, mem_pull.2 (mem_pull.1 h).2⟩)
    (fun x j j' h h' => by
      have e := mem_pull.1 h
      have e' := mem_pull.1 h'
      refine ((gm_pull_g (CechPic.tens L.B M.B) π (𝟙 Y) x j j' h h').trans
        (gm_tens L.B M.B (𝟙 Y ≫ π) x _ _ e e')).trans (Eq.symm ?_)
      exact (gm_tens (L.B.pull π) (M.B.pull π) (𝟙 Y) x (fun _ => (j PUnit.unit).1, fun _ => (j PUnit.unit).2)
        (fun _ => (j' PUnit.unit).1, fun _ => (j' PUnit.unit).2) ⟨mem_pull.2 e.1, mem_pull.2 e.2⟩
        ⟨mem_pull.2 e'.1, mem_pull.2 e'.2⟩).trans (congrArg₂ (· * ·)
          (gm_pull_g L.B π (𝟙 Y) x _ _ (mem_pull.2 e.1) (mem_pull.2 e'.1))
          (gm_pull_g M.B π (𝟙 Y) x _ _ (mem_pull.2 e.2) (mem_pull.2 e'.2))))
    fun j y _ => (congrArg₂ (· + ·) (L.φ.pull_φ π hπ _ y) (M.φ.pull_φ π hπ _ y)).trans
      ((L.tens M).φ.pull_φ π hπ j y).symm

theorem isom_pull_ofFun (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y) (π : Y ⟶ X) (hπ : π ≫ p = q)
    (hu' : ∀ z, CInfAt (fun z => u (ptMap π hπ σ z)) z) :
    ((MLine.ofFun u hu).pull π hπ).Isom (MLine.ofFun (fun z => u (ptMap π hπ σ z)) hu') :=
  isom_of_chart (fun _ => PUnit.unit) (fun _ => le_top)
    (fun x j j' h h' => (gm_pull_g (LB.triv X) π (𝟙 Y) x j j' h h').trans ((map_one _).trans (map_one _).symm))
    fun j y _ => ((MLine.ofFun u hu).φ.pull_φ π hπ j y).symm

theorem isom_addFn (L : MLine p σ) (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y) :
    (L.addFn u hu).Isom (L.tens (MLine.ofFun u hu)) :=
  isom_of_chart (fun c => (c, PUnit.unit)) (fun _ _ h => ⟨h, trivial⟩)
    (fun x c c' h h' => ((gm_tens L.B (LB.triv X) (𝟙 X) x (c, PUnit.unit) (c', PUnit.unit)
      ⟨h, trivial⟩ ⟨h', trivial⟩).trans ((congrArg (_ * ·) (map_one _)).trans (mul_one _))).symm)
    fun _ _ _ => rfl

theorem isom_pull_pull (L : MLine p σ) (π : Y ⟶ X) (hπ : π ≫ p = q) {Z : Scheme.{0}} {r : Z ⟶ Sp k} (i : Z ⟶ Y)
    (hi : i ≫ q = r) (h₀ : (i ≫ π) ≫ p = r) : ((L.pull π hπ).pull i hi).Isom (L.pull (i ≫ π) h₀) :=
  isom_of_chart (fun J => fun _ => J PUnit.unit PUnit.unit)
    (fun _ _ h => mem_pull₂.2 (mem_pull.1 (mem_pull.1 h)))
    (fun x (J J' : PUnit → PUnit → L.B.ι) h h' => by
      have e := mem_pull.1 h
      have e' := mem_pull.1 h'
      refine (gm_pull_g (L.B.pull π) i (𝟙 Z) x J J' h h').trans
        ((gm_pull_g L.B π (𝟙 Z ≫ i) x (J PUnit.unit) (J' PUnit.unit) e e').trans ?_)
      rw [Category.assoc]
      exact (gm_pull_g L.B (i ≫ π) (𝟙 Z) x (fun _ => J PUnit.unit PUnit.unit) (fun _ => J' PUnit.unit PUnit.unit)
        (mem_pull₂.2 (mem_pull.1 e)) (mem_pull₂.2 (mem_pull.1 e'))).symm)
    fun (J : PUnit → PUnit → L.B.ι) y _ => by
      refine (L.φ.pull_φ (i ≫ π) h₀ (fun _ => J PUnit.unit PUnit.unit) y).trans (Eq.trans ?_
        ((Weight.pull_φ (L.pull π hπ).φ i hi J y).trans (L.φ.pull_φ π hπ (J PUnit.unit) _)).symm)
      exact congrArg _ (Subtype.ext (by simp [PtsOver.map_val]))

end GlobalTheory.Mix.IsomCalc


open GlobalTheory.Mix.IsomCalc in
theorem GlobalTheory.Mix.isom_calculus : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (π : Y ⟶ X) (hπ : π ≫ p = q), (∀ A : MLine p σ, A.Isom A) ∧ (∀ A B : MLine p σ, A.Isom B → (A.pull π hπ).Isom (B.pull π hπ)) ∧ (∀ A B : MLine p σ, ((A.tens B).pull π hπ).Isom ((A.pull π hπ).tens (B.pull π hπ))) ∧ (∀ (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y), ((MLine.ofFun u hu).pull π hπ).Isom (MLine.ofFun (fun z => u (ptMap π hπ σ z)) fun z => (hu _).pull π hπ)) ∧ (∀ (A : MLine p σ) (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y), (A.addFn u hu).Isom (A.tens (MLine.ofFun u hu))) ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp k) (g : Z ⟶ Y) (hg : g ≫ q = r) (h : (g ≫ π) ≫ p = r) (A : MLine p σ), ((A.pull π hπ).pull g hg).Isom (A.pull (g ≫ π) h) :=
  fun _ _ _ _ _ _ _ π hπ => ⟨isom_refl, fun _ _ h => isom_pull h π hπ, fun A B => isom_pull_tens A B π hπ,
    fun u hu => isom_pull_ofFun u hu π hπ _, isom_addFn, fun _ _ g hg h A => isom_pull_pull A π hπ g hg h⟩
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp GlobalTheory.ChartGlue GlobalTheory.Points

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp.ChPow

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} {B : LB X}

theorem cHess_zero' (v : ReciprocityTheory.L2DbarEstimates.V D) :
    ReciprocityTheory.L2DbarEstimates.cHess D (fun _ => ((0 : ℝ) : ℂ)) v = 0 := by
  have h := ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul isOpen_univ (p := fun _ => (0 : ℝ)) (q := fun _ => (0 : ℝ))
    contDiffOn_const contDiffOn_const 1 (Set.mem_univ v)
  simp only [mul_zero, add_zero, Complex.ofReal_one, one_smul] at h
  simpa using h

theorem hess_pow {φ : Weight p σ B} (hφ : φ.IsCInf) (c : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source)
    (n : ℕ) {j : PUnit → B.ι} (hj : y ∈ ptsIn p σ (B.U (j PUnit.unit))) :
    c.hess (φ.pow n) j y = (n : ℂ) • c.hess φ (j PUnit.unit) y := by
  have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (B.U (j PUnit.unit)))
  have hm := mem_over c.e hy hj
  have e := ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul ho (p := fun _ => (0 : ℝ)) contDiffOn_const
    (contDiffOn_chart (hφ (j PUnit.unit)) c) (n : ℝ) hm
  rw [cHess_zero', zero_add] at e
  simp only [zero_add, Complex.ofReal_natCast] at e
  refine Eq.trans ?_ e
  show ReciprocityTheory.L2DbarEstimates.cHess D (fun v => (((φ.pow n).φ j (c.e.symm v) : ℝ) : ℂ)) (c.e y) = _
  congr 1
  funext v
  simp [Weight.pow, Weight.zpow_φ]

theorem chernDens_pow {φ : Weight p σ B} (hφ : φ.IsCInf) (c : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source)
    (n : ℕ) : c.chernDens (φ.pow n) y = (n : ℝ) ^ D * c.chernDens φ y := by
  have hj := (mem_pow_iff (n := (n : ℤ))).1 (mem_pick (φ.pow n).isLB y)
  rw [c.chernDens_eq hφ hy hj, AlgChart.chernDens, hess_pow hφ c hy n hj, Matrix.det_smul, Fintype.card_fin,
    ← Complex.ofReal_natCast, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
  ring

theorem chernPart_pow {φ : Weight p σ B} (hφ : φ.IsCInf) (n : ℕ) (ε : ℤˣ) :
    (φ.pow n).chernPart D ε = ENNReal.ofReal ((n : ℝ) ^ D) • φ.chernPart D ε := by
  have h := GlobalTheory.ChernScale.glueMeas_restrict_eq (fun c : AlgChart p σ D => c.e)
    (ρ := fun c y => ENNReal.ofReal ((ε : ℤ) * c.chernDens (φ.pow n) y))
    (ρ' := fun c y => ENNReal.ofReal ((ε : ℤ) * c.chernDens φ y)) ENNReal.ofReal_ne_top MeasurableSet.univ
    fun c y hy _ => by
      rw [chernDens_pow hφ c hy n, mul_left_comm, ENNReal.ofReal_mul (by positivity)]
  rw [Weight.chernPart, Weight.chernPart]
  simpa only [Measure.restrict_univ] using h

end GlobalTheory.HSAmp.ChPow

namespace GlobalTheory.HSAmp


open ChPow in
theorem chInt_pow : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∀ (L : HermLB p) (n : ℕ) (w : ∀ σ, CxPts p σ → ℝ), chInt (L.pow n) D w = (n : ℝ) ^ D * chInt L D w := by
  intro k _ X _ p D _ L n w
  rw [chInt, chInt, mul_finsum]
  refine finsum_congr fun σ => ?_
  show ((L.φ σ).pow n).chernInt D Set.univ (w σ) = _
  rw [Weight.chernInt, Weight.chernInt, chernPart_pow (L.cInf σ), chernPart_pow (L.cInf σ), Measure.restrict_smul,
    Measure.restrict_smul, integral_smul_measure, integral_smul_measure, ENNReal.toReal_ofReal (by positivity),
    smul_eq_mul, smul_eq_mul, mul_sub]

end GlobalTheory.HSAmp
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

namespace GlobalTheory.Mix

theorem exists_secPull_props : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (π : Y ⟶ X) (hπ : π ≫ p = q) (M : MLine p σ) (s : M.B.Sec), ∃ s' : (M.pull π hπ).B.Sec, nonzeroLocus s' = π ⁻¹ᵁ nonzeroLocus s ∧ (∀ y, (M.pull π hπ).φ.nsq (secVal q σ s') y = M.φ.nsq (secVal p σ s) (ptMap π hπ σ y)) ∧ ∀ [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y] (hη : π (genericPoint Y) ⤳ genericPoint X) (hs : genericPoint X ∈ nonzeroLocus s) (hs' : genericPoint Y ∈ nonzeroLocus s') (w : Y) (i : M.B.ι), π w ∈ M.B.U i → (divOfSec (M.pull π hπ).φ.isLB s' hs').mult w = Scheme.ord (TrueGeo.SmallSec.fnMap π hη (ratOfSec s hs i : X.functionField)) w := by
  intro k _ X Y p q σ π hπ M s
  refine ⟨GlobalTheory.Cartier.secPull s π, GlobalTheory.Cartier.nonzeroLocus_secPull s π, fun y =>
    Weight.nsq_pull_secPull M.φ π hπ s y, ?_⟩
  intro _ _ _ hη hs hs' w i hw
  have hc : w ∈ (M.B.pull π).U (fun _ => i) := by
    rw [GlobalTheory.Cartier.pull_U]; exact hw
  have hg : genericPoint Y ∈ (M.B.pull π).U (fun _ => i) := gen_mem hc
  have hg' : genericPoint Y ∈ π ⁻¹ᵁ M.B.U i := by
    have h := hg
    rw [GlobalTheory.Cartier.pull_U] at h
    exact h
  have h0 : genericPoint X ∈ M.B.U i := gen_mem hw
  have e : ((ratOfSec (L := (M.pull π hπ).B) (GlobalTheory.Cartier.secPull s π) hs' fun _ => i : Y.functionFieldˣ) :
      Y.functionField) = TrueGeo.SmallSec.fnMap π hη (ratOfSec s hs i : X.functionField) := by
    rw [val_ratOfSec h0, TrueGeo.SmallSec.fnMap_fnOf π hη h0 hg']
    exact (val_ratOfSec (L := M.B.pull π) (s := GlobalTheory.Cartier.secPull s π) (hs := hs') hg).trans
      (fnOf_resG (GlobalTheory.Cartier.pull_U M.B π fun _ => i).le hg _)
  exact ((presents_divOfRatSec _ _).isEqn (fun _ => i) w hc).mult_eq.trans (congrArg (Scheme.ord · w) e)

end GlobalTheory.Mix
end
end

section

open GlobalTheory.LKCount

theorem _root_.GlobalTheory.T.twistedCentralizerMass_ne_zero_of_mem_support : ∀ {G : Type} [Group G] (Γ' T K : Subgroup G) (F : G → ℂ), Γ' ≤ T → (∀ t ∈ T, ∀ x, ∀ k ∈ K, F (t * x * k) = F x) → (∀ x : G, ((Γ' ⊓ K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G).Finite) → {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) | F (Quotient.out q) ≠ 0}.Finite → ∀ y : G, F y ≠ 0 → massC Γ' T (T ⊓ K.map (MulAut.conj y).toMonoidHom) ≠ 0 := by
  first | exact @GlobalTheory.massC_ne_zero_of_support | exact GlobalTheory.massC_ne_zero_of_support | (intros; apply GlobalTheory.massC_ne_zero_of_support <;> assumption)
end

section

open scoped Classical

namespace GlobalTheory.FinTrace

noncomputable def dcToOrbit (G : Type) [Group G] (H K : Subgroup G) :
    DoubleCoset.Quotient (H : Set G) (K : Set G) → MulAction.orbitRel.Quotient H (G ⧸ K) :=
  Quotient.lift (fun g : G => (Quotient.mk _ (QuotientGroup.mk g : G ⧸ K) : MulAction.orbitRel.Quotient H (G ⧸ K)))
    (by
      intro a b hab
      obtain ⟨h, hh, k, hk, rfl⟩ := DoubleCoset.rel_iff.1 hab
      apply Quotient.sound
      show _ ∈ MulAction.orbit H _
      refine ⟨⟨h⁻¹, H.inv_mem hh⟩, ?_⟩
      show ((h⁻¹ : G) • (QuotientGroup.mk (h * a * k) : G ⧸ K)) = _
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
      simpa [mul_assoc] using hk)

theorem dcToOrbit_mk (G : Type) [Group G] (H K : Subgroup G) (g : G) :
    dcToOrbit G H K (Quotient.mk _ g) = Quotient.mk _ (QuotientGroup.mk g : G ⧸ K) := rfl

theorem dcToOrbit_bijective (G : Type) [Group G] (H K : Subgroup G) :
    Function.Bijective (dcToOrbit G H K) := by
  constructor
  · intro q₁ q₂ he
    induction q₁ using Quotient.inductionOn with | h a => ?_
    induction q₂ using Quotient.inductionOn with | h b => ?_
    rw [dcToOrbit_mk, dcToOrbit_mk] at he
    obtain ⟨h, hh⟩ := Quotient.exact he
    change ((h : G) • (QuotientGroup.mk b : G ⧸ K)) = _ at hh
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq] at hh
    apply Quotient.sound
    apply DoubleCoset.rel_iff.2
    refine ⟨(h : G)⁻¹, H.inv_mem h.2, ((h * b)⁻¹ * a)⁻¹, K.inv_mem hh, ?_⟩
    group
  · intro o
    induction o using Quotient.inductionOn with | h x => ?_
    induction x using QuotientGroup.induction_on with | H g => ?_
    exact ⟨Quotient.mk _ g, rfl⟩

theorem sum_doubleCoset_eq_sum_orbit : ∀ (G : Type) [Group G] (H K : Subgroup G) (F : G ⧸ K → ℂ), (∀ h : H, ∀ x : G ⧸ K, F (h • x) = F x) →
    ∑ᶠ q : DoubleCoset.Quotient (H : Set G) (K : Set G),
        (1 / (Nat.card (GlobalTheory.LKLoc.locPart H K (Quotient.out q)) : ℂ)) * F (QuotientGroup.mk (Quotient.out q)) =
      ∑ᶠ a : MulAction.orbitRel.Quotient H (G ⧸ K),
        (1 / (Nat.card (MulAction.stabilizer H (Quotient.out a)) : ℂ)) * F (Quotient.out a) := by
  intro G _ H K F hF
  let e := Equiv.ofBijective _ (dcToOrbit_bijective G H K)
  rw [← finsum_comp_equiv e]
  refine finsum_congr fun q => ?_
  have heq : e q = Quotient.mk _ (QuotientGroup.mk (Quotient.out q) : G ⧸ K) := by
    show dcToOrbit G H K q = _
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  have hrel : MulAction.orbitRel H (G ⧸ K) (Quotient.out (e q)) (QuotientGroup.mk (Quotient.out q)) := by
    apply Quotient.exact
    rw [Quotient.out_eq, heq]
  obtain ⟨h, hh⟩ := hrel
  rw [← hh, hF]
  congr 2
  have h1 := Nat.card_congr (Classical.choice (stabilizer_equiv_locPart G H K (Quotient.out q)))
  rw [← h1]
  exact_mod_cast (Nat.card_congr (MulAction.stabilizerEquivStabilizerOfOrbitRel (G := H) (a := h • (QuotientGroup.mk (Quotient.out q) : G ⧸ K))
    (b := (QuotientGroup.mk (Quotient.out q) : G ⧸ K)) (MulAction.orbitRel_apply.2 ⟨h, rfl⟩)).toEquiv).symm
end GlobalTheory.FinTrace
end

section

open GlobalTheory.LKCount

theorem _root_.GlobalTheory.T.twistedCentralizerMass_map_conj : ∀ {G : Type} [Group G] (Γ' T C : Subgroup G) (t : G), t ∈ T → C ≤ T → massC Γ' T (C.map (MulAut.conj t).toMonoidHom) = massC Γ' T C := by
  first | exact @GlobalTheory.LKCount.massC_map_conj | exact GlobalTheory.LKCount.massC_map_conj | (intros; apply GlobalTheory.LKCount.massC_map_conj <;> assumption)
end
