module

public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle020
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle015
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle011
public import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle021
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle017
import Formalism.LocalToGlobal.ProjectiveLattices.ThetaFramePf
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle008
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MeanSquareMultipleThetaSectionFamily
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.LevelFrameOfLaws
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle004
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem _root_.GlobalTheory.T.lift_baseChange_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (R : Type) [CommRing R] [Algebra c.F R] (f : Γ(Y.X, M.U) →+* R) (x : Sp R ⟶ Xo.X) (Λ : M.Lift f x), ∀ (S : Type) [CommRing S] [Algebra c.F S] (ψ : R →ₐ[c.F] S), ∃ Λ' : M.Lift (ψ.toRingHom.comp f) (spMap ψ.toRingHom ≫ x), (∀ cv w, Λ.Vec cv w → Λ'.Vec (fun j => ψ (cv j)) (spMap (dualMap ψ.toRingHom) ≫ w)) ∧ ∀ (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx (spMap ψ.toRingHom ≫ x))) (pm : Gx (spMap ψ.toRingHom ≫ x) ⟶ Gx x), pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk (spMap ψ.toRingHom ≫ x)) Xo.univ.t.G).left → pm ≫ (fst (Over.mk x) Xo.univ.t.G).left = (fst (Over.mk (spMap ψ.toRingHom ≫ x)) Xo.univ.t.G).left ≫ spMap ψ.toRingHom → (∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx (spMap ψ.toRingHom ≫ x)).U i ≤ pm ⁻¹ᵁ (PPx x).U i), (pm.appLE _ _ h).hom (s.f i) = s'.f i) → Λ.ThTie s → Λ'.ThTie s' := by
  first | exact @GlobalTheory.lift_baseChange | exact GlobalTheory.lift_baseChange | (intros; apply GlobalTheory.lift_baseChange <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem _root_.GlobalTheory.T.modelChartLift_coords_generator_indep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (R : Type) [CommRing R] [Algebra c.F R] (f : Γ(Y.X, M.U) →+* R) (x : Sp R ⟶ Xo.X) (Λ : M.Lift f x), ∀ Λ' : M.Lift f x, (∀ cv w, Λ.Vec cv w → Λ'.Vec cv w) ∧ ∀ s, Λ.ThTie s → Λ'.ThTie s := by
  first | exact @GlobalTheory.Reg.LiftUnique.lift_indep | exact GlobalTheory.Reg.LiftUnique.lift_indep | (intros; apply GlobalTheory.Reg.LiftUnique.lift_indep <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg

theorem exists_frPt_tie : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (R : Type) [CommRing R] [Algebra c.F R] (f : Γ(Y.X, M.U) →+* R) (x : Sp R ⟶ Xo.X) (Λ : M.Lift f x), ∀ u : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) R, (∀ τ i, M.Eig f τ (fun j => u τ j i)) → (∀ τ cv, M.Eig f τ cv → ∃! a : Fin (Dw.mult τ) → R, (u τ).mulVec a = cv) → ∃ y : FrPt Xo c R, y.x = x ∧ M.Comparison₂ f u y := by
  intro hT E _ _ _ H Dw l Xo c O _ β Y M R _ _ f x Λ u hu huniq
  have hover : x ≫ Xo.s = sOf c R := by
    rw [← Λ.xF_fst, Category.assoc, pullback.condition, ← Category.assoc, Λ.xF_snd]
    unfold sOf spMap
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  have hV := GlobalTheory.T.lieBasis_coordinates_bijective_tangent E H Dw l Xo c O β Y M R f x Λ
  choose w hw _ using fun τ (i : Fin (Dw.mult τ)) => hV.1 (fun j => u τ j i)
  obtain ⟨s, hs, hgen⟩ := GlobalTheory.T.exists_chart_generator_pullback_generates_fibre hT E H Dw l Xo c O β Y M R f x Λ
  refine ⟨⟨x, hover, w, fun τ i => hV.2.1 _ _ (hw τ i),
    fun τ i => (GlobalTheory.T.isEigenvector_iff_lieBasis_coordinates E H Dw l Xo c O β Y M R f x Λ τ _ _ (hw τ i)).2 (hu τ i), ?_, s, hgen⟩,
    rfl, Λ, fun τ i => hw τ i, hs⟩
  intro τ v hvt hve
  obtain ⟨cv, hcv, hcvu⟩ := hV.2.2 v hvt
  have hcomb : ∀ a, IsCombAt x (w τ) a v ↔ Λ.Vec ((u τ).mulVec a) v := by
    intro a
    have hsum : (∑ i, a i • fun j => u τ j i) = (u τ).mulVec a := by
      funext j
      simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
    rw [GlobalTheory.T.isCombAt_iff_coordinate_combination E H Dw l Xo c O β Y M R f x Λ _ (fun i j => u τ j i) (w τ) a v (hw τ), hsum]
  have hcve : M.Eig f τ cv := (GlobalTheory.T.isEigenvector_iff_lieBasis_coordinates E H Dw l Xo c O β Y M R f x Λ τ cv v hcv).1 hve
  obtain ⟨a, ha, hau⟩ := huniq τ cv hcve
  refine ⟨a, (hcomb a).2 (ha ▸ hcv), fun a' ha' => hau a' ?_⟩
  exact hcvu _ ((hcomb a').1 ha')

end GlobalTheory.Reg
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg.TieIntegral


open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1 IsLocalRing in
theorem generates_of_generic_line {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type}
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (G : SAB H (Sp V)) {t' : SAB H (Sp (FractionRing V))}
    (m2 : SABMap t' G (spMap (algebraMap V (FractionRing V)))) (b : LB.Sec t'.PP.L)
    (hb : ∀ s : LB.Sec t'.PP.L, ∃! a : FractionRing V, ∀ i, s.f i = constFn t'.G.hom _ a * b.f i)
    (θ : LB.Sec G.PP.L)
    (hne : ∃ (g : G.G.left) (i : G.PP.L.ι), G.G.hom g = closedPoint V ∧ g ∈ G.G.left.basicOpen (θ.f i)) :
    ∀ σ : LB.Sec G.PP.L, ∃! a : V, ∀ i, σ.f i = constFn G.G.hom _ a * θ.f i := by
  have := G.semi.smooth
  obtain ⟨g, k₀, hg₂, hb₀⟩ := hne
  have hk₀ : g ∈ G.PP.L.U k₀ := G.G.left.basicOpen_le _ hb₀
  have un : IsUnit (gs (𝟙 _) g _ (θ.f k₀)) := by
    rw [gs_eq (𝟙 _) g _ hk₀]; exact (G.G.left.mem_basicOpen _ _ hk₀).1 hb₀
  obtain ⟨w2, g2, -⟩ := m2.lin
  have down := sec_pull_down ((isGen_iff w2).1 g2) G.PP.isLB t'.PP.isLB
  obtain ⟨σ', hσ'⟩ := down θ
  have : IsDominant (spMap (algebraMap V (FractionRing V))) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V (FractionRing V))).le.trans bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (spMap (algebraMap V (FractionRing V)))
  have : IsSchemeTheoreticallyDominant m2.φ := IsSchemeTheoreticallyDominant.of_isPullback m2.cart.1.flip
  have : QuasiCompact m2.φ := MorphismProperty.of_isPullback (P := @QuasiCompact) m2.cart.1.flip inferInstance

  have inj : ∀ (σ τ σK τK : _) (r : V), (∀ (Z : Scheme.{0}) (q : Z ⟶ t'.G.left) (y : Z) j k, m2.φ (q y) ∈ G.PP.L.U j →
      q y ∈ t'.PP.L.U k → gs (q ≫ m2.φ) y _ (LB.Sec.f σ j) = (gw w2 q y j k).val * gs q y _ (LB.Sec.f σK k)) →
      (∀ (Z : Scheme.{0}) (q : Z ⟶ t'.G.left) (y : Z) j k, m2.φ (q y) ∈ G.PP.L.U j →
      q y ∈ t'.PP.L.U k → gs (q ≫ m2.φ) y _ (LB.Sec.f τ j) = (gw w2 q y j k).val * gs q y _ (LB.Sec.f τK k)) →
      (∀ k, LB.Sec.f σK k = constFn t'.G.hom _ (algebraMap V _ r) * LB.Sec.f τK k) →
      ∀ j, LB.Sec.f σ j = constFn G.G.hom _ r * LB.Sec.f τ j := by
    intro σ τ σK τK r h₁ h₂ h₃ j
    refine m2.φ.app_injective _ (fn_ext fun y hy => ?_)
    obtain ⟨k, hk⟩ := exists_chart t'.PP.isLB y
    refine (gs_pull (𝟙 _) m2.φ y _ hy _).trans (Eq.trans ?_ (gs_pull (𝟙 _) m2.φ y _ hy _).symm)
    rw [gs_mul (𝟙 _ ≫ m2.φ) y _ hy, gs_constFn _ _ (𝟙 _ ≫ m2.φ) y hy, h₁ _ (𝟙 _) y j k hy hk, h₂ _ (𝟙 _) y j k hy hk, (sec_eq_iff _ _ _ _).1 h₃ k y hk,
      Category.id_comp, m2.cart.1.w, cst_comp, mul_left_comm]
  have mulc : ∀ {s t u : LB.Sec t'.PP.L} {a a' : FractionRing V}, (∀ k, s.f k = constFn t'.G.hom _ a * t.f k) →
      (∀ k, t.f k = constFn t'.G.hom _ a' * u.f k) → ∀ k, s.f k = constFn t'.G.hom _ (a * a') * u.f k :=
    fun h h' => (sec_eq_iff _ _ _ _).2 fun k y hy => by
      rw [(sec_eq_iff _ _ _ _).1 h k y hy, (sec_eq_iff _ _ _ _).1 h' k y hy, cst_mul, _root_.mul_assoc]
  have invc : ∀ {s t : LB.Sec t'.PP.L} {a : FractionRing V}, a ≠ 0 → (∀ k, s.f k = constFn t'.G.hom _ a * t.f k) →
      ∀ k, t.f k = constFn t'.G.hom _ a⁻¹ * s.f k := fun ha h => (sec_eq_iff _ _ _ _).2 fun k y hy => by
    rw [(sec_eq_iff _ _ _ _).1 h k y hy, ← _root_.mul_assoc, ← cst_mul, inv_mul_cancel₀ ha, cst_one, _root_.one_mul]
  have unit : ∀ (σ : LB.Sec G.PP.L) (r : V), (∀ j, θ.f j = constFn G.G.hom _ r * σ.f j) → IsUnit r := fun σ r h => by
    by_contra hr
    rw [(sec_eq_iff _ _ _ _).1 h k₀ g hk₀] at un
    exact cst_not_isUnit G.G.hom g hg₂ hr (isUnit_of_mul_isUnit_left un)
  obtain ⟨a₀, ha₀, -⟩ := hb σ'
  have h₀ : a₀ ≠ 0 := fun h => not_isUnit_zero (unit θ 0 (inj θ θ σ' σ' 0 hσ' hσ' ((sec_eq_iff _ _ _ _).2 fun k y hy => by
    rw [(sec_eq_iff _ _ _ _).1 ha₀ k y hy, h, map_zero, ← _root_.mul_assoc, ← cst_mul, mul_zero])))
  have gen : ∀ s' : LB.Sec t'.PP.L, ∃! a : FractionRing V, ∀ i, s'.f i = constFn t'.G.hom _ a * σ'.f i := fun s' => by
    obtain ⟨a, ha, hu⟩ := hb s'
    refine ⟨a * a₀⁻¹, mulc ha (invc h₀ ha₀), fun a' ha' => ?_⟩
    rw [← hu _ (mulc ha' ha₀), mul_inv_cancel_right₀ h₀]
  intro σ
  · obtain ⟨σK, hσK⟩ := down σ
    obtain ⟨a, ha, -⟩ := gen σK
    have ex : ∃ r : V, ∀ i, σ.f i = constFn G.G.hom _ r * θ.f i := by
      by_cases h : IsLocalization.IsInteger V a
      · obtain ⟨r, rfl⟩ := h
        exact ⟨r, inj σ θ σK σ' r hσK hσ' ha⟩
      · have hne : a ≠ 0 := fun e => h (e ▸ IsLocalization.isInteger_zero)
        obtain ⟨r, hr⟩ := (ValuationRing.isInteger_or_isInteger V a).resolve_left h
        obtain ⟨u, rfl⟩ := unit σ r (inj θ σ σ' σK r hσ' hσK (hr ▸ invc hne ha))
        exact absurd ⟨(u⁻¹ : Vˣ), by rw [← inv_inv a, ← hr, map_units_inv]⟩ h
    obtain ⟨r, hr⟩ := ex
    refine ⟨r, hr, fun r' hr' => ?_⟩
    by_contra hne
    have e : cst G.G.hom g (r' - r) * gs (𝟙 _) g _ (θ.f k₀) = cst G.G.hom g (r' - r) * 0 := by
      rw [cst_sub, sub_mul, ← (sec_eq_iff _ _ _ _).1 hr' k₀ g hk₀, ← (sec_eq_iff _ _ _ _).1 hr k₀ g hk₀, sub_self, mul_zero]
    exact un.ne_zero (cst_regular G.G.hom g (sub_ne_zero.2 hne) e)

end GlobalTheory.Reg.TieIntegral

namespace GlobalTheory.Reg


open TieIntegral in
theorem exists_generator_of_thTie_free :
    ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (T : CDVR) (io : c.F →+* T.Fr) (f₀ : Γ(Y.X, M.U) →+* T.V), letI := io.toAlgebra; ∀ (x : Sp T.Fr ⟶ Xo.X) (s : LB.Sec (PPx x)) (Λ : M.Lift ((algebraMap T.V T.Fr).comp f₀) x), Λ.ThTie s → ∀ (G : SAB H (Sp T.V)) (m : SABMap G Y.t (spMap f₀ ≫ M.hU.fromSpec)) (m2 : SABMap Λ.t' G (spMap (algebraMap T.V T.Fr))), m2.φ ≫ m.φ = Λ.m2.φ → ∃ θ : LB.Sec G.PP.L, (∀ σ : LB.Sec G.PP.L, ∃! a : T.V, ∀ i, σ.f i = resG G.G.left (le_top : G.PP.L.U i ≤ ⊤) ((G.G.hom).appTop.hom (toΓ T.V a)) * θ.f i) ∧ ∃ (w1 : LB.Iso Λ.t'.PP.L (Xo.univ.t.PP.L.pull Λ.m1.φ)) (w2 : LB.Iso Λ.t'.PP.L (G.PP.L.pull m2.φ)) (σ : LB.Sec Λ.t'.PP.L) (s1 : LB.Sec (Xo.univ.t.PP.L.pull Λ.m1.φ)) (θ2 : LB.Sec (G.PP.L.pull m2.φ)), RigIso Λ.m1 w1 ∧ RigIso m2 w2 ∧ IsoMaps w1 σ s1 ∧ IsoMaps w2 σ θ2 ∧ PullSec m2.φ θ θ2 ∧ ∀ g : Λ.t'.G.left ⟶ Gx x, g ≫ (snd (Over.mk x) Xo.univ.t.G).left = Λ.m1.φ → g ≫ (fst (Over.mk x) Xo.univ.t.G).left = Λ.t'.G.hom → ∀ j (h : (Xo.univ.t.PP.L.pull Λ.m1.φ).U j ≤ g ⁻¹ᵁ (PPx x).U (fun _ => j PUnit.unit)), s1.f j = (g.appLE _ _ h).hom (s.f (fun _ => j PUnit.unit)) := by
  intro hT E _ _ _ H Dw l Xo c O _ β Y M T io f₀
  let _ := io.toAlgebra
  intro x s Λ hTie G m m2 hφ
  obtain ⟨w1, wΛ, σ, s1, r1, rΛ, hI1, hform, hg⟩ := hTie
  have hcomp : spMap ((algebraMap T.V T.Fr).comp f₀) = spMap (algebraMap T.V T.Fr) ≫ spMap f₀ := by
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  obtain ⟨b, hb⟩ := globalSections_rank_one_fibre hT amplePt Y.oF Λ.m'
  have hU : ⊤ ≤ (spMap f₀ ≫ M.hU.fromSpec) ⁻¹ᵁ M.U := fun y _ => by
    have : M.hU.fromSpec (spMap f₀ y) ∈ Set.range M.hU.fromSpec := ⟨_, rfl⟩
    rw [M.hU.range_fromSpec] at this
    exact this
  obtain ⟨w, θ, rw', hθ, hne⟩ := exists_sec_pull_nonzero_on_fibres E H _ _ Y.t G _ m M.U hU M.θ M.θ_mem M.θ_ne
  have hgen := generates_of_generic_line G m2 b hb θ (hne _)
  have he : Λ.m2.cm.e = m2.cm.e ≫ m.cm.e := by
    rw [Λ.m2.base, m2.base, m.base, hcomp]; exact Category.assoc _ _ _
  obtain ⟨w2, r2, tri⟩ := exists_rigIso_cancel m.cm m2.cm Λ.m2.cm hφ.symm he Λ.t'.PP G.PP Y.t.PP w wΛ rw' rΛ
  refine ⟨θ, hgen, w1, w2, σ, s1, thfPull G.PP.L m2.φ θ, r1, r2, hI1,
    fun (i : PUnit → G.PP.L.ι) k => fn_ext fun y hy => ?_, fun j hj => rfl, hg⟩
  have hi : m2.φ y ∈ G.PP.L.U (i PUnit.unit) := mem_pull.1 hy.1
  obtain ⟨j, hj⟩ := exists_chart Y.t.PP.isLB (m.φ (m2.φ y))
  have hyU : m.φ (m2.φ y) ∈ Y.t.G.hom ⁻¹ᵁ M.U := (congrArg (fun q => q (m2.φ y) ∈ M.U) m.cart.1.w).mpr
    (hU (show G.G.hom (m2.φ y) ∈ (⊤ : (Sp T.V).Opens) from trivial))
  have pt : Λ.m2.φ y = m.φ (m2.φ y) := congrArg (fun q => q y) hφ.symm
  have e1 := gs_of_formula w _ M.θ θ hθ (𝟙 _ ≫ m2.φ) y j (i PUnit.unit) hyU hj hi
  have e2 := gs_of_formula wΛ _ M.θ σ hform (𝟙 _) y j k (pt ▸ hyU) (pt ▸ hj) hy.2
  have e3 := tri _ (𝟙 _) y j (i PUnit.unit) k hj hi hy.2
  have e4 : (𝟙 _ ≫ m2.φ) ≫ m.φ = 𝟙 _ ≫ Λ.m2.φ := by rw [Category.assoc, hφ]
  rw [e4, e2, e3, Units.val_mul, _root_.mul_assoc, Units.mul_right_inj] at e1
  refine (gs_res _ y _ hy _).trans ((gs_appLE m2.φ _ _ _ (𝟙 _) y hy.1 _).trans (e1.symm.trans ?_))
  refine Eq.symm ((gs_mul _ y _ hy _ _).trans ?_)
  exact congrArg₂ (· * ·) (gs_unit _ y _ hy _) (gs_res _ y _ hy _)

end GlobalTheory.Reg
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem _root_.GlobalTheory.T.exists_integralGenerator_of_chartPoint_cdvr : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), PushInvertible Y.t.G Y.t.PP.L → ∀ (T : CDVR) (io : c.F →+* T.Fr) (f₀ : Γ(Y.X, M.U) →+* T.V), letI := io.toAlgebra; ∀ (x : Sp T.Fr ⟶ Xo.X) (s : LB.Sec (PPx x)) (Λ : M.Lift ((algebraMap T.V T.Fr).comp f₀) x), Λ.ThTie s → ∀ (G : SAB H (Sp T.V)) (m : SABMap G Y.t (spMap f₀ ≫ M.hU.fromSpec)) (m2 : SABMap Λ.t' G (spMap (algebraMap T.V T.Fr))), m2.φ ≫ m.φ = Λ.m2.φ → ∃ θ : LB.Sec G.PP.L, (∀ σ : LB.Sec G.PP.L, ∃! a : T.V, ∀ i, σ.f i = resG G.G.left (le_top : G.PP.L.U i ≤ ⊤) ((G.G.hom).appTop.hom (toΓ T.V a)) * θ.f i) ∧ ∃ (w1 : LB.Iso Λ.t'.PP.L (Xo.univ.t.PP.L.pull Λ.m1.φ)) (w2 : LB.Iso Λ.t'.PP.L (G.PP.L.pull m2.φ)) (σ : LB.Sec Λ.t'.PP.L) (s1 : LB.Sec (Xo.univ.t.PP.L.pull Λ.m1.φ)) (θ2 : LB.Sec (G.PP.L.pull m2.φ)), RigIso Λ.m1 w1 ∧ RigIso m2 w2 ∧ IsoMaps w1 σ s1 ∧ IsoMaps w2 σ θ2 ∧ PullSec m2.φ θ θ2 ∧ ∀ g : Λ.t'.G.left ⟶ Gx x, g ≫ (snd (Over.mk x) Xo.univ.t.G).left = Λ.m1.φ → g ≫ (fst (Over.mk x) Xo.univ.t.G).left = Λ.t'.G.hom → ∀ j (h : (Xo.univ.t.PP.L.pull Λ.m1.φ).U j ≤ g ⁻¹ᵁ (PPx x).U (fun _ => j PUnit.unit)), s1.f j = (g.appLE _ _ h).hom (s.f (fun _ => j PUnit.unit)) := by
  first | exact @GlobalTheory.Reg.exists_generator_of_thTie | exact GlobalTheory.Reg.exists_generator_of_thTie | (intros; apply GlobalTheory.Reg.exists_generator_of_thTie <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif GlobalTheory.FrameNorm
open scoped Matrix nonZeroDivisors

theorem _root_.GlobalTheory.T.meanSquare_multiple_thetaSection_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ' ty) (k : Fin F.n) (m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → ((F.Di k).La →+ (Fin g → ℂ))) (fr : Xo.univ.t.PP.L.ι → (Fin m → ℂ) × (Fin g → ℂ) → ℂ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (F.Di k).La) (b : Fin m → ℂ) (h τ : Matrix (Fin g) (Fin g) ℂ) (c₁ c₂ : Fin g → ℂ) (x : Sp ℂ ⟶ Xo.X) (s : LB.Sec (PPx x)) (κ : ℂ), b ∈ B → IsPeriod (F.Di k) ty (P b) → (∀ v w, (F.Di k).EF (bas v) (bas w) = -omegaStd v w) → IsUnit h.det → τ.IsSymm → (τ.map Complex.im).PosDef → (∀ i, h *ᵥ P b (bas (Pi.single (Sum.inl i) 1)) = Pi.single i 1 ∧ h *ᵥ P b (bas (Pi.single (Sum.inr i) 1)) = τ *ᵥ Pi.single i 1) → (∀ i, c₁ i = 0 ∨ c₁ i = 1 / 2) → (∀ i, c₂ i = 0 ∨ c₂ i = 1 / 2) → RigFrame F k B P fr → x = F.u k (P b) → κ ≠ 0 → SecVal F k (P b) x s (fun z => κ * thetaChar τ c₁ c₂ (h *ᵥ z)) (fun j z => fr j (b, z)) → AHMean F k (P b) x s (‖κ‖ ^ 2 * (Real.sqrt (2 ^ g * (τ.map Complex.im).det))⁻¹) := by
  first | exact @GlobalTheory.FrameNorm.ahMean_of_secVal_thetaChar | exact GlobalTheory.FrameNorm.ahMean_of_secVal_thetaChar | (intros; apply GlobalTheory.FrameNorm.ahMean_of_secVal_thetaChar <;> assumption)
end
