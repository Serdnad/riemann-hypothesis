module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1203
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle041
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionValuesCoordsOperatorPermute
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1220
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1215
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1235
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1238
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.EtaleKlt

theorem isFreeGen_formMap_of_formallyEtale {k A B : Type*} [CommRing k] [CommRing A] [CommRing B]
    {α : k →+* A} {β : k →+* B} {D : ℕ} {ρ : A →+* B} (hρ : ρ.FormallyEtale) (h : ρ.comp α = β)
    {ω : Forms α D} (hω : IsFreeGen A ω) : IsFreeGen B (TopForm.formMap D ρ h ω) := by
  letI := α.toAlgebra
  letI := β.toAlgebra
  letI := ρ.toAlgebra
  haveI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq' h.symm
  haveI : Algebra.FormallyEtale A B := hρ
  exact hω.of_isBaseChange (isBaseChange_exteriorPower
    (KaehlerDifferential.isBaseChange_of_formallyEtale k A B) D)

theorem formOrd_ratPull (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (p : W ⟶ Sp ℂ)
    (f : M ⟶ W) [IsDominant f] (n : ℕ) [LocallyOfFiniteType p]
    (hn : topologicalKrullDim W = n) (E : DivOver p) (E' : DivOver (f ≫ p))
    (h : ∀ x ∈ E.ring, functionFieldMap f x ∈ E'.ring)
    (hρ : ((functionFieldMap f).restrict E.ring E'.ring h).FormallyEtale)
    (hord : ∀ g : W.functionFieldˣ,
      E'.ord (Units.map (functionFieldMap f).toMonoidHom g) = E.ord g)
    (η : RatForms p n) (hη : η ≠ 0) :
    (fun ω => @dite ℤ (∃ a, E'.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (GlobalTheory.EtaleKlt.ratPull p f n η) = (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) η := by
  set φ := functionFieldMap f with hφ
  set ρ := φ.restrict E.ring E'.ring h with hρdef
  obtain ⟨ω, hω, g, hη', hg⟩ := E.isFormOrd_formOrd hn hη
  have hc : ρ.comp E.const = E'.const := by
    ext a
    exact RingHom.congr_fun (functionFieldMap_comp_constFn p f) a
  have hω' : IsFreeGen E'.ring (TopForm.formMap n ρ hc ω) := isFreeGen_formMap_of_formallyEtale hρ hc hω
  have e : φ.comp E.ring.subtype = E'.ring.subtype.comp ρ := by
    ext x
    rfl
  have hτ : (E'.ring.subtype.comp ρ).comp E.const = Cartier.constFn (f ≫ p) := by
    rw [RingHom.comp_assoc, hc]
    rfl
  have key : ratPull p f n (E.toRat n ω) = E'.toRat n (TopForm.formMap n ρ hc ω) := by
    have k1 := TopForm.formMap_formMap (D := n) E.ring.subtype φ _ e rfl
      (functionFieldMap_comp_constFn p f) hτ ω
    have k2 := TopForm.formMap_formMap (D := n) ρ E'.ring.subtype _ rfl hc rfl hτ ω
    exact k1.trans k2.symm
  have hpull : ratPull p f n η = φ (g : W.functionField) • E'.toRat n (TopForm.formMap n ρ hc ω) := by
    rw [hη', map_smulₛₗ, key]
  have hne : ratPull p f n η ≠ 0 := by
    rw [hpull]
    intro h0
    have hinj := (E'.isFreeGen_toRat hω').1
    have : φ (g : W.functionField) = 0 := hinj (by simpa using h0)
    exact (g.map φ.toMonoidHom).ne_zero this
  change E'.formOrd (ratPull p f n η) = E.formOrd η
  rw [← hg]
  refine DivOver.IsFormOrd.formOrd_eq hne ⟨_, hω', Units.map φ.toMonoidHom g, hpull, hord g⟩

end GlobalTheory.EtaleKlt
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.TanGauge

noncomputable section
namespace GlobalTheory.MBLow.TanGauge

theorem valHom_res_pullU_zpow {X Y : Scheme.{0}} {A : Type} [CommRing A] (y : Sp A ⟶ Y) (f : Y ⟶ X)
    (U : X.Opens) {V : Y.Opens} (e : V ≤ f ⁻¹ᵁ U) (hV : ⊤ ≤ y ⁻¹ᵁ V) (u : Γ(X, U)ˣ) (n : ℤ) :
    GlobalTheory.ZH.CrdCalc.valHom y V hV ((res e (pullU f U u)) ^ n : Γ(Y, V)ˣ).val = valR (y ≫ f) U (u ^ n).val := by
  rw [← map_zpow, ← map_zpow, ← GlobalTheory.ZH.CrdCalc.valR_eq y V hV]
  have hU : ⊤ ≤ y ⁻¹ᵁ f ⁻¹ᵁ U := hV.trans (y.preimage_mono e)
  refine (GlobalTheory.ZH.CrdCalc.valR_res y e hV _).trans ?_
  exact GlobalTheory.ZH.EvCrd.valR_comp y f U hU _

theorem valR_linComb_sec : ∀ {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (s : LB.Sec (LB.LinComb L φ ε)) {A : Type} [CommRing A] (y : Sp A ⟶ Y) (j j' : K → L.ι),
    ⊤ ≤ y ⁻¹ᵁ LB.wchart L φ j → ⊤ ≤ y ⁻¹ᵁ LB.wchart L φ j' →
    valR y (LB.wchart L φ j) (s.f j) =
      (∏ k, trV L (y ≫ φ k) (j k) (j' k) (ε k)) * valR y (LB.wchart L φ j') (s.f j') := by
  intro X Y L K _ φ ε s A _ y j j' h h'
  have hh : ⊤ ≤ y ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ j') := fun q hq => ⟨h hq, h' hq⟩
  have e1 := GlobalTheory.ZH.CrdCalc.valR_res y
    (inf_le_left : LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ LB.wchart L φ j) hh (s.f j)
  have e2 := GlobalTheory.ZH.CrdCalc.valR_res y
    (inf_le_right : LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ LB.wchart L φ j') hh (s.f j')
  rw [← e1, ← e2]
  have c := s.compat j j'
  change valR y _ ((Y.presheaf.map _).hom _) = _ * valR y _ ((Y.presheaf.map _).hom _)
  refine (congrArg (valR y (LB.wchart L φ j ⊓ LB.wchart L φ j')) c).trans ?_
  refine (GlobalTheory.ZH.CrdCalc.valR_mul y (LB.wchart L φ j ⊓ LB.wchart L φ j') hh _ _).trans ?_
  congr 1
  refine (GlobalTheory.ZH.CrdCalc.valR_eq y (LB.wchart L φ j ⊓ LB.wchart L φ j') hh _).trans ?_
  dsimp only [LB.LinComb]
  rw [Units.coe_prod, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  have hk : ⊤ ≤ (y ≫ φ k) ⁻¹ᵁ (L.U (j k) ⊓ L.U (j' k)) := fun q _ =>
    ⟨wchart_top_le L φ j y h k (x := q) trivial, wchart_top_le L φ j' y h' k (x := q) trivial⟩
  unfold trV
  exact valHom_res_pullU_zpow y (φ k) (L.U (j k) ⊓ L.U (j' k)) (V := LB.wchart L φ j ⊓ LB.wchart L φ j') _ hh
    (L.g (j k) (j' k)) (ε k)

end GlobalTheory.MBLow.TanGauge
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

namespace GlobalTheory.MBLow.Cl.FJD

open GlobalTheory.MBLow.Cl.FJ

theorem deriv_line {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : E → ℂ} (hf : Differentiable ℂ f) (Z W : E) :
    deriv (fun s : ℂ => f (Z + s • W)) 0 = fderiv ℂ f Z W := by
  have h1 : HasDerivAt (fun s : ℂ => Z + s • W) W 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const W).const_add Z
  have h2 : HasFDerivAt f (fderiv ℂ f Z) (Z + (0 : ℂ) • W) := by
    simpa using (hf Z).hasFDerivAt
  exact (h2.comp_hasDerivAt (0 : ℂ) h1).deriv

theorem termwise {J E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : J → E → ℂ} {F : E → ℂ}
    (hf : ∀ i, Differentiable ℂ (f i)) (hF : Differentiable ℂ F) (hs : ∀ Z, ∑' i, f i Z = F Z) (Z W : E)
    {u : J → ℝ} (hu : Summable u) (hb : ∀ i (s : ℂ), ‖s‖ ≤ 2 → ‖f i (Z + s • W)‖ ≤ u i) :
    (Summable fun i => ‖fderiv ℂ (f i) Z W‖) ∧ ∑' i, fderiv ℂ (f i) Z W = fderiv ℂ F Z W := by
  have hl : Differentiable ℂ (fun s : ℂ => Z + s • W) := by fun_prop
  have hd : ∀ i, Differentiable ℂ (fun s : ℂ => f i (Z + s • W)) := fun i => (hf i).comp hl
  refine ⟨hu.of_nonneg_of_le (fun _ => norm_nonneg _) fun i => ?_, ?_⟩
  · rw [← deriv_line (hf i)]
    have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := 0) (R := 1) (C := u i) one_pos
      (hd i).diffContOnCl (fun s hs => hb i s (by
        have : ‖s‖ = 1 := by simpa using hs
        linarith))
    simpa using this
  · have h := Complex.hasSum_deriv_of_summable_norm (U := Metric.ball (0 : ℂ) 2) (z := 0)
      (F := fun i s => f i (Z + s • W)) hu (fun i => (hd i).differentiableOn) Metric.isOpen_ball
      (fun i s hs => hb i s (le_of_lt (by simpa using hs))) (by simp)
    simp only [hs] at h
    rw [deriv_line hF] at h
    simp only [deriv_line (hf _)] at h
    exact h.tsum_eq

theorem norm_exp_le_corners (α c s : ℂ) (hs : ‖s‖ ≤ 2) :
    ‖Complex.exp (α + s * c)‖ ≤ ‖Complex.exp (α + (2 + 2 * Complex.I) * c)‖ + ‖Complex.exp (α + (2 - 2 * Complex.I) * c)‖ +
      ‖Complex.exp (α + (-2 + 2 * Complex.I) * c)‖ + ‖Complex.exp (α + (-2 - 2 * Complex.I) * c)‖ := by
  have h1 := abs_le.mp ((Complex.abs_re_le_norm s).trans hs)
  have h2 := abs_le.mp ((Complex.abs_im_le_norm s).trans hs)
  simp only [Complex.norm_exp]
  have p1 := Real.exp_pos (α + (2 + 2 * Complex.I) * c).re
  have p2 := Real.exp_pos (α + (2 - 2 * Complex.I) * c).re
  have p3 := Real.exp_pos (α + (-2 + 2 * Complex.I) * c).re
  have p4 := Real.exp_pos (α + (-2 - 2 * Complex.I) * c).re
  rcases le_total 0 c.re with hr | hr <;> rcases le_total 0 c.im with hi | hi
  · have : Real.exp (α + s * c).re ≤ Real.exp (α + (2 - 2 * Complex.I) * c).re :=
      Real.exp_le_exp.mpr (by simp; nlinarith)
    linarith
  · have : Real.exp (α + s * c).re ≤ Real.exp (α + (2 + 2 * Complex.I) * c).re :=
      Real.exp_le_exp.mpr (by simp; nlinarith)
    linarith
  · have : Real.exp (α + s * c).re ≤ Real.exp (α + (-2 - 2 * Complex.I) * c).re :=
      Real.exp_le_exp.mpr (by simp; nlinarith)
    linarith
  · have : Real.exp (α + s * c).re ≤ Real.exp (α + (-2 + 2 * Complex.I) * c).re :=
      Real.exp_le_exp.mpr (by simp; nlinarith)
    linarith

theorem norm_thT_le_corners {k : ℕ} (τ : Matrix (Fin k) (Fin k) ℂ) (a b Z W : Fin k → ℂ) (n : Fin k → ℤ) (s : ℂ)
    (hs : ‖s‖ ≤ 2) :
    ‖thT τ a b (Z + s • W) n‖ ≤ ‖thT τ a b (Z + (2 + 2 * Complex.I) • W) n‖ + ‖thT τ a b (Z + (2 - 2 * Complex.I) • W) n‖ +
      ‖thT τ a b (Z + (-2 + 2 * Complex.I) • W) n‖ + ‖thT τ a b (Z + (-2 - 2 * Complex.I) • W) n‖ := by
  have key : ∀ t : ℂ, thT τ a b (Z + t • W) n =
      Complex.exp ((Real.pi * Complex.I * (((fun i => (n i : ℂ)) + a) ⬝ᵥ τ.mulVec ((fun i => (n i : ℂ)) + a)) +
        2 * Real.pi * Complex.I * (((fun i => (n i : ℂ)) + a) ⬝ᵥ (Z + b))) +
        t * (2 * Real.pi * Complex.I * (((fun i => (n i : ℂ)) + a) ⬝ᵥ W))) := by
    intro t
    unfold thT
    congr 1
    generalize ((fun i => (n i : ℂ)) + a) = v
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
    ring
  simp only [key]
  exact norm_exp_le_corners _ _ s hs

def splitE {g g' r : ℕ} (σ : Fin g ≃ Fin g' ⊕ Fin r) : (Fin g → ℤ) ≃ (Fin r → ℤ) × (Fin g' → ℤ) where
  toFun := fun n => (tP σ n, zP σ n)
  invFun := fun p j => Sum.elim p.2 p.1 (σ j)
  left_inv := fun n => by
    funext j
    rcases h : σ j with i | l
    · simp only [h, Sum.elim_inl, zP]; rw [σ.symm_apply_eq.mpr h.symm]
    · simp only [h, Sum.elim_inr, tP]; rw [σ.symm_apply_eq.mpr h.symm]
  right_inv := fun p => by ext <;> simp [zP, tP]

variable {N : NumD ℂ} {g' r g : ℕ} {bX : Module.Basis (Fin r) ℤ N.X} (d : CD N g' r bX) (σ : Fin g ≃ Fin g' ⊕ Fin r)

theorem fj_eq_tsum (S : Matrix (Fin r) (Fin r) ℂ) (χ : N.X) (Z : Fin g → ℂ) :
    d.fj σ S χ Z = ∑' m, thT (d.full σ S) (d.aF σ) (d.bF σ) Z ((splitE σ).symm (bX.equivFun χ, m)) := by
  have hcv : cv (bX.equivFun χ) = co bX χ := by
    funext l; simp [cv, co, Module.Basis.equivFun_apply]
  have hsymm : ∀ p, splitE σ ((splitE σ).symm p) = p := (splitE σ).apply_symm_apply
  simp only [CD.fj, thetaChar_eq_tsum, ← tsum_mul_left]
  congr 1
  funext m
  have h1 : tP σ ((splitE σ).symm (bX.equivFun χ, m)) = bX.equivFun χ := congrArg Prod.fst (hsymm (bX.equivFun χ, m))
  have h2 : zP σ ((splitE σ).symm (bX.equivFun χ, m)) = m := congrArg Prod.snd (hsymm (bX.equivFun χ, m))
  rw [thT_full, h1, h2, hcv]

theorem half_aF : Half (d.aF σ) := by
  intro j
  simp only [CD.aF]
  rcases σ j with i | l
  · exact d.ha i
  · simp

theorem half_bF : Half (d.bF σ) := by
  intro j
  simp only [CD.bF]
  rcases σ j with i | l
  · exact d.hb i
  · exact d.hb2 l

theorem full_isSymm {S : Matrix (Fin r) (Fin r) ℂ} (hS : S.IsSymm) : (d.full σ S).IsSymm :=
  (Matrix.IsSymm.fromBlocks d.symm rfl (d.toricPeriodBlock_isSymm.add hS)).submatrix σ

theorem differentiable_fj (S : Matrix (Fin r) (Fin r) ℂ) (χ : N.X) : Differentiable ℂ (d.fj σ S χ) := by
  have h := (thetaChar_entire_ne_zero_automorphy g' d.τ d.a d.b d.symm d.pos d.ha d.hb).1
  have hz : Differentiable ℂ (fun Z : Fin g → ℂ => zP σ Z + d.t12 *ᵥ co bX χ) := by
    refine Differentiable.add_const _ ?_
    unfold zP
    fun_prop
  have ht : Differentiable ℂ (fun Z : Fin g → ℂ => co bX χ ⬝ᵥ (tP σ Z + d.b2)) := by
    simp only [dotProduct, tP, Pi.add_apply]
    fun_prop
  unfold CD.fj
  exact (((ht.const_mul _).const_add _).cexp).mul (h.comp hz)

theorem exists_bound {S : Matrix (Fin r) (Fin r) ℂ} (hpos : ((d.full σ S).map Complex.im).PosDef) (Z W : Fin g → ℂ) :
    ∃ u : N.X → ℝ, Summable u ∧ ∀ χ (s : ℂ), ‖s‖ ≤ 2 → ‖d.fj σ S χ (Z + s • W)‖ ≤ u χ := by
  have haF : ∀ j, ((d.aF σ j).re : ℂ) = d.aF σ j := by
    intro j
    rcases half_aF d σ j with h | h <;> simp [h]
  have hF : ∀ t : ℂ, Summable fun p => ‖thT (d.full σ S) (d.aF σ) (d.bF σ) (Z + t • W) ((splitE σ).symm p)‖ := fun t =>
    ((splitE σ).symm.summable_iff (f := fun n => ‖thT (d.full σ S) (d.aF σ) (d.bF σ) (Z + t • W) n‖)).mpr
      (summable_thT hpos haF (d.bF σ) _)
  have hG := (((hF (2 + 2 * Complex.I)).add (hF (2 - 2 * Complex.I))).add (hF (-2 + 2 * Complex.I))).add
    (hF (-2 - 2 * Complex.I))
  refine ⟨_, hG.prod.comp_injective bX.equivFun.injective, fun χ s hs => ?_⟩
  rw [fj_eq_tsum]
  refine (norm_tsum_le_tsum_norm ((hF s).prod_factor _)).trans ?_
  exact Summable.tsum_le_tsum (fun m => norm_thT_le_corners _ _ _ Z W _ s hs) ((hF s).prod_factor _) (hG.prod_factor _)

end GlobalTheory.MBLow.Cl.FJD


open GlobalTheory.MBLow.Cl.FJD in
theorem GlobalTheory.MBLow.Cl.fj_expansion_fderiv : AllCD fun {N} {g'} {r} {g} {bX} d σ => ∀ S : Matrix (Fin r) (Fin r) ℂ, S.IsSymm → ((d.full σ S).map Complex.im).PosDef → (∀ χ, Differentiable ℂ (d.fj σ S χ)) ∧ ∀ Z W, (Summable fun χ => ‖fderiv ℂ (d.fj σ S χ) Z W‖) ∧ ∑' χ, fderiv ℂ (d.fj σ S χ) Z W = fderiv ℂ (thetaChar (d.full σ S) (d.aF σ) (d.bF σ)) Z W := by
  intro N g' r g bX d σ S hS hpos
  refine ⟨differentiable_fj d σ S, fun Z W => ?_⟩
  obtain ⟨u, hu, hb⟩ := exists_bound d σ hpos Z W
  exact termwise (differentiable_fj d σ S)
    (thetaChar_entire_ne_zero_automorphy g _ _ _ (full_isSymm d σ hS) hpos (half_aF d σ) (half_bF d σ)).1
    (fun Z => (fj_expansion N g' r g bX d σ S hS hpos Z).2) Z W hu hb

end
end

section

open Filter GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.TwOrbGood

theorem avg_const {H : Type} [Group H] (c : ℂ) : GlobalTheory.BCT.avg (fun _ : H => c) = c := by
  have h : GlobalTheory.BCT.rStab (fun _ : H => c) = ⊤ := by
    ext k; simp [GlobalTheory.TwOrbConj.mem_rStab]
  unfold GlobalTheory.BCT.avg
  rw [h, Subgroup.index_top]
  have : (∑ᶠ q : H ⧸ (⊤ : Subgroup H), (fun _ : H => c) q.out) = c := by
    rw [finsum_eq_single (fun q : H ⧸ (⊤ : Subgroup H) => (fun _ : H => c) q.out) (QuotientGroup.mk 1)
      (fun q hq => absurd (by induction q using QuotientGroup.induction_on with | H a => exact QuotientGroup.eq.2 (Subgroup.mem_top _)) hq)]
  rw [this]; simp

theorem summand_goodplace : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (KH : Subgroup H) (δ : H), δ ∈ KH → cptPart (twCent (MonoidHom.id H) δ) ≤ KH → (∀ g : H, g⁻¹ * δ * g ∈ KH → ∃ t ∈ twCent (MonoidHom.id H) δ, t⁻¹ * g ∈ KH) → ∀ x : H, GlobalTheory.TwOrbConj.summand (MonoidHom.id H) KH δ ((KH : Set H).indicator 1) x = if ∃ t ∈ twCent (MonoidHom.id H) δ, ∃ k ∈ KH, x = t * k then 1 else 0 := by
  intro H _ _ _ KH δ hδ hc hg x
  split_ifs with hx
  · obtain ⟨t, ht, k, hk, rfl⟩ := hx
    have e : t * k = t * 1 * k := by group
    rw [e, GlobalTheory.TwOrbConj.summand_rep _ _ _ _ _ ht hk]
    unfold GlobalTheory.TwOrbConj.summand
    have hmap : KH.map (MulAut.conj (1 : H)).toMonoidHom = KH := GlobalTheory.TwOrbConj.map_conj_self KH KH.one_mem
    have hcT : cptPart (twCent (MonoidHom.id H) δ) ≤ twCent (MonoidHom.id H) δ := by
      unfold GlobalTheory.BCT.cptPart
      rw [Subgroup.closure_le]
      intro y hy; exact hy.1
    have hrel : (twCent (MonoidHom.id H) δ ⊓ KH.map (MulAut.conj (1 : H)).toMonoidHom).relIndex
        (cptPart (twCent (MonoidHom.id H) δ)) = 1 := by
      rw [hmap, Subgroup.relIndex_eq_one]
      exact le_inf hcT hc
    have hfun : (fun k : KH => (KH : Set H).indicator (1 : H → ℂ) ((1 * (k : H))⁻¹ * δ * (MonoidHom.id H) (1 * (k : H))))
        = fun _ => 1 := by
      funext k
      rw [Set.indicator_of_mem]
      · rfl
      · simp only [one_mul, MonoidHom.id_apply]
        exact KH.mul_mem (KH.mul_mem (KH.inv_mem k.2) hδ) k.2
    rw [hrel, hfun, avg_const]; simp
  · unfold GlobalTheory.TwOrbConj.summand
    have hfun : (fun k : KH => (KH : Set H).indicator (1 : H → ℂ) ((x * (k : H))⁻¹ * δ * (MonoidHom.id H) (x * (k : H))))
        = fun _ => 0 := by
      funext k
      rw [Set.indicator_of_notMem]
      intro hm
      simp only [MonoidHom.id_apply] at hm
      obtain ⟨t, ht, htk⟩ := hg (x * k) hm
      apply hx
      refine ⟨t, ht, t⁻¹ * (x * k) * (k : H)⁻¹, KH.mul_mem htk (KH.inv_mem k.2), by group⟩
    rw [hfun, avg_const]; simp

end GlobalTheory.TwOrbGood
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.EulerAbs

theorem avg_const_one {H : Type} [Group H] : avg (fun _ : H => (1 : ℂ)) = 1 := by
  have hs : rStab (fun _ : H => (1 : ℂ)) = ⊤ := by
    ext k; simp [rStab]
  unfold avg
  rw [hs, Subgroup.index_top]
  haveI : Subsingleton (H ⧸ (⊤ : Subgroup H)) := QuotientGroup.subsingleton_quotient_top
  haveI : Unique (H ⧸ (⊤ : Subgroup H)) := uniqueOfSubsingleton (QuotientGroup.mk 1)
  rw [finsum_unique]
  simp

theorem twTerm_one_eq_one {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (δ : G)
    (hθ : ∀ k ∈ K, θ k ∈ K) (hδ : δ ∈ K) (hc : cptPart (twCent θ δ) ≤ K) :
    twTerm θ K δ ((K : Set G).indicator 1) 1 = 1 := by
  have hT : cptPart (twCent θ δ) ≤ twCent θ δ := by
    unfold cptPart
    rw [Subgroup.closure_le]
    intro t ht; exact ht.1
  have hmap : K.map (MulAut.conj (1 : G)).toMonoidHom = K := by
    ext x; simp
  have hidx : ((twCent θ δ ⊓ K.map (MulAut.conj (1 : G)).toMonoidHom).relIndex (cptPart (twCent θ δ))) = 1 := by
    rw [hmap, Subgroup.relIndex_eq_one]
    exact le_inf hT hc
  have hf : (fun k : K => (K : Set G).indicator (1 : G → ℂ) ((1 * (k : G))⁻¹ * δ * θ (1 * k))) = fun _ => 1 := by
    funext k
    rw [Set.indicator_of_mem]
    · rfl
    · simp only [one_mul, SetLike.mem_coe]
      exact K.mul_mem (K.mul_mem (K.inv_mem k.2) hδ) (hθ _ k.2)
  unfold twTerm
  rw [hidx, hf, avg_const_one]
  simp

end GlobalTheory.EulerAbs
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.EulerAbs

theorem exists_ne_zero_of_twTerm_ne_zero {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G)
    (δ : G) (f : G → ℂ) (y : G) (h : GlobalTheory.EulerAbs.twTerm θ K δ f y ≠ 0) :
    ∃ k ∈ K, f ((y * k)⁻¹ * δ * θ (y * k)) ≠ 0 := by
  by_contra hc
  push_neg at hc
  apply h
  have hu : (fun k : K => f ((y * k)⁻¹ * δ * θ (y * k))) = fun _ => 0 := by
    funext k
    exact hc k k.2
  unfold GlobalTheory.EulerAbs.twTerm
  rw [hu]
  simp [GlobalTheory.BCT.avg]

end GlobalTheory.EulerAbs
end
