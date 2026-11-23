module

import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle019
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.LetAct
public import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FinalD
public import Formalism.LocalToGlobal.Columns.PolyFnLemmas
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle018
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.JetSubstPCompJetBC
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.LocalToGlobal.Columns.PolyFn

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FrameBaseChange

open MvPolynomial (X C)

theorem spec_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R' →+* R'') (g : R →+* R') :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

theorem gm_unit_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (u : Aˣ) {Z : Scheme.{0}} (r : Z ⟶ Sp B)
    (z : Z) : gm r z ⊤ (unitΓ (Units.map f.toMonoidHom u)) = gm (r ≫ spMap f) z ⊤ (unitΓ u) := by
  apply Units.ext
  rw [gm_val _ _ _ (by simp), gm_val _ _ _ (by simp)]
  unfold unitΓ toΓ
  simp only [Units.coe_map]
  have key := congrArg (fun g => g.hom (u : A)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at key
  erw [key]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

theorem val_scale {Y Z : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ Xo.univ.t.G.left)} {ε : K → ℤ}
    {z : Z} {J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι} (hJ : Good Xo.univ.t.PP.L z J) (c : Γ(Y, ⊤)ˣ)
    (t : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ ε)) (r : Z ⟶ Y) :
    val (Formalism.L2.Pj.scaleGen φ ε c t) r z J = gm r z ⊤ c * val t r z J := by
  unfold val Formalism.L2.Pj.scaleGen
  erw [map_mul, gm_res r z _ (hJ.mem φ r)]

variable {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ Xo.X)

theorem psIn_map {d n n' : ℕ} (m : ℕ) (r : Fin n → Fin n') (f : MvPowerSeries (Fin n × Fin d) S) :
    psIn d m r (MvPowerSeries.map ψ f) = MvPolynomial.map ψ (psIn d m r f) := by
  unfold psIn
  rw [MvPolynomial.map_rename]
  congr 1
  unfold psTrunc

  rw [map_sum]
  simp only [MvPolynomial.map_monomial, MvPowerSeries.coeff_map]

theorem subst_square {n n' d : ℕ} (m : ℕ) (φ : Fin n × Fin d → MvPolynomial (Fin n' × Fin d) S) :
    homAt (spMap ψ ≫ x0) (jetSubstP m (fun i => MvPolynomial.map ψ (φ i)) :
        Jet S' (Fin n × Fin d) m →ₐ[S'] Jet S' (Fin n' × Fin d) m) ≫ rjBC ψ x0 d m n =
      rjBC ψ x0 d m n' ≫ homAt x0 (jetSubstP m φ : Jet S (Fin n × Fin d) m →ₐ[S] Jet S (Fin n' × Fin d) m) := by
  unfold rjBC Formalism.L2.Pj.homAt
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, Over.homMk_left]
  rw [spec_comp, spec_comp]
  congr 1
  exact ReciprocityTheory.ChartRestriction.G.PullbackSections.jetSubstP_comp_jetBC ψ m φ

theorem jetMap_congr {R κ κ' : Type} [CommRing R] {m : ℕ} {f g : κ → MvPolynomial κ' R} (e : f = g)
    (hf : ∀ i, f i ∈ orig R κ') (hg : ∀ i, g i ∈ orig R κ') : jetMap (m := m) f hf = jetMap (m := m) g hg := by
  subst e
  rfl

theorem copy_square (d m n : ℕ) (i : Fin n) :
    homAt (spMap ψ ≫ x0) (jetCopy d m i : Jet S' (Fin 1 × Fin d) m →ₐ[S'] Jet S' (Fin n × Fin d) m) ≫
        rjBC ψ x0 d m 1 =
      rjBC ψ x0 d m n ≫ homAt x0 (jetCopy d m i : Jet S (Fin 1 × Fin d) m →ₐ[S] Jet S (Fin n × Fin d) m) := by
  apply GlobalTheory.RawChartBC.sq_copy <;> assumption

variable {ψ x0} {d : ℕ} {x : ∀ m, rjO x0 d m 1 ⟶ Xo.univ.t.G} {x' : ∀ m, rjO (spMap ψ ≫ x0) d m 1 ⟶ Xo.univ.t.G}

theorem point_bc (hx : ∀ m, x' m = rjBC ψ x0 d m 1 ≫ x m) {n : ℕ} (m : ℕ) (i : Fin n) :
    rjpt (spMap ψ ≫ x0) d x' m i = rjBC ψ x0 d m n ≫ rjpt x0 d x m i := by
  unfold rjpt
  rw [hx m, ← Category.assoc, copy_square, Category.assoc]

variable {e : ∀ m, RFrTy x0 d x m} {e' : ∀ m, RFrTy (spMap ψ ≫ x0) d x' m} {m : ℕ}
  (hc : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e' m) (LB.pullGen Xo.univ.t.PP.L
    (cφ ![rjpt x0 d x m (0 : Fin 2), rjpt x0 d x m (1 : Fin 2)]) (cε 2) (e m) (rjBC ψ x0 d m 2).left))
  {Z : Scheme.{0}} {z : Z} {J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι} (hJ : Good Xo.univ.t.PP.L z J)
include hc hJ

theorem val_subst {n : ℕ} (φ : Fin 2 → Fin d → MvPolynomial (Fin n × Fin d) S)
    (φ' : Fin 2 → Fin d → MvPolynomial (Fin n × Fin d) S') (hφ : ∀ i j, φ' i j = MvPolynomial.map ψ (φ i j))
    (r : Z ⟶ (rjO (spMap ψ ≫ x0) d m n).left) :
    val (rpe (spMap ψ ≫ x0) d x' e' m φ') r z J = val (rpe x0 d x e m φ) (r ≫ (rjBC ψ x0 d m n).left) z J := by
  unfold rpe
  refine ((val_pull hJ _ _ r).trans ((val_corr hJ hc _).trans (val_pull hJ _ _ _))).trans
    (Eq.trans (congrArg (fun q => val (e m) q z J) ?_) (val_pull hJ _ _ _).symm)
  have e2 : (fun p : Fin 2 × Fin d => φ' p.1 p.2) = fun p => MvPolynomial.map ψ (φ p.1 p.2) :=
    funext fun p => hφ p.1 p.2
  have hsq := subst_square ψ x0 m (fun p : Fin 2 × Fin d => φ p.1 p.2)
  simp only [Category.assoc, ← Over.comp_left, e2, hsq]

end GlobalTheory.FrameBaseChange

namespace GlobalTheory

open FrameBaseChange
open MvPolynomial (X C)

theorem isFrame_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S S' : Type) [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ Xo.X) (d : ℕ) (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (x : ∀ m, rjO x0 d m 1 ⟶ Xo.univ.t.G) (x' : ∀ m, rjO (spMap ψ ≫ x0) d m 1 ⟶ Xo.univ.t.G), (∀ m, x' m = rjBC ψ x0 d m 1 ≫ x m) → ∀ (e : ∀ m, RFrTy x0 d x m) (e' : ∀ m, RFrTy (spMap ψ ≫ x0) d x' m), (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → (∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e' m) (LB.pullGen Xo.univ.t.PP.L (cφ ![rjpt x0 d x m (0 : Fin 2), rjpt x0 d x m (1 : Fin 2)]) (cε 2) (e m) (rjBC ψ x0 d m 2).left)) → ∀ (ph1 ph2 : MvPowerSeries (Fin 3 × Fin d) S) (sy : MvPowerSeries (Fin 2 × Fin d) S) (ad : 𝓞 E → MvPowerSeries (Fin 2 × Fin d) S), RIsFrame x0 d x F act ph1 ph2 sy ad e → RIsFrame (spMap ψ ≫ x0) d x' (fun i => MvPowerSeries.map ψ (F i)) (fun a i => MvPowerSeries.map ψ (act a i)) (MvPowerSeries.map ψ ph1) (MvPowerSeries.map ψ ph2) (MvPowerSeries.map ψ sy) (fun a => MvPowerSeries.map ψ (ad a)) e' := by
  intro E _ _ _ H Dw l Xo S S' _ _ ψ x0 d F act x x' hx e e' he he' hc ph1 ph2 sy ad hF
  have hL : Xo.univ.t.PP.L.IsLB := Xo.univ.t.PP.isLB
  refine ⟨he', ?_, ?_, ?_, ?_⟩
  · intro m
    obtain ⟨u, hu, hcr⟩ := hF.ph1 m
    refine ⟨Units.map (jetBC ψ (Fin 3 × Fin d) m).toMonoidHom u, ?_, ?_⟩
    · rw [Units.coe_map]
      show jetBC ψ _ m (u : Jet S (Fin 3 × Fin d) m) = _
      rw [hu, ReciprocityTheory.ChartRestriction.G.PullbackSections.jetBC_psJet]
    · apply corr_of_val hL
      intro y J hJ
      have hlift : lift (rjpt (spMap ψ ≫ x0) d x' m (0 : Fin 3))
          (lift (rjpt (spMap ψ ≫ x0) d x' m (1 : Fin 3)) (rjpt (spMap ψ ≫ x0) d x' m (2 : Fin 3))) =
          rjBC ψ x0 d m 3 ≫ lift (rjpt x0 d x m (0 : Fin 3)) (lift (rjpt x0 d x m (1 : Fin 3)) (rjpt x0 d x m (2 : Fin 3))) := by
        simp only [point_bc hx, CartesianMonoidalCategory.comp_lift]
      refine (val_pull hJ _ _ _).trans ?_
      rw [hlift, Over.comp_left, ← Category.assoc]
      refine Eq.trans (val_pull hJ _ _ _).symm ((val_corr hJ hcr _).trans ((val_scale hJ _ _ _).trans ?_))
      refine Eq.trans ?_ (val_scale hJ _ _ _).symm
      refine congrArg₂ (· * ·) ?_ ?_
      · rw [gm_unit_map]
        rfl
      · simp only [val_mul hJ, val_inv]
        refine congrArg₂ (· * ·) ?_ (congrArg₂ (· * ·) (congrArg Inv.inv ?_) (congrArg Inv.inv ?_)) <;>
          exact (val_subst (hc m) hJ _ _ (by intro i j; fin_cases i <;> simp [psIn_map]) _).symm
  · intro m
    obtain ⟨u, hu, hcr⟩ := hF.ph2 m
    refine ⟨Units.map (jetBC ψ (Fin 3 × Fin d) m).toMonoidHom u, ?_, ?_⟩
    · rw [Units.coe_map]
      show jetBC ψ _ m (u : Jet S (Fin 3 × Fin d) m) = _
      rw [hu, ReciprocityTheory.ChartRestriction.G.PullbackSections.jetBC_psJet]
    · apply corr_of_val hL
      intro y J hJ
      have hlift : lift (rjpt (spMap ψ ≫ x0) d x' m (1 : Fin 3))
          (lift (rjpt (spMap ψ ≫ x0) d x' m (2 : Fin 3)) (rjpt (spMap ψ ≫ x0) d x' m (0 : Fin 3))) =
          rjBC ψ x0 d m 3 ≫ lift (rjpt x0 d x m (1 : Fin 3)) (lift (rjpt x0 d x m (2 : Fin 3)) (rjpt x0 d x m (0 : Fin 3))) := by
        simp only [point_bc hx, CartesianMonoidalCategory.comp_lift]
      refine (val_pull hJ _ _ _).trans ?_
      rw [hlift, Over.comp_left, ← Category.assoc]
      refine Eq.trans (val_pull hJ _ _ _).symm ((val_corr hJ hcr _).trans ((val_scale hJ _ _ _).trans ?_))
      refine Eq.trans ?_ (val_scale hJ _ _ _).symm
      refine congrArg₂ (· * ·) ?_ ?_
      · rw [gm_unit_map]
        rfl
      · simp only [val_mul hJ, val_inv]
        refine congrArg₂ (· * ·) ?_ (congrArg₂ (· * ·) (congrArg Inv.inv ?_) (congrArg Inv.inv ?_)) <;>
          exact (val_subst (hc m) hJ _ _ (by intro i j; fin_cases i <;> simp [psIn_map]) _).symm
  · intro m
    obtain ⟨u, hu, hcr⟩ := hF.sy m
    refine ⟨Units.map (jetBC ψ (Fin 2 × Fin d) m).toMonoidHom u, ?_, ?_⟩
    · rw [Units.coe_map]
      show jetBC ψ _ m (u : Jet S (Fin 2 × Fin d) m) = _
      rw [hu, ReciprocityTheory.ChartRestriction.G.PullbackSections.jetBC_psJet]
    · apply corr_of_val hL
      intro y J hJ
      refine ((val_corr hJ (hc m) _).trans (val_pull hJ _ _ _)).trans ?_
      refine ((val_corr hJ hcr _).trans (val_scale hJ _ _ _)).trans ?_
      refine Eq.trans ?_ (val_scale hJ _ _ _).symm
      refine congrArg₂ (· * ·) ?_ ?_
      · rw [← map_inv, gm_unit_map]
        rfl
      · refine (val_subst (hc m) hJ _ _ ?_ _).symm
        intro i j
        fin_cases i <;> simp
  · intro a
    obtain ⟨wL, hwL, hm⟩ := hF.ad a
    refine ⟨wL, hwL, fun m => ?_⟩
    obtain ⟨u, hu, hcr⟩ := hm m
    refine ⟨Units.map (jetBC ψ (Fin 2 × Fin d) m).toMonoidHom u, ?_, ?_⟩
    · rw [Units.coe_map]
      show jetBC ψ _ m (u : Jet S (Fin 2 × Fin d) m) = _
      rw [hu, ReciprocityTheory.ChartRestriction.G.PullbackSections.jetBC_psJet]
    · apply corr_of_val hL
      intro y J hJ
      have hlift : lift (rjpt (spMap ψ ≫ x0) d x' m (0 : Fin 2)) (rjpt (spMap ψ ≫ x0) d x' m (1 : Fin 2)) =
          rjBC ψ x0 d m 2 ≫ lift (rjpt x0 d x m (0 : Fin 2)) (rjpt x0 d x m (1 : Fin 2)) := by
        simp only [point_bc hx, CartesianMonoidalCategory.comp_lift]
      have h3 := (val_mul hJ _ _ _).symm.trans
        ((val_corr hJ hcr (𝟙 _ ≫ (rjBC ψ x0 d m 2).left)).trans (val_scale hJ _ _ _))
      refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (h3.trans (Eq.trans ?_ (val_scale hJ _ _ _).symm)))
      · refine congrArg₂ (· * ·) ?_ (val_subst (hc m) hJ _ _ (by intro i j; fin_cases i <;> simp [psIn_map]) _)
        refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
        show val wL (𝟙 _ ≫ (lift (rjpt (spMap ψ ≫ x0) d x' m (0 : Fin 2)) (rjpt (spMap ψ ≫ x0) d x' m (1 : Fin 2))).left) y J =
          val wL ((𝟙 _ ≫ (rjBC ψ x0 d m 2).left) ≫ (lift (rjpt x0 d x m (0 : Fin 2)) (rjpt x0 d x m (1 : Fin 2))).left) y J
        rw [hlift, Over.comp_left, Category.assoc]
      · refine congrArg₂ (· * ·) ?_ (val_subst (hc m) hJ _ _ (by intro i j; fin_cases i <;> simp [psIn_map]) _).symm
        rw [gm_unit_map]
        rfl

end GlobalTheory
end
end

section

open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.FrameRead
open scoped Classical

theorem _root_.GlobalTheory.T.hodge_weight_dominance_condition : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (n : ℕ) (Ix : Type) [Fintype Ix] (pl : Ix → (E →+* ℂ)), IsEnum H pl → Dw.p + Dw.q ≤ n → ∀ (l : Level H) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (s : Ix → ℤ) (lam : Ix → DomWeight n), (∀ τ, Antitone fun i => a (τ, i)) → WtIs Dw pl a s lam → (∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), ∃ F ∈ VV c.F lam, cof Dw pl c.F n P = detFac Dw pl c.F a s lam * F) ∧ (∀ F ∈ VV c.F lam, ∃! P, P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) ∧ cof Dw pl c.F n P = detFac Dw pl c.F a s lam * F) ∧ ∀ (g : Ix → GL (Fin n) c.F), ∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), ∀ F ∈ VV c.F lam, cof Dw pl c.F n P = detFac Dw pl c.F a s lam * F → cof Dw pl c.F n (letAct Dw pl c.F g P) = (∏ t, ((g t : Matrix (Fin n) (Fin n) c.F).det) ^ (-(s t))) • (detFac Dw pl c.F a s lam * actP lam g F) := by
  first | exact @GlobalTheory.FrameRead.cof_image | exact GlobalTheory.FrameRead.cof_image | (intros; apply GlobalTheory.FrameRead.cof_image <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OrbitSpan

open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.GradedWeylDivisibility
open scoped Classical Pointwise Matrix

theorem coeff_mem_of_eval_mem {K A : Type} [Field K] [CharZero K] [CommRing A] [Algebra K A] (M : Submodule K A)
    (p : Polynomial A) (h : ∀ c : ℕ, p.eval (c : A) ∈ M) (k : ℕ) : p.coeff k ∈ M := by
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro φ hφ
  rw [Submodule.mem_dualAnnihilator] at hφ
  set q : Polynomial K := ∑ i ∈ Finset.range (p.natDegree + 1), Polynomial.monomial i (φ (p.coeff i)) with hq
  have hq0 : q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono (s := Set.range (fun c : ℕ => (c : K))) ?_
      (Set.infinite_range_of_injective Nat.cast_injective)
    rintro _ ⟨c, rfl⟩
    have h1 := hφ _ (h c)

    rw [Polynomial.eval_eq_sum_range, map_sum] at h1
    simp only [Set.mem_setOf_eq, Polynomial.IsRoot.def, hq, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
    rw [← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : p.coeff i * (c : A) ^ i = ((c : K) ^ i) • p.coeff i := by
      rw [Algebra.smul_def, map_pow, map_natCast, mul_comm]
    rw [this, map_smul, smul_eq_mul, mul_comm]
  by_cases hk : k ≤ p.natDegree
  · have := congrArg (fun r => r.coeff k) hq0
    simp only [hq, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Finsupp.single_apply, Finset.sum_ite_eq', Finset.mem_range,
      Polynomial.coeff_zero] at this
    rwa [if_pos (by omega)] at this
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero]

theorem eval_rowGen {K : Type} [Field K] {r n : ℕ} (a b : Fin r) (c : K) (f : MvPolynomial (Fin r × Fin n) K) :
    (rowGen K a b f).eval (C c) = rowAct K (1 + Matrix.single b a c) f := by
  induction f using MvPolynomial.induction_on with
  | C x => simp [rowGen, rowAct]
  | add f g hf hg => simp only [map_add (f := _), Polynomial.eval_add, hf, hg]
  | mul_X f v hf =>
    simp only [map_mul, Polynomial.eval_mul, hf]
    congr 1
    simp only [rowGen, rowAct, aeval_X, Matrix.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib,
      Polynomial.eval_add, Polynomial.eval_C]
    congr 1
    · rw [Finset.sum_eq_single v.1]
      · simp
      · intro x _ hx
        simp [Matrix.one_apply, Ne.symm hx]
      · simp
    · rw [Finset.sum_eq_single a]
      · by_cases hv : v.1 = b
        · simp only [hv, if_true, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C,
            Matrix.single_apply_same]
        · simp [hv, Matrix.single, Ne.symm hv]
      · intro x _ hx
        simp [Matrix.single, Ne.symm hx]
      · simp

theorem isUnit_elem {K : Type} [Field K] [CharZero K] {r : ℕ} (a b : Fin r) (c : ℕ) :
    IsUnit (1 + Matrix.single b a (c : K)) := by
  by_cases h : a = b
  · subst h
    have hc : (1 + c : K) ≠ 0 := by exact_mod_cast (by omega : 1 + c ≠ 0)
    refine IsUnit.of_mul_eq_one (1 + Matrix.single a a (-(c : K) / (1 + c))) ?_
    rw [add_mul, mul_add, mul_add, one_mul, one_mul, mul_one, Matrix.single_mul_single_same, add_assoc,
      ← Matrix.single_add, ← Matrix.single_add]
    have : -(c : K) / (1 + c) + (c + c * (-(c : K) / (1 + c))) = 0 := by field_simp; ring
    rw [this]; simp
  · refine IsUnit.of_mul_eq_one (1 + Matrix.single b a (-(c : K))) ?_
    rw [add_mul, mul_add, mul_add, one_mul, one_mul, mul_one, Matrix.single_mul_single_of_ne _ _ _ _ h, add_zero,
      add_assoc, ← Matrix.single_add]
    simp

def trGL {K : Type} [Field K] {r : ℕ} (g : GL (Fin r) K) : GL (Fin r) K := inside₂ K r g⁻¹

theorem trGL_coe {K : Type} [Field K] {r : ℕ} (g : GL (Fin r) K) :
    (trGL g : Matrix (Fin r) (Fin r) K) = (g : Matrix (Fin r) (Fin r) K)ᵀ := by
  simp [trGL, inside₂]

theorem rowDiv_mem_of_stable {K : Type} [Field K] [CharZero K] {r m : ℕ}
    (M : Submodule K (MvPolynomial (Fin r × Fin m) K))
    (hst : ∀ u : GL (Fin r) K, ∀ f ∈ M, rowAct K (u : Matrix (Fin r) (Fin r) K) f ∈ M)
    (a b : Fin r) (k : ℕ) (f : MvPolynomial (Fin r × Fin m) K) (hf : f ∈ M) : rowDiv K a b k f ∈ M := by
  unfold rowDiv
  refine coeff_mem_of_eval_mem M _ (fun c => ?_) k
  have h1 := eval_rowGen a b (c : K) f
  rw [map_natCast] at h1
  rw [h1]
  obtain ⟨u, hu⟩ := isUnit_elem (K := K) a b c
  rw [← hu]
  exact hst u f hf

theorem applyWord_mem_of_stable {K : Type} [Field K] [CharZero K] {r m : ℕ}
    (M : Submodule K (MvPolynomial (Fin r × Fin m) K))
    (hst : ∀ u : GL (Fin r) K, ∀ f ∈ M, rowAct K (u : Matrix (Fin r) (Fin r) K) f ∈ M)
    (f : MvPolynomial (Fin r × Fin m) K) (hf : f ∈ M) (w : List (Fin r × Fin r × ℕ)) : applyWord K w f ∈ M := by
  unfold applyWord
  induction w with
  | nil => rw [List.foldr_nil]; exact hf
  | cons x w ih => rw [List.foldr_cons]; exact rowDiv_mem_of_stable M hst _ _ _ _ ih

theorem rowAct_one {K : Type} [Field K] {r m : ℕ} :
    rowAct K (n := m) (1 : Matrix (Fin r) (Fin r) K) = AlgHom.id K _ := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [rowAct, aeval_X, Matrix.one_apply, AlgHom.id_apply]
  rw [Finset.sum_eq_single v.1]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

theorem orbit_stable {K : Type} [Field K] {r m : ℕ} (v : MvPolynomial (Fin r × Fin m) K) (u : GL (Fin r) K)
    (f : MvPolynomial (Fin r × Fin m) K)
    (hf : f ∈ Submodule.span K (Set.range fun g : GL (Fin r) K => rowAct K (g : Matrix (Fin r) (Fin r) K)ᵀ v)) :
    rowAct K (u : Matrix (Fin r) (Fin r) K) f ∈
      Submodule.span K (Set.range fun g : GL (Fin r) K => rowAct K (g : Matrix (Fin r) (Fin r) K)ᵀ v) := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    refine Submodule.subset_span ⟨trGL u * g, ?_⟩
    have := DFunLike.congr_fun
      (rowActMul K r m (u : Matrix (Fin r) (Fin r) K) (g : Matrix (Fin r) (Fin r) K)ᵀ) v
    rw [AlgHom.comp_apply] at this
    beta_reduce
    rw [this, Units.val_mul, trGL_coe, Matrix.transpose_mul, Matrix.transpose_transpose]
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem dualWeyl_le_span_orbit (K : Type) [Field K] [CharZero K] {r m : ℕ} (hm : m ≤ r) (ν : Fin m → ℕ)
    (hν : Antitone ν) :
    dualWeyl K r m ν ≤ Submodule.span K (Set.range fun g : GL (Fin r) K =>
      rowAct K (g : Matrix (Fin r) (Fin r) K)ᵀ (hw K hm ν)) := by
  rw [Formalism.L2.Col.dualWeyl_eq_weyl K hm ν hν, weyl, Submodule.span_le]
  rintro _ ⟨w, rfl⟩
  generalize hw K hm ν = v
  refine applyWord_mem_of_stable _ (orbit_stable v) v (Submodule.subset_span ⟨1, ?_⟩) w
  beta_reduce
  rw [Units.val_one, Matrix.transpose_one, rowAct_one, AlgHom.id_apply]

theorem prod_mem_span_prod {K A ι : Type} [Field K] [CommRing A] [Algebra K A] (s : Finset ι) (S : ι → Set A)
    (x : ι → A) (hx : ∀ i, x i ∈ Submodule.span K (S i)) : ∏ i ∈ s, x i ∈ Submodule.span K (∏ i ∈ s, S i) := by
  induction s using Finset.induction_on with
  | empty => exact Submodule.subset_span (by simp)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ← Submodule.span_mul_span]
    exact Submodule.mul_mem_mul (hx a) ih

theorem trAct_ten {K : Type} [Field K] {Ix : Type} [Fintype Ix] {n : ℕ} (g : Ix → GL (Fin n) K)
    (f : Ix → MvPolynomial (Fin n × Fin n) K) :
    trAct g (ten f) = ten fun t => rowAct K (g t : Matrix (Fin n) (Fin n) K)ᵀ (f t) := by
  unfold trAct ten
  rw [map_prod]
  exact Finset.prod_congr rfl fun t _ =>
    (blockActTensor K K Ix n n (fun τ => (g τ : Matrix (Fin n) (Fin n) K)ᵀ)).1 t (f t)

theorem VV_eq_span_orbit (K : Type) [Field K] [CharZero K] (Ix : Type) [Fintype Ix] (n : ℕ)
    (lam : Ix → DomWeight n) :
    VV K lam = Submodule.span K
      (Set.range fun g : Ix → GL (Fin n) K => actP lam g (ten fun t => extremal K n (lam t))) := by
  apply le_antisymm
  · rw [VV, tensorLat, Submodule.span_le]
    rintro _ ⟨F, hF, rfl⟩
    have h1 := prod_mem_span_prod (K := K) Finset.univ
      (fun t => blockEmb K t '' (Set.range fun g : GL (Fin n) K =>
        rowAct K (g : Matrix (Fin n) (Fin n) K)ᵀ (extremal K n (lam t))))
      (fun t => blockEmb K t (F t)) (fun t => by
        have := dualWeyl_le_span_orbit K le_rfl (lam t).natW (Formalism.L2.Col.natW_anti (lam t)) (hF t)
        exact Submodule.apply_mem_span_image_of_mem_span (blockEmb K t).toLinearMap this)
    refine Submodule.span_le.mpr ?_ h1
    intro y hy
    rw [Set.mem_fintype_prod] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    choose w hw hw' using hz
    choose g hg using hw
    have hd : detTwK lam g ≠ 0 := Finset.prod_ne_zero_iff.mpr fun t _ => Units.ne_zero _
    have h2 : ∏ t, z t = (detTwK lam g)⁻¹ • actP lam g (ten fun t => extremal K n (lam t)) := by
      simp only [actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply, smul_smul, inv_mul_cancel₀ hd, one_smul,
        trAct_ten]
      unfold ten
      exact Finset.prod_congr rfl fun t _ => by rw [← hw', ← hg]
    rw [h2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    refine polyAction_mem_VV lam g (Submodule.subset_span ⟨_, fun t => ?_, rfl⟩)
    exact Formalism.GradedWeylDivisibility.weylLeDual K n n le_rfl _ (Formalism.L2.Col.natW_anti (lam t)) (Submodule.subset_span ⟨[], rfl⟩)

end GlobalTheory.OrbitSpan
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_isotropic_group_lattice_class_representatives : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → 0 < N → Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La → ∃ zz : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → Dw.La, (∀ i₀, (∀ (mu : Matrix (Fin n) (Fin n) E), (∀ v ∈ Λ.La, mu.mulVec v ∈ stdLat E n) → ∀ cm : Fin n → Fin n → 𝓞 E, (∀ i j, (cm i j : E) = (N : E) * mu i j) → ∀ i, Dw.ModN (N ^ 2) (∑ j, cm i j • zz i₀ j))) ∧ (∀ i i', (∀ b, Dw.ModN (N ^ 2) (zz i b - zz i' b)) → i = i') ∧ ∀ a : Fin n → Dw.La, (∀ (mu : Matrix (Fin n) (Fin n) E), (∀ v ∈ Λ.La, mu.mulVec v ∈ stdLat E n) → ∀ cm : Fin n → Fin n → 𝓞 E, (∀ i j, (cm i j : E) = (N : E) * mu i j) → ∀ i, Dw.ModN (N ^ 2) (∑ j, cm i j • a j)) → ∃ i, ∀ b, Dw.ModN (N ^ 2) (a b - zz i b) := by
  first | exact @GlobalTheory.ZCount.exists_class_representatives | exact GlobalTheory.ZCount.exists_class_representatives | (intros; apply GlobalTheory.ZCount.exists_class_representatives <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_rawChart_frames_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S S' : Type) [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ Xo.X) (d : ℕ) (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (x : ∀ m, rjO x0 d m 1 ⟶ Xo.univ.t.G) (x' : ∀ m, rjO (spMap ψ ≫ x0) d m 1 ⟶ Xo.univ.t.G), (∀ m, x' m = rjBC ψ x0 d m 1 ≫ x m) → ∀ (e : ∀ m, RFrTy x0 d x m), (∀ m, (e m).IsGen) → ∃ e' : ∀ m, RFrTy (spMap ψ ≫ x0) d x' m, (∀ m, (e' m).IsGen) ∧ (∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e' m) (LB.pullGen Xo.univ.t.PP.L (cφ ![rjpt x0 d x m (0 : Fin 2), rjpt x0 d x m (1 : Fin 2)]) (cε 2) (e m) (rjBC ψ x0 d m 2).left)) ∧ ∀ (m n' : ℕ) (φ : Fin 2 → Fin d → MvPolynomial (Fin n' × Fin d) S), LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (rpe (spMap ψ ≫ x0) d x' e' m (fun i j => MvPolynomial.map ψ (φ i j))) (LB.pullGen Xo.univ.t.PP.L _ _ (rpe x0 d x e m φ) (rjBC ψ x0 d m n').left) := by
  first | exact @GlobalTheory.RawFrameBC.exists_frames | exact GlobalTheory.RawFrameBC.exists_frames | (intros; apply GlobalTheory.RawFrameBC.exists_frames <;> assumption)
end

end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isFrame_rawChart_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S S' : Type) [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ Xo.X) (d : ℕ) (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (x : ∀ m, rjO x0 d m 1 ⟶ Xo.univ.t.G) (x' : ∀ m, rjO (spMap ψ ≫ x0) d m 1 ⟶ Xo.univ.t.G), (∀ m, x' m = rjBC ψ x0 d m 1 ≫ x m) → ∀ (e : ∀ m, RFrTy x0 d x m) (e' : ∀ m, RFrTy (spMap ψ ≫ x0) d x' m), (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → (∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e' m) (LB.pullGen Xo.univ.t.PP.L (cφ ![rjpt x0 d x m (0 : Fin 2), rjpt x0 d x m (1 : Fin 2)]) (cε 2) (e m) (rjBC ψ x0 d m 2).left)) → ∀ (ph1 ph2 : MvPowerSeries (Fin 3 × Fin d) S) (sy : MvPowerSeries (Fin 2 × Fin d) S) (ad : 𝓞 E → MvPowerSeries (Fin 2 × Fin d) S), RIsFrame x0 d x F act ph1 ph2 sy ad e → RIsFrame (spMap ψ ≫ x0) d x' (fun i => MvPowerSeries.map ψ (F i)) (fun a i => MvPowerSeries.map ψ (act a i)) (MvPowerSeries.map ψ ph1) (MvPowerSeries.map ψ ph2) (MvPowerSeries.map ψ sy) (fun a => MvPowerSeries.map ψ (ad a)) e' := by
  first | exact @GlobalTheory.isFrame_baseChange | exact GlobalTheory.isFrame_baseChange | (intros; apply GlobalTheory.isFrame_baseChange <;> assumption)

end
end
