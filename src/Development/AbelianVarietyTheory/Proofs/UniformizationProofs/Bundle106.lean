module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle001
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle019
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle104
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle028
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle103
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle100
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle016
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle042
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle077
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle086
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle076
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBimultOfIsPullDeg
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionPointsIntegral
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle102
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SecTower

theorem exists_veryAmpleBy_pullback {R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R') {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of R)) {H : LB X} {n : ℕ} {s : Fin (n + 1) → LB.Sec H} (hH : H.IsLB)
    (hs : VeryAmpleBy f H s) :
    ∃ s' : Fin (n + 1) → LB.Sec (H.pull (pullback.fst f (Spec.map (CommRingCat.ofHom g)))),
      VeryAmpleBy (pullback.snd f (Spec.map (CommRingCat.ofHom g)))
        (H.pull (pullback.fst f (Spec.map (CommRingCat.ofHom g)))) s' := by
  have hL := LB.isLB_pull hH (pullback.fst f (Spec.map (CommRingCat.ofHom g)))
  have hw := CubePf.idIsoL_isGen hL
  choose s' hs' using fun j => GlobalTheory.SecPullIso.exists_pull _ H (H.pull _) _ hH hL hw (s j)
  refine ⟨s', GlobalTheory.AbLaw.VeryAmplePull.veryAmpleBy_pull R X f H n s hH hs R' g _ _ _ pullback.condition ?_ _ _ s' hL hw
    hs'⟩
  rw [pullback.lift_fst_snd]
  infer_instance

theorem exists_test_maps {R S : Type} [CommRing R] [CommRing S] (I : Ideal R) (g : R →+* S) (hg : ∀ x ∈ I, g x = 0)
    (Y : Over (Spec (CommRingCat.of R))) :
    ∃ (g' : ∀ e : ℕ, R ⧸ I ^ (e + 1) →+* S)
      (σ : ∀ e : ℕ, pullback Y.hom (Spec.map (CommRingCat.ofHom g)) ⟶ (thickObj R I e Y).left),
      (∀ e, (g' e).comp (Ideal.Quotient.mk _) = g) ∧
      (∀ e, IsPullback (σ e) (pullback.snd _ _) (thickObj R I e Y).hom (Spec.map (CommRingCat.ofHom (g' e)))) ∧
      (∀ e, σ e ≫ pullback.fst Y.hom (thick R I e) = pullback.fst _ _) ∧
      ∀ e, σ e ≫ thickMap R I e Y = σ (e + 1) := by
  let g' : ∀ e : ℕ, R ⧸ I ^ (e + 1) →+* S := fun e =>
    Ideal.Quotient.lift _ g fun x hx => hg x (Ideal.pow_le_self (Nat.succ_ne_zero e) hx)
  have hg' : ∀ e, (g' e).comp (Ideal.Quotient.mk _) = g := fun e => RingHom.ext fun x => rfl
  have hc : ∀ e, Spec.map (CommRingCat.ofHom (g' e)) ≫ thick R I e = Spec.map (CommRingCat.ofHom g) := fun e => by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hg']
  have ht : ∀ e, Spec.map (CommRingCat.ofHom (g' e)) ≫ thickTrans R I e =
      Spec.map (CommRingCat.ofHom (g' (e + 1))) := fun e => by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    rfl
  refine ⟨g', fun e => pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (g' e)))
    (by rw [Category.assoc, hc]; exact pullback.condition), hg', fun e => ?_, fun e => pullback.lift_fst _ _ _,
    fun e => ?_⟩
  · refine IsPullback.of_right (h₁₂ := pullback.fst Y.hom (thick R I e)) (h₂₂ := thick R I e)
      (v₁₃ := Y.hom) ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
    rw [hc, pullback.lift_fst]
    exact IsPullback.of_hasPullback _ _
  · apply pullback.hom_ext
    · erw [Category.assoc, pullback.lift_fst, pullback.lift_fst, pullback.lift_fst]
    · erw [Category.assoc, pullback.lift_snd, pullback.lift_snd, ← Category.assoc, pullback.lift_snd,
        Category.assoc, ht]

theorem isPullback_thickMap {R : Type} [CommRing R] (I : Ideal R) (Y : Over (Spec (CommRingCat.of R))) (e : ℕ) :
    IsPullback (thickMap R I e Y) (thickObj R I e Y).hom (thickObj R I (e + 1) Y).hom (thickTrans R I e) := by
  refine IsPullback.of_right (h₁₂ := pullback.fst Y.hom (thick R I (e + 1))) (h₂₂ := thick R I (e + 1))
    (v₁₃ := Y.hom) ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
  rw [thickTrans_comp, pullback.lift_fst, Category.comp_id]
  exact IsPullback.of_hasPullback _ _

theorem exists_tower : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (Y : Over (Spec (CommRingCat.of R))) (H : LB Y.left) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), Smooth Y.hom → H.IsLB → VeryAmpleBy Y.hom H s → ∀ f : ∀ e, (thickObj R I e Y).left ⟶ Y.left, (∀ e, thickMap R I e Y ≫ f (e + 1) = f e) → ∃ (t : ℤ) (m : ℕ) (u : ∀ e, Fin (m + 1) → LB.Sec (LB.LinComb H (Y := (thickObj R I e Y).left) (K := Fin 2) ![pullback.fst Y.hom (thick R I e), f e] ![t, -1])), (⨆ i, nonzeroLocus (u 0 i) = ⊤) ∧ ∀ e i z J, Good H z J → sval (u (e + 1) i) (thickMap R I e Y) z J = sval (u e i) (𝟙 _) z J := by
  intro R _ _ I Y H n s hsm hH hs f hf
  obtain ⟨S, _, g, hS, hg, hker⟩ := GlobalTheory.exists_graded_ring_kernel_lift R I
  obtain ⟨g', σ, hg', hσ, hσa, hσt⟩ := exists_test_maps I g hg Y
  have hσb : ∀ e, σ e ≫ f e = σ 0 ≫ f 0 := fun e => by
    induction e with
    | zero => rfl
    | succ e ih => rw [← hσt, Category.assoc, hf, ih]
  obtain ⟨sS, hsS⟩ := exists_veryAmpleBy_pullback g Y.hom hH hs
  have hva := fun e : ℕ => exists_veryAmpleBy_pullback (Ideal.Quotient.mk (I ^ (e + 1))) Y.hom hH hs
  obtain ⟨t₁, h₁⟩ := GlobalTheory.T.exists_h1Vanishes_generated_pullbackPow_tensor_dual S _ _ _ H _ (σ 0 ≫ f 0) n sS hH hsS
  obtain ⟨s₀, hs₀⟩ := hva 0
  obtain ⟨t₂, h₂⟩ := GlobalTheory.T.exists_h1Vanishes_generated_pullbackPow_tensor_dual _ _ _ _ H _ (f 0) n s₀ hH hs₀
  obtain ⟨m, u₀, hu₀⟩ := (h₂ (max t₁ t₂) (le_max_right _ _)).2
  have hZ := (h₁ (max t₁ t₂) (le_max_left _ _)).1
  have step : ∀ (e : ℕ) (v : LB.Sec (LB.LinComb H (Y := (thickObj R I e Y).left) (K := Fin 2)
      ![pullback.fst Y.hom (thick R I e), f e] ![max t₁ t₂, -1])),
      ∃ v' : LB.Sec (LB.LinComb H (Y := (thickObj R I (e + 1) Y).left) (K := Fin 2)
        ![pullback.fst Y.hom (thick R I (e + 1)), f (e + 1)] ![max t₁ t₂, -1]),
        ∀ z J, Good H z J → sval v' (thickMap R I e Y) z J = sval v (𝟙 _) z J := fun e v => by
    obtain ⟨s₁, hs₁⟩ := hva (e + 1)
    refine GlobalTheory.T.exists_section_lift_baseChange_h1Vanishing_testRing _ _ S _ (g' (e + 1)) (hker e (g' (e + 1)) (hg' _)) _ _ _ (thickObj R I (e + 1) Y).hom
      (thickObj R I e Y).hom _ (thickMap R I e Y) (σ (e + 1))
      (inferInstanceAs (Smooth (pullback.snd Y.hom (thick R I (e + 1))))) ⟨_, LB.isLB_pull hH _, n, s₁, hs₁⟩
      (isPullback_thickMap I Y e) (hσ (e + 1)) _ H (Fin 2) _ _ _ hH (fun k => ?_)
      (hZ _ (σ (e + 1)) _ _ (hσa _) (hσb _)) v
    fin_cases k
    · exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)
    · exact hf e
  choose F hF using step
  exact ⟨max t₁ t₂, m, fun e => Nat.rec (motive := fun e => Fin (m + 1) → LB.Sec (LB.LinComb H
      (Y := (thickObj R I e Y).left) (K := Fin 2) ![pullback.fst Y.hom (thick R I e), f e] ![max t₁ t₂, -1]))
    u₀ (fun e v i => F e (v i)) e, hu₀, fun e i => hF e _⟩

end GlobalTheory.SecTower
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_generator_of_compatible_thickening_generators : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), IsAdicComplete I R → ∀ (Y : Over (Spec (CommRingCat.of R))), Smooth Y.hom → IsProjBy Y.hom → ∀ (W : Scheme.{0}) (L : LB W) (K : Type) [Fintype K] (φ : K → (Y.left ⟶ W)) (ε : K → ℤ) (φ' : ∀ e, K → ((thickObj R I e Y).left ⟶ W)), L.IsLB → (∀ e k, pullback.fst Y.hom (thick R I e) ≫ φ k = φ' e k) → ∀ f : ∀ e, LB.Gen (LB.LinComb L (φ' e) ε), (∀ e, (f e).IsGen) → (∀ e z J, Good L z J → val (f (e + 1)) (thickMap R I e Y) z J = val (f e) (𝟙 _) z J) → ∃ u : LB.Gen (LB.LinComb L φ ε), u.IsGen ∧ ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e Y).left) (z : Z) (J), Good L z J → val u (r ≫ pullback.fst Y.hom (thick R I e)) z J = val (f e) r z J := by
  first | exact @GlobalTheory.Unif.exists_gen_of_thick | exact GlobalTheory.Unif.exists_gen_of_thick | (intros; apply GlobalTheory.Unif.exists_gen_of_thick <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_projective_algebraisation_formal_embedding : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans V (IsLocalRing.maximalIdeal V) e)) → (∀ e, Flat (Y e).hom) → ∀ (H : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (H e) ((H (e + 1)).pull (β e))), (∀ e, (H e).IsLB ∧ (v e).IsGen) → ∀ (n : ℕ) (s : ∀ e, Fin (n + 1) → LB.Sec (H e)), (∀ e, (∀ j, (∀ z (k : (H (e + 1)).ι) (k' : (H e).ι), (β e) z ∈ (H (e + 1)).U k → z ∈ (H e).U k' → gs (β e) z _ ((s (e + 1) j).f k) = (Geo.Tor.gw (v e) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s e j).f k')))) → VeryAmpleBy (Y 0).hom (H 0) (s 0) → ∃ (B : Over (Spec (CommRingCat.of V))) (H' : LB B.left) (s' : Fin (n + 1) → LB.Sec H') (b : ∀ e, (Y e).left ⟶ B.left) (w : ∀ e, LB.Iso (H e) (H'.pull (b e))), H'.IsLB ∧ VeryAmpleBy B.hom H' s' ∧ (∀ e, IsPullback (b e) (Y e).hom B.hom (thick V (IsLocalRing.maximalIdeal V) e)) ∧ (∀ e, β e ≫ b (e + 1) = b e) ∧ (∀ e, (w e).IsGen ∧ (∀ j, (∀ z (k : (H').ι) (k' : (H e).ι), (b e) z ∈ (H').U k → z ∈ (H e).U k' → gs (b e) z _ ((s' j).f k) = (Geo.Tor.gw (w e) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s e j).f k')))) ∧ ∀ (t : ℕ) (F : MvPolynomial (Fin (n + 1)) V), F.IsHomogeneous t → (∀ e, (∀ k : (H e).ι, MvPolynomial.eval₂Hom (cst ((Y (e)).hom ≫ thick V (IsLocalRing.maximalIdeal V) (e)) ((H e).U k)) (fun j => (s e j).f k) (F) = 0)) → (∀ k : (H').ι, MvPolynomial.eval₂Hom (cst (B.hom) ((H').U k)) (fun j => (s' j).f k) (F) = 0) := by
  first | exact @GlobalTheory.Unif.exists_projective_of_formal_embedding | exact GlobalTheory.Unif.exists_projective_of_formal_embedding | (intros; apply GlobalTheory.Unif.exists_projective_of_formal_embedding <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

theorem _root_.GlobalTheory.T.semiAbelian_hom_extension_dvr : HomExtSt := by
  first | exact @GlobalTheory.homExtension_semiAbelian_dvr_unconditional | exact GlobalTheory.homExtension_semiAbelian_dvr_unconditional | (intros; apply GlobalTheory.homExtension_semiAbelian_dvr_unconditional <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.FrameVal
open GlobalTheory.UT.CoefBasic GlobalTheory.UT.CoefUnit

theorem genV_of_pow : AllDV fun {V} _ _ _ {ϖ} hϖ D Q {F} _ _ {v} hv => ∀ (n : ℕ), 1 ≤ n → ∀ (p : QkPt D.toPre F n) (w₁ : Frm D.toPre F 1 p.g.b), w₁.IsGen → ∀ κ : LB.Gen (kapLB D.toPre (𝟙 D.toPre.P.A ^ n) (4 * n ^ 2) 4), κ.IsGen → (∀ z J, Good D.toPre.P.L z J → val w₁ (𝟙 _) z J ^ (4 * n ^ 2) * val κ p.g.b.left z J = (@id ((TF (R := V) F).left.presheaf.stalk z)ˣ (val (D.toPre.psi p.y) (jFK (R := V) F) z J) * rigV D.toPre (TF (R := V) F).hom z J) ^ 4) → GenV hϖ hv w₁ ((Q p.y : ℚ) / (n : ℚ) ^ 2) := by
  intro V _ _ _ _ _ ϖ hϖ D Q hQ F _ _ _ v hv n hn p w hw κ hκ H
  have hL := D.toPre.P.isLB
  obtain ⟨m, hm⟩ := TWM.exists_liftO hϖ hv (D := D) p.g.b
  have hmy : cP D.toPre (TWM.TO hϖ hv) p.y = m ^ n := TWM.liftO_unique hϖ hv _ _ (by
    rw [comp_cP, cPoint_y, ← hm]; exact (map_pow (preHom (TWM.ιS hϖ hv)) m n).symm)
  obtain ⟨t₀, ht₀⟩ := exists_gen_of_local D.toPre.P.L hL (TWM.lineφO hϖ hv m) (DegPre.lineε 1)
  have hl : ∀ i, DegPre.lineφ D.toPre F p.g.b i = (TWM.ιS hϖ hv).left ≫ TWM.lineφO hϖ hv m i := by
    intro i; fin_cases i
    · show (DegPre.zeroF D.toPre F).left = (TWM.ιS hϖ hv).left ≫ (1 : TWM.TO hϖ hv ⟶ D.toPre.P.A).left
      rw [← Over.comp_left, MonObj.comp_one]; rfl
    · show p.g.b.left = (TWM.ιS hϖ hv).left ≫ m.left
      rw [← Over.comp_left, hm]
  obtain ⟨x, hx0, hx⟩ := TWM.exists_ratio hL w hw (LB.pullGen D.toPre.P.L _ _ t₀ (TWM.ιS hϖ hv).left)
    (pullGen_isGen _ _ _ _ ht₀ _) (fun U _ h => Finset.prod_congr rfl fun i _ => by rw [hl])
  have hx' : ∀ z J, Good D.toPre.P.L z J → (val w (𝟙 _) z J).val =
      cst (R := V) F z x * (val t₀ (TWM.ιS hϖ hv).left z J).val := fun z J hJ => by
    have e := hx _ (𝟙 _) z J hJ
    rw [val_pull hJ] at e
    exact e
  refine ⟨TWM.lineφO hϖ hv m, hl, t₀, ht₀, x, ?_, hx'⟩
  obtain ⟨e, c, he, hc, hce⟩ := SectionScalarValuation.exists_val_genHasVal (hQ p.y)
  obtain ⟨u, hu, eu⟩ := exists_ratio_zero hϖ hv hL (fun U _ h => by
      have q : (TWM.TO hϖ hv).hom ≫ eSec D.toPre.P.A = (1 : TWM.TO hϖ hv ⟶ D.toPre.P.A).left := rfl
      have q₁ : (TWM.TO hϖ hv).hom ≫ (D.toPre.c p.y).left = (m ^ n).left := hmy ▸ rfl
      have q₂ : m.left ≫ (𝟙 D.toPre.P.A ^ n).left = (m ^ n).left :=
        congrArg (·.left) ((map_pow (preHom m) (𝟙 D.toPre.P.A) n).trans (congrArg (· ^ n) (Category.comp_id m)))
      have q₃ : m.left ≫ (1 : D.toPre.P.A ⟶ D.toPre.P.A).left = (1 : TWM.TO hϖ hv ⟶ D.toPre.P.A).left :=
        congrArg (·.left) (MonObj.comp_one (M := D.toPre.P.A) m)
      rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [Fintype.prod_unique (_ : PUnit → U), Fintype.prod_unique (_ : PUnit → U), q, q₁, Fin.prod_univ_two,
        Fin.prod_univ_three]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
        TWM.lineφO, DegPre.lineε, q₂, q₃, Category.comp_id]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen _ _ _ _ _ (GeneratorPullback.powGen _ _ _ t₀ (4 * n ^ 2)) (LB.pullGen _ _ _ κ m.left))
    (mulGen_isGen _ _ _ _ _ _ _ (DVR.powGen_isGen _ _ _ _ ht₀ _) (DVR.pullGen_isGen _ _ _ _ hκ _))
    (GeneratorPullback.powGen _ _ _ (LB.mulGen _ _ _ _ _ (LB.pullGen _ _ _ e (TWM.TO hϖ hv).hom)
      (LB.pullGen D.toPre.P.L (fun _ : PUnit => eSec D.toPre.P.A) (fun _ => 1) D.toPre.rig (TWM.TO hϖ hv).hom)) 4)
    (DVR.powGen_isGen _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ he _)
      (DVR.pullGen_isGen _ _ _ _ D.toPre.rig_gen _)) _)
  obtain ⟨z⟩ := exists_pt (R := V) (F := F)
  obtain ⟨J, hJ⟩ := exists_good' hL z
  have a := eu z J hJ
  rw [val_mul hJ, RatioVal.val_powGen, RatioVal.val_powGen, val_mul hJ, val_pull hJ, val_pull hJ, val_pull hJ,
    Over.w (TWM.ιS hϖ hv), ← Over.comp_left, hm] at a
  have b := congrArg Units.val (H z J hJ)
  have d : (@id ((TF (R := V) F).left.presheaf.stalk z)ˣ (val (D.toPre.psi p.y) (jFK (R := V) F) z J)).val =
      cstH z (algebraMap (FractionRing V) F c) * (val e (TF (R := V) F).hom z J).val :=
    (hce _ (jFK (R := V) F) z J hJ).trans (congrArg (· * _) (RatioVal.gs_scal _ z c))
  have key : x ^ (4 * n ^ 2) * u = algebraMap (FractionRing V) F c ^ 4 := by
    apply cstH_inj (R := V) z
    apply ((val e (TF (R := V) F).hom z J * rigV D.toPre (TF (R := V) F).hom z J) ^ 4).isUnit.mul_right_cancel
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, d, hx' z J hJ, cst_eq, rigV, map_mul, map_pow, mul_pow] at a b ⊢
    linear_combination b - cstH z x ^ (4 * n ^ 2) * a
  have k := congrArg v key
  obtain ⟨q, hq⟩ := TWM.wt_coe_of_ne (v := v) hx0
  rw [AddValuation.map_mul, AddValuation.map_pow, AddValuation.map_pow, hu, hv _ _ hc, hq] at k
  have k' : (4 * n ^ 2) • q + 0 = 4 • ((Q p.y : ℤ) : ℚ) := by exact_mod_cast k
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [hq, WithTop.coe_inj, eq_div_iff (pow_ne_zero 2 hn0)]
  simp only [nsmul_eq_mul] at k'
  push_cast at k'
  linarith

end GlobalTheory.UT.FrameVal
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

theorem _root_.GlobalTheory.T.pullbackSectionFamily_ne_zero_iff : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (f : ∀ α, SecBT D (𝟙_ _) k α) (s : Raw D F k), PullB D F (toUnit _) k f s → ∀ α, ((∃ j, (s α).f j ≠ 0) ↔ ∃ j, (f α).f j ≠ 0) := by
  first | exact @GlobalTheory.pullB_ne_zero_iff | exact GlobalTheory.pullB_ne_zero_iff | (intros; apply GlobalTheory.pullB_ne_zero_iff <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.Eqv

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem mem_of_nonempty {W : Type} [CommRing W] [IsDomain W] [Algebra R W] [Module.Finite R W]
    (φ : TF (R := R) F ⟶ TA R W) (z : (TF (R := R) F).left) (U : (TA R W).left.Opens)
    (hU : (U : Set (TA R W).left).Nonempty) : φ.left z ∈ U := by
  obtain ⟨x, hx⟩ := hU
  let p : PrimeSpectrum W := φ.left z
  have e : (TA R W).hom (φ.left z) = (TF (R := R) F).hom z := by
    rw [← Scheme.Hom.comp_apply, Over.w]
  have hp : p.asIdeal = ⊥ := by
    refine Ideal.eq_bot_of_comap_eq_bot (R := R) (eq_bot_iff.2 fun r hr => ?_)
    have h0 : r ∈ PrimeSpectrum.asIdeal (R := R) ((TA R W).hom (φ.left z)) := hr
    rw [e] at h0
    have h1 : algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) ∈ PrimeSpectrum.asIdeal (R := F) z := h0
    have hz : PrimeSpectrum.asIdeal (R := F) z = ⊥ := @Ideal.eq_bot_of_prime _ _ _ (PrimeSpectrum.isPrime _)
    rw [hz, Ideal.mem_bot, map_eq_zero,
      map_eq_zero_iff _ (IsFractionRing.injective R (FractionRing R))] at h1
    exact Ideal.mem_bot.2 h1
  have hle : p.asIdeal ≤ PrimeSpectrum.asIdeal (R := W) x := hp ▸ bot_le
  exact ((PrimeSpectrum.le_iff_specializes _ _).1 hle).mem_open U.isOpen hx

section Pull
variable {T : Over (Spec (CommRingCat.of R))} {φ : TF (R := R) F ⟶ T}

theorem pull_b {g : GtPt D T} {g' : GtPtF D F} (h : GtPt.IsPullF F φ.left g g') : g'.b = φ ≫ g.b :=
  Over.OverMorphism.ext h.1

theorem pull_val {g : GtPt D T} {g' : GtPtF D F} (h : GtPt.IsPullF F φ.left g g') (χ : D.X) {y J}
    (hJ : Good D.P.L y J) : val (g'.s χ) (𝟙 _) y J = val (g.s χ) φ.left y J :=
  (val_corr hJ (h.2 χ) _).trans ((val_pull hJ _ _ _).trans (by rw [Category.id_comp]))

theorem comp_cT (χ : D.X) : φ ≫ DegPre.cT D T χ = DegPre.cF D F χ := by
  rw [← Category.assoc, comp_toUnit]

theorem val_cubAtT {y J} (hJ : Good D.P.L y J) (χ : D.X) (a b : T ⟶ D.P.A) :
    val (DegPre.cubAtT D T (DegPre.cT D T χ) a b) φ.left y J =
      cubV D.cub y J (DegPre.cF D F χ) (φ ≫ a) (φ ≫ b) := by
  rw [← comp_cT (φ := φ)]
  exact val_cub D.cub φ hJ _ _ _

theorem isAdd_of_pull [IsReduced T.left] (hd : ∀ z (U : T.left.Opens), (U : Set T.left).Nonempty → φ.left z ∈ U)
    {g₁ g₂ g₃ : GtPt D T} {h₁ h₂ h₃ : GtPtF D F} (p₁ : GtPt.IsPullF F φ.left g₁ h₁) (p₂ : GtPt.IsPullF F φ.left g₂ h₂)
    (p₃ : GtPt.IsPullF F φ.left g₃ h₃) (H : h₁.IsAdd h₂ h₃) : g₁.IsAdd g₂ g₃ := by
  have : IsProper D.P.A.hom := D.P.isAb.proper
  have : D.P.A.left.IsSeparated := by
    rw [Scheme.isSeparated_iff, ← terminal.comp_from D.P.A.hom]; infer_instance
  obtain ⟨z⟩ : Nonempty (TF (R := R) F).left := ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum F)⟩
  have dom : IsDominant φ.left := ⟨dense_iff_inter_open.2 fun U hU hne => ⟨φ.left z, hd z ⟨U, hU⟩ hne, z, rfl⟩⟩
  obtain ⟨hb, hv⟩ := (isAdd_iff _ _ _).1 H
  refine ⟨Over.OverMorphism.ext (ext_of_isDominant φ.left ?_), fun χ =>
    GlobalTheory.TauPull.corr_of_dense D.P.isLB φ.left z (hd z) fun J hJ => ?_⟩
  · rw [pull_b p₁, pull_b p₂, pull_b p₃, ← MonObj.comp_mul] at hb
    exact congrArg (fun q => q.left) hb
  · have e := hv χ z J hJ
    rw [pull_val p₁ χ hJ, pull_val p₂ χ hJ, pull_val p₃ χ hJ, pull_b p₁, pull_b p₂] at e
    exact (val_mul hJ _ _ _).trans ((congrArg₂ (· * ·) rfl (val_cubAtT hJ χ _ _)).trans
      (e.trans (val_mul hJ _ _ _).symm))

theorem pull_eq_of_isAdd {g₁ g₂ g₃ g₃' : GtPt D T} {h h' : GtPtF D F} (a : g₁.IsAdd g₂ g₃) (a' : g₁.IsAdd g₂ g₃')
    (p : GtPt.IsPullF F φ.left g₃ h) (p' : GtPt.IsPullF F φ.left g₃' h') : h = h' := by
  refine GlobalTheory.TorusExt.gt_ext_val (by rw [pull_b p, pull_b p', a.1, a'.1]) fun χ y J hJ => ?_
  refine (pull_val p χ hJ).trans (Eq.trans ?_ (pull_val p' χ hJ).symm)
  have e := (val_mul hJ _ _ _).symm.trans (val_corr hJ (a.2 χ) φ.left)
  have e' := (val_mul hJ _ _ _).symm.trans (val_corr hJ (a'.2 χ) φ.left)
  exact mul_right_cancel (e.trans e'.symm)

end Pull

section Generic
variable {G : Over (Spec (CommRingCat.of R))}

def liftK (y : TF (R := R) F ⟶ G) : TFK (R := R) F ⟶ (Over.pullback (jK R)).obj G :=
  Over.homMk (pullback.lift y.left (jFK (R := R) F) (Over.w y)) (pullback.lift_snd _ _ _)

theorem liftK_fst (y : TF (R := R) F ⟶ G) : (liftK y).left ≫ pullback.fst G.hom (jK R) = y.left :=
  pullback.lift_fst _ _ _

theorem liftK_mul [GrpObj G] (y y' : TF (R := R) F ⟶ G) : liftK (y * y') = liftK y * liftK y' := by
  have e := toBase_mul_pullback G (jK R) _ (liftK y) (liftK y')
  have a : ∀ u : TF (R := R) F ⟶ G, toBase (A := G) (A' := (Over.pullback (jK R)).obj G)
      (g := pullback.fst G.hom (jK R)) pullback.condition (liftK u) = u := fun u => Over.OverMorphism.ext (liftK_fst u)
  rw [a, a] at e
  refine Over.OverMorphism.ext (pullback.hom_ext ((liftK_fst _).trans (congrArg (fun q => q.left) e).symm) ?_)
  exact (Over.w (liftK (y * y'))).trans (Over.w (liftK y * liftK y')).symm

end Generic

theorem main : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {_} _ _ U => ∀ N : ℕ, 1 ≤ N → ∃ m : {g : GtPtF D (Kbar V) // GtTors D N g} → (TFK (R := V) (Kbar V) ⟶ A.A), Function.Injective m ∧ (∀ g, U.Acts (Kbar V) N 0 g.1 (m g)) ∧ ∀ g g' g'', GtPtF.IsAdd g.1 g'.1 g''.1 → m g'' = m g * m g') := by
  intro hL hL2 V _ _ _ hV D A G _ _ U N hN
  classical
  have := hV.1
  have := hV.2.2
  have : CharZero (Kbar V) := algebraRat.charZero _
  have hN0 : N ≠ 0 := by omega
  have hfin : Finite {g : GtPtF D (Kbar V) // GtTors D N g} :=
    Nat.finite_of_card_ne_zero (by
      rw [(GlobalTheory.GtCount.card_gtTors hL hL2 V D (Kbar V) N (Nat.cast_ne_zero.2 hN0)).1]
      exact pow_ne_zero _ hN0)
  have hs : {g : GtPtF D (Kbar V) | GtTors D N g}.Finite := hfin
  obtain ⟨W, _, _, _, φ, hW, hg⟩ := GlobalTheory.torsion_points_integral V hV D N hN hs.toFinset fun g h => hs.mem_toFinset.1 h
  have := hW.1
  have := hW.2.2.1
  have : IsReduced (TA V W).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of W)))
  have hd := mem_of_nonempty φ
  choose x hx hxu using GlobalTheory.UU.RedOnto.main V hV D A G U W hW
  have add := fun g g' g'' => GlobalTheory.UU.RedAdd.main hL.globalFns V hV D A G U W hW _ _ _ g g' g'' (hx g) (hx g') (hx g'')
  choose i ip ih using fun g : {g : GtPtF D (Kbar V) // GtTors D N g} => hg g.1 (hs.mem_toFinset.2 g.2)
  have := U.gen_hom
  have := U.semi.separated
  obtain ⟨z⟩ : Nonempty (TF (R := V) (Kbar V)).left := ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Kbar V))⟩
  have dom : IsDominant φ.left := ⟨dense_iff_inter_open.2 fun U hU hne => ⟨φ.left z, hd z ⟨U, hU⟩ hne, z, rfl⟩⟩
  refine ⟨fun g => liftK (φ ≫ x (i g)) ≫ U.gen.hom, fun g g' e => ?_, fun g => ?_, fun g g' g'' h => ?_⟩
  · have e₁ : liftK (φ ≫ x (i g)) = liftK (φ ≫ x (i g')) := (cancel_mono U.gen.hom).1 e
    have e₂ : φ.left ≫ (x (i g)).left = φ.left ≫ (x (i g')).left :=
      (liftK_fst _).symm.trans ((congrArg (fun q => q.left ≫ pullback.fst G.hom (jK V)) e₁).trans (liftK_fst _))
    have e₃ : x (i g) = x (i g') := Over.OverMorphism.ext
      (ext_of_isDominant_of_isSeparated G.hom ((Over.w _).trans (Over.w _).symm) φ.left e₂)
    obtain ⟨o, -, ho⟩ := ih g
    have o1 : x o = 1 := (add o o o).2.2 ho
    exact Subtype.ext (pull_eq_of_isAdd ((add (i g) o (i g)).1.1 (by rw [o1, _root_.mul_one]))
      ((add (i g) o (i g')).1.1 (by rw [o1, _root_.mul_one, e₃])) (ip g) (ip g'))
  · refine GlobalTheory.T.torsionTranslation_acts_on_expansions hL hL2 V hV D A G U W hW (Kbar V) φ N hN (x (i g)) (i g) g.1 _ ?_ (hx _) (ip g) ?_
    · obtain ⟨o, ⟨gs, h₀, hs, rfl⟩, ho⟩ := ih g
      have key : ∀ n (hn : n < N + 1), x (gs ⟨n, hn⟩) = x (i g) ^ n := by
        intro n
        induction n with
        | zero => exact fun _ => ((add (gs 0) (gs 0) (gs 0)).2.2 h₀).trans (pow_zero _).symm
        | succ n ihn =>
          exact fun hn => ((add _ _ _).1.2 (hs ⟨n, by omega⟩)).trans
            ((congrArg (· * x (i g)) (ihn (by omega))).trans (pow_succ _ _).symm)
      exact (key N (Nat.lt_succ_self N)).symm.trans ((add _ (i g) (i g)).2.2 ho)
    · show (liftK (φ ≫ x (i g)) ≫ U.gen.hom).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK V) = _
      rw [← Category.assoc, ← Over.comp_left, Category.assoc, U.gen.hom_inv_id, Category.comp_id]
      exact liftK_fst _
  · have e : x (i g'') = x (i g) * x (i g') := (add _ _ _).1.2 (isAdd_of_pull hd (ip g) (ip g') (ip g'') h)
    show liftK (φ ≫ x (i g'')) ≫ U.gen.hom = _
    rw [e, MonObj.comp_mul, liftK_mul, MonObj.mul_comp]

end GlobalTheory.UU.Eqv
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

theorem _root_.GlobalTheory.T.exists_functionalEquation_section_nonzero_class : Laws → Laws2 → AllPre fun {V} _ _ _ {D} {_} {_} _ _ U => D.TauBimult → ∀ k : ℕ, 1 ≤ k → U.FE (Kbar V) 1 → U.FE (Kbar V) k → (∃ β, U.Supp (Kbar V) 1 β) → (∃ β, U.Supp (Kbar V) k β) → ∀ α, ∃ t s, U.ExpF (Kbar V) (k + 1) t s ∧ DegPre.FamFE D (Kbar V) (k + 1) s ∧ ∃ j, (s α).f j ≠ 0 := by
  first | exact @GlobalTheory.UU.FESection.main | exact GlobalTheory.UU.FESection.main | (intros; apply GlobalTheory.UU.FESection.main <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

theorem _root_.GlobalTheory.T.exists_integral_theta_section_with_expansion : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∃ θ f, U.Theta θ f) := by
  first | exact @GlobalTheory.ThetaIntegral.exists_theta | exact GlobalTheory.ThetaIntegral.exists_theta | (intros; apply GlobalTheory.ThetaIntegral.exists_theta <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

theorem _root_.GlobalTheory.T.exists_linear_fourierJacobi_expansion_family : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → ∃ ex : ∀ α : D.X, EA A (jFK (R := V) F) k →ₗ[F] WB D F k α, (∀ t, U.ExpF F k t.sec (fun α => (ex α t).sec)) ∧ (∀ t s, U.ExpF F k t s → ∀ α, s α = (ex α (SecMod.mk _ t)).sec) ∧ (∀ t, (∀ α, ex α t = 0) → t = 0) ∧ ∀ α, (U.Supp F k α ↔ ex α ≠ 0)) := by
  first | exact @GlobalTheory.UU.ExpLinMap.exists_expansion_linear | exact GlobalTheory.UU.ExpLinMap.exists_expansion_linear | (intros; apply GlobalTheory.UU.ExpLinMap.exists_expansion_linear <;> assumption)
end
