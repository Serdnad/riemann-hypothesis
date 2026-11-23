module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2897
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3280
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2966
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3338
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle077
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3339
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3038
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2940
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3340
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3332
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3180
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3336
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3171
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3222
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3341
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3343
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumCmp

theorem point_and_compare : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₀ D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, SamePol D₀.toPre D.toPre → ∃ g : GtPt D.toPre (𝟙_ (Over (Sp R))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) ∧ ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) → ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G), LBIso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (D₁ D₂' : DegData R' (maximalIdeal R')), FinExt ρ ∧ IsLocalHom ρ ∧ Nonempty (IsPullDeg ρ D₀.toPre D₁.toPre) ∧ Nonempty (IsPullDeg ρ D₂.toPre D₂'.toPre) ∧ Nonempty (IsPullDeg (RingHom.id R') D₁.toPre D₂'.toPre) := by
  have L1 := GlobalTheory.T.exists_twoTorsion_twist_of_same_polarisedData
  have L2 := GlobalTheory.T.uniformisationData_translate_orderTwo_isTwist
  have L3 := GlobalTheory.T.nonempty_isPullDeg_of_same_torus_twist
  intro R _ _ _ hB D₀ D A G _ _ hG U hS
  obtain ⟨g, hz, htw⟩ := L1 R hB D₀ D hS
  refine ⟨g, hz, fun a ha hlev A₂ D₂ U₂ hL => ?_⟩
  have h2 := L2 R hB D A G hG U g hz a ha hlev A₂ D₂ U₂ hL
  obtain ⟨h3⟩ := L3 R hB D₀ D₂ D g htw h2
  obtain ⟨s₀, -⟩ := GlobalTheory.DegPullId.exists_isPullDeg_id_self R (maximalIdeal R) hB.1 D₀
  obtain ⟨s₂, -⟩ := GlobalTheory.DegPullId.exists_isPullDeg_id_self R (maximalIdeal R) hB.1 D₂
  exact ⟨R, inferInstance, inferInstance, inferInstance, RingHom.id R, D₀, D₂,
    ⟨hB.1, Function.injective_id, RingHom.Finite.id R⟩, inferInstance, ⟨s₀⟩, ⟨s₂⟩, ⟨h3⟩⟩

end GlobalTheory.MumCmp
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.exists_surjective_lattice_coordMap_equivariant_dvr : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → IsDiscreteValuationRing V → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G') (g : R →+* V) (β : G'.left ⟶ G.left) (p : ℕ), p.Prime → (p : R) ∈ maximalIdeal R → ∀ (Wo : Set (Sp R)), IsOpen Wo → (∀ y, PsiUnitOn D.toPre y Wo) → (⟨RingHom.ker g, RingHom.ker_isPrime g⟩ : PrimeSpectrum R) ∈ Wo → IsGrpPullback G' G (spMap g) β → LBIso U'.LG.L (U.LG.L.pull β) → ∃ ρ : D.toPre.X →+ D'.toPre.X, Function.Surjective ρ ∧ CoordMap D.toPre D'.toPre g ρ ∧ EquivMap U U' β ρ := by
  first | exact @GlobalTheory.Poinc.Eq8.GenRestrict.exists_surjective_coordMap_equivMap | exact GlobalTheory.Poinc.Eq8.GenRestrict.exists_surjective_coordMap_equivMap | (intros; apply GlobalTheory.Poinc.Eq8.GenRestrict.exists_surjective_coordMap_equivMap <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.exists_thetaSetup_tower_large_ratio : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ N₀ : ℕ, ∃ 𝔗 : Tower X₁ act, N₀ ≤ 𝔗.X₂.S.r * 𝔗.X₂.S.N := by
  first | exact @GlobalTheory.Poinc.Sep.TowerLarge.exists_tower_ge | exact GlobalTheory.Poinc.Sep.TowerLarge.exists_tower_ge | (intros; apply GlobalTheory.Poinc.Sep.TowerLarge.exists_tower_ge <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.thetaSetupTower_member_terms_baseChange : ∀ {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z} (X₁ : Setup F W i) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (𝔗 : Tower X₁ act) (z₁ : X₁.M.Z) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ x₀ : X₁.S.Gam, X₁.M.Div X₁.S.th x₀ z₁ → ∃ eps : X₁.S.Gam → ℕ, ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam) (T : (Fin 8 → X) → C → V), 𝔪.Terms x₀ lab T → ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (io : V →+* V') (f : FractionRing V →+* FractionRing V'), (∀ v, f (algebraMap V (FractionRing V) v) = algebraMap V' (FractionRing V') (io v)) → Function.Injective io → io.Finite → ∀ (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (𝔪₂ : UMem 𝔗.X₂ z₂ 𝔗.act₂ V' ev₂ X (fun k => io (t k)) δ) (ψ : 𝔪₂.A.A.left ⟶ 𝔪.A.A.left) (hD : IsPullDeg io 𝔪.D.toPre 𝔪₂.D.toPre) (bc : 𝔪₂.G ≅ (Over.pullback (spMap io)).obj 𝔪.G), 𝔗.Ext ev io ev₂ → 𝔪₂.yK.comp 𝔗.om = f.comp 𝔪.yK → IsGrpPullback 𝔪₂.A.A 𝔪.A.A (spMap f) ψ → (∃ w : LB.Iso 𝔪₂.A.L (𝔪.A.L.pull ψ), w.IsGen) → 𝔪₂.φ ≫ 𝔗.φ = ψ ≫ 𝔪.φ → IsMonHom bc.hom → IsPullUnif io hD bc 𝔪.U 𝔪₂.U → (∀ mu, hD.xe (𝔪₂.e₈ mu) = 𝔪.e₈ mu) → 𝔪₂.U.gen.hom.left ≫ ψ ≫ 𝔪.U.gen.inv.left ≫ pullback.fst 𝔪.G.hom (jK V) = pullback.fst 𝔪₂.G.hom (jK V') ≫ bc.hom.left ≫ pullback.fst 𝔪.G.hom (spMap io) → ∀ zt : 𝔗.X₂.M.Z.presheaf.stalk z₂, 𝔗.X₂.M.stalkHom z₂ zt = algebraMap 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ 𝔗.X₂.S.ζ → 𝔪₂.Terms (𝔗.lam x₀) (fun c => 𝔗.lam (lab c)) (fun mu c => ev₂ zt ^ eps (lab c) * io (T mu c)) := by
  first | exact @GlobalTheory.Poinc.Sep.BaseTerms.terms_baseChange | exact GlobalTheory.Poinc.Sep.BaseTerms.terms_baseChange | (intros; apply GlobalTheory.Poinc.Sep.BaseTerms.terms_baseChange <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc.PreSys

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {C : UCompact Xo c}

theorem rank_le (T : UTrait Xo c) : Module.finrank (𝓞 E) T.P.D.toPre.X ≤ min Dw.p Dw.q := GlobalTheory.T.character_group_finrank_le_min_signature_unitary_trait E H Dw l Xo c T

theorem lam (X₁ : USetup C) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (hz : IsClosed ({z₁} : Set X₁.M.Z)) :
    ∃ K : ℝ, ∀ (t : UCTrait X₁ p z₁) (x : t.T.P.D.toPre.X), x ≠ 0 →
      ∃ h ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁), Real.exp (-(K * (t.sc * t.T.be x x))) ≤ ‖t.val h‖ :=
  GlobalTheory.T.classical_trait_periods_bounded_below_closed_point E H Dw l Xo c C X₁ p z₁ hz

theorem finite_X (T : UTrait Xo c) : Module.Finite (𝓞 E) T.P.D.toPre.X :=
  Module.Finite.of_restrictScalars_finite ℤ _ _

theorem projective_X (T : UTrait Xo c) : Module.Projective (𝓞 E) T.P.D.toPre.X := by
  have : Module.Finite (𝓞 E) T.P.D.toPre.X := finite_X T
  have : Module.Flat (𝓞 E) T.P.D.toPre.X := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    rintro x ⟨a, hx⟩
    by_contra hx0
    obtain ⟨n, hn, b, hb⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) (a : 𝓞 E)).exists_nonzero_dvd
      (mem_nonZeroDivisors_of_ne_zero (nonZeroDivisors.coe_ne_zero a))
    have h : n • x = 0 := by
      have hx' : (a : 𝓞 E) • x = 0 := hx
      rw [← algebraMap_smul (𝓞 E) n x, hb, mul_comm, mul_smul, hx', smul_zero]
    exact hx0 ((smul_eq_zero.1 h).resolve_left hn)
  have : Module.FinitePresentation (𝓞 E) T.P.D.toPre.X := Module.finitePresentation_of_finite _ _
  exact Module.Flat.projective_of_finitePresentation

variable {X₁ : USetup C} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z}

def evC (t : UCTrait X₁ p z₁) : X₁.M.Z.presheaf.stalk z₁ →+* PadicAlgCl p :=
  (RatModel.valHomOf (gPt p ≫ t.y) z₁ (RatModel.gPt_specializes t.cen)).comp (X₁.M.stalkEquiv z₁).toRingHom

theorem evC_apply (t : UCTrait X₁ p z₁) (a : X₁.M.Z.presheaf.stalk z₁) : evC t a = t.val a := rfl

theorem norm_evC_le (t : UCTrait X₁ p z₁) (a : X₁.M.Z.presheaf.stalk z₁) : ‖evC t a‖ ≤ 1 :=
  RatModel.norm_val_le_one t.cen (X₁.M.stalkEquiv z₁ a).2

theorem norm_evC_lt (t : UCTrait X₁ p z₁) (a : X₁.M.Z.presheaf.stalk z₁) (ha : a ∈ maximalIdeal _) :
    ‖evC t a‖ < 1 := by
  have h1 : ¬ IsUnit (X₁.M.stalkEquiv z₁ a) := fun hu => ha ((isUnit_map_iff (X₁.M.stalkEquiv z₁) a).1 hu)
  exact (RatModel.norm_val_lt_one_iff t.cen (X₁.M.stalkEquiv z₁ a).2).2 h1

theorem sc_pos (t : UCTrait X₁ p z₁) : 0 < t.sc := by
  have hϖ0 : algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 t.T.irr.ne_zero
  have h0 : t.ι (algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ) ≠ 0 := (map_ne_zero _).2 hϖ0
  have hlt : ‖t.ι (algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ)‖ < 1 := by
    by_contra hge
    push_neg at hge
    have hinv : ‖t.ι (algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ)⁻¹‖ ≤ 1 := by
      rw [map_inv₀, norm_inv]
      exact inv_le_one_of_one_le₀ hge
    obtain ⟨w, hw⟩ := (t.int _).1 hinv
    apply t.T.irr.not_isUnit
    refine isUnit_iff_exists_inv.2 ⟨w, IsFractionRing.injective t.T.V (FractionRing t.T.V) ?_⟩
    rw [map_mul, hw, map_one, mul_inv_cancel₀ hϖ0]
  unfold UCTrait.sc
  have := Real.log_neg (norm_pos_iff.2 h0) hlt
  linarith

theorem be_pos (T : UTrait Xo c) (x : T.P.D.toPre.X) (hx : x ≠ 0) : 0 < T.be x x := by
  obtain ⟨j, hj⟩ := IsMonomial.exists_pos (IsLocalRing.maximalIdeal.isMaximal T.V).ne_top T.mono hx
  fin_cases j
  simpa using hj

theorem be_bal (T : UTrait Xo c) : T.be ∈ balForms (H.bar : 𝓞 E → 𝓞 E) T.P.D.toPre.X := by
  rw [balForms_eq_levelForms]; exact T.lev

end GlobalTheory.UPoinc.PreSys

namespace GlobalTheory.UPoinc.PreSys

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {C : UCompact Xo c} {X₁ : USetup C} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z}


variable (E X₁ p) in
abbrev Key : Type :=
  (Sp (OO p) ⟶ X₁.M.Z) × (Σ k : ℕ, (𝓞 E →+* Module.End ℤ (Fin k → ℤ)) × ((Fin k → ℤ) → (Fin k → ℤ) → ℝ))

def Rep (t : UCTrait X₁ p z₁) (q : Key E X₁ p) : Prop :=
  t.y = q.1 ∧ ∃ e : (Fin q.2.1 → ℤ) ≃ₗ[ℤ] t.T.P.D.toPre.X, (∀ (a : 𝓞 E) u, e (q.2.2.1 a u) = a • e u) ∧
    ∀ u v, q.2.2.2 u v = t.sc * t.T.be (e u) (e v)

def coord (t : UCTrait X₁ p z₁) : (Fin (Module.finrank ℤ t.T.P.D.toPre.X) → ℤ) ≃ₗ[ℤ] t.T.P.D.toPre.X :=
  (Module.finBasis ℤ t.T.P.D.toPre.X).equivFun.symm

def actOf (t : UCTrait X₁ p z₁) : 𝓞 E →+* Module.End ℤ (Fin (Module.finrank ℤ t.T.P.D.toPre.X) → ℤ) where
  toFun a := (coord t).symm.toLinearMap ∘ₗ (DistribSMul.toLinearMap ℤ t.T.P.D.toPre.X a) ∘ₗ (coord t).toLinearMap
  map_one' := LinearMap.ext fun u => by simp
  map_mul' a b := LinearMap.ext fun u => by simp [mul_smul]
  map_zero' := LinearMap.ext fun u => by simp
  map_add' a b := LinearMap.ext fun u => by simp [add_smul]

theorem coord_actOf (t : UCTrait X₁ p z₁) (a : 𝓞 E) (u : Fin (Module.finrank ℤ t.T.P.D.toPre.X) → ℤ) :
    coord t (actOf t a u) = a • coord t u := by
  simp [actOf]

def keyOf (t : UCTrait X₁ p z₁) : Key E X₁ p :=
  (t.y, ⟨Module.finrank ℤ t.T.P.D.toPre.X, actOf t, fun u v => t.sc * t.T.be (coord t u) (coord t v)⟩)

theorem rep_keyOf (t : UCTrait X₁ p z₁) : Rep t (keyOf t) := ⟨rfl, coord t, coord_actOf t, fun _ _ => rfl⟩


variable (X₁ p z₁) in
def Pts : Type := {q : Key E X₁ p // ∃ t : UCTrait X₁ p z₁, Rep t q}

noncomputable def pick (y : Pts X₁ p z₁) : UCTrait X₁ p z₁ := Classical.choose y.2

theorem pick_rep (y : Pts X₁ p z₁) : Rep (pick y) y.1 := Classical.choose_spec y.2

theorem exists_equiv_of_rep {t t' : UCTrait X₁ p z₁} {q : Key E X₁ p} (h : Rep t q) (h' : Rep t' q) :
    ∃ e : t.T.P.D.toPre.X ≃ₗ[𝓞 E] t'.T.P.D.toPre.X, ∀ a b, t.sc * t.T.be a b = t'.sc * t'.T.be (e a) (e b) := by
  obtain ⟨-, f, hf, hfb⟩ := h
  obtain ⟨-, f', hf', hfb'⟩ := h'
  let g : t.T.P.D.toPre.X ≃ₗ[ℤ] t'.T.P.D.toPre.X := f.symm.trans f'
  have hg : ∀ (a : 𝓞 E) x, g (a • x) = a • g x := by
    intro a x
    obtain ⟨u, rfl⟩ := f.surjective x
    simp only [g, LinearEquiv.trans_apply, ← hf, LinearEquiv.symm_apply_apply, hf']
  refine ⟨{ g with map_smul' := hg }, fun a b => ?_⟩
  obtain ⟨u, rfl⟩ := f.surjective a
  obtain ⟨v, rfl⟩ := f.surjective b
  show _ = t'.sc * t'.T.be (g (f u)) (g (f v))
  simp only [g, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rw [← hfb, ← hfb']


variable (X₁ p z₁) in
noncomputable def sys : FPre (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) p (X₁.M.Z.presheaf.stalk z₁) where
  Y := Pts X₁ p z₁
  ev y := evC (pick y)
  ev_le y h := norm_evC_le _ h
  ev_lt y h hh := norm_evC_lt _ h hh
  X y := (pick y).T.P.D.toPre.X
  fin y := finite_X _
  proj y := projective_X _
  rank_le y := rank_le _
  β y := (pick y).T.be
  bal y := be_bal _
  pos y x hx := be_pos _ x hx
  sc y := (pick y).sc
  sc_pos y := sc_pos _

theorem sys_matches : UMatches (sys X₁ p z₁) := by
  intro t
  refine ⟨⟨keyOf t, t, rep_keyOf t⟩, fun a => ?_, ?_⟩
  · obtain ⟨hy, -⟩ := pick_rep ⟨keyOf t, t, rep_keyOf t⟩
    show evC _ a = t.val a
    rw [evC_apply]
    unfold UCTrait.val
    rw [hy]
    rfl
  · exact exists_equiv_of_rep (pick_rep ⟨keyOf t, t, rep_keyOf t⟩) (rep_keyOf t)

theorem sys_lam (hz : IsClosed ({z₁} : Set X₁.M.Z)) : (sys X₁ p z₁).abelian₂ := by
  obtain ⟨K, hK⟩ := lam X₁ p z₁ hz
  exact ⟨K, fun y x hx => hK (pick y) x hx⟩

end GlobalTheory.UPoinc.PreSys


open GlobalTheory Classical in
theorem GlobalTheory.UPoinc.PreSys.main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z), IsClosed ({z₁} : Set X₁.M.Z) → ∃ (Φ : FPre (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) p (X₁.M.Z.presheaf.stalk z₁)), UMatches Φ ∧ Φ.abelian₂ ∧ (∀ y, ∃ t : UCTrait X₁ p z₁, (∀ a, Φ.ev y a = t.val a) ∧ ∃ e : Φ.X y ≃ₗ[𝓞 E] t.T.P.D.toPre.X, ∀ a b, Φ.sc y * Φ.β y a b = t.sc * t.T.be (e a) (e b)) := by
  intro E _ _ _ H Dw _ l Xo c C X₁ p _ z₁ hz
  exact ⟨GlobalTheory.UPoinc.PreSys.sys X₁ p z₁, GlobalTheory.UPoinc.PreSys.sys_matches, GlobalTheory.UPoinc.PreSys.sys_lam hz,
    fun y => ⟨GlobalTheory.UPoinc.PreSys.pick y, fun a => rfl, LinearEquiv.refl _ _, fun a b => rfl⟩⟩
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_polynomial_defect_heatOperator_monomial : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (m : ℕ) (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Dd.toPre.X), IsMonomial Dd.toPre t gam → (∀ i, t i ≠ 0) → ∀ D : Derivation ℤ R R, (∀ i, D (t i) ∈ Ideal.span {t i}) → ∀ h : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D, IsBasic Y h → ∃ (w : Dd.toPre.X → Dd.toPre.X →+ R) (π π' : Dd.toPre.X → R), HasDefect Y h (fun (k : ℕ) mu α => 2 * (k : R) * w mu α + 2 * (k : R) ^ 2 * π mu + 2 * (k : R) * π' mu) := by
  first | exact @GlobalTheory.Heat.exists_polynomial_defect_of_isMonomial | exact GlobalTheory.Heat.exists_polynomial_defect_of_isMonomial | (intros; apply GlobalTheory.Heat.exists_polynomial_defect_of_isMonomial <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSFlatPer

theorem isConstAlong_of_heat_flat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∃ c : ℚ, c ≠ 0 ∧ IsConstAlong P.D.toPre (bdParam k m d) gam ρ (fun i => (c : k) * MvPowerSeries.constantCoeff (q i)) := by
  intro E _ _ _ H k _ _ m d t P gam hmon hlin hab Y n' v' dd hdd D q hq h hb hdef hΘ ρ hρ
  obtain ⟨B', inst, π₁, π₂, h₁, h₂, h₃⟩ := GlobalTheory.T.abelian_part_constant_heat_operator_symbol_in_maximal_ideal E H k m d t P gam hmon hlin hab Y n' v' dd hdd D q hq h hb hdef hΘ ρ hρ
  choose c' hc' using GlobalTheory.T.heatOperators_symbol_zero_torsion_points_horizontal E H k m d t P gam hmon hlin hab Y n' v' dd hdd D q hq h hb hdef hΘ ρ hρ B' π₁ π₂ h₁ h₂ h₃
  obtain ⟨c, hc, w, hw, hrel⟩ := GlobalTheory.T.unitPart_periods_constant_along_tangent E H k m d t P gam hmon hlin hab Y n' v' dd hdd D q hq h hb hdef hΘ ρ hρ B' π₁ π₂ c' h₁ h₂ h₃ hc'
  exact ⟨c, hc, B', inst, π₁, π₂, w, c', h₁, h₂, h₃, hw, hc', hrel⟩

end GlobalTheory.KSFlatPer
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep

namespace GlobalTheory.USep

theorem member_of_monomial_unif : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (X₁ : GlobalTheory.GSep.GSet) (act : 𝓞 E → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (u : Sp (ratHull X₁.S.R) ⟶ Xo.XF c) (π : X₁.M.Z ⟶ C.Z), GlobalTheory.GSep.ULink C X₁ act u π → ∀ (z₁ : X₁.M.Z) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (t : SAB H (Sp V)) (y : Sp (FractionRing V) ⟶ Xo.XF c) (P : PELUnif (maximalIdeal V) t), GenOf Xo c y t → ∀ (m : ℕ) (s : Fin m → V) (β : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre s β → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ρ : V →+* V₁) (fK : FractionRing V →+* FractionRing V₁) (r : Fin m → V₁), IsCN V₁ → Function.Injective ρ → IsLocalHom ρ → (∀ a, fK (algebraMap V _ a) = algebraMap V₁ _ (ρ a)) → (∀ k, r k ^ 2 = ρ (s k)) → ∀ ev : X₁.M.Z.presheaf.stalk z₁ →+* V₁, IsLocalHom ev → GlobalTheory.GSep.RegAt X₁ z₁ ev → jK V₁ ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ ≫ π = spMap fK ≫ y ≫ C.i → ∃ (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V₁ ev (Fin 1 → P.D.toPre.X) (mono !![(1 : ℤ)] r β) (fun a mu => a • mu)) (p : IsPullDeg ρ P.D.toPre 𝔪.D.toPre), ∀ mu, p.xe (𝔪.e₈ mu) = mu 0 := by
  intro E _ _ _ H Dw hpq l Xo c C X₁ act u π hL z₁ V _ _ _ hV t y P hG m s β hmono V₁ _ _ _ ρ fK r hV₁ hinj hloc hfK hr ev hev hreg hpt
  obtain ⟨t₁, P₁, p, hG₁, hlin, hpsi⟩ := GlobalTheory.T.exists_unitaryUniformisation_baseChange_injective E H Dw l Xo c V hV t y P hG V₁ ρ fK hV₁ hinj hloc hfK
  obtain ⟨yK, x', hyK, hx', hx'u⟩ := GlobalTheory.GSep.valPt_lies_over_unitary E H Dw hpq l Xo c C X₁ act u π hL z₁ V₁ ev (spMap fK ≫ y) hreg
    (hpt.trans (Category.assoc _ _ _).symm)
  obtain ⟨φ, hcart, hwl, hact⟩ := GlobalTheory.T.unitaryUniformisation_genericFibre_isPullback E H Dw hpq l Xo c C X₁ act u π hL V₁ hV₁ t₁ P₁ yK x' hx'
    (by rw [hx'u]; exact hG₁)
  obtain ⟨wl, hwl⟩ := hwl
  let e₈ : (Fin 1 → P.D.toPre.X) ≃+ P₁.D.toPre.X := (AddEquiv.piUnique fun _ : Fin 1 => P.D.toPre.X).trans p.xe.symm
  have he₈ : ∀ mu, p.xe (e₈ mu) = mu 0 := fun mu => by simp [e₈]
  refine ⟨{
    cn := hV₁
    loc := hev
    reg := hreg
    yK := yK
    yK_eq := hyK
    D := P₁.D
    e₈ := e₈
    G := t₁.G
    semi := t₁.semi
    A := P₁.A
    U := P₁.U
    φ := φ
    cart := hcart
    wl := wl
    wl_gen := hwl
    equiv := fun a => ?_
    psi := fun mu => ?_ }, p, he₈⟩
  · obtain ⟨En, hEn, hh⟩ := GlobalTheory.USep.conjAct_endU_chars E H V₁ hV₁ t₁ P₁ a
    refine ⟨En, by rw [hEn]; exact hact a, fun mu => ?_⟩
    rw [hh]
    apply p.xe.injective
    rw [hlin, he₈, he₈]
    rfl
  · obtain ⟨u₀, n, hn, hc⟩ := hmono (mu 0)
    rw [← he₈ mu] at hc
    obtain ⟨w, hw⟩ := hpsi _ _ hc
    refine ⟨w * Units.map ρ.toMonoidHom u₀, ?_⟩
    have hmo : mono !![(1 : ℤ)] r β mu = ρ (∏ i, s i ^ n i) := by
      simp only [mono, qW, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.empty_val', _root_.one_mul, map_prod, map_pow]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hn i, ← hr i, ← pow_mul]
      congr 1
    rw [hmo]
    have hu : (↑(w * Units.map ρ.toMonoidHom u₀) : V₁) * ρ (∏ i, s i ^ n i) = ↑w * ρ (↑u₀ * ∏ i, s i ^ n i) := by
      rw [map_mul, Units.val_mul, Units.coe_map, _root_.mul_assoc]; rfl
    rw [hu]
    exact hw

end GlobalTheory.USep
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

namespace GlobalTheory.GSep.TorLabel

theorem exists_torus_char : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ, χ ^ (X₁.S.r * X₁.S.N) = 1 ∧ (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) :=
  fun I X₁ z₁ act V _ _ _ ev X _ t δ 𝔪 => GlobalTheory.T.exists_torus_char_of_label_orthogonal_dividing I X₁ z₁ act V ev X t δ 𝔪

end GlobalTheory.GSep.TorLabel
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section

namespace GlobalTheory.GSep

theorem exists_terms_single : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (t1 : Y1 → V1) (δ1 : I → Y1 → Y1) (𝔪1 : GlobalTheory.GSep.GMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (a : X₁.S.Gam), a ∈ X₁.S.HH X₁.M z₁ → ∃ T : Y1 → Unit → V1, 𝔪1.Terms x₀ (fun _ : Unit => a) T := by
  intro I X₁ z₁ act x₀ hdiv V _ _ _ ev Y _ t δ 𝔪 a ha
  obtain ⟨u, ⟨x, fr, th, w₀, s, g', w, hx, hfr, hth, hw₀, hs, hc, hT⟩, -, -⟩ :=
    GlobalTheory.T.thetaMember_exists_integral_terms_unit_shift I X₁ z₁ act x₀ hdiv V ev Y t δ 𝔪 (X₁.S.HH X₁.M z₁) Subtype.val Subtype.range_coe
  exact ⟨fun mu _ => u mu ⟨a, ha⟩ * t mu, x, fr, th, w₀, s, fun _ => g' ⟨a, ha⟩, fun _ => w ⟨a, ha⟩, hx, hfr, hth,
    hw₀, hs, fun _ => hc ⟨a, ha⟩, fun mu _ => hT mu ⟨a, ha⟩⟩

end GlobalTheory.GSep
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep


theorem _root_.GlobalTheory.T.thetaMember_term_nonzero_index_mem_maximalIdeal : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (t1 : Y1 → V1) (δ1 : I → Y1 → Y1) (𝔪1 : GlobalTheory.GSep.GMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : Y1 → C → V1, 𝔪1.Terms x₀ lab T → ∀ (c : C) (mu : Y1), mu ≠ 0 → T mu c ∈ maximalIdeal V1 := by
  first | exact @GlobalTheory.GSep.HighTerms.term_mem_maximalIdeal | exact GlobalTheory.GSep.HighTerms.term_mem_maximalIdeal | (intros; apply GlobalTheory.GSep.HighTerms.term_mem_maximalIdeal <;> assumption)
end

section

namespace GlobalTheory.ChernDegree

theorem chernWeilNumbers_holds : GlobalTheory.Published.ChernWeilNumbers :=
  GlobalTheory.T.chernWeilNumbers_of_degree_eq_chernIntegral GlobalTheory.T.degree_eq_integral_topChernForm_complex

end GlobalTheory.ChernDegree
end
