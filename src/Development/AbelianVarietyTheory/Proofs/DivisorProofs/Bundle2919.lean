module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle065
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqTorusOfClassify
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothCommGroupSchemeEqOfPowEqOfClosedPoint
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle513
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle119
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2792
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2795
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2797
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle877
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPositiveDefiniteQuadraticFormEndomorphisms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2810
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2809
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SelfTorusExtensionCoordValuesEqOne
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2771
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2770
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle680
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle043
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle032
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
import Mathlib.RingTheory.Valuation.LocalSubring
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.HomTor

theorem pow_comp_monHom {S : Scheme.{0}} {G G' Z : Over S} [MonObj G] [MonObj G'] (φ : G ⟶ G')
    [IsMonHom φ] (x : Z ⟶ G) (n : ℕ) : (x ^ n) ≫ φ = (x ≫ φ) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.one_comp]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.mul_comp, ih]

theorem exists_torMatch : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (p : G' ⟶ G), IsMonHom p → ∃ ρ, TorMatch U U' (RingHom.id R) p.left ρ := by
  intro R _ _ _ hR G _ _ hG D A U G' _ _ hG' D' A' U' p hpm
  have hr : ∀ x ∈ maximalIdeal R ^ (0 + 1), residue R x = 0 := fun x hx =>
    (residue_eq_zero_iff x).2 (Ideal.pow_le_self (Nat.succ_ne_zero 0) hx)
  have hp := isGrpPullback_pullback G (spMap (residue R))
  have hp' := isGrpPullback_pullback G' (spMap (residue R))
  have e : ((Over.pullback (spMap (residue R))).map p).left ≫ pullback.fst G.hom (spMap (residue R)) =
      pullback.fst G'.hom (spMap (residue R)) ≫ p.left := pullback.lift_fst _ _ _
  have hf₁ : IsMonHom ((Over.pullback (spMap (residue R))).map p) :=
    Out.PullGtPf.isMonHom_of_grpPullback hp' hp p _ e
  obtain ⟨ρ, hρ⟩ := (GlobalTheory.TorusPart.mono_gtTorus_and_factor (U.gt 0) hr hp).2 _
    (GlobalTheory.TorusPart.gtTorus (U'.gt 0) hr hp' ≫ (Over.pullback (spMap (residue R))).map p) inferInstance
  refine ⟨ρ, ?_⟩
  intro F _ _ i₁ i₂ hF k hk τ τ' q q' a a' hτ'k hττ' hqy hq hq'y hq' ha ha'
  have hi : i₁ = i₂ := Algebra.algebra_ext _ _ fun x =>
    RingHom.congr_fun (IsLocalization.ringHom_ext (nonZeroDivisors R)
      (j := @algebraMap _ _ _ _ i₁) (k := @algebraMap _ _ _ _ i₂) (RingHom.ext hF)) x
  subst hi
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp at hk
    · exact h
  obtain ⟨s, s1, s2, s3, s4⟩ := GlobalTheory.ToricTorsionUnif.main R hR G hG D A U k hk1
  obtain ⟨s', s1', s2', s3', s4'⟩ := GlobalTheory.ToricTorsionUnif.main R hR G' hG' D' A' U' k hk1
  let ρm := AddMonoidHom.toMultiplicative ρ
  have powc : ∀ {H : Type} [CommGroup H] (f : Multiplicative D'.toPre.X →* H), f ^ k = 1 → (f.comp ρm) ^ k = 1 :=
    fun f hf => MonoidHom.ext fun x => by
      rw [MonoidHom.pow_apply, MonoidHom.comp_apply, ← MonoidHom.pow_apply, hf]; rfl
  have hτ : τ = τ'.comp ρm := MonoidHom.ext fun x => hττ' (Multiplicative.toAdd x)
  have hτk : τ ^ k = 1 := by
    rw [hτ]; exact powc τ' hτ'k
  let c : R →+* F := (algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))
  rw [s4 F c τ hτk q a rfl hqy hq ha, ← Category.assoc, s4' F c τ' hτ'k q' a' rfl hq'y hq' ha']
  obtain ⟨O, hO, hloc⟩ := IsLocalRing.exists_factor_valuationRing c
  let φ : R →+* O := c.codRestrict O.toSubring hO
  haveI : IsLocalHom φ := hloc
  have hc : c = O.subtype.comp φ := rfl
  obtain ⟨τO, hτO⟩ := GlobalTheory.ToricTorsionCompare.units_of_pow_eq_one F O _ k hk1 τ' hτ'k
  have hτOk : τO ^ k = 1 := by
    refine MonoidHom.ext fun x => Units.ext (Subtype.ext ?_)
    have := congrArg (fun f => ((f x : Fˣ) : F)) hτ'k
    simp only [MonoidHom.pow_apply, MonoidHom.one_apply, Units.val_pow_eq_pow_val, Units.val_one] at this ⊢
    rw [SubmonoidClass.coe_pow, hτO, this]; rfl
  let τR := τO.comp ρm
  have hτR : τR ^ k = 1 := powc τO hτOk
  have hkO : IsUnit (k : O) := by simpa using hk.map φ
  have hxy : s O φ τR hτR = s' O φ τO hτOk ≫ p := by
    refine GlobalTheory.LocalRigid.eq_of_pow_eq_of_closedPoint (Sp R) G hG.smooth O (spMap φ) k hkO _ _ ?_
      (ResidueField O) (residue O) inferInstance ?_
    · rw [s1, ← pow_comp_monHom, s1', MonObj.one_comp]
    · let τ₀ : Multiplicative D'.toPre.X →* (ResidueField O)ˣ := (Units.map (residue O).toMonoidHom).comp τO
      have h₀ : τ₀ ^ k = 1 := by
        rw [show τ₀ ^ k = (Units.map (residue O).toMonoidHom).comp (τO ^ k) by ext x; simp [τ₀]]
        rw [hτOk]; ext; simp
      let τ₁ := τ₀.comp ρm
      have h₁ : τ₁ ^ k = 1 := powc τ₀ h₀
      let z : Over.mk (spMap (ResidueField.map φ)) ⟶ splitTorus (Sp (ResidueField R)) D'.toPre.X :=
        (GlobalTheory.splitTorusPointsEquiv _ _ _).symm
          ((Units.map (Scheme.ΓSpecIso (CommRingCat.of (ResidueField O))).inv.hom.toMonoidHom).comp τ₀)
      have hz : ∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ₀ (Multiplicative.ofAdd χ)) := fun χ => by
        simp only [GlobalTheory.UU.chV, z, MulEquiv.apply_symm_apply]; rfl
      have hz₁ : ∀ χ, GlobalTheory.UU.chV (z ≫ GlobalTheory.SplitTorus.torusMap _ ρ) χ = unitOn (τ₁ (Multiplicative.ofAdd χ)) :=
        fun χ => by
          apply Units.ext
          rw [GlobalTheory.UU.chV_val, GlobalTheory.SplitTorus.charUnit_val, ← GlobalTheory.SplitTorus.val_eq,
            GlobalTheory.SplitTorus.val_comp_torusMap, GlobalTheory.SplitTorus.val_eq, ← GlobalTheory.SplitTorus.charUnit_val,
            ← GlobalTheory.UU.chV_val, hz]
          rfl
      have hres : (residue O).comp φ = (ResidueField.map φ).comp (residue R) := by
        ext r; simp [ResidueField.map_residue]
      rw [Over.comp_left, ← Category.assoc,
        ← s2 O _ φ ((residue O).comp φ) (residue O) τR hτR τ₁ h₁ rfl (fun χ => rfl),
        ← s2' O _ φ ((residue O).comp φ) (residue O) τO hτOk τ₀ h₀ rfl (fun χ => rfl),
        s3 _ _ (residue R) hr _ (ResidueField.map φ) _ _ hp τ₁ h₁ _ hres hz₁,
        s3' _ _ (residue R) hr _ (ResidueField.map φ) _ _ hp' τ₀ h₀ z hres hz,
        Category.assoc z, ← hρ, Category.assoc _ _ p.left, ← e]
      simp only [Over.comp_left, Category.assoc]
  rw [s2 O F φ c O.subtype τR hτR τ hτk hc (fun χ => by simp [τR, hτ, hτO]),
    s2' O F φ c O.subtype τO hτOk τ' hτ'k hc (fun χ => by simp [hτO]), hxy, Over.comp_left, Category.assoc]

end GlobalTheory.Poinc.HomTor

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_affineChart_lift_to_moduli_scheme : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (w : X₁.M.Z), X₁.π w ∈ Set.range i → ∃ (U : X₁.M.Z.Opens) (u : Sp (X₁.M.ringOn U) ⟶ F.X), IsAffineOpen U ∧ w ∈ U ∧ (∀ w' ∈ U, X₁.π w' ∈ Set.range i) ∧ spMap (X₁.M.ringOn U).val.toRingHom ≫ u = spMap X₁.S.R.val.toRingHom ≫ X₁.u := by
  first | exact @GlobalTheory.Poinc.ChartAt.exists_affine_chart_lift | exact GlobalTheory.Poinc.ChartAt.exists_affine_chart_lift | (intros; apply GlobalTheory.Poinc.ChartAt.exists_affine_chart_lift <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.thetaSetup_stalk_noetherian_normal_fractionRing : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z), letI : Algebra (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ := (X₁.M.stalkHom z₁).toAlgebra; IsDomain (X₁.M.Z.presheaf.stalk z₁) ∧ IsFractionRing (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ ∧ IsIntegrallyClosed (X₁.M.Z.presheaf.stalk z₁) ∧ IsNoetherianRing (X₁.M.Z.presheaf.stalk z₁) := by
  first | exact @GlobalTheory.Poinc.stalk_isNoetherian_normal_fractionRing | exact GlobalTheory.Poinc.stalk_isNoetherian_normal_fractionRing | (intros; apply GlobalTheory.Poinc.stalk_isNoetherian_normal_fractionRing <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_normalisation_model_finite_extension : ∀ {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z} (X₁ : Setup F W i) (o₂ Ω₂ : Type) [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] [ArithBase o₂ Ω₂] [Algebra X₁.Ω₁ Ω₂] [FiniteDimensional X₁.Ω₁ Ω₂] (κ : X₁.o₁ →+* o₂), κ.Finite → (algebraMap o₂ Ω₂).comp κ = (algebraMap X₁.Ω₁ Ω₂).comp (algebraMap X₁.o₁ X₁.Ω₁) → ∃ (M : RatModel o₂ Ω₂) (q : M.Z ⟶ X₁.M.Z), GlobalTheory.IsNormalScheme M.Z ∧ IsFinite q ∧ M.pt ≫ q = spMap (algebraMap X₁.Ω₁ Ω₂) ≫ X₁.M.pt := by
  first | exact @GlobalTheory.Poinc.Setup.exists_model_of_finiteDimensional | exact GlobalTheory.Poinc.Setup.exists_model_of_finiteDimensional | (intros; apply GlobalTheory.Poinc.Setup.exists_model_of_finiteDimensional <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep

variable {V V₁ : Type} [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁]

theorem exists_points_equiv {W₀ : Type} [CommRing W₀] (ρ : V →+* V₁) (ib : W₀ →+* V) (Q : Data V) (D : DegPre V₁)
    (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B)) (hpr : ∀ a, IsMonHom (pr a))
    (huniv : ∀ (T : Over (Sp V₁)) (y : Fin 8 → (T ⟶ (Over.pullback (spMap ρ)).obj Q.B)),
      ∃! x : T ⟶ D.P.A, ∀ a, x ≫ pr a = y a)
    (B₀ : Over (Sp W₀)) [GrpObj B₀] (β : Q.B.left ⟶ B₀.left) (hβ : IsGrpPullback Q.B B₀ (spMap ib) β)
    {X : Scheme.{0}} (t : X ⟶ Sp V₁) (g : X ⟶ Sp W₀) (hg : t ≫ spMap ρ ≫ spMap ib = g) :
    ∃ Φ : (Over.mk t ⟶ D.P.A) ≃* (Fin 8 → (Over.mk g ⟶ B₀)),
      ∀ x a, (Φ x a).left = x.left ≫ (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) ≫ β := by
  obtain ⟨E1, hE1⟩ := GlobalTheory.GroupBplus.Aff.exists_mulEquiv_points_of_isGrpPullback
    (isGrpPullback_pullback Q.B (spMap ρ)) t (t ≫ spMap ρ) rfl
  obtain ⟨E2, hE2⟩ := GlobalTheory.GroupBplus.Aff.exists_mulEquiv_points_of_isGrpPullback hβ (t ≫ spMap ρ) g
    (by rw [Category.assoc]; exact hg)
  let P : (Over.mk t ⟶ D.P.A) →* (Fin 8 → (Over.mk t ⟶ (Over.pullback (spMap ρ)).obj Q.B)) :=
    Pi.monoidHom fun a =>
      { toFun := fun x => x ≫ pr a
        map_one' := MonObj.one_comp _
        map_mul' := fun x y => MonObj.mul_comp _ _ _ }
  have hP : Function.Bijective P := by
    refine ⟨fun x y h => ?_, fun y => ?_⟩
    · obtain ⟨z, -, hz⟩ := huniv (Over.mk t) (P x)
      exact (hz x fun a => rfl).trans (hz y fun a => (congrFun h a).symm).symm
    · obtain ⟨z, hz, -⟩ := huniv (Over.mk t) y
      exact ⟨z, funext hz⟩
  refine ⟨(MulEquiv.ofBijective P hP).trans (MulEquiv.piCongrRight fun _ => E1.trans E2), fun x a => ?_⟩
  show (E2 (E1 (x ≫ pr a))).left = _
  rw [hE2, hE1, Over.comp_left]
  simp only [Category.assoc]

theorem spMap_three {A B C E : Type} [CommRing A] [CommRing B] [CommRing C] [CommRing E] (f : A →+* B) (g : B →+* C)
    (h : C →+* E) : spMap h ≫ spMap g ≫ spMap f = spMap ((h.comp g).comp f) := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem sharp_c_defOver {W₀ : Type} [CommRing W₀] (ρ : V →+* V₁) (ib : W₀ →+* V) (Q : Data V) (D : DegPre V₁)
    (e : (Fin 8 → Q.X) ≃+ D.X) (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B))
    (hc : ∀ mu a, (D.c (e mu) ≫ pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) = spMap ρ ≫ (Q.c (mu a)).left)
    (B₀ : Over (Sp W₀)) (β : Q.B.left ⟶ B₀.left) (c₀ : Q.X → (𝟙_ (Over (Sp W₀)) ⟶ B₀))
    (hβc : ∀ a, (Q.c a).left ≫ β = spMap ib ≫ (c₀ a).left)
    (K : Type) [Field K] (ev : V₁ →+* K) (k₀ : Subfield K) (hk : ∀ a, ev (ρ (ib a)) ∈ k₀) :
    ∀ mu a, DefOver k₀ (spMap ev ≫ (D.c (e mu) ≫ pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) ≫ β) := by
  intro mu a
  have h : spMap ev ≫ (D.c (e mu) ≫ pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) ≫ β =
      spMap ((ev.comp ρ).comp ib) ≫ (c₀ (mu a)).left := by
    rw [reassoc_of% (hc mu a), hβc, ← spMap_three]
    simp only [Category.assoc]
  rw [h]
  refine ⟨spMap (((ev.comp ρ).comp ib).codRestrict k₀ hk) ≫ (c₀ (mu a)).left, ?_⟩
  rw [← Category.assoc]
  congr 1
  simp only [spMap, ← Spec.map_comp]; rfl

theorem sharp_torsion_defOver {W₀ : Type} [CommRing W₀] [IsNoetherianRing V₁] (ρ : V →+* V₁) (ib : W₀ →+* V)
    (Q : Data V) (D : DegPre V₁)
    (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B)) (hpr : ∀ a, IsMonHom (pr a))
    (huniv : ∀ (T : Over (Sp V₁)) (y : Fin 8 → (T ⟶ (Over.pullback (spMap ρ)).obj Q.B)),
      ∃! x : T ⟶ D.P.A, ∀ a, x ≫ pr a = y a)
    (B₀ : Over (Sp W₀)) [GrpObj B₀] (β : Q.B.left ⟶ B₀.left) (hβ : IsGrpPullback Q.B B₀ (spMap ib) β)
    (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K) (hk₀ : IsAlgClosed k₀)
    (hk : ∀ a, ev (ρ (ib a)) ∈ k₀) (N : ℕ) (hN : 1 ≤ N) (hNu : IsUnit (N : V₁))
    (x : Over.mk (spMap ev) ⟶ D.P.A) (hx : x ^ N = 1) (a : Fin 8) :
    DefOver k₀ (x.left ≫ (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) ≫ β) := by
  classical
  obtain ⟨Φ, hΦ⟩ := exists_points_equiv ρ ib Q D pr hpr huniv B₀ β hβ (spMap ev) (spMap ((ev.comp ρ).comp ib))
    (spMap_three _ _ _)
  have hNK : (N : K) ≠ 0 := by
    have := (hNu.map ev).ne_zero
    simpa using this
  have hcard := (GlobalTheory.abelianSchemeLaws_all.1.mulN (Sp V₁) D.P N hN).2.2.2.2 K (spMap ev) hNK
  have hfin : Finite {y : Over.mk (spMap ev) ⟶ D.P.A // y ^ N = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (by omega))
  refine defOver_of_finite_orbit K k₀ hk₀ _ _ ((Set.finite_range fun y : {y : Over.mk (spMap ev) ⟶ D.P.A // y ^ N = 1} =>
    (Φ y.1 a).left).subset ?_)
  rintro _ ⟨σ, hσ, rfl⟩
  have hσf : spMap σ.toRingHom ≫ spMap ((ev.comp ρ).comp ib) = spMap ((ev.comp ρ).comp ib) := by
    simp only [spMap, ← Spec.map_comp]
    congr 2
    ext w
    exact hσ _ (hk w)
  let h : Over.mk (spMap ((ev.comp ρ).comp ib)) ⟶ Over.mk (spMap ((ev.comp ρ).comp ib)) :=
    Over.homMk (spMap σ.toRingHom) hσf
  refine ⟨⟨Φ.symm (fun b => h ≫ Φ x b), ?_⟩, ?_⟩
  · have e : (fun b => h ≫ Φ x b) ^ N = 1 := by
      funext b
      rw [Pi.pow_apply, ← MonObj.comp_pow, ← Pi.pow_apply, ← map_pow, hx, map_one, Pi.one_apply, MonObj.comp_one]
    rw [← map_pow, e, map_one]
  · show (Φ (Φ.symm fun b => h ≫ Φ x b) a).left = _
    rw [MulEquiv.apply_symm_apply, Over.comp_left, hΦ]
    rfl

end GlobalTheory.Poinc.Sep
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.HalfEx

theorem kappa_unique (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] (ρ : R →+* R')
    (κ κ' : (TK R').left ⟶ (TK R).left) (h : κ ≫ jK R = jK R' ≫ spMap ρ) (h' : κ' ≫ jK R = jK R' ≫ spMap ρ) :
    κ = κ' := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective κ
  obtain ⟨φ', rfl⟩ := Spec.map_surjective κ'
  have e : Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)) ≫ φ) =
      Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)) ≫ φ') := by
    rw [Spec.map_comp, Spec.map_comp]; exact h.trans h'.symm
  have e' := Spec.map_injective e
  congr 1
  ext x
  have := IsLocalization.ringHom_ext (nonZeroDivisors R) (j := φ.hom) (k := φ'.hom)
    (congrArg CommRingCat.Hom.hom e')
  exact congrArg (fun q => q x) this

theorem half_exists : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] [IsNoetherianRing R'] (Q : Data R) (ρ : R →+* R') (P : PolAV (Sp R')) (β : P.A.left ⟶ Q.B.left) (β₂ : (G2 P.A).left ⟶ (G2 Q.B).left), Function.Injective ρ → IsGrpPullback P.A Q.B (spMap ρ) β → IsSquare β β₂ → (letI := P.isAb.comm; LBIso (abelian₂ P.A P.L) ((abelian₂ Q.B Q.M.L).pull β₂)) → ∃ (D : DegPre R') (e : D.X ≃+ Q.X) (f : D.X → D.X → (FractionRing R')ˣ), Half Q ρ D e f := by
  intro R _ _ R' _ _ _ _ Q ρ P β β₂ hρ hpb hsq hiso
  obtain ⟨rig, hrig⟩ := P.rigid
  obtain ⟨cub⟩ := (GlobalTheory.T.all_six_abelian_scheme_laws_hold.1.cube _ P ⟨P.L, rig, P.isLB, hrig⟩ rfl).1
  obtain ⟨sym, hsym, hsr⟩ := GlobalTheory.SelfUnif.exists_sym P
  have hF := hpb.1
  obtain ⟨c, hc⟩ : ∃ c : Q.X → (𝟙_ (Over (Sp R')) ⟶ P.A), ∀ x,
      (c x).left ≫ β = spMap ρ ≫ (Q.c x).left :=
    ⟨fun x => Over.homMk (hF.lift (spMap ρ ≫ (Q.c x).left) (𝟙 _) (by
      rw [Category.assoc, Over.w, Category.id_comp]; exact Category.comp_id _)) (hF.lift_snd _ _ _),
      fun x => hF.lift_fst _ _ _⟩
  have cadd : ∀ a b, c (a + b) = padd P.A (c a) (c b) := fun a b => by
    refine Over.OverMorphism.ext (hF.hom_ext ?_ (by rw [Over.w, Over.w]))
    have u : (toUnit (Over.mk ((𝟙_ (Over (Sp R'))).hom ≫ spMap ρ))).left = spMap ρ :=
      Category.id_comp _
    have m := hpb.2 _ (c a) (c b) (toUnit _ ≫ Q.c a) (toUnit _ ≫ Q.c b)
      (by rw [hc, Over.comp_left, u]) (by rw [hc, Over.comp_left, u])
    rw [← MonObj.comp_mul, Over.comp_left, u] at m
    rw [hc, Q.c_add]
    exact m
  choose psi hpsi using fun x : Q.X => GlobalTheory.SS.HtForm.gen_field _
    (DVR.linComb_isLB P.L P.isLB (K := PUnit) (fun _ => ptK (c x)) (fun _ => -1))
  let D : DegPre R' :=
    { P := P, rig := rig, rig_gen := hrig, cub := cub, sym := sym, sym_gen := hsym, sym_rig := hsr, X := Q.X,
      c := c, c_add := cadd, psi := psi, psi_gen := hpsi }
  obtain ⟨w, hw, hw1⟩ := GlobalTheory.T.exists_mumfordBundleIso_value_one_origin_polarised R R' Q ρ P β β₂ hpb hsq hiso
  have hR := GlobalTheory.T.exists_fraction_constant_period_ratio_polarised R R' Q ρ D (AddEquiv.refl _) β β₂ w hpb hsq hw hc
  classical
  let f : D.X → D.X → (FractionRing R')ˣ := fun a b =>
    if h : ∃ κ : (TK R').left ⟶ (TK R).left, κ ≫ jK R = jK R' ≫ spMap ρ then
      (hR h.choose h.choose_spec a b).choose else 1
  refine ⟨D, AddEquiv.refl _, f, β, β₂, w, hpb, hsq, hw, hw1, hc, ?_⟩
  intro κ hκ a b z J J' hJ hJ'
  have h : ∃ κ : (TK R').left ⟶ (TK R).left, κ ≫ jK R = jK R' ≫ spMap ρ := ⟨κ, hκ⟩
  have e := kappa_unique R R' ρ _ _ h.choose_spec hκ
  have := (hR h.choose h.choose_spec a b).choose_spec z J J' hJ hJ'
  simp only [f, dif_pos h]
  rw [← e]
  exact this

end GlobalTheory.HalfEx
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MonoTriv

open GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues Formalism.L2.Pj

theorem psiCoord_zero {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (hB : D.TauBimult)
    (x : (FractionRing R)ˣ) (hx : IsPsiCoord D 0 x) :
    ∃ u : Rˣ, (x : FractionRing R) = algebraMap R (FractionRing R) u := by
  obtain ⟨j, hj⟩ := PsiCoordLocal.exists_chart_top D 0
  have h := PsiCoordLocal.generic_le D 0 j hj
  have hU := PsiCoordLocal.psiUnitOn_zero D hB
  obtain ⟨s, -, e⟩ := hU j ⊤ (isAffineOpen_top _) (Set.subset_univ _) hj h
  obtain ⟨r, rfl⟩ := PsiCoordLocal.toOpen_top_bijective.2 s
  have hr : PsiCoord D 0 r := ⟨j, hj, h, e⟩
  have hu : IsUnit r := IsLocalRing.notMem_maximalIdeal.1
    (PsiCoordLocal.not_mem_of_coord (𝔭 := closedPoint R) isOpen_univ trivial hU hr)
  obtain ⟨x₀, hx₀, e₀⟩ := (GlobalTheory.PeriodFormCompare.psiCoord_iff D 0 r).1 hr
  obtain ⟨v, hv⟩ := IsPsiCoord.unique hx hx₀
  refine ⟨v * hu.unit, ?_⟩
  rw [hv, Units.val_mul, e₀, Units.val_mul, IsUnit.unit_spec, map_mul]
  rfl

theorem exists_unit_of_sq {R : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (g : FractionRing R) (w : Rˣ)
    (h : g ^ 2 = algebraMap R (FractionRing R) w) : ∃ a : Rˣ, g = algebraMap R (FractionRing R) a := by
  have hw : algebraMap R (FractionRing R) (w : R) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 w.ne_zero
  have hg : g ≠ 0 := by rintro rfl; exact hw (by rw [← h]; ring)
  have int : ∀ (g : FractionRing R) (w : Rˣ), g ^ 2 = algebraMap R (FractionRing R) w →
      ∃ a : R, algebraMap R (FractionRing R) a = g := fun g w h => by
    refine IsIntegrallyClosed.isIntegral_iff.1 ⟨Polynomial.X ^ 2 - Polynomial.C (w : R),
      Polynomial.monic_X_pow_sub_C _ two_ne_zero, ?_⟩
    simp [h]
  obtain ⟨a, ha⟩ := int g w h
  obtain ⟨b, hb⟩ := int g⁻¹ w⁻¹ (by
    rw [inv_pow, h]
    exact inv_eq_of_mul_eq_one_right (by rw [← map_mul, Units.mul_inv, map_one]))
  have hab : a * b = 1 := IsFractionRing.injective R (FractionRing R) (by
    rw [map_mul, ha, hb, mul_inv_cancel₀ hg, map_one])
  exact ⟨⟨a, b, hab, by rw [mul_comm, hab]⟩, ha.symm⟩

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] (Q : Data R) (ρ : R →+* R') (D : DegPre R') (e : D.X ≃+ Q.X) [IsLocalRing R'] (m : ℕ) (t : Fin m → R) (r : Fin m → R') (δ : Fin m → LinearMap.BilinForm ℤ Q.X), IsCN R' → Function.Injective ρ → Half Q ρ D e (fun _ _ => 1) → D.PsiEven → D.TauBimult → Q.IsMonomialTau t δ → (∀ i y, 0 ≤ δ i y y) → (∀ i, t i ≠ 0) → (∀ i, r i ^ 2 = ρ (t i)) → IsMonomial D r fun i => (2 : ℤ) • pull e.toIntLinearEquiv.toLinearMap (δ i) := by
  intro R _ _ R' _ _ Q ρ D e _ m t r δ hCN hρ hH hE hB hQ hδ ht hr y
  haveI : IsIntegrallyClosed R' := hCN.2.1
  set n : Fin m → ℕ := fun i => (δ i (e y) (e y)).toNat with hn_def
  have hn : ∀ i, δ i (e y) (e y) = n i := fun i => (Int.toNat_of_nonneg (hδ i (e y))).symm
  obtain ⟨x, hx⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R' D y (-y)
  obtain ⟨k, hk, hkc⟩ := hQ (e y) (e (-y))
  obtain ⟨u₁, hu₁⟩ := GlobalTheory.T.refining_degenerationData_tauCoordinate_unit R R' Q ρ D e hρ hH.refines y (-y) k hkc x hx
  have h0 : IsPsiCoord D (y + -y) (psiCoord D 0) := by rw [add_neg_cancel]; exact psiCoord_spec D 0
  obtain ⟨u₂, hu₂⟩ := GlobalTheory.T.tauCoordinate_eq_unit_mul_psi_quotient R' D y (-y) x _ _ _ hx h0 (psiCoord_spec D y) (psiCoord_spec D (-y))
  obtain ⟨u₃, hu₃⟩ := GlobalTheory.T.psiEven_coordinates_neg_differ_by_unit R' D hE y _ _ (psiCoord_spec D y) (psiCoord_spec D (-y))
  obtain ⟨u₄, hu₄⟩ := psiCoord_zero D hB _ (psiCoord_spec D 0)
  set X : FractionRing R' := (psiCoord D y : FractionRing R') with hX
  have hX0 : X ≠ 0 := (psiCoord D y).ne_zero
  have hσ : ∀ s, IsFractionRing.lift (A := R) (K := FractionRing R)
      (g := (algebraMap R' (FractionRing R')).comp ρ) ((IsFractionRing.injective R' (FractionRing R')).comp hρ) (algebraMap R (FractionRing R) s) =
      algebraMap R' (FractionRing R') (ρ s) := fun s => IsFractionRing.lift_algebraMap _ s
  have hneg : ∀ i, δ i (e y) (e (-y)) = -(n i : ℤ) := fun i => by
    rw [map_neg, map_neg, hn]
  have hr0 : ∀ i, algebraMap R' (FractionRing R') (r i) ≠ 0 := fun i h => by
    have : algebraMap R' (FractionRing R') (ρ (t i)) = 0 := by rw [← hr i, map_pow, h, zero_pow two_ne_zero]
    exact ht i (hρ ((IsFractionRing.injective R' (FractionRing R')) (by rw [this, map_zero, map_zero])))
  set P : FractionRing R' := ∏ i, algebraMap R' (FractionRing R') (r i) ^ n i with hP
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (hr0 i)
  have hk' : IsFractionRing.lift (A := R) (K := FractionRing R)
      (g := (algebraMap R' (FractionRing R')).comp ρ) ((IsFractionRing.injective R' (FractionRing R')).comp hρ) (k : FractionRing R) = (P ^ 2)⁻¹ := by
    rw [hk, map_prod, hP, ← Finset.prod_pow, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_zpow₀, hσ, hneg, ← hr i, map_pow, zpow_neg, zpow_natCast, ← pow_mul, ← pow_mul, mul_comm]
  rw [hk'] at hu₁
  rw [hu₄, hu₃] at hu₂
  have hsq : (X / P) ^ 2 = algebraMap R' (FractionRing R') (u₂ * u₄ * u₃⁻¹ * u₁⁻¹ : R'ˣ) := by
    have h1 := hu₁.symm.trans hu₂
    have hu : ∀ u : R'ˣ, algebraMap R' (FractionRing R') (u : R') ≠ 0 := fun u =>
      (map_ne_zero_iff _ (IsFractionRing.injective R' (FractionRing R'))).2 u.ne_zero
    simp only [Units.val_mul, map_mul, map_units_inv]
    have := hu u₁; have := hu u₂; have := hu u₃; have := hu u₄
    have h1' : algebraMap R' (FractionRing R') (u₁ : R') = algebraMap R' (FractionRing R') (u₂ : R') *
        algebraMap R' (FractionRing R') (u₄ : R') * X⁻¹ * (algebraMap R' (FractionRing R') (u₃ : R') * X)⁻¹ * P ^ 2 := by
      rw [← h1, inv_mul_cancel_right₀ (pow_ne_zero 2 hP0)]
    rw [h1']
    field_simp
  obtain ⟨a, ha⟩ := exists_unit_of_sq (X / P) _ hsq
  have hcoord : PsiCoord D y (a * ∏ i, r i ^ n i) := (GlobalTheory.PeriodFormCompare.psiCoord_iff D y _).2
    ⟨psiCoord D y, psiCoord_spec D y, by
      rw [map_mul, map_prod, ← ha]; simp only [map_pow]; rw [← hP, div_mul_cancel₀ _ hP0]⟩
  refine ⟨a, n, fun i => ?_, hcoord⟩
  simp [pull, hn]

end GlobalTheory.MonoTriv
end
