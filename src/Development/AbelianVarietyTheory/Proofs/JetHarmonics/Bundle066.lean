module

public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle025
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle009
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle039
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThreePointSeriesExponentialOfDefect
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle045
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle006
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle029
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle058
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Jets.SupWOfSup
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FormalPoint

namespace GlobalTheory.AdicColimit


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry in
theorem _root_.GlobalTheory.AdicColimit.isAdicColimit_spec_of_isLocalRing (R : Type) [CommRing R] (I : Ideal R) (A : Type) [CommRing A]
    [IsLocalRing A] (φ : R →+* A) (hA : IsAdicComplete (I.map φ) A) :
    _root_.GlobalTheory.AdicColimit.IsAdicColimit I (Over.mk (Spec.map (CommRingCat.ofHom φ))) := by
  have hthick : ∀ e : ℕ, _root_.ReciprocityTheory.ChartRestriction.G.Out.thickTrans R I e ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I (e + 1) = _root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e := by
    intro e
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Out.thickTrans _root_.ReciprocityTheory.ChartRestriction.G.Out.thick
    rw [← Spec.map_comp]
    rfl
  have hPV : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ = Spec.map (CommRingCat.ofHom φ) := rfl
  have hC : ∀ e, _root_.GlobalTheory.AdicColimit.thickι I e (Over.mk (Spec.map (CommRingCat.ofHom φ))) =
      pullback.fst (Spec.map (CommRingCat.ofHom φ)) (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e) := fun e => rfl
  have hD_fst : ∀ e, _root_.ReciprocityTheory.ChartRestriction.G.Out.thickMap R I e (Over.mk (Spec.map (CommRingCat.ofHom φ))) ≫
      pullback.fst (Spec.map (CommRingCat.ofHom φ)) (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I (e + 1)) =
      pullback.fst (Spec.map (CommRingCat.ofHom φ)) (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e) := by
    intro e; exact pullback.lift_fst _ _ _
  have hD_snd : ∀ e, _root_.ReciprocityTheory.ChartRestriction.G.Out.thickMap R I e (Over.mk (Spec.map (CommRingCat.ofHom φ))) ≫
      pullback.snd (Spec.map (CommRingCat.ofHom φ)) (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I (e + 1)) =
      pullback.snd (Spec.map (CommRingCat.ofHom φ)) (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e) ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thickTrans R I e := by
    intro e
    exact pullback.lift_snd _ _ _
  have hcond : ∀ e, pullback.fst (Spec.map (CommRingCat.ofHom φ)) (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e) ≫
      Spec.map (CommRingCat.ofHom φ) =
      pullback.snd (Spec.map (CommRingCat.ofHom φ)) (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e) ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e :=
    fun e => pullback.condition
  have hq : ∀ e, _root_.GlobalTheory.FormalPoint.levelMap I φ e ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e =
      _root_.GlobalTheory.adicLevelι (I.map φ) (e + 1) ≫ Spec.map (CommRingCat.ofHom φ) := fun e => by
    rw [_root_.GlobalTheory.FormalPoint.levelMap_thick, hPV]
  obtain ⟨s, hs_fst, hs_snd⟩ : ∃ s : ∀ e : ℕ, Spec (CommRingCat.of (A ⧸ I.map φ ^ (e + 1))) ⟶
      pullback (Spec.map (CommRingCat.ofHom φ)) (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e),
      (∀ e, s e ≫ pullback.fst _ _ = _root_.GlobalTheory.adicLevelι (I.map φ) (e + 1)) ∧
      (∀ e, s e ≫ pullback.snd _ _ = _root_.GlobalTheory.FormalPoint.levelMap I φ e) :=
    ⟨fun e => pullback.lift _ _ (hq e).symm, fun e => pullback.lift_fst _ _ _,
      fun e => pullback.lift_snd _ _ _⟩
  have hsec : ∀ e, ∃ l, l ≫ s e = 𝟙 _ := by
    intro e
    obtain ⟨l, hl⟩ := _root_.GlobalTheory.FormalPoint.exists_factor_level I φ
      (pullback.fst (Spec.map (CommRingCat.ofHom φ)) (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e))
      (pullback.snd _ _) (by rw [hPV]; exact hcond e)
    refine ⟨l, ?_⟩
    apply pullback.hom_ext
    · rw [Category.assoc, hs_fst, Category.id_comp, hl]
    · rw [← cancel_mono (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e), Category.assoc, Category.assoc, ← Category.assoc (s e), hs_snd, hq,
        ← Category.assoc, hl, Category.id_comp, hcond]
  intro X f hf
  have hfam : _root_.GlobalTheory.IsAdicFamily (I.map φ) (fun e => s e ≫ f e) := by
    intro n
    have hmap : _root_.GlobalTheory.adicLevelMap (I.map φ) (by omega : n + 1 ≤ n + 1 + 1) ≫ s (n + 1) =
        s n ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thickMap R I n (Over.mk (Spec.map (CommRingCat.ofHom φ))) := by
      apply pullback.hom_ext
      · rw [Category.assoc, hs_fst, _root_.GlobalTheory.adicLevelMap_ι, Category.assoc, hD_fst, hs_fst]
      · rw [← cancel_mono (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I (n + 1))]
        simp only [Category.assoc]
        rw [← Category.assoc (s (n + 1)), hs_snd, hq, _root_.GlobalTheory.adicLevelMap_ι_assoc, ← Category.assoc (_root_.ReciprocityTheory.ChartRestriction.G.Out.thickMap R I n (Over.mk (Spec.map (CommRingCat.ofHom φ)))), hD_snd,
          Category.assoc, hthick, ← Category.assoc, hs_snd, hq]
    show _root_.GlobalTheory.adicLevelMap (I.map φ) _ ≫ s (n + 1) ≫ f (n + 1) = s n ≫ f n
    rw [← Category.assoc, hmap, Category.assoc, hf]
  haveI := hA
  obtain ⟨g, hg, hgu⟩ := _root_.GlobalTheory.existsUnique_of_isAdicFamily hfam
  have key : ∀ y : Spec (CommRingCat.of A) ⟶ X,
      (∀ e, _root_.GlobalTheory.AdicColimit.thickι I e (Over.mk (Spec.map (CommRingCat.ofHom φ))) ≫ y = f e) ↔
      (∀ n, _root_.GlobalTheory.adicLevelι (I.map φ) (n + 1) ≫ y = s n ≫ f n) := by
    intro y
    constructor
    · intro hy n
      rw [← hs_fst, Category.assoc, ← hC, hy]
    · intro hy e
      obtain ⟨l, hl⟩ := hsec e
      have h1 : _root_.GlobalTheory.AdicColimit.thickι I e (Over.mk (Spec.map (CommRingCat.ofHom φ))) =
          l ≫ _root_.GlobalTheory.adicLevelι (I.map φ) (e + 1) := by
        rw [← hs_fst, ← Category.assoc, hl, Category.id_comp, hC]
      rw [h1, Category.assoc, hy, ← Category.assoc, hl]
      exact Category.id_comp _
  exact ⟨g, (key g).2 hg, fun y hy => hgu y ((key y).1 hy)⟩

end GlobalTheory.AdicColimit
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FieldBaseChange (constVal isoVal)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Jets

theorem units_mul_pow_mul_inv_cancel {R : Type} [CommRing R] (x y m : Rˣ) (s : R) :
    x.val * s * (y * x⁻¹ * m).val = y.val * (m.val * s) := by
  rw [Units.val_mul, Units.val_mul]
  linear_combination (s * y.val * m.val) * x.mul_inv

theorem ring_relation_transfer_identity {R : Type} [CommRing R] {t t' m m' e : R} (E : t' * m = e * (t * m')) (x y y' : R) :
    y' * t' * (y * x * m) = e * (y * t * (y' * x * m')) := by
  linear_combination (x * y * y') * E

theorem sval_of_isoRelM {Y Y' X₁ X₂ Z₁ Z : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    {w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)} {m : Y' ⟶ Y} {k : ℕ} {g₁ : Z₁ ⟶ X₁} {h₁ : Y' ⟶ Z₁}
    {a : LB.Sec (LB.LinComb L₁ (K := Fin 1) (fun _ => g₁) (fun _ => (k : ℤ)))}
    {b : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => m ≫ f₂) (fun _ => (k : ℤ)))}
    (H : GeneratorPullback.IsoRelM L₁ L₂ f₁ f₂ w m k g₁ h₁ a (m ≫ f₂) (𝟙 _) b) (r : Z ⟶ Y') (z : Z) {J₂} {J₁}
    (hJ₂ : Good L₂ z J₂) (hJ₁ : Good L₁ z J₁) :
    sval b r z J₂ = (isoVal w (r ≫ m) z (J₂ ((r ≫ m) ≫ f₂)) (J₁ ((r ≫ m) ≫ f₁)) ^ (k : ℤ)).val *
      sval a (r ≫ h₁) z J₁ := by
  have := (GlobalTheory.FieldBaseChange.isoRelM_iff w m k h₁ H.1 _ H.2.1 a b).1 H Z r z _ _
    (hJ₂ ((r ≫ m) ≫ f₂)) (hJ₁ ((r ≫ m) ≫ f₁))
  rw [Category.comp_id] at this
  rw [GlobalTheory.FieldBaseChange.sval_eq_powVal, GlobalTheory.FieldBaseChange.sval_eq_powVal, Category.assoc r h₁, H.1,
    ← Category.assoc r m f₁, ← Category.assoc r m f₂]
  exact this

theorem eigen_transfer {S X : Scheme.{0}} {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] (e : B ≅ A)
    [IsMonHom e.hom] {L₁ : LB A.left} {L₂ : LB X} (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB) (f : B.left ⟶ X)
    {K : Type} [Field K] (p : Spec (CommRingCat.of K) ⟶ S) (φ : X ⟶ X) (b : B ⟶ B) (hφ : b.left ≫ f = f ≫ φ)
    (a : A ⟶ A) (ha : IsMonHom a) (hb : b ≫ e.hom = e.hom ≫ a) (N k : ℕ)
    (mu : LB.Gen (LB.LinComb L₂ (K := Fin 2) ![𝟙 X, φ] ![(N : ℤ), -1])) (hmu : mu.IsGen)
    (w : LB.Iso (L₁.pull e.hom.left) (L₂.pull f)) (hw : w.IsGen)
    (σ₀ : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => (snd (Over.mk p) B).left ≫ f) (fun _ => (k : ℤ))))
    (σ' τ : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => (snd (Over.mk p) B).left ≫ f)
      (fun _ => ((k * N : ℕ) : ℤ))))
    (t' t : LB.Sec (LPow A L₁ ((k * N : ℕ) : ℤ) (Over.mk p)))
    (h₀ : ∀ (y : (Over.mk p ⊗ B).left) (J), Good L₂ y J → sval σ' (𝟙 _) y J =
      sval σ₀ (Over.mk p ◁ b).left y J * (val mu ((snd (Over.mk p) B).left ≫ f) y J).val ^ k)
    (h₁ : GeneratorPullback.IsoRelM L₁ L₂ e.hom.left f w (snd (Over.mk p) B).left (k * N) (snd (Over.mk p) A).left
      (lift (fst (Over.mk p) B) (snd (Over.mk p) B ≫ e.hom)).left t' ((snd (Over.mk p) B).left ≫ f) (𝟙 _) σ')
    (h₂ : GeneratorPullback.IsoRelM L₁ L₂ e.hom.left f w (snd (Over.mk p) B).left (k * N) (snd (Over.mk p) A).left
      (lift (fst (Over.mk p) B) (snd (Over.mk p) B ≫ e.hom)).left t ((snd (Over.mk p) B).left ≫ f) (𝟙 _) τ)
    (θ : ThetaGrp A L₁ ((k * N : ℕ) : ℤ) (Over.mk p)) (hθ : IsActOf A L₁ ((k * N : ℕ) : ℤ) θ t' t)
    (c : Over.mk p ⟶ A) (u : Γ((Over.mk p).left, ⊤)ˣ) (hc : c ≫ a = 1)
    (hW : WeilIs A L₁ ((k * N : ℕ) : ℤ) c θ.pt u)
    (Z : Scheme.{0}) (ρ : Z ⟶ (Over.mk p ⊗ B).left) (z : Z) (J) (hJ : Good L₂ z J) :
    sval τ (ρ ≫ (translT B (c ≫ e.inv)).left) z J * (val mu (ρ ≫ (snd (Over.mk p) B).left ≫ f) z J).val ^ k =
      gs (ρ ≫ (fst (Over.mk p) B).left) z ⊤ u.val * (sval τ ρ z J *
        (val mu ((ρ ≫ (translT B (c ≫ e.inv)).left) ≫ (snd (Over.mk p) B).left ≫ f) z J).val ^ k) := by
  obtain ⟨g, hg⟩ : ∃ g, g = lift (fst (Over.mk p) B) (snd (Over.mk p) B ≫ e.hom) := ⟨_, rfl⟩
  rw [← hg] at h₁ h₂
  have g₁ : g ≫ fst _ _ = fst _ _ := by rw [hg, lift_fst]
  have g₂ : g ≫ snd _ _ = snd _ _ ≫ e.hom := by rw [hg, lift_snd]
  let n : Over.mk p ⊗ A ⟶ Over.mk p ⊗ B := lift (fst _ _) (snd _ _ ≫ e.inv)
  have hn : n ≫ g = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [n, g₁, g₂]
  have hn' : g ≫ n = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [n, g₁, reassoc_of% g₂]
  have hb' : a ≫ e.inv = e.inv ≫ b := by
    rw [Iso.comp_inv_eq, Category.assoc, hb, e.inv_hom_id_assoc]
  have gb : Over.mk p ◁ b ≫ g = g ≫ Over.mk p ◁ a := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [g₁, g₂, reassoc_of% g₂, hb]
  have gt : translT B (c ≫ e.inv) ≫ g = g ≫ translT A c := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [translT, g₁]
    · rw [Category.assoc, Category.assoc, g₂, translT, translT, lift_snd_assoc, lift_snd]
      show ((fst _ B ≫ c ≫ e.inv) * snd _ B) ≫ e.hom = g ≫ ((fst _ A ≫ c) * snd _ A)
      rw [MonObj.mul_comp, MonObj.comp_mul, g₂, reassoc_of% g₁]
      simp
  have tb : translT B (c ≫ e.inv) ≫ snd _ _ ≫ b = snd _ _ ≫ b := by
    rw [← cancel_mono e.hom]
    simp only [Category.assoc]
    rw [hb, ← reassoc_of% g₂, reassoc_of% gt, GlobalTheory.KernelEigen.translT_snd_comp a hc]
  obtain ⟨s, hs⟩ := ((GlobalTheory.FieldBaseChange.isoRelM_bijective (k := k) (m := (snd (Over.mk p) B).left)
    (g₁ := (snd (Over.mk p) A).left) (h₁ := g.left) hL₁ hL₂ hw (congrArg (fun q => q.left) g₂) n.left
    (congrArg (fun q => q.left) hn) (congrArg (fun q => q.left) hn')).2 σ₀).exists
  obtain ⟨ν, hν, vν⟩ := exists_gen hL₂ (K' := Fin 2) (φ' := ![𝟙 X, φ]) (ε' := ![((k * N : ℕ) : ℤ), -(k : ℤ)])
    (fun U _ h => by simp [Fin.prod_univ_two]) (GeneratorPullback.powGen L₂ _ _ mu k) (GlobalTheory.FrameGeo.powGen_isGen _ _ _ _ hmu k)
  obtain ⟨mA, hmA, vmA⟩ := exists_gen_move_back _ _ _ _ _ L₁ L₂ hL₁ hL₂ _ _ w hw (Fin 2)
    ![(snd (Over.mk p) A ≫ e.inv).left, (snd (Over.mk p) A ≫ a ≫ e.inv).left] _
    ![(snd (Over.mk p) A).left, (snd (Over.mk p) A ≫ a).left]
    (fun i => by
      fin_cases i
      · show (snd (Over.mk p) A).left = (snd (Over.mk p) A ≫ e.inv).left ≫ e.hom.left
        rw [← Over.comp_left, Category.assoc, e.inv_hom_id, Category.comp_id]
      · show (snd (Over.mk p) A ≫ a).left = (snd (Over.mk p) A ≫ a ≫ e.inv).left ≫ e.hom.left
        rw [← Over.comp_left, Category.assoc, Category.assoc, e.inv_hom_id, Category.comp_id])
    _ ((snd (Over.mk p) A ≫ e.inv).left ≫ f)
    (fun i => by
      fin_cases i
      · exact Category.comp_id _
      · show ((snd (Over.mk p) A ≫ e.inv).left ≫ f) ≫ φ = (snd (Over.mk p) A ≫ a ≫ e.inv).left ≫ f
        rw [Category.assoc, ← hφ, ← Category.assoc, ← Over.comp_left, Category.assoc, hb'])
    ν hν
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ (Over.mk p ⊗ B).left) (z : Z) (J₂) (J₁), Good L₂ z J₂ → Good L₁ z J₁ →
      val mu (r ≫ (snd (Over.mk p) B).left ≫ f) z J₂ ^ k =
        isoVal w (r ≫ (snd (Over.mk p) B).left) z (J₂ ((r ≫ (snd (Over.mk p) B).left) ≫ f))
          (J₁ ((r ≫ (snd (Over.mk p) B).left) ≫ e.hom.left)) ^ ((k * N : ℕ) : ℤ) *
        (isoVal w (r ≫ (snd (Over.mk p) B ≫ b).left) z (J₂ ((r ≫ (snd (Over.mk p) B ≫ b).left) ≫ f))
          (J₁ ((r ≫ (snd (Over.mk p) B ≫ b).left) ≫ e.hom.left)) ^ (k : ℤ))⁻¹ * val mA (r ≫ g.left) z J₁ := by
    intro Z r z J₂ J₁ hJ₂ hJ₁
    have e₀ : (r ≫ g.left) ≫ (snd (Over.mk p) A ≫ e.inv).left = r ≫ (snd (Over.mk p) B).left := by
      rw [Category.assoc, ← Over.comp_left, reassoc_of% g₂, e.hom_inv_id, Category.comp_id]
    have e₁ : (r ≫ g.left) ≫ (snd (Over.mk p) A ≫ a ≫ e.inv).left = r ≫ (snd (Over.mk p) B ≫ b).left := by
      rw [Category.assoc, ← Over.comp_left, reassoc_of% g₂, hb', e.hom_inv_id_assoc]
    have := vmA Z (r ≫ g.left) z J₂ J₁ hJ₂ hJ₁
    rw [vν _ _ z J₂ hJ₂, GlobalTheory.FrameGeo.val_powGen, Fin.prod_univ_two, ← Category.assoc, e₀, Category.assoc] at this
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, e₀, e₁, zpow_neg] at this
    exact this
  have hσ := secRel_iff hL₂ _ _ σ' _ _ σ₀ (Over.mk p ◁ b).left _ _
    (LB.pullGen L₂ _ _ (GeneratorPullback.powGen L₂ _ _ mu k) ((snd (Over.mk p) B).left ≫ f))
  have h₀' := hσ.1 (hσ.2 fun y J hJ => by
    rw [h₀ y J hJ, val_pull hJ, GlobalTheory.FrameGeo.val_powGen, Category.id_comp, Category.id_comp,
      Units.val_pow_eq_pow_val])
  choose J₁ hJ₁ using fun χ : Z ⟶ A.left => exists_chart hL₁ (χ z)
  have E := GlobalTheory.translate_pullback_eigensection S A L₁ hL₁ K p a ha N k mA hmA s t' t (fun y I₁ hI₁ => by
    choose I₂ hI₂ using fun χ : (Over.mk p ⊗ A).left ⟶ X => exists_chart hL₂ (χ y)
    have ng : n.left ≫ g.left = 𝟙 _ := congrArg (fun q => q.left) hn
    have e₁ : (n.left ≫ (Over.mk p ◁ b).left) ≫ g.left = (Over.mk p ◁ a).left := by
      rw [← Over.comp_left, ← Over.comp_left, Category.assoc, gb, reassoc_of% hn]
    have e₂ : (n.left ≫ (Over.mk p ◁ b).left) ≫ (snd (Over.mk p) B).left =
        n.left ≫ (snd (Over.mk p) B ≫ b).left := by
      rw [Category.assoc, ← Over.comp_left, whiskerLeft_snd]
    have := h₀' _ n.left y I₂ hI₂
    rw [val_pull hI₂, GlobalTheory.FrameGeo.val_powGen, hv _ _ y I₂ I₁ hI₂ hI₁, sval_of_isoRelM h₁ _ y hI₂ hI₁,
      sval_of_isoRelM hs _ y hI₂ hI₁, ng, e₁, e₂] at this
    refine (Units.mul_right_inj _).1 (this.trans ?_)
    exact units_mul_pow_mul_inv_cancel _ _ _ _) θ hθ c u hc hW Z (ρ ≫ g.left) z J₁ hJ₁
  have e₁ : (ρ ≫ (translT B (c ≫ e.inv)).left) ≫ g.left = (ρ ≫ g.left) ≫ (translT A c).left := by
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, gt]
  have e₂ : (ρ ≫ (translT B (c ≫ e.inv)).left) ≫ (snd (Over.mk p) B ≫ b).left =
      ρ ≫ (snd (Over.mk p) B ≫ b).left := by
    rw [Category.assoc, ← Over.comp_left, tb]
  have e₃ : (ρ ≫ g.left) ≫ (fst (Over.mk p) A).left = ρ ≫ (fst (Over.mk p) B).left := by
    rw [Category.assoc, ← Over.comp_left, g₁]
  rw [e₃] at E
  rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, hv _ _ z J J₁ hJ hJ₁, hv _ _ z J J₁ hJ hJ₁,
    sval_of_isoRelM h₂ _ z hJ hJ₁, sval_of_isoRelM h₂ _ z hJ hJ₁, e₁, e₂]
  simp only [Units.val_mul]
  exact ring_relation_transfer_identity E _ _ _

theorem eigen_equation_generic : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (φ : G ⟶ G) (a : A.A ⟶ A.A), IsMonHom a → (Over.pullback (jK R)).map φ ≫ U.gen.hom = U.gen.hom ≫ a → ∀ (N k : ℕ) (mu : LB.Gen (LB.LinComb U.LG.L (K := Fin 2) ![𝟙 G.left, φ.left] ![(N : ℤ), -1])), mu.IsGen → ∀ (w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R)))), w.IsGen → ∀ (σ₀ : U.SecGF F k) (σ' τ : U.SecGF F (k * N)) (t' t : LB.Sec (LPow A.A A.L ((k * N : ℕ) : ℤ) (TFK (R := R) F))), (∀ (y : (UnifPre.GF (G := G) F).left) (J), Good U.LG.L y J → sval σ' (𝟙 _) y J = sval σ₀ (TFK (R := R) F ◁ (Over.pullback (jK R)).map φ).left y J * (val mu (UnifPre.gFK (G := G) F) y J).val ^ k) → GeneratorPullback.IsoRelM A.L U.LG.L U.gen.hom.left (pullback.fst G.hom (jK R)) w (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left (k * N) (snd (TFK (R := R) F) A.A).left (U.genF F).left t' (UnifPre.gFK (G := G) F) (𝟙 _) σ' → GeneratorPullback.IsoRelM A.L U.LG.L U.gen.hom.left (pullback.fst G.hom (jK R)) w (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left (k * N) (snd (TFK (R := R) F) A.A).left (U.genF F).left t (UnifPre.gFK (G := G) F) (𝟙 _) τ → ∀ θ : ThetaGrp A.A A.L ((k * N : ℕ) : ℤ) (TFK (R := R) F), IsActOf A.A A.L ((k * N : ℕ) : ℤ) θ t' t → ∀ (z₀ : TFK (R := R) F ⟶ A.A) (ε : Fˣ), z₀ ≫ a = 1 → WeilIs A.A A.L ((k * N : ℕ) : ℤ) z₀ θ.pt (unitOn ε) → ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (UnifPre.GF (G := G) F).left) (z : Z) (J), Good U.LG.L z J → sval τ (ρ ≫ (translT ((Over.pullback (jK R)).obj G) (z₀ ≫ U.gen.inv)).left) z J * (val mu (ρ ≫ UnifPre.gFK (G := G) F) z J).val ^ k = constVal (ρ ≫ (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left) z (ε : F) * (sval τ ρ z J * (val mu ((ρ ≫ (translT ((Over.pullback (jK R)).obj G) (z₀ ≫ U.gen.inv)).left) ≫ UnifPre.gFK (G := G) F) z J).val ^ k) := by
  intro R _ _ I D A G _ _ U F _ _ φ a ha hφ N k mu hmu w hw σ₀ σ' τ t' t h₀ h₁ h₂ θ hθ z₀ ε hz hW Z ρ z J hJ
  haveI := U.gen_hom
  exact eigen_transfer U.gen A.isLB U.LG.isLB (pullback.fst G.hom (jK R)) (jFK (R := R) F) φ.left
    ((Over.pullback (jK R)).map φ) (pullback.lift_fst _ _ _) a ha hφ N k mu hmu w hw σ₀ σ' τ t' t h₀ h₁ h₂ θ hθ
    z₀ (unitOn ε) hz hW Z ρ z J hJ

end GlobalTheory.Jets
end
end

section

open BpJoin Formalism.FourierDecayAlt Formalism.MainNotions.S.ThB

namespace GlobalTheory

theorem margin_arith_closing : ∀ Cc C₀ : ℝ, 0 ≤ C₀ → ∃ Cg₀ : ℝ, 0 ≤ Cg₀ ∧ ∀ Cg : ℝ, Cg₀ ≤ Cg → ∀ (k r n₀ p₀ : ℕ) (h d : ℝ), 1 ≤ k → n₀ ≤ 30 * (r + 1) ^ 2 + 6 → (p₀ : ℝ) ≤ C₀ * ((r : ℝ) + 1) ^ 2 → Cg * (((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) * (((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3)) ≤ h → 0 ≤ d → (Cc * ((r : ℝ) + 1) ^ 4 * (((3 * (r + 1) : ℕ) : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ (ThreeDimData.aOf r (h / 2) - 1) - (((2 * r + 2) * p₀ + n₀ * (r + 1) : ℕ) : ℝ)) ∧ d + (((2 * r + 2) * p₀ + n₀ * (r + 1) : ℕ) : ℝ) ≤ max (Cg * ((2 * r + 2 : ℕ) : ℝ) ^ 3) (200 * d) / 2 - 1 ∧ (((r + 1) * (2 * p₀ + n₀) + (r + 1) * (r + 2) : ℕ) : ℝ) ≤ (C₀ + 10) * ((2 * r + 2 : ℕ) : ℝ) ^ 3 := by
  intro Cc C₀ hC₀
  have habs : 0 ≤ |Cc| := abs_nonneg _
  have hle : Cc ≤ |Cc| := le_abs_self _
  refine ⟨|Cc| + C₀ + 40, by linarith, ?_⟩
  intro Cg hCg k r n₀ p₀ h d hk hn hp hh hd
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hn' : (n₀ : ℝ) ≤ 30 * ((r : ℝ) + 1) ^ 2 + 6 := by exact_mod_cast hn
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  unfold ThreeDimData.aOf
  push_cast at hh ⊢
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = (r : ℝ) + 1 := ⟨_, rfl⟩
  have hrR : (r : ℝ) = R - 1 := by linarith
  have e1 : 2 * (r : ℝ) + 2 = 2 * R := by linarith
  have e2 : (r : ℝ) + 2 = R + 1 := by linarith
  rw [e1] at hh ⊢
  rw [e2]
  rw [← hR] at hh hn' hp ⊢
  have hR1 : 1 ≤ R := by linarith
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = 2 * (r : ℝ) + k + 1 := ⟨_, rfl⟩
  rw [← hN] at hh ⊢
  have hN2 : 2 ≤ N := by linarith
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = 3 * R * N ^ 2 + N ^ 3 := ⟨_, rfl⟩
  rw [← hQ] at hh ⊢
  have hQ1 : 2 ≤ Q := by
    have h1 : 0 ≤ 3 * R * N ^ 2 := by positivity
    have h2 : (2 : ℝ) ^ 3 ≤ N ^ 3 := pow_le_pow_left₀ (by norm_num) hN2 3
    linarith
  have hR0 : 0 < R := by linarith
  have hR2 : 1 ≤ R ^ 2 := one_le_pow₀ hR1
  have hR3 : 1 ≤ R ^ 3 := one_le_pow₀ hR1
  have hR23 : R ^ 2 ≤ R ^ 3 := pow_le_pow_right₀ hR1 (by norm_num)
  have hR13 : R ≤ R ^ 3 := by
    have := pow_le_pow_right₀ hR1 (show 1 ≤ 3 by norm_num)
    simpa using this
  have hR34 : R ^ 3 ≤ R ^ 4 := pow_le_pow_right₀ hR1 (by norm_num)
  have hA : R * p₀ ≤ C₀ * R ^ 3 := by
    have := mul_le_mul_of_nonneg_left hp hR0.le
    calc R * p₀ ≤ R * (C₀ * R ^ 2) := this
      _ = C₀ * R ^ 3 := by ring
  have hB : R * n₀ ≤ 36 * R ^ 3 := by
    have := mul_le_mul_of_nonneg_left hn' hR0.le
    calc R * n₀ ≤ R * (30 * R ^ 2 + 6) := this
      _ = 30 * R ^ 3 + 6 * R := by ring
      _ ≤ _ := by linarith
  have hC3 : 0 ≤ C₀ * R ^ 3 := by positivity
  have hCg0 : 0 ≤ Cg := by linarith
  refine ⟨?_, ?_, ?_⟩
  · have hs : 0 < Real.sqrt (2 * R) := Real.sqrt_pos.mpr (by linarith)
    have hpow : (2 * R) ^ ((9 : ℝ) / 2) = (2 * R) ^ 4 * Real.sqrt (2 * R) := by
      rw [Real.sqrt_eq_rpow, show (9 : ℝ) / 2 = ((4 : ℕ) : ℝ) + 1 / 2 by norm_num,
        Real.rpow_add (by linarith), Real.rpow_natCast]
    rw [hpow] at hh
    have h1 : Cg * (R ^ 4 * Q) ≤ h / 2 / (8 * Real.sqrt (2 * R)) := by
      rw [le_div_iff₀ (by positivity)]
      have : Cg * (R ^ 4 * Q) * (8 * Real.sqrt (2 * R))
          = Cg * ((2 * R) ^ 4 * Real.sqrt (2 * R) * Q) / 2 := by ring
      rw [this]
      linarith
    have hX : 2 * R ^ 3 ≤ R ^ 4 * Q := by
      have : R ^ 4 * 2 ≤ R ^ 4 * Q := mul_le_mul_of_nonneg_left hQ1 (by positivity)
      linarith
    have hX0 : 0 ≤ R ^ 4 * Q := by linarith
    have h2 : (|Cc| + C₀ + 40) * (R ^ 4 * Q) ≤ Cg * (R ^ 4 * Q) :=
      mul_le_mul_of_nonneg_right hCg hX0
    have h3 : Cc * (R ^ 4 * Q) ≤ |Cc| * (R ^ 4 * Q) := mul_le_mul_of_nonneg_right hle hX0
    have h4 : C₀ * (2 * R ^ 3) ≤ C₀ * (R ^ 4 * Q) := mul_le_mul_of_nonneg_left hX hC₀
    nlinarith
  · have h1 := le_max_left (Cg * (2 * R) ^ 3) (200 * d)
    have h2 := le_max_right (Cg * (2 * R) ^ 3) (200 * d)
    have h3 : (C₀ + 40) * R ^ 3 ≤ Cg * R ^ 3 :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h4 : Cg * (2 * R) ^ 3 = 8 * (Cg * R ^ 3) := by ring
    nlinarith
  · nlinarith

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem nonempty_tateIso_of_mulEquiv_pi {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    (Dw Dw' : Datum H) (j : ℕ) (e : Dw'.La ≃ₗ[𝓞 E] (Fin j → Dw.La))
    (he : ∀ x y, Dw'.EF x y = ∑ i, Dw.EF (e x i) (e y i))
    (F : Type) [Field F] (Q Q' : Type) [Group Q] [Group Q'] (φ : Q' ≃* (Fin j → Q))
    (act : 𝓞 E → Q → Q) (act' : 𝓞 E → Q' → Q') (hact : ∀ a x i, φ (act' a x) i = act a (φ x i))
    (w : ℕ → Q → Q → Fˣ → Prop) (w' : ℕ → Q' → Q' → Fˣ → Prop)
    (hw : ∀ k, 0 < k → ∀ (x x' : Q') (c : Fin j → Fˣ), (∀ i, w k (φ x i) (φ x' i) (c i)) → w' k x x' (∏ i, c i))
    (I : TateIso Dw F Q act w) : Nonempty (TateIso Dw' F Q' act' w') := by
  refine ⟨{ ζ := I.ζ, ζ_prim := I.ζ_prim, ζ_pow := I.ζ_pow
            ev := fun n a => φ.symm (fun i => I.ev n (e a i))
            add := ?_, lin := ?_, ker := ?_, onto := ?_, tower := ?_, isom := ?_ }⟩
  · intro n a b
    rw [← map_mul]
    congr 1
    funext i
    simp [I.add]
  · intro n c a
    apply φ.injective
    funext i
    simp [hact, I.lin]
  · intro n hn a
    rw [MulEquiv.map_eq_one_iff, funext_iff]
    simp only [Pi.one_apply, I.ker n hn]
    constructor
    · intro h
      choose b hb using h
      refine ⟨e.symm b, e.injective ?_⟩
      funext i
      simp [hb i]
    · rintro ⟨b, rfl⟩ i
      exact ⟨e b i, by simp⟩
  · intro n hn x
    rw [← φ.map_eq_one_iff, map_pow, funext_iff]
    simp only [Pi.pow_apply, Pi.one_apply, I.onto n hn]
    constructor
    · intro h
      choose b hb using h
      refine ⟨e.symm b, φ.injective ?_⟩
      funext i
      simp [hb i]
    · rintro ⟨a, rfl⟩ i
      exact ⟨e a i, by simp⟩
  · intro n m hn hm a
    rw [← map_pow]
    congr 1
    funext i
    simp [I.tower n m hn hm]
  · intro n hn a b
    have hz : I.ζ n ^ Dw'.EF a b = ∏ i, I.ζ n ^ Dw.EF (e a i) (e b i) := by
      rw [he]
      exact map_prod (zpowersHom Fˣ (I.ζ n)) (fun i => Multiplicative.ofAdd (Dw.EF (e a i) (e b i))) Finset.univ
    rw [hz]
    apply hw n hn
    intro i
    simpa using I.isom n hn (e a i) (e b i)

theorem exists_mulEquiv_points_of_isPowGrp {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [GrpObj G] {j : ℕ}
    (p : IsPowGrp G' G j) (T : Over S) :
    ∃ φ : (T ⟶ G') ≃* (Fin j → (T ⟶ G)), ∀ x i, φ x i = x ≫ p.pr i := by
  let f : (T ⟶ G') →* (Fin j → (T ⟶ G)) := MonoidHom.mk' (fun x i => x ≫ p.pr i) (by
    intro x y
    funext i
    have := p.hom i
    exact MonObj.mul_comp x y (p.pr i))
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      apply p.lim.hom_ext
      rintro ⟨i⟩
      exact congrFun h i
    · intro y
      refine ⟨p.lim.lift (Fan.mk T y), ?_⟩
      funext i
      exact p.lim.fac (Fan.mk T y) ⟨i⟩
  exact ⟨MulEquiv.ofBijective f hf, fun _ _ => rfl⟩

theorem exists_tateIso_of_isPowPolAV : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (pA : IsPowPolAV A' A j) (F : Type) [Field F] [Algebra (FractionRing R) F] (act : 𝓞 E → (A.A ⟶ A.A)) (act' : 𝓞 E → (A'.A ⟶ A'.A)), (∀ a i, act' a ≫ pA.pr i = pA.pr i ≫ act a) → ∀ (Dw : Datum H) (_I : TateIso Dw F (TFK (R := R) F ⟶ A.A) (fun a x => x ≫ act a) (fun k x x' z => WeilIs A.A A.L k x x' (unitOn z))), ∃ Dw' : Datum H, Nonempty (TateIso Dw' F (TFK (R := R) F ⟶ A'.A) (fun a x => x ≫ act' a) (fun k x x' z => WeilIs A'.A A'.L k x x' (unitOn z))) := by
  intro h1 h2 h4 htw E _ _ _ H R _ _ j A A' pA F _ _ act act' hact Dw I
  obtain ⟨Dw', e, he, -, -⟩ := GlobalTheory.T.hermitian_datum_direct_power E H Dw j
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_points_of_isPowGrp pA.toIsPowGrp (TFK (R := R) F)
  refine ⟨Dw', nonempty_tateIso_of_mulEquiv_pi Dw Dw' j e he F _ _ φ _ _ ?_ _ _ ?_ I⟩
  · intro a x i
    simp only [hφ, Category.assoc, hact]
  · intro k hk x x' c hc
    simp only [hφ] at hc
    exact GlobalTheory.T.weilPairing_powPolAV_eq_prod_field h1 h2 h4 htw R j A A' pA F k hk x x' c hc

end GlobalTheory
end
