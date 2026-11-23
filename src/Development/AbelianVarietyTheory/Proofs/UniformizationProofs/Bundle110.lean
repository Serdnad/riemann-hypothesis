module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle007
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.AppCompatGeneric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle006
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBasisOfEq
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle001
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FamEqOnClassOfEq
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralDegenerationFamilyBaseChangeExtensionFie
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFamOfIsPullDeg
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIntegralFamiliesSpanPullDegeneration
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTwistBasisOffPrime
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle033
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IntegralFamilyPrescribedTermUnitAtPrime
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle001
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuationsTorusPointsFramesFamilyTerms
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle107
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle015
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle009
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle072
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle102
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle018
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
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsFamRep
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.PsiExists

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem cT_zero (T : Over (Spec (CommRingCat.of R))) : cT D T 0 = 1 := by
  have h := DVR.cPoint_add D T 0 0
  rw [add_zero] at h
  exact mul_eq_left.1 h.symm

theorem comp_famφT {T T₀ : Over (Spec (CommRingCat.of R))} (r : T ⟶ T₀ ⊗ D.P.A) (α : D.X) (k : Fin 4) :
    r.left ≫ famφT D T₀ α k = ![(r ≫ snd T₀ D.P.A).left, ((r ≫ snd T₀ D.P.A) * cT D T α).left, (cT D T α).left,
      (1 : T ⟶ D.P.A).left] k := by
  have c : r ≫ cT D _ α = cT D T α := by rw [← Category.assoc, comp_toUnit]
  fin_cases k
  · rfl
  · exact congrArg (fun q => q.left) ((MonObj.comp_mul r (snd T₀ D.P.A) (cT D _ α)).trans (congrArg _ c))
  · exact congrArg (fun q => q.left) c
  · exact congrArg (fun q => q.left) (MonObj.comp_one (M := D.P.A) r)

theorem famφT_eq (T₀ : Over (Spec (CommRingCat.of R))) (α : D.X) :
    famφT D T₀ α = ![(snd T₀ D.P.A).left, (snd T₀ D.P.A * cT D _ α).left, (cT D _ α).left,
      (1 : T₀ ⊗ D.P.A ⟶ D.P.A).left] := rfl

theorem oneGen_isGen {X Y : Scheme.{0}} (L : LB X) : (LB.oneGen L (Y := Y)).IsGen := fun _ _ =>
  (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm

variable (F : Type) [Field F] [Algebra (FractionRing R) F]

theorem exists_pullB {T : Over (Spec (CommRingCat.of R))} (φ : TF (R := R) F ⟶ T) (k : ℕ) (f : ∀ α, SecBT D T k α) :
    ∃ s : Raw D F k, PullB D F φ k f s := by
  have H : ∀ α, FormEq (Sum.elim (fun i => (φ ▷ D.P.A).left ≫ famφT D T α i)
      (fun e : PEmpty => (e.elim : (DegPre.BF D F).left ⟶ D.P.A.left))) (Sum.elim (DegPre.famε k) fun e => e.elim)
      (DegPre.famφ D F α) (DegPre.famε k) := by
    intro α U _ h
    have e : (fun i => (φ ▷ D.P.A).left ≫ famφT D T α i) = DegPre.famφ D F α := by
      funext i
      rw [comp_famφT, whiskerRight_snd]; rfl
    rw [e, Fintype.prod_sum_type]
    simp
  choose s hs using fun α => exists_sec D.P.isLB (H α)
    (pullMulSec (f α) (φ ▷ D.P.A).left (LB.oneGen D.P.L) (oneGen_isGen _))
  refine ⟨s, fun α z J hJ => ?_⟩
  refine (hs α _ _ z J hJ).trans ((sval_pullMulSec _ _ _ _ _ _ hJ).trans ?_)
  rw [val_one, Units.val_one, _root_.mul_one, Category.id_comp]

theorem isIso_trF (χ : D.X) : IsIso (DegPre.trF D F χ) := by
  have key : ∀ a b : D.X, a + b = 0 → DegPre.trF D F a ≫ DegPre.trF D F b = 𝟙 _ := by
    intro a b hab
    have c : DegPre.trF D F a ≫ cT D _ b = cT D _ b := by rw [← Category.assoc, comp_toUnit]
    have e : DegPre.trF D F a ≫ (snd (TF (R := R) F) D.P.A * cT D _ b) = snd _ _ := by
      rw [MonObj.comp_mul, c, show DegPre.trF D F a ≫ snd _ _ = snd (TF (R := R) F) D.P.A * cT D _ a from lift_snd _ _,
        _root_.mul_assoc]
      have := (DVR.cPoint_add D (DegPre.BF D F) a b).symm
      rw [hab] at this
      rw [show cT D (DegPre.BF D F) a * cT D _ b = 1 from this.trans (cT_zero D _), _root_.mul_one]
    have e' : DegPre.trF D F a ≫ fst _ _ = fst _ _ := lift_fst _ _
    exact (comp_lift _ _ _).trans ((congrArg₂ lift e' e).trans lift_fst_snd)
  exact ⟨DegPre.trF D F (-χ), key _ _ (add_neg_cancel χ), key _ _ (neg_add_cancel χ)⟩

theorem exists_translate (χ : D.X) (s₀ : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F 0) (DegPre.famε 1))) :
    ∃ h : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F χ) (DegPre.famε 1)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J), Good D.P.L z J →
        sval h r z J = sval s₀ (r ≫ (DegPre.trF D F χ).left) z J *
          (val (D.psi χ) (r ≫ (fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F) z J *
            val (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig
              (r ≫ (DegPre.BF D F).hom) z J).val := by
  let κ : DegPre.BF D F ⟶ TK R := Over.homMk ((fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F)
    ((Category.assoc _ _ _).trans (Over.w (fst (TF (R := R) F) D.P.A)))
  have H : FormEq (Sum.elim (fun i => (DegPre.trF D F χ).left ≫ DegPre.famφ D F 0 i)
      (Sum.elim (fun _ : PUnit => κ.left ≫ ptK (D.c χ)) (fun _ : PUnit => (DegPre.BF D F).hom ≫ eSec D.P.A)))
      (Sum.elim (DegPre.famε 1) (Sum.elim (fun _ => -1) (fun _ => 1))) (DegPre.famφ D F χ) (DegPre.famε 1) := by
    intro U _ h
    have e₁ : (fun i => (DegPre.trF D F χ).left ≫ DegPre.famφ D F 0 i) =
        ![(snd (TF (R := R) F) D.P.A * cT D _ χ).left, (snd (TF (R := R) F) D.P.A * cT D _ χ).left,
          (1 : DegPre.BF D F ⟶ D.P.A).left, (1 : DegPre.BF D F ⟶ D.P.A).left] := by
      funext i
      refine (comp_famφT D (DegPre.trF D F χ) 0 i).trans ?_
      rw [cT_zero, _root_.mul_one,
        show DegPre.trF D F χ ≫ snd _ _ = snd (TF (R := R) F) D.P.A * cT D _ χ from lift_snd _ _]
    have e₂ : κ.left ≫ ptK (D.c χ) = (cT D (DegPre.BF D F) χ).left :=
      congrArg (fun q => q.left) (show κ ≫ cT D _ χ = cT D _ χ by rw [← Category.assoc, comp_toUnit])
    have e₃ : (DegPre.BF D F).hom ≫ eSec D.P.A = (1 : DegPre.BF D F ⟶ D.P.A).left := rfl
    rw [e₁, e₂, e₃, show DegPre.famφ D F χ = _ from famφT_eq D (TF (R := R) F) χ, Fintype.prod_sum_type,
      Fintype.prod_sum_type]
    simp [Fin.prod_univ_four, DegPre.famε, _root_.mul_assoc]
  obtain ⟨h, hh⟩ := exists_sec D.P.isLB H (pullMulSec s₀ (DegPre.trF D F χ).left
    (LB.mulGen D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (D.psi χ) κ.left)
      (LB.pullGen D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => 1) D.rig (DegPre.BF D F).hom))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ (D.psi_gen χ) _) (DVR.pullGen_isGen _ _ _ _ D.rig_gen _)))
  refine ⟨h, fun Z r z J hJ => (hh Z r z J hJ).trans ((sval_pullMulSec _ _ _ _ _ _ hJ).trans ?_)⟩
  exact congrArg (fun u : (Z.presheaf.stalk z)ˣ => sval s₀ (r ≫ (DegPre.trF D F χ).left) z J * u.val)
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_pull hJ _ _ _) (val_pull hJ _ _ _)))

def constVal {F : Type} [Field F] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of F)) (z : Z) : F →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ (p ⁻¹ᵁ ⊤) z trivial).hom.comp ((p.app ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom)

theorem constVal_eq {F : Type} [Field F] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of F)) (z : Z) (c : F) :
    constVal p z c = gs p z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) := (gs_eq p z ⊤ trivial _).symm

theorem exists_ratio (h₁ : Laws) (h₂ : Laws2) (χ : D.X)
    (s t : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F χ) (DegPre.famε 1))) (hs : ∃ j, s.f j ≠ 0) (ht : ∃ j, t.f j ≠ 0) :
    ∃ a : Fˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J), Good D.P.L z J →
      sval s r z J = constVal (r ≫ (fst (TF (R := R) F) D.P.A).left) z a.val * sval t r z J := by
  obtain ⟨b, hb⟩ := exists_basis_twist_field h₁ h₂ R D F 1 le_rfl χ
  have : Subsingleton (Fin (1 ^ D.P.g)) := by rw [one_pow]; infer_instance
  let i₀ : Fin (1 ^ D.P.g) := ⟨0, by simp⟩
  have key : ∀ s : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F χ) (DegPre.famε 1)), (∃ j, s.f j ≠ 0) →
      ∃ c : F, c ≠ 0 ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J), Good D.P.L z J →
        sval s r z J = constVal (r ≫ (fst (TF (R := R) F) D.P.A).left) z c * sval (b i₀) r z J := by
    rintro s ⟨j, hj⟩
    obtain ⟨c, hc, -⟩ := hb s
    have hc' : ∀ j, s.f j = DegPre.constBF D F (c i₀) _ * (b i₀).f j := fun j =>
      (hc j).trans (Fintype.sum_subsingleton _ i₀)
    refine ⟨c i₀, fun h0 => hj ?_, fun Z r z J hJ => ?_⟩
    · rw [hc', h0, DegPre.constBF, map_zero, map_zero, map_zero, zero_mul]
    · rw [constVal_eq]
      exact (congrArg (gs r z _) (hc' _)).trans ((gs_mul r z _ (hJ.mem _ r) _ _).trans (congrArg₂ (· * ·)
        ((gs_res r z le_top (hJ.mem _ r) _).trans (gs_pull r (fst (TF (R := R) F) D.P.A).left z ⊤ trivial _)) rfl))
  obtain ⟨c, hc0, hc⟩ := key s hs
  obtain ⟨d, hd0, hd⟩ := key t ht
  refine ⟨Units.mk0 (c / d) (div_ne_zero hc0 hd0), fun Z r z J hJ => ?_⟩
  rw [hc Z r z J hJ, hd Z r z J hJ, ← _root_.mul_assoc, ← map_mul, Units.val_mk0, div_mul_cancel₀ c hd0]

theorem exists_psi_of_section (h₁ : Laws) (h₂ : Laws2) (i : (TK R).left ⟶ Spec (CommRingCat.of F))
    (hi : i ≫ jFK (R := R) F = 𝟙 _) (f : ∀ α, SecBT D (𝟙_ _) 1 α) (hf : ∀ α, ∃ j, (f α).f j ≠ 0) :
    ∃ ψ : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => ptK (D.c χ)) (fun _ => -1)),
      (∀ χ, (ψ χ).IsGen) ∧ ∀ (χ : D.X) (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ 𝟙_ _) (κ : T ⟶ TK R)
        (y : T ⟶ D.P.A) (z : T.left) (J), Good D.P.L z J → sval (f χ) (lift ρ y).left z J =
          (val (ψ χ) κ.left z J * rigV D z J).val * sval (f 0) (lift ρ (y * cT D T χ)).left z J := by
  obtain ⟨s, hs⟩ := exists_pullB D F (toUnit _) 1 f
  have hs0 := fun α => (pullB_ne_zero_iff R D F 1 f s hs α).2 (hf α)
  have := D.P.isAb.smooth
  have := D.P.isAb.geomConnected
  have : IsIntegral (TF (R := R) F).left := inferInstanceAs (IsIntegral (Spec (CommRingCat.of F)))
  have : IsIntegral (DegPre.BF D F).left := isIntegral_tensor_left_of_smooth_grpObj _ D.P.A (TF (R := R) F)
  choose h hh using fun χ => exists_translate D F χ (s 0)
  have hh0 : ∀ χ, ∃ j, (h χ).f j ≠ 0 := fun χ => by
    obtain ⟨J, hJ⟩ := exists_good_pt (Z := (DegPre.BF D F).left) D.P.isLB (genericPoint _)
    have := isIso_trF D F χ
    have : IsIso (DegPre.trF D F χ).left := inferInstanceAs (IsIso ((Over.forget _).map (DegPre.trF D F χ)))
    rw [exists_ne_zero_iff_sval_ne_zero _ hJ, hh χ _ _ _ J hJ, Category.id_comp]
    exact mul_ne_zero (sval_ne_zero_of_isIso _ _ D.P.L D.P.isLB _ _ _ (s 0) (hs0 0) _ _ _ J hJ) (Units.ne_zero _)
  choose a ha using fun χ => exists_ratio D F h₁ h₂ χ (s χ) (h χ) (hs0 χ) (hh0 χ)
  let u : D.X → Γ((TK R).left, ⊤)ˣ := fun χ => Units.map (i.app ⊤).hom.toMonoidHom (unitOn (a χ))
  refine ⟨fun χ => GlobalTheory.UU.scaleGen (u χ) (D.psi χ), fun χ => GlobalTheory.UU.scaleGen_isGen _ (D.psi_gen χ), ?_⟩
  intro χ T ρ κ y z J hJ
  have hκ : (κ.left ≫ i) ≫ jFK (R := R) F = κ.left := by rw [Category.assoc, hi, Category.comp_id]
  let κ' : T ⟶ TF (R := R) F := Over.homMk (κ.left ≫ i)
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ jK R) hκ).trans (Over.w κ)))
  have hρ : κ' ≫ toUnit _ = ρ := toUnit_unique _ _
  have v₁ := pullB_values R D _ _ _ 1 f s hs χ T κ' y z J hJ
  have v₂ := pullB_values R D _ _ _ 1 f s hs 0 T κ' (y * cT D T χ) z J hJ
  rw [hρ] at v₁ v₂
  have a₁ : (lift κ' y).left ≫ (fst (TF (R := R) F) D.P.A).left = κ.left ≫ i :=
    congrArg (fun q => q.left) (lift_fst κ' y)
  have a₂ : (lift κ' y).left ≫ (DegPre.trF D F χ).left = (lift κ' (y * cT D T χ)).left := by
    refine congrArg (fun q => q.left) (?_ : lift κ' y ≫ DegPre.trF D F χ = _)
    refine (comp_lift _ _ _).trans (congrArg₂ lift (lift_fst _ _) ?_)
    refine (MonObj.comp_mul (lift κ' y) (snd _ D.P.A) (cT D _ χ)).trans ?_
    rw [lift_snd, ← Category.assoc, comp_toUnit]
  have a₃ : (lift κ' y).left ≫ (DegPre.BF D F).hom = T.hom := Over.w _
  have a₄ : (lift κ' y).left ≫ (fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F = κ.left :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ jFK (R := R) F) a₁).trans hκ)
  have w₁ := ha χ _ (lift κ' y).left z J hJ
  have w₂ := hh χ _ (lift κ' y).left z J hJ
  rw [a₂, a₃, a₄] at w₂
  rw [a₁] at w₁
  have w₃ := GlobalTheory.UU.val_scaleGen (u χ) (D.psi χ) κ.left hJ
  have w₄ : (gm κ.left z ⊤ (u χ)).val = constVal (κ.left ≫ i) z (a χ).val :=
    (gs_unit κ.left z ⊤ trivial _).symm.trans ((gs_pull κ.left i z ⊤ trivial _).trans (constVal_eq _ _ _).symm)
  have alg : ∀ (A : Type) [CommRing A] (x₁ x₂ s₁ s₂ t c : A) (p q u v : Aˣ), s₁ = x₁ → s₂ = x₂ → s₁ = c * t →
      t = s₂ * (p * q).val → v = u * p → u.val = c → x₁ = (v * q).val * x₂ := by
    intro A _ x₁ x₂ s₁ s₂ t c p q u v e₁ e₂ e₃ e₄ e₅ e₆
    rw [← e₁, ← e₂, e₃, e₄, e₅, ← e₆]
    simp only [Units.val_mul]
    ring
  exact alg _ _ _ _ _ _ _ _ _ _ _ v₁ v₂ w₁ w₂ w₃ w₄

end GlobalTheory.PsiExists

namespace GlobalTheory

theorem exists_psi_psiRel : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (f : ∀ α, SecBT D (𝟙_ _) 1 α), (∀ α, ∃ j, (f α).f j ≠ 0) → ∃ ψ h, PsiRel (setPsi D ψ h) (𝟙_ _) f := by
  intro h₁ h₂ R _ _ D f hf
  obtain ⟨ψ, h, H⟩ := PsiExists.exists_psi_of_section D (FractionRing R) h₁ h₂ (𝟙 _)
    ((Category.id_comp _).trans (Spec.map_id _)) f hf
  exact ⟨ψ, h, H⟩

end GlobalTheory
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FamGen

open GlobalTheory.FamSpan GlobalTheory.FieldBaseChange

theorem constVal_mul {R : Type} [CommRing R] {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of R)) (z : Z) (a b : R) :
    constVal q z (a * b) = constVal q z a * constVal q z b := by
  rw [constVal, map_mul, gs_mul q z ⊤ trivial]; rfl

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem comb_term {S : Type} [CommRing S] (σ : R →+* S) (ιF : S →+* F)
    (ρ : TF (R := R) F ⟶ Over.mk (specOf σ)) (hρ : ρ.left = specOf ιF) (k : ℕ) (α : D.X) {m : ℕ}
    (b g : Fin m → D.SecB k α)
    (hb : IsSecBasis (T := Over.mk (specOf σ)) (A := D.P.A) _ (fun i => DVR.pullSec D.P.L (D.famφB α) (DegPre.famε k)
      (b i) (snd (Over.mk (specOf σ)) D.P.A).left))
    (r : Fin m → R) (hr : ∀ i, IsUnit (σ (r i)))
    (hg : ∀ i j, (g i).f j = resTop _ (scal D.P.A.hom (r i)) * (b i).f j)
    (G : Fin m → LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k)))
    (hG : ∀ i, GeneratorPullback.SecScal D.P.L (DegPre.famφ D F α) (DegPre.famε k) (G i) (D.famφB α)
      (DegPre.famε k) (g i) (DegPre.prB D F).left 1)
    (s : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k)))
    (sg : LB.Sec (LB.LinComb D.P.L (fun i => (snd (Over.mk (specOf σ)) D.P.A).left ≫ D.famφB α i) (DegPre.famε k)))
    (hsg : GeneratorPullback.SecScal D.P.L (DegPre.famφ D F α) (DegPre.famε k) s
      (fun i => (snd (Over.mk (specOf σ)) D.P.A).left ≫ D.famφB α i) (DegPre.famε k) sg (ρ ▷ D.P.A).left 1) :
    ∃ c : Fin m → S, ∀ j, s.f j = ∑ i, resTop _ (DVR.gF D F (ιF (c i))) * (G i).f j := by
  obtain ⟨c, hc, -⟩ := hb sg
  choose u hu using fun i => (hr i).exists_left_inv
  refine ⟨fun i => (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom (c i) * u i,
    IntegralCoord.lin_of_sval D.P.isLB _ G fun y J hJ => ?_⟩
  have a₁ : (𝟙 _ ≫ (ρ ▷ D.P.A).left) ≫ (snd (Over.mk (specOf σ)) D.P.A).left = 𝟙 _ ≫ (DegPre.prB D F).left := by
    rw [Category.assoc, ← Over.comp_left, whiskerRight_snd]
  have a₂ : (𝟙 _ ≫ (ρ ▷ D.P.A).left) ≫ (fst (Over.mk (specOf σ)) D.P.A).left =
      (𝟙 _ ≫ (fst (TF (R := R) F) D.P.A).left) ≫ specOf ιF := by
    rw [Category.assoc, ← Over.comp_left, whiskerRight_fst, Over.comp_left, hρ, Category.assoc]
  have a₃ : (𝟙 _ ≫ (DegPre.prB D F).left) ≫ D.P.A.hom =
      ((𝟙 _ ≫ (fst (TF (R := R) F) D.P.A).left) ≫ specOf ιF) ≫ specOf σ := by
    rw [← a₂, ← a₁]
    simp only [Category.assoc]
    rw [Over.w (snd (Over.mk (specOf σ)) D.P.A)]
    exact congrArg _ (congrArg _ (Over.w (fst (Over.mk (specOf σ)) D.P.A)).symm)
  rw [← secScal_sval hsg _ y hJ]
  refine (sval_lin (fun i => scal (fst (Over.mk (specOf σ)) D.P.A).left
    ((Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom (c i))) _ (fun j => (hc j).trans (Finset.sum_congr rfl fun i _ =>
      congrArg₂ (· * ·) (congrArg _ (congrArg _ (Iso.hom_inv_id_apply _ _).symm)) rfl)) _ y hJ).trans
    (Finset.sum_congr rfl fun i _ => ?_)
  have e₃ : sval (g i) (𝟙 _ ≫ (DegPre.prB D F).left) y J =
      gs (𝟙 _ ≫ (DegPre.prB D F).left) y ⊤ (scal D.P.A.hom (r i)) * sval (b i) (𝟙 _ ≫ (DegPre.prB D F).left) y J := by
    have hm := hJ.mem (D.famφB α) (𝟙 _ ≫ (DegPre.prB D F).left)
    exact (congrArg (gs _ y _) (hg i _)).trans ((gs_mul _ y _ hm _ _).trans
      (congrArg₂ (· * ·) (gs_res _ y le_top hm _) rfl))
  have e₄ : gs (𝟙 _) y ⊤ (DVR.gF D F (ιF ((Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom (c i) * u i))) =
      constVal (𝟙 _ ≫ (fst (TF (R := R) F) D.P.A).left) y
        (ιF ((Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom (c i) * u i)) :=
    gs_scal (fst (TF (R := R) F) D.P.A).left _ y _
  rw [sval_pullSec _ _ _ _ _ y hJ, a₁, ← secScal_sval (hG i) _ y hJ, e₃, e₄, gs_scal, gs_scal, a₂, a₃,
    constVal_specMap, constVal_specMap, constVal_specMap, ← _root_.mul_assoc, ← constVal_mul, ← map_mul,
    _root_.mul_assoc _ (u i), hu, _root_.mul_one]

theorem zero_term {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ψ : K → (Y' ⟶ X)} {ε : K → ℤ} {h : Y' ⟶ Y} {g : LB.Sec (LB.LinComb L φ ε)} (hg : ∀ j, g.f j = 0)
    {G : LB.Sec (LB.LinComb L ψ ε)} (hG : GeneratorPullback.SecScal L ψ ε G φ ε g h 1) (j) : G.f j = 0 := by
  refine sec_ext_val hL (s' := DVR.SecOps.secZero) (fun y J hJ => ?_) j
  rw [← secScal_sval hG _ y hJ, DVR.UUA.sval_zero_of hg _ y J (hJ.mem _ _),
    DVR.UUA.sval_zero_of (s := DVR.SecOps.secZero) (fun _ => rfl) _ y J (hJ.mem _ _)]


open DVR in
theorem exists_span_generate : PolBaseChangeSt → GlobalFnsSt → DVR.TwistBaseChangeStatement → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R), AdmBase R I → ∀ (φ : R →+* R') (D : DegData R I) (D' : DegPre R') (hD : IsPullDeg φ D.toPre D') (k : ℕ), 1 ≤ k → ∃ (n : ℕ) (F₀ : Fin n → Fam D.toPre (FractionRing R) k) (f : Fin n → ∀ α, D.toPre.SecB k α) (F₁ : Fin n → Fam D' (FractionRing R') k) (f' : Fin n → ∀ α, D'.SecB k α), (∀ i, (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) ((F₀ i).s α) (D.toPre.famφB α) (DegPre.famε k) (f i α) (DegPre.prB D.toPre (FractionRing R)).left 1) ∧ (∀ α, GeneratorPullback.SecScal D'.P.L (DegPre.famφ D' (FractionRing R') α) (DegPre.famε k) ((F₁ i).s α) (D'.famφB α) (DegPre.famε k) (f' i α) (DegPre.prB D' (FractionRing R')).left 1) ∧ (∀ x : D'.X, (∀ (Z : Scheme.{0}) (r : Z ⟶ D'.P.A.left) (z : Z) (p : Fin 4 → D.toPre.P.L.ι) (q : Fin 4 → D'.P.L.ι), (∀ κ, ((hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ))) ((D'.famφB x) κ (r z)) ∈ D.toPre.P.L.U (p κ)) → (∀ κ, (D'.famφB x) κ (r z) ∈ D'.P.L.U (q κ)) → Geo.Tor.gs (r ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ))) z (LB.wchart D.toPre.P.L (D.toPre.famφB (hD.xe x)) p) ((f i (hD.xe x)).f p) = (∏ κ, Geo.Tor.gw hD.w (r ≫ (D'.famφB x) κ) z (p κ) (q κ) ^ (DegPre.famε k) κ).val * Geo.Tor.gs r z (LB.wchart D'.P.L (D'.famφB x) q) ((f' i x).f q)))) ∧ Submodule.span (FractionRing R') (Set.range F₁) = ⊤ ∧ (∀ (S : Type) [CommRing S] [IsDomain S] [ValuationRing S] (σ : R →+* S) (F : Type) [Field F] [Algebra (FractionRing R) F] (ιF : S →+* F), Function.Injective ιF → ∀ (ρ : TF (R := R) F ⟶ (Over.mk (specOf σ))), ρ.left = specOf ιF → ∀ (F' : Type) [Field F'] [Algebra (FractionRing R') F'] (π : S →+* F'), IsLocalHom π → (∀ r : R, π (σ r) = algebraMap (FractionRing R') F' (algebraMap R' (FractionRing R') (φ r))) → ∀ s : Fam D.toPre F k, (∃ g : ∀ α, LB.Sec (LB.LinComb D.toPre.P.L (fun i => (snd (Over.mk (specOf σ)) D.toPre.P.A).left ≫ D.toPre.famφB α i) (DegPre.famε k)), (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (s.s α) (fun i => (snd (Over.mk (specOf σ)) D.toPre.P.A).left ≫ D.toPre.famφB α i) (DegPre.famε k) (g α) (ρ ▷ D.toPre.P.A).left 1)) → ∃ c : Fin n → S, ∀ α, GeneratorPullback.SecLin D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (s.s α) (D.toPre.famφB α) (DegPre.famε k) (fun i => f i α) (DegPre.prB D.toPre F).left (fun i => scal (fst (TF (R := R) F) D.toPre.P.A).left (ιF (c i)))) := by
  intro hP hG hT R R' _ _ _ _ I hA φ D D' hD k hk
  classical
  have : IsNoetherianRing R := hA.1
  let pt : (TK R').left := genericPoint (Spec (CommRingCat.of (FractionRing R')))
  let P : Spec (CommRingCat.of R) := (jK R' ≫ specOf φ) pt
  have hPW : P ∈ hD.W := by
    show (jK R' ≫ specOf φ) pt ∈ hD.W
    rw [← hD.g_comm]
    exact (hD.g pt).2
  have hne : ∀ r : R, r ∉ P.asIdeal → algebraMap R' (FractionRing R') (φ r) ≠ 0 := fun r hr h => hr (by
    show algebraMap R' (FractionRing R') (φ r) ∈ PrimeSpectrum.asIdeal pt
    rw [h]; exact Ideal.zero_mem _)
  have hgen : genericPoint (Spec (CommRingCat.of R)) ∈ hD.W :=
    (genericPoint_specializes P).mem_open hD.W.isOpen hPW
  have := P.isPrime
  obtain ⟨-, e, he⟩ := exists_representatives_mod_nsmul D'.X k hk
  choose b hb using fun α => GlobalTheory.TwistLoc.exists_basis_off_prime hP hG hT R D.toPre ⟨hD.W, hgen, ⟨hD.psiW⟩⟩ P.asIdeal k hk α
  choose r hr F f hF hfρ hf0 using fun q : Fin (k ^ Module.finrank ℤ D'.X) × Fin (k ^ D.toPre.P.g) =>
    integralFamily_at_prime hG R I hA D hD.W ⟨hD.psiW⟩ P hPW k hk (hD.xe (e q.1)) (b (hD.xe (e q.1)) q.2)
  choose f' hf' using fun q x => (SecPull.existsUnique_secPull _ _ _ _ D.toPre.P.L D'.P.L _ D.toPre.P.isLB D'.P.isLB
    hD.w hD.w_gen (Fin 4) (D'.famφB x) (D.toPre.famφB (hD.xe x)) (DegPre.famε k) _ (famφB_comm hD x)
    (f q (hD.xe x))).exists
  choose F' hF' using fun q => exists_fam_of_isPullDeg hG R R' φ D.toPre D' hD k (F q) (f q) (f' q) (hF q) (hf' q)
  let en := (finProdFinEquiv (m := k ^ Module.finrank ℤ D'.X) (n := k ^ D.toPre.P.g)).symm
  have hoff : ∀ i i' l, i' ≠ i → ∀ j, (f (i', l) (hD.xe (e i))).f j = 0 := fun i i' l hi =>
    hf0 (i', l) _ fun mu hmu => hi ((he (e i)).unique ⟨hD.xe.symm mu, hD.xe.injective (by
      rw [map_add (f := _), map_nsmul, AddEquiv.apply_symm_apply]; exact hmu.symm)⟩ ⟨0, by rw [smul_zero, add_zero]⟩)
  refine ⟨_, fun i => F (en i), fun i => f (en i), fun i => F' (en i), fun i => f' (en i),
    fun i => ⟨hF _, hF' _, hf' _⟩, ?_, ?_⟩
  · have hrange : Set.range (fun i => F' (en i)) = Set.range F' := en.surjective.range_comp F'
    rw [hrange, eq_top_iff]
    rintro s -
    choose c hc using fun i => span_term hD k (e i) (b (hD.xe (e i))) (fun l => f (i, l) (hD.xe (e i)))
      (hb _ _ _ (fun t ht => (hne t ht).isUnit) _ (fun _ _ => rfl)) (fun l => r (i, l)) (fun l => hne _ (hr (i, l)))
      (fun l => hfρ (i, l)) (fun l => f' (i, l) (e i))
      (fun l y J J' hJ hJ' => val_of_rel (famφB_comm hD (e i)) (hf' (i, l) (e i)) _ y hJ hJ')
      (fun l => (F' (i, l)).s (e i)) (fun l => hF' (i, l) (e i)) (s.s (e i))
    have hs : s = ∑ q : Fin (k ^ Module.finrank ℤ D'.X) × Fin (k ^ D.toPre.P.g), c q.1 q.2 • F' q := by
      refine fam_ext fun χ j => ?_
      obtain ⟨i, ⟨m, rfl⟩, -⟩ := he χ
      refine fam_eq_on_class_of_eq hG R' D' _ k s _ (e i) (fun j => ?_) m j
      rw [sum_f, Fintype.sum_prod_type, Finset.sum_eq_single i, hc i j]
      · rfl
      · intro i' _ hi
        refine Finset.sum_eq_zero fun l _ => ?_
        have h0 := zero_sec D.toPre.P.isLB D'.P.isLB (DegPre.prB D' (FractionRing R')).left (f (i', l) (hD.xe (e i)))
          (hoff i i' l hi) (f' (i', l) (e i))
          (fun y J J' hJ hJ' => val_of_rel (famφB_comm hD (e i)) (hf' (i', l) (e i)) _ y hJ hJ')
          ((F' (i', l)).s (e i)) (hF' (i', l) (e i)) j
        rw [smul_f, h0, mul_zero]
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [hs]
    exact Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)
  · rintro S _ _ _ σ E _ _ ιE - ρ hρ E' _ _ π hπ hπσ s ⟨sg, hsg⟩
    have hun : ∀ t : R, t ∉ P.asIdeal → IsUnit (σ t) := fun t ht => hπ.map_nonunit _ (by
      rw [hπσ]
      exact ((hne t ht).isUnit).map _)
    choose θ hθ using fun q => FamBaseChange.main hG R I D k (F q) (f q) (hF q) E
    choose c hc using fun i => comb_term σ ιE ρ hρ k (hD.xe (e i)) (b (hD.xe (e i))) (fun l => f (i, l) (hD.xe (e i)))
      (hb _ _ _ hun _ (fun _ _ => rfl)) (fun l => r (i, l)) (fun l => hun _ (hr (i, l))) (fun l => hfρ (i, l))
      (fun l => (θ (i, l)).s (hD.xe (e i))) (fun l => hθ (i, l) _) (s.s (hD.xe (e i))) (sg _) (hsg _)
    have hs : s = ∑ q : Fin (k ^ Module.finrank ℤ D'.X) × Fin (k ^ D.toPre.P.g), ιE (c q.1 q.2) • θ q := by
      refine fam_ext fun χ j => ?_
      obtain ⟨i, ⟨m, hm⟩, -⟩ := he (hD.xe.symm χ)
      obtain rfl : χ = hD.xe (e i) + k • hD.xe m := by
        rw [← map_nsmul, ← map_add (f := _), ← hm, AddEquiv.apply_symm_apply]
      refine fam_eq_on_class_of_eq hG R D.toPre _ k s _ (hD.xe (e i)) (fun j => ?_) _ j
      rw [sum_f, Fintype.sum_prod_type, Finset.sum_eq_single i, hc i j]
      · rfl
      · intro i' _ hi
        refine Finset.sum_eq_zero fun l _ => ?_
        rw [smul_f, zero_term D.toPre.P.isLB (hoff i i' l hi) (hθ (i', l) _) j, mul_zero]
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [← en.sum_comp] at hs
    refine ⟨fun i => c (en i).1 (en i).2, fun α => (secLin_iff_val D.toPre.P.isLB _ _ _ _).2 fun y J hJ => ?_⟩
    refine (sval_lin (fun i => gF D.toPre E (ιE (c (en i).1 (en i).2))) (fun i => (θ (en i)).s α)
      (fun j => (congrArg (fun t : Fam D.toPre E k => (t.s α).f j) hs).trans (sum_f _ _ α j)) _ y hJ).trans
      (Finset.sum_congr rfl fun i _ => ?_)
    rw [secScal_sval (hθ (en i) α) _ y hJ]
    rfl

end GlobalTheory.FamGen
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
theorem _root_.GlobalTheory.T.valuations_torusPoints_frames_familyTerms : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllDV fun {V} _ _ _ {ϖ} hϖ D Q {F} _ _ {v} hv => ∀ g : GtPtF D.toPre F, (∃! l : D.toPre.X →+ ℚ, GtV hϖ hv g l) ∧ (∀ (k : ℕ) (w : Frm D.toPre F k g.b), w.IsGen → ∃! r, GenV hϖ hv w r) ∧ (∀ (k : ℕ) (w : Frm D.toPre F k g.b), FrmOne w → g.b = 1 → GenV hϖ hv w 0) ∧ (∀ (g' g'' : GtPtF D.toPre F) l l', g.IsAdd g' g'' → GtV hϖ hv g l → GtV hϖ hv g' l' → GtV hϖ hv g'' (l + l')) ∧ (∀ (k : ℕ), 1 ≤ k → ∀ p : QkPt D.toPre F k, GtV hϖ hv p.g fun χ => (QForm.bOf D.toPre Q p.y χ : ℚ) / k) ∧ (∀ y, GtPtF.IsIota y g → GtV hϖ hv g fun χ => (QForm.bOf D.toPre Q y χ : ℚ)) ∧ ∀ (k : ℕ), 1 ≤ k → ∀ (w : Frm D.toPre F k g.b) (s : Fam D.toPre F k), w.IsGen → NullV v (coef s g w) ∧ ∀ l ω r, GtV hϖ hv g l → GenV hϖ hv w ω → NuGe D Q F v k s r → ∀ χ, ((r + (Q χ : ℚ) / k + l χ + ω : ℚ) : WithTop ℚ) ≤ v (coef s g w χ) := by
  first | exact @GlobalTheory.UT.CoefVal.main | exact GlobalTheory.UT.CoefVal.main | (intros; apply GlobalTheory.UT.CoefVal.main <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.abelianPart_eq_of_thetaOperator_eq : GlobalFnsSt → SecTwistSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (n : ℕ), 1 ≤ n → ∀ (p p' : QkPt D F n) (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε n))) (w' : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p'.g.b) (DegPre.lineε n))), w.IsGen → w'.IsGen → (∀ s : Fam D F n, ∃ s' : Fam D F n, PhiRel D F n p w s s' ∧ PhiRel D F n p' w' s s') → p'.y = p.y → p.g.b = p'.g.b := by
  first | exact @GlobalTheory.PhiBase.b_eq_of_phiRel | exact GlobalTheory.PhiBase.b_eq_of_phiRel | (intros; apply GlobalTheory.PhiBase.b_eq_of_phiRel <;> assumption)
end
