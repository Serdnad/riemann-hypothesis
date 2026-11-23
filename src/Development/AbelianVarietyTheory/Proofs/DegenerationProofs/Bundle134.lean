module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle007
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle120
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtActIffEqGtSmul
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtExtOfTorsion
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PullQkSurjective
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle124
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle125
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle128

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

noncomputable section
namespace GlobalTheory.PsiExpansion

theorem exists_sec_of_retract {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X)} {ε : K → ℤ} (h : Y' ⟶ Y) (m : Y ⟶ Y') (hm : h ≫ m = 𝟙 Y')
    (e : ∀ k, m ≫ φ' k = φ k) (s' : LB.Sec (LB.LinComb L φ' ε)) :
    ∃ s : LB.Sec (LB.LinComb L φ ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J), Good L z J →
      sval s' r z J = sval s (r ≫ h) z J := by
  obtain ⟨s, hs⟩ := exists_sec hL (φ' := φ) (ε' := ε) (fun U _ g => by simp only [e]) (H1.SectionArithmetic.pullSec s' m)
  refine ⟨s, fun Z r z J hJ => ?_⟩
  rw [hs Z _ z J hJ, H1.SectionArithmetic.sval_pullSec _ _ _ z hJ, Category.assoc, hm, Category.comp_id]

theorem snd_lift_unit {S : Scheme.{0}} (G : Over S) :
    (snd (𝟙_ _) G).left ≫ (lift (toUnit G) (𝟙 G)).left = 𝟙 (𝟙_ (Over S) ⊗ G).left := by
  have : snd (𝟙_ _) G ≫ lift (toUnit G) (𝟙 G) = 𝟙 _ := by
    refine CartesianMonoidalCategory.hom_ext _ _ (toUnit_unique _ _) ?_
    rw [Category.assoc, lift_snd, Category.comp_id, Category.id_comp]
  exact congrArg CommaMorphism.left this

variable {R : Type} [CommRing R] [IsDomain R]


omit [IsDomain R] in
theorem exists_lift_of_retraction (F : Type) [Field F] [Algebra (FractionRing R) F] (g : F →+* FractionRing R)
    (hg : ∀ a, g (algebraMap (FractionRing R) F a) = a) {T : Over (Spec (CommRingCat.of R))} (κ : T ⟶ TK R) :
    ∃ κ' : T ⟶ TF (R := R) F, κ'.left ≫ jFK (R := R) F = κ.left := by
  let i : (TK R).left ⟶ Spec (CommRingCat.of F) := Spec.map (CommRingCat.ofHom g)
  have hi : i ≫ jFK (R := R) F = 𝟙 (TK R).left := by
    refine (Spec.map_comp _ _).symm.trans (Eq.trans (congrArg Spec.map ?_) (Spec.map_id _))
    exact CommRingCat.hom_ext (RingHom.ext hg)
  have hκ : (κ.left ≫ i) ≫ jFK (R := R) F = κ.left := by
    rw [Category.assoc, hi, Category.comp_id]
  exact ⟨Over.homMk (κ.left ≫ i)
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ jK R) hκ).trans (Over.w κ))), hκ⟩

theorem exists_lift_frac {T : Over (Spec (CommRingCat.of R))} (κ : T ⟶ TK R) :
    ∃ κ' : T ⟶ TF (R := R) (FractionRing R), κ'.left ≫ jFK (R := R) (FractionRing R) = κ.left :=
  exists_lift_of_retraction (FractionRing R) (RingHom.id _) (fun _ => rfl) κ


omit [IsDomain R] in
theorem exists_sameG {G : Over (Spec (CommRingCat.of R))} {L : LB G.left} (hL : L.IsLB) {k : ℕ}
    (s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => (snd (𝟙_ _) G).left) (fun _ => (k : ℤ)))) :
    ∃ σ : H0 L k, SameG σ s :=
  exists_sec_of_retract hL _ _ (snd_lift_unit G)
    (fun _ => congrArg CommaMorphism.left (lift_snd (toUnit G) (𝟙 G))) s

theorem exists_sameB {D : DegPre R} {k : ℕ} (s : ∀ α, SecBT D (𝟙_ _) k α) : ∃ f : ∀ α, D.SecB k α, SameB f s := by
  have H : ∀ α, ∃ f : D.SecB k α, ∀ (Z : Scheme.{0}) (r : Z ⟶ _) (z : Z) (J), Good D.P.L z J →
      sval (s α) r z J = sval f (r ≫ (snd _ D.P.A).left) z J := fun α => by
    refine exists_sec_of_retract D.P.isLB _ _ (snd_lift_unit D.P.A) (fun i => ?_) (s α)
    fin_cases i
    · exact congrArg CommaMorphism.left (lift_snd (toUnit D.P.A) (𝟙 D.P.A))
    · refine congrArg CommaMorphism.left (show lift (toUnit D.P.A) (𝟙 D.P.A) ≫
        padd D.P.A (snd _ _) (toUnit _ ≫ D.c α) = padd D.P.A (𝟙 _) (toUnit _ ≫ D.c α) from ?_)
      simp only [padd, ← Category.assoc, comp_lift, lift_snd, comp_toUnit]
    · refine congrArg CommaMorphism.left
        (show lift (toUnit D.P.A) (𝟙 D.P.A) ≫ toUnit _ ≫ D.c α = toUnit _ ≫ D.c α from ?_)
      rw [← Category.assoc, comp_toUnit]
    · refine congrArg CommaMorphism.left
        (show lift (toUnit D.P.A) (𝟙 D.P.A) ≫ toUnit _ ≫ η[D.P.A] = toUnit _ ≫ η[D.P.A] from ?_)
      rw [← Category.assoc, comp_toUnit]
  choose f hf using H
  exact ⟨f, hf⟩

theorem psiRel_of_levelOneEq {D : DegPre R} {f₀ : ∀ α, D.SecB 1 α} {f : ∀ α, SecBT D (𝟙_ _) 1 α}
    (hs : SameB f₀ f) (h : PsiCompare.LevelOneEq D f₀) : PsiRel D (𝟙_ _) f := by
  intro χ T ρ κ y z J hJ
  obtain ⟨κ', hκ⟩ := exists_lift_frac κ
  have l : ∀ u : T ⟶ D.P.A, (lift ρ u).left ≫ (snd _ D.P.A).left = u.left := fun u =>
    congrArg CommaMorphism.left (lift_snd ρ u)
  have e := (h χ 0 rfl T κ' y z J hJ).trans (congrArg (fun q => sval (f₀ 0) (y * cT D T χ).left z J *
    (val (D.psi χ) q z J * rigV D z J).val) hκ)
  rw [hs χ _ _ z J hJ, hs 0 _ _ z J hJ, l, l]
  exact e.trans (mul_comm _ _)

theorem psiRel_of_expT : Laws → Laws2 → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (I : Ideal V), AdmBase V I → ∀ (D : DegData V I) (A : PolAV (Sp (FractionRing V))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : PreU I D.toPre A G) (U₀ : Unif I D A G), Under U U₀.toUnifPre → ∀ (σ : U.SecGT (𝟙_ _) 1) (f : ∀ α, SecBT D.toPre (𝟙_ _) 1 α), U.ExpT (𝟙_ _) 1 σ f → PsiRel D.toPre (𝟙_ _) f := by
  intro h₁ h₂ V _ _ _ I hV D A G _ _ U U₀ hU σ f hE
  obtain ⟨σ₁, hσ₁⟩ := exists_sameG U.P.L.isLB σ
  obtain ⟨f₀, hf₀⟩ := exists_sameB f
  have ht : H0 U.P.L.L 1 = H0 U₀.toUnifPre.LG.L 1 := by rw [hU.2.1]
  have hc : HEq (cast ht σ₁) σ₁ := cast_heq ht σ₁
  have H := ((PreForm.under_exists_and_expands h₁ h₂ V I D A G U.semi).2.2 U U₀.toUnifPre hU 1 σ f (cast ht σ₁) f₀
    (fun τ hτ z J hJ => by
      obtain rfl : τ = σ₁ := eq_of_heq (hτ.trans hc)
      rw [hσ₁ _ _ z J hJ, Category.id_comp])
    (fun α z J hJ => by rw [hf₀ α _ _ z J hJ, Category.id_comp])).1 hE
  exact psiRel_of_levelOneEq hf₀
    (PsiCompare.levelOneEq_of_expandsAt h₁.globalFns hV U₀.toUnifPre (U₀.expand 1 le_rfl) _ f₀ H)

end GlobalTheory.PsiExpansion
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.GaugeHom
open GlobalTheory.TorusExt GlobalTheory.ArcExt

section Val
variable {F : Type} [Field F] {X : Scheme.{0}} {L : LB X}
  {J J' : (Sp F ⟶ X) → L.ι} (hJ : ∀ ψ : Sp F ⟶ X, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ)) (hJ' : ∀ ψ : Sp F ⟶ X, ⊤ ≤ ψ ⁻¹ᵁ L.U (J' ψ))
include hJ hJ'

theorem exists_trans : ∃ T : (Sp F ⟶ X) → Fˣ, ∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (s : LB.Sec (LB.LinComb L φ ε)) (r : Sp F ⟶ Y), sF s r J = (∏ k, T (r ≫ φ k) ^ ε k : Fˣ) * sF s r J' := by
  let y : Sp F := IsLocalRing.closedPoint F
  have hm : ∀ ψ : Sp F ⟶ X, ⊤ ≤ ψ ⁻¹ᵁ (L.U (J ψ) ⊓ L.U (J' ψ)) := fun ψ z hz => ⟨hJ ψ hz, hJ' ψ hz⟩
  have hv : ∀ ψ : Sp F ⟶ X, (gm ψ y (L.U (J ψ) ⊓ L.U (J' ψ)) (L.g (J ψ) (J' ψ))).val =
      stalkConst y (valF ψ (L.U (J ψ) ⊓ L.U (J' ψ)) (L.g (J ψ) (J' ψ)).val) := fun ψ =>
    (gs_unit ψ y _ (hm ψ trivial) _).symm.trans (gs_eq_stalkConst ψ y (hm ψ) _)
  have hne : ∀ ψ : Sp F ⟶ X, valF ψ (L.U (J ψ) ⊓ L.U (J' ψ)) (L.g (J ψ) (J' ψ)).val ≠ 0 := fun ψ h =>
    (((Units.isUnit _).map _).map _).ne_zero ((dif_pos (hm ψ)).symm.trans h)
  refine ⟨fun ψ => Units.mk0 _ (hne ψ), fun Y K _ φ ε s r => (stalkConst y).injective ?_⟩
  have e : ∀ ψ : Sp F ⟶ X, gm ψ y (L.U (J ψ) ⊓ L.U (J' ψ)) (L.g (J ψ) (J' ψ)) =
      Units.map (stalkConst y).toMonoidHom (Units.mk0 _ (hne ψ)) := fun ψ => Units.ext (hv ψ)
  have a := sec_trans s r y (top_le_chart hJ φ r trivial) (top_le_chart hJ' φ r trivial)
  rw [map_mul]
  refine (gs_eq_stalkConst r y (top_le_chart hJ φ r) _).symm.trans
    (a.trans (congrArg₂ (· * ·) ?_ (gs_eq_stalkConst r y (top_le_chart hJ' φ r) _)))
  show _ = (Units.map (stalkConst y).toMonoidHom _).val
  rw [map_prod, trF]
  refine congrArg Units.val (Finset.prod_congr rfl fun k _ => ?_)
  rw [map_zpow, e]

end Val

theorem exists_trans_ext {F F' : Type} [Field F] [Field F'] (f : F →+* F') {X : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    {J : (Sp F ⟶ X) → L.ι} {J' : (Sp F' ⟶ X) → L.ι} (hJ : ∀ ψ : Sp F ⟶ X, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ))
    (hJ' : ∀ ψ : Sp F' ⟶ X, ⊤ ≤ ψ ⁻¹ᵁ L.U (J' ψ)) : ∃ T : (Sp F ⟶ X) → F'ˣ,
    (∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
      (s : LB.Sec (LB.LinComb L φ ε)) (r : Sp F ⟶ Y),
      sF s (spMap f ≫ r) J' = (∏ k, T (r ≫ φ k) ^ ε k : F'ˣ) * f (sF s r J)) ∧
    ∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
      (t : LB.Gen (LB.LinComb L φ ε)), t.IsGen → ∀ r : Sp F ⟶ Y,
      vF t (spMap f ≫ r) J' = (∏ k, T (r ≫ φ k) ^ ε k : F'ˣ) * f (vF t r J) := by
  obtain ⟨J₀, h₀, e₀⟩ := exists_gauge f hL hJ
  obtain ⟨T, hT⟩ := exists_trans hJ' h₀
  have k : ∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
      (s : LB.Sec (LB.LinComb L φ ε)) (r : Sp F ⟶ Y),
      sF s (spMap f ≫ r) J' = (∏ k, T (spMap f ≫ r ≫ φ k) ^ ε k : F'ˣ) * f (sF s r J) := fun Y K _ φ ε s r => by
    rw [hT, sF_ext f hJ e₀]
    simp only [Category.assoc]
  exact ⟨fun ψ => T (spMap f ≫ ψ), k, fun Y K _ φ ε t ht r => k Y K φ ε (genSec t ht) r⟩

theorem exists_hom (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F F' : Type) [Field F]
    [Algebra (FractionRing R) F] [Field F'] [Algebra (FractionRing R) F'] (f : F →+* F')
    (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F') (N : NumD F) (N' : NumD F')
    (ν : NumOf D F N) (ν' : NumOf D F' N') (hth : ν'.th = ν.th) :
    ∃ I : NumD.Hom f N N', I.lam = 1 ∧ (∀ y, ν'.eX (I.e y) = ν.eX y) ∧
      ∀ (k : ℕ) (p : QkPt D F k) (p' : QkPt D F' k) (q : N.QT k) (q' : N'.QT k), QkExt f p p' → ν.QPt p q →
        ν'.QPt p' q' → q'.1.1.toAdd = I.e q.1.1.toAdd ∧ I.Rel q.1.2 q'.1.2 := by
  obtain ⟨T, hs, hg⟩ := exists_trans_ext f D.P.isLB ν.good ν'.good
  have hr : rigVal ν' = T (1 : TF (R := R) F ⟶ D.P.A).left * f (rigVal ν) := by
    have := hg _ _ (fun _ : PUnit => eSec D.P.A) (fun _ => 1) D.rig D.rig_gen (TF (R := R) F).hom
    rw [Fintype.prod_unique, zpow_one] at this
    refine Eq.trans ?_ this
    exact congrArg (fun r => vF (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig r ν'.J)
      (Over.w (extMap (R := R) f hf)).symm
  have h0 : rigVal ν ≠ 0 := vF_ne_zero ν.good _ _
  let I : NumD.Hom f N N' :=
    { φ := ptHom f hf ν ν'
      h := fun x => T (ν.eA x).left / T (1 : TF (R := R) F ⟶ D.P.A).left
      h_one := by rw [map_one, div_self']
      θ_eq := fun x y u => by
        have e : N'.θ (ptHom f hf ν ν' x) (ptHom f hf ν ν' y) (ptHom f hf ν ν' u) =
            (∏ I : thK, T ((lift (ν.eA x) (lift (ν.eA y) (ν.eA u))).left ≫ thφ D.P.A (x3 D.P.A) I) ^ thε I) *
              Units.map f.toMonoidHom (N.θ x y u) := by
          refine Units.ext ?_
          show _ = _ * f (N.θ x y u : F)
          rw [ν'.θ_eq, ν.θ_eq, eA_ptHom, eA_ptHom, eA_ptHom, ← comp_lift, ← comp_lift]
          exact hg _ _ _ _ _ D.cub.isGen _
        rw [e, prod_cub]
        simp only [map_mul]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_div, ofMul_inv]; abel
      σ_eq := fun x => by
        have e : N'.σ (ptHom f hf ν ν' x) = (T (ν.eA x)⁻¹.left * (T (ν.eA x).left)⁻¹) *
            Units.map f.toMonoidHom (N.σ x) := by
          refine Units.ext ?_
          show _ = _ * f (N.σ x : F)
          rw [ν'.σ_eq, ν.σ_eq, eA_ptHom]
          refine (hg _ _ _ _ _ D.sym_gen _).trans (congrArg (fun z : F'ˣ => z.val * _) ?_)
          rw [Fin.prod_univ_two]
          show T ((ν.eA x)⁻¹).left ^ (1 : ℤ) * T ((ν.eA x).left ≫ 𝟙 _) ^ (-1 : ℤ) = _
          rw [Category.comp_id, zpow_one, zpow_neg, zpow_one]
        rw [e, map_inv]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_div, ofMul_inv]; abel
      lam := 1
      th_eq := fun x => by
        have a : N'.th (ptHom f hf ν ν' x) * rigVal ν' = _ := ν'.th_eq _
        have b : N.th x * rigVal ν = _ := ν.th_eq _
        have c := hs _ _ _ _ ν.th (ν.eA x).left
        rw [Fintype.prod_unique, Category.comp_id, ← b, zpow_natCast, pow_one, map_mul] at c
        rw [eA_ptHom, hth, hr] at a
        have d := a.trans c
        have h1 : f (rigVal ν) ≠ 0 := (map_ne_zero f).2 h0
        rw [← _root_.mul_assoc, ← _root_.mul_assoc] at d
        have d' := mul_right_cancel₀ h1 d
        rw [_root_.one_mul, Units.val_div_eq_div_val, div_mul_eq_mul_div, ← d', mul_div_cancel_right₀ _ (Units.ne_zero _)]
      e := ν.eX.trans ν'.eX.symm
      c_eq := fun χ => ν'.eA.injective (by
        rw [ν'.c_eq, eA_ptHom, ν.c_eq, AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
        exact (DVR.comp_cP D (extMap f hf) _).symm)
      ψ_eq := fun χ => by
        have e : N'.ψ (ν.eX.trans ν'.eX.symm χ) = ((T (ν.eA (N.c χ)).left)⁻¹ * T (1 : TF (R := R) F ⟶ D.P.A).left) *
            Units.map f.toMonoidHom (N.ψ χ) := by
          refine Units.ext ?_
          show _ = ((T (ν.eA (N.c χ)).left)⁻¹).val * (T (1 : TF (R := R) F ⟶ D.P.A).left).val * f (N.ψ χ : F)
          rw [ν'.ψ_eq, ν.ψ_eq, map_mul, AddEquiv.trans_apply, AddEquiv.apply_symm_apply, _root_.mul_mul_mul_comm]
          refine congrArg₂ (· * ·) ?_ hr
          have c := hg _ _ _ _ _ (D.psi_gen (ν.eX χ)) (jFK (R := R) F)
          rw [Fintype.prod_unique, zpow_neg, zpow_one] at c
          refine (congrArg (fun r => vF (D.psi (ν.eX χ)) r ν'.J)
            ((extMap_jFK f hf).trans (Category.id_comp _)).symm).trans (c.trans ?_)
          refine congrArg (fun z => ((T z)⁻¹).val * _) ?_
          rw [ν.c_eq]
          exact congrArg (fun z => z.left) (DVR.comp_cP D
            (Over.homMk (jFK (R := R) F) rfl : TF (R := R) F ⟶ TK R) _)
        rw [e]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_div, ofMul_inv]; abel }
  have hX : ∀ y, ν'.eX (I.e y) = ν.eX y := fun y => ν'.eX.apply_symm_apply _
  refine ⟨I, rfl, hX, fun k p p' q q' h hq hq' => ⟨ν'.eX.injective (hq'.1.trans (h.1.trans (hq.1.symm.trans (hX _).symm))),
    ν'.eA.injective (hq'.2.1.trans (Over.OverMorphism.ext ?_)), fun χ => ?_⟩⟩
  · rw [h.2.1, ← hq.2.1]
    exact (congrArg (fun z => z.left) (eA_ptHom f hf ν ν' _)).symm
  · have e : q'.1.2.s (I.e χ) = (∏ i, T (DegPre.gtφ D F p.g.b (ν.eX χ) i) ^ DegPre.gtε i) *
        Units.map f.toMonoidHom (q.1.2.s χ) := by
      refine Units.ext ?_
      show _ = _ * f (q.1.2.s χ : F)
      rw [hq'.2.2, hq.2.2, hX]
      have c := hg _ _ _ _ _ (p.g.isGen (ν.eX χ)) (𝟙 (Sp F))
      simp only [Category.id_comp, Category.comp_id] at c
      refine Eq.trans ?_ c
      let y : Sp F' := IsLocalRing.closedPoint F'
      have hJ : Good D.P.L y ν'.J := fun ψ => ν'.good ψ trivial
      refine (stalkConst y).injective ((val_eq_vF ν'.good _ _ y).symm.trans (Eq.trans ?_ (val_eq_vF ν'.good _ _ y)))
      refine congrArg Units.val ((val_corr hJ (h.2.2 _) _).trans ((val_pull hJ _ _ _).trans ?_))
      rw [Category.id_comp]
    rw [e, prod_gt]
    show _ * (T (ν.eA (N.c χ * q.1.2.b)).left / _) = _ * (T (ν.eA (N.c χ)).left / _) * (T (ν.eA q.1.2.b).left / _)
    rw [map_mul, hq.2.1, ν.c_eq]
    show _ * (T (DVR.cP D (TF (R := R) F) (ν.eX χ) * p.g.b).left / _) =
      _ * (T (DVR.cP D (TF (R := R) F) (ν.eX χ)).left / _) * _
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div, ofMul_inv]; abel

end GlobalTheory.GaugeHom
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.FiniteValues
open GlobalTheory.TorusExt GlobalTheory.ArcExt

theorem exists_finset_point {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F]
    (B : Over (Spec (CommRingCat.of R))) [LocallyOfFiniteType B.hom] (p : TF (R := R) F ⟶ B) :
    ∃ S : Finset F, ∀ K : IntermediateField (FractionRing R) F, (S : Set F) ⊆ K →
      ∃ l : TF (R := R) K ⟶ B, extMap (R := R) (algebraMap K F) rfl ≫ l = p := by
  classical
  obtain ⟨_, ⟨U, hU, rfl⟩, hpt, -⟩ := B.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (p.left (IsLocalRing.closedPoint F))) isOpen_univ
  have hU : IsAffineOpen U := hU
  obtain ⟨f, hf⟩ : ∃ f : Γ(B.left, U) ⟶ CommRingCat.of F, Spec.map f ≫ hU.fromSpec = p.left := by
    refine ⟨Spec.preimage (IsOpenImmersion.lift hU.fromSpec p.left ?_), ?_⟩
    · rintro _ ⟨y, rfl⟩
      rw [hU.range_fromSpec, Subsingleton.elim (α := PrimeSpectrum F) y (IsLocalRing.closedPoint F)]
      exact hpt
    · rw [Spec.map_preimage]; exact IsOpenImmersion.lift_fac _ _ _
  obtain ⟨g, hg⟩ : ∃ g : CommRingCat.of R ⟶ Γ(B.left, U), Spec.map g = hU.fromSpec ≫ B.hom :=
    ⟨Spec.preimage _, Spec.map_preimage _⟩
  have hgf : g ≫ f = CommRingCat.ofHom (algebraMap R (FractionRing R)) ≫
      CommRingCat.ofHom (algebraMap (FractionRing R) F) :=
    Spec.map_injective (by
      rw [Spec.map_comp, hg, ← Category.assoc, hf, Spec.map_comp]
      exact Over.w p)
  have hV : ∀ r : R, f.hom (g.hom r) = algebraMap (FractionRing R) F (algebraMap R _ r) := fun r =>
    congrArg (fun q => q.hom r) hgf
  have hft : g.hom.FiniteType := by
    have : LocallyOfFiniteType (Spec.map g) := by rw [hg]; infer_instance
    exact HasRingHomProperty.Spec_iff.1 this
  let _ : Algebra R Γ(B.left, U) := g.hom.toAlgebra
  obtain ⟨s, hs⟩ := (show Algebra.FiniteType R Γ(B.left, U) from hft).out
  refine ⟨s.image f.hom, fun K hK => ?_⟩
  have hr : ∀ a, f.hom a ∈ K := fun a => by
    have ha : a ∈ Algebra.adjoin R (s : Set Γ(B.left, U)) := hs ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem x hx => exact hK (Finset.mem_image_of_mem _ hx)
    | algebraMap r => exact (hV r).symm ▸ K.algebraMap_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  let f' : Γ(B.left, U) ⟶ CommRingCat.of K := CommRingCat.ofHom (f.hom.codRestrict K hr)
  refine ⟨Over.homMk (Spec.map f' ≫ hU.fromSpec) ?_, Over.OverMorphism.ext ?_⟩
  · change (Spec.map f' ≫ hU.fromSpec) ≫ B.hom = Spec.map _ ≫ Spec.map _
    rw [Category.assoc, ← hg, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext r
    exact hV r
  · change Spec.map _ ≫ Spec.map f' ≫ hU.fromSpec = _
    rw [← hf, ← Spec.map_comp_assoc]
    rfl

theorem exists_finite_field_of_values : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra.IsAlgebraic (FractionRing R) F] (N : NumD F) (_ : NumOf D F N) (T : Set N.A), T.Finite → ∃ (K₁ : IntermediateField (FractionRing R) F) (A₀ : Subgroup N.A), FiniteDimensional (FractionRing R) K₁ ∧ (∀ x ∈ T, x ∈ A₀) ∧ (∀ χ, N.c χ ∈ A₀) ∧ (∀ x ∈ A₀, ∀ y ∈ A₀, ∀ u ∈ A₀, (N.θ x y u : F) ∈ K₁) ∧ (∀ x ∈ A₀, (N.σ x : F) ∈ K₁) ∧ (∀ x ∈ A₀, N.th x ∈ K₁) ∧ ∀ χ, (N.ψ χ : F) ∈ K₁ := by
  intro R _ _ D F _ _ _ N ν T hT
  haveI := D.P.isAb.proper
  choose S hS using fun x : N.A => exists_finset_point D.P.A (ν.eA x)
  let s : Set F := ⋃ x ∈ T, (S x : Set F)
  haveI : Finite s := (hT.biUnion fun x _ => (S x).finite_toSet).to_subtype
  let K := IntermediateField.adjoin (FractionRing R) s
  let f : K →+* F := algebraMap K F
  have hf : f.comp (algebraMap (FractionRing R) K) = algebraMap (FractionRing R) F := rfl
  let Φ : (TF (R := R) K ⟶ D.P.A) →* N.A :=
    MonoidHom.mk' (fun x => ν.eA.symm (extMap f hf ≫ x)) fun x y => by rw [MonObj.comp_mul, map_mul]
  have hΦ : ∀ x, ν.eA (Φ x) = extMap f hf ≫ x := fun x => ν.eA.apply_symm_apply _
  let J : (Sp K ⟶ D.P.A.left) → D.P.L.ι := fun ψ => ν.J (spMap f ≫ ψ)
  have hJ : ∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ D.P.L.U (J ψ) := fun ψ z _ => by
    have h := ν.good (spMap f ≫ ψ) (Set.mem_univ (IsLocalRing.closedPoint F))
    rw [Subsingleton.elim (α := PrimeSpectrum K) z (spMap f (IsLocalRing.closedPoint F))]
    exact h
  have hJ' : ∀ ψ, ν.J (spMap f ≫ ψ) = J ψ := fun _ => rfl
  have hm : ∀ a : K, f a ∈ K := fun a => a.2
  have hv : ∀ {Y : Scheme.{0}} {I : Type} [Fintype I] {φ : I → (Y ⟶ D.P.A.left)} {ε : I → ℤ}
      (t : LB.Gen (LB.LinComb D.P.L φ ε)) (r : Sp K ⟶ Y), vF t (spMap f ≫ r) ν.J ∈ K := fun t r => by
    rw [vF_ext f hJ hJ']; exact hm _
  have hw : ∀ {Y : Scheme.{0}} {I : Type} [Fintype I] {φ : I → (Y ⟶ D.P.A.left)} {ε : I → ℤ}
      (t : LB.Sec (LB.LinComb D.P.L φ ε)) (r : Sp K ⟶ Y), sF t (spMap f ≫ r) ν.J ∈ K := fun t r => by
    rw [sF_ext f hJ hJ']; exact hm _
  have hrig : rigVal ν ∈ K := by
    rw [rigVal, ← Over.w (extMap (R := R) f hf)]
    exact hv _ _
  refine ⟨K, Φ.range, IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral,
    fun x hx => ?_, fun χ => ?_, ?_, ?_, ?_, fun χ => ?_⟩
  · obtain ⟨l, hl⟩ := hS x K ((Set.subset_biUnion_of_mem (u := fun x => (S x : Set F)) hx).trans
      (IntermediateField.subset_adjoin _ _))
    exact ⟨l, ν.eA.injective ((hΦ l).trans hl)⟩
  · exact ⟨DegPre.cF D K (ν.eX χ), ν.eA.injective ((hΦ _).trans ((DVR.comp_cP D _ _).trans (ν.c_eq χ).symm))⟩
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ _ ⟨u, rfl⟩
    rw [ν.θ_eq, hΦ, hΦ, hΦ, ← comp_lift, ← comp_lift]
    exact hv _ _
  · rintro _ ⟨x, rfl⟩
    rw [ν.σ_eq, hΦ]
    exact hv _ _
  · rintro _ ⟨x, rfl⟩
    have h0 : rigVal ν ≠ 0 := vF_ne_zero ν.good _ _
    rw [eq_div_of_mul_eq h0 (ν.th_eq (Φ x)), hΦ]
    exact div_mem (hw _ _) hrig
  · rw [ν.ψ_eq]
    refine mul_mem ?_ hrig
    rw [← (extMap_jFK (R := R) f hf).trans (Category.id_comp _)]
    exact hv _ _

end GlobalTheory.FiniteValues
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

theorem _root_.GlobalTheory.T.exists_degenerationValuesIso_fieldPullback : GlobalFnsSt → ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] (φ : R →+* K) (D : DegPre R) (D' : DegPre K) (hD : IsPullDeg φ D D') (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing K) F], ArcPull.Compat φ F → ∀ (N N' : NumD F) (ν : NumOf D F N) (ν' : NumOf D' F N'), ∃ I : NumD.Iso N' N, (∀ y, ν.eX (I.e y) = hD.xe (ν'.eX y)) ∧ ∀ (g : GtPtF D F) (g' : GtPtF D' F) (c : N.Gt) (c' : N'.Gt), ν.Pt g c → ν'.Pt g' c' → IsPullGtF φ hD F g g' → I.Rel c' c := by
  first | exact @GlobalTheory.ValuesPullIso.exists_values_iso | exact GlobalTheory.ValuesPullIso.exists_values_iso | (intros; apply GlobalTheory.ValuesPullIso.exists_values_iso <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

theorem _root_.GlobalTheory.T.exists_tateIso_of_isPolIso : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (K : Type) [Field K] [IsAlgClosed K] (o o' : Full D K) (φ : o.P.A ≅ o'.P.A), IsPolIso o.P o'.P φ → (letI := H.starRing; ∀ x, o.oa.act x ≫ φ.hom = φ.hom ≫ o'.oa.act x) → ∃ I' : (letI := H.starRing; TateIso D K (baseOver (Sp K) ⟶ o'.P.A) (fun a g => g ≫ o'.oa.act a) (fun n g g' c => WeilIs o'.P.A o'.P.L n g g' (unitOn c))), I'.ζ = o.I.ζ ∧ (∀ M a, I'.ev M a = o.I.ev M a ≫ φ.hom) ∧ ∀ m v, o.Theta m v → Full.Theta { o' with I := I' } m v := by
  first | exact @GlobalTheory.FullMove.exists_tateIso_move | exact GlobalTheory.FullMove.exists_tateIso_move | (intros; apply GlobalTheory.FullMove.exists_tateIso_move <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

theorem _root_.GlobalTheory.T.exists_level_of_full' : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (g : ℕ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), (∀ i j, D.EF (bas (Pi.single i 1)) (bas (Pi.single j 1)) = stdSymp g i j) → ∀ (K : Type) [Field K] [IsAlgClosed K] (o : Full D K) (M : ℕ), 0 < M → ∃ (hg : o.P.g = g) (lev : Out.Level o.P M (unitOn (o.I.ζ M))), (∀ i, levelBasis lev hg i = o.I.ev M (bas (Pi.single i 1))) ∧ ∀ c : Fin (2 * g) → ℤ, levelPoint lev hg (fun i => (c i : ZMod M)) = o.I.ev M (bas c) := by
  first | exact @GlobalTheory.exists_level_of_full | exact GlobalTheory.exists_level_of_full | (intros; apply GlobalTheory.exists_level_of_full <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

theorem _root_.GlobalTheory.T.fourthSide_respects_rig_symmetry_cube : ∀ (hG : GlobalFnsSt) (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (I : Ideal R) (I' : Ideal V) (φ : R →+* V), I.map φ ≤ I' → ∀ (D : DegPre R) (D' : DegPre V) (A : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of V))) [GrpObj G'] [IsCommMonObj G'] (U : PreU I D A G) (P' : CP G') (F : G'.left ⟶ G.left) (hF : F ≫ G.hom = G'.hom ≫ spMap φ) (wL : LB.Iso P'.L.L (U.P.L.L.pull F)), IsCPMap P' U.P (spMap φ) F hF wL → ∀ (β : D'.P.A.left ⟶ D.P.A.left) (hβ : β ≫ D.P.A.hom = D'.P.A.hom ≫ spMap φ) (v : LB.Iso D'.P.L (D.P.L.pull β)), IsCPMap (CP.ofDegPre hG D') (CP.ofDegPre hG D) (spMap φ) β hβ v → ∀ (e : ℕ) (g' : GtCoord I' D' e G') (h : (thickObj V I' e G').left ⟶ (thickObj R I e G).left), h ≫ (fstG I e G).left = (fstG I' e G').left ≫ F → g'.pG.left ≫ β = h ≫ (U.gt e).pG.left → ∀ w' : LB.Iso (P'.L.L.pull (fstG I' e G').left) (D'.P.L.pull g'.pG.left), (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj V I' e G').left) (z : Z) (jM : D.P.L.ι) (jM' : D'.P.L.ι) (jL : U.P.L.L.ι) (jL' : P'.L.L.ι), β (g'.pG.left (r z)) ∈ D.P.L.U jM → g'.pG.left (r z) ∈ D'.P.L.U jM' → F ((fstG I' e G').left (r z)) ∈ U.P.L.L.U jL → (fstG I' e G').left (r z) ∈ P'.L.L.U jL' → gw v (r ≫ g'.pG.left) z jM jM' * gw w' r z jM' (fun _ => jL') = gw (U.w e) (r ≫ h) z jM (fun _ => jL) * gw wL (r ≫ (fstG I' e G').left) z jL jL') → ∀ (T : Over (Spec (CommRingCat.of (V ⧸ I' ^ (e + 1))))) (z : T.left) (JG : (T.left ⟶ G'.left) → P'.L.L.ι) (J : (T.left ⟶ D'.P.A.left) → D'.P.L.ι), Good P'.L.L z JG → Good D'.P.L z J → ∀ W : (T ⟶ thickObj V I' e G') → (T.left.presheaf.stalk z)ˣ, (∀ x, W x = gw w' x.left z (J (x.left ≫ g'.pG.left)) (fun _ => JG (x.left ≫ (fstG I' e G').left))) → (val (L := D'.P.L) (φ := fun _ : PUnit => eSec D'.P.A) (ε := fun _ => 1) D'.rig (T.hom ≫ thick V I' e) z J = W 1 * val (L := P'.L.L) (φ := fun _ : PUnit => eSec G') (ε := fun _ => 1) P'.L.rig (T.hom ≫ thick V I' e) z JG) ∧ (∀ x : T ⟶ thickObj V I' e G', val D'.sym (x.left ≫ g'.pG.left) z J * W x = W x⁻¹ * val P'.sym (x.left ≫ (fstG I' e G').left) z JG) ∧ ∀ x y u : T ⟶ thickObj V I' e G', @id (T.left.presheaf.stalk z)ˣ (cubV D'.cub (T := (Over.map (thick V I' e)).obj T) z J ((Over.map (thick V I' e)).map x ≫ g'.pG) ((Over.map (thick V I' e)).map y ≫ g'.pG) ((Over.map (thick V I' e)).map u ≫ g'.pG)) * W (x * y) * W (x * u) * W (y * u) * W 1 = W (x * y * u) * W x * W y * W u * @id (T.left.presheaf.stalk z)ˣ (cubV P'.c (T := (Over.map (thick V I' e)).obj T) z JG ((Over.map (thick V I' e)).map x ≫ fstG I' e G') ((Over.map (thick V I' e)).map y ≫ fstG I' e G') ((Over.map (thick V I' e)).map u ≫ fstG I' e G')) := by
  first | exact @GlobalTheory.LN.FourthSide.fourth_side_vals | exact GlobalTheory.LN.FourthSide.fourth_side_vals | (intros; apply GlobalTheory.LN.FourthSide.fourth_side_vals <;> assumption)
end
