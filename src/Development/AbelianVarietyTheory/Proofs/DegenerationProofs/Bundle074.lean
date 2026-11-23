module

public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle015
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SymmetricLiftOddOrderExistsUnique
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle044
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle068
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle070
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.QSurjective
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle009
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle051
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle069
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.OLinBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationDataIsoOfTwoWitnesses
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle016
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle049
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle002

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal
noncomputable section
namespace GlobalTheory.TorsFrame

open CommPairing GlobalLift ThetaCoord

theorem val_powGen {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (n : ℕ) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) :
    val (GeneratorPullback.powGen L φ ε t n) r z J = val t r z J ^ n := map_pow _ _ _

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S}

theorem exists_pow_two (hL : L.IsLB) {Y : Scheme.{0}} {f g : Y ⟶ A.left} {k : ℤ} (m : ℕ)
    {u : LB.Gen (LB.LinComb L (K := Fin 2) ![f, g] ![k, -k])} (hu : u.IsGen) :
    ∃ u' : LB.Gen (LB.LinComb L (K := Fin 2) ![f, g] ![m * k, -(m * k)]), u'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → val u' r z J = val u r z J ^ m := by
  obtain ⟨t, ht, hv⟩ := exists_gen hL (φ' := ![f, g]) (ε' := ![m * k, -(m * k)])
    (fun U _ h => by
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, mul_neg])
    (GeneratorPullback.powGen L _ _ u m) (DVR.powGen_isGen _ _ _ _ hu _)
  exact ⟨t, ht, fun Z r z J hJ => (hv Z r z J hJ).trans (val_powGen _ _ _ _ _)⟩

theorem exists_symLift_pow (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {k : ℤ} {q : ℕ} {x : T ⟶ A}
    {θ : ThetaGrp A L k T} (H : SymLift A L k q x θ) (m : ℕ) :
    ∃ θ' : ThetaGrp A L (m * k) T, SymLift A L (m * k) q x θ' ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J → tval θ' r z J = tval θ r z J ^ m := by
  obtain ⟨ν, hν, -⟩ := H.sym
  obtain ⟨u, hu, vu⟩ := exists_pow_two hL m (u := θ.φ) θ.isGen
  obtain ⟨ν', hν', vν⟩ := exists_pow_two hL m (u := ν) hν
  have vu' : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J →
      tval (⟨θ.pt, u, hu⟩ : ThetaGrp A L (m * k) T) r z J = tval θ r z J ^ m := vu
  have vν' : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J →
      nval (k := m * k) ν' r z J = nval ν r z J ^ m := vν
  refine ⟨⟨θ.pt, u, hu⟩, symLift_of_tval hL H.pt_eq (ν := ν') hν' (fun T' π z J hJ p => ?_)
    (fun T' π z J hJ p => ?_), vu'⟩
  · rw [Finset.prod_congr rfl fun j _ => vu' _ _ z J hJ, Finset.prod_pow, prod_tval H π hJ p, one_pow]
  · rw [vu' _ _ z J hJ, vu' _ _ z J hJ, vν' _ _ z J hJ, vν' _ _ z J hJ, ← inv_pow, ← mul_pow, ← mul_pow, ← mul_pow,
      sym_tval hG hA hL H hν π hJ p, one_pow]

theorem eSec_hom : eSec A ≫ A.hom = 𝟙 S := Over.w η[A]

theorem eSec_mulA (n : ℕ) : eSec A ≫ (mulA A n).left = eSec A := by
  have e : η[A] = (1 : 𝟙_ (Over S) ⟶ A) := by rw [Hom.one_def, toUnit_unit, Category.id_comp]
  rw [eSec, ← Over.comp_left, MonObj.comp_pow, Category.comp_id, e, one_pow]

theorem one_left : (1 : T ⟶ A).left = T.hom ≫ eSec A := rfl

theorem exists_norm (hL : L.IsLB) {rig : LB.Gen (L.pull (eSec A))} (hr : rig.IsGen) {n : ℕ}
    {α₀ : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, (mulA A n).left] ![(n : ℤ) ^ 2, -1])} (h₀ : α₀.IsGen) :
    ∃ α : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, (mulA A n).left] ![(n : ℤ) ^ 2, -1]), α.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ S) (z : Z) (J), Good L z J → val α (r ≫ eSec A) z J =
        val (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) rig r z J ^ (n ^ 2) *
          (val (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) rig r z J)⁻¹ := by
  obtain ⟨t, ht, hv⟩ := exists_gen hL (φ' := ![𝟙 A.left, (mulA A n).left]) (ε' := ![(n : ℤ) ^ 2, -1])
    (fun U _ h => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, eSec_mulA, Category.comp_id]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen L _ _ _ _ α₀ (LB.pullGen L _ _ (LB.mulGen L _ _ _ _
      (LB.mulGen L _ _ _ _ (GeneratorPullback.powGen L (fun _ : PUnit => eSec A) (fun _ => 1) rig (n ^ 2))
        (LB.invGen L (fun _ : PUnit => eSec A) (fun _ => 1) rig))
      (LB.invGen L _ _ (LB.pullGen L _ _ α₀ (eSec A)))) A.hom))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ h₀ (DVR.pullGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.powGen_isGen _ _ _ _ hr _) (DVR.invGen_isGen _ _ _ _ hr))
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ h₀ _))) _))
  refine ⟨t, ht, fun Z r z J hJ => ?_⟩
  have e : (r ≫ eSec A) ≫ A.hom = r := by rw [Category.assoc, eSec_hom, Category.comp_id]
  rw [hv _ _ z J hJ, val_mul hJ, val_pull hJ, e, val_mul hJ, val_mul hJ, val_inv, val_inv, val_pull hJ, val_powGen,
    mul_comm, inv_mul_cancel_right]

theorem val_rigT (rig : LB.Gen (L.pull (eSec A))) {Z : Scheme.{0}} (r : Z ⟶ T.left) (z : Z) {J} (hJ : Good L z J) :
    val (rigT A L rig T 1) r z J =
      val (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) rig (r ≫ T.hom) z J := by
  rw [val_of (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) rig (r ≫ T.hom) z J
    (fun _ => J (r ≫ T.hom ≫ eSec A)) (fun _ => by rw [Category.assoc])]
  have hm := hJ.mem (fun _ : Fin 1 => T.hom ≫ eSec A) r
  refine (map_zpow _ _ _).trans ((zpow_one _).trans ((gm_res r z _ hm _).trans ?_))
  exact gm_pull r T.hom z _ (show T.hom (r z) ∈ LB.wchart L (fun _ : PUnit => eSec A)
    (fun _ => J (r ≫ T.hom ≫ eSec A)) from Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hm 0) _

theorem tval_pow (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {ν : LB.Gen (negLB A L 1 T)}
    (hν : ν.IsGen) {n : ℕ} (hn : Odd n)
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, (mulA A n).left] ![(n : ℤ) ^ 2, -1])} (hα : α.IsGen)
    {y : T ⟶ A} (hy : y ^ (n ^ 2) = 1) {θ : ThetaGrp A L (n ^ 2 : ℕ) T} (H : SymLift A L (n ^ 2 : ℕ) (n ^ 2) y θ)
    {z : T.left} {J} (hJ : Good L z J) :
    tval θ (lift (𝟙 T) (1 : T ⟶ A)).left z J ^ (n ^ 2) =
      val α (1 : T ⟶ A).left z J ^ (n ^ 2) * val α (1 : T ⟶ A).left z J *
        (val α y.left z J ^ (n ^ 2) * val α (y ^ n).left z J)⁻¹ := by
  have e₁ : ∀ p : T ⊗ A ⟶ A, p.left ≫ (mulA A n).left = (p ^ n).left := fun p => by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  obtain ⟨β, hβ, vβ⟩ := exists_gen hL (φ' := ![(snd T A).left, (snd T A ^ (n ^ 2)).left])
    (ε' := ![((n ^ 2 : ℕ) : ℤ) * (n ^ 2 : ℕ), -1])
    (fun U _ h => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, e₁, Category.comp_id, ← pow_mul, ← sq]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen L _ _ _ _ (GeneratorPullback.powGen L _ _ (LB.pullGen L _ _ α (snd T A).left) (n ^ 2))
      (LB.pullGen L _ _ α (snd T A ^ n).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.powGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hα _) _)
      (DVR.pullGen_isGen _ _ _ _ hα _))
  have vβ' : ∀ p : T ⟶ A, bval (b := 1) β (lift (𝟙 T) p).left z J =
      val α p.left z J ^ (n ^ 2) * val α (p ^ n).left z J := fun p => by
    refine (vβ _ _ z J hJ).trans ?_
    rw [val_mul hJ, val_powGen, val_pull hJ, val_pull hJ, ← Over.comp_left, ← Over.comp_left, MonObj.comp_pow, lift_snd]
  obtain ⟨o, ho, vo⟩ := exists_symLift_one hL hν 1
  obtain ⟨θ₁, H₁, v₁⟩ := exists_symLift_mulPull hA hL (one_dvd (n ^ 2)) (b := 1) hβ hy (hy.symm ▸ ho)
  obtain ⟨θ₂, H₂, v₂⟩ := exists_symLift_pow hG hA hL H (n ^ 2)
  have e : tval θ₂ (lift (𝟙 T) (1 : T ⟶ A)).left z J = tval θ₁ (lift (𝟙 T) (1 : T ⟶ A)).left z J :=
    val_corr hJ (SymLiftOdd.symLift_unique hG hA hL hn.pow θ₂ θ₁ H₂ H₁) _
  rw [v₂ _ _ z J hJ, v₁ _ _ z J hJ, vo _ _ z J hJ, vβ', vβ', one_pow, _root_.mul_one, _root_.mul_one,
    Category.id_comp] at e
  exact e

end GlobalTheory.TorsFrame

namespace GlobalTheory


open TorsFrame CommPairing in
theorem exists_isTorsFrame_of_symLift : Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (rig : LB.Gen (P.L.pull (eSec P.A))), rig.IsGen → ∀ (n : ℕ), Odd n → ∀ (T : Over S) (y x : T ⟶ P.A), y ^ (n ^ 2) = 1 → y ^ n = x → ∀ θ : ThetaGrp P.A P.L (n ^ 2 : ℕ) T, SymLift P.A P.L (n ^ 2 : ℕ) (n ^ 2) y θ → ∃ τ : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => 1)), IsTorsFrame P rig n x τ := by
  intro hLaw S _ P rig hr n hn T y x hy hx θ H
  subst hx
  have hL := P.isLB
  obtain ⟨α₀, h₀⟩ := hLaw.mulPull S P n
  obtain ⟨α, hα, vα⟩ := exists_norm hL hr h₀
  obtain ⟨ν, hν⟩ := exists_gen_negLB hLaw.globalFns S P 1 T
  have e₁ : y.left ≫ (mulA P.A n).left = (y ^ n).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  have e₂ : (lift (𝟙 T) (1 : T ⟶ P.A)).left ≫ (snd T P.A).left = T.hom ≫ eSec P.A := by
    rw [← Over.comp_left, lift_snd, one_left]
  have e₃ : (lift (𝟙 T) (1 : T ⟶ P.A)).left ≫ (translPt P.A θ.pt).left = y.left := by
    rw [← Over.comp_left, translPt, comp_lift_assoc, lift_fst_assoc, lift_snd, Category.id_comp, H.pt_eq]
    exact congrArg (·.left) (_root_.mul_one y)
  obtain ⟨τ, hτ, vτ⟩ := exists_gen hL (φ' := fun _ : Fin 1 => (y ^ n).left) (ε' := fun _ => 1)
    (fun U _ h => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, e₁, e₂, e₃, Category.comp_id]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen P.L _ _ _ _ (GeneratorPullback.powGen P.L _ _
        (LB.pullGen P.L (fun _ : PUnit => eSec P.A) (fun _ => 1) rig T.hom) (n ^ 2))
      (LB.invGen P.L _ _ (LB.mulGen P.L _ _ _ _
        (LB.pullGen P.L ![(snd T P.A).left, (translPt P.A θ.pt).left] ![(n ^ 2 : ℕ), -(n ^ 2 : ℕ)] θ.φ
          (lift (𝟙 T) (1 : T ⟶ P.A)).left) (LB.pullGen P.L _ _ α y.left))))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.powGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hr _) _)
      (DVR.invGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ θ.isGen _)
        (DVR.pullGen_isGen _ _ _ _ hα _))))
  refine ⟨τ, by rw [← pow_mul, ← sq, hy], hτ, α, hα, corr_of_val hL fun z J hJ => ?_,
    corr_of_val hL fun z J hJ => ?_⟩
  · refine (val_pull hJ _ _ _).trans ((vα _ _ z J hJ).trans (Eq.symm ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) ((map_zpow _ _ _).trans ?_) (val_inv _ _)))))
    rw [← Nat.cast_pow, zpow_natCast]; rfl
  · have a : val (powFrame P.A P.L (y ^ n) τ ((n : ℤ) ^ 2)) (𝟙 _) z J = val τ (𝟙 _) z J ^ (n ^ 2) :=
      (map_zpow _ _ _).trans (by rw [← Nat.cast_pow, zpow_natCast]; rfl)
    have b := tval_pow hLaw.globalFns P.isAb hL hν hn hα hy H hJ
    have c : val (LB.pullGen P.L ![(snd T P.A).left, (translPt P.A θ.pt).left] ![(n ^ 2 : ℕ), -(n ^ 2 : ℕ)] θ.φ
        (lift (𝟙 T) (1 : T ⟶ P.A)).left) (𝟙 T.left) z J = tval θ (lift (𝟙 T) (1 : T ⟶ P.A)).left z J :=
      (val_pull hJ _ _ _).trans (by rw [Category.id_comp]; rfl)
    rw [one_left, vα _ _ z J hJ] at b
    rw [a, vτ _ _ z J hJ, val_mul hJ, val_mul hJ, val_inv, val_mul hJ, c, val_powGen, val_pull hJ, val_pull hJ,
      val_pull hJ, val_rigT rig _ z hJ, Category.id_comp, Category.id_comp, Category.id_comp, mul_pow, inv_pow, mul_pow, b]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    module

end GlobalTheory
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

theorem _root_.GlobalTheory.T.exists_pureWeight_section_reduction : ∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (Y : Scheme.{0}) (L : LB Y), L.IsLB → ∀ (π : Φ.E.B.left ⟶ Y) (N : ℕ) (c : ChartPull Φ.N₀ (npw L N) π) (K K' : Type) [Fintype K] [Fintype K'] (ψ : K → (Φ.E.B.left ⟶ Y)) (ε : K → ℤ) (φt : K' → (Φ.G.left ⟶ Y)) (εt : K' → ℤ) (t : LB.Gen (LB.LinComb L φt εt)), t.IsGen → FormEq (Sum.elim (fun a => Φ.D.q.left ≫ ψ a) φt) (Sum.elim ε εt) (fun _ : Fin 1 => Φ.D.q.left ≫ π) (fun _ => (N : ℤ)) → ∀ α : Φ.E.X, UFib.GenWt Φ.D.i t α → ∀ φ : (Φ.H 1).Sec, Φ.Pure α φ → ∃ b : LB.Sec (LB.LinComb L ψ ε), UFib.Red Φ c t b φ := by
  first | exact @GlobalTheory.ZH.UFib.exists_red_of_pure | exact GlobalTheory.ZH.UFib.exists_red_of_pure | (intros; apply GlobalTheory.ZH.UFib.exists_red_of_pure <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

theorem _root_.GlobalTheory.T.exists_gtDatum_of_torusCoords : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G), ∃ (E : SplitExt (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (xe : E.X ≃+ D.X) (d : E.GtDatum (thickObj R I e G)) (π : E.B.left ⟶ D.P.A.left), IsGrpPullback E.B D.P.A (thick R I e) π ∧ d.q.left ≫ π = g.pG.left ∧ (∀ χ, LBIso (E.O χ).L (LB.LinComb D.P.L (fun a => π ≫ D.Oφ (𝟙 D.P.A) (xe χ) a) Oε)) ∧ ∀ χ, UFib.GenWt (G := thickObj R I e G) d.i (g.t (xe χ)) χ := by
  first | exact @GlobalTheory.ZH.UFib.exists_gtDatum_of_gtCoord | exact GlobalTheory.ZH.UFib.exists_gtDatum_of_gtCoord | (intros; apply GlobalTheory.ZH.UFib.exists_gtDatum_of_gtCoord <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnitTheta

theorem pow_eq_one_iff_of_isGrpPullback {S S' X : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {a' : X ⟶ S'} {a : X ⟶ S} (e : a = a' ≫ f)
    (x' : Over.mk a' ⟶ G') (x : Over.mk a ⟶ G) (hx : x.left = x'.left ≫ φ) (m : ℕ) :
    x' ^ m = 1 ↔ x ^ m = 1 := by
  subst e
  have hx' : x = pushHom h (Over.mk a') x' := Over.OverMorphism.ext hx
  have inj : Function.Injective (pushHom h (Over.mk a')) := fun y y' hy => by
    apply Over.OverMorphism.ext
    apply h.1.hom_ext
    · exact congrArg (fun z => z.left) hy
    · rw [Over.w y, Over.w y']
  have : x ^ m = pushHom h (Over.mk a') (x' ^ m) := by rw [map_pow]; exact congrArg (· ^ m) hx'
  rw [this]
  exact (map_eq_one_iff _ inj).symm

theorem epi_spMap_of_field {K L : Type} [Field K] [Field L] (i : K →+* L) : Epi (spMap i) := by
  have : Flat (spMap i) := by
    letI := i.toAlgebra
    exact HasRingHomProperty.Spec_iff.2 (inferInstance : Module.Flat K L)
  have : Surjective (spMap i) := ⟨fun x => ⟨(⊥ : PrimeSpectrum L), Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem exists_label_of_pow_eq_one : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real)
    (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (m : ℕ), m ∣ S.r * S.N →
    ∀ h : baseOver (Sp u.V) ⟶ u.G, h ^ m = 1 → ∃ b : S.Gam, m • b = 0 ∧ GlobalTheory.UnitTheta.Extends u b h := by
  intro o Ω _ _ _ S ρ p _ y₀ u m hm h hh
  have := u.U.gen_hom
  have hw : h.left ≫ u.G.hom = 𝟙 _ := Over.w h
  let x : Sp (FractionRing u.V) ⟶ pullback u.G.hom (jK u.V) :=
    pullback.lift (jK u.V ≫ h.left) (𝟙 _) (by rw [Category.assoc, hw]; simp)
  have hx₁ : x ≫ pullback.fst _ _ = jK u.V ≫ h.left := pullback.lift_fst _ _ _
  have hx₂ : x ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
  let i : Sp (PadicAlgCl p) ⟶ Sp (FractionRing u.V) := spMap (algebraMap (FractionRing u.V) (PadicAlgCl p))
  have : Epi i := epi_spMap_of_field _
  have hy : spMap y₀ = i ≫ spMap u.yK :=
    (congrArg spMap u.fac).symm.trans (Spec.map_comp (CommRingCat.ofHom u.yK) (CommRingCat.ofHom _))
  have hψ : IsGrpPullback ((Over.pullback (jK u.V)).obj u.G) ρ.P.A (spMap u.yK) (u.U.gen.hom.left ≫ u.φ) :=
    ((isGrpPullback_of_iso u.U.gen).comp u.cart).congr (Category.id_comp _) rfl
  let x' : Over.mk i ⟶ (Over.pullback (jK u.V)).obj u.G :=
    Over.homMk (i ≫ x) (by
      show (i ≫ x) ≫ pullback.snd _ _ = i
      rw [Category.assoc, hx₂, Category.comp_id])
  let t : Over.mk (i ≫ jK u.V) ⟶ baseOver (Sp u.V) := Over.homMk (i ≫ jK u.V) (by simp)
  have h₀ : (t ≫ h) ^ m = 1 := by
    have := (map_pow (preHom (G := u.G) t) h m).symm.trans ((congrArg _ hh).trans (map_one _))
    exact this
  have h₁ : x' ^ m = 1 :=
    (pow_eq_one_iff_of_isGrpPullback (isGrpPullback_pullback u.G (jK u.V)) rfl x' (t ≫ h) (by
      show (i ≫ jK u.V) ≫ h.left = (i ≫ x) ≫ pullback.fst _ _
      rw [Category.assoc, Category.assoc, hx₁]) m).2 h₀
  let z : Over.mk (spMap y₀) ⟶ ρ.P.A := Over.homMk (x'.left ≫ u.U.gen.hom.left ≫ u.φ) (by
    show (x'.left ≫ u.U.gen.hom.left ≫ u.φ) ≫ ρ.P.A.hom = spMap y₀
    rw [Category.assoc, hψ.1.w, ← Category.assoc, Over.w x', hy]; rfl)
  have h₂ : z ^ m = 1 := (pow_eq_one_iff_of_isGrpPullback hψ hy x' z rfl m).1 h₁
  have h₃ : z ^ (S.r * S.N) = 1 := by
    obtain ⟨c, hc⟩ := hm
    rw [hc, pow_mul, h₂, one_pow]
  obtain ⟨b, hb, -⟩ := ρ.pt_bij (PadicAlgCl p) (spMap y₀) z h₃
  have h0 : ρ.pt 0 = 1 := by
    have := ρ.pt_add 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hp : ∀ (n : ℕ) b, ρ.pt (n • b) = ρ.pt b ^ n := fun n b => by
    induction n with
    | zero => rw [zero_smul, pow_zero, h0]
    | succ n ih => rw [succ_nsmul, ρ.pt_add, ih, pow_succ]
  refine ⟨b, ?_, x, hx₁, hx₂, ?_⟩
  · refine (ρ.pt_bij (PadicAlgCl p) (spMap y₀) 1 (one_pow _)).unique ?_ ?_
    · rw [hp, ← h₂, ← hb]
      exact map_pow (preHom (G := ρ.P.A) _) _ m
    · rw [h0]
      exact map_one (preHom (G := ρ.P.A) _)
  · have e : spMap y₀ ≫ (ρ.pt b).left = (i ≫ x) ≫ u.U.gen.hom.left ≫ u.φ := congrArg (fun w => w.left) hb
    rw [← cancel_epi i, ← Category.assoc i (spMap u.yK), ← hy, e, Category.assoc]

end GlobalTheory.UnitTheta
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnitTheta

theorem grpPullback_mul_section {B B' : Scheme.{0}} {G : Over B} {G' : Over B'} [GrpObj G] [GrpObj G']
    {f : B' ⟶ B} {φ : G'.left ⟶ G.left} (H : IsGrpPullback G' G f φ) (x y : baseOver B' ⟶ G')
    (h h' : baseOver B ⟶ G) (hx : x.left ≫ φ = f ≫ h.left) (hy : y.left ≫ φ = f ≫ h'.left) :
    (x * y).left ≫ φ = f ≫ (h * h').left := by
  let U : Over.mk ((baseOver B').hom ≫ f) ⟶ baseOver B := Over.homMk f (by simp)
  have e := H.2 (baseOver B') x y (U ≫ h) (U ≫ h') hx.symm hy.symm
  rw [← MonObj.comp_mul] at e
  exact e.symm

theorem extends_mul (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ)
    [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (a b : S.Gam) (h h' : baseOver (Sp u.V) ⟶ u.G)
    (ha : Extends u a h) (hb : Extends u b h') : Extends u (a + b) (h * h') := by
  obtain ⟨x, x1, x2, x3⟩ := ha
  obtain ⟨y, y1, y2, y3⟩ := hb
  have := u.U.gen_hom
  let X : baseOver (Sp (FractionRing u.V)) ⟶ (Over.pullback (jK u.V)).obj u.G := Over.homMk x x2
  let Y : baseOver (Sp (FractionRing u.V)) ⟶ (Over.pullback (jK u.V)).obj u.G := Over.homMk y y2
  refine ⟨(X * Y).left, ?_, Over.w (X * Y), ?_⟩
  · exact grpPullback_mul_section (isGrpPullback_pullback u.G (jK u.V)) X Y h h' x1 y1
  · rw [ρ.pt_add]
    exact grpPullback_mul_section
      (((isGrpPullback_of_iso u.U.gen).comp u.cart).congr (Category.id_comp _) rfl) X Y _ _ x3 y3

end GlobalTheory.UnitTheta
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

theorem _root_.GlobalTheory.T.exists_splitTorusExtension_descent_galois_invariant : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K] (G₀ B₀ : Over (Sp k)) [GrpObj G₀] [IsCommMonObj G₀] [GrpObj B₀], IsAbelianScheme B₀ → ∀ (G B : Over (Sp K)) [GrpObj G] [GrpObj B] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (φG : G.left ⟶ G₀.left) (φ : B.left ⟶ B₀.left), IsGrpPullback G G₀ (spMap (algebraMap k K)) φG → IsGrpPullback B B₀ (spMap (algebraMap k K)) φ → ∀ (q : G ⟶ B) (i : splitTorus (Sp K) X ⟶ G), IsMonHom q → Flat q.left → Surjective q.left → QuasiCompact q.left → IsMonHom i → IsPullback i (toUnit _) q (η[B] : 𝟙_ _ ⟶ B) → (∀ (τ : K ≃ₐ[k] K) (s : G.left ⟶ G.left), s ≫ φG = φG → s ≫ G.hom = G.hom ≫ spMap (τ : K →+* K) → s ≫ q.left ≫ φ = q.left ≫ φ ∧ GlobalTheory.SplitTorus.bcMap (spMap (τ : K →+* K)) X ≫ i.left = i.left ≫ s) → ∃ S : SplitExt (Sp k), S.IsGt G₀ := by
  first | exact @GlobalTheory.exists_splitExt_of_galois_invariant | exact GlobalTheory.exists_splitExt_of_galois_invariant | (intros; apply GlobalTheory.exists_splitExt_of_galois_invariant <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem splitTorus_point_eq_one_of_axes (K : Type) [Field K] [IsAlgClosed K] (E : SplitExt (Sp K))
    (G : Over (Sp K)) [GrpObj G] (h : E.IsGt G) (X : Type) [AddCommGroup X]
    (t : G ⊗ G ⟶ splitTorus (Sp K) X)
    (h₁ : lift (𝟙 G) (1 : G ⟶ G) ≫ t = 1) (h₂ : lift (1 : G ⟶ G) (𝟙 G) ≫ t = 1) : t = 1 := by
  have key : ∀ (a : G ⟶ G ⊗ G), a ≫ t = 1 → ∀ χ : X, a.left.appTop.hom
      (splitTorusPointsEquiv (Sp K) X (G ⊗ G) t (Multiplicative.ofAdd χ)).val = 1 := by
    intro a ha χ
    have := splitTorusPointsEquiv_val (Sp K) X G (a ≫ t) χ
    rw [Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, ha, map_one] at this
    rw [splitTorusPointsEquiv_val]
    exact this.symm
  apply (splitTorusPointsEquiv (Sp K) X (G ⊗ G)).injective
  rw [map_one]
  ext χ
  exact unit_eq_one_of_axes_of_isGt K E G h _ (Units.isUnit _) (key _ h₁ χ) (key _ h₂ χ)

theorem isMonHom_of_isGt_of_one :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (E E' : SplitExt (Sp K)) (G G' : Over (Sp K)) [GrpObj G] [GrpObj G'] [IsCommMonObj G] [IsCommMonObj G'], E.IsGt G → E'.IsGt G' → ∀ f : G ⟶ G', η[G] ≫ f = η[G'] → IsMonHom f := by
  intro K _ _ E E' G G' _ _ _ _ h ⟨D⟩ f hf
  have := D.q_hom
  have := D.i_hom
  have hk := D.isKernel
  have hq : IsMonHom (f ≫ D.q) := GlobalTheory.T.isMonHom_pointed_splitExt_to_abelianVariety K E G h E'.B E'.isAbelian (f ≫ D.q) (by
    rw [reassoc_of% hf]; exact IsMonHom.one_hom D.q)
  have hf1 : ∀ {W : Over (Sp K)}, (1 : W ⟶ G) ≫ f = 1 := by
    intro W
    rw [Hom.one_def, Hom.one_def, Category.assoc, hf]
  let d : G ⊗ G ⟶ G' := ((fst G G * snd G G) ≫ f) / ((fst G G ≫ f) * (snd G G ≫ f))
  have hd : d ≫ D.q = 1 := by
    simp only [d]
    rw [GrpObj.div_comp, Category.assoc, MonObj.mul_comp, MonObj.mul_comp, Category.assoc,
      Category.assoc, div_self']
  let t : G ⊗ G ⟶ splitTorus (Sp K) E'.X := hk.lift d (toUnit _) (by rw [hd, Hom.one_def])
  have ht : t ≫ D.i = d := hk.lift_fst _ _ _
  have inj : ∀ a : G ⟶ G ⊗ G, a ≫ d = 1 → a ≫ t = 1 := fun a ha =>
    hk.hom_ext (by rw [Category.assoc, ht, ha, MonObj.one_comp]) (toUnit_unique _ _)
  have t1 : t = 1 := by
    refine splitTorus_point_eq_one_of_axes K E G h E'.X t (inj _ ?_) (inj _ ?_)
    · simp only [d]
      rw [GrpObj.comp_div, MonObj.comp_mul, ← Category.assoc, MonObj.comp_mul, lift_fst, lift_snd,
        lift_fst_assoc, lift_snd_assoc, hf1, _root_.mul_one, _root_.mul_one, div_self']
    · simp only [d]
      rw [GrpObj.comp_div, MonObj.comp_mul, ← Category.assoc, MonObj.comp_mul, lift_fst, lift_snd,
        lift_fst_assoc, lift_snd_assoc, hf1, _root_.one_mul, _root_.one_mul, div_self']
  rw [t1, MonObj.one_comp] at ht
  have hm : (fst G G * snd G G) ≫ f = (fst G G ≫ f) * (snd G G ≫ f) := div_eq_one.mp ht.symm
  refine ⟨hf, ?_⟩
  rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at hm
  rw [hm]
  congr 1

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.degenerationData_iso_of_two_witnesses : Laws → Laws2 → Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b : c.V W₀ →+* O') (a : ArcIn D l (c.V W₀).subtype O' b) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (I : Ideal R) (f : O' →+* R) (u : R), AdmBase R I → I ≠ ⊤ → Function.Injective f → ∀ (χ χ' : Sp R ⟶ Y.X) (W : ArcWit Y a I f u χ) (W' : ArcWit Y a I f u χ'), ∃ hD : IsPullDeg (RingHom.id R) W.P.D.toPre W'.P.D.toPre, (∀ y, hD.xe (W'.e y) = W.e y) ∧ (∀ x, (letI := H.starRing; W'.P.oD.onB.act x ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf (RingHom.id R))).map (W.P.oD.onB.act x))) ∧ ∃ w' : LB.Iso W'.P.D.toPre.P.L (a.D₀.P.L.pull ((hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (specOf (RingHom.id R))) ≫ W.φ)), W'.φ = (hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (specOf (RingHom.id R))) ≫ W.φ ∧ HEq W'.w w' ∧ Tri W.w hD.w w' := by
  first | exact @GlobalTheory.WitnessData.witness_data_iso | exact GlobalTheory.WitnessData.witness_data_iso | (intros; apply GlobalTheory.WitnessData.witness_data_iso <;> assumption)
end
