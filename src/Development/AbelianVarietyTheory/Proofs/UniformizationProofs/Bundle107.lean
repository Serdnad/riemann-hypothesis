module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle003
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle015
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CrossRelationGivesConvolutionRelation
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProductOfSectionsExpandsToConvolution
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.WeilQkPairingExistsUniqueTorus
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle016
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle094
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle103
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle042
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle028
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle010
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle021
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle102
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle101
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle038
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle049
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle104
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle016
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsFamRep
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

theorem _root_.GlobalTheory.T.expBij_of_match_of_fam_expF : Laws → Laws2 → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (D : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : PreU (IsLocalRing.maximalIdeal V) D.toPre A G) (U' : UnifPre (IsLocalRing.maximalIdeal V) D A G), Match U U' → ∀ k : ℕ, 1 ≤ k → U.FE (FractionRing V) k → (∀ s : Fam D.toPre (FractionRing V) k, ∃ t, U.ExpF (FractionRing V) k t s.s) → U'.ExpBij k := by
  first | exact @GlobalTheory.ExpansionClause.expBij_of_match | exact GlobalTheory.ExpansionClause.expBij_of_match | (intros; apply GlobalTheory.ExpansionClause.expBij_of_match <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

theorem _root_.GlobalTheory.T.thetaExpansion_functionalEquation_degree_one : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → PsiRel D (𝟙_ _) f → U.FE (Kbar V) 1) := by
  first | exact @GlobalTheory.UU.fe_one_of_psiRel | exact GlobalTheory.UU.fe_one_of_psiRel | (intros; apply GlobalTheory.UU.fe_one_of_psiRel <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.UT

theorem dim_eq_rank_add_dim :
    LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => A.g = D.toPre.rank + D.toPre.P.g := by
  rintro ⟨hL, hL₂, -, -, -⟩ R _ _ _ I hadm D A G _ _ hG U
  haveI := hG.geomConnected
  have h₁ := GlobalTheory.finrank_fam_of_expBij hL.secBaseChange R I hadm D A G U.toUnifPre 2 (by norm_num)
    (U.expand 2 (by norm_num))
  have h₂ := (GlobalTheory.FamDimension.main hL.globalFns hL.cube hL.square hL₂.secTwist R I D (FractionRing R) 2
    (by norm_num)).2
  exact Nat.pow_right_injective (le_refl 2) (h₁.symm.trans h₂)

end GlobalTheory.UT
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

theorem _root_.GlobalTheory.T.indAt_comp_equiv_unique_id : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (N : ℕ), 1 ≤ N → ∀ (p p' p'' : QkPt D.toPre F N) (ψ ψ' : (TFK (R := R) F ⊗ A.A) ⟶ (TFK (R := R) F ⊗ A.A)), IndAt U.toUnifPre F N p ψ → (IndAt U.toUnifPre F N p' ψ' → QkAdd p p' p'' → IndAt U.toUnifPre F N p'' (ψ ≫ ψ')) ∧ (QkPt.Equiv D.toPre F p p' → IndAt U.toUnifPre F N p' ψ) ∧ (4 ≤ N → IndAt U.toUnifPre F N p ψ' → ψ = ψ') ∧ (p'.y = 0 → p'.g.IsZero → IndAt U.toUnifPre F N p' (𝟙 _)) := by
  first | exact @GlobalTheory.UT.IndComp.indAt_comp_unique | exact GlobalTheory.UT.IndComp.indAt_comp_unique | (intros; apply GlobalTheory.UT.IndComp.indAt_comp_unique <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

theorem _root_.GlobalTheory.T.crossRelation_gives_convolution_relation : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (E : EndU U.toUnifPre) (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (j j' : ℕ), 1 ≤ j → 1 ≤ j' → ∀ (t₁ t₂ : SecA A F j) (t₁' t₂' : SecA A F j') s₁ s₂ s₁' s₂', U.ExpandsF F j w₀ t₁ s₁ → U.ExpandsF F j w₀ t₂ s₂ → U.ExpandsF F j' w₀ t₁' s₁' → U.ExpandsF F j' w₀ t₂' s₂' → Cross E.aA t₁ t₂ t₁' t₂' → ∀ (g g' : GtPtF D.toPre F), E.Act g g' → ∀ (w : Frm D.toPre F j g'.b) (w' : Frm D.toPre F j' g.b), w.IsGen → w'.IsGen → ∀ α, SumF I F (fun p : {p : D.toPre.X × D.toPre.X // E.h p.1 + p.2 = α} => coef s₁ g' w p.1.1 * coef s₂' g w' p.1.2 - coef s₂ g' w p.1.1 * coef s₁' g w' p.1.2) 0 := by
  first | exact @GlobalTheory.UT.MixedConv.sumF_conv_of_cross | exact GlobalTheory.UT.MixedConv.sumF_conv_of_cross | (intros; apply GlobalTheory.UT.MixedConv.sumF_conv_of_cross <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

theorem _root_.GlobalTheory.T.product_of_sections_expands_to_convolution : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (k k' k'' : ℕ), 1 ≤ k → 1 ≤ k' → k'' = k + k' → ∀ (t : SecA A F k) (t' : SecA A F k') (t'' : SecA A F k'') s s' s'', U.ExpandsF F k w₀ t s → U.ExpandsF F k' w₀ t' s' → U.ExpandsF F k'' w₀ t'' s'' → (∀ z J, Good A.L z J → sA t'' (𝟙 _) z J = sA t (𝟙 _) z J * sA t' (𝟙 _) z J) → ∀ (g : GtPtF D.toPre F) (w : Frm D.toPre F k g.b) (w' : Frm D.toPre F k' g.b) (w'' : Frm D.toPre F k'' g.b), w.IsGen → w'.IsGen → w''.IsGen → (∀ z J, Good D.toPre.P.L z J → val w'' (𝟙 _) z J = val w (𝟙 _) z J * val w' (𝟙 _) z J) → ∀ α, SumF I F (fun χ => coef s g w χ * coef s' g w' (α - χ)) (coef s'' g w'' α) := by
  first | exact @GlobalTheory.UT.ProdConv.main | exact GlobalTheory.UT.ProdConv.main | (intros; apply GlobalTheory.UT.ProdConv.main <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
theorem _root_.GlobalTheory.T.weilQk_pairing_existsUnique_torus : LL → AllD fun {R} _ _ {I} D F _ _ => ∀ (k : ℕ), 1 ≤ k → ∀ p p' : QkPt D.toPre F k, (∃! ζ : Fˣ, WeilQkIs D.toPre F k p p' ζ) ∧ ∀ t, p.y = 0 → IsTor t p.g → WeilQkIs D.toPre F k p p' (t (Multiplicative.ofAdd p'.y)).val := by
  first | exact @GlobalTheory.weilQk_existsUnique | exact GlobalTheory.weilQk_existsUnique | (intros; apply GlobalTheory.weilQk_existsUnique <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.UT.WeilAbelianPart

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem translPt_eq (b : TF (R := R) F ⟶ D.P.A) : translPt D.P.A b = DegPre.trPt D F b ≫ DegPre.prB D F :=
  (_root_.mul_comm (fst (TF (R := R) F) D.P.A ≫ b) (DegPre.prB D F)).trans (tr_pr D F b).symm

theorem translT_eq (b : TF (R := R) F ⟶ D.P.A) : translT D.P.A b = DegPre.trPt D F b := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [tr_fst, translT, lift_fst]
  · rw [translT, lift_snd, translPt_eq]

theorem exists_theta (hG : GlobalFnsSt) {k : ℕ} (p : QkPt D F k) (hy : p.y = 0) (w : Frm D F k p.g.b)
    (hw : w.IsGen) : ∃ θ : ThetaGrp D.P.A D.P.L (k : ℤ) (TF (R := R) F), θ.pt = p.g.b ∧
      ∀ s t : Fam D F k, PhiRel D F k p w s t → ∀ (ρ : DegPre.BF D F ⟶ DegPre.BF D F) z J, Good D.P.L z J →
        sval (t.s 0) ρ.left z J = sval (s.s 0) (ρ ≫ DegPre.trPt D F p.g.b).left z J *
          (CommPairing.tval θ ρ.left z J).val := by
  obtain ⟨⟨u, hu, hc⟩, hv⟩ := gen_phi hG p w hw 0
  obtain ⟨v, hvg, hvv⟩ := exists_gen D.P.isLB (K' := Fin 2)
    (φ' := ![(snd (TF (R := R) F) D.P.A).left, (translPt D.P.A p.g.b).left])
    (ε' := ![(k : ℤ), -(k : ℤ)]) (fun U _ h => by
      have a := ThetaPow.prod_fam_zero D F k (fun q => h ((DegPre.trPt D F p.g.b).left ≫ q))
      have c : ∏ i, h (DegPre.famφ D F (0 + p.y) i) ^ DegPre.famε k i = h (DegPre.prB D F).left ^ k := by
        rw [hy, add_zero]; exact ThetaPow.prod_fam_zero D F k h
      refine Eq.trans (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ c (prod_neg _ _ a)) ?_
      rw [Fin.prod_univ_two, translPt_eq]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg, zpow_natCast, Over.comp_left]) u hu
  refine ⟨⟨p.g.b, v, hvg⟩, rfl, fun s t H ρ z J hJ => ?_⟩
  have e := (phiRel_iff hG p w hw s t).1 H 0 0 (by rw [hy, add_zero]) _ ρ z J hJ
  rw [← hv u hu hc _ ρ z J hJ, ← hvv _ _ z J hJ] at e
  exact e

theorem eq_of_sval {k : ℕ} (s : Fam D F k) (hs : ¬ ∀ j, (s.s 0).f j = 0) {c c' : F}
    (h : ∀ y J, Good D.P.L y J → sval ((c • s).s 0) (𝟙 _) y J = sval ((c' • s).s 0) (𝟙 _) y J) : c = c' := by
  by_contra hne
  refine hs fun j => sec_ext_val (s' := SecOps.secZero) D.P.isLB (fun y J hJ => ?_) j
  have e : s = (c - c')⁻¹ • (c • s + (-1 : F) • c' • s) := by
    rw [neg_one_smul, ← sub_eq_add_neg, ← sub_smul, smul_smul, inv_mul_cancel₀ (sub_ne_zero.2 hne), one_smul]
  have e₀ : c' • s + (-1 : F) • c' • s = 0 := by rw [neg_one_smul, add_neg_cancel]
  have e₁ := sval_add (c' • s) ((-1 : F) • c' • s) 0 (𝟙 _) y hJ
  rw [e₀, UUA.sval_zero_of (s := (0 : Fam D F k).s 0) (fun _ => rfl) _ y J (hJ.mem _ _)] at e₁
  rw [e, sval_smul _ _ _ _ y hJ, sval_add _ _ _ _ y hJ, h y J hJ, ← e₁, mul_zero,
    UUA.sval_zero_of (s := SecOps.secZero) (fun _ => rfl) _ y J (hJ.mem _ _)]

attribute [local instance] TorusExt.gtGroup in
theorem qkAdd_swap (hB : D.TauBimult) {k : ℕ} (p p' : QkPt D F k) : QkAdd p' p (TorusExt.qkAdd hB p p') := by
  have : TorusExt.qkAdd hB p p' = TorusExt.qkAdd hB p' p := TorusExt.qk_ext (add_comm _ _) (add_comm p.g p'.g)
  rw [this]
  exact TorusExt.qkAdd_qkAdd hB p' p

theorem weilQkIs_iff_weilIs_abelianPart : LL → AllD fun {R} _ _ {I} D F _ _ => ∀ (k : ℕ), 1 ≤ k → ∀ p p' : QkPt D.toPre F k, p.y = 0 → p'.y = 0 → ∀ ζ : Fˣ, WeilQkIs D.toPre F k p p' ζ ↔ WeilIs D.toPre.P.A D.toPre.P.L k p.g.b p'.g.b (Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom.toMonoidHom ζ) := by
  intro hL R _ _ _ I hI D F _ _ _ k hk p p' hy hy' ζ
  have hG := hL.1.globalFns
  have hB := D.tau_bimult
  obtain ⟨Φ, h₁, -, h₃, -, h₅, -⟩ := PhiProj.phi_projective hL R I hI D F k hk
  obtain ⟨w, hw⟩ := (CoefBasic.coef_basic R D.toPre F k p.g).1
  obtain ⟨w', hw'⟩ := (CoefBasic.coef_basic R D.toPre F k p'.g).1
  obtain ⟨v, hv, ev⟩ := h₅ p p' _ w w' hw hw' (TorusExt.qkAdd_qkAdd hB p p')
  obtain ⟨v', hv', ev'⟩ := h₅ p' p _ w' w hw' hw (qkAdd_swap hB p p')
  obtain ⟨c, -, hc⟩ := h₃ _ v' v hv' hv
  rw [ev, ev'] at hc
  have hc' : ∀ s, Φ p w (Φ p' w' s) = c • Φ p' w' (Φ p w s) := fun s => LinearMap.congr_fun hc s
  have r : ∀ s, PhiRel D.toPre F k p w s (Φ p w s) := fun s => ((h₁ p w hw).2 _ _).2 rfl
  have r' : ∀ s, PhiRel D.toPre F k p' w' s (Φ p' w' s) := fun s => ((h₁ p' w' hw').2 _ _).2 rfl
  obtain ⟨σ, hσ⟩ := FamFree.exists_sec_ne_zero (D := D.toPre) (F := F) hL.2.1.secTwist hk 0
  obtain ⟨t, rfl, -⟩ := FamFree.exists_fam_single hG hB hk 0 σ
  obtain ⟨t, rfl⟩ := (h₁ p' w' hw').1.2 t
  obtain ⟨s, rfl⟩ := (h₁ p w hw).1.2 t
  have key := weilQkIs_iff_of_comm hG D p p' w w' hw hw' c (fun s s₁ s₂ s₃ s₄ a₁ a₂ a₃ a₄ => by
    rw [((h₁ p w hw).2 _ _).1 a₂, ((h₁ p' w' hw').2 _ _).1 a₁, ((h₁ p' w' hw').2 _ _).1 a₄,
      ((h₁ p w hw).2 _ _).1 a₃, hc']) ⟨s, _, _, r s, r' _, fun h0 => hσ fun j => by rw [h0]; rfl⟩ hk (ζ : F)
  obtain ⟨θ, hp, hθ⟩ := exists_theta hG p hy w hw
  obtain ⟨θ', hp', hθ'⟩ := exists_theta hG p' hy' w' hw'
  obtain ⟨c₀, hc₀⟩ := CommutatorPairing.exists_commIsOf hG D.toPre.P.isAb D.toPre.P.isLB θ θ'
  obtain ⟨z, rfl⟩ : ∃ z : Fˣ, unitOn z = c₀ :=
    ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom.toMonoidHom c₀, Units.ext (by simp [unitOn])⟩
  have hz := GlobalLift.weilIs_of_commIsOf hG D.toPre.P.isAb D.toPre.P.isLB hc₀
  rw [hp, hp'] at hz
  have hcz : c = (z : F) := eq_of_sval _ hσ fun y J hJ => by
    have e := congrArg Units.val ((CommPairing.commIsOf_iff D.toPre.P.isLB θ θ' _).1 hc₀ _ (𝟙 _) y J hJ)
    rw [Units.val_mul, Units.val_mul, Units.val_mul, ← gs_unit _ _ ⊤ trivial, hp, hp', translT_eq, translT_eq] at e
    have a₂ := hθ _ _ (r (Φ p' w' s)) (𝟙 _) y J hJ
    have a₁ := hθ' _ _ (r' s) (𝟙 _ ≫ DegPre.trPt D.toPre F p.g.b) y J hJ
    have a₄ := hθ' _ _ (r' (Φ p w s)) (𝟙 _) y J hJ
    have a₃ := hθ _ _ (r s) (𝟙 _ ≫ DegPre.trPt D.toPre F p'.g.b) y J hJ
    rw [a₁] at a₂
    rw [a₃] at a₄
    simp only [Category.id_comp, Over.id_left] at a₂ a₄ e
    rw [← hc', sval_smul _ _ _ _ y hJ, a₂, a₄, tr_comm, _root_.mul_assoc, _root_.mul_comm (Units.val _), e,
      Category.id_comp]
    show _ * (_ * _ * gs _ y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (z : F))) = _
    ring
  rw [key, hcz]
  constructor
  · intro H
    obtain rfl : ζ = z := Units.ext H
    exact hz
  · intro H
    exact congrArg Units.val (H1.unitOn_injective
      (CommutatorPairing.weilIs_unique hG D.toPre.P.isAb D.toPre.P.isLB H hz))

end GlobalTheory.UT.WeilAbelianPart
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KernelRep

theorem exists_finite_closed_kernel : GlobalFnsSt → ∀ (V : Type) [CommRing V] (B : Over (Sp V)) [GrpObj B], IsAbelianScheme B → ∀ L : LB B.left, L.IsLB → RelAmple B L → ∃ (H : Over (Sp V)) (j : H ⟶ B), IsClosedImmersion j.left ∧ IsFinite H.hom ∧ (∀ (T : Over (Sp V)) (x : T ⟶ B), GlobalTheory.MemKL B L x ↔ ∃ z : T ⟶ H, z ≫ j = x) := by
  intro hG V _ B _ hB L hL hA
  have hP : IsProjBy B.hom := (GlobalTheory.AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral _ B L hB hL hA V
    (𝟙 _) B.left (𝟙 _) B.hom IsPullback.of_id_fst).1
  obtain ⟨hO, -, hK⟩ := GlobalTheory.UU.TrivTwist.inK_iff_trivial_twist _ B L hL
  obtain ⟨H, j, hj, hH⟩ := GlobalTheory.T.exists_closed_subscheme_translation_kernel hG V B hB hP L (pw L 0) hL hO
  have : IsCommMonObj B := hB.comm
  exact ⟨H, j, hj, GlobalTheory.AmpleStabFinite.isFinite_of_relAmple hG V B hB L (pw L 0) hL hO hA H j hj hH,
    fun T x => (hK _ rfl T x).trans (hH T x)⟩

end GlobalTheory.KernelRep
end

section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PhiBase

theorem exists_pull_sec {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (t : Y' ⟶ Y) (g : Y' ⟶ X)
    (hg : t ≫ f = g) (θ : LB.Sec (L.pull f)) : ∃ θ' : LB.Sec (L.pull g),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J), Good L z J →
        sval (L := L) (φ := fun _ : PUnit => g) (ε := fun _ => 1) θ' r z J =
          sval (L := L) (φ := fun _ : PUnit => f) (ε := fun _ => 1) θ (r ≫ t) z J := by
  subst hg
  obtain ⟨θ', h⟩ := exists_sec hL (φ' := fun _ : PUnit => t ≫ f) (ε' := fun _ => 1)
    (fun U _ h => by simp [Fintype.prod_sum_type])
    (pullMulSec (L := L) (φ := fun _ : PUnit => f) (ε := fun _ => 1) θ t (LB.oneGen L (Y := Y'))
      (fun _ _ => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm))
  refine ⟨θ', fun Z r z J hJ => ?_⟩
  refine (h Z r z J hJ).trans ((sval_pullMulSec _ _ _ _ _ z hJ).trans ?_)
  rw [val_one, Units.val_one, _root_.mul_one]

theorem trPt_inv_comp {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (b : TF (R := R) F ⟶ D.P.A) :
    DegPre.trPt D F b⁻¹ ≫ DegPre.trPt D F b = 𝟙 _ := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, DVR.tr_fst, DVR.tr_fst, Category.id_comp]
  · have : (DegPre.trPt D F b⁻¹ ≫ DegPre.trPt D F b) ≫ DegPre.prB D F = DegPre.prB D F := by
      rw [Category.assoc, DVR.tr_pr, MonObj.comp_mul, DVR.tr_pr, ← Category.assoc, DVR.tr_fst, _root_.mul_assoc,
        ← MonObj.comp_mul, inv_mul_cancel, MonObj.comp_one, _root_.mul_one]
    exact this.trans (Category.id_comp _).symm

theorem prod_comp_fam_zero {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (k : ℕ) (t : DegPre.BF D F ⟶ DegPre.BF D F) {U : Type} [CommGroup U]
    (h : ((DegPre.BF D F).left ⟶ D.P.A.left) → U) :
    ∏ i, h (t.left ≫ DegPre.famφ D F 0 i) ^ DegPre.famε k i = h (t ≫ DegPre.prB D F).left ^ k :=
  ThetaPow.prod_fam_zero D F k (fun q => h (t.left ≫ q))

theorem b_eq_of_phiRel : GlobalFnsSt → SecTwistSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (n : ℕ), 1 ≤ n → ∀ (p p' : QkPt D F n) (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε n))) (w' : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p'.g.b) (DegPre.lineε n))), w.IsGen → w'.IsGen → (∀ s : Fam D F n, ∃ s' : Fam D F n, PhiRel D F n p w s s' ∧ PhiRel D F n p' w' s s') → p'.y = p.y → p.g.b = p'.g.b := by
  intro hG hT R _ _ D hB F _ _ n hn p p' w w' hw hw' H hy
  have hL := D.P.isLB
  obtain ⟨θ, σ, hθ, hσ⟩ := ThetaPow.exists_theta_pow hT R D F n hn
  obtain ⟨s, hs, -⟩ := FamFree.exists_fam_single hG hB hn 0 σ
  obtain ⟨s', h₁, h₂⟩ := H s
  have v₁ := (DVR.phiRel_iff hG p w hw s s').1 h₁ 0 p.y (zero_add _) _ (𝟙 _)
  have v₂ := (DVR.phiRel_iff hG p' w' hw' s s').1 h₂ 0 p.y ((zero_add _).trans hy) _ (𝟙 _)
  obtain ⟨⟨u, hu, hc⟩, hv⟩ := DVR.gen_phi hG p w hw 0
  obtain ⟨⟨u', hu', hc'⟩, hv'⟩ := DVR.gen_phi hG p' w' hw' 0
  obtain ⟨θ₁, hθ₁⟩ := exists_pull_sec hL (DegPre.prB D F).left (DegPre.trPt D F p.g.b).left
    (DegPre.trPt D F p.g.b ≫ DegPre.prB D F).left rfl θ
  obtain ⟨θ₂, hθ₂⟩ := exists_pull_sec hL (DegPre.prB D F).left (DegPre.trPt D F p'.g.b).left
    (DegPre.trPt D F p'.g.b ≫ DegPre.prB D F).left rfl θ
  obtain ⟨v, hvg, hvv⟩ := exists_gen hL (K' := Fin 2)
    (φ' := ![(DegPre.trPt D F p.g.b ≫ DegPre.prB D F).left, (DegPre.trPt D F p'.g.b ≫ DegPre.prB D F).left])
    (ε' := ![(n : ℤ), -(n : ℤ)]) (fun U _ h => by
      have a := prod_comp_fam_zero D F n (DegPre.trPt D F p.g.b) h
      have a' := prod_comp_fam_zero D F n (DegPre.trPt D F p'.g.b) h
      have c : ∏ i, h (DegPre.famφ D F (0 + p'.y) i) ^ DegPre.famε n i =
        ∏ i, h (DegPre.famφ D F (0 + p.y) i) ^ DegPre.famε n i := by rw [hy]
      refine Eq.trans (DVR.prod_sum₂ (K := Fin 4 ⊕ Fin 4) (K' := Fin 4 ⊕ Fin 4) (U := U) _
        (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ c (DVR.prod_neg _ _ a'))
        (DVR.prod_neg _ _ (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _
          (c := ∏ i, h (DegPre.famφ D F (0 + p.y) i) ^ DegPre.famε n i) rfl (DVR.prod_neg _ _ a)))) ?_
      rw [Fin.prod_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg, zpow_natCast]
      rw [mul_inv, inv_inv, _root_.mul_mul_mul_comm, mul_inv_cancel, _root_.one_mul, _root_.mul_comm])
    (LB.mulGen D.P.L _ _ _ _ u' (LB.invGen D.P.L _ _ u))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hu' (DVR.invGen_isGen _ _ _ _ hu))
  obtain ⟨hI, hN⟩ := degPre_abelianPart_isIntegral_and_isIntegrallyClosed_stalk R D F
  have hne : ∃ j, θ₂.f j ≠ 0 := by
    by_contra h0
    have h0' : ∀ j, θ₂.f j = 0 := fun j => by_contra fun hj => h0 ⟨j, hj⟩
    obtain ⟨j, hj⟩ := hθ
    refine hj (sec_ext_val (L := D.P.L) (φ := fun _ : PUnit => (DegPre.prB D F).left) (ε := fun _ => 1) (s := θ)
      (s' := DVR.SecOps.secZero) hL (fun y J hJ => ?_) j)
    have e := hθ₂ _ (DegPre.trPt D F p'.g.b⁻¹).left y J hJ
    rw [← Over.comp_left, trPt_inv_comp, Over.id_left] at e
    rw [← e, DVR.UUA.sval_zero_of h0' _ y J (hJ.mem _ _),
      DVR.UUA.sval_zero_of (s := DVR.SecOps.secZero) (fun _ => rfl) _ y J (hJ.mem _ _)]
  obtain ⟨r, hr, -⟩ := RootUnit.exists_gen_of_pow _ _ hN D.P.L hL _ _ n hn θ₁ θ₂ v hvg hne (fun y J hJ => by
    have e₁ := v₁ y J hJ
    have e₂ := v₂ y J hJ
    rw [← hv u hu hc _ (𝟙 _) y J hJ, hs, hσ _ _ y J hJ] at e₁
    rw [← hv' u' hu' hc' _ (𝟙 _) y J hJ, hs, hσ _ _ y J hJ] at e₂
    have e := e₁.symm.trans e₂
    have f₁ := hθ₁ _ (𝟙 _) y J hJ
    have f₂ := hθ₂ _ (𝟙 _) y J hJ
    simp only [Category.id_comp, Over.id_left] at e f₁ f₂
    rw [← f₁, ← f₂] at e
    rw [hvv _ _ y J hJ, val_mul hJ, val_inv, Units.val_mul, mul_right_comm, _root_.mul_comm (Units.val _)]
    exact ((Units.eq_mul_inv_iff_mul_eq _).2 e))
  exact eq_of_isGen_transl R D F _ _ r hr

end GlobalTheory.PhiBase
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UU

theorem finrank_fam_of_laws : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → Module.Finite F (Fam D F k) ∧ Module.finrank F (Fam D F k) = k ^ (D.P.g + D.rank) :=
  fun h₁ h₂ _ _ _ D hB F _ _ k hk => by
    rw [Nat.add_comm]
    exact GlobalTheory.FamDimension.finrank_fam (D := D) (F := F) h₁.globalFns h₂.secTwist hB hk

end GlobalTheory.UU
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem exists_basis_twist_field : Laws → Laws2 → (∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → ∀ α : D.X, ∃ b : Fin (k ^ D.P.g) → LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k)), ∀ s : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k)), ∃! c : Fin (k ^ D.P.g) → F, ∀ j, s.f j = ∑ i, DegPre.constBF D F (c i) _ * (b i).f j) :=
  fun _ h₂ _ _ _ D F _ _ _ hk α =>
    GlobalTheory.FamDimension.exists_basis_famSec (D := D) (F := F) h₂.secTwist hk α

end GlobalTheory.UU
end
