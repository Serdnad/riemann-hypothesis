module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2887
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Order.CompletePartialOrder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2888
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2895
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle536
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2968
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2969
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2965
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2896
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle777
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CrossRelationGivesConvolutionRelation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2975
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle028
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2899
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2927
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2926
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle490
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle107
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle201
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2930
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.finiteGeneratedSubring_localised_basicOpen : ∀ {S : Scheme.{0}} {K : Type} [Field K] (gp : Sp K ⟶ S) [IsLocallyNoetherian S] {r : ℕ} (V : Fin r → S.Opens)
    (t : ∀ i, Finset Γ(Sp K, gp ⁻¹ᵁ V i)) (W : S.Opens), IsAffineOpen W → ∀ (f : Γ(S, W))
    (x : Γ(Sp K, gp ⁻¹ᵁ S.basicOpen f)), x ∈ finFam gp V t (S.basicOpen f) →
    ∃ (k : ℕ) (y : Γ(Sp K, gp ⁻¹ᵁ W)), y ∈ finFam gp V t W ∧
      resK gp (S.basicOpen_le f) y = resK gp (S.basicOpen_le f) ((gp.app W).hom f) ^ k * x := by
  first | exact @GlobalTheory.Mum.finFam_basicOpen_loc | exact GlobalTheory.Mum.finFam_basicOpen_loc | (intros; apply GlobalTheory.Mum.finFam_basicOpen_loc <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem finFam_finite : ∀ {S : Scheme.{0}} {K : Type} [Field K] (gp : Sp K ⟶ S) [IsLocallyNoetherian S] {r : ℕ} (V : Fin r → S.Opens)
    (t : ∀ i, Finset Γ(Sp K, gp ⁻¹ᵁ V i)), (⨆ i, V i) = ⊤ →
    (∀ i, ∀ y ∈ t i, (gp.app (V i)).hom.IsIntegralElem y) → ∀ W : S.Opens, IsAffineOpen W →
    ∃ s : Finset Γ(Sp K, gp ⁻¹ᵁ W), (∀ y ∈ s, y ∈ finFam gp V t W) ∧
      ∀ x ∈ finFam gp V t W, ∃ c : Γ(Sp K, gp ⁻¹ᵁ W) → Γ(S, W), x = ∑ y ∈ s, (gp.app W).hom (c y) * y := by
  first
  | exact @_root_.GlobalTheory.FinitePowerAnnihilation.finFam_finite
  | exact _root_.GlobalTheory.FinitePowerAnnihilation.finFam_finite
  | (apply _root_.GlobalTheory.FinitePowerAnnihilation.finFam_finite <;> assumption)
  | (intros; apply _root_.GlobalTheory.FinitePowerAnnihilation.finFam_finite <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FinitePowerAnnihilation.finFam_finite <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FinitePowerAnnihilation.finFam_finite ..)

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.eq_of_same_expansion_thickening_open : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e k : ℕ) (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (i' : Fin 1 → U.LG.L.ι) (W : (thickObj R I e G).left.Opens) (hW : W ≤ (fstG I e G).left ⁻¹ᵁ secChart U.LG.L i') (g : Γ((thickObj R I e G).left, W)), U.ExpandsAt e k σ f → GlobalTheory.MumMult.ChartExpOn U e k i' W g f → ((thickObj R I e G).left.presheaf.map (homOfLE hW).op).hom (((fstG I e G).left.app (secChart U.LG.L i')).hom (σ.f i')) = g := by
  first | exact @GlobalTheory.MumMult.eq_of_expandsAt_of_chartExpOn | exact GlobalTheory.MumMult.eq_of_expandsAt_of_chartExpOn | (intros; apply GlobalTheory.MumMult.eq_of_expandsAt_of_chartExpOn <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_frameCoefficient_unitGerms_finiteFree : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ₁ : R →+* R₁) (d : ℕ) (b : Fin d → R₁) (X : Scheme.{0}) (f : X ⟶ Sp R) (L : LB X), L.IsLB → ∀ (W O : X.Opens), O ≤ W → ∀ (τ : ∀ k : L.ι, Γ((pullback f (spMap ρ₁)), (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W ⊓ (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ L.U k)ˣ) (s : Fin d → ∀ k : L.ι, Γ(X, O ⊓ L.U k)), (∀ l, IsSecOver L O (s l)) → (∀ (z : (pullback f (spMap ρ₁) : Scheme.{0})) (k : L.ι), (pullback.fst f (spMap ρ₁)) z ∈ O → (pullback.fst f (spMap ρ₁)) z ∈ L.U k → gs (𝟙 (pullback f (spMap ρ₁))) z ((pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W ⊓ (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ L.U k) (τ k).val = ∑ l, gs (pullback.snd f (spMap ρ₁)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) * gs (pullback.fst f (spMap ρ₁)) z (O ⊓ L.U k) (s l k)) → ∀ z : (pullback f (spMap ρ₁) : Scheme.{0}), (pullback.fst f (spMap ρ₁)) z ∈ O → ∃ l, ∀ k, (pullback.fst f (spMap ρ₁)) z ∈ L.U k → IsUnit (gs (𝟙 X) ((pullback.fst f (spMap ρ₁)) z) (O ⊓ L.U k) (s l k)) := by
  first | exact @GlobalTheory.Mum.exists_isUnit_gs_of_frame_eq_sum | exact GlobalTheory.Mum.exists_isUnit_gs_of_frame_eq_sum | (intros; apply GlobalTheory.Mum.exists_isUnit_gs_of_frame_eq_sum <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_lineBundleFrame_of_section_units_on_closedFibre : ∀ (X Y : Scheme.{0}) (β : X ⟶ Y), IsClosedMap β.base → ∀ (L : LB X), L.IsLB → ∀ (V : Y.Opens) (s : ∀ k : L.ι, Γ(X, β ⁻¹ᵁ V ⊓ L.U k)), IsSecOver L (β ⁻¹ᵁ V) s → ∀ y : Y, y ∈ V → (∀ (z : X) (k : L.ι), β z = y → z ∈ L.U k → IsUnit (gs (𝟙 X) z (β ⁻¹ᵁ V ⊓ L.U k) (s k))) → ∃ V' : Y.Opens, y ∈ V' ∧ V' ≤ V ∧ ∃ T : ∀ k : L.ι, Γ(X, β ⁻¹ᵁ V' ⊓ L.U k)ˣ, IsFrameOver L (β ⁻¹ᵁ V') T ∧ ∀ (f : X ⟶ X) (w : LB.Iso L (L.pull f)), SecCarriedOver L (β ⁻¹ᵁ V) s f w → FrameCarried L (β ⁻¹ᵁ V') T f w := by
  first | exact @GlobalTheory.Mum.exists_frame_of_isUnit_on_fibre | exact GlobalTheory.Mum.exists_frame_of_isUnit_on_fibre | (intros; apply GlobalTheory.Mum.exists_frame_of_isUnit_on_fibre <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.FieldBaseChange GlobalTheory.Mum.Two.Mix

theorem _root_.GlobalTheory.T.exists_mixed_bundle_frame_from_part_frames : ∀ (R : Type) [CommRing R] [IsDomain R] (D₁ D₂ : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (b : D₁.P.A ⟶ D₂.P.A) (α : D₁.X) (j j' : ℕ) (g : GtPtF D₁ F) (b' : TF (R := R) F ⟶ D₂.P.A), b' = g.b ≫ b → ∀ (w : Frm D₂ F j b') (w' : Frm D₁ F j' g.b), w.IsGen → w'.IsGen → ∃ τ : LB.Gen (LB.LinComb (JN D₁ D₂) (fun i => g.b.left ≫ mixφ D₁ D₂ b α i) (MixedConv.mixε j j')), τ.IsGen ∧ ∀ z J, Good (JN D₁ D₂) z J → val τ (𝟙 _) z J = rigV D₂ (TF (R := R) F).hom z (rr J) ^ j * rigV D₁ (TF (R := R) F).hom z (rl J) ^ j' * (val (g.s α) (𝟙 _) z (rl J) * (val w (𝟙 _) z (rr J) * val w' (𝟙 _) z (rl J)))⁻¹ := by
  first | exact @GlobalTheory.Mum.Two.Mix.exists_frame_hom | exact GlobalTheory.Mum.Two.Mix.exists_frame_hom | (intros; apply GlobalTheory.Mum.Two.Mix.exists_frame_hom <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.FieldBaseChange GlobalTheory.Mum.Two.Mix

theorem _root_.GlobalTheory.T.exists_mixed_section_join_bundles : ∀ (R : Type) [CommRing R] [IsDomain R] (D₁ D₂ : DegPre R) (b : D₁.P.A ⟶ D₂.P.A) (j j' : ℕ) (χ : D₂.X) (χ' β α : D₁.X), χ' + β = α → ∀ (u : LB.Gen (CmpLB D₁ D₂ b χ' χ)), u.IsGen → ∀ (f : D₂.SecB j χ) (f' : D₁.SecB j' β), ∃ n : LB.Sec (LB.LinComb (JN D₁ D₂) (mixφ D₁ D₂ b α) (MixedConv.mixε j j')), ∀ (Z : Scheme.{0}) (r : Z ⟶ D₁.P.A.left) (z : Z) (J), Good (JN D₁ D₂) z J → sval n r z J = sval f (r ≫ b.left) z (rr J) * sval f' r z (rl J) * (val u r z J * val (MixedConv.cubB D₁ χ' β) r z (rl J)).val := by
  first | exact @GlobalTheory.Mum.Two.Mix.exists_mix_hom | exact GlobalTheory.Mum.Two.Mix.exists_mix_hom | (intros; apply GlobalTheory.Mum.Two.Mix.exists_mix_hom <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.FieldBaseChange GlobalTheory.Mum.Two.Mix

noncomputable section
namespace GlobalTheory.Mum.Two.Mix



theorem level : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (h : D₂.toPre.X →+ D₁.toPre.X), Over₀ U₁ U₂ a b → ∀ (u : ∀ χ, LB.Gen (CmpLB D₁.toPre D₂.toPre b (h χ) χ)), (∀ χ (e : ℕ) (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G₁).left) (z : Z) (J), Good (JN D₁.toPre D₂.toPre) z J → val ((U₂.gt e).t χ) (x ≫ ((Over.pullback (thick R I e)).map a).left) z (rr J) = val ((U₁.gt e).t (h χ)) x z (rl J) * val (u χ) (x ≫ (U₁.gt e).pG.left) z J) → ∀ (j j' e : ℕ) (N : Type) [Fintype N] (ρ : N → R) (σ : N → H0 U₂.LG.L j) (σ' : N → H0 U₁.LG.L j') (f : N → ∀ α : D₂.toPre.X, D₂.toPre.SecB j α) (f' : N → ∀ α : D₁.toPre.X, D₁.toPre.SecB j' α), (∀ ν, U₂.ExpandsAt e j (σ ν) (f ν)) → (∀ ν, U₁.ExpandsAt e j' (σ' ν) (f' ν)) → (∀ (Z : Scheme.{0}) (r : Z ⟶ G₁.left) (z : Z) (J₁ J₂), Good U₁.LG.L z J₁ → Good U₂.LG.L z J₂ → ∑ ν, constVal (r ≫ G₁.hom) z (ρ ν) * (sval (σ ν) (r ≫ a.left) z J₂ * sval (σ' ν) r z J₁) = 0) → ∀ (m : ∀ α, {p : D₂.toPre.X × D₁.toPre.X // h p.1 + p.2 = α} → LB.Sec (LB.LinComb (JN D₁.toPre D₂.toPre) (mixφ D₁.toPre D₂.toPre b α) (MixedConv.mixε j j'))), (∀ α p (Z : Scheme.{0}) (r : Z ⟶ D₁.toPre.P.A.left) (z : Z) (J), Good (JN D₁.toPre D₂.toPre) z J → sval (m α p) r z J = ∑ ν, constVal (r ≫ D₁.toPre.P.A.hom) z (ρ ν) * (sval (f ν p.1.1) (r ≫ b.left) z (rr J) * sval (f' ν p.1.2) r z (rl J) * (val (u p.1.1) r z J * val (MixedConv.cubB D₁.toPre (h p.1.1) p.1.2) r z (rl J)).val)) → ∀ (α : D₁.toPre.X), ∃ S : Finset {p : D₂.toPre.X × D₁.toPre.X // h p.1 + p.2 = α}, ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e D₁.toPre.P.A).left) (z : Z) (J), Good (JN D₁.toPre D₂.toPre) z J → (∀ i ∉ S, sval (m α i) (r ≫ (D₁.toPre.prBe I e).left) z J = 0) ∧ ∑ i ∈ S, sval (m α i) (r ≫ (D₁.toPre.prBe I e).left) z J = 0 := by
  intro R _ _ I D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ U₁ U₂ a b h hO u hu j j' e N _ ρ σ σ' f f' hE hE' hrel m hm α
  classical
  obtain ⟨S, hS⟩ := MixedConv.expand_common U₂ e j σ f hE
  obtain ⟨S', hS'⟩ := MixedConv.expand_common U₁ e j' σ' f' hE'
  have pl := isPart_inl D₁.toPre.P.L D₂.toPre.P.L
  have pr := isPart_inr D₁.toPre.P.L D₂.toPre.P.L
  let ae := ((Over.pullback (thick R I e)).map a).left
  have hpe : ae ≫ pGl U₂ e = pGl U₁ e ≫ b.left := by
    have h₁ := congrArg (fun q => q.left) (hO e)
    have h₂ : ((Over.pullback (thick R I e)).map b).left ≫ pullback.fst _ _ = pullback.fst _ _ ≫ b.left :=
      pullback.lift_fst _ _ _
    show _ ≫ (U₂.gt e).q.left ≫ pullback.fst _ _ = ((U₁.gt e).q.left ≫ pullback.fst _ _) ≫ _
    rw [← Category.assoc]
    exact (congrArg (· ≫ pullback.fst _ _) h₁).trans ((Category.assoc _ _ _).trans
      ((congrArg ((U₁.gt e).q.left ≫ ·) h₂).trans (Category.assoc _ _ _).symm))
  have hfe : ae ≫ fGl I G₂ e = fGl I G₁ e ≫ a.left := pullback.lift_fst _ _ _
  have hp : ∀ {Z : Scheme.{0}} (x : Z ⟶ (thickObj R I e G₁).left),
      (x ≫ ae) ≫ pGl U₂ e = (x ≫ pGl U₁ e) ≫ b.left :=
    fun x => by rw [Category.assoc, Category.assoc, hpe]
  have hf : ∀ {Z : Scheme.{0}} (x : Z ⟶ (thickObj R I e G₁).left),
      (x ≫ ae) ≫ fGl I G₂ e = (x ≫ fGl I G₁ e) ≫ a.left :=
    fun x => by rw [Category.assoc, Category.assoc, hfe]
  let d : ∀ α, SecOver D₁.toPre.P.A.hom
      (LB.LinComb (JN D₁.toPre D₂.toPre) (mixφ D₁.toPre D₂.toPre b α) (MixedConv.mixε j j')) := fun α =>
    ∑ p ∈ (S ×ˢ S').subtype (fun p => h p.1 + p.2 = α), (m α p : SecOver D₁.toPre.P.A.hom _)
  have lift : ∀ n : LB.Sec (LB.LinComb (JN D₁.toPre D₂.toPre) (mixφ D₁.toPre D₂.toPre b α) (MixedConv.mixε j j')),
      (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G₁).left) (z : Z) (J), Good (JN D₁.toPre D₂.toPre) z J →
        sval n (x ≫ pGl U₁ e) z J = 0) → ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e D₁.toPre.P.A).left) (z : Z) (J),
        Good (JN D₁.toPre D₂.toPre) z J → sval n (r ≫ (D₁.toPre.prBe I e).left) z J = 0 := fun n hn Z r z J hJ =>
    GlobalTheory.LiftTest.main R I D₁.toPre e G₁ (U₁.gt e) D₁.toPre.P.A (𝟙 _) _ (JN D₁.toPre D₂.toPre)
      (jn_isLB D₁.toPre D₂.toPre) _ _ _ n
      (fun Z x r hr z J hJ => by
        obtain rfl : r = x ≫ pGl U₁ e := (Category.comp_id r).symm.trans hr
        exact hn Z x z J hJ) Z _
      ⟨r ≫ pullback.snd _ _, by
        rw [Category.assoc, Category.assoc]; exact congrArg (r ≫ ·) pullback.condition.symm⟩ z J hJ
  refine ⟨(S ×ˢ S').subtype (fun p => h p.1 + p.2 = α), fun Z r z J hJ => ⟨fun i hi => ?_, ?_⟩⟩
  · refine lift _ (fun Z x z J hJ => ?_) Z r z J hJ
    rw [hm α i _ _ z J hJ]
    refine Finset.sum_eq_zero fun ν _ => ?_
    rw [Finset.mem_subtype, Finset.mem_product, not_and_or] at hi
    rcases hi with hi | hi
    · rw [← hp, (hS ν Z (x ≫ ae) z (rr J) (pr.good hJ)).1 _ hi, zero_mul, zero_mul, mul_zero]
    · rw [(hS' ν Z x z (rl J) (pl.good hJ)).1 _ hi, mul_zero, zero_mul, mul_zero]
  · refine (sval_sum' (π := D₁.toPre.P.A.hom) hJ _ _ _).symm.trans (lift (d α) (fun Z x z J hJ => ?_) Z r z J hJ)
    refine GlobalTheory.T.sectionValue_eq_zero_weightIndependence_level R I D₁.toPre e G₁ (U₁.gt e) D₁.toPre.P.A (𝟙 _) _ (JN D₁.toPre D₂.toPre)
      (jn_isLB D₁.toPre D₂.toPre) coprod.inl Prod.fst pl _
      (mixφ D₁.toPre D₂.toPre b) (MixedConv.mixε j j') d (insert α ((S ×ˢ S').image fun p => h p.1 + p.2)) ?_ α
      (Finset.mem_insert_self _ _) Z x _ (Category.comp_id _) z J hJ
    intro Z x r hr z J hJ
    obtain rfl : r = x ≫ pGl U₁ e := (Category.comp_id r).symm.trans hr
    have hJl : Good D₁.toPre.P.L z (rl J) := pl.good hJ
    have hJr : Good D₂.toPre.P.L z (rr J) := pr.good hJ
    obtain ⟨J₁, hJ₁⟩ := CoefBasic.exists_good' U₁.LG.isLB z
    obtain ⟨J₂, hJ₂⟩ := CoefBasic.exists_good' U₂.LG.isLB z
    let T : D₂.toPre.X × D₁.toPre.X → Z.presheaf.stalk z := fun p =>
      ∑ ν, constVal ((x ≫ pGl U₁ e) ≫ D₁.toPre.P.A.hom) z (ρ ν) *
      ((sval (f ν p.1) ((x ≫ ae) ≫ pGl U₂ e) z (rr J) * (val (tG U₂ e p.1) (x ≫ ae) z (rr J)).val) *
        (sval (f' ν p.2) (x ≫ pGl U₁ e) z (rl J) * (val (tG U₁ e p.2) x z (rl J)).val))
    have k₁ : ∀ β, sval (d β) (x ≫ pGl U₁ e) z J * (val ((U₁.gt e).t β) x z (rs coprod.inl Prod.fst J)).val =
        ∑ p ∈ (S ×ˢ S').filter (fun p => h p.1 + p.2 = β), T p := fun β => by
      refine (congrArg (· * _) (sval_sum' (π := D₁.toPre.P.A.hom) hJ _ _ _)).trans ?_
      rw [← Finset.sum_subtype_eq_sum_filter, Finset.sum_mul]
      refine Finset.sum_congr rfl fun p _ => ?_
      obtain ⟨⟨χ, δ⟩, rfl⟩ := p
      rw [hm _ _ _ _ z J hJ, Finset.sum_mul]
      refine Finset.sum_congr rfl fun ν _ => ?_
      have a₁ := congrArg Units.val (MixedConv.t_mul_val U₁ e (h χ) δ x z hJl)
      have a₂ := congrArg Units.val (hu χ e Z x z J hJ)
      simp only [Units.val_mul] at a₁ a₂ ⊢
      rw [hp]
      linear_combination (constVal ((x ≫ pGl U₁ e) ≫ D₁.toPre.P.A.hom) z (ρ ν) *
        sval (f ν χ) ((x ≫ pGl U₁ e) ≫ b.left) z (rr J) * sval (f' ν δ) (x ≫ pGl U₁ e) z (rl J) *
        (val (u χ) (x ≫ pGl U₁ e) z J).val) * a₁ -
        (constVal ((x ≫ pGl U₁ e) ≫ D₁.toPre.P.A.hom) z (ρ ν) *
        sval (f ν χ) ((x ≫ pGl U₁ e) ≫ b.left) z (rr J) * sval (f' ν δ) (x ≫ pGl U₁ e) z (rl J) *
        (val (tG U₁ e δ) x z (rl J)).val) * a₂
    refine (Finset.sum_congr rfl fun β _ => k₁ β).trans ((Finset.sum_fiberwise_of_maps_to (fun p hp =>
      Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hp)) T).trans ?_)
    have hc : (x ≫ pGl U₁ e) ≫ D₁.toPre.P.A.hom = (x ≫ fGl I G₁ e) ≫ G₁.hom := by
      rw [Category.assoc, Category.assoc]
      exact congrArg (x ≫ ·) ((Over.w (U₁.gt e).pG).trans (Over.w (fstG I e G₁)).symm)
    have k₂ := hrel Z (x ≫ fGl I G₁ e) z J₁ J₂ hJ₁ hJ₂
    rw [Finset.sum_comm]
    refine Eq.trans (Finset.sum_congr rfl fun ν _ => ?_) ((Finset.mul_sum _ _ _).symm.trans
      ((congrArg (((wv U₂ e (x ≫ ae) z (rr J ((x ≫ ae) ≫ pGl U₂ e)) (J₂ (((x ≫ ae) ≫ fGl I G₂ e) ≫ 𝟙 _)) ^ j).val *
        (wv U₁ e x z (rl J (x ≫ pGl U₁ e)) (J₁ ((x ≫ fGl I G₁ e) ≫ 𝟙 _)) ^ j').val) * ·) k₂).trans (mul_zero _)))
    rw [← Finset.mul_sum, Finset.sum_product]
    dsimp only
    rw [← Finset.sum_mul_sum, ← (hS ν Z (x ≫ ae) z (rr J) hJr).2 J₂ hJ₂,
      ← (hS' ν Z x z (rl J) hJl).2 J₁ hJ₁, hc, ← hf]
    ring

end GlobalTheory.Mum.Two.Mix
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_preimage_of_local_preimages_injective : ∀ {X Y : Scheme.{0}} (a : Y ⟶ X), (∀ U : X.Opens, Function.Injective (a.app U).hom) → ∀ (V : X.Opens) {B : Type} (W : B → X.Opens), V ≤ ⨆ b, W b → ∀ (x : Γ(Y, a ⁻¹ᵁ V)), (∀ b, ∃ y : Γ(X, V ⊓ W b), (a.app (V ⊓ W b)).hom y = (Y.presheaf.map (homOfLE (extLI_preimage_mono a (inf_le_left : V ⊓ W b ≤ V))).op).hom x) → ∃ y : Γ(X, V), (a.app V).hom y = x := by
  first | exact @GlobalTheory.Mum.imgLoc_exists | exact GlobalTheory.Mum.imgLoc_exists | (intros; apply GlobalTheory.Mum.imgLoc_exists <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LowDat

theorem mono_jK_of_domain (R : Type) [CommRing R] [IsDomain R] : Mono (jK R) := by
  have : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  infer_instance

theorem spMap_comp_jFK {R : Type} [CommRing R] [IsDomain R] {F F' : Type} [Field F] [Algebra (FractionRing R) F]
    [Field F'] [Algebra (FractionRing R) F'] (σ : F →ₐ[FractionRing R] F') :
    spMap σ.toRingHom ≫ jFK (R := R) F = jFK (R := R) F' := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

theorem left_eq_of_section (C : UChart.Fam Xo c R) (tK : SAB H (Sp (FractionRing R))) (m1 : SABMap tK C.t (jK R))
    (m2 : SABMap tK Xo.univ.t (C.y ≫ pullback.fst _ _)) {F F' : Type} [Field F] [Algebra (FractionRing R) F]
    [Field F'] [Algebra (FractionRing R) F'] (σ : F →ₐ[FractionRing R] F') (s : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G)
    (x : TFK (R := R) F ⟶ C.P.A.A) (x' : TFK (R := R) F' ⟶ C.P.A.A)
    (g : Sp F ⟶ tK.G.left) (h1 : g ≫ m1.φ = x.left ≫ C.P.U.gen.inv.left ≫ pullback.fst C.t.G.hom (jK R))
    (h2 : g ≫ m2.φ = jFK (R := R) F ≫ C.y ≫ pullback.fst _ _ ≫ s.left)
    (g' : Sp F' ⟶ tK.G.left) (h1' : g' ≫ m1.φ = x'.left ≫ C.P.U.gen.inv.left ≫ pullback.fst C.t.G.hom (jK R))
    (h2' : g' ≫ m2.φ = jFK (R := R) F' ≫ C.y ≫ pullback.fst _ _ ≫ s.left) :
    x'.left = spMap σ.toRingHom ≫ x.left := by
  have := mono_jK_of_domain R
  have w0 : C.P.U.gen.inv.left ≫ pullback.snd C.t.G.hom (jK R) = C.P.A.A.hom := Over.w C.P.U.gen.inv
  have w : x.left ≫ C.P.A.A.hom = jFK (R := R) F := Over.w x
  have w' : x'.left ≫ C.P.A.A.hom = jFK (R := R) F' := Over.w x'
  have c1 : m1.φ ≫ C.t.G.hom = tK.G.hom ≫ jK R := m1.cart.1.w
  have key : ∀ {T : Scheme.{0}} (p : T ⟶ tK.G.left) (z : T ⟶ C.P.A.A.left),
      p ≫ m1.φ = z ≫ C.P.U.gen.inv.left ≫ pullback.fst C.t.G.hom (jK R) → p ≫ tK.G.hom = z ≫ C.P.A.A.hom := by
    intro T p z h
    rw [← cancel_mono (jK R), Category.assoc, ← c1, ← Category.assoc, h, ← w0]
    simp only [Category.assoc, pullback.condition]
  have e1 : g ≫ tK.G.hom = jFK (R := R) F := (key g _ h1).trans w
  have e1' : g' ≫ tK.G.hom = jFK (R := R) F' := (key g' _ h1').trans w'
  have e : g' = spMap σ.toRingHom ≫ g := by
    refine m2.cart.1.hom_ext ?_ ?_
    · have q := congrArg (· ≫ C.y ≫ pullback.fst _ _ ≫ s.left) (spMap_comp_jFK σ)
      exact h2'.trans (q.symm.trans ((Category.assoc _ _ _).trans
        ((congrArg (spMap σ.toRingHom ≫ ·) h2.symm).trans (Category.assoc _ _ _).symm)))
    · rw [Category.assoc, e1, e1', spMap_comp_jFK]
  have e2 : x'.left ≫ C.P.U.gen.inv.left = spMap σ.toRingHom ≫ x.left ≫ C.P.U.gen.inv.left := by
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc]
      rw [← h1, ← h1', e, Category.assoc]
    · simp only [Category.assoc]
      rw [w0, w, w', spMap_comp_jFK]
  have hi : C.P.U.gen.inv.left ≫ C.P.U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have e3 := congrArg (· ≫ C.P.U.gen.hom.left) e2
  simpa only [Category.assoc, hi, Category.comp_id] using e3

theorem exists_tateIso_ext (D : Datum H) {S : Scheme.{0}} (P : Out.PolAV S) (act : 𝓞 E → (P.A ⟶ P.A))
    {K Ω : Type} [Field K] [Field Ω] [IsAlgClosed K] [IsAlgClosed Ω] [CharZero K] (i : K →+* Ω)
    (x : Sp K ⟶ S) (x' : Sp Ω ⟶ S) (h : spMap i ≫ x = x')
    (I : TateIso D K (Over.mk x ⟶ P.A) (fun c y => y ≫ act c) (fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c))) :
    ∃ I' : TateIso D Ω (Over.mk x' ⟶ P.A) (fun c y => y ≫ act c) (fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c)),
      ∀ n, 0 < n → (I'.ζ n : Ω) = i (I.ζ n) ∧ ∀ v, (I'.ev n v).left = spMap i ≫ (I.ev n v).left := by
  subst h
  obtain ⟨I', hI⟩ := (TateIsoFieldExt.tateIso_fieldExt abelianSchemeLaws_all.1 E H D S P act K Ω i x).1 I
  exact ⟨I', fun n hn => ⟨(hI n hn).1, fun v => by rw [(hI n hn).2 v]; rfl⟩⟩

end GlobalTheory.LowDat

theorem GlobalTheory.LowDat.level_points_compat : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l)
  (c : Coeff l) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : GlobalTheory.UChart.Fam Xo c R)
  (tK : SAB H (Sp (FractionRing R))) (m1 : SABMap tK C.t (jK R)) (m2 : SABMap tK Xo.univ.t (C.y ≫ pullback.fst _ _))
  (F F' : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Field F'] [IsAlgClosed F'] [Algebra (FractionRing R) F']
  (σ : F →ₐ[FractionRing R] F')
  (I : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F)) (I' : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F')),
  GlobalTheory.LowDat.XFLevel C tK m1 m2 F I → GlobalTheory.LowDat.XFLevel C tK m1 m2 F' I' →
  ∀ (a : Dw.La) (x : TFK (R := R) F ⟶ C.P.A.A) (x' : TFK (R := R) F' ⟶ C.P.A.A),
    C.P.ToA F l.M' (I.ev l.M' a) x → C.P.ToA F' l.M' (I'.ev l.M' a) x' → x'.left = spMap σ.toRingHom ≫ x.left := by
  intro E _ _ _ H Dw l Xo c R _ _ _ hR C tK m1 m2 F F' _ _ _ _ _ _ σ I I' hI hI' a x x' hx hx'
  haveI : CharZero R := hR.2
  haveI : CharZero (FractionRing R) := charZero_of_injective_algebraMap (IsFractionRing.injective R _)
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap (FractionRing R) F).injective
  obtain ⟨J, hJζ, hJ⟩ := GlobalTheory.T.exists_tateIso_generic_abelian_of_uniformisation Dw R hR C.t C.P F I
  obtain ⟨J', hJζ', hJ'⟩ := GlobalTheory.T.exists_tateIso_generic_abelian_of_uniformisation Dw R hR C.t C.P F' I'
  obtain ⟨J₂, h₂⟩ := GlobalTheory.LowDat.exists_tateIso_ext Dw C.P.A _ σ.toRingHom _ _ (GlobalTheory.LowDat.spMap_comp_jFK σ) J
  have hM : 0 < l.M := by have := l.three_le; omega
  have hM' : 0 < l.M' := Nat.lcm_pos hM l.A_pos
  have hT := GlobalTheory.T.linearUniformisation_torsionIsomorphism E H R _ hR.1 C.t C.P
  have u : J₂.ev l.M' a = J'.ev l.M' a := by
    refine GlobalTheory.T.tateIso_ev_eq_at_lcm_level Dw l F' _ _ _
      (fun n _ p q d d' => GlobalTheory.weilIs_unique_fieldPoint _ _ _ C.P.A.isLB F' _ n p q d d') J₂ J' ?_ ?_ ?_ a
    · apply Units.ext
      rw [(h₂ _ hM').1, hJζ, hJζ', hI.1, hI'.1]
      simp [GlobalTheory.LowDat.toF]
    · intro b
      obtain ⟨g, g1, g2⟩ := hI.2 _ b _ (Or.inl ⟨rfl, rfl⟩) _ (hJ _ l.A_pos b)
      obtain ⟨g', g1', g2'⟩ := hI'.2 _ b _ (Or.inl ⟨rfl, rfl⟩) _ (hJ' _ l.A_pos b)
      exact Over.OverMorphism.ext (((h₂ _ l.A_pos).2 b).trans
        (GlobalTheory.LowDat.left_eq_of_section C tK m1 m2 σ _ _ _ g g1 g2 g' g1' g2').symm)
    · intro b hb
      obtain ⟨g, g1, g2⟩ := hI.2 _ b _ (Or.inr ⟨rfl, hb, rfl⟩) _ (hJ _ hM b)
      obtain ⟨g', g1', g2'⟩ := hI'.2 _ b _ (Or.inr ⟨rfl, hb, rfl⟩) _ (hJ' _ hM b)
      exact Over.OverMorphism.ext (((h₂ _ hM).2 b).trans
        (GlobalTheory.LowDat.left_eq_of_section C tK m1 m2 σ _ _ _ g g1 g2 g' g1' g2').symm)
  obtain ⟨f, hf, -⟩ := hT F l.M' hM'
  obtain ⟨f', hf', -⟩ := hT F' l.M' hM'
  have e : x = J.ev l.M' a := ((hf _ _).1 hx).trans ((hf _ _).1 (hJ _ hM' a)).symm
  have e' : x' = J'.ev l.M' a := ((hf' _ _).1 hx').trans ((hf' _ _).1 (hJ' _ hM' a)).symm
  rw [e, e', ← u]
  exact (h₂ _ hM').2 a
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

theorem degPre_c_zero {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) : D.c 0 = 1 := by
  have h := D.c_add 0 0
  rw [add_zero, padd, ← Hom.mul_def] at h
  exact mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)

theorem tens_inc_pr_facts (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ}
    (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W) (i₀ : Fin r) :
    IsMonHom (T.inc i₀) ∧ T.inc i₀ ≫ T.pr i₀ = 𝟙 _ ∧ T.pr i₀ ≫ T.inc i₀ = T.act (Matrix.single i₀ i₀ 1) ∧
      ∀ y, D'.c (T.xi i₀ y) = D.c y ≫ T.inc i₀ := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · apply Fan.IsLimit.hom_ext T.lim
    intro i
    have hp : ∀ k, (Fan.mk D'.P.A T.pr).proj k = T.pr k := fun _ => rfl
    simp only [hp, Category.assoc, T.inc_pr']
    rw [(T.pr_hom i).one_hom]
    split_ifs
    · simp
    · rw [comp_one, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  · apply Fan.IsLimit.hom_ext T.lim
    intro i
    have hp : ∀ k, (Fan.mk D'.P.A T.pr).proj k = T.pr k := fun _ => rfl
    simp only [hp, Category.assoc, T.inc_pr']
    rw [(T.pr_hom i).mul_hom, ← Category.assoc, tensorHom_comp_tensorHom, T.inc_pr']
    split_ifs
    · simp
    · rw [comp_one]
      have : ((1 : D.P.A ⟶ D.P.A) ⊗ₘ (1 : D.P.A ⟶ D.P.A)) = lift (fst _ _ ≫ 1) (snd _ _ ≫ 1) := by
        ext <;> simp
      rw [this, ← Hom.mul_def, comp_one, comp_one, _root_.mul_one]
  · simpa using T.inc_pr' i₀ i₀
  · apply Fan.IsLimit.hom_ext T.lim
    intro i
    have hp : ∀ k, (Fan.mk D'.P.A T.pr).proj k = T.pr k := fun _ => rfl
    simp only [hp, Category.assoc, T.inc_pr', Tens.act_pr]
    by_cases h : i = i₀
    · subst h
      rw [if_pos rfl, Category.comp_id, Finset.prod_eq_single i]
      · simp [Matrix.single_apply]
      · intro j _ hj
        simp [Matrix.single_apply, Ne.symm hj]
      · simp
    · rw [if_neg h, comp_one]
      symm
      apply Finset.prod_eq_one
      intro j _
      simp [Matrix.single_apply, Ne.symm h]
  · intro y
    apply Fan.IsLimit.hom_ext T.lim
    intro i
    have hp : ∀ k, (Fan.mk D'.P.A T.pr).proj k = T.pr k := fun _ => rfl
    simp only [hp, Category.assoc, T.inc_pr', T.c_pr]
    by_cases h : i = i₀
    · subst h
      simp [Tens.xi]
    · rw [if_neg h, comp_one]
      simp [Tens.xi, Pi.single_apply, h, degPre_c_zero]

end GlobalTheory.Mum
end
