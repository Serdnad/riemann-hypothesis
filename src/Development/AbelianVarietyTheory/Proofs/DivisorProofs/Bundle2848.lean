module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle777
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2007
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ThetaGrpActIterateEqOfPowEqOne
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle023
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle787
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.FlatIsoUnitGenerator
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle788
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle004
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle032
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.LevelFrameOfLaws
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

theorem _root_.GlobalTheory.T.torusCoordinates_compare_normalisedGenerators : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (h : D₂.toPre.X →+ D₁.toPre.X), Lin U₁ U₂ a b h → Coord U₁ U₂ a b h := by
  first | exact @GlobalTheory.Mum.Two.coord_of_lin | exact GlobalTheory.Mum.Two.coord_of_lin | (intros; apply GlobalTheory.Mum.Two.coord_of_lin <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.CrossTheta₂

theorem sval_comp {X Y Y' Z : Scheme.{0}} {L : LB X} (p : Y' ⟶ X) {k : ℤ}
    (s : LB.Sec (LB.LinComb L (fun _ : Fin 1 => p) (fun _ => k))) (r : Z ⟶ Y) (c : Y ⟶ Y') (z : Z)
    {J : (Z ⟶ X) → L.ι} {I : (Y ⟶ X) → L.ι} (hI : Good L (r z) I) (hc : I (c ≫ p) = J (r ≫ c ≫ p)) :
    sval s (r ≫ c) z J = (r.stalkMap z).hom (sval s c (r z) I) := by
  rw [sval_of s (r ≫ c) z J (fun _ => I (c ≫ p)) (fun _ => by rw [Category.assoc, hc])]
  exact GlobalTheory.CrossTheta.gs_comp_stalk r c z _ (hI.mem (fun _ : Fin 1 => p) c) _

theorem cross_val {X₁ X₂ Y₁ Y₂ : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂} (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB)
    (p₁ : Y₁ ⟶ X₁) (p₂ : Y₂ ⟶ X₂) (b : Y₁ ⟶ Y₂) {k k' : ℤ}
    (s₁ s₂ : LB.Sec (LB.LinComb L₂ (fun _ : Fin 1 => p₂) (fun _ => k)))
    (s₁' s₂' : LB.Sec (LB.LinComb L₁ (fun _ : Fin 1 => p₁) (fun _ => k')))
    (H : ∀ y J₁ J₂, Good L₁ y J₁ → Good L₂ y J₂ →
      sval s₁ b y J₂ * sval s₂' (𝟙 _) y J₁ = sval s₂ b y J₂ * sval s₁' (𝟙 _) y J₁)
    {Z : Scheme.{0}} (r : Z ⟶ Y₁) (z : Z) {J₁ J₂} (hJ₁ : Good L₁ z J₁) (hJ₂ : Good L₂ z J₂) :
    sval s₁ (r ≫ b) z J₂ * sval s₂' r z J₁ = sval s₂ (r ≫ b) z J₂ * sval s₁' r z J₁ := by
  obtain ⟨I₁, hI₁, e₁⟩ := exists_good L₁ hL₁ (r z) (K := Unit) (fun _ => 𝟙 _ ≫ p₁)
    (fun _ => J₁ (r ≫ 𝟙 _ ≫ p₁)) (fun _ _ _ => rfl) (fun _ => hJ₁ (r ≫ 𝟙 _ ≫ p₁))
  obtain ⟨I₂, hI₂, e₂⟩ := exists_good L₂ hL₂ (r z) (K := Unit) (fun _ => b ≫ p₂)
    (fun _ => J₂ (r ≫ b ≫ p₂)) (fun _ _ _ => rfl) (fun _ => hJ₂ (r ≫ b ≫ p₂))
  have h := congrArg (r.stalkMap z).hom (H (r z) I₁ I₂ hI₁ hI₂)
  rw [map_mul, map_mul, ← sval_comp p₂ s₁ r b z hI₂ (e₂ ()), ← sval_comp p₂ s₂ r b z hI₂ (e₂ ()),
    ← sval_comp p₁ s₁' r (𝟙 _) z hI₁ (e₁ ()), ← sval_comp p₁ s₂' r (𝟙 _) z hI₁ (e₁ ()), Category.comp_id] at h
  exact h

theorem translT_whisker {S : Scheme.{0}} {A₁ A₂ : Over S} [GrpObj A₁] [GrpObj A₂] {T : Over S} (c : A₁ ⟶ A₂)
    [IsMonHom c] (x : T ⟶ A₁) :
    translT A₁ x ≫ T ◁ c = T ◁ c ≫ translT A₂ (x ≫ c) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [translT]
  · simp only [translT, Category.assoc, whiskerLeft_snd, lift_snd, lift_snd_assoc, ThetaPowOrder.translPt_eq,
      MonObj.comp_mul, MonObj.mul_comp, whiskerLeft_fst_assoc]

theorem cross_act {S : Scheme.{0}} {A₁ A₂ : Over S} [GrpObj A₁] [GrpObj A₂] {L₁ : LB A₁.left} {L₂ : LB A₂.left}
    (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB) {T : Over S} (c : A₁ ⟶ A₂) [IsMonHom c] {k k' : ℤ}
    (θ : ThetaGrp A₂ L₂ k T) (θ' : ThetaGrp A₁ L₁ k' T) (hp : θ.pt = θ'.pt ≫ c)
    {t₁ t₂ T₁ T₂ : LB.Sec (LPow A₂ L₂ k T)} {t₁' t₂' T₁' T₂' : LB.Sec (LPow A₁ L₁ k' T)}
    (h₁ : IsActOf A₂ L₂ k θ t₁ T₁) (h₂ : IsActOf A₂ L₂ k θ t₂ T₂) (h₁' : IsActOf A₁ L₁ k' θ' t₁' T₁')
    (h₂' : IsActOf A₁ L₁ k' θ' t₂' T₂') :
    (∀ y J₁ J₂, Good L₁ y J₁ → Good L₂ y J₂ →
      sval (L := L₂) t₁ (T ◁ c).left y J₂ * sval (L := L₁) t₂' (𝟙 _) y J₁ =
        sval (L := L₂) t₂ (T ◁ c).left y J₂ * sval (L := L₁) t₁' (𝟙 _) y J₁) ↔
    (∀ y J₁ J₂, Good L₁ y J₁ → Good L₂ y J₂ →
      sval (L := L₂) T₁ (T ◁ c).left y J₂ * sval (L := L₁) T₂' (𝟙 _) y J₁ =
        sval (L := L₂) T₂ (T ◁ c).left y J₂ * sval (L := L₁) T₁' (𝟙 _) y J₁) := by
  have cc : (T ◁ c).left ≫ (translT A₂ θ.pt).left = (translT A₁ θ'.pt).left ≫ (T ◁ c).left := by
    rw [← Over.comp_left, ← Over.comp_left, hp, translT_whisker]
  have key : ∀ {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A₁).left) (z : Z) {J₁ J₂}, Good L₁ z J₁ → Good L₂ z J₂ →
      (sval (L := L₂) T₁ (r ≫ (T ◁ c).left) z J₂ * sval (L := L₁) T₂' r z J₁ =
        sval (L := L₂) T₂ (r ≫ (T ◁ c).left) z J₂ * sval (L := L₁) T₁' r z J₁ ↔
      sval (L := L₂) t₁ ((r ≫ (translT A₁ θ'.pt).left) ≫ (T ◁ c).left) z J₂ *
          sval (L := L₁) t₂' (r ≫ (translT A₁ θ'.pt).left) z J₁ =
        sval (L := L₂) t₂ ((r ≫ (translT A₁ θ'.pt).left) ≫ (T ◁ c).left) z J₂ *
          sval (L := L₁) t₁' (r ≫ (translT A₁ θ'.pt).left) z J₁) := by
    intro Z r z J₁ J₂ hJ₁ hJ₂
    rw [ThetaPowOrder.act_sval h₁ _ z hJ₂, ThetaPowOrder.act_sval h₂ _ z hJ₂, ThetaPowOrder.act_sval h₁' _ z hJ₁,
      ThetaPowOrder.act_sval h₂' _ z hJ₁, Category.assoc, cc, ← Category.assoc, _root_.mul_mul_mul_comm,
      _root_.mul_mul_mul_comm _ (sval (L := L₂) t₂ _ z J₂), ← Units.val_mul, Units.mul_right_inj]
  constructor
  · intro H y J₁ J₂ hJ₁ hJ₂
    have h := (key (𝟙 _) y hJ₁ hJ₂).2 (cross_val hL₁ hL₂ _ _ _ t₁ t₂ t₁' t₂' H _ y hJ₁ hJ₂)
    rwa [Category.id_comp] at h
  · intro H y J₁ J₂ hJ₁ hJ₂
    have h := (key (translT A₁ θ'.pt⁻¹).left y hJ₁ hJ₂).1 (cross_val hL₁ hL₂ _ _ _ T₁ T₂ T₁' T₂' H _ y hJ₁ hJ₂)
    rwa [← Over.comp_left, ThetaPowOrder.translT_comp, mul_inv_cancel, ThetaPowOrder.translT_one, Over.id_left,
      Category.id_comp] at h

end GlobalTheory.CrossTheta₂

namespace GlobalTheory

theorem crossH_iff_of_isActOf : ∀ (R : Type) [CommRing R] [IsDomain R] (A₁ A₂ : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [Algebra (FractionRing R) F] (c : A₁.A ⟶ A₂.A), IsMonHom c → ∀ (j j' : ℕ) (θ : ThetaGrp A₂.A A₂.L (j : ℤ) (TFK (R := R) F)) (θ' : ThetaGrp A₁.A A₁.L (j' : ℤ) (TFK (R := R) F)), θ.pt = θ'.pt ≫ c → ∀ (t₁ t₂ T₁ T₂ : SecA A₂ F j) (t₁' t₂' T₁' T₂' : SecA A₁ F j'), IsActOf A₂.A A₂.L j θ t₁ T₁ → IsActOf A₂.A A₂.L j θ t₂ T₂ → IsActOf A₁.A A₁.L j' θ' t₁' T₁' → IsActOf A₁.A A₁.L j' θ' t₂' T₂' → (CrossH c t₁ t₂ t₁' t₂' ↔ CrossH c T₁ T₂ T₁' T₂') := by
  intro R _ _ A₁ A₂ F _ _ c hc j j' θ θ' hp t₁ t₂ T₁ T₂ t₁' t₂' T₁' T₂' h₁ h₂ h₁' h₂'
  haveI := hc
  exact CrossTheta₂.cross_act A₁.isLB A₂.isLB c θ θ' hp h₁ h₂ h₁' h₂'

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.Mum.Two

theorem act_val_frac : ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ D' : DegPre R) (pr : D'.P.A ⟶ D₀.P.A) (h : D₀.X →+ D'.X) (F : Type) [Field F] [Algebra (FractionRing R) F] (y : D'.X) (y₀ : D₀.X) (g : GtPtF D' F) (g' : GtPtF D₀ F), GtPtF.IsIota y g → GtPtF.IsIota y₀ g' → Act D' D₀ pr h g g' → ∀ (χ : D₀.X) (u : LB.Gen (CmpLB D' D₀ pr (h χ) χ)), Nrm u → ∀ (z : (TK R).left) (J : ((TK R).left ⟶ (D'.P.A.left ⨿ D₀.P.A.left : Scheme.{0})) → (JN D' D₀).ι), Good (JN D' D₀) z J → val (D₀.tau y₀ χ) (𝟙 _) z (rr J) = val (D'.tau y (h χ)) (𝟙 _) z (rl J) * val u (ptK (D'.c y)) z J := by
  intro R _ _ D₀ D' pr h F _ _ y y₀ g g' hg hg' ha χ u hu z J hJ
  have hsurj : Surjective (jFK (R := R) F) := GlobalTheory.Balanced.surjective_spMap _
  have hflat : Flat (jFK (R := R) F) := (inferInstance : Flat (spMap (algebraMap (FractionRing R) F)))
  have hb : g.b.left = jFK (R := R) F ≫ ptK (D'.c y) := by
    rw [hg.1]
    have e : toUnit (TF (R := R) F) = (Over.homMk (jFK (R := R) F) rfl : TF (R := R) F ⟶ TK R) ≫ toUnit (TK R) :=
      toUnit_unique _ _
    show (toUnit (TF (R := R) F) ≫ D'.c y).left = _
    rw [e, Category.assoc, Over.comp_left]
    rfl

  have step1 : ∀ (z' : (TF (R := R) F).left) (J' : _), Good (JN D' D₀) z' J' →
      val (D₀.tau y₀ χ) (jFK (R := R) F) z' (rr J') =
        val (D'.tau y (h χ)) (jFK (R := R) F) z' (rl J') * val u (jFK (R := R) F ≫ ptK (D'.c y)) z' J' := by
    intro z' J' hJ'
    have g₀ := (isPart_inr D'.P.L D₀.P.L).good hJ'
    have g₁ := (isPart_inl D'.P.L D₀.P.L).good hJ'
    have e := ha.2 χ u hu z' J' hJ'
    rw [val_corr g₀ (hg'.2 χ), val_corr g₁ (hg.2 (h χ)), val_pull g₀, val_pull g₁, hb] at e
    simp only [Category.id_comp] at e
    exact e

  have p₀ := isPart_inr D'.P.L D₀.P.L
  have p₁ := isPart_inl D'.P.L D₀.P.L
  let t₀ := p₀.gen (D₀.tau y₀ χ)
  let t₂ := LB.mulGen (JN D' D₀) _ _ _ _ (p₁.gen (D'.tau y (h χ))) (LB.pullGen (JN D' D₀) _ _ u (ptK (D'.c y)))
  have key := GlobalTheory.Balanced.val_descend (jn_isLB D' D₀) t₀ t₂ (jFK (R := R) F) (fun z' J' hJ' => by
    rw [p₀.val_gen _ _ _ hJ', val_mul hJ', p₁.val_gen _ _ _ hJ', val_pull hJ']
    exact step1 z' J' hJ') z J hJ
  rw [p₀.val_gen _ _ _ hJ, val_mul hJ, p₁.val_gen _ _ _ hJ, val_pull hJ, Category.id_comp] at key
  exact key

end GlobalTheory.Mum.Two

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

namespace GlobalTheory.Poinc.IntEval

theorem value_sub_sum_mem_hRed : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (h : 𝟙_ (Over (Sp R)) ⟶ G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.FormalEq U h g → ∀ (f : LB.Gen (LB.LinComb U.LG.L (K := Fin 1) (fun _ => h.left) (fun _ => 1))) (t : LB.Gen (LB.LinComb D.toPre.P.L ![(η[D.toPre.P.A]).left, g.b.left] (DegPre.lineε 1))) (e k : ℕ), GlobalTheory.Poinc.IntEval.TRel U h g.b f t e → ∀ (σ : H0 U.LG.L k) (fs : ∀ α : D.toPre.X, D.toPre.SecB k α), U.ExpandsAt e k σ fs → ∀ x : R, (∀ (Z : Scheme.{0}) (r : Z ⟶ Sp R) (z : Z) (J : (Z ⟶ G.left) → U.LG.L.ι), Good U.LG.L z J → sval σ (r ≫ h.left) z J = Geo.Tor.cst r z x * (val f r z J ^ k).val) → ∀ a : D.toPre.X → R, (∀ (α : D.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ Sp R) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Good D.toPre.P.L z J → sval (fs α) (r ≫ g.b.left) z J * (val (g.s α) r z J).val * (val t r z J ^ k).val = Geo.Tor.cst r z (a α) * (val (L := D.toPre.P.L) D.toPre.rig r z J ^ k).val) → ∃ S : Finset D.toPre.X, ∀ T : Finset D.toPre.X, S ⊆ T → x - ∑ α ∈ T, a α ∈ I ^ (e + 1) := by
  intro R _ _ I D A G _ _ U h g hF f t e k hT σ fs hE x hx a ha
  let s : Sp (R ⧸ I ^ (e + 1)) ⟶ (thickObj R I e (𝟙_ (Over (Sp R)))).left :=
    pullback.lift (thick R I e) (𝟙 _) (by simp)
  have hs1 : s ≫ (fstG I e (𝟙_ (Over (Sp R)))).left = thick R I e := pullback.lift_fst _ _ _
  have hs2 : s ≫ ((Over.pullback (thick R I e)).map h).left = hRed I h e := by
    apply pullback.hom_ext
    · rw [Category.assoc]
      erw [pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_fst]
    · rw [Category.assoc]
      erw [pullback.lift_snd, pullback.lift_snd, pullback.lift_snd]
  obtain ⟨hb, hχ⟩ := hF e
  have hp : hRed I h e ≫ pGl U e = thick R I e ≫ g.b.left := by
    rw [← hs2, Category.assoc, ← hb, ← Category.assoc, hs1]
  have hf : hRed I h e ≫ fGl I G e = thick R I e ≫ h.left := hRed_fst h e
  obtain ⟨S, hS⟩ := expandsAt_val U e k σ fs hE
  have hc : ∀ (z : Sp (R ⧸ I ^ (e + 1))) (c : R),
      cst (thick R I e) z c = cst (𝟙 _) z (Ideal.Quotient.mk (I ^ (e + 1)) c) := fun z c => H1.gs_spec _ z c
  refine ⟨S, fun T hT' => ?_⟩
  rw [← Ideal.Quotient.eq]
  refine H1.cst_ext fun z => ?_
  rw [← hc, ← hc, GlobalTheory.ExpansionValueZero.cst_sum]
  choose J hJ using fun ψ : Sp (R ⧸ I ^ (e + 1)) ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (ψ z)
  choose J' hJ' using fun ψ : Sp (R ⧸ I ^ (e + 1)) ⟶ G.left => exists_chart U.LG.isLB (ψ z)
  have hJ : Good D.toPre.P.L z J := hJ
  have hJ' : Good U.LG.L z J' := hJ'
  obtain ⟨h₀, h₁⟩ := hS _ (hRed I h e) z J hJ
  have h₂ := h₁ (J' (hRed I h e ≫ fGl I G e)) (hJ' (hRed I h e ≫ fGl I G e))
  have hsv : sv U k σ (hRed I h e ≫ fGl I G e) z (J' (hRed I h e ≫ fGl I G e)) =
      cst (thick R I e) z x * (val f (thick R I e) z J' ^ k).val := by
    rw [hf]
    exact (sval_of σ _ z J' (fun _ => J' (thick R I e ≫ h.left)) (fun _ => by rw [Category.comp_id])).symm.trans
      (hx _ _ z J' hJ')
  have ht : ∀ α, val (tG U e α) (hRed I h e) z J = val (g.s α) (thick R I e) z J := fun α => by
    have e₁ := (val_pull hJ (tG U e α) ((Over.pullback (thick R I e)).map h).left s).symm
    have e₂ := (val_corr hJ (hχ α) s).symm
    have e₃ := val_pull hJ (g.s α) (fstG I e (𝟙_ (Over (Sp R)))).left s
    rw [hs2] at e₁
    rw [hs1] at e₃
    exact e₁.trans (e₂.trans e₃)
  have hg : ∀ α, sval (fs α) (hRed I h e ≫ pGl U e) z J = sval (fs α) (thick R I e ≫ g.b.left) z J := fun α => by
    rw [hp]
  have hTR := hT _ (𝟙 _) z J J' hJ hJ'
  simp only [Category.id_comp] at hTR
  refine (val (L := D.toPre.P.L) D.toPre.rig (thick R I e) z J ^ k).mul_left_inj.1 ?_
  rw [Finset.sum_mul, ← Finset.sum_subset hT' (fun α _ hα => (ha α _ _ z J hJ).symm.trans
    (by rw [← hg, h₀ α hα, zero_mul, zero_mul]))]
  have L₁ : cst (thick R I e) z x * (val (L := D.toPre.P.L) D.toPre.rig (thick R I e) z J ^ k).val =
      ((wv U e (hRed I h e) z (J (hRed I h e ≫ pGl U e)) (J' (hRed I h e ≫ fGl I G e)) ^ k).val *
        sv U k σ (hRed I h e ≫ fGl I G e) z (J' (hRed I h e ≫ fGl I G e))) *
        (val t (thick R I e) z J ^ k).val := by
    rw [hsv, ← hTR]
    simp only [mul_pow, Units.val_mul]
    ring
  rw [L₁, h₂, Finset.sum_mul]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [ht, hg]
  exact ha α _ _ z J hJ

end GlobalTheory.Poinc.IntEval
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Mum.UnitValuedLeadingSection

noncomputable section

namespace GlobalTheory.Mum.UnitValuedLeadingSection

theorem left_comp_hom_unit {R : Type} [CommRing R] {B : Over (Spec (CommRingCat.of R))}
    (s : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ B) : s.left ≫ B.hom = 𝟙 _ :=
  Over.w s

theorem toUnit_TK_left (R : Type) [CommRing R] [IsDomain R] : (toUnit (TK R)).left = jK R :=
  Over.w (toUnit (TK R))

theorem tau_diag_eq_unit_mul_psi_sq (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R)
    (hT : D.TauBimult) (hE : D.PsiEven) (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι)
    (hJ : TopGood D.P z J) (y : D.X) :
    ∃ u : Rˣ, val (D.tau y y) (𝟙 _) z J = uK R z u * val (D.psi y) (𝟙 _) z J ^ 2 := by
  have hG := hJ.1
  set P : D.X → ((TK R).left.presheaf.stalk z)ˣ := fun χ => val (D.psi χ) (𝟙 _) z J with hPdef
  have hP : ∀ χ, val (D.psi χ) (𝟙 _) z J = P χ := fun _ => rfl
  set rg := val D.rigK (𝟙 _) z J with hrgdef

  have h1 : ∀ a b, val (D.tau a b) (𝟙 _) z J = P (a + b) * (P a)⁻¹ * (P b)⁻¹ * rg⁻¹ := by
    intro a b
    unfold DegPre.tau
    rw [val_mul hG, val_mul hG, val_mul hG, val_inv, val_inv, val_inv]

  obtain ⟨r, hr⟩ : ∃ u : Rˣ, rg = uK R z u := by
    rw [hrgdef]
    unfold DegPre.rigK
    rw [val_pull hG, Category.id_comp, toUnit_TK_left]
    have e : jK R = jK R ≫ (𝟙 (Spec (CommRingCat.of R)) : Spec (CommRingCat.of R) ⟶ (𝟙_ (Over (Spec (CommRingCat.of R)))).left) :=
      (Category.comp_id _).symm
    rw [e]
    exact val_section_unit D.P z J hJ D.rig _ (fun _ => by
      rw [Category.id_comp]; exact left_comp_hom_unit (η[D.P.A]))

  set C : D.X → D.X → D.X → ((TK R).left.presheaf.stalk z)ˣ :=
    fun a a' b => val D.cub.t (D.pt3 a a' b) z J with hCdef
  have h2 : ∀ a a' b, val (D.tau (a + a') b) (𝟙 _) z J * C a a' b =
      val (D.tau a b) (𝟙 _) z J * val (D.tau a' b) (𝟙 _) z J := by
    intro a a' b
    have := (val_mul hG _ _ _).symm.trans ((val_corr hG (hT a a' b) (𝟙 _)).trans (val_mul hG _ _ _))
    have hp : val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a a' b)) (𝟙 _) z J = C a a' b :=
      (val_pull hG D.cub.t (D.pt3 a a' b) (𝟙 _)).trans (by rw [Category.id_comp])
    exact (congrArg (fun x => val (D.tau (a + a') b) (𝟙 _) z J * x) hp).symm.trans this
  have hC : ∀ a a' b, ∃ u : Rˣ, C a a' b = uK R z u := by
    intro a a' b
    have e : D.pt3 a a' b = jK R ≫ (lift (D.c a) (lift (D.c a') (D.c b))).left := by
      unfold DegPre.pt3
      rw [← comp_lift, ← comp_lift, Over.comp_left, toUnit_TK_left]
    show ∃ u : Rˣ, val D.cub.t (D.pt3 a a' b) z J = uK R z u
    rw [e]
    exact val_section_unit D.P z J hJ D.cub.t _ (fun k => by
      rw [← Over.comp_left]; exact left_comp_hom_unit _)

  set S : D.X → ((TK R).left.presheaf.stalk z)ˣ :=
    fun χ => val D.sym (D.xK χ) z J with hSdef
  have h3 : ∀ χ, P (-χ) * S χ = P χ := by
    intro χ
    have := (val_mul hG _ _ _).symm.trans (val_corr hG (hE χ) (𝟙 _))
    rw [val_pull hG, Category.id_comp] at this
    exact this
  have hS : ∀ χ, ∃ u : Rˣ, S χ = uK R z u := by
    intro χ
    have e : D.xK χ = jK R ≫ (D.c χ).left := by
      show (toUnit (TK R) ≫ D.c χ).left = _
      rw [Over.comp_left, toUnit_TK_left]
    show ∃ u : Rˣ, val D.sym (D.xK χ) z J = uK R z u
    rw [e]
    refine val_section_unit D.P z J hJ D.sym _ (fun k => ?_)
    fin_cases k
    · show ((D.c χ).left ≫ (ι[D.P.A]).left) ≫ D.P.A.hom = 𝟙 _
      rw [← Over.comp_left]; exact left_comp_hom_unit _
    · show ((D.c χ).left ≫ 𝟙 D.P.A.left) ≫ D.P.A.hom = 𝟙 _
      rw [Category.comp_id]; exact left_comp_hom_unit _

  obtain ⟨c0, hc0⟩ := hC 0 0 0
  obtain ⟨c1, hc1⟩ := hC y (-y) y
  obtain ⟨s, hs⟩ := hS y
  have e0 := h2 0 0 0
  simp only [h1, add_zero] at e0

  have hP0 : P 0 = (C 0 0 0 * rg)⁻¹ := by
    have : C 0 0 0 = P 0 * (P 0)⁻¹ * (P 0)⁻¹ * rg⁻¹ := mul_left_cancel e0
    rw [this]; group
  have e1 := h2 y (-y) y
  simp only [h1, add_neg_cancel, zero_add, neg_add_cancel] at e1
  have hPm : P (-y) = P y * (S y)⁻¹ := by rw [← h3 y]; group
  rw [hPm, hP0] at e1
  refine ⟨(c0 * r) ^ 2 * c1 * s⁻¹, ?_⟩
  rw [h1, map_mul, map_mul, map_inv, map_pow, map_mul, ← hc0, ← hc1, ← hs, ← hr, hP y]

  rw [eq_mul_inv_of_mul_eq e1.symm]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow]
  abel

end GlobalTheory.Mum.UnitValuedLeadingSection
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Mum.UnitValuedLeadingSection

noncomputable section

namespace GlobalTheory.Mum.UnitValuedLeadingSection

open Formalism.L2.Pj GlobalTheory.PsiCoordLocal

theorem gs_jK_toOpen_top {R : Type} [CommRing R] [IsDomain R] (z : (TK R).left) (r : R) :
    gs (jK R) z ⊤ (DegPre.toOpen (R := R) ⊤ r) = thK R z (algebraMap R (FractionRing R) r) := by
  have hz : jK R z ∈ (⊤ : (Spec (CommRingCat.of R)).Opens) := trivial
  rw [gs_eq _ z ⊤ hz]
  have e := congrArg (fun f => f.hom r)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  have t : DegPre.toOpen (R := R) ⊤ r = (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r := by
    simp [DegPre.toOpen]
  rw [t]
  simp only [thK, RingHom.comp_apply]
  rw [e]
  rfl

theorem psiIn_iff_val : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι), TopGood D.P z J → ∀ (χ : D.X) (I : Ideal R), D.PsiIn χ I ↔ ∃ r ∈ I, ((val (D.psi χ) (𝟙 _) z J : ((TK R).left.presheaf.stalk z)ˣ) : (TK R).left.presheaf.stalk z) = thK R z (algebraMap R (FractionRing R) r) := by
  intro R _ _ _ D z J hJ χ I
  let j : PUnit → D.P.L.ι := fun _ => J (𝟙 _ ≫ D.xK χ)
  have hxK : 𝟙 _ ≫ D.xK χ = jK R ≫ (D.c χ).left := by
    rw [Category.id_comp]
    show (toUnit (TK R) ≫ D.c χ).left = _
    rw [Over.comp_left]
    congr 1 <;> simp
  have hj : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U (j PUnit.unit) := by
    have := hJ.2 (D.c χ).left (Over.w (D.c χ))
    show ⊤ ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U (J (𝟙 _ ≫ D.xK χ))
    rw [hxK, this]
  have h := generic_le D χ j hj
  have key : ∀ r : R, ((jK R).app ⊤).hom (DegPre.toOpen (R := R) ⊤ r) =
      ((TK R).left.presheaf.map (homOfLE h).op).hom ((D.psi χ).s j).val ↔
      ((val (D.psi χ) (𝟙 _) z J : ((TK R).left.presheaf.stalk z)ˣ) : (TK R).left.presheaf.stalk z) =
        thK R z (algebraMap R (FractionRing R) r) := by
    intro r
    have hz : z ∈ jK R ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of R)).Opens) := trivial
    have g1 : gs (𝟙 (Spec (CommRingCat.of (FractionRing R)))) z _ (((jK R).app ⊤).hom (DegPre.toOpen (R := R) ⊤ r)) =
        thK R z (algebraMap R (FractionRing R) r) := by
      rw [gs_pull (𝟙 _) (jK R) z ⊤ trivial, Category.id_comp]
      exact gs_jK_toOpen_top z r
    have g2 : gs (𝟙 (Spec (CommRingCat.of (FractionRing R)))) z _ (((TK R).left.presheaf.map (homOfLE h).op).hom ((D.psi χ).s j).val) =
        ((val (D.psi χ) (𝟙 _) z J : ((TK R).left.presheaf.stalk z)ˣ) : (TK R).left.presheaf.stalk z) := by
      refine (gs_res _ z h hz _).trans ((gs_unit _ _ _ (h hz) _).trans ?_)
      rfl
    constructor
    · intro e
      rw [← g1, ← g2, e]
    · intro e
      refine fn_ext fun y _ => ?_
      obtain rfl : y = z := Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) y z
      rw [g1, g2, e]
  constructor
  · intro hI
    obtain ⟨s, hs, es⟩ := hI j ⊤ (isAffineOpen_top _) hj h
    obtain ⟨r, hr, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ toOpen_top_bijective.2).1 hs
    exact ⟨r, hr, (key r).1 es⟩
  · rintro ⟨r, hr, e⟩
    exact (GlobalTheory.PeriodFormEdge.psiIn_iff ⟨j, hj, h, (key r).2 e⟩ I).2 hr

end GlobalTheory.Mum.UnitValuedLeadingSection
end
end
