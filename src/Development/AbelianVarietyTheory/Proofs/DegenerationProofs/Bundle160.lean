module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle033
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle118
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIsUUOver
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsOfCubeBundleGenerator
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle022
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibre
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle121
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle122
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle130
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle002
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle156
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle155
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolarisedAVIsoDescendsOfRationalThreeTorsion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle133
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle157
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle028
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle016
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle158
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenericFibreIsoOfCompatibleThickenings
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.ExtremalEpi
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

theorem _root_.GlobalTheory.T.thetaPoints_allPrimePowerLevels_of_single_object : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllA fun {E} _ _ _ {H} {D} {l} {Xo} {c} {W₀} Y {O'} _ _ {b} a => ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing O') K] [Algebra (PowerSeries O') K] [FaithfulSMul (PowerSeries O') K] [Algebra.IsAlgebraic (PowerSeries O') K], (∀ x, algebraMap (FractionRing O') K (algebraMap O' _ x) = algebraMap (PowerSeries O') K (PowerSeries.C x)) → ∀ (S : Ser a K (algebraMap _ K)) (n : ℕ), n.Prime → Odd n → (∀ j, 2 ≤ j → ∃ o : Full D K, o.ρ = S.A.ρ ∧ o.I.ζ ((n ^ j) ^ 2) = S.A.I.ζ ((n ^ j) ^ 2) ∧ o.Theta (n ^ j) (S.v (n ^ j))) → ∃ o : Full D K, o.ρ = S.A.ρ ∧ ∀ j, o.I.ζ (n ^ j) = S.A.I.ζ (n ^ j) ∧ o.Theta (n ^ j) (S.v (n ^ j)) := by
  first | exact @GlobalTheory.Ex.AllLevels.one_object | exact GlobalTheory.Ex.AllLevels.one_object | (intros; apply GlobalTheory.Ex.AllLevels.one_object <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

theorem _root_.GlobalTheory.T.exists_compare_uniformisationData_pullback : Laws → Laws2 → Ega → ∀ (R V : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing V] [IsDomain V] [IsLocalRing V] (I : Ideal R) (I' : Ideal V), AdmBase R I → AdmBase V I' → I' ≠ ⊤ → ∀ φ : R →+* V, I.map φ ≤ I' → ∀ (D : DegPre R) (D' : DegPre V) (A : PolAV (Sp (FractionRing R))) (A' : PolAV (Sp (FractionRing V))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of V))) [GrpObj G'] [IsCommMonObj G'] (U : PreU I D A G) (U' : PreU I' D' A' G') (F : G'.left ⟶ G.left) (pb : IsGrpPullback G' G (spMap φ) F) (wL : LB.Iso U'.P.L.L (U.P.L.L.pull F)), IsCPMap U'.P U.P (spMap φ) F pb.1.w wL → ∃ C : Cmp φ U U' F, C.wL = wL := by
  first | exact @GlobalTheory.LN.PreCompare.exists_cmp | exact GlobalTheory.LN.PreCompare.exists_cmp | (intros; apply GlobalTheory.LN.PreCompare.exists_cmp <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem card_torsion_le : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B], IsAbelianScheme B → ∀ (L : LB B.left), AmpleCub B L → ∀ a, SmoothOfRelativeDimension a B.hom → ∃ C : ℕ, ∀ n : ℕ, (n : k) ≠ 0 → Finite {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} ∧ Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} ≤ C * n ^ (2 * a) := by
  intro k _ _ B _ hB L _ a ha
  refine ⟨1, fun n hn => ?_⟩
  have h := GlobalTheory.T.abelianVarietyTorsionCardEqPow k B a n hB ha hn
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn Nat.cast_zero
  refine ⟨Nat.finite_of_card_ne_zero ?_, ?_⟩
  · rw [h]
    exact pow_ne_zero _ hn0
  · rw [h, Nat.one_mul]

end GlobalTheory.SS
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section
namespace GlobalTheory.OneBasis.ThMove
open GlobalTheory.TranslMove

theorem gs_comp {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (q : Y ⟶ X) (z : Z) (U : X.Opens) (h : q (r z) ∈ U) (a : Γ(X, U)) :
    gs (r ≫ q) z U a = (r.stalkMap z).hom (gs q (r z) U a) := by
  rw [← gs_pull r q z U h, gs_stalkMap r z _ h, gs_pull (𝟙 Y) q (r z) U h, Category.id_comp]

theorem sval_all {S : Scheme.{0}} {A T : Over S} {L : LB A.left} {k : ℤ} {s : LB.Sec (LPow A L k T)}
    {q : T.left ⟶ (T ⊗ A).left} {p : T.left ⟶ A.left}
    {e : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => p) (fun _ => k))} {c : Γ(T.left, ⊤)}
    (H : ∀ z J, Good L z J → sval (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) s q z J =
      gs (𝟙 _) z ⊤ c * (val e (𝟙 _) z J).val) {Z : Scheme.{0}} (r : Z ⟶ T.left) (z : Z) {J} (hJ : Good L z J) :
    sval (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) s (r ≫ q) z J = gs r z ⊤ c * (val e r z J).val := by
  have hJ₀ : Good L (r z) (fun χ : T.left ⟶ A.left => J (r ≫ χ)) := fun χ => hJ (r ≫ χ)
  have a := congrArg (r.stalkMap z).hom (H (r z) _ hJ₀)
  rw [map_mul, ← gs_stalkMap r z ⊤ trivial] at a
  refine Eq.trans ?_ (a.trans (congrArg _ ?_))
  · rw [sval_of s (r ≫ q) z J (fun _ => J (r ≫ q ≫ (snd T A).left)) (fun _ => by rw [Category.assoc])]
    exact gs_comp r q z _ (hJ₀.mem _ q) _
  · have m := hJ.mem (fun _ : Fin 1 => p) r
    exact (congrArg _ (gs_unit (𝟙 _) (r z) _ m _).symm).trans ((gs_stalkMap r z _ m _).symm.trans (gs_unit r z _ m _))

section
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {P : PolAV S} {P' : PolAV S'} {φ : P'.A.left ⟶ P.A.left}
  {w : LB.Iso P'.L (P.L.pull φ)} {T : Over S} {T' : Over S'} {h : T'.left ⟶ T.left}
  {Ψ : (T' ⊗ P'.A).left ⟶ (T ⊗ P.A).left}

theorem secRel_of_thru (h₁ : Ψ ≫ (fst T P.A).left = (fst T' P'.A).left ≫ h)
    (h₂ : Ψ ≫ (snd T P.A).left = (snd T' P'.A).left ≫ φ) {k : ℕ} {s : LB.Sec (LPow P.A P.L (k : ℤ) T)}
    {s' : LB.Sec (LPow P'.A P'.L (k : ℤ) T')} (H : Thru w k h s s') : SecRel w Ψ s s' := by
  intro Z r z J J' hJ hJ'
  rw [zpow_natCast, Units.val_pow_eq_pow_val]
  exact H Z r (r ≫ Ψ) (by rw [Category.assoc, h₁]) (by rw [Category.assoc, h₂]) z J J' hJ hJ'

theorem secRel_unique {k : ℤ} {s : LB.Sec (LPow P.A P.L k T)} {a b : LB.Sec (LPow P'.A P'.L k T')}
    (ha : SecRel w Ψ s a) (hb : SecRel w Ψ s b) : a = b :=
  FieldBaseChange.sec_ext' P'.isLB (fun y J' hJ' => by
    obtain ⟨J, hJ⟩ := exists_good_pt P.isLB y
    exact (Units.mul_right_inj _).1 ((ha _ _ y J J' hJ hJ').symm.trans (hb _ _ y J J' hJ hJ')))

theorem val_rigT_move {ρ ρ'} (R : RigPull P'.A P.A f φ w ρ' ρ) (hh : h ≫ T.hom = T'.hom ≫ f) (k : ℤ) (y : T'.left)
    {J J'} (hJ : Good P.L y J) (hJ' : Good P'.L y J') :
    val (rigT P.A P.L ρ T k) h y J =
      wv w y J J' (1 : T' ⟶ P'.A).left ^ k * val (rigT P'.A P'.L ρ' T' k) (𝟙 _) y J' := by
  rw [FrameMove.val_rigT _ _ _ hJ, FrameMove.val_rigT _ _ _ hJ', hh, Category.id_comp, ← mul_zpow]
  refine congrArg (· ^ k) ?_
  exact (val_move (fun _ => PolBaseChange.eSec_comm R.1) R.2.2.2 T'.hom hJ hJ').trans
    (congrArg (· * _) ((Fintype.prod_unique _).trans (zpow_one _)))

end

theorem thC_move : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (gam : FractionRing R →+* FractionRing R') (A : PolAV (Sp (FractionRing R))) (A' : PolAV (Sp (FractionRing R'))) (ψ : A'.A.left ⟶ A.A.left) (ω : LB.Iso A'.L (A.L.pull ψ)) ρ ρ', RigPull A'.A A.A (spMap gam) ψ ω ρ' ρ → ∀ (F F' : Type) [Field F] [Field F'] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F'] (σ : F →+* F'), (∀ x, σ (algebraMap (FractionRing R) F x) = algebraMap (FractionRing R') F' (gam x)) → ∀ (m : ℕ) (th : SecA A F 1) (th' : SecA A' F' 1) (x : TFK (R := R) F ⟶ A.A) (x' : TFK (R := R') F' ⟶ A'.A) (t : SecA A F (m ^ 2)) (t' : SecA A' F' (m ^ 2)) (c : F), x'.left ≫ ψ = spMap σ ≫ x.left → Thru ω 1 (T' := TFK (R := R') F') (T := TFK (R := R) F) (spMap σ) th th' → Thru ω (m ^ 2) (T' := TFK (R := R') F') (T := TFK (R := R) F) (spMap σ) t t' → ThC A ρ m th x t c → ThC A' ρ' m th' x' t' (σ c) := by
  intro R R' _ _ _ _ gam A A' ψ ω ρ ρ' hR F F' _ _ _ _ σ _ m th th' x x' t t' c hx hth ht H
  obtain ⟨α, s₁, θ, gα, nα, tw, sl, ac, hv⟩ := H
  have gp := hR.1
  have hw := hR.2.1
  have := A'.isAb.comm
  replace hx : (spMap σ : (TFK (R := R') F').left ⟶ (TFK (R := R) F).left) ≫ x.left = x'.left ≫ ψ := hx.symm
  have hh := base_comm (x := x') (x₀ := x) gp hx
  obtain ⟨Ψ, h₁, h₂⟩ : ∃ Ψ : (TFK (R := R') F' ⊗ A'.A).left ⟶ (TFK (R := R) F ⊗ A.A).left,
      Ψ ≫ (fst _ A.A).left = (fst _ A'.A).left ≫ spMap σ ∧ Ψ ≫ (snd _ A.A).left = (snd _ A'.A).left ≫ ψ :=
    ⟨pullback.lift ((fst _ A'.A).left ≫ spMap σ) ((snd _ A'.A).left ≫ ψ) (by
      rw [Category.assoc, Category.assoc, hh, gp.1.w, ← Category.assoc, ← Category.assoc, Over.w, Over.w]),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have h0 := pt_pow (x := x') (x₀ := x) gp hx 0
  rw [pow_zero, pow_zero] at h0
  have s₂ : (ptSecT A'.A (1 : TFK (R := R') F' ⟶ A'.A)).left ≫ (snd _ A'.A).left = (1 : TFK (R := R') F' ⟶ A'.A).left := by
    rw [← Over.comp_left, ptSecT, lift_snd]
  have s₃ : (ptSecT A'.A (1 : TFK (R := R') F' ⟶ A'.A)).left ≫ (snd _ A'.A ^ m).left =
      (1 : TFK (R := R') F' ⟶ A'.A).left := by
    rw [← Over.comp_left, FrameMove.comp_pow, ptSecT, lift_snd, one_pow]
  have e₀ : (ptSecT A'.A (1 : TFK (R := R') F' ⟶ A'.A)).left ≫ Ψ =
      spMap σ ≫ (ptSecT A.A (1 : TFK (R := R) F ⟶ A.A)).left := by
    refine FrameMove.prod_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, h₁, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, ptSecT, ptSecT,
        lift_fst, lift_fst, Over.id_left, Over.id_left, Category.id_comp]
      exact (Category.comp_id _).symm
    · rw [Category.assoc, Category.assoc, h₂, ← Category.assoc, s₂, ← Over.comp_left, ptSecT, lift_snd, h0]
  obtain ⟨α', gα', vα⟩ := exists_genRel A.isLB A'.isLB hw Ψ h₂ (pt_pow gp h₂ m) α gα
  obtain ⟨s₁', tw'⟩ := VVRank.exists_isTwistPull A'.A (ψ := mulT A'.A _ m) (hm := lift_snd _ _) A'.isLB gα' th'
  have R₁ := secRel_twist (lift_comm h₁ (pt_pow gp h₂ m) h₂) vα tw tw' (secRel_of_thru h₁ h₂ hth)
  obtain ⟨θ', sl', a⟩ := exists_symLift gp A.isLB A'.isLB hw h₁ h₂
    (fun θ => pt_pow_eq_one (AbLaw.FromCube.kerPow AbLaw.CubeAssembly.cube_and_sections.1) A' (m ^ 2) rfl θ) hx sl
  obtain ⟨u, ac', R₂⟩ := a _ _ _ ac R₁
  obtain rfl : u = t' := secRel_unique R₂ (secRel_of_thru h₁ h₂ ht)
  refine ⟨α', s₁', θ', gα', corr_of_val A'.isLB fun y J' hJ' => ?_, tw', sl', ac', fun y J' hJ' => ?_⟩
  · obtain ⟨J, hJ⟩ := exists_good_pt A.isLB y
    have a₁ := vα _ (ptSecT A'.A (1 : TFK (R := R') F' ⟶ A'.A)).left y J J' hJ hJ'
    have a₂ := (val_pull hJ α _ (spMap σ)).symm.trans ((val_corr hJ nα (spMap σ)).trans
      (val_rigT_move hR hh _ y hJ hJ'))
    rw [e₀, a₂, s₂, s₃, ← zpow_add] at a₁
    rw [val_pull hJ', Category.id_comp]
    exact (mul_left_cancel a₁).symm
  · obtain ⟨J, hJ⟩ := exists_good_pt A.isLB y
    have a₁ := R₂ _ (ptSecT A'.A (1 : TFK (R := R') F' ⟶ A'.A)).left y J J' hJ hJ'
    have a₂ := (sval_all hv (spMap σ) y hJ).trans
      (congrArg (fun v => _ * Units.val v) (val_rigT_move hR hh _ y hJ hJ'))
    rw [Units.val_mul, mul_left_comm] at a₂
    rw [e₀, s₂] at a₁
    exact ((Units.mul_right_inj _).1 (a₁.symm.trans a₂)).trans (congrArg (· * _) (FrameMove.gs_spMap σ y c))

end GlobalTheory.OneBasis.ThMove
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel

theorem _root_.GlobalTheory.T.exists_torsionIsometry_twistByRoots_of_dataIso : BrGtSt → BrWpSt → AllD fun {E} _ _ _ {H} D => letI := H.starRing; ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F] (A : ArcF D R F) (D' : DegPre R') [Module (𝓞 E) D'.X] (oa' : D'.OAct (𝓞 E)), D'.PsiEven → D'.TauBimult → ∀ (N' : NumD F) (ν' : NumOf D' F N') (k : ℕ) (β : A.N.Form k) (u : Fˣ) (r : ℕ → Fˣ) (J : NumD.Iso (A.N.twist β u) N'), Roots u r → ActCompat A.ν A.oa ν' oa' β u r J → ∃ I' : TateIsoQ D D' oa' F, I'.ζ = A.I.ζ ∧ ∀ j, 0 < j → ∀ x, ∃ q', TwJ β u (r j) J (A.q j x) q' ∧ ν'.QPt (I'.ev j x) q' := by
  first | exact @GlobalTheory.Relabel.exists_tateIsoQ_twJ | exact GlobalTheory.Relabel.exists_tateIsoQ_twJ | (intros; apply GlobalTheory.Relabel.exists_tateIsoQ_twJ <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel

theorem _root_.GlobalTheory.T.torsionQuotientAction_compat_of_rosatiValues : GlobalFnsSt → BrGtSt → AllD fun {E} _ _ _ {H} D => letI := H.starRing; ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F] (A : ArcF D R F) (D' : DegPre R') [Module (𝓞 E) D'.X] (oa' : D'.OAct (𝓞 E)), D'.PsiEven → D'.TauBimult → ∀ (N' : NumD F) (ν' : NumOf D' F N') (k : ℕ) (β : A.N.Form k) (u : Fˣ) (r : ℕ → Fˣ) (J : NumD.Iso (A.N.twist β u) N'), Roots u r → A.Bal β → (∀ (x : 𝓞 E) y, ν'.eX (J.e (A.act x y)) = x • ν'.eX (J.e y)) → (∀ (x : 𝓞 E) b, J.φ (actV (N := A.N) A.ν A.oa.onB x b) = actV ν' oa'.onB x (J.φ b)) → (∀ a : 𝓞 E, ∃ ρ ρ', RosV A.ν A.oa.onB a ρ ∧ RosV ν' oa'.onB a ρ' ∧ ∀ b b' : A.N.A, ρ' (J.φ b) (J.φ b') * (J.h (actV (N := A.N) A.ν A.oa.onB (star a) b) * J.h b' * J.h (b * actV (N := A.N) A.ν A.oa.onB a b') : Fˣ) = ρ b b' * (J.h (actV (N := A.N) A.ν A.oa.onB (star a) b * b') * J.h b * J.h (actV (N := A.N) A.ν A.oa.onB a b') : Fˣ)) → ActCompat A.ν A.oa ν' oa' β u r J := by
  first | exact @GlobalTheory.Relabel.actCompat_of_rosV | exact GlobalTheory.Relabel.actCompat_of_rosV | (intros; apply GlobalTheory.Relabel.actCompat_of_rosV <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.Ex.AbPartIso

theorem _root_.GlobalTheory.T.exists_abelianFibre_iso_of_matched_torsion_theta : Laws → ThetaPtDeterminesSt → BrUthSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R), D.PsiEven → D.TauBimult → D'.PsiEven → D'.TauBimult → D.P.g = D'.P.g → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D F N) (ν' : NumOf D' F N') (Q Q' : PolAV (Sp F)) (Φ : Q.A.left ⟶ D.P.A.left) (Φ' : Q'.A.left ⟶ D'.P.A.left), IsFib D F Q Φ → IsFib D' F Q' Φ' → ∀ n : ℕ, n.Prime → Odd n → (n : F) ≠ 0 → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (c : F) (ρ : N.A → N'.A), c ≠ 0 → TorsMap N.toNumB N'.toNumB (n ^ j) c ρ → ∃ σ : Q.A ≅ Q'.A, IsPolIso Q Q' σ ∧ ∀ (x : baseOver (Sp F) ⟶ Q.A) (b : N.A), b ^ (n ^ j) ^ 2 = 1 → (ν.eA b).left = x.left ≫ Φ → (ν'.eA (ρ b)).left = (x ≫ σ.hom).left ≫ Φ' := by
  first | exact @GlobalTheory.Ex.FibIso.exists_iso_fib | exact GlobalTheory.Ex.FibIso.exists_iso_fib | (intros; apply GlobalTheory.Ex.FibIso.exists_iso_fib <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

theorem _root_.GlobalTheory.T.polarisedAVIso_descends_of_rational_threeTorsion : Laws → Laws2 → GlobalTheory.LN.HomExtSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (C : Type) [Field C] [IsAlgClosed C] [Algebra (FractionRing R) C] (B B' : PolAV (Sp R)), RatTors B C 3 → RatTors B' C 3 → ∀ (φ : TF (R := R) C ⊗ B.A ≅ TF (R := R) C ⊗ B'.A) (g : (TF (R := R) C ⟶ B.A) ≃* (TF (R := R) C ⟶ B'.A)), φ.hom ≫ fst _ _ = fst _ _ → (∀ x, lift (𝟙 _) x ≫ φ.hom = lift (𝟙 _) (g x)) → LBIso (B.L.pull (snd (TF (R := R) C) B.A).left) (B'.L.pull (φ.hom ≫ snd (TF (R := R) C) B'.A).left) → ∃ Ψ : B'.A ≅ B.A, IsMonHom Ψ.hom ∧ LBIso B'.L (B.L.pull Ψ.hom.left) ∧ ∀ x, g x ≫ Ψ.hom = x := by
  first | exact @GlobalTheory.polAV_iso_descends_of_ratTors | exact GlobalTheory.polAV_iso_descends_of_ratTors | (intros; apply GlobalTheory.polAV_iso_descends_of_ratTors <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

noncomputable section
namespace GlobalTheory.Ex.OneGen

section Pts
variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
include hp hτ

theorem exists_torsion_up [IsIso τ] {n : ℕ} (x : T ⟶ A) (hx : x ^ n = 1) :
    ∃ x₀ : T₀ ⟶ G, τ ≫ x₀.left = x.left ≫ φ ∧ x₀ ^ n = 1 := by
  let x₀ : T₀ ⟶ G := Over.homMk (inv τ ≫ x.left ≫ φ) (by
    rw [Category.assoc, Category.assoc, hp.1.w, IsIso.inv_comp_eq, hτ, ← Category.assoc, Over.w])
  have e : τ ≫ x₀.left = x.left ≫ φ := IsIso.hom_inv_id_assoc _ _
  refine ⟨x₀, e, Over.OverMorphism.ext ((cancel_epi τ).1 ?_)⟩
  rw [over_pow hp τ hτ e, hx, over_one hp τ hτ]

theorem exists_torsion_down {n : ℕ} (x₀ : T₀ ⟶ G) (hx : x₀ ^ n = 1) :
    ∃ x : T ⟶ A, τ ≫ x₀.left = x.left ≫ φ ∧ x ^ n = 1 := by
  have w : (τ ≫ x₀.left) ≫ G.hom = T.hom ≫ f := by rw [Category.assoc, Over.w, hτ]
  let x : T ⟶ A := Over.homMk (hp.1.lift _ _ w) (hp.1.lift_snd _ _ _)
  have e : τ ≫ x₀.left = x.left ≫ φ := (hp.1.lift_fst _ _ _).symm
  refine ⟨x, e, Over.OverMorphism.ext (hp.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩
  rw [← over_pow hp τ hτ e, hx, over_one hp τ hτ]

theorem secRel_smul {L₀ : LB G.left} {L₁ : LB A.left} {w : LB.Iso L₁ (L₀.pull φ)} {a : ℤ} {B : Over S}
    (σ : T.left ⟶ B.left) (hσ : σ ≫ B.hom = T.hom ≫ f) (β : B ⟶ T₀) (hβ : σ ≫ β.left = τ)
    {th : LB.Sec (LPow A L₁ a T)} {th₀ : LB.Sec (LPow G L₀ a T₀)} (h : SecRel hp τ hτ w th th₀)
    {th' : LB.Sec (LPow G L₀ a B)} {c : Γ(B.left, ⊤)}
    (hc : SecM.ofSec G th' = c • SecM.ofSec G (VVRank.pullS G a β th₀)) :
    SecRel hp σ hσ w (SecM.toSec A (σ.appTop.hom c • SecM.ofSec A th)) th' := by
  intro Z r z J J' hJ hJ'
  have e : psi hp σ hσ ≫ (β ▷ G).left = psi hp τ hτ := by
    refine psi_ext ?_ ?_
    · rw [Category.assoc, ← Over.comp_left, whiskerRight_fst, Over.comp_left, ← Category.assoc, psi_fst', psi_fst',
        Category.assoc, hβ]
    · rw [Category.assoc, VVRank.whisker_snd_left, psi_snd', psi_snd']
  rw [sv_of_eq_mul (s := th') (t := VVRank.pullS G a β th₀) (c := c) (fun j => congrArg (fun q => q.1 j) hc) _ z hJ,
    sv_of_eq_mul (s := SecM.toSec A (σ.appTop.hom c • SecM.ofSec A th)) (t := th) (c := σ.appTop.hom c)
      (fun j => rfl) _ z hJ',
    VVRank.sv_pullS _ _ _ _ _ _ hJ, Category.assoc r _ (β ▷ G).left, e, h _ _ _ _ _ hJ hJ', mul_left_comm,
    Category.assoc r _ (fst B G).left, psi_fst', ← Category.assoc]
  exact congrArg (fun q => _ * (q * _)) (gs_pull _ σ z ⊤ trivial c).symm

end Pts

theorem exists_gen_thG_generic : Laws → Laws2 → ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (x₀ : Sp K ⟶ S) (P : PolAV (Sp K)) (φ : P.A.left ⟶ G.left), IsGrpPullback P.A G x₀ φ → LBIso P.L (L.pull φ) → ∀ (m : ℕ), Odd m → ∀ (Ix : Type) (x : Ix → (baseOver (Sp K) ⟶ P.A)) (v : Ix → K), (∀ y, y ^ (m ^ 2) = 1 ↔ ∃ i, x i = y) → IsThetaPt P m x (fun i => fnOf (v i)) → ∃ th : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk x₀)), IsGenSec G L ((1 : ℕ) : ℤ) th ∧ ∀ (F : Type) [Field F] [IsAlgClosed F] (e : K →+* F) (x' : Sp F ⟶ S) (h : spMap e ≫ x₀ = x') (a : F) (th' : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk x'))), SecM.ofSec G th' = @id Γ((Over.mk x').left, ⊤) (fnOf a) • SecM.ofSec G (VVRank.pullS G _ (Over.homMk (spMap e) h : Over.mk x' ⟶ Over.mk x₀) th) → (∀ i, ∃ z, ThG G L ρ m th' z (fnOf (a * e (v i)))) ∧ ∀ z (c : F), ThG G L ρ m th' z (fnOf c) → ∃ i, c = a * e (v i) := by
  intro hLaw _ S G _ L ρ hL hρ K _ _ _ x₀ P φ hp ⟨w, hw⟩ m hm Ix x v hx hv
  have hL₁ := P.isLB
  have := P.isAb.comm
  obtain ⟨ρ', hρ', hr⟩ := exists_rigidificationPullbackCompatibleIso hp hw hL hL₁ hρ
  have hx' : ∀ i, x i ^ (m ^ 2) = 1 := fun i => (hx _).2 ⟨i, rfl⟩
  obtain ⟨thP, hg, hth⟩ := GlobalTheory.T.exists_generator_thetaPoint_normalised_thetaConstants K P ρ' hρ' m Ix x v hx' hv
  let τ : (baseOver (Sp K)).left ⟶ (Over.mk x₀).left := 𝟙 (Sp K)
  haveI : IsIso τ := inferInstanceAs (IsIso (𝟙 (Sp K)))
  have hτ : τ ≫ (Over.mk x₀).hom = (baseOver (Sp K)).hom ≫ x₀ := rfl
  have hi : inv τ = 𝟙 (Sp K) := IsIso.inv_eq_of_hom_inv_id (Category.id_comp _)
  obtain ⟨th, hrel⟩ := exists_secRel_up hp τ hτ hw hL hL₁ thP
  refine ⟨th, ThetaPtUp.isGenSec_up hp τ hτ hw hL hL₁ hrel hg, fun F _ _ e x' h a th' hth' => ?_⟩
  choose y hy hy' using fun i => exists_torsion_up hp τ hτ (x i) (hx' i)
  have up : ∀ i, ThG G L ρ m th (y i) (fnOf (v i)) := fun i => by
    have q := ThG.up hp τ hτ hw hL hL₁ hr (hy i) (hy' i) hrel (hth i)
    rw [hi] at q
    exact q
  let T' : Over (Sp K) := Over.mk (spMap e)
  let u : T' ⟶ baseOver (Sp K) := Over.homMk (spMap e) (Category.comp_id _)
  let τ' : T'.left ⟶ (Over.mk x₀).left := spMap e
  have hτ' : τ' ≫ (Over.mk x₀).hom = T'.hom ≫ x₀ := rfl
  let σ : T'.left ⟶ (Over.mk x').left := 𝟙 (Sp F)
  haveI : IsIso σ := inferInstanceAs (IsIso (𝟙 (Sp F)))
  have hσ : σ ≫ (Over.mk x').hom = T'.hom ≫ x₀ := (Category.id_comp _).trans h.symm
  have hj : inv σ = 𝟙 (Sp F) := IsIso.inv_eq_of_hom_inv_id (Category.id_comp _)
  obtain ⟨t, ht⟩ := exists_secRel hp τ' hτ' hw hL hL₁ th
  have hrel' := secRel_smul hp τ' hτ' σ hσ (Over.homMk (spMap e) h : Over.mk x' ⟶ Over.mk x₀)
    (Category.id_comp _) ht hth'
  have hu : ∀ i, (u ≫ x i) ^ (m ^ 2) = 1 := fun i => by rw [← MonObj.comp_pow, hx', MonObj.comp_one]
  have down : ∀ i, ThG P.A P.L ρ' m (SecM.toSec P.A (σ.appTop.hom (fnOf a) • SecM.ofSec P.A t)) (u ≫ x i)
      (fnOf (a * e (v i))) := fun i => by
    have e₁ : τ' ≫ (y i).left = (u ≫ x i).left ≫ φ :=
      (congrArg (spMap e ≫ ·) ((Category.id_comp _).symm.trans (hy i))).trans (Category.assoc _ _ _).symm
    have q := ThG.smul (th' := SecM.toSec P.A (σ.appTop.hom (fnOf a) • SecM.ofSec P.A t)) hL₁ rfl
      (ThG.move hp τ' hτ' hw hL hL₁ hr e₁ (hu i) ht (up i))
    have e₂ : σ.appTop.hom (fnOf a) * τ'.appTop.hom (fnOf (v i)) = fnOf (a * e (v i)) :=
      (congrArg (fnOf a * ·)
        (congrArg (fun q => q.hom (v i)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom e))).symm).trans
        (map_mul (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom _ _).symm
    rw [e₂] at q
    exact q
  have hK : ((m ^ 2 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (pow_ne_zero _ hm.pos.ne')
  refine ⟨fun i => ?_, fun z c hz => ?_⟩
  · obtain ⟨z, hz, hz'⟩ := exists_torsion_up hp σ hσ _ (hu i)
    have q := ThG.up hp σ hσ hw hL hL₁ hr hz hz' hrel' (down i)
    rw [hj] at q
    exact ⟨z, q⟩
  · obtain ⟨z', hz₁, hz₂⟩ := exists_torsion_down hp σ hσ z hz.1
    obtain ⟨y', hy₁, rfl⟩ := TorsionFieldExt.exists_of_isAlgClosed hLaw P u hK
      (by rw [← map_natCast e]; exact (map_ne_zero e).2 hK) z' hz₂
    obtain ⟨i, rfl⟩ := (hx y').1 hy₁
    have hun : IsUnit ((m ^ 2 : ℕ) : Γ(Sp K, ⊤)) := by
      rw [← map_natCast (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom]
      exact (IsUnit.mk0 _ hK).map _
    have q : fnOf c = fnOf (a * e (v i)) :=
      ThG.unique hLaw P hm hun (ThG.move hp σ hσ hw hL hL₁ hr hz₁ hz₂ hrel' hz) (down i)
    exact ⟨i, (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv.injective q⟩

end GlobalTheory.Ex.OneGen
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GenericIso


open GlobalTheory.RigidGeneric GlobalTheory.SecRingIso ReciprocityTheory.ChartRestriction.G.DVR in
theorem exists_genericRel : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (U : Unif I D A G) (U' : Unif I D' A' G') (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre) (j : ∀ e : ℕ, thickObj R I e G' ≅ thickObj R I e G), GlobalTheory.GenericIso.LevelIso U.toUnifPre U'.toUnifPre hD j → GlobalTheory.GenericIso.Enough U.toUnifPre U'.toUnifPre hD j → ∃ (Φ : (Over.pullback (jK R)).obj G' ≅ (Over.pullback (jK R)).obj G) (w : LB.Iso (U'.LG.L.pull (pullback.fst G'.hom (jK R))) (U.LG.L.pull (Φ.hom.left ≫ pullback.fst G.hom (jK R)))), GlobalTheory.GenericIso.GenericRel U.toUnifPre U'.toUnifPre hD j Φ w := by
  intro hL R _ _ I hI D D' A A' G G' _ _ _ _ hG hG' U U' hD j _ en
  obtain ⟨w, v, hw, hv, -, lf⟩ := exists_compare U
  obtain ⟨w', v', hw', hv', e', lf'⟩ := exists_compare U'
  have jac : I ≤ Ideal.jacobson ⊥ := by
    have := hI.2.2.2
    exact IsAdicComplete.le_jacobson_bot I
  have := hI.1
  have := hG.smooth
  have := hG'.smooth
  have := hG.geomConnected
  have := hG'.geomConnected
  let Ag : ∀ k, H0 U'.LG.L k → H0 U.LG.L k → Prop := fun k σ' σ => ∀ e,
    Agr (W := (thickObj R I e G').left) (Idx := D.toPre.P.L.ι × D'.toPre.P.L.ι)
      ((j e).hom.left ≫ (fstG I e G).left) (fstG I e G').left
      (fun y i => (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) ((U'.gt e).pG.left y) ∈
        D.toPre.P.L.U i.1 ∧ (U'.gt e).pG.left y ∈ D'.toPre.P.L.U i.2)
      (fun Z r z i jL => Geo.Tor.gw (U.w e) (r ≫ (j e).hom.left) z i.1 (fun _ => jL))
      (fun Z r z i jL => Geo.Tor.gw hD.w (r ≫ (U'.gt e).pG.left) z i.1 i.2 * Geo.Tor.gw (U'.w e) r z i.2 (fun _ => jL))
      σ σ'
  have ov : ∀ e, ((j e).hom.left ≫ (fstG I e G).left) ≫ G.hom = (fstG I e G').left ≫ G'.hom := fun e =>
    (Category.assoc _ _ _).trans ((congrArg ((j e).hom.left ≫ ·) (Over.w (fstG I e G))).trans
      (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ thick R I e) (Over.w (j e).hom))).trans
        (Over.w (fstG I e G')).symm))
  have cov : ∀ e (y : (thickObj R I e G').left), ∃ i : D.toPre.P.L.ι × D'.toPre.P.L.ι,
      (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) ((U'.gt e).pG.left y) ∈
        D.toPre.P.L.U i.1 ∧ (U'.gt e).pG.left y ∈ D'.toPre.P.L.U i.2 := fun e y => by
    obtain ⟨a, ha⟩ := exists_chart D.toPre.P.isLB
      ((hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) ((U'.gt e).pG.left y))
    obtain ⟨b, hb⟩ := exists_chart D'.toPre.P.isLB ((U'.gt e).pG.left y)
    exact ⟨(a, b), ha, hb⟩
  obtain ⟨Φ, w₀, h₀, H⟩ := exists_iso_of_rel hL G.hom G'.hom U.LG.isLB U'.LG.isLB A A' (gen_over' U) (gen_over' U')
    (gen_injective U) (gen_injective U') hv hv' lf lf' Ag
    (fun k c s' s t' t d' d h h' f' f e => (h e).comb (ov e) (h' e) f f')
    (fun n m s' s t' t d' d h h' f' f e => (h e).mul (h' e) f f')
    (fun k s' s h => ⟨fun f => funext ((sec_eq_zero_and_hom_eq_of_thickenings R I jac G).1 _
        (linComb_isLB _ U.LG.isLB _ _) s fun e J => by
          have : IsIso (j e).hom.left := inferInstanceAs (IsIso ((Over.forget _).map (j e).hom))
          exact (ConcreteCategory.bijective_of_isIso ((j e).hom.left.app _)).1
            (((h e).zero U'.LG.isLB (cov e) f J).trans (map_zero _).symm)),
      fun f => funext ((sec_eq_zero_and_hom_eq_of_thickenings R I jac G').1 _
        (linComb_isLB _ U'.LG.isLB _ _) s' fun e J => (h e).symm.zero U.LG.isLB (cov e) f J)⟩)
    (fun k hk s => by
      obtain ⟨c, t', t, hc, h₁, h₂⟩ := (en k hk).1 s
      exact ⟨c, hc, t', t, fun e Z r z i a b hC => h₂ e Z r z i.1 i.2 a b hC.1 hC.2, funext h₁⟩)
    (fun k hk s => by
      obtain ⟨c, t', t, hc, h₁, h₂⟩ := (en k hk).2 s
      exact ⟨c, hc, t', t, fun e Z r z i a b hC => h₂ e Z r z i.1 i.2 a b hC.1 hC.2, funext h₁⟩)
  obtain ⟨u, hu, K⟩ := exists_move U.LG.isLB U'.LG.isLB A.isLB A'.isLB (gen_inv U') hv h₀ hw' e'
    ((U'.gen ≪≫ Φ ≪≫ U.gen.symm).hom.left ≫ pullback.fst G.hom (jK R))
    ((Category.assoc _ _ _).trans (congrArg (U'.gen.hom.left ≫ ·) (Category.assoc _ _ _)))
  refine ⟨U'.gen ≪≫ Φ ≪≫ U.gen.symm, u, hu, fun k hk σ' σ h => ?_⟩
  obtain ⟨a, ha⟩ := exists_pulls U.LG.isLB A.isLB hv σ
  obtain ⟨a', ha'⟩ := exists_pulls U'.LG.isLB A'.isLB hv' σ'
  exact K k σ σ' a a' ha
    (H k hk σ' σ a' a (fun e Z r z i a b hC => h e Z r z i.1 i.2 a b hC.1 hC.2) ha' ha) ha'

end GlobalTheory.GenericIso
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

theorem _root_.GlobalTheory.T.exists_degenerationPreData_over_subfield : Laws → ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (D : DegPre K) (P₀ : PolAV (Sp K₀)) (Φ : D.P.A.left ⟶ P₀.A.left), IsGrpPullback D.P.A P₀.A (spMap i) Φ → LBIso D.P.L (P₀.L.pull Φ) → ∀ c₀ : D.X → (𝟙_ (Over (Sp K₀)) ⟶ P₀.A), (∀ y z, c₀ (y + z) = padd P₀.A (c₀ y) (c₀ z)) → (∀ y, (D.c y).left ≫ Φ = spMap i ≫ (c₀ y).left) → ∃ (D₀ : DegPre K₀) (ψ : TauTwist.PsiFam D) (hψ : ∀ χ, (ψ χ).IsGen) (hD : IsPullDeg i D₀ (TauTwist.withPsi D ψ hψ)), D₀.P = P₀ ∧ HEq (PsiEvenPull.proj hD) Φ := by
  first | exact @GlobalTheory.FieldPull.exists_pre_below | exact GlobalTheory.FieldPull.exists_pre_below | (intros; apply GlobalTheory.FieldPull.exists_pre_below <;> assumption)
end
