module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FinrankMumfordBundleCechHomologyOrigin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2758
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2944
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2762
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2746
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2759
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle090
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle180
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2904
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2907
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleDeeperLevelSiegelCover
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2946
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2696
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2731
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2764
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2697
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle051
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2908
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralDegenerationValues
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle126
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2909
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExistsObjMapOfPIsogenyPullback
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2932
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2838
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnifTorsK

theorem spComp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : B →+* C) (g : A →+* B) :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

theorem bc {S S' : Scheme.{0}} (f : S' ⟶ S) (P : PolAV S) : ∃ (P' : PolAV S') (φ : P'.A.left ⟶ P.A.left),
    P'.g = P.g ∧ IsGrpPullback P'.A P.A f φ ∧ LBIso P'.L (P.L.pull φ) := by
  refine ⟨GlobalTheory.AmpleSpecialisation.baseChange P f, pullback.fst P.A.hom f, rfl, isGrpPullback_pullback P.A f, ?_⟩
  obtain ⟨w, hw⟩ := PolBaseChange.lbIso_refl (pull_isLB P.isLB (pullback.fst P.A.hom f))
  exact ⟨w, hw⟩

theorem lbcomp {X Y Y' : Scheme.{0}} {L : LB X} {L' : LB Y} {L'' : LB Y'} (hL : L.IsLB) (hL' : L'.IsLB)
    (hL'' : L''.IsLB) {φ : Y ⟶ X} {ψ : Y' ⟶ Y} (h : LBIso L' (L.pull φ)) (h' : LBIso L'' (L'.pull ψ)) :
    LBIso L'' (L.pull (ψ ≫ φ)) := by
  have h₁ : LBIso (L'.pull ψ) ((L.pull φ).pull ψ) := GlobalTheory.RigidBundleGlue.LBIso.pull h ψ
  have h₂ : LBIso ((L.pull φ).pull ψ) (L.pull (ψ ≫ φ)) := GlobalTheory.OriginCohom.lbIso_pull_pull_comp hL φ ψ
  have h₃ : LBIso (L'.pull ψ) (L.pull (ψ ≫ φ)) :=
    LBIso.trans (pull_isLB hL' ψ) (pull_isLB (pull_isLB hL φ) ψ) (pull_isLB hL (ψ ≫ φ)) h₁ h₂
  exact LBIso.trans hL'' (pull_isLB hL' ψ) (pull_isLB hL (ψ ≫ φ)) h' h₃

theorem unit_norm (p : ℕ) [Fact p.Prime] (W : Type) [CommRing W] [IsDomain W] [Algebra (FractionRing W) (PadicAlgCl p)]
    (hn : ∀ x : FractionRing W, ‖algebraMap _ (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap W (FractionRing W)))
    {r r' : W} (h : Associated r r') :
    ‖algebraMap (FractionRing W) (PadicAlgCl p) (algebraMap W _ r)‖ =
      ‖algebraMap (FractionRing W) (PadicAlgCl p) (algebraMap W _ r')‖ := by
  obtain ⟨u, rfl⟩ := h
  set emb : W →+* PadicAlgCl p := (algebraMap (FractionRing W) (PadicAlgCl p)).comp (algebraMap W (FractionRing W))
    with hemb
  have hle : ∀ v : W, ‖emb v‖ ≤ 1 := fun v => (hn _).2 ⟨v, rfl⟩
  have hprod : ‖emb (u : W)‖ * ‖emb ((u⁻¹ : Wˣ) : W)‖ = 1 := by
    rw [← norm_mul, ← map_mul, Units.mul_inv, _root_.map_one, norm_one]
  have hu : ‖emb (u : W)‖ = 1 :=
    le_antisymm (hle _) (by nlinarith [norm_nonneg (emb (u : W)), norm_nonneg (emb ((u⁻¹ : Wˣ) : W)), hle ((u⁻¹ : Wˣ) : W)])
  have e₁ : ∀ v : W, algebraMap (FractionRing W) (PadicAlgCl p) (algebraMap W _ v) = emb v := fun _ => rfl
  rw [e₁, e₁, map_mul, norm_mul, hu, _root_.mul_one]



theorem main : ∀ {o Ω o' Ω' : Type} [CommRing o] [Field Ω] [Algebra o Ω] [CommRing o'] [Field Ω'] [Algebra o' Ω'] (S : ThetaSys o Ω) (S' : ThetaSys o' Ω') (ρ : S.Real) (ρ' : S'.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (y₁ : S'.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (u' : ρ'.UTest p y₁) (P₀ : PolAV (Sp (PadicAlgCl p))) (a : P₀.A.left ⟶ u.A.A.left) (a' : P₀.A.left ⟶ u'.A.A.left), IsGrpPullback P₀.A u.A.A (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p))) a → IsGrpPullback P₀.A u'.A.A (spMap (algebraMap (FractionRing u'.V) (PadicAlgCl p))) a' → LBIso P₀.L (u.A.L.pull a) → LBIso P₀.L (u'.A.L.pull a') → ∃ e : u.D.toPre.X ≃+ u'.D.toPre.X, (∀ χ r, u.PsiNorm χ r ↔ u'.PsiNorm (e χ) r) ∧ ∀ (m : ℕ) (pk : QkPt u.D.toPre (PadicAlgCl p) m) (pk' : QkPt u'.D.toPre (PadicAlgCl p) m) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) (x' : TFK (R := u'.V) (PadicAlgCl p) ⟶ u'.A.A) (w : Sp (PadicAlgCl p) ⟶ P₀.A.left), 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x → QkToAkU u'.U.toUnifPre (PadicAlgCl p) m pk' x' → w ≫ P₀.A.hom = 𝟙 _ → w ≫ a = x.left → w ≫ a' = x'.left → CongMod m pk'.y (e pk.y) := by
  intro o Ω o' Ω' _ _ _ _ _ _ S S' ρ ρ' p _ y₀ y₁ u u' P₀ a a' ha ha' hLa hLa'

  obtain ⟨W₀, _, _, _, _, hW₀c, hW₀n, -, hW₀alg, ⟨φ₀, φK₀, hφK₀, hmax₀, hcp₀⟩,
      ⟨φ₀', φK₀', hφK₀', hmax₀', hcp₀'⟩⟩ :=
    GlobalTheory.T.exists_common_complete_dvr_padicAlgClosure_unitBalls p u.V u'.V u.complete u'.complete u.norm_le u'.norm_le ∅

  obtain ⟨B₁, b₁, -, hb₁, hLb₁⟩ := bc (spMap φK₀) u.A
  obtain ⟨B₂, b₂, -, hb₂, hLb₂⟩ := bc (spMap φK₀') u'.A
  have hpa : IsGrpPullback P₀.A u.A.A
      (spMap (algebraMap (FractionRing W₀) (PadicAlgCl p)) ≫ spMap φK₀) a :=
    ha.congr (by rw [spComp, hcp₀]) rfl
  have hpa' : IsGrpPullback P₀.A u'.A.A
      (spMap (algebraMap (FractionRing W₀) (PadicAlgCl p)) ≫ spMap φK₀') a' :=
    ha'.congr (by rw [spComp, hcp₀']) rfl
  obtain ⟨c₁, hc₁b, hc₁h, hc₁, hc₁L⟩ := GlobalTheory.T.polarisedAbelianPoint_lifts_through_intermediate_pullback (spMap φK₀)
    (spMap (algebraMap (FractionRing W₀) (PadicAlgCl p))) u.A B₁ P₀ b₁ a hb₁ hpa
  obtain ⟨c₂, hc₂b, hc₂h, hc₂, hc₂L⟩ := GlobalTheory.T.polarisedAbelianPoint_lifts_through_intermediate_pullback (spMap φK₀')
    (spMap (algebraMap (FractionRing W₀) (PadicAlgCl p))) u'.A B₂ P₀ b₂ a' hb₂ hpa'
  have hLc₁ := hc₁L hLa hLb₁
  have hLc₂ := hc₂L hLa' hLb₂

  obtain ⟨s, hs⟩ := GlobalTheory.T.polarisedAbelian_iso_descends_from_algebraicExtension (FractionRing W₀) (PadicAlgCl p) (algebraMap _ _) hW₀alg B₁ B₂ P₀ c₁ c₂
    hc₁ hc₂ hLc₁ hLc₂

  obtain ⟨W, _, _, _, _, hWc, hWn, hsW, -, ⟨α₀, αK, hαK, hαmax, hαcp⟩, -⟩ :=
    GlobalTheory.T.exists_common_complete_dvr_padicAlgClosure_unitBalls p W₀ W₀ hW₀c hW₀c hW₀n hW₀n s
  have hcomm : (αK.comp φK₀).comp (algebraMap u.V (FractionRing u.V)) =
      (algebraMap W (FractionRing W)).comp (α₀.comp φ₀) := by
    ext v
    have h1 := RingHom.congr_fun hφK₀ v
    have h2 := RingHom.congr_fun hαK (φ₀ v)
    simp only [RingHom.comp_apply] at h1 h2 ⊢
    rw [h1, h2]
  have hcomm' : (αK.comp φK₀').comp (algebraMap u'.V (FractionRing u'.V)) =
      (algebraMap W (FractionRing W)).comp (α₀.comp φ₀') := by
    ext v
    have h1 := RingHom.congr_fun hφK₀' v
    have h2 := RingHom.congr_fun hαK (φ₀' v)
    simp only [RingHom.comp_apply] at h1 h2 ⊢
    rw [h1, h2]
  have hmax : (IsLocalRing.maximalIdeal u.V).map (α₀.comp φ₀) ≤ IsLocalRing.maximalIdeal W := by
    rw [← Ideal.map_map]
    exact (Ideal.map_mono hmax₀).trans hαmax
  have hmax' : (IsLocalRing.maximalIdeal u'.V).map (α₀.comp φ₀') ≤ IsLocalRing.maximalIdeal W := by
    rw [← Ideal.map_map]
    exact (Ideal.map_mono hmax₀').trans hαmax
  have hF : (algebraMap (FractionRing W) (PadicAlgCl p)).comp (αK.comp φK₀) =
      algebraMap (FractionRing u.V) (PadicAlgCl p) := by
    rw [← RingHom.comp_assoc, hαcp, hcp₀]
  have hF' : (algebraMap (FractionRing W) (PadicAlgCl p)).comp (αK.comp φK₀') =
      algebraMap (FractionRing u'.V) (PadicAlgCl p) := by
    rw [← RingHom.comp_assoc, hαcp, hcp₀']

  obtain ⟨C, ψ₁, hgC, hψ₁, hLψ₁⟩ := bc (spMap (αK.comp φK₀)) u.A
  have hψ₁' : IsGrpPullback C.A u.A.A (spMap αK ≫ spMap φK₀) ψ₁ := hψ₁.congr (spComp _ _).symm rfl
  obtain ⟨χ, hχb, -, hχ, hχL⟩ := GlobalTheory.T.polarisedAbelianPoint_lifts_through_intermediate_pullback (spMap φK₀) (spMap αK) u.A B₁ C b₁ ψ₁ hb₁ hψ₁'
  have hLχ := hχL hLψ₁ hLb₁
  obtain ⟨χ₂, hχ₂, hLχ₂, hd⟩ :=
    hs (FractionRing W) αK (algebraMap (FractionRing W) (PadicAlgCl p)) hαcp hsW C χ hχ hLχ
  have hψ₂ : IsGrpPullback C.A u'.A.A (spMap (αK.comp φK₀')) (χ₂ ≫ b₂) :=
    (hχ₂.comp hb₂).congr (spComp _ _) rfl
  have hLψ₂ : LBIso C.L (u'.A.L.pull (χ₂ ≫ b₂)) := lbcomp u'.A.isLB B₂.isLB C.isLB hLb₂ hLχ₂
  have hgC' : C.g = u'.A.g := GlobalTheory.T.polarisedAbelian_relDim_eq_of_grpPullback_field (FractionRing W) _ (spMap (αK.comp φK₀')) u'.A C (χ₂ ≫ b₂) hψ₂

  obtain ⟨D₁, hD₁, G₁, _, _, U₁, hG₁, htor₁⟩ :=
    GlobalTheory.T.uniformisation_moves_along_dvr_injection_given_fibre u.V W u.complete hWc (α₀.comp φ₀) (αK.comp φK₀) hcomm hmax u.D u.A u.G u.U C ψ₁ hψ₁ hLψ₁
      hgC (PadicAlgCl p) hF
  obtain ⟨D₂, hD₂, G₂, _, _, U₂, hG₂, htor₂⟩ :=
    GlobalTheory.T.uniformisation_moves_along_dvr_injection_given_fibre u'.V W u'.complete hWc (α₀.comp φ₀') (αK.comp φK₀') hcomm' hmax' u'.D u'.A u'.G u'.U C
      (χ₂ ≫ b₂) hψ₂ hLψ₂ hgC' (PadicAlgCl p) hF'
  haveI : CharZero (PadicAlgCl p) :=
    charZero_of_injective_algebraMap (algebraMap ℚ_[p] (PadicAlgCl p)).injective
  haveI : CharZero W :=
    RingHom.charZero ((algebraMap (FractionRing W) (PadicAlgCl p)).comp (algebraMap W (FractionRing W)))

  obtain ⟨ε, hεψ, hεt⟩ := GlobalTheory.TwoUnifTors.main W hWc C G₁ G₂ hG₁ hG₂ D₁ D₂ U₁ U₂
  have hv₁ : ∀ v : u.V, algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ v) =
      algebraMap (FractionRing W) (PadicAlgCl p) (algebraMap W _ ((α₀.comp φ₀) v)) := by
    intro v
    have h1 := RingHom.congr_fun hcomm v
    have h2 := RingHom.congr_fun hF (algebraMap u.V (FractionRing u.V) v)
    simp only [RingHom.comp_apply] at h1 h2 ⊢
    rw [← h2, h1]
  have hv₂ : ∀ v : u'.V, algebraMap (FractionRing u'.V) (PadicAlgCl p) (algebraMap u'.V _ v) =
      algebraMap (FractionRing W) (PadicAlgCl p) (algebraMap W _ ((α₀.comp φ₀') v)) := by
    intro v
    have h1 := RingHom.congr_fun hcomm' v
    have h2 := RingHom.congr_fun hF' (algebraMap u'.V (FractionRing u'.V) v)
    simp only [RingHom.comp_apply] at h1 h2 ⊢
    rw [← h2, h1]
  have hW1 : ∀ v : W, ‖algebraMap (FractionRing W) (PadicAlgCl p) (algebraMap W _ v)‖ ≤ 1 :=
    fun v => (hWn _).2 ⟨v, rfl⟩
  refine ⟨hD₁.xe.symm.trans (ε.trans hD₂.xe), ?_, ?_⟩
  · intro χ r
    obtain ⟨y, rfl⟩ := hD₁.xe.surjective χ
    rw [psiNorm_iff, psiNorm_iff]
    have e1 := GlobalTheory.T.psiCoordinate_norm_invariant_degData_pullback p u.V W (α₀.comp φ₀) hv₁ hW1 u.D.toPre D₁.toPre hD₁ y r
    have e2 := GlobalTheory.T.psiCoordinate_norm_invariant_degData_pullback p u'.V W (α₀.comp φ₀') hv₂ hW1 u'.D.toPre D₂.toPre hD₂ (ε y) r
    obtain ⟨⟨r₁, hr₁⟩, n₁⟩ := GlobalTheory.T.psiCoordinate_norm_chart_eq_coordinate_norm_padicDVR p W hWn D₁ y
    obtain ⟨⟨r₂, hr₂⟩, n₂⟩ := GlobalTheory.T.psiCoordinate_norm_chart_eq_coordinate_norm_padicDVR p W hWn D₂ (ε y)
    have e3 : PsiNormAt p D₁.toPre y r ↔ PsiNormAt p D₂.toPre (ε y) r := by
      rw [n₁ r₁ hr₁ r, n₂ r₂ hr₂ r, unit_norm p W hWn (hεψ y r₁ r₂ hr₁ hr₂)]
    simp only [AddEquiv.trans_apply, AddEquiv.symm_apply_apply]
    exact e1.trans (e3.trans e2.symm)
  · intro m pk pk' x x' w hm hx hx' hw hwx hwx'
    obtain ⟨q₁, x₁, hq₁, hx₁ψ, hx₁⟩ := htor₁ m hm pk x hx
    obtain ⟨q₂, x₂, hq₂, hx₂ψ, hx₂⟩ := htor₂ m hm pk' x' hx'

    have hsq : c₁ ≫ B₁.A.hom =
        (P₀.A.hom ≫ spMap (algebraMap (FractionRing W) (PadicAlgCl p))) ≫ spMap αK := by
      rw [hc₁h, Category.assoc, spComp, hαcp]
    obtain ⟨d, hdχ, hdh⟩ : ∃ d : P₀.A.left ⟶ C.A.left, d ≫ χ = c₁ ∧
        d ≫ C.A.hom = P₀.A.hom ≫ spMap (algebraMap (FractionRing W) (PadicAlgCl p)) :=
      ⟨hχ.1.lift _ _ hsq, hχ.1.lift_fst _ _ _, hχ.1.lift_snd _ _ _⟩
    have hdχ₂ : d ≫ χ₂ = c₂ := hd d hdχ hdh
    have hT : (TFK (R := W) (PadicAlgCl p)).hom = spMap (algebraMap (FractionRing W) (PadicAlgCl p)) := rfl
    have hbase : (w ≫ d) ≫ C.A.hom = (TFK (R := W) (PadicAlgCl p)).hom := by
      rw [Category.assoc, hdh, ← Category.assoc, hw, Category.id_comp, hT]
    have k₁ : x₁.left = w ≫ d := by
      apply hψ₁.1.hom_ext
      · rw [hx₁ψ, ← hχb, Category.assoc, reassoc_of% hdχ, hc₁b, hwx]
      · rw [Over.w x₁, hbase]
    have k₂ : x₂.left = w ≫ d := by
      apply hψ₂.1.hom_ext
      · rw [hx₂ψ, Category.assoc, reassoc_of% hdχ₂, hc₂b, hwx']
      · rw [Over.w x₂, hbase]
    have hxx : x₂ = x₁ := Over.OverMorphism.ext (k₂.trans k₁.symm)
    rw [hxx] at hx₂
    have hc := hεt (PadicAlgCl p) m q₁ q₂ x₁ hm hx₁ hx₂
    unfold CongMod at hc ⊢
    obtain ⟨z, hz⟩ := hc
    refine ⟨hD₂.xe z, ?_⟩
    rw [← hq₂, hz, map_add (f := _), map_nsmul, ← hq₁]
    simp

end GlobalTheory.UnifTorsK
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

theorem _root_.GlobalTheory.T.labelCongruence_endo_all_algClosed_fields : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (eA : u.A.A ⟶ u.A.A) (s : u.D.toPre.X →+ u.D.toPre.X), (∀ (m : ℕ) (pk pk' : QkPt u.D.toPre (PadicAlgCl p) m) (x x' : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk' x' → x'.left = x.left ≫ eA.left → CongMod m pk'.y (s pk.y)) → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing u.V) F] (k : ℕ), 1 ≤ k → IsUnit (k : u.V) → ∀ (q q' : QkPt u.D.toPre F k) (a a' : TFK (R := u.V) F ⟶ u.A.A), QkToAkU u.U.toUnifPre F k q a → QkToAkU u.U.toUnifPre F k q' a' → a.left = a'.left ≫ eA.left → CongMod k q.y (s q'.y) := by
  first | exact @GlobalTheory.LabelTransfer.main | exact GlobalTheory.LabelTransfer.main | (intros; apply GlobalTheory.LabelTransfer.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.polAV_point_defined_over_of_coords_proportional : ∀ (K : Type) [Field K] [IsAlgClosed K] (k₀ : Subfield K), IsAlgClosed k₀ → ∀ (P₀ : PolAV (Sp k₀)) (m : ℕ), Odd m → 3 ≤ m → (m : K) ≠ 0 → ∀ (z : Over.mk (spMap k₀.subtype) ⟶ P₀.A) (v : {y : Over.mk (spMap k₀.subtype) ⟶ P₀.A // y ^ m ^ 2 = 1} → K) (l : K) (r : {y : Over.mk (spMap k₀.subtype) ⟶ P₀.A // y ^ m ^ 2 = 1} → K), GlobalTheory.Ex.IsCoordPt P₀ m (fun i => i.1) z (fun i => GlobalTheory.Ex.fnOf (v i)) → (∀ i, r i ∈ k₀) → (∀ i, v i = l * r i) → GlobalTheory.Poinc.Sep.DefOver k₀ z.left := by
  first | exact @GlobalTheory.Poinc.Sep.defOver_of_coord_proportional | exact GlobalTheory.Poinc.Sep.defOver_of_coord_proportional | (intros; apply GlobalTheory.Poinc.Sep.defOver_of_coord_proportional <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

namespace GlobalTheory.MumValues

theorem exists_values : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F], ∃ N : NumD F, Nonempty (NumOf D.toPre F N) := by
  intro R _ _ _ hR D F _ _ _
  haveI : IsNoetherianRing R := hR.1.1
  obtain ⟨N, ν, -⟩ := GlobalTheory.ValuesExist.exists_integral_values GlobalTheory.allSixLaws.1 R D.toPre D.psi_even D.tau_bimult F ⊤
    (fun _ => trivial)
  exact ⟨N, ⟨ν⟩⟩

end GlobalTheory.MumValues
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover

theorem _root_.GlobalTheory.T.torsionFamily_surjective_iff_geometricPoint : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 0 < M → M.Coprime p → ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ S) (e : (Fin h ⊕ Fin h → ℤ) → (Over.mk y ⟶ o.A)), (∀ a c, e (a + c) = e a * e c) → (∀ a, e a ^ M = 1) → (∀ a, e a = 1 ↔ ∃ c, a = M • c) → ((∀ g : Over.mk y ⟶ o.A, g ^ M = 1 → ∃ a, e a = g) ↔ (M = 1 ∨ 2 * h = Module.finrank ℤ D.La)) := by
  first | (exact @GlobalTheory.HTSympCover.onto_tors_iff) | (exact GlobalTheory.HTSympCover.onto_tors_iff) | (intros; apply GlobalTheory.HTSympCover.onto_tors_iff  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.harrisTaylor_pullback_abelian_map_unique_of_base_eq : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (S S' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (o : Obj b N s) (o' : Obj b N s') (f f' : S' ⟶ S) (m₁ : ObjMap o' o f) (m₂ : ObjMap o' o f'), f = f' → m₁.φ = m₂.φ := by
  first | exact @GlobalTheory.UPel.HT.Rigid.objMap_phi_unique | exact GlobalTheory.UPel.HT.Rigid.objMap_phi_unique | (intros; apply GlobalTheory.UPel.HT.Rigid.objMap_phi_unique <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_finite_etale_deeper_level_siegel_cover : ∀ (h n N : ℕ) (B B' : Type) [CommRing B] [CommRing B'] (ζ : B) (b : TBase B' N) (j : B →+* B') (S : Scheme.{0}) (s' : S ⟶ Sp B') (c : SiegPre h n ζ (s' ≫ spMap j)), 3 ≤ n → Odd N → n ∣ N → j ζ = (b.ζ : B') ^ (N / n) → c.Principal → ∃ (S₁ : Scheme.{0}) (π : S₁ ⟶ S) (C : SiegPre h N (b.ζ : B') (π ≫ s')), IsFinite π ∧ Etale π ∧ Surjective π ∧ SRel C c (N / n) 1 π ∧ ∀ (T : Scheme.{0}) (t : T ⟶ S) (C' : SiegPre h N (b.ζ : B') (t ≫ s')), SRel C' c (N / n) 1 t → ∃! t₁ : T ⟶ S₁, t₁ ≫ π = t ∧ SiegPB C' C t₁ := by
  first | exact @GlobalTheory.SiegCover.exists_levelCover | exact GlobalTheory.SiegCover.exists_levelCover | (intros; apply GlobalTheory.SiegCover.exists_levelCover <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.PrincipalDescent

theorem principal_descends : ∀ (h n N : ℕ) (o o' : Type) [CommRing o] [IsNoetherianRing o] [CommRing o'] (b : TBase o n) (ζ' : o') (j : o →+* o') (X Y : Scheme.{0}) (s' : X ⟶ Sp o') (π : X ⟶ Y) (sY : Y ⟶ Sp o) (C : SiegPre h N ζ' s') (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (ν : Ga → (C.A.left ⟶ C.A.left)), N ≠ 0 → IsUnit (N : o') → n ∣ N → j (b.ζ : o) = ζ' ^ (N / n) → π ≫ sY = s' ≫ spMap j → IsGaloisCover Ga ρ π → IsQProjOver (π ≫ sY) → LocallyOfFiniteType sY → C.Principal → ν 1 = 𝟙 _ → (∀ a c, ν (a * c) = ν a ≫ ν c) → (∀ a, SRelBy C C (N / n) (N / n) (ρ a) (ν a)) → ∃ c : SiegPre h n (b.ζ : o) sY, c.Principal ∧ SRel C c (N / n) 1 π := by
  intro h n N o o' _ _ _ b ζ' j X Y s' π sY C Ga _ ρ ν hN hNu hdiv hζ hbase hπ hq hft hP ν1 νm hν
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  obtain ⟨c, hCc, -⟩ := GlobalTheory.T.exists_siegelObject_lowered_level h n N o o' b.ζ ζ' j X s' C hN hNu hdiv hζ
  have hqA : IsQProjOver (C.A.hom ≫ π ≫ sY) := GlobalTheory.T.isQProjOver_of_relAmple_over_qproj_noetherian o X (π ≫ sY) C.A C.diag hq (pull_isLB C.isLB _) hP.1
  obtain ⟨A₀, _, φ, hA₀, gp, hφ⟩ := GlobalTheory.T.abelianScheme_descends_galoisCover_noetherian_base o X Y π sY Ga ρ C.A ν hπ hqA C.ab (fun a => (hν a).1) ν1 νm
  obtain ⟨P₀, φ₂, hP₀, sq, iso, norm⟩ := GlobalTheory.T.exists_squareBundle_descent_galoisCover X Y π Ga ρ C.A A₀ φ ν C.P hπ C.ab hA₀ gp hφ (fun a => (hν a).1) ν1 νm
    C.isLB C.rig₁ (fun a => (hν a).2.1)
  have hlev : ∀ a, ∃ x₀ : 𝟙_ (Over Y) ⟶ A₀, (C.lev a ^ (N / n)).left ≫ φ = π ≫ x₀.left := by
    intro a
    obtain ⟨f, hf, -⟩ := hπ.existsUnique_desc ((C.lev a ^ (N / n)).left ≫ φ) (fun g => by
      rw [← Category.assoc, ← (hν g).2.2 a, Category.assoc, hφ.inv g])
    have hf' : f ≫ A₀.hom = 𝟙 Y := by
      have := hπ.fin
      have := hπ.etale
      have := hπ.onto
      have : Epi π := Flat.epi_of_flat_of_surjective _
      rw [← cancel_epi π, ← Category.assoc, hf, Category.assoc, gp.1.w, ← Category.assoc, Over.w]
      simp
    exact ⟨Over.homMk f hf', hf.symm⟩
  choose lev₀ hlev₀ using hlev
  obtain ⟨φ', φ₂', gp', sq', iso', hlev'⟩ := GlobalTheory.T.descendedData_transport_identity_levelChange h n N (N / n) o o' b.ζ ζ' X Y (s' ≫ spMap j) s' C c π A₀ φ φ₂ P₀ lev₀
    hCc gp sq hP₀ iso hlev₀
  obtain ⟨c₀, hpb⟩ := GlobalTheory.T.exists_siegelObject_of_galois_descended_data h n o b.ζ X Y π (s' ≫ spMap j) sY Ga ρ c A₀ φ' φ₂' P₀ lev₀ hbase.symm hπ hA₀ gp' sq' hP₀
    iso' norm hlev'
  have hR : SRel C c₀ (N / n) 1 π := by
    have e := ((GlobalTheory.T.siegelObjectPullbackLevelPower_calculus h n n N o o o' b.ζ b.ζ ζ' Y X X sY (s' ≫ spMap j) s' c₀ c C π (𝟙 X) 1 1 (N / n)
      ((sRel_one_one_iff c c₀ π).2 hpb)).1).1 hCc
    rwa [Category.id_comp] at e
  exact ⟨c₀, GlobalTheory.T.principal_descent_finite_etale_surjective h N n (N / n) 1 o' o ζ' b.ζ X Y s' sY π C c₀ hπ.fin hπ.etale hπ.onto hR hP, hR⟩

end GlobalTheory.PrincipalDescent
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

theorem _root_.GlobalTheory.T.holomorphicMap_lifts_locally_to_periodFamilies : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (Λ : Type) (F : Fam ℂ O Λ g) (N : ℕ) (D' : PLat O bar) (t : Λ → D'.La) (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ F.X)) (b₀ : Fin m → ℂ) P₀ e₀, 0 < N → (∀ a, F.eta a ^ N = 1) → LocallyOfFiniteType F.s → IsOpen B → b₀ ∈ B → (∀ b ∈ B, y b ≫ F.s = spMap (RingHom.id ℂ)) → IsHolTo B y → UnifAt F (RingHom.id ℂ) ρ N D' t P₀ (y b₀) e₀ → ∃ (B' : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → (D'.La →+ (Fin g → ℂ))) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ F.A)), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ P b₀ = P₀ ∧ IsHolPeriods D' ρ B' P ∧ IsHolTo (B' ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left) ∧ ∀ b ∈ B', UnifAt F (RingHom.id ℂ) ρ N D' t (P b) (y b) (e b) := by
  first | exact @GlobalTheory.PELU.holomorphic_map_lifts_to_periods | exact GlobalTheory.PELU.holomorphic_map_lifts_to_periods | (intros; apply GlobalTheory.PELU.holomorphic_map_lifts_to_periods <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.InvUnit

theorem exists_unit_of_mem_range {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (hf : Function.Injective f)
    (u : Bˣ) (h : u.val ∈ Set.range f) (h' : (u⁻¹).val ∈ Set.range f) : ∃ g : Aˣ, Units.map (f : A →* B) g = u := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨g', hg'⟩ := h'
  have e : g * g' = 1 := hf (by rw [map_mul, hg, hg', map_one, Units.mul_inv])
  exact ⟨⟨g, g', e, (mul_comm g' g).trans e⟩, Units.ext hg⟩

theorem map_inv_eq {B : Type} [CommRing B] (t : B →+* B) (u : Bˣ) (h : t u.val = u.val) :
    t (u⁻¹).val = (u⁻¹).val := by
  have e : u.val * t (u⁻¹).val = 1 := by
    conv_lhs => rw [← h]
    rw [← map_mul, Units.mul_inv, map_one]
  exact (Units.inv_eq_of_mul_eq_one_right e).symm

theorem invariant_units : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (G' : Over (Sp R')) [GrpObj G'] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (act : Gal ρ → (G'.left ⟶ G'.left)), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → (∀ σ, IsGrpPullback G' G' (spMap (Gal.hom σ)) (act σ)) → (∀ σ, act σ ≫ β = β) → ∀ O : G.left.Opens, Function.Injective (β.app O).hom ∧ ∀ u : Γ(G'.left, β ⁻¹ᵁ O)ˣ, (∀ σ (h : β ⁻¹ᵁ O ≤ act σ ⁻¹ᵁ (β ⁻¹ᵁ O)), ((act σ).appLE _ _ h).hom u.val = u.val) → ∃ g : Γ(G.left, O)ˣ, pullU β O g = u := by
  intro R _ _ _ _ R' _ _ _ ρ hF hG G' _ G _ _ β act hS hβ hact hinv O
  have := hS.smooth
  have H := GlobalTheory.T.galois_invariant_functions_flat_baseChange R R' ρ hF hG G.left G'.left G.hom G'.hom β inferInstance hβ.1 act hinv
    (fun σ => (hact σ).1.w) O
  refine ⟨H.1, fun u hu => ?_⟩
  exact exists_unit_of_mem_range (β.app O).hom H.1 u (H.2 _ hu) (H.2 _ fun σ h => map_inv_eq _ u (hu σ h))

end GlobalTheory.Mum.InvUnit
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.galois_transitive_on_fibres_flat_baseChange : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'], Function.Injective (algebraMap R R') → IsGal (algebraMap R R') → ∀ (Y : Over (Sp R)), Flat Y.hom → ∀ (Z : Scheme.{0}) (p : Z ⟶ Y.left) (s : Z ⟶ Sp R'), IsPullback p s Y.hom (spMap (algebraMap R R')) → ∀ z z' : Z, p z = p z' → ∃ (σ : Gal (algebraMap R R')) (h : Z ⟶ Z), h ≫ p = p ∧ h ≫ s = s ≫ spMap (Gal.hom σ) ∧ h z = z' := by
  first | exact @GlobalTheory.Mum.gal_transitive_on_fibres | exact GlobalTheory.Mum.gal_transitive_on_fibres | (intros; apply GlobalTheory.Mum.gal_transitive_on_fibres <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem _root_.GlobalTheory.T.exists_objMap_of_p_isogeny_pullback : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (T Y : Scheme.{0}) (s₁ : T ⟶ Sp R) (s : Y ⟶ Sp R) (t : T ⟶ Y) (o₁ o₁' : Obj b N s₁) (o o' : Obj b N s) (m : ObjMap o₁ o t) (ψ₁ : o₁.A ⟶ o₁'.A) (ψ : o.A ⟶ o'.A) (θ : o₁'.A.left ⟶ o'.A.left), IsUnit ((p : ℕ) : R) → IsPIsog c o₁ o₁' ψ₁ → IsPIsog c o o' ψ → IsGrpPullback o₁'.A o'.A t θ → m.φ ≫ ψ.left = ψ₁.left ≫ θ → ∃ m' : ObjMap o₁' o' t, m'.φ = θ := by
  first | exact @UpperTheory.Cb.exists_objMap_of_p_isogeny_pullback | exact UpperTheory.Cb.exists_objMap_of_p_isogeny_pullback
end
