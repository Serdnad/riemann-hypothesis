module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle019
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle048
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle020
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle016
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDescentOfInvGenOfInvariants
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle078
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecOnNonvanishingOfTameQuotient
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle112
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle052
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmulApplyEqOfEqOnInvariants
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle047
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle064
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle065
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle111
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle109
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelAbelianSchemeConstOverDualNumbers
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle108
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionSectionCoordsThetaTimesRoots
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle110
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.RelAmpleQProj

open LBGerm GlobalTheory.AbLaw ReciprocityTheory.ChartRestriction.G.Out TopologicalSpace

variable {Y : Scheme.{0}} {L M G : LB Y}

def secPwOne (σ : G.Sec) : (pw G 1).Sec where
  f := σ.f
  compat i j := by
    have h := σ.compat i j
    rw [← zpow_one (G.g i j)] at h
    exact h

theorem exists_sec_tw_locus [CompactSpace Y] [QuasiSeparatedSpace Y] (hM : M.IsLB) (hG : G.IsLB) (σ : G.Sec)
    (V : Y.Opens) (hV : V = nonzeroLocus σ) (r : (M.pull V.ι).Sec) :
    ∃ (k : ℕ) (u : (tw M G (k : ℤ)).Sec), V.ι ⁻¹ᵁ nonzeroLocus u = nonzeroLocus r := by
  obtain ⟨s, ⟨hs, hr⟩, -⟩ := existsUnique_secOn_of_pull M V r
  obtain ⟨k, H⟩ := exists_tw_extend_pow_mul Y G M 1 (secPwOne σ) V 0 hG hM hV inferInstance inferInstance
    (SecOn.twZeroEquiv hM hG V (GlobalTheory.LB.mkSec s hs))
  rw [show (0 : ℤ) + k * 1 = k by ring] at H
  obtain ⟨a, ha⟩ := H
  let w : (tw M G (k : ℤ)).Sec := ⟨fun i => resG Y (le_inf le_top le_rfl) (GlobalTheory.LB.coord a i), fun i j => by
    change resG Y _ (resG Y _ _) = _ * resG Y _ (resG Y _ _)
    rw [resG_resG, resG_resG, GlobalTheory.LB.coord_rel a i j (le_inf le_top inf_le_left) (le_inf le_top inf_le_right) le_rfl, rs_self]⟩
  refine ⟨k, w, ?_⟩
  ext z
  obtain ⟨p, hp⟩ := exists_chart hM (V.ι z)
  obtain ⟨l, hl⟩ := exists_chart hG (V.ι z)
  have hzV : V.ι z ∈ V := z.2
  have hz : V.ι z ∈ V ⊓ (M.U p ⊓ G.U l) := ⟨hzV, hp, hl⟩
  have hz' : V.ι z ∈ M.U p ⊓ G.U l := ⟨hp, hl⟩
  have hzp : z ∈ (M.pull V.ι).U (fun _ => p) := mem_pull.2 hp
  have e := congrArg (gs V.ι z _) (ha p l)
  rw [SecOn.twCoord_twZeroEquiv, gs_res _ z _ hz, gs_mul _ z _ hz, gs_pow _ z _ hz, gs_res _ z _ hz] at e
  have e₁ : gs V.ι z _ ((w).f (p, l)) = gs V.ι z _ (SecOn.twCoord a p l) :=
    gs_res V.ι z _ hz' _
  have e₂ : gs (𝟙 _) z _ (r.f fun _ => p) = gs V.ι z _ (s p) := by
    rw [← hr, gs_appLE V.ι _ _ _ (𝟙 _) z hzp, Category.id_comp]
  have hσ : IsUnit (gs V.ι z (V ⊓ (M.U p ⊓ G.U l)) (rs Y (inf_le_right.trans inf_le_right) (σ.f l))) := by
    rw [gs_res _ z _ hz]
    exact (mem_nonzeroLocus_iff_pull σ V.ι z hl).1 (hV.le hzV)
  refine (mem_nonzeroLocus_iff_pull (w) V.ι z (k := (p, l)) hz').trans
    (Iff.trans ?_ (mem_nonzeroLocus_iff_isUnit r hzp).symm)
  rw [e₂]
  refine (iff_of_eq (congrArg IsUnit (e₁.trans e))).trans ?_
  rw [IsUnit.mul_iff]
  exact and_iff_right (hσ.pow k)

theorem exists_sec_pow_tw {m k c e : ℕ} (he : 1 ≤ e) (h : c * m = k + e) (u : (tw (lbPow L m) G (k : ℤ)).Sec)
    (σ : G.Sec) : ∃ w : (lbPow (tw L G (c : ℤ)) m).Sec, nonzeroLocus w = nonzeroLocus u ⊓ nonzeroLocus σ := by
  have le : ∀ J : PUnit → L.ι × G.ι, powChart (tw L G (c : ℤ)) J ≤
      powChart L (fun _ => (J PUnit.unit).1) ⊓ G.U (J PUnit.unit).2 := fun J y hy =>
    ⟨mem_powChart.2 (mem_powChart.1 hy).1, (mem_powChart.1 hy).2⟩
  let F : ∀ J : PUnit → L.ι × G.ι, Γ(Y, powChart (tw L G (c : ℤ)) J) := fun J =>
    resG Y (le J) (show Γ(Y, powChart L (fun _ => (J PUnit.unit).1) ⊓ G.U (J PUnit.unit).2) from
      u.f (fun _ => (J PUnit.unit).1, (J PUnit.unit).2)) *
      resG Y ((le J).trans inf_le_right) (σ.f (J PUnit.unit).2) ^ e
  have hF : ∀ (y : Y) (J : PUnit → L.ι × G.ι), y ∈ powChart (tw L G (c : ℤ)) J → gs (𝟙 Y) y _ (F J) =
      gs (𝟙 Y) y _ (u.f (fun _ => (J PUnit.unit).1, (J PUnit.unit).2)) *
        gs (𝟙 Y) y _ (σ.f (J PUnit.unit).2) ^ e := fun y J hy => by
    rw [gs_mul _ y _ hy, gs_pow _ y _ hy, gs_res _ y _ hy, gs_res _ y _ hy]
    rfl
  refine ⟨powSecOfGerm (L := tw L G (c : ℤ)) m F fun y J J' hJ hJ' => ?_, ?_⟩
  · have e₁ := gs_compat u (𝟙 Y) y (j := (fun _ => (J PUnit.unit).1, (J PUnit.unit).2))
      (j' := (fun _ => (J' PUnit.unit).1, (J' PUnit.unit).2)) (le J hJ) (le J' hJ')
    have e₂ := TwistGen.gm_tw_g (lbPow L m) G k y (fun _ => (J PUnit.unit).1, (J PUnit.unit).2)
      (fun _ => (J' PUnit.unit).1, (J' PUnit.unit).2) (le J hJ) (le J' hJ')
    have e₃ := gm_lbPow_g (L := L) m (𝟙 Y) y (fun _ => (J PUnit.unit).1) (fun _ => (J' PUnit.unit).1)
      (le J hJ).1 (le J' hJ').1
    have e₄ := TwistGen.gm_tw_g L G c y (J PUnit.unit) (J' PUnit.unit) (mem_powChart.1 hJ) (mem_powChart.1 hJ')
    have e₅ := gs_compat σ (𝟙 Y) y (le J hJ).2 (le J' hJ').2
    dsimp only at e₂
    rw [e₃] at e₂
    refine (hF y J hJ).trans (Eq.trans ?_ (congrArg₂ (fun a b => a ^ m * b) e₄ (hF y J' hJ')).symm)
    rw [e₅]
    refine (congrArg (· * _) (e₁.trans (congrArg (· * _) e₂))).trans ?_
    simp only [Units.val_pow_eq_pow_val]
    rw [mul_pow, mul_pow, ← pow_mul, h]
    ring
  · refine nonzeroLocus_pow_eq_of _ _ (fun y hy => ?_) fun y J hJ => ?_
    · obtain ⟨p, hp⟩ := exists_chart_of_mem_nonzeroLocus hy.1
      exact ⟨fun _ => (p.1 PUnit.unit, p.2), mem_powChart.2 ⟨mem_powChart.1 hp.1, hp.2⟩⟩
    · refine (iff_of_eq (congrArg IsUnit (hF y J hJ))).trans ?_
      rw [IsUnit.mul_iff, isUnit_pow_iff (by omega)]
      exact and_congr (mem_nonzeroLocus_iff_isUnit u (k := (fun _ => (J PUnit.unit).1, (J PUnit.unit).2))
        (le J hJ)).symm (mem_nonzeroLocus_iff_isUnit σ (le J hJ).2).symm

theorem exists_isAmpleLB_tw [CompactSpace Y] [QuasiSeparatedSpace Y] (hL : L.IsLB) (hG : G.IsLB)
    (h : ∀ y : Y, ∃ (σ : G.Sec) (V : Y.Opens), V = nonzeroLocus σ ∧ y ∈ V ∧ IsAmpleLB (L.pull V.ι)) :
    ∃ c : ℕ, IsAmpleLB (tw L G (c : ℤ)) := by
  have loc : ∀ y : Y, ∃ (m k : ℕ) (u : (tw (lbPow L m) G (k : ℤ)).Sec) (σ : G.Sec), 1 ≤ m ∧
      y ∈ nonzeroLocus u ⊓ nonzeroLocus σ ∧ IsAffineOpen (nonzeroLocus u ⊓ nonzeroLocus σ) := fun y => by
    obtain ⟨σ, V, hV, hy, hA⟩ := h y
    obtain ⟨m, hm, τ, hτ, ha⟩ := hA.exists_affine ⟨y, hy⟩
    obtain ⟨r, hr⟩ := exists_sec_nonzeroLocus_eq_of_lbIso (LB.isLB_pull (isLB_lbPow hL m) V.ι)
      (isLB_lbPow hA.isLB m) (lbIso_lbPow_pull hL V.ι m).symm τ
    obtain ⟨k, u, hu⟩ := exists_sec_tw_locus (isLB_lbPow hL m) hG σ V hV r
    have e := hu.trans hr
    refine ⟨m, k, u, σ, hm, ⟨e.ge hτ, hV.le hy⟩, ?_⟩
    have h₁ := ha.image_of_isOpenImmersion V.ι
    rwa [← e, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_comm, hV] at h₁
  choose m k u σ hm hy ha using loc
  obtain ⟨T, hT⟩ := exists_finset_iSup_eq_top (fun y => nonzeroLocus (u y) ⊓ nonzeroLocus (σ y)) hy
  refine ⟨T.sup k + 1, isLB_tw hL hG _, inferInstance, fun x => ?_⟩
  obtain ⟨y, hx⟩ := Opens.mem_iSup.1 (hT.ge (Set.mem_univ x))
  have h₁ : k y ≤ T.sup k := Finset.le_sup y.2
  have h₂ : T.sup k + 1 ≤ (T.sup k + 1) * m y := Nat.le_mul_of_pos_right _ (hm y)
  obtain ⟨w, hw⟩ := exists_sec_pow_tw (c := T.sup k + 1) (e := (T.sup k + 1) * m y - k y) (by omega) (by omega)
    (u y) (σ y)
  exact ⟨m y, hm y, w, hw.ge hx, hw ▸ ha y⟩

theorem isProper_morphismRestrict {S : Scheme.{0}} (A : Over S) {B : LB A.left} (h : RelAmple A B) {U : S.Opens}
    (hU : IsAffineOpen U) : IsProper (A.hom ∣_ U) := by
  obtain ⟨N, -, K, s, H⟩ := h U hU
  have h₁ := isProper_of_veryAmpleBy
    ((ProjSpace.veryAmpleBy_comp_iff (R := Γ(S, U)) (A.hom ∣_ U) hU.isoSpec.hom s).2 H)
  exact (MorphismProperty.cancel_right_of_respectsIso @IsProper _ _).1 h₁

theorem isProper_and_exists_isAmpleLB {S : Scheme.{0}} (A : Over S) {B : LB A.left} (hB : B.IsLB)
    (h : RelAmple A B) {H : LB S} (hH : IsAmpleLB H) : IsProper A.hom ∧ ∃ N : LB A.left, IsAmpleLB N := by
  obtain ⟨n, -, c, s, hs, ha⟩ := hH.exists_cover
  have hp : IsProper A.hom := IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsProper) _ hs
    fun i => isProper_morphismRestrict A h (ha i)
  have := hH.compactSpace
  have := hH.quasiSeparatedSpace
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have : QuasiSeparatedSpace A.left := quasiSeparatedSpace_of_quasiSeparated A.hom
  obtain ⟨d, hd⟩ := exists_isAmpleLB_tw hB (LB.isLB_pull (isLB_lbPow hH.isLB n) A.hom) fun y => by
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hs.ge (Set.mem_univ (A.hom y)))
    exact ⟨secPull (s i) A.hom, _, (nonzeroLocus_secPull _ _).symm, hi, isAmpleLB_of_relAmple A hB h _ (ha i)⟩
  exact ⟨hp, _, hd⟩

theorem isQProjOver_of_relAmple : ∀ (K : Type) [Field K] (X : Scheme.{0}) (s : X ⟶ Sp K) (A : Over X) (L : LB A.left), IsQProjOver s → L.IsLB → Out.RelAmple A L → IsQProjOver (A.hom ≫ s) := by
  rintro K _ X s A L ⟨N, i, _, _, rfl⟩ hL hA
  obtain ⟨_, B, hB⟩ := isProper_and_exists_isAmpleLB A hL hA ((isAmple_projective_O_one K N).pull_of_isImmersion i)
  have := isProper_str K N
  exact hB.isQProjOver _

end GlobalTheory.RelAmpleQProj
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

theorem fixes_iff_fixes_image {X Y T : Scheme.{0}} (p : Y ⟶ X) (r : X ⟶ X) (q : Y ⟶ Y) (y : T ⟶ Y)
    (w : q ≫ p = p ≫ r)
    (h : (y ≫ p) ≫ r = y ≫ p → pullback.fst p (y ≫ p) ≫ q = pullback.fst p (y ≫ p)) :
    y ≫ q = y ↔ (y ≫ p) ≫ r = y ≫ p := by
  refine ⟨fun hy => ?_, fun hy => ?_⟩
  · rw [Category.assoc, ← w, ← Category.assoc, hy]
  · have := pullback.lift y (𝟙 _) (Category.id_comp _).symm ≫= h hy
    rwa [pullback.lift_fst_assoc, pullback.lift_fst] at this

theorem exists_sab_descent_of_tame_quotient :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Γ : Type) [Group Γ] [Finite Γ] (R : Type) [CommRing R] (X X' : Scheme.{0}) [IsLocallyNoetherian X'] (ρ : Γ →* Aut X) (π : X ⟶ X') (t : SAB H X) (s : X ⟶ Sp R) (τ : Γ →* Aut t.G.left) (mu : ∀ g, SABMap t t (ρ g).asIso.hom), (IsAffineHom π ∧ (∀ g, (ρ g).asIso.hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → IsFinite π → IsQProjOver (t.G.hom ≫ s) → (IsReduced X ∧ genericPoints X ⊆ abLocus t.G) → (∀ g, (mu g).φ = (τ g).asIso.hom) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X), (Nat.card {g // x ≫ (ρ g).asIso.hom = x} : k) ≠ 0) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) g, x ≫ (ρ g).asIso.hom = x → pullback.fst t.G.hom x ≫ (τ g).asIso.hom = pullback.fst t.G.hom x) → ∃ (t' : SAB H X') (ν : SABMap t t' π), (∀ g, (τ g).asIso.hom ≫ ν.φ = ν.φ) ∧ (Good t → PushInvertible t.G t.PP.L → Good t') := by
  intro E _ _ _ H Γ _ _ R _ X X' _ ρ π t s τ mu hQ hfin hqp hga hmu htame hfib
  have hsemi := t.semi
  have hcart (g : Γ) : IsGrpPullback t.G t.G (ρ g).asIso.hom (τ g).asIso.hom := hmu g ▸ (mu g).cart
  have hw (g : Γ) : (τ g).asIso.hom ≫ t.G.hom = t.G.hom ≫ (ρ g).asIso.hom := (hcart g).1.w
  have hact (g : Γ) (c) : (t.act.act c).left ≫ (τ g).asIso.hom = (τ g).asIso.hom ≫ (t.act.act c).left :=
    hmu g ▸ (mu g).act c
  have he (g : Γ) : eSec t.G ≫ (τ g).asIso.hom = (ρ g).asIso.hom ≫ eSec t.G := by
    have := (mu g).cm.e_comm
    rw [(mu g).base] at this
    rw [← hmu g]
    exact this
  have hL (g : Γ) : LBIso t.PP.L (t.PP.L.pull (τ g).asIso.hom) := by
    obtain ⟨w, hw, -⟩ := (mu g).lin
    rw [← hmu g]
    exact ⟨w, hw⟩
  have hsec : eSec t.G ≫ t.G.hom = 𝟙 X := Over.w (η[t.G])
  have hgi : GeometricallyIntegral t.G.hom :=
    forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hsemi.smooth hsemi.geomConnected
  obtain ⟨-, hsurj, -⟩ := quotient_isIntegral_surjective_orbits Γ X X' ρ π hQ
  obtain ⟨G', φ, hpb, hsm, hinv⟩ :=
    exists_smooth_descent_of_tame_quotient Γ R X X' ρ π t.G s τ hQ hfin hqp hsemi.smooth hw htame hfib
  obtain ⟨_, _, a', hgp, ha⟩ := quotient_descend_grpObj Γ (𝓞 E) X X' ρ π t.G G' φ τ t.act hQ hpb inferInstance
    fun g => ⟨hinv g, hcart g, hact g⟩
  have hsemi' := (SemiAbelianDescent.main X X' π t.G G' φ inferInstance hsurj hgp hsm hsemi).1
  obtain ⟨u, hu₁, hu₂, hu₃⟩ := RigidLinearisation.exists_linearisation Γ X t.G (eSec t.G) ρ τ t.PP.L hsec hgi
    (eq_one_of_appLE_section_eq_one X t.G (eSec t.G) hsec hsemi.smooth hgi hga) (fun g => ⟨hw g, he g⟩) hfib
    t.PP.isLB ⟨t.PP.rig, t.PP.rigGen⟩ hL
  have hQ' := (quotient_flat_baseChange Γ X X' _ _ ρ π φ t.G.hom G'.hom hQ hpb inferInstance).2 τ
    fun g => ⟨hinv g, hw g⟩
  obtain ⟨L', hL', hiso⟩ := LinDescent.exists_descent_of_tame Γ _ _ τ φ t.PP.L hQ' (fun k _ _ y => by
    convert htame k (y ≫ t.G.hom) using 2
    exact Nat.card_congr (Equiv.subtypeEquivRight fun g =>
      fixes_iff_fixes_image t.G.hom _ _ y (hw g) (hfib k _ g))) t.PP.isLB u hu₁ hu₂ hu₃
  obtain ⟨t', ν, e, hν⟩ := T.exists_semiAbelianTriple_of_finiteQuotient E H Γ X X' ρ π t G' a' φ L' hQ hga hsemi' hgp ha hL' hiso
  have hinv' (g : Γ) : (τ g).asIso.hom ≫ ν.φ = ν.φ := by
    rw [← cancel_mono e.hom.left, Category.assoc, hν, hinv]
  refine ⟨t', ν, hinv', fun ⟨h₁, h₂, _⟩ hP => ⟨?_, ?_, ?_⟩⟩
  · exact (SemiAbelianDescent.main X X' π t.G t'.G ν.φ inferInstance hsurj ν.cart t'.semi.smooth hsemi).2 h₁
  · exact splitFibres_descend_of_tame_quotient Γ X X' ρ π t.G t'.G ν.φ hQ htame ν.cart h₂
  · obtain ⟨w, hw', -⟩ := ν.lin
    have := t'.semi.smooth
    exact exists_secOn_nonvanishing_of_tame_quotient Γ X X' ρ π t.G t'.G ν.φ τ t.PP.L t'.PP.L hQ ν.cart.1
      inferInstance (fun g => ⟨hinv' g, hw g⟩) htame hfib t.PP.isLB t'.PP.isLB ⟨w, hw'⟩ hP

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.SiegelDataPull

open GlobalTheory.SiegelPullComp

theorem isSquare_comp {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} {φ : G'.left ⟶ G.left}
    {ψ : G''.left ⟶ G'.left} {φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} {ψ₂ : (G'' ⊗ G'').left ⟶ (G' ⊗ G').left}
    (h' : Geo.Tor.IsSquare ψ ψ₂) (h : Geo.Tor.IsSquare φ φ₂) : Geo.Tor.IsSquare (ψ ≫ φ) (ψ₂ ≫ φ₂) := by
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, h.1, ← Category.assoc, h'.1, Category.assoc]
  · rw [Category.assoc, h.2, ← Category.assoc, h'.2, Category.assoc]

theorem siegData_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (O : Type) [CommRing O] (T T' : Scheme.{0}) (sT : T ⟶ Sp O) (f : T' ⟶ T) (t : SAB H T) (t' : SAB H T') (ν : SABMap t' t f) (lev : D.La → (𝟙_ (Over T) ⟶ t.G)) (lev' : D.La → (𝟙_ (Over T') ⟶ t'.G)) (g p N : ℕ) (Ag : SiegelFamily g p N) (z : ZP p N →+* O) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La) (w : T ⟶ pullback Ag.s (spMap z)), (∀ x, (lev' x).left ≫ ν.φ = f ≫ (lev x).left) → SiegData sT t lev Ag z bas w → SiegData (f ≫ sT) t' lev' Ag z bas (f ≫ w) := by
  intro E _ _ _ H D O _ T T' sT f t t' ν lev lev' g p N Ag z bas w hlev hw
  obtain ⟨o, φ, φ₂, hpb, hsq, hiso, hlv, hsnd, hSPB⟩ := hw
  obtain ⟨⟨o', ho'⟩, -⟩ := GlobalTheory.siegPre_pullback _ _ _ _ _ _ _ ((f ≫ sT) ≫ spMap z) f o
    (Category.assoc f sT (spMap z)).symm
  have hpbo := ho'
  obtain ⟨φ₁, φ₁₂, hpb₁, hsq₁, hiso₁, hlv₁⟩ := hpbo
  have hν : IsGrpPullback t'.G t.G f ν.φ := ν.cart
  have hc : IsGrpPullback o'.A t.G f (φ₁ ≫ φ) := (hpb₁.comp hpb).congr (Category.comp_id f) rfl
  obtain ⟨e, he, hel⟩ := grpPullback_iso hc hν
  haveI := he
  have hpb' : IsGrpPullback o'.A t'.G (𝟙 T') e.hom.left := isGrpPullback_of_iso e
  have hsq' := GlobalTheory.LamPull.exists_isSquare hpb'.1.w
  have hν₂ := GlobalTheory.LamPull.exists_isSquare hν.1.w
  have hΛ : (abelian₂ t.G t.PP.L).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ t.PP.isLB _ _
  have hΛ' : (abelian₂ t'.G t'.PP.L).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ t'.PP.isLB _ _
  have sA := isSquare_comp hsq₁ hsq
  have sB := isSquare_comp hsq' hν₂
  rw [hel] at sB
  have key := GlobalTheory.LamPull.isSquare_unique sA sB
  refine ⟨o', e.hom.left, _, hpb', hsq', ?_, ?_, ?_, ?_⟩
  · have h2 := GlobalTheory.SiegelPullComp.iso_pull φ₁₂ hiso
    have h3 := GlobalTheory.SiegelPullComp.iso_pull_pull hΛ φ₂ φ₁₂
    rw [key] at h3
    have h4 := (GlobalTheory.SiegelPullComp.iso_pull_pull hΛ (lift (pushPt hν.1.w (fst t'.G t'.G))
      (pushPt hν.1.w (snd t'.G t'.G))).left (lift (pushPt hpb'.1.w (fst o'.A o'.A))
      (pushPt hpb'.1.w (snd o'.A o'.A))).left).symm
    have h5 := GlobalTheory.SiegelPullComp.iso_pull (lift (pushPt hpb'.1.w (fst o'.A o'.A))
      (pushPt hpb'.1.w (snd o'.A o'.A))).left ((GlobalTheory.LamPull.lam_pull E H T T' t t' f).2 ν _ hν₂).symm
    have l0 := o'.isLB
    have l1 := pull_isLB o.isLB φ₁₂
    have l2 := pull_isLB (pull_isLB hΛ φ₂) φ₁₂
    refine LBIso.trans l0 l1 (pull_isLB hΛ' _) hiso₁ ?_
    refine LBIso.trans l1 l2 (pull_isLB hΛ' _) h2 ?_
    refine LBIso.trans l2 (pull_isLB hΛ _) (pull_isLB hΛ' _) h3 ?_
    refine LBIso.trans (pull_isLB hΛ _) (pull_isLB (pull_isLB hΛ _) _) (pull_isLB hΛ' _) h4 h5
  · intro u
    apply hν.1.hom_ext
    · rw [Category.assoc, hel, ← Category.assoc, hlv₁ u, Category.assoc, hlv u, hlev]
    · rw [Category.assoc, Over.w e.hom, Over.w (o'.lev u), Over.w (lev' (bas u))]
  · rw [Category.assoc, hsnd]
  · rw [Category.assoc f w (pullback.fst Ag.s (spMap z))]
    exact GlobalTheory.SiegelPullComp.pb_comp hSPB ho'

end GlobalTheory.SiegelDataPull

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
theorem _root_.GlobalTheory.T.exists_model_baseChange_overring : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (O' : Type) [CommRing O'] (β' : O' →+* F) (b : O →+* O') (C : Cpt c t β) (ν : SABMap t t (𝟙 U)), ν.φ = 𝟙 _ → IsDedFrac β → IsDedFrac β' → β'.comp b = β → ∃ (C' : Cpt c t β') (a : C'.Above C b (𝟙 U) ν), IsIso (pullback.lift a.π C'.s a.π_over) := by
  first | exact @GlobalTheory.Models.Cpt.exists_above_isIso_of_overring | exact GlobalTheory.Models.Cpt.exists_above_isIso_of_overring | (intros; apply GlobalTheory.Models.Cpt.exists_above_isIso_of_overring <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.exists_symmetric_biadditive_bundle_eighthPower : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (S : Scheme.{0}) (G A : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A] (pr : Fin 8 → (G ⟶ A)) (L : LB G.left) (ρ : Matrix (Fin 8) (Fin 8) ℤ → (G ⟶ G)), IsE8 W → (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u) → L.IsLB → (∃ t : LB.Gen (Theta G L), t.IsGen) → (∀ m u, ρ m ≫ pr u = (List.ofFn fun v => pr v ^ m u v).prod) → (∀ m m', m.transpose * (W + W.transpose) = (W + W.transpose) * m' → LBIso (cubeLB G ![fst G G ≫ ρ m, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ ρ m'] L)) → (∀ m, (W + W.transpose) * m = W → LBIso L (cubeLB G ![𝟙 G, ρ m] L)) → ∃ P : LB (G2 A).left, P.IsLB ∧ (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) ∧ (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) ∧ LBIso P (P.pull (lift (snd A A) (fst A A)).left) ∧ (∀ (T : Over S) (x x' y : T ⟶ A), (∃ t : (LB.LinComb P (K := Fin 3) ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]).Gen, t.IsGen) ∧ ∃ t : (LB.LinComb P (K := Fin 3) ![(lift y (x * x')).left, (lift y x).left, (lift y x').left] ![1, -1, -1]).Gen, t.IsGen) ∧ LBIso L (LB.LinComb P (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) := by
  first | exact @GlobalTheory.EighthPower.main | exact GlobalTheory.EighthPower.main | (intros; apply GlobalTheory.EighthPower.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV
theorem _root_.GlobalTheory.T.isFinite_and_surjective_of_formIs' : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left) (s : P.A ⟶ P.A), M.IsLB → Out.RelAmple P.A M → FormIs P M s → IsFinite s.left ∧ Surjective s.left := by
  first | exact @GlobalTheory.FormFinite.isFinite_and_surjective_of_formIs | exact GlobalTheory.FormFinite.isFinite_and_surjective_of_formIs | (intros; apply GlobalTheory.FormFinite.isFinite_and_surjective_of_formIs <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.weilPairing_diagonal_bundle_of_eighthPower_form : Out.GlobalFnsSt → ∀ (h k : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (S : Scheme.{0}) (G A : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A] (pr : Fin 8 → (G ⟶ A)) (L : LB G.left) (P : LB (G2 A).left) (K : Type) [Field K] (p : Sp K ⟶ S) (lev : (Fin h ⊕ Fin h → ℤ) → (Over.mk p ⟶ A)) (c : Γ((Over.mk p).left, ⊤)ˣ), IsE8 W → IsAbelianScheme G → IsAbelianScheme A → (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u) → L.IsLB → P.IsLB → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → (∀ (T : Over S) (x x' y : T ⟶ A), (∃ t : (LB.LinComb P (K := Fin 3) ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]).Gen, t.IsGen) ∧ ∃ t : (LB.LinComb P (K := Fin 3) ![(lift y (x * x')).left, (lift y x).left, (lift y x').left] ![1, -1, -1]).Gen, t.IsGen) → LBIso L (LB.LinComb P (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) → (∀ x y, lev (x + y) = lev x * lev y) → (∀ x, lev x ^ k = 1) → (∀ (X Y : Fin 8 → (Fin h ⊕ Fin h → ℤ)) (y y' : Over.mk p ⟶ G), (∀ u, y ≫ pr u = lev (X u)) → (∀ u, y' ≫ pr u = lev (Y u)) → Out.WeilIs G L k y y' (c ^ ∑ u, ∑ v, (W + W.transpose) u v * omegaStd (X u) (Y v))) → ∀ x y, Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) k (lev x) (lev y) (c ^ (2 * omegaStd x y)) := by
  first | exact @GlobalTheory.WeilDown.weilIs_diag | exact GlobalTheory.WeilDown.weilIs_diag | (intros; apply GlobalTheory.WeilDown.weilIs_diag <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.pelStructure_descends_field_extension : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g k : ℕ) (J : Type) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (o : Type) [CommRing o] (b : TBase o k) (ρ : o) (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (β₀ : o →+* K₀) (s : Sp K ⟶ Sp o) (t₀ : TObj g k J b (spMap β₀)) (t : TObj g k J b s) (τ : SAB H (Sp K)), Subring.closure (Set.range a) = ⊤ → s = spMap i ≫ spMap β₀ → TMap t t₀ (spMap i) → IsPEL D a bas ρ t τ → ∃ τ₀ : SAB H (Sp K₀), IsPEL D a bas ρ t₀ τ₀ := by
  first | exact @GlobalTheory.PELDesc.isPEL_descends | exact GlobalTheory.PELDesc.isPEL_descends | (intros; apply GlobalTheory.PELDesc.isPEL_descends <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS

theorem torsion_section_const : Out.Laws → ∀ (P₀ : Out.PolAV (Sp ℂ)), ∀ (A' : Over (Sp (DualNumber ℂ))) [GrpObj A'] (ρ : A'.left ⟶ P₀.A.left) (j : P₀.A.left ⟶ A'.left), IsConst A' P₀.A ρ j → ∀ (k : ℕ) (y : Out.baseOver (Sp (DualNumber ℂ)) ⟶ A') (y₀ : Out.baseOver (Sp ℂ) ⟶ P₀.A), k ≠ 0 → y ^ k = 1 → y₀ ^ k = 1 → (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ y.left = y₀.left ≫ j → y.left ≫ ρ = (spMap (algebraMap ℂ (DualNumber ℂ))) ≫ y₀.left := by
  intro _ P₀ A' _ ρ j hc k y y₀ hk hy hy₀ hyj
  letI := P₀.isAb.comm
  have hu : IsUnit ((k : ℕ) : Γ(Sp ℂ, ⊤)) := by
    let e : Γ(Sp ℂ, ⊤) ≃+* ℂ := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv
    refine (MulEquiv.isUnit_map e.toMulEquiv).mp ?_
    have he : e.toMulEquiv (k : Γ(Sp ℂ, ⊤)) = (k : ℂ) := map_natCast e k
    rw [he]
    exact (Nat.cast_ne_zero.mpr hk).isUnit
  exact GlobalTheory.ConstTheta.torsion_const hc.1 hc.2.2 hu y y₀ hy hy₀ hyj.symm

end GlobalTheory.KS
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.torsion_sectionCoords_theta_times_roots : Out.Laws → Out.Laws2 → ∀ (g m N' : ℕ), Odd N' → m ^ 2 ∣ N' → ∃ (e : Ix g (N' ^ 2) → Ix g (N' ^ 2) → ℕ) (idx : Ix g (N' ^ 2) → Ix g (N' ^ 2) → Ix g (N' ^ 2)), ∀ (o : Type) [CommRing o] (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (R : Type) [CommRing R] (β : o →+* R) (x : Sp R ⟶ S) (v : Ix g (N' ^ 2) → R) σ, x ≫ s = spMap β → t.HasTh x v → Ideal.span (Set.range v) = ⊤ → t.Emb m (Over.mk x) σ → ∀ h (y : Sp R ⟶ (Over.mk x ⊗ t.A).left), y = (lift (𝟙 (Over.mk x)) (((Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ t.lab h) ^ N')).left → ∀ p : Sp R, ∃ (R' : Type) (_ : CommRing R') (φ : R →+* R'), IsOpenImmersion (spMap φ) ∧ p ∈ Set.range (spMap φ) ∧ SecCoord _ σ (spMap φ ≫ y) (fun a => φ (β (b.ζ ^ e a h : oˣ) * v (idx a h))) := by
  first | exact @GlobalTheory.torsion_secCoord | exact GlobalTheory.torsion_secCoord | (intros; apply GlobalTheory.torsion_secCoord <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem IsAmpleLB.of_pow_div_generated {X : Scheme.{0}} {L N : LB X} (hL : IsAmpleLB L) (hN : N.IsLB) {m : ℕ}
    (hm : 1 ≤ m) {J : Type} (u : J → (lbPow (LB.div N L) m).Sec) (hu : ⨆ i, Out.nonzeroLocus (u i) = ⊤) :
    IsAmpleLB N := by
  refine ⟨hN, hL.compactSpace, fun x => ?_⟩
  obtain ⟨n, hn, s, hs, ha⟩ := hL.exists_affine x
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hu.ge (Set.mem_univ x))
  have hD := LB.isLB_div hN hL.isLB
  obtain ⟨v, hv⟩ := exists_sec_pow_nonzeroLocus_eq_inf hL.isLB hD hN (lbIso_refl hD) (secPow s m)
    (secCast (Nat.mul_comm m n) (secPow (u i) n))
  rw [nonzeroLocus_secCast, nonzeroLocus_secPow _ hn, nonzeroLocus_secPow _ hm] at hv
  exact ⟨n * m, Nat.mul_pos hn hm, v, hv.ge ⟨hi, hs⟩,
    hv ▸ isAffineOpen_nonzeroLocus_inf (isLB_lbPow hD m) (u i) ha⟩

theorem relAmple_of_cube_div_generated : ∀ (K : Type) [Field K] (A : Over (Sp K)) (L M : LB A.left) (a r : ℕ) (u : Fin r → (lbPow (LB.div (lbPow M a) L) 3).Sec), IsProper A.hom → L.IsLB → M.IsLB → 1 ≤ a → Out.RelAmple A L → ⨆ i, Out.nonzeroLocus (u i) = ⊤ → Out.RelAmple A M := by
  intro K _ A L M a r u hA hL hM ha hamp hu
  have h₁ := (relAmple_iff_isAmpleLB_of_isAffine A hL).1 hamp
  exact (relAmple_iff_isAmpleLB_of_isAffine A hM).2 ((isAmpleLB_pow_iff hM ha).1
    (h₁.of_pow_div_generated (isLB_lbPow hM a) (by norm_num) u hu))

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.semistableReductionSplit_of_padic : GlobalTheory.Published.SemistableReductionSt → GlobalTheory.SS.SemistablePol := by
  first | exact @GlobalTheory.SS.semistablePol_of_padic | exact GlobalTheory.SS.semistablePol_of_padic | (intros; apply GlobalTheory.SS.semistablePol_of_padic <;> assumption)
end
