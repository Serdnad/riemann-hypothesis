module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFrameReorderingLevelData
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle232
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle234
public import Formalism.RealPlaceAnalysis.Bundle001
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.Real.Pi.Irrational
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Definitions.Foundations.ContinuousOfMemCcSmooth
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule
public import Formalism.PeriodIntegrals.Bundle020
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsAdmissibleSubOfFiniteDimensional
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_frame_reordering_levelData : ∀ {D : D7} {T : Type} (Lc : LevCh D T) (P P' : LevelP Lc.Pg D.R.r ℂ) (π : Equiv.Perm (Fin D.R.r)), (∀ g, g ∈ P.H ↔ reord π g ∈ P'.H) → (∀ g hg hg', P.chi ⟨g, hg⟩ = P'.chi ⟨reord π g, hg'⟩) → ∀ β₃ : GL (Fin (Yc D 0).rank) (EAf D), IsFrame β₃ (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∃ β₂ : GL (Fin (Yc D 0).rank) (EAf D), IsFrame β₂ (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) ∧ ∀ κ : GA D (Yc D 0), (κ ∈ levS (Yc D 0) β₂ (Lc.dat0 P) ↔ κ ∈ levS (Yc D 0) β₃ (Lc.dat0 P')) ∧ levChi (Yc D 0) β₂ (Lc.dat0 P) κ = levChi (Yc D 0) β₃ (Lc.dat0 P') κ := by
  first | exact @GlobalTheory.SeeConjReord.exists_frame_reord | exact GlobalTheory.SeeConjReord.exists_frame_reord | (intros; apply GlobalTheory.SeeConjReord.exists_frame_reord <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.levS_iff_and_levChi_eq_of_redFn_eq : ∀ {D : D7} (V : HSp D) (β β' : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (L : LevDat D.host.E ℂ V.rank), IsFrame β Λ → IsFrame β' Λ → (∀ PP ∈ L.Pg, ∀ x, redFn β PP x = redFn β' PP x) → (∀ PP ∈ L.Q, ∀ x, redFn β PP x = redFn β' PP x) → ∀ κ : GA D V, (κ ∈ levS V β L ↔ κ ∈ levS V β' L) ∧ levChi V β L κ = levChi V β' L κ := by
  first | exact @GlobalTheory.levS_levChi_of_frames | exact GlobalTheory.levS_levChi_of_frames | (intros; apply GlobalTheory.levS_levChi_of_frames <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.levelSubgroup_conj_finite_moves_frame : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (L : LevDat D.host.E ℂ V.rank) (t : GA D V), t ∈ GfC V → ∀ k : GA D V, (k ∈ levS V β L ↔ t * k * t⁻¹ ∈ levS V (finE V t * β) L) ∧ levChi V (finE V t * β) L (t * k * t⁻¹) = levChi V β L k := by
  first | exact @GlobalTheory.FrameConj.levS_conj_frame | exact GlobalTheory.FrameConj.levS_conj_frame | (intros; apply GlobalTheory.FrameConj.levS_conj_frame <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.finite_group_lifts_to_parahoric_level : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (Λ : Submodule (NumberField.RingOfIntegers D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsBaseFrame V β Λ N → L.Q = ∅ → (∀ PP ∈ L.Pg, ∀ PP' ∈ L.Pg, ¬ IsConjPl PP PP') → LiftsExist V β L := by
  first | exact @GlobalTheory.FiniteGroupLifts.liftsExist_of_twist_empty | exact GlobalTheory.FiniteGroupLifts.liftsExist_of_twist_empty | (intros; apply GlobalTheory.FiniteGroupLifts.liftsExist_of_twist_empty <;> assumption)
end

section

open Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.FlagMeas GlobalTheory.RealInd

noncomputable section

namespace GlobalTheory.SplitTorus

variable {n : ℕ} (ε : Fin n → Bool)

def bJ (u y : Fin n → ℂ) : ℂ := star u ⬝ᵥ (Jm ε *ᵥ y)

variable {ε}

theorem coord {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) (b : Fin n) (y : Fin n → ℂ) :
    bJ ε (P *ᵥ Pi.single b 1) y = ((Pᴴ * Jm ε * P) *ᵥ (P⁻¹ *ᵥ y)) b := by
  have hPP : P * P⁻¹ = 1 := mul_nonsing_inv P ((isUnit_iff_isUnit_det P).1 hP)
  conv_lhs => rw [show y = P *ᵥ (P⁻¹ *ᵥ y) by rw [mulVec_mulVec, hPP, one_mulVec]]
  rw [bJ, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
  simp [Pi.star_def, Pi.single_apply, dotProduct]

end GlobalTheory.SplitTorus

namespace GlobalTheory.SplitTorus

variable {n : ℕ} {ε : Fin n → Bool}

end GlobalTheory.SplitTorus

namespace GlobalTheory.SplitTorus

variable {n : ℕ} {ε : Fin n → Bool}

end GlobalTheory.SplitTorus

namespace GlobalTheory.SplitTorus

variable {n : ℕ} {ε : Fin n → Bool}

end GlobalTheory.SplitTorus

namespace GlobalTheory.SplitTorus

variable {n : ℕ} {ε : Fin n → Bool}

section
variable {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) {p q : Fin n} (hpq : p ≠ q)
    (hG : ∀ a b, (a = p ∨ a = q ∨ b = p ∨ b = q) →
      (Pᴴ * Jm ε * P) a b = if (a = p ∧ b = q) ∨ (a = q ∧ b = p) then 1 else 0)
include hP hpq hG

end

end GlobalTheory.SplitTorus

namespace GlobalTheory.SplitTorus

variable {n : ℕ} {ε : Fin n → Bool}

section
variable {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) {p q : Fin n} (hpq : p ≠ q)
    (hG : ∀ a b, (a = p ∨ a = q ∨ b = p ∨ b = q) →
      (Pᴴ * Jm ε * P) a b = if (a = p ∧ b = q) ∨ (a = q ∧ b = p) then 1 else 0)
include hP hpq hG

end

end GlobalTheory.SplitTorus

namespace GlobalTheory.SplitTorus

variable {n : ℕ} {ε : Fin n → Bool}

end GlobalTheory.SplitTorus

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
end
end

section

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace

namespace GlobalTheory.KStableGraph

theorem exists_partner {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {S S' U : Submodule ℂ H}
    (hS : Formalism.MainNotions.S.IsKStableOn ε ρ S) (hS' : Formalism.MainNotions.S.IsKStableOn ε ρ S')
    (hU : Formalism.MainNotions.S.IsKStableOn ε ρ U)
    (irr : ∀ T : Submodule ℂ H, T ≤ S → Formalism.MainNotions.S.IsKStableOn ε ρ T → T = ⊥ ∨ T = S)
    (hle : U ≤ S ⊔ S') (hUS' : U ⊓ S' = ⊥) (hU0 : U ≠ ⊥) :
    ∀ s ∈ S, ∃ s' ∈ S', s + s' ∈ U := by
  have hT : Formalism.MainNotions.S.IsKStableOn ε ρ (S ⊓ (U ⊔ S')) := by
    intro g hg v hv
    obtain ⟨hvS, hvU⟩ := Submodule.mem_inf.mp hv
    obtain ⟨u, hu, t, ht, rfl⟩ := Submodule.mem_sup.mp hvU
    refine Submodule.mem_inf.mpr ⟨hS g hg _ hvS, ?_⟩
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (hU g hg u hu) (hS' g hg t ht)
  rcases irr _ inf_le_left hT with h | h
  · exfalso
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
    obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.mp (hle hu)
    have hsT : s ∈ S ⊓ (U ⊔ S') := by
      refine Submodule.mem_inf.mpr ⟨hs, ?_⟩
      have : s = u - t := by rw [← hst]; abel
      rw [this]
      exact Submodule.sub_mem_sup hu ht
    rw [h] at hsT
    have hs0 : s = 0 := (Submodule.mem_bot ℂ).mp hsT
    have hut : u = t := by rw [← hst, hs0, zero_add]
    have : u ∈ U ⊓ S' := Submodule.mem_inf.mpr ⟨hu, hut ▸ ht⟩
    rw [hUS'] at this
    exact hu0 ((Submodule.mem_bot ℂ).mp this)
  · intro s hs
    have hs' : s ∈ S ⊓ (U ⊔ S') := h.symm ▸ hs
    obtain ⟨u, hu, t, ht, hut⟩ := Submodule.mem_sup.mp (Submodule.mem_inf.mp hs').2
    refine ⟨-t, S'.neg_mem ht, ?_⟩
    have : s + -t = u := by rw [← hut]; abel
    rw [this]; exact hu

theorem exists_kMap_onto : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S S' U : Submodule ℂ H), Formalism.MainNotions.S.IsKStableOn ε ρ S → Formalism.MainNotions.S.IsKStableOn ε ρ S' → Formalism.MainNotions.S.IsKStableOn ε ρ U → (∀ T : Submodule ℂ H, T ≤ S → Formalism.MainNotions.S.IsKStableOn ε ρ T → T = ⊥ ∨ T = S) → (∀ T : Submodule ℂ H, T ≤ S' → Formalism.MainNotions.S.IsKStableOn ε ρ T → T = ⊥ ∨ T = S') → S ⊓ S' = ⊥ → U ≤ S ⊔ S' → U ⊓ S = ⊥ → U ⊓ S' = ⊥ → U ≠ ⊥ → ∃ φ : H →ₗ[ℂ] H, (∀ k ∈ Formalism.REAL.Kset ε, ∀ u ∈ S, φ (ρ k u) = ρ k (φ u)) ∧ S.map φ = S' := by
  intro n ε H _ _ ρ S S' U hS hS' hU irrS irrS' hSS' hle hUS hUS' hU0
  have ex := exists_partner hS hS' hU irrS hle hUS' hU0
  have ex' := exists_partner hS' hS hU irrS' (by rwa [sup_comm]) hUS hU0
  have uniq : ∀ s ∈ S, ∀ a ∈ S', ∀ b ∈ S', s + a ∈ U → s + b ∈ U → a = b := by
    intro s _ a ha b hb h1 h2
    have h3 := U.sub_mem h1 h2
    rw [add_sub_add_left_eq_sub] at h3
    have : a - b ∈ U ⊓ S' := Submodule.mem_inf.mpr ⟨h3, S'.sub_mem ha hb⟩
    rw [hUS'] at this
    exact sub_eq_zero.mp ((Submodule.mem_bot ℂ).mp this)
  choose g hg using ex
  let f : S →ₗ[ℂ] S' :=
    { toFun := fun x => ⟨g x x.2, (hg x x.2).1⟩
      map_add' := fun x y => by
        apply Subtype.ext
        show g ((x + y : S) : H) (x + y).2 = g x x.2 + g y y.2
        refine uniq _ (x + y).2 _ (hg _ _).1 _ (S'.add_mem (hg x x.2).1 (hg y y.2).1) (hg _ _).2 ?_
        have := U.add_mem (hg x x.2).2 (hg y y.2).2
        rw [Submodule.coe_add]
        convert this using 1
        abel
      map_smul' := fun c x => by
        apply Subtype.ext
        show g ((c • x : S) : H) (c • x).2 = c • g x x.2
        refine uniq _ (c • x).2 _ (hg _ _).1 _ (S'.smul_mem c (hg x x.2).1) (hg _ _).2 ?_
        have := U.smul_mem c (hg x x.2).2
        rw [Submodule.coe_smul]
        convert this using 1
        rw [smul_add] }
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl S
  let φ : H →ₗ[ℂ] H := S'.subtype ∘ₗ f ∘ₗ S.projectionOnto C hC
  have hφ : ∀ u (hu : u ∈ S), φ u = g u hu := by
    intro u hu
    have := Submodule.linearProjOfIsCompl_apply_left hC ⟨u, hu⟩
    change ((f (S.projectionOnto C hC ((⟨u, hu⟩ : S) : H)) : S') : H) = _
    rw [this]
    rfl
  refine ⟨φ, ?_, ?_⟩
  · intro k hk u hu
    have hku : ρ k u ∈ S := hS k hk u hu
    rw [hφ _ hku, hφ u hu]
    refine uniq _ hku _ (hg _ hku).1 _ (hS' k hk _ (hg u hu).1) (hg _ hku).2 ?_
    rw [← map_add (f := _)]
    exact hU k hk _ (hg u hu).2
  · apply le_antisymm
    · rintro _ ⟨u, hu, rfl⟩
      rw [hφ u hu]
      exact (hg u hu).1
    · intro s' hs'
      obtain ⟨s, hs, hsU⟩ := ex' s' hs'
      refine Submodule.mem_map.mpr ⟨s, hs, ?_⟩
      rw [hφ s hs]
      exact uniq s hs _ (hg s hs).1 s' hs' (hg s hs).2 (by rwa [add_comm])

end GlobalTheory.KStableGraph
end

section

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace

namespace GlobalTheory.TorusWtFin

open Complex

noncomputable abbrev dg {n : ℕ} (θ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))

lemma diag_mem (n : ℕ) (ε : Fin n → Bool) (θ : Fin n → ℝ) : dg θ ∈ Formalism.REAL.Kset ε := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff]
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_one]
    congr 1
    funext i
    simp only [Pi.star_apply, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
    simp [Complex.conj_ofReal]
  · unfold Formalism.REAL.Jm
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    ring

lemma sum_single {n : ℕ} (μ : Fin n → ℝ) (a : Fin n) (c : ℝ) :
    (∑ b, μ b * (Pi.single a c : Fin n → ℝ) b) = μ a * c := by
  simp [Pi.single_apply]

lemma wt_int {n : ℕ} (ε : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) {μ : Fin n → ℝ} {v : H} (hv : v ≠ 0)
    (hw : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) ρ μ v) (a : Fin n) : ∃ k : ℤ, μ a = k := by
  have h1 := hw (Pi.single a (2 * Real.pi)) (diag_mem n ε _)
  have h0 := hw 0 (diag_mem n ε _)
  change ρ (dg _) v = _ at h1 h0
  have hD : dg (Pi.single a (2 * Real.pi) : Fin n → ℝ) = dg (0 : Fin n → ℝ) := by
    unfold dg
    congr 1
    funext b
    by_cases hb : b = a
    · subst hb
      simp only [Pi.single_eq_same, Pi.zero_apply, Complex.ofReal_zero, zero_mul, Complex.exp_zero]
      push_cast
      exact Complex.exp_two_pi_mul_I
    · simp [Pi.single_apply, hb]
  rw [sum_single] at h1
  rw [hD, h0] at h1
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero, one_smul] at h1
  have h2 : (Complex.exp (((μ a * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) - 1) • v = 0 := by
    rw [sub_smul, one_smul, ← h1, sub_self]
  have h3 : Complex.exp (((μ a * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) = 1 := by
    rcases smul_eq_zero.1 h2 with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hv
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.1 h3
  refine ⟨k, ?_⟩
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h4 : ((μ a : ℝ) : ℂ) = (k : ℂ) := by
    have := hk
    push_cast at this
    have hI : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by simp [hpi, Complex.I_ne_zero]
    apply mul_right_cancel₀ hI
    linear_combination this
  exact_mod_cast h4

lemma exp_injOn : Set.InjOn (fun x : ℝ => Complex.exp ((x : ℂ) * Complex.I)) {x | ∃ k : ℤ, x = k} := by
  rintro x ⟨k, rfl⟩ y ⟨k', rfl⟩ h
  simp only at h
  have h1 : Complex.exp ((((k - k' : ℤ) : ℝ) : ℂ) * Complex.I) = 1 := by
    have h' : Complex.exp ((k : ℂ) * Complex.I) = Complex.exp ((k' : ℂ) * Complex.I) := by
      exact_mod_cast h
    push_cast
    rw [sub_mul, Complex.exp_sub, h', div_self (Complex.exp_ne_zero _)]
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 h1
  have hm' : (((k - k' : ℤ) : ℝ) : ℂ) = ((2 * m * Real.pi : ℝ) : ℂ) := by
    push_cast
    apply mul_right_cancel₀ Complex.I_ne_zero
    push_cast at hm
    linear_combination hm
  have hm'' : ((k - k' : ℤ) : ℝ) = ((2 * m : ℤ) : ℝ) * Real.pi := by
    have := Complex.ofReal_injective hm'
    push_cast at this ⊢
    linarith
  by_cases h0 : (2 * m : ℤ) = 0
  · rw [h0] at hm''
    simp only [Int.cast_zero, zero_mul] at hm''
    have : (k - k' : ℤ) = 0 := by exact_mod_cast hm''
    have : k = k' := by omega
    rw [this]
  · exact absurd hm''.symm ((irrational_pi.intCast_mul h0).ne_int _)

theorem finite_weights : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H), FiniteDimensional ℂ S → ∃ F : Finset (Fin n → ℝ), ∀ (μ : Fin n → ℝ) (v : H), v ∈ S → v ≠ 0 → Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) ρ μ v → μ ∈ F := by
  intro n ε H _ _ ρ S hS
  let W : Set (Fin n → ℝ) := {μ | ∃ v ∈ S, v ≠ 0 ∧ Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) ρ μ v}
  suffices hW : W.Finite by
    exact ⟨hW.toFinset, fun μ v hv h0 hw => hW.mem_toFinset.2 ⟨v, hv, h0, hw⟩⟩

  let T : Fin n → Module.End ℂ H := fun a => (ρ (dg (Pi.single a (1 : ℝ)))).toLinearMap
  let C : Fin n → Set ℂ := fun a => {c | ∃ v ∈ S, v ≠ 0 ∧ T a v = c • v}
  have hC : ∀ a, (C a).Finite := by
    intro a
    have hx : ∀ c : C a, ∃ v : S, (v : H) ≠ 0 ∧ T a v = (c : ℂ) • (v : H) := fun c => by
      obtain ⟨v, hvS, hv0, hv⟩ := c.2
      exact ⟨⟨v, hvS⟩, hv0, hv⟩
    choose xs hxs using hx
    have hli : LinearIndependent ℂ (fun c : C a => ((xs c : S) : H)) :=
      (T a).eigenvectors_linearIndependent (C a) (fun c => (xs c : H))
        (fun c => ⟨Module.End.mem_eigenspace_iff.2 (hxs c).2, (hxs c).1⟩)
    have hli' : LinearIndependent ℂ xs := LinearIndependent.of_comp S.subtype hli
    have := hli'.finite
    exact Set.finite_coe_iff.1 this
  let Z : Fin n → Set ℝ := fun a => {x | (∃ k : ℤ, x = k) ∧ Complex.exp ((x : ℂ) * Complex.I) ∈ C a}
  have hZ : ∀ a, (Z a).Finite := by
    intro a
    refine Set.Finite.of_finite_image ((hC a).subset ?_) (exp_injOn.mono fun x hx => hx.1)
    rintro _ ⟨x, hx, rfl⟩
    exact hx.2
  refine (Set.Finite.pi hZ).subset ?_
  rintro μ ⟨v, hvS, hv0, hw⟩ a _
  refine ⟨wt_int ε ρ hv0 hw a, v, hvS, hv0, ?_⟩
  have h := hw (Pi.single a (1 : ℝ)) (diag_mem n ε _)
  rw [sum_single, mul_one] at h
  exact h

end GlobalTheory.TorusWtFin
end
