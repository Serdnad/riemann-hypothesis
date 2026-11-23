module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle214
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle144
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle173
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle163
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle223
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle225
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle229
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle143
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualOrthAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle211
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH

@[expose] public section

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacLoc

variable {D : D7}

theorem latO_mono (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    {P Q : Pl D → Prop} (h : ∀ v, Q v → P v) : latO S T LS LT Q ≤ latO S T LS LT P := by
  apply AddSubgroup.closure_mono
  rintro w ⟨α, hα, hvan, rest⟩
  exact ⟨α, hα, fun v hv => hvan v fun hq => hv (h v hq), rest⟩

theorem heisO_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ) : heisO ψ S T 0 f = f := by
  funext w
  simp [heisO, symplOH, symplO, hO]

theorem pairA_add (a b : Af D.host.F) :
    pairA D.host.F 0 (a + b) = pairA D.host.F 0 a + pairA D.host.F 0 b := by
  show ((0 : Ainf D.host.F), a + b) = ((0 : Ainf D.host.F), a) + ((0 : Ainf D.host.F), b)
  rw [Prod.mk_add_mk, add_zero]

theorem pairA_mul (a b : Af D.host.F) :
    pairA D.host.F 0 a * pairA D.host.F 0 b = pairA D.host.F 0 (a * b) := by
  show ((0 : Ainf D.host.F), a) * ((0 : Ainf D.host.F), b) = ((0 : Ainf D.host.F), a * b)
  rw [Prod.mk_mul_mk, mul_zero]

theorem pairA_zero : pairA D.host.F 0 (0 : Af D.host.F) = 0 := rfl


open Classical in
theorem latVac_of_places (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (LS : Lat S) (LT : Lat T) (P : Pl D → Prop)
    (f : WO S T → ℂ) (hf : IsThetaFunO ψ S T f) (hv : ∀ v, P v → Vac ψ S T LS LT (· = v) f) :
    IsLatVac (heisO ψ S T) (latO S T (LS : Set _) (LT : Set _) P) f := by

  have one : ∀ (v : Pl D) (w : WO S T), w ∈ latO S T (LS : Set _) (LT : Set _) (fun v' => P v' ∧ v' = v) →
      (heisO ψ S T (2 • w) f = f) ∧ ∀ e, IsSplitIdem D e → IsHalf e w → heisO ψ S T w f = f := by
    intro v w hw
    by_cases hP : P v
    · have hw' : w ∈ latO S T (LS : Set _) (LT : Set _) (· = v) :=
        latO_mono S T _ _ (fun v' h => h.2) hw
      exact ⟨(hv v hP).2.1 w hw', fun e he hh => (hv v hP).2.2 e he w hw' hh⟩
    · have h0 : w = 0 := ((GlobalTheory.T.homLatticeCompletion_cut_integral_properties) D S T _ _ _ w hw).2.2.2 fun v' h => hP (h.2 ▸ h.1)
      subst h0
      simp [heisO_zero]
  refine ⟨?_, ?_⟩
  · intro u hu
    obtain ⟨U, hUo, hU⟩ := hf.level
    have h2u : 2 • u ∈ latO S T (LS : Set _) (LT : Set _) P := AddSubgroup.nsmul_mem _ hu 2
    obtain ⟨s, hs⟩ := (GlobalTheory.T.homLattice_placeCut_smul_mem_openSubgroup) D S T _ _ P U hUo (2 • u) h2u
    have key : ∀ t : Finset (Pl D), t ⊆ s →
        heisO ψ S T (pairA D.host.F 0 (indP D (↑(s \ t) : Set (Pl D))ᶜ) • (2 • u)) f = f := by
      intro t
      induction t using Finset.induction_on with
      | empty =>
        intro _
        have hγ : ∀ v ∈ s, evalV D.host.F v (indP D (↑(s \ ∅) : Set (Pl D))ᶜ) = 0 := by
          intro v hv; rw [evalV_indP]; simp [hv]
        have hm := hs _ (indicatorAdele_mem_integralAdeles _) hγ
        have hl := ((GlobalTheory.T.homLatticeCompletion_cut_integral_properties) D S T _ _ P _ h2u).1 _ (indicatorAdele_mem_integralAdeles ((↑(s \ ∅) : Set (Pl D))ᶜ))
        exact hU _ hm (((GlobalTheory.T.homLatticeCompletion_cut_integral_properties) D S T _ _ _ _ hl).2.2.1)
      | insert v t hvt ih =>
        intro hts
        have hvs : v ∈ s := hts (Finset.mem_insert_self v t)
        have ih' := ih (fun x hx => hts (Finset.mem_insert_of_mem hx))
        have hset : ((↑(s \ insert v t) : Set (Pl D))ᶜ) = {v} ∪ (↑(s \ t) : Set (Pl D))ᶜ := by
          ext x; simp only [Set.mem_compl_iff, Finset.coe_sdiff, Set.mem_sdiff, Finset.mem_coe,
            Finset.mem_insert, Set.mem_union, Set.mem_singleton_iff]
          constructor
          · intro h; by_cases hx : x = v; · exact Or.inl hx
            right; intro h'; exact h ⟨h'.1, fun h'' => h''.elim hx h'.2⟩
          · rintro (rfl | h) h'; · exact h'.2 (Or.inl rfl)
            exact h ⟨h'.1, fun h'' => h'.2 (Or.inr h'')⟩
        have hdisj : Disjoint ({v} : Set (Pl D)) (↑(s \ t) : Set (Pl D))ᶜ := by
          rw [Set.disjoint_singleton_left]; simp [hvs, hvt]
        rw [hset, ← indicatorAdele_union_of_disjoint hdisj, pairA_add, add_smul]
        have hprod : pairA D.host.F 0 (indP D {v}) * pairA D.host.F 0 (indP D (↑(s \ t) : Set (Pl D))ᶜ) = 0 := by
          rw [pairA_mul, indicatorAdele_singleton_mul_singleton, Set.disjoint_iff_inter_eq_empty.mp hdisj, indicatorAdele_empty, pairA_zero]
        rw [(GlobalTheory.T.heisenbergOperator_disjointSupport_smul_add) D ψ S T _ _ _ _ f hprod, ih']
        have hw := ((GlobalTheory.T.homLatticeCompletion_cut_integral_properties) D S T _ _ P u hu).1 _ (indicatorAdele_mem_integralAdeles {v})
        have hw' : pairA D.host.F 0 (indP D {v}) • u ∈
            latO S T (LS : Set _) (LT : Set _) (fun v' => P v' ∧ v' = v) := by
          refine latO_mono S T _ _ (fun v' h => ⟨h.1, ?_⟩) hw
          by_contra hne; apply h.2; rw [evalV_indP]; simp [hne]
        rw [smul_comm]
        exact (one v _ hw').1
    have := key s (subset_refl s)
    rwa [Finset.sdiff_self, Finset.coe_empty, Set.compl_empty, indicatorAdele_univ,
      ((GlobalTheory.T.homLatticeCompletion_cut_integral_properties) D S T _ _ P _ h2u).2.1] at this
  · intro e he u hu hh
    obtain ⟨hee, hec, v, ε, ⟨α, rfl, hα1, hα0⟩, hsum⟩ := he
    have hα : α ∈ intAf D.host.F := by
      intro v'; by_cases h : v' = v
      · subst h; rw [hα1]; exact one_mem _
      · rw [hα0 v' h]; exact zero_mem _
    have hfix : pairA D.host.F 0 α • u = u := by
      ext i j
      show pairA D.host.F 0 α • u i j = u i j
      rw [Algebra.smul_def, ← hsum, ← hh i j, ← mul_assoc, add_mul, hee, mul_comm (cA D e) e, hec, add_zero]
    have hw := ((GlobalTheory.T.homLatticeCompletion_cut_integral_properties) D S T _ _ P u hu).1 α hα
    rw [hfix] at hw
    refine (one v u (latO_mono S T _ _ (fun v' h => ⟨h.1, ?_⟩) hw)).2 e
      ⟨hee, hec, v, _, ⟨α, rfl, hα1, hα0⟩, hsum⟩ hh
    by_contra hne; exact h.2 (hα0 v' hne)

theorem vac_loc : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ (P : Pl D → Prop), (∀ v, P v → Tame D v) → ∀ f, (Vac ψ S T LS LT P f ↔ IsThetaFunO ψ S T f ∧ ∀ v, P v → Vac ψ S T LS LT (· = v) f) ∧ (Vac ψ S T LS LT P f → ∀ g ∈ grpOff S P, ∀ h ∈ grpOff T P, Vac ψ S T LS LT P (om (g, h) f)) ∧ (Vac ψ S T LS LT P f → ∀ (g : GA D S) (h : GA D T) (MS : Lat S) (MT : Lat T), IsSelfDualC S MS → IsSelfDualC T MT → Moves S g LS MS P → Moves T h LT MT P → Vac ψ S T MS MT P (om (g, h) f)) := by
  intro D ψ S T χS χT om hW LS LT hLS hLT P _ f
  refine ⟨⟨fun h => ⟨h.1, fun v hv => ⟨h.1, ?_, ?_⟩⟩, fun h => ⟨h.1, latVac_of_places ψ S T LS LT P f h.1 h.2⟩⟩, ?_, ?_⟩
  · exact fun u hu => h.2.1 u (latO_mono S T _ _ (fun v' h' => h' ▸ hv) hu)
  · exact fun e he u hu => h.2.2 e he u (latO_mono S T _ _ (fun v' h' => h' ▸ hv) hu)
  · intro h g hg k hk
    exact (GlobalTheory.T.thetaLatticeVacuum_of_carriesLatticeCompletions) D ψ S T χS χT om hW LS LT hLS hLT P f h g k LS LT hLS hLT
      ((GlobalTheory.T.carriesLatticeCompletion_of_trivialAtPlaces) D S LS P g hg) ((GlobalTheory.T.carriesLatticeCompletion_of_trivialAtPlaces) D T LT P k hk)
  · intro h g k MS MT hMS hMT hg hk
    exact (GlobalTheory.T.thetaLatticeVacuum_of_carriesLatticeCompletions) D ψ S T χS χT om hW LS LT hLS hLT P f h g k MS MT hMS hMT hg hk

end GlobalTheory.VacLoc

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.latticeCompletionAtPlaces_selfDual_of_selfDual : ∀ (D : D7) (S : HSp D) (LS : Lat S), IsSelfDualC S LS → ∀ (P : Pl D → Prop) (y : Fin S.rank → AE D), (∀ r, y r ∈ idAt D P) → (y ∈ latV S LS P ↔ ∀ s ∈ latV S LS P, (∑ i, ∑ j, cA D (s i) * incA D (HSpace.gram S i j) * y j) ∈ intAt D P) := by
  first | exact @GlobalTheory.FinPl.SelfDualCompl.selfDual_latV | exact GlobalTheory.FinPl.SelfDualCompl.selfDual_latV | (intros; apply GlobalTheory.FinPl.SelfDualCompl.selfDual_latV <;> assumption)
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.integral_of_keeps_selfDualLatticeLineColon : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀) (v : Pl D), Tame D v → IsSelfDualC S L → MonoAt d L L₀ v → ∀ (i j : Fin ρ) (x : AE D), x - 1 ∈ idAt D (· = v) → (∀ r ∈ idAt D (· = v), (∀ a : AE D, colMul d.jX j a ∈ latV S L (· = v) → colMul d.jX i (r * a) ∈ latV S L (· = v)) → ∀ a : AE D, colMul d.jX j a ∈ latV S L (· = v) → colMul d.jX i (r * x * a) ∈ latV S L (· = v)) → x - 1 ∈ intAt D (· = v) := by
  first | exact @GlobalTheory.ColonInt.colon_int | exact GlobalTheory.ColonInt.colon_int | (intros; apply GlobalTheory.ColonInt.colon_int <;> assumption)
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.SplitWeil ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.OffFix

open scoped TensorProduct

variable {D : D7}

theorem idOff_mul_eq_zero {v : Pl D} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) {x y : AE D}
    (hx : x ∈ idOff D (· = v)) (hy : algebraMap (AF D.host.F) (AE D) ε * y = y) : x * y = 0 := by
  classical
  obtain ⟨α, hεα, hv, hw⟩ := hε
  obtain ⟨h0, hc⟩ := placeIdempotent_infinite_and_finite_components D v ε α hεα
  have hc' : ∀ w, compAt D w (algebraMap (AF D.host.F) (AE D) ε) = if w = v then 1 else 0 := by
    intro w
    rw [hc w]
    by_cases h : w = v
    · subst h; rw [if_pos rfl, hv]; rfl
    · rw [if_neg h, hw w h, TensorProduct.zero_tmul]
  have hx0 := (SetCut.mem_idOff_iff_mul (· = v) _ h0 hc' x).1 hx
  rw [← hy, ← mul_assoc, mul_comm x, hx0, zero_mul]

theorem supp_of_mem {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) {ε : AF D.host.F} (hε : IsPlaceIdem D p.v ε)
    (hsum : p.e + cA D p.e = algebraMap (AF D.host.F) (AE D) ε) (S T : HSp D) (LS : Lat S) (LT : Lat T) (u : WO S T)
    (hu : u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v) ∨
      IsHalf p.e u ∨ IsHalf (cA D p.e) u) :
    ∀ i j, algebraMap (AF D.host.F) (AE D) ε * u i j = u i j := by
  rcases hu with hu | hu | hu
  · intro i j
    induction hu using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨α, -, hα0, a, -, s, -, t, -, rfl⟩ := hw
      have hmem : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) ∈ idAt D (· = p.v) := by
        obtain ⟨h0, hc⟩ := placeIdempotent_infinite_and_finite_components D p.v _ α rfl
        rw [mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere]
        exact ⟨h0, fun w hw => by rw [hc w, hα0 w hw, TensorProduct.zero_tmul]⟩
      rw [Matrix.of_apply]
      have hfac : (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) =
          algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) *
            ((1 : AF D.host.F) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j)) := by
        rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
          Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hfac]
      exact ((placeIdem_acts D p.v ε hε).1 _).1 (Ideal.mul_mem_right _ _ hmem)
    | zero => simp
    | add x y _ _ hx hy => simp only [Matrix.add_apply, mul_add, hx, hy]
    | neg x _ hx => simp only [Matrix.neg_apply, mul_neg, hx]
  · intro i j
    have hce : algebraMap (AF D.host.F) (AE D) ε * p.e = p.e := by
      rw [← hsum, add_mul, p.split.1, mul_comm (cA D p.e), p.split.2.1, add_zero]
    rw [← hu i j, ← mul_assoc, hce]
  · intro i j
    have hce : algebraMap (AF D.host.F) (AE D) ε * cA D p.e = cA D p.e := by
      rw [← hsum, add_mul, p.split.2.1, zero_add, ← map_mul, p.split.1]
    rw [← hu i j, ← mul_assoc, hce]

theorem actO_eq_of_grpOff : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (S T : HSp D) (LS : Lat S) (LT : Lat T) (g : GA D S) (h : GA D T),
    g ∈ grpOff S (· = p.v) → h ∈ grpOff T (· = p.v) → ∀ u : WO S T,
    (u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v) ∨ IsHalf p.e u ∨
      IsHalf (cA D p.e) u) → actO S T g h u = u := by
  intro D k _ _ _ _ p S T LS LT g h hg hh u hu
  obtain ⟨ε, hε, hsum⟩ := p.above
  have hsupp := supp_of_mem p hε hsum S T LS LT u hu
  have hA : ∀ i j, (Formalism.L2.Theta.mt T h - 1) i j ∈ idOff D (· = p.v) :=
    (SetCut.mem_congGrp_iff T (idOff D (· = p.v)) h).1 hh
  have hB : ∀ i j, (Formalism.L2.Theta.mt S g⁻¹ - 1) i j ∈ idOff D (· = p.v) :=
    (SetCut.mem_congGrp_iff S (idOff D (· = p.v)) g⁻¹).1 (inv_mem hg)
  let U : Matrix (Fin T.rank) (Fin S.rank) (AE D) := u
  have hU : ∀ i j, algebraMap (AF D.host.F) (AE D) ε * U i j = U i j := hsupp
  have h1 : HMul.hMul (Formalism.L2.Theta.mt T h - 1) U = (0 : Matrix (Fin T.rank) (Fin S.rank) (AE D)) := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    exact Finset.sum_eq_zero fun l _ => idOff_mul_eq_zero hε (hA i l) (hU l j)
  have h2 : HMul.hMul U (Formalism.L2.Theta.mt S g⁻¹ - 1) = (0 : Matrix (Fin T.rank) (Fin S.rank) (AE D)) := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    exact Finset.sum_eq_zero fun l _ => by rw [mul_comm]; exact idOff_mul_eq_zero hε (hB l j) (hU i l)
  have e1 : HMul.hMul (Formalism.L2.Theta.mt T h) U = U := by rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h1; exact h1
  have e2 : HMul.hMul U (Formalism.L2.Theta.mt S g⁻¹) = U := by rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at h2; exact h2
  show HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt T h) U) (Formalism.L2.Theta.mt S g⁻¹) = U
  rw [e1, e2]

end GlobalTheory.FinPl.OffFix

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LineSplitAt
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)

theorem mulVec_sec {m n : ℕ} (M : Matrix (Fin m) (Fin n) (AE D)) (u : Fin n → k) :
    M *ᵥ (fun i => p.sec (u i)) = fun i => p.sec ((M.map p.pr *ᵥ u) i) := by
  funext i

  simp only [Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm, FrameLat.sec_mul_right, mul_comm (u j)]

theorem mulVec_csec {m n : ℕ} (M : Matrix (Fin m) (Fin n) (AE D)) (z : Fin n → k) :
    M *ᵥ (fun i => cA D (p.sec (z i))) = fun i => cA D (p.sec ((M.map (fun a => p.pr (cA D a)) *ᵥ z) i)) := by
  funext i

  simp only [Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [FrameLat.sec_mul, p.sec_pr, mul_comm p.e, mul_assoc, FrameLat.e_mul_sec, map_mul, cA_cA]

theorem eq_sec_add_csec {n : ℕ} {y : Fin n → AE D} (hy : ∀ i, y i ∈ idAt D (· = p.v)) :
    y = (fun i => p.sec (p.pr (y i))) + (fun i => cA D (p.sec (p.pr (cA D (y i))))) := by
  funext i
  have h := (FrameLat.idem_iff p (y i)).1 (hy i)
  simp only [Pi.add_apply, p.sec_pr, map_mul, cA_cA]
  rw [← add_mul, h]

variable {p}

theorem mulVec_mem_of_parts {S T : HSp D} {L : Lat S} {L' : Lat T} (hL : IsSelfDualC S L)
    (M : Matrix (Fin T.rank) (Fin S.rank) (AE D))
    (hw : ∀ u, (fun i => p.sec (u i)) ∈ latV S L (· = p.v) → (fun i => p.sec ((M.map p.pr *ᵥ u) i)) ∈ latV T L' (· = p.v))
    (hc : ∀ z, (fun i => cA D (p.sec (z i))) ∈ latV S L (· = p.v) →
      (fun i => cA D (p.sec ((M.map (fun a => p.pr (cA D a)) *ᵥ z) i))) ∈ latV T L' (· = p.v))
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L (· = p.v)) : M *ᵥ y ∈ latV T L' (· = p.v) := by
  have e := eq_sec_add_csec p (FrameLat.latV_supp hy)
  rw [e] at hy ⊢
  have h := (FrameLat.decomp hL _ _).1 hy
  rw [Matrix.mulVec_add, mulVec_sec, mulVec_csec]
  exact add_mem (hw _ h.1) (hc _ h.2)

theorem pair_eq (S : HSp D) (x z : Fin S.rank → k) :
    ∑ i, ∑ j, x i * p.pr (cA D (incA D (S.gram i j))) * z j =
      x ⬝ᵥ (S.gram.map (p.pr.comp ((cA D).comp (incA D))) *ᵥ z) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.map_apply, RingHom.comp_apply, mul_assoc]

theorem conjT_map {m n : Type} (M : Matrix m n D.host.E) :
    Mᴴ.map (p.pr.comp ((cA D).comp (incA D))) = (M.map (p.pr.comp (incA D)))ᵀ := by
  ext i j
  simp only [Matrix.map_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply, RingHom.comp_apply, FrameLat.cA_incA,
    star_star]

end GlobalTheory.LineSplitAt

namespace GlobalTheory.LineSplitAt



theorem orthAt_of_frames : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n' : Type) [Fintype n'] [DecidableEq n'] (S A L : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (α : Frame p A n') (α₀ : Frame p S (n' ⊕ Fin 1)), IsSumFrame o ζ α α₀ → p.UnitAA → ∀ (LA : Lat A) (LS : Lat S) (ΛA : Submodule 𝒪[k] (n' → k)), IsSelfDualC A LA → IsSelfDualC S LS → α.IsLat LA ΛA → α₀.IsLat LS (lastKer ΛA) → ∃ LL : Lat L, OrthAt o LS LA LL p.v := by
  intro D k _ _ _ _ p n' _ _ S A L o ζ _ α α₀ hsum _ LA LS ΛA hLA hLS hα hα₀
  have hb : α₀.b = fromCols (o.jA.map p.pr * α.b) (replicateCol (Fin 1) fun i => p.pr (ratV (vecB o ζ) i)) := hsum
  have hPJ : o.pA.map p.pr * o.jA.map p.pr = 1 := by
    rw [← Matrix.map_mul, o.pA_jA, Matrix.map_one _ (map_zero _) (map_one _)]
  have hz : o.pA.map p.pr *ᵥ (⇑p.pr ∘ ratV (vecB o ζ)) = 0 := by
    have e1 : ratV (vecB o ζ) = o.jB *ᵥ ratV ζ := by
      funext i

      simp only [ratV, vecB, OrthDec.jB, rat, Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
    funext i
    rw [← RingHom.map_mulVec, e1, Matrix.mulVec_mulVec, o.pA_jB, Matrix.zero_mulVec]
    simp
  have hPz : o.pA.map p.pr * replicateCol (Fin 1) (fun i => p.pr (ratV (vecB o ζ) i)) = 0 := by
    ext i j
    have := congrFun hz i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this

  have hwA : ∀ u : Fin A.rank → k, (fun i => p.sec (u i)) ∈ latV A LA (· = p.v) →
      (fun i => p.sec ((o.jA.map p.pr *ᵥ u) i)) ∈ latV S LS (· = p.v) := by
    intro u hu
    have hx : α.b' *ᵥ u ∈ ΛA := (hα _).2 (by rwa [Matrix.mulVec_mulVec, α.bb', Matrix.one_mulVec])
    have e : o.jA.map p.pr *ᵥ u = α₀.b *ᵥ Sum.elim (α.b' *ᵥ u) 0 := by
      rw [hb, Matrix.fromCols_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.mulVec_mulVec, Matrix.mul_assoc, α.bb',
        Matrix.mul_one, Matrix.mulVec_zero, add_zero]
    rw [e]
    exact (hα₀ _).1 (GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer.2 ⟨by simpa using hx, by simp⟩)
  have hwS : ∀ u : Fin S.rank → k, (fun i => p.sec (u i)) ∈ latV S LS (· = p.v) →
      (fun i => p.sec ((o.pA.map p.pr *ᵥ u) i)) ∈ latV A LA (· = p.v) := by
    intro u hu
    have hy : α₀.b' *ᵥ u ∈ lastKer ΛA := (hα₀ _).2 (by rwa [Matrix.mulVec_mulVec, α₀.bb', Matrix.one_mulVec])
    have e : o.pA.map p.pr *ᵥ u = α.b *ᵥ ((α₀.b' *ᵥ u) ∘ Sum.inl) := by
      conv_lhs => rw [← Matrix.one_mulVec u, ← α₀.bb', ← Matrix.mulVec_mulVec, hb, Matrix.fromCols_mulVec, Matrix.mulVec_add,
        Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hPJ, Matrix.one_mul, Matrix.mulVec_mulVec _ (o.pA.map p.pr), hPz,
        Matrix.zero_mulVec, add_zero]
    rw [e]
    exact (hα _).1 (GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer.1 hy).1

  have hG2 : A.gram * o.qA = o.iAᴴ * S.gram := by
    rw [OrthDec.qA, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (gram_isUnit_det A), Matrix.one_mul]
  have hG1 : S.gram * o.iA = o.qAᴴ * A.gram := by
    have := congrArg Matrix.conjTranspose hG2
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, gram_conjTranspose, gram_conjTranspose] at this
    exact this.symm
  have hcA : ∀ z : Fin A.rank → k, (fun i => cA D (p.sec (z i))) ∈ latV A LA (· = p.v) →
      (fun i => cA D (p.sec ((o.jA.map (fun a => p.pr (cA D a)) *ᵥ z) i))) ∈ latV S LS (· = p.v) := by
    intro z hz
    refine (FrameLat.csec_mem_iff hLS _).2 fun x hx => ?_
    have key : ∑ i, ∑ j, x i * p.pr (cA D (incA D (S.gram i j))) * (o.jA.map (fun a => p.pr (cA D a)) *ᵥ z) j =
        ∑ i, ∑ j, (o.pA.map p.pr *ᵥ x) i * p.pr (cA D (incA D (A.gram i j))) * z j := by
      rw [pair_eq, pair_eq]
      change x ⬝ᵥ (S.gram.map (p.pr.comp ((cA D).comp (incA D))) *ᵥ (o.iA.map (p.pr.comp ((cA D).comp (incA D))) *ᵥ z)) =
        (o.qA.map (p.pr.comp (incA D)) *ᵥ x) ⬝ᵥ (A.gram.map (p.pr.comp ((cA D).comp (incA D))) *ᵥ z)
      rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hG1, Matrix.map_mul, conjT_map, ← Matrix.mulVec_mulVec,
        Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    rw [key]
    exact (FrameLat.csec_mem_iff hLA z).1 hz _ (hwS x hx)
  have hcS : ∀ z : Fin S.rank → k, (fun i => cA D (p.sec (z i))) ∈ latV S LS (· = p.v) →
      (fun i => cA D (p.sec ((o.pA.map (fun a => p.pr (cA D a)) *ᵥ z) i))) ∈ latV A LA (· = p.v) := by
    intro z hz
    refine (FrameLat.csec_mem_iff hLA _).2 fun x hx => ?_
    have key : ∑ i, ∑ j, x i * p.pr (cA D (incA D (A.gram i j))) * (o.pA.map (fun a => p.pr (cA D a)) *ᵥ z) j =
        ∑ i, ∑ j, (o.jA.map p.pr *ᵥ x) i * p.pr (cA D (incA D (S.gram i j))) * z j := by
      rw [pair_eq, pair_eq]
      change x ⬝ᵥ (A.gram.map (p.pr.comp ((cA D).comp (incA D))) *ᵥ (o.qA.map (p.pr.comp ((cA D).comp (incA D))) *ᵥ z)) =
        (o.iA.map (p.pr.comp (incA D)) *ᵥ x) ⬝ᵥ (S.gram.map (p.pr.comp ((cA D).comp (incA D))) *ᵥ z)
      rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hG2, Matrix.map_mul, conjT_map, ← Matrix.mulVec_mulVec,
        Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    rw [key]
    exact (FrameLat.csec_mem_iff hLS z).1 hz _ (hwA x hx)
  have h1 : ∀ y ∈ latV A LA (· = p.v), o.jA *ᵥ y ∈ latV S LS (· = p.v) := fun y hy =>
    mulVec_mem_of_parts hLA o.jA hwA hcA hy
  have h2 : ∀ y ∈ latV S LS (· = p.v), o.pA *ᵥ y ∈ latV A LA (· = p.v) := fun y hy =>
    mulVec_mem_of_parts hLS o.pA hwS hcS hy
  have hsplit : ∀ g : Fin S.rank → AE D, o.jA *ᵥ (o.pA *ᵥ g) + o.jB *ᵥ (o.pB *ᵥ g) = g := fun g => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, o.sum_eq_one, Matrix.one_mulVec]
  let fB := (mulVecLin o.qB).restrictScalars (𝓞 D.host.E)
  have h3 : ∀ x ∈ latV L (LS.map fB) (· = p.v), o.jB *ᵥ x ∈ latV S LS (· = p.v) := by
    intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨a, ha, ha', c, hc, w, hw, rfl⟩ := hx
      rw [Set.mem_singleton_iff] at hc
      subst hc
      obtain ⟨s, hs, rfl⟩ := hw
      have hg : (fun i => pairA D.host.F 0 a ⊗ₜ[D.host.F] (1 * s i)) ∈ latV S LS (· = p.v) :=
        AddSubgroup.subset_closure ⟨a, ha, ha', 1, rfl, s, hs, rfl⟩
      have e2 : o.pB *ᵥ (fun i => pairA D.host.F 0 a ⊗ₜ[D.host.F] (1 * s i)) =
          fun i => pairA D.host.F 0 a ⊗ₜ[D.host.F] (1 * (o.qB *ᵥ s) i) := by
        funext i
        simp only [Matrix.mulVec, dotProduct, one_mul, TensorProduct.tmul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        change ((1 : AF D.host.F) ⊗ₜ[D.host.F] o.qB i j) * _ = _
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      show o.jB *ᵥ (fun i => pairA D.host.F 0 a ⊗ₜ[D.host.F] (1 * (o.qB *ᵥ s) i)) ∈ _
      rw [← e2]
      have hm := hg
      rw [← hsplit (fun i => pairA D.host.F 0 a ⊗ₜ[D.host.F] (1 * s i))] at hm
      exact (add_mem_cancel_left (h1 _ (h2 _ hg))).1 hm
    | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
    | neg x _ hx => rw [Matrix.mulVec_neg]; exact neg_mem hx
  refine ⟨LS.map fB, fun y => ⟨fun hy => ⟨h2 y hy, GlobalTheory.OrthSumLat.rat_mulVec_mem_latV o.qB
    (fun x hx => Submodule.mem_map_of_mem hx) hy⟩, fun h => ?_⟩⟩
  rw [← hsplit y]
  exact add_mem (h1 _ h.1) (h3 _ h.2)

end GlobalTheory.LineSplitAt
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.besselGroup_quotient_fundamentalDomain_cocompact : ∀ (D : D7) (ρ : ℕ) (B : BesLev D ρ), B.μR.IsHaarMeasure ∧ IsClosed (besGrp B.d B.o : Set (GA D B.V)) ∧ (∃ Ω : Set (GA D B.V), IsCompact Ω ∧ ∀ s ∈ besGrp B.d B.o, ∃ γ ∈ GQ B.V ⊓ besGrp B.d B.o, γ * s ∈ Ω) ∧ ∃ 𝓢 : Set (besGrp B.d B.o), IsFundamentalDomain ((GQ B.V).subgroupOf (besGrp B.d B.o)) 𝓢 B.μR ∧ B.μR 𝓢 < ⊤ ∧ ∀ F : GA D B.V → ℂ, ContinuousOn F (besGrp B.d B.o : Set (GA D B.V)) → (∀ γ ∈ GQ B.V ⊓ besGrp B.d B.o, ∀ s ∈ besGrp B.d B.o, F (γ * s) = F s) → IntegrableOn (fun s : besGrp B.d B.o => F s) 𝓢 B.μR ∧ ∫ s in 𝓢, F s ∂B.μR = ∫ a in B.vA.𝓕, ∫ n in B.vN.𝓝, F (n.1 * embA B.d B.o a) ∂B.vN.ν ∂B.vA.μ := by
  exact @GlobalTheory.BesselQuot.besGrp_quotient
end
