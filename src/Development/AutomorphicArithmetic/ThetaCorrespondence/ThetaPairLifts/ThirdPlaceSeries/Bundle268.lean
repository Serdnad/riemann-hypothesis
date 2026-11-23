module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle247
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle036
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle570
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle561
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle259
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle261
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle065
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle035
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle427
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle258
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
namespace GlobalTheory.ElemAtStates
theorem elem_all_alt_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x => Elem (Dof x) ∧ ValLL0 (Dof x) (cfOf x) ∧ (Function.Injective (Dof x).what₂.OtoLL ∧ ∃ F : Subfield (Dof x).what₂.LL, ∀ y, y ∈ (Dof x).what₂.OtoLL.range ↔ y ∈ F ∧ IsIntegral ℤ y) ∧ ∃ (h : HostTied (Dof x)) (jE : (Dof x).host.E →+* Qb), (∀ y, jE y = h.fr.j y) ∧ ∀ k, IsRayPrime (GlobalTheory.HeightCounting.KQbar (Dof x) jE) ((Dof x).host.QS * (Dof x).host.q * (Dof x).host.d) ((Dof x).host.g k) := by
  intro hP
  have h := allSt_and (allSt_and (allSt_and (_root_.GlobalTheory.T.star_mem_LL0 hP) (_root_.GlobalTheory.T.eExp_integral_at_member hP)) (allSt_and (_root_.GlobalTheory.T.is_split_pl_of_places_over_pde hP) (_root_.GlobalTheory.T.valLL0_cfOf_at_states hP)))
    (allSt_and (_root_.GlobalTheory.T.integer_embedding_injective_range_integral_of_inputs hP) (_root_.GlobalTheory.T.exists_norm_element_congruent_one_at_member hP))
  refine allSt_mono h ?_
  rintro K B f T w P x ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5, h6⟩
  refine ⟨⟨h1, h2, h3⟩, h4, h5, ?_⟩
  obtain ⟨hT⟩ := HostTied.exists (Dof x)
  exact ⟨hT, hT.fr.j.toRingHom, fun y => rfl, fun k => GlobalTheory.T.isRayPrime_of_norm_integer_congruent_one (Dof x) k _ (h6 k).1 (h6 k).2⟩
end GlobalTheory.ElemAtStates
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

theorem _root_.GlobalTheory.T.isRayPrime_g_and_integral_range : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x => Elem (Dof x) ∧ ValLL0 (Dof x) (cfOf x) ∧ (Function.Injective (Dof x).what₂.OtoLL ∧ ∃ F : Subfield (Dof x).what₂.LL, ∀ y, y ∈ (Dof x).what₂.OtoLL.range ↔ y ∈ F ∧ IsIntegral ℤ y) ∧ ∃ (h : HostTied (Dof x)) (jE : (Dof x).host.E →+* Qb), (∀ y, jE y = h.fr.j y) ∧ ∀ k, IsRayPrime (GlobalTheory.HeightCounting.KQbar (Dof x) jE) ((Dof x).host.QS * (Dof x).host.q * (Dof x).host.d) ((Dof x).host.g k) := by
  first | exact @_root_.GlobalTheory.ElemAtStates.elem_all_alt_alt | exact _root_.GlobalTheory.ElemAtStates.elem_all_alt_alt | (intros; apply _root_.GlobalTheory.ElemAtStates.elem_all_alt_alt <;> assumption)
end
end
end

section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.GalLoc.FieldAt
theorem galoisRep_field_of_definition_at_place_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c =>
    ValLL0 (w.D Z) (TC.cf w.I w.l Z) ∧ (∀ (k : Fin 2) (z : ℂ), z ^ ((w.D Z).host.g k * ((w.D Z).host.g k - 1)) = 1 → z ∈ (embLL0 (w.D Z)).fieldRange) ∧ (∀ x : (w.D Z).LL0, star (x : (w.D Z).what₂.LL) ∈ (w.D Z).LL0) := by
  intro hP _ hL
  have h1 := _root_.GlobalTheory.TwInputs.SmallField.fieldOk_and_exists_lamDat_ok_teich_valuesIn hP
  have h2 := (evG_of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev).inter (evG_of_ev GlobalTheory.Mem.StdSize.vstd_size_ev)
  refine (h1.inter h2).imp fun K _ _ _ _ hK => ?_
  obtain ⟨hF, hH, hV⟩ := hK
  refine hF.imp fun B f T hO hF' => ?_
  intro hKP w Z Wt p0 t nch n xd c _ _ _
  obtain ⟨hX, -⟩ := hF' hKP T w Z
  have hHH := (hH (w.st Z) hO).1
  obtain ⟨hVs, hs⟩ := hV (w.st Z) hO
  have F := hX (GlobalTheory.TwInputs.JoinModel.realOf t hHH hVs hs) t.r.z.lev.C
  refine ⟨?_, F.roots, F.star⟩
  have v : ValLL0 (w.D Z) t.r.z.R.C := F.vals
  have e : t.r.z.R.C = TC.cf w.I w.l Z := t.r.z.lev.C
  rw [← e]
  exact v
end GlobalTheory.GalLoc.FieldAt
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

theorem _root_.GlobalTheory.T.valLL0_roots_of_unity_mem_star_closed_at_members : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c =>
    ValLL0 (w.D Z) (TC.cf w.I w.l Z) ∧ (∀ (k : Fin 2) (z : ℂ), z ^ ((w.D Z).host.g k * ((w.D Z).host.g k - 1)) = 1 → z ∈ (embLL0 (w.D Z)).fieldRange) ∧ (∀ x : (w.D Z).LL0, star (x : (w.D Z).what₂.LL) ∈ (w.D Z).LL0) := by
  first | exact @_root_.GlobalTheory.GalLoc.FieldAt.galoisRep_field_of_definition_at_place_alt | exact _root_.GlobalTheory.GalLoc.FieldAt.galoisRep_field_of_definition_at_place_alt | (intros; apply _root_.GlobalTheory.GalLoc.FieldAt.galoisRep_field_of_definition_at_place_alt <;> assumption)
end
end
end
