module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle247
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle036
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle559
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle564
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanRangeEquiv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle568
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle576
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle060
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle020
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle569
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle833
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IndicesPairingLengthsVanishOffTwistedPlaces
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle350
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle457
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HtCard
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle563
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle078
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
namespace GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem lowerLeftValuation_eq_zero_all_stages_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x => ValLL0 (Dof x) (cfOf x) := by
  intro _
  refine StepW.of_all fun K B f T w _ _ _ P x => ?_
  exact valLL0_colW w x.o.Z
end GlobalTheory.HeightCounting.Up
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

theorem _root_.GlobalTheory.T.valLL0_cfOf_at_states : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x => ValLL0 (Dof x) (cfOf x) := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.lowerLeftValuation_eq_zero_all_stages_alt | exact _root_.GlobalTheory.HeightCounting.Up.lowerLeftValuation_eq_zero_all_stages_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.lowerLeftValuation_eq_zero_all_stages_alt <;> assumption)
end
end
end

section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.RowDepthTrue
open GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up in

theorem rowDepth_allSt_alt_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x => RowDepth (Dof x) (repOf x.r.Y) := by
  intro hPr
  have hId : StepW Start Start := StepW.of_all fun _ _ _ _ _ _ _ h => h
  refine (hId.and (GlobalTheory.RowDepthTrue.stepW_of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev Start)).trans
    (StepW.of_all fun K B f T w hO _ H => ?_)
  intro P x
  obtain ⟨hHo, hF, -⟩ := H.2 (w.st x.o.Z) hO
  exact rowDepth_rowRepR hPr.hc hPr.decay _ _ _ _ _ _ _ _ _ _ _ _ x.m.z.pins x.m.intersectionNumber_baseChange hHo hF
end GlobalTheory.RowDepthTrue
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

theorem _root_.GlobalTheory.T.depth_of_repOf_of_inputs : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x => RowDepth (Dof x) (repOf x.r.Y) := by
  first | exact @_root_.GlobalTheory.RowDepthTrue.rowDepth_allSt_alt_alt | exact _root_.GlobalTheory.RowDepthTrue.rowDepth_allSt_alt_alt | (intros; apply _root_.GlobalTheory.RowDepthTrue.rowDepth_allSt_alt_alt <;> assumption)
end
end
end

section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
namespace GlobalTheory.HeightCounting.Up
theorem splits_at_all_stages_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x => ∀ v : HeightOneSpectrum (𝓞 (Dof x).host.E), v ∈ placesOver (Dof x).host.E (Dof x).host.pde ∨ v ∈ placesOver (Dof x).host.E (Dof x).host.pde' → IsSplitPl (Dof x).host v := by
  intro _
  refine StepW.of_all fun K B f T w _ _ _ P x v hv => ?_
  have hc : ∀ p ∈ (Dof x).host.levelPrimes, p.Prime ∧ p % ((Dof x).host.QS * (Dof x).host.q * (Dof x).host.d) = 1 :=
    (w.st x.o.Z).B.level_cond
  rcases hv with hv | hv
  · exact isSplitPl_of_mem_levelPrimes _ hc (Dof x).host.pde_level.1 v hv
  · exact isSplitPl_of_mem_levelPrimes _ hc (Dof x).host.pde_level.2 v hv
end GlobalTheory.HeightCounting.Up
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

theorem _root_.GlobalTheory.T.is_split_pl_of_places_over_pde : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x => ∀ v : HeightOneSpectrum (𝓞 (Dof x).host.E), v ∈ placesOver (Dof x).host.E (Dof x).host.pde ∨ v ∈ placesOver (Dof x).host.E (Dof x).host.pde' → IsSplitPl (Dof x).host v := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.splits_at_all_stages_alt | exact _root_.GlobalTheory.HeightCounting.Up.splits_at_all_stages_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.splits_at_all_stages_alt <;> assumption)
end
end
end

section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
namespace GlobalTheory.MtInMain
theorem prN_sMt_alt_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SMt := fun _ => GlobalTheory.MtId.sMt
end GlobalTheory.MtInMain
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

theorem _root_.GlobalTheory.T.sMt_of_published_inputs' : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SMt := by
  first | exact @_root_.GlobalTheory.MtInMain.prN_sMt_alt_alt | exact _root_.GlobalTheory.MtInMain.prN_sMt_alt_alt | (intros; apply _root_.GlobalTheory.MtInMain.prN_sMt_alt_alt <;> assumption)
end
end
end

section



section
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.HeightCounting.Up
open GlobalTheory.Mem.Top.TwChar
theorem exists_twisted_cohomology_class_lift_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ (X : Stages) (f : Fr X.B.toPre) (pl : Finset ℕ) (A : X.toD7.ntw.Tw → Finset (PlE X.toD7.host)) (σ : Seed X.toD7 A) (Av : ℕ → Finset ℕ), (∀ v, TwistedAt X.toD7 v → X.B.places.resChar v ∈ pl) → (∀ v v', OverOne X.toD7 v v' → TwistedAt X.toD7 v → TwistedAt X.toD7 v') → (∀ i (p : ℕ), p ∈ offSet X.B.toPre ∨ p ∈ Av (X.toD7.ntw.l i) → p.Prime → placesOver X.toD7.host.E p ⊆ ↑(A i)) → ∀ S₂ : ∀ P : Pre, Fr P → Set (HChar P.host.E) → Finset ℂ, (∀ P g Ξ, ∀ z ∈ S₂ P g Ξ, IsAlgebraic ℚ z) → ∃ (B' : Base) (f' : Fr B'.toPre) (T' : TwDat B') (h : Enl X.B B'), HEq f' f ∧ T'.pl = pl ∧ T'.Avoids Av ∧ (∀ z ∈ S₂ B'.toPre f' (T'.set f'), ∃ x : B'.LL, B'.embLL x = z) ∧ Coh B' T' ∧ TwFrom X σ h T' := by
  intro hP X f pl A σ Av hpl hsat hA S₂ h₂
  obtain ⟨art, ha⟩ := hP.what₂.art X.toD7.host.E X.toD7.nd.Om
  obtain ⟨h1, T₁, e1, hav, hT, hT', hS⟩ := exists_twDat_stagesOn X f pl {v | TwistedAt X.toD7 v} hpl
    (twistedAt_conj X.toD7) σ.s (fun w => let ⟨_, hb⟩ := σ.reads w; hb.l_eq) (fun w _ => σ.conj w) art ha A σ.Q σ.k σ.ψ
    (fun i => rootIsoAt X.toD7 i (σ.k i)) Av hA (fun w hw => σ.psiOk hw)
  obtain ⟨B', h, a, b, e⟩ := hS (S₂ X.B.toPre f (T₁.set f)) (h₂ _ _ _)
  have e2 : ∀ (P : Pre) (_ : P = X.B.toPre) (g : Fr P) (Ξ : Set (HChar P.host.E)), HEq g f → HEq Ξ (T₁.set f) →
      S₂ P g Ξ = S₂ X.B.toPre f (T₁.set f) := by
    intro P eP g Ξ h1 h2
    subst eP
    rw [eq_of_heq h1, eq_of_heq h2]
  refine ⟨B', tr h.1 Fr f, pull h T₁, h, tr_heq _ _ _, e1, avoids_pull h hav, ?_, ⟨fun v v' hv => ?_, fun v => ?_⟩,
    b, fun v => ⟨fun hw => ?_, fun hw => ?_⟩⟩
  · rw [e2 _ h.1 _ _ (tr_heq _ _ _) e]
    exact a
  · have ho := overOne_plUnder X h v v' hv
    have key : T₁.psi (plUnder h v) = T₁.psi (plUnder h v') ∧ T₁.Q (plUnder h v) = T₁.Q (plUnder h v') ∧
        T₁.k (plUnder h v) = T₁.k (plUnder h v') := by
      by_cases hw : TwistedAt X.toD7 (plUnder h v)
      · have hw' := hsat _ _ ho hw
        obtain ⟨x, y, z⟩ := hT _ hw
        obtain ⟨x', y', z'⟩ := hT _ hw'
        rw [σ.same _ _ hw hw' ho] at x' y' z'
        exact ⟨x.trans x'.symm, y.trans y'.symm, z.trans z'.symm⟩
      · have hw' : ¬ TwistedAt X.toD7 (plUnder h v') := fun h' => hw (hsat _ _ (fun x => (ho x).symm) h')
        obtain ⟨x, y, z⟩ := hT' _ hw
        obtain ⟨x', y', z'⟩ := hT' _ hw'
        exact ⟨x.trans x'.symm, y.trans y'.symm, z.trans z'.symm⟩
    exact ⟨congrArg (tr h.1 (fun P => Finset (HeightOneSpectrum (𝓞 P.host.E)))) key.2.1, key.2.2,
      congrArg (tr h.1 (fun P => HChar P.host.E)) key.1⟩
  · have hn : B'.places.resChar v ^ (pull h T₁).k v ≠ 0 := pow_ne_zero _ (B'.places.resChar_prime v).ne_zero
    have hz := Complex.isPrimitiveRoot_exp _ hn
    obtain ⟨x, hx⟩ := b v _ hz.pow_eq_one
    exact ⟨x, IsPrimitiveRoot.of_map_of_injective (hx ▸ hz) B'.embLL.injective⟩
  · obtain ⟨x, y, z⟩ := hT (plUnder h v) hw
    exact ⟨(tr_heq h.1 (fun P => Finset (HeightOneSpectrum (𝓞 P.host.E))) _).trans (heq_of_eq y), z, _, _,
      (h1 _ (σ.psiOk hw)).2.1, (tr_heq h.1 (fun P => HChar P.host.E) _).trans (heq_of_eq x)⟩
  · exact (congrArg (tr h.1 (fun P => HChar P.host.E)) (hT' _ hw).1).trans (tr_one _)
end GlobalTheory.HeightCounting.Up
end
end
end
end

section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
namespace GlobalTheory.SplitPrimeAuxiliary
open scoped Pointwise
theorem exists_auxiliary_prime_split_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ _ _ _ x => ∀ _ : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, ∀ v, v ∈ placesOver (Dof x).host.E (Dof x).host.pde ∨ v ∈ placesOver (Dof x).host.E (Dof x).host.pde' → IsSplitPl (Dof x).host v := by
  intro _ hL
  apply StepW.of_all
  intro K B f T w _ _ _ P x _ v hv
  rcases hv with hv | hv
  · exact isSplitPl_of_split B.host B.host.pde_prime B.toPre.pde_split.1 v hv
  · exact isSplitPl_of_split B.host B.host.pde'_prime B.toPre.pde_split.2 v hv
end GlobalTheory.SplitPrimeAuxiliary
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

theorem _root_.GlobalTheory.T.places_over_pde_isSplitPl_of_levelC : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ _ _ _ x => ∀ _ : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, ∀ v, v ∈ placesOver (Dof x).host.E (Dof x).host.pde ∨ v ∈ placesOver (Dof x).host.E (Dof x).host.pde' → IsSplitPl (Dof x).host v := by
  first | exact @_root_.GlobalTheory.SplitPrimeAuxiliary.exists_auxiliary_prime_split_alt | exact _root_.GlobalTheory.SplitPrimeAuxiliary.exists_auxiliary_prime_split_alt | (intros; apply _root_.GlobalTheory.SplitPrimeAuxiliary.exists_auxiliary_prime_split_alt <;> assumption)
end
end
end

section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

theorem GlobalTheory.etaJ_with_local_data_eq_alt : ∀ (hPr : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}, KPx B f → Forced K B T → Start K B f T w → ∀ (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) (big : (Dof x).what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 (Dof x))), _root_.GlobalTheory.CoefDuty.BuiltAlt l.a.A l.mt.M l.c.ch l.c.tp.tup big L → SumRepresentations.hypO (withLoc L) → ∀ (M : MtFam (withLoc L)) (Tn : NormalizedLocalCompatibility (withLoc L) M) (Q : (withLoc L).what₂.places.Pl → Finset (PlE (withLoc L).host)), HeckeStdTw Tn.B → (∀ i, (withLoc L).nd.Q i = Q ((withLoc L).nd.w i)) → (∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ (withLoc L).R.m) (w' : (withLoc L).what₂.places.Pl), (withLoc L).what₂.muAt w' ≠ (withLoc L).what₂.mu0 → GlobalTheory.CoefDuty.LatInt (withLoc L) M (Q w') j h1 h2 w') → HeckeTied (withLoc L) M → HeckeRational (withLoc L) M → AVTied (withLoc L) M → (∀ i, GlobalTheory.CoefDuty.ClassSum (M.loc i)) → (withLoc L).nd.EigSpan → Rows.IsotInternal (withLoc L).what₂ → SumRepresentations.Conclusion42 (withLoc L) → SumRepresentations.ConclusionZ (withLoc L) → GoodFTAll (withLoc L) → ∀ (j : ℕ) (v : B.places.Pl), 1 ≤ j → j ≤ (Dof x).R.m → ∀ v' : (withLoc L).what₂.places.Pl, HEq v' v → (withLoc L).what₂.etaJ j v' = P.q.eta j v := by
  intro hPr hL K B f T w P hK hF hS x l big L hB hO M Tn Q hstd hQ hlat hT hR hAV hCS hE hI h42 hZ hG j v h1 h2 v' hv
  obtain rfl : v' = v := eq_of_heq hv
  have hTup : Formalism.L2.DIV.TupTie (withLoc L) (famR (w.st x.o.Z) w.I P.hX (usedOf w.I T P.Wt) x.m.z.Xg x.m.z.tr).A
      ((famR (w.st x.o.Z) w.I P.hX (usedOf w.I T P.Wt) x.m.z.Xg x.m.z.tr).indefDown (s0Of x.m.z.R x.m.z.F)) x.r.Y.tup :=
    ⟨x.r.Y.tup0, x.r.Y.muAt, x.m.z.R.hv0, fun a b h => by rw [← x.r.Y.tupT_tup a, h, x.r.Y.tupT_tup]⟩
  have hTw : ∀ y, y ∈ ((famR (w.st x.o.Z) w.I P.hX (usedOf w.I T P.Wt) x.m.z.Xg x.m.z.tr).indefDown (s0Of x.m.z.R x.m.z.F)).Tw ↔
      ((famR (w.st x.o.Z) w.I P.hX (usedOf w.I T P.Wt) x.m.z.Xg x.m.z.tr).indefDown (s0Of x.m.z.R x.m.z.F)).μ y ≠
        (famR (w.st x.o.Z) w.I P.hX (usedOf w.I T P.Wt) x.m.z.Xg x.m.z.tr).A.μ0 :=
    fun y => ⟨x.m.z.pins.char.tup.mu_ne y, fun h => by_contra fun hw => h (x.m.z.pins.char.tup.mu_off y hw)⟩
  have hθ := GlobalTheory.Mem.ThRead.theta_of_noEta GlobalTheory.Mem.ThetaRead3.thetaP_read_noEta GlobalTheory.Mem.ThOrth.thG_eq_zero_of_orth_noEta
    _ _ _ _ _ _ _ x.m.z.R x.m.z.F x.m.z.cG x.s.p0 x.r.Y x.r.Z x.m.z.pins x.m.intersectionNumber_baseChange
  have hZ0 := GlobalTheory.Mem.R3.DivisionRationalLift.rationalReadingNoCongruence_thetaComplement_spanned _ _ _ _ _ _ _ x.m.z.R x.m.z.F x.m.z.cG x.s.p0 x.r.Y x.r.Z x.m.z.pins x.m.intersectionNumber_baseChange
  have key := GlobalTheory.T.congruenceLength_twistedPlaces_of_heckeIntegrality (withLoc L) _ _ _ _ (famR (w.st x.o.Z) w.I P.hX (usedOf w.I T P.Wt) x.m.z.Xg x.m.z.tr).A
    x.m.z.F.P0 x.m.z.F.ψ0 ((famR (w.st x.o.Z) w.I P.hX (usedOf w.I T P.Wt) x.m.z.Xg x.m.z.tr).fam3.toSub2 (zsOf x.m.z.R x.m.z.F))
    x.r.Y.tup x.r.Y.eMt 1 x.m.intersectionNumber_baseChange.ok.ok2 le_rfl
    ((famR (w.st x.o.Z) w.I P.hX (usedOf w.I T P.Wt) x.m.z.Xg x.m.z.tr).indefDown (s0Of x.m.z.R x.m.z.F)) M Tn
    hTup hTw (fun i y _ => ⟨x.r.Y.formsL i _, x.r.Y.latL i _, hZ0 i _⟩) hstd Q hQ hlat hT hR hAV hCS x.r.Z.jW rfl
    (fun i y _ x' => hθ i _ x') hE hI h42 hZ hG
  obtain ⟨i, rfl⟩ : ∃ i : Fin (Dof x).R.m, j = (i : ℕ) + 1 := ⟨⟨j - 1, by omega⟩, by simp only; omega⟩
  refine (key i v').trans (Eq.trans ?_ (x.m.eta _ v'))
  unfold Rw.etaOf
  rw [dite_eq_left ⟨by omega, i.2⟩]
  split_ifs with ha hb hb
  · simp only [Nat.add_sub_cancel, Fin.eta]
    rfl
  · exact (hb ha).elim
  · exact (ha hb).elim
  · rfl
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

theorem _root_.GlobalTheory.T.etaJ_local_compatibility_alt : ∀ (hPr : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}, KPx B f → Forced K B T → Start K B f T w → ∀ (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) (big : (Dof x).what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 (Dof x))), _root_.GlobalTheory.CoefDuty.BuiltAlt l.a.A l.mt.M l.c.ch l.c.tp.tup big L → SumRepresentations.hypO (withLoc L) → ∀ (M : MtFam (withLoc L)) (Tn : NormalizedLocalCompatibility (withLoc L) M) (Q : (withLoc L).what₂.places.Pl → Finset (PlE (withLoc L).host)), HeckeStdTw Tn.B → (∀ i, (withLoc L).nd.Q i = Q ((withLoc L).nd.w i)) → (∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ (withLoc L).R.m) (w' : (withLoc L).what₂.places.Pl), (withLoc L).what₂.muAt w' ≠ (withLoc L).what₂.mu0 → GlobalTheory.CoefDuty.LatInt (withLoc L) M (Q w') j h1 h2 w') → HeckeTied (withLoc L) M → HeckeRational (withLoc L) M → AVTied (withLoc L) M → (∀ i, GlobalTheory.CoefDuty.ClassSum (M.loc i)) → (withLoc L).nd.EigSpan → Rows.IsotInternal (withLoc L).what₂ → SumRepresentations.Conclusion42 (withLoc L) → SumRepresentations.ConclusionZ (withLoc L) → GoodFTAll (withLoc L) → ∀ (j : ℕ) (v : B.places.Pl), 1 ≤ j → j ≤ (Dof x).R.m → ∀ v' : (withLoc L).what₂.places.Pl, HEq v' v → (withLoc L).what₂.etaJ j v' = P.q.eta j v := by
  first | exact @_root_.GlobalTheory.etaJ_with_local_data_eq_alt | exact _root_.GlobalTheory.etaJ_with_local_data_eq_alt | (intros; apply _root_.GlobalTheory.etaJ_with_local_data_eq_alt <;> assumption)
end
end
end

section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
namespace GlobalTheory.HeightCounting.Up
theorem fixedField_star_stable_of_third_jump_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ _ _ _ x =>
    ∀ _ : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, ∀ y : (Dof x).LL0, star (y : (Dof x).what₂.LL) ∈ (Dof x).LL0 := by
  intro _ _
  refine StepW.of_all fun K B f T w _ _ _ P x _ y => ?_
  exact (IntermediateField.normal_iff_forall_map_le.1 B.coeffGaloisSubfield_isGalois.to_normal
    (starRingEnd (Dof x).what₂.LL).toRatAlgHom) ⟨_, y.2, rfl⟩
end GlobalTheory.HeightCounting.Up
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

theorem _root_.GlobalTheory.T.star_mem_LL0_at_level_c : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ _ _ _ x => ∀ _ : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, ∀ y : (Dof x).LL0, star (y : (Dof x).what₂.LL) ∈ (Dof x).LL0 := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.fixedField_star_stable_of_third_jump_alt | exact _root_.GlobalTheory.HeightCounting.Up.fixedField_star_stable_of_third_jump_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.fixedField_star_stable_of_third_jump_alt <;> assumption)
end
end
end

section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
namespace GlobalTheory.HeightCounting.Up
theorem ramification_index_integral_of_third_jump_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ _ _ _ x => ∀ _ : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, ∀ j g, ∃ z : ℤ, eExp (Dof x) j g = z := by
  intro _ _
  refine StepW.of_all fun K B f T w _ _ _ P x _ j g => ?_
  exact ((Dof x).hc ((Dof x).eTau.symm g)).e_int j
end GlobalTheory.HeightCounting.Up
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

theorem _root_.GlobalTheory.T.eExp_integer_of_levelC : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ _ _ _ x => ∀ _ : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, ∀ j g, ∃ z : ℤ, eExp (Dof x) j g = z := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.ramification_index_integral_of_third_jump_alt | exact _root_.GlobalTheory.HeightCounting.Up.ramification_index_integral_of_third_jump_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.ramification_index_integral_of_third_jump_alt <;> assumption)
end
end
end

section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
namespace GlobalTheory.HeightCounting.Up.ChebAtThird
theorem chebotarev_split_places_at_all_levels_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists,
    AllSt fun _ _ _ _ _ _ x => ∀ _ : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, GlobalTheory.RowTie.ChebSplit (Dof x).nd := by
  intro hP hL
  exact StepW.of_all fun _ _ _ _ _ _ _ _ _ _ _ => GlobalTheory.ChebSplitDense.chebSplit_nd hP.what₂.cheb _
end GlobalTheory.HeightCounting.Up.ChebAtThird
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

theorem _root_.GlobalTheory.T.chebSplit_of_published_inputs_at_level_c : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ _ _ _ x => ∀ _ : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, GlobalTheory.RowTie.ChebSplit (Dof x).nd := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.ChebAtThird.chebotarev_split_places_at_all_levels_alt | exact _root_.GlobalTheory.HeightCounting.Up.ChebAtThird.chebotarev_split_places_at_all_levels_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.ChebAtThird.chebotarev_split_places_at_all_levels_alt <;> assumption)
end
end
end

section



section
section
noncomputable section
namespace GlobalTheory.HeightCounting.Up
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem eventually_eigSpan_of_levelC : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x =>
    ∀ l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => D'.nd.EigSpan := by
  intro hL _
  refine StepW.of_all fun K B f T w _ _ _ => ?_
  intro P x l
  exact ⟨fun _ => ∅, fun L _ => eigSpan_of_record _⟩
end GlobalTheory.HeightCounting.Up
end
end
end
end

section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.HeightCounting.JumpsSt

theorem locComp_of_isRc_classMapD_cenLoc : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → GlobalTheory.HeightCounting.HtCard → AllSt fun _ _ _ _ _ _ x =>
    ∀ l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => SumRepresentations.hypO D' → JumpsCard D'.nd D'.naut := by
  intro hL _ hH
  refine StepW.of_all fun K B f T w _ _ _ => ?_
  intro P x l
  refine ⟨fun _ => ∅, fun L hB _ => ?_⟩
  obtain ⟨Sp, ⟨Au⟩, hs⟩ := hB
  let b : _root_.GlobalTheory.HeightCounting.NormChoiceConstructed hL (withLoc L) :=
    { D := Dof x, cf := cfOf x, jE := l.a.jE, A := l.a.A, cg := l.a.cg, au := l.a.au, rep := repOf x.r.Y, row := l.a.row,
      low := lowAll (Dof x), Pq := l.Pq, S := l.rat.S, hL := l.rat.In.hL, eig := l.rat.In.eig, θ := l.rat.In.θ, Bs := l.b.Bs,
      M := l.mt.M, C := l.c.ch, tp := l.c.tp, ch := l.c.side, mt := mtInput_of l.c.tp l.mt.mt l.c.xi_eq l.c.Q_eq, big := fun _ => ∅, L := L, Sp := Sp, Au := Au, ss := hs,
      eq := rfl }
  exact _root_.GlobalTheory.HeightCounting.JumpsAt.jumpsCard_of_built_alt hH b l.a.fr l.a.pht
end GlobalTheory.HeightCounting.JumpsSt
end
end
end
end
