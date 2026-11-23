module

import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle041
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsIrrKSubOfIsKTypeOf
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SmoothDefs
public import CompanionTheory.AutomorphicTheory.HarishChandraMultiplicity.HCMult
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.SubquotientNontrivial
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle034
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HarishChandraModulesIndefiniteUnitaryGroup
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1698
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle013
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle015
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1484
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle230
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.BottomMinor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1122
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle230
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PolarisationOperatorApplyVariable
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1697
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SmoothA
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.Clause1
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle050
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle218
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

open Matrix

noncomputable section

namespace GlobalTheory.KFinLinkPort

open GlobalTheory.KFinVec
open ReciprocityTheory.ChartRestriction.DS (smD smE smE_apply isDerivedOn_smE dS dS_eq_actM actM)
open CompanionTheory.D.gk.HC (KF)

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem dRep_eq_dS (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (X : Matrix (Fin n) (Fin n) ℂ) (w : H) :
    Formalism.L2.Theta.dRep σ X w = dS σ X w := by
  unfold Formalism.L2.Theta.dRep dS
  congr 1

theorem isAdmissible_of [CompleteSpace H] (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ)
    (hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ) : IsAdmissible ε σ := by
  rintro S ⟨hf, -, hK, -⟩
  have hfin : FiniteDimensional ℂ (Formalism.MainNotions.BridgeCPX.eqImg (fun k : Formalism.REAL.KG ε => σ (Formalism.REAL.toMK k)) S) :=
    (CompanionTheory.HCMult.harish_chandra_multiplicity : Formalism.MainNotions.BridgeCPX.HCMult) n ε H σ hσ hirr S hf hK
  have hle : kIsotypic ε σ S ≤ Formalism.MainNotions.BridgeCPX.eqImg (fun k : Formalism.REAL.KG ε => σ (Formalism.REAL.toMK k)) S :=
    iSup_le fun T => le_sSup ⟨T.1, fun a v w h => T.2 _ a.2 v w h, rfl⟩
  exact Submodule.finiteDimensional_of_le hle

theorem isLieStable_of [CompleteSpace H] (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ)
    (hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ) : IsLieStable ε σ (kFinSub ε σ) := by
  apply _root_.GlobalTheory.CompanionTheory.KFinLink.isLieStable_of <;> assumption

theorem lieIrr_of [CompleteSpace H] (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ)
    (hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ) (S : Submodule ℂ H) (hS : S ≤ kFinSub ε σ)
    (hL : IsLieStable ε σ S) : S = ⊥ ∨ S = kFinSub ε σ := by
  obtain ⟨h1, -⟩ := CompanionTheory.D.gk.HC.K_finite_smooth_vectors n ε H σ hσ hirr
  let N : Submodule ℂ (smD ε σ) := S.comap (smD ε σ).subtype
  have hNK : (N : Set (smD ε σ)) ⊆ KF ε σ := fun v hv => hS hv
  have hst : ∀ a b, ∀ v ∈ N, smE ε σ a b v ∈ N := by
    intro a b v hv
    show ((smE ε σ a b v : smD ε σ) : H) ∈ S
    rw [smE_apply hσ]
    have e1 := hL _ (ReciprocityTheory.ChartRestriction.DS.SmDerA.inG_cpart1 ε (Matrix.single a b 1)) (v : H) hv
    have e2 := hL _ (ReciprocityTheory.ChartRestriction.DS.SmDerA.inG_cpart2 ε (Matrix.single a b 1)) (v : H) hv
    rw [dRep_eq_dS] at e1 e2
    exact S.add_mem e1 (S.smul_mem _ e2)
  rcases GlobalTheory.HcPort.uIrr n ε H σ hσ hirr N hNK hst with h | h
  · left
    refine eq_bot_iff.2 fun v hv => ?_
    have hvN : (⟨v, h1 v (hS hv)⟩ : smD ε σ) ∈ N := hv
    rw [h] at hvN
    have := (Submodule.mem_bot ℂ).1 hvN
    exact (Submodule.mem_bot ℂ).2 (congrArg Subtype.val this)
  · right
    refine le_antisymm hS fun v hv => ?_
    have hvK : (⟨v, h1 v hv⟩ : smD ε σ) ∈ KF ε σ := hv
    rw [← h] at hvK
    exact hvK

end GlobalTheory.KFinLinkPort

namespace GlobalTheory.KFinLinkPort

theorem kFiniteVectors_irreducibleUnitary_unitaryGroupPQ : GlobalTheory.Published.KFiniteVectorsUnitary := by
  intro n ε H _ _ _ _ σ hσ hirr
  exact ⟨GlobalTheory.KFinLinkPort.isAdmissible_of hσ hirr,
    GlobalTheory.HcPort.kFiniteVectors_analytic_indefiniteUnitary n ε H σ hσ hirr,
    GlobalTheory.T.dense_kFinite_vectors_unitaryGroupRep n ε H σ hσ,
    GlobalTheory.KFinLinkPort.isLieStable_of hσ hirr,
    fun S hS hL => GlobalTheory.KFinLinkPort.lieIrr_of hσ hirr S hS hL⟩

end GlobalTheory.KFinLinkPort

end
end

section

open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

namespace GlobalTheory.LowKType

theorem lowKSub_mem_of_forall {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {lam : Fin n → ℝ} {D : Submodule ℂ H} (Q : Submodule ℂ D)
    (hD : ∀ S : Submodule ℂ H, IsKTypeOf ε σ (lowK ε lam) S → S ≤ D)
    (hQ : ∀ S : Submodule ℂ H, IsKTypeOf ε σ (lowK ε lam) S → ∀ y : D, (y : H) ∈ S → y ∈ Q) :
    ∀ y : D, (y : H) ∈ lowKSub ε lam σ → y ∈ Q := by
  have hle : lowKSub ε lam σ ≤ Q.map D.subtype := by
    unfold lowKSub
    refine sSup_le fun S hS x hx => ?_
    exact ⟨⟨x, hD S hS hx⟩, hQ S hS ⟨x, hD S hS hx⟩ hx, rfl⟩
  intro y hy
  obtain ⟨z, hz, hzy⟩ := hle hy
  have : z = y := Subtype.ext hzy
  exact this ▸ hz

end GlobalTheory.LowKType

open GlobalTheory.LowKType in
theorem GlobalTheory.HolDS.lowKSub_kMod : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D) (lam : Fin n → ℝ), IsHCParam lam → IsHolChamber ε lam → IsDS ε lam σ → IsKMod ε σ D E → lowKSub ε lam σ ≤ D ∧ KStab ε E ((lowKSub ε lam σ).comap D.subtype) ∧ (lowKSub ε lam σ).comap D.subtype ≠ ⊥ ∧ ∀ a b : Fin n, ε a = true → ε b = false → ∀ x ∈ (lowKSub ε lam σ).comap D.subtype, E b a x = 0 := by
  intro n ε H _ _ σ D E lam hHC hch hDS hK
  obtain ⟨hC, _, hU, hI, _, hEx, hmin⟩ := hDS
  have hT := fun μ S hS => GlobalTheory.T.kType_le_kFiniteVectors_finiteDimensional n ε H σ D E hC hU hI hK μ S hS
  have hD : ∀ S : Submodule ℂ H, IsKTypeOf ε σ (lowK ε lam) S → S ≤ D := fun S hS => (hT _ S hS).1
  have hM : IsMin ε E lam := fun μ x hx0 hx => by
    obtain ⟨T, hT'⟩ := hK.ty μ x hx0 hx
    exact hmin μ T hT'
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold lowKSub
    exact sSup_le fun S hS => hD S hS
  · intro a b hab v hv
    exact lowKSub_mem_of_forall ((lowKSub ε lam σ).comap D.subtype |>.comap (E a b)) hD
      (fun S hS y hy => by
        have h3 := (hT _ S hS).2.2.1 a b hab y hy
        show ((E a b y : D) : H) ∈ lowKSub ε lam σ
        exact (le_sSup hS : S ≤ lowKSub ε lam σ) h3) v hv
  · obtain ⟨S, hS⟩ := hEx
    obtain ⟨v, hv0, hvS, _⟩ := hK.hw _ S hS
    intro hbot
    have hv : v ∈ (lowKSub ε lam σ).comap D.subtype := (le_sSup hS : S ≤ lowKSub ε lam σ) hvS
    rw [hbot] at hv
    exact hv0 ((Submodule.mem_bot ℂ).1 hv)
  · intro a b ha hb x hx
    exact (lowKSub_mem_of_forall (LinearMap.ker (E b a)) hD
      (fun S hS y hy => by
        have h := hT _ S hS
        haveI := h.2.1
        exact GlobalTheory.T.pMinus_annihilates_lowestKType_holomorphicChamber n ε D E lam hK.gl hK.unit hHC.1 hch hM (S.comap D.subtype) h.2.1 h.2.2.1 h.2.2.2
          a b ha hb y hy) x hx : x ∈ LinearMap.ker (E b a))
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

namespace GlobalTheory.LowRow

theorem isEnum_unique {n : ℕ} {S : SPar} {lam lam' : Fin n → ℝ} {ε ε' : Fin n → Bool}
    (h : IsEnum S lam ε) (h' : IsEnum S lam' ε') : lam = lam' ∧ ε = ε' := by
  obtain ⟨hA, q, hq, hS⟩ := h
  obtain ⟨hA', q', hq', hS'⟩ := h'
  have hqA : StrictAnti q := fun a b hab => by
    have := hA hab; rw [hq, hq] at this; exact_mod_cast this
  have hqA' : StrictAnti q' := fun a b hab => by
    have := hA' hab; rw [hq', hq'] at this; exact_mod_cast this
  have himg : Finset.univ.image q = Finset.univ.image q' := by
    have e := congrArg (Finset.image Prod.fst) (hS.symm.trans hS')
    simpa [Finset.image_image, Function.comp_def] using e
  have hr : Set.range q = Set.range q' := by
    have := congrArg (fun s : Finset ℚ => (s : Set ℚ)) himg
    simpa [Finset.coe_image] using this
  have hqq : q = q' := (StrictAnti.range_inj hqA hqA').1 hr
  subst hqq
  refine ⟨funext fun a => by rw [hq, hq'], funext fun a => ?_⟩
  have hm : (q a, ε a) ∈ S := by rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
  rw [hS'] at hm
  obtain ⟨b, -, hb⟩ := Finset.mem_image.1 hm
  have hb1 : b = a := hqA.injective (congrArg Prod.fst hb)
  subst hb1
  exact (congrArg Prod.snd hb).symm

theorem parAt_overK {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    (σ : D.what₂.LL →+* ℂ) (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ) (ρ : D.what₂.Tau) :
    parAt (Wc D i) σ ρ = parAt (Wc D i) (sg0 D A) (lab σ ρ) := by
  have hs : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0
  have hsig : ∀ τ, (Wc D i).sig (tauE D τ) = D.R.sigW ((i : ℕ) + 1) :=
    fun τ => D.sp.W_sigval _ (Nat.le_add_left _ _) i.2 _
  have hl := ((GlobalTheory.GalLift.labels_overK σ).1 hK).2 ρ
  unfold parAt kapAt
  rw [if_pos hl, hs, GlobalTheory.ThetaFiresProbe.lab_fixed, if_pos (GlobalTheory.ThetaFiresProbe.labE_fixed _), hsig ρ, hsig (lab σ ρ)]

theorem model_overK {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    (σ : D.what₂.LL →+* ℂ) (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ) (ρ : D.what₂.Tau) :
    (R.MW i σ).lam ρ = (R.MW i (sg0 D A)).lam (lab σ ρ) ∧ (R.MW i σ).ε ρ = (R.MW i (sg0 D A)).ε (lab σ ρ) := by
  have h1 := (R.MW i σ).enum ρ
  rw [parAt_overK R i σ hK ρ] at h1
  exact isEnum_unique h1 ((R.MW i (sg0 D A)).enum (lab σ ρ))

theorem holShape_overK : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F →
    ∀ i σ s, IsEmbOverK D σ s → HolShape (R.MW i σ) ∧ ∃ w, WtIs (R.MW i σ) w := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hc i σ s hE
  have hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ := hE.2
  obtain ⟨hH, w0, hw0⟩ := holShape_fixed D G Pl0 T A Ks R hc.models.order i
  have hm := model_overK R i σ hK
  refine ⟨fun ρ => ?_, fun ρ c => w0 (lab σ ρ) c, fun ρ c => ?_⟩
  · have h := hH (lab σ ρ)
    rw [← (hm ρ).1, ← (hm ρ).2] at h
    exact h
  · have h := hw0 (lab σ ρ) c
    unfold extWt at h ⊢
    rw [← (hm ρ).1, ← (hm ρ).2] at h
    exact h

end GlobalTheory.LowRow
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

namespace GlobalTheory.LowRowFock

open MvPolynomial

theorem fock_one {σ : Type} : Formalism.E.fock (1 : MvPolynomial σ ℂ) 1 = 1 := by
  simp [Formalism.E.fock, Formalism.A.mfact]

theorem fock_rename_inj {σ τ : Type} {f : σ → τ} (hf : Function.Injective f) (P P' : MvPolynomial σ ℂ) :
    Formalism.E.fock (rename f P) (rename f P') = Formalism.E.fock P P' := by
  have h := GlobalTheory.JointHarm.fock_rename_mul (g := (fun e : Empty => e.elim : Empty → τ)) hf
    (fun x => x.elim) (fun _ y => y.elim) P P' 1 1
  simpa [fock_one] using h

theorem fock_mul_of_supported {σ : Type} {A B : Set σ} (hAB : Disjoint A B) {P P' Q Q' : MvPolynomial σ ℂ}
    (hP : P ∈ supported ℂ A) (hP' : P' ∈ supported ℂ A) (hQ : Q ∈ supported ℂ B) (hQ' : Q' ∈ supported ℂ B) :
    Formalism.E.fock (P * Q) (P' * Q') = Formalism.E.fock P P' * Formalism.E.fock Q Q' := by
  rw [supported_eq_range_rename] at hP hP' hQ hQ'
  obtain ⟨P₀, rfl⟩ := (AlgHom.mem_range _).mp hP
  obtain ⟨P₁, rfl⟩ := (AlgHom.mem_range _).mp hP'
  obtain ⟨Q₀, rfl⟩ := (AlgHom.mem_range _).mp hQ
  obtain ⟨Q₁, rfl⟩ := (AlgHom.mem_range _).mp hQ'
  rw [GlobalTheory.JointHarm.fock_rename_mul Subtype.val_injective Subtype.val_injective
      (fun x y h => Set.disjoint_left.mp hAB x.2 (h ▸ y.2)),
    fock_rename_inj Subtype.val_injective, fock_rename_inj Subtype.val_injective]

theorem fock_prod_of_supported {σ ι : Type} [DecidableEq ι] (A : ι → Set σ) (hA : Pairwise fun i j => Disjoint (A i) (A j))
    (F G : ι → MvPolynomial σ ℂ) (hF : ∀ i, F i ∈ supported ℂ (A i)) (hG : ∀ i, G i ∈ supported ℂ (A i))
    (s : Finset ι) :
    Formalism.E.fock (∏ i ∈ s, F i) (∏ i ∈ s, G i) = ∏ i ∈ s, Formalism.E.fock (F i) (G i) := by
  induction s using Finset.induction_on with
  | empty => simp [fock_one]
  | insert a s ha ih =>
    have hd : Disjoint (A a) (⋃ i ∈ s, A i) :=
      Set.disjoint_iUnion₂_right.mpr fun i hi => hA (fun e => ha (e ▸ hi))
    have hmem : ∀ H : ι → MvPolynomial σ ℂ, (∀ i, H i ∈ supported ℂ (A i)) →
        ∏ i ∈ s, H i ∈ supported ℂ (⋃ i ∈ s, A i) := fun H hH =>
      Subalgebra.prod_mem _ fun i hi => supported_mono (Set.subset_biUnion_of_mem hi) (hH i)
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.prod_insert ha,
      fock_mul_of_supported hd (hF a) (hG a) (hmem F hF) (hmem G hG), ih]

theorem rename_mem_supported {σ τ : Type} (f : σ → τ) (s : Set τ) (hs : ∀ x, f x ∈ s) (P : MvPolynomial σ ℂ) :
    rename f P ∈ supported ℂ s := by
  classical
  rw [mem_supported]
  intro v hv
  obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp (vars_rename f P hv)
  exact hs w

variable {D : D7} {m n : ℕ}

theorem minorPlus_eq (τ : D.what₂.Tau) {p : ℕ} (hpm : p ≤ m) (hpn : p ≤ n) (i : Fin p) :
    minorPlus (D := D) (m := m) (n := n) τ (i + 1) =
      rename (fun v : Fin n × Fin p => ((τ, ⟨v.2, lt_of_lt_of_le v.2.2 hpm⟩, v.1) : FVar D m n))
        (GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.topMinor hpn i) := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.topMinor, AlgHom.map_det]
  unfold minorPlus
  congr 1
  ext α β
  have := α.2
  have := β.2
  have := i.2
  simp only [Matrix.of_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, rename_X, varF]
  rw [dite_eq_left ⟨by omega, by omega⟩]

theorem minorMinus_eq (τ : D.what₂.Tau) {p q : ℕ} (hm : p + q ≤ m) (hqn : q ≤ n) (i : Fin q) :
    minorMinus (D := D) (m := m) (n := n) τ p (i + 1) =
      rename (fun v : Fin n × Fin q => ((τ, ⟨p + v.2, by have := v.2.2; omega⟩, v.1) : FVar D m n))
        (GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.bottomMinor hqn i) := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.bottomMinor, AlgHom.map_det]
  unfold minorMinus
  congr 1
  ext α β
  have := α.2
  have := β.2
  have := i.2
  simp only [Matrix.of_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, rename_X, varF]
  rw [dite_eq_left ⟨by omega, by omega⟩]

def embTop (τ : D.what₂.Tau) {p : ℕ} (hpm : p ≤ m) : Fin n × Fin p → FVar D m n :=
  fun v => (τ, ⟨v.2, lt_of_lt_of_le v.2.2 hpm⟩, v.1)

def embBot (τ : D.what₂.Tau) {p q : ℕ} (hm : p + q ≤ m) : Fin n × Fin q → FVar D m n :=
  fun v => (τ, ⟨p + v.2, by have := v.2.2; omega⟩, v.1)

theorem embTop_injective (τ : D.what₂.Tau) {p : ℕ} (hpm : p ≤ m) : Function.Injective (embTop (n := n) τ hpm) := by
  intro x y e
  simp only [embTop, Prod.mk.injEq, Fin.mk.injEq] at e
  exact Prod.ext e.2.2 (Fin.ext e.2.1)

theorem embBot_injective (τ : D.what₂.Tau) {p q : ℕ} (hm : p + q ≤ m) :
    Function.Injective (embBot (n := n) τ (q := q) hm) := by
  intro x y e
  simp only [embBot, Prod.mk.injEq, Fin.mk.injEq, add_right_inj] at e
  exact Prod.ext e.2.2 (Fin.ext e.2.1)

theorem embTop_ne_embBot (τ : D.what₂.Tau) {p q : ℕ} (hm : p + q ≤ m) (x : Fin n × Fin p) (y : Fin n × Fin q) :
    embTop τ (by omega) x ≠ embBot τ hm y := by
  intro e
  simp only [embTop, embBot, Prod.mk.injEq, Fin.mk.injEq] at e
  have := x.2.2
  omega

theorem minorProduct_rename_mem_supported_place (τ : D.what₂.Tau) {p q : ℕ} (hm : p + q ≤ m) (P : MvPolynomial (Fin n × Fin p) ℂ)
    (Q : MvPolynomial (Fin n × Fin q) ℂ) :
    rename (embTop τ (by omega)) P * rename (embBot τ hm) Q ∈ supported ℂ {v : FVar D m n | v.1 = τ} :=
  Subalgebra.mul_mem _ (rename_mem_supported (embTop τ (by omega)) {v : FVar D m n | v.1 = τ} (fun x => by simp [embTop]) P)
    (rename_mem_supported (embBot τ hm) {v : FVar D m n | v.1 = τ} (fun x => by simp [embBot]) Q)

theorem deltaAt_eq (τ : D.what₂.Tau) {p q : ℕ} (hm : p + q ≤ m) (hpn : p ≤ n) (hqn : q ≤ n) (ap am : ℕ → ℕ) :
    deltaAt (D := D) (m := m) (n := n) τ p ap q am =
      rename (embTop τ (by omega)) (GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.delTop hpn (fun i : Fin p => ap i)) *
        rename (embBot τ hm) (GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.delBottom hqn (fun i : Fin q => am i)) := by
  unfold deltaAt GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.delTop GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.delBottom
  rw [map_prod, map_prod, Finset.prod_range, Finset.prod_range]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_pow, minorPlus_eq τ (by omega) hpn i]
    congr 1
    try (unfold GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.nextPart; split_ifs <;> rfl)
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_pow, minorMinus_eq τ hm hqn i]
    congr 1
    try (unfold GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.nextPart; split_ifs <;> rfl)

theorem hookOf_eq_hookProd (l : ℕ) (a : ℕ → ℕ) (ha : Antitone a) :
    (hookOf l a : ℂ) = ((GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.hookProd (fun i : Fin l => a i) : ℚ) : ℂ) := by
  have ha' : ∀ x y, x ≤ y → y < l → a y ≤ a x := fun x y h _ => ha h
  have hant : Antitone (fun i : Fin l => a i) := fun i j h => ha (Fin.le_iff_val_le_val.mp h)
  suffices h : (hookOf l a : ℚ) = GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.hookProd (fun i : Fin l => a i) by
    rw [← h]; push_cast; rfl
  rw [GlobalTheory.HookDiagram.hookOf_eq l a ha', GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.hookProd,
    eq_div_iff (GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.hookDen_pos hant).ne']
  have key := congrArg (Nat.cast : ℕ → ℚ) (GlobalTheory.LiftSizeCompare.hookProd_mul l a ha')
  push_cast [Nat.cast_prod] at key
  have hden : (∏ r ∈ Finset.range l, ∏ j ∈ Finset.Ioo r l, ((a r - a j + (j - r) : ℕ) : ℚ)) =
      GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.hookDen (fun i : Fin l => a i) := by
    rw [Finset.prod_range, GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.hookDen]
    refine Finset.prod_congr rfl fun i _ => ?_
    symm
    refine Finset.prod_bij (fun j _ => (j : ℕ)) ?_ ?_ ?_ ?_
    · intro j hj
      exact Finset.mem_Ioo.mpr ⟨Fin.lt_iff_val_lt_val.mp (Finset.mem_Ioi.mp hj), j.2⟩
    · intro j _ j' _ e
      exact Fin.ext e
    · intro b hb
      have := Finset.mem_Ioo.mp hb
      exact ⟨⟨b, this.2⟩, Finset.mem_Ioi.mpr (Fin.lt_iff_val_lt_val.mpr this.1), rfl⟩
    · intro j hj
      have hij : (i : ℕ) < j := Fin.lt_iff_val_lt_val.mp (Finset.mem_Ioi.mp hj)
      have h1 : a j ≤ a i := ha hij.le
      rw [Nat.cast_add, Nat.cast_sub h1, Nat.cast_sub hij.le]
      ring
  have hnum : (∏ r ∈ Finset.range l, (((a r + l - 1 - r).factorial : ℕ) : ℚ)) =
      ∏ i : Fin l, (((a i + (l - ((i : ℕ) + 1))).factorial : ℕ) : ℚ) := by
    rw [Finset.prod_range]
    refine Finset.prod_congr rfl fun i _ => ?_
    have := i.2
    congr 3
    omega
  rw [← hden, ← hnum]
  exact_mod_cast key

theorem fock_deltaAt (τ : D.what₂.Tau) {p q : ℕ} (hm : p + q ≤ m) (hpn : p ≤ n) (hqn : q ≤ n) (ap am : ℕ → ℕ)
    (hap : Antitone ap) (ham : Antitone am) :
    Formalism.E.fock (deltaAt (D := D) (m := m) (n := n) τ p ap q am) (deltaAt τ p ap q am) =
      (hookOf p ap : ℂ) * (hookOf q am : ℂ) := by
  have hp : Antitone (fun i : Fin p => ap i) := fun i j h => hap (Fin.le_iff_val_le_val.mp h)
  have hq : Antitone (fun i : Fin q => am i) := fun i j h => ham (Fin.le_iff_val_le_val.mp h)
  rw [deltaAt_eq τ hm hpn hqn, GlobalTheory.JointHarm.fock_rename_mul (embTop_injective τ _) (embBot_injective τ hm)
      (embTop_ne_embBot τ hm),
    GlobalTheory.MinorNorm.hookNorm _ _ _ _ hp, GlobalTheory.MinorNorm.hookNormBottom _ _ _ _ hq,
    hookOf_eq_hookProd _ _ hap, hookOf_eq_hookProd _ _ ham]

theorem fock_delta (D : D7) (m n : ℕ) (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ)
    (h1 : ∀ τ, p τ + q τ ≤ m) (h2 : ∀ τ, p τ ≤ n ∧ q τ ≤ n) (h3 : ∀ τ, Antitone (ap τ) ∧ Antitone (am τ)) :
    Formalism.E.fock (Formalism.IndefR.Datum.delta (D := D) (m := m) (n := n) p q ap am) (Formalism.IndefR.Datum.delta p q ap am) =
      ∏ τ, ((hookOf (p τ) (ap τ) : ℂ) * (hookOf (q τ) (am τ) : ℂ)) := by
  classical
  have hmem : ∀ τ, deltaAt (D := D) (m := m) (n := n) τ (p τ) (ap τ) (q τ) (am τ) ∈
      supported ℂ {v : FVar D m n | v.1 = τ} := fun τ => by
    rw [deltaAt_eq τ (h1 τ) (h2 τ).1 (h2 τ).2]
    exact minorProduct_rename_mem_supported_place τ (h1 τ) _ _
  unfold Formalism.IndefR.Datum.delta
  rw [fock_prod_of_supported (fun τ => {v : FVar D m n | v.1 = τ})
    (fun a b hab => Set.disjoint_left.mpr fun v ha hb => hab (ha.symm.trans hb)) _ _ hmem hmem Finset.univ]
  exact Finset.prod_congr rfl fun τ _ =>
    fock_deltaAt τ (h1 τ) (h2 τ).1 (h2 τ).2 _ _ (h3 τ).1 (h3 τ).2

end GlobalTheory.LowRowFock
end
end

section

open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart

theorem _root_.GlobalTheory.T.formalGroupDetPowDepth_le_of_integralLogHom : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)), ∀ (i d d' k : ℕ) (G : LogFGL v d) (G' : LogFGL v d') (φ : Fin d' → MvPowerSeries (Fin d) C) (M : Matrix (Fin d') (Fin d) C), IsIntHom G G' φ M → ∀ u : Fin i → Fin d → C, detDepth G u k ≤ detDepth G' (fun a => M.mulVec (u a)) k := by
  first | exact @GlobalTheory.DepthMono.detDepth_le_of_isIntHom | exact GlobalTheory.DepthMono.detDepth_le_of_isIntHom | (intros; apply GlobalTheory.DepthMono.detDepth_le_of_isIntHom <;> assumption)
end
