module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle142
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle237
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StrongApproximationDecomposition
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle115
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle155
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1084
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle293
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle219
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle149
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle325
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.MeasureTheory.Group.ModularCharacter
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VolumeFlatSection
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle385

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt

noncomputable section

namespace GlobalTheory.ResLift

open GlobalTheory.AdelicU

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)}

def swapProj (φ : SplitProj D v) : D.host.E ⊗[D.host.F] Fv D.host.F v →+* Fv D.host.F v :=
  φ.toRingHom.comp (Algebra.TensorProduct.comm D.host.F D.host.E (Fv D.host.F v)).toAlgHom.toRingHom

theorem swapProj_one_tmul (φ : SplitProj D v) (a : Fv D.host.F v) : swapProj φ ((1 : D.host.E) ⊗ₜ[D.host.F] a) = a := by
  change φ (a ⊗ₜ[D.host.F] (1 : D.host.E)) = a
  exact φ.commutes a

theorem swapProj_prV (φ : SplitProj D v) (z : EAf D) : swapProj φ (Formalism.UG.prV v z) = GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul b y => rfl

theorem swapProj_prV_oToS (φ : SplitProj D v) (x : 𝓞 D.host.E) :
    swapProj φ (Formalism.UG.prV v (Formalism.L2.DIV.oToS D.host.F D.host.E x).1) = GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (x : D.host.E) := by
  rw [swapProj_prV, Formalism.L2.DIV.oToS_coe]
  change φ ((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v 1) ⊗ₜ[D.host.F] (x : D.host.E)) = _
  rw [map_one]
  rfl

theorem isIdemOf_idem (φ : SplitProj D v) : IsIdemOf φ (GlobalTheory.EmbChart.idem (GlobalTheory.SplitProjChart.emb φ)) := by
  refine ⟨GlobalTheory.EmbChart.isSplitIdem_idem _, ?_, GlobalTheory.SplitProjChart.rdA_idem φ⟩
  rw [GlobalTheory.EmbChart.cA_idem, GlobalTheory.EmbChart.idem, ← LinearMap.map_add (f := _), add_sub_cancel]
  rfl

theorem eq_splitPrime {φ : SplitProj D v} {PP : Pl D.host.E} (hφ : IsProjAt φ PP) :
    PP = splitPrime (GlobalTheory.SplitProjChart.emb φ) :=
  HeightOneSpectrum.ext (Ideal.ext fun x => (hφ x).trans (mem_splitPrime (GlobalTheory.SplitProjChart.emb φ) x).symm)

theorem exists_mem_only (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) : ∃ p ∈ (splitPrime τ).asIdeal,
    ∀ P : HeightOneSpectrum (𝓞 D.host.E), P.under (𝓞 D.host.F) = v → p ∈ P.asIdeal → P = splitPrime τ := by
  obtain ⟨p, hp, hp'⟩ : ∃ p ∈ (splitPrime τ).asIdeal, p ∉ (splitPrime (τ.comp D.sp.cm.sig)).asIdeal := by
    by_contra hc
    push Not at hc
    have h := (splitPrime τ).isMaximal.eq_of_le (splitPrime (τ.comp D.sp.cm.sig)).isPrime.ne_top hc
    exact splitPrime_comp_ne (isCMExt_host D) τ (HeightOneSpectrum.ext h.symm)
  refine ⟨p, hp, fun P hP hpP => ?_⟩
  have hm : P.asIdeal ∈ v.asIdeal.primesOver (𝓞 D.host.E) := ⟨P.isPrime, ⟨hP ▸ rfl⟩⟩
  rw [primesOver_eq_split (isCMExt_host D) τ] at hm
  rcases hm with h | h
  · exact HeightOneSpectrum.ext h
  · exact absurd (h ▸ hpP) hp'

theorem resS_eq {φ : SplitProj D v} {PP : Pl D.host.E} (hφ : IsProjAt φ PP)
    (s : Formalism.L2.Herm.intAf D.host.F D.host.E) (x : 𝓞 D.host.E)
    (h : Valued.v (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ s.1 - GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (x : D.host.E)) < 1) :
    resS D.host.F PP s = Ideal.Quotient.mk PP.asIdeal x := by
  obtain ⟨p, hp, hp'⟩ := exists_mem_only (GlobalTheory.SplitProjChart.emb φ)
  rw [← eq_splitPrime hφ] at hp hp'
  obtain ⟨ρ, ι, hρ, hρr⟩ := GlobalTheory.SplitResidue.exists_residue_equiv D.host.F D.host.E v PP
    (swapProj φ) p (swapProj_one_tmul φ) ((hφ p).1 hp) hp'
  have h0 : IsLocalRing.residue _ (ρ s) = IsLocalRing.residue _ (ρ (oToS D.host.F D.host.E x)) := by
    refine Ideal.Quotient.eq.2 ((GlobalTheory.SplitResidue.mem_maximalIdeal_iff v _).2 ?_)
    rw [AddSubgroupClass.coe_sub, hρ, hρ, swapProj_prV_oToS, swapProj_prV]
    exact h
  rw [hρr, hρr, resS_oToS] at h0
  exact ι.injective h0

theorem exists_unit_lift {A K : Type} [CommRing A] [CommRing K] (π : A →+* K) {e : A} (hee : e * e = e)
    (hs : Function.Surjective π) (hk : ∀ a, π a = 0 ↔ e * a = 0) (u : Kˣ) :
    ∃ x : Aˣ, (1 - e) * (x : A) = 1 - e ∧ e * ((x : A) - 1) = (x : A) - 1 ∧ π x = u := by
  obtain ⟨U, hU⟩ := hs (u : K)
  obtain ⟨U', hU'⟩ := hs ((u⁻¹ : Kˣ) : K)
  have h1 : e * (U * U' - 1) = 0 := (hk _).1 (by rw [map_sub, map_mul, hU, hU', map_one, Units.mul_inv, sub_self])
  have h2 : π (1 - e) = 0 := (hk _).2 (by linear_combination -hee)
  have h3 : π e = 1 := by
    rw [map_sub, map_one, sub_eq_zero] at h2
    exact h2.symm
  refine ⟨⟨e * U + (1 - e), e * U' + (1 - e), by linear_combination h1 + (U * U' - U - U' + 1) * hee,
    by linear_combination h1 + (U * U' - U - U' + 1) * hee⟩, ?_, ?_, ?_⟩
  · change (1 - e) * (e * U + (1 - e)) = 1 - e
    linear_combination (1 - U) * hee
  · change e * (e * U + (1 - e) - 1) = e * U + (1 - e) - 1
    linear_combination (U - 1) * hee
  · change π (e * U + (1 - e)) = u
    rw [map_add (f := _), map_mul, h2, h3, hU, one_mul, add_zero]

theorem liftsChar_of_resAt : ∀ (D : D7) (χ : (AE D)ˣ →* Circle) (PP : Pl D.host.E) (a : (kP PP)ˣ →* ℂˣ), GlobalTheory.StepLaw.ResAt χ PP a → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → ∀ μ : (Fv D.host.F v)ˣ →* ℂˣ, (∀ (x : (AE D)ˣ) (y : (Fv D.host.F v)ˣ), (∃ e, IsIdemOf φ e ∧ (1 - e) * (x : AE D) = 1 - e ∧ rdA φ (x : AE D) = y) → μ y = Circle.toUnits (χ x)) → LiftsChar φ PP μ a := by
  intro D χ PP a hres v φ hφ μ hμ u k ⟨x0, hx0k, hx0⟩
  have he := isIdemOf_idem φ
  generalize GlobalTheory.EmbChart.idem (GlobalTheory.SplitProjChart.emb φ) = e at he
  have hch := (GlobalTheory.SplitProjChart.chart_rdA D v φ e he).1
  have hAt : Formalism.L2.NTheta.IsIdemAt e PP := (((GlobalTheory.SplitIdemDict.idem_dictionary D).2 v φ PP hφ).2.2 e he).1
  obtain ⟨x, h1, h2, h3⟩ := exists_unit_lift (rdA φ) he.1.1 hch.1 hch.2.1 u
  have hu : (u : Fv D.host.F v) ∈ v.adicCompletionIntegers D.host.F := by
    have h4 : (u : Fv D.host.F v) - GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (x0 : D.host.E) ∈ v.adicCompletionIntegers D.host.F := hx0.le
    have h5 : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (x0 : D.host.E) ∈ v.adicCompletionIntegers D.host.F :=
      apply_coe_mem (GlobalTheory.SplitProjChart.emb φ) x0
    have h6 := add_mem h4 h5
    rwa [sub_add_cancel] at h6
  have hint : toEAf D (x : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    have h4 : finPart D (e * ((x : AE D) - 1)) ∈ intAE D := by
      refine (hch.2.2.2 _).2 (GlobalTheory.SplitHecke.isInt_Ov.2 ?_)
      rw [RingHom.map_sub, h3, RingHom.map_one]
      exact sub_mem hu (one_mem _)
    have h5 := (GlobalTheory.SplitDec.int_iff _).1 h4
    rw [h2, RingHom.map_sub, RingHom.map_one] at h5
    have h6 := add_mem h5 (one_mem _)
    rwa [sub_add_cancel] at h6
  have hk : resS D.host.F PP ⟨_, hint⟩ = Ideal.Quotient.mk PP.asIdeal x0 := by
    refine resS_eq hφ _ x0 ?_
    change Valued.v (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ (toEAf D (x : AE D)) - _) < 1
    rw [GlobalTheory.SplitProjChart.rdE_toEAf, h3]
    exact hx0
  rw [hμ x u ⟨e, he, h1, h3⟩]
  exact Units.ext (hres e hAt x h2 hint k (hk.trans hx0k).symm)

end GlobalTheory.ResLift

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HeckeAdjEigen

variable {D : D7} {V : HSp D}

open GlobalTheory.FinZeta (bddAut bddRep coe_bddRep)

theorem exists_dual_rep (J : Set (GA D V)) (χ : GA D V → ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ) (R : Finset (GA D V))
    (e f : Formalism.L2.Theta.AE D) (ϖ : 𝓞 D.host.E) (α : GA D V)
    (hS : OffS D Sb P) (hef : IsPrimeIdem P e f) (hϖ : ϖ ∈ P.asIdeal) (hϖ2 : ϖ ∉ P.asIdeal ^ 2)
    (hd : d.Pairwise (fun a b => b ≤ a)) (hJ : ∀ g, SuppF V f g → (g ∈ J ↔ g ∈ KsphC V ∅))
    (hχ : ∀ g ∈ J, SuppF V f g → χ g = 1) (hα : SuppF V f α) (hdiv : DivAt V e (ϖ : D.host.E) d α)
    (hrep : IsCosetRep V {k | k ∈ J ∧ SuppF V f k} α R) :
    ∃ R' : Finset (GA D V), Hecke₂ V J χ Sb P (dualLab d) R' ∧ R'.card = R.card ∧
      ∀ γ ∈ R', ∃ k₁ ∈ {k | k ∈ J ∧ SuppF V f k}, ∃ k₂ ∈ {k | k ∈ J ∧ SuppF V f k}, γ = k₁ * α⁻¹ * k₂ := by
  obtain ⟨he, v, hf⟩ := GlobalTheory.HeckeDual.idem_of_isPrimeIdem hef
  obtain ⟨a, rfl⟩ := (GlobalTheory.HeckeDual.suppF_iff V hf α).1 hα
  obtain ⟨δ, hδ, hσδ⟩ := GlobalTheory.HeckeDual.exists_skew D
  haveI := GlobalTheory.HeckeDual.isLattice_frameLat V
  have hK : ∀ g, g ∈ {k | k ∈ J ∧ SuppF V f k} ↔
      ∃ k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram (GlobalTheory.AdelicU.frameLat V) v,
        GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v k = g := fun g => by
    constructor
    · rintro ⟨h1, h2⟩
      have h3 := (hJ g h2).1 h1
      obtain ⟨k, rfl⟩ := (GlobalTheory.HeckeDual.suppF_iff V hf g).1 h2
      rw [GlobalTheory.AdelicU.KsphC_eq] at h3
      have h4 := (GlobalTheory.AdelicU.mem_levelOff.1 h3).2.2 v (Finset.notMem_empty v)
      rw [GlobalTheory.AdelicU.proj_emb_self] at h4
      exact ⟨k, h4, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      have h2 := (GlobalTheory.HeckeDual.suppF_iff V hf _).2 ⟨k, rfl⟩
      refine ⟨(hJ _ h2).2 ?_, h2⟩
      rw [GlobalTheory.AdelicU.KsphC_eq]
      exact GlobalTheory.AdelicU.emb_mem_levelOff (Finset.notMem_empty v) hk
  obtain ⟨R', h1, h2, h3⟩ := GlobalTheory.HeckeDual.exists_rep_inv
    (GlobalTheory.HeckeDual.modular_eq_one D.sp.cm.sig V.gram (fun x => star_star x) hδ hσδ
      ((GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).2 V) v)
    (GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v) (GlobalTheory.AdelicU.emb_injective _ _ v) _
    (GlobalTheory.AdelicU.isOpen_stabLoc _ _ _ v) (GlobalTheory.AdelicU.isCompact_stabLoc _ _ _ v) _ hK a R
    (fun γ hγ => (hrep.1 γ hγ).2) hrep.2
  have hϖ0 : (ϖ : D.host.E) ≠ 0 := fun h => hϖ2 (by
    rw [show ϖ = 0 from RingOfIntegers.ext h]
    exact zero_mem _)
  refine ⟨R', ⟨e, f, ϖ, _, hS, hef, hϖ, hϖ2, ?_, hJ, hχ, (GlobalTheory.HeckeDual.suppF_iff V hf _).2 (inv_mem ⟨a, rfl⟩),
    (GlobalTheory.DivDual.divAt_inv_and_mul V e _ d _ he hϖ0 hdiv).1, fun γ hγ => (GlobalTheory.HeckeDual.suppF_iff V hf _).2 (h1 γ hγ).1,
    fun γ hγ => ⟨?_, (h1 γ hγ).2⟩, h2⟩, h3, fun γ hγ => (h1 γ hγ).2⟩
  · rw [dualLab, List.pairwise_reverse, List.pairwise_map]
    exact hd.imp fun h => neg_le_neg h
  · obtain ⟨x, rfl⟩ := (h1 γ hγ).1
    exact GlobalTheory.AdelicU.mem_finPts.2 (GlobalTheory.AdelicU.projInf_emb _ _ v x)

theorem form_sum (B : bddAut V →ₗ[ℂ] bddAut V →ₛₗ[starRingEnd ℂ] ℂ)
    (hinv : ∀ g v w, B (bddRep V g v) (bddRep V g w) = B v w) (K : Set (GA D V)) (F : bddAut V)
    (hF : ∀ k ∈ K, bddRep V k F = F) (α : GA D V) (R : Finset (GA D V))
    (hR : ∀ γ ∈ R, ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = k₁ * α * k₂) :
    B (∑ γ ∈ R, bddRep V γ F) F = (R.card : ℂ) * B (bddRep V α F) F := by

  rw [map_sum, LinearMap.sum_apply]
  rw [Finset.sum_congr rfl (g := fun _ => B (bddRep V α F) F), Finset.sum_const, nsmul_eq_mul]
  intro γ hγ
  obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := hR γ hγ
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hF k₂ hk₂]
  have h := hinv k₁ (bddRep V α F) F
  rwa [hF k₁ hk₁] at h

theorem form_inv (B : bddAut V →ₗ[ℂ] bddAut V →ₛₗ[starRingEnd ℂ] ℂ)
    (hsym : ∀ v w, B w v = starRingEnd ℂ (B v w))
    (hinv : ∀ g v w, B (bddRep V g v) (bddRep V g w) = B v w) (F : bddAut V) (α : GA D V) :
    B (bddRep V α⁻¹ F) F = starRingEnd ℂ (B (bddRep V α F) F) := by
  have h := hinv α⁻¹ F (bddRep V α F)
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at h
  rw [h, hsym]

theorem coe_sum_bddRep (f : GA D V → ℂ) (hf : f ∈ bddAut V) (R : Finset (GA D V)) :
    ((∑ γ ∈ R, bddRep V γ ⟨f, hf⟩ : bddAut V) : GA D V → ℂ) = heckeLin V R f := by
  funext g
  rw [Submodule.coe_sum, Finset.sum_apply, heckeLin_apply]
  rfl

theorem heckeLin_eq_conj_of_dualLab : ∀ (D : D7) (V : HSp D) (J : Set (GA D V)) (χ : GA D V → ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))), SphOff J χ Sb → ∀ f ∈ GlobalTheory.FinZeta.bddAut V, (∀ k ∈ J, ∀ g, f (g * k) = χ k * f g) → ∀ e : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ, (∀ P d R, Hecke₂ V J χ Sb P d R → heckeLin V R f = e P (dualLab d) • f) → ∀ P d R, Hecke₂ V J χ Sb P d R → heckeLin V R f = conj (e P d) • f := by
  intro D V J χ Sb _ f hf hJχ ev heig P d R hR
  obtain ⟨e, f', ϖ, α, hS, hef, hϖ, hϖ2, hd, hJ, hχ, hα, hdiv, -, hrep⟩ := id hR
  obtain ⟨R', hR', hcard, hR're⟩ := exists_dual_rep J χ Sb P d R e f' ϖ α hS hef hϖ hϖ2 hd hJ hχ hα hdiv hrep
  obtain ⟨B, hsym, hpos, hinv⟩ := (GlobalTheory.FinZeta.bddRep_unitarisable_and_bounded D V).1
  set F : bddAut V := ⟨f, hf⟩ with hFdef
  have hFK : ∀ k ∈ {k | k ∈ J ∧ SuppF V f' k}, bddRep V k F = F := fun k hk => by
    refine Subtype.ext (funext fun g => ?_)
    rw [coe_bddRep]
    show f (g * k) = f g
    rw [hJχ k hk.1, hχ k hk.1 hk.2, one_mul]
  have e1 := heig P d R hR
  have e2 := heig P (dualLab d) R' hR'
  rw [show dualLab (dualLab d) = d by simp [dualLab, List.map_reverse]] at e2
  have s1 : (∑ γ ∈ R, bddRep V γ F) = ev P (dualLab d) • F := Subtype.ext (by
    rw [coe_sum_bddRep, e1]; rfl)
  have s2 : (∑ γ ∈ R', bddRep V γ F) = ev P d • F := Subtype.ext (by
    rw [coe_sum_bddRep, e2]; rfl)
  have t1 := form_sum B hinv _ F hFK α R (fun γ hγ => (hrep.1 γ hγ).2)
  have t2 := form_sum B hinv _ F hFK α⁻¹ R' hR're
  rw [form_inv B hsym hinv, s2, hcard, map_smul, LinearMap.smul_apply, smul_eq_mul] at t2
  rw [s1, map_smul, LinearMap.smul_apply, smul_eq_mul] at t1
  by_cases h0 : F = 0
  · have : f = 0 := congrArg Subtype.val h0
    subst this
    rw [map_zero, smul_zero]
  · have hb : B F F ≠ 0 := fun h => by
      have := hpos F h0
      rw [h, Complex.zero_re] at this
      exact lt_irrefl _ this
    have hbr : starRingEnd ℂ (B F F) = B F F := (hsym F F).symm
    have key : ev P (dualLab d) = starRingEnd ℂ (ev P d) := by
      apply mul_right_cancel₀ hb
      rw [t1, ← hbr, ← map_mul, t2, map_mul, map_natCast, Complex.conj_conj]
    rw [e1, key]

end GlobalTheory.HeckeAdjEigen
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.Core.Rk.FubiniPlace



theorem integral_split_place : ∀ (D : D7) (A : HSp D) (m : Measure (GA D A)), m.IsHaarMeasure → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (μ : Measure (GlobalTheory.FinZeta.Gv A v)), μ.IsHaarMeasure → ∀ J : Subgroup (GlobalTheory.FinZeta.Gv A v), IsOpen (J : Set (GlobalTheory.FinZeta.Gv A v)) → μ J = 1 → ∀ E : Set (GA D A), MeasurableSet E → (∀ x y, x * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y ∈ E ↔ x ∈ E) → ∀ (F : GA D A → ℂ) (ζ : GlobalTheory.FinZeta.Gv A v → ℂ), Integrable ζ μ → (∀ y ∈ J, ζ y = 1) → (∀ x ∈ E, GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x = 1 → ∀ y, F (x * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y) = ζ y * F x) → IntegrableOn F (E ∩ {g | GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ J}) m → IntegrableOn F E m ∧ ∫ g in E, F g ∂m = (∫ y, ζ y ∂μ) * ∫ g in E ∩ {g | GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ J}, F g ∂m := by
  intro D A m hm v μ hμ J hJo hJ1 E hE hEr F ζ hζ hζJ hF hFi
  have hec : Continuous (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v) := GlobalTheory.AdelicU.continuous_emb _ _ v
  have hpc : Continuous (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v) := GlobalTheory.AdelicU.continuous_proj _ _ v
  have hPm : MeasurableSet {g : GA D A | GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ J} := (hJo.preimage hpc).measurableSet
  have hUm : MeasurableSet (E ∩ {g : GA D A | GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ J}) := hE.inter hPm
  have hJm : MeasurableSet (J : Set (GlobalTheory.FinZeta.Gv A v)) := hJo.measurableSet

  have hright : ∀ k ∈ J, μ.map (fun y => y * k) = μ := by
    intro k hk
    have h := Measure.map_right_mul_eq_modularCharacterFun_smul μ k
    have h2 := congrArg (fun m' : Measure (GlobalTheory.FinZeta.Gv A v) => m' (J : Set (GlobalTheory.FinZeta.Gv A v))) h
    simp only [Measure.coe_nnreal_smul_apply] at h2
    rw [Measure.map_apply (measurable_mul_const _) hJm,
      show (fun x => x * k) ⁻¹' (J : Set (GlobalTheory.FinZeta.Gv A v)) = J from Set.ext fun x => J.mul_mem_cancel_right hk,
      hJ1, mul_one] at h2
    have h3 : Measure.modularCharacterFun k = 1 := by exact_mod_cast h2.symm
    rw [h, h3, one_smul]

  have dec : ∀ x : GA D A, GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v (x * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x)⁻¹) = 1 := by
    intro x; rw [map_mul, GlobalTheory.AdelicU.proj_emb_self, mul_inv_cancel]
  have dec2 : ∀ x : GA D A, x = (x * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x)⁻¹) * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x) := by
    intro x; rw [map_inv, inv_mul_cancel_right]
  have shift : ∀ (x : GA D A) (y : GlobalTheory.FinZeta.Gv A v),
      GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * x = (x * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x)⁻¹) * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v (y * GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x) := by
    intro x y
    have hc := (GlobalTheory.AdelicU.commute_emb D.sp.cm.sig A.gram y (dec x)).eq
    calc GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * x = GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * (x * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x)⁻¹) * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x) := by
          rw [mul_assoc, ← dec2]
      _ = _ := by rw [hc, mul_assoc, ← map_mul]
  have hEl : ∀ (y : GlobalTheory.FinZeta.Gv A v) (x : GA D A), GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * x ∈ E ↔ x ∈ E := by
    intro y x
    have h1 := hEr (x * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x)⁻¹) (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x)
    rw [← dec2 x] at h1
    rw [shift, hEr, h1]
  have key : ∀ x ∈ (E ∩ {g : GA D A | GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ J}), ∀ y, F (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * x) = F x * ζ (y * GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x) := by
    intro x hx y
    have h1 := hEr (x * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x)⁻¹) (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x)
    rw [← dec2 x] at h1
    have hx' : x * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x)⁻¹ ∈ E := h1.1 hx.1
    have h2 := hF _ hx' (dec x) (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x)
    rw [← dec2 x] at h2
    rw [shift, hF _ hx' (dec x), h2, hζJ _ hx.2, one_mul, mul_comm]
  classical

  let c : GA D A → GlobalTheory.FinZeta.Gv A v := fun x => if GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x ∈ J then GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x else 1
  have hcm : Measurable c := Measurable.ite hPm hpc.measurable measurable_const
  have hR : MeasurePreserving (fun q : GA D A × GlobalTheory.FinZeta.Gv A v => (q.1, q.2 * c q.1)) (m.prod μ) (m.prod μ) := by
    refine MeasurePreserving.skew_product (g := fun x y => y * c x) (MeasurePreserving.id m)
      (measurable_snd.mul (hcm.comp measurable_fst) : Measurable fun p : GA D A × GlobalTheory.FinZeta.Gv A v => p.2 * c p.1)
      (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x ∈ J
    · simp only [c, if_pos hx]; exact hright _ hx
    · simp only [c, if_neg hx, mul_one, Measure.map_id']
  let g0 : GA D A × GlobalTheory.FinZeta.Gv A v → ℂ := fun q => (E ∩ {g : GA D A | GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ J}).indicator F q.1 * ζ q.2
  have hg0 : Integrable g0 (m.prod μ) := Integrable.mul_prod ((integrable_indicator_iff hUm).2 hFi) hζ
  let f : GA D A × GlobalTheory.FinZeta.Gv A v → ℂ := fun q => (E ∩ {g : GA D A | GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ J}).indicator (fun x => F (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v q.2 * x)) q.1
  have hfg : f = g0 ∘ (fun q : GA D A × GlobalTheory.FinZeta.Gv A v => (q.1, q.2 * c q.1)) := by
    funext q
    by_cases hx : q.1 ∈ (E ∩ {g : GA D A | GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ J})
    · have hx2 : GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v q.1 ∈ J := hx.2
      simp only [f, g0, Function.comp_apply, c, if_pos hx2]
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, key q.1 hx]
    · simp only [f, g0, Function.comp_apply, Set.indicator_of_notMem hx, zero_mul]
  have hf : Integrable f (m.prod μ) := by
    rw [hfg]; exact (hR.integrable_comp hg0.aestronglyMeasurable).2 hg0
  have hfint : ∫ q, f q ∂(m.prod μ) = ∫ q, g0 q ∂(m.prod μ) := by
    have h := integral_map (μ := m.prod μ) hR.measurable.aemeasurable (f := g0)
      (by rw [hR.map_eq]; exact hg0.aestronglyMeasurable)
    rw [hR.map_eq] at h
    rw [hfg]; exact h.symm

  let T : GA D A × GlobalTheory.FinZeta.Gv A v → GA D A × GlobalTheory.FinZeta.Gv A v := fun q => (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v q.2 * q.1, q.2)
  have hTp : MeasurePreserving T (m.prod μ) (m.prod μ) := by
    have h1 : MeasurePreserving (fun p : GlobalTheory.FinZeta.Gv A v × GA D A => (p.1, GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v p.1 * p.2)) (μ.prod m) (μ.prod m) :=
      MeasurePreserving.skew_product (MeasurePreserving.id μ)
        ((hec.comp continuous_fst).mul continuous_snd).measurable
        (Filter.Eventually.of_forall fun y => map_mul_left_eq_self m (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y))
    have h2 : MeasurePreserving (Prod.swap : GA D A × GlobalTheory.FinZeta.Gv A v → GlobalTheory.FinZeta.Gv A v × GA D A) (m.prod μ) (μ.prod m) :=
      Measure.measurePreserving_swap
    have h3 : MeasurePreserving (Prod.swap : GlobalTheory.FinZeta.Gv A v × GA D A → GA D A × GlobalTheory.FinZeta.Gv A v) (μ.prod m) (m.prod μ) :=
      Measure.measurePreserving_swap
    have h4 := (h3.comp h1).comp h2
    have e : T = (Prod.swap ∘ (fun p : GlobalTheory.FinZeta.Gv A v × GA D A => (p.1, GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v p.1 * p.2))) ∘ Prod.swap := by
      funext p; rfl
    rw [e]; exact h4
  let Te : (GA D A × GlobalTheory.FinZeta.Gv A v) ≃ᵐ (GA D A × GlobalTheory.FinZeta.Gv A v) :=
    { toFun := T
      invFun := fun q => ((GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v q.2)⁻¹ * q.1, q.2)
      left_inv := fun q => by simp [T]
      right_inv := fun q => by simp [T]
      measurable_toFun := (((hec.comp continuous_snd).mul continuous_fst).prodMk continuous_snd).measurable
      measurable_invFun := ((((hec.comp continuous_snd).inv).mul continuous_fst).prodMk continuous_snd).measurable }
  have hT : MeasurePreserving Te (m.prod μ) (m.prod μ) := hTp
  let f₂ : GA D A × GlobalTheory.FinZeta.Gv A v → ℂ :=
    fun q => {q : GA D A × GlobalTheory.FinZeta.Gv A v | (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v q.1)⁻¹ * q.2 ∈ J}.indicator (fun q => E.indicator F q.1) q
  have hf₂T : ∀ q, f₂ (Te q) = f q := by
    rintro ⟨x, y⟩
    have hp : (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * x))⁻¹ * y = (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x)⁻¹ := by
      rw [map_mul, GlobalTheory.AdelicU.proj_emb_self, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
    show {q : GA D A × GlobalTheory.FinZeta.Gv A v | (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v q.1)⁻¹ * q.2 ∈ J}.indicator (fun q => E.indicator F q.1) (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * x, y) =
      (E ∩ {g : GA D A | GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ J}).indicator (fun x => F (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * x)) x
    by_cases h2 : GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x ∈ J
    · have hq : (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * x, y) ∈ {q : GA D A × GlobalTheory.FinZeta.Gv A v | (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v q.1)⁻¹ * q.2 ∈ J} := by
        show (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * x))⁻¹ * y ∈ J
        rw [hp]; exact J.inv_mem h2
      rw [Set.indicator_of_mem hq]
      by_cases h1 : x ∈ E
      · rw [Set.indicator_of_mem ((hEl y x).2 h1), Set.indicator_of_mem (show x ∈ (E ∩ {g : GA D A | GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ J}) from ⟨h1, h2⟩)]
      · rw [Set.indicator_of_notMem (mt (hEl y x).1 h1), Set.indicator_of_notMem (by exact fun h => h1 h.1)]
    · have hq : (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * x, y) ∉ {q : GA D A × GlobalTheory.FinZeta.Gv A v | (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v q.1)⁻¹ * q.2 ∈ J} := by
        show ¬ (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * x))⁻¹ * y ∈ J
        rw [hp, inv_mem_iff]; exact h2
      rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem (by exact fun h => h2 h.2)]
  have hf₂ : Integrable f₂ (m.prod μ) := by
    refine (hT.integrable_comp_emb Te.measurableEmbedding).1 ?_
    have : f₂ ∘ Te = f := funext hf₂T
    rw [this]; exact hf
  have hCm : ∀ a : GlobalTheory.FinZeta.Gv A v, MeasurableSet {y : GlobalTheory.FinZeta.Gv A v | a⁻¹ * y ∈ J} :=
    fun a => (hJo.preimage (continuous_const.mul continuous_id)).measurableSet
  have hμC : ∀ a : GlobalTheory.FinZeta.Gv A v, μ {y : GlobalTheory.FinZeta.Gv A v | a⁻¹ * y ∈ J} = 1 := by
    intro a
    rw [← hJ1]
    exact measure_preimage_mul μ a⁻¹ _
  have inner : ∀ w, ∫ y, f₂ (w, y) ∂μ = E.indicator F w := by
    intro w
    have : (fun y => f₂ (w, y)) = {y : GlobalTheory.FinZeta.Gv A v | (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v w)⁻¹ * y ∈ J}.indicator (fun _ => E.indicator F w) := by
      funext y; rfl
    rw [this, integral_indicator_const _ (hCm _), Measure.real, hμC, ENNReal.toReal_one, one_smul]
  have hFE : Integrable (E.indicator F) m := by
    have h := hf₂.integral_prod_left
    simp_rw [inner] at h
    exact h
  refine ⟨(integrable_indicator_iff hE).1 hFE, ?_⟩
  calc ∫ g in E, F g ∂m = ∫ w, E.indicator F w ∂m := (integral_indicator hE).symm
    _ = ∫ q, f₂ q ∂(m.prod μ) := by rw [integral_prod f₂ hf₂]; simp_rw [inner]
    _ = ∫ q, f₂ (Te q) ∂(m.prod μ) := (hT.integral_comp' f₂).symm
    _ = ∫ q, f q ∂(m.prod μ) := by simp_rw [hf₂T]
    _ = ∫ q, g0 q ∂(m.prod μ) := hfint
    _ = (∫ x, (E ∩ {g : GA D A | GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ J}).indicator F x ∂m) * ∫ y, ζ y ∂μ := integral_prod_mul _ _
    _ = _ := by rw [integral_indicator hUm, mul_comm]

end GlobalTheory.Core.Rk.FubiniPlace
end
end
