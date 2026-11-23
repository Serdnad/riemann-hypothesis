module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle020
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle245
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle244
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle270
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle205
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle405
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle022
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle327
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle404
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualOrthAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle369
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle374
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle320
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle398
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle408
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle192
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupClosedEmbeddingIntegral
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)

noncomputable section

namespace GlobalTheory.ChainTw.ExactNS

variable {D : D7}

theorem petersson_conj (V : HSp D) (ν : Measure (GA D V)) (hν : ν.IsHaarMeasure) (X : Set (GA D V))
    (hX : IsFundamentalDomain (GQ V) X ν)
    (f g : GA D V → ℂ) (hf : ∀ γ ∈ GQ V, ∀ h, f (γ * h) = f h) (hg : ∀ γ ∈ GQ V, ∀ h, g (γ * h) = g h) :
    GlobalTheory.Cusp.petersson V ν (fun h => conj (f h)) (fun h => conj (g h)) = conj (Lift.pet ν X f g) := by
  haveI := hν
  have hL : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) (fun h => conj (f h) * conj (conj (g h))) := fun γ hγ h => by
    simp only [hf γ hγ, hg γ hγ]
  change ∫ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (fun h => conj (f h) * conj (conj (g h))) q ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure (GQ V) ν = _
  rw [GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure hX]
  simp only [hL.descend_mk]
  unfold Lift.pet
  rw [← integral_conj]
  simp only [map_mul]

theorem up_conj {c : Com D} {s s' : PiLocalization₂ D} {w : Twist D} {k : ℕ} (p : Step c s s') (hp : IsStep w (k + 1) p)
    (hν : s.ν.IsHaarMeasure) (hX : IsFundamentalDomain (GQ s.V) s.fd s.ν) (φ : PolF D s'.V.rank s.V.rank)
    (F : GA D s.V → ℂ) (hF : ∀ γ ∈ GQ s.V, ∀ g, F (γ * g) = F g) :
    GlobalTheory.Core.Rk.IP.up p.ω s.ν (p.pt φ) (fun x => conj (F x)) = fun h => conj (p.up φ F h) := by
  haveI := hν
  funext h
  have hΦ : IsThetaFunO c.ψ s.V s'.V (p.pt φ) := hp.theta φ
  have hθl : ∀ γ ∈ GQ s.V, ∀ g, thetaKO p.ω (γ * g) h (p.pt φ) = thetaKO p.ω g h (p.pt φ) := by
    intro γ hγ g
    have e : ((γ * g, h) : GA D s.V × GA D s'.V) = (γ, 1) * (g, h) := by simp
    simp only [thetaKO, e, map_mul, Module.End.mul_apply]
    exact hp.weil.om_aut γ hγ 1 (one_mem _) _ (hp.weil.om_pres _ _ hΦ)
  have hL : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ s.V) (fun g => thetaKO p.ω g h (p.pt φ) * conj (F g)) := fun γ hγ x => by
    simp only [hθl γ hγ, hF γ hγ]
  simp only [GlobalTheory.Core.Rk.IP.up, Step.up]
  change ∫ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ s.V) _ q ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure (GQ s.V) s.ν = _
  rw [GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure hX]
  simp only [hL.descend_mk]
  rw [← integral_conj]
  simp only [map_mul, Complex.conj_conj]

theorem up_leftInv {c : Com D} {s s' : PiLocalization₂ D} {w : Twist D} {k : ℕ} (p : Step c s s') (hp : IsStep w (k + 1) p)
    (φ : PolF D s'.V.rank s.V.rank) (F : GA D s.V → ℂ) : ∀ γ ∈ GQ s'.V, ∀ h, p.up φ F (γ * h) = p.up φ F h := by
  have hΦ : IsThetaFunO c.ψ s.V s'.V (p.pt φ) := hp.theta φ
  have hθr : ∀ g, ∀ γ ∈ GQ s'.V, ∀ h, thetaKO p.ω g (γ * h) (p.pt φ) = thetaKO p.ω g h (p.pt φ) := by
    intro g γ hγ h
    have e : ((g, γ * h) : GA D s.V × GA D s'.V) = (1, γ) * (g, h) := by simp
    simp only [thetaKO, e, map_mul, Module.End.mul_apply]
    exact hp.weil.om_aut 1 (one_mem _) γ hγ _ (hp.weil.om_pres _ _ hΦ)
  intro γ hγ h
  simp only [Step.up, hθr _ γ hγ]

theorem stepExactNS : ∀ D : D7, GlobalTheory.Core.Rk.SW.HeckeFormNS D → SoftQ D → QPeel D → LevInt D → StepExactNS D := by
  intro D hHF hSoft hPeel hLev hgap c w hw k hk s s' hs hs' p hp ipD ip hMet m X hmX mR hmR φ v hRC u₁ u₂ B hB hQ hNS l hl
  have hc : c.Is := hw.com
  obtain ⟨hr, -, hsF⟩ := id hs
  obtain ⟨hr', -, hs'F⟩ := id hs'
  have hv : PiTensorProduct.tprod ℂ v ∈ s.KF := Submodule.subset_span ⟨v, hRC.1, rfl⟩
  by_cases h0 : PiTensorProduct.tprod ℂ v = 0
  · have hz : ∀ g, zReal p m X φ v g = 0 := by
      intro g
      have hp0 := hMet.pure v v
      simp only [h0, map_zero, LinearMap.zero_apply] at hp0
      obtain ⟨τ, -, hτ⟩ := Finset.prod_eq_zero_iff.1 hp0.symm
      have h0τ : ((v τ : s.M.sm τ) : s.M.H τ) = 0 := inner_self_eq_zero.1 hτ
      simp only [zReal]
      rw [Finset.prod_eq_zero (Finset.mem_univ τ) (by rw [h0τ, inner_zero_left])]
      simp
    simp [h0, hz, Step.up, Lift.pet]
  have hF₁ : PiLocalization₂.val u₁ (PiTensorProduct.tprod ℂ v) ≠ 0 := fun h =>
    hB.1 ((hSoft c w hw k hk.le s hs).2.2.1 u₁ _ h0 h)
  have hparF : ParFun c s (PiLocalization₂.val u₁ (PiTensorProduct.tprod ℂ v)) B := hB.2 _ hF₁
  have hFlat := GlobalTheory.T.chain_stage_forms_twisted_level_le_finer_level D c w hw k hk.le s hs hr
  obtain ⟨cA, a, hcA, hcart, hJ, hmaj, hmaj_eq, hA0⟩ := GlobalTheory.ChainOnto.conj_stage_val_mem_A0_and_cartan_frame D c hc k hk.le _ hsF
  obtain ⟨-, -, -, hcartB, -, -, -, -⟩ := GlobalTheory.ChainOnto.conj_stage_val_mem_A0_and_cartan_frame D c hc (k + 1) hk _ hs'F
  obtain ⟨hwitt, htwo⟩ := GlobalTheory.ChainOnto.WittTwo.wittIndex_lt_and_two_split D c (k + 1) _ hk hs'F
  obtain ⟨hfock, -, hunrT⟩ := GlobalTheory.T.twistedChainStep_fockVectors_spherical_offS D hgap c w hw k hk s s' hs hs' p hp
  set F₁ := PiLocalization₂.val u₁ (PiTensorProduct.tprod ℂ v) with hF₁def
  set F₂ := PiLocalization₂.val u₂ (PiTensorProduct.tprod ℂ v) with hF₂def
  have hu1 : (fun g => conj (F₁ g)) ∈ GlobalTheory.Cusp.A0 c.θ s.V cA := hA0 ⟨u₁.1, hFlat u₁.2⟩ _ hv
  have hu2 : (fun g => conj (F₂ g)) ∈ GlobalTheory.Cusp.A0 c.θ s.V cA := hA0 ⟨u₂.1, hFlat u₂.2⟩ _ hv
  have hrk0 : s.V.rank = D.R.rankY k := hsF.rank
  have hrk1 : s'.V.rank = D.R.rankY (k + 1) := hs'F.rank
  have hr1 : 1 ≤ s.V.rank := by
    rw [hrk0]; simp only [Ranks.rankY, Ranks.r]; have := D.R.two_le_m; omega
  have ht2 : 2 ≤ D.R.t := by have := D.R.rank_add_five_le; omega
  have hrk : s'.V.rank = s.V.rank + D.R.t := by rw [hrk1, hrk0]; simp only [Ranks.rankY]; ring
  have hPair : GlobalTheory.Core.Rk.IP.Pair c.ψ c.θ s.V s'.V (c.chS (k + 1)) (c.chT (k + 1)) (cart s.M) (cart s'.M) D.R.t cA a p.ω
      m X :=
    { setting := ⟨hr1, by omega, hrk, hc.inf, hsF.sigOK, hcA, hcart, hcartB, hJ⟩
      maj := hmaj
      maj_eq := hmaj_eq
      weil := hp.weil
      covol := hmX }
  have hUnr : GlobalTheory.Core.Rk.IP.Unram c.ψ s.V s'.V (c.chT (k + 1)) s.Λ s'.Λ c.S (p.pt φ) (p.pt φ) :=
    ⟨hsF.selfDual, hs'F.selfDual, fun w _ h2 => htwo w h2, hunrT, (hfock φ).2.1, (hfock φ).2.1⟩
  have hsph : GlobalTheory.Core.Rk.IP.SphFun s.V s.Λ c.S (fun g => conj (F₂ g)) := by
    obtain ⟨-, hoffS, -⟩ := GlobalTheory.ChainOnto.LevelFacts.levFacts D c hc k hk.le _ hsF
    have hT := (GlobalTheory.MultMem.mem_mult_iff ..).1 ((mem_multT ..).1 (hFlat u₂.2))
    intro v' hv' κ hκ g
    obtain ⟨hκL, hκχ⟩ := hoffS v' hv' κ hκ
    have e : F₂ = PiTensorProduct.lift.symm (u₂ : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) v := by
      rw [PiTensorProduct.lift_symm]; rfl
    simp only [e]
    have hlev := hT.lev v _ hκL g
    rw [hκχ, one_mul] at hlev
    exact congrArg (starRingEnd ℂ) hlev
  have hIM : IsMajOf c s a := ⟨hmaj, hmaj_eq⟩
  obtain ⟨s₁, hs₁, hLI⟩ := hLev hgap c w hw k hk s s' hs hs' p hp ipD ip hMet m X hmX mR hmR φ v hRC a hIM
  obtain ⟨hLint, hLeq⟩ := hLI u₁ u₂
  have hint : ∃ z : ℝ, z < (D.R.t : ℝ) / 2 ∧ IntegrableOn (GlobalTheory.Core.Rk.IP.integrand p.ω s.ν m X s.Λ a (p.pt φ)
      (p.pt φ) (fun x => conj (F₁ x)) (fun x => conj (F₂ x)) z) (GlobalTheory.Core.Rk.IP.openOff s.V s.Λ c.S) s.ν := by
    refine ⟨max s₁ ((D.R.t : ℝ) / 2 - 1 / 2), max_lt hs₁ (by linarith), ?_⟩
    exact (hPeel hgap c w hw k hk s s' hs hs' p hp m X hmX a hIM u₁ u₂ φ hQ _ hv _ hv _
      (lt_of_lt_of_le (by linarith) (le_max_right _ _)) (hLint _ (le_max_left _ _))).1
  have hPt := hPeel hgap c w hw k hk s s' hs hs' p hp m X hmX a hIM u₁ u₂ φ hQ _ hv _ hv ((D.R.t : ℝ) / 2)
    (by linarith) (hLint _ hs₁.le)
  obtain ⟨-, -, -, hval⟩ := hHF c.ψ c.θ s.V s'.V (c.chS (k + 1)) (c.chT (k + 1)) (cart s.M) (cart s'.M) D.R.t cA a p.ω
    m X hPair ht2 (Or.inr hwitt) s.Λ s'.Λ c.S (p.pt φ) (p.pt φ) (hfock φ).1 (hfock φ).1 hUnr s.ν s'.ν hsF.haar hs'F.haar
    _ hu1 _ hu2 B hparF hsph hNS hint
  have key := hval l hl
  have hsZ : GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.sZero s.V s'.V = (((D.R.t : ℝ) / 2 : ℝ) : ℂ) := by
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.sZero, hrk]; push_cast; ring
  have hI : ∫ g in GlobalTheory.Core.Rk.IP.openOff s.V s.Λ c.S, GlobalTheory.Core.Rk.IP.wcoef p.ω m X (p.pt φ) (p.pt φ) g *
      GlobalTheory.Core.Rk.IP.rcoef s.ν (fun x => conj (F₁ x)) (fun x => conj (F₂ x)) g ∂s.ν =
      locQ c w k * ((∫ g, zReal p m X φ v g ∂mR) * conj (ip u₁ u₂)) := by
    rw [← hLeq, ← hPt.2 rfl]
    change _ = ∫ g in GlobalTheory.Core.Rk.IP.openOff s.V s.Λ c.S, flatInt p m X a φ F₁ F₂ (((D.R.t : ℝ) / 2 : ℝ) : ℂ) g ∂s.ν
    congr 1
    funext g
    rw [← hsZ]
    exact (GlobalTheory.Core.Rk.IP.integrand_sZero (A := s.V) (B := s'.V) p.ω s.ν m X s.Λ a (p.pt φ) (p.pt φ) _ _ g).symm
  have hFl : ∀ F : GA D s.V → ℂ, (fun g => conj (F g)) ∈ GlobalTheory.Cusp.A0 c.θ s.V cA →
      ∀ γ ∈ GQ s.V, ∀ g, F (γ * g) = F g := fun F hF γ hγ g => by
    simpa using congrArg (starRingEnd ℂ) (hF.1.1.left γ hγ g)
  rw [ExactNS.up_conj p hp hsF.haar hsF.fund φ F₁ (hFl F₁ hu1), ExactNS.up_conj p hp hsF.haar hsF.fund φ F₂ (hFl F₂ hu2),
    ExactNS.petersson_conj s'.V s'.ν hs'F.haar s'.fd hs'F.fund _ _ (ExactNS.up_leftInv p hp φ F₁)
      (ExactNS.up_leftInv p hp φ F₂), hI] at key
  have key' := congrArg (starRingEnd ℂ) key
  rw [Complex.conj_conj] at key'
  change Lift.pet s'.ν s'.fd _ _ = _
  rw [key']
  simp only [dS, map_mul, Complex.conj_conj]
  ring

end GlobalTheory.ChainTw.ExactNS

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LineSplit

theorem mem_latV_iff_wParts {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : GlobalTheory.FinPl.SplitPt D k) {S : HSp D} {L : GlobalTheory.FinPl.Lat S} (hL : IsSelfDualC S L) (y : Fin S.rank → AE D)
    (hy : ∀ i, y i ∈ GlobalTheory.FinPl.idAt D (· = p.v)) :
    y ∈ GlobalTheory.FinPl.latV S L (· = p.v) ↔ (fun i => p.sec (p.pr (y i))) ∈ GlobalTheory.FinPl.latV S L (· = p.v) ∧
      ∀ x : Fin S.rank → k, (fun i => p.sec (x i)) ∈ GlobalTheory.FinPl.latV S L (· = p.v) →
        ∑ i, ∑ j, x i * p.pr (cA D (incA D (S.gram i j))) * p.pr (cA D (y j)) ∈ 𝒪[k] := by
  have hy' : y = (fun i => p.sec (p.pr (y i))) + (fun i => cA D (p.sec (p.pr (cA D (y i))))) := by
    funext i
    rw [Pi.add_apply, p.sec_pr, p.sec_pr, map_mul, GlobalTheory.LatVac.cA_cA, ← add_mul]
    exact ((GlobalTheory.FinPl.FrameLat.idem_iff p (y i)).1 (hy i)).symm
  conv_lhs => rw [hy']
  rw [GlobalTheory.FinPl.FrameLat.decomp hL, GlobalTheory.FinPl.FrameLat.csec_mem_iff hL]

theorem latV_eq_of_wPart : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) (L L' : GlobalTheory.FinPl.Lat S), IsSelfDualC S L → IsSelfDualC S L' → (∀ x : Fin S.rank → k, (fun i => q.sec (x i)) ∈ GlobalTheory.FinPl.latV S L (· = q.v) ↔ (fun i => q.sec (x i)) ∈ GlobalTheory.FinPl.latV S L' (· = q.v)) → GlobalTheory.FinPl.latV S L (· = q.v) = GlobalTheory.FinPl.latV S L' (· = q.v) := by
  intro D k _ _ _ _ q S L L' hL hL' h
  have key : ∀ (M M' : GlobalTheory.FinPl.Lat S), IsSelfDualC S M → IsSelfDualC S M' →
      (∀ x : Fin S.rank → k, (fun i => q.sec (x i)) ∈ GlobalTheory.FinPl.latV S M (· = q.v) ↔
        (fun i => q.sec (x i)) ∈ GlobalTheory.FinPl.latV S M' (· = q.v)) →
      ∀ y, y ∈ GlobalTheory.FinPl.latV S M (· = q.v) → y ∈ GlobalTheory.FinPl.latV S M' (· = q.v) := by
    intro M M' hM hM' hMM' y hy
    have hs : ∀ i, y i ∈ GlobalTheory.FinPl.idAt D (· = q.v) := fun i => GlobalTheory.FinPl.FrameLat.latV_supp hy i
    rw [mem_latV_iff_wParts q hM y hs] at hy
    rw [mem_latV_iff_wParts q hM' y hs]
    exact ⟨(hMM' _).1 hy.1, fun x hx => hy.2 x ((hMM' x).2 hx)⟩
  ext y
  exact ⟨key L L' hL hL' h y, key L' L hL' hL (fun x => (h x).symm) y⟩

section
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem rat_mulVec_sec (q : GlobalTheory.FinPl.SplitPt D k) {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (b : Fin n → k) :
    ((rat M : Mx D m n) *ᵥ fun i => q.sec (b i)) = fun i => q.sec ((M.map ((ofSplit q).π.comp (incA D)) *ᵥ b) i) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]

  rw [map_sum q.sec]
  exact Finset.sum_congr rfl fun j _ => GlobalTheory.SplitInt.mul_sec q _ _

end

theorem exists_lineLat : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S A B : HSp D) (o : OrthDec S A B) (MS : GlobalTheory.FinPl.Lat S) (MA : GlobalTheory.FinPl.Lat A) (Y : Type) [Fintype Y] [DecidableEq Y] (FA : Frame k A.rank Y) (FS : Frame k S.rank (Y ⊕ Unit)) (z : Fin B.rank → k), IsSelfDualC S MS → IsSelfDualC A MA → (∃ LB : GlobalTheory.FinPl.Lat B, IsSelfDualC B LB) → (∀ r a, FS.β r (Sum.inl a) = (o.iA.map (ofSplit q).pr * FA.β) r a) → (∀ r, FS.β r (Sum.inr ()) = (o.iB.map (ofSplit q).pr *ᵥ z) r) → IntIn q S FS MS → IntIn q A FA MA → ∃ LB : GlobalTheory.FinPl.Lat B, IsSelfDualC B LB ∧ GlobalTheory.FinPl.OrthAt o MS MA LB q.v ∧ ∀ y : k, (y ∈ 𝒪[k] ↔ (fun i => q.sec (z i * y)) ∈ GlobalTheory.FinPl.latV B LB (· = q.v)) := by
  intro D k _ _ _ _ q S A B o MS MA Y _ _ FA FS z hMS hMA ⟨LB₀, hLB₀⟩ hβA hβB hIS hIA
  set f : D.host.E →+* k := (ofSplit q).π.comp (incA D) with hf
  have hpr : (ofSplit q).pr = ⇑f := rfl
  rw [hpr] at hβA hβB
  have hc : Fintype.card (Y ⊕ Unit) = S.rank := FS.card_eq
  have hcA : Fintype.card Y = A.rank := FA.card_eq
  have hB1 : B.rank = 1 := by
    have := o.rank_add
    rw [Fintype.card_sum, hcA, Fintype.card_unit] at hc
    omega
  have hsub : ∀ i j : Fin B.rank, i = j := fun i j => Fin.ext (by omega)
  haveI : Subsingleton (Fin B.rank) := ⟨hsub⟩
  let i₀ : Fin B.rank := ⟨0, by omega⟩

  have hcol : ∀ c : Y ⊕ Unit → k, FS.β *ᵥ c =
      o.iA.map f *ᵥ (FA.β *ᵥ fun a => c (Sum.inl a)) + c (Sum.inr ()) • (o.iB.map f *ᵥ z) := by
    intro c
    funext r
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fintype.univ_unit, Finset.sum_singleton, hβA, hβB,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    congr 1
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun s _ => by ring
    · exact Finset.sum_congr rfl fun s _ => by ring
  have hz : z i₀ ≠ 0 := by
    intro h0
    have hz0 : z = 0 := funext fun i => by rw [hsub i i₀, h0]; rfl
    have h1 := congrFun (congrFun FS.γβ (Sum.inr ())) (Sum.inr ())
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
    simp only [hβB, hz0, Matrix.mulVec_zero, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at h1
    exact zero_ne_one h1
  have hz' : ∀ i, z i ≠ 0 := fun i => by rw [hsub i i₀]; exact hz
  let FB : Frame k B.rank Unit :=
    { β := Matrix.of fun i _ => z i
      γ := Matrix.of fun _ i => (z i)⁻¹
      βγ := by
        ext i j
        rw [hsub j i]
        simp [Matrix.mul_apply, hz' i]
      γβ := by
        ext u u'
        rw [Subsingleton.elim u' u]
        simp [Matrix.mul_apply, Fintype.sum_subsingleton _ i₀, hz] }
  obtain ⟨LB, hLB, -, hLBw⟩ := GlobalTheory.T.exists_selfDualLattice_prescribed_splitPlace D k q B Unit FB LB₀ hLB₀
  obtain ⟨L', hL', hL'o⟩ := GlobalTheory.OrthSumLat.exists_selfDual_orthAt D S A B o MA LB hMA hLB
  have hFBv : ∀ y : k, (FB.β *ᵥ fun _ => y) = fun i => z i * y := fun y => by
    funext i
    simp [FB, Matrix.mulVec, dotProduct]
  refine ⟨LB, hLB, ?_, fun y => ?_⟩
  ·
    have hqA : o.qA.map f * o.iA.map f = 1 := by
      rw [← Matrix.map_mul, o.qA_iA, Matrix.map_one _ (map_zero f) (map_one f)]
    have hqAB : o.qA.map f * o.iB.map f = 0 := by
      rw [← Matrix.map_mul, o.qA_iB, Matrix.map_zero _ (map_zero f)]
    have hqB : o.qB.map f * o.iB.map f = 1 := by
      rw [← Matrix.map_mul, o.qB_iB, Matrix.map_one _ (map_zero f) (map_one f)]
    have hqBA : o.qB.map f * o.iA.map f = 0 := by
      rw [← Matrix.map_mul, o.qB_iA, Matrix.map_zero _ (map_zero f)]
    have hw : ∀ x : Fin S.rank → k, (fun i => q.sec (x i)) ∈ GlobalTheory.FinPl.latV S MS (· = q.v) ↔
        (fun i => q.sec (x i)) ∈ GlobalTheory.FinPl.latV S L' (· = q.v) := by
      intro x
      set c := FS.γ *ᵥ x with hcdef
      have hx : x = FS.β *ᵥ c := by rw [hcdef, Matrix.mulVec_mulVec, FS.βγ, Matrix.one_mulVec]
      have hqx : o.qA.map f *ᵥ x = FA.β *ᵥ fun a => c (Sum.inl a) := by
        rw [hx, hcol, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec (M := o.qA.map f) (N := o.iA.map f), hqA,
          Matrix.one_mulVec, Matrix.mulVec_mulVec (M := o.qA.map f) (N := o.iB.map f), hqAB, Matrix.zero_mulVec, smul_zero,
          add_zero]
      have hqBx : o.qB.map f *ᵥ x = FB.β *ᵥ fun _ => c (Sum.inr ()) := by
        rw [hx, hcol, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec (M := o.qB.map f) (N := o.iA.map f), hqBA,
          Matrix.zero_mulVec, Matrix.mulVec_mulVec (M := o.qB.map f) (N := o.iB.map f), hqB, Matrix.one_mulVec, zero_add,
          hFBv]
        funext i
        simp [mul_comm]
      have eS := hIS c
      rw [← hx] at eS
      have eA := hIA (fun a => c (Sum.inl a))
      have eB := hLBw (fun _ => c (Sum.inr ()))
      rw [← eS, hL'o q.v, show o.pA = rat o.qA from rfl, show o.pB = rat o.qB from rfl, rat_mulVec_sec,
        rat_mulVec_sec, ← hf, hqx, hqBx, ← eA, ← eB, Sum.forall]
    intro y
    rw [latV_eq_of_wPart D k q S MS L' hMS hL' hw]
    exact hL'o q.v y
  · have := hLBw (fun _ => y)
    rw [hFBv] at this
    exact ⟨fun h => this.1 fun _ => h, fun h => this.2 h ()⟩

end GlobalTheory.LineSplit
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ColsBFSplit

theorem xi_unit {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) (hU : q.UnitAA) : valuation k ((ofSplit q).xi) = 1 := by
  have hpe : q.pr q.e = 1 := by
    have h := q.pr_sec 1
    rwa [show q.sec 1 = q.e by simpa using q.sec_pr 1] at h
  have hpce : q.pr (cA D q.e) = 0 := by
    have h : q.pr (q.e * cA D q.e) = 0 := by rw [q.split.2.1, map_zero]
    rwa [map_mul, hpe, one_mul] at h
  have heI := GlobalTheory.FinPl.LatIndHalf.e_mem_idAt q
  have heInt : q.e ∈ GlobalTheory.FinPl.intAt D (· = q.v) :=
    (GlobalTheory.T.splitPlace_integralAdele_iff_both_components D k q q.e heI).2 ⟨by rw [hpe]; exact one_mem _, by rw [hpce]; exact zero_mem _⟩
  obtain ⟨h1, h2⟩ := hU.1 q.e heInt
  have a1 := ((GlobalTheory.T.splitPlace_integralAdele_iff_both_components D k q _ h1.1).1 h1).1
  have a2 := ((GlobalTheory.T.splitPlace_integralAdele_iff_both_components D k q _ h2.1).1 h2).1
  rw [map_mul, hpe, mul_one] at a1 a2
  have hne : q.pr (incA D D.host.xi0) ≠ 0 := by
    intro h0
    have : q.pr (incA D D.host.xi0⁻¹) * q.pr (incA D D.host.xi0) = 1 := by
      rw [← map_mul, ← map_mul, inv_mul_cancel₀ (GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero (D := D)), map_one, map_one]
    rw [h0, mul_zero] at this
    exact zero_ne_one this
  have hinv : q.pr (incA D D.host.xi0⁻¹) = (q.pr (incA D D.host.xi0))⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_mul, ← map_mul, inv_mul_cancel₀ (GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero (D := D)), map_one, map_one]
  rw [hinv] at a2
  have b1 := (Valuation.mem_integer_iff _ _).1 a1
  have b2 := (Valuation.mem_integer_iff _ _).1 a2
  rw [map_inv₀] at b2
  change valuation k (q.pr (incA D D.host.xi0)) = 1
  have hv0 : valuation k (q.pr (incA D D.host.xi0)) ≠ 0 := by simpa using hne
  exact le_antisymm b1 ((inv_le_one₀ (zero_lt_iff.2 hv0)).1 b2)

theorem line_crit {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) {S : HSp D} {L : GlobalTheory.FinPl.Lat S} {Y : Type} [Fintype Y] [DecidableEq Y]
    (F : Frame k S.rank Y) (u u' : Fin S.rank → D.host.E) (m₀ m₁ : Y) (c₀ c₁ : k) (hL : IsSelfDualC S L)
    (hI : IntIn q S F L) (h0 : valuation k c₀ = 1) (h1 : valuation k c₁ = 1)
    (hc0 : ∀ r, F.β r m₀ = c₀ * (ofSplit q).pr (u r)) (hc1 : ∀ r, F.β r m₁ = c₁ * (ofSplit q).pr (u' r))
    (hd : ∑ r, ∑ r', star (u r) * S.gram r r' * u' r' = 1)
    (hp : ∀ m, m ≠ m₁ → ∑ r, ∑ r', (ofSplit q).pr (star (u r)) * (ofSplit q).pr (S.gram r r') * F.β r' m = 0)
    (a : AE D) (ha : a ∈ GlobalTheory.FinPl.idAt D (· = q.v)) :
    (fun r => a * incA D (u r)) ∈ GlobalTheory.FinPl.latV S L (· = q.v) ↔ a ∈ GlobalTheory.FinPl.intAt D (· = q.v) := by
  rw [GlobalTheory.T.splitPlace_mem_latticeCompletion_iff_parts D k q S L _ (fun r => Ideal.mul_mem_right _ _ ha), GlobalTheory.T.splitPlace_wPart_frameColumnMultiple_mem_iff D k q S L Y F u m₀ c₀ hI h0 hc0 a,
    GlobalTheory.T.splitPlace_conjPart_lineMultiple_mem_iff D k q S L Y F u u' m₁ c₁ hL hI h1 hc1 hd hp a, GlobalTheory.T.splitPlace_integralAdele_iff_both_components D k q a ha]

end GlobalTheory.ColsBFSplit

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel

noncomputable section
namespace GlobalTheory.LevProd.SamePlace

open GlobalTheory.FinPl (Lat latV Moves SplitPt)
open GlobalTheory.IwaPlace (hermAt)

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (q : SplitPt D k) {V : HSp D} {Y : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k V.rank Y) {L : Lat V}

theorem half_mem (hL : IntIn q V F L) {g : GA D V} (hg : GlobalTheory.LevIdx.locHom q V F g ∈ KO k Y)
    {y : Fin V.rank → Formalism.L2.Theta.AE D} (hy : y ∈ latV V L (· = q.v)) :
    q.e • (Formalism.L2.Theta.mt V g *ᵥ y) ∈ latV V L (· = q.v) := by
  have he : finPart D q.e ∈ intAE D := by
    rw [← GlobalTheory.FinPl.LatIndHalf.sec_one]; exact (q.int_iff 1).1 (one_mem _)
  have h2 : (Formalism.L2.Theta.mt V g).map q.pr = F.β * (GlobalTheory.LevIdx.locHom q V F g).val * F.γ :=
    (GlobalTheory.LevIdx.eq_locHom_iff q V F g _).2 rfl
  have e : q.e • (Formalism.L2.Theta.mt V g *ᵥ y) =
      fun i => q.sec ((F.β *ᵥ ((GlobalTheory.LevIdx.locHom q V F g).val *ᵥ (F.γ *ᵥ fun j => q.pr (y j)))) i) := by
    funext i
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← h2, Pi.smul_apply, smul_eq_mul, ← q.sec_pr]
    exact congrArg q.sec (RingHom.map_mulVec q.pr _ y i)
  rw [e]
  refine (hL _).1 (GlobalTheory.LocGl.mulVec_int ((GlobalTheory.LocGl.mem_KO_iff _).1 hg).1 ((hL _).2 ?_))
  rw [Matrix.mulVec_mulVec, F.βγ, Matrix.one_mulVec]
  simpa only [q.sec_pr] using GlobalTheory.FinPl.LatIndHalf.mul_mem_latV he hy

theorem act_mem (hsd : IsSelfDualC V L) (hL : IntIn q V F L) {g : GA D V} (hg : GlobalTheory.LevIdx.locHom q V F g ∈ KO k Y)
    {y : Fin V.rank → Formalism.L2.Theta.AE D} (hy : y ∈ latV V L (· = q.v)) :
    Formalism.L2.Theta.mt V g *ᵥ y ∈ latV V L (· = q.v) := by
  obtain ⟨s1, -, s2⟩ := GlobalTheory.IwaPlace.LocSD.isSDAt_latV D V L q.v hsd
  have hs := GlobalTheory.IwaPlace.mulVec_mem_idAt (Formalism.L2.Theta.mt V g) (s1 y hy)
  have e : Formalism.L2.Theta.mt V g *ᵥ y =
      q.e • (Formalism.L2.Theta.mt V g *ᵥ y) + cA D q.e • (Formalism.L2.Theta.mt V g *ᵥ y) := by
    rw [← add_smul, GlobalTheory.LocGl.idem_eq]
    exact funext fun i => ((GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 (hs i)).symm
  have hg' : GlobalTheory.LevIdx.locHom q V F g⁻¹ ∈ KO k Y := by rw [map_inv]; exact inv_mem hg
  rw [e]
  refine add_mem (half_mem q F hL hg hy) ((s2 _ fun i => Ideal.mul_mem_left _ _ (hs i)).2 fun x hx => ?_)
  have e2 : q.e • x = Formalism.L2.Theta.mt V g *ᵥ (q.e • (Formalism.L2.Theta.mt V g⁻¹ *ᵥ x)) := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← GlobalTheory.MixModel.mt_mul, mul_inv_cancel,
      GlobalTheory.MixModel.mt_one, Matrix.one_mulVec]
  change hermAt V (cA D q.e • (Formalism.L2.Theta.mt V g *ᵥ y)) x ∈ _
  rw [GlobalTheory.LocGl.hermAt_smul, e2, GlobalTheory.LocGl.hermAt_unitary]
  exact (s2 y (s1 y hy)).1 hy _ (half_mem q F hL hg' hx)

theorem moves_of_mem_KO (hsd : IsSelfDualC V L) (hL : IntIn q V F L) {g : GA D V}
    (hg : GlobalTheory.LevIdx.locHom q V F g ∈ KO k Y) : Moves V g L L (· = q.v) := by
  refine fun y _ => ⟨act_mem q F hsd hL hg, fun hy => ?_⟩
  have := act_mem q F hsd hL (g := g⁻¹) (by rw [map_inv]; exact inv_mem hg) hy
  rwa [Matrix.mulVec_mulVec, ← GlobalTheory.MixModel.mt_mul, inv_mul_cancel, GlobalTheory.MixModel.mt_one, Matrix.one_mulVec] at this


end GlobalTheory.LevProd.SamePlace
end
end
