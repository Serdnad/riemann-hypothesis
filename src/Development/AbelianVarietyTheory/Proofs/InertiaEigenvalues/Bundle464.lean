module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JumpDictCrysAtOfWeights
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle032
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle305
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle454
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle352
public import Formalism.SharpRestriction.LevelLetterCocycles.TWSet
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle280
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle367
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle455
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousFixingSubgroupEquiv
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsLiftOfMemKO
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIrreducibleHarishChandraOfStdTraceNeZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Mathlib.RingTheory.PowerSeries.Exp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle427
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle453
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Padics.LocalField
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle013
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle016
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary

noncomputable section

namespace GlobalTheory.JumpDictRec

open GlobalTheory.JumpDictionaryFoundation

theorem main : ∀ D : D7, WeightParam D → BlockCharParam D → GlobalTheory.JumpDictionaryFoundation.AlgebraicCharacter_at D →
    GlobalTheory.TwSys.Cheb → ∀ (i : D.nd.Loc) (τ : D.host.E →+* Qbar (D.nd.l i)) (ρ : D.what₂.Tau) (b : Bool),
    (D.naut.iotaQC i).toRingHom.comp τ = embOver D ρ b → ∃ cτ : ℤ,
      (D.naut.locAutHodgeTateWeightsLevelZero i τ).map (fun n : ℤ => (n : ℚ)) = (PP D i ρ).map (fun p => sgnOf true b * p + cτ) ∧
      ∀ w ∈ placesOver D.host.E (D.nd.l i),
        D.naut.IsdRW i (mapRep (iotaOQ D.nd D.naut i) (chiGL D i 1)) w ∧
        (D.naut.jumpsW i (mapRep (iotaOQ D.nd D.naut i) (chiGL D i 1)) τ).map (fun n : ℤ => (n : ℚ)) =
          {sgnOf true b * (-(D.hc ρ).e (liftIdx D i)) - ((D.R.t : ℚ) - 1) / 2 + cτ} := by
  intro D hW hB hG hC i τ ρ b hτ
  have hs := shift_embOver D ρ b
  refine ⟨shift D (embOver D ρ b), ?_, fun w hw => ?_⟩
  · apply Multiset.map_injective (f := fun q : ℚ => (q : ℂ)) Rat.cast_injective
    rw [Multiset.map_map, Multiset.map_map]
    have e0 := D.naut.locAut_hodgeTateWeightsLevelZero_def i τ
    rw [hτ] at e0
    have e1 : (D.naut.locAutHodgeTateWeightsLevelZero i τ).map ((fun q : ℚ => (q : ℂ)) ∘ fun n : ℤ => (n : ℚ)) =
        (D.naut.locAutHodgeTateWeightsLevelZero i τ).map (fun n : ℤ => (n : ℂ)) :=
      Multiset.map_congr rfl fun n _ => by simp
    rw [e1, e0]
    cases b
    · rw [(hW i ρ).1, Multiset.map_map]
      refine Multiset.map_congr rfl fun p _ => ?_
      simp only [Function.comp, sgnOf, hs]
      push_cast
      norm_num
      ring
    · rw [(hW i ρ).2, Multiset.map_map]
      refine Multiset.map_congr rfl fun p _ => ?_
      simp only [Function.comp, sgnOf, hs]
      push_cast
      norm_num
      ring
  · have ht : 1 ≤ D.R.t := by
      obtain ⟨u, v, -, hv, -⟩ := exists_halves D.R
      omega
    have hz : ∀ φ, ∃ z : ℤ, (D.naut.infG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) φ).map
        (· + (blockExp D 1 : ℂ)) = {(z : ℂ)} := by
      intro φ
      obtain ⟨ρ', b', rfl⟩ := exists_embOver D φ
      obtain ⟨a, ha⟩ := firstJump_int D i ρ' b'
      refine ⟨-a, ?_⟩
      rw [inf_block D hB, ha]
      push_cast
      simp
    choose z hz using hz
    obtain ⟨r, hrc, hrf, hrd, hrj⟩ := hG i _ _ z hz
    have hr : r = mapRep (iotaOQ D.nd D.naut i) (chiGL D i 1) := by
      have h := eq_of_frob D.nd hC i
        (a := fun g => ((r g : GL (Fin 1) (Qbar (D.nd.l i))) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0)
        (b := fun g => iotaOQ D.nd D.naut i ((D.nd.chi i 1 g : (D.nd.O i)ˣ) : D.nd.O i))
        ((continuous_apply 0).comp ((continuous_apply 0).comp hrc))
        ((continuous_iotaOQ D i w hw).comp (D.nd.chi_cont i 1)) fun v hv B σ hB' hσ => by
          have e1 := hrf v hv.2.1 (D.naut.chi_mu i v hv).1 B σ hB' hσ
          rw [chi_frob D i 1 le_rfl ht v hv B σ hB' hσ, Multiset.singleton_inj] at e1
          exact ((D.naut.iotaQC i).injective e1).symm
      ext g a c
      obtain rfl : a = 0 := Subsingleton.elim _ _
      obtain rfl : c = 0 := Subsingleton.elim _ _
      refine (congrFun h g).trans ?_
      rw [← chiGL_apply D i 1 g 0 0]
      rfl
    subst hr
    refine ⟨hrd w hw, ?_⟩
    have hq : firstJump D i ρ b + (((1 : ℕ) : ℚ) - 1) = ((-z (embOver D ρ b) : ℤ) : ℚ) := by
      have e := (inf_block D hB i 1 ρ b).symm.trans (hz _)
      rw [Multiset.singleton_inj] at e
      have e' : -(firstJump D i ρ b + (((1 : ℕ) : ℚ) - 1)) = (z (embOver D ρ b) : ℚ) := by exact_mod_cast e
      rw [Int.cast_neg, ← e', neg_neg]
    rw [hrj, hτ, Multiset.map_singleton, ← hq, hs]
    congr 1
    cases b
    · simp only [firstJump, sgnOf, Ranks.nV]
      push_cast
      norm_num
      ring
    · simp only [firstJump, sgnOf, Ranks.nV]
      push_cast
      norm_num
      ring

end GlobalTheory.JumpDictRec

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per


theorem _root_.GlobalTheory.T.blockTriangular_extensionCocycle_trivial_deRham : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI) (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (K : FinExt l) (ρ : ↥(GK K) →* GL (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (ρ₁ : ↥(GK K) →* GL a ↥(MaximalUnramifiedExtension l)) (ρ₂ : ↥(GK K) →* GL b ↥(MaximalUnramifiedExtension l)) (c : ↥(GK K) → Matrix a b ↥(MaximalUnramifiedExtension l)), (∀ g, (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) = Matrix.fromBlocks (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)) (c g) 0 (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l))) → AdmDR P ρ → AdmDR P ρ₂ → ∀ m : ℕ, ∃ v : a × b → P.R.BdR, ∀ g : ↥(GK K), (fun i => kd P (fr l m (extCoc ρ₂ c g i))) = (matD P (homRep ρ₁ ρ₂) m g).mulVec (fun i => P.actQdR (g : GQ l) (v i)) - v := by
  first | exact @GlobalTheory.PMon.extCoc_dies_in_BdR | exact GlobalTheory.PMon.extCoc_dies_in_BdR | (intros; apply GlobalTheory.PMon.extCoc_dies_in_BdR <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.hasHodgeTateWeightFrame_character_twist : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n] (K K' : FinExt l) (hK : K.1 ≤ K'.1) (r N : ℕ) (hr : 0 < r) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (w : Fin r → n → ℤ) (χ : ↥(GK K') →* (↥(MaximalUnramifiedExtension l))ˣ) (x : P.R.Bˣ) (a : ℤ), IsRat r ρ → Framed P ρ w → (∀ g : ↥(GK K'), P.actQ (g : GQ l) (x : P.R.B) = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (χ g : ↥(MaximalUnramifiedExtension l)) * x) → P.ιB x ∈ Fil P 1 → P.ιB x ∉ Fil P 2 → (∀ j, 0 < j → j < r * N → ev P j x ∈ Fil P 0 ∧ ev P j x ∉ Fil P 1) → Framed P (GlobalTheory.PMon.Twist.twist hK ρ χ a) (fun (m : Fin (r * N)) j => w ⟨(m : ℕ) % r, Nat.mod_lt _ hr⟩ j + if (m : ℕ) = 0 then a else 0) := by
  first | exact @GlobalTheory.PMon.Twist.framed_twist | exact GlobalTheory.PMon.Twist.framed_twist | (intros; apply GlobalTheory.PMon.Twist.framed_twist <;> assumption)
end

section

noncomputable section

open GlobalTheory.LiftLeaf GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.UnivCharIne

theorem surj_conj (D : D7) {B : Type} [CommGroup B] (χ : G D.host.E D.nd.Om →* B) (hA : AntiHom D.ntw.cc χ)
    {P P' : PlE D.host} (hPP : IsConjPl D.host P P')
    (hs : ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P → ∀ b : B, ∃ σ ∈ Ine (F := D.host.E) A, χ σ = b)
    (A : ValuationSubring D.nd.Om) (hA' : IsPlaceOver A P') (b : B) : ∃ σ ∈ Ine (F := D.host.E) A, χ σ = b := by
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  have hst : ∀ x : D.host.E, IsCMField.complexConj D.host.E x = D.host.conj x :=
    Formalism.BasicNotions.bridge_star_holds D.R D.host
  obtain ⟨⟨j, hj⟩, -⟩ := D.ntw.cc_cm
  have hκ : ∀ x, D.host.conj (D.host.conj x) = x := fun x => by
    rw [← hst, ← hst, IsCMField.complexConj_apply_apply]
  have hc : ∀ x, D.ntw.cc (algebraMap D.host.E D.nd.Om x) =
      algebraMap D.host.E D.nd.Om (D.host.conj x) := fun x => by
    apply j.injective
    rw [hj, ← hst]
    exact (IsCMField.complexEmbedding_complexConj D.host.E
      (j.comp (algebraMap D.host.E D.nd.Om)) x).symm
  have hs' : ∀ x, D.ntw.cc.symm (algebraMap D.host.E D.nd.Om x) =
      algebraMap D.host.E D.nd.Om (D.host.conj x) := fun x => by
    rw [RingEquiv.symm_apply_eq, hc, hκ]
  have hinv : ∀ x, D.ntw.cc (D.ntw.cc x) = x := fun x => by
    apply j.injective
    rw [hj, hj]
    simp
  have hsymm : ∀ x, D.ntw.cc.symm x = D.ntw.cc x := fun x => by
    rw [RingEquiv.symm_apply_eq, hinv]
  have hP'P := GlobalTheory.GalChar.isConjPl_symm hPP
  have hpl : IsPlaceOver (A.comap D.ntw.cc.symm.toRingHom) P := fun y => by
    have hint : IsIntegral ℤ (D.host.conj (y : D.host.E)) := by
      rw [← hst]
      exact (RingOfIntegers.isIntegral_coe y).map
        ((IsCMField.complexConj D.host.E).toRingEquiv.toRingHom.toIntAlgHom)
    rw [GlobalTheory.AntiRam.valuation_comap_lt_one, hs', ← hP'P ⟨_, hint⟩ y (hκ _).symm]
    exact hA' ⟨_, hint⟩
  obtain ⟨σ, hσ, hσb⟩ := hs _ hpl b⁻¹
  obtain ⟨σ', h1, h2⟩ := GlobalTheory.AntiRam.exists_conj_mem_Ine D.ntw.cc (fun x => D.host.conj x) hc hκ _ σ hσ
  have eA : (A.comap D.ntw.cc.symm.toRingHom).comap D.ntw.cc.symm.toRingHom = A := by
    ext y
    show D.ntw.cc.symm (D.ntw.cc.symm y) ∈ A ↔ y ∈ A
    rw [hsymm, hsymm, hinv]
  refine ⟨σ', eA ▸ h2, ?_⟩
  rw [hA σ σ' h1, hσb, inv_inv]

theorem delU_ine : ∀ D : D7, GlobalTheory.UnivChar.IsUnivChar D.nexp → (∀ (i : D.ntw.Tw) (Q : Finset (PlE D.host)) (M : ℕ), Formalism.MainNotions.NAdm.AdmQ D.ntw i Q M → ∀ P (hP : P ∈ Q), (∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P → Function.Surjective fun σ : Ine (F := D.host.E) A => Multiplicative.toAdd (D.nexp.delU i Q M σ) ⟨P, hP⟩) ∧ ∀ P' ∈ Q, P' ≠ P → ¬ IsConjPl D.host P P' → ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P' → ∀ σ ∈ Ine (F := D.host.E) A, Multiplicative.toAdd (D.nexp.delU i Q M σ) ⟨P, hP⟩ = 0) := by
  intro D hU i Q M hQ P hP
  obtain ⟨-, hQ'⟩ := hQ
  have hcl : ∀ P ∈ Q, ∀ P', IsConjPl D.host P P' → P' ∈ Q := fun P hP P' h => by
    obtain ⟨⟨P'', hP'', h''⟩, -⟩ := hQ' P hP
    rwa [GlobalTheory.GalChar.isConjPl_unique h h'']
  obtain ⟨-, χ, h1, h2, h3, h4, h5⟩ := hQ' P hP
  have hsP : ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P →
      ∀ b, ∃ σ ∈ Ine (F := D.host.E) A, χ σ = b := fun A hA b => by
    obtain ⟨σ, hσ⟩ := h5 A hA (Multiplicative.toAdd b)
    exact ⟨σ.1, σ.2, Multiplicative.toAdd.injective hσ⟩
  have hDel : GlobalTheory.GalChar.IsDel D.host D.ntw.cc (D.ntw.l i) M (GlobalTheory.GalChar.pair D.host P) χ := by
    refine ⟨h1, h2, h3, fun v hv => h4 v (fun e => hv (Or.inl e)) (fun e => hv (Or.inr e)), fun v hv A hA b => ?_⟩
    rcases hv with rfl | hv
    · exact hsP A hA b
    · exact surj_conj D χ h2 hv hsP A hA b
  have hD := GlobalTheory.GalChar.isDel_delOf D.host D.ntw.cc (D.ntw.l i) ⟨χ, hDel⟩
  have e : ∀ σ, Multiplicative.toAdd (D.nexp.delU i Q M σ) ⟨P, hP⟩ =
      Multiplicative.toAdd (GlobalTheory.GalChar.delOf D.host D.ntw.cc (D.ntw.l i) M (GlobalTheory.GalChar.pair D.host P) σ) := by
    intro σ
    rw [hU]
    exact (GlobalTheory.GalChar.universal_anticyclotomic_character_laws D.host D.ntw.cc (D.ntw.l i)).2.2.2.2.2.2.1 Q M hcl P hP σ
  refine ⟨fun A hA x => ?_, fun P' _ hne hnc A hA σ hσ => ?_⟩
  · obtain ⟨σ, hσ, hx⟩ := hD.2.2.2.2 P (Or.inl rfl) A hA (Multiplicative.ofAdd x)
    exact ⟨⟨σ, hσ⟩, by simp only [e, hx, toAdd_ofAdd]⟩
  · rw [e, hD.2.2.2.1 P' (by rintro (h | h); exacts [hne h, hnc h]) A hA σ hσ]
    rfl

end GlobalTheory.UnivCharIne
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

theorem _root_.GlobalTheory.T.selmer_order_formula_dual_selmer : PoitouTateTotallyComplex → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → Gen.ArchimedeanSignatureMatching → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Setup bkP i s κ Q → Kills i A → IsDual i s ρ → NoInvDual i κ ρ → OrderFormula bkP i s κ ρ Q := by
  first | exact @GlobalTheory.SelOrder.orderFormula | exact GlobalTheory.SelOrder.orderFormula | (intros; apply GlobalTheory.SelOrder.orderFormula <;> assumption)
end

section

open GlobalTheory.Cyc GlobalTheory.Cyc.TwistLift

namespace GlobalTheory.Cyc.CocycleCount

theorem dependent_of_card_le : ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (ψ : G →* ℤ_[l]ˣ) (C n : ℕ), (∀ r : ℕ, 0 < r → Finite (ReciprocityTheory.Gal.Z1 (ReciprocityTheory.Gal.charRep (redChar ψ r))) ∧ Nat.card (ReciprocityTheory.Gal.Z1 (ReciprocityTheory.Gal.charRep (redChar ψ r))) ≤ C * l ^ (r * n)) → ∀ z : Fin (n + 1) → G → ℚ_[l], (∀ i, Continuous (z i)) → (∀ i g h, z i (g * h) = z i g + ((ψ g : ℤ_[l]) : ℚ_[l]) * z i h) → ∃ c : Fin (n + 1) → ℚ_[l], c ≠ 0 ∧ ∀ g, ∑ i, c i * z i g = 0 := by
  intro l _ G _ _ _ _ ψ C n hC z hz hcoc
  have hl : l.Prime := Fact.out
  by_contra hne
  push Not at hne

  obtain ⟨B, hB⟩ := (isCompact_range (continuous_pi hz : Continuous fun g i => z i g)).isBounded.exists_norm_le
  obtain ⟨a, ha0, ha⟩ := NormedField.exists_norm_lt ℚ_[l] (r := (max B 1)⁻¹) (by positivity)
  have ha1 : ∀ i g, ‖a * z i g‖ ≤ 1 := fun i g => by
    rw [norm_mul]
    have h1 : ‖z i g‖ ≤ max B 1 :=
      ((norm_le_pi_norm (fun i => z i g) i).trans (hB _ ⟨g, rfl⟩)).trans (le_max_left _ _)
    calc ‖a‖ * ‖z i g‖ ≤ (max B 1)⁻¹ * max B 1 := by gcongr
      _ = 1 := inv_mul_cancel₀ (by positivity)
  have ha' : a ≠ 0 := norm_pos_iff.1 ha0
  let w : Fin (n + 1) → G → ℤ_[l] := fun i g => ⟨a * z i g, ha1 i g⟩
  have hw : ∀ i, Continuous (w i) := fun i => (continuous_const.mul (hz i)).subtype_mk _
  have hwc : ∀ i g h, w i (g * h) = w i g + (ψ g : ℤ_[l]) * w i h := fun i g h => Subtype.ext (by
    change a * z i (g * h) = a * z i g + ((ψ g : ℤ_[l]) : ℚ_[l]) * (a * z i h)
    rw [hcoc]; ring)
  let W : Fin (n + 1) → C(G, ℚ_[l]) := fun i => ⟨fun g => a * z i g, continuous_const.mul (hz i)⟩
  let L : (Fin (n + 1) → ℚ_[l]) →ₗ[ℚ_[l]] C(G, ℚ_[l]) := Fintype.linearCombination ℚ_[l] W
  have hL : ∀ c g, L c g = ∑ i, c i * (a * z i g) := fun c g => by
    simp [L, W, Fintype.linearCombination_apply, ContinuousMap.sum_apply]
  have hker : LinearMap.ker L = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    by_contra h0
    obtain ⟨g, hg⟩ := hne c h0
    apply hg
    have h1 := hL c g
    rw [hc, ContinuousMap.zero_apply] at h1
    apply mul_left_cancel₀ ha'
    rw [mul_zero, h1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  obtain ⟨K, -, hK⟩ := L.exists_antilipschitzWith hker
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  obtain ⟨v, hv⟩ := pow_unbounded_of_one_lt (K : ℝ) hl1
  have key : ∀ r : ℕ, 0 < r → l ^ r ≤ C * l ^ (v * n) := by
    intro r hr
    obtain ⟨hfin, hcard⟩ := hC (r + v) (by omega)
    let F : (Fin (n + 1) → Fin (l ^ r)) →
        ReciprocityTheory.Gal.Z1 (ReciprocityTheory.Gal.charRep (redChar ψ (r + v))) := fun c =>
      ⟨fun g => PadicInt.toZModPow (r + v) (∑ i, ((c i : ℕ) : ℤ_[l]) * w i g),
        (continuous_toZModPow _).comp
          (continuous_finsetSum _ fun i _ => continuous_const.mul (hw i)), fun g h => by
        rw [ReciprocityTheory.Gal.charRep_apply, redChar_apply, ← map_mul, ← map_add (f := _), Finset.mul_sum,
          ← Finset.sum_add_distrib]
        refine congrArg (PadicInt.toZModPow (r + v)) ?_
        exact Finset.sum_congr rfl fun i _ => by rw [hwc]; ring⟩
    have hF : Function.Injective F := by
      intro c c' h
      let d : Fin (n + 1) → ℚ_[l] := fun i => ((((c i : ℕ) : ℤ) - ((c' i : ℕ) : ℤ) : ℤ) : ℚ_[l])
      have h1 : ‖L d‖ ≤ (l : ℝ) ^ (-((r + v : ℕ) : ℤ)) := by
        rw [ContinuousMap.norm_le _ (by positivity)]
        intro g
        have h2 : PadicInt.toZModPow (r + v) (∑ i, ((c i : ℕ) : ℤ_[l]) * w i g) =
            PadicInt.toZModPow (r + v) (∑ i, ((c' i : ℕ) : ℤ_[l]) * w i g) :=
          congrFun (congrArg Subtype.val h) g
        rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow,
          ← PadicInt.norm_le_pow_iff_mem_span_pow, PadicInt.norm_def] at h2
        refine le_of_eq_of_le (congrArg norm ?_) h2
        rw [hL, ← Finset.sum_sub_distrib]
        refine Eq.trans ?_ (map_sum (PadicInt.Coe.ringHom (p := l)) _ _).symm
        refine Finset.sum_congr rfl fun i _ => ?_
        change _ = ((((c i : ℕ) : ℤ_[l]) * w i g - ((c' i : ℕ) : ℤ_[l]) * w i g : ℤ_[l]) : ℚ_[l])
        have hwv : ((w i g : ℤ_[l]) : ℚ_[l]) = a * z i g := rfl
        rw [PadicInt.coe_sub, PadicInt.coe_mul, PadicInt.coe_mul, PadicInt.coe_natCast,
          PadicInt.coe_natCast, hwv]
        simp only [d, Int.cast_sub, Int.cast_natCast]
        ring
      have h3 : ‖d‖ ≤ (l : ℝ) ^ (-(r : ℤ)) := by
        have h4 := ZeroHomClass.bound_of_antilipschitz L hK d
        calc ‖d‖ ≤ K * ‖L d‖ := h4
          _ ≤ (l : ℝ) ^ v * (l : ℝ) ^ (-((r + v : ℕ) : ℤ)) := by gcongr
          _ = _ := by
            rw [← zpow_natCast, ← zpow_add₀ (by positivity)]
            congr 1
            push_cast; ring
      funext i
      have h5 := (Padic.norm_int_le_pow_iff_dvd (p := l) _ r).1 ((norm_le_pi_norm d i).trans h3)
      apply Fin.ext
      have h6 : ((c i : ℕ) : ℤ) - ((c' i : ℕ) : ℤ) = 0 := by
        apply Int.eq_zero_of_abs_lt_dvd h5
        have e1 : ((c i : ℕ) : ℤ) < (l : ℤ) ^ r := by exact_mod_cast (c i).2
        have e2 : ((c' i : ℕ) : ℤ) < (l : ℤ) ^ r := by exact_mod_cast (c' i).2
        rw [abs_lt]
        constructor <;> omega
      omega
    have h7 := (Nat.card_le_card_of_injective F hF).trans hcard
    rw [Nat.card_fun, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_fin,
      Fintype.card_fin] at h7
    have h8 : l ^ r * l ^ (r * n) ≤ (C * l ^ (v * n)) * l ^ (r * n) := by
      calc l ^ r * l ^ (r * n) = (l ^ r) ^ (n + 1) := by ring
        _ ≤ _ := h7
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_right h8 (pow_pos hl.pos _)
  have h9 := key (C * l ^ (v * n) + 1) (Nat.succ_pos _)
  have h10 : C * l ^ (v * n) + 1 < l ^ (C * l ^ (v * n) + 1) := Nat.lt_pow_self hl.one_lt
  omega

end GlobalTheory.Cyc.CocycleCount
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_irreducible_harishChandra_of_stdTrace_ne_zero : ∀ (p : ℕ) [Fact p.Prime] (r a c : ℕ) (θ : (ZMod p)ˣ →* ℂˣ) (ψ : GlobalTheory.GLq.Gn p r → ℂ), r = a + 1 + c → GlobalTheory.GLq.IsChar ψ → stdTrace a θ ψ ≠ 0 → ∃ (α : GlobalTheory.GLq.Gn p (a + 1) → ℂ) (β : GlobalTheory.GLq.Gn p c → ℂ), GlobalTheory.GLq.IsIrr α ∧ GlobalTheory.GLq.IsIrr β ∧ GlobalTheory.GLq.ip ψ (GlobalTheory.GLq.hc (a + 1) c α β r) ≠ 0 ∧ stdTrace a θ α ≠ 0 := by
  first | exact @GlobalTheory.LevelType.exists_irr_hc_of_stdTrace_ne_zero | exact GlobalTheory.LevelType.exists_irr_hc_of_stdTrace_ne_zero | (intros; apply GlobalTheory.LevelType.exists_irr_hc_of_stdTrace_ne_zero <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.ExpImage.PolyTaylor

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {R : Type*} [CommRing R]

theorem eval₂_mem_zero (φ : R →+* P.R.BdR) (hφ : ∀ x, φ x ∈ FilB P 0) {τ : P.R.BdR}
    (hτ : τ ∈ FilB P 0) (q : Polynomial R) : q.eval₂ φ τ ∈ FilB P 0 := by
  rw [Polynomial.eval₂_eq_sum_range]
  exact Submodule.sum_mem _ fun k _ => FilB_zero_mul (hφ _) (by simpa using FilB_pow hτ k)

theorem trunc_mul_sub_mem (φ : R →+* P.R.BdR) (hφ : ∀ x, φ x ∈ FilB P 0) {τ : P.R.BdR}
    (hτ : τ ∈ FilB P 1) (m : ℕ) (f g : PowerSeries R) :
    (f.trunc m).eval₂ φ τ * (g.trunc m).eval₂ φ τ - ((f * g).trunc m).eval₂ φ τ ∈
      FilB P (m : ℤ) := by
  have hd : Polynomial.X ^ m ∣ f.trunc m * g.trunc m - (f * g).trunc m := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    rw [Polynomial.coeff_sub, PowerSeries.coeff_trunc, if_pos hd,
      PowerSeries.coeff_mul_eq_coeff_trunc_mul_trunc f g hd, ← Polynomial.coe_mul,
      Polynomial.coeff_coe, sub_self]
  obtain ⟨q, hq⟩ := hd
  rw [← Polynomial.eval₂_mul, ← Polynomial.eval₂_sub, hq, Polynomial.eval₂_mul,
    Polynomial.eval₂_X_pow, mul_comm]
  exact FilB_zero_mul (eval₂_mem_zero φ hφ (FilB_anti zero_le_one hτ) q)
    (by simpa using FilB_pow hτ m)

theorem eval₂_sub_trunc_mem (φ : R →+* P.R.BdR) (hφ : ∀ x, φ x ∈ FilB P 0) {τ : P.R.BdR}
    (hτ : τ ∈ FilB P 1) (m : ℕ) (E : PowerSeries R) {v : P.R.BdR} (hv : v ∈ FilB P 0)
    (hE : v - (E.trunc m).eval₂ φ τ ∈ FilB P (m : ℤ)) (p : Polynomial R) :
    p.eval₂ φ v - ((Polynomial.aeval E p).trunc m).eval₂ φ τ ∈ FilB P (m : ℤ) := by
  have hτ0 := FilB_anti zero_le_one hτ
  induction p using Polynomial.induction_on with
  | C a =>
    rcases m with _ | m
    · exact sub_mem (eval₂_mem_zero φ hφ hv _) (eval₂_mem_zero φ hφ hτ0 _)
    · rw [Polynomial.aeval_C, ← PowerSeries.C_eq_algebraMap, PowerSeries.trunc_C]
      simp
  | add p q hp hq =>
    have := add_mem hp hq
    rw [map_add (f := _), map_add (f := _), Polynomial.eval₂_add, Polynomial.eval₂_add]
    convert this using 1
    ring
  | monomial n a h =>
    rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, Polynomial.eval₂_mul,
      Polynomial.eval₂_X]
    have h1 := FilB_zero_mul hv h
    have h2 := FilB_zero_mul (eval₂_mem_zero φ hφ hτ0
      ((Polynomial.aeval E (Polynomial.C a * Polynomial.X ^ n)).trunc m)) hE
    have h3 := trunc_mul_sub_mem φ hφ hτ m
      (Polynomial.aeval E (Polynomial.C a * Polynomial.X ^ n)) E
    have := add_mem (add_mem h1 h2) h3
    convert this using 1
    ring

theorem poly_taylor : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (LL : FinExt l) (s : ℕ) (ζ : ↥LL.1) (ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR), ι ζ = algebraMap (Om l) P.R.BdR (P.ζQ s) → ∀ (p : Polynomial ↥LL.1) (m : ℕ), Polynomial.eval₂ (ι : ↥LL.1 →+* P.R.BdR) (P.ιB (AI.ιA (WittVector.teichmuller l (AI.εroot s) - 1))) p - ∑ k ∈ Finset.range m, ι (PowerSeries.coeff k (Polynomial.aeval (PowerSeries.C ζ * PowerSeries.exp ↥LL.1 - 1) p)) * ((((l : ℚ_[l]) ^ s)⁻¹) • P.ιB P.tB) ^ k ∈ GlobalTheory.ExpImage.FilB P (m : ℤ) := by
  intro l _ P AI T LL s ζ ι hζ p m
  have hφ : ∀ x, (ι : ↥LL.1 →+* P.R.BdR) x ∈ FilB P 0 := EmbFil.emb_mem_fil_zero l P AI T LL ι
  have hτ : (((l : ℚ_[l]) ^ s)⁻¹) • P.ιB P.tB ∈ FilB P 1 := by
    rw [Algebra.smul_def]
    exact qB_mul_mem _ tD_mem
  have hv : P.ιB (AI.ιA (WittVector.teichmuller l (AI.εroot s) - 1)) ∈ FilB P 0 := io_mem AI _
  have key := eval₂_sub_trunc_mem (ι : ↥LL.1 →+* P.R.BdR) hφ hτ m
    (PowerSeries.C ζ * PowerSeries.exp ↥LL.1 - 1) hv ?_ p
  · rw [PowerSeries.eval₂_trunc_eq_sum_range] at key
    exact key
  rcases m with _ | m
  · exact sub_mem hv (eval₂_mem_zero _ hφ (FilB_anti zero_le_one hτ) _)
  have h := GlobalTheory.T.teichmullerEpsilonRoot_pow_sub_zeta_exp_mem_filtration l P AI T s 1 (m + 1)
  rw [map_sub (PowerSeries.trunc (m + 1)), PowerSeries.trunc_one, Polynomial.eval₂_sub,
    Polynomial.eval₂_one, PowerSeries.eval₂_trunc_eq_sum_range, ← io_apply, map_sub, map_one,
    sub_sub_sub_cancel_right]
  rw [pow_one, pow_one, Finset.mul_sum] at h
  suffices hs : ∑ k ∈ Finset.range (m + 1), (ι : ↥LL.1 →+* P.R.BdR)
      (PowerSeries.coeff k (PowerSeries.C ζ * PowerSeries.exp ↥LL.1)) *
        ((((l : ℚ_[l]) ^ s)⁻¹) • P.ιB P.tB) ^ k = ∑ k ∈ Finset.range (m + 1), oB P (P.ζQ s) *
          (qB P ((((1 : ℕ) : ℚ_[l]) / (l : ℚ_[l]) ^ s) ^ k / (k.factorial : ℚ_[l])) * tD P ^ k) by
    rw [hs]
    exact h
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : ι (algebraMap ℚ ↥LL.1 (1 / (k.factorial : ℚ))) = qB P (1 / (k.factorial : ℚ_[l])) := by
    rw [← ι.commutes]
    congr 1
    simp
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_exp, map_mul, RingHom.coe_coe, hζ, hk,
    Algebra.smul_def, mul_pow, ← map_pow, mul_assoc, ← mul_assoc (qB P _), ← map_mul]
  congr 3
  simp [div_eq_mul_inv, mul_comm]

end GlobalTheory.ExpImage.PolyTaylor
end
