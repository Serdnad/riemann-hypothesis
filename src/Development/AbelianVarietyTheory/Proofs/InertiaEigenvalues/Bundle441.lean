module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle017
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle194
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle012
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle013
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle367
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle346
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleIndexBoundAllPowersOfConditions
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalOneSubOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle366
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle386
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle322
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedSelmerLengthsEqDeterminantValuation
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle423
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle224
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle370
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle375
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle281
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle412
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle371
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle243
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle113
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle230
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle314
public import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle426
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle293
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle409
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle425
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.SetTheory.ZFC.PSet
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle289
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.DesignFromSize

theorem main : GlobalTheory.TwSys.Cheb → ∀ D : D7, TakenAll D → Formalism.MainNotions.N.K.Rows.AllDesignConditions D := by
  intro hC D hT i _ _ r ρ π dc lenRow e' cB hr hA hπ
  obtain ⟨_, _, hG3, _, _, _, _, _, _, _, _, _, _, hDec, _⟩ := hA
  have hdec : ∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t := D.R.t) (r π) (ρ π) (D.nd.chi i) e := hDec
  have hpos : 0 < D.R.r := by
    have := D.R.two_le_m; have := D.R.m_add_three_le_k; unfold Ranks.r; omega
  have habs : AbsIrrSub (mapRep (IsLocalRing.residue (D.nd.O i)) (ρ π)) ⊤ :=
    GlobalTheory.Proof.AbsoluteIrreducibilitySpan.absIrr_of_span hpos _ _ (fun _ => 1) (fun g => by rw [one_smul]; rfl) hG3.2.2
  have hlive : Live D.nd i := ⟨π, hπ, r π, ρ π, hr π, hdec, habs⟩
  obtain ⟨r₀, ρ₀, hr₀, hw⟩ := hT i hlive
  obtain ⟨S, hS, _⟩ := GlobalTheory.T.exists_globalObjects_every_family_wild hC D.nd i r₀ ρ₀ hr₀ hw r ρ hr π hπ hdec
  exact ⟨S, hS⟩

end GlobalTheory.DesignFromSize
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.OrthogonalDesignFromSize

theorem main : GlobalTheory.TwSys.Cheb → ∀ D : D7, AutomorphicSideWildInertia.ResidualIrreducibleGood D → TakenAll D → TypePrimeCongruences.TypePrimeWildIdempotentChoice D := by
  intro hC D hN9 hT i k hk hHG r ρ hr π hπ hd _
  have hdec : ∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t := D.R.t) (r π) (ρ π) (D.nd.chi i) e := hd
  have hcont : Continuous (fun g => ((ρ π g : GL (Fin D.R.r) (D.nd.O i)) :
      Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))) :=
    GlobalTheory.BlockJumpsCompare.continuous_rho D.nd i r ρ π (hr π) hd
  have hrb : IsRhoBar D.nd i (redRep D.nd i (ρ π)) := by
    refine ⟨isOpen_ker_redRep D i (ρ π) hcont, ?_⟩
    intro x w hw B σ hB hσ
    have e2 := congrArg (Polynomial.map (IsLocalRing.residue (D.nd.O i)))
      (charpoly_of_decomp D i r ρ π hd σ)
    rw [Polynomial.map_mul, Polynomial.map_prod, ← Matrix.charpoly_map, ← Matrix.charpoly_map] at e2
    rw [heckePol_res D i x π w, ← (hr π).2.2 w hw B σ hB hσ, ← Matrix.charpoly_map]
    refine (e2.trans ?_).symm
    congr 1
    refine Finset.prod_congr rfl fun c _ => ?_
    simp
  have hirr := (hN9 i hHG _ hrb).1
  have hpos : 0 < D.R.r := by
    have := D.R.two_le_m
    unfold Ranks.r
    omega
  have habs : AbsIrrSub (mapRep (IsLocalRing.residue (D.nd.O i)) (ρ π)) ⊤ :=
    GlobalTheory.ResAbsIrrGood.absIrrSub_top_of_irred (D.naut.kFbar i) hpos _
      fun W hW => hirr W fun g _ x hx => hW g x hx
  have hlive : Live D.nd i := ⟨π, hπ, r π, ρ π, hr π, hdec, habs⟩
  obtain ⟨r₀, ρ₀, hr₀, hw⟩ := hT i hlive
  obtain ⟨S, hS, hg⟩ := GlobalTheory.T.exists_globalObjects_every_family_wild hC D.nd i r₀ ρ₀ hr₀ hw r ρ hr π hπ hdec
  exact ⟨S, hS, hg.2 ⟨k, hk⟩⟩

end GlobalTheory.OrthogonalDesignFromSize
end

section

open GlobalTheory.LiftLeaf GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.TwExportSup

theorem heckeLaws_of_range (D : D7) (hC : HkComm D) (hO : OffRange D) : HeckeLaws D.nexp := by
  intro i hi
  refine ⟨fun j b k P k' P' h h' => ?_, (hO i hi).2⟩
  by_cases hj : j ∈ Finset.Icc 1 D.R.m
  · exact (hC i hi j hj b k P k' P' h h').eq
  · haveI := (hO i hi).1 j hj b
    exact LinearMap.ext fun x => Subsingleton.elim _ _

theorem twistTheorem_allPowers_of_selmer_supLattice :
    ∀ (D : D7) (E : IntegralHeckeForms.XD D) (N0 : D.ntw.Tw → ℕ), ThmS (BlochKatoReduction.bk0 D) → ResidualBoundOddPrimes (BlochKatoReduction.bk0 D) → ThmC (BlochKatoReduction.bk0 D) →
      BlochKatoReduction.Gen.AdmACD (BlochKatoReduction.bk0 D) N0 → DelUTie D.nexp → ThURel D.nexp → HkComm D → OffRange D → AllGood D.nexp →
      BlochKatoReduction.Gen.adm8 D.ntw D.nexp → SupG D → SupFull D → SupHk D → UnivSup D E → TypeKept E → CommG D →
      IntegralHeckeForms.admT4 D.nexp E → IntegralHeckeForms.TwistedSeriesSpecialisation D.nexp → D.nexp.sig_all → HkSS D →
      ∀ i, D.ntw.NonzeroIndexPlace i → goodTwistExistsAllCoprimePowers D.nexp (BlochKatoReduction.bk0 D) E N0 i := by
  intro D E N0 hS h103 hC hACD hTie hRel hHC hOff hGood h8 hG hFull hHk hU hT hComm hT4 hL3 hSig hSS
  have hX : GaloisSideTwistedSelmerAuxiliaryPrimes (BlochKatoReduction.bk0 D) :=
    GlobalTheory.TwSys.galois_twisted_selmer_auxprimes_of_matrix_and_bounds D D.nd D.ntw (BlochKatoReduction.bk0 D) hS
      (GlobalTheory.SelDetLength.twisted_selmer_lengths_eq_determinant_valuation D D.nd D.ntw (BlochKatoReduction.bk0 D)) h103 hC
  have hP : PropABCD D.nexp :=
    GlobalTheory.TwistDet.propABCD_of_rel D D.nd D.ntw D.nexp hRel (heckeLaws_of_range D hHC hOff) hGood h8
  have hAB : admissibleIndexBoundAllPowers D.nexp (BlochKatoReduction.bk0 D) N0 :=
    GlobalTheory.TwistChoiceAll.admissibleIndexBoundAllPowers_of_conditions D D.nd D.ntw (BlochKatoReduction.bk0 D) N0 hTie hP hX hACD
  have hInt : IntegralHeckeForms.IsotypicPartsInternalDirectSum D.nexp E := GlobalTheory.T.admInt_of_sup_laws D E hG hFull hHk hU hT hComm
  have hAlg : IntegralHeckeForms.GroupAlgebraIntegrality D.nexp := GlobalTheory.T.admALG_of_commG_var D hComm
  exact GlobalTheory.exportAll_of_six_inputs D E N0 hAB hInt hAlg hT4 hL3 (GlobalTheory.T.admT3_of_hecke_semisimple D E hInt hAlg hSig hSS)

end GlobalTheory.TwExportSup
end

section

noncomputable section

namespace GlobalTheory.Pass.LocDirect

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in
theorem main : StepLocDirect := by
  intro D hLOC hBK hFont hPDR i r hr Xs w hw hdeg n e hPot hLift k M hSub
  have hM : Continuous fun g => M g := hSub.1
  have hc : ∀ x, Continuous fun g => Br.loc D.nbr i w hw (rTwO D.nd i r x) g := fun x =>
    GlobalTheory.PotDual.continuous_loc D i w hw _ (FamCont.stepCont D i r hr x).1
  unfold LocBoundP
  have hcut : cutCoc i w hw r Xs M = ⋃₀ {A | ∃ (a : ℕ) (x : Fin a → D.nd.X i) (_ : ∀ j, x j ∈ Xs)
      (E : Fin a → Fin D.R.nV → KK D.nd i) (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i)) (_ : Y.FG)
      (hst : ∀ γ : GE D.nd, ∀ y ∈ Y, (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (y j)) ∈ Y)
      (hE : ∀ γ : GE D.nd, (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (E j) - E j) ∈ Y),
      A = LocDirect.pushSet i w hw r M x E Y hst hE} := by
    ext c
    rw [LocDirect.mem_cutCoc, Set.mem_sUnion]
    constructor
    · rintro ⟨a, x, hx, E, Y, hY, hst, hE, hc⟩
      exact ⟨_, ⟨a, x, hx, E, Y, hY, hst, hE, rfl⟩, hc⟩
    · rintro ⟨_, ⟨a, x, hx, E, Y, hY, hst, hE, rfl⟩, hc⟩
      exact ⟨a, x, hx, E, Y, hY, hst, hE, hc⟩
  rw [hcut]
  apply GlobalTheory.T.lenMod_span_sUnion_le_of_directed'
  · rintro _ ⟨a₁, x₁, hx₁, E₁, Y₁, hY₁, hst₁, hE₁, rfl⟩ _ ⟨a₂, x₂, hx₂, E₂, Y₂, hY₂, hst₂, hE₂, rfl⟩
    obtain ⟨a, x, hx, E, Y, hY, hst, hE, h1, h2⟩ :=
      GlobalTheory.T.exists_merged_module_pushouts_contain_both D i w hw r Xs M a₁ x₁ hx₁ E₁ Y₁ hY₁ hst₁ hE₁ a₂ x₂ hx₂ E₂ Y₂ hY₂ hst₂ hE₂
    exact ⟨_, ⟨a, x, hx, E, Y, hY, hst, hE, rfl⟩, h1, h2⟩
  · rintro _ ⟨a, x, hx, E, Y, hY, hst, hE, rfl⟩
    let U := LocDirect.ModuleGaloisRepresentation i w hw M hM
    let X := LocDirect.Xgrep i w hw r x (fun j => hc (x j)) Y hst
    obtain ⟨K', hK', hcrys⟩ := GlobalTheory.T.tensorLocalField_isCrystalline_over_familyField D hFont i r hr Xs w hw n hPot M hSub hM
    have hUdR : IsDR (Br.PD D.loc D.nbr i w hw) U.ρ :=
      hPDR (D.nd.l i) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL hK' U hcrys
    obtain ⟨U', LT', PU, hdual, hrank⟩ := GlobalTheory.T.crystalline_over_extension D hFont hBK hPDR i w hw hdeg M hM K' hK' hcrys
    obtain ⟨X', PX, hX⟩ := GlobalTheory.T.exists_tateDual_localGaloisRep_atPlace D i w hw X
    have hLA := GlobalTheory.T.liftAll_of_blochKatoLiftingFamilyAtPlace D i w hw r hr Xs e hLift M hSub hM a x hx (fun j => hc (x j)) Y hst
    have hsub := GlobalTheory.T.pushouts_mem_span_localSelmerPushouts D hFont i r hr Xs w hw n hPot M hM a x hx (fun j => hc (x j)) E Y hY hst hE
    obtain ⟨m, k', hm, hk', hle⟩ := hLOC.2 (D.nd.l i) (D.nbr i w hw).Kw (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw)
      (goodO_ringOfIntegers _ _) X X U X' U' 1 PX PU (Br.locLat D.nbr i w hw M) LT' e
      ⟨⟨LinearEquiv.refl _ _, fun g v => by simp⟩, hUdR, hX, hdual, Or.inl hLA⟩
    have hmono := GlobalTheory.T.lenMod_mono_left' _ _ (HfD (Br.PD D.loc D.nbr i w hw) (Br.locLat D.nbr i w hw M))
      (Submodule.span_le.2 hsub)
    have hT : finrank (Br.OLL D.nbr i w hw) ↥(Br.locLat D.nbr i w hw M).T = k := by
      have hinj := stdG_inj (O := Br.OLL D.nbr i w hw) (LL := Br.LL D.nbr i w hw) Subtype.val_injective k
      show finrank _ ↥(stdG (Br.OLL D.nbr i w hw) (Br.LL D.nbr i w hw) k) = k
      exact (LinearEquiv.ofInjective _ hinj).finrank_eq.symm.trans (Module.finrank_fin_fun _)
    have h2 : m ≤ 2 * k * e * k' := by
      refine hle.trans ?_
      calc _ ≤ e * (k + k) * k' := by
            gcongr
            · exact hrank
            · exact hT.le
        _ = 2 * k * e * k' := by ring
    calc _ ≤ BlochKatoDuality.lenMod (BlochKatoDuality.spanPush (Br.PD D.loc D.nbr i w hw) X U (Br.locLat D.nbr i w hw M))
          (HfD (Br.PD D.loc D.nbr i w hw) (Br.locLat D.nbr i w hw M)) := hmono
      _ = (m : ℕ∞) := hm
      _ ≤ ((2 * k * e * k' : ℕ) : ℕ∞) := by exact_mod_cast h2
      _ = _ := by
        rw [show lenOl (Br.PD D.loc D.nbr i w hw) (O := Br.OLL D.nbr i w hw) = (k' : ℕ∞) from hk']
        push_cast; ring

end GlobalTheory.Pass.LocDirect
end
end

section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLq.DegDer

variable {g : ℕ} [Fact g.Prime]

theorem tl_one {a n : ℕ} (h : a ≤ n) : tl a (1 : Mt g n) = (1 : Mt g a) := by
  ext i j
  have hi : (i : ℕ) < n := by omega
  have hj : (j : ℕ) < n := by omega
  simp only [tl, entN, hi, hj, and_self, dif_pos, Matrix.one_apply, Fin.ext_iff]

theorem br_one {a b n : ℕ} (h : a + b ≤ n) : br a b (1 : Mt g n) = (1 : Mt g b) := by
  ext i j
  have hi : a + (i : ℕ) < n := by omega
  have hj : a + (j : ℕ) < n := by omega
  simp only [br, entN, hi, hj, and_self, dif_pos, Matrix.one_apply, Fin.ext_iff]
  simp

theorem toG_one {n : ℕ} : toG (1 : Mt g n) = 1 := by
  unfold toG
  rw [dif_pos isUnit_one]
  ext : 1
  simp

theorem hc_one (a b : ℕ) (α : Gn g a → ℂ) (β : Gn g b → ℂ) :
    hc a b α β (a + b) 1 = ((Fintype.card (Gn g a) * Fintype.card (Gn g b) * g ^ (a * b) : ℕ) : ℂ)⁻¹ *
      ((Fintype.card (Gn g (a + b)) : ℂ) * (α 1 * β 1)) := by
  unfold hc hcT
  rw [← GlobalTheory.GLm.ParBasic.card_par]
  congr 1
  simp only [mul_one, inv_mul_cancel, Units.val_one, GlobalTheory.GLm.ParBasic.inPar_one, if_true,
    tl_one (Nat.le_add_right a b), br_one (le_refl (a + b)), toG_one, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]

theorem blockDiagonalWithIdentityGL_one (k : ℕ) : diag1 (1 : Gn g k) (k + 1) = 1 := by
  unfold diag1
  have : (fun i j : Fin (k + 1) => if (i : ℕ) < k ∧ (j : ℕ) < k then entN ((1 : Gn g k) : Mt g k) i j
      else (1 : Mt g (k + 1)) i j) = (1 : Mt g (k + 1)) := by
    ext i j
    split_ifs with h
    · simp only [Units.val_one, entN, h, and_self, dif_pos, Matrix.one_apply, Fin.ext_iff]
    · rfl
  rw [this, toG_one]

theorem prod_pow_add (a b : ℕ) :
    (∏ i : Fin (a + b), (g : ℂ) ^ (i : ℕ)) =
      (∏ i : Fin a, (g : ℂ) ^ (i : ℕ)) * (∏ i : Fin b, (g : ℂ) ^ (i : ℕ)) * (g : ℂ) ^ (a * b) := by
  rw [Fin.prod_univ_add]
  simp only [Fin.coe_castAdd, Fin.coe_natAdd, pow_add, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  rw [← pow_mul]
  ring

theorem prod_Icc_add (f : ℕ → ℂ) (a b : ℕ) :
    (∏ i ∈ Finset.Icc 1 (a + b), f i) = (∏ i ∈ Finset.Icc 1 a, f i) * ∏ i ∈ Finset.Ico (a + 1) (a + b + 1), f i := by
  have e : ∀ n, Finset.Icc 1 n = Finset.Ico 1 (n + 1) := fun n => by ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [e, e, Finset.prod_Ico_consecutive _ (by omega) (by omega)]

theorem card_Gn_factors_ne_zero (n : ℕ) :
    (∏ i : Fin n, (g : ℂ) ^ (i : ℕ)) ≠ 0 ∧ (∏ i ∈ Finset.Icc 1 n, ((g : ℂ) ^ i - 1)) ≠ 0 := by
  have h : (Fintype.card (Gn g n) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [GlobalTheory.GLq.GGDeg.card_Gn] at h
  exact mul_ne_zero_iff.mp h

theorem one_eq_sum_der : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (n : ℕ) (χ : Gn g n → ℂ),
    0 < n → IsClass χ → χ 1 = ∑ m ∈ Finset.range n, der ψ m χ 1 * ∏ i ∈ Finset.Ico (m + 1) n, ((g : ℂ) ^ i - 1) := by
  intro g _ ψ hψ n χ hn hχ
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hM : IsMirClass χ := fun p x _ _ => hχ x p
  have h1 : χ 1 = χ (diag1 (1 : Gn g k) (k + 1)) := by rw [blockDiagonalWithIdentityGL_one]
  rw [h1, GlobalTheory.GLm.mirClass_diag1_eq_sum g ψ hψ k χ hM 1]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ k := by have := Finset.mem_range.mp hi; omega
  obtain ⟨b, rfl⟩ : ∃ b, k = i + b := ⟨k - i, by omega⟩
  have hkb : i + b - i = b := by omega
  rw [hkb, hc_one, (GlobalTheory.GLq.GGDeg.gg_one_and_isClass g ψ b).1]
  push_cast
  rw [GlobalTheory.GLq.GGDeg.card_Gn i, GlobalTheory.GLq.GGDeg.card_Gn b, GlobalTheory.GLq.GGDeg.card_Gn (i + b), prod_pow_add,
    prod_Icc_add]
  obtain ⟨hPi, hQi⟩ := card_Gn_factors_ne_zero (g := g) i
  obtain ⟨hPb, hQb⟩ := card_Gn_factors_ne_zero (g := g) b
  have hg : (g : ℂ) ^ (i * b) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : g.Prime).ne_zero)
  field_simp

end GlobalTheory.GLq.DegDer
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_inclR_smul_mem' :
    ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (s : ℕ)
      {K LL : FinExt l} (T : Lt K LL) {d : ℕ} (b : LatB T d) (y : TW (RW LL) T),
      letI := twTop T b
      ∀ U ∈ 𝓝 (0 : TW (RW LL) T), ∃ k : ℕ, ∀ z : RA LL,
        inclR LL ((((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]]
          (WittVector.teichmuller l (AI.εroot s) - 1)) : RA LL) ^ k * z) • y ∈ U :=
  @GlobalTheory.WeakClosed.exists_pow_inclR_smul_mem
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localCocycles_mem_span_pushout_summandLattice : ∀ (D : D7), FontaineAtPlacesOverL (D := D) → ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))),
    GoodR D.nd i r → ∀ (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (n : ℕ), PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n →
    ∀ (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hSub : SubTw i r Xs M)
      (F : Finset (Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T)),
      (F : Set (Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T)) ⊆ cutCoc i w hw r Xs M →
      ∃ X : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw),
        IsSummandTw i w hw r Xs X ∧
        Submodule.span (Br.OLL D.nbr i w hw) (F : Set (Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T)) ≤
          BlochKatoDuality.spanPush (Br.PD D.loc D.nbr i w hw) X (locU i w hw M hSub.1) (Br.locLat D.nbr i w hw M) := by
  first | exact @GlobalTheory.Pass.LocDual.OneX.main | exact GlobalTheory.Pass.LocDual.OneX.main | (intros; apply GlobalTheory.Pass.LocDual.OneX.main <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrime.FormNonzero

theorem cob_of_vanish {G Λ V : Type} [Group G] [CommRing Λ] [AddCommGroup V] [Module Λ V] (π : Representation Λ G V)
    (L : Subgroup G) (hL : ∀ h ∈ L, ∀ m, π h m = m) (z : G) (d : Λ) (hd : IsUnit (d - 1)) (hz : ∀ m, π z m = d • m)
    (hc : ∀ g, g * z * g⁻¹ * z⁻¹ ∈ L) (f : G → V) (hf : ∀ g h, f (g * h) = f g + π g (f h)) (h0 : ∀ h ∈ L, f h = 0) :
    Cob π f := by
  obtain ⟨u, hu⟩ := hd
  refine ⟨((u⁻¹ : Λˣ) : Λ) • f z, fun g => ?_⟩
  have e1 : f (g * z) = f (z * g) := by
    have : g * z = (g * z * g⁻¹ * z⁻¹) * (z * g) := by group
    rw [this, hf, h0 _ (hc g), hL _ (hc g), zero_add]
  rw [hf, hf, hz] at e1
  rw [map_smul, ← smul_sub]
  have e2 : π g (f z) - f z = (d - 1) • f g := by
    rw [sub_smul, one_smul, sub_eq_sub_iff_add_eq_add, add_comm (π g (f z)), e1, add_comm]
  rw [e2, smul_smul, ← hu, Units.inv_mul, one_smul]

theorem repOn_scalar {G O Λ : Type} [Group G] [CommRing O] [CommRing Λ] [Algebra O Λ] {r : ℕ} (ρ : G →* GL (Fin r) O)
    (κ : G →* Λˣ) (Y : Type) [AddCommGroup Y] [Module Λ Y] (z : G) (d : O) (hκ : κ z = 1)
    (hz : (ρ z : Matrix (Fin r) (Fin r) O) = d • (1 : Matrix (Fin r) (Fin r) O)) (m : Fin r → Y) :
    repOn ρ κ Y z m = algebraMap O Λ d • m := by
  funext a
  simp only [repOn, matAct, MonoidHom.coe_mk, OneHom.coe_mk, hκ, hz, Units.val_one, one_smul, LinearMap.coe_mk,
    AddHom.coe_mk, Matrix.map_apply, Matrix.smul_apply, Pi.smul_apply]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [Matrix.one_apply_ne hb.symm]
  · simp

theorem exists_bform_ne_zero : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), 0 < nu X i → ∀ (M : ℕ) (L : Subgroup (GE N)) (z : GE N), nu X i + 1 ≤ M → IsTameInertiaElementAtTwistPrime X i z → Small2 i s M L z → ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] [TopologicalSpace A] [DiscreteTopology A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Setup bkP i s κ Q → Kills i A → IsDual i s ρ → AntiHom X.cc κ → κ z = 1 → (∀ g ∈ L, κ g = 1) → ∀ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) A) Z, Univ bkP i s κ Q Φ Z → ∀ (x₀ : Fin a → A) (j : Fin a) (c : A) (y : Z1 (repOn ρ κ⁻¹ A)), matAct Φ x₀ = 0 → x₀ j ∣ c → ¬ Cob (repOn ρ κ⁻¹ A) (fun g => ((X.l i : A) ^ nu X i * c) • y.1 g) → ∃ h ∈ L, bform (X := X) (fun g => rect (Z g) x₀) y.1 h ≠ 0 := by
  intro D N X bkP i s hl M L z hM hz hL A _ _ _ _ _ _ κ Q ρ hS hK hρ hanti hκz hκL a Φ Z hU x₀ j c y hx₀ hj hy
  by_contra hcon
  push Not at hcon
  apply hy
  obtain ⟨d, hd, hd2, hd1, he⟩ := GlobalTheory.TwSys.TameScalar.exists_scalar_tmat_of_tame_inertia D N X bkP i s z hS.1.1 hz
  obtain ⟨x, hx, -⟩ := (hU A).1 x₀ hx₀
  have hcl := GlobalTheory.T.two_mul_cocycle_values_zero_on_small_subgroup D N X bkP i s hl M L z hM hz hL A κ Q ρ hS hK hρ hanti hκz hκL x y
    (fun h hh => by rw [hx]; exact hcon h hh)
  let I : Ideal A := Ideal.span {t | ∃ h ∈ L, ∃ b, t = x.1 h b}
  have hjI : x₀ j ∈ I := by
    letI : TopologicalSpace (A ⧸ I) := ⊥
    haveI : DiscreteTopology (A ⧸ I) := ⟨rfl⟩
    have hker : matAct Φ (fun k => I.mkQ (x₀ k)) = 0 := by
      funext k
      have := congrArg I.mkQ (congrFun hx₀ k)

      simpa only [matAct, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul, Pi.zero_apply, map_zero] using this
    obtain ⟨x', hx', -⟩ := (hU (A ⧸ I)).1 _ hker
    have h0 := (hU (A ⧸ I)).2.1 _ hker (by
      rw [← hx']
      refine cob_of_vanish _ L (fun h hh m => ?_) z (algebraMap (X.O0 i) A d) (by simpa using hd1.map (algebraMap (X.O0 i) A))
        (repOn_scalar _ _ _ z _ hκz (by rw [Tgl_coe, hd])) hL.1.2.2.2.1 _ x'.2.2 (fun h hh => ?_)
      · rw [(GlobalTheory.T.twisted_representation_kills_small_subgroup D N X i s hl M L z hM hL A κ ρ hK hρ (A ⧸ I) h hh).1, hκL h hh, Units.val_one, one_smul]
      · funext b
        have e : x'.1 h b = I.mkQ (x.1 h b) := by
          rw [hx, hx']

          simp only [rect, map_sum, map_smul]
        rw [e, Pi.zero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact Ideal.subset_span ⟨h, hh, b, rfl⟩)
    have := congrFun h0 j
    rwa [Pi.zero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
  have hcI : c ∈ I := by
    obtain ⟨t, rfl⟩ := hj
    exact I.mul_mem_right _ hjI
  have hkill : ∀ t ∈ I, ∀ h' ∈ L, ∀ b, (X.l i : A) ^ nu X i * t * y.1 h' b = 0 := by
    intro t ht h' hh' b
    induction ht using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨h, hh, b', rfl⟩ := ht
      exact hcl h hh h' hh' b' b
    | zero => simp
    | add t t' _ _ h1 h2 => rw [mul_add, add_mul, h1, h2, add_zero]
    | smul u t _ h1 => rw [smul_eq_mul]; linear_combination u * h1
  have hρz : (ρ z : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)) = ((d⁻¹ : (X.O0 i)ˣ) : X.O0 i) • 1 := by
    have hinv : (Tmat i s z)⁻¹ = ((d⁻¹ : (X.O0 i)ˣ) : X.O0 i) • 1 := by
      apply Matrix.inv_eq_left_inv
      rw [hd, Matrix.smul_mul, one_mul, smul_smul, Units.inv_mul, one_smul]
    rw [hρ z, Tdual, he, hinv, Units.val_one, one_smul, Matrix.transpose_smul, Matrix.transpose_one]
  have hdi := GlobalTheory.TwSys.TameScalar.isUnit_sub_one _ (GlobalTheory.TwSys.TameScalar.isUnit_inv_sq_sub_one d hd2)
  refine cob_of_vanish _ L (fun h hh m => ?_) z (algebraMap (X.O0 i) A ((d⁻¹ : (X.O0 i)ˣ) : X.O0 i))
    (by simpa only [map_sub, map_one] using hdi.map (algebraMap (X.O0 i) A))
    (repOn_scalar _ _ _ z _ (by simp [hκz]) hρz) hL.1.2.2.2.1 _ (fun g h => ?_) (fun h hh => ?_)
  · rw [(GlobalTheory.T.twisted_representation_kills_small_subgroup D N X i s hl M L z hM hL A κ⁻¹ ρ hK hρ A h hh).2.1]
    simp [hκL h hh]
  · rw [y.2.2, smul_add, map_smul]
  · funext b
    exact hkill c hcI h hh b

end GlobalTheory.NewPrime.FormNonzero
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

theorem _root_.GlobalTheory.T.exists_universalSelmerCocycle_baseChange : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (M : ℕ) (ι : Type) (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (Q : Finset (PlE D.host)) (a : ℕ) (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M ι)), Computes bkP i s M d Q Φ → ∀ (B : Type) [CommRing B] [Algebra (X.O0 i) B] (φ : abelian₂ X i M ι →ₐ[X.O0 i] B) (κ : GE N →* Bˣ), (∀ g, ((κ g : Bˣ) : B) = φ (delInv i M d g : (abelian₂ X i M ι)ˣ)) → Kills i B → ∃ Z, Univ bkP i s κ Q (Φ.map φ) Z := by
  first | exact @GlobalTheory.NewPrime.UnivCocycle.main | exact GlobalTheory.NewPrime.UnivCocycle.main | (intros; apply GlobalTheory.NewPrime.UnivCocycle.main <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

theorem _root_.GlobalTheory.T.universalSelmerCocycle_map_algHom : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (B : Type) [CommRing B] [Algebra (X.O0 i) B] (A : Type) [CommRing A] [Algebra (X.O0 i) A] (π : B →ₐ[X.O0 i] A) (κ : GE N →* Bˣ) (κ' : GE N →* Aˣ), (∀ g, ((κ' g : Aˣ) : A) = π (κ g : Bˣ)) → ∀ (Q : Finset (PlE D.host)) (a : ℕ) (Φ : Matrix (Fin a) (Fin a) B) Z, Univ bkP i s κ Q Φ Z → Univ bkP i s κ' Q (Φ.map π) (fun g => (Z g).map π) := by
  first | exact @GlobalTheory.NewPrime.univ_map | exact GlobalTheory.NewPrime.univ_map | (intros; apply GlobalTheory.NewPrime.univ_map <;> assumption)
end
