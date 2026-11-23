module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RootsOfUnityRingLeWittIntegers
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle119
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsIsoOfIsFiniteOfUniqueLiftOfClassicalPoints
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModuliModelUltrametricPoints
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle102
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle175
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle013
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle008
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LineBundleIsoOfAmpleDeterminantFrames
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle204
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle004
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle126
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle123
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle032
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MovedReadingSameMapsBaseReadingAgrees
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle550
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle551
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSameData
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle218

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.HeightCounting GlobalTheory.TwInputs.Move GlobalTheory.HeightCounting.SideCopy
open Formalism.L2.DIV Formalism.L2.Theta
attribute [local instance] Formalism.BasicNotions.Host.cmStar


noncomputable section

namespace GlobalTheory.HeightCounting.ExpCopy

open GlobalTheory.Mem.R3.Tr

theorem sig_heq {R R' : Ranks} (hR : R = R') {H : Host R} {H' : Host R'} (hH : HEq H H') {T T' : Type} (hT : T = T')
    {f : T ≃ R.Psi} {f' : T' ≃ R'.Psi} (hf : HEq f f') {t : T} {t' : T'} (ht : HEq t t')
    {x : H.E} {x' : H'.E} (hx : HEq x x') :
    HEq (H.sigmaOf ((f t : R.Psi) : R.GG) x)
      (H'.sigmaOf ((f' t' : R'.Psi) : R'.GG) x') := by
  subst hR; cases hH; subst hT; cases hf; cases ht; cases hx; rfl

section
variable {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}

theorem kEmb_heq (h : CopyTw D D' ι e) {i : D.ntw.Tw} {i' : D'.ntw.Tw} (hi : HEq i i') (b : Bool) {t : D.what₂.Tau}
    {t' : D'.what₂.Tau} (ht : HEq t t') {x : D.host.E} {x' : D'.host.E} (hx : HEq x x') :
    HEq (Formalism.L2.NX.kEmb D i b t x) (Formalism.L2.NX.kEmb D' i' b t' x') := by
  have hσ := sig_heq h.gal.R h.gal.host h.Tau h.eTau ht hx
  have hy : e (Formalism.L2.NX.embEL0 D' (D'.host.sigmaOf ((D'.eTau t' : D'.R.Psi) : D'.R.GG) x')) =
      Formalism.L2.NX.embEL0 D (D.host.sigmaOf ((D.eTau t : D.R.Psi) : D.R.GG) x) :=
    Subtype.ext (ι.injective ((h.LL0 _).trans (h.map_embE hσ).symm))
  have := h.sideEmb_heq hi b (Formalism.L2.NX.embEL0 D' (D'.host.sigmaOf ((D'.eTau t' : D'.R.Psi) : D'.R.GG) x'))
  rw [hy] at this
  exact this

theorem side_heq (h : CopyTw D D' ι e) {i : D.ntw.Tw} {i' : D'.ntw.Tw} (hi : HEq i i') (b : Bool) (z : ↥D.LL0) :
    HEq (GlobalTheory.SeriesTie.sideEmb D.ntw i b z) (GlobalTheory.SeriesTie.sideEmb D'.ntw i' b (e.symm z)) := by
  have := h.sideEmb_heq hi b (e.symm z)
  rw [e.apply_symm_apply] at this
  exact this

end

theorem infG_eta {D : D7} {cf : CharFrame D} (hcs : CharSide D cf) (t : D.what₂.Tau) :
    D.naut.infG D.naut.etaT (Formalism.L2.Host.embPsi D.host (D.eTau t)) = {(((1 / 2 : ℚ)) : ℂ)} :=
  (hcs.infG D.naut.etaT (fun _ => 1 / 2) (by rw [hcs.etaT]; exact ⟨fun _ => 1, fun _ => by norm_num, cf.isEta.inf⟩) (D.eTau t)).1



set_option maxRecDepth 100000 in
theorem core (D : D7) (r : Rest D) (X : NExpTied D) (hpl : HEq D.naut.plGw (overD D r).naut.plGw)
    (hhw : ∀ i j b (t : D.what₂.Tau), 1 ≤ j → j ≤ D.R.m →
      ∃ lam : Fin D.R.nV → ℤ, Formalism.L2.NX.HWAtF (Formalism.L2.NX.cE D) (X.rhoW i j b).dual ((by exact NX.kEmb (overD D r) i b t)) lam)
    (hwt : ∀ i j b (t : D.what₂.Tau) (hj : 1 ≤ j) (hjm : j ≤ D.R.m) (sh : ℂ) (lam : Fin D.R.nV → ℤ),
      (overD D r).naut.infG (overD D r).naut.etaT ((by exact embPsi D.host (D.eTau t))) = {sh} →
      Formalism.L2.NX.HWAtF (Formalism.L2.NX.cE D) (X.rhoW i j b).dual ((by exact NX.kEmb (overD D r) i b t)) lam →
      NG.infOf lam = NG.paramV D.R (D.hc t) ⟨j - 1, by omega⟩ sh) :
    ∃ X' : NExpTied (overD D r), HEq X.tauG X'.tauG ∧ ∀ (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
      (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (hA : NX.AdmTw D i k Q ψ),
      HEq (X.mtV i j b k Q ψ h1 h2 hA).QP (X'.mtV ((by exact i)) j b k ((by exact Q)) ((by exact ψ)) h1 ((by exact h2)) ((by exact hA))).QP ∧
      HEq (X.mtV i j b k Q ψ h1 h2 hA).DP (X'.mtV ((by exact i)) j b k ((by exact Q)) ((by exact ψ)) h1 ((by exact h2)) ((by exact hA))).DP ∧
      ∀ (ε : FractionRing (D.ntw.Ok i k) →+* ℂ) (V : Type) [AddCommGroup V] [Module ℂ V]
        (ρ : D.nexp.MtV i j b k Q ψ → Formalism.AUTREP.GAf D.host.E D.R.nV → V),
        GlobalTheory.HeightCounting.Reads X i j b k Q ψ h1 h2 hA ε V ρ →
          GlobalTheory.HeightCounting.Reads X' ((by exact i)) j b k ((by exact Q)) ((by exact ψ)) h1 ((by exact h2)) ((by exact hA)) ((by exact ε)) V ((by exact ρ)) := by
  cases r
  rename NAut _ => n
  cases n
  dsimp only [overD] at hpl
  cases hpl
  refine ⟨@Formalism.L2.NExpTied.mk (_)
      (U_eq := (X.U_eq))
      (psiU_gen := (X.psiU_gen))
      (psiU_side := (X.psiU_side))
      (psiU_xi := (X.psiU_xi))
      (delU_cont := (X.delU_cont))
      (delU_ine := (X.delU_ine))
      (thU_empty := (X.thU_empty))
      (sgnT := (X.sgnT))
      (sgnT_one := (X.sgnT_one))
      (Wt := (X.Wt))
      (acgWt := (X.acgWt))
      (modWt := (X.modWt))
      (fdWt := (X.fdWt))
      (rhoW := (X.rhoW))
      (rhoW_irr := (X.rhoW_irr))
      (rhoW_alg := (X.rhoW_alg))
      (tauG := (X.tauG))
      (sgnG := (X.sgnG))
      (sgnG_one := (X.sgnG_one))
      (tau_galois_first_character := (X.tau_galois_first_character))
      (mtV := fun x1 x2 x3 x4 x5 x6 x7 x8 x9 => @Formalism.L2.NX.MtVReal.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_)
        (W := (@NX.MtVReal.W D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (acg := (@NX.MtVReal.acg D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (mod := (@NX.MtVReal.mod D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (fd := (@NX.MtVReal.fd D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (ρ := (@NX.MtVReal.ρ D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (irr := (@NX.MtVReal.irr D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (alg := (@NX.MtVReal.alg D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (bc := (@NX.MtVReal.bc D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (J := (@NX.MtVReal.J D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (χ := (@NX.MtVReal.χ D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (J_open := (@NX.MtVReal.J_open D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (hyp := (@NX.MtVReal.hyp D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (QP := (@NX.MtVReal.QP D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (QP_sub := (@NX.MtVReal.QP_sub D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (QP_cover := (@NX.MtVReal.QP_cover D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (QP_nconj := (@NX.MtVReal.QP_nconj D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (DP := (@NX.MtVReal.DP D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (DP_sub := (@NX.MtVReal.DP_sub D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (DP_cover := (@NX.MtVReal.DP_cover D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (DP_nconj := (@NX.MtVReal.DP_nconj D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (sp := (@NX.MtVReal.sp D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (sp_w := (@NX.MtVReal.sp_w D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (redG := (@NX.MtVReal.redG D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (J_mem := (@NX.MtVReal.J_mem D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (chi_eq := (@NX.MtVReal.chi_eq D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9)))
        (real := (@NX.MtVReal.real D x1 x2 x3 x4 x5 x6 (@NExpTied.sgnT D X) (@NExpTied.Wt D X x1 x2 x3) (@NExpTied.acgWt D X x1 x2 x3) (@NExpTied.modWt D X x1 x2 x3) (@NExpTied.rhoW D X x1 x2 x3) (@NExpTied.tauG D X x1 x2 x3) (@NExpTied.mtV D X x1 x2 x3 x4 x5 x6 x7 x8 x9))))
      (rhoW_hw := (hhw))
      (rhoW_wt := (hwt)), (HEq.refl X.tauG), fun i j b k Q ψ h1 h2 hA => ⟨?_, ?_, fun ε V _ _ ρ hR => ?_⟩⟩
  · exact (HEq.refl (X.mtV i j b k Q ψ h1 h2 hA).QP)
  · exact (HEq.refl (X.mtV i j b k Q ψ h1 h2 hA).DP)
  · exact (hR)



set_option maxRecDepth 100000 in
theorem expTied_copy : ∀ {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}, CopyAll D D' ι e → ∀ {cf : CharFrame D} {cf' : CharFrame D'}, SameFrame cf cf' → CharSide D cf → CharSide D' cf' → ∀ X : NExpTied D, ∃ X' : NExpTied D', (TauTrue X → TauTrue X') ∧ ∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw), HEq i i' → ∀ (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host)) (Q' : Finset (PlE D'.host)), HEq Q Q' → ∀ (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (ψ' : G D'.host.E D'.nd.Om →* (D'.ntw.Ok i' k)ˣ), HEq ψ ψ' → ∀ (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (h2' : j ≤ D'.R.m) (hA' : NX.AdmTw D' i' k Q' ψ'), ∃ hA : NX.AdmTw D i k Q ψ, HEq (X.mtV i j b k Q ψ h1 h2 hA).QP (X'.mtV i' j b k Q' ψ' h1 h2' hA').QP ∧ HEq (X.mtV i j b k Q ψ h1 h2 hA).DP (X'.mtV i' j b k Q' ψ' h1 h2' hA').DP ∧ ∀ (ε : FractionRing (D.ntw.Ok i k) →+* ℂ) (ε' : FractionRing (D'.ntw.Ok i' k) →+* ℂ), HEq ε ε' → ∀ (V V' : Type) [aV : AddCommGroup V] [mV : Module ℂ V] [aV' : AddCommGroup V'] [mV' : Module ℂ V'], V = V' → HEq aV aV' → HEq mV mV' → ∀ (r : D.nexp.MtV i j b k Q ψ → Formalism.AUTREP.GAf D.host.E D.R.nV → V) (r' : D'.nexp.MtV i' j b k Q' ψ' → Formalism.AUTREP.GAf D'.host.E D'.R.nV → V'), HEq r r' → GlobalTheory.HeightCounting.Reads X i j b k Q ψ h1 h2 hA ε V r → GlobalTheory.HeightCounting.Reads X' i' j b k Q' ψ' h1 h2' hA' ε' V' r' := by
  intro D D' ι e h cf cf' _ hcs hcs' X
  obtain ⟨r, rfl⟩ := h.cp.exists_rest
  have hk : ∀ i b t, Formalism.L2.NX.kEmb D i b t = (by with_unfolding_all exact ((Formalism.L2.NX.kEmb (overD D r) ((by with_unfolding_all exact (i :))) b ((by with_unfolding_all exact (t :)))) :)) := fun i b t =>
    RingHom.ext fun x => (by with_unfolding_all exact (eq_of_heq (α := FractionRing (D.ntw.O i)) (a := Formalism.L2.NX.kEmb D i b t x)
        (a' := (by with_unfolding_all exact ((Formalism.L2.NX.kEmb (overD D r) ((i)) b ((t)) ((x))) : _)))
        ((by with_unfolding_all exact ((kEmb_heq h.cp (i := i) (i' := (i)) (((HEq.refl i))) b (t := t) (t' := (t)) (((HEq.refl t)))
          (x := x) (x' := (x)) (((HEq.refl x)))) : _))) :))
  obtain ⟨X', hτ, hM⟩ := core D r X h.pl
    (fun i j b t h1 h2 => by
      have := X.rhoW_hw i j b t h1 h2
      rw [hk] at this
      exact this)
    (fun i j b t h1 h2 sh lam hsh hw => by
      refine X.rhoW_wt i j b t h1 h2 sh lam ?_ ?_
      · have h3 : ({(((1 / 2 : ℚ)) : ℂ)} : Multiset ℂ) = {sh} := (infG_eta hcs' ((by with_unfolding_all exact (t :)))).symm.trans (c := {sh}) ((by with_unfolding_all exact (hsh :)))
        exact (infG_eta hcs t).trans h3
      · rw [hk]
        exact hw)
  refine ⟨X', fun ⟨τ, hτ'⟩ => ?_, fun i i' hi j b k Q Q' hQ ψ ψ' hψ h1 h2 h2' hA' => ?_⟩
  · have hτ2 : X'.tauG = (by with_unfolding_all exact (X.tauG :)) := (by with_unfolding_all exact ((eq_of_heq (a := X'.tauG) (a' := (by with_unfolding_all exact (X.tauG :))) ((by with_unfolding_all exact (hτ.symm :)))) :))
    refine ⟨fun j kv => (Units.map e.symm.toRingHom.toMonoidHom).comp ((by with_unfolding_all exact ((τ j ((by with_unfolding_all exact (kv :)))) :))), fun i j b kv x h1 h2 => ?_⟩
    rw [hτ2]
    exact (by with_unfolding_all exact ((hτ' ((by with_unfolding_all exact (i :))) j b ((by with_unfolding_all exact (kv :))) ((by with_unfolding_all exact (x :))) h1 ((by with_unfolding_all exact (h2 :)))).trans (eq_of_heq (α := FractionRing (D.ntw.O ((by with_unfolding_all exact (i :)))))
      (a' := (by with_unfolding_all exact ((GlobalTheory.SeriesTie.sideEmb (overD D r).ntw i b (e.symm ((τ j ((kv)) ((x)) : (↥D.LL0)ˣ) : ↥D.LL0))) : _)))
      ((by with_unfolding_all exact ((side_heq h.cp (i := (i)) (i' := i) (((HEq.refl i))) b ((τ j ((kv)) ((x)) : (↥D.LL0)ˣ) : ↥D.LL0)) : _)))) :))
  · cases hi; cases hQ; cases hψ
    refine ⟨(by with_unfolding_all exact (hA' :)), (hM i j b k Q ψ h1 h2 ((by with_unfolding_all exact (hA' :)))).1, (hM i j b k Q ψ h1 h2 ((by with_unfolding_all exact (hA' :)))).2.1, ?_⟩
    intro ε ε' hε V V' aV mV aV' mV' hV haV hmV ρ ρ' hρ hR
    subst hV; cases haV; cases hmV; cases hε; cases hρ
    exact (by with_unfolding_all exact (((hM i j b k Q ψ h1 h2 ((by with_unfolding_all exact (hA' :)))).2.2 ε V ρ hR) :))

end GlobalTheory.HeightCounting.ExpCopy

end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorRef

section Form

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_periodForm {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CharZero W]
    [IsAdicComplete (maximalIdeal W) W] {t : SAB H (Sp W)}
    (P : PELUnif (maximalIdeal W) t) {ϖ : W} (hϖ : Irreducible ϖ) :
    ∃ be ∈ levelForms H 1 P.D.toPre.X, IsMonomial P.D.toPre ![ϖ] ![be] ∧ ∀ y, y ≠ 0 → 0 < be y y := by
  letI := H.starRing
  choose Q hQ using QForm.exists_QVal hϖ P.D
  have hQ' : QForm.IsQ P.D.toPre ϖ Q := hQ
  have hex : ∀ χ, ∃ r, PsiCoord P.D.toPre χ r := fun χ =>
    ((GlobalTheory.PsiCoordLocal.main W P.D inferInstance χ).1).imp fun _ h => h.1
  have h0 : ∀ a, 0 ≤ Q a := fun a => by
    by_cases ha : a = 0
    · rw [ha, QForm.Q_zero hϖ P.D hQ']
    · exact zero_le_one.trans (QForm.Q_pos hϖ P.D hQ' ha)
  let be : LinearMap.BilinForm ℤ P.D.toPre.X :=
    LinearMap.mk₂ ℤ (fun a b => QForm.bHom hϖ P.D hQ' a b)
      (fun a a' b => by simp only [map_add (f := _), AddMonoidHom.add_apply])
      (fun c a b => by simp only [map_zsmul, AddMonoidHom.smul_apply, smul_eq_mul, zsmul_eq_mul, Int.cast_id])
      (fun a b b' => by simp only [map_add (f := _)])
      (fun c a b => by simp only [map_zsmul, smul_eq_mul, zsmul_eq_mul, Int.cast_id])
  have hbe : ∀ a b, be a b = QForm.bOf P.D.toPre Q a b := fun _ _ => rfl
  refine ⟨be, ⟨fun a b => ?_, fun x a b => ?_, fun a b => ?_⟩, fun y => ?_, fun y hy => ?_⟩
  · rw [hbe, hbe, QForm.bOf_comm]
  · rw [hbe, hbe]
    exact QForm.bOf_balance hϖ P.D GlobalTheory.allSixLaws.1 P.oD hQ' x a b
  · simp
  · obtain ⟨r, hr⟩ := hex y
    obtain ⟨u, hu⟩ := GlobalTheory.ValForm.hasVal_coord (hQ y) hr
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (h0 y)
    rw [hn, zpow_natCast, ← map_pow, ← map_mul] at hu
    have e : r = u * ϖ ^ n := (IsFractionRing.injective W (FractionRing W) hu).trans (_root_.mul_comm _ _)
    refine ⟨u, fun _ => n, fun i => ?_, ?_⟩
    · have : i = 0 := Subsingleton.elim _ _
      subst this
      show be y y = _
      rw [hbe, ← QForm.two_Q_eq hϖ P.D hQ', hn]
    · simpa [e] using hr
  · rw [hbe, ← QForm.two_Q_eq hϖ P.D hQ']
    have := QForm.Q_pos hϖ P.D hQ' hy
    omega

end Form

section Trait

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_unif_ext (T : CDVR) (t : SAB H (Sp T.V)) (hp : PolAt t (jK T.V)) :
    ∃ (T' : CDVR) (φ : T.V →+* T'.V) (t' : SAB H (Sp T'.V)), Function.Injective φ ∧ IsLocalHom φ ∧
      Nonempty (SABMap t' t (spMap φ)) ∧ Nonempty (PELUnif (maximalIdeal T'.V) t') := by
  let F := AlgebraicClosure (FractionRing T.V)
  have hF : Function.Injective (algebraMap T.V F) := by
    rw [IsScalarTower.algebraMap_eq T.V (FractionRing T.V) F]
    exact (algebraMap (FractionRing T.V) F).injective.comp (IsFractionRing.injective T.V _)
  have : FaithfulSMul T.V F := (faithfulSMul_iff_algebraMap_injective _ _).2 hF
  have : Algebra.IsAlgebraic T.V F := (IsFractionRing.comap_isAlgebraic_iff (K := FractionRing T.V)).2 inferInstance
  obtain ⟨W, hd, hc, hf, hs⟩ := GlobalTheory.Ex.UnifModel.exists_split T.V F t.G t.semi
  have hi : Function.Injective (algebraMap T.V W) := fun _ _ h => hF (congrArg (fun z : W => (z : F)) h)
  have hz : CharZero W := charZero_of_injective_ringHom hi
  have : FaithfulSMul T.V W := (faithfulSMul_iff_algebraMap_injective _ _).2 hi
  have hl : IsLocalHom (algebraMap T.V W) := inferInstance
  obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull CubePf.cubePull (spMap (algebraMap T.V W)) t
  have j : Function.Injective ((algebraMap W (FractionRing W)).comp (algebraMap T.V W)) :=
    (IsFractionRing.injective W _).comp hi
  let g : FractionRing T.V →+* FractionRing W := IsFractionRing.lift j
  have hp' := GlobalTheory.DatUniq.polAt_pull m hp (jK W) (spMap g)
    ((GlobalTheory.Ex.UnifModel.spMap_comp (IsFractionRing.lift_algebraMap j)).trans
      (GlobalTheory.Ex.UnifModel.spMap_comp fun _ => rfl).symm)
  obtain ⟨P, -⟩ := GlobalTheory.LN.uDvrSt_holds E H W ⟨hd, hc, hz⟩ _ hp' hs
  exact ⟨{ V := W }, algebraMap T.V W, _, hi, hl, ⟨m⟩, ⟨P⟩⟩

theorem closed_mem_abLocus_iff (T : CDVR) {t : SAB H (Sp T.V)} (P : PELUnif (maximalIdeal T.V) t) :
    (closedPoint T.V : Sp T.V) ∈ abLocus t.G ↔ Subsingleton P.D.toPre.X := by
  constructor
  · intro hc
    have hmax : (maximalIdeal T.V ^ (0 + 1)).IsMaximal := by
      rw [zero_add, pow_one]; infer_instance
    have hF : IsField (T.V ⧸ maximalIdeal T.V ^ (0 + 1)) := (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 hmax
    have hle : maximalIdeal T.V ^ (0 + 1) ≤ (closedPoint T.V).asIdeal := by
      rw [zero_add, pow_one]; exact le_rfl
    obtain ⟨q, hq⟩ : closedPoint T.V ∈ Set.range (PrimeSpectrum.comap
        (Ideal.Quotient.mk (maximalIdeal T.V ^ (0 + 1)))) := by
      rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
      exact hle
    let g := P.U.gt 0
    have m : Mono g.i := ⟨fun a b h => g.isKernel.hom_ext h (toUnit_unique _ _)⟩
    have hq' : thick T.V (maximalIdeal T.V) 0 q ∈ abLocus t.G := by
      rw [← hq] at hc; exact hc
    exact ArcNotAbelian.subsingleton_of_mem_abLocus t.G t.semi _ hF _ q hq' P.D.toPre.X g.i g.i_hom
  · intro hs K _ _ s _
    have := (isAbelianScheme_of_unif_of_subsingleton GlobalTheory.allSixLaws.1 GlobalTheory.allSixLaws.2.1 T.V T.cpl P.D P.A t.G t.semi
      P.U hs).proper
    infer_instance

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem charZero_of_point {K : CommRingCat.{0}} [Nontrivial K] (y : Spec K ⟶ Xo.XF c) : CharZero K := by
  let f := Spec.preimage (y ≫ pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
  exact charZero_of_injective_ringHom f.hom.injective


open GlobalTheory.HomExt in
theorem exists_base_trait (Z : Model Xo c β) (hβ : IsDedFrac β) (x : Z.X) :
    ∃ (T : CDVR) (χ : Sp T.V ⟶ Z.X) (y : Sp (FractionRing T.V) ⟶ Xo.XF c),
      χ (closedPoint T.V : Sp T.V) = x ∧ y ≫ Z.j = jK T.V ≫ χ := by
  by_cases hx : x ∈ Set.range Z.j
  · obtain ⟨u, rfl⟩ := hx
    let K := (Xo.XF c).residueField u
    have : CharZero K := charZero_of_point ((Xo.XF c).fromSpecResidueField u)
    obtain ⟨h₁, h₂, h₃⟩ := (GlobalTheory.FrameCmp.cDvr_powerSeries K : CDvr (PowerSeries K))
    let a : Sp (PowerSeries K) ⟶ Xo.XF c := spMap (PowerSeries.C (R := K)) ≫ (Xo.XF c).fromSpecResidueField u
    refine ⟨{ V := PowerSeries K }, a ≫ Z.j, jK _ ≫ a, ?_, Category.assoc _ _ _⟩
    exact (Scheme.Hom.comp_apply a Z.j _).trans (congrArg Z.j ((Scheme.Hom.comp_apply _ _ _).trans
      (Scheme.fromSpecResidueField_apply u _)))
  · obtain ⟨h₁, -, -, _, _, _, _⟩ := GlobalTheory.ModelRelCompare.densePart Z hβ
    obtain ⟨ξ, hξ, hs⟩ := exists_mem_genericPoints_specializes x
    have hξ' := genericPoints_subset_range_of_isDominant Z.j hξ
    have hne : ξ ≠ x := fun e => hx (e ▸ hξ')
    obtain ⟨W, _, _, _, a, h₀, h₁⟩ := exists_complete_discreteValuationRing_of_specializes hs hne
    obtain ⟨y, hy⟩ := exists_lift_of_range_subset Z.j
      (spMap (algebraMap W (FractionRing W)) ≫ a) (by
        rintro _ ⟨t, rfl⟩
        have : spMap (algebraMap W (FractionRing W)) t = (⊥ : PrimeSpectrum W) := by
          apply PrimeSpectrum.ext
          change Ideal.comap (algebraMap W (FractionRing W)) t.asIdeal = ⊥
          rw [@Ideal.eq_bot_of_prime _ _ t.asIdeal t.isPrime]
          exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective _ _)
        rw [Scheme.Hom.comp_apply, this]
        exact h₀ ▸ hξ')
    have hc : CharZero (FractionRing W) := charZero_of_point (K := .of (FractionRing W)) y
    have hc' : CharZero W := ⟨fun p q e => Nat.cast_injective (R := FractionRing W) (by
      simpa using congrArg (algebraMap W (FractionRing W)) e)⟩
    exact ⟨{ V := W }, a, y, h₁, hy⟩

theorem exists_trait (Z : Model Xo c β) (hβ : IsDedFrac β) (x : Z.X) :
    ∃ (T : CDVR) (χ : Sp T.V ⟶ Z.X) (t : SAB H (Sp T.V)) (_ : SABMap t Z.t χ) (_ : PELUnif (maximalIdeal T.V) t),
      χ (closedPoint T.V : Sp T.V) = x ∧ Set.range (jK T.V ≫ χ) ⊆ Set.range Z.j := by
  obtain ⟨T, χ, y, hx, hy⟩ := exists_base_trait Z hβ x
  obtain ⟨_, ⟨m⟩⟩ := exists_sab χ Z.t
  have hp := GlobalTheory.GoodTrait.polAt_of_point Z m (jK T.V) y hy
  obtain ⟨T', φ, t', hi, hl, ⟨m'⟩, ⟨P⟩⟩ := exists_unif_ext T _ hp
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m'
  have j : Function.Injective ((algebraMap T'.V (FractionRing T'.V)).comp φ) :=
    (IsFractionRing.injective T'.V _).comp hi
  let g : FractionRing T.V →+* FractionRing T'.V := IsFractionRing.lift j
  have e : jK T'.V ≫ spMap φ = spMap g ≫ jK T.V :=
    (GlobalTheory.Ex.UnifModel.spMap_comp fun _ => rfl).trans
      (GlobalTheory.Ex.UnifModel.spMap_comp (IsFractionRing.lift_algebraMap j)).symm
  refine ⟨T', spMap φ ≫ χ, t', n, P, ?_, ?_⟩
  · exact (Scheme.Hom.comp_apply (spMap φ) χ _).trans ((congrArg χ (comap_closedPoint φ)).trans hx)
  · rintro _ ⟨p, rfl⟩
    refine ⟨(spMap g ≫ y) p, ?_⟩
    rw [← Scheme.Hom.comp_apply, Category.assoc, hy, ← Category.assoc, ← e, Category.assoc]

end Trait

end GlobalTheory.TorRef
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.PolNormal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem polAt_generic_pull {S T : Type} [CommRing S] [IsDomain S] [CommRing T] [IsDomain T] (i : S →+* T)
    (hi : Function.Injective i) {t : SAB H (Sp S)} {t' : SAB H (Sp T)} (m : SABMap t' t (spMap i))
    (hg : GlobalTheory.LN.PolAt t (Out.jK S)) : GlobalTheory.LN.PolAt t' (Out.jK T) := by
  let ι : FractionRing S →+* FractionRing T :=
    IsLocalization.map (FractionRing T) i (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective i hi)
  refine GlobalTheory.DatUniq.polAt_pull m hg (Out.jK T) (spMap ι) ?_
  simp only [spMap, Out.jK, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact IsLocalization.map_comp _

end GlobalTheory.PolNormal

namespace GlobalTheory.PolNormal

end GlobalTheory.PolNormal

namespace GlobalTheory.PolNormal
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

end GlobalTheory.PolNormal

namespace GlobalTheory.PolNormal

end GlobalTheory.PolNormal
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

theorem _root_.GlobalTheory.T.rows_pass_to_moved_divisionLatticesHeights :
    ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt)
      (Wt : Set B.places.Pl) (O : Obj2 (w.D Z)) (t : RowsT K w Z Wt O.p0)
      (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ)
      (O' : Obj2 (w.D (Db.setDivZ Z N h))),
    O' = DivMv.objMv (w := w) (Z := Z) N h O →
    ∃ t' : RowsT K w (Db.setDivZ Z N h) Wt O'.p0, RowsSame t t' ∧
      HEq t'.r.z.geo (GlobalTheory.Mem.R3.Tr.geoHalf (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩)
        (SRe.upL Z Z.S N h) (iK := t.r.z.alg) t.r.z.geo) ∧
      HEq (SRe.pkOf t') ((SRe.pkOf t).up Z Z.S N h) ∧
      (ObjT O t → ObjT O' t') ∧ (Nonempty (RXs t) → Nonempty (RXs t')) :=
  GlobalTheory.Mem.R3.Rw.DivMv.rows_move_geo
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg

theorem _root_.GlobalTheory.T.liftLevelType_trivial_splitPlaceSupport : ∀ (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (hI : I.Ok) (hV : ValsIn I) (hL : LevOf X I U L) (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (x : (famR X I hX U Xg tr).A.ok t × ℕ) (j : (envL X I hX U Xg tr L cV i t).lev.J) (hj : (envL X I hX U Xg tr L cV i t).isLoc x j),
    (envL X I hX U Xg tr L cV i t).lev.χ j = 1 := by
  first | exact @GlobalTheory.Mem.R3.LiftBrg.SplitChi.chi_loc_lift | exact GlobalTheory.Mem.R3.LiftBrg.SplitChi.chi_loc_lift | (intros; apply GlobalTheory.Mem.R3.LiftBrg.SplitChi.chi_loc_lift <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift

theorem _root_.GlobalTheory.T.weilFiniteVector_fixed_principalLevel_coeffSpace : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.thP_ωP → R.thP_vP → (∀ i t, IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t)) → ∀ i t, ∀ k ∈ Lev.levG (Wc D i) (R.βW i) (R.datWp i R.triv), R.ωP i t (1, k) (R.vP i t) = R.vP i t := by
  first | exact @GlobalTheory.DefLift.Level.om_level_vP | exact GlobalTheory.DefLift.Level.om_level_vP | (intros; apply GlobalTheory.DefLift.Level.om_level_vP <;> assumption)
end
