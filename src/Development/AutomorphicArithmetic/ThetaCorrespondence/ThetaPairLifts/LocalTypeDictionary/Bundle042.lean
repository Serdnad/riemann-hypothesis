module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle503
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle320
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle304
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumTranslateConjugateJetBound
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilRepresentationVacuumSignInertPlaces
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle487
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle023
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaFunctionInfiniteRationalLaw
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle022
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle632
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle673
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle472
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle508
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle641
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle012
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
noncomputable section
namespace GlobalTheory.SplitMoveKappa
theorem jetKappa_split_move : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big) (κ : ℂ), GlobalTheory.MovedKappaEx.JetKap ch p x y κ →
    ∀ (e : Formalism.L2.Theta.AE D), IsSplitIdem D e → ∀ (s : FinPt ch.G p.small) (s' : FinPt ch.G p.big),
    SuppAt e _ (s : GA D (ch.G.V p.small)) → SuppAt e _ (s' : GA D (ch.G.V p.big)) →
    ∃ x₀ y₀ : (Formalism.L2.Theta.AE D)ˣ,
      (∃ a : Formalism.L2.Theta.AE D, (x₀ : Formalism.L2.Theta.AE D) = e * a + (1 - e) ∨ (x₀ : Formalism.L2.Theta.AE D) = cA D e * a + (1 - cA D e)) ∧
      (∃ b : Formalism.L2.Theta.AE D, (y₀ : Formalism.L2.Theta.AE D) = e * b + (1 - e) ∨ (y₀ : Formalism.L2.Theta.AE D) = cA D e * b + (1 - cA D e)) ∧
      ∃ ζ : ℂ, (∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) ∧ ∃ r : ℝ, 0 < r ∧
        GlobalTheory.MovedKappaEx.JetKap ch p (s * x) (s' * y)
          ((r : ℂ) * ζ * ((((ch.G.chrT p x₀)⁻¹ * ch.G.chrS p y₀ : Circle)) : ℂ) * κ) := by
  intro hP hI D Γ _ _ Pl0 T A Ks _ _ _ R ch hch p hp x y κ hκ e he s s' hs hs'
  obtain ⟨x₀, y₀, hx₀, hy₀, ζ, ⟨n, hn, hζ⟩, r, hr, hread⟩ := _root_.GlobalTheory.T.twist_splitMoveFrames_jets hP hI ch hch p hp x y e he s s' hs hs'
  have hC := ch.S.Z.crv
  have he0 := ch.S.Z.e0_is p hp
  have hsd := _root_.GlobalTheory.T.twisted_moved_series_decomposition hP hI ch hch p hp x y
  have hsd' := _root_.GlobalTheory.T.twisted_moved_series_decomposition hP hI ch hch p hp (s * x) (s' * y)
  have hG := (GlobalTheory.InducedType.induced_type D).1
  have he0ne : ch.S.Z.e0 p ≠ 0 := by
    intro h
    have hn := he0.2.2.1
    rw [h] at hn
    have h0 : Formalism.MainNotions.TaylorLogMetric.normSq D (tor0 D D.host.ccK ch.S.Z.δ) (Formalism.MainNotions.StandardLatticesGL3.La0 D (tor0 D D.host.ccK ch.S.Z.δ) (ch.G.pS p).rank (ch.G.pT p).rank) (0 : Formalism.MainNotions.TaylorLogMetric.VC D (ch.G.pS p).rank (ch.G.pT p).rank → ℂ) = 0 := by
      simp [Formalism.MainNotions.TaylorLogMetric.normSq]
    rw [h0] at hn
    exact pow_ne_zero _ (GlobalTheory.ConjJet.thetaZeroNormSq_ne_zero_cmLattice D hG D.host.ccK ch.S.Z.δ _ hC ch.S.Z.pt0) hn.symm
  have hK0 : Formalism.MainNotions.StandardLatticesGL3.KLat D (tor0 D D.host.ccK ch.S.Z.δ) (Formalism.MainNotions.StandardLatticesGL3.La0 D (tor0 D D.host.ccK ch.S.Z.δ) (ch.G.pS p).rank (ch.G.pT p).rank) :=
    Or.inr ⟨_, _, GlobalTheory.NormSum.VacInt.sd_std D _, GlobalTheory.NormSum.VacInt.sd_std D _, rfl⟩
  have hK1 : Formalism.MainNotions.StandardLatticesGL3.KLat D (tor0 D D.host.ccK ch.S.Z.δ) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) := Or.inr ⟨_, _, hsd.1, hsd.2, rfl⟩
  have hK2 : Formalism.MainNotions.StandardLatticesGL3.KLat D (tor0 D D.host.ccK ch.S.Z.δ) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p (s * x) (s' * y)) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p (s * x) (s' * y))) := Or.inr ⟨_, _, hsd'.1, hsd'.2, rfl⟩
  obtain ⟨-, -, -, htrip⟩ := GlobalTheory.ThetaTriple.klat_triples D D.host.ccK ch.S.Z.δ hC (ch.G.pS p).rank (ch.G.pT p).rank
  obtain ⟨μ, hμ⟩ := htrip _ _ _ hK0 hK1 hK2 _ he0.1 he0ne
  have hμ8 : μ ^ 8 = 1 := hμ.2.2.2.2.2.2.2.2.1
  have hμI := hμ.2.2.2.2.2.2.2.2.2
  refine ⟨x₀, y₀, hx₀, hy₀, ζ * μ, ⟨8 * n, by omega, by rw [mul_pow, pow_mul', hζ, pow_mul, hμ8, one_pow, one_pow, one_mul]⟩, r, hr, ?_⟩
  have hd := _root_.GlobalTheory.MovedDict.Entire.differentiable_moved_operator_eval hP hI ch hch p hp x y
  have h1 := hread (fun z => κ * Iop D (tor0 D D.host.ccK ch.S.Z.δ) (Formalism.MainNotions.StandardLatticesGL3.La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p) z) (hd.const_mul κ) hκ
  intro k
  rw [om_toPair_mul, h1 k]
  congr 3
  refine congrArg _ (funext fun z => ?_)
  have hs1 : (fun z => κ * Iop D (tor0 D D.host.ccK ch.S.Z.δ) (Formalism.MainNotions.StandardLatticesGL3.La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p) z) =
      κ • Iop D (tor0 D D.host.ccK ch.S.Z.δ) (Formalism.MainNotions.StandardLatticesGL3.La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p) := rfl
  rw [hs1, GlobalTheory.InertSign.Iop_smul, hμI]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring
end GlobalTheory.SplitMoveKappa
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

theorem _root_.GlobalTheory.T.twist_jetKappa_split_move : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big) (κ : ℂ), GlobalTheory.MovedKappaEx.JetKap ch p x y κ →
    ∀ (e : Formalism.L2.Theta.AE D), IsSplitIdem D e → ∀ (s : FinPt ch.G p.small) (s' : FinPt ch.G p.big),
    SuppAt e _ (s : GA D (ch.G.V p.small)) → SuppAt e _ (s' : GA D (ch.G.V p.big)) →
    ∃ x₀ y₀ : (Formalism.L2.Theta.AE D)ˣ,
      (∃ a : Formalism.L2.Theta.AE D, (x₀ : Formalism.L2.Theta.AE D) = e * a + (1 - e) ∨ (x₀ : Formalism.L2.Theta.AE D) = cA D e * a + (1 - cA D e)) ∧
      (∃ b : Formalism.L2.Theta.AE D, (y₀ : Formalism.L2.Theta.AE D) = e * b + (1 - e) ∨ (y₀ : Formalism.L2.Theta.AE D) = cA D e * b + (1 - cA D e)) ∧
      ∃ ζ : ℂ, (∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) ∧ ∃ r : ℝ, 0 < r ∧
        GlobalTheory.MovedKappaEx.JetKap ch p (s * x) (s' * y)
          ((r : ℂ) * ζ * ((((ch.G.chrT p x₀)⁻¹ * ch.G.chrS p y₀ : Circle)) : ℂ) * κ) := by
  first | exact @_root_.GlobalTheory.SplitMoveKappa.jetKappa_split_move | exact _root_.GlobalTheory.SplitMoveKappa.jetKappa_split_move | (intros; apply _root_.GlobalTheory.SplitMoveKappa.jetKappa_split_move <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section
namespace GlobalTheory.SplitVacAlg
open GlobalTheory.MovedAlg
section Comb
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f₀ : WO S T → ℂ}
end Comb

theorem split_vacuum_algebraic_combination : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T) (N : ℕ) (e : AE D) (P : Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e P → ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal →
    ∀ h ∈ GfC WW, Formalism.L2.Theta.SuppAt e WW h →
      GlobalTheory.MovedAlg.IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (1, h) X.vac) := by
  intro D T _ L μ₀ sc G W i j A A' WW X hPr hInp hLμ hX t N e P hP _ h hh hs
  classical
  have hψ : ∀ u v : WO (GlobalTheory.Grid.neg A) WW, u.map (infPart D) = 0 → v.map (infPart D) = 0 →
      IsAlgebraic ℚ (W.ψ (symplOH (GlobalTheory.Grid.neg A) WW u v)) :=
    fun u v hu hv => GlobalTheory.T.isAlgebraic_stdChar_halfSymplectic_realPart_zero hX.is.isVac.1 (GlobalTheory.Grid.neg A) WW u v hu hv
  have hchr := _root_.GlobalTheory.T.isAlgebraic_splitCharacter_twist hPr hInp hLμ hX
  have vac : IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac X.vac := isAlgComb_self
  have detAlg : ∀ (e' : AE D) (he' : IsSplitIdem D e') (g : GA D WW),
      IsAlgebraic ℚ (((G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)) (GlobalTheory.VecInv.detAt e' he'.1 WW g) : Circle) : ℂ) :=
    fun e' he' g => hchr e' he' _ (by
      change e' * (Formalism.L2.Theta.mt WW g).det + (1 - e') =
        e' * (e' * (Formalism.L2.Theta.mt WW g).det + (1 - e')) + (1 - e')
      rw [mul_add, ← mul_assoc, he'.1, mul_sub, mul_one, he'.1, sub_self, add_zero])
  have hecke : ∀ (e' : AE D) (he' : IsSplitIdem D e') (ϖ : 𝓞 D.host.E) (k : ℕ) (α : GA D WW),
      Formalism.L2.NTheta.IsHeckeElt (stdLatSp WW hX.stdW.1) e' (ϖ : D.host.E) k α →
      IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (1, α) X.vac) := by
    intro e' he' ϖ k α hα
    obtain ⟨Δ, hΔ, heq⟩ := GlobalTheory.T.definiteBottom_splitHecke_vacuum hX t e' he' ϖ k α hα
    rw [heq]
    exact (isAlgComb_sum Δ hΔ).smul (isAlg_mul (detAlg e' he' α) (isAlg_sqrt_inv _))
  obtain ⟨ϖ, hϖ, hϖ2⟩ : ∃ ϖ : 𝓞 D.host.E, ϖ ∈ P.asIdeal ∧ ϖ ∉ P.asIdeal ^ 2 :=
    SetLike.exists_of_lt (by
      simpa using Ideal.pow_right_strictAnti P.asIdeal P.ne_bot P.isPrime.ne_top (by norm_num : 1 < 2))
  have gen := GlobalTheory.T.splitPlace_unitaryPoint_mem_heckeClosure (stdLatSp WW hX.stdW.1) P e ϖ hP hϖ hϖ2 h hh hs
  refine Submonoid.closure_induction
    (motive := fun x _ => IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (1, x) X.vac)) ?_ ?_ ?_ gen
  · intro x hx
    rcases hx with (⟨hk, hks⟩ | ⟨k, hα⟩) | ⟨k, hα⟩
    · rw [GlobalTheory.T.definiteBottom_splitPlace_stabiliser_vacuum hX t e hP.1 x hk hks]
      exact vac.smul (detAlg e hP.1 x)
    · exact hecke e hP.1 ϖ k x hα
    · have hc := ((GlobalTheory.SplitPlace.split_local (stdLatSp WW hX.stdW.1) P e hP).2.2 ϖ hϖ hϖ2).2 k x⁻¹ hα |>.1
      have h2 := hecke (cA D e) (GlobalTheory.SplitScalar.isSplitIdem_conj hP.1)
        ⟨star (ϖ : D.host.E), ϖ.2.map (starRingEnd D.host.E).toIntAlgHom⟩ k _ hc
      exact (congrArg (fun y : GA D WW => IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (1, y) X.vac))
        (inv_inv x)).mp h2
  · show IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t 1 X.vac)
    rw [map_one]
    exact vac
  · intro x y _ _ hx hy
    have e1 : ((1 : GA D A), x * y) = (1, x) * (1, y) := by simp
    rw [e1, map_mul, Module.End.mul_apply]
    exact om_algComb hX hψ t 1 x hx hy
end GlobalTheory.SplitVacAlg
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

theorem _root_.GlobalTheory.T.split_place_vacuum_algebraic : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T) (N : ℕ) (e : AE D) (P : Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e P → ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal →
    ∀ h ∈ GfC WW, Formalism.L2.Theta.SuppAt e WW h →
      GlobalTheory.MovedAlg.IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (1, h) X.vac) := by
  first | exact @_root_.GlobalTheory.SplitVacAlg.split_vacuum_algebraic_combination | exact _root_.GlobalTheory.SplitVacAlg.split_vacuum_algebraic_combination | (intros; apply _root_.GlobalTheory.SplitVacAlg.split_vacuum_algebraic_combination <;> assumption)
end
end
