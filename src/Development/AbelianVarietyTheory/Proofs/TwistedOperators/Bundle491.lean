module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1780
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle001
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealSmulSplit
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle054
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorLaws
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorTestThetaZeroEqThetaSeries
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle039
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle059
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle458
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle136
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle316
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle163
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle357
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle440
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle374
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle152
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle379
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle460
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle386
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle465
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle236
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.SquareComm

open GlobalTheory.RowClaim

theorem natCast_not_mem_of_coprime {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {n p : ℕ}
    (hc : Nat.Coprime n p) (hp : (p : 𝓞 K) ∈ w.asIdeal) : (n : 𝓞 K) ∉ w.asIdeal := by
  intro hn
  obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 hc).map (Int.castRingHom (𝓞 K))
  apply w.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  simp only [eq_intCast, Int.cast_natCast]
  exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ hn) (w.asIdeal.mul_mem_left _ hp)

theorem natCast_mem_w {D : D7} {T : Type} {L : LevCh D T} (P : Places L) {v : HeightOneSpectrum (𝓞 D.host.F)}
    (hv : v ∈ P.S0) {n : ℕ} (hn : (n : 𝓞 D.host.F) ∈ v.asIdeal) : (n : 𝓞 D.host.E) ∈ (P.w v).asIdeal := by
  rw [← P.under_w hv] at hn
  have h : (n : 𝓞 D.host.F) ∈ Ideal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (P.w v).asIdeal := hn
  rwa [Ideal.mem_comap, map_natCast] at h

end GlobalTheory.SquareComm

namespace GlobalTheory.SquareComm

open GlobalTheory.RowClaim

theorem squareStanding_of_setting {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {large₂ : SizeData₂ D}
    {R : RealDat D A Ks} {F : Face D A} (s : HidaSetting large₂ R F) (h11 : 11 ≤ D.host.splitBound) {sc : Consts}
    (G : GridData R.toLevCh sc) (t : T) : SquareStanding G t := by
  classical
  refine ⟨h11, fun w hw => ?_⟩
  obtain ⟨⟨Pm, -, -⟩, -⟩ := s.size
  have hq := D.host.hyp.1
  have hd := D.host.hyp.2.1
  have cop : ∀ p ∈ D.host.levelPrimes, p.Prime →
      Nat.Coprime (D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK) p := by
    intro p hpl hp
    exact Nat.Coprime.mul_left (UpperTheory.Ram.Fun.coprime_condN_of_splitK D.host hp (Pm.level_split p hpl)).symm
      (D.host.ccK_coprime p (by simp [hpl]))
  have cop0 : Nat.Coprime (D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK) (q0 D) := by
    obtain ⟨hp0, hm, hn⟩ := leastSplitAuxiliaryPrimeThetaChain_spec D
    have c1 : Nat.Coprime (Formalism.MainNotions.rPrAv D * LevelStarExponents.condE D) (q0 D) := by
      rw [Nat.Coprime, Nat.gcd_rec, hm]
      simp
    refine Nat.Coprime.mul_left (Nat.Coprime.coprime_dvd_left ⟨Formalism.MainNotions.rPrAv D, by unfold LevelStarExponents.condE; ring⟩ c1) ?_
    exact ((Nat.Prime.coprime_iff_not_dvd hp0).2 hn).symm
  rcases Finset.mem_union.1 hw with hw | hw
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hw
    rcases G.pl.mem_S0_of_sum_eq.1 hv with rfl | hv1
    · exact natCast_not_mem_of_coprime _ cop0 (natCast_mem_w G.pl hv G.pl.basePlace_over_qZero)
    · rcases (S1_mem_OmF D).1 hv1 with h | h | h | h
      · exact natCast_not_mem_of_coprime _ (cop _ (D.host.g_level 0) (D.host.g_prime 0)) (natCast_mem_w G.pl hv h)
      · exact natCast_not_mem_of_coprime _ (cop _ (D.host.g_level 1) (D.host.g_prime 1)) (natCast_mem_w G.pl hv h)
      · exact natCast_not_mem_of_coprime _ (cop _ D.host.pde_level.1 D.host.pde_prime) (natCast_mem_w G.pl hv h)
      · exact natCast_not_mem_of_coprime _ (cop _ D.host.pde_level.2 D.host.pde'_prime) (natCast_mem_w G.pl hv h)
  · have h1 := (s.core.lev.Q_off t w hw).1
    have h2 := s.guard.2 t w hw
    simp only [Nat.cast_mul, w.isPrime.mul_mem_iff_mem_or_mem, not_or] at h1 h2 ⊢
    tauto

end GlobalTheory.SquareComm
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KFinCuspApprox

variable {D : D7}

abbrev avgN (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ) → ℂ)
    (φ : GA D N.V → ℂ) : GA D N.V → ℂ :=
  GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) e φ

def KStab (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (s : Set D.what₂.Tau) (W : Submodule ℂ (GA D N.V → ℂ)) : Prop :=
  ∀ τ ∈ s, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ), N.M.fr τ * g * (N.M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (N.M.ε τ) →
    ∀ f ∈ W, rTr N.V (atTau θ N.V τ g) f ∈ W

theorem kStab_empty (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (W : Submodule ℂ (GA D N.V → ℂ)) : KStab θ N ∅ W := fun _ h => h.elim

end GlobalTheory.KFinCuspApprox

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Ker.RealColAct

open GlobalTheory.Ker.ColChange

theorem pureTensor_compAt {D : D7} {S T : HSp D} (C : Ctx S T) (h : GA D S) {B : C.Bas} (hB : C.IsB B)
    {f : WO S T → ℂ} (hf : C.IsTh f) (Q : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB B) (fun τ => compAt C.θ τ (Formalism.L2.Theta.mt S h)) B f Q =
      C.fvec B f (ColChange.sub C h Q) := by
  have hU : ∀ τ, (compAt C.θ τ (Formalism.L2.Theta.mt S h))⁻¹ = (compAt C.θ τ (Formalism.L2.Theta.mt S h))ᴴ := fun τ =>
    Matrix.inv_eq_left_inv (GlobalTheory.Ker.ColChange.compAt_unitary C h τ)
  have key : ∀ g : WO S T → ℂ, C.IsTh g → ∀ v : FVar D T.rank S.rank,
      aPlusAll (heisO C.ψ S T) C.θ (fun τ => cplxO 1 (C.sB B τ)) (fun τ => compAt C.θ τ (Formalism.L2.Theta.mt S h)) B v g =
        ∑ l, (if (v.2.1 : ℕ) < C.X.p0 then conj (compAt C.θ v.1 (Formalism.L2.Theta.mt S h) l v.2.2)
            else compAt C.θ v.1 (Formalism.L2.Theta.mt S h) l v.2.2) •
          aPlusAll (heisO C.ψ S T) C.θ (fun τ => cplxO 1 (C.sB B τ)) (fun _ => 1) B (v.1, v.2.1, l) g := by
    rintro g hg ⟨τ, i, j⟩
    have hc : ∀ z : Matrix (Fin T.rank) (Fin S.rank) ℂ, aPlus (heisO C.ψ S T) C.θ τ (cplxO 1 (C.sB B τ)) z g =
        ((fockScale D τ : ℂ)⁻¹) • crea (heisO C.ψ S T) C.θ τ (cplxO 1 (C.sB B τ)) z g := by
      intro z
      rw [GlobalTheory.Ker.FockAlg.aPlus_eq C]
      unfold crea
      rw [sub_eq_add_neg, neg_smul]
    change aPlus (heisO C.ψ S T) C.θ τ (cplxO 1 (C.sB B τ)) (unitMap (compAt C.θ τ (Formalism.L2.Theta.mt S h)) (B τ) i j) g =
      ∑ l, (if (i : ℕ) < C.X.p0 then conj (compAt C.θ τ (Formalism.L2.Theta.mt S h) l j)
            else compAt C.θ τ (Formalism.L2.Theta.mt S h) l j) •
        aPlus (heisO C.ψ S T) C.θ τ (cplxO 1 (C.sB B τ)) (unitMap 1 (B τ) i l) g
    simp only [hc]
    rw [GlobalTheory.Ker.ColChange.unitMap_expand, GlobalTheory.Ker.ColChange.crea_sum C hg, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [GlobalTheory.Ker.ColChange.crea_smul C hg τ (C.sB B τ) (unitMap 1 (B τ) i l) ((i : ℕ) < C.X.p0)
      (GlobalTheory.Ker.ColChange.sB_unitMap C hB τ i l), hU τ, Matrix.conjTranspose_apply, smul_smul, smul_smul]
    congr 1
    split_ifs <;> simp [Complex.star_def, mul_comm]
  have Lc := fun P : MvPolynomial (FVar D T.rank S.rank) ℂ =>
    GlobalTheory.Ker.FockAlg.fock_vec_laws D S T C B hB (fun τ => compAt C.θ τ (Formalism.L2.Theta.mt S h)) f hf P
  have L1 := fun P : MvPolynomial (FVar D T.rank S.rank) ℂ =>
    GlobalTheory.Ker.FockAlg.fock_vec_laws D S T C B hB (fun _ => 1) f hf P
  have hX : ∀ v : FVar D T.rank S.rank, ColChange.sub C h (MvPolynomial.X v) =
      ∑ l, (if (v.2.1 : ℕ) < C.X.p0 then conj (compAt C.θ v.1 (Formalism.L2.Theta.mt S h) l v.2.2)
          else compAt C.θ v.1 (Formalism.L2.Theta.mt S h) l v.2.2) • MvPolynomial.X (v.1, v.2.1, l) := fun v =>
    MvPolynomial.aeval_X _ v
  show pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB B) (fun τ => compAt C.θ τ (Formalism.L2.Theta.mt S h)) B f Q =
    pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB B) (fun _ => 1) B f (ColChange.sub C h Q)
  induction Q using MvPolynomial.induction_on
  next a =>
    have e : (MvPolynomial.C a : MvPolynomial (FVar D T.rank S.rank) ℂ) = a • 1 := by
      rw [MvPolynomial.smul_eq_C_mul, mul_one]
    rw [e, map_smul, map_smul, map_smul, map_one (ColChange.sub C h), (Lc 1).2.2.1, (L1 1).2.2.1]
  next p q hp hq =>
    rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
  next p v hp =>

    rw [mul_comm p, (Lc p).2.1 v, hp, key _ (L1 (ColChange.sub C h p)).1 v, map_mul, hX, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_mul_assoc, map_smul, (L1 (ColChange.sub C h p)).2.1]

theorem om_real_fvec : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → ∀ B, C.IsB B → ∀ f, C.IsTh f → C.IsFock B f → ∀ h ∈ GinfC S, ∃ c : ℂ, c ≠ 0 ∧ ∀ Q Q' : MvPolynomial (FVar D T.rank S.rank) ℂ, C.toH Q' = Harm.colActHom (GlobalTheory.Ker.ColChange.colU C h) (C.toH Q) → om (h, 1) (C.fvec B f Q) = c • C.fvec B f Q' := by
  intro D S T C om hom B hB f hf hF h hh
  obtain ⟨φ, hφ, hfφ⟩ := GlobalTheory.Ker.exists_test_of_fock D S T C B hB f hf hF
  obtain ⟨c, hc, hcφ⟩ := GlobalTheory.Ker.RealScalar.om_real_Th D S T C om hom h hh 1 (one_mem _) B hB
  have h1 : C.mvB 1 B = B := GlobalTheory.Ker.ONBasis.mvB_fin C B (one_mem _)
  have hom1 : om (h, 1) f = c • f := by rw [hfφ, hcφ φ hφ, h1]
  refine ⟨c, fun h0 => by simp [h0] at hc, fun Q Q' hQ => ?_⟩
  have hQ' : Q' = ColChange.sub C h Q := C.toH_bijective.1 (by
    rw [hQ]; exact (DFunLike.congr_fun (GlobalTheory.Ker.ColChange.toH_sub C h) Q).symm)
  rw [hQ', GlobalTheory.Ker.WeakMove.om_fvec C hom h 1 hf B Q, h1, hom1,
    pureTensor_compAt C h hB (GlobalTheory.Ker.FockAlg.th_smul C c hf) Q]
  exact (GlobalTheory.Ker.FockAlg.fock_vec_laws D S T C B hB (fun _ => 1) f hf (ColChange.sub C h Q)).2.2.2.2.1 c

end GlobalTheory.Ker.RealColAct

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

theorem _root_.GlobalTheory.T.heisenberg_derivative_mem_fockAlgebraicThetaVectors : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X), ∀ f ∈ algF ψ θ ε A B, ∀ (τ : D.what₂.Tau) (z : Matrix (Fin X.rank) (Fin S.rank) ℂ),
      dRho (heisO ψ (sgn ε S) X) θ τ z f ∈ algF ψ θ ε A B := by
  first | exact @GlobalTheory.SquareComm.dRho_mem_algF | exact GlobalTheory.SquareComm.dRho_mem_algF | (intros; apply GlobalTheory.SquareComm.dRho_mem_algF <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocalPure

variable {D : D7}

theorem wAt_add {m n : ℕ} (p : Place D) (x y : Mx D m n) : wAt p (x + y) = wAt p x + wAt p y := by
  rw [wAt_eq_smul, wAt_eq_smul, wAt_eq_smul, smul_add]

theorem wAt_two {m n : ℕ} (p : Place D) (x : Mx D m n) : wAt p (2 • x) = 2 • wAt p x := by
  rw [wAt_eq_smul, wAt_eq_smul, smul_comm]

theorem wAt_wAt_self {m n : ℕ} (p : Place D) (x : Mx D m n) : wAt p (wAt p x) = wAt p x := by
  rw [wAt_eq_smul, wAt_eq_smul, smul_smul, ((GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).1 p)]

theorem wAt_wAt_ne {m n : ℕ} {p q : Place D} (h : p ≠ q) (x : Mx D m n) : wAt p (wAt q x) = 0 := by
  rw [wAt_eq_smul, wAt_eq_smul, smul_smul, ((GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).2.1 p q h), zero_smul]

theorem wAt_sum_of_notMem {m n : ℕ} {p : Place D} {P : Finset (Place D)} (h : p ∉ P) (x : Mx D m n) :
    wAt p (∑ r ∈ P, wAt r x) = 0 := by
  rw [wAt_eq_smul, Finset.smul_sum]
  refine Finset.sum_eq_zero fun r hr => ?_
  have hpr : p ≠ r := fun e => h (e ▸ hr)
  rw [← wAt_eq_smul]
  exact wAt_wAt_ne hpr x

theorem wAt_sum_of_mem {m n : ℕ} {p : Place D} {P : Finset (Place D)} (h : p ∈ P) (x : Mx D m n) :
    wAt p (∑ r ∈ P, wAt r x) = wAt p x := by
  rw [wAt_eq_smul, Finset.smul_sum, Finset.sum_eq_single_of_mem p h]
  · rw [← wAt_eq_smul]
    exact wAt_wAt_self p x
  · intro r _ hrp
    rw [← wAt_eq_smul]
    exact wAt_wAt_ne (Ne.symm hrp) x

theorem symplO_wAt (S T : HSp D) {p : Place D} (w : WO S T) {z : WO S T} (hz : wAt p z = 0) :
    symplO S T (wAt p w) z = 0 := by
  rw [wAt_eq_smul, GlobalTheory.SplitScalar.symplO_smul, (GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).2.2.1 p, ← wAt_eq_smul, hz,
    GlobalTheory.SplitScalar.symplO_zero_right]

section

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
  {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
  {f₀ : WO S T → ℂ} {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}

theorem ip_base (h : IsBase ψ θ S T sS sT ΛS ΛT f₀) (hμ : IsCovolOne (ratL T S) μ 𝓕) : ipO μ 𝓕 f₀ f₀ = 1 := by
  obtain ⟨-, -, -, -, hff, -⟩ := GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 (base_std h) hμ f₀ f₀ (base_theta h) (base_theta h)
  rw [hff, restrictedTensorBasePoint_norm_sq h hμ]
  simp

theorem ip_heis_wAt (h : IsBase ψ θ S T sS sT ΛS ΛT f₀) (hμ : IsCovolOne (ratL T S) μ 𝓕) (p : Place D) (w : WO S T)
    {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g)
    (vf : VacAt ψ θ S T sS sT ΛS ΛT p f) (vg : VacAt ψ θ S T sS sT ΛS ΛT p g) :
    ipO μ 𝓕 g (heisO ψ S T (wAt p w) f) = ipO μ 𝓕 f₀ (heisO ψ S T (wAt p w) f₀) * ipO μ 𝓕 g f := by
  have h0 := base_vacAt h p
  have hb := base_theta h
  rcases p with v | τ
  · obtain ⟨γ, hγ⟩ := GlobalTheory.T.heisenberg_compression_finite_place_lattice_vacua_scalar D ψ S T ΛS ΛT μ 𝓕 (base_std h) h.2.2.1 h.2.2.2.1 hμ v w
    have e0 := hγ f₀ f₀ hb hb h0 h0
    rw [ip_base h hμ, mul_one] at e0
    rw [hγ f g hf hg vf vg, e0]
  · obtain ⟨γ, hγ⟩ := GlobalTheory.T.heisenberg_compression_real_place_fock_vacua_scalar D ψ θ S T μ 𝓕 (base_std h) (base_inf h) hμ τ (sS τ) (sT τ) (h.1 τ) (h.2.1 τ) w
    have e0 := hγ f₀ f₀ hb hb h0 h0
    rw [ip_base h hμ, mul_one] at e0
    rw [hγ f g hf hg vf vg, e0]

theorem ip_heis_sum (h : IsBase ψ θ S T sS sT ΛS ΛT f₀) (hμ : IsCovolOne (ratL T S) μ 𝓕) (w z : WO S T)
    {y : WO S T → ℂ} (hy : IsThetaFunO ψ S T y) (P : Finset (Place D)) (hz : ∀ p ∈ P, wAt p z = 0)
    (vy : ∀ p ∈ P, VacAt ψ θ S T sS sT ΛS ΛT p y) :
    ipO μ 𝓕 y (heisO ψ S T (∑ p ∈ P, wAt p w + z) f₀) =
      (∏ p ∈ P, ipO μ 𝓕 f₀ (heisO ψ S T (wAt p w) f₀)) * ipO μ 𝓕 y (heisO ψ S T z f₀) := by
  classical
  have hψ := base_std h
  have hb := base_theta h
  have hth := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1
  revert hz vy
  refine Finset.induction_on P ?_ ?_
  · intro _ _
    rw [Finset.sum_empty, zero_add, Finset.prod_empty, one_mul]
  · intro a P ha ih hz vy
    have hzP : ∀ p ∈ P, wAt p z = 0 := fun p hp => hz p (Finset.mem_insert_of_mem hp)
    have vyP : ∀ p ∈ P, VacAt ψ θ S T sS sT ΛS ΛT p y := fun p hp => vy p (Finset.mem_insert_of_mem hp)
    have hZ : wAt a (∑ p ∈ P, wAt p w + z) = 0 := by
      rw [wAt_add, wAt_sum_of_notMem ha, hz a (Finset.mem_insert_self a P), add_zero]
    have hv : VacAt ψ θ S T sS sT ΛS ΛT a (heisO ψ S T (∑ p ∈ P, wAt p w + z) f₀) :=
      (GlobalTheory.T.fockVacua_localFactors_stable_heisenberg_away D ψ θ S T sS sT ΛS ΛT hψ (base_inf h) f₀ hb).1 a _ hZ (base_vacAt h a)
    rw [Finset.sum_insert ha, Finset.prod_insert ha, add_assoc,
      GlobalTheory.SplitScalar.heisO_add_of_orth ψ S T (symplO_wAt S T w hZ),
      ip_heis_wAt h hμ a w (hth _ _ hb) hy hv (vy a (Finset.mem_insert_self a P)), ih hzP vyP]
    ring

private theorem isLatVac_of_isBase (h : IsBase ψ θ S T sS sT ΛS ΛT f₀) :
    IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun _ => True) f₀ := by
  have hv := h.2.2.2.2
  unfold IsVacO at hv
  obtain ⟨-, hv2⟩ := hv
  cases hv2
  assumption

theorem isPure_local (h : IsBase ψ θ S T sS sT ΛS ΛT f₀) (hμ : IsCovolOne (ratL T S) μ 𝓕) (q : Place D)
    (x : Place D → WO S T → ℂ) (hx : IsLocal ψ θ S T sS sT ΛS ΛT q (x q)) (hq : ∀ p, p ≠ q → x p = f₀) :
    IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x (x q) := by
  classical
  have hfull := isLatVac_of_isBase h
  unfold IsPure IsRestricted
  refine ⟨⟨fun p => ?_, ?_⟩, hx.1, fun w => ?_⟩
  · by_cases hpq : p = q
    · subst hpq
      exact hx
    · rw [hq p hpq]
      exact base_isLocal h p
  · refine (Set.finite_singleton q).subset fun p hp => ?_
    by_contra hpq
    exact hp (hq p hpq)
  · obtain ⟨P₀, hP₀⟩ := GlobalTheory.T.exists_eq_sum_weilComponents_add_two_smul_lattice D S T ΛS ΛT h.2.2.1 h.2.2.2.1 w
    obtain ⟨u, hu, hw⟩ := hP₀ (insert q P₀) (Finset.subset_insert q P₀)
    have hqP : q ∈ insert q P₀ := Finset.mem_insert_self q P₀
    generalize insert q P₀ = P at hw hqP

    have key : ∀ p ∈ P, wAt p (2 • u) = 0 := by
      intro p hp
      have e := congrArg (wAt p) hw
      rw [wAt_add, wAt_sum_of_mem hp] at e
      calc wAt p (2 • u) = wAt p w + wAt p (2 • u) - wAt p w := by abel
        _ = wAt p w - wAt p w := by rw [← e]
        _ = 0 := sub_self _
    have hS : symplO S T (∑ p ∈ P, wAt p w) (2 • u) = 0 := by
      refine Finset.sum_induction _ (fun t => symplO S T t (2 • u) = 0) ?_
        (GlobalTheory.SplitScalar.symplO_zero_left S T _) (fun p hp => symplO_wAt S T w (key p hp))
      intro a b (ha : symplO S T a (2 • u) = 0) (hb : symplO S T b (2 • u) = 0)
      show symplO S T (a + b) (2 • u) = 0
      have e := GlobalTheory.SplitScalar.symplO_sub_left S T (a + b) b (2 • u)
      rw [show a + b - b = a by abel, ha, hb, sub_zero] at e
      exact e.symm
    have hsub : Function.mulSupport (fun p => ipO μ 𝓕 (x p) (heisO ψ S T (wAt p w) f₀)) ⊆ ↑P := by
      intro p hp
      by_contra hpP
      apply hp
      have hpq : p ≠ q := fun e => hpP (e ▸ hqP)
      have ew : wAt p w = wAt p (2 • u) := by
        conv_lhs => rw [hw]
        rw [wAt_add, wAt_sum_of_notMem hpP, zero_add]
      show ipO μ 𝓕 (x p) (heisO ψ S T (wAt p w) f₀) = 1
      rw [hq p hpq, ew, wAt_two]
      have hh : heisO ψ S T (2 • wAt p u) f₀ = f₀ := by
        rcases p with v | τ
        · have hv : IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun u => u = v) f₀ := base_vacAt h (.inl v)
          exact hv.1 _ (latO_mono (fun v' hv' => Sum.inl_injective hv'.2)
            (GlobalTheory.T.weilMatrixComponentAtPlace_mem_completedLattice D S T ΛS ΛT (fun _ => True) u hu (.inl v)).1)
        · rw [(GlobalTheory.T.weilMatrixComponentAtPlace_mem_completedLattice D S T ΛS ΛT (fun _ => True) u hu (.inr τ)).2.2 (fun v _ => Sum.inl_ne_inr),
            smul_zero, GlobalTheory.SplitScalar.heisO_zero]
      rw [hh, ip_base h hμ]
    have e1 : heisO ψ S T w f₀ = heisO ψ S T (∑ p ∈ P, wAt p w) f₀ := by
      conv_lhs => rw [hw]
      rw [GlobalTheory.SplitScalar.heisO_add_of_orth ψ S T hS, hfull.1 u hu]
    have e2 : ipO μ 𝓕 (x q) (heisO ψ S T w f₀) =
        (∏ p ∈ P.erase q, ipO μ 𝓕 f₀ (heisO ψ S T (wAt p w) f₀)) * ipO μ 𝓕 (x q) (heisO ψ S T (wAt q w) f₀) := by
      rw [e1, ← Finset.sum_erase_add P (fun p => wAt p w) hqP]
      exact ip_heis_sum h hμ w (wAt q w) hx.1 (P.erase q) (fun p hp => wAt_wAt_ne (Finset.ne_of_mem_erase hp) w)
        (fun p hp => vacAt_of_isLocal hx (Finset.ne_of_mem_erase hp))
    refine ⟨P.finite_toSet.subset hsub, ?_⟩
    rw [finprod_eq_prod_of_mulSupport_subset _ hsub, ← Finset.prod_erase_mul P _ hqP, e2]
    congr 1
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [hq p (Finset.ne_of_mem_erase hp)]

end

theorem isPure_base_and_local : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ (fun _ => f₀) f₀ ∧ ∀ (q : Place D) (x : Place D → WO S T → ℂ), IsLocal ψ θ S T sS sT ΛS ΛT q (x q) → (∀ p, p ≠ q → x p = f₀) → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x (x q) := by
  classical
  intro D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 h hμ
  refine ⟨?_, fun q x hx hq => isPure_local h hμ q x hx hq⟩
  rcases isEmpty_or_nonempty (Place D) with hE | ⟨⟨q⟩⟩
  · unfold IsPure IsRestricted
    refine ⟨⟨fun p => isEmptyElim p, Set.toFinite _⟩, base_theta h, fun w => ⟨Set.toFinite _, ?_⟩⟩
    rw [finprod_of_isEmpty]
    obtain ⟨P₀, hP₀⟩ := GlobalTheory.T.exists_eq_sum_weilComponents_add_two_smul_lattice D S T ΛS ΛT h.2.2.1 h.2.2.2.1 w
    obtain ⟨u, hu, hw⟩ := hP₀ P₀ subset_rfl
    rw [Finset.eq_empty_of_isEmpty P₀, Finset.sum_empty, zero_add] at hw
    rw [hw, (isLatVac_of_isBase h).1 u hu, ip_base h hμ]
  · exact isPure_local h hμ q (fun _ => f₀) (base_isLocal h q) (fun _ _ => rfl)

end GlobalTheory.LocalPure

end
end

section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.AdelicU GlobalTheory.Cusp
open scoped Matrix TensorProduct

theorem _root_.GlobalTheory.T.mem_isotropic_flag_unipotent_iff_split_chain_trivial : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    {V : Formalism.BasicNotions.HSpace E} {v : HeightOneSpectrum (𝓞 F)} (hc : Formalism.BasicNotions.CMData F E), IsCMExt F E hc.sig →
    IsHermND hc.sig V.gram → ∀ (τ : E →ₐ[F] Fv F v) (𝔉 : GlobalTheory.Cusp.IsoFlag V) (g : GlobalTheory.AdelicU.GLoc hc.sig V.gram v),
    g ∈ 𝔉.unip hc (Fv F v) ↔ ∀ j : Fin (2 * 𝔉.k + 1), ∀ u ∈ GlobalTheory.SplitFlag.flagChain 𝔉 τ j.succ,
      ((GlobalTheory.AdelicU.splitHom hc.sig V.gram τ g : GL (Fin V.rank) (Fv F v)) : Matrix (Fin V.rank) (Fin V.rank) (Fv F v)) *ᵥ u - u ∈
        GlobalTheory.SplitFlag.flagChain 𝔉 τ j.castSucc := by
  first | exact @GlobalTheory.SplitFlag.mem_unip_iff_flagChain | exact GlobalTheory.SplitFlag.mem_unip_iff_flagChain | (intros; apply GlobalTheory.SplitFlag.mem_unip_iff_flagChain <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

theorem _root_.GlobalTheory.T.symplecticForm_fockMatrix_eq_neg_sum_im_real_places : ∀ (D : D7) (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (Z Y : VCx D.what₂.Tau S.rank T.rank), GlobalTheory.VacUnique.omO S T (fun τ => fockMat A B τ (Z τ) : GlobalTheory.FockCompare.RW T S) (fun τ => fockMat A B τ (Y τ) : GlobalTheory.FockCompare.RW T S) = -(2 * ∑ τ, ‖tauE D τ D.host.xi0‖ * ∑ i, ∑ j, (Z τ i j * conj (Y τ i j)).im) := by
  first | exact @GlobalTheory.FockOmega.omO_fockMat | exact GlobalTheory.FockOmega.omO_fockMat | (intros; apply GlobalTheory.FockOmega.omO_fockMat <;> assumption)
end
