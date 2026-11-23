module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1282
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2173
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle304
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorThetaFunctionalMixedSourceMode
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle305
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacewiseToAdelicDecompositionForall
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle552
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1803
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2172
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBoundedUnitary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle329
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle220
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle021
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle306
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle022
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle147
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle310
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Matrix.ColumnRowPartitioned
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle016
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame

@[expose] public section

section

noncomputable section
open scoped Matrix ComplexOrder
open Formalism.IndefR.Datum

namespace GlobalTheory.VacuumSplitReal

theorem trace_cartan_of_sig {k t : ℕ} (G s : Matrix (Fin k) (Fin k) ℂ) (hs : IsCartanInv G s)
    (hG : Formalism.UG.HasSignature G t t) (hk : k = 2 * t) : s.trace = 0 := by
  obtain ⟨e, P, hP⟩ := hG
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) ℂ, Q = (P : Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) ℂ) := ⟨_, rfl⟩
  obtain ⟨Q', hQ'⟩ : ∃ Q' : Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) ℂ,
      Q' = ((P⁻¹ : GL (Fin t ⊕ Fin t) ℂ) : Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) ℂ) := ⟨_, rfl⟩
  have hQQ : Q' * Q = 1 := by rw [hQ, hQ', ← Units.val_mul, inv_mul_cancel, Units.val_one]
  let B0 : Matrix (Fin t ⊕ Fin t) (Fin t) ℂ := Matrix.fromRows 1 1
  let C0 : Matrix (Fin t) (Fin t ⊕ Fin t) ℂ := Matrix.fromCols 1 0
  have hC0 : C0 * B0 = 1 := by
    simp [C0, B0, Matrix.fromCols_mul_fromRows]
  have hPP : Qᴴ * G.reindex e e * Q = Formalism.UG.Jpq t t := by
    rw [← hP, hQ]; rfl
  have hB0 : B0ᴴ * Formalism.UG.Jpq t t * B0 = 0 := by
    simp [B0, Formalism.UG.Jpq, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromCols_mul_fromBlocks,
      Matrix.fromCols_mul_fromRows]
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin k) (Fin t) ℂ, B = (Q * B0).submatrix e id := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : Matrix (Fin t) (Fin k) ℂ, C = (C0 * Q').submatrix id e := ⟨_, rfl⟩
  have h1 : C * B = 1 := by
    rw [hB, hC, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id, Matrix.mul_assoc, ← Matrix.mul_assoc Q', hQQ,
      Matrix.one_mul, hC0]
  have h2 : Bᴴ * G * B = 0 := by
    have hG' : G = (G.reindex e e).submatrix e e := by
      ext i j; simp [Matrix.reindex_apply]
    rw [hB, Matrix.conjTranspose_submatrix, hG', Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_id_id]
    have h3 : (Q * B0)ᴴ * G.reindex e e * (Q * B0) = B0ᴴ * (Qᴴ * G.reindex e e * Q) * B0 := by
      rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    rw [h3, hPP, hB0]
  exact GlobalTheory.SplitVacSum.trace_eq_zero hs.1 hs.2.2 (m := t) (by rw [Fintype.card_fin, hk]) B C h1 h2

end GlobalTheory.VacuumSplitReal

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

namespace GlobalTheory.VacuumSplitReal

theorem vacuum_fixed : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A H : HSp D) (t : ℕ) (χA : (AE D)ˣ →* Circle) (om : WRep A H) (sH : RealMat H), IsInfFam θ → (∃ η, GlobalTheory.WeilParts.IsEtaTilde D η) → IsWeilDatumO ψ A H χA 1 om → (∀ τ, IsCartanInv (gramAt D A τ) 1) → (∀ τ, IsCartanInv (gramAt D H τ) (sH τ)) → HSpace.SigOK H → H.rank = 2 * t → (∀ τ, H.sig τ = (t, t)) → ∀ f, IsThetaFunO ψ A H f → (∀ τ, IsFockVacAt (heisO ψ A H) θ τ (cplxO 1 (sH τ)) f) → ∀ b ∈ GinfC A, om (b, 1) f = f := by
  intro D ψ θ A H t χA om sH hθ ⟨η, hη⟩ hW hA hH hsig hrank hsigt f hf hv b hb
  have hdet : ∀ {k : ℕ} {G s : Matrix (Fin k) (Fin k) ℂ}, IsCartanInv G s → G.det ≠ 0 := fun {k G s} hG => by
    have := hG.2.2.det_pos.ne'
    rw [Matrix.det_mul] at this
    exact left_ne_zero_of_mul this
  obtain ⟨x, hx, hxv⟩ := GlobalTheory.VacuumCharacter.exists_root hθ A (fun τ => hdet (hA τ)) b hb
  have mt1 : ∀ τ, compAt θ τ (Formalism.L2.Theta.mt H 1) = 1 := fun τ => by
    unfold Formalism.L2.Theta.mt compAt
    rw [map_one, Units.val_one]
    exact Matrix.map_one _ (by simp) (by simp)
  have h1 : ∀ τ, HasInfExp D 1 τ 0 := fun τ => ⟨0, by norm_num, ⟨θ, hθ⟩, fun _ _ _ _ _ => by simp⟩
  have hexp : ∀ τ, HasInfExp D (1 * (η ^ H.rank)⁻¹) τ ((-(t : ℤ) : ℤ) : ℚ) := fun τ => by
    have h := GlobalTheory.VacuumCharacter.hasInfExp_twist (h1 τ) (hη.2.2.2 τ) H.rank
    convert h using 1
    rw [hrank]; push_cast; ring
  have hν := hxv _ (fun _ => -(t : ℤ)) hexp
  rw [GlobalTheory.WeilVacChar.vacuum_character D ψ hW.std A H θ hθ χA 1 om η hη hW (fun _ => 1) sH hA hH b hb 1 (one_mem _)
    (fun τ => by rw [one_mul, mul_one]) (fun τ => by rw [mt1, one_mul, mul_one]) x 1 hx ?_ f hf hv]
  · conv_rhs => rw [← one_smul ℂ f]
    congr 1
    rw [Circle.coe_mul, Circle.coe_inv, hν, MonoidHom.map_one, Circle.coe_one, mul_one, ← Finset.prod_inv_distrib,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun τ _ => ?_
    obtain ⟨p, hp, hd⟩ := GlobalTheory.VacuumCharacter.detPlus_one (n := A.rank) (sH τ) (hH τ).1
    have htr : (sH τ).trace = 0 := by
      have hs := hsig (tauE D τ)
      rw [hsigt] at hs
      exact trace_cartan_of_sig (gramAt D H τ) (sH τ) (hH τ) hs hrank
    have hpt : p = t := by
      have : (p : ℂ) = t := by
        rw [htr, hrank] at hp; push_cast at hp; linear_combination -hp / 2
      exact_mod_cast this
    have inv : (compAt θ τ (Formalism.L2.Theta.mt A b)).det * (compAt θ τ (Formalism.L2.Theta.mt A b⁻¹)).det = 1 := by
      rw [GlobalTheory.VacuumCharacter.det_compAt, GlobalTheory.VacuumCharacter.det_compAt, ← map_mul, ← map_mul, ← Matrix.det_mul]
      unfold Formalism.L2.Theta.mt
      rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.det_one, map_one, map_one]
    have d0 := left_ne_zero_of_mul_eq_one inv
    rw [mt1, (hd _ 1 (by rw [one_mul, mul_one])).1, eq_inv_of_mul_eq_one_right inv, hpt, mul_one,
      show (1 / 2 : ℂ) • (1 + sH τ) + (1 / 2 : ℂ) • (1 - sH τ) = 1 by module, Matrix.det_one, one_pow, one_mul,
      zpow_neg, inv_inv, zpow_natCast, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ d0)]
  · unfold Formalism.L2.Theta.IsDetRoot
    simp

end GlobalTheory.VacuumSplitReal

end
end

section

open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW

namespace GlobalTheory.Core.Rk.SchwInj

theorem sch_heisO_extY {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (A B : HSp D)
    {ν : Measure (WO A B)} {𝓨 : Set (WO A B)} (hν : IsCovolOne (ratL B A) ν 𝓨) {f : WO (dblSp A) B → ℂ}
    (hf : IsThetaFunO ψ (dblSp A) B f) (x y : Mx D B.rank A.rank) :
    sch ψ A B ν 𝓨 (heisO ψ (dblSp A) B ((dblDec A).extY B y) f) x =
      ψ (symplO (dblSp A) B ((dblDec A).extX B x) ((dblDec A).extY B y)) * sch ψ A B ν 𝓨 f x :=
  congrFun ((GlobalTheory.HeisMixSource.heis_mixS D ψ hψ (dblSp A) (zeroSp D) B A.rank (dblDec A) ⟨ν, 𝓨, hν⟩ f hf).2.1 x y) 0

theorem exists_extX_add_extY {D : D7} (A B : HSp D) (w : WO (dblSp A) B) :
    ∃ x y : Mx D B.rank A.rank, w = (dblDec A).extX B x + (dblDec A).extY B y := by
  obtain ⟨⟨x, w₀, y⟩, rfl⟩ := ((dblDec A).coordS B).symm.surjective w
  have hw : w₀ = 0 := Matrix.ext fun _ j => Fin.elim0 j
  subst hw
  refine ⟨x, y, ?_⟩
  show (dblDec A).extX B x + (dblDec A).ext0 B 0 + (dblDec A).extY B y = _
  rw [map_zero, add_zero]

theorem eq_zero_of_sch_eq_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ f, IsThetaFunO ψ (dblSp A) B f → sch ψ A B ν 𝓨 f = 0 → f = 0 := by
  intro D ψ hψ A B ν 𝓨 hν f hf hs
  funext w
  obtain ⟨x, y, rfl⟩ := exists_extX_add_extY A B w
  have hg := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf ((dblDec A).extY B y)
  have hsum := (GlobalTheory.T.doubledTheta_eq_sum_schrodingerFunction_periodisation D ψ hψ A B ν 𝓨 hν _ hg x).2
  simp only [sch_heisO_extY hψ A B hν hf, hs, Pi.zero_apply, mul_zero] at hsum
  have h0 : ψ (symplOH (dblSp A) B ((dblDec A).extX B x) ((dblDec A).extY B y)) *
      f ((dblDec A).extX B x + (dblDec A).extY B y) = 0 := hsum.unique hasSum_zero
  refine (mul_eq_zero.1 h0).resolve_left fun h => ?_
  have h1 := ψ.map_add_eq_mul (symplOH (dblSp A) B ((dblDec A).extX B x) ((dblDec A).extY B y))
    (-symplOH (dblSp A) B ((dblDec A).extX B x) ((dblDec A).extY B y))
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at h1
  exact one_ne_zero h1

end GlobalTheory.Core.Rk.SchwInj
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.besselLink_kappa_preserves_supported_matrices : ∀ (D : D7) (ρ : ℕ) (B : BesLev D ρ) (L' : HSp D) (ζ' : Fin L'.rank → D.host.E) (l : Link B L' ζ') (S : HSp D) (P : Pl D → Prop) (w : WO S L'), MxAt P w → MxAt P (l.κ S w) := by
  first | exact @GlobalTheory.LinkKapMx.mxAt_linkKappa | exact GlobalTheory.LinkKapMx.mxAt_linkKappa | (intros; apply GlobalTheory.LinkKapMx.mxAt_linkKappa <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.besselLink_kappa_surjective_supported_conjugateHalf : ∀ (D : D7) (ρ : ℕ) (B : BesLev D ρ) (L' : HSp D) (ζ' : Fin L'.rank → D.host.E) (l : Link B L' ζ') (S : HSp D) (P : Pl D → Prop) (h : WO B.L S), ∃ x : WO S L', l.κ S x = h ∧ (MxAt P h → MxAt P x) ∧ ∀ e : AE D, IsHalf e h → IsHalf (cA D e) x := by
  first | exact @GlobalTheory.LinkKapInv.kappa_inv | exact GlobalTheory.LinkKapInv.kappa_inv | (intros; apply GlobalTheory.LinkKapInv.kappa_inv <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_nat_mul_splitHalf_latticeCoordinates_integral : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (S T : HSp D) (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∃ N : ℕ, 0 < N ∧ ∀ u ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v), IsHalf p.e u → ∀ i j, (N : k) * rd α β u i j ∈ 𝒪[k] := by
  first | exact @GlobalTheory.FinPl.RdBound.exists_nat_mul_rd_mem | exact GlobalTheory.FinPl.RdBound.exists_nat_mul_rd_mem | (intros; apply GlobalTheory.FinPl.RdBound.exists_nat_mul_rd_mem <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel ValuativeRel
open scoped Pointwise

theorem _root_.GlobalTheory.T.splitPlaceHermitianFrame_properties : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] (β : Frame p S n), (∀ h : GA D S, h ∈ grpAt S (· = p.v) ↔ ∃ g, h = β.gl g) ∧ Function.Injective β.gl ∧ Continuous β.gl ∧ (∀ L : Lat S, IsSelfDualC S L → ∃ Λ : Submodule 𝒪[k] (n → k), Λ.IsLattice k ∧ β.IsLat L Λ ∧ ∀ g, InK S L (· = p.v) (β.gl g) ↔ g • Λ = Λ) ∧ (∀ (L : Lat S) (Λ : Submodule 𝒪[k] (n → k)), IsSelfDualC S L → Λ.IsFullLattice k → ∃ M : Lat S, IsSelfDualC S M ∧ β.IsLat M Λ ∧ latV S M (· ≠ p.v) = latV S L (· ≠ p.v)) ∧ ∀ g, ∃ x : (AE D)ˣ, IsDetAt p.e S (β.gl g) x ∧ p.pr x = g.val.det := by
  first | exact @GlobalTheory.FrameAt.frame_facts | exact GlobalTheory.FrameAt.frame_facts | (intros; apply GlobalTheory.FrameAt.frame_facts <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair ValuativeRel NumberField Filter
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.HalfInd

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p : SplitPt D k} {S T : HSp D} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

def wr (α : Frame p S n') (β : Frame p T n) : Matrix n n' k →+ WO S T where
  toFun x := (β.b * x * α.b').map p.sec
  map_zero' := by rw [Matrix.mul_zero, Matrix.zero_mul, Matrix.map_zero _ (map_zero _)]
  map_add' x y := by rw [Matrix.mul_add, Matrix.add_mul, Matrix.map_add _ (map_add _)]

theorem wr_apply (α : Frame p S n') (β : Frame p T n) (x : Matrix n n' k) (i : Fin T.rank) (j : Fin S.rank) :
    wr α β x i j = p.sec ((β.b * x * α.b') i j) := rfl

theorem rd_eq (α : Frame p S n') (β : Frame p T n) (t : WO S T) :
    rd α β t = β.b' * (Matrix.map t p.pr : Matrix (Fin T.rank) (Fin S.rank) k) * α.b := rfl

theorem isHalf_wr (α : Frame p S n') (β : Frame p T n) (x : Matrix n n' k) : IsHalf p.e (wr α β x) := fun i j => by
  rw [wr_apply, ← p.sec_pr, p.pr_sec]

theorem wr_rd (α : Frame p S n') (β : Frame p T n) {t : WO S T} (ht : IsHalf p.e t) : wr α β (rd α β t) = t := by
  ext i j
  rw [wr_apply, rd_eq, Matrix.mul_assoc β.b', ← Matrix.mul_assoc β.b, β.bb', Matrix.one_mul, Matrix.mul_assoc, α.bb',
    Matrix.mul_one, Matrix.map_apply, p.sec_pr, ht i j]



theorem open_compact_sec (p : SplitPt D k) {LS : Lat S} {LT : Lat T} (hS : Submodule.IsFullLattice D.host.E LS)
    (hT : Submodule.IsFullLattice D.host.E LT) :
    IsOpen {y : Matrix (Fin T.rank) (Fin S.rank) k | y.map p.sec ∈ latO S T (LS : Set _) (LT : Set _) fun _ => True} ∧
    IsCompact {y : Matrix (Fin T.rank) (Fin S.rank) k |
      y.map p.sec ∈ latO S T (LS : Set _) (LT : Set _) fun _ => True} := by
  have : CharZero k := charZero_of_injective_ringHom (f := p.pr.comp (incA D)) (RingHom.injective _)
  obtain ⟨M, hM, hden⟩ := GlobalTheory.PlaceDatum.exists_den_latO (S := S) (T := T) hS.toIsLattice.fg hT.toIsLattice.fg
  obtain ⟨N, hN, hmul⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO (S := S) (T := T) hS hT
  let A : AddSubgroup (Matrix (Fin T.rank) (Fin S.rank) k) :=
    (latO S T (LS : Set _) (LT : Set _) fun _ => True).comap p.sec.mapMatrix
  have hA : ∀ y, y ∈ A ↔ y.map p.sec ∈ latO S T (LS : Set _) (LT : Set _) fun _ => True := fun _ => Iff.rfl
  have hO : ∀ a : k, a ∈ (𝒪[k]).toAddSubgroup ↔ finPart D (p.sec a) ∈ intAE D := p.int_iff
  have key := GlobalTheory.PlaceCoord.isOpen_isCompact_of_comm (𝒪[k]).toAddSubgroup
    (Valuation.isOpen_integer (v := valuation k)) (IsNonarchimedeanLocalField.isCompact_closedBall k 1) A hN hM
    (fun y hy => by
      have ht : IsHalf p.e (y.map p.sec : WO S T) := fun i j => by
        rw [Matrix.map_apply, ← p.sec_pr, p.pr_sec]
      have h1 : (N • y).map p.sec = N • y.map p.sec := Matrix.ext fun i j => map_nsmul p.sec N (y i j)
      rw [hA, h1]
      exact hmul _ (GlobalTheory.PlaceDatum.infPart_of_half (GlobalTheory.PlaceCoord.infPart_split p.split) ht) fun i j =>
        GlobalTheory.PlaceCoord.toEAf_mem ((hO _).1 (hy i j)))
    (fun y hy i j => by
      have h1 : p.sec ((M : k) * y i j) = (M : AE D) * p.sec (y i j) := by
        rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]
      rw [hO, h1]
      refine GlobalTheory.PlaceDatum.finPart_mem_of_toEAf ?_
      rw [RingHom.map_mul, map_natCast]
      exact hden _ ((hA y).1 hy) i j)
  exact key

theorem exists_idem (p : SplitPt D k) : ∃ ε, IsPlaceIdem D p.v ε ∧ algebraMap (AF D.host.F) (AE D) ε * p.e = p.e := by
  obtain ⟨ε, hε, h⟩ := p.above
  exact ⟨ε, hε, by rw [← h, add_mul, p.split.1, mul_comm, p.split.2.1, add_zero]⟩

theorem compact_open (α : Frame p S n') (β : Frame p T n) {LS : Lat S} {LT : Lat T} (hS : IsSelfDualC S LS)
    (hT : IsSelfDualC T LT) :
    IsCompact {x | wr α β x ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v) ∧ IsHalf p.e (wr α β x)} ∧
      IsOpen {x | wr α β x ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v) ∧ IsHalf p.e (wr α β x)} := by
  obtain ⟨ε, hε, heε⟩ := exists_idem p
  have hh : ∀ x, wr α β x ∈ GlobalTheory.PlaceModel.half S T p.e := fun x => (GlobalTheory.PlaceModel.isHalf_iff S T).1 (isHalf_wr α β x)
  obtain ⟨ho, hc⟩ := open_compact_sec p (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull S LS hS)
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull T LT hT)
  have h1 : {x | wr α β x ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v) ∧ IsHalf p.e (wr α β x)} =
      {x | wr α β x ∈ latO S T (LS : Set _) (LT : Set _) fun _ => True} := by
    ext x
    refine ⟨fun h => GlobalTheory.PlaceModel.latO_le_top _ h.1, fun h => ⟨?_, isHalf_wr α β x⟩⟩
    have h2 := (GlobalTheory.PlaceModel.idem_smul_mem hε p.split.1 heε h).1
    rwa [(GlobalTheory.PlaceModel.mem_half S T).1 (hh x)] at h2
  rw [h1]
  refine ⟨?_, ho.preimage (f := fun x : Matrix n n' k => β.b * x * α.b')
    ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)⟩
  convert hc.image (f := fun y => β.b' * y * α.b)
    ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const) using 1
  ext x
  refine ⟨fun h => ⟨β.b * x * α.b', h, ?_⟩, ?_⟩
  · beta_reduce
    rw [Matrix.mul_assoc β.b, ← Matrix.mul_assoc β.b', β.b'b, Matrix.one_mul, Matrix.mul_assoc, α.b'b, Matrix.mul_one]
  · rintro ⟨y, hy, rfl⟩
    change (β.b * (β.b' * y * α.b) * α.b').map p.sec ∈ latO S T (LS : Set _) (LT : Set _) fun _ => True
    rwa [Matrix.mul_assoc β.b', ← Matrix.mul_assoc β.b, β.bb', Matrix.one_mul, Matrix.mul_assoc, α.bb', Matrix.mul_one]

theorem exists_SB_extFun_eq_halfInd : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S T : HSp D) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∃ Ψ : Matrix n n' k → ℂ, Ψ ∈ GlobalTheory.SplitWeil.SB (Matrix n n' k) ∧ extFun α β Ψ = halfInd p.e (latO S T (LS : Set _) (LT : Set _) (· = p.v)) := by
  intro D k _ _ _ _ p S T n n' _ _ _ _ α β LS LT hS hT
  have := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := k) (n := n) (n' := n')
  obtain ⟨hc, ho⟩ := compact_open α β hS hT
  refine ⟨fun x => halfInd p.e (latO S T (LS : Set _) (LT : Set _) (· = p.v)) (wr α β x), ?_, ?_⟩
  · unfold halfInd
    convert GlobalTheory.FinPl.Comm.ite_mem_SB hc ho
  · funext t
    unfold extFun
    by_cases ht : IsHalf p.e t
    · rw [if_pos ht]
      beta_reduce
      rw [wr_rd α β ht]
    · rw [if_neg ht, halfInd, if_neg fun h => ht h.2]

end GlobalTheory.FinPl.HalfInd

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unf.Inhab

variable {D : D7}

theorem nonempty_vol (V : HSp D) : Nonempty (Vol V) :=
  let ⟨μ, 𝓕, h1, h2⟩ := GlobalTheory.RawLift.exists_haar_fundDomain V
  ⟨⟨μ, 𝓕, h1, h2⟩⟩

theorem nonempty_volN {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) : Nonempty (VolN d) :=
  let ⟨ν, 𝓝, h⟩ := GlobalTheory.Per.UnitN.exists_isUnitN D S ρ d.e (isIsoSub_e d)
  ⟨⟨ν, 𝓝, h⟩⟩

theorem nonempty_volM (D : D7) (m n : ℕ) : Nonempty (VolM D m n) :=
  let ⟨μ, 𝓕, h⟩ := exists_isCovolOne D m n
  ⟨⟨μ, 𝓕, h⟩⟩

theorem nonempty_volU (D : D7) (ρ : ℕ) : Nonempty (VolU D ρ) :=
  let ⟨ν, h⟩ := (GlobalTheory.UnitU.isUnitU_exists_unique_rightInvariant D ρ).1
  ⟨⟨ν, h⟩⟩

theorem coCpt_of_mul {V : HSp D} (h : ∃ K : Set (GA D V), IsCompact K ∧ ∀ g, ∃ γ ∈ GQ V, ∃ k ∈ K, g = γ * k) : CoCpt V := by
  obtain ⟨K, hK, h⟩ := h
  refine ⟨K, hK, fun g => ?_⟩
  obtain ⟨γ, hγ, k, hk, rfl⟩ := h g
  exact ⟨γ⁻¹, inv_mem hγ, by rwa [inv_mul_cancel_left]⟩

theorem coCpt_of_isAniso {V : HSp D} (h : IsAniso V) : CoCpt V :=
  coCpt_of_mul (GlobalTheory.Mem.AnisoQuotient.exists_compact D V h)

theorem coCpt_of_posDef {V : HSp D} (h : ∀ τ, (gramAt D V τ).PosDef) : CoCpt V :=
  coCpt_of_mul (GlobalTheory.definite_unitary_cocompact V h)

theorem exists_weil {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D) {χS χT : (AE D)ˣ →* Circle}
    (h1 : IsHeckeChar D χS) (h2 : IsHeckeChar D χT) (h3 : ResEta D χS S.rank) (h4 : ResEta D χT T.rank) :
    ∃ om, IsWeilDatumO ψ S T χS χT om :=
  GlobalTheory.WeilExist.exists_isWeilDatumO D ψ hψ S T χS χT (GlobalTheory.WeilParts.exists_isEtaTilde_unramified D) h1 h2 h3 h4

theorem nonempty_step {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (V V₀ W W₀ : HSp D) (ρ σ : ℕ)
    (hV : V.rank % 2 = V₀.rank % 2) (hW : W.rank % 2 = W₀.rank % 2) : Nonempty (Step ψ V V₀ W W₀ ρ σ) := by
  obtain ⟨χV, a1, a2⟩ := GlobalTheory.RawLift.exists_hecke_resEta D V.rank
  obtain ⟨χW, b1, b2⟩ := GlobalTheory.RawLift.exists_hecke_resEta D W.rank
  obtain ⟨om, h⟩ := exists_weil hψ V W a1 b1 a2 b2
  obtain ⟨om₀, h₀⟩ := exists_weil hψ V₀ W₀ a1 b1 (resEta_parity a2 hV) (resEta_parity b2 hW)
  obtain ⟨vW⟩ := nonempty_vol W
  obtain ⟨vS⟩ := nonempty_volM D W.rank ρ
  obtain ⟨vT⟩ := nonempty_volM D σ V₀.rank
  obtain ⟨vU⟩ := nonempty_volU D ρ
  exact ⟨⟨χV, χW, om, om₀, h, h₀, vW, vS, vT, vU⟩⟩

theorem even_im_hermitian_sub {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) : S.rank % 2 = S₀.rank % 2 := by
  have := d.rank_add
  omega

theorem nonempty_stepBF {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {ρ : ℕ} (B : BesLev D ρ) (J : JacLev D ρ) :
    Nonempty (StepBF ψ B J) :=
  nonempty_step hψ _ _ _ _ _ _ (even_im_hermitian_sub B.d) (even_im_hermitian_sub J.d)

theorem nonempty_stepFB {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {σ : ℕ} (J : JacLev D (σ + 1))
    (B : BesLev D σ) : Nonempty (StepFB ψ J B) :=
  nonempty_step hψ _ _ _ _ _ _ (even_im_hermitian_sub J.d) (even_im_hermitian_sub B.d)

theorem cmHost_imaginaryGenerator_ne_zero (D : D7) : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D

end GlobalTheory.Unf.Inhab

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lastPeriodClasses_give_tailReading : ∀ (D : D7) (c : Comm D) (t : Tup c) (ρ : RealD c) (A : ClsT ρ t), A.Is → t.cP ≠ 0 → t.TailRd := by
  first | exact @GlobalTheory.SeeSaw.tailRd_of_clsT | exact GlobalTheory.SeeSaw.tailRd_of_clsT | (intros; apply GlobalTheory.SeeSaw.tailRd_of_clsT <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

theorem _root_.GlobalTheory.T.scalarComponent_parameters_contain_string : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t h, GlobalTheory.Hk3.IsOpsV R i t h → ∀ s y, IsEigV R i t h s y → ∀ l : (R.cV i).W →ₗ[ℂ] ℂ, (fun g => l (R.extV i t y g)) ≠ 0 → ∀ B, GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) (Vc D i).rank s B → GlobalTheory.LFun.IsParamFunV (Vc D i) (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) (fun g => l (R.extV i t y g)) B := by
  first | exact @GlobalTheory.LiftParams.param_of_sysParam | exact GlobalTheory.LiftParams.param_of_sysParam | (intros; apply GlobalTheory.LiftParams.param_of_sysParam <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

theorem _root_.GlobalTheory.T.selfDualLattices_single_orbit_tamePlace : ∀ (D : D7) (S₀ : HSp D) (v : Pl D) (Λ Λ' : AddSubgroup (Fin S₀.rank → AE D)), Tame D v → IsSDAt S₀ v Λ → IsSDAt S₀ v Λ' → ∃ γ ∈ grpAt S₀ (· = v), ∀ y : Fin S₀.rank → AE D, (∀ i, y i ∈ idAt D (· = v)) → (y ∈ Λ ↔ mt S₀ γ *ᵥ y ∈ Λ') := by
  first | exact @GlobalTheory.IwaOrbit.selfDual_orbit | exact GlobalTheory.IwaOrbit.selfDual_orbit | (intros; apply GlobalTheory.IwaOrbit.selfDual_orbit <;> assumption)
end
