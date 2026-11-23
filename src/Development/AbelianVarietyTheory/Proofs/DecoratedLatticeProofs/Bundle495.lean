module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConjugateAdjointDagger
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle016
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle022
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle020
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle021
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle266
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle322
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle487
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle465
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle117
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle466
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle264
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle488
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle329
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle490
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle024
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle489
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle155
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.thetaTensorRule_targetOrthogonalSum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (T A B : HSp D) (d : OrthDec T A B) (S : HSp D), GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.TensorTarget ψ d S := by
  first | exact @GlobalTheory.TensorTargetRule.tensorTarget | exact GlobalTheory.TensorTargetRule.tensorTarget | (intros; apply GlobalTheory.TensorTargetRule.tensorTarget <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

theorem _root_.GlobalTheory.T.thetaLift_nonvanishing_onString_of_definiteDown : ∀ (D : D7) (_ : DownNe D) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t, NonVan R i t := by
  first | exact @GlobalTheory.Core.Rk.NonVanAt.nonVan_of_downNe | exact GlobalTheory.Core.Rk.NonVanAt.nonVan_of_downNe | (intros; apply GlobalTheory.Core.Rk.NonVanAt.nonVan_of_downNe <;> assumption)
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

theorem _root_.GlobalTheory.T.exists_vacuumVector_principalCongruenceSupport : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A H : HSp D) (χA : (AE D)ˣ →* Circle) (om : WRep A H) (sA : RealMat A) (sH : RealMat H), IsInfFam θ → (∃ η, GlobalTheory.WeilParts.IsEtaTilde D η) → IsWeilDatumO ψ A H χA 1 om → (∀ τ, IsCartanInv (gramAt D A τ) (sA τ)) → (∀ τ, IsCartanInv (gramAt D H τ) (sH τ)) → A.rank ≤ H.rank → ∀ (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D)) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)), Places A β Z → ∃ f, IsThetaFunO ψ A H f ∧ f ≠ 0 ∧ (∀ τ, IsFockVacAt (heisO ψ A H) θ τ (cplxO (sA τ) (sH τ)) f) ∧ IsSphOff ψ A H (frameLat A) (frameLat H) (under Z) f ∧ (∀ κ ∈ prin A β Z, om (κ, 1) f = f) ∧ ∀ ν 𝓕, IsCovolOne (ratL H A) ν 𝓕 → ∀ g ∈ openOff A (frameLat A) (under Z), g ∉ prinInf A β Z → wcoef om ν 𝓕 f f g = 0 := by
  first | exact @GlobalTheory.Core.Rk.Small.exists_small_vac_vec | exact GlobalTheory.Core.Rk.Small.exists_small_vac_vec | (intros; apply GlobalTheory.Core.Rk.Small.exists_small_vac_vec <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.sphericalParameterTransfer_splitPlace : ∀ D : D7, TransferOn D fun v => IsSplit (E := D.host.E) v := by
  first | exact @GlobalTheory.ChainOnto.SplitTransfer.transferOn_isSplit | exact GlobalTheory.ChainOnto.SplitTransfer.transferOn_isSplit | (intros; apply GlobalTheory.ChainOnto.SplitTransfer.transferOn_isSplit <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

namespace GlobalTheory.AdForm.RatApprox

theorem mt_mul' {D : D7} (V : HSp D) (g h : GA D V) :
    Formalism.L2.Theta.mt V (g * h) = Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V h := by
  unfold Formalism.L2.Theta.mt; rw [map_mul]; rfl

theorem actO_actO' {D : D7} (S T : HSp D) (g g' : GA D S) (h h' : GA D T) (x : WO S T) :
    actO S T g h (actO S T g' h' x) = actO S T (g * g') (h * h') x := by
  unfold actO
  rw [_root_.mul_inv_rev, mt_mul', mt_mul']
  simp only [Matrix.mul_assoc]

theorem isHalf_actO' {D : D7} {S T : HSp D} {e : AE D} (g : GA D S) (h : GA D T) {u : WO S T} (hu : IsHalf e u) :
    IsHalf e (actO S T g h u) := by
  intro i j
  simp only [actO, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  conv_rhs => rw [← hu l k]
  ring

end GlobalTheory.AdForm.RatApprox

namespace GlobalTheory.AdForm.RatApprox



theorem approx : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ (k : ℕ), 0 < k → ∀ (κ : A.U i α) (κ' : A.U (i + 1) γ) x y, IsDetRoot _ κ.1 x → IsDetRoot _ κ'.1 y → ∀ (z : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E), ∃ (κ₁ : A.U i α) (κ₁' : A.U (i + 1) γ) (x₁ y₁ : (AE (I.rec7 l Z))ˣ) (t : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))), (∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.host.E, ∀ r s, adAt B.host.F P ((finM _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) κ₁.1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s)) ∧ (∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.host.E, ∀ r s, adAt B.host.F P ((finM _ (rankN (I.rec7 l Z) (i + 1) hi) κ₁'.1 : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s)) ∧ IsDetRoot _ κ₁.1 x₁ ∧ IsDetRoot _ κ₁'.1 y₁ ∧ A.chr (i + 1) x₁ = A.chr (i + 1) x ∧ A.chr (i + 1) y₁ = A.chr (i + 1) y ∧ A.chi i α κ₁ = A.chi i α κ ∧ A.chi (i + 1) γ κ₁' = A.chi (i + 1) γ κ' ∧ t ∈ stdHom _ _ ∧ IsHalf A.e t ∧ actO _ _ κ₁.1⁻¹ κ₁'.1⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r) = actO _ _ κ.1⁻¹ κ'.1⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r) + k • t := by
  intro B X I hI hP l Z u a Ch A hA i hi α γ k hk κ κ' x y hx hy z
  have hi' : i ≤ B.R.m := Nat.le_of_succ_le hi
  obtain ⟨NB, hNB⟩ := GlobalTheory.T.heckeCharacter_eq_at_det_roots_of_congruent (I.rec7 l Z) (A.chr (i + 1)) (hA.chr ⟨i, hi⟩).1
  have hee : A.e * A.e = A.e := GlobalTheory.PlaceDatum.idemSum_mul_self hA.idem
  have hez : IsHalf A.e (z.map fun r => A.e * incA (I.rec7 l Z) r) := fun r s => by
    simp only [Matrix.map_apply, ← mul_assoc, hee]
  have hM := isHalf_actO' κ.1⁻¹ κ'.1⁻¹ hez
  obtain ⟨NC, hNC⟩ := GlobalTheory.T.halfMatrix_move_deepCongruence_bound (I.rec7 l Z) _ _ (rankN (I.rec7 l Z) i hi') (rankN (I.rec7 l Z) (i + 1) hi) A.e _ hM k hk
  have hfin : ∀ j (hj : j ≤ B.R.m) (β : Ch j), GlobalTheory.Mem.Col2.AdT.ChiFin I l Z (A.K j hj β).lev := fun j hj β => by
    obtain ⟨n, hn, h⟩ := hA.fin j hj β
    exact ⟨n, hn, fun κ _ => h κ⟩
  have step : ∀ j (hj : j ≤ B.R.m) (β : Ch j) (g : A.U j β), ∃ w : A.U j β, A.chi j β w = 1 ∧
      (∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) B.host.E, ∀ r s, adAt B.host.F P ((finM _ (rankN (I.rec7 l Z) j hj) (g * w).1 : Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s)) ∧
      ∀ (P : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.E)) (r s : Fin (B.R.N j)), Valued.v (adAt (I.rec7 l Z).host.F P (finM _ (rankN (I.rec7 l Z) j hj) w.1 r s - (1 : Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) (EF (I.rec7 l Z))) r s)) ≤ WithZero.exp (-((max NB NC : ℕ) : ℤ)) := by
    intro j hj β g
    obtain ⟨g₀, hg₀⟩ := ((hA.U j hj β g.1).1 g.2).2
    obtain ⟨zz, hz1, hz2, hz3⟩ := GlobalTheory.T.exists_trivialCharLevel_elt_rational_at_twistPrimes I hI hP l Z a _ j hj _ (A.K j hj β).lev (hfin j hj β) (max NB NC) (show TC.GA B (B.R.N j) from g₀.1)
    obtain ⟨w, hw⟩ := GlobalTheory.T.chartLevel_exists_adelicLevel_trivialReal_lift I hI hP l Z u a Ch A hA j hj β zz
    refine ⟨w, ?_, fun P hPQ => ?_, fun P r s => ?_⟩
    · rw [hA.chi j hj β w zz hw, hz1]
    · obtain ⟨M, hM⟩ := hz2 P hPQ
      refine ⟨M, fun r s => ?_⟩
      rw [← hM r s, Subgroup.coe_mul, GlobalTheory.RepLattice.finM_mul', ← hg₀, ← hw]
      rfl
    · rw [← hw]
      exact hz3 P r s
  obtain ⟨w, hw1, hw2, hw3⟩ := step i hi' α κ
  obtain ⟨w', hw1', hw2', hw3'⟩ := step (i + 1) hi γ κ'
  have hwG : w.1 ∈ GfC _ := ((hA.U i hi' α w.1).1 w.2).1
  have hwG' : w'.1 ∈ GfC _ := ((hA.U (i + 1) hi γ w'.1).1 w'.2).1
  have dB : ∀ {n : ℕ} (f : Matrix (Fin n) (Fin n) (EF (I.rec7 l Z))), (∀ (P : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.E)) (r s : Fin n), Valued.v (adAt (I.rec7 l Z).host.F P (f r s - (1 : Matrix (Fin n) (Fin n) (EF (I.rec7 l Z))) r s)) ≤ WithZero.exp (-((max NB NC : ℕ) : ℤ))) → ∀ N₀ : ℕ, N₀ ≤ max NB NC → ∀ (P : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.E)) (r s : Fin n), Valued.v (adAt (I.rec7 l Z).host.F P (f r s - (1 : Matrix (Fin n) (Fin n) (EF (I.rec7 l Z))) r s)) ≤ WithZero.exp (-(N₀ : ℤ)) := by
    intro n f hf N₀ hN P r s
    exact (hf P r s).trans (WithZero.exp_le_exp.2 (neg_le_neg (Nat.cast_le.2 hN)))
  obtain ⟨x₁, hx₁, hcx⟩ := hNB _ (rankN (I.rec7 l Z) i hi') κ.1 w.1 hwG (dB _ hw3 NB (le_max_left _ _)) x hx
  obtain ⟨y₁, hy₁, hcy⟩ := hNB _ (rankN (I.rec7 l Z) (i + 1) hi) κ'.1 w'.1 hwG' (dB _ hw3' NB (le_max_left _ _)) y hy
  obtain ⟨t, ht, hth, hte⟩ := hNC w.1 w'.1 hwG hwG' (dB _ hw3 NC (le_max_right _ _)) (dB _ hw3' NC (le_max_right _ _))
  refine ⟨κ * w, κ' * w', x₁, y₁, t, hw2, hw2', hx₁, hy₁, hcx, hcy, ?_, ?_, ht, hth, ?_⟩
  · rw [map_mul, hw1, mul_one]
  · rw [map_mul, hw1', mul_one]
  · rw [← hte, actO_actO']
    simp only [Subgroup.coe_mul, _root_.mul_inv_rev]

end GlobalTheory.AdForm.RatApprox
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)

theorem _root_.GlobalTheory.T.twistedChain_step_constants_tuple_indep : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D → RealZetaQ D → Restore D → ∀ h : RangeX R, RChain R h → RMeas R → RVol R → RNrm R → RUnif R h := by
  first | exact @GlobalTheory.ChainTw.UnifFree.rUnif_of | exact GlobalTheory.ChainTw.UnifFree.rUnif_of | (intros; apply GlobalTheory.ChainTw.UnifFree.rUnif_of <;> assumption)
end

section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.weylElement_acts_on_schrodinger_by_fourier : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ μ : D.host.E, IsSkew μ → ∀ w : GA D (dblSp A), IsWeyl A w → mt (dblSp A) w ⬝ (dblDec A).jX = -(incA D μ • (dblDec A).jY) → mt (dblSp A) w ⬝ (dblDec A).jY = incA D μ⁻¹ • (dblDec A).jX → ∀ f, IsThetaFunO ψ (dblSp A) B f → ∀ x, sch ψ A B ν 𝓨 (omh (w, 1) f) x = ∫ y, sch ψ A B ν 𝓨 f y * ψ (trA (incA D (-D.host.xi0 / μ) * Matrix.trace (GlobalTheory.StdUnn.inner B x y))) ∂ν := by
  first | exact @GlobalTheory.StdUnn.WeylFourier.sch_weyl | exact GlobalTheory.StdUnn.WeylFourier.sch_weyl | (intros; apply GlobalTheory.StdUnn.WeylFourier.sch_weyl <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.AdForm.twLev_prime : GlobalTheory.AdForm.TwLev' := by
  intro B X I hOk hPins l Z u a Ch A hA k _ _ _ _ ι p β Q L hS J hJ hJall j hj b
  refine ⟨fun i g hg => ⟨GlobalTheory.T.standardPair_stabiliser_mem_chartLevel I hOk hPins l Z u a Ch A hA k ι p β Q L hS j hj b i g hg,
    GlobalTheory.T.chartCharacter_trivial_on_standardPairStabilizer I hOk hPins l Z u a Ch A hA k ι p β Q L hS j hj b i g hg _⟩, fun κ hκ => ?_⟩
  obtain ⟨g, hg1, κ', hκ', heq⟩ := GlobalTheory.T.unitaryAdelicPoint_eq_prod_splitComponents_mul_off (I.rec7 l Z) ((I.rec7 l Z).sp.X j) k ι p _ (β j)
    (GlobalTheory.T.splitPoints_lie_over_distinct_places I hOk hPins l Z u p β Q L hS) J hJ hJall κ
  exact ⟨g, fun i => GlobalTheory.T.chartLevel_component_fixes_standardPair I hOk hPins l Z u a Ch A hA k ι p β Q L hS j hj b κ hκ i (g i) (hg1 i), κ', hκ', heq⟩
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl GlobalTheory.SeeSaw ValuativeRel IsLocalRing
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.definiteLift_comm_levelPrimeOperators : ∀ (D : D7) (c : Comm D) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom c) (o : TDat c k ι) (t : Tup c) (w : VTup t), LiftExact D → c.Is → t.Is → v.Is → VForm v w → ShapeOff v o → (∀ j, j < D.R.m → ∃ μ, IsWeilDatumO c.ψ _ _ μ μ (t.kom j) ∧ ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D μ (o.p i).v) → LiftS o t := by
  first | exact @GlobalTheory.SeeSaw.liftS_of_exact | exact GlobalTheory.SeeSaw.liftS_of_exact | (intros; apply GlobalTheory.SeeSaw.liftS_of_exact <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.seeSaw_unfoldedSupport_fixedLevelPlaces : ∀ (D : D7) (c : Comm D) (v : VCom c) (n : ℕ) (G : Fin n → GLoc v), c.Is → v.Is → GPin G → GlobalTheory.LocMod.GSupp1 D → GlobalTheory.LocMod.GSupp2 D → FlatLaw D → ∀ t : Tup c, t.Is → (∀ i, (G i).Chars t) → GSupp (t := t) v := by
  first | exact @GlobalTheory.SeeSaw.GSuppAsm.gsupp_of_local | exact GlobalTheory.SeeSaw.GSuppAsm.gsupp_of_local | (intros; apply GlobalTheory.SeeSaw.GSuppAsm.gsupp_of_local <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section


namespace GlobalTheory.LineDual

variable {D : D7}

theorem intAt_zero' (P : Pl D → Prop) : (0 : AE D) ∈ intAt D P :=
  ⟨zero_mem _, by rw [RingHom.map_zero]; exact zero_mem _⟩

theorem intAt_add' {P : Pl D → Prop} {a b : AE D} (ha : a ∈ intAt D P) (hb : b ∈ intAt D P) : a + b ∈ intAt D P :=
  ⟨add_mem ha.1 hb.1, by rw [RingHom.map_add (f := _)]; exact add_mem ha.2 hb.2⟩

theorem intAt_neg' {P : Pl D → Prop} {a : AE D} (ha : a ∈ intAt D P) : -a ∈ intAt D P :=
  ⟨neg_mem ha.1, by rw [RingHom.map_neg]; exact neg_mem ha.2⟩

theorem latV_entry_mem_idAt {S : HSp D} {M : Lat S} {P : Pl D → Prop} {y : Fin S.rank → AE D}
    (hy : y ∈ latV S M P) (i : Fin S.rank) : y i ∈ idAt D P := by
  induction hy using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, -, hα, a, -, x, -, rfl⟩ := hw
    exact LatMem.tmul_mem_idAt hα _
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | neg x _ hx => exact neg_mem hx

theorem idV_mem_idAt {𝔞 : FI D} {v : Pl D} {t : AE D} (ht : t ∈ idV 𝔞 v) : t ∈ idAt D (· = v) := by
  induction ht using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, -, hα, a, -, rfl⟩ := hw
    exact LatMem.tmul_mem_idAt (fun w hw => hα w hw) _
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | neg x _ hx => exact neg_mem hx

theorem cA_mem_idAt {v : Pl D} {a : AE D} (h : a ∈ idAt D (· = v)) : cA D a ∈ idAt D (· = v) := by
  rw [GlobalTheory.FinPl.Model.mem_idAt_iff] at h ⊢
  rw [← Algebra.smul_def] at h ⊢
  conv_rhs => rw [← h]
  rw [GlobalTheory.HeisDisj.cA_smul]

def pr (S : HSp D) (w y : Fin S.rank → AE D) : AE D := ∑ l, (∑ m, cA D (w m) * gA S m l) * y l

theorem pr_zero_left (S : HSp D) (y : Fin S.rank → AE D) : pr S 0 y = 0 := by simp [pr]
theorem pr_zero_right (S : HSp D) (w : Fin S.rank → AE D) : pr S w 0 = 0 := by simp [pr]
theorem pr_add_left (S : HSp D) (w w' y : Fin S.rank → AE D) : pr S (w + w') y = pr S w y + pr S w' y := by
  simp [pr, add_mul, Finset.sum_add_distrib]
theorem pr_add_right (S : HSp D) (w y y' : Fin S.rank → AE D) : pr S w (y + y') = pr S w y + pr S w y' := by
  simp [pr, mul_add, Finset.sum_add_distrib]
theorem pr_neg_left (S : HSp D) (w y : Fin S.rank → AE D) : pr S (-w) y = -pr S w y := by
  simp [pr]
theorem pr_neg_right (S : HSp D) (w y : Fin S.rank → AE D) : pr S w (-y) = -pr S w y := by
  simp [pr]

theorem pr_gen (S : HSp D) (α β : Af D.host.F) (x x' : Fin S.rank → D.host.E) :
    pr S (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x i)) (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x' i)) =
      pairA D.host.F 0 (α * β) ⊗ₜ[D.host.F] (∑ m, ∑ l, star (x m) * S.gram m l * x' l) := by
  have hc : ∀ m, cA D (pairA D.host.F 0 α ⊗ₜ[D.host.F] x m) = pairA D.host.F 0 α ⊗ₜ[D.host.F] star (x m) :=
    fun _ => rfl
  have hg : ∀ m l, gA S m l = (1 : AF D.host.F) ⊗ₜ[D.host.F] S.gram m l := fun _ _ => rfl
  have hp : pairA D.host.F 0 α * pairA D.host.F 0 β = pairA D.host.F 0 (α * β) := Prod.ext (zero_mul _) rfl
  simp only [pr, one_mul]
  simp only [hc, hg, Finset.sum_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hp]
  rw [Finset.sum_comm]
  simp only [← TensorProduct.tmul_sum]

theorem pr_mem_intAt {S : HSp D} {M : Lat S} (hM : IsSelfDualC S M) {P : Pl D → Prop} {w y : Fin S.rank → AE D}
    (hw : w ∈ latV S M P) (hy : y ∈ latV S M P) : pr S w y ∈ intAt D P := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hαi, hα, a, ha, x, hx, rfl⟩ := hw
    rw [Set.mem_singleton_iff] at ha
    subst ha
    induction hy using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨β, hβi, hβ, c, hc, x', hx', rfl⟩ := hz
      rw [Set.mem_singleton_iff] at hc
      subst hc
      rw [pr_gen]
      obtain ⟨b, hb⟩ := (hM.2 x').1 hx' x hx
      refine ⟨LatMem.tmul_mem_idAt (fun v hv => by rw [map_mul, hα v hv, zero_mul]) _, ?_⟩
      rw [← hb]
      exact AddSubgroup.subset_closure ⟨α * β, LatMem.intAf_mul' hαi hβi, b, rfl⟩
    | zero => rw [pr_zero_right]; exact intAt_zero' _
    | add z z' _ _ hz hz' => rw [pr_add_right]; exact intAt_add' hz hz'
    | neg z _ hz => rw [pr_neg_right]; exact intAt_neg' hz
  | zero => rw [pr_zero_left]; exact intAt_zero' _
  | add w w' _ _ hw hw' => rw [pr_add_left]; exact intAt_add' hw hw'
  | neg w _ hw => rw [pr_neg_left]; exact intAt_neg' hw

theorem line_pair_mem_idV : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S A L : HSp D) (o : OrthDec S A L)
    (ζ : Fin L.rank → D.host.E) (M : Lat S) (𝔠 : FI D) (v : Pl D), IsSelfDualC S M → LineId o ζ M 𝔠 v → 𝔠 ≠ 0 →
      ∀ y ∈ latV S M (· = v), cA D (∑ l, (∑ m, cA D (ratV (vecB o ζ) m) * gA S m l) * y l) ∈ idV 𝔠⁻¹ v := by
  intro D ψ hψ S A L o ζ M 𝔠 v hM hline h𝔠 y hy
  obtain ⟨h1, h2, -, h4, -⟩ := GlobalTheory.SeeSaw.idV_props D ψ hψ v
  have hX : (∑ l, (∑ m, cA D (ratV (vecB o ζ) m) * gA S m l) * y l) ∈ idAt D (· = v) :=
    sum_mem fun l _ => Ideal.mul_mem_left _ _ (latV_entry_mem_idAt hy l)
  have hcX := cA_mem_idAt hX
  have hcint : ∀ s, s ∈ intAt D (· = v) → cA D s ∈ intAt D (· = v) := by
    intro s hs
    have e2 : s ∈ idV (D.host.AA ^ (0 : ℤ)) v := by rw [zpow_zero]; exact (h1 s).2 hs
    have e3 := (h4 0 s).1 e2
    rw [zpow_zero] at e3
    exact (h1 _).1 e3
  have key := (h2 𝔠 1 h𝔠 one_ne_zero _ hcX).1 (fun t ht => ?_)
  · rwa [one_mul] at key
  · have htI : t ∈ idAt D (· = v) := idV_mem_idAt ht
    have htz : t • ratV (vecB o ζ) ∈ latV S M (· = v) := (hline t htI).2 ht
    have hp := pr_mem_intAt hM htz hy
    have he : pr S (t • ratV (vecB o ζ)) y = cA D t * ∑ l, (∑ m, cA D (ratV (vecB o ζ) m) * gA S m l) * y l := by
      simp only [pr, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [he] at hp
    have h5 := hcint _ hp
    rw [map_mul, Formalism.L2.Theta.cA_cA, mul_comm] at h5
    exact (h1 _).2 h5

end GlobalTheory.LineDual

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.fractionalIdealCompletion_properties_at_place : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ v : Pl D, (∀ a, a ∈ idV (1 : FI D) v ↔ a ∈ intAt D (· = v)) ∧ (∀ 𝔞 𝔟 : FI D, 𝔞 ≠ 0 → 𝔟 ≠ 0 → ∀ s ∈ idAt D (· = v), (∀ a ∈ idV 𝔞 v, s * a ∈ idV 𝔟 v) ↔ s ∈ idV (𝔟 * 𝔞⁻¹) v) ∧ (∀ (𝔞 : FI D) (x : D.host.E), x ≠ 0 → ∀ s, s ∈ idV (FractionalIdeal.spanSingleton _ x * 𝔞) v ↔ incA D x⁻¹ * s ∈ idV 𝔞 v ∧ s ∈ idAt D (· = v)) ∧ (∀ n : ℤ, ∀ s, s ∈ idV (D.host.AA ^ n) v ↔ cA D s ∈ idV (D.host.AAbar ^ n) v) ∧ (∀ s ∈ idAt D (· = v), s ∈ idV (dI D) v ↔ ∀ o ∈ intAt D (· = v), psiE ψ (s * o) = 1) ∧ (∀ 𝔞 : FI D, 𝔞 ≠ 0 → ∃ g ∈ idV 𝔞 v, ∃ g' ∈ idAt D (· = v), (∀ s ∈ idAt D (· = v), g' * g * s = s) ∧ ∀ s, s ∈ idV 𝔞 v ↔ s ∈ idAt D (· = v) ∧ g' * s ∈ intAt D (· = v)) ∧ ∀ (S : HSp D) (L : Lat S) (y : Fin S.rank → AE D), y ∈ latA S L (· = v) ↔ (∀ i, y i ∈ idAt D (· = v)) ∧ ∀ s ∈ idV D.host.AA⁻¹ v, s • y ∈ latV S L (· = v) := by
  first | exact @GlobalTheory.SeeSaw.idV_props | exact GlobalTheory.SeeSaw.idV_props | (intros; apply GlobalTheory.SeeSaw.idV_props <;> assumption)
end
