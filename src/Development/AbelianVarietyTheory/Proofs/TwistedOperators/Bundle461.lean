module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle385
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelConjugateTransfer
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsRealThetaParameterPairThetaPartnerSignedParame
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealThetaIntertwinerAdjointIsRealThetaIntertwine
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealThetaRuleExchangePairMembers
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle386
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1946
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle428
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle429
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle430
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle431
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle404
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift

theorem _root_.GlobalTheory.T.lowerTowerLiftsVanish_of_vanish_on_fock : ∀ (D : D7) (X : ProvA), Inputs D X → LowFock D X → LowAll D X := by
  first | exact @GlobalTheory.PairLift.lowAll_of_lowFock | exact GlobalTheory.PairLift.lowAll_of_lowFock | (intros; apply GlobalTheory.PairLift.lowAll_of_lowFock <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift

theorem _root_.GlobalTheory.T.discrete_series_model_conjugate_transfer : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), ∃ (M₁ : DSModel (sgn false V) fun τ => dualPar (S τ)) (κ : SmT M₁ ≃+ SmT M), ModelTr (starRingEnd ℂ) false θ M₁ M κ := by
  first | exact @GlobalTheory.ConjModelTr.exists_conjModelTr | exact GlobalTheory.ConjModelTr.exists_conjModelTr | (intros; apply GlobalTheory.ConjModelTr.exists_conjModelTr <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift

theorem _root_.GlobalTheory.T.isRealThetaParameterPair_thetaPartnerSignedParameter : ∀ (t : ℕ) (b : Bool) (c c' : ℚ) (P : SPar) (N : ℕ), 1 ≤ t → P.Nonempty → GlobalTheory.SignedHC.IsRegular P → GlobalTheory.SignedHC.InCoset (c + ((t : ℚ) + 1) / 2) (GlobalTheory.SignedHC.entries P) → GlobalTheory.SignedHC.FarFrom c (((t : ℚ) + 1) / 2) P → P.card + t ≤ N → 1800 < N → GapOver P (2 * (N : ℚ) ^ 3) → GapOver (partner t b c c' P) (2 * (N : ℚ) ^ 3) → ThetaPar t P (partner t b c c' P) c c' := by
  first | exact @GlobalTheory.PairLift.FromSigned.thetaPar_partner | exact GlobalTheory.PairLift.FromSigned.thetaPar_partner | (intros; apply GlobalTheory.PairLift.FromSigned.thetaPar_partner <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift

theorem _root_.GlobalTheory.T.realThetaIntertwiner_adjoint_isRealThetaIntertwiner : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (Z P : Type) [AddCommGroup P] [Module ℂ P] (θ : InfFam D) (ω : GA D V × GA D W →* Module.End ℂ (Z → ℂ)) (ω' : GA D W × GA D V →* Module.End ℂ (Z → ℂ)) (pt : P → Z → ℂ) (It : P →ₗ[ℂ] SmT M →ₗ[ℂ] SmT M') (Tp : P → SmT M' →ₗ[ℂ] SmT M), (∀ g h, ω' (h, g) = ω (g, h)) → GlobalTheory.Grid.IsIntw θ M' M ω' pt It → (∀ (p : P) (v : M.Vec) (w : M'.Vec), ellT M' (fun τ => w τ) (inclT M' (It p (PiTensorProduct.tprod ℂ v))) = starRingEnd ℂ (ellT M (fun τ => v τ) (inclT M (Tp p (PiTensorProduct.tprod ℂ w))))) → IsIntwF θ M M' ω pt Tp := by
  first | exact @GlobalTheory.Adopt.realThetaIntertwiner_adjoint_isRealThetaIntertwiner | exact GlobalTheory.Adopt.realThetaIntertwiner_adjoint_isRealThetaIntertwiner | (intros; apply GlobalTheory.Adopt.realThetaIntertwiner_adjoint_isRealThetaIntertwiner <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift

theorem _root_.GlobalTheory.T.realThetaRule_exchange_pair_members : ∀ (X : ProvA) (p q r s : ℕ) (lam : Ix p q → ℚ) (lam' : Ix r s → ℚ), (Formalism.MainNotions.SchurIrreducible.ARiiiUp X lam lam' → Formalism.MainNotions.SchurIrreducible.ARiiiDown X lam' lam) ∧ (Formalism.MainNotions.SchurIrreducible.ARiiiLine X lam lam' → Formalism.MainNotions.SchurIrreducible.ARiiiLine X lam' lam) ∧ (Formalism.MainNotions.SchurIrreducible.ARiv X (r := r) (s := s) lam → NoLow X r s lam) := by
  first | exact @GlobalTheory.SwapRule.swap_rule | exact GlobalTheory.SwapRule.swap_rule | (intros; apply GlobalTheory.SwapRule.swap_rule <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

noncomputable section

namespace GlobalTheory.FlipMatch.SplitSymp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem piW_cA' {σ : E →ₐ[F] E} {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (τ : E →ₐ[F] Fv F v) (w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    piW τ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ w) = piW (τ.comp σ) w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem piW_incl {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (τ : E →ₐ[F] Fv F v) (e : E) :
    piW τ (inclR (F := F) (AF F) e) = τ e := by
  change GlobalTheory.AdelicU.evFin F v 1 * τ e = τ e
  simp

end GlobalTheory.FlipMatch.SplitSymp

namespace GlobalTheory.FlipMatch.SplitSymp

theorem pairM_comm {K : Type} [CommRing K] {n d : ℕ} (P Q : Matrix (Fin n) (Fin d) K) :
    pairM P Q = pairM Q P := by
  simp only [pairM, mul_comm]

theorem pairM_chart {K : Type} [Field K] {n d : ℕ} (A : Matrix (Fin n) (Fin n) K) (B : Matrix (Fin d) (Fin d) K)
    (b : GL (Fin n) K) (c : GL (Fin d) K) (P Q : Matrix (Fin n) (Fin d) K) :
    pairM ((b⁻¹).1 * P * (c⁻¹).1ᵀ) (-(b.1ᵀ * A * Q * Bᵀ * c.1)) =
      -∑ i : Fin n, ∑ j : Fin d, ∑ k : Fin n, ∑ l : Fin d, P i j * A i k * B j l * Q k l := by
  first
  | exact @_root_.GlobalTheory.TracePairingBasisChange.pair_change_basis
  | exact _root_.GlobalTheory.TracePairingBasisChange.pair_change_basis
  | (apply _root_.GlobalTheory.TracePairingBasisChange.pair_change_basis <;> assumption)
  | (intros; apply _root_.GlobalTheory.TracePairingBasisChange.pair_change_basis <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TracePairingBasisChange.pair_change_basis <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TracePairingBasisChange.pair_change_basis ..)

theorem sum_four_swap_pairs_alt {R α β : Type} [AddCommMonoid R] [Fintype α] [Fintype β] (f : α → β → α → β → R) :
    ∑ a, ∑ b, ∑ c, ∑ e, f a b c e = ∑ c, ∑ e, ∑ a, ∑ b, f a b c e := by
  first
  | exact @_root_.GlobalTheory.SumFourSwap.sum_four_swap
  | exact _root_.GlobalTheory.SumFourSwap.sum_four_swap
  | (apply _root_.GlobalTheory.SumFourSwap.sum_four_swap <;> assumption)
  | (intros; apply _root_.GlobalTheory.SumFourSwap.sum_four_swap <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SumFourSwap.sum_four_swap <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SumFourSwap.sum_four_swap ..)

theorem symp_at_split : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}, IsCMExt F E σ →
    ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d), (∀ r s, σ (X.J s r) = X.J r s) → (∀ r s, σ (Y.J s r) = -Y.J r s) → ∀ (ψ : AddChar (AF F) ℂ) {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (t : E →ₐ[F] Fv F v)
    (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)) (x u : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
    At (evFin F v) x → At (evFin F v) u →
    ψ (GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) x u) =
      psiLoc ψ v (pairM (coX t b c x) (coY σ X Y t b c u) - pairM (coY σ X Y t b c x) (coX t b c u)) := by
  intro F E _ _ _ _ _ σ hcm n d X Y hX hY ψ v t b c x u hx hu
  have hss := GlobalTheory.AdelicU.comp_conj_conj hcm t
  have hz : At (evFin F v) ((-1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) *
      GlobalTheory.WeilM.hTens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) x u) := by
    intro r hr
    have h : ∀ i j, r • x i j = 0 := fun i j => by
      have := congrFun (congrFun (hx r hr) i) j
      simpa using this
    rw [← mul_smul_comm]
    unfold GlobalTheory.WeilM.hTens
    simp only [Finset.smul_sum, ← smul_mul_assoc, h, zero_mul, Finset.sum_const_zero, mul_zero]
  unfold GlobalTheory.WeilM.symp
  rw [GlobalTheory.T.adelicTrace_supportedAtSplitPlace hcm v t _ hz]
  change psiLoc ψ v _ = psiLoc ψ v _
  congr 1
  rw [pairM_comm (coY σ X Y t b c x), coX, coX, coY, coY, pairM_chart, pairM_chart]

  simp only [map_mul, map_neg, map_one, neg_one_mul, GlobalTheory.WeilM.hTens, map_sum, piW_cA', piW_incl,
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, Matrix.map_apply, hss, AlgHom.comp_apply, hX, hY]
  rw [sub_eq_add_neg]
  congr 1
  rw [neg_neg]
  refine Eq.trans ?_ (sum_four_swap_pairs_alt _).symm
  simp only [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

end GlobalTheory.FlipMatch.SplitSymp
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

theorem _root_.GlobalTheory.T.integrable_gaussian_exp_linear_norm_term_complex_matrix : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (c : ι → ℝ), (∀ τ, 0 < c τ) → ∀ z₀ : VCx ι a b, Integrable fun z : VCx ι a b => Real.exp ((∑ k : DVar ι a b, ‖(c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2‖ * ‖z k.1 k.2.1 k.2.2‖) - gq c z / 2) := by
  first | exact @GlobalTheory.FockTransl.integrable_exp_lin_sub_gq | exact GlobalTheory.FockTransl.integrable_exp_lin_sub_gq | (intros; apply GlobalTheory.FockTransl.integrable_exp_lin_sub_gq <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

theorem _root_.GlobalTheory.T.fockRealPoint_transport_continuous_integral : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T), Continuous (fockPt σ A B) ∧ (∀ w : WO S T, w.map (finPart D) = 0 → ∃ z, fockPt σ A B z = w) ∧ ∀ g : VCx D.what₂.Tau S.rank T.rank → ℂ, Integrable g → ∃ (m : Measure (WO S T)) (α : WO S T → ℂ), SFinite m ∧ Integrable α m ∧ ∀ H : WO S T → ℂ, ∫ w, α w * H w ∂m = ∫ z, g z * H (fockPt σ A B z) := by
  first | exact @GlobalTheory.FockTransport.fockPt_transport | exact GlobalTheory.FockTransport.fockPt_transport | (intros; apply GlobalTheory.FockTransport.fockPt_transport <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

theorem _root_.GlobalTheory.T.integrable_conjMonomial_bargmann_gaussian : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (c : ι → ℝ), (∀ τ, 0 < c τ) → (∀ m : DVar ι a b →₀ ℕ, Integrable fun z => conjMono m z * (Real.exp (-gq c z / 2) : ℂ)) ∧ ∀ z₀ : VCx ι a b, Integrable fun z => Complex.exp (bk c z₀ z) * (Real.exp (-gq c z / 2) : ℂ) := by
  first | exact @GlobalTheory.FockTransl.integrable_conjMono_bargmann_gauss | exact GlobalTheory.FockTransl.integrable_conjMono_bargmann_gauss | (intros; apply GlobalTheory.FockTransl.integrable_conjMono_bargmann_gauss <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch


theorem _root_.GlobalTheory.T.exists_placeIso_reading_components_characters : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (t : T) (i j : Fin D.R.m) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E), X.α = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j → X.β = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j →
    ∀ {v : Pl D.host.F} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (w : Pl D.host.E), splitPrime τ = w →
    ∃ jj : Fv D.host.F v ≃+* Kw w, IsPlaceIso τ w jj ∧ IsLocIso jj ∧
      (∀ x, chrW X.ν τ x = (locGrid G t w).nu i j (Units.map (jj : Fv D.host.F v →* Kw w) x)) ∧
      ∀ x, psiLoc W.ψ v x = psiAt W w ((xiAt w)⁻¹ * jj x) := by
  first | exact @GlobalTheory.FlipMatch.exists_placeIso_chars | exact GlobalTheory.FlipMatch.exists_placeIso_chars | (intros; apply GlobalTheory.FlipMatch.exists_placeIso_chars <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch


theorem _root_.GlobalTheory.T.exists_partialFourier_columnBlock_schwartzBruhat : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A : Type) [Fintype A] [DecidableEq A] (C : Type) [Fintype C] [DecidableEq C] (ψ : AddChar k Circle) (ϖ : kˣ) (P : Finset C), IsUnif ϖ → HasConductor ψ 1 →
    ∃ 𝓕 : (Matrix A C k → ℂ) →ₗ[ℂ] (Matrix A C k → ℂ), Set.BijOn 𝓕 (GlobalTheory.WeilM.SB (Matrix A C k) : Set _) (GlobalTheory.WeilM.SB (Matrix A C k) : Set _) ∧
      (∀ Ξ ∈ GlobalTheory.WeilM.SB (Matrix A C k), ∀ T R : Matrix A C k, (∀ r, ∀ s ∈ P, T r s = 0) → (∀ r, ∀ s ∉ P, R r s = 0) →
        𝓕 (fun S => (ψ (pairM S R) : ℂ) * Ξ (S + T)) = fun Z => 𝓕 Ξ (Z + (T + R))) ∧
      (∀ Ξ ∈ GlobalTheory.WeilM.SB (Matrix A C k), ∀ T R : Matrix A C k, (∀ r, ∀ s ∉ P, T r s = 0) → (∀ r, ∀ s ∈ P, R r s = 0) →
        𝓕 (fun S => (ψ (pairM S R) : ℂ) * Ξ (S + T)) = fun Z => (ψ (pairM Z R - pairM Z T) : ℂ) * 𝓕 Ξ Z) ∧
      ∀ Ξ ∈ GlobalTheory.WeilM.SB (Matrix A C k), ∀ n, IsNatDatum ϖ n (𝓕 Ξ) → fourierSum ψ⁻¹ ϖ n P (𝓕 Ξ) = Ξ := by
  first | exact @GlobalTheory.ColFourier.exists_blockFourier | exact GlobalTheory.ColFourier.exists_blockFourier | (intros; apply GlobalTheory.ColFourier.exists_blockFourier <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevRestrict

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem map_hatL {m n : ℕ} (M : Matrix (Fin m) (Fin n) E) {Λ : Submodule (𝓞 E) (Fin n → E)}
    {Λ' : Submodule (𝓞 E) (Fin m → E)} (hM : ∀ y ∈ Λ, M *ᵥ y ∈ Λ') :
    ∀ x ∈ Formalism.L2.Herm.hatL (F := F) Λ,
      (M.map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F))) *ᵥ x ∈ Formalism.L2.Herm.hatL (F := F) Λ' := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    refine Submodule.subset_span ⟨M *ᵥ y, hM y hy, ?_⟩
    funext i
    exact RingHom.map_mulVec _ M y i
  | zero => rw [mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mulVec_add]; exact add_mem hx hy
  | smul s x _ hx =>
    have := Submodule.smul_mem _ s hx
    rw [Subring.smul_def, ← mulVec_smul] at this
    rw [Subring.smul_def]
    exact this

theorem map_smul {m n : ℕ} (M : Matrix (Fin m) (Fin n) E) {Λ : Submodule (𝓞 E) (Fin n → E)}
    {Λ' : Submodule (𝓞 E) (Fin m → E)} (hM : ∀ y ∈ Λ, M *ᵥ y ∈ Λ') (𝔪 : Ideal (𝓞 E)) :
    ∀ y ∈ 𝔪 • Λ, M *ᵥ y ∈ 𝔪 • Λ' := by
  have : 𝔪 • Λ ≤ (𝔪 • Λ').comap ((Matrix.mulVecLin M).restrictScalars (𝓞 E)) := by
    rw [Submodule.smul_le]
    intro r hr z hz
    show M *ᵥ (r • z) ∈ 𝔪 • Λ'
    rw [mulVec_smul]
    exact Submodule.smul_mem_smul hr (hM z hz)
  exact fun y hy => this hy

theorem map_hatL_smul {m n : ℕ} (M : Matrix (Fin m) (Fin n) E) {Λ : Submodule (𝓞 E) (Fin n → E)}
    {Λ' : Submodule (𝓞 E) (Fin m → E)} (hM : ∀ y ∈ Λ, M *ᵥ y ∈ Λ') (𝔪 : Ideal (𝓞 E)) :
    ∀ x ∈ Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ),
      (M.map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F))) *ᵥ x ∈ Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ') :=
  map_hatL M (map_smul M hM 𝔪)

end General

open GlobalTheory.UnitaryEmbeddingProperties

variable {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E}

theorem qM_mul_a (d : HermitianOrthogonalExtensionData A B c ε) : qM d * d.a = 0 := by
  rw [qM, Matrix.mul_assoc, d.perp, Matrix.mul_zero]

theorem qM_lat (d : HermitianOrthogonalExtensionData A B c ε) (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E))
    (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : ∀ x ∈ d.lat Λ 𝔟, qM d *ᵥ x ∈ Λ := by
  intro x hx
  obtain ⟨y, hy, u, -, rfl⟩ := hx
  rw [mulVec_add, mulVec_mulVec, mulVec_mulVec, qM_mul, qM_mul_a, one_mulVec, zero_mulVec, add_zero]
  exact hy

theorem frameMat_lat (d : HermitianOrthogonalExtensionData A B c ε) (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E))
    (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : ∀ y ∈ Λ, frameMat B A d.ι *ᵥ y ∈ d.lat Λ 𝔟 :=
  fun y hy => ⟨y, hy, 0, fun p => (𝔟 p).zero_mem, by simp⟩



theorem finE_mem_congLev : ∀ {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
    (𝔪 : Ideal (𝓞 D.host.E)) (h : GA D A), Lev.finE B (stabilizerEmbedding d h) ∈ congLev D.sp.cm B.gram (d.lat Λ 𝔟) 𝔪 →
      Lev.finE A h ∈ congLev D.sp.cm A.gram Λ 𝔪 := by
  intro D A B c ε d Λ 𝔟 𝔪 h hg
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin B.rank) (Fin A.rank) (Lev.EAf D),
      P = (frameMat B A d.ι).map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix (Fin A.rank) (Fin B.rank) (Lev.EAf D),
      Q = (qM d).map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) := ⟨_, rfl⟩
  obtain ⟨g, hgdef⟩ : ∃ g, g = Lev.finE B (stabilizerEmbedding d h) := ⟨_, rfl⟩
  obtain ⟨k, hkdef⟩ : ∃ k, k = Lev.finE A h := ⟨_, rfl⟩
  rw [← hgdef] at hg
  rw [← hkdef]
  have hQP : HMul.hMul Q P = (1 : Matrix (Fin A.rank) (Fin A.rank) (Lev.EAf D)) := by
    rw [hP, hQ]; exact qM_mul_map _ d
  have e : ∀ {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E),
      (M.map (incA D)).map (GlobalTheory.LevSplit.finSw D) =
        M.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) := fun M => by
    ext i j; exact GlobalTheory.LevSplit.finSw_incA _
  have hG : g.1 = ex P Q k.1 := by
    rw [hgdef, hkdef, GlobalTheory.LevSplit.finE_val, GlobalTheory.LevSplit.finE_val, hP, hQ]
    show ((matHom B (stabilizerEmbedding d h)).1).map _ = ex _ _ (((matHom A h).1).map _)
    rw [unitaryEmbedding_matrix_formula, ex_map, e, e]
  have hGP : HMul.hMul g.1 P = HMul.hMul P k.1 := by rw [hG]; exact ex_mul_P P Q hQP _
  have hk : k.1 = HMul.hMul (HMul.hMul Q g.1) P := by
    rw [Matrix.mul_assoc, hGP, ← Matrix.mul_assoc, hQP, Matrix.one_mul]
  have hPl : ∀ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ, P *ᵥ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) (d.lat Λ 𝔟) :=
    by subst hP; exact map_hatL (F := D.host.F) (frameMat B A d.ι) (frameMat_lat d Λ 𝔟)
  have hQl : ∀ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) (d.lat Λ 𝔟), Q *ᵥ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ :=
    by subst hQ; exact map_hatL (F := D.host.F) (qM d) (qM_lat d Λ 𝔟)
  rw [mem_congLev] at hg
  have g2 := hg.2.1
  have g3 := hg.2.2
  rw [mem_congLev]
  refine ⟨?_, fun x => ⟨fun hx => ?_, fun hx => ?_⟩, fun x hx => ?_⟩
  · rw [hkdef]; exact GlobalTheory.LevSplit.finE_mem_UA A h
  · rw [hk, ← mulVec_mulVec, ← mulVec_mulVec]; exact hQl _ ((g2 _).1 (hPl x hx))
  · have h1 := hPl _ hx
    rw [mulVec_mulVec, ← hGP, ← mulVec_mulVec] at h1
    have h2 := hQl _ ((g2 _).2 h1)
    rwa [mulVec_mulVec, hQP, one_mulVec] at h2
  · have e2 : k.1 *ᵥ x - x = Q *ᵥ (g.1 *ᵥ (P *ᵥ x) - P *ᵥ x) := by
      rw [mulVec_sub, mulVec_mulVec, mulVec_mulVec, mulVec_mulVec, hQP, one_mulVec, hk]
    rw [e2, hQ]
    exact map_hatL_smul (F := D.host.F) (qM d) (qM_lat d Λ 𝔟) 𝔪 _ (g3 _ (hPl x hx))

end GlobalTheory.LevRestrict
end
end
