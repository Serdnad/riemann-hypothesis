module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle711
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefinitePeriodDependsOnProductFunction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle732

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle692
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1780
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1899
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2527
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1904
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2735
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2233
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle599
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle035
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle518
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle611
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProductFunctionTotalTensorInvariantLastArrows
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockRed

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem opPow_smul {ι X : Type} (A : ι → (X → ℂ) → X → ℂ) (hA : ∀ i (c : ℂ) g, A i (c • g) = c • A i g)
    (k : ι →₀ ℕ) (c : ℂ) (f : X → ℂ) : opPow A k (c • f) = c • opPow A k f := by
  unfold opPow
  induction (Finsupp.toMultiset k).toList with
  | nil => rfl
  | cons i l ih => simp only [List.foldr_cons, ih, hA]

theorem pureTensorL_smul {ι X : Type} (A : ι → (X → ℂ) → X → ℂ) (hA : ∀ i (c : ℂ) g, A i (c • g) = c • A i g)
    (c : ℂ) (f : X → ℂ) : pureTensorL A (c • f) = c • pureTensorL A f := by
  refine (MvPolynomial.basisMonomials ι ℂ).ext fun k => ?_
  simp only [pureTensorL, Module.Basis.constr_basis, LinearMap.smul_apply, opPow_smul A hA]

theorem dRho_smul {m n : ℕ} (hs : Mx D m n → (Mx D m n → ℂ) → Mx D m n → ℂ)
    (hhs : ∀ w (c : ℂ) g, hs w (c • g) = c • hs w g) (θ : InfFam D) (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ)
    (c : ℂ) (g : Mx D m n → ℂ) : Datum.dRho hs θ τ z (c • g) = c • Datum.dRho hs θ τ z g := by
  funext x
  simp only [Datum.dRho, hhs, Pi.smul_apply, smul_eq_mul]
  exact deriv_const_mul_field c

theorem aPlusAll_smul {m n : ℕ} (hs : Mx D m n → (Mx D m n → ℂ) → Mx D m n → ℂ)
    (hhs : ∀ w (c : ℂ) g, hs w (c • g) = c • hs w g) (θ : InfFam D) J B B' (k : FVar D m n) (c : ℂ) (g : Mx D m n → ℂ) :
    aPlusAll hs θ J B B' k (c • g) = c • aPlusAll hs θ J B B' k g := by
  simp only [aPlusAll, aPlus, crea, dRho_smul hs hhs, smul_comm _ c, smul_sub]

theorem fock_smul (W : G.Weil) (p : Pair T) (c : ℂ) (f : WO (G.pS p) (G.pT p) → ℂ) (Q : PolF D (G.pT p).rank (G.pS p).rank) :
    W.fock p (c • f) Q = c • W.fock p f Q := by
  have hh : ∀ w (c : ℂ) g, heisO W.ψ (G.pS p) (G.pT p) w (c • g) = c • heisO W.ψ (G.pS p) (G.pT p) w g := by
    intro w c g; funext x; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring
  simp only [GridData.Weil.fock, pureTensorO]
  rw [pureTensorL_smul _ (fun i c g => aPlusAll_smul _ hh _ _ _ _ i c g)]
  rfl

end GlobalTheory.FockRed

namespace GlobalTheory.FockRed

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem liftA_smul_left (W : G.Weil) (M : Vol G) (a : Arrow T) (f : Sch G a) (c : ℂ) (F : Fn G a.src) :
    liftA W M a f (c • F) = c • liftA W M a f F := by
  funext g
  simp only [liftA, Formalism.IndefR.Lift.liftInt, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext h; ring

theorem liftA_smul_right (W : G.Weil) (M : Vol G) (a : Arrow T) (ha : ∀ i, a ≠ .coreUp i) (c : ℂ) (f : Sch G a)
    (F : Fn G a.src) : liftA W M a (c • f) F = c • liftA W M a f F := by
  funext g
  simp only [liftA, Formalism.IndefR.Lift.liftInt, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext h
  cases a with
  | coreUp i => exact absurd rfl (ha i)
  | _ => simp only [GridData.Weil.kerA, GridData.Weil.ker, thetaKO, map_smul, LinearMap.smul_apply, Module.End.smul_def, Pi.smul_apply, smul_eq_mul]; ring

theorem pathLift_column_smul_univ (W : G.Weil) (M : Vol G) (t : T) : ∀ (n : ℕ) (s : Fin n → ℂ) (g : ∀ j : Fin n, Sch G (.col t j))
    (φ : Fn G (.top 0)), liftP W M (colPath t n) (colFam t n fun j => s j • g j) φ =
      (∏ j, s j) • liftP W M (colPath t n) (colFam t n g) φ
  | 0, s, g, φ => by simp [colPath, liftP]
  | n + 1, s, g, φ => by
    show liftA W M (.col t n) (s (Fin.last n) • g (Fin.last n))
        (liftP W M (colPath t n) (colFam t n fun j => s j.castSucc • g j.castSucc) φ) =
      (∏ j, s j) • liftA W M (.col t n) (g (Fin.last n)) (liftP W M (colPath t n) (colFam t n fun j => g j.castSucc) φ)
    rw [pathLift_column_smul_univ W M t n (fun j => s j.castSucc) (fun j => g j.castSucc) φ, liftA_smul_left,
      liftA_smul_right W M _ (fun i h => by cases h), Fin.prod_univ_castSucc, smul_smul, mul_comm]

theorem pathLift_row_smul_univ (W : G.Weil) (M : Vol G) (m : ℕ) : ∀ (n : ℕ) (s : Fin n → ℂ) (g : ∀ i : Fin n, Sch G (.right i m))
    (F : Fn G (.grid 0 m)), liftP W M (rowPath T m n) (rowFam m n fun i => s i • g i) F =
      (∏ i, s i) • liftP W M (rowPath T m n) (rowFam m n g) F
  | 0, s, g, F => by simp [rowPath, liftP]
  | n + 1, s, g, F => by
    show liftA W M (.right n m) (s (Fin.last n) • g (Fin.last n))
        (liftP W M (rowPath T m n) (rowFam m n fun i => s i.castSucc • g i.castSucc) F) =
      (∏ i, s i) • liftA W M (.right n m) (g (Fin.last n)) (liftP W M (rowPath T m n) (rowFam m n fun i => g i.castSucc) F)
    rw [pathLift_row_smul_univ W M m n (fun i => s i.castSucc) (fun i => g i.castSucc) F, liftA_smul_left,
      liftA_smul_right W M _ (fun i h => by cases h), Fin.prod_univ_castSucc, smul_smul, mul_comm]

end GlobalTheory.FockRed

namespace GlobalTheory.FockRed

theorem defPer_of_smul {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) (t : T) (M : Vol G) (Q : PolCol G) (P : PolRow G) (d : PureDat G t) (φ : Fn G (.top 0))
    (F : Fn G (.grid 0 D.R.m)) (s s' : Fin D.R.m → ℂ) (g : ∀ j : Fin D.R.m, WO (G.V (.top j)) (G.V (.top (j + 1))) → ℂ)
    (f : SchRow G) (h1 : ∀ j : Fin D.R.m, movedVec t S (d.1 j) = s j • g j) (h2 : ∀ i : Fin D.R.m, movedVec t S (d.2 i) = s' i • f i) :
    defPer t S M (Q, P) d φ F = ((∏ j, s j) * ∏ i, s' i) * ∫ h in M.fd (.grid D.R.m D.R.m),
      liftP W M (colPath t D.R.m) (colFam t D.R.m fun j => W.fock (.top t j) (g j) (Q j)) φ (stabilizerEmbedding G.sp.topDec h) *
        liftP W M (rowPath T D.R.m D.R.m) (rowFam D.R.m D.R.m fun i => W.fock (.chi i D.R.m) (f i) (P i)) F h
        ∂M.ν (.grid D.R.m D.R.m) := by
  have e1 : (fun j : Fin D.R.m => (W.fock (.top t j) (movedVec t S (d.1 j)) (Q j) : Sch G (.col t j))) =
      fun j : Fin D.R.m => s j • (W.fock (.top t j) (g j) (Q j) : Sch G (.col t j)) := funext fun j => by
    rw [h1 j]; exact fock_smul W (.top t j) _ _ _
  have e2 : (fun i : Fin D.R.m => (W.fock (.chi i D.R.m) (movedVec t S (d.2 i)) (P i) : Sch G (.right i D.R.m))) =
      fun i : Fin D.R.m => s' i • (W.fock (.chi i D.R.m) (f i) (P i) : Sch G (.right i D.R.m)) := funext fun i => by
    rw [h2 i]; exact fock_smul W (.chi i D.R.m) _ _ _
  have e3 := (congrArg (fun x => liftP W M (colPath t D.R.m) (colFam t D.R.m x) φ) e1).trans
    (pathLift_column_smul_univ W M t D.R.m s (fun j => W.fock (.top t j) (g j) (Q j)) φ)
  have e4 := (congrArg (fun x => liftP W M (rowPath T D.R.m D.R.m) (rowFam D.R.m D.R.m x) F) e2).trans
    (pathLift_row_smul_univ W M D.R.m D.R.m s' (fun i => W.fock (.chi i D.R.m) (f i) (P i)) F)
  unfold defPer
  rw [← integral_const_mul]
  congr 1
  funext h
  have e5 := congrFun e3 (stabilizerEmbedding G.sp.topDec h)
  have e6 := congrFun e4 h
  simp only [Pi.smul_apply, smul_eq_mul] at e5 e6
  refine (congrArg₂ (· * ·) e5 e6).trans ?_
  ring

section
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}



theorem fockAt_of_steps (ch : Choice R) (hB : BasicAt ch) (hMv : MovedAt ch) (hCF : ColFock ch)
    (hL : ∀ (t : T) (M : Vol ch.G), IsHaarDef M → ∀ (f : SchRow ch.G), (∀ i, IsThetaFunO ch.W.ψ _ _ (f i)) →
      ∀ (P : PolRow ch.G) (y : (R.HX t).H), GlobalTheory.Unf.IsContAut _ (liftP ch.W M (rowPath T D.R.m D.R.m)
        (rowFam D.R.m D.R.m fun i => ch.W.fock (.chi i D.R.m) (f i) (P i)) (formTop ch t y))) : FockAt ch := by
  classical
  obtain ⟨_, _, _, _, _, hBgood', _⟩ := hB
  obtain ⟨v, hv, κ, κ', z, hz, hmv⟩ := hMv
  refine ⟨fun t => ∏ j : Fin D.R.m, z t j, fun t => Subgroup.prod_mem _ fun j _ => hz t j, ?_⟩
  intro C hC P
  obtain ⟨σc, hσc⟩ := hCF v hv C hC
  obtain ⟨K, hK⟩ : ∃ K : ℂ, K = (∏ j : Fin D.R.m, ((κ j : ℂˣ) : ℂ))⁻¹ * (∏ i : Fin D.R.m, ((κ' i : ℂˣ) : ℂ))⁻¹ := ⟨_, rfl⟩
  refine ⟨K • σc.mapDomain (fun Q => (Q, P)), ?_⟩
  intro t a β M hM hS τ c hτ hc y
  obtain ⟨Z, hZ⟩ : ∃ Z : ℂ, Z = ∏ j : Fin D.R.m, ((z t j : ℂˣ) : ℂ) := ⟨_, rfl⟩
  have hone : Z⁻¹ * K * ((∏ j : Fin D.R.m, ((κ j * z t j : ℂˣ) : ℂ)) * ∏ i : Fin D.R.m, ((κ' i : ℂˣ) : ℂ)) = 1 := by
    have n1 : (∏ j : Fin D.R.m, ((κ j : ℂˣ) : ℂ)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => (κ j).ne_zero
    have n2 : (∏ j : Fin D.R.m, ((κ' j : ℂˣ) : ℂ)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => (κ' j).ne_zero
    have n3 : (∏ j : Fin D.R.m, ((z t j : ℂˣ) : ℂ)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => (z t j).ne_zero
    simp only [Units.val_mul, Finset.prod_mul_distrib]
    rw [hK, hZ]
    field_simp
  have key : ∀ d ∈ τ.support, per ch.W M t (combC ch.W (c d) C) (combR ch.rm (c d)) P (colFn ch a) (formTop ch t y) =
      σc.sum fun Q x => x * (Z⁻¹ * K * defPer t ch.S.toGridChoice M (Q, P) d (colFn ch a) (formTop ch t y)) := by
    intro d hd
    obtain ⟨h1, h2⟩ := hmv t a β τ c hS hτ hc d hd
    have hfin : ∀ j, j < D.R.m → IsFinComb ((c d).1 j) := fun j hj => ((hc d hd).1 ⟨j, hj⟩).1
    have hth := (hBgood' C hC (c d) hfin).2
    refine (hσc t M hM a (c d) hfin _ (hL t M hM (combR ch.rm (c d)) hth P y)).trans ?_
    refine Finset.sum_congr rfl fun Q _ => ?_
    dsimp only
    rw [defPer_of_smul ch.S.toGridChoice t M Q P d (colFn ch a) (formTop ch t y) (fun j => ((κ j * z t j : ℂˣ) : ℂ))
      (fun i => ((κ' i : ℂˣ) : ℂ)) (fun j => comb ch.W.ψ _ _ ((c d).1 j) (v j)) (combR ch.rm (c d)) h1 h2,
      ← mul_assoc (Z⁻¹ * K), hone, one_mul]
  rw [defTot_smul, Units.coe_prod, ← hZ]
  unfold defTot
  rw [Finsupp.sum_mapDomain_index_inj (fun Q Q' h => (Prod.ext_iff.1 h).1), Finsupp.sum_comm]
  simp only [Finsupp.sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [key d hd, Finsupp.sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun Q _ => ?_
  ring

end

theorem fockAt_big : Big fun ch => FockAt ch := by
  obtain ⟨a0, ha⟩ := Big.and (Big.and GlobalTheory.T.lastRow_unfolding_basicHypotheses GlobalTheory.T.movedVectorsAreCombinationsOfVacua_of_large_depth) GlobalTheory.T.columnRealDatum_fockCombination_largeDepth
  refine ⟨a0, fun ε CF hC => ?_⟩
  obtain ⟨x, hx⟩ := ha ε CF hC
  refine ⟨x, fun D large₂ he hxx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch hsc => ?_⟩
  obtain ⟨⟨hB, hMv⟩, hCF⟩ := hx D large₂ he hxx Γ Pl0 T A Ks R F s ch hch hsc
  refine fockAt_of_steps ch hB hMv hCF fun t M hM f hf P y => ?_
  have hN : ∀ X, DefNode D.R.m X → X ≠ .top D.R.m → GlobalTheory.RowTens.Nice M X := fun X hX hX' => by
    refine ⟨?_, hM X hX hX'⟩
    rcases X with ⟨i, j⟩ | i | j
    all_goals first
      | exact hX.elim
      | exact GlobalTheory.DefConv.posDef_of_node ch.G s.core.lev hX rfl
      | (obtain ⟨h1, rfl⟩ := hX
         exact GlobalTheory.DefConv.posDef_of_node ch.G s.core.lev ⟨h1, le_rfl⟩ (by simp [Node.neg]))
  have := GlobalTheory.RowTens.row_invCont ch.W hN (hB.2.1 t y) D.R.m le_rfl _
    fun k : Fin D.R.m => GlobalTheory.RowTens.fock_theta ch.W _ (hf k) (P k)
  exact ⟨this.2, this.1⟩

end GlobalTheory.FockRed
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.RouteSeesaw GlobalTheory.ChainFr
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num)

namespace GlobalTheory.SquareTripleForm

variable {D : D7}

theorem hasSignature_add {n : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} {a b : ℕ} (h : Formalism.UG.HasSignature J a b) :
    a + b = n := by
  obtain ⟨e, -⟩ := h
  simpa using (Fintype.card_congr e).symm

theorem isTriple_of_standing : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (t : T) (i j : Fin D.R.m),
    SquareStanding G t → ∀ M : Vol G, M.Is t →
      GlobalTheory.SquareComm.IsTriple (G.V (.grid (↑i + 1) (↑j + 1))) (G.V (.grid ↑i ↑j)) (GlobalTheory.Doubling.hsum (G.V (.grid ↑i (↑j + 1))) (G.V (.grid (↑i + 1) ↑j))) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) := by
  intro D T L sc G μ₀ hL W t i j hS M hM
  obtain ⟨e, Bs, Γ, X, om, om', hX, hY, -⟩ := GlobalTheory.T.squareThetaTripleHypotheses_of_standing hL W t i j hS M hM
  have hi := i.2
  have hj := j.2
  have nv : ∀ a b, a ≤ D.R.m → b ≤ D.R.m → (G.node (.grid a b)).IsV (rankV D a b) ((D.R.m - b) / 2) :=
    fun a b ha hb => node_isV G hL (X := .grid a b) ⟨ha, hb⟩
  have rW : (G.V (.grid (↑i + 1) (↑j + 1))).rank = rankV D (↑i + 1) (↑j + 1) := (nv _ _ (by omega) (by omega)).rank
  have rW₁ : (G.V (.grid ↑i ↑j)).rank = rankV D ↑i ↑j := (nv _ _ (by omega) (by omega)).rank
  have rV : (G.V (.grid ↑i (↑j + 1))).rank = rankV D ↑i (↑j + 1) := (nv _ _ (by omega) (by omega)).rank
  have rV₁ : (G.V (.grid (↑i + 1) ↑j)).rank = rankV D (↑i + 1) ↑j := (nv _ _ (by omega) (by omega)).rank
  have hrank : (GlobalTheory.Doubling.hsum (G.V (.grid ↑i (↑j + 1))) (G.V (.grid (↑i + 1) ↑j))).rank =
      (G.V (.grid (↑i + 1) (↑j + 1))).rank + (G.V (.grid ↑i ↑j)).rank := by
    show (G.V (.grid ↑i (↑j + 1))).rank + (G.V (.grid (↑i + 1) ↑j)).rank = _
    rw [rW, rW₁, rV, rV₁]; simp only [rankV]; ring
  obtain ⟨hχ, hχ0⟩ := GlobalTheory.SquareChars.chi_hecke_res G hL i
  have hμ := GlobalTheory.HeckeCharacterRestriction.isHecke_mu hL t j
  have hμ0 := GlobalTheory.HeckeCharacterRestriction.resEta_mu hL t j
  have hη := GlobalTheory.SquareChars.isHeckeChar_pow' hL.eta.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps G i j)
  have hη1 := GlobalTheory.SquareChars.resEta_pow' (GlobalTheory.HeckeCharacterRestriction.resEta_eta hL) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps G i j)
  obtain ⟨p1, p2⟩ := GlobalTheory.SquareChars.rank_parity G hL i j
  refine ⟨GlobalTheory.SquareChars.isHeckeChar_mul' hμ hη, GlobalTheory.SquareChars.isHeckeChar_mul' hχ hη,
    resEta_parity (resEta_mul hμ0 hη1) (by rw [zero_add]; exact p2),
    resEta_parity (resEta_mul hχ0 hη1) (by rw [zero_add]; exact p1), hrank, ?_, ?_, ?_, ?_⟩
  · rw [hrank]; exact hY.geo.even
  · have sgn : ∀ a b (ha : a ≤ D.R.m) (hb : b ≤ D.R.m) τ, Formalism.UG.HasSignature (gramAt D (G.V (.grid a b)) τ)
        ((G.V (.grid a b)).rank - (D.R.m - b) / 2) ((D.R.m - b) / 2) := by
      intro a b ha hb τ
      have s := (nv a b ha hb).sigOK (tauE D τ)
      rw [(nv a b ha hb).sig, ← (nv a b ha hb).rank] at s
      exact s
    have sgnN : ∀ a b (ha : a ≤ D.R.m) (hb : b ≤ D.R.m) τ, Formalism.UG.HasSignature (gramAt D (negSp (G.V (.grid a b))) τ)
        ((D.R.m - b) / 2) ((G.V (.grid a b)).rank - (D.R.m - b) / 2) := by
      intro a b ha hb τ
      have s := GlobalTheory.GridWeil.sigOK_neg (nv a b ha hb).sigOK (tauE D τ)
      have e : (negSp (G.V (.grid a b))).sig (tauE D τ) = ((G.V (.grid a b)).sig (tauE D τ)).swap := rfl
      rw [e, (nv a b ha hb).sig, ← (nv a b ha hb).rank] at s
      exact s
    obtain ⟨w⟩ : Nonempty (InfinitePlace D.host.F) := inferInstance
    obtain ⟨τ₀, hτ₀, -⟩ := hX.cart w
    have tW : Formalism.UG.HasSignature (gramAt D (G.V (.grid (↑i + 1) (↑j + 1))) τ₀)
        ((G.V (.grid (↑i + 1) (↑j + 1))).rank - Γ.p) Γ.p := by
      refine GlobalTheory.FunObj.hasSignature_of_hasSig_conj ?_
      have hs := hY.geo.hV.sig w
      rw [hX.JW, one_smul] at hs
      have hmap : (G.V (.grid (↑i + 1) (↑j + 1))).gram.map (Bs.emb w).1 = (gramAt D _ τ₀).map (starRingEnd ℂ) := by
        ext a b; simp [gramAt, hτ₀]
      rw [hmap] at hs
      exact hs
    have tW₁ : Formalism.UG.HasSignature (gramAt D (negSp (G.V (.grid ↑i ↑j))) τ₀) Γ.q
        ((G.V (.grid ↑i ↑j)).rank - Γ.q) := by
      refine GlobalTheory.FunObj.hasSignature_of_hasSig_conj ?_
      have hs := hY.geo.hV'.sig w
      rw [hX.JW₁] at hs
      have hmap : ((-1 : D.host.E) • (G.V (.grid ↑i ↑j)).gram).map (Bs.emb w).1 =
          (gramAt D (negSp (G.V (.grid ↑i ↑j))) τ₀).map (starRingEnd ℂ) := by
        ext a b; simp [gramAt, hτ₀, HSpace.gram]
      rw [hmap] at hs
      exact hs
    have hp : Γ.p = (D.R.m - (↑j + 1)) / 2 := by
      have r1 := sgn (↑i + 1) (↑j + 1) (by omega) (by omega) τ₀
      have c1 := hasSignature_add r1
      have c2 := hasSignature_add tW
      have u := GlobalTheory.T.hasSignature_fst_unique_sylvester tW r1
      omega
    have hq : Γ.q = (D.R.m - ↑j) / 2 := GlobalTheory.T.hasSignature_fst_unique_sylvester tW₁ (sgnN ↑i ↑j (by omega) (by omega) τ₀)
    have h1 := hY.geo.eBig
    have h2 := hY.geo.aBig
    have h3 := hY.geo.lt
    dsimp only [spW, spW₁] at h1 h2 h3
    refine ⟨(D.R.m - (↑j + 1)) / 2, (D.R.m - ↑j) / 2, fun τ => ⟨sgn _ _ (by omega) (by omega) τ,
      sgn _ _ (by omega) (by omega) τ, ?_⟩, by rw [← hp, ← hq]; omega, by rw [← hp, ← hq]; exact h2⟩
    have sV := sgn ↑i (↑j + 1) (by omega) (by omega) τ
    have sV₁ := sgn (↑i + 1) ↑j (by omega) (by omega) τ
    have cV := hasSignature_add sV
    have cV₁ := hasSignature_add sV₁
    have s := GlobalTheory.Doubling.sigOK_hsum (nv ↑i (↑j + 1) (by omega) (by omega)).sigOK
      (nv (↑i + 1) ↑j (by omega) (by omega)).sigOK (tauE D τ)
    have e : (GlobalTheory.Doubling.hsum (G.V (.grid ↑i (↑j + 1))) (G.V (.grid (↑i + 1) ↑j))).sig (tauE D τ) =
        (G.V (.grid ↑i (↑j + 1))).sig (tauE D τ) + (G.V (.grid (↑i + 1) ↑j)).sig (tauE D τ) := rfl
    rw [e, (nv ↑i (↑j + 1) (by omega) (by omega)).sig, (nv (↑i + 1) ↑j (by omega) (by omega)).sig] at s
    simp only [Prod.fst_add, Prod.snd_add] at s
    have e3 : (GlobalTheory.Doubling.hsum (G.V (.grid ↑i (↑j + 1))) (G.V (.grid (↑i + 1) ↑j))).rank -
        ((D.R.m - (↑j + 1)) / 2 + (D.R.m - ↑j) / 2) =
        rankV D ↑i (↑j + 1) - (D.R.m - (↑j + 1)) / 2 + (rankV D (↑i + 1) ↑j - (D.R.m - ↑j) / 2) := by
      show (G.V (.grid ↑i (↑j + 1))).rank + (G.V (.grid (↑i + 1) ↑j)).rank - _ = _
      omega
    rw [e3]
    exact s
  · intro τ
    refine ⟨_, _, GlobalTheory.SquareExps.alpha_exp (G := G) hL t ↑i ↑j j.2 τ, GlobalTheory.SquareExps.beta_exp (G := G) hL ↑i ↑j i.2 τ, ?_⟩
    have key := GlobalTheory.T.chiGridVertexRank_add_lt_two_exponent_add_centre sc.cGap τ ↑i ↑j i.2 j.2
    rw [hrank, rW, rW₁]
    push_cast at key ⊢
    linarith
  · exact GlobalTheory.T.squareTriple_finitePlaces_of_orientedRoutes hL W t i j hS M hM e Bs Γ X om om' hX hY

end GlobalTheory.SquareTripleForm
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.productFunction_totalTensor_invariant_lastArrows : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ →
    (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) →
    ∀ k : FinPt G (.grid D.R.m D.R.m), finG (G.V (.grid D.R.m D.R.m)) k ∈ S.levRow t D.R.m le_rfl →
    ∀ (w : ∀ j : Fin D.R.m, WO (G.pS (.top t j)) (G.pT (.top t j)))
      (v : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
    (τ.sum fun d a => a *
      (∏ j, Function.update (fun j => S.Z.vec (d.1 j)) (lastIx D)
        (colShift S t (finEmb G.sp.topDec k) (S.Z.vec (d.1 (lastIx D)))) j (w j)) *
      ∏ i, Function.update (fun i => S.Z.vec (d.2 i)) (lastIx D) (rowShift S k (S.Z.vec (d.2 (lastIx D)))) i (v i)) =
    τ.sum fun d a => a * (∏ j, S.Z.vec (d.1 j) (w j)) * ∏ i, S.Z.vec (d.2 i) (v i) := by
  first | exact @GlobalTheory.LastVertexTensor.productFn_invariant | exact GlobalTheory.LastVertexTensor.productFn_invariant | (intros; apply GlobalTheory.LastVertexTensor.productFn_invariant <;> assumption)
end
