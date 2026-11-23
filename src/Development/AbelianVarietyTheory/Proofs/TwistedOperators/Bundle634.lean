module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle429
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PureTensorOZeroEqJetP
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle520
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle006
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsRealFnNeZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle288
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle617
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactPairRealAverageFockEqJetOperator
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle611
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle626
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle524
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle539
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumFockOfThetaSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmVacuumEqSplitFacSmulSum
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle009
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSplit
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle010
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StabOrd

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

noncomputable section

namespace GlobalTheory.FockTransl.Jet

open Complex

variable {D : D7}

theorem list_prod_toMultiset {ι : Type} (m : ι →₀ ℕ) (g : ι → ℂ) :
    ((Finsupp.toMultiset m).toList.map g).prod = m.prod fun l n => g l ^ n := by
  rw [Multiset.prod_map_toList]
  induction m using Finsupp.induction with
  | zero => simp
  | single_add a n g' ha hn ih =>
    rw [map_add (f := _), Multiset.map_add (f := _), Multiset.prod_add, ih, Finsupp.toMultiset_single, Finsupp.prod_add_index']
    · simp [Multiset.map_nsmul, Multiset.prod_nsmul]
    · simp
    · intro a b c; rw [pow_add]

theorem crOp_const_mul {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (l : DVar D.what₂.Tau S.rank T.rank)
    (c : ℂ) (Φ : VCx D.what₂.Tau S.rank T.rank → ℂ) (z : VCx D.what₂.Tau S.rank T.rank) (hΦ : DifferentiableAt ℝ Φ z) :
    crOp A B l (fun z => c * Φ z) z = c * crOp A B l Φ z := by
  unfold crOp
  rw [fderiv_const_mul hΦ]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem jet_eq_fock : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), IsStdChar D ψ (-1) → GlobalTheory.FockCompare.Chart θ σ → ∀ (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T), ∃ C : (FVar D T.rank S.rank →₀ ℕ) → ℂ, ∀ f : WO S T → ℂ, GlobalTheory.ChainFr.IsVacF ψ θ A B f → ∀ (x : WO S T) (m : FVar D T.rank S.rank →₀ ℕ), derivAt0 (rd ψ σ A B f x) m = C m * GlobalTheory.ChainFr.ptF ψ θ A B f (MvPolynomial.monomial m 1) x := by
  intro D ψ θ σ hψ hσ S T A B
  have L1 : ∀ (D : D7) (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (l : DVar D.what₂.Tau S.rank T.rank), (∀ a b, GlobalTheory.FockTransl.Jet.lamF A B l (a + b) = GlobalTheory.FockTransl.Jet.lamF A B l a + GlobalTheory.FockTransl.Jet.lamF A B l b) ∧ ∀ (t : ℂ) a, GlobalTheory.FockTransl.Jet.lamF A B l (t • a) = conj t * GlobalTheory.FockTransl.Jet.lamF A B l a := GlobalTheory.T.fockCreationOperatorMultiplier_antilinear
  have L2 : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), IsStdChar D ψ (-1) → GlobalTheory.FockCompare.Chart θ σ → ∀ (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (h : WO S T → ℂ) (x : WO S T) (l : FVar D T.rank S.rank) (z : VCx D.what₂.Tau S.rank T.rank), DifferentiableAt ℝ (rd ψ σ A B h x) z → rd ψ σ A B (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb l h) x z = (2 / (fockScale D l.1 : ℂ)) * GlobalTheory.FockTransl.Jet.crOp A B l (rd ψ σ A B h x) z := GlobalTheory.T.fock_creation_operator_reading
  refine ⟨fun m => m.prod fun l n => ((fockScale D l.1 : ℂ) / 2) ^ n, fun f hf x m => ?_⟩
  set Aop := aPlusAll (heisO ψ S T) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb with hAop
  have hent : Differentiable ℂ (rd ψ σ A B f x) := GlobalTheory.T.fockGaussianReading_differentiable D ψ θ σ hψ hσ S T A B f hf x
  have hops := GlobalTheory.Ker.CreOp.foldr_creation_zero _ _ Formalism.L2.Ker.coordX (GlobalTheory.FockTransl.Jet.lamF A B) (rd ψ σ A B f x)
    (fun l => L1 D S T A B l) hent (GlobalTheory.FockTransl.Jet.crOp A B) (fun _ _ _ => rfl)
  have key : ∀ L : List (FVar D T.rank S.rank), rd ψ σ A B (L.foldr (fun i g => Aop i g) f) x =
      fun z => (L.map fun l => 2 / (fockScale D l.1 : ℂ)).prod * L.foldr (GlobalTheory.FockTransl.Jet.crOp A B) (rd ψ σ A B f x) z := by
    intro L
    induction L with
    | nil => funext z; simp
    | cons l L ih =>
      funext z
      have hd0 : Differentiable ℝ (L.foldr (GlobalTheory.FockTransl.Jet.crOp A B) (rd ψ σ A B f x)) :=
        (hops L).1.differentiable (by simp)
      have hd : DifferentiableAt ℝ (rd ψ σ A B (L.foldr (fun i g => Aop i g) f) x) z := by
        rw [ih]; exact ((hd0.const_mul _) z)
      rw [List.foldr_cons, L2 D ψ θ σ hψ hσ S T A B _ x l z hd, ih, GlobalTheory.FockTransl.Jet.crOp_const_mul A B l _ _ z (hd0 z),
        List.foldr_cons, List.map_cons, List.prod_cons]
      ring
  have h0 : ∀ h : WO S T → ℂ, rd ψ σ A B h x 0 = h x := by
    intro h
    have hz : fockPt σ A B (0 : VCx D.what₂.Tau S.rank T.rank) = 0 := by
      have e : (fun τ => fockMat A B τ ((0 : VCx D.what₂.Tau S.rank T.rank) τ)) = 0 := by
        funext τ; simp [fockMat]
      rw [fockPt, e]; exact (FockCompare.iotaW σ T S).map_zero
    simp [rd, gq, hz, GlobalTheory.OrientedHeis.heisO_zero]
  have hfs : ∀ l : FVar D T.rank S.rank, (fockScale D l.1 : ℂ) ≠ 0 := fun l => GlobalTheory.VacuumFockLaws.fockScale_ne l.1
  have hval : opPow Aop m f x = (m.prod fun l n => (2 / (fockScale D l.1 : ℂ)) ^ n) * derivAt0 (rd ψ σ A B f x) m := by
    rw [opPow, ← h0 (List.foldr _ f _), key]
    beta_reduce
    rw [(hops _).2, derivAt0, GlobalTheory.AdForm.JetRead.iter_cast _ _ _ (Multiset.length_toList _) Formalism.L2.Ker.coordX,
      list_prod_toMultiset]
  have hpt : GlobalTheory.ChainFr.ptF ψ θ A B f (MvPolynomial.monomial m 1) x = opPow Aop m f x := by
    have e : MvPolynomial.basisMonomials (FVar D T.rank S.rank) ℂ m = MvPolynomial.monomial m 1 := by
      rw [MvPolynomial.coe_basisMonomials]
    rw [GlobalTheory.ChainFr.ptF, pureTensorO, pureTensorL, ← e, Module.Basis.constr_basis]
  rw [hpt, hval, ← mul_assoc, ← Finsupp.prod_mul]
  have e1 : (m.prod fun l n => ((fockScale D l.1 : ℂ) / 2) ^ n * (2 / (fockScale D l.1 : ℂ)) ^ n) = 1 := by
    refine Finset.prod_eq_one fun l _ => ?_
    beta_reduce
    rw [← mul_pow, div_mul_div_comm, mul_comm (fockScale D l.1 : ℂ) 2, div_self (mul_ne_zero two_ne_zero (hfs l)), one_pow]
  rw [e1, one_mul]

end GlobalTheory.FockTransl.Jet

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel)
open scoped ComplexOrder Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RowTest

theorem realPts_ontoUni_haar_unique : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {μ0 : T}, L.Is μ0 → ∀ (j : ℕ), j ≤ D.R.m →
    GlobalTheory.KJInf.OntoUni (fun (k : GinfC (G.V (.top j))) τ =>
      ((realIn W.θ S.N.fr (.top j) (k : GA D (G.V (.top j))) τ : GL (Fin (G.V (.top j)).rank) ℂ) :
        Matrix (Fin (G.V (.top j)).rank) (Fin (G.V (.top j)).rank) ℂ)) ∧
    ∀ κ κ' : Measure (GinfC (G.V (.top j))), κ.IsHaarMeasure → IsProbabilityMeasure κ → κ'.IsHaarMeasure →
      IsProbabilityMeasure κ' → κ = κ' := by
  intro D T L sc G W U S μ0 _ j hj
  have hX : DefNode D.R.m (Node.top j) := hj
  have hO := GlobalTheory.SeeSaw.ontoUni_inB D W.θ (G.V (.top j)) (S.N.frC _) W.θ_is (GlobalTheory.RealType.frC_on S.N hX)
  refine ⟨?_, ?_⟩
  · have e : (fun (k : GinfC (G.V (.top j))) τ =>
        ((realIn W.θ S.N.fr (.top j) (k : GA D (G.V (.top j))) τ : GL (Fin (G.V (.top j)).rank) ℂ) :
          Matrix (Fin (G.V (.top j)).rank) (Fin (G.V (.top j)).rank) ℂ)) =
        fun k : GinfC (G.V (.top j)) => GlobalTheory.SeeSaw.inB W.θ (G.V (.top j)) (S.N.frC (.top j)) k.1 :=
      funext fun k => funext fun τ => GlobalTheory.RowHoweAvg.realIn_coe W.θ S.N _ _ τ
    rw [e]
    exact hO
  · intro κ κ' h1 h2 h3 h4
    haveI : LocallyCompactSpace (GinfC (G.V (.top j))) :=
      (GlobalTheory.AdelicSplit.isClosed_GinfC' _).locallyCompactSpace
    exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure κ κ'

end GlobalTheory.RowTest
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel)
open GlobalTheory.FockReal MvPolynomial
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.compactPair_realAverage_fock_eq_jetOperator : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {μ0 : T},
    L.Is μ0 → ∀ (i : ℕ), i < D.R.m →
    ∀ (a b : D.what₂.Tau → ℚ), (∀ τ, HasInfExp D (G.chrS (.chi i D.R.m : Pair T)) τ (a τ)) → (∀ τ, HasInfExp D (G.chrT (.chi i D.R.m : Pair T)) τ (b τ)) →
    ∀ (e₁ e₂ : D.what₂.Tau → ℤ), (∀ τ, (e₁ τ : ℚ) = a τ + sgnP (.chi i D.R.m : Pair T) * (G.pS (.chi i D.R.m : Pair T)).rank / 2) →
      (∀ τ, (e₂ τ : ℚ) = -(b τ + sgnP (.chi i D.R.m : Pair T) * (G.pT (.chi i D.R.m : Pair T)).rank / 2)) →
    ∀ (Q : PolF D (G.pT (.chi i D.R.m : Pair T)).rank (G.pS (.chi i D.R.m : Pair T)).rank) (Λ : Module.Dual ℂ (VV ℂ (wt G (.grid i D.R.m)))),
    ∃ Λ' : Module.Dual ℂ (VV ℂ (wt G (.grid (i + 1) D.R.m))),
      ∀ (ℓ : PolF D (G.pT (.chi i D.R.m : Pair T)).rank (G.pS (.chi i D.R.m : Pair T)).rank →ₗ[ℂ] ℂ) (κ : Measure (GinfC (G.V (.grid i D.R.m)))), κ.IsHaarMeasure → IsProbabilityMeasure κ →
        ∀ (k' : GA D (G.V (.grid (i + 1) D.R.m))), k' ∈ GinfC (G.V (.grid (i + 1) D.R.m)) →
        ∀ v : VV ℂ (wt G (.grid i D.R.m)),
          ∫ k, realChar W (.chi i D.R.m) e₁ e₂ (k : GA D (G.V (.grid i D.R.m))) k' *
              ℓ (realSubst W S.N.frC (.chi i D.R.m) (k : GA D (G.V (.grid i D.R.m))) k' Q) *
              Λ (realAct W.θ S.N.fr (.grid i D.R.m) ((k : GA D (G.V (.grid i D.R.m)))⁻¹) v) ∂κ =
            Λ' (realAct W.θ S.N.fr (.grid (i + 1) D.R.m) k'⁻¹
              (Formalism.L2.Ker.jetOp (wt G (.grid i D.R.m)) (wt G (.grid (i + 1) D.R.m))
                (fun m => ℓ (MvPolynomial.monomial (m.mapDomain (fvar G (.chi i D.R.m : Pair T))) 1)) (nuEnd G (.chi i D.R.m : Pair T)) v)) := by
  first | exact @GlobalTheory.RowHoweAvg.real_average_jet | exact GlobalTheory.RowHoweAvg.real_average_jet | (intros; apply GlobalTheory.RowHoweAvg.real_average_jet <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.exists_multilinear_columnRowKernelPairing : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) (t : T) (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (Ψ₀ : VV ℂ (wt G (.top 0))) (F₀ : VV ℂ (listedWt G (.grid 0 D.R.m))),
    ∃ M : MultilinearMap (RingHom.id ℂ) (fun j : Fin D.R.m => thSub W (.top t j))
        (MultilinearMap (RingHom.id ℂ) (fun i : Fin D.R.m => thSub W (.chi i D.R.m : Pair T)) ℂ),
      ∀ fs gs, M fs gs = (brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m))).compl₁₂
        (colMapV S (fun j => (fs j : WO (G.pS (.top t j)) (G.pT (.top t j)) → ℂ)) x)
        (rowMapV S (fun i => (gs i : WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ)) y) Ψ₀ F₀ := by
  intro D T L sc G W U S t x y Ψ₀ F₀
  have chain {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)] :
      ∀ (m : ℕ) (A : Fin m → Type) [∀ j, AddCommGroup (A j)] [∀ j, Module ℂ (A j)]
        (k : ∀ j : Fin m, A j →ₗ[ℂ] (V j →ₗ[ℂ] V (j + 1))),
        ∃ M : MultilinearMap (RingHom.id ℂ) A (V 0 →ₗ[ℂ] V m), ∀ fs,
          M fs = chainTo (fun j => if h : j < m then k ⟨j, h⟩ (fs ⟨j, h⟩) else 0) m := by
    intro m
    induction m with
    | zero =>
      intro A _ _ k
      exact ⟨MultilinearMap.constOfIsEmpty (RingHom.id ℂ) A LinearMap.id, fun _ => rfl⟩
    | succ m ih =>
      intro A _ _ k
      obtain ⟨M, hM⟩ := ih (fun j => A j.castSucc) (fun j => k j.castSucc)
      let kl : A (Fin.last m) →ₗ[ℂ] (V m →ₗ[ℂ] V (m + 1)) := k (Fin.last m)
      refine ⟨MultilinearMap.uncurryRight
        (((LinearMap.llcomp ℂ (V 0) (V m) (V (m + 1)) ∘ₗ kl).flip).compMultilinearMap M),
        fun fs => ?_⟩
      show kl (fs (Fin.last m)) ∘ₗ M (Fin.init fs) = _ ∘ₗ chainTo _ m
      rw [hM]
      beta_reduce
      rw [dite_eq_left (Nat.lt_succ_self m)]
      congr 1
      refine GlobalTheory.ArrowMultilinear.chainTo_congr m fun j hj => ?_
      rw [dite_eq_left hj, dite_eq_left (Nat.lt_succ_of_lt hj)]
      rfl
  obtain ⟨Mc, hc⟩ := chain (V := fun j => VV ℂ (wt G (.top j))) D.R.m
    (fun j : Fin D.R.m => thSub W (.top t j))
    (fun j => S.Z.scal 1 (.top t j) •
      GlobalTheory.ArrowMultilinear.fockLin W S.N.frC (.top t j)
        (x j * S.N.u _) (x (j + 1) * S.N.u _))
  obtain ⟨Mr, hr⟩ := chain (V := fun i => VV ℂ (wt G (.grid i D.R.m))) D.R.m
    (fun i : Fin D.R.m => thSub W (.chi i D.R.m : Pair T))
    (fun i => S.Z.scal 1 (.chi i D.R.m : Pair T) •
      GlobalTheory.ArrowMultilinear.fockLin W S.N.frC (.chi i D.R.m : Pair T)
        (y i * S.N.u _) (y (i + 1) * S.N.u _))
  let col := (LinearMap.applyₗ (R := ℂ) (rhoVr (tauE D) _ (S.N.fr (.top 0))⁻¹ Ψ₀)).compMultilinearMap Mc
  let row := (LinearMap.applyₗ (R := ℂ)
    (rhoVr (tauE D) _ (S.N.fr (.grid 0 D.R.m))⁻¹ (funOf (listedWt G (.grid 0 D.R.m)) F₀))).compMultilinearMap Mr
  have hcol (fs : ∀ j : Fin D.R.m, thSub W (.top t j)) :
      col fs = colMapV S (t := t) (fun j => (fs j : WO _ _ → ℂ)) x Ψ₀ := by
    show Mc fs _ = _
    rw [hc]
    refine LinearMap.congr_fun (GlobalTheory.ArrowMultilinear.chainTo_congr
      (V := fun j => VV ℂ (wt G (.top j))) D.R.m fun j hj => ?_) _
    exact dite_congr rfl (fun _ => rfl) (fun _ => rfl)
  have hrow (gs : ∀ i : Fin D.R.m, thSub W (.chi i D.R.m : Pair T)) :
      row gs = rowMapV S (fun i => (gs i : WO _ _ → ℂ)) y F₀ := by
    show Mr gs _ = _
    rw [hr]
    refine LinearMap.congr_fun (GlobalTheory.ArrowMultilinear.chainTo_congr
      (V := fun i => VV ℂ (wt G (.grid i D.R.m))) D.R.m fun j hj => ?_) _
    exact dite_congr rfl (fun _ => rfl) (fun _ => rfl)
  let β := brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m))
  let pairWithRow : VV ℂ (wt G (.top D.R.m)) →ₗ[ℂ]
      MultilinearMap (RingHom.id ℂ) (fun i : Fin D.R.m => thSub W (.chi i D.R.m : Pair T)) ℂ :=
    { toFun := fun v => (β v).compMultilinearMap row
      map_add' := fun v v' => by
        ext gs
        change β (v + v') (row gs) = β v (row gs) + β v' (row gs)
        simp only [map_add]
        rfl
      map_smul' := fun c v => by
        ext gs
        change β (c • v) (row gs) = c • β v (row gs)
        simp only [map_smul]
        rfl }
  refine ⟨pairWithRow.compMultilinearMap col, fun fs gs => ?_⟩
  show β (col fs) (row gs) = _
  rw [hcol, hrow]
  rfl
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv GlobalTheory.LastVertexMove

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.StdHalfLat

variable {D : D7}

theorem idemSum_mul_eq_zero {P P' : Finset (Pl D.host.E)} {e e' : AE D} (he : IsIdemSum e P) (he' : IsIdemSum e' P')
    (hPP : ∀ w ∈ P, ∀ w' ∈ P', w ≠ w' ∧ ¬ Formalism.IndefR.Lev.IsConjPl (D := D) w w') : e * (e' + cA D e') = 0 := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  obtain ⟨⟨es', hes', rfl⟩, -⟩ := he'

  rw [map_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_eq_zero fun w' hw' => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_eq_zero fun w hw => ?_
  obtain ⟨h1, h2⟩ := hPP w hw w' hw'
  rw [mul_add, Formalism.IndefR.Fin.idem_orth (Formalism.IndefR.Fin.idemAt_split (hes w hw)) (hes w hw) (hes' w' hw') h1,
    Formalism.IndefR.Fin.idem_orth_conj (Formalism.IndefR.Fin.idemAt_split (hes w hw)) (hes w hw) (hes' w' hw') h2, add_zero]

theorem ne_and_not_conj {S : Finset ℕ} {w w' : Pl D.host.E} (hw : ¬ Off S w) (hw' : Off S w') :
    w ≠ w' ∧ ¬ Formalism.IndefR.Lev.IsConjPl (D := D) w w' := by
  unfold Off at hw hw'
  push_neg at hw
  obtain ⟨q, hq, hqw⟩ := hw
  refine ⟨fun h => hw' q hq (h ▸ hqw), fun h => ?_⟩
  obtain ⟨c', hc', hc'eq⟩ := h _ hqw
  apply hw' q hq
  have : c' = (q : 𝓞 D.host.E) := by
    apply RingOfIntegers.ext
    rw [hc'eq]
    simp
  rwa [this] at hc'

theorem actO_eq_self_of_half {S T : HSp D} {e a b : AE D} (ha : e * (a + cA D a) = 0) (hb : e * (b + cA D b) = 0)
    {g : GA D S} {h : GA D T} (hg : SuppAt a S g) (hh : SuppAt b T h) {x : WO S T} (hx : IsHalf e x) :
    actO S T g h x = x := by
  have hx' : ∀ c : AE D, e * c = 0 → (1 - c) • x = x := fun c hc => by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [← hx i j, ← mul_assoc, sub_mul, one_mul, mul_comm c e, hc, sub_zero]
  unfold actO
  have k1 : HMul.hMul (mt T h) (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) = (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) := by
    conv_lhs => rw [← hx' _ hb]
    rw [Matrix.mul_smul, ← Matrix.smul_mul, GlobalTheory.SplitScalar.off_smul_mt hh, Matrix.smul_mul, Matrix.one_mul, hx' _ hb]
  rw [k1]
  conv_lhs => rw [← hx' _ ha]
  rw [Matrix.smul_mul, ← Matrix.mul_smul, GlobalTheory.SplitScalar.off_smul_mt_inv hg, Matrix.mul_smul, Matrix.mul_one, hx' _ ha]

theorem suppAt_inv' {a : AE D} {V : HSp D} {g : GA D V} (hg : SuppAt a V g) : SuppAt a V g⁻¹ := by
  have h := GlobalTheory.SplitScalar.off_smul_mt_inv hg
  rw [← sub_eq_zero, ← smul_sub, sub_smul, one_smul, sub_eq_zero] at h
  exact fun i j => (congrFun (congrFun h i) j).symm

end GlobalTheory.StdHalfLat

namespace GlobalTheory.StdHalfLat

open Matrix




variable {D : D7}

theorem actO_mem_latO_of_hat {S T : HSp D} (g : GA D S) (h : GA D T)
    {ΛS ΛS' : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT ΛT' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : ∀ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛS,
      (mt S g).map (toEAf D) *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛS')
    (hT : ∀ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛT,
      (mt T h).map (toEAf D) *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛT')
    {u : WO S T} (hu : u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) :
    actO S T g h u ∈ latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True := by
  induction hu using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hu
    have e := GlobalTheory.AdelicLatMove.rankOne_pure S T a s t 1 α
    rw [mul_one] at e
    rw [← e, GlobalTheory.AdelicLatMove.actO_rankOne]
    exact GlobalTheory.AdelicLatMove.rankOne_mem_latO S T ΛS' ΛT' a ha _
      (hS _ (GlobalTheory.AdelicLatMove.pure_mem_hatL ΛS 1 (one_mem _) s hs)) _
      (hT _ (GlobalTheory.AdelicLatMove.pure_mem_hatL ΛT α hα t ht))
  | zero => simp only [actO, Matrix.mul_zero, Matrix.zero_mul]; exact zero_mem _
  | add y z _ _ hy hz => simp only [actO, Matrix.mul_add, Matrix.add_mul] at hy hz ⊢; exact add_mem hy hz
  | neg y _ hy => simp only [actO, Matrix.mul_neg, Matrix.neg_mul] at hy ⊢; exact neg_mem hy

theorem mem_latO_iff_of_half {S T : HSp D} (g : GA D S) (h : GA D T)
    {ΛS ΛS' : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT ΛT' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : ∀ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛS,
      (mt S g).map (toEAf D) *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛS')
    (hS' : ∀ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛS',
      (mt S g⁻¹).map (toEAf D) *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛS)
    (hT : ∀ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛT,
      (mt T h).map (toEAf D) *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛT')
    (hT' : ∀ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛT',
      (mt T h⁻¹).map (toEAf D) *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛT)
    {e a b : AE D} (ha : e * (a + cA D a) = 0) (hb : e * (b + cA D b) = 0) (hg : SuppAt a S g) (hh : SuppAt b T h)
    {x : WO S T} (hx : IsHalf e x) :
    x ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔
      x ∈ latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True := by
  constructor
  · intro hm
    have := actO_mem_latO_of_hat g h hS hT hm
    rwa [actO_eq_self_of_half ha hb hg hh hx] at this
  · intro hm
    have := actO_mem_latO_of_hat g⁻¹ h⁻¹ hS' hT' hm
    rwa [actO_eq_self_of_half ha hb (suppAt_inv' hg) (suppAt_inv' hh) hx] at this

theorem half_nsmul {m n : ℕ} {e : AE D} {x : Mx D m n} (hx : IsHalf e x) (k : ℕ) : IsHalf e (k • x) := fun i j => by
  have h := hx i j
  simp only [Matrix.smul_apply, nsmul_eq_mul]
  linear_combination (k : AE D) * h

end GlobalTheory.StdHalfLat

namespace GlobalTheory.StdHalfLat

open Matrix




theorem hat_moves {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {U : Set T} (N : Std G U)
    {X : Node} (hX : DefNode D.R.m X) :
    (∀ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (N.fr X)),
      (mt (G.V X) (N.u X).1).map (toEAf D) *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ X)) ∧
    ∀ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ X),
      (mt (G.V X) (N.u X).1⁻¹).map (toEAf D) *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (N.fr X)) := by
  refine ⟨fun v hv => (N.u_lat X hX v).1 hv, fun v hv => (N.u_lat X hX _).2 ?_⟩
  have e : (Formalism.IndefR.Lev.finE (G.V X) (N.u X).1).1 *ᵥ ((mt (G.V X) (N.u X).1⁻¹).map (toEAf D) *ᵥ v) = v := by
    rw [show (mt (G.V X) (N.u X).1⁻¹).map (toEAf D) = (Formalism.IndefR.Lev.finE (G.V X) (N.u X).1⁻¹).1 from rfl,
      Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.one_mulVec]
  rw [e]
  exact hv

theorem exists_kill {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {U : Set T} (N : Std G U)
    {t : T} (ht : t ∈ U) {p : Pair T} (d : FinDatum G t p) {X : Node} (hX : DefNode D.R.m X) :
    ∃ a : AE D, d.e * (a + cA D a) = 0 ∧ SuppAt a (G.V X) (N.u X).1 := by
  obtain ⟨P', e', he', hsupp, hoff⟩ := N.u_supp X hX
  refine ⟨e', idemSum_mul_eq_zero d.e_is he' fun w hw w' hw' => ne_and_not_conj ?_ (hoff w' hw'), hsupp⟩
  intro hw0
  have h3 := N.off w hw0
  rcases d.P_over w hw with h | ⟨w'', hw'', h⟩
  · exact h3.1 h
  · exact h3.2.1 t ht w'' hw'' h

end GlobalTheory.StdHalfLat

namespace GlobalTheory.LastVertexMove

open GlobalTheory.StdHalfLat




theorem isSBHalf_stdLat : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {t : T}, t ∈ U → ∀ {p : Pair T}, DefPair D.R.m p → ∀ d : FinDatum G t p,
    d.P = locPl G t → IsSBHalf d.e (stdLat S p) d.fn := by
  intro D T L sc G W U S t ht p hp d _
  have key : ∀ x, IsHalf d.e x →
      (x ∈ latO (G.pS p) (G.pT p) (G.latS p : Set _) (G.latT p : Set _) (fun _ => True) ↔ x ∈ stdLat S p) := by
    intro x hx
    obtain ⟨h1, h2⟩ := hp.nodes
    rcases p with ⟨i, j⟩ | ⟨t', i, j⟩ | i | ⟨t', j⟩
    · obtain ⟨a, ha, hga⟩ := exists_kill S.N ht d h2
      obtain ⟨b, hb, hgb⟩ := exists_kill S.N ht d h1
      have m2 := hat_moves S.N h2
      have m1 := hat_moves S.N h1
      exact (mem_latO_iff_of_half (negGA _ (S.N.u (.grid (i + 1) j)).1) (S.N.u (.grid i j)).1
        m2.1 (fun v hv => by rw [← map_inv]; exact m2.2 v hv) m1.1 m1.2 ha hb hga hgb hx).symm
    · exact hp.elim
    · exact hp.elim
    · obtain ⟨a, ha, hga⟩ := exists_kill S.N ht d h1
      obtain ⟨b, hb, hgb⟩ := exists_kill S.N ht d h2
      have m1 := hat_moves S.N h1
      have m2 := hat_moves S.N h2
      exact (mem_latO_iff_of_half (S.N.u (.top j)).1 (S.N.u (.top (j + 1))).1
        m1.1 m1.2 m2.1 m2.2 ha hb hga hgb hx).symm
  obtain ⟨hsupp, k, hk, hinv, hfin⟩ := d.sb
  refine ⟨hsupp, k, hk, fun u hu hub y => hinv u ((key u hub).2 hu) hub y, fun y hy => ?_⟩
  exact (key _ (half_nsmul (hsupp y hy) k)).1 (hfin y hy)

end GlobalTheory.LastVertexMove
end
end
