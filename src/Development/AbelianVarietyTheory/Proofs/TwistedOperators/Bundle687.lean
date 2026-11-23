module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle310
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacewiseToAdelicDecompositionForall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2180
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle633
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmEqSumLattice
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle683
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle608
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle481
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle612
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle684
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumHermitianPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle261
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle244
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle504
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastTwoStepsDoubleLiftPeriodEqIntegral
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle514
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle220
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumDescendsToWittCore
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle527
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle582
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittRankZeroEmbeddingMemLatticeCongruenceIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2561
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ExpansionInvariance

theorem product_invariant : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T}
    {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) →
    (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ →
    (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) →
    ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))), finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj →
    ∀ (w : ∀ j' : Fin D.R.m, WO (G.pS (.top t j' : Pair T)) (G.pT (.top t j' : Pair T)))
      (z : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
      (τ.sum fun d a => a * (∏ j', movedCol S d j hj ((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1))) j' (w j')) *
          ∏ i, S.Z.vec (d.2 i) (z i)) =
        τ.sum fun d a => a * (∏ j', S.Z.vec (d.1 j') (w j')) * ∏ i, S.Z.vec (d.2 i) (z i) := by
  intro D T L sc G W U S t Φ β τ μ₀ hL₀ hde hcc ht hβ hexp hvec j hj k hk w z
  classical
  have hexp' := hexp
  obtain ⟨e, he, hsupp, -⟩ := hexp
  by_cases hτ : τ = 0
  · subst hτ; simp
  obtain ⟨d₀, hd₀⟩ : ∃ d, d ∈ τ.support := by
    obtain ⟨d, hd⟩ := Finsupp.ne_iff.1 hτ
    exact ⟨d, Finsupp.mem_support_iff.2 (by simpa using hd)⟩
  have hmc : ∀ j' : Fin D.R.m, ∃ Tm, IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (stdLatO S (.top t j')) 1
      (S.Z.vac (.top t j')) Tm := fun j' => by
    obtain ⟨f, hf⟩ := (hvec d₀ hd₀).1 j'
    obtain ⟨Tm, hTm⟩ := hf.1
    refine ⟨Tm, ?_⟩
    rw [← ((hsupp d₀ hd₀).1 j').2.1]
    exact hTm
  have hmr : ∀ i : Fin D.R.m, ∃ Tm, IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (stdLatO S (.chi i D.R.m)) 1
      (S.Z.vac (.chi i D.R.m)) Tm := fun i => by
    obtain ⟨f, hf⟩ := (hvec d₀ hd₀).2 i
    obtain ⟨Tm, hTm⟩ := hf.1
    refine ⟨Tm, ?_⟩
    rw [← ((hsupp d₀ hd₀).2 i).2.1]
    exact hTm
  choose Tc hTc using hmc
  choose Tr hTr using hmr
  have hvc : ∀ d ∈ τ.support, ∀ j', S.Z.vec (d.1 j') = Tc j' (d.1 j').fn := fun d hd j' =>
    vec_eq_model S _ ((hsupp d hd).1 j').2.2 ((hvec d hd).1 j') _ (by rw [((hsupp d hd).1 j').2.1]; exact hTc j')
  have hvr : ∀ d ∈ τ.support, ∀ i, S.Z.vec (d.2 i) = Tr i (d.2 i).fn := fun d hd i =>
    vec_eq_model S _ ((hsupp d hd).2 i).2.2 ((hvec d hd).2 i) _ (by rw [((hsupp d hd).2 i).2.1]; exact hTr i)
  set g : FinPt G (.top (j + 1)) := (S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) with hg
  obtain ⟨c₁, hc₁⟩ := GlobalTheory.T.columnArrow_realAverage_howeDuality_fockComponent S ht (Φ := Φ) (β := β) j hj k hk e he (Tc ⟨j, by omega⟩) (hTc ⟨j, by omega⟩)
  obtain ⟨c₂, hc₂⟩ := vac_move_high S ht j hj k hk e he (Tc ⟨j + 1, hj⟩) (hTc ⟨j + 1, hj⟩)
  have hla : ∀ X : Node, DefNode D.R.m X → (∀ i, X ≠ .grid 0 i) → X.InRange D.R.m →
      Submodule.IsFullLattice D.host.E (G.Λ X) := fun X _ h0 hX =>
        GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ (G.isV hX h0).sd
  have hsb : ∀ d ∈ τ.support, ∀ j' : Fin D.R.m, IsSBHalf e (stdLatO S (.top t j')) (d.1 j').fn := fun d hd j' => by
    have h1 := (d.1 j').sb
    rw [((hsupp d hd).1 j').2.1] at h1
    have hj₀ : (j' : ℕ) ≤ D.R.m := Nat.le_of_lt j'.2
    have hj₁ : (j' : ℕ) + 1 ≤ D.R.m := j'.2
    letI := hla (.top j') hj₀ (by simp) hj₀
    letI := hla (.top (j' + 1)) hj₁ (by simp) hj₁
    letI : Submodule.IsFullLattice D.host.E (S.N.latS (.top t j')) :=
      GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ (S.N.selfDual (X := .top j') hj₀)
    letI : Submodule.IsFullLattice D.host.E (S.N.latT (.top t j')) :=
      GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ (S.N.selfDual (X := .top (j' + 1)) hj₁)
    exact VecEx.isSBHalf_of_lattices inferInstance inferInstance inferInstance inferInstance
      (GlobalTheory.PlaceDatum.infPart_idemSum he) h1
  have hmv : ∀ d ∈ τ.support, ∀ j', movedCol S d j hj g j' =
      (Function.update (Function.update (1 : Fin D.R.m → ℂ) ⟨j, by omega⟩ c₁) ⟨j + 1, hj⟩ c₂ j') •
        Tc j' (movedFn S d j hj g j') := fun d hd j' => by
    rcases eq_or_ne j' ⟨j + 1, hj⟩ with rfl | h1
    · simp only [movedCol, movedFn, Function.update_self]
      rw [hvc d hd]
      exact GlobalTheory.SplitLinear.om_model_of_base D W.ψ _ _ _ _ _ (S.N.latS (.top t (j + 1))) (S.N.latT (.top t (j + 1))) e
        (S.Z.vac (.top t (j + 1))) _ (W.om_is (.top t (j + 1)) (show j + 1 + 1 ≤ D.R.m by omega))
        (S.N.selfDual (X := .top (j + 1)) (show j + 1 ≤ D.R.m by omega))
        (S.N.selfDual (X := .top (j + 1 + 1)) (show j + 1 + 1 ≤ D.R.m by omega))
        (GlobalTheory.PlaceDatum.idemSum_mul_self he) (GlobalTheory.PlaceDatum.infPart_idemSum he)
        (S.Z.vac_is (.top t (j + 1)) (show j + 1 + 1 ≤ D.R.m by omega)).2.theta (hTc ⟨j + 1, hj⟩) _ _ c₂ hc₂ _ (hsb d hd ⟨j + 1, hj⟩)
    rcases eq_or_ne j' ⟨j, by omega⟩ with rfl | h2
    · simp only [movedCol, movedFn, Function.update_of_ne h1, Function.update_self]
      rw [hvc d hd]
      exact GlobalTheory.SplitLinear.om_model_of_base D W.ψ _ _ _ _ _ (S.N.latS (.top t j)) (S.N.latT (.top t j)) e
        (S.Z.vac (.top t j)) _ (W.om_is (.top t j) (show j + 1 ≤ D.R.m by omega))
        (S.N.selfDual (X := .top j) (show j ≤ D.R.m by omega))
        (S.N.selfDual (X := .top (j + 1)) (show j + 1 ≤ D.R.m by omega))
        (GlobalTheory.PlaceDatum.idemSum_mul_self he) (GlobalTheory.PlaceDatum.infPart_idemSum he)
        (S.Z.vac_is (.top t j) (show j + 1 ≤ D.R.m by omega)).2.theta (hTc ⟨j, by omega⟩) _ _ c₁ hc₁ _ (hsb d hd ⟨j, by omega⟩)
    · simp only [movedCol, movedFn, Function.update_of_ne h1, Function.update_of_ne h2, Pi.one_apply, one_smul]
      exact hvc d hd j'
  have hprod : ∏ j' : Fin D.R.m, Function.update (Function.update (1 : Fin D.R.m → ℂ) ⟨j, by omega⟩ c₁) ⟨j + 1, hj⟩ c₂ j' =
      c₁ * c₂ := by
    have hne : (⟨j, by omega⟩ : Fin D.R.m) ≠ ⟨j + 1, hj⟩ := fun h => by simp [Fin.ext_iff] at h
    rw [Finset.prod_update_of_mem (Finset.mem_univ _), Finset.prod_update_of_mem (by simp [hne])]
    simp only [Pi.one_apply, Finset.prod_const_one, mul_one]
    ring
  let X : Fin D.R.m ⊕ Fin D.R.m → Type := Sum.elim (fun j' => WO (G.pS (.top t j' : Pair T)) (G.pT (.top t j' : Pair T)))
    fun i => WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))
  let Tt : ∀ a, (X a → ℂ) →ₗ[ℂ] (X a → ℂ) := fun a => match a with
    | .inl j' => Tc j'
    | .inr i => Tr i
  let F : PureDat G t → ∀ a, X a → ℂ := fun d a => match a with
    | .inl j' => (d.1 j').fn
    | .inr i => (d.2 i).fn
  let F' : PureDat G t → ∀ a, X a → ℂ := fun d a => match a with
    | .inl j' => movedFn S d j hj g j'
    | .inr i => (d.2 i).fn
  let yy : ∀ a, X a := fun a => match a with
    | .inl j' => w j'
    | .inr i => z i
  have key := sum_prod_map_congr Tt τ.support τ.support (fun d => τ d) (fun d => τ d * (c₁ * c₂)) F F' (fun x => by
    have := GlobalTheory.T.unfoldingExpansion_productFunction_localInvariant S hL₀ hde hcc ht hβ hexp' j hj k hk e he (fun d hd j' => ((hsupp d hd).1 j').2.1) _ _ (hTc ⟨j, by omega⟩)
      (hTc ⟨j + 1, hj⟩) c₁ c₂ hc₁ hc₂ (fun j' => x (.inl j')) (fun i => x (.inr i))
    simp only [Finsupp.sum] at this
    simp only [Fintype.prod_sum_type]
    refine (Finset.sum_congr rfl fun d _ => ?_).trans (this.trans (Finset.sum_congr rfl fun d _ => ?_))
    · exact (mul_assoc _ _ _).symm
    · exact mul_assoc _ _ _) yy
  simp only [Fintype.prod_sum_type] at key
  have hL : (∑ d ∈ τ.support, τ d * (∏ j', movedCol S d j hj g j' (w j')) * ∏ i, S.Z.vec (d.2 i) (z i)) =
      ∑ d ∈ τ.support, τ d * (c₁ * c₂) * ((∏ j', Tc j' (movedFn S d j hj g j') (w j')) * ∏ i, Tr i (d.2 i).fn (z i)) :=
    Finset.sum_congr rfl fun d hd => by
      simp only [hmv d hd, hvr d hd, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, hprod]; ring
  have hR : (∑ d ∈ τ.support, τ d * (∏ j', S.Z.vec (d.1 j') (w j')) * ∏ i, S.Z.vec (d.2 i) (z i)) =
      ∑ d ∈ τ.support, τ d * ((∏ j', Tc j' (d.1 j').fn (w j')) * ∏ i, Tr i (d.2 i).fn (z i)) :=
    Finset.sum_congr rfl fun d hd => by simp only [hvc d hd, hvr d hd]; ring
  simp only [Finsupp.sum]
  rw [hL, hR]
  exact key

end GlobalTheory.ExpansionInvariance

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR Formalism.IndefR.Links GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.ChiGrid GlobalTheory.Unf GlobalTheory.FunObj GlobalTheory.RowUnf GlobalTheory.RowChain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowChain.LastSeeSawStep

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem topOrthAt_emb (G : GridData L sc) {n : ℕ} (h : D.R.m = n) (h' : GA D (G.V (.grid D.R.m D.R.m))) :
    (topOrthAt G h).emb (h', 1) = topEmb G h h' := by
  subst h
  exact topOrth_emb G h'

theorem lastTau_gram :
    (lastTau (D := D))ᴴ * ((GlobalTheory.SeeSaw.Model.nLine D).gram * lastTau) =
      (-(D.host.xi0 * star D.host.xi0)) • (pLine D).gram := by
  refine Matrix.ext fun i j => ?_
  rw [pLine_gram]
  have h1 : ∀ a b : Fin (GlobalTheory.SeeSaw.Model.nLine D).rank, (GlobalTheory.SeeSaw.Model.nLine D).gram a b = -1 := nLine_gram
  simp only [Matrix.mul_apply, conjTranspose_apply, lastTau, Matrix.of_apply, Matrix.smul_apply, h1]
  change ∑ x : Fin 1, star (-D.host.xi0) * ∑ y : Fin 1, (-1) * (-D.host.xi0) = (-(D.host.xi0 * star D.host.xi0)) * antiDiagonalSignGramMatrix (R := D.host.E) 1 1 i j
  have hij : i = j := Subsingleton.elim (α := Fin 1) _ _
  subst hij
  have hi : (i : ℕ) = 0 := by have := i.2; change (i : ℕ) < 1 at this; omega
  simp [antiDiagonalSignGramMatrix, hi]
  ring

end GlobalTheory.RowChain.LastSeeSawStep

namespace GlobalTheory.RowChain.LastSeeSawStep



theorem main : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (Wl : G.Weil) (t : T) {M : GlobalTheory.FunObj.Vol G}
    (hM : M.Is t) (j : ℕ) (hj : j + 2 * 0 + 2 = D.R.m) (vN : VolN (besDecAt G j 0 hj))
    (Φ₁ : WO (G.V (.grid D.R.m j)) (G.V (.grid D.R.m (j + 1))) → ℂ)
    (Φ₂ : WO (G.V (.grid D.R.m (j + 1))) (G.V (.grid D.R.m D.R.m)) → ℂ) (F : Fn G (.grid D.R.m D.R.m))
    (φ : GA D (G.V (.top j)) → ℂ),
    IsThetaFunO Wl.ψ _ _ Φ₁ → IsThetaFunO Wl.ψ _ _ Φ₂ → IsContAut (G.V (.grid D.R.m D.R.m)) F → IsContAut (G.V (.top j)) φ →
    ∀ g : GA D (G.V (.grid D.R.m j)),
      (lastAt G Wl t hM j hj vN).Q φ ((lastAt G Wl t hM j hj vN).s.om (g, 1) Φ₁) Φ₂ F =
        ∫ h' in M.fd (.grid D.R.m D.R.m), F h' * GlobalTheory.SeeSaw.biLift (Wl.om (.top t j)) (Wl.om (.top t (j + 1)))
          (volAt hM (.top j) (by show j ≤ D.R.m; omega)) (volAt hM (.top (j + 1)) (by show j + 1 ≤ D.R.m; omega)) φ
          (lastDat Wl hM j hj vN g Φ₁ Φ₂) (topEmb G (show D.R.m = j + 1 + 1 by omega) h') ∂M.ν (.grid D.R.m D.R.m) := by
  intro D T L sc G Wl t M hM j hj vN Φ₁ Φ₂ F φ hΦ₁ hΦ₂ hF hφ g
  have hψ : IsStdChar D Wl.ψ (-1) := Wl.ψ_std
  obtain ⟨χz, hzH, hzE, -, hev, hodd⟩ := GlobalTheory.RowChars.rowChars G Wl t
  obtain ⟨hS0, hT0⟩ := hodd j (by omega) (by omega)
  obtain ⟨hS1, hT1⟩ := hev (j + 1) (by omega) (by omega)
  have homa : IsWeilDatumO Wl.ψ (G.V (.top j)) (G.V (.top (j + 1))) (G.chrS (.top t j)) (G.chrT (.top t j))
      (Wl.om (.top t j)) := Wl.om_is (.top t j) (by show j + 1 ≤ D.R.m; omega)
  have homX0 : IsWeilDatumO Wl.ψ (G.V (.top (j + 1))) (G.V (.top (j + 1 + 1))) (G.chrS (.top t (j + 1)))
      (G.chrT (.top t (j + 1))) (Wl.om (.top t (j + 1))) := Wl.om_is (.top t (j + 1)) (by show j + 1 + 1 ≤ D.R.m; omega)
  have homX : IsWeilDatumO Wl.ψ (G.V (.top (j + 1))) (G.V (.top (j + 1 + 1))) (G.chrS (.top t (j + 1)))
      (G.chrT (.top t (j + 1)) * χz * χz⁻¹) (Wl.om (.top t (j + 1))) := by
    rw [mul_inv_cancel_right]; exact homX0
  have hom₁ : IsWeilDatumO Wl.ψ (besAt G hM j 0 hj vN).V₀ (G.V (.top (j + 1))) (G.chrS (.top t j) * χz) (G.chrT (.top t j)) (lastAt G Wl t hM j hj vN).s.om₀ := by
    rw [← hS0, ← hT0]; exact (lastAt G Wl t hM j hj vN).s.weil₀
  obtain ⟨omT, homT⟩ := (GlobalTheory.Desc.weil_data_descend D Wl.ψ _ _ _ _ _ (lastAt G Wl t hM j hj vN).weil).1 (G.V (.top (j + 1))) 0 (rowJac G (j + 1) (by omega) 0 (by omega))
  have homT' : IsWeilDatumO Wl.ψ (G.V (.top (j + 1))) (G.V (.grid D.R.m D.R.m)) (G.chrS (.top t (j + 1)))
      (G.chrT (.top t (j + 1)) * χz) omT := by
    rw [← hS1, ← hT1]; exact homT
  obtain ⟨omz, homz⟩ := GlobalTheory.WeilDatumExistence.weilDatumExists D (GlobalTheory.SeeSaw.Model.nLine D) (G.V (.top (j + 1))) Wl.ψ χz
    (G.chrT (.top t j)) hψ hzH homa.hecT hzE homa.resT
  obtain ⟨hzH', hzE'⟩ := GlobalTheory.StdUnn.isHeckeChar_resEta_inv D χz 1 hzH hzE
  obtain ⟨omz'', homz''⟩ := GlobalTheory.WeilDatumExistence.weilDatumExists D (G.V (.top (j + 1))) (pLine D) Wl.ψ
    (G.chrS (.top t (j + 1))) χz⁻¹ hψ homX0.hecS hzH' homX0.resS hzE'
  have hΨ : IsThetaFunO Wl.ψ _ _ ((lastAt G Wl t hM j hj vN).s.om (g, 1) Φ₁) := (lastAt G Wl t hM j hj vN).s.weil.om_pres _ _ hΦ₁
  have hΞ : IsThetaFunO Wl.ψ (besAt G hM j 0 hj vN).V₀ (G.V (.top (j + 1))) (flatBF (lastAt G Wl t hM j hj vN).s ((lastAt G Wl t hM j hj vN).s.om (g, 1) Φ₁)) :=
    (GlobalTheory.LastRed.val_zero (lastAt G Wl t hM j hj vN).s hΨ).1
  have hΦ₂' : IsThetaFunO Wl.ψ (G.V (.top (j + 1))) (G.V (.grid D.R.m D.R.m))
      (fun w => Φ₂ ((rowJac G (j + 1) (by omega) 0 (by omega)).ext0 _ w)) := GlobalTheory.RankZeroVac.isThetaFunction_comp_wittExtendByZero _ _ hΦ₂
  obtain ⟨-, key⟩ := GlobalTheory.SeeLastPf.seeLast D Wl.ψ (besAt G hM j 0 hj vN).V₀ (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D) (G.V (.top (j + 1)))
    (G.V (.top (j + 1 + 1))) (G.V (.grid D.R.m D.R.m)) (pLine D) (besAt G hM j 0 hj vN).o (topOrthAt G (show D.R.m = j + 1 + 1 by omega))
    lastTau rfl rfl lastTau_gram (G.chrS (.top t j)) χz (G.chrT (.top t j)) (G.chrS (.top t (j + 1)))
    (G.chrT (.top t (j + 1)) * χz) (lastAt G Wl t hM j hj vN).s.om₀ (Wl.om (.top t j)) omz (Wl.om (.top t (j + 1))) omT omz''
    hom₁ homa homz homX homT' homz'' _ _ hΞ hΦ₂'
  have hC := GlobalTheory.LastBiTheta.isBiTheta_lastBi D Wl.ψ hψ (besAt G hM j 0 hj vN).V₀ (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)
    (G.V (.top (j + 1))) (G.V (.top (j + 1 + 1))) (G.V (.grid D.R.m D.R.m)) (pLine D) (besAt G hM j 0 hj vN).o
    (topOrthAt G (show D.R.m = j + 1 + 1 by omega)) lastTau lastTau_gram _ _ hΞ hΦ₂'
  obtain ⟨-, -, hcomm, -⟩ := GlobalTheory.SeeSaw.biAct_all D Wl.ψ (G.V (.top j)) (G.V (.top (j + 1))) (G.V (.top (j + 1 + 1)))
    _ _ _ _ (Wl.om (.top t j)) (Wl.om (.top t (j + 1))) homa homX0 _ hC
  have pt : ∀ h' g₀ h₀, omT (g₀, h') (fun w => Φ₂ ((rowJac G (j + 1) (by omega) 0 (by omega)).ext0 _ w)) 0 *
      (φ h₀ * (lastAt G Wl t hM j hj vN).s.om₀ ((besAt G hM j 0 hj vN).o.emb (h₀, 1), g₀) (flatBF (lastAt G Wl t hM j hj vN).s ((lastAt G Wl t hM j hj vN).s.om (g, 1) Φ₁)) 0) =
      φ h₀ * Wl.om (.top t (j + 1)) (g₀, topEmb G (show D.R.m = j + 1 + 1 by omega) h')
        (fun v => Wl.om (.top t j) (h₀, g₀) (fun u => lastDat Wl hM j hj vN g Φ₁ Φ₂ u v) 0) 0 := by
    intro h' g₀ h₀
    rw [mul_left_comm]
    congr 1
    refine (key h₀ g₀ h').trans ?_
    rw [← topOrthAt_emb]
    exact (hcomm (h₀, g₀) (g₀, _) 0 0).symm
  have inner : ∀ h', (∫ h in (lastAt G Wl t hM j hj vN).s.vW.𝓕, (lastAt G Wl t hM j hj vN).om (h, h') Φ₂ 0 *
      (∫ h₀ in (besAt G hM j 0 hj vN).vA.𝓕, φ h₀ * (lastAt G Wl t hM j hj vN).s.om (embA (besAt G hM j 0 hj vN).d (besAt G hM j 0 hj vN).o h₀, h) ((lastAt G Wl t hM j hj vN).s.om (g, 1) Φ₁) 0 ∂(besAt G hM j 0 hj vN).vA.μ) ∂(lastAt G Wl t hM j hj vN).s.vW.μ) =
      GlobalTheory.SeeSaw.biLift (Wl.om (.top t j)) (Wl.om (.top t (j + 1)))
        (volAt hM (.top j) (by show j ≤ D.R.m; omega)) (volAt hM (.top (j + 1)) (by show j + 1 ≤ D.R.m; omega)) φ
        (lastDat Wl hM j hj vN g Φ₁ Φ₂) (topEmb G (show D.R.m = j + 1 + 1 by omega) h') := by
    intro h'
    refine (GlobalTheory.RowVolZero.vol_rankZero G t hM (j + 1) (by omega) (fun h => (lastAt G Wl t hM j hj vN).om (h, h') Φ₂ 0 *
      (∫ h₀ in (besAt G hM j 0 hj vN).vA.𝓕, φ h₀ * (lastAt G Wl t hM j hj vN).s.om (embA (besAt G hM j 0 hj vN).d (besAt G hM j 0 hj vN).o h₀, h) ((lastAt G Wl t hM j hj vN).s.om (g, 1) Φ₁) 0 ∂(besAt G hM j 0 hj vN).vA.μ)) ?_).trans ?_
    · intro γ hγ x
      have a1 : (lastAt G Wl t hM j hj vN).om (γ * x, h') Φ₂ 0 = (lastAt G Wl t hM j hj vN).om (x, h') Φ₂ 0 := by
        have hm : (lastAt G Wl t hM j hj vN).om (γ * x, h') = (lastAt G Wl t hM j hj vN).om (γ, 1) * (lastAt G Wl t hM j hj vN).om (x, h') := by
          rw [← map_mul]; exact congrArg _ (Prod.ext rfl (one_mul h').symm)
        rw [hm]
        exact (lastAt G Wl t hM j hj vN).weil.om_aut γ hγ 1 (one_mem _) _ ((lastAt G Wl t hM j hj vN).weil.om_pres _ _ hΦ₂)
      have a2 : ∀ h₀, (lastAt G Wl t hM j hj vN).s.om (embA (besAt G hM j 0 hj vN).d (besAt G hM j 0 hj vN).o h₀, γ * x) ((lastAt G Wl t hM j hj vN).s.om (g, 1) Φ₁) 0 =
          (lastAt G Wl t hM j hj vN).s.om (embA (besAt G hM j 0 hj vN).d (besAt G hM j 0 hj vN).o h₀, x) ((lastAt G Wl t hM j hj vN).s.om (g, 1) Φ₁) 0 := by
        intro h₀
        have hm : (lastAt G Wl t hM j hj vN).s.om (embA (besAt G hM j 0 hj vN).d (besAt G hM j 0 hj vN).o h₀, γ * x) = (lastAt G Wl t hM j hj vN).s.om (1, γ) * (lastAt G Wl t hM j hj vN).s.om (embA (besAt G hM j 0 hj vN).d (besAt G hM j 0 hj vN).o h₀, x) := by
          rw [← map_mul]; exact congrArg _ (Prod.ext (one_mul _).symm rfl)
        rw [hm]
        exact (lastAt G Wl t hM j hj vN).s.weil.om_aut 1 (one_mem _) γ hγ _ ((lastAt G Wl t hM j hj vN).s.weil.om_pres _ _ hΨ)
      simp only [a1, a2]
    · unfold GlobalTheory.SeeSaw.biLift
      refine integral_congr_ae (Filter.Eventually.of_forall fun g₀ => ?_)
      have e1 : (lastAt G Wl t hM j hj vN).om ((rowJac G (j + 1) (by omega) 0 (by omega)).emb0 g₀, h') Φ₂ 0 = omT (g₀, h') (fun w => Φ₂ ((rowJac G (j + 1) (by omega) 0 (by omega)).ext0 _ w)) 0 :=
        GlobalTheory.FinPl.VLast.Transport.weilRep_rankZeroWittEmbedding_valueAtZero D Wl.ψ _ _ _ (rowJac G (j + 1) (by omega) 0 (by omega)) _ _ _ omT (lastAt G Wl t hM j hj vN).weil homT Φ₂ hΦ₂ g₀ h'
      have e2 : ∀ h₀, (lastAt G Wl t hM j hj vN).s.om (embA (besAt G hM j 0 hj vN).d (besAt G hM j 0 hj vN).o h₀, (rowJac G (j + 1) (by omega) 0 (by omega)).emb0 g₀) ((lastAt G Wl t hM j hj vN).s.om (g, 1) Φ₁) 0 =
          (lastAt G Wl t hM j hj vN).s.om₀ ((besAt G hM j 0 hj vN).o.emb (h₀, 1), g₀) (flatBF (lastAt G Wl t hM j hj vN).s ((lastAt G Wl t hM j hj vN).s.om (g, 1) Φ₁)) 0 := fun h₀ =>
        GlobalTheory.FinPl.VLast.Transport.om_flatBF_rankZero D Wl.ψ (besAt G hM j 0 hj vN) (lastAt G Wl t hM j hj vN).J (lastAt G Wl t hM j hj vN).s _ hΨ h₀ g₀
      show (lastAt G Wl t hM j hj vN).om ((rowJac G (j + 1) (by omega) 0 (by omega)).emb0 g₀, h') Φ₂ 0 * (∫ h₀ in (besAt G hM j 0 hj vN).vA.𝓕,
        φ h₀ * (lastAt G Wl t hM j hj vN).s.om (embA (besAt G hM j 0 hj vN).d (besAt G hM j 0 hj vN).o h₀, (rowJac G (j + 1) (by omega) 0 (by omega)).emb0 g₀) ((lastAt G Wl t hM j hj vN).s.om (g, 1) Φ₁) 0 ∂(besAt G hM j 0 hj vN).vA.μ) = _
      rw [e1]
      simp only [e2]
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun h₀ => ?_)
      exact pt h' g₀ h₀
  unfold Last.Q
  refine integral_congr_ae (Filter.Eventually.of_forall fun h' => ?_)
  exact congrArg (F h' * ·) (inner h')

end GlobalTheory.RowChain.LastSeeSawStep
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3
open GlobalTheory.RowClaim

namespace GlobalTheory.Twist

theorem atDat_rowTest_of_exField : GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.CuspRapidDecay → LinK → InjK → ConstK → SumOKK → Formula2K → SumRatK → RatioK → GlobalTheory.RowEx.ExField → AtDat fun _ _ _ _ _ _ _ _ z => Formalism.IndefR.Rat.RowTest (z.R.toCx3 z.F) :=
  fun hG hC h1 h2 h3 h4 h5 h6 h7 hE => GlobalTheory.Mem.R3.Rw.RowAt.atDat_rowTest hG hC h1 h2 h3 h4 h5 h6 h7 hE

end GlobalTheory.Twist
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FirstRowLevel

theorem finE_cast_mem {D : D7} (X Y : LSp D) (e : X = Y) (K : Subgroup (GL (Fin X.sp.rank) (Lev.EAf D)))
    (K' : Subgroup (GL (Fin Y.sp.rank) (Lev.EAf D))) (h : HEq K K') (g : GA D X.sp) (hg : Lev.finE X.sp g ∈ K) :
    Lev.finE Y.sp (cast (congrArg (fun Z : LSp D => GA D Z.sp) e) g) ∈ K' := by
  subst e
  cases h
  exact hg

theorem toXf_mem_of_is {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) {U : Set T}
    (S : GridChoice W U) {μ₀ : T} (hL : L.Is μ₀) (t : T) (k : FinPt G (.grid 0 D.R.m))
    (hk : finG (G.V (.grid 0 D.R.m)) k ∈ S.levRow t 0 (Nat.zero_le _)) :
    toXf k ∈ (levEnv D.sp.X' L.βX (L.datXt t)).J := by

  have hU : finG (G.V (.grid 0 D.R.m)) k ∈ S.levRow t 0 (Nat.zero_le _) ⊓ UA D.sp.cm (G.V (.grid 0 D.R.m)).gram :=
    ⟨hk, GlobalTheory.LevSplit.finE_mem_UA _ _⟩
  have hX := finE_cast_mem (columnBlock L D.R.m) ⟨D.sp.X', L.ΛX⟩ (colY_m L) _ _
    (GlobalTheory.T.gridRowLevel_zero_inf_unitary_eq_datumLevel W S hL t (Nat.zero_le _)) k.1 hU
  exact hX

theorem levRow_zero_le : Big fun {D} {_Γ} _ _ {_Pl0} {T} {_A} {_Ks} _ _ _ {R} ch =>
    ∀ (t : T) (k : FinPt ch.G (.grid 0 D.R.m)), finG (ch.G.V (.grid 0 D.R.m)) k ∈ ch.S.levRow t 0 (Nat.zero_le _) →
      toXf k ∈ (levEnv D.sp.X' R.βX (R.datXt t)).J := by
  refine ⟨0, fun ε CF _ => ⟨0, ?_⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ _
  exact fun t k hk => toXf_mem_of_is ch.W ch.S.toGridChoice hS.core.lev t k hk

end GlobalTheory.FirstRowLevel

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim

theorem _root_.GlobalTheory.T.unfoldedFlipTensor_values_mem_coeffField : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A) (CF b : ℝ), HidaSetting large₂ R F → ch.Is → ch.AtScale CF b → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ch.S.SumOK t Φ → ∀ β ∈ ch.S.supp t Φ, ∀ (w : locPl ch.G t) X Y, (ch.S.term t Φ β w).datum X Y ∈ Set.range D.what₂.embLL := by
  first | exact @GlobalTheory.RowTest.term_datum_mem_range | exact GlobalTheory.RowTest.term_datum_mem_range | (intros; apply GlobalTheory.RowTest.term_datum_mem_range <;> assumption)
end
