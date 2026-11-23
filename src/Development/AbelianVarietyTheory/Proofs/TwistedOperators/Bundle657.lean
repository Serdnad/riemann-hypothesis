module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle636
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaAtSeesawProductDatumEqVacuumCombinations
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingMulRight
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle204
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle221
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle209
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle023
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle650
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainCompositeLiftIntertwinesFiniteGroupActions
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle469

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section
namespace GlobalTheory.CosetRow

section ThetaExt
variable {D : D7} {m n : ℕ}

theorem isHalf_add_right_iff {e : AE D} {t x : Mx D m n} (hx : IsHalf e x) :
    IsHalf e (t + x) ↔ IsHalf e t := by
  constructor
  · intro h i j
    have h1 := h i j
    have h2 := hx i j
    simp only [Matrix.add_apply, mul_add] at h1
    linear_combination h1 - h2
  · intro h i j
    have h1 := h i j
    have h2 := hx i j
    simp only [Matrix.add_apply, mul_add]
    linear_combination h1 + h2

theorem smul_of_isHalf {e : AE D} {x : Mx D m n} (hx : IsHalf e x) : e • x = x := by
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact hx i j

theorem smul_eq_zero_of_isHalf {e e' : AE D} (h : e' * e = 0) {x : Mx D m n} (hx : IsHalf e x) : e' • x = 0 := by
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
  rw [← hx i j, ← mul_assoc, h, zero_mul]

theorem isHalf_smul_idem {e : AE D} (he : e * e = e) (t : Mx D m n) : IsHalf e (e • t) := by
  intro i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [← mul_assoc, he]

def extLin (e₀ e₁ : AE D) (Λ : AddSubgroup (Mx D m n)) : (Mx D m n → ℂ) →ₗ[ℂ] (Mx D m n → ℂ) where
  toFun := extFn e₀ e₁ Λ
  map_add' Φ Ψ := by
    funext t
    simp only [extFn, Pi.add_apply]
    split_ifs <;> ring
  map_smul' c Φ := by
    funext t
    simp only [extFn, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

theorem extFn_shift {e₀ e₁ : AE D} (h10 : e₁ * e₀ = 0) (Λ : AddSubgroup (Mx D m n)) (Φ : Mx D m n → ℂ)
    {x : Mx D m n} (hx : IsHalf e₀ x) :
    extFn e₀ e₁ Λ (fun t => Φ (t + x)) = fun t => extFn e₀ e₁ Λ Φ (t + x) := by
  funext t
  have hx' : IsHalf (e₀ + e₁) x := by
    rw [add_comm]; exact GlobalTheory.VecProd.half_add_of_right h10 hx
  simp only [extFn]
  rw [isHalf_add_right_iff hx', smul_add, smul_add, smul_of_isHalf hx, smul_eq_zero_of_isHalf h10 hx, add_zero]

theorem extFn_modul {e₀ e₁ : AE D} (Λ : AddSubgroup (Mx D m n)) (Φ : Mx D m n → ℂ) (g : Mx D m n → ℂ)
    (hg : ∀ t, IsHalf (e₀ + e₁) t → g t = g (e₀ • t)) :
    extFn e₀ e₁ Λ (fun t => g t * Φ t) = fun t => g t * extFn e₀ e₁ Λ Φ t := by
  funext t
  simp only [extFn]
  split_ifs with h
  · rw [hg t h]; ring
  · ring

theorem extFn_halfInd {e₀ e₁ : AE D} (h00 : e₀ * e₀ = e₀) (h11 : e₁ * e₁ = e₁) {Λ : AddSubgroup (Mx D m n)}
    (hΛ0 : ∀ u ∈ Λ, e₀ • u ∈ Λ) (hΛ1 : ∀ u ∈ Λ, e₁ • u ∈ Λ) :
    extFn e₀ e₁ Λ (halfInd e₀ Λ) = halfInd (e₀ + e₁) Λ := by
  funext t
  simp only [extFn, halfInd]
  by_cases ht : IsHalf (e₀ + e₁) t
  · have hdec : t = e₀ • t + e₁ • t := by
      rw [← add_smul, smul_of_isHalf ht]
    have hiff : (e₀ • t ∈ Λ ∧ e₁ • t ∈ Λ) ↔ t ∈ Λ := by
      constructor
      · rintro ⟨h0, h1⟩; rw [hdec]; exact Λ.add_mem h0 h1
      · intro h; exact ⟨hΛ0 t h, hΛ1 t h⟩
    have a0 := isHalf_smul_idem h00 t
    have a1 := isHalf_smul_idem h11 t
    rw [if_pos ht]
    by_cases h0 : e₀ • t ∈ Λ <;> by_cases h1 : e₁ • t ∈ Λ
    · rw [if_pos ⟨h0, a0⟩, if_pos ⟨h1, a1⟩, if_pos ⟨hiff.1 ⟨h0, h1⟩, ht⟩, one_mul]
    · rw [if_pos ⟨h0, a0⟩, if_neg (fun h => h1 h.1), if_neg (fun h => h1 (hiff.2 h.1).2), mul_zero]
    · rw [if_neg (fun h => h0 h.1), if_pos ⟨h1, a1⟩, if_neg (fun h => h0 (hiff.2 h.1).1), zero_mul]
    · rw [if_neg (fun h => h0 h.1), if_neg (fun h => h1 h.1), if_neg (fun h => h0 (hiff.2 h.1).1), zero_mul]
  · simp only [if_neg ht]
    rw [if_neg (fun h => ht h.2)]

theorem isThetaAt_extFn : ∀ {D : D7} {m n : ℕ} {ψ : AddChar (AF D.host.F) ℂ} {B : Mx D m n → Mx D m n → AF D.host.F} {hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ)} {Λ : AddSubgroup (Mx D m n)} {e₀ e₁ : AE D} {f₀ Φ f : Mx D m n → ℂ}, e₀ * e₀ = e₀ → e₁ * e₁ = e₁ → e₀ * e₁ = 0 → (∀ u ∈ Λ, e₀ • u ∈ Λ) → (∀ u ∈ Λ, e₁ • u ∈ Λ) → (∀ t y, IsHalf (e₀ + e₁) t → IsHalf (cA D e₀) y → B t y = B (e₀ • t) y) → (∃ T, IsPlaceModel ψ B hs (e₀ + e₁) Λ 1 f₀ T) → IsThetaAt ψ B hs e₀ Λ 1 f₀ Φ f → IsThetaAt ψ B hs (e₀ + e₁) Λ 1 f₀ (GlobalTheory.CosetRow.extFn e₀ e₁ Λ Φ) f := by
  intro D m n ψ B hs Λ e₀ e₁ f₀ Φ f h00 h11 h01 hΛ0 hΛ1 hB hex h
  have h10 : e₁ * e₀ = 0 := by rw [mul_comm]; exact h01
  have hsb : ∀ Ψ, IsSBHalf e₀ Λ Ψ → IsSBHalf (e₀ + e₁) Λ (extFn e₀ e₁ Λ Ψ) := fun Ψ hΨ =>
    GlobalTheory.T.isSBHalf_halfExtensionLatticeIndicatorFn h00 h11 h01 hΛ0 hΛ1 hΨ
  refine ⟨hex, fun T hT => ?_⟩
  have hT₀ : IsPlaceModel ψ B hs e₀ Λ 1 f₀ (T ∘ₗ extLin e₀ e₁ Λ) := by
    refine ⟨fun Ψ hΨ x hx => ?_, fun Ψ hΨ y hy => ?_, ?_⟩
    · have hx' : IsHalf (e₀ + e₁) x := by
        rw [add_comm]; exact GlobalTheory.VecProd.half_add_of_right h10 hx
      simp only [LinearMap.comp_apply]
      change T (extFn e₀ e₁ Λ (fun t => Ψ (t + x))) = hs x (T (extFn e₀ e₁ Λ Ψ))
      rw [extFn_shift h10 Λ Ψ hx]
      exact hT.trans _ (hsb Ψ hΨ) x hx'
    · have hy' : IsHalf (cA D (e₀ + e₁)) y := by
        rw [add_comm]; exact GlobalTheory.VecProd.half_conj_add_of_right h10 hy
      simp only [LinearMap.comp_apply]
      change T (extFn e₀ e₁ Λ (fun t => ψ (B t y) * Ψ t)) = hs y (T (extFn e₀ e₁ Λ Ψ))
      rw [extFn_modul Λ Ψ (fun t => ψ (B t y)) (fun t ht => by simp only [hB t y ht hy])]
      exact hT.modul _ (hsb Ψ hΨ) y hy'
    · simp only [LinearMap.comp_apply, one_smul]
      change T (extFn e₀ e₁ Λ (halfInd e₀ Λ)) = f₀
      rw [extFn_halfInd h00 h11 hΛ0 hΛ1]
      simpa using hT.vac
  exact h.2 _ hT₀

end ThetaExt

end GlobalTheory.CosetRow

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowReal

section Subst

variable {D : D7}

def fockSubAll {m n : ℕ} (pS pT : D.what₂.Tau → ℕ) (κS : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ)
    (κT : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) : MvPolynomial (FVar D m n) ℂ →ₐ[ℂ] MvPolynomial (FVar D m n) ℂ :=
  MvPolynomial.aeval fun y : FVar D m n =>
    ∑ i, ∑ j, MvPolynomial.C (if (y.2.1.val < pT y.1 ↔ y.2.2.val < pS y.1) then κT y.1 i y.2.1 * (κS y.1)⁻¹ y.2.2 j
      else (starRingEnd ℂ) (κT y.1 i y.2.1 * (κS y.1)⁻¹ y.2.2 j)) * MvPolynomial.X (y.1, i, j)

end Subst

section Points

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def ptTop (W : G.Weil) (g : Gc D.what₂.Tau (rowSizes D)) (n : ℕ) : GA D (G.V (.top n)) :=
  if h : n < D.R.m then (kappa W g).1 ⟨n, h⟩ else if h' : n = D.R.m then h' ▸ kappaTop W g else 1

def ptGrid (W : G.Weil) (g : Gc D.what₂.Tau (rowSizes D)) (i : ℕ) : GA D (G.V (.grid i D.R.m)) :=
  if h : i < D.R.m + 1 then (kappa W g).2 ⟨i, h⟩ else 1

theorem ptTop_lt (W : G.Weil) (g : Gc D.what₂.Tau (rowSizes D)) {n : ℕ} (h : n < D.R.m) :
    ptTop W g n = (kappa W g).1 ⟨n, h⟩ := by
  simp only [ptTop, dif_pos h]

theorem ptTop_m (W : G.Weil) (g : Gc D.what₂.Tau (rowSizes D)) : ptTop W g D.R.m = kappaTop W g := by
  simp only [ptTop, lt_irrefl, dif_neg (lt_irrefl _), not_false_eq_true]
  rfl

theorem ptGrid_le (W : G.Weil) (g : Gc D.what₂.Tau (rowSizes D)) {i : ℕ} (h : i < D.R.m + 1) :
    ptGrid W g i = (kappa W g).2 ⟨i, h⟩ := by
  simp only [ptGrid, dif_pos h]

end Points

section Scal

variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : Sizes} (P : ι → Entries S)

def rowScal (j : Fin S.m) (g : Gc ι S) : ℂ :=
  ((detChar (S.nR j.castSucc) (fun τ => (P τ).e j - (S.nR j.succ / 2 : ℕ)) ((rowComp S g) j.castSucc) *
    detChar (S.nR j.succ) (fun τ => -(P τ).e j + (S.nR j.castSucc / 2 : ℕ)) ((rowComp S g) j.succ) : ℂˣ) : ℂ)

def colScal (i : Fin S.m) (g : Gc ι S) : ℂ :=
  ((detChar (S.nC i.castSucc) (fun τ => (P τ).c i.rev - ((S.nC i.succ + 1) / 2 : ℕ)) (g.2 i.castSucc) *
    detChar (S.nC i.succ) (fun τ => -(P τ).c i.rev + ((S.nC i.castSucc + 1) / 2 : ℕ)) (g.2 i.succ) : ℂˣ) : ℂ)

end Scal

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

section Frame

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def topFrame (W : G.Weil) (τ : D.what₂.Tau) : Matrix (Fin (G.V (.top D.R.m)).rank) (Fin (G.V (.top D.R.m)).rank) ℂ :=
  Matrix.of fun a k =>
    Sum.elim (fun b : Fin ((rowSizes D).nC D.R.m) =>
        ((frameMat _ _ G.sp.topDec.ι).map (tauE D τ) * W.onb (.grid D.R.m D.R.m) τ) a (Fin.cast (rank_gridM G le_rfl).symm b))
      (fun _ : Fin 1 => (G.sp.topDec.a.map (tauE D τ)) a 0)
      ((finSumFinEquiv.trans (finCongr (rowSizes D).nC_succ)).symm (Fin.cast (rank_top G le_rfl) k))

end Frame

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

section More

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem ptTop_mem (W : G.Weil) (g : Gc D.what₂.Tau (rowSizes D)) (n : ℕ) : ptTop W g n ∈ GinfC (G.V (.top n)) := by
  unfold ptTop
  split_ifs with h h'
  · exact kappa_fst_mem W g _
  · subst h'; exact kappaTop_mem W g
  · exact one_mem _

theorem ptGrid_mem (W : G.Weil) (g : Gc D.what₂.Tau (rowSizes D)) (i : ℕ) : ptGrid W g i ∈ GinfC (G.V (.grid i D.R.m)) := by
  unfold ptGrid
  split_ifs with h
  · exact kappa_snd_mem W g _
  · exact one_mem _

theorem isKMat_cast {a b : ℕ} (h : a = b) (u : Matrix.unitaryGroup (Fin b) ℂ) {p : ℕ} (hp : p = a ∨ p = 0) :
    GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsKMat p ((u : Matrix (Fin b) (Fin b) ℂ).submatrix (Fin.cast h) (Fin.cast h)) := by
  subst h
  refine ⟨by simpa using u.2, fun i j hij => absurd ?_ hij⟩
  rcases hp with rfl | rfl
  · exact iff_of_true i.2 j.2
  · exact iff_of_false (Nat.not_lt_zero _) (Nat.not_lt_zero _)

theorem trCol_injective (G : GridData L sc) (j : Fin D.R.m) : Function.Injective (trCol G j) :=
  MvPolynomial.rename_injective _ fun x y h => by
    simp only [Prod.mk.injEq, Fin.cast_inj] at h
    exact Prod.ext h.1 (Prod.ext h.2.1 h.2.2)

theorem trRow_injective (G : GridData L sc) (i : Fin D.R.m) : Function.Injective (trRow G i) :=
  MvPolynomial.rename_injective _ fun x y h => by
    simp only [Prod.mk.injEq, Fin.cast_inj] at h
    exact Prod.ext h.1 (Prod.ext h.2.2 h.2.1)

theorem eq_conj_of_inFrame {n : ℕ} {B M K : Matrix (Fin n) (Fin n) ℂ} (hB : IsUnit B.det) (h : B⁻¹ * M * B = K) :
    M = B * K * B⁻¹ := by
  rw [← h]
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hB, Matrix.mul_one]
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hB, Matrix.one_mul]

end More

end GlobalTheory.RowReal
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open GlobalTheory.ChiGrid GlobalTheory.RowReal GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CoefPairTens

open GlobalTheory.DefLift GlobalTheory.DefiniteMult Formalism.IndefR.Mult

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}

theorem sigma_one (M : DSModel V S) (τ : D.what₂.Tau) : M.σ τ 1 = 1 := (M.ds τ).2.2.1.1.1

theorem sigma_mul (hp : AllPlus M) (τ : D.what₂.Tau) (a b : Matrix.unitaryGroup (Fin V.rank) ℂ) :
    M.σ τ ((a : Matrix (Fin V.rank) (Fin V.rank) ℂ) * b) = (M.σ τ a).comp (M.σ τ b) := by
  have hm : ∀ x : Matrix.unitaryGroup (Fin V.rank) ℂ,
      (x : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᴴ * Formalism.REAL.Jm (M.ε τ) * x = Formalism.REAL.Jm (M.ε τ) := fun x => by
    rw [hp.jm τ, Matrix.mul_one]
    exact Matrix.mem_unitaryGroup_iff'.1 x.2
  exact (M.ds τ).2.2.1.1.2 _ (hm a) _ (hm b)

theorem sigma_comp_inv (hp : AllPlus M) (τ : D.what₂.Tau) (v : Matrix.unitaryGroup (Fin V.rank) ℂ) :
    ((M.σ τ v : M.H τ →L[ℂ] M.H τ) : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ
      ((M.σ τ (v⁻¹ : Matrix.unitaryGroup (Fin V.rank) ℂ) : M.H τ →L[ℂ] M.H τ) : M.H τ →ₗ[ℂ] M.H τ) = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  show M.σ τ v (M.σ τ (v⁻¹ : Matrix.unitaryGroup (Fin V.rank) ℂ) x) = x
  rw [← ContinuousLinearMap.comp_apply, ← sigma_mul hp, ← Submonoid.coe_mul, mul_inv_cancel, OneMemClass.coe_one,
    sigma_one]
  rfl

theorem unfr_one (M : DSModel V S) (τ : D.what₂.Tau) : unfr M τ 1 = 1 := by
  unfold unfr
  rw [Matrix.mul_one, Matrix.nonsing_inv_mul _ (fr_det M τ)]

theorem pairEquiv_realAll : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S) (θ : InfFam D) (c : CoefA V) (pr : c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ), IsInfFam θ → GlobalTheory.DefLift.AllPlus M → c.Is → IsDualPair θ M c pr → ∃ E : c.W ≃ₗ[ℂ] Module.Dual ℂ (⨂[ℂ] τ, M.H τ), ∀ (u : UG D.what₂.Tau V.rank) (w : c.W), E (c.ρ (realAll θ V (fun τ => GlobalTheory.DefLift.unfr M τ (u τ))) w) = E w ∘ₗ PiTensorProduct.map (fun τ => ((M.σ τ ((u τ)⁻¹ : Matrix.unitaryGroup (Fin V.rank) ℂ) : M.H τ →L[ℂ] M.H τ) : M.H τ →ₗ[ℂ] M.H τ)) := by
  intro D V S M θ c pr hθ hp hc hpr
  classical
  have m := AllPlus.finite_smooth_irreducible D V S M hp
  obtain ⟨-, inj, π, hπ, -⟩ := tensor_irreducible D V S M m hp
  have key := pair_tens hp (fun τ => (m τ).2.1) inj hπ hpr
  have hb := pair_bijective hθ hp hc hpr
  let e : SmT M ≃ₗ[ℂ] ⨂[ℂ] τ, M.H τ := PiTensorProduct.congr fun τ => LinearEquiv.ofTop (M.sm τ) (m τ).2.1
  have he : ∀ x, e x = inclT M x := fun x => rfl
  let E : c.W ≃ₗ[ℂ] Module.Dual ℂ (⨂[ℂ] τ, M.H τ) := (LinearEquiv.ofBijective pr hb).trans e.symm.dualMap
  have hE : ∀ w y, E w y = pr w (e.symm y) := fun w y => rfl
  let F : ∀ τ, Matrix.unitaryGroup (Fin V.rank) ℂ → (M.H τ →ₗ[ℂ] M.H τ) := fun τ v =>
    ((M.σ τ v : M.H τ →L[ℂ] M.H τ) : M.H τ →ₗ[ℂ] M.H τ)
  have hact : ∀ τ (v : Matrix.unitaryGroup (Fin V.rank) ℂ), actT M τ (unfr M τ v) =
      PiTensorProduct.map (Function.update (fun ρ => (LinearMap.id : M.H ρ →ₗ[ℂ] M.H ρ)) τ (F τ v)) := by
    intro τ v
    unfold actT
    rw [rep_unfr]
  have hπe : ∀ τ v x, π τ v x = e.symm (actT M τ (unfr M τ v) (e x)) := fun τ v x => by
    apply e.injective
    rw [LinearEquiv.apply_symm_apply, he, he, hπ]
  have hinv : ∀ τ (v : Matrix.unitaryGroup (Fin V.rank) ℂ) x, π τ v (π τ v⁻¹ x) = x := by
    intro τ v x
    rw [hπe, hπe, LinearEquiv.apply_symm_apply, hact, hact, ← LinearMap.comp_apply (PiTensorProduct.map _),
      ← PiTensorProduct.map_comp]
    have : (fun ρ => Function.update (fun ρ => (LinearMap.id : M.H ρ →ₗ[ℂ] M.H ρ)) τ (F τ v) ρ ∘ₗ
        Function.update (fun ρ => (LinearMap.id : M.H ρ →ₗ[ℂ] M.H ρ)) τ (F τ v⁻¹) ρ) = fun ρ => LinearMap.id := by
      funext ρ
      by_cases h : ρ = τ
      · subst h
        simp only [Function.update_self]
        exact GlobalTheory.CoefPairTens.sigma_comp_inv hp ρ v
      · simp only [Function.update_of_ne h, LinearMap.id_comp]
    rw [this, PiTensorProduct.map_id, LinearMap.id_apply, LinearEquiv.symm_apply_apply]
  have one : ∀ τ (v : Matrix.unitaryGroup (Fin V.rank) ℂ) w,
      E (c.ρ (atTau θ V τ (unfr M τ v)) w) =
        E w ∘ₗ PiTensorProduct.map (Function.update (fun ρ => (LinearMap.id : M.H ρ →ₗ[ℂ] M.H ρ)) τ (F τ v⁻¹)) := by
    intro τ v w
    refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [LinearMap.comp_apply, hE, hE, ← hact, ← hπe, LinearEquiv.symm_apply_apply]
    have h1 := key τ v (c.ρ (atTau θ V τ (unfr M τ v)) w) (π τ v⁻¹ x)
    rw [hinv, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at h1
    exact h1
  refine ⟨E, fun u w => ?_⟩
  let us : Finset D.what₂.Tau → UG D.what₂.Tau V.rank := fun s ρ => if ρ ∈ s then u ρ else 1
  have hM : ∀ (s : Finset D.what₂.Tau) ρ, unfr M ρ (us s ρ) ∈ Formalism.QuantumDeterminants.UH (gramAt D V ρ) := fun s ρ =>
    hp.unfr_mem ρ _
  have ind : ∀ s : Finset D.what₂.Tau, ∀ w, E (c.ρ (realAll θ V (fun ρ => unfr M ρ (us s ρ))) w) =
      E w ∘ₗ PiTensorProduct.map (fun ρ => F ρ (us s ρ)⁻¹) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro w
      have h0 : (fun ρ => unfr M ρ (us ∅ ρ)) = 1 := by
        funext ρ
        have : us ∅ ρ = 1 := if_neg (Finset.notMem_empty ρ)
        rw [this, OneMemClass.coe_one, Pi.one_apply]
        exact GlobalTheory.CoefPairTens.unfr_one M ρ
      have h1 : (fun ρ => F ρ (us ∅ ρ)⁻¹) = fun ρ => LinearMap.id := by
        funext ρ
        have : us ∅ ρ = 1 := if_neg (Finset.notMem_empty ρ)
        show ((M.σ ρ ((us ∅ ρ)⁻¹ : Matrix.unitaryGroup (Fin V.rank) ℂ) : M.H ρ →L[ℂ] M.H ρ) : M.H ρ →ₗ[ℂ] M.H ρ) = _
        rw [this, inv_one, OneMemClass.coe_one, GlobalTheory.CoefPairTens.sigma_one]
        rfl
      rw [h0, realAll_one hθ, map_one, Module.End.one_apply, h1, PiTensorProduct.map_id, LinearMap.comp_id]
    | insert τ s hτ ih =>
      intro w
      have hs : us s τ = 1 := if_neg hτ
      have h3 : us (insert τ s) τ = u τ := if_pos (Finset.mem_insert_self τ s)
      have h4 : ∀ ρ, ρ ≠ τ → us (insert τ s) ρ = us s ρ := fun ρ h => by
        simp only [us, Finset.mem_insert, h, false_or]
      rw [realAll_eq_atTau_mul hθ (hM (insert τ s)) τ]
      have h2 : Function.update (fun ρ => unfr M ρ (us (insert τ s) ρ)) τ 1 = fun ρ => unfr M ρ (us s ρ) := by
        funext ρ
        by_cases h : ρ = τ
        · rw [h, Function.update_self, hs, OneMemClass.coe_one, GlobalTheory.CoefPairTens.unfr_one]
        · rw [Function.update_of_ne h, h4 ρ h]
      rw [h2, map_mul, Module.End.mul_apply, h3, one, ih, LinearMap.comp_assoc, ← PiTensorProduct.map_comp]
      congr 2
      funext ρ
      by_cases h : ρ = τ
      · subst h
        rw [Function.update_self, hs, h3]
        show ((M.σ ρ ((1 : Matrix.unitaryGroup (Fin V.rank) ℂ)⁻¹ : Matrix.unitaryGroup (Fin V.rank) ℂ) :
          M.H ρ →L[ℂ] M.H ρ) : M.H ρ →ₗ[ℂ] M.H ρ) ∘ₗ F ρ (u ρ)⁻¹ = F ρ (u ρ)⁻¹
        rw [inv_one, OneMemClass.coe_one, GlobalTheory.CoefPairTens.sigma_one]
        rfl
      · rw [Function.update_of_ne h, h4 ρ h, LinearMap.comp_id]
  have huniv : us Finset.univ = u := funext fun ρ => if_pos (Finset.mem_univ ρ)
  have := ind Finset.univ w
  rw [huniv] at this
  exact this

end GlobalTheory.CoefPairTens

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_multiplicitySpaceThetaMap_of_rapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.IsThPW → R.ex_ioP → R.ex_thF := by
  first | exact @GlobalTheory.DefLift.ThetaMap.ex_thF_of_weak | exact GlobalTheory.DefLift.ThetaMap.ex_thF_of_weak | (intros; apply GlobalTheory.DefLift.ThetaMap.ex_thF_of_weak <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_innerStepIntertwiners_thetaChain : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → HostHyp D → R.IsChainW → R.ex_ItY := by
  first | exact @GlobalTheory.Chain.ExItY.ex_ItY_holds | exact GlobalTheory.Chain.ExItY.ex_ItY_holds | (intros; apply GlobalTheory.Chain.ExItY.ex_ItY_holds <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.chainCompositeLift_intertwines_finiteGroupActions : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ F : Face D A, R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsChain → (∀ t j, j < D.R.m → SchurMult R.θ (R.MY j) (levS _ (R.βY j) (R.datYt t j R.triv)) (levChi _ (R.βY j) (R.datYt t j R.triv)) (R.νY t j) (R.fdY t j)) → ∀ t g κ, IsLevelLift D.sp.X' R.βX (R.datXt t) (R.eG g) κ → ∀ y y' : (R.HX t).H, (∀ h, (R.HX t).e y' h = (levChi _ R.βX (flagL (R.datXt t)) κ)⁻¹ • (R.HX t).e y (h * (finHom _).rangeRestrict κ)) → R.Th t y' = R.gE g (R.Th t y) := by
  first | exact @GlobalTheory.ChainLiftEquiv.th_intertwines | exact GlobalTheory.ChainLiftEquiv.th_intertwines | (intros; apply GlobalTheory.ChainLiftEquiv.th_intertwines <;> assumption)
end
