module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumBorelSphericalOverDiagonalDoubleCosetReps
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle006
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle033
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.QuotientMetricDivisors.Statement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle014
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.FinalAll
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle034
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle022
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.SharpRestriction.Divisibility.SchurIrreducible

@[expose] public section

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

theorem _root_.GlobalTheory.T.sum_borelSpherical_over_diagonalDoubleCosetReps : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (γ : Fin N → ℂ) (ψ : GL (Fin N) k → ℂ), IsBorelSph k γ ψ → (∀ i, γ i ≠ 0) → ∀ (s : Finset (Fin N)) (R : Finset (GL (Fin N) k)), IsRepsK (GlobalTheory.GLDoubling.torusElt k (Fin N) ϖ (indic s)) R → ∑ g ∈ R, ψ g = ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard s.card, ((resCard k : ℂ) ^ ((S ×ˢ Sᶜ).filter fun p : Fin N × Fin N => p.1 < p.2).card * ∏ a ∈ S, γ a) := by
  first | exact @GlobalTheory.BorelCosetSum.sum_cosets_eq | exact GlobalTheory.BorelCosetSum.sum_cosets_eq | (intros; apply GlobalTheory.BorelCosetSum.sum_cosets_eq <;> assumption)
end

section

namespace GlobalTheory.SymResCount

open Formalism.L2.DIV

theorem mem_unipSym_iff {K : Type} [CommRing K] {r : ℕ} (ρ κ : ℕ) (g : GL (Fin r) K) :
    g ∈ unipSym K r ρ κ ↔ ∀ a b : Fin r, ¬ (a.val < b.val ∧ ¬ (ρ ≤ a.val ∧ a.val < ρ + κ ∧ b.val = ρ + κ)) →
      (g : Matrix (Fin r) (Fin r) K) a b = (1 : Matrix (Fin r) (Fin r) K) a b := by
  constructor
  · rintro ⟨⟨hl, hd⟩, hc⟩ a b hab
    by_cases e : a = b
    · subst e; rw [hd a, Matrix.one_apply_eq]
    · rw [Matrix.one_apply_ne e]
      have hne : a.val ≠ b.val := fun h => e (Fin.ext h)
      by_cases h1 : b.val < a.val
      · exact hl (show b.val < a.val from h1)
      · exact hc a b (by omega) (by omega) (by omega)
  · intro h
    refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun i j h0 h1 h2 => ?_⟩
    · have hij' : j.val < i.val := hij
      rw [h i j (by omega), Matrix.one_apply_ne (fun e => by rw [e] at hij'; omega)]
    · rw [h i i (by omega), Matrix.one_apply_eq]
    · rw [h i j (by omega), Matrix.one_apply_ne (fun e => by rw [e] at h1; omega)]

def permFn (ρ κ i : ℕ) : ℕ := if i < κ then ρ + i else if i < κ + ρ then i - κ else i

def permInv (ρ κ a : ℕ) : ℕ := if a < ρ then κ + a else if a < ρ + κ then a - ρ else a

def perm (r ρ κ : ℕ) (hr : κ + ρ ≤ r) : Fin r ≃ Fin r where
  toFun i := ⟨permFn ρ κ i.val, by unfold permFn; split_ifs <;> omega⟩
  invFun a := ⟨permInv ρ κ a.val, by unfold permInv; split_ifs <;> omega⟩
  left_inv i := by
    apply Fin.ext; simp only; unfold permFn permInv; split_ifs <;> omega
  right_inv a := by
    apply Fin.ext; simp only; unfold permFn permInv; split_ifs <;> omega

theorem perm_val {r ρ κ : ℕ} (hr : κ + ρ ≤ r) (i : Fin r) : (perm r ρ κ hr i).val = permFn ρ κ i.val := rfl

theorem freePos_iff (ρ κ i j : ℕ) :
    GlobalTheory.SymRes.FreePos ρ κ i j ↔ (permFn ρ κ i < permFn ρ κ j ∧
      ¬ (ρ ≤ permFn ρ κ i ∧ permFn ρ κ i < ρ + κ ∧ permFn ρ κ j = ρ + κ)) := by
  unfold GlobalTheory.SymRes.FreePos permFn; split_ifs <;> omega

def reidx {K : Type} [CommRing K] (r ρ κ : ℕ) (hr : κ + ρ ≤ r) : GL (Fin r) K ≃* GL (Fin r) K :=
  Units.mapEquiv (Matrix.reindexAlgEquiv K K (perm r ρ κ hr)).toMulEquiv

theorem reidx_apply {K : Type} [CommRing K] {r ρ κ : ℕ} (hr : κ + ρ ≤ r) (g : GL (Fin r) K) (i j : Fin r) :
    ((reidx r ρ κ hr g : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) (perm r ρ κ hr i) (perm r ρ κ hr j) =
      (g : Matrix (Fin r) (Fin r) K) i j := by
  simp [reidx, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply]

theorem reidx_mem_iff {K : Type} [CommRing K] {r ρ κ : ℕ} (hr : κ + ρ ≤ r) (g : GL (Fin r) K) :
    reidx r ρ κ hr g ∈ unipSym K r ρ κ ↔ GlobalTheory.SymRes.IsPat ρ κ g := by
  rw [mem_unipSym_iff]
  constructor
  · intro h i j hf
    have := h (perm r ρ κ hr i) (perm r ρ κ hr j) (by rw [perm_val, perm_val, ← freePos_iff]; exact hf)
    rw [reidx_apply] at this
    rw [this]
    by_cases e : i = j
    · subst e; simp
    · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne (fun e' => e ((perm r ρ κ hr).injective e'))]
  · intro h a b hab
    obtain ⟨i, rfl⟩ := (perm r ρ κ hr).surjective a
    obtain ⟨j, rfl⟩ := (perm r ρ κ hr).surjective b
    rw [reidx_apply, h i j (by rw [freePos_iff, ← perm_val hr, ← perm_val hr]; exact hab)]
    by_cases e : i = j
    · subst e; simp
    · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne (fun e' => e ((perm r ρ κ hr).injective e'))]

end GlobalTheory.SymResCount

namespace GlobalTheory.SymResCount
open Formalism.L2.DIV

theorem conj_pat_onto : ∀ (K : Type) [CommRing K] [Finite K] (r ρ κ : ℕ), r = κ + (2 * ρ + 1) →
    ∀ m : GL (Fin r) K, (∀ g : GL (Fin r) K, GlobalTheory.SymRes.IsPat ρ κ g → m * g * m⁻¹ ∈ Formalism.L2.DIV.unipSym K r ρ κ) →
    ∀ g : GL (Fin r) K, m * g * m⁻¹ ∈ Formalism.L2.DIV.unipSym K r ρ κ → GlobalTheory.SymRes.IsPat ρ κ g := by
  intro K _ _ r ρ κ hr m hm g hg
  have hr' : κ + ρ ≤ r := by omega
  haveI : Finite (GL (Fin r) K) := Finite.of_injective (fun u : GL (Fin r) K => (u : Matrix (Fin r) (Fin r) K)) Units.val_injective
  set S : Set (GL (Fin r) K) := {g | GlobalTheory.SymRes.IsPat ρ κ g} with hS
  set U : Set (GL (Fin r) K) := (unipSym K r ρ κ : Set (GL (Fin r) K)) with hU
  have hSU : (reidx (K := K) r ρ κ hr') '' S = U := by
    ext h
    constructor
    · rintro ⟨x, hx, rfl⟩; exact (reidx_mem_iff hr' x).2 hx
    · intro hh
      refine ⟨(reidx r ρ κ hr').symm h, (reidx_mem_iff hr' _).1 (by rw [MulEquiv.apply_symm_apply]; exact hh), by simp⟩
  have hinj : Function.Injective (fun x : GL (Fin r) K => m * x * m⁻¹) := fun x y h =>
    mul_left_cancel (mul_right_cancel h)
  have hc : (fun x : GL (Fin r) K => m * x * m⁻¹) '' S = U := by
    apply Set.eq_of_subset_of_ncard_le
    · rintro _ ⟨x, hx, rfl⟩; exact hm x hx
    · rw [Set.ncard_image_of_injective S hinj, ← hSU, Set.ncard_image_of_injective S (reidx r ρ κ hr').injective]
    · exact Set.toFinite U
  have hg' : m * g * m⁻¹ ∈ U := hg
  rw [← hc] at hg'
  obtain ⟨x, hx, he⟩ := hg'
  have : x = g := hinj he
  rw [← this]; exact hx

end GlobalTheory.SymResCount
end

section

open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling


theorem _root_.GlobalTheory.T.hecke_series_cell_has_sum : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (e : Fin n → ℤ), ∀ g ∈ cell k (Fin n) ϖ e, ∀ X : ℂ, (∀ i : Fin n, ‖(resCard k : ℂ) ^ (i : ℕ) * X ^ 2‖ < 1) → HasSum (fun h : {h : GL (Fin n) k ⧸ KO k (Fin n) // (∀ i j, (h.out⁻¹ : GL (Fin n) k).1 i j ∈ 𝒪[k]) ∧ (∀ i j, (h.out⁻¹ * g : GL (Fin n) k).1 i j ∈ 𝒪[k])} => X ^ ((-ord k (Matrix.GeneralLinearGroup.det h.1.out)).toNat + (ord k (Matrix.GeneralLinearGroup.det (h.1.out⁻¹ * g))).toNat)) (X ^ (∑ i, |e i|).toNat * ∏ i : Fin n, (1 - (resCard k : ℂ) ^ (i : ℕ) * X ^ 2)⁻¹) := by
  first | exact @GlobalTheory.LatticePair.hasSum_pair | exact GlobalTheory.LatticePair.hasSum_pair | (intros; apply GlobalTheory.LatticePair.hasSum_pair <;> assumption)
end

section

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Forms
open scoped Matrix ComplexOrder

namespace GlobalTheory

theorem ptField_main : ∀ D : D7, IsTotallyComplex D.what₂.LL ∧ (∃ v0 : InfinitePlace D.what₂.LL, Formalism.DivisionValues.IsConjAt v0) ∧ ∀ (u : D.what₂.Word) (c : (D.fm u).clsP), Nat.card ((D.fm u).stabilizer₂ c) ∣ (D.mem u).C.DGam := by
  intro D
  refine ⟨D.tcLL, GlobalTheory.isConjAt_exists_main D.what₂.LL ⟨D.what₂.embLL, D.starLL_cx⟩, ?_⟩
  intro u c
  exact (Subgroup.card_dvd_of_injective _ ((D.fm u).stabMap_inj c)).trans
    ((D.mem u).C.dvd_DGam _ le_rfl _)

end GlobalTheory
end

section

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Forms
open scoped Matrix ComplexOrder

namespace GlobalTheory.Core.CoefGram

theorem posDef_of_hasSignature {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (h : Formalism.UG.HasSignature G n 0) : G.PosDef := by
  obtain ⟨e, P, hP⟩ := h
  have hJ : Formalism.UG.Jpq n 0 = 1 := by
    ext i j
    rcases i with i | i
    · rcases j with j | j
      · simp [Formalism.UG.Jpq, Matrix.one_apply]
      · exact j.elim0
    · exact i.elim0
  have hcT : Formalism.UG.cT (starRingEnd ℂ) P.val = P.valᴴ := by
    ext i j; simp [Formalism.UG.cT, Matrix.conjTranspose_apply]
  rw [hcT, hJ] at hP
  have h1 : (P.valᴴ * G.reindex e e * P.val).PosDef := by rw [hP]; exact Matrix.PosDef.one
  have h2 : (G.reindex e e).PosDef := (Matrix.IsUnit.posDef_star_left_conjugate_iff P.isUnit).1 h1
  have h3 : G = (G.reindex e e).submatrix e e := by ext i j; simp
  rw [h3]
  exact h2.submatrix e.injective

end GlobalTheory.Core.CoefGram
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)
open scoped InnerProductSpace

namespace GlobalTheory.AdmUnitary

theorem admissible_and_kFin_smooth : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → (∀ S : Submodule ℂ H, FiniteDimensional ℂ S → IsKStableOn ε σ S → ∀ v ∈ S, ∃ Y : Submodule ℂ H, FiniteDimensional ℂ Y ∧ v ∈ Y ∧ ∀ B : H →L[ℂ] H, (∀ k ∈ Formalism.REAL.Kset ε, ∀ u, B (σ k u) = σ k (B u)) → ∀ y ∈ Y, B y ∈ Y) ∧ ∀ v, IsKFin ε σ v → Formalism.QuantumDeterminants.SmoothOnH (Formalism.REAL.Jm ε) (fun g => σ g v) := by
  intro n ε H _ _ _ σ hσ hirr
  refine ⟨fun S hS hst v hv => ?_, fun v hv => CompanionTheory.D.gk.admitted.kFin_smooth n ε H σ hσ hirr v hv⟩
  obtain ⟨Y, hY, -, hvY, hT⟩ := CompanionTheory.D.gk.admitted.unitary_group_admissible n ε H σ hσ hirr S hst v hv
  exact ⟨Y, hY, hvY, hT⟩

end GlobalTheory.AdmUnitary
end

section

open Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory

theorem finrank_ker_le_hsNormSq_sub_id {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (K : V →L[ℂ] V) (N : Submodule ℂ V) (hN : ∀ x ∈ N, K x = 0) :
    (Module.finrank ℂ N : ℝ) ≤ hsNormSq (K - ContinuousLinearMap.id ℂ V) := by
  let b := stdOrthonormalBasis ℂ N
  let v : Fin (Module.finrank ℂ N) → V := fun i => (b i : V)
  have hv : Orthonormal ℂ v := b.orthonormal.comp_linearIsometry N.subtypeₗᵢ
  have h := GlobalTheory.T.sum_norm_sq_orthonormal_le_hilbertSchmidt (K - ContinuousLinearMap.id ℂ V) v hv
  have hterm : ∀ i, ‖(K - ContinuousLinearMap.id ℂ V) (v i)‖ ^ 2 = 1 := by
    intro i
    have hK : K (v i) = 0 := hN _ (b i).2
    have hn : ‖v i‖ = 1 := hv.1 i
    simp [hK, hn]
  have hsum : ∑ i, ‖(K - ContinuousLinearMap.id ℂ V) (v i)‖ ^ 2 = (Module.finrank ℂ N : ℝ) := by
    rw [Finset.sum_congr rfl (fun i _ => hterm i)]
    simp
  rw [hsum] at h
  exact h

end GlobalTheory
end
