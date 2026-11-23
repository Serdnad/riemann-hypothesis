module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle001
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle003
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle004
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HasProdQuadExtLocalEulerFactorInvInv
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.IsSemiChar
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle026
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle004
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow
public import Mathlib.Analysis.Analytic.Order
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle038
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DifferentiableOddTheta
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle037
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle025
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.DataN

@[expose] public section

section

open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal

theorem _root_.GlobalTheory.T.quotientMeasure_normalised_by_haar_unique : NormaliseQuotientClause := by
  first | exact @GlobalTheory.Proof.quotientMeasure_normalised_by_haar_unique.normaliseQuotientClause | exact GlobalTheory.Proof.quotientMeasure_normalised_by_haar_unique.normaliseQuotientClause | (intros; apply GlobalTheory.Proof.quotientMeasure_normalised_by_haar_unique.normaliseQuotientClause <;> assumption)
end

section


theorem _root_.GlobalTheory.T.selfDual_lattices_unramified_place_no_hypothesis : GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions.SelfDualLatticeLemmas := by
  first | exact @GlobalTheory.UnramSelfDualClosed.selfDualLatticeLemmas | exact GlobalTheory.UnramSelfDualClosed.selfDualLatticeLemmas | (intros; apply GlobalTheory.UnramSelfDualClosed.selfDualLatticeLemmas <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex

theorem _root_.GlobalTheory.T.hasProd_quadExtLocalEulerFactorInv_inv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (σ : E →ₐ[F] E), IsCMExt F E σ → (∀ x : E, star x = σ x) → Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ M : ℕ, 2 ≤ M → 0 < Formalism.HermitianLatticesTheory.lValEta E M ∧ HasProd (fun v => (eulerInv F E M v)⁻¹) (Formalism.HermitianLatticesTheory.lValEta E M) := by
  first | exact @GlobalTheory.EtaEulerProduct.hasProd_eulerInv_inv | exact GlobalTheory.EtaEulerProduct.hasProd_eulerInv_inv | (intros; apply GlobalTheory.EtaEulerProduct.hasProd_eulerInv_inv <;> assumption)
end

section

open GlobalTheory.MomN Formalism.L2.Th1.H

noncomputable section

namespace GlobalTheory.MomRoot

theorem mahler_comp_clm (E V : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup V] [NormedSpace ℂ V]
    (κ : Type) [Fintype κ] (L : E →L[ℂ] V) (u : κ → E) (G : V → ℂ) (hG : ContDiff ℂ ⊤ G) (k : κ → ℕ) :
    mahler u (fun z => G (L z)) k = mahler (fun i => L (u i)) G k := by
  unfold GlobalTheory.MomN.mahler
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  unfold GlobalTheory.MomN.monoJet
  have h := L.iteratedFDeriv_comp_right hG (0 : E) (i := m.toMultiset.toList.length) le_top
  change iteratedFDeriv ℂ _ (G ∘ L) 0 _ = _
  rw [h, ContinuousMultilinearMap.compContinuousLinearMap_apply, map_zero]

theorem mahler_embed (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (κ ι' : Type) [Fintype κ] [Fintype ι']
    (e : κ ↪ ι') (w : κ → V) (u : ι' → V) (G : V → ℂ) (hG : ContDiff ℂ ⊤ G)
    (hu : ∀ i, u (e i) = w i) (hz : ∀ p, p ∉ Set.range e → u p = 0) :
    (∀ k : ι' → ℕ, (∃ p, p ∉ Set.range e ∧ k p ≠ 0) → mahler u G k = 0) ∧
    (∀ k : ι' → ℕ, (∀ p, p ∉ Set.range e → k p = 0) → mahler u G k = mahler w G (fun i => k (e i))) :=
  GlobalTheory.T.mahlerJetCoefficient_of_family_zero_off_embedding V κ ι' e w u G hG hu hz

theorem mahler_mul_disj (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (ι' : Type) [Fintype ι'] [DecidableEq ι']
    (u : ι' → V) (F H : V → ℂ) (hF : ContDiff ℂ ⊤ F) (hH : ContDiff ℂ ⊤ H) (S T : Finset ι') (hST : Disjoint S T)
    (hFS : ∀ k : ι' → ℕ, (∃ p, p ∉ S ∧ k p ≠ 0) → mahler u F k = 0)
    (hHT : ∀ k : ι' → ℕ, (∃ p, p ∉ T ∧ k p ≠ 0) → mahler u H k = 0) :
    (∀ N : ι' → ℕ, (∃ p, p ∉ S ∪ T ∧ N p ≠ 0) → mahler u (fun z => F z * H z) N = 0) ∧
    (∀ N : ι' → ℕ, (∀ p, p ∉ S ∪ T → N p = 0) → mahler u (fun z => F z * H z) N =
      mahler u F (fun p => if p ∈ S then N p else 0) * mahler u H (fun p => if p ∈ T then N p else 0)) :=
  GlobalTheory.T.mahlerJetCoefficient_mul_of_disjoint_support V ι' u F H hF hH S T hST hFS hHT

variable {n : Type} [Fintype n]

def sliceL (a : Fin 4) : (Fin 4 × n → ℂ) →L[ℂ] (n → ℂ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (a, i)

theorem sliceL_apply (a : Fin 4) (z : Fin 4 × n → ℂ) : sliceL a z = slice a z := rfl

def fourBlockInclusionVector (b : Fin 4) (x : n → ℂ) : Fin 4 × n → ℂ := fun z => if z.1 = b then x z.2 else 0

theorem slice_fourBlockInclusionVector (a b : Fin 4) (x : n → ℂ) : slice a (fourBlockInclusionVector b x) = if a = b then x else 0 := by
  funext i; by_cases h : a = b <;> simp [slice, fourBlockInclusionVector, h]

end GlobalTheory.MomRoot

namespace GlobalTheory.MomRoot

theorem jets_root : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (n : Type) [Fintype n] (ω : ℂ_[q]) (Λ : AddSubgroup (n → ℂ))
    (G : (n → ℂ) → ℂ), ContDiff ℂ ⊤ G → LatInt ι ω (pow4 Λ) (tens4 G) → LatInt ι ω Λ G := by
  intro q _ ι n _ ω Λ G hG hL κ _ v hv
  classical
  set c := ι.symm ω
  rw [GlobalTheory.T.mahlerCoefficient_norm_le_one_iff_jets_boundedMeasureMoments q ι (n → ℂ) κ _ G hG]
  intro m
  let U : Fin 4 × κ → (Fin 4 × n → ℂ) := fun p => c • fourBlockInclusionVector p.1 (v p.2)
  have hU : MomInt ι U (tens4 G) := hL (Fin 4 × κ) (fun p => fourBlockInclusionVector p.1 (v p.2)) (fun p a => by
    show slice a (fourBlockInclusionVector p.1 (v p.2)) ∈ Λ
    rw [slice_fourBlockInclusionVector]; split_ifs
    · exact hv _
    · exact Λ.zero_mem)
  have hGa : ∀ a, ContDiff ℂ ⊤ (fun z => G (slice a z)) := fun a => by
    have h : ContDiff ℂ ⊤ (sliceL (n := n) a) := ContinuousLinearMap.contDiff _
    exact hG.comp h
  have ht : tens4 G = fun z => G (slice 0 z) * G (slice 1 z) * G (slice 2 z) * G (slice 3 z) := by
    funext z; simp [tens4, Fin.prod_univ_four]
  have hcd : ContDiff ℂ ⊤ (tens4 G) := by
    rw [ht]; exact (((hGa 0).mul (hGa 1)).mul (hGa 2)).mul (hGa 3)
  have hb := ((GlobalTheory.T.mahlerCoefficient_norm_le_one_iff_jets_boundedMeasureMoments q ι _ _ U (tens4 G) hcd).1 hU) (fun p => m p.2)
  let S : Fin 4 → Finset (Fin 4 × κ) := fun a => Finset.univ.filter (fun p => p.1 = a)
  let e : Fin 4 → κ ↪ Fin 4 × κ := fun a => ⟨fun i => (a, i), fun i j h => (Prod.mk.inj h).2⟩
  have hposition : ∀ a, (∀ k : Fin 4 × κ → ℕ, (∃ p, p ∉ S a ∧ k p ≠ 0) → mahler U (fun z => G (slice a z)) k = 0) ∧
      (∀ k : Fin 4 × κ → ℕ, (∀ p, p ∉ S a → k p = 0) →
        mahler U (fun z => G (slice a z)) k = mahler (fun i => c • v i) G (fun i => k (a, i))) := by
    intro a
    have he : ∀ i, e a i = (a, i) := fun _ => rfl
    have hcomp : ∀ k, mahler U (fun z => G (slice a z)) k = mahler (fun p => sliceL a (U p)) G k :=
      fun k => by
        have h := mahler_comp_clm _ _ _ (sliceL a) U G hG k
        simp only [sliceL_apply] at h
        exact h
    have hrange : ∀ p : Fin 4 × κ, p ∈ Set.range (e a) ↔ p ∈ S a := by
      rintro ⟨b, i⟩; simp [Set.mem_range, he, S, eq_comm]
    obtain ⟨h1, h2⟩ := mahler_embed (n → ℂ) κ (Fin 4 × κ) (e a) (fun i => c • v i) (fun p => sliceL a (U p)) G hG
      (fun i => by simp [U, he, sliceL_apply, slice_fourBlockInclusionVector])
      (fun p hp => by
        have : p.1 ≠ a := fun h => hp ((hrange p).2 (by simp [S, h]))
        simp [U, sliceL_apply, slice_fourBlockInclusionVector, Ne.symm this])
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · rw [hcomp]; obtain ⟨p, hp, hk⟩ := hk; exact h1 k ⟨p, by rwa [hrange], hk⟩
    · rw [hcomp]; exact h2 k (fun p hp => hk p (by rwa [← hrange]))
  have dj : ∀ (A : Finset (Fin 4)) (b : Fin 4), b ∉ A → Disjoint (A.biUnion S) (S b) := by
    intro A b hb
    rw [Finset.disjoint_left]; intro p hp hq
    simp only [Finset.mem_biUnion, S, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    obtain ⟨a, ha, rfl⟩ := hp; exact hb (hq ▸ ha)
  have u1 : ({0} : Finset (Fin 4)).biUnion S = S 0 := by simp
  have u2 : ({0, 1} : Finset (Fin 4)).biUnion S = S 0 ∪ S 1 := by simp [Finset.biUnion_insert]
  have u3 : ({0, 1, 2} : Finset (Fin 4)).biUnion S = S 0 ∪ S 1 ∪ S 2 := by
    simp [Finset.biUnion_insert, Finset.union_assoc]
  have d1 := dj {0} 1 (by decide)
  have d2 := dj {0, 1} 2 (by decide)
  have d3 := dj {0, 1, 2} 3 (by decide)
  rw [u1] at d1; rw [u2] at d2; rw [u3] at d3
  obtain ⟨A1v, A1⟩ := mahler_mul_disj _ _ U _ _ (hGa 0) (hGa 1) (S 0) (S 1) d1 (hposition 0).1 (hposition 1).1
  obtain ⟨A2v, A2⟩ := mahler_mul_disj _ _ U _ _ ((hGa 0).mul (hGa 1)) (hGa 2) (S 0 ∪ S 1) (S 2) d2 A1v (hposition 2).1
  obtain ⟨-, A3⟩ := mahler_mul_disj _ _ U _ _ (((hGa 0).mul (hGa 1)).mul (hGa 2)) (hGa 3)
    (S 0 ∪ S 1 ∪ S 2) (S 3) d3 A2v (hposition 3).1
  have key : mahler U (tens4 G) (fun p => m p.2) = (mahler (fun i => c • v i) G m) ^ 4 := by
    rw [ht, A3 _ ?_, A2 _ ?_, A1 _ ?_, (hposition 0).2 _ ?_, (hposition 1).2 _ ?_, (hposition 2).2 _ ?_, (hposition 3).2 _ ?_]
    · simp only [S, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      norm_num
      ring
    all_goals
      intro p hp
      rcases p with ⟨b, i⟩
      simp only [S, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      fin_cases b <;> simp at hp ⊢
  rw [key, map_pow, norm_pow] at hb
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 hb
end GlobalTheory.MomRoot
end
end

section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

noncomputable section

namespace GlobalTheory.Alc

def hwRowSum (R : Type) [CommRing R] {N : ℕ} (μ : Fin N → R) (k : ℕ) (i : Fin N) : R :=
  ∑ l, (hcMat R μ ^ k) i l

theorem hwRowSum_zero (R : Type) [CommRing R] {N : ℕ} (μ : Fin N → R) (i : Fin N) :
    hwRowSum R μ 0 i = 1 := by
  simp [hwRowSum, Matrix.one_apply]

theorem hwRowSum_succ_eq_mul (R : Type) [CommRing R] {N : ℕ} (μ : Fin N → R) (k : ℕ) (i : Fin N) :
    hwRowSum R μ (k + 1) i = ∑ m, hcMat R μ i m * hwRowSum R μ k m := by
  simp only [hwRowSum, pow_succ', Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_comm

theorem hwRowSum_succ (R : Type) [CommRing R] {N : ℕ} (μ : Fin N → R) (k : ℕ) (i : Fin N) :
    hwRowSum R μ (k + 1) i =
      ∑ l, (if l < i then 0 else if l = i then μ i * hwRowSum R μ k i
        else hwRowSum R μ k i - hwRowSum R μ k l) := by
  rw [hwRowSum_succ_eq_mul]
  set r := hwRowSum R μ k with hr
  have h1 : ∀ l, hcMat R μ i l * r l =
      (if l = i then μ i * r i else 0) + (if l = i then ((N - 1 - i.val : ℕ) : R) * r i else 0)
        - (if i < l then r l else 0) := by
    intro l
    by_cases hl : l = i
    · subst hl
      simp [hcMat, shift, add_mul]
    · by_cases hil : i < l
      · simp [hcMat, hl, hil]
      · simp [hcMat, hl, hil]
  have h2 : ∀ l, (if l < i then 0 else if l = i then μ i * r i else r i - r l) =
      (if l = i then μ i * r i else 0) + (if i < l then r i else 0)
        - (if i < l then r l else 0) := by
    intro l
    rcases lt_trichotomy l i with h | h | h
    · simp [h, h.ne, h.not_gt]
    · subst h
      simp
    · simp [h, h.ne', h.not_gt]
  simp only [h1, h2, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  congr 2
  have h3 : ∑ l : Fin N, (if i < l then r i else 0) = ((N - 1 - i.val : ℕ) : R) * r i := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    congr 2
    have : Finset.univ.filter (fun l : Fin N => i < l) = Finset.Ioi i := by
      ext l
      simp
    rw [this, Fin.card_Ioi]
  rw [h3]
  simp

theorem pow_entry_stable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {N : ℕ}
    (E : Matrix (Fin N) (Fin N) (Module.End R V)) (M : Submodule R V)
    (hM : ∀ a b, ∀ f ∈ M, E a b f ∈ M) (k : ℕ) :
    ∀ a b, ∀ f ∈ M, (E ^ k) a b f ∈ M := by
  induction k with
  | zero =>
    intro a b f hf
    by_cases h : a = b
    · subst h
      simpa [Matrix.one_apply] using hf
    · simp [Matrix.one_apply, h]
  | succ k ih =>
    intro a b f hf
    rw [pow_succ', Matrix.mul_apply, LinearMap.sum_apply]
    exact Submodule.sum_mem _ fun l _ => hM a l _ (ih l b f hf)

theorem hw_pow_entries {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {N : ℕ}
    (E : Matrix (Fin N) (Fin N) (Module.End R V)) (hE : GlRel E) (M : Submodule R V)
    (hM : ∀ a b, ∀ f ∈ M, E a b f ∈ M) (μ : Fin N → R) (v : V)
    (hup : ∀ a b, a < b → E a b v ∈ M) (hd : ∀ a, E a a v - μ a • v ∈ M) (k : ℕ) :
    (∀ i j, i < j → (E ^ k) i j v ∈ M) ∧ (∀ i, (E ^ k) i i v - hwRowSum R μ k i • v ∈ M) := by
  induction k with
  | zero =>
    constructor
    · intro i j hij
      simp [Matrix.one_apply, hij.ne]
    · intro i
      simp [hwRowSum_zero, Matrix.one_apply]
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hcomm := (GlobalTheory.T.glMatrixUnit_pow_commutator_and_trace_central (Module.End R V) N E hE k).1
    have hst := pow_entry_stable E M hM k
    have key : ∀ i j l, i < l →
        E i l ((E ^ k) l j v) - ((E ^ k) i j v - (if j = i then (E ^ k) l l v else 0)) ∈ M := by
      intro i j l hil
      have h := LinearMap.congr_fun (hcomm i l l j) v
      have h' : E i l ((E ^ k) l j v) - (E ^ k) l j (E i l v) =
          (E ^ k) i j v - (if j = i then (E ^ k) l l v else 0) := by
        by_cases hji : j = i
        · simpa [hji, Module.End.mul_apply] using h
        · simpa [hji, Module.End.mul_apply] using h
      have h2 : (E ^ k) l j (E i l v) ∈ M := hst l j _ (hup i l hil)
      rw [← h']
      simpa using h2
    constructor
    · intro i j hij
      rw [pow_succ', Matrix.mul_apply, LinearMap.sum_apply]
      refine Submodule.sum_mem _ fun l _ => ?_
      rw [Module.End.mul_apply]
      rcases lt_trichotomy l j with h | h | h
      · exact hM i l _ (ih1 l j h)
      · subst h
        have h1 := hM i l _ (ih2 l)
        rw [map_sub, map_smul] at h1
        have h2 := M.smul_mem (hwRowSum R μ k l) (hup i l hij)
        simpa using M.add_mem h1 h2
      · have h1 := key i j l (hij.trans h)
        rw [if_neg hij.ne'] at h1
        simpa using M.add_mem h1 (ih1 i j hij)
    · intro i
      rw [pow_succ', Matrix.mul_apply, LinearMap.sum_apply, hwRowSum_succ, Finset.sum_smul,
        ← Finset.sum_sub_distrib]
      refine Submodule.sum_mem _ fun l _ => ?_
      rw [Module.End.mul_apply]
      rcases lt_trichotomy l i with h | h | h
      · simpa [h] using hM i l _ (ih1 l i h)
      · subst h
        have h1 := hM l l _ (ih2 l)
        rw [map_sub, map_smul] at h1
        have h2 := M.smul_mem (hwRowSum R μ k l) (hd l)
        have h3 := M.add_mem h1 h2
        have e : E l l ((E ^ k) l l v) - hwRowSum R μ k l • E l l v +
            hwRowSum R μ k l • (E l l v - μ l • v) =
            E l l ((E ^ k) l l v) - (μ l * hwRowSum R μ k l) • v := by
          rw [smul_sub, smul_smul, mul_comm (hwRowSum R μ k l)]
          abel
        rw [e] at h3
        simpa using h3
      · have h1 := key i i l h
        rw [if_pos rfl] at h1
        have h3 := M.sub_mem (M.add_mem h1 (ih2 i)) (ih2 l)
        have e : E i l ((E ^ k) l i v) - ((E ^ k) i i v - (E ^ k) l l v) +
            ((E ^ k) i i v - hwRowSum R μ k i • v) - ((E ^ k) l l v - hwRowSum R μ k l • v) =
            E i l ((E ^ k) l i v) - (hwRowSum R μ k i - hwRowSum R μ k l) • v := by
          rw [sub_smul]
          abel
        rw [e] at h3
        simpa [h.not_gt, h.ne'] using h3

theorem trace_pow_hw : ∀ (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] (N : ℕ)
    (E : Matrix (Fin N) (Fin N) (Module.End R V)), GlRel E → ∀ (M : Submodule R V),
    (∀ a b, ∀ f ∈ M, E a b f ∈ M) → ∀ (μ : Fin N → R) (v : V), (∀ a b, a < b → E a b v ∈ M) →
    (∀ a, E a a v - μ a • v ∈ M) → ∀ k : ℕ, (E ^ k).trace v - hcVal R μ k • v ∈ M := by
  intro R V _ _ _ N E hE M hM μ v hup hd k
  have h := (hw_pow_entries E hE M hM μ v hup hd k).2
  have e : (E ^ k).trace v - hcVal R μ k • v = ∑ i, ((E ^ k) i i v - hwRowSum R μ k i • v) := by
    simp only [Matrix.trace, Matrix.diag, LinearMap.sum_apply, hcVal, Finset.sum_sub_distrib,
      Finset.sum_smul, hwRowSum]
  rw [e]
  exact Submodule.sum_mem _ fun i _ => h i

end GlobalTheory.Alc
end
end

section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

theorem _root_.GlobalTheory.T.eq_weights_of_traceEPowerHighestWeightValue_eq : ∀ (p : ℕ), p.Prime → ∀ (k : Type) [Field k] [CharP k p] (N : ℕ) (ν μ : Fin N → ℕ), Antitone ν → Antitone μ → (∀ h : 0 < N, ν ⟨N - 1, by omega⟩ = 0 ∧ μ ⟨0, h⟩ ≤ ν ⟨0, h⟩ ∧ ν ⟨0, h⟩ + (N - 1) ≤ p) → (∀ j, hcVal k (fun i => (μ i : k)) j = hcVal k (fun i => (ν i : k)) j) → μ = ν := by
  first | exact @GlobalTheory.Alc.eq_of_hcVal_eq | exact GlobalTheory.Alc.eq_of_hcVal_eq | (intros; apply GlobalTheory.Alc.eq_of_hcVal_eq <;> assumption)
end

section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

theorem _root_.GlobalTheory.T.exists_dominant_highest_vector_of_lt_stable : ∀ (k : Type) [Field k] (N : ℕ) (M M' : Submodule k (MvPolynomial (Fin N × Fin N) k)), Good M → Good M' → M < M' → (∃ c : ℕ, ∀ f ∈ M', ∀ m ∈ f.support, ∑ a, rowDeg m a ≤ c) → ∃ (μ : Fin N → ℕ) (v : MvPolynomial (Fin N × Fin N) k), Antitone μ ∧ v ∈ M' ∧ v ∉ M ∧ IsWeightedHomogeneous (rowW N N) v μ ∧ ∀ a b, a < b → rowE k N N a b v ∈ M := by
  first | exact @GlobalTheory.Alc.exists_dominant_highest_vector_of_lt | exact GlobalTheory.Alc.exists_dominant_highest_vector_of_lt | (intros; apply GlobalTheory.Alc.exists_dominant_highest_vector_of_lt <;> assumption)
end

section

open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

theorem _root_.GlobalTheory.T.exists_rayClassLFunction_real_zero_far_from_one : ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (β : ℝ), χ * χ = 1 → 3 / 4 ≤ β → 𝓕.F χ β = 0 → c / 𝓕.B ^ A ≤ 1 - β := by
  first | exact @GlobalTheory.Hk.LFam.real_zero_far_from_one | exact GlobalTheory.Hk.LFam.real_zero_far_from_one | (intros; apply GlobalTheory.Hk.LFam.real_zero_far_from_one <;> assumption)
end

section

open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

theorem _root_.GlobalTheory.T.rayClassLFunction_logDeriv_local_formula : ∃ C : ℝ, 0 < C ∧ ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (t : ℝ), {w : ℂ | ‖w - (5 / 4 + t * I)‖ ≤ 3 / 5 ∧ 𝓕.F χ w = 0}.Finite ∧ (∑ᶠ w ∈ {w : ℂ | ‖w - (5 / 4 + t * I)‖ ≤ 3 / 5 ∧ 𝓕.F χ w = 0}, (analyticOrderNatAt (𝓕.F χ) w : ℝ)) ≤ C * 𝓕.ell t ∧ ∀ s : ℂ, ‖s - (5 / 4 + t * I)‖ ≤ 1 / 2 → 𝓕.F χ s ≠ 0 → ‖deriv (𝓕.F χ) s / 𝓕.F χ s - ∑ᶠ w ∈ {w : ℂ | ‖w - (5 / 4 + t * I)‖ ≤ 3 / 5 ∧ 𝓕.F χ w = 0}, (analyticOrderNatAt (𝓕.F χ) w : ℂ) / (s - w)‖ ≤ C * 𝓕.ell t := by
  first | exact @GlobalTheory.HkLocal.logDeriv_local | exact GlobalTheory.HkLocal.logDeriv_local | (intros; apply GlobalTheory.HkLocal.logDeriv_local <;> assumption)
end

section

open Complex

theorem _root_.GlobalTheory.T.jacobiTripleProduct_twoVariableTheta : GlobalTheory.ThetaWeberRoad.TripleProduct := by
  first | exact @GlobalTheory.JacobiTriple.tripleProduct | exact GlobalTheory.JacobiTriple.tripleProduct | (intros; apply GlobalTheory.JacobiTriple.tripleProduct <;> assumption)
end

section

open Formalism.MainNotions.N

namespace GlobalTheory

theorem linearIndependent_conj_eigenmatrices {Γ k ι : Type} [Group Γ] [Field k] {n : ℕ}
    (r : Γ →* GL (Fin n) k) (ψ : ι → Γ →* k) (hψ : Function.Injective ψ)
    (X : ι → Matrix (Fin n) (Fin n) k) (hX : ∀ i, X i ≠ 0)
    (h : ∀ i g, ((r g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X i =
      ψ i g • (X i * ((r g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))) :
    LinearIndependent k X := by
  have hli : LinearIndependent k (fun i => (ψ i : Γ → k)) :=
    (linearIndependent_monoidHom Γ k).comp ψ hψ
  rw [linearIndependent_iff'] at hli ⊢
  intro s c hc i hi
  have key : ∀ g, ∑ j ∈ s, (c j * ψ j g) • X j = 0 := by
    intro g
    have h1 : (∑ j ∈ s, (c j * ψ j g) • X j) *
        ((r g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = 0 := by
      have h2 : ((r g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * (∑ j ∈ s, c j • X j) = 0 := by
        rw [hc, Matrix.mul_zero]
      rw [← h2, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_smul_comm, h, smul_smul, smul_mul_assoc]
    exact (Units.mul_left_eq_zero (r g)).1 h1
  by_contra hci
  apply hX i
  ext a b
  have h3 := hli s (fun j => c j * X j a b) (by
    funext g
    have h4 := congrFun (congrFun (key g) a) b
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at h4
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← h4]
    exact Finset.sum_congr rfl fun j _ => by ring) i hi
  simpa [hci] using h3

theorem finite_quadratic_characters_in_adjoint :
    ∀ (Γ k : Type) [Group Γ] [Field k] [CharZero k] (n : ℕ) (r : Γ →* GL (Fin n) k),
      Set.Finite {χ : Γ →* ℤˣ | ∃ X : Matrix (Fin n) (Fin n) k, X ≠ 0 ∧ ∀ g,
        ((r g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X =
          ((χ g : ℤ) : k) • (X * ((r g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))} := by
  intro Γ k _ _ _ n r
  set S := {χ : Γ →* ℤˣ | ∃ X : Matrix (Fin n) (Fin n) k, X ≠ 0 ∧ ∀ g,
        ((r g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X =
          ((χ g : ℤ) : k) • (X * ((r g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))} with hS
  have hex : ∀ χ : S, ∃ X : Matrix (Fin n) (Fin n) k, X ≠ 0 ∧ ∀ g,
        ((r g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X =
          ((χ.1 g : ℤ) : k) • (X * ((r g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) :=
    fun χ => χ.2
  choose X hX h using hex
  let ψ : S → Γ →* k := fun χ =>
    ((Int.castRingHom k).toMonoidHom.comp (Units.coeHom ℤ)).comp χ.1
  have hψ : Function.Injective ψ := by
    intro χ₁ χ₂ e
    apply Subtype.ext
    ext g
    have h1 : ((χ₁.1 g : ℤ) : k) = ((χ₂.1 g : ℤ) : k) := DFunLike.congr_fun e g
    exact_mod_cast h1
  have hli := linearIndependent_conj_eigenmatrices r ψ hψ X hX h
  have : Finite S := hli.finite_of_isNoetherian
  exact Set.toFinite S

end GlobalTheory
end
