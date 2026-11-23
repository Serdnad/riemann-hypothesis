module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTestVectorExpansion
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle233
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle291
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle305
public import Development.AbelianVarietyTheory.Definitions.Foundations.ThNSpec
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeLetterPreservesBasisSet
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle371
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle307
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle197
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle088
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle095
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle333
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle379
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

@[expose] public section

section

noncomputable section

namespace GlobalTheory.Cusp.FlagCocompact

open scoped TensorProduct
open NumberField IsDedekindDomain Matrix
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups GlobalTheory.AutFunCompare

theorem exists_adapted_set {K M : Type} [Field K] [AddCommGroup M] [Module K M] (X : ℕ → Submodule K M)
    (hX : Monotone X) (h0 : X 0 = ⊥) (k : ℕ) :
    ∃ s : Set M, LinearIndepOn K id s ∧ s ⊆ X k ∧ ∀ i ≤ k, X i ≤ Submodule.span K (s ∩ X i) := by
  induction k with
  | zero => exact ⟨∅, linearIndepOn_empty _ _, Set.empty_subset _, fun i hi => by
      rw [Nat.le_zero.1 hi, h0]; exact bot_le⟩
  | succ k ih =>
    obtain ⟨s, hs, h1, h2⟩ := ih
    have h3 : s ⊆ X (k + 1) := h1.trans (hX k.le_succ)
    refine ⟨hs.extend h3, hs.linearIndepOn_extend h3, hs.extend_subset h3, fun i hi => ?_⟩
    rcases Nat.le_succ_iff.1 hi with h | rfl
    · exact (h2 i h).trans (Submodule.span_mono (Set.inter_subset_inter_left _ (hs.subset_extend h3)))
    · rw [Set.inter_eq_left.2 (hs.extend_subset h3)]
      exact hs.subset_span_extend h3

theorem exists_adapted_basis {K M : Type} [Field K] [AddCommGroup M] [Module K M] [Module.Finite K M]
    (X : ℕ → Submodule K M) (hX : Monotone X) (h0 : X 0 = ⊥) (k : ℕ) :
    ∃ (r : ℕ) (e : Fin r → M) (d : Fin r → ℕ), LinearIndependent K e ∧ (∀ j, d j < k) ∧
      ∀ i ≤ k, X i = Submodule.span K (e '' {j | d j < i}) := by
  classical
  obtain ⟨s, hs, h1, h2⟩ := exists_adapted_set X hX h0 k
  have hf : Finite s := LinearIndependent.finite (R := K) hs
  obtain ⟨r, ⟨q⟩⟩ := Finite.exists_equiv_fin s
  let e : Fin r → M := fun j => (q.symm j).1
  have he : LinearIndependent K e := LinearIndependent.comp hs q.symm q.symm.injective
  have hex : ∀ j, ∃ i, e j ∈ X (i + 1) := fun j => ⟨k, hX k.le_succ (h1 (q.symm j).2)⟩
  have hd : ∀ j i, Nat.find (hex j) < i ↔ e j ∈ X i := fun j i => by
    refine ⟨fun h => hX (Nat.succ_le_of_lt h) (Nat.find_spec (hex j)), fun h => ?_⟩
    cases i with
    | zero => rw [h0] at h; exact absurd h (he.ne_zero j)
    | succ i => exact Nat.lt_succ_of_le (Nat.find_min' _ h)
  refine ⟨r, e, fun j => Nat.find (hex j), he, fun j => (hd j k).2 (h1 (q.symm j).2), fun i hi => le_antisymm
    ((h2 i hi).trans (Submodule.span_mono ?_)) (Submodule.span_le.2 ?_)⟩
  · rintro x ⟨hx, hx'⟩
    have : e (q ⟨x, hx⟩) = x := by simp [e]
    exact ⟨q ⟨x, hx⟩, (hd _ _).2 (this.symm ▸ hx'), this⟩
  · rintro _ ⟨j, hj, rfl⟩
    exact (hd _ _).1 hj

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {hc : CMData F E} {V : HSpace E}


omit [NumberField F] in
theorem mem_extSub_span_depth {R : Type} [CommRing R] [Algebra F R] {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) E}
    (d : Fin r → ℕ) (i : ℕ) (y : Fin V.rank → R ⊗[F] E) :
    y ∈ extSub (F := F) V R (Submodule.span E ((fun k => vecOf V (Cᵀ k)) '' {j | d j < i})) ↔
      ∃ a : Fin r → R ⊗[F] E, (∀ j, i ≤ d j → a j = 0) ∧ y = (C.map (inclR (F := F) R)).mulVec a := by
  let C' : Matrix (Fin V.rank) (Fin r) E := fun a j => if d j < i then C a j else 0
  have e : Submodule.span E ((fun k => vecOf V (Cᵀ k)) '' {j | d j < i}) = colSpan V C' := by
    refine le_antisymm (Submodule.span_mono ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨j, hj, rfl⟩
      exact ⟨j, congrArg (vecOf V) (funext fun a => if_pos hj)⟩
    · rintro _ ⟨j, rfl⟩
      by_cases hj : d j < i
      · exact Submodule.subset_span ⟨j, hj, congrArg (vecOf V) (funext fun a => (if_pos hj).symm)⟩
      · have : C'ᵀ j = 0 := funext fun a => if_neg hj
        simp [this, vecOf]
  rw [e, AutFunCompare.mem_extSub_colSpan]
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨fun j => if d j < i then a j else 0, fun j hj => if_neg (not_lt.2 hj), funext fun b => ?_⟩
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : d j < i <;> simp [C', hj]
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a, funext fun b => ?_⟩
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : d j < i
    · simp [C', hj]
    · rw [ha j (not_lt.1 hj), mul_zero, mul_zero]

theorem exists_adapted_frame (𝔉 : IsoFlag V) : ∃ (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) E) (d : Fin r → ℕ),
    LinearIndependent E Cᵀ ∧ (∀ j, d j < 𝔉.k) ∧
      ∀ i, 𝔉.X i = Submodule.span E ((fun k => vecOf V (Cᵀ k)) '' {j | d j < i.val}) := by
  have : Module.Finite E V.V := Module.Finite.of_basis V.frame
  obtain ⟨r, e, d, he, hd, hX⟩ := exists_adapted_basis (K := E)
    (fun i => 𝔉.X ⟨min i 𝔉.k, Nat.lt_succ_of_le (min_le_right _ _)⟩)
    (fun a b h => 𝔉.strictMono.monotone (Fin.mk_le_mk.2 (min_le_min_right _ h)))
    (by rw [← 𝔉.zero]; congr 1) 𝔉.k
  refine ⟨r, Matrix.of fun a j => V.frame.repr (e j) a, d, he.map' V.frame.equivFun.toLinearMap (LinearEquiv.ker _),
    hd, fun i => ?_⟩
  have e1 : (fun k => vecOf V ((Matrix.of fun a j => V.frame.repr (e j) a)ᵀ k)) = e :=
    funext fun k => V.frame.equivFun.symm_apply_apply (e k)
  rw [e1, ← hX i (Nat.lt_succ_iff.1 i.2)]
  congr 1
  ext
  simp [Nat.lt_succ_iff.1 i.2]

theorem unip_cocompact (hc : CMData F E) (𝔉 : IsoFlag V) : Cocompact (ratPts hc V) (𝔉.unip hc (AF F)) := by
  obtain ⟨r, C, d, hC, hd, hX⟩ := exists_adapted_frame 𝔉
  have ht : 𝔉.top = colSpan V C := (hX _).trans (congrArg (Submodule.span _) (by
    rw [← Set.image_univ]; congr 1; exact Set.eq_univ_of_forall fun j => hd j))
  have h0 : cT (hc.sig : E →+* E) C * V.gram * C = 0 := by
    have h := 𝔉.iso
    change 𝔉.top ≤ perp V 𝔉.top at h
    rw [ht] at h
    ext a k
    have := (mem_perp_colSpan hc V C _).1 (h (Submodule.subset_span ⟨k, rfl⟩))
    simp only [repr_vecOf] at this
    exact congrFun this a
  have hm : ∀ (g : GA hc V) (x : Fin V.rank → E),
      ((HA.mat _ hc.sig V.gram g).1 - 1) *ᵥ (fun i => inclR (F := F) (AF F) (x i)) =
      act hc V g (coordR V _ (vecOf V x)) - coordR V _ (vecOf V x) := fun g x => by
    have : coordR (F := F) V (AF F) (vecOf V x) = fun i => inclR (F := F) (AF F) (x i) :=
      funext fun i => by rw [coordR, repr_vecOf]
    rw [this, Matrix.sub_mulVec, Matrix.one_mulVec]; rfl
  have e : 𝔉.unip hc (AF F) = Subgroup.closure (Mem.UnipCocompact.radSet hc V C d) := by
    rw [← Subgroup.closure_eq (𝔉.unip hc (AF F))]
    congr 1
    ext g
    refine IsoFlag.mem_unip_iff.trans
      (and_congr ⟨fun h i => ?_, fun h i x hx => ?_⟩ ⟨fun h x hx => ?_, fun h x hx => ?_⟩)
    · have := h ⟨d i, hd i⟩ (vecOf V (Cᵀ i)) (by
        rw [hX]; exact Submodule.subset_span ⟨i, Nat.lt_succ_self _, rfl⟩)
      rw [hX, ← hm] at this
      exact (mem_extSub_span_depth d _ _).1 this
    · rw [hX] at hx ⊢
      refine act_sub_mem_of_mem_span ?_ hx
      rintro _ ⟨j, hj, rfl⟩
      obtain ⟨a, ha, h'⟩ := h j
      exact (mem_extSub_span_depth d _ _).2
        ⟨a, fun l hl => ha l (Nat.le_trans (Nat.lt_succ_iff.1 hj) hl), (hm g _).symm.trans h'⟩
    · rw [ht] at h
      rw [hm]
      exact (mem_extSub_colSpan V _ C _).1 (h _ ((mem_perp_colSpan hc V C _).2 (by simpa only [repr_vecOf] using hx)))
    · rw [ht] at hx ⊢
      have := h _ ((mem_perp_colSpan hc V C _).1 hx)
      rw [hm, show vecOf V (fun i => V.frame.repr x i) = x from V.frame.equivFun.symm_apply_apply x] at this
      exact (mem_extSub_colSpan V _ C _).2 this
  rw [e]
  obtain ⟨K, hK, h⟩ := Mem.UnipCocompact.closure_radSet_cocompact hc V C hC h0 d
  refine ⟨K, hK, fun n => ?_⟩
  obtain ⟨γ, hγ, k, hk, rfl⟩ := h n
  exact ⟨γ⁻¹, inv_mem hγ, by rwa [inv_mul_cancel_left]⟩

end GlobalTheory.Cusp.FlagCocompact

namespace GlobalTheory.Cusp

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.Mem.Th

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cocompact_flag : ∀ (D : D7) (V : HSp D) (𝔉 : IsoFlag V), Cocompact (GQ V) (NA 𝔉) := fun D V 𝔉 => by
  rw [AutFunCompare.GQ_eq]
  exact FlagCocompact.unip_cocompact D.sp.cm 𝔉

end GlobalTheory.Cusp

end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.NormSum.Expand
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ArchFree.expand

theorem om_expand : ∀ (D : D7), ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ) (Q : ℕ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (P : Pair D cc δ t0 Q), ∀ (g : GA D P.a) (g' : GA D P.d) L₁ L₁', Moves D (g : GL (Fin P.a) (AE D)) L₁ → Moves D (g' : GL (Fin P.d) (AE D)) L₁' → ∃ (c : ℂ) (k : ℕ) (r : Fin k → Qbar) (y : Fin k → VC D P.a P.d), 0 < Q → (Mod1All c ∧ (∀ i, Q • y i ∈ La D (tor0 D cc δ) L₁ L₁') ∧ (∀ i, IsIntegral ℤ ((Q : Qbar) ^ (P.a * P.d) * r i)) ∧ (∀ ρ : Qbar →+* ℂ, (∑ i, ‖ρ (r i)‖) ^ 2 ≤ (Q : ℝ) ^ (P.a * P.d)) ∧ (P.W.Om g g' P.F = fun z => c * ∑ i, (r i : ℂ) * U D (tor0 D cc δ) (y i) (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) P.a P.d) (La D (tor0 D cc δ) L₁ L₁') P.e0) z) ∧ ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (k' : GA D P.d), k' ∈ intG D P.d → TrivAt D p (g : GL (Fin P.a) (AE D)) → TrivAt D p ((g' * k' : GA D P.d) : GL (Fin P.d) (AE D)) → ‖lamC lam c‖ = 1) := by
  intro D cc δ t0 Q hC _ P g g' L₁ L₁' hL hL'
  rcases Nat.eq_zero_or_pos Q with hQ | hQ
  · exact ⟨0, 0, Fin.elim0, Fin.elim0, fun h => absurd h (by omega)⟩
  have hSD : ∀ (N : ℕ) (g : GA D N) L, Moves D (g : GL (Fin N) (AE D)) L → SD D L := by
    intro N g L hL
    obtain ⟨Lt, h1, -⟩ := GlobalTheory.T.Lt_eq_iff_inv_mul_mem_intG_and_transport D N
    have : L = Lt g := by
      ext x; rw [hL x, (h1 g).1 x]
    rw [this]; exact (h1 g).2
  have hSD0 : ∀ N : ℕ, SD D (stdL D N) := by
    intro N
    obtain ⟨Lt, h1, h2, -⟩ := GlobalTheory.T.Lt_eq_iff_inv_mul_mem_intG_and_transport D N
    rw [← h2]; exact (h1 1).2
  obtain ⟨-, hW, hint, -⟩ := GlobalTheory.T.theta_space_selfDual_pair_at_most_line D (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 cc δ hC P.a P.d (La0 D (tor0 D cc δ) P.a P.d)
    (Or.inr ⟨_, _, hSD0 _, hSD0 _, rfl⟩)
  obtain ⟨-, -, -, -, -, -, hq⟩ := GlobalTheory.T.theta_space_selfDual_pair_at_most_line D (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 cc δ hC P.a P.d (La D (tor0 D cc δ) L₁ L₁')
    (Or.inr ⟨_, _, hSD _ g _ hL, hSD _ g' _ hL', rfl⟩)
  have he0 : P.e0 ∈ Th D (tor0 D cc δ) (stdL D P.a) (stdL D P.d) := P.vac.1
  have hfix : ∀ x ∈ La0 D (tor0 D cc δ) P.a P.d, Wd D (tor0 D cc δ) x P.e0 = P.e0 := by
    intro x hx
    rw [hW x hx]; funext z; exact he0.2 x hx z
  have heT : P.e0 ∈ TT D (tor0 D cc δ) P.a P.d :=
    ⟨he0.1, 1, one_pos, fun x hx => by rw [one_nsmul]; exact hfix x hx⟩
  obtain ⟨c, hc1, hc2, hc3⟩ := GlobalTheory.T.vacuum_under_adelic_pair_unit_modulus_factor D cc δ hC P.a P.d (P.d_even.mul_left _) P.e0 he0 P.W g g'
    L₁ L₁' hL hL'
  obtain ⟨k, r, z, hz, hr1, hr2, hF⟩ := P.pres
  have hT : ∀ i, Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z i)) P.e0 ∈ TT D (tor0 D cc δ) P.a P.d := by
    intro i
    refine ⟨Wd_diff _ he0.1, Q, hQ, fun x hx => ?_⟩
    obtain ⟨m, hm⟩ := hint x hx _ (hz i)
    rw [Hf_nsmul_right, ← Hf_nsmul_left] at hm
    rw [Wd_comm _ _ m hm, hfix _ (nsmul_mem hx _)]
  have hQc : (Q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hQ.ne'
  have key : ∀ i, ∃ y : VC D P.a P.d, Q • y ∈ La D (tor0 D cc δ) L₁ L₁' ∧
      P.W.Om g g' (Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z i)) P.e0) =
        Wd D (tor0 D cc δ) y (P.W.Om g g' P.e0) := by
    intro i
    obtain ⟨B, hB, h⟩ := approx_La (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1.1 _ _ hL hL' (hz i)
    obtain ⟨m, hm, hl⟩ := P.W.lift g g' ((Q : D.host.E)⁻¹ • B) P.e0 heT
    obtain ⟨B', h1, h2⟩ := h (m * Q) (by positivity)
    refine ⟨pt D (tor0 D cc δ) δ ((Q : D.host.E)⁻¹ • B'), ?_, ?_⟩
    · rw [pt_div, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hQc, one_smul]; exact h1
    · rw [← hl _ (closeTo_div hQ h2), pt_div, ← hB, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
        inv_mul_cancel₀ hQc, one_smul]
  choose y hy1 hy2 using key
  have hu : ∀ i, ∃ u : Qbar, (u : ℂ) = wdPh D (tor0 D cc δ) (y i) ∧ IsIntegral ℤ u ∧
      ∀ ρ : Qbar →+* ℂ, ‖ρ u‖ = 1 := by
    intro i
    obtain ⟨m, hm⟩ := hq _ (hy1 i)
    exact root_unity (by positivity) (wdPh_pow _ m hm)
  choose u hu1 hu2 hu3 using hu
  refine ⟨c, k, fun i => r i * u i, y, fun _ => ⟨hc1, hy1, fun i => ?_, fun ρ => ?_, ?_, hc3⟩⟩
  · rw [← mul_assoc]; exact (hr1 i).mul (hu2 i)
  · simpa only [map_mul, norm_mul, hu3, mul_one] using hr2 ρ
  · have hF' : P.F = ∑ i, (r i : ℂ) • Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z i)) P.e0 := by
      rw [hF]; funext w; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hF', (Om_sum P.W g g' Finset.univ _ _ hT).2]
    funext w
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hy2, hc2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [IntermediateField.coe_mul, hu1]
    simp only [Wd, U]
    ring

end GlobalTheory.ArchFree.expand
end
end

section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

noncomputable section

namespace GlobalTheory.ThNHecke

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem inv_natCast_mem (A : ValuationSubring Ω) {l q : ℕ} (hq : q.Prime) (hl : l.Prime) (hql : q ≠ l)
    (hlA : (l : Ω) ∈ A.nonunits) : ((q : Ω))⁻¹ ∈ A := by
  have hcop : Nat.Coprime q l := (Nat.coprime_primes hq hl).mpr hql
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  have e : (u : Ω) * (q : Ω) + (v : Ω) * (l : Ω) = 1 := by exact_mod_cast congrArg (fun t : ℤ => (t : Ω)) huv
  have hu : A.valuation (u : Ω) ≤ 1 := (A.valuation_le_one_iff _).mpr (intCast_mem A u)
  have hv : A.valuation (v : Ω) ≤ 1 := (A.valuation_le_one_iff _).mpr (intCast_mem A v)
  have hqle : A.valuation (q : Ω) ≤ 1 := (A.valuation_le_one_iff _).mpr (natCast_mem A q)
  have hl1 : A.valuation (l : Ω) < 1 := (A.mem_nonunits_iff).mp hlA
  have hq1 : A.valuation (q : Ω) = 1 := by
    refine le_antisymm hqle (not_lt.mp fun hlt => ?_)
    have h1 : A.valuation ((u : Ω) * (q : Ω)) < 1 := by
      rw [map_mul]; exact (mul_le_mul' hu le_rfl).trans_lt (by rwa [one_mul])
    have h2 : A.valuation ((v : Ω) * (l : Ω)) < 1 := by
      rw [map_mul]; exact (mul_le_mul' hv le_rfl).trans_lt (by rwa [one_mul])
    have h3 := Valuation.map_add_lt A.valuation h1 h2
    rw [e, map_one] at h3
    exact lt_irrefl _ h3
  rw [← A.valuation_le_one_iff, map_inv₀, hq1, inv_one]

theorem op_mem_B [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (hj : ∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) (N l w : ℕ) [Fact l.Prime]
    (hN : 1 ≤ N) (hlN : ¬ l ∣ N) (T : Letter) (hT : admitted N l T) (b : X.Fn l) (hb : b ∈ X.B N l w) :
    X.op N l T b ∈ X.B N l w := by
  obtain ⟨φ, h1, h2⟩ := hj
  have hA := (GlobalTheory.T.modular_function_tower_integrality ε X ε.injective ⟨φ, h2, h1⟩ l).1
  have hNl : Nat.Coprime N l :=
    Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd (Fact.out : l.Prime)).mpr hlN)
  have hle : X.B N l w ≤ (X.B N l w).comap (X.op N l T) :=
    Submodule.span_le.mpr (fun x hx => Submodule.subset_span
      (StabHecke.op_BSet X hA N w (by omega) hNl T hT x hx))
  exact hle hb

theorem isThB_cong [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [hl : Fact l.Prime]
    (l2 : l ≠ 2) (hN : ¬ l ∣ N) (hN1 : 1 ≤ N) (hlA : (l : Ω) ∈ A.nonunits) (n : ℕ) (b : X.Fn l)
    (φ φ' : HahnSeries ℚ Ω) (h1 : IsThB X A N l n b φ) (h2 : IsThB X A N l n b φ') :
    ∀ r, CgA A l n (φ.coeff r) (φ'.coeff r) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨f, hfI, hfc, hfδ, hfD⟩ := h1
  obtain ⟨f', hf'I, hf'c, hf'δ, hf'D⟩ := h2
  obtain ⟨u, hu⟩ := GlobalTheory.Tower.cls_eq_pow X l n f f' (hfc.symm.trans hf'c)
  have hf0 : (f : X.K) ≠ 0 := f.ne_zero
  have hu0 : (u : X.K) ≠ 0 := u.ne_zero
  have hL : (u : X.K) ^ (l ^ n) = (f : X.K)⁻¹ * f' := by rw [hu]; field_simp
  have hT := GlobalTheory.TInv.sl_T_eq X N l n hl.out l2 hN hN1 (u : X.K) hu0 (by
      intro γ hγ; rw [hL, map_mul, map_inv₀, hfI γ hγ, hf'I γ hγ]) (by
      intro δ hδ hδ'
      obtain ⟨g, hgI, hg⟩ := hfδ δ hδ hδ'
      obtain ⟨g', hg'I, hg'⟩ := hf'δ δ hδ hδ'
      have hsf : X.sl (ofSL δ) (f : X.K) ≠ 0 := by
        intro h0; exact hf0 ((X.sl (ofSL δ)).injective (h0.trans (map_zero _).symm))
      have hg0 : g ≠ 0 := by
        intro h0; rw [h0, zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)] at hg; exact mul_ne_zero hf0 hsf hg
      refine ⟨g' / g, ?_, ?_⟩
      · intro γ hγ; rw [map_div₀, hgI γ hγ, hg'I γ hγ]
      · rw [div_pow, ← hg', ← hg, hu, map_mul, map_pow]; field_simp; ring)
  exact GlobalTheory.Glue.DlPow.isDl_mul_lpow_cong X A l hlA n (f : X.K) (u : X.K) hf0 hu0 hT φ φ' hfD (by rw [← hu]; exact hf'D)

end GlobalTheory.ThNHecke


open GlobalTheory.ThNHecke in
theorem GlobalTheory.CyclotomicQExpansion.thN_hecke : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime], (∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) → l ≠ 2 → ¬ l ∣ N → 5 ≤ N → ((l : Ω) ∈ A.nonunits) → ∀ (n w d : ℕ), Odd w → d.Coprime N → ∀ b : X.Fn l, b ∈ X.B N l w →
  (∀ q : ℕ, q.Prime → ¬ q ∣ N * l → ∀ r, CgA A l n ((thN X A N l n d (X.heckeT N l q b)).coeff r)
      ((hq ε q (thN X A N l n d b) + ((q : Ω) ^ (w + 1)) • vq q (thN X A N l n (d * q) b)).coeff r)) ∧
  (∀ r, CgA A l n ((thN X A N l n d (X.heckeU l b)).coeff r) ((uq l (thN X A N l (n + 1) d b)).coeff r)) ∧
  (∀ a : ℕ, a.Coprime N → ∀ r, CgA A l n ((thN X A N l n d (X.diam N l a b)).coeff r) ((thN X A N l n (d * a) b).coeff r)) := by
  intro Ω _ _ _ ε X A N l _ hj hl2 hlN hN hlA n w d hw hd b hb
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have halg : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  have hl : l.Prime := Fact.out
  have stab : ∀ T : Letter, admitted N l T → ∀ c : X.Fn l, c ∈ X.B N l w → X.op N l T c ∈ X.B N l w :=
    fun T hT c hc => op_mem_B ε X hj N l w (by omega) hlN T hT c hc
  have dB : ∀ e : ℕ, e.Coprime N → ∀ c : X.Fn l, c ∈ X.B N l w →
      X.act l (sgD N l e : Matrix (Fin 2) (Fin 2) ℤ) c ∈ X.B N l w :=
    fun e he c hc => stab (Letter.D e) he c hc
  have exL : ∀ (m e : ℕ), e.Coprime N → ∀ c : X.Fn l, c ∈ X.B N l w →
      IsThB X A N l m (X.act l (sgD N l e : Matrix (Fin 2) (Fin 2) ℤ) c) (thN X A N l m e c) ∧ IsLat 1 (thN X A N l m e c) :=
    fun m e he c hc => GlobalTheory.T.theta_lattice_diamond_action Ω ε X A N l hj hl2 hlN (by omega) hlA m w e hw he c hc
  have ex : ∀ (m e : ℕ), e.Coprime N → ∀ c : X.Fn l, c ∈ X.B N l w →
      IsThB X A N l m (X.act l (sgD N l e : Matrix (Fin 2) (Fin 2) ℤ) c) (thN X A N l m e c) :=
    fun m e he c hc => (exL m e he c hc).1
  have uniq : ∀ (m : ℕ) (c : X.Fn l), c ∈ X.B N l w → ∀ φ φ' : HahnSeries ℚ Ω,
      IsThB X A N l m c φ → IsThB X A N l m c φ' → ∀ r, CgA A l m (φ.coeff r) (φ'.coeff r) :=
    fun m c _ φ φ' h h' => isThB_cong X A N l hl2 hlN (by omega) hlA m c φ φ' h h'
  refine ⟨?_, ?_, ?_⟩
  · intro q hqP hqd r
    have hqN : q.Coprime N := (Nat.Prime.coprime_iff_not_dvd hqP).mpr (fun h => hqd (dvd_mul_of_dvd_left h l))
    have hql : q ≠ l := by
      rintro rfl; exact hqd (dvd_mul_left q N)
    have hqinv := inv_natCast_mem A hqP hl hql hlA
    have hTb : X.heckeT N l q b ∈ X.B N l w := stab (Letter.T q) ⟨hqP, hqd⟩ b hb
    have e1 := exL n d hd b hb
    have e2 := exL n (d * q) (Nat.Coprime.mul_left hd hqN) b hb
    have h2 : IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) (X.heckeT N l q b))
        (hq ε q (thN X A N l n d b) + ((q : Ω) ^ (w + 1)) • vq q (thN X A N l n (d * q) b)) :=
      GlobalTheory.T.thetaOperator_heckeT_q_eq_U_add_V_twist Ω ε X A N l halg hj (by omega) n w d q hw hqP hqd hqinv hlA hl2 hlN hd b hb _ _ e1.2 e2.2 e1.1 e2.1
    exact uniq n _ (dB d hd _ hTb) _ _ (ex n d hd _ hTb) h2 r
  · intro r
    have hUb : X.heckeU l b ∈ X.B N l w := stab Letter.U trivial b hb
    have e1 := exL (n + 1) d hd b hb
    have h2 : IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) (X.heckeU l b))
        (uq l (thN X A N l (n + 1) d b)) :=
      GlobalTheory.T.thetaOperator_upperU_l_commute_scale_one Ω ε X A N l n w d halg hj hl2 (by omega) hw hlA hd hlN b hb _ e1.2 e1.1
    exact uniq n _ (dB d hd _ hUb) _ _ (ex n d hd _ hUb) h2 r
  · intro a ha r
    have hDb : X.diam N l a b ∈ X.B N l w := stab (Letter.D a) ha b hb
    have h1 := (GlobalTheory.KZ.isThB_act_sgD_diam_iff Ω ε X A N l n w a d ha hd b hb _).mp (ex n d hd _ hDb)
    exact uniq n _ (dB (d * a) (Nat.Coprime.mul_left hd ha) b hb) _ _ h1 (ex n (d * a) (Nat.Coprime.mul_left hd ha) b hb) r
end
end
