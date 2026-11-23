module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle892
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle733
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle894
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CohomologyLogDerivativeAdjointEndomorphisms
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle022
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle813
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FinrankOfIsSecBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle120
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle893
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle009
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007

@[expose] public section

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.height_le_cotangent_dim_add_dual_cotangent_dim : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0) (G : PDivGroup p K), G.height ≤ Module.finrank K (Cot K (G.A 1)) + Module.finrank K (Cot K (G.dual.A 1)) := by
  first | exact @GlobalTheory.PDivGroup.height_le_finrank_cot_add_finrank_cot_dual | exact GlobalTheory.PDivGroup.height_le_finrank_cot_add_finrank_cot_dual | (intros; apply GlobalTheory.PDivGroup.height_le_finrank_cot_add_finrank_cot_dual <;> assumption)
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.cotangent_dim_add_dual_cotangent_dim_le_height : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0) (G : PDivGroup p K), Module.finrank K (Cot K (G.A 1)) + Module.finrank K (Cot K (G.dual.A 1)) ≤ G.height := by
  first | exact @GlobalTheory.PDivGroup.finrank_cot_add_finrank_cot_dual_le_of_cast_eq_zero | exact GlobalTheory.PDivGroup.finrank_cot_add_finrank_cot_dual_le_of_cast_eq_zero | (intros; apply GlobalTheory.PDivGroup.finrank_cot_add_finrank_cot_dual_le_of_cast_eq_zero <;> assumption)
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)

noncomputable section

namespace GlobalTheory.SizeSqIntegral

theorem sz_nat_val (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (D : ℕ) :
    Sz l lam (-(padicValNat l D : ℝ)) (D : ℂ) := by
  have h := GlobalTheory.SizeRat.sz_ratCast l lam (D : ℚ) (-(padicValNat l D : ℝ)) (by
    rw [padicValRat.of_nat, Nat.padicValNat_def]; simp)
  simpa using h

theorem sz_zero_of_isIntegral (l : ℕ) [hl : Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (x : ℂ)
    (h : IsIntegral ℤ x) : Sz l lam 0 x :=
  GlobalTheory.SzRules.sz_of_isIntegral 1 x (fun hd => hl.out.one_lt.ne' (Nat.dvd_one.1 hd)) (by simpa using h)

theorem main : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (D M : ℕ) (x : ℂ), 0 < D → IsIntegral ℤ ((D : ℂ) * x ^ 2) → Sz l lam (-(padicValNat l D : ℝ) / 2) ((D : ℂ) * x) ∧ Sz l lam (-(padicValNat l D : ℝ) / 2) ((M * l ^ padicValNat l D : ℕ) : ℂ) := by
  intro l hl lam D M x _ hx
  constructor
  · apply GlobalTheory.SzRules.sz_of_sq
    have h := GlobalTheory.SzRules.sz_mul (sz_nat_val l lam D) (sz_zero_of_isIntegral l lam _ hx)
    rw [add_zero] at h
    convert h using 1
    ring
  · have h1 := sz_nat_val l lam (l ^ padicValNat l D)
    rw [Nat.padicValNat_def, Nat.multiplicity_prime_pow] at h1
    have h2 : Sz l lam 0 (M : ℂ) := sz_zero_of_isIntegral l lam _ (by simpa using (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (M : ℤ))))
    have h := GlobalTheory.SzRules.sz_mul h2 h1
    rw [zero_add, ← Nat.cast_mul] at h
    refine GlobalTheory.SzRules.sz_mono ?_ h
    have : (0 : ℝ) ≤ (padicValNat l D : ℝ) := Nat.cast_nonneg _
    linarith

end GlobalTheory.SizeSqIntegral
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.KS (rsT)

namespace GlobalTheory.GlueOver

open GlobalTheory.KS

variable {X : Scheme.{0}}

theorem rsT_cocycle {M : LB X} (hM : M.IsLB) (a b c : M.ι) {O : X.Opens} (h : O ≤ M.U a ⊓ M.U b ⊓ M.U c) :
    rsT (M.g a b).val O * rsT (M.g b c).val O = rsT (M.g a c).val O := by
  have e := congrArg (fun u => rsT u.val O) (hM.cocycle a b c)
  simp only [Units.val_mul, GlobalTheory.KS.AdjDlog.val_res, rsT_mul] at e
  rwa [rsT_rsT inf_le_left h, rsT_rsT (le_inf (inf_le_left.trans inf_le_right) inf_le_right) h,
    rsT_rsT (le_inf (inf_le_left.trans inf_le_left) inf_le_right) h] at e

theorem rsT_g_self {M : LB X} (hM : M.IsLB) (a : M.ι) {O : X.Opens} (h : O ≤ M.U a) :
    rsT (M.g a a).val O = 1 := by
  have h2 : O ≤ M.U a ⊓ M.U a := le_inf h h
  have e := rsT_cocycle hM a a a (le_inf h2 h)
  have hu : IsUnit (rsT (M.g a a).val O) := by
    rw [rsT_of_le h2]
    exact (M.g a a).isUnit.map _
  exact hu.mul_left_cancel (e.trans (_root_.mul_one _).symm)

theorem exists_glue : ∀ {X : Scheme.{0}} (M : LB X), M.IsLB → ∀ (V : X.Opens) {J : Type} (W : J → X.Opens)
    (j : J → M.ι) (F : ∀ i, Γ(X, W i)), ⨆ i, W i = V → (∀ i, W i ≤ M.U (j i)) →
    (∀ i i', rsT (F i) (W i ⊓ W i') = rsT (M.g (j i) (j i')).val (W i ⊓ W i') * rsT (F i') (W i ⊓ W i')) →
    ∃ t : ∀ c, Γ(X, M.U c ⊓ V),
      (∀ c c', rsT (t c) (M.U c ⊓ M.U c' ⊓ V) =
        rsT (M.g c c').val (M.U c ⊓ M.U c' ⊓ V) * rsT (t c') (M.U c ⊓ M.U c' ⊓ V)) ∧
      ∀ i, rsT (t (j i)) (W i) = F i := by
  intro X M hM V J W j F hV hW Fc
  have hWV : ∀ i, W i ≤ V := fun i => hV ▸ le_iSup W i
  have cov : ∀ O : X.Opens, O ⊓ V ≤ ⨆ i, O ⊓ W i := by
    intro O y hy
    have : y ∈ ⨆ i, W i := by rw [hV]; exact hy.2
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hy.1, hi⟩
  have hU : ∀ c i, M.U c ⊓ W i ≤ M.U c ⊓ M.U (j i) := fun c i => inf_le_inf le_rfl (hW i)
  have hUV : ∀ (O : X.Opens) i, O ⊓ W i ≤ O ⊓ V := fun O i => inf_le_inf le_rfl (hWV i)
  have glue : ∀ c : M.ι, ∃ t : Γ(X, M.U c ⊓ V), ∀ i,
      rsT t (M.U c ⊓ W i) = rsT (M.g c (j i)).val (M.U c ⊓ W i) * rsT (F i) (M.U c ⊓ W i) := by
    intro c
    refine exists_rsT_eq (fun i => M.U c ⊓ W i) (fun i => hUV _ i) (cov _) _ fun i i' => ?_
    have hN1 : (M.U c ⊓ W i) ⊓ (M.U c ⊓ W i') ≤ M.U c ⊓ W i := inf_le_left
    have hN2 : (M.U c ⊓ W i) ⊓ (M.U c ⊓ W i') ≤ M.U c ⊓ W i' := inf_le_right
    have hNW : (M.U c ⊓ W i) ⊓ (M.U c ⊓ W i') ≤ W i ⊓ W i' := fun y hy => ⟨hy.1.2, hy.2.2⟩
    have h3 : (M.U c ⊓ W i) ⊓ (M.U c ⊓ W i') ≤ M.U c ⊓ M.U (j i) ⊓ M.U (j i') :=
      fun y hy => ⟨⟨hy.1.1, hW i hy.1.2⟩, hW i' hy.2.2⟩
    rw [rsT_mul, rsT_mul, rsT_rsT (hU c i) hN1, rsT_rsT (hU c i') hN2,
      rsT_rsT inf_le_right hN1, rsT_rsT inf_le_right hN2, ← rsT_rsT inf_le_left hNW (F i), Fc, rsT_mul,
      rsT_rsT (inf_le_inf (hW i) (hW i')) hNW, rsT_rsT inf_le_right hNW,
      ← _root_.mul_assoc, rsT_cocycle hM _ _ _ h3]
  choose t ht using glue
  refine ⟨t, fun c c' => ?_, fun i => ?_⟩
  · refine eq_of_rsT_eq (fun i => M.U c ⊓ M.U c' ⊓ W i) (fun i => hUV _ i) (cov _) _ _ fun i => ?_
    have a1 : M.U c ⊓ M.U c' ⊓ W i ≤ M.U c ⊓ W i := fun y hy => ⟨hy.1.1, hy.2⟩
    have a2 : M.U c ⊓ M.U c' ⊓ W i ≤ M.U c' ⊓ W i := fun y hy => ⟨hy.1.2, hy.2⟩
    have h3 : M.U c ⊓ M.U c' ⊓ W i ≤ M.U c ⊓ M.U c' ⊓ M.U (j i) := inf_le_inf le_rfl (hW i)
    have e' : M.U c ⊓ M.U c' ⊓ W i ≤ M.U c ⊓ M.U c' ⊓ V := hUV _ i
    have eL : M.U c ⊓ M.U c' ⊓ V ≤ M.U c ⊓ V := fun y hy => ⟨hy.1.1, hy.2⟩
    have eR : M.U c ⊓ M.U c' ⊓ V ≤ M.U c' ⊓ V := fun y hy => ⟨hy.1.2, hy.2⟩
    rw [rsT_rsT eL e', rsT_mul, rsT_rsT eR e', rsT_rsT inf_le_left e',
      ← rsT_rsT (hUV _ i) a1 (t c), ← rsT_rsT (hUV _ i) a2 (t c'), ht, ht, rsT_mul, rsT_mul,
      rsT_rsT (hU c i) a1, rsT_rsT (hU c' i) a2, rsT_rsT inf_le_right a1,
      rsT_rsT inf_le_right a2, ← _root_.mul_assoc, rsT_cocycle hM _ _ _ h3]
  · have a : W i ≤ M.U (j i) ⊓ W i := le_inf (hW i) le_rfl
    rw [← rsT_rsT (hUV _ i) a, ht, rsT_mul, rsT_rsT (hU _ i) a, rsT_rsT inf_le_right a, rsT_self,
      rsT_g_self hM (j i) (hW i), _root_.one_mul]

end GlobalTheory.GlueOver
end
end

section

open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism

namespace GlobalTheory.FinGL.BlockMatch

variable {F : Type} [Field F] {r : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem eq_zero_of_invariant [Finite F] {b : Fin r → ℕ} {σ : Representation ℂ (blockTri (κ := F) b) V}
    (hσ : IsCuspDatum b σ) (S : Finset (Fin r)) (hS : ∃ i j, b i = b j ∧ i ∈ S ∧ j ∉ S) (T : V →ₗ[ℂ] W)
    (hT : ∀ u : blockTri (κ := F) b, (∀ i j, ((u : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j ≠
      (1 : Matrix (Fin r) (Fin r) F) i j → b i = b j ∧ i ∈ S ∧ j ∉ S) → T ∘ₗ σ u = T) : T = 0 := by
  classical
  let c : Fin r → ℕ := fun k => if k ∈ S then 0 else 1
  let U : Subgroup (blockTri (κ := F) b) :=
    (levi F b ⊓ GlobalTheory.FiniteGL.unipRadical F c).subgroupOf (blockTri b)
  have hU : ∀ u : blockTri (κ := F) b, u ∈ U ↔ ∀ i j, ((u : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j ≠
      (1 : Matrix (Fin r) (Fin r) F) i j → b i = b j ∧ i ∈ S ∧ j ∉ S := by
    intro u
    simp only [U, Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_levi, GlobalTheory.FiniteGL.mem_unipRadical,
      Matrix.sub_apply, sub_eq_zero]
    constructor
    · rintro ⟨h1, h2⟩ i j hne
      refine ⟨?_, ?_⟩
      · by_contra h
        exact hne (by rw [h1 i j h, Matrix.one_apply_ne (fun e => h (congrArg b e))])
      · by_contra h
        refine hne (h2 i j ?_)
        by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> simp_all [c]
    · intro h
      refine ⟨fun i j hij => ?_, fun i j hij => ?_⟩
      · by_contra h0
        exact hij (h i j (by rwa [Matrix.one_apply_ne (fun e => hij (congrArg b e))])).1
      · by_contra h0
        obtain ⟨-, hi, hj⟩ := h i j h0
        simp [c, hi, hj] at hij
  letI := Fintype.ofFinite U
  have hc : (Fintype.card U : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  ext v
  have h0 : ∑ u : U, σ u v = 0 := by
    refine hσ.cusp S hS _ fun n hn => ?_

    rw [map_sum]
    exact Fintype.sum_equiv (Equiv.mulLeft (⟨n, (hU n).2 hn⟩ : U)) _ _ fun u => by simp
  have h1 := congrArg T h0
  have h2 : ∀ u : U, T (σ u v) = T v := fun u => LinearMap.congr_fun (hT u ((hU u).1 u.2)) v

  rw [map_sum, map_zero, Finset.sum_congr rfl fun u _ => h2 u, Finset.sum_const, Finset.card_univ,
  ← Nat.cast_smul_eq_nsmul ℂ] at h1
  exact (smul_eq_zero.1 h1).resolve_left hc

theorem mem_blockTri_of_ne {b : Fin r → ℕ} {g : GL (Fin r) F}
    (h : ∀ i j, (g : Matrix (Fin r) (Fin r) F) i j ≠ (1 : Matrix (Fin r) (Fin r) F) i j → b i < b j) :
    g ∈ blockTri (κ := F) b := by
  refine mem_blockTri.2 fun i j hij => ?_
  by_contra h0
  have := h i j (by rwa [Matrix.one_apply_ne (fun e => by rw [e] at hij; exact lt_irrefl _ hij)])
  omega

theorem blocks_match : ∀ (F : Type) [Field F] [Finite F] (r : ℕ) (b b' : Fin r → ℕ) (V V' : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (σ : Representation ℂ (blockTri (κ := F) b) V) (σ' : Representation ℂ (blockTri (κ := F) b') V'), IsCuspDatum b σ → IsCuspDatum b' σ' → ∀ (w : Equiv.Perm (Fin r)) (T : V →ₗ[ℂ] V'), T ≠ 0 → (∀ (p : blockTri (κ := F) b) (p' : blockTri (κ := F) b'), (p' : GL (Fin r) F) * permGL F w = permGL F w * (p : GL (Fin r) F) → σ' p' ∘ₗ T = T ∘ₗ σ p) → ∀ i j : Fin r, b i = b j ↔ b' (w i) = b' (w j) := by
  intro F _ _ r b b' V V' _ _ _ _ σ σ' hσ hσ' w T hT hint
  have hone : ∀ k l : Fin r, (1 : Matrix (Fin r) (Fin r) F) (w k) (w l) = (1 : Matrix (Fin r) (Fin r) F) k l := by
    intro k l
    simp [Matrix.one_apply]
  have A : ∀ i j, b i = b j → ¬ b' (w i) < b' (w j) := by
    intro i j hij hlt
    refine hT (eq_zero_of_invariant hσ (Finset.univ.filter fun k => b' (w k) ≤ b' (w i))
      ⟨i, j, hij, by simp, by simpa using hlt⟩ T fun u hu => ?_)
    have key : ∀ k l, ((permGL F w * u * (permGL F w)⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) k l ≠
        (1 : Matrix (Fin r) (Fin r) F) k l → b' k < b' l := by
      intro k l
      obtain ⟨k, rfl⟩ := w.surjective k
      obtain ⟨l, rfl⟩ := w.surjective l
      rw [conj_permGL_apply, hone]
      intro h
      obtain ⟨-, h1, h2⟩ := hu k l h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      omega
    have h1 := hint u ⟨_, mem_blockTri_of_ne key⟩ (by simp)
    rw [hσ'.infl ⟨_, mem_blockTri_of_ne key⟩ fun k l hkl => by
      by_contra h0
      have := key k l h0
      omega] at h1
    exact h1.symm
  have B : ∀ i j, b' (w i) = b' (w j) → ¬ b i < b j := by
    intro i j hij hlt
    apply hT
    ext v
    refine hσ'.cusp (Finset.univ.filter fun k => b (w.symm k) ≤ b i)
      ⟨w i, w j, hij, by simp, by simpa using hlt⟩ (T v) fun u hu => ?_
    have key : ∀ k l, (((permGL F w)⁻¹ * u * permGL F w : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) k l ≠
        (1 : Matrix (Fin r) (Fin r) F) k l → b k < b l := by
      intro k l
      rw [← conj_permGL_apply w, ← hone]
      intro h
      obtain ⟨-, h1, h2⟩ := hu (w k) (w l) (by simpa [mul_assoc] using h)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply] at h1 h2
      omega
    have h1 := hint ⟨_, mem_blockTri_of_ne key⟩ u (by simp [mul_assoc])
    rw [hσ.infl ⟨_, mem_blockTri_of_ne key⟩ fun k l hkl => by
      by_contra h0
      have := key k l h0
      omega] at h1
    exact LinearMap.congr_fun h1 v
  intro i j
  constructor
  · intro h
    have := A i j h
    have := A j i h.symm
    omega
  · intro h
    have := B i j h
    have := B j i h.symm
    omega

end GlobalTheory.FinGL.BlockMatch
end

section

open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism

namespace GlobalTheory.FinGL.Bruhat

theorem exists_perm_rep_blockTri : ∀ (F : Type) [Field F] (r : ℕ) (b b' : Fin r → ℕ), Monotone b → Monotone b' → ∀ g : GL (Fin r) F, ∃ (w : Equiv.Perm (Fin r)) (p' : blockTri (κ := F) b') (p : blockTri (κ := F) b), g = (p' : GL (Fin r) F) * permGL F w * (p : GL (Fin r) F) := by
  intro F _ r b b' hb hb' g
  have hle : ∀ (c : Fin r → ℕ), Monotone c → ∀ u ∈ unip F r, u ∈ blockTri (κ := F) c := by
    intro c hc u hu
    rw [mem_blockTri]
    intro i j hij
    exact unip_lower hu (lt_of_not_ge fun h => absurd (hc h) (not_le.2 hij))
  obtain ⟨m, u, hu, u', hu', h⟩ := exists_decomp g
  have hdet : (Matrix.diagonal fun c => (m.2 c : F)).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun c _ => (m.2 c).ne_zero
  let d : GL (Fin r) F := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet
  have hdv : (d : Matrix (Fin r) (Fin r) F) = Matrix.diagonal fun c => (m.2 c : F) := rfl
  have hd : d ∈ blockTri (κ := F) b := by
    rw [mem_blockTri]
    intro i j hij
    rw [hdv]
    exact Matrix.diagonal_apply_ne _ (fun e => by rw [e] at hij; exact lt_irrefl _ hij)
  have hm : mono m = (permGL F m.1 : Matrix (Fin r) (Fin r) F) * (d : Matrix (Fin r) (Fin r) F) := by
    ext a c
    rw [hdv, Matrix.mul_diagonal, permGL_apply]
    by_cases e : a = m.1 c <;> simp [mono, e]
  refine ⟨m.1, ⟨u, hle b' hb' u hu⟩, ⟨d * u', Subgroup.mul_mem _ hd (hle b hb u' hu')⟩, Units.ext ?_⟩
  rw [h, hm]
  simp only [Units.val_mul, Matrix.mul_assoc]

end GlobalTheory.FinGL.Bruhat
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SecBasisTransfer

def chartPullUnLinComb {X X' Y Y' : Scheme.{0}} (L : LB X) (F : X' ⟶ X) {K : Type} [Fintype K]
    (ψ' : K → (Y' ⟶ X')) (ψ : K → (Y ⟶ X)) (ε : K → ℤ) (g : Y ⟶ Y') (hc : ∀ k, g ≫ ψ' k ≫ F = ψ k) :
    ChartPull (LB.LinComb L ψ ε) (LB.LinComb (L.pull F) ψ' ε) g :=
  have pt : ∀ k (y : Y), F (ψ' k (g y)) = ψ k y := fun k y => by
    rw [← hc k]; rfl
  have le : ∀ j : K → L.ι, LB.wchart L ψ j ≤ g ⁻¹ᵁ LB.wchart (L.pull F) ψ' (fun k _ => j k) :=
    fun j y hy => Set.mem_iInter.2 fun k => mem_pull.2 (by
      show F (ψ' k (g y)) ∈ L.U (j k)
      rw [pt k y]; exact Set.mem_iInter.1 hy k)
  { idx := fun j k _ => j k
    le := le
    g := fun y j j' hj hj' => by
      have m : g y ∈ LB.wchart (L.pull F) ψ' (fun k _ => j k) := le j hj
      have m' : g y ∈ LB.wchart (L.pull F) ψ' (fun k _ => j' k) := le j' hj'
      refine (gm_linComb L ψ ε (𝟙 Y) y j j' hj hj').trans
        (Eq.trans (Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) ?_)
          (gm_linComb (L.pull F) ψ' ε g y _ _ m m').symm)
      refine Eq.trans ?_ (gm_pull_g L F (g ≫ ψ' k) y (fun _ => j k) (fun _ => j' k)
        (Set.mem_iInter.1 m k) (Set.mem_iInter.1 m' k)).symm
      rw [Category.assoc, hc k, Category.id_comp] }

theorem sec_eq_of_f {Y : Scheme.{0}} {N : LB Y} {s t : LB.Sec N} (e : s.f = t.f) : s = t := by
  obtain ⟨a, ha⟩ := s
  obtain ⟨b, hb⟩ := t
  cases e
  rfl

theorem pullSec_pullSec {Y Y' : Scheme.{0}} {M : LB Y} {M' : LB Y'} {g : Y ⟶ Y'} {h : Y' ⟶ Y}
    (c' : ChartPull M M' g) (c : ChartPull M' M h) (hh : g ≫ h = 𝟙 Y) (hidx : ∀ j, c.idx (c'.idx j) = j)
    (s : LB.Sec M) : GlobalTheory.SecTwist.pullSec c' (GlobalTheory.SecTwist.pullSec c s) = s := by
  refine sec_eq_of_f (funext fun j => fn_ext fun y hy => ?_)
  have hy' : (𝟙 Y ≫ g) y ∈ M'.U (c'.idx j) := c'.le j hy
  rw [GlobalTheory.SecTwist.gs_pullSec c' _ (𝟙 Y) y j hy, GlobalTheory.SecTwist.gs_pullSec c s (𝟙 Y ≫ g) y _ hy',
    Category.id_comp, hh, hidx j]

theorem gs_liftHom {S : Scheme.{0}} (A : Over S) [GrpObj A] {T : Over S} {Z : Scheme.{0}}
    (f : Z ⟶ (T ⊗ A).left) (z : Z) (W : (T ⊗ A).left.Opens) (hz : f z ∈ W) (r : Γ(T.left, ⊤)) :
    gs f z W (liftHom A W r) = gs (f ≫ (fst T A).left) z ⊤ r :=
  (gs_res f z le_top hz _).trans (gs_pull f (fst T A).left z ⊤ trivial _)

def pullLin {S S' Z : Scheme.{0}} (A : Over S) [GrpObj A] (A' : Over S') [GrpObj A'] (L : LB A.left)
    (L' : LB A'.left) (k k' : ℤ) (y : Z ⟶ S) (x : Z ⟶ S') {h : (Over.mk x ⊗ A').left ⟶ (Over.mk y ⊗ A).left}
    (c : ChartPull (LPow A' L' k' (Over.mk x)) (LPow A L k (Over.mk y)) h)
    (hfst : h ≫ (fst (Over.mk y) A).left = (fst (Over.mk x) A').left) :
    SecM A L k (Over.mk y) →ₗ[Γ(Z, ⊤)] SecM A' L' k' (Over.mk x) where
  toFun m := SecM.ofSec A' (GlobalTheory.SecTwist.pullSec c (SecM.toSec A m))
  map_add' m₁ m₂ := Subtype.ext (funext fun i => fn_ext fun z hz => by
    have hz' : (𝟙 _ ≫ h) z ∈ (LPow A L k (Over.mk y)).U (c.idx i) := c.le i hz
    show gs (𝟙 _) z _ ((GlobalTheory.SecTwist.pullSec c (SecM.toSec A (m₁ + m₂))).f i) =
      gs (𝟙 _) z _ ((GlobalTheory.SecTwist.pullSec c (SecM.toSec A m₁)).f i +
        (GlobalTheory.SecTwist.pullSec c (SecM.toSec A m₂)).f i)
    rw [gs_add _ z _ hz, GlobalTheory.SecTwist.gs_pullSec c _ _ z i hz, GlobalTheory.SecTwist.gs_pullSec c _ _ z i hz,
      GlobalTheory.SecTwist.gs_pullSec c _ _ z i hz]
    exact gs_add _ z _ hz' _ _)
  map_smul' r m := Subtype.ext (funext fun i => fn_ext fun z hz => by
    have hz' : (𝟙 _ ≫ h) z ∈ (LPow A L k (Over.mk y)).U (c.idx i) := c.le i hz
    show gs (𝟙 _) z _ ((GlobalTheory.SecTwist.pullSec c (SecM.toSec A (r • m))).f i) =
      gs (𝟙 _) z _ (liftHom A' _ r * (GlobalTheory.SecTwist.pullSec c (SecM.toSec A m)).f i)
    rw [gs_mul _ z _ hz, GlobalTheory.SecTwist.gs_pullSec c _ _ z i hz, GlobalTheory.SecTwist.gs_pullSec c _ _ z i hz]
    refine (gs_mul _ z _ hz' (liftHom A _ r) _).trans (congrArg (· * _) ?_)
    rw [gs_liftHom A _ z _ hz' r, gs_liftHom A' (𝟙 _) z _ hz r, Category.assoc, hfst])

theorem li_span_map {R M M' : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M']
    [Module R M'] {I : Type*} (E : M ≃ₗ[R] M') (v : I → M) (hli : LinearIndependent R v)
    (hsp : Submodule.span R (Set.range v) = ⊤) :
    LinearIndependent R (E ∘ v) ∧ Submodule.span R (Set.range (E ∘ v)) = ⊤ := by
  refine ⟨hli.map' E.toLinearMap E.ker, ?_⟩
  rw [Set.range_comp, ← E.coe_toLinearMap, Submodule.span_image, hsp, Submodule.map_top, LinearEquiv.range]

theorem bases_transfer : ∀ {S S' : Scheme.{0}} (A : Over S) [GrpObj A] (Ag : Over S') [GrpObj Ag] (φ : Ag.left ⟶ A.left) (L : LB A.left), L.IsLB → ∀ (k : ℤ) (R : Type) [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S') (y : Spec (CommRingCat.of R) ⟶ S) (h : (Over.mk x ⊗ Ag).left ⟶ (Over.mk y ⊗ A).left) (hc : ∀ _ : Fin 1, (snd (Over.mk x) Ag).left ≫ φ = h ≫ (snd (Over.mk y) A).left), IsIso h → h ≫ (fst (Over.mk y) A).left = (fst (Over.mk x) Ag).left → ∀ (m : ℕ) (b : Fin m → LB.Sec (LPow A L k (Over.mk y))) (b' : Fin m → LB.Sec (LPow Ag (L.pull φ) k (Over.mk x))), (∀ i, b' i = GlobalTheory.SecTwist.pullSec (chartPullLinComb L φ (fun _ : Fin 1 => (snd (Over.mk x) Ag).left) (fun _ : Fin 1 => (snd (Over.mk y) A).left) (fun _ => k) h hc) (b i)) → LinearIndependent Γ((Over.mk y).left, ⊤) (fun i => (SecM.ofSec A (b i) : SecM A L k (Over.mk y))) → Submodule.span Γ((Over.mk y).left, ⊤) (Set.range fun i => (SecM.ofSec A (b i) : SecM A L k (Over.mk y))) = ⊤ → LinearIndependent Γ((Over.mk x).left, ⊤) (fun i => (SecM.ofSec Ag (b' i) : SecM Ag (L.pull φ) k (Over.mk x))) ∧ Submodule.span Γ((Over.mk x).left, ⊤) (Set.range fun i => (SecM.ofSec Ag (b' i) : SecM Ag (L.pull φ) k (Over.mk x))) = ⊤ := by
  intro S S' A _ Ag _ φ L _ k R _ x y h hc _ hfst m b b' hb' hli hsp
  let c := chartPullLinComb L φ (fun _ : Fin 1 => (snd (Over.mk x) Ag).left)
    (fun _ : Fin 1 => (snd (Over.mk y) A).left) (fun _ => k) h hc
  have hc' : ∀ _ : Fin 1, inv h ≫ (snd (Over.mk x) Ag).left ≫ φ = (snd (Over.mk y) A).left := fun _ => by
    rw [hc 0, IsIso.inv_hom_id_assoc]
  let c' := chartPullUnLinComb L φ (fun _ : Fin 1 => (snd (Over.mk x) Ag).left)
    (fun _ : Fin 1 => (snd (Over.mk y) A).left) (fun _ => k) (inv h) hc'
  have hfst' : inv h ≫ (fst (Over.mk x) Ag).left = (fst (Over.mk y) A).left := by
    rw [← hfst, IsIso.inv_hom_id_assoc]
  let F := pullLin A Ag L (L.pull φ) k k y x c hfst
  let G := pullLin Ag A (L.pull φ) L k k x y c' hfst'
  have GF : ∀ s : LB.Sec (LPow A L k (Over.mk y)),
      GlobalTheory.SecTwist.pullSec c' (GlobalTheory.SecTwist.pullSec c s) = s :=
    pullSec_pullSec c' c (IsIso.inv_hom_id h) (fun _ => rfl)
  have FG : ∀ s : LB.Sec (LPow Ag (L.pull φ) k (Over.mk x)),
      GlobalTheory.SecTwist.pullSec c (GlobalTheory.SecTwist.pullSec c' s) = s :=
    pullSec_pullSec c c' (IsIso.hom_inv_id h) (fun _ => rfl)
  let E : SecM A L k (Over.mk y) ≃ₗ[Γ(Spec (CommRingCat.of R), ⊤)] SecM Ag (L.pull φ) k (Over.mk x) :=
    { F with
      invFun := G
      left_inv := fun n => congrArg (SecM.ofSec A) (GF (SecM.toSec A n))
      right_inv := fun n => congrArg (SecM.ofSec Ag) (FG (SecM.toSec Ag n)) }
  have hv : (fun i => (SecM.ofSec Ag (b' i) : SecM Ag (L.pull φ) k (Over.mk x))) =
      E ∘ fun i => (SecM.ofSec A (b i) : SecM A L k (Over.mk y)) :=
    funext fun i => by rw [hb' i]; rfl
  have key := li_span_map E _ hli hsp
  rw [← hv] at key
  exact key

end GlobalTheory.SecBasisTransfer
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.exists_natural_excision_boundary_etaleNbhd : ∀ (q : ℕ) (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A), IsExcisionNbhd A A' f → ∀ (n i : ℤ), ∃ δ : Ht q (sp (Localization.Away (algebraMap A A' f))) n i →+ Ht q (sp A) (n + 1) i, Function.Exact δ (fun x : Ht q (sp A) (n + 1) i => (pull _ (spMap (algebraMap A (Localization.Away f))) _ _ x, pull _ (spMap (algebraMap A A')) _ _ x)) ∧ ∀ (A₂ : Type) [CommRing A₂] [Algebra A A₂] [Algebra A' A₂] [IsScalarTower A A' A₂], IsExcisionNbhd A A₂ f → ∀ (φ : Localization.Away (algebraMap A A' f) →+* Localization.Away (algebraMap A A₂ f)), φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) → ∀ (w : Ht q (sp (Localization.Away (algebraMap A A' f))) n i) (b : Ht q (sp (Localization.Away f)) n i), pull _ (spMap φ) _ _ w = pull _ (spMap (Localization.awayMap (algebraMap A A₂) f)) _ _ b → δ w = 0 := by
  first | (exact @GlobalTheory.EtC.excision_boundary_natural_refine) | (exact GlobalTheory.EtC.excision_boundary_natural_refine) | (intros; apply GlobalTheory.EtC.excision_boundary_natural_refine <;> assumption)
end
