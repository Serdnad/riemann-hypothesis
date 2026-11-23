module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle022
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle023
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricChainOneCouplingCosetOfPattern
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricChainSupportOneOfPattern
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

theorem _root_.GlobalTheory.T.matrix_block_column_vanishing_step : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.Pattern t → ∀ (j c : ℕ) (H : j + c = s) (q : Fin c), q.val + 1 ≤ S.ρ → q.val + 2 ≤ c → ∀ (x : Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin c) (XIx (Fin κ) t j ⊕ Fin (c + 1)) k), (∀ r, x (Sum.inl r) (Sum.inr q.succ) = 0) → ∀ w : XIx (Fin κ) t (j + 1) → k, (S.T t).Phi j c H (x + Matrix.of fun r s' => if s' = Sum.inr q.succ then Sum.elim w 0 r else 0) = if ∀ r, valuation k (((S.ϖ ^ (q.val + 2) : kˣ) : k) * w r) < 1 then (S.T t).Phi j c H x else 0 := by
  first | exact @GlobalTheory.SymChain.ExchangeCol.phi_add_col | exact GlobalTheory.SymChain.ExchangeCol.phi_add_col | (intros; apply GlobalTheory.SymChain.ExchangeCol.phi_add_col <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

theorem _root_.GlobalTheory.T.rootExchangeRowUnipotent_mem_sourceLevel : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.Pattern t → ∀ j c (H : j + 1 + c = s) (r : ℕ), c = 2 * r → ∀ u : XIx (Fin κ) t j → k, u ∈ box (XIx (Fin κ) t j) (S.ϖ ^ (r + 1)) → rowE (c + 1 + 1) (r + 1) u ∈ ((S.T t).lev j (c + 1 + 1) (by omega)).J := by
  first | exact @GlobalTheory.SymChain.rowE_mem_symLev_of_box | exact GlobalTheory.SymChain.rowE_mem_symLev_of_box | (intros; apply GlobalTheory.SymChain.rowE_mem_symLev_of_box <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

theorem _root_.GlobalTheory.T.symmetricChain_projected_level_of_pattern : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.Pattern t → S.PrLevel t := by
  first | exact @GlobalTheory.SymChain.PrImage.prLevel_of_pattern | exact GlobalTheory.SymChain.PrImage.prLevel_of_pattern | (intros; apply GlobalTheory.SymChain.PrImage.prLevel_of_pattern <;> assumption)
end

section

open ValuativeRel Matrix
open scoped Classical

noncomputable section
namespace GlobalTheory.SymChain.SymData
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

theorem exists_N_embX_inv_mul_mem_KOne :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ)
      (S : GlobalTheory.SymChain.SymData k s κ), ∀ x ∈ S.P.J, ∃ (n : GL (Fin κ ⊕ Fin (s + 1)) k) (γ : GL (Fin κ) k),
        n ∈ GlobalTheory.RootEx.N k (Fin κ) (s + 1) (S.ρ + 1) ∧ n ∈ S.P.J ∧ GlobalTheory.RootEx.embX (s + 1) γ ∈ S.P.J ∧
        (n * GlobalTheory.RootEx.embX (s + 1) γ)⁻¹ * x ∈ GlobalTheory.SplitWeil.KOne k (Fin κ ⊕ Fin (s + 1)) := by
  intro k _ _ _ _ s κ S x hx
  have mem_J_iff_pattern (g : GL (Fin κ ⊕ Fin (s + 1)) k) :
      g ∈ S.P.J ↔ g ∈ KO k _ ∧ ∀ a b, ¬ FreeTop S.ρ a b →
        valuation k (g.val a b - (1 : Matrix _ _ k) a b) < 1 := by
    rw [S.sym.1 g]
    constructor
    · rintro ⟨u, hu, γ, hγ, g₀, hg₀, hgb⟩
      refine ⟨⟨g₀, hg₀⟩, fun a b hab => ?_⟩
      rw [← hg₀, SymPattern.entry_lt_iff, hgb]
      exact SymPattern.pat_of_mul S.ρ u ((Radical.mem_N_iff u).mp hu) γ hγ a b hab
    · rintro ⟨⟨g₀, hg₀⟩, hpat⟩
      obtain ⟨u, hu, γ, hγ, he⟩ := SymPattern.exists_of_pat S.ρ
        (Matrix.GeneralLinearGroup.map (IsLocalRing.residue 𝒪[k]) g₀) (fun a b hab => by
          rw [← SymPattern.entry_lt_iff, hg₀]; exact hpat a b hab)
      exact ⟨u, (Radical.mem_N_iff u).mpr hu, γ, hγ, g₀, hg₀, he⟩
  obtain ⟨hxK, hpat⟩ := (mem_J_iff_pattern x).1 hx
  set M : Matrix (Fin κ ⊕ Fin (s + 1)) (Fin κ ⊕ Fin (s + 1)) k :=
    fun a b => if FreeTop S.ρ a b then x.val a b else (1 : Matrix _ _ k) a b with hMdef
  have hMax : MaxM (M - x.val) := by
    intro a b
    show valuation k ((if FreeTop S.ρ a b then x.val a b else (1 : Matrix _ _ k) a b) - x.val a b) < 1
    split_ifs with h
    · simp
    · rw [Valuation.map_sub_swap]; exact hpat a b h
  obtain ⟨u, hu, hMu⟩ := exists_mul_KOne hxK hMax
  have hMK : x * u ∈ KO k _ := mul_mem hxK (KOne_le_KO hu)
  have hpatM : ∀ a b, ¬ FreeTop S.ρ a b → (x * u).val a b = (1 : Matrix _ _ k) a b := by
    intro a b h; rw [hMu]; simp [hMdef, h]
  obtain ⟨n, hn, γ, hγ, e⟩ := GlobalTheory.SymPattern.exists_of_pat S.ρ (x * u) hpatM

  have hγv : ∀ i j, γ.val i j = (x * u).val (Sum.inl i) (Sum.inl j) := by
    intro i j
    rw [e, Units.val_mul, Radical.embX_val, GlobalTheory.SymPattern.mul_fromBlocks_inl]
    have e1 : ∀ t, n.val (Sum.inl i) (Sum.inl t) = (1 : Matrix (Fin κ) (Fin κ) k) i t := by
      intro t
      rw [hn _ _ (by simp [lev])]
      simp [Matrix.one_apply]
    simp only [e1]
    rw [← Matrix.mul_apply, Matrix.one_mul]
  have hγint : ∀ i j, γ.val i j ∈ 𝒪[k] := fun i j => by
    rw [hγv]; exact intM_of_mem_KO hMK _ _

  have hγK : γ ∈ KO k (Fin κ) := by
    let A₀ : Matrix (Fin κ) (Fin κ) 𝒪[k] := fun i j => ⟨γ.val i j, hγint i j⟩
    have hmap : (algebraMap 𝒪[k] k).mapMatrix A₀ = γ.val := by ext i j; rfl
    have hdet1 : γ.val.det = 1 := Radical.Uni.det (b := Fin.val) hγ
    have hdet : A₀.det = 1 := by
      apply Subtype.ext
      have := RingHom.map_det (algebraMap 𝒪[k] k) A₀
      rw [hmap, hdet1] at this
      simpa using this
    refine ⟨Matrix.nonsingInvUnit A₀ (by rw [hdet]; exact isUnit_one), ?_⟩
    ext i j
    rfl
  have hembK : embX (s + 1) γ ∈ KO k _ := by
    refine mem_KO.2 ⟨?_, ?_⟩
    · rw [Radical.embX_val]
      exact intM_fromBlocks.2 ⟨intM_of_mem_KO hγK, intM_zero, intM_zero, intM_one⟩
    · rw [← map_inv, Radical.embX_val]
      exact intM_fromBlocks.2 ⟨intM_of_mem_KO (inv_mem hγK), intM_zero, intM_zero, intM_one⟩
  have hnK : n ∈ KO k _ := by
    have : n = (x * u) * (embX (s + 1) γ)⁻¹ := by rw [e]; group
    rw [this]; exact mul_mem hMK (inv_mem hembK)
  refine ⟨n, γ, (Radical.mem_N_iff n).2 hn, ?_, ?_, ?_⟩
  · refine (mem_J_iff_pattern n).2 ⟨hnK, fun a b hab => ?_⟩
    have h1 := GlobalTheory.SymPattern.pat_of_mul S.ρ n hn 1 (fun r s _ => rfl) a b hab
    rw [map_one, mul_one] at h1
    rw [h1, sub_self, map_zero]; exact zero_lt_one
  · refine (mem_J_iff_pattern _).2 ⟨hembK, fun a b hab => ?_⟩
    have h1 := GlobalTheory.SymPattern.pat_of_mul S.ρ 1 (fun r s _ => rfl) γ hγ a b hab
    rw [one_mul] at h1
    rw [h1, sub_self, map_zero]; exact zero_lt_one
  · rw [← e, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
    exact inv_mem hu

end GlobalTheory.SymChain.SymData
end
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

namespace GlobalTheory.SymChain.IterPattern

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem intM_submatrix_iff {a b : Type*} (e : a ≃ b) (M : Matrix b b k) :
    IntM (M.submatrix e e) ↔ IntM M := by
  constructor
  · intro h i j
    simpa using h (e.symm i) (e.symm j)
  · intro h i j
    exact h (e i) (e j)

theorem symm_mem_KO_iff {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (e : a ≃ b)
    (g : GL b k) : (reGL e).symm g ∈ KO k a ↔ g ∈ KO k b := by
  rw [mem_KO, mem_KO, ← map_inv (reGL e).symm g, reGL_symm_val, reGL_symm_val,
    intM_submatrix_iff, intM_submatrix_iff]

theorem mem_reindex_J {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (P : GlobalTheory.StepData.TypeDatum k a)
    (e : a ≃ b) (g : GL b k) : g ∈ (P.reindex e).J ↔ (reGL e).symm g ∈ P.J := Iff.rfl

variable {ρ κ l j : ℕ} {t : Type}

theorem free_ll (x y : Ix (Fin κ ⊕ Fin l) t j) :
    FreeIx ρ (ixSucc _ t j (.inl x)) (ixSucc _ t j (.inl y)) ↔ FreeIx ρ x y := by
  rcases x with a | ⟨i, s⟩ <;> rcases y with b | ⟨i', s'⟩ <;> simp [ixSucc, FreeIx]

theorem free_lr (x : Ix (Fin κ ⊕ Fin l) t j) (s : t) :
    FreeIx ρ (ixSucc _ t j (.inl x)) (ixSucc _ t j (.inr s)) := by
  rcases x with a | ⟨i, s'⟩ <;> simp [ixSucc, FreeIx, (Fin.castSucc_lt_last _).le]

theorem not_free_rl (s : t) (y : Ix (Fin κ ⊕ Fin l) t j) :
    ¬ FreeIx ρ (ixSucc _ t j (.inr s)) (ixSucc _ t j (.inl y)) := by
  rcases y with b | ⟨i, s'⟩
  · simp [ixSucc, FreeIx]
  · simp [ixSucc, FreeIx]

theorem free_rr (s s' : t) : FreeIx ρ (ixSucc (Fin κ ⊕ Fin l) t j (.inr s)) (ixSucc _ t j (.inr s')) := by
  simp [ixSucc, FreeIx]

variable [Fintype t] [DecidableEq t]

theorem base_iff (P : GlobalTheory.StepData.TypeDatum k (Fin κ ⊕ Fin l))
    (hP : ∀ g : GL (Fin κ ⊕ Fin l) k, g ∈ P.J ↔
      g ∈ KO k _ ∧ ∀ a b, ¬ FreeTop ρ a b → valuation k (g.val a b - (1 : Matrix _ _ k) a b) < 1)
    (g : GL (Ix (Fin κ ⊕ Fin l) t 0) k) :
    g ∈ (P.reindex (ixZero _ t)).J ↔
      g ∈ KO k _ ∧ ∀ a b, ¬ FreeIx ρ a b → valuation k (g.val a b - (1 : Matrix _ _ k) a b) < 1 := by
  have hz : ∀ a b : Fin κ ⊕ Fin l, FreeIx ρ (ixZero _ t a) (ixZero _ t b) ↔ FreeTop ρ a b := fun _ _ => Iff.rfl
  rw [mem_reindex_J, hP, symm_mem_KO_iff]
  simp only [reGL_symm_val]
  refine and_congr_right fun _ => ⟨fun h a b hab => ?_, fun h a b hab => ?_⟩
  · obtain ⟨a, rfl⟩ := (ixZero _ t).surjective a
    obtain ⟨b, rfl⟩ := (ixZero _ t).surjective b
    have := h a b (fun hf => hab ((hz a b).2 hf))
    simpa [Matrix.one_apply] using this
  · have := h _ _ (fun hf => hab ((hz a b).1 hf))
    simpa [Matrix.one_apply] using this

theorem step_iff (Q : GlobalTheory.StepData.TypeDatum k (Ix (Fin κ ⊕ Fin l) t j))
    (μ : kˣ →* ℂˣ) (hμ : IsTame μ)
    (hQ : ∀ g : GL (Ix (Fin κ ⊕ Fin l) t j) k, g ∈ Q.J ↔
      g ∈ KO k _ ∧ ∀ a b, ¬ FreeIx ρ a b → valuation k (g.val a b - (1 : Matrix _ _ k) a b) < 1)
    (g : GL (Ix (Fin κ ⊕ Fin l) t (j + 1)) k) :
    g ∈ ((Q.step t μ hμ).reindex (ixSucc _ t j)).J ↔
      g ∈ KO k _ ∧ ∀ a b, ¬ FreeIx ρ a b → valuation k (g.val a b - (1 : Matrix _ _ k) a b) < 1 := by
  rw [mem_reindex_J, TypeDatum.step_J, TypeDatum.mem_stepJ_iff, symm_mem_KO_iff]
  constructor
  · rintro ⟨hK, ⟨g', hg', hval⟩, hC⟩
    refine ⟨hK, fun a b hab => ?_⟩
    obtain ⟨a, rfl⟩ := (ixSucc _ t j).surjective a
    obtain ⟨b, rfl⟩ := (ixSucc _ t j).surjective b
    rcases a with x | s <;> rcases b with y | s'
    ·
      have hxy : ¬ FreeIx ρ x y := fun h => hab ((free_ll x y).2 h)
      have hold := ((hQ g').1 hg').2 x y hxy
      have hentry : g'.val x y = g.val (ixSucc _ t j (.inl x)) (ixSucc _ t j (.inl y)) := by
        rw [hval, reGL_symm_val]; rfl
      rw [hentry] at hold
      simpa [Matrix.one_apply] using hold
    · exact absurd (free_lr x s') hab
    ·
      have hlow := hC s y
      simpa [Matrix.one_apply, reGL_symm_val, Matrix.toBlocks₂₁] using hlow
    · exact absurd (free_rr s s') hab
  · rintro ⟨hK, hfree⟩
    have hK' : (reGL (ixSucc _ t j)).symm g ∈ KO k _ := (symm_mem_KO_iff _ g).2 hK
    have hC : MaxM ((reGL (ixSucc _ t j)).symm g).val.toBlocks₂₁ := by
      intro s y
      have hnf := hfree _ _ (not_free_rl s y)
      simpa [Matrix.one_apply, reGL_symm_val, Matrix.toBlocks₂₁] using hnf
    refine ⟨hK, ?_, hC⟩
    obtain ⟨⟨g', hg'K, hg'val⟩, -⟩ := exists_diag_blocks hK' hC
    refine ⟨g', (hQ g').2 ⟨hg'K, fun x y hxy => ?_⟩, hg'val⟩
    have hnf := hfree _ _ (fun h => hxy ((free_ll x y).1 h))
    have hentry : g'.val x y = g.val (ixSucc _ t j (.inl x)) (ixSucc _ t j (.inl y)) := by
      rw [hg'val, reGL_symm_val]; rfl
    rw [hentry]
    simpa [Matrix.one_apply] using hnf

theorem iter_iff (P : GlobalTheory.StepData.TypeDatum k (Fin κ ⊕ Fin l))
    (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j))
    (hP : ∀ g : GL (Fin κ ⊕ Fin l) k, g ∈ P.J ↔
      g ∈ KO k _ ∧ ∀ a b, ¬ FreeTop ρ a b → valuation k (g.val a b - (1 : Matrix _ _ k) a b) < 1)
    (j : ℕ) (g : GL (Ix (Fin κ ⊕ Fin l) t j) k) :
    g ∈ (P.iter t μ hμ j).J ↔
      g ∈ KO k _ ∧ ∀ a b, ¬ FreeIx ρ a b → valuation k (g.val a b - (1 : Matrix _ _ k) a b) < 1 := by
  induction j with
  | zero =>
    rw [TypeDatum.iter_zero]
    exact base_iff P hP g
  | succ j ih =>
    rw [TypeDatum.iter_succ]
    exact step_iff _ (μ (j + 1)) (hμ _) ih g

end GlobalTheory.SymChain.IterPattern

theorem GlobalTheory.SymChain.pattern_iter (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : GlobalTheory.SymChain.SymData k s κ)
    (t : Type) [Fintype t] [DecidableEq t] :
    S.Pattern t := by
  intro j g
  have hP : ∀ x : GL (Fin κ ⊕ Fin (s + 1)) k, x ∈ S.P.J ↔
      x ∈ KO k _ ∧ ∀ a b, ¬ FreeTop S.ρ a b →
        valuation k (x.val a b - (1 : Matrix _ _ k) a b) < 1 := by
    intro x
    rw [S.sym.1 x]
    constructor
    · rintro ⟨u, hu, γ, hγ, x₀, hx₀, hxb⟩
      refine ⟨⟨x₀, hx₀⟩, fun a b hab => ?_⟩
      rw [← hx₀, GlobalTheory.SymPattern.entry_lt_iff, hxb]
      exact GlobalTheory.SymPattern.pat_of_mul S.ρ u ((Radical.mem_N_iff u).mp hu) γ hγ a b hab
    · rintro ⟨⟨x₀, hx₀⟩, hpat⟩
      obtain ⟨u, hu, γ, hγ, he⟩ := GlobalTheory.SymPattern.exists_of_pat S.ρ
        (Matrix.GeneralLinearGroup.map (IsLocalRing.residue 𝒪[k]) x₀) (fun a b hab => by
          rw [← GlobalTheory.SymPattern.entry_lt_iff, hx₀]
          exact hpat a b hab)
      exact ⟨u, (Radical.mem_N_iff u).mpr hu, γ, hγ, x₀, hx₀, he⟩
  exact IterPattern.iter_iff S.P S.μ S.tame hP j g
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

theorem _root_.GlobalTheory.T.mem_level_iff_symmetricPosition_entry_pattern : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : SymData k s κ) (g : GL (Fin κ ⊕ Fin (s + 1)) k), g ∈ S.P.J ↔ g ∈ KO k _ ∧ ∀ a b, ¬ FreeTop S.ρ a b → valuation k (g.val a b - (1 : Matrix _ _ k) a b) < 1 := by
  first | exact @GlobalTheory.SymChain.SymData.mem_J_iff_pattern | exact GlobalTheory.SymChain.SymData.mem_J_iff_pattern | (intros; apply GlobalTheory.SymChain.SymData.mem_J_iff_pattern <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

theorem _root_.GlobalTheory.T.symmetricChain_oneLatticeClass : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.OneClass t ν := by
  first | exact @GlobalTheory.SymChain.LatClass.oneClass_symChain | exact GlobalTheory.SymChain.LatClass.oneClass_symChain | (intros; apply GlobalTheory.SymChain.LatClass.oneClass_symChain <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

theorem _root_.GlobalTheory.T.symmetricChain_oneCoupling_coset_of_pattern : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.Pattern t → S.OneCoupling t := by
  first | exact @GlobalTheory.SymChain.oneCoupling | exact GlobalTheory.SymChain.oneCoupling | (intros; apply GlobalTheory.SymChain.oneCoupling <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

theorem _root_.GlobalTheory.T.symmetricChain_supportOne_of_pattern : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.Pattern t → S.SupportOne t := by
  first | exact @GlobalTheory.SymSupport.supportOne_of_pattern | exact GlobalTheory.SymSupport.supportOne_of_pattern | (intros; apply GlobalTheory.SymSupport.supportOne_of_pattern <;> assumption)
end
