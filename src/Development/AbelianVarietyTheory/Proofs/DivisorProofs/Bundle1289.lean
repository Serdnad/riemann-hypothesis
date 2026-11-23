module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.BoxDecomp

open Topology Filter

variable {F : Type} [Field F] [NumberField F] {v : Pl (F := F)}

theorem ball_mem_nhds_zero (v : Pl (F := F)) (N : ℕ) :
    {y : Fv F v | Valued.v y ≤ WithZero.exp (-(N : ℤ))} ∈ 𝓝 (0 : Fv F v) := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  set p : Fv F v := (π : v.adicCompletion F) with hp
  have hpv : Valued.v p = WithZero.exp (-1) := by
    rw [hp, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]
  have hrv : Valued.v (p ^ N) = WithZero.exp (-(N : ℤ)) := by
    rw [map_pow, hpv, ← WithZero.exp_nsmul]; congr 1; simp
  have hr : Valued.v (p ^ N) ≠ 0 := by rw [hrv]; exact WithZero.exp_ne_zero
  rw [Valued.mem_nhds_zero]
  have h' : (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).restrict (p ^ N) ≠ 0 := by simpa using hr
  refine ⟨Units.mk0 _ h', fun y hy => ?_⟩
  have := (Valuation.restrict_lt_iff _).1 hy
  rw [hrv] at this
  exact le_of_lt this

theorem exists_ball_subset (v : Pl (F := F)) {s : Set (Fv F v)} (hs : s ∈ 𝓝 (0 : Fv F v)) :
    ∃ N : ℕ, {y : Fv F v | Valued.v y ≤ WithZero.exp (-(N : ℤ))} ⊆ s := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hs
  set g : WithZero (Multiplicative ℤ) := MonoidWithZeroHom.ValueGroup₀.embedding γ.1 with hg
  have hg0 : g ≠ 0 := by
    rw [hg]; exact (map_ne_zero _).2 γ.ne_zero
  refine ⟨(-(WithZero.log g)).toNat + 1, fun y hy => hγ ?_⟩
  show (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).restrict y < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding]
  refine lt_of_le_of_lt hy ?_
  have hlt : WithZero.exp (-((((-(WithZero.log g)).toNat + 1 : ℕ)) : ℤ)) < WithZero.exp (WithZero.log g) :=
    WithZero.exp_lt_exp.2 (by omega)
  rwa [WithZero.exp_log hg0] at hlt

def B (v : Pl (F := F)) (κ : Type) (N : ℕ) : Set (κ → Fv F v) :=
  {x | ∀ i, Valued.v (x i) ≤ WithZero.exp (-(N : ℤ))}

theorem B_anti {κ : Type} {N M : ℕ} (h : N ≤ M) : B v κ M ⊆ B v κ N := fun x hx i =>
  (hx i).trans (WithZero.exp_le_exp.2 (by omega))

theorem zero_mem_B (κ : Type) (N : ℕ) : (0 : κ → Fv F v) ∈ B v κ N := fun i => by simp

theorem sub_mem_B {κ : Type} {N : ℕ} {x y : κ → Fv F v} (hx : x ∈ B v κ N) (hy : y ∈ B v κ N) :
    x - y ∈ B v κ N := fun i =>
  (Valuation.map_sub _ _ _).trans (max_le (hx i) (hy i))

theorem add_mem_B {κ : Type} {N : ℕ} {x y : κ → Fv F v} (hx : x ∈ B v κ N) (hy : y ∈ B v κ N) :
    x + y ∈ B v κ N := fun i =>
  (Valuation.map_add _ _ _).trans (max_le (hx i) (hy i))

theorem neg_mem_B {κ : Type} {N : ℕ} {x : κ → Fv F v} (hx : x ∈ B v κ N) : -x ∈ B v κ N := fun i => by
  simpa using hx i

theorem B_mem_nhds (κ : Type) [Fintype κ] (N : ℕ) : B v κ N ∈ 𝓝 (0 : κ → Fv F v) := by
  have : B v κ N = Set.pi Set.univ fun _ => {y : Fv F v | Valued.v y ≤ WithZero.exp (-(N : ℤ))} := by
    ext x; simp [B]
  rw [this]
  exact set_pi_mem_nhds Set.finite_univ fun i _ => ball_mem_nhds_zero v N

theorem exists_B_subset (κ : Type) [Fintype κ] {s : Set (κ → Fv F v)} (hs : s ∈ 𝓝 (0 : κ → Fv F v)) :
    ∃ N : ℕ, B v κ N ⊆ s := by
  rw [nhds_pi, Filter.mem_pi] at hs
  obtain ⟨I, -, t, ht, hts⟩ := hs
  choose Nf hNf using fun i => exists_ball_subset v (ht i)
  refine ⟨Finset.univ.sup Nf, fun x hx => hts fun i _ => hNf i ?_⟩
  exact (hx i).trans (WithZero.exp_le_exp.2 (by
    have := Finset.le_sup (f := Nf) (Finset.mem_univ i); omega))

theorem isOpen_box (κ : Type) [Fintype κ] (N : ℕ) (c : κ → Fv F v) :
    IsOpen {x : κ → Fv F v | x - c ∈ B v κ N} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have ht : Tendsto (fun y : κ → Fv F v => y - x) (𝓝 x) (𝓝 0) := by
    simpa using (continuous_sub_right x).tendsto x
  refine Filter.mem_of_superset (ht (B_mem_nhds κ N)) fun y hy => ?_
  have : y - c = (y - x) + (x - c) := by abel
  show y - c ∈ B v κ N
  rw [this]; exact add_mem_B hy hx

theorem exists_invariant {κ : Type} [Fintype κ] {φ : (κ → Fv F v) → ℂ} (hφ : φ ∈ SB (κ → Fv F v)) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ y u, u ∈ B v κ N → φ (y + u) = φ y := by
  have hloc : ∀ x : κ → Fv F v, ∃ N : ℕ, ∀ u ∈ B v κ N, φ (x + u) = φ x := by
    intro x
    have hlc : IsLocallyConstant fun u : κ → Fv F v => φ (x + u) :=
      hφ.1.comp_continuous (continuous_const_add x)
    have hO : {u : κ → Fv F v | φ (x + u) = φ x} ∈ 𝓝 (0 : κ → Fv F v) :=
      (hlc.isOpen_fiber (φ x)).mem_nhds (by simp)
    obtain ⟨N, hN⟩ := exists_B_subset κ hO
    exact ⟨N, fun u hu => hN hu⟩
  choose Nx hNx using hloc
  have hK : IsCompact (tsupport φ) := hφ.2
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x => {y : κ → Fv F v | y - x ∈ B v κ (Nx x)})
    (fun x => isOpen_box κ (Nx x) x) (fun y _ => Set.mem_iUnion.2 ⟨y, by simpa using zero_mem_B κ (Nx y)⟩)
  refine ⟨t.sup Nx, fun N hN y u hu => ?_⟩
  have hsub : ∀ x ∈ t, u ∈ B v κ (Nx x) := fun x hx =>
    B_anti ((Finset.le_sup (f := Nx) hx).trans hN) hu
  by_cases hy : ∃ x ∈ t, y - x ∈ B v κ (Nx x)
  · obtain ⟨x, hx, hyx⟩ := hy
    have h1 : φ (y + u) = φ x := by
      have := hNx x ((y - x) + u) (add_mem_B hyx (hsub x hx))
      rwa [show x + ((y - x) + u) = y + u by abel] at this
    have h2 : φ y = φ x := by
      have := hNx x (y - x) hyx
      rwa [show x + (y - x) = y by abel] at this
    rw [h1, h2]
  · push_neg at hy
    have hyK : y ∉ tsupport φ := fun hyK => by
      obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (ht hyK)
      exact hy x hx hyx
    have hyuK : y + u ∉ tsupport φ := fun hyK => by
      obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (ht hyK)
      refine hy x hx ?_
      have := sub_mem_B hyx (hsub x hx)
      rwa [show y + u - x - u = y - x by abel] at this
    rw [image_eq_zero_of_notMem_tsupport hyK, image_eq_zero_of_notMem_tsupport hyuK]

def BG (v : Pl (F := F)) (κ : Type) (N : ℕ) : AddSubgroup (κ → Fv F v) where
  carrier := B v κ N
  add_mem' := add_mem_B
  zero_mem' := zero_mem_B κ N
  neg_mem' := neg_mem_B

theorem mk_eq_iff {κ : Type} {N : ℕ} {x c : κ → Fv F v} :
    (x : (κ → Fv F v) ⧸ BG v κ N) = c ↔ x - c ∈ B v κ N := by
  rw [QuotientAddGroup.eq]
  constructor
  · intro h
    have := neg_mem_B h
    rwa [show -(-x + c) = x - c by abel] at this
  · intro h
    have := neg_mem_B h
    rwa [show -(x - c) = -x + c by abel] at this

theorem mem_span_boxes (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ : Type) [Fintype κ]
    (φ : (κ → Fv F v) → ℂ) : φ ∈ SB (κ → Fv F v) → ∃ N₀ : ℕ, ∀ N ≥ N₀, φ ∈ Submodule.span ℂ
      (Set.range fun c : κ → Fv F v => Set.indicator
        {x : κ → Fv F v | ∀ i, Valued.v (x i - c i) ≤ WithZero.exp (-(N : ℤ))} (1 : (κ → Fv F v) → ℂ)) := by
  classical
  intro hφ
  obtain ⟨N₀, hN₀⟩ := exists_invariant hφ
  refine ⟨N₀, fun N hN => ?_⟩
  have hK : IsCompact (tsupport φ) := hφ.2
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun c => {y : κ → Fv F v | y - c ∈ B v κ N})
    (fun c => isOpen_box κ N c) (fun y _ => Set.mem_iUnion.2 ⟨y, by simpa using zero_mem_B κ N⟩)
  set Q : Finset ((κ → Fv F v) ⧸ BG v κ N) := t.image (QuotientAddGroup.mk (s := BG v κ N)) with hQ
  have heq : φ = ∑ q ∈ Q, φ q.out • Set.indicator
      {x : κ → Fv F v | ∀ i, Valued.v (x i - q.out i) ≤ WithZero.exp (-(N : ℤ))} (1 : (κ → Fv F v) → ℂ) := by
    funext x
    have hterm : ∀ q : (κ → Fv F v) ⧸ BG v κ N, (φ q.out • Set.indicator
        {x : κ → Fv F v | ∀ i, Valued.v (x i - q.out i) ≤ WithZero.exp (-(N : ℤ))} (1 : (κ → Fv F v) → ℂ)) x =
        if (x : (κ → Fv F v) ⧸ BG v κ N) = q then φ q.out else 0 := by
      intro q
      have hm : (x ∈ {x : κ → Fv F v | ∀ i, Valued.v (x i - q.out i) ≤ WithZero.exp (-(N : ℤ))}) ↔
          (x : (κ → Fv F v) ⧸ BG v κ N) = q := by
        rw [← QuotientAddGroup.out_eq' q, mk_eq_iff, QuotientAddGroup.out_eq']
        rfl
      rw [Pi.smul_apply, Set.indicator_apply]
      by_cases h : (x : (κ → Fv F v) ⧸ BG v κ N) = q
      · rw [if_pos (hm.2 h), if_pos h, Pi.one_apply, smul_eq_mul, mul_one]
      · rw [if_neg (fun h' => h (hm.1 h')), if_neg h, smul_zero]
    rw [Finset.sum_apply]
    simp_rw [hterm]
    rw [Finset.sum_ite_eq]
    split_ifs with hx
    · set q : (κ → Fv F v) ⧸ BG v κ N := (x : (κ → Fv F v) ⧸ BG v κ N)
      have hqx : q.out - x ∈ B v κ N := mk_eq_iff.1 (QuotientAddGroup.out_eq' q)
      have := hN₀ N hN x (q.out - x) hqx
      rw [show x + (q.out - x) = q.out by abel] at this
      exact this.symm
    · have hxK : x ∉ tsupport φ := fun hxK => by
        obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.1 (ht hxK)
        have hcQ : (c : (κ → Fv F v) ⧸ BG v κ N) ∈ Q :=
          Finset.mem_image_of_mem (QuotientAddGroup.mk (s := BG v κ N)) hc
        rw [← mk_eq_iff.2 hxc] at hcQ
        exact hx hcQ
      exact image_eq_zero_of_notMem_tsupport hxK
  rw [heq]
  exact Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨q.out, rfl⟩)

end GlobalTheory.BoxDecomp
end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.DoublingEv

def conjMap {X Y : Type} (T : (X → ℂ) →ₗ[ℂ] (Y → ℂ)) : (X → ℂ) →ₗ[ℂ] (Y → ℂ) where
  toFun φ := star (T (star φ))
  map_add' φ φ' := by rw [star_add, map_add (f := _), star_add]
  map_smul' c φ := by rw [star_smul, map_smul, star_smul, star_star]; rfl

theorem conjMap_apply {X Y : Type} (T : (X → ℂ) →ₗ[ℂ] (Y → ℂ)) (φ : X → ℂ) :
    conjMap T φ = star (T (star φ)) := rfl

variable {R : Type}

def partR {κ κ' κ₁' : Type} (T : ((κ' → R) → ℂ) →ₗ[ℂ] ((κ₁' → R) → ℂ)) :
    ((κ ⊕ κ' → R) → ℂ) →ₗ[ℂ] ((κ ⊕ κ₁' → R) → ℂ) where
  toFun Φ s := T (fun x₂ => Φ (Sum.elim (s ∘ Sum.inl) x₂)) (s ∘ Sum.inr)
  map_add' Φ Ψ := by funext s; exact congrFun (map_add T (fun x₂ => Φ (Sum.elim (s ∘ Sum.inl) x₂)) (fun x₂ => Ψ (Sum.elim (s ∘ Sum.inl) x₂))) _
  map_smul' c Φ := by funext s; exact congrFun (map_smul T c (fun x₂ => Φ (Sum.elim (s ∘ Sum.inl) x₂))) _

def partL {κ κ₁ κ' : Type} (T : ((κ → R) → ℂ) →ₗ[ℂ] ((κ₁ → R) → ℂ)) :
    ((κ ⊕ κ' → R) → ℂ) →ₗ[ℂ] ((κ₁ ⊕ κ' → R) → ℂ) where
  toFun Φ s := T (fun x₁ => Φ (Sum.elim x₁ (s ∘ Sum.inr))) (s ∘ Sum.inl)
  map_add' Φ Ψ := by funext s; exact congrFun (map_add T (fun x₁ => Φ (Sum.elim x₁ (s ∘ Sum.inr))) (fun x₁ => Ψ (Sum.elim x₁ (s ∘ Sum.inr)))) _
  map_smul' c Φ := by funext s; exact congrFun (map_smul T c (fun x₁ => Φ (Sum.elim x₁ (s ∘ Sum.inr)))) _

theorem partR_apply {κ κ' κ₁' : Type} (T : ((κ' → R) → ℂ) →ₗ[ℂ] ((κ₁' → R) → ℂ)) (Φ : (κ ⊕ κ' → R) → ℂ)
    (s : κ ⊕ κ₁' → R) : partR (κ := κ) T Φ s = T (fun x₂ => Φ (Sum.elim (s ∘ Sum.inl) x₂)) (s ∘ Sum.inr) := rfl

theorem partL_apply {κ κ₁ κ' : Type} (T : ((κ → R) → ℂ) →ₗ[ℂ] ((κ₁ → R) → ℂ)) (Φ : (κ ⊕ κ' → R) → ℂ)
    (s : κ₁ ⊕ κ' → R) : partL (κ' := κ') T Φ s = T (fun x₁ => Φ (Sum.elim x₁ (s ∘ Sum.inr))) (s ∘ Sum.inl) := rfl

def evDbl {κ κ₁ : Type} (e : ((κ → R) → ℂ) →ₗ[ℂ] ((κ₁ → R) → ℂ)) :
    ((κ ⊕ κ → R) → ℂ) →ₗ[ℂ] ((κ₁ ⊕ κ₁ → R) → ℂ) :=
  partL e ∘ₗ partR (conjMap e)

theorem evDbl_apply {κ κ₁ : Type} (e : ((κ → R) → ℂ) →ₗ[ℂ] ((κ₁ → R) → ℂ)) (Φ : (κ ⊕ κ → R) → ℂ)
    (s : κ₁ ⊕ κ₁ → R) : evDbl e Φ s =
      e (fun x₁ => conjMap e (fun x₂ => Φ (Sum.elim x₁ x₂)) (s ∘ Sum.inr)) (s ∘ Sum.inl) := by
  simp only [evDbl, LinearMap.comp_apply, partL_apply, partR_apply, Sum.elim_comp_inl, Sum.elim_comp_inr]

theorem evDbl_boxFun {κ κ₁ : Type} (e : ((κ → R) → ℂ) →ₗ[ℂ] ((κ₁ → R) → ℂ)) (φ₁ φ₂ : (κ → R) → ℂ) :
    evDbl e (boxFun φ₁ φ₂) = boxFun (e φ₁) (conjMap e φ₂) := by
  funext s
  rw [evDbl_apply]
  have h1 : ∀ x₁ : κ → R, (fun x₂ => boxFun φ₁ φ₂ (Sum.elim x₁ x₂)) = φ₁ x₁ • φ₂ := fun x₁ => by
    funext x₂; simp [boxFun]
  have h2 : (fun x₁ => conjMap e (fun x₂ => boxFun φ₁ φ₂ (Sum.elim x₁ x₂)) (s ∘ Sum.inr)) =
      conjMap e φ₂ (s ∘ Sum.inr) • φ₁ := by
    funext x₁; rw [h1, map_smul]; simp [mul_comm]
  rw [h2, map_smul]
  simp [boxFun, mul_comm]

section Tame

open scoped Classical

variable (F : Type) [Field F] [NumberField F]

def IsTame {κ κ' : Type} [Fintype κ] [Fintype κ'] (T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)) : Prop :=
  ∀ g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F), ∃ (ι : Type) (_ : Fintype ι)
    (P : ι → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] SchwartzMap (κ' → mixedEmbedding.mixedSpace F) ℂ)
    (g' : ι → (κ' → FiniteAdeleRing (𝓞 F) F) → ℂ), (∀ j, g' j ∈ SB (κ' → FiniteAdeleRing (𝓞 F) F)) ∧
      ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, T (pureA F f g) = ∑ j, pureA F (P j f) (g' j)

variable {F}

theorem IsTame.comp {κ κ' κ'' : Type} [Fintype κ] [Fintype κ'] [Fintype κ'']
    {T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)} {T' : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ'' → AF F) → ℂ)}
    (hT : IsTame F T) (hT' : IsTame F T') : IsTame F (T' ∘ₗ T) := by
  intro g hg
  obtain ⟨ι, _, P, g', hg', hP⟩ := hT g hg
  choose ι' inst P' g'' hg'' hP' using fun j => hT' (g' j) (hg' j)
  letI : ∀ j, Fintype (ι' j) := inst
  refine ⟨Σ j, ι' j, inferInstance, fun p => (P' p.1 p.2).comp (P p.1), fun p => g'' p.1 p.2,
    fun p => hg'' p.1 p.2, fun f => ?_⟩

  rw [LinearMap.comp_apply, hP, map_sum, Fintype.sum_sigma]
  exact Finset.sum_congr rfl fun j _ => hP' j (P j f)

theorem IsTame.mapsTo {κ κ' : Type} [Fintype κ] [Fintype κ'] {T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)}
    (hT : IsTame F T) : ∀ φ ∈ schA F κ, T φ ∈ schA F κ' := by
  intro φ hφ
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    obtain ⟨ι, _, P, g', hg', hP⟩ := hT g hg
    rw [hP]
    exact Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨P j f, g' j, hg' j, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem IsTame.comp_adm {κ κ' : Type} [Fintype κ] [Fintype κ'] {T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)}
    (hT : IsTame F T) {l : ((κ' → AF F) → ℂ) →ₗ[ℂ] ℂ} (hl : l ∈ (adeleClass F).adm κ') :
    l ∘ₗ T ∈ (adeleClass F).adm κ := by
  intro g hg
  obtain ⟨ι, _, P, g', hg', hP⟩ := hT g hg
  choose L hL using fun j => hl (g' j) (hg' j)
  refine ⟨∑ j, (L j).comp (P j), fun f => ?_⟩

  rw [LinearMap.comp_apply, hP, map_sum, ContinuousLinearMap.sum_apply]
  exact Finset.sum_congr rfl fun j _ => hL j (P j f)

end Tame

end GlobalTheory.DoublingEv
end
end

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.HeisSplit

theorem schr_add_of_orth {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (a b : (κ → R) × (κ → R)) (h1 : a.1 ⬝ᵥ b.2 = 0) (h2 : b.1 ⬝ᵥ a.2 = 0) (φ : (κ → R) → ℂ) :
    schr ψ (a + b) φ = schr ψ a (schr ψ b φ) := by
  funext x
  simp only [schr, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add, h1, h2]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul, add_assoc x]
  congr 2
  ring

theorem dot_eq_zero {R : Type} [CommRing R] {κ : Type} [Fintype κ] (e : R) (a c : κ → R) (h : e • a = 0) :
    a ⬝ᵥ (e • c) = 0 := by
  rw [dotProduct_smul, ← smul_dotProduct, h, zero_dotProduct]

section

variable (F : Type) [Field F] [NumberField F]

noncomputable def finAd (z : Af F) : AF F := ((0 : InfiniteAdeleRing F), z)

theorem finAd_mul (x : AF F) : finAd F x.2 * finAd F 1 = x * finAd F 1 := by
  refine Prod.ext ?_ ?_
  · show (0 : InfiniteAdeleRing F) * 0 = x.1 * 0
    simp
  · rfl

theorem finAd_idem : finAd F 1 * finAd F 1 = finAd F 1 := by
  refine Prod.ext ?_ ?_
  · show (0 : InfiniteAdeleRing F) * 0 = 0
    simp
  · show (1 : Af F) * 1 = 1
    simp

theorem evI_finAd : evI F (finAd F 1) = 0 := by
  exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)

theorem mul_finAd_of (t : AF F) (ht : evI F t = 0) : t * finAd F 1 = t := by
  have h : t.1 = 0 := (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).1 ht
  refine Prod.ext ?_ ?_
  · show t.1 * 0 = t.1
    simp [h]
  · show t.2 * 1 = t.2
    simp

theorem schr_pureA [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ) {κ : Type} [Fintype κ] (c : (κ → AF F) × (κ → AF F))
    (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (h : (κ → Af F) → ℂ) :
    schr ψ (finAd F 1 • c) (pureA F f h) =
      pureA F f (fun z => schr ψ (finAd F 1 • c) (fun x => h fun i => (x i).2) fun i => finAd F (z i)) := by
  funext x
  have e1 : (fun i => finAd F (x i).2) ⬝ᵥ (finAd F 1 • c).2 = x ⬝ᵥ (finAd F 1 • c).2 := by
    simp only [dotProduct, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, ← mul_assoc, finAd_mul]
  have e2 : ∀ i, ((x + (finAd F 1 • c).1) i).1 = (x i).1 := by
    intro i
    show (x i).1 + 0 * (c.1 i).1 = (x i).1
    simp
  have e3 : ∀ i, (((fun i => finAd F (x i).2) + (finAd F 1 • c).1) i).2 = ((x + (finAd F 1 • c).1) i).2 := fun i => rfl
  simp only [schr, pureA, e1, e2, e3]
  ring

end

theorem rho_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (α β κ : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (ψ : AddChar (AF F) ℂ)
    (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E)) (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ),
    ∀ w : Matrix α β (AE F E),
    ∃ (u : Matrix α β (AE F E)) (H : ((κ → Af F) → ℂ) → (κ → Af F) → ℂ), At (evI F) u ∧
      ∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) →
        ∀ (f f₁ : SInf F κ) (h : (κ → Af F) → ℂ),
          (∀ h' : (κ → Af F) → ℂ, d.rho ψ (actB (cA σ) g u) (pureA F f h') = pureA F f₁ h') →
            d.rho ψ (actB (cA σ) g w) (pureA F f h) = pureA F f₁ (H h) := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ ψ JA JB d w
  have hu : finAd F 1 • (w - finAd F 1 • w) = 0 := by
    rw [smul_sub, smul_smul, finAd_idem, sub_self]
  refine ⟨w - finAd F 1 • w,
    fun h z => schr ψ (finAd F 1 • d.e w) (fun x => h fun i => (x i).2) fun i => finAd F (z i), ?_, ?_⟩
  · intro t ht
    rw [smul_sub, smul_smul, mul_finAd_of F t ht, sub_self]
  · intro g hg f f₁ h hyp
    have hg' := hg _ (evI_finAd F)
    rw [smul_sub, sub_eq_zero] at hg'
    have hv : actB (cA σ) g (finAd F 1 • w) = finAd F 1 • w := by
      unfold actB
      rw [Matrix.smul_mul, ← Matrix.mul_smul, ← Matrix.transpose_smul, hg', Matrix.transpose_smul, Matrix.transpose_one,
        Matrix.mul_smul, Matrix.mul_one]
    have hw : actB (cA σ) g w = actB (cA σ) g (w - finAd F 1 • w) + finAd F 1 • w := by
      have : actB (cA σ) g (w - finAd F 1 • w) = actB (cA σ) g w - actB (cA σ) g (finAd F 1 • w) := by
        unfold actB
        rw [Matrix.sub_mul]
      rw [this, hv, sub_add_cancel]
    have ha : finAd F 1 • d.e (actB (cA σ) g (w - finAd F 1 • w)) = 0 := by
      rw [← map_smul]
      unfold actB
      rw [← Matrix.smul_mul, hu, Matrix.zero_mul, map_zero]
    rw [← hyp, hw]
    unfold Darboux.rho
    rw [map_add (f := _), map_smul, schr_add_of_orth, schr_pureA]
    · exact dot_eq_zero _ _ _ (congrArg Prod.fst ha)
    · rw [dotProduct_comm]
      exact dot_eq_zero _ _ _ (congrArg Prod.snd ha)

end GlobalTheory.HeisSplit
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ThKTorus.IntegralOfAdic

theorem evFin_realAd (F : Type) [Field F] [NumberField F] (v : Pl F) (x : ℝ) :
    evFin F v (realAd F x) = 0 := by
  show evalV F v 0 = 0
  exact map_zero _

end GlobalTheory.ThKTorus.IntegralOfAdic
end

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.continuous_unitaryOneParameter_realPlaceComponent : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {β : Type} [Fintype β] [DecidableEq β] {J : Matrix β β (AE F E)} (γ : Multiplicative ℝ →* UG (cA σ) J), Continuous γ → ∀ (w : InfinitePlace F) (τ : EmbOver E w), Continuous (fun t : ℝ => ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)).map (piInf τ)) := by
  first | exact @GlobalTheory.ContMapReal.contmap | exact GlobalTheory.ContMapReal.contmap | (intros; apply GlobalTheory.ContMapReal.contmap <;> assumption)
end
