module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle019
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle003
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsIsomScale
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SplitAtOf
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsOrthTransfer
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle005
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AlgebraMapIntCastSmul
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MemSmulOfMemSmulLocF
public import Formalism.HermitianLattices.HermitianLatticesProofs.GenusCovol
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle004
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle003

@[expose] public section

section

open NumberField Module Matrix

open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

noncomputable section

namespace Formalism.L2.SG.Pf.G5

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

def diagQ (K : Type) {F : Type} [Field K] [Field F] [Algebra F K] {m : ℕ} (𝔭 : Ideal (𝓞 F)) (k : ℕ)
    (a : Fin m → 𝓞 F) : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k) :=
  Matrix.diagonal fun i => Ideal.Quotient.mk (extP K 𝔭 ^ k) (algebraMap (𝓞 F) (𝓞 K) (a i))

def phiQ (K : Type) {F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
    [Algebra F K] [Fact (IsFixF K F)] {m : ℕ} (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : Fin m → 𝓞 F)
    (Y : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k)) : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k) :=
  Y + Yᴴ + Yᴴ * diagQ K 𝔭 k a * Y

def kerSet (K : Type) {F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
    [Algebra F K] [Fact (IsFixF K F)] {m : ℕ} (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : Fin m → 𝓞 F) :
    Set (Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k)) :=
  {X | Xᴴ * diagQ K 𝔭 k a * X = diagQ K 𝔭 k a ∧ ∃ Y, X = 1 + Y * diagQ K 𝔭 k a}

def PhiCount : Prop :=
  ∀ (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [Fact (IsFixF K F)], Formalism.HermitianLatticesTheory.IsCMUnram K →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ (m : ℕ) (a : Fin m → 𝓞 F), (∀ i, a i ≠ 0) →
    ∀ k : ℕ, 1 ≤ k → ∀ T : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k), Tᴴ = T →
      (∀ i j, T i j ∈ (extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ k))) →
      (Nat.card {Y : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k) // phiQ K 𝔭 k a Y = T} : ℝ) =
        (Ideal.absNorm 𝔭 : ℝ) ^ (m ^ 2 * k) * alphaStd K 𝔭 (m - cJof 𝔭 a)

def KerCount : Prop :=
  ∀ (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [Fact (IsFixF K F)], Formalism.HermitianLatticesTheory.IsCMUnram K →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ (m : ℕ) (a : Fin m → 𝓞 F), (∀ i, a i ≠ 0) →
    ∀ k : ℕ, 2 * vJof 𝔭 a + 1 ≤ k → ∀ N : ℕ,
      (∀ T : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k), Tᴴ = T →
        (∀ i j, T i j ∈ (extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ k))) →
        Nat.card {Y : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k) // phiQ K 𝔭 k a Y = T} = N) →
      Nat.card (kerSet K 𝔭 k a) = N

def DiscOnto : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    [Fact (IsFixF K F)], Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → IsTotPosDef h →
    ∀ L : Submodule (𝓞 K) V, Submodule.IsLattice K L → Formalism.HermitianLatticesTheory.IsIntegralLat h L →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ b a, IsJordanIn h ⊤ L 𝔭 b a →
    ∀ k : ℕ, 2 * vJof 𝔭 a + 1 ≤ k →
      akCount h L 𝔭 k = discAut h ⊤ L 𝔭 * Nat.card (kerSet K 𝔭 k a)

end Formalism.L2.SG.Pf.G5
end
end

section

open Module

noncomputable section

namespace Formalism.L2.SG.Pf.G3

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA

section

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}

theorem sd_basis_bot {W : Submodule K V} {M : AddSubgroup V} (hM : IsSD S h W M) (hW : W = ⊥) :
    ∃ (k : ℕ) (f : Fin k → V), (∀ i j, i ≠ j → h (f i) (f j) = 0) ∧
      (∀ i, IsUnitIn S (h (f i) (f i))) ∧ (∀ v, v ∈ spanS S f ↔ v ∈ M) ∧
      Submodule.span K (Set.range f) = W := by
  refine ⟨0, Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun v => ?_, ?_⟩
  · rw [spanS_empty]
    constructor
    · rintro rfl
      exact M.zero_mem
    · intro hv
      have := hM.le v hv
      rwa [hW, Submodule.mem_bot] at this
  · rw [hW, Set.range_eq_empty, Submodule.span_empty]

theorem sup_cutW {W : Submodule K V} {x : V} (hx : x ∈ W) (hxx : h x x ≠ 0) :
    K ∙ x ⊔ cutW h W x = W := by
  apply le_antisymm
  · exact sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr hx) inf_le_left
  · intro w hw
    have e : w = (h x w * (h x x)⁻¹) • x + (w - (h x w * (h x x)⁻¹) • x) := by abel
    rw [e]
    refine Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)) ?_
    refine mem_cutW.mpr ⟨W.sub_mem hw (W.smul_mem _ hx), ?_⟩
    rw [map_sub, map_smul, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hxx, mul_one, sub_self]

theorem sd_basis (hS : IsHermSemilocal S) (hπ : IsUnif S π) (hs : h.IsSymm)
    (hd : ∀ x, h x x = 0 → x = 0) : ∀ (n : ℕ) (W : Submodule K V) (M : AddSubgroup V),
    finrank K W ≤ n → IsSD S h W M →
    ∃ (k : ℕ) (f : Fin k → V), (∀ i j, i ≠ j → h (f i) (f j) = 0) ∧
      (∀ i, IsUnitIn S (h (f i) (f i))) ∧ (∀ v, v ∈ spanS S f ↔ v ∈ M) ∧
      Submodule.span K (Set.range f) = W := by
  intro n
  induction n with
  | zero =>
    intro W M hn hM
    exact sd_basis_bot hM (Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hn))
  | succ n ih =>
    intro W M hn hM
    by_cases hbot : W = ⊥
    · exact sd_basis_bot hM hbot
    obtain ⟨ξ, hξ, hξ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    obtain ⟨x, hx, hu⟩ := hM.exists_unit_norm hS hπ hs hd hξ hξ0
    have hxW := hM.le x hx
    obtain ⟨k, f, hfo, hfu, hfM, hfW⟩ := ih _ _
      (by have := finrank_cutW_lt (h := h) hxW hu.1; omega) (hM.cut hx hu)
    have hfc : ∀ i, f i ∈ cutW h W x := fun i => by
      rw [← hfW]
      exact Submodule.subset_span ⟨i, rfl⟩
    have hfm : ∀ i, f i ∈ M := fun i =>
      (mem_cutM.mp ((hfM (f i)).mp (mem_spanS_self f i))).1
    refine ⟨k + 1, Fin.cons x f, ?_, ?_, fun v => ?_, ?_⟩
    · intro i j hij
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => exact absurd rfl hij
        | succ j => simpa using (mem_cutW.mp (hfc j)).2
      | succ i =>
        cases j using Fin.cases with
        | zero => simpa using symm_zero hs (mem_cutW.mp (hfc i)).2
        | succ j =>
          simpa using hfo i j (fun h' => hij (by rw [h']))
    · intro i
      cases i using Fin.cases with
      | zero => simpa using hu
      | succ i => simpa using hfu i
    · constructor
      · rintro ⟨c, hc, rfl⟩
        refine M.sum_mem fun i _ => hM.smul_mem _ (hc i) _ ?_
        cases i using Fin.cases with
        | zero => simpa using hx
        | succ i => simpa using hfm i
      · intro hv
        obtain ⟨d, hd', hdv⟩ := (hfM _).mpr (proj_mem hM.toIsLatIn hx hu hv)
        refine ⟨Fin.cons (h x v * (h x x)⁻¹) d, fun i => ?_, ?_⟩
        · cases i using Fin.cases with
          | zero => simpa using S.mul_mem (hM.int _ hx _ hv) hu.2.2
          | succ i => simpa using hd' i
        · rw [Fin.sum_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ]
          rw [← hdv]
          abel
    · rw [Fin.range_cons, Submodule.span_insert, hfW]
      exact sup_cutW hxW hu.1

end

end Formalism.L2.SG.Pf.G3
end
end

section

open NumberField Module Matrix

noncomputable section

namespace Formalism.L2.SG.Pf.GluingBases

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem isLattice_span {ι' : Type} [Finite ι'] (β : ι' → V)
    (hβ : Submodule.span K (Set.range β) = ⊤) :
    Submodule.IsFullLattice K (Submodule.span (𝓞 K) (Set.range β)) := by
  let : Submodule.IsLattice K (Submodule.span (𝓞 K) (Set.range β)) :=
    Submodule.IsLattice.of_fg K (Submodule.fg_span (Set.finite_range β))
  exact { span_eq_top := (Submodule.span_span_of_tower (𝓞 K) K (Set.range β)).trans hβ }

def rdualF (h : V →ₗ⋆[K] V →ₗ[K] K) (𝔭 : Ideal (𝓞 F)) (y : V) : Submodule (𝓞 K) V :=
  (locF 𝔭 (1 : Submodule (𝓞 K) K)).comap ((h y).restrictScalars (𝓞 K))

def ldualF (h : V →ₗ⋆[K] V →ₗ[K] K) (𝔭 : Ideal (𝓞 F)) (x : V) : Submodule (𝓞 K) V where
  carrier := {y | h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, map_add (f := _), LinearMap.add_apply] at *
    exact Submodule.add_mem _ ha hb
  smul_mem' := by
    intro c z hz
    simp only [Set.mem_ofPred_eq] at *
    obtain ⟨r, hr⟩ := Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range c
    rw [← algebraMap_smul K c z, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply,
      ← hr, ← smul_eq_mul, algebraMap_smul]
    exact Submodule.smul_mem _ r hz

theorem le_dualF_of_gram (hF : IsFixF K F) (h : V →ₗ⋆[K] V →ₗ[K] K) {𝔭 : Ideal (𝓞 F)}
    (hp : 𝔭.IsPrime) {ι' : Type} (β : ι' → V)
    (hβ : ∀ i j, h (β i) (β j) ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)) :
    locF 𝔭 (Submodule.span (𝓞 K) (Set.range β)) ≤
      dualF h 𝔭 (locF 𝔭 (Submodule.span (𝓞 K) (Set.range β))) := by
  have key : ∀ y ∈ Submodule.span (𝓞 K) (Set.range β), ∀ x ∈ Submodule.span (𝓞 K) (Set.range β),
      h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K) := by
    intro y hy x hx
    have hx' : Submodule.span (𝓞 K) (Set.range β) ≤ rdualF h 𝔭 y := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      have hy' : Submodule.span (𝓞 K) (Set.range β) ≤ ldualF h 𝔭 (β j) := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact hβ i j
      exact hy' hy
    exact hx' hx
  intro x hx
  show ∀ y ∈ _, h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)
  intro y hy
  obtain ⟨t, ht, htx⟩ := (LocF.mem_locF_iff hp _ x).1 hx
  obtain ⟨s, hs, hsy⟩ := (LocF.mem_locF_iff hp _ y).1 hy
  have := key _ hsy _ htx
  rw [localizedQuotients.form_smul hF] at this
  obtain ⟨u, hu, hux⟩ := (LocF.mem_locF_iff hp _ _).1 this
  refine (LocF.mem_locF_iff hp _ _).2 ⟨u * (s * t), fun hm => ?_, ?_⟩
  · rcases hp.mem_or_mem hm with h1 | h1
    · exact hu h1
    · exact (hp.mem_or_mem h1).elim hs ht
  · rw [Algebra.smul_def] at hux ⊢
    rw [map_mul, map_mul] at hux ⊢
    simpa [mul_assoc, mul_comm, mul_left_comm] using hux

end Formalism.L2.SG.Pf.GluingBases
end
end

section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.OrthogonalProjections

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G6

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

structure Good {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} (hc : IsCompl U (orthK h U))
    (M T : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (Λ : Submodule (𝓞 K) V) : Prop where
  iU : ∀ x ∈ Λ, prO hc x ∈ locF 𝔭 (dualIn h U M)
  iW : ∀ x ∈ Λ, prO hc.symm x ∈ locF 𝔭 (dualIn h (orthK h U) T)
  oU : ∀ v ∈ locF 𝔭 (dualIn h U M), ∃ x ∈ Λ, prO hc x = v
  oW : ∀ v ∈ locF 𝔭 (dualIn h (orthK h U) T), ∃ x ∈ Λ, prO hc.symm x = v
  cU : Λ ⊓ U.restrictScalars (𝓞 K) = locF 𝔭 M
  cW : Λ ⊓ (orthK h U).restrictScalars (𝓞 K) = locF 𝔭 T

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {hc : IsCompl U (orthK h U)}
  {M T Λ : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)}

theorem mk_eq_iff {X : Submodule K V} {L : Submodule (𝓞 K) V} (a b : ↥(locF 𝔭 (dualIn h X L))) :
    (Submodule.Quotient.mk a : DiscMod h X L 𝔭) = Submodule.Quotient.mk b ↔
      (a : V) - (b : V) ∈ locF 𝔭 L := by
  rw [Submodule.Quotient.eq]
  simp [Submodule.mem_comap]

private theorem prO_mem' {X Y : Submodule K V} (hc : IsCompl X Y) (x : V) : prO hc x ∈ X := by
  exact (Submodule.projectionOnto X Y hc x).2

private theorem prO_eq_zero_of_mem_compl {X Y : Submodule K V} (hc : IsCompl X Y) {x : V} (hx : x ∈ Y) :
    prO hc x = 0 := by
  have h1 : prO hc x ∈ X := prO_mem' hc x
  have h2 : prO hc x ∈ Y := by
    have e : prO hc x = x - prO hc.symm x := eq_sub_of_add_eq (prO_add hc x)
    rw [e]
    exact Y.sub_mem hx (prO_mem' hc.symm x)
  have h3 : prO hc x ∈ X ⊓ Y := Submodule.mem_inf.2 ⟨h1, h2⟩
  rw [hc.inf_eq_bot] at h3
  exact (Submodule.mem_bot K).1 h3

private theorem prO_eq_self_of_mem {X Y : Submodule K V} (hc : IsCompl X Y) {x : V} (hx : x ∈ X) :
    prO hc x = x := by
  have h0 : prO hc.symm x = 0 := prO_eq_zero_of_mem_compl hc.symm hx
  have e := prO_add hc x
  rw [h0, add_zero] at e
  exact e

theorem prO_mem (hc' : IsCompl U (orthK h U)) (x : V) : prO hc' x ∈ U := prO_mem' hc' x

theorem prO_symm_mem (hc' : IsCompl U (orthK h U)) (x : V) : prO hc'.symm x ∈ orthK h U := prO_mem' hc'.symm x

theorem orth_projection_of_mem_compl {hc' : IsCompl U (orthK h U)} {x : V} (hx : x ∈ orthK h U) : prO hc' x = 0 := by
  exact prO_eq_zero_of_mem_compl hc' hx

theorem orth_projection_symm_of_mem {hc' : IsCompl U (orthK h U)} {x : V} (hx : x ∈ orthK h U) :
    prO hc'.symm x = x := by
  exact prO_eq_self_of_mem hc'.symm hx

theorem prO_symm_of_mem_U {hc' : IsCompl U (orthK h U)} {x : V} (hx : x ∈ U) : prO hc'.symm x = 0 := by
  exact prO_eq_zero_of_mem_compl hc'.symm hx

theorem mem_of_proj (hG : Good hc M T 𝔭 Λ) {x x' : V} (hx' : x' ∈ Λ) (hU : prO hc x' = prO hc x)
    (hW : prO hc.symm x - prO hc.symm x' ∈ locF 𝔭 T) : x ∈ Λ := by
  have hle : locF 𝔭 T ≤ Λ := by
    rw [← hG.cW]
    exact inf_le_left
  have ht : prO hc.symm x - prO hc.symm x' ∈ Λ := hle hW
  have e1 := prO_add hc x
  have e2 := prO_add hc x'
  rw [hU] at e2
  have hx : x = x' + (prO hc.symm x - prO hc.symm x') := by
    calc x = prO hc x + prO hc.symm x := e1.symm
      _ = (prO hc x + prO hc.symm x') + (prO hc.symm x - prO hc.symm x') := by abel
      _ = x' + (prO hc.symm x - prO hc.symm x') := by rw [e2]
  rw [hx]
  exact Λ.add_mem hx' ht

def gam (hG : Good hc M T 𝔭 Λ) : DiscMod h U M 𝔭 ≃ₗ[𝓞 K] DiscMod h (orthK h U) T 𝔭 :=
  have hker : LinearMap.ker (toDisc h hc M Λ 𝔭 hG.iU) =
      LinearMap.ker (toDisc h hc.symm T Λ 𝔭 hG.iW) := by
    ext x
    rw [mem_ker_toDisc, mem_ker_toDisc, prO_mem_iff hc hG.cU, prO_mem_iff hc.symm hG.cW]
    have e := prO_add hc (x : V)
    constructor
    · intro H
      have : prO hc.symm (x : V) = (x : V) - prO hc (x : V) := eq_sub_of_add_eq' e
      rw [this]
      exact Λ.sub_mem x.2 H
    · intro H
      have : prO hc (x : V) = (x : V) - prO hc.symm (x : V) := eq_sub_of_add_eq e
      rw [this]
      exact Λ.sub_mem x.2 H
  ((LinearMap.quotKerEquivOfSurjective _ (toDisc_surj h hc M Λ 𝔭 hG.iU hG.oU)).symm.trans
    (Submodule.quotEquivOfEq _ _ hker)).trans
    (LinearMap.quotKerEquivOfSurjective _ (toDisc_surj h hc.symm T Λ 𝔭 hG.iW hG.oW))

end Formalism.L2.SG.Pf.OrthogonalProjections
end
end

section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G8

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

def extU {U W : Submodule K V} (hUc : IsCompl U W) (g : W ≃ₗ[K] W) : V ≃ₗ[K] V :=
  ((Submodule.prodEquivOfIsCompl U W hUc).symm.trans ((LinearEquiv.refl K U).prodCongr g)).trans
    (Submodule.prodEquivOfIsCompl U W hUc)

theorem extU_apply {U W : Submodule K V} (hUc : IsCompl U W) (g : W ≃ₗ[K] W) (x : U) (y : W) :
    extU hUc g ((x : V) + y) = x + g y := by
  have e : (Submodule.prodEquivOfIsCompl U W hUc).symm ((x : V) + y) = (x, y) := by
    rw [LinearEquiv.symm_apply_eq, Submodule.coe_prodEquivOfIsCompl']
  simp only [extU, LinearEquiv.trans_apply, e, LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply,
    Submodule.coe_prodEquivOfIsCompl']

theorem extU_mem {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {U : Submodule K V}
    (hUc : IsCompl U (orthK h U)) {g : orthK h U ≃ₗ[K] orthK h U} (hg : g ∈ Formalism.HermitianLatticesTheory.isom (resF h (orthK h U))) :
    extU hUc g ∈ isomFix h U := by
  have horth : ∀ u ∈ U, ∀ w ∈ orthK h U, h u w = 0 := by
    intro u hu w hw
    simp only [orthK, Submodule.mem_iInf, LinearMap.mem_ker] at hw
    exact hw u hu
  have horth' : ∀ u ∈ U, ∀ w ∈ orthK h U, h w u = 0 := by
    intro u hu w hw
    rw [← hs.eq u w, horth u hu w hw, map_zero]
  have hdec : ∀ x : V, ∃ a : U, ∃ b : orthK h U, (a : V) + b = x := by
    intro x
    have hx : x ∈ U ⊔ orthK h U := by rw [hUc.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩
  have hg' : ∀ x y, resF h (orthK h U) (g x) (g y) = resF h (orthK h U) x y := hg
  change extU hUc g ∈ Formalism.HermitianLatticesTheory.isom h ∧ ∀ u ∈ U, extU hUc g u = u
  refine ⟨?_, ?_⟩
  · change ∀ x y, h (extU hUc g x) (extU hUc g y) = h x y
    intro x y
    obtain ⟨a, b, rfl⟩ := hdec x
    obtain ⟨c, d, rfl⟩ := hdec y
    rw [extU_apply, extU_apply]
    have hgb : h (g b) (g d) = h b d := by
      have := hg' b d
      simpa only [resF_apply] using this
    simp only [map_add (f := _), LinearMap.add_apply, horth _ a.2 _ (g d).2, horth _ a.2 _ d.2,
      horth' _ c.2 _ (g b).2, horth' _ c.2 _ b.2, hgb]
  · intro u hu
    have := extU_apply hUc g ⟨u, hu⟩ 0
    simpa using this

theorem gmap_extU {U W : Submodule K V} (hUc : IsCompl U W) (g : W ≃ₗ[K] W) (X : Submodule (𝓞 K) W) :
    Formalism.HermitianLatticesTheory.gmap (extU hUc g) (X.map (incO W)) = (Formalism.HermitianLatticesTheory.gmap g X).map (incO W) := by
  have key : ∀ w : W, extU hUc g (w : V) = (g w : V) := by
    intro w
    have := extU_apply hUc g 0 w
    simpa using this
  ext v
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨g x, ⟨x, hx, rfl⟩, (key x).symm⟩
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, ⟨x, hx, rfl⟩, key x⟩

theorem isomFixOfExp_of (hJ : JordanIsom) : IsomFixOfExp := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hN U hUc hpos T T' hT hT' 𝔭 h𝔭 b a b' a' hb hb' hv
  haveI := h𝔭.isPrime
  have hs' : (resF h (orthK h U)).IsSymm := by
    exact ⟨fun x y => by simpa only [resF_apply] using hs.eq (x : V) y⟩
  have hd' : IsTotPosDef (resF h (orthK h U)) := by
    intro x hx φ
    rw [resF_apply]
    exact hpos x x.2 (by simpa using hx) φ
  obtain ⟨g, hg, hgL⟩ := hJ K F (orthK h U) hK hF (resF h (orthK h U)) hs' hd'
    (latW (orthK h U) T) (latW (orthK h U) T') (isLattice_latW hT).toIsLattice
    (isLattice_latW hT').toIsLattice 𝔭 h𝔭 _ _ _ _
    (isJordanIn_res hT hb) (isJordanIn_res hT' hb') (fun i => hv _)
  refine ⟨extU hUc g, extU_mem hs hUc hg, ?_⟩
  rw [← locF_latW hT 𝔭, gmap_extU, hgL, locF_latW hT' 𝔭]

end Formalism.L2.SG.Pf.G8
end
end
