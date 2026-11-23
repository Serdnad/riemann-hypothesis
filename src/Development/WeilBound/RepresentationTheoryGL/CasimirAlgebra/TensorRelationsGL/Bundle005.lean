module

public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.Bundle004
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

section

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

section
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]

def curF (n : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (m k : ℕ) :
    TV n M (Fin (m + k)) →ₗ[ℂ] TV n (TV n M (Fin m)) (Fin k) :=
  LinearMap.pi fun J => LinearMap.pi fun I => LinearMap.proj (Fin.append I J)

inductive Deg (E : Fin n → Fin n → Module.End ℂ M) : ℕ → Module.End ℂ (TV n M P) → Prop
  | one (d : ℕ) : Deg E d 1
  | add {d g g'} : Deg E d g → Deg E d g' → Deg E d (g + g')
  | smul {d g} (c : ℂ) : Deg E d g → Deg E d (c • g)
  | om {d g} (p : P) : Deg E d g → Deg E (d + 1) (g * Om E p)
  | perm {d g} (σ : Equiv.Perm P) : Deg E d g → Deg E d (g * pm σ)

def colD {m : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (col : Fin m → ℕ) : Module.End ℂ (TV n M (Fin m)) :=
  (List.ofFn fun j : Fin m => (List.ofFn fun i : Fin m =>
    if i < j ∧ col i = col j then xJ E i - xJ E j + 1 else 1).prod).prod

def Semi {ι Γ : Type} [Fintype ι] (bar : ι → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ)
    (E : ι → Fin n → Fin n → Module.End ℂ M) (ρ : Γ → Module.End ℂ M) (φ : M →ₗ[ℂ] ℂ) (m : ℕ) : Prop :=
  ∃ (lab : Fin m → ι) (c : ι → ℤ) (ξ : TV n M (Fin m)), (∀ p q, lab p ≠ bar (lab q)) ∧
    (∀ γ, actT lab κ ρ γ ξ = (∏ τ, (κ τ γ).det ^ c τ) • ξ) ∧ ∃ I, ∃ w ∈ envAlg E, φ (w (ξ I)) ≠ 0

end

def Curry : Prop := ∀ (n : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M) (m k : ℕ),
  Function.Bijective (curF n M m k) ∧
  (∀ a b, curF n M m k ∘ₗ tE Finset.univ E a b = tE Finset.univ (tE Finset.univ E) a b ∘ₗ curF n M m k) ∧
  (∀ i : Fin m, curF n M m k ∘ₗ xJ E (Fin.castAdd k i) = lift (xJ E i) ∘ₗ curF n M m k) ∧
  (∀ j : Fin k, curF n M m k ∘ₗ xJ E (Fin.natAdd m j) = xJ (tE Finset.univ E) j ∘ₗ curF n M m k) ∧
  (∀ B : Module.End ℂ M, curF n M m k ∘ₗ lift B = lift (lift B) ∘ₗ curF n M m k) ∧
  (∀ i i' : Fin m, curF n M m k ∘ₗ pm (Equiv.swap (Fin.castAdd k i) (Fin.castAdd k i')) =
    lift (pm (Equiv.swap i i')) ∘ₗ curF n M m k) ∧
  ∀ j j' : Fin k, curF n M m k ∘ₗ pm (Equiv.swap (Fin.natAdd m j) (Fin.natAdd m j')) =
    pm (Equiv.swap j j') ∘ₗ curF n M m k

def StepChar : Prop := ∀ (n : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M),
  GlRel E → ∀ l : Fin n → ℂ, HasChar E l →
    (List.ofFn fun k => Om E (0 : Fin 1) - algebraMap ℂ _ (l k)).prod = 0 ∧
    ∀ (W : Submodule ℂ (TV n M (Fin 1))) (N : Type) [AddCommGroup N] [Module ℂ N] (F : Fin n → Fin n → Module.End ℂ N)
      (q : W →ₗ[ℂ] N) (hW : ∀ a b, ∀ w ∈ W, tE Finset.univ E a b w ∈ W) (hO : ∀ w ∈ W, Om E 0 w ∈ W) (k : Fin n),
      Function.Surjective q → (∀ a b (w : W), q ⟨_, hW a b w w.2⟩ = F a b (q w)) →
      (∀ w : W, q ⟨_, hO w w.2⟩ = l k • q w) → HasChar F (Function.update l k (l k + 1))

def QdetFacts : Prop := ∀ (n : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M),
  GlRel E → (∀ u a b, Commute (qdet E u) (E a b)) ∧
    (∃ c : ℕ → Module.End ℂ M, ∀ u : ℂ, qdet E u = ∑ i ∈ Finset.range (n + 1), u ^ i • c i) ∧
    (∀ l, HasChar E l → ∑ a, E a a = algebraMap ℂ _ (∑ k, l k + (n : ℂ) * (n - 1) / 2)) ∧
    GlRel (fun a b => -E b a) ∧ ∀ l, HasChar E l → HasChar (fun a b => -E b a) fun k => -((n : ℂ) - 1) - l k

def Height : Prop := ∀ (n : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M),
  GlRel E → ∀ ℓ : M →ₗ[ℂ] ℂ, IsWh E ℓ → ∀ top : Fin n, (top : ℕ) + 1 = n →
    (∀ (P : Type) [Fintype P] [DecidableEq P] (d : ℕ) (g : Module.End ℂ (TV n M P)), Deg E d g → ∀ I : P → Fin n,
      (d < ∑ p, ((top : ℕ) - I p) → ∀ v, ℓ (g (Pi.single I v) fun _ => top) = 0) ∧
      (d = ∑ p, ((top : ℕ) - I p) → ∃ c : ℂ, ∀ v, ℓ (g (Pi.single I v) fun _ => top) = c * ℓ v)) ∧
    (ℓ ≠ 0 → ∀ L : List ℂ, L.length = top →
      ℓ ∘ₗ LinearMap.proj (fun _ => top) ∘ₗ (L.map fun r => Om E (0 : Fin 1) - algebraMap ℂ _ r).prod ≠ 0) ∧
    ∀ m : ℕ, IsWh (tE (Finset.univ : Finset (Fin m)) E) (ℓ ∘ₗ LinearMap.proj fun _ => top)

def Chain : Prop := ∀ (n : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M),
  GlRel E → ∀ l : Fin n → ℂ, HasChar E l → ∀ ℓ : M →ₗ[ℂ] ℂ, ℓ ≠ 0 → IsWh E ℓ → ∀ top : Fin n, (top : ℕ) + 1 = n →
  ∀ (m : ℕ) (co : Fin m → Fin n), ∃ g ∈ Algebra.adjoin ℂ (Set.range fun j : Fin m => xJ E j),
    ℓ ∘ₗ LinearMap.proj (fun _ => top) ∘ₗ g ≠ 0 ∧
    (∀ j, (ℓ ∘ₗ LinearMap.proj (fun _ => top) ∘ₗ g) ∘ₗ xJ E j =
      (l (co j) + ((Finset.univ.filter fun i => i < j ∧ co i = co j).card : ℂ)) •
        (ℓ ∘ₗ LinearMap.proj (fun _ => top) ∘ₗ g)) ∧
    ∀ u : ℂ, (ℓ ∘ₗ LinearMap.proj (fun _ => top) ∘ₗ g) ∘ₗ qdet (tE (Finset.univ : Finset (Fin m)) E) u =
      (∏ k, (u + l k + ((Finset.univ.filter fun p => co p = k).card : ℂ))) • (ℓ ∘ₗ LinearMap.proj (fun _ => top) ∘ₗ g)

def ColAnti : Prop := ∀ (n : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M),
  GlRel E → ∀ ℓ : M →ₗ[ℂ] ℂ, IsWh E ℓ → ∀ top : Fin n, (top : ℕ) + 1 = n →
  ∀ (m : ℕ) (col : Fin m → ℕ) (b : Fin m → Fin n), Monotone col → IsTab col b →
    ∃ c : ℂ, ℓ ∘ₗ LinearMap.proj (fun _ => top) ∘ₗ colD E col = c • (ℓ ∘ₗ cA col b)

def TransFin : Prop := ∀ (n : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M),
  GlRel E → ∀ (l : Fin n → ℤ), HasChar E (fun k => (l k : ℂ)) → ∀ ℓ : M →ₗ[ℂ] ℂ, ℓ ≠ 0 → IsWh E ℓ → 1 ≤ n →
  ∀ (m : ℕ) (col : Fin m → ℕ) (b co : Fin m → Fin n), Monotone col → IsTab col b →
    (∀ i j, i < j → col i = col j →
      l (co j) + ((Finset.univ.filter fun p => p < j ∧ co p = co j).card : ℤ) ≤
        l (co i) + ((Finset.univ.filter fun p => p < i ∧ co p = co i).card : ℤ)) →
    ∃ S ∈ envAlg (fun _ : Unit => tE (Finset.univ : Finset (Fin m)) E), ℓ ∘ₗ cA col b ∘ₗ S ≠ 0 ∧ ∀ u : ℂ,
      (ℓ ∘ₗ cA col b ∘ₗ S) ∘ₗ qdet (tE (Finset.univ : Finset (Fin m)) E) u =
        (∏ k, (u + l k + ((Finset.univ.filter fun p => co p = k).card : ℂ))) • (ℓ ∘ₗ cA col b ∘ₗ S)

def LieInv : Prop := ∀ (n : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ι : Type) [Fintype ι] [DecidableEq ι]
  (Γ : Type) [Group Γ] [TopologicalSpace Γ] (bar : ι → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ)
  (E : ι → Fin n → Fin n → Module.End ℂ M) (ρ : Γ → Module.End ℂ M), IsKD bar κ → IsGK bar κ E ρ →
  ∀ (c : ι → ℤ) (ξ : M), (∀ γ, ρ γ ξ = (∏ τ, (κ τ γ).det ^ c τ) • ξ) → ∀ τ a b,
    E τ a b ξ - E (bar τ) b a ξ = if a = b then ((c τ - c (bar τ) : ℤ) : ℂ) • ξ else 0

def WallQuot : Prop := ∀ (n : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ι : Type)
  (E : ι → Fin n → Fin n → Module.End ℂ M), (∀ τ, GlRel (E τ)) →
  (∀ τ τ', τ ≠ τ' → ∀ a b c d, Commute (E τ a b) (E τ' c d)) → ∀ (l : ι → Fin n → ℂ) (φ : M →ₗ[ℂ] ℂ),
  (∀ τ (u : ℂ), φ ∘ₗ qdet (E τ) u = (∏ k, (u + l τ k)) • φ) →
    ∃ (N : Submodule ℂ M) (F : ι → Fin n → Fin n → Module.End ℂ (M ⧸ N)), (∀ τ, GlRel (F τ)) ∧
      (∀ τ τ', τ ≠ τ' → ∀ a b c d, Commute (F τ a b) (F τ' c d)) ∧ (∀ τ, HasChar (F τ) (l τ)) ∧
      (∀ τ a b, N.mkQ ∘ₗ E τ a b = F τ a b ∘ₗ N.mkQ) ∧ ∀ y, y ∈ N ↔ ∀ w ∈ envAlg E, φ (w y) = 0

def SWStart : Prop := ∀ (n : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ι : Type) [Fintype ι] [DecidableEq ι]
  (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ]
  (bar : ι → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ)
  (E : ι → Fin n → Fin n → Module.End ℂ M) (ρ : Γ → Module.End ℂ M), IsKD bar κ → IsGK bar κ E ρ →
  ∀ φ : M →ₗ[ℂ] ℂ, φ ≠ 0 → ∃ m, Semi bar κ E ρ φ m

def Contract : Prop := ∀ (n : ℕ), 1 ≤ n → ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (ι : Type) [Fintype ι]
  [DecidableEq ι] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (bar : ι → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ)
  (E : ι → Fin n → Fin n → Module.End ℂ M) (ρ : Γ → Module.End ℂ M), IsKD bar κ → IsGK bar κ E ρ →
  ∀ (s : ℂ) (φ : M →ₗ[ℂ] ℂ), (∀ τ (u : ℂ), φ ∘ₗ qdet (E τ) u = ((u + s) ^ n) • φ) →
  ∀ m, 0 < m → Semi bar κ E ρ φ m → ∃ m' < m, Semi bar κ E ρ φ m'

def SemiZero : Prop := ∀ (n : ℕ), 1 ≤ n → ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (ι : Type) [Fintype ι]
  [DecidableEq ι] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (bar : ι → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ)
  (E : ι → Fin n → Fin n → Module.End ℂ M) (ρ : Γ → Module.End ℂ M), IsKD bar κ → IsGK bar κ E ρ →
  ∀ (s : ℂ) (φ : M →ₗ[ℂ] ℂ), (∀ τ (u : ℂ), φ ∘ₗ qdet (E τ) u = ((u + s) ^ n) • φ) →
  Semi bar κ E ρ φ 0 → ∃ ξ : M, (∀ γ, ρ γ ξ = ξ) ∧ ∃ w ∈ envAlg E, φ (w ξ) ≠ 0

theorem sphAll_of (h1 : SWStart) (h2 : Contract) (h3 : SemiZero) : SphAll := by
  intro n hn M _ _ ι _ _ Γ _ _ _ _ _ bar κ E ρ hK hG s φ h0 hφ
  obtain ⟨m, hm⟩ := h1 n M ι Γ bar κ E ρ hK hG φ h0
  refine h3 n hn M ι Γ bar κ E ρ hK hG s φ hφ ?_
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hp
    · exact hm
    · obtain ⟨m', h, h'⟩ := h2 n hn M ι Γ bar κ E ρ hK hG s φ hφ m hp hm
      exact ih m' h h'

end PositivityTheory.Rg.Cz

end
end

section

noncomputable section

open Formalism.REAL Matrix MeasureTheory

namespace PositivityTheory.Rg.Cz

namespace SWS

variable {n : ℕ} {ι Γ : Type} [Fintype ι] [DecidableEq ι] [Group Γ] [TopologicalSpace Γ]
  {bar : ι → ι} {κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ}

theorem dense [CompactSpace Γ] [T2Space Γ] (hK : IsKD bar κ) {H : Set ι} (hH : ∀ τ, τ ∈ H ↔ bar τ ∉ H)
    (g : C(Γ, ℂ)) : g ∈ closure {h : C(Γ, ℂ) | ⇑h ∈ Submodule.span ℂ (Mono κ H)} := by
  let S : Set C(Γ, ℂ) := {g | ∃ τ i j, (g : Γ → ℂ) = fun k => κ τ k i j}
  let A : StarSubalgebra ℂ C(Γ, ℂ) := StarAlgebra.adjoin ℂ S
  have hsep : A.SeparatesPoints := by
    intro x y hxy
    obtain ⟨τ, hτ⟩ : ∃ τ, κ τ x ≠ κ τ y := by
      by_contra h
      push Not at h
      exact hxy (hK.sep x y h)
    obtain ⟨i, j, hij⟩ : ∃ i j, κ τ x i j ≠ κ τ y i j := by
      by_contra h
      push Not at h
      exact hτ (Matrix.ext h)
    exact ⟨fun k => κ τ k i j, ⟨⟨fun k => κ τ k i j, hK.cont τ i j⟩,
      StarAlgebra.subset_adjoin ℂ S ⟨τ, i, j, rfl⟩, rfl⟩, hij⟩
  have hsub : A.toSubalgebra ≤ (monoAlg hK H).comap (ContinuousMap.coeFnAlgHom ℂ) := by
    rw [StarAlgebra.adjoin_toSubalgebra]
    apply Algebra.adjoin_le
    rintro g (hg | hg)
    · obtain ⟨τ, i, j, hg⟩ := hg
      show (g : Γ → ℂ) ∈ Submodule.span ℂ (Mono κ H)
      rw [hg]
      exact entry_mem hK hH τ i j
    · obtain ⟨τ, i, j, hg⟩ := Set.mem_star.1 hg
      show (g : Γ → ℂ) ∈ Submodule.span ℂ (Mono κ H)
      have : (g : Γ → ℂ) = fun k => κ (bar τ) k i j := by
        funext k
        have h1 := congrFun hg k
        simp only [ContinuousMap.star_apply] at h1
        rw [hK.conj, ← h1, star_star]
      rw [this]
      exact entry_mem hK hH (bar τ) i j
  have hle : ∀ h ∈ A, ⇑h ∈ Submodule.span ℂ (Mono κ H) := fun h hh => hsub hh
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A hsep
  have hg : g ∈ A.topologicalClosure := by rw [htop]; exact StarSubalgebra.mem_top
  rw [← SetLike.mem_coe, StarSubalgebra.topologicalClosure_coe] at hg
  exact closure_mono (fun h hh => hle h hh) hg

theorem nonvanish [MeasurableSpace Γ] [BorelSpace Γ] [CompactSpace Γ] [T2Space Γ] (μ : Measure Γ) [IsFiniteMeasure μ]
    [μ.IsOpenPosMeasure] (hK : IsKD bar κ) {H : Set ι} (hH : ∀ τ, τ ∈ H ↔ bar τ ∉ H)
    {f : Γ → ℂ} (hf : Continuous f) (x : Γ) (hx : f x ≠ 0) : ∃ g ∈ Mono κ H, ∫ k, g k * f k ∂μ ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hspan : ∀ g ∈ Submodule.span ℂ (Mono κ H), Continuous g ∧ ∫ k, g k * f k ∂μ = 0 := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      refine ⟨?_, hcon g hg⟩
      obtain ⟨m, lab, c, I, K, -, rfl⟩ := hg
      exact mono_cont hK lab c I K
    | zero => exact ⟨continuous_const, by simp⟩
    | add g g' _ _ h h' =>
      refine ⟨h.1.add h'.1, ?_⟩
      simp only [Pi.add_apply, add_mul]
      rw [integral_add (integrable_of_cont μ (f := fun k => g k * f k) (h.1.mul hf))
        (integrable_of_cont μ (f := fun k => g' k * f k) (h'.1.mul hf)), h.2, h'.2,
        add_zero]
    | smul a g _ h =>
      refine ⟨h.1.const_smul a, ?_⟩
      simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
      rw [integral_const_mul, h.2, mul_zero]
  let F : C(Γ, ℂ) := ⟨fun k => star (f k), hf.star⟩
  let f' : C(Γ, ℂ) := ⟨f, hf⟩
  have hclose := dense hK hH F
  have hbound : ∀ ε > 0, ‖∫ k, F k * f k ∂μ‖ ≤ ε * (‖f'‖ * μ.real Set.univ) := by
    intro ε hε
    obtain ⟨b, hb, hdist⟩ := Metric.mem_closure_iff.1 hclose ε hε
    have hb' := hspan b hb
    have heq : ∫ k, F k * f k ∂μ = ∫ k, (F k - b k) * f k ∂μ := by
      rw [← sub_zero (∫ k, F k * f k ∂μ), ← hb'.2, ← integral_sub
        (integrable_of_cont μ (f := fun k => F k * f k) (F.continuous.mul hf))
        (integrable_of_cont μ (f := fun k => b k * f k) (b.continuous.mul hf))]
      congr 1
      funext k
      ring
    rw [heq, ← mul_assoc]
    refine norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun k => ?_)
    rw [norm_mul]
    have h1 : ‖F k - b k‖ ≤ ε := by
      have := ContinuousMap.norm_coe_le_norm (F - b) k
      rw [dist_eq_norm] at hdist
      simp only [ContinuousMap.sub_apply] at this
      linarith
    have h2 : ‖f k‖ ≤ ‖f'‖ := ContinuousMap.norm_coe_le_norm f' k
    exact mul_le_mul h1 h2 (norm_nonneg _) hε.le
  have hzero : ∫ k, F k * f k ∂μ = 0 := by
    by_contra hne
    have hpos : 0 < ‖∫ k, F k * f k ∂μ‖ := norm_pos_iff.2 hne
    set C := ‖f'‖ * μ.real Set.univ
    have hC : 0 ≤ C := mul_nonneg (norm_nonneg _) measureReal_nonneg
    set x := ‖∫ k, F k * f k ∂μ‖
    have := hbound (x / (2 * (C + 1))) (by positivity)
    have h3 : x / (2 * (C + 1)) * C ≤ x / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have hre : ∀ k, F k * f k = ((‖f k‖ ^ 2 : ℝ) : ℂ) := by
    intro k
    simp only [F, ContinuousMap.coe_mk]
    rw [Complex.ofReal_pow]
    exact RCLike.conj_mul (f k)
  simp_rw [hre, integral_complex_ofReal, Complex.ofReal_eq_zero] at hzero
  have hint : Integrable (fun k => ‖f k‖ ^ 2) μ := by
    have := (integrable_of_cont μ (f := fun k => ((‖f k‖ ^ 2 : ℝ) : ℂ)) (by fun_prop)).re
    exact this
  have hae := (integral_eq_zero_iff_of_nonneg (fun k => sq_nonneg ‖f k‖) hint).1 hzero
  have hfun := (Continuous.ae_eq_iff_eq μ (by fun_prop) continuous_const).1 hae
  have h0 : ‖f x‖ ^ 2 = 0 := congrFun hfun x
  exact hx (norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h0))

end SWS

end PositivityTheory.Rg.Cz

end
end
