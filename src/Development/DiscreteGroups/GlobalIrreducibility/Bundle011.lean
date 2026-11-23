module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle151
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle007
public import Mathlib.Analysis.InnerProductSpace.Adjoint
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

@[expose] public section

section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.Whittaker Matrix

namespace DiscreteGroups.sglob.LConvGenM

variable {k : Type} [Field k] {n : ℕ}

def colM (j : ℕ) (c : Fin n → k) : Matrix (Fin n) (Fin n) k :=
  Matrix.of fun i l => if i.val < j ∧ l.val = j then c i else 0

theorem colM_apply (j : ℕ) (c : Fin n → k) (i l : Fin n) :
    colM j c i l = if i.val < j ∧ l.val = j then c i else 0 := rfl

theorem colM_mul (j : ℕ) (c d : Fin n → k) : colM j c * colM j d = 0 := by
  ext i l
  simp only [Matrix.mul_apply, colM_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun a _ => ?_
  by_cases h1 : i.val < j ∧ a.val = j
  · by_cases h2 : a.val < j ∧ l.val = j
    · exact absurd h2.1 (by omega)
    · simp [h2]
  · simp [h1]

theorem colM_add (j : ℕ) (c d : Fin n → k) : colM j (c + d) = colM j c + colM j d := by
  ext i l
  simp only [colM_apply, Matrix.add_apply, Pi.add_apply]
  split_ifs <;> simp

def colU (j : ℕ) (c : Fin n → k) : GL (Fin n) k :=
  ⟨1 + colM j c, 1 - colM j c, by rw [add_mul, one_mul, mul_sub, mul_one, colM_mul]; abel,
    by rw [sub_mul, one_mul, mul_add, mul_one, colM_mul]; abel⟩

theorem val_colU (j : ℕ) (c : Fin n → k) : (colU j c : Matrix (Fin n) (Fin n) k) = 1 + colM j c := rfl

theorem colU_add (j : ℕ) (c d : Fin n → k) : colU j (c + d) = colU j c * colU j d := by
  ext : 1
  rw [Units.val_mul, val_colU, val_colU, val_colU, colM_add, add_mul, one_mul, mul_add, mul_one, colM_mul]
  abel

theorem colU_zero (j : ℕ) : colU j (0 : Fin n → k) = 1 := by
  ext : 1
  rw [val_colU, Units.val_one]
  have : colM j (0 : Fin n → k) = 0 := by ext i l; simp [colM_apply]
  rw [this, add_zero]

theorem colU_inv (j : ℕ) (c : Fin n → k) : (colU j c)⁻¹ = colU j (-c) := by
  refine (inv_eq_of_mul_eq_one_right ?_)
  rw [← colU_add, add_neg_cancel, colU_zero]

theorem colU_mul_apply (j : ℕ) (hj : j < n) (c : Fin n → k) (M : Matrix (Fin n) (Fin n) k) (i l : Fin n) :
    ((colU j c : Matrix (Fin n) (Fin n) k) * M) i l = M i l + (if i.val < j then c i * M ⟨j, hj⟩ l else 0) := by
  rw [val_colU, add_mul, one_mul, Matrix.add_apply, Matrix.mul_apply]
  congr 1
  rw [Finset.sum_eq_single (⟨j, hj⟩ : Fin n)]
  · simp only [colM_apply, and_true]
    split_ifs <;> simp
  · intro a _ ha
    have : ¬ (a.val = j) := fun h => ha (Fin.ext h)
    simp [colM_apply, this]
  · simp

theorem colU_single_of_lt (j : ℕ) (hj : j < n) {r : Fin n} (hr : r.val < j) (a : k) :
    colU j (Pi.single r a) = GlobalTheory.RootUp.elem (i := r) (j := ⟨j, hj⟩) (fun h => by
      have := congrArg Fin.val h; simp at this; omega) a := by
  ext i l
  rw [val_colU, GlobalTheory.RootUp.val_elem, Matrix.add_apply, Matrix.add_apply]
  congr 1
  rw [colM_apply, Matrix.single_apply]
  by_cases hi : i = r
  · subst hi
    by_cases hl : l.val = j
    · have : (⟨j, hj⟩ : Fin n) = l := Fin.ext hl.symm
      simp [hr, hl, this]
    · have : (⟨j, hj⟩ : Fin n) ≠ l := fun h => hl (by rw [← h])
      simp [hl, this]
  · have : r ≠ i := Ne.symm hi
    simp [Pi.single_apply, hi, this]

theorem colU_single_of_ge (j : ℕ) {r : Fin n} (hr : j ≤ r.val) (a : k) : colU j (Pi.single r a) = 1 := by
  ext i l
  rw [val_colU, Units.val_one, Matrix.add_apply, colM_apply]
  by_cases hi : i = r
  · subst hi; simp [show ¬ i.val < j by omega]
  · simp [Pi.single_apply, hi]

end DiscreteGroups.sglob.LConvGenM
end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocLanglands GlobalTheory.Whittaker

namespace DiscreteGroups.sglob.LConv

def IsWhitTest {k : Type} [Field k] [TopologicalSpace k] {m : ℕ} (ψ : AddChar k Circle) (f : GL (Fin m) k → ℂ) :
    Prop :=
  (∀ u ∈ unipB k (Fin m), ∀ g, f (u * g) = (ψ (superDiag u) : ℂ) * f g) ∧ IsLocallyConstant f ∧
    ∃ C : Set (GL (Fin m) k), IsCompact C ∧ ∀ g, f g ≠ 0 → ∃ u ∈ unipB k (Fin m), ∃ c ∈ C, g = u * c

def IsInvForm {G M : Type} [Group G] [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M)
    (B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) : Prop :=
  (∀ x y, (starRingEnd ℂ) (B x y) = B y x) ∧ (∀ x, 0 ≤ (B x x).re) ∧ ∀ g x y, B (ρ g x) (ρ g y) = B x y

def IsExtremeForm {G M : Type} [Group G] [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M)
    (B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) : Prop :=
  IsInvForm ρ B ∧ ∀ B' : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ, IsInvForm ρ B' → IsInvForm ρ (B - B') →
    ∃ c : ℂ, ∀ x y, B' x y = c * B x y

def UnitAdm (G : Type) [Group G] (K : Subgroup G) : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : G →* (H →L[ℂ] H)),
    (∀ g x, ‖π g x‖ = ‖x‖) → (∀ T : H →L[ℂ] H, (∀ g, T * π g = π g * T) → ∃ c : ℂ, T = c • (1 : H →L[ℂ] H)) →
    ∃ s : Finset H, ∀ x : H, (∀ κ ∈ K, π κ x = x) → x ∈ Submodule.span ℂ (s : Set H)

def UnifAdm (G : Type) [Group G] [TopologicalSpace G] (K : Subgroup G) (N : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), IsSmooth ρ → ρ.IsIrreducible →
    FiniteDimensional ℂ (fixed ρ K) ∧ Module.finrank ℂ (fixed ρ K) ≤ N

def CuspGen : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V), Nontrivial V → IsCuspidal π → IsGeneric ψ π

def KirBump : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin (m + 1)) k) V), IsSmooth ρ → ∀ v₀ : V, ∃ v : V,
      ∀ l : Module.Dual ℂ V, IsFunctional ψ ρ l →
        l v = l v₀ ∧ (l v₀ = 0 → ∀ g : GL (Fin m) k, l (ρ (corner g) v) = 0)

def BigCell : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle) (m : ℕ), 0 < m → ∀ (π₁ π₂ : IrrRep (GL (Fin (m + 1)) k))
    (l₁ : Module.Dual ℂ π₁.V) (l₂ : Module.Dual ℂ π₂.V), IsFunctional ψ π₁.ρ l₁ → IsFunctional ψ π₂.ρ l₂ →
    (∀ (v₁ : π₁.V) (v₂ : π₂.V), (∀ g : GL (Fin m) k, l₁ (π₁.ρ (corner g) v₁) = l₂ (π₂.ρ (corner g) v₂)) →
      l₁ (π₁.ρ (longElt (m + 1) k) v₁) = l₂ (π₂.ρ (longElt (m + 1) k) v₂)) →
    (∃ (v₁ : π₁.V) (v₂ : π₂.V), (∀ g : GL (Fin m) k, l₁ (π₁.ρ (corner g) v₁) = l₂ (π₂.ρ (corner g) v₂)) ∧
      l₁ v₁ ≠ 0) →
    Nonempty (π₁.ρ.Equiv π₂.ρ)

def WhitSep : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (m : ℕ),
    ∃ I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ, IsInvIntegral I ∧
      ∀ ψ : AddChar k Circle, Continuous ψ → ∀ f : GL (Fin m) k → ℂ, IsWhitTest ψ f →
        (∀ (τ : IrrRep (GL (Fin m) k)) (l : Module.Dual ℂ τ.V), IsFunctional ψ⁻¹ τ.ρ l →
          ∀ v : τ.V, I (fun g => f g * l (τ.ρ g v)) = 0) → f = 0

def ExtremeExists : Prop :=
  ∀ (G M : Type) [Group G] [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M),
    (∃ s : Set M, s.Countable ∧ Submodule.span ℂ s = ⊤) →
    ∀ B₀ : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ, IsInvForm ρ B₀ → ∀ f : M, B₀ f f ≠ 0 →
      ∃ B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ, IsExtremeForm ρ B ∧ B f f ≠ 0

def ExtremeIrred : Prop :=
  ∀ (G M : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module ℂ M]
    (ρ : Representation ℂ G M), IsSmooth ρ →
    (∀ x : M, ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ ∀ κ ∈ K, ρ κ x = x) →
    (∀ K : Subgroup G, IsOpen (K : Set G) → IsCompact (K : Set G) → UnitAdm G K) →
    ∀ B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ, IsExtremeForm ρ B →
      ∀ Z : Submodule ℂ M, (∀ g, ∀ z ∈ Z, ρ g z ∈ Z) →
        (∀ z ∈ Z, B z z = 0) ∨ ∀ x : M, ∃ z ∈ Z, B (x - z) (x - z) = 0

def UnitAdmGL : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m : ℕ)
    (K : Subgroup (GL (Fin m) k)), IsOpen (K : Set (GL (Fin m) k)) → IsCompact (K : Set (GL (Fin m) k)) →
    UnitAdm (GL (Fin m) k) K

def SepOfExtreme : Prop := ExtremeExists → ExtremeIrred → UnitAdmGL → WhitSep

def CommBound : Prop :=
  ∀ l t : ℕ, ∃ c : ℕ, ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (a : Fin l → Module.End ℂ V), (∀ i j, a i * a j = a j * a i) →
    t * Module.finrank ℂ (Algebra.adjoin ℂ (Set.range a)) ≤ Module.finrank ℂ V ^ 2 + c * Module.finrank ℂ V

def UnifAdmGL : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m : ℕ)
    (K : Subgroup (GL (Fin m) k)), IsOpen (K : Set (GL (Fin m) k)) → ∃ N : ℕ, UnifAdm (GL (Fin m) k) K N

def UnifOfComm : Prop := CommBound → UnifAdmGL

def AltIdentity : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) →
    IsCompact (K : Set G) → Countable (G ⧸ K) → ∀ N : ℕ, UnifAdm G K N →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : G →* (H →L[ℂ] H)),
      (∀ g x, ‖π g x‖ = ‖x‖) → ∀ e : H →L[ℂ] H, IsSelfAdjoint e → (∀ x, ∀ κ ∈ K, π κ (e x) = e x) →
      (∀ x, (∀ κ ∈ K, π κ x = x) → e x = x) → ∀ d : ℕ, N ^ 2 < d → ∀ g : Fin d → G,
        ∑ σ : Equiv.Perm (Fin d), ((Equiv.Perm.sign σ : ℤ) : ℂ) • (List.ofFn fun i => e * π (g (σ i)) * e).prod = 0

def FiniteOfAlt : Prop :=
  ∀ (G : Type) [Group G] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : G →* (H →L[ℂ] H)), (∀ g x, ‖π g x‖ = ‖x‖) →
    (∀ T : H →L[ℂ] H, (∀ g, T * π g = π g * T) → ∃ c : ℂ, T = c • (1 : H →L[ℂ] H)) →
    ∀ e : H →L[ℂ] H, e * e = e → ∀ d : ℕ, (∀ g : Fin d → G,
      ∑ σ : Equiv.Perm (Fin d), ((Equiv.Perm.sign σ : ℤ) : ℂ) • (List.ofFn fun i => e * π (g (σ i)) * e).prod = 0) →
    ∃ s : Finset H, ∀ x : H, e x ∈ Submodule.span ℂ (s : Set H)

def UnitOfUnif : Prop := AltIdentity → FiniteOfAlt → UnifAdmGL → UnitAdmGL

def Glue : Prop := CuspGen → KirBump → BigCell → WhitSep → GlobalTheory.Published.LocalConverseGL

theorem localConverseGL_of_leaves (h1 : CuspGen) (h2 : KirBump) (h3 : BigCell) (h4 : ExtremeExists)
    (h5 : ExtremeIrred) (h6 : SepOfExtreme) (h7 : CommBound) (h8 : UnifOfComm) (h9 : AltIdentity)
    (h10 : FiniteOfAlt) (h11 : UnitOfUnif) (h12 : Glue) : GlobalTheory.Published.LocalConverseGL :=
  h12 h1 h2 h3 (h6 h4 h5 (h11 h9 h10 (h8 h7)))

end DiscreteGroups.sglob.LConv

end
end
