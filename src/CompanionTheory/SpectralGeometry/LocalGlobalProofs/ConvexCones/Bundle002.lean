module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Mathlib.Algebra.Module.Torsion.Prod
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle667

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

section Orth

variable {X₁ X₂ : Type} [AddCommGroup X₁] [AddCommGroup X₂]

def orthSum (B₁ : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ) (B₂ : X₂ →ₗ[ℤ] X₂ →ₗ[ℤ] ℝ) :
    (X₁ × X₂) →ₗ[ℤ] (X₁ × X₂) →ₗ[ℤ] ℝ :=
  B₁.compl₁₂ (LinearMap.fst ℤ X₁ X₂) (LinearMap.fst ℤ X₁ X₂) +
    B₂.compl₁₂ (LinearMap.snd ℤ X₁ X₂) (LinearMap.snd ℤ X₁ X₂)

theorem sum_basis_nonneg {K : Type} [Fintype K] (e : Module.Basis K ℤ X₁) {B : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ} (h : IsPosDef B)
    (c : K → ℝ) : 0 ≤ ∑ k, ∑ l, c k * c l * B (e k) (e l) := by
  by_cases hc : c = 0
  · simp [hc]
  · exact ((isPosDef_iff_basis e B).1 h c hc).le

theorem isPosDef_orthSum {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂] (e₁ : Module.Basis K₁ ℤ X₁)
    (e₂ : Module.Basis K₂ ℤ X₂) {B₁ : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ} {B₂ : X₂ →ₗ[ℤ] X₂ →ₗ[ℤ] ℝ}
    (h₁ : IsPosDef B₁) (h₂ : IsPosDef B₂) : IsPosDef (orthSum B₁ B₂) := by
  rw [isPosDef_iff_basis (e₁.prod e₂)]
  intro c hc
  have key : ∑ i, ∑ j, c i * c j * orthSum B₁ B₂ ((e₁.prod e₂) i) ((e₁.prod e₂) j) =
      (∑ k, ∑ l, c (Sum.inl k) * c (Sum.inl l) * B₁ (e₁ k) (e₁ l)) +
        ∑ k, ∑ l, c (Sum.inr k) * c (Sum.inr l) * B₂ (e₂ k) (e₂ l) := by
    simp [Fintype.sum_sum_type, Finset.sum_add_distrib, orthSum]
  rw [key]
  by_cases h0 : (fun k => c (Sum.inl k)) = 0
  · have h3 : (fun k => c (Sum.inr k)) ≠ 0 := fun h3 => hc (by
      ext (k | k)
      · exact congrFun h0 k
      · exact congrFun h3 k)
    exact add_pos_of_nonneg_of_pos (sum_basis_nonneg e₁ h₁ _) ((isPosDef_iff_basis e₂ B₂).1 h₂ _ h3)
  · exact add_pos_of_pos_of_nonneg ((isPosDef_iff_basis e₁ B₁).1 h₁ _ h0) (sum_basis_nonneg e₂ h₂ _)

theorem isPosDef_compl_injective {Y : Type} [AddCommGroup Y] {C : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ} (h : IsPosDef C)
    (j : Y →ₗ[ℤ] X₁) (hj : Function.Injective j) : IsPosDef (C.compl₁₂ j j) := fun n x hx c hc => by
  simpa using h n (fun i => j (x i)) (hx.map' j (LinearMap.ker_eq_bot.2 hj)) c hc

end Orth

section DedekindLFunctions

variable (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O]

theorem free_int_of_torsion_eq_bot (M : Type) [AddCommGroup M] [Module O M] [Module.Finite O M]
    (ht : Submodule.torsion O M = ⊥) : Module.Free ℤ M := by
  have : Module.Finite ℤ M := Module.Finite.trans O M
  have : HasUniqueDiv M := by
    refine ⟨fun n hn a b hab => ?_⟩
    change n • a = n • b at hab
    have h0 : ((n : ℕ) : O) ≠ 0 := by exact_mod_cast hn
    have h1 : ((n : ℕ) : O) • (a - b) = 0 := by
      rw [Nat.cast_smul_eq_nsmul, smul_sub, hab, sub_self]
    have h2 : a - b ∈ Submodule.torsion O M :=
      (Submodule.mem_torsion_iff _).2 ⟨⟨_, mem_nonZeroDivisors_of_ne_zero h0⟩, h1⟩
    rw [ht] at h2
    exact sub_eq_zero.1 h2
  exact Module.free_of_finite_type_torsion_free'

end DedekindLFunctions

theorem add_mem_psdCone : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (B B' : X →ₗ[ℤ] X →ₗ[ℤ] ℝ), B ∈ psdCone (bar := bar) (X := X) → B' ∈ psdCone (bar := bar) (X := X) → B + B' ∈ psdCone (bar := bar) (X := X) := by
  intro O _ _ _ _ bar X _ _ _ B B' hB hB'
  obtain ⟨X₁, _, _, _, r₁, B₁, hr₁, hb₁, hd₁, he₁⟩ := hB
  obtain ⟨X₂, _, _, _, r₂, B₂, hr₂, hb₂, hd₂, he₂⟩ := hB'
  have : Module.Finite O X₁ := Module.Finite.of_surjective r₁ hr₁
  have : Module.Finite O X₂ := Module.Finite.of_surjective r₂ hr₂
  have ht₁ : Submodule.torsion O X₁ = ⊥ := IsDedekindDomain.flat_iff_torsion_eq_bot.1 inferInstance
  have ht₂ : Submodule.torsion O X₂ = ⊥ := IsDedekindDomain.flat_iff_torsion_eq_bot.1 inferInstance
  have : Module.Free ℤ X₁ := free_int_of_torsion_eq_bot O X₁ ht₁
  have : Module.Free ℤ X₂ := free_int_of_torsion_eq_bot O X₂ ht₂
  have : Module.Finite ℤ X₁ := Module.Finite.trans O X₁
  have : Module.Finite ℤ X₂ := Module.Finite.trans O X₂
  have hdef := isPosDef_orthSum (Module.Free.chooseBasis ℤ X₁) (Module.Free.chooseBasis ℤ X₂) hd₁ hd₂
  let r : X →ₗ[O] X₁ × X₂ := r₁.prod r₂
  let P := LinearMap.range r
  have htP : Submodule.torsion O P = ⊥ := by
    have ht : Submodule.torsion O (X₁ × X₂) = ⊥ := IsDedekindDomain.flat_iff_torsion_eq_bot.1 inferInstance
    refine (Submodule.eq_bot_iff _).2 fun u hu => ?_
    obtain ⟨a, hau⟩ := (Submodule.mem_torsion_iff u).1 hu
    have h1 : (u : X₁ × X₂) ∈ Submodule.torsion O (X₁ × X₂) :=
      (Submodule.mem_torsion_iff _).2 ⟨a, by simpa using congrArg Subtype.val hau⟩
    rw [ht] at h1
    exact Subtype.ext h1
  have : Module.Flat O P := IsDedekindDomain.flat_iff_torsion_eq_bot.2 htP
  have : Module.FinitePresentation O P := Module.finitePresentation_of_finite _ _
  have hproj : Module.Projective O P := Module.Flat.projective_of_finitePresentation
  let j : P →ₗ[ℤ] X₁ × X₂ := P.subtype.toAddMonoidHom.toIntLinearMap
  refine ⟨P, inferInstance, inferInstance, hproj, r.rangeRestrict, (orthSum B₁ B₂).compl₁₂ j j,
    r.surjective_rangeRestrict, ⟨fun y z => ?_, fun a y z => ?_⟩,
    isPosDef_compl_injective hdef j Subtype.val_injective, fun a b => ?_⟩
  · change B₁ _ _ + B₂ _ _ = B₁ _ _ + B₂ _ _
    rw [hb₁.1, hb₂.1]
  · change B₁ (a • _) _ + B₂ (a • _) _ = B₁ _ (bar a • _) + B₂ _ (bar a • _)
    rw [hb₁.2, hb₂.2]
    rfl
  · change B a b + B' a b = B₁ (r₁ a) (r₁ b) + B₂ (r₂ a) (r₂ b)
    rw [he₁, he₂]

end GlobalTheory.CompanionTheory.Ar.Fan
end
end

section

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem free_int_of_projective (O : Type) [CommRing O] [IsDomain O] [CharZero O] [Module.Finite ℤ O]
    (Y : Type) [AddCommGroup Y] [Module O Y] [Module.Finite O Y] [Module.Projective O Y] :
    Module.Finite ℤ Y ∧ Module.Free ℤ Y := by
  have hfin : Module.Finite ℤ Y := Module.Finite.trans O Y
  obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective O Y)
  have hinj : Function.Injective s := Function.LeftInverse.injective (g := Finsupp.linearCombination O id) (fun y => by
    simpa using LinearMap.congr_fun hs y)
  have htf : Module.IsTorsionFree ℤ Y := by
    refine Module.IsTorsionFree.of_smul_eq_zero ?_
    intro n y h
    by_contra hc
    push_neg at hc
    have h1 : ((n : O)) • y = 0 := by rw [Int.cast_smul_eq_zsmul]; exact h
    have h2 : (n : O) • s y = 0 := by rw [← map_smul, h1, map_zero]
    have hy : s y ≠ 0 := fun h0 => hc.2 (hinj (by rw [h0, map_zero]))
    obtain ⟨a, ha⟩ := Finsupp.ne_iff.1 hy
    have h3 := DFunLike.congr_fun h2 a
    simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply] at h3 ha
    exact (mul_ne_zero (Int.cast_ne_zero.2 hc.1) ha) h3
  exact ⟨hfin, Module.free_of_finite_type_torsion_free'⟩

theorem sum_nonneg_of_isPosDef {Y ι : Type} [AddCommGroup Y] [Fintype ι] (b : Module.Basis ι ℤ Y)
    {B : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ} (h : IsPosDef B) {n : ℕ} (y : Fin n → Y) (c : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * B (y i) (y j) := by
  have hy : ∀ i j, B (y i) (y j) = ∑ k, ∑ l, (b.repr (y i) k : ℝ) * (b.repr (y j) l : ℝ) * B (b k) (b l) := fun i j => by
    conv_lhs => rw [← b.sum_repr (y i), ← b.sum_repr (y j)]

    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, zsmul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  have key : ∑ i, ∑ j, c i * c j * B (y i) (y j) = ∑ k, ∑ l, (∑ i, c i * (b.repr (y i) k : ℝ)) *
      (∑ i, c i * (b.repr (y i) l : ℝ)) * B (b k) (b l) := by
    symm
    simp only [hy, Finset.mul_sum, Finset.sum_mul]
    calc _ = ∑ k, ∑ l, ∑ i, ∑ j, c i * c j * ((b.repr (y i) k : ℝ) * (b.repr (y j) l : ℝ) * B (b k) (b l)) :=
          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ k, ∑ i, ∑ j, ∑ l, c i * c j * ((b.repr (y i) k : ℝ) * (b.repr (y j) l : ℝ) * B (b k) (b l)) :=
          Finset.sum_congr rfl fun k _ => by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = _ := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
  rw [key]
  by_cases hd : (fun k => ∑ i, c i * (b.repr (y i) k : ℝ)) = 0
  · have hd' : ∀ k, ∑ i, c i * (b.repr (y i) k : ℝ) = 0 := fun k => congrFun hd k
    simp [hd']
  · exact ((isPosDef_iff_basis b B).1 h _ hd).le

theorem sum_nonneg_of_mem_psdCone (O : Type) [CommRing O] [IsDomain O] [CharZero O] [Module.Finite ℤ O] {bar : O → O}
    {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} (hB : B ∈ psdCone (bar := bar) (X := X))
    {n : ℕ} (x : Fin n → X) (c : Fin n → ℝ) : 0 ≤ ∑ i, ∑ j, c i * c j * B (x i) (x j) := by
  obtain ⟨X₁, _, _, _, r, B₁, hr, -, h1, h2⟩ := hB
  have : Module.Finite O X₁ := Module.Finite.of_surjective r hr
  obtain ⟨_, _⟩ := free_int_of_projective O X₁
  simp only [h2]
  exact sum_nonneg_of_isPosDef (Module.Free.chooseBasis ℤ X₁) h1 (fun i => r (x i)) c

theorem isPosDef_add_and_mem_psdCone (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O]
    (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X]
    (B B₀ : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) (hB : B ∈ psdCone (bar := bar) (X := X)) (hB₀ : B₀ ∈ realForms bar X) (h₀ : IsPosDef B₀) :
    IsPosDef (B + B₀) ∧ B + B₀ ∈ psdCone (bar := bar) (X := X) := by
  have hpos : IsPosDef (B + B₀) := fun n x hx c hc => by
    have h1 := sum_nonneg_of_mem_psdCone O hB x c
    have h2 := h₀ n x hx c hc
    have h3 : ∑ i, ∑ j, c i * c j * (B + B₀) (x i) (x j) =
        ∑ i, ∑ j, c i * c j * B (x i) (x j) + ∑ i, ∑ j, c i * c j * B₀ (x i) (x j) := by
      simp only [LinearMap.add_apply, mul_add, Finset.sum_add_distrib]
    rw [h3]
    exact add_pos_of_nonneg_of_pos h1 h2
  exact ⟨hpos, hpos.mem_psdCone (add_mem (mem_realForms_of_mem_psdCone hB) hB₀)⟩

end GlobalTheory.CompanionTheory.Ar.Fan
end
end

section

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem eq_zero_of_zsmul_eq_zero_of_projective {O : Type} [CommRing O] [IsDomain O] [CharZero O] {P : Type}
    [AddCommGroup P] [Module O P] [Module.Projective O P] {n : ℤ} (hn : n ≠ 0) {z : P} (h : n • z = 0) : z = 0 := by
  obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective O P)
  have hs' : ∀ x, Finsupp.linearCombination O (id : P → P) (s x) = x := fun x => LinearMap.congr_fun hs x
  have h0 : s z = 0 := by
    ext i
    have h1 : n • s z = 0 := by rw [← map_zsmul, h, map_zero]
    have h2 : (n : O) * s z i = 0 := by
      have := DFunLike.congr_fun h1 i
      simpa [zsmul_eq_mul] using this
    have h3 : (n : O) ≠ 0 := by exact_mod_cast hn
    simpa using (mul_eq_zero.1 h2).resolve_left h3
  rw [← hs' z, h0, map_zero]

theorem IsPosDef.eq_zero_of_apply_self {O : Type} [CommRing O] [IsDomain O] [CharZero O] {P : Type}
    [AddCommGroup P] [Module O P] [Module.Projective O P] {B : P →ₗ[ℤ] P →ₗ[ℤ] ℝ} (h : IsPosDef B) {z : P}
    (hz : B z z = 0) : z = 0 := by
  by_contra hne
  have hli : LinearIndependent ℤ ![z] := by
    refine Fintype.linearIndependent_iff.2 fun g hg i => ?_
    obtain rfl : i = 0 := Subsingleton.elim _ _
    by_contra hi
    exact hne (eq_zero_of_zsmul_eq_zero_of_projective (O := O) hi (by simpa using hg))
  have := h 1 _ hli ![1] (by simp)
  simp [hz] at this

theorem exists_psdCone_descend (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O)
    (X X₁ : Type) [AddCommGroup X] [Module O X] [AddCommGroup X₁] [Module O X₁] (r : X →ₗ[O] X₁)
    (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) (hr : Function.Surjective r) (hB : B ∈ psdCone (bar := bar) (X := X))
    (hk : ∀ y, r y = 0 → B y y = 0) : ∃ B₁ ∈ psdCone (bar := bar) (X := X₁), B = pullR r B₁ := by
  obtain ⟨X', _, _, _, r', B', hr', h1, h2, h3⟩ := hB
  have hker : LinearMap.ker r ≤ LinearMap.ker r' := fun y hy =>
    IsPosDef.eq_zero_of_apply_self (O := O) h2 (by rw [← h3]; exact hk y hy)
  let s : X₁ →ₗ[O] X' := ((LinearMap.ker r).liftQ r' hker) ∘ₗ (r.quotKerEquivOfSurjective hr).symm.toLinearMap
  have hs : ∀ x, s (r x) = r' x := fun x => by
    have : (r.quotKerEquivOfSurjective hr).symm (r x) = (LinearMap.ker r).mkQ x := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp only [s, LinearMap.comp_apply, LinearEquiv.coe_coe, this]
    rfl
  have hsurj : Function.Surjective s := fun z => by
    obtain ⟨x, rfl⟩ := hr' z
    exact ⟨r x, hs x⟩
  refine ⟨pullR s B', ⟨X', _, _, inferInstance, s, B', hsurj, h1, h2, fun _ _ => rfl⟩, ?_⟩
  ext a b
  simp [h3, hs]

end GlobalTheory.CompanionTheory.Ar.Fan
end
end

section

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem exists_smul_mem_of_le_of_finrank_le {M : Type} [AddCommGroup M] [Module.Finite ℤ M] {P Q : Submodule ℤ M}
    (h : P ≤ Q) (hr : Module.finrank ℤ Q ≤ Module.finrank ℤ P) {y : M} (hy : y ∈ Q) :
    ∃ n : ℤ, n ≠ 0 ∧ n • y ∈ P := by
  have e : (P.comap Q.subtype) ≃ₗ[ℤ] P := Submodule.comapSubtypeEquivOfLe h
  have h1 := Submodule.finrank_quotient_add_finrank (P.comap Q.subtype)
  rw [e.finrank_eq] at h1
  have h2 : Module.finrank ℤ (Q ⧸ P.comap Q.subtype) = 0 := by omega
  obtain ⟨n, hn, hz⟩ := Module.finrank_eq_zero_iff.1 h2 (Submodule.Quotient.mk ⟨y, hy⟩)
  refine ⟨n, hn, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hz
  simpa using hz

theorem diag_eq_zero_iff_of_isPosDef {X₁ : Type} [AddCommGroup X₁] {B : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ} (h : IsPosDef B) (z : X₁) :
    B z z = 0 ↔ z ∈ Submodule.torsion ℤ X₁ := by
  constructor
  · intro h0
    by_contra hz
    have hy : LinearIndependent ℤ ![z] := by
      refine Fintype.linearIndependent_iff.2 fun g hg i => ?_
      obtain rfl : i = 0 := Subsingleton.elim _ _
      by_contra hi
      have hg' : g 0 • z = 0 := by simpa using hg
      exact hz ((Submodule.mem_torsion_iff _).2 ⟨⟨g 0, mem_nonZeroDivisors_of_ne_zero hi⟩, hg'⟩)
    have := h 1 _ hy ![1] (by simp)
    simp [h0] at this
  · intro hz
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff _).1 hz
    have ha' : (a : ℤ) • z = 0 := ha
    have h1 : ((a : ℤ) : ℝ) * B z z = 0 := by
      rw [← zsmul_eq_mul, ← map_smul, ha', map_zero]
    exact (mul_eq_zero.1 h1).resolve_left (by exact_mod_cast nonZeroDivisors.ne_zero a.2)

theorem exists_radical_of_mem_psdCone {O : Type} [CommRing O] {bar : O → O} {X : Type} [AddCommGroup X] [Module O X]
    {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} (hB : B ∈ psdCone (bar := bar) (X := X)) : ∃ N : Submodule ℤ X, ∀ y, y ∈ N ↔ B y y = 0 := by
  obtain ⟨X₁, _, _, _, r, B₁, -, -, h1, h2⟩ := hB
  refine ⟨(Submodule.torsion ℤ X₁).comap r.toAddMonoidHom.toIntLinearMap, fun y => ?_⟩
  rw [h2, diag_eq_zero_iff_of_isPosDef h1]
  rfl

theorem exists_least_radical : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O)
    (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (K : Set (X →ₗ[ℤ] X →ₗ[ℤ] ℝ)),
    K.Nonempty → K ⊆ psdCone (bar := bar) (X := X) → (∀ B ∈ K, ∀ B' ∈ K, B + B' ∈ K) →
      ∃ B₁ ∈ K, ∀ B ∈ K, ∀ y, B₁ y y = 0 → B y y = 0 := by
  intro O _ _ _ _ bar X _ _ _ K hne hK hadd
  haveI : Module.Finite ℤ X := Module.Finite.trans O X
  choose! N hN using fun B (hB : B ∈ K) => exists_radical_of_mem_psdCone (hK hB)
  have hnn : ∀ B ∈ K, ∀ y, 0 ≤ B y y := fun B hB y => nonneg_of_mem_psdCone (hK hB) y
  obtain ⟨B₁, hB₁, hmin⟩ : ∃ B₁ ∈ K, ∀ B ∈ K, Module.finrank ℤ (N B₁) ≤ Module.finrank ℤ (N B) :=
    ⟨Function.argminOn (fun B => Module.finrank ℤ (N B)) K hne, Function.argminOn_mem _ _ hne,
      fun B hB => Function.argminOn_le (fun B => Module.finrank ℤ (N B)) K hB⟩
  refine ⟨B₁, hB₁, fun B hB y hy => ?_⟩
  have hsum := hadd B hB B₁ hB₁
  have hle : N (B + B₁) ≤ N B₁ := fun z hz => by
    have h0 : B z z + B₁ z z = 0 := by simpa using (hN _ hsum z).1 hz
    exact (hN _ hB₁ z).2 (by linarith [hnn B hB z, hnn B₁ hB₁ z])
  obtain ⟨n, hn, hny⟩ := exists_smul_mem_of_le_of_finrank_le hle (hmin _ hsum) ((hN _ hB₁ y).2 hy)
  have h0 : B (n • y) (n • y) + B₁ (n • y) (n • y) = 0 := by simpa using (hN _ hsum _).1 hny
  have h1 : B (n • y) (n • y) = 0 := by linarith [hnn B hB (n • y), hnn B₁ hB₁ (n • y)]
  have h2 : ((n : ℝ) * (n : ℝ)) * B y y = 0 := by
    rw [← h1]
    simp only [map_smul, LinearMap.smul_apply, zsmul_eq_mul]
    ring
  exact (mul_eq_zero.1 h2).resolve_left (mul_ne_zero (by exact_mod_cast hn) (by exact_mod_cast hn))

end GlobalTheory.CompanionTheory.Ar.Fan
end
end

end

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

theorem _root_.GlobalTheory.T.psd_cone_add_mem : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (B B' : X →ₗ[ℤ] X →ₗ[ℤ] ℝ), B ∈ psdCone (bar := bar) (X := X) → B' ∈ psdCone (bar := bar) (X := X) → B + B' ∈ psdCone (bar := bar) (X := X) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.add_mem_psdCone | exact GlobalTheory.CompanionTheory.Ar.Fan.add_mem_psdCone | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.add_mem_psdCone <;> assumption)

end
end

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

theorem _root_.GlobalTheory.T.psd_cone_descends_along_surjection : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (X X₁ : Type) [AddCommGroup X] [Module O X] [AddCommGroup X₁] [Module O X₁] (r : X →ₗ[O] X₁) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ), Function.Surjective r → B ∈ psdCone (bar := bar) (X := X) → (∀ y, r y = 0 → B y y = 0) → ∃ B₁ ∈ psdCone (bar := bar) (X := X₁), B = pullR r B₁ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.exists_psdCone_descend | exact GlobalTheory.CompanionTheory.Ar.Fan.exists_psdCone_descend | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.exists_psdCone_descend <;> assumption)

end
end

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

theorem _root_.GlobalTheory.T.psd_cone_exists_maximal_support : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (K : Set (X →ₗ[ℤ] X →ₗ[ℤ] ℝ)), K.Nonempty → K ⊆ psdCone (bar := bar) (X := X) → (∀ B ∈ K, ∀ B' ∈ K, B + B' ∈ K) → ∃ B₁ ∈ K, ∀ B ∈ K, ∀ y, B₁ y y = 0 → B y y = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.exists_least_radical | exact GlobalTheory.CompanionTheory.Ar.Fan.exists_least_radical | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.exists_least_radical <;> assumption)

end
end
