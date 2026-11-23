module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Algebra.Algebra.Spectrum.Basic

@[expose] public section

section

open Matrix Finset
open scoped TensorProduct Classical

namespace GlobalTheory

theorem charPowPrimeOrder_embeddings_differ_by_coprime_power :
    ∀ (Γ : Type) [Group Γ] (C : Type) [Field C] [CharZero C] (l n : ℕ), l.Prime →
      ∀ (ψ : Γ →* Cˣ), (∀ g, ψ g ^ (l ^ n) = 1) → ∀ e e' : C →+* ℂ,
        ∃ a : ℕ, Nat.Coprime a l ∧ ∀ g, e' ((ψ g : Cˣ) : C) = e (((ψ g ^ a : Cˣ)) : C) := by
  intro Γ _ C _ _ l n hl ψ hψ e e'
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hl.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := rootsOfUnity (l ^ n) C)
  set u : Cˣ := (ζ : Cˣ) with hu
  have hul : u ^ (l ^ n) = 1 := (mem_rootsOfUnity _ _).mp ζ.2
  set k := orderOf u with hk
  have hkd : k ∣ l ^ n := orderOf_dvd_of_pow_eq_one hul
  have hk0 : 0 < k := Nat.pos_of_ne_zero (fun h => by
    rw [h] at hkd; exact (NeZero.ne (l ^ n)) (Nat.eq_zero_of_zero_dvd hkd))
  haveI : NeZero k := ⟨hk0.ne'⟩
  have hpu : IsPrimitiveRoot (u : C) k := IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.orderOf u)
  have h1 : IsPrimitiveRoot (e (u : C)) k := hpu.map_of_injective e.injective
  have h2 : IsPrimitiveRoot (e' (u : C)) k := hpu.map_of_injective e'.injective
  obtain ⟨i, hik, hi⟩ := h1.eq_pow_of_pow_eq_one h2.pow_eq_one
  have hic : i.Coprime k := (h1.pow_iff_coprime hk0 i).mp (by rw [hi]; exact h2)
  refine ⟨i + k, ?_, ?_⟩
  · have hc : (i + k).Coprime k := by simpa using hic
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hl]
    intro hdvd
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hl).mp hkd
    rcases m with _ | m
    · simp at hm
      have : i = 0 := by omega
      subst this
      rw [hm] at hdvd
      exact hl.one_lt.ne' (Nat.dvd_one.mp (by simpa using hdvd))
    · have hlk : l ∣ k := by rw [hm]; exact dvd_pow_self l (Nat.succ_ne_zero m)
      have := Nat.Coprime.coprime_dvd_left hdvd hc
      have := Nat.Coprime.coprime_dvd_right hlk this
      exact hl.one_lt.ne' (by simpa using this)
  · have hEu : e' (u : C) = e (u : C) ^ (i + k) := by
      rw [pow_add, hi, h1.pow_eq_one, mul_one]
    let E : Cˣ →* ℂˣ := Units.map (e : C →* ℂ)
    let E' : Cˣ →* ℂˣ := Units.map (e' : C →* ℂ)
    have hEu' : E' u = E u ^ (i + k) := by
      ext; simp [E, E', hEu]
    intro g
    have hmem : ψ g ∈ rootsOfUnity (l ^ n) C := (mem_rootsOfUnity _ _).mpr (hψ g)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hζ ⟨ψ g, hmem⟩)
    have hj' : u ^ j = ψ g := by
      have := congrArg Subtype.val hj
      simpa [hu] using this
    have key : E' (ψ g) = E (ψ g ^ (i + k)) := by
      rw [← hj', map_zpow, map_pow, map_zpow, hEu', ← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul,
        ← _root_.zpow_mul, mul_comm]
    have := congrArg Units.val key
    simpa [E, E'] using this

end GlobalTheory
end

section

universe u_1 u_2

namespace GlobalTheory.CommonEigenvector

private lemma exists_common_eigenspace_of_commuting {V : Type u_1} {ι : Type u_2} [AddCommGroup V] [Module ℂ V]
    (H : ι → Module.End ℂ V) (hc : ∀ (i j : ι), H i * H j = H j * H i)
    (E : Submodule ℂ V) [FiniteDimensional ℂ ↥E] (hE : ∀ (i : ι), ∀ x ∈ E, (H i : V → V) x ∈ E)
    (hne : E ≠ ⊥) :
    ∃ W : Submodule ℂ V, W ≤ E ∧ W ≠ ⊥ ∧ ∀ i, ∃ c : ℂ, ∀ x ∈ W, (H i : V → V) x = c • x := by

  classical
  let P : Submodule ℂ V → Prop := fun W => W ≤ E ∧ W ≠ ⊥ ∧ ∀ i, ∀ x ∈ W, (H i : V → V) x ∈ W
  have hex : ∃ n, ∃ W, P W ∧ Module.finrank ℂ W = n := ⟨_, E, ⟨le_rfl, hne, hE⟩, rfl⟩
  obtain ⟨W, ⟨hWE, hW0, hWi⟩, hWn⟩ := Nat.find_spec hex
  have hmin : ∀ W', P W' → Module.finrank ℂ W ≤ Module.finrank ℂ W' := fun W' hW' => by
    rw [hWn]
    exact Nat.find_min' hex ⟨W', hW', rfl⟩
  have : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le hWE
  have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW0
  refine ⟨W, hWE, hW0, fun i => ?_⟩
  obtain ⟨c, hce⟩ := Module.End.exists_eigenvalue ((H i).restrict (hWi i))
  obtain ⟨w, hw⟩ := hce.exists_hasEigenvector
  have hwv : (H i : V → V) w = c • (w : V) := by
    have h1 := congrArg Subtype.val hw.apply_eq_smul
    simpa using h1
  let W' : Submodule ℂ V := W ⊓ LinearMap.ker (H i - c • LinearMap.id)
  have hmem : ∀ x, x ∈ W' ↔ x ∈ W ∧ (H i : V → V) x = c • x := by
    intro x
    simp [W', sub_eq_zero]
  have hW'le : W' ≤ W := inf_le_left
  have hW'P : P W' := by
    refine ⟨hW'le.trans hWE, ?_, ?_⟩
    · intro h
      have hw' : (w : V) ∈ W' := (hmem _).2 ⟨w.2, hwv⟩
      rw [h, Submodule.mem_bot] at hw'
      exact hw.2 (Subtype.ext hw')
    · intro j x hx
      obtain ⟨hxW, hxe⟩ := (hmem x).1 hx
      refine (hmem _).2 ⟨hWi j x hxW, ?_⟩
      have hcom := congrArg (fun f : Module.End ℂ V => f x) (hc i j)
      simp only [Module.End.mul_apply] at hcom
      rw [hcom, hxe, map_smul]
  have hle : Module.finrank ℂ W' ≤ Module.finrank ℂ W :=
    LinearMap.finrank_le_finrank_of_injective (Submodule.inclusion_injective hW'le)
  have hEq : W' = W := Submodule.eq_of_le_of_finrank_eq hW'le (le_antisymm hle (hmin W' hW'P))
  refine ⟨c, fun x hx => ?_⟩
  rw [← hEq] at hx
  exact ((hmem x).1 hx).2

theorem common_eigenvector : ∀ {V : Type u_1} {ι : Type u_2} [inst : AddCommGroup V] [inst_1 : Module ℂ V] [Fintype ι] (H : ι → Module.End ℂ V), (∀ (i j : ι), H i * H j = H j * H i) → ∀ (E : Submodule ℂ V) [FiniteDimensional ℂ ↥E], (∀ (i : ι), ∀ x ∈ E, (H i : V → V) x ∈ E) → E ≠ ⊥ → ∃ v ∈ E, v ≠ (0 : V) ∧ ∀ (i : ι), ∃ (c : ℂ), (H i : V → V) v = c • v := by
  intro V ι _ _ _ H hc E _ hE hne

  obtain ⟨W, hWE, hW0, hW⟩ := exists_common_eigenspace_of_commuting H hc E hE hne
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  refine ⟨v, hWE hv, hv0, fun i => ?_⟩
  obtain ⟨c, hc'⟩ := hW i
  exact ⟨c, hc' v hv⟩

end GlobalTheory.CommonEigenvector
end

section

namespace GlobalTheory

theorem schur_proportional_of_range_le
    (H W X : Type) [Group H] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] [Nontrivial W]
    [AddCommGroup X] [Module ℂ X] (ρ : H → Module.End ℂ W) (a : H → Module.End ℂ X)
    (φ ξ : W →ₗ[ℂ] X)
    (hirr : ∀ U : Submodule ℂ W, (∀ h, U.map (ρ h) ≤ U) → U = ⊥ ∨ U = ⊤)
    (hξ : Function.Injective ξ) (hr : LinearMap.range φ ≤ LinearMap.range ξ)
    (hφe : ∀ h w, φ (ρ h w) = a h (φ w)) (hξe : ∀ h w, ξ (ρ h w) = a h (ξ w)) :
    ∃ c : ℂ, φ = c • ξ := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective ξ (LinearMap.ker_eq_bot.mpr hξ)
  have hgx : ∀ v, g (ξ v) = v := fun v => by
    simpa using LinearMap.congr_fun hg v
  set A : Module.End ℂ W := g ∘ₗ φ with hA
  have hxA : ∀ w, ξ (A w) = φ w := by
    intro w
    obtain ⟨v, hv⟩ := hr (LinearMap.mem_range_self φ w)
    simp only [hA, LinearMap.comp_apply, ← hv, hgx]
  have hcomm : ∀ h w, A (ρ h w) = ρ h (A w) := by
    intro h w
    apply hξ
    rw [hxA, hφe, hξe, hxA]
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue A
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  have hAv : A v = c • v := hv.apply_eq_smul
  let U : Submodule ℂ W := LinearMap.ker (A - c • LinearMap.id)
  have hmemU : ∀ u, u ∈ U ↔ A u = c • u := by
    intro u
    simp [U, sub_eq_zero]
  have hstab : ∀ h, U.map (ρ h) ≤ U := by
    intro h x hx
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hx
    rw [hmemU] at hu ⊢
    rw [hcomm, hu, map_smul]
  have hne : U ≠ ⊥ := by
    intro hU
    have : v ∈ U := (hmemU v).mpr hAv
    rw [hU, Submodule.mem_bot] at this
    exact hv.2 this
  have htop : U = ⊤ := (hirr U hstab).resolve_left hne
  refine ⟨c, ?_⟩
  ext w
  have hw : w ∈ U := htop ▸ Submodule.mem_top
  rw [hmemU] at hw
  rw [LinearMap.smul_apply, ← hxA, hw, map_smul]

theorem schur_proportional :
    ∀ (H W X : Type) [Group H] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] [Nontrivial W] [AddCommGroup X] [Module ℂ X] (ρ : H → Module.End ℂ W) (a : H → Module.End ℂ X) (φ ξ : W →ₗ[ℂ] X), (∀ U : Submodule ℂ W, (∀ h, U.map (ρ h) ≤ U) → U = ⊥ ∨ U = ⊤) → Function.Injective ξ → LinearMap.range φ ≤ LinearMap.range ξ → (∀ h w, φ (ρ h w) = a h (φ w)) → (∀ h w, ξ (ρ h w) = a h (ξ w)) → ∃ c : ℂ, φ = c • ξ :=
  fun H W X _ _ _ _ _ _ _ ρ a φ ξ hirr hξ hr hφe hξe =>
    schur_proportional_of_range_le H W X ρ a φ ξ hirr hξ hr hφe hξe

end GlobalTheory
end

section

open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory


open Matrix in
theorem finsum_char_det_fix_hyperplane_eq_zero :
    ∀ (k : Type) [Field k] [Finite k] (r : ℕ) (ξ : kˣ →* ℂˣ), ξ ≠ 1 → ∀ a : Fin r → k, a ≠ 0 →
      ∑ᶠ g ∈ {g : GL (Fin r) k | ∀ v, a ⬝ᵥ v = 0 → (g : Matrix (Fin r) (Fin r) k).mulVec v = v},
        ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) = 0 := by
  intro k _ _ r ξ hξ a ha
  set S : Set (GL (Fin r) k) :=
    {g : GL (Fin r) k | ∀ v, a ⬝ᵥ v = 0 → (g : Matrix (Fin r) (Fin r) k).mulVec v = v} with hS
  obtain ⟨c, hc⟩ : ∃ c : kˣ, ξ c ≠ 1 := by
    by_contra h
    push_neg at h
    exact hξ (MonoidHom.ext h)
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra h
    push_neg at h
    exact ha (funext h)
  set v₀ : Fin r → k := Pi.single i (a i)⁻¹ with hv₀
  have hav₀ : a ⬝ᵥ v₀ = 1 := by
    rw [hv₀, dotProduct_single, mul_inv_cancel₀ hi]
  set u : Fin r → k := ((c : k) - 1) • v₀ with hu
  set M : Matrix (Fin r) (Fin r) k :=
    1 + replicateCol (Fin 1) u * replicateRow (Fin 1) a with hM
  have hdet : M.det = (c : k) := by
    have h1 := det_one_add_replicateCol_mul_replicateRow (ι := Fin 1) u a
    rw [hM]
    refine h1.trans ?_
    rw [hu, dotProduct_smul, hav₀, smul_eq_mul, mul_one]
    ring
  have hMfix : ∀ v, a ⬝ᵥ v = 0 → M *ᵥ v = v := by
    intro v hv
    rw [hM, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
    have : replicateRow (Fin 1) a *ᵥ v = 0 := by
      ext j
      simp [Matrix.mulVec, replicateRow, hv]
    rw [this, Matrix.mulVec_zero, add_zero]
  let h₀ : GL (Fin r) k := Matrix.GeneralLinearGroup.mkOfDetNeZero M (by rw [hdet]; exact c.ne_zero)
  have hh₀ : (h₀ : Matrix (Fin r) (Fin r) k) = M := rfl
  have hdeth₀ : Matrix.GeneralLinearGroup.det h₀ = c := by
    ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, hh₀, hdet]
  have hh₀S : h₀ ∈ S := fun v hv => by rw [hh₀]; exact hMfix v hv
  have hmulS : ∀ g ∈ S, h₀ * g ∈ S := by
    intro g hg v hv
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hg v hv, hh₀S v hv]
  have hinvS : ∀ g ∈ S, h₀⁻¹ * g ∈ S := by
    intro g hg v hv
    have h1 : (h₀ : Matrix (Fin r) (Fin r) k) *ᵥ v = v := hh₀S v hv
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hg v hv]
    conv_lhs => rw [← h1]
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have hbij : Set.BijOn (fun g => h₀ * g) S S := by
    refine ⟨fun g hg => hmulS g hg, fun x _ y _ hxy => mul_left_cancel hxy, ?_⟩
    intro g hg
    exact ⟨h₀⁻¹ * g, hinvS g hg, by simp⟩
  set F : GL (Fin r) k → ℂ := fun g => ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) with hF
  have hFmul : ∀ g, F (h₀ * g) = ((ξ c : ℂˣ) : ℂ) * F g := by
    intro g
    simp [hF, map_mul, hdeth₀]
  have key : ∑ᶠ g ∈ S, F (h₀ * g) = ∑ᶠ g ∈ S, F g :=
    finsum_mem_eq_of_bijOn (fun g => h₀ * g) hbij (fun x _ => rfl)
  simp_rw [hFmul] at key
  rw [← mul_finsum_mem] at key
  have hc' : ((ξ c : ℂˣ) : ℂ) ≠ 1 := by
    intro h
    exact hc (Units.ext h)
  have : (((ξ c : ℂˣ) : ℂ) - 1) * ∑ᶠ g ∈ S, F g = 0 := by
    rw [sub_mul, key, one_mul, sub_self]
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (sub_eq_zero.mp h) hc'
  · exact h

end GlobalTheory
end

section

universe u_1

namespace GlobalTheory.IntegralTrace

open Polynomial

theorem exists_monic_aeval_eq_zero {R E : Type*} [CommRing R] [Field E] [Algebra R E] {n : ℕ}
    (L : Submodule R (Fin n → E)) (hL : L.FG)
    (hspan : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (M : Matrix (Fin n) (Fin n) E) (hM : ∀ x ∈ L, M.mulVec x ∈ L) :
    ∃ p : R[X], p.Monic ∧ aeval M (p.map (algebraMap R E)) = 0 := by
  haveI : Module.Finite R L := Module.Finite.iff_fg.mpr hL
  let g : Module.End R (Fin n → E) := (Matrix.toLin' M).restrictScalars R
  have hg : ∀ x ∈ L, g x ∈ L := fun x hx => by simpa [g] using hM x hx
  obtain ⟨p, hp, hp0⟩ := LinearMap.exists_monic_and_aeval_eq_zero R (g.restrict hg)
  refine ⟨p, hp, ?_⟩
  have key : ∀ (q : R[X]) (x : L), ((aeval (g.restrict hg) q x : L) : Fin n → E)
      = (aeval M (q.map (algebraMap R E))).mulVec x := by
    intro q
    induction q using Polynomial.induction_on with
    | C a =>
      intro x
      simp [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec]
    | add a b ha hb =>
      intro x
      simp only [map_add (f := _), Polynomial.map_add (f := _), LinearMap.add_apply, Submodule.coe_add, ha, hb,
        Matrix.add_mulVec]
    | monomial k a ih =>
      intro x
      rw [pow_succ, ← mul_assoc, map_mul, Polynomial.map_mul, map_mul (aeval M), Module.End.mul_apply,
        ih,
        Polynomial.map_X, aeval_X, aeval_X, ← Matrix.mulVec_mulVec]
      rfl
  apply Matrix.toLin'.injective
  rw [map_zero]
  apply LinearMap.ext_on hspan
  intro x hx
  have := key p ⟨x, hx⟩
  rw [hp0] at this
  simpa using this.symm

theorem isIntegral_trace {E : Type u_1} [inst : Field E] [NumberField E] (_φ : E →+* ℂ) {n : ℕ}
    (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)) (hL : Submodule.FG L)
    (hspan : Submodule.span E (↑L : Set (Fin n → E)) = ⊤)
    (M : Matrix (Fin n) (Fin n) E) (hM : ∀ x ∈ L, Matrix.mulVec M x ∈ L) :
    IsIntegral ℤ (Matrix.trace M) := by
  obtain ⟨p, hp, hp0⟩ := exists_monic_aeval_eq_zero L hL hspan M hM
  let K := AlgebraicClosure E
  let N : Matrix (Fin n) (Fin n) K := (algebraMap E K).mapMatrix M
  have hN : aeval N (p.map (algebraMap (NumberField.RingOfIntegers E) K)) = 0 := by
    have h1 := Polynomial.aeval_algHom_apply ((Algebra.ofId E K).mapMatrix (m := Fin n)) M
      (p.map (algebraMap (NumberField.RingOfIntegers E) E))
    rw [hp0, map_zero] at h1
    rw [IsScalarTower.algebraMap_eq (NumberField.RingOfIntegers E) E K, ← Polynomial.map_map,
      aeval_map_algebraMap]
    exact h1
  rw [← isIntegral_algebraMap_iff (B := K)]
  have htr : algebraMap E K M.trace = N.trace := by
    simp [N, Matrix.trace]
  rw [htr, Matrix.trace_eq_sum_roots_charpoly]
  apply IsIntegral.multiset_sum
  intro z hz
  have hz1 : z ∈ spectrum K N := by
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
    exact (Polynomial.mem_roots N.charpoly_monic.ne_zero).mp hz
  have hz2 := spectrum.subset_polynomial_aeval N
    (p.map (algebraMap (NumberField.RingOfIntegers E) K)) ⟨z, hz1, rfl⟩
  rw [hN] at hz2
  have hz3 : eval z (p.map (algebraMap (NumberField.RingOfIntegers E) K)) = 0 := by
    by_contra h
    rw [spectrum.mem_iff] at hz2
    apply hz2
    rw [sub_zero]
    exact (IsUnit.mk0 _ h).map _
  have hz4 : IsIntegral (NumberField.RingOfIntegers E) z := ⟨p, hp, by rwa [eval_map] at hz3⟩
  exact isIntegral_trans z hz4

end GlobalTheory.IntegralTrace
end

section

open NumberField IsDedekindDomain

namespace GlobalTheory

theorem ringOfIntegers_map_mem_valuationSubring {K : Type} [Field K] [NumberField K]
    (A : ValuationSubring ℂ) (σ : K →+* ℂ) (x : 𝓞 K) : σ (x : K) ∈ A := by
  have h1 : IsIntegral ℤ (σ (x : K)) := (RingOfIntegers.isIntegral_coe x).map σ.toIntAlgHom
  have h2 : IsIntegral A (σ (x : K)) := h1.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
  rw [← hy]
  exact y.2

noncomputable def ringOfIntegersToValuationSubring {K : Type} [Field K] [NumberField K]
    (A : ValuationSubring ℂ) (σ : K →+* ℂ) : 𝓞 K →+* A :=
  ((σ.comp (algebraMap (𝓞 K) K)).codRestrict A.toSubring
    (fun x => ringOfIntegers_map_mem_valuationSubring A σ x))

theorem valuation_embedding_generator_eq_one :
    ∀ (K : Type) [Field K] [NumberField K] (A : ValuationSubring ℂ) (p : ℕ), p.Prime →
      (p : ℂ) ∈ A.nonunits → ∀ (P : HeightOneSpectrum (𝓞 K)), (p : 𝓞 K) ∉ P.asIdeal →
      ∀ (α : 𝓞 K) (h : ℕ), Ideal.span {α} = P.asIdeal ^ h →
      ∀ σ : K →+* ℂ, A.valuation (σ (α : K)) = 1 := by
  intro K _ _ A p _ hpA P hpP α h hα σ
  set f := ringOfIntegersToValuationSubring A σ with hf
  have hfx : ∀ x : 𝓞 K, ((f x : A) : ℂ) = σ (x : K) := fun x => rfl
  set Q : Ideal (𝓞 K) := (IsLocalRing.maximalIdeal A).comap f with hQ
  have hQp : Q.IsPrime := Ideal.comap_isPrime f (IsLocalRing.maximalIdeal A)
  have hQne : Q ≠ ⊤ := hQp.ne_top
  have hmem : ∀ x : 𝓞 K, x ∈ Q ↔ A.valuation (σ (x : K)) < 1 := by
    intro x
    rw [hQ, Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff, hfx]
  have hpQ : (p : 𝓞 K) ∈ Q := by
    rw [hmem]
    have : σ (((p : 𝓞 K) : K)) = (p : ℂ) := by simp
    rw [this]
    exact (ValuationSubring.mem_nonunits_iff A).mp hpA
  refine le_antisymm ?_ ?_
  · exact (ValuationSubring.valuation_le_one_iff A _).mpr (ringOfIntegers_map_mem_valuationSubring A σ α)
  · by_contra hlt
    push_neg at hlt
    have hαQ : α ∈ Q := (hmem α).mpr hlt
    have hspan : P.asIdeal ^ h ≤ Q := by
      rw [← hα, Ideal.span_singleton_le_iff_mem]
      exact hαQ
    have hPQ : P.asIdeal ≤ Q := Ideal.IsPrime.le_of_pow_le hspan
    have hPeq : P.asIdeal = Q := P.isMaximal.eq_of_le hQne hPQ
    exact hpP (hPeq ▸ hpQ)

end GlobalTheory
end

section

open scoped NNReal

namespace GlobalTheory

theorem ringHom_eq_of_perfect_of_dvd_sub :
    ∀ (l : ℕ) [Fact l.Prime] (R O : Type) [CommRing R] [CharP R l] [PerfectRing R l] [CommRing O] [CharP O l] (x : O) (e : ℕ), 0 < e → IsHausdorff (Ideal.span {x}) O → ∀ ψ ψ' : R →+* O, (∀ y, x ^ e ∣ ψ y - ψ' y) → ψ = ψ' := by
  intro l _ R O _ _ _ _ _ x e he hH ψ ψ' h
  ext y
  rw [← sub_eq_zero]
  apply hH.haus
  intro n
  rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]
  obtain ⟨z, rfl⟩ : ∃ z : R, z ^ l ^ n = y :=
    ⟨(iterateFrobeniusEquiv R l n).symm y, by
      have hs := (iterateFrobeniusEquiv R l n).apply_symm_apply y
      rwa [iterateFrobeniusEquiv_apply, iterateFrobenius_def] at hs⟩
  rw [map_pow, map_pow, ← sub_pow_char_pow]
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hn : n ≤ e * l ^ n :=
    (Nat.lt_pow_self (by omega)).le.trans (Nat.le_mul_of_pos_left _ he)
  exact (pow_dvd_pow x hn).trans (by rw [pow_mul]; exact pow_dvd_pow_of_dvd (h z) _)

end GlobalTheory
end
