module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.Bundle003
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.Bundle001
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HostGeneratorPowFourTraceNormModEight
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle702
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle681
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle669
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem exists_least_points {X : Type} [AddCommGroup X] {n : ℕ} (r : (Fin n → ℤ) →ₗ[ℤ] X)
    (hr : Function.Surjective r) (β : LinearMap.BilinForm ℤ X) (hβ : ∀ y, 0 ≤ β y y) :
    ∃ a : (Fin n → ZMod (1 + 1)) → Fin n → ℤ, (∀ y, redV 1 (a y) = y) ∧ ∀ y, IsMin2 (toReal β) (r (a y)) := by
  have hmin : ∀ y : Fin n → ZMod (1 + 1), ∃ c : Fin n → ℤ, redV 1 c = y ∧
      ∀ c', redV 1 c' = y → β (r c) (r c) ≤ β (r c') (r c') := fun y => by
    obtain ⟨c0, h0⟩ := redV_surjective 1 n y
    obtain ⟨c, hc, hm⟩ := WellFounded.has_min
      (InvImage.wf (fun c : Fin n → ℤ => (β (r c) (r c)).toNat) Nat.lt_wfRel.wf)
      {c | redV 1 c = y} ⟨c0, h0⟩
    refine ⟨c, hc, fun c' hc' => ?_⟩
    have h1 : ¬ (β (r c') (r c')).toNat < (β (r c) (r c)).toNat := hm c' hc'
    have h2 := hβ (r c)
    have h3 := hβ (r c')
    omega
  choose a ha hm using hmin
  refine ⟨a, ha, fun y x => ?_⟩
  obtain ⟨d, rfl⟩ := hr x
  have h := hm y (a y + (((1 : ℕ) : ℤ) + 1) • d) (by rw [redV_add_smul, ha])
  have e : r (a y + (((1 : ℕ) : ℤ) + 1) • d) = r (a y) + (r d + r d) := by
    rw [map_add (f := _), map_smul, show (((1 : ℕ) : ℤ) + 1) = 2 by norm_num, two_smul]
  rw [e] at h
  simp only [toReal, LinearMap.compr₂_apply, Algebra.linearMap_apply, eq_intCast]
  exact_mod_cast h

theorem apply_eq_zero_of_self {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X) (hs : ∀ y z, β y z = β z y)
    (hβ : ∀ y, 0 ≤ β y y) {z : X} (hz : β z z = 0) (w : X) : β z w = 0 := by
  by_contra ht
  have h := hβ (w + (-(β w w + 1) * β z w) • z)
  simp only [map_add (f := _), LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hz, hs w z] at h
  have h1 : 1 ≤ β z w * β z w := mul_self_pos.2 ht
  have h2 := hβ w
  nlinarith

theorem eq_zero_of_covers {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X) (hs : ∀ y z, β y z = β z y)
    (hβ : ∀ y, 0 ≤ β y y) {ι : Type} {a : ι → X} (hc : Covers2 a) (h0 : ∀ i, β (a i) (a i) = 0) : β = 0 := by
  have hdiv : ∀ (k : ℕ) (z w : X), (2 : ℤ) ^ k ∣ β z w := by
    intro k
    induction k with
    | zero => intro z w; simp
    | succ k ih =>
      intro z w
      obtain ⟨i, x, rfl⟩ := hc z
      obtain ⟨m, hm⟩ := ih x w
      refine ⟨m, ?_⟩
      simp only [map_add (f := _), LinearMap.add_apply, apply_eq_zero_of_self β hs hβ (h0 i) w, hm]
      ring
  refine LinearMap.ext₂ fun z w => ?_
  refine Int.eq_zero_of_abs_lt_dvd (hdiv (β z w).natAbs z w) ?_
  rw [Int.abs_eq_natAbs]
  exact_mod_cast Nat.lt_two_pow_self

theorem vorFun_int_pos : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (g q : ℕ)
    (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X],
    Module.finrank ℤ O * q ≤ g → Module.finrank O X ≤ q →
    (∀ β : LinearMap.BilinForm ℤ X, (∀ y, 0 ≤ β y y) → ∃ n : ℤ, (vorFun O g).evalZ β = n) ∧
    ∀ β : LinearMap.BilinForm ℤ X, (∀ y z, β y z = β z y) → (∀ y, 0 ≤ β y y) → β ≠ 0 → 0 < (vorFun O g).evalZ β := by
  intro O _ _ _ _ bar g q X _ _ _ _ hg hq
  have hfin : Module.Finite ℤ X := Module.Finite.trans O X
  have hO : Module.Free ℤ O := Module.free_of_finite_type_torsion_free'
  have htf : Module.IsTorsionFree ℤ X := Module.IsTorsionFree.trans O
  have hfree : Module.Free ℤ X := Module.free_of_finite_type_torsion_free'
  have hn : Module.finrank ℤ X ≤ g := by
    rw [GlobalTheory.finrank_int_eq_mul_of_finite (O := O) (M := X)]
    exact (Nat.mul_le_mul_left _ hq).trans hg
  let b : Module.Basis (Fin (Module.finrank ℤ X)) ℤ X := Module.finBasis ℤ X
  let r : (Fin (Module.finrank ℤ X) → ℤ) →ₗ[ℤ] X := b.equivFun.symm.toLinearMap
  have hr : Function.Surjective r := b.equivFun.symm.surjective
  have key : ∀ β : LinearMap.BilinForm ℤ X, (∀ y, 0 ≤ β y y) →
      ∃ a : (Fin (Module.finrank ℤ X) → ZMod (1 + 1)) → Fin (Module.finrank ℤ X) → ℤ, Covers2 (fun y => r (a y)) ∧
        (vorFun O g).evalZ β = 2 ^ (g - Module.finrank ℤ X) * ∑ y, (β (r (a y)) (r (a y)) : ℝ) := by
    intro β hβ
    obtain ⟨a, ha, hm⟩ := exists_least_points r hr β hβ
    obtain ⟨hc, h⟩ := vorFun_value_le O bar g X _ r a hr ha
    refine ⟨a, hc, ?_⟩
    have hB : ∀ y, 0 ≤ toReal β y y := fun y => by
      simp only [toReal, LinearMap.compr₂_apply, Algebra.linearMap_apply, eq_intCast]
      exact_mod_cast hβ y
    have h1 := ((h (toReal β) hB).2).2 hm
    rw [evalR_toReal] at h1
    have h2 : ∀ u v, toReal β u v = (β u v : ℝ) := fun u v => by
      simp only [toReal, LinearMap.compr₂_apply, Algebra.linearMap_apply, eq_intCast]
    simp only [h2] at h1
    have h3 : (2 : ℝ) ^ g = 2 ^ Module.finrank ℤ X * 2 ^ (g - Module.finrank ℤ X) := by
      rw [← pow_add, Nat.add_sub_cancel' hn]
    rw [h3, mul_assoc] at h1
    exact mul_left_cancel₀ (by positivity) h1
  refine ⟨fun β hβ => ?_, fun β hs hβ hne => ?_⟩
  · obtain ⟨a, -, h⟩ := key β hβ
    exact ⟨2 ^ (g - Module.finrank ℤ X) * ∑ y, β (r (a y)) (r (a y)), by rw [h]; push_cast; rfl⟩
  · obtain ⟨a, hc, h⟩ := key β hβ
    have hnn : ∀ y, (0 : ℝ) ≤ (β (r (a y)) (r (a y)) : ℝ) := fun y => by exact_mod_cast hβ _
    rw [h]
    refine mul_pos (by positivity) (lt_of_le_of_ne (Finset.sum_nonneg fun y _ => hnn y) fun h0 => hne ?_)
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun y _ => hnn y).1 h0.symm
    exact eq_zero_of_covers β hs hβ hc fun y => by exact_mod_cast h1 y (Finset.mem_univ y)

end GlobalTheory.CompanionTheory.Ar.Fan
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

theorem _root_.GlobalTheory.T.balanced_nonneg_form_in_psd_cone : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] (β : LinearMap.BilinForm ℤ X), β ∈ balForms bar X → (∀ y, 0 ≤ β y y) → toReal β ∈ psdCone (bar := bar) (X := X) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.PsdConeMembership.toReal_mem_psdCone_of_nonneg | exact GlobalTheory.CompanionTheory.Ar.Fan.PsdConeMembership.toReal_mem_psdCone_of_nonneg | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.PsdConeMembership.toReal_mem_psdCone_of_nonneg <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem contact_inter_rcone_spanned : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O]
    (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] (ι : Type) [Finite ι]
    (a : ι → X) (m : ℕ) (u : Fin m → LinearMap.BilinForm ℤ X), (∀ i y z, u i y z = u i z y) → (∀ i y, 0 ≤ u i y y) →
    ∃ (s : ℕ) (γ : Fin s → LinearMap.BilinForm ℤ X), (∀ i, γ i ∈ balForms bar X) ∧ (∀ i y, 0 ≤ γ i y y) ∧
      (∀ i, toReal (γ i) ∈ contact bar a) ∧ ∀ B ∈ contact bar a, B ∈ rcone u → B ∈ rcone γ := by
  intro O _ _ _ _ bar X _ _ _ _ ι _ a m u hsym hpsd
  classical
  choose F hF using fun i => isMin2_iff_finite X m u (a i) hpsd
  let A : Set (Fin m → ℤ) := ⋃ i, (fun (x : X) (k : Fin m) =>
    u k (a i) (a i) - u k (a i + (x + x)) (a i + (x + x))) '' (F i : Set X)
  let V : Set (Fin m → ℤ) := Set.range fun (p : O × X × X) (k : Fin m) =>
    u k (p.1 • p.2.1) p.2.2 - u k p.2.1 (bar p.1 • p.2.2)
  have hA : A.Finite := Set.finite_iUnion fun i => (F i).finite_toSet.image _
  obtain ⟨r, v, hv, -⟩ := GlobalTheory.T.minkowskiWeyl_orthant_cone_integral_constraints m A V hA
  have hval : ∀ (t : Fin m → ℝ) (y z : X), (∑ k, t k • toReal (u k)) y z = ∑ k, t k * (u k y z : ℝ) :=
    fun t y z => by simp [LinearMap.sum_apply]
  have hdiff : ∀ (t : Fin m → ℝ) (p p' q q' : X), ∑ k, (((u k p p' - u k q q' : ℤ)) : ℝ) * t k =
      (∑ k, t k • toReal (u k)) p p' - (∑ k, t k • toReal (u k)) q q' := fun t p p' q q' => by
    rw [hval, hval, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by push_cast; ring
  have hAiff : ∀ t : Fin m → ℝ, (∀ k, 0 ≤ t k) → ((∀ i, IsMin2 (∑ k, t k • toReal (u k)) (a i)) ↔
      ∀ b ∈ A, ∑ k, (b k : ℝ) * t k ≤ 0) := fun t ht => by
    constructor
    · intro h b hb
      obtain ⟨i, x, -, rfl⟩ : ∃ i, ∃ x ∈ (F i : Set X), (fun k : Fin m =>
          u k (a i) (a i) - u k (a i + (x + x)) (a i + (x + x))) = b := by
        simpa [A] using hb
      rw [hdiff]
      linarith [h i x]
    · intro h i
      refine (hF i _ ⟨t, ht, rfl⟩).2 fun x hx => ?_
      have := h _ (Set.mem_iUnion.2 ⟨i, x, hx, rfl⟩)
      rw [hdiff] at this
      linarith
  have hViff : ∀ t : Fin m → ℝ, (∀ (c : O) (y z : X), (∑ k, t k • toReal (u k)) (c • y) z =
      (∑ k, t k • toReal (u k)) y (bar c • z)) ↔ ∀ b ∈ V, ∑ k, (b k : ℝ) * t k = 0 := fun t => by
    constructor
    · rintro h _ ⟨⟨c, y, z⟩, rfl⟩
      simp only []
      rw [hdiff, h, sub_self]
    · intro h c y z
      have := h _ ⟨(c, y, z), rfl⟩
      simp only [] at this
      rw [hdiff] at this
      linarith
  let γ : Fin r → LinearMap.BilinForm ℤ X := fun s => ∑ k, v s k • u k
  have hγ : ∀ s y z, γ s y z = ∑ k, (v s k : ℤ) * u k y z := fun s y z => by
    simp [γ, LinearMap.sum_apply]
  have hγr : ∀ s, toReal (γ s) = ∑ k, (v s k : ℝ) • toReal (u k) := fun s => LinearMap.ext₂ fun y z => by
    rw [hval, toReal_apply, hγ]
    push_cast
    rfl
  have hvs : ∀ s, (∀ k, (0 : ℝ) ≤ v s k) ∧ (∀ b ∈ A, ∑ k, (b k : ℝ) * (v s k : ℝ) ≤ 0) ∧
      (∀ b ∈ V, ∑ k, (b k : ℝ) * (v s k : ℝ) = 0) := fun s => by
    refine (hv fun k => (v s k : ℝ)).2 ⟨Pi.single s 1, fun j => ?_, ?_⟩
    · by_cases h : j = s
      · subst h; simp
      · simp [Pi.single_eq_of_ne h]
    · rw [Finset.sum_eq_single s (fun j _ h => by simp [Pi.single_eq_of_ne h]) (by simp)]
      simp
  have hbal : ∀ s, γ s ∈ balForms bar X := fun s => by
    refine mem_balForms.2 ⟨fun y z => ?_, fun c y z => ?_⟩
    · simp only [hγ, hsym _ y z]
    · have := (hViff _).2 (hvs s).2.2 c y z
      rw [← hγr] at this
      simpa using this
  have hnn : ∀ s y, 0 ≤ γ s y y := fun s y => by
    rw [hγ]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (Int.natCast_nonneg _) (hpsd k y)
  refine ⟨r, γ, hbal, hnn, fun s => ⟨?_, fun i => ?_⟩, ?_⟩
  · simpa using GlobalTheory.T.nonneg_sum_smul_intBilinFormToReal_mem_psdCone O bar X 1 ![γ s] ![1] (by simpa using hbal s) (by simpa using hnn s) (by simp)
  · rw [hγr]
    exact (hAiff _ (hvs s).1).2 (hvs s).2.1 i
  · rintro _ hB ⟨t, ht, rfl⟩
    have hre := mem_realForms_of_mem_psdCone hB.1
    obtain ⟨c, hc, rfl⟩ := (hv t).1 ⟨ht, (hAiff t ht).1 hB.2, (hViff t).1 hre.2⟩
    refine ⟨c, hc, LinearMap.ext₂ fun y z => ?_⟩
    rw [hval]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, hγ, smul_eq_mul, Finset.sum_apply, Pi.smul_apply]
    push_cast
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun k _ => by ring

end GlobalTheory.CompanionTheory.Ar.Fan
end
end

section

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem isMin2_sum_smul {X : Type} [AddCommGroup X] {m : ℕ} (B : Fin m → X →ₗ[ℤ] X →ₗ[ℤ] ℝ) (c : Fin m → ℝ) (y : X)
    (hc : ∀ i, 0 ≤ c i) (hB : ∀ i, IsMin2 (B i) y) : IsMin2 (∑ i, c i • B i) y := by
  intro x
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hB i x) (hc i)

def sumDiag {X ι : Type} [AddCommGroup X] [Fintype ι] (g : ℕ) (p : ι → X) : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ where
  toFun β := 2 ^ g * ∑ y, β (p y) (p y)
  map_add' β γ := by
    simp only [LinearMap.add_apply, Finset.sum_add_distrib, mul_add]
  map_smul' k β := by
    simp only [LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]
    ring

theorem isCell_vorFun_of_contact : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O)
    (g : ℕ) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] (n : ℕ)
    (r : (Fin n → ℤ) →ₗ[ℤ] X) (a : (Fin n → ZMod (1 + 1)) → Fin n → ℤ), Function.Surjective r → (∀ y, redV 1 (a y) = y) →
    ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), (∀ i, γ i ∈ balForms bar X) → (∀ i y, 0 ≤ γ i y y) →
    (∀ i, toReal (γ i) ∈ contact bar fun y => r (a y)) → (contact bar fun y => r (a y)) ⊆ rcone γ →
    IsCell bar (vorFun O g) γ := by
  intro O _ _ _ _ bar g X _ _ _ _ n r a hr ha m γ hbal hpsd hcon hsub
  have hval := (vorFun_value_le O bar g X n r a hr ha).2
  have hreal : ∀ (β : LinearMap.BilinForm ℤ X) , (∀ y, 0 ≤ β y y) → ∀ y, 0 ≤ toReal β y y := fun β hβ y => by
    simpa [toReal_apply] using hβ y
  have hℓ : ∀ β : LinearMap.BilinForm ℤ X, ((sumDiag g (fun y => r (a y)) β : ℤ) : ℝ) =
      2 ^ g * ∑ y, toReal β (r (a y)) (r (a y)) := fun β => by
    simp [sumDiag, toReal_apply]
  have hgen : ∀ i, (2 : ℝ) ^ n * (vorFun O g).evalZ (γ i) = sumDiag g (fun y => r (a y)) (γ i) := fun i => by
    rw [hℓ, ← evalR_toReal]
    exact (hval _ (hreal _ (hpsd i))).2.2 (hcon i).2
  refine ⟨hbal, hpsd, (linearOn_iff _ γ).2 fun c hc => ?_, 2 ^ n, sumDiag g (fun y => r (a y)), by positivity, ?_, ?_, ?_⟩
  · have hS : ∀ y, 0 ≤ (∑ i, c i • toReal (γ i)) y y := fun y => by
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
      exact Finset.sum_nonneg fun i _ => mul_nonneg (hc i) (hreal _ (hpsd i) y)
    have h1 := (hval _ hS).2.2 fun y => isMin2_sum_smul _ c _ hc fun i => (hcon i).2 y
    have hp : (2 : ℝ) ^ n ≠ 0 := by positivity
    refine mul_left_cancel₀ hp (h1.trans ?_)
    have h2 : ∀ i, (2 : ℝ) ^ g * ∑ y, toReal (γ i) (r (a y)) (r (a y)) = 2 ^ n * (vorFun O g).evalZ (γ i) := fun i => by
      rw [hgen, hℓ]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.mul_sum, mul_left_comm, h2, mul_left_comm]
  · intro i
    push_cast
    exact (hgen i).symm
  · intro β _ hβ
    have h := (hval _ (hreal β hβ)).1
    rw [evalR_toReal] at h
    rw [hℓ]
    push_cast
    exact h
  · intro β hb hβ he
    have hmin : ∀ y, IsMin2 (toReal β) (r (a y)) := by
      refine (hval _ (hreal β hβ)).2.1 ?_
      rw [evalR_toReal, ← hℓ]
      exact_mod_cast he
    have hpc : toReal β ∈ psdCone (bar := bar) (X := X) := by
      simpa using ConeSub.sum_smul_toReal_mem_psdCone O bar X 1 ![β] ![1] (by simp [hb]) (by simp [hβ]) (by simp)
    exact exists_nat_comb_of_toReal_mem_rcone X m γ β (hsub ⟨hpc, hmin⟩)

end GlobalTheory.CompanionTheory.Ar.Fan
end
end
