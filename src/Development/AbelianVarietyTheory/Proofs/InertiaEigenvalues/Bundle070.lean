module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle003
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
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
public import Mathlib.LinearAlgebra.FreeModule.PID

@[expose] public section

section

noncomputable section
namespace GlobalTheory.IndependentSpanDual
open scoped LaurentSeries PowerSeries
open GlobalTheory.PhiGam

variable {k : Type} [Field k]

theorem exists_indep_span {Q : Type} [AddCommGroup Q] [Module k⸨X⸩ Q] [Module k⟦X⟧ Q]
    [IsScalarTower k⟦X⟧ k⸨X⸩ Q] {P : Submodule k⟦X⟧ Q} (hP : P.FG) :
    ∃ (ι : Type) (_ : Fintype ι) (e : ι → Q), LinearIndependent k⸨X⸩ e ∧
      Submodule.span k⟦X⟧ (Set.range e) = P := by
  classical
  haveI : Module.Finite k⟦X⟧ P := Module.Finite.iff_fg.mpr hP
  haveI : NoZeroSMulDivisors k⟦X⟧ Q := by
    refine ⟨fun {c x} h => ?_⟩
    by_contra hne
    push_neg at hne
    have hc : algebraMap k⟦X⟧ k⸨X⸩ c ≠ 0 := by
      intro h0
      exact hne.1 ((IsFractionRing.injective k⟦X⟧ k⸨X⸩) (by rw [h0, map_zero]))
    have h' : algebraMap k⟦X⟧ k⸨X⸩ c • x = 0 := by
      rw [algebraMap_smul]
      exact h
    exact hne.2 ((smul_eq_zero.mp h').resolve_left hc)
  haveI : Module.Free k⟦X⟧ P := Module.free_of_finite_type_torsion_free'
  let b := Module.Free.chooseBasis k⟦X⟧ P
  refine ⟨Module.Free.ChooseBasisIndex k⟦X⟧ P, inferInstance, fun i => (b i : Q), ?_, ?_⟩
  · have hli : LinearIndependent k⟦X⟧ (P.subtype ∘ b) :=
      b.linearIndependent.map' P.subtype (Submodule.ker_subtype P)
    exact (LinearIndependent.iff_fractionRing k⟦X⟧ k⸨X⸩).mp hli
  · have hr : Set.range (fun i => (b i : Q)) = P.subtype '' Set.range b := by
      rw [← Set.range_comp]
      rfl
    rw [hr, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]

theorem exists_form {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k V] {l n : ℕ} {R : RingPG k l}
    (D : ModPG R n V) (i : ZMod n) (t : V →ₗ[k⸨X⸩] k⸨X⸩) :
    ∃ u : V →ₗ[k⸨X⸩] k⸨X⸩, ∀ x, u (D.φ i x) = R.φ (t x) := by
  let b := Module.Basis.ofVectorSpace k⸨X⸩ V
  let c := Module.Basis.mk (D.linearIndependent_φ i b) (D.span_φ i b).ge
  refine ⟨c.constr k⸨X⸩ fun j => R.φ (t (b j)), fun x => ?_⟩
  have hx : x ∈ Submodule.span k⸨X⸩ (Set.range b) := by rw [b.span_eq]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    have hc : D.φ i (b j) = c j :=
      (Module.Basis.mk_apply (D.linearIndependent_φ i b) (D.span_φ i b).ge j).symm
    rw [hc, Module.Basis.constr_basis]
  | zero => simp
  | add y z _ _ hy hz => simp only [map_add (f := _), hy, hz]
  | smul a y _ hy => rw [D.φ_semi i a y, map_smul, map_smul, hy, smul_eq_mul, smul_eq_mul, map_mul]

theorem exists_dual {K Q ι : Type} [Field K] [AddCommGroup Q] [Module K Q] [DecidableEq ι] {e : ι → Q}
    (he : LinearIndependent K e) (j : ι) :
    ∃ t : Q →ₗ[K] K, ∀ m, t (e m) = if m = j then 1 else 0 := by
  classical
  obtain ⟨g, hg⟩ := LinearMap.exists_extend ((Module.Basis.span he).coord j)
  refine ⟨g, fun m => ?_⟩
  have hm : e m = (Submodule.span K (Set.range e)).subtype (Module.Basis.span he m) := by
    rw [Module.Basis.span_apply]
    rfl
  rw [hm, ← LinearMap.comp_apply, hg, Module.Basis.coord_apply, Module.Basis.repr_self,
    Finsupp.single_apply]

theorem comap_pull {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V]
    [IsScalarTower k⟦X⟧ k⸨X⸩ V] {W : Type} [AddCommGroup W] [Module k⸨X⸩ W] [Module k⟦X⟧ W]
    [IsScalarTower k⟦X⟧ k⸨X⸩ W] [Module k V] [Module k W] {l n : ℕ} {R : RingPG k l}
    (D : ModPG R n V) (D' : ModPG R n W) (i : ZMod n) (f g : W →ₗ[k⸨X⸩] V)
    (_hf : Function.Injective f) (hg : Function.Injective g)
    (h : ∀ x, g (D'.φ i x) = D.φ i (f x)) {N : Submodule k⟦X⟧ V} (hN : N.FG) :
    (pull (D.φ i) N).comap (g.restrictScalars k⟦X⟧) = pull (D'.φ i) (N.comap (f.restrictScalars k⟦X⟧)) := by
  classical
  apply le_antisymm
  swap
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    change g (D'.φ i x) ∈ pull (D.φ i) N
    rw [h]
    exact Submodule.subset_span ⟨_, hx, rfl⟩
  let π := (LinearMap.range f).mkQ
  obtain ⟨ι, _, e, he, hsp⟩ := exists_indep_span (hN.map (π.restrictScalars k⟦X⟧))
  have hlift : ∀ j, ∃ s ∈ N, π s = e j := fun j => by
    have : e j ∈ N.map (π.restrictScalars k⟦X⟧) := hsp ▸ Submodule.subset_span ⟨j, rfl⟩
    exact this
  choose s hsN hs using hlift

  have hle : pull (D.φ i) N ≤ (pull (D'.φ i) (N.comap (f.restrictScalars k⟦X⟧))).map (g.restrictScalars k⟦X⟧) ⊔
      Submodule.span k⟦X⟧ (Set.range fun j => D.φ i (s j)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    have hx' : π x ∈ Submodule.span k⟦X⟧ (Set.range e) := hsp ▸ ⟨x, hx, rfl⟩
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun k⟦X⟧).1 hx'
    have h0 : x - ∑ j, a j • s j ∈ LinearMap.range f := by
      rw [← Submodule.ker_mkQ (LinearMap.range f), LinearMap.mem_ker]
      change (π.restrictScalars k⟦X⟧) _ = 0

      rw [map_sub, map_sum, sub_eq_zero]
      simp only [map_smul, LinearMap.restrictScalars_apply, hs, ha]
    obtain ⟨w, hw⟩ := h0
    have hwN : f w ∈ N := hw ▸ N.sub_mem hx (N.sum_mem fun j _ => N.smul_mem _ (hsN j))
    have hx2 : x = f w + ∑ j, a j • s j := by rw [hw, sub_add_cancel]

    rw [hx2, map_add (f := _), map_sum, ← h]
    refine Submodule.add_mem_sup ⟨_, Submodule.subset_span ⟨w, hwN, rfl⟩, rfl⟩
      (Submodule.sum_mem _ fun j _ => ?_)
    obtain ⟨b, hb⟩ := R.φ_int (a j)
    have : D.φ i (a j • s j) = b • D.φ i (s j) := by
      rw [← algebraMap_smul k⸨X⸩ (a j), D.φ_semi i, ← algebraMap_smul k⸨X⸩ b]
      exact congrArg (· • D.φ i (s j)) hb
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  intro y hy
  obtain ⟨_, ⟨p, hp, rfl⟩, q, hq, hpq⟩ := Submodule.mem_sup.1 (hle hy)
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun k⟦X⟧).1 hq
  have hq' : ∑ j, a j • D.φ i (s j) = g (y - p) := by
    rw [map_sub, eq_sub_iff_add_eq']
    exact hpq
  have ha : ∀ j, algebraMap k⟦X⟧ k⸨X⸩ (a j) = 0 := fun j => by
    obtain ⟨t, ht⟩ := exists_dual he j
    obtain ⟨u, hu⟩ := exists_form D i (t.comp π)
    have hug : u.comp g = 0 := by
      refine LinearMap.ext_on_range (D'.etale i) fun x => ?_
      have : π (f x) = 0 := (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩
      rw [LinearMap.comp_apply, h, hu, LinearMap.comp_apply, this, map_zero, map_zero, LinearMap.zero_apply]
    have h1 : u (∑ m, a m • D.φ i (s m)) = 0 := by
      rw [hq']; exact LinearMap.congr_fun hug _
    have h2 : ∀ m, u (a m • D.φ i (s m)) = if m = j then algebraMap k⟦X⟧ k⸨X⸩ (a m) else 0 := fun m => by
      rw [← algebraMap_smul k⸨X⸩ (a m), map_smul, hu, LinearMap.comp_apply, hs, ht]
      split_ifs <;> simp

    rw [map_sum] at h1
    simpa [h2] using h1
  have hz : g (y - p) = 0 := by
    rw [← hq']
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← algebraMap_smul k⸨X⸩ (a j), ha, zero_smul]
  have : y = p := sub_eq_zero.1 (hg (hz.trans (map_zero g).symm))
  rw [this]
  exact hp

end GlobalTheory.IndependentSpanDual
end
end

section

open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.PhiGam.Img

section
variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] {W : Type} [AddCommGroup W] [Module k⸨X⸩ W] [Module k⟦X⟧ W]
  [IsScalarTower k⟦X⟧ k⸨X⸩ W]

theorem map_sh (f : V →ₗ[k⸨X⸩] W) (a : ℤ) (N : Submodule k⟦X⟧ V) :
    (sh a N).map (f.restrictScalars k⟦X⟧) = sh a (N.map (f.restrictScalars k⟦X⟧)) := by
  ext x
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact mem_sh_iff_exists.2 ⟨f y, ⟨y, hy, rfl⟩, (f.map_smul _ y).symm⟩
  · intro hx
    obtain ⟨_, ⟨y, hy, rfl⟩, rfl⟩ := mem_sh_iff_exists.1 hx
    exact ⟨_, mem_sh_iff_exists.2 ⟨y, hy, rfl⟩, f.map_smul _ y⟩

theorem isLat_map (f : V →ₗ[k⸨X⸩] W) (hf : Function.Surjective f) {N : Submodule k⟦X⟧ V} (h : IsLat N) :
    IsLat (N.map (f.restrictScalars k⟦X⟧)) := by
  refine ⟨h.1.map _, ?_⟩
  have : ((N.map (f.restrictScalars k⟦X⟧) : Submodule k⟦X⟧ W) : Set W) = f '' (N : Set V) := rfl
  rw [this, ← Submodule.map_span, h.2, Submodule.map_top, LinearMap.range_eq_top.2 hf]

theorem map_pull [Module k V] [Module k W] (f g : V →ₗ[k⸨X⸩] W) (φ : V →ₗ[k] V) (φ' : W →ₗ[k] W)
    (h : ∀ x, f (φ x) = φ' (g x)) (N : Submodule k⟦X⟧ V) :
    (pull φ N).map (f.restrictScalars k⟦X⟧) = pull φ' (N.map (g.restrictScalars k⟦X⟧)) := by
  rw [pull, pull, Submodule.map_span, Submodule.map_coe, Set.image_image, Set.image_image]
  congr 1
  exact Set.image_congr fun x _ => h x

end

theorem image_lattice :
    ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l)
      {n : ℕ} [NeZero n]
      {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
      [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]
      [FiniteDimensional k⸨X⸩ V]
      {W : Type} [AddCommGroup W] [Module k⸨X⸩ W] [Module k⟦X⟧ W] [Module k W]
      [IsScalarTower k⟦X⟧ k⸨X⸩ W] [IsScalarTower k k⸨X⸩ W] [IsScalarTower k k⟦X⟧ W]
      [FiniteDimensional k⸨X⸩ W] (D : ModPG R n V) (D' : ModPG R n W)
      (f : ZMod n → V →ₗ[k⸨X⸩] W),
      (∀ i, Function.Surjective (f i)) →
      (∀ i x, f i (D.φ i x) = D'.φ i (f (i - 1) x)) →
      (∀ i x, f i (D.γ i x) = D'.γ i (f i x)) →
      ∀ (w w' : ZMod n → ℤ) (N : ZMod n → Submodule k⟦X⟧ V),
        (∀ i, IsLat (N i)) → CondAB D.φ w w' N → (∀ i, CondC (D.γ i) (N i)) →
        (let N' := fun i => (N i).map ((f i).restrictScalars k⟦X⟧)
         (∀ i, IsLat (N' i)) ∧ CondAB D'.φ w w' N' ∧ ∀ i, CondC (D'.γ i) (N' i)) := by
  intro k _ l _ _ R n _ V _ _ _ _ _ _ _ _ W _ _ _ _ _ _ _ _ D D' f hf hφ hγ w w' N hN hAB hC N'
  refine ⟨fun i => isLat_map (f i) (hf i) (hN i), fun i => ?_, fun i => ?_⟩
  · simp only [N']
    rw [← map_pull (f i) (f (i - 1)) (D.φ i) (D'.φ i) (hφ i), ← map_sh, ← map_sh]
    exact ⟨Submodule.map_mono (hAB i).1, Submodule.map_mono (hAB i).2⟩
  · rintro _ ⟨x, hx, rfl⟩
    simp only [N']
    rw [← map_sh]
    refine ⟨_, hC i x hx, ?_⟩
    change f i _ = D'.γ i (f i x) - f i x
    rw [map_sub, hγ]

end GlobalTheory.PhiGam.Img
end

section

noncomputable section

namespace GlobalTheory.UnimodMass

variable {G : Type*} [Group G]

def dcSetoid (Γ K : Subgroup G) : Setoid G := GlobalTheory.DoubleCosetSetoid.doubleCosetSetoid Γ K

abbrev DC (Γ K : Subgroup G) : Type _ := Quotient (dcSetoid Γ K)

def stabCard (Γ K : Subgroup G) (t : G) : ℕ := Nat.card {γ : Γ // t⁻¹ * (γ : G) * t ∈ K}

def mass (Γ K : Subgroup G) : ℚ := ∑ᶠ c : DC Γ K, ((stabCard Γ K c.out : ℕ) : ℚ)⁻¹

theorem finite_dc_of_le {Γ W K : Subgroup G} (hWK : W ≤ K) [Finite (DC Γ W)] : Finite (DC Γ K) := by
  let f : DC Γ W → DC Γ K := Quotient.map' (s₁ := dcSetoid Γ W) (s₂ := dcSetoid Γ K) id (by
    intro a b hab
    obtain ⟨γ, hγ, κ, hκ, e⟩ := hab
    exact ⟨γ, hγ, κ, hWK hκ, e⟩)
  refine Finite.of_surjective f ?_
  rintro ⟨x⟩
  exact ⟨Quotient.mk'' x, rfl⟩

theorem finite_dc_of_cover {Γ K : Subgroup G} (hT : ∃ T : Finset G, ∀ g, ∃ γ ∈ Γ, ∃ t ∈ T, ∃ κ ∈ K, g = γ * t * κ) :
    Finite (DC Γ K) := by
  obtain ⟨T, hT⟩ := hT
  refine Finite.of_surjective (fun t : T => (Quotient.mk'' (t : G) : DC Γ K)) ?_
  rintro ⟨g⟩
  obtain ⟨γ, hγ, t, ht, κ, hκ, e⟩ := hT g
  refine ⟨⟨t, ht⟩, Quotient.sound' ⟨γ, hγ, κ, hκ, e⟩⟩

theorem stabCard_pos {Γ K : Subgroup G} (t : G) (h : Finite {γ : Γ // t⁻¹ * (γ : G) * t ∈ K}) :
    0 < stabCard Γ K t := by
  haveI := h
  haveI : Nonempty {γ : Γ // t⁻¹ * (γ : G) * t ∈ K} := ⟨⟨1, by simp [K.one_mem]⟩⟩
  exact Nat.card_pos

theorem mass_pos {Γ K : Subgroup G} [Finite (DC Γ K)]
    (hfin : ∀ t : G, Finite {γ : Γ // t⁻¹ * (γ : G) * t ∈ K}) : 0 < mass Γ K := by
  haveI := Fintype.ofFinite (DC Γ K)
  rw [mass, finsum_eq_sum_of_fintype]
  have hne : (Finset.univ : Finset (DC Γ K)).Nonempty := ⟨Quotient.mk'' 1, Finset.mem_univ _⟩
  refine Finset.sum_pos (fun c _ => ?_) hne
  have := stabCard_pos c.out (hfin c.out)
  positivity

end GlobalTheory.UnimodMass

namespace GlobalTheory.UnimodMass

variable {G : Type*} [Group G]

theorem stabCard_eq {Γ K : Subgroup G} {t t' : G} (hr : (dcSetoid Γ K) t t') :
    stabCard Γ K t' = stabCard Γ K t := by
  obtain ⟨γ, hγ, κ, hκ, rfl⟩ := hr
  unfold stabCard
  refine Nat.card_congr
    { toFun := fun x => ⟨⟨γ⁻¹ * (x.1 : G) * γ, Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hγ) x.1.2) hγ⟩, ?_⟩
      invFun := fun x => ⟨⟨γ * (x.1 : G) * γ⁻¹, Γ.mul_mem (Γ.mul_mem hγ x.1.2) (Γ.inv_mem hγ)⟩, ?_⟩
      left_inv := fun x => by ext; simp [mul_assoc]
      right_inv := fun x => by ext; simp [mul_assoc] }
  · have := K.mul_mem (K.mul_mem hκ x.2) (K.inv_mem hκ)
    convert this using 1
    simp [mul_assoc]
  · have := K.mul_mem (K.mul_mem (K.inv_mem hκ) x.2) hκ
    convert this using 1
    simp [mul_assoc]

theorem stabCard_out (Γ K : Subgroup G) (x : G) :
    stabCard Γ K (Quotient.mk (dcSetoid Γ K) x).out = stabCard Γ K x :=
  (stabCard_eq (Quotient.mk_out (s := dcSetoid Γ K) x)).symm

theorem stabCard_conj (Γ K : Subgroup G) (h g : G) :
    stabCard Γ (K.map (MulAut.conj h).toMonoidHom) g = stabCard Γ K (g * h) := by
  unfold stabCard
  refine Nat.card_congr (Equiv.subtypeEquivRight fun γ => ?_)
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply, mul_assoc]

def dcConj (Γ K : Subgroup G) (h : G) : DC Γ (K.map (MulAut.conj h).toMonoidHom) ≃ DC Γ K :=
  Quotient.congr (Equiv.mulRight h) (by
    intro a b
    constructor
    · rintro ⟨γ, hγ, κ, hκ, e⟩
      rw [Subgroup.mem_map_equiv] at hκ
      refine ⟨γ, hγ, _, hκ, ?_⟩
      simp [e, MulAut.conj_symm_apply, mul_assoc]
    · rintro ⟨γ, hγ, κ, hκ, e⟩
      refine ⟨γ, hγ, h * κ * h⁻¹, ?_, ?_⟩
      · rw [Subgroup.mem_map_equiv]
        simpa [MulAut.conj_symm_apply, mul_assoc] using hκ
      · have e' : b = γ * a * h * κ * h⁻¹ := by
          have := congrArg (· * h⁻¹) e
          simpa [mul_assoc] using this
        rw [e']
        simp [mul_assoc])

theorem mass_conj (Γ K : Subgroup G) (h : G) :
    mass Γ (K.map (MulAut.conj h).toMonoidHom) = mass Γ K := by
  unfold mass
  rw [← finsum_comp_equiv (dcConj Γ K h)]
  refine finsum_congr fun c => ?_
  induction c using Quotient.inductionOn with
  | h x =>
    have e1 : dcConj Γ K h (Quotient.mk _ x) = Quotient.mk (dcSetoid Γ K) (x * h) := rfl
    rw [e1, stabCard_out, stabCard_out, stabCard_conj]

end GlobalTheory.UnimodMass
end
end

section

open GlobalTheory.UnitLemma GlobalTheory.StableLatCount Polynomial

noncomputable section

namespace GlobalTheory.StableLatCount

theorem card_commMaps_eq_card_homQuot : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (E : Type) [Field E] [Algebra O E] [IsFractionRing O E] (A₁ A₂ : Type) [CommRing A₁] [CommRing A₂] [Algebra E A₁] [Algebra E A₂] [Algebra O A₁] [Algebra O A₂] [IsScalarTower O E A₁] [IsScalarTower O E A₂] [Module.Finite E A₁] [Module.Finite E A₂] (g₁ : A₁) (g₂ : A₂) (M₁ : Submodule O A₁) (M₂ : Submodule O A₂), IsLat O E M₂ → (∀ y ∈ M₁, g₁ * y ∈ M₁) → (∀ y ∈ M₂, g₂ * y ∈ M₂) → Nat.card {φ : M₂ →ₗ[O] A₁ ⧸ M₁ // ∀ x y : M₂, (y : A₂) = g₂ * x → ∀ a : A₁, φ x = Submodule.Quotient.mk a → φ y = Submodule.Quotient.mk (g₁ * a)} = Nat.card {z : (A₂ →ₗ[E] A₁) ⧸ homLat E M₁ M₂ // ∀ ψ : A₂ →ₗ[E] A₁, Submodule.Quotient.mk ψ = z → adE E g₁ g₂ ψ ∈ homLat E M₁ M₂} := by
  intro O _ _ _ E _ _ _ A₁ A₂ _ _ _ _ _ _ _ _ _ _ g₁ g₂ M₁ M₂ hM₂ hg₁ hg₂
  classical
  let F : (A₂ →ₗ[E] A₁) →ₗ[O] (M₂ →ₗ[O] A₁ ⧸ M₁) :=
    { toFun := fun ψ => M₁.mkQ ∘ₗ (ψ.restrictScalars O) ∘ₗ M₂.subtype
      map_add' := fun ψ χ => by ext x; simp
      map_smul' := fun c ψ => by ext x; simp }
  have hF : ∀ ψ (x : M₂), F ψ x = Submodule.Quotient.mk (ψ (x : A₂)) := fun _ _ => rfl
  have hsurj : Function.Surjective F := by
    intro φ
    haveI : Module.Finite O M₂ := Module.Finite.iff_fg.2 hM₂.1
    haveI : Module.IsTorsionFree O A₂ := Module.IsTorsionFree.of_smul_eq_zero fun r m h => by
      by_cases hr : r = 0
      · exact Or.inl hr
      right
      rw [← algebraMap_smul E r m] at h
      have hr' : algebraMap O E r ≠ 0 := by
        intro h0
        exact hr ((IsFractionRing.injective O E) (by rw [h0, map_zero]))
      exact (smul_eq_zero.1 h).resolve_left hr'
    haveI : Module.Free O M₂ := Module.free_of_finite_type_torsion_free'
    let b := Module.Free.chooseBasis O M₂
    let bs : Module.Free.ChooseBasisIndex O M₂ → A₂ := fun i => (b i : A₂)
    have hli : LinearIndependent O bs := b.linearIndependent.map' M₂.subtype (Submodule.ker_subtype M₂)
    have hliE : LinearIndependent E bs := (LinearIndependent.iff_fractionRing O E).1 hli
    have hspan : ⊤ ≤ Submodule.span E (Set.range bs) := by
      rw [← hM₂.2, Submodule.span_le]
      intro x hx
      have h1 : (⟨x, hx⟩ : M₂) ∈ Submodule.span O (Set.range b) := by
        rw [b.span_eq]; exact Submodule.mem_top
      have h2 := Submodule.mem_map_of_mem (f := M₂.subtype) h1
      rw [Submodule.map_span, ← Set.range_comp] at h2
      exact Submodule.span_le_restrictScalars O E _ h2
    let bE := Module.Basis.mk hliE hspan
    let lift : Module.Free.ChooseBasisIndex O M₂ → A₁ := fun i =>
      Classical.choose (Submodule.Quotient.mk_surjective M₁ (φ (b i)))
    have hlift : ∀ i, Submodule.Quotient.mk (p := M₁) (lift i) = φ (b i) := fun i =>
      Classical.choose_spec (Submodule.Quotient.mk_surjective M₁ (φ (b i)))
    refine ⟨bE.constr E lift, b.ext fun i => ?_⟩
    rw [hF, ← hlift i]
    congr 1
    have : ((b i : M₂) : A₂) = bE i := by simp [bE, bs]
    rw [this, Module.Basis.constr_basis]
  have hker : LinearMap.ker F = homLat E M₁ M₂ := by
    ext ψ
    rw [LinearMap.mem_ker]
    constructor
    · intro h x hx
      have := congrArg (fun f => f ⟨x, hx⟩) h
      simp only [hF, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero] at this
      exact this
    · intro h
      ext x
      rw [hF, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero]
      exact h x x.2
  let e : ((A₂ →ₗ[E] A₁) ⧸ homLat E M₁ M₂) ≃ (M₂ →ₗ[O] A₁ ⧸ M₁) :=
    ((Submodule.quotEquivOfEq _ _ hker.symm).trans (F.quotKerEquivOfSurjective hsurj)).toEquiv
  have he : ∀ ψ, e (Submodule.Quotient.mk ψ) = F ψ := fun ψ => rfl
  refine (Nat.card_congr (e.subtypeEquiv fun z => ?_)).symm
  induction z using Submodule.Quotient.induction_on with
  | H ψ₀ => ?_
  rw [he]
  constructor
  · intro h x y hxy a ha
    have hA : ∀ x ∈ M₂, g₁ * ψ₀ x - ψ₀ (g₂ * x) ∈ M₁ := fun x hx => by
      have := h ψ₀ rfl x hx
      rwa [adE_apply] at this
    rw [hF] at ha ⊢
    rw [Submodule.Quotient.eq] at ha ⊢
    have := M₁.add_mem (M₁.neg_mem (hA x x.2)) (hg₁ _ ha)
    convert this using 1
    rw [hxy]
    ring
  · intro h ψ hψ x hx
    rw [Submodule.Quotient.eq] at hψ
    have hd : ∀ x ∈ M₂, ψ x - ψ₀ x ∈ M₁ := fun x hx => by
      have := hψ x hx
      rwa [LinearMap.sub_apply] at this
    have hc := h ⟨x, hx⟩ ⟨g₂ * x, hg₂ x hx⟩ rfl (ψ₀ x) (hF ψ₀ ⟨x, hx⟩)
    rw [hF, Submodule.Quotient.eq] at hc
    rw [adE_apply]
    have := M₁.sub_mem (M₁.sub_mem (hg₁ _ (hd x hx)) (hd _ (hg₂ x hx))) hc
    convert this using 1
    simp only
    ring

end GlobalTheory.StableLatCount
end
end

section

open Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.linearIndependent_forms_intermediate_field : ∀ (Ks L0 L WL : Type) [Field Ks] [Field L0] [Field L] [Algebra Ks L0] [Algebra L0 L] [Algebra Ks L]
    [IsScalarTower Ks L0 L] [AddCommGroup WL] [Module L WL] [Module Ks WL] [IsScalarTower Ks L WL]
    (WK : Submodule Ks WL) (n : ℕ) (bs : Fin n → WL), (∀ a, bs a ∈ WK) → Submodule.span Ks (Set.range bs) = WK →
    LinearIndependent L bs → ∀ (ι : L0 ⊗[Ks] WK →ₗ[Ks] WL), (∀ (c : L0) (f : WK), ι (c ⊗ₜ[Ks] f) = algebraMap L0 L c • (f : WL)) →
    ∀ (m : ℕ) (x : Fin m → L0 ⊗[Ks] WK), LinearIndependent L0 x → LinearIndependent L (fun a => ι (x a)) := by
  first | exact @GlobalTheory.ksForm_tensor_linearIndependent | exact GlobalTheory.ksForm_tensor_linearIndependent | (intros; apply GlobalTheory.ksForm_tensor_linearIndependent <;> assumption)
end
