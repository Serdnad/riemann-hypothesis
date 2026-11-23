module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
public import Mathlib.RingTheory.Norm.Defs
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace GlobalTheory.UnitLemma.OrthBasis

open GlobalTheory.UnitLemma

variable {K : UQ} (B : InvAlg K)

theorem herm_add_right (x y z₁ z₂ : B.A) : B.herm x y (z₁ + z₂) = B.herm x y z₁ + B.herm x y z₂ := by
  unfold InvAlg.herm
  rw [map_add (f := _), mul_add, map_add (f := _)]

theorem herm_zero_right (x y : B.A) : B.herm x y 0 = 0 := by
  unfold InvAlg.herm
  simp

theorem herm_smul_right' (x y z : B.A) (a : K.E) : B.herm x y (a • z) = K.c a * B.herm x y z := by
  unfold InvAlg.herm
  rw [Algebra.smul_def, map_mul B.σ, B.σ_alg, ← Algebra.smul_def, mul_smul_comm, map_smul, smul_eq_mul]

theorem herm_sum_smul_left {n : ℕ} (x z : B.A) (a : Fin n → K.E) (v : Fin n → B.A) :
    B.herm x (∑ j, a j • v j) z = ∑ j, a j * B.herm x (v j) z := by
  unfold InvAlg.herm

  rw [Finset.mul_sum, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, map_smul, smul_eq_mul]

theorem herm_mul_left_of_fixed (x g y z : B.A) (hg : B.σ g = g) :
    B.herm x (g * y) z = B.herm x y (g * z) := by
  unfold InvAlg.herm
  rw [map_mul B.σ, hg]; congr 1; ring

theorem repr_mul {n : ℕ} (e : Module.Basis (Fin n) K.E B.A) (g z : B.A) (i : Fin n) :
    e.repr (g * z) i = ∑ j, e.repr z j * e.repr (g * e j) i := by
  conv_lhs => rw [← e.sum_repr z]

  rw [Finset.mul_sum, map_sum, Finset.sum_apply']
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_smul_comm, map_smul, Finsupp.smul_apply, smul_eq_mul]

end GlobalTheory.UnitLemma.OrthBasis

namespace GlobalTheory.UnitLemma

open GlobalTheory.UnitLemma.OrthBasis

theorem herm_basis_orthonormal : ∀ (K : UQ) (B : InvAlg K) (x w : B.A), B.σ B.g = B.g → IsUnit w →
    Submodule.span K.E (Set.range fun l : ℕ => B.g ^ l) = ⊤ → ∀ (n : ℕ) (e : Module.Basis (Fin n) K.E B.A),
    (∀ i j, K.c (e.repr (B.g * e j) i) = e.repr (B.g * e i) j) → (∀ j, B.herm x (e j) w = K.c (e.repr w j)) →
    ∀ i j, B.herm x (e i) (e j) = if i = j then 1 else 0 := by
  intro K B x w hg hw hspan n e hM hwj

  let P : B.A → Prop := fun z => ∀ i, B.herm x (e i) z = K.c (e.repr z i)
  have hstep : ∀ z, P z → P (B.g * z) := by
    intro z hz i
    rw [← herm_mul_left_of_fixed B x B.g (e i) z hg]
    conv_lhs => rw [← e.sum_repr (B.g * e i)]

    rw [herm_sum_smul_left, repr_mul, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hz j, RingEquiv.map_mul K.c, hM, mul_comm]
  have hpow : ∀ l : ℕ, P (B.g ^ l * w) := by
    intro l
    induction l with
    | zero => simpa [P] using hwj
    | succ l ih => rw [pow_succ', mul_assoc]; exact hstep _ ih
  have hspanP : ∀ a ∈ Submodule.span K.E (Set.range fun l : ℕ => B.g ^ l), P (a * w) := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem y hy => obtain ⟨l, rfl⟩ := hy; exact hpow l
    | zero => intro i; simp [herm_zero_right]
    | add y z _ _ hy hz =>
      intro i; rw [add_mul, herm_add_right, hy i, hz i, map_add (f := _), Finsupp.add_apply, map_add (f := _)]
    | smul a y _ hy =>
      intro i; rw [smul_mul_assoc, herm_smul_right', hy i, LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul,
        RingEquiv.map_mul K.c]
  have hall : ∀ z, P z := by
    intro z
    obtain ⟨u, rfl⟩ := hw
    have := hspanP (z * ((u⁻¹ : B.Aˣ) : B.A)) (by rw [hspan]; exact Submodule.mem_top)
    rwa [mul_assoc, Units.inv_mul, mul_one] at this
  intro i j
  rw [hall (e j) i, e.repr_self, Finsupp.single_apply]
  split_ifs with h1 h2 h2
  · exact map_one _
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · exact map_zero _

end GlobalTheory.UnitLemma
end
end

section

open GlobalTheory.UnitLemma Polynomial

noncomputable section

namespace GlobalTheory.UnitLemma.TorusAction

open InvAlg

variable {K : UQ} (B : InvAlg K)

theorem mem_mulLat_unit (u : B.Aˣ) (L : Submodule K.O B.A) (y : B.A) :
    y ∈ mulLat K.O (u : B.A) L ↔ ((u⁻¹ : B.Aˣ) : B.A) * y ∈ L := by
  unfold mulLat
  simp only [Submodule.mem_map, LinearMap.mulLeft_apply]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rwa [← mul_assoc, Units.inv_mul, one_mul]
  · intro h
    exact ⟨_, h, by rw [← mul_assoc, Units.mul_inv, one_mul]⟩

theorem sigma_eq_inv (t : B.Aˣ) (ht : t ∈ B.T) : B.σ (t : B.A) = ((t⁻¹ : B.Aˣ) : B.A) := by
  have h : (t : B.A) * B.σ (t : B.A) = 1 := ht
  calc B.σ (t : B.A) = ((t⁻¹ : B.Aˣ) : B.A) * ((t : B.A) * B.σ (t : B.A)) := by
        rw [← mul_assoc, Units.inv_mul, one_mul]
    _ = _ := by rw [h, mul_one]

theorem isLat_mulLat (u : B.Aˣ) (L : Submodule K.O B.A) (hL : IsLat K.O K.E L) :
    IsLat K.O K.E (mulLat K.O (u : B.A) L) := by
  refine ⟨hL.1.map _, ?_⟩
  have hc : ((mulLat K.O (u : B.A) L : Submodule K.O B.A) : Set B.A) =
      (LinearMap.mulLeft K.E (u : B.A)) '' (L : Set B.A) := by
    unfold mulLat; rw [Submodule.map_coe]; rfl
  rw [hc, Submodule.span_image, hL.2, Submodule.map_top, LinearMap.range_eq_top]
  intro y
  exact ⟨((u⁻¹ : B.Aˣ) : B.A) * y, by simp [← mul_assoc]⟩

theorem torus_mem_X (K : UQ) (B : InvAlg K) (x : B.A) :
    ∀ t ∈ B.T, ∀ L ∈ B.X x, mulLat K.O (t : B.A) L ∈ B.X x := by
  intro t ht L hL
  obtain ⟨hlat, hg, hdual⟩ := hL
  have hs := sigma_eq_inv B t ht
  refine ⟨isLat_mulLat B t L hlat, ?_, ?_⟩
  · intro y hy
    rw [mem_mulLat_unit] at hy ⊢
    have := hg _ hy
    rwa [mul_left_comm] at this
  · intro y
    rw [mem_mulLat_unit, hdual]
    constructor
    · intro h z hz
      rw [mem_mulLat_unit] at hz
      have := h _ hz
      have e : B.herm x (((t⁻¹ : B.Aˣ) : B.A) * y) (((t⁻¹ : B.Aˣ) : B.A) * z) = B.herm x y z := by
        have hs' : B.σ ((t⁻¹ : B.Aˣ) : B.A) = (t : B.A) := by rw [← hs, B.σ_σ]
        unfold InvAlg.herm; rw [map_mul B.σ, hs']
        congr 1
        linear_combination (x * y * B.σ z) * Units.inv_mul t
      rwa [e] at this
    · intro h w hw
      have hz : (t : B.A) * w ∈ mulLat K.O (t : B.A) L := by
        rw [mem_mulLat_unit, ← mul_assoc, Units.inv_mul, one_mul]; exact hw
      have := h _ hz
      have e : B.herm x (((t⁻¹ : B.Aˣ) : B.A) * y) w = B.herm x y ((t : B.A) * w) := by
        unfold InvAlg.herm; rw [map_mul B.σ, hs]; congr 1; ring
      rwa [e]

end GlobalTheory.UnitLemma.TorusAction
end
end

section

open GlobalTheory.UnitLemma Polynomial
open scoped Pointwise

namespace GlobalTheory.UnitLemma.StabIndex

variable {O : Type} [CommRing O] {A : Type} [CommRing A] [Algebra O A]

theorem smul_eq_mulLat (t : Aˣ) (L : Submodule O A) : t • L = mulLat O (t : A) L := by
  ext y
  simp [mulLat, Submodule.mem_smul_pointwise_iff_exists, Units.smul_def]

theorem mem_stabLat_iff (t : Aˣ) (L : Submodule O A) : t ∈ stabLat O L ↔ t • L = L := by
  have key : ∀ y, y ∈ t • L ↔ ((t⁻¹ : Aˣ) : A) * y ∈ L := by
    intro y
    rw [smul_eq_mulLat]
    simp only [mulLat, Submodule.mem_map, LinearMap.mulLeft_apply]
    constructor
    · rintro ⟨b, hb, rfl⟩
      rw [← mul_assoc, Units.inv_mul, one_mul]; exact hb
    · intro h
      exact ⟨_, h, by rw [← mul_assoc, Units.mul_inv, one_mul]⟩
  constructor
  · intro ht
    ext y
    rw [key, ht (((t⁻¹ : Aˣ) : A) * y), ← mul_assoc, Units.mul_inv, one_mul]
  · intro ht y
    have := key ((t : A) * y)
    rw [ht, ← mul_assoc, Units.inv_mul, one_mul] at this
    exact this.symm

end GlobalTheory.UnitLemma.StabIndex

namespace GlobalTheory.UnitLemma.StabIndex

theorem isUnit_algebraMap (K : UQ) (B : InvAlg K) (c : K.O) (hc : c ≠ 0) :
    IsUnit (algebraMap K.O B.A c) := by
  rw [IsScalarTower.algebraMap_apply K.O K.E B.A]
  refine (isUnit_iff_ne_zero.mpr ?_).map (algebraMap K.E B.A)
  exact (map_ne_zero_iff _ (IsFractionRing.injective K.O K.E)).mpr hc

theorem relIndex_ne_zero_of_between (K : UQ) (B : InvAlg K) (L : Submodule K.O B.A) (c : K.O) (hc : c ≠ 0)
    (hfin : {M : Submodule K.O B.A | mulLat K.O (algebraMap K.O B.A (c * c)) L ≤ M ∧ M ≤ L}.Finite)
    (h : ∀ u : B.A, IsIntegral K.O u → ∀ y ∈ L, algebraMap K.O B.A c * u * y ∈ L) :
    (stabLat K.O L ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) ≠ 0 := by
  set G := intUnits K.O B.A ⊓ B.T
  set γ : B.Aˣ := (isUnit_algebraMap K B c hc).unit
  have hγ : (γ : B.A) = algebraMap K.O B.A c := rfl
  have hsub : (stabLat K.O L ⊓ B.T).subgroupOf G = MulAction.stabilizer G L := by
    ext u
    rw [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff, Subgroup.mem_inf, Subgroup.smul_def,
      ← mem_stabLat_iff]
    exact ⟨fun hu => hu.1, fun hu => ⟨hu, (Subgroup.mem_inf.mp u.2).2⟩⟩
  have horb : (MulAction.orbit G L).Finite := by
    refine (hfin.preimage (MulAction.injective γ).injOn).subset ?_
    rintro _ ⟨u, rfl⟩
    have hu := (Subgroup.mem_inf.mp u.2).1
    have hM : γ • ((u : B.Aˣ) • L) = mulLat K.O (algebraMap K.O B.A c * ((u : B.Aˣ) : B.A)) L := by
      rw [smul_smul, smul_eq_mulLat, Units.val_mul, hγ]
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Subgroup.smul_def, hM]
    constructor
    · rintro _ ⟨y, hy, rfl⟩
      refine ⟨algebraMap K.O B.A c * (((u : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * y, h _ hu.2 y hy, ?_⟩
      simp only [LinearMap.mulLeft_apply, map_mul]
      calc algebraMap K.O B.A c * ((u : B.Aˣ) : B.A) * (algebraMap K.O B.A c * (((u : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * y)
          = algebraMap K.O B.A c * algebraMap K.O B.A c * (((u : B.Aˣ) : B.A) * (((u : B.Aˣ)⁻¹ : B.Aˣ) : B.A)) * y := by ring
        _ = _ := by rw [Units.mul_inv, mul_one]
    · rintro _ ⟨y, hy, rfl⟩
      simp only [LinearMap.mulLeft_apply]
      exact h _ hu.1 y hy
  rw [Subgroup.relIndex, hsub]
  haveI : Finite (MulAction.orbit G L) := horb.to_subtype
  haveI : Finite (G ⧸ MulAction.stabilizer G L) := Finite.of_equiv _ (MulAction.orbitEquivQuotientStabilizer G L)
  exact Subgroup.index_ne_zero_of_finite

end GlobalTheory.UnitLemma.StabIndex
end

section

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma.SwapInt

theorem isIntegral_map_semilinear {O S S' : Type} [CommRing O] [CommRing S] [CommRing S'] [Algebra O S]
    [Algebra O S'] (κ : O →+* O) (ψ : S →+* S')
    (hψ : ∀ o, ψ (algebraMap O S o) = algebraMap O S' (κ o)) {y : S} (h : IsIntegral O y) :
    IsIntegral O (ψ y) := by
  obtain ⟨p, hm, hp⟩ := h
  refine ⟨p.map κ, hm.map κ, ?_⟩
  rw [eval₂_map]
  have e : (algebraMap O S').comp κ = ψ.comp (algebraMap O S) := by
    ext o; simp [hψ]
  rw [e, ← hom_eval₂, hp, map_zero]

noncomputable def conjO (K : UQ) : K.O →+* K.O where
  toFun o := Classical.choose (K.c_int o)
  map_one' := by
    apply IsFractionRing.injective K.O K.E
    rw [← Classical.choose_spec (K.c_int 1)]; simp
  map_mul' a b := by
    apply IsFractionRing.injective K.O K.E
    rw [← Classical.choose_spec (K.c_int (a * b)), map_mul, map_mul, map_mul,
      ← Classical.choose_spec (K.c_int a), ← Classical.choose_spec (K.c_int b)]
  map_zero' := by
    apply IsFractionRing.injective K.O K.E
    rw [← Classical.choose_spec (K.c_int 0)]; simp
  map_add' a b := by
    apply IsFractionRing.injective K.O K.E
    rw [← Classical.choose_spec (K.c_int (a + b)), map_add (f := _), map_add (f := _), map_add (f := _),
      ← Classical.choose_spec (K.c_int a), ← Classical.choose_spec (K.c_int b)]

theorem conjO_spec (K : UQ) (o : K.O) :
    algebraMap K.O K.E (conjO K o) = K.c (algebraMap K.O K.E o) :=
  (Classical.choose_spec (K.c_int o)).symm

theorem sigma_algebraMap {K : UQ} (B : InvAlg K) (o : K.O) :
    B.σ (algebraMap K.O B.A o) = algebraMap K.O B.A (conjO K o) := by
  rw [IsScalarTower.algebraMap_apply K.O K.E B.A, B.σ_alg, ← conjO_spec,
    ← IsScalarTower.algebraMap_apply K.O K.E B.A]

end GlobalTheory.UnitLemma.SwapInt


open GlobalTheory.UnitLemma.SwapInt in
theorem GlobalTheory.UnitLemma.InvAlg.isIntegral_mk_comap_sigma_iff :
    ∀ (K : UQ) (B : InvAlg K) (m : MaximalSpectrum B.A) (x : B.A),
      IsIntegral K.O (Ideal.Quotient.mk (m.asIdeal.comap B.σ) x) ↔
        IsIntegral K.O (Ideal.Quotient.mk m.asIdeal (B.σ x)) := by
  intro K B m x
  let σr : B.A →+* B.A := B.σ
  let ψ := Ideal.quotientMap m.asIdeal σr (le_refl (m.asIdeal.comap σr))
  have hm : m.asIdeal ≤ (m.asIdeal.comap σr).comap σr := by
    intro y hy
    simp only [Ideal.mem_comap]
    show B.σ (B.σ y) ∈ m.asIdeal
    rw [B.σ_σ]; exact hy
  let φ := Ideal.quotientMap (m.asIdeal.comap σr) σr hm
  have key : ∀ o : K.O, σr (algebraMap K.O B.A o) = algebraMap K.O B.A (conjO K o) :=
    sigma_algebraMap B
  constructor
  · intro h
    have h' : IsIntegral K.O (Ideal.Quotient.mk (m.asIdeal.comap σr) x) := h
    have := isIntegral_map_semilinear (conjO K) ψ (fun o => by
      rw [← Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.mk_algebraMap]
      simp only [ψ]
      rw [Ideal.quotientMap_mk, key]) h'
    have e2 : ψ (Ideal.Quotient.mk (m.asIdeal.comap σr) x) = Ideal.Quotient.mk m.asIdeal (σr x) :=
      Ideal.quotientMap_mk
    rw [e2] at this
    exact this
  · intro h
    have h' : IsIntegral K.O (Ideal.Quotient.mk m.asIdeal (σr x)) := h
    have := isIntegral_map_semilinear (conjO K) φ (fun o => by
      rw [← Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.mk_algebraMap]
      simp only [φ]
      rw [Ideal.quotientMap_mk, key]) h'
    have e2 : φ (Ideal.Quotient.mk m.asIdeal (σr x)) = Ideal.Quotient.mk (m.asIdeal.comap σr) (σr (σr x)) :=
      Ideal.quotientMap_mk
    have e : σr (σr x) = x := B.σ_σ x
    rw [e2, e] at this
    exact this
end

section

namespace GlobalTheory.DenominatorOfSpan

open GlobalTheory.UnitLemma

theorem exists_smul_mem_of_span_eq_top {O E A : Type} [CommRing O] [IsDomain O] [Field E] [Algebra O E]
    [IsFractionRing O E] [AddCommGroup A] [Module E A] [Module O A] [IsScalarTower O E A]
    (L : Submodule O A) (hL : Submodule.span E (L : Set A) = ⊤) (x : A) :
    ∃ d : O, d ≠ 0 ∧ d • x ∈ L := by
  have hx : x ∈ Submodule.span E (L : Set A) := by rw [hL]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hy⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact L.zero_mem⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact L.smul_mem b hay
    · rw [mul_smul]; exact L.smul_mem a hbz
  | smul e y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨⟨n, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors O) e
    have hs' : e * algebraMap O E (s : O) = algebraMap O E n := hs
    refine ⟨a * (s : O), mul_ne_zero ha (nonZeroDivisors.ne_zero s.2), ?_⟩
    have h1 : (s : O) • e • y = n • y := by
      rw [← algebraMap_smul E (s : O), ← mul_smul, mul_comm, hs', algebraMap_smul]
    rw [mul_smul, h1, smul_comm]
    exact L.smul_mem n hay

theorem exists_denominator {K : UQ} (B : InvAlg K) (L : Submodule K.O B.A)
    (hL : Submodule.span K.E (L : Set B.A) = ⊤) (x : B.A) :
    ∃ d : K.O, d ≠ 0 ∧ d • x ∈ L :=
  exists_smul_mem_of_span_eq_top L hL x

end GlobalTheory.DenominatorOfSpan
end

section

noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial

def IsUnrExt (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E) : Prop :=
  K'.q = K.q ^ d ∧ (∀ x, φ (K.c x) = K'.c (φ x)) ∧ (∀ x, val K'.O (φ x) = val K.O x) ∧ (K.Odd → K'.Odd) ∧
    @Module.finrank K.E K'.E _ _ (φ.toAlgebra).toModule = d

variable {K K' : UQ}

def overExt (φ : K.E →+* K'.E) (B : InvAlg K) (ψ : K'.E →+* B.A)
    (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)) : InvAlg K' :=
  letI : Algebra K'.E B.A := ψ.toAlgebra
  letI : Algebra K'.O B.A := (ψ.comp (algebraMap K'.O K'.E)).toAlgebra
  haveI : IsScalarTower K'.O K'.E B.A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Finite K'.E B.A := by
    obtain ⟨S, hS⟩ := B.fd.fg_top
    refine ⟨⟨S, eq_top_iff.2 fun y hy0 => ?_⟩⟩
    clear hy0
    have hy : y ∈ Submodule.span K.E (S : Set B.A) := hS ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span hx
    | zero => exact zero_mem _
    | add x z _ _ hx hz => exact add_mem hx hz
    | smul e x _ hx =>
      have h : e • x = (φ e) • x := by
        rw [Algebra.smul_def, Algebra.smul_def, ← hψ e]; rfl
      rw [h]; exact Submodule.smul_mem _ _ hx
  { A := B.A
    σ := B.σ
    σ_σ := B.σ_σ
    σ_alg := hσ
    g := B.g }

end GlobalTheory.UnitLemma.Unr
end
end

section

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma.InvAlg

theorem gramDet_eq_norm_mul (K : UQ) (B : InvAlg K) (x : B.A) :
    B.gramDet x = Algebra.norm K.E x * B.gramDet 1 := by
  classical
  set b := Module.finBasis K.E B.A
  have hM : (Matrix.of fun i j => B.herm x (b i) (b j)) =
      (Algebra.leftMulMatrix b x).transpose * (Matrix.of fun i j => B.herm 1 (b i) (b j)) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, herm, one_mul,
      Algebra.leftMulMatrix_apply]
    have h := b.sum_repr (x * b i)
    conv_lhs => rw [← h]

    rw [Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_mul_assoc, map_smul, smul_eq_mul, LinearMap.toMatrix_apply]
    simp
  unfold gramDet
  rw [hM, Matrix.det_mul, Matrix.det_transpose, Algebra.norm_eq_matrix_det b]

end GlobalTheory.UnitLemma.InvAlg
end
