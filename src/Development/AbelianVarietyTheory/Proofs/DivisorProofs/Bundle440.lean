module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle390
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
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
public import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LowDat.Uniq

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem ev_zsmul {D : Datum H} {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q}
    {e : ℕ → Q → Q → kˣ → Prop} (J : TateIso D k Q act e) (n : ℕ) (m : ℤ) (x : D.La) :
    J.ev n (m • x) = J.ev n x ^ m := by
  let f : Multiplicative D.La →* Q :=
    MonoidHom.mk' (fun y => J.ev n (Multiplicative.toAdd y)) (fun a b => J.add n _ _)
  have h := map_zpow f (Multiplicative.ofAdd x) m
  rw [← ofAdd_zsmul] at h
  exact h

theorem mul_mem_M (l : Level H) {x y : 𝓞 E} (hx : x ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) (hy : y ∈ l.Mb) :
    ∃ r : 𝓞 E, x * y = r * (l.M : 𝓞 E) := by
  have h : y * x ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := Ideal.mul_mem_mul hy hx
  rw [l.prod, Ideal.mem_span_singleton'] at h
  obtain ⟨r, hr⟩ := h
  exact ⟨r, by rw [mul_comm, ← hr]⟩

theorem smul_mem_M {D : Datum H} (l : Level H) {x : 𝓞 E} (hx : x ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E))
    {b : D.La} (hb : b ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)) : ∃ c : D.La, x • b = l.M • c := by
  refine Submodule.smul_induction_on (p := fun b => ∃ c : D.La, x • b = l.M • c) hb ?_ ?_
  · intro y hy t _
    obtain ⟨r, hr⟩ := mul_mem_M l hx hy
    refine ⟨r • t, ?_⟩
    rw [← mul_smul, hr, mul_comm, mul_smul, Nat.cast_smul_eq_nsmul]
  · rintro b1 b2 ⟨c1, hc1⟩ ⟨c2, hc2⟩
    exact ⟨c1 + c2, by rw [smul_add, hc1, hc2, smul_add]⟩

theorem dvd_EF (D : Datum H) (l : Level H) {a c : D.La} (ha : a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La))
    (hc : c ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)) : (l.M : ℤ) ∣ D.EF a c := by
  refine Submodule.smul_induction_on (p := fun a => (l.M : ℤ) ∣ D.EF a c) ha ?_ ?_
  · intro y hy t _
    show (l.M : ℤ) ∣ D.EF (y • t) c
    rw [D.adj]
    have hy' : H.bar y ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hy
    obtain ⟨c', hc'⟩ := smul_mem_M l hy' hc
    rw [hc', map_nsmul, nsmul_eq_mul]
    exact dvd_mul_right _ _
  · intro x y hx hy
    show (l.M : ℤ) ∣ D.EF (x + y) c
    rw [map_add (f := _), LinearMap.add_apply]
    exact dvd_add hx hy

end GlobalTheory.LowDat.Uniq

namespace GlobalTheory.LowDat


open GlobalTheory.LowDat.Uniq in
theorem tateIso_ev_lcm_eq : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (l : Level H)
    (k : Type) [Field k] (Q : Type) [Group Q] (act : 𝓞 E → Q → Q) (e : ℕ → Q → Q → kˣ → Prop),
    (∀ n, 0 < n → ∀ x y c c', e n x y c → e n x y c' → c = c') → ∀ J J' : TateIso D k Q act e, J.ζ l.M' = J'.ζ l.M' →
    (∀ a, J.ev l.A a = J'.ev l.A a) →
    (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), J.ev l.M a = J'.ev l.M a) →
    ∀ a, J.ev l.M' a = J'.ev l.M' a := by
  intro E _ _ _ H D l k _ Q _ act e huniq J J' hζ hA hM
  have hM0 : 0 < l.M := by have := l.three_le; omega
  have hA0 := l.A_pos

  obtain ⟨j, hj⟩ := Nat.gcd_dvd_left l.M l.A
  obtain ⟨kk, hkk⟩ := Nat.gcd_dvd_right l.M l.A
  have hgl : Nat.gcd l.M l.A * l.M' = l.M * l.A := Nat.gcd_mul_lcm _ _
  have hg0 : 0 < Nat.gcd l.M l.A := Nat.gcd_pos_of_pos_left _ hM0
  have hcop0 := Nat.coprime_div_gcd_div_gcd (m := l.M) (n := l.A) hg0
  generalize Nat.gcd l.M l.A = G at hj hkk hgl hg0 hcop0
  have hMk : l.M' = l.M * kk := Nat.eq_of_mul_eq_mul_left hg0 (by rw [hgl, hkk]; ring)
  have hAj : l.M' = l.A * j := Nat.eq_of_mul_eq_mul_left hg0 (by rw [hgl, hj]; ring)
  have hj0 : 0 < j := by
    rcases Nat.eq_zero_or_pos j with h | h
    · rw [h, mul_zero] at hj; omega
    · exact h
  have hk0 : 0 < kk := by
    rcases Nat.eq_zero_or_pos kk with h | h
    · rw [h, mul_zero] at hkk; omega
    · exact h
  have hcop : Nat.Coprime j kk := by
    have e1 : l.M / G = j := by rw [hj]; exact Nat.mul_div_cancel_left j hg0
    have e2 : l.A / G = kk := by rw [hkk]; exact Nat.mul_div_cancel_left kk hg0
    rw [e1, e2] at hcop0; exact hcop0
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop

  have hζM : J.ζ l.M = J'.ζ l.M := by
    rw [← J.ζ_pow l.M kk hM0 hk0, ← J'.ζ_pow l.M kk hM0 hk0, ← hMk, hζ]

  have h1 : (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by rw [l.coprime]; trivial
  obtain ⟨f, hf, g2, hg2, hfg⟩ := Submodule.mem_sup.mp h1
  have decomp : ∀ x : D.La, x = f • x + g2 • x := fun x => by rw [← add_smul, hfg, one_smul]

  have key : ∀ b ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La), J.ev l.M b = J'.ev l.M b := by
    intro b hb
    have hord : (J'.ev l.M b) ^ l.M = 1 := (J'.onto l.M hM0 _).mpr ⟨b, rfl⟩
    obtain ⟨b', hb'⟩ := (J.onto l.M hM0 _).mp hord
    have h2 : J.ev l.M (g2 • b') = 1 := by
      rw [J.lin, hb', ← J'.lin]
      obtain ⟨c, hc⟩ := smul_mem_M (D := D) l hg2 hb
      rw [hc]; exact (J'.ker l.M hM0 _).mpr ⟨c, rfl⟩
    have hb'' : J.ev l.M (f • b') = J'.ev l.M b := by
      have h := J.add l.M (f • b') (g2 • b')
      rw [← decomp b', h2, _root_.mul_one] at h
      rw [← hb', h]
    have hf' : f • b' ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := Submodule.smul_mem_smul hf Submodule.mem_top
    set c := b - f • b' with hcdef
    have hcm : c ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := Submodule.sub_mem _ hb hf'
    have hdiv : ∀ a, (l.M : ℤ) ∣ D.EF a c := by
      intro a
      rw [decomp a, map_add (f := _), LinearMap.add_apply]
      refine dvd_add (dvd_EF D l (Submodule.smul_mem_smul hf Submodule.mem_top) hcm) ?_
      have hga : g2 • a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La) :=
        Submodule.smul_mem_smul hg2 Submodule.mem_top
      have i1 := J.isom l.M hM0 (g2 • a) (f • b')
      have i2 := J'.isom l.M hM0 (g2 • a) b
      rw [hM _ hga, hb'', hζM] at i1
      have heq := huniq l.M hM0 _ _ _ _ i1 i2
      rw [← (J'.ζ_prim l.M hM0).zpow_eq_one_iff_dvd, hcdef, map_sub, zpow_sub, heq, mul_inv_cancel]
    have hdiv' : ∀ a, (l.M : ℤ) ∣ D.EF c a := fun a => by
      have h := D.alt (a + c)
      simp only [map_add (f := _), LinearMap.add_apply, D.alt a, D.alt c, zero_add, add_zero] at h
      have h' : D.EF c a = - D.EF a c := by linarith
      rw [h']; exact (hdiv a).neg_right
    choose q hq using hdiv'
    have hMne : (l.M : ℤ) ≠ 0 := by exact_mod_cast hM0.ne'
    let φ : D.La →ₗ[ℤ] ℤ :=
      { toFun := q
        map_add' := fun x y => by
          apply mul_left_cancel₀ hMne
          rw [← hq, mul_add, ← hq, ← hq, map_add (f := _)]
        map_smul' := fun m x => by
          apply mul_left_cancel₀ hMne
          rw [← hq, RingHom.id_apply, smul_eq_mul, mul_left_comm, ← hq, map_zsmul, smul_eq_mul] }
    obtain ⟨c0, hc0⟩ := D.unimod.2 φ
    have hc : c = l.M • c0 := by
      apply D.unimod.1
      ext a
      rw [map_nsmul, LinearMap.smul_apply, hc0, nsmul_eq_mul]
      exact hq a
    have hJc : J.ev l.M c = 1 := (J.ker l.M hM0 _).mpr ⟨c0, hc⟩
    have hbc : b = f • b' + c := by rw [hcdef]; abel
    rw [hbc, J.add, hJc, _root_.mul_one, hb'', ← hbc]
  have hall : ∀ a, J.ev l.M a = J'.ev l.M a := by
    intro a
    rw [decomp a, J.add, J'.add, key _ (Submodule.smul_mem_smul hf Submodule.mem_top),
      hM _ (Submodule.smul_mem_smul hg2 Submodule.mem_top)]

  have expand : ∀ (K : TateIso D k Q act e) (a : D.La),
      K.ev l.M' a = K.ev l.A (u • a) * K.ev l.M (v • a) := by
    intro K a
    have ha : a = (j : ℤ) • (u • a) + (kk : ℤ) • (v • a) := by
      rw [smul_smul, smul_smul, ← add_smul, mul_comm (j : ℤ), mul_comm (kk : ℤ), huv, one_smul]
    conv_lhs => rw [ha]
    rw [K.add, ev_zsmul K l.M' (j : ℤ) (u • a), ev_zsmul K l.M' (kk : ℤ) (v • a), zpow_natCast, zpow_natCast]
    congr 1
    · have h := K.tower l.A j hA0 hj0 (u • a); rw [← hAj] at h; exact h
    · have h := K.tower l.M kk hM0 hk0 (v • a); rw [← hMk] at h; exact h
  intro a
  rw [expand J, expand J', hA, hall]

end GlobalTheory.LowDat
end
end

section

noncomputable section

namespace GlobalTheory.UPel.GeometricLevelExistence

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem epi_spMap_field {K L : Type} [Field K] [Field L] (σ : K →+* L) : Epi (spMap σ) := by
  have : Flat (Spec.map (CommRingCat.ofHom σ)) := inferInstance
  have : Surjective (Spec.map (CommRingCat.ofHom σ)) :=
    ⟨fun u => ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem unitOn_pull_spMap {K Ω : Type} [CommRing K] [CommRing Ω] (i : K →+* Ω) (c : Kˣ) :
    Units.map (spMap i).appTop.hom.toMonoidHom (unitOn c) = unitOn (Units.map i.toMonoidHom c) := by
  apply Units.ext
  exact (congrArg (fun q => q.hom c.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom i))).symm

theorem eq_iff_of_add {La G : Type} [AddGroup La] [Group G] (P : La → G)
    (hP : ∀ a b, P (a + b) = P a * P b) (a b : La) : P a = P b ↔ P (-a + b) = 1 := by
  have h := hP a (-a + b)
  rw [add_neg_cancel_left] at h
  rw [h]
  constructor
  · intro e
    exact mul_left_cancel (e.symm.trans (_root_.mul_one _).symm)
  · intro e
    rw [e, _root_.mul_one]

theorem exists_eq_of_count {La G : Type} [AddCommGroup La] [Module.Finite ℤ La] [Group G] (n : ℕ) (hn : 0 < n)
    (P Q : La → G) (hPa : ∀ a b, P (a + b) = P a * P b) (hQa : ∀ a b, Q (a + b) = Q a * Q b)
    (hP : ∀ a, P a = 1 ↔ ∃ b, a = n • b) (hQ : ∀ a, Q a = 1 ↔ ∃ b, a = n • b)
    (hPQ : ∀ a, ∃ c, P a = Q c) (c : La) : ∃ a, P a = Q c := by
  let m : La →+ La := AddMonoidHom.mk' (fun a : La => n • a) (fun a b => smul_add n a b)
  let K : AddSubgroup La := m.range
  have hK : ∀ a, a ∈ K ↔ ∃ b, a = n • b := fun a => by
    simp only [K, AddMonoidHom.mem_range]
    exact ⟨fun ⟨b, hb⟩ => ⟨b, hb.symm⟩, fun ⟨b, hb⟩ => ⟨b, hb.symm⟩⟩
  have : AddGroup.FG La := Module.Finite.iff_addGroup_fg.1 inferInstance
  have : Finite (La ⧸ K) := AddCommGroup.finite_of_fg_torsion _ fun q => by
    induction q using QuotientAddGroup.induction_on with
    | H a =>
      refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, hn, ?_⟩
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, hK]
      exact ⟨a, rfl⟩
  have hmk : ∀ (R : La → G), (∀ a b, R (a + b) = R a * R b) → (∀ a, R a = 1 ↔ ∃ b, a = n • b) →
      ∀ a b, R a = R b ↔ (a : La ⧸ K) = b := fun R hRa hR a b => by
    rw [eq_iff_of_add R hRa, QuotientAddGroup.eq, hK, hR]
  choose f hf using hPQ
  let g : La ⧸ K → La ⧸ K := fun q => (f q.out : La ⧸ K)
  have hg : Function.Injective g := fun q q' e => by
    have e' := (hmk Q hQa hQ _ _).2 e
    rw [← hf, ← hf, hmk P hPa hP] at e'
    simpa using e'
  obtain ⟨q, hq⟩ := (Finite.injective_iff_surjective.1 hg) (c : La ⧸ K)
  refine ⟨q.out, ?_⟩
  rw [hf, hmk Q hQa hQ]
  exact hq

end GlobalTheory.UPel.GeometricLevelExistence

namespace GlobalTheory.UPel.GeometricLevelExistence

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

end GlobalTheory.UPel.GeometricLevelExistence
end
end

section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

theorem _root_.GlobalTheory.T.exists_section_nonvanishing_where_single_coefficient : ∀ (X : Scheme.{0}) (L : LB X) (κ : Type) [Fintype κ] (r : κ → Γ(X, ⊤)) (σ : κ → LB.Sec L), ∃ s : LB.Sec L, ∀ (z : X) (i : κ), z ∈ X.basicOpen (r i) → z ∈ nonzeroLocus (σ i) → (∀ j, j ≠ i → z ∉ X.basicOpen (r j)) → z ∈ nonzeroLocus s := by
  first | exact @GlobalTheory.exists_sec_sum_nonzero | exact GlobalTheory.exists_sec_sum_nonzero | (intros; apply GlobalTheory.exists_sec_sum_nonzero <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MumProd

def tensLB {X : Scheme.{0}} (L M : LB X) : LB X :=
  LB.mk (L.ι × M.ι) (fun p => L.U p.1 ⊓ M.U p.2) fun p q =>
    res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
      L.U p.1 ⊓ M.U p.2 ⊓ (L.U q.1 ⊓ M.U q.2) ≤ L.U p.1 ⊓ L.U q.1) (L.g p.1 q.1) *
    res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
      L.U p.1 ⊓ M.U p.2 ⊓ (L.U q.1 ⊓ M.U q.2) ≤ M.U p.2 ⊓ M.U q.2) (M.g p.2 q.2)

abbrev extLB {X X₁ X₂ : Scheme.{0}} (L₁ : LB X₁) (L₂ : LB X₂) (f₁ : X ⟶ X₁) (f₂ : X ⟶ X₂) : LB X :=
  tensLB (L₁.pull f₁) (L₂.pull f₂)

section MapsAt

variable {Y X X₁ X₂ : Scheme.{0}} {L : LB X} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : X ⟶ X₁} {f₂ : X ⟶ X₂}

def extIdx (j₁ : L₁.ι) (j₂ : L₂.ι) : (extLB L₁ L₂ f₁ f₂).ι :=
  ((fun _ => j₁, fun _ => j₂) : (PUnit → L₁.ι) × (PUnit → L₂.ι))

lemma mapsAt₂_le_a (w : LB.Iso L (extLB L₁ L₂ f₁ f₂)) (p : Y ⟶ X) (j₁ : L₁.ι) (j₂ : L₂.ι) (jL : L.ι) :
    p ⁻¹ᵁ (LB.div (extLB L₁ L₂ f₁ f₂) L).U (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂, jL) ≤
      LB.wchart L (fun _ : PUnit => p) (fun _ => jL) :=
  fun _ hy => Set.mem_iInter.2 fun _ => hy.2

lemma mapsAt₂_le_1 (w : LB.Iso L (extLB L₁ L₂ f₁ f₂)) (p : Y ⟶ X) (j₁ : L₁.ι) (j₂ : L₂.ι) (jL : L.ι) :
    p ⁻¹ᵁ (LB.div (extLB L₁ L₂ f₁ f₂) L).U (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂, jL) ≤
      LB.wchart L₁ (fun _ : PUnit => p ≫ f₁) (fun _ => j₁) := by
  intro y hy
  refine Set.mem_iInter.2 fun _ => ?_
  have h1 := Set.mem_iInter.1 hy.1.1 PUnit.unit
  exact h1

lemma mapsAt₂_le_2 (w : LB.Iso L (extLB L₁ L₂ f₁ f₂)) (p : Y ⟶ X) (j₁ : L₁.ι) (j₂ : L₂.ι) (jL : L.ι) :
    p ⁻¹ᵁ (LB.div (extLB L₁ L₂ f₁ f₂) L).U (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂, jL) ≤
      LB.wchart L₂ (fun _ : PUnit => p ≫ f₂) (fun _ => j₂) := by
  intro y hy
  refine Set.mem_iInter.2 fun _ => ?_
  have h1 := Set.mem_iInter.1 hy.1.2 PUnit.unit
  exact h1

def MapsAt₂ (w : LB.Iso L (extLB L₁ L₂ f₁ f₂)) (p : Y ⟶ X) (n : ℤ)
    (a : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => p) (fun _ => n)))
    (b₁ : LB.Gen (LB.LinComb L₁ (K := PUnit) (fun _ => p ≫ f₁) (fun _ => n)))
    (b₂ : LB.Gen (LB.LinComb L₂ (K := PUnit) (fun _ => p ≫ f₂) (fun _ => n))) : Prop :=
  ∀ (j₁ : L₁.ι) (j₂ : L₂.ι) (jL : L.ι),
    res (mapsAt₂_le_1 w p j₁ j₂ jL) (b₁.s fun _ => j₁) * res (mapsAt₂_le_2 w p j₁ j₂ jL) (b₂.s fun _ => j₂) =
      (pullU p _ (w.s (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂, jL))) ^ n * res (mapsAt₂_le_a w p j₁ j₂ jL) (a.s fun _ => jL)

end MapsAt

structure IsSumPolAV {S : Scheme.{0}} (P P₁ P₂ : PolAV S) (a₁ : P.A ⟶ P₁.A) (a₂ : P.A ⟶ P₂.A) : Prop where
  hom₁ : IsMonHom a₁
  hom₂ : IsMonHom a₂
  lim : IsIso (lift a₁ a₂)
  w : ∃ w : LB.Iso P.L (extLB P₁.L P₂.L a₁.left a₂.left), w.IsGen

variable {R : Type} [CommRing R] [IsDomain R]

structure IsSumDeg (D D₁ D₂ : DegPre R) (p₁ : D.P.A ⟶ D₁.P.A) (p₂ : D.P.A ⟶ D₂.P.A) (q₁ : D.X →+ D₁.X)
    (q₂ : D.X →+ D₂.X) : Prop where
  hom₁ : IsMonHom p₁
  hom₂ : IsMonHom p₂
  lim : IsIso (lift p₁ p₂)
  xsum : Function.Bijective (q₁.prod q₂)
  c_pr₁ : ∀ x, D.c x ≫ p₁ = D₁.c (q₁ x)
  c_pr₂ : ∀ x, D.c x ≫ p₂ = D₂.c (q₂ x)
  w : ∃ w : LB.Iso D.P.L (extLB D₁.P.L D₂.P.L p₁.left p₂.left), w.IsGen ∧
    (∃ b₁ b₂, MapsAt₂ w (eSec D.P.A) 1 D.rig b₁ b₂ ∧ LB.Gen.Corr D₁.P.L _ _ _ _ b₁ D₁.rig ∧
      LB.Gen.Corr D₂.P.L _ _ _ _ b₂ D₂.rig) ∧
    ∀ x, ∃ b₁ b₂, MapsAt₂ w (D.xK x) (-1) (D.psi x) b₁ b₂ ∧ LB.Gen.Corr D₁.P.L _ _ _ _ b₁ (D₁.psi (q₁ x)) ∧
      LB.Gen.Corr D₂.P.L _ _ _ _ b₂ (D₂.psi (q₂ x))

end GlobalTheory.MumProd
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AlgClosedFibre

theorem exists_point_mem_translates :
    ∀ (S : Scheme.{0}) (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S),
      IrreducibleSpace (Over.mk t ⊗ P.A).left → ∀ (U : (Over.mk t ⊗ P.A).left.Opens),
      (U : Set (Over.mk t ⊗ P.A).left).Nonempty → ∀ (a c : Over.mk t ⟶ P.A) (p : Spec (CommRingCat.of K)),
      ∃ u : Over.mk t ⟶ P.A, (lift (𝟙 (Over.mk t)) (c * u * a)).left p ∈ U ∧
        (lift (𝟙 (Over.mk t)) (u⁻¹ * a)).left p ∈ U := by
  intro S P K _ _ t hirr U hU a c p
  let T : Over S := Over.mk t
  let E : Over S := T ⊗ P.A
  have hsm : Smooth P.A.hom := P.isAb.smooth
  have hlft : LocallyOfFiniteType (fst T P.A).left := by
    change LocallyOfFiniteType (pullback.fst t P.A.hom)
    infer_instance
  have hJ0 : JacobsonSpace T.left := by
    change JacobsonSpace (PrimeSpectrum K)
    infer_instance
  have hJ : JacobsonSpace E.left := LocallyOfFiniteType.jacobsonSpace (fst T P.A).left
  let g₁ : E ⟶ E := lift (fst T P.A) ((fst T P.A ≫ c) * snd T P.A * (fst T P.A ≫ a))
  let g₂ : E ⟶ E := lift (fst T P.A) ((snd T P.A)⁻¹ * (fst T P.A ≫ a))
  let h₁ : E ⟶ E := lift (fst T P.A) ((fst T P.A ≫ c)⁻¹ * snd T P.A * (fst T P.A ≫ a)⁻¹)
  let h₂ : E ⟶ E := lift (fst T P.A) ((fst T P.A ≫ a) * (snd T P.A)⁻¹)
  have e₁ : h₁ ≫ g₁ = 𝟙 E := by
    ext1
    · simp [g₁, h₁]
    · simp [g₁, h₁, MonObj.comp_mul, GrpObj.comp_inv, _root_.mul_assoc]
      exact (Category.id_comp _).symm
  have e₂ : h₂ ≫ g₂ = 𝟙 E := by
    ext1
    · simp [g₂, h₂]
    · simp [g₂, h₂, MonObj.comp_mul, GrpObj.comp_inv, _root_.mul_assoc]
      exact (Category.id_comp _).symm
  have ne : ∀ {f g : E ⟶ E}, g ≫ f = 𝟙 E → ((f.left ⁻¹ᵁ U : E.left.Opens) : Set E.left).Nonempty := by
    intro f g h
    obtain ⟨w, hw⟩ := hU
    refine ⟨g.left w, ?_⟩
    change f.left (g.left w) ∈ U
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, h]
    exact hw
  have hin := nonempty_preirreducible_inter (TopologicalSpace.Opens.isOpen _)
      (TopologicalSpace.Opens.isOpen _) (ne e₁) (ne e₂)
  obtain ⟨z, hz, hc⟩ := nonempty_inter_closedPoints hin
    ((TopologicalSpace.Opens.isOpen _).inter (TopologicalSpace.Opens.isOpen _)).isLocallyClosed
  let q := pointOfClosedPoint (fst T P.A).left z hc
  have hq : q ≫ (fst T P.A).left = 𝟙 _ := pointOfClosedPoint_comp _ z hc
  have hqw : q ≫ E.hom = t := by
    rw [← Over.w (fst T P.A), ← Category.assoc, hq, Category.id_comp]
    rfl
  let Q : T ⟶ E := Over.homMk q hqw
  have hQf : Q ≫ fst T P.A = 𝟙 T := by
    ext1
    exact hq
  have hQf' : ∀ (f : T ⟶ P.A), Q ≫ fst T P.A ≫ f = f := fun f => by
    rw [← Category.assoc, hQf, Category.id_comp]
  have hqp : q p = z := pointOfClosedPoint_apply _ z hc p
  refine ⟨Q ≫ snd T P.A, ?_, ?_⟩
  · have hQ : lift (𝟙 T) (c * (Q ≫ snd T P.A) * a) = Q ≫ g₁ := by
      ext1
      · simp only [lift_fst, Category.assoc, g₁, hQf]
      · simp only [lift_snd, Category.assoc, g₁, MonObj.comp_mul, hQf']
    rw [hQ, Over.comp_left, Scheme.Hom.comp_apply]
    change g₁.left (q p) ∈ U
    rw [hqp]
    exact hz.1
  · have hQ : lift (𝟙 T) ((Q ≫ snd T P.A)⁻¹ * a) = Q ≫ g₂ := by
      ext1
      · simp only [lift_fst, Category.assoc, g₂, hQf]
      · simp only [lift_snd, Category.assoc, g₂, MonObj.comp_mul, GrpObj.comp_inv, hQf']
    rw [hQ, Over.comp_left, Scheme.Hom.comp_apply]
    change g₂.left (q p) ∈ U
    rw [hqp]
    exact hz.2

end GlobalTheory.AlgClosedFibre
end

section

open NumberField Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD

theorem _root_.GlobalTheory.T.exists_unitary_lie_basis : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (G : Matrix (Fin r) (Fin r) E), (∀ a b, cc (G a b) = G b a) → G.det ≠ 0 → ∃ e : Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) E, (∀ i, (e i).trace = 0 ∧ ∀ x y, herm G (e i *ᵥ x) y + herm G x (e i *ᵥ y) = 0) ∧ LinearIndependent (maximalRealSubfield E) e := by
  first | exact @GlobalTheory.suLie_finrank_ge | exact GlobalTheory.suLie_finrank_ge | (intros; apply GlobalTheory.suLie_finrank_ge <;> assumption)
end
