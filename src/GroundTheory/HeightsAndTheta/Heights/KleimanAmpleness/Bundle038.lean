module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle029
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle032
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w u₁ v₁ w₁

namespace Cech

variable {n : ℕ} {U : Finset (Fin n)} {R : Type u₁} [CommRing R]
  {G : Cell U → Type v₁} [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)]
  {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J}
  {G' : Cell U → Type w₁} [∀ I, AddCommGroup (G' I)] [∀ I, Module R (G' I)]
  {ρ' : ∀ I J : Cell U, I.1 ⊆ J.1 → G' I →ₗ[R] G' J}

def mapH (φ : ∀ I, G I →ₗ[R] G' I) (hφ : ∀ I J h m, φ J (ρ I J h m) = ρ' I J h (φ I m)) (i : ℕ) :
    H G ρ i →ₗ[R] H G' ρ' i :=
  Submodule.mapQ _ _ ((mapC φ i).restrict (p := LinearMap.ker (d G ρ i)) (q := LinearMap.ker (d G' ρ' i))
      (fun s hs => by
        change d G' ρ' i (mapC φ i s) = 0
        rw [← mapC_d φ hφ, show d G ρ i s = 0 from hs, map_zero]))
    (by
      intro s hs
      cases i with
      | zero =>
        change (s : Cochain G 0) ∈ (⊥ : Submodule R _) at hs
        rw [Submodule.mem_bot] at hs
        change (mapC φ 0 s : Cochain G' 0) ∈ (⊥ : Submodule R _)
        rw [hs, map_zero]; exact Submodule.zero_mem _
      | succ i =>
        obtain ⟨t, hts⟩ := hs
        refine ⟨mapC φ i t, ?_⟩
        change d G' ρ' i (mapC φ i t) = mapC φ (i + 1) s
        rw [← mapC_d φ hφ, hts]
        rfl)

def hEquivOfEquiv (φ : ∀ I, G I ≃ₗ[R] G' I) (hφ : ∀ I J h m, φ J (ρ I J h m) = ρ' I J h (φ I m)) (i : ℕ) :
    H G ρ i ≃ₗ[R] H G' ρ' i :=
  have hψ : ∀ I J h m, (φ J).symm (ρ' I J h m) = ρ I J h ((φ I).symm m) := fun I J h m => by
    rw [LinearEquiv.symm_apply_eq, hφ, LinearEquiv.apply_symm_apply]
  LinearEquiv.ofLinearMap (mapH (fun I => (φ I).toLinearMap) hφ i)
    (mapH (fun I => (φ I).symm.toLinearMap) hψ i)
    (by
      refine Submodule.linearMap_qext _ (LinearMap.ext fun z => ?_)
      change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
      congr 1
      exact Subtype.ext (funext fun I => (φ I.1).apply_symm_apply _))
    (by
      refine Submodule.linearMap_qext _ (LinearMap.ext fun z => ?_)
      change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
      congr 1
      exact Subtype.ext (funext fun I => (φ I.1).symm_apply_apply _))

end Cech

section Zero

variable (k : Type u) [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} (x : Fin (N + 1) → Ω)
  (E : Type v) [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]

def zeroFamily : SubFamily k x E where
  sub _ := ⊥
  mono _ _ _ _ hy := hy
  mem_iff I J h y := by
    simp only [Submodule.mem_bot]
    constructor
    · rintro rfl
      exact ⟨1, by simp, by simp⟩
    · rintro ⟨a, ha, hay⟩
      obtain ⟨b, hb⟩ := ha.exists_right_inv
      have hne : (a : Ω) ≠ 0 := by
        intro h0
        have h1 := congrArg (fun z : chartRing k x J => (z : Ω)) hb
        change (a : Ω) * _ = 1 at h1
        rw [h0, zero_mul] at h1
        exact zero_ne_one h1
      exact (smul_eq_zero.mp hay).resolve_left hne

end Zero

section Lemmas

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]


omit [Module k E] [IsScalarTower k Ω E] in
theorem twist_sub_eq_bot {F : SubSystem k x E} (hF : ∀ I, F.sub I = ⊥) (Q : SubSystem k x Ω) (I : Chart x) :
    (F.twist Q).sub I = ⊥ := by
  refine Submodule.span_eq_bot.mpr ?_
  rintro _ ⟨q, -, y, hy, rfl⟩
  rw [hF I, Submodule.mem_bot] at hy
  rw [hy, smul_zero]


omit [Module k E] [IsScalarTower k Ω E] in
theorem twistPows_sub_eq_bot {F : SubSystem k x E} (hF : ∀ I, F.sub I = ⊥) :
    ∀ (t : ℕ) (L : Fin t → SubSystem k x Ω) (n : Fin t → ℕ) (I : Chart x), (F.twistPows t L n).sub I = ⊥
  | 0, _, _, I => hF I
  | t + 1, _, _, I => twist_sub_eq_bot (fun I => twistPows_sub_eq_bot hF t _ _ I) _ I


omit [Module k E] [IsScalarTower k Ω E] in
theorem twist_idealSys_primeOf_sub (F : SubSystem k x E) (I : Chart x) :
    (F.twist (idealSys x (primeOf (S := k) x))).sub I = ⊥ := by
  refine Submodule.span_eq_bot.mpr ?_
  rintro _ ⟨q, hq, y, -, rfl⟩
  have hq0 : q = 0 := by
    have h0 : idealMod (primeOf (S := k) x) I = ⊥ := by
      refine Submodule.span_eq_bot.mpr ?_
      rintro _ ⟨f, s, e, hf, _, hfe, _, rfl⟩
      rw [(mem_primeOf_of_isHomogeneous x hfe).mp hf, zero_div]
    have hq' : q ∈ (⊥ : Submodule (chartRing k x I) Ω) := h0 ▸ hq
    exact (Submodule.mem_bot _).mp hq'
  rw [hq0, zero_smul]

theorem eulerCharQuot_of_bot (F₁ F₂ : SubSystem k x E) (h : ∀ I, F₂.sub I = ⊥) :
    eulerCharQuot k F₁ F₂ = eulerChar k F₁ := by
  have hq : ∀ I, SubSystem.quotSub F₁ F₂ I = ⊥ := fun I => by
    refine (Submodule.eq_bot_iff _).mpr fun y hy => Subtype.ext ?_
    have hy' : (y : E) ∈ F₂.sub I := hy
    rw [h I, Submodule.mem_bot] at hy'
    exact hy'
  let φ : ∀ I, F₁.sub I ≃ₗ[k] (F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) := fun I =>
    (Submodule.quotEquivOfEqBot _ (hq I)).symm
  have hφ : ∀ I J h m, φ J (F₁.res I J h m) = SubSystem.quotRes F₁ F₂ I J h (φ I m) := fun _ _ _ _ => rfl
  unfold eulerCharQuot eulerChar
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  exact ((Cech.hEquivOfEquiv φ hφ i).finrank_eq).symm

end Lemmas

theorem SnapperDevissage.proof (hQ : SnapperQuotDevissage.Statement.{u, v, w}) :
    SnapperDevissage.Statement.{u, v, w} := by
  intro k _ Ω _ _ N x E _ _ _ _ F hF
  obtain ⟨r, pp, a, hpp, heq⟩ := hQ k Ω N x E F (zeroFamily k x E) hF (fun _ => bot_le)
    (primeOf (S := k) x) (fun f hf d => homogeneousComponent_mem_primeOf x hf d) le_rfl
    (fun I => (twist_idealSys_primeOf_sub F.toSubSystem I).le)
  refine ⟨r, pp, a, hpp, fun t L n c => ?_⟩
  rw [← heq t L n c]
  exact (eulerCharQuot_of_bot _ _ fun I =>
    twist_sub_eq_bot (twistPows_sub_eq_bot (fun _ => rfl) t _ n) _ I).symm

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

namespace Cech

variable {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R]
  {G : Cell U → Type v} [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)]
  {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J}
  {G' : Cell U → Type w} [∀ I, AddCommGroup (G' I)] [∀ I, Module R (G' I)]
  {ρ' : ∀ I J : Cell U, I.1 ⊆ J.1 → G' I →ₗ[R] G' J}

def mapCEquiv (e : ∀ I, G I ≃ₗ[R] G' I) (i : ℕ) : Cochain G i ≃ₗ[R] Cochain G' i :=
  LinearEquiv.piCongrRight fun I : Idx U i => e I.1

theorem mapCEquiv_d (e : ∀ I, G I ≃ₗ[R] G' I) (he : ∀ I J h m, e J (ρ I J h m) = ρ' I J h (e I m))
    (i : ℕ) (s : Cochain G i) : mapCEquiv e (i + 1) (d G ρ i s) = d G' ρ' i (mapCEquiv e i s) :=
  mapC_d (fun I => (e I).toLinearMap) he i s

theorem mem_bdry_iff (e : ∀ I, G I ≃ₗ[R] G' I) (he : ∀ I J h m, e J (ρ I J h m) = ρ' I J h (e I m))
    (i : ℕ) (s : Cochain G i) : s ∈ bdry G ρ i ↔ mapCEquiv e i s ∈ bdry G' ρ' i := by
  cases i with
  | zero =>
    change s ∈ (⊥ : Submodule R _) ↔ mapCEquiv e 0 s ∈ (⊥ : Submodule R _)
    rw [Submodule.mem_bot, Submodule.mem_bot, LinearEquiv.map_eq_zero_iff]
  | succ i =>
    change s ∈ LinearMap.range (d G ρ i) ↔ mapCEquiv e (i + 1) s ∈ LinearMap.range (d G' ρ' i)
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨mapCEquiv e i t, (mapCEquiv_d e he i t).symm⟩
    · rintro ⟨t', ht'⟩
      refine ⟨(mapCEquiv e i).symm t', (mapCEquiv e (i + 1)).injective ?_⟩
      rw [mapCEquiv_d e he, LinearEquiv.apply_symm_apply, ht']

theorem mem_ker_iff (e : ∀ I, G I ≃ₗ[R] G' I) (he : ∀ I J h m, e J (ρ I J h m) = ρ' I J h (e I m))
    (i : ℕ) (s : Cochain G i) : s ∈ LinearMap.ker (d G ρ i) ↔ mapCEquiv e i s ∈ LinearMap.ker (d G' ρ' i) := by
  rw [LinearMap.mem_ker, LinearMap.mem_ker, ← mapCEquiv_d e he, LinearEquiv.map_eq_zero_iff]

def kerEquiv (e : ∀ I, G I ≃ₗ[R] G' I) (he : ∀ I J h m, e J (ρ I J h m) = ρ' I J h (e I m)) (i : ℕ) :
    LinearMap.ker (d G ρ i) ≃ₗ[R] LinearMap.ker (d G' ρ' i) :=
  LinearEquiv.ofSubmodules (mapCEquiv e i) _ _ (by
    ext z
    rw [Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap, mem_ker_iff e he,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply])

def equivH (e : ∀ I, G I ≃ₗ[R] G' I) (he : ∀ I J h m, e J (ρ I J h m) = ρ' I J h (e I m)) (i : ℕ) :
    H G ρ i ≃ₗ[R] H G' ρ' i :=
  Submodule.Quotient.equiv _ _ (kerEquiv e he i) (by
    ext z
    rw [Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap, Submodule.mem_comap,
      Submodule.mem_comap, Submodule.subtype_apply, Submodule.subtype_apply, mem_bdry_iff e he]
    congr! 1
    change mapCEquiv e i ((mapCEquiv e i).symm (z : Cochain G' i)) = z
    exact LinearEquiv.apply_symm_apply _ _)

end Cech

section Mul

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {F₁ F₂ G₁ G₂ : SubSystem k x Ω} {s : Ω}

def mulSubMap (h₁ : ∀ I, ∀ y ∈ F₁.sub I, s * y ∈ G₁.sub I) (I : Chart x) : F₁.sub I →ₗ[k] G₁.sub I where
  toFun y := ⟨s * y, h₁ I y y.2⟩
  map_add' a b := Subtype.ext (mul_add s (a : Ω) b)
  map_smul' c y := Subtype.ext (by
    change s * ((c • y : F₁.sub I) : Ω) = ((c • (⟨s * y, h₁ I y y.2⟩ : G₁.sub I) : G₁.sub I) : Ω)
    rw [Submodule.coe_smul_of_tower, Submodule.coe_smul_of_tower, mul_smul_comm])

def mulQuotMap (h₁ : ∀ I, ∀ y ∈ F₁.sub I, s * y ∈ G₁.sub I)
    (h₃ : ∀ I, ∀ y ∈ F₁.sub I, (s * y ∈ G₂.sub I ↔ y ∈ F₂.sub I)) (I : Chart x) :
    (F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) →ₗ[k] (G₁.sub I ⧸ SubSystem.quotSub G₁ G₂ I) :=
  (SubSystem.quotSub F₁ F₂ I).mapQ (SubSystem.quotSub G₁ G₂ I) (mulSubMap h₁ I)
    (fun y hy => (h₃ I y y.2).mpr hy)

theorem mulQuotMap_bijective (h₁ : ∀ I, ∀ y ∈ F₁.sub I, s * y ∈ G₁.sub I)
    (h₂ : ∀ I, ∀ z ∈ G₁.sub I, ∃ y ∈ F₁.sub I, z - s * y ∈ G₂.sub I)
    (h₃ : ∀ I, ∀ y ∈ F₁.sub I, (s * y ∈ G₂.sub I ↔ y ∈ F₂.sub I)) (I : Chart x) :
    Function.Bijective (mulQuotMap h₁ h₃ I) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro m hm
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    rw [LinearMap.mem_ker] at hm
    change Submodule.Quotient.mk (mulSubMap h₁ I y) = 0 at hm
    rw [Submodule.Quotient.mk_eq_zero] at hm
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    exact (h₃ I y y.2).mp hm
  · intro m
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    obtain ⟨y, hy, hz⟩ := h₂ I z z.2
    refine ⟨Submodule.Quotient.mk ⟨y, hy⟩, ?_⟩
    change Submodule.Quotient.mk (mulSubMap h₁ I ⟨y, hy⟩) = Submodule.Quotient.mk z
    rw [Submodule.Quotient.eq]
    change ((mulSubMap h₁ I ⟨y, hy⟩ - z : G₁.sub I) : Ω) ∈ G₂.sub I
    rw [Submodule.coe_sub, ← neg_sub]
    exact (G₂.sub I).neg_mem hz

end Mul

theorem MulQuotEq.proof : MulQuotEq.Statement.{u, w} := by
  intro k _ Ω _ _ N x F₁ F₂ G₁ G₂ s h₁ h₂ h₃
  let e : ∀ I, (F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) ≃ₗ[k] (G₁.sub I ⧸ SubSystem.quotSub G₁ G₂ I) :=
    fun I => LinearEquiv.ofBijective (mulQuotMap h₁ h₃ I) (mulQuotMap_bijective h₁ h₂ h₃ I)
  have he : ∀ I J h m, e J (SubSystem.quotRes F₁ F₂ I J h m) = SubSystem.quotRes G₁ G₂ I J h (e I m) := by
    intro I J h m
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    rfl
  unfold eulerCharQuot
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  exact ((Cech.equivH e he i).finrank_eq).symm

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (Cell cellMon IsMGraded)

namespace SectionMapInj

variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

noncomputable def chartMon (S : Type) [CommRing S] (c : ∀ k, ι k) : MRingOver S ι :=
  ∏ k, X ⟨k, c k⟩

def chartCell (c : ∀ k, ι k) : _root_.ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι 0 :=
  ⟨fun k => {c k}, fun _ => Finset.singleton_nonempty _, by simp⟩

theorem dvd_pow_of_mem_cellMon (c : ∀ k, ι k) {t : MRingOver S ι} (ht : t ∈ cellMon S (chartCell c).1) :
    ∃ n : ℕ, t ∣ chartMon S c ^ n := by
  induction ht using Submonoid.closure_induction with
  | mem f hf =>
    obtain ⟨k, i, hi, rfl⟩ := hf
    rw [show i = c k from Finset.mem_singleton.mp hi]
    exact ⟨1, by rw [pow_one]; exact Finset.dvd_prod_of_mem _ (Finset.mem_univ k)⟩
  | one => exact ⟨0, one_dvd _⟩
  | mul a b _ _ ha hb =>
    obtain ⟨m, hm⟩ := ha
    obtain ⟨n, hn⟩ := hb
    exact ⟨m + n, by rw [pow_add]; exact mul_dvd_mul hm hn⟩

variable {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M]

theorem pow_smul_eq_zero_of_le {r : MRingOver S ι} {y : M} {m n : ℕ} (h : r ^ m • y = 0) (hmn : m ≤ n) :
    r ^ n • y = 0 := by
  rw [← Nat.sub_add_cancel hmn, pow_add, mul_smul, h, smul_zero]

theorem exists_pow_smul_eq_zero (c : ∀ k, ι k) {t : MRingOver S ι} (ht : t ∈ cellMon S (chartCell c).1) {y : M}
    (hy : t • y = 0) : ∃ n : ℕ, chartMon S c ^ n • y = 0 := by
  obtain ⟨n, q, hq⟩ := dvd_pow_of_mem_cellMon c ht
  exact ⟨n, by rw [hq, mul_comm, mul_smul, hy, smul_zero]⟩

theorem exists_chart_dvd (N : ℕ) (μ : (Σ k, ι k) →₀ ℕ) (r : S)
    (hμ : ∀ k, Fintype.card (ι k) * N + 1 ≤ ∑ i, μ ⟨k, i⟩) :
    ∃ c : ∀ k, ι k, chartMon S c ^ N ∣ (monomial μ r : MRingOver S ι) := by
  classical
  have hex : ∀ k, ∃ i, N ≤ μ ⟨k, i⟩ := by
    intro k
    by_contra hne
    simp only [not_exists, not_le] at hne
    have hle : ∑ i, μ ⟨k, i⟩ ≤ ∑ _i : ι k, N := Finset.sum_le_sum fun i _ => (hne i).le
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hle
    have := hμ k
    omega
  choose c hc using hex
  refine ⟨c, ?_⟩
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun q => pow_zero _), Fintype.prod_sigma, chartMon,
    ← Finset.prod_pow]
  refine Dvd.dvd.mul_left (Finset.prod_dvd_prod_of_dvd _ _ fun k _ => ?_) _
  exact (pow_dvd_pow _ (hc k)).trans (Finset.dvd_prod_of_mem (fun i => (X ⟨k, i⟩ : MRingOver S ι) ^ μ ⟨k, i⟩)
    (Finset.mem_univ (c k)))

variable [Module S M] [IsScalarTower S (MRingOver S ι) M]

def killedSet (𝓜 : (K → ℤ) → Submodule S M) : Set M :=
  {y | (∃ d, y ∈ 𝓜 d) ∧ ∃ n : ℕ, ∀ c : ∀ k, ι k, chartMon S c ^ n • y = 0}

theorem bound_finset (𝓜 : (K → ℤ) → Submodule S M) (F : Finset M) (hF : (↑F : Set M) ⊆ killedSet (ι := ι) 𝓜) :
    ∃ (D : ℤ) (N : ℕ), ∀ f ∈ F, ∃ d : K → ℤ, f ∈ 𝓜 d ∧ (∀ k, d k ≤ D) ∧
      ∀ c : ∀ k, ι k, chartMon S c ^ N • f = 0 := by
  classical
  revert hF
  induction F using Finset.induction_on with
  | empty => intro _; exact ⟨0, 0, by simp⟩
  | insert a F ha ih =>
    intro hF
    rw [Finset.coe_insert, Set.insert_subset_iff] at hF
    obtain ⟨D, N, hDN⟩ := ih hF.2
    obtain ⟨⟨d, hd⟩, n, hn⟩ := hF.1
    refine ⟨max D (∑ k, |d k|), max N n, fun f hf => ?_⟩
    rcases Finset.mem_insert.mp hf with rfl | hf
    · refine ⟨d, hd, fun k => ?_, fun c => pow_smul_eq_zero_of_le (hn c) (le_max_right _ _)⟩
      exact ((le_abs_self _).trans (Finset.single_le_sum (f := fun k => |d k|) (fun l _ => abs_nonneg _)
        (Finset.mem_univ k))).trans (le_max_right _ _)
    · obtain ⟨e, he, heD, heN⟩ := hDN f hf
      exact ⟨e, he, fun k => (heD k).trans (le_max_left _ _),
        fun c => pow_smul_eq_zero_of_le (heN c) (le_max_left _ _)⟩

theorem exists_finset_span [IsNoetherian (MRingOver S ι) M] (𝓜 : (K → ℤ) → Submodule S M) :
    ∃ F : Finset M, (↑F : Set M) ⊆ killedSet (ι := ι) 𝓜 ∧
      ∀ y ∈ killedSet (ι := ι) 𝓜, y ∈ Submodule.span (MRingOver S ι) (↑F : Set M) := by
  classical
  obtain ⟨W, ⟨F, hFH, rfl⟩, hmax⟩ := (set_has_maximal_iff_noetherian (R := MRingOver S ι) (M := M)).mpr ‹_›
    {W | ∃ F : Finset M, (↑F : Set M) ⊆ killedSet (ι := ι) 𝓜 ∧ W = Submodule.span (MRingOver S ι) (↑F : Set M)}
    ⟨_, ∅, by simp, rfl⟩
  refine ⟨F, hFH, fun y hy => ?_⟩
  by_contra hn
  refine hmax (Submodule.span _ ↑(insert y F)) ⟨insert y F, ?_, rfl⟩ ?_
  · rw [Finset.coe_insert]; exact Set.insert_subset hy hFH
  · refine lt_of_le_of_ne (Submodule.span_mono (by simp)) fun h => hn ?_
    rw [h]; exact Submodule.subset_span (by simp)

end SectionMapInj

theorem SectionMapInj.full : SectionMapInj.Statement := by
  intro S _ K _ ι _ M _ _ _ _ 𝓜 hS hfin hM
  classical
  have := hS
  have : IsNoetherian (MRingOver S ι) M := isNoetherian_of_isNoetherianRing_of_finite _ _
  obtain ⟨F, hFH, hspan⟩ := SectionMapInj.exists_finset_span (ι := ι) 𝓜
  obtain ⟨D, N, hDN⟩ := SectionMapInj.bound_finset (ι := ι) 𝓜 F hFH
  set L : ℕ := ∑ k, Fintype.card (ι k) with hL
  refine ⟨D + L * N + 1, fun c hc x hx hloc => ?_⟩
  have hxH : x ∈ SectionMapInj.killedSet (ι := ι) 𝓜 := by
    refine ⟨⟨c, hx⟩, ?_⟩
    have hch : ∀ ch : ∀ k, ι k, ∃ n : ℕ, SectionMapInj.chartMon S ch ^ n • x = 0 := by
      intro ch
      have h := hloc (SectionMapInj.chartCell ch)
      rw [← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq] at h
      obtain ⟨u, hu⟩ := h
      rw [one_smul, one_smul, smul_zero] at hu
      exact SectionMapInj.exists_pow_smul_eq_zero ch u.2 hu
    choose n hn using hch
    exact ⟨Finset.univ.sup n, fun ch =>
      SectionMapInj.pow_smul_eq_zero_of_le (hn ch) (Finset.le_sup (Finset.mem_univ ch))⟩
  obtain ⟨g, -, hg⟩ := Submodule.mem_span_finset.mp (hspan x hxH)
  have hV : x ∈ ⨆ (e : K → ℤ) (_ : e ≠ c), 𝓜 e := by
    rw [← hg]
    refine Submodule.sum_mem _ fun f hf => ?_
    obtain ⟨d, hfd, hdD, hfN⟩ := hDN f hf
    rw [MvPolynomial.as_sum (g f), Finset.sum_smul]
    refine Submodule.sum_mem _ fun μ _ => ?_
    set a : K → ℕ := fun k => ∑ i, μ ⟨k, i⟩ with ha
    have hhom : IsMultiHomog (monomial μ (AddMonoidAlgebra.coeff (g f) μ) : MRingOver S ι) a := fun m hm k => by
      rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm)]
    have hmem := hM.2 a d _ f hhom hfd
    by_cases he : (d + fun k => (a k : ℤ)) = c
    · have hdeg : ∀ k, Fintype.card (ι k) * N + 1 ≤ ∑ i, μ ⟨k, i⟩ := by
        intro k
        have h1 := congrFun he k
        have h2 := hc k
        have h3 := hdD k
        have h4 : Fintype.card (ι k) ≤ L :=
          Finset.single_le_sum (f := fun k => Fintype.card (ι k)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
        have h5 : ((Fintype.card (ι k) * N : ℕ) : ℤ) ≤ ((L * N : ℕ) : ℤ) := by
          exact_mod_cast Nat.mul_le_mul_right _ h4
        simp only [Pi.add_apply] at h1
        push_cast at h5
        have h6 : ((Fintype.card (ι k) * N + 1 : ℕ) : ℤ) ≤ (a k : ℤ) := by push_cast; linarith
        exact_mod_cast h6
      obtain ⟨ch, q, hq⟩ := SectionMapInj.exists_chart_dvd (S := S) N μ (AddMonoidAlgebra.coeff (g f) μ) hdeg
      rw [hq, mul_comm, mul_smul, hfN ch, smul_zero]
      exact Submodule.zero_mem _
    · exact (le_iSup₂ (f := fun (e : K → ℤ) (_ : e ≠ c) => 𝓜 e) _ he) hmem
  exact Submodule.disjoint_def.mp (hM.1.submodule_iSupIndep c) x hx hV

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end
