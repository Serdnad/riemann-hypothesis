module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Invariant.Defs
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle013
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import Mathlib.Algebra.AffineMonoid.Basic
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
public import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem mem_smul_ker_of_flat_quotient {B T C : Type} [CommRing B] [AddCommGroup T] [Module B T]
    [AddCommGroup C] [Module B C] [Module.Flat B C] (φ : T →ₗ[B] C) (hφ : Function.Surjective φ)
    (q : Ideal B) (x : LinearMap.ker φ) (hx : (x : T) ∈ q • (⊤ : Submodule B T)) :
    x ∈ q • (⊤ : Submodule B (LinearMap.ker φ)) := by
  have hinj := LinearMap.lTensor_injective_of_exact_of_flat φ hφ (LinearMap.ker φ).subtype
    (Submodule.injective_subtype _) (LinearMap.exact_subtype_ker_map φ) (B ⧸ q)
  have h0 : ∀ (M : Type) [AddCommGroup M] [Module B M] (y : M),
      ((1 : B ⧸ q) ⊗ₜ[B] y = 0 ↔ y ∈ q • (⊤ : Submodule B M)) := by
    intro M _ _ y
    rw [← Submodule.Quotient.mk_eq_zero, ← TensorProduct.quotTensorEquivQuotSMul_symm_mk,
      LinearEquiv.map_eq_zero_iff]
  rw [← h0]
  apply hinj
  rw [LinearMap.lTensor_tmul, map_zero, h0]
  exact hx

theorem ideal_eq_bot_of_forall_prime_smul_mem {B T : Type} [CommRing B] [CommRing T]
    [Algebra B T] (J : Ideal T) (hJ : J.FG)
    (h : ∀ q : Ideal B, q.IsPrime → ∀ x ∈ J, ∃ s : B, s ∉ q ∧
      s • x ∈ q • (J.restrictScalars B)) : J = ⊥ := by
  by_cases hJt : Submodule.annihilator J = ⊤
  · exact Submodule.annihilator_eq_top_iff.1 hJt
  obtain ⟨n, hn, hJn⟩ := Ideal.exists_le_maximal _ hJt
  have hle : J ≤ n • J := by
    intro x hxJ
    obtain ⟨s, hs, hx⟩ := h (n.comap (algebraMap B T)) (Ideal.comap_isPrime _ _) x hxJ
    have hx' : s • x ∈ n • J := by
      refine Submodule.smul_induction_on hx ?_ ?_
      · intro r hr c hc
        rw [← algebraMap_smul T r c]
        exact Submodule.smul_mem_smul hr hc
      · intro a b ha hb
        exact Submodule.add_mem _ ha hb
    obtain ⟨t, m, hm, e⟩ := hn.exists_inv (x := algebraMap B T s) hs
    have e' : x = t • (s • x) + m • x := by
      rw [← algebraMap_smul T s x, ← mul_smul, ← add_smul, e, one_smul]
    rw [e']
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hx') (Submodule.smul_mem_smul hm hxJ)
  obtain ⟨r, hr, hrM⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul n J hJ hle
  have hrJ : r ∈ n := hJn (Submodule.mem_annihilator.2 hrM)
  exfalso
  apply hn.ne_top
  rw [Ideal.eq_top_iff_one]
  have := n.sub_mem hrJ hr
  rwa [sub_sub_cancel] at this

theorem isPushout_of_tame :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (A B R C : Type) [CommRing A] [CommRing B] [CommRing R] [CommRing C] [MulSemiringAction Γ B] [MulSemiringAction Γ C] [Algebra A B] [Algebra A R] [Algebra B C] [Algebra R C] [Algebra A C] [IsScalarTower A B C] [IsScalarTower A R C] [SMulCommClass Γ A B] [SMulCommClass Γ R C] [Algebra.IsInvariant A B Γ] [Algebra.IsInvariant R C Γ], Function.Injective (algebraMap A B) → Function.Injective (algebraMap R C) → (∀ (g : Γ) (b : B), g • algebraMap B C b = algebraMap B C (g • b)) → IsNoetherianRing R → Module.Finite A B → Module.Finite R C → Module.Flat B C → (∀ q : Ideal B, q.IsPrime → (Nat.card (q.inertia Γ) : B) ∉ q) → (∀ q : Ideal B, q.IsPrime → ∀ g ∈ q.inertia Γ, ∀ c : C, g • c - c ∈ q.map (algebraMap B C)) → Algebra.IsPushout A B R C := by
  intro Γ _ _ A B R C _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hAB hRC heq hnoeth hfAB hfRC hflat hcard hI
  classical
  haveI := Fintype.ofFinite Γ
  haveI : SMulCommClass A Γ B := SMulCommClass.symm _ _ _
  let φ : B ⊗[A] R →ₐ[B] C := Algebra.TensorProduct.lift (Algebra.ofId B C)
    (IsScalarTower.toAlgHom A R C) (fun _ _ => Commute.all _ _)
  have hφ : ∀ (b : B) (r : R), φ (b ⊗ₜ r) = algebraMap B C b * algebraMap R C r := by
    intro b r
    simp [φ, Algebra.ofId_apply]
  have hsurj : Function.Surjective φ := by
    have := span_range_algebraMap_eq_top_of_tame Γ A B R C hAB hRC heq hfRC hcard hI
    have h2 : LinearMap.range φ.toLinearMap = ⊤ := by
      rw [eq_top_iff, ← this, Submodule.span_le]
      rintro _ ⟨r, rfl⟩
      exact ⟨1 ⊗ₜ r, by simp [hφ]⟩
    exact LinearMap.range_eq_top.1 h2
  have hR : ∀ (g : Γ) (r : R), g • algebraMap R C r = algebraMap R C r := by
    intro g r
    rw [Algebra.algebraMap_eq_smul_one, smul_comm, smul_one]
  have hequi : ∀ (g : Γ) (x : B ⊗[A] R), φ (g • x) = g • φ x := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b r => rw [TensorProduct.smul_tmul', hφ, hφ, smul_mul', heq, hR]
    | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), smul_add, hx, hy]
  have hsl : ∀ (g : Γ) (b : B) (x : B ⊗[A] R), g • (b • x) = (g • b) • (g • x) := by
    intro g b x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c r => simp only [TensorProduct.smul_tmul', smul_eq_mul, smul_mul']
    | add x y hx hy => simp only [smul_add, hx, hy]
  have htr : ∀ x : B ⊗[A] R, ∃ r : R, ∑ g : Γ, g • x = (1 : B) ⊗ₜ[A] r := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul c r =>
      obtain ⟨a, ha⟩ := Algebra.IsInvariant.isInvariant (A := A) (G := Γ) (∑ g : Γ, g • c) (by
        intro k
        rw [Finset.smul_sum]
        simp only [← mul_smul]
        exact Equiv.sum_comp (Equiv.mulLeft k) (fun g => g • c))
      refine ⟨a • r, ?_⟩
      simp only [TensorProduct.smul_tmul']
      rw [← TensorProduct.sum_tmul, ← ha, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    | add x y hx hy =>
      obtain ⟨r, hr⟩ := hx
      obtain ⟨s, hs⟩ := hy
      exact ⟨r + s, by simp only [smul_add, Finset.sum_add_distrib, hr, hs, TensorProduct.tmul_add]⟩
  have hinv : ∀ x : B ⊗[A] R, φ x = 0 → (∀ g : Γ, g • x = x) → x = 0 := by
    intro x hx hg
    obtain ⟨b, hb⟩ := exists_finsum_smul_eq_one_of_tame Γ B hcard
    rw [finsum_eq_sum_of_fintype] at hb
    obtain ⟨r, hr⟩ := htr (b • x)
    simp only [hsl, hg] at hr
    rw [← Finset.sum_smul, hb, one_smul] at hr
    rw [hr, hφ, map_one, _root_.one_mul, map_eq_zero_iff _ hRC] at hx
    rw [hr, hx, TensorProduct.tmul_zero]
  have hinert : ∀ q : Ideal B, ∀ g ∈ q.inertia Γ, ∀ x : B ⊗[A] R,
      g • x - x ∈ q • (⊤ : Submodule B (B ⊗[A] R)) := by
    intro q g hg x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c r =>
      have : g • (c ⊗ₜ[A] r) - c ⊗ₜ[A] r = (g • c - c) • ((1 : B) ⊗ₜ[A] r) := by
        simp only [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one, TensorProduct.sub_tmul]
      rw [this]
      exact Submodule.smul_mem_smul (hg c) Submodule.mem_top
    | add x y hx hy =>
      rw [smul_add, add_sub_add_comm]
      exact Submodule.add_mem _ hx hy
  let K : Submodule B (B ⊗[A] R) := LinearMap.ker φ.toLinearMap
  have hK : ∀ x, x ∈ K ↔ φ x = 0 := fun x => Iff.rfl
  letI : SMul Γ K := ⟨fun g x => ⟨g • (x : B ⊗[A] R), by
    rw [hK, hequi, (hK _).1 x.2, smul_zero]⟩⟩
  letI : DistribMulAction Γ K :=
    Function.Injective.distribMulAction K.subtype.toAddMonoidHom K.injective_subtype
      (fun _ _ => rfl)
  haveI : IsNoetherianRing (B ⊗[A] R) := by
    haveI : IsNoetherianRing (R ⊗[A] B) := Algebra.FiniteType.isNoetherianRing R _
    exact isNoetherianRing_of_ringEquiv _ (Algebra.TensorProduct.comm A R B).toRingEquiv
  have hker : RingHom.ker φ = ⊥ := by
    refine ideal_eq_bot_of_forall_prime_smul_mem (B := B) _ (IsNoetherian.noetherian _) ?_
    intro q hq x hx
    obtain ⟨s, hs, hsx⟩ := exists_smul_mem_span_invariants_sup Γ B K
      (fun g b y => Subtype.ext (hsl g b y)) q hq (hcard q hq)
      (fun g hg y => mem_smul_ker_of_flat_quotient φ.toLinearMap hsurj q _ (hinert q g hg y))
      ⟨x, hx⟩
    refine ⟨s, hs, ?_⟩
    have hbot : Submodule.span B {y : K | ∀ g : Γ, g • y = y} = ⊥ := by
      rw [Submodule.span_eq_bot]
      intro y hy
      exact Subtype.ext (hinv y y.2 fun g => congrArg Subtype.val (hy g))
    rw [hbot, bot_sup_eq, Submodule.mem_smul_top_iff] at hsx
    exact hsx
  have hinj : Function.Injective φ := (RingHom.injective_iff_ker_eq_bot φ).2 hker
  exact ⟨IsBaseChange.of_equiv (LinearEquiv.ofBijective φ.toLinearMap ⟨hinj, hsurj⟩)
    (fun r => (hφ 1 r).trans (by simp))⟩

end GlobalTheory
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.TateTower

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def LevelIso (D : Datum H) {K : Type} [Field K] {Q : Type} [Group Q] (act : 𝓞 E → Q → Q)
    (e : ℕ → Q → Q → Kˣ → Prop) (N : ℕ) (p : Kˣ × (D.La → Q)) : Prop :=
  IsPrimitiveRoot p.1 N ∧ (∀ a c, p.2 (a + c) = p.2 a * p.2 c) ∧ (∀ (c : 𝓞 E) a, p.2 (c • a) = act c (p.2 a)) ∧
    (∀ a, p.2 a = 1 ↔ ∃ c, a = N • c) ∧ (∀ x, x ^ N = 1 ↔ ∃ a, p.2 a = x) ∧
    ∀ a c, e N (p.2 a) (p.2 c) (p.1 ^ D.EF a c)

variable {D : Datum H} {K : Type} [Field K] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → Kˣ → Prop}

theorem map_nsmul_of_add {M : Type} [AddCommGroup M] {f : M → Q} (hf : ∀ a c, f (a + c) = f a * f c)
    (n : ℕ) (a : M) : f (n • a) = f a ^ n :=
  map_nsmul (AddMonoidHom.mk' (fun a => Additive.ofMul (f a)) hf) n a

theorem nsmul_cancel (D : Datum H) {r : ℕ} (hr : 0 < r) {a c : D.La} (h : r • a = r • c) : a = c := by
  have := D.proj
  have : Module.Flat ℤ D.La := Module.Flat.trans ℤ (𝓞 E) D.La
  have h' : (r : ℤ) • a = (r : ℤ) • c := by simpa only [natCast_zsmul] using h
  exact smul_right_injective D.La (by exact_mod_cast hr.ne' : (r : ℤ) ≠ 0) h'

theorem LevelIso.pow
    (he : ∀ n m x x' c, 0 < n → 0 < m → x ^ (n * m) = 1 → x' ^ (n * m) = 1 → e (n * m) x x' c →
      e n (x ^ m) (x' ^ m) (c ^ m))
    {N r : ℕ} (hN : 0 < N) (hr : 0 < r) {p : Kˣ × (D.La → Q)} (h : LevelIso D act e (N * r) p) :
    LevelIso D act e N (p ^ r) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hp : ∀ a, (p ^ r).2 a = p.2 (r • a) := fun a => (map_nsmul_of_add h2 r a).symm
  refine ⟨h1.pow (Nat.mul_pos hN hr) (mul_comm _ _), fun a c => ?_, fun c a => ?_, fun a => ?_, fun x => ?_,
    fun a c => ?_⟩
  · rw [hp, hp, hp, smul_add, h2]
  · rw [hp, hp, smul_comm, h3]
  · rw [hp, h4]
    refine exists_congr fun c => ⟨fun h => nsmul_cancel D hr ?_, fun h => ?_⟩
    · rw [h, mul_comm, mul_smul]
    · rw [h, mul_comm, mul_smul]
  · constructor
    · intro hx
      obtain ⟨a, rfl⟩ := (h5 x).1 (by rw [pow_mul, hx, one_pow])
      rw [← map_nsmul_of_add h2, h4] at hx
      obtain ⟨c, hc⟩ := hx
      rw [mul_smul] at hc
      exact ⟨c, by rw [hp, nsmul_cancel D hN hc]⟩
    · rintro ⟨a, rfl⟩
      rw [hp, ← map_nsmul_of_add h2, h4]
      exact ⟨a, by rw [mul_smul]⟩
  · have := he N r _ _ _ hN hr ((h5 _).2 ⟨a, rfl⟩) ((h5 _).2 ⟨c, rfl⟩) (h6 a c)
    have e1 : (p.1 ^ D.EF a c) ^ r = (p.1 ^ r) ^ D.EF a c := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    rw [e1] at this
    exact this

theorem finite_levelIso {N : ℕ} (hN : 0 < N) (hQ : Finite {x : Q // x ^ N = 1}) :
    {p | LevelIso D act e N p}.Finite := by
  have := D.fin
  have hf : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  obtain ⟨S, hS, hSf⟩ := AddGroup.fg_iff.1 (Module.Finite.iff_addGroup_fg.1 hf)
  have := hSf.to_subtype
  have hQ' : {x : Q | x ^ N = 1}.Finite := hQ
  have hζ : {ζ : Kˣ | ζ ^ N = 1}.Finite := by
    have : NeZero N := ⟨hN.ne'⟩
    have : Finite (rootsOfUnity N K) := inferInstance
    exact this
  refine Set.Finite.of_finite_image (f := fun p => (p.1, fun s : S => p.2 s))
    ((hζ.prod (Set.Finite.pi' (fun _ : S => hQ'))).subset ?_) ?_
  · rintro _ ⟨p, hp, rfl⟩
    exact ⟨hp.1.pow_eq_one, fun s => (hp.2.2.2.2.1 _).2 ⟨_, rfl⟩⟩
  · intro p hp q hq h
    refine Prod.ext (Prod.ext_iff.1 h).1 (funext fun a => ?_)
    have := AddMonoidHom.eq_of_eqOn_dense hS
      (f := AddMonoidHom.mk' (fun a => Additive.ofMul (p.2 a)) hp.2.1)
      (g := AddMonoidHom.mk' (fun a => Additive.ofMul (q.2 a)) hq.2.1)
      (fun s hs => congrFun (Prod.ext_iff.1 h).2 ⟨s, hs⟩)
    exact DFunLike.congr_fun this a

theorem tateIso_of_levels : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (K : Type) [Field K] (Q : Type) [Group Q] (act : 𝓞 E → Q → Q) (e : ℕ → Q → Q → Kˣ → Prop) (k : ℕ) (z : K) (κ : Type) (lam : κ → D.La) (y : κ → Q), 0 < k → (∀ n, 0 < n → Finite {x : Q // x ^ n = 1}) → (∀ n m x x' c, 0 < n → 0 < m → x ^ (n * m) = 1 → x' ^ (n * m) = 1 → e (n * m) x x' c → e n (x ^ m) (x' ^ m) (c ^ m)) → (∀ m, 0 < m → ∃ (ζ : Kˣ) (ev : D.La → Q), IsPrimitiveRoot ζ (k * m) ∧ (∀ a c, ev (a + c) = ev a * ev c) ∧ (∀ (c : 𝓞 E) a, ev (c • a) = act c (ev a)) ∧ (∀ a, ev a = 1 ↔ ∃ c, a = (k * m) • c) ∧ (∀ x, x ^ (k * m) = 1 ↔ ∃ a, ev a = x) ∧ (∀ a c, e (k * m) (ev a) (ev c) (ζ ^ D.EF a c)) ∧ (ζ : K) ^ m = z ∧ ∀ i, ev (lam i) ^ m = y i) → ∃ I : TateIso D K Q act e, (I.ζ k : K) = z ∧ ∀ i, I.ev k (lam i) = y i := by
  intro E _ _ _ H D K _ Q _ act e k z κ lam y hk hQ he hex
  have hx : ∀ j : ℕ, ∃ p : Kˣ × (D.La → Q), LevelIso D act e (k * j.factorial) p ∧
      (p.1 : K) ^ j.factorial = z ∧ ∀ i, p.2 (lam i) ^ j.factorial = y i := fun j => by
    obtain ⟨ζ, ev, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hex _ j.factorial_pos
    exact ⟨(ζ, ev), ⟨h1, h2, h3, h4, h5, h6⟩, h7, h8⟩
  choose x hx hz hy using hx
  let U : Ultrafilter ℕ := Ultrafilter.of Filter.atTop
  have hU : ∀ n, 0 < n → ∀ᶠ j : ℕ in U, n ∣ k * j.factorial := fun n hn =>
    Ultrafilter.of_le _ ((Filter.eventually_ge_atTop n).mono fun j hj =>
      Dvd.dvd.mul_left (Nat.dvd_factorial hn hj) k)
  have hs : ∀ n, 0 < n → ∃ s, LevelIso D act e n s ∧ ∀ᶠ j in U, x j ^ (k * j.factorial / n) = s := fun n hn => by
    have hm : {p | LevelIso D act e n p} ∈ U.map fun j => x j ^ (k * j.factorial / n) := by
      refine (hU n hn).mono fun j hj => ?_
      have hj' := hx j
      have hpos := Nat.mul_pos hk j.factorial_pos
      rw [← Nat.mul_div_cancel' hj] at hj'
      exact hj'.pow he hn (Nat.div_pos (Nat.le_of_dvd hpos hj) hn)
    obtain ⟨s, h1, h2⟩ := Ultrafilter.eq_pure_of_finite_mem (finite_levelIso hn (hQ n hn)) hm
    refine ⟨s, h1, ?_⟩
    have : {s} ∈ U.map fun j => x j ^ (k * j.factorial / n) := by
      rw [h2]
      exact rfl
    exact this
  have hs' : ∀ n, ∃ s, LevelIso D act e (max n 1) s ∧ ∀ᶠ j in U, x j ^ (k * j.factorial / max n 1) = s :=
    fun n => hs _ (by omega)
  choose s hs1 hs2 using hs'
  have hs3 : ∀ n, 0 < n → LevelIso D act e n (s n) := fun n hn => by
    have := hs1 n
    rwa [max_eq_left hn] at this
  have hs4 : ∀ n, 0 < n → ∀ᶠ j in U, x j ^ (k * j.factorial / n) = s n := fun n hn => by
    have := hs2 n
    rwa [max_eq_left hn] at this
  have htow : ∀ n m, 0 < n → 0 < m → s (n * m) ^ m = s n := fun n m hn hm => by
    have hnm := Nat.mul_pos hn hm
    obtain ⟨j, h1, h2, c, h3⟩ := ((hs4 _ hnm).and ((hs4 n hn).and (hU _ hnm))).exists
    rw [← h1, ← h2, h3, ← pow_mul, Nat.mul_div_cancel_left _ hnm, Nat.mul_assoc, Nat.mul_div_cancel_left _ hn,
      mul_comm c m]
  obtain ⟨j, hj⟩ := (hs4 k hk).exists
  rw [Nat.mul_div_cancel_left _ hk] at hj
  refine ⟨⟨fun n => (s n).1, fun n hn => (hs3 n hn).1, fun n m hn hm => congrArg Prod.fst (htow n m hn hm),
    fun n => (s n).2, fun n => (hs1 n).2.1, fun n => (hs1 n).2.2.1, fun n hn => (hs3 n hn).2.2.2.1,
    fun n hn => (hs3 n hn).2.2.2.2.1, fun n m hn hm a => congrFun (congrArg Prod.snd (htow n m hn hm)) a,
    fun n hn => (hs3 n hn).2.2.2.2.2⟩, ?_, fun i => ?_⟩
  · show ((s k).1 : K) = z
    rw [← hj, ← hz j]
    exact Units.val_pow_eq_pow_val _ _
  · show (s k).2 (lam i) = y i
    rw [← hj, ← hy j i]
    rfl

end GlobalTheory.TateTower
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.TorsIsometry


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
theorem _root_.GlobalTheory.TorsIsometry.exists_eq_nsmul_of_dvd {M : Type} [AddCommGroup M] (B : LinearMap.BilinForm ℤ M)
    (hB : Function.Bijective B) (n : ℕ) (d : M) (hd : ∀ b, (n : ℤ) ∣ B d b) : ∃ f : M, d = n • f := by
  let φ : M →ₗ[ℤ] ℤ :=
    { toFun := fun b => B d b / n
      map_add' := fun x y => by
        simp only [map_add (f := _)]
        exact Int.add_ediv_of_dvd_left (hd x)
      map_smul' := fun c x => by
        simp only [map_zsmul, smul_eq_mul, RingHom.id_apply]
        exact Int.mul_ediv_assoc c (hd x) }
  obtain ⟨f, hf⟩ := hB.2 φ
  refine ⟨f, hB.1 ?_⟩
  ext b
  simp only [map_nsmul, LinearMap.smul_apply, hf, nsmul_eq_mul]
  exact (Int.mul_ediv_cancel' (hd b)).symm


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
theorem _root_.GlobalTheory.TorsIsometry.ker_and_onto : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (K : Type) [Field K] (Q : Type) [Group Q] (e : Q → Q → Kˣ → Prop) (n : ℕ) (ζ : Kˣ) (ev : D.La → Q), 0 < n → Nat.card {y : Q // y ^ n = 1} = n ^ Module.finrank ℤ D.La → (∀ y c, y ^ n = 1 → e 1 y c → c = 1) → IsPrimitiveRoot ζ n → (∀ a c, ev (a + c) = ev a * ev c) → (∀ a, ev a ^ n = 1) → (∀ a c, e (ev a) (ev c) (ζ ^ D.EF a c)) → (∀ a, ev a = 1 ↔ ∃ c, a = n • c) ∧ ∀ y, y ^ n = 1 ↔ ∃ a, ev a = y := by
  intro E _ _ _ H D K _ Q _ e n ζ ev hn hcard he1 hζ hev hevn hpair
  have hev0 : ev 0 = 1 := by
    have h := hev 0 0
    rw [add_zero] at h
    exact (mul_eq_left.1 h.symm)
  have hevsmul : ∀ (m : ℕ) (c : D.La), ev (m • c) = ev c ^ m := by
    intro m c
    induction m with
    | zero => simp [hev0]
    | succ m ih => rw [succ_nsmul, hev, ih, pow_succ]
  have hker : ∀ a, ev a = 1 ↔ ∃ c, a = n • c := by
    intro a
    constructor
    · intro ha
      refine _root_.GlobalTheory.TorsIsometry.exists_eq_nsmul_of_dvd D.EF D.unimod n a fun c => ?_
      have h := hpair a c
      rw [ha] at h
      exact (hζ.zpow_eq_one_iff_dvd _).1 (he1 _ _ (hevn c) h)
    · rintro ⟨c, rfl⟩
      rw [hevsmul, hevn]
  refine ⟨hker, fun y => ⟨fun hy => ?_, ?_⟩⟩
  swap
  · rintro ⟨a, rfl⟩
    exact hevn a
  haveI : NeZero n := ⟨hn.ne'⟩
  haveI := D.fin
  haveI : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  haveI : NoZeroSMulDivisors ℤ D.La := ⟨fun {c x} h => by
    by_cases hc : c = 0
    · exact Or.inl hc
    · right
      apply D.unimod.1
      ext b
      have := congrArg (fun x => D.EF x b) h
      simp only [map_zsmul, LinearMap.smul_apply, smul_eq_mul, map_zero,
        LinearMap.zero_apply] at this
      simpa [hc] using this⟩
  haveI : Module.Free ℤ D.La := Module.free_of_finite_type_torsion_free'
  let b := Module.finBasis ℤ D.La
  let g : (Fin (Module.finrank ℤ D.La) → ZMod n) → {y : Q // y ^ n = 1} :=
    fun t => ⟨ev (b.equivFun.symm fun i => ((t i).val : ℤ)), hevn _⟩
  have hinj : Function.Injective g := by
    intro t t' htt
    have h : ev (b.equivFun.symm fun i => ((t i).val : ℤ)) =
        ev (b.equivFun.symm fun i => ((t' i).val : ℤ)) := congrArg Subtype.val htt
    have hdiff : ev ((b.equivFun.symm fun i => ((t i).val : ℤ)) -
        b.equivFun.symm fun i => ((t' i).val : ℤ)) = 1 := by
      have h2 := hev ((b.equivFun.symm fun i => ((t i).val : ℤ)) -
        b.equivFun.symm fun i => ((t' i).val : ℤ)) (b.equivFun.symm fun i => ((t' i).val : ℤ))
      rw [sub_add_cancel, h] at h2
      exact mul_eq_right.1 h2.symm
    obtain ⟨c, hc⟩ := (hker _).1 hdiff
    funext i
    have hi := congrArg (fun z => b.equivFun z i) hc
    simp only [map_sub, LinearEquiv.apply_symm_apply, Pi.sub_apply, map_nsmul,
      Pi.smul_apply, nsmul_eq_mul] at hi
    have hcast := congrArg (Int.cast : ℤ → ZMod n) hi
    push_cast at hcast
    simpa [sub_eq_zero] using hcast
  haveI : Finite {y : Q // y ^ n = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  have hbij : Function.Bijective g := hinj.bijective_of_nat_card_le (by
    rw [hcard, Nat.card_fun, Nat.card_zmod, Nat.card_fin])
  obtain ⟨t, ht⟩ := hbij.2 ⟨y, hy⟩
  exact ⟨_, congrArg Subtype.val ht⟩

end GlobalTheory.TorsIsometry
end
