module

public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
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
public import Mathlib.RingTheory.HopfAlgebra.Convolution
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Basify
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
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

@[expose] public section

section

open scoped TensorProduct

namespace GlobalTheory


open TensorProduct in
theorem isUnit_of_unit_mul_comul_eq_tmul_self (K H : Type) [Field K] [CommRing H] [HopfAlgebra K H]
    (c : H ⊗[K] H) (hc : IsUnit c) (u : H) (hu : u ≠ 0)
    (h : c * Coalgebra.comul (R := K) u = u ⊗ₜ[K] u) : IsUnit u := by

  let φ : H ⊗[K] H →ₐ[K] H :=
    (Algebra.TensorProduct.lid K H).toAlgHom.comp
      (Algebra.TensorProduct.map (Bialgebra.counitAlgHom K H) (AlgHom.id K H))
  have hφΔ : φ (Coalgebra.comul (R := K) u) = u := by
    have e := congrArg (TensorProduct.lid K H) (Coalgebra.rTensor_counit_comul (R := K) u)
    rw [TensorProduct.lid_tmul, one_smul] at e
    exact e
  have hφuu : φ (u ⊗ₜ[K] u) = Coalgebra.counit (R := K) u • u := by
    simp [φ]
  have hε : Coalgebra.counit (R := K) u ≠ 0 := by
    intro h0
    have e := congrArg φ h
    rw [map_mul, hφΔ, hφuu, h0, zero_smul] at e
    exact hu ((hc.map φ).mul_right_eq_zero.mp e)

  let ψ : H ⊗[K] H →ₐ[K] H :=
    Algebra.TensorProduct.lift (AlgHom.id K H) (HopfAlgebra.antipodeAlgHom K H)
      (fun _ _ => Commute.all _ _)
  have hψΔ : ψ (Coalgebra.comul (R := K) u) = algebraMap K H (Coalgebra.counit (R := K) u) := by
    rw [← HopfAlgebra.mul_antipode_lTensor_comul_apply (R := K) u]
    induction Coalgebra.comul (R := K) u using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [ψ]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hψuu : ψ (u ⊗ₜ[K] u) = u * HopfAlgebra.antipode K u := by
    simp [ψ]
  have e := congrArg ψ h
  rw [map_mul, hψΔ, hψuu] at e
  have hU : IsUnit (u * HopfAlgebra.antipode K u) := by
    rw [← e]
    exact (hc.map ψ).mul ((isUnit_iff_ne_zero.mpr hε).map (algebraMap K H))
  exact isUnit_of_mul_isUnit_left hU

end GlobalTheory
end

section

open TensorProduct Polynomial

namespace GlobalTheory

theorem torsion_of_one_tmul_eq_zero (D K M : Type) [CommRing D] [IsDomain D] [Field K]
    [Algebra D K] [FaithfulSMul D K] [AddCommGroup M] [Module D M] (m : M)
    (h : (1 : K) ⊗ₜ[D] m = 0) : ∃ d : D, d ≠ 0 ∧ d • m = 0 := by
  letI : Algebra (FractionRing D) K := FractionRing.liftAlgebra D K
  haveI : IsScalarTower D (FractionRing D) K := FractionRing.isScalarTower_liftAlgebra D K
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap (FractionRing D) K)
    (by rw [LinearMap.ker_eq_bot]; exact (algebraMap (FractionRing D) K).injective)
  have hg1 : g 1 = 1 := by
    have := LinearMap.congr_fun hg 1
    simpa using this
  have h2 : (1 : FractionRing D) ⊗ₜ[D] m = 0 := by
    have := congrArg ((g.restrictScalars D).rTensor M) h
    simpa [hg1] using this
  obtain ⟨⟨d, hd⟩, hdm⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors D)
    (TensorProduct.mk D (FractionRing D) M 1)).1 h2
  exact ⟨d, nonZeroDivisors.ne_zero hd, hdm⟩

theorem exists_not_mem_ker_smul_mem_map_of_one_tmul_eq_zero (A B K : Type) [CommRing A] [CommRing B]
    [Algebra A B] [Field K] [Algebra A K] (b : B) (h : (1 : K) ⊗ₜ[A] b = 0) :
    ∃ f : A, f ∉ RingHom.ker (algebraMap A K) ∧
      f • b ∈ (RingHom.ker (algebraMap A K)).map (algebraMap A B) := by
  set P := RingHom.ker (algebraMap A K) with hP
  haveI : P.IsPrime := RingHom.ker_isPrime _
  letI : Algebra (A ⧸ P) K := (RingHom.kerLift (algebraMap A K)).toAlgebra
  haveI : IsScalarTower A (A ⧸ P) K := IsScalarTower.of_algebraMap_eq' (by ext a; rfl)
  haveI : FaithfulSMul (A ⧸ P) K :=
    (faithfulSMul_iff_algebraMap_injective (A ⧸ P) K).2 (RingHom.kerLift_injective _)
  let I := P.map (algebraMap A B)
  let q : B →ₗ[A] B ⧸ I := (Ideal.Quotient.mkₐ A I).toLinearMap
  let Φ : K ⊗[A] B →ₗ[A] K ⊗[A ⧸ P] (B ⧸ I) :=
    (TensorProduct.mapOfCompatibleSMul (A ⧸ P) A A K (B ⧸ I)) ∘ₗ q.lTensor K
  have h1 : (1 : K) ⊗ₜ[A ⧸ P] (Ideal.Quotient.mk I b) = 0 := by
    have hΦ : Φ ((1 : K) ⊗ₜ[A] b) = (1 : K) ⊗ₜ[A ⧸ P] (Ideal.Quotient.mk I b) := rfl
    rw [← hΦ, h, map_zero]
  obtain ⟨d, hd0, hdb⟩ := torsion_of_one_tmul_eq_zero (A ⧸ P) K (B ⧸ I) _ h1
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective d
  refine ⟨f, fun hf => hd0 (Ideal.Quotient.eq_zero_iff_mem.2 hf), ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have : Ideal.Quotient.mk I (f • b) = (Ideal.Quotient.mk P f) • Ideal.Quotient.mk I b := by
    rw [Algebra.smul_def, map_mul, Algebra.smul_def]
    rfl
  rw [this, hdb]

end GlobalTheory
end

section

namespace GlobalTheory

theorem surj_mod_of_surj_mod_map_sup_of_pow_map_le :
    ∀ (B A : Type) [CommRing B] [CommRing A] [Algebra B A] (I : Ideal B) (K : Ideal A) (N : ℕ),
      (∀ a : A, ∃ b : B, a - algebraMap B A b ∈ I.map (algebraMap B A) ⊔ K) →
      (I ^ N).map (algebraMap B A) ≤ K → ∀ a : A, ∃ b : B, a - algebraMap B A b ∈ K := by
  intro B A _ _ _ I K N hsurj hN
  set f := algebraMap B A with hf
  set J := I.map f with hJ

  have key : ∀ n : ℕ, ∀ a : A, ∃ b : B, a - f b ∈ J ^ n ⊔ K := by
    intro n
    induction n with
    | zero =>
      intro a
      exact ⟨0, by simp⟩
    | succ n ih =>

      have hspan : ∀ x ∈ J ^ n, ∀ c : A, ∃ b : B, c * x - f b ∈ J ^ (n + 1) ⊔ K := by
        intro x hx
        rw [hJ, ← Ideal.map_pow] at hx
        unfold Ideal.map at hx
        induction hx using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨i, hi, rfl⟩ := hx
          intro c
          obtain ⟨b', hb'⟩ := hsurj c
          obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hb'
          refine ⟨b' * i, ?_⟩
          have hfi : f i ∈ J ^ n := by
            rw [hJ, ← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hi
          have hc : c = f b' + y + z := by rw [add_assoc, hyz]; ring
          have e : c * f i - f (b' * i) = f i * y + z * f i := by
            rw [hc, map_mul]; ring
          rw [e]
          refine Submodule.add_mem_sup ?_ (K.mul_mem_right _ hz)
          rw [pow_succ]
          exact Ideal.mul_mem_mul hfi hy
        | zero =>
          intro c; exact ⟨0, by simp⟩
        | add x y _ _ hx hy =>
          intro c
          obtain ⟨b1, h1⟩ := hx c
          obtain ⟨b2, h2⟩ := hy c
          refine ⟨b1 + b2, ?_⟩
          have e : c * (x + y) - f (b1 + b2) = (c * x - f b1) + (c * y - f b2) := by
            rw [map_add (f := _)]; ring
          rw [e]; exact add_mem h1 h2
        | smul d x _ hx =>
          intro c
          obtain ⟨b, h⟩ := hx (c * d)
          refine ⟨b, ?_⟩
          rw [smul_eq_mul, ← mul_assoc]; exact h
      intro a
      obtain ⟨b, hb⟩ := ih a
      obtain ⟨x, hx, k, hk, hxk⟩ := Submodule.mem_sup.mp hb
      obtain ⟨b2, hb2⟩ := hspan x hx 1
      refine ⟨b + b2, ?_⟩
      have e : a - f (b + b2) = (1 * x - f b2) + k := by
        rw [map_add (f := _), one_mul]; linear_combination -hxk
      rw [e]
      refine add_mem hb2 (Submodule.mem_sup_right hk)
  intro a
  obtain ⟨b, hb⟩ := key N a
  refine ⟨b, ?_⟩
  have hle : J ^ N ⊔ K ≤ K := by
    refine sup_le ?_ le_rfl
    rw [hJ, ← Ideal.map_pow]; exact hN
  exact hle hb

end GlobalTheory
end

section

open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory

theorem tensor_isLocalRing_of_unique_prime_over : ∀ (P T L : Type) [CommRing P] [CommRing T] [CommRing L] [Algebra P T] [Algebra P L] [IsLocalRing L] [Algebra.IsIntegral P T] (𝔐 : Ideal T) [𝔐.IsPrime],
    𝔐.comap (algebraMap P T) = (maximalIdeal L).comap (algebraMap P L) →
    (∀ 𝔔 : Ideal T, 𝔔.IsPrime → 𝔔.comap (algebraMap P T) = (maximalIdeal L).comap (algebraMap P L) → 𝔔 = 𝔐) →
    (∀ y : L, ∃ a : P, y - algebraMap P L a ∈ maximalIdeal L) →
    IsLocalRing (TensorProduct P T L) := by
  intro P T L _ _ _ _ _ _ _ 𝔐 _ hM huniq hres

  let fκ : P →ₐ[P] L ⧸ maximalIdeal L := Algebra.ofId P _
  have hfκ : ∀ a, fκ a = Ideal.Quotient.mk (maximalIdeal L) (algebraMap P L a) := fun a => rfl
  have hsurj : Function.Surjective fκ := by
    intro z
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨a, ha⟩ := hres y
    exact ⟨a, by rw [hfκ]; exact (Ideal.Quotient.eq.mpr ha).symm⟩
  have hker : RingHom.ker fκ = (maximalIdeal L).comap (algebraMap P L) := by
    ext a
    rw [RingHom.mem_ker, hfκ, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_comap]
  let e : (P ⧸ RingHom.ker fκ) ≃ₐ[P] L ⧸ maximalIdeal L := Ideal.quotientKerAlgEquivOfSurjective hsurj
  let q : (P ⧸ RingHom.ker fκ) →ₐ[P] T ⧸ 𝔐 :=
    Ideal.quotientMapₐ 𝔐 (Algebra.ofId P T) (le_of_eq (by rw [hker, ← hM]; rfl))
  let g : L →ₐ[P] T ⧸ 𝔐 := (q.comp e.symm.toAlgHom).comp (Ideal.Quotient.mkₐ P (maximalIdeal L))
  have hg : ∀ a : P, ∀ y : L, y - algebraMap P L a ∈ maximalIdeal L →
      g y = Ideal.Quotient.mk 𝔐 (algebraMap P T a) := by
    intro a y hy
    have h1 : Ideal.Quotient.mkₐ P (maximalIdeal L) y = Ideal.Quotient.mkₐ P (maximalIdeal L) (algebraMap P L a) := by
      rw [Ideal.Quotient.mkₐ_eq_mk]; exact Ideal.Quotient.eq.mpr hy
    have h2 : g y = g (algebraMap P L a) := by
      simp only [g, AlgHom.comp_apply]; rw [h1]
    rw [h2, AlgHom.commutes]; rfl
  let ψ : TensorProduct P T L →ₐ[P] T ⧸ 𝔐 :=
    Algebra.TensorProduct.lift (Ideal.Quotient.mkₐ P 𝔐) g (fun _ _ => Commute.all _ _)
  have hψ : ∀ t y, ψ (t ⊗ₜ[P] y) = Ideal.Quotient.mk 𝔐 t * g y := by
    intro t y; simp [ψ, Algebra.TensorProduct.lift_tmul]
  haveI : Nontrivial (T ⧸ 𝔐) := Ideal.Quotient.nontrivial_iff.mpr (Ideal.IsPrime.ne_top inferInstance)
  have hψs : Function.Surjective ψ := by
    intro z
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨t ⊗ₜ[P] 1, by rw [hψ, map_one, mul_one]⟩
  haveI : Nontrivial (TensorProduct P T L) := hψs.nontrivial

  letI : Algebra L (TensorProduct P T L) := Algebra.TensorProduct.rightAlgebra
  have hmap : ∀ x, algebraMap L (TensorProduct P T L) x = (1 : T) ⊗ₜ[P] x := fun _ => rfl
  have hint : Algebra.IsIntegral L (TensorProduct P T L) := by
    constructor
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact isIntegral_zero
    | add a b ha hb => exact ha.add hb
    | tmul a b =>
      have h1 : a ⊗ₜ[P] b = (a ⊗ₜ[P] (1 : L)) * algebraMap L (TensorProduct P T L) b := by
        rw [hmap]; simp
      rw [h1]
      refine IsIntegral.mul ?_ isIntegral_algebraMap
      have ha : IsIntegral P a := Algebra.IsIntegral.isIntegral a
      have h2 : IsIntegral P (a ⊗ₜ[P] (1 : L)) :=
        ha.map (Algebra.TensorProduct.includeLeft : T →ₐ[P] TensorProduct P T L)
      obtain ⟨p, hp, hp0⟩ := h2
      refine ⟨p.map (algebraMap P L), hp.map _, ?_⟩
      rw [Polynomial.eval₂_map]
      have : (algebraMap L (TensorProduct P T L)).comp (algebraMap P L) = algebraMap P _ := by
        ext x
        exact (Algebra.TensorProduct.includeRight : L →ₐ[P] TensorProduct P T L).commutes x
      rw [this]; exact hp0
  have hPB : ∀ a : P, (algebraMap P T a) ⊗ₜ[P] (1 : L) = (1 : T) ⊗ₜ[P] (algebraMap P L a) := by
    intro a
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have key : ∀ 𝔫 : Ideal (TensorProduct P T L), 𝔫.IsMaximal → 𝔫 = RingHom.ker ψ := by
    intro 𝔫 h𝔫
    have hLmax : (𝔫.comap (algebraMap L (TensorProduct P T L))).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
        (algebraMap L (TensorProduct P T L)) (by
          intro x
          exact hint.isIntegral x) 𝔫
    have hL : 𝔫.comap (algebraMap L (TensorProduct P T L)) = maximalIdeal L :=
      IsLocalRing.eq_maximalIdeal hLmax
    let iT : T →+* TensorProduct P T L := Algebra.TensorProduct.includeLeftRingHom
    have hiT : ∀ t, iT t = t ⊗ₜ[P] (1 : L) := fun _ => rfl
    have hcomp : iT.comp (algebraMap P T) = (algebraMap L (TensorProduct P T L)).comp (algebraMap P L) := by
      ext a; simp only [RingHom.comp_apply, hiT, hmap]; exact hPB a
    have hT : 𝔫.comap iT = 𝔐 := by
      apply huniq
      · exact Ideal.comap_isPrime iT 𝔫
      · rw [Ideal.comap_comap, hcomp, ← Ideal.comap_comap, hL]
    let j : T ⧸ 𝔐 →+* TensorProduct P T L ⧸ 𝔫 := Ideal.quotientMap 𝔫 iT hT.ge
    have hj : Function.Injective j := Ideal.quotientMap_injective' hT.le
    have hφ : ∀ b, Ideal.Quotient.mk 𝔫 b = j (ψ b) := by
      intro b
      induction b using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]
      | tmul t y =>
        obtain ⟨a, ha⟩ := hres y
        have hy1 : (1 : T) ⊗ₜ[P] (y - algebraMap P L a) ∈ 𝔫 := by
          rw [← hmap, ← Ideal.mem_comap, hL]; exact ha
        have hsplit : t ⊗ₜ[P] y - (t * algebraMap P T a) ⊗ₜ[P] (1 : L) = (t ⊗ₜ[P] (1 : L)) * ((1 : T) ⊗ₜ[P] (y - algebraMap P L a)) := by
          rw [TensorProduct.tmul_sub, mul_sub, ← hPB]
          simp [Algebra.TensorProduct.tmul_mul_tmul]
        rw [hψ, hg a y ha, ← map_mul]
        show _ = Ideal.quotientMap 𝔫 iT hT.ge (Ideal.Quotient.mk 𝔐 (t * algebraMap P T a))
        rw [Ideal.quotientMap_mk, Ideal.Quotient.eq, hiT, hsplit]
        exact 𝔫.mul_mem_left _ hy1
    ext b
    rw [← Ideal.Quotient.eq_zero_iff_mem, hφ, RingHom.mem_ker, map_eq_zero_iff j hj]
  obtain ⟨𝔫₀, h0⟩ := Ideal.exists_maximal (TensorProduct P T L)
  exact IsLocalRing.of_unique_max_ideal ⟨𝔫₀, h0, fun 𝔫 h => (key 𝔫 h).trans (key 𝔫₀ h0).symm⟩

end GlobalTheory
end

section

open IsLocalRing

namespace GlobalTheory

theorem pushout_residue_linearIndependent :
  ∀ (T D A B : Type) [CommRing T] [CommRing D] [CommRing A] [CommRing B] [IsLocalRing T] [IsLocalRing D] [Algebra T D] [Algebra T A] [Algebra D B] [Algebra A B] [Algebra T B] [IsScalarTower T D B] [IsScalarTower T A B] [Algebra.IsPushout T D A B], (maximalIdeal T).map (algebraMap T D) = maximalIdeal D → ∀ (n : ℕ) (x : Fin n → A), (∀ c : Fin n → T, ∑ i, c i • x i ∈ (maximalIdeal T).map (algebraMap T A) → ∀ i, c i ∈ maximalIdeal T) → ∀ d : Fin n → D, ∑ i, d i • algebraMap A B (x i) ∈ (maximalIdeal D).map (algebraMap D B) → ∀ i, d i ∈ maximalIdeal D := by
  intro T D A B _ _ _ _ _ _ _ _ _ _ _ _ _ _ hTD n x hx d hd j

  haveI : IsLocalHom (algebraMap T D) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have h1 : a ∈ maximalIdeal T := (mem_maximalIdeal a).2 hna
    have h2 : algebraMap T D a ∈ maximalIdeal D := hTD ▸ Ideal.mem_map_of_mem _ h1
    exact (mem_maximalIdeal _).1 h2 ha
  letI : Field (T ⧸ maximalIdeal T) := Ideal.Quotient.field _

  let v : Fin n → A ⧸ (maximalIdeal T • (⊤ : Submodule T A)) := fun i => Submodule.Quotient.mk (x i)
  have hmem : ∀ y : A, y ∈ maximalIdeal T • (⊤ : Submodule T A) ↔
      y ∈ (maximalIdeal T).map (algebraMap T A) := by
    intro y; rw [Ideal.smul_top_eq_map]; rfl
  have hli : LinearIndependent (T ⧸ maximalIdeal T) v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    obtain ⟨c', rfl⟩ : ∃ c' : Fin n → T, (fun k => Ideal.Quotient.mk (maximalIdeal T) (c' k)) = c :=
      ⟨fun k => (Ideal.Quotient.mk_surjective (c k)).choose,
        funext fun k => (Ideal.Quotient.mk_surjective (c k)).choose_spec⟩
    have hsum : (∑ k, Ideal.Quotient.mk (maximalIdeal T) (c' k) • v k) =
        Submodule.Quotient.mk (p := maximalIdeal T • (⊤ : Submodule T A)) (∑ k, c' k • x k) := by

      rw [← Submodule.mkQ_apply, map_sum]
      rfl
    rw [hsum, Submodule.Quotient.mk_eq_zero, hmem] at hc
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hx c' hc i)

  let bs := Module.Basis.span hli
  obtain ⟨f, hf⟩ := LinearMap.exists_extend (K := T ⧸ maximalIdeal T) (bs.coord j)
  have hfv : ∀ i, f (v i) = if i = j then 1 else 0 := by
    intro i
    have := congrArg (fun F => F (bs i)) hf
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, Module.Basis.coord_apply,
      Module.Basis.repr_self] at this
    rw [Module.Basis.span_apply] at this
    rw [this, Finsupp.single_apply]

  let φ : T ⧸ maximalIdeal T →+* ResidueField D := ResidueField.map (algebraMap T D)
  have hφ : ∀ t : T, φ (Ideal.Quotient.mk _ t) = algebraMap T (ResidueField D) t := fun t => rfl

  let g : A →ₗ[T] ResidueField D :=
    { toFun := fun a => φ (f (Submodule.Quotient.mk (p := maximalIdeal T • (⊤ : Submodule T A)) a))
      map_add' := fun a b => by simp only [Submodule.Quotient.mk_add, map_add (f := _)]
      map_smul' := fun t a => by
        simp only [RingHom.id_apply]
        have hq : Submodule.Quotient.mk (p := maximalIdeal T • (⊤ : Submodule T A)) (t • a) =
            Ideal.Quotient.mk (maximalIdeal T) t •
              Submodule.Quotient.mk (p := maximalIdeal T • (⊤ : Submodule T A)) a :=
          (Module.Quotient.mk_smul_mk A (maximalIdeal T) t a).symm
        rw [hq, map_smul, smul_eq_mul, map_mul, hφ, ← Algebra.smul_def] }
  have hg : ∀ i, g (x i) = if i = j then 1 else 0 := by
    intro i
    show φ (f (v i)) = _
    rw [hfv]; split_ifs <;> simp

  have hbc := (Algebra.IsPushout.out (R := T) (S := D) (R' := A) (S' := B))
  let ψ := hbc.lift g
  have hψ : ∀ a : A, ψ (algebraMap A B a) = g a := fun a => hbc.lift_eq g a
  have hkill : ∀ y ∈ (maximalIdeal D).map (algebraMap D B), ψ y = 0 := by
    intro y hy
    have hy' : y ∈ maximalIdeal D • (⊤ : Submodule D B) := by
      rw [Ideal.smul_top_eq_map]; exact hy
    refine Submodule.smul_induction_on hy' ?_ ?_
    · intro r hr b _
      rw [map_smul, Algebra.smul_def]
      have : algebraMap D (ResidueField D) r = 0 := (residue_eq_zero_iff r).2 hr
      rw [this, zero_mul]
    · intro a b ha hb; rw [map_add (f := _), ha, hb, add_zero]
  have := hkill _ hd

  rw [map_sum, Finset.sum_eq_single j (fun i _ hi => by rw [map_smul, hψ, hg, if_neg hi, smul_zero])
  (by simp)] at this
  rw [map_smul, hψ, hg, if_pos rfl, Algebra.smul_def, mul_one] at this
  exact (residue_eq_zero_iff _).1 this

end GlobalTheory
end

section

open IsLocalRing

namespace GlobalTheory.AbhyankarLocal

variable (S L D : Type) [CommRing S] [Field L] [Algebra S L] [CommRing D] [Algebra S D]

noncomputable def toNorm : integralClosure S L →+* integralClosure D (TensorProduct S D L) :=
  RingHom.codRestrict
    ((Algebra.TensorProduct.includeRight (R := S) (A := D) (B := L)).toRingHom.comp
      (integralClosure S L).val.toRingHom)
    (integralClosure D (TensorProduct S D L)) (fun o => by
      have h : IsIntegral S (Algebra.TensorProduct.includeRight (R := S) (A := D) (B := L) (o : L)) :=
        o.2.map _
      exact h.tower_top)

@[simp] theorem toNorm_coe (o : integralClosure S L) :
    ((toNorm S L D o : integralClosure D (TensorProduct S D L)) : TensorProduct S D L) =
      (1 : D) ⊗ₜ[S] (o : L) := rfl

variable {S L D}

noncomputable def locHom (Q : Ideal (integralClosure D (TensorProduct S D L))) [Q.IsPrime] :
    Localization.AtPrime (Q.comap (toNorm S L D)) →+* Localization.AtPrime Q :=
  IsLocalization.lift (M := (Q.comap (toNorm S L D)).primeCompl)
    (g := (algebraMap _ (Localization.AtPrime Q)).comp (toNorm S L D)) (fun s =>
      IsLocalization.map_units (Localization.AtPrime Q) (⟨toNorm S L D s, s.2⟩ : Q.primeCompl))

theorem locHom_algebraMap (Q : Ideal (integralClosure D (TensorProduct S D L))) [Q.IsPrime]
    (o : integralClosure S L) :
    locHom Q (algebraMap _ _ o) = algebraMap _ (Localization.AtPrime Q) (toNorm S L D o) :=
  IsLocalization.lift_eq _ _

end GlobalTheory.AbhyankarLocal
end
