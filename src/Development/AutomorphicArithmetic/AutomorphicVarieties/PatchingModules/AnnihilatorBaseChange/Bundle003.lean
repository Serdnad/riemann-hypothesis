module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchedSupportCompletions
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle018
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle067
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SecondSelmerSpanBoundAtAllLevels
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle004

@[expose] public section

section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem fib_tmul_zero {R σ : Type} [CommRing R] (y : σ → R) (S : Type) [CommRing S] [Algebra R S]
    (X : Type) [AddCommGroup X] [Module R X] (hX : ∀ a (x : X), y a • x = 0)
    (k : S) (hk : k ∈ (Ideal.span (Set.range y)).map (algebraMap R S)) (t : S ⊗[R] X) : k • t = 0 := by
  have hI : Ideal.span (Set.range y) ≤ Module.annihilator R X := by
    rw [Ideal.span_le]
    rintro _ ⟨a, rfl⟩
    exact Module.mem_annihilator.mpr (hX a)
  have hmap : (Ideal.span (Set.range y)).map (algebraMap R S) ≤ Module.annihilator S (S ⊗[R] X) := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    have hr' := Module.mem_annihilator.mp (hI hr)
    rw [Ideal.mem_comap, Module.mem_annihilator]
    intro u
    rw [algebraMap_smul]
    induction u using TensorProduct.induction_on with
    | zero => exact smul_zero r
    | tmul a b => rw [← TensorProduct.tmul_smul, hr' b, TensorProduct.tmul_zero]
    | add u v hu hv => rw [smul_add, hu, hv, add_zero]
  exact Module.mem_annihilator.mp (hmap hk) t

private theorem fib_tmul_zero' {R σ : Type} [CommRing R] (y : σ → R) (S : Type) [CommRing S] [Algebra R S]
    (X : Type) [AddCommGroup X] [Module R X] (hX : ∀ a (x : X), y a • x = 0)
    (k : S) (hk : k ∈ (Ideal.span (Set.range y)).map (algebraMap R S)) (x : X) : k ⊗ₜ[R] x = 0 := by
  have := fib_tmul_zero y S X hX k hk (1 ⊗ₜ[R] x)
  rwa [TensorProduct.smul_tmul', smul_eq_mul, mul_one] at this

private theorem fib_bij {R σ : Type} [CommRing R] (y : σ → R) (S BB : Type) [CommRing S] [Algebra R S]
    [CommRing BB] [Algebra S BB] [Algebra R BB] [IsScalarTower R S BB]
    (X : Type) [AddCommGroup X] [Module R X] (hX : ∀ a (x : X), y a • x = 0)
    (hD : ∀ b : BB, ∃ s : S, b - algebraMap S BB s ∈ (Ideal.span (Set.range y)).map (algebraMap R BB))
    (hS : ∀ s : S, algebraMap S BB s ∈ (Ideal.span (Set.range y)).map (algebraMap R BB) →
      s ∈ (Ideal.span (Set.range y)).map (algebraMap R S)) :
    Function.Bijective (LinearMap.rTensor X (IsScalarTower.toAlgHom R S BB).toLinearMap) := by
  classical
  set IB := (Ideal.span (Set.range y)).map (algebraMap R BB) with hIB
  choose sel hsel using hD
  have hz : ∀ (s1 s2 : S) (x : X), algebraMap S BB s1 - algebraMap S BB s2 ∈ IB →
      s1 ⊗ₜ[R] x = s2 ⊗ₜ[R] x := by
    intro s1 s2 x h12
    have h0 := fib_tmul_zero' y S X hX (s1 - s2) (hS _ (by rwa [map_sub])) x
    rwa [TensorProduct.sub_tmul, sub_eq_zero] at h0
  have hrt : ∀ (s : S) (x : X), LinearMap.rTensor X (IsScalarTower.toAlgHom R S BB).toLinearMap (s ⊗ₜ[R] x) = algebraMap S BB s ⊗ₜ[R] x := fun s x => rfl
  let F : BB →ₗ[R] X →ₗ[R] S ⊗[R] X := LinearMap.mk₂ R (fun b x => sel b ⊗ₜ[R] x)
    (fun b1 b2 x => by
      rw [← TensorProduct.add_tmul]
      apply hz
      have e : algebraMap S BB (sel (b1 + b2)) - algebraMap S BB (sel b1 + sel b2) = (b1 - algebraMap S BB (sel b1)) + (b2 - algebraMap S BB (sel b2)) - (b1 + b2 - algebraMap S BB (sel (b1 + b2))) := by
        rw [map_add (f := _)]
        ring
      rw [e]
      exact sub_mem (add_mem (hsel b1) (hsel b2)) (hsel _))
    (fun r b x => by
      rw [TensorProduct.smul_tmul']
      apply hz
      have e : algebraMap S BB (sel (r • b)) - algebraMap S BB (r • sel b) = algebraMap R BB r * (b - algebraMap S BB (sel b)) - (r • b - algebraMap S BB (sel (r • b))) := by
        rw [Algebra.smul_def r (sel b), map_mul, ← IsScalarTower.algebraMap_apply, Algebra.smul_def r b]
        ring
      rw [e]
      exact sub_mem (Ideal.mul_mem_left _ _ (hsel b)) (hsel _))
    (fun b x1 x2 => TensorProduct.tmul_add _ _ _)
    (fun r b x => TensorProduct.tmul_smul _ _ _)
  let g := TensorProduct.lift F
  have hg : ∀ (b : BB) (x : X), g (b ⊗ₜ[R] x) = sel b ⊗ₜ[R] x := fun b x => by
    simp [g, F]
  constructor
  · apply Function.LeftInverse.injective (g := g)
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul s x =>
      rw [hrt, hg]
      apply hz
      have e : algebraMap S BB (sel (algebraMap S BB s)) - algebraMap S BB s = -(algebraMap S BB s - algebraMap S BB (sel (algebraMap S BB s))) := by ring
      rw [e]
      exact neg_mem (hsel _)
    | add u v hu hv => rw [map_add (f := _), map_add (f := _), hu, hv]
  · intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul b x =>
      refine ⟨sel b ⊗ₜ[R] x, ?_⟩
      rw [hrt]
      have h0 := fib_tmul_zero' y BB X hX (b - algebraMap S BB (sel b)) (hsel b) x
      rwa [TensorProduct.sub_tmul, sub_eq_zero, eq_comm] at h0
    | add u v hu hv =>
      obtain ⟨a, ha⟩ := hu
      obtain ⟨c, hc⟩ := hv
      exact ⟨a + c, by rw [map_add (f := _), ha, hc]⟩

private theorem fib_dense {R σ : Type} [CommRing R] (y : σ → R) (f : R) (S BB : Type) [CommRing S] [Algebra R S]
    [IsLocalization.Away f S] [CommRing BB] [Algebra S BB] [Algebra R BB] [IsScalarTower R S BB]
    (h : IsYCpl y f BB) (b : BB) :
    ∃ s : S, b - algebraMap S BB s ∈ (Ideal.span (Set.range y)).map (algebraMap R BB) := by
  obtain ⟨k, r, hkr⟩ := h.dense 1 b
  rw [pow_one] at hkr
  set v := algebraMap S BB (IsLocalization.Away.invSelf (S := S) f) with hv
  have hvf : v * algebraMap R BB f = 1 := by
    rw [hv, IsScalarTower.algebraMap_apply R S BB f, ← map_mul, mul_comm,
      IsLocalization.Away.mul_invSelf, map_one]
  refine ⟨algebraMap R S r * (IsLocalization.Away.invSelf (S := S) f) ^ k, ?_⟩
  have : b - algebraMap S BB (algebraMap R S r * IsLocalization.Away.invSelf (S := S) f ^ k) = v ^ k * (algebraMap R BB f ^ k * b - algebraMap R BB r) := by
    rw [map_mul, map_pow, ← hv, ← IsScalarTower.algebraMap_apply]
    calc b - algebraMap R BB r * v ^ k = (v * algebraMap R BB f) ^ k * b - algebraMap R BB r * v ^ k := by rw [hvf, one_pow, one_mul]
      _ = _ := by ring
  rw [this]
  exact Ideal.mul_mem_left _ _ hkr

private theorem fib_strict {R σ : Type} [CommRing R] (y : σ → R) (f : R) (S BB : Type) [CommRing S] [Algebra R S]
    [IsLocalization.Away f S] [CommRing BB] [Algebra S BB] [Algebra R BB] [IsScalarTower R S BB]
    (h : IsYCpl y f BB) (s : S) (hs : algebraMap S BB s ∈ (Ideal.span (Set.range y)).map (algebraMap R BB)) :
    s ∈ (Ideal.span (Set.range y)).map (algebraMap R S) := by
  obtain ⟨⟨r, m⟩, hrm⟩ := IsLocalization.surj (Submonoid.powers f) s
  obtain ⟨k, hk⟩ := m.2
  simp only at hrm
  rw [← hk] at hrm
  have hB : algebraMap R BB r ∈ (Ideal.span (Set.range y) ^ 1).map (algebraMap R BB) := by
    rw [pow_one, IsScalarTower.algebraMap_apply R S BB r, ← hrm, map_mul]
    exact Ideal.mul_mem_right _ _ hs
  obtain ⟨k', hk'⟩ := h.strict 1 r hB
  rw [pow_one] at hk'
  have hmem : s * algebraMap R S (f ^ (k' + k)) ∈ (Ideal.span (Set.range y)).map (algebraMap R S) := by
    rw [pow_add, map_mul, mul_comm (algebraMap R S (f ^ k')), ← mul_assoc, hrm, ← map_mul, mul_comm]
    exact Ideal.mem_map_of_mem _ hk'
  have hu : IsUnit (algebraMap R S (f ^ (k' + k))) := by
    rw [map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit f).pow _
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  have : s = s * algebraMap R S (f ^ (k' + k)) * w := by rw [mul_assoc, hw, mul_one]
  rw [this]
  exact Ideal.mul_mem_right _ _ hmem

theorem UpperTheory.V.Pa.Core.fibEquiv :
    ∀ (R σ : Type) [CommRing R] [Fintype σ] (y : σ → R) (f : R) (S BB : Type) [CommRing S] [Algebra R S] [IsLocalization.Away f S] [CommRing BB] [Algebra S BB] [Algebra R BB] [IsScalarTower R S BB] (X : Type) [AddCommGroup X] [Module R X] (MM : Type) [AddCommGroup MM] [Module S MM] [Module BB MM] [IsScalarTower S BB MM] (q : MM →ₗ[S] S ⊗[R] X), IsYCpl y f BB → (∀ a (x : X), y a • x = 0) → Function.Surjective q → LinearMap.ker q = (Ideal.span (Set.range y)).map (algebraMap R S) • ⊤ → Nonempty ((MM ⧸ (Ideal.span (Set.range fun a => algebraMap R BB (y a)) • ⊤ : Submodule BB MM)) ≃ₗ[BB] BB ⊗[R] X) := by
  intro R σ _ _ y f S BB _ _ _ _ _ _ _ X _ _ MM _ _ _ _ q hC hX hq hker
  have hbij := fib_bij y S BB X hX (fun b => fib_dense y f S BB hC b)
    (fun s hs => fib_strict y f S BB hC s hs)
  set rT := LinearMap.rTensor X (IsScalarTower.toAlgHom R S BB).toLinearMap with hrTdef
  have hrt : ∀ (s : S) (x : X), rT (s ⊗ₜ[R] x) = algebraMap S BB s ⊗ₜ[R] x := fun s x => rfl
  have hrtS : ∀ (s : S) (t : S ⊗[R] X), rT (s • t) = algebraMap S BB s • rT t := by
    intro s t
    induction t using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | tmul s' x =>
      rw [TensorProduct.smul_tmul', smul_eq_mul, hrt, hrt, TensorProduct.smul_tmul', smul_eq_mul, map_mul]
    | add u v hu hv => rw [smul_add, map_add (f := _), map_add (f := _), hu, hv, smul_add]
  have hJ : Ideal.span (Set.range fun a => algebraMap R BB (y a)) = (Ideal.span (Set.range y)).map (algebraMap R BB) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  have hL : ∀ i ∈ (Ideal.span (Set.range y)).map (algebraMap R BB), ∀ m : MM, q (i • m) = 0 := by
    intro i hi
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hi
    · rintro _ ⟨r, hr, rfl⟩ m
      rw [IsScalarTower.algebraMap_apply R S BB, algebraMap_smul, ← LinearMap.mem_ker, hker]
      exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hr) trivial
    · intro m
      rw [zero_smul, map_zero]
    · intro a c _ _ ha hc m
      rw [add_smul, map_add (f := _), ha, hc, add_zero]
    · intro a c _ hc m
      rw [smul_eq_mul, mul_comm, mul_smul, hc]
  let φ : MM →ₗ[BB] BB ⊗[R] X :=
    { toFun := fun m => rT (q m)
      map_add' := fun a c => by rw [map_add (f := _), map_add (f := _)]
      map_smul' := fun b m => by
        obtain ⟨s, hs⟩ := fib_dense y f S BB hC b
        have e : b • m = s • m + (b - algebraMap S BB s) • m := by
          rw [← algebraMap_smul BB s m, ← add_smul, add_sub_cancel]
        show rT (q (b • m)) = b • rT (q m)
        rw [e, map_add (f := _), map_smul, hL _ hs m, add_zero, hrtS]
        conv_rhs => rw [show b = algebraMap S BB s + (b - algebraMap S BB s) by ring, add_smul, fib_tmul_zero y BB X hX _ hs, add_zero] }
  have hφ : Function.Surjective φ := by
    intro t
    obtain ⟨u, hu⟩ := hbij.2 t
    obtain ⟨m, hm⟩ := hq u
    refine ⟨m, ?_⟩
    show rT (q m) = t
    rw [hm, hu]
  have hK : LinearMap.ker φ = (Ideal.span (Set.range fun a => algebraMap R BB (y a)) • ⊤ : Submodule BB MM) := by
    apply le_antisymm
    · intro m hm
      have h0 : q m = 0 := hbij.1 ((LinearMap.mem_ker.mp hm).trans (map_zero rT).symm)
      rw [← LinearMap.mem_ker, hker] at h0
      have hle : ((Ideal.span (Set.range y)).map (algebraMap R S) • ⊤ : Submodule S MM) ≤ (Ideal.span (Set.range fun a => algebraMap R BB (y a)) • ⊤ : Submodule BB MM).restrictScalars S := by
        rw [Submodule.smul_le]
        intro s hs n _
        rw [Submodule.restrictScalars_mem, ← algebraMap_smul BB s n]
        refine Submodule.smul_mem_smul ?_ trivial
        rw [hJ, IsScalarTower.algebraMap_eq R S BB, ← Ideal.map_map]
        exact Ideal.mem_map_of_mem _ hs
      exact hle h0
    · rw [Submodule.smul_le]
      intro i hi m _
      rw [LinearMap.mem_ker]
      show rT (q (i • m)) = 0
      rw [hJ] at hi
      rw [hL i hi m, map_zero]
  exact ⟨(Submodule.quotEquivOfEq _ _ hK.symm).trans (φ.quotKerEquivOfSurjective hφ)⟩
end

section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

theorem UpperTheory.V.Pa.Core.pmFib :
    ∀ (R σ : Type) [CommRing R] [IsNoetherianRing R] [Fintype σ] (y : σ → R) (f : R) (ii : Ideal R) (X : Type) [AddCommGroup X] [Module R X] [Module.Finite R X] (P : PMod y f ii X) (B : Type) [CommRing B] [Algebra P.BB B] (Q : Ideal B), Q.IsPrime → (∀ a, algebraMap P.BB B (algebraMap R P.BB (y a)) ∈ Q) → (Module.annihilator B (B ⊗[P.BB] P.MM) ≤ Q ↔ Module.annihilator R X ≤ (Q.comap (algebraMap P.BB B)).comap (algebraMap R P.BB)) := by
  intro R σ _ _ _ y f ii X _ _ _ P B _ _ Q hQ hy
  haveI := P.fin
  let Qp : PrimeSpectrum B := ⟨Q, hQ⟩
  let q := PrimeSpectrum.comap (algebraMap P.BB B) Qp
  have h1 := Module.mem_support_iff_of_finite (R := B) (M := B ⊗[P.BB] P.MM) (p := Qp)
  have h2 := mem_support_baseChange P.BB B P.MM Qp
  have h3 := Module.support_quotient (R := P.BB) (M := P.MM)
    (Ideal.span (Set.range fun a => algebraMap R P.BB (y a)))
  have h4 := P.fib.support_eq
  have h5 := mem_support_baseChange R P.BB X q
  have h6 := Module.mem_support_iff_of_finite (R := R) (M := X) (p := PrimeSpectrum.comap (algebraMap R P.BB) q)
  have hz : q ∈ PrimeSpectrum.zeroLocus (Ideal.span (Set.range fun a => algebraMap R P.BB (y a)) : Set P.BB) := by
    rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, Ideal.span_le]
    rintro _ ⟨a, rfl⟩
    exact hy a
  calc Module.annihilator B (B ⊗[P.BB] P.MM) ≤ Q ↔ Qp ∈ Module.support B (B ⊗[P.BB] P.MM) := h1.symm
    _ ↔ q ∈ Module.support P.BB P.MM := h2
    _ ↔ q ∈ Module.support P.BB (P.MM ⧸ (Ideal.span (Set.range fun a => algebraMap R P.BB (y a)) • ⊤ : Submodule P.BB P.MM)) := by
      rw [h3]
      exact ⟨fun h => ⟨h, hz⟩, fun h => h.1⟩
    _ ↔ q ∈ Module.support P.BB (P.BB ⊗[R] X) := by rw [h4]
    _ ↔ PrimeSpectrum.comap (algebraMap R P.BB) q ∈ Module.support R X := h5
    _ ↔ _ := h6
end

section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

theorem UpperTheory.V.Pa.Core.foCong :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W) (j N : ℕ), j ≤ N → fo W - fEl (T.Nq N) W.t.U ∈ maximalIdeal W.R ^ j ∧ m.ρ N (fEl (T.Nq N) W.t.U) = fEl (T.Nq N) (A.A N).U ∧ ∃ c : W.R, fo W - fEl (T.Nq N) W.t.U = (l : W.R) ^ j * c := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W m j N hj
  have hlO : (l : O) ∈ maximalIdeal O := by
    haveI := IsCoef.char (l := l) (O := O)
    rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
    exact CharP.cast_eq_zero _ l
  have hl : (l : W.R) ∈ maximalIdeal W.R := by
    have hco := (inferInstance : IsCO O W.R).isLocalHom
    intro hu
    rw [← map_natCast (algebraMap O W.R)] at hu
    exact hlO (hco.map_nonunit _ hu)
  set I : Ideal W.R := Ideal.span {(l : W.R) ^ j} with hI
  have hq : ∀ jj, (T.Nq N jj : W.R) - 1 ∈ I := by
    intro jj
    obtain ⟨k, hk⟩ := Nat.modEq_iff_dvd.mp (T.Nq_mod N jj).symm
    have h3 := congrArg (Int.cast : ℤ → W.R) hk
    push_cast at h3
    rw [Ideal.mem_span_singleton]
    refine ⟨(l : W.R) ^ (N - j) * (k : W.R), ?_⟩
    rw [h3, ← pow_mul_pow_sub (l : W.R) hj, mul_assoc]
  have hq' : ∀ jj, Ideal.Quotient.mk I (T.Nq N jj : W.R) = 1 := by
    intro jj
    rw [← map_one (Ideal.Quotient.mk I)]
    exact Ideal.Quotient.eq.mpr (hq jj)
  have hmod : Ideal.Quotient.mk I (fo W) = Ideal.Quotient.mk I (fEl (T.Nq N) W.t.U) := by
    simp only [fo, fEl, map_prod, map_mul, map_sub, hq', Nat.cast_one, map_one, one_mul]
  have hdiff : fo W - fEl (T.Nq N) W.t.U ∈ I := Ideal.Quotient.eq.mp hmod
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hdiff
  refine ⟨?_, ?_, ⟨c, hc⟩⟩
  · rw [hc]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hl j)
  · obtain ⟨-, -, -, hU, -⟩ := m.ρ_maps N
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hU
    simp [fEl, map_prod, hU]
end

section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem ann_baseChange_le_iff (B S : Type) [CommRing B] [CommRing S] [Algebra B S] (M : Type) [AddCommGroup M]
    [Module B M] [Module.Finite B M] (P : Ideal S) (hP : P.IsPrime) :
    Module.annihilator S (S ⊗[B] M) ≤ P ↔ Module.annihilator B M ≤ P.comap (algebraMap B S) := by
  have h := UpperTheory.V.AlgebraTools.mem_support_baseChange B S M ⟨P, hP⟩
  rw [Module.mem_support_iff_of_finite, Module.mem_support_iff_of_finite] at h
  exact h

theorem UpperTheory.V.Pa.Core.patchedModule_annihilator_le_comap_iff_ideal_le :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W), Function.Surjective m.π → ∀ P : Ideal (Spo A), P.IsPrime → (Module.annihilator W.R (X0 m) ≤ P.comap m.π ↔ J ≤ P.comap (algebraMap B (Spo A))) := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W m hπ P hP
  have hfin : Module.Finite B A.b.M := by
    letI : Algebra (abelian₂ O Unit D) B := A.b.lam.toRingHom.toAlgebra
    haveI : IsScalarTower (abelian₂ O Unit D) B A.b.M :=
      IsScalarTower.of_algebraMap_smul fun a x => (A.b.smul_lam a x).symm
    haveI := A.b.fin
    exact Module.Finite.of_restrictScalars_finite (abelian₂ O Unit D) B A.b.M
  have h1 : Module.annihilator W.R (X0 m) =
      (Module.annihilator (Spo A) (Spo A ⊗[B] A.b.M)).comap m.π := by
    ext a
    rw [Ideal.mem_comap, Module.mem_annihilator, Module.mem_annihilator]
    exact Iff.rfl
  rw [h1, Ideal.comap_le_comap_iff_of_surjective m.π hπ, ann_baseChange_le_iff B (Spo A) A.b.M P hP]
  exact A.b.supp _ (Ideal.comap_isPrime _ P)
end

section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem UpperTheory.V.Pa.Core.freeN_quot {R S M : Type} [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]
    (s : S →+* R) (I K : Ideal S) (hIK : I ≤ K) (c : ℕ) (e : M ≃+ (Fin c → S ⧸ I))
    (he : ∀ z x, e (s z • x) = z • e x) :
    ∃ e' : (M ⧸ (K.map s • ⊤ : Submodule R M)) ≃+ (Fin c → S ⧸ K), ∀ a x, e' (s a • x) = a • e' x :=
  _root_.UpperTheory.Reformulated.B.FreeModuleQuotient.freeN_quot s I K hIK c e he

private theorem UpperTheory.V.Pa.Core.freeN_le (l : ℕ) (hl : l.Prime) (R : Type) [CommRing R] [IsLocalRing R]
    (hR : (l : R) ∈ maximalIdeal R) (q n : ℕ) (a : Fin q → ℕ) (k j : ℕ) (ha : ∀ i, j + k ≤ a i) :
    delIdeal l R n a ≤ kjIdeal R (Fin q × Fin n) k j := by
  refine Ideal.span_le.2 ?_
  rintro _ ⟨p, rfl⟩
  have h1 := ha p.1
  have h2 : a p.1 - j < l ^ (a p.1 - j) := Nat.lt_pow_self hl.one_lt
  have h := one_add_pow_sub_one_mem (MvPowerSeries (Fin q × Fin n) R) l hl (MvPowerSeries.X p) (a p.1) j k
    (by omega) (by omega)
  refine (sup_le_sup ?_ ?_ : _ ≤ kjIdeal R (Fin q × Fin n) k j) h
  · rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self p)) k
  · rw [Ideal.span_singleton_le_iff_mem]
    have := Ideal.mem_map_of_mem (MvPowerSeries.C : R →+* MvPowerSeries (Fin q × Fin n) R) (Ideal.pow_mem_pow hR j)
    rwa [map_pow, map_natCast] at this

theorem UpperTheory.V.Pa.Core.freeN :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W) (k j : ℕ), ∀ᶠ N in (Λ.U : Filter ℕ), ∃ (c : ℕ) (e : (MN m N ⧸ ((kjIdeal (abelian₂ O Unit D) (Fin T.q × Fin n) k j).map m.s.toRingHom • ⊤ : Submodule W.R (MN m N))) ≃+ (Fin c → Sinf O Unit D T.q n ⧸ kjIdeal (abelian₂ O Unit D) (Fin T.q × Fin n) k j)), ∀ a x, e (m.s.toRingHom a • x) = a • e x := by
  intro l hl L G0 T Λ n O _ _ _ hO _ r B _ _ _ u J D A W m k j
  have hlm : (l : abelian₂ O Unit D) ∈ maximalIdeal (abelian₂ O Unit D) := by
    intro hu
    have h1 := hu.map ((residue O).comp (MvPowerSeries.constantCoeff : abelian₂ O Unit D →+* O))
    haveI := hO.char
    rw [map_natCast, CharP.cast_eq_zero] at h1
    exact not_isUnit_zero h1
  refine Λ.U_le ((eventually_ge_atTop (j + k)).mono fun N hN => ⟨(A.A N).rk, ?_⟩)
  refine freeN_quot (M := MN m N) m.s.toRingHom _ _
    (freeN_le l hl.out _ hlm T.q n (A.A N).a k j fun i => hN.trans ((A.A N).le_a i)) _ (A.A N).e ?_
  intro z x
  have := (A.A N).e_smul z x
  rw [← m.specializationMap_comp_universalSection N z] at this
  exact this
end

section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem tupN_lam {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : GDet n A G) (φ : H →* G)
    (i : ℕ) (g : H) : (D.comap φ).lam i (MonoidAlgebra.single g 1) = D.lam i (MonoidAlgebra.single (φ g) 1) := by
  show (-1) ^ i * _root_.AddMonoidAlgebra.coeff (M := ℕ) (D.D (Polynomial A) (MonoidAlgebra.mapDomainRingHom (Polynomial A) φ
      (MonoidAlgebra.single 1 Polynomial.X -
        MonoidAlgebra.mapRingHom H Polynomial.C (MonoidAlgebra.single g 1)))) (n - i) = _
  rw [map_sub]
  simp [GDet.lam, GDet.chi, MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single]

private theorem tupN_ofRep {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H]
    (ρ : G →* Matrix (Fin n) (Fin n) A) (φ : H →* G) : (GDet.ofRep ρ).comap φ = GDet.ofRep (ρ.comp φ) := by
  refine GDet.ext fun B _ _ x => ?_
  change (GDet.repAlg ρ B (MonoidAlgebra.mapDomainRingHom B φ x)).det = (GDet.repAlg (ρ.comp φ) B x).det
  congr 1
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | single g r => simp [GDet.repAlg]

private theorem tupN_X {R σ : Type} [CommRing R] [IsLocalRing R] (a : σ) :
    (MvPowerSeries.X a : MvPowerSeries σ R) ∈ maximalIdeal (MvPowerSeries σ R) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff,
    MvPowerSeries.constantCoeff_X]
  exact not_isUnit_zero

theorem UpperTheory.V.Pa.Core.tupN :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T), Adapted T (r := r) → ∀ N, ∃ t : Tup Λ A (A.A N).R, t.D = (A.A N).p.D.comap (πN0 Λ N) ∧ t.ψ = (A.A N).p.ψ ∧ t.s = (A.A N).s (MvPowerSeries.C (MvPowerSeries.X (.inl ()))) ∧ t.U = (A.A N).U ∧ t.y = fun j i => (A.A N).s (MvPowerSeries.X (j, i)) := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A hAd N
  haveI : IsAdicComplete (maximalIdeal O) O := IsCoef.complete (l := l)
  haveI hO : IsCO O O :=
    { complete := inferInstance
      isLocalHom := ⟨fun x hx => by simpa using hx⟩
      res_surj := fun x => ⟨x, by simp⟩ }
  haveI hL : IsCO O (abelian₂ O Unit D) := co_mvps O O (Unit ⊕ Fin D)
  haveI hS : IsCO O (Sinf O Unit D T.q n) := co_mvps O (abelian₂ O Unit D) (Fin T.q × Fin n)
  have hC : ∀ x : abelian₂ O Unit D, x ∈ maximalIdeal (abelian₂ O Unit D) →
      (MvPowerSeries.C x : Sinf O Unit D T.q n) ∈ maximalIdeal (Sinf O Unit D T.q n) := by
    intro x hx
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff,
      MvPowerSeries.constantCoeff_C]
    exact (IsLocalRing.mem_maximalIdeal x).mp hx
  have hmap : ∀ z : Sinf O Unit D T.q n, z ∈ maximalIdeal (Sinf O Unit D T.q n) →
      (A.A N).s z ∈ maximalIdeal (A.A N).R := by
    intro z hz
    rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
    exact hz
  have hcomp := (A.A N).compat
  have key : ∀ (g : Ph0 Λ) (i : Fin n),
      (r.chib i) ((T.h N).p₀ (πN0 Λ N g)) = (r.chib i) (Λ.h.p₀ (πo0 Λ g)) := by
    intro g i
    have hH := hAd.1 ((T.h N).p₀ (πN0 Λ N g) * (Λ.h.p₀ (πo0 Λ g))⁻¹) (Λ.modH N g) i
    rw [map_mul, map_inv, mul_inv_eq_one] at hH
    exact hH
  refine ⟨⟨(A.A N).p.D.comap (πN0 Λ N), ?_, ?_, (A.A N).p.ψ, ?_,
    (A.A N).s (MvPowerSeries.C (MvPowerSeries.X (.inl ()))), ?_, (A.A N).U, (A.A N).U_res,
    fun j i => (A.A N).s (MvPowerSeries.X (j, i)), ?_⟩, rfl, rfl, rfl, rfl, rfl⟩
  · intro i M
    have h2 := ((A.A N).p.cont i M).comp_continuous (Λ.π0_cont N)
    convert h2 using 1
    funext g
    simp only [Function.comp_apply, tupN_lam]
    rfl
  · show ((A.A N).p.D.map (res O (A.A N).R : (A.A N).R →+* ResidueField O)).comap (πN0 Λ N) = _
    rw [(A.A N).p.red]
    simp only [Resid.Dbar, tupN_ofRep]
    congr 1
    ext g i j
    simp only [MonoidHom.comp_apply, diagRep, MonoidHom.coe_mk, OneHom.coe_mk]
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq]
      rw [hcomp.1 i, MonoidHom.comp_apply, key]
    · simp [Matrix.diagonal_apply_ne _ hij]
  · intro v i
    have hp := (A.A N).p.psi v i
    exact ⟨hp.cont, fun g => by rw [hp.red g, hcomp.2.1], fun g => by rw [hp.mu g, hcomp.2.2] <;> rfl⟩
  · exact hmap _ (hC _ (tupN_X _))
  · intro j i
    exact hmap _ (tupN_X _)
end
