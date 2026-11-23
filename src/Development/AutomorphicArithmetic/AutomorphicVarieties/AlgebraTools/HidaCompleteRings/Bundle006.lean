module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Finiteness.Defs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.Bundle001
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.Bundle004
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.Bundle002
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section

section

open IsLocalRing UpperTheory.V.Hi

private theorem restr_pow {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] {Y : Submodule A M}
    {t : Module.End A Y} {φ : Module.End A M} (h : Restr t φ) (n : ℕ) : Restr (t ^ n) (φ ^ n) := by
  induction n with
  | zero => intro y; simp
  | succ n ih => intro y; rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]

private theorem mem_locPart_iff {A M ι : Type} [CommRing A] [IsLocalRing A] [AddCommGroup M] [Module A M]
    {Y : Submodule A M} {op : ι → Module.End A M} {a : ι → A} (u : ι → Module.End A Y)
    (hu : ∀ i, Restr (u i) (op i - algebraMap A _ (a i))) (y : Y) :
    (y : M) ∈ locPart Y op a ↔
      ∀ (i : ι) (k : ℕ), ∃ n : ℕ, (u i ^ n) y ∈ maximalIdeal A ^ k • (⊤ : Submodule A Y) := by
  have hmono : ∀ (i : ι) (k : ℕ), Monotone fun n : ℕ =>
      (maximalIdeal A ^ k • Y).comap ((op i - algebraMap A _ (a i)) ^ n) := by
    intro i k
    refine monotone_nat_of_le_succ fun n x hx => ?_
    rw [Submodule.mem_comap] at hx ⊢
    rw [pow_succ', Module.End.mul_apply]
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr z hz
      rw [map_smul]
      refine Submodule.smul_mem_smul hr ?_
      rw [← hu i ⟨z, hz⟩]
      exact (u i ⟨z, hz⟩).2
    · intro b c hb hc
      rw [map_add (f := _)]
      exact Submodule.add_mem _ hb hc
  unfold locPart
  rw [Submodule.mem_inf, and_iff_right y.2]
  simp only [Submodule.mem_iInf]
  refine forall_congr' fun i => forall_congr' fun k => ?_
  rw [Submodule.mem_iSup_of_directed _ (hmono i k).directed_le]
  refine exists_congr fun n => ?_
  rw [Submodule.mem_comap, Submodule.mem_smul_top_iff, restr_pow (hu i) n y]

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.heckeRestr :
    ∀ (A M ι : Type) [CommRing A] [IsCNL A] [AddCommGroup M] [Module A M] (Y : Submodule A M) [Module.Finite A Y] (op : ι → Module.End A M) (a : ι → A), CommOn Y op → ∀ (T T' : Type) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (j : T →ₐ[A] Module.End A Y) (j' : T' →ₐ[A] Module.End A (locPart Y op a)), Function.Injective j → j.range = heckeAlg Y op → Function.Injective j' → j'.range = heckeAlg (locPart Y op a) op → ∃ r : T →ₐ[A] T', Function.Surjective r ∧ (∀ (s : T) (y : locPart Y op a), (j' (r s) y : M) = j s ⟨y, y.2.1⟩) ∧ ∀ (R : Type) [CommRing R] [IsLocalRing R] (x : T →+* R), (∀ c ∈ maximalIdeal A, x (algebraMap A T c) ∈ maximalIdeal R) → (∀ i s, Restr (j s) (op i) → x s - x (algebraMap A T (a i)) ∈ maximalIdeal R) → locPart Y op a ≠ ⊥ ∧ ∃ x' : T' →+* R, x'.comp (r : T →+* T') = x := by
  intro A M ι _ _ _ _ Y _ op a hC T T' _ _ _ _ j j' hj hjr hj' hjr'
  have ht0 : ∀ i, ∃ s : T, Restr (j s) (op i) := by
    intro i
    have h : (op i).restrict (hC.1 i) ∈ j.range := by
      rw [hjr]
      exact Algebra.subset_adjoin ⟨i, fun _ => rfl⟩
    obtain ⟨s, hs⟩ := h
    refine ⟨s, fun y => ?_⟩
    have hs' : j s = (op i).restrict (hC.1 i) := hs
    rw [hs']
    rfl
  choose t ht using ht0
  have hset : ∀ (Z : Submodule A M) (ρ : T →ₐ[A] Module.End A Z), (∀ i, Restr (ρ (t i)) (op i)) →
      (Algebra.adjoin A (Set.range t)).map ρ = heckeAlg Z op := by
    intro Z ρ hρ
    rw [AlgHom.map_adjoin, heckeAlg]
    congr 1
    ext φ
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, hρ i⟩
    · rintro ⟨i, hi⟩
      exact ⟨t i, ⟨i, rfl⟩, LinearMap.ext fun y => Subtype.ext ((hρ i y).trans (hi y).symm)⟩
  have hgen : Algebra.adjoin A (Set.range t) = ⊤ := by
    refine eq_top_iff.2 fun s _ => ?_
    have h : j s ∈ (Algebra.adjoin A (Set.range t)).map j := by
      rw [hset Y j ht, ← hjr]
      exact ⟨s, rfl⟩
    obtain ⟨s', hs', h'⟩ := h
    rwa [← hj h']
  haveI : IsNoetherian A (Module.End A Y) := isNoetherian_linearMap A Y Y
  haveI : Module.Finite A T := Module.Finite.of_injective j.toLinearMap hj
  obtain ⟨e, he, hnil, h1e, -, -⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.locAbs A T ι t a hgen
  have hI : ∀ μ ∈ (maximalIdeal A).map (algebraMap A T), ∀ y,
      j μ y ∈ maximalIdeal A • (⊤ : Submodule A Y) := by
    intro μ hμ
    refine Submodule.span_induction (p := fun μ _ => ∀ y,
      j μ y ∈ maximalIdeal A • (⊤ : Submodule A Y)) ?_ ?_ ?_ ?_ hμ
    · rintro _ ⟨c, hc, rfl⟩ y
      rw [AlgHom.commutes, Module.algebraMap_end_apply]
      exact Submodule.smul_mem_smul hc Submodule.mem_top
    · intro y; simp
    · intro b c _ _ hb hc y
      rw [map_add (f := _), LinearMap.add_apply]
      exact Submodule.add_mem _ (hb y) (hc y)
    · intro b c _ hc y
      rw [smul_eq_mul, mul_comm, map_mul, Module.End.mul_apply]
      exact hc _
  have hL : ∀ y : Y, (y : M) ∈ locPart Y op a ↔ j e y = y := by
    intro y
    rw [mem_locPart_iff (fun i => j (t i - algebraMap A T (a i)))]
    · exact (UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.locChar A Y T ι (j : T →+* Module.End A Y) _ _ e hI he hnil h1e y).symm
    · intro i z
      rw [map_sub, AlgHom.commutes, LinearMap.sub_apply, LinearMap.sub_apply, Submodule.coe_sub, ht i z]
      rfl
  have hpres : ∀ (s : T) (y : locPart Y op a), (j s ⟨y, y.2.1⟩ : M) ∈ locPart Y op a := by
    intro s y
    rw [hL, ← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply,
      (hL ⟨y, y.2.1⟩).1 y.2]
  have he' : ∀ y : Y, (j e y : M) ∈ locPart Y op a := by
    intro y
    rw [hL, ← Module.End.mul_apply, ← map_mul, he.eq]
  let ρ0 : T → Module.End A (locPart Y op a) := fun s =>
    LinearMap.codRestrict _ (Y.subtype ∘ₗ j s ∘ₗ Submodule.inclusion inf_le_left) (hpres s)
  have hρ0 : ∀ s y, (ρ0 s y : M) = j s ⟨y, y.2.1⟩ := fun _ _ => rfl
  let ρ : T →ₐ[A] Module.End A (locPart Y op a) :=
    { toFun := ρ0
      map_one' := by ext y; rw [hρ0, map_one]; rfl
      map_mul' := fun s s' => by ext y; rw [hρ0, map_mul]; rfl
      map_zero' := by ext y; rw [hρ0, map_zero]; rfl
      map_add' := fun s s' => by ext y; rw [hρ0, map_add (f := _)]; rfl
      commutes' := fun c => by ext y; rw [hρ0, AlgHom.commutes]; rfl }
  have hρ : ∀ s y, (ρ s y : M) = j s ⟨y, y.2.1⟩ := fun _ _ => rfl
  have hrange : ρ.range = j'.range := by
    rw [hjr', ← hset _ ρ (fun i y => by rw [hρ, ht i]), hgen, Algebra.map_top]
  let r : T →ₐ[A] T' := (AlgEquiv.ofInjective j' hj').symm.toAlgHom.comp
    (ρ.codRestrict j'.range fun s => hrange ▸ ⟨s, rfl⟩)
  have hr : ∀ s, j' (r s) = ρ s := fun s =>
    congrArg Subtype.val ((AlgEquiv.ofInjective j' hj').apply_symm_apply
      (ρ.codRestrict j'.range (fun s => hrange ▸ ⟨s, rfl⟩) s))
  have hsurj : Function.Surjective r := by
    intro s'
    have h : j' s' ∈ ρ.range := hrange ▸ ⟨s', rfl⟩
    obtain ⟨s, hs⟩ := h
    exact ⟨s, hj' ((hr s).trans hs)⟩
  refine ⟨r, hsurj, fun s y => by rw [hr, hρ], fun R _ _ x hx hxt => ?_⟩
  have hle : (maximalIdeal A).map (algebraMap A T) ⊔
      Ideal.span (Set.range fun i => t i - algebraMap A T (a i)) ≤ (maximalIdeal R).comap x := by
    refine sup_le (Ideal.map_le_iff_le_comap.2 fun c hc => hx c hc) (Ideal.span_le.2 ?_)
    rintro _ ⟨i, rfl⟩
    have := hxt i (t i) (ht i)
    rwa [← map_sub] at this
  have hxe : x e = 1 := by
    have h1 : 1 - x e ∈ maximalIdeal R := by
      have := hle h1e
      rwa [Ideal.mem_comap, map_sub, map_one] at this
    have h2 : IsUnit (x e) := by
      have := isUnit_one_sub_self_of_mem_nonunits _ h1
      rwa [sub_sub_cancel] at this
    exact h2.mul_left_cancel (by rw [← map_mul, he.eq, mul_one])
  refine ⟨fun hb => ?_, ?_⟩
  · have h0 : e = 0 := by
      refine hj ?_
      rw [map_zero]
      ext y
      have := he' y
      rw [hb] at this
      exact this
    rw [h0, map_zero] at hxe
    exact zero_ne_one hxe
  · have hker : RingHom.ker (r : T →+* T') ≤ RingHom.ker x := by
      intro s hs
      have hs0 : r s = 0 := hs
      have h0 : s * e = 0 := by
        refine hj ?_
        ext y
        have := hρ s ⟨_, he' y⟩
        rw [← hr, hs0, map_zero] at this
        rw [map_mul, map_zero]
        exact this.symm
      rw [RingHom.mem_ker, ← mul_one (x s), ← hxe, ← map_mul, h0, map_zero]
    exact ⟨(r : T →+* T').liftOfSurjective hsurj ⟨x, hker⟩,
      RingHom.liftOfRightInverse_comp _ _ _ _⟩
end

section

open UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite TensorProduct

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.quotOfEig :
    ∀ {K Y ι : Type*} [Field K] [AddCommGroup Y] [Module K Y] [FiniteDimensional K Y] (A : ι → Module.End K Y), (∀ i j, Commute (A i) (A j)) → ∀ (x : ι → K) (y : Y), y ≠ 0 → (∀ i, A i y = x i • y) → ∃ φ : Module.Dual K Y, φ ≠ 0 ∧ ∀ i z, φ (A i z) = x i * φ z := by
  intro K Y ι _ _ _ _ A hA x y hy hAy
  have hc : ∀ i j, Commute (A i).dualMap (A j).dualMap := by
    intro i j
    show (A i).dualMap * (A j).dualMap = (A j).dualMap * (A i).dualMap
    refine LinearMap.ext fun ψ => LinearMap.ext fun z => ?_
    have h := LinearMap.congr_fun (hA j i).eq z
    simp only [Module.End.mul_apply] at h
    simp only [Module.End.mul_apply, LinearMap.dualMap_apply]
    rw [h]
  have hne : Module.Dual.eval K Y y ≠ 0 := by
    intro h0
    apply hy
    refine (Module.forall_dual_apply_eq_zero_iff K y).mp ?_
    intro ψ
    exact LinearMap.congr_fun h0 ψ
  obtain ⟨ψ, hψ, hψA⟩ := eigOfQuot (fun i => (A i).dualMap) hc x (Module.Dual.eval K Y y) hne (by
    intro i ψ
    simp [LinearMap.dualMap_apply, hAy])
  refine ⟨ψ, hψ, fun i z => ?_⟩
  have := LinearMap.congr_fun (hψA i) z
  simpa [LinearMap.dualMap_apply] using this
end

section

open UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite TensorProduct

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.pointEig :
    ∀ {Λ T K M : Type*} [CommRing Λ] [CommRing T] [Algebra Λ T] [Field K] [Algebra Λ K] [AddCommGroup M] [Module Λ M] [Module T M] [IsScalarTower Λ T M] [Module.Finite Λ M] [FaithfulSMul T M] (x : T →ₐ[Λ] K), ∃ y : K ⊗[Λ] M, y ≠ 0 ∧ ∀ t : T, (Algebra.lsmul Λ Λ M t).baseChange K y = x t • y := by
  intro Λ T K M _ _ _ _ _ _ _ _ _ _ _ x
  letI : Algebra T K := x.toRingHom.toAlgebra
  haveI : IsScalarTower Λ T K := IsScalarTower.of_algebraMap_eq fun r => (x.commutes r).symm
  haveI : Module.Finite T M := Module.Finite.of_restrictScalars_finite Λ T M
  have hne : Nontrivial (K ⊗[T] M) := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.fibreNe
  let φ : K ⊗[Λ] M →ₗ[K] K ⊗[T] M := TensorProduct.AlgebraTensorModule.lift
    ((LinearMap.restrictScalarsₗ Λ T M (K ⊗[T] M) K).comp
      (TensorProduct.AlgebraTensorModule.mk T K K M))
  have hφt : ∀ (k : K) (m : M), φ (k ⊗ₜ[Λ] m) = k ⊗ₜ[T] m := by
    intro k m
    simp [φ]
  let A : T → Module.End K (K ⊗[Λ] M) := fun t => (Algebra.lsmul Λ Λ M t).baseChange K
  have hA : ∀ (t : T) (k : K) (m : M), A t (k ⊗ₜ[Λ] m) = k ⊗ₜ[Λ] (t • m) := by
    intro t k m
    simp [A]
  have hc : ∀ s t, Commute (A s) (A t) := by
    intro s t
    show A s * A t = A t * A s
    apply LinearMap.ext
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul k m =>
      rw [Module.End.mul_apply, Module.End.mul_apply, hA, hA, hA, hA, smul_comm]
    | add a b ha hb =>
      rw [Module.End.mul_apply, Module.End.mul_apply] at ha hb ⊢
      rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _), map_add (f := _)]
  have hφA : ∀ t y, φ (A t y) = x t • φ y := by
    intro t y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul k m =>
      rw [hA, hφt, hφt, ← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
      congr 1
    | add a b ha hb =>
      rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _), smul_add]
  have hφ0 : φ ≠ 0 := by
    intro h0
    have hall : ∀ p : K ⊗[T] M, p = 0 := by
      intro p
      induction p using TensorProduct.induction_on with
      | zero => rfl
      | tmul k m => rw [← hφt, h0, LinearMap.zero_apply]
      | add a b ha hb => rw [ha, hb, add_zero]
    obtain ⟨p, hp⟩ := exists_ne (0 : K ⊗[T] M)
    exact hp (hall p)
  exact UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigOfQuot A hc (fun t => x t) φ hφ0 hφA
end
