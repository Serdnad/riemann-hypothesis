module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.TCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ScNorm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.AuChi
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

private theorem plus_eq {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    {D : Raw Ω c} (T : Tower D) (x : Ω) : x ∈ T.F ↔ ∃ y : W.Lp T.L, algebraMap (W.Lp T.L) Ω y = x := by
  classical
  set E : Subfield T.L := Subfield.comap (T.L.val : T.L →+* Ω) T.F.toSubfield with hEdef
  let e : E ≃+* T.F :=
    { toFun := fun y => ⟨((y : T.L) : Ω), y.2⟩
      invFun := fun z => ⟨⟨(z : Ω), T.F_le z.2⟩, z.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  haveI : IsTotallyReal E := IsTotallyReal.ofRingEquiv e.symm
  have hEM : E ≤ maximalRealSubfield T.L := IsTotallyReal.le_maximalRealSubfield E
  have hdE : Module.finrank ℚ E = Module.finrank ℚ T.F :=
    (RingEquiv.toRatAlgEquiv e).toLinearEquiv.finrank_eq
  have hsup : Module.finrank ℚ T.L ≤ Module.finrank ℚ T.F * 2 := by
    have h1 := IntermediateField.finrank_sup_le T.F T.K
    rw [T.degK, ← T.hL] at h1
    exact h1
  have hM : Module.finrank ℚ (maximalRealSubfield T.L) * 2 = Module.finrank ℚ T.L := by
    rw [← Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield T.L) T.L]
    exact (letI : Module.Free (maximalRealSubfield T.L) T.L := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield T.L) T.L)
  letI : Module.Free E T.L := Module.Free.of_divisionRing _ _
  have hE2 : Module.finrank ℚ E * Module.finrank E T.L = Module.finrank ℚ T.L :=
    Module.finrank_mul_finrank ℚ E T.L
  have hle : Module.finrank ℚ E ≤ Module.finrank ℚ (maximalRealSubfield T.L) :=
    LinearMap.finrank_le_finrank_of_injective
      (f := (Subfield.inclusion hEM).toRatAlgHom.toLinearMap) (Subfield.inclusion hEM).injective
  have hpos : 0 < Module.finrank ℚ E := Module.finrank_pos
  have hposM : 0 < Module.finrank ℚ (maximalRealSubfield T.L) := Module.finrank_pos
  have hdeg : Module.finrank E T.L = 2 := by
    apply le_antisymm
    · have : Module.finrank ℚ E * Module.finrank E T.L ≤ Module.finrank ℚ E * 2 := by
        rw [hE2, hdE]; exact hsup
      exact Nat.le_of_mul_le_mul_left this hpos
    · have : Module.finrank ℚ (maximalRealSubfield T.L) * 2 ≤
          Module.finrank ℚ (maximalRealSubfield T.L) * Module.finrank E T.L := by
        rw [hM, ← hE2]
        exact Nat.mul_le_mul_right _ hle
      exact Nat.le_of_mul_le_mul_left this hposM
  haveI : Algebra.IsQuadraticExtension E T.L := { finrank_eq_two' := hdeg }
  have hEq : E = maximalRealSubfield T.L := NumberField.CMExtension.eq_maximalRealSubfield T.L E
  constructor
  · intro hx
    have hy : (⟨x, T.F_le hx⟩ : T.L) ∈ maximalRealSubfield T.L := by
      rw [← hEq]; exact hx
    exact ⟨⟨⟨x, T.F_le hx⟩, hy⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    have hy : (y : T.L) ∈ E := by rw [hEq]; exact y.2
    exact hy

private theorem fix_L {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    {D : Raw Ω c} (T : Tower D) (τ : G T.F Ω) : τ ∈ T.GalL ↔ ∀ x : T.L, τ (x : Ω) = x := by
  have hF : resQ T.F τ ∈ T.F.fixingSubgroup := by
    rw [IntermediateField.fixingSubgroup, mem_fixingSubgroup_iff]
    intro y hy
    exact τ.commutes ⟨y, hy⟩
  unfold Tower.GalL
  rw [Subgroup.mem_comap]
  constructor
  · intro h x
    have hsup : resQ T.F τ ∈ (T.F ⊔ T.K).fixingSubgroup := by
      rw [IntermediateField.fixingSubgroup_sup]
      exact ⟨hF, h⟩
    rw [← T.hL, IntermediateField.fixingSubgroup, mem_fixingSubgroup_iff] at hsup
    exact hsup x x.2
  · intro h
    rw [IntermediateField.fixingSubgroup, mem_fixingSubgroup_iff]
    intro y hy
    exact h ⟨y, Lk.K_le T hy⟩

theorem UpperTheory.V.Ws.Lk.galEq :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} (T : Tower D), (∀ x : Ω, x ∈ T.F ↔ ∃ y : W.Lp T.L, algebraMap (W.Lp T.L) Ω y = x) ∧ (∃ φ : G (W.Lp T.L) Ω ≃* G T.F Ω, (∀ σ x, φ σ x = σ x) ∧ ∀ σ, φ σ ∈ T.GalL ↔ σ ∈ (W.resP T.L Ω).range) ∧ ∀ τ : G T.F Ω, τ ∈ T.GalL ↔ τ ∈ (resLe T.F_le).range := by
  intro Ω _ _ _ l _ c D T
  have hP := plus_eq T
  refine ⟨hP, ?_, ?_⟩
  · let φ : G (W.Lp T.L) Ω ≃* G T.F Ω :=
      { toFun := fun σ => AlgEquiv.ofRingEquiv (f := (σ : Ω ≃ₐ[W.Lp T.L] Ω).toRingEquiv) (fun x => by
            obtain ⟨y, hy⟩ := (hP (x : Ω)).1 x.2
            change σ (x : Ω) = (x : Ω)
            rw [← hy]
            exact σ.commutes y)
        invFun := fun σ => AlgEquiv.ofRingEquiv (f := (σ : Ω ≃ₐ[T.F] Ω).toRingEquiv) (fun y => by
            have hx := (hP (algebraMap (W.Lp T.L) Ω y)).2 ⟨y, rfl⟩
            exact σ.commutes ⟨_, hx⟩)
        left_inv := fun σ => by ext; rfl
        right_inv := fun σ => by ext; rfl
        map_mul' := fun σ τ => by ext; rfl }
    refine ⟨φ, fun σ x => rfl, fun σ => ?_⟩
    rw [fix_L, MonoidHom.mem_range]
    constructor
    · intro h
      exact ⟨AlgEquiv.ofRingEquiv (f := (σ : Ω ≃ₐ[W.Lp T.L] Ω).toRingEquiv) (fun x => h x), by ext; rfl⟩
    · rintro ⟨ρ, rfl⟩ x
      exact ρ.commutes x
  · intro τ
    rw [fix_L, MonoidHom.mem_range]
    constructor
    · intro h
      exact ⟨AlgEquiv.ofRingEquiv (f := (τ : Ω ≃ₐ[T.F] Ω).toRingEquiv) (fun x => h x), by ext; rfl⟩
    · rintro ⟨ρ, rfl⟩ x
      exact ρ.commutes x
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

private theorem kill {Γ M : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CommGroup M] (f : Γ →* M)
    (hf : IsClosed (f.ker : Set Γ)) {g : Γ} {n : ℕ} (hg : g ^ n ∈ (commutator Γ).topologicalClosure) : f g ^ n = 1 := by
  rw [← map_pow]
  have hle : (commutator Γ).topologicalClosure ≤ f.ker :=
    Subgroup.topologicalClosure_minimal _ (Abelianization.commutator_subset_ker f) hf
  exact hle hg

private theorem padic_pow_l {l : ℕ} [hl : Fact l.Prime] (h2 : l ≠ 2) (x : ℤ_[l]) (hx : x ^ l = 1) : x = 1 := by
  have hp := PadicInt.prime_p (p := l)
  have hodd : Odd l := hl.out.odd_of_ne_two h2
  have hc : PadicInt.toZMod x = 1 := by
    have h1 : PadicInt.toZMod x ^ l = 1 := by rw [← map_pow, hx, map_one]
    rw [ZMod.pow_card] at h1
    exact h1
  have hdvd : (l : ℤ_[l]) ∣ x - 1 := by
    have hs := PadicInt.toZMod_spec x
    rw [hc, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton, ZMod.cast_eq_val, ZMod.val_one,
      Nat.cast_one] at hs
    exact hs
  have hnd : ¬ (l : ℤ_[l]) ∣ x := by
    intro h
    have h1 : (l : ℤ_[l]) ∣ x ^ l := dvd_pow h hl.out.ne_zero
    rw [hx] at h1
    exact hp.not_dvd_one h1
  have key := emultiplicity_pow_prime_sub_pow_prime hp hodd hdvd hnd
  rw [hx, one_pow, sub_self, emultiplicity_zero] at key
  by_contra hne
  have hfin : FiniteMultiplicity (l : ℤ_[l]) (x - 1) :=
    FiniteMultiplicity.of_not_isUnit hp.not_unit (sub_ne_zero.2 hne)
  rw [hfin.emultiplicity_eq_multiplicity] at key
  exact ENat.coe_ne_top (multiplicity (l : ℤ_[l]) (x - 1) + 1) (by push_cast; exact key.symm)

private theorem padic_pow {l : ℕ} [Fact l.Prime] (h2 : l ≠ 2) (a : ℕ) (x : ℤ_[l]) (hx : x ^ l ^ a = 1) : x = 1 := by
  induction a generalizing x with
  | zero => simpa using hx
  | succ a ih =>
    apply ih
    apply padic_pow_l h2
    rw [← pow_mul, ← pow_succ]
    exact hx

theorem UpperTheory.V.Ws.Lk.kapMu :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} (P : Pre T), D.Good → ∀ (g : G T.L Ω) (a : ℕ), g ^ l ^ a ∈ (commutator (G T.L Ω)).topologicalClosure → P.κ g = 1 ∧ P.tL g = 1 := by
  intro Ω _ _ _ l _ c D T P hD g a hg
  have h2 : l ≠ 2 := Raw.Good.l_odd hD
  have hl := (Fact.out : l.Prime)
  have hcLe : Continuous (resLe (K_le T)) := by
    letI : Algebra T.K T.L := (IntermediateField.inclusion (K_le T)).toAlgebra
    haveI : IsScalarTower T.K T.L Ω := IsScalarTower.of_algebraMap_eq (fun x => rfl)
    exact Af.continuous_restrictScalarsHom T.K T.L Ω
  have ht : P.tL g = 1 := by
    have hk : IsClosed ((P.t.comp (resLe (K_le T))).ker : Set (G T.L Ω)) :=
      isClosed_singleton.preimage (P.t_cont.comp hcLe)
    have hp := kill (P.t.comp (resLe (K_le T))) hk hg
    change (P.t.comp (resLe (K_le T))) g = 1
    have hz : (l ^ a) • Multiplicative.toAdd ((P.t.comp (resLe (K_le T))) g) = 0 := by
      rw [← toAdd_pow, hp, toAdd_one]
    have hz' := (smul_eq_zero.1 hz).resolve_left (pow_ne_zero _ hl.ne_zero)
    rw [← ofAdd_toAdd ((P.t.comp (resLe (K_le T))) g), hz', ofAdd_zero]
  refine ⟨?_, ht⟩
  have hβ : P.βL g = 1 := P.β_t ht
  have hγ : P.γ (resQ T.L g) = 1 := by
    have hcQ : Continuous (resQ T.L) := Af.continuous_restrictScalarsHom ℚ T.L Ω
    have hk : IsClosed (((cycZ ℚ Ω l).comp (resQ T.L)).ker : Set (G T.L Ω)) :=
      isClosed_singleton.preimage ((continuous_cycZ ℚ Ω l).comp hcQ)
    have hp := kill ((cycZ ℚ Ω l).comp (resQ T.L)) hk hg
    have hu : ((((cycZ ℚ Ω l).comp (resQ T.L)) g : ℤ_[l]ˣ) : ℤ_[l]) = 1 :=
      padic_pow h2 a _ (by rw [← Units.val_pow_eq_pow_val, hp, Units.val_one])
    exact P.γ_ker (Units.ext hu)
  have hκ : P.κ₀ (resLe (K_le T) g) = 1 := by
    have hk : IsClosed ((P.κ₀.comp (resLe (K_le T))).ker : Set (G T.L Ω)) :=
      (Subgroup.isClosed_of_isOpen _ P.κ₀_open).preimage hcLe
    have hp := kill (P.κ₀.comp (resLe (K_le T))) hk hg
    obtain ⟨m, hm, hm1⟩ := P.κ₀_ord
    have hq : P.κ₀ (resLe (K_le T) g) ^ m = 1 := by
      rw [← MonoidHom.pow_apply, hm1, MonoidHom.one_apply]
    have hcop : Nat.Coprime (l ^ a) m := Nat.Coprime.pow_left a hm
    have := pow_gcd_eq_one.2 ⟨hp, hq⟩
    rwa [hcop, pow_one] at this
  have hγ' : P.γ (AlgEquiv.restrictScalars ℚ g) = 1 := hγ
  simp only [Pre.κ, MonoidHom.mul_apply, MonoidHom.comp_apply, hβ, hγ, hκ]
  simp [hγ', hβ]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

private theorem cont_resLe {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {F L : IntermediateField ℚ Ω} (h : F ≤ L) :
    Continuous (resLe h) := by
  letI : Algebra F L := (IntermediateField.inclusion h).toRingHom.toAlgebra
  haveI : IsScalarTower F L Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Af.continuous_restrictScalarsHom F L Ω

private theorem cont_of_open_ker {Γ H : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] (f : Γ →* H) (h : IsOpen (f.ker : Set Γ)) : Continuous f := by
  refine continuous_of_continuousAt_one f ?_
  rw [ContinuousAt, map_one]
  have hk : (f.ker : Set Γ) ∈ nhds (1 : Γ) := h.mem_nhds (one_mem _)
  exact (Filter.tendsto_pure.2 (Filter.mem_of_superset hk fun x hx => MonoidHom.mem_ker.1 hx)).mono_right (pure_le_nhds _)

theorem UpperTheory.V.Ws.Lk.kapCont :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} (P : Pre T), Continuous P.κ ∧ Continuous P.βL ∧ Continuous P.tL := by
  intro Ω _ _ _ l _ c D T P
  have hβ : Continuous P.βL := P.β_cont.comp (cont_resLe _)
  have ht : Continuous P.tL := P.t_cont.comp (cont_resLe _)
  refine ⟨?_, hβ, ht⟩
  have h0 : Continuous (P.κ₀.comp (resLe (K_le T))) :=
    (cont_of_open_ker P.κ₀ P.κ₀_open).comp (cont_resLe _)
  have h1 : Continuous (P.γ.comp (resQ T.L)) :=
    P.γ_cont.comp (UpperTheory.V.Af.continuous_restrictScalarsHom ℚ T.L Ω)
  show Continuous fun g => P.κ₀.comp (resLe (K_le T)) g * ((P.γ.comp (resQ T.L)) g)⁻¹ ^ (D.e + 4) * P.βL g ^ (D.e % 2)
  exact (h0.mul ((h1.inv).pow _)).mul (hβ.pow _)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

private theorem torsion_combination_smul_eq_zero {M : Type} [AddCommGroup M] (x γ β ε ω : M) (m n k q r : ℕ) (j : ℤ)
    (hx : m • x = 0) (hω : n • ω = 0) (hγ : 2 • γ + ω = ε) (hβ : k • (2 • β + (-(2 * j + 1)) • ε) = 0) :
    (2 * k * m * n) • (x + (2 * q + r + 4) • (-γ) + r • β + (-(r * j - q - 2 : ℤ)) • ε) = 0 := by
  linear_combination (norm := module) (2 * k * n : ℤ) • hx + (k * m * (2 * q + r + 4) : ℤ) • hω - (k * m * n * (2 * q + r + 4) : ℤ) • hγ + (m * n * r : ℤ) • hβ

private theorem mul_aux {M : Type} [CommGroup M] (x γ β ε ω : M) (m n k q r : ℕ) (j : ℤ)
    (hx : x ^ m = 1) (hω : ω ^ n = 1) (hγ : γ ^ 2 * ω = ε) (hβ : (β ^ 2 * ε ^ (-(2 * j + 1))) ^ k = 1) :
    (x * γ⁻¹ ^ (2 * q + r + 4) * β ^ r * ε ^ (-(r * j - q - 2 : ℤ))) ^ (2 * k * m * n) = 1 := by
  have h := torsion_combination_smul_eq_zero (M := Additive M) (Additive.ofMul x) (Additive.ofMul γ) (Additive.ofMul β)
    (Additive.ofMul ε) (Additive.ofMul ω) m n k q r j
    (by rw [← ofMul_pow, hx, ofMul_one]) (by rw [← ofMul_pow, hω, ofMul_one])
    (by rw [← ofMul_pow, ← ofMul_mul, hγ])
    (by rw [← ofMul_zpow, ← ofMul_pow, ← ofMul_mul, ← ofMul_pow, hβ, ofMul_one])
  apply_fun Additive.toMul at h
  simpa [toMul_nsmul, toMul_zsmul, toMul_add, toMul_neg, mul_pow, inv_pow] using h

theorem UpperTheory.V.Ws.Lk.kapCyc :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} (P : Pre T), D.Good → ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃ (a b : ℤ) (k : ℕ), 0 < k ∧ Odd b ∧ ∀ g ∈ Ine (F := T.L) A, (P.κ g * cycBar T.L Ω l g ^ (-a)) ^ k = 1 ∧ (P.βL g ^ 2 * cycBar T.L Ω l g ^ (-b)) ^ k = 1 := by
  intro Ω _ _ _ l _ c D T P hG A hA
  obtain ⟨b, k, hk, hb, hcyc⟩ := P.cyc A hA
  obtain ⟨j, rfl⟩ := hb
  obtain ⟨m, hm, hm1⟩ := P.κ₀_ord
  have hl : l.Prime := Fact.out
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      exact absurd (Nat.coprime_zero_right l |>.1 hm) hl.one_lt.ne'
    · exact h
  have hn0 : 0 < l - 1 := Nat.sub_pos_of_lt hl.one_lt
  refine ⟨((D.e % 2 : ℕ) : ℤ) * j - ((D.e / 2 : ℕ) : ℤ) - 2, 2 * j + 1, 2 * k * m * (l - 1),
    by positivity, ⟨j, rfl⟩, ?_⟩
  intro g hg
  have hω : (toQ D.om (resQ T.L g)) ^ (l - 1) = 1 := by
    rw [show toQ D.om (resQ T.L g) = Units.map (algebraMap c.O (PadicAlgCl l) : c.O →* PadicAlgCl l)
        (D.om (resQ T.L g)) from rfl,
      ← map_pow, ← MonoidHom.pow_apply, hG.om_pow, MonoidHom.one_apply, map_one]
  have hγ : P.γ (resQ T.L g) ^ 2 * toQ D.om (resQ T.L g) = cycBar T.L Ω l g := P.γ_sq _
  have hβ : (P.β (resLe (K_le T) g) ^ 2 * cycBar T.L Ω l g ^ (-(2 * j + 1))) ^ k = 1 :=
    hcyc _ hg
  have hx : P.κ₀ (resLe (K_le T) g) ^ m = 1 := by
    rw [← MonoidHom.pow_apply, hm1, MonoidHom.one_apply]
  have hκ : P.κ g = P.κ₀ (resLe (K_le T) g) * (P.γ (resQ T.L g))⁻¹ ^ (D.e + 4) *
      P.β (resLe (K_le T) g) ^ (D.e % 2) := rfl
  constructor
  · rw [hκ, show D.e + 4 = 2 * (D.e / 2) + D.e % 2 + 4 by omega]
    exact mul_aux _ _ _ _ _ m (l - 1) k (D.e / 2) (D.e % 2) j hx hω hγ hβ
  · show (P.β (resLe (K_le T) g) ^ 2 * cycBar T.L Ω l g ^ (-(2 * j + 1))) ^ (2 * k * m * (l - 1)) = 1
    rw [show 2 * k * m * (l - 1) = k * (2 * m * (l - 1)) by ring, pow_mul, hβ, one_pow]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

attribute [-instance] UpperTheory.V.UnitaryThreeInertia.Coef.isLocalRing in
theorem UpperTheory.V.Ws.Lk.liftO :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l) {Γ : Type} [Group Γ] [TopologicalSpace Γ] (χ : Γ →* (PadicAlgCl l)ˣ), Continuous χ → (∀ g, (χ g : PadicAlgCl l) ∈ c.O) → ∃ χ' : Γ →* c.Oˣ, toQ χ' = χ ∧ (AdicCont (maximalIdeal c.O) fun g => (χ' g : c.O)) ∧ ∀ g, ‖(χ g : PadicAlgCl l) - 1‖ < 1 → residue c.O (χ' g) = 1 := by
  intro l _ c Γ _ _ χ hχ hO
  have hinv : ∀ g, (χ g : PadicAlgCl l) * (χ g⁻¹ : PadicAlgCl l) = 1 := by
    intro g
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have hinv' : ∀ g, (χ g⁻¹ : PadicAlgCl l) * (χ g : PadicAlgCl l) = 1 := by
    intro g
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  let u : Γ → c.Oˣ := fun g =>
    ⟨⟨χ g, hO g⟩, ⟨χ g⁻¹, hO g⁻¹⟩, Subtype.ext (hinv g), Subtype.ext (hinv' g)⟩
  let χ' : Γ →* c.Oˣ :=
    { toFun := u
      map_one' := by
        ext
        simp [u]
      map_mul' := by
        intro a b
        ext
        simp [u] }
  have hval : ∀ g, ((χ' g : c.O) : PadicAlgCl l) = χ g := fun g => rfl
  refine ⟨χ', ?_, ?_, ?_⟩
  · ext g
    rfl
  · rw [(X.So.adicCont l c).2 Γ]
    exact Continuous.subtype_mk (Units.continuous_val.comp hχ) _
  · intro g hg
    rw [← sub_eq_zero, ← map_one (residue c.O), ← map_sub, residue_eq_zero_iff,
      (Fr.sc_norm l c _).2]
    simpa [hval] using hg
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

theorem UpperTheory.V.Ws.Lk.kapUnr :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} (P : Pre T), D.Good → (∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → Ine (F := T.L) A ≤ P.tL.ker) ∧ (∀ A, Raw.Away D.S A → Ine (F := T.L) A ≤ P.κ.ker) ∧ ∃ m : ℕ, l.Coprime m ∧ ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := T.L) A, P.κ g ^ m = 1 := by
  intro Ω _ _ _ l _ c D T P hG
  have hK : ∀ A : ValuationSubring Ω, ∀ g ∈ Ine (F := T.L) A, resLe (K_le T) g ∈ Ine (F := T.K) A :=
    fun A g hg => hg
  have hQ : ∀ A : ValuationSubring Ω, ∀ g ∈ Ine (F := T.L) A, resQ T.L g ∈ Ine (F := ℚ) A :=
    fun A g hg => hg
  have ht : ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := T.L) A,
      P.t (resLe (K_le T) g) = 1 :=
    fun A hA g hg => MonoidHom.mem_ker.1 (P.t_unr A hA (hK A g hg))
  have hb : ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := T.L) A,
      P.β (resLe (K_le T) g) = 1 :=
    fun A hA g hg => MonoidHom.mem_ker.1 (P.β_t (P.t_unr A hA (hK A g hg)))
  have hc : ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := T.L) A,
      P.γ (resQ T.L g) = 1 :=
    fun A hA g hg => MonoidHom.mem_ker.1 (P.γ_ker ((places ℚ Ω l A).2.2.2 hA (hQ A g hg)))
  have hκ : ∀ g, P.κ g = P.κ₀ (resLe (K_le T) g) * (P.γ (resQ T.L g))⁻¹ ^ (D.e + 4) *
      P.β (resLe (K_le T) g) ^ (D.e % 2) := fun g => rfl
  obtain ⟨m, hm, hm1⟩ := P.κ₀_ord
  refine ⟨fun A hA g hg => MonoidHom.mem_ker.2 (ht A hA g hg), ?_, m, hm, ?_⟩
  · intro A hA g hg
    have hl : ¬ A.valuation (l : Ω) < 1 := hA l hG.l_mem
    rw [MonoidHom.mem_ker, hκ, MonoidHom.mem_ker.1 (P.κ₀_unr A hA (hK A g hg)), hc A hl g hg,
      hb A hl g hg]
    simp
  · intro A hA g hg
    have h0 : P.κ₀ (resLe (K_le T) g) ^ m = 1 := by
      rw [← MonoidHom.pow_apply, hm1, MonoidHom.one_apply]
    rw [hκ, hc A hA g hg, hb A hA g hg]
    simp [h0]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

private theorem kapConj_alg {M : Type} [CommGroup M] (k k' y b b' o x p E : M) (e n : ℕ)
    (h0 : k * k' * (o ^ (e + 3) * x * p) = 1) (h1 : y ^ 2 * o = E) (h2 : b * b' = 1) :
    (k * y⁻¹ ^ (e + 4) * b ^ n) * (k' * y⁻¹ ^ (e + 4) * b' ^ n) * (E * o⁻¹ * x * (E ^ e * p)) * E ^ 3 = 1 := by
  subst h1
  apply Additive.ofMul.injective
  have h0' := congrArg Additive.ofMul h0
  have h2' := congrArg Additive.ofMul h2
  simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_one, add_smul, one_smul, neg_smul, smul_add, smul_neg] at h0' h2' ⊢
  have hk : Additive.ofMul k' = -(Additive.ofMul k +
      (e • Additive.ofMul o + 3 • Additive.ofMul o + Additive.ofMul x + Additive.ofMul p)) := by
    rw [eq_neg_iff_add_eq_zero, ← h0']
    abel
  have hb : Additive.ofMul b' = -Additive.ofMul b := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact h2'
  rw [hk, hb]
  simp only [smul_add, smul_neg, neg_add, neg_neg, two_smul]
  abel

theorem UpperTheory.V.Ws.Lk.kapConj :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} (P : Pre T), T.Deep → ∀ σ ∉ T.K.fixingSubgroup, ∀ g g' : G T.L Ω, resQ T.L g' = σ * resQ T.L g * σ⁻¹ → P.κ g * P.κ g' * toQ D.th (resQ T.L g) * cycBar T.L Ω l g ^ 3 = 1 ∧ P.βL g * P.βL g' = 1 ∧ P.tL g * P.tL g' = 1 := by
  intro Ω _ _ _ l _ c D T P hDeep σ hσ g g' hgg
  have hKL := K_le T
  have hFL : T.F ≤ T.L := T.hL ▸ le_sup_left
  have hres : ∀ h : G T.L Ω, resQ T.K (resLe hKL h) = resQ T.L h := fun h => rfl
  have hresF : ∀ h : G T.L Ω, resQ T.F (resLe hFL h) = resQ T.L h := fun h => rfl
  have hss : resQ T.K (resLe hKL g') = σ * resQ T.K (resLe hKL g) * σ⁻¹ := by
    rw [hres, hres]
    exact hgg
  obtain ⟨m, hm, hψ⟩ := hDeep
  have hψg : ∃ m, l.Coprime m ∧ D.ψ (resQ T.K (resLe hKL g)) ^ m = 1 :=
    ⟨m, hm, by rw [hres, ← hresF]; exact hψ _⟩
  have h0 := P.κ₀_conj σ hσ _ _ hss hψg
  obtain ⟨hb, ht⟩ := P.conj σ hσ _ _ hss
  refine ⟨?_, hb, ht⟩
  have hγ : P.γ (resQ T.L g') = P.γ (resQ T.L g) := by
    rw [hgg, map_mul, map_mul, map_inv, mul_comm (P.γ σ), mul_inv_cancel_right]
  have hcyc : cycBar T.L Ω l g = cycBar ℚ Ω l (resQ T.L g) := by
    rfl
  have hchi : ∀ x, toQ (chiO ℚ Ω l c.O) x = cycBar ℚ Ω l x := fun x => by
    rw [← (auChi ℚ Ω c).1]
  have hth : ∀ x, toQ D.th x = toQ (chiO ℚ Ω l c.O) x * (toQ D.om x)⁻¹ * toQ D.ξ x *
      (toQ (chiO ℚ Ω l c.O) x ^ D.e * toQ D.ψ x) := by
    intro x
    simp only [toQ, W.pushCh, Raw.th, Raw.al, Raw.Psi, Chr.Psi, MonoidHom.comp_apply, MonoidHom.mul_apply,
      MonoidHom.inv_apply, map_mul, map_inv]
    rw [show (chiO ℚ Ω l c.O ^ (D.e : ℤ)) x = (chiO ℚ Ω l c.O x) ^ (D.e : ℤ) from rfl, zpow_natCast, map_pow]
  have hk0 : toQ (D.om ^ (D.e + 3) * D.ξ * D.ψ) (resQ T.L g) =
      toQ D.om (resQ T.L g) ^ (D.e + 3) * toQ D.ξ (resQ T.L g) * toQ D.ψ (resQ T.L g) := by
    simp only [toQ, W.pushCh, MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.pow_apply, map_mul, map_pow]
  rw [hres, hk0] at h0
  have h1 := P.γ_sq (resQ T.L g)
  have key := kapConj_alg _ _ _ _ _ _ _ _ _ D.e (D.e % 2) h0 h1 hb
  rw [hth, hchi, hcyc]
  simp only [Pre.κ, Pre.βL, MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.pow_apply, MonoidHom.inv_apply]
  rw [hγ]
  exact key
end
