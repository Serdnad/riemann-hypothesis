module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Defs
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.RingTheory.Ideal.Defs
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.LocalProperties.FinitePresentation
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
public import Mathlib.Topology.Constructions
public import Mathlib.Order.Int.LeastGreatest
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.Ideal.Lattice

@[expose] public section

section

noncomputable section

namespace GlobalTheory.Cusp.Shear

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {N N' : Subgroup G}
  {V : Type} [AddCommGroup V] [TopologicalSpace V] {s : V → G} {π : N → V}

def prodMap (hle : N' ≤ N) (hs : ∀ v, s v ∈ N) (z : N' × V) : N :=
  ⟨z.1 * s z.2, N.mul_mem (hle z.1.2) (hs z.2)⟩

theorem coe_prodMap (hle : N' ≤ N) (hs : ∀ v, s v ∈ N) (z : N' × V) :
    (prodMap hle hs z : G) = z.1 * s z.2 := rfl

theorem map_inv_of_mul (hπmul : ∀ a b : N, π (a * b) = π a + π b) (a : N) : π a⁻¹ = -π a := by
  have h1 : π 1 = 0 := by simpa using hπmul 1 1
  have := hπmul a a⁻¹
  rw [mul_inv_cancel, h1] at this
  exact (neg_eq_of_add_eq_zero_right this.symm).symm

theorem mul_inv_mem (hs : ∀ v, s v ∈ N) (hπmul : ∀ a b : N, π (a * b) = π a + π b)
    (hπs : ∀ (a : N) (v : V), (a : G) = s v → π a = v) (hker : ∀ a : N, π a = 0 ↔ (a : G) ∈ N') (n : N) :
    (n : G) * (s (π n))⁻¹ ∈ N' := by
  have h := (hker (n * (⟨s (π n), hs _⟩ : N)⁻¹)).1 (by
    rw [hπmul, map_inv_of_mul hπmul, hπs ⟨s (π n), hs _⟩ _ rfl, add_neg_cancel])
  simpa using h

def prodHomeo (hle : N' ≤ N) (hs : ∀ v, s v ∈ N) (hsc : Continuous s) (hπc : Continuous π)
    (hπmul : ∀ a b : N, π (a * b) = π a + π b) (hπs : ∀ (a : N) (v : V), (a : G) = s v → π a = v)
    (hker : ∀ a : N, π a = 0 ↔ (a : G) ∈ N') : N' × V ≃ₜ N where
  toFun := prodMap hle hs
  invFun n := (⟨(n : G) * (s (π n))⁻¹, mul_inv_mem hs hπmul hπs hker n⟩, π n)
  left_inv z := by
    have hv : π (prodMap hle hs z) = z.2 := by
      have e : prodMap hle hs z = ⟨z.1, hle z.1.2⟩ * ⟨s z.2, hs _⟩ := rfl
      rw [e, hπmul, hπs ⟨s z.2, hs _⟩ z.2 rfl, (hker _).2 z.1.2, zero_add]
    refine Prod.ext (Subtype.ext ?_) hv
    simp [hv, coe_prodMap]
  right_inv n := by
    apply Subtype.ext
    simp [coe_prodMap]
  continuous_toFun := by
    unfold prodMap
    fun_prop
  continuous_invFun := by
    refine Continuous.prodMk (Continuous.subtype_mk ?_ _) hπc
    fun_prop

@[simp] theorem prodHomeo_apply (hle : N' ≤ N) (hs : ∀ v, s v ∈ N) (hsc : Continuous s) (hπc : Continuous π)
    (hπmul : ∀ a b : N, π (a * b) = π a + π b) (hπs : ∀ (a : N) (v : V), (a : G) = s v → π a = v)
    (hker : ∀ a : N, π a = 0 ↔ (a : G) ∈ N') (z : N' × V) :
    (prodHomeo hle hs hsc hπc hπmul hπs hker z : G) = z.1 * s z.2 := rfl

end GlobalTheory.Cusp.Shear

end
end

section

open NumberField IsDedekindDomain
open scoped Matrix

namespace GlobalTheory

theorem exists_valuation_bound_of_fg {E : Type} [Field E] [NumberField E]
    (w : HeightOneSpectrum (𝓞 E)) {n : ℕ} {L : Submodule (𝓞 E) (Fin n → E)} (hL : L.FG) :
    ∃ C : WithZero (Multiplicative ℤ), ∀ x ∈ L, ∀ i, w.valuation E (x i) ≤ C := by
  classical
  obtain ⟨s, rfl⟩ := hL
  refine ⟨(s ×ˢ (Finset.univ : Finset (Fin n))).sup fun p => w.valuation E (p.1 p.2), ?_⟩
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    intro i
    exact Finset.le_sup (f := fun p : (Fin n → E) × Fin n => w.valuation E (p.1 p.2))
      (b := (x, i)) (Finset.mem_product.2 ⟨hx, Finset.mem_univ _⟩)
  | zero => intro i; simp
  | add x y _ _ hx hy => intro i; exact Valuation.map_add_le _ (hx i) (hy i)
  | smul a x _ hx =>
    intro i
    rw [Pi.smul_apply, Algebra.smul_def, map_mul]
    exact (mul_le_of_le_one_left' (w.valuation_le_one a)).trans (hx i)

theorem valuation_det_le_pow_of_entry_le {E : Type} [Field E] [NumberField E]
    (w : HeightOneSpectrum (𝓞 E)) {n : ℕ} (X : Matrix (Fin n) (Fin n) E)
    {C : WithZero (Multiplicative ℤ)} (h : ∀ i j, w.valuation E (X i j) ≤ C) :
    w.valuation E X.det ≤ C ^ n := by
  rw [Matrix.det_apply']
  refine Valuation.map_sum_le _ fun σ _ => ?_
  rw [map_mul, map_prod]
  have h1 : w.valuation E ((Equiv.Perm.sign σ : ℤ) : E) ≤ 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  refine (mul_le_of_le_one_left' h1).trans ?_
  calc ∏ i, w.valuation E (X (σ i) i) ≤ ∏ _i : Fin n, C :=
        Finset.prod_le_prod' fun i _ => h _ _
    _ = C ^ n := by simp

theorem exists_det_ne_zero_col_mem_of_span_eq_top {E : Type} [Field E] {n : ℕ}
    {S : Set (Fin n → E)} (hS : Submodule.span E S = ⊤) :
    ∃ X : Matrix (Fin n) (Fin n) E, X.det ≠ 0 ∧ ∀ j, (fun i => X i j) ∈ S := by
  classical
  obtain ⟨t, htS, hspan, hli⟩ := exists_linearIndependent E S
  rw [hS] at hspan
  let b : Module.Basis t E (Fin n → E) := Module.Basis.mk hli (by simp [hspan])
  have hfin : Finite t := Module.Finite.finite_basis b
  have := Fintype.ofFinite t
  have hc : Fintype.card t = n := by
    rw [← Module.finrank_eq_card_basis b]; simp
  let e : t ≃ Fin n := Fintype.equivFinOfCardEq hc
  let b' := b.reindex e
  refine ⟨Matrix.of fun i j => b' j i, ?_, fun j => ?_⟩
  · have hli' : LinearIndependent E (Matrix.of fun i j => b' j i).col := b'.linearIndependent
    have := Matrix.linearIndependent_cols_iff_isUnit.1 hli'
    exact ((Matrix.isUnit_iff_isUnit_det _).1 this).ne_zero
  · have : (fun i => (Matrix.of fun i j => b' j i) i j) = (e.symm j : Fin n → E) := by
      funext i; simp [b', b]
    rw [this]
    exact htS (e.symm j).2

theorem exists_local_basis_of_isLattice (E : Type) [Field E] [NumberField E]
    (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E))
    (hL : L.IsFullLattice E) :
    ∃ X : Matrix (Fin n) (Fin n) E, IsUnit X.det ∧ (∀ j, (fun i => X i j) ∈ L) ∧
      ∀ x ∈ L, ∀ i, w.valuation E ((X⁻¹ *ᵥ x) i) ≤ 1 := by
  classical
  obtain ⟨C, hC⟩ := exists_valuation_bound_of_fg w hL.fg
  obtain ⟨X₀, hX₀, hX₀L⟩ := exists_det_ne_zero_col_mem_of_span_eq_top hL.span_eq_top
  have hbd : ∀ X : Matrix (Fin n) (Fin n) E, (∀ j, (fun i => X i j) ∈ L) →
      w.valuation E X.det ≤ C ^ n := fun X hX =>
    valuation_det_le_pow_of_entry_le w X fun i j => hC _ (hX j) i
  obtain ⟨m, ⟨X, hX, hXL, rfl⟩, hmax⟩ := Int.exists_greatest_of_bdd
    (P := fun m => ∃ X : Matrix (Fin n) (Fin n) E, X.det ≠ 0 ∧ (∀ j, (fun i => X i j) ∈ L) ∧
      WithZero.log (w.valuation E X.det) = m)
    ⟨WithZero.log (C ^ n), by
      rintro _ ⟨X, hX, hXL, rfl⟩
      have h0 : w.valuation E X.det ≠ 0 := by simpa using hX
      have h1 := hbd X hXL
      have h2 : C ^ n ≠ 0 := fun h => h0 (le_antisymm (h ▸ h1) zero_le')
      exact (WithZero.log_le_log h0 h2).2 h1⟩
    ⟨_, X₀, hX₀, hX₀L, rfl⟩
  have h0 : w.valuation E X.det ≠ 0 := by simpa using hX
  refine ⟨X, hX.isUnit, hXL, fun x hx i => ?_⟩
  have hcr : X.det * (X⁻¹ *ᵥ x) i = (X.updateCol i x).det := by
    have := congrFun (Matrix.det_smul_inv_mulVec_eq_cramer X x hX.isUnit) i
    simpa [Matrix.cramer_apply] using this
  have hle : w.valuation E (X.updateCol i x).det ≤ w.valuation E X.det := by
    by_cases hY : (X.updateCol i x).det = 0
    · simp [hY]
    · have h1 : w.valuation E (X.updateCol i x).det ≠ 0 := by simpa using hY
      refine (WithZero.log_le_log h1 h0).1 (hmax _ ⟨_, hY, fun j => ?_, rfl⟩)
      by_cases hj : j = i
      · subst hj
        simpa using hx
      · simpa [Matrix.updateCol_ne hj] using hXL j
  rw [← hcr, map_mul] at hle
  have hpos : 0 < w.valuation E X.det := zero_lt_iff.2 h0
  exact (mul_le_iff_le_one_right hpos).1 hle

end GlobalTheory
end

section

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LocFreeProj

theorem finite_projective_of_locally_free : ∀ (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M], (∀ q : PrimeSpectrum R, ∃ r : R, r ∉ q.asIdeal ∧ ∃ (F : Type) (_ : AddCommGroup F) (_ : Module R F) (_ : Module (Localization.Away r) F) (_ : IsScalarTower R (Localization.Away r) F) (_ : Module.Finite (Localization.Away r) F) (_ : Module.Free (Localization.Away r) F) (ϕ : M →ₗ[R] F), IsLocalizedModule (Submonoid.powers r) ϕ) → Module.Finite R M ∧ Module.Projective R M := by
  intro R _ M _ _ h
  let s : Set R := {r | ∃ (F : Type) (_ : AddCommGroup F) (_ : Module R F)
    (_ : Module (Localization.Away r) F) (_ : IsScalarTower R (Localization.Away r) F)
    (_ : Module.Finite (Localization.Away r) F) (_ : Module.Free (Localization.Away r) F)
    (ϕ : M →ₗ[R] F), IsLocalizedModule (Submonoid.powers r) ϕ}
  have hs : Ideal.span s = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hsm⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨r, hr, hP⟩ := h ⟨m, hm.isPrime⟩
    exact hr (hsm (Ideal.subset_span hP))
  have hg : ∀ g : s, g.1 ∈ s := fun g => g.2
  choose F iA iM iL iT iFin iFree ϕ hϕ using hg
  letI := iA
  letI := iM
  letI := iL
  haveI := iT
  haveI := iFin
  haveI := iFree
  haveI := hϕ
  haveI (g : s) : Module.Flat R (F g) := by
    haveI : Module.Flat R (Localization.Away g.1) :=
      IsLocalization.flat _ (Submonoid.powers g.1)
    exact Module.Flat.trans R (Localization.Away g.1) (F g)
  haveI hfp : Module.FinitePresentation R M :=
    Module.FinitePresentation.of_localizationSpan' s hs (Mₚ := F)
      (Rₚ := fun g : s => Localization.Away g.1) ϕ
      fun _ => Module.finitePresentation_of_projective _ _
  haveI : Module.Flat R M :=
    Module.flat_of_isLocalized_span R M s hs F ϕ fun _ => inferInstance
  exact ⟨inferInstance, Module.Flat.projective_of_finitePresentation⟩

end GlobalTheory.LocFreeProj
end
end

section

universe u

namespace GlobalTheory

theorem idem_retract_coords : ∀ {C : Type} [CommRing C] [IsLocalRing C] (I : Ideal C), I ≠ ⊤ →
  ∀ {W : Type u} [AddCommGroup W] [Module C W] (m : ℕ) (s : W →ₗ[C] (Fin m → C ⧸ I))
  (r : (Fin m → C ⧸ I) →ₗ[C] W), r ∘ₗ s = LinearMap.id →
  ∀ (p : Module.End C W), p * p = p →
  ∃ (n : ℕ) (b : Fin n → W) (f : Fin n → W →ₗ[C] C ⧸ I),
    (∀ k, b k ∈ LinearMap.range p) ∧ (∀ k w, f k (p w) = f k w) ∧
    (∀ j k, f j (b k) = if j = k then 1 else 0) ∧
    (∀ w ∈ LinearMap.range p, (∀ k, f k w = 0) → w = 0) := by
  intro C _ _ I hI W _ _ m s r hrs p hp
  haveI : Nontrivial (C ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  haveI : IsLocalRing (C ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hrs' : ∀ w, r (s w) = w := fun w => by simpa using LinearMap.congr_fun hrs w
  have hp' : ∀ w, p (p w) = p w := fun w => by simpa [Module.End.mul_apply] using LinearMap.congr_fun hp w
  let q0 : (Fin m → C ⧸ I) →ₗ[C] (Fin m → C ⧸ I) := s ∘ₗ p ∘ₗ r
  let q : (Fin m → C ⧸ I) →ₗ[C ⧸ I] (Fin m → C ⧸ I) :=
    q0.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
  have hq : ∀ x, q x = s (p (r x)) := fun x => rfl
  have hqq : ∀ x, q (q x) = q x := by
    intro x; simp only [hq, hrs', hp']
  let P := LinearMap.range q
  let π : (Fin m → C ⧸ I) →ₗ[C ⧸ I] P :=
    LinearMap.codRestrict P q (fun x => LinearMap.mem_range_self q x)
  have hπι : π ∘ₗ P.subtype = LinearMap.id := by
    ext ⟨x, y, rfl⟩
    simp [π, hqq]
  haveI : Module.Projective (C ⧸ I) P := Module.Projective.of_split P.subtype π hπι
  haveI : Module.Finite (C ⧸ I) P := Module.Finite.of_surjective π (by
    intro y; exact ⟨y, by simpa using LinearMap.congr_fun hπι y⟩)
  haveI : Module.FinitePresentation (C ⧸ I) P := Module.finitePresentation_of_projective _ _
  haveI : Module.Free (C ⧸ I) P := Module.free_of_flat_of_isLocalRing
  let β := Module.finBasis (C ⧸ I) P
  have mem : ∀ w, s (p w) ∈ P := fun w => ⟨s w, by simp [hq, hrs']⟩
  let f : Fin (Module.finrank (C ⧸ I) P) → W →ₗ[C] C ⧸ I := fun k =>
    { toFun := fun w => β.coord k ⟨s (p w), mem w⟩
      map_add' := by
        intro a c
        rw [← map_add (f := _)]; congr 1; ext1; simp
      map_smul' := by
        intro c w
        have e : (⟨s (p (c • w)), mem _⟩ : P) = (Ideal.Quotient.mk I c) • ⟨s (p w), mem w⟩ := by
          ext1
          funext i
          simp [Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
        show β.coord k ⟨s (p (c • w)), mem _⟩ = _
        rw [e, map_smul, RingHom.id_apply, smul_eq_mul, Algebra.smul_def,
          Ideal.Quotient.algebraMap_eq] }
  have hf : ∀ k w, f k w = β.coord k ⟨s (p w), mem w⟩ := fun _ _ => rfl
  refine ⟨_, fun k => r (β k), f, ?_, ?_, ?_, ?_⟩
  · intro k
    obtain ⟨x, hx⟩ := (β k).2
    refine ⟨r x, ?_⟩
    show p (r x) = r ((β k : P) : Fin m → C ⧸ I)
    rw [← hx, hq, hrs']
  · intro k w
    rw [hf, hf]
    congr 1
    ext1
    simp [hp']
  · intro j k
    rw [hf]
    have e : (⟨s (p (r (β k))), mem _⟩ : P) = β k := by
      ext1
      show s (p (r ((β k : P) : Fin m → C ⧸ I))) = ((β k : P) : Fin m → C ⧸ I)
      obtain ⟨x, hx⟩ := (β k).2
      rw [← hq, ← hx, hqq]
    rw [e, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    simp [eq_comm]
  · rintro w ⟨y, rfl⟩ h0
    have e : (⟨s (p (p y)), mem _⟩ : P) = 0 := by
      apply β.forall_coord_eq_zero_iff.mp
      intro k; rw [← hf]; exact h0 k
    have e2 : s (p (p y)) = 0 := congrArg Subtype.val e
    rw [← hrs' (p y), ← hp' y, e2, map_zero]

end GlobalTheory
end

section

open scoped TensorProduct
universe u

namespace GlobalTheory

theorem finrank_quot_one_sub_idem_eq_mul : ∀ (k : Type) [Field k] (A : Type) [CommRing A] [Algebra k A] [FiniteDimensional k A] (φ : A →ₐ[k] k) (e : A), IsIdempotentElem e → φ e = 1 → (∀ a, φ a = 0 → IsNilpotent (e * a)) → ∀ (H : Type u) [AddCommGroup H] [Module A H] [Module k H] [IsScalarTower k A H] [FiniteDimensional k H] [Module.Projective A H], Module.finrank k (H ⧸ (Ideal.span {1 - e} • ⊤ : Submodule A H)) = Module.finrank k (H ⧸ (RingHom.ker φ • ⊤ : Submodule A H)) * Module.finrank k (A ⧸ Ideal.span {1 - e}) := by
  intro k _ A _ _ _ φ e he hφe hnil H _ _ _ _ _ _
  have : Module.Finite A H := Module.Finite.of_restrictScalars_finite k A H
  set I : Ideal A := Ideal.span {1 - e} with hI
  have hIφ : ∀ a ∈ I, φ a = 0 := by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    simp [hφe]
  have hItop : I ≠ ⊤ := by
    intro h
    have := hIφ 1 (h ▸ Submodule.mem_top)
    simp at this
  let B := A ⧸ I
  have : Nontrivial B := Ideal.Quotient.nontrivial_iff.mpr hItop
  have hloc : IsLocalRing B := by
    apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
    have key : ∀ x : A, φ x ≠ 0 → IsUnit (Ideal.Quotient.mk I x) := by
      intro x hx
      have he1 : Ideal.Quotient.mk I e = 1 := by
        rw [eq_comm, ← sub_eq_zero, ← map_one (Ideal.Quotient.mk I), ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.subset_span rfl
      set a := x - algebraMap k A (φ x) with ha
      have hφa : φ a = 0 := by simp [ha]
      have hxa : x = algebraMap k A (φ x) + a := by simp [ha]
      rw [hxa, map_add (f := _)]
      have hn : IsNilpotent (Ideal.Quotient.mk I a) := by
        have : Ideal.Quotient.mk I a = Ideal.Quotient.mk I (e * a) := by rw [map_mul, he1, one_mul]
        rw [this]; exact (hnil a hφa).map _
      apply hn.isUnit_add_left_of_commute _ (Commute.all _ _)
      have : IsUnit (algebraMap k B (φ x)) := (isUnit_iff_ne_zero.mpr hx).map _
      simpa [Ideal.Quotient.mk_algebraMap] using this
    intro b
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective b
    by_cases hx : φ x = 0
    · right
      rw [← map_one (Ideal.Quotient.mk I), ← map_sub]
      exact key _ (by simp [hx])
    · left; exact key x hx
  let T := B ⊗[A] H
  have : Module.Free B T := Module.free_of_flat_of_isLocalRing

  have h3 : Module.finrank k (H ⧸ (I • ⊤ : Submodule A H)) = Module.finrank B T * Module.finrank k B := by
    let b := Module.Free.chooseBasis B T
    let e1 : T ≃ₗ[A] H ⧸ (I • ⊤ : Submodule A H) := TensorProduct.quotTensorEquivQuotSMul H I
    let e3 : (H ⧸ (I • ⊤ : Submodule A H)) ≃ₗ[A] (Module.Free.ChooseBasisIndex B T → B) :=
      e1.symm.trans (b.equivFun.restrictScalars A)
    rw [(e3.restrictScalars k).finrank_eq, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ,
      smul_eq_mul, Module.finrank_eq_card_chooseBasisIndex (R := B) (M := T)]
  have h4 : Module.finrank k (H ⧸ (RingHom.ker φ • ⊤ : Submodule A H)) = Module.finrank B T := by
    have hsurj : Function.Surjective φ := fun c => ⟨algebraMap k A c, φ.commutes c⟩
    let φB : B →ₐ[k] k := Ideal.Quotient.liftₐ I φ hIφ
    letI : Algebra A k := φ.toRingHom.toAlgebra
    letI : Algebra B k := φB.toRingHom.toAlgebra
    haveI : IsScalarTower A B k := IsScalarTower.of_algebraMap_eq (fun x => rfl)
    haveI : IsScalarTower k A k := IsScalarTower.of_algebraMap_eq (fun c => (φ.commutes c).symm)
    let f := Ideal.quotientKerAlgEquivOfSurjective hsurj
    let g : (A ⧸ RingHom.ker φ) ≃ₗ[A] k :=
      { f.toLinearEquiv with
        map_smul' := by
          intro a x
          obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
          change f (Ideal.Quotient.mk _ (a * y)) = φ a * f (Ideal.Quotient.mk _ y)
          simp [f, Ideal.quotientKerAlgEquivOfSurjective_apply] }
    let e6 : (k ⊗[A] H) ≃ₗ[A] H ⧸ (RingHom.ker φ • ⊤ : Submodule A H) :=
      (LinearEquiv.rTensor H g.symm).trans (TensorProduct.quotTensorEquivQuotSMul H (RingHom.ker φ))
    rw [← (e6.restrictScalars k).finrank_eq,
      ← (TensorProduct.AlgebraTensorModule.cancelBaseChange A B k k H).finrank_eq,
      Module.finrank_baseChange]
  rw [h3, h4]

end GlobalTheory
end

section

universe u_1

namespace GlobalTheory.CoprimeNatNotMem

theorem natCast_not_mem_of_coprime {Rg : Type u_1} [CommRing Rg] {P : Ideal Rg} (hP : P ≠ ⊤)
    {p n : ℕ} (h : Nat.Coprime p n) (hp : (p : Rg) ∈ P) : (n : Rg) ∉ P := by
  intro hn

  obtain ⟨u, v, huv⟩ : IsCoprime (p : Rg) (n : Rg) := by
    have hz : IsCoprime (p : ℤ) (n : ℤ) := Nat.isCoprime_iff_coprime.mpr h
    simpa using hz.map (Int.castRingHom Rg)
  apply hP
  rw [Ideal.eq_top_iff_one, ← huv]
  exact P.add_mem (P.mul_mem_left u hp) (P.mul_mem_left v hn)

end GlobalTheory.CoprimeNatNotMem
end
