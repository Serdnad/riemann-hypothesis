module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Topology.Instances.Matrix
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle220
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Unramified.Locus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle380
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralHeckeEigensystemDeligneSerre
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.Noetherian.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle382
public import Mathlib.RingTheory.Ideal.Height
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle383
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle384
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
public import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle381
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ComplexMultiplicationJPremises
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle001
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap

@[expose] public section

section

open ValuativeRel Matrix

theorem GlobalTheory.isOpen_setOf_le_rank_localField : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D]
    [DecidableEq D] (s : ℕ), IsOpen {X : Matrix A D k | s ≤ X.rank} := by
  intro k _ _ _ _ A D _ _ _ _ s
  rw [isOpen_iff_mem_nhds]
  intro X hX
  obtain ⟨H, Q, hHQ⟩ := GlobalTheory.T.matrix_rank_normal_form k A D X
  have hc : Continuous fun Y : Matrix A D k => (H * Y * Q).det :=
    ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_det
  have hopen : IsOpen {Y : Matrix A D k | (H * Y * Q).det ≠ 0} :=
    isOpen_ne_fun hc continuous_const
  filter_upwards [hopen.mem_nhds (by simp [hHQ])] with Y hY
  replace hY : (H * Y * Q).det ≠ 0 := hY
  show s ≤ Y.rank
  refine le_trans hX ?_
  have hu : IsUnit (H * Y * Q) := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hY)
  have hr : (H * Y * Q).rank = X.rank := by
    rw [Matrix.rank_of_isUnit _ hu]; simp
  calc X.rank = (H * Y * Q).rank := hr.symm
    _ ≤ (H * Y).rank := Matrix.rank_mul_le_left _ _
    _ ≤ Y.rank := Matrix.rank_mul_le_right _ _
end

section

open NumberField IsDedekindDomain GlobalTheory.FixNormCls
open scoped Classical nonZeroDivisors

noncomputable section

namespace GlobalTheory.UnitSq

def fixedUnits (E : Type) [Field E] [NumberField E] (τ : E ≃+* E) : Subgroup (𝓞 E)ˣ where
  carrier := {u | τ ((u : 𝓞 E) : E) = ((u : 𝓞 E) : E)}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Units.val_mul, map_mul] at *
    rw [ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    have h1 : ((a⁻¹ : (𝓞 E)ˣ) : 𝓞 E) * (a : 𝓞 E) = 1 := by simp
    have h1' : (((a⁻¹ : (𝓞 E)ˣ) : 𝓞 E) : E) * (((a : 𝓞 E) : E)) = 1 := by
      exact_mod_cast congrArg (fun x : 𝓞 E => (x : E)) h1
    have h2 : (((a⁻¹ : (𝓞 E)ˣ) : 𝓞 E) : E) = (((a : 𝓞 E) : E))⁻¹ :=
      eq_inv_of_mul_eq_one_left h1'
    rw [h2, map_inv₀, ha]

end GlobalTheory.UnitSq
end
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory

theorem mem_prime_sq_of_sq_mem_prime_cube {A : Type} [CommRing A] [IsDedekindDomain A]
    (P : Ideal A) [hP : P.IsPrime] (hP0 : P ≠ ⊥) (Y : A) (h : Y ^ 2 ∈ P ^ 3) : Y ∈ P ^ 2 := by
  have hY : Y ∈ P := hP.mem_of_pow_mem 2 (Ideal.pow_le_self (by norm_num) h)
  have hprime : Prime P := Ideal.prime_of_isPrime hP0 hP
  have hdvd : P ∣ Ideal.span {Y} := Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hY)
  obtain ⟨J, hJ⟩ := hdvd
  have h2 : P ^ 3 ∣ Ideal.span {Y} ^ 2 := by
    rw [Ideal.span_singleton_pow]
    exact Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr h)
  rw [hJ, mul_pow, show P ^ 3 = P ^ 2 * P by ring] at h2
  have hP2 : P ^ 2 ≠ 0 := pow_ne_zero _ hP0
  have h3 : P ∣ J ^ 2 := (mul_dvd_mul_iff_left hP2).mp h2
  have h4 : P ∣ J := hprime.dvd_of_dvd_pow h3
  have h5 : P ^ 2 ∣ Ideal.span {Y} := by
    rw [hJ, sq]; exact mul_dvd_mul_left P h4
  exact (Ideal.span_singleton_le_iff_mem _).mp (Ideal.le_of_dvd h5)

theorem natPrime_not_mem_cube_of_isUnramifiedAt :
    ∀ (p : ℕ) (K H : Type) [Field K] [NumberField K] [Field H] [NumberField H] [Algebra K H] (x : K) (P : Ideal (𝓞 H)) [P.IsPrime], p.Prime → Module.finrank ℚ K = 2 → x ^ 2 = -(p : K) → P ≠ ⊥ → Algebra.IsUnramifiedAt (𝓞 K) P → (p : 𝓞 H) ∉ P ^ 3 := by
  intro p K H _ _ _ _ _ x P _ hp hK hx hP hunr hpP
  have hint : IsIntegral ℤ x := by
    refine ⟨Polynomial.X ^ 2 + Polynomial.C (p : ℤ), ?_, ?_⟩
    · exact Polynomial.monic_X_pow_add_C _ (by norm_num)
    · simp [hx]
  set y : 𝓞 K := ⟨x, hint⟩ with hydef
  have hy : y ^ 2 = -(p : 𝓞 K) := by
    apply RingOfIntegers.coe_injective
    rw [map_pow, map_neg, map_natCast]
    exact hx
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0] at hy
    have : ((p : 𝓞 K)) = 0 := by simpa using hy.symm
    exact hp.ne_zero (by exact_mod_cast this)
  have hprime : (Ideal.span {y}).IsPrime := GlobalTheory.T.isPrime_span_of_sq_eq_neg_prime_quadratic p K y hp hK hy
  set Y : 𝓞 H := algebraMap (𝓞 K) (𝓞 H) y with hYdef
  have hpY : (p : 𝓞 H) = -(Y ^ 2) := by
    rw [hYdef, ← map_pow, hy, map_neg, map_natCast, neg_neg]
  have hY2 : Y ^ 2 ∈ P ^ 3 := by
    have := (P ^ 3).neg_mem_iff.mpr hpP
    rwa [hpY, neg_neg] at this
  have hYP2 : Y ∈ P ^ 2 := mem_prime_sq_of_sq_mem_prime_cube P hP Y hY2
  have hYP : Y ∈ P := Ideal.pow_le_self (by norm_num) hYP2
  have hyU : y ∈ P.under (𝓞 K) := by
    rw [Ideal.under_def, Ideal.mem_comap]; exact hYP
  have hU0 : P.under (𝓞 K) ≠ ⊥ := by
    intro h; rw [h, Ideal.mem_bot] at hyU; exact hy0 hyU
  have hspan : Ideal.span {y} = P.under (𝓞 K) := by
    have hmax : (Ideal.span {y}).IsMaximal :=
      hprime.isMaximal (by simpa [Ideal.span_singleton_eq_bot] using hy0)
    exact hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance)
      ((Ideal.span_singleton_le_iff_mem _).mpr hyU)
  have he : P.ramificationIdx (𝓞 K) = 1 := Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (P.under (𝓞 K)) P hU0] at he
  have hle : Ideal.map (algebraMap (𝓞 K) (𝓞 H)) (P.under (𝓞 K)) ≤ P := Ideal.map_comap_le
  have hne := (Ideal.ramificationIdx'_ne_one_iff hle).not
  apply hne.mp (not_not.mpr he)
  rw [← hspan, Ideal.map_span, Set.image_singleton]
  exact (Ideal.span_singleton_le_iff_mem _).mpr hYP2

end GlobalTheory
end

section


theorem _root_.GlobalTheory.T.exists_integral_hecke_eigensystem_deligne_serre : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (emb : O →+* PadicAlgCl l), Function.Injective emb → (∃ L : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] L ∧ Set.range emb = {x | x ∈ L ∧ ‖x‖ ≤ 1}) → ∀ (I : Type) (M : Type) [AddCommGroup M] [Module O M] [Module (MvPolynomial I O) M] [IsScalarTower O (MvPolynomial I O) M], Module.Finite O M → (∀ (c : O) (x : M), c • x = 0 → c = 0 ∨ x = 0) → ∀ (V : Type) [AddCommGroup V] [Module (PadicAlgCl l) V] (j : M →ₛₗ[emb] V) (Tq : I → V →ₗ[PadicAlgCl l] V), (∀ (n : ℕ) (x : Fin n → M), LinearIndependent O x → LinearIndependent (PadicAlgCl l) fun a => j (x a)) → (∀ i x, j ((MvPolynomial.X i : MvPolynomial I O) • x) = Tq i (j x)) → ∀ (m : Ideal (MvPolynomial I O)), m.IsMaximal → (∀ p : MvPolynomial I O, (∀ x : M, p • x = 0) → p ∈ m) → ∃ θ : I → PadicAlgCl l, (∀ i, ‖θ i‖ ≤ 1) ∧ (∀ p, p ∈ m ↔ ‖MvPolynomial.eval₂ emb θ p‖ < 1) ∧ ∃ v ∈ Submodule.span (PadicAlgCl l) (Set.range j), v ≠ 0 ∧ ∀ i, Tq i v = θ i • v := by
  first | exact @GlobalTheory.DeligneSerre.exists_integral_eigensystem | exact GlobalTheory.DeligneSerre.exists_integral_eigensystem | (intros; apply GlobalTheory.DeligneSerre.exists_integral_eigensystem <;> assumption)
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.exists_finite_padicInt_domain_embedding : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [CommRing C] [IsDomain C] [IsLocalRing C] [IsNoetherianRing C], Finite (ResidueField C) → (p : C) ≠ 0 → (p : C) ∈ maximalIdeal C → (∀ P : Ideal C, P.IsPrime → P ≠ ⊥ → P = maximalIdeal C) → ∃ (D : Type) (_ : CommRing D) (_ : IsDomain D) (_ : Algebra ℤ_[p] D), Module.Finite ℤ_[p] D ∧ ∃ ι : C →+* D, Function.Injective ι := by
  first | exact @GlobalTheory.CompletionEmbed.exists_finite_padicInt_domain | exact GlobalTheory.CompletionEmbed.exists_finite_padicInt_domain | (intros; apply GlobalTheory.CompletionEmbed.exists_finite_padicInt_domain <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.closure_generic_fibre_clopen_split_alt : ∀ (R A : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing A] [Algebra R A], Algebra.Smooth R A → ∀ C C' : Set (PrimeSpectrum A), C ∪ C' = {r | r.asIdeal.comap (algebraMap R A) = ⊥} → Disjoint C (closure C') → Disjoint (closure C) C' → Disjoint (closure C) (closure C') ∧ closure C ∪ closure C' = Set.univ := by
  first | exact @GlobalTheory.closure_generic_fibre_clopen_split | exact GlobalTheory.closure_generic_fibre_clopen_split | (intros; apply GlobalTheory.closure_generic_fibre_clopen_split <;> assumption)
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.surjective_finite_of_unique_embedding_complete_normal : ∀ (B R : Type) [CommRing B] [IsDomain B] [IsLocalRing B] [IsNoetherianRing B] [IsIntegrallyClosed B] [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (ψ : B →+* R), IsAdicComplete (maximalIdeal B) B → Function.Injective ψ → ψ.Finite → (∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] [IsNoetherianRing R'] [IsIntegrallyClosed R'] [CharZero R'], IsAdicComplete (maximalIdeal R') R' → ∀ f g : R →+* R', Function.Injective f → Function.Injective g → IsLocalHom f → IsLocalHom g → f.comp ψ = g.comp ψ → f = g) → Function.Surjective ψ := by
  first | exact @GlobalTheory.DegreeOne.surjective_of_unique_injective_localHom | exact GlobalTheory.DegreeOne.surjective_of_unique_injective_localHom | (intros; apply GlobalTheory.DegreeOne.surjective_of_unique_injective_localHom <;> assumption)
end

section

open IsLocalRing

namespace GlobalTheory.CompleteNakayamaLocal

theorem exists_fg_sup_pow_eq_top {B R : Type} [CommRing B] [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [Algebra B R]
    (hres : Module.Finite B (R ⧸ maximalIdeal R)) (n : ℕ) :
    ∃ P : Submodule B R, P.FG ∧ P ⊔ (maximalIdeal R ^ n).restrictScalars B = ⊤ := by
  obtain ⟨T, hT⟩ := (Module.Finite.fg_top (R := B) (M := R ⧸ maximalIdeal R))
  choose lift hlift using fun x : R ⧸ maximalIdeal R => Ideal.Quotient.mk_surjective x

  have hTop : Submodule.span B (lift '' (T : Set _)) ⊔ (maximalIdeal R).restrictScalars B = ⊤ := by
    rw [eq_top_iff]
    intro r _
    have hr : Ideal.Quotient.mk (maximalIdeal R) r ∈ Submodule.span B (T : Set _) := by
      rw [hT]; trivial
    have hmap : Submodule.span B (T : Set (R ⧸ maximalIdeal R)) =
        (Submodule.span B (lift '' (T : Set _))).map
          (Ideal.Quotient.mkₐ B (maximalIdeal R)).toLinearMap := by
      rw [Submodule.map_span, ← Set.image_comp]
      congr 1
      ext x
      simp [hlift]
    rw [hmap] at hr
    obtain ⟨t, ht, hte⟩ := hr
    have hu : r - t ∈ maximalIdeal R := by
      rw [← Ideal.Quotient.eq]
      simpa using hte.symm
    rw [Submodule.mem_sup]
    exact ⟨t, ht, r - t, hu, by ring⟩
  induction n with
  | zero => exact ⟨⊥, Submodule.fg_bot, by simp⟩
  | succ n ih =>
    obtain ⟨P, hP, hPtop⟩ := ih
    obtain ⟨gens, hgens⟩ := (IsNoetherian.noetherian (maximalIdeal R ^ n) : (maximalIdeal R ^ n).FG)
    let G : Set R := Set.image2 (· * ·) (lift '' (T : Set _)) (gens : Set R)
    have hGf : G.Finite := ((T.finite_toSet.image _).image2 _ gens.finite_toSet)
    refine ⟨P ⊔ Submodule.span B G, hP.sup (Submodule.fg_def.2 ⟨G, hGf, rfl⟩), ?_⟩

    have key : ∀ y ∈ maximalIdeal R ^ n, ∀ r : R,
        r * y ∈ Submodule.span B G ⊔ (maximalIdeal R ^ (n + 1)).restrictScalars B := by
      intro y hy
      rw [← hgens] at hy
      induction hy using Submodule.span_induction with
      | mem g hg =>
        intro r
        have hr : r ∈ (⊤ : Submodule B R) := trivial
        rw [← hTop, Submodule.mem_sup] at hr
        obtain ⟨t, ht, u, hu, rfl⟩ := hr
        rw [add_mul]
        refine Submodule.add_mem_sup ?_ ?_
        · have : t * g ∈ (Submodule.span B (lift '' (T : Set _))).map (LinearMap.mulRight B g) :=
            ⟨t, ht, rfl⟩
          rw [Submodule.map_span] at this
          refine Submodule.span_mono ?_ this
          rintro _ ⟨s, hs, rfl⟩
          exact ⟨s, hs, g, hg, rfl⟩
        · show u * g ∈ maximalIdeal R ^ (n + 1)
          rw [pow_succ']
          exact Ideal.mul_mem_mul hu (hgens ▸ Submodule.subset_span hg)
      | zero => intro r; simp
      | add a b _ _ ha hb => intro r; rw [mul_add]; exact Submodule.add_mem _ (ha r) (hb r)
      | smul s a _ ha => intro r; rw [smul_eq_mul, ← mul_assoc]; exact ha (r * s)
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ (⊤ : Submodule B R) := trivial
    rw [← hPtop, Submodule.mem_sup] at hx
    obtain ⟨p, hp, y, hy, rfl⟩ := hx
    have hy' := key y hy 1
    rw [one_mul, Submodule.mem_sup] at hy'
    obtain ⟨a, ha, c, hc, rfl⟩ := hy'
    rw [Submodule.mem_sup]
    refine ⟨p + a, Submodule.add_mem_sup hp ha, c, hc, by ring⟩

theorem finite_of_maximalIdeal_le_radical : ∀ (B R : Type) [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (ψ : B →+* R),
    IsAdicComplete (maximalIdeal B) B → IsLocalHom ψ →
    maximalIdeal R ≤ ((maximalIdeal B).map ψ).radical → ((residue R).comp ψ).Finite →
    ψ.Finite := by
  intro B R _ _ _ _ _ _ ψ hB hψ hrad hres
  letI : Algebra B R := ψ.toAlgebra
  set J : Ideal R := (maximalIdeal B).map (algebraMap B R) with hJdef
  have hJm : J ≤ maximalIdeal R := by
    refine Ideal.map_le_iff_le_comap.2 fun x hx => ?_
    rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
    exact fun h => (mem_maximalIdeal x).1 hx (isUnit_of_map_unit ψ x h)
  haveI : IsHausdorff J R := ⟨fun x hx => IsHausdorff.haus (I := maximalIdeal R) inferInstance x
    fun n => (hx n).mono (Submodule.smul_mono_left (Ideal.pow_right_mono hJm n))⟩
  obtain ⟨e, he⟩ : ∃ e, maximalIdeal R ^ e ≤ J :=
    Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  have hres' : Module.Finite B (R ⧸ maximalIdeal R) := hres
  obtain ⟨P, hP, hPtop⟩ := exists_fg_sup_pow_eq_top hres' e
  haveI : Module.Finite B (R ⧸ J) := by
    refine ⟨?_⟩
    have : (⊤ : Submodule B (R ⧸ J)) = P.map (Ideal.Quotient.mkₐ B J).toLinearMap := by
      refine le_antisymm ?_ le_top
      rintro z -
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
      have hx : x ∈ (⊤ : Submodule B R) := trivial
      rw [← hPtop, Submodule.mem_sup] at hx
      obtain ⟨p, hp, y, hy, rfl⟩ := hx
      refine ⟨p, hp, ?_⟩
      show Ideal.Quotient.mk J p = Ideal.Quotient.mk J (p + y)
      rw [map_add (f := _), Ideal.Quotient.eq_zero_iff_mem.2 (he hy), add_zero]
    rw [this]
    exact hP.map _
  exact GlobalTheory.FormalIsogeny.finite_of_finite_quotient_map (maximalIdeal B)

end GlobalTheory.CompleteNakayamaLocal
end

section


theorem _root_.GlobalTheory.T.exists_adicCompletion_noetherian_flat_complete : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (I : Ideal B), ∃ (C : Type) (_ : CommRing C) (φ : B →+* C), IsNoetherianRing C ∧ φ.Flat ∧ IsAdicComplete (I.map φ) C ∧ ∀ (m : ℕ) (a : Ideal B), I ^ m ≤ a → (a.map φ).comap φ = a := by
  first | exact @GlobalTheory.AdicPackage.adicCompletion_package | exact GlobalTheory.AdicPackage.adicCompletion_package | (intros; apply GlobalTheory.AdicPackage.adicCompletion_package <;> assumption)
end

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.integralClosure_finiteType_over_adjoin : ∀ (k F K : Type) [Field k] [CharZero k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] [FiniteDimensional F K] (d : ℕ) (u : Fin d → F), AlgebraicIndependent k u → ∀ (A : Subalgebra k F) [IsFractionRing A F], A = Algebra.adjoin k (Set.range u) → ∀ (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → Algebra.FiniteType k B := by
  first | (exact @GlobalTheory.integralClosure_finiteType_of_charZero) | (exact GlobalTheory.integralClosure_finiteType_of_charZero) | (intros; apply GlobalTheory.integralClosure_finiteType_of_charZero  <;> assumption)
end

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.exists_uniformizer_ramification_of_height_one : ∀ (k F K : Type) [Field k] [CharZero k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] [FiniteDimensional F K] (d : ℕ) (u : Fin d → F), AlgebraicIndependent k u → ∀ (A : Subalgebra k F) [IsFractionRing A F], A = Algebra.adjoin k (Set.range u) → ∀ (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → ∀ (p : Ideal A), p.IsPrime → ∀ t : A, Irreducible t → p = Ideal.span {t} → ∀ Q : Ideal B, Q.IsPrime → Q.height = 1 → (∀ a : A, ∀ b : B, (b : K) = algebraMap F K a → (b ∈ Q ↔ a ∈ p)) → ∃ (s : B) (e : ℕ), 1 ≤ e ∧ s ∈ Q ∧ (∀ y ∈ Q, ∃ c r : B, r ∉ Q ∧ r * y = c * s) ∧ (∃ a r : B, a ∉ Q ∧ r ∉ Q ∧ (r : K) * algebraMap F K t = a * s ^ e) := by
  first | (exact @GlobalTheory.integralClosure_height_one_uniformizer_ramification) | (exact GlobalTheory.integralClosure_height_one_uniformizer_ramification) | (intros; apply GlobalTheory.integralClosure_height_one_uniformizer_ramification  <;> assumption)
end

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.mem_heightOne_prime_integralClosure_iff_dvd_irreducible : ∀ (k F K : Type) [Field k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (u : Fin d → F), AlgebraicIndependent k u → ∀ (A : Subalgebra k F) [IsFractionRing A F], A = Algebra.adjoin k (Set.range u) → ∀ (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → ∀ (Q : Ideal B), Q.IsPrime → Q.height = 1 → ∀ (t : A), Irreducible t → (∀ b : B, (b : K) = algebraMap F K t → b ∈ Q) → ∀ (a : A) (b : B), (b : K) = algebraMap F K a → (b ∈ Q ↔ t ∣ a) := by
  first | (exact @GlobalTheory.JacVal.mem_iff_dvd_of_height_one) | (exact GlobalTheory.JacVal.mem_iff_dvd_of_height_one) | (intros; apply GlobalTheory.JacVal.mem_iff_dvd_of_height_one  <;> assumption)
end
