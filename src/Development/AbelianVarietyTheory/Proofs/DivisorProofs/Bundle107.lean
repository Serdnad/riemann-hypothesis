module

public import Mathlib.NumberTheory.NumberField.Basic
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
import Mathlib.RingTheory.PiTensorProduct
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
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

@[expose] public section

section

open scoped TensorProduct Classical

namespace GlobalTheory
namespace ReducedInvolutionNormClass

variable {E : Type} [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E]

theorem numberField_quot (I : Ideal E) [I.IsMaximal] :
    @NumberField (E ⧸ I) (Ideal.Quotient.field I) := by
  letI := Ideal.Quotient.field I
  have hfin : Module.Finite ℚ (E ⧸ I) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℚ I).toLinearMap Ideal.Quotient.mk_surjective
  haveI : CharZero (E ⧸ I) := charZero_of_injective_ringHom (algebraMap ℚ (E ⧸ I)).injective
  exact @NumberField.mk _ _ _ (by
    convert hfin
    exact congrArg (fun A : Algebra ℚ (E ⧸ I) => A.toModule) (Subsingleton.elim _ (Ideal.Quotient.algebra ℚ)))

theorem stable_factor (H : (∀ (K : Type) [Field K] [NumberField K] (τ : K ≃+* K), (∀ x, τ (τ x) = x) → ∀ S : Finset ℕ,
    ∃ M : Finset K, ∀ a : K, a ≠ 0 → τ a = a →
    (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∃ (b x y : K), b ≠ 0 ∧ a = x * (b * τ b) ∧ b * τ b = y * a ∧
      ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : K) * x) ∧ IsIntegral ℤ ((d : K) * y)) →
    ∃ m ∈ M, ∃ e : K, e ≠ 0 ∧ a = e * m * τ e)) (τ : E ≃ₐ[ℚ] E) (hτ : ∀ x, τ (τ x) = x) (S : Finset ℕ)
    (I : Ideal E) [I.IsMaximal] (hI : ∀ x ∈ I, τ x ∈ I) :
    ∃ M : Finset E, ∀ a : E, IsUnit a → τ a = a →
    (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∃ (b x y : E), IsUnit b ∧ a = x * (b * τ b) ∧ b * τ b = y * a ∧
      ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : E) * x) ∧ IsIntegral ℤ ((d : E) * y)) →
    ∃ m ∈ M, ∃ e : E, e ∉ I ∧ a - e * m * τ e ∈ I := by
  letI := Ideal.Quotient.field I
  haveI := numberField_quot I
  have hmap : I = I.map (τ : E ≃+* E) := by
    apply le_antisymm
    · intro x hx
      have : x = (τ : E ≃+* E) (τ x) := (hτ x).symm
      rw [this]; exact Ideal.mem_map_of_mem _ (hI x hx)
    · rw [Ideal.map_le_iff_le_comap]; intro x hx; exact hI x hx
  let τI := Ideal.quotientEquiv I I (τ : E ≃+* E) hmap
  have hτmk : ∀ x, τI (Ideal.Quotient.mk I x) = Ideal.Quotient.mk I (τ x) := fun x => rfl
  have hτI : ∀ z, τI (τI z) = z := by
    intro z; obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [hτmk, hτmk, hτ]
  obtain ⟨M, hM⟩ := H (E ⧸ I) τI hτI S
  let lift : E ⧸ I → E := fun z => Classical.choose (Ideal.Quotient.mk_surjective z)
  have hlift : ∀ z, Ideal.Quotient.mk I (lift z) = z :=
    fun z => Classical.choose_spec (Ideal.Quotient.mk_surjective z)
  refine ⟨M.image lift, fun a ha hτa hyp => ?_⟩
  have ha0 : Ideal.Quotient.mk I a ≠ 0 := (ha.map _).ne_zero
  obtain ⟨m, hm, e', he', hae⟩ := hM (Ideal.Quotient.mk I a) ha0 (by rw [hτmk, hτa]) (by
    intro ℓ hℓ hS
    obtain ⟨b, x, y, hb, h1, h2, d, hd, hx, hy⟩ := hyp ℓ hℓ hS
    refine ⟨Ideal.Quotient.mk I b, Ideal.Quotient.mk I x, Ideal.Quotient.mk I y,
      (hb.map _).ne_zero, ?_, ?_, d, hd, ?_, ?_⟩
    · rw [hτmk, h1, map_mul, map_mul]
    · rw [hτmk, ← map_mul, h2, map_mul]
    · have := hx.map (Ideal.Quotient.mk I).toIntAlgHom
      simp only [map_mul, map_natCast, RingHom.toIntAlgHom_apply] at this
      convert this using 1
      all_goals first | rfl | exact Subsingleton.elim _ _ | (congr; exact Subsingleton.elim _ _)
    · have := hy.map (Ideal.Quotient.mk I).toIntAlgHom
      simp only [map_mul, map_natCast, RingHom.toIntAlgHom_apply] at this
      convert this using 1
      all_goals first | rfl | exact Subsingleton.elim _ _ | (congr; exact Subsingleton.elim _ _))
  obtain ⟨e, rfl⟩ := Ideal.Quotient.mk_surjective e'
  refine ⟨lift m, Finset.mem_image_of_mem _ hm, e, ?_, ?_⟩
  · intro he; exact he' (Ideal.Quotient.eq_zero_iff_mem.2 he)
  · rw [← Ideal.Quotient.eq, map_mul, map_mul, hlift, hae, hτmk]

variable [IsReduced E]

theorem crt (c : MaximalSpectrum E → E) : ∃ u : E, ∀ I : MaximalSpectrum E, u - c I ∈ I.asIdeal := by
  haveI : IsArtinianRing E := IsArtinianRing.of_finite ℚ E
  refine ⟨(IsArtinianRing.equivPi E).symm (fun I => Ideal.Quotient.mk I.asIdeal (c I)), fun I => ?_⟩
  rw [← Ideal.Quotient.eq]
  exact congrFun ((IsArtinianRing.equivPi E).apply_symm_apply
    (fun I => Ideal.Quotient.mk I.asIdeal (c I))) I

theorem eq_zero_of_mem_all (x : E) (h : ∀ I : MaximalSpectrum E, x ∈ I.asIdeal) : x = 0 := by
  haveI : IsArtinianRing E := IsArtinianRing.of_finite ℚ E
  apply (IsArtinianRing.equivPi E).injective
  rw [map_zero]; funext I; exact Ideal.Quotient.eq_zero_iff_mem.2 (h I)

end ReducedInvolutionNormClass


open ReducedInvolutionNormClass in
theorem normClassFinite_of_reduced : (∀ (K : Type) [Field K] [NumberField K] (τ : K ≃+* K), (∀ x, τ (τ x) = x) → ∀ S : Finset ℕ,
    ∃ M : Finset K, ∀ a : K, a ≠ 0 → τ a = a →
    (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∃ (b x y : K), b ≠ 0 ∧ a = x * (b * τ b) ∧ b * τ b = y * a ∧
      ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : K) * x) ∧ IsIntegral ℤ ((d : K) * y)) →
    ∃ m ∈ M, ∃ e : K, e ≠ 0 ∧ a = e * m * τ e) →
  ∀ (E : Type) [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E] [IsReduced E] (τ : E ≃ₐ[ℚ] E),
    (∀ x, τ (τ x) = x) → ∀ S : Finset ℕ, ∃ A : Finset E, ∀ a : E, IsUnit a → τ a = a →
    (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∃ (b x y : E), IsUnit b ∧ a = x * (b * τ b) ∧ b * τ b = y * a ∧
      ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : E) * x) ∧ IsIntegral ℤ ((d : E) * y)) →
    ∃ a₀ ∈ A, ∃ e : Eˣ, a = (e : E) * a₀ * τ e := by
  intro H E _ _ _ _ τ hτ S
  haveI : IsArtinianRing E := IsArtinianRing.of_finite ℚ E
  haveI : Fintype (MaximalSpectrum E) := Fintype.ofFinite _
  let σ : MaximalSpectrum E → MaximalSpectrum E := fun I =>
    ⟨I.asIdeal.comap (τ : E ≃+* E), Ideal.comap_isMaximal_of_surjective _ (τ : E ≃+* E).surjective⟩
  have hσ : ∀ I x, x ∈ (σ I).asIdeal ↔ τ x ∈ I.asIdeal := fun I x => Iff.rfl
  have hσσ : ∀ I, σ (σ I) = I := fun I =>
    MaximalSpectrum.ext (Ideal.ext fun x => by rw [hσ, hσ, hτ])
  have hst : ∀ I, σ I = I → ∀ x ∈ I.asIdeal, τ x ∈ I.asIdeal := by
    intro I h x hx; rw [← hσ, h]; exact hx
  let n := Fintype.equivFin (MaximalSpectrum E)
  let ch : MaximalSpectrum E → Prop := fun I => n I < n (σ I)
  let Mset : MaximalSpectrum E → Finset E := fun I =>
    if h : σ I = I then Classical.choose (stable_factor H τ hτ S I.asIdeal (hst I h)) else {1}
  let F : (MaximalSpectrum E → E) → E := fun f => Classical.choose (crt f)
  have hF : ∀ f I, F f - f I ∈ I.asIdeal := fun f => Classical.choose_spec (crt f)
  refine ⟨(Fintype.piFinset Mset).image F, fun a ha hτa hyp => ?_⟩
  have key : ∀ I, ∃ m ∈ Mset I, ∃ e : E, e ∉ I.asIdeal ∧ (σ I = I → a - e * m * τ e ∈ I.asIdeal) ∧
      (σ I ≠ I → m = 1 ∧ e = if ch I then a else 1) := by
    intro I
    by_cases h : σ I = I
    · obtain ⟨m, hm, e, he, hae⟩ :=
        Classical.choose_spec (stable_factor H τ hτ S I.asIdeal (hst I h)) a ha hτa hyp
      refine ⟨m, by simp only [Mset, dif_pos h]; exact hm, e, he, fun _ => hae, fun h' => absurd h h'⟩
    · refine ⟨1, by simp [Mset, h], if ch I then a else 1, ?_, fun h' => absurd h' h, fun _ => ⟨rfl, rfl⟩⟩
      split_ifs
      · exact fun hmem => I.isMaximal.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem ha)
      · exact fun hmem => I.isMaximal.ne_top ((Ideal.eq_top_iff_one _).2 hmem)
  choose m hm e he hst1 hst2 using key
  obtain ⟨u, hu⟩ := crt e
  have hunit : IsUnit u := by
    by_contra hn
    obtain ⟨J, hJ, huJ⟩ := exists_max_ideal_of_mem_nonunits hn
    apply he ⟨J, hJ⟩
    have := J.sub_mem huJ (hu ⟨J, hJ⟩)
    simpa using this
  refine ⟨F m, Finset.mem_image_of_mem _ (Fintype.mem_piFinset.2 hm), hunit.unit, ?_⟩
  simp only [IsUnit.unit_spec]
  rw [← sub_eq_zero]
  apply eq_zero_of_mem_all
  intro I
  have hu' : ∀ J : MaximalSpectrum E, Ideal.Quotient.mk J.asIdeal u = Ideal.Quotient.mk J.asIdeal (e J) :=
    fun J => Ideal.Quotient.eq.2 (hu J)
  have hF' : Ideal.Quotient.mk I.asIdeal (F m) = Ideal.Quotient.mk I.asIdeal (m I) :=
    Ideal.Quotient.eq.2 (hF m I)
  have hτu : ∀ J, Ideal.Quotient.mk J.asIdeal (τ u) = Ideal.Quotient.mk J.asIdeal (τ (e (σ J))) := by
    intro J; rw [Ideal.Quotient.eq, ← map_sub, ← hσ]; exact hu (σ J)
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_mul, hu', hF', hτu, sub_eq_zero]
  by_cases h : σ I = I
  · rw [h, ← map_mul, ← map_mul, Ideal.Quotient.eq]
    exact hst1 I h
  · obtain ⟨hm1, he1⟩ := hst2 I h
    have hJ : σ (σ I) ≠ σ I := by rw [hσσ]; exact fun h' => h h'.symm
    obtain ⟨_, he2⟩ := hst2 (σ I) hJ
    rw [hm1, he1, he2]
    have hne : n I ≠ n (σ I) := fun h' => h (n.injective h').symm
    by_cases hc : ch I
    · have hc' : ¬ ch (σ I) := by
        show ¬ n (σ I) < n (σ (σ I)); rw [hσσ]; exact not_lt.2 hc.le
      rw [if_pos hc, if_neg hc']
      simp
    · have hc' : ch (σ I) := by
        show n (σ I) < n (σ (σ I)); rw [hσσ]; exact lt_of_le_of_ne (not_lt.1 hc) hne.symm
      rw [if_neg hc, if_pos hc', hτa]
      simp

end GlobalTheory
end

section

open NumberField

namespace GlobalTheory

theorem finrank_dvd_of_ringOfIntegers_to_matrix (E : Type) [Field E] [NumberField E] {r : ℕ}
    (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ) : ∃ s : ℕ, r = s * Module.finrank ℚ E := by
  classical
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 E) (nonZeroDivisors ℤ)) E :=
    IsIntegralClosure.isLocalization ℤ ℚ E (𝓞 E)
  let g : 𝓞 E →+* Matrix (Fin r) (Fin r) ℚ := (Int.castRingHom ℚ).mapMatrix.comp ρ
  let S : Subalgebra ℚ (Matrix (Fin r) (Fin r) ℚ) := Algebra.adjoin ℚ (Set.range g)
  letI : IsMulCommutative S := Algebra.isMulCommutative_adjoin ℚ (by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ _
    change g a * g b = g b * g a
    rw [← map_mul, mul_comm, map_mul])
  open scoped IsMulCommutative in
  letI : CommRing S := inferInstance
  let g₁ : 𝓞 E →+* S := g.codRestrict S (fun a => Algebra.subset_adjoin ⟨a, rfl⟩)
  have hg : ∀ y : Algebra.algebraMapSubmonoid (𝓞 E) (nonZeroDivisors ℤ), IsUnit (g₁ y) := by
    rintro ⟨_, m, hm, rfl⟩
    have hm0 : (m : ℚ) ≠ 0 := by
      exact_mod_cast mem_nonZeroDivisors_iff_ne_zero.mp hm
    have : g₁ (algebraMap ℤ (𝓞 E) m) = algebraMap ℚ S (m : ℚ) := by
      apply Subtype.ext
      simp [g₁, g, map_intCast]
    rw [this]
    exact (IsUnit.mk0 _ hm0).map _
  let ρ' : E →+* Matrix (Fin r) (Fin r) ℚ := S.val.toRingHom.comp (IsLocalization.lift hg)
  letI : Module E (Fin r → ℚ) :=
    Module.compHom (Fin r → ℚ)
      ((Matrix.toLinAlgEquiv' : Matrix (Fin r) (Fin r) ℚ ≃ₐ[ℚ] _).toRingEquiv.toRingHom.comp ρ')
  have hq : ρ'.comp (algebraMap ℚ E) = algebraMap ℚ (Matrix (Fin r) (Fin r) ℚ) := RingHom.ext_rat _ _
  haveI : IsScalarTower ℚ E (Fin r → ℚ) := by
    refine ⟨fun q e v => ?_⟩
    show Matrix.toLin' (ρ' (q • e)) v = q • Matrix.toLin' (ρ' e) v
    rw [Algebra.smul_def, map_mul, ← RingHom.comp_apply, hq, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul, map_smul]
    rfl
  refine ⟨Module.finrank E (Fin r → ℚ), ?_⟩
  have := Module.finrank_mul_finrank ℚ E (Fin r → ℚ)
  rw [Module.finrank_fin_fun] at this
  rw [mul_comm] at this
  exact this.symm

end GlobalTheory
end

section

open scoped TensorProduct

namespace GlobalTheory

theorem exists_order_integers_mul_finite_index (F B : Type) [Field F] [NumberField F] [Ring B]
    [Algebra F B] [Algebra ℚ B] [IsScalarTower ℚ F B] (OB : Subring B) (hfin : Module.Finite ℤ OB)
    (hsat : ∀ b : B, ∃ m : ℕ, 0 < m ∧ (m : B) * b ∈ OB) :
    ∃ Λ : Subring B, OB ≤ Λ ∧ (∀ a : NumberField.RingOfIntegers F, algebraMap F B (a : F) ∈ Λ) ∧
      Module.Finite ℤ Λ ∧ ∃ N : ℕ, 0 < N ∧ ∀ x ∈ Λ, (N : B) * x ∈ OB := by
  classical
  let f : NumberField.RingOfIntegers F →ₐ[ℤ] B :=
    ((algebraMap F B).comp (algebraMap (NumberField.RingOfIntegers F) F)).toIntAlgHom
  let g : OB →ₐ[ℤ] B := OB.subtype.toIntAlgHom
  have hc : ∀ a b, Commute (f a) (g b) := fun a b => Algebra.commutes _ _
  let L := Algebra.TensorProduct.lift f g hc
  have hL : ∀ a b, L (a ⊗ₜ b) = f a * g b := fun a b => Algebra.TensorProduct.lift_tmul f g hc a b

  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ (NumberField.RingOfIntegers F)).FG)
  choose m hm0 hm using fun a : NumberField.RingOfIntegers F => hsat (f a)
  let N : ℕ := ∏ a ∈ s, m a
  have hN0 : 0 < N := Finset.prod_pos fun a _ => hm0 a
  have hnat : ∀ (k : ℕ) (y : B), y ∈ OB → (k : B) * y ∈ OB := fun k y hy =>
    OB.mul_mem (natCast_mem OB k) hy
  let P : Submodule ℤ (NumberField.RingOfIntegers F) :=
    { carrier := {a | (N : B) * f a ∈ OB}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, map_add (f := _), mul_add] at *
        exact OB.add_mem ha hb
      zero_mem' := by simp
      smul_mem' := by
        intro n a ha
        simp only [Set.mem_setOf_eq, map_zsmul, mul_smul_comm] at *
        exact OB.zsmul_mem ha n }
  have hsP : (s : Set (NumberField.RingOfIntegers F)) ⊆ SetLike.coe P := by
    intro a ha
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem m ha
    show (N : B) * f a ∈ OB
    have : (N : B) = (k : B) * (m a : B) := by
      rw [show N = m a * k from hk, Nat.cast_mul, (Nat.cast_commute _ _).eq]
    rw [this, mul_assoc]
    exact hnat k _ (hm a)
  have hP : ∀ a, (N : B) * f a ∈ OB := by
    intro a
    have : a ∈ Submodule.span ℤ (s : Set _) := by rw [hs]; trivial
    exact (Submodule.span_le.mpr hsP) this
  refine ⟨L.toRingHom.range, ?_, ?_, ?_, N, hN0, ?_⟩
  · intro b hb
    refine ⟨1 ⊗ₜ ⟨b, hb⟩, ?_⟩
    show L _ = b
    rw [hL]; simp [f, g]
  · intro a
    refine ⟨a ⊗ₜ 1, ?_⟩
    show L _ = _
    rw [hL]; simp [f, g]
  · haveI : Module.Finite ℤ OB := hfin
    haveI : Module.Finite ℤ (NumberField.RingOfIntegers F ⊗[ℤ] OB) := Module.Finite.tensorProduct _ _ _
    exact Module.Finite.of_surjective (L.toRingHom.rangeRestrict.toIntAlgHom.toLinearMap)
      (RingHom.rangeRestrict_surjective _)
  · rintro x ⟨t, rfl⟩
    show (N : B) * L t ∈ OB
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      rw [hL, ← mul_assoc]
      exact OB.mul_mem (hP a) b.2
    | add t u ht hu =>
      rw [map_add (f := _), mul_add]
      exact OB.add_mem ht hu

end GlobalTheory
end

section

open scoped Matrix
open IntermediateField

namespace GlobalTheory

theorem exists_pow_linearIndependent_of_isFractionRing (O F : Type) [CommRing O] [Field F]
    [NumberField F] [Algebra O F] [IsFractionRing O F] :
    ∃ α : O, LinearIndependent ℚ (fun i : Fin (Module.finrank ℚ F) => algebraMap O F (α ^ (i : ℕ))) := by
  obtain ⟨γ, hγ⟩ := Field.exists_primitive_element ℚ F
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := O) γ
  have hfin : Finite (IntermediateField ℚ F) :=
    Field.finite_intermediateField_of_exists_primitive_element ℚ F ⟨γ, hγ⟩
  obtain ⟨t, t', htt, he⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun t : ℕ => ℚ⟮algebraMap O F x + (t : F) * algebraMap O F y⟯)
  have h1 : algebraMap O F x + (t : F) * algebraMap O F y ∈
      ℚ⟮algebraMap O F x + (t : F) * algebraMap O F y⟯ := mem_adjoin_simple_self _ _
  have h2 : algebraMap O F x + (t' : F) * algebraMap O F y ∈
      ℚ⟮algebraMap O F x + (t : F) * algebraMap O F y⟯ := by
    rw [he]; exact mem_adjoin_simple_self _ _
  set L := ℚ⟮algebraMap O F x + (t : F) * algebraMap O F y⟯ with hL
  have hyL : algebraMap O F y ∈ L := by
    have hd : ((t : F) - t') * algebraMap O F y ∈ L := by
      have := L.sub_mem h1 h2
      convert this using 1; ring
    have htt' : ((t : F) - t') ≠ 0 := sub_ne_zero.2 (by exact_mod_cast htt)
    have hc : ((t : F) - t') ∈ L := L.sub_mem (L.natCast_mem t) (L.natCast_mem t')
    have := L.mul_mem (L.inv_mem hc) hd
    rwa [← mul_assoc, inv_mul_cancel₀ htt', one_mul] at this
  have hxL : algebraMap O F x ∈ L := by
    have := L.sub_mem h1 (L.mul_mem (L.natCast_mem t) hyL)
    simpa using this
  have hγL : γ ∈ L := hxy ▸ L.div_mem hxL hyL
  have htop : L = ⊤ := by
    rw [eq_top_iff, ← hγ, adjoin_simple_le_iff]; exact hγL
  refine ⟨x + t • y, ?_⟩
  have ha : algebraMap O F (x + t • y) = algebraMap O F x + (t : F) * algebraMap O F y := by
    rw [map_add (f := _), map_nsmul, nsmul_eq_mul]
  have hint : IsIntegral ℚ (algebraMap O F (x + t • y)) := Algebra.IsIntegral.isIntegral _
  have hdeg : (minpoly ℚ (algebraMap O F (x + t • y))).natDegree = Module.finrank ℚ F := by
    rw [← adjoin.finrank hint, ha, ← hL, htop, finrank_top']
  have h' := (linearIndependent_pow (K := ℚ) (algebraMap O F (x + t • y))).comp
    (Fin.cast hdeg.symm) (Fin.cast_injective _)
  have hf : (fun i : Fin (Module.finrank ℚ F) => algebraMap O F ((x + t • y) ^ (i : ℕ))) =
      (fun i : Fin (minpoly ℚ (algebraMap O F (x + t • y))).natDegree =>
        algebraMap O F (x + t • y) ^ (i : ℕ)) ∘ Fin.cast hdeg.symm := by
    ext i; simp [map_pow]
  rw [hf]; exact h'

end GlobalTheory
end

section

namespace GlobalTheory.DenominatorExistence

open NumberField

theorem den_exists {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ d : ℕ, 0 < d ∧ IsIntegral ℤ ((d : E) * c) := by
  have hc : IsAlgebraic ℤ c :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic c)
  obtain ⟨y, hy, hint⟩ := hc.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy, ?_⟩
  rcases Int.natAbs_eq y with h | h
  · have h' : (y.natAbs : ℤ) = y := by omega
    have h2 : ((y.natAbs : ℤ) : E) = (y : E) := congrArg _ h'
    rw [Int.cast_natCast] at h2
    rw [h2, ← zsmul_eq_mul]; exact hint
  · have h' : (y.natAbs : ℤ) = -y := by omega
    have h2 : ((y.natAbs : ℤ) : E) = ((-y : ℤ) : E) := congrArg _ h'
    rw [Int.cast_natCast, Int.cast_neg] at h2
    rw [h2, neg_mul, ← zsmul_eq_mul]; exact hint.neg

theorem main {E : Type} [Field E] [NumberField E] {r : ℕ}
    (Λ Λ' : Submodule (RingOfIntegers E) (Fin r → E)) (hfg : Λ'.FG)
    (hspan : Submodule.span E (Λ : Set (Fin r → E)) = ⊤) :
    ∃ n : ℕ, 0 < n ∧ ∀ v ∈ Λ', (n : E) • v ∈ Λ := by

  have key : ∀ v : Fin r → E, ∃ n : ℕ, 0 < n ∧ n • v ∈ Λ := by
    intro v
    have hv : v ∈ Submodule.span E (Λ : Set (Fin r → E)) := by rw [hspan]; trivial
    induction hv using Submodule.span_induction with
    | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
    | zero => exact ⟨1, one_pos, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, hax⟩ := hx
      obtain ⟨b, hb, hby⟩ := hy
      refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
      rw [smul_add]
      refine Λ.add_mem ?_ ?_
      · rw [mul_nsmul]; exact Λ.toAddSubmonoid.nsmul_mem hax b
      · rw [mul_comm, mul_nsmul]; exact Λ.toAddSubmonoid.nsmul_mem hby a
    | smul c x _ hx =>
      obtain ⟨a, ha, hax⟩ := hx
      obtain ⟨d, hd, hdc⟩ := den_exists c
      refine ⟨d * a, Nat.mul_pos hd ha, ?_⟩
      have e1 : (⟨(d : E) * c, hdc⟩ : RingOfIntegers E) • (a • x)
          = ((d : E) * c) • (a • x) := by
        rw [← algebraMap_smul E]; rfl
      have e : (d * a) • (c • x) = (⟨(d : E) * c, hdc⟩ : RingOfIntegers E) • (a • x) := by
        rw [e1, ← Nat.cast_smul_eq_nsmul E, ← Nat.cast_smul_eq_nsmul E, smul_smul, smul_smul]
        congr 1
        push_cast; ring
      rw [e]; exact Λ.smul_mem _ hax
  obtain ⟨s, hs⟩ := hfg
  classical
  choose f hfpos hfmem using key
  refine ⟨∏ x ∈ s, f x, Finset.prod_pos (fun x _ => hfpos x), ?_⟩
  intro v hv
  rw [Nat.cast_smul_eq_nsmul]
  rw [← hs] at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    rw [← Finset.mul_prod_erase s f hx, mul_nsmul]
    exact Λ.toAddSubmonoid.nsmul_mem (hfmem x) _
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact Λ.add_mem hx hy
  | smul o x _ hx => rw [smul_comm]; exact Λ.smul_mem o hx

end GlobalTheory.DenominatorExistence
end

section

open NumberField

namespace GlobalTheory.CMModel

theorem isPrime_span_of_sq_eq_neg_prime :
    ∀ (p : ℕ) (K : Type) [Field K] [NumberField K] (y : 𝓞 K), p.Prime → Module.finrank ℚ K = 2 →
      y ^ 2 = -(p : 𝓞 K) → (Ideal.span {y}).IsPrime := by
  intro p K _ _ y hp hK hy
  have hr : Module.finrank ℤ (𝓞 K) = 2 := by rw [RingOfIntegers.rank, hK]
  have h1 : Ideal.absNorm (Ideal.span {y}) ^ 2 = p ^ 2 := by
    rw [← map_pow, Ideal.span_singleton_pow, hy, Ideal.span_singleton_neg,
      Ideal.absNorm_span_singleton]
    have : (p : 𝓞 K) = algebraMap ℤ (𝓞 K) (p : ℤ) := by simp
    rw [this, Algebra.norm_algebraMap, hr]
    simp [Int.natAbs_pow]
  have h2 : Ideal.absNorm (Ideal.span {y}) = p :=
    Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) h1
  apply Ideal.isPrime_of_irreducible_absNorm
  rw [h2]
  exact (Nat.irreducible_iff_nat_prime p).2 hp

end GlobalTheory.CMModel
end
