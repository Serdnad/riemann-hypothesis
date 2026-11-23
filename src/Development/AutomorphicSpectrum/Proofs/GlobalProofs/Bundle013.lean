module

public import Formalism.RealPlaceAnalysis.SmoothOnGVIff
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.Bundle001
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle012
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle002
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.VanishingIdealSmoothAgreesOff
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
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.ConjugateSelfDual.Bundle001
import ReciprocityTheory.GaloisValuations.GlobalA
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle001

@[expose] public section

section

open Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.JStable


open Module in
theorem exists_adapted_onb {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : Submodule ℂ (EuclideanSpace ℂ ι)) :
    ∃ (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι)) (T : Set ι),
      W = Submodule.span ℂ (b '' T) := by
  classical
  let v : Set (EuclideanSpace ℂ ι) := Set.range (fun i => ((stdOrthonormalBasis ℂ W i : W) : EuclideanSpace ℂ ι))
  have hon : Orthonormal ℂ (fun i => ((stdOrthonormalBasis ℂ W i : W) : EuclideanSpace ℂ ι)) :=
    (stdOrthonormalBasis ℂ W).orthonormal.comp_linearIsometry W.subtypeₗᵢ
  have hv : Orthonormal ℂ ((↑) : v → EuclideanSpace ℂ ι) :=
    (orthonormal_subtype_range hon.linearIndependent.injective).2 hon
  obtain ⟨u, bu, hvu, hbu⟩ := hv.exists_orthonormalBasis_extension
  have hcard : Fintype.card u = Fintype.card ι :=
    (Module.finrank_eq_card_basis bu.toBasis).symm.trans finrank_euclideanSpace
  let e : u ≃ ι := Fintype.equivOfCardEq hcard
  refine ⟨bu.reindex e, e '' {x | (x : EuclideanSpace ℂ ι) ∈ v}, ?_⟩
  have himg : (bu.reindex e) '' (e '' {x | (x : EuclideanSpace ℂ ι) ∈ v}) = v := by
    rw [Set.image_image]
    ext y
    simp only [OrthonormalBasis.reindex_apply, Equiv.symm_apply_apply, hbu, Set.mem_image,
      Set.mem_ofPred_eq]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      exact ⟨⟨y, hvu hy⟩, hy, rfl⟩
  rw [himg]
  have hr : W.subtype '' Set.range (stdOrthonormalBasis ℂ W) = v := (Set.range_comp _ _).symm
  rw [← hr, Submodule.span_image, ← (stdOrthonormalBasis ℂ W).coe_toBasis,
    (stdOrthonormalBasis ℂ W).toBasis.span_eq, Submodule.map_subtype_top]

variable {n : ℕ} (ε : Fin n → Bool)

def ext0 (s : Bool) : EuclideanSpace ℂ {i : Fin n // ε i = s} →ₗ[ℂ] (Fin n → ℂ) where
  toFun x a := if h : ε a = s then x ⟨a, h⟩ else 0
  map_add' x y := by
    funext a
    by_cases h : ε a = s <;> simp [h]
  map_smul' c x := by
    funext a
    by_cases h : ε a = s <;> simp [h]

def res0 (s : Bool) (v : Fin n → ℂ) : EuclideanSpace ℂ {i : Fin n // ε i = s} :=
  WithLp.toLp 2 fun i => v i

lemma extendByZero_apply_of_ne {s : Bool} (x : EuclideanSpace ℂ {i : Fin n // ε i = s}) {a : Fin n}
    (h : ε a ≠ s) : ext0 ε s x a = 0 := by
  simp only [ext0, LinearMap.coe_mk, AddHom.coe_mk, dif_neg h]

lemma extendByZero_restrict_eigen_projection (s : Bool) (v : Fin n → ℂ) :
    ext0 ε s (res0 ε s v) =
      (1 / 2 : ℂ) • (v + (if s then (1 : ℂ) else -1) • (Formalism.REAL.Jm ε *ᵥ v)) := by
  funext a
  have hJ : (Formalism.REAL.Jm ε *ᵥ v) a = (if ε a then 1 else -1) * v a := by
    simp [Formalism.REAL.Jm, Matrix.mulVec_diagonal]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hJ, ext0, LinearMap.coe_mk, AddHom.coe_mk, res0]
  cases s <;> cases h : ε a <;> simp <;> ring

lemma eq_extendByZero_restrict_sum (v : Fin n → ℂ) :
    v = ext0 ε true (res0 ε true v) + ext0 ε false (res0 ε false v) := by
  funext a
  simp only [Pi.add_apply, ext0, LinearMap.coe_mk, AddHom.coe_mk, res0]
  cases h : ε a <;> simp

lemma sum_extendByZero_fin_eq_sum_of_eq (s : Bool) (x y : EuclideanSpace ℂ {i : Fin n // ε i = s}) :
    ∑ a, star (ext0 ε s x a) * ext0 ε s y a = inner ℂ x y := by
  classical
  rw [← Fintype.sum_subtype_add_sum_subtype (fun a => ε a = s)
    (fun a => star (ext0 ε s x a) * ext0 ε s y a)]
  have h2 : ∑ a : {a // ¬ ε a = s}, star (ext0 ε s x a) * ext0 ε s y a = 0 :=
    Finset.sum_eq_zero (fun a _ => by rw [extendByZero_apply_of_ne ε x a.2, star_zero, zero_mul])
  rw [h2, add_zero, PiLp.inner_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hx : ∀ z : EuclideanSpace ℂ {i : Fin n // ε i = s}, ext0 ε s z i.1 = z i := by
    intro z
    simp only [ext0, LinearMap.coe_mk, AddHom.coe_mk, dif_pos i.2]
  rw [hx x, hx y]
  simp [mul_comm]

theorem exists_KG_coordinate (W : Submodule ℂ (Fin n → ℂ))
    (hW : ∀ v ∈ W, Formalism.REAL.Jm ε *ᵥ v ∈ W) :
    ∃ (k : Formalism.REAL.KG ε) (S : Set (Fin n)),
      W = (Submodule.span ℂ (Set.range fun j : S => (Pi.single (j : Fin n) (1 : ℂ) : Fin n → ℂ))).map
        (Formalism.REAL.toMK k).mulVecLin := by
  classical
  choose b T hT using fun s : Bool => exists_adapted_onb (W.comap (ext0 ε s))
  have hres : ∀ (s : Bool) (v : Fin n → ℂ), v ∈ W → res0 ε s v ∈ W.comap (ext0 ε s) := by
    intro s v hv
    rw [Submodule.mem_comap, extendByZero_restrict_eigen_projection]
    exact W.smul_mem _ (W.add_mem hv (W.smul_mem _ (hW v hv)))
  have hdecomp : W = (W.comap (ext0 ε true)).map (ext0 ε true) ⊔
      (W.comap (ext0 ε false)).map (ext0 ε false) := by
    refine le_antisymm (fun v hv => ?_) (sup_le (Submodule.map_le_iff_le_comap.2 le_rfl)
      (Submodule.map_le_iff_le_comap.2 le_rfl))
    rw [eq_extendByZero_restrict_sum ε v]
    exact Submodule.add_mem_sup (Submodule.mem_map_of_mem (hres true v hv))
      (Submodule.mem_map_of_mem (hres false v hv))
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin n) (Fin n) ℂ,
      ∀ i j, M i j = ext0 ε (ε j) (b (ε j) ⟨j, rfl⟩) i :=
    ⟨Matrix.of fun i j => ext0 ε (ε j) (b (ε j) ⟨j, rfl⟩) i, fun _ _ => rfl⟩
  have hcol : ∀ (s : Bool) (i' : {i : Fin n // ε i = s}) (a : Fin n),
      M a i'.1 = ext0 ε s (b s i') a := by
    rintro s ⟨j, rfl⟩ a
    exact hM a j
  have hMM : Mᴴ * M = 1 := by
    ext j l
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
    by_cases hjl : ε j = ε l
    · have h1 : ∀ a, M a j = ext0 ε (ε j) (b (ε j) ⟨j, rfl⟩) a := fun a => hcol (ε j) ⟨j, rfl⟩ a
      have h2 : ∀ a, M a l = ext0 ε (ε j) (b (ε j) ⟨l, hjl.symm⟩) a :=
        fun a => hcol (ε j) ⟨l, hjl.symm⟩ a
      simp only [h1, h2]
      rw [sum_extendByZero_fin_eq_sum_of_eq, orthonormal_iff_ite.1 (b (ε j)).orthonormal]
      simp only [Subtype.mk.injEq]
    · have hne : j ≠ l := fun h => hjl (h ▸ rfl)
      rw [if_neg hne]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      by_cases hi : ε i = ε j
      · rw [hM i l, extendByZero_apply_of_ne ε _ (fun h => hjl (hi.symm.trans h)), mul_zero]
      · rw [hM i j, extendByZero_apply_of_ne ε _ hi, star_zero, zero_mul]
  have hMM' : M * Mᴴ = 1 := mul_eq_one_comm.1 hMM
  have hJ : M * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * M := by
    have hJd : Formalism.REAL.Jm ε = Matrix.diagonal (fun a => if ε a then (1 : ℂ) else -1) := rfl
    ext i j
    rw [hJd, Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hi : ε i = ε j
    · simp only [hi]
      ring
    · rw [hM i j, extendByZero_apply_of_ne ε _ hi]
      ring
  have hunit : M ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    exact hMM
  let u : (Matrix (Fin n) (Fin n) ℂ)ˣ := ⟨M, Mᴴ, hMM', hMM⟩
  have hUJ : u ∈ Formalism.REAL.UJ ε := by
    show Mᴴ * Formalism.REAL.Jm ε * M = Formalism.REAL.Jm ε
    rw [Matrix.mul_assoc, ← hJ, ← Matrix.mul_assoc, hMM, Matrix.one_mul]
  let gu : Formalism.REAL.UJ ε := ⟨u, hUJ⟩
  have hK : M ∈ Formalism.REAL.Kset ε := ⟨hunit, hJ⟩
  let k : Formalism.REAL.KG ε := ⟨gu, (Formalism.REAL.mem_KG ε gu).2 hK⟩
  let S : Set (Fin n) := {j | (⟨j, rfl⟩ : {i : Fin n // ε i = ε j}) ∈ T (ε j)}
  refine ⟨k, S, ?_⟩
  change W = (Submodule.span ℂ (Set.range fun j : S => (Pi.single (j : Fin n) (1 : ℂ) : Fin n → ℂ))).map
    M.mulVecLin
  have hMcol : ∀ (s : Bool) (i' : {i : Fin n // ε i = s}),
      M *ᵥ Pi.single i'.1 1 = ext0 ε s (b s i') := by
    intro s i'
    funext a
    rw [Matrix.mulVec_single_one, Matrix.col_apply, hcol s i' a]
  have hmemS : ∀ (s : Bool) (i' : {i : Fin n // ε i = s}), i' ∈ T s → i'.1 ∈ S := by
    rintro s ⟨j, rfl⟩ hi'
    exact hi'
  have hset : ⇑(ext0 ε true) '' (⇑(b true) '' T true) ∪ ⇑(ext0 ε false) '' (⇑(b false) '' T false) =
      Set.range (⇑M.mulVecLin ∘ fun j : S => (Pi.single (j : Fin n) (1 : ℂ) : Fin n → ℂ)) := by
    ext x
    simp only [Set.mem_union, Set.mem_image, Set.mem_range, Function.comp_apply,
      Matrix.mulVecLin_apply]
    constructor
    · rintro (⟨y, ⟨i', hi', rfl⟩, rfl⟩ | ⟨y, ⟨i', hi', rfl⟩, rfl⟩)
      · exact ⟨⟨i'.1, hmemS true i' hi'⟩, hMcol true i'⟩
      · exact ⟨⟨i'.1, hmemS false i' hi'⟩, hMcol false i'⟩
    · rintro ⟨⟨j, hj⟩, rfl⟩
      have htr : ∀ (s : Bool) (h : ε j = s), (⟨j, h⟩ : {i : Fin n // ε i = s}) ∈ T s := by
        rintro s rfl
        exact hj
      have hback : ∀ (s : Bool) (i' : {i : Fin n // ε i = s}), i' ∈ T s →
          ∃ y, (∃ a ∈ T s, b s a = y) ∧ ext0 ε s y = M *ᵥ Pi.single i'.1 1 :=
        fun s i' hi' => ⟨b s i', ⟨i', hi', rfl⟩, (hMcol s i').symm⟩
      rcases Bool.eq_false_or_eq_true (ε j) with h | h
      · exact Or.inl (hback _ ⟨j, h⟩ (htr _ h))
      · exact Or.inr (hback _ ⟨j, h⟩ (htr _ h))
  conv_lhs => rw [hdecomp, hT true, hT false]
  rw [Submodule.map_span, Submodule.map_span, Submodule.map_span, ← Submodule.span_union, hset,
    Set.range_comp]

end GlobalTheory.CompanionTheory.JStable
end
end

section

@[expose] public section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual

namespace GlobalTheory.CompanionTheory.HermiteMinkowski

noncomputable def bound {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) : ℕ :=
  (discr F).natAbs * ∏ v ∈ S, v.asIdeal.absNorm

theorem bound_ne_zero {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) : bound S ≠ 0 := by
  refine mul_ne_zero (Int.natAbs_ne_zero.mpr (discr_ne_zero F)) ?_
  refine Finset.prod_ne_zero_iff.mpr fun v _ => ?_
  rw [Ne, Ideal.absNorm_eq_zero_iff]
  exact v.ne_bot

theorem natAbs_discr_dvd {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hE : ∀ v ∉ S, Algebra.IsUnramifiedIn (𝓞 E) v.asIdeal) :
    (discr E).natAbs ∣ bound S ^ (Module.finrank ℚ E * Module.finrank ℚ E) := by
  have hdvd := GlobalTheory.T.different_dvd_ramified_prime_power E (bound S) (bound_ne_zero S) fun P hP hP0 hPd => by
    haveI := hP
    exact GlobalTheory.T.ramified_prime_contains_discriminant F E S hE P hP0 hPd
  have h := map_dvd Ideal.absNorm hdvd
  rw [absNorm_differentIdeal E (𝓞 E)] at h
  have hr : ((bound S : 𝓞 E)) ^ (Module.finrank ℚ E) =
      algebraMap ℤ (𝓞 E) (((bound S : ℕ) : ℤ) ^ (Module.finrank ℚ E)) := by
    simp
  rw [Ideal.absNorm_span_singleton, hr, Algebra.norm_algebraMap, RingOfIntegers.rank,
    Int.natAbs_pow, Int.natAbs_pow, Int.natAbs_natCast, ← pow_mul] at h
  exact h

end GlobalTheory.CompanionTheory.HermiteMinkowski

open GlobalTheory.CompanionTheory.HermiteMinkowski in
theorem GlobalTheory.CompanionTheory.HermiteMinkowski.finite_unramified_bounded_degree :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
      (S : Finset (HeightOneSpectrum (𝓞 F))) (N : ℕ),
      {E : IntermediateField F Ω | FiniteDimensional F E ∧
        IsUnramifiedOutside (S : Set (HeightOneSpectrum (𝓞 F))) E ∧
        Module.finrank F E ≤ N}.Finite := by
  intro F Ω _ _ _ _ _ S N
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  set n := Module.finrank ℚ F * N with hn
  set M : ℕ := bound S ^ (n * n) with hM
  have hfin := (NumberField.finite_of_discr_bdd Ω M).image Subtype.val
  have hinj : Function.Injective (fun E : IntermediateField F Ω => E.restrictScalars ℚ) :=
    IntermediateField.restrictScalars_injective ℚ
  refine (hfin.preimage hinj.injOn).subset ?_
  rintro E ⟨hfd, hun, hdeg⟩
  haveI := hfd
  haveI : NumberField E := NumberField.of_module_finite F E
  let e : (E.restrictScalars ℚ) ≃ₐ[ℚ] E := (RingEquiv.refl E : E ≃+* E).toRatAlgEquiv
  haveI hfd' : FiniteDimensional ℚ (E.restrictScalars ℚ) :=
    e.toLinearEquiv.symm.finiteDimensional
  refine ⟨⟨E.restrictScalars ℚ, hfd'⟩, ?_, rfl⟩
  haveI : NumberField (E.restrictScalars ℚ) := @NumberField.mk _ _ inferInstance hfd'
  show |discr (E.restrictScalars ℚ)| ≤ (M : ℤ)
  rw [discr_eq_discr_of_algEquiv _ e]
  have hdvd := natAbs_discr_dvd (E := E) S fun v hv => hun v (by simpa using hv)
  have hd : Module.finrank ℚ E ≤ n := by
    rw [← Module.finrank_mul_finrank ℚ F E]
    exact Nat.mul_le_mul_left _ hdeg
  have hb : 0 < bound S := Nat.pos_of_ne_zero (bound_ne_zero S)
  have hle := Nat.le_of_dvd (pow_pos hb _) hdvd
  have hle2 : bound S ^ (Module.finrank ℚ E * Module.finrank ℚ E) ≤ bound S ^ (n * n) :=
    Nat.pow_le_pow_right hb (Nat.mul_le_mul hd hd)
  rw [hM, Int.abs_eq_natAbs]
  exact_mod_cast hle.trans hle2
end

section

noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual

namespace GlobalTheory.CompanionTheory.Hypotheses₂

theorem NS_eq_fixingSubgroup (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (S : Set (HeightOneSpectrum (𝓞 F))) :
    NS Ω S = (maxUnramifiedOutside F Ω S).fixingSubgroup :=
  le_antisymm (GlobalTheory.T.normal_subgroup_le_unramified_fixing F Ω S) (GlobalTheory.T.galois_unramified_outside_cohomology F Ω S)

end GlobalTheory.CompanionTheory.Hypotheses₂
end
end

section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

theorem _root_.GlobalTheory.T.vanishing_ideal_smooth_agrees_off : ∀ {k : Type} [Field k] {X : Scheme.{0}} (g : X ⟶ Sp k) (Z : X.IdealSheafData) (A : Closeds X) (O : X.Opens), Smooth (Z.subschemeι ≫ g) → (A : Set X) ⊆ Z.support → (O : Set X) = ((Z.support : Set X) \ A)ᶜ → Smooth ((Scheme.IdealSheafData.vanishingIdeal A).subschemeι ≫ g) ∧ (Scheme.IdealSheafData.vanishingIdeal A).comap O.ι = Z.comap O.ι := by
  first | exact @GlobalTheory.CompanionTheory.SmoothPart.smooth_and_comap_eq | exact GlobalTheory.CompanionTheory.SmoothPart.smooth_and_comap_eq | (intros; apply GlobalTheory.CompanionTheory.SmoothPart.smooth_and_comap_eq <;> assumption)
end
