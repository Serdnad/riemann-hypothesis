module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.FormsFiniteAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle021
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle028
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle019
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle022
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.NeutralLocalFields.Bundle001

@[expose] public section

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

private theorem exists_equiv_sigma_blk_lt_iff_lt {N : ℕ} {β : Type} [LinearOrder β] (κ : Fin N → β) :
    ∃ (t : ℕ) (c : Fin t → ℕ) (f : (Σ a, Fin (c a)) ≃ Fin N), ∀ p q, blk f p < blk f q ↔ κ p < κ q := by
  classical
  let S : Finset β := Finset.univ.image κ
  let o : Fin S.card ≃o S := S.orderIsoOfFin rfl
  have hS : ∀ p, κ p ∈ S := fun p => Finset.mem_image_of_mem κ (Finset.mem_univ p)
  let g : Fin N → Fin S.card := fun p => o.symm ⟨κ p, hS p⟩
  refine ⟨S.card, fun a => Fintype.card {p // g p = a},
    (Equiv.sigmaCongrRight (fun a => (Fintype.equivFin {p // g p = a}).symm)).trans
      (Equiv.sigmaFiberEquiv g), ?_⟩
  intro p q
  have hb : ∀ x, blk ((Equiv.sigmaCongrRight (fun a => (Fintype.equivFin {p // g p = a}).symm)).trans
      (Equiv.sigmaFiberEquiv g)) x = g x := by
    intro x
    rfl
  rw [hb, hb]
  show o.symm ⟨κ p, hS p⟩ < o.symm ⟨κ q, hS q⟩ ↔ κ p < κ q
  rw [OrderIso.lt_iff_lt]
  exact Subtype.mk_lt_mk

theorem UpperTheory.exists_refinement_block_order :
    ∀ (N : ℕ) (r s : ℕ) (d : Fin r → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin N) (j : Fin r) (d' : Fin s → ℕ) (e' : (Σ b, Fin (d' b)) ≃ Fin (d j)),
    ∃ (t : ℕ) (c : Fin t → ℕ) (f : (Σ a, Fin (c a)) ≃ Fin N), ∀ p q, blk f p < blk f q ↔ (blk e p < blk e q ∨ ∃ p' q', p = e ⟨j, p'⟩ ∧ q = e ⟨j, q'⟩ ∧ blk e' p' < blk e' q') := by
  intro N r s d e j d' e'
  classical
  obtain ⟨K, hK⟩ : ∃ K : (Σ a, Fin (d a)) → Lex (ℕ × ℕ), ∀ x y, K x < K y ↔
      (x.1 < y.1 ∨ ∃ p' q', x = ⟨j, p'⟩ ∧ y = ⟨j, q'⟩ ∧ blk e' p' < blk e' q') := by
    refine ⟨fun x => toLex ((x.1 : ℕ), if h : x.1 = j then ((blk e' (h ▸ x.2) : Fin s) : ℕ) else 0), ?_⟩
    rintro ⟨a, u⟩ ⟨b, w⟩
    show toLex ((a : ℕ), if h : a = j then ((blk e' (h ▸ u) : Fin s) : ℕ) else 0) <
        toLex ((b : ℕ), if h : b = j then ((blk e' (h ▸ w) : Fin s) : ℕ) else 0) ↔ _
    rw [Prod.Lex.toLex_lt_toLex]
    by_cases ha : a = j <;> by_cases hb : b = j
    · subst ha
      subst hb
      rw [dite_eq_left rfl, dite_eq_left rfl]
      constructor
      · rintro (h | ⟨-, h⟩)
        · exact absurd h (lt_irrefl _)
        · exact Or.inr ⟨u, w, rfl, rfl, Fin.lt_iff_val_lt_val.mpr h⟩
      · rintro (h | ⟨p', q', h1, h2, h3⟩)
        · exact absurd h (lt_irrefl _)
        · refine Or.inr ⟨rfl, ?_⟩
          rw [Sigma.mk.inj_iff] at h1 h2
          rw [eq_of_heq h1.2, eq_of_heq h2.2]
          exact Fin.lt_iff_val_lt_val.mp h3
    · subst ha
      rw [dite_eq_left rfl, dite_eq_right hb]
      constructor
      · rintro (h | ⟨-, h⟩)
        · exact Or.inl (Fin.lt_iff_val_lt_val.mpr h)
        · exact absurd h (Nat.not_lt_zero _)
      · rintro (h | ⟨p', q', -, h2, -⟩)
        · exact Or.inl (Fin.lt_iff_val_lt_val.mp h)
        · exact absurd (congrArg Sigma.fst h2) hb
    · subst hb
      rw [dite_eq_right ha, dite_eq_left rfl]
      constructor
      · rintro (h | ⟨h, -⟩)
        · exact Or.inl (Fin.lt_iff_val_lt_val.mpr h)
        · exact absurd (Fin.ext h) ha
      · rintro (h | ⟨p', q', h1, -, -⟩)
        · exact Or.inl (Fin.lt_iff_val_lt_val.mp h)
        · exact absurd (congrArg Sigma.fst h1) ha
    · rw [dite_eq_right ha, dite_eq_right hb]
      constructor
      · rintro (h | ⟨-, h⟩)
        · exact Or.inl (Fin.lt_iff_val_lt_val.mpr h)
        · exact absurd h (lt_irrefl 0)
      · rintro (h | ⟨p', q', h1, -, -⟩)
        · exact Or.inl (Fin.lt_iff_val_lt_val.mp h)
        · exact absurd (congrArg Sigma.fst h1) ha
  obtain ⟨t, c, f, hf⟩ := exists_equiv_sigma_blk_lt_iff_lt (fun p : Fin N => K (e.symm p))
  refine ⟨t, c, f, fun p q => ?_⟩
  rw [hf, hK]
  simp only [Equiv.symm_apply_eq]
  rfl
end

section

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.finiteDimensional_of_finiteDimensional_levi_slices :
    ∀ (K : Type) [Field K] [NumberField K] (r s : ℕ) (S : Submodule ℂ (archSmooth K (r + s))), S ≤ NInv K (r + s) r → Sat S → Level S → Types S → FiniteDimensional ℂ (slSp (e1 r s) (Set.range (emb (e2 r s))) S) → FiniteDimensional ℂ (slSp (e2 r s) (Set.range (emb (e1 r s))) S) → FiniteDimensional ℂ S := by
  intro K _ _ r s S hN hsat hlev htyp h1 h2
  obtain ⟨V, hVfd, hV⟩ := UpperTheory.exists_finiteDimensional_compact_translates_of_level_types K (r + s) S hlev htyp
  let Φ₀ : archSmooth K (r + s) →ₗ[ℂ] (AdelicGLn.AdelicGL K r × AdelicGLn.AdelicGL K s → ℂ) :=
    { toFun := fun m p => (m : AdelicGLn.AdelicGL K (r + s) → ℂ) (emb (e1 r s) p.1 * emb (e2 r s) p.2)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let Φ : archSmooth K (r + s) →ₗ[ℂ]
      ((AdelicGLn.AdelicGL K r × AdelicGLn.AdelicGL K s) × (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL K (r + s))) → ℂ) :=
    { toFun := fun m p => (m : AdelicGLn.AdelicGL K (r + s) → ℂ) (emb (e1 r s) p.1.1 * emb (e2 r s) p.1.2 * (p.2 : AdelicGLn.AdelicGL K (r + s)))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hfd0 : FiniteDimensional ℂ (Submodule.map Φ₀ S) := by
    refine UpperTheory.finiteDimensional_map_of_separately_finite _ _ _ S Φ₀ ((slSp (e1 r s) (Set.range (emb (e2 r s))) S).map (archSmooth K r).subtype)
      ((slSp (e2 r s) (Set.range (emb (e1 r s))) S).map (archSmooth K s).subtype) inferInstance inferInstance ?_ ?_
    · intro m hm y
      obtain ⟨f, hf, -⟩ := UpperTheory.exists_restriction_blockEmbedding_intertwines_lie K r (r + s) (e1 r s) (emb (e2 r s) y)
      refine Submodule.mem_map.mpr ⟨f m, Submodule.subset_span ⟨m, hm, emb (e2 r s) y, ⟨y, rfl⟩, fun x => hf m x⟩, ?_⟩
      funext x
      change (f m : AdelicGLn.AdelicGL K r → ℂ) x = _
      rw [hf, ← emb_comm]
      rfl
    · intro m hm x
      obtain ⟨f, hf, -⟩ := UpperTheory.exists_restriction_blockEmbedding_intertwines_lie K s (r + s) (e2 r s) (emb (e1 r s) x)
      refine Submodule.mem_map.mpr ⟨f m, Submodule.subset_span ⟨m, hm, emb (e1 r s) x, ⟨x, rfl⟩, fun y => hf m y⟩, ?_⟩
      funext y
      change (f m : AdelicGLn.AdelicGL K s → ℂ) y = _
      rw [hf]
      rfl
  have hfd : FiniteDimensional ℂ (Submodule.map Φ S) := by
    refine UpperTheory.finiteDimensional_map_of_separately_finite _ _ _ S Φ (Submodule.map Φ₀ S) V hfd0 hVfd ?_ ?_
    · intro m hm k
      refine Submodule.mem_map.mpr ⟨rt (k : AdelicGLn.AdelicGL K (r + s)) m, hsat _ k.2 m hm, ?_⟩
      funext x
      change ((rt (k : AdelicGLn.AdelicGL K (r + s)) m : archSmooth K (r + s)) : AdelicGLn.AdelicGL K (r + s) → ℂ) _ = _
      rw [rt_apply]
      rfl
    · intro m hm x
      exact hV m hm (emb (e1 r s) x.1 * emb (e2 r s) x.2)
  refine FiniteDimensional.of_injective (Φ.submoduleMap S) ?_
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  have hx' : ∀ p, Φ x p = 0 := fun p => congrFun (congrArg Subtype.val hx) p
  apply Subtype.ext
  apply Subtype.ext
  funext g
  obtain ⟨b, hb, k, hk, rfl⟩ := Reduction.exists_adelicBorel_mul_maxCompact g
  obtain ⟨X, m₁, m₂, rfl⟩ := UpperTheory.upperTriangular_eq_unipotent_mul_levi _ r s b (Reduction.mem_adelicBorel.mp hb)
  have hxN := hN x.2
  change ((x : archSmooth K (r + s)) : AdelicGLn.AdelicGL K (r + s) → ℂ) (unipGL X * blk m₁ m₂ * k) = 0
  rw [mul_assoc]
  change (∀ (X : UPos (r + s) r → AdeleRing (𝓞 K) K) g, ((x : archSmooth K (r + s)) : AdelicGLn.AdelicGL K (r + s) → ℂ) (unipGL X * g) = _) at hxN
  rw [hxN]
  exact hx' ((m₁, m₂), ⟨k, hk⟩)
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N ValuativeRel
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.inertia_fixes_roots_of_unity_prime_to_residue_char :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω),
    _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w → ∀ M : ℕ, (M : 𝓞 F) ∉ w.asIdeal → ∀ s ∈ Ine (F := F) A, ∀ ζ : Ω, ζ ^ M = 1 → s ζ = ζ := by
  intro F Ω _ _ _ _ _ w A hA M hM s hs ζ hζ
  have hM0 : M ≠ 0 := by
    rintro rfl
    exact hM (by simpa using w.asIdeal.zero_mem)
  have hvM : A.valuation (M : Ω) = 1 := by
    have h1 := (hA (M : 𝓞 F)).not.mpr hM
    have h2 : (algebraMap F Ω) ((M : 𝓞 F) : F) = (M : Ω) := by simp
    rw [h2] at h1
    refine le_antisymm ?_ (not_lt.mp h1)
    simpa using A.valuation_le_one (M : A)
  have hvz : A.valuation ζ = 1 := by
    have hp : A.valuation ζ ^ M = 1 := by rw [← map_pow, hζ, map_one]
    rcases lt_trichotomy (A.valuation ζ) 1 with h | h | h
    · exact absurd hp (pow_lt_one₀ zero_le' h hM0).ne
    · exact h
    · exact absurd hp (one_lt_pow₀ h hM0).ne'
  have hI : s ∈ _root_.Formalism.ConjugateSelfDual.Inertia A := hs
  unfold _root_.Formalism.ConjugateSelfDual.Inertia at hI
  obtain ⟨-, hI⟩ := hI
  have hd : A.valuation (s ζ - ζ) < 1 := hI ζ hvz.le
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    simp at hvz
  set η := s ζ / ζ with hηdef
  have hsz : s ζ = η * ζ := (div_mul_cancel₀ _ hζ0).symm
  have hη : η ^ M = 1 := by
    rw [hηdef, div_pow, ← map_pow, hζ, map_one, div_one]
  have hη1 : A.valuation (η - 1) < 1 := by
    have e : s ζ - ζ = (η - 1) * ζ := by rw [hsz]; ring
    rw [e, map_mul, hvz, mul_one] at hd
    exact hd
  have hvη : A.valuation η = 1 := by
    have e : η = 1 + (η - 1) := by ring
    rw [e]
    exact Valuation.map_one_add_of_lt _ hη1
  by_contra hne
  have hne' : η ≠ 1 := by
    intro h1
    apply hne
    rw [hsz, h1, one_mul]
  have hsum : ∑ i ∈ Finset.range M, η ^ i = 0 := by
    have e := mul_geom_sum η M
    rw [hη, sub_self] at e
    exact (mul_eq_zero.mp e).resolve_left (sub_ne_zero.mpr hne')
  have hMsum : (M : Ω) = ∑ i ∈ Finset.range M, (1 - η ^ i) := by
    rw [Finset.sum_sub_distrib, hsum, sub_zero]
    simp
  have hlt : A.valuation (M : Ω) < 1 := by
    rw [hMsum]
    refine Valuation.map_sum_lt _ one_ne_zero ?_
    intro i _
    have e := mul_geom_sum η i
    have hS : A.valuation (∑ j ∈ Finset.range i, η ^ j) ≤ 1 := by
      refine Valuation.map_sum_le _ ?_
      intro j _
      rw [map_pow, hvη, one_pow]
    rw [Valuation.map_sub_swap, ← e, map_mul]
    calc A.valuation (η - 1) * A.valuation (∑ j ∈ Finset.range i, η ^ j)
        ≤ A.valuation (η - 1) * 1 := by gcongr
      _ = A.valuation (η - 1) := mul_one _
      _ < 1 := hη1
  rw [hvM] at hlt
  exact lt_irrefl _ hlt
end
