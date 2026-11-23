module

public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.GaloisConditionFiveExtraOf
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle124
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Padics.LocalField
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle334

@[expose] public section

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.TameDesign
open scoped Pointwise

private theorem wild_mem_Ine {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    {A : ValuationSubring Ω} {σ : Formalism.ConjugateSelfDual.G E Ω}
    (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) : σ ∈ Ine (F := E) A := by
  have hv : ∀ y : Ω, A.valuation (σ y) = A.valuation y := by
    intro y
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    have h := A.valuation.map_one_add_of_lt (hσ y hy)
    rw [add_sub_cancel, map_div₀, div_eq_one_iff_eq (by simpa using hy)] at h
    exact h
  refine ⟨?_, fun x hx => ?_⟩
  · show σ • A = A
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def,
      ← A.valuation_le_one_iff, ← A.valuation_le_one_iff, ← hv, mul_inv_apply]
  · rcases eq_or_ne x 0 with rfl | hx0
    · simp
    have e : σ x - x = (σ x / x - 1) * x := by field_simp
    rw [e, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' hx) (hσ x hx0)

section General

variable {Γ R : Type} [Group Γ] [CommRing R]

private theorem mem_ker_char_iff (J : Ideal R) (χ : Γ →* Rˣ) (g : Γ) :
    g ∈ ((Units.map (Ideal.Quotient.mk J).toMonoidHom).comp χ).ker ↔ ((χ g : Rˣ) : R) - 1 ∈ J := by
  rw [MonoidHom.mem_ker, Units.ext_iff, ← Ideal.Quotient.eq]
  rfl

private theorem isOpen_ker_char [TopologicalSpace Γ] [TopologicalSpace R] [IsTopologicalRing R]
    (J : Ideal R) (hJ : IsOpen (J : Set R)) (χ : Γ →* Rˣ)
    (hχ : Continuous fun g => ((χ g : Rˣ) : R)) :
    IsOpen (((Units.map (Ideal.Quotient.mk J).toMonoidHom).comp χ).ker : Set Γ) := by
  have : (((Units.map (Ideal.Quotient.mk J).toMonoidHom).comp χ).ker : Set Γ) =
      (fun g => ((χ g : Rˣ) : R) - 1) ⁻¹' (J : Set R) := by
    ext g
    simp only [SetLike.mem_coe, mem_ker_char_iff, Set.mem_preimage]
  rw [this]
  exact hJ.preimage (hχ.sub continuous_const)

end General

section Wild

variable {E Ω R : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [TopologicalSpace R] [IsTopologicalRing R]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 E)}

omit [TopologicalSpace R] [IsTopologicalRing R] in
private theorem eq_zero_of_mem_pow (x : R) (h : ∀ m, x ∈ IsLocalRing.maximalIdeal R ^ (m + 1)) : x = 0 := by
  rw [← Ideal.mem_bot, ← Ideal.iInf_pow_eq_bot_of_isLocalRing (IsLocalRing.maximalIdeal R)
    (IsLocalRing.maximalIdeal.isMaximal R).ne_top, Ideal.mem_iInf]
  exact fun m => Ideal.pow_le_pow_right (Nat.le_succ m) (h m)

private theorem char_eq_one_of_wild (hR : IsAdic (IsLocalRing.maximalIdeal R)) (hA : IsPlaceOver A v) (n : ℕ)
    (hv : ((n : ℕ) : 𝓞 E) ∉ v.asIdeal) (χ : Formalism.ConjugateSelfDual.G E Ω →* Rˣ) (hχ : Continuous fun g => ((χ g : Rˣ) : R))
    (σ : Formalism.ConjugateSelfDual.G E Ω) (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) (h1 : χ σ ^ n = 1) : χ σ = 1 := by
  rw [Units.ext_iff, Units.val_one, ← sub_eq_zero]
  refine eq_zero_of_mem_pow _ fun m => ?_
  rw [← mem_ker_char_iff]
  refine GlobalTheory.mem_of_wild_of_pow_mem_open_normal E Ω A v hA _ inferInstance
    (isOpen_ker_char _ ((isAdic_iff.mp hR).1 _) χ hχ) σ n hv hσ ?_
  rw [mem_ker_char_iff, map_pow, h1]
  simp

end Wild

theorem firstLocalChar_wild_eq_one_away_from_l (D : D7) (i : D.nd.Loc) (v : HeightOneSpectrum (𝓞 D.host.E))
    (hvl : v ∉ placesOver D.host.E (D.nd.l i)) (σ : GE D.nd) (hσ : σ ∈ wildSet D.nd (D.nd.plOm.1 v)) :
    D.nd.chi i 1 σ = 1 := by
  have hA : IsPlaceOver (D.nd.plOm.1 v) v := D.nd.plOm.2 v
  have hI : σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v) := wild_mem_Ine hσ
  have hvl' : v ∉ placesOver D.host.E (D.ntw.l (D.ntw.twOf i)) := by rwa [D.ntw.twOf_l]

  have hψ : D.ntw.psiL i σ = 1 := by
    obtain ⟨n, hn⟩ := D.ntw.psiL_ord i σ
    have hmem := GlobalTheory.mem_of_wild_of_pow_mem_open_normal _ _ (D.nd.plOm.1 v) v hA (D.ntw.psiL i).ker
      inferInstance (D.ntw.psiL_open i) σ (D.nd.l i ^ n) ?_ hσ (by rw [MonoidHom.mem_ker, map_pow, hn])
    · exact hmem
    · intro h
      apply hvl
      have hp : (D.nd.l i).Prime := Fact.out
      exact v.isPrime.mem_of_pow_mem n (by simpa using h)

  have hc : D.ntw.chi1 (D.ntw.twOf i) (D.nd.j i) (D.ntw.twSide i) σ = 1 := by
    by_cases hpD : v ∈ D.ntw.pD (D.ntw.twOf i)
    · have h15 := D.ntw.delta_15 (D.ntw.twOf i) v hpD _ hA
      have hd : D.ntw.delta (D.ntw.twOf i) σ ^ 15 = 1 := by
        have h := pow_card_eq_one'
          (G := (Ine (F := D.host.E) (D.nd.plOm.1 v)).map (D.ntw.delta (D.ntw.twOf i)))
          (x := ⟨_, σ, hI, rfl⟩)
        rw [h15] at h
        exact congrArg Subtype.val h
      have h15v : ((15 : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal := by
        intro h
        have hN := D.ntw.delta_tame (D.ntw.twOf i) v hpD
        have hm : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal := Ideal.absNorm_mem _
        have e : Ideal.absNorm v.asIdeal = 15 * (Ideal.absNorm v.asIdeal / 15) + 1 := by omega
        rw [e] at hm
        push_cast at hm
        have h1 : (1 : 𝓞 D.host.E) ∈ v.asIdeal := by
          have := v.asIdeal.sub_mem hm (v.asIdeal.mul_mem_right (((Ideal.absNorm v.asIdeal / 15 : ℕ)) : 𝓞 D.host.E) (by simpa using h))
          simpa using this
        exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
      refine char_eq_one_of_wild (D.ntw.twistBaseCoefficientRing_isAdic _) hA 15 h15v _
        (D.ntw.twistCharacterFamily_continuous _ _ _) σ hσ ?_
      rw [D.ntw.twistCharacterFamily_at_auxiliaryPlaces _ _ _ v hpD _ hA σ hI]
      split_ifs
      · exact hd
      · rw [inv_pow, hd, inv_one]
    · by_cases hg : ∃ k, v ∈ placesOver D.host.E (D.host.g k)
      · obtain ⟨k, hvg⟩ := hg
        have hg1 : ((D.host.g k - 1 : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal := fun hm => by
          refine v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr ?_)
          have := v.asIdeal.sub_mem hvg hm
          rwa [Nat.cast_sub (D.host.g_prime k).one_le, Nat.cast_one, sub_sub_cancel] at this
        exact char_eq_one_of_wild (D.ntw.twistBaseCoefficientRing_isAdic _) hA _ hg1 _
          (D.ntw.twistCharacterFamily_continuous _ _ _) σ hσ (D.ntw.twistCharacterFamily_tame _ _ _ k v hvg hvl' _ hA σ hI)
      · push_neg at hg
        exact D.ntw.twistCharacterFamily_unramified _ _ _ v hvl' hg hpD _ hA σ hI
  rw [D.ntw.chi_tw i]
  simp [hψ, hc]

theorem main : ∀ (D : D7) (i : D.nd.Loc), TameCharacterConditions D i ∧ TruncatedSeriesCountingIdentities.TameGeneratorConditions (D := D) i := by
  intro D i
  have hc : TameCharacterConditions D i := by
    refine ⟨fun v hv σ hσ => GlobalTheory.TameDesign.firstLocalChar_wild_eq_one_away_from_l D i v ?_ σ hσ, Formalism.MainNotions.SumRepresentations.Del_holds D i⟩
    rcases hv with hQ | ⟨hS, -⟩
    · exact D.nd.SQ_l i v (Or.inr hQ)
    · exact D.nd.SQ_l i v (Or.inl hS)
  exact ⟨hc, galois_condition_five_extra_of D i hc⟩

end GlobalTheory.TameDesign
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.DecomplRed

open GlobalTheory.WachTensor

private theorem tensorProduct_map_algHom_smul {O A M N : Type} [CommRing O] [CommRing A] [Algebra O A]
    [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N]
    (f : A →ₐ[O] A) (g : M →ₗ[O] N) (r : A) (x : A ⊗[O] M) :
    TensorProduct.map f.toLinearMap g (r • x) = f r • TensorProduct.map f.toLinearMap g x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
    rw [TensorProduct.smul_tmul', TensorProduct.map_tmul, TensorProduct.map_tmul,
      TensorProduct.smul_tmul', AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, smul_eq_mul,
      smul_eq_mul, map_mul]
  | add x y hx hy => rw [smul_add, map_add (f := _), hx, hy, map_add (f := _), smul_add]

private theorem coeffs_eq_of_sum_smul_eq_of_span_eq {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
    (B : Module.Basis (Fin n) R M) (c : Fin n → M) (hc : Submodule.span R (Set.range c) = ⊤)
    {v w : Fin n → R} (hvw : ∑ i, v i • c i = ∑ i, w i • c i) : v = w := by
  have hs : Function.Surjective (Fintype.linearCombination R c) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hc]
  have hi : Function.Injective (B.equivFun.toLinearMap ∘ₗ Fintype.linearCombination R c) :=
    OrzechProperty.injective_of_surjective_endomorphism _ (B.equivFun.surjective.comp hs)
  apply hi
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Fintype.linearCombination_apply, hvw]

theorem decW_of_matrix (S : Sit) (E : S.Comparison₂)
    (h : ∀ (d : ℕ) (Pm : Matrix (Fin d) (Fin d) S.W.EE),
      (∀ y : Fin d → S.RW, (∀ i, ∀ g ∈ Hker S, S.gR g (y i) = y i) →
        ∃ z : Fin d → S.RW, (∀ i, ∀ g ∈ Hker S, S.gR g (z i) = z i) ∧
          ∀ i, ∃ e, y i - (∑ k, E.ioE (Pm i k) * S.φR (z k) - z i) = E.ioE e) ∧
      (∀ z : Fin d → S.RW, (∀ i, ∀ g ∈ Hker S, S.gR g (z i) = z i) →
        (∀ i, ∃ e, ∑ k, E.ioE (Pm i k) * S.φR (z k) - z i = E.ioE e) →
          ∀ i, ∃ e, z i = E.ioE e)) : DecW S E := by
  unfold DecW
  intro T
  have memH : ∀ x, x ∈ Htl S T ↔ ∀ g ∈ Hker S, TWact (S.gR g) T g x = x := fun x => Iff.rfl
  have hH : ∀ g ∈ Hker S, S.W.resΓ g = 1 := fun g hg => MonoidHom.mem_ker.1 hg

  by_cases hsub : Subsingleton (TW S.RW T)
  · have key : ∀ x : TW S.RW T, x ∈ LinearMap.range (E.jD T) := fun x => ⟨0, Subsingleton.elim _ _⟩
    exact ⟨fun y _ => ⟨0, (Htl S T).zero_mem, key _⟩, fun z _ _ => key z⟩
  have : Nontrivial (TW S.RW T) := not_subsingleton_iff_nontrivial.1 hsub
  have : Nontrivial S.RW := by
    by_contra hR
    rw [not_nontrivial_iff_subsingleton] at hR
    exact hsub (Module.subsingleton S.RW _)
  have : Nontrivial S.O := RingHom.domain_nontrivial (algebraMap S.O S.RW)
  have : Nontrivial S.W.EE := RingHom.domain_nontrivial E.ioE.toRingHom
  have : Module.Free S.O ↥T.L.T := T.L.free
  have : Module.Finite S.O ↥T.L.T := Module.Finite.iff_fg.2 T.L.fg

  have bW : Module.Basis (Fin (Module.finrank S.O ↥T.L.T)) S.RW (TW S.RW T) :=
    (Module.finBasis S.O ↥T.L.T).baseChange S.RW
  have hr : 0 < Module.finrank S.O ↥T.L.T := by
    rw [Nat.pos_iff_ne_zero]
    intro h0
    obtain ⟨x, y, hxy⟩ := exists_pair_ne (TW S.RW T)
    exact hxy (bW.repr.injective (Finsupp.ext fun i => absurd i.isLt (by omega)))
  have hdr := (S.W.DD_free T).2
  have : Module.Free S.W.EE (S.W.DD T) := (S.W.DD_free T).1
  have : Module.Finite S.W.EE (S.W.DD T) := Module.finite_of_finrank_pos (by rw [hdr]; exact hr)
  obtain ⟨d, ⟨bD⟩, ⟨bW'⟩⟩ : ∃ d, Nonempty (Module.Basis (Fin d) S.W.EE (S.W.DD T)) ∧
      Nonempty (Module.Basis (Fin d) S.RW (TW S.RW T)) :=
    ⟨_, ⟨Module.finBasis _ _⟩, ⟨bW.reindex (finCongr hdr.symm)⟩⟩

  have hexp : ∀ x : S.W.DD T, E.jD T x = ∑ i, E.ioE (bD.repr x i) • E.jD T (bD i) := by
    intro x
    conv_lhs => rw [← bD.sum_repr x]

    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => E.jD_smul T _ _
  have hspan : Submodule.span S.RW (Set.range fun i => E.jD T (bD i)) = ⊤ := by
    rw [eq_top_iff, ← E.jD_span T, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    rw [hexp x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hinj : ∀ v w : Fin d → S.RW, ∑ i, v i • E.jD T (bD i) = ∑ i, w i • E.jD T (bD i) → v = w :=
    fun v w hvw => coeffs_eq_of_sum_smul_eq_of_span_eq bW' _ hspan hvw
  have hsurj : ∀ y : TW S.RW T, ∃ v : Fin d → S.RW, y = ∑ i, v i • E.jD T (bD i) := by
    intro y
    have hy : y ∈ Submodule.span S.RW (Set.range fun i => E.jD T (bD i)) := by
      rw [hspan]; exact Submodule.mem_top
    obtain ⟨v, hv⟩ := (Submodule.mem_span_range_iff_exists_fun S.RW).1 hy
    exact ⟨v, hv.symm⟩

  have actS : ∀ g (r : S.RW) (x : TW S.RW T),
      TWact (S.gR g) T g (r • x) = S.gR g r • TWact (S.gR g) T g x :=
    fun g r x => tensorProduct_map_algHom_smul (S.gR g) (T.actT g) r x
  have mapS : ∀ (r : S.RW) (x : TW S.RW T), TWmap S.φR T (r • x) = S.φR r • TWmap S.φR T x :=
    fun r x => tensorProduct_map_algHom_smul S.φR LinearMap.id r x
  have hfix : ∀ g ∈ Hker S, ∀ x, TWact (S.gR g) T g (E.jD T x) = E.jD T x := by
    intro g hg x
    rw [← E.jD_act, hH g hg, S.W.γD_one]
  have hact : ∀ g ∈ Hker S, ∀ v : Fin d → S.RW,
      TWact (S.gR g) T g (∑ i, v i • E.jD T (bD i)) = ∑ i, S.gR g (v i) • E.jD T (bD i) := by
    intro g hg v

    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [actS, hfix g hg]
  have hinv : ∀ v : Fin d → S.RW,
      (∑ i, v i • E.jD T (bD i)) ∈ Htl S T ↔ ∀ i, ∀ g ∈ Hker S, S.gR g (v i) = v i := by
    intro v
    rw [memH]
    constructor
    · intro hv i g hg
      exact congrFun (hinj _ _ ((hact g hg v).symm.trans (hv g hg))) i
    · intro hv g hg
      rw [hact g hg v]
      exact Finset.sum_congr rfl fun i _ => by rw [hv i g hg]
  have hk : ∀ k, TWmap S.φR T (E.jD T (bD k)) =
      ∑ i, E.ioE (bD.repr (S.W.φD T (bD k)) i) • E.jD T (bD i) := fun k => by
    rw [← E.jD_φ]
    exact hexp _
  have hφ : ∀ z : Fin d → S.RW, TWmap S.φR T (∑ k, z k • E.jD T (bD k)) =
      ∑ i, (∑ k, E.ioE (bD.repr (S.W.φD T (bD k)) i) * S.φR (z k)) • E.jD T (bD i) := by
    intro z

    rw [map_sum]
    simp only [mapS, hk, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_smul]
    exact Finset.sum_congr rfl fun k _ => by rw [mul_comm]
  have hrng : ∀ v : Fin d → S.RW,
      (∑ i, v i • E.jD T (bD i)) ∈ LinearMap.range (E.jD T) ↔ ∀ i, ∃ e, v i = E.ioE e := by
    intro v
    constructor
    · rintro ⟨x, hx⟩
      rw [hexp] at hx
      have hv := hinj _ _ hx
      exact fun i => ⟨bD.repr x i, (congrFun hv i).symm⟩
    · intro hv
      choose e he using hv
      refine ⟨∑ i, e i • bD i, ?_⟩

      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [E.jD_smul, he i]

  obtain ⟨h1, h2⟩ := h d (Matrix.of fun i k => bD.repr (S.W.φD T (bD k)) i)
  simp only [Matrix.of_apply] at h1 h2
  refine ⟨fun y hy => ?_, fun z hz hφz => ?_⟩
  · obtain ⟨v, rfl⟩ := hsurj y
    obtain ⟨z, hzH, hz⟩ := h1 v ((hinv v).1 hy)
    refine ⟨∑ i, z i • E.jD T (bD i), (hinv z).2 hzH, ?_⟩
    rw [hφ z, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    simp only [← sub_smul]
    exact (hrng _).2 hz
  · obtain ⟨u, rfl⟩ := hsurj z
    have hu := (hinv u).1 hz
    rw [hφ u, ← Finset.sum_sub_distrib] at hφz
    simp only [← sub_smul] at hφz
    exact (hrng u).2 (h2 u hu ((hrng _).1 hφz))

end GlobalTheory.DecomplRed
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.BkCoeff

open GlobalTheory.PstCoeff

theorem isModuleTopology_of_tower (R LL V : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [Field LL] [Algebra R LL] [TopologicalSpace LL] [IsTopologicalRing LL] [IsModuleTopology R LL]
    [AddCommGroup V] [Module LL V] [Module R V] [IsScalarTower R LL V] [FiniteDimensional LL V]
    [TopologicalSpace V] [IsModuleTopology LL V] : IsModuleTopology R V := by
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd LL V
  let e : V ≃ₗ[LL] (Fin (finrank LL V) → LL) := (Module.finBasis LL V).equivFun
  have h1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have h2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let e' : (Fin (finrank LL V) → LL) ≃L[R] V :=
    { e.symm.restrictScalars R with continuous_toFun := h2, continuous_invFun := h1 }
  exact IsModuleTopology.iso e'

section Coeff

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l}
  {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
  (ρ : Representation LL ↥(GK K) V)

theorem actVB_resQ (g : ↥(GK K)) (x : V ⊗[ℚ_[l]] P.R.B) :
    actVB (P.PD K) (resQ ρ) g x = actVB (P.PD K) ρ g x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem galoisInvariants_restrictScalarsToQl : H0V (resQ ρ) = (H0V ρ).restrictScalars ℚ_[l] := by
  ext x
  simp [H0V, Submodule.mem_iInf, sub_eq_zero]

theorem FilV_resQ (a : ℤ) :
    FilV (P.PD K) (LL := ℚ_[l]) (V := V) a = (FilV (P.PD K) (LL := LL) (V := V) a).restrictScalars ℚ_[l] := by
  have h : ∀ y, AlgebraTensorModule.map (LinearMap.id : V →ₗ[ℚ_[l]] V)
      (((P.PD K).Fil a).restrictScalars ℚ_[l]).subtype y =
      AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (((P.PD K).Fil a).restrictScalars ℚ_[l]).subtype y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  ext x
  simp only [FilV, Submodule.restrictScalars_mem, LinearMap.mem_range, h]

variable [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V] [ContinuousConstSMul ℚ_[l] V]

theorem mem_finiteCocycles_restrictScalars_Ql (c : ↥(GK K) → V) : c ∈ finiteCocycles (P.PD K) (resQ ρ) ↔ c ∈ finiteCocycles (P.PD K) ρ := by
  show (c ∈ continuousCocycles (resQ ρ) ∧ ∃ x, ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : P.R.B) = actVB (P.PD K) (resQ ρ) g x - x) ↔
    (c ∈ continuousCocycles ρ ∧ ∃ x, ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : P.R.B) = actVB (P.PD K) ρ g x - x)
  simp only [actVB_resQ]
  exact Iff.rfl

def finiteCocyclesResEquiv : ↥(finiteCocycles (P.PD K) (resQ ρ)) ≃ₗ[ℚ_[l]] ↥(finiteCocycles (P.PD K) ρ) where
  toFun x := ⟨x.1, (mem_finiteCocycles_restrictScalars_Ql P ρ x.1).mp x.2⟩
  invFun x := ⟨x.1, (mem_finiteCocycles_restrictScalars_Ql P ρ x.1).mpr x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

def h1fEquiv : FiniteCohomology (P.PD K) (resQ ρ) ≃ₗ[ℚ_[l]] FiniteCohomology (P.PD K) ρ :=
  (Submodule.Quotient.equiv _ (((B1 ρ).comap (finiteCocycles (P.PD K) ρ).subtype).restrictScalars ℚ_[l]) (finiteCocyclesResEquiv P ρ) (by
    rw [Submodule.map_equiv_eq_comap_symm]
    ext x
    exact Iff.rfl)).trans (Submodule.Quotient.restrictScalarsEquiv ℚ_[l] _)

end Coeff

end GlobalTheory.BkCoeff

namespace GlobalTheory

open GlobalTheory.PstCoeff GlobalTheory.BkCoeff

theorem bkADim_of_dimFormula : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l),
    GlobalTheory.Published.BlochKato.DimFormula (P.PD K) → Formalism.MainNotions.LocalSituation.bkADim (P.PD K) := by
  intro l _ P K hD LL _ _ _ O _ _ hO A hdR
  obtain ⟨-, hfin, hmt, htr, -⟩ := hO
  haveI := hfin
  haveI := hmt
  haveI := htr
  haveI : FiniteDimensional ℚ_[l] A.V := Module.Finite.trans LL A.V
  haveI : IsModuleTopology ℚ_[l] A.V := isModuleTopology_of_tower ℚ_[l] LL A.V
  obtain ⟨-, he⟩ := hD A.V (resQ (LL := LL) A.ρ) A.cont ((isDR_resQ_iff P A.ρ).mpr hdR)
  have hH1 : finrank ℚ_[l] (FiniteCohomology (P.PD K) (resQ A.ρ)) = finrank ℚ_[l] LL * finrank LL (FiniteCohomology (P.PD K) A.ρ) := by
    rw [(h1fEquiv P A.ρ).finrank_eq, finrank_mul_finrank]
  have hH0 : finrank ℚ_[l] ↥(H0V (resQ A.ρ)) = finrank ℚ_[l] LL * finrank LL ↥(H0V A.ρ) := by
    rw [galoisInvariants_restrictScalarsToQl, finrank_mul_finrank]
    rfl
  have hdR' : finrank ℚ_[l] ↥(DdR (P.PD K) (resQ A.ρ)) = finrank ℚ_[l] LL * finrank LL ↥(DdR (P.PD K) A.ρ) := by
    rw [DdR_resQ, finrank_mul_finrank]
    rfl
  have hF : finrank ℚ_[l] ↥(DdR (P.PD K) (resQ A.ρ) ⊓ FilV (P.PD K) (LL := ℚ_[l]) (V := A.V) 0) =
      finrank ℚ_[l] LL * finrank LL ↥(DdR (P.PD K) A.ρ ⊓ FilV (P.PD K) (LL := LL) (V := A.V) 0) := by
    rw [DdR_resQ, FilV_resQ P (LL := LL), ← Submodule.restrictScalars_inf, finrank_mul_finrank]
    rfl
  rw [hH1, hH0, hdR', hF] at he
  push_cast at he
  have hd : (finrank ℚ_[l] LL : ℤ) ≠ 0 := by exact_mod_cast (Module.finrank_pos (R := ℚ_[l]) (M := LL)).ne'
  refine mul_left_cancel₀ hd ?_
  rw [he]
  ring

end GlobalTheory
end
end
