module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle080
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle149
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle153
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecompositionGroupLocalGaloisIso
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowCharPowEqSelf
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Formalism.LocalToGlobal.Columns.RecLevelLocT
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle022
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
import Mathlib.Data.Finset.Functor
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle002
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentCharacterArgumentMulStabilizer
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Mathlib.Topology.Sheaves.Presheaf
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.local_embeddings_differ_by_decomposition : ∀ (K Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (ι ι₂ : Ω →ₐ[K] Kbar v), IsLocEmb A v ι → IsLocEmb A v ι₂ → ∃ σ ∈ Dec (F := K) A, ∀ z, ι₂ z = ι (σ z) := by
  first | exact @GlobalTheory.LocEmbDec.exists_dec_of_isLocEmb | exact GlobalTheory.LocEmbDec.exists_dec_of_isLocEmb | (intros; apply GlobalTheory.LocEmbDec.exists_dec_of_isLocEmb <;> assumption)
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.residue_closure_iso_ramified_ext : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (e : ℕ) (f : v.adicCompletion K →+* v'.adicCompletion L), 0 < e → (∀ y, Valued.v (f y) = Valued.v y ^ e) → letI := f.toAlgebra; FiniteDimensional (v.adicCompletion K) (v'.adicCompletion L) → ∀ b₀ : Kbar v ≃+* Kbar v', (∀ x, b₀ (algebraMap (v.adicCompletion K) (Kbar v) x) = algebraMap (v'.adicCompletion L) (Kbar v') (f x)) → ∀ y : Kbar v, IsIntegral (v.adicCompletionIntegers K) y ↔ IsIntegral (v'.adicCompletionIntegers L) (b₀ y) := by
  first | exact @GlobalTheory.LocIntegral.isIntegral_iff_isIntegral_map | exact GlobalTheory.LocIntegral.isIntegral_iff_isIntegral_map | (intros; apply GlobalTheory.LocIntegral.isIntegral_iff_isIntegral_map <;> assumption)
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem normGroup_adjoin_eq_norm_range_completion : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] (w : HeightOneSpectrum (𝓞 E)) (W : HeightOneSpectrum (𝓞 K)) (j : K → Kbar w) (f : w.adicCompletion E →+* W.adicCompletion K) (b : Kbar w ≃+* Kbar W), Continuous f → (∀ x, b (algebraMap _ _ x) = algebraMap _ _ (f x)) → (∀ x : K, b (j x) = algebraMap (W.adicCompletion K) _ (algebraMap K (W.adicCompletion K) x)) → (∀ x : E, f (algebraMap E _ x) = algebraMap K _ (algebraMap E K x)) → letI := f.toAlgebra; Neutral.B1.normGroup (w.adicCompletion E) (IntermediateField.adjoin (w.adicCompletion E) (Set.range j)) = (Units.map (Algebra.norm (w.adicCompletion E) : W.adicCompletion K →* w.adicCompletion E)).range := by
  intro E K _ _ _ _ _ w W j f b hfc hb hj hf
  letI := f.toAlgebra

  let c : W.adicCompletion K →ₐ[w.adicCompletion E] Kbar w :=
    { toRingHom := b.symm.toRingHom.comp (algebraMap (W.adicCompletion K) (Kbar W))
      commutes' := fun x => by
        change b.symm (algebraMap _ _ (f x)) = _
        rw [← hb x]; exact b.symm_apply_apply _ }
  have hcj : ∀ x : K, c (algebraMap K (W.adicCompletion K) x) = j x := by
    intro x
    change b.symm (algebraMap _ _ _) = _
    rw [← hj x]; exact b.symm_apply_apply _
  have hrange : c.fieldRange = IntermediateField.adjoin (w.adicCompletion E) (Set.range j) := by
    apply le_antisymm
    · rintro _ ⟨y, rfl⟩
      have hspan := span_basis_image_adicCompletion_eq_top E K w W f hfc hf _ (Module.finBasis E K)
      have hy : y ∈ Submodule.span (w.adicCompletion E)
          (Set.range fun i => algebraMap K (W.adicCompletion K) (Module.finBasis E K i)) := by
        rw [hspan]; trivial
      induction hy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        change c _ ∈ _
        rw [hcj]
        exact IntermediateField.subset_adjoin _ _ ⟨_, rfl⟩
      | zero => simp
      | add x y _ _ hx hy =>
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_add (f := _)] at hx hy ⊢
        exact add_mem hx hy
      | smul a x _ hx =>
        change c.toLinearMap (a • x) ∈ _
        rw [map_smul c.toLinearMap]
        exact IntermediateField.smul_mem _ hx
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨x, rfl⟩
      exact ⟨algebraMap K _ x, hcj x⟩
  let e : W.adicCompletion K ≃ₐ[w.adicCompletion E]
      IntermediateField.adjoin (w.adicCompletion E) (Set.range j) :=
    (AlgEquiv.ofInjectiveField c).trans (IntermediateField.equivOfEq hrange)
  ext u
  simp only [Neutral.B1.normGroup, MonoidHom.mem_range]
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨Units.map e.symm.toRingEquiv.toMonoidHom v, ?_⟩
    ext
    simp [Algebra.norm_eq_of_algEquiv]
  · rintro ⟨v, rfl⟩
    refine ⟨Units.map e.toRingEquiv.toMonoidHom v, ?_⟩
    ext
    simp [Algebra.norm_eq_of_algEquiv]

end GlobalTheory
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocIrred

theorem minpoly_map_adicCompletion_irreducible : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)), IsPlaceOver A v → (∀ σ : G K Ω, ∃ τ ∈ Dec (F := K) A, ∀ x : L, τ (algebraMap L Ω x) = σ (algebraMap L Ω x)) → ∀ ι : Ω →ₐ[K] Kbar v, IsLocEmb A v ι → ∀ α : L, Irreducible ((minpoly K α).map (algebraMap K (v.adicCompletion K))) := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ A v hA hdec ι hι α
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  haveI : Normal K Ω := IsAlgClosure.normal K Ω
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  set a : Ω := algebraMap L Ω α with ha
  have hPa : minpoly K a = minpoly K α := by
    have := minpoly.algHom_eq (IsScalarTower.toAlgHom K L Ω) (algebraMap L Ω).injective α
    simpa [ha] using this
  rw [← hPa]
  have haint : IsIntegral K a := (Algebra.IsAlgebraic.isAlgebraic a).isIntegral
  set P := minpoly K a with hP
  have hsep : P.Separable := (minpoly.irreducible haint).separable
  set β := ι a with hβdef
  have hβ : IsIntegral (v.adicCompletion K) β := Algebra.IsIntegral.isIntegral β
  set Q := minpoly (v.adicCompletion K) β with hQ
  have hQdvd : Q ∣ P.map (algebraMap K (v.adicCompletion K)) := by
    apply minpoly.dvd
    rw [Polynomial.aeval_map_algebraMap, hβdef, Polynomial.aeval_algHom_apply, hP, minpoly.aeval, map_zero]
  obtain ⟨θ, -, -, hlift⟩ := GlobalTheory.LocDec.decomposition_mulEquiv_galLoc K Ω A v hA ι hι
  set R := (P.map (algebraMap K Ω)).roots with hR
  have hRcard : Multiset.card R = P.natDegree :=
    by
    rw [hR, IsAlgClosed.card_roots_eq_natDegree, Polynomial.natDegree_map]
  have hRnd : R.Nodup := Polynomial.nodup_roots (hsep.map)
  have hSnd : (R.map ι).Nodup := hRnd.map ι.injective
  have hQ0 : Q ≠ 0 := minpoly.ne_zero hβ
  have hsub : R.map ι ≤ (Q.map (algebraMap (v.adicCompletion K) (Kbar v))).roots := by
    rw [Multiset.le_iff_subset hSnd]
    intro y hy
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hy
    have hr0 : Polynomial.aeval r P = 0 := by
      have := (Polynomial.mem_roots_map (minpoly.ne_zero haint)).mp hr
      rwa [Polynomial.aeval_def]
    obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root' haint.isAlgebraic hr0
    obtain ⟨τ, hτ, hτσ⟩ := hdec σ
    have hg : θ ⟨τ, hτ⟩ β = ι r := by
      rw [hβdef, hlift ⟨τ, hτ⟩ a, ← hσ]
      exact congrArg ι (hτσ α)
    rw [Polynomial.mem_roots_map hQ0, ← Polynomial.aeval_def, ← hg, Polynomial.aeval_algEquiv,
      AlgHom.comp_apply, hQ, minpoly.aeval, map_zero]
  have hdeg : P.natDegree ≤ Q.natDegree := by
    calc P.natDegree = Multiset.card (R.map ι) := by rw [Multiset.card_map, hRcard]
      _ ≤ Multiset.card (Q.map (algebraMap (v.adicCompletion K) (Kbar v))).roots := Multiset.card_le_card hsub
      _ ≤ (Q.map (algebraMap (v.adicCompletion K) (Kbar v))).natDegree := Polynomial.card_roots' _
      _ = Q.natDegree := Polynomial.natDegree_map _
  have heq : P.map (algebraMap K (v.adicCompletion K)) = Q :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hβ) ((minpoly.monic haint).map _) hQdvd
      (by rw [Polynomial.natDegree_map]; exact hdeg)
  rw [heq]
  exact minpoly.irreducible hβ

end GlobalTheory.LocIrred
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.decomposition_group_local_galois_iso : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (ι : Ω →ₐ[E] Kbar w), IsLocEmb A w ι → ∃ θ : Dec (F := E) A ≃* GalLoc w, Continuous θ ∧ Continuous θ.symm ∧ ∀ σ : Dec (F := E) A, Lifts ι (θ σ) (σ : G E Ω) := by
  first | exact @GlobalTheory.LocDec.decomposition_mulEquiv_galLoc | exact GlobalTheory.LocDec.decomposition_mulEquiv_galLoc | (intros; apply GlobalTheory.LocDec.decomposition_mulEquiv_galLoc <;> assumption)
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.WeilDict


open Polynomial in
theorem exists_eq_of_pow_eq_self {Ω L : Type} [Field Ω] [IsAlgClosed Ω] [Field L] (j : Ω →+* L) {N : ℕ}
    (hN : 2 ≤ N) {ζ : L} (hζ : ζ ^ N = ζ) : ∃ z, j z = ζ := by
  have hmon : (X ^ N - X : Polynomial Ω).Monic :=
    monic_X_pow_sub (by rw [degree_X]; exact_mod_cast (by omega : 1 < N))
  have hb : ζ ∈ ((X ^ N - X : Polynomial Ω).map j).roots := by
    rw [mem_roots (hmon.map j).ne_zero]
    simp [hζ]
  rw [Splits.roots_map (IsAlgClosed.splits _), Multiset.mem_map] at hb
  obtain ⟨y, -, hy⟩ := hb
  exact ⟨y, hy⟩

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}

theorem isFrob_iff_of_lifts (h : IsPlaceOver A w) {ι : Ω →ₐ[E] Kbar w} {g : GalLoc w} {σ : G E Ω}
    (hσ : σ ∈ Dec (F := E) A) (H : Lifts ι g σ) :
    IsFrob (F := E) A (normV w) σ ↔
      ∀ (ζ : Kbar w) (m : ℕ), 0 < m → ζ ^ normV w ^ m = ζ → g ζ = ζ ^ normV w := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  rw [GlobalTheory.FrobTeich.isFrob_iff_teichmuller E Ω A w h σ]
  constructor
  · rintro ⟨-, hT⟩ ζ m hm hζ
    obtain ⟨z, rfl⟩ := exists_eq_of_pow_eq_self (ι : Ω →+* Kbar w)
      (Nat.one_lt_pow hm.ne' (one_lt_normV w)) hζ
    have hz : z ^ normV w ^ m = z := (ι : Ω →+* Kbar w).injective (by rw [map_pow]; exact hζ)
    change g (ι z) = ι z ^ normV w
    rw [H z, hT z m hm hz, map_pow]
  · intro hT
    refine ⟨hσ, fun z m hm hz => (ι : Ω →+* Kbar w).injective ?_⟩
    change ι (σ z) = ι (z ^ normV w)
    rw [← H z, map_pow]
    exact hT _ m hm (by rw [← map_pow, hz])

end GlobalTheory.WeilDict
end
end

section

namespace GlobalTheory.Mem.Col2.IdxEx

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

theorem apply_single_of_mem_unip {F : Type} [Field F] {n c : ℕ} {r : (Fin (n + c) → F) ≃ₗ[F] (Fin (n + c) → F)}
    (hr : r ∈ _root_.Formalism.L2.Col.Loc.N1 F n c) (s l : Fin (n + c)) (hl : s ≤ l) :
    r (Pi.single s 1) l = (Pi.single s 1 : Fin (n + c) → F) l := by
  obtain ⟨h1, h2⟩ := hr
  by_cases hs : s.1 < n
  · have e : (Pi.single s 1 : Fin (n + c) → F) = _root_.Formalism.L2.Col.Loc.inX F n c (Pi.single ⟨s.1, hs⟩ 1) := by
      funext m
      by_cases hm : m.1 < n
      · simp [_root_.Formalism.L2.Col.Loc.inX, hm, Pi.single_apply, Fin.ext_iff]
      · have : m ≠ s := fun h => hm (h ▸ hs)
        simp [_root_.Formalism.L2.Col.Loc.inX, hm, this]
    rw [e, h2]
  · have e : (Pi.single s 1 : Fin (n + c) → F) = _root_.Formalism.L2.Col.Loc.eN F (n + c) (n + (s.1 - n)) := by
      funext m
      have : n + (s.1 - n) = s.1 := by omega
      simp [_root_.Formalism.L2.Col.Loc.eN, this, Pi.single_apply, Fin.ext_iff]
    have h3 := h1.1.2.2 (s.1 - n) l (by
      have : s.1 ≤ l.1 := hl
      simp only [Set.mem_setOf_eq]
      omega)
    rw [e]
    exact sub_eq_zero.1 h3

theorem det_eq_one_of_mem_unip :
    ∀ (F : Type) [Field F] (n c : ℕ), ∀ r ∈ _root_.Formalism.L2.Col.Loc.N1 F n c, LinearEquiv.det r = 1 := by
  intro F _ n c r hr
  apply Units.ext
  rw [LinearEquiv.coe_det, ← LinearMap.det_toMatrix', Matrix.det_of_upperTriangular]
  · refine Finset.prod_eq_one fun s _ => ?_
    have := apply_single_of_mem_unip hr s s le_rfl
    rw [LinearMap.toMatrix'_apply]
    simpa using this
  · intro l s hls
    have hls' : s < l := hls
    have := apply_single_of_mem_unip hr s l hls'.le
    rw [LinearMap.toMatrix'_apply]
    simpa [hls'.ne'] using this

end GlobalTheory.Mem.Col2.IdxEx
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.UG Formalism.L2.Forms Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory

theorem uLocDual_intOE_map {E : Type} [Field E] [NumberField E] (σ : E →+* E) {a : E}
    (ha : a ∈ intOE E) : σ a ∈ intOE E := by
  obtain ⟨r, rfl⟩ := ha
  exact ⟨⟨σ r, (RingOfIntegers.isIntegral_coe r).map σ.toIntAlgHom⟩, rfl⟩

theorem uLocDual_hform_one {E : Type} [Field E] {n : ℕ} (σ : E →+* E) (x y : Fin n → E) :
    Formalism.UG.hform σ (1 : Matrix (Fin n) (Fin n) E) x y = ∑ i, σ (x i) * y i := by
  unfold Formalism.UG.hform
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [Matrix.one_apply_eq, mul_one]
  · intro j _ hj; rw [Matrix.one_apply_ne (Ne.symm hj), mul_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem uLocDual_eq : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (_ : ∀ x, σ (σ x) = x) (n : ℕ) [NeZero n] (p q : 𝓞 E) (_ : (p : E) ≠ 0) (_ : (q : E) = σ (p : E)),
    Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) (rll_dLat n ((p : E)⁻¹))) = rll_dLat n (q : E) := by
  intro F E _ _ _ _ _ σ _ n _ p q hp hq
  have e : dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) (rll_dLat n ((p : E)⁻¹)) =
      (rll_dLat n (q : E) : Set (Fin n → E)) := by
    ext y
    rw [SetLike.mem_coe, rll_mem_dLat]
    show (∀ x ∈ rll_dLat n ((p : E)⁻¹), Formalism.UG.hform (σ : E →+* E) 1 x y ∈ (algebraMap (𝓞 E) E).range) ↔ _
    simp only [uLocDual_hform_one]
    constructor
    · intro hy
      refine ⟨fun i hi => ?_, ?_⟩
      · have := hy (Pi.single i 1) ⟨fun j _ => by
          by_cases hj : j = i
          · subst hj; rw [Pi.single_eq_same]; exact one_mem _
          · rw [Pi.single_eq_of_ne hj]; exact zero_mem _, by
          rw [Pi.single_eq_of_ne (Ne.symm hi), mul_zero]; exact zero_mem _⟩
        rw [Finset.sum_eq_single i] at this
        · rwa [Pi.single_eq_same, map_one, one_mul] at this
        · intro j _ hj; rw [Pi.single_eq_of_ne hj, map_zero, zero_mul]
        · intro h; exact absurd (Finset.mem_univ _) h
      · have := hy (Pi.single (lastIdx n) (p : E)) ⟨fun j hj => by
          rw [Pi.single_eq_of_ne hj]; exact zero_mem _, by
          rw [Pi.single_eq_same, inv_mul_cancel₀ hp]; exact one_mem _⟩
        rw [Finset.sum_eq_single (lastIdx n)] at this
        · rw [Pi.single_eq_same] at this
          show (q : E) * y (lastIdx n) ∈ intOE E
          rw [hq]; exact this
        · intro j _ hj; rw [Pi.single_eq_of_ne hj, map_zero, zero_mul]
        · intro h; exact absurd (Finset.mem_univ _) h
    · rintro ⟨h1, h2⟩ x ⟨hx1, hx2⟩
      refine sum_mem fun i _ => ?_
      by_cases hi : i = lastIdx n
      · subst hi
        have hl : x (lastIdx n) = (p : E) * ((p : E)⁻¹ * x (lastIdx n)) := by
          rw [mul_inv_cancel_left₀ hp]
        rw [hl, map_mul, mul_comm ((σ : E →+* E) (p : E)), mul_assoc]
        refine mul_mem (uLocDual_intOE_map _ hx2) ?_
        have : (σ : E →+* E) (p : E) = (q : E) := by rw [hq]; rfl
        rw [this]; exact h2
      · exact mul_mem (uLocDual_intOE_map _ (hx1 i hi)) (h1 i hi)
  rw [e, Submodule.span_eq]

end GlobalTheory
end
end

section

noncomputable section

namespace GlobalTheory.Mem.Col2.JetEx

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker

def FinAlg (T : Set ℂ) : Prop :=
  ∃ Z : Finset ℂ, (∀ z ∈ Z, IsAlgebraic ℚ z) ∧ T ⊆ (Subfield.closure (Z : Set ℂ) : Set ℂ)

theorem FinAlg.mono {T T' : Set ℂ} (h : FinAlg T') (hT : T ⊆ T') : FinAlg T := by
  obtain ⟨Z, hZ, hsub⟩ := h
  exact ⟨Z, hZ, hT.trans hsub⟩

theorem finAlg_of_finite {T : Set ℂ} (h : T.Finite) (ha : ∀ z ∈ T, IsAlgebraic ℚ z) : FinAlg T := by
  refine ⟨h.toFinset, fun z hz => ha z (h.mem_toFinset.mp hz), ?_⟩
  rw [h.coe_toFinset]
  exact Subfield.subset_closure

theorem finAlg_biUnion {κ : Type} {s : Set κ} (hs : s.Finite) {T : κ → Set ℂ} (h : ∀ k ∈ s, FinAlg (T k)) :
    FinAlg (⋃ k ∈ s, T k) := by
  classical
  choose! Z hZ hsub using h
  refine ⟨hs.toFinset.biUnion Z, ?_, ?_⟩
  · intro z hz
    obtain ⟨k, hk, hzk⟩ := Finset.mem_biUnion.mp hz
    exact hZ k (hs.mem_toFinset.mp hk) z hzk
  · refine Set.iUnion₂_subset fun k hk => (hsub k hk).trans (Subfield.closure_mono ?_)
    intro z hz
    exact Finset.mem_biUnion.mpr ⟨k, hs.mem_toFinset.mpr hk, hz⟩

theorem FinAlg.union {T T' : Set ℂ} (h : FinAlg T) (h' : FinAlg T') : FinAlg (T ∪ T') := by
  classical
  obtain ⟨Z, hZ, hsub⟩ := h
  obtain ⟨Z', hZ', hsub'⟩ := h'
  refine ⟨Z ∪ Z', fun z hz => ?_, Set.union_subset ?_ ?_⟩
  · rcases Finset.mem_union.mp hz with hz | hz
    · exact hZ z hz
    · exact hZ' z hz
  · exact hsub.trans (Subfield.closure_mono (by simp))
  · exact hsub'.trans (Subfield.closure_mono (by simp))

theorem FinAlg.closure {T : Set ℂ} (h : FinAlg T) : FinAlg (Subfield.closure T : Set ℂ) := by
  obtain ⟨Z, hZ, hsub⟩ := h
  exact ⟨Z, hZ, SetLike.coe_subset_coe.mpr (Subfield.closure_le.mpr hsub)⟩

open _root_.Formalism.L2.Col (Fields Sp HomE UF IsSdLat)

variable {X : Fields} (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (M : ℕ)

def jetSet (n : ℕ) : Set ℂ :=
  {z | ∃ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ) (x : HomE X.E a b)
    (e : DVar X.Tau a b →₀ ℕ), InRange S M c N N' x ∧ e.degree = n ∧
      z = (A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd S N N' c x) e}

def JetAlg : Prop :=
  ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ) (x : HomE X.E a b),
    InRange S M c N N' x → ∀ e : DVar X.Tau a b →₀ ℕ,
      IsAlgebraic ℚ ((A.chiF a b N N')⁻¹ * derivAt0 (A.thInd S N N' c x) e)

def VacEq : Prop :=
  ∀ (γ : UF X.E a) (γ' : UF X.E b) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)),
    IsSdLat N → IsSdLat N' → ∀ z, A.e a b (gmap γ.1 N) (gmap γ'.1 N') z = A.e a b N N' (A.pullV a b γ.1 γ'.1 z)

end GlobalTheory.Mem.Col2.JetEx

end
end

section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.Vol

theorem exists_isFdeg_smul_of_isDS : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ → ∀ c : NNReal, 0 < c → ∃ d : ℝ, IsFdeg ((c : ENNReal) • Formalism.REAL.muG ε) σ d := by
  intro n ε lam H _ _ σ h c hc
  obtain ⟨h1, h2, hU, hirr, hsq, -⟩ := h
  obtain ⟨d, hd, hI⟩ := GlobalTheory.schur_orthogonality_unitary n ε H σ hU hirr hsq
  have hc' : (0 : ℝ) < (c : ℝ) := hc
  refine ⟨d / c, div_pos hd hc', fun v w v' w' => ⟨(hI v w v' w').1.smul_measure ENNReal.coe_ne_top, ?_⟩⟩
  rw [integral_smul_measure, (hI v w v' w').2, ENNReal.coe_toReal, Complex.real_smul,
    Complex.ofReal_div, div_div_eq_mul_div]
  ring

end GlobalTheory.Mem.Vol
end
