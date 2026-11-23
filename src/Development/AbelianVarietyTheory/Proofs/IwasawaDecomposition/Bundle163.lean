module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle154
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.NcardEqTwoIff
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
public import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle271
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle159
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.InfAdeleTensorBijective
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletedLatticeStabilizerCompactOpen
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HdimEqZeroOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.PreservesFiniteColimitsTwistFunctor
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle080
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle158
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle146
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle155
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.PicardGroup
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle157
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Mathlib.Topology.UniformSpace.Uniformizable
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle002

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.acris_frobenius_eigen_fil_eq_qlMul_tPow : ∀ (l : ℕ) [Fact l.Prime], ∀ (C : Core l) (r : ℕ) (x : Per.Acris l), phiA l x = (l : Per.Acris l) ^ r * x → C.j x ∈ Per.FilP l r → ∃ (z : ℤ_[l]) (k : ℕ), (l : Per.Acris l) ^ k * x = algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l z) * C.t ^ r := by
  first | exact @GlobalTheory.MemLoc.fix_pow | exact GlobalTheory.MemLoc.fix_pow | (intros; apply GlobalTheory.MemLoc.fix_pow <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.bdR_galois_invariants_eq_finExt : ∀ (l : ℕ) [Fact l.Prime], ∀ (C : Core l) (K : FinExt l) (b : Per.BdR l), (∀ g ∈ GK K, Per.σD g b = b) → ∃ y ∈ K.1, algebraMap (Per.BdRp l) (Per.BdR l) (C.o y) = b := by
  first | exact @GlobalTheory.MemLoc.InvDR.invariants_BdR | exact GlobalTheory.MemLoc.InvDR.invariants_BdR | (intros; apply GlobalTheory.MemLoc.InvDR.invariants_BdR <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.HostCM

theorem valuation_eq_of_unram (K : Type) [Field K] [NumberField K] [IsCMField K]
    (hunr : ∀ P : Ideal (𝓞 K), P.IsPrime → P ≠ ⊥ →
      ¬ ∀ x : 𝓞 K, IsCMField.complexConj K • x - x ∈ P)
    (P : HeightOneSpectrum (𝓞 K)) (x : maximalRealSubfield K) :
    P.valuation K (algebraMap (maximalRealSubfield K) K x) =
      (P.under (𝓞 (maximalRealSubfield K))).valuation (maximalRealSubfield K) x := by
  have hp := P.isPrime
  have hp' := (P.under (𝓞 (maximalRealSubfield K))).isPrime
  have : P.asIdeal.LiesOver (P.under (𝓞 (maximalRealSubfield K))).asIdeal := ⟨rfl⟩
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := K ≃ₐ[maximalRealSubfield K] K)
    (P.under (𝓞 (maximalRealSubfield K))).asIdeal P.asIdeal
  have h1 : Nat.card (P.asIdeal.inertia (K ≃ₐ[maximalRealSubfield K] K)) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun x y => Subtype.ext ?_⟩, ⟨⟨1, one_mem _⟩⟩⟩
    have key : ∀ z : P.asIdeal.inertia (K ≃ₐ[maximalRealSubfield K] K),
        (z : K ≃ₐ[maximalRealSubfield K] K) = 1 := by
      intro z
      rcases Eta.cases K z.1 with hz | hz
      · exact hz
      · exfalso
        have hm := AddSubgroup.mem_inertia.mp z.2
        rw [hz] at hm
        exact hunr P.asIdeal hp P.ne_bot hm
    rw [key x, key y]
  rw [h1, Ideal.ramificationIdxIn_eq_ramificationIdx _ P.asIdeal (K ≃ₐ[maximalRealSubfield K] K)] at hcard
  rw [← HeightOneSpectrum.valuation_liesOver K (P.under (𝓞 (maximalRealSubfield K))) P x,
    ← hcard, pow_one]


open Classical in
theorem host_cm_embedding_properties : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), ∃ c : H.E ≃ₐ[H.F] H.E, (∀ x, c x = H.conj x) ∧ (IsTotallyReal H.F ∧ IsTotallyComplex H.E ∧ Module.finrank H.F H.E = 2 ∧ c ≠ 1 ∧ Function.Bijective fun g => InfinitePlace.mk (_root_.Formalism.L2.Host.embPsi H g)) ∧ (∀ (P : HeightOneSpectrum (𝓞 H.E)) (k : (H.F)ˣ), _root_.Formalism.L2.Host.ordF P (_root_.Formalism.L2.Host.upF H.F k) = _root_.Formalism.L2.Host.ordF (P.under (𝓞 H.F)) k) ∧ (∀ g : R.Psi, _root_.Formalism.L2.Host.embPsi H g H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ)) ∧ Fintype.card (R.Psi) = R.f := by
  intro R H
  have hcm : IsCMField H.E := H.isCMField_hostE
  have hc : ∀ x, IsCMField.complexConj H.E x = H.conj x := fun x => bridge_star_holds R H x
  have hmem : ∀ g : R.Psi, _root_.Formalism.L2.Host.embPsi H g ∈ H.cmType := fun g => ((factEmb R H).2 g).2 g.2
  have hT := H.der.cmType.1
  refine ⟨IsCMField.complexConj H.E, hc, ⟨inferInstance, inferInstance,
    Algebra.IsQuadraticExtension.finrank_eq_two _ _, IsCMField.complexConj_ne_one _,
    ?_, ?_⟩, ?_, hmem, ?_⟩
  · intro g g' h
    rcases InfinitePlace.mk_eq_iff.1 h with h | h
    · exact Subtype.ext ((factEmb R H).1.1 h)
    · have h' := hmem g'
      rw [← h] at h'
      exact absurd h' ((hT _).1 (hmem g))
  · intro w
    by_cases hw : w.embedding ∈ H.cmType
    · obtain ⟨g, hg⟩ := (factEmb R H).1.2 w.embedding
      refine ⟨⟨g, ((factEmb R H).2 g).1 (hg ▸ hw)⟩, ?_⟩
      show InfinitePlace.mk (H.emb g) = w
      rw [hg, InfinitePlace.mk_embedding]
    · obtain ⟨g, hg⟩ := (factEmb R H).1.2 (ComplexEmbedding.conjugate w.embedding)
      have hw' : ComplexEmbedding.conjugate w.embedding ∈ H.cmType := by
        by_contra h'
        exact hw ((hT _).2 h')
      refine ⟨⟨g, ((factEmb R H).2 g).1 (hg ▸ hw')⟩, ?_⟩
      show InfinitePlace.mk (H.emb g) = w
      rw [hg, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
  · intro P k
    have := valuation_eq_of_unram H.E (fun P hP h0 hx => H.der.unramEF P hP h0 fun x => by
      have e : H.conj • x = IsCMField.complexConj H.E • x := Subtype.ext (hc x).symm
      rw [e]
      exact hx x) P k
    unfold _root_.Formalism.L2.Host.ordF
    rw [← this]
    rfl
  · rw [← Nat.card_eq_fintype_card]
    exact (factCardPsi R H).1


open Classical in
theorem host_cm : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), ∃ c : H.E ≃ₐ[H.F] H.E, (∀ x, c x = H.conj x) ∧ CMData H.F c (_root_.Formalism.L2.Host.embPsi H) ∧ (∀ (P : HeightOneSpectrum (𝓞 H.E)) (k : (H.F)ˣ), _root_.Formalism.L2.Host.ordF P (_root_.Formalism.L2.Host.upF H.F k) = _root_.Formalism.L2.Host.ordF (P.under (𝓞 H.F)) k) ∧ (∀ g : R.Psi, _root_.Formalism.L2.Host.embPsi H g H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ)) ∧ Fintype.card (R.Psi) = R.f := by
  intro R H
  obtain ⟨c, hc, ⟨h1, h2, h3, h4, h5⟩, h⟩ := host_cm_embedding_properties R H
  exact ⟨c, hc, ⟨h1, h2, h3, h4, h5⟩, h⟩

end GlobalTheory.Mem.HostCM
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc Matrix
open scoped ComplexOrder

namespace GlobalTheory.FockParseval

open MvPolynomial GlobalTheory.FockSeq

variable {σ : Type} [DecidableEq σ]

def unitMono (F : Fock σ) (α : σ →₀ ℕ) : F.H := (wt α)⁻¹ • F.ι (monomial α 1)


omit [DecidableEq σ] in
theorem conj_wt (α : σ →₀ ℕ) : (starRingEnd ℂ) (wt α) = wt α := Complex.conj_ofReal _


omit [DecidableEq σ] in
theorem wt_mul_self (α : σ →₀ ℕ) : wt α * wt α = (mfact α : ℕ) := by
  rw [← star_wt_mul, conj_wt]

theorem orthonormal_unitMono (F : Fock σ) : Orthonormal ℂ (unitMono F) := by
  classical
  rw [orthonormal_iff_ite]
  intro α β
  rw [unitMono, unitMono, inner_smul_left, inner_smul_right, F.fockIP, ← mfact_cast, map_inv₀, conj_wt]
  by_cases h : α = β
  · subst h
    have := wt_ne_zero α
    rw [if_pos rfl, if_pos rfl, ← wt_mul_self]
    field_simp
  · simp [h]

theorem dense_span_unitMono (F : Fock σ) :
    ⊤ ≤ (Submodule.span ℂ (Set.range (unitMono F))).topologicalClosure := by
  intro x _
  refine closure_mono ?_ (F.dense x)
  rintro _ ⟨f, rfl⟩
  induction f using MvPolynomial.induction_on' with
  | add f g hf hg => rw [map_add (f := _)]; exact Submodule.add_mem _ hf hg
  | monomial α c =>
    have e : F.ι (monomial α c) = (c * wt α) • unitMono F α := by
      rw [unitMono, smul_smul, mul_assoc, mul_inv_cancel₀ (wt_ne_zero α), mul_one, ← map_smul, smul_monomial]
      simp
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨α, rfl⟩)

theorem inner_unitMono {F : Fock σ} {v : F.H} {E : MvPowerSeries σ ℂ} (h : HasCoeff F v E) (α : σ →₀ ℕ) :
    inner ℂ (unitMono F α) v = wt α * MvPowerSeries.coeff α E := by
  have := wt_ne_zero α
  rw [unitMono, inner_smul_left, h α, ← mfact_cast, map_inv₀, conj_wt, ← wt_mul_self]
  field_simp

theorem parseval (σ : Type) [DecidableEq σ] (F : Fock σ) (v w : F.H) (E E' : MvPowerSeries σ ℂ)
    (hv : HasCoeff F v E) (hw : HasCoeff F w E') :
    Summable (fun α : σ →₀ ℕ => (GlobalTheory.FockSeq.mfact α : ℝ) * ‖MvPowerSeries.coeff α E‖ ^ 2) ∧
      inner ℂ v w = ∑' α : σ →₀ ℕ, (GlobalTheory.FockSeq.mfact α : ℂ) * (starRingEnd ℂ) (MvPowerSeries.coeff α E) *
        MvPowerSeries.coeff α E' := by
  refine ⟨((orthonormal_unitMono F).inner_products_summable v).congr fun α => ?_, ?_⟩
  · rw [inner_unitMono hv, norm_mul, mul_pow, wt, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt (Nat.cast_nonneg _)]
  · let b := HilbertBasis.mk (orthonormal_unitMono F) (dense_span_unitMono F)
    rw [← b.tsum_inner_mul_inner v w]
    refine tsum_congr fun α => ?_
    rw [HilbertBasis.coe_mk, ← inner_conj_symm, inner_unitMono hv, inner_unitMono hw, map_mul, conj_wt,
      ← wt_mul_self]
    ring

end GlobalTheory.FockParseval
end
end

section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.Vol.ScaleExists

theorem trueScale_isScale : ∀ cd : CDHaar, CdScaleIs cd (trueScale cd) :=
  GlobalTheory.Mem.Vol.Scale.cdScaleIs_trueScale

end GlobalTheory.Mem.Vol.ScaleExists
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.VolInfIso

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem bijective_fam (σ : E →ₐ[F] E) {I : Type} (τ : I → (E →+* ℂ)) (θ : I → (Ainf F ⊗[F] E →+* ℂ))
    (h : IsCMExt F E σ) (hτ : IsCMFam τ) (hθ : ∀ i, IsInfEmb (τ i) (θ i)) :
    Function.Bijective (fun (z : Ainf F ⊗[F] E) (i : I) => θ i z) := by
  obtain ⟨hF, hE, h2, hσ⟩ := h
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  let c : E ≃ₐ[F] E := AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ)
  have hc' : ∀ (τ : E →+* ℂ) x, τ (c x) = starRingEnd ℂ (τ x) := hσ
  have hnr : ∀ φ : E →+* ℂ, ComplexEmbedding.conjugate φ ≠ φ := fun φ hφ =>
    IsTotallyComplex.complexEmbedding_not_isReal φ (ComplexEmbedding.isReal_iff.2 hφ)
  have hc : c ≠ 1 := by
    intro h1
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    refine hnr φ (RingHom.ext fun x => ?_)
    rw [ComplexEmbedding.conjugate_coe_eq, ← hc', h1]
    rfl
  choose θ0 h0 h0' using fun φ : E →+* ℂ => GlobalTheory.InfAdeleCM.exists_hom (F := F) φ
  have hΨ : ∀ φ : E →+* ℂ, φ ∈ Set.range τ ↔ ComplexEmbedding.conjugate φ ∉ Set.range τ := by
    intro φ
    constructor
    · rintro ⟨i, rfl⟩ ⟨j, hj⟩
      have : j = i := hτ.1 (by
        show InfinitePlace.mk (τ j) = InfinitePlace.mk (τ i)
        rw [hj, InfinitePlace.mk_conjugate_eq])
      subst this
      exact hnr _ hj.symm
    · intro hn
      obtain ⟨i, hi⟩ := hτ.2 (InfinitePlace.mk φ)
      rcases InfinitePlace.mk_eq_iff.1 hi with e | e
      · exact ⟨i, e⟩
      · refine absurd ⟨i, ?_⟩ hn
        rw [← e]
        ext x
        simp
  have hb := GlobalTheory.InfAdeleCM.bijective c h2 hc hc' θ0
    (fun φ => GlobalTheory.InfAdeleCM.hom_tmul φ (θ0 φ) (h0 φ) (h0' φ)) (Set.range τ) hΨ
  have hinj : Function.Injective τ := fun i j hij => hτ.1 (by
    show InfinitePlace.mk (τ i) = InfinitePlace.mk (τ j)
    rw [hij])
  let u : I ≃ Set.range τ := Equiv.ofInjective τ hinj
  have he : (fun (z : Ainf F ⊗[F] E) (i : I) => θ i z) =
      (Equiv.arrowCongr u.symm (Equiv.refl ℂ)) ∘ (fun (z : Ainf F ⊗[F] E) (φ : Set.range τ) => θ0 φ.1 z) := by
    funext z i
    rw [GlobalTheory.Mem.VolEmb.infEmb_unique (τ i) (θ i) (θ0 (τ i)) (hθ i) ⟨h0 _, h0' _⟩]
    rfl
  rw [he]
  exact (Equiv.bijective _).comp hb

theorem infEmb_sigR (σ : E →ₐ[F] E) (τ : E →+* ℂ) (θ : Ainf F ⊗[F] E →+* ℂ)
    (h : IsCMExt F E σ) (hθ : IsInfEmb τ θ) (z : Ainf F ⊗[F] E) :
    θ (sigR (Ainf F) σ z) = star (θ z) := by
  obtain ⟨hF, -, -, hσ⟩ := h
  have hθ' := GlobalTheory.InfAdeleCM.hom_tmul τ θ hθ.1 hθ.2
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    show θ (a ⊗ₜ[F] σ x) = starRingEnd ℂ _
    rw [hθ', hθ', map_mul, GlobalTheory.InfAdeleCM.conj_ext, hσ]
    rfl
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy, star_add]

theorem exists_infAdele_equiv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (I : Type) [Fintype I] (τ : I → (E →+* ℂ)) (θ : I → (Ainf F ⊗[F] E →+* ℂ)), IsCMExt F E σ → IsCMFam τ → (∀ i, IsInfEmb (τ i) (θ i)) → ∃ e : (Ainf F ⊗[F] E) ≃+* (I → ℂ), (∀ x i, e x i = θ i x) ∧ Continuous e ∧ Continuous e.symm ∧ ∀ x i, e (sigR (Ainf F) σ x) i = star (e x i) := by
  intro F E _ _ _ _ _ σ I _ τ θ h hτ hθ
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [h.2.2.1]; omega)
  haveI : IsModuleTopology (Ainf F) (Ainf F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Ainf F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Ainf F) _
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_infiniteAdele F
  obtain ⟨e0⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (Ainf F)
  haveI : LocallyCompactSpace (Ainf F ⊗[F] E) := e0.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (Ainf F ⊗[F] E) := e0.secondCountableTopology
  have hb : Function.Bijective (Pi.ringHom θ : Ainf F ⊗[F] E →+* (I → ℂ)) := bijective_fam σ τ θ h hτ hθ
  let e : (Ainf F ⊗[F] E) ≃+* (I → ℂ) := RingEquiv.ofBijective _ hb
  have hc : Continuous e := continuous_pi fun i =>
    IsModuleTopology.continuous_of_ringHom (R := Ainf F) (θ i) (hθ i).2
  have ho : IsOpenMap e :=
    AddMonoidHom.isOpenMap_of_sigmaCompact e.toAddEquiv.toAddMonoidHom e.surjective hc
  refine ⟨e, fun _ _ => rfl, hc, ?_, fun x i => infEmb_sigR σ (τ i) (θ i) h (hθ i) x⟩
  exact (e.toEquiv.toHomeomorphOfContinuousOpen hc ho).symm.continuous

end GlobalTheory.Mem.VolInfIso
end
end

section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

theorem _root_.GlobalTheory.T.completedLattice_stabilizer_compact_open : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (L : Submodule (𝓞 E) (Fin M → E)), L.FG → Submodule.span E (L : Set (Fin M → E)) = ⊤ → ∃ K : Subgroup (HA (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J), (∀ h, h ∈ K ↔ StabHat F (L : Set (Fin M → E)) ((HA.mat (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J h : GL (Fin M) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E)) : Matrix (Fin M) (Fin M) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E))) ∧ IsOpen (K : Set (HA (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J)) ∧ IsCompact (K : Set (HA (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J)) := by
  first | exact @GlobalTheory.Mem.Vol.StabGroup.exists_compact_open_stab | exact GlobalTheory.Mem.Vol.StabGroup.exists_compact_open_stab | (intros; apply GlobalTheory.Mem.Vol.StabGroup.exists_compact_open_stab <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem exists_subsingleton_coh_twist_tens_lbPow : ∀ (k : Type) [Field k] {Y : Scheme.{0}} (f : Y ⟶ Sp k), IsProjOver f → ∀ (A N : LB Y), IsAmpleLB A → N.IsLB → ∀ (G : Y.Modules) [IsFiniteQC G] (B : ℕ), ∃ j₁ : ℕ, ∀ j m : ℕ, j₁ ≤ j → m < B → ∀ p, 0 < p → Subsingleton (coh (twist G (tens (lbPow A j) (lbPow N m))) p) := by
  intro k _ Y f hf A N hA hN G _ B
  letI := algebraΓOfHom f
  have := (isProper_and_exists_isAmpleLB_of_isProjOver hf).1
  have H (m : Fin B) : ∃ q : ℕ, ∀ n ≥ q, ∀ p, 0 < p →
      Subsingleton (coh (twist (twist G (lbPow N m)) (lbPow A n)) p) :=
    have := isFiniteQC_twist (F := G) (isLB_lbPow hN m)
    eventually_atTop.1 (hA.eventually_subsingleton_coh_twist (f := f) (fun _ => rfl) _)
  choose q hq using H
  obtain ⟨Q, hQ⟩ := Finite.exists_le q
  refine ⟨Q, fun j m hj hm p hp => ?_⟩
  have := hq ⟨m, hm⟩ j ((hQ _).trans hj) p hp
  obtain ⟨e⟩ := nonempty_twist_twist_iso_of_cls_eq G (isLB_lbPow hN m)
    (isLB_lbPow hA.isLB j) (isLB_tens (isLB_lbPow hA.isLB j) (isLB_lbPow hN m)) (by
      rw [cls_tens (isLB_lbPow hA.isLB j) (isLB_lbPow hN m),
        ← cls_tens (isLB_lbPow hA.isLB j) (isLB_lbPow hN m) (isLB_tens (isLB_lbPow hA.isLB j) (isLB_lbPow hN m)),
        ← cls_tens (isLB_lbPow hN m) (isLB_lbPow hA.isLB j) (isLB_tens (isLB_lbPow hN m) (isLB_lbPow hA.isLB j))]
      exact (cls_eq_iff _ _).2 (tens_comm_iso (isLB_lbPow hA.isLB j) (isLB_lbPow hN m)))
  exact (cohOn.mapIso k ⊤ p e).symm.injective.subsingleton

end GlobalTheory
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.completion_embedding_compatible_closures : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] (w : HeightOneSpectrum (𝓞 E)) (W : HeightOneSpectrum (𝓞 K)) (j : K → Kbar w) (f : w.adicCompletion E →+* W.adicCompletion K) (b : Kbar w ≃+* Kbar W), Continuous f → (∀ x, b (algebraMap _ _ x) = algebraMap _ _ (f x)) → (∀ x : K, b (j x) = algebraMap (W.adicCompletion K) _ (algebraMap K (W.adicCompletion K) x)) → (∀ x : E, f (algebraMap E _ x) = algebraMap K _ (algebraMap E K x)) → letI := f.toAlgebra; Neutral.B1.normGroup (w.adicCompletion E) (IntermediateField.adjoin (w.adicCompletion E) (Set.range j)) = (Units.map (Algebra.norm (w.adicCompletion E) : W.adicCompletion K →* w.adicCompletion E)).range := by
  first | exact @GlobalTheory.normGroup_adjoin_eq_norm_range_completion | exact GlobalTheory.normGroup_adjoin_eq_norm_range_completion | (intros; apply GlobalTheory.normGroup_adjoin_eq_norm_range_completion <;> assumption)
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.minpoly_irreducible_local_embedding : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)), IsPlaceOver A v → (∀ σ : G K Ω, ∃ τ ∈ Dec (F := K) A, ∀ x : L, τ (algebraMap L Ω x) = σ (algebraMap L Ω x)) → ∀ ι : Ω →ₐ[K] Kbar v, IsLocEmb A v ι → ∀ α : L, Irreducible ((minpoly K α).map (algebraMap K (v.adicCompletion K))) := by
  first | exact @GlobalTheory.LocIrred.minpoly_map_adicCompletion_irreducible | exact GlobalTheory.LocIrred.minpoly_map_adicCompletion_irreducible | (intros; apply GlobalTheory.LocIrred.minpoly_map_adicCompletion_irreducible <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

theorem _root_.GlobalTheory.T.twistedPowerHigherCohomVanishing_pullback_iff_pushforward : ∀ {X Y : Scheme.{0}} (g : Y ⟶ X) [IsAffineHom g] (A N : LB X), A.IsLB → N.IsLB → ∀ (G : Y.Modules) [G.IsQuasicoherent], (TwistConeVanishing (A.pull g) (N.pull g) G ↔ TwistConeVanishing A N ((Scheme.Modules.pushforward g).obj G)) := by
  first | exact @GlobalTheory.twistConeVanishing_pull_iff_pushforward | exact GlobalTheory.twistConeVanishing_pull_iff_pushforward | (intros; apply GlobalTheory.twistConeVanishing_pull_iff_pushforward <;> assumption)
end

section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

theorem _root_.GlobalTheory.T.artin_restrict_eq_artin_norm_single_place : ∀ (E Ω : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (K : IntermediateField E Ω) [FiniteDimensional E K] [NumberField K] [IsAlgClosure K Ω]
    (art : Ideles E →* Gab E Ω) (artK : Ideles K →* Gab K Ω), IsGlobalArtin art → IsGlobalArtin artK →
    ∀ (v : HeightOneSpectrum (𝓞 E)) (W : HeightOneSpectrum (𝓞 K)),
      W.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal →
      (∀ W' : HeightOneSpectrum (𝓞 K), W'.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal → W' = W) →
      ∀ (y : Kˣ) (τ : _root_.Formalism.ConjugateSelfDual.G K Ω),
        toAb K Ω τ = artK (localIdele K W (Units.map (algebraMap K (W.adicCompletion K)).toMonoidHom y)) →
        toAb E Ω (τ.restrictScalars E) =
          art (localIdele E v (Units.map (algebraMap E (v.adicCompletion E)).toMonoidHom
            (Units.map (Algebra.norm E (S := K)) y))) := by
  first | exact @GlobalTheory.NormCompat.res_art_eq_art_norm | exact GlobalTheory.NormCompat.res_art_eq_art_norm | (intros; apply GlobalTheory.NormCompat.res_art_eq_art_norm <;> assumption)
end
