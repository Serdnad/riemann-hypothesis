module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CoefficientRepTrivialOnUnramified
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2476
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle087
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.IsCondAt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.CompatReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle010
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Algebra.Valued.WithZeroMulInt
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import ReciprocityTheory.Automorphisms.PlaceA
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


private theorem mem_iff {l : ℕ} [Fact l.Prime] {L : Type} [Field L] [NumberField L] {w : Plc L} (j : W.Emb l w) (x : 𝓞 L) :
    x ∈ w.asIdeal ↔ ‖j.1 (algebraMap L _ (x : L))‖ < 1 := by
  have h : w.asIdeal ≤ (GlobalTheory.EvExtend.placeOf (j.1.comp (algebraMap L _))).asIdeal := fun y hy => by
    rw [GlobalTheory.EvExtend.mem_placeOf]
    have h1 : Valued.v (algebraMap L (w.adicCompletion L) (y : L)) < 1 := by
      rw [ReciprocityTheory.Aut.adic_valued_algebraMap]
      exact (w.valuation_lt_one_iff_mem (K := L) y).2 hy
    have h2 := (j.2.tendsto 0).comp (Valued.tendsto_zero_pow_of_v_lt_one h1)
    rw [map_zero] at h2
    refine tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.1 (h2.congr fun n => ?_)
    exact map_pow j.1 _ n
  rw [w.isMaximal.eq_of_le (GlobalTheory.EvExtend.placeOf _).isPrime.ne_top h, GlobalTheory.EvExtend.mem_placeOf]
  rfl

private theorem cc {L : Type} [Field L] [NumberField L] [IsCMField L] (x : 𝓞 L) :
    IsCMField.ringOfIntegersComplexConj L (IsCMField.ringOfIntegersComplexConj L x) = x :=
  RingOfIntegers.ext (IsCMField.complexConj_apply_apply L x)

private theorem norm_mem {L : Type} [Field L] [NumberField L] [IsCMField L] {u w : Plc L}
    (hu : u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))) {x : 𝓞 L} (hx : x ∈ u.asIdeal) :
    x ∈ w.asIdeal ∨ IsCMField.ringOfIntegersComplexConj L x ∈ w.asIdeal := by
  obtain ⟨y, hy⟩ := (IsCMField.ringOfIntegersComplexConj_eq_self_iff L (x * IsCMField.ringOfIntegersComplexConj L x)).1 (by
    rw [map_mul, mul_comm, cc])
  have h1 : y ∈ (u.under (𝓞 (Lp L))).asIdeal := by
    change algebraMap _ (𝓞 L) y ∈ u.asIdeal
    rw [hy]
    exact Ideal.mul_mem_right _ _ hx
  rw [hu] at h1
  change algebraMap _ (𝓞 L) y ∈ w.asIdeal at h1
  rw [hy] at h1
  exact w.isPrime.mem_or_mem h1

private theorem not_stable {L : Type} [Field L] [NumberField L] [IsCMField L] {w : Plc L} (hw : IsSplitAt w)
    (h : ∀ x, IsCMField.ringOfIntegersComplexConj L x ∈ w.asIdeal → x ∈ w.asIdeal) : False := by
  obtain ⟨u, hu, hu'⟩ := hw
  exact hu (HeightOneSpectrum.ext (u.isMaximal.eq_of_le w.isPrime.ne_top fun x hx => (norm_mem hu' hx).elim id (h x)))

private theorem two {L : Type} [Field L] [NumberField L] [IsCMField L] {u w : Plc L}
    (hu : u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))) :
    u = w ∨ ∀ x, x ∈ u.asIdeal ↔ IsCMField.ringOfIntegersComplexConj L x ∈ w.asIdeal := by
  haveI := w.isPrime
  have h : (u.asIdeal : Set (𝓞 L)) ⊆ w.asIdeal ∪ w.asIdeal.comap (IsCMField.ringOfIntegersComplexConj L) :=
    fun x hx => norm_mem hu hx
  rcases Ideal.subset_union.1 h with h | h
  · exact Or.inl (HeightOneSpectrum.ext (u.isMaximal.eq_of_le w.isPrime.ne_top h))
  · refine Or.inr fun x => ?_
    rw [u.isMaximal.eq_of_le (Ideal.comap_ne_top _ w.isPrime.ne_top) h, Ideal.mem_comap]

private theorem ex_emb {l : ℕ} [Fact l.Prime] {L : Type} [Field L] [NumberField L] {w : Plc L} (τ : L →+* Qbar l)
    (h : ∀ x : 𝓞 L, x ∈ w.asIdeal ↔ ‖τ x‖ < 1) : ∃ j : W.Emb l w, j.1.comp (algebraMap L _) = τ := by
  have e : w = GlobalTheory.EvExtend.placeOf τ := HeightOneSpectrum.ext (Ideal.ext fun x => by
    rw [GlobalTheory.EvExtend.mem_placeOf, h])
  subst e
  obtain ⟨j, hc, hx, -⟩ := GlobalTheory.EvExtend.exists_ext τ
  exact ⟨⟨j, hc⟩, RingHom.ext hx⟩

theorem UpperTheory.placeEmbeddings_bijective_infinitePlaces :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V : s.Lev) (ι : Qbar l ≃+* ℂ), Finite (Emb l (fun v : V.frame.Vl => s.w v.1)) ∧ Function.Bijective (fun x : Emb l (fun v : V.frame.Vl => s.w v.1) => InfinitePlace.mk (ι.toRingHom.comp x.res)) := by
  intro l _ L Ω _ _ _ _ _ _ s V ι
  obtain ⟨hun, hsp⟩ := UpperTheory.under_chosen_place_and_isSplitAt_of_decomp_le l L Ω s
  have hinj : Function.Injective
      (fun x : Emb l (fun v : V.frame.Vl => s.w v.1) => InfinitePlace.mk (ι.toRingHom.comp x.res)) := by
    rintro ⟨v, j⟩ ⟨v', j'⟩ h
    rcases InfinitePlace.mk_eq_iff.1 h with h | h
    · have h1 : ∀ x : L, j.1 (algebraMap L _ x) = j'.1 (algebraMap L _ x) := fun x =>
        ι.injective (RingHom.congr_fun h x)
      have h2 : s.w v.1 = s.w v'.1 := HeightOneSpectrum.ext (Ideal.ext fun x => by
        rw [mem_iff j, mem_iff j', h1])
      have h3 : v = v' := Subtype.ext (by rw [← hun v.1, h2, hun])
      subst h3
      refine congrArg (Sigma.mk v) (Subtype.ext (DFunLike.coe_injective ?_))
      exact (HeightOneSpectrum.denseRange_algebraMap L (s.w v.1)).equalizer j.2 j'.2 (funext h1)
    · have h1 : ∀ x : L, j.1 (algebraMap L _ (IsCMField.complexConj L x)) = j'.1 (algebraMap L _ x) := fun x =>
        ι.injective ((IsCMField.complexEmbedding_complexConj L _ x).trans (RingHom.congr_fun h x))
      have h2 : ∀ x, IsCMField.ringOfIntegersComplexConj L x ∈ (s.w v.1).asIdeal ↔ x ∈ (s.w v'.1).asIdeal := fun x => by
        rw [mem_iff j, mem_iff j', ← h1]
        rfl
      have h3 : v = v' := Subtype.ext (by
        rw [← hun v.1, ← hun v'.1]
        refine HeightOneSpectrum.ext (Ideal.ext fun y => ?_)
        change algebraMap _ (𝓞 L) y ∈ (s.w v.1).asIdeal ↔ algebraMap _ (𝓞 L) y ∈ (s.w v'.1).asIdeal
        rw [← h2, (IsCMField.ringOfIntegersComplexConj_eq_self_iff L _).2 ⟨y, rfl⟩])
      subst h3
      refine (not_stable (hsp (s.w v.1) ?_) fun x hx => (h2 x).1 hx).elim
      rw [hun]
      exact s.split _ (Or.inl v.2)
  refine ⟨Finite.of_injective _ hinj, hinj, fun p => ?_⟩
  obtain ⟨φ, rfl⟩ : ∃ φ, InfinitePlace.mk φ = p := ⟨_, p.mk_embedding⟩
  let τ : L →+* Qbar l := ι.symm.toRingHom.comp φ
  have hl : ((l : ℕ) : 𝓞 (Lp L)) ∈ ((GlobalTheory.EvExtend.placeOf τ).under (𝓞 (Lp L))).asIdeal := by
    change algebraMap _ (𝓞 L) ((l : ℕ) : 𝓞 (Lp L)) ∈ (GlobalTheory.EvExtend.placeOf τ).asIdeal
    rw [map_natCast, GlobalTheory.EvExtend.mem_placeOf]
    simpa using GlobalTheory.EvExtend.norm_natCast_lt_one (l := l)
  rcases two (hun ((GlobalTheory.EvExtend.placeOf τ).under (𝓞 (Lp L)))).symm with h | h
  · obtain ⟨j, hj⟩ := ex_emb (w := s.w ((GlobalTheory.EvExtend.placeOf τ).under (𝓞 (Lp L)))) τ fun x => by
      rw [← h, GlobalTheory.EvExtend.mem_placeOf]
    refine ⟨⟨⟨_, hl⟩, j⟩, congrArg InfinitePlace.mk (RingHom.ext fun x => ?_)⟩
    exact (congrArg ι (RingHom.congr_fun hj x)).trans (ι.apply_symm_apply _)
  · obtain ⟨j, hj⟩ := ex_emb (w := s.w ((GlobalTheory.EvExtend.placeOf τ).under (𝓞 (Lp L))))
      (τ.comp (IsCMField.complexConj L).toRingEquiv.toRingHom) fun x => by
        have h1 := h (IsCMField.ringOfIntegersComplexConj L x)
        rw [cc, GlobalTheory.EvExtend.mem_placeOf] at h1
        exact h1.symm
    refine ⟨⟨⟨_, hl⟩, j⟩, InfinitePlace.mk_eq_iff.2 (Or.inr (RingHom.ext fun x => ?_))⟩
    have h1 : ι (j.1 (algebraMap L _ x)) = φ (IsCMField.complexConj L x) :=
      (congrArg ι (RingHom.congr_fun hj x)).trans (ι.apply_symm_apply _)
    change starRingEnd ℂ (ι (j.1 (algebraMap L _ x))) = φ x
    rw [h1, IsCMField.complexEmbedding_complexConj, Complex.conj_conj]
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.HeckeGal UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem norm_hom {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (σ : K →ₐ[ℚ_[l]] PadicAlgCl l) (x : K) : ‖σ x‖ = ‖(x : PadicAlgCl l)‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm,
    minpoly.algHom_eq σ σ.injective, ← minpoly.algHom_eq K.val K.val.injective]
  rfl

private theorem embAt_of_induced {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ}
    [Fact l.Prime] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) {O : Type} [CommRing O]
    [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (_root_.ReciprocityTheory.Gal.Dec (F := F) A) O)
    (hj : GlobalTheory.Pst.Induces Bw) (τ : F →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1)
    (hτ : GlobalTheory.Pst.IsInduced Bw τ τ') : EmbAt w τ := by
  intro x
  rw [hτ]
  have h1 := norm_hom (LL'.1.val.comp τ') ⟨Bw.j (algebraMap F Ω x), Bw.j_E x⟩
  refine ((hj.valuation_lt_one_iff _).symm.trans (h x)).symm.trans ?_
  exact iff_of_eq (congrArg (· < 1) h1.symm)

theorem UpperTheory.local_global_compatibility_gl2 :
    Af.HypothesesH → ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (ι : Qbar l ≃+* ℂ) (n : ℕ) [Fact (n = 2)], 1 ≤ n → ∀ (r : _root_.Formalism.ConjugateSelfDual.G F Ω →* GL (Fin n) (Qbar l)) (π : TR.CuspSub F n) (χ : HChar F), Continuous r → π.IsRegAlg → π.Polarized χ → AttR ι r π → ∀ (w : HeightOneSpectrum (𝓞 F)) (m : Fin n → ℤ), (∀ τ : F →+* Qbar l, EmbAt w τ → π.HasInfChar (InfinitePlace.mk (ι.toRingHom.comp τ)) (infOf m)) → ∀ σ, π.IsLocComp w σ → ∀ (A : ValuationSubring Ω) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) rc, IsRec h rc → UpperTheory.V.Lev.AbW (rc (algNorm σ)) → Hi.DRat ι h (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := F) A).subtype) (fun _ => Finset.univ.val.map fun j => -m j) fun s => (rc (algNorm σ)).charPol s := by
  intro PH F Ω _ _ _ _ _ _ l _ hl ι n _ hn r π χ hr hreg hpol hatt w m hm σ hσ A h rc hrc hab O _ _ _ Bw hj
  obtain ⟨-, wt, HT, -, -, hG⟩ := Af.exR PH F Ω l ι n hn π χ hreg hpol
  replace hG := hG r hr hatt
  obtain ⟨h1, h2, -, -⟩ := hG.above _ _ (Loc.tiedP l) w A h O Bw hj
  refine ⟨h1, fun τ LL' τ' hτ => ?_, fun s => ?_⟩
  · have e : HT τ = Finset.univ.val.map fun j => -m j := by
      refine Multiset.map_injective (f := fun n : ℤ => (n : ℂ)) Int.cast_injective ?_
      have := hG.weights τ _ (hm τ (embAt_of_induced h Bw hj τ LL' τ' hτ))
      simp only [this, infOf, Multiset.map_map]
      exact Multiset.map_congr rfl fun i _ => by simp
    exact e ▸ h2 τ LL' τ' hτ
  · exact ((Af.compatReal PH F Ω l hl ι n hn r π χ hr hreg hpol hatt w σ hσ A h rc hrc).2 O Bw hj).2 (Or.inr hab) s
end
