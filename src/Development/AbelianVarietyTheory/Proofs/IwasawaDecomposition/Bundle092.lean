module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle073
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle087
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HaarMeasureGramGL2ActionTensor
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralWittTheoremAlmostAllPlaces
public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle084
public import Formalism.LocalRingCardinality.Bundle003
public import Formalism.LocalToGlobal.Columns.GoodXgFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle086
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle085
public import Formalism.LocalToGlobal.Columns.StdLatUnimodular
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.LocalToGlobal.Divisibility.Bundle001
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.Chr

section General

variable {L : Type} [Field L] [NumberField L]

theorem conjPl_iff_comap (c : L ≃+* L) (v v' : HeightOneSpectrum (𝓞 L)) :
    ConjPl c v v' ↔ v.asIdeal = v'.asIdeal.comap (RingOfIntegers.mapRingEquiv c) := by
  constructor
  · intro h
    ext x
    have h1 : v'.valuation L (algebraMap (𝓞 L) L (RingOfIntegers.mapRingEquiv c x)) =
        v.valuation L (algebraMap (𝓞 L) L x) := h (algebraMap (𝓞 L) L x)
    rw [Ideal.mem_comap, ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := L),
      ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := L), h1]
  · intro h x
    exact (GlobalTheory.QNorm.valuation_of_eq_comap c v' v h x).symm

theorem conjPl_iff_mem (c : L ≃+* L) (v v' : HeightOneSpectrum (𝓞 L)) :
    ConjPl c v v' ↔ ∀ x y : 𝓞 L, (y : L) = c (x : L) → (x ∈ v.asIdeal ↔ y ∈ v'.asIdeal) := by
  rw [conjPl_iff_comap]
  constructor
  · intro h x y hxy
    have e : y = RingOfIntegers.mapRingEquiv c x := RingOfIntegers.ext hxy
    rw [h, Ideal.mem_comap, e]
  · intro h
    ext x
    exact h x (RingOfIntegers.mapRingEquiv c x) rfl

theorem existsUnique_conjPl (c : L ≃+* L) (v : HeightOneSpectrum (𝓞 L)) : ∃! v', ConjPl c v v' := by
  set e : 𝓞 L ≃+* 𝓞 L := RingOfIntegers.mapRingEquiv c with he
  refine ⟨v.comap (e.symm : 𝓞 L →+* 𝓞 L) e.symm.surjective, ?_, ?_⟩
  · show ConjPl c v _
    rw [conjPl_iff_comap]
    ext x
    change x ∈ v.asIdeal ↔ e.symm (e x) ∈ v.asIdeal
    rw [e.symm_apply_apply]
  · intro v' h
    rw [conjPl_iff_comap] at h
    ext x
    change x ∈ v'.asIdeal ↔ e.symm x ∈ v.asIdeal
    rw [h, Ideal.mem_comap, e.apply_symm_apply]

theorem under_eq_iff_conjPl {F : Type} [Field F] [NumberField F] [Algebra F L] (c : L ≃ₐ[F] L)
    (hr : Module.finrank F L = 2) (hc : c ≠ 1) (w w' : HeightOneSpectrum (𝓞 L)) :
    w'.under (𝓞 F) = w.under (𝓞 F) ↔ (w' = w ∨ ConjPl c.toRingEquiv w w') := by
  have : Algebra.IsQuadraticExtension F L := { finrank_eq_two' := hr }
  have : IsGalois F L := inferInstance
  have hall : ∀ σ : L ≃ₐ[F] L, σ = 1 ∨ σ = c := by
    intro σ
    have hcard : Nat.card (L ≃ₐ[F] L) = 2 := by rw [IsGalois.card_aut_eq_finrank, hr]
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : L ≃ₐ[F] L)).1 hcard
    by_cases h : σ = 1
    · exact Or.inl h
    · exact Or.inr ((hy σ h).trans (hy c hc).symm)
  constructor
  · intro hu
    have := w.isPrime
    have := w'.isPrime
    have hu' : w'.asIdeal.under (𝓞 F) = w.asIdeal.under (𝓞 F) := congrArg HeightOneSpectrum.asIdeal hu
    obtain ⟨σ, hσ⟩ := Ideal.exists_comap_galRestrict_eq (𝓞 F) F L (𝓞 L) (p := w.asIdeal.under (𝓞 F))
      (P₁ := w'.asIdeal) (P₂ := w.asIdeal) ⟨inferInstance, ⟨hu'.symm⟩⟩ ⟨inferInstance, ⟨rfl⟩⟩
    rcases hall σ with rfl | rfl
    · left
      ext x
      rw [← hσ, map_one, Ideal.mem_comap]
      rfl
    · right
      rw [conjPl_iff_mem]
      intro x y hxy
      have e : y = galRestrict (𝓞 F) F L (𝓞 L) σ x := by
        apply RingOfIntegers.ext
        rw [hxy]
        exact (algebraMap_galRestrict_apply (𝓞 F) σ x).symm
      rw [← hσ, Ideal.mem_comap, e]
  · rintro (rfl | h)
    · rfl
    · rw [conjPl_iff_mem] at h
      ext a
      exact (h (algebraMap (𝓞 F) (𝓞 L) a) (algebraMap (𝓞 F) (𝓞 L) a) (c.commutes (a : F)).symm).symm

end General


open Classical in
theorem conjPl_main : (∀ (L : Type) [Field L] [NumberField L] (c : L ≃+* L) (v : HeightOneSpectrum (𝓞 L)), ∃! v', ConjPl c v v') ∧ (∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (w w' : HeightOneSpectrum (𝓞 H.E)), IsConjPl H w w' ↔ ConjPl H.conj.toRingEquiv w w') ∧ ∀ (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L] (c : L ≃ₐ[F] L), Module.finrank F L = 2 → c ≠ 1 → ∀ (w w' : HeightOneSpectrum (𝓞 L)), w'.under (𝓞 F) = w.under (𝓞 F) ↔ (w' = w ∨ ConjPl c.toRingEquiv w w') :=
  ⟨fun _ _ _ c v => existsUnique_conjPl c v,
    fun _ H w w' => (conjPl_iff_mem H.conj.toRingEquiv w w').symm,
    fun _ _ _ _ _ _ _ c hr hc w w' => under_eq_iff_conjPl c hr hc w w'⟩

end GlobalTheory.Mem.Chr
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx

theorem isFibreFamily_transport {V R : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [MeasurableSpace R] [BorelSpace R]
    (μ : Measure V) (ν : Measure R) (q q₂ : V → R) (e : V ≃ₜ V) (u : Rˣ) (a d : ℝ≥0) (hd : d ≠ 0)
    (hμ : μ = a • μ.map e) (hν : ν = d • ν.map (fun z => (u : R) * z))
    (hq : ∀ v, q₂ (e v) = u * q v) (fib : R → Measure V)
    (h : IsFibreFamily μ q id Set.univ ν {c | IsUnit c} fib) :
    IsFibreFamily μ q₂ id Set.univ ν {c | IsUnit c}
      (fun b => (a * d⁻¹) • (fib ((u⁻¹ : Rˣ) * b)).map e) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hme : MeasurableEmbedding e := e.measurableEmbedding
  have hmu : MeasurableEmbedding (fun z : R => (u : R) * z) :=
    (Homeomorph.smul u : R ≃ₜ R).measurableEmbedding
  refine ⟨fun b => ?_, fun φ hφ => ?_, fun φ hφ hc _ => ?_⟩
  · rw [Measure.smul_apply, hme.map_apply]
    have : e ⁻¹' (q₂ ⁻¹' {id b} ∩ Set.univ)ᶜ = (q ⁻¹' {id ((u⁻¹ : Rˣ) * b)} ∩ Set.univ)ᶜ := by
      ext v
      simp [hq, Units.eq_inv_mul_iff_mul_eq]
    rw [this, h1, smul_zero]
  · have h2' := h2 (φ ∘ e) (hφ.comp e.measurable)
    simp only [Measure.restrict_univ, Function.comp] at h2' ⊢
    have hL : ∫⁻ v, φ v ∂μ = (a : ℝ≥0∞) * ∫⁻ v, φ (e v) ∂μ := by
      conv_lhs => rw [hμ]
      rw [lintegral_smul_measure, hme.lintegral_map, ENNReal.smul_def, smul_eq_mul]
    rw [hL, h2']
    conv_rhs => rw [hν]
    rw [lintegral_smul_measure, hmu.lintegral_map]
    simp only [lintegral_smul_measure, hme.lintegral_map, Units.inv_mul_cancel_left,
      ENNReal.smul_def, smul_eq_mul]
    rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, ← mul_assoc, ← ENNReal.coe_mul]
    congr 2
    field_simp
  · obtain ⟨h4, h5⟩ := h3 (φ ∘ e) (hφ.comp e.continuous) (hc.comp_homeomorph e) (Set.subset_univ _)
    have hmem : ∀ b ∈ {c : R | IsUnit c}, ((u⁻¹ : Rˣ) : R) * b ∈ {c : R | IsUnit c} :=
      fun b hb => (Units.isUnit _).mul hb
    refine ⟨fun b hb => ?_, ?_⟩
    · exact (hme.integrable_map_iff.2 (h4 _ (hmem b hb))).smul_measure_nnreal
    · simp only [integral_smul_nnreal_measure, hme.integral_map]
      exact (h5.comp (continuous_const.mul continuous_id).continuousOn hmem).const_smul _

theorem lrAct_one_right {S : Type} [CommRing S] {n M : ℕ} (g : Matrix (Fin M) (Fin M) S)
    (X : Fin n → Fin M → S) : lrAct g 1 X = fun a => g.mulVec (X a) := by
  funext a
  simp [lrAct, Matrix.one_apply]

theorem exists_homeomorph_lrAct {S : Type} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
    {n M : ℕ} (g : Matrix (Fin M) (Fin M) S) (hg : IsUnit g.det) :
    ∃ e : (Fin n → Fin M → S) ≃ₜ (Fin n → Fin M → S), ⇑e = lrAct g 1 := by
  refine ⟨{ toFun := fun X a => g.mulVec (X a)
            invFun := fun X a => g⁻¹.mulVec (X a)
            left_inv := fun X => ?_
            right_inv := fun X => ?_
            continuous_toFun := continuous_pi fun a =>
              continuous_const.matrix_mulVec (continuous_apply a)
            continuous_invFun := continuous_pi fun a =>
              continuous_const.matrix_mulVec (continuous_apply a) }, ?_⟩
  · funext a
    simp [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul g hg]
  · funext a
    simp [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv g hg]
  · funext X
    rw [lrAct_one_right]
    rfl

theorem fibAt_similitude : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], Nice R → ∀ (M : ℕ) (J J₂ : Matrix (Fin M) (Fin M) E) (lam : Measure (R ⊗[F] E)) (ν : Measure R) (β c : R) (m : Measure (Fin 1 → Fin M → R ⊗[F] E)) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)), lam.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsUnit g.det → IsUnit c → (∀ z, qR R σ J₂ (g.mulVec z) = c * qR R σ J z) → FibAt R σ J (tupMeas lam 1 M) ν β m → FibAt R σ J₂ (tupMeas lam 1 M) ν (c * β) ((modu (R ⊗[F] E) g.det * (modu R c)⁻¹) • m.map (lrAct g 1)) := by
  intro F E _ _ _ _ _ σ R _ _ _ _ _ _ _ _ _ hR M J J₂ lam ν β c m g hlam hν hg hc hq hfib
  obtain ⟨fib, hfib, rfl⟩ := hfib
  obtain ⟨hA, hred, -⟩ := GlobalTheory.T.tensor_niceRing_artinian_reduced_openUnits F E R hR
  have hμ := GlobalTheory.T.vectorTupleProductMeasure_two_sided_action (R ⊗[F] E) hA hred lam hlam 1 M g 1 hg (by simp)
  rw [Matrix.det_one, (modu_basic (R ⊗[F] E)).2.2.1, one_pow, mul_one, pow_one] at hμ
  obtain ⟨e, he⟩ := exists_homeomorph_lrAct (n := 1) g hg
  obtain ⟨hpos, hν'⟩ := (modu_basic R).1 c hc
  obtain ⟨u, rfl⟩ := hc
  rw [← he] at hμ ⊢
  refine ⟨_, isFibreFamily_transport _ ν _ _ e u _ _ hpos.ne' hμ (hν' ν hν) (fun X => ?_) fib hfib, ?_⟩
  · rw [he, lrAct_one_right]
    exact hq _
  · simp only [Units.inv_mul_cancel_left]

end GlobalTheory.GaugeEx
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx

theorem exists_isProd : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (mi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)), Conv b mi mv → ∃ ν, IsProd b ν mi mv := by
  intro F E _ _ _ _ _ d b n M mi mv hc
  obtain ⟨hi, hv, hs⟩ := hc
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  haveI : Countable (𝓞 F) := Countable.of_equiv _ (RingOfIntegers.basis F).equivFun.symm.toEquiv
  haveI : Countable (Ideal (𝓞 F)) := by
    have hsurj : Function.Surjective (fun s : Finset (𝓞 F) => Ideal.span (s : Set (𝓞 F))) :=
      fun I => (IsNoetherian.noetherian I)
    exact hsurj.countable
  haveI : Countable (HeightOneSpectrum (𝓞 F)) :=
    Function.Injective.countable (f := fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal)
      (fun _ _ h => HeightOneSpectrum.ext h)
  obtain ⟨hint, -⟩ := GlobalTheory.T.integralPointsFinitePlaceTensor_properties F E (AlgHom.id F E) d b
  obtain ⟨hemb, hrange, -, -⟩ := GlobalTheory.T.measurableEmbedding_adelicTuple_localComponents F E d b n M
  have hlat : ∀ v, (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) =
      Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => intV b v := by
    intro v
    ext Y
    rw [mem_latV_iff]
    simp
  have hcpt : ∀ v, IsCompact (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := by
    intro v
    rw [hlat]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => (hint v).1
  have hmeas : ∀ v, MeasurableSet (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := by
    intro v
    rw [hlat]
    exact MeasurableSet.univ_pi fun _ => MeasurableSet.univ_pi fun _ => (hint v).2.measurableSet
  have hsi : SigmaFinite mi := inferInstance
  have hsv : ∀ v, SigmaFinite (mv v) := fun v => by
    haveI := hv v
    infer_instance
  obtain ⟨ν, hν0, hν⟩ := GlobalTheory.T.exists_restricted_product_measure_countable (HeightOneSpectrum (𝓞 F)) _ _ (fun v => latV b v) mi mv hsi hsv hmeas
    (fun v => by haveI := hv v; exact (hcpt v).measure_lt_top.ne) hs
  set e := (fun X : (Fin n → Fin M → AF F ⊗[F] E) =>
    (projInf X, fun v : HeightOneSpectrum (𝓞 F) => projV v (projFin X))) with he
  have hmap : (ν.comap e).map e = ν := by
    rw [hemb.map_comap, hrange]
    exact Measure.restrict_eq_self_of_ae_mem hν0
  refine ⟨ν.comap e, ⟨hi, hv, hs⟩, fun S fi fv hfi hfv => ?_⟩
  have h := hν S fi fv hfi hfv
  rw [← hmap, hemb.restrict_map, hemb.lintegral_map] at h
  exact h

end GlobalTheory.GaugeEx
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx

section

variable {F E : Type} [Field F] [Field E] [Algebra F E]
  (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (B : Matrix (Fin (M + 1)) (Fin M) E)

theorem pairOf_mul_frame (J' : Matrix (Fin M) (Fin M) E) (y : Fin 1 → Fin (M + 1) → R ⊗[F] E)
    (g h : HA R σ J) (h' : HA R σ J') (hh : FrameRelR R σ J J' B h h')
    (y' : Fin 1 → Fin M → R ⊗[F] E) :
    pairOf R σ J B y (g * h) y' = pairOf R σ J B y g (h' • y') := by
  unfold pairOf
  congr 2
  have h1 : (h' • y') 0 = ((HA.mat R σ J' h' : GL (Fin M) (R ⊗[F] E)) :
      Matrix (Fin M) (Fin M) (R ⊗[F] E)).mulVec (y' 0) := rfl
  have h2 : ((HA.mat R σ J (g * h) : GL (Fin (M + 1)) (R ⊗[F] E)) : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) =
      ((HA.mat R σ J g : GL (Fin (M + 1)) (R ⊗[F] E)) : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) *
      ((HA.mat R σ J h : GL (Fin (M + 1)) (R ⊗[F] E)) : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) := rfl
  unfold FrameRelR at hh
  rw [h1, h2]
  simp only [Matrix.mulVec_mulVec]
  rw [Matrix.mul_assoc]
  exact congrArg (fun A => Matrix.mulVec (((HA.mat R σ J g : GL (Fin (M + 1)) (R ⊗[F] E)) :
    Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) * A) (y' 0)) hh

variable [TopologicalSpace R] [FiniteDimensional F E] [IsTopologicalRing R]

theorem continuous_pairOf : Continuous fun p : (Fin 1 → Fin (M + 1) → R ⊗[F] E) × HA R σ J ×
    (Fin 1 → Fin M → R ⊗[F] E) => pairOf R σ J B p.1 p.2.1 p.2.2 := by
  refine continuous_pi fun a => ?_
  fin_cases a
  · exact (by fun_prop : Continuous fun p : (Fin 1 → Fin (M + 1) → R ⊗[F] E) × HA R σ J ×
      (Fin 1 → Fin M → R ⊗[F] E) => p.1 0)
  · exact ((continuous_mat R σ J).comp (continuous_fst.comp continuous_snd)).matrix_mulVec
      (continuous_const.matrix_mulVec
        ((continuous_apply 0).comp (continuous_snd.comp continuous_snd)))

end

theorem twoStep_existsUnique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E) (m : Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : Measure (Fin 1 → Fin M → R ⊗[F] E)), StepData σ J x a B J' → OnOrbit R σ J x m → IsFiniteMeasureOnCompacts m → IsFiniteMeasureOnCompacts m' → IsInvTup R σ J' m' → ∃! N, TwoStep R σ J x B m m' N := by
  intro F E _ _ _ _ _ σ hσ R _ _ _ _ _ _ _ _ _ M J x a B J' m m' hd horb hm hm' hinv
  obtain ⟨-, ⟨e, he, -⟩, -⟩ := GlobalTheory.T.unitary_stabilizer_anisotropic_vector_equiv_complement F E σ hσ R M J x a B J' hd
  obtain ⟨-, s₀, hs₀m, hs₀⟩ := GlobalTheory.T.measurableSet_orbit_exists_measurable_section (HA R σ J) (Fin 1 → Fin (M + 1) → R ⊗[F] E)
    (ratTup (F := F) R x)
  have hP : Measurable fun p : (Fin 1 → Fin (M + 1) → R ⊗[F] E) × HA R σ J ×
      (Fin 1 → Fin M → R ⊗[F] E) => pairOf R σ J B p.1 p.2.1 p.2.2 :=
    (continuous_pairOf R σ J B).measurable
  have hΦ : Measurable fun p : (Fin 1 → Fin (M + 1) → R ⊗[F] E) × (Fin 1 → Fin M → R ⊗[F] E) =>
      pairOf R σ J B p.1 (s₀ p.1) p.2 :=
    hP.comp (measurable_fst.prodMk ((hs₀m.comp measurable_fst).prodMk measurable_snd))
  have hex : TwoStep R σ J x B m m' ((m.prod m').map fun p => pairOf R σ J B p.1 (s₀ p.1) p.2) := by
    intro f hf s hs
    rw [lintegral_map hf hΦ, lintegral_prod (fun p : (Fin 1 → Fin (M + 1) → R ⊗[F] E) ×
      (Fin 1 → Fin M → R ⊗[F] E) => f (pairOf R σ J B p.1 (s₀ p.1) p.2)) (hf.comp hΦ).aemeasurable]
    refine lintegral_congr_ae ?_
    have hae : ∀ᵐ y ∂m, ∃ g : HA R σ J, g • ratTup (F := F) R x = y := horb
    filter_upwards [hae] with y hy
    have hst : (s₀ y)⁻¹ * s y ∈ Hstab R σ J x := by
      change ((s₀ y)⁻¹ * s y) • ratTup (F := F) R x = ratTup (F := F) R x
      rw [mul_smul, hs y hy, inv_smul_eq_iff, hs₀ y hy]
    have hfac : s y = s₀ y * ((s₀ y)⁻¹ * s y) := by group
    have hk : Measurable fun y' => f (pairOf R σ J B y (s₀ y) y') :=
      (hf.comp hΦ).comp measurable_prodMk_left
    have hsm : Measurable fun X : Fin 1 → Fin M → R ⊗[F] E => e ⟨_, hst⟩ • X :=
      (continuous_const_smul _).measurable
    calc ∫⁻ y', f (pairOf R σ J B y (s₀ y) y') ∂m'
        = ∫⁻ y', f (pairOf R σ J B y (s₀ y) y') ∂(m'.map fun X => e ⟨_, hst⟩ • X) := by
          rw [hinv]
      _ = ∫⁻ y', f (pairOf R σ J B y (s₀ y) (e ⟨_, hst⟩ • y')) ∂m' := lintegral_map hk hsm
      _ = ∫⁻ y', f (pairOf R σ J B y (s y) y') ∂m' := by
          refine lintegral_congr fun y' => ?_
          rw [← pairOf_mul_frame R σ J B J' y (s₀ y) _ _ (he ⟨_, hst⟩), ← hfac]
  refine ⟨_, hex, fun N hN => ?_⟩
  ext A hA
  rw [← lintegral_indicator_one hA, ← lintegral_indicator_one hA,
    hN _ (measurable_one.indicator hA) s₀ hs₀, hex _ (measurable_one.indicator hA) s₀ hs₀]

end GlobalTheory.GaugeEx
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.haar_measure_gram_GL2_action_tensor : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], ∀ (lam : Measure (R ⊗[F] E)) (ν : Measure R) (γ : GL (Fin 2) E), lam.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∃ Φ : (R × (R ⊗[F] E) × R) ≃ₜ (R × (R ⊗[F] E) × R), (∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ X : (Fin 2 → Fin M → R ⊗[F] E), gram3 R σ J (lrAct 1 ((γ : Matrix (Fin 2) (Fin 2) E).map (inclR R)) X) = Φ (gram3 R σ J X)) ∧ ν.prod (lam.prod ν) = (modu (R ⊗[F] E) (inclR R (γ : Matrix (Fin 2) (Fin 2) E).det) ^ 2) • (ν.prod (lam.prod ν)).map Φ := by
  first | exact @GlobalTheory.GaugeEx.HermMod.haar_measure_gram_GL2_action | exact GlobalTheory.GaugeEx.HermMod.haar_measure_gram_GL2_action | (intros; apply GlobalTheory.GaugeEx.HermMod.haar_measure_gram_GL2_action <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.integral_witt_theorem_almost_all_places : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (x : Fin 1 → Fin M → E) (β : F), IsHermND σ J → β ≠ 0 → hE σ J (x 0) (x 0) = algebraMap F E β → ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ y ∈ latV (M := M) (n := 1) b v, qR (Fv F v) σ J (y 0) = algebraMap F (Fv F v) β → ∃ g : HA (Fv F v) σ J, g • ratTup (F := F) (Fv F v) x = y ∧ ∀ i j, ((HA.mat (Fv F v) σ J g : GL (Fin M) (Fv F v ⊗[F] E)) : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) i j ∈ intV b v ∧ ((HA.mat (Fv F v) σ J g⁻¹ : GL (Fin M) (Fv F v ⊗[F] E)) : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) i j ∈ intV b v := by
  first | exact @GlobalTheory.WittIntegral.witt_integral | exact GlobalTheory.WittIntegral.witt_integral | (intros; apply GlobalTheory.WittIntegral.witt_integral <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.usage : ∀ (l : ℕ) [Fact l.Prime], IsDomain (Per.Ainf l) ∧ IsDomain (Per.AinfP l) ∧ Function.Injective (algebraMap (Per.Ainf l) (Per.AinfP l)) := by
  first | exact @GlobalTheory.MemLoc.ainf_isDomain_and_injective | exact GlobalTheory.MemLoc.ainf_isDomain_and_injective | (intros; apply GlobalTheory.MemLoc.ainf_isDomain_and_injective <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2.DIV Formalism.L2.Indef

namespace GlobalTheory

theorem rowSide_card_eq_of_coord {D : D7} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE]
    [FiniteDimensional ℂ EE] (X : RowSide D EE) {n d : ℕ} (b : OrthonormalBasis (Fin n) ℂ EE)
    (e : (Fin d → D.what₂.LL) ≃ₗ[D.what₂.LL] X.RR.V) : n = d := by
  let bC : Module.Basis X.RR.ι ℂ EE := Module.Basis.mk X.jEE_basis.1 X.jEE_basis.2.ge
  let bL : Module.Basis (Fin d) D.what₂.LL X.RR.V := (Pi.basisFun D.what₂.LL (Fin d)).map e
  have e1 : Fin n ≃ X.RR.ι := b.toBasis.indexEquiv bC
  have e2 : X.RR.ι ≃ Fin d := X.RR.b.indexEquiv bL
  simpa using Fintype.card_congr (e1.trans e2)

end GlobalTheory
end

section

open Formalism.L2.DIV

theorem _root_.GlobalTheory.T.sum_irrChar_one_mul_irrChar_column_orthogonality : ∀ {G : Type} [inst : Group G] [inst_1 : Fintype G] [inst_2 : DecidableEq G] (A : Finset (G → ℂ)), (∀ ψ, ψ ∈ A ↔ ψ ∈ Formalism.L2.Col.gxIrrSet (G := G) ℂ) → ∀ g : G, ∑ ψ ∈ A, ψ 1 * ψ g = if g = 1 then (Fintype.card G : ℂ) else 0 := by
  first | exact @GlobalTheory.ColumnOrth.sum_char_one_mul_char | exact GlobalTheory.ColumnOrth.sum_char_one_mul_char | (intros; apply GlobalTheory.ColumnOrth.sum_char_one_mul_char <;> assumption)
end

section

open Formalism.L2.DIV

theorem _root_.GlobalTheory.T.absIrrChar_comp_mem_complexIrrCharSet : ∀ {G : Type} [inst : Group G] [inst_1 : Fintype G] {K : Type} [inst_2 : Field K] [inst_3 : CharZero K] (σ : K →+* ℂ) (χ : G → K), IsAbsIrrChar χ → (fun g => σ (χ g)) ∈ Formalism.L2.Col.gxIrrSet (G := G) ℂ := by
  first | exact @GlobalTheory.absIrrChar_comp_mem_gxIrrSet | exact GlobalTheory.absIrrChar_comp_mem_gxIrrSet | (intros; apply GlobalTheory.absIrrChar_comp_mem_gxIrrSet <;> assumption)
end

section

open Formalism.L2.DIV

theorem _root_.GlobalTheory.T.classFunction_acts_by_scalar_on_irrChar : ∀ {G : Type} [inst : Group G] [inst_1 : Fintype G] (e : MonoidAlgebra ℂ G), (∀ x y : G, e.coeff (y * x * y⁻¹) = e.coeff x) → ∀ (ψ : G → ℂ), ψ ∈ Formalism.L2.Col.gxIrrSet (G := G) ℂ → ∀ x : G, ψ 1 * ∑ g, e.coeff g * ψ (g * x) = (∑ g, e.coeff g * ψ g) * ψ x := by
  first | exact @GlobalTheory.classFun_char_scalar | exact GlobalTheory.classFun_char_scalar | (intros; apply GlobalTheory.classFun_char_scalar <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.InertExchange

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.L2.Col

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}


open Classical in
def patchAt (P : HeightOneSpectrum (𝓞 E)) (A B : Submodule (𝓞 E) (Sp E n)) : Submodule (𝓞 E) (Sp E n) :=
  ⨅ Q : HeightOneSpectrum (𝓞 E), localization₂ Q.asIdeal (if Q = P then A else B)

end GlobalTheory.InertExchange
end
end
