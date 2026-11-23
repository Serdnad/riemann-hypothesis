module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle008
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle040
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle041
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle012
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle011
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle028
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle042
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle025
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle004
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle031
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle021
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

@[expose] public section

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.EulerZero

theorem exists_tail_pos {ι : Type} {a : ι → ℝ} (h : Summable (fun v => |a v - 1|)) (S₀ : Finset ι) :
    ∃ S : Finset ι, S₀ ⊆ S ∧ 0 < ∏' v : {v // v ∉ S}, a v.1 := by
  classical
  have hev : ∀ᶠ v in Filter.cofinite, |a v - 1| < 1 :=
    h.tendsto_cofinite_zero.eventually (gt_mem_nhds one_pos)
  have hfin : {v | ¬ |a v - 1| < 1}.Finite := Filter.eventually_cofinite.1 hev
  refine ⟨S₀ ∪ hfin.toFinset, Finset.subset_union_left, ?_⟩
  have hs : Summable (fun v : {v // v ∉ S₀ ∪ hfin.toFinset} => |a v.1 - 1|) :=
    h.comp_injective Subtype.val_injective
  refine (AbsTprod.abs_tprod _ (fun v : {v // v ∉ S₀ ∪ hfin.toFinset} => a v.1) hs).2.2.1 ?_
  rintro ⟨v, hv⟩
  have hv' : |a v - 1| < 1 := by
    by_contra hc
    exact hv (Finset.mem_union_right _ (hfin.mem_toFinset.2 hc))
  have := (abs_lt.1 hv').1
  show 0 < a v
  linarith

theorem countable_places (F : Type) [Field F] [NumberField F] :
    Countable (HeightOneSpectrum (𝓞 F)) := by
  haveI : Countable (𝓞 F) := by
    haveI : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
    exact RingOfIntegers.coe_injective.countable
  haveI : Countable (Ideal (𝓞 F)) := by
    refine Function.Surjective.countable
      (f := fun s : Finset (𝓞 F) => Ideal.span (s : Set (𝓞 F))) ?_
    intro I
    exact (IsNoetherian.noetherian I : I.FG)
  exact Function.Injective.countable (f := fun la : HeightOneSpectrum (𝓞 F) => la.asIdeal)
    fun a b h => HeightOneSpectrum.ext h

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem exists_measure_intOff {d M n : ℕ} {b : Module.Basis (Fin d) F E}
    {I : Measure (Fin n → Fin M → AF F ⊗[F] E)} {c : ℝ≥0}
    {minf : Measure (Fin n → Fin M → Ainf F ⊗[F] E)}
    {m : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)}
    (h : IsEulerProd b I c minf m)
    (hmeas : ∀ S, MeasurableSet (intOff (n := n) (M := M) b S)) :
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₀ ⊆ S →
      I (intOff b S) = (c : ℝ≥0∞) * (minf Set.univ * ∏ v ∈ S, m v Set.univ) *
        ENNReal.ofReal (∏' v : {v // v ∉ S}, (m v.1 (latV b v.1)).toReal) := by
  obtain ⟨-, -, S₀, hS₀⟩ := h
  refine ⟨S₀, fun S hS => ?_⟩
  have key := hS₀ S hS (fun _ => 1) (fun _ _ => 1) measurable_const (fun _ => measurable_const)
  have hp : pureL b S (fun _ => 1) (fun _ _ => 1) = (intOff (n := n) (M := M) b S).indicator 1 := by
    funext X
    simp [pureL, Set.indicator]
  rw [hp, lintegral_indicator_one (hmeas S)] at key
  simpa using key

end GlobalTheory.CompanionTheory.SW.EulerZero


open GlobalTheory.CompanionTheory.SW.EulerZero in
theorem GlobalTheory.CompanionTheory.SW.EulerZero.euler_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (I : Measure (Fin n → Fin M → AF F ⊗[F] E)) (c : ℝ≥0) (minf : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (m : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)), (IsEulerProd b I c minf m → I = 0 → c = 0 ∨ minf = 0 ∨ ∃ v, m v = 0) ∧ (IsEulerProd b I c minf m → (minf = 0 ∨ ∃ v, m v = 0) → I = 0) ∧ ((∀ v, m v (latV b v) < ⊤) → Summable (fun v => |(m v (latV b v)).toReal - 1|) → (minf = 0 ∨ ∃ v, m v = 0) → IsEulerProd b 0 c minf m) := by
  intro F E _ _ _ _ _ σ hσ d b n M I c minf m
  obtain ⟨-, -, -, -, hopen, hcof, -⟩ := GlobalTheory.T.adelic_tuple_projections F E σ hσ d b n M
  obtain ⟨⟨hlc, hsc, ht2⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  obtain ⟨-, -, -, -, -, -, -, hborel, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (AF F)
  haveI := hborel n M
  have hmeas : ∀ S, MeasurableSet (intOff (n := n) (M := M) b S) := fun S => (hopen S).measurableSet
  refine ⟨fun h hI => ?_, fun h hz => ?_, fun hfin hsum hz => ?_⟩
  · by_contra hcon
    push_neg at hcon
    obtain ⟨hc, hminf, hm⟩ := hcon
    obtain ⟨S₀, hS₀⟩ := exists_measure_intOff h hmeas
    obtain ⟨S, hS, hpos⟩ := exists_tail_pos h.2.1 S₀
    have key := hS₀ S hS
    rw [hI] at key
    have h1 : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc
    have h2 : minf Set.univ ≠ 0 := by simpa using hminf
    have h3 : ∏ v ∈ S, m v Set.univ ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun v _ => by simpa using hm v
    have h4 : ENNReal.ofReal (∏' v : {v // v ∉ S}, (m v.1 (latV b v.1)).toReal) ≠ 0 := by
      simpa using hpos
    exact (mul_ne_zero (mul_ne_zero h1 (mul_ne_zero h2 h3)) h4) (by simpa using key.symm)
  · obtain ⟨S₀, hS₀⟩ := exists_measure_intOff h hmeas
    classical
    obtain ⟨S₁, hS₁, hzero⟩ : ∃ S₁ : Finset (HeightOneSpectrum (𝓞 F)), S₀ ⊆ S₁ ∧
        ∀ S, S₁ ⊆ S → minf Set.univ * ∏ v ∈ S, m v Set.univ = 0 := by
      rcases hz with hz | ⟨v, hv⟩
      · exact ⟨S₀, subset_rfl, fun S _ => by simp [hz]⟩
      · refine ⟨insert v S₀, Finset.subset_insert _ _, fun S hS => ?_⟩
        rw [Finset.prod_eq_zero (hS (Finset.mem_insert_self v S₀)) (by simp [hv]), mul_zero]
    haveI := countable_places F
    have hcover : (Set.univ : Set (Fin n → Fin M → AF F ⊗[F] E)) ⊆
        ⋃ T : Finset (HeightOneSpectrum (𝓞 F)), intOff b (S₁ ∪ T) := by
      intro X _
      have hT := Filter.eventually_cofinite.1 (hcof (projFin X))
      refine Set.mem_iUnion.2 ⟨hT.toFinset, fun v hv => ?_⟩
      by_contra hc
      exact hv (Finset.mem_union_right _ (hT.mem_toFinset.2 hc))
    have hnull : I Set.univ = 0 := by
      refine measure_mono_null hcover (measure_iUnion_null fun T => ?_)
      rw [hS₀ _ (hS₁.trans Finset.subset_union_left), hzero _ Finset.subset_union_left]
      simp
    exact Measure.measure_univ_eq_zero.1 hnull
  · refine ⟨hfin, hsum, ?_⟩
    classical
    obtain ⟨S₀, hS₀⟩ : ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), minf = 0 ∨ ∃ v ∈ S₀, m v = 0 := by
      rcases hz with hz | ⟨v, hv⟩
      · exact ⟨∅, Or.inl hz⟩
      · exact ⟨{v}, Or.inr ⟨v, by simp, hv⟩⟩
    refine ⟨S₀, fun S hS φinf φ _ _ => ?_⟩
    rcases hS₀ with hz | ⟨v, hv, hmv⟩
    · simp [hz]
    · rw [Finset.prod_eq_zero (hS hv) (by simp [hmv])]
      simp
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.BB

theorem finDensity_coord : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (B : Matrix (Fin M × Fin d) (Fin M × Fin d) F), (∀ x y : Fin M → Af F ⊗[F] E, Algebra.trace (Af F) (Af F ⊗[F] E) (hR (Af F) σ J x y) = cv (Af F) b x ⬝ᵥ (B.map (algebraMap F (Af F)) *ᵥ cv (Af F) b y)) → ∀ (lf : Measure (Af F)), lf.IsAddHaarMeasure → ∀ (a : ℕ) (U : Set (Af F)), coordW (Af F) b lf 1 M {X | (∀ v, projV v X ∈ {X : (Fin 1 → Fin M → Fv F v ⊗[F] E) | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v}) ∧ algebraMap F (Af F) (1 / 2) * Algebra.trace (Af F) (Af F ⊗[F] E) (gramR (Af F) σ J X 0 0) ∈ U} = (Measure.pi fun _ : Fin M × Fin d => lf) {x | (∀ i v, ((a : Af F) * x i) v ∈ v.adicCompletionIntegers F) ∧ algebraMap F (Af F) (1 / 2) * (x ⬝ᵥ (B.map (algebraMap F (Af F)) *ᵥ x)) ∈ U} := by
  intro F E _ _ _ _ _ σ hCM M J hJ d b B hB lf hlf a U
  obtain ⟨-, h1, h2, h3⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  obtain ⟨-, hme, hmap⟩ := GlobalTheory.T.coordinate_homeomorph_rank_one_tuples F E σ hCM (Af F) d b lf hlf M
  rw [← hmap, hme.map_apply]
  congr 1
  ext X
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  have hl := GlobalTheory.T.finite_adelic_lattice_membership_iff F E d M b a X
  have ht : gramR (Af F) σ J X 0 0 = hR (Af F) σ J (X 0) (X 0) := rfl
  rw [ht, hB, ← hl]

end GlobalTheory.CompanionTheory.SW.BB
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.archimedean_local_density_formula : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (B : Matrix (Fin M × Fin d) (Fin M × Fin d) F), (∀ x y : Fin M → Ainf F ⊗[F] E, Algebra.trace (Ainf F) (Ainf F ⊗[F] E) (hR (Ainf F) σ J x y) = cv (Ainf F) b x ⬝ᵥ (B.map (algebraMap F (Ainf F)) *ᵥ cv (Ainf F) b y)) → ∀ (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), IsHomeomorph e → (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) → ∀ (Pm : InfinitePlace F → Matrix (Fin M × Fin d) (Fin M × Fin d) ℝ) (laminf : Measure (Ainf F)), laminf.IsAddHaarMeasure → laminf.map e = ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|)⁻¹ • (volume : Measure (InfinitePlace F → ℝ)) → ∀ Dinf : (InfinitePlace F → ℝ) → ℝ, Continuous Dinf → (∀ y, 0 ≤ Dinf y) → (∀ U : Set (InfinitePlace F → ℝ), MeasurableSet U → ∫⁻ x in {x : InfinitePlace F → Fin M × Fin d → ℝ | (fun w => (1 / 2 : ℝ) * (x w ⬝ᵥ (B.map (ρ w) *ᵥ x w))) ∈ U}, ENNReal.ofReal (Real.exp (-Real.pi * ∑ w, x w ⬝ᵥ (Pm w *ᵥ x w))) = ∫⁻ y in U, ENNReal.ofReal (Dinf y)) → ∀ U : Set (HermR (Ainf F) σ 1), MeasurableSet U → ∫⁻ X in gramR (Ainf F) σ J ⁻¹' (Subtype.val '' U), ENNReal.ofReal (gaussQ e b Pm X) ∂(coordW (Ainf F) b laminf 1 M) = ∫⁻ S in U, ENNReal.ofReal ((Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (2 * M - 1) * Dinf (e (algebraMap F (Ainf F) (1 / 2) * Algebra.trace (Ainf F) (Ainf F ⊗[F] E) ((S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) 0 0)))) ∂(coordHerm (Ainf F) σ b laminf 1) := by
  first | exact @GlobalTheory.CompanionTheory.SW.BB.InfDens.infDens | exact GlobalTheory.CompanionTheory.SW.BB.InfDens.infDens | (intros; apply GlobalTheory.CompanionTheory.SW.BB.InfDens.infDens <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.gram_coordinates_measurable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), IsHomeomorph e → (∀ w p q, Measurable fun ω => ginf e σ J b ω w p q) ∧ (∀ p q, Measurable fun ω => gfin σ J b ω p q) := by
  first | exact @GlobalTheory.CompanionTheory.SW.BB.ginf_gfin_measurable | exact GlobalTheory.CompanionTheory.SW.BB.ginf_gfin_measurable | (intros; apply GlobalTheory.CompanionTheory.SW.BB.ginf_gfin_measurable <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.GoodIso

theorem exists_gl_to_one (A : Type) [CommRing A] [Finite (MaximalSpectrum A)] (σ : A →+* A)
    (hσ : ∀ y, σ (σ y) = y) (h2 : IsUnit (2 : A)) (hδ : ∃ δ : A, IsUnit δ ∧ σ δ = -δ)
    (hN : ∀ β : A, IsUnit β → σ β = β → ∃ a : A, a * σ a = β)
    (m : ℕ) (J : Matrix (Fin m) (Fin m) A) (hJ : ∀ i j, σ (J j i) = J i j) (hd : IsUnit J.det) :
    ∃ h : GL (Fin m) A,
      cT σ (h : Matrix (Fin m) (Fin m) A) * J * (h : Matrix (Fin m) (Fin m) A) = 1 := by
  obtain ⟨g, d, hg, hdd, hgJ⟩ := GlobalTheory.T.hermitian_unit_form_diagonalizes A σ hσ
    (fun m J hJ hu => GlobalTheory.T.hermitian_unit_form_represents_unit A σ hσ h2 hδ m J hJ hu) m J hJ hd
  choose a ha using fun i => hN (d i) (hdd i).1 (hdd i).2
  have hau : ∀ i, IsUnit (a i) := fun i =>
    isUnit_of_mul_isUnit_left (y := σ (a i)) (by rw [ha i]; exact (hdd i).1)
  choose c hc using fun i => (hau i).exists_right_inv
  have hcu : ∀ i, IsUnit (c i) := fun i => IsUnit.of_mul_eq_one (a i) (by rw [mul_comm]; exact hc i)
  have hdet : IsUnit (g * Matrix.diagonal c).det := by
    rw [Matrix.det_mul, Matrix.det_diagonal]
    exact hg.mul (IsUnit.prod_univ_iff.2 hcu)
  refine ⟨((Matrix.isUnit_iff_isUnit_det _).2 hdet).unit, ?_⟩
  rw [IsUnit.unit_spec, cT_mul]
  have hD : cT σ (Matrix.diagonal c) = Matrix.diagonal (fun i => σ (c i)) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [cT]
    · simp [cT, Matrix.diagonal_apply, hij, Ne.symm hij]
  calc cT σ (Matrix.diagonal c) * cT σ g * J * (g * Matrix.diagonal c)
      = cT σ (Matrix.diagonal c) * (cT σ g * J * g) * Matrix.diagonal c := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [hgJ, hD, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
        congr 1
        funext i
        have h1 : σ (c i) * σ (a i) = 1 := by rw [← map_mul, mul_comm, hc i, map_one]
        rw [← ha i]
        calc σ (c i) * (a i * σ (a i)) * c i = (σ (c i) * σ (a i)) * (a i * c i) := by ring
          _ = 1 := by rw [h1, hc i, one_mul]

theorem exists_gl_equiv (A : Type) [CommRing A] [Finite (MaximalSpectrum A)] (σ : A →+* A)
    (hσ : ∀ y, σ (σ y) = y) (h2 : IsUnit (2 : A)) (hδ : ∃ δ : A, IsUnit δ ∧ σ δ = -δ)
    (hN : ∀ β : A, IsUnit β → σ β = β → ∃ a : A, a * σ a = β)
    (m : ℕ) (J J' : Matrix (Fin m) (Fin m) A) (hJ : ∀ i j, σ (J j i) = J i j) (hd : IsUnit J.det)
    (hJ' : ∀ i j, σ (J' j i) = J' i j) (hd' : IsUnit J'.det) :
    ∃ G : GL (Fin m) A,
      J' = cT σ (G : Matrix (Fin m) (Fin m) A) * J * (G : Matrix (Fin m) (Fin m) A) := by
  obtain ⟨h, hh⟩ := exists_gl_to_one A σ hσ h2 hδ hN m J hJ hd
  obtain ⟨k, hk⟩ := exists_gl_to_one A σ hσ h2 hδ hN m J' hJ' hd'
  refine ⟨h * k⁻¹, ?_⟩
  have hkk : (k : Matrix (Fin m) (Fin m) A) * ((k⁻¹ : GL (Fin m) A) : Matrix (Fin m) (Fin m) A) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hck : cT σ ((k⁻¹ : GL (Fin m) A) : Matrix (Fin m) (Fin m) A) * cT σ (k : Matrix (Fin m) (Fin m) A) = 1 := by
    rw [← cT_mul, hkk, cT_one]
  set K : Matrix (Fin m) (Fin m) A := (k : Matrix (Fin m) (Fin m) A)
  set L : Matrix (Fin m) (Fin m) A := ((k⁻¹ : GL (Fin m) A) : Matrix (Fin m) (Fin m) A)
  set H : Matrix (Fin m) (Fin m) A := (h : Matrix (Fin m) (Fin m) A)
  have e1 : J' = cT σ L * (cT σ K * J' * K) * L := by
    calc J' = (cT σ L * cT σ K) * J' * (K * L) := by rw [hck, hkk, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  have e2 : cT σ (H * L) * J * (H * L) = cT σ L * (cT σ H * J * H) * L := by
    rw [cT_mul]; simp only [Matrix.mul_assoc]
  rw [Units.val_mul]
  change J' = cT σ (H * L) * J * (H * L)
  rw [e2, hh, ← hk, ← e1]

theorem exists_gl_sub {R : Type} [CommRing R] (s : R →+* R) (hs : ∀ y, s (s y) = y) (O : Subring R)
    (hO : ∀ y ∈ O, s y ∈ O) [Finite (MaximalSpectrum O)] (h2 : IsUnit (2 : O))
    (hδ : ∃ δ : O, IsUnit δ ∧ s (δ : R) = -(δ : R))
    (hN : ∀ β : O, IsUnit β → s (β : R) = β → ∃ a : O, (a : R) * s a = β)
    (m : ℕ) (K K' : Matrix (Fin m) (Fin m) R)
    (hK : ∀ i j, s (K j i) = K i j) (hK' : ∀ i j, s (K' j i) = K' i j)
    (iK : ∀ i j, K i j ∈ O) (iK' : ∀ i j, K' i j ∈ O)
    (wK : ∃ w ∈ O, K.det * w = 1) (wK' : ∃ w ∈ O, K'.det * w = 1) :
    ∃ g : GL (Fin m) R, K' = cT s (g : Matrix (Fin m) (Fin m) R) * K * (g : Matrix (Fin m) (Fin m) R) ∧
      (∀ i j, (g : Matrix (Fin m) (Fin m) R) i j ∈ O) ∧
      ∀ i j, ((g⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) i j ∈ O := by
  let σO : O →+* O := (s.comp O.subtype).codRestrict O (fun y => hO y y.2)
  have lift : ∀ (P : Matrix (Fin m) (Fin m) R) (iP : ∀ i j, P i j ∈ O), (∃ w ∈ O, P.det * w = 1) →
      ∃ Q : Matrix (Fin m) (Fin m) O, Q.map O.subtype = P ∧ IsUnit Q.det := by
    intro P iP ⟨w, hw, hPw⟩
    refine ⟨Matrix.of fun i j => ⟨P i j, iP i j⟩, by ext i j; rfl, ?_⟩
    have hdet : ((Matrix.of fun i j => (⟨P i j, iP i j⟩ : O)).det : O).1 = P.det := by
      have := RingHom.map_det O.subtype (Matrix.of fun i j => (⟨P i j, iP i j⟩ : O))
      exact this
    refine IsUnit.of_mul_eq_one ⟨w, hw⟩ (Subtype.ext ?_)
    simpa [hdet] using hPw
  obtain ⟨Q, rfl, uQ⟩ := lift K iK wK
  obtain ⟨Q', rfl, uQ'⟩ := lift K' iK' wK'
  have herm : ∀ (Q : Matrix (Fin m) (Fin m) O), (∀ i j, s ((Q.map O.subtype) j i) = (Q.map O.subtype) i j) →
      ∀ i j, σO (Q j i) = Q i j := fun Q h i j => Subtype.ext (h i j)
  obtain ⟨G, hG⟩ := exists_gl_equiv O σO (fun y => Subtype.ext (hs _)) h2
    (by obtain ⟨δ, h1, h3⟩ := hδ; exact ⟨δ, h1, Subtype.ext h3⟩)
    (fun β hβ hβ' => by
      obtain ⟨a, ha⟩ := hN β hβ (congrArg Subtype.val hβ')
      exact ⟨a, Subtype.ext ha⟩)
    m Q Q' (herm Q hK) uQ (herm Q' hK') uQ'
  have hcT : ∀ P : Matrix (Fin m) (Fin m) O,
      cT s (P.map O.subtype) = (cT σO P).map O.subtype := fun P => by ext i j; rfl
  refine ⟨bc O.subtype G, ?_, ?_, ?_⟩
  · have hv : ((bc O.subtype G : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) =
        (G : Matrix (Fin m) (Fin m) O).map O.subtype := rfl
    rw [hv, hcT, hG, Matrix.map_mul, Matrix.map_mul]
  · intro i j
    exact (G.val i j).2
  · intro i j
    rw [← map_inv]
    exact ((G⁻¹).val i j).2

theorem sigma_sigma {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2]
  simp

theorem sigR_sigR {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (h : ∀ x, σ (σ x) = x) (y : R ⊗[F] E) : sigR R σ (sigR R σ y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [sigR, h]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem mulVec_mem {R : Type} [CommRing R] (O : Subring R) {m : ℕ} (P : Matrix (Fin m) (Fin m) R)
    (hP : ∀ i j, P i j ∈ O) (x : Fin m → R) (hx : ∀ i, x i ∈ O) (i : Fin m) : P.mulVec x i ∈ O := by
  change ∑ j, P i j * x j ∈ O
  exact O.sum_mem fun j _ => O.mul_mem (hP i j) (hx j)

theorem good_iso : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (J' : Matrix (Fin M) (Fin M) E), IsHermND σ J' → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ g : GL (Fin M) (Fv F v ⊗[F] E), JR (Fv F v) J' = cT (sigR (Fv F v) σ) (g : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) * JR (Fv F v) J * (g : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) ∧ ∀ (n : ℕ) (X : Fin n → Fin M → Fv F v ⊗[F] E), actTup (Fv F v) g X ∈ latV b v ↔ X ∈ latV b v := by
  intro F E _ _ _ _ _ σ hCM M J hJ J' hJ' d b
  have h1 := (GlobalTheory.T.integral_almost_all_places F E σ hCM d b).1
  have ent : ∀ P : Matrix (Fin M) (Fin M) E, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ i j k, (Algebra.TensorProduct.basis (Fv F v) b).repr (inclR (F := F) (Fv F v) (P i j)) k ∈
        v.adicCompletionIntegers F := fun P =>
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => h1 (P i j)
  filter_upwards [GlobalTheory.T.tensor_integer_ring_almost_all_places F E σ hCM d b, ent J, ent J', h1 (J.det)⁻¹, h1 (J'.det)⁻¹]
    with v hv eJ eJ' dJ dJ'
  obtain ⟨O, hmem, hst, hfin, h2, hδ, -, hN⟩ := hv
  have wit : ∀ P : Matrix (Fin M) (Fin M) E, P.det ≠ 0 →
      (∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr (inclR (F := F) (Fv F v) (P.det)⁻¹) k ∈
        v.adicCompletionIntegers F) → ∃ w ∈ O, (JR (Fv F v) P).det * w = 1 := by
    intro P hP hk
    refine ⟨inclR (F := F) (Fv F v) (P.det)⁻¹, (hmem _).2 hk, ?_⟩
    have : (JR (Fv F v) P).det = inclR (F := F) (Fv F v) P.det := (RingHom.map_det (inclR (F := F) (Fv F v)) P).symm
    rw [this, ← map_mul, mul_inv_cancel₀ hP, map_one]
  obtain ⟨g, hg, ig, ig'⟩ := exists_gl_sub (sigR (Fv F v) σ)
    (sigR_sigR (Fv F v) σ (sigma_sigma σ hCM)) O hst h2 hδ hN M (JR (Fv F v) J) (JR (Fv F v) J')
    (map_mem_HermR (Fv F v) σ J hJ.1) (map_mem_HermR (Fv F v) σ J' hJ'.1)
    (fun i j => (hmem _).2 (eJ i j)) (fun i j => (hmem _).2 (eJ' i j))
    (wit J hJ.2 dJ) (wit J' hJ'.2 dJ')
  refine ⟨g, hg, fun n X => ?_⟩
  have lat : ∀ Y : Fin n → Fin M → Fv F v ⊗[F] E, Y ∈ latV b v ↔ ∀ a i, Y a i ∈ O := fun Y =>
    ⟨fun h a i => (hmem _).2 (h a i), fun h a i => (hmem _).1 (h a i)⟩
  rw [lat, lat]
  constructor
  · intro h a i
    have e : X a = ((g⁻¹ : GL (Fin M) (Fv F v ⊗[F] E)) : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)).mulVec
        (actTup (Fv F v) g X a) := by
      simp only [actTup, Matrix.mulVec_mulVec]
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    rw [e]
    exact mulVec_mem O _ ig' _ (h a) i
  · intro h a i
    exact mulVec_mem O _ ig _ (h a) i

end GlobalTheory.CompanionTheory.SW.GoodIso
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.haar_fundamental_domain_exists_unitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → (∃ μ, IsHaarH F E σ M J μ) ∧ ∀ μ, IsHaarH F E σ M J μ → (∃ 𝓕, IsFDH F E σ M J μ 𝓕) ∧ (∃ 𝓕, MeasurableSet 𝓕 ∧ IsFDH F E σ M J μ 𝓕 ∧ ∀ h : HA (AF F) σ J, ∃ γ : HA (AF F) σ J, HA.mat (AF F) σ J γ ∈ HFin (AF F) σ J ∧ γ * h ∈ 𝓕) ∧ ∀ 𝓕, IsFDH F E σ M J μ 𝓕 → μ 𝓕 ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.SW.haar_fundamental_exist | exact GlobalTheory.CompanionTheory.SW.haar_fundamental_exist | (intros; apply GlobalTheory.CompanionTheory.SW.haar_fundamental_exist <;> assumption)
end
