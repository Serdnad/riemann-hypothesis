module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle047
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle009
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicBoxesCompactExhaust
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle039
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle018
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle024
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle008
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle028
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle040
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle041
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.PNatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace GlobalTheory.CompanionTheory.SW.Core.AfTop

variable (F : Type) [Field F] [NumberField F]

theorem isCompact_Oh : IsCompact (Oh F) :=
  (GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties F).1

theorem isOpen_Oh : IsOpen (Oh F) := by
  haveI : Fact (∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    ⟨fun _ ↦ Valued.isOpen_valuationSubring _⟩
  exact RestrictedProduct.isOpen_forall_mem
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Fact.out

theorem natCast_mul_mem_Oh (N : ℕ) {x : A F} (hx : x ∈ Oh F) : (N : A F) * x ∈ Oh F := by
  induction N with
  | zero =>
    intro v
    rw [Nat.cast_zero, zero_mul]
    exact zero_mem (v.adicCompletionIntegers F)
  | succ n ih =>
    intro v
    rw [Nat.cast_succ, add_mul, one_mul]
    exact add_mem (ih v) (hx v)

theorem algebraMap_mem_Oh_iff (b : F) : algebraMap F (A F) b ∈ Oh F ↔ ∃ r : 𝓞 F, (r : F) = b := by
  constructor
  · intro h
    obtain ⟨y, hy⟩ := (GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.1 b h
    exact ⟨y, hy.symm⟩
  · rintro ⟨r, rfl⟩ v
    exact HeightOneSpectrum.coe_mem_adicCompletionIntegers v r

theorem exists_mul_Oh_subset (U : Set (A F)) (hU : U ∈ 𝓝 (0 : A F)) :
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ Oh F, (N : A F) * x ∈ U := by
  obtain ⟨h1, h2, h3, -⟩ := GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties F
  let V : ℕ+ → Set (A F) := fun N => {a | ∃ c ∈ Oh F, a = ((N : ℕ) : A F) * c}
  have hV : Directed (· ⊇ ·) V := by
    intro M N
    refine ⟨M * N, ?_, ?_⟩
    · rintro _ ⟨c, hc, rfl⟩
      exact ⟨_, natCast_mul_mem_Oh F N hc, by push_cast; ring⟩
    · rintro _ ⟨c, hc, rfl⟩
      exact ⟨_, natCast_mul_mem_Oh F M hc, by push_cast; ring⟩
  have hc : ∀ N, IsCompact (V N) := by
    intro N
    have : V N = (fun c => ((N : ℕ) : A F) * c) '' Oh F := by
      ext a
      simp only [V, Set.mem_setOf_eq, Set.mem_image, eq_comm]
    rw [this]
    exact (isCompact_Oh F).image (continuous_const.mul continuous_id)
  obtain ⟨N, hN⟩ := exists_subset_nhds_of_isCompact' hV hc (fun N => h2 N N.pos) (U := U) (by
    apply mem_nhdsSet_iff_forall.mpr
    intro x hx
    have : x = 0 := h3 x fun M hM => Set.mem_iInter.1 hx ⟨M, hM⟩
    rwa [this])
  exact ⟨N, N.pos, fun x hx => hN ⟨x, hx, rfl⟩⟩

theorem exists_mul_mem_Oh_of_isCompact (K : Set (A F)) (hK : IsCompact K) :
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ K, (N : A F) * x ∈ Oh F := by
  let V : ℕ+ → Set (A F) := fun N => {a | ((N : ℕ) : A F) * a ∈ Oh F}
  have hV : Directed (· ⊆ ·) V := by
    intro M N
    refine ⟨M * N, fun a ha => ?_, fun a ha => ?_⟩
    · have := natCast_mul_mem_Oh F N ha
      show (((M * N : ℕ+) : ℕ) : A F) * a ∈ Oh F
      convert this using 1
      push_cast; ring
    · have := natCast_mul_mem_Oh F M ha
      show (((M * N : ℕ+) : ℕ) : A F) * a ∈ Oh F
      convert this using 1
      push_cast; ring
  obtain ⟨N, hN⟩ := hK.elim_directed_cover V
    (fun N => (isOpen_Oh F).preimage (continuous_const.mul continuous_id)) (fun a _ => by
      obtain ⟨M, hM, h⟩ := (GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.2.1 a
      exact Set.mem_iUnion.2 ⟨⟨M, hM⟩, h⟩) hV
  exact ⟨N, N.pos, fun x hx => hN hx⟩

theorem isOpen_mul_Oh (N : ℕ) (hN : 0 < N) :
    IsOpen {x : A F | ∃ y ∈ Oh F, x = (N : A F) * y} := by
  have hN' : (N : F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have h1 : (N : A F) * algebraMap F (A F) (N : F)⁻¹ = 1 := by
    rw [← map_natCast (algebraMap F (A F)), ← map_mul, mul_inv_cancel₀ hN', map_one]
  have : {x : A F | ∃ y ∈ Oh F, x = (N : A F) * y} =
      (fun x => algebraMap F (A F) (N : F)⁻¹ * x) ⁻¹' Oh F := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      show _ * (_ * y) ∈ Oh F
      rwa [← mul_assoc, mul_comm _ (N : A F), h1, one_mul]
    · intro hx
      exact ⟨_, hx, by rw [← mul_assoc, h1, one_mul]⟩
  rw [this]
  exact (isOpen_Oh F).preimage (continuous_const.mul continuous_id)

theorem denseRange_algebraMap : DenseRange (algebraMap F (A F)) := by
  intro y
  rw [mem_closure_iff_nhds]
  intro U hU
  have hc : Continuous fun z : A F => y - z := continuous_const.sub continuous_id
  have hU' : (fun z : A F => y - z) ⁻¹' U ∈ 𝓝 (0 : A F) :=
    hc.continuousAt.preimage_mem_nhds (by simpa using hU)
  obtain ⟨N, hN, h⟩ := exists_mul_Oh_subset F _ hU'
  obtain ⟨x, a, ha, hy⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat F N hN).1 y
  refine ⟨algebraMap F (A F) x, ?_, x, rfl⟩
  have h2 : y - (N : A F) * a ∈ U := h a ha
  have h3 : y - (N : A F) * a = algebraMap F (A F) x := by
    rw [sub_eq_iff_eq_add, ← nsmul_eq_mul]
    exact hy
  rwa [h3] at h2

theorem finiteAdele_topology : ∀ (F : Type) [Field F] [NumberField F], LocallyCompactSpace (A F) ∧ SecondCountableTopology (A F) ∧ T2Space (A F) ∧ IsCompact (Oh F) ∧ IsOpen (Oh F) ∧ DenseRange (algebraMap F (A F)) ∧ (∀ b : F, algebraMap F (A F) b ∈ Oh F ↔ ∃ r : 𝓞 F, (r : F) = b) ∧ (∀ U ∈ 𝓝 (0 : A F), ∃ N : ℕ, 0 < N ∧ ∀ x ∈ Oh F, (N : A F) * x ∈ U) ∧ (∀ K : Set (A F), IsCompact K → ∃ N : ℕ, 0 < N ∧ ∀ x ∈ K, (N : A F) * x ∈ Oh F) ∧ ∀ N : ℕ, 0 < N → IsOpen {x : A F | ∃ y ∈ Oh F, x = (N : A F) * y} :=
  fun F _ _ => ⟨GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F,
    GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F, GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F,
    isCompact_Oh F, isOpen_Oh F, denseRange_algebraMap F, algebraMap_mem_Oh_iff F,
    exists_mul_Oh_subset F, exists_mul_mem_Oh_of_isCompact F, isOpen_mul_Oh F⟩

end GlobalTheory.CompanionTheory.SW.Core.AfTop
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.adelic_boxes_compact_exhaust : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ), (∀ (N : ℕ) (r : ℝ), 0 < N → IsCompact (box b N r : Set (Fin n → Fin M → AF F ⊗[F] E))) ∧ (∀ C : Set (Fin n → Fin M → AF F ⊗[F] E), IsCompact C → ∃ (N : ℕ) (r : ℝ), 0 < N ∧ 0 < r ∧ C ⊆ box b N r) ∧ ∀ τ : Multiplicative ℝ →* (AF F ⊗[F] E)ˣ, IsFlow τ → ∀ (N : ℕ) (r x : ℝ) (X : Fin n → Fin M → AF F ⊗[F] E), ((τ (Multiplicative.ofAdd (x)) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • X ∈ box b N (Real.exp x * r) ↔ X ∈ box b N r := by
  first | exact @GlobalTheory.CompanionTheory.SW.BoxF.box_facts | exact GlobalTheory.CompanionTheory.SW.BoxF.box_facts | (intros; apply GlobalTheory.CompanionTheory.SW.BoxF.box_facts <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.haar_scaling_under_flow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ τ : Multiplicative ℝ →* (AF F ⊗[F] E)ˣ, IsFlow τ → ∀ (n M : ℕ) (μ : Measure (Fin n → Fin M → AF F ⊗[F] E)), μ.IsAddHaarMeasure → ∀ x : ℝ, μ.map (fun X => ((τ (Multiplicative.ofAdd (x)) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • X) = ENNReal.ofReal (Real.exp (-(2 * Module.finrank ℚ F * n * M * x))) • μ := by
  first | exact @GlobalTheory.CompanionTheory.SW.Flow.modulus_flow | exact GlobalTheory.CompanionTheory.SW.Flow.modulus_flow | (intros; apply GlobalTheory.CompanionTheory.SW.Flow.modulus_flow <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.GramNear

theorem fibre_on_orbit (V X Y : Type) [AddCommGroup V] [TopologicalSpace V] [LocallyCompactSpace V]
    [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [IsTopologicalAddGroup V]
    [AddCommGroup X] [TopologicalSpace X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] [IsTopologicalAddGroup X]
    (μ : Measure V) (ν : Measure X) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    (f : V → Y) (g : V → X) (ι : X → Y) (hι : Function.Injective ι) (hg : Continuous g)
    (hf : ∀ v, f v = ι (g v))
    (Q : Type) [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [LocallyCompactSpace Q]
    [SecondCountableTopology Q] [T2Space Q] [DistribMulAction Q V] [ContinuousSMul Q V]
    [DistribMulAction Q X] [ContinuousSMul Q X]
    (heq : ∀ (q : Q) (v : V), g (q • v) = q • g v) (b₀ : X)
    (ho : IsOpenEmbedding (fun q : Q => q • b₀)) :
    ∃ fib : X → Measure V, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' (Set.range fun q : Q => q • b₀)) ν
      (Set.range fun q : Q => q • b₀) fib := by
  obtain ⟨χ, hχ, hμ⟩ := GlobalTheory.T.haar_modular_character_of_continuous_action V μ Q
  obtain ⟨χ', hχ', hν⟩ := GlobalTheory.T.haar_modular_character_of_continuous_action X ν Q
  exact GlobalTheory.T.exists_fibre_family_on_open_orbit V X Y μ ν f g ι hι hg hf Q heq χ χ' hχ hχ' hμ hν b₀ ho

theorem exists_fibre_near : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ) (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∀ S : HermR R σ n, IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det → ∃ B : Set (HermR R σ n), IsOpen B ∧ S ∈ B ∧ (∀ S' ∈ B, IsUnit (S' : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det) ∧ ∃ fib, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ (gramR R σ J) Subtype.val (gramR R σ J ⁻¹' (Subtype.val '' B)) ν B fib := by
  intro F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hR n μ ν hμ hν S hS
  have hR' := hR
  obtain ⟨_, _, _, _, -, -, -, -⟩ := hR'
  obtain ⟨_, _, _, _, hsig, -, -, hbor, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R
  have hbor' := hbor n M
  obtain ⟨_, _, _, _, hlift⟩ := GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ hσ R n
  obtain ⟨g, hgc, hgf⟩ := hlift M J hJ
  obtain ⟨hgram, hmul, hone, hherm, -⟩ := GlobalTheory.T.gram_right_action_identities F E σ hσ M J hJ R n
  obtain ⟨Q, o, _, _, hoe, ho⟩ := GlobalTheory.T.hermitian_orbit_local_section_subgroup F E σ hσ R hR n S hS

  let c : Q → Matrix (Fin n) (Fin n) (R ⊗[F] E) := fun q => (((q⁻¹ : Q) : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E))
  have hc1 : c 1 = 1 := by simp [c]
  have hcm : ∀ a b : Q, c (a * b) = c b * c a := by
    intro a b
    simp only [c, mul_inv_rev]
    rfl
  have hcc : Continuous c := Units.continuous_val.comp (continuous_subtype_val.comp continuous_inv)
  letI actV : DistribMulAction Q (Fin n → Fin M → R ⊗[F] E) :=
    { smul := fun q X => rmul R X (c q)
      one_smul := fun X => by
        change rmul R X (c 1) = X
        rw [hc1, hone]
      mul_smul := fun a b X => by
        change rmul R X (c (a * b)) = rmul R (rmul R X (c b)) (c a)
        rw [hcm, hmul]
      smul_zero := fun q => by
        change rmul R 0 (c q) = 0
        funext a i; simp [rmul]
      smul_add := fun q X Y => by
        change rmul R (X + Y) (c q) = rmul R X (c q) + rmul R Y (c q)
        funext a i; simp [rmul, add_mul, Finset.sum_add_distrib] }
  have hsmulV : ∀ (q : Q) (X : Fin n → Fin M → R ⊗[F] E), q • X = rmul R X (c q) := fun _ _ => rfl
  letI actH : DistribMulAction Q (HermR R σ n) :=
    { smul := fun q T => ⟨cT (sigR R σ) (c q) * (T : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * c q, hherm T (c q)⟩
      one_smul := fun T => by
        apply Subtype.ext
        change cT (sigR R σ) (c 1) * (T : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * c 1 = T
        rw [hc1]; simp [cT]
      mul_smul := fun a b T => by
        apply Subtype.ext
        change cT (sigR R σ) (c (a * b)) * (T : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * c (a * b) =
          cT (sigR R σ) (c a) * (cT (sigR R σ) (c b) * (T : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * c b) * c a
        rw [hcm]
        simp only [cT, Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]
      smul_zero := fun q => by
        apply Subtype.ext
        change cT (sigR R σ) (c q) * (0 : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * c q = 0
        simp
      smul_add := fun q T T' => by
        apply Subtype.ext
        change cT (sigR R σ) (c q) * ((T : Matrix (Fin n) (Fin n) (R ⊗[F] E)) + T') * c q =
          cT (sigR R σ) (c q) * (T : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * c q +
            cT (sigR R σ) (c q) * (T' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * c q
        rw [Matrix.mul_add, Matrix.add_mul] }
  have hsmulH : ∀ (q : Q) (T : HermR R σ n), ((q • T : HermR R σ n) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) =
      cT (sigR R σ) (c q) * (T : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * c q := fun _ _ => rfl
  have hcontV : ContinuousSMul Q (Fin n → Fin M → R ⊗[F] E) := by
    refine ⟨?_⟩
    change Continuous fun p : Q × (Fin n → Fin M → R ⊗[F] E) => rmul R p.2 (c p.1)
    refine continuous_pi fun a => continuous_pi fun i => ?_
    simp only [rmul]
    refine continuous_finsetSum _ fun b _ => Continuous.mul ?_ ?_
    · exact (continuous_apply i).comp ((continuous_apply b).comp continuous_snd)
    · exact (hcc.comp continuous_fst).matrix_elem b a
  have hcontH : ContinuousSMul Q (HermR R σ n) := by
    refine ⟨?_⟩
    refine Continuous.subtype_mk (f := fun p : Q × HermR R σ n => cT (sigR R σ) (c p.1) * (p.2 : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * c p.1) ?_ _
    have h1 : Continuous fun p : Q × HermR R σ n => c p.1 := hcc.comp continuous_fst
    have h2 : Continuous fun p : Q × HermR R σ n => cT (sigR R σ) (c p.1) :=
      (h1.matrix_map hsig).matrix_transpose
    exact (h2.matrix_mul (continuous_subtype_val.comp continuous_snd)).matrix_mul h1
  have heq : ∀ (q : Q) (X : Fin n → Fin M → R ⊗[F] E), g (q • X) = q • g X := by
    intro q X
    apply Subtype.ext
    rw [hsmulV, hsmulH, ← hgf, ← hgf, hgram]
  have horb : IsOpenEmbedding (fun q : Q => q • S) := by
    have : (fun q : Q => q • S) = o ∘ (Homeomorph.inv Q) := by
      funext q
      apply Subtype.ext
      rw [hsmulH]
      exact (ho q⁻¹).symm
    rw [this]
    exact hoe.comp (Homeomorph.inv Q).isOpenEmbedding
  obtain ⟨fib, hfib⟩ := fibre_on_orbit (Fin n → Fin M → R ⊗[F] E) (HermR R σ n) (Matrix (Fin n) (Fin n) (R ⊗[F] E))
    μ ν (gramR R σ J) g Subtype.val Subtype.val_injective hgc hgf Q heq S horb
  refine ⟨Set.range fun q : Q => q • S, horb.isOpen_range, ⟨1, one_smul _ _⟩, ?_, fib, ?_⟩
  · rintro _ ⟨q, rfl⟩
    change IsUnit ((q • S : HermR R σ n) : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det
    rw [hsmulH]
    have hdc : IsUnit (c q).det := Matrix.isUnits_det_units _
    have hdc' : IsUnit (cT (sigR R σ) (c q)).det := by
      simp only [cT, Matrix.det_transpose]
      have := hdc.map (sigR R σ)
      rwa [RingHom.map_det] at this
    rw [Matrix.det_mul, Matrix.det_mul]
    exact (hdc'.mul hS).mul hdc
  · have hpre : gramR R σ J ⁻¹' (Subtype.val '' (Set.range fun q : Q => q • S)) = g ⁻¹' (Set.range fun q : Q => q • S) := by
      ext X
      simp only [Set.mem_preimage, hgf X]
      exact Subtype.val_injective.mem_set_image
    rw [hpre]
    exact hfib

end GlobalTheory.CompanionTheory.SW.GramNear
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.gram_fiber_measures_change_of_form : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (J' : Matrix (Fin M) (Fin M) E), IsHermND σ J' → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib R σ J n μ ν m → ∀ (μ' : Measure (Fin n → Fin M → R ⊗[F] E)) m', μ'.IsAddHaarMeasure → IsGramFib R σ J' n μ' ν m' → ∀ g : GL (Fin M) (R ⊗[F] E), JR R J' = cT (sigR R σ) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J * (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) → ∀ a : ℝ≥0, μ'.map (actTup R g) = a • μ → ∀ S, (m' S).map (actTup R g) = a • m S := by
  first | exact @GlobalTheory.CompanionTheory.SW.LocIsom.fibre_map_isometry | exact GlobalTheory.CompanionTheory.SW.LocIsom.fibre_map_isometry | (intros; apply GlobalTheory.CompanionTheory.SW.LocIsom.fibre_map_isometry <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.gram_fiber_measures_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib R σ J n μ ν m → ∀ (h : HA R σ J) (S : HermR R σ n), (m S).map (actW R σ J h) = m S := by
  first | exact @GlobalTheory.CompanionTheory.SW.FibreInv.map_actW_fibre | exact GlobalTheory.CompanionTheory.SW.FibreInv.map_actW_fibre | (intros; apply GlobalTheory.CompanionTheory.SW.FibreInv.map_actW_fibre <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.lattice_gram_scalar_almost_all : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (t : F), t ≠ 0 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ x y : Fin 1 → Fin M → Fv F v ⊗[F] E, x ∈ latV b v → y ∈ latV b v → gramR (Fv F v) σ J x = (hermScal (Fv F v) σ (algebraMap F _ t) : HermR (Fv F v) σ 1) → gramR (Fv F v) σ J y = gramR (Fv F v) σ J x → ∃ h : HA (Fv F v) σ J, actW (Fv F v) σ J h x = y ∧ ∀ (n : ℕ) (X : Fin n → Fin M → Fv F v ⊗[F] E), actW (Fv F v) σ J h X ∈ latV b v ↔ X ∈ latV b v := by
  first | exact @GlobalTheory.CompanionTheory.SW.GoodTrans.good_trans | exact GlobalTheory.CompanionTheory.SW.GoodTrans.good_trans | (intros; apply GlobalTheory.CompanionTheory.SW.GoodTrans.good_trans <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section
namespace GlobalTheory.CompanionTheory.SW

theorem exists_local_section : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ) (S : HermR R σ n), IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det → ∃ (B : Set (HermR R σ n)) (g : HermR R σ n → GL (Fin n) (R ⊗[F] E)), IsOpen B ∧ S ∈ B ∧ ContinuousOn g B ∧ g S = 1 ∧ ∀ S' ∈ B, (S' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = cT (sigR R σ) (g S' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * (g S' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := by
  intro F E _ _ _ _ _ σ hσ R _ _ _ _ _ hR n S hS
  obtain ⟨Q, o, -, -, ho, hform⟩ := GlobalTheory.T.hermitian_orbit_local_section_subgroup F E σ hσ R hR n S hS
  have hc : cT (sigR R σ) (1 : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = 1 := by
    ext i j
    by_cases h : i = j
    · subst h; simp [cT]
    · simp [cT, Matrix.one_apply, h, Ne.symm h]
  have ho1 : o 1 = S := by
    apply Subtype.ext
    rw [hform]
    simp [hc]
  have hinv : Function.LeftInverse (Function.invFun o) o := Function.leftInverse_invFun ho.injective
  refine ⟨Set.range o, fun S' => ((Function.invFun o S' : Q) : GL (Fin n) (R ⊗[F] E)),
    ho.isOpen_range, ⟨1, ho1⟩, ?_, ?_, ?_⟩
  · have hcont : ContinuousOn (Function.invFun o) (Set.range o) := by
      rw [continuousOn_iff_continuous_restrict]
      have h1 : (fun y : Set.range o => Function.invFun o y.1) = ho.isEmbedding.toHomeomorph.symm := by
        funext y
        obtain ⟨_, x, rfl⟩ := y
        show Function.invFun o (o x) = _
        rw [hinv x]
        exact ho.isEmbedding.toHomeomorph.eq_symm_apply.2 (Subtype.ext rfl)
      have h2 : Continuous (fun y : Set.range o => Function.invFun o y.1) := by
        rw [h1]
        exact Homeomorph.continuous _
      exact h2
    exact continuous_subtype_val.comp_continuousOn hcont
  · show ((Function.invFun o S : Q) : GL (Fin n) (R ⊗[F] E)) = 1
    rw [← ho1, hinv 1]
    rfl
  · rintro _ ⟨x, rfl⟩
    simp only [hinv x]
    exact hform x

end GlobalTheory.CompanionTheory.SW
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.gram_fiber_measures_rmul_equivariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib R σ J n μ ν m → ∀ (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)), IsUnit g.det → ∀ τ : HermR R σ n → HermR R σ n, (∀ S, (τ S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = cT (sigR R σ) g * S * g) → ∀ a c : ℝ≥0, μ.map (fun X => rmul R X g) = a • μ → ν.map τ = c • ν → ∀ S, a • m (τ S) = c • (m S).map (fun X => rmul R X g) := by
  first | exact @GlobalTheory.CompanionTheory.SW.FibScale.fib_rmul | exact GlobalTheory.CompanionTheory.SW.FibScale.fib_rmul | (intros; apply GlobalTheory.CompanionTheory.SW.FibScale.fib_rmul <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.pure_adelic_function_measurable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F))) (φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) (φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℝ≥0∞), Measurable φinf → (∀ v, Measurable (φ v)) → Measurable (pureL b S φinf φ) := by
  first | exact @GlobalTheory.CompanionTheory.SW.PureMeas.measurable_pureL | exact GlobalTheory.CompanionTheory.SW.PureMeas.measurable_pureL | (intros; apply GlobalTheory.CompanionTheory.SW.PureMeas.measurable_pureL <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.adelic_haar_invariant_unitary_action : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (μ : Measure (Fin 1 → Fin M → AF F ⊗[F] E)), μ.IsAddHaarMeasure → ∀ h : HA (AF F) σ J, μ.map (actW (AF F) σ J h) = μ := by
  first | exact @GlobalTheory.CompanionTheory.SW.HaarInv.actW_map_eq | exact GlobalTheory.CompanionTheory.SW.HaarInv.actW_map_eq | (intros; apply GlobalTheory.CompanionTheory.SW.HaarInv.actW_map_eq <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.completion_is_local_ring : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)), IsLocR (Fv F v) := by
  first | exact @GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv | exact GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv | (intros; apply GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv <;> assumption)
end
