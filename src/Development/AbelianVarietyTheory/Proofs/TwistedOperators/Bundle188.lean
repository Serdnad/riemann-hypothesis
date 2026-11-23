module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle994
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplexConjugationMapsMultiplicitySpace
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Aesop.Main
import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle170
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.LocalToGlobal.Divisibility.DefGroup
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Topology.UrysohnsLemma

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelRamif

variable {D : D7}

theorem not_two_primes (PP : Pl D.host.E) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (h1 : (p : 𝓞 D.host.E) ∈ PP.asIdeal) (h2 : (q : 𝓞 D.host.E) ∈ PP.asIdeal) : False := by
  have hc : IsCoprime (p : 𝓞 D.host.E) (q : 𝓞 D.host.E) :=
    Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 hne)
  obtain ⟨a, b, hab⟩ := hc
  apply PP.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  exact add_mem (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)

theorem natCast_mem_conj {PP PP' : Pl D.host.E} (h : Formalism.IndefR.Lev.IsConjPl PP PP') {n : ℕ}
    (hn : (n : 𝓞 D.host.E) ∈ PP.asIdeal) : (n : 𝓞 D.host.E) ∈ PP'.asIdeal := by
  obtain ⟨c', hc', e⟩ := h _ hn
  have e2 : c' = (n : 𝓞 D.host.E) := by
    apply RingOfIntegers.ext
    have e3 : (((n : 𝓞 D.host.E)) : D.host.E) = (n : D.host.E) := map_natCast (algebraMap (𝓞 D.host.E) D.host.E) n
    rw [e, e3, star_natCast]
  rwa [e2] at hc'

theorem exists_prime_mem {Q : Finset (Pl D.host.E)} (hQ : IsTwistPlaces D.host.g Q) {PP : Pl D.host.E}
    (h : PP ∈ Q) : ∃ q : ℕ, q.Prime ∧ (q : 𝓞 D.host.E) ∈ PP.asIdeal ∧ ∀ i, q ≠ D.host.g i := by
  obtain ⟨⟨q, hq, hc, -, hne⟩, -⟩ := hQ PP h
  refine ⟨q, hq, ?_, hne⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← hc, ← nsmul_one]
  exact card_nsmul_eq_zero'

theorem typePrime_mem {P : Formalism.L2.Host.PiBar D.host} {k : Fin 2} {PP : Pl D.host.E} (h : P.Div k PP) :
    ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
  have h1 := P.pb_over k
  have h2 : PP.under (𝓞 D.host.K) = P.pb k := h
  rw [← h2] at h1
  have h3 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ PP.asIdeal := h1
  rwa [map_natCast] at h3

theorem isConjPl_of_eq {w w' : Pl D.host.E}
    (h : w'.asIdeal = Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) w.asIdeal) : Formalism.IndefR.Lev.IsConjPl w' w := by
  intro c hc
  rw [h, Formalism.L2.Col.mem_conjIdeal] at hc
  exact ⟨_, hc, rfl⟩

theorem ramif_at_levels : ∀ (D : D7) (T0 : Type) (L : LevCh D T0) (μ0 : T0), L.Is μ0 → ∀ (t : T0) (j : Fin D.R.m), Disjoint L.Pg (L.Q t) ∧ (∀ PP ∈ L.Q t, (L.C.mu0 j).UnrAt PP) ∧ (∀ PP ∈ L.Pg, (L.xiH t).UnrAt PP) ∧ ∀ PP', PP' ∉ L.Pg → (∀ PP ∈ L.Pg, ¬ Formalism.IndefR.Lev.IsConjPl PP PP') → (L.C.mu0 j).UnrAt PP' := by
  classical
  intro D T0 L μ0 hL t j
  have hoff : ∀ (k : Fin 2) (PP : Pl D.host.E), ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal →
      PP ∉ L.Q t ∧ ¬ ∃ PP' ∈ L.Q t, Formalism.IndefR.Lev.IsConjPl PP' PP := by
    intro k PP hk
    refine ⟨fun hQ => ?_, fun ⟨PP', hQ, hc⟩ => ?_⟩
    · obtain ⟨q, hq, hm, hne⟩ := exists_prime_mem (hL.Q_pl t) hQ
      exact not_two_primes PP hq (D.host.g_prime k) (hne k) hm hk
    · obtain ⟨q, hq, hm, hne⟩ := exists_prime_mem (hL.Q_pl t) hQ
      exact not_two_primes PP hq (D.host.g_prime k) (hne k) (natCast_mem_conj hc hm) hk
  have hPg : ∀ PP ∈ L.Pg, PP ∉ L.Q t ∧ ¬ ∃ PP' ∈ L.Q t, Formalism.IndefR.Lev.IsConjPl PP' PP := by
    intro PP h
    obtain ⟨k, hk⟩ := (hL.Pg PP).1 h
    exact hoff k PP (typePrime_mem hk)
  have hM := L.C.isMu0 j
  refine ⟨Finset.disjoint_left.2 fun PP h => (hPg PP h).1, fun PP hQ => ?_, fun PP h => ?_, fun PP h1 h2 => ?_⟩
  · exact hM.unr PP fun k hk => (hoff k PP hk).1 hQ
  · by_contra hn
    rcases (hL.Q_ram t PP).1 hn with h' | h'
    · exact (hPg PP h).1 h'
    · exact (hPg PP h).2 h'
  · refine hM.unr PP fun k hk => ?_
    rcases GlobalTheory.ConjOverQuad.div_or_conj_div D L.C.P k PP hk with h | ⟨PP', h, hc⟩
    · exact h1 ((hL.Pg PP).2 ⟨k, h⟩)
    · exact h2 PP' ((hL.Pg PP').2 ⟨k, h⟩) (isConjPl_of_eq hc)

end GlobalTheory.LevelRamif
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.complexConjugation_maps_multiplicitySpace : ∀ {D : D7} {V : HSp D} {S S' : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, c τ (M'.rep τ g w) = M.rep τ g (c τ w)) → (∀ τ (w : M'.H τ), w ∈ M'.sm τ ↔ c τ w ∈ M.sm τ) ∧ ∀ J χ, ∀ T ∈ Mult θ M J χ, ∃ T' ∈ Mult θ M' J (fun k => star (χ k)), ∀ (v' : M'.Vec) (v : M.Vec), (∀ τ, (v τ : M.H τ) = c τ (v' τ)) → ∀ g, T' v' g = star (T v g) := by
  first | exact @GlobalTheory.ConjMult.conj_mult | exact GlobalTheory.ConjMult.conj_mult | (intros; apply GlobalTheory.ConjMult.conj_mult <;> assumption)
end

section

open MeasureTheory GlobalTheory.AutomorphicL2Unitary Topology Set Filter
open scoped Pointwise

noncomputable section

namespace GlobalTheory.CosetIntegralZero

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]

def cosetAvg (H : Subgroup G) (ν : Measure H) (ψ : G → ℝ) (g : G) : ℝ :=
  ∫ u : H, ψ ((u : G)⁻¹ * g) ∂ν

theorem cosetAvg_mul [BorelSpace G] [SecondCountableTopology G] (H : Subgroup G) (ν : Measure H) [ν.IsMulLeftInvariant]
    (ψ : G → ℝ) (u : H) (g : G) : cosetAvg H ν ψ ((u : G) * g) = cosetAvg H ν ψ g := by
  unfold cosetAvg
  rw [← integral_mul_left_eq_self (fun v : H => ψ ((v : G)⁻¹ * ((u : G) * g))) u]
  congr 1; ext v
  simp [mul_inv_rev, mul_assoc]

theorem continuous_cosetAvg [LocallyCompactSpace G] [BorelSpace G] (H : Subgroup G) (hH : IsClosed (H : Set G))
    (ν : Measure H) [IsFiniteMeasureOnCompacts ν] {ψ : G → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    Continuous (cosetAvg H ν ψ) := by
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  obtain ⟨t, t_comp, ht⟩ := exists_compact_mem_nhds x₀
  have hk : IsCompact (((↑) : H → G) ⁻¹' (t • (tsupport ψ)⁻¹)) :=
    hH.isClosedEmbedding_subtypeVal.isCompact_preimage (t_comp.smul_set hψc.inv)
  have A : ContinuousOn (cosetAvg H ν ψ) t := by
    apply continuousOn_integral_of_compact_support hk
    · exact (hψ.comp ((continuous_subtype_val.comp continuous_snd).inv.mul continuous_fst)).continuousOn
    · intro p x hp hx
      contrapose! hx
      refine ⟨p, hp, p⁻¹ * (x : G), ?_, by simp⟩
      simpa only [Set.mem_inv, mul_inv_rev, inv_inv] using subset_tsupport _ hx
  exact A.continuousAt ht

theorem cosetAvg_pos [BorelSpace G] [SecondCountableTopology G] (H : Subgroup G) (hH : IsClosed (H : Set G))
    (ν : Measure H) [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts ν] {ψ : G → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x) {g : G} (hg : ψ g ≠ 0) : 0 < cosetAvg H ν ψ g := by
  have C : Continuous (fun u : H => ψ ((u : G)⁻¹ * g)) := by fun_prop
  apply (integral_pos_iff_support_of_nonneg (fun u => hψ0 _) ?_).2
  · apply C.isOpen_support.measure_pos ν
    exact ⟨1, by simpa using hg⟩
  · apply C.integrable_of_hasCompactSupport
    refine HasCompactSupport.intro (hH.isClosedEmbedding_subtypeVal.isCompact_preimage
      ((show IsCompact (tsupport ψ) from hψc).image (f := fun k => g * k⁻¹) (by fun_prop))) ?_
    intro u hu
    by_contra h
    exact hu ⟨(u : G)⁻¹ * g, subset_tsupport _ h, by simp⟩

theorem integrable_prod_of_bound [LocallyCompactSpace G] [T2Space G] [BorelSpace G] [SecondCountableTopology G]
    (H : Subgroup G) (ν : Measure H) [IsFiniteMeasureOnCompacts ν] [SFinite ν]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [SFinite μ]
    {P : H × G → ℂ} (hP : Continuous P) {C : ℝ} (hC : ∀ z, ‖P z‖ ≤ C) {S : Set H} {M : Set G}
    (hS : IsCompact S) (hM : IsCompact M) (hPS : ∀ u g, P (u, g) ≠ 0 → u ∈ S ∧ g ∈ M)
    {w : G → ℂ} (hw : LocallyIntegrable w μ) :
    Integrable (fun z : H × G => P z * w z.2) (ν.prod μ) := by
  have hSi : Integrable (S.indicator (fun _ => (1:ℝ))) ν :=
    (integrableOn_const hS.measure_ne_top).integrable_indicator hS.measurableSet
  have hMi : Integrable (fun g => C * ‖M.indicator w g‖) μ :=
    ((hw.integrableOn_isCompact hM).integrable_indicator hM.measurableSet).norm.const_mul C
  refine (hSi.mul_prod hMi).mono' ?_ (Eventually.of_forall fun z => ?_)
  · exact hP.aestronglyMeasurable.mul hw.aestronglyMeasurable.comp_snd
  · obtain ⟨u, g⟩ := z
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC (u, g))
    by_cases h : P (u, g) = 0
    · simp only [h, zero_mul, norm_zero]
      exact mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) (mul_nonneg hC0 (norm_nonneg _))
    · obtain ⟨hu, hg⟩ := hPS u g h
      simp only [Set.indicator_of_mem hu, Set.indicator_of_mem hg, one_mul, norm_mul]
      exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)

theorem integral_cosetAvg_mul_eq [LocallyCompactSpace G] [T2Space G] [BorelSpace G] [SecondCountableTopology G]
    (H : Subgroup G) (hH : IsClosed (H : Set G)) (ν : Measure H) [ν.IsHaarMeasure] [SFinite ν]
    (μ : Measure G) [μ.IsHaarMeasure] [SFinite μ] {ψ : G → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (hψ1 : ∀ g, |ψ g| ≤ 1) {F w : G → ℂ} (hF : Continuous F) (hFc : HasCompactSupport F)
    (hw : LocallyIntegrable w μ) (hinv : ∀ u ∈ H, (fun g => w (u * g)) =ᵐ[μ] w) :
    ∫ g, (cosetAvg H ν ψ g : ℂ) * F g * w g ∂μ = ∫ g, (ψ g : ℂ) * w g * ∫ u : H, F ((u : G) * g) ∂ν ∂μ := by
  obtain ⟨C, hC⟩ := hF.bounded_above_of_compact_support hFc
  have hS : IsCompact (((↑) : H → G) ⁻¹' ((fun p : G × G => p.1 * p.2⁻¹) '' (tsupport F ×ˢ tsupport ψ))) :=
    hH.isClosedEmbedding_subtypeVal.isCompact_preimage
      (((show IsCompact (tsupport F) from hFc).prod (show IsCompact (tsupport ψ) from hψc)).image (by fun_prop))
  have I1 : Integrable (fun z : H × G => ((ψ ((z.1 : G)⁻¹ * z.2) : ℂ) * F z.2) * w z.2) (ν.prod μ) := by
    refine integrable_prod_of_bound H ν μ (by fun_prop) (C := C) ?_ hS (show IsCompact (tsupport F) from hFc) ?_ hw
    · intro z
      rw [norm_mul]
      calc _ ≤ 1 * C := mul_le_mul (by simpa using hψ1 _) (hC _) (norm_nonneg _) zero_le_one
        _ = C := one_mul C
    · intro u g h
      have h1 : ψ ((u : G)⁻¹ * g) ≠ 0 := fun h' => h (by simp [h'])
      have h2 : F g ≠ 0 := fun h' => h (by simp [h'])
      exact ⟨⟨(g, (u : G)⁻¹ * g), ⟨subset_tsupport _ h2, subset_tsupport _ h1⟩, by simp⟩, subset_tsupport _ h2⟩
  have I2 : Integrable (fun z : H × G => ((ψ z.2 : ℂ) * F ((z.1 : G) * z.2)) * w z.2) (ν.prod μ) := by
    refine integrable_prod_of_bound H ν μ (by fun_prop) (C := C) ?_ hS (show IsCompact (tsupport ψ) from hψc) ?_ hw
    · intro z
      rw [norm_mul]
      calc _ ≤ 1 * C := mul_le_mul (by simpa using hψ1 _) (hC _) (norm_nonneg _) zero_le_one
        _ = C := one_mul C
    · intro u g h
      have h1 : ψ g ≠ 0 := fun h' => h (by simp [h'])
      have h2 : F ((u : G) * g) ≠ 0 := fun h' => h (by simp [h'])
      exact ⟨⟨((u : G) * g, g), ⟨subset_tsupport _ h2, subset_tsupport _ h1⟩, by simp⟩, subset_tsupport _ h1⟩
  calc ∫ g, (cosetAvg H ν ψ g : ℂ) * F g * w g ∂μ
      = ∫ g, ∫ u : H, (ψ ((u : G)⁻¹ * g) : ℂ) * F g * w g ∂ν ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun g => ?_)
        simp only [cosetAvg, mul_assoc]
        rw [integral_mul_const, integral_complex_ofReal]
    _ = ∫ u : H, ∫ g, (ψ ((u : G)⁻¹ * g) : ℂ) * F g * w g ∂μ ∂ν :=
        (integral_integral_swap (f := fun (u : H) (g : G) => (ψ ((u : G)⁻¹ * g) : ℂ) * F g * w g) I1).symm
    _ = ∫ u : H, ∫ g, (ψ g : ℂ) * F ((u : G) * g) * w g ∂μ ∂ν := by
        refine integral_congr_ae (Eventually.of_forall fun u => ?_)
        dsimp only
        conv_lhs => rw [← integral_mul_left_eq_self _ (u : G)]
        refine integral_congr_ae ?_
        filter_upwards [hinv u u.2] with g hg
        simp only [inv_mul_cancel_left, hg]
    _ = ∫ g, ∫ u : H, (ψ g : ℂ) * F ((u : G) * g) * w g ∂ν ∂μ :=
        integral_integral_swap (f := fun (u : H) (g : G) => (ψ g : ℂ) * F ((u : G) * g) * w g) I2
    _ = ∫ g, (ψ g : ℂ) * w g * ∫ u : H, F ((u : G) * g) ∂ν ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun g => ?_)
        dsimp only
        rw [← integral_const_mul]
        congr 1; ext u; ring

theorem integral_mul_eq_zero_of_coset_integral_eq_zero : ∀ (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G]
    [BorelSpace G] (H : Subgroup G), IsClosed (H : Set G) → ∀ (ν : Measure H) [ν.IsHaarMeasure]
    (μ : Measure G) [μ.IsHaarMeasure] (f w : G → ℂ), Continuous f → HasCompactSupport f →
    LocallyIntegrable w μ → (∀ u ∈ H, (fun g => w (u * g)) =ᵐ[μ] w) →
    (∀ g, ∫ u : H, f (u * g) ∂ν = 0) → ∫ g, f g * w g ∂μ = 0 := by
  intro G _ _ _ _ _ _ _ _ H hH ν _ μ _ f w hf hfc hw hinv hzero
  haveI : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  obtain ⟨ψ₀, hψ1, -, hψc, hψ01⟩ := exists_continuous_one_zero_of_isCompact
    (show IsCompact (tsupport f) from hfc) isClosed_empty (Set.disjoint_empty _)
  have hJc : Continuous (cosetAvg H ν ψ₀) := continuous_cosetAvg H hH ν ψ₀.continuous hψc
  have hJpos : ∀ g ∈ tsupport f, 0 < cosetAvg H ν ψ₀ g := fun g hg =>
    cosetAvg_pos H hH ν ψ₀.continuous hψc (fun x => (hψ01 x).1) (by rw [hψ1 hg]; simp)
  set F : G → ℂ := fun g => f g / (cosetAvg H ν ψ₀ g : ℂ) with hFdef
  have hF : Continuous F := by
    refine continuous_iff_continuousAt.2 fun g => ?_
    by_cases hg : g ∈ tsupport f
    · exact hf.continuousAt.div (Complex.continuous_ofReal.comp hJc).continuousAt
        (by exact_mod_cast (hJpos g hg).ne')
    · have : F =ᶠ[𝓝 g] fun _ => 0 := by
        filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hg] with x hx
        simp [hFdef, image_eq_zero_of_notMem_tsupport hx]
      exact continuousAt_const.congr this.symm
  have hFc : HasCompactSupport F :=
    hfc.mono fun g hg h => hg (by simp [hFdef, h])
  have hFJ : ∀ g, (cosetAvg H ν ψ₀ g : ℂ) * F g * w g = f g * w g := by
    intro g
    by_cases h : f g = 0
    · simp [hFdef, h]
    · have hJ : (cosetAvg H ν ψ₀ g : ℂ) ≠ 0 := by exact_mod_cast (hJpos g (subset_tsupport _ h)).ne'
      rw [hFdef, mul_div_cancel₀ _ hJ]
  have hFH : ∀ g, ∫ u : H, F ((u : G) * g) ∂ν = 0 := by
    intro g
    simp only [hFdef, cosetAvg_mul H ν ψ₀ _ g]
    rw [integral_div, hzero g, zero_div]
  have key := integral_cosetAvg_mul_eq H hH ν μ ψ₀.continuous hψc
    (fun g => by rw [abs_le]; constructor <;> linarith [(hψ01 g).1, (hψ01 g).2]) hF hFc hw hinv
  simp only [hFJ, hFH, mul_zero, integral_zero] at key
  exact key

end GlobalTheory.CosetIntegralZero
end
end
