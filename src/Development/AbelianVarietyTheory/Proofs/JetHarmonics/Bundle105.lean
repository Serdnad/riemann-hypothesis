module

public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle002
public import Formalism.LocalToGlobal.ProjectiveLattices.ConjNeSelfOfCM
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsMultiplicativeChartAtSplitPrime
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Mathlib.MeasureTheory.Function.L2Space
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesParameterUnique
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle081
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle096
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle103
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle094
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle100
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle084
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle059
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle036
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle034
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegrandAestronglyMeasurable
public import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationScalesHeisenbergMeasure
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationUnipotentWeylMeasure
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr

@[expose] public section

section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharDepth

theorem crP_map_ringHom {Ty : Type} [Fintype Ty] [DecidableEq Ty] (r : Ty → ℕ) (n : ℕ) {R S : Type} [CommRing R]
    [CommRing S] (φ : R →+* S) (β : (Σ σ : Ty, Fin (r σ)) → Fin n) (a : Ty → ℕ → ℕ) :
    MvPolynomial.map φ (Crude.crP r n R β a) = Crude.crP r n S β a := by
  rw [← Crude.crP_map R, ← Crude.crP_map S, MvPolynomial.map_map]
  congr 2
  exact RingHom.ext_int _ _

theorem exists_col_extend {ι κ α : Type} (β : ι → κ) (hβ : Function.Injective β) (g : ι → α) (x : α) :
    ∃ G : κ → α, (∀ i, G (β i) = g i) ∧ ∀ b, G b = x ∨ ∃ i, G b = g i := by
  classical
  refine ⟨Function.extend β g (fun _ => x), fun i => hβ.extend_apply _ _ _, fun b => ?_⟩
  by_cases hb : ∃ i, β i = b
  · obtain ⟨i, rfl⟩ := hb
    exact Or.inr ⟨i, hβ.extend_apply _ _ _⟩
  · exact Or.inl (Function.extend_apply' _ _ _ hb)

theorem nuLocC_le_of_character_flags : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (p : ℕ) [Fact p.Prime] (X : ValExt T p) (τO : (E →+* ℂ) → (𝓞 E →+* X.O)), IsTypes X io τO → (∀ τ, ∃ a0, IsUnit (τO τ a0 - τO τ (star a0))) → (∀ x : X.O, x ≠ 0 → ∃ N : ℕ, X.v (N : X.C) < X.v (algebraMap X.O X.C x) ∧ ∀ τ, ∃ a : 𝓞 E, star a * a = (N : 𝓞 E) ∧ X.v (algebraMap X.O X.C (τO τ a - 1)) < X.v (algebraMap X.O X.C x)) → ∀ (e k n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ), 0 < e → DomW Dw a → Fintype.card (Lt1 Dw) ≤ n → ∀ (len : (E →+* ℂ) → ℝ), (∀ τ, 0 ≤ len τ) → (∀ τ, ∃ χ : Fin (Dw.mult τ) → PS X.O 1 (chD Ch.ch), (∀ b, IsCh (fun i => MvPowerSeries.map X.ι (Ch.FT i)) (χ b)) ∧ ∀ i : Fin (Dw.mult τ), (X.v (p : X.C) : ℝ) ^ len τ ≤ (X.v (algebraMap X.O X.C (Matrix.of fun s b : Fin (i.val + 1) => ∑ j, X.ι (Ch.uvecT ⟨τ, Fin.castLE i.isLt s⟩ j) * dl (χ (Fin.castLE i.isLt b)) j).det) : ℝ)) → nuLocC Ch e k a n ≤ (((vV T.V (p : T.Fr) : ℝ) / (e : ℝ) * ∑ τ, len τ * (a (τ, 0) : ℝ) : ℝ) : EReal) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y Ch p _ X τO hty hun happ e k n a he ha hn len hlen hχ
  classical
  obtain ⟨B, hF, hact, hg⟩ := GlobalTheory.T.exists_formalBiextension_integral_chart_valuedExtension E H Dw l Xo c T io y Ch p X
  choose χ hχ1 hχ2 using hχ
  have hβ : Function.Injective (colP Dw hn) := fun p q h =>
    (Fintype.equivFin _).injective (Fin.castLE_injective hn h)
  obtain ⟨ty, hty1, -⟩ := exists_col_extend (colP Dw hn) hβ (fun q : Lt1 Dw => q.1) (Classical.arbitrary _)
  obtain ⟨χ', hχ'1, hχ'2⟩ := exists_col_extend (colP Dw hn) hβ (fun q : Lt1 Dw => χ q.1 q.2) 1
  have hp0 : X.v (p : X.C) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hp1 : X.v (p : X.C) ≤ 1 := by
    have := X.ints.map_le_one (p : X.O)
    rwa [map_natCast] at this
  obtain ⟨hval, hsupp⟩ := GlobalTheory.T.valuation_blockPolynomial_ge_prod X.C X.v X.O X.ints (E →+* ℂ) Dw.mult n (colP Dw hn) hβ
    (fun τ i => a (τ, i)) ha
    (fun ℓ : LtN Dw n => ∑ j, X.ι (Ch.uvecT ⟨ℓ.1, ℓ.2.1⟩ j) * dl (χ' ℓ.2.2) j)
    (fun τ => X.v (p : X.C) ^ len τ) (fun τ => NNReal.rpow_le_one hp1 (hlen τ))
    (fun τ i => by
      have h := hχ2 τ i
      rw [← NNReal.coe_le_coe, NNReal.coe_rpow]
      simp only [hχ'1]
      exact h)
  have hprod : ∏ τ, (X.v (p : X.C) ^ len τ) ^ (a (τ, 0)) =
      X.v (p : X.C) ^ (∑ τ, len τ * (a (τ, 0) : ℝ)) := by
    apply NNReal.coe_injective
    rw [NNReal.coe_rpow, Real.rpow_sum_of_pos (by exact_mod_cast pos_iff_ne_zero.2 hp0), NNReal.coe_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [NNReal.coe_pow, NNReal.coe_rpow, Real.rpow_mul_natCast (NNReal.coe_nonneg _)]
  rw [hprod] at hval
  have hne : MvPolynomial.eval
      (fun ℓ : LtN Dw n => ∑ j, X.ι (Ch.uvecT ⟨ℓ.1, ℓ.2.1⟩ j) * dl (χ' ℓ.2.2) j)
      (Crude.crP Dw.mult n X.O (colP Dw hn) (fun τ i => a (τ, i))) ≠ 0 := by
    intro h0
    rw [h0, map_zero, map_zero] at hval
    exact absurd hval (not_le.2 (NNReal.rpow_pos (pos_iff_ne_zero.2 hp0)))
  obtain ⟨f, hf⟩ := GlobalTheory.T.exists_characterGerm_valuation_eq_columnTyped X.C X.v X.O X.ints (chD Ch.ch) (𝓞 E) B _ hg H.w0 k n (E →+* ℂ) Dw.mult τO
    (fun q j => X.ι (Ch.uvecT q j))
    (fun q a0 => by
      rw [hact]
      exact (GlobalTheory.T.cmTypeDirections_eigenbasis_valuedIntegers E H Dw l Xo c T io y Ch p X τO hty q.1).1.1 q.2 a0)
    hun happ ty (Crude.crP Dw.mult n X.O (colP Dw hn) (fun τ i => a (τ, i)))
    (fun mo hmo ℓ hℓ => by
      obtain ⟨i, hi⟩ := hsupp mo hmo ℓ hℓ
      rw [← hi, hty1])
    χ'
    (fun b => by
      rw [hF]
      rcases hχ'2 b with h | ⟨q, h⟩
      · rw [h]
        exact ⟨by simp, by simp⟩
      · rw [h]
        exact hχ1 q.1 q.2)
    hne
  refine GlobalTheory.T.chart_local_depth_le_of_valuedExtension_bound E H Dw l Xo c T io y Ch p X B hF hact e k n a he
    (Crude.crP Dw.mult n X.O (colP Dw hn) (fun τ i => a (τ, i))) ?_ f _ ?_
  · rw [crP_map_ringHom, ← Crude.crP_map]
    exact (Crude.Pmin_mem Dw.mult n X.C (colP Dw hn) _ ⊤ _ _ (fun τ _ => conj_ne_self_of_CM τ) hβ ha).1
  · rw [← NNReal.coe_rpow, NNReal.coe_le_coe]
    exact hval.trans (le_of_eq hf.symm)

end GlobalTheory.CharDepth
end

section

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

theorem _root_.GlobalTheory.T.cpSeriesCoeffBounded_taylor_elliptic_of_poles : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (ℓ : ℂ_[q]⟦X⟧) (φ : ℂ → ℂ), M.Chart ℓ → Ell M.L φ → AnalyticAt ℂ φ 0 → (∀ p, meromorphicOrderAt φ p < 0 → ¬ M.Small p) → Bdd (hat M.ι ℓ φ) := by
  first | exact @GlobalTheory.MomOne.EllBdd.bdd_hat_of_ell | exact GlobalTheory.MomOne.EllBdd.bdd_hat_of_ell | (intros; apply GlobalTheory.MomOne.EllBdd.bdd_hat_of_ell <;> assumption)
end

section

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

theorem _root_.GlobalTheory.T.multiplicativeCoord_add_and_complexMul : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]), M.MChart ω → (∀ ζ ζ' p p', M.At ω ζ p → M.At ω ζ' p' → M.At ω (ζ * ζ') (p + p')) ∧ ∀ (α : ℂ) (a : ℤ_[q]) (n k : ℕ) (ζ : ℂ_[q]) (p : ℂ), (∀ l ∈ M.L.lattice, α * l ∈ M.L.lattice) → M.ι α = zc a → ‖a - (k : ℤ_[q])‖ ≤ (q : ℝ) ^ (-(n : ℤ)) → ζ ^ (q ^ n) = 1 → M.At ω ζ p → M.At ω (ζ ^ k) (α * p) := by
  first | exact @GlobalTheory.MomOne.AtAdd.at_add_and_mul | exact GlobalTheory.MomOne.AtAdd.at_add_and_mul | (intros; apply GlobalTheory.MomOne.AtAdd.at_add_and_mul <;> assumption)
end

section

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

theorem _root_.GlobalTheory.T.exists_multiplicativeChart_at_splitPrime : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.Ok → IsAlgebraic ℚ M.W.a₁ → IsAlgebraic ℚ M.W.a₂ → IsAlgebraic ℚ M.W.a₃ → IsAlgebraic ℚ M.W.a₄ → IsAlgebraic ℚ M.W.a₆ → ∃ ω : ℂ_[q], M.MChart ω := by
  first | exact @GlobalTheory.MomOne.SplitChart.exists_mChart | exact GlobalTheory.MomOne.SplitChart.exists_mChart | (intros; apply GlobalTheory.MomOne.SplitChart.exists_mChart <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.BesselOrth

section L2

variable {X E : Type} [MeasurableSpace X] {ν : Measure X} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem inner_toLp {f g : X → E} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    ⟪hf.toLp f, hg.toLp g⟫_ℂ = ∫ x, ⟪f x, g x⟫_ℂ ∂ν := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
  rw [h1, h2]

theorem integrable_inner {f g : X → E} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    Integrable (fun x => ⟪f x, g x⟫_ℂ) ν := by
  refine (L2.integrable_inner (𝕜 := ℂ) (hf.toLp f) (hg.toLp g)).congr ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
  rw [h1, h2]

theorem norm_toLp_eq {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {f : X → E} (hf : MemLp f 2 ν)
    {a : H} (h : ∫ x, ⟪f x, f x⟫_ℂ ∂ν = ⟪a, a⟫_ℂ) : ‖hf.toLp f‖ = ‖a‖ := by
  rw [← inner_toLp hf hf] at h
  rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ, h]

theorem norm_integral_inner_le {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] {f g : X → E} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν)
    {a : H} {b : H'} (h : ∫ x, ⟪f x, f x⟫_ℂ ∂ν = ⟪a, a⟫_ℂ) (h' : ∫ x, ⟪g x, g x⟫_ℂ ∂ν = ⟪b, b⟫_ℂ) :
    ‖∫ x, ⟪f x, g x⟫_ℂ ∂ν‖ ≤ ‖a‖ * ‖b‖ := by
  rw [← inner_toLp hf hg, ← norm_toLp_eq hf h, ← norm_toLp_eq hg h']
  exact norm_inner_le_norm _ _

end L2

end GlobalTheory.BesselOrth

namespace GlobalTheory

open BesselOrth Formalism.FourierDecayAlt.P

theorem bessel_orth_of_param_ne : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (mu' : Fin (2 * r + k + 1) → ℝ) (R R' : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (Bm : R.H → Wp) (Bm' : R'.H → Wp), R.IsDS ε mu → R'.IsDS ε mu' → mu ≠ mu' → SideG k r z π u μW μN μG νq → IsIsoB R z π νq Bm → IsIsoB R' z π νq Bm' → ∀ w ∈ R.sm, ∀ y ∈ R'.sm, ∫ x, ⟪Bm' (R'.σ (Matrix.of x) y), Bm (R.σ (Matrix.of x) w)⟫_ℂ ∂νq = 0 := by
  intro hH k r ε mu mu' R R' Wp _ _ _ _ z π u μW μN μG νq Bm Bm' hR hR' hne hS hB hB'
  have hK : PI.KFinSmooth := hH.1.2.2.1
  have hP : Poulsen := hH.2.2.2.2.2.1
  obtain ⟨hL, hI⟩ := GlobalTheory.T.isometric_bessel_memLp_and_integral_inner_eq hK k r ε mu R Wp z π u μW μN μG νq Bm hR hS hB
  obtain ⟨hL', hI'⟩ := GlobalTheory.T.isometric_bessel_memLp_and_integral_inner_eq hK k r ε mu' R' Wp z π u μW μN μG νq Bm' hR' hS hB'
  have hq := GlobalTheory.T.quotientMeasure_integral_rmul_besselGroup k r Wp z π u μW μN μG νq
  obtain ⟨⟨ha, hs, he, hc⟩, -⟩ := hB
  obtain ⟨⟨ha', hs', he', hc'⟩, -⟩ := hB'
  have hco := GlobalTheory.T.frechetContinuous_continuousOn_orbit_hasDerivAt hK k r ε mu R hR Wp Bm ha hs hc
  have hco' := GlobalTheory.T.frechetContinuous_continuousOn_orbit_hasDerivAt hK k r ε mu' R' hR' Wp Bm' ha' hs' hc'
  have hae : ∀ᵐ x ∂νq, Matrix.of x ∈ GG k r := by
    obtain ⟨-, -, -, -, hW, hN, hG, hQ⟩ := hS
    exact DDSmoothness.ae_UH_of_quot hG.2.2.1 (DDSmoothness.muSof_facts hW hN).1 (DDSmoothness.muSof_facts hW hN).2 hQ
  have ht : ∀ w ∈ R.sm, ∀ g ∈ GG k r, R.σ g w ∈ R.sm := fun w hw g hg => TranslationBesselVanishing.smooth_translate hR.2 hw hg
  have ht' : ∀ w ∈ R'.sm, ∀ g ∈ GG k r, R'.σ g w ∈ R'.sm := fun w hw g hg => TranslationBesselVanishing.smooth_translate hR'.2 hw hg
  have hm : ∀ a ∈ GG k r, ∀ b ∈ GG k r, ∀ v, R.σ (a * b) v = R.σ a (R.σ b v) := fun a ha b hb v => by
    rw [TranslationBesselVanishing.sigma_mul hR.2 ha hb]; rfl
  have hm' : ∀ a ∈ GG k r, ∀ b ∈ GG k r, ∀ v, R'.σ (a * b) v = R'.σ a (R'.σ b v) := fun a ha b hb v => by
    rw [TranslationBesselVanishing.sigma_mul hR'.2 ha hb]; rfl
  have hform : IsInvForm R R' (fun w y =>
      ∫ x, ⟪Bm' (R'.σ (Matrix.of x) y), Bm (R.σ (Matrix.of x) w)⟫_ℂ ∂νq) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, 1, [[]], [[]], by simp, ?_⟩
    · intro w hw w' hw' y hy
      beta_reduce
      rw [← integral_add (integrable_inner (hL' y hy) (hL w hw)) (integrable_inner (hL' y hy) (hL w' hw'))]
      refine integral_congr_ae ?_
      filter_upwards [hae] with x hx
      rw [map_add (f := _), ha _ (ht w hw _ hx) _ (ht w' hw' _ hx), inner_add_right]
    · intro a w hw y hy
      beta_reduce
      rw [← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [hae] with x hx
      rw [map_smul, hs a _ (ht w hw _ hx), inner_smul_right]
    · intro w hw y hy y' hy'
      beta_reduce
      rw [← integral_add (integrable_inner (hL' y hy) (hL w hw)) (integrable_inner (hL' y' hy') (hL w hw))]
      refine integral_congr_ae ?_
      filter_upwards [hae] with x hx
      rw [map_add (f := _), ha' _ (ht' y hy _ hx) _ (ht' y' hy' _ hx), inner_add_left]
    · intro a w hw y hy
      beta_reduce
      rw [← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [hae] with x hx
      rw [map_smul, hs' a _ (ht' y hy _ hx), inner_smul_left]
      rfl
    · intro g hg w hw y hy
      beta_reduce
      have key := hq (fun x => ⟪Bm' (R'.σ x y), Bm (R.σ x w)⟫_ℂ) hS
        (ContinuousOn.inner (𝕜 := ℂ) (hco' y hy).1 (hco w hw).1) ?_ (integrable_inner (hL' y hy) (hL w hw)) g hg
      · rw [← key]
        refine integral_congr_ae ?_
        filter_upwards [hae] with x hx
        rw [hm _ hx _ hg, hm' _ hx _ hg]
      · rintro s ⟨h, hh, m, hmN, rfl⟩ x hx
        obtain ⟨-, hT, ⟨u₀, hπ⟩, -⟩ := hS
        have hsG : h * m ∈ GG k r := DDSmoothness.uh_mul hh.1 hmN.1
        have hiso : ∀ a b, ⟪π h a, π h b⟫_ℂ = ⟪a, b⟫_ℂ :=
          (LinearMap.norm_map_iff_inner_map_map ((π h : Wp →L[ℂ] Wp) : Wp →ₗ[ℂ] Wp)).1
            (MatrixMultiplicationContinuity.piW_unitary hT hπ h hh)
        have hψ := MatrixMultiplicationContinuity.psi_norm z Formalism.QuantumDeterminants.cStd m
        beta_reduce
        rw [hm _ hsG _ hx, hm' _ hsG _ hx, he h hh m hmN _ (ht w hw _ hx), he' h hh m hmN _ (ht' y hy _ hx),
          inner_smul_left, inner_smul_right, hiso, ← mul_assoc, Complex.conj_mul', hψ]
        simp
    · intro w hw y hy
      have := norm_integral_inner_le (hL' y hy) (hL w hw) (hI' y hy y hy) (hI w hw w hw)
      simpa [PI.UpqRep.dsigW, mul_comm] using this
  rcases (hP k r ε mu mu' R R' hR hR').2 _ hform with h | ⟨U, hU⟩
  · exact h
  · exact absurd (GlobalTheory.DSInequiv.param_eq_of_equiv hH k r ε mu mu' R R' hR hR' U hU) hne

end GlobalTheory

end
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.bessel_frame_entry_relation : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (l : R.H → Wp) (g : Mx k r), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → PI.UpqRep.IsFrameW k r z g → IsBes R z π l → ∀ i j : Fin k, ∀ v ∈ R.sm, l (R.dC (g * Matrix.single ((fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) i) ((fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) j) 1 * g⁻¹) v) = Formalism.FourierDecayAlt.Q.EcRep (Formalism.QuantumDeterminants.Hpk k r) π (g * Matrix.single ((fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) i) ((fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) j) 1 * g⁻¹) (l v) := by
  first | exact @GlobalTheory.BesselIntertwine.bessel_intertwines_glW | exact GlobalTheory.BesselIntertwine.bessel_intertwines_glW | (intros; apply GlobalTheory.BesselIntertwine.bessel_intertwines_glW <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.RegularisedIntegral

section

open Matrix MeasureTheory Filter Topology
open scoped ENNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B6

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem dilate_subst (D : RealPlaceData k r Wp Wq) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : SS k r → E} (hf : Integrable f D.μSS) {t : ℝ × ℝ} (h1 : 0 < t.1) (h2 : 0 < t.2) :
    Integrable (fun p => f (dilation₂ t p)) D.μSS ∧
      (∫ p, f (dilation₂ t p) ∂D.μSS) = ((t.1 * t.2) ^ kap k r)⁻¹ • ∫ p, f p ∂D.μSS := by
  have hm := map_measure_dilation_pair_eq_smul (dilation_jacobian_every_setting k r Wp Wq D) h1 h2
  have hf' : Integrable f (D.μSS.map (dilation₂ t)) := by
    rw [hm]
    exact hf.smul_measure (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
  refine ⟨hf'.comp_measurable (dilation_action_measurable t), ?_⟩
  rw [← integral_map (dilation_action_measurable t).aemeasurable hf'.1, hm, integral_smul_measure, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity), mul_pow, mul_inv]

def kernel (D : RealPlaceData k r Wp Wq) (F F' : Mat k r → (Wq →L[ℂ] Wp)) (τ : ℝ × ℝ) (q : SS k r × (ℝ × ℝ)) : ℂ :=
  Bt D F F' q * Complex.exp (Complex.I * (phase D τ q.1 q.2 : ℂ))

variable {D : RealPlaceData k r Wp Wq} {α : ℝ}

theorem betaInfTau_eq_kernel (H : SqIntegrable D α) {F F' : Mat k r → (Wq →L[ℂ] Wp)} {c c' : ℝ}
    (hF : AdmW α c 2 2 F) (hF' : AdmW α c' 2 2 F') (τ : ℝ × ℝ) :
    betaInfTau D τ F F' = ∫ p, (∫ t : ℝ × ℝ, kernel D F F' τ (p, t)) ∂D.μSS := by
  unfold betaInfTau
  refine integral_congr_ae ?_
  filter_upwards [ae_inSS D] with p hp
  have key := (bracket_calculus H hF hF' hp).2.2.2 (τ.1 * lam k r D.z (Matrix.of p.1.2))
    (-(τ.2 * lam k r D.z' (Matrix.of p.2.2)))
  have e : ∀ t : ℝ × ℝ, τ.1 * t.1 * lam k r D.z (Matrix.of p.1.2) - τ.2 * t.2 * lam k r D.z' (Matrix.of p.2.2) =
      τ.1 * lam k r D.z (Matrix.of p.1.2) * t.1 + -(τ.2 * lam k r D.z' (Matrix.of p.2.2)) * t.2 := fun t => by ring
  simp only [kernel, phase, Bt_eq D F F' hp, e]
  rw [key, ← mul_assoc, ← Complex.ofReal_mul]
  have : (1 + τ.1 ^ 2 * lam k r D.z (Matrix.of p.1.2) ^ 2)⁻¹ * (1 + τ.2 ^ 2 * lam k r D.z' (Matrix.of p.2.2) ^ 2)⁻¹ *
      ((1 + (τ.1 * lam k r D.z (Matrix.of p.1.2)) ^ 2) *
        (1 + (-(τ.2 * lam k r D.z' (Matrix.of p.2.2))) ^ 2)) = 1 := by
    have a1 : (1 + τ.1 ^ 2 * lam k r D.z (Matrix.of p.1.2) ^ 2) ≠ 0 := by positivity
    have a2 : (1 + τ.2 ^ 2 * lam k r D.z' (Matrix.of p.2.2) ^ 2) ≠ 0 := by positivity
    field_simp
  rw [this]
  simp

theorem kernel_slice (D : RealPlaceData k r Wp Wq) (F F' : Mat k r → (Wq →L[ℂ] Wp)) (τ : ℝ × ℝ) {t : ℝ × ℝ}
    (h1 : 0 < t.1) (h2 : 0 < t.2) :
    (fun p => kernel D F F' τ (p, t)) =ᵐ[D.μSS] fun p =>
      (D.χ t.1 * D.χ t.2 * (t.1 * t.2) ^ kap k r : ℝ) • (xiTau D τ (dilation₂ t p) * Ph D F F' (dilation₂ t p)) := by
  filter_upwards [ae_inSS D] with p hp
  obtain ⟨l1, l2⟩ := lam_dil dilation_unipotent_measure D hp h1 h2
  have l1' : lam k r D.z (Matrix.of (dilation₂ t p).1.2) = t.1 * lam k r D.z (Matrix.of p.1.2) := l1
  have l2' : lam k r D.z' (Matrix.of (dilation₂ t p).2.2) = t.2 * lam k r D.z' (Matrix.of p.2.2) := l2
  unfold kernel xiTau phase
  rw [Bt_eq D F F' hp, l1', l2', Complex.real_smul]
  unfold regBracket
  simp only [mul_assoc]
  ring

theorem kernel_slice_integral (D : RealPlaceData k r Wp Wq) {F F' : Mat k r → (Wq →L[ℂ] Wp)} (τ : ℝ × ℝ)
    (hf : Integrable (fun p => xiTau D τ p * Ph D F F' p) D.μSS) (t : ℝ × ℝ) :
    Integrable (fun p => kernel D F F' τ (p, t)) D.μSS ∧
      (∫ p, kernel D F F' τ (p, t) ∂D.μSS) =
        ((D.χ t.1 * D.χ t.2 : ℝ) : ℂ) * ∫ p, xiTau D τ p * Ph D F F' p ∂D.μSS ∧
      (∫ p, ‖kernel D F F' τ (p, t)‖ ∂D.μSS) =
        |D.χ t.1| * |D.χ t.2| * ∫ p, ‖xiTau D τ p * Ph D F F' p‖ ∂D.μSS := by
  by_cases ht : t ∈ Set.Ioo (1 / 2 : ℝ) 2 ×ˢ Set.Ioo (1 / 2 : ℝ) 2
  · have h1 : 0 < t.1 := lt_trans (by norm_num) ht.1.1
    have h2 : 0 < t.2 := lt_trans (by norm_num) ht.2.1
    have e := kernel_slice D F F' τ h1 h2
    obtain ⟨i1, s1⟩ := dilate_subst D hf h1 h2
    obtain ⟨-, s2⟩ := dilate_subst D hf.norm h1 h2
    have hpos : 0 < (t.1 * t.2) ^ kap k r := by positivity
    refine ⟨(i1.smul (D.χ t.1 * D.χ t.2 * (t.1 * t.2) ^ kap k r : ℝ)).congr e.symm, ?_, ?_⟩
    · rw [integral_congr_ae e, integral_smul, s1, smul_smul, mul_assoc, mul_inv_cancel₀ hpos.ne', mul_one,
        Complex.real_smul]
    · have e' : (fun p => ‖kernel D F F' τ (p, t)‖) =ᵐ[D.μSS] fun p =>
          (|D.χ t.1| * |D.χ t.2| * (t.1 * t.2) ^ kap k r) * ‖xiTau D τ (dilation₂ t p) * Ph D F F' (dilation₂ t p)‖ := by
        filter_upwards [e] with p hp
        rw [hp, norm_smul, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hpos]
      rw [integral_congr_ae e', integral_const_mul, s2, smul_eq_mul, ← mul_assoc, mul_assoc _ _ (_⁻¹),
        mul_inv_cancel₀ hpos.ne', mul_one]
  · have hz : D.χ t.1 * D.χ t.2 = 0 := by
      by_cases h1 : t.1 ∈ Set.Ioo (1 / 2 : ℝ) 2
      · have h2 : t.2 ∉ Set.Ioo (1 / 2 : ℝ) 2 := fun h => ht ⟨h1, h⟩
        rw [cutoff_vanishes_outside_interval D h2, mul_zero]
      · rw [cutoff_vanishes_outside_interval D h1, zero_mul]
    have e : ∀ p, kernel D F F' τ (p, t) = 0 := fun p => by
      unfold kernel
      rw [Bt_zero D F F' p ht, zero_mul]
    rw [← abs_mul, hz]
    simp [e]

theorem betaInfTau_eq_integral (hα : AB k r ≤ α) {F F' : Mat k r → (Wq →L[ℂ] Wp)} (hcF : InCC α 4 F)
    (hcF' : InCC α 4 F') (hΦ : Integrable (Ph D F F') D.μSS) (τ : ℝ × ℝ) :
    betaInfTau D τ F F' = ∫ p, xiTau D τ p * Ph D F F' p ∂D.μSS := by
  obtain ⟨c, hc⟩ := hcF
  obtain ⟨c', hc'⟩ := hcF'
  have hF := admissible_weighted_of_bound hc
  have hF' := admissible_weighted_of_bound hc'
  have H := sqIntegrable_of_threshold D hα
  have := sigmaFinite_μSS D
  have hξ : Continuous (xiTau D τ) := by
    unfold xiTau
    exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
      ((continuous_const.mul (first_eigenvalue_continuous D)).sub (continuous_const.mul (continuous_lambda_second_coordinate D)))))
  have hf : Integrable (fun p => xiTau D τ p * Ph D F F' p) D.μSS := by
    refine hΦ.norm.mono' (hξ.aestronglyMeasurable.mul hΦ.1) (Eventually.of_forall fun p => ?_)
    unfold xiTau
    rw [norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  have hs := kernel_slice_integral D τ hf
  have hmeas : AEStronglyMeasurable (kernel D F F' τ) (D.μSS.prod volume) := by
    unfold kernel
    refine ((cutBracket_measurable H hF hF').mul (Continuous.stronglyMeasurable ?_)).aestronglyMeasurable
    have hp : Continuous fun q : SS k r × (ℝ × ℝ) => phase D τ q.1 q.2 :=
      (phase_continuous D).comp ((continuous_const.prodMk continuous_fst).prodMk continuous_snd)
    exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp hp))
  have hχ : Integrable D.χ := by
    by_contra h
    have := D.χ_int
    rw [integral_undef h] at this
    exact zero_ne_one this
  have hK : Integrable (kernel D F F' τ) (D.μSS.prod volume) := by
    refine (integrable_prod_iff' hmeas).2 ⟨Eventually.of_forall fun t => (hs t).1, ?_⟩
    simp only [fun t => (hs t).2.2]
    refine Integrable.mul_const ?_ _
    rw [Measure.volume_eq_prod]
    exact hχ.abs.mul_prod hχ.abs
  rw [betaInfTau_eq_kernel H hF hF', integral_integral_swap (f := fun p t => kernel D F F' τ (p, t)) hK]
  simp only [fun t => (hs t).2.1]
  rw [integral_mul_const, integral_cutoff_product_eq_one, one_mul]

end

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem betaInf_eq_integral :
    ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
      [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq]
      [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ) (F : Mx k r → (Wq →L[ℂ] Wp)),
      B.AB k r ≤ A → B.InCC A 4 F → Integrable (B.Ph D F F) D.μSS →
      B.betaInf D F F = ∫ p, B.xiTau D (1, 1) p * B.Ph D F F p ∂D.μSS :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA hF hΦ => betaInfTau_eq_integral hA hF hF hΦ (1, 1)

end GlobalTheory.RegularisedIntegral
end
end
