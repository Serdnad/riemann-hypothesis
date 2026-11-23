module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle134
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCompletedIsometryInducingHalfLevelAutomorp
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle026
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle077
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle090
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle089
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
public import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle049
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle063
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EllipticEstimateWordLeOnePlusLaplacianPow
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle056
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle062
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle053
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle054
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactHaarRightInvariantInst
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactUnitaryKernelConcentratedNearOne
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
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.FinalJoin GlobalTheory.CompRat
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfLift

theorem exists_isometry_agreeing {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H) (l : Level H) (g g' : Dw.La →ₗ[𝓞 E] Dw.La)
    (h : ∀ a, g' (g a) - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) ∧
      g (g' a) - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) :
    ∃ s : Sim Dw, (∀ n, s.ν n = 1) ∧
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), Dw.ModN l.M (s.f l.M a - g a) := by
  have hle : ∀ f : Dw.La →ₗ[𝓞 E] Dw.La, l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) ≤
      (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).comap f := fun f => by
    rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  obtain ⟨s, h1, h2, -⟩ := GlobalTheory.LevelIsometry.exists_isometry_inducing E H Dw l
    (LinearEquiv.ofLinear (Submodule.mapQ _ _ g (hle g)) (Submodule.mapQ _ _ g' (hle g'))
      (Submodule.linearMap_qext _ (LinearMap.ext fun a => (Submodule.Quotient.eq _).2 (h a).2))
      (Submodule.linearMap_qext _ (LinearMap.ext fun a => (Submodule.Quotient.eq _).2 (h a).1)))
  refine ⟨s, h1, fun a ha => ?_⟩
  have key : ∀ x, s.f l.M x - g x ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := fun x =>
    (Submodule.Quotient.eq _).1 (h2 x)
  refine Submodule.smul_induction_on ha (fun r hr y _ => ?_) fun y z hy hz => ?_
  · rw [map_smul, map_smul, ← smul_sub]
    exact GlobalTheory.LevelIsometry.modN_smul_of_mem_smul Dw l hr (key y)
  · rw [map_add (f := _), map_add (f := _), add_sub_add_comm]
    exact GlobalTheory.SimAlg.modN_add hy hz

theorem add_sub_eq_nsmul {A : Type} [AddCommGroup A] (N : ℕ) (x e w : A) :
    x + N • e + N • w - x = N • (e + w) := by
  rw [smul_add]
  abel

theorem exists_unitary_inducing : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (V : HSp D) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), GlobalTheory.Member.IotaOK Dw V ι → ∀ g g' : Dw.La →ₗ[𝓞 D.host.E] Dw.La, (∀ a, g' (g a) - a ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La) ∧ g (g' a) - a ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)) → ∃ u ∈ GfC V, gLat V u = latHat V ∧ ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La), ∃ w ∈ latGHat V 1, (finHom V u).1.mulVec (finVec V (ι a)) - finVec V (ι (g a)) = (l.M : ℕ) • w := by
  intro D H Dw l V ι hι g g' h
  obtain ⟨s, hν, hs⟩ := exists_isometry_agreeing Dw l g g' h
  obtain ⟨κ, hκ, hκs⟩ := GlobalTheory.ShortMove.exists_adelic_of_isometry D V H Dw ι hι.emb hι.isom s hν
  obtain ⟨b, hb, u, hu, e⟩ := (GlobalTheory.UnitarySplit.real_finite_split D V).1 κ
  have hb' : finHom V b = 1 := hb
  have hf : finHom V u = finHom V κ := by rw [e, map_mul, hb', one_mul]
  obtain ⟨-, m2, -, m4⟩ := GlobalTheory.Member.latG_move D V
  have hL : latG V 1 = latG V u := GlobalTheory.Member.LatMove.lat_eq_of_hat_eq V (hκ.symm.trans (m2 u κ hf).2.symm)
  have hc := m4 1 u hL
  rw [inv_one, one_mul] at hc
  refine ⟨u, hu, GlobalTheory.MarkDet.gLat_eq_of_finCong hc, fun a ha => ?_⟩
  obtain ⟨c, hc'⟩ := hs a ha
  obtain ⟨w, hw, ew⟩ := hκs l.M (lt_of_lt_of_le (by norm_num) l.three_le) a
  have hm : finVec V (ι c) ∈ latGHat V 1 :=
    (GlobalTheory.Member.LatMove.mem_lat_iff V 1 _).1 (hι.emb.2 ▸ LinearMap.mem_range_self ι c)
  refine ⟨finVec V (ι c) + w, add_mem hm hw, ?_⟩
  have h2 : finVec V (ι (s.f l.M a)) = finVec V (ι (g a)) + l.M • finVec V (ι c) := by
    rw [sub_eq_iff_eq_add'.1 hc', map_add (f := _), map_nsmul]
    funext i
    simp only [finVec, Pi.add_apply, Pi.smul_apply, TensorProduct.tmul_add]
    congr 1
    exact map_nsmul (TensorProduct.mk D.host.F (Af D.host.F) D.host.E 1) _ _
  rw [hf, ew, h2]
  exact add_sub_eq_nsmul _ _ _ _

end GlobalTheory.HalfLift
end

section

set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.FieldSize

theorem card_GL_zmod_le (r g : ℕ) (hg : g ≠ 0) : Nat.card (GL (Fin r) (ZMod g)) ≤ g ^ (r ^ 2) := by
  have : NeZero g := ⟨hg⟩
  have h := Nat.card_le_card_of_injective (Units.val : GL (Fin r) (ZMod g) → Matrix (Fin r) (Fin r) (ZMod g))
    Units.val_injective
  refine h.trans (le_of_eq ?_)
  unfold Matrix
  rw [Nat.card_fun, Nat.card_fun, Nat.card_zmod, ← pow_mul]
  simp [sq]

theorem card_units_quot_le (E : Type) [Field E] [NumberField E] (N : ℕ) (hN : N ≠ 0) :
    0 < Nat.card (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)})ˣ ∧
      Nat.card (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)})ˣ ≤ N ^ Module.finrank ℚ E := by
  have hc : Nat.card (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)}) = N ^ Module.finrank ℚ E := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_natCast, RingOfIntegers.rank]
  have : Finite (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)}) := Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
  exact ⟨Nat.card_pos, hc ▸ Nat.card_le_card_of_injective _ Units.val_injective⟩

theorem roots_sizes (P : Pre) (L : ℝ) (h : HostSz P.host L) :
    Real.log P.restRowsFiniteGroupCard ≤ P.R.f * (P.R.r : ℝ) ^ 2 * (18 * L + 2) ∧
      (∀ p ∈ [P.host.pde, P.host.pde'], 0 < xiOrd P.host (P.host.g 0 * P.host.g 1 * p) ∧
        Real.log (xiOrd P.host (P.host.g 0 * P.host.g 1 * p)) ≤
          1 + Real.log (classNumber P.host.E) + 2 * P.R.f * (21 * L)) ∧ 8 ≤ P.R.f ∧ 2 * P.R.m ≤ P.R.r := by
  have hg : ∀ k, P.host.g k ≠ 0 := fun k => (P.host.g_prime k).ne_zero
  have hg' : ∀ k, (P.host.g k : ℝ) ≠ 0 := fun k => Nat.cast_ne_zero.2 (hg k)
  have h0 := h.g 0
  have h1 := h.g 1
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hle : P.restRowsFiniteGroupCard ≤ (P.host.g 0 * P.host.g 1) ^ (P.R.f * P.R.r ^ 2) := by
      unfold Pre.restRowsFiniteGroupCard
      rw [Fin.prod_univ_two, mul_pow, mul_comm P.R.f, pow_mul, pow_mul]
      exact Nat.mul_le_mul (Nat.pow_le_pow_left (card_GL_zmod_le _ _ (hg 0)) _)
        (Nat.pow_le_pow_left (card_GL_zmod_le _ _ (hg 1)) _)
    have hpos : (0 : ℝ) < P.restRowsFiniteGroupCard := Nat.cast_pos.2 P.restRowsFiniteGroupCard_pos
    refine (Real.log_le_log hpos (Nat.cast_le.2 hle)).trans ?_
    rw [Nat.cast_pow, Real.log_pow, Nat.cast_mul (P.host.g 0), Real.log_mul (hg' 0) (hg' 1)]
    push_cast
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · intro p hp
    have hp' : p ≠ 0 ∧ Real.log p ≤ L := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact ⟨(P.level_prime _ P.host.pde_level.1).ne_zero, h.p.1⟩
      · exact ⟨(P.level_prime _ P.host.pde_level.2).ne_zero, h.p.2⟩
    have hN : P.host.g 0 * P.host.g 1 * p ≠ 0 := mul_ne_zero (mul_ne_zero (hg 0) (hg 1)) hp'.1
    obtain ⟨hu, hu'⟩ := card_units_quot_le P.host.E _ hN
    have hE : Module.finrank ℚ P.host.E = 2 * P.R.f := by
      rw [P.host.finrank_cmField, Formalism.BasicNotions.Ranks.f, Formalism.BasicNotions.Ranks.n]
      ring
    have hh : 0 < classNumber P.host.E := classNumber_pos _
    refine ⟨by unfold xiOrd; positivity, ?_⟩
    unfold xiOrd
    generalize Nat.card (𝓞 P.host.E ⧸
        Ideal.span {((P.host.g 0 * P.host.g 1 * p : ℕ) : 𝓞 P.host.E)})ˣ = c at hu hu' ⊢
    have hu1 : (0 : ℝ) < c := Nat.cast_pos.2 hu
    have hh1 : (0 : ℝ) < classNumber P.host.E := Nat.cast_pos.2 hh
    have h2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    have h3 := Real.log_le_log hu1 (Nat.cast_le.2 hu')
    have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hp'.1
    rw [hE, Nat.cast_pow, Real.log_pow, Nat.cast_mul (P.host.g 0 * P.host.g 1), Nat.cast_mul (P.host.g 0),
      Real.log_mul (mul_ne_zero (hg' 0) (hg' 1)) hp0, Real.log_mul (hg' 0) (hg' 1), Nat.cast_mul,
      Nat.cast_ofNat] at h3
    have h4 : 2 * (P.R.f : ℝ) * (Real.log (P.host.g 0) + Real.log (P.host.g 1) + Real.log p) ≤
        2 * P.R.f * (21 * L) :=
      mul_le_mul_of_nonneg_left (by linarith [h.len, hp'.2]) (by positivity)
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by positivity) hu1.ne',
      Real.log_mul two_ne_zero hh1.ne']
    linarith
  · have he := P.host.two_le_e
    have : 2 ^ 2 ≤ 2 ^ P.R.e := Nat.pow_le_pow_right two_pos he
    have h2 := P.R.toFrame.two_pow_le_ord
    unfold Ranks.f Ranks.n
    omega
  · have := P.R.m_add_three_le_k
    unfold Ranks.r
    omega

end GlobalTheory.FieldSize
end

section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined

theorem _root_.GlobalTheory.T.signature_lieSet_expand_orthonormal_bases : ∀ (n : ℕ) (ε : Fin n → Bool), ∀ U ∈ lieSet ε, U = ∑ b, (trace (U * pB ε b)).re • pB ε b - ∑ i, (trace (U * kB ε i)).re • kB ε i := by
  first | exact @GlobalTheory.TypeSum.CasBasis.lieSet_expand_bases | exact GlobalTheory.TypeSum.CasBasis.lieSet_expand_bases | (intros; apply GlobalTheory.TypeSum.CasBasis.lieSet_expand_bases <;> assumption)
end

section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace


theorem _root_.GlobalTheory.T.elliptic_estimate_word_le_onePlusLaplacian_pow : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ l : List (Mx n), (∀ X ∈ l, X ∈ lieSet ε) → ∃ (s : ℕ) (C : ℝ), ∀ v, Sm ε σ v → ‖Dw σ l v‖ ≤ C * ‖(lapOne ε σ)^[s] v‖ := by
  first | exact @GlobalTheory.TypeSum.Elliptic.word_le_lapOne | exact GlobalTheory.TypeSum.Elliptic.word_le_lapOne | (intros; apply GlobalTheory.TypeSum.Elliptic.word_le_lapOne <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.KFourier
open MeasureTheory
variable {n : ℕ}

theorem orth_decomp_L (ε : Fin n → Bool) (d : ℕ) (p : KG ε → ℂ) (hp : Continuous p) :
    ∃ p' ∈ polyV ε d, ∀ q ∈ polyV ε d, ∫ k, star (q k) * (p k - p' k) ∂(muK ε) = 0 :=
  GlobalTheory.T.exists_orthogonal_projection_polynomial_compact_unitary ε d p hp

theorem conv_swap_L (ε : Fin n → Bool) (e q g : KG ε → ℂ) (he : Continuous e) (hq : Continuous q)
    (hg : Continuous g) :
    ∫ k', star (q k') * ∫ k, e k * g (k' * k) ∂(muK ε) ∂(muK ε) =
      ∫ y, g y * ∫ x, e x * star (q (y * x⁻¹)) ∂(muK ε) ∂(muK ε) :=
  GlobalTheory.T.integral_star_mul_convolution_eq_integral_swap ε e q g he hq hg

theorem eq_zero_of_orth_L (ε : Fin n → Bool) (h : KG ε → ℂ) (hh : Continuous h)
    (ho : ∀ d, ∀ q ∈ polyV ε d, ∫ k, star (q k) * h k ∂(muK ε) = 0) : h = 0 :=
  GlobalTheory.T.eq_zero_of_orthogonal_compactUnitaryPolyFun ε h hh ho

theorem integrable_of_cont (ε : Fin n → Bool) {f : KG ε → ℂ} (hf : Continuous f) : Integrable f (muK ε) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem firstCountable_KG (ε : Fin n → Bool) : FirstCountableTopology (KG ε) :=
  haveI : FirstCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (FirstCountableTopology (Fin n → Fin n → ℂ))
  ((isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal).isInducing.firstCountableTopology

theorem continuous_param (ε : Fin n → Bool) {F : KG ε → KG ε → ℂ} (hF : Continuous (Function.uncurry F)) :
    Continuous fun a => ∫ k, F a k ∂(muK ε) := by
  haveI := firstCountable_KG ε
  have := continuous_parametric_integral_of_continuous (μ := muK ε) hF (s := Set.univ) isCompact_univ
  simpa [Measure.restrict_univ] using this

theorem sum_ker_poly (ε : Fin n → Bool) (e : ℕ → KG ε → ℂ) (he : ∀ i, IsKer ε i (e i)) :
    ∀ d, ∀ p ∈ polyV ε d, ∑ i ∈ Finset.range (d + 1), ∫ k, e i k * p k ∂(muK ε) = p 1 := by
  intro d
  induction d with
  | zero =>
    intro p hp
    simp only [zero_add, Finset.range_one, Finset.sum_singleton]
    exact (he 0).2.2 p hp (fun q hq => by simp [lowV] at hq; simp [hq])
  | succ d ih =>
    intro p hp
    obtain ⟨p', hp', horth⟩ := orth_decomp_L ε d p (continuous_of_mem hp)
    have hp'' : (fun k => p k - p' k) ∈ polyV ε (d + 1) :=
      sub_mem hp (polyV_mono ε (Nat.le_succ d) hp')
    have hcp : Continuous p := continuous_of_mem hp
    have hcp' : Continuous p' := continuous_of_mem hp'
    have hce : ∀ i, Continuous (e i) := fun i => continuous_of_mem (he i).1
    have hsplit : ∀ i, ∫ k, e i k * p k ∂(muK ε) =
        ∫ k, e i k * p' k ∂(muK ε) + ∫ k, e i k * (p k - p' k) ∂(muK ε) := by
      intro i
      rw [← integral_add (integrable_of_cont ε (f := fun k => e i k * p' k) ((hce i).mul hcp'))
        (integrable_of_cont ε (f := fun k => e i k * (p k - p' k)) ((hce i).mul (hcp.sub hcp')))]
      congr 1; funext k; ring
    rw [Finset.sum_range_succ, hsplit (d + 1), Finset.sum_congr rfl (fun i _ => hsplit i),
      Finset.sum_add_distrib, ih p' hp']
    have h0 : ∫ k, e (d + 1) k * p' k ∂(muK ε) = 0 := (he (d + 1)).2.1 p' hp'
    have h1 : ∫ k, e (d + 1) k * (p k - p' k) ∂(muK ε) = p 1 - p' 1 :=
      (he (d + 1)).2.2 _ hp'' (fun q hq => horth q hq)
    have h2 : ∀ i ∈ Finset.range (d + 1), ∫ k, e i k * (p k - p' k) ∂(muK ε) = 0 := by
      intro i hi
      have hi' : i ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      have hs : (fun k => star (e i k)) ∈ polyV ε d := polyV_mono ε hi' (star_mem (he i).1)
      have := horth _ hs
      simpa using this
    rw [Finset.sum_eq_zero h2, h0, h1]
    ring

theorem ker_vanish (ε : Fin n → Bool) (e : ℕ → KG ε → ℂ) (he : ∀ i, IsKer ε i (e i)) {d i : ℕ} (hi : d < i)
    {p : KG ε → ℂ} (hp : p ∈ polyV ε d) : ∫ k, e i k * p k ∂(muK ε) = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  exact (he (j + 1)).2.1 p (polyV_mono ε (by omega) hp)

theorem hasSum_kFourier (ε : Fin n → Bool) (e : ℕ → KG ε → ℂ) (he : ∀ i, IsKer ε i (e i))
    (g : KG ε → ℂ) (hg : Continuous g) (b : ℕ → ℝ) (hb : Summable b)
    (hbd : ∀ i (k' : KG ε), ‖∫ k, e i k * g (k' * k) ∂(muK ε)‖ ≤ b i) :
    HasSum (fun i => ∫ k, e i k * g k ∂(muK ε)) (g 1) := by
  have hce : ∀ i, Continuous (e i) := fun i => continuous_of_mem (he i).1
  set P : ℕ → KG ε → ℂ := fun i k' => ∫ k, e i k * g (k' * k) ∂(muK ε) with hPdef
  have hPc : ∀ i, Continuous (P i) := fun i =>
    continuous_param ε (F := fun k' k => e i k * g (k' * k))
      (((hce i).comp continuous_snd).mul (hg.comp (continuous_fst.mul continuous_snd)))
  have hsum : ∀ k', Summable (fun i => P i k') := fun k' => Summable.of_norm_bounded hb (fun i => hbd i k')
  set u : KG ε → ℂ := fun k' => ∑' i, P i k' with hudef
  have hu : Continuous u := continuous_tsum hPc hb hbd
  have key : ∀ d, ∀ q ∈ polyV ε d, ∫ k, star (q k) * (u k - g k) ∂(muK ε) = 0 := by
    intro d q hq
    have hcq : Continuous q := continuous_of_mem hq
    obtain ⟨M, hM⟩ : ∃ M, ∀ k, ‖star (q k)‖ ≤ M := by
      obtain ⟨M, hM⟩ := (isCompact_univ.image (continuous_star.comp hcq)).isBounded.exists_norm_le
      exact ⟨M, fun k => hM _ ⟨k, Set.mem_univ _, rfl⟩⟩
    have hint : ∀ i, Integrable (fun k => star (q k) * P i k) (muK ε) := fun i =>
      integrable_of_cont ε ((continuous_star.comp hcq).mul (hPc i))
    have hnorm : ∀ i, ∫ k, ‖star (q k) * P i k‖ ∂(muK ε) ≤ M * b i := by
      intro i
      calc ∫ k, ‖star (q k) * P i k‖ ∂(muK ε) ≤ ∫ _k, M * b i ∂(muK ε) := by
            refine integral_mono (hint i).norm (integrable_const _) (fun k => ?_)
            rw [norm_mul]
            exact mul_le_mul (hM k) (hbd i k) (norm_nonneg _) ((norm_nonneg _).trans (hM k))
        _ = M * b i := by simp
    have hsn : Summable fun i => ∫ k, ‖star (q k) * P i k‖ ∂(muK ε) :=
      Summable.of_nonneg_of_le (fun i => integral_nonneg fun k => norm_nonneg _) hnorm (hb.mul_left M)
    have e1 : ∫ k, star (q k) * u k ∂(muK ε) = ∑' i, ∫ k, star (q k) * P i k ∂(muK ε) := by
      rw [integral_tsum_of_summable_integral_norm hint hsn]
      congr 1; funext k
      rw [hudef]; simp only
      exact (tsum_mul_left).symm
    set r : ℕ → KG ε → ℂ := fun i y => ∫ x, e i x * star (q (y * x⁻¹)) ∂(muK ε) with hrdef
    have hpy : ∀ y, (fun x => star (q (y * x⁻¹))) ∈ polyV ε d := fun y =>
      star_mem (inv_mem (φ := fun k => q (y * k)) (mul_left_mem y hq))
    have hrc : ∀ i, Continuous (r i) := fun i =>
      continuous_param ε (F := fun y x => e i x * star (q (y * x⁻¹)))
        (((hce i).comp continuous_snd).mul (continuous_star.comp (hcq.comp (continuous_fst.mul continuous_snd.inv))))
    have e2 : ∀ i, ∫ k, star (q k) * P i k ∂(muK ε) = ∫ y, g y * r i y ∂(muK ε) := fun i =>
      conv_swap_L ε (e i) q g (hce i) hcq hg
    have hr0 : ∀ i ∉ Finset.range (d + 1), ∫ y, g y * r i y ∂(muK ε) = 0 := by
      intro i hi
      have hi' : d < i := by simpa using hi
      have : ∀ y, r i y = 0 := fun y => ker_vanish ε e he hi' (hpy y)
      simp [this]
    have hrs : ∀ y, ∑ i ∈ Finset.range (d + 1), r i y = star (q y) := by
      intro y
      have := sum_ker_poly ε e he d _ (hpy y)
      simp only [hrdef]
      simpa using this
    have e3 : ∫ k, star (q k) * u k ∂(muK ε) = ∫ k, star (q k) * g k ∂(muK ε) := by
      rw [e1, tsum_congr e2, tsum_eq_sum hr0, ← integral_finsetSum]
      · congr 1; funext y
        rw [← Finset.mul_sum, hrs y, mul_comm]
      · intro i _
        exact integrable_of_cont ε (hg.mul (hrc i))
    have hsub : (fun k => star (q k) * (u k - g k)) = fun k => star (q k) * u k - star (q k) * g k := by
      funext k; ring
    rw [hsub, integral_sub (integrable_of_cont ε (f := fun k => star (q k) * u k) ((continuous_star.comp hcq).mul hu))
      (integrable_of_cont ε (f := fun k => star (q k) * g k) ((continuous_star.comp hcq).mul hg)), e3, sub_self]
  have hzero := eq_zero_of_orth_L ε (fun k => u k - g k) (hu.sub hg) key
  have h1 : u 1 = g 1 := sub_eq_zero.1 (congrFun hzero 1)
  have h2 : u 1 = ∑' i, ∫ k, e i k * g k ∂(muK ε) := by simp [hudef, hPdef]
  rw [← h1, h2]
  have := (hsum 1).hasSum
  simpa [hPdef] using this

end GlobalTheory.KFourier
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory


theorem _root_.GlobalTheory.T.exists_compactUnitaryKernel_concentrated_near_one : ∀ {n : ℕ} (ε : Fin n → Bool), ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, ∃ κ : KG ε → ℝ, Continuous κ ∧ (∀ k, 0 ≤ κ k) ∧ ∫ k, κ k ∂(muK ε) = 1 ∧ (fun k => (κ k : ℂ)) ∈ polyV ε m ∧ ∫ k, κ k * Real.sqrt (Formalism.REAL.hs (toMK k - 1)) ∂(muK ε) ≤ C * ((m : ℝ) + 1) ^ (-(1 / 4 : ℝ)) := by
  first | exact @GlobalTheory.KFourier.kernel_near_one | exact GlobalTheory.KFourier.kernel_near_one | (intros; apply GlobalTheory.KFourier.kernel_near_one <;> assumption)
end
