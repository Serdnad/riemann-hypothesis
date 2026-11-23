module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.BaseIntSet
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle843
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle854
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle014
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle031
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle030
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.SubsingletonOfScalar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormBoundGoodPointsExtendsAllPoints
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle976
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle889
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle910
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle897
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle886
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle862
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle132
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle975
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupSetFinitelyGenerated
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle059
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle033
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.FiniteExtensionRamificationEmbedding
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle068
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle097
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle082
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle033
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
import Mathlib.RingTheory.Valuation.LocalSubring
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
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt

@[expose] public section

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.LevelSeries

variable {D : D7}

theorem not_mem_of_coprime {a b : ℕ} (h : Nat.Coprime a b) {PP : Formalism.L2.DIV.Pl D.host.E}
    (ha : ((a : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) : ((b : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun hb => by
  have h1 : IsCoprime ((a : ℤ) : 𝓞 D.host.E) ((b : ℤ) : 𝓞 D.host.E) :=
    (Nat.isCoprime_iff_coprime.2 h).map (Int.castRingHom (𝓞 D.host.E))
  obtain ⟨u, v, huv⟩ := h1
  push_cast at huv
  apply PP.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← huv]
  exact add_mem (Ideal.mul_mem_left _ _ ha) (Ideal.mul_mem_left _ _ hb)

theorem exists_flip_theta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → Odd W.rank → ∀ (χ : Formalism.L2.Host.HChar D.host.E) (M₀ l : ℕ), ChiData χW χ M₀ → l.Prime → M₀ ≠ 0 → ∃ (Z : Finset (GA D V)) (c : ℕ), (∀ z ∈ Z, z ∈ GfC V) ∧ ∀ (H : Geo.Tor.Host D.host.E) (l₂ : Geo.Tor.Level H) (pd : ℕ), l₂.M = M₀ * pd → Nat.Coprime pd M₀ → Nat.Coprime pd l → Nat.Coprime l₂.M (GlobalTheory.Tow.badN D) → ∀ (k : Type) [Field k] [NumberField k] (σ : k →+* ℂ) (la : HeightOneSpectrum (𝓞 k)) (O : Subring ℂ), ((l : ℕ) : 𝓞 k) ∈ la.asIdeal → ValRing σ la O → ConjIn D σ → χ.ValuesIn (-1 / 2) σ → zeta l₂.M ∈ O → ∀ (e e₂ : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e P → (∀ PP ∈ P, ((l₂.M : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → IsHalfIdem l₂ e₂ → ∃ z₂ ∈ Z, ∃ z₁ ∈ GfC V, OneAt V l z₁ ∧ ∀ f ∈ trSp ψ V W ΛV ΛW f₀ e l₂.M O, ∃ f' ∈ trSp ψ V W ΛV ΛW f₀ e₂ l₂.M O, ∀ (BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (Q : MvPolynomial (FVar D W.rank V.rank) ℂ) (s : GA D V) (g : GA D W), (l : ℂ) ^ c * thetaKO om s g (stdF ψ θ V W sW BW f Q) = thetaKO om (s * z₂ * z₁) g (stdF ψ θ V W sW BW f' Q) := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hP hodd χ M₀ l hχ hl hM₀
  have hfin : {PP : Formalism.L2.DIV.Pl D.host.E | ((M₀ : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal}.Finite := by
    have h0 : Ideal.span {((M₀ : ℕ) : 𝓞 D.host.E)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hM₀
    refine (Ideal.finite_factors h0).subset fun PP hPP => ?_
    exact Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hPP)
  choose zOf hzG hzOne hzFlip using fun T : Finset (Formalism.L2.DIV.Pl D.host.E) =>
    GlobalTheory.T.exists_central_flip_translate_halfPlaces_thetaPair D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T M₀
  choose cOf hcOf using fun T => GlobalTheory.T.flipScalar_primePow_integral_at_levelPlaces D ψ θ V W χV χW om ΛV ΛW sW f₀ hP hodd χ M₀ l hχ hl hM₀ T
  refine ⟨hfin.toFinset.powerset.image zOf, hfin.toFinset.powerset.sup cOf, ?_, ?_⟩
  · intro z hz
    obtain ⟨T, -, rfl⟩ := Finset.mem_image.1 hz
    exact hzG T
  intro H l₂ pd hM hc1 hc2 hbad k _ _ σ la O hla hO hconj hval hz e e₂ P he hPM he₂
  have hoddM : Odd (M₀ * pd) := hM ▸ l₂.odd
  have hoddM₀ : Odd M₀ := (Nat.odd_mul.1 hoddM).1
  have hoddpd : Odd pd := (Nat.odd_mul.1 hoddM).2
  set T₀ := P.filter fun PP => ((M₀ : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal ∧ ¬ l₂.Mb ≤ PP.asIdeal with hT₀
  set T₁ := P.filter fun PP => ((pd : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal ∧ ¬ l₂.Mb ≤ PP.asIdeal with hT₁
  set P₁ := (P \ T₀) ∪ T₀.image Formalism.L2.DIV.conjPl with hP₁
  have hT₁P₁ : T₁ ⊆ P₁ := fun PP hPP => by
    obtain ⟨h1, h2, -⟩ := Finset.mem_filter.1 hPP
    refine Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨h1, fun h3 => ?_⟩)
    exact not_mem_of_coprime hc1 h2 (Finset.mem_filter.1 h3).2.1
  obtain ⟨⟨eT₀, heT₀⟩, e₁, he₁⟩ := GlobalTheory.T.exists_idempotentSum_subset_and_conjugate_flip D e P T₀ he (Finset.filter_subset _ _)
  obtain ⟨⟨eT₁, heT₁⟩, e₃, he₃⟩ := GlobalTheory.T.exists_idempotentSum_subset_and_conjugate_flip D e₁ P₁ T₁ he₁ hT₁P₁
  have hT₀S : T₀ ∈ hfin.toFinset.powerset :=
    Finset.mem_powerset.2 fun PP hPP => hfin.mem_toFinset.2 (Finset.mem_filter.1 hPP).2.1
  obtain ⟨x₂, hx₂, hstep₂⟩ := hzFlip T₀ eT₀ heT₀ hoddM₀ (Nat.Coprime.coprime_mul_right (hM ▸ hbad)) fun PP hPP => (Finset.mem_filter.1 hPP).2.1
  obtain ⟨z₁, hz₁G, hz₁One, hz₁F⟩ := GlobalTheory.T.exists_central_flip_translate_halfPlaces_thetaPair D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T₁ pd
  obtain ⟨x₁, hx₁, hstep₁⟩ := hz₁F eT₁ heT₁ hoddpd (Nat.Coprime.coprime_mul_left (hM ▸ hbad)) fun PP hPP => (Finset.mem_filter.1 hPP).2.1
  have hsub := GlobalTheory.T.halfTranslates_le_levelHalfTranslates_of_dvd D H l₂ e₂ e₃ _ he₂ he₃ (fun PP hPP => by
    rcases Finset.mem_union.1 hPP with h1 | h1
    · obtain ⟨h2, h3⟩ := Finset.mem_sdiff.1 h1
      rcases Finset.mem_union.1 h2 with h4 | h4
      · obtain ⟨h5, h6⟩ := Finset.mem_sdiff.1 h4
        by_contra h7
        have h8 := hPM PP h5
        rw [hM, Nat.cast_mul] at h8
        rcases PP.isPrime.mem_or_mem h8 with h9 | h9
        · exact h6 (Finset.mem_filter.2 ⟨h5, h9, h7⟩)
        · exact h3 (Finset.mem_filter.2 ⟨h5, h9, h7⟩)
      · obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.1 h4
        obtain ⟨hQ1, -, hQ2⟩ := Finset.mem_filter.1 hQ
        exact GlobalTheory.T.levelHalf_le_conj_place_of_not_le D H l₂ Q (hPM Q hQ1) hQ2
    · obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.1 h1
      obtain ⟨hQ1, -, hQ2⟩ := Finset.mem_filter.1 hQ
      exact GlobalTheory.T.levelHalf_le_conj_place_of_not_le D H l₂ Q (hPM Q hQ1) hQ2) ψ V W ΛV ΛW f₀ l₂.M O
  have hlO : ((l : ℕ) : ℂ) ∈ O := natCast_mem O l
  have ha : (l : ℂ) ^ (hfin.toFinset.powerset.sup cOf) * flipScal χW V W T₀ M₀ x₂ ∈ O := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := cOf) hT₀S)
    rw [hd, pow_add, mul_assoc]
    exact mul_mem (pow_mem hlO _) (hcOf T₀ eT₀ x₂ heT₀ (fun PP hPP => (Finset.mem_filter.1 hPP).2.1) hx₂ k σ la O hla hO
      hconj hval hoddM₀ (Nat.Coprime.coprime_mul_right (hM ▸ hbad)))
  have hb : flipScal χW V W T₁ pd x₁ ∈ O :=
    GlobalTheory.T.flipScalar_mem_coefficientRing_auxiliaryLevel D ψ θ V W χV χW om ΛV ΛW sW f₀ hP hodd χ M₀ l pd hχ hl hc1 hc2 (Nat.Coprime.coprime_mul_left (hM ▸ hbad))
      k σ la O hla hO hconj hval T₁ eT₁ x₁ heT₁ (fun PP hPP => (Finset.mem_filter.1 hPP).2.1) hx₁
  refine ⟨zOf T₀, Finset.mem_image_of_mem _ hT₀S, z₁, hz₁G,
    hz₁One l (fun PP hPP => not_mem_of_coprime hc2 (Finset.mem_filter.1 hPP).2.1), fun f hf => ?_⟩
  obtain ⟨F₁, hF₁, hF₁eq⟩ := hstep₂ l₂.M pd e e₁ P O hM
    (fun PP hPP => not_mem_of_coprime (Nat.Coprime.symm hc1) (Finset.mem_filter.1 hPP).2.1) he (Finset.filter_subset _ _) he₁ hz f hf
  obtain ⟨F₂, hF₂, hF₂eq⟩ := hstep₁ l₂.M M₀ e₁ e₃ P₁ O (by rw [hM, mul_comm])
    (fun PP hPP => not_mem_of_coprime hc1 (Finset.mem_filter.1 hPP).2.1) he₁ hT₁P₁ he₃ hz F₁ hF₁
  set c := hfin.toFinset.powerset.sup cOf
  refine ⟨(⟨_, mul_mem ha hb⟩ : O) • F₂, Submodule.smul_mem _ _ (hsub hF₂), fun BW Q s g => ?_⟩
  have hom : om (zOf T₀ * z₁, 1) ((⟨_, mul_mem ha hb⟩ : O) • F₂) = ((l : ℂ) ^ c) • f := by
    have e1 : ((zOf T₀ * z₁, 1) : GA D V × GA D W) = (zOf T₀, 1) * (z₁, 1) := by simp
    rw [e1, map_mul, Module.End.mul_apply, Subring.smul_def]
    change om (zOf T₀, 1) (om (z₁, 1) (((l : ℂ) ^ c * flipScal χW V W T₀ M₀ x₂ * flipScal χW V W T₁ pd x₁) • F₂)) = _
    rw [← smul_smul, map_smul, hF₂eq, ← smul_smul, map_smul, hF₁eq]
  have := GlobalTheory.T.thetaKernel_fockVector_eq_of_finite_point_move D ψ θ V W χV χW om ΛV ΛW sW f₀ hP (zOf T₀ * z₁) (mul_mem (hzG T₀) hz₁G) e e₂ l₂.M O f _ _ hf
    (Submodule.smul_mem _ _ (hsub hF₂)) hom BW Q s g
  rw [← mul_assoc] at this
  exact this

end GlobalTheory.LevelSeries

end
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.exists_dominantWeight_cuspSections_noCommonZero : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∃ (b : (D.host.E →+* ℂ) × ℕ → ℕ) (m : ℕ), Dom b m ∧ LastPos (T.Q.Dw j) b ∧ 4 * (Module.finrank ℚ D.host.E * D.R.r) + 4 ≤ m ∧ ∀ k, ∀ x ∈ ((T.U j σ).X k).dom, ∃ P ∈ Formalism.L2.Pj.holSub0 (T.U j σ).X (laU (T.U j σ) b m), P k x ≠ 0 := by
  first | exact @GlobalTheory.BpfUniform.exists_weight_noCommonZero | exact GlobalTheory.BpfUniform.exists_weight_noCommonZero | (intros; apply GlobalTheory.BpfUniform.exists_weight_noCommonZero <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EqCharCusp

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GoodPts GlobalTheory.GoodTransfer

theorem exists_goodAt {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Level H) :
    ∃ p : ℕ, p.Prime ∧ l.GoodAt p := by
  obtain ⟨p, hle, hp⟩ := Nat.exists_infinite_primes (l.M + 1)
  refine ⟨p, hp, ?_⟩
  have h3 := l.three_le
  have hM : ¬ p ∣ l.M := fun hd => by have := Nat.le_of_dvd (by omega) hd; omega
  unfold Level.GoodAt
  rw [Nat.factorization_eq_zero_of_not_dvd hM]
  simpa using h3

theorem exists_place (K : Type) [Field K] [NumberField K] (p : ℕ) (hp : p.Prime) :
    ∃ la : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ la.asIdeal := by
  have hP : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2 (Nat.prime_iff_prime_int.mp hp)
  obtain ⟨Q, -, hQ, hQl⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 K) (Ideal.span {(p : ℤ)}) ⊥
    (by rw [(show Ideal.under _ ⊥ = ⊥ from Ideal.comap_bot_of_injective _ (algebraMap ℤ (𝓞 K)).injective_int)]; exact bot_le)
  have hpQ : (p : 𝓞 K) ∈ Q := by
    have : ((p : ℤ)) ∈ Ideal.under ℤ Q := by
      rw [hQl]
      exact Ideal.mem_span_singleton_self _
    simpa using this
  refine ⟨⟨Q, hQ, fun h => ?_⟩, hpQ⟩
  rw [h] at hQl
  change Ideal.comap (algebraMap ℤ (𝓞 K)) ⊥ = _ at hQl
  rw [Ideal.comap_bot_of_injective _ (algebraMap ℤ (𝓞 K)).injective_int] at hQl
  have : ((p : ℤ)) ∈ (⊥ : Ideal ℤ) := hQl ▸ Ideal.mem_span_singleton_self _
  exact hp.ne_zero (by exact_mod_cast (Ideal.mem_bot.1 this))

theorem integral_of_eqChar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), Dom a n → f ∈ cusp Xo c U a n → ∀ (T : CDVR), Countable (IsLocalRing.ResidueField T.V) → ∀ (io : c.F →+* T.Fr), (∀ k : c.F, io k ∈ (algebraMap T.V T.Fr).range) → ∀ y : IntFr Xo c T io, evI y f ∈ (algebraMap T.V T.Fr).range := by
  intro E _ _ _ H Dw l Xo c r U hU a n f hd hf T hcnt io hint y
  obtain ⟨p, hp, hg⟩ := exists_goodAt l
  obtain ⟨la, hpl⟩ := exists_place c.F p hp
  let _ := io.toAlgebra
  obtain ⟨b, hb⟩ := exists_factor T (io.comp (la.valuation c.F).valuationSubring.subtype) (fun x => hint _)
  let z : Sp T.Fr ⟶ Xo.XF c := pullback.lift y.1.x (spMap io) (y.1.x_over.trans (sp_comp _ _).symm)
  have hz₁ : z ≫ pullback.fst _ _ = y.1.x := pullback.lift_fst _ _ _
  have hz₂ : z ≫ pullback.snd _ _ = spMap io := pullback.lift_snd _ _ _
  have hA : ∀ Y : Model Xo c (la.valuation c.F).valuationSubring.subtype, PushInvertible Y.t.G Y.t.PP.L →
      ∀ y' : Sp T.V ⟶ Y.X, z ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ y' → Set.range y' ⊆ abLocus Y.t.G →
      evI y f ∈ (algebraMap T.V T.Fr).range := fun Y hP y' h3 hr =>
    GlobalTheory.T.section_integral_equalChar_abelianLocus E H Dw l Xo c a n f hf.1 la Y hP T io hint y ⟨y', z, hz₁, hz₂, h3, hr⟩
  rcases Nat.eq_zero_or_pos (Dw.p + Dw.q) with hD | hD
  · obtain ⟨Y, hP⟩ := GlobalTheory.SupFinite.exists_model_rank_zero Xo c hD (la.valuation c.F).valuationSubring.subtype
    obtain ⟨⟨y', ⟨-, hz₃⟩, -⟩, -⟩ :=
      GlobalTheory.ValuativeExtension.valuation_extension E H Dw l Xo c _ _ Y T.V T.Fr b io z hb hz₂
    refine hA Y hP y' hz₃.symm ?_
    rw [GlobalTheory.DefiniteAbelian.abLocus_eq_univ (by omega) _ Y]
    exact Set.subset_univ _
  obtain ⟨Y, hP, hop, hS, h3, h4⟩ := exists_model (by omega) Xo c la p hp hpl hg
  obtain ⟨⟨y', ⟨hy', hz₃⟩, -⟩, -⟩ :=
    GlobalTheory.ValuativeExtension.valuation_extension E H Dw l Xo c _ _ Y T.V T.Fr b io z hb hz₂
  by_cases hr : Set.range y' ⊆ abLocus Y.t.G
  · exact hA Y hP y' hz₃.symm hr
  obtain ⟨T', g, ϖ, a₀, hg₁, hg₂, hϖ, hA'⟩ := GlobalTheory.T.exists_arcData_of_badReduction_finiteExtension E H Dw l Xo c _ Y h3 hS T io b y' z hb hy' hz₂ hz₃.symm hr
  obtain ⟨i, ρ, hρ, hi, hv, -⟩ := GlobalTheory.EtaVal.finite_extension_ramification_embedding T T' g hg₁ hg₂
  obtain ⟨y₁, φ, hφ, hy₁⟩ := GlobalTheory.IntFrBaseChange.exists_intFr_baseChange E H Dw l Xo c T T' io y i ρ hρ
    (fun x _ => hv x)
  let _ := (i.comp io).toAlgebra
  have e₁ : (algebraMap T'.V T'.Fr).comp g = i.comp (algebraMap T.V T.Fr) := RingHom.ext fun x => (hi x).symm
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.exists_complex_embedding_fractionField_finite_over_cdvr c.F c.F.val.toRingHom T T' g hg₁ hg₂ hcnt (i.comp io)
  have hint' : ∀ k : c.F, (i.comp io) k ∈ (algebraMap T'.V T'.Fr).range := fun k => by
    obtain ⟨v, hv'⟩ := hint k
    exact ⟨g v, by rw [RingHom.comp_apply, ← hv', hi]⟩
  have key := GlobalTheory.T.cuspForm_integral_arc_section_equalChar E H Dw l Xo c r U hU la Y hP hop h4 a n f hd hf
    (fun T₁ io₁ h₁ y₂ hy₂ => GlobalTheory.T.section_integral_equalChar_abelianLocus E H Dw l Xo c a n f hf.1 la Y hP T₁ io₁ h₁ y₂ hy₂)
    T' (i.comp io) hint' ⟨κ, hκ⟩ (g.comp b)
    (by rw [← RingHom.comp_assoc, e₁, RingHom.comp_assoc, hb]; rfl) ϖ hϖ a₀ (spMap g ≫ y')
    (by rw [Category.assoc, hy', sp_comp]) hA' y₁ (spMap i ≫ z)
    (by rw [Category.assoc, hz₁, hy₁.1, hφ]) (by rw [Category.assoc, hz₂, sp_comp])
    (by rw [Category.assoc, ← hz₃, ← Category.assoc, ← Category.assoc, sp_comp, sp_comp, e₁])
  have hE : GlobalTheory.Reg.EvLaws Xo c := by
    have hB : Out.SecBaseChangeSt := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
    obtain ⟨-, -, hwd, hwt, hint, -⟩ := GlobalTheory.T.framedModuli_algebraicLaws_chart_weight_integrality hB E H Dw l Xo c
    have hbc : GlobalTheory.Reg.FrBC Xo c := fun S T _ _ _ _ φ y =>
      GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c S T φ y
    exact ⟨hwd, GlobalTheory.T.framedPoint_reduced_from_testRing hB E H Dw l Xo c, hwt, hbc⟩
  have e₂ : evI y₁ f = φ (evI y f) :=
    (GlobalTheory.ArcQ.evR_natural_weight_scaling E H Dw l Xo c hE a n f hf.1 T.Fr).1 _ φ _ _ hy₁
  have e₃ : φ (evI y f) = i (evI y f) := RingHom.congr_fun hφ _
  have key' : InV T' (i (evI y f)) := by rw [← e₃, ← e₂]; exact key
  rw [inV_iff, hv] at key'
  show InV T (evI y f)
  rw [inV_iff]
  exact nonneg_of_mul_nonneg_right key' (by exact_mod_cast hρ)

end GlobalTheory.EqCharCusp
end
end
