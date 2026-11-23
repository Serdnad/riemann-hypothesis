module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle173
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle300
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1843
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1769
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1770
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle199
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1287
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1393
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1524
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1294
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1794
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianSelfDualLatticeHyperbolicPlaneSplit
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinIsotropicLine
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle266

@[expose] public section

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.SkewAdCover

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sig_sig (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem sigR_sigR (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (z : AF F ⊗[F] E) :
    sigR (AF F) σ (sigR (AF F) σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [sigR, sig_sig σ h]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem sigR_inclR (σ : E →ₐ[F] E) (e : E) : sigR (AF F) σ (inclR (F := F) (AF F) e) = inclR (AF F) (σ e) := by
  simp [sigR, inclR]

theorem sigR_alg (σ : E →ₐ[F] E) (c : F) :
    sigR (AF F) σ (algebraMap F (AF F ⊗[F] E) c) = algebraMap F (AF F ⊗[F] E) c :=
  (Algebra.TensorProduct.map (AlgHom.id F (AF F)) σ).commutes c

theorem inclR_alg (c : F) : inclR (F := F) (AF F) (algebraMap F E c) = algebraMap F (AF F ⊗[F] E) c :=
  (Algebra.TensorProduct.includeRight (R := F) (A := AF F) (B := E)).commutes c

theorem continuous_sigR (σ : E →ₐ[F] E) : Continuous (sigR (AF F) σ) := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  have : (sigR (AF F) σ : AF F ⊗[F] E → AF F ⊗[F] E) = LinearMap.baseChange (AF F) σ.toLinearMap := by
    funext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [sigR]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  rw [this]
  exact IsModuleTopology.continuous_of_linearMap _

theorem cT_apply {A : Type} [CommRing A] (s : A →+* A) {m p : Type} (M : Matrix m p A) (i : p) (k : m) :
    cT s M i k = s (M k i) := rfl

theorem cover (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : IsCMExt F E σ) (j : ℕ) : ∃ (Ω : Set (AF F ⊗[F] E)) (B : ℝ), IsCompact Ω ∧ ∀ μ : Fin j → ℕ, ∃ Y : Finset (Matrix (Fin j) (Fin j) (AF F ⊗[F] E)), (Y.card : ℝ) ≤ B * ∏ i, bse F ^ (j * μ i) ∧ (∀ y ∈ Y, cT (sigR (AF F) σ) y = -y) ∧ ∀ x : Matrix (Fin j) (Fin j) (AF F ⊗[F] E), cT (sigR (AF F) σ) x = -x → ∃ x₀ : Matrix (Fin j) (Fin j) E, cT (σ : E →+* E) x₀ = -x₀ ∧ ∃ y ∈ Y, ∃ ω : Matrix (Fin j) (Fin j) (AF F ⊗[F] E), cT (sigR (AF F) σ) ω = -ω ∧ (∀ i k, ω i k ∈ Ω) ∧ x = adMat F x₀ + (y + (tor F E fun i => (μ i : ℤ)).1 * ω * cT (sigR (AF F) σ) (tor F E fun i => (μ i : ℤ)).1) := by
  classical
  haveI := hσ.1
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  obtain ⟨Ω₀, C₀, hΩ₀, hcov⟩ := GlobalTheory.T.exists_adele_cover_mod_field_shrunk_compact F
  obtain ⟨Ω, C, hΩ, h⟩ := GlobalTheory.T.skewHermitian_adelic_cover_of_adele_cover F E σ hσ _ _ _ hΩ₀ hcov j
  set s := sigR (AF F) σ with hs_def
  set hh : AF F ⊗[F] E := algebraMap F (AF F ⊗[F] E) 2⁻¹ with hh_def
  have h2 : hh * 2 = 1 := by
    rw [hh_def, ← map_ofNat (algebraMap F (AF F ⊗[F] E)) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]
  have hsh : s hh = hh := sigR_alg σ _
  have hss : ∀ z, s (s z) = z := sigR_sigR σ hσ
  have hsi : ∀ e, s (inclR (F := F) (AF F) e) = inclR (AF F) (σ e) := sigR_inclR σ
  let sk : Matrix (Fin j) (Fin j) (AF F ⊗[F] E) → Matrix (Fin j) (Fin j) (AF F ⊗[F] E) :=
    fun z => Matrix.of fun i k => hh * (z i k - s (z k i))
  have sk_skew : ∀ z, cT s (sk z) = -sk z := fun z => by
    ext i k
    simp only [cT_apply, sk, Matrix.of_apply, Matrix.neg_apply, map_mul, map_sub, hsh, hss]
    ring
  have hcont : Continuous fun p : (AF F ⊗[F] E) × (AF F ⊗[F] E) => hh * (p.1 - s p.2) :=
    continuous_const.mul (continuous_fst.sub ((continuous_sigR σ).comp continuous_snd))
  refine ⟨_, C, (hΩ.prod hΩ).image hcont, fun μ => ?_⟩
  obtain ⟨Y, hY, hc⟩ := h μ
  have hd : ∀ i, s ((GlobalTheory.Eis.Conv.halfE F E).1 ^ μ i) = (GlobalTheory.Eis.Conv.halfE F E).1 ^ μ i := fun i => by
    rw [map_pow, hs_def, GlobalTheory.Eis.Conv.sigR_halfE]
  have htor : (tor F E fun i => (μ i : ℤ)).1 = Matrix.diagonal fun i => (GlobalTheory.Eis.Conv.halfE F E).1 ^ μ i := by
    simp [tor, GlobalTheory.Eis.Conv.dg]
  have htor' : cT s (tor F E fun i => (μ i : ℤ)).1 = Matrix.diagonal fun i => (GlobalTheory.Eis.Conv.halfE F E).1 ^ μ i := by
    rw [htor]
    ext i k
    rw [cT_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
    by_cases hik : i = k
    · subst hik; simp [hd]
    · simp [hik, Ne.symm hik]
  refine ⟨Y.image sk, (Nat.cast_le.mpr Finset.card_image_le).trans (hY.trans (le_of_eq ?_)), ?_, fun x hx => ?_⟩
  · simp only [bse, ← pow_mul, mul_comm _ 2, show (4 : ℝ) = 2 ^ 2 by norm_num]
  · intro y hy
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 hy
    exact sk_skew z
  · obtain ⟨S₀, y, hy, ω, hω, e⟩ := hc x hx
    set c : E := algebraMap F E 2⁻¹ with hc_def
    have hσc : σ c = c := σ.commutes _
    refine ⟨Matrix.of fun i k => c * (S₀ i k - σ (S₀ k i)), ?_, sk y, Finset.mem_image_of_mem _ hy, sk ω, sk_skew ω,
      fun i k => ⟨(ω i k, ω k i), ⟨hω i k, hω k i⟩, rfl⟩, ?_⟩
    · ext i k
      simp only [cT_apply, Matrix.of_apply, Matrix.neg_apply, AlgHom.coe_toRingHom, map_mul, map_sub, hσc,
        sig_sig σ hσ]
      ring
    · rw [htor', htor]
      ext i k
      have hx1 : s (x k i) = - x i k := by
        have := congrFun (congrFun hx i) k
        rwa [cT_apply, Matrix.neg_apply] at this
      have e1 := congrFun (congrFun e i) k
      have e2 := congrArg s (congrFun (congrFun e k) i)
      simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, map_add (f := _), map_mul,
        hsi, hd] at e1 e2
      rw [hx1] at e2
      simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, adMat, Matrix.map_apply,
        Matrix.of_apply, sk, map_mul, map_sub, inclR_alg]
      rw [hc_def, inclR_alg, ← hh_def]
      linear_combination hh * e1 - hh * e2 - x i k * h2
end GlobalTheory.SkewAdCover
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal

noncomputable section

namespace GlobalTheory.ModelAdm

open Filter
open scoped Classical

theorem model_admissible_iff_evaluation : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M₁ 1 1 ∅ e → Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) →
    ∀ l : Fn F n d →ₗ[ℂ] ℂ, l ∈ (adeleClass F).adm (Fin n × Fin d) ↔ l ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d) := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP M₁ hM₁ e hE hbij l
  constructor
  · intro hl
    exact GlobalTheory.T.eigen_intertwiner_good_models F E σ B n d n d X W X W M M₁ 1 1 ∅ e hP.good hM₁ hE l hl
  · intro hl g hg
    obtain ⟨m, c, φ, hφ, hstd, rfl⟩ := GlobalTheory.MixEvAdm.sb_decomp F (Fin n × Fin d) g hg
    obtain ⟨ei, ev, -, hev, hloc⟩ := hE.loc
    have hbi : Function.Bijective ei :=
      ⟨GlobalTheory.T.weil_eigen_injective_extends F E σ B n d X W M M₁ hP.good e hbij.injOn ei ev (fun v => (hev v).1) hloc,
        GlobalTheory.T.weil_eigen_surjective_extends F E σ B n d X W M M₁ hP.good hM₁ e hbij.surjOn ei ev hev hloc⟩
    obtain ⟨S, hS⟩ := GlobalTheory.T.schwartz_bijection_right_inverse _ _ ei hbi
    have hpre : ∀ j v, ∃ ψ ∈ SB (Fin n × Fin d → Fv F v), ev v ψ = φ j v ∧ (φ j v = M₁.vac v → ψ = M.vac v) := by
      intro j v
      by_cases h : φ j v = M₁.vac v
      · exact ⟨M.vac v, (hP.good.vac v).1, (hev v).1.trans h.symm, fun _ => rfl⟩
      · have h2 : φ j v ∈ (SB (Fin n × Fin d → Fv F v)).map (ev v) := (hev v).2.symm ▸ hφ j v
        obtain ⟨ψ, hψ, hψe⟩ := Submodule.mem_map.1 h2
        exact ⟨ψ, hψ, hψe, fun h' => (h h').elim⟩
    choose ψ hψSB hψev hψvac using hpre
    have hψfam : ∀ j, ∀ᶠ v in cofinite, ψ j v = M.vac v := fun j =>
      ((hstd j).and hM₁.std).mono fun v hv => hψvac j v (hv.1.trans hv.2.symm)
    have hψstd : ∀ j, ∀ᶠ v in cofinite,
        ψ j v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := fun j =>
      ((hψfam j).and hP.good.std).mono fun v hv => hv.1.trans hv.2
    have hG : ∀ j, (fun y : Fin n × Fin d → Af F => ∏ᶠ v, ψ j v fun i => evalV F v (y i)) ∈
        SB (Fin n × Fin d → Af F) := fun j =>
      ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV _ (hψSB j) (hψstd j),
        GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod _ (hψSB j) (hψstd j)⟩
    choose Tj hTj using fun j => hl _ (hG j)
    refine ⟨∑ j, c j • (Tj j).comp S, fun f => ?_⟩
    have hsplit : pureA F (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ)
        (∑ j, c j • fun y => ∏ᶠ v, φ j v fun i => evalV F v (y i)) =
        ∑ j, c j • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (φ j) := by
      funext x
      simp only [pureA, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_left_comm]
      rfl
    have hφe : ∀ j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (φ j) =
        e (pureA F ((S f : SInf F _) : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ)
          (fun y => ∏ᶠ v, ψ j v fun i => evalV F v (y i))) := by
      intro j
      have h1 := hloc (S f) (ψ j) (hψSB j) (hψfam j)
      rw [hS] at h1
      have h2 : (fun v => ev v (ψ j v)) = φ j := funext fun v => hψev j v
      rw [h2] at h1
      exact h1.symm

    rw [hsplit, map_sum, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hφe j]
    simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.coe_comp', Function.comp_apply]
    rw [← hTj j (S f)]
    rfl

end GlobalTheory.ModelAdm
end
end

section

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
noncomputable section
namespace GlobalTheory.TorusDilate

variable {F : Type} [Field F] [NumberField F]

theorem infScale_inv_mul (t : ℝ) (ht : t ≠ 0) (a : AF F) :
    GlobalTheory.TorusTheta.infScale F t⁻¹ * (GlobalTheory.TorusTheta.infScale F t * a) = a := by
  have h : GlobalTheory.TorusTheta.infScale F t⁻¹ * GlobalTheory.TorusTheta.infScale F t = 1 := by
    unfold GlobalTheory.TorusTheta.infScale
    refine Prod.ext ?_ ?_
    · show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ t⁻¹) *
        (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ t) = 1
      rw [← map_mul, ← map_mul, inv_mul_cancel₀ ht, map_one, map_one]
    · show (1 : FiniteAdeleRing (𝓞 F) F) * 1 = 1
      exact one_mul 1
  rw [← mul_assoc, h, one_mul]

theorem proj_zero_mem_adm' (κ : Type) [Fintype κ] :
    (LinearMap.proj (R := ℂ) (φ := fun _ : (κ → AF F) => ℂ) 0) ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g 0 • (BoundedContinuousFunction.evalCLM ℂ 0).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ), fun f => ?_⟩
  simp only [LinearMap.proj_apply, pureA, ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_comp',
    Function.comp_apply, Pi.smul_apply, SchwartzMap.toBoundedContinuousFunctionCLM_apply,
    BoundedContinuousFunction.evalCLM_apply, smul_eq_mul]
  have h1 : (fun i : κ => InfiniteAdeleRing.ringEquiv_mixedSpace F ((0 : κ → AdeleRing (𝓞 F) F) i).1) = 0 := by
    funext i; exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  have h2 : (fun i : κ => ((0 : κ → AdeleRing (𝓞 F) F) i).2) = 0 := by
    funext i; rfl
  rw [h1, h2, mul_comm]

theorem memLp_of_mem_schA {κ : Type} [Fintype κ] (μ : @Measure (κ → AF F) (borel _))
    (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    (letI : MeasurableSpace (κ → AF F) := borel _; MemLp Φ 2 μ) := by
  letI mA : MeasurableSpace (κ → AF F) := borel _
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    exact GlobalTheory.ThetaSobolevBase.memLp_pureA μ hμ f hg
  | zero => exact MemLp.zero
  | add _ _ _ _ h1 h2 => exact h1.add h2
  | smul c _ _ h => exact h.const_smul c

theorem lintegral_sq_ne_zero {κ : Type} [Fintype κ] (μ : @Measure (κ → AF F) (borel _))
    (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) {Φ : (κ → AF F) → ℂ} (hc : Continuous Φ) (h0 : Φ 0 ≠ 0) :
    ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ ≠ 0 := by
  letI mA : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  intro h
  have hm : AEMeasurable (fun x => ‖Φ x‖ₑ ^ 2) μ := (hc.measurable.enorm.pow_const 2).aemeasurable
  rw [lintegral_eq_zero_iff' hm] at h
  have h' : Φ =ᵐ[μ] 0 := h.mono fun x hx => by
    simpa using hx
  have := (hc.ae_eq_iff_eq μ continuous_const).1 h'
  exact h0 (congrFun this 0)

end GlobalTheory.TorusDilate

namespace GlobalTheory.TorusDilate

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (g : UA σ X.J) (u : Fin n × Fin d → ℝ), (∀ j, 0 < u j) →
    (∀ z : Matrix (Fin n) (Fin d) (AE F E), M.co.e (mat g * z) =
      (fun j => GlobalTheory.TorusTheta.infScale F ((u j)⁻¹) * (M.co.e z).1 j,
       fun j => GlobalTheory.TorusTheta.infScale F (u j) * (M.co.e z).2 j)) →
    ∃ κ : ℂ, ‖κ‖ ^ 2 = ∏ j, u j ^ Module.finrank ℚ F ∧
      ∀ Φ ∈ schA F (Fin n × Fin d), ∀ x, om (g, 1) Φ x = κ * Φ (fun j => GlobalTheory.TorusTheta.infScale F (u j) * x j) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP g u hu hg
  have hψ : IsStd B.ψ := hP.base.std
  have hS := IsUWeilPair.isUSplitting hP.weil
  have hact : ∀ w, actAB (cA σ) (g, (1 : UA σ W.J)) w = mat g * w := fun w => by
    simp [actAB, mat]
  have himpl : ∀ w, ∀ φ ∈ schA F (Fin n × Fin d),
      om (g, 1) (schr B.ψ (M.co.e w) φ) = schr B.ψ (M.co.e (mat g * w)) (om (g, 1) φ) := fun w φ hφ => by
    have := hS.impl (g, 1) w φ hφ
    rw [hact] at this
    exact this
  set l₁ : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ :=
    (LinearMap.proj (R := ℂ) (φ := fun _ : (Fin n × Fin d → AF F) => ℂ) 0) ∘ₗ om (g, 1) with hl₁
  have hadm : l₁ ∈ (adeleClass F).adm (Fin n × Fin d) := hS.adm (g, 1) _ (proj_zero_mem_adm' _)
  obtain ⟨c, hc⟩ := GlobalTheory.T.character_invariant_adelic_form_eq_mul_eval_zero F B.ψ hψ (Fin n × Fin d) l₁ hadm (fun y φ hφ => by
    have e : (fun x => B.ψ (x ⬝ᵥ y) * φ x) = schr B.ψ (M.co.e (M.co.e.symm (0, y))) φ := by
      funext x; simp [schr]
    rw [e]
    simp only [hl₁, LinearMap.comp_apply, LinearMap.proj_apply]
    rw [himpl _ φ hφ, hg]
    (simp [schr, dotProduct]) <;> rfl)
  have hval : ∀ Φ ∈ schA F (Fin n × Fin d), ∀ x,
      om (g, 1) Φ x = c * Φ (fun j => GlobalTheory.TorusTheta.infScale F (u j) * x j) := fun Φ hΦ x => by
    set p : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F) :=
      (fun j => GlobalTheory.TorusTheta.infScale F (u j) * x j, 0) with hp
    have hmem := GlobalTheory.HeisSchA.schr_mem_schA B.ψ hψ p Φ hΦ
    have h1 := hc _ hmem
    simp only [hl₁, LinearMap.comp_apply, LinearMap.proj_apply] at h1
    have e : schr B.ψ p Φ = schr B.ψ (M.co.e (M.co.e.symm p)) Φ := by rw [LinearEquiv.apply_symm_apply]
    rw [e, himpl _ Φ hΦ, hg, LinearEquiv.apply_symm_apply] at h1
    have hx : (fun j => GlobalTheory.TorusTheta.infScale F (u j)⁻¹ * (GlobalTheory.TorusTheta.infScale F (u j) * x j)) = x :=
      funext fun j => infScale_inv_mul (u j) (hu j).ne' (x j)
    simp only [hp, hx] at h1
    simpa [schr, dotProduct] using h1
  refine ⟨c, ?_, hval⟩

  letI mA : MeasurableSpace (Fin n × Fin d → AF F) := borel _
  haveI : BorelSpace (Fin n × Fin d → AF F) := ⟨rfl⟩
  let μ : Measure (Fin n × Fin d → AF F) := Measure.addHaar
  have hμ : μ.IsAddHaarMeasure := inferInstance
  obtain ⟨Φ, hΦ, h0⟩ := GlobalTheory.SchANonzero.exists_mem_schA_ne_zero F (Fin n × Fin d)
  have hI0 : ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ ≠ 0 :=
    lintegral_sq_ne_zero μ hμ (GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA (F := F) hΦ) h0
  have hIt : ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ ≠ ⊤ := by
    have h2 := (memLp_of_mem_schA μ hμ hΦ).eLpNorm_lt_top
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)] at h2
    · simpa using h2.ne
    · exact (memLp_of_mem_schA μ hμ hΦ).aestronglyMeasurable
  have hU := hS.unit μ hμ (g, 1) Φ hΦ
  have hsc := GlobalTheory.T.lintegral_infinite_scaling F (Fin n × Fin d) u hu μ hμ (fun y => ‖Φ y‖ₑ ^ 2)
  simp only [hval Φ hΦ, enorm_mul, mul_pow] at hU
  rw [lintegral_const_mul' _ _ (by simp), hsc] at hU
  set P := ENNReal.ofReal (∏ j, u j ^ Module.finrank ℚ F) with hPdef
  have hPpos : 0 < ∏ j, u j ^ Module.finrank ℚ F := Finset.prod_pos fun j _ => pow_pos (hu j) _
  have hP0 : P ≠ 0 := by rw [hPdef]; exact (ENNReal.ofReal_pos.2 hPpos).ne'
  have hPt : P ≠ ⊤ := ENNReal.ofReal_ne_top
  have hk : ‖c‖ₑ ^ 2 * P⁻¹ = 1 := by
    rw [← mul_assoc] at hU
    exact (ENNReal.mul_eq_right hI0 hIt).1 hU
  have hk' : ‖c‖ₑ ^ 2 = P := by
    have := congrArg (· * P) hk
    simpa [mul_assoc, ENNReal.inv_mul_cancel hP0 hPt] using this
  have hk'' : ENNReal.ofReal (‖c‖ ^ 2) = ENNReal.ofReal (∏ j, u j ^ Module.finrank ℚ F) := by
    rw [← hPdef, ← hk', ← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
  exact (ENNReal.ofReal_eq_ofReal_iff (by positivity) hPpos.le).1 hk''

end GlobalTheory.TorusDilate
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal

noncomputable section

namespace GlobalTheory.ModelAdmUnconditional

open Filter
open scoped Classical

theorem model_admissible_iff_evaluation : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M₁ 1 1 ∅ e → Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) →
    ∀ l : Fn F n d →ₗ[ℂ] ℂ, l ∈ (adeleClass F).adm (Fin n × Fin d) ↔ l ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP M₁ hM₁ e hE hbij l
  constructor
  · intro hl
    exact GlobalTheory.T.eigen_intertwiner_good_models F E σ B n d n d X W X W M M₁ 1 1 ∅ e hP.good hM₁ hE l hl
  · intro hl g hg
    obtain ⟨m, c, φ, hφ, hstd, rfl⟩ := GlobalTheory.MixEvAdm.sb_decomp F (Fin n × Fin d) g hg
    obtain ⟨ei, ev, -, hev, hloc⟩ := hE.loc
    have hbi : Function.Bijective ei :=
      ⟨GlobalTheory.T.weil_eigen_injective_extends F E σ B n d X W M M₁ hP.good e hbij.injOn ei ev (fun v => (hev v).1) hloc,
        GlobalTheory.T.weil_eigen_surjective_extends F E σ B n d X W M M₁ hP.good hM₁ e hbij.surjOn ei ev hev hloc⟩
    obtain ⟨S, hS⟩ := GlobalTheory.T.schwartz_bijection_right_inverse _ _ ei hbi
    have hpre : ∀ j v, ∃ ψ ∈ SB (Fin n × Fin d → Fv F v), ev v ψ = φ j v ∧ (φ j v = M₁.vac v → ψ = M.vac v) := by
      intro j v
      by_cases h : φ j v = M₁.vac v
      · exact ⟨M.vac v, (hP.good.vac v).1, (hev v).1.trans h.symm, fun _ => rfl⟩
      · have h2 : φ j v ∈ (SB (Fin n × Fin d → Fv F v)).map (ev v) := (hev v).2.symm ▸ hφ j v
        obtain ⟨ψ, hψ, hψe⟩ := Submodule.mem_map.1 h2
        exact ⟨ψ, hψ, hψe, fun h' => (h h').elim⟩
    choose ψ hψSB hψev hψvac using hpre
    have hψfam : ∀ j, ∀ᶠ v in cofinite, ψ j v = M.vac v := fun j =>
      ((hstd j).and hM₁.std).mono fun v hv => hψvac j v (hv.1.trans hv.2.symm)
    have hψstd : ∀ j, ∀ᶠ v in cofinite,
        ψ j v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := fun j =>
      ((hψfam j).and hP.good.std).mono fun v hv => hv.1.trans hv.2
    have hG : ∀ j, (fun y : Fin n × Fin d → Af F => ∏ᶠ v, ψ j v fun i => evalV F v (y i)) ∈
        SB (Fin n × Fin d → Af F) := fun j =>
      ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV _ (hψSB j) (hψstd j),
        GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod _ (hψSB j) (hψstd j)⟩
    choose Tj hTj using fun j => hl _ (hG j)
    refine ⟨∑ j, c j • (Tj j).comp S, fun f => ?_⟩
    have hsplit : pureA F (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ)
        (∑ j, c j • fun y => ∏ᶠ v, φ j v fun i => evalV F v (y i)) =
        ∑ j, c j • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (φ j) := by
      funext x
      simp only [pureA, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_left_comm]
      rfl
    have hφe : ∀ j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (φ j) =
        e (pureA F ((S f : SInf F _) : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ)
          (fun y => ∏ᶠ v, ψ j v fun i => evalV F v (y i))) := by
      intro j
      have h1 := hloc (S f) (ψ j) (hψSB j) (hψfam j)
      rw [hS] at h1
      have h2 : (fun v => ev v (ψ j v)) = φ j := funext fun v => hψev j v
      rw [h2] at h1
      exact h1.symm

    rw [hsplit, map_sum, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hφe j]
    simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.coe_comp', Function.comp_apply]
    rw [← hTj j (S f)]
    rfl

end GlobalTheory.ModelAdmUnconditional
end
end

section

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.skewHermitian_selfDual_lattice_hyperbolic_plane_splitting : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (n n₁ : ℕ), n = n₁ + 2 → 1 ≤ n₁ → ∀ (Y : Spc F E n) (r s : ℕ), 1 ≤ r → 1 ≤ s →
    Y.IsSkew σ B r s → ∀ i₀ i₁ : ℕ, i₀ < i₁ → i₁ < n → ∃ (Y' : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁),
      (GlobalTheory.ThK.reS Y Y').IsSkew σ B r s ∧ Y₁.IsSkew σ B (r - 1) (s - 1) ∧ H.IsAdapted σ B (GlobalTheory.ThK.reS Y Y') Y₁ i₀ i₁ := by
  first | exact @GlobalTheory.PlaneSkew.plane_skew | exact GlobalTheory.PlaneSkew.plane_skew | (intros; apply GlobalTheory.PlaneSkew.plane_skew <;> assumption)
end
