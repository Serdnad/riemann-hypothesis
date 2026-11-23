module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle474
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf
public import Development.WeilBound.ThetaLifts.SmallCones.Bundle003
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalMassFormula
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle472
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle475
import Std.Tactic.BVDecide.Normalize.Prop
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.MapsExist

@[expose] public section

section

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate

namespace GlobalTheory.CompanionTheory.RealCountG.LefDual

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

variable {n : ℕ}

theorem trace_dualT (E : KMod n) (S : E.V →L[ℂ] E.V) :
    LinearMap.trace ℂ (E.V →L[ℂ] ℂ) (dualT E S : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) =
      LinearMap.trace ℂ E.V (S : E.V →ₗ[ℂ] E.V) := by
  let e : Module.Dual ℂ E.V ≃ₗ[ℂ] (E.V →L[ℂ] ℂ) := LinearMap.toContinuousLinearMap
  have h : (dualT E S : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) =
      e.conj (Module.Dual.transpose (R := ℂ) (S : E.V →ₗ[ℂ] E.V)) := by
    ext φ x
    simp [e, dualT, LinearEquiv.conj_apply, Module.Dual.transpose_apply]
  rw [h, LinearMap.trace_conj', LinearMap.trace_transpose']

theorem weylChar_conj_arg (lam : Fin n → ℤ) (u : Fin n → ℂ) :
    weylChar lam (fun a => conj (u a)) = conj (weylChar lam u) := by
  unfold weylChar
  rw [map_div₀, RingHom.map_det, RingHom.map_det]
  congr 2 <;> ext i j <;> simp [map_zpow₀]

theorem conj_eq_inv (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ) (hk : k.1 = diagonal z) (a : Fin n) :
    z a ≠ 0 ∧ conj (z a) = (z a)⁻¹ := by
  have h := Matrix.mem_unitaryGroup_iff'.1 k.2
  rw [hk, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal] at h
  have ha := congrFun (congrFun h a) a
  rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, Pi.star_apply] at ha
  have h1 : conj (z a) * z a = 1 := ha
  have h0 : z a ≠ 0 := fun h0 => by rw [h0, mul_zero] at h1; exact zero_ne_one h1
  exact ⟨h0, eq_inv_of_mul_eq_one_left h1⟩

theorem trace_dualT_inv (lam : Fin n → ℤ) (E : KMod n) (T : E.V →L[ℂ] E.V) (hT : IsLefK lam E T)
    (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ) (hk : k.1 = diagonal z)
    (hinj : Function.Injective (fun a => z a ^ 2)) :
    LinearMap.trace ℂ (E.V →L[ℂ] ℂ) (dualT E (E.ρ k⁻¹ * T) : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) =
      (∏ a, ∏ b, (1 + z a / z b)) * weylChar lam (fun a => z a ^ 2) := by
  have hz := conj_eq_inv k z hk
  have hk' : (k⁻¹ : Matrix.unitaryGroup (Fin n) ℂ).1 = diagonal (fun a => (z a)⁻¹) := by
    rw [← Unitary.star_eq_inv, Unitary.coe_star, hk, Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    exact (hz a).2
  have hinj' : Function.Injective (fun a => (z a)⁻¹ ^ 2) := fun a b h => by
    apply hinj
    simpa [inv_pow] using h
  obtain ⟨-, -, h3⟩ := hT
  obtain ⟨-, h2⟩ := h3 k⁻¹ (fun a => (z a)⁻¹) hk' hinj'
  beta_reduce at h2
  rw [trace_dualT, h2]
  have hw : (fun a => (z a)⁻¹ ^ 2) = fun a => conj (z a ^ 2) := by
    funext a
    rw [map_pow, (hz a).2]
  congr 1
  · simp_rw [inv_div_inv]
    exact Finset.prod_comm
  · rw [hw, weylChar_conj_arg, Complex.conj_conj]

end GlobalTheory.CompanionTheory.RealCountG.LefDual
end
end

section

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.gelfand_invariant_commute_generator : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E : Fin n → Fin n → Module.End ℂ V), Formalism.REAL.GlRel E → ∀ (m : ℕ) (a b : Fin n), gelA E m * E a b = E a b * gelA E m := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.gelA_central | exact GlobalTheory.CompanionTheory.ModelS.gelA_central | (intros; apply GlobalTheory.CompanionTheory.ModelS.gelA_central <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.EisDict

open scoped TensorProduct NNReal Matrix NumberField.AdeleRing
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open PositivityTheory.RgEis

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


variable (F E) in
def sec : (Af F ⊗[F] E) →+ AE F E :=
  (TensorProduct.map (LinearMap.inr F (Ainf F) (Af F)) (LinearMap.id : E →ₗ[F] E)).toAddMonoidHom

theorem sec_tmul (a : Af F) (x : E) : sec F E (a ⊗ₜ[F] x) = ((0, a) : AF F) ⊗ₜ[F] x := rfl

theorem sec_finPart (z : AE F E) : sec F E (HeckeCharacterZeroLocus.ThmBIn.finPart F E z) = finOne F • z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, smul_add]
  | tmul a x =>
    change sec F E (HeckeCharacterZeroLocus.ThmBIn.sndA F a ⊗ₜ[F] x) = _
    rw [sec_tmul, TensorProduct.smul_tmul']
    congr 1
    refine Prod.ext ?_ ?_
    · change (0 : Ainf F) = 0 * a.1
      simp
    · change a.2 = 1 * a.2
      simp

theorem finPart_finOne_smul (z : AE F E) :
    HeckeCharacterZeroLocus.ThmBIn.finPart F E (finOne F • z) = HeckeCharacterZeroLocus.ThmBIn.finPart F E z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy]
  | tmul a x =>
    rw [TensorProduct.smul_tmul']
    change HeckeCharacterZeroLocus.ThmBIn.sndA F (finOne F • a) ⊗ₜ[F] x = HeckeCharacterZeroLocus.ThmBIn.sndA F a ⊗ₜ[F] x
    congr 1
    change 1 * a.2 = a.2
    simp

theorem sec_mem {y : Af F ⊗[F] E} (hy : y ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E) : sec F E y ∈ intHat F E := by
  induction hy using AddSubgroup.closure_induction with
  | mem y h =>
    obtain ⟨a, ha, x, rfl⟩ := h
    refine AddSubgroup.subset_closure ⟨(0, a), ?_, fun v => ha v, x, ?_⟩
    · exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
    · rw [sec_tmul]
      change _ = pairA F 0 a • ((1 : AF F) ⊗ₜ[F] (x : E))
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rfl
  | zero => simpa using (intHat F E).zero_mem
  | add x y _ _ hx hy => simpa using (intHat F E).add_mem hx hy
  | neg x _ hx => simpa using (intHat F E).neg_mem hx

theorem finPart_mem {z : AE F E} (hz : z ∈ intHat F E) : HeckeCharacterZeroLocus.ThmBIn.finPart F E z ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E := by
  induction hz using AddSubgroup.closure_induction with
  | mem z h =>
    obtain ⟨a, -, ha, o, rfl⟩ := h
    refine AddSubgroup.subset_closure ⟨HeckeCharacterZeroLocus.ThmBIn.sndA F a, fun v => ha v, o, ?_⟩
    change HeckeCharacterZeroLocus.ThmBIn.finPart F E (a • ((1 : AF F) ⊗ₜ[F] (o : E))) = _
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rfl
  | zero => simpa using (HeckeCharacterZeroLocus.ThmBIn.intAE F E).zero_mem
  | add x y _ _ hx hy => simpa using (HeckeCharacterZeroLocus.ThmBIn.intAE F E).add_mem hx hy
  | neg x _ hx => simpa using (HeckeCharacterZeroLocus.ThmBIn.intAE F E).neg_mem hx

theorem mem_intAd_iff (z : AE F E) :
    eqv F E z ∈ intAd E ↔ HeckeCharacterZeroLocus.ThmBIn.finPart F E z ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E := by
  rw [GroundTheory.BlockD.ThmBHecke.mem_intAE_iff, ← GroundTheory.BlockD.ThmBHecke.adeleEquiv_snd,
    GroundTheory.Global.mem_integralFiniteAdeles]
  simp only [intAd, Subring.mem_iInf, Subring.mem_comap]
  rfl

theorem dict : Dict := by
  intro F E _ _ _ _ _
  refine ⟨GroundTheory.BlockD.ThmBHecke.continuous_adeleEquiv, GroundTheory.BlockD.ThmBHecke.continuous_adeleEquiv_symm,
    GroundTheory.BlockD.ThmBHecke.adeleEquiv_incA, fun z => ?_, fun x => ?_⟩
  · rw [mem_intAd_iff]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [← sec_finPart]
      exact sec_mem h
    · rw [← finPart_finOne_smul]
      exact finPart_mem h
  · exact (PositivityTheory.ThKCT.Tate.absE_eq x).symm

end GlobalTheory.CompanionTheory.EisDict
end
end

section

open Filter Topology Metric
open PositivityTheory.Rg.Rsw

namespace GlobalTheory.CompanionTheory.PoleBound

theorem factor_of_real_bound (s₀ ε : ℝ) (hε : 0 < ε) :
    ∀ (r : ℕ) (u : ℂ → ℂ), ContinuousOn u (closedBall (s₀ : ℂ) ε) →
      DifferentiableOn ℂ u (ball (s₀ : ℂ) ε) →
      (∃ B : ℝ, ∀ᶠ σ : ℝ in 𝓝[>] s₀, ‖u (σ : ℂ) / ((σ : ℂ) - s₀) ^ r‖ ≤ B) →
      ∃ w : ℂ → ℂ, ContinuousOn w (closedBall (s₀ : ℂ) ε) ∧
        DifferentiableOn ℂ w (ball (s₀ : ℂ) ε) ∧
        ∀ z ∈ closedBall (s₀ : ℂ) ε, z ≠ s₀ → u z = (z - s₀) ^ r * w z := by
  intro r
  induction r with
  | zero =>
    intro u hc hd _
    exact ⟨u, hc, hd, fun z _ _ => by simp⟩
  | succ r ih =>
    intro u hc hd hb
    obtain ⟨B, hB⟩ := hb
    have hdiff : DifferentiableAt ℂ u (s₀ : ℂ) := hd.differentiableAt (ball_mem_nhds _ hε)
    have hu0 : u (s₀ : ℂ) = 0 := by
      have hlim₁ : Tendsto (fun σ : ℝ => u (σ : ℂ)) (𝓝[>] s₀) (𝓝 (u (s₀ : ℂ))) :=
        ((hdiff.continuousAt.tendsto).comp (Complex.continuous_ofReal.tendsto s₀)).mono_left
          nhdsWithin_le_nhds
      have hsmall : Tendsto (fun σ : ℝ => B * ‖(σ : ℂ) - s₀‖ ^ (r + 1)) (𝓝[>] s₀) (𝓝 0) := by
        have hcont : Continuous (fun σ : ℝ => B * ‖(σ : ℂ) - s₀‖ ^ (r + 1)) := by fun_prop
        simpa using (hcont.tendsto s₀).mono_left nhdsWithin_le_nhds
      have hlim₂ : Tendsto (fun σ : ℝ => u (σ : ℂ)) (𝓝[>] s₀) (𝓝 0) := by
        refine squeeze_zero_norm' ?_ hsmall
        filter_upwards [hB, self_mem_nhdsWithin] with σ hσB hσ
        have hne : ((σ : ℂ) - s₀) ^ (r + 1) ≠ 0 :=
          pow_ne_zero _ (sub_ne_zero.mpr (Complex.ofReal_injective.ne (show s₀ < σ from hσ).ne'))
        calc ‖u (σ : ℂ)‖ = ‖u (σ : ℂ) / ((σ : ℂ) - s₀) ^ (r + 1)‖ * ‖(σ : ℂ) - s₀‖ ^ (r + 1) := by
              rw [← norm_pow, ← norm_mul, div_mul_cancel₀ _ hne]
          _ ≤ B * ‖(σ : ℂ) - s₀‖ ^ (r + 1) :=
              mul_le_mul_of_nonneg_right hσB (pow_nonneg (norm_nonneg _) _)
      exact tendsto_nhds_unique hlim₁ hlim₂
    have huv : ∀ z, u z = (z - s₀) * dslope u (s₀ : ℂ) z := by
      intro z
      have h := sub_smul_dslope u (s₀ : ℂ) z
      rw [hu0, sub_zero, smul_eq_mul] at h
      exact h.symm
    have hvc : ContinuousOn (dslope u (s₀ : ℂ)) (closedBall (s₀ : ℂ) ε) := by
      intro z hz
      by_cases hzs : z = s₀
      · subst hzs
        exact (continuousAt_dslope_same.mpr hdiff).continuousWithinAt
      · exact (continuousWithinAt_dslope_of_ne hzs).mpr (hc z hz)
    have hvd : DifferentiableOn ℂ (dslope u (s₀ : ℂ)) (ball (s₀ : ℂ) ε) :=
      (Complex.differentiableOn_dslope (ball_mem_nhds _ hε)).mpr hd
    have hvb : ∃ B : ℝ, ∀ᶠ σ : ℝ in 𝓝[>] s₀,
        ‖dslope u (s₀ : ℂ) (σ : ℂ) / ((σ : ℂ) - s₀) ^ r‖ ≤ B := by
      refine ⟨B, ?_⟩
      filter_upwards [hB, self_mem_nhdsWithin] with σ hσB hσ
      have hne : (σ : ℂ) - s₀ ≠ 0 :=
        sub_ne_zero.mpr (Complex.ofReal_injective.ne (show s₀ < σ from hσ).ne')
      rwa [huv (σ : ℂ), pow_succ, mul_comm ((σ : ℂ) - s₀) (dslope u (s₀ : ℂ) (σ : ℂ)),
        mul_div_mul_right _ _ hne] at hσB
    obtain ⟨w, hwc, hwd, hw⟩ := ih (dslope u (s₀ : ℂ)) hvc hvd hvb
    refine ⟨w, hwc, hwd, fun z hz hzs => ?_⟩
    rw [huv z, hw z hz hzs, pow_succ]
    ring

theorem extend_of_real_bound (h : ℂ → ℂ) (d : Polynomial ℂ) (s₀ ε : ℝ) (hε : 0 < ε) (hd0 : d ≠ 0)
    (hh : DifferentiableOn ℂ h (closedBall (s₀ : ℂ) ε))
    (hne : ∀ z ∈ closedBall (s₀ : ℂ) ε, z ≠ s₀ → d.eval z ≠ 0) (n : ℕ)
    (hb : ∃ B : ℝ, ∀ᶠ σ : ℝ in 𝓝[>] s₀,
      ‖((σ : ℂ) - s₀) ^ n * (h (σ : ℂ) / d.eval (σ : ℂ))‖ ≤ B) :
    ∃ w : ℂ → ℂ, ContinuousOn w (closedBall (s₀ : ℂ) ε) ∧
      DifferentiableOn ℂ w (ball (s₀ : ℂ) ε) ∧
      ∀ z ∈ closedBall (s₀ : ℂ) ε, z ≠ s₀ → (z - s₀) ^ n * (h z / d.eval z) = w z := by
  obtain ⟨q, hdq, hndvd⟩ :=
    Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd d hd0 (s₀ : ℂ)
  set m := Polynomial.rootMultiplicity (s₀ : ℂ) d
  have hdeval : ∀ z, d.eval z = (z - s₀) ^ m * q.eval z := by
    intro z
    conv_lhs => rw [hdq]
    simp
  have hq : ∀ z ∈ closedBall (s₀ : ℂ) ε, q.eval z ≠ 0 := by
    intro z hz
    by_cases hzs : z = s₀
    · subst hzs
      intro h0
      exact hndvd (Polynomial.dvd_iff_isRoot.mpr h0)
    · intro h0
      exact hne z hz hzs (by rw [hdeval, h0, mul_zero])
  have hkey : ∀ z, (z - s₀) ^ n * (h z / d.eval z) =
      ((z - s₀) ^ n * h z / q.eval z) / (z - s₀) ^ m := by
    intro z
    rw [hdeval]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  have hud : DifferentiableOn ℂ (fun z => (z - s₀) ^ n * h z / q.eval z)
      (closedBall (s₀ : ℂ) ε) := by
    have hnum : DifferentiableOn ℂ (fun z => (z - s₀) ^ n * h z) (closedBall (s₀ : ℂ) ε) := by
      fun_prop
    exact hnum.div q.differentiable.differentiableOn hq
  obtain ⟨B, hB⟩ := hb
  have hub : ∃ B : ℝ, ∀ᶠ σ : ℝ in 𝓝[>] s₀,
      ‖((σ : ℂ) - s₀) ^ n * h (σ : ℂ) / q.eval (σ : ℂ) / ((σ : ℂ) - s₀) ^ m‖ ≤ B :=
    ⟨B, hB.mono fun σ hσ => by rwa [hkey] at hσ⟩
  obtain ⟨w, hwc, hwd, hw⟩ := GlobalTheory.CompanionTheory.PoleBound.factor_of_real_bound s₀ ε hε m
    (fun z => (z - s₀) ^ n * h z / q.eval z) hud.continuousOn
    (hud.mono ball_subset_closedBall) hub
  refine ⟨w, hwc, hwd, fun z hz hzs => ?_⟩
  rw [hkey z, hw z hz hzs, mul_div_cancel_left₀ _ (pow_ne_zero _ (sub_ne_zero.mpr hzs))]

theorem circle_zero (c : ℂ) (ε : ℝ) (hε : 0 < ε) (g : ℂ → ℂ) (hc : ContinuousOn g (closedBall c ε))
    (hd : DifferentiableOn ℂ g (ball c ε)) : (∮ z in C(c, ε), g z) = 0 :=
  Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hε.le Set.countable_empty hc
    fun _ hz => hd.differentiableAt (isOpen_ball.mem_nhds hz.1)

theorem sphere_facts {c z : ℂ} {ε : ℝ} (hε : 0 < ε) (hz : z ∈ sphere c ε) :
    z ∈ closedBall c ε ∧ z ≠ c := by
  refine ⟨sphere_subset_closedBall hz, ?_⟩
  rintro rfl
  rw [mem_sphere, dist_self] at hz
  exact hε.ne hz

theorem moment_zero (f w : ℂ → ℂ) (s₀ : ℂ) (ε : ℝ) (hε : 0 < ε) (n j : ℕ)
    (hwc : ContinuousOn w (closedBall s₀ ε)) (hwd : DifferentiableOn ℂ w (ball s₀ ε))
    (hw : ∀ z ∈ closedBall s₀ ε, z ≠ s₀ → (z - s₀) ^ n * f z = w z) :
    (∮ z in C(s₀, ε), (z - s₀) ^ (j + n) * f z) = 0 := by
  have hcongr : (∮ z in C(s₀, ε), (z - s₀) ^ (j + n) * f z) =
      ∮ z in C(s₀, ε), (z - s₀) ^ j * w z := by
    refine circleIntegral.integral_congr hε.le fun z hz => ?_
    obtain ⟨hzc, hzs⟩ := GlobalTheory.CompanionTheory.PoleBound.sphere_facts hε hz
    show (z - s₀) ^ (j + n) * f z = (z - s₀) ^ j * w z
    rw [pow_add, mul_assoc, hw z hzc hzs]
  rw [hcongr]
  refine GlobalTheory.CompanionTheory.PoleBound.circle_zero s₀ ε hε _ ?_ ?_
  · fun_prop
  · fun_prop

theorem poleReal : PoleReal := by
  intro h d s₀ ε hε hd0 hh _ hne
  refine ⟨fun hb => ?_, fun hb => ?_⟩
  · have hb' : ∃ B : ℝ, ∀ᶠ σ : ℝ in 𝓝[>] s₀,
        ‖((σ : ℂ) - s₀) ^ 1 * (h (σ : ℂ) / d.eval (σ : ℂ))‖ ≤ B := by
      obtain ⟨B, hB⟩ := hb
      exact ⟨B, hB.mono fun σ hσ => by rwa [pow_one, ← Complex.ofReal_sub]⟩
    obtain ⟨w, hwc, hwd, hw⟩ := GlobalTheory.CompanionTheory.PoleBound.extend_of_real_bound h d s₀ ε hε hd0 hh hne 1 hb'
    refine ⟨fun k hk => ?_, ?_⟩
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
      have hj : j + 2 - 1 = j + 1 := by omega
      rw [hj]
      exact GlobalTheory.CompanionTheory.PoleBound.moment_zero (fun z => h z / d.eval z) w (s₀ : ℂ) ε hε 1 j
        hwc hwd hw
    · have hint : (∮ z in C((s₀ : ℂ), ε), (z - s₀) ^ (1 - 1) * (h z / d.eval z)) =
          ∮ z in C((s₀ : ℂ), ε), (z - s₀)⁻¹ • w z := by
        refine circleIntegral.integral_congr hε.le fun z hz => ?_
        obtain ⟨hzc, hzs⟩ := GlobalTheory.CompanionTheory.PoleBound.sphere_facts hε hz
        show (z - s₀) ^ (1 - 1) * (h z / d.eval z) = (z - s₀)⁻¹ • w z
        rw [← hw z hzc hzs, smul_eq_mul, pow_one, ← mul_assoc,
          inv_mul_cancel₀ (sub_ne_zero.mpr hzs), one_mul, Nat.sub_self, pow_zero, one_mul]
      have hcauchy : (∮ z in C((s₀ : ℂ), ε), (z - s₀)⁻¹ • w z) =
          (2 * Real.pi * Complex.I : ℂ) • w s₀ :=
        Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
          Set.countable_empty (mem_ball_self hε) hwc
          fun x hx => hwd.differentiableAt (isOpen_ball.mem_nhds hx.1)
      have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
        mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
          Complex.I_ne_zero
      rw [hint, hcauchy, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ h2pi, one_mul]
      have hlim : Tendsto (fun σ : ℝ => w (σ : ℂ)) (𝓝[>] s₀) (𝓝 (w (s₀ : ℂ))) :=
        (((hwc.continuousAt (closedBall_mem_nhds _ hε)).tendsto).comp
          (Complex.continuous_ofReal.tendsto s₀)).mono_left nhdsWithin_le_nhds
      refine Tendsto.congr' ?_ hlim
      have hball : ∀ᶠ σ : ℝ in 𝓝[>] s₀, (σ : ℂ) ∈ closedBall (s₀ : ℂ) ε :=
        nhdsWithin_le_nhds
          ((Complex.continuous_ofReal.tendsto s₀).eventually_mem (closedBall_mem_nhds _ hε))
      filter_upwards [hball, self_mem_nhdsWithin] with σ hσb hσ
      rw [← hw (σ : ℂ) hσb (Complex.ofReal_injective.ne (show s₀ < σ from hσ).ne'), pow_one,
        Complex.ofReal_sub]
  · have hb' : ∃ B : ℝ, ∀ᶠ σ : ℝ in 𝓝[>] s₀,
        ‖((σ : ℂ) - s₀) ^ 0 * (h (σ : ℂ) / d.eval (σ : ℂ))‖ ≤ B := by
      obtain ⟨B, hB⟩ := hb
      exact ⟨B, hB.mono fun σ hσ => by rwa [pow_zero, one_mul]⟩
    obtain ⟨w, hwc, hwd, hw⟩ := GlobalTheory.CompanionTheory.PoleBound.extend_of_real_bound h d s₀ ε hε hd0 hh hne 0 hb'
    intro k _
    exact GlobalTheory.CompanionTheory.PoleBound.moment_zero (fun z => h z / d.eval z) w (s₀ : ℂ) ε hε 0
      (k - 1) hwc hwd hw

end GlobalTheory.CompanionTheory.PoleBound
end

section

open PositivityTheory.Rg.Rsw GlobalTheory.Cont

namespace GlobalTheory.CompanionTheory.Dblock

theorem rightId : RightId := by
  intro U h g c σ hUo hU hh hg hhg z hzU hzc
  obtain ⟨⟨σ₀, hσ₀⟩, htr⟩ := hU
  set M : ℝ := max (max σ₀ σ) c
  set V : Set ℂ := U ∩ {w : ℂ | c < w.re}
  have hVo : IsOpen V := hUo.inter (isOpen_lt continuous_const Complex.continuous_re)
  have hHV : {w : ℂ | M < w.re} ⊆ V := by
    intro w hw
    have hw' : M < w.re := hw
    refine ⟨hσ₀ ?_, ?_⟩
    · show σ₀ < w.re
      exact lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hw'
    · show c < w.re
      exact lt_of_le_of_lt (le_max_right _ _) hw'
  set x₀ : ℂ := ((M + 1 : ℝ) : ℂ)
  have hx₀ : M < x₀.re := by
    show M < ((M + 1 : ℝ) : ℂ).re
    rw [Complex.ofReal_re]
    linarith
  have hVconn : IsPreconnected V := by
    refine isPreconnected_of_forall x₀ fun y hy => ?_
    have hyc : c < y.re := hy.2
    set T : ℝ := |M - y.re| + 1
    have hT : 0 ≤ T := by positivity
    refine ⟨(fun s : ℝ => y + (s : ℂ)) '' Set.Icc 0 T ∪ {w : ℂ | M < w.re}, ?_, ?_, ?_, ?_⟩
    · rintro w (⟨s, ⟨hs0, _⟩, rfl⟩ | hw)
      · refine ⟨htr y hy.1 s hs0, ?_⟩
        show c < (y + (s : ℂ)).re
        rw [Complex.add_re, Complex.ofReal_re]
        linarith
      · exact hHV hw
    · exact Or.inr hx₀
    · exact Or.inl ⟨0, ⟨le_refl 0, hT⟩, by simp⟩
    · refine IsPreconnected.union (y + (T : ℂ)) ⟨T, ⟨hT, le_refl T⟩, rfl⟩ ?_ ?_ ?_
      · show M < (y + (T : ℂ)).re
        rw [Complex.add_re, Complex.ofReal_re]
        have := le_abs_self (M - y.re)
        linarith
      · exact isPreconnected_Icc.image _
          (continuous_const.add Complex.continuous_ofReal).continuousOn
      · exact (convex_halfSpace_re_gt M).isPreconnected
  have hhA : AnalyticOnNhd ℂ h V := (hh.mono Set.inter_subset_left).analyticOnNhd hVo
  have hgA : AnalyticOnNhd ℂ g V := (hg.mono Set.inter_subset_right).analyticOnNhd hVo
  have hσx : σ < x₀.re := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hx₀
  have hev : h =ᶠ[nhds x₀] g := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hσx] with w hw
    exact hhg w hw
  exact hhA.eqOn_of_preconnected_of_eventuallyEq hgA hVconn (hHV hx₀) hev ⟨hzU, hzc⟩

end GlobalTheory.CompanionTheory.Dblock
end

section

open PositivityTheory.Rg.Mass

theorem _root_.GlobalTheory.T.local_mass_formula : LocMass := by
  first | exact @GlobalTheory.CompanionTheory.SW.LocBin.locMass | exact GlobalTheory.CompanionTheory.SW.LocBin.locMass | (intros; apply GlobalTheory.CompanionTheory.SW.LocBin.locMass <;> assumption)
end
