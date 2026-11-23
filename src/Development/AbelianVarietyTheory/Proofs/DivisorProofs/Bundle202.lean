module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle050
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle009
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle051
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SpecialisationNumberFieldAndCountableValues
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle026
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle052
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle053
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Topology.Algebra.Polynomial

@[expose] public section

section

open MeasureTheory Filter Topology
open scoped ContDiff

namespace GlobalTheory.LocRep


open MeasureTheory Filter Topology in
open scoped ContDiff in
theorem _root_.GlobalTheory.LocRep.exists_eval_closure (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (ι : K → G → ℂ)
    (hloc : ∀ C, IsCompact C → ∃ M : ℝ, ∀ v, IntegrableOn (ι v) C μ ∧ ∫ x in C, ‖ι v x‖ ∂μ ≤ M * ‖v‖)
    (hlin : ∀ (a : ℂ) v w, ι (a • v + w) =ᵐ[μ] fun x => a * ι v x + ι w x)
    (A : K →L[ℂ] K) (E : Submodule ℂ K)
    (hE : ∀ v ∈ E, ∃ φ : G → ℂ, Continuous φ ∧ ι (A v) =ᵐ[μ] φ)
    (hB : ∀ B, IsCompact B → ∃ C : ℝ, ∀ v ∈ E, ∀ φ : G → ℂ, Continuous φ → ι (A v) =ᵐ[μ] φ →
      ∀ x ∈ B, ‖φ x‖ ≤ C * ‖v‖) :
    ∃ Λ : G → (K →L[ℂ] ℂ), ∀ v ∈ closure (E : Set K),
      (Continuous fun x => Λ x v) ∧ ι (A v) =ᵐ[μ] fun x => Λ x v := by
  have hE' : ∀ w : E, ∃ φ : G → ℂ, Continuous φ ∧ ι (A w) =ᵐ[μ] φ := fun w => hE w w.2
  choose ψ hψc hψae using hE'
  have hadd : ∀ w w' : E, ψ (w + w') = fun x => ψ w x + ψ w' x := fun w w' =>
    (Continuous.ae_eq_iff_eq μ (hψc _) ((hψc w).add (hψc w'))).1 (by
      filter_upwards [hψae (w + w'), _root_.GlobalTheory.LocRep.rep_add hlin (A w) (A w'), hψae w, hψae w']
        with x h0 h1 h2 h3
      show ψ (w + w') x = ψ w x + ψ w' x
      rw [← h0, ← h2, ← h3, ← h1]
      simp)
  have hsmul : ∀ (a : ℂ) (w : E), ψ (a • w) = fun x => a * ψ w x := fun a w =>
    (Continuous.ae_eq_iff_eq μ (hψc _) (continuous_const.mul (hψc w))).1 (by
      filter_upwards [hψae (a • w), _root_.GlobalTheory.LocRep.rep_smul hlin a (A w), hψae w] with x h0 h1 h2
      show ψ (a • w) x = a * ψ w x
      rw [← h0, ← h2, ← h1]
      simp)
  let L : G → E →L[ℂ] ℂ := fun x => LinearMap.mkContinuousOfExistsBound
    { toFun := fun w => ψ w x
      map_add' := fun w w' => congrFun (hadd w w') x
      map_smul' := fun a w => by simpa using congrFun (hsmul a w) x } (by
      obtain ⟨c, hc⟩ := hB {x} isCompact_singleton
      exact ⟨c, fun w => hc w w.2 _ (hψc w) (hψae w) x rfl⟩)
  have hext : ∀ x, ∃ g : K →L[ℂ] ℂ, (∀ w : E, g w = L x w) ∧ ‖g‖ = ‖L x‖ :=
    fun x => exists_extension_norm_eq E (L x)
  choose Λ hΛext hΛnorm using hext
  have hbound : ∀ B, IsCompact B → ∃ c : ℝ, 0 ≤ c ∧ ∀ x ∈ B, ‖Λ x‖ ≤ c := by
    intro B hBc
    obtain ⟨c, hc⟩ := hB B hBc
    refine ⟨max c 0, le_max_right _ _, fun x hx => ?_⟩
    rw [hΛnorm]
    refine ContinuousLinearMap.opNorm_le_bound _ (le_max_right _ _) fun w => ?_
    exact (hc w w.2 _ (hψc w) (hψae w) x hx).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  refine ⟨Λ, fun v hv => ?_⟩
  obtain ⟨u, hun, hu⟩ := mem_closure_iff_seq_limit.1 hv
  have hcont : ∀ n, Continuous fun x => Λ x (u n) := fun n => by
    have h : (fun x => Λ x (u n)) = ψ ⟨u n, hun n⟩ := funext fun x => hΛext x ⟨u n, hun n⟩
    rw [h]
    exact hψc _
  have hunif : ∀ B, IsCompact B →
      TendstoUniformlyOn (fun n x => Λ x (u n)) (fun x => Λ x v) atTop B := by
    intro B hBc
    obtain ⟨c, hc0, hc⟩ := hbound B hBc
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hu' := (Metric.tendsto_nhds.1 hu) (ε / (c + 1)) (by positivity)
    filter_upwards [hu'] with n hn x hx
    rw [dist_eq_norm, ← map_sub]
    calc ‖Λ x (v - u n)‖ ≤ ‖Λ x‖ * ‖v - u n‖ := (Λ x).le_opNorm _
      _ ≤ c * (ε / (c + 1)) := by
          refine mul_le_mul (hc x hx) ?_ (norm_nonneg _) hc0
          rw [← dist_eq_norm, dist_comm]
          exact hn.le
      _ < ε := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
          nlinarith
  have hcontv : Continuous fun x => Λ x v :=
    (tendstoLocallyUniformly_iff_forall_isCompact.2 hunif).continuous
      (Eventually.of_forall hcont).frequently
  have hint : ∀ C, IsCompact C → ∫ x in C, ι (A v) x ∂μ = ∫ x in C, Λ x v ∂μ := by
    intro C hC
    obtain ⟨Pr, hPr⟩ := _root_.GlobalTheory.LocRep.exists_pairing hloc hlin hC
    obtain ⟨c, hc0, hc⟩ := hbound C hC
    have h1 : Tendsto (fun n => Pr (A (u n))) atTop (𝓝 (Pr (A v))) :=
      ((Pr.continuous.comp A.continuous).tendsto v).comp hu
    have h2 : ∀ n, Pr (A (u n)) = ∫ x in C, Λ x (u n) ∂μ := fun n => by
      rw [hPr]
      refine integral_congr_ae (ae_restrict_of_ae ?_)
      filter_upwards [hψae ⟨u n, hun n⟩] with x hx
      rw [hx]
      exact (hΛext x ⟨u n, hun n⟩).symm
    have h3 : Tendsto (fun n => ∫ x in C, Λ x (u n) ∂μ) atTop (𝓝 (∫ x in C, Λ x v ∂μ)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun n => norm_nonneg _) (g := fun n => c * ‖u n - v‖ * (μ C).toReal)
        (fun n => ?_) ?_
      · rw [← integral_sub ((hcont n).locallyIntegrable.integrableOn_isCompact hC)
          (hcontv.locallyIntegrable.integrableOn_isCompact hC)]
        refine norm_setIntegral_le_of_norm_le_const hC.measure_lt_top fun x hx => ?_
        rw [← map_sub]
        exact ((Λ x).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hc x hx) (norm_nonneg _))
      · have h4 : Tendsto (fun n => ‖u n - v‖) atTop (𝓝 0) :=
          tendsto_iff_norm_sub_tendsto_zero.1 hu
        simpa using (h4.const_mul c).mul_const (μ C).toReal
    rw [← hPr]
    exact tendsto_nhds_unique (h1.congr h2) h3
  exact ⟨hcontv, _root_.GlobalTheory.LocRep.rep_of_pairing hloc hcontv.locallyIntegrable hint⟩

end GlobalTheory.LocRep
end

section

open Filter Topology

namespace GlobalTheory.OneParamMatrix

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem eq_exp_of_continuous_oneParameter {n : Type} [Fintype n] [DecidableEq n]
    (N : ℝ → Matrix n n ℂ) (hc : Continuous N) (h0 : N 0 = 1)
    (hm : ∀ s t, N (s + t) = N s * N t) :
    ∃ Y : Matrix n n ℂ, ∀ t : ℝ, N t = NormedSpace.exp (t • Y) := by
  have hd := GlobalTheory.LocWeil.DerComm.differentiableAt_oneParameter N hc h0 hm
  set Y := deriv N 0 with hY
  have hN : ∀ t, HasDerivAt N (N t * Y) t := by
    intro t
    have h1 : HasDerivAt (fun s => N t * N (s - t)) (N t * Y) t := by
      have h2 : HasDerivAt (fun s => N (s - t)) Y t := by
        have hd' : HasDerivAt N Y (t - t) := by rw [sub_self]; exact hd.hasDerivAt
        exact hd'.comp_sub_const t t
      exact h2.const_mul (N t)
    refine h1.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
    simp only
    rw [← hm]; congr 1; ring
  refine ⟨Y, fun t => ?_⟩
  set f : ℝ → Matrix n n ℂ := fun s => N s * NormedSpace.exp ((-s) • Y) with hf
  have hfd : ∀ s, HasDerivAt f 0 s := by
    intro s
    have he : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • (-Y))) (NormedSpace.exp (s • (-Y)) * (-Y)) s :=
      hasDerivAt_exp_smul_const (𝕂 := ℝ) (-Y) s
    have he' : HasDerivAt (fun u : ℝ => NormedSpace.exp ((-u) • Y))
        (NormedSpace.exp ((-s) • Y) * (-Y)) s := by
      simpa [smul_neg, neg_smul] using he
    have := (hN s).mul he'
    refine this.congr_deriv ?_
    have hcomm : Y * NormedSpace.exp ((-s) • Y) = NormedSpace.exp ((-s) • Y) * Y :=
      ((Commute.refl Y).smul_right (-s)).exp_right.eq
    rw [mul_assoc, hcomm]
    simp [mul_neg]
  have hconst := is_const_of_deriv_eq_zero (fun s => (hfd s).differentiableAt)
    (fun s => (hfd s).deriv) t 0
  have hf0 : f 0 = 1 := by simp [hf, h0]
  rw [hf0] at hconst
  have hinv : NormedSpace.exp ((-t) • Y) * NormedSpace.exp (t • Y) = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl Y).smul_left _).smul_right _)]
    simp
  calc N t = N t * (NormedSpace.exp ((-t) • Y) * NormedSpace.exp (t • Y)) := by rw [hinv, mul_one]
    _ = f t * NormedSpace.exp (t • Y) := by simp only [hf, mul_assoc]
    _ = NormedSpace.exp (t • Y) := by rw [hconst, one_mul]

end GlobalTheory.OneParamMatrix
end

section

open Filter Topology

theorem _root_.GlobalTheory.T.polyGrowth_strip_of_integral_monodromy : ∀ (g m : ℕ) (lam : ℂ → Fin m → Fin g → ℂ) (C : ℝ) (k : ℕ) (P Q : Fin m → Fin m → ℤ), (∀ s : ℂ, s.re < 0 → ∀ j, lam (s + 2 * Real.pi * Complex.I) j = ∑ i, P j i • lam s i) → (∀ s : ℂ, s.re < 0 → ∀ j, lam s j = ∑ i, Q j i • lam (s + 2 * Real.pi * Complex.I) i) → (∀ s : ℂ, s.re < 0 → ‖Complex.exp s‖ ≤ 1 / 2 → |s.im| ≤ Real.pi → ‖lam s‖ ≤ C * (1 + ‖s‖) ^ k) → ∀ R : ℝ, ∃ C' : ℝ, ∀ s : ℂ, s.re < 0 → ‖Complex.exp s‖ ≤ 1 / 2 → |s.im| ≤ R → ‖lam s‖ ≤ C' * (1 + ‖s‖) ^ k := by
  first | exact @GlobalTheory.polyGrowth_spread_of_integral_monodromy | exact GlobalTheory.polyGrowth_spread_of_integral_monodromy | (intros; apply GlobalTheory.polyGrowth_spread_of_integral_monodromy <;> assumption)
end

section

open Polynomial Filter Topology

namespace GlobalTheory

namespace SmallPoint

theorem exists_extend_of_ker_le {R B Ω : Type*} [CommRing R] [CommRing B]
    [Algebra R B] [Algebra.IsIntegral R B] [Field Ω] [IsAlgClosed Ω]
    (φ : R →+* Ω) (h : RingHom.ker (algebraMap R B) ≤ RingHom.ker φ) :
    ∃ ψ : B →+* Ω, ψ.comp (algebraMap R B) = φ := by
  haveI := RingHom.ker_isPrime φ
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := B)
    (RingHom.ker φ) ⊥ h
  haveI : Q.LiesOver (RingHom.ker φ) := ⟨hQP.symm⟩
  letI : Algebra (R ⧸ RingHom.ker φ) Ω := (RingHom.kerLift φ).toAlgebra
  haveI : FaithfulSMul (R ⧸ RingHom.ker φ) Ω :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (RingHom.kerLift_injective φ)
  haveI : Module.IsTorsionFree (R ⧸ RingHom.ker φ) Ω := FaithfulSMul.to_isTorsionFree _ _
  haveI : Module.IsTorsionFree (R ⧸ RingHom.ker φ) (B ⧸ Q) := FaithfulSMul.to_isTorsionFree _ _
  haveI : Algebra.IsIntegral (R ⧸ RingHom.ker φ) (B ⧸ Q) :=
    Algebra.IsIntegral.tower_top (R := R)
  haveI : Algebra.IsAlgebraic (R ⧸ RingHom.ker φ) (B ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  let σ : (B ⧸ Q) →ₐ[R ⧸ RingHom.ker φ] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨σ.toRingHom.comp (Ideal.Quotient.mk Q), RingHom.ext fun r => ?_⟩
  exact (σ.commutes (Ideal.Quotient.mk _ r)).trans (RingHom.kerLift_mk φ r)

theorem exists_extend_apply_eq {R B Ω : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing B] [IsDomain B] [Algebra R B] [Algebra.IsIntegral R B] [FaithfulSMul R B]
    [Field Ω] [IsAlgClosed Ω] (ψ : R →+* Ω) (u : B) (t : Ω)
    (ht : (minpoly R u).eval₂ ψ t = 0) :
    ∃ φ : B →+* Ω, φ.comp (algebraMap R B) = ψ ∧ φ u = t := by
  letI : Algebra R[X] B := (aeval u : R[X] →ₐ[R] B).toRingHom.toAlgebra
  haveI : IsScalarTower R R[X] B :=
    IsScalarTower.of_algebraMap_eq fun x => ((aeval u : R[X] →ₐ[R] B).commutes x).symm
  haveI : Algebra.IsIntegral R[X] B := Algebra.IsIntegral.tower_top (R := R)
  obtain ⟨φ, hφ⟩ := exists_extend_of_ker_le (B := B) (eval₂RingHom ψ t) (fun f hf => by
    obtain ⟨g, rfl⟩ := minpoly.isIntegrallyClosed_dvd
      (Algebra.IsIntegral.isIntegral (R := R) u) (p := f) hf
    rw [RingHom.mem_ker, map_mul, coe_eval₂RingHom, ht, zero_mul])
  have h : ∀ f : R[X], φ (aeval u f) = f.eval₂ ψ t := fun f => DFunLike.congr_fun hφ f
  refine ⟨φ, RingHom.ext fun r => ?_, ?_⟩
  · simpa using h (C r)
  · simpa using h X

theorem exists_root_norm_lt {F : ℂ[X]} (hF : F.Monic) {ε : ℝ} (hε : 0 < ε)
    (h : ‖F.coeff 0‖ < ε ^ F.natDegree) : ∃ t, F.IsRoot t ∧ ‖t‖ < ε := by
  first
  | exact @_root_.GlobalTheory.RootNormLowerBound.exists_root_norm_lt
  | exact _root_.GlobalTheory.RootNormLowerBound.exists_root_norm_lt
  | (apply _root_.GlobalTheory.RootNormLowerBound.exists_root_norm_lt <;> assumption)
  | (intros; apply _root_.GlobalTheory.RootNormLowerBound.exists_root_norm_lt <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RootNormLowerBound.exists_root_norm_lt <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RootNormLowerBound.exists_root_norm_lt ..)

theorem exists_eventually_norm_le {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    (Ψ : R →+* ℂ[X]) {b : B} (hb : IsIntegral R b) :
    ∃ M : ℝ, ∀ᶠ s in 𝓝 (0 : ℂ), ∀ φ : B →+* ℂ,
      φ.comp (algebraMap R B) = (evalRingHom s).comp Ψ → ‖φ b‖ ≤ M := by
  obtain ⟨G, hG, hGb⟩ := hb
  have h1 : ∀ i : ℕ, ∀ᶠ s in 𝓝 (0 : ℂ),
      ‖(Ψ (G.coeff i)).eval s‖ < ‖(Ψ (G.coeff i)).eval 0‖ + 1 := fun i =>
    ((Ψ (G.coeff i)).continuous.norm.tendsto 0).eventually (gt_mem_nhds (lt_add_one _))
  refine ⟨∑ i ∈ Finset.range G.natDegree, (‖(Ψ (G.coeff i)).eval 0‖ + 1) + 1, ?_⟩
  filter_upwards [(Finset.range G.natDegree).eventually_all.2 fun i _ => h1 i] with s hs φ hφ
  have hm : (G.map ((evalRingHom s).comp Ψ)).Monic := hG.map _
  have hr : (G.map ((evalRingHom s).comp Ψ)).IsRoot (φ b) := by
    rw [IsRoot, eval_map, ← hφ, ← hom_eval₂, hGb, map_zero]
  have h2 := hr.norm_lt_cauchyBound hm.ne_zero
  rw [cauchyBound, hm.leadingCoeff, nnnorm_one, div_one, hG.natDegree_map] at h2
  have h3 : ((Finset.range G.natDegree).sup
      (fun i => ‖(G.map ((evalRingHom s).comp Ψ)).coeff i‖₊) : NNReal) ≤
      ∑ i ∈ Finset.range G.natDegree, (‖(Ψ (G.coeff i)).eval 0‖₊ + 1) := by
    refine Finset.sup_le fun i hi => ?_
    refine le_trans ?_ (Finset.single_le_sum
      (f := fun i => ‖(Ψ (G.coeff i)).eval 0‖₊ + 1) (fun _ _ => zero_le) hi)
    rw [coeff_map]
    exact_mod_cast (hs i hi).le
  have h4 := h2.le.trans (add_le_add_left h3 1)
  have h5 := NNReal.coe_le_coe.2 h4
  push_cast at h5
  exact h5

theorem exists_small_of_curve {R B : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing B] [IsDomain B] [Algebra R B] [Algebra.IsIntegral R B] [FaithfulSMul R B]
    (Ψ : R →+* ℂ[X]) (p : B →+* ℂ) (hp : p.comp (algebraMap R B) = (evalRingHom 0).comp Ψ)
    {n : ℕ} (w : Fin n → B) {u : B} (hu : p u = 0) {r : R} (hr : Ψ r ≠ 0) :
    ∃ M : ℝ, ∀ ε : ℝ, 0 < ε → ∃ (s : ℂ) (φ : B →+* ℂ),
      φ.comp (algebraMap R B) = (evalRingHom s).comp Ψ ∧ (Ψ r).eval s ≠ 0 ∧ ‖φ u‖ < ε ∧
        ∀ i, ‖φ (w i)‖ ≤ M := by
  choose M hM using fun i => exists_eventually_norm_le Ψ
    (Algebra.IsIntegral.isIntegral (R := R) (w i))
  refine ⟨∑ i, |M i|, fun ε hε => ?_⟩
  have hint := Algebra.IsIntegral.isIntegral (R := R) u
  have hF := minpoly.monic hint
  have h0 : (Ψ ((minpoly R u).coeff 0)).eval 0 = 0 := by
    have h := congrArg p (minpoly.aeval R u)
    rw [aeval_def, hom_eval₂, hu, eval₂_at_zero, hp, p.map_zero] at h
    exact h
  have h1 : ∀ᶠ s in 𝓝 (0 : ℂ),
      ‖(Ψ ((minpoly R u).coeff 0)).eval s‖ < ε ^ (minpoly R u).natDegree :=
    ((Ψ _).continuous.norm.tendsto 0).eventually (gt_mem_nhds (by
      simp only [h0, norm_zero]
      positivity))
  have h2 : ∀ᶠ s in 𝓝[≠] (0 : ℂ), ¬ (Ψ r).IsRoot s :=
    nhdsNE_le_cofinite _ (eventually_cofinite.2 (by
      simpa using (Ψ r).finite_setOf_isRoot hr))
  obtain ⟨s, hs2, hs1, hs3⟩ := (h2.and
    ((h1.and (eventually_all.2 hM)).filter_mono nhdsWithin_le_nhds)).exists
  obtain ⟨t, ht, htε⟩ := exists_root_norm_lt (hF.map ((evalRingHom s).comp Ψ)) hε (by
    rw [coeff_map, hF.natDegree_map]
    exact hs1)
  obtain ⟨φ, hφ, hφu⟩ := exists_extend_apply_eq ((evalRingHom s).comp Ψ) u t (by
    rwa [IsRoot, eval_map] at ht)
  refine ⟨s, φ, hφ, hs2, hφu ▸ htε, fun i => (hs3 i φ hφ).trans ((le_abs_self _).trans ?_)⟩
  exact Finset.single_le_sum (f := fun i => |M i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)

end SmallPoint

theorem exists_complex_point_norm_lt_of_not_isUnit :
    ∀ (K B : Type) [Field K] [CommRing B] [IsDomain B] [Algebra K B] [Algebra.FiniteType K B]
      (σ : K →+* ℂ) (n : ℕ) (w : Fin n → B) (u q : B), ¬ IsUnit u → q ≠ 0 →
      ∃ M : ℝ, ∀ ε : ℝ, 0 < ε → ∃ φ : B →+* ℂ, φ.comp (algebraMap K B) = σ ∧ φ q ≠ 0 ∧
        ‖φ u‖ < ε ∧ ∀ i, ‖φ (w i)‖ ≤ M := by
  intro K B _ _ _ _ _ σ n w u q hu hq
  obtain ⟨d, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg K B
  letI := g.toRingHom.toAlgebra
  haveI : Algebra.IsIntegral (MvPolynomial (Fin d) K) B := ⟨hint⟩
  haveI : FaithfulSMul (MvPolynomial (Fin d) K) B :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  haveI : Nontrivial (B ⧸ Ideal.span {u}) :=
    Ideal.Quotient.nontrivial_iff.2 (by rwa [Ne, Ideal.span_singleton_eq_top])
  obtain ⟨p₀, hp₀⟩ := exists_ringHom_extend_of_finiteType K (B ⧸ Ideal.span {u}) ℂ σ
  let p : B →+* ℂ := p₀.comp (Ideal.Quotient.mk _)
  have hpu : p u = 0 := by
    change p₀ (Ideal.Quotient.mk _ u) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self u), map_zero]
  obtain ⟨r, hr, c, hc⟩ :=
    (Algebra.IsIntegral.isIntegral (R := MvPolynomial (Fin d) K) q).isAlgebraic.exists_nonzero_dvd
      (mem_nonZeroDivisors_of_ne_zero hq)
  obtain ⟨z, hz⟩ : ∃ z : Fin d → ℂ, MvPolynomial.eval z (MvPolynomial.map σ r) ≠ 0 := by
    by_contra! h
    exact hr (MvPolynomial.map_injective σ σ.injective
      (MvPolynomial.funext (by simpa using h)))
  let Ψ : MvPolynomial (Fin d) K →+* ℂ[X] := MvPolynomial.eval₂Hom (C.comp σ)
    fun j => C (p (g (MvPolynomial.X j))) + X * C (z j - p (g (MvPolynomial.X j)))
  have hΨ0 : p.comp (algebraMap (MvPolynomial (Fin d) K) B) = (evalRingHom 0).comp Ψ := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_)
    · have : p (g (MvPolynomial.C a)) = σ a := by
        rw [MvPolynomial.algHom_C]
        exact hp₀ a
      exact this.trans (by simp [Ψ])
    · simp [Ψ]
      rfl
  have hΨ1 : (evalRingHom 1).comp Ψ = (MvPolynomial.eval z).comp (MvPolynomial.map σ) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_) <;> simp [Ψ]
  have hΨr : Ψ r ≠ 0 := fun h => hz (by
    have := DFunLike.congr_fun hΨ1 r
    simpa [h] using this.symm)
  obtain ⟨M, hM⟩ := SmallPoint.exists_small_of_curve Ψ p hΨ0 w hpu hΨr
  refine ⟨M, fun ε hε => ?_⟩
  obtain ⟨s, φ, hφ, h1, h2, h3⟩ := hM ε hε
  refine ⟨φ, RingHom.ext fun a => ?_, fun h => h1 ?_, h2, h3⟩
  · have := DFunLike.congr_fun hφ (MvPolynomial.C a)
    rw [RingHom.comp_apply, ← MvPolynomial.algHom_C g]
    exact this.trans (by simp [Ψ])
  · have := DFunLike.congr_fun hφ r
    rw [RingHom.comp_apply, hc, map_mul, h, zero_mul] at this
    exact this.symm

end GlobalTheory
end

section

open Topology Filter

theorem _root_.GlobalTheory.T.exists_nhds_fix_of_continuous_coefficients : (∀ {V : Type} [AddCommGroup V] [Module ℂ V] (s : Set V),
    (∀ l : V →ₗ[ℂ] ℂ, ∃ C : ℝ, ∀ x ∈ s, ‖l x‖ ≤ C) → FiniteDimensional ℂ (Submodule.span ℂ s)) →
  ∀ {G : Type} [Group G] [TopologicalSpace G] (H : Subgroup G) {V : Type} [AddCommGroup V] [Module ℂ V]
    (S : G → Module.End ℂ V), (∀ x ∈ H, ∀ y ∈ H, S (x * y) = S x * S y) → S 1 = 1 →
    (∀ (l : V →ₗ[ℂ] ℂ) (w : V), ContinuousOn (fun x => l (S x w)) (H : Set G)) →
    (∀ U ∈ 𝓝 (1 : G), ∃ K : Subgroup G, K ≤ H ∧ IsCompact (K : Set G) ∧
      (∃ O : Set G, IsOpen O ∧ (1 : G) ∈ O ∧ ∀ x ∈ O, x ∈ H → x ∈ K) ∧ (K : Set G) ⊆ U) →
    ∀ v : V, ∃ U ∈ 𝓝 (1 : G), ∀ x ∈ U, x ∈ H → S x v = v := by
  first | exact @GlobalTheory.SmoothFix.exists_nhds_fix | exact GlobalTheory.SmoothFix.exists_nhds_fix | (intros; apply GlobalTheory.SmoothFix.exists_nhds_fix <;> assumption)
end

section

open MeasureTheory

theorem _root_.GlobalTheory.T.vanishing_of_projection_support : ∀ {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.IsAddHaarMeasure] (P : X →+ X), Continuous P →
    (∀ x, P (P x) = P x) → ∀ (Φ Ψ : X → ℂ), Continuous Φ → Continuous Ψ → ∀ K : Set X, IsCompact K →
    (∀ x, Φ x ≠ 0 → P x ∈ K) → ∀ y : X, (∀ z, P z = z → Φ (y + z) = 0) →
    (∀ O : Set X, IsOpen O → y ∈ O → ∃ h : X → ENNReal, Measurable h ∧ (∀ x, h x ≤ 1) ∧
      (∀ x z, P z = z → h (x + z) = h x) ∧ (∀ x, h x ≠ 0 → x + (P y - P x) ∈ O) ∧
      (∃ O' : Set X, IsOpen O' ∧ y ∈ O' ∧ ∀ x ∈ O', Ψ x ≠ 0 → 1 / 2 ≤ h x) ∧
      ∫⁻ x, h x * ‖Ψ x‖ₑ ^ 2 ∂μ = ∫⁻ x, h x * ‖Φ x‖ₑ ^ 2 ∂μ) → Ψ y = 0 := by
  first | exact @GlobalTheory.FiberPointwise.vanish_at_point | exact GlobalTheory.FiberPointwise.vanish_at_point | (intros; apply GlobalTheory.FiberPointwise.vanish_at_point <;> assumption)
end

section

open NumberField MeasureTheory

theorem _root_.GlobalTheory.T.mellin_integral_split_functional_equation : ∀ (I : Type) [Fintype I] [Nonempty I] (p : (I → ℝ) → ℝ) (θ θ' : (I → ℝ) → ℂ) (κ s : ℂ), (∀ y, θ y = κ * (Real.exp (-∑ i, y i) : ℂ) * θ' (-y)) → MeasureTheory.Integrable (fun y => (p y : ℂ) * θ y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ))) (MeasureTheory.volume.restrict {y : I → ℝ | 0 ≤ ∑ i, y i}) → MeasureTheory.Integrable (fun y => (p (-y) : ℂ) * θ' y * Complex.exp ((1 - s) * ((∑ i, y i : ℝ) : ℂ))) (MeasureTheory.volume.restrict {y : I → ℝ | 0 ≤ ∑ i, y i}) → ∫ y, (p y : ℂ) * θ y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ)) = (∫ y in {y : I → ℝ | 0 ≤ ∑ i, y i}, (p y : ℂ) * θ y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ))) + κ * ∫ y in {y : I → ℝ | 0 ≤ ∑ i, y i}, (p (-y) : ℂ) * θ' y * Complex.exp ((1 - s) * ((∑ i, y i : ℝ) : ℂ)) := by
  first | exact @GlobalTheory.mellinSplit_neg | exact GlobalTheory.mellinSplit_neg | (intros; apply GlobalTheory.mellinSplit_neg <;> assumption)
end

section

open NumberField MeasureTheory

theorem _root_.GlobalTheory.T.orbit_unfold_integral_partition_of_unity : ∀ (I : Type) [Fintype I] (U : Type) [Countable U] (t : U → I → ℝ) (p : (I → ℝ) → ℝ), Measurable p → (∀ y, 0 ≤ p y) → (∀ y, HasSum (fun u => p (y - t u)) 1) → ∀ g : (I → ℝ) → ℂ, Integrable g → HasSum (fun u => ∫ y, (p y : ℂ) * g (y + t u)) (∫ y, g y) ∧ HasSum (fun u => ∫ y, p y * ‖g (y + t u)‖) (∫ y, ‖g y‖) := by
  first | exact @GlobalTheory.OrbitUnfold.orbit_unfold | exact GlobalTheory.OrbitUnfold.orbit_unfold | (intros; apply GlobalTheory.OrbitUnfold.orbit_unfold <;> assumption)
end

section

open IsDedekindDomain NumberField
open scoped Classical


theorem _root_.GlobalTheory.T.exists_mixedSpace_dual_vector_traceForm : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ),
    (∀ z : mixedEmbedding.mixedSpace F, z ≠ 0 → ∃ u, ℓ (z * u) ≠ 0) →
    ∀ lam : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ, ∃ u : κ → mixedEmbedding.mixedSpace F,
      ∀ x, ℓ (∑ k, x k * u k) = lam x := by
  first | exact @GlobalTheory.dualform | exact GlobalTheory.dualform | (intros; apply GlobalTheory.dualform <;> assumption)
end
