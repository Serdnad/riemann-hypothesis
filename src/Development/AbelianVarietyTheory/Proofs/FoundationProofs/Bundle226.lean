module

public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.CoeffSubstInvMemOfTwoLeOrder
public import Development.AutomorphicArithmetic.WeightCongruences.IsRootOfIntegral
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsDual
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle020
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.Normed
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
public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle209
import Formalism.LocalRingCardinality.DataTheta
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormSum

noncomputable def hYYLeft (D : D7) {N N' : ℕ} (y : Matrix (Fin N') (Fin N) D.host.E) :
    Matrix (Fin N') (Fin N) D.host.E →ₗ[D.host.K] D.host.K where
  toFun x := hYY D x y
  map_add' x x' := by
    simp only [hYY, Matrix.add_apply, add_mul, Finset.sum_add_distrib, map_add (f := _)]
  map_smul' c x := by
    simp only [hYY, Matrix.smul_apply, smul_mul_assoc, RingHom.id_apply]
    rw [← map_smul, Finset.smul_sum]
    simp only [Finset.smul_sum]

theorem hYY_herm (D : D7) (h : TraceMapNormalisation D) {N N' : ℕ} (x y : Matrix (Fin N') (Fin N) D.host.E) :
    D.host.φ₀ ((hYY D y x : D.host.K) : D.host.E) =
      starRingEnd ℂ (D.host.φ₀ ((hYY D x y : D.host.K) : D.host.E)) := by
  have hc : ∀ (φ : D.host.E →+* ℂ) (z : D.host.E), φ (D.host.conj z) = starRingEnd ℂ (φ z) :=
    fun φ z => D.host.conjE_apply φ z
  unfold hYY
  rw [← h, ← h]

  simp only [map_sum, map_mul, hc, Complex.conj_conj]
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem onB_expand (D : D7) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (hb : OnB D b)
    (x : Matrix (Fin N') (Fin N) D.host.E) : x = ∑ i, hYY D x (b i) • b i := by
  have hx : x ∈ Submodule.span D.host.K (Set.range b) := by rw [hb.2]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.K).1 hx
  have h1 : ∀ k, hYY D x (b k) = c k := by
    intro k
    change hYYLeft D (b k) x = c k

    rw [← hc, map_sum]
    have h2 : ∀ i, hYYLeft D (b k) (c i • b i) = if i = k then c i else 0 := by
      intro i
      rw [map_smul]
      change c i • hYY D (b i) (b k) = _
      rw [hb.1 i k]
      split_ifs <;> simp
    simp only [h2]
    simp
  simp only [h1]
  exact hc.symm

theorem onB_parseval (D : D7) (h : TraceMapNormalisation D) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (hb : OnB D b) (x y : Matrix (Fin N') (Fin N) D.host.E) :
    D.host.φ₀ ((hYY D x y : D.host.K) : D.host.E) =
      ∑ i, D.host.φ₀ ((hYY D x (b i) : D.host.K) : D.host.E) *
        starRingEnd ℂ (D.host.φ₀ ((hYY D y (b i) : D.host.K) : D.host.E)) := by
  have h1 : hYY D x y = ∑ i, hYY D x (b i) * hYY D (b i) y := by
    change hYYLeft D y x = _
    conv_lhs => rw [onB_expand D b hb x]

    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
    rfl
  have h2 := congrArg (D.host.φ₀.comp (algebraMap D.host.K D.host.E)) h1

  rw [map_sum] at h2
  refine h2.trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [map_mul, ← hYY_herm D h y (b i)]
  rfl

theorem det_onB_mul_conj : ∀ (D : D7), admG1 D → ∀ (N N' r : ℕ) (b₀ b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b₀ → OnB D b → (((Matrix.of fun i j => hYY D (b j) (b₀ i)).det : D.host.K) : D.host.E) * D.host.conj (((Matrix.of fun i j => hYY D (b j) (b₀ i)).det : D.host.K) : D.host.E) = 1 := by
  intro D hD N N' r b₀ b hb₀ hb
  have hc : ∀ (φ : D.host.E →+* ℂ) (z : D.host.E), φ (D.host.conj z) = starRingEnd ℂ (φ z) :=
    fun φ z => D.host.conjE_apply φ z
  set M : Matrix (Fin r) (Fin r) D.host.K := Matrix.of fun i j => hYY D (b j) (b₀ i) with hM
  let ψ : D.host.K →+* ℂ := D.host.φ₀.comp (algebraMap D.host.K D.host.E)
  have hA : (ψ.mapMatrix M).transpose * (starRingEnd ℂ).mapMatrix (ψ.mapMatrix M) = 1 := by
    ext j k
    rw [Matrix.mul_apply]
    have h1 := onB_parseval D hD.2 b₀ hb₀ (b j) (b k)
    rw [hb.1 j k] at h1
    refine Eq.trans h1.symm ?_
    rw [Matrix.one_apply]
    split_ifs
    · exact map_one ψ
    · exact map_zero ψ
  have hdet := congrArg Matrix.det hA
  rw [Matrix.det_mul, Matrix.det_transpose, ← RingHom.map_det (starRingEnd ℂ), ← RingHom.map_det ψ, Matrix.det_one] at hdet
  apply D.host.φ₀.injective
  rw [map_mul, hc, map_one]
  exact hdet

end GlobalTheory.NormSum
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormSum

theorem isIntegral_half_one_add {L : Type*} [Field L] [CharZero L] (d : ℕ) (hd : d % 16 = 7) (b : L)
    (hb : b ^ 2 = -(d : L)) : IsIntegral ℤ ((1 + b) / 2) := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, d + 1 = 4 * m := ⟨(d + 1) / 4, by omega⟩
  have hm' : (d : L) + 1 = 4 * (m : L) := by exact_mod_cast hm
  refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (m : ℤ), ?_, ?_⟩
  · monicity!
  · rw [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C, map_natCast]
    linear_combination (1 / 4 : L) * hb - (1 / 4 : L) * hm'

theorem exists_integer_map_eq_w0 :
    ∀ (D : D7), ∃ a : 𝓞 D.host.K, D.host.φ₀ (((a : D.host.K) : D.host.E)) = w0 D := by
  intro D
  have hsq := D.host.sqd_sq
  have hd16 : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
  have hd0 : (0 : ℝ) ≤ D.host.d := Nat.cast_nonneg _
  have key : ∀ b : D.host.K, (b : D.host.E) ^ 2 = -(D.host.d : D.host.E) →
      D.host.φ₀ (b : D.host.E) = Complex.I * (Real.sqrt D.host.d : ℂ) →
      ∃ a : 𝓞 D.host.K, D.host.φ₀ (((a : D.host.K) : D.host.E)) = w0 D := by
    intro b hb hφ
    have hb' : b ^ 2 = -(D.host.d : D.host.K) := by
      apply Subtype.ext
      simpa using hb
    refine ⟨⟨(1 + b) / 2, isIntegral_half_one_add _ hd16 b hb'⟩, ?_⟩
    change D.host.φ₀ (algebraMap D.host.K D.host.E ((1 + b) / 2)) = _
    rw [map_div₀, map_add (f := _), map_one, map_ofNat, map_div₀, map_add (f := _), map_one, map_ofNat]
    change (1 + D.host.φ₀ (b : D.host.E)) / 2 = _
    rw [hφ, w0]
  let b : D.host.K := ⟨D.host.sqd, IntermediateField.mem_adjoin_simple_self ℚ _⟩
  have h1 : (D.host.φ₀ (b : D.host.E)) ^ 2 = (Complex.I * (Real.sqrt D.host.d : ℂ)) ^ 2 := by
    change (D.host.φ₀ (D.host.sqd)) ^ 2 = _
    rw [← map_pow, hsq, map_neg, map_natCast, mul_pow, Complex.I_sq, ← Complex.ofReal_pow,
      Real.sq_sqrt hd0]
    simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
  · exact key b hsq h
  · refine key (-b) ?_ ?_
    · change (-(D.host.sqd)) ^ 2 = _
      rw [neg_sq, hsq]
    · change D.host.φ₀ (-(b : D.host.E)) = _
      rw [map_neg, h, neg_neg]

end GlobalTheory.NormSum
end

section

noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.GenusOneDatum


open PowerSeries in
theorem exists_fixed_of_contract {R : Type*} [CommRing R] (T : PowerSeries R → PowerSeries R)
    (hT : ∀ (n : ℕ) (x y : PowerSeries R), X ^ n ∣ x - y → X ^ (n + 1) ∣ T x - T y) :
    ∃ x, T x = x := by
  have hit : ∀ (n : ℕ) (x y : PowerSeries R), X ^ n ∣ T^[n] x - T^[n] y := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro x y
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact hT n _ _ (ih x y)
  let L : PowerSeries R := PowerSeries.mk fun n => coeff n (T^[n + 1] 0)
  have hL : ∀ n, X ^ n ∣ L - T^[n] 0 := by
    intro n
    rw [X_pow_dvd_iff]
    intro m hm
    obtain ⟨k, rfl⟩ : ∃ k, n = (m + 1) + k := ⟨n - (m + 1), by omega⟩
    have := X_pow_dvd_iff.1 (hit (m + 1) 0 (T^[k] 0)) m (by omega)
    rw [← Function.iterate_add_apply] at this
    simpa [L] using this
  refine ⟨L, ?_⟩
  ext n
  have h1 := hT n _ _ (hL n)
  have h2 := hL (n + 1)
  rw [Function.iterate_succ_apply'] at h2
  have h3 := dvd_sub h1 h2
  have h4 := X_pow_dvd_iff.1 h3 n (by omega)
  rw [sub_sub_sub_cancel_right, map_sub, sub_eq_zero] at h4
  exact h4

theorem exists_isWq {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) : ∃ wq, IsWq W wq := by
  let c := algebraMap ℂ_[p] (PowerSeries ℂ_[p])
  let X := (PowerSeries.X : PowerSeries ℂ_[p])
  obtain ⟨w, hw⟩ := exists_fixed_of_contract (fun wq : PowerSeries ℂ_[p] =>
    1 + c W.a₁ * X * wq + c W.a₂ * X ^ 2 * wq + c W.a₃ * X ^ 3 * wq ^ 2 +
    c W.a₄ * X ^ 4 * wq ^ 2 + c W.a₆ * X ^ 6 * wq ^ 3) (by
      rintro n x y ⟨z, hz⟩
      refine ⟨z * (c W.a₁ + c W.a₂ * X + (c W.a₃ * X ^ 2 + c W.a₄ * X ^ 3) * (x + y) +
        c W.a₆ * X ^ 5 * (x ^ 2 + x * y + y ^ 2)), ?_⟩
      have hz' : x - y = X ^ n * z := hz
      change _ = X ^ (n + 1) * _
      linear_combination (X * (c W.a₁ + c W.a₂ * X + (c W.a₃ * X ^ 2 + c W.a₄ * X ^ 3) * (x + y) +
        c W.a₆ * X ^ 5 * (x ^ 2 + x * y + y ^ 2))) * hz')
  exact ⟨w, hw.symm⟩

theorem constantCoeff_of_isWq {p : ℕ} [Fact p.Prime] {W : WeierstrassCurve ℂ_[p]}
    {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) : PowerSeries.constantCoeff wq = 1 := by
  have h' := congrArg PowerSeries.constantCoeff h
  simpa using h'

theorem coeff_one_flog {p : ℕ} [Fact p.Prime] {W : WeierstrassCurve ℂ_[p]}
    {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) : PowerSeries.coeff 1 (flog W wq) = 1 := by
  have h2 : PowerSeries.constantCoeff (2 : PowerSeries ℂ_[p]) = 2 := map_ofNat _ 2
  simp [flog, omegaW, PowerSeries.constantCoeff_inv, constantCoeff_of_isWq h, h2]

theorem constantCoeff_flog {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p])
    (wq : PowerSeries ℂ_[p]) : PowerSeries.constantCoeff (flog W wq) = 0 := by
  simp [flog]

theorem exists_subst_eq_X {R : Type*} [CommRing R] (l : PowerSeries R)
    (h0 : PowerSeries.constantCoeff l = 0) (h1 : PowerSeries.coeff 1 l = 1) :
    ∃ ex : PowerSeries R, PowerSeries.constantCoeff ex = 0 ∧
      PowerSeries.subst ex l = PowerSeries.X := by
  have hA : GlobalTheory.FormalInv.linearPart (fun _ : Unit => (l : MvPowerSeries Unit R)) = 1 := by
    ext i j
    exact h1
  obtain ⟨v, hv, h, -⟩ := (GlobalTheory.FormalInv.exists_substInv_iff
    (u := fun _ : Unit => (l : MvPowerSeries Unit R)) (fun _ => h0)).2 (hA ▸ isUnit_one)
  exact ⟨v (), hv (), h ()⟩

theorem exists_genusOne_datum : ∀ (D : D7), GL3Theta.modelEx D → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → Nat.Coprime (Ideal.absNorm cc) p → ∃ g : GL3Theta.G1 p, GL3Theta.At D cc δ g ∧ g.lam = lam ∧ ‖((g.C.u : ℂ_[p]ˣ) : ℂ_[p])‖ = 1 := by
  intro D hm p _ lam cc δ hc hcop
  obtain ⟨⟨C, hC⟩, -, hu⟩ := hm p lam cc δ hc.1 hcop hc.2
  obtain ⟨wq, hwq⟩ := exists_isWq (C • wModel lam (lamOf D cc δ))
  obtain ⟨ex, he0, he⟩ := exists_subst_eq_X _ (constantCoeff_flog _ wq) (coeff_one_flog hwq)
  exact ⟨⟨lam, lamOf D cc δ, C, wq, ex⟩, ⟨hc.1, hcop, hc.2, rfl, hC, hwq, he0, he⟩, rfl, hu C hC⟩

end GlobalTheory.GenusOneDatum
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.NormSum.UnramHecke

def phase : ℂˣ →* ℂˣ where
  toFun z := Units.mk0 ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) (div_ne_zero z.ne_zero (by simp))
  map_one' := by ext; simp
  map_mul' x y := by
    ext
    simp only [Units.val_mul, Units.val_mk0, norm_mul, Complex.ofReal_mul]
    rw [div_mul_div_comm]

theorem phase_val (z : ℂˣ) : ((phase z : ℂˣ) : ℂ) = (z : ℂ) / (‖(z : ℂ)‖ : ℂ) := rfl

theorem norm_phase (z : ℂˣ) : ‖((phase z : ℂˣ) : ℂ)‖ = 1 := by
  rw [phase_val, norm_div, Complex.norm_real, norm_norm, div_self (by simp)]

theorem phase_of_norm (z : ℂˣ) (h : ‖(z : ℂ)‖ = 1) : phase z = z := by
  ext; rw [phase_val, h]; simp

theorem exists_unitary_extension {A M : Type} [CommGroup A] [CommGroup M] (Φ : A →* M) (χ : A →* ℂˣ)
    (hk : ∀ a, Φ a = 1 → χ a = 1) (hu : ∀ a, ‖((χ a : ℂˣ) : ℂ)‖ = 1) :
    ∃ κ : M →* ℂˣ, (∀ x, κ (Φ x) = χ x) ∧ ∀ y, ‖((κ y : ℂˣ) : ℂ)‖ = 1 := by
  let _ : DivisibleBy (Additive ℂˣ) ℕ := divisibleByOfSMulRightSurj _ _ fun {n} hn u => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u.toMul : ℂ) (Nat.pos_of_ne_zero hn)
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hn] at hz
      exact Units.ne_zero _ hz.symm
    exact ⟨Additive.ofMul (Units.mk0 z hz0), Units.ext hz⟩
  let _ : DivisibleBy (Additive ℂˣ) ℤ := AddGroup.divisibleByIntOfDivisibleByNat _
  obtain ⟨ρ, hρ⟩ := (Module.Baer.of_divisible (Additive ℂˣ)).extension_property_addMonoidHom
    (MonoidHom.toAdditive (QuotientGroup.kerLift Φ)) (QuotientGroup.kerLift_injective Φ)
    (MonoidHom.toAdditive (QuotientGroup.lift Φ.ker χ fun a ha => hk a ha))
  refine ⟨phase.comp (MonoidHom.toAdditive.symm ρ), fun x => ?_, fun y => norm_phase _⟩
  have h : (MonoidHom.toAdditive.symm ρ) (Φ x) = χ x :=
    DFunLike.congr_fun hρ (Additive.ofMul (QuotientGroup.mk x))
  rw [MonoidHom.comp_apply, h, phase_of_norm _ (hu x)]

variable (D : D7)

theorem emb_conj (σ : D.host.E →+* ℂ) (z : D.host.E) : σ (D.host.conj z) = starRingEnd ℂ (σ z) :=
  D.host.conjE_apply σ z

theorem conj_conj (z : D.host.E) : D.host.conj (D.host.conj z) = z := by
  apply D.host.φ₀.injective
  rw [emb_conj, emb_conj, Complex.conj_conj]

theorem sgA_sgA (x : AE D) : sgA D (sgA D x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
  | tmul a b => simp [sgA, Formalism.UG.sigR, conj_conj]

theorem sgU_sgU (x : (AE D)ˣ) : sgU D (sgU D x) = x := Units.ext (sgA_sgA D x)

theorem sgA_mem {x : AE D} (hx : x ∈ OhE D) : sgA D x ∈ OhE D :=
  Formalism.UG.P.csDual_sig_mem _ hx

def intUnits : Subgroup (AE D)ˣ where
  carrier := {u | IntU D u}
  one_mem' := ⟨by simp, by simp⟩
  mul_mem' := fun {a b} ha hb => ⟨by rw [Units.val_mul]; exact mul_mem ha.1 hb.1,
    by rw [mul_inv, Units.val_mul]; exact mul_mem ha.2 hb.2⟩
  inv_mem' := fun {a} ha => ⟨ha.2, by rw [inv_inv]; exact ha.1⟩

theorem sgU_mem {u : (AE D)ˣ} (hu : u ∈ intUnits D) : sgU D u ∈ intUnits D :=
  ⟨sgA_mem D hu.1, by rw [← map_inv]; exact sgA_mem D hu.2⟩

def ratio : (AE D)ˣ →* (AE D)ˣ := MonoidHom.id _ / sgU D

theorem ratio_apply (x : (AE D)ˣ) : ratio D x = x / sgU D x := rfl

abbrev incU : D.host.Eˣ →* (AE D)ˣ := Units.map (inc D).toMonoidHom

def infChar (c : ℤ) : D.host.Eˣ →* ℂˣ :=
  ∏ τ : D.what₂.Tau, (zpowGroupHom (2 * c)).comp (phase.comp (Units.map (embT D τ).toMonoidHom))

theorem infChar_val (c : ℤ) (a : D.host.Eˣ) : ((infChar D c a : ℂˣ) : ℂ) =
    ∏ τ, (embT D τ (a : D.host.E) / (‖embT D τ (a : D.host.E)‖ : ℂ)) ^ (2 * c) := by
  simp [infChar, phase_val]

theorem norm_infChar (c : ℤ) (a : D.host.Eˣ) : ‖((infChar D c a : ℂˣ) : ℂ)‖ = 1 := by
  rw [infChar_val, norm_prod]
  refine Finset.prod_eq_one fun τ _ => ?_
  have h : embT D τ (a : D.host.E) ≠ 0 := (map_ne_zero _).2 a.ne_zero
  rw [norm_zpow, norm_div, Complex.norm_real, norm_norm, div_self (by simpa using h), one_zpow]

theorem ratio_eq_pm (a : D.host.Eˣ) (h : ratio D (incU D a) ∈ intUnits D) :
    ∃ m : ℕ, 0 < m ∧ ((a : D.host.E) / D.host.conj a) ^ m = 1 := by
  have hc : D.host.conj (a : D.host.E) ≠ 0 := (map_ne_zero _).2 a.ne_zero
  have hval : ((ratio D (incU D a) : (AE D)ˣ) : AE D) = inc D ((a : D.host.E) / D.host.conj a) := by
    have h1 : ((sgU D (incU D a) : (AE D)ˣ) : AE D) = inc D (D.host.conj a) :=
      Formalism.UG.P.csDual_sig_incl _ _
    rw [ratio_apply, div_eq_mul_inv, Units.val_mul, Units.mul_inv_eq_iff_eq_mul, h1, ← map_mul,
      div_mul_cancel₀ _ hc]
    rfl
  have hint : IsIntegral ℤ ((a : D.host.E) / D.host.conj a) :=
    Formalism.UG.P.csGlob_int (F := ℚ) _ (by have := h.1; rw [hval] at this; exact this)
  obtain ⟨n, hn, hpow⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one D.host.E ℂ hint (fun φ => by
    rw [map_div₀, emb_conj, norm_div, Complex.norm_conj, div_self]
    simpa using a.ne_zero)
  exact ⟨n, hn, hpow⟩

theorem infChar_eq_one (c : ℤ) (a : D.host.Eˣ) (h : ratio D (incU D a) ∈ intUnits D) : infChar D c a = 1 := by
  apply Units.ext
  rw [infChar_val, Units.val_one]
  have key : ∀ τ, (embT D τ (a : D.host.E) / (‖embT D τ (a : D.host.E)‖ : ℂ)) ^ (2 * c) =
      embT D τ ((a : D.host.E) / D.host.conj a) ^ c := by
    intro τ
    have h : embT D τ (a : D.host.E) ≠ 0 := (map_ne_zero _).2 a.ne_zero
    rw [zpow_mul, map_div₀, emb_conj, zpow_two, div_mul_div_comm, ← sq (‖_‖ : ℂ), ← Complex.mul_conj',
      mul_div_mul_left _ _ h]
  simp only [key]
  exact UpperTheory.Mu.prod_emb_zpow D.host D.eTau (ratio_eq_pm D a h) c

end GlobalTheory.NormSum.UnramHecke

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.HolDS Matrix MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace GlobalTheory.HolDS.DerPt

section Gen

variable {n : Type} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.Operator in
theorem hasDerivAt_exp_entry (X : Matrix n n ℂ) (i j : n) :
    HasDerivAt (fun t : ℝ => (NormedSpace.exp (t • X)) i j) (X i j) 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
  let L : Matrix n n ℂ →L[ℝ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  exact L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h

theorem hasDerivAt_det_of_one (A : ℝ → Matrix n n ℂ) (A' : Matrix n n ℂ) (h0 : A 0 = 1)
    (h : ∀ i j, HasDerivAt (fun t => A t i j) (A' i j) 0) :
    HasDerivAt (fun t => (A t).det) A'.trace 0 := by
  first
  | exact @_root_.GlobalTheory.DetDerivativeAtOne.hasDerivAt_det_of_one
  | exact _root_.GlobalTheory.DetDerivativeAtOne.hasDerivAt_det_of_one
  | (apply _root_.GlobalTheory.DetDerivativeAtOne.hasDerivAt_det_of_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.DetDerivativeAtOne.hasDerivAt_det_of_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DetDerivativeAtOne.hasDerivAt_det_of_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DetDerivativeAtOne.hasDerivAt_det_of_one ..)

end Gen

variable {p q : ℕ}

end GlobalTheory.HolDS.DerPt
end
