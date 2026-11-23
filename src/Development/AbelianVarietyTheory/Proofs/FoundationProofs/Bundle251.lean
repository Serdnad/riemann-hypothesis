module

public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle230
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle231
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle238
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle239
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle240
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle222
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.HasSumLocallyUniformlyWeierstrassZetaExcept
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus

@[expose] public section

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.AdaptedBasis

theorem exists_denominator {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] (κ : ι → K) :
    ∃ R : ℕ, 0 < R ∧ ∃ a : ι → 𝓞 K, ∀ i, (a i : K) = (R : K) * κ i := by
  obtain ⟨y, hy, h⟩ := exists_integral_multiples ℤ ℚ (L := K) (Finset.univ.image κ)
  have h' : ∀ i, IsIntegral ℤ (((y.natAbs : ℕ) : K) * κ i) := by
    intro i
    have hi := h (κ i) (Finset.mem_image_of_mem κ (Finset.mem_univ i))
    rw [zsmul_eq_mul] at hi
    rcases Int.natAbs_eq y with e | e
    · have : ((y.natAbs : ℕ) : K) = (y : K) := by
        conv_rhs => rw [e]
        simp only [Int.cast_natCast]
      rw [this]; exact hi
    · have : ((y.natAbs : ℕ) : K) = -(y : K) := by
        conv_rhs => rw [e]
        simp only [Int.cast_neg, Int.cast_natCast, neg_neg]
      rw [this, neg_mul]; exact hi.neg
  exact ⟨y.natAbs, Int.natAbs_pos.2 hy, fun i => ⟨_, h' i⟩, fun i => rfl⟩

theorem embV_sum (D : D7) (T : Tor D) (h0 : ∀ τ, T.emb τ 0 = 0)
    (hadd : ∀ τ x y, T.emb τ (x + y) = T.emb τ x + T.emb τ y)
    (hmul : ∀ τ (a : D.host.K) y, T.emb τ ((a : D.host.E) * y) = D.host.φ₀ (a : D.host.E) * T.emb τ y)
    {N N' r : ℕ} (B : Fin r → Matrix (Fin N') (Fin N) D.host.E) (κ : Fin r → D.host.K) :
    embV D T (∑ i, κ i • B i) = ∑ i, D.host.φ₀ (κ i : D.host.E) • embV D T (B i) := by
  funext τ p q
  let f : D.host.E →+ ℂ := ⟨⟨T.emb τ, h0 τ⟩, hadd τ⟩
  have e : (∑ i, κ i • B i) p q = ∑ i, (κ i : D.host.E) * B i p q := by
    rw [Matrix.sum_apply]
    rfl
  have e2 : T.emb τ (∑ i, (κ i : D.host.E) * B i p q) = ∑ i, T.emb τ ((κ i : D.host.E) * B i p q) :=
    map_sum f _ _
  simp only [embV, e, e2, hmul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem liftM_of_mem (M : IntermediateField ℚ ℂ) {x : ℂ} (h : x ∈ M) : liftM M x = ⟨x, h⟩ := dif_pos h

theorem sum_smul_comm {V : Type*} [AddCommGroup V] [Module ℂ V] {r s : ℕ} (c : Fin s → ℂ) (k : Fin s → Fin r → ℂ)
    (v : Fin r → V) : ∑ j, c j • ∑ i, k j i • v i = ∑ i, (∑ j, k j i * c j) • v i := by
  simp only [Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

theorem rationalLatticePoint_add {Λ : AddSubgroup ℂ} {x y : ℂ} (hx : InRationalLattice Λ x) (hy : InRationalLattice Λ y) : InRationalLattice Λ (x + y) := by
  obtain ⟨m, hm, hx⟩ := hx
  obtain ⟨n, hn, hy⟩ := hy
  refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
  have : ((m * n : ℕ) : ℂ) * (x + y) = n • ((m : ℂ) * x) + m • ((n : ℂ) * y) := by
    simp only [nsmul_eq_mul]; push_cast; ring
  rw [this]
  exact Λ.add_mem (Λ.nsmul_mem hx n) (Λ.nsmul_mem hy m)

theorem adpB_of_family : ∀ (D : D7), admG1 D → galStar D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ), FixK D M ρ → DataIn D (tor0 D cc δ) M → ∀ (N N' r s : ℕ) (B : Fin r → Matrix (Fin N') (Fin N) D.host.E) (b : Fin s → Matrix (Fin N') (Fin N) D.host.E), OnB D B → ∃ R : ℕ, 0 < R ∧ ∀ (n : ℕ) (c c' : Fin s → ℂ), 0 < n → (∀ j, InRationalLattice (lamOf D cc δ) (c j)) → (∀ j, Adp1 M ρ (lamOf D cc δ) (n * R) (c j) (c' j)) → AdpB D (tor0 D cc δ) M ρ B n (∑ j, c j • embV D (tor0 D cc δ) (b j)) (∑ j, c' j • embV D (torConj D (tor0 D cc δ) M ρ) (b j)) := by
  intro D hG hS cc δ hC M ρ hF hD N N' r s B b hB
  have hspan : ∀ j, ∃ κ : Fin r → D.host.K, ∑ i, κ i • B i = b j := fun j =>
    (Submodule.mem_span_range_iff_exists_fun D.host.K).1 (by rw [hB.2]; trivial)
  choose κ hκ using hspan
  obtain ⟨R, hR, a, ha⟩ := exists_denominator (fun p : Fin s × Fin r => κ p.1 p.2)
  have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have haφ : ∀ j i, D.host.φ₀ (((a (j, i) : D.host.K) : D.host.E)) = R * D.host.φ₀ (κ j i : D.host.E) := by
    intro j i
    rw [ha]
    push_cast
    rw [map_mul, map_natCast]
  have hΛ := (GlobalTheory.CurveLattice.lattice_of_curve D hG cc δ hC).2.2.2.2
  obtain ⟨-, -, -, hadd, hmul, -⟩ := hS cc δ hC M ρ hF hD.2.1 hD.2.2
  have hM : ∀ τ x, embT D τ x ∈ M := hD.1
  have hψ := hG.1
  have e1 : ∀ j, embV D (tor0 D cc δ) (b j) =
      ∑ i, D.host.φ₀ (κ j i : D.host.E) • embV D (tor0 D cc δ) (B i) := by
    intro j
    rw [← hκ j]
    refine embV_sum D _ (fun τ => map_zero (embT D τ)) (fun τ => map_add (embT D τ)) (fun τ k y => ?_) B _
    show embT D τ _ = _ * embT D τ y
    rw [map_mul, hψ]
  have e2 : ∀ j, embV D (torConj D (tor0 D cc δ) M ρ) (b j) =
      ∑ i, D.host.φ₀ (κ j i : D.host.E) • embV D (torConj D (tor0 D cc δ) M ρ) (B i) := by
    intro j
    rw [← hκ j]
    refine embV_sum D _ (fun τ => ?_) (fun τ x y => ?_) (fun τ k y => ?_) B _
    · show ρ (liftM M (embT D τ 0)) = 0
      rw [map_zero, liftM_of_mem M (zero_mem M)]
      exact map_zero ρ
    · show ρ (liftM M (embT D τ (x + y))) = ρ (liftM M (embT D τ x)) + ρ (liftM M (embT D τ y))
      rw [liftM_of_mem M (hM τ _), liftM_of_mem M (hM τ _), liftM_of_mem M (hM τ _), ← map_add ρ]
      congr 1
      exact Subtype.ext (map_add (embT D τ) x y)
    · show ρ (liftM M (embT D τ (_ * y))) = _ * ρ (liftM M (embT D τ y))
      rw [← (hF k).2, cj, liftM_of_mem M (hM τ _), liftM_of_mem M (hM τ _), liftM_of_mem M (hF k).1, ← map_mul ρ]
      congr 1
      apply Subtype.ext
      show embT D τ (_ * y) = D.host.φ₀ _ * embT D τ y
      rw [map_mul, hψ]
  refine ⟨R, hR, fun n c c' hn hc hA => ⟨fun i => ∑ j, D.host.φ₀ (κ j i : D.host.E) * c j,
    fun i => ∑ j, D.host.φ₀ (κ j i : D.host.E) * c' j, fun i => ?_, ?_, ?_, fun i => ?_⟩⟩
  · refine Finset.sum_induction _ (InRationalLattice (lamOf D cc δ)) (fun x y => rationalLatticePoint_add)
      ⟨1, one_pos, by simp⟩ (fun j _ => ?_)
    obtain ⟨m, hm, hj⟩ := hc j
    refine ⟨R * m, Nat.mul_pos hR hm, ?_⟩
    have := hΛ (a (j, i)) _ hj
    rw [haφ] at this
    convert this using 1
    push_cast; ring
  · simp only [e1]; exact sum_smul_comm _ _ _
  · simp only [e2]; exact sum_smul_comm _ _ _
  · have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have key : ∀ t : Finset (Fin s), StarPt M ρ (lamOf D cc δ)
        ((∑ j ∈ t, D.host.φ₀ (κ j i : D.host.E) * c j) / n) ((∑ j ∈ t, D.host.φ₀ (κ j i : D.host.E) * c' j) / n) := by
      intro t
      induction t using Finset.induction_on with
      | empty => left; simp
      | insert j t hj ih =>
        rw [Finset.sum_insert hj, Finset.sum_insert hj, add_div, add_div]
        refine hadd _ _ _ _ ?_ ih
        have := hmul (a (j, i)) _ _ (hA j)
        rw [haφ] at this
        convert this using 1 <;> (push_cast; field_simp)
    exact key Finset.univ

end GlobalTheory.AdaptedBasis
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.EvenTheta

def IsLat (Λ : AddSubgroup ℂ) : Prop :=
  ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}

def sqTh (Λ : AddSubgroup ℂ) (v z : ℂ) : ℂ := sgStar Λ (v + z) * sgStar Λ (v - z) / sgStar Λ v ^ 2

def AlgEnt (F : ℂ → ℂ) : Prop := Differentiable ℂ F ∧ ∀ n, coef1 F n ∈ Qbar

def IntSer {K : Type*} [NormedField K] (f : PowerSeries K) : Prop := ∀ n, ‖PowerSeries.coeff n f‖ ≤ 1

def BddSer {K : Type*} [NormedField K] (f : PowerSeries K) : Prop :=
  ∃ B : ℝ, ∀ n, ‖PowerSeries.coeff n f‖ ≤ B

def lineSer {K : Type*} [CommRing K] (e : PowerSeries K) (x : K) : PowerSeries K :=
  e - PowerSeries.C x * PowerSeries.X ^ 2

def IsWpSer {K : Type*} [CommRing K] (a b : K) (P : PowerSeries K) : Prop :=
  PowerSeries.constantCoeff P = 1 ∧
    (PowerSeries.X * PowerSeries.derivativeFun P - 2 * P) ^ 2 =
      4 * P ^ 3 - PowerSeries.C a * PowerSeries.X ^ 4 * P - PowerSeries.C b * PowerSeries.X ^ 6

def xAt {p : ℕ} [Fact p.Prime] (g : GL3Theta.G1 p) (v : ℂ) : ℂ_[p] :=
  ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 2 * (lamC g.lam (wpF g.abelian₂ v) - g.C.r)

variable {Λ : AddSubgroup ℂ}

theorem IsLat.differentiable (h : IsLat Λ) : Differentiable ℂ (sgStar Λ) :=
  (GlobalTheory.OddTheta.sgStar_laws Λ h).1.1

theorem IsLat.sg_neg (h : IsLat Λ) (z : ℂ) : sgStar Λ (-z) = -sgStar Λ z :=
  (GlobalTheory.OddTheta.sgStar_laws Λ h).1.2.2.1 z

theorem IsLat.sg_eq_zero (h : IsLat Λ) (z : ℂ) : sgStar Λ z = 0 ↔ z ∈ Λ :=
  (GlobalTheory.OddTheta.sgStar_laws Λ h).2.1 z

theorem IsLat.sg_law (h : IsLat Λ) {ω : ℂ} (hω : ω ∈ Λ) (z : ℂ) :
    U1 Λ ω (sgStar Λ) z = (if ω / 2 ∈ Λ then 1 else -1) * sgStar Λ z :=
  (GlobalTheory.OddTheta.sgStar_laws Λ h).1.2.2.2 ω hω z

theorem IsLat.dense_compl (h : IsLat Λ) : Dense (Λ : Set ℂ)ᶜ := by
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ h
  have : (Λ : Set ℂ) = (L.lattice : Set ℂ) := Set.ext fun z => hL z
  rw [this]
  exact GlobalTheory.dense_compl_lattice L

theorem IsLat.differentiable_sqTh (h : IsLat Λ) (v : ℂ) : Differentiable ℂ (sqTh Λ v) := by
  have := h.differentiable
  unfold sqTh
  fun_prop

theorem sqTh_neg (v z : ℂ) : sqTh Λ v (-z) = sqTh Λ v z := by
  simp only [sqTh, sub_neg_eq_add, ← sub_eq_add_neg, mul_comm]

theorem IsLat.sqTh_zero (h : IsLat Λ) {v : ℂ} (hv : v ∉ Λ) : sqTh Λ v 0 = 1 := by
  have := (h.sg_eq_zero v).not.2 hv
  simp only [sqTh, add_zero, sub_zero]
  field_simp

theorem IsLat.sqTh_eq_zero (h : IsLat Λ) {v : ℂ} (hv : v ∉ Λ) (z : ℂ) :
    sqTh Λ v z = 0 ↔ v + z ∈ Λ ∨ v - z ∈ Λ := by
  have := (h.sg_eq_zero v).not.2 hv
  simp [sqTh, this, h.sg_eq_zero]

theorem IsLat.sqTh_eq (h : IsLat Λ) {v z : ℂ} (hv : v ∉ Λ) (hz : z ∉ Λ) :
    sqTh Λ v z = sgStar Λ z ^ 2 * (wpF Λ z - wpF Λ v) := by
  have h0 := (h.sg_eq_zero v).not.2 hv
  have h1 := (GlobalTheory.OddTheta.sgStar_laws Λ h).2.2.2.1 v z hv hz
  rw [sqTh, div_eq_iff (pow_ne_zero 2 h0)]
  linear_combination h1

theorem IsLat.sqTh_sub (h : IsLat Λ) {v w : ℂ} (hv : v ∉ Λ) (hw : w ∉ Λ) (z : ℂ) :
    sqTh Λ v z = sqTh Λ w z + (wpF Λ w - wpF Λ v) * sgStar Λ z ^ 2 := by
  have h1 := (h.differentiable_sqTh v).continuous
  have h2 := (h.differentiable_sqTh w).continuous
  have h3 := h.differentiable.continuous
  refine congrFun (Continuous.ext_on h.dense_compl h1
    (g := fun z => sqTh Λ w z + (wpF Λ w - wpF Λ v) * sgStar Λ z ^ 2) (by fun_prop) fun z hz => ?_) z
  beta_reduce
  rw [h.sqTh_eq hv hz, h.sqTh_eq hw hz]
  ring

theorem IsLat.wp_eq_iff (h : IsLat Λ) {v w : ℂ} (hv : v ∉ Λ) (hw : w ∉ Λ) :
    wpF Λ w = wpF Λ v ↔ v + w ∈ Λ ∨ v - w ∈ Λ := by
  rw [← h.sqTh_eq_zero hv, h.sqTh_eq hv hw]
  simp [(h.sg_eq_zero w).not.2 hw, sub_eq_zero]

theorem IsLat.sqTh_mul (h : IsLat Λ) {v : ℂ} (hv : v ∉ Λ) (z : ℂ) :
    (U1 Λ v (sgStar Λ) 0 * U1 Λ (-v) (sgStar Λ) 0) * sqTh Λ v z =
      U1 Λ v (sgStar Λ) z * U1 Λ (-v) (sgStar Λ) z := by
  have h0 := (h.sg_eq_zero v).not.2 hv
  have e : ∀ z : ℂ, U1 Λ v (sgStar Λ) z * U1 Λ (-v) (sgStar Λ) z =
      -(sgStar Λ (v + z) * sgStar Λ (v - z)) *
        Complex.exp (-((Real.pi : ℂ) * v * (starRingEnd ℂ) v / (area Λ : ℂ))) := by
    intro z
    simp only [U1]
    rw [show z + -v = -(v - z) by ring, h.sg_neg, add_comm z v, mul_mul_mul_comm, ← Complex.exp_add]
    congr 1
    · ring
    · congr 1
      simp only [map_neg]
      ring
  rw [e, e, sqTh]
  simp only [add_zero, sub_zero]
  field_simp

end GlobalTheory.EvenTheta
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators

theorem _root_.GlobalTheory.T.adapted_torsion_lift_deeper_level : ∀ (D : D7), galStar D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ σ : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ, FixK D ⊤ σ → ∀ (c c' : ℂ) (n₀ n : ℕ), 0 < n₀ → 0 < n → InRationalLattice (lamOf D cc δ) c → Adp1 ⊤ σ (lamOf D cc δ) n₀ c c' → ∃ ω ∈ lamOf D cc δ, Adp1 ⊤ σ (lamOf D cc δ) (n₀ * n) (c + (n₀ : ℂ) * ω) c' := by
  first | exact @GlobalTheory.GalTheta.adapted_lift_deeper | exact GlobalTheory.GalTheta.adapted_lift_deeper | (intros; apply GlobalTheory.GalTheta.adapted_lift_deeper <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators

theorem _root_.GlobalTheory.T.thetaOddPrimePhase_conj_invariant : ∀ (D : D7) (T T' : Tor D) (N N' : ℕ) (x x' : VC D N N') (σ : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ) (p k : ℕ) (m : ℤ), p.Prime → p ≠ 2 → (p : ℝ) ^ k * qH D T x = (m : ℝ) → cj ⊤ σ (wdPh D T x) = wdPh D T' x' → wPh D T p x = (-1 : ℂ) ^ m ∧ wPh D T' p x' = (-1 : ℂ) ^ m := by
  first | exact @GlobalTheory.GalThetaSign.wPh_conj | exact GlobalTheory.GalThetaSign.wPh_conj | (intros; apply GlobalTheory.GalThetaSign.wPh_conj <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

theorem _root_.GlobalTheory.T.conjugateLattice_eq_closure_independent_pair : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ), g2 (lamOf D cc δ) ∈ M → g3 (lamOf D cc δ) ∈ M → ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ lamConj M ρ (lamOf D cc δ) = AddSubgroup.closure {w₁, w₂} := by
  first | exact @GlobalTheory.ConjugateLattice.lamConj_eq_closure_pair | exact GlobalTheory.ConjugateLattice.lamConj_eq_closure_pair | (intros; apply GlobalTheory.ConjugateLattice.lamConj_eq_closure_pair <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

theorem _root_.GlobalTheory.T.exists_algClosure_embedding_extending_on_algebraic : ∀ (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ), ∃ ρ' : Qbar →ₐ[ℚ] ℂ, ∀ x : ℂ, x ∈ Qbar → x ∈ M → cj M ρ x = cj Qbar ρ' x := by
  first | exact @GlobalTheory.ThetaConj.exists_cj_Qbar_eq | exact GlobalTheory.ThetaConj.exists_cj_Qbar_eq | (intros; apply GlobalTheory.ThetaConj.exists_cj_Qbar_eq <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators

theorem _root_.GlobalTheory.T.exists_complexEndomorphism_eq_on_countable : ∀ (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (S : Set ℂ), S.Countable → ∃ σ : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ, ∀ x ∈ S, x ∈ M → cj ⊤ σ x = cj M ρ x := by
  first | exact @GlobalTheory.GalTheta.exists_top_embedding_eq_on_countable | exact GlobalTheory.GalTheta.exists_top_embedding_eq_on_countable | (intros; apply GlobalTheory.GalTheta.exists_top_embedding_eq_on_countable <;> assumption)
end
