module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarFundamentalDomainOrthogonalSum
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle089
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle028
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle453
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle450
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle456
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle418
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ConsCompSuccAboveZero
import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle003

@[expose] public section

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf
open GlobalTheory.CompanionTheory.SW.ThetaStage

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep.WittOne

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem hE_add_right (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x y z : Fin M → E) :
    hE σ J x (y + z) = hE σ J x y + hE σ J x z := by
  simp [hE, hform, mul_add, Finset.sum_add_distrib]

theorem hE_add_left (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x y z : Fin M → E) :
    hE σ J (x + y) z = hE σ J x z + hE σ J y z := by
  simp [hE, hform, add_mul, Finset.sum_add_distrib]

theorem hE_smul_right (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (c : E)
    (x y : Fin M → E) : hE σ J x (c • y) = c * hE σ J x y := by
  simp only [hE, hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hE_smul_left (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (c : E)
    (x y : Fin M → E) : hE σ J (c • x) y = σ c * hE σ J x y := by
  simp only [hE, hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, map_mul,
    AlgHom.coe_toRingHom, RingHom.coe_coe]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hE_herm (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (y z : Fin M → E) : σ (hE σ J y z) = hE σ J z y := by

  simp only [hE, hform, map_sum, map_mul, AlgHom.coe_toRingHom, RingHom.coe_coe, hσ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ i j]
  ring

theorem exists_partner [CharZero E] (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) {N : ℕ}
    (K : Matrix (Fin N) (Fin N) E) (hK : IsHermND σ K) (x : Fin N → E) (hx0 : x ≠ 0)
    (hxx : hE σ K x x = 0) : ∃ y, hE σ K x y = 1 ∧ hE σ K y y = 0 := by
  have hherm := hE_herm σ hσ K hK.1
  have hex : ∃ y₀, hE σ K x y₀ ≠ 0 := by
    by_contra hall
    push_neg at hall
    have hv : Matrix.vecMul (fun i => σ (x i)) K = 0 := by
      funext j
      have := hall (Pi.single j 1)
      simpa [hE, hform, Pi.single_apply, Matrix.vecMul, dotProduct] using this
    have hz : (fun i => σ (x i)) = 0 := by
      have hu : IsUnit K := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hK.2)
      exact (Matrix.vecMul_injective_of_isUnit hu) (by simpa using hv)
    apply hx0
    funext i
    have h := congrArg σ (congrFun hz i)
    simpa [hσ] using h
  obtain ⟨y₀, hy₀⟩ := hex
  obtain ⟨y₁, hxy₁⟩ : ∃ y₁, hE σ K x y₁ = 1 :=
    ⟨(hE σ K x y₀)⁻¹ • y₀, by rw [hE_smul_right]; exact inv_mul_cancel₀ hy₀⟩
  have hy₁x : hE σ K y₁ x = 1 := by rw [← hherm, hxy₁, map_one]
  obtain ⟨q, hq⟩ : ∃ q, q = hE σ K y₁ y₁ := ⟨_, rfl⟩
  have hqs : σ q = q := by rw [hq]; exact hherm _ _
  obtain ⟨y, hy⟩ : ∃ y : Fin N → E, y = y₁ + (-(q / 2)) • x := ⟨_, rfl⟩
  have hxy : hE σ K x y = 1 := by
    rw [hy, hE_add_right, hE_smul_right, hxy₁, hxx]; simp
  have hyy : hE σ K y y = 0 := by
    have hs2 : σ (-(q / 2)) = -(q / 2) := by
      rw [map_neg, map_div₀, hqs, map_ofNat]
    rw [hy, hE_add_right, hE_add_left, hE_add_left, hE_smul_right, hE_smul_right, hE_smul_left,
      hE_smul_left, hs2, hy₁x, hxy₁, hxx, ← hq]
    field_simp
    ring
  exact ⟨y, hxy, hyy⟩

theorem gramE_pair (σ : E →ₐ[F] E) {N : ℕ} (K : Matrix (Fin N) (Fin N) E) (u v : Fin N → E)
    (h1 : hE σ K u u = 0) (h2 : hE σ K u v = 1) (h3 : hE σ K v u = 1) (h4 : hE σ K v v = 0) :
    gramE σ K ![u, v] = !![0, 1; 1, 0] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [gramE, h1, h2, h3, h4]

theorem hE_hypOne_basis (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    hE σ (hypOne J) (Fin.cons 1 fun _ => 0) (Fin.cons 1 fun _ => 0) = 0 ∧
    hE σ (hypOne J) (Fin.cons 1 fun _ => 0) (Fin.cons 0 (Fin.cons 1 fun _ => 0)) = 1 ∧
    hE σ (hypOne J) (Fin.cons 0 (Fin.cons 1 fun _ => 0)) (Fin.cons 1 fun _ => 0) = 1 ∧
    hE σ (hypOne J) (Fin.cons 0 (Fin.cons 1 fun _ => 0)) (Fin.cons 0 (Fin.cons 1 fun _ => 0)) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [hE, hform, Fin.sum_univ_succ, hypOne_zero_zero, hypOne_zero_one, hypOne_one_zero, hypOne_one_one]

end Alg

theorem exists_unitary_e0 : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ q : Fin 1 → Fin (M + 2) → E, q ∈ framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) → ∃ g : UJ (σ : E →+* E) (hypOne J), gact σ g q = e0 E M := by
  intro F E _ _ _ _ _ σ hCM M J hJ q hq
  obtain ⟨hσ, -⟩ := GlobalTheory.CompanionTheory.SW.HaarCoord.conj_facts hCM
  have hK := isHermND_hypOne σ hJ
  obtain ⟨hli, hg⟩ := hq
  have hx0 : q 0 ≠ 0 := hli.ne_zero 0
  have hxx : hE σ (hypOne J) (q 0) (q 0) = 0 := congrFun (congrFun hg 0) 0
  obtain ⟨y, hxy, hyy⟩ := exists_partner σ hσ (hypOne J) hK (q 0) hx0 hxx
  have hyx : hE σ (hypOne J) y (q 0) = 1 := by
    rw [← hE_herm σ hσ _ hK.1, hxy, map_one]
  obtain ⟨b1, b2, b3, b4⟩ := hE_hypOne_basis σ J
  have hX := gramE_pair σ (hypOne J) (q 0) y hxx hxy hyx hyy
  have hY := gramE_pair σ (hypOne J) _ _ b1 b2 b3 b4
  obtain ⟨g, hgU, hgX⟩ := GlobalTheory.T.witt_extension_global F E σ hCM (M + 2) (hypOne J) hK 2 _ _ (hX.trans hY.symm)
    (by rw [hX]; simp [Matrix.det_fin_two_of])
  refine ⟨⟨g, hgU⟩, ?_⟩
  funext a
  obtain rfl : a = 0 := Subsingleton.elim _ _
  exact hgX 0

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep.WittOne
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.Basic

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf
open GlobalTheory.CompanionTheory.SW.ThetaStage

theorem linearIndependent_mulVec_GL {E : Type} [Field E] {M n : ℕ} (A : GL (Fin M) E)
    {X : Fin n → Fin M → E} (hX : LinearIndependent E X) :
    LinearIndependent E (fun a => (A : Matrix (Fin M) (Fin M) E) *ᵥ X a) := by
  have hinj : Function.Injective (Matrix.mulVecLin (A : Matrix (Fin M) (Fin M) E)) := by
    intro x y hxy
    have h : ∀ v : Fin M → E, ((A⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) *ᵥ
        ((A : Matrix (Fin M) (Fin M) E) *ᵥ v) = v := by
      intro v
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    have hxy' : (A : Matrix (Fin M) (Fin M) E) *ᵥ x = (A : Matrix (Fin M) (Fin M) E) *ᵥ y := hxy
    rw [← h x, ← h y, hxy']
  exact hX.map' (Matrix.mulVecLin (A : Matrix (Fin M) (Fin M) E)) (LinearMap.ker_eq_bot.2 hinj)

theorem gact_mem_framesE {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M n : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (g : UJ (σ : E →+* E) J) {T : Matrix (Fin n) (Fin n) E}
    {q : Fin n → Fin M → E} (hq : q ∈ framesE σ J T) : gact σ g q ∈ framesE σ J T := by
  have h1 : LinearIndependent E (gact σ g q) := linearIndependent_mulVec_GL (g : GL (Fin M) E) hq.1
  have h2 : gramE σ J (gact σ g q) = T := by
    rw [gramE_gact]
    exact hq.2
  exact ⟨h1, h2⟩

theorem hypOne_basic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → IsHermND σ (hypOne J) ∧ e0 E M ∈ framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) ∧ ∀ (g : UJ (σ : E →+* E) (hypOne J)) (q : Fin 1 → Fin (M + 2) → E), q ∈ framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) → gact σ g q ∈ framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) := by
  intro F E _ _ _ _ _ σ _ M J hJ
  exact ⟨isHermND_hypOne σ hJ, e0_mem_framesE σ J, fun g q hq => gact_mem_framesE σ g hq⟩

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.Basic
end
end

section

noncomputable section

open GlobalTheory.SmGL ValuativeRel

namespace GlobalTheory.CompanionTheory.ExtCharU

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pw_add {n : ℕ} (ξ : Fin n → ℂˣ) (x y : Fin n → ℤ) :
    GlobalTheory.BCT.pw ξ (x + y) = GlobalTheory.BCT.pw ξ x * GlobalTheory.BCT.pw ξ y := by
  simp only [GlobalTheory.BCT.pw, Pi.add_apply, zpow_add, Units.val_mul, Finset.prod_mul_distrib]

theorem pw_ne_zero {n : ℕ} (ξ : Fin n → ℂˣ) (x : Fin n → ℤ) : GlobalTheory.BCT.pw ξ x ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun i _ => Units.ne_zero _

def dg {n : ℕ} (ϖ : kˣ) (e : Fin n → ℤ) : Fin n → kˣ := fun i => ϖ ^ e i

theorem dg_add {n : ℕ} (ϖ : kˣ) (x y : Fin n → ℤ) : dg ϖ (x + y) = dg ϖ x * dg ϖ y := by
  funext i; simp [dg, zpow_add]

theorem ord_zpow (ϖ : kˣ) (m : ℤ) : ord k (ϖ ^ m) = m * ord k ϖ := by
  let o : kˣ →* Multiplicative ℤ := MonoidHom.mk' (fun x => .ofAdd (ord k x)) fun x y => by
    rw [ord_mul, ofAdd_add]
  have h := map_zpow o ϖ m
  have h2 : ord k (ϖ ^ m) = m • ord k ϖ := by
    have := congrArg Multiplicative.toAdd h
    simpa [o] using this
  simpa using h2

def rr (n : ℕ) : Fin n → ℤ := fun i => (n : ℤ) - 1 - (i : ℕ)

theorem rr_anti (n : ℕ) : StrictAnti (rr n) := fun i j h => by
  have : (i : ℕ) < j := h
  simp only [rr]; omega

theorem rr_smul_anti (n : ℕ) {N : ℤ} (hN : 0 < N) : StrictAnti (N • rr n) := fun i j h => by
  have := rr_anti n h
  simp only [Pi.smul_apply, smul_eq_mul]
  exact mul_lt_mul_of_pos_left this hN

theorem add_anti {n : ℕ} (e : Fin n → ℤ) :
    ∃ N : ℤ, 0 < N ∧ StrictAnti (e + N • rr n) := by
  refine ⟨1 + 2 * ∑ i, |e i|, by positivity, fun i j h => ?_⟩
  have hij : (i : ℕ) < j := h
  have hi : |e i| ≤ ∑ l, |e l| :=
    Finset.single_le_sum (f := fun l => |e l|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have hj : |e j| ≤ ∑ l, |e l| :=
    Finset.single_le_sum (f := fun l => |e l|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
  have h1 := abs_le.1 (le_refl |e i|)
  have h2 := abs_le.1 (le_refl |e j|)
  set S := ∑ l, |e l|
  have hd : (1 : ℤ) ≤ rr n i - rr n j := by simp only [rr]; omega
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  nlinarith

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem const_eq_one (R : Representation ℂ (Fin n → kˣ) M) {z : M} {ϖ : kˣ} {ξ : Fin n → ℂˣ} {c : ℂ}
    (hz : z ≠ 0)
    (hx : ∀ x : Fin n → ℤ, StrictAnti x → R (fun i => ϖ ^ x i) z = (c * GlobalTheory.BCT.pw ξ x) • z) :
    c = 1 := by
  have hr := hx (rr n) (rr_anti n)
  have h2 := hx (rr n + rr n) (by
    simpa [two_smul] using rr_smul_anti n (N := 2) (by norm_num))
  have hd : (fun i => ϖ ^ (rr n + rr n) i) = (fun i => ϖ ^ rr n i) * (fun i => ϖ ^ rr n i) :=
    dg_add ϖ (rr n) (rr n)
  rw [hd, map_mul, Module.End.mul_apply, hr, map_smul, hr, smul_smul, pw_add] at h2
  set p := GlobalTheory.BCT.pw ξ (rr n)
  have hp : p ≠ 0 := pw_ne_zero ξ _
  have h3 : c * p * (c * p) = c * (p * p) := smul_left_injective ℂ hz h2
  have hc : c ≠ 0 := by
    rintro rfl
    apply hz
    have h4 : R (fun i => ϖ ^ rr n i) z = 0 := by simpa using hr
    have h5 := congrArg (R (fun i => ϖ ^ rr n i)⁻¹) h4
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, map_zero] at h5
    simpa using h5
  have hpp : p * p ≠ 0 := mul_ne_zero hp hp
  apply mul_left_cancel₀ (mul_ne_zero hc hpp)
  linear_combination h3

theorem eig_all (R : Representation ℂ (Fin n → kˣ) M) {z : M} {ϖ : kˣ} {ξ : Fin n → ℂˣ}
    (hx : ∀ x : Fin n → ℤ, StrictAnti x → R (fun i => ϖ ^ x i) z = GlobalTheory.BCT.pw ξ x • z)
    (e : Fin n → ℤ) : R (dg ϖ e) z = GlobalTheory.BCT.pw ξ e • z := by
  obtain ⟨N, hN, ha⟩ := add_anti e
  have hy := hx _ (rr_smul_anti n hN)
  have hxy := hx _ ha
  have hd : (fun i => ϖ ^ (e + N • rr n) i) = dg ϖ e * (fun i => ϖ ^ (N • rr n) i) :=
    dg_add ϖ e _
  rw [hd, map_mul, Module.End.mul_apply, hy, map_smul, pw_add, mul_comm, mul_smul] at hxy
  exact smul_right_injective M (pw_ne_zero ξ (N • rr n)) hxy

theorem extChar : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (R : Representation ℂ (Fin n → kˣ) M) (z : M) (ϖ : kˣ) (ξ : Fin n → ℂˣ) (c : ℂ),
    z ≠ 0 → ord k ϖ = 1 → (∀ t ∈ torusO k (Fin n), R t z = z) →
    (∀ x : Fin n → ℤ, StrictAnti x → R (fun i => ϖ ^ x i) z = (c * GlobalTheory.BCT.pw ξ x) • z) →
    ∀ t : Fin n → kˣ,
      R t z = (((_root_.GlobalTheory.SmGL.torusChar fun i => unrChar k (ξ i)) t : ℂˣ) : ℂ) • z := by
  intro k _ _ _ _ n M _ _ R z ϖ ξ c hz hϖ hO hx t
  have hc : c = 1 := const_eq_one R hz hx
  subst hc
  simp only [one_mul] at hx
  set e : Fin n → ℤ := fun i => ord k (t i) with he
  have hu : t * (dg ϖ e)⁻¹ ∈ torusO k (Fin n) := by
    intro i
    apply ord_eq_zero_iff.1
    have h1 : ord k (t i * (ϖ ^ e i)⁻¹) = 0 := by
      have h2 := ord_mul k (t i * (ϖ ^ e i)⁻¹) (ϖ ^ e i)
      rw [inv_mul_cancel_right, ord_zpow, hϖ, mul_one] at h2
      have h3 : e i = ord k (t i) := rfl
      omega
    simpa [dg] using h1
  have ht : t = dg ϖ e * (t * (dg ϖ e)⁻¹) := by simp
  have h1 : R t z = R (dg ϖ e) z := by
    conv_lhs => rw [ht]
    rw [map_mul, Module.End.mul_apply, hO _ hu]
  rw [h1, eig_all R hx e, _root_.GlobalTheory.SmGL.torusChar_apply]
  congr 1
  simp [GlobalTheory.BCT.pw, he, unrChar_apply]

end GlobalTheory.CompanionTheory.ExtCharU
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.HintLevel

theorem finsum_out_of_le {H : Type} [Group H] {L S : Subgroup H} (u : H → ℂ) (hLS : L ≤ S)
    (hS : S ≤ rStab u) (hm : L.relIndex S ≠ 0) :
    ∑ᶠ q : H ⧸ L, u q.out = ((L.relIndex S : ℕ) : ℂ) * ∑ᶠ c : H ⧸ S, u c.out := by
  have hm' : Nat.card (S ⧸ L.subgroupOf S) ≠ 0 := hm
  haveI : Finite (S ⧸ L.subgroupOf S) := Nat.finite_of_card_ne_zero hm'
  let e := Subgroup.quotientEquivProdOfLE hLS
  have hfst : ∀ q : H ⧸ L, (e q).1 = ((q.out : H) : H ⧸ S) := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    have h1 : (e (g : H ⧸ L)).1 = (g : H ⧸ S) := rfl
    rw [h1]
    exact QuotientGroup.eq.2 (hLS (QuotientGroup.eq.1 (QuotientGroup.out_eq' (g : H ⧸ L)).symm))
  have hg : ∀ q : H ⧸ L, u q.out = u (e q).1.out := by
    intro q
    rw [hfst q]
    have hk : (((q.out : H) : H ⧸ S).out)⁻¹ * q.out ∈ S :=
      QuotientGroup.eq.1 (QuotientGroup.out_eq' ((q.out : H) : H ⧸ S))
    have := hS hk (((q.out : H) : H ⧸ S).out)
    simpa using this
  have hcomp : ∑ᶠ q : H ⧸ L, u q.out =
      ∑ᶠ p : (H ⧸ S) × (S ⧸ L.subgroupOf S), u p.1.out := by
    rw [← finsum_comp_equiv e]
    exact finsum_congr hg
  rw [hcomp]
  by_cases hfin : (Function.support fun c : H ⧸ S => u c.out).Finite
  · have hsupp : (Function.support fun p : (H ⧸ S) × (S ⧸ L.subgroupOf S) => u p.1.out).Finite := by
      refine (hfin.prod (Set.finite_univ (α := S ⧸ L.subgroupOf S))).subset ?_
      intro p hp
      exact ⟨hp, Set.mem_univ _⟩
    rw [finsum_curry _ hsupp]
    have hin : ∀ c : H ⧸ S, ∑ᶠ _ : S ⧸ L.subgroupOf S, u c.out = ((L.relIndex S : ℕ) : ℂ) * u c.out := by
      intro c
      haveI := Fintype.ofFinite (S ⧸ L.subgroupOf S)
      rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        ← Nat.card_eq_fintype_card]
      rfl
    simp only [hin]
    rw [mul_finsum]
  · have h0 : ∑ᶠ c : H ⧸ S, u c.out = 0 := finsum_of_infinite_support hfin
    rw [h0, mul_zero]
    refine finsum_of_infinite_support fun hsupp => hfin ?_
    refine (hsupp.image Prod.fst).subset ?_
    intro c hc
    exact ⟨(c, ((1 : S) : S ⧸ L.subgroupOf S)), hc, rfl⟩

theorem hint_eq_level : ∀ (H : Type) [Group H] (K L : Subgroup H) (u : H → ℂ), L ≤ K → L ≤ rStab u →
    L.relIndex K ≠ 0 → hint K u = ((L.relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ q : H ⧸ L, u q.out := by
  intro H _ K L u hLK hLu hfin
  have hLS : L ≤ rStab u ⊓ K := le_inf hLu hLK
  have hmul := Subgroup.relIndex_mul_relIndex L (rStab u ⊓ K) K hLS inf_le_right
  have hm : L.relIndex (rStab u ⊓ K) ≠ 0 := fun h0 => hfin (by rw [← hmul, h0, zero_mul])
  rw [finsum_out_of_le u hLS inf_le_left hm, ← hmul, hint]
  have hmC : ((L.relIndex (rStab u ⊓ K) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hm
  rw [Nat.cast_mul, mul_inv, mul_mul_mul_comm, inv_mul_cancel₀ hmC, one_mul]

end GlobalTheory.CompanionTheory.HintLevel
end
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BCT ValuativeRel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.ParabBlock

theorem parab_eq_blk : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (p : parab (w.adicCompletion E) (two (stdSum h))), ∃ X, (p : GLw n w) = GlobalTheory.BCT.blk h w ((leviTwo (w.adicCompletion E) (Fin a) (Fin b)).symm (leviProj (w.adicCompletion E) (two (stdSum h)) p)) X := by
  intro E _ _ _ n a b h w p
  obtain ⟨m, hm⟩ : ∃ m, m = (leviTwo (w.adicCompletion E) (Fin a) (Fin b)).symm
      (leviProj (w.adicCompletion E) (two (stdSum h)) p) := ⟨_, rfl⟩
  have h1 : ∀ i j, (m.1 : Matrix _ _ (w.adicCompletion E)) i j =
      ((p : GLw n w) : Matrix _ _ (w.adicCompletion E)) (stdSum h (Sum.inl i)) (stdSum h (Sum.inl j)) := by
    intro i j; rw [hm]; rfl
  have h2 : ∀ i j, (m.2 : Matrix _ _ (w.adicCompletion E)) i j =
      ((p : GLw n w) : Matrix _ _ (w.adicCompletion E)) (stdSum h (Sum.inr i)) (stdSum h (Sum.inr j)) := by
    intro i j; rw [hm]; rfl
  have h0 : ∀ (i : Fin b) (j : Fin a),
      ((p : GLw n w) : Matrix _ _ (w.adicCompletion E)) (stdSum h (Sum.inr i)) (stdSum h (Sum.inl j)) = 0 := by
    intro i j
    exact mem_parab_iff.1 p.2 true false i j (by decide)
  rw [← hm]
  let B : Matrix (Fin a) (Fin b) (w.adicCompletion E) := fun i j =>
    ((p : GLw n w) : Matrix _ _ (w.adicCompletion E)) (stdSum h (Sum.inl i)) (stdSum h (Sum.inr j))
  refine ⟨(m.1⁻¹).val * B, ?_⟩
  have hM : Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
      (Matrix.fromBlocks m.1.val (m.1.val * ((m.1⁻¹).val * B)) 0 m.2.val) =
      ((p : GLw n w) : Matrix _ _ (w.adicCompletion E)) := by
    have hc : m.1.val * ((m.1⁻¹).val * B) = B := by
      rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
    rw [hc]
    refine Matrix.ext fun i j => ?_
    obtain ⟨i, rfl⟩ := (stdSum h).surjective i
    obtain ⟨j, rfl⟩ := (stdSum h).surjective j
    have hs : finSumFinEquiv.trans (finCongr h) = stdSum h := rfl
    rw [hs]
    rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rcases i with i | i <;> rcases j with j | j
    · exact h1 i j
    · rfl
    · exact (h0 i j).symm
    · exact h2 i j
  have hU : IsUnit (Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
      (Matrix.fromBlocks m.1.val (m.1.val * ((m.1⁻¹).val * B)) 0 m.2.val)) := by
    rw [hM]; exact (p : GLw n w).isUnit
  unfold GlobalTheory.BCT.blk
  simp only
  rw [dite_eq_left hU]
  exact Units.ext (by rw [IsUnit.unit_spec, hM])

end GlobalTheory.CompanionTheory.ParabBlock
end

section

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)

theorem _root_.GlobalTheory.T.arithmetic_variety_generically_etale_coordinates : ∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℤ) (D : ℕ), GlobalTheory.IsArithVar p D →
    ∃ (U : X.Opens) (x : Fin D → Γ(X, U)), IsAffineOpen U ∧ genericPoint X ∈ U ∧
      (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U) x).Etale := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.GenericCoords.exists_etale_coords_int | exact GlobalTheory.CompanionTheory.MixZ.GenericCoords.exists_etale_coords_int | (intros; apply GlobalTheory.CompanionTheory.MixZ.GenericCoords.exists_etale_coords_int <;> assumption)
end
