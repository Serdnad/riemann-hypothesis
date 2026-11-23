module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle077
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle073
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle078
public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle224
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle231
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundedOrbitHasNearbyFixedPoint
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodDiscExtensionTateElement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOpenDiscConvergentRingWithExpansions
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle230
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachExpansionLatticeFullDescends
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachExpansionLatticeGradedOfLevelLe
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLevelExpansionAtRootOfUnity
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Order.Interval.Finset.Box
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP

@[expose] public section

section

noncomputable section

open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.SenLines GlobalTheory.IndefiniteRowSideFullHecke.DiagonalQuotientEigen

namespace GlobalTheory.SenLines.Coords

variable {F M : Type} [Field F] [AddCommGroup M] [Module F M]

def zc (c : F⟦X⟧) (n : ℤ) : F := if 0 ≤ n then coeff n.toNat c else 0

theorem zc_nat (c : F⟦X⟧) (n : ℕ) : zc c n = coeff n c := by
  simp [zc]

theorem zc_neg (c : F⟦X⟧) {n : ℤ} (h : n < 0) : zc c n = 0 := by
  unfold zc
  rw [if_neg (not_le.mpr h)]

theorem zc_add (c c' : F⟦X⟧) (n : ℤ) : zc (c + c') n = zc c n + zc c' n := by
  unfold zc
  split_ifs <;> simp [map_add (f := _)]

theorem zc_mul (f c : F⟦X⟧) (n : ℤ) (N : ℕ) (h : n < N) :
    zc (f * c) n = ∑ j ∈ Finset.range N, coeff j f * zc c (n - j) := by
  rcases lt_or_ge n 0 with hn | hn
  · rw [zc_neg _ hn]
    symm
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [zc_neg _ (by omega), mul_zero]
  · lift n to ℕ using hn
    have hN : n < N := by exact_mod_cast h
    rw [zc_nat, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i f * coeff j c),
      ← Finset.sum_range_add_sum_Ico _ (show n + 1 ≤ N by omega)]
    rw [Finset.sum_eq_zero (s := Finset.Ico (n + 1) N) ?_, add_zero]
    · refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_range] at hj
      rw [show ((n : ℤ) - (j : ℤ)) = ((n - j : ℕ) : ℤ) by omega, zc_nat]
    · intro j hj
      rw [Finset.mem_Ico] at hj
      rw [zc_neg _ (by omega), mul_zero]

def lines {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M) (c : Fin r → F⟦X⟧) : ℤ → M :=
  ∑ k, serLine (u k) (d k) (c k)

theorem lines_apply {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M) (c : Fin r → F⟦X⟧) (m : ℤ) :
    lines u d c m = ∑ k, zc (c k) (m + u k) • d k := by
  unfold lines
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [serLine, zc]
  split_ifs <;> simp

theorem lines_add {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M) (c c' : Fin r → F⟦X⟧) :
    lines u d (c + c') = lines u d c + lines u d c' := by
  funext m
  simp only [lines_apply, Pi.add_apply, zc_add, add_smul, Finset.sum_add_distrib]

theorem lines_zero {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M) :
    lines u d (0 : Fin r → F⟦X⟧) = 0 := by
  funext m
  rw [lines_apply, Pi.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  have : zc (0 : F⟦X⟧) (m + u k) = 0 := by
    unfold zc
    split_ifs <;> simp
  rw [Pi.zero_apply, this, zero_smul]

theorem lines_sum {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M) {ι : Type} (s : Finset ι)
    (c : ι → Fin r → F⟦X⟧) : lines u d (∑ j ∈ s, c j) = ∑ j ∈ s, lines u d (c j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, lines_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, lines_add, ih]

theorem coeff_eq_of_apply {r : ℕ} (u : Fin r → ℤ) {d : Fin r → M} (hd : LinearIndependent F d)
    (c c' : Fin r → F⟦X⟧) (a : F) (m : ℤ) (h : lines u d c m = a • lines u d c' m) (k : Fin r) :
    zc (c k) (m + u k) = a * zc (c' k) (m + u k) := by
  rw [lines_apply, lines_apply, Finset.smul_sum] at h
  have h2 : ∑ k, (zc (c k) (m + u k) - a * zc (c' k) (m + u k)) • d k = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, mul_smul]
    rw [h, sub_self]
  exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hd _ h2 k)

theorem lines_injective {r : ℕ} (u : Fin r → ℤ) {d : Fin r → M} (hd : LinearIndependent F d) :
    Function.Injective (lines (F := F) u d) := by
  intro c c' h
  funext k
  ext n
  have := coeff_eq_of_apply u hd c c' 1 ((n : ℤ) - u k) (by rw [h, one_smul]) k
  rwa [sub_add_cancel, one_mul, zc_nat, zc_nat] at this

theorem serAct_lines {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M) (f : F⟦X⟧) (c : Fin r → F⟦X⟧) :
    serAct f (lines u d c) = lines u d (f • c) := by
  funext m
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ k, m + u k < N := by
    refine ⟨(Finset.univ.sup fun k => (m + u k).toNat) + 1, fun k => ?_⟩
    have h1 : (m + u k).toNat ≤ Finset.univ.sup fun k => (m + u k).toNat :=
      Finset.le_sup (f := fun k => (m + u k).toNat) (Finset.mem_univ k)
    have h2 := Int.self_le_toNat (m + u k)
    push_cast
    omega
  have hsupp : (Function.support fun j : ℕ => coeff j f • lines u d c (m - j)) ⊆ ↑(Finset.range N) := by
    intro j hj
    rw [Function.mem_support] at hj
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hjN
    apply hj
    rw [lines_apply, Finset.sum_eq_zero, smul_zero]
    intro k _
    rw [zc_neg _ (by have := hN k; omega), zero_smul]
  unfold serAct
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  simp_rw [lines_apply, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [zc_mul f (c k) (m + u k) N (hN k), Finset.sum_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show m - (j : ℤ) + u k = m + u k - j by ring]

theorem exists_coords : ∀ {F M A N : Type} [Field F] [AddCommGroup M] [Module F M] [CommRing A] [AddCommGroup N] [Module A N] (lev : A → F⟦X⟧) (L : N →+ (ℤ → M)) {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M), LinearIndependent F d → (∀ a x, L (a • x) = serAct (lev a) (L x)) → SpanIsLines L u d F → ∃ e : N →+ (Fin r → F⟦X⟧), (∀ a x, e (a • x) = lev a • e x) ∧ Submodule.span F⟦X⟧ (Set.range e) = ⊤ ∧ ∀ (χ : F) (x y : N), χ ≠ 0 → (∀ k : ℤ, L y k = χ ^ k • L x k) → ∀ k, e y k = C (χ ^ (-u k)) * rescale χ (e x k) := by
  intro F M A N _ _ _ _ _ _ lev L r u d hd hL hS
  have hex : ∀ x, ∃ c : Fin r → F⟦X⟧, L x = lines u d c := by
    intro x
    obtain ⟨c, hc⟩ := (hS (L x)).mp ⟨1, fun _ => x, fun _ => 1, by simp only [Fin.sum_univ_one, serAct_one]⟩
    exact ⟨c, hc⟩
  choose e he using hex
  have hinj := lines_injective (F := F) u hd
  have eadd : ∀ x y, e (x + y) = e x + e y := fun x y =>
    hinj (by rw [← he, lines_add, ← he, ← he, map_add (f := _)])
  refine ⟨AddMonoidHom.mk' e eadd, ?_, ?_, ?_⟩
  · intro a x
    show e (a • x) = lev a • e x
    apply hinj
    rw [← he, hL, he x, serAct_lines]
  · rw [eq_top_iff]
    intro c _
    obtain ⟨s, x, f, hy⟩ := (hS (lines u d c)).mpr ⟨c, rfl⟩
    have hc : c = ∑ j, f j • e (x j) := by
      apply hinj
      rw [hy, lines_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [he, serAct_lines]
    rw [hc]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨x j, rfl⟩)
  · intro χ x y hχ hxy k
    show e y k = C (χ ^ (-u k)) * rescale χ (e x k)
    ext n
    have h1 : lines u d (e y) ((n : ℤ) - u k) = χ ^ ((n : ℤ) - u k) • lines u d (e x) ((n : ℤ) - u k) := by
      rw [← he, ← he]
      exact hxy _
    have h2 := coeff_eq_of_apply u hd (e y) (e x) _ _ h1 k
    rw [sub_add_cancel, zc_nat, zc_nat] at h2
    rw [h2, PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale, zpow_sub₀ hχ, zpow_neg, zpow_natCast]
    ring

end GlobalTheory.SenLines.Coords
end
end

section

open Matrix Polynomial

namespace GlobalTheory.IntConj

section Krylov

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem mul_krylov_of_semiconj {M M' x : Matrix n n A} (h : x * M' = M * x) (w : n → A) :
    x * GlobalTheory.RegSS.krylov M' w = GlobalTheory.RegSS.krylov M (x *ᵥ w) := by
  ext i j
  have hk : ∀ k : ℕ, x * M' ^ k = M ^ k * x := fun k => SemiconjBy.pow_right h k
  calc (x * GlobalTheory.RegSS.krylov M' w) i j
      = (x *ᵥ ((M' ^ ((Fintype.equivFin n j : Fin (Fintype.card n)) : ℕ)) *ᵥ w)) i := by
        simp [GlobalTheory.RegSS.krylov, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    _ = ((M ^ ((Fintype.equivFin n j : Fin (Fintype.card n)) : ℕ)) *ᵥ (x *ᵥ w)) i := by
        rw [mulVec_mulVec, hk, ← mulVec_mulVec]
    _ = GlobalTheory.RegSS.krylov M (x *ᵥ w) i j := by simp [GlobalTheory.RegSS.krylov]

end Krylov

theorem mem_unitBall {E : Type} [NormedField E] [IsUltrametricDist E] (y : E) :
    y ∈ (NormedField.valuation (K := E)).valuationSubring ↔ ‖y‖ ≤ 1 := by
  rw [Valuation.mem_valuationSubring_iff, NormedField.valuation_apply, ← NNReal.coe_le_coe]
  simp

theorem norm_eq_one_of_isUnit {E : Type} [NormedField E] [IsUltrametricDist E]
    {a : (NormedField.valuation (K := E)).valuationSubring} (ha : IsUnit a) : ‖(a : E)‖ = 1 := by
  obtain ⟨u, rfl⟩ := ha
  have h := congrArg (fun y : (NormedField.valuation (K := E)).valuationSubring => ‖(y : E)‖) u.mul_inv
  simp only [MulMemClass.coe_mul, norm_mul, OneMemClass.coe_one, norm_one] at h
  have h1 : ‖((u : (NormedField.valuation (K := E)).valuationSubring) : E)‖ ≤ 1 :=
    (mem_unitBall _).1 (u : (NormedField.valuation (K := E)).valuationSubring).2
  have h2 : ‖(((u⁻¹ : _ˣ) : (NormedField.valuation (K := E)).valuationSubring) : E)‖ ≤ 1 :=
    (mem_unitBall _).1 ((u⁻¹ : _ˣ) : (NormedField.valuation (K := E)).valuationSubring).2
  nlinarith [norm_nonneg ((u : (NormedField.valuation (K := E)).valuationSubring) : E),
    norm_nonneg (((u⁻¹ : _ˣ) : (NormedField.valuation (K := E)).valuationSubring) : E)]

end GlobalTheory.IntConj

namespace GlobalTheory.IntConj

theorem exists_commuting_mul_integral (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E]
    (n : ℕ) (N x : Matrix (Fin n) (Fin n) E) (hN : ∀ i j, ‖N i j‖ ≤ 1)
    (hsep : ∃ u v : Polynomial E, (∀ i, ‖u.coeff i‖ ≤ 1) ∧ (∀ i, ‖v.coeff i‖ ≤ 1) ∧
      u * N.charpoly + v * Polynomial.derivative N.charpoly = 1)
    (hx : IsUnit x) (hN' : ∀ i j, ‖(x⁻¹ * N * x) i j‖ ≤ 1) :
    ∃ c : Matrix (Fin n) (Fin n) E, IsUnit c ∧ c * N = N * c ∧ (∀ i j, ‖(c⁻¹ * x) i j‖ ≤ 1) ∧
      ‖(c⁻¹ * x).det‖ = 1 := by
  classical
  let O := (NormedField.valuation (K := E)).valuationSubring
  let φ : O →+* E := O.subtype
  have hφ : Function.Injective φ := Subtype.val_injective
  have lift : ∀ M : Matrix (Fin n) (Fin n) E, (∀ i j, ‖M i j‖ ≤ 1) →
      ∃ M₀ : Matrix (Fin n) (Fin n) O, M₀.map φ = M := fun M hM =>
    ⟨Matrix.of fun i j => ⟨M i j, (mem_unitBall _).2 (hM i j)⟩, by ext i j; rfl⟩
  have liftP : ∀ p : E[X], (∀ i, ‖p.coeff i‖ ≤ 1) → ∃ p₀ : O[X], p₀.map φ = p := by
    intro p hp
    have : p ∈ Polynomial.lifts φ :=
      (lifts_iff_coeff_lifts p).2 fun k => ⟨⟨_, (mem_unitBall _).2 (hp k)⟩, rfl⟩
    exact (mem_lifts p).1 this
  obtain ⟨u, v, hu, hv, huv⟩ := hsep
  obtain ⟨u₀, rfl⟩ := liftP u hu
  obtain ⟨v₀, rfl⟩ := liftP v hv
  have sep : ∀ M₀ : Matrix (Fin n) (Fin n) O, (M₀.map φ).charpoly = N.charpoly →
      M₀.charpoly.Separable := by
    intro M₀ hM
    refine ⟨u₀, v₀, ?_⟩
    apply Polynomial.map_injective φ hφ
    rw [Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.map_mul, ← Polynomial.derivative_map,
      ← Matrix.charpoly_map, hM, Polynomial.map_one]
    exact huv
  obtain ⟨X, rfl⟩ := hx
  have hXd : IsUnit (X : Matrix (Fin n) (Fin n) E).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 X.isUnit
  have hcp : ((X : Matrix (Fin n) (Fin n) E)⁻¹ * N * (X : Matrix (Fin n) (Fin n) E)).charpoly = N.charpoly := by
    exact Matrix.charpoly_units_conj' X N
  obtain ⟨N₀, hN₀⟩ := lift N hN
  obtain ⟨N₀', hN₀'⟩ := lift _ hN'
  obtain ⟨v₁, hv₁⟩ := GlobalTheory.RegSS.Semilocal.cyclicSemilocal_of_cyclicField GlobalTheory.RegSS.cyclicField
    O (Fin n) N₀ (sep N₀ (by rw [hN₀]))
  obtain ⟨w₁, hw₁⟩ := GlobalTheory.RegSS.Semilocal.cyclicSemilocal_of_cyclicField GlobalTheory.RegSS.cyclicField
    O (Fin n) N₀' (sep N₀' (by rw [hN₀', hcp]))
  have hK : (GlobalTheory.RegSS.krylov N₀ v₁).map φ = GlobalTheory.RegSS.krylov N (φ ∘ v₁) := by
    rw [GlobalTheory.RegSS.Semilocal.krylov_map_ringHom, hN₀]
  have hK' : (GlobalTheory.RegSS.krylov N₀' w₁).map φ =
      GlobalTheory.RegSS.krylov ((X : Matrix (Fin n) (Fin n) E)⁻¹ * N * (X : Matrix (Fin n) (Fin n) E)) (φ ∘ w₁) := by
    rw [GlobalTheory.RegSS.Semilocal.krylov_map_ringHom, hN₀']
  have hKu := GlobalTheory.RegSS.isUnit_det_map φ hv₁
  have hKu' := GlobalTheory.RegSS.isUnit_det_map φ hw₁
  obtain ⟨-, -, hbij⟩ := GlobalTheory.RegSS.CycAlg.cyclicAlgebra E (Fin n) N (φ ∘ v₁) (by rw [← hK]; exact hKu)
  obtain ⟨l, hl⟩ := hbij.2 ((X : Matrix (Fin n) (Fin n) E) *ᵥ (φ ∘ w₁))
  simp only at hl
  have hcN : N * (l : Matrix (Fin n) (Fin n) E) = l * N := GlobalTheory.RegSS.commute_of_mem_genAlg rfl l.2
  have hXN : (X : Matrix (Fin n) (Fin n) E) * ((X : Matrix (Fin n) (Fin n) E)⁻¹ * N * (X : Matrix (Fin n) (Fin n) E)) = N * X := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hXd, Matrix.one_mul]
  have key : (l : Matrix (Fin n) (Fin n) E) * (GlobalTheory.RegSS.krylov N₀ v₁).map φ =
      (X : Matrix (Fin n) (Fin n) E) * (GlobalTheory.RegSS.krylov N₀' w₁).map φ := by
    rw [hK, hK', mul_krylov_of_semiconj hcN.symm, mul_krylov_of_semiconj hXN, hl]
  set Kv := (GlobalTheory.RegSS.krylov N₀ v₁).map φ with hKv
  set Kw := (GlobalTheory.RegSS.krylov N₀' w₁).map φ with hKw
  generalize (l : Matrix (Fin n) (Fin n) E) = c at key hcN
  have hcu : IsUnit c := by
    have : c = (X : Matrix (Fin n) (Fin n) E) * Kw * Kv⁻¹ := by
      rw [← key, Matrix.mul_nonsing_inv_cancel_right _ _ hKu]
    rw [this]
    exact (X.isUnit.mul ((Matrix.isUnit_iff_isUnit_det _).2 hKu')).mul
      ((Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_nonsing_inv_det _ hKu))
  have hcd : IsUnit c.det := (Matrix.isUnit_iff_isUnit_det _).1 hcu
  have e2 : c⁻¹ * (X : Matrix (Fin n) (Fin n) E) = Kv * Kw⁻¹ := by
    rw [← Matrix.mul_nonsing_inv_cancel_right _ (c⁻¹ * (X : Matrix (Fin n) (Fin n) E)) hKu',
      Matrix.mul_assoc c⁻¹, ← key, Matrix.nonsing_inv_mul_cancel_left _ _ hcd]
  have hinv : Kw⁻¹ = ((GlobalTheory.RegSS.krylov N₀' w₁)⁻¹).map φ := by
    refine Matrix.inv_eq_left_inv ?_
    rw [hKw, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← map_mul,
      Matrix.nonsing_inv_mul _ hw₁, map_one]
  have e3 : c⁻¹ * (X : Matrix (Fin n) (Fin n) E) =
      (GlobalTheory.RegSS.krylov N₀ v₁ * (GlobalTheory.RegSS.krylov N₀' w₁)⁻¹).map φ := by
    rw [e2, hinv, hKv, Matrix.map_mul]
  refine ⟨c, hcu, hcN.symm, fun i j => ?_, ?_⟩
  · rw [e3]; exact (mem_unitBall _).1 ((GlobalTheory.RegSS.krylov N₀ v₁ * (GlobalTheory.RegSS.krylov N₀' w₁)⁻¹) i j).2
  · rw [e3, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact norm_eq_one_of_isUnit (by
      rw [Matrix.det_mul]; exact hv₁.mul (Matrix.isUnit_nonsing_inv_det _ hw₁))

end GlobalTheory.IntConj
end

section

open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

namespace GlobalTheory.TiltAbs

theorem norm_untilt_sub_eq_one_of_pow_fixed :
    ∀ (l : ℕ) [Fact l.Prime] (o : ℕ) (ζ ζ' : Formalism.Per.Fl l), 0 < o → ζ ^ (l ^ o) = ζ →
      ζ' ^ (l ^ o) = ζ' → ζ ≠ ζ' → ‖(((ζ - ζ').untilt : Formalism.Per.OC l) : ℂ_[l])‖ = 1 := by
  intro l _ o ζ ζ' ho h1 h2 hne
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  set d : Formalism.Per.Fl l := ζ - ζ' with hd
  have hdpow : d ^ (l ^ o) = d := by
    rw [hd, sub_pow_char_pow, h1, h2]
  have hd0 : d ≠ 0 := sub_ne_zero.2 hne
  set a : ℝ := ‖((d.untilt : Formalism.Per.OC l) : ℂ_[l])‖ with ha
  have ha0 : a ≠ 0 := by
    intro h
    apply hd0
    refine (untilt_ultrametric_definite l d 0).2 ?_
    have : ((d.untilt : Formalism.Per.OC l) : ℂ_[l]) = 0 := norm_eq_zero.1 h
    exact Subtype.ext this
  have hapow : a ^ (l ^ o) = a := by
    have := congrArg (fun x : Formalism.Per.Fl l => ‖((x.untilt : Formalism.Per.OC l) : ℂ_[l])‖) hdpow
    simp only [map_pow, SubmonoidClass.coe_pow, norm_pow] at this
    exact this
  have hlo : 1 ≤ l ^ o := Nat.one_le_pow _ _ (by omega)
  have hlo' : l ^ o - 1 ≠ 0 := by
    have : 1 < l ^ o := Nat.one_lt_pow (by omega) hl
    omega
  have hsub : a ^ (l ^ o - 1) = 1 := by
    have : a ^ (l ^ o - 1) * a = 1 * a := by
      rw [← pow_succ, Nat.sub_add_cancel hlo, hapow, one_mul]
    exact mul_right_cancel₀ ha0 this
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hlo').1 hsub

end GlobalTheory.TiltAbs
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.AxLemma

theorem ax_lemma_complete : ∀ (l : ℕ) [Fact l.Prime], ∃ c : ℝ, 0 < c ∧ ∀ (H : Subgroup (GQ l)) (y : ℂ_[l]) (r : ℝ), 0 < r → (∀ g ∈ H, ‖Per.σC g y - y‖ ≤ r) → ∃ z : Om l, (∀ g ∈ H, g z = z) ∧ ‖y - (z : ℂ_[l])‖ ≤ c * r := by
  intro l _
  obtain ⟨c, hc, hax⟩ := ax_lemma l
  refine ⟨c + 1, by linarith, fun H y r hr hy => ?_⟩
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : Om l, ‖y - (y₀ : ℂ_[l])‖ ≤ r := by
    have hd : DenseRange ((↑) : PadicAlgCl l → ℂ_[l]) := UniformSpace.Completion.denseRange_coe
    obtain ⟨b, hb⟩ := Metric.denseRange_iff.1 hd y r hr
    exact ⟨b, by rw [← dist_eq_norm]; exact hb.le⟩
  have hsub : ∀ a b : Om l, ((a - b : Om l) : ℂ_[l]) = (a : ℂ_[l]) - (b : ℂ_[l]) := by
    intro a b
    rw [PadicComplex.coe_eq, map_sub, ← PadicComplex.coe_eq, ← PadicComplex.coe_eq]
  obtain ⟨z, hz, hyz⟩ := hax H y₀ r (fun g hg => by
    rw [← PadicComplex.norm_extends l, hsub, ← GlobalTheory.RingBasics.σC_coe]
    have e : Per.σC g (y₀ : ℂ_[l]) - (y₀ : ℂ_[l])
        = Per.σC g ((y₀ : ℂ_[l]) - y) + ((Per.σC g y - y) + (y - (y₀ : ℂ_[l]))) := by
      rw [map_sub]; ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [GlobalTheory.RingBasics.norm_σC, norm_sub_rev]; exact hy₀
    · exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hy g hg) hy₀))
  refine ⟨z, hz, ?_⟩
  rw [← PadicComplex.norm_extends l, hsub] at hyz
  have e : y - (z : ℂ_[l]) = (y - (y₀ : ℂ_[l])) + ((y₀ : ℂ_[l]) - (z : ℂ_[l])) := by ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  linarith

end GlobalTheory.AxLemma
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.tilt_galois_action_root_of_unity_coprime : ∀ (l : ℕ) [Fact l.Prime] (e : Per.Fl l) (m n : ℕ) (g : GQ l), 0 < m → ¬ l ∣ m → e ^ m = 1 → (∀ x : Om l, x ^ m = 1 → g x = x ^ n) → Per.σF g e = e ^ n := by
  first | exact @GlobalTheory.MemLoc.σF_root_of_unity | exact GlobalTheory.MemLoc.σF_root_of_unity | (intros; apply GlobalTheory.MemLoc.σF_root_of_unity <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.HWL.Cmp

theorem _root_.GlobalTheory.T.exists_openDiscConvergentRing_with_expansions : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∀ β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B, IsBeta AI β → ∀ J, IsEval I β J → (∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1), (∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j)) → ∀ a : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)), IsExp ζ (toLL a i) (R.lev i ζ a)) → (∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (c : ↥(K0 K)), ((1 : ↥LL.1) ⊗ₜ[ℚ_[l]] algebraMap ↥(K0 K) P.R.B c) * β (I.io (letE i)) = Γ.emb i c • β (I.io (letE i))) → ∃ D : Disc R (β.comp I.io.toRingHom) ((((l : ℚ_[l]) ^ s)⁻¹) • P.ιB P.tB) (algebraMap (Om l) P.R.BdR (P.ζQ s)), (∀ a : LetA ↥LL.1 (Module.finrank ℚ_[l] ↥(K0 K)), (∀ i, Conv (a i)) → a ∈ D.C) ∧ (D.t : LetA ↥LL.1 (Module.finrank ℚ_[l] ↥(K0 K))) = fun _ => logS LL := by
  first | exact @GlobalTheory.HWL.Cmp.OpenDisc.exists_disc | exact GlobalTheory.HWL.Cmp.OpenDisc.exists_disc | (intros; apply GlobalTheory.HWL.Cmp.OpenDisc.exists_disc <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

theorem _root_.GlobalTheory.T.wachExpansionLattice_full_descends : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (i : Let K) (ζ : ↥LL.1), (∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j)) → Full (Di (HW l) h T i) (Lat C h T i ζ) → Full (Di (HW l) h T (i - 1)) (Lat C h T (i - 1) (ζ ^ l)) := by
  first | exact @GlobalTheory.NL.FullDown.full_down | exact GlobalTheory.NL.FullDown.full_down | (intros; apply GlobalTheory.NL.FullDown.full_down <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

theorem _root_.GlobalTheory.T.wachExpansionLattice_graded_of_level_le : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (i : Let K) (ζ : ↥LL.1), ζ ^ (l ^ s) = 1 → Full (Di (HW l) h T i) (Lat C h T i ζ) → Graded (Lat C h T i ζ) := by
  first | exact @GlobalTheory.NL.GradedLat.graded_of_level_le | exact GlobalTheory.NL.GradedLat.graded_of_level_le | (intros; apply GlobalTheory.NL.GradedLat.graded_of_level_le <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

theorem _root_.GlobalTheory.T.wachLevel_expansion_at_root_of_unity : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (i : Let K) (ζ : ↥LL.1), (∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j)) → (∃ x : ↥(OL LL), ¬ IsUnit x ∧ (x : ↥LL.1) = ζ - 1 ∧ ∃ w : PowerSeries ↥LL.1, IsUnit w ∧ W.lev i ζ letπ = PowerSeries.C (x : ↥LL.1) + PowerSeries.X * w) ∧ W.lev i ζ (letE i) = 1 ∧ (ζ ^ (l ^ (s - 1)) = 1 → (∃ w : PowerSeries ↥LL.1, IsUnit w ∧ W.lev i ζ W.X = PowerSeries.X * w) ∧ IsUnit (W.lev i ζ W.Q)) ∧ (IsPrimitiveRoot ζ (l ^ s) → (∃ w : PowerSeries ↥LL.1, IsUnit w ∧ W.lev i ζ W.Q = PowerSeries.X * w) ∧ IsUnit (W.lev i ζ W.X)) ∧ (PowerSeries.constantCoeff (W.lev i ζ W.X) = 0 ↔ ζ ^ (l ^ (s - 1)) = 1) ∧ (PowerSeries.constantCoeff (W.lev i ζ W.Q) = 0 ↔ IsPrimitiveRoot ζ (l ^ s)) ∧ W.lev i ζ W.Q ≠ 0 := by
  first | exact @GlobalTheory.NL.lev_at_root_of_unity | exact GlobalTheory.NL.lev_at_root_of_unity | (intros; apply GlobalTheory.NL.lev_at_root_of_unity <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

theorem _root_.GlobalTheory.T.infWt_nodup_and_half_integral : ∀ (D : D7) (i : D.nd.Loc) (P : D.naut.AV i) (τ : D.host.E →+* ℂ), (D.naut.infWt i τ).Nodup ∧ ∀ z ∈ D.naut.infWt i τ, ∃ k : ℤ, z = (k : ℂ) + ((D.R.nV : ℂ) - 1) / 2 := by
  first | exact @GlobalTheory.weight_localisation_regular_algebraic | exact GlobalTheory.weight_localisation_regular_algebraic | (intros; apply GlobalTheory.weight_localisation_regular_algebraic <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.norm_sum_pow_apply_le_and_norm_pow_prime_sub_le : ∀ (l : ℕ) [Fact l.Prime] (σ : GQ l) (S : AddSubgroup (Om l)) (s : ℝ), 0 ≤ s → s ≤ 1 → (∀ x ∈ S, σ x ∈ S) → (∀ x ∈ S, ‖σ x - x‖ ≤ s * ‖x‖) → ∀ x ∈ S, ‖∑ i ∈ Finset.range l, (σ ^ i) x‖ ≤ max (s ^ (l - 1)) ‖((l : ℕ) : Om l)‖ * ‖x‖ ∧ ‖(σ ^ l) x - x‖ ≤ max (s ^ (l - 1)) ‖((l : ℕ) : Om l)‖ * s * ‖x‖ := by
  first | exact @GlobalTheory.MemLoc.norm_geom_sum_galois_le | exact GlobalTheory.MemLoc.norm_geom_sum_galois_le | (intros; apply GlobalTheory.MemLoc.norm_geom_sum_galois_le <;> assumption)
end
