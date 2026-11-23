module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle292
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle269
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle308
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle301
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle302
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation

@[expose] public section

section

open GlobalTheory.GLq GlobalTheory.MirAvg Polynomial

noncomputable section

namespace GlobalTheory.MirAvg

open Matrix

variable {g : ℕ} [Fact g.Prime]

theorem exists_gl_mulVec_single_eq {r : ℕ} (i : Fin r) {a : Fin r → ZMod g} (ha : a ≠ 0) :
    ∃ y : Gn g r, (y : Mt g r) *ᵥ Pi.single i 1 = a := by
  have he : (Pi.single i (1 : ZMod g) : Fin r → ZMod g) ≠ 0 := by
    intro h; have := congrFun h i; simp at this
  let f := (LinearEquiv.toSpanNonzeroSingleton (ZMod g) (Fin r → ZMod g) _ he).symm.trans
    (LinearEquiv.toSpanNonzeroSingleton (ZMod g) (Fin r → ZMod g) a ha)
  obtain ⟨e, hef⟩ := Submodule.exists_linearEquiv_restrict_eq f
  have h1 : e (Pi.single i 1) = a := by
    have := hef ⟨_, Submodule.mem_span_singleton_self _⟩
    rw [← this]
    simp only [f, LinearEquiv.trans_apply]
    rw [← LinearEquiv.toSpanNonzeroSingleton_one (ZMod g) (Fin r → ZMod g) _ he, LinearEquiv.symm_apply_apply,
      LinearEquiv.toSpanNonzeroSingleton_one]
  refine ⟨⟨LinearMap.toMatrix' e.toLinearMap, LinearMap.toMatrix' e.symm.toLinearMap, ?_, ?_⟩, ?_⟩
  · rw [← LinearMap.toMatrix'_comp]; simp
  · rw [← LinearMap.toMatrix'_comp]; simp
  · show LinearMap.toMatrix' e.toLinearMap *ᵥ _ = a
    rw [LinearMap.toMatrix'_mulVec]; exact h1

theorem mirSet_true_conj {r : ℕ} (a : Fin r → ZMod g) (y z : Gn g r) :
    mirSet a true (y * z * y⁻¹) ↔ mirSet ((↑y⁻¹ : Mt g r) *ᵥ a) true z := by
  have hAB : (y : Mt g r) * (↑y⁻¹ : Mt g r) = 1 := y.mul_inv
  have hBA : (↑y⁻¹ : Mt g r) * (y : Mt g r) = 1 := y.inv_mul
  simp only [mirSet, if_true, Units.val_mul]
  constructor
  · intro h x
    obtain ⟨c, hc⟩ := h ((y : Mt g r) *ᵥ x)
    refine ⟨c, ?_⟩
    have := congrArg (fun v => (↑y⁻¹ : Mt g r) *ᵥ v) hc
    simp only [mulVec_sub, mulVec_smul, mulVec_mulVec, ← Matrix.mul_assoc, hBA, Matrix.one_mul] at this
    rw [Matrix.mul_assoc, hBA, Matrix.mul_one, one_mulVec] at this
    exact this
  · intro h x
    obtain ⟨c, hc⟩ := h ((↑y⁻¹ : Mt g r) *ᵥ x)
    refine ⟨c, ?_⟩
    have := congrArg (fun v => (y : Mt g r) *ᵥ v) hc
    simp only [mulVec_sub, mulVec_smul, mulVec_mulVec, ← Matrix.mul_assoc, hAB, Matrix.one_mul, one_mulVec] at this
    rw [← this]

theorem mirSet_false_conj {r : ℕ} (a : Fin r → ZMod g) (y z : Gn g r) :
    mirSet a false (y * z * y⁻¹) ↔ mirSet (a ᵥ* (y : Mt g r)) false z := by
  have hAB : (y : Mt g r) * (↑y⁻¹ : Mt g r) = 1 := y.mul_inv
  have hBA : (↑y⁻¹ : Mt g r) * (y : Mt g r) = 1 := y.inv_mul
  simp only [mirSet, Bool.false_eq_true, if_false, Units.val_mul]
  constructor
  · intro h x hx
    rw [← dotProduct_mulVec] at hx
    have := h _ hx
    have := congrArg (fun v => (↑y⁻¹ : Mt g r) *ᵥ v) this
    simp only [mulVec_mulVec, ← Matrix.mul_assoc, hBA, Matrix.one_mul] at this
    rw [Matrix.mul_assoc, hBA, Matrix.mul_one, one_mulVec] at this
    exact this
  · intro h x hx
    have h2 : (a ᵥ* (y : Mt g r)) ⬝ᵥ ((↑y⁻¹ : Mt g r) *ᵥ x) = 0 := by
      rw [← dotProduct_mulVec, mulVec_mulVec, hAB, one_mulVec]; exact hx
    have := h _ h2
    have := congrArg (fun v => (y : Mt g r) *ᵥ v) this
    simp only [mulVec_mulVec, hAB, one_mulVec] at this
    rw [Matrix.mul_assoc]; exact this

open Classical in
theorem mirEl_coeff {r : ℕ} (θ : (ZMod g)ˣ →* ℂˣ) (a : Fin r → ZMod g) (b : Bool) (x : Gn g r) :
    (mirEl θ a b).coeff x = if mirSet a b x then ((θ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) else 0 := by
  unfold mirEl
  rw [MonoidAlgebra.coeff_sum, Finset.sum_apply', Finset.sum_eq_single x]
  · simp [MonoidAlgebra.coeff_single]
  · intro h _ hne; simp [MonoidAlgebra.coeff_single, Finsupp.single_apply, hne]
  · intro h; exact absurd (Finset.mem_univ x) h

theorem tr_mirEl_conj {r : ℕ} (ψ : Gn g r → ℂ) (hψ : IsClass ψ) (θ : (ZMod g)ˣ →* ℂˣ)
    (a a' : Fin r → ZMod g) (b : Bool) (y : Gn g r) (H : ∀ z, mirSet a b (y * z * y⁻¹) ↔ mirSet a' b z) :
    tr (mirEl θ a b) ψ = tr (mirEl θ a' b) ψ := by
  classical
  unfold tr
  simp only [mirEl_coeff]
  rw [← Equiv.sum_comp (MulAut.conj y).toEquiv]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
  have hd : Matrix.GeneralLinearGroup.det (y * z * y⁻¹) = Matrix.GeneralLinearGroup.det z := by
    rw [map_mul, map_mul, map_inv, mul_comm (Matrix.GeneralLinearGroup.det y), mul_inv_cancel_right]
  rw [hd, hψ z y]
  simp only [H z]

end GlobalTheory.MirAvg


open GlobalTheory.GLq GlobalTheory.MirAvg Matrix in
theorem GlobalTheory.MirAvg.tr_mirEl_indep : ∀ (g : ℕ) [Fact g.Prime] (n : ℕ) (ψ : Gn g (n + 1) → ℂ), IsClass ψ → ∀ (θ : (ZMod g)ˣ →* ℂˣ)
    (a : Fin (n + 1) → ZMod g), a ≠ 0 → ∀ b : Bool,
      tr (mirEl θ a b) ψ = tr (mirEl θ (if b then Pi.single 0 1 else Pi.single (Fin.last n) 1) b) ψ := by
  intro g _ n ψ hψ θ a ha b
  cases b with
  | true =>
    obtain ⟨y, hy⟩ := exists_gl_mulVec_single_eq (0 : Fin (n + 1)) ha
    refine tr_mirEl_conj ψ hψ θ a _ true y fun z => ?_
    rw [mirSet_true_conj, if_pos rfl, ← hy, mulVec_mulVec, y.inv_mul, one_mulVec]
  | false =>
    obtain ⟨P, hP⟩ := exists_gl_mulVec_single_eq (Fin.last n) ha
    let y : Gn g (n + 1) := ⟨(↑P⁻¹ : Mt g (n + 1))ᵀ, (P : Mt g (n + 1))ᵀ,
      by rw [← transpose_mul, P.mul_inv, transpose_one], by rw [← transpose_mul, P.inv_mul, transpose_one]⟩
    refine tr_mirEl_conj ψ hψ θ a _ false y fun z => ?_
    rw [mirSet_false_conj]
    have : a ᵥ* (y : Mt g (n + 1)) = Pi.single (Fin.last n) 1 := by
      show a ᵥ* (↑P⁻¹ : Mt g (n + 1))ᵀ = _
      rw [vecMul_transpose, ← hP, mulVec_mulVec, P.inv_mul, one_mulVec]
    rw [this]; rfl
end
end

section

open GlobalTheory.GLq GlobalTheory.MirAvg Polynomial

noncomputable section

namespace GlobalTheory.MirAvg.Kill

theorem idem_eq_zero {G : Type} [Group G] [Fintype G] (E : MonoidAlgebra ℂ G) (h : E * E = E)
    (h1 : E.coeff 1 = 0) : E = 0 := by
  classical
  haveI : Module.Finite ℂ (MonoidAlgebra ℂ G) := Module.Finite.of_basis (MonoidAlgebra.basis G ℂ)
  haveI : Module.Free ℂ (MonoidAlgebra ℂ G) := Module.Free.of_basis (MonoidAlgebra.basis G ℂ)
  have hi : IsIdempotentElem (LinearMap.mulLeft ℂ E) := by
    refine LinearMap.ext fun x => ?_
    simp [← mul_assoc, h]
  have ht : LinearMap.trace ℂ _ (LinearMap.mulLeft ℂ E) = 0 := by
    rw [LinearMap.trace_eq_matrix_trace ℂ (MonoidAlgebra.basis G ℂ), Matrix.trace]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
    have : (MonoidAlgebra.basis G ℂ) x = MonoidAlgebra.single x 1 := by simp
    rw [this]
    show (E * MonoidAlgebra.single x 1).coeff x = 0
    rw [MonoidAlgebra.coeff_mul_single_apply]
    simp [h1]
  have h0 := LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero hi ht
  simpa using LinearMap.congr_fun h0 1

variable {G : Type} [Group G] [Fintype G]

theorem coeff_sum_single (F : G → ℂ) (x : G) :
    (∑ h : G, MonoidAlgebra.single h (F h)).coeff x = F x := by
  classical
  simp [MonoidAlgebra.coeff_sum, Finset.sum_apply', Finsupp.single_apply]

theorem coeff_mul' (a b : MonoidAlgebra ℂ G) (x : G) :
    (a * b).coeff x = ∑ q, a.coeff q * b.coeff (q⁻¹ * x) := by
  rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype]
  intro q; simp

def avg (P : G → Prop) [DecidablePred P] (χ : G →* ℂ) : MonoidAlgebra ℂ G :=
  ∑ h : G, MonoidAlgebra.single h (if P h then χ h else 0)

theorem avg_coeff (P : G → Prop) [DecidablePred P] (χ : G →* ℂ) (x : G) :
    (avg P χ).coeff x = if P x then χ x else 0 :=
  coeff_sum_single _ x

theorem avg_mul_self (P : G → Prop) [DecidablePred P] (χ : G →* ℂ)
    (hm : ∀ x y, P x → P y → P (x * y)) (hi : ∀ x, P x → P x⁻¹) :
    avg P χ * avg P χ = ((Finset.univ.filter P).card : ℂ) • avg P χ := by
  ext x
  rw [coeff_mul', MonoidAlgebra.coeff_smul_apply, avg_coeff, smul_eq_mul]
  have key : ∀ q, (avg P χ).coeff q * (avg P χ).coeff (q⁻¹ * x) = if P q then (if P x then χ x else 0) else 0 := by
    intro q
    simp only [avg_coeff]
    by_cases hq : P q
    · have hiff : P (q⁻¹ * x) ↔ P x := ⟨fun h => by simpa using hm _ _ hq h, fun h => hm _ _ (hi _ hq) h⟩
      by_cases hx : P x
      · rw [if_pos hq, if_pos (hiff.2 hx), if_pos hq, if_pos hx, ← map_mul, mul_inv_cancel_left]
      · rw [if_pos hq, if_neg (fun h => hx (hiff.1 h)), if_pos hq, if_neg hx, mul_zero]
    · rw [if_neg hq, if_neg hq, zero_mul]
  simp only [key]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

theorem coeff_one_zOf_mul (ψ : G → ℂ) (a : MonoidAlgebra ℂ G) :
    (zOf ψ * a).coeff 1 = ψ 1 / (Fintype.card G : ℂ) * tr a ψ := by
  rw [coeff_mul', tr, Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.inv G) _ _ fun q => ?_
  rw [zOf, coeff_sum_single]
  simp only [Equiv.inv_apply, inv_inv, mul_one]
  ring

theorem zOf_mul_avg_eq_zero (ψ : G → ℂ) (hψ : IsIrr ψ) (P : G → Prop) [DecidablePred P] (χ : G →* ℂ) (h1 : P 1)
    (hm : ∀ x y, P x → P y → P (x * y)) (hi : ∀ x, P x → P x⁻¹) (htr : tr (avg P χ) ψ = 0) :
    zOf ψ * avg P χ = 0 := by
  obtain ⟨hid, hcen, -⟩ := GlobalTheory.GLq.ZOrth.zorth G ψ ψ hψ hψ
  rw [if_pos rfl] at hid
  set m := avg P χ with hmdef
  set n : ℂ := ((Finset.univ.filter P).card : ℂ) with hn
  have hn0 : n ≠ 0 := by
    rw [hn, Nat.cast_ne_zero]
    exact Finset.card_ne_zero.2 ⟨1, by simp [h1]⟩
  have hmm : m * m = n • m := avg_mul_self P χ hm hi
  have hE : (n⁻¹ • (zOf ψ * m)) * (n⁻¹ • (zOf ψ * m)) = n⁻¹ • (zOf ψ * m) := by
    rw [smul_mul_smul_comm]
    have : zOf ψ * m * (zOf ψ * m) = n • (zOf ψ * m) := by
      calc zOf ψ * m * (zOf ψ * m) = zOf ψ * (m * zOf ψ) * m := by simp only [mul_assoc]
        _ = zOf ψ * (zOf ψ * m) * m := by rw [← hcen m]
        _ = (zOf ψ * zOf ψ) * (m * m) := by simp only [mul_assoc]
        _ = n • (zOf ψ * m) := by rw [hid, hmm, mul_smul_comm]
    rw [this, smul_smul, mul_assoc, inv_mul_cancel₀ hn0, mul_one]
  have h1' : (n⁻¹ • (zOf ψ * m)).coeff 1 = 0 := by
    rw [MonoidAlgebra.coeff_smul_apply, coeff_one_zOf_mul, htr]
    simp
  have h0 := idem_eq_zero _ hE h1'
  rwa [smul_eq_zero, or_iff_right (inv_ne_zero hn0)] at h0

end GlobalTheory.MirAvg.Kill

namespace GlobalTheory.MirAvg

theorem mirSet_one {g : ℕ} [Fact g.Prime] {r : ℕ} (a : Fin r → ZMod g) (b : Bool) : mirSet a b (1 : Gn g r) := by
  cases b
  · intro x _; simp
  · intro x; exact ⟨0, by simp⟩

theorem mirSet_mul {g : ℕ} [Fact g.Prime] {r : ℕ} (a : Fin r → ZMod g) (b : Bool) (h h' : Gn g r)
    (hh : mirSet a b h) (hh' : mirSet a b h') : mirSet a b (h * h') := by
  cases b
  · intro x hx
    simp only [mirSet, Bool.false_eq_true, if_false] at hh hh'
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hh' x hx, hh x hx]
  · intro x
    simp only [mirSet, if_true] at hh hh'
    obtain ⟨c₂, hc₂⟩ := hh' x
    obtain ⟨c₁, hc₁⟩ := hh ((h' : Mt g r).mulVec x)
    refine ⟨c₁ + c₂, ?_⟩
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, add_smul, ← hc₁, ← hc₂]
    abel

theorem mirSet_inv {g : ℕ} [Fact g.Prime] {r : ℕ} (a : Fin r → ZMod g) (b : Bool) (h : Gn g r)
    (hh : mirSet a b h) : mirSet a b h⁻¹ := by
  have hhi : ∀ x, (h : Mt g r).mulVec (((h⁻¹ : Gn g r) : Mt g r).mulVec x) = x := by
    intro x
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hih : ∀ x, ((h⁻¹ : Gn g r) : Mt g r).mulVec ((h : Mt g r).mulVec x) = x := by
    intro x
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  cases b
  · intro x hx
    simp only [mirSet, Bool.false_eq_true, if_false] at hh
    conv_lhs => rw [← hh x hx]
    exact hih x
  · intro x
    simp only [mirSet, if_true] at hh
    obtain ⟨c, hc⟩ := hh (((h⁻¹ : Gn g r) : Mt g r).mulVec x)
    refine ⟨-c, ?_⟩
    rw [hhi x] at hc
    rw [neg_smul, ← hc]
    abel


open Classical in
theorem zOf_mul_mirEl_eq_zero : ∀ (g : ℕ) [Fact g.Prime] (r : ℕ) (ψ : Gn g r → ℂ), IsIrr ψ →
    ∀ (θ : (ZMod g)ˣ →* ℂˣ) (a : Fin r → ZMod g)
    (b : Bool), tr (mirEl θ a b) ψ = 0 → zOf ψ * mirEl θ a b = 0 := by
  intro g _ r ψ hψ θ a b htr
  let χ : Gn g r →* ℂ := (Units.coeHom ℂ).comp (θ.comp Matrix.GeneralLinearGroup.det)
  have hm : mirEl θ a b = Kill.avg (mirSet a b) χ := rfl
  rw [hm] at htr ⊢
  exact Kill.zOf_mul_avg_eq_zero ψ hψ (mirSet a b) χ (mirSet_one a b) (mirSet_mul a b) (mirSet_inv a b) htr

end GlobalTheory.MirAvg
end
end

section

open Formalism.MainNotions.N Formalism.BasicNotions.Loc GlobalTheory.UseLoc

noncomputable section

namespace GlobalTheory.UseLoc.ExtRet

variable {l : ℕ} [Fact l.Prime] {LL LL' : FinExt l}

theorem algebraMap_ne_zero (LL : FinExt l) {d : ℤ_[l]} (hd : d ≠ 0) : algebraMap ℤ_[l] LL.1 d ≠ 0 := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] LL.1]
  intro h0
  apply hd
  have h1 : algebraMap ℤ_[l] ℚ_[l] d = 0 := (map_eq_zero_iff _ (algebraMap ℚ_[l] LL.1).injective).1 h0
  exact (map_eq_zero_iff _ (IsFractionRing.injective ℤ_[l] ℚ_[l])).1 h1

theorem exists_mul (LL : FinExt l) (x : LL.1) : ∃ d : ℤ_[l], d ≠ 0 ∧ IsIntegral ℤ_[l] (d • x) := by
  haveI := LL.2
  haveI : Algebra.IsAlgebraic ℤ_[l] LL.1 :=
    (IsFractionRing.comap_isAlgebraic_iff (A := ℤ_[l]) (K := ℚ_[l]) (C := LL.1)).2 inferInstance
  exact (Algebra.IsAlgebraic.isAlgebraic x).exists_integral_multiple

theorem r_smul (h : LL.1 ≤ LL'.1) (r : ↥(OL LL') →+ ↥(OL LL))
    (hr : ∀ (a : ↥(OL LL)) (x : ↥(OL LL')), r (incO h a * x) = a * r x) (c : ℤ_[l]) (z : ↥(OL LL')) :
    ((r (c • z) : ↥(OL LL)) : LL.1) = algebraMap ℤ_[l] LL.1 c * ((r z : ↥(OL LL)) : LL.1) := by
  have e : c • z = incO h (algebraMap ℤ_[l] (OL LL) c) * z := by
    apply Subtype.ext
    simp [incO, Algebra.smul_def]
  rw [e, hr]
  simp

def ext (r : ↥(OL LL') →+ ↥(OL LL)) (x : LL'.1) : LL.1 :=
  ((r ⟨(exists_mul LL' x).choose • x, (exists_mul LL' x).choose_spec.2⟩ : ↥(OL LL)) : LL.1) /
    algebraMap ℤ_[l] LL.1 (exists_mul LL' x).choose

theorem ext_eq (h : LL.1 ≤ LL'.1) (r : ↥(OL LL') →+ ↥(OL LL))
    (hr : ∀ (a : ↥(OL LL)) (x : ↥(OL LL')), r (incO h a * x) = a * r x)
    (x : LL'.1) (d : ℤ_[l]) (hd : d ≠ 0) (y : ↥(OL LL')) (hy : (y : LL'.1) = d • x) :
    ext r x = ((r y : ↥(OL LL)) : LL.1) / algebraMap ℤ_[l] LL.1 d := by
  unfold ext
  set d0 := (exists_mul LL' x).choose with hd0def
  have hd0 : d0 ≠ 0 := (exists_mul LL' x).choose_spec.1
  set y0 : ↥(OL LL') := ⟨d0 • x, (exists_mul LL' x).choose_spec.2⟩ with hy0
  have key : d • y0 = d0 • y := by
    apply Subtype.ext
    simp only [SetLike.val_smul, hy0, hy, smul_smul, mul_comm]
  have k2 := congrArg (fun z => ((r z : ↥(OL LL)) : LL.1)) key
  simp only [r_smul h r hr] at k2
  rw [div_eq_div_iff (algebraMap_ne_zero LL hd0) (algebraMap_ne_zero LL hd)]
  linear_combination k2

theorem ext_add (h : LL.1 ≤ LL'.1) (r : ↥(OL LL') →+ ↥(OL LL))
    (hr : ∀ (a : ↥(OL LL)) (x : ↥(OL LL')), r (incO h a * x) = a * r x) (x₁ x₂ : LL'.1) :
    ext r (x₁ + x₂) = ext r x₁ + ext r x₂ := by
  obtain ⟨d₁, hd₁, hi₁⟩ := exists_mul LL' x₁
  obtain ⟨d₂, hd₂, hi₂⟩ := exists_mul LL' x₂
  let y₁ : ↥(OL LL') := ⟨d₁ • x₁, hi₁⟩
  let y₂ : ↥(OL LL') := ⟨d₂ • x₂, hi₂⟩
  have hy : ((d₂ • y₁ + d₁ • y₂ : ↥(OL LL')) : LL'.1) = (d₁ * d₂) • (x₁ + x₂) := by
    simp only [y₁, y₂, Subalgebra.coe_add, SetLike.val_smul, smul_smul, smul_add]
    rw [mul_comm d₂ d₁]
  rw [ext_eq h r hr _ (d₁ * d₂) (mul_ne_zero hd₁ hd₂) _ hy, ext_eq h r hr x₁ d₁ hd₁ y₁ rfl,
    ext_eq h r hr x₂ d₂ hd₂ y₂ rfl, map_add, Subalgebra.coe_add, r_smul h r hr, r_smul h r hr, map_mul]
  have n₁ := algebraMap_ne_zero LL hd₁
  have n₂ := algebraMap_ne_zero LL hd₂
  field_simp

theorem ext_mul (h : LL.1 ≤ LL'.1) (r : ↥(OL LL') →+ ↥(OL LL))
    (hr : ∀ (a : ↥(OL LL)) (x : ↥(OL LL')), r (incO h a * x) = a * r x) (a : LL.1) (x : LL'.1) :
    ext r (IntermediateField.inclusion h a * x) = a * ext r x := by
  obtain ⟨d, hd, hi⟩ := exists_mul LL' x
  obtain ⟨e, he, hie⟩ := exists_mul LL a
  let y : ↥(OL LL') := ⟨d • x, hi⟩
  let a'' : ↥(OL LL) := ⟨e • a, hie⟩
  have hy : ((incO h a'' * y : ↥(OL LL')) : LL'.1) = (e * d) • (IntermediateField.inclusion h a * x) := by
    simp only [incO, y, a'', RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, Subalgebra.coe_mul,
      SetLike.val_smul, map_smul]
    simp only [Algebra.smul_def, map_mul]
    have hc : IntermediateField.inclusion h (algebraMap ℤ_[l] LL.1 e) = algebraMap ℤ_[l] LL'.1 e := by simp
    rw [hc]
    ring
  rw [ext_eq h r hr _ (e * d) (mul_ne_zero he hd) _ hy, ext_eq h r hr x d hd y rfl, hr,
    Subalgebra.coe_mul, map_mul]
  have n₁ := algebraMap_ne_zero LL hd
  have n₂ := algebraMap_ne_zero LL he
  have ha : ((a'' : ↥(OL LL)) : LL.1) = algebraMap ℤ_[l] LL.1 e * a := by
    simp [a'', Algebra.smul_def]
  rw [ha]
  field_simp

theorem ext_int (h : LL.1 ≤ LL'.1) (r : ↥(OL LL') →+ ↥(OL LL))
    (hr : ∀ (a : ↥(OL LL)) (x : ↥(OL LL')), r (incO h a * x) = a * r x) (x : ↥(OL LL')) :
    ext r (x : LL'.1) = ((r x : ↥(OL LL)) : LL.1) := by
  rw [ext_eq h r hr _ 1 one_ne_zero x (by simp)]
  simp

end GlobalTheory.UseLoc.ExtRet

namespace GlobalTheory.UseLoc

theorem extRet_exists : ∀ {l : ℕ} [Fact l.Prime] {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) (r : ↥(OL LL') →+ ↥(OL LL)), (∀ (a : ↥(OL LL)) (x : ↥(OL LL')), r (incO h a * x) = a * r x) → r 1 = 1 → ∃ p : ↥LL'.1 →ₗ[ℚ_[l]] ↥LL.1, (∀ (a : ↥LL.1) (x : ↥LL'.1), p (IntermediateField.inclusion h a * x) = a * p x) ∧ ∀ x : ↥(OL LL'), p (x : ↥LL'.1) = ((r x : ↥(OL LL)) : ↥LL.1) := by
  intro l _ LL LL' h r hr _
  refine ⟨{ toFun := ExtRet.ext r
            map_add' := ExtRet.ext_add h r hr
            map_smul' := fun q x => ?_ }, ExtRet.ext_mul h r hr, ExtRet.ext_int h r hr⟩
  have e : q • x = IntermediateField.inclusion h (algebraMap ℚ_[l] LL.1 q) * x := by
    rw [Algebra.smul_def]
    rfl
  simp only [RingHom.id_apply]
  rw [e, ExtRet.ext_mul h r hr, Algebra.smul_def]

end GlobalTheory.UseLoc
end
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_galois_fixed_lift_of_fixed_mod_prime : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (LL : FinExt l) (H : Set (GQ l)) (x : RW LL), (∀ g ∈ H, ∃ r, AI.gRW LL g x - x = (l : RW LL) * r) → ∃ y ∈ fixSub AI LL H, ∃ r, y - x = (l : RW LL) * r := by
  first | exact @GlobalTheory.Decompl.exists_fix_lift_of_fix_mod | exact GlobalTheory.Decompl.exists_fix_lift_of_fix_mod | (intros; apply GlobalTheory.Decompl.exists_fix_lift_of_fix_mod <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

theorem _root_.GlobalTheory.T.etaleEmbedding_frobenius_galois_compat : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : Wach P K LL) (E : EtSit P AI K s LL h W), (∀ e, E.tie.ioE (W.φE e) = φRW LL (E.tie.ioE e)) ∧ (∀ g : ↥(GK K), W.resΓ g = 1 → ∀ e, AI.gRW LL (g : GQ l) (E.tie.ioE e) = E.tie.ioE e) ∧ E.tie.ioE (algebraMap (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) W.EE letπ) = piR AI LL s ∧ (∀ e, ∃ c : ℕ, NearPi AI LL s 0 (piR AI LL s ^ c * E.tie.ioE e)) := by
  first | exact @GlobalTheory.Decompl.ioE_compat | exact GlobalTheory.Decompl.ioE_compat | (intros; apply GlobalTheory.Decompl.ioE_compat <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

theorem _root_.GlobalTheory.T.matrix_frobenius_sub_one_bijective_mod_subring : ∀ (R EE A : Type) [CommRing R] [CommRing EE] [CommRing A] (j : EE →+* R) (ι : A →+* R) (φ : R →+* R) (S : Subring R) (p : ℕ) (t : R) (τ : A), ι τ = t → (∀ e, j e ∈ S) → (∀ x ∈ S, φ x ∈ S) → (∀ e, ∃ e', φ (j e) = j e') → (∀ a, ∃ a', φ (ι a) = ι a') → Near ι p t 2 (φ t) → (∀ e, ∃ c : ℕ, Near ι p t 0 (t ^ c * j e)) → (∀ x, (p : R) * x ∈ S → x ∈ S) → (∀ x e, (p : R) * x = j e → ∃ e', x = j e') → (∀ (k : ℕ) (f : ℕ → R), (∀ i, f i ∈ S) → (∀ i, Near ι p t (i + k) (f i)) → ∃ s ∈ S, ∀ m, Near ι p t (m + k) (s - ∑ i ∈ Finset.range m, f i)) → (∀ x, (∀ m, ∃ e, Near ι p t m (x - j e)) → ∃ e r, x - j e = (p : R) * r) → (∀ y ∈ S, ∀ m, ∃ (n : ℕ) (y0 : R) (e : EE) (r : R), φ^[n] y0 = j e + (p : R) * r ∧ Near ι p t m (y - y0)) → (∀ x : ℕ → R, (∀ i, x i ∈ S) → ∃ s ∈ S, ∀ k, ∃ r, s - ∑ i ∈ Finset.range k, (p : R) ^ i * x i = (p : R) ^ k * r) → (∀ x, (∀ k : ℕ, ∃ e r, x - j e = (p : R) ^ k * r) → ∃ e, x = j e) → ∀ (d : ℕ) (Pm : Matrix (Fin d) (Fin d) EE), (∀ y : Fin d → R, (∀ i, y i ∈ S) → ∃ z : Fin d → R, (∀ i, z i ∈ S) ∧ ∀ i, ∃ e, y i - (∑ k, j (Pm i k) * φ (z k) - z i) = j e) ∧ (∀ z : Fin d → R, (∀ i, z i ∈ S) → (∀ i, ∃ e, ∑ k, j (Pm i k) * φ (z k) - z i = j e) → ∀ i, ∃ e, z i = j e) := by
  first | exact @GlobalTheory.DecomplMat.matrix_frob_sub_one_bijective | exact GlobalTheory.DecomplMat.matrix_frob_sub_one_bijective | (intros; apply GlobalTheory.DecomplMat.matrix_frob_sub_one_bijective <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

theorem _root_.GlobalTheory.T.ainfCocycleSolution_teichmullerEpsilonRoot_pow : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ), Lev l s → ∀ g : GQ l, (P.χQ g : ℚ_[l]) = ((1 + l ^ s : ℕ) : ℚ_[l]) → ∀ U : ℤ_[l], (l : ℤ_[l]) ^ s ∣ U - 1 → ∀ m : ℕ, ¬ l ∣ m → Solv AI K s g U (epsT AI s ^ m) := by
  first | exact @GlobalTheory.ExpImage.EpsSolve.main | exact GlobalTheory.ExpImage.EpsSolve.main | (intros; apply GlobalTheory.ExpImage.EpsSolve.main <;> assumption)
end
