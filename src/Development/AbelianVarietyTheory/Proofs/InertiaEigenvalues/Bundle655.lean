module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsGenIsUnitSub
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle624
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIterateDerivative
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle625
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle626
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InstTameDescentExponentDataPadicThree
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle076
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle627
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle621
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle580
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle604
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle622
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsSumMonomialAdd
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalMapSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle224
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationBoundOfPrimePowDvdMuPowAcris
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.crystal_coordinates_constantCoeff_eq : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (EE : FCrys l ↥(OL (ϖ.field a))) (c : EE.M (ϖ.prism a) →+ Vec K a ι), (∀ (w : (ϖ.prism a).A) (x : EE.M (ϖ.prism a)), c (w • x) = fun τ i => (toAc t K w τ : K⟦X⟧) * c x τ i) → ∀ (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := K))^[i] f) → ∀ (PP S₀ : Obj l ↥(OL (ϖ.field a))) (p₀ p₁ : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (δ : GlobalTheory.Prism.Hom PP S₀) (j : ZMod a → PP.A →+* K⟦X⟧⟦X⟧) (j₀ : ZMod a → S₀.A →+* K⟦X⟧), δ.comp p₀ = δ.comp p₁ → (∀ τ y, j₀ τ (δ.f y) = PowerSeries.constantCoeff (j τ y)) → (∀ τ (x : (Wq l a)⟦X⟧), j τ (p₀.f x) = PowerSeries.C (toAc t K (frobS l a x) τ : K⟦X⟧) ∧ j τ (p₁.f x) = sh (toAc t K (frobS l a x) τ : K⟦X⟧)) → ∀ (lam₀ lam₁ : EE.M PP →+ (ZMod a → ι → K⟦X⟧⟦X⟧)), (∀ (r : PP.A) (y : EE.M PP) τ i, lam₀ (r • y) τ i = j τ r * lam₀ y τ i) → (∀ (r : PP.A) (y : EE.M PP) τ i, lam₁ (r • y) τ i = j τ r * lam₁ y τ i) → (∀ x τ i, lam₀ (EE.tr p₀ x) τ i = PowerSeries.C (frob K l (c x (τ - 1) i))) → (∀ x τ i, lam₁ (EE.tr p₁ x) τ i = sh (frob K l (c x (τ - 1) i))) → ∀ y τ i, PowerSeries.constantCoeff (lam₀ y τ i) = PowerSeries.constantCoeff (lam₁ y τ i) := by
  first | exact @GlobalTheory.CrysConst.constantCoeff_eq | exact GlobalTheory.CrysConst.constantCoeff_eq | (intros; apply GlobalTheory.CrysConst.constantCoeff_eq <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal Matrix

theorem _root_.GlobalTheory.T.mem_range_coeffTensorAinf_of_frobenius_eq_matrix_mul : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] {n : Type} [Fintype n] (v : n → OW l O) (Y : Matrix n n (OA l O)), (∀ i, frobOW l O (v i) = (Y.map (inclO l O) *ᵥ v) i) → ∀ i, v i ∈ (inclO l O).range := by
  first | exact @GlobalTheory.FrobIntTensor.mem_range_inclO | exact GlobalTheory.FrobIntTensor.mem_range_inclO | (intros; apply GlobalTheory.FrobIntTensor.mem_range_inclO <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.crystal_frobenius_breuilKisin_coordinates : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (EE : FCrys l ↥(OL (ϖ.field a))) (c : EE.M (ϖ.prism a) →+ Vec K a ι), (∀ (w : (ϖ.prism a).A) (x : EE.M (ϖ.prism a)), c (w • x) = fun τ i => (toAc t K w τ : K⟦X⟧) * c x τ i) → (∀ (x m : EE.M (ϖ.prism a)) (k : ℕ), IsFrac (A := (ϖ.prism a).A) (eis l a e) (EE.Φ (ϖ.prism a) ⟨eis l a e, Ideal.mem_span_singleton_self _⟩ x) m k → c m = fun τ i => E K l e ^ k * P.phi (c x) τ i) → ∀ (PP : Obj l ↥(OL (ϖ.field a))) (hl : (l : PP.A) ∈ PP.I) (p : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (J : ZMod a → PP.A →+* K⟦X⟧⟦X⟧) (g : K⟦X⟧ →+* K⟦X⟧⟦X⟧) (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ τ (w : (Wq l a)⟦X⟧), J τ (p.f w) = g (toAc t K (frobS l a w) τ : K⟦X⟧)) → (∀ τ y, J τ (PP.D.φ y) = φ₂ (J (τ - 1) y)) → (∀ f, φ₂ (g f) = g (frob K l f)) → Function.Injective g → ∀ lam : EE.M PP →+ (ZMod a → ι → K⟦X⟧⟦X⟧), (∀ (r : PP.A) (y : EE.M PP) τ i, lam (r • y) τ i = J τ r * lam y τ i) → (∀ x τ i, lam (EE.tr p x) τ i = g (frob K l (c x (τ - 1) i))) → ∀ (y n : EE.M PP) (k : ℕ), IsFrac (l : PP.A) (EE.Φ PP ⟨l, hl⟩ y) n k → ∀ τ i, lam n τ i = (l : K⟦X⟧⟦X⟧) ^ k * (((P.mx (τ - 1)).map (frob K l)).map g *ᵥ fun j => φ₂ (lam y (τ - 1) j)) i := by
  first | exact @GlobalTheory.CrysFrobCoord.frob_in_coordinates | exact GlobalTheory.CrysFrobCoord.frob_in_coordinates | (intros; apply GlobalTheory.CrysFrobCoord.frob_in_coordinates <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_unit_coeff_wittTilt_relation : ∀ {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {S : Type} [Fintype S] (y : S → ZMod a → A O K) (c : S → OW l O) (h : ∑ s, c s * inclO l O (ϖ.iTot t K (y s)) = 1) (τ : ZMod a), ∃ s k, ‖coeff k (y s τ : K⟦X⟧)‖ = 1 := by
  first | exact @GlobalTheory.ResidueUnitCoeff.exists_norm_coeff_eq_one | exact GlobalTheory.ResidueUnitCoeff.exists_norm_coeff_eq_one | (intros; apply GlobalTheory.ResidueUnitCoeff.exists_norm_coeff_eq_one <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal Matrix

theorem _root_.GlobalTheory.T.frobenius_integrality_coeffTensorAinf_vector : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] (ι : Type) [Fintype ι] [DecidableEq ι] (Y : Matrix ι ι (OA l O)) (w : ι → OA l O) (z : ι → OW l O), (fun i => frobOW l O (z i)) = (Y.map (inclO l O)) *ᵥ z + (fun i => inclO l O (w i)) → ∀ i, z i ∈ (inclO l O).range := by
  first | exact @GlobalTheory.FrobIntO.frobenius_integrality_vec_O | exact GlobalTheory.FrobIntO.frobenius_integrality_vec_O | (intros; apply GlobalTheory.FrobIntO.frobenius_integrality_vec_O <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.crystalline_phi_module_map_exists : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (EE : FCrys l ↥(OL (ϖ.field a))) (c : EE.M (ϖ.prism a) →+ Vec K a ι), Function.Injective c → (∀ x, c x ∈ P.M) → (∀ m ∈ P.M, ∃ x, c x = m) → (∀ (w : (ϖ.prism a).A) (x : EE.M (ϖ.prism a)), c (w • x) = fun τ i => (toAc t K w τ : K⟦X⟧) * c x τ i) → (∀ o : O, ∃ U : FHom EE EE, ∀ x, c (U.u (ϖ.prism a) x) = fun τ i => PowerSeries.C (algebraMap O K o) * c x τ i) → ∀ (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := K))^[i] f) → ∀ (PP : Obj l ↥(OL (ϖ.field a))) (p₀ p₁ : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (j : ZMod a → PP.A →+* K⟦X⟧⟦X⟧), (∀ τ (x : (Wq l a)⟦X⟧), j τ (p₀.f x) = PowerSeries.C (toAc t K (frobS l a x) τ : K⟦X⟧) ∧ j τ (p₁.f x) = sh (toAc t K (frobS l a x) τ : K⟦X⟧)) → ∀ (lam₀ lam₁ : EE.M PP →+ (ZMod a → ι → K⟦X⟧⟦X⟧)), (∀ (r : PP.A) (y : EE.M PP) τ i, lam₀ (r • y) τ i = j τ r * lam₀ y τ i) → (∀ (r : PP.A) (y : EE.M PP) τ i, lam₁ (r • y) τ i = j τ r * lam₁ y τ i) → (∀ x τ i, lam₀ (EE.tr p₀ x) τ i = PowerSeries.C (frob K l (c x (τ - 1) i))) → (∀ x τ i, lam₁ (EE.tr p₁ x) τ i = sh (frob K l (c x (τ - 1) i))) → ∃ ε : ZMod a → Matrix ι ι K⟦X⟧⟦X⟧, ∀ y τ, lam₀ y τ = ε τ *ᵥ lam₁ y τ := by
  first | exact @GlobalTheory.BKGal.CrysEps.exists_eps | exact GlobalTheory.BKGal.CrysEps.exists_eps | (intros; apply GlobalTheory.BKGal.CrysEps.exists_eps <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.TaylorBasis

theorem cauchy_dvd {R : Type} [CommRing R] (x : R) (α β : ℕ → R) (A B : R)
    (hA : ∀ r, ∃ n₀, ∀ n ≥ n₀, x ^ r ∣ A - ∑ p ∈ Finset.range n, α p)
    (hB : ∀ r, ∃ n₀, ∀ n ≥ n₀, x ^ r ∣ B - ∑ q ∈ Finset.range n, β q) (r : ℕ) :
    ∃ n₀, ∀ n ≥ n₀, x ^ r ∣ A * B - ∑ k ∈ Finset.range n, ∑ p ∈ Finset.range (k + 1), α p * β (k - p) :=
  GlobalTheory.T.cauchy_product_partial_sums_dvd_pow x α β A B hA hB r

theorem desc_eq {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
    {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {P : PhiMod O K l e a ι} (C : Conn P) (k : ℕ)
    (v : Vec K a ι) : C.desc k v = (X : K⟦X⟧) ^ k • (C.nabla ^ k) v :=
  GlobalTheory.T.desc_eq_X_pow_smul_nabla_pow' C k v

theorem nabla_pow_smul {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
    {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {P : PhiMod O K l e a ι} (C : Conn P) (k : ℕ)
    (f : ZMod a → K⟦X⟧) (v : Vec K a ι) : (C.nabla ^ k) (f • v) = ∑ p ∈ Finset.range (k + 1),
      (k.choose p : K⟦X⟧) • ((fun τ => (⇑(derivative (R := K)))^[p] (f τ)) • (C.nabla ^ (k - p)) v) :=
  GlobalTheory.T.nabla_pow_apply_smul_leibniz C k f v

theorem descN_eq (K : Type) [NormedField K] (p : ℕ) (f : K⟦X⟧) :
    descN K p f = X ^ p * (⇑(derivative (R := K)))^[p] f :=
  GlobalTheory.T.descN_eq_X_pow_mul_iterate_derivative' K p f

theorem muDiv_mul_choose {l : ℕ} [Fact l.Prime] (a : ℕ) [NeZero a] {e : ℕ} [NeZero e] (O : Type) [CommRing O]
    [Algebra ℤ_[l] O] (ϖ : PiSys l e) (g : ↥(GK (ϖ.field a))) {k p : ℕ} (h : p ≤ k) :
    ϖ.muDiv a O g k * (k.choose p : OCr l O) = ϖ.muDiv a O g p * ϖ.muDiv a O g (k - p) := by
  have hx := ϖ.theta_mu (ϖ.gal_pi a g)
  have key : dpow (ϖ.mu g) hx k * (k.choose p : Per.Acris l) = dpow (ϖ.mu g) hx p * dpow (ϖ.mu g) hx (k - p) := by
    apply sub_eq_zero.1
    refine acris_nat_cancel (Nat.factorial_ne_zero k) ?_
    have hf : (k.factorial : Per.Acris l) = (k.choose p : Per.Acris l) * p.factorial * (k - p).factorial := by
      rw [← Nat.cast_mul, ← Nat.cast_mul, Nat.choose_mul_factorial_mul_factorial h]
    rw [show (k.factorial : Per.Acris l) * (dpow (ϖ.mu g) hx k * (k.choose p : Per.Acris l) -
        dpow (ϖ.mu g) hx p * dpow (ϖ.mu g) hx (k - p)) = (k.choose p : Per.Acris l) * ((k.factorial : Per.Acris l) *
        dpow (ϖ.mu g) hx k) - (k.choose p : Per.Acris l) * (((p.factorial : Per.Acris l) * dpow (ϖ.mu g) hx p) *
        (((k - p).factorial : Per.Acris l) * dpow (ϖ.mu g) hx (k - p))) by
      linear_combination (-(dpow (ϖ.mu g) hx p * dpow (ϖ.mu g) hx (k - p))) * hf]
    rw [factorial_mul_dpow, factorial_mul_dpow, factorial_mul_dpow, ← pow_add, Nat.add_sub_cancel' h, sub_self]
  have hm : ∀ n, ϖ.muDiv a O g n =
      (Algebra.TensorProduct.includeRight : Per.Acris l →ₐ[ℤ_[l]] OCr l O) (dpow (ϖ.mu g) hx n) := fun n => rfl
  rw [hm, hm, hm, ← map_natCast (Algebra.TensorProduct.includeRight : Per.Acris l →ₐ[ℤ_[l]] OCr l O), ← map_mul,
    ← map_mul, key]

theorem galOCr_iC_taylor {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e] {O K : Type} [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e)
    (g : ↥(GK (ϖ.field a))) (c : ZMod a → S O K e) (r : ℕ) :
    ∃ n₀, ∀ n ≥ n₀, (l : OCr l O) ^ r ∣ galOCr O (g : GQ l) (ϖ.iC t K c) -
      ∑ p ∈ Finset.range n, ϖ.muDiv a O g p * ϖ.iC t K (fun τ => ⟨descN K p (c τ), descN_mem_S e p (c τ).2⟩) := by
  choose N hN using fun τ : ZMod a => ϖ.taylor_S a O K g (c τ) r
  refine ⟨Finset.univ.sup N, fun n hn => ?_⟩
  choose z hz using fun τ => hN τ n ((Finset.le_sup (Finset.mem_univ τ)).trans hn)
  refine ⟨∑ τ, idem (constC t) τ * z τ, ?_⟩

  simp only [PiSys.iC, glue_apply, map_sum, map_mul, galOCr_idem, Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [mul_left_comm, ← hz τ, mul_sub, Finset.mul_sum]
  simp only [mul_left_comm (idem (constC t) τ)]

theorem coord_desc {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
    {l e a : ℕ} [Fact l.Prime] {ι : Type} [Fintype ι] [DecidableEq ι] {P : PhiMod O K l e a ι} (C : Conn P)
    (m : Vec K a ι) (k : ℕ) (τ : ZMod a) (i : ι) :
    (P.mxInv τ *ᵥ C.desc k m τ) i = ∑ j, ∑ p ∈ Finset.range (k + 1), (k.choose p : K⟦X⟧) *
      (descN K p ((P.mxInv τ *ᵥ m τ) j) * (X ^ (k - p) * (P.mxInv τ *ᵥ (C.nabla ^ (k - p)) (P.phi (bas j)) τ) i)) := by
  have hΦ : ∀ (f : ZMod a → K⟦X⟧) (w : Vec K a ι),
      (P.mxInv τ *ᵥ (f • w) τ) i = f τ * (P.mxInv τ *ᵥ w τ) i := fun f w => by
    rw [Pi.smul_apply', Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
  have hΦs : ∀ (s : K⟦X⟧) (w : Vec K a ι),
      (P.mxInv τ *ᵥ (s • w) τ) i = s * (P.mxInv τ *ᵥ w τ) i := fun s w => by
    rw [Pi.smul_apply, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
  have hΦsum : ∀ {J : Type} (s : Finset J) (w : J → Vec K a ι),
      (P.mxInv τ *ᵥ (∑ x ∈ s, w x) τ) i = ∑ x ∈ s, (P.mxInv τ *ᵥ w x τ) i := fun s w => by
    rw [Finset.sum_apply, Matrix.mulVec_sum, Finset.sum_apply]
  conv_lhs => rw [desc_eq, P.eq_sum_phi_bas m]

  rw [hΦs, map_sum, hΦsum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [nabla_pow_smul, hΦsum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpk : p ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hp)
  rw [hΦs, hΦ, descN_eq]
  have hX : (X : K⟦X⟧) ^ k = X ^ p * X ^ (k - p) := by rw [← pow_add, Nat.add_sub_cancel' hpk]
  rw [hX]
  ring

theorem taylor_of_basis {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] {O K : Type} [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {ι : Type}
    [Fintype ι] [DecidableEq ι] {P : PhiMod O K l e a ι} {T : Lat a O K ϖ} (I : Ident t ϖ P T) (C : Conn P)
    (hS : ∀ (τ : ZMod a) (j : ι) (k : ℕ) (i : ι),
      (X : K⟦X⟧) ^ k * (P.mxInv τ *ᵥ (C.nabla ^ k) (P.phi (bas j)) τ) i ∈ S O K e)
    (hΓ : ∀ g : ↥(GK (ϖ.field a)), ∃ Γ, I.IsLMat (g : GQ l) g Γ ∧ ∀ (i j : ι) (r : ℕ), ∃ n₀ : ℕ, ∀ n ≥ n₀,
      (l : OCr l O) ^ r ∣ toOCr l O (Γ i j) -
        ∑ k ∈ Finset.range n, ϖ.muDiv a O g k * ϖ.iC t K (fun τ => ⟨_, hS τ j k i⟩)) :
    I.Taylor C := by
  intro g
  obtain ⟨Γ, hΓL, hconv⟩ := hΓ g
  refine ⟨Γ, hΓL, fun m r => ?_⟩
  let c : ι → ZMod a → ↥(S O K e) := coordL P (S O K e) m
  have hcj : ∀ j τ, (c j τ : K⟦X⟧) = (P.mxInv τ *ᵥ (m : Vec K a ι) τ) j := fun j τ => rfl
  have hcm : ∀ j, toCris t ϖ P m j = ϖ.iC t K (c j) := fun j => rfl
  have F3 : ∀ k i, toCris t ϖ P ⟨C.desc k m, C.desc_mem k m.2⟩ i =
      ∑ j, ∑ p ∈ Finset.range (k + 1), (k.choose p : OCr l O) *
        (ϖ.iC t K (fun τ => ⟨descN K p (c j τ), descN_mem_S e p (c j τ).2⟩) *
          ϖ.iC t K (fun τ => ⟨_, hS τ j (k - p) i⟩)) := by
    intro k i
    have h1 : coordL P (S O K e) ⟨C.desc k m, C.desc_mem k m.2⟩ i =
        ∑ j, ∑ p ∈ Finset.range (k + 1), ((k.choose p : ℕ) : ZMod a → ↥(S O K e)) *
          ((fun τ => ⟨descN K p (c j τ), descN_mem_S e p (c j τ).2⟩) * (fun τ => ⟨_, hS τ j (k - p) i⟩)) := by
      funext τ
      apply Subtype.ext
      refine (coord_desc C m k τ i).trans ?_
      simp only [Finset.sum_apply, Pi.mul_apply, Pi.natCast_apply, AddSubmonoidClass.coe_finsetSum,
        MulMemClass.coe_mul, SubringClass.coe_natCast, hcj]
    rw [toCris_apply, h1]

    simp only [map_sum, map_mul, map_natCast]
  have key : ∀ p : ι × ι, ∃ n₀, ∀ n ≥ n₀, (l : OCr l O) ^ r ∣
      galOCr O (g : GQ l) (ϖ.iC t K (c p.2)) * toOCr l O (Γ p.1 p.2) -
        ∑ k ∈ Finset.range n, ∑ q ∈ Finset.range (k + 1),
          (ϖ.muDiv a O g q * ϖ.iC t K (fun τ => ⟨descN K q (c p.2 τ), descN_mem_S e q (c p.2 τ).2⟩)) *
          (ϖ.muDiv a O g (k - q) * ϖ.iC t K (fun τ => ⟨_, hS τ p.2 (k - q) p.1⟩)) :=
    fun p => cauchy_dvd _ _ (fun k => ϖ.muDiv a O g k * ϖ.iC t K (fun τ => ⟨_, hS τ p.2 k p.1⟩)) _ _
      (fun r => galOCr_iC_taylor t ϖ g (c p.2) r) (fun r => hconv p.1 p.2 r) r
  choose N hN using key
  refine ⟨Finset.univ.sup N, fun n hn => ?_⟩
  choose z hz using fun p : ι × ι => hN p n ((Finset.le_sup (Finset.mem_univ p)).trans hn)
  refine ⟨fun i => ∑ j, z (i, j), funext fun i => ?_⟩
  have e1 : (Γ.map (toOCr l O) *ᵥ fun j => galOCr O (g : GQ l) (toCris t ϖ P m j)) i =
      ∑ j, galOCr O (g : GQ l) (ϖ.iC t K (c j)) * toOCr l O (Γ i j) := by
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, hcm]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have e2 : (∑ k ∈ Finset.range n, ϖ.muDiv a O g k • toCris t ϖ P ⟨C.desc k m, C.desc_mem k m.2⟩) i =
      ∑ j, ∑ k ∈ Finset.range n, ∑ q ∈ Finset.range (k + 1),
          (ϖ.muDiv a O g q * ϖ.iC t K (fun τ => ⟨descN K q (c j τ), descN_mem_S e q (c j τ).2⟩)) *
          (ϖ.muDiv a O g (k - q) * ϖ.iC t K (fun τ => ⟨_, hS τ j (k - q) i⟩)) := by
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, F3, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun q hq => ?_
    rw [← mul_assoc, muDiv_mul_choose a O ϖ g (Nat.lt_succ_iff.1 (Finset.mem_range.1 hq))]
    ring
  rw [Pi.sub_apply, e1, e2, ← Finset.sum_sub_distrib, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => hz (i, j)

theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : Lat a ↥(OL LL) ↥LL.1 ϖ) (I : Ident (thetaW a LL) ϖ P T) (C : Conn P) (hS : ∀ (τ : ZMod a) (j : ι) (k : ℕ) (i : ι), (X : (↥LL.1)⟦X⟧) ^ k * (P.mxInv τ *ᵥ (C.nabla ^ k) (P.phi (bas j)) τ) i ∈ S (↥(OL LL)) (↥LL.1) e), (∀ g : ↥(GK (ϖ.field a)), ∃ Γ, I.IsLMat (g : GQ l) g Γ ∧ ∀ (i j : ι) (r : ℕ), ∃ n₀ : ℕ, ∀ n ≥ n₀, (l : OCr l ↥(OL LL)) ^ r ∣ toOCr l ↥(OL LL) (Γ i j) - ∑ k ∈ Finset.range n, ϖ.muDiv a ↥(OL LL) g k * ϖ.iC (thetaW a LL) ↥LL.1 (fun τ => ⟨_, hS τ j k i⟩)) → I.Taylor C :=
  fun _ _ _ _ _ _ ϖ LL _ _ _ _ _ _ _ _ I C hS hΓ => taylor_of_basis (thetaW _ LL) ϖ I C hS hΓ

end GlobalTheory.TaylorBasis
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.eis_pow_smul_phiW_inclL_eq_inclL_mulVec : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (α : ℕ) (Y : Matrix ι ι (OA l O)), (∀ i j, ∃ f : ZMod a → A O K, (∀ τ, (f τ : K⟦X⟧) = E K l e ^ α * P.mx τ i j) ∧ Y i j = ϖ.iTot t K f) → ∀ c : ι → OA l O, inclO l O (frobOA l O (1 ⊗ₜ ϖ.ev a (eis l a e))) ^ α • phiW t ϖ P (inclL t ϖ P c) = inclL t ϖ P (Y.map (frobOA l O) *ᵥ fun i => frobOA l O (c i)) := by
  first | exact @GlobalTheory.BKReal.phiW_inclL_E_pow | exact GlobalTheory.BKReal.phiW_inclL_E_pow | (intros; apply GlobalTheory.BKReal.phiW_inclL_E_pow <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.tame_setting_group_action_compat : ∀ {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {G : Type} [Group G] [TopologicalSpace G] {ι κ μ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ] {P₀ : PhiMod O K l e a ι} {P₁ : PhiMod O K l e a κ} {P₂ : PhiMod O K l e a μ} {T₀ T₁ T₂ : LocLat G ℚ_[l] K O} {I₀ : Ident t ϖ P₀ T₀} {I₁ : Ident t ϖ P₁ T₁} {I₂ : Ident t ϖ P₂ T₂} {f : LatHom T₀.L T₁.L} {g : LatHom T₁.L T₂.L} {F : GlobalTheory.BK.Hom P₀ P₁} {H : GlobalTheory.BK.Hom P₁ P₂} (hS : IsSESLat (Qp := ℚ_[l]) f g) (hF : IsMapOf I₀ I₁ f F) (hH : IsMapOf I₁ I₂ g H), ∀ v : κ → OW l O, homW t ϖ H v = 0 → ∃ w, homW t ϖ F w = v := by
  first | exact @GlobalTheory.BKReal.SESExact.homW_exact_middle | exact GlobalTheory.BKReal.SESExact.homW_exact_middle | (intros; apply GlobalTheory.BKReal.SESExact.homW_exact_middle <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.phiModuleHom_shortExact_split_wittTilt_alt : ∀ {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {G : Type} [Group G] [TopologicalSpace G] {ι κ μ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ] {P₀ : PhiMod O K l e a ι} {P₁ : PhiMod O K l e a κ} {P₂ : PhiMod O K l e a μ} {T₀ T₁ T₂ : LocLat G ℚ_[l] K O} {I₀ : Ident t ϖ P₀ T₀} {I₁ : Ident t ϖ P₁ T₁} {I₂ : Ident t ϖ P₂ T₂} {f : LatHom T₀.L T₁.L} {g : LatHom T₁.L T₂.L} {F : GlobalTheory.BK.Hom P₀ P₁} {H : GlobalTheory.BK.Hom P₁ P₂} (hS : IsSESLat (Qp := ℚ_[l]) f g) (hF : IsMapOf I₀ I₁ f F) (hH : IsMapOf I₁ I₂ g H), (∃ Z : Matrix κ μ (OW l O), (homMat t ϖ H).map (inclO l O) * Z = 1) ∧ (∃ Y : Matrix ι κ (OW l O), Y * (homMat t ϖ F).map (inclO l O) = 1) := by
  first | exact @GlobalTheory.phiModuleHom_shortExact_split_wittTilt | exact GlobalTheory.phiModuleHom_shortExact_split_wittTilt | (intros; apply GlobalTheory.phiModuleHom_shortExact_split_wittTilt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.Per

namespace GlobalTheory

theorem nonempty_crysBKFunctorOL_of_bhattScholze :
    GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] (P : LocPrime l) (AI : LocAinf l P), IsStd P AI → Nonempty (CrysBKFunctorOL a ϖ LL P) := by
  intro BS l _ a e _ _ ϖ LL _ P AI h
  refine ⟨BKFunctor.ofExists (fun T hT => GlobalTheory.T.exists_breuilKisin_module_basis_of_fCrystal BS l a e _ _ _ ϖ T ?_) fun M M' f => GlobalTheory.T.breuilKisin_full_faithfulness_lattice_morphism BS l a e _ _ _ ϖ _ _ _ _ _ _ M.I M'.I M.isBK M'.isBK f⟩
  obtain ⟨E, j, H⟩ := (BS l _ _ _ (isAinf_ainfObj (ϖ.field a))).1 P AI h LL T hT
  exact ⟨E, j, H⟩

end GlobalTheory
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.AcrisMonBound

variable {l : ℕ} [hl : Fact l.Prime]

theorem exists_pow_bound {ϖ : OCb l} (hϖ : ϖ.untilt = (l : Per.OC l)) {c : OCb l} (hc : c ≠ 0) :
    ∃ K : ℕ, ∀ k : ℕ, ϖ ^ k ∣ c → k < K := by
  set a := ‖((c.untilt : Per.OC l) : ℂ_[l])‖
  set b := ‖((l : ℕ) : ℂ_[l])‖
  have ha : 0 < a := by
    refine norm_pos_iff.2 fun h => hc (GlobalTheory.TiltAbs.eq_zero_of_untilt c ?_)
    exact Subtype.ext (by simpa using h)
  have hb1 : b < 1 := GlobalTheory.RingBasics.norm_p_lt
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one ha hb1
  refine ⟨K, fun k hk => ?_⟩
  by_contra hkK
  obtain ⟨d, hd⟩ := map_dvd (PreTilt.untilt (O := Per.OC l) (p := l)) hk
  rw [map_pow, hϖ] at hd
  have h1 := congrArg (fun z : Per.OC l => ‖(z : ℂ_[l])‖) hd
  push_cast at h1
  rw [norm_mul, norm_pow] at h1
  have h2 : a ≤ b ^ k := by
    change ‖((c.untilt : Per.OC l) : ℂ_[l])‖ ≤ _
    rw [h1]
    exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) _) (GlobalTheory.TiltAbs.norm_le_one d)
  have h3 : b ^ k ≤ b ^ K := pow_le_pow_of_le_one (norm_nonneg _) hb1.le (not_lt.1 hkK)
  linarith

end GlobalTheory.AcrisMonBound

namespace GlobalTheory.AcrisMonBound

theorem main : ∀ (l : ℕ) [Fact l.Prime] (y : Ainf l), WittVector.constantCoeff y ≠ 0 → ∃ C : ℕ, ∀ (z : ℤ_[l]) (N : ℕ), z ≠ 0 → (l : Per.Acris l) ^ N ∣ ainfToAcris l y * algebraMap ℤ_[l] (Per.Acris l) z → N ≤ z.valuation + C := by
  intro l hl y hy
  have hl2 : 2 ≤ l := hl.out.two_le
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.MemLoc.FundOnto.untilt_surjective l (l : Per.OC l)
  obtain ⟨K, hK⟩ := exists_pow_bound hϖ hy
  refine ⟨K, fun z N hz h => ?_⟩
  set u := PadicInt.unitCoeff hz
  set v := z.valuation
  rcases le_or_gt N v with hNv | hNv
  · omega
  obtain ⟨n', rfl⟩ := Nat.exists_eq_add_of_le hNv.le
  set y' := y * algebraMap ℤ_[l] (Ainf l) (u : ℤ_[l])
  have hza : algebraMap ℤ_[l] (Per.Acris l) z =
      (l : Per.Acris l) ^ v * algebraMap ℤ_[l] (Per.Acris l) (u : ℤ_[l]) := by
    conv_lhs => rw [PadicInt.unitCoeff_spec hz]
    rw [map_mul, map_pow, map_natCast, mul_comm]
  have hy' : ainfToAcris l y' = ainfToAcris l y * algebraMap ℤ_[l] (Per.Acris l) (u : ℤ_[l]) := by
    simp only [y', map_mul]
    congr 1
  have h2 : (l : Per.Acris l) ^ n' ∣ ainfToAcris l y' := by
    obtain ⟨w, hw⟩ := h
    refine ⟨w, ?_⟩
    have h3 : ((l ^ v : ℕ) : Per.Acris l) * (ainfToAcris l y' - (l : Per.Acris l) ^ n' * w) = 0 := by
      rw [hza] at hw
      rw [hy']
      push_cast
      rw [mul_sub]
      linear_combination hw
    exact sub_eq_zero.1 (acris_nat_cancel (pow_ne_zero _ hl.out.ne_zero) h3)
  have h4 := GlobalTheory.AcrisMuBound.pow_dvd_cc hl2 hϖ h2
  have hu : IsUnit (WittVector.constantCoeff (algebraMap ℤ_[l] (Ainf l) (u : ℤ_[l]))) :=
    (u.isUnit.map _).map _
  rw [show y' = y * algebraMap ℤ_[l] (Ainf l) (u : ℤ_[l]) from rfl, map_mul, hu.dvd_mul_right] at h4
  have h5 := hK _ h4
  have h6 : n' ≤ (l - 1) * n' := Nat.le_mul_of_pos_left n' (by omega)
  omega

end GlobalTheory.AcrisMonBound
end
end
