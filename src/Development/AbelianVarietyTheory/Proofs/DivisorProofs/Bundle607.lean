module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle585
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle580
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNatura
public import Mathlib.RingTheory.PowerSeries.Log
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle559
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle560
public import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle566
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle506
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle557
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.Domain
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle137
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.NatCastMulCoeffOfPderivEq
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
open TensorProduct

namespace GlobalTheory

theorem comul_ev_sub_ev₂_subst_mem :
    ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (n : ℕ)
      (F : MvPowerSeries (Fin d) O), ∃ t : G.A n ⊗[O] G.A n,
        Coalgebra.comul (R := O) (c.ev n F) - c.ev₂ n (subst c.μ F) = (p : O) • t := by
  intro p O _ G d c n F
  have hμ : HasSubst c.μ := hasSubst_of_constantCoeff_zero c.isLaw.const
  let φ₁ : MvPowerSeries (Fin d) O →ₐ[O] G.A n ⊗[O] G.A n :=
    (Bialgebra.comulAlgHom O (G.A n)).comp (c.ev n)
  let φ₂ : MvPowerSeries (Fin d) O →ₐ[O] G.A n ⊗[O] G.A n := (c.ev₂ n).comp (substAlgHom hμ)
  have h1 : ∀ f, φ₁ f = Coalgebra.comul (R := O) (c.ev n f) := fun f => rfl
  have h2 : ∀ f, φ₂ f = c.ev₂ n (subst c.μ f) := fun f => by
    simp only [φ₂, AlgHom.comp_apply, coe_substAlgHom]
  have hpoly : φ₁.comp (MvPolynomial.coeToMvPowerSeries.algHom O) =
      φ₂.comp (MvPolynomial.coeToMvPowerSeries.algHom O) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    simp only [AlgHom.comp_apply, MvPolynomial.coeToMvPowerSeries.algHom_apply, MvPolynomial.coe_X,
      Algebra.algebraMap_self, MvPowerSeries.map_id, RingHom.id_apply]
    rw [h1, h2, (c.isEval n).1 i, subst_X hμ, c.comul]
  obtain ⟨N₁, hN₁⟩ := (c.isEval n).2 1
  obtain ⟨N₂, hN₂⟩ := (c.isEval₂ n).2 1
  set N := max N₁ N₂
  set P := trunc' O (Finsupp.equivFunOnFinite.symm fun _ => N) F
  set T := F - (P : MvPowerSeries (Fin d) O)
  have hT : ∀ α : Fin d →₀ ℕ, α.degree < N → coeff α T = 0 := by
    intro α hα
    simp only [T, P, map_sub, MvPolynomial.coeff_coe, coeff_trunc']
    rw [if_pos, sub_self]
    intro i
    show α i ≤ N
    exact le_of_lt (lt_of_le_of_lt (Finsupp.le_degree i α) hα)
  have hPe : φ₁ (P : MvPowerSeries (Fin d) O) = φ₂ (P : MvPowerSeries (Fin d) O) := by
    have := congrArg (fun ψ => ψ P) hpoly
    simpa [MvPolynomial.coeToMvPowerSeries.algHom_apply] using this
  obtain ⟨a, ha⟩ := hN₁ T fun α hα => hT α (lt_of_lt_of_le hα (le_max_left _ _))
  obtain ⟨b, hb⟩ := hN₂ (subst c.μ T) fun β hβ =>
    coeff_subst_eq_zero_of_degree_lt O (Fin d) (Fin d ⊕ Fin d) c.μ T N c.isLaw.const hT β
      (lt_of_lt_of_le hβ (le_max_right _ _))
  rw [pow_one] at ha hb
  refine ⟨Coalgebra.comul (R := O) a - b, ?_⟩
  have hF : F = (P : MvPowerSeries (Fin d) O) + T := by simp [T]
  rw [← h1, ← h2, hF, map_add (f := _), map_add (f := _), hPe, add_sub_add_left_eq_sub, h1, h2, ha, hb,
    ← Bialgebra.comulAlgHom_apply, map_mul, map_natCast, Bialgebra.comulAlgHom_apply,
    ← mul_sub, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]

end GlobalTheory
end

section

set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

namespace GlobalTheory.CEval

theorem eq_zero_of_projective {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]
    [Module.Projective O M] (p : ℕ) [IsHausdorff (Ideal.span {(p : O)}) O] (y : M)
    (h : ∀ m : ℕ, ∃ z : M, y = ((p : O) ^ m) • z) : y = 0 := by
  obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective O M)
  have h0 : s y = 0 := by
    ext i
    refine eq_of_forall_dvd p fun m => ?_
    obtain ⟨z, hz⟩ := h m
    rw [hz, map_smul, Finsupp.smul_apply, smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply, sub_zero]
    exact dvd_mul_right _ _
  have := LinearMap.congr_fun hs y
  rw [LinearMap.comp_apply, h0, map_zero, LinearMap.id_apply] at this
  exact this.symm

theorem isHausdorff_of_projective {O A : Type} [CommRing O] [CommRing A] [Algebra O A]
    [Module.Projective O A] (p : ℕ) [IsHausdorff (Ideal.span {(p : O)}) O] :
    IsHausdorff (Ideal.span {(p : A)}) A := by
  refine ⟨fun y hy => eq_zero_of_projective (O := O) p y fun m => ?_⟩
  have := dvd_of_smodEq p m (hy m)
  rw [sub_zero] at this
  obtain ⟨z, hz⟩ := this
  refine ⟨z, ?_⟩
  rw [hz, Algebra.smul_def, map_pow, map_natCast]

theorem isEval_comp {σ R A A' : Type} [CommRing R] [CommRing A] [CommRing A'] [Algebra R A]
    [Algebra R A'] (p : ℕ) {x : σ → A} {E : MvPowerSeries σ R →ₐ[R] A} (h : IsEval p x E)
    (g : A →ₐ[R] A') : IsEval p (fun i => g (x i)) (g.comp E) := by
  refine ⟨fun i => by rw [AlgHom.comp_apply, h.1], fun m => ?_⟩
  obtain ⟨N, hN⟩ := h.2 m
  refine ⟨N, fun f hf => ?_⟩
  have := map_dvd g (hN f hf)
  rwa [map_pow, map_natCast] at this

theorem eval_subst {σ τ R A : Type} [Fintype σ] [Fintype τ] [CommRing R] [CommRing A]
    [Algebra R A] (p : ℕ) [IsHausdorff (Ideal.span {(p : A)}) A] {x : σ → A}
    {E : MvPowerSeries σ R →ₐ[R] A} (hE : IsEval p x E) (u : τ → MvPowerSeries σ R)
    (E' : MvPowerSeries τ R →ₐ[R] A) (hu : ∀ j, constantCoeff (u j) = 0)
    (hE' : IsEval p (fun j => E (u j)) E') (f : MvPowerSeries τ R) : E (subst u f) = E' f := by
  have hs : HasSubst u := hasSubst_of_constantCoeff_zero hu
  rw [← coe_substAlgHom hs]
  exact ext_of_cont p ((E.comp (substAlgHom hs)).toRingHom) E'.toRingHom
    (fun c => by
      show E (substAlgHom hs (C c)) = E' (C c)
      rw [c_eq_algebraMap, AlgHom.commutes, AlgHom.commutes, AlgHom.commutes])
    (fun j => by
      show E (substAlgHom hs (X j)) = E' (X j)
      rw [substAlgHom_X, hE'.1])
    (fun m => by
      obtain ⟨N, hN⟩ := hE.2 m
      refine ⟨N, fun f hf => ?_⟩
      show (p : A) ^ m ∣ E (substAlgHom hs f)
      rw [coe_substAlgHom]
      refine hN _ fun α hα => coeff_of_lt_order ?_
      have h1 : (1 : ℕ∞) ≤ ⨅ j, (u j).order :=
        le_iInf fun j => one_le_order_iff_constCoeff_eq_zero.2 (hu j)
      have h2 : (N : ℕ∞) ≤ f.order := nat_le_order hf
      calc (α.degree : ℕ∞) < N := by exact_mod_cast hα
        _ = 1 * N := (one_mul _).symm
        _ ≤ (⨅ j, (u j).order) * f.order := mul_le_mul' h1 h2
        _ ≤ (subst u f).order := le_order_subst hs f)
    hE'.2 f

end GlobalTheory.CEval

namespace GlobalTheory.QLog.Chart

open GlobalTheory.CEval

variable {p : ℕ} {O : Type} [CommRing O] [IsHausdorff (Ideal.span {(p : O)}) O]
  {G : PDivGroup p O} {d : ℕ} (c : Chart G d)

omit c in
theorem isHausdorff₂ (G : PDivGroup p O) (n : ℕ) :
    IsHausdorff (Ideal.span {(p : G.A n ⊗[O] G.A n)}) (G.A n ⊗[O] G.A n) :=
  isHausdorff_of_projective (O := O) p

theorem ev₂_subst_μ (n : ℕ) (s : MvPowerSeries (Fin d) O) :
    c.ev₂ n (subst c.μ s) = Coalgebra.comul (R := O) (c.ev n s) := by
  have := isHausdorff₂ G n
  have h := isEval_comp p (c.isEval n) (Bialgebra.comulAlgHom O (G.A n))
  rw [eval_subst p (c.isEval₂ n) c.μ ((Bialgebra.comulAlgHom O (G.A n)).comp (c.ev n))
    c.isLaw.const ?_ s]
  · rfl
  convert h using 2 with j
  rw [c.comul n j]
  rfl

theorem ev₂_inL (n : ℕ) (s : MvPowerSeries (Fin d) O) :
    c.ev₂ n (inL s) = c.ev n s ⊗ₜ[O] (1 : G.A n) := by
  have := isHausdorff₂ G n
  have h := isEval_comp p (c.isEval n) (Algebra.TensorProduct.includeLeft (R := O) (S := O)
    (A := G.A n) (B := G.A n))
  rw [inL, eval_subst p (c.isEval₂ n) (fun i => X (Sum.inl i))
    ((Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := G.A n) (B := G.A n)).comp (c.ev n))
    (fun _ => constantCoeff_X _) ?_ s]
  · rfl
  exact ⟨fun j => (h.1 j).trans ((c.isEval₂ n).1 (Sum.inl j)).symm, h.2⟩

theorem ev₂_inR (n : ℕ) (s : MvPowerSeries (Fin d) O) :
    c.ev₂ n (inR s) = (1 : G.A n) ⊗ₜ[O] c.ev n s := by
  have := isHausdorff₂ G n
  have h := isEval_comp p (c.isEval n) (Algebra.TensorProduct.includeRight (R := O)
    (A := G.A n) (B := G.A n))
  rw [inR, eval_subst p (c.isEval₂ n) (fun i => X (Sum.inr i))
    ((Algebra.TensorProduct.includeRight (R := O) (A := G.A n) (B := G.A n)).comp (c.ev n))
    (fun _ => constantCoeff_X _) ?_ s]
  · rfl
  convert h using 2 with j
  rw [(c.isEval₂ n).1]
  rfl

end GlobalTheory.QLog.Chart

namespace GlobalTheory.QLog.Chart

theorem comul_ev : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (n : ℕ) (s : MvPowerSeries (Fin d) O), Coalgebra.comul (R := O) (c.ev n s) = c.ev n s ⊗ₜ[O] (1 : G.A n) + (1 : G.A n) ⊗ₜ[O] c.ev n s + c.ev₂ n (cob1 c.μ s) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ G d c n s
  rw [cob1, map_sub, map_sub, c.ev₂_subst_μ, c.ev₂_inL, c.ev₂_inR]
  abel

end GlobalTheory.QLog.Chart
end
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

namespace GlobalTheory.ChartUnit

theorem isEval_comp {p : ℕ} {σ R A A' : Type} [CommRing R] [CommRing A] [CommRing A'] [Algebra R A] [Algebra R A']
    {x : σ → A} {E : MvPowerSeries σ R →ₐ[R] A} (φ : A →ₐ[R] A') (h : IsEval p x E) :
    IsEval p (fun i => φ (x i)) (φ.comp E) := by
  refine ⟨fun i => by simp [h.1 i], fun m => ?_⟩
  obtain ⟨N, hN⟩ := h.2 m
  refine ⟨N, fun f hf => ?_⟩
  have := map_dvd φ (hN f hf)
  simpa using this

theorem lift_counit_eq {O A : Type} [CommRing O] [CommRing A] [Bialgebra O A] (t : A ⊗[O] A) :
    Algebra.TensorProduct.lift (AlgHom.id O A) ((Algebra.ofId O A).comp (Bialgebra.counitAlgHom O A))
      (fun _ _ => Commute.all _ _) t = TensorProduct.rid O A (LinearMap.lTensor A (Coalgebra.counit (R := O)) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [Algebra.smul_def, mul_comm]
  | add s t hs ht => simp only [map_add (f := _), hs, ht]

end GlobalTheory.ChartUnit


open GlobalTheory.ChartUnit in
theorem GlobalTheory.chart_unit : ∀ (p : ℕ) (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A] [IsAdicComplete (Ideal.span {(p : A)}) A] {d : ℕ} (x : Fin d → A) (ev : MvPowerSeries (Fin d) O →ₐ[O] A) (E₂ : MvPowerSeries (Fin d ⊕ Fin d) O →ₐ[O] A ⊗[O] A) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), (∀ i, ∃ N : ℕ, (p : A) ∣ x i ^ N) → (∀ i, Coalgebra.counit (R := O) (x i) = 0) → IsEval p x ev → IsEval p (Sum.elim (fun i => x i ⊗ₜ[O] (1 : A)) fun i => (1 : A) ⊗ₜ[O] x i) E₂ → (∀ i, E₂ (μ i) = Coalgebra.comul (R := O) (x i)) → ∀ i, ev (op μ (fun i => (X i : MvPowerSeries (Fin d) O)) (fun _ => 0) i) = x i := by
  intro p O A _ _ _ _ d x ev E₂ μ hnil hcu hev hev₂ hcomul i
  set ψ : A ⊗[O] A →ₐ[O] A := Algebra.TensorProduct.lift (AlgHom.id O A)
    ((Algebra.ofId O A).comp (Bialgebra.counitAlgHom O A)) (fun _ _ => Commute.all _ _) with hψ
  have key := (GlobalTheory.CEval.continuous_eval p O A (Fin d) x hnil).2 ev hev
  let u : Fin d ⊕ Fin d → MvPowerSeries (Fin d) O :=
    Sum.elim (fun i => (X i : MvPowerSeries (Fin d) O)) (fun _ => 0)
  have hE' : IsEval p (fun j => ev (u j)) (ψ.comp E₂) := by
    have h := isEval_comp ψ hev₂
    convert h using 2 with j
    rcases j with j | j
    · simp [u, hψ, hev.1 j]
    · simp [u, hψ, hcu j]
  have hu : ∀ j, constantCoeff (u j) = 0 := by
    intro j; rcases j with j | j <;> simp [u]
  have := key.1 (Fin d ⊕ Fin d) u (ψ.comp E₂) hu hE' (μ i)
  show ev (subst u (μ i)) = x i
  rw [this, AlgHom.comp_apply, hcomul, hψ, lift_counit_eq, Coalgebra.lTensor_counit_comul]
  simp
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

namespace GlobalTheory.CommSwap

theorem eval_swap_eq : ∀ (p : ℕ) (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A] [Coalgebra.IsCocomm O A] [IsAdicComplete (Ideal.span {(p : A ⊗[O] A)}) (A ⊗[O] A)] {d : ℕ} (x : Fin d → A) (E₂ : MvPowerSeries (Fin d ⊕ Fin d) O →ₐ[O] A ⊗[O] A) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), (∀ i, ∃ N : ℕ, (p : A) ∣ x i ^ N) → IsEval p (Sum.elim (fun i => x i ⊗ₜ[O] (1 : A)) fun i => (1 : A) ⊗ₜ[O] x i) E₂ → (∀ i, E₂ (μ i) = Coalgebra.comul (R := O) (x i)) → ∀ i, E₂ (swap (μ i)) = E₂ (μ i) := by
  intro p O A _ _ _ _ _ d x E₂ μ hnil hE hμ i
  set y : Fin d ⊕ Fin d → A ⊗[O] A := Sum.elim (fun i => x i ⊗ₜ[O] (1 : A)) fun i => (1 : A) ⊗ₜ[O] x i with hy
  have hny : ∀ j, ∃ N : ℕ, (p : A ⊗[O] A) ∣ y j ^ N := by
    intro j
    rcases j with j | j
    · obtain ⟨N, a, ha⟩ := hnil j
      refine ⟨N, a ⊗ₜ[O] 1, ?_⟩
      have h1 := map_mul (Algebra.TensorProduct.includeLeftRingHom (R := O) (A := A) (B := A)) (p : A) a
      simp only [Algebra.TensorProduct.includeLeftRingHom_apply, map_natCast] at h1
      simp only [hy, Sum.elim_inl, Algebra.TensorProduct.tmul_pow, one_pow, ha, h1]
    · obtain ⟨N, a, ha⟩ := hnil j
      refine ⟨N, 1 ⊗ₜ[O] a, ?_⟩
      have h1 := map_mul (Algebra.TensorProduct.includeRight (R := O) (A := A) (B := A)) (p : A) a
      simp only [Algebra.TensorProduct.includeRight_apply, map_natCast] at h1
      simp only [hy, Sum.elim_inr, Algebra.TensorProduct.tmul_pow, one_pow, ha, h1]
  set T := (Algebra.TensorProduct.comm O A A).toAlgHom
  set E' := T.comp E₂
  set u : Fin d ⊕ Fin d → MvPowerSeries (Fin d ⊕ Fin d) O :=
    Sum.elim (fun i => X (Sum.inr i)) (fun i => X (Sum.inl i)) with hu
  have hu0 : ∀ j, constantCoeff (u j) = 0 := by
    intro j; rcases j with j | j <;> simp [hu]
  have hE' : IsEval p (fun j => E₂ (u j)) E' := by
    refine ⟨?_, ?_⟩
    · intro j
      rcases j with j | j
      · simp [E', T, hu, hE.1, hy]
      · simp [E', T, hu, hE.1, hy]
    · intro m
      obtain ⟨N, hN⟩ := hE.2 m
      refine ⟨N, fun f hf => ?_⟩
      obtain ⟨c, hc⟩ := hN f hf
      refine ⟨T c, ?_⟩
      simp [E', hc, map_mul, map_pow, map_natCast]
  have key := ((GlobalTheory.CEval.continuous_eval p O (A ⊗[O] A) (Fin d ⊕ Fin d) y hny).2 E₂ hE).1 (Fin d ⊕ Fin d) u E' hu0 hE' (μ i)
  have hs : swap (μ i) = subst u (μ i) := rfl
  rw [hs, key, hμ i]
  simp only [E', T, AlgHom.comp_apply, hμ i]
  exact Coalgebra.comm_comul (R := O) (x i)

end GlobalTheory.CommSwap
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog.Chart

theorem isEval_comp {p : ℕ} {O A A' : Type} {σ : Type} [CommRing O] [CommRing A] [CommRing A']
    [Algebra O A] [Algebra O A'] {x : σ → A} {E : MvPowerSeries σ O →ₐ[O] A} (hE : IsEval p x E)
    (g : A →ₐ[O] A') : IsEval p (fun i => g (x i)) (g.comp E) := by
  refine ⟨fun i => by simp [hE.1 i], fun m => ?_⟩
  obtain ⟨N, hN⟩ := hE.2 m
  refine ⟨N, fun f hf => ?_⟩
  have := map_dvd g (hN f hf)
  rwa [map_pow, map_natCast] at this

theorem ev₂_eval : ∀ (p : ℕ) (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O]
    (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ n f,
    c.ev₂ n (inL f) = c.ev n f ⊗ₜ[O] 1 ∧ c.ev₂ n (inR f) = 1 ⊗ₜ[O] c.ev n f ∧
    c.ev₂ n (subst c.μ f) = Coalgebra.comul (R := O) (c.ev n f) ∧
    c.ev₂ n (cob1 c.μ f) = cobOne O (G.A n) (c.ev n f) := by
  intro p O _ _ G d c n f
  haveI : IsAdicComplete (Ideal.span {(p : G.A n ⊗[O] G.A n)}) (G.A n ⊗[O] G.A n) :=
    T.isAdicComplete_of_finite_projective_algebra p O (G.A n ⊗[O] G.A n)
  have hnil : ∀ i, ∃ N : ℕ, (p : G.A n ⊗[O] G.A n) ∣
      (Sum.elim (fun i => c.x n i ⊗ₜ[O] (1 : G.A n)) (fun i => (1 : G.A n) ⊗ₜ[O] c.x n i) i) ^ N := by
    rintro (i | i)
    · obtain ⟨N, hN⟩ := c.nil n i
      refine ⟨N, ?_⟩
      have := map_dvd (Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := G.A n) (B := G.A n)) hN
      simpa [map_pow, map_natCast] using this
    · obtain ⟨N, hN⟩ := c.nil n i
      refine ⟨N, ?_⟩
      have := map_dvd (Algebra.TensorProduct.includeRight (R := O) (A := G.A n) (B := G.A n)) hN
      simpa [map_pow, map_natCast] using this
  have H := ((CEval.continuous_eval p O (G.A n ⊗[O] G.A n) (Fin d ⊕ Fin d) _ hnil).2
    (c.ev₂ n) (c.isEval₂ n)).1
  have h1 : c.ev₂ n (inL f) = c.ev n f ⊗ₜ[O] 1 := by
    have hx : (fun j => c.ev₂ n ((fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) O)) j)) =
        fun j => Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := G.A n) (B := G.A n)
          (c.x n j) := funext fun j => (c.isEval₂ n).1 (Sum.inl j)
    have hE := isEval_comp (c.isEval n)
      (Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := G.A n) (B := G.A n))
    rw [← hx] at hE
    exact H (Fin d) _ _ (fun _ => constantCoeff_X _) hE f
  have h2 : c.ev₂ n (inR f) = 1 ⊗ₜ[O] c.ev n f := by
    have hx : (fun j => c.ev₂ n ((fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) O)) j)) =
        fun j => Algebra.TensorProduct.includeRight (R := O) (A := G.A n) (B := G.A n)
          (c.x n j) := funext fun j => (c.isEval₂ n).1 (Sum.inr j)
    have hE := isEval_comp (c.isEval n)
      (Algebra.TensorProduct.includeRight (R := O) (A := G.A n) (B := G.A n))
    rw [← hx] at hE
    exact H (Fin d) _ _ (fun _ => constantCoeff_X _) hE f
  have h3 : c.ev₂ n (subst c.μ f) = Coalgebra.comul (R := O) (c.ev n f) := by
    have hx : (fun j => c.ev₂ n (c.μ j)) =
        fun j => Bialgebra.comulAlgHom O (G.A n) (c.x n j) := funext fun j => c.comul n j
    have hE := isEval_comp (c.isEval n) (Bialgebra.comulAlgHom O (G.A n))
    rw [← hx] at hE
    exact H (Fin d) _ _ c.isLaw.const hE f
  refine ⟨h1, h2, h3, ?_⟩
  rw [cob1, map_sub, map_sub, h1, h2, h3, cobOne_apply]

end GlobalTheory.QLog.Chart
end
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

theorem _root_.GlobalTheory.T.subst_one_add_X_pow_log_eq_nsmul : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] [Algebra ℚ Q] (m : ℕ), subst (up Q (fun _ : Unit => ((1 + X ()) ^ m - 1 : MvPowerSeries Unit B))) (PowerSeries.log Q : MvPowerSeries Unit Q) = (m : Q) • (PowerSeries.log Q : MvPowerSeries Unit Q) := by
  first | exact @GlobalTheory.Proof.subst_one_add_X_pow_log_eq_nsmul.subst_pow_log | exact GlobalTheory.Proof.subst_one_add_X_pow_log_eq_nsmul.subst_pow_log | (intros; apply GlobalTheory.Proof.subst_one_add_X_pow_log_eq_nsmul.subst_pow_log <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

theorem _root_.GlobalTheory.T.hasVal_log_of_mul_self_eq_zero' : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] [Algebra ℚ Q] (p : ℕ) (x : B), x * x = 0 → HasVal p (fun _ : Unit => x) (PowerSeries.log Q : MvPowerSeries Unit Q) (algebraMap B Q x) := by
  first | exact @GlobalTheory.QLog.SqZero.hasVal_log_of_mul_self_eq_zero | exact GlobalTheory.QLog.SqZero.hasVal_log_of_mul_self_eq_zero | (intros; apply GlobalTheory.QLog.SqZero.hasVal_log_of_mul_self_eq_zero <;> assumption)
end

section

open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx

theorem _root_.GlobalTheory.T.exists_inverseUnipotentVolume_conj_diagonal_eq : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} (ϖ : kˣ), IsUnif ϖ → ∀ t : n ⊕ Fin c, ∃ z : ℤ, invVol ((KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL (Pi.mulSingle t ϖ))).toMonoidHom) = (resCard k : ℚ) ^ z ∧ |z| ≤ Fintype.card (n ⊕ Fin c) := by
  first | exact @GlobalTheory.DiagVol.invVol_diag_one | exact GlobalTheory.DiagVol.invVol_diag_one | (intros; apply GlobalTheory.DiagVol.invVol_diag_one <;> assumption)
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

theorem mod_noPTorsion : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (h : IsLaw μ), (∀ b, cob1 μ b = 0 → b = 0) → ∀ m : Mod p h, (p : WittVector p k) • m = 0 → m = 0 := by
  intro p _ k _ _ _ d μ h hb m hm
  obtain ⟨R1, R2, -, -, -, R6, ZariskiNoetherianInduction⟩ := GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k (Fin d)
  obtain ⟨-, R2', -, -, -, R6', R7'⟩ := GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k (Fin d ⊕ Fin d)
  obtain ⟨-, C1, -, -⟩ := GlobalTheory.T.reduction_commutes_formalGroupLawCoboundaries p k d μ h.const
  induction m using Submodule.Quotient.induction_on with
  | H x =>
  obtain ⟨f, hf⟩ := x
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hm
  rw [Submodule.Quotient.mk_eq_zero]
  change (p : WittVector p k) • f ∈ intBy p k (Fin d) 1 at hm
  change f ∈ intBy p k (Fin d) 1
  obtain ⟨b, hB⟩ := (R1 _).1 hm
  have hL : ∀ i, constantCoeff (lift p (μ i)) = 0 := fun i => constantCoeff_lift p (h.const i)
  have hcob : cob1 (fun i => lift p (μ i)) ((p : WittVector p k) • f) =
      (p : WittVector p k) • cob1 (fun i => lift p (μ i)) f := by
    rw [← algebraMap_smul (Fr p k) (p : WittVector p k) f, formalCoboundary_smul hL, algebraMap_smul]
  have hcp : cob1 (fun i => lift p (μ i)) ((p : WittVector p k) • f) ∈ intBy p k _ (p : WittVector p k) := by
    rw [hcob, R7']; exact ⟨_, hf.2, rfl⟩
  have h0 : cob1 μ b = 0 := R2' _ _ _ (C1 _ _ hB).1 ((R6' _).1 hcp)
  have hb0 : b = 0 := hb b h0
  subst hb0
  obtain ⟨g, hg, hfg⟩ := (ZariskiNoetherianInduction _ _).1 ((R6 _).2 hB)
  have hp : (algebraMap (WittVector p k) (Fr p k) (p : WittVector p k)) ≠ 0 := by
    rw [map_natCast]
    intro h0
    have := IsFractionRing.injective (WittVector p k) (Fr p k)
    apply WittVector.p_nonzero (p := p) (R := k)
    apply this; rw [map_natCast, map_zero]; exact h0
  have : f = g := by
    ext α
    have := congrArg (coeff α) hfg
    rw [← algebraMap_smul (Fr p k) (p : WittVector p k) f, ← algebraMap_smul (Fr p k) (p : WittVector p k) g,
      map_smul, map_smul, smul_eq_mul, smul_eq_mul] at this
    exact mul_left_cancel₀ hp this
  rw [this]; exact hg

end GlobalTheory.Katz
end
