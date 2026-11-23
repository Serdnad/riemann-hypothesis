module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle139
public import Mathlib.RingTheory.PowerSeries.Log
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle452
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

@[expose] public section

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

set_option autoImplicit false

namespace GlobalTheory.QLog

theorem defect_sum {O E : Type} [CommRing O] [CommRing E] [Algebra O E] {d : ℕ}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O} (hμ : ∀ i, constantCoeff (μ i) = 0) (m : ℕ)
    {ι : Type} [Fintype ι] (a : ι → E) (f : ι → MvPowerSeries (Fin d) E) :
    defect μ m (∑ i, a i • f i) = ∑ i, a i • defect μ m (f i) := by

  simp only [defect, ← coe_substAlgHom (hasSubst_up_nmul (Q := E) hμ m), map_sum, map_smul,
  Finset.smul_sum, smul_sub, Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _

theorem map_sum_smul {O E : Type} [CommRing O] [CommRing E] [Algebra O E] {σ : Type}
    {ι : Type} [Fintype ι] (b : ι → O) (s : ι → MvPowerSeries σ O) :
    map (algebraMap O E) (∑ i, b i • s i) = ∑ i, algebraMap O E (b i) • map (algebraMap O E) (s i) := by

  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ext α
  rw [coeff_map, MvPowerSeries.coeff_smul, MvPowerSeries.coeff_smul, coeff_map]
  simp only [smul_eq_mul, map_mul]

theorem Chart.isLie_comb : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (ι : Type) [Fintype ι] (e : ι → MvPowerSeries (Fin d) E) (l : ι → G.dual.Lie) (b : ι → O), (∀ i, QL c.μ ⊤ (e i)) → (∀ i, c.IsLie (e i) (l i)) → c.IsLie (comb b e) (∑ i, b i • l i) := by
  intro p _ O E _ _ _ hF G d c ι _ e l b _ hl
  have hinj : Function.Injective (algebraMap O E) := hF.inj
  rw [c.isLie_iff hinj]
  intro n
  choose s hs hc using fun i => (c.isLie_iff hinj _ _).1 (hl i) n
  refine ⟨∑ i, b i • s i, ?_, fun w φ hφ => ?_⟩
  · rw [map_sum_smul, comb, defect_sum c.isLaw.const]
    exact Finset.sum_congr rfl fun i _ => by rw [hs i]
  · have : (∑ i, b i • l i) w - φ (c.ev n (∑ i, b i • s i)) =
        ∑ i, b i * (l i w - φ (c.ev n (s i))) := by

      simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
      smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
    rw [this]
    exact Finset.dvd_sum fun i _ => dvd_mul_of_dvd_right (hc i w φ hφ) _

end GlobalTheory.QLog
end

section

set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog.NmulSubst

theorem subst_zero_fun {R : Type} [CommRing R] {σ τ : Type} [Finite σ] (g : MvPowerSeries σ R) :
    subst (fun _ : σ => (0 : MvPowerSeries τ R)) g = C (constantCoeff g) := by
  have ha : HasSubst (fun _ : σ => (0 : MvPowerSeries τ R)) :=
    hasSubst_of_constantCoeff_zero fun _ => map_zero _
  ext e
  rw [coeff_subst ha, finsum_eq_single _ 0]
  · classical
    rw [Finsupp.prod_zero_index, coeff_one, coeff_C, coeff_zero_eq_constantCoeff_apply]
    split_ifs <;> simp
  · intro x hx
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra! hc
      exact hx (Finsupp.ext hc)
    have : (x.prod fun _ n => (0 : MvPowerSeries τ R) ^ n) = 0 :=
      Finset.prod_eq_zero (i := i) (Finsupp.mem_support_iff.2 hi) (zero_pow hi)
    rw [this, map_zero, smul_zero]

theorem nmul_succ {R : Type} [CommRing R] {d : ℕ} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (k : ℕ) : nmul μ (k + 1) = op μ (nmul μ k) (fun i => X i) := by
  unfold nmul
  exact Function.iterate_succ_apply' _ _ _

theorem constantCoeff_nmul {R : Type} [CommRing R] {d : ℕ}
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : ∀ i, constantCoeff (μ i) = 0) (n : ℕ) :
    ∀ i, constantCoeff (nmul μ n i) = 0 := by
  induction n with
  | zero => intro i; simp [nmul]
  | succ k ih =>
    intro i
    rw [nmul_succ]
    have hs : ∀ j, constantCoeff (Sum.elim (nmul μ k) (fun i => (X i : MvPowerSeries (Fin d) R)) j) = 0 := by
      rintro (j | j)
      · exact ih j
      · exact constantCoeff_X _
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hs) hs (hμ i)

end GlobalTheory.QLog.NmulSubst


open GlobalTheory.QLog.NmulSubst in
theorem GlobalTheory.QLog.subst_nmul_eq (R : Type) [CommRing R] (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (g : MvPowerSeries (Fin d) R) (n : ℕ) :
    subst (nmul μ n) g = C (constantCoeff g) + (n : R) • g +
      ∑ k ∈ Finset.range n, at2 (cob1 μ g) (nmul μ k) (fun i => X i) := by
  induction n with
  | zero =>
    have : nmul μ 0 = fun _ => 0 := rfl
    rw [this, subst_zero_fun]
    simp
  | succ k ih =>
    have hE : ∀ j, constantCoeff (Sum.elim (nmul μ k) (fun i => (X i : MvPowerSeries (Fin d) R)) j) = 0 := by
      rintro (j | j)
      · exact constantCoeff_nmul μ hμ k j
      · exact constantCoeff_X _
    have hsE := hasSubst_of_constantCoeff_zero hE
    have hμs : HasSubst μ := hasSubst_of_constantCoeff_zero hμ
    have hX : ∀ (f : Fin d → Fin d ⊕ Fin d),
        HasSubst (fun i => (X (f i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
      fun _ => hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
    rw [nmul_succ]
    change subst (fun i => subst (Sum.elim (nmul μ k) fun i => X i) (μ i)) g = _
    rw [← subst_comp_subst_apply hμs hsE]
    have hsplit : subst μ g = cob1 μ g + inL g + inR g := by unfold cob1; abel
    have hL : subst (Sum.elim (nmul μ k) fun i => (X i : MvPowerSeries (Fin d) R)) (inL g) =
        subst (nmul μ k) g := by
      unfold inL
      rw [subst_comp_subst_apply (hX Sum.inl) hsE]
      congr 1
      funext i
      rw [subst_X hsE]
      rfl
    have hR : subst (Sum.elim (nmul μ k) fun i => (X i : MvPowerSeries (Fin d) R)) (inR g) = g := by
      unfold inR
      rw [subst_comp_subst_apply (hX Sum.inr) hsE]
      have : (fun i => subst (Sum.elim (nmul μ k) fun i => (X i : MvPowerSeries (Fin d) R))
          (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R)) = X := by
        funext i
        rw [subst_X hsE]
        rfl
      rw [this, subst_self]
      rfl
    rw [hsplit, subst_add hsE, subst_add hsE, hL, hR, ih, Finset.sum_range_succ]
    change _ = _ + _ + (_ + subst (Sum.elim (nmul μ k) fun i => X i) (cob1 μ g))
    push_cast
    rw [add_smul, one_smul]
    abel
end
end

section

set_option autoImplicit false

noncomputable section

open GlobalTheory.QLog GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta

namespace GlobalTheory.WinLift

section Nil

theorem isNil_of_theta_eq {B R ι : Type} [CommRing B] [CommRing R] [IsLocalRing R] [Fintype ι]
    (p : ℕ) [Fact p.Prime] (θ : B →+* R) (σ : B →+* B) (hp : ¬IsUnit (p : R))
    (hσ : ∀ b, (p : B) ∣ σ b - b ^ p) (M M' : Matrix ι ι B) (h : ∀ i j, θ (M i j) = θ (M' i j))
    (hM : IsNil θ σ M) : IsNil θ σ M' := by
  obtain ⟨N, hN⟩ := hM
  refine ⟨N, fun v i => ?_⟩
  have hs : ∀ z : B, θ z ∈ IsLocalRing.maximalIdeal R → θ (σ z) ∈ IsLocalRing.maximalIdeal R := by
    intro z hz
    obtain ⟨c, hc⟩ := hσ z
    have e : σ z = z ^ p + p * c := by rw [← hc]; ring
    rw [e, map_add (f := _), map_pow, map_mul, map_natCast]
    exact Ideal.add_mem _ (Ideal.pow_mem_of_mem _ hz _ (Fact.out : p.Prime).pos)
      (Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).2 hp))
  have key : ∀ (n : ℕ) (w : ι → B) (i : ι),
      θ (((fun w : ι → B => M.mulVec fun j => σ (w j))^[n] w) i) -
        θ (((fun w : ι → B => M'.mulVec fun j => σ (w j))^[n] w) i) ∈
          IsLocalRing.maximalIdeal R := by
    intro n
    induction n with
    | zero => intro w i; simp
    | succ n ih =>
      intro w i
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      simp only [Matrix.mulVec, dotProduct]

      rw [map_sum, map_sum, ← Finset.sum_sub_distrib]
      refine Ideal.sum_mem _ fun j _ => ?_
      rw [map_mul, map_mul, h i j, ← mul_sub, ← map_sub, ← map_sub]
      exact Ideal.mul_mem_left _ _ (hs _ (by rw [map_sub]; exact ih w j))
  intro hu
  have h1 := (IsLocalRing.mem_maximalIdeal _).2 (hN v i)
  have h2 := Ideal.sub_mem _ h1 (key N v i)
  rw [sub_sub_cancel] at h2
  exact (IsLocalRing.mem_maximalIdeal _).1 h2 hu

theorem isNil_of_map {A B R ι : Type} [CommRing A] [CommRing B] [CommRing R] [Fintype ι]
    (a : A →+* B) (θA : A →+* R) (θB : B →+* R) (φ : A →+* A) (σ : B →+* B)
    (hθ : ∀ x, θB (a x) = θA x) (hσ : ∀ x, σ (a x) = a (φ x)) (M : Matrix ι ι A)
    (h : IsNil θB σ (M.map a)) : IsNil θA φ M := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun v i => ?_⟩
  have key : ∀ (n : ℕ) (w : ι → A),
      (fun w : ι → B => (M.map a).mulVec fun j => σ (w j))^[n] (fun j => a (w j)) =
        fun j => a (((fun w : ι → A => M.mulVec fun j => φ (w j))^[n] w) j) := by
    intro n
    induction n with
    | zero => intro w; rfl
    | succ n ih =>
      intro w
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      funext j

      simp [Matrix.mulVec, dotProduct, map_sum, hσ]
  have := hN (fun j => a (v j)) i
  rwa [key, hθ] at this

theorem map_inv_of_isUnit {R S ι : Type} [CommRing R] [CommRing S] [Fintype ι] [DecidableEq ι]
    (f : R →+* S) (M : Matrix ι ι R) (hM : IsUnit M) : (M.map f)⁻¹ = M⁻¹.map f := by
  apply Matrix.inv_eq_right_inv
  rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← map_mul,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det M).1 hM), map_one]

end Nil

end GlobalTheory.WinLift

namespace GlobalTheory.WinLift

section Frob

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]

theorem frob_teich (x : PreTilt O p) :
    WittVector.frobenius (WittVector.teichmuller p x) = WittVector.teichmuller p x ^ p := by
  rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]

theorem frob_xi (ε : PreTilt O p) :
    WittVector.frobenius (xi ε) = ∑ i ∈ Finset.range p, WittVector.teichmuller p ε ^ i := by
  have : root ε ^ p = ε := (_root_.frobeniusEquiv (PreTilt O p) p).apply_symm_apply ε

  simp only [xi, map_sum, map_pow, frob_teich]
  simp only [← map_pow, this]

theorem frob_mu (ε : PreTilt O p) :
    WittVector.frobenius (Sandwich.mu ε) = WittVector.frobenius (xi ε) * Sandwich.mu ε := by
  rw [frob_xi, Sandwich.mu, geom_sum_mul, map_sub, map_one, frob_teich]

theorem mu_dvd_frob_xi_sub (ε : PreTilt O p) :
    Sandwich.mu ε ∣ WittVector.frobenius (xi ε) - p := by
  have : (p : Ainf p O) = ∑ i ∈ Finset.range p, 1 ^ i := by simp
  rw [this, frob_xi, ← Finset.sum_sub_distrib]
  exact Finset.dvd_sum fun i _ => sub_dvd_pow_sub_pow _ _ i

end Frob

end GlobalTheory.WinLift

namespace GlobalTheory.WinLift

section Frame

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] {ε : PreTilt O p}

theorem root_prim (hε : IsPrimitiveSystem ε) : IsPrimitiveRoot (PreTilt.untilt (root ε)) p := by
  simpa [zeta] using hε 1

theorem theta_mu (hv : v.Integers O) (hε : IsPrimitiveSystem ε) :
    WittVector.fontaineTheta O p (Sandwich.mu ε) = 0 :=
  Sandwich.Model.theta_mu hv (root_prim hε)

theorem theta_frob_xi (hv : v.Integers O) (hε : IsPrimitiveSystem ε) :
    WittVector.fontaineTheta O p (WittVector.frobenius (xi ε)) = p := by
  have h1 : WittVector.fontaineTheta O p (WittVector.teichmuller p ε) = 1 := by
    have := theta_mu hv hε
    rw [Sandwich.mu, map_sub, map_one, sub_eq_zero] at this
    exact this

  rw [frob_xi, map_sum]
  simp [h1]

variable (F : BFrame ε)

theorem tf (b : F.B) (h : (p : F.B) * b = 0) : b = 0 := by
  apply F.frame.inj
  have h1 := congrArg (algebraMap F.B F.Q) h
  rw [map_mul, map_natCast, map_zero] at h1
  rw [map_zero]
  exact (F.frame.unit_p.mul_right_eq_zero).1 h1

theorem theta_tau (hv : v.Integers O) (hε : IsPrimitiveSystem ε) : F.θ F.τ = 0 := by
  apply F.frame.sat
  have h := congrArg F.θ F.p_τ
  rw [map_mul, map_natCast, F.θ_a, theta_mu hv hε] at h
  exact h

theorem sigma_tau : F.σ F.τ = F.a (WittVector.frobenius (xi ε)) * F.τ := by
  apply sub_eq_zero.1
  apply tf F
  have h := congrArg F.σ F.p_τ
  rw [map_mul, map_natCast, F.σ_a, frob_mu, map_mul, ← F.p_τ] at h
  rw [mul_sub, h]
  ring

theorem tau_dvd_sigma (b : F.B) (h : F.τ ∣ b) : F.τ ∣ F.σ b := by
  obtain ⟨c, rfl⟩ := h
  rw [map_mul, sigma_tau]
  exact ⟨F.a (WittVector.frobenius (xi ε)) * F.σ c, by ring⟩

theorem mu_dvd_of_p_mul (F : BFrame ε) (z : Ainf p O) (h : Sandwich.mu ε ∣ (p : Ainf p O) * z) :
    Sandwich.mu ε ∣ z := by
  obtain ⟨w, hw⟩ := h
  apply (F.τ_mul z).1
  apply tf F
  have h1 := congrArg F.a hw
  rw [map_mul, map_natCast, map_mul, ← F.p_τ] at h1
  calc (p : F.B) * (F.τ * F.a z) = F.τ * ((p : F.B) * F.a z) := by ring
    _ = 0 := by rw [h1]; linear_combination (p * F.a w) * F.τ_sq

theorem mu_dvd_of_xi_mul (F : BFrame ε) (z : Ainf p O)
    (h : Sandwich.mu ε ∣ WittVector.frobenius (xi ε) * z) : Sandwich.mu ε ∣ z := by
  apply mu_dvd_of_p_mul F
  have h2 := (mu_dvd_frob_xi_sub ε).mul_right z
  have := dvd_sub h h2
  rwa [sub_mul, sub_sub_cancel] at this

end Frame

end GlobalTheory.WinLift
end
end

section

set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog

namespace GlobalTheory.SubstMod

theorem order_prod_sub_prod {R τ ι : Type} [CommRing R] (s : Finset ι)
    (a b : ι → MvPowerSeries τ R) (k : ι → ℕ)
    (ha : ∀ i ∈ s, (k i : ℕ∞) ≤ (a i).order) (hb : ∀ i ∈ s, (k i : ℕ∞) ≤ (b i).order)
    (hab : ∀ i ∈ s, (k i : ℕ∞) + 1 ≤ (a i - b i).order) :
    (∑ i ∈ s, (k i : ℕ∞)) + 1 ≤ (∏ i ∈ s, a i - ∏ i ∈ s, b i).order := by
  first
  | exact @_root_.GlobalTheory.OrderProductDifference.target
  | exact _root_.GlobalTheory.OrderProductDifference.target
  | (apply _root_.GlobalTheory.OrderProductDifference.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.OrderProductDifference.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.OrderProductDifference.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.OrderProductDifference.target ..)

theorem order_pow_sub_pow {R τ : Type} [CommRing R] (u l : MvPowerSeries τ R)
    (hu : constantCoeff u = 0) (hl : constantCoeff l = 0) (hul : (2 : ℕ∞) ≤ (u - l).order)
    (n : ℕ) : (n : ℕ∞) + 1 ≤ (u ^ n - l ^ n).order := by
  have := order_prod_sub_prod (Finset.range n) (fun _ => u) (fun _ => l) (fun _ => 1)
    (fun _ _ => by simpa using one_le_order_iff_constCoeff_eq_zero.mpr hu)
    (fun _ _ => by simpa using one_le_order_iff_constCoeff_eq_zero.mpr hl)
    (fun _ _ => by simpa [one_add_one_eq_two] using hul)
  simpa [Finset.prod_const] using this

theorem order_monoProd_sub {R σ τ : Type} [CommRing R] (u l : σ → MvPowerSeries τ R)
    (hu : ∀ s, constantCoeff (u s) = 0) (hl : ∀ s, constantCoeff (l s) = 0)
    (hul : ∀ s, (2 : ℕ∞) ≤ (u s - l s).order) (α : σ →₀ ℕ) :
    (α.degree : ℕ∞) + 1 ≤
      ((α.prod fun s e => u s ^ e) - α.prod fun s e => l s ^ e).order := by
  have := order_prod_sub_prod α.support (fun s => u s ^ α s) (fun s => l s ^ α s) α
    (fun s _ => le_order_pow_of_constantCoeff_eq_zero _ (hu s))
    (fun s _ => le_order_pow_of_constantCoeff_eq_zero _ (hl s))
    (fun s _ => order_pow_sub_pow _ _ (hu s) (hl s) (hul s) _)
  rw [Finsupp.degree_apply]
  push_cast
  exact this

theorem subst_coeff_sub_mem : ∀ {B Q σ τ : Type} [CommRing B] [CommRing Q] [Algebra B Q] [Fintype σ]
    (N : Ideal B) (u ℓ : σ → MvPowerSeries τ B), (∀ s, constantCoeff (u s) = 0) →
    (∀ s (β : τ →₀ ℕ), β.degree ≤ 1 → coeff β (u s) = coeff β (ℓ s)) →
    ∀ (m : ℕ) (c : MvPowerSeries σ Q), (∀ α : σ →₀ ℕ, α.degree < m → ∃ b ∈ N, coeff α c = algebraMap B Q b) →
    ∀ (w : τ →₀ ℕ), w.degree = m →
      ∃ r ∈ N, coeff w (subst (up Q u) c) - coeff w (subst (up Q ℓ) c) = algebraMap B Q r := by
  intro B Q σ τ _ _ _ _ N u ℓ hu hl m c hc w hw
  have hℓ : ∀ s, constantCoeff (ℓ s) = 0 := fun s => by
    rw [← coeff_zero_eq_constantCoeff_apply, ← hl s 0 (by simp), coeff_zero_eq_constantCoeff_apply,
      hu s]
  have hul : ∀ s, (2 : ℕ∞) ≤ (u s - ℓ s).order := fun s =>
    nat_le_order (n := 2) fun β hβ => by
      rw [map_sub, hl s β (by omega), sub_self]
  have hU : HasSubst (up Q u) := hasSubst_of_constantCoeff_zero fun s => by
    simp [up, hu s]
  have hL : HasSubst (up Q ℓ) := hasSubst_of_constantCoeff_zero fun s => by
    simp [up, hℓ s]
  rw [coeff_subst hU, coeff_subst hL,
    ← finsum_sub_distrib (coeff_subst_finite hU c w) (coeff_subst_finite hL c w)]
  refine finsum_induction (fun x : Q => ∃ r ∈ N, x = algebraMap B Q r) ⟨0, N.zero_mem, by simp⟩
    (fun x y ⟨r, hr, hx⟩ ⟨t, ht, hy⟩ => ⟨r + t, N.add_mem hr ht, by rw [hx, hy, map_add (f := _)]⟩)
    fun α => ?_
  have hprod : ∀ v : σ → MvPowerSeries τ B, (α.prod fun s e => up Q v s ^ e) =
      map (algebraMap B Q) (α.prod fun s e => v s ^ e) := by
    intro v
    simp only [up, Finsupp.prod, map_prod, map_pow]
  rw [hprod u, hprod ℓ, coeff_map, coeff_map, smul_eq_mul, smul_eq_mul, ← mul_sub, ← map_sub,
    ← map_sub]
  by_cases h : α.degree < m
  · obtain ⟨b, hb, hcb⟩ := hc α h
    exact ⟨b * _, N.mul_mem_right _ hb, by rw [hcb, map_mul]⟩
  · have h0 : coeff w ((α.prod fun s e => u s ^ e) - α.prod fun s e => ℓ s ^ e) = 0 := by
      refine coeff_of_lt_order (lt_of_lt_of_le ?_ (order_monoProd_sub u ℓ hu hℓ hul α))
      have : w.degree ≤ α.degree := by omega
      exact_mod_cast Nat.lt_succ_of_le this
    exact ⟨0, N.zero_mem, by rw [h0, map_zero, mul_zero]⟩

end GlobalTheory.SubstMod
end

section

set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.QLog

namespace GlobalTheory.QLog.LogDiff

theorem dIn_log : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] [Algebra ℚ Q],
    DIn (⊤ : Ideal B) (PowerSeries.log Q : MvPowerSeries Unit Q) := by
  intro B Q _ _ _ _ α i
  have hc : MvPowerSeries.coeff α (PowerSeries.log Q : MvPowerSeries Unit Q) =
      PowerSeries.coeff (α i) (PowerSeries.log Q) := by
    rw [PowerSeries.coeff_def (s := α) (n := α i) rfl]
  rw [hc, PowerSeries.coeff_log]
  by_cases h : α i = 0
  · exact ⟨0, trivial, by simp [h]⟩
  · refine ⟨(-1) ^ (α i + 1), trivial, ?_⟩
    have h' : ((α i : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 h
    rw [if_neg h, ← map_natCast (algebraMap ℚ Q), ← map_mul, mul_div_cancel₀ _ h']
    simp

end GlobalTheory.QLog.LogDiff
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.cob1_addLaw_X_pow_eq_sum_choose : ∀ (R : Type) [CommRing R] (d N : ℕ) (m : Fin d), 1 ≤ N → cob1 (addLaw R d) (X m ^ N) = ∑ i ∈ Finset.Ioo 0 N, monomial (Finsupp.single (Sum.inl m) i + Finsupp.single (Sum.inr m) (N - i)) (N.choose i : R) := by
  first | exact @GlobalTheory.coboundaryOne_additiveFormalGroupLaw_X_pow | exact GlobalTheory.coboundaryOne_additiveFormalGroupLaw_X_pow | (intros; apply GlobalTheory.coboundaryOne_additiveFormalGroupLaw_X_pow <;> assumption)
end
