module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle256
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle004
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle009
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle257
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle258
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle259
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
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm

@[expose] public section

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

theorem _root_.GlobalTheory.T.modularGroup_rowVec_and_conj_rightActions : ∀ (N : ℕ), IsRAct (vact N) ∧ (∀ D, IsRAct (gact N D)) ∧ (∀ (x : Fin 2 → ZMod N) α β, vmul (vmul x α) β = vmul x (α * β)) ∧ (∀ x : Fin 2 → ZMod N, vmul x 1 = x) ∧ (∀ (x : Fin 2 → ZMod N) α, vmul x α = 0 ↔ x = 0) ∧ (∀ (M : ℕ) (x : Fin 2 → ZMod N) α, vmul (M • x) α = M • vmul x α) ∧ (∀ (x : Fin 2 → ZMod N) (a : (ZMod N)ˣ), vmul x (dg a) = ![x 0, (a : ZMod N) * x 1]) ∧ (∀ γ δ, redGL N (γ * δ) = redGL N γ * redGL N δ) ∧ redGL N 1 = 1 := by
  first | exact @GlobalTheory.WpFam.Act.rightActions | exact GlobalTheory.WpFam.Act.rightActions | (intros; apply GlobalTheory.WpFam.Act.rightActions <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
private lemma exp_two_pi_I_div_pow_eq_mul (N : ℕ) (hN : (N : ℂ) ≠ 0) (d : ℕ) (τ c : ℂ) (j : ℕ) :
    Complex.exp (2 * Real.pi * Complex.I * ((d * τ + c) / N)) ^ j
      = Complex.exp (2 * Real.pi * Complex.I * (j * c) / N)
        * Complex.exp (2 * Real.pi * Complex.I * τ / N) ^ (d * j) := by
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  ring

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
private lemma wpFam_ch_natCast_mul (N : ℕ) [NeZero N] (j : ℕ) (b : ZMod N) :
    _root_.GlobalTheory.WpFam.ch N ((j : ZMod N) * b)
      = Complex.exp (2 * Real.pi * Complex.I * (j * (b.val : ℂ)) / N) := by
  have h := (_root_.GlobalTheory.WpFam.AddCharZMod.main N).1 ((j * b.val : ℕ) : ℤ)
  have hc : (((j * b.val : ℕ) : ℤ) : ZMod N) = (j : ZMod N) * b := by
    push_cast
    rw [ZMod.natCast_zmod_val]
  rw [hc] at h
  rw [h]
  congr 1
  first | (push_cast; ring) | push_cast

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
private lemma wpFam_ch_neg_natCast_mul (N : ℕ) [NeZero N] (j : ℕ) (b : ZMod N) :
    _root_.GlobalTheory.WpFam.ch N (-((j : ZMod N) * b))
      = Complex.exp (2 * Real.pi * Complex.I * (j * -(b.val : ℂ)) / N) := by
  have h := (_root_.GlobalTheory.WpFam.AddCharZMod.main N).1 (-((j * b.val : ℕ) : ℤ))
  have hc : ((-((j * b.val : ℕ) : ℤ) : ℤ) : ZMod N) = -((j : ZMod N) * b) := by
    push_cast
    rw [ZMod.natCast_zmod_val]
  rw [hc] at h
  rw [h]
  congr 1
  first | (push_cast; ring) | push_cast


open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
theorem _root_.GlobalTheory.WpFam.torsion_row_series : ∀ (N : ℕ) [NeZero N] (e : ℕ) (τ : ℍ) (b : ZMod N) (d : ℕ+), 1 ≤ e → (∑' m : ℤ, 1 / ((((d : ℕ) : ℂ) * τ + (b.val : ℂ)) / N + m) ^ (e + 1) = (-(2 * (Real.pi : ℂ) * Complex.I)) ^ (e + 1) / (e.factorial : ℂ) * ∑' j : ℕ+, ((j : ℕ) : ℂ) ^ e * _root_.GlobalTheory.WpFam.ch N (((j : ℕ) : ZMod N) * b) * Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * τ / N) ^ ((d : ℕ) * (j : ℕ))) ∧ ∑' m : ℤ, 1 / ((-((d : ℕ) : ℂ) * τ + (b.val : ℂ)) / N + m) ^ (e + 1) = (-(2 * (Real.pi : ℂ) * Complex.I)) ^ (e + 1) / (e.factorial : ℂ) * ((-1) ^ (e + 1) * ∑' j : ℕ+, ((j : ℕ) : ℂ) ^ e * _root_.GlobalTheory.WpFam.ch N (-(((j : ℕ) : ZMod N) * b)) * Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * τ / N) ^ ((d : ℕ) * (j : ℕ))) := by
  intro N _ e τ b d he
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have him : ∀ c : ℂ, c.im = 0 → 0 < ((((d : ℕ) : ℂ) * τ + c) / N).im := by
    intro c hc
    rw [Complex.div_natCast_im]
    have h1 : (((d : ℕ) : ℂ) * (τ : ℂ) + c).im = ((d : ℕ) : ℝ) * τ.im := by
      simp [Complex.mul_im, hc]
    rw [h1]
    exact div_pos (mul_pos (by exact_mod_cast d.pos) τ.im_pos) hN
  constructor
  · have h := EisensteinSeries.qExpansion_identity_pnat he
      ⟨(((d : ℕ) : ℂ) * τ + (b.val : ℂ)) / N, him _ (Complex.natCast_im _)⟩
    simp only [UpperHalfPlane.coe_mk] at h
    have hS : (∑' j : ℕ+, ((j : ℕ) : ℂ) ^ e * Complex.exp (2 * Real.pi * Complex.I
        * ((((d : ℕ) : ℂ) * τ + (b.val : ℂ)) / N)) ^ (j : ℕ))
        = ∑' j : ℕ+, ((j : ℕ) : ℂ) ^ e * _root_.GlobalTheory.WpFam.ch N (((j : ℕ) : ZMod N) * b)
          * Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * τ / N) ^ ((d : ℕ) * (j : ℕ)) :=
      tsum_congr fun j => by
        rw [exp_two_pi_I_div_pow_eq_mul N hNc, wpFam_ch_natCast_mul]
        ring
    rw [h, hS]
    ring
  · have h := EisensteinSeries.qExpansion_identity_pnat he
      ⟨(((d : ℕ) : ℂ) * τ + -(b.val : ℂ)) / N, him _
        (by rw [Complex.neg_im, Complex.natCast_im, neg_zero])⟩
    simp only [UpperHalfPlane.coe_mk] at h
    have hterm : ∀ m : ℤ, 1 / ((-((d : ℕ) : ℂ) * τ + (b.val : ℂ)) / N + m) ^ (e + 1)
        = (-1) ^ (e + 1) * (1 / ((((d : ℕ) : ℂ) * τ + -(b.val : ℂ)) / N + ((-m : ℤ) : ℂ)) ^ (e + 1)) := by
      intro m
      rw [show (-((d : ℕ) : ℂ) * τ + (b.val : ℂ)) / N + m
          = -((((d : ℕ) : ℂ) * τ + -(b.val : ℂ)) / N + ((-m : ℤ) : ℂ)) by push_cast; ring]
      rw [neg_pow, one_div, one_div, mul_inv, ← inv_pow, inv_neg, inv_one]
    have hre : ∑' m : ℤ, 1 / ((((d : ℕ) : ℂ) * τ + -(b.val : ℂ)) / N + ((-m : ℤ) : ℂ)) ^ (e + 1)
        = ∑' m : ℤ, 1 / ((((d : ℕ) : ℂ) * τ + -(b.val : ℂ)) / N + (m : ℂ)) ^ (e + 1) :=
      (Equiv.neg ℤ).tsum_eq
        (fun m : ℤ => 1 / ((((d : ℕ) : ℂ) * τ + -(b.val : ℂ)) / N + (m : ℂ)) ^ (e + 1))
    have hS : (∑' j : ℕ+, ((j : ℕ) : ℂ) ^ e * Complex.exp (2 * Real.pi * Complex.I
        * ((((d : ℕ) : ℂ) * τ + -(b.val : ℂ)) / N)) ^ (j : ℕ))
        = ∑' j : ℕ+, ((j : ℕ) : ℂ) ^ e * _root_.GlobalTheory.WpFam.ch N (-(((j : ℕ) : ZMod N) * b))
          * Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * τ / N) ^ ((d : ℕ) * (j : ℕ)) :=
      tsum_congr fun j => by
        rw [exp_two_pi_I_div_pow_eq_mul N hNc, wpFam_ch_neg_natCast_mul]
        ring
    rw [tsum_congr hterm, tsum_mul_left, hre, h, hS]
    ring

end GlobalTheory.WpFam
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
private lemma hc_conj_invariant {F : Type} [Field F] (a b n : ℕ) (α : GL (Fin a) F → ℂ)
    (β : GL (Fin b) F → ℂ) (x p : GL (Fin n) F) :
    hc a b α β n (p * x * p⁻¹) = hc a b α β n x := by
  unfold hc hcTw
  simp only [GlobalTheory.HCCommF.gal_id]
  congr 1
  rw [← finsum_comp_equiv (Equiv.mulLeft p)]
  congr 1
  funext y
  have h : ((Equiv.mulLeft p) y)⁻¹ * (p * x * p⁻¹) * (Equiv.mulLeft p) y = y⁻¹ * x * y := by
    change (p * y)⁻¹ * (p * x * p⁻¹) * (p * y) = y⁻¹ * x * y
    simp [mul_assoc]
  rw [h]

private lemma inPar_swap_eq_inPar_aflipG {F : Type} [Field F] (a b : ℕ) (α : GL (Fin a) F → ℂ)
    (β : GL (Fin b) F → ℂ) (hα : IsCl α) (hβ : IsCl β) (z : GL (Fin (a + b)) F) :
    (if InPar b z then β (tlG b z) * α (brG b a z) else 0) =
      (if InPar a (GlobalTheory.HCCommF.aflipG z) then
        α (tlG a (GlobalTheory.HCCommF.aflipG z)) * β (brG a b (GlobalTheory.HCCommF.aflipG z)) else 0) := by
  obtain ⟨w, rfl⟩ : ∃ w, z = GlobalTheory.HCCommF.aflipG w :=
    ⟨GlobalTheory.HCCommF.aflipG z, (GlobalTheory.HCCommF.aflipG_aflipG z).symm⟩
  rw [GlobalTheory.HCCommF.aflipG_aflipG, GlobalTheory.HCCommF.inPar_aflip]
  unfold tlG brG
  rw [GlobalTheory.HCCommF.aflipG_coe, GlobalTheory.HCCommF.tl_aflip, GlobalTheory.HCCommF.br_aflip,
    GlobalTheory.HCCommF.class_aflip hβ, GlobalTheory.HCCommF.class_aflip hα, mul_comm (β _)]

private lemma hc_swap_eq_hc_aflipG {F : Type} [Field F] (a b : ℕ) (α : GL (Fin a) F → ℂ)
    (β : GL (Fin b) F → ℂ) (hα : IsCl α) (hβ : IsCl β) (x : GL (Fin (a + b)) F) :
    hc b a β α (a + b) x = hc a b α β (a + b) (GlobalTheory.HCCommF.aflipG x) := by
  unfold hc hcTw
  simp only [GlobalTheory.HCCommF.gal_id]
  have hcard : Nat.card {p : GL (Fin (a + b)) F // InPar b p} =
      Nat.card {p : GL (Fin (a + b)) F // InPar a p} :=
    Nat.card_congr (Equiv.subtypeEquiv (GlobalTheory.HCCommF.aflipE (F := F) (a + b)) (fun p => by
      show InPar b p ↔ InPar a (GlobalTheory.HCCommF.aflipG p)
      conv_lhs => rw [← GlobalTheory.HCCommF.aflipG_aflipG p]
      exact GlobalTheory.HCCommF.inPar_aflip _))
  rw [hcard]
  congr 1
  conv_rhs => rw [← finsum_comp_equiv ((GlobalTheory.HCCommF.aflipE (F := F) (a + b)).trans (Equiv.inv _))]
  congr 1
  funext y
  rw [inPar_swap_eq_inPar_aflipG a b α β hα hβ]
  have h : GlobalTheory.HCCommF.aflipG (y⁻¹ * x * y) =
      ((GlobalTheory.HCCommF.aflipG y)⁻¹)⁻¹ * GlobalTheory.HCCommF.aflipG x * (GlobalTheory.HCCommF.aflipG y)⁻¹ := by
    rw [inv_inv, GlobalTheory.HCCommF.aflipG_mul, GlobalTheory.HCCommF.aflipG_mul, GlobalTheory.HCCommF.aflipG_inv, mul_assoc]
  rw [h]
  rfl


theorem _root_.GlobalTheory.T.harishChandraInductionGL_comm : ∀ (F : Type) [Field F] [Finite F], ∀ (a b n : ℕ) (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ), IsCl α → IsCl β → n = a + b → hc a b α β n = hc b a β α n := by
  intro F _ _ a b n α β hα hβ hn
  subst hn
  funext x
  rw [hc_swap_eq_hc_aflipG a b α β hα hβ x]
  obtain ⟨p, hp⟩ := GlobalTheory.HCCommF.aflipG_conj x
  rw [hp, hc_conj_invariant]
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.twistedHarishChandraInductionGL_isTwistedClassFunction : ∀ (F : Type) [Field F] [Finite F], ∀ (t : F →+* F) (a b n : ℕ) (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ), (∀ x y, hcTw t a b α β n (y⁻¹ * x * gal t n y) = hcTw t a b α β n x) ∧ IsCl (hc a b α β n) ∧ ∀ S : F[X] → ℂ, IsCl (psiG S n) ∧ IsCl (chG S n) := by
  first | (exact @GlobalTheory.Shin.twisted_class_main) | (exact GlobalTheory.Shin.twisted_class_main) | (intros; apply GlobalTheory.Shin.twisted_class_main  <;> assumption)
end

section

open NumberField Matrix GlobalTheory.AdLat GlobalTheory.UCls

theorem _root_.GlobalTheory.T.isTA_conj_det_of_isUA_cm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (g : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)), G.det ≠ 0 → IsUA (IsCMField.complexConj E) G g → IsTA (IsCMField.complexConj E) g.det := by
  first | exact @GlobalTheory.unitary_det_isTA | exact GlobalTheory.unitary_det_isTA | (intros; apply GlobalTheory.unitary_det_isTA <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.AdLat GlobalTheory.UCls ReciprocityTheory.ChartRestriction.G.FD
open scoped TensorProduct

theorem _root_.GlobalTheory.T.isInvertibleUnitaryAdelicMatrix_of_rational_unitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (γ : Matrix (Fin r) (Fin r) E), γ.det ≠ 0 → (∀ x y, herm G (γ *ᵥ x) (γ *ᵥ y) = herm G x y) → IsUA (IsCMField.complexConj E) G (ratM (maximalRealSubfield E) γ) := by
  first | exact @GlobalTheory.RatUnit.isUA_ratM | exact GlobalTheory.RatUnit.isUA_ratM | (intros; apply GlobalTheory.RatUnit.isUA_ratM <;> assumption)
end

section

open NumberField Matrix GlobalTheory.AdLat GlobalTheory.UCls ReciprocityTheory.ChartRestriction.G.FD IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.UCls.NormOneMod

theorem exists_integer_add_nsmul (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (M : ℕ) (hM : 1 ≤ M) (k : RA F E) (hk : k ∈ hat1 F {x : E | IsIntegral ℤ x}) :
    ∃ x : 𝓞 E, ∃ y ∈ hat1 F {x : E | IsIntegral ℤ x},
      k = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (x : E) + M • y := by
  induction hk using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    obtain ⟨u, b, hb, h⟩ := (strong_approximation_mod_nat F M hM).2 a ha
    have hu : IsIntegral ℤ (algebraMap F E (u : F)) := u.isIntegral_coe.algebraMap
    refine ⟨⟨algebraMap F E (u : F) * x, hu.mul hx⟩, b ⊗ₜ x, tmul_mem_adelicCompletion_of_integral F hb hx, ?_⟩
    rw [h, TensorProduct.add_tmul, TensorProduct.smul_tmul']
    congr 1
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, Algebra.smul_def]
    rfl
  | zero => exact ⟨0, 0, zero_mem _, by simp⟩
  | add y z _ _ h1 h2 =>
    obtain ⟨x, y, hy, rfl⟩ := h1
    obtain ⟨x', y', hy', rfl⟩ := h2
    refine ⟨x + x', y + y', add_mem hy hy', ?_⟩
    have : ((x + x' : 𝓞 E) : E) = x + x' := by simp
    rw [this, TensorProduct.tmul_add, smul_add]
    abel
  | neg y _ h1 =>
    obtain ⟨x, y, hy, rfl⟩ := h1
    refine ⟨-x, -y, neg_mem hy, ?_⟩
    have : ((-x : 𝓞 E) : E) = -x := by simp
    rw [this, TensorProduct.tmul_neg, smul_neg]
    abel

theorem exists_reps (E : Type) [Field E] [NumberField E] (M : ℕ) (hM : 1 ≤ M) :
    ∃ T : Finset (𝓞 E), T.card ≤ M ^ Module.finrank ℚ E ∧
      ∀ x : 𝓞 E, ∃ t ∈ T, ∃ y : 𝓞 E, x = t + M • y := by
  classical
  let b := Module.finBasis ℤ (𝓞 E)
  let g : (Fin (Module.finrank ℤ (𝓞 E)) → Fin M) → 𝓞 E := fun f => ∑ i, ((f i : ℕ) : ℤ) • b i
  refine ⟨Finset.univ.image g, ?_, fun x => ?_⟩
  · refine Finset.card_image_le.trans ?_
    simp [RingOfIntegers.rank]
  · have hM0 : (0 : ℤ) < M := by exact_mod_cast hM
    let f : Fin (Module.finrank ℤ (𝓞 E)) → Fin M := fun i =>
      ⟨(b.repr x i % M).toNat, by
        have h1 := Int.emod_nonneg (b.repr x i) hM0.ne'
        have h2 := Int.emod_lt_of_pos (b.repr x i) hM0
        omega⟩
    refine ⟨g f, Finset.mem_image_of_mem _ (Finset.mem_univ _),
      ∑ i, (b.repr x i / M) • b i, ?_⟩
    conv_lhs => rw [← b.sum_repr x]
    simp only [g, f, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hM0.ne'), ← natCast_zsmul, smul_smul, ← add_smul,
      Int.emod_add_mul_ediv]

theorem two_mul_fdeg (E : Type) [Field E] [NumberField E] [IsCMField E] :
    2 * fdeg E = Module.finrank ℚ E := by
  have h := (letI : Module.Free (maximalRealSubfield E) E := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E)
  have h2 : Module.finrank (maximalRealSubfield E) E = 2 :=
    Algebra.IsQuadraticExtension.finrank_eq_two _ _
  rw [h2] at h
  unfold fdeg
  omega

theorem exists_reps_normOne (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (c : E ≃ₐ[F] E) (M : ℕ) (hM : 1 ≤ M) :
    ∃ S : Finset (RA F E), S.card ≤ M ^ Module.finrank ℚ E ∧ ∀ k : RA F E, IsTA c k →
      k ∈ hat1 F {x : E | IsIntegral ℤ x} → ∃ s ∈ S, IsTA c s ∧ ∃ k', IsTA c k' ∧
        (∃ y ∈ hat1 F {x : E | IsIntegral ℤ x}, k' - 1 = M • y) ∧ k = s * k' := by
  classical
  obtain ⟨T, hT, hT'⟩ := exists_reps E M hM
  let P : 𝓞 E → RA F E → Prop := fun t k => IsTA c k ∧ k ∈ hat1 F {x : E | IsIntegral ℤ x} ∧
    ∃ y ∈ hat1 F {x : E | IsIntegral ℤ x},
      k = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (t : E) + M • y
  let s : 𝓞 E → RA F E := fun t => Classical.epsilon (P t)
  refine ⟨T.image s, Finset.card_image_le.trans hT, fun k hk hk' => ?_⟩
  obtain ⟨x, y, hy, hxy⟩ := exists_integer_add_nsmul F E M hM k hk'
  obtain ⟨t, ht, z, rfl⟩ := hT' x
  have hP : P t k := by
    refine ⟨hk, hk', (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (z : E) + y,
      add_mem (one_tmul_mem_adelicCompletionOfElementSet F z.isIntegral_coe) hy, ?_⟩
    have : ((t + M • z : 𝓞 E) : E) = t + M • (z : E) := by simp
    rw [hxy, this, TensorProduct.tmul_add, TensorProduct.tmul_smul, smul_add, add_assoc]
  obtain ⟨hs, hs', w, hw, hsw⟩ : P t (s t) := Classical.epsilon_spec ⟨k, hP⟩
  obtain ⟨-, -, w', hw', hkw⟩ := hP
  have hc : sg (FiniteAdeleRing (𝓞 F) F) c (s t) ∈ hat1 F {x : E | IsIntegral ℤ x} :=
    galoisAut_mem_adelicCompletionOfElementSet F c (fun x hx => IsIntegral.map (c : E →+* E).toIntAlgHom hx) hs'
  refine ⟨s t, Finset.mem_image_of_mem _ ht, hs, k * sg _ c (s t), ?_,
    ⟨(w' - w) * sg _ c (s t), mul_mem_adelicCompletionOfElementSet_of_mul_mem F (fun a ha b hb => IsIntegral.mul ha hb)
      (sub_mem hw' hw) hc, ?_⟩, ?_⟩
  · have h1 := congrArg (sg (FiniteAdeleRing (𝓞 F) F) c) hs
    rw [map_mul, map_one] at h1
    unfold IsTA at hk ⊢
    rw [map_mul, mul_mul_mul_comm, hk, h1, one_mul]
  · have h1 : k - s t = M • (w' - w) := by
      rw [smul_sub]
      conv_lhs => rw [hkw, hsw]
      abel
    unfold IsTA at hs
    rw [← smul_mul_assoc, ← h1, sub_mul, hs]
  · unfold IsTA at hs
    rw [mul_left_comm, hs, mul_one]

theorem normOne_mod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (M : ℕ), 1 ≤ M → ∃ S : Finset (RA (maximalRealSubfield E) E), S.card ≤ M ^ (2 * fdeg E) ∧ ∀ k : RA (maximalRealSubfield E) E, IsTA (IsCMField.complexConj E) k → k ∈ hat1 (maximalRealSubfield E) {x : E | IsIntegral ℤ x} → ∃ s ∈ S, IsTA (IsCMField.complexConj E) s ∧ ∃ k', IsTA (IsCMField.complexConj E) k' ∧ (∃ y ∈ hat1 (maximalRealSubfield E) {x : E | IsIntegral ℤ x}, k' - 1 = M • y) ∧ k = s * k' := by
  intro E _ _ _ M hM
  rw [two_mul_fdeg]
  exact exists_reps_normOne _ E _ M hM

end GlobalTheory.UCls.NormOneMod
end

section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef


theorem _root_.GlobalTheory.T.nrm_coeff_prod_linear' : ∀ (k F : Type) [Field k] [Field F] [Algebra k F], ∀ (v : Place k F) (m : ℕ) (α β : Fin m → F), nrm v (fun a : Fin (m + 1) => (∏ j, (Polynomial.C (α j) + Polynomial.C (β j) * Polynomial.X)).coeff a) = ∏ j, max (v.1 (α j)) (v.1 (β j)) := by
  first | exact @GlobalTheory.Nef.nrm_coeff_prod_linear | exact GlobalTheory.Nef.nrm_coeff_prod_linear | (intros; apply GlobalTheory.Nef.nrm_coeff_prod_linear <;> assumption)
end

section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef


theorem _root_.GlobalTheory.T.exists_linearIndependent_bounded_by_pow_of_transcendental : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ t : F, Transcendental k t → ∃ c : ℕ, ∀ N : ℕ, ∃ (n : ℕ) (f : Fin n → F), LinearIndependent k f ∧ ((N : ℤ) - c) * Module.finrank k⟮t⟯ F ≤ n ∧ ∀ (i : Fin n) (v : Place k F), v.1 (f i) ≤ max 1 (v.1 t) ^ N := by
  first | exact @GlobalTheory.Nef.exists_many_bounded_by_pow | exact GlobalTheory.Nef.exists_many_bounded_by_pow | (intros; apply GlobalTheory.Nef.exists_many_bounded_by_pow <;> assumption)
end

section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef


theorem _root_.GlobalTheory.T.existsUnique_place_ord_eq_one_of_transcendental_generator : ∀ (k L : Type) [Field k] [Field L] [Algebra k L] (x : L), Transcendental k x → k⟮x⟯ = ⊤ → ∃ v : Place k L, ord v x = 1 ∧ ∀ w : Place k L, w.1 x < 1 → w = v := by
  first | exact @GlobalTheory.Nef.exists_unique_place_ord_eq_one | exact GlobalTheory.Nef.exists_unique_place_ord_eq_one | (intros; apply GlobalTheory.Nef.exists_unique_place_ord_eq_one <;> assumption)
end

section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef


theorem _root_.GlobalTheory.T.functionFieldOneVariable_transcendental_finite_and_ext : ∀ (k F : Type) [Field k] [Field F] [Algebra k F], IsFF k F → (∀ x : F, Transcendental k x → FiniteDimensional k⟮x⟯ F) ∧ ∀ (E : Type) [Field E] [Algebra k E] [Algebra F E] [IsScalarTower k F E] [FiniteDimensional F E], IsFF k E := by
  first | exact @GlobalTheory.Nef.isFF_main | exact GlobalTheory.Nef.isFF_main | (intros; apply GlobalTheory.Nef.isFF_main <;> assumption)
end

section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef


theorem _root_.GlobalTheory.T.functionFieldPlace_restriction_exists_pow : ∀ (k F E : Type) [Field k] [Field F] [Field E] [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E] [FiniteDimensional F E], (∃ ρ : Place k E → Place k F, IsRes ρ) ∧ ∀ ρ : Place k E → Place k F, IsRes ρ → ∀ p, ∃ e : ℕ, 0 < e ∧ (∀ x : F, p.1 (algebraMap F E x) = (ρ p).1 x ^ e) ∧ ∀ x : F, ord p (algebraMap F E x) = e * ord (ρ p) x := by
  first | exact @GlobalTheory.Nef.place_res_exists_pow | exact GlobalTheory.Nef.place_res_exists_pow | (intros; apply GlobalTheory.Nef.place_res_exists_pow <;> assumption)
end
