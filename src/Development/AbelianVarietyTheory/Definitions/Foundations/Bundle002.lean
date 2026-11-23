module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.NumberTheory.BernoulliPolynomials
public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.NumberTheory.ModularForms.SlashActions
public import Mathlib.Analysis.RCLike.Sqrt
public import Mathlib.NumberTheory.ModularForms.DedekindEta
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

section

noncomputable section

open scoped UpperHalfPlane MatrixGroups

namespace GlobalTheory.Sieg

def ee (z : ℂ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * z)

def cthFac (c : ℕ) (q t : ℂ) (m : ℕ) : ℂ :=
  (1 - q ^ m * t) ^ (c ^ 2) * (1 - q ^ m * t⁻¹) ^ (c ^ 2) / ((1 - q ^ m * t ^ c) * (1 - q ^ m * (t ^ c)⁻¹))

def cth (c : ℕ) (q t : ℂ) : ℂ :=
  q ^ ((c ^ 2 - 1) / 12) * (-t) ^ (((c : ℤ) - (c : ℤ) ^ 2) / 2) * (1 - t) ^ (c ^ 2) / (1 - t ^ c) *
    ∏' m : ℕ, cthFac c q t (m + 1)

def pt (x : Fin 2 → ℚ) (τ : ℍ) : ℂ := (x 0 : ℂ) * (τ : ℂ) + (x 1 : ℂ)

def sg (c : ℕ) (x : Fin 2 → ℚ) (τ : ℍ) : ℂ := cth c (ee τ) (ee (pt x τ))


open Classical in
def f0 (j : ℕ) (x : Fin 2 → ℚ) : ℂ :=
  if j = 1 then (if Int.fract (x 0) = 0 then (1 / 2) * (1 + ee (x 1)) / (1 - ee (x 1)) else 1 / 2 - ((Int.fract (x 0) : ℚ) : ℂ))
  else -((((Polynomial.bernoulli j).eval (Int.fract (x 0)) : ℚ)) : ℂ) / j


open Classical in
def fTerm (j : ℕ) (x : Fin 2 → ℚ) (τ : ℍ) (p : ℤ × ℤ) : ℂ :=
  if 0 < (x 0 + p.1) * p.2 then
    (Int.sign p.2 : ℂ) * ((x 0 + p.1 : ℚ) : ℂ) ^ (j - 1) * ee (((x 0 + p.1 : ℚ) : ℂ) * p.2 * (τ : ℂ)) * ee ((x 1 : ℂ) * p.2)
  else 0

def F (j : ℕ) (x : Fin 2 → ℚ) (τ : ℍ) : ℂ := f0 j x + ∑' p : ℤ × ℤ, fTerm j x τ p

def cF (c j : ℕ) (x : Fin 2 → ℚ) (τ : ℍ) : ℂ := (c : ℂ) ^ 2 * F j x τ - (c : ℂ) ^ (2 - (j : ℤ)) * F j (c • x) τ

def admitted (c : ℕ) (x : Fin 2 → ℚ) : Prop :=
  1 < c ∧ Nat.Coprime c 6 ∧ ¬ ((c : ℚ) * x 0 ∈ Set.range ((↑) : ℤ → ℚ) ∧ (c : ℚ) * x 1 ∈ Set.range ((↑) : ℤ → ℚ))

end GlobalTheory.Sieg
end
end

section

noncomputable section

open Polynomial Matrix
open scoped MatrixGroups ModularForm

namespace GlobalTheory.HeckeFamilyMatrices

abbrev mat (γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ)

def slP (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) : ℂ[X] →ₗ[ℂ] ℂ[X] :=
  ∑ i ∈ Finset.range (w + 1),
    (LinearMap.toSpanSingleton ℂ ℂ[X]
      ((C ((g 0 0 : ℤ) : ℂ) * X + C ((g 0 1 : ℤ) : ℂ)) ^ i *
        (C ((g 1 0 : ℤ) : ℂ) * X + C ((g 1 1 : ℤ) : ℂ)) ^ (w - i))).comp (lcoeff ℂ i)

def Z1 (Γ : Subgroup SL(2, ℤ)) (w : ℕ) : Submodule ℂ (Γ → ℂ[X]) where
  carrier := {z | (∀ γ, z γ ∈ degreeLT ℂ (w + 1)) ∧
    ∀ γ δ : Γ, z (γ * δ) = slP w (mat δ) (z γ) + z δ}
  add_mem' := by
    rintro z z' ⟨h1, h2⟩ ⟨h1', h2'⟩
    refine ⟨fun γ => Submodule.add_mem _ (h1 γ) (h1' γ), fun γ δ => ?_⟩
    simp only [Pi.add_apply, h2, h2', map_add (f := _)]
    abel
  zero_mem' := ⟨fun _ => Submodule.zero_mem _, fun _ _ => by simp⟩
  smul_mem' := by
    rintro c z ⟨h1, h2⟩
    refine ⟨fun γ => Submodule.smul_mem _ c (h1 γ), fun γ δ => ?_⟩
    simp only [Pi.smul_apply, h2, map_smul, smul_add]

def B1 (Γ : Subgroup SL(2, ℤ)) (w : ℕ) : Submodule ℂ (Γ → ℂ[X]) :=
  LinearMap.range ((LinearMap.pi fun γ : Γ => slP w (mat γ) - LinearMap.id).comp (degreeLT ℂ (w + 1)).subtype)

def IsDCReps (Γ : Subgroup SL(2, ℤ)) (α : Matrix (Fin 2) (Fin 2) ℤ) {ι : Type} (δ : ι → Matrix (Fin 2) (Fin 2) ℤ) :
    Prop :=
  (∀ i, ∃ γ₁ γ₂ : Γ, δ i = mat γ₁ * α * mat γ₂) ∧
    ∀ γ₁ γ₂ : Γ, ∃! i, ∃ γ : Γ, mat γ₁ * α * mat γ₂ = mat γ * δ i


open Classical in
def hk (Γ : Subgroup SL(2, ℤ)) (w : ℕ) {ι : Type} [Fintype ι] (δ : ι → Matrix (Fin 2) (Fin 2) ℤ) :
    (Γ → ℂ[X]) →ₗ[ℂ] (Γ → ℂ[X]) :=
  by
    classical
    exact LinearMap.pi fun γ : Γ =>
      if h : ∃ π : Equiv.Perm ι, ∀ i, ∃ γ' : Γ, δ i * mat γ = mat γ' * δ (π i) then
        ∑ i, (slP w (δ (h.choose i))).comp (LinearMap.proj (h.choose_spec i).choose)
      else 0

def dg (a b : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![a, 0; 0, b]

def Lev (N l : ℕ) : Subgroup SL(2, ℤ) := CongruenceSubgroup.Gamma1 N ⊓ CongruenceSubgroup.Gamma0 l

def IsDiam (N l : ℕ) (d : ZMod N) (σ : SL(2, ℤ)) : Prop :=
  σ ∈ CongruenceSubgroup.Gamma0 (N * l) ∧ ((mat σ 1 1 : ℤ) : ZMod N) = d

def tqFam (q : ℕ) (σ : SL(2, ℤ)) : Fin (q + 1) → Matrix (Fin 2) (Fin 2) ℤ := fun i =>
  if (i : ℕ) < q then !![1, (i : ℤ); 0, (q : ℤ)] else mat σ * dg q 1

def ulFam (l : ℕ) : Fin l → Matrix (Fin 2) (Fin 2) ℤ := fun j => !![1, (j : ℤ); 0, (l : ℤ)]

def TqZ (Γ : Subgroup SL(2, ℤ)) (w q : ℕ) (σ : SL(2, ℤ)) : Module.End ℂ (Γ → ℂ[X]) := hk Γ w (tqFam q σ)

def UlZ (Γ : Subgroup SL(2, ℤ)) (w l : ℕ) : Module.End ℂ (Γ → ℂ[X]) := hk Γ w (ulFam l)

def DdZ (Γ : Subgroup SL(2, ℤ)) (w : ℕ) (σ : SL(2, ℤ)) : Module.End ℂ (Γ → ℂ[X]) :=
  hk Γ w (fun _ : Unit => mat σ)

def toGL (g : Matrix (Fin 2) (Fin 2) ℤ) : GL (Fin 2) ℝ :=
  if h : g.det = 0 then 1 else
    Matrix.GeneralLinearGroup.mkOfDetNeZero ((Int.castRingHom ℝ).mapMatrix g)
      (by rw [← RingHom.map_det]; simpa using h)


open scoped ModularForm in
def hkF (k : ℤ) {ι : Type} [Fintype ι] (δ : ι → Matrix (Fin 2) (Fin 2) ℤ) (f : UpperHalfPlane → ℂ) :
    UpperHalfPlane → ℂ :=
  ∑ i, f ∣[k] toGL (δ i)

def TqF (k : ℤ) (q : ℕ) (σ : SL(2, ℤ)) (f : UpperHalfPlane → ℂ) : UpperHalfPlane → ℂ := hkF k (tqFam q σ) f

def UlF (k : ℤ) (l : ℕ) (f : UpperHalfPlane → ℂ) : UpperHalfPlane → ℂ := hkF k (ulFam l) f

def DdF (k : ℤ) (σ : SL(2, ℤ)) (f : UpperHalfPlane → ℂ) : UpperHalfPlane → ℂ :=
  hkF k (fun _ : Unit => mat σ) f

def eichler (w : ℕ) (f : UpperHalfPlane → ℂ) (τ : UpperHalfPlane) : ℂ[X] :=
  ∑ j ∈ Finset.range (w + 1),
    C ((w.choose j : ℂ) * ∫ t in (0 : ℝ)..1,
      (f ∘ UpperHalfPlane.ofComplex) (Complex.I + t * ((τ : ℂ) - Complex.I)) *
        (-(Complex.I + t * ((τ : ℂ) - Complex.I))) ^ (w - j) * ((τ : ℂ) - Complex.I)) * X ^ j

def per (Γ : Subgroup SL(2, ℤ)) (w : ℕ) (f : UpperHalfPlane → ℂ) : Γ → ℂ[X] := fun γ =>
  slP w (mat γ) (eichler w f ((γ : SL(2, ℤ)) • UpperHalfPlane.I))

def cj {Γ : Type} (z : Γ → ℂ[X]) : Γ → ℂ[X] := fun γ => (z γ).map (starRingEnd ℂ)

end GlobalTheory.HeckeFamilyMatrices
end
end

section

noncomputable section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup
open scoped MatrixGroups Real ComplexConjugate

namespace GlobalTheory.EisM

abbrev M2 : Type := Matrix (Fin 2) (Fin 2) ℤ

def slz (k : ℕ) (δ : M2) (f : ℍ → ℂ) (τ : ℍ) : ℂ :=
  ((δ.det : ℤ) : ℂ) ^ (k - 1) * ((((δ 1 0 : ℤ) : ℂ) * τ + ((δ 1 1 : ℤ) : ℂ)) ^ k)⁻¹ *
    f (ofComplex ((((δ 0 0 : ℤ) : ℂ) * τ + ((δ 0 1 : ℤ) : ℂ)) / (((δ 1 0 : ℤ) : ℂ) * τ + ((δ 1 1 : ℤ) : ℂ))))

def LRep (L : ℕ) (Δ : Set M2) {ι : Type} (β : ι → M2) : Prop :=
  Set.BijOn (fun p : Gamma0 L × ι => ((p.1 : SL(2, ℤ)) : M2) * β p.2) Set.univ Δ

def RRep (L : ℕ) (Δ : Set M2) {κ : Type} (α : κ → M2) : Prop :=
  Set.BijOn (fun p : κ × Gamma0 L => α p.1 * ((p.2 : SL(2, ℤ)) : M2)) Set.univ Δ

def hsum (k : ℕ) (ε : ℤ → ℂ) {ι : Type} [Fintype ι] (β : ι → M2) (f : ℍ → ℂ) (τ : ℍ) : ℂ :=
  ∑ i, ε (β i 0 0) * slz k (β i) f τ

def DT (L q : ℕ) : Set M2 := {δ | δ.det = q ∧ (L : ℤ) ∣ δ 1 0}

def DU (L l : ℕ) : Set M2 := {δ | δ.det = l ∧ (L : ℤ) ∣ δ 1 0 ∧ ¬ (l : ℤ) ∣ δ 0 0}

def repU (q : ℕ) (j : Fin q) : M2 := !![1, (j : ℕ); 0, q]

def repT (q : ℕ) : Option (Fin q) → M2
  | some j => repU q j
  | none => !![q, 0; 0, 1]

def repL (L q : ℕ) : Option (Fin q) → M2
  | some j => !![q, 0; L * (j : ℕ), 1]
  | none => !![1, 0; 0, q]

def Mod (F : ℍ → ℂ) : Prop := ∃ (C : ℝ) (A : ℕ), ∀ τ : ℍ, ‖F τ‖ ≤ C * (τ.im ^ A + (τ.im ^ A)⁻¹)

def latF (L : ℕ) (b : ℤ → ℂ) (φ : ZMod L → ℂ) : ℤ × ℤ → ℂ := fun x => if (L : ℤ) ∣ x.1 then b (x.1 / L) * φ (x.2 : ZMod L) else 0

def Kills (L : ℕ) (v : ℤ × ℤ) (Φ : ℤ × ℤ → ℂ) : Prop := ∀ x, ∑ r ∈ Finset.range L, Φ (x - (r : ℤ) • v) = 0

def strip : Set ℍ := {τ | 0 ≤ τ.re ∧ τ.re < 1}

end GlobalTheory.EisM

end
end

section

noncomputable section

open UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace GlobalTheory.HeckeFamilyMatrices

def ev (k : ℤ) (F : ℍ → ℂ) (τ : ℍ) : SL(2, ℤ) → ℂ := fun x => (F ∣[k] x) τ

section EtaSix

open Complex Function ModularForm
open scoped Manifold Real

def eta6 (z : ℍ) : ℂ := ModularForm.eta z ^ 6

lemma eta_six_ne_zero (z : ℍ) : eta6 z ≠ 0 := pow_ne_zero _ (eta_ne_zero z.2)

lemma eta_six_product_formula (z : ℍ) : eta6 z = Periodic.qParam 4 z * (∏' n, (1 - eta_q n z)) ^ 6 := by
  simp only [eta6, ModularForm.eta, mul_pow]
  congr
  simp [Periodic.qParam, ← Complex.exp_nsmul, nsmul_eq_mul]
  congr 1
  ring

lemma eta6_slash_three_T_eq_I_smul : eta6 ∣[(3 : ℤ)] ModularGroup.T = (Complex.I : ℂ) • eta6 := by
  ext z
  rw [SL_slash_apply, ModularGroup.denom_apply, modular_T_smul]
  have h1 : ∀ n, eta_q n (((1 : ℝ) +ᵥ z : ℍ) : ℂ) = eta_q n z := by
    intro n
    simp only [eta_q, Periodic.qParam, coe_vadd]
    rw [← exp_periodic (2 * π * Complex.I * z / ((1:ℝ):ℂ))]
    congr 2
    push_cast; ring
  have h2 : Periodic.qParam 4 (((1 : ℝ) +ᵥ z : ℍ) : ℂ) = Complex.I * Periodic.qParam 4 z := by
    simp only [Periodic.qParam, coe_vadd]
    rw [← exp_pi_div_two_mul_I, ← Complex.exp_add, exp_pi_div_two_mul_I]
    congr 1
    push_cast; ring
  simp only [eta_six_product_formula, h1, h2, Pi.smul_apply, smul_eq_mul]
  simp [ModularGroup.T, mul_assoc]

lemma sqrt_pow_six (z : ℂ) : Complex.sqrt z ^ 6 = z ^ 3 := by
  have : Complex.sqrt z ^ 2 = z := by
    simp [Complex.sqrt]
  rw [show 6 = 2 * 3 by rfl, pow_mul, this]

lemma eta_six_slash_S : eta6 ∣[(3 : ℤ)] ModularGroup.S = (Complex.I : ℂ) • eta6 := by
  ext z
  rw [SL_slash_apply, UpperHalfPlane.modular_S_smul, ModularGroup.denom_S]
  have he : η (-(↑z)⁻¹) = (Complex.sqrt Complex.I)⁻¹ * (Complex.sqrt z * η z) := by
    simpa [neg_div] using eta_comp_eq_csqrt_I_inv z.2
  have hz := z.ne_zero
  simp only [eta6, inv_neg, he, mul_pow, inv_pow, sqrt_pow_six, Pi.smul_apply, smul_eq_mul]
  have : (Complex.I : ℂ) ^ 3 = -Complex.I := by rw [pow_succ, I_sq]; ring
  rw [this, zpow_neg, inv_neg, inv_I]
  field_simp

lemma eta_six_slash_root_of_unity (γ : SL(2, ℤ)) : ∃ c : ℂ, c ^ 4 = 1 ∧ eta6 ∣[(3 : ℤ)] γ = c • eta6 := by
  have hγ : γ ∈ Subgroup.closure ({ModularGroup.S, ModularGroup.T} : Set SL(2, ℤ)) := by
    rw [SpecialLinearGroup.SL2Z_generators]; trivial
  induction hγ using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨Complex.I, I_pow_four, eta_six_slash_S⟩
    · exact ⟨Complex.I, I_pow_four, eta6_slash_three_T_eq_I_smul⟩
  | one => exact ⟨1, by simp, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, hx⟩ := hx
    obtain ⟨b, hb, hy⟩ := hy
    refine ⟨a * b, by rw [mul_pow, ha, hb, one_mul], ?_⟩
    rw [SlashAction.slash_mul, hx, SL_smul_slash, hy, smul_smul]
  | inv x _ hx =>
    obtain ⟨a, ha, hx⟩ := hx
    have ha0 : a ≠ 0 := by rintro rfl; simp at ha
    refine ⟨a⁻¹, by rw [inv_pow, ha, inv_one], ?_⟩
    have : eta6 = a • eta6 ∣[(3 : ℤ)] x⁻¹ := by
      rw [← SL_smul_slash, ← hx, ← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one]
    conv_rhs => rw [this]
    rw [smul_smul, inv_mul_cancel₀ ha0, one_smul]

def eta6MultiplierFunction (γ : SL(2, ℤ)) : ℂ := (eta6 ∣[(3 : ℤ)] γ) UpperHalfPlane.I / eta6 UpperHalfPlane.I

lemma eta6Mult0_eq {γ : SL(2, ℤ)} {c : ℂ} (h : eta6 ∣[(3 : ℤ)] γ = c • eta6) : eta6MultiplierFunction γ = c := by
  simp [eta6MultiplierFunction, h, eta_six_ne_zero]

lemma eta_six_slash_multiplier (γ : SL(2, ℤ)) : eta6 ∣[(3 : ℤ)] γ = eta6MultiplierFunction γ • eta6 := by
  obtain ⟨c, -, h⟩ := eta_six_slash_root_of_unity γ
  rw [eta6Mult0_eq h, h]

def eta6Mult : SL(2, ℤ) →* ℂ where
  toFun := eta6MultiplierFunction
  map_one' := eta6Mult0_eq (by simp)
  map_mul' x y := eta6Mult0_eq (by
    rw [SlashAction.slash_mul, eta_six_slash_multiplier, SL_smul_slash, eta_six_slash_multiplier, smul_smul])

lemma eta6Mult_T_eq_I : eta6Mult ModularGroup.T = Complex.I := eta6Mult0_eq eta6_slash_three_T_eq_I_smul

lemma eta6Mult_S : eta6Mult ModularGroup.S = Complex.I := eta6Mult0_eq eta_six_slash_S

lemma eta6Mult_neg_one : eta6Mult (-1) = -1 := by
  have : (-1 : SL(2, ℤ)) = ModularGroup.S * ModularGroup.S := by decide
  rw [this, map_mul, eta6Mult_S, I_mul_I]

def eta6Group : Subgroup SL(2, ℤ) := eta6Mult.toHomUnits.ker

lemma mem_eta6Group (γ : SL(2, ℤ)) : γ ∈ eta6Group ↔ eta6Mult γ = 1 := by
  simp [eta6Group, MonoidHom.mem_ker, Units.ext_iff]

lemma neg_one_not_mem_eta6Group : (-1 : SL(2, ℤ)) ∉ eta6Group := by
  rw [mem_eta6Group, eta6Mult_neg_one]; norm_num

end EtaSix

end GlobalTheory.HeckeFamilyMatrices
end
end
