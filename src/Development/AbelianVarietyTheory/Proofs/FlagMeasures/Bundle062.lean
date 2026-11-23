module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle045
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle046
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
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
public import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle043
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
public import Mathlib.RingTheory.Valuation.Discrete.RankOne

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

noncomputable section

namespace GlobalTheory.SnMass.VolN.IntU

theorem hpk_row (k r : ℕ) (a : Fin r) (j : Fin (2 * r + k + 1)) :
    Hpk k r (esI k r a) j = if j = eI k r a then 1 else 0 := by
  simp only [Hpk, esI, eI, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem hpk_mulVec_esI (k r : ℕ) (a : Fin r) (z : Fin (2 * r + k + 1) → ℂ) :
    (Hpk k r *ᵥ z) (esI k r a) = z (eI k r a) := by
  simp [Matrix.mulVec, dotProduct, hpk_row]

theorem coord_eI {E : Type} [Field E] {k r : ℕ} (σ : E →+* E) (τ : E →+* ℂ)
    (hτ : ∀ x, τ (σ x) = star (τ x)) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E)
    (B : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hB : Bᴴ * Hpk k r * B = J.map τ)
    (x y : Fin (2 * r + k + 1) → E) (a : Fin r) (s : ℝ) (hs : s ≠ 0)
    (hy : B *ᵥ (fun i => τ (y i)) = (s : ℂ)⁻¹ • bvec (esI k r a)) :
    (B *ᵥ fun i => τ (x i)) (eI k r a) = (s : ℂ) * τ (form σ J x y) := by
  have key : star (B *ᵥ (fun i => τ (y i))) ⬝ᵥ (Hpk k r *ᵥ (B *ᵥ fun i => τ (x i))) =
      star (fun i => τ (y i)) ⬝ᵥ (J.map τ *ᵥ fun i => τ (x i)) := by
    rw [← hB]
    simp only [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.mulVec_mulVec,
      Matrix.mul_assoc]
  have lhs : star (B *ᵥ (fun i => τ (y i))) ⬝ᵥ (Hpk k r *ᵥ (B *ᵥ fun i => τ (x i))) =
      (s : ℂ)⁻¹ * (B *ᵥ fun i => τ (x i)) (eI k r a) := by
    rw [hy, star_smul, bvec, ← hpk_mulVec_esI k r a (B *ᵥ fun i => τ (x i))]
    simp [Pi.star_def, dotProduct, Pi.single_apply, -Matrix.mulVec_mulVec]
  have rhs : star (fun i => τ (y i)) ⬝ᵥ (J.map τ *ᵥ fun i => τ (x i)) = τ (form σ J x y) := by

    simp only [form, dotProduct, map_sum, map_mul, hτ, RingHom.map_mulVec]
    rfl
  rw [lhs, rhs] at key
  rw [← key, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hs), one_mul]

end GlobalTheory.SnMass.VolN.IntU

namespace GlobalTheory.SnMass.VolN.IntU

theorem form_smul_smul {E : Type} [Field E] {n : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E)
    (c c' : E) (x y : Fin n → E) : form σ J (c • x) (c' • y) = c * σ c' * form σ J x y := by
  simp only [form, dotProduct, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem mem_of_pair {E : Type} [Field E] [NumberField E] (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x)
    (𝔞 𝔟 : FractionalIdeal (𝓞 E)⁰ E) (h𝔞 : 𝔞 ≠ 0) (h𝔟 : 𝔟 ≠ 0) (hst : FrameDual.Stab σ 𝔞⁻¹) (u : E)
    (hu : ∀ c ∈ 𝔟, ∀ c' ∈ 𝔞⁻¹, c * σ c' * u ∈ (algebraMap (𝓞 E) E).range) : u ∈ 𝔞 * 𝔟⁻¹ := by
  have hI : 𝔟 * 𝔞⁻¹ ≠ 0 := mul_ne_zero h𝔟 (inv_ne_zero h𝔞)
  have e : 𝔞 * 𝔟⁻¹ = (𝔟 * 𝔞⁻¹)⁻¹ := by rw [mul_inv, inv_inv, mul_comm]
  rw [e, FractionalIdeal.mem_inv_iff hI]
  intro y hy
  refine FractionalIdeal.mul_induction_on hy (fun c hc d hd => ?_) (fun y₁ y₂ h₁ h₂ => ?_)
  · have := hu c hc (σ d) (hst d hd)
    rw [hσ] at this
    obtain ⟨t, ht⟩ := this
    exact (FractionalIdeal.mem_one_iff _).2 ⟨t, by rw [ht]; ring⟩
  · rw [mul_add]; exact Submodule.add_mem (1 : FractionalIdeal (𝓞 E)⁰ E).coeToSubmodule h₁ h₂

end GlobalTheory.SnMass.VolN.IntU


open GlobalTheory.SnMass.VolN.IntU in
theorem GlobalTheory.SnMass.VolN.gM_entry_mem_ideLat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ γ ∈ GN (σ : E →+* E) J Λ P, ∀ p : UTr r, (fun w => gM A γ w (eI k r p.1.1) (eI k r p.1.2)) ∈ ideLat (dInv E (r - p.1.1.val) * (dInv E (r - p.1.2.val))⁻¹) (s p.1.1 / s p.1.2) := by
  intro F E _ _ _ _ _ σ k r J Λ P f T A s hV γ hγ p
  obtain ⟨hCM, -, hND, hSD, -, -, hTup, hMod, hs, hAd⟩ := hV
  obtain ⟨⟨a, b⟩, hab⟩ := p
  dsimp only
  have hconj : ∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x) := hCM.2.2.2
  have hσ : ∀ x, (σ : E →+* E) ((σ : E →+* E) x) = x := by
    intro x
    show σ (σ x) = x
    exact (Classical.arbitrary (InfinitePlace E)).embedding.injective (by rw [hconj, hconj, star_star])
  set eb : Fin (2 * r + k + 1) → E := fun i => P i b.castSucc with heb
  set fa : Fin (2 * r + k + 1) → E := fun i => f i a with hfa
  refine ⟨form (σ : E →+* E) J (γ *ᵥ eb) fa, ?_, fun w => ?_⟩
  · refine mem_of_pair (σ : E →+* E) hσ _ _ (FrameDual.dInv_ne_zero _) (FrameDual.dInv_ne_zero _)
      ((FrameDual.stab_dInv hσ _).inv hσ (FrameDual.dInv_ne_zero _)) _ ?_
    intro c hc c' hc'
    have h1 : c • eb ∈ Λ := hTup (Submodule.subset_span
      ⟨Fin.castAdd r b.castSucc, c, by rw [FrameDual.frameDualTupleIdeals_castAdd]; exact hc, by
        funext i; simp [heb, sideM]⟩)
    have h2 : c' • fa ∈ Λ := hTup (Submodule.subset_span
      ⟨Fin.natAdd (r + 1) a, c', by rw [FrameDual.frameDualTupleIdeals_natAdd]; exact hc', by
        funext i; simp [hfa, sideM]⟩)
    have h3 : γ *ᵥ (c • eb) ∈ Λ := by
      rw [← hγ.2]; exact ⟨_, h1, rfl⟩
    have h4 := (hSD.2 _).1 h3 _ h2
    rwa [Matrix.mulVec_smul, form_smul_smul] at h4
  · set τ := w.embedding with hτ
    have hB := hMod w
    have hdet : IsUnit (A w).det := by
      refine Ne.isUnit fun h0 => hND.2 ?_
      have := congrArg Matrix.det hB
      rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at this
      exact (map_eq_zero τ).1 this.symm
    have hsb : (s b : ℂ) ≠ 0 := by exact_mod_cast (hs b).ne'
    have hbv : bvec (eI k r b) = (s b : ℂ)⁻¹ • (A w *ᵥ fun i => τ (eb i)) := by
      rw [(hAd w b).1, smul_smul, inv_mul_cancel₀ hsb, one_smul]
    have hmap : (γ.map τ *ᵥ fun i => τ (eb i)) = fun i => τ ((γ *ᵥ eb) i) := by
      funext i; exact (RingHom.map_mulVec τ γ eb i).symm
    have hent : gM A γ w (eI k r a) (eI k r b) =
        (s b : ℂ)⁻¹ * (A w *ᵥ fun i => τ ((γ *ᵥ eb) i)) (eI k r a) := by
      have e1 : gM A γ w (eI k r a) (eI k r b) = (gM A γ w *ᵥ bvec (eI k r b)) (eI k r a) := by
        simp [bvec]
      rw [e1, hbv, Matrix.mulVec_smul, gM, Matrix.mulVec_mulVec, Matrix.mul_assoc (A w * γ.map τ),
        Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one, ← Matrix.mulVec_mulVec, hmap]
      rfl
    show gM A γ w (eI k r a) (eI k r b) = _
    rw [hent, coord_eI (σ : E →+* E) τ (hconj τ) J (A w) hB (γ *ᵥ eb) fa a (s a) (hs a).ne' (hAd w a).2]
    push_cast
    ring
end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN

section Corner

variable {E : Type} [Field E] [NumberField E]

omit [NumberField E] in
theorem form_smul_smul' (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : E) (u v : Fin n → E) :
    form σ J (y • u) (x • v) = σ x * y * form σ J u v := by
  simp only [form, Matrix.mulVec_smul, dotProduct, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem form_mem_dInv_mul (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (hΛ : GlobalTheory.SgGlob.SelfDual σ J Λ) (i j : ℕ) (u v : Fin n → E)
    (hu : ∀ y ∈ (dInv E j)⁻¹, y • u ∈ Λ) (hv : ∀ x ∈ (dInv E i)⁻¹, x • v ∈ Λ) :
    form σ J u v ∈ dInv E i * dInv E j := by
  have h0 : dInv E i * dInv E j ≠ 0 :=
    mul_ne_zero (FrameDual.dInv_ne_zero i) (FrameDual.dInv_ne_zero j)
  rw [← inv_inv (dInv E i * dInv E j), FractionalIdeal.mem_inv_iff (inv_ne_zero h0)]
  intro z hz
  rw [mul_inv] at hz
  refine FractionalIdeal.mul_induction_on hz (fun x hx y hy => ?_) (fun a b ha hb => ?_)
  · have hsx : σ x ∈ (dInv E i)⁻¹ :=
      FrameDual.Stab.inv hσ (FrameDual.stab_dInv hσ i) (FrameDual.dInv_ne_zero i) x hx
    have h1 := (hΛ.2 (y • u)).1 (hu y hy) ((σ x) • v) (hv _ hsx)
    rw [form_smul_smul', hσ] at h1
    obtain ⟨d, hd⟩ := h1
    refine (FractionalIdeal.mem_one_iff _).2 ⟨d, ?_⟩
    rw [hd]; ring
  · rw [mul_add]; exact Submodule.add_mem (1 : FractionalIdeal (𝓞 E)⁰ E).coeToSubmodule ha hb

end Corner

theorem Hpk_esI_apply (k r : ℕ) (a : Fin r) (j : Fin (2 * r + k + 1)) :
    Hpk k r (esI k r a) j = if j = eI k r a then 1 else 0 := by
  have ha := a.isLt
  have hj := j.isLt
  unfold Hpk
  simp only [esI, eI, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

end GlobalTheory.SnMass.VolN

namespace GlobalTheory.SnMass.VolN

theorem Hpk_mulVec_esI (k r : ℕ) (a : Fin r) (v : Fin (2 * r + k + 1) → ℂ) :
    (Hpk k r *ᵥ v) (esI k r a) = v (eI k r a) := by
  simp only [Matrix.mulVec, dotProduct, Hpk_esI_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem map_mulVec_comp {E : Type} [Field E] (φ : E →+* ℂ) {n : ℕ} (γ : Matrix (Fin n) (Fin n) E)
    (v : Fin n → E) : (γ.map φ) *ᵥ (fun i => φ (v i)) = fun i => φ ((γ *ᵥ v) i) := by
  funext i

  simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem corner_entry {E : Type} [Field E] (σ : E →+* E) (φ : E →+* ℂ) (hφ : ∀ x, φ (σ x) = star (φ x))
    {k r : ℕ} (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (hJ : J.det ≠ 0)
    (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hM : Mᴴ * Hpk k r * M = J.map φ)
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (a b : Fin r) (fa fb : Fin (2 * r + k + 1) → E)
    (sa sb : ℝ) (hsa : sa ≠ 0) (hsb : sb ≠ 0)
    (ha : M *ᵥ (fun i => φ (fa i)) = ((sa : ℂ)⁻¹) • bvec (esI k r a))
    (hb : M *ᵥ (fun i => φ (fb i)) = ((sb : ℂ)⁻¹) • bvec (esI k r b)) :
    (M * γ.map φ * M⁻¹) (eI k r a) (esI k r b) = ((sa * sb : ℝ) : ℂ) * φ (form σ J (γ *ᵥ fb) fa) := by
  have hsa' : (sa : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hsa
  have hsb' : (sb : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hsb
  have hdet : (J.map φ).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact (map_ne_zero φ).2 hJ
  have hU : IsUnit M.det := by
    refine isUnit_iff_ne_zero.2 fun h => hdet ?_
    rw [← hM, Matrix.det_mul, h, mul_zero]
  have hinv : M⁻¹ *ᵥ bvec (esI k r b) = (sb : ℂ) • fun i => φ (fb i) := by
    have e1 : M⁻¹ *ᵥ (M *ᵥ (fun i => φ (fb i))) = fun i => φ (fb i) := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hU, Matrix.one_mulVec]
    rw [hb, Matrix.mulVec_smul] at e1
    rw [← e1, smul_smul, mul_inv_cancel₀ hsb', one_smul]
  have hreal : star (M *ᵥ (fun i => φ (fa i))) = M *ᵥ (fun i => φ (fa i)) := by
    rw [ha]; funext j
    simp only [Pi.star_apply, Pi.smul_apply, bvec, Pi.single_apply, smul_eq_mul]
    split_ifs <;> simp
  have hbv : bvec (esI k r a) = (sa : ℂ) • (M *ᵥ (fun i => φ (fa i))) := by
    rw [ha, smul_smul, mul_inv_cancel₀ hsa', one_smul]
  set X : Fin (2 * r + k + 1) → ℂ := fun i => φ ((γ *ᵥ fb) i) with hX
  have h1 : (M * γ.map φ * M⁻¹) (eI k r a) (esI k r b) = (sb : ℂ) * (M *ᵥ X) (eI k r a) := by
    have : (M * γ.map φ * M⁻¹) (eI k r a) (esI k r b) =
        ((M * γ.map φ * M⁻¹) *ᵥ bvec (esI k r b)) (eI k r a) := by
      simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [this, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hinv, Matrix.mulVec_smul,
      map_mulVec_comp, Matrix.mulVec_smul]
    rfl
  have h2 : (M *ᵥ X) (eI k r a) = (sa : ℂ) * (star (fun i => φ (fa i)) ⬝ᵥ ((J.map φ) *ᵥ X)) := by
    rw [← Hpk_mulVec_esI k r a (M *ᵥ X)]
    have e2 : (Hpk k r *ᵥ (M *ᵥ X)) (esI k r a) = bvec (esI k r a) ⬝ᵥ (Hpk k r *ᵥ (M *ᵥ X)) := by
      simp [bvec]
    rw [e2, hbv, smul_dotProduct, smul_eq_mul, ← hreal, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM]
  have h3 : star (fun i => φ (fa i)) ⬝ᵥ ((J.map φ) *ᵥ X) = φ (form σ J (γ *ᵥ fb) fa) := by
    rw [hX, map_mulVec_comp]

    simp [form, dotProduct, map_sum, map_mul, hφ]
  rw [h1, h2, h3]
  push_cast; ring

end GlobalTheory.SnMass.VolN

namespace GlobalTheory.SnMass.VolN

theorem corner_entry_mem_ideLat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ γ ∈ GN (σ : E →+* E) J Λ P, ∀ p : UTr r, (fun w => gM A γ w (eI k r p.1.1) (esI k r p.1.2)) ∈ ideLat (dInv E (r - p.1.1.val) * dInv E (r - p.1.2.val)) (s p.1.1 * s p.1.2) := by
  intro F E _ _ _ _ _ σ k r J Λ P f T A s hD γ hγ p
  obtain ⟨hCM, -, hJ, hΛ, -, -, hlat, hA, hs, had⟩ := hD
  obtain ⟨-, -, -, hcc⟩ := hCM
  obtain ⟨-, hγΛ⟩ := hγ
  have hσ : ∀ x, (σ : E →+* E) ((σ : E →+* E) x) = x := by
    intro x
    let τ : E →+* ℂ := Classical.arbitrary _
    apply τ.injective
    change τ (σ (σ x)) = τ x
    rw [hcc, hcc, star_star]
  have hcol : ∀ (b : Fin r) (y : E), y ∈ (dInv E (r - (b : ℕ)))⁻¹ → y • (fun i => f i b) ∈ Λ := by
    intro b y hy
    refine hlat (Submodule.subset_span ⟨Fin.natAdd (r + 1) b, y, ?_, ?_⟩)
    · simpa [id1] using hy
    · funext i; simp [sideM]
  have hmap : ∀ v ∈ Λ, γ *ᵥ v ∈ Λ := by
    intro v hv
    have : γ *ᵥ v ∈ latMap γ Λ := ⟨v, hv, rfl⟩
    rwa [hγΛ] at this
  have hc : form (σ : E →+* E) J (γ *ᵥ fun i => f i p.1.2) (fun i => f i p.1.1) ∈
      dInv E (r - p.1.1.val) * dInv E (r - p.1.2.val) := by
    refine form_mem_dInv_mul (σ : E →+* E) hσ J Λ hΛ _ _ _ _ (fun y hy => ?_) (fun x hx => hcol _ x hx)
    rw [← Matrix.mulVec_smul]
    exact hmap _ (hcol _ y hy)
  refine ⟨_, hc, fun w => ?_⟩
  have hJ0 : J.det ≠ 0 := hJ.2
  have hφ : ∀ x, w.embedding ((σ : E →+* E) x) = star (w.embedding x) := fun x => hcc _ x
  have := corner_entry (σ : E →+* E) w.embedding hφ J hJ0 (A w) (hA w) γ p.1.1 p.1.2
    (fun i => f i p.1.1) (fun i => f i p.1.2) (s p.1.1) (s p.1.2) (hs _).ne' (hs _).ne'
    (had w p.1.1).2 (had w p.1.2).2
  simp only [gM]
  rw [this]

end GlobalTheory.SnMass.VolN
end
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.NonGenericCompare
open scoped Pointwise ENNReal Classical

noncomputable section

namespace GlobalTheory.LocFieldOfDVR

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Topology
open scoped WithZero

theorem exists_pow_lt_of_lt_one (a c : ℤᵐ⁰) (ha : a ≠ 0) (ha1 : a < 1) (hc : c ≠ 0) :
    ∃ n : ℕ, a ^ n < c := by
  obtain ⟨a', rfl⟩ := WithZero.ne_zero_iff_exists.mp ha
  obtain ⟨c', rfl⟩ := WithZero.ne_zero_iff_exists.mp hc
  refine ⟨(Multiplicative.toAdd c').natAbs + 1, ?_⟩
  rw [← WithZero.coe_pow, WithZero.coe_lt_coe]
  rw [← WithZero.coe_one, WithZero.coe_lt_coe] at ha1
  rw [← Multiplicative.toAdd_lt, toAdd_pow, nsmul_eq_mul]
  rw [← Multiplicative.toAdd_lt, toAdd_one] at ha1
  push_cast
  have ha2 : Multiplicative.toAdd a' ≤ -1 := by omega
  nlinarith [mul_le_mul_of_nonneg_left ha2 (by positivity : (0 : ℤ) ≤ |Multiplicative.toAdd c'| + 1),
    neg_abs_le (Multiplicative.toAdd c')]

variable (o F : Type) [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [Field F] [Algebra o F]
  [IsFractionRing o F]

abbrev val : Valuation F ℤᵐ⁰ := (IsDiscreteValuationRing.maximalIdeal o).valuation F

abbrev valued : Valued F ℤᵐ⁰ := Valued.mk' (val o F)

def equivInt : o ≃+* (val o F).integer :=
  RingEquiv.ofBijective
    ((algebraMap o F).codRestrict (val o F).integer (fun a => valuation_le_one _ a))
    ⟨fun a b h => IsFractionRing.injective o F (congrArg Subtype.val h),
     fun x => by
      obtain ⟨a, ha⟩ := IsDiscreteValuationRing.exists_lift_of_le_one x.2
      exact ⟨a, Subtype.ext ha⟩⟩

@[simp] theorem equivInt_val (a : o) : ((equivInt o F a : (val o F).integer) : F) = algebraMap o F a := rfl

variable {o F}

theorem mem_pow_iff {ϖ : o} (hϖ : Irreducible ϖ) (n : ℕ) (x : (val o F).integer) :
    x ∈ ((IsLocalRing.maximalIdeal o).map (equivInt o F)) ^ n ↔
      val o F (x : F) ≤ val o F (algebraMap o F ϖ) ^ n := by
  rw [← Ideal.map_pow, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.map_span,
    Set.image_singleton, Ideal.mem_span_singleton, (Valuation.integer.integers _).dvd_iff_le]
  simp only [map_pow, equivInt_val]
  exact Iff.rfl

end GlobalTheory.LocFieldOfDVR

namespace GlobalTheory.LocFieldOfDVR
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Topology
open scoped WithZero
variable {o F : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [Field F] [Algebra o F]
  [IsFractionRing o F]

theorem isAdic_map {ϖ : o} (hϖ : Irreducible ϖ) :
    letI := valued o F
    IsAdic ((IsLocalRing.maximalIdeal o).map (equivInt o F)) := by
  letI := valued o F
  set J := (IsLocalRing.maximalIdeal o).map (equivInt o F)
  set π := algebraMap o F ϖ
  have hπ0 : val o F π ≠ 0 := by
    simp only [π, ne_eq, map_eq_zero]
    exact (IsFractionRing.injective o F).ne_iff' (map_zero _) |>.mpr hϖ.ne_zero
  have hπ1 : val o F π < 1 := (valuation_lt_one_iff_mem _ ϖ).mpr
    (by simpa [IsDiscreteValuationRing.maximalIdeal] using hϖ.not_isUnit)
  rw [isAdic_iff]
  refine ⟨fun n => ?_, fun s hs => ?_⟩
  · refine AddSubgroup.isOpen_of_mem_nhds (J ^ n).toAddSubgroup (g := 0) ?_
    rw [mem_nhds_subtype]
    refine ⟨{y | val o F y < val o F π ^ n}, ?_, fun y hy => ?_⟩
    · change _ ∈ 𝓝 (0 : F)
      rw [Valued.mem_nhds_zero]
      have hπne : π ≠ 0 := by rintro h; simp [h] at hπ0
      refine ⟨Units.mk0 ((val o F).restrict (π ^ n)) (by simp [hπne]), fun y hy => ?_⟩
      simp only [Units.val_mk0, Set.mem_setOf_eq] at hy ⊢
      have hy' : (val o F).restrict y < (val o F).restrict (π ^ n) := hy
      rw [Valuation.restrict_lt_iff] at hy'
      simpa [map_pow] using hy'
    · exact (mem_pow_iff hϖ n y).mpr (le_of_lt hy)
  · obtain ⟨u, hu, hus⟩ := (mem_nhds_subtype _ _ _).mp hs
    obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hu
    have hγ0 : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one _ _ hπ0 hπ1 hγ0
    refine ⟨n, fun y hy => hus (hγ ?_)⟩
    simp only [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding]
    exact ((mem_pow_iff hϖ n y).mp hy).trans_lt hn

end GlobalTheory.LocFieldOfDVR

namespace GlobalTheory.LocFieldOfDVR
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Topology
open scoped WithZero
variable {o F : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [Field F] [Algebra o F]
  [IsFractionRing o F]

theorem compactSpace_integer [IsAdicComplete (IsLocalRing.maximalIdeal o) o]
    [Finite (IsLocalRing.ResidueField o)] :
    letI := valued o F
    CompactSpace (Valued.integer F) := by
  letI := valued o F
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible o
  letI : (Valued.v : Valuation F ℤᵐ⁰).RankOne :=
    Valuation.IsRankOneDiscrete.rankOne (val o F) (e := 2) one_lt_two
  have hI := isAdic_map (F := F) hϖ
  have hpre : IsPrecomplete ((IsLocalRing.maximalIdeal o).map (equivInt o F)) (val o F).integer :=
    (IsPrecomplete.congr_ringEquiv _ _).mpr inferInstance
  haveI : IsUniformAddGroup (val o F).integer :=
    inferInstanceAs (IsUniformAddGroup (val o F).integer.toAddSubgroup)
  have hcomp : CompleteSpace (val o F).integer := (IsAdic.isPrecomplete_iff hI).mp hpre
  have hdvr : IsDiscreteValuationRing (Valued.integer F) :=
    inferInstanceAs (IsDiscreteValuationRing (val o F).integer)
  have hfin : Finite (IsLocalRing.ResidueField (Valued.integer F)) :=
    Finite.of_equiv _ (IsLocalRing.ResidueField.mapEquiv (equivInt o F)).toEquiv
  exact Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mpr
    ⟨hcomp, hdvr, hfin⟩

theorem locallyCompactSpace [IsAdicComplete (IsLocalRing.maximalIdeal o) o]
    [Finite (IsLocalRing.ResidueField o)] :
    letI := valued o F
    LocallyCompactSpace F := by
  letI := valued o F
  have := compactSpace_integer (o := o) (F := F)
  exact IsCompact.locallyCompactSpace_of_mem_nhds_of_addGroup
    (isCompact_iff_compactSpace.mpr this) ((Valued.isOpen_integer F).mem_nhds (zero_mem _))

end GlobalTheory.LocFieldOfDVR

namespace GlobalTheory.LocFieldOfDVR
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Topology
open scoped WithZero

theorem exists_isNonarchimedeanLocalField : ∀ (o F : Type) [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [IsAdicComplete (IsLocalRing.maximalIdeal o) o] [Finite (IsLocalRing.ResidueField o)] [Field F] [Algebra o F] [IsFractionRing o F], ∃ (_ : ValuativeRel F) (_ : TopologicalSpace F), IsNonarchimedeanLocalField F ∧ ∀ x : F, x ∈ 𝒪[F] ↔ ∃ a : o, algebraMap o F a = x := by
  intro o F _ _ _ _ _ _ _ _
  letI := valued o F
  letI vr : ValuativeRel F := .ofValuation (val o F)
  haveI : (val o F).Compatible := .ofValuation _
  refine ⟨vr, inferInstance, ?_, fun x => ?_⟩
  · have h1 : IsValuativeTopology F :=
      IsValuativeTopology.of_mem_nhds_iff_vle (val o F) (fun {s x} => Valued.mem_nhds)
    have h2 : ValuativeRel.IsNontrivial F :=
      (ValuativeRel.isNontrivial_iff_isNontrivial (val o F)).mpr inferInstance
    have h3 : LocallyCompactSpace F := locallyCompactSpace (o := o) (F := F)
    exact {}
  · rw [Valuation.mem_integer_iff, ← (ValuativeRel.valuation F).vle_one_iff, (val o F).vle_one_iff]
    exact ⟨IsDiscreteValuationRing.exists_lift_of_le_one,
      fun ⟨a, ha⟩ => ha ▸ valuation_le_one _ a⟩

end GlobalTheory.LocFieldOfDVR
end
end
