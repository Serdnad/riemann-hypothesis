module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1239
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle074
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1240
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle156
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryCentralizerEquivNormOneTorus
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
import Mathlib.RingTheory.Artinian.Instances
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

namespace GlobalTheory.KapLat

theorem stdH_mulVec_of_mem {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n : ℕ)
    (y : GLw n w) (hy : y ∈ UJ (cj w) 1) (v v' : Fin n → w.adicCompletion E) :
    stdH w (y.val *ᵥ v) (y.val *ᵥ v') = stdH w v v' := by
  have h1 : (cT (cj w) y.val) * 1 * y.val = 1 := hy
  have h2 : (y.val)ᵀ * y.val.map (cj w) = 1 := by
    have := congrArg Matrix.transpose h1
    simpa [cT, Matrix.transpose_mul] using this
  have hs : ∀ z : Fin n → w.adicCompletion E, ∀ z', stdH w z z' = z ⬝ᵥ (fun k => cj w (z' k)) := by
    intro z z'; rfl
  have hc : (fun k => cj w ((y.val *ᵥ v') k)) = y.val.map (cj w) *ᵥ (fun k => cj w (v' k)) := by
    funext k; exact RingHom.map_mulVec (cj w) y.val v' k
  rw [hs, hs, hc, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, h2,
    Matrix.vecMul_one]

theorem isReduced_of_adjoin_squarefree {F A : Type} [Field F] [CommRing A] [Algebra F A] [Module.Finite F A]
    (u : A) (hu : Algebra.adjoin F {u} = ⊤) (P : F[X]) (hP : Squarefree P) (hPu : aeval u P = 0) :
    IsReduced A := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨k, hk⟩ := ha
  have hmem : a ∈ Algebra.adjoin F {u} := by rw [hu]; trivial
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hmem
  obtain ⟨p, rfl⟩ := hmem
  have hsq : Squarefree (minpoly F u) := hP.squarefree_of_dvd (minpoly.dvd F u hPu)
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  ·
    have h10 : (1 : A) = 0 := by simpa using hk
    exact (subsingleton_of_zero_eq_one h10.symm).elim _ _
  have hd : minpoly F u ∣ p ^ k := minpoly.dvd F u (by rw [map_pow]; exact hk)
  have hd' : minpoly F u ∣ p := (hsq.dvd_pow_iff_dvd hk0.ne').1 hd
  obtain ⟨r, hr⟩ := hd'
  change aeval u p = 0
  rw [hr, map_mul, minpoly.aeval, zero_mul]

theorem model_conj_norm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w →
    ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E) (n : ℕ) (Q : (w.adicCompletion E)[X])
    (B : GlobalTheory.UnitLemma.InvAlg K) (u x x' : B.A), Q.Separable → Fits w e B Q u →
    ∀ γ y : GLw n w, y ∈ UL n w → IsModel w e B u x γ → IsModel w e B u x' (y⁻¹ * γ * y) →
    ∃ c : B.Aˣ, x' = x * ((c : B.A) * B.σ (c : B.A)) := by
  intro E _ _ _ w hw K e n Q B u x x' hQ hF γ y hy hM hM'
  obtain ⟨hadj, hroot, -, -⟩ := hF
  have hyU : y ∈ UJ (cj w) 1 := by simpa [UL, hw] using hy
  obtain ⟨ψ, hψs, hψu, hψh⟩ := hM
  obtain ⟨ψ', hψs', hψu', hψh'⟩ := hM'

  let ψ₃ : B.A → (Fin n → w.adicCompletion E) := fun a => y.val *ᵥ ψ' a
  have h3s : ∀ (c : K.E) (a : B.A), ψ₃ (c • a) = e c • ψ₃ a := by
    intro c a; simp only [ψ₃, hψs', Matrix.mulVec_smul]
  have h3u : ∀ a, ψ₃ (u * a) = γ.val *ᵥ ψ₃ a := by
    intro a
    simp only [ψ₃, hψu', Matrix.mulVec_mulVec, Units.val_mul]
    congr 1
    rw [← mul_assoc, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
  have h3h : ∀ a b, stdH w (ψ₃ a) (ψ₃ b) = e (B.herm x' a b) := by
    intro a b; simp only [ψ₃]; rw [stdH_mulVec_of_mem w n y hyU, hψh']

  let φ : B.A → B.A := fun a => ψ.symm (ψ₃ a)
  have hφψ : ∀ a, ψ (φ a) = ψ₃ a := fun a => ψ.apply_symm_apply _
  have hφs : ∀ (c : K.E) (a : B.A), φ (c • a) = c • φ a := by
    intro c a; apply ψ.injective; rw [hψs, hφψ, hφψ, h3s]
  have hφu : ∀ a, φ (u * a) = u * φ a := by
    intro a; apply ψ.injective; rw [hψu, hφψ, hφψ, h3u]
  have hφadd : ∀ a b, φ (a + b) = φ a + φ b := by
    intro a b; apply ψ.injective; rw [map_add (f := _), hφψ, hφψ, hφψ]; simp [ψ₃, Matrix.mulVec_add]

  have hφmul : ∀ a b, φ (a * b) = a * φ b := by
    intro a
    have ha : a ∈ Algebra.adjoin K.E {u} := by rw [hadj]; trivial
    induction ha using Algebra.adjoin_induction with
    | mem z hz =>
      rw [Set.mem_singleton_iff] at hz; subst hz; exact hφu
    | algebraMap r =>
      intro b; rw [← Algebra.smul_def, ← Algebra.smul_def, hφs]
    | add a₁ a₂ _ _ h₁ h₂ =>
      intro b; rw [add_mul, hφadd, h₁, h₂, add_mul]
    | mul a₁ a₂ _ _ h₁ h₂ =>
      intro b; rw [mul_assoc, h₁, h₂, mul_assoc]
  have hφ : ∀ a, φ a = a * φ 1 := fun a => by rw [← hφmul, mul_one]

  obtain ⟨a₀, ha₀⟩ : ∃ a₀, φ a₀ = 1 := by
    refine ⟨ψ'.symm ((y⁻¹ : GLw n w).val *ᵥ ψ 1), ?_⟩
    apply ψ.injective
    rw [hφψ]
    simp only [ψ₃, AddEquiv.apply_symm_apply, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.one_mulVec]
  let c : B.Aˣ := ⟨φ 1, a₀, by rw [mul_comm, ← hφ, ha₀], by rw [← hφ, ha₀]⟩
  refine ⟨c, ?_⟩

  have hh : ∀ a b, B.herm x' a b = B.herm x (φ a) (φ b) := by
    intro a b; apply e.injective; rw [← h3h, ← hψh, hφψ, hφψ]
  have htr : ∀ z : B.A, Algebra.trace K.E B.A ((x * ((c : B.A) * B.σ (c : B.A)) - x') * z) = 0 := by
    intro z
    have := hh z 1
    simp only [GlobalTheory.UnitLemma.InvAlg.herm, map_one, mul_one] at this
    rw [hφ z] at this
    have hc : (c : B.A) = φ 1 := rfl
    rw [hc, sub_mul, map_sub, sub_eq_zero, this]
    congr 1; ring
  haveI : IsReduced B.A := isReduced_of_adjoin_squarefree u hadj _ (hQ.map.squarefree) hroot
  exact (sub_eq_zero.1 (GlobalTheory.RegSS.eq_zero_of_trace_mul_eq_zero _ htr)).symm

end GlobalTheory.KapLat
end

section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.TwLatCoset

variable {E : Type} [Field E] [NumberField E] {w : Pl E} {K : GlobalTheory.UnitLemma.UQ}
  (e : K.E ≃+* w.adicCompletion E) {B : GlobalTheory.UnitLemma.InvAlg K} {m : ℕ} (b : Module.Basis (Fin m) K.E B.A)

def vec (y : Fin m → w.adicCompletion E) : B.A := ∑ i, e.symm (y i) • b i

def crd (a : B.A) : Fin m → w.adicCompletion E := fun i => e (b.repr a i)

def IntV (y : Fin m → w.adicCompletion E) : Prop := ∀ i, y i ∈ Ov E w

lemma vec_crd (a : B.A) : vec e b (crd e b a) = a := by
  simp [vec, crd, b.sum_repr]

lemma crd_vec (y : Fin m → w.adicCompletion E) : crd e b (vec e b y) = y := by
  funext i; simp only [vec, crd]; rw [Module.Basis.repr_sum_self]; simp

lemma sum_cols (M : Matrix (Fin m) (Fin m) (w.adicCompletion E)) (x : Fin m → w.adicCompletion E) :
    ∑ j, e.symm (x j) • vec e b (fun i => M i j) = vec e b (M *ᵥ x) := by

  simp only [vec, Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.smul_sum, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]

lemma memOv (x : w.adicCompletion E) : x ∈ Ov E w ↔ Valued.v x ≤ 1 := by
  simp [Ov, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]

lemma intV_mulVec {M : Matrix (Fin m) (Fin m) (w.adicCompletion E)} (hM : ∀ i j, M i j ∈ Ov E w)
    {z : Fin m → w.adicCompletion E} (hz : IntV z) : IntV (M *ᵥ z) := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hM i j) (hz j)

lemma intV_single (j : Fin m) : IntV (w := w) (Pi.single j 1) := by
  intro i
  rcases eq_or_ne i j with rfl | h
  · simp [Subring.one_mem]
  · simp [Pi.single_apply, h, Subring.zero_mem]

lemma gl_vec (h : GL (Fin m) (w.adicCompletion E)) (z : Fin m → w.adicCompletion E) :
    (↑h⁻¹ : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *ᵥ ((↑h : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *ᵥ z) = z := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

lemma gl_vec' (h : GL (Fin m) (w.adicCompletion E)) (z : Fin m → w.adicCompletion E) :
    (↑h : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *ᵥ ((↑h⁻¹ : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *ᵥ z) = z := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

lemma preserves_iff (h : GL (Fin m) (w.adicCompletion E)) :
    (∀ z, IntV ((↑h : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *ᵥ z) ↔ IntV z) ↔ h ∈ GLint (Fin m) (Ov E w) := by
  constructor
  · intro H
    have hh : ∀ i j, (↑h : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j ∈ Ov E w := by
      intro i j
      have := (H (Pi.single j 1)).2 (intV_single j) i
      simpa [Matrix.mulVec_single_one] using this
    have hi : ∀ i j, (↑h⁻¹ : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j ∈ Ov E w := by
      intro i j
      have := (H ((↑h⁻¹ : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *ᵥ Pi.single j 1)).1 (by rw [gl_vec']; exact intV_single j) i
      simpa [Matrix.mulVec_single_one] using this
    have inj : Function.Injective ((Ov E w).subtype.mapMatrix :
        Matrix (Fin m) (Fin m) (Ov E w) →+* Matrix (Fin m) (Fin m) (w.adicCompletion E)) := by
      intro A A' hAA
      exact Matrix.ext fun i j => Subtype.ext (congrArg (fun M : Matrix (Fin m) (Fin m) (w.adicCompletion E) => M i j) hAA)
    let M1 : Matrix (Fin m) (Fin m) (Ov E w) := Matrix.of fun i j => ⟨_, hh i j⟩
    let M2 : Matrix (Fin m) (Fin m) (Ov E w) := Matrix.of fun i j => ⟨_, hi i j⟩
    have e1 : (Ov E w).subtype.mapMatrix M1 = ↑h := Matrix.ext fun i j => rfl
    have e2 : (Ov E w).subtype.mapMatrix M2 = ↑h⁻¹ := Matrix.ext fun i j => rfl
    let k : GL (Fin m) (Ov E w) :=
      ⟨M1, M2, inj (by rw [map_mul, map_one, e1, e2, ← Units.val_mul, mul_inv_cancel, Units.val_one]),
        inj (by rw [map_mul, map_one, e1, e2, ← Units.val_mul, inv_mul_cancel, Units.val_one])⟩
    exact ⟨k, Units.ext (Matrix.ext fun i j => rfl)⟩
  · rintro ⟨k, rfl⟩ z
    have ent : ∀ (k : GL (Fin m) (Ov E w)) i j,
        ((bc (Ov E w).subtype k : GL (Fin m) (w.adicCompletion E)) : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j ∈ Ov E w :=
      fun k i j => (k.val i j).2
    constructor
    · intro hz
      have := intV_mulVec (ent k⁻¹) hz
      rwa [map_inv, gl_vec] at this
    · exact intV_mulVec (ent k)

lemma mem_lat (hI : ∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) (g : GLw m w) (a : B.A) :
    a ∈ GlobalTheory.TwLat.lat e b g ↔
      IntV ((↑g⁻¹ : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *ᵥ crd e b a) := by
  constructor
  · intro ha
    induction ha using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      have : crd e b (∑ i, e.symm ((↑g : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) • b i) =
          (↑g : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *ᵥ Pi.single j 1 := by
        rw [Matrix.mulVec_single_one]
        exact crd_vec e b _
      rw [this, gl_vec]
      exact intV_single j
    | zero =>
      have : crd e b (0 : B.A) = 0 := by funext i; simp [crd]
      rw [this, Matrix.mulVec_zero]
      intro i; exact Subring.zero_mem _
    | add x y _ _ hx hy =>
      have : crd e b (x + y) = crd e b x + crd e b y := by funext i; simp [crd]
      rw [this, Matrix.mulVec_add]
      intro i; exact Subring.add_mem _ (hx i) (hy i)
    | smul c x _ hx =>
      have hc : e (algebraMap K.O K.E c) ∈ Ov E w := (memOv _).2 ((hI _).1 ⟨c, rfl⟩)
      have : crd e b (c • x) = e (algebraMap K.O K.E c) • crd e b x := by
        funext i; simp only [crd, Pi.smul_apply, smul_eq_mul]; rw [← algebraMap_smul K.E c x, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul]
      rw [this, Matrix.mulVec_smul]
      intro i; exact Subring.mul_mem _ hc (hx i)
  · intro hx
    set x := (↑g⁻¹ : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *ᵥ crd e b a with hxdef
    have hr : ∀ j, e.symm (x j) ∈ (algebraMap K.O K.E).range := fun j =>
      (hI _).2 (by rw [RingEquiv.apply_symm_apply]; exact (memOv _).1 (hx j))
    choose c hc using hr
    have hsum : a = ∑ j, c j • vec e b (fun i => (↑g : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) := by
      simp_rw [← algebraMap_smul K.E (c _), hc]
      rw [sum_cols, hxdef, gl_vec', vec_crd]
    rw [hsum]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem lat_coset : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w →
    ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) →
    (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) →
    (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ)
    (b : Module.Basis (Fin m) K.E B.A),
    (∀ g g' : GLw m w, GlobalTheory.TwLat.lat e b g = GlobalTheory.TwLat.lat e b g' ↔ g⁻¹ * g' ∈ GlobalTheory.LFun.KGL w (n := m)) ∧
      ∀ g : GLw m w, GlobalTheory.UnitLemma.IsLat K.O K.E (GlobalTheory.TwLat.lat e b g) := by
  intro E _ _ _ _ w _ K e _ hI _ B m b
  refine ⟨fun g g' => ?_, fun g => ?_⟩
  · show _ ↔ g⁻¹ * g' ∈ GLint (Fin m) (Ov E w)
    rw [SetLike.ext_iff, ← preserves_iff]
    simp only [mem_lat e b hI]
    constructor
    · intro H z
      have := H (vec e b ((↑g' : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *ᵥ z))
      rw [crd_vec, gl_vec] at this
      rwa [Units.val_mul, ← Matrix.mulVec_mulVec]
    · intro H a
      have := H ((↑g'⁻¹ : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *ᵥ crd e b a)
      rwa [Units.val_mul, ← Matrix.mulVec_mulVec, gl_vec'] at this
  · refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
    rw [eq_top_iff]
    intro a _
    have hsum : a = ∑ j, e.symm (((↑g⁻¹ : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *ᵥ crd e b a) j) •
        vec e b (fun i => (↑g : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) := by
      rw [sum_cols, gl_vec', vec_crd]
    rw [hsum]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Submodule.subset_span ⟨j, rfl⟩))

end GlobalTheory.TwLatCoset
end
end

section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.TwLat

theorem betaSym_expand {K : GlobalTheory.UnitLemma.UQ} {B : GlobalTheory.UnitLemma.InvAlg K} {m : ℕ}
    (b : Module.Basis (Fin m) K.E B.A) (f : B.A →ₗ[K.E] K.E) (a : B.A) :
    f a = ∑ k, b.repr a k * f (b k) := by
  calc f a = f (∑ k, b.repr a k • b k) := by rw [b.sum_repr]
    _ = ∑ k, b.repr a k * f (b k) := by rw [map_sum]; simp only [map_smul, smul_eq_mul]

theorem betaSym_trace_sigma {K : GlobalTheory.UnitLemma.UQ} (B : GlobalTheory.UnitLemma.InvAlg K) (y : B.A) :
    Algebra.trace K.E B.A (B.σ y) = K.c (Algebra.trace K.E B.A y) := by
  have h := Algebra.trace_eq_of_equiv_equiv K.c B.σ (by ext e; simp [B.σ_alg]) y
  rw [h, RingEquiv.apply_symm_apply]

theorem betaSym : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A) (u β : B.A), (Algebra.traceForm K.E B.A).Nondegenerate → IsUnit (GlobalTheory.TwLat.gram e b β) → (cj w).mapMatrix (GlobalTheory.TwLat.gram e b β) = (-1 : w.adicCompletion E) ^ (m - 1) • ((GlobalTheory.TwLat.gram e b β)ᵀ * GlobalTheory.TwLat.mulMat e b u) → B.σ β = β * ((-1) ^ (m - 1) * u) ∧ IsUnit β := by
  intro E _ _ _ w K e he B m b u β hnd hG hsym

  let f : B.A → (B.A →ₗ[K.E] K.E) := fun z =>
    (Algebra.trace K.E B.A).comp ((LinearMap.mulRight K.E (B.σ z)).comp (LinearMap.mulLeft K.E β))
  have hf : ∀ y z, f z y = Algebra.trace K.E B.A (β * y * B.σ z) := fun y z => rfl
  have hsgn : ((-1 : B.A) ^ (m - 1)) = algebraMap K.E B.A ((-1) ^ (m - 1)) := by simp
  set x : B.A := B.σ β - β * ((-1) ^ (m - 1) * u) with hx
  have h1 : ∀ i j, Algebra.trace K.E B.A (x * b j * B.σ (b i)) = 0 := by
    intro i j
    have h := congrFun (congrFun hsym i) j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
      Matrix.transpose_apply, gram, mulMat, Matrix.of_apply, LinearMap.toMatrix_apply,
      LinearMap.mulLeft_apply, GlobalTheory.UnitLemma.InvAlg.herm] at h
    have hA : Algebra.trace K.E B.A (B.σ β * b j * B.σ (b i)) =
        K.c (Algebra.trace K.E B.A (β * b i * B.σ (b j))) := by
      rw [← betaSym_trace_sigma B]; congr 1; rw [map_mul, map_mul, B.σ_σ]; ring
    have hB : Algebra.trace K.E B.A (β * ((-1) ^ (m - 1) * u) * b j * B.σ (b i)) =
        (-1) ^ (m - 1) * ∑ k, b.repr (u * b j) k * Algebra.trace K.E B.A (β * b k * B.σ (b i)) := by
      have : β * ((-1) ^ (m - 1) * u) * b j * B.σ (b i) = ((-1 : K.E) ^ (m - 1)) • (β * (u * b j) * B.σ (b i)) := by
        rw [Algebra.smul_def, ← hsgn]; ring
      rw [this, map_smul, smul_eq_mul, ← hf, betaSym_expand b (f (b i)) (u * b j)]
      rfl
    have hsub : x * b j * B.σ (b i) = B.σ β * b j * B.σ (b i) - β * ((-1) ^ (m - 1) * u) * b j * B.σ (b i) := by
      rw [hx]; ring
    apply e.injective

    rw [hsub, map_sub, hA, hB, map_sub e, map_zero, he, h, map_mul e, map_sum e, map_pow, map_neg, map_one]
    simp only [map_mul e]
    rw [sub_eq_zero]; congr 1; refine Finset.sum_congr rfl fun k _ => ?_; ring
  have h2 : ∀ i a, Algebra.trace K.E B.A (x * B.σ (b i) * a) = 0 := by
    intro i a
    have h := betaSym_expand b ((Algebra.trace K.E B.A).comp (LinearMap.mulLeft K.E (x * B.σ (b i)))) a
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply] at h
    rw [h]
    apply Finset.sum_eq_zero
    intro j _
    rw [show x * B.σ (b i) * b j = x * b j * B.σ (b i) by ring, h1, mul_zero]
  have h3 : ∀ a, Algebra.trace K.E B.A (x * a) = 0 := by
    intro a
    have hs : ∀ i, Algebra.trace K.E B.A (B.σ (x * a) * b i) = 0 := by
      intro i
      have h := h2 i a
      rw [show x * B.σ (b i) * a = B.σ (B.σ (x * a) * b i) by rw [map_mul, B.σ_σ]; ring,
        betaSym_trace_sigma] at h
      exact (map_eq_zero_iff K.c K.c.injective).mp h
    have h4 := betaSym_expand b ((Algebra.trace K.E B.A).comp (LinearMap.mulLeft K.E (B.σ (x * a)))) 1
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, mul_one, hs, mul_zero, Finset.sum_const_zero,
      betaSym_trace_sigma] at h4
    exact (map_eq_zero_iff K.c K.c.injective).mp h4
  have hx0 : x = 0 := hnd.1 x (fun n => by simpa [Algebra.traceForm_apply] using h3 n)
  refine ⟨by rw [hx] at hx0; exact sub_eq_zero.mp hx0, ?_⟩
  by_contra hβ
  have hinj : ¬ Function.Injective (LinearMap.mulLeft K.E β) := by
    intro hi
    have hs := (LinearMap.injective_iff_surjective (f := LinearMap.mulLeft K.E β)).mp hi
    obtain ⟨a, ha⟩ := hs 1
    have ha' : β * a = 1 := ha
    exact hβ ⟨⟨β, a, ha', by rw [mul_comm]; exact ha'⟩, rfl⟩
  obtain ⟨a, ha0, hβa⟩ : ∃ a, a ≠ 0 ∧ β * a = 0 := by
    rw [injective_iff_map_eq_zero] at hinj
    push_neg at hinj
    obtain ⟨a, h, ha⟩ := hinj
    exact ⟨a, ha, h⟩
  let v : Fin m → w.adicCompletion E := fun i => e (b.repr a i)
  have hv : Matrix.vecMul v (gram e b β) = 0 := by
    funext j
    have h := betaSym_expand b (f (b j)) a
    simp only [hf] at h
    simp only [Matrix.vecMul, dotProduct, gram, Matrix.of_apply, GlobalTheory.UnitLemma.InvAlg.herm, v, Pi.zero_apply]
    simp_rw [← map_mul e]

    rw [← map_sum e, ← h, hβa]
    simp
  have hvz : v = 0 := by
    have hdet := (Matrix.isUnit_iff_isUnit_det _).mp hG
    calc v = Matrix.vecMul v (gram e b β * (gram e b β)⁻¹) := by
          rw [Matrix.mul_nonsing_inv _ hdet, Matrix.vecMul_one]
      _ = 0 := by rw [← Matrix.vecMul_vecMul, hv, Matrix.zero_vecMul]
  apply ha0
  have hr : b.repr a = 0 := by
    ext i
    have h := congrFun hvz i
    simpa [v] using h
  simpa using hr

end GlobalTheory.TwLat
end
end

section

noncomputable section

open NumberField GlobalTheory.BCT Matrix
open scoped Classical

namespace GlobalTheory.TwLat

variable {E : Type} [Field E] [NumberField E] {w : Pl E} {K : GlobalTheory.UnitLemma.UQ}
  (e : K.E ≃+* w.adicCompletion E) {B : GlobalTheory.UnitLemma.InvAlg K} {m : ℕ} (b : Module.Basis (Fin m) K.E B.A)

theorem mulMat_eq_map (a : B.A) :
    mulMat e b a = (e : K.E →+* w.adicCompletion E).mapMatrix (LinearMap.toMatrix b b (LinearMap.mulLeft K.E a)) := rfl

theorem mulMat_one : mulMat e b (1 : B.A) = 1 := by
  rw [mulMat_eq_map, LinearMap.mulLeft_one, LinearMap.toMatrix_id, map_one]

theorem mulMat_mul (a a' : B.A) : mulMat e b (a * a') = mulMat e b a * mulMat e b a' := by
  rw [mulMat_eq_map, mulMat_eq_map, mulMat_eq_map, LinearMap.mulLeft_mul, ← map_mul, ← LinearMap.toMatrix_mul]
  rfl

theorem mulMat_injective : Function.Injective (mulMat e b) := by
  intro a a' h
  have h1 : LinearMap.toMatrix b b (LinearMap.mulLeft K.E a) = LinearMap.toMatrix b b (LinearMap.mulLeft K.E a') :=
    Matrix.map_injective e.injective h
  have h2 := congrArg (fun f : B.A →ₗ[K.E] B.A => f 1) ((LinearMap.toMatrix b b).injective h1)
  simpa using h2

def mulU : B.Aˣ →* GLw m w where
  toFun a := ⟨mulMat e b a, mulMat e b ((a⁻¹ : B.Aˣ) : B.A),
    by rw [← mulMat_mul, Units.mul_inv, mulMat_one], by rw [← mulMat_mul, Units.inv_mul, mulMat_one]⟩
  map_one' := Units.ext (mulMat_one e b)
  map_mul' a a' := Units.ext (mulMat_mul e b _ _)

theorem mulU_val (a : B.Aˣ) : (mulU e b a).val = mulMat e b a := rfl

theorem mulU_injective : Function.Injective (mulU e b) :=
  fun _ _ h => Units.ext (mulMat_injective e b (congrArg Units.val h))

end GlobalTheory.TwLat
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb

theorem _root_.GlobalTheory.T.localUnitaryCentralizer_equiv_normOneTorus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ (x : B.Aˣ) (γ : UL n w), IsModel B ((((γ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) x ψ → B.P.Separable → ∃ τ : twCent (MonoidHom.id (UL n w)) γ ≃* B.T, ∀ (t : twCent (MonoidHom.id (UL n w)) γ) (y : B.A), ψ (((τ t : B.Aˣ) : B.A) * y) = (((((t : UL n w) : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) *ᵥ ψ y := by
  first | exact @GlobalTheory.CentTorusModel.cent_equiv_torus | exact GlobalTheory.CentTorusModel.cent_equiv_torus | (intros; apply GlobalTheory.CentTorusModel.cent_equiv_torus <;> assumption)
end
