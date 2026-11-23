module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle004
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.MapWopWmap

@[expose] public section

section

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

private lemma realForm_eq_zero {E : Type} [Field E] [NumberField E] {P : Type} [Fintype P] (g : P → (E →+* ℂ))
    (hg : Function.Injective (Sum.elim g (fun p => ComplexEmbedding.conjugate (g p))))
    (u v : P → ℝ) (h : ∀ x : 𝓞 E, ∑ p, (u p * (g p (x : E)).re + v p * (g p (x : E)).im) = 0) :
    ∀ p, u p = 0 ∧ v p = 0 := by
  classical
  let σ : P ⊕ P → (E →* ℂ) := fun k =>
    (Sum.elim g (fun p => ComplexEmbedding.conjugate (g p)) k).toMonoidHom
  have hσ : Function.Injective σ := by
    intro k l hkl
    apply hg
    ext x
    exact DFunLike.congr_fun hkl x
  have hli : LinearIndependent ℂ (fun k => (σ k : E → ℂ)) :=
    (linearIndependent_monoidHom E ℂ).comp σ hσ
  have hE : ∀ x : E, ∑ p, (u p * (g p x).re + v p * (g p x).im) = 0 := by
    intro x
    obtain ⟨d, hd, hdx⟩ := exists_integral_multiples ℤ ℚ ({x} : Finset E)
    obtain ⟨w, hw⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).mp
      (hdx x (Finset.mem_singleton_self x))
    have h1 := h w
    have hw' : (w : E) = (d : E) * x := by
      rw [← zsmul_eq_mul, ← hw]
    rw [hw'] at h1
    simp only [map_mul, map_intCast, Complex.mul_re, Complex.mul_im, Complex.intCast_re,
      Complex.intCast_im, zero_mul, sub_zero, add_zero] at h1
    have h3 : (d : ℝ) * ∑ p, (u p * (g p x).re + v p * (g p x).im) = 0 := by
      rw [Finset.mul_sum, ← h1]
      exact Finset.sum_congr rfl fun p _ => by ring
    rcases mul_eq_zero.mp h3 with h2 | h2
    · exact absurd (Int.cast_eq_zero.mp h2) hd
    · exact h2
  let c : P ⊕ P → ℂ := Sum.elim (fun p => ((u p : ℂ) - Complex.I * v p) / 2)
    (fun p => ((u p : ℂ) + Complex.I * v p) / 2)
  have hterm : ∀ p (x : E), ((u p : ℂ) - Complex.I * v p) / 2 * g p x +
      ((u p : ℂ) + Complex.I * v p) / 2 * ComplexEmbedding.conjugate (g p) x =
      ((u p * (g p x).re + v p * (g p x).im : ℝ) : ℂ) := by
    intro p x
    rw [ComplexEmbedding.conjugate_coe_eq]
    apply Complex.ext <;> simp <;> ring
  have hsum : ∑ k, c k • (σ k : E → ℂ) = 0 := by
    funext x
    rw [Finset.sum_apply, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
    calc _ = ∑ p, ((u p * (g p x).re + v p * (g p x).im : ℝ) : ℂ) :=
          Finset.sum_congr rfl fun p _ => hterm p x
      _ = 0 := by rw [← Complex.ofReal_sum, hE x, Complex.ofReal_zero]
  have hc := (Fintype.linearIndependent_iff.mp hli) c hsum
  intro p
  have h1 : ((u p : ℂ) - Complex.I * v p) / 2 = 0 := hc (Sum.inl p)
  have h1' : (u p : ℂ) - Complex.I * v p = 0 := by
    rcases div_eq_zero_iff.mp h1 with h | h
    · exact h
    · norm_num at h
  constructor
  · have h4 := congrArg Complex.re h1'
    simpa using h4
  · have h4 := congrArg Complex.im h1'
    simpa using h4

theorem UpperTheory.Gal.W2.Seed.pRealIso :
    TraceType → RealIso := by
  intro hT E _ _ _ A n
  classical
  obtain ⟨-, -, hpl, him⟩ := hT E A
  have hcardPhi : Fintype.card (Phi A) = Fintype.card (InfinitePlace E) := by
    refine Fintype.card_congr (Equiv.ofBijective (fun τ : Phi A => InfinitePlace.mk τ.1) ⟨?_, ?_⟩)
    · intro a b hab
      exact (hpl (InfinitePlace.mk a.1)).unique rfl hab.symm
    · intro v
      obtain ⟨τ, hτ, -⟩ := hpl v
      exact ⟨τ, hτ⟩
  have hrank : 2 * Fintype.card (InfinitePlace E) = Module.finrank ℚ E := by
    have h1 := InfinitePlace.card_add_two_mul_card_eq_rank E
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero E]
    rw [IsTotallyComplex.nrRealPlaces_eq_zero E] at h1
    omega
  let b := NumberField.RingOfIntegers.basis E
  let bZ := Pi.basis (fun _ : Fin n => b)
  let b1 := Algebra.TensorProduct.basis ℝ bZ
  let F : (Fin n → 𝓞 E) →ₗ[ℤ] (Phi A × Fin n → ℂ) :=
    LinearMap.pi (fun p : Phi A × Fin n =>
      ((p.1.1.comp (algebraMap (𝓞 E) E)).toIntAlgHom.toLinearMap) ∘ₗ LinearMap.proj p.2)
  let L : ℝ ⊗[ℤ] (Fin n → 𝓞 E) →ₗ[ℝ] (Phi A × Fin n → ℂ) := b1.constr ℝ (fun k => F (bZ k))
  have hL : ∀ x, L (1 ⊗ₜ x) = F x := by
    have hcomp : (L.restrictScalars ℤ) ∘ₗ TensorProduct.mk ℤ ℝ (Fin n → 𝓞 E) 1 = F := by
      refine bZ.ext fun k => ?_
      have hk : ((L.restrictScalars ℤ) ∘ₗ TensorProduct.mk ℤ ℝ (Fin n → 𝓞 E) 1) (bZ k) =
          L (b1 k) := by
        rw [Algebra.TensorProduct.basis_apply]
        rfl
      rw [hk, Module.Basis.constr_basis]
    intro x
    exact LinearMap.congr_fun hcomp x
  have dec : ∀ (φ : Module.Dual ℝ (Phi A × Fin n → ℂ)) p (w : ℂ),
      φ (Pi.single p w) = w.re * φ (Pi.single p 1) + w.im * φ (Pi.single p Complex.I) := by
    intro φ p w
    have hw : (Pi.single p w : Phi A × Fin n → ℂ) =
        w.re • (Pi.single p (1 : ℂ) : Phi A × Fin n → ℂ) +
          w.im • (Pi.single p Complex.I : Phi A × Fin n → ℂ) := by
      ext q
      by_cases hq : q = p
      · subst hq
        simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same]
        apply Complex.ext <;> simp
      · simp [Pi.single_apply, hq]
    rw [hw, map_add (f := _), map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have hg : Function.Injective
      (Sum.elim (fun τ : Phi A => τ.1) (fun τ : Phi A => ComplexEmbedding.conjugate τ.1)) := by
    have hcross : ∀ a b : Phi A, a.1 ≠ ComplexEmbedding.conjugate b.1 := by
      intro a b h
      have h2 := RingHom.congr_fun h (A.ω : E)
      rw [ComplexEmbedding.conjugate_coe_eq, a.2, b.2] at h2
      have h3 := congrArg Complex.im h2
      rw [Complex.conj_im] at h3
      exact him (by linarith)
    rintro (a | a) (b | b) h
    · exact congrArg _ (Subtype.ext h)
    · exact absurd h (hcross a b)
    · exact absurd h.symm (hcross b a)
    · simp only [Sum.elim_inr] at h
      have h' : (a.1 : E →+* ℂ) = b.1 := by
        ext x
        have hx := RingHom.congr_fun h x
        rw [ComplexEmbedding.conjugate_coe_eq, ComplexEmbedding.conjugate_coe_eq] at hx
        simpa using congrArg (starRingEnd ℂ) hx
      exact congrArg _ (Subtype.ext h')
  have hsurj : Function.Surjective L := by
    rw [← LinearMap.range_eq_top]
    by_contra hne
    obtain ⟨φ, hφ0, hφ⟩ :=
      Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr hne) inferInstance
    have hvan : ∀ y, φ (L y) = 0 := by
      intro y
      have hm : φ (L y) ∈ (LinearMap.range L).map φ := ⟨L y, ⟨y, rfl⟩, rfl⟩
      rw [hφ] at hm
      exact (Submodule.mem_bot ℝ).mp hm
    have huv : ∀ i : Fin n, ∀ τ : Phi A,
        φ (Pi.single (τ, i) 1) = 0 ∧ φ (Pi.single (τ, i) Complex.I) = 0 := by
      intro i
      refine realForm_eq_zero (fun τ : Phi A => τ.1) hg _ _ fun x => ?_
      have h1 := hvan (1 ⊗ₜ Pi.single i x)
      rw [hL] at h1
      have hFx : F (Pi.single i x) = ∑ τ : Phi A, Pi.single (τ, i) (τ.1 (x : E)) := by
        ext ⟨τ', i'⟩
        rw [Finset.sum_apply]
        by_cases hi : i' = i
        · subst hi
          rw [Finset.sum_eq_single τ']
          · simp [F]
          · intro τ _ hτ
            simp [Pi.single_apply, hτ]
          · simp
        · simp [F, Pi.single_apply, hi]

      rw [hFx, map_sum] at h1
      rw [← h1]
      exact Finset.sum_congr rfl fun τ _ => by rw [dec φ (τ, i) (τ.1 (x : E))]; ring
    apply hφ0
    refine LinearMap.ext fun z => ?_

    rw [LinearMap.zero_apply, ← Finset.univ_sum_single z, map_sum]
    refine Finset.sum_eq_zero fun p _ => ?_
    obtain ⟨τ, i⟩ := p
    rw [dec, (huv i τ).1, (huv i τ).2]
    simp
  have hdim : Module.finrank ℝ (ℝ ⊗[ℤ] (Fin n → 𝓞 E)) =
      Module.finrank ℝ (Phi A × Fin n → ℂ) := by
    rw [Module.finrank_eq_card_basis b1,
      Module.finrank_eq_card_basis (Pi.basis fun _ : Phi A × Fin n => Complex.basisOneI)]
    simp only [Fintype.card_sigma, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      Fintype.card_fin, Fintype.card_prod]
    rw [← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank, ← hrank, hcardPhi]
    ring
  refine ⟨LinearEquiv.ofBijective L
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj, hsurj⟩, ?_⟩
  intro x τ i
  show L (1 ⊗ₜ x) (τ, i) = _
  rw [hL]
  rfl
end

section

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pAtPEx :
    KqEx → UEx → OrbEx → LiftEx → AtPEx := by
  intro hK hU hO hL E _ _ _ A p _ hs
  obtain ⟨Kq, hω, hKq, hgen⟩ := hK E A
  obtain ⟨s, iotaC, hsC⟩ := hL E A.τ₀
  haveI : CharZero (PadicAlgCl p) := charZero_of_injective_algebraMap (algebraMap ℚ_[p] (PadicAlgCl p)).injective
  haveI hAlg : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    convert (AlgebraicClosure.isAlgebraic ℚ)
  let iotaA : AlgebraicClosure ℚ →ₐ[ℚ] PadicAlgCl p := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let iotaP : AlgebraicClosure ℚ →+* PadicAlgCl p := iotaA.toRingHom
  let τ₁ : E →+* PadicAlgCl p := iotaP.comp s
  obtain ⟨u, ρ, hover, hρ⟩ := hU E A p hs Kq hω hgen τ₁
  obtain ⟨m, emb, w, hw, hov, hinj, hall⟩ := hO E p Kq u τ₁ hover
  exact ⟨{ Kq := Kq, hKq := hKq, u := u, m := m, emb := emb, emb_over := hov, emb_inj := hinj, emb_all := hall,
           iotaP := iotaP, iotaC := iotaC, ρp := ρ, ρp_eq := ⟨hω, hρ⟩, s := s, s_C := hsC, w := w,
           s_P := fun x => by rw [hw]; rfl }⟩
end

section

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pFormPerfSt :
    FormPerfSt := by
  intro E _ _ _ A n q hP
  obtain ⟨e, he, hx, c', hc⟩ := hP
  refine ⟨e ^ 3, Nat.Coprime.pow_left 3 he, fun f => ?_⟩
  choose x hxf using fun i : Fin n =>
    hx (((f.toAddMonoidHom.comp (AddMonoidHom.single _ i)).comp A.bar.toAddMonoidHom).toIntLinearMap)
  refine ⟨fun i => -((if (i : ℕ) = 0 then c' * (e : 𝓞 E) else c' ^ 2) * x i), ?_⟩
  refine LinearMap.ext fun y => ?_
  rw [Arith.EF_apply]
  have key : ∀ i, A.hd n i * -((if (i : ℕ) = 0 then c' * (e : 𝓞 E) else c' ^ 2) * x i) * A.bar (y i)
      = ((e ^ 2 : ℕ) : 𝓞 E) * (x i * A.bar (y i)) := by
    intro i
    simp only [Arith.hd, Arith.dg]
    push_cast
    split_ifs
    · linear_combination ((e : 𝓞 E) * x i * A.bar (y i)) * hc
    · linear_combination (c' * A.c + (e : 𝓞 E)) * x i * A.bar (y i) * hc
  have hs : ∀ i, A.trd (x i * A.bar (y i)) = (e : ℤ) * f (Pi.single i (y i)) := by
    intro i
    rw [hxf i]
    simp [Arith.bar_bar]

  rw [Finset.sum_congr rfl (fun i _ => key i), ← Finset.mul_sum, ← nsmul_eq_mul, map_nsmul, map_sum]
  simp_rw [hs]

  rw [← Finset.mul_sum, ← map_sum, Finset.univ_sum_single]
  simp only [LinearMap.smul_apply, nsmul_eq_mul]
  push_cast
  ring
end

section

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pLiftEx :
    LiftEx := by
  unfold UpperTheory.Gal.W2.Seed.LiftEx
  intro E _ _ τ₀
  let sA : E →ₐ[ℚ] AlgebraicClosure ℚ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  letI : Algebra E (AlgebraicClosure ℚ) := sA.toRingHom.toAlgebra
  letI : Algebra E ℂ := τ₀.toAlgebra
  haveI : IsScalarTower ℚ E (AlgebraicClosure ℚ) :=
    IsScalarTower.of_algebraMap_eq (fun x => (sA.commutes x).symm)
  haveI hQ : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : Algebra.IsAlgebraic E (AlgebraicClosure ℚ) := Algebra.IsAlgebraic.tower_top (K := ℚ) E
  let iA : AlgebraicClosure ℚ →ₐ[E] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨sA.toRingHom, iA.toRingHom, fun x => ?_⟩
  exact iA.commutes x
end

section

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pOrbEx :
    OrbEx := by
  intro E _ _ p _ Kq u τ₁ h₁
  classical
  let S := {τ : E →+* PadicAlgCl p // LiesOver Kq u τ}
  let R : Setoid S :=
    { r := fun a b => ∃ σ : Gal(PadicAlgCl p/ℚ_[p]),
        b.1 = ((σ.toRingEquiv : PadicAlgCl p ≃+* PadicAlgCl p) : PadicAlgCl p →+* PadicAlgCl p).comp a.1
      iseqv := ⟨fun a => ⟨1, by ext x; simp⟩,
        fun {a b} ⟨σ, hσ⟩ => ⟨σ⁻¹, by rw [hσ]; ext x; simp⟩,
        fun {a b c} ⟨σ, hσ⟩ ⟨ρ, hρ⟩ => ⟨ρ * σ, by rw [hρ, hσ]; ext x; simp⟩⟩ }
  haveI : Finite (E →+* PadicAlgCl p) := inferInstance
  haveI : Finite S := Subtype.finite
  haveI : Finite (Quotient R) := Quotient.finite _
  let s₁ : S := ⟨τ₁, h₁⟩
  let rep : Quotient R → S := fun q => if q = Quotient.mk R s₁ then s₁ else q.out
  have hrep : ∀ q, Quotient.mk R (rep q) = q := by
    intro q
    by_cases hq : q = Quotient.mk R s₁
    · simp only [rep, if_pos hq]
      exact hq.symm
    · simp only [rep, if_neg hq]
      exact Quotient.out_eq q
  let eq := Finite.equivFin (Quotient R)
  refine ⟨Nat.card (Quotient R), fun i => (rep (eq.symm i)).1, eq (Quotient.mk R s₁), ?_, ?_, ?_, ?_⟩
  · simp [rep, s₁]
  · intro i
    exact (rep _).2
  · intro i j σ hij
    apply eq.symm.injective
    rw [← hrep (eq.symm i), ← hrep (eq.symm j)]
    exact Quotient.sound ⟨σ, hij.symm⟩
  · intro τ hτ
    obtain ⟨σ, hσ⟩ := Quotient.exact (hrep (Quotient.mk R ⟨τ, hτ⟩))
    exact ⟨eq (Quotient.mk R ⟨τ, hτ⟩), σ, by simpa using hσ⟩
end

section

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

private theorem exists_trace_rep (E : Type) [Field E] [NumberField E] (f : 𝓞 E →ₗ[ℤ] ℤ) :
    ∃ z : E, ∀ y : 𝓞 E, Algebra.trace ℚ E (z * (y : E)) = ((f y : ℤ) : ℚ) := by
  let g : E →ₗ[ℚ] ℚ := (integralBasis E).constr ℚ (fun i => ((f (RingOfIntegers.basis E i) : ℤ) : ℚ))
  have hg : ∀ y : 𝓞 E, g (y : E) = ((f y : ℤ) : ℚ) := by
    have hext : ((g.restrictScalars ℤ).comp ((Algebra.linearMap (𝓞 E) E).restrictScalars ℤ)) =
        (Algebra.linearMap ℤ ℚ).comp f := by
      refine (RingOfIntegers.basis E).ext fun i => ?_
      simp [g, ← integralBasis_apply]
    intro y
    simpa using LinearMap.congr_fun hext y
  have hnd : (Algebra.traceForm ℚ E).Nondegenerate := traceForm_nondegenerate ℚ E
  refine ⟨(LinearMap.BilinForm.toDual (Algebra.traceForm ℚ E) hnd).symm g, fun y => ?_⟩
  rw [← Algebra.traceForm_apply, ← LinearMap.BilinForm.toDual_def hnd, LinearEquiv.apply_symm_apply]
  exact hg y

theorem UpperTheory.Gal.W2.Seed.pPerfOf :
    PerfOf := by
  intro E _ _ _ A M hgen hc q hq
  obtain ⟨_, e1, he1, hz⟩ := hgen
  obtain ⟨e2, he2, c', hc'⟩ := hc
  refine ⟨e1 * e2, Nat.Coprime.mul_left (he1.coprime_dvd_right hq) (he2.coprime_dvd_right hq), ?_, ⟨c' * e1, ?_⟩⟩
  · intro f
    obtain ⟨z, hzf⟩ := exists_trace_rep E f
    have hzc : InCodiff z := fun y => ⟨f y, hzf y⟩
    obtain ⟨x, hx⟩ := hz z hzc
    refine ⟨(e2 : 𝓞 E) * x, fun y => ?_⟩
    have h := A.trd_spec ((e2 : 𝓞 E) * x * y)
    have hmul : A.δ * ((((e2 : 𝓞 E) * x * y : 𝓞 E)) : E) = ((e1 * e2 : ℕ) : ℚ) • (z * (y : E)) := by
      rw [Algebra.smul_def, map_natCast]
      push_cast
      linear_combination (-((e2 : E) * (y : E))) * hx
    have hq' : ((A.trd ((e2 : 𝓞 E) * x * y) : ℤ) : ℚ) = (((e1 * e2 : ℕ) : ℤ) : ℚ) * ((f y : ℤ) : ℚ) := by
      rw [h, hmul, map_smul, hzf, smul_eq_mul]
      push_cast; ring
    exact_mod_cast hq'
  · rw [← mul_assoc, hc']
    push_cast
    ring
end

section

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pRepEx :
    RepEx := by
  intro E _ _ n
  classical
  let b := NumberField.RingOfIntegers.basis E
  let bZ := Pi.basis (fun _ : Fin n => b)
  let bQ := Pi.basis (fun _ : Fin n => NumberField.integralBasis E)
  let b1 := Algebra.TensorProduct.basis ℚ bZ
  refine ⟨b1.equiv bQ (Equiv.refl _), ?_⟩
  let f1 : (Fin n → 𝓞 E) →ₗ[ℤ] (Fin n → E) :=
    ((b1.equiv bQ (Equiv.refl _)).toLinearMap.restrictScalars ℤ) ∘ₗ
      TensorProduct.mk ℤ ℚ (Fin n → 𝓞 E) 1
  let f2 : (Fin n → 𝓞 E) →ₗ[ℤ] (Fin n → E) :=
    LinearMap.pi (fun i => (algebraMap (𝓞 E) E).toIntAlgHom.toLinearMap ∘ₗ LinearMap.proj i)
  have hf : f1 = f2 := by
    refine bZ.ext fun k => ?_
    have hk : f1 (bZ k) = b1.equiv bQ (Equiv.refl _) (b1 k) := by
      rw [Algebra.TensorProduct.basis_apply]
      rfl
    rw [hk, Module.Basis.equiv_apply]
    obtain ⟨i, j⟩ := k
    funext l
    simp [bQ, bZ, f2, Pi.basis_apply, Pi.single_apply, NumberField.integralBasis_apply]
    split_ifs <;> simp
    rfl
  intro v i
  exact congr_fun (LinearMap.congr_fun hf v) i
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct

private theorem upts_ext {C : Type} [Ring C] [Algebra ℚ C] [Nontrivial C] {star : C →+* Cᵐᵒᵖ} {R : Type} [CommRing R] [Algebra ℚ R]
    (x y : UPts star R) (h : (((x : (R ⊗[ℚ] C)ˣ × Rˣ).1 : (R ⊗[ℚ] C)ˣ) : R ⊗[ℚ] C) = ((y : (R ⊗[ℚ] C)ˣ × Rˣ).1 : (R ⊗[ℚ] C)ˣ)) :
    x = y := by
  obtain ⟨⟨g, c⟩, hx⟩ := x
  obtain ⟨⟨g', c'⟩, hy⟩ := y
  have hx' : (g : R ⊗[ℚ] C) * (starT star R g).unop = algebraMap R (R ⊗[ℚ] C) c := hx
  have hy' : (g' : R ⊗[ℚ] C) * (starT star R g').unop = algebraMap R (R ⊗[ℚ] C) c' := hy
  have hg : g = g' := Units.ext h
  subst hg
  have hinj : Function.Injective (algebraMap R (R ⊗[ℚ] C)) := fun a b hab =>
    Algebra.TensorProduct.includeLeft_injective (R := ℚ) (S := ℚ) (A := R) (B := C) (algebraMap ℚ C).injective hab
  have hc : c = c' := Units.ext (hinj (hx'.symm.trans hy'))
  subst hc
  rfl

theorem UpperTheory.Gal.W2.Seed.pTrEx :
    AdTEx → MuEx → IsoEx' → JEx → JEq → JSurj → TrEx := by
  intro hT hM hI hJ hQ hS E _ _ _ A n p _ S hn
  obtain ⟨T⟩ := hT p E
  obtain ⟨μ, hμ⟩ := hM (AfP p) E n
  obtain ⟨a, ha⟩ := hI E A n hn
  obtain ⟨j, hj1, hj2⟩ := hJ E A n p S T μ hμ a ha
  obtain ⟨hc, he⟩ := hQ E A n p S T μ hμ a j hj1
  choose sec hs1 hs2 using hS E A n p S T μ hμ a ha
  have hjs : ∀ h, j (sec h) = h := fun h =>
    upts_ext _ _ (μ.injective ((hj1 (sec h)).trans (hs1 h).symm))
  have hmul : ∀ h h', sec (h * h') = sec h * sec h' := by
    intro h h'
    apply hc
    intro w
    by_cases hw : (p : 𝓞 E) ∈ w.asIdeal
    · rw [map_mul, hs2 _ w hw, hs2 _ w hw, hs2 _ w hw, one_mul]
    · exact (he _ _).1 (by rw [map_mul, hjs, hjs, hjs]) w hw
  exact ⟨{ T with
    μ := μ, mu := hμ, a := a, iso := ha, j := j, j_mx := hj1, j_sim := hj2
    sec := MonoidHom.mk' sec hmul, j_sec := hjs, sec_p := hs2, j_eq := he }⟩
end
