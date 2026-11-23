module

public import ReciprocityTheory.DualLattices.Bundle024
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
public import ReciprocityTheory.DualLattices.Bundle022
public import ReciprocityTheory.DualLattices.Bundle014
import ReciprocityTheory.DualLattices.Bundle013
import ReciprocityTheory.DualLattices.Bundle020
public import ReciprocityTheory.DualLattices.IsPairingValueAddRight

@[expose] public section

section

noncomputable section

open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2

namespace GlobalTheory

private def htDualRing {R₀ : Type} [CommRing R₀] {Λ S : LAlg R₀} (Dq : DualPair S) (ψ : LHom Λ S) :
    DualNum.DN Λ →+* (Dq.D : Type) :=
  Ideal.Quotient.lift _
    (Polynomial.eval₂RingHom ((Dq.σ.1.comp ψ.1 : (Λ : Type) →ₐ[R₀] (Dq.D : Type)) :
      (Λ : Type) →+* (Dq.D : Type)) Dq.η) (fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, map_pow, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, sq, Dq.η_sq, mul_zero])

private lemma htDualRing_C {R₀ : Type} [CommRing R₀] {Λ S : LAlg R₀} (Dq : DualPair S)
    (ψ : LHom Λ S) (r : (Λ : Type)) :
    htDualRing Dq ψ (Ideal.Quotient.mk _ (Polynomial.C r)) = Dq.σ.1 (ψ.1 r) := by
  rw [htDualRing, Ideal.Quotient.lift_mk, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
  rfl

private lemma htDualRing_X {R₀ : Type} [CommRing R₀] {Λ S : LAlg R₀} (Dq : DualPair S)
    (ψ : LHom Λ S) : htDualRing Dq ψ (DualNum.eta Λ) = Dq.η := by
  rw [htDualRing, DualNum.eta, Ideal.Quotient.lift_mk, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_X]

private lemma htDualRing_π {R₀ : Type} [CommRing R₀] {Λ S : LAlg R₀} (Dq : DualPair S)
    (ψ : LHom Λ S) (x : DualNum.DN Λ) :
    Dq.π.1 (htDualRing Dq ψ x) = ψ.1 (DualNum.ev Λ x) := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  induction f using Polynomial.induction_on with
  | C a => rw [htDualRing_C, Dq.sect, DualNum.ev_mk, Polynomial.eval_C]
  | add f g hf hg => simp only [map_add (f := _), hf, hg]
  | monomial n a _ =>
    have h := htDualRing_X Dq ψ
    rw [DualNum.eta] at h
    rw [DualNum.ev_mk, pow_succ Polynomial.X n, ← mul_assoc, map_mul, map_mul, h, map_mul, Dq.π_η]
    simp

private lemma htDual_exists {R₀ : Type} [CommRing R₀] {Λ S : LAlg R₀} (Dq : DualPair S)
    (ψ : LHom Λ S) :
    ∃ f : LHom (DualNum.dualPair Λ).D Dq.D,
      (∀ x, Dq.π.1 (f.1 x) = ψ.1 ((DualNum.dualPair Λ).π.1 x)) ∧
      (∀ x, f.1 ((DualNum.dualPair Λ).σ.1 x) = Dq.σ.1 (ψ.1 x)) ∧
      f.1 (DualNum.dualPair Λ).η = Dq.η := by
  let fA : DualNum.DN Λ →ₐ[R₀] (Dq.D : Type) :=
    { htDualRing Dq ψ with
      commutes' := fun r => by
        show htDualRing Dq ψ (algebraMap R₀ (DualNum.DN Λ) r) = _
        rw [← Ideal.Quotient.mk_algebraMap, Polynomial.algebraMap_apply, htDualRing_C,
          AlgHom.commutes, AlgHom.commutes] }
  refine ⟨mkLHom (R := (DualNum.dualPair Λ).D) fA fun a ha => ?_, fun x => htDualRing_π Dq ψ x,
    fun x => ?_, htDualRing_X Dq ψ⟩
  · refine (DualNum.dualPair Λ).isUnit_of_π ?_
    have h1 : IsUnit (Dq.π.1 (htDualRing Dq ψ a)) := ha.map Dq.π.1
    exact ψ.2.map_nonunit _ ((htDualRing_π Dq ψ a) ▸ h1)
  · show htDualRing Dq ψ (algebraMap (Λ : Type) (DualNum.DN Λ) x) = _
    rw [← Ideal.Quotient.mk_algebraMap, Polynomial.algebraMap_apply, htDualRing_C]
    rfl

private lemma ht_padic_val {p : ℕ} [Fact p.Prime] (a : ℤ_[p]) :
    ∃ b : ℤ_[p], a - ((PadicInt.toZMod a).val : ℤ_[p]) = p * b := by
  have h : a - ((PadicInt.toZMod a).val : ℤ_[p]) ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at h
  obtain ⟨b, hb⟩ := h
  exact ⟨b, by rw [← hb, mul_comm]⟩

theorem evHt_of_lam :
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : Dat p g B Tw Dt Oe σ cp), 0 < g → maximalIdeal (D.K : Type) = ⊥ ∧ IsNilOver D.wd.ρ1 ∧ ∀ i : D.fin.ι,
    ∃ (Λ : LAlg R₀) (μ : LHom (D.fin.AAx i) Λ) (j : LHom (Tw.R 0) Λ) (ρΛ : LHom Λ D.K),
      IsNilOver ρΛ ∧ Function.Surjective μ.1 ∧ ρΛ.comp j = D.wd.ρ1 ∧ μ.comp (D.fin.sO i) = j.comp (Tw.q 0) ∧
      ∀ φ : LHom (D.fin.AAx i) Tw.O, φ.comp (D.fin.sO i) = LHom.id Tw.O →
        ∃ ψ : LHom Λ (Tw.R 0), ψ.comp μ = (Tw.q 0).comp φ ∧ ψ.comp j = LHom.id (Tw.R 0) ∧ D.wd.ρ1.comp ψ = ρΛ) →
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : Dat p g B Tw Dt Oe σ cp), EvHtStatement D) := by
  intro hLam R₀ _ p _ g B Tw Dt _ Oe _ _ σ cp D C _ _ k
  have hg : 0 < g := Nat.zero_lt_of_lt k.2
  obtain ⟨-, -, hL⟩ := hLam D hg
  clear hLam
  choose Λ μ j ρΛ _ hμ _ _ hψ using hL
  have hB1 := pairingProperties B
  have hchar := Tw.toATower.char_R 0
  have hcharΛ : ∀ i, ((p ^ (0 + 1) : ℕ) : (Λ i : Type)) = 0 := fun i => by
    rw [← map_natCast (j i).1, hchar, map_zero]
  have hy : ∀ i, (p ^ (0 + 1)) • B.map (μ i) (D.fin.y i) = 0 := fun i => by
    rw [← map_nsmul, zero_add, pow_one, D.fin.y_p, map_zero]
  choose h hh using fun i =>
    B.isHeight_exists hB1 (DualNum.dualPair (Λ i)) (p ^ (0 + 1)) (hcharΛ i) _ (hy i)
  choose F hF using fun i => hμ i (h i (D.ch.gb k))
  refine ⟨D.evAll C F, Submodule.subset_span ⟨F, rfl⟩, fun t => ?_⟩
  obtain ⟨hs, hyt, -⟩ := Classical.choose_spec (Classical.choose_spec
    (D.fin.univ Tw.O (LHom.id Tw.O) (ptOf B D.L.τ (red p g t)) (D.pt_p (red p g t))))
  change (D.ptMap (red p g t)).comp (D.fin.sO (D.ptIdx (red p g t))) = LHom.id Tw.O at hs
  change B.map (D.ptMap (red p g t)) (D.fin.y (D.ptIdx (red p g t))) = ptOf B D.L.τ (red p g t) at hyt
  obtain ⟨ψ, hψμ, -, -⟩ := hψ _ _ hs
  obtain ⟨f, f1, f2, f3⟩ := htDual_exists (Dt.Dp 0) ψ
  have H1 := B.isHeight_map hB1 _ _ ψ f f1 f2 f3 _ _ _ (hh (D.ptIdx (red p g t)))
  rw [← B.map_comp, hψμ, B.map_comp, hyt] at H1
  choose b hb using fun i => ht_padic_val (t i)
  have hp0 : ((p : ℕ) : (Tw.R 0 : Type)) = 0 := by simpa using hchar
  have hy2 : ∀ i, (p ^ (0 + 1)) • B.map (Tw.q 0) (D.L.τ i 0) = 0 := fun i => by
    rw [← map_nsmul, D.L.τ_tors, map_zero]
  have H2 := B.isHeight_sum hB1 (Dt.Dp 0) _ hchar Finset.univ
    (fun i => (((red p g t i).val : ℕ) : ℤ) • B.map (Tw.q 0) (D.L.τ i 0))
    (fun i => by rw [smul_comm, hy2, smul_zero]) _
    (fun i => B.isHeight_zsmul hB1 (Dt.Dp 0) _ hchar (hy2 i) (D.L.ht_spec i 0) _)
  have e1 : ∑ i, (((red p g t i).val : ℕ) : ℤ) • B.map (Tw.q 0) (D.L.τ i 0) =
      B.map (Tw.q 0) (ptOf B D.L.τ (red p g t)) := by

    simp only [ptOf, map_sum, map_nsmul, natCast_zsmul]
  rw [e1] at H2
  have hyp : (p ^ (0 + 1)) • B.map (Tw.q 0) (ptOf B D.L.τ (red p g t)) = 0 := by
    rw [← map_nsmul, zero_add, pow_one, D.pt_p, map_zero]
  have hU := LinearMap.congr_fun (B.isHeight_unique hB1 _ _ hchar _ hyp _ _ H1 H2) (D.ch.gb k)
  have hmem : (D.H.Ht *ᵥ (algebraMap ℤ_[p] (Tw.O : Type) ∘ t)) k -
      (D.ptMap (red p g t)).1 (F (D.ptIdx (red p g t))) ∈ RingHom.ker (Tw.q 0).1 := by
    rw [RingHom.mem_ker, map_sub, sub_eq_zero]
    have e2 : (Tw.q 0).1 ((D.ptMap (red p g t)).1 (F (D.ptIdx (red p g t)))) =
        ψ.1 (h (D.ptIdx (red p g t)) (D.ch.gb k)) := by
      rw [← hF]
      exact (congrArg (fun u : LHom _ _ => u.1 (F (D.ptIdx (red p g t)))) hψμ).symm
    rw [e2]
    refine Eq.trans ?_ hU.symm

    rw [LinearMap.sum_apply, Matrix.mulVec, dotProduct, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e3 : t i = ((red p g t i).val : ℤ_[p]) + p * b i := by
      rw [← hb i]
      show t i = ((PadicInt.toZMod (t i)).val : ℤ_[p]) + _
      ring
    rw [D.L.Ht_eq, Function.comp_apply, e3]
    rw [map_add (f := _), map_mul (algebraMap ℤ_[p] (Tw.O : Type)), map_natCast, map_natCast, map_mul, map_add (f := _),
      map_mul (Tw.q 0).1, map_natCast, map_natCast, hp0, zero_mul, add_zero, natCast_zsmul,
      LinearMap.smul_apply, nsmul_eq_mul, mul_comm]
    rfl
  rw [D.tower_zero_ker, Ideal.mem_span_singleton'] at hmem
  obtain ⟨r, hr⟩ := hmem
  refine ⟨r, ?_⟩
  rw [Dat.evAll, ← map_sub, ← hr, mul_comm]

end GlobalTheory
end
end

section

open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2

noncomputable section

namespace GlobalTheory

namespace SignChar

variable {R₀ : Type} [CommRing R₀]

section Pairing

variable (B : BX R₀) {R : LAlg R₀}

lemma pairing_zero_left (N : ℕ) (y : B.G R) (hy : N • y = 0) : B.IsPairing N 0 y 1 := by
  obtain ⟨z, hz⟩ := B.pairing_exists N 0 y (smul_zero N) hy
  have h2 := B.isPairingValue_add_left N 0 0 y z z hz hz
  rw [add_zero] at h2
  have h3 : z * z = z := B.pairing_unique N 0 y _ _ h2 hz
  have h4 : z = 1 := mul_eq_left.1 h3
  rwa [h4] at hz

lemma pairing_zero_right (N : ℕ) (x : B.G R) (hx : N • x = 0) : B.IsPairing N x 0 1 := by
  have h := B.pairing_sw N 0 x 1 (pairing_zero_left B N x hx)
  rwa [inv_one] at h

lemma pairing_nsmul_left (N : ℕ) (x y : B.G R) (z : (R : Type)ˣ) (h : B.IsPairing N x y z)
    (n : ℕ) : B.IsPairing N (n • x) y (z ^ n) := by
  induction n with
  | zero =>
    rw [zero_nsmul, pow_zero]
    exact pairing_zero_left B N y h.2.1
  | succ n ih =>
    rw [succ_nsmul, pow_succ]
    exact B.isPairingValue_add_left N _ _ _ _ _ ih h

lemma pairing_nsmul_right (N : ℕ) (x y : B.G R) (z : (R : Type)ˣ) (h : B.IsPairing N x y z)
    (n : ℕ) : B.IsPairing N x (n • y) (z ^ n) := by
  induction n with
  | zero =>
    rw [zero_nsmul, pow_zero]
    exact pairing_zero_right B N x h.1
  | succ n ih =>
    rw [succ_nsmul, pow_succ]
    exact B.isPairingValue_add_right N _ _ _ _ _ ih h

lemma pairing_sum_left {ι : Type} (s : Finset ι) (N : ℕ) (x : ι → B.G R) (y : B.G R)
    (z : ι → (R : Type)ˣ) (hy : N • y = 0) (h : ∀ i, B.IsPairing N (x i) y (z i)) :
    B.IsPairing N (∑ i ∈ s, x i) y (∏ i ∈ s, z i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.prod_empty]
    exact pairing_zero_left B N y hy
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact B.isPairingValue_add_left N _ _ _ _ _ (h a) ih

lemma pairing_sum_right {ι : Type} (s : Finset ι) (N : ℕ) (x : B.G R) (y : ι → B.G R)
    (z : ι → (R : Type)ˣ) (hx : N • x = 0) (h : ∀ i, B.IsPairing N x (y i) (z i)) :
    B.IsPairing N x (∑ i ∈ s, y i) (∏ i ∈ s, z i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.prod_empty]
    exact pairing_zero_right B N x hx
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact B.isPairingValue_add_right N _ _ _ _ _ (h a) ih

end Pairing

variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)}

lemma ptMap_spec (D : Dat p g B Tw Dt Oe σ cp) (t : Nb p g) :
    (D.ptMap t).comp (D.fin.sO (D.ptIdx t)) = LHom.id Tw.O ∧
      B.map (D.ptMap t) (D.fin.y (D.ptIdx t)) = ptOf B D.L.τ t := by
  have h := Classical.choose_spec (Classical.choose_spec
    (D.fin.univ Tw.O (LHom.id Tw.O) (ptOf B D.L.τ t) (D.pt_p t)))
  exact ⟨h.1, h.2.1⟩

lemma toZMod_eq_of_q (a : ℤ_[p]) (k : ℕ)
    (h : (Tw.q 0).1 (algebraMap ℤ_[p] (Tw.O : Type) a) = k) :
    PadicInt.toZMod a = (k : ZMod p) := by
  have h1 : ¬ IsUnit (a - k) := by
    intro hu
    have h2 := (hu.map (algebraMap ℤ_[p] (Tw.O : Type))).map (Tw.q 0).1
    rw [map_sub, map_sub, h, map_natCast, map_natCast, sub_self] at h2
    exact not_isUnit_zero h2
  have h3 : a - k ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
    rw [PadicInt.ker_toZMod]
    exact h1
  rw [RingHom.mem_ker, map_sub, map_natCast, sub_eq_zero] at h3
  exact h3

lemma pairing_ptOf (D : Dat p g B Tw Dt Oe σ cp) (s t : TT p g) :
    ∃ n : ℕ, (n : ZMod p) = PadicInt.toZMod (pair p g D.H.E s t) ∧
      B.IsPairing p (ptOf B D.L.τ (red p g s)) (ptOf B D.L.τ (red p g t)) (Tw.ζ 0 ^ n) := by
  choose k hk hpair using fun i j => D.L.E_spec i j 0
  simp only [zero_add, pow_one] at hpair
  refine ⟨∑ i, (∑ j, k i j * (red p g t j).val) * (red p g s i).val, ?_, ?_⟩

  · simp only [pair, dotProduct, mulVec, map_sum, map_mul, Nat.cast_sum, Nat.cast_mul,
    ZMod.natCast_zmod_val, red]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [toZMod_eq_of_q _ _ (hk i j)]
  · rw [← Finset.prod_pow_eq_pow_sum]
    refine pairing_sum_left B _ p _ _ _ (D.pt_p _) fun i => ?_
    rw [pow_mul]
    refine pairing_nsmul_left B p _ _ _ ?_ _
    rw [← Finset.prod_pow_eq_pow_sum]
    refine pairing_sum_right B _ p _ _ _ (hpair i i).1 fun j => ?_
    rw [pow_mul]
    exact pairing_nsmul_right B p _ _ _ (hpair i j) _

end SignChar

theorem signChar_mem_evImg :
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : Dat p g B Tw Dt Oe σ cp), EvenTwoEvaluationSign D) := by
  intro R₀ _ p _ g B Tw Dt _ Oe _ _ σ cp D C _ _ _ _ hp s
  have hex : ∀ i, ∃ z, B.IsPairing p (B.map (D.fin.sO i) (ptOf B D.L.τ (red p g s)))
      (D.fin.y i) z := fun i =>
    B.pairing_exists p _ _ (by rw [← map_nsmul, D.pt_p, map_zero]) (D.fin.y_p i)
  choose e he using hex
  refine ⟨D.evAll C fun i => (e i : (D.fin.AAx i : Type)), Submodule.subset_span ⟨_, rfl⟩,
    fun t => ?_⟩
  obtain ⟨h1, h2⟩ := SignChar.ptMap_spec D (red p g t)
  have h3 := B.pairing_map (D.ptMap (red p g t)) p _ _ _ (he (D.ptIdx (red p g t)))
  rw [← B.map_comp, h1, B.map_id, h2] at h3
  obtain ⟨n, hn, h4⟩ := SignChar.pairing_ptOf D s t
  have h5 := congrArg Units.val (B.pairing_unique p _ _ _ _ h3 h4)
  rw [Units.val_pow_eq_pow_val, D.zeta0 hp, Units.coe_map] at h5
  have h6 : (D.ptMap (red p g t)).1 (e (D.ptIdx (red p g t)) : (D.fin.AAx _ : Type)) =
      (-1) ^ n := h5
  have h7 : (PadicInt.toZMod (pair p g D.H.E s t)).val % 2 = n % 2 := by
    rw [← hn, ZMod.val_natCast, ← hp, Nat.mod_mod]
  unfold Dat.evAll
  rw [h6, map_pow, map_neg, map_one, neg_one_pow_eq_pow_mod_two n, ← h7,
    ← neg_one_pow_eq_pow_mod_two]

end GlobalTheory
end
end

section

noncomputable section

open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2

namespace GlobalTheory.EvAct

variable {R₀ : Type} [CommRing R₀]
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)}

private lemma val_natCast_smul {M : Type} [AddCommGroup M] (x : M) (hx : p • x = 0) (n : ℕ) :
    ((n : ZMod p)).val • x = n • x := by
  rw [ZMod.val_natCast]
  conv_rhs => rw [← Nat.mod_add_div n p, add_smul, mul_comm, mul_smul, hx, smul_zero, add_zero]

private lemma val_sum_mul_smul {M ι : Type} [AddCommGroup M] [Fintype ι] (x : M) (hx : p • x = 0)
    (u v : ι → ZMod p) : (∑ j, u j * v j).val • x = ∑ j, (v j).val • (u j).val • x := by
  have h : (∑ j, u j * v j) = ((∑ j, (v j).val * (u j).val : ℕ) : ZMod p) := by
    push_cast
    simp [mul_comm]
  rw [h, val_natCast_smul x hx, Finset.sum_smul]
  simp only [mul_smul]

private lemma ptMap_spec (D : Dat p g B Tw Dt Oe σ cp) (t : Nb p g) :
    (D.ptMap t).comp (D.fin.sO _) = LHom.id Tw.O ∧ B.map (D.ptMap t) (D.fin.y _) = ptOf B D.L.τ t ∧
      ∀ j (φ' : LHom (D.fin.AAx j) Tw.O), φ'.comp (D.fin.sO j) = LHom.id Tw.O →
        B.map φ' (D.fin.y j) = ptOf B D.L.τ t → j = D.ptIdx t ∧ HEq φ' (D.ptMap t) :=
  Classical.choose_spec (Classical.choose_spec
    (D.fin.univ Tw.O (LHom.id Tw.O) (ptOf B D.L.τ t) (D.pt_p t)))

private lemma tau_p (D : Dat p g B Tw Dt Oe σ cp) (j : Ix g) : p • D.L.τ j 0 = 0 := by
  have h := D.L.τ_tors j 0
  rwa [zero_add, pow_one] at h

private lemma act_ptOf (D : Dat p g B Tw Dt Oe σ cp) (a : Oe) (t : Nb p g) :
    (D.A.act a Tw.O (LHom.id Tw.O) ⟨ptOf B D.L.τ t, (mem_torP B p _).2 (D.pt_p t)⟩ : B.G Tw.O) =
      ptOf B D.L.τ (((D.H.ρ a).map PadicInt.toZMod) *ᵥ t) := by
  have h : (⟨ptOf B D.L.τ t, (mem_torP B p _).2 (D.pt_p t)⟩ : torP B p Tw.O) =
      ∑ j, (t j).val • (⟨D.L.τ j 0, (mem_torP B p _).2 (tau_p D j)⟩ : torP B p Tw.O) := by
    apply Subtype.ext
    simp [ptOf]

  rw [h, map_sum, AddSubgroup.val_finsetSum]
  simp only [map_nsmul, AddSubgroup.coe_nsmul]
  simp only [D.L.ρ_spec, Finset.smul_sum]
  rw [Finset.sum_comm, ptOf]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mulVec, dotProduct, val_sum_mul_smul _ (tau_p D k)]
  rfl

private lemma red_mulVec (M : Matrix (Ix g) (Ix g) ℤ_[p]) (t : TT p g) :
    red p g (M *ᵥ t) = (M.map PadicInt.toZMod) *ᵥ red p g t := by
  funext k
  exact (RingHom.map_mulVec PadicInt.toZMod M t k)

private lemma eval_congr (D : Dat p g B Tw Dt Oe σ cp) (F : ∀ i, (D.fin.AAx i : Type))
    {i j : D.fin.ι} (φ : LHom (D.fin.AAx i) Tw.O) (φ' : LHom (D.fin.AAx j) Tw.O) (h : i = j)
    (h' : HEq φ φ') : φ.1 (F i) = φ'.1 (F j) := by
  subst h
  rw [eq_of_heq h']

private lemma evAll_act (D : Dat p g B Tw Dt Oe σ cp) (C : Type) [Field C]
    [Algebra (Tw.O : Type) C] (a : Oe) (F : ∀ i, (D.fin.AAx i : Type)) :
    ∃ F' : ∀ i, (D.fin.AAx i : Type), ∀ t : Nb p g,
      D.evAll C F' t = D.evAll C F (((D.H.ρ a).map PadicInt.toZMod) *ᵥ t) := by
  have key := fun i => D.fin.univ (D.fin.AAx i) (D.fin.sO i)
    (D.A.act a (D.fin.AAx i) (D.fin.sO i) ⟨D.fin.y i, (mem_torP B p _).2 (D.fin.y_p i)⟩ : B.G _)
    ((mem_torP B p _).1 (Subtype.property _))
  choose m α hs hy _ using key
  refine ⟨fun i => (α i).1 (F (m i)), fun t => ?_⟩
  obtain ⟨h1, h2, -⟩ := ptMap_spec D t
  obtain ⟨-, -, h3⟩ := ptMap_spec D (((D.H.ρ a).map PadicInt.toZMod) *ᵥ t)
  have e1 : ((D.ptMap t).comp (α (D.ptIdx t))).comp (D.fin.sO _) = LHom.id Tw.O := by
    rw [← h1, ← hs (D.ptIdx t)]
    rfl
  have e2 : B.map ((D.ptMap t).comp (α (D.ptIdx t))) (D.fin.y _) =
      ptOf B D.L.τ (((D.H.ρ a).map PadicInt.toZMod) *ᵥ t) := by
    rw [B.map_comp, hy, D.A.act_nat a _ _ _ h1, ← act_ptOf]
    congr 2
    exact Subtype.ext h2
  obtain ⟨h4, h5⟩ := h3 _ _ e1 e2
  unfold Dat.evAll
  rw [← eval_congr D F _ _ h4 h5]
  rfl

theorem evImg_act_stable :
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : Dat p g B Tw Dt Oe σ cp), EvActStatement D) := by
  intro R₀ _ p _ g B Tw Dt _ Oe _ _ σ cp D C _ _ a f hf
  refine ⟨fun t => f (((D.H.ρ a).map PadicInt.toZMod) *ᵥ t), ?_, fun t => by rw [red_mulVec]⟩
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, rfl⟩ := hx
    obtain ⟨F', hF'⟩ := evAll_act D C a F
    exact Submodule.subset_span ⟨F', funext hF'⟩
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul c x _ hx => exact Submodule.smul_mem _ c hx

end GlobalTheory.EvAct
end
end
