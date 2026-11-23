module

public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentCharacterArgumentMulStabilizer
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle061
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

noncomputable section

namespace GlobalTheory.Proof.twistPrimeDatum_integral_support_and_invariant

variable {E : Type} [Field E] [NumberField E]

theorem entB_zero (q : ℕ) {N' N : ℕ} (k₀ c' n' c n : ℕ) (x : (Fin N' → E) →ₗ[E] (Fin N → E)) (p p' : ℕ) :
    LocE.entB q k₀ c' n' c n 0 0 x p p' =
      Loc.atN (x (Loc.eN E N' (LocE.fIdx k₀ c' n' p'))) (LocE.fIdx k₀ c n p) := by
  simp [LocE.entB, LocE.scE]

theorem intAt_entB {P : HeightOneSpectrum (𝓞 E)} (q : ℕ) {N' N : ℕ} (k₀ c' n' c n : ℕ)
    {y : (Fin N' → E) →ₗ[E] (Fin N → E)} (hy : IntHom P y) (p p' : ℕ) :
    IntAt P (LocE.entB q k₀ c' n' c n 0 0 y p p') := by
  rw [entB_zero]
  have h : IntV P (Loc.eN E N' (LocE.fIdx k₀ c' n' p')) := fun l => by
    unfold Loc.eN
    split_ifs
    · exact intAt_one P
    · exact IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P
  unfold Loc.atN
  split_ifs
  · exact hy _ h _
  · exact IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P

theorem entB_add (q : ℕ) {N' N : ℕ} (k₀ c' n' c n : ℕ) (x y : (Fin N' → E) →ₗ[E] (Fin N → E)) (a : E) (p p' : ℕ) :
    LocE.entB q k₀ c' n' c n 0 0 (x + a • y) p p' =
      LocE.entB q k₀ c' n' c n 0 0 x p p' + a * LocE.entB q k₀ c' n' c n 0 0 y p p' := by
  rw [entB_zero, entB_zero, entB_zero, LinearMap.add_apply, LinearMap.smul_apply, atN_add, atN_smul]

theorem fIdx_fPos {k₀ c n l : ℕ} (hk : k₀ ≤ n) (hl : l < n + c) :
    LocE.fIdx k₀ c n (LocE.fPos k₀ c n l) = l ∧ LocE.fPos k₀ c n l < n + c := by
  unfold LocE.fIdx LocE.fPos
  split_ifs <;> omega

theorem unitV_congr {K : Type} [Field K] {P : HeightOneSpectrum (𝓞 E)} (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {a b : E}
    (h : redP P a = redP P b) : LocE.unitV ξ a = LocE.unitV ξ b := by
  unfold LocE.unitV
  have key : ∀ u v : 𝓞 E ⧸ P.asIdeal, u = v →
      (open Classical in if h : IsUnit u then ((ξ h.unit : Kˣ) : K) else 0) =
        (open Classical in if h : IsUnit v then ((ξ h.unit : Kˣ) : K) else 0) := by
    rintro u v rfl
    rfl
  exact key _ _ h

theorem intAt_add_iff {P : HeightOneSpectrum (𝓞 E)} {a b : E} (hb : IntAt P b) : IntAt P (a + b) ↔ IntAt P a :=
  ⟨fun h => by simpa using h.add (IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_neg hb), fun h => h.add hb⟩

theorem phiQ_bdd : ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] (P : HeightOneSpectrum (𝓞 E)) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (k₀ r c' n' c n : ℕ), k₀ ≤ n' → k₀ ≤ n → r ≤ n' + c' → r ≤ n + c → (∀ x, LocE.PhiQ (qOf P) ξ k₀ r c' n' c n x ≠ 0 → IntHom P x) ∧ ∀ x y : (Fin (n' + c') → E) →ₗ[E] (Fin (n + c) → E), IntHom P y → LocE.PhiQ (qOf P) ξ k₀ r c' n' c n (x + (qOf P : E) • y) = LocE.PhiQ (qOf P) ξ k₀ r c' n' c n x := by
  intro E _ _ K _ P ξ k₀ r c' n' c n hk' hk hr' hr
  refine ⟨fun x hx => ?_, fun x y hy => ?_⟩
  · unfold LocE.PhiQ at hx
    split_ifs at hx with h
    · rw [intHom_iff]
      intro s l
      obtain ⟨a1, a2⟩ := fIdx_fPos hk l.2
      obtain ⟨b1, b2⟩ := fIdx_fPos hk' s.2
      have := h.1 _ _ a2 b2
      rw [entB_zero, a1, b1] at this
      have e : Loc.eN E (n' + c') s.1 = Pi.single s 1 := by
        funext i
        simp [Loc.eN, Pi.single_apply, Fin.ext_iff]
      rw [e] at this
      simpa [Loc.atN] using this
    · exact absurd rfl hx
  · have hq : (qOf P : E) ≠ 0 := NormalFormAtPrime.qOf_ne_zero P
    have hI := intAt_entB (qOf P) k₀ c' n' c n hy
    have e1 : ∀ p p', IntAt P (LocE.entB (qOf P) k₀ c' n' c n 0 0 (x + (qOf P : E) • y) p p') ↔
        IntAt P (LocE.entB (qOf P) k₀ c' n' c n 0 0 x p p') := fun p p' => by
      rw [entB_add, intAt_add_iff ((TopStep.intAt_nat (qOf P)).mul (hI p p'))]
    have e2 : ∀ p p', IntAt P (LocE.entB (qOf P) k₀ c' n' c n 0 0 (x + (qOf P : E) • y) p p' / (qOf P : E)) ↔
        IntAt P (LocE.entB (qOf P) k₀ c' n' c n 0 0 x p p' / (qOf P : E)) := fun p p' => by
      rw [entB_add, add_div, mul_div_cancel_left₀ _ hq, intAt_add_iff (hI p p')]
    unfold LocE.PhiQ
    split_ifs with h' h h
    rotate_left
    · exact absurd ⟨fun p p' a b => (e1 p p').1 (h'.1 p p' a b), fun p p' a b d => (e2 p p').1 (h'.2 p p' a b d)⟩ h
    · exact absurd ⟨fun p p' a b => (e1 p p').2 (h.1 p p' a b), fun p p' a b d => (e2 p p').2 (h.2 p p' a b d)⟩ h'
    · rfl
    · apply unitV_congr
      have hx : ∀ s t : Fin r, IntAt P (LocE.entB (qOf P) k₀ c' n' c n 0 0 x s.1 t.1) :=
        fun s t => h.1 _ _ (by have := s.2; omega) (by have := t.2; omega)
      refine (TopStep.det_int ?_).2.trans (Eq.trans ?_ (TopStep.det_int ?_).2.symm)
      · exact fun s t => (e1 _ _).2 (hx s t)
      swap
      · exact hx
      refine congrArg Matrix.det (Matrix.ext fun s t => ?_)
      change redP P (LocE.entB (qOf P) k₀ c' n' c n 0 0 (x + (qOf P : E) • y) s.1 t.1) =
        redP P (LocE.entB (qOf P) k₀ c' n' c n 0 0 x s.1 t.1)
      rw [entB_add, reduction_add (hx s t) ((TopStep.intAt_nat (qOf P)).mul (hI _ _)), reduction_mul (TopStep.intAt_nat (qOf P)) (hI _ _), TopStep.reduction_absNorm_eq_zero, zero_mul, add_zero]

end GlobalTheory.Proof.twistPrimeDatum_integral_support_and_invariant
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

noncomputable section

namespace GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz

variable {E : Type} [Field E] {n' c' n c : ℕ}

open NumberField IsDedekindDomain in
variable {E : Type} [Field E] {n' c' n c : ℕ} in
theorem _root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.chArg_add (x y : (Fin (n' + c') → E) →ₗ[E] (Fin (n + c) → E)) :
    _root_.Formalism.L2.Col.Loc.chArg (x + y) = _root_.Formalism.L2.Col.Loc.chArg x + _root_.Formalism.L2.Col.Loc.chArg y := by
  unfold _root_.Formalism.L2.Col.Loc.chArg
  simp only [LinearMap.add_apply, _root_.GlobalTheory.QNormal.atN_add, Finset.sum_add_distrib]

open NumberField IsDedekindDomain in
variable {E : Type} [Field E] {n' c' n c : ℕ} in
theorem _root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.chArg_smul (a : E) (x : (Fin (n' + c') → E) →ₗ[E] (Fin (n + c) → E)) :
    _root_.Formalism.L2.Col.Loc.chArg (a • x) = a * _root_.Formalism.L2.Col.Loc.chArg x := by
  unfold _root_.Formalism.L2.Col.Loc.chArg
  simp only [LinearMap.smul_apply, _root_.GlobalTheory.QNormal.atN_smul, Finset.mul_sum]

def freeMap (u : Loc.FC n' c' n c → E) : (Fin (n' + c') → E) →ₗ[E] (Fin (n + c) → E) :=
  Matrix.toLin' (Matrix.of fun (l : Fin (n + c)) (s : Fin (n' + c')) =>
    if hf : Loc.IsFree n' n c l.1 s.1 then u ⟨(l, s), hf⟩ else 0)

open NumberField IsDedekindDomain in
variable {E : Type} [Field E] {n' c' n c : ℕ} in
theorem _root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.periodXX1_add_smul (xj : (Fin n' → E) →ₗ[E] (Fin n → E))
    (t u : _root_.Formalism.L2.Col.Loc.FC n' c' n c → E) (a : E) :
    _root_.Formalism.L2.Col.Loc.xx1 xj (t + a • u) = _root_.Formalism.L2.Col.Loc.xx1 xj t + a • _root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.freeMap u := by
  unfold _root_.Formalism.L2.Col.Loc.xx1 _root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.freeMap
  rw [← map_smul, ← map_add (f := _)]
  congr 1
  ext l s
  simp only [Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  split_ifs <;> simp

variable [NumberField E] {P : HeightOneSpectrum (𝓞 E)}

open NumberField IsDedekindDomain in
variable {E : Type} [Field E] {n' c' n c : ℕ} in
variable [NumberField E] {P : HeightOneSpectrum (𝓞 E)} in
private lemma intAt_atN_of_intV {N : ℕ} {v : Fin N → E}
    (hv : _root_.GlobalTheory.QNormal.IntV P v) (i : ℕ) : _root_.Formalism.L2.Col.IntAt P (_root_.Formalism.L2.Col.Loc.atN v i) := by
  unfold _root_.Formalism.L2.Col.Loc.atN
  split_ifs with h
  · exact hv ⟨i, h⟩
  · exact _root_.GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P

open NumberField IsDedekindDomain in
variable {E : Type} [Field E] {n' c' n c : ℕ} in
variable [NumberField E] {P : HeightOneSpectrum (𝓞 E)} in
private lemma intV_eN' (N s : ℕ) :
    _root_.GlobalTheory.QNormal.IntV P (_root_.Formalism.L2.Col.Loc.eN E N s) := by
  intro l
  dsimp only [_root_.Formalism.L2.Col.Loc.eN]
  split_ifs
  · exact _root_.GlobalTheory.QNormal.intAt_one P
  · exact _root_.GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P

open NumberField IsDedekindDomain in
variable {E : Type} [Field E] {n' c' n c : ℕ} in
variable [NumberField E] {P : HeightOneSpectrum (𝓞 E)} in
theorem _root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.intAt_chArg
    {y : (Fin (n' + c') → E) →ₗ[E] (Fin (n + c) → E)} (hy : _root_.GlobalTheory.QNormal.IntHom P y) :
    _root_.Formalism.L2.Col.IntAt P (_root_.Formalism.L2.Col.Loc.chArg y) := by
  unfold _root_.Formalism.L2.Col.Loc.chArg
  exact _root_.GlobalTheory.QNormal.intAt_sum _ _ fun i _ =>
    intAt_atN_of_intV (hy _ (intV_eN' _ _)) _

open NumberField IsDedekindDomain in
variable {E : Type} [Field E] {n' c' n c : ℕ} in
variable [NumberField E] {P : HeightOneSpectrum (𝓞 E)} in
theorem _root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.intHom_freeMap {u : _root_.Formalism.L2.Col.Loc.FC n' c' n c → E}
    (hu : ∀ i, _root_.Formalism.L2.Col.IntAt P (u i)) : _root_.GlobalTheory.QNormal.IntHom P (_root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.freeMap u) := by
  rw [_root_.GlobalTheory.QNormal.intHom_iff]
  intro s l
  simp only [_root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.freeMap, Matrix.toLin'_apply, Matrix.mulVec_single_one,
    Matrix.transpose_apply, Matrix.col_apply, Matrix.of_apply]
  split_ifs with hf
  · exact hu _
  · exact _root_.GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P


open NumberField IsDedekindDomain in
variable {E : Type} [Field E] {n' c' n c : ℕ} in
variable [NumberField E] {P : HeightOneSpectrum (𝓞 E)} in
theorem _root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.integrand_bdd : ∀ (E : Type) [Field E] [NumberField E] (K : Type)
    [Field K] (P : HeightOneSpectrum (𝓞 E))
    (n' c' n c : ℕ) (psi : E → K) (D N : ℕ) (Psi : _root_.Formalism.L2.Col.Loc.SF E K (n' + c') (n + c)), N ≤ D →
    _root_.GlobalTheory.QNormal.CharTo P D psi → _root_.GlobalTheory.QNormal.HomBdd P N Psi →
    ∀ xj : (Fin n' → E) →ₗ[E] (Fin n → E),
      _root_.GlobalTheory.QNormal.FunBdd P N (_root_.GlobalTheory.QNormal.integrand psi Psi xj) ∧
      ∀ t : _root_.Formalism.L2.Col.Loc.FC n' c' n c → E, Psi (_root_.Formalism.L2.Col.Loc.xx1 xj t) ≠ 0 →
        _root_.Formalism.L2.Col.IntAt P ((_root_.Formalism.L2.Col.qOf P : E) ^ N * _root_.Formalism.L2.Col.Loc.chArg (_root_.Formalism.L2.Col.Loc.xx1 xj t)) := by
  intro E _ _ K _ P n' c' n c psi D N Psi hND hpsi hPsi xj
  obtain ⟨hPsi1, hPsi2⟩ := hPsi
  obtain ⟨hpsi1, hpsi2⟩ := hpsi
  have hchar : ∀ t : _root_.Formalism.L2.Col.Loc.FC n' c' n c → E, Psi (_root_.Formalism.L2.Col.Loc.xx1 xj t) ≠ 0 →
      _root_.Formalism.L2.Col.IntAt P ((_root_.Formalism.L2.Col.qOf P : E) ^ N * _root_.Formalism.L2.Col.Loc.chArg (_root_.Formalism.L2.Col.Loc.xx1 xj t)) := fun t ht => by
    rw [← _root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.chArg_smul]
    exact _root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.intAt_chArg (hPsi1 _ ht)
  refine ⟨?_, hchar⟩
  unfold _root_.GlobalTheory.QNormal.FunBdd
  refine ⟨fun t ht i => ?_, fun t u hu => ?_⟩
  · have hne : Psi (_root_.Formalism.L2.Col.Loc.xx1 xj t) ≠ 0 := fun h => ht (by simp [_root_.GlobalTheory.QNormal.integrand, h])
    have hint := (_root_.GlobalTheory.QNormal.intHom_iff _).1 (hPsi1 _ hne)
    obtain ⟨⟨l, s⟩, hf⟩ := i
    have hentry := hint s l
    simpa only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul,
      _root_.GlobalTheory.QNormal.linearMap_unfolding_apply_single, dif_pos hf] using hentry
  · have hfree := _root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.intHom_freeMap (P := P) hu
    have hPsi_eq : Psi (_root_.Formalism.L2.Col.Loc.xx1 xj (t + (_root_.Formalism.L2.Col.qOf P : E) ^ N • u)) = Psi (_root_.Formalism.L2.Col.Loc.xx1 xj t) := by
      rw [_root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.periodXX1_add_smul]
      exact hPsi2 _ _ hfree
    simp only [_root_.GlobalTheory.QNormal.integrand, hPsi_eq]
    by_cases h0 : Psi (_root_.Formalism.L2.Col.Loc.xx1 xj t) = 0
    · simp [h0]
    · congr 1
      rw [_root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.periodXX1_add_smul, _root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.chArg_add,
        _root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.chArg_smul, neg_add]
      have hx : _root_.Formalism.L2.Col.IntAt P ((_root_.Formalism.L2.Col.qOf P : E) ^ D * -_root_.Formalism.L2.Col.Loc.chArg (_root_.Formalism.L2.Col.Loc.xx1 xj t)) := by
        rw [mul_neg]
        exact _root_.GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_neg (_root_.GlobalTheory.Proof.NormalFormAtPrime.intAt_pow_mono hND (hchar t h0))
      have hy : _root_.Formalism.L2.Col.IntAt P (-((_root_.Formalism.L2.Col.qOf P : E) ^ N * _root_.Formalism.L2.Col.Loc.chArg (_root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.freeMap u))) :=
        _root_.GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_neg (_root_.GlobalTheory.Proof.NormalFormAtPrime.intAt_pow_mul N
          (_root_.GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.intAt_chArg hfree))
      rw [hpsi1 _ _ hx (_root_.GlobalTheory.Proof.NormalFormAtPrime.intAt_pow_mul D hy), hpsi2 _ hy, mul_one]

end GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

namespace GlobalTheory.Proof.unipotentRadicals_act_affine_unfoldingSpaces

variable {F : Type} [Field F] {n' c' n c : ℕ}

theorem hom_ext {a b : ℕ} {x y : (Fin a → F) →ₗ[F] (Fin b → F)}
    (h : ∀ s l, x (Pi.single s 1) l = y (Pi.single s 1) l) : x = y := by
  ext s l
  simpa using h s l

noncomputable def linPart (xj : (Fin n' → F) →ₗ[F] (Fin n → F)) :
    (Loc.FC n' c' n c → F) →ₗ[F] ((Fin (n' + c') → F) →ₗ[F] (Fin (n + c) → F)) where
  toFun t := Loc.xx1 xj t - Loc.xx1 xj 0
  map_add' t u := hom_ext fun s l => by
    simp only [LinearMap.sub_apply, LinearMap.add_apply, Pi.sub_apply, Pi.add_apply, linearMap_unfolding_apply_single]
    split_ifs <;> simp
  map_smul' a t := hom_ext fun s l => by
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Pi.sub_apply, Pi.smul_apply, linearMap_unfolding_apply_single, RingHom.id_apply]
    split_ifs <;> simp

theorem unfoldingAffineLinearMap_apply_freeEntry (xj : (Fin n' → F) →ₗ[F] (Fin n → F)) (t : Loc.FC n' c' n c → F) (p : Loc.FC n' c' n c) :
    Loc.xx1 xj t (Pi.single p.1.2 1) p.1.1 = t p := by
  rw [linearMap_unfolding_apply_single, dite_eq_left p.2]

theorem map_Ufl {xj : (Fin n' → F) →ₗ[F] (Fin n → F)} {x : (Fin (n' + c') → F) →ₗ[F] (Fin (n + c) → F)}
    (h1 : ∀ v, x (Loc.inX F n' c' v) = Loc.inX F n c (xj v))
    (h3 : ∀ s : ℕ, x (Loc.eN F (n' + c') (n' + s)) - Loc.eN F (n + c) (n + s) ∈ Loc.Ufl F n c s)
    (s : ℕ) {v : Fin (n' + c') → F} (hv : v ∈ Loc.Ufl F n' c' s) : x v ∈ Loc.Ufl F n c s := by
  have key : ∀ l : Fin (n' + c'), l.1 < n' + s → x (Pi.single l 1) ∈ Loc.Ufl F n c s := by
    intro l hl
    by_cases hln : l.1 < n'
    · have hsingle : (Pi.single l (1 : F) : Fin (n' + c') → F) =
          Loc.inX F n' c' (Pi.single (⟨l.1, hln⟩ : Fin n') 1) := by
        funext m
        rw [inX_apply]
        split_ifs with hm
        · by_cases hml : m = l
          · subst hml
            simp
          · have hne : (⟨m.1, hm⟩ : Fin n') ≠ ⟨l.1, hln⟩ := fun he => hml (Fin.ext (by simpa using he))
            simp [hml, hne]
        · have hml : m ≠ l := fun he => hm (he ▸ hln)
          simp [hml]
      rw [hsingle, h1]
      exact inX_mem_Ufl s _
    · have hle : n' ≤ l.1 := not_lt.1 hln
      have hsingle : (Pi.single l (1 : F) : Fin (n' + c') → F) = Loc.eN F (n' + c') (n' + (l.1 - n')) := by
        funext m
        rw [Nat.add_sub_cancel' hle]
        by_cases hml : m = l
        · subst hml
          simp [Loc.eN]
        · have hv : m.1 ≠ l.1 := fun he => hml (Fin.ext he)
          simp [Loc.eN, hml, hv]
      rw [hsingle, ← sub_add_cancel (x (Loc.eN F (n' + c') (n' + (l.1 - n'))))
        (Loc.eN F (n + c) (n + (l.1 - n')))]
      exact Submodule.add_mem _ (Ufl_mono (by omega) (h3 (l.1 - n'))) (eN_mem_Ufl (by omega))

  rw [← Finset.univ_sum_single v, map_sum]
  refine Submodule.sum_mem _ fun l _ => ?_
  by_cases hl : l.1 < n' + s
  · have hsm : (Pi.single l (v l) : Fin (n' + c') → F) = v l • Pi.single l 1 := by
      funext m
      by_cases hml : m = l
      · subst hml
        simp
      · simp [hml]
    rw [hsm, map_smul]
    exact Submodule.smul_mem _ _ (key l hl)
  · have hz : v l = 0 := (mem_Ufl.1 hv) l hl
    rw [hz, Pi.single_zero, map_zero]
    exact Submodule.zero_mem _

theorem affine_action : (∀ (F : Type) [Field F] (n' c' n c : ℕ), 1 ≤ c → c' = c + 1 → ∀ (xj : (Fin n' → F) →ₗ[F] (Fin n → F)) (x : (Fin (n' + c') → F) →ₗ[F] (Fin (n + c) → F)), (∃ t : Loc.FC n' c' n c → F, x = Loc.xx1 xj t) ↔ ((∀ v, x (Loc.inX F n' c' v) = Loc.inX F n c (xj v)) ∧ x (Loc.eN F (n' + c') n') = Loc.eN F (n + c) n ∧ ∀ s : ℕ, x (Loc.eN F (n' + c') (n' + s)) - Loc.eN F (n + c) (n + s) ∈ Loc.Ufl F n c s)) → ∀ (F : Type) [Field F] (n' c' n c : ℕ), 1 ≤ c → c' = c + 1 → ∀ r ∈ Loc.R1 F n c, ∀ r' ∈ Loc.R1 F n' c', ∀ xj' : (Fin n' → F) →ₗ[F] (Fin n → F), ∃ (xj : (Fin n' → F) →ₗ[F] (Fin n → F)) (T : (Loc.FC n' c' n c → F) ≃ₗ[F] (Loc.FC n' c' n c → F)) (b : Loc.FC n' c' n c → F), ∀ t, r.toLinearMap ∘ₗ Loc.xx1 xj t ∘ₗ r'.toLinearMap = Loc.xx1 xj' (T t + b) := by
  intro H F _ n' c' n c hc hc' r hr r' hr' xj'
  have hR : Loc.R1cond F n c r := hr.1
  have hR' : Loc.R1cond F n' c' r' := hr'.1
  obtain ⟨γ, hγ⟩ := exists_res hr
  obtain ⟨γ', hγ'⟩ := exists_res hr'
  obtain ⟨xj, hxj⟩ : ∃ xj : (Fin n' → F) →ₗ[F] (Fin n → F),
      xj = γ.symm.toLinearMap ∘ₗ xj' ∘ₗ γ'.symm.toLinearMap := ⟨_, rfl⟩
  have hy : ∀ t, ∃ t', r.toLinearMap ∘ₗ Loc.xx1 xj t ∘ₗ r'.toLinearMap = Loc.xx1 xj' t' := by
    intro t
    obtain ⟨c1, c2, c3⟩ := (H F n' c' n c hc hc' xj (Loc.xx1 xj t)).1 ⟨t, rfl⟩
    refine (H F n' c' n c hc hc' xj' _).2 ⟨?_, ?_, ?_⟩
    · intro v
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [hγ', c1, hγ, hxj]
      simp
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [hR'.2.1, c2, hR.2.1]
    · intro s
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      have hsplit : r (Loc.xx1 xj t (r' (Loc.eN F (n' + c') (n' + s)))) - Loc.eN F (n + c) (n + s) =
          r (Loc.xx1 xj t (Loc.eN F (n' + c') (n' + s)) - Loc.eN F (n + c) (n + s)) +
            (r (Loc.eN F (n + c) (n + s)) - Loc.eN F (n + c) (n + s)) +
            r (Loc.xx1 xj t (r' (Loc.eN F (n' + c') (n' + s)) - Loc.eN F (n' + c') (n' + s))) := by
        simp only [map_sub]
        abel
      rw [hsplit]
      exact Submodule.add_mem _ (Submodule.add_mem _ (hR.1 s _ (c3 s)) (hR.2.2 s))
        (hR.1 s _ (map_Ufl c1 c3 s (hR'.2.2 s)))
  obtain ⟨f, hf⟩ : ∃ f : (Loc.FC n' c' n c → F) → (Loc.FC n' c' n c → F), ∀ t p,
      f t p = (r.toLinearMap ∘ₗ Loc.xx1 xj t ∘ₗ r'.toLinearMap) (Pi.single p.1.2 1) p.1.1 :=
    ⟨_, fun _ _ => rfl⟩
  have hyf : ∀ t, r.toLinearMap ∘ₗ Loc.xx1 xj t ∘ₗ r'.toLinearMap = Loc.xx1 xj' (f t) := by
    intro t
    obtain ⟨t', ht'⟩ := hy t
    have hft : f t = t' := by
      funext p
      rw [hf, ht', unfoldingAffineLinearMap_apply_freeEntry]
    rw [hft, ht']
  obtain ⟨L, hL⟩ : ∃ L : (Loc.FC n' c' n c → F) →ₗ[F] (Loc.FC n' c' n c → F), ∀ t p,
      L t p = (r.toLinearMap ∘ₗ linPart xj t ∘ₗ r'.toLinearMap) (Pi.single p.1.2 1) p.1.1 :=
    ⟨{ toFun := fun t p => (r.toLinearMap ∘ₗ linPart xj t ∘ₗ r'.toLinearMap) (Pi.single p.1.2 1) p.1.1
       map_add' := fun t u => by
         funext p
         simp only [map_add (f := _), LinearMap.add_comp, LinearMap.comp_add, LinearMap.add_apply, Pi.add_apply]
       map_smul' := fun a t => by
         funext p
         simp only [map_smul, LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.smul_apply, Pi.smul_apply,
           RingHom.id_apply] }, fun _ _ => rfl⟩
  have hxx : ∀ t : Loc.FC n' c' n c → F, Loc.xx1 xj t = linPart xj t + Loc.xx1 xj 0 := by
    intro t
    simp only [linPart, LinearMap.coe_mk, AddHom.coe_mk, sub_add_cancel]
  have hLf : ∀ t, L t + f 0 = f t := by
    intro t
    funext p
    rw [Pi.add_apply, hL, hf, hf, hxx t]
    simp only [LinearMap.comp_add, LinearMap.add_comp, LinearMap.add_apply, Pi.add_apply]
  have hinj : Function.Injective L := by
    intro t u htu
    have hfe : f t = f u := by rw [← hLf t, ← hLf u, htu]
    have hyy : r.toLinearMap ∘ₗ Loc.xx1 xj t ∘ₗ r'.toLinearMap =
        r.toLinearMap ∘ₗ Loc.xx1 xj u ∘ₗ r'.toLinearMap := by rw [hyf t, hyf u, hfe]
    have hx : Loc.xx1 xj t = Loc.xx1 xj u := by
      refine LinearMap.ext fun v => ?_
      have hv := congrArg (fun g => r.symm (g (r'.symm v))) hyy
      simpa using hv
    funext p
    rw [← unfoldingAffineLinearMap_apply_freeEntry xj t p, ← unfoldingAffineLinearMap_apply_freeEntry xj u p, hx]
  refine ⟨xj, LinearEquiv.ofInjectiveEndo L hinj, f 0, fun t => ?_⟩
  rw [hyf t]
  congr 1
  exact (hLf t).symm

end GlobalTheory.Proof.unipotentRadicals_act_affine_unfoldingSpaces
end
