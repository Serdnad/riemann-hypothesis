module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle098
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemZmuOfPowPred
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle158
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Smooth.Basic
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaFrameValueEqUnitSmoothConnectedBase
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentCharacterArgumentMulStabilizer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle180
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ContinuousAevalMvPolynomial

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

noncomputable section

namespace GlobalTheory.TwistRowMul

open GlobalTheory.TwistRowType

variable {E : Type} [Field E] [NumberField E]

theorem isUnit_of_reduction_mul {K : Type} [Field K] {P : HeightOneSpectrum (𝓞 E)} (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    {a b c : E} (h : redP P c = redP P a * redP P b) : LocE.unitV ξ c = LocE.unitV ξ a * LocE.unitV ξ b := by
  unfold LocE.unitV
  by_cases hc : IsUnit (redP P c)
  · have hab := hc
    rw [h] at hab
    have ha : IsUnit (redP P a) := isUnit_of_mul_isUnit_left hab
    have hb : IsUnit (redP P b) := isUnit_of_mul_isUnit_right hab
    rw [dite_eq_left ha, dite_eq_left hb, dite_eq_left hc, ← Units.val_mul, ← map_mul]
    have : hc.unit = ha.unit * hb.unit := Units.ext (by simpa using h)
    rw [this]
  · rw [dite_eq_right hc]
    by_cases ha : IsUnit (redP P a)
    · by_cases hb : IsUnit (redP P b)
      · exact absurd (h ▸ ha.mul hb) hc
      · rw [dite_eq_right hb, mul_zero]
    · rw [dite_eq_right ha, zero_mul]

variable [StarRing E]

theorem mem_parL' (P : HeightOneSpectrum (𝓞 E)) (q kj n c : ℕ) (x : Sp E (n + c)) :
    x ∈ LocE.parL P q kj n c ↔
      ∀ i : Fin (n + c), IntAt P (((q : E) ^ (if kj ≤ i.1 ∧ i.1 < n then (1 : ℤ) else 0))⁻¹ * x i) := by
  unfold LocE.parL LocE.sclLat
  rw [Submodule.mem_comap, mem_stdAt]
  rfl

theorem block_mul' (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (hq0 : q ≠ 0) (hq : (q : 𝓞 E) ∈ P.asIdeal) (kj n c : ℕ)
    {g g' : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hg : g ∈ stabL E (n + c) (stdAt E (n + c) P))
    (hg' : g' ∈ stabL E (n + c) (stdAt E (n + c) P)) (hp : g ∈ stabL E (n + c) (LocE.parL P q kj n c)) :
    (redHom P).mapMatrix (blockD P kj n hg * blockD P kj n hg') =
      (redHom P).mapMatrix (blockD P kj n (mul_mem hg hg')) := by
  ext s t
  have hs0 : kj + s.1 < n := by have := s.2; omega
  have hs : kj + s.1 < n + c := by omega
  set v : Sp E (n + c) := g' (Loc.eN E (n + c) (kj + t.1)) with hv
  have hvi : ∀ i, IntAt P (v i) := (GlobalTheory.TwistRowType.mem_stdAt P _).1 ((hg' _).2 (eN_mem P _ _))
  set w : Sp E (n + c) := fun l => if kj ≤ l.1 ∧ l.1 < n then 0 else v l with hw
  have hdec : v = w + ∑ u : Fin (n - kj), Loc.atN v (kj + u.1) • Loc.eN E (n + c) (kj + u.1) := by
    funext l
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Loc.eN, hw, smul_eq_mul]
    by_cases hl : kj ≤ l.1 ∧ l.1 < n
    · have hl2 := l.2
      rw [if_pos hl, zero_add, Finset.sum_eq_single (⟨l.1 - kj, by omega⟩ : Fin (n - kj))]
      · have e : kj + (l.1 - kj) = l.1 := by omega
        simp only [e, if_true, mul_one, Loc.atN]
        rw [dite_eq_left hl2]
      · intro u _ hu
        rw [if_neg, mul_zero]
        intro h
        apply hu
        apply Fin.ext
        simp only
        omega
      · simp
    · rw [if_neg hl, Finset.sum_eq_zero, add_zero]
      intro u _
      have := u.2
      rw [if_neg (by omega), mul_zero]
  have hwp : w ∈ LocE.parL P q kj n c := by
    rw [mem_parL']
    intro i
    by_cases hl : kj ≤ i.1 ∧ i.1 < n
    · simp only [hw, if_pos hl, mul_zero]
      exact (intSub P).zero_mem
    · simp only [hw, if_neg hl, zpow_zero, inv_one, one_mul]
      exact hvi i
  have hgw := (mem_parL' P q kj n c _).1 ((hp w).2 hwp) ⟨kj + s.1, hs⟩
  rw [if_pos ⟨by simp, hs0⟩, zpow_one] at hgw
  have hqE : (q : E) ≠ 0 := Nat.cast_ne_zero.2 hq0
  have hqi : IntAt P (q : E) := natCast_mem (intSub P) q
  have e1 : g w ⟨kj + s.1, hs⟩ = (q : E) * ((q : E)⁻¹ * g w ⟨kj + s.1, hs⟩) := by
    rw [mul_inv_cancel_left₀ hqE]
  have hgwi : IntAt P (g w ⟨kj + s.1, hs⟩) := by rw [e1]; exact hqi.mul hgw
  have hred : redP P (g w ⟨kj + s.1, hs⟩) = 0 := by
    rw [e1, reduction_mul hqi hgw]
    have : redP P (q : E) = 0 := by
      have h := reduction_coe P (q : 𝓞 E)
      rw [map_natCast] at h
      rw [h, Ideal.Quotient.eq_zero_iff_mem]
      exact hq
    rw [this, zero_mul]
  have key : (⟨g w ⟨kj + s.1, hs⟩, hgwi⟩ : intSub P) + (blockD P kj n hg * blockD P kj n hg') s t =
      blockD P kj n (mul_mem hg hg') s t := by
    apply Subtype.ext
    have h2 : (blockD P kj n (mul_mem hg hg') s t : E) = g v ⟨kj + s.1, hs⟩ := by
      simp only [blockD, Matrix.of_apply, Loc.atN]
      rw [dite_eq_left hs]
      rfl
    have h1 : g v ⟨kj + s.1, hs⟩ = g w ⟨kj + s.1, hs⟩ +
        ∑ u : Fin (n - kj), Loc.atN v (kj + u.1) * g (Loc.eN E (n + c) (kj + u.1)) ⟨kj + s.1, hs⟩ := by

      conv_lhs => rw [hdec, map_add (f := _), map_sum]
      simp only [map_smul, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [h2, h1, Matrix.mul_apply, Subring.coe_add, AddSubmonoidClass.coe_finsetSum]
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Subring.coe_mul, mul_comm]
    congr 1
    simp only [blockD, Matrix.of_apply, Loc.atN]
    rw [dite_eq_left hs]
  have h3 := congrArg (redHom P) key
  rw [map_add (f := _), redHom_apply, hred, zero_add] at h3
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, h3]
  rfl

theorem lamQB_mul {K : Type} [Field K] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (hq0 : q ≠ 0) (hq : (q : 𝓞 E) ∈ P.asIdeal)
    (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (kj n c : ℕ) {g g' : Sp E (n + c) ≃ₗ[E] Sp E (n + c)}
    (hg : g ∈ LocE.JQ P q kj n c) (hg' : g' ∈ LocE.JQ P q kj n c) :
    LocE.lamQB ξ kj n (g * g').toLinearMap = LocE.lamQB ξ kj n g.toLinearMap * LocE.lamQB ξ kj n g'.toLinearMap := by
  have hg1 : g ∈ stabL E (n + c) (stdAt E (n + c) P) := hg.1
  have hg2 : g' ∈ stabL E (n + c) (stdAt E (n + c) P) := hg'.1
  unfold LocE.lamQB
  rw [← mul_inv]
  congr 1
  apply isUnit_of_reduction_mul
  rw [redP_det_block P kj n hg1, redP_det_block P kj n hg2, redP_det_block P kj n (mul_mem hg1 hg2), ← Matrix.det_mul,
    ← map_mul, block_mul' P q hq0 hq kj n c hg1 hg2 hg.2]

theorem lamRow_mul : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), P ∉ Pr.vGs → ∀ g ∈ Jat (Pr := Pr) (R := R) sharp j P, ∀ g' ∈ Jat (Pr := Pr) (R := R) sharp j P, lamRow Ch mu sharp j P (g * g').toLinearMap = lamRow Ch mu sharp j P g.toLinearMap * lamRow Ch mu sharp j P g'.toLinearMap := by
  intro X Pr R Ch S mu sharp j P hP g hg g' hg'
  unfold Jat at hg hg'
  rw [if_neg hP] at hg hg'
  unfold lamRow
  rw [if_neg hP, if_neg hP, if_neg hP]
  exact lamQB_mul P (qOf P) (fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)) (Ideal.absNorm_mem _) _ _ _ _ hg hg'

end GlobalTheory.TwistRowMul

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

noncomputable section

namespace GlobalTheory.Mem.Col2.IdxEx.Cong

open GlobalTheory.LastSteps

section Loc

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}

omit [StarRing E] in
theorem unitV_one (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) : LocE.unitV χ (1 : E) = 1 := by
  have h : IsUnit (redP P (1 : E)) := by
    rw [GlobalTheory.TopStep.reduction_one₂]
    exact isUnit_one
  have h1 : h.unit = 1 := Units.ext (by rw [IsUnit.unit_spec, GlobalTheory.TopStep.reduction_one₂, Units.val_one])
  unfold LocE.unitV
  rw [dite_eq_left h, h1, map_one, Units.val_one]

omit [StarRing E] in
theorem unitV_det_delta (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {t : ℕ} {A : Fin t → Fin t → E}
    (hA : ∀ s s', A s s' = if s = s' then 1 else 0) : LocE.unitV χ (Matrix.det (Matrix.of fun s s' => A s s')) = 1 := by
  have : (Matrix.of fun s s' => A s s') = 1 := by
    ext s s'
    rw [Matrix.of_apply, hA, Matrix.one_apply]
  rw [this, Matrix.det_one, unitV_one]


omit [NumberField E] [StarRing E] in
theorem entB_id (q : ℕ) {k₀ c n : ℕ} (hk : k₀ ≤ n) (ex : ℕ → ℕ) {p p' : ℕ} (hp : p < n + c) (hp' : p' < n + c) :
    LocE.entB q k₀ c n c n ex ex (LinearMap.id : HomE E (n + c) (n + c)) p p' = if p = p' then 1 else 0 := by
  have h1 : LocE.fIdx k₀ c n p < n + c := by
    unfold LocE.fIdx
    split_ifs <;> omega
  have h2 : LocE.fIdx k₀ c n p = LocE.fIdx k₀ c n p' ↔ p = p' := by
    refine ⟨fun h => ?_, fun h => by rw [h]⟩
    unfold LocE.fIdx at h
    split_ifs at h <;> omega
  unfold LocE.entB Loc.atN
  rw [dite_eq_left h1, LinearMap.id_apply]
  unfold Loc.eN
  by_cases h : p = p'
  · subst h
    simp
  · rw [if_neg h, if_neg (fun h' => h (h2.1 h')), zero_mul]

variable (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)

omit [StarRing E] in
theorem blocks_delta {r t j : ℕ} {M : ℕ → ℕ → E}
    (hM : ∀ p p', p < r + j * t → p' < r + j * t → M p p' = if p = p' then 1 else 0) :
    ∏ i ∈ Finset.range j, LocE.unitV (χ i)
      (Matrix.det (Matrix.of fun s s' : Fin t => M (r + i * t + s.1) (r + i * t + s'.1))) = 1 := by
  refine Finset.prod_eq_one fun i hi => unitV_det_delta _ fun s s' => ?_
  have h1 : ∀ s : Fin t, r + i * t + s.1 < r + j * t := fun s => by
    have := Finset.mem_range.1 hi
    have := s.2
    nlinarith
  rw [hM _ _ (h1 s) (h1 s')]
  simp [Fin.ext_iff]

omit [StarRing E] in
theorem int_delta {N : ℕ} {M : ℕ → ℕ → E} (hM : ∀ p p', p < N → p' < N → M p p' = if p = p' then 1 else 0)
    (p p' : ℕ) (h : p < N) (h' : p' < N) : IntAt P (M p p') := by
  rw [hM _ _ h h']
  split_ifs
  · exact GlobalTheory.TopStep.intAt_one
  · exact GlobalTheory.TopStep.intAt_zero

omit [StarRing E] in
theorem lamGv_delta {r t j : ℕ} {M : ℕ → ℕ → E}
    (hM : ∀ p p', p < r + j * t → p' < r + j * t → M p p' = if p = p' then 1 else 0) :
    LocE.lamGv ψ₀ χ r t j M = 1 := by
  unfold LocE.lamGv
  rw [blocks_delta χ hM, mul_one, Finset.sum_eq_zero, GlobalTheory.TopStep.reduction_zero, AddChar.map_zero_eq_one]
  intro i hi
  have := Finset.mem_range.1 hi
  rw [hM _ _ (by omega) (by omega), if_neg (by omega)]

omit [StarRing E] in
theorem lamGvS_delta {k₀ r t j : ℕ} (hk : k₀ ≤ r) {M : ℕ → ℕ → E}
    (hM : ∀ p p', p < r + j * t → p' < r + j * t → M p p' = if p = p' then 1 else 0) :
    LocE.lamGvS ψ₀ χ k₀ r t j M = 1 := by
  unfold LocE.lamGvS
  rw [blocks_delta χ hM, mul_one, Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero, GlobalTheory.TopStep.reduction_zero,
    AddChar.map_zero_eq_one]
  all_goals
    intro i hi
    have := Finset.mem_range.1 hi
    rw [hM _ _ (by omega) (by omega), if_neg (by omega)]

theorem lamQB_cong (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (kj n c : ℕ) {y : HomE E (n + c) (n + c)}
    (hy : y ∈ homS (LocE.lamY P (qOf P) n c 0) (LocE.lamY P (qOf P) n c 0)) :
    LocE.lamQB ξ kj n (LinearMap.id + (qOf P : E) • y) = 1 := by
  unfold LocE.lamQB
  have hl : ∀ s : Fin (n - kj), kj + s.1 < n + c := fun s => by
    have := s.2
    omega
  have e : (fun s t : Fin (n - kj) => Loc.atN ((LinearMap.id + (qOf P : E) • y : HomE E (n + c) (n + c))
      (Loc.eN E (n + c) (kj + t.1))) (kj + s.1)) =
      fun s t : Fin (n - kj) => (if s = t then 1 else 0) + (qOf P : E) * y (Pi.single ⟨_, hl t⟩ 1) ⟨_, hl s⟩ := by
    funext s t
    unfold Loc.atN
    rw [dite_eq_left (hl s), eN_eq (hl t)]
    simp [Pi.single_apply, Fin.ext_iff]
  rw [e, unitV_congr ξ (redP_det_add_q (A := fun s t => if s = t then 1 else 0) (fun s t => ?_) fun s t => ?_),
    unitV_det_delta ξ fun _ _ => rfl, inv_one]
  · split_ifs
    · exact GlobalTheory.TopStep.intAt_one
    · exact GlobalTheory.TopStep.intAt_zero
  · simpa [LocE.scE] using mem_homS_sclLat.1 hy ⟨_, hl s⟩ ⟨_, hl t⟩

end Loc

theorem lamRow_cong : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), j < R.m → ∀ y : HomE X.E (R.N j + cOf R j) (R.N j + cOf R j), (∀ x ∈ lamYat (Pr := Pr) (R := R) j P, y x ∈ lamYat (Pr := Pr) (R := R) j P) → lamRow Ch mu sharp j P (LinearMap.id + (qOf P : X.E) • y) = 1 := by
  intro X Pr R Ch S mu sharp j P hj y hy
  have hN : R.N j + cOf R j = R.r + j * R.t := by
    unfold Ranks.N cOf Ranks.r
    rw [mul_add, mul_one]
    omega
  have hk : R.k ≤ R.N j := Nat.le_add_right _ _
  have hr : R.k ≤ R.r := by
    unfold Ranks.r
    omega
  unfold lamYat at hy
  unfold lamRow
  by_cases hP : P ∈ Pr.vGs
  · rw [if_pos hP] at hy ⊢
    have hZ := entB_int R.k (x := y) hy
    have hM : ∀ p p', p < R.r + j * R.t → p' < R.r + j * R.t →
        LocE.entB (qOf P) R.k (cOf R j) (R.N j) (cOf R j) (R.N j) (fun i => i + 1) (fun i => i + 1)
          (LinearMap.id : HomE X.E (R.N j + cOf R j) (R.N j + cOf R j)) p p' = if p = p' then 1 else 0 :=
      fun p p' h h' => entB_id _ hk _ (hN ▸ h) (hN ▸ h')
    split_ifs
    · unfold LocE.lamGBS
      rw [entB_add_smul, lamGvS_congr _ _ (int_delta hM) hZ, lamGvS_delta _ _ hr hM]
    · unfold LocE.lamGB
      rw [entB_add_smul, lamGv_congr _ _ (int_delta hM) hZ, lamGv_delta _ _ hM]
  · rw [if_neg hP] at hy ⊢
    exact lamQB_cong _ _ _ _ hy

end GlobalTheory.Mem.Col2.IdxEx.Cong

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

theorem _root_.GlobalTheory.T.norm_one_det_eq_one : ∀ (F : Type) [Field F] (n c : ℕ), ∀ r ∈ Loc.N1 F n c, LinearEquiv.det r = 1 := by
  first | exact @GlobalTheory.Mem.Col2.IdxEx.det_eq_one_of_mem_unip | exact GlobalTheory.Mem.Col2.IdxEx.det_eq_one_of_mem_unip | (intros; apply GlobalTheory.Mem.Col2.IdxEx.det_eq_one_of_mem_unip <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

namespace GlobalTheory.Mem.Col2.IdxEx

theorem jat_le_stab_lamY {X : Fields} {Pr : Primes X} {R : Ranks} (sharp : Bool) (j : ℕ)
    (P : HeightOneSpectrum (𝓞 X.E)) (hP : P ∈ Pr.vGs) (g : AutY X R j) (hg : g ∈ Jat (Pr := Pr) sharp j P) :
    g ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) j P) := by
  unfold Jat at hg
  rw [if_pos hP] at hg
  unfold lamYat
  rw [if_pos hP]
  split_ifs at hg
  · exact hg.1
  · exact hg.1

theorem prCat_le_GLint : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), P ∈ Pr.vGs → ∀ h ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) j P), prCat (Pr := Pr) sharp j P h ≤ GLint X.E (R.N j) P := by
  intro X Pr R sharp j P hP h hh g hg
  obtain ⟨r, ⟨-, hr⟩, hrg⟩ := hg
  have e : (MulAut.conj h⁻¹).toMonoidHom r = h⁻¹ * r * h := by simp
  have hr' : (MulAut.conj h⁻¹).toMonoidHom r ∈ Jat (Pr := Pr) sharp j P := hr
  rw [e] at hr'
  have h1 := jat_le_stab_lamY sharp j P hP _ hr'
  have h2 := mul_mem (mul_mem hh h1) (inv_mem hh)
  have e2 : h * (h⁻¹ * r * h) * h⁻¹ = r := by group
  rw [e2] at h2
  unfold lamYat at h2
  rw [if_pos hP] at h2
  have key : ∀ x : Sp X.E (R.N j), Loc.inX X.E (R.N j) (cOf R j) x ∈
      LocE.lamY P (qOf P) (R.N j) (cOf R j) (fun i => i + 1) ↔ x ∈ stdAt X.E (R.N j) P := fun x =>
    ⟨fun hx => by simpa only [GlobalTheory.CongLevel.resX_inX] using GlobalTheory.CongLevel.resX_mem P _ _ _ _ hx,
      GlobalTheory.CongLevel.inX_mem_lamY P _ _ _ x⟩
  intro x
  have h3 := h2 (Loc.inX X.E (R.N j) (cOf R j) x)
  rw [hrg x] at h3
  exact (key _).symm.trans (h3.trans (key _))

end GlobalTheory.Mem.Col2.IdxEx
end

section

open Polynomial

namespace GlobalTheory.ContRoot

open GlobalTheory.AffinePoints

theorem nonempty_algHom (B : Type) [CommRing B] [Nontrivial B] [Algebra ℂ B]
    [Algebra.FiniteType ℂ B] : Nonempty (B →ₐ[ℂ] ℂ) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal B
  let _ := Ideal.Quotient.field m
  have : Module.Finite ℂ (B ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℂ (B ⧸ m)
  exact ⟨(IsAlgClosed.lift : (B ⧸ m) →ₐ[ℂ] ℂ).comp (Ideal.Quotient.mkₐ ℂ m)⟩

theorem exists_monic_prime_dvd (B : Type) [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
    {n : ℕ} (hn : 0 < n) (u : B) :
    ∃ P : B[X], P.Monic ∧ Prime P ∧ 0 < P.natDegree ∧ P ∣ X ^ n - C u := by
  let L := AlgebraicClosure (FractionRing B)
  have hinj : Function.Injective (algebraMap B L) := by
    rw [IsScalarTower.algebraMap_eq B (FractionRing B) L]
    exact (algebraMap (FractionRing B) L).injective.comp (IsFractionRing.injective B _)
  have : FaithfulSMul B L := (faithfulSMul_iff_algebraMap_injective B L).2 hinj
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap B L u) hn
  have h0 : aeval β (X ^ n - C u : B[X]) = 0 := by simp [hβ]
  have hint : IsIntegral B β := ⟨_, monic_X_pow_sub_C u hn.ne', h0⟩
  exact ⟨minpoly B β, minpoly.monic hint, minpoly.prime_of_isIntegrallyClosed hint,
    minpoly.natDegree_pos hint, minpoly.isIntegrallyClosed_dvd hint h0⟩

theorem exists_pow_eq_of_continuous_root : ∀ (B : Type) [CommRing B] [IsDomain B] [Algebra ℂ B] [Algebra.Smooth ℂ B] (n : ℕ) (u : Bˣ) (ρ : (B →ₐ[ℂ] ℂ) → ℂ), 0 < n → (∀ (m : ℕ) (V : Set (Fin m → ℂ)) (s : (Fin m → ℂ) → (B →ₐ[ℂ] ℂ)), IsOpen V → (∀ a : B, DifferentiableOn ℂ (fun p => s p a) V) → ContinuousOn (fun p => ρ (s p)) V) → (∀ ψ : B →ₐ[ℂ] ℂ, ρ ψ ^ n = ψ (u : B)) → ∃ b : B, b ^ n = u := by
  intro B _ _ _ _ n u ρ hn hc hρ
  have hρc : Continuous ρ := GlobalTheory.RootConst.continuous_of_holomorphic_families B ρ hc
  have := GlobalTheory.isIntegrallyClosed_of_smooth ℂ B
  obtain ⟨P, hm, hp, hd, hdvd⟩ := exists_monic_prime_dvd B hn (u : B)
  have hdom : IsDomain (AdjoinRoot P) := AdjoinRoot.isDomain_of_prime hp
  have hft : Algebra.FiniteType ℂ (AdjoinRoot P) :=
    Algebra.FiniteType.trans (S := B) inferInstance inferInstance
  have hconn := GlobalTheory.RootConst.preconnectedSpace_algHom (AdjoinRoot P)
  let φ : B →ₐ[ℂ] AdjoinRoot P := IsScalarTower.toAlgHom ℂ B (AdjoinRoot P)
  have hroot : AdjoinRoot.root P ^ n = φ u := by
    have h := (AdjoinRoot.mk_eq_zero (f := P)).2 hdvd
    rw [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, sub_eq_zero] at h
    exact h
  have hu : ∀ ψ : B →ₐ[ℂ] ℂ, ψ u ≠ 0 := fun ψ => (u.isUnit.map ψ).ne_zero
  have hρ0 : ∀ ψ, ρ ψ ≠ 0 := fun ψ h => hu ψ (by rw [← hρ, h, zero_pow hn.ne'])
  have hcont : Continuous fun χ : AdjoinRoot P →ₐ[ℂ] ℂ =>
      χ (AdjoinRoot.root P) / ρ (comap φ χ) :=
    (continuous_eval _).div (hρc.comp (continuous_comap φ)) fun _ => hρ0 _
  have hconst := GlobalTheory.RootConst.eq_of_pow_eq_one hcont hn fun χ => by
    rw [div_pow, ← map_pow, hroot, hρ, comap_apply]
    exact div_self (hu (comap φ χ))
  obtain ⟨ψ⟩ := nonempty_algHom B
  have key : ∀ z, (P.map (ψ : B →+* ℂ)).IsRoot z → ∃ χ : AdjoinRoot P →ₐ[ℂ] ℂ,
      comap φ χ = ψ ∧ χ (AdjoinRoot.root P) = z := by
    intro z hz
    have hz' : P.eval₂ (ψ : B →+* ℂ) z = 0 := by rw [← eval_map]; exact hz
    refine ⟨AdjoinRoot.liftAlgHom P ψ z hz', ?_, by simp⟩
    ext b
    simp [φ]
  have huniq : ∀ z w, (P.map (ψ : B →+* ℂ)).IsRoot z → (P.map (ψ : B →+* ℂ)).IsRoot w →
      z = w := by
    intro z w hz hw
    obtain ⟨χ, h1, h2⟩ := key z hz
    obtain ⟨χ', h1', h2'⟩ := key w hw
    have h := hconst χ χ'
    simp only [h1, h1', h2, h2'] at h
    exact (div_left_inj' (hρ0 ψ)).1 h
  have hsep : (P.map (ψ : B →+* ℂ)).Separable := by
    refine (separable_X_pow_sub_C (n := n) (ψ u) (Nat.cast_ne_zero.2 hn.ne') (hu ψ)).of_dvd ?_
    simpa using Polynomial.map_dvd (ψ : B →+* ℂ) hdvd
  have hne : P.map (ψ : B →+* ℂ) ≠ 0 := (hm.map _).ne_zero
  have hdeg : P.natDegree ≤ 1 := by
    rw [← hm.natDegree_map (ψ : B →+* ℂ),
      (IsAlgClosed.splits (P.map (ψ : B →+* ℂ))).natDegree_eq_card_roots,
      ← Multiset.toFinset_card_of_nodup (nodup_roots hsep)]
    refine Finset.card_le_one.2 fun a ha b hb => huniq a b ?_ ?_
    · exact (mem_roots hne).1 (Multiset.mem_toFinset.1 ha)
    · exact (mem_roots hne).1 (Multiset.mem_toFinset.1 hb)
  have h1 : P = X + C (P.coeff 0) := hm.eq_X_add_C (le_antisymm hdeg hd)
  refine ⟨-P.coeff 0, ?_⟩
  have h2 : P.eval (-P.coeff 0) = 0 := by
    rw [congrArg (eval (-P.coeff 0)) h1]; simp
  have h3 := eval_eq_zero_of_dvd_of_eval_eq_zero hdvd h2
  simpa [sub_eq_zero] using h3

end GlobalTheory.ContRoot
end
