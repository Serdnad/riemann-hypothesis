module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle023
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle036
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle154
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1193
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle055
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2468
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2469
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1203
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1346
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2312
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1374
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2470
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1527
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2182
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2471
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle052
import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaSeriesTies
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivOfNotLinearIndependent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2458
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigOn

theorem _root_.GlobalTheory.T.hodgeLineMultiple_le_familyThreshold : Closed FamHyp fun Fm _ => ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x → ∀ ι : Fm.Ix x, 2 * (Fm.D x ι).R.r + 50 * (Fm.D x ι).R.r ^ 2 * ((Fm.D x ι).R.f * ((Fm.D x ι).R.r * (Fm.D x ι).R.r / 4)) + 2 ≤ (Fm.parT x hx ι).TO := by
  first | exact @GlobalTheory.HodgeMultNum.hodgeMult_le_TO | exact GlobalTheory.HodgeMultNum.hodgeMult_le_TO | (intros; apply GlobalTheory.HodgeMultNum.hodgeMult_le_TO <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical



namespace GlobalTheory.ResidueFourier

section Local

variable {k : Type} [Field k] [Fintype k]

theorem sum_char_trace {n r : ℕ} {ψ : AddChar k ℂ} (hψ : ψ.IsPrimitive) (w : Matrix (Fin n) (Fin r) k) :
    ∑ x : Matrix (Fin r) (Fin n) k, ψ (Matrix.trace (x * w)) =
      if w = 0 then ((Nat.card k : ℂ) ^ (n * r)) else 0 := by
  let L : Matrix (Fin r) (Fin n) k →+ k :=
    AddMonoidHom.mk' (fun x => Matrix.trace (x * w)) (fun a b => by rw [Matrix.add_mul, Matrix.trace_add])
  have h := AddChar.sum_eq_ite (ψ.compAddMonoidHom L)
  have h2 : ψ.compAddMonoidHom L = 0 ↔ w = 0 := by
    constructor
    · intro h0
      ext i j
      by_contra hne
      refine hψ hne ?_
      ext t
      have := DFunLike.congr_fun h0 (Matrix.single j i t)
      change ψ (Matrix.trace (Matrix.single j i t * w)) = 1 at this
      rw [Matrix.trace_single_mul, smul_eq_mul] at this
      rw [AddChar.mulShift_apply, mul_comm]
      exact this
    · rintro rfl
      ext x
      change ψ (Matrix.trace (x * (0 : Matrix (Fin n) (Fin r) k))) = 1
      simp
  refine Eq.trans h ?_
  by_cases hw : w = 0
  · rw [if_pos (h2.2 hw), if_pos hw, Nat.card_eq_fintype_card]
    have : Fintype.card (Matrix (Fin r) (Fin n) k) = Fintype.card k ^ (n * r) := by
      change Fintype.card (Fin r → Fin n → k) = _
      simp [pow_mul]
    rw [this]; push_cast; rfl
  · rw [if_neg (fun h => hw (h2.1 h)), if_neg hw]

theorem inversion {n r : ℕ} {ψ : AddChar k ℂ} (hψ : ψ.IsPrimitive) (f : Matrix (Fin n) (Fin r) k → ℂ)
    (u : Matrix (Fin n) (Fin r) k) :
    f u = ∑ x : Matrix (Fin r) (Fin n) k,
      (((Nat.card k : ℂ) ^ (n * r))⁻¹ * ∑ v, f v * ψ (Matrix.trace (-x * v))) * ψ (Matrix.trace (x * u)) := by
  have hc : ((Nat.card k : ℂ) ^ (n * r)) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 Nat.card_pos.ne')
  have h1 : ∀ x : Matrix (Fin r) (Fin n) k,
      (((Nat.card k : ℂ) ^ (n * r))⁻¹ * ∑ v, f v * ψ (Matrix.trace (-x * v))) * ψ (Matrix.trace (x * u)) =
      ∑ v, ((Nat.card k : ℂ) ^ (n * r))⁻¹ * f v * ψ (Matrix.trace (x * (u - v))) := fun x => by
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [mul_assoc, mul_assoc, mul_assoc, ← AddChar.map_add_eq_mul, ← Matrix.trace_add, Matrix.mul_sub, Matrix.neg_mul,
      neg_add_eq_sub]
  simp only [h1]
  rw [Finset.sum_comm, Finset.sum_eq_single u]
  · rw [← Finset.mul_sum, sum_char_trace hψ, if_pos (sub_self u)]
    field_simp
  · intro v _ hv
    rw [← Finset.mul_sum, sum_char_trace hψ, if_neg (fun h => hv (sub_eq_zero.1 h).symm), mul_zero]
  · simp

def embTop (n : ℕ) {r : ℕ} (g : Matrix (Fin r) (Fin r) k) : Matrix (Fin n) (Fin r) k :=
  fun i j => if h : i.val < r then g ⟨i.val, h⟩ j else 0

omit [Fintype k] in
theorem topL_embTop {n r : ℕ} (h : r ≤ n) (g : Matrix (Fin r) (Fin r) k) : topL r (embTop n g) = g := by
  ext i j
  have : i.val < n := lt_of_lt_of_le i.2 h
  simp [topL, embTop, this]

omit [Fintype k] in
theorem lowZero_embTop {n r : ℕ} (g : Matrix (Fin r) (Fin r) k) : LowZero r (embTop n g) := by
  intro i j hi _
  simp [embTop, not_lt.2 hi]

omit [Fintype k] in
theorem embTop_topL {n r : ℕ} {u : Matrix (Fin n) (Fin r) k} (hu : LowZero r u) : embTop n (topL r u) = u := by
  ext i j
  by_cases hi : i.val < r
  · simp [topL, embTop, hi]
  · simp [embTop, hi, hu i j (not_lt.1 hi) j.2]

omit [Fintype k] in
theorem trace_embTop {n r : ℕ} (h : r ≤ n) (x : Matrix (Fin r) (Fin n) k) (g : Matrix (Fin r) (Fin r) k) :
    Matrix.trace (x * embTop n g) = Matrix.trace (topL r x * g) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fin.sum_univ_add]
  have h2 : ∀ i : Fin r, i.val < r + t := fun i => lt_of_lt_of_le i.2 h
  simp [embTop, topL, h2]
  rfl

theorem transform {n r : ℕ} (h : r ≤ n) {ψ : AddChar k ℂ} (hψ : ψ.IsPrimitive) {ξ : kˣ →* ℂˣ} (hξ : ξ ≠ 1)
    (x : Matrix (Fin r) (Fin n) k) :
    ∑ v : Matrix (Fin n) (Fin r) k,
      (if h : LowZero r v ∧ IsUnit (topL r v).det then ((ξ h.2.unit : ℂˣ) : ℂ) ^ (-1 : ℤ) else 0) * ψ (Matrix.trace (x * v)) =
      (∑ g : GL (Fin r) k, (((ξ (Matrix.GeneralLinearGroup.det g))⁻¹ : ℂˣ) : ℂ) *
        ψ (Matrix.trace (g : Matrix (Fin r) (Fin r) k))) *
      (if h : IsUnit (topL r x).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) := by
  obtain ⟨h0, h1⟩ := GlobalTheory.matrixGaussSum_singular_and_invertible k ℂ ψ ξ r hψ hξ
  have step : ∑ v : Matrix (Fin n) (Fin r) k,
      (if h : LowZero r v ∧ IsUnit (topL r v).det then ((ξ h.2.unit : ℂˣ) : ℂ) ^ (-1 : ℤ) else 0) * ψ (Matrix.trace (x * v)) =
      ∑ g : GL (Fin r) k, (((ξ (Matrix.GeneralLinearGroup.det g))⁻¹ : ℂˣ) : ℂ) *
        ψ (Matrix.trace (topL r x * (g : Matrix (Fin r) (Fin r) k))) := by
    symm
    apply Finset.sum_of_injOn (fun g : GL (Fin r) k => embTop n (g : Matrix (Fin r) (Fin r) k))
    · intro a _ b _ hab
      have := congrArg (topL r) hab
      simp only [topL_embTop h] at this
      exact Units.ext this
    · intro a _
      simp
    · intro u _ hu
      rw [dif_neg, zero_mul]
      rintro ⟨hl, hd⟩
      exact hu ⟨((Matrix.isUnit_iff_isUnit_det _).2 hd).unit, by simp, embTop_topL hl⟩
    · intro g _
      have hx : IsUnit (topL r (embTop n (g : Matrix (Fin r) (Fin r) k))).det := by
        rw [topL_embTop h]; exact (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
      have hdet : hx.unit = Matrix.GeneralLinearGroup.det g := Units.ext (by simp [topL_embTop h])
      rw [dif_pos ⟨lowZero_embTop _, hx⟩, trace_embTop h, hdet, zpow_neg_one, Units.val_inv_eq_inv_val]
  rw [step]
  by_cases hy : IsUnit (topL r x).det
  · have hm := (Matrix.isUnit_iff_isUnit_det _).2 hy
    have hdet : Matrix.GeneralLinearGroup.det (hm.unit : GL (Fin r) k) = hy.unit :=
      Units.ext (by simp [Matrix.GeneralLinearGroup.det])
    have key := h1 hm.unit
    rw [hdet] at key
    simp only [IsUnit.unit_spec, one_mul] at key
    rw [key, dif_pos hy, mul_comm]
  · have hz : (topL r x).det = 0 := by simpa using hy
    rw [h0 _ hz, dif_neg hy, mul_zero]

end Local

theorem dite_prod {ι : Type} (Q : Finset ι) (p : ι → Prop) (f : ∀ i, p i → ℂ) :
    (if h : ∀ i ∈ Q, p i then ∏ i ∈ Q.attach, f i.1 (h i.1 i.2) else 0) =
      ∏ i ∈ Q.attach, if h : p i.1 then f i.1 h else 0 := by
  split_ifs with h
  · exact Finset.prod_congr rfl fun i _ => (dif_pos (h i.1 i.2)).symm
  · push_neg at h
    obtain ⟨i, hi, hp⟩ := h
    exact (Finset.prod_eq_zero (Finset.mem_attach Q ⟨i, hi⟩) (dif_neg hp)).symm

theorem omegaQ_fourier : ∀ (D : D7) [∀ PP : Pl D.host.E, Fintype (kP PP)] (Q : Finset (Pl D.host.E)) (n r : ℕ), r ≤ n → ∀ (ψP : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), (∀ PP ∈ Q, (ψP PP).IsPrimitive) → (∀ PP ∈ Q, ξ PP ≠ 1) → ∃ c : (∀ PP : ↥Q, Matrix (Fin r) (Fin n) (kP PP.1)) → ℂ, (∀ u : ∀ PP : Pl D.host.E, Matrix (Fin n) (Fin r) (kP PP), omegaQ Q r ξ (-1) u = ∑ x, c x * ∏ PP ∈ Q.attach, ψP PP.1 (Matrix.trace (x PP * u PP.1))) ∧ ∀ (x : ∀ PP : ↥Q, Matrix (Fin r) (Fin n) (kP PP.1)) (y : ∀ PP : Pl D.host.E, Matrix (Fin r) (Fin n) (kP PP)), (∀ PP : ↥Q, y PP.1 = x PP) → c (-x) = (∏ PP ∈ Q.attach, ((Nat.card (kP PP.1) : ℂ) ^ (n * r))⁻¹ * ∑ g : GL (Fin r) (kP PP.1), (((ξ PP.1 (Matrix.GeneralLinearGroup.det g))⁻¹ : ℂˣ) : ℂ) * ψP PP.1 (Matrix.trace (g : Matrix (Fin r) (Fin r) (kP PP.1)))) * omegaFlat Q r ξ y := by
  intro D _ Q n r hrn ψP ξ hψ hξ
  let f : ∀ PP : Pl D.host.E, Matrix (Fin n) (Fin r) (kP PP) → ℂ := fun PP v =>
    if h : LowZero r v ∧ IsUnit (topL r v).det then ((ξ PP h.2.unit : ℂˣ) : ℂ) ^ (-1 : ℤ) else 0
  let c : ∀ PP : Pl D.host.E, Matrix (Fin r) (Fin n) (kP PP) → ℂ := fun PP x =>
    ((Nat.card (kP PP) : ℂ) ^ (n * r))⁻¹ * ∑ v, f PP v * ψP PP (Matrix.trace (-x * v))
  refine ⟨fun x => ∏ PP ∈ Q.attach, c PP.1 (x PP), fun u => ?_, fun x y hxy => ?_⟩
  · have h1 : omegaQ Q r ξ (-1) u = ∏ PP ∈ Q.attach, f PP.1 (u PP.1) := by
      unfold omegaQ
      convert dite_prod Q (fun PP => LowZero r (u PP) ∧ IsUnit (topL r (u PP)).det)
        (fun PP h => ((ξ PP h.2.unit : ℂˣ) : ℂ) ^ (-1 : ℤ))
    have h2 : ∀ PP : ↥Q, f PP.1 (u PP.1) = ∑ x, c PP.1 x * ψP PP.1 (Matrix.trace (x * u PP.1)) := fun PP => by
      letI := Ideal.Quotient.field PP.1.asIdeal
      exact inversion (k := kP PP.1) (hψ PP.1 PP.2) (f PP.1) (u PP.1)
    rw [h1]
    simp only [h2, ← Finset.prod_mul_distrib, Finset.attach_eq_univ]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  · have h1 : omegaFlat Q r ξ y = ∏ PP ∈ Q.attach, if h : IsUnit (topL r (y PP.1)).det then ((ξ PP.1 h.unit : ℂˣ) : ℂ) else 0 := by
      unfold omegaFlat
      convert dite_prod Q (fun PP => IsUnit (topL r (y PP)).det) (fun PP h => ((ξ PP h.unit : ℂˣ) : ℂ))
    rw [h1, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun PP _ => ?_
    rw [hxy PP, mul_assoc]
    simp only [c, Pi.neg_apply, neg_neg]
    congr 1
    letI := Ideal.Quotient.field PP.1.asIdeal
    convert transform (k := kP PP.1) hrn (hψ PP.1 PP.2) (hξ PP.1 PP.2) (x PP)

end GlobalTheory.ResidueFourier
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical



namespace GlobalTheory.GaussUnit

theorem isIntegral_of_eq {x y : ℂ} (h : IsIntegral ℤ x) (e : y = x) : IsIntegral ℤ y := e ▸ h

theorem unitOff_of_two {N : ℕ} {u : ℂ} (h0 : u ≠ 0) {a b : ℕ} (ha : IsIntegral ℤ ((N : ℂ) ^ a * u))
    (hb : IsIntegral ℤ ((N : ℂ) ^ b * u⁻¹)) : UnitOff N u := by
  have hN : ∀ c : ℕ, IsIntegral ℤ ((N : ℂ) ^ c) := fun c => by
    have : IsIntegral ℤ ((N : ℕ) : ℂ) := by
      simpa using (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (N : ℤ)))
    exact this.pow c
  refine ⟨h0, a + b, ?_, ?_⟩
  · have := (hN b).mul ha
    refine isIntegral_of_eq (this) ?_
    ring
  · have := (hN a).mul hb
    refine isIntegral_of_eq (this) ?_
    ring

theorem unitOff_one (N : ℕ) : UnitOff N 1 :=
  unitOff_of_two (a := 0) (b := 0) one_ne_zero (by simpa using isIntegral_one) (by simpa using isIntegral_one)

theorem unitOff_mul {N : ℕ} {u v : ℂ} (hu : UnitOff N u) (hv : UnitOff N v) : UnitOff N (u * v) := by
  obtain ⟨hu0, a, ha, ha'⟩ := hu
  obtain ⟨hv0, b, hb, hb'⟩ := hv
  refine ⟨mul_ne_zero hu0 hv0, a + b, ?_, ?_⟩
  · refine isIntegral_of_eq (ha.mul hb) ?_
    ring
  · refine isIntegral_of_eq (ha'.mul hb') ?_
    rw [mul_inv]
    ring

theorem unitOff_prod {N : ℕ} {ι : Type*} (s : Finset ι) (f : ι → ℂ) (h : ∀ i ∈ s, UnitOff N (f i)) :
    UnitOff N (∏ i ∈ s, f i) :=
  Finset.prod_induction f (UnitOff N) (fun _ _ => unitOff_mul) (unitOff_one N) h

theorem unitOff_normalised {N q n r : ℕ} (hq : q ≠ 0) {m : ℕ} (hd : q ∣ N ^ m) (hrn : r ≤ n) {S : ℂ}
    (h1 : ‖S‖ ^ 2 = (q : ℝ) ^ (r ^ 2)) (h2 : IsIntegral ℤ S) (h3 : IsIntegral ℤ ((q : ℂ) ^ (r ^ 2) * S⁻¹)) :
    UnitOff N (((q : ℂ) ^ (n * r))⁻¹ * S) := by
  have hI : ∀ c : ℕ, IsIntegral ℤ ((c : ℕ) : ℂ) := fun c => by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (c : ℤ)))
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  have hS : S ≠ 0 := by
    rintro rfl
    have : (0 : ℝ) < (q : ℝ) ^ (r ^ 2) := pow_pos (by exact_mod_cast Nat.pos_of_ne_zero hq) _
    rw [← h1] at this
    simp at this
  obtain ⟨c, hc⟩ := hd
  have hcC : (N : ℂ) ^ m = q * c := by exact_mod_cast hc
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hrn
  refine unitOff_of_two (a := m * ((r + d) * r)) (b := 0) (mul_ne_zero (inv_ne_zero (pow_ne_zero _ hqC)) hS) ?_ ?_
  · refine isIntegral_of_eq (((hI c).pow ((r + d) * r)).mul h2) ?_
    rw [pow_mul, hcC, mul_pow]
    field_simp
  · refine isIntegral_of_eq (((hI q).pow (d * r)).mul h3) ?_
    rw [mul_inv, inv_inv]
    ring

theorem card_dvd_pow (k : Type) [Field k] [Fintype k] {N : ℕ} (hN : (N : k) = 0) : ∃ m, Fintype.card k ∣ N ^ m := by
  obtain ⟨p, hp⟩ := CharP.exists k
  obtain ⟨m, -, hm⟩ := FiniteField.card k p
  exact ⟨m, hm ▸ pow_dvd_pow_of_dvd ((CharP.cast_eq_zero_iff k p N).mp hN) _⟩

theorem unitOff_prod_gaussSum : ∀ (D : D7) [∀ PP : Pl D.host.E, Fintype (kP PP)] (Q : Finset (Pl D.host.E)) (n r : ℕ), r ≤ n → ∀ (ψP : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), (∀ PP ∈ Q, (ψP PP).IsPrimitive) → (∀ PP ∈ Q, ξ PP ≠ 1) → ∀ N : ℕ, N ≠ 0 → (∀ PP ∈ Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) → UnitOff N (∏ PP ∈ Q.attach, ((Nat.card (kP PP.1) : ℂ) ^ (n * r))⁻¹ * ∑ g : GL (Fin r) (kP PP.1), (((ξ PP.1 (Matrix.GeneralLinearGroup.det g))⁻¹ : ℂˣ) : ℂ) * ψP PP.1 (Matrix.trace (g : Matrix (Fin r) (Fin r) (kP PP.1)))) := by
  intro D _ Q n r hrn ψP ξ hψ hξ N _ hN
  refine unitOff_prod _ _ ?_
  rintro ⟨PP, hPP⟩ -
  haveI := PP.isMaximal
  letI : Field (kP PP) := Ideal.Quotient.field PP.asIdeal
  have h0 : (N : kP PP) = 0 := by
    have := Ideal.Quotient.eq_zero_iff_mem.mpr (hN PP hPP)
    simpa using this
  obtain ⟨m, hm⟩ := card_dvd_pow (kP PP) h0
  obtain ⟨h1, h2, h3, -⟩ := GlobalTheory.T.galois_matrix_gaussSum_eq_char_pow_mul (kP PP) (ψP PP) (ξ PP) r (hψ PP hPP) (hξ PP hPP) _ rfl
  rw [Nat.card_eq_fintype_card]
  exact unitOff_normalised Fintype.card_ne_zero hm hrn h1 h2 h3

end GlobalTheory.GaussUnit
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.linear_witt_model_unitary_action : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), ∀ ι, M.IsLinW B.ψ t b c ι →
    ∀ g ∈ UAt σ X (evFin F v), ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
      Acts (evFin F v) (om (g, h)) φ φ₁ → ι φ₁ = GlobalTheory.SplitFlip.omA (chrW χW t)⁻¹ (chrW χX t) (locMat t b g) (locMat t c h) (ι φ) := by
  first | exact @GlobalTheory.KSplit.om_linW_split | exact GlobalTheory.KSplit.om_linW_split | (intros; apply GlobalTheory.KSplit.om_linW_split <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.inertPlace_latticeStabilizer_vacuumScalar_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V' v, ∀ c : ℂ, Acts (evFin F v) (om' (k, 1)) (G.M'.vac v) (c • G.M'.vac v) → c = 1 := by
  first | exact @GlobalTheory.InertScalarLeft.scalar_eq_one | exact GlobalTheory.InertScalarLeft.scalar_eq_one | (intros; apply GlobalTheory.InertScalarLeft.scalar_eq_one <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.latticeStabilizer_vacuum_eigenvalue_eq_one_inertPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, ∀ c : ℂ, Acts (evFin F v) (om (1, k)) (G.M.vac v) (c • G.M.vac v) → c = 1 := by
  first | exact @GlobalTheory.DblVac.eigen_eq_one | exact GlobalTheory.DblVac.eigen_eq_one | (intros; apply GlobalTheory.DblVac.eigen_eq_one <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

theorem _root_.GlobalTheory.T.primeDivisorOver_restrict_etale : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] [IsLocallyNoetherian M] [IsLocallyNoetherian W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f] (n : ℕ) [SmoothOfRelativeDimension n p] [SmoothOfRelativeDimension n (f ≫ p)] (U : M.Opens), Etale (U.ι ≫ f) → ∀ y ∈ U, ∀ E' : DivOver (f ≫ p), E'.Through y → ∃ E : DivOver p, E.Through (f y) ∧ (∀ g : W.functionFieldˣ, E'.ord (Units.map (functionFieldMap f).toMonoidHom g) = E.ord g) ∧ ∀ η : RatForms p n, η ≠ 0 → (fun ω => @dite ℤ (∃ a, E'.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (GlobalTheory.EtaleKlt.ratPull p f n η) = (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) η := by
  first | exact @GlobalTheory.EtaleKlt.divOver_restrict | exact GlobalTheory.EtaleKlt.divOver_restrict | (intros; apply GlobalTheory.EtaleKlt.divOver_restrict <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.NabFix

theorem nab_fix : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T → ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')))
      (omd : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) →* Module.End ℂ ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → AF F) → ℂ)),
      IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) G.M'.co dd →
      IsUWeilSplit (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) B.ψ (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) dd X.α (diagCols (Fin (a + a'))) omd →
    ∀ R : (Fin a' × Fin (a + a') → AF F) → ℂ, R 0 ≠ 0 → Rest (evFin F v) (G.M'.vac v) R →
    ∀ n ∈ GlobalTheory.InertDbl.NabD σ G.W v, omd n (GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R)) =
      GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v w hin hT dd omd hdc hws R hR0 hRv n hn
  change GlobalTheory.InertDbl.UD σ G.W →* _ at omd
  set Φ := GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R) with hΦdef
  obtain ⟨c, hc⟩ := GlobalTheory.T.doubledWeil_inert_place_vacuum_eigenfunction F E σ B a a' G X om om' hTr v w hin hT dd omd hdc hws R hR0 hRv n hn.1
  change omd n Φ = c • Φ at hc
  obtain ⟨s, hs, hsn⟩ := GlobalTheory.T.integralUnipotentRadical_conj_to_square_inertPlace F E σ B hTr.base (a + a') G.W v w hin n hn
  have hs1 : omd s Φ = Φ := GlobalTheory.T.doubledWeilRep_fixes_vacuum_tensor_siegelParabolic_inert F E σ B a a' G X om om' hTr v w hin hT dd omd hdc hws R hR0 hRv s hs
  have hs2 : omd s⁻¹ Φ = Φ := by
    conv_lhs => rw [← hs1]
    change (omd _ * omd _) Φ = Φ
    rw [← omd.map_mul, inv_mul_cancel, map_one, one_apply_eq_self]
  have e1 : omd (s * n * s⁻¹) Φ = c • Φ := by
    simp only [omd.map_mul, mul_apply_eq_comp, hs2, hc, map_smul, hs1]
  have e2 : omd (n * n) Φ = (c * c) • Φ := by
    simp only [omd.map_mul, mul_apply_eq_comp, hc, map_smul, smul_smul]
  rw [hsn, e2] at e1
  by_cases hΦ : Φ = 0
  · rw [hΦ, map_zero]
  have hcc : c * c = c := smul_left_injective ℂ hΦ e1
  have h01 : c = 0 ∨ c = 1 := by
    rcases mul_eq_zero.1 (show c * (c - 1) = 0 by linear_combination hcc) with h | h
    · exact Or.inl h
    · exact Or.inr (by linear_combination h)
  rcases h01 with h0 | h1
  · exfalso
    apply hΦ
    have : omd n⁻¹ (omd n Φ) = Φ := by
      change (omd n⁻¹ * omd n) Φ = Φ
      rw [← omd.map_mul, inv_mul_cancel, map_one, one_apply_eq_self]
    rw [← this, hc, h0, zero_smul, map_zero]
  · change omd n Φ = Φ
    rw [hc, h1, one_smul]

end GlobalTheory.NabFix
end
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.weilDatumTransport_cm_preserves_admissibleForms : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
        ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om →
              ∀ p, ∀ l ∈ (adeleClass F).adm κ, l ∘ₗ om p ∈ (adeleClass F).adm κ := by
  first | exact @GlobalTheory.WeilAdmCM.transport_adm | exact GlobalTheory.WeilAdmCM.transport_adm | (intros; apply GlobalTheory.WeilAdmCM.transport_adm <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.AV.KerPart
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.MonObj
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_kernelPart_order_prime_to_p : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (A B : AbVar k) (f : A ⟶ B) (m : ℕ), 0 < m → ¬ p ∣ m → ∃ (H : Type) (_ : CommRing H) (_ : Algebra k H) (i : ptOver k H ⟶ A.X), KerPow f m H i ∧ ¬ p ∣ Module.finrank k H := by
  first | exact @GlobalTheory.AV.KerPart.exists_kerPow_not_dvd | exact GlobalTheory.AV.KerPart.exists_kerPow_not_dvd | (intros; apply GlobalTheory.AV.KerPart.exists_kerPow_not_dvd <;> assumption)
end
