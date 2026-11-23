module

public import Formalism.LocalToGlobal.Columns.Bundle023
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CongruenceLevelEqDepthSucc
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemZmuOfPowPred
import Formalism.LocalToGlobal.Columns.ChainInst
public import Formalism.LocalToGlobal.Columns.ChainTopLawTw
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle210
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle097
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle123
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValuationLeOneOfMemZmu
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle117
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2 GlobalTheory.TopStep

namespace GlobalTheory.BlockDecompositionK1

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)}

theorem reduction_eq_zero_of_integral_absNorm_pow_inv_mul {c : ℕ} {a : E} (h : IntAt P (((qOf P : E) ^ (c + 1))⁻¹ * a)) : redP P a = 0 := by
  apply redP_eq_zero_of_div
  have hq := qOf_ne_zero (P := P)
  have h2 := (intAt_pow (intAt_nat (P := P) (qOf P)) c).mul h
  convert h2 using 1
  rw [pow_succ]
  field_simp

theorem intAt_inv_of_isUnit {a : E} (ha : IntAt P a) (hu : IsUnit (redP P a)) : a ≠ 0 ∧ IntAt P a⁻¹ := by
  obtain ⟨r, s, hs, h⟩ := id ha
  have hsp := reduction_spec P hs h
  have hr : r ∉ P.asIdeal := fun hr => by
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hr] at hsp
    have hs0 : (Ideal.Quotient.mk P.asIdeal) s ≠ 0 := fun h0 => hs (Ideal.Quotient.eq_zero_iff_mem.1 h0)
    exact hs0 ((hu.mul_left_eq_zero).1 hsp)
  have hr0 : algebraMap (𝓞 E) E r ≠ 0 := by
    rw [Ne, FaithfulSMul.algebraMap_eq_zero_iff]
    intro h0
    exact hr (h0 ▸ Ideal.zero_mem _)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [mul_zero] at h
    exact hr0 h.symm
  refine ⟨ha0, ?_⟩
  have h1 := (IntAt.coe P s).div_of_notMem hr
  convert h1 using 1
  rw [eq_div_iff hr0, ← h]
  field_simp

theorem mulVec_mem_stdAt {n : ℕ} {M : Matrix (Fin n) (Fin n) E} (hM : ∀ i l, IntAt P (M i l)) {x : Sp E n}
    (hx : x ∈ stdAt E n P) : M.mulVec x ∈ stdAt E n P :=
  mem_stdAt.2 fun i => by
    show IntAt P (∑ l, M i l * x l)
    exact intAt_sum _ fun l _ => (hM i l).mul (mem_stdAt.1 hx l)

theorem exists_glint_of_matrix {n : ℕ} (A : Matrix (Fin n) (Fin n) E) (hA : ∀ i l, IntAt P (A i l))
    (hd : IsUnit (redP P A.det)) : ∃ j : GLint E n P, ∀ x, j.1 x = A.mulVec x := by
  obtain ⟨hne, hinv⟩ := intAt_inv_of_isUnit (det_int hA).1 hd
  have hU : IsUnit A.det := isUnit_iff_ne_zero.2 hne
  let I : Invertible A := Matrix.invertibleOfIsUnitDet A hU
  have hB : ∀ i l, IntAt P (A⁻¹ i l) := by
    intro i l
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
    refine hinv.mul ?_
    rw [Matrix.adjugate_apply]
    refine (det_int fun a b => ?_).1
    rw [Matrix.updateRow_apply]
    split_ifs
    · rw [Pi.single_apply]
      split_ifs
      · exact intAt_one
      · exact intAt_zero
    · exact hA a b
  have hf : ∀ x, Matrix.toLinearEquiv' A I x = A.mulVec x := fun x => rfl
  have hf' : ∀ x, (Matrix.toLinearEquiv' A I).symm x = A⁻¹.mulVec x := fun x => by
    rw [← Matrix.invOf_eq_nonsing_inv]
    rfl
  refine ⟨⟨Matrix.toLinearEquiv' A I, fun x => ⟨fun h => ?_, fun h => ?_⟩⟩, hf⟩
  · have := mulVec_mem_stdAt hB h
    rwa [← hf', LinearEquiv.symm_apply_apply] at this
  · rw [hf]
    exact mulVec_mem_stdAt hA h

theorem inv_extI_mul_mem {N n : ℕ} (hN : N = n + 1) (c : ℕ) (g : GLint E N P) (j : GLint E n P)
    (hj : ∀ i l, j.1 (Pi.single l 1) i = g.1 (Pi.single (Br.iC hN l) 1) (Br.iC hN i))
    (hB : ∀ i : Fin n, IntAt P (((qOf P : E) ^ c)⁻¹ * g.1 (Pi.single (Br.iL hN) 1) (Br.iC hN i)))
    (hC : ∀ l : Fin n, IntAt P (((qOf P : E) ^ c)⁻¹ * g.1 (Pi.single (Br.iC hN l) 1) (Br.iL hN)))
    (hD : IntAt P (((qOf P : E) ^ c)⁻¹ * (g.1 (Pi.single (Br.iL hN) 1) (Br.iL hN) - 1))) :
    (extI hN P j)⁻¹ * g ∈ prinCong N P c := by
  subst hN
  rw [inv_mul_mem_prinCong]
  intro x hx
  have hxi := mem_stdAt.1 hx
  have eg : ∀ i, g.1 x i = ∑ l : Fin n, x l.castSucc * g.1 (Pi.single l.castSucc 1) i +
      x (Fin.last n) * g.1 (Pi.single (Fin.last n) 1) i := fun i => by
    have := apply_eq_sum (g.1 : Sp E (n + 1) →ₗ[E] Sp E (n + 1)) x i
    rw [Fin.sum_univ_castSucc] at this
    exact this
  refine mem_stdAt.2 fun k => ?_
  show IntAt P (((qOf P : E) ^ c)⁻¹ * (g.1 x k - (extI rfl P j).1 x k))
  rw [extI_val]
  refine Fin.lastCases ?_ (fun i => ?_) k
  · have e : sumE rfl j.1 1 x (Fin.last n) = x (Fin.last n) := by
      have := sumE_last (rfl : n + 1 = n + 1) j.1 1 x
      rw [Units.val_one, one_mul] at this
      exact this
    rw [e, eg]
    have e2 : ((qOf P : E) ^ c)⁻¹ * (∑ l : Fin n, x l.castSucc * g.1 (Pi.single l.castSucc 1) (Fin.last n) +
        x (Fin.last n) * g.1 (Pi.single (Fin.last n) 1) (Fin.last n) - x (Fin.last n)) =
        ∑ l : Fin n, x l.castSucc * (((qOf P : E) ^ c)⁻¹ * g.1 (Pi.single l.castSucc 1) (Fin.last n)) +
        x (Fin.last n) * (((qOf P : E) ^ c)⁻¹ * (g.1 (Pi.single (Fin.last n) 1) (Fin.last n) - 1)) := by
      rw [show ∑ l : Fin n, x l.castSucc * (((qOf P : E) ^ c)⁻¹ * g.1 (Pi.single l.castSucc 1) (Fin.last n)) =
          ((qOf P : E) ^ c)⁻¹ * ∑ l : Fin n, x l.castSucc * g.1 (Pi.single l.castSucc 1) (Fin.last n) by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by ring]
      ring
    rw [e2]
    exact IntAt.add (intAt_sum _ fun l _ => (hxi _).mul (hC l)) ((hxi _).mul hD)
  · have e : sumE rfl j.1 1 x i.castSucc = ∑ l : Fin n, x l.castSucc * g.1 (Pi.single l.castSucc 1) i.castSucc := by
      have h1 := congrFun (prH_sumE (rfl : n + 1 = n + 1) j.1 1 x) i
      rw [prH_apply] at h1
      have h2 := apply_eq_sum (j.1 : Sp E n →ₗ[E] Sp E n) (prH E rfl x) i
      rw [LinearEquiv.coe_coe] at h2
      rw [show i.castSucc = Br.iC (rfl : n + 1 = n + 1) i from rfl, h1, h2]
      exact Finset.sum_congr rfl fun l _ => by rw [prH_apply, hj]; rfl
    rw [e, eg, add_sub_cancel_left, mul_left_comm]
    exact (hxi _).mul (hB i)

theorem det_last {κ : Type} [CommRing κ] {n : ℕ} (R : Matrix (Fin (n + 1)) (Fin (n + 1)) κ)
    (h0 : ∀ l : Fin n, R (Fin.last n) l.castSucc = 0) (h1 : R (Fin.last n) (Fin.last n) = 1) :
    R.det = (R.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [Matrix.det_succ_row R (Fin.last n), Fin.sum_univ_castSucc]
  simp only [h0, mul_zero, zero_mul, Finset.sum_const_zero, zero_add, h1, mul_one, Fin.succAbove_last, Fin.val_last]
  rw [Even.neg_one_pow ⟨n, rfl⟩, one_mul]

theorem coarse_two {r b n : ℕ} (hn : n = r + b) (k : Fin n) : coarse r [b] k.1 = if k.1 < r then 0 else 1 := by
  split_ifs with h
  · exact coarse_of_lt h
  · rw [coarse_of_le (Nat.not_lt.1 h)]
    simp only [blkIdx]
    rw [if_pos (by have := k.2; omega)]

theorem exists_block_of_twisted_k1 : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) {N n : ℕ} (hN : N = n + 1) (r b c : ℕ), n = r + b → ∀ g : GLint E N P, g ∈ twK1H P N r (c + 1) → ∃ j : GLint E n P, redGL n P j ∈ HQ (𝓞 E ⧸ P.asIdeal) n r b ∧ (extI hN P j)⁻¹ * g ∈ prinCong N P (c + 1) := by
  intro E _ _ _ P N n hN r b c hn g hg
  subst hN
  obtain ⟨-, hT1, hT2⟩ := isKOneType_of_mem_kOne P g hg
  have eC : ∀ l : Fin n, Br.iC (rfl : n + 1 = n + 1) l = l.castSucc := fun l => rfl
  have eL : Br.iL (rfl : n + 1 = n + 1) = Fin.last n := rfl
  have hlast : (Fin.last n).1 + 1 = n + 1 := by simp
  have hC' : ∀ i : Fin n, ¬ (i.castSucc : Fin (n + 1)).1 + 1 = n + 1 := fun i h => by
    simp only [Fin.coe_castSucc] at h; omega
  have hB : ∀ i : Fin n, IntAt P (((qOf P : E) ^ (c + 1))⁻¹ * g.1 (Pi.single (Br.iL rfl) 1) (Br.iC rfl i)) :=
    fun i => hT1 _ _ (iff_of_false (hC' i) (not_not.2 hlast))
  have hC : ∀ l : Fin n, IntAt P (((qOf P : E) ^ (c + 1))⁻¹ * g.1 (Pi.single (Br.iC rfl l) 1) (Br.iL rfl)) :=
    fun l => hT1 _ _ (iff_of_true hlast (hC' l))
  have hD : IntAt P (((qOf P : E) ^ (c + 1))⁻¹ * (g.1 (Pi.single (Br.iL rfl) 1) (Br.iL rfl) - 1)) := hT2 _ hlast
  let A : Matrix (Fin n) (Fin n) E := Matrix.of fun i l => g.1 (Pi.single (Br.iC rfl l) 1) (Br.iC rfl i)
  have hAint : ∀ i l, IntAt P (A i l) := fun i l => glint_entry g _ _
  have hdet : IsUnit (redP P A.det) := by
    rw [redP_det A hAint]
    have hR := IsUnit.map Matrix.detMonoidHom (Units.isUnit (redGL (n + 1) P g))
    have e1 : A.map (redP P) = (redMat g).submatrix Fin.castSucc Fin.castSucc := by
      ext i l
      rfl
    rw [e1, ← det_last]
    · exact hR
    · intro l
      exact reduction_eq_zero_of_integral_absNorm_pow_inv_mul (hC l)
    · have h := reduction_eq_zero_of_integral_absNorm_pow_inv_mul hD
      rw [reduction_sub (glint_entry g _ _) intAt_one, reduction_one₂, sub_eq_zero] at h
      exact h
  obtain ⟨j, hj⟩ := exists_glint_of_matrix A hAint hdet
  have hj' : ∀ i l, j.1 (Pi.single l 1) i = g.1 (Pi.single (Br.iC rfl l) 1) (Br.iC rfl i) := fun i l => by
    rw [hj]
    simp [Matrix.mulVec_single_one, A]
  refine ⟨j, ?_, inv_extI_mul_mem rfl (c + 1) g j hj' hB hC hD⟩
  show redGL n P j ∈ btG n _ (coarse r [b])
  rw [mem_btG]
  intro i l hil
  rw [coarse_two hn, coarse_two hn] at hil
  have hl : l.1 < r := by
    by_contra h
    rw [if_neg h] at hil
    split_ifs at hil <;> omega
  have hi : r ≤ i.1 := by
    by_contra h
    rw [if_pos (Nat.lt_of_not_le h)] at hil
    omega
  rw [redGL_val]
  show redP P (j.1 (Pi.single l 1) i) = 0
  rw [hj']
  have hv : (Pi.single (Br.iC rfl l) 1 : Sp E (n + 1 + 0)) ∈ LocE.parL P (qOf P) r (n + 1) 0 :=
    GlobalTheory.LastSteps.mem_sclLat.2 fun k => by
      by_cases hk : k = Br.iC rfl l
      · subst hk
        have : ¬ (r ≤ (Br.iC (rfl : n + 1 = n + 1) l).1 ∧ (Br.iC (rfl : n + 1 = n + 1) l).1 < n + 1) := fun h => by
          have := h.1; simp [Br.iC] at this; omega
        simp only [if_neg this, zpow_zero, inv_one, one_mul, Pi.single_eq_same]
        exact intAt_one
      · simp only [Pi.single_apply, hk, if_false, mul_zero]
        exact intAt_zero
  have h1 := GlobalTheory.LastSteps.mem_sclLat.1 (((hg.1.2 _).2 hv)) (Br.iC rfl i)
  have h2 : r ≤ (Br.iC (rfl : n + 1 = n + 1) i).1 ∧ (Br.iC (rfl : n + 1 = n + 1) i).1 < n + 1 := by
    simp [Br.iC]; omega
  rw [if_pos h2, zpow_one] at h1
  apply redP_eq_zero_of_div
  rw [div_eq_inv_mul]
  exact h1

end GlobalTheory.BlockDecompositionK1
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical

namespace GlobalTheory.CplTwoInt

open GlobalTheory.GO.ChRoot (mem_stdAt' intAt_natCast intAt_one' intAt_zero' psi_root)

theorem intOff_prod {S : Finset ℕ} {ι : Type} (s : Finset ι) (f : ι → ℂ) (h : ∀ i ∈ s, IntOff S (f i)) :
    IntOff S (∏ i ∈ s, f i) :=
  Finset.prod_induction f (IntOff S) (fun _ _ ha hb => ha.mul hb) IntOff.one h

theorem sNum_pow {S : Finset ℕ} {a : ℕ} (h : SNum S a) (k : ℕ) : SNum S (a ^ k) :=
  ⟨pow_pos h.1 k, fun q hq hd => h.2 q hq (hq.dvd_of_dvd_pow hd)⟩

section Lin

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)}

theorem intAt_eval {n : ℕ} (η : Sp E n →ₗ[E] E) (c a : E) (y : Sp E n)
    (hη : ∀ i, IntAt P (c * η (Pi.single i 1))) (hy : a • y ∈ stdAt E n P) : IntAt P (a * c * η y) := by
  have hy' := mem_stdAt'.1 hy
  have e : η y = ∑ i, y i * η (Pi.single i 1) := by
    conv_lhs => rw [← Finset.univ_sum_single y]

    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show (Pi.single i (y i) : Sp E n) = y i • Pi.single i (1 : E) by
      ext j; by_cases h : j = i <;> simp [h, Pi.single_apply], map_smul, smul_eq_mul]
  rw [e, Finset.mul_sum]
  refine Finset.sum_induction _ (IntAt P) (fun _ _ ha hb => ha.add hb) intAt_zero' fun i _ => ?_
  have := (hy' i).mul (hη i)
  simp only [Pi.smul_apply, smul_eq_mul] at this
  convert this using 1
  ring

theorem smul_symm_mem {n : ℕ} {N : Submodule (𝓞 E) (Sp E n)} {f : Sp E n ≃ₗ[E] Sp E n}
    (hf : ∀ x, f x ∈ localization₂ P.asIdeal N ↔ x ∈ stdAt E n P) (a : E) {z : Sp E n} (hz : a • z ∈ localization₂ P.asIdeal N) :
    a • f.symm z ∈ stdAt E n P := by
  rw [← hf, map_smul, LinearEquiv.apply_symm_apply]
  exact hz

end Lin

section Yb

variable {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem repY_mem {n : ℕ} {N : Submodule (𝓞 X.E) (Sp X.E n)} {Yb : Set (Sp X.E n)} (hY : Yb ∈ ybSet sel mu cst N)
    (P : rowSG Pr sel mu) :
    ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 1 else cst.M)) • repY Yb ∈ localization₂ P.1.asIdeal N := by
  obtain ⟨y, hy, rfl⟩ := hY
  have hq : (qOf P.1 : X.E) ≠ 0 := by exact_mod_cast (GlobalTheory.GO.ChRoot.qOf_pos P.1).ne'
  have hs : ∀ (k : ℕ) v, v ∈ localization₂ P.1.asIdeal N → ((qOf P.1 : X.E) ^ k) • v ∈ localization₂ P.1.asIdeal N := by
    intro k v hv
    have := Submodule.smul_mem _ ((qOf P.1 : 𝓞 X.E) ^ k) hv
    rwa [← algebraMap_smul X.E, map_pow, map_natCast] at this
  have key : ∀ z, z - y ∈ locLat (rowSG Pr sel mu) N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ)) →
      ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 1 else cst.M)) • z ∈ localization₂ P.1.asIdeal N := by
    intro z hz
    rw [mem_locLat] at hy hz
    have h1 := hy P
    have h2 := hz P
    rw [show z = y + (z - y) by abel, smul_add]
    split_ifs at h1 h2 ⊢ with hP
    · refine add_mem ?_ ?_
      · simpa using h1
      · exact hs 1 _ (by simpa using h2)
    · refine add_mem ?_ ?_
      · simpa [zpow_neg] using h1
      · have e : ((qOf P.1 : X.E) ^ cst.M) • (z - y) =
            ((qOf P.1 : X.E) ^ (cst.M + cst.M)) • (((qOf P.1 : X.E) ^ (cst.M : ℤ))⁻¹ • (z - y)) := by
          rw [smul_smul, zpow_natCast, pow_add, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq), mul_one]
        rw [e]
        exact hs _ _ h2
  exact key _ (Classical.epsilon_spec (p := fun z => z - y ∈ locLat (rowSG Pr sel mu) N
    (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ))) ⟨y, by simp⟩)

end Yb

end GlobalTheory.CplTwoInt

namespace GlobalTheory.CplTwoInt

open GlobalTheory.GO.ChRoot (mem_stdAt' intAt_natCast intAt_one' intAt_zero' psi_root)

section Ft

variable {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem ftY_intOff (hc : cst.Ok) (P : rowSG Pr sel mu) (hG : P.1 ∈ Pr.vGs → cst.D P = 1)
    (hQ : P.1 ∉ Pr.vGs → 2 * cst.M ≤ cst.D P) (σ : X.K →+* ℂ) {B : Finset ℕ} (hB : SNum B (qOf P.1)) {n : ℕ}
    (η : Sp X.E n →ₗ[X.E] X.E) {y : Sp X.E n}
    (hy : ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 1 else cst.M)) • y ∈ stdAt X.E n P.1) :
    IntOff B (σ (ftY sel mu cst P η y)) := by
  have he : IntAt P.1 ((epsSg : ℤ) : X.E) := by simpa [epsSg] using IntAt.coe P.1 (-1 : 𝓞 X.E)
  have hpos : 0 < qOf P.1 ^ cst.D P := pow_pos (GlobalTheory.GO.ChRoot.qOf_pos P.1) _
  unfold ftY
  by_cases hP : P.1 ∈ Pr.vGs
  · rw [if_pos hP] at hy ⊢
    split_ifs with hη
    · refine IntOff.of_pow hpos ?_
      rw [← map_pow, psi_root hc P _ ?_, map_one]
      rw [hG hP, pow_one]
      have h1 := intAt_eval η 1 _ y (fun i => by simpa using hη i) hy
      convert he.mul h1 using 1
      ring
    · simpa using (IntOff.zero : IntOff B 0)
  · rw [if_neg hP] at hy ⊢
    split_ifs with hη
    · rw [map_mul, map_inv₀, map_pow, map_natCast]
      refine IntOff.mul ?_ (IntOff.of_pow hpos ?_)
      · simpa [Nat.cast_pow] using IntOff.inv_nat (sNum_pow hB (cst.M * n))
      · rw [← map_pow, psi_root hc P _ ?_, map_one]
        obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (hQ hP)
        have h1 := intAt_eval η _ _ y hη hy
        have hk' : IntAt P.1 ((qOf P.1 : X.E) ^ k) := by simpa using _root_.GlobalTheory.GO.ChRoot.intAt_natCast (P := P.1) (qOf P.1 ^ k)
        rw [hk]
        convert (he.mul hk').mul h1 using 1
        ring
    · simpa using (IntOff.zero : IntOff B 0)

end Ft

theorem xiCpl2_intOff (hPhi : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D)
      (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), ∀ u μ
      (P : HeightOneSpectrum (𝓞 t.X.E)) x,
      IntOff (t.O u μ).S (t.seam.σ₀ (PhiTop (R := D.R) t.Ch (t.tup μ) (t.cst μ).sharp t.m2 P x))) :
    ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), ∀ u μ p Yb d x, Yb ∈ ybSet t.sel (t.tup μ) (t.cst μ) p.deco.1.N → IntOff (t.O u μ).S (t.seam.σ₀ (XiCpl2 (R := D.R) (u := t.word u) t.Ch t.sel (t.tup μ) (t.cst μ) t.m2 p Yb d x)) := by
  intro D L hT Gi Gl K Y cX ex t u μ p Yb d x hY
  have hok := t.idx_ok μ
  unfold XiCpl2
  rw [map_mul, map_prod]
  refine IntOff.mul ?_ (intOff_prod _ _ fun P _ => ?_)
  · unfold phiT
    split_ifs
    · simpa using (IntOff.one : IntOff (t.O u μ).S 1)
    · simpa using (IntOff.zero : IntOff (t.O u μ).S 0)
  · rw [map_mul]
    refine IntOff.mul (hPhi D L hT Gi Gl K Y cX ex t u μ P.1 _) ?_
    exact ftY_intOff t.sel (t.tup μ) (t.cst μ) hok.cst_ok P (hok.depthG P) (hok.depthQ P) _
      (GlobalTheory.KerTie.sNum_qOf_rowSG D L hT Gi Gl K Y cX ex t u μ P) _
      (smul_symm_mem (GlobalTheory.ColPeriod.isFrames_frsF p P) _ (repY_mem t.sel (t.tup μ) (t.cst μ) hY P))

theorem xiCpl2_intOff_tied : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), ∀ u μ p Yb d x, Yb ∈ ybSet t.sel (t.tup μ) (t.cst μ) p.deco.1.N → IntOff (t.O u μ).S (t.seam.σ₀ (XiCpl2 (R := D.R) (u := t.word u) t.Ch t.sel (t.tup μ) (t.cst μ) t.m2 p Yb d x)) :=
  xiCpl2_intOff fun D L hT Gi Gl K Y cX ex t u μ P x => (GlobalTheory.T.chain_local_data_integral_off_levels D L hT Gi Gl K Y cX ex t u μ P).2 x

end GlobalTheory.CplTwoInt
end

section

open NumberField

open scoped IntermediateField

namespace GlobalTheory.CMSqrtNeg

theorem finrank_adjoin_sq {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] (c : E) (t : Ω)
    (ht : t ^ 2 = algebraMap E Ω c) (hn : t ∉ Set.range (algebraMap E Ω)) :
    IsIntegral E t ∧ Module.finrank E E⟮t⟯ = 2 := by
  have hm : (Polynomial.X ^ 2 - Polynomial.C c).Monic := Polynomial.monic_X_pow_sub_C c two_ne_zero
  have h0 : Polynomial.aeval t (Polynomial.X ^ 2 - Polynomial.C c) = 0 := by simp [ht]
  have hi : IsIntegral E t := ⟨_, hm, by simpa [Polynomial.aeval_def] using h0⟩
  refine ⟨hi, ?_⟩
  rw [IntermediateField.adjoin.finrank hi]
  have h1 : (minpoly E t).natDegree ≤ 2 := by
    have := Polynomial.natDegree_le_of_dvd (minpoly.dvd E t h0) hm.ne_zero
    rwa [Polynomial.natDegree_X_pow_sub_C _] at this
  have h2 : 2 ≤ (minpoly E t).natDegree := (minpoly.two_le_natDegree_iff hi).2 (by simpa using hn)
  omega

theorem exists_qcm_adjoin_sqrt_neg : ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (p : ℕ), 0 < p → ∀ δ : Ω, δ ^ 2 = -(p : Ω) → δ ∉ Set.range (algebraMap E Ω) →
    ∃ Q : GlobalTheory.RealGal.QCM E Ω, Q.K = IntermediateField.adjoin E {δ} := by
  intro E Ω _ _ _ _ _ _ p hp δ hδ hδn
  have hδ' : δ ^ 2 = algebraMap E Ω (-(p : E)) := by simp [hδ]
  obtain ⟨hint, htwo⟩ := finrank_adjoin_sq (-(p : E)) δ hδ' hδn
  haveI : FiniteDimensional E E⟮δ⟯ := IntermediateField.adjoin.finiteDimensional hint
  haveI nf : NumberField E⟮δ⟯ := NumberField.of_module_finite E _
  obtain ⟨d, s, hs, hsn, hneg⟩ := GlobalTheory.CMGen.exists_sqrt_totallyNegative E
  have hs0 : s ≠ 0 := fun h => hsn (h ▸ zero_mem _)
  let t : E⟮δ⟯ := ⟨δ * algebraMap E Ω s,
    mul_mem (IntermediateField.subset_adjoin E {δ} rfl) (IntermediateField.algebraMap_mem _ s)⟩
  let d' : maximalRealSubfield E := -(p : maximalRealSubfield E) * (d : maximalRealSubfield E)
  have ht : t ^ 2 = algebraMap E E⟮δ⟯ (algebraMap (maximalRealSubfield E) E d') := by
    apply Subtype.ext
    show (δ * algebraMap E Ω s) ^ 2 = algebraMap E Ω (algebraMap (maximalRealSubfield E) E d')
    rw [mul_pow, hδ, ← map_pow, hs]
    simp [d']
  have htn : t ∉ Set.range (algebraMap E E⟮δ⟯) := by
    rintro ⟨e, he⟩
    apply hδn
    refine ⟨e * s⁻¹, ?_⟩
    have h1 : algebraMap E Ω e = δ * algebraMap E Ω s := congrArg Subtype.val he
    have h2 : algebraMap E Ω s ≠ 0 := (map_ne_zero _).2 hs0
    rw [map_mul, h1, map_inv₀, mul_assoc, mul_inv_cancel₀ h2, mul_one]
  have hpos : ∀ φ : maximalRealSubfield E →+* ℝ, 0 < φ d' := fun φ => by
    have := hneg φ
    have hp' : (0 : ℝ) < p := by exact_mod_cast hp
    simp only [d', map_mul, map_neg, map_natCast]
    nlinarith
  have hcm := (GlobalTheory.isCMField_of_sq_eq_totallyPositive E E⟮δ⟯ htwo d' t ht htn hpos).1
  exact ⟨⟨E⟮δ⟯, nf, hcm, htwo⟩, rfl⟩

end GlobalTheory.CMSqrtNeg
end
