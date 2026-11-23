module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle118
import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsSupportedIdele
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle121
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle276
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemAdelicLatticeIffLocalSelfDualCompletion
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiMapsAndOmegaLaw
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle097
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle119
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemZmuOfPowPred
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass

@[expose] public section

section

namespace GlobalTheory.ColPeriod

open Formalism.L2.Col Formalism.BasicNotions Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint (WtCompat)

theorem sub_half_rank_int (R : Ranks) (z : ℤ) (j : ℕ) : ∃ a : ℤ, (z : ℚ) - (R.N j : ℚ) / 2 = a := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨c, hc⟩ := R.t_odd
  unfold Ranks.N
  rw [ha, hc]
  exact ⟨z - a - (j : ℤ) * (c + 1), by push_cast; ring⟩

theorem chainWeights : ChainWeights := by
  intro X Pr R W u j hj
  have hs : ∀ τ : X.Tau, ∃ a : ℤ, sExp R ((W.hc u τ).e ⟨j, hj⟩) (j + 1) = a := by
    intro τ
    obtain ⟨z, hz⟩ := (W.hc u τ).e_int ⟨j, hj⟩
    rw [hz]
    exact sub_half_rank_int R z _
  have hs' : ∀ τ : X.Tau, ∃ a : ℤ, sExp' R ((W.hc u τ).e ⟨j, hj⟩) (j + 1) = a := by
    intro τ
    obtain ⟨z, hz⟩ := (W.hc u τ).e_int ⟨j, hj⟩
    rw [hz]
    exact sub_half_rank_int R z _
  choose s hs using hs
  choose s' hs' using hs'
  have hlt := N_lt_succ R j
  have h1 : ∀ τ (i : Fin (R.N j)),
      (W.lamTrue u (j + 1) τ).w (Fin.castLE hlt.le i) + s τ = (W.lamTrue u j τ).w i + s' τ := by
    intro τ i
    have h := W.lamTrue_old u hj τ (Fin.castLE hlt.le i) i.2
    rw [hs, hs'] at h
    have h' : (((W.lamTrue u (j + 1) τ).w (Fin.castLE hlt.le i) + s τ : ℤ) : ℚ) =
        (((W.lamTrue u j τ).w i + s' τ : ℤ) : ℚ) := by
      push_cast
      rw [h]
      simp
    exact_mod_cast h'
  have h2 : ∀ τ (i : Fin (R.N (j + 1))), R.N j ≤ (i : ℕ) → (W.lamTrue u (j + 1) τ).w i = -s τ := by
    intro τ i hi
    have h := W.lamTrue_new u hj τ i (by omega)
    rw [hs] at h
    exact_mod_cast h
  have h3 : ∀ (τ : X.Tau) (a : Fin (R.N j)), (W.lamTrue u j τ).w a + s' τ = (W.nuW u (j + 1) τ).w a := by
    intro τ a
    have h := W.nuW_eq_true u hj τ a
    rw [hs'] at h
    exact_mod_cast h.symm
  refine ⟨s, s', ⟨h1, h2, fun τ => ?_⟩, h3⟩
  have hpos : 0 < R.N j := R.N_pos j
  have e1 : (W.lamTrue u j τ).detShift = (W.lamTrue u j τ).w ⟨R.N j - 1, by omega⟩ := by
    unfold DomWeight.detShift
    rw [dif_pos hpos]
  have e2 : (W.nuW u (j + 1) τ).detShift = (W.nuW u (j + 1) τ).w (⟨R.N j - 1, by omega⟩ : Fin (R.N j)) := by
    unfold DomWeight.detShift
    exact dif_pos hpos
  have hge : 0 ≤ (W.lamTrue u j τ).w ⟨R.N j - 1, by omega⟩ + s' τ := by
    rw [← h1]
    have ha := (W.lamTrue u (j + 1) τ).anti
      (show Fin.castLE hlt.le (⟨R.N j - 1, by omega⟩ : Fin (R.N j)) ≤ ⟨R.N j, hlt⟩ from by
        rw [Fin.le_def]; simp)
    have hb := h2 τ ⟨R.N j, hlt⟩ le_rfl
    omega
  unfold nuLast
  rw [e1, e2, ← h3, Int.toNat_of_nonneg hge]

end GlobalTheory.ColPeriod
end

section

open NumberField IsDedekindDomain Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV
open GlobalTheory.GO.ChRoot GlobalTheory.TopStep

namespace GlobalTheory.ColPeriod.EntQ

section Val

variable {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))

theorem val_of_pow {a : K} {k : ℕ} (hk : 0 < k) (h : w.valuation K (a ^ k) = 1) : w.valuation K a = 1 := by
  rw [map_pow] at h
  exact (pow_eq_one_iff_of_nonneg zero_le' hk.ne').1 h

theorem val_nat {q : ℕ} (hq : (q : 𝓞 K) ∉ w.asIdeal) : w.valuation K (q : K) = 1 := by
  have := (w.valuation_eq_one_iff_notMem (K := K) (r := (q : 𝓞 K))).2 hq
  simpa using this

variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)}

theorem val_unitV (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (a : E) :
    w.valuation K (LocE.unitV χ a) ≤ 1 ∧ w.valuation K (LocE.unitV χ a)⁻¹ ≤ 1 := by
  by_cases h : LocE.unitV χ a = 0
  · simp [h]
  · obtain ⟨k, hk, h1⟩ := unitV_root χ a h
    have := val_of_pow w hk (a := LocE.unitV χ a) (by rw [h1, map_one])
    simp [this]

theorem val_locChar (q : ℕ) {cq : K} (hc : w.valuation K cq = 1) (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (a : E) :
    w.valuation K (LocE.locChar q cq χ a) ≤ 1 ∧ w.valuation K (LocE.locChar q cq χ a)⁻¹ ≤ 1 := by
  unfold LocE.locChar
  rw [mul_inv, map_mul, map_mul, map_inv₀ _ (cq ^ _), map_zpow₀, hc, one_zpow, inv_one, one_mul, one_mul]
  exact val_unitV w χ _

theorem val_om {a b : ℕ} {mu : E → K} (hmu : ∀ t, w.valuation K (mu t) ≤ 1 ∧ w.valuation K (mu t)⁻¹ ≤ 1) (v : E → ℤ)
    {sq : K} (hsq : w.valuation K sq = 1) (g₀ : (Fin a → E) ≃ₗ[E] (Fin a → E)) (h : (Fin b → E) ≃ₗ[E] (Fin b → E))
    {Φ : Loc.SF E K a b} (hΦ : ∀ x, w.valuation K (Φ x) ≤ 1) (x) : w.valuation K (Loc.om mu v sq g₀ h Φ x) ≤ 1 := by
  unfold Loc.om
  simp only [map_mul, map_zpow₀, hsq, one_zpow, mul_one]
  exact mul_le_one' (mul_le_one' (hmu _).1 (hmu _).2) (hΦ _)

theorem val_PhiQ (q : ℕ) (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (k₀ r c' n' c n : ℕ) (x) :
    w.valuation K (LocE.PhiQ q χ k₀ r c' n' c n x) ≤ 1 := by
  unfold LocE.PhiQ
  split_ifs
  · exact (val_unitV w χ _).1
  · simp

end Val

section Supp

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}

theorem exists_fIdx {k₀ c n l : ℕ} (hk : k₀ ≤ n) (hl : l < n + c) : ∃ s, s < n + c ∧ LocE.fIdx k₀ c n s = l := by
  refine ⟨LocE.fPos k₀ c n l, ?_, ?_⟩
  · unfold LocE.fPos
    split_ifs <;> omega
  · unfold LocE.fIdx LocE.fPos
    split_ifs <;> omega

theorem int_of_PhiQ {q : ℕ} {χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ} {k₀ r c' n' c n : ℕ} (hk' : k₀ ≤ n') (hk : k₀ ≤ n)
    {x : HomE E (n' + c') (n + c)} (hx : LocE.PhiQ q χ k₀ r c' n' c n x ≠ 0) {v : Sp E (n' + c')}
    (hv : v ∈ stdAt E (n' + c') P) : x v ∈ stdAt E (n + c) P := by
  unfold LocE.PhiQ at hx
  split_ifs at hx with h
  · rw [mem_stdAt] at hv ⊢
    intro i
    rw [apply_eq_sum]
    refine intAt_sum _ fun j _ => (hv j).mul ?_
    obtain ⟨p, hp, e⟩ := exists_fIdx hk i.2
    obtain ⟨p', hp', e'⟩ := exists_fIdx hk' j.2
    have h1 := h.1 p p' hp hp'
    have h2 : Loc.eN E (n' + c') j.1 = Pi.single j 1 := by
      funext l
      simp [Loc.eN, Pi.single_apply, Fin.ext_iff]
    simpa [LocE.entB, e, e', LocE.scE, Loc.atN, h2] using h1
  · exact absurd rfl hx

theorem intAt_chArg {n' c' n c : ℕ} (a : E) (x : HomE E (n' + c') (n + c))
    (h : ∀ v ∈ stdAt E (n' + c') P, a • x v ∈ stdAt E (n + c) P) : IntAt P (a * Loc.chArg x) := by
  unfold Loc.chArg
  rw [Finset.mul_sum]
  refine intAt_sum _ fun i _ => ?_
  unfold Loc.atN
  split_ifs with hi
  · exact mem_stdAt.1 (h _ eN_mem) ⟨n + i, hi⟩
  · simpa using intAt_zero

theorem int_of_homAt {a b : ℕ} {z : HomE E a b} (hz : z ∈ homAt {P} (stdLat E a) (stdLat E b)) (B : ℕ) (s : Fin a) (l : Fin b) :
    IntAt P (((qOf P : E) ^ B)⁻¹ * (((qOf P : E) ^ B) • z) (Pi.single s 1) l) := by
  have h := mem_stdAt.1 (hz P (Finset.mem_singleton_self P) _ (single_mem_stdAt s)) l
  have hq := qOf_ne_zero (P := P)
  rwa [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, inv_mul_cancel_left₀ (pow_ne_zero _ hq)]

end Supp

theorem k_le_N (R : Ranks) (j : ℕ) : R.k ≤ R.N j := by
  unfold Ranks.N
  omega

theorem entryAtQ (hV : VolumeAtQ) : EntryAtQ := by
  intro X Pr R Ch sel S mu cst L G m2 hL P w hP hdeg hq hmu
  have hm := hL.hm
  have hqv := val_nat w hq
  have hsq : w.valuation X.K (cst.sq P) = 1 := val_of_pow w two_pos (by rw [hL.cst_ok.sq_sq, hqv])
  have hom : ∀ i, i < R.m → ∀ hal h x, w.valuation X.K (omPhi Ch sel mu cst i P hal h x) ≤ 1 := by
    intro i hi hal h x
    refine val_om w (fun t => val_locChar w _ (hmu i hi) _ t) _ hsq _ _ (fun y => ?_) x
    rw [PhiAt, if_neg hP]
    exact val_PhiQ w _ _ _ _ _ _ _ _ y
  refine ⟨fun i hi al be => ⟨fun x => ?_, fun x z hz => hL.xiInv i hi al be P x _ (int_of_homAt hz _)⟩,
    fun al y => ⟨fun x => hom m2 (by omega) _ _ _, fun x z hz => hL.psiInvX al P x _ y (int_of_homAt hz _)⟩⟩
  unfold XiAt E1at Loc.E1
  rw [map_mul, map_mul, map_pow, map_inv₀ _ (_ ^ cst.B), map_pow, hqv, one_pow, inv_one, one_pow, one_mul]
  refine mul_le_one' (hV X Pr R _ _ _ _ w hP hdeg hq) (Valuation.map_sum_le _ fun t _ => ?_)
  generalize Loc.xx1 x t = y
  by_cases h0 : omPhi Ch sel mu cst i P (L.h i al P) (L.h (i + 1) be P) y = 0
  · simp [h0]
  rw [map_mul]
  refine mul_le_one' (hom i (by omega) _ _ _) (le_of_eq ?_)
  have h1 := right_ne_zero_of_mul h0
  rw [PhiAt, if_neg hP] at h1
  have hb := hL.boundQ i al P hP
  have hb' := hL.boundQ (i + 1) be P hP
  have hD := hL.depthQ' P hP
  simp only [lamYat, hP, if_false, mem_lamY_zero] at hb hb'
  have hint : IntAt P.1 ((qOf P.1 : X.E) ^ (i + 1) * Loc.chArg y) := by
    refine intAt_chArg _ y fun v hv => ?_
    have h2 := (hb' _ (int_of_PhiQ (k_le_N R _) (k_le_N R _) h1 (hb v hv).1)).2
    have h3 : (L.h i al P) ((L.h i al P)⁻¹ v) = v := LinearEquiv.apply_symm_apply _ v
    simpa [h3] using h2
  have hint' : IntAt P.1 ((qOf P.1 : X.E) ^ cst.D P * -Loc.chArg y) := by
    obtain ⟨d, hd⟩ : ∃ d, cst.D P = d + (i + 1) := ⟨cst.D P - (i + 1), by omega⟩
    rw [hd, pow_add, mul_neg, mul_assoc]
    exact intAt_neg ((intAt_pow (intAt_nat _) _).mul hint)
  exact val_of_pow w (pow_pos (qOf_pos _) _) (by rw [psi_root hL.cst_ok P _ hint', map_one])

end GlobalTheory.ColPeriod.EntQ
end

section

open NumberField IsDedekindDomain Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.ColPeriod

theorem valuation_finOrder_apply {G K : Type} [Group G] [Field K] [NumberField K] (ξ : G →* Kˣ) (hξ : IsOfFinOrder ξ)
    (w : HeightOneSpectrum (𝓞 K)) (y : G) : w.valuation K ((ξ y : Kˣ) : K) = 1 := by
  obtain ⟨n, hn, h⟩ := isOfFinOrder_iff_pow_eq_one.1 hξ
  have h1 : (ξ y) ^ n = 1 := by
    have := congrArg (fun φ : G →* Kˣ => φ y) h
    simpa using this
  have h2 : (w.valuation K ((ξ y : Kˣ) : K)) ^ n = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, map_one]
  exact (pow_eq_one_iff_of_nonneg zero_le hn.ne').1 h2

theorem twistUnit : TwistUnit := by
  intro F E K _ _ _ _ _ _ _ S mu P w
  have hfin : IsOfFinOrder (mu : Chr F E K) := mu.2.1.1.1.2
  let v : HeightOneSpectrum (𝓞 F) := P.under (𝓞 F)
  have hv : P.asIdeal.under (𝓞 F) = v.asIdeal := rfl
  constructor
  · unfold unifVal
    split_ifs with h
    · obtain ⟨b, hb, hb2⟩ : ∃ b ∈ P.asIdeal, b ∉ P.asIdeal ^ 2 := by
        have := Ideal.exists_mem_pow_notMem_pow_succ P.asIdeal P.ne_bot P.isPrime.ne_top 1
        simpa using this
      obtain ⟨y, y₀, h1, h2, h3, h4⟩ := GlobalTheory.SuppIdele.exists_supported_idele F E P v b hv
      rw [← h.choose_spec v hv y y₀ b h1 hb hb2 h2 h3 h4]
      exact valuation_finOrder_apply _ hfin w y
    · simp
  · unfold qValC
    split_ifs with h
    · obtain ⟨y, y₀, h1, h2, h3, h4⟩ :=
        GlobalTheory.SuppIdele.exists_supported_idele F E P v ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) hv
      rw [← h.choose_spec v hv y y₀ h1 h2 h3 h4]
      exact valuation_finOrder_apply _ hfin w y
    · simp

end GlobalTheory.ColPeriod
end
end

section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField GlobalTheory.PlaceComp
open scoped TensorProduct Matrix

namespace GlobalTheory.SuppLocal

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem adele_ext {z z' : AF F ⊗[F] E} (h1 : infP F E z = infP F E z')
    (h2 : ∀ w, evF E w (finP F E z) = evF E w (finP F E z')) : z = z' := by
  have h3 : finP F E z = finP F E z' := evF_ext h2
  let b := Module.Basis.ofVectorSpace F E
  refine (Algebra.TensorProduct.basis (AF F) b).repr.injective (Finsupp.ext fun k => Prod.ext ?_ ?_)
  · have a1 := GlobalTheory.LatticeLocalGlobal.repr_map (fstA F) b z k
    have a2 := GlobalTheory.LatticeLocalGlobal.repr_map (fstA F) b z' k
    exact a1.symm.trans ((congrArg (fun x => (Algebra.TensorProduct.basis (Ainf F) b).repr x k) h1).trans a2)
  · have a1 := GlobalTheory.LatticeLocalGlobal.repr_map (sndA F) b z k
    have a2 := GlobalTheory.LatticeLocalGlobal.repr_map (sndA F) b z' k
    exact a1.symm.trans ((congrArg (fun x => (Algebra.TensorProduct.basis (Af F) b).repr x k) h3).trans a2)

theorem idem_mul_iff {v : HeightOneSpectrum (𝓞 F)} {e : AF F ⊗[F] E} (he : IsIdemOf E v e) (x : AF F ⊗[F] E) :
    e * x = x ↔ infP F E x = 0 ∧ ∀ w, w ≠ v → evF E w (finP F E x) = 0 := by
  obtain ⟨e1, e2, e3⟩ := he
  constructor
  · intro h
    refine ⟨?_, fun w hw => ?_⟩
    · rw [← h, map_mul, e1, zero_mul]
    · rw [← h, map_mul, map_mul, e3 w hw, zero_mul]
  · rintro ⟨h1, h2⟩
    refine adele_ext ?_ fun w => ?_
    · rw [map_mul, h1, mul_zero]
    · rw [map_mul, map_mul]
      by_cases hw : w = v
      · subst hw
        rw [e2, one_mul]
      · rw [h2 w hw, mul_zero]

theorem bc_eq_one_iff {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (φ : A →+* B) (g : GL (Fin n) A) :
    Formalism.UG.bc φ g = 1 ↔ ∀ i j, φ ((g.1 - 1) i j) = 0 := by
  rw [Units.ext_iff, ← Matrix.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  show φ (g.1 i j) = (1 : Matrix (Fin n) (Fin n) B) i j ↔ _
  rw [Matrix.sub_apply, map_sub, sub_eq_zero, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

variable [NumberField E] [StarRing E] (hc : CMData F E) (V : HSpace E)

theorem supp_iff {v : HeightOneSpectrum (𝓞 F)} {e : AF F ⊗[F] E} (he : IsIdemOf E v e)
    (g : HA (AF F) hc.sig V.gram) :
    Supp hc V e g ↔ IsFin hc V g ∧ ∀ w, w ≠ v → locMat hc V w g = 1 := by
  have h1 : IsFin hc V g ↔ ∀ i j, infP F E (((HA.mat (AF F) hc.sig V.gram g).1 - 1) i j) = 0 :=
    bc_eq_one_iff _ _
  have h2 : ∀ w, locMat hc V w g = 1 ↔
      ∀ i j, evF E w (finP F E (((HA.mat (AF F) hc.sig V.gram g).1 - 1) i j)) = 0 :=
    fun w => bc_eq_one_iff ((evF E w).comp (finP F E)) (HA.mat (AF F) hc.sig V.gram g)
  rw [h1]
  simp only [h2, Supp, idem_mul_iff he]
  exact ⟨fun h => ⟨fun i j => (h i j).1, fun w hw i j => (h i j).2 w hw⟩,
    fun h i j => ⟨h.1 i j, fun w hw => h.2 w hw i j⟩⟩

theorem supp_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : CMData F E) (V : HSpace E) (v : HeightOneSpectrum (𝓞 F)) (e : AF F ⊗[F] E), IsIdemOf E v e → (∀ g, Supp hc V e g ↔ IsFin hc V g ∧ ∀ w, w ≠ v → locMat hc V w g = 1) ∧ (∀ g g', Supp hc V e g → Supp hc V e g' → locMat hc V v g = locMat hc V v g' → g = g') ∧ ∀ u ∈ HR (Fv F v) hc.sig V.gram, ∃ g, Supp hc V e g ∧ locMat hc V v g = u := by
  classical
  intro F E _ _ _ _ _ _ hc V v e he
  refine ⟨supp_iff hc V he, fun g g' hg hg' h => ?_, fun u hu => ?_⟩
  · obtain ⟨a1, a2⟩ := (supp_iff hc V he g).1 hg
    obtain ⟨b1, b2⟩ := (supp_iff hc V he g').1 hg'
    have hw : ∀ w, locMat hc V w g = locMat hc V w g' := fun w => by
      by_cases hw : w = v
      · exact hw ▸ h
      · rw [a2 w hw, b2 w hw]
    have hi := Eq.trans a1 (Eq.symm b1)
    refine Subtype.ext (Units.ext (Matrix.ext fun i j => adele_ext ?_ fun w => ?_))
    · exact congrArg (fun x => x.1 i j) hi
    · exact congrArg (fun x => x.1 i j) (hw w)
  · let u' : HA (Fv F v) hc.sig V.gram := ⟨u, hu⟩
    obtain ⟨k, hk⟩ := GlobalTheory.LocalUnitaryGlue.exists_of_finite hc.sig V.gram
      (Pi.mulSingle (M := fun w : HeightOneSpectrum (𝓞 F) => HA (Fv F w) hc.sig V.gram) v u')
      ((Set.finite_singleton v).subset fun w hw => by
        by_contra hne
        exact hw (Pi.mulSingle_eq_of_ne
          (M := fun w : HeightOneSpectrum (𝓞 F) => HA (Fv F w) hc.sig V.gram) (i := v) (i' := w) hne u'))
    have hl : ∀ w, locMat hc V w (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.ofFin hc V k) = HA.mat _ _ _
        (Pi.mulSingle (M := fun w : HeightOneSpectrum (𝓞 F) => HA (Fv F w) hc.sig V.gram) v u' w) := fun w => by
      rw [← hk w]
      exact congrArg (fun x => HA.mat _ _ _ (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.projLoc hc V w x))
        (GlobalTheory.AutFunCompare.projFin_ofFin hc V k)
    refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.ofFin hc V k, (supp_iff hc V he _).2 ⟨?_, fun w hw => ?_⟩, ?_⟩
    · exact congrArg (HA.mat _ _ _) (GlobalTheory.AutFunCompare.projInf_ofFin hc V k)
    · rw [hl, Pi.mulSingle_eq_of_ne hw]; rfl
    · rw [hl, Pi.mulSingle_eq_same]; rfl

end GlobalTheory.SuppLocal
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.TopStep

namespace GlobalTheory.TopLaw

section Gen

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)} {n r b : ℕ}

theorem parL_map_of_red (hq : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (j : GLint E n P)
    (h : redGL n P j ∈ HQ (𝓞 E ⧸ P.asIdeal) n r b) {v : Sp E n} (hv : v ∈ LocE.parL P (qOf P) r n 0) :
    j.1 v ∈ LocE.parL P (qOf P) r n 0 := by
  have hq0 := qOf_ne_zero (P := P)
  have hv' : ∀ l : Fin n, IntAt P (((qOf P : E) ^ (if r ≤ l.1 ∧ l.1 < n then (1 : ℤ) else 0))⁻¹ * v l) :=
    GlobalTheory.LastSteps.mem_sclLat.1 hv
  have hv0 : ∀ l : Fin n, IntAt P (v l) := fun l => by
    have h1 := hv' l
    split_ifs at h1
    · have h2 := (intAt_nat (P := P) (qOf P)).mul h1
      rwa [zpow_one, mul_inv_cancel_left₀ hq0] at h2
    · simpa using h1
  refine GlobalTheory.LastSteps.mem_sclLat.2 fun (l : Fin n) => ?_
  show IntAt P (((qOf P : E) ^ (if r ≤ l.1 ∧ l.1 < n then (1 : ℤ) else 0))⁻¹ * j.1 v l)
  split_ifs with hl
  · have e := apply_eq_sum (j.1 : Sp E n →ₗ[E] Sp E n) v l
    rw [LinearEquiv.coe_coe] at e
    rw [e, Finset.mul_sum, zpow_one]
    refine intAt_sum _ fun i _ => ?_
    by_cases hi : r ≤ i.1
    · have h1 := hv' i
      rw [if_pos ⟨hi, i.2⟩, zpow_one] at h1
      rw [← mul_assoc]
      exact h1.mul (glint_entry j l i)
    · have h0 : redP P (j.1 (Pi.single i 1) l) = 0 :=
        mem_btG.1 h l i (by rw [coarse_of_lt (Nat.not_le.1 hi), coarse_of_le hl.1]; omega)
      have h1 := (hv0 i).mul (intAt_div_of_redP hq (glint_entry j l i) h0)
      convert h1 using 1
      ring
  · rw [zpow_zero, inv_one, one_mul]
    exact mem_stdAt.1 (glint_mem j (mem_stdAt.2 hv0)) l

theorem mem_JQ_of_red (hq : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (j : GLint E n P)
    (h : redGL n P j ∈ HQ (𝓞 E ⧸ P.asIdeal) n r b) : j.1 ∈ LocE.JQ P (qOf P) r n 0 := by
  refine ⟨j.2, fun v => ⟨fun hv => ?_, parL_map_of_red hq j h⟩⟩
  have h1 := parL_map_of_red hq j⁻¹ (by rw [map_inv]; exact inv_mem h) hv
  have e : (j⁻¹).1 (j.1 v) = v := LinearEquiv.symm_apply_apply j.1 v
  exact e ▸ h1

theorem lamQB_eq_red (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (hn : n = r + b) (j : GLint E n P)
    (h : redGL n P j ∈ HQ (𝓞 E ⧸ P.asIdeal) n r b) :
    LocE.lamQB ξ r n j.1.toLinearMap = (((lamQ ξ n r b ⟨_, h⟩)⁻¹ : Kˣ) : K) := by
  have hA : GlobalTheory.DatumLaw.IntM P n n fun p p' => Loc.atN (j.1.toLinearMap (Loc.eN E n p')) p := fun p p' hp hp' => by
    show IntAt P (Loc.atN _ _)
    rw [GlobalTheory.LastSteps.eN_eq hp', Loc.atN, dite_eq_left hp]
    exact glint_entry j _ _
  have h1 := blkDet_eq_dB (coarse r [b]) 1 r (n - r) (by omega) (fun i hi => by
    by_cases hr : i < r
    · rw [coarse_of_lt hr]; omega
    · rw [coarse_of_le (Nat.not_lt.1 hr), blkIdx, if_pos (by omega)]; omega) ⟨_, h⟩
    (GlobalTheory.DatumLaw.red P fun p p' => Loc.atN (j.1.toLinearMap (Loc.eN E n p')) p) (fun i l => by
      show redP P (Loc.atN _ _) = _
      rw [GlobalTheory.LastSteps.eN_eq l.2, Loc.atN, dite_eq_left i.2]
      rfl)
  rw [← GlobalTheory.DatumLaw.redP_dB hA (by omega) (by omega)] at h1
  rw [lamQ_apply, Units.val_inv_eq_inv_val]
  show (GlobalTheory.DatumLaw.ext0 ξ (redP P (GlobalTheory.DatumLaw.dB (fun p p' => Loc.atN (j.1.toLinearMap (Loc.eN E n p')) p) r (n - r))))⁻¹ = _
  rw [← h1, GlobalTheory.DatumLaw.ext0, dite_eq_left (Units.isUnit _), IsUnit.unit_of_val_units]

end Gen

theorem phiTop_target_twist : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (m2 : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), R.m = m2 + 2 → ((qOf P : ℕ) : 𝓞 X.E) ∉ P.asIdeal ^ 2 → P ∉ Pr.vGs → ∀ (sharp : Bool) (Q : Finset (HeightOneSpectrum (𝓞 X.E))) (hQ : P ∈ Q) (j : GLint X.E (R.N R.m - 1) P) (h : redGL _ P j ∈ (rowTyQ R (mu : Chr X.F X.E X.K) Q ⟨P, hQ⟩).H) (x : HomE X.E (R.N (m2 + 1) + cOf R (m2 + 1)) (R.N R.m - 1)), PhiTop Ch mu sharp m2 P (j.1.toLinearMap ∘ₗ x) * LocE.unitV (resChar (mu : Chr X.F X.E X.K) P)⁻¹ ((LinearEquiv.det j.1 : X.Eˣ) : X.E) = (((rowTyQ R (mu : Chr X.F X.E X.K) Q ⟨P, hQ⟩).lam ⟨_, h⟩ : X.Kˣ) : X.K) * PhiTop Ch mu sharp m2 P x := by
  intro X Pr R Ch S mu m2 P hm hq hP sharp Q hQ j h x
  obtain ⟨a1, a2, a3, -⟩ := GlobalTheory.DatumLaw.ranks R (j := m2 + 1) (by omega)
  unfold PhiTop
  rw [if_neg hP]
  have h1 := GlobalTheory.DatumLaw.phiQ_target (resChar (mu : Chr X.F X.E X.K) P) (k₀ := R.k) (r := R.r) (c' := cOf R (m2 + 1))
    (n' := R.N (m2 + 1)) (c := 0) (n := R.N R.m - 1) (kj := R.r) (by omega) (r_le_X' R) rfl (by omega)
    (mem_JQ_of_red hq j h) x
  exact h1.trans (congrArg (· * _) (lamQB_eq_red _ (rank_X'_eq R) j h))

end GlobalTheory.TopLaw
end
