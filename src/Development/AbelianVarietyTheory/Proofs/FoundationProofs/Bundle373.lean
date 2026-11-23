module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle020
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle021
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle369
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousMatQApply
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle341
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle346
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle360
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle364
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle357
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle366
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle188
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle367
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle368
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrdinarySelmerModPrimePowInjectsResidualSelmer
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle018
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle365
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries GlobalTheory.KZ.Cmp

namespace GlobalTheory.KZ.Cmp

theorem tval_eq_sum_pow_of_integral : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (F : PowerSeries (Qbar l)) (N : ℕ), (∀ n, F.coeff n ∈ c.O) → ∃ a : ℕ → Qbar l, (∀ j, a j ∈ c.O) ∧ ∀ z : Qbar l, tval F N z = ∑ j ∈ Finset.range N, a j * z ^ j := by
  intro l _ c F N hF
  let Q : Polynomial c.O := ∑ n ∈ Finset.range N, Polynomial.C (⟨F.coeff n, hF n⟩ : c.O) * (Polynomial.X - Polynomial.C 1) ^ n
  refine ⟨fun j => ((Q.coeff j : c.O) : Qbar l), fun j => (Q.coeff j).2, fun z => ?_⟩
  have hdeg : Q.natDegree < N ∨ N = 0 := by
    rcases Nat.eq_zero_or_pos N with h | h
    · exact Or.inr h
    · left
      obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
      refine Nat.lt_succ_of_le (Polynomial.natDegree_sum_le_of_forall_le _ _ fun n hn => ?_)
      have hn' : n ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      refine (Polynomial.natDegree_C_mul_le _ _).trans ((Polynomial.natDegree_pow_le).trans ?_)
      calc n * (Polynomial.X - Polynomial.C (1 : c.O)).natDegree ≤ n * 1 :=
            Nat.mul_le_mul_left _ (Polynomial.natDegree_X_sub_C_le _)
        _ ≤ k := by omega
  rcases hdeg with hd | rfl
  · have h1 := Polynomial.aeval_eq_sum_range' (R := c.O) (x := z) hd
    have h2 : Polynomial.aeval z Q = tval F N z := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp [Q, tval, map_sum]
    rw [← h2, h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def]
    rfl
  · simp [tval]

end GlobalTheory.KZ.Cmp
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ
open scoped Matrix

namespace GlobalTheory.KZ

theorem htPresNu7_mono_loss : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) (c : Coef l)
  (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) (m c₂ c' : ℕ) (ζ : Ω) (ι : Type) [Fintype ι] (P : ι → Polynomial Ω) (o : ι → Qbar l),
  HTPresNuOfPolys A c m c₂ Z ζ P o → c₂ ≤ c' → HTPresNuOfPolys A c m c' Z ζ P o := by
  intro l _ Ω _ _ _ A c Z m c₂ c' ζ ι _ P o h hc
  obtain ⟨hζ, hco, hoO, hne, hK⟩ := h
  obtain ⟨hζ₂, -, hu, ho, hs⟩ := hK
  have hl : l.Prime := Fact.out
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => by
    have : NeZero ((l ^ i : ℕ) : Ω) := ⟨by exact_mod_cast (pow_pos hl.pos i).ne'⟩
    infer_instance
  set n' := m - c' with hn'
  set d := (m - c₂) - n' with hd
  have hdn : d + n' = m - c₂ := by omega
  have hpow : (ζ ^ l ^ c₂) ^ l ^ d = ζ ^ l ^ c' := by
    rw [← pow_mul, ← pow_add]
    rcases Nat.lt_or_ge m c' with h | h
    swap
    · congr 2; omega
    · have e1 : m ≤ c₂ + d := by omega
      rw [(hζ.pow_eq_one_iff_dvd _).2 (pow_dvd_pow l e1), (hζ.pow_eq_one_iff_dvd _).2 (pow_dvd_pow l h.le)]
  have hζ' : IsPrimitiveRoot (ζ ^ l ^ c') (l ^ n') := by
    rw [← hpow]
    exact hζ₂.pow (pow_pos hl.pos _) (by rw [← pow_add, hdn])
  refine ⟨hζ, hco, hoO, hne, hζ', by omega, hu, ho, ?_⟩
  intro s hsI hcyc _
  have hfix : s (ζ ^ l ^ c₂) = ζ ^ l ^ c₂ := by
    refine GlobalTheory.Col.fix_of_cycMod (le_refl m) hcyc ?_
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  obtain ⟨k, hkv, hcg⟩ := hs s hsI hcyc hfix
  refine ⟨fun i => ((k i).val : ZMod (l ^ n')), fun i => ?_, ?_⟩
  · obtain ⟨v, hv, hsv⟩ := hkv i
    refine ⟨v ^ l ^ d, by rw [← pow_mul, ← pow_add, hdn, hv], ?_⟩
    rw [ZMod.val_natCast, map_pow, hsv, mul_pow, ← pow_mul, mul_comm (k i).val, pow_mul, hpow,
      ← pow_eq_pow_mod _ hζ'.pow_eq_one]
  · have hN : ∀ a : ℕ, ‖(a : Qbar l)‖ ≤ 1 := fun a => IsUltrametricDist.norm_natCast_le_one _ a
    have key : ∀ i, ‖o i * ((k i).val : Qbar l) -
        o i * ((((k i).val : ZMod (l ^ n')).val : ℕ) : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ n'‖ := by
      intro i
      have e : (((k i).val : ℕ) : Qbar l) =
          ((l : ℕ) : Qbar l) ^ n' * (((k i).val / l ^ n' : ℕ) : Qbar l) + (((k i).val % l ^ n' : ℕ) : Qbar l) := by
        exact_mod_cast (Nat.div_add_mod (k i).val (l ^ n')).symm
      have e2 : o i * ((k i).val : Qbar l) - o i * ((((k i).val : ZMod (l ^ n')).val : ℕ) : Qbar l) =
          ((l : ℕ) : Qbar l) ^ n' * (o i * (((k i).val / l ^ n' : ℕ) : Qbar l)) := by
        rw [ZMod.val_natCast]
        linear_combination (o i) * e
      rw [e2, norm_mul, norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (mul_le_one₀ (ho i) (norm_nonneg _) (hN _))
    have h1 : ‖Z m s 1 - ∑ i, o i * ((k i).val : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ n'‖ := by
      refine le_trans hcg ?_
      rw [norm_pow, norm_pow]
      exact pow_le_pow_of_le_one (norm_nonneg _) (hN l) (by omega)
    have h2 : ‖∑ i, (o i * ((k i).val : Qbar l) -
        o i * ((((k i).val : ZMod (l ^ n')).val : ℕ) : Qbar l))‖ ≤ ‖((l : ℕ) : Qbar l) ^ n'‖ :=
      IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) (fun i _ => key i)
    have h3 := (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)
    rw [Finset.sum_sub_distrib, sub_add_sub_cancel] at h3
    exact h3

end GlobalTheory.KZ
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem limit_nonzero_ordinary_class : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l) (c : Coef l), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → (∃ g, (mat W g - 1).det ≠ 0) → ∀ (a : ℕ → G ℚ Ω → Fin 2 → Qbar l) (N : ℕ), (∀ n s i, a n s i ∈ c.O) → (∀ n s t, Cv n (a n (s * t)) (a n s + mat W s *ᵥ a n t)) → (∀ n s, ∀ᶠ t in nhds s, Cv n (a n t) (a n s)) → (∀ n s, Cv n (a (n + 1) s) (a n s)) → (∀ n, ∀ b ∈ (toGS Ω (S : Set Pl)).ker, Cv n (a n b) 0) → (∀ n, ∀ q ∈ S, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∀ B : ValuationSubring Ω, IsPlaceOver B q → ∃ y : Fin 2 → Qbar l, VecE c y ∧ ∀ s ∈ Ine (F := ℚ) B, Cv n (a n s) (mat W s *ᵥ y - y)) → (∀ n, ∃ y : Qbar l, MemE c y ∧ ∀ s ∈ Dec (F := ℚ) A, Cg n (a n s 1) (mat W s 1 1 * y - y)) → (¬ ∃ y : Fin 2 → Qbar l, VecE c y ∧ ∀ s, Cv N (a N s) (mat W s *ᵥ y - y)) → ¬ GrZero W A := by
  intro l _ Ω _ _ _ S A W c hWc hWint hg a N ha hcoc hloc hstep hker hine hdec hN hGZ
  obtain ⟨z0, hz0O, hz0⟩ := GlobalTheory.T.exists_integral_limit_compatible_modPrimePow l c (G ℚ Ω × Fin 2) (fun n p => a n p.1 p.2) (fun n p => ha n p.1 p.2)
    (fun n p => hstep n p.1 p.2)
  let z : G ℚ Ω → Fin 2 → Qbar l := fun s i => z0 (s, i)
  have hzO : ∀ s i, z s i ∈ c.O := fun s i => hz0O (s, i)
  have hza : ∀ n s, Cv n (z s) (a n s) := fun n s i => hz0 n (s, i)
  have hZ : z ∈ Z1 (Loc.colRep W) := GlobalTheory.T.limit_of_approximate_cocycles l Ω W c hWint a z hcoc hloc hza
  have hcol : ∀ s (v : Fin 2 → Qbar l), Loc.colRep W s v = mat W s *ᵥ v := fun s v => by
    simp [Loc.colRep, Matrix.toLin'_apply]
  have hrow : ∀ s (y : Fin 2 → Qbar l) i, (fun j => (mat W s - 1) i j) ⬝ᵥ y = (mat W s *ᵥ y - y) i := by
    intro s y i
    show ((mat W s - 1) *ᵥ y) i = _
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  have hzker : ∀ b ∈ (toGS Ω (S : Set Pl)).ker, z b = 0 := by
    intro b hb
    funext i
    refine eq_zero_of_forall_norm_le _ fun n => ?_
    have h := cg_trans (hza n b i) (hker n b hb i)
    simp only [Cg, Pi.zero_apply, sub_zero] at h
    exact h
  have hexact : ∀ H : Subgroup (G ℚ Ω), (∀ n, ∃ y : Fin 2 → Qbar l, ∀ s ∈ H, Cv n (a n s) (mat W s *ᵥ y - y)) →
      ∃ x : Fin 2 → Qbar l, ∀ s ∈ H, z s = mat W s *ᵥ x - x := by
    intro H hH
    obtain ⟨x, hx⟩ := GlobalTheory.T.exists_dotProduct_eq_of_primePow_approx_qbarL l (↥H × Fin 2) 2 (fun p j => (mat W p.1 - 1) p.2 j) (fun p => z p.1 p.2) (fun n => by
      obtain ⟨y, hy⟩ := hH n
      refine ⟨y, fun p => ?_⟩
      have h := cg_trans (hza n p.1 p.2) (hy p.1 p.1.2 p.2)
      rw [← hrow] at h
      exact h)
    exact ⟨x, fun s hs => funext fun i => by rw [← hrow]; exact hx (⟨s, hs⟩, i)⟩
  have hUnr : Unr W z := by
    intro w hw
    refine ⟨placeOf Ω w, isPlaceOver_placeOf Ω w, ?_⟩
    by_cases hwS : w ∈ S
    · exact hexact (Ine (F := ℚ) (placeOf Ω w)) fun n => by
        obtain ⟨y, -, hy⟩ := hine n w hwS hw _ (isPlaceOver_placeOf Ω w)
        exact ⟨y, hy⟩
    · refine ⟨0, fun s hs => ?_⟩
      have hsN : s ∈ (toGS Ω (S : Set Pl)).ker := by
        show s ∈ (QuotientGroup.mk' (NS Ω (S : Set Pl))).ker
        rw [QuotientGroup.ker_mk']
        apply Subgroup.le_topologicalClosure
        apply Subgroup.subset_normalClosure
        simp only [Set.mem_iUnion]
        exact ⟨w, by simpa using hwS, placeOf Ω w, isPlaceOver_placeOf Ω w, hs⟩
      rw [hzker s hsN]
      simp
  have hGr : Gr W A z := by
    obtain ⟨y, hy⟩ := GlobalTheory.T.exists_dotProduct_eq_of_primePow_approx_qbarL l (↥(Dec (F := ℚ) A)) 1 (fun s _ => mat W s 1 1 - 1) (fun s => z s 1) (fun n => by
      obtain ⟨y, -, hy⟩ := hdec n
      refine ⟨fun _ => y, fun s => ?_⟩
      have h := cg_trans (hza n s 1) (hy s s.2)
      have e : (fun _ : Fin 1 => mat W s 1 1 - 1) ⬝ᵥ (fun _ => y) = mat W s 1 1 * y - y := by
        simp [dotProduct]; ring
      rw [e]; exact h)
    refine ⟨y 0, fun s hs => ?_⟩
    have h := hy ⟨s, hs⟩
    rw [h]
    simp [dotProduct]
    ring
  obtain ⟨x, hx⟩ := (mem_coboundaries1 _ _).1 (hGZ z hZ hUnr hGr)
  obtain ⟨g, hdg⟩ := hg
  have hMO : ∀ i j, (mat W g - 1) i j ∈ c.O := by
    intro i j
    rw [Matrix.sub_apply, Matrix.one_apply]
    split_ifs
    · exact c.O.sub_mem (hWint g i j) c.O.one_mem
    · exact c.O.sub_mem (hWint g i j) c.O.zero_mem
  have hdO : (mat W g - 1).det ∈ c.O := by
    rw [Matrix.det_fin_two]
    exact c.O.sub_mem (c.O.mul_mem (hMO 0 0) (hMO 1 1)) (c.O.mul_mem (hMO 0 1) (hMO 1 0))
  have hadjO : ∀ i j, (mat W g - 1).adjugate i j ∈ c.O := by
    intro i j
    rw [Matrix.adjugate_fin_two]
    fin_cases i <;> fin_cases j
    · exact hMO 1 1
    · exact c.O.neg_mem (hMO 0 1)
    · exact c.O.neg_mem (hMO 1 0)
    · exact hMO 0 0
  have hMx : (mat W g - 1) *ᵥ x = z g := by rw [hx g, hcol, Matrix.sub_mulVec, Matrix.one_mulVec]
  have hdx : (mat W g - 1).det • x = (mat W g - 1).adjugate *ᵥ z g := by
    rw [← hMx, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  obtain ⟨k, hk⟩ := GlobalTheory.T.memCoefRingInvertPrime_inv_of_mem_ne_zero l c _ hdO hdg
  have hxE : VecE c x := ⟨k, fun i => by
    have e : x i = ((mat W g - 1).det)⁻¹ * ((mat W g - 1).adjugate *ᵥ z g) i := by
      rw [← hdx, Pi.smul_apply, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hdg, one_mul]
    rw [e, ← mul_assoc]
    refine c.O.mul_mem hk ?_
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    exact c.O.add_mem (c.O.mul_mem (hadjO i 0) (hzO g 0)) (c.O.mul_mem (hadjO i 1) (hzO g 1))⟩
  refine hN ⟨x, hxE, fun s => ?_⟩
  have h := hza N s
  rw [hx s, hcol] at h
  exact cv_symm h

end GlobalTheory.Ord2

end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.Unbounded

variable {l : ℕ} [Fact l.Prime]

theorem norm_le_one_of_mem (c : Coef l) {x : Qbar l} (hx : x ∈ c.O) : ‖x‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.IntegralElementNorm.norm_le_one_of_mem
  | exact _root_.GlobalTheory.IntegralElementNorm.norm_le_one_of_mem
  | (apply _root_.GlobalTheory.IntegralElementNorm.norm_le_one_of_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralElementNorm.norm_le_one_of_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralElementNorm.norm_le_one_of_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralElementNorm.norm_le_one_of_mem ..)

theorem mulVec_mem (c : Coef l) {M : Matrix (Fin 2) (Fin 2) (Qbar l)} {x : Fin 2 → Qbar l}
    (hM : ∀ i j, M i j ∈ c.O) (hx : ∀ j, x j ∈ c.O) (i : Fin 2) : (M *ᵥ x) i ∈ c.O := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  exact c.O.add_mem (c.O.mul_mem (hM i 0) (hx 0)) (c.O.mul_mem (hM i 1) (hx 1))

theorem lpow_ne_zero (n : ℕ) : ((l : ℕ) : Qbar l) ^ n ≠ 0 :=
  pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)

theorem inv_mul_sub_mem (c : Coef l) (n : ℕ) {a b : Qbar l} (ha : a ∈ c.O) (hb : b ∈ c.O) (h : Cg n a b) :
    (((l : ℕ) : Qbar l) ^ n)⁻¹ * (a - b) ∈ c.O := by
  refine GlobalTheory.T.mem_integers_of_norm_le_one l c _ ⟨n, ?_⟩ ?_
  · rw [← mul_assoc, mul_inv_cancel₀ (lpow_ne_zero n), one_mul]
    exact c.O.sub_mem ha hb
  · rw [norm_mul, norm_inv]
    have hp : 0 < ‖((l : ℕ) : Qbar l) ^ n‖ := norm_pos_iff.2 (lpow_ne_zero n)
    rw [inv_mul_le_iff₀ hp, mul_one]
    exact h

end GlobalTheory.Ord2.Unbounded

namespace GlobalTheory.Ord2.Unbounded

theorem divSel_unbounded : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (S : Finset Pl)
    (A : ValuationSubring Ω) (W : R2 Ω l) (c : Coef l), (∀ s i j, mat W s i j ∈ c.O) → (∃ g, (mat W g - 1).det ≠ 0) →
    (∀ m : ℕ, ∃ (n : ℕ) (z : G ℚ Ω → Fin 2 → Qbar l), Coc1 c n W ⊤ z ∧ (∀ a ∈ (toGS Ω (S : Set Pl)).ker, Cv n (z a) 0) ∧
      (∀ q ∈ S, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∃ B : ValuationSubring Ω, IsPlaceOver B q ∧ Cob1 c n W (Ine (F := ℚ) B) z) ∧
      (∃ x ∈ c.O, ∀ s ∈ Dec (F := ℚ) A, Cg n (z s 1) (mat W s 1 1 * x - x)) ∧
      ¬ Cob1 c n W ⊤ (fun s => ((l : ℕ) : Qbar l) ^ m • z s)) →
    ∀ m : ℕ, ∃ x : DivSel c W S A, l ^ m • x ≠ 0 := by
  intro l _ Ω _ _ _ S A W c hW hg H m
  obtain ⟨r, hr⟩ := GlobalTheory.T.cohomologyKernel_modPrimePower_killed_by_fixed_pow l Ω W c hW hg
  obtain ⟨n, z, hcoc, hker, hine, hdec, hnot⟩ := H (m + r)
  have hz : ∀ s i, z s i ∈ c.O := hcoc.2.1
  have hL0 : ((l : ℕ) : Qbar l) ^ n ≠ 0 := lpow_ne_zero n
  set L : Qbar l := ((l : ℕ) : Qbar l) ^ n with hL
  have hLO : L ∈ c.O := natPow_mem c n
  let ζ : G ℚ Ω → Fin 2 → Qbar l := fun s => L⁻¹ • z s
  have hζ : ∀ s i, ζ s i = L⁻¹ * z s i := fun s i => rfl
  have hmem : ζ ∈ divSelCoc c W S A := by
    refine ⟨⟨n, fun s i => ?_⟩, fun s t i => ?_, fun s => ?_, fun a ha i => ?_, fun q hq hl B' hB' => ?_, ?_⟩
    · rw [hζ, ← mul_assoc, ← hL, mul_inv_cancel₀ hL0, one_mul]; exact hz s i
    · have e : ζ (s * t) i - ζ s i - (mat W s *ᵥ ζ t) i = L⁻¹ * (z (s * t) i - (z s + mat W s *ᵥ z t) i) := by
        simp only [ζ, Matrix.mulVec_smul, Pi.smul_apply, Pi.add_apply, smul_eq_mul]; ring
      rw [e]
      exact inv_mul_sub_mem c n (hz _ _) (c.O.add_mem (hz s i) (mulVec_mem c (hW s) (hz t) i))
        (hcoc.2.2 s trivial t trivial i)
    · have hc : Continuous z := by
        have := hcoc.1
        rw [Subgroup.coe_top, continuousOn_univ] at this
        exact this
      have hp : 0 < ‖L‖ := norm_pos_iff.2 hL0
      filter_upwards [Metric.tendsto_nhds.1 (hc.tendsto s) _ hp] with t ht i
      have e : ζ t i - ζ s i = L⁻¹ * (z t i - z s i) := by
        simp only [ζ, Pi.smul_apply, smul_eq_mul]; ring
      rw [e]
      refine inv_mul_sub_mem c n (hz t i) (hz s i) ?_
      unfold Cg
      rw [dist_eq_norm] at ht
      exact le_trans (norm_le_pi_norm (z t - z s) i) ht.le
    · have e : ζ a i = L⁻¹ * (z a i - 0) := by rw [sub_zero, hζ]
      rw [e]
      exact inv_mul_sub_mem c n (hz a i) c.O.zero_mem (hker a ha i)
    · obtain ⟨B, hB, hcob⟩ := hine q hq hl
      obtain ⟨x, hx, hxs⟩ := GlobalTheory.T.coboundary_inertia_independent l Ω W c n z q B B' hW hcoc hB hB' hcob
      refine ⟨L⁻¹ • x, ⟨n, fun i => ?_⟩, fun s hs i => ?_⟩
      · rw [Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← hL, mul_inv_cancel₀ hL0, one_mul]; exact hx i
      · have e : ζ s i - (mat W s *ᵥ (L⁻¹ • x) - L⁻¹ • x) i = L⁻¹ * (z s i - (mat W s *ᵥ x - x) i) := by
          simp only [ζ, Matrix.mulVec_smul, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
        rw [e]
        exact inv_mul_sub_mem c n (hz s i) (c.O.sub_mem (mulVec_mem c (hW s) hx i) (hx i)) (hxs s hs i)
    · obtain ⟨x, hx, hxs⟩ := hdec
      refine ⟨L⁻¹ * x, ⟨n, ?_⟩, fun s hs => ?_⟩
      · rw [← mul_assoc, ← hL, mul_inv_cancel₀ hL0, one_mul]; exact hx
      · have e : ζ s 1 - (mat W s 1 1 * (L⁻¹ * x) - L⁻¹ * x) = L⁻¹ * (z s 1 - (mat W s 1 1 * x - x)) := by
          rw [hζ]; ring
        rw [e]
        exact inv_mul_sub_mem c n (hz s 1) (c.O.sub_mem (c.O.mul_mem (hW s 1 1) hx) hx) (hxs s hs)
  refine ⟨QuotientAddGroup.mk ⟨ζ, hmem⟩, fun h0 => hnot ?_⟩
  rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at h0
  obtain ⟨y, ⟨k, hk⟩, hy⟩ := h0
  have hy' : ∀ s i, ((l : ℕ) : Qbar l) ^ m * ζ s i - (mat W s *ᵥ y - y) i ∈ c.O := by
    intro s i
    have := hy s i
    simp only [AddSubgroup.coe_nsmul, Pi.smul_apply, nsmul_eq_mul] at this
    push_cast at this
    exact this
  have key := hr n (fun s => ((l : ℕ) : Qbar l) ^ m • z s) (L • y)
    (fun s i => by rw [Pi.smul_apply, smul_eq_mul]; exact c.O.mul_mem (natPow_mem c m) (hz s i))
    ⟨k, fun i => by
      rw [Pi.smul_apply, smul_eq_mul, mul_left_comm]; exact c.O.mul_mem hLO (hk i)⟩
    (fun s i => by
      have e : (((l : ℕ) : Qbar l) ^ m • z s) i - (mat W s *ᵥ (L • y) - L • y) i =
          L * (((l : ℕ) : Qbar l) ^ m * ζ s i - (mat W s *ᵥ y - y) i) := by
        rw [hζ]
        simp only [Matrix.mulVec_smul, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        rw [mul_sub L, mul_sub L, mul_left_comm L, mul_inv_cancel_left₀ hL0]
      unfold Cg
      rw [e, norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (norm_le_one_of_mem c (hy' s i)))
  have hf : (fun s => ((l : ℕ) : Qbar l) ^ r • (fun s => ((l : ℕ) : Qbar l) ^ m • z s) s) =
      fun s => ((l : ℕ) : Qbar l) ^ (m + r) • z s := by
    funext s; rw [smul_smul, ← pow_add, add_comm]
  rw [hf] at key
  exact key

end GlobalTheory.Ord2.Unbounded

end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem _root_.GlobalTheory.T.continuous_residuePlaneGaloisRep_unramifiedOutside : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (S : Finset Pl) (W : R2 Ω l) (c : Coef l) (hO : ∀ s i j, mat W s i j ∈ c.O) (hN : ∀ a ∈ (toGS Ω (S : Set Pl)).ker, W a = 1), Continuous W → ContAction (resRep c W hO S hN) := by
  first | exact @GlobalTheory.Ord2.resRep_contAction | exact GlobalTheory.Ord2.resRep_contAction | (intros; apply GlobalTheory.Ord2.resRep_contAction <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem _root_.GlobalTheory.T.divCoboundary_of_reducedCocycles_cohomologous : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : R2 Ω l) (c : Coef l) (hO : ∀ s i j, mat W s i j ∈ c.O) (z z' : G ℚ Ω → Fin 2 → Qbar l) (y y' : Fin 2 → Qbar l), VecE c y → VecE c y' → (∀ s i, (l : Qbar l) * z s i - (mat W s *ᵥ y - y) i ∈ c.O) → (∀ s i, (l : Qbar l) * z' s i - (mat W s *ᵥ y' - y') i ∈ c.O) → (∃ m : ResPlane c, ∀ s, resCoc c W z y s - resCoc c W z' y' s = resAct c W hO s m - m) → z - z' ∈ divCob c W := by
  first | exact @GlobalTheory.Ord2.divCob_of_resCoc_cohom | exact GlobalTheory.Ord2.divCob_of_resCoc_cohom | (intros; apply GlobalTheory.Ord2.divCob_of_resCoc_cohom <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

namespace GlobalTheory.Ord2.SelPerp

theorem coef_free_pairSurj (l : ℕ) [Fact l.Prime] (c : Coef l) : Module.Free ℤ_[l] c.O := by
  haveI : Module.IsTorsionFree ℤ_[l] c.O := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun a x h => ?_
    have h' : a • (x : Qbar l) = 0 := by rw [← Subalgebra.coe_smul, h]; rfl
    rw [Algebra.smul_def, mul_eq_zero] at h'
    rcases h' with h' | h'
    · left
      have := congrArg norm h'
      rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), norm_algebraMap', norm_zero] at this
      have h2 : ((a : ℤ_[l]) : ℚ_[l]) = 0 := norm_eq_zero.1 this
      exact PadicInt.coe_eq_zero.1 h2
    · right
      exact Subtype.ext h'
  infer_instance

theorem exists_eq_tbA_mul (l : ℕ) [Fact l.Prime] (c : Coef l) (n : ℕ) (φ : Qn c n →+ ZMod (l ^ n)) :
    ∃ b : Qn c n, ∀ a : Qn c n, φ a = GlobalTheory.Ord2.SelPerp.tbA c n (a * b) := by
  classical
  haveI := coef_free_pairSurj l c
  let e := Module.Free.chooseBasis ℤ_[l] c.O
  let f : c.O →ₗ[ℤ_[l]] ℤ_[l] := e.constr ℤ_[l] fun i => (((φ (red c n (e i))).val : ℕ) : ℤ_[l])
  have hf : ∀ x : c.O, PadicInt.toZModPow n (f x) = φ (red c n x) := by
    intro x
    have hx : x ∈ Submodule.span ℤ_[l] (Set.range e) := by rw [e.span_eq]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      simp only [f, Module.Basis.constr_basis]
      rw [map_natCast, ZMod.natCast_zmod_val]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]
    | smul a x _ hx =>
      rw [map_smul, smul_eq_mul, map_mul, hx, red_smul, map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val]
  obtain ⟨b, hb, -⟩ := tau_spec c f
  refine ⟨red c n b, fun a => ?_⟩
  obtain ⟨x, rfl⟩ := red_surjective c n a
  rw [← hf, hb, ← map_mul, tbA_red, mul_comm]

end GlobalTheory.Ord2.SelPerp
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix


theorem _root_.GlobalTheory.T.ordinarySelmerModPrimePow_injects_residualSelmer : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ (c : Coef l) (hint : ∀ s i j, mat W s i j ∈ c.O) (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1) (n : ℕ), 1 ≤ n → ∃ cls : (G ℚ Ω → Fin 2 → Qbar l) → H1 (rhoS c n W hint S hN), (∀ y, GwCount.SelN c n S A W y → cls y ∈ SelG c n W hint S hN A) ∧ ∀ y y', GwCount.SelN c n S A W y → GwCount.SelN c n S A W y' → cls y = cls y' → Cob1 c n W ⊤ (y - y') := by
  first | exact @GlobalTheory.Ord2.SelLower.sel_lower | exact GlobalTheory.Ord2.SelLower.sel_lower | (intros; apply GlobalTheory.Ord2.SelLower.sel_lower <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix


theorem _root_.GlobalTheory.T.archimedean_invariants_card : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ (c : Coef l) (hint : ∀ s i j, mat W s i j ∈ c.O) (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1) (n : ℕ), 1 ≤ n → ∀ cc : InfinitePlace ℚ → G ℚ Ω, (∀ w, w.IsReal → IsCCAt w (cc w)) → archH0Card S (rhoS c n W hint S hN) cc = Nat.card (Qn c n) := by
  first | exact @GlobalTheory.Ord2.GwIneq.Arch.archimedean_h0_card_eq | exact GlobalTheory.Ord2.GwIneq.Arch.archimedean_h0_card_eq | (intros; apply GlobalTheory.Ord2.GwIneq.Arch.archimedean_h0_card_eq <;> assumption)
end
