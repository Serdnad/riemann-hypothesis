module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.PMinorAff
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open scoped BigOperators
open Classical

namespace PI.EntAtD.W

open PI.EntAtD

section Ker

variable {A : Type} [CommRing A] (D : Derivation ℤ A A)

end Ker

private theorem derivation_prod_eq_zero_of_forall' {R A ι : Type} [CommRing R] [CommRing A] [Algebra R A]
    (D : Derivation R A A) (s : Finset ι) (f : ι → A) (h : ∀ i ∈ s, D (f i) = 0) :
    D (∏ i ∈ s, f i) = 0 := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp
  · intro i s hi ih h
    rw [Finset.prod_insert hi, Derivation.leibniz, h i (Finset.mem_insert_self i s),
      ih (fun j hj => h j (Finset.mem_insert_of_mem hj)), smul_zero, smul_zero, add_zero]

private theorem derivation_det_eq_zero_of_entries {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (D : Derivation R A A) {k : ℕ} (M : Matrix (Fin k) (Fin k) A) (h : ∀ i j, D (M i j) = 0) :
    D M.det = 0 := by

  rw [Matrix.det_apply, map_sum]
  refine Finset.sum_eq_zero fun σ _ => ?_
  rw [Units.smul_def, map_zsmul, derivation_prod_eq_zero_of_forall' D _ _ (fun i _ => h _ _), smul_zero]

theorem heart_pderiv_minor {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N0 N1 : ℕ) (s s' : Lt) (hs : s ≠ s')
    (k : ℕ) (I : Fin k ↪o Fin N1) (a : Fin N0) (b : Fin N1) :
    MvPolynomial.pderiv (R := ℤ) (Sum.inr (s', a, b)) (minorXZ N0 N1 s k I) = 0 := by
  simp only [minorXZ]
  apply derivation_det_eq_zero_of_entries
  intro i j

  rw [Matrix.of_apply, map_sum]
  refine Finset.sum_eq_zero fun a0 _ => ?_
  rw [Derivation.leibniz, MvPolynomial.pderiv_X, MvPolynomial.pderiv_X]
  simp [Pi.single_apply, hs, Ne.symm hs]

private theorem derivation_finset_sum_apply' {R A ι : Type} [CommRing R] [CommRing A] [Algebra R A]
    (s : Finset ι) (D : ι → Derivation R A A) (x : A) : (∑ i ∈ s, D i) x = ∑ i ∈ s, D i x := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro i s hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi, Derivation.add_apply, ih]

theorem heart_dRow_zero {H : Type} {N0 N1 : ℕ} (t : H) (r : ℕ) (b : Fin N1) (f : PolyXZ H N0 N1)
    (h : ∀ a : Fin N0, MvPolynomial.pderiv (R := ℤ) (Sum.inr ((true, t), a, b)) f = 0) :
    dRow (N0 := N0) t r b f = 0 := by
  simp only [dRow]
  rw [derivation_finset_sum_apply']
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [Derivation.smul_apply, h a, smul_zero]

theorem heart_sdeg_prod (hS : PSDegMul) {A : Type} [CommRing A] {ι : Type} (d : ι → Derivation ℤ A A)
    {κ : Type} [DecidableEq κ] (s : Finset κ) (f : κ → A) (k : κ → ℕ) :
    (∀ i ∈ s, SDegD d (k i) (f i)) → SDegD d (∑ i ∈ s, k i) (∏ i ∈ s, f i) := by
  refine Finset.induction_on s ?_ ?_
  · intro _
    rw [Finset.sum_empty, Finset.prod_empty]
    intro j
    exact (d j).map_one_eq_zero
  · intro i s hi ih h
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    exact hS A ι d _ _ _ _ (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem lapZero_of (hM : PMinorAff) (hS : PSDegMul) (hF : PLapForms) : PLapZero := by
  intro H _ inst N0 N1 nu I t n hn
  clear inst
  let P : Bool × H → PolyXZ H N0 N1 := fun s => ∏ c : Fin ((nu s).rowLen 0),
    minorXZ (Lt := Bool × H) N0 N1 s ((nu s).colLen c) (I s c)
  let R : PolyXZ H N0 N1 := ∏ s ∈ (Finset.univ.erase (false, t)).erase (true, t), P s
  have hne : (true, t) ≠ (false, t) := by simp
  have hmem : (true, t) ∈ Finset.univ.erase (false, t) := by simp
  have hG : Gxz N0 N1 nu I = P (false, t) * (P (true, t) * R) := by
    show (∏ s, P s) = _
    rw [← Finset.mul_prod_erase Finset.univ P (Finset.mem_univ (false, t)),
      ← Finset.mul_prod_erase (Finset.univ.erase (false, t)) P hmem]
  have hnoP : ∀ (s s' : Bool × H), s ≠ s' → ∀ (a : Fin N0) (b : Fin N1),
      MvPolynomial.pderiv (R := ℤ) (Sum.inr (s', a, b)) (P s) = 0 := by
    intro s s' hs a b
    apply derivation_prod_eq_zero_of_forall'
    intro c _
    convert heart_pderiv_minor N0 N1 s s' hs _ (I s c) a b
  have hnoR : ∀ (s' : Bool × H), s' = (false, t) ∨ s' = (true, t) → ∀ (a : Fin N0) (b : Fin N1),
      MvPolynomial.pderiv (R := ℤ) (Sum.inr (s', a, b)) R = 0 := by
    intro s' hs' a b
    apply derivation_prod_eq_zero_of_forall'
    intro s hs
    apply hnoP s s' _ a b
    rintro rfl
    rcases hs' with rfl | rfl
    · exact Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hs) rfl
    · exact Finset.ne_of_mem_erase hs rfl
  have h1 : ∀ (a : Fin N0) (b : Fin N1), pd (Sum.inr ((false, t), a, b)) (P (true, t) * R) = 0 := by
    intro a b
    show MvPolynomial.pderiv (R := ℤ) (Sum.inr ((false, t), a, b)) (P (true, t) * R) = 0
    rw [Derivation.leibniz, hnoP (true, t) (false, t) hne a b, hnoR (false, t) (Or.inl rfl) a b,
      smul_zero, smul_zero, add_zero]
  have hR0 : SDegD (fun b : Fin N1 => dRow (N0 := N0) t 0 b) 0 R := by
    intro b
    exact heart_dRow_zero t 0 b R (fun a => hnoR (true, t) (Or.inr rfl) a b)
  have hmin : ∀ c : Fin ((nu (true, t)).rowLen 0), SDegD (fun b : Fin N1 => dRow (N0 := N0) t 0 b) 1
      (minorXZ (Lt := Bool × H) N0 N1 (true, t) ((nu (true, t)).colLen c) (I (true, t) c)) := by
    intro c j j'
    exact hM H N0 N1 t _ _ j' j
  have hPT0 := heart_sdeg_prod hS (fun b : Fin N1 => dRow (N0 := N0) t 0 b) Finset.univ _ (fun _ => 1)
    (fun c _ => hmin c)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hPT0
  have hPT : SDegD (fun b : Fin N1 => dRow (N0 := N0) t 0 b) ((nu (true, t)).rowLen 0) (P (true, t)) :=
    hPT0
  have h2 := hS _ _ _ _ _ _ 0 hPT hR0
  rw [hG]
  exact hF H N0 N1 (nu (false, t)) (I (false, t)) t (P (true, t) * R) ((nu (true, t)).rowLen 0) n h1 h2 hn

end PI.EntAtD.W
end
end

section

noncomputable section

open scoped BigOperators
open Classical

namespace PI.EntAtD.W

open PI.EntAtD

namespace ExponentialCoefficients

variable {H : Type} [Fintype H] [DecidableEq H] {N0 N1 : ℕ}

abbrev JI (H : Type) (N0 N1 : ℕ) : Type := H × Fin N0 × Fin N1

def vX (s : Bool) (j : JI H N0 N1) : ZV H N0 N1 := ((s, j.1), j.2.1, j.2.2)

def eJ (j : JI H N0 N1) : ZV H N0 N1 →₀ ℕ :=
  Finsupp.single (vX false j) 1 + Finsupp.single (vX true j) 1

def eK (k : JI H N0 N1 → ℕ) : ZV H N0 N1 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun v => k (v.1.2, v.2))

theorem eK_apply (k : JI H N0 N1 → ℕ) (s : Bool) (t : H) (a : Fin N0) (b : Fin N1) :
    eK k ((s, t), a, b) = k (t, a, b) := by
  first
  | rfl
  | simp [eK]

theorem sum_eJ (k : JI H N0 N1 → ℕ) : ∑ j, k j • eJ j = eK k := by
  ext ⟨⟨s, t⟩, a, b⟩
  rw [eK_apply, Finsupp.finsetSum_apply, Finset.sum_eq_single (t, a, b)]
  · cases s <;> simp [eJ, vX, Finsupp.single_apply]
  · rintro ⟨t', a', b'⟩ _ hne
    simp only [eJ, vX, Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul,
      Prod.mk.injEq]
    split_ifs <;> simp_all
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem eK_eq_iff (k : JI H N0 N1 → ℕ) (κ : ZV H N0 N1 →₀ ℕ) :
    κ = eK k ↔ (∀ t a b, κ ((false, t), a, b) = κ ((true, t), a, b)) ∧ k = fun j => κ (vX true j) := by
  constructor
  · rintro rfl
    refine ⟨fun t a b => by rw [eK_apply, eK_apply], ?_⟩
    funext ⟨t, a, b⟩
    exact (eK_apply k true t a b).symm
  · rintro ⟨h1, rfl⟩
    ext ⟨⟨s, t⟩, a, b⟩
    rw [eK_apply]
    cases s
    · exact h1 t a b
    · rfl

theorem prod_monomial' {σ ι R : Type*} [CommSemiring R] (s : Finset ι) (f : ι → σ →₀ ℕ) (a : ι → R) :
    ∏ i ∈ s, MvPowerSeries.monomial (f i) (a i) =
      MvPowerSeries.monomial (∑ i ∈ s, f i) (∏ i ∈ s, a i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [MvPowerSeries.monomial_zero_one]
  · intro i s hi ih
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi, ih,
      MvPowerSeries.monomial_mul_monomial]

variable (p : ℕ) [Fact p.Prime]

theorem f_eq (S : ℂ_[p]) (ut : H → ℂ_[p]) :
    (-(S • ∑ t : H, ut t • ∑ a : Fin N0, ∑ b : Fin N1,
        (MvPowerSeries.X ((false, t), a, b) * MvPowerSeries.X ((true, t), a, b) :
          MvPowerSeries (ZV H N0 N1) ℂ_[p]))) =
      ∑ j : JI H N0 N1, MvPowerSeries.monomial (eJ j) (-(S * ut j.1)) := by
  have key : ∀ (c : ℂ_[p]) (n : ZV H N0 N1 →₀ ℕ),
      c • (MvPowerSeries.monomial n (1 : ℂ_[p])) = MvPowerSeries.monomial n c := by
    intro c n
    rw [← map_smul, smul_eq_mul, mul_one]
  simp only [Finset.smul_sum, ← Finset.sum_neg_distrib, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun b _ => ?_
  rw [MvPowerSeries.X, MvPowerSeries.X, MvPowerSeries.monomial_mul_monomial, mul_one, smul_smul,
    ← neg_smul, key]
  rfl

theorem cc_zero (S : ℂ_[p]) (ut : H → ℂ_[p]) :
    MvPowerSeries.constantCoeff
      (∑ j : JI H N0 N1, MvPowerSeries.monomial (eJ j) (-(S * ut j.1))) = 0 := by

  rw [map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_monomial, if_neg]
  intro h
  have h2 := DFunLike.congr_fun h (vX false j)
  simp [eJ, vX, Finsupp.single_apply] at h2

private theorem monomial_pow_lemma {σ R : Type*} [CommSemiring R] (n : σ →₀ ℕ) (a : R) (k : ℕ) :
    MvPowerSeries.monomial n a ^ k = MvPowerSeries.monomial (k • n) (a ^ k) := by
  induction k with
  | zero => simp [MvPowerSeries.monomial_zero_one]
  | succ k ih => rw [pow_succ, ih, MvPowerSeries.monomial_mul_monomial, succ_nsmul, pow_succ]

theorem coeff_pow (S : ℂ_[p]) (ut : H → ℂ_[p]) (κ : ZV H N0 N1 →₀ ℕ) (d : ℕ) :
    MvPowerSeries.coeff κ ((∑ j : JI H N0 N1, MvPowerSeries.monomial (eJ j) (-(S * ut j.1))) ^ d) =
      if (∀ t a b, κ ((false, t), a, b) = κ ((true, t), a, b)) ∧ ∑ j, κ (vX true j) = d then
        ((Nat.multinomial Finset.univ fun j => κ (vX true j) : ℕ) : ℂ_[p]) *
          ∏ j, (-(S * ut j.1)) ^ κ (vX true j)
      else 0 := by
  classical
  have hn : ∀ (n : ℕ) (m : ZV H N0 N1 →₀ ℕ) (c : ℂ_[p]),
      (n : MvPowerSeries (ZV H N0 N1) ℂ_[p]) * MvPowerSeries.monomial m c =
        MvPowerSeries.monomial m ((n : ℂ_[p]) * c) := by
    intro n m c
    rw [← nsmul_eq_mul, ← map_nsmul, nsmul_eq_mul]
  have hterm : ∀ k : JI H N0 N1 → ℕ,
      (Nat.multinomial Finset.univ k : MvPowerSeries (ZV H N0 N1) ℂ_[p]) *
          ∏ j, MvPowerSeries.monomial (eJ j) (-(S * ut j.1)) ^ k j =
        MvPowerSeries.monomial (eK k)
          ((Nat.multinomial Finset.univ k : ℂ_[p]) * ∏ j, (-(S * ut j.1)) ^ k j) := by
    intro k
    simp only [monomial_pow_lemma]
    rw [prod_monomial', sum_eJ, hn]

  rw [Finset.sum_pow_eq_sum_piAntidiag, map_sum]
  simp only [hterm, MvPowerSeries.coeff_monomial]
  split_ifs with h
  · rw [Finset.sum_eq_single (fun j => κ (vX true j))]
    · rw [if_pos ((eK_eq_iff _ _).2 ⟨h.1, rfl⟩)]
    · intro k _ hk
      rw [if_neg]
      intro he
      exact hk ((eK_eq_iff k κ).1 he).2
    · intro hn'
      exfalso
      apply hn'
      rw [Finset.mem_piAntidiag]
      exact ⟨h.2, fun i _ => Finset.mem_univ i⟩
  · refine Finset.sum_eq_zero fun k hk => ?_
    rw [if_neg]
    intro he
    apply h
    obtain ⟨h1, h2⟩ := (eK_eq_iff k κ).1 he
    refine ⟨h1, ?_⟩
    rw [Finset.mem_piAntidiag] at hk
    subst h2
    exact hk.1

end ExponentialCoefficients

theorem pExpCoeff : PExpCoeff := by
  intro H _ _ N0 N1 p _ S ut κ
  have hs : PowerSeries.HasSubst (∑ j : ExponentialCoefficients.JI H N0 N1,
      MvPowerSeries.monomial (ExponentialCoefficients.eJ j) (-(S * ut j.1))) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (ExponentialCoefficients.cc_zero p S ut)
  rw [expS, ExponentialCoefficients.f_eq, PowerSeries.coeff_subst hs]
  simp only [ExponentialCoefficients.coeff_pow, PowerSeries.coeff_exp, smul_eq_mul]
  split_ifs with hbal
  · rw [finsum_eq_single _ (∑ j, κ (ExponentialCoefficients.vX true j)) ?_]
    · rw [if_pos ⟨hbal, rfl⟩]
      have hκ : (κ.prod fun _ k => (k.factorial : ℂ_[p])) =
          ∏ j : ExponentialCoefficients.JI H N0 N1, ((κ (ExponentialCoefficients.vX true j)).factorial : ℂ_[p]) ^ 2 := by
        rw [Finsupp.prod_fintype _ _ (fun _ => by simp)]
        let e : (Bool × ExponentialCoefficients.JI H N0 N1) ≃ ZV H N0 N1 :=
          { toFun := fun x => ExponentialCoefficients.vX x.1 x.2
            invFun := fun v => (v.1.1, v.1.2, v.2)
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
        rw [← e.prod_comp, Fintype.prod_prod_type, Fintype.prod_bool, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun j _ => ?_
        obtain ⟨t, a, b⟩ := j
        simp only [e, Equiv.coe_fn_mk, ExponentialCoefficients.vX]
        rw [← hbal t a b, sq]
      have hR : (∏ t : H, ∏ a : Fin N0, ∏ b : Fin N1,
          ((κ ((true, t), a, b)).factorial : ℂ_[p]) * (-(S * ut t)) ^ κ ((true, t), a, b)) =
          ∏ j : ExponentialCoefficients.JI H N0 N1, ((κ (ExponentialCoefficients.vX true j)).factorial : ℂ_[p]) *
            (-(S * ut j.1)) ^ κ (ExponentialCoefficients.vX true j) := by
        simp only [Fintype.prod_prod_type] <;> rfl
      have hM := congrArg (Nat.cast (R := ℂ_[p]))
        (Nat.multinomial_spec Finset.univ (fun j => κ (ExponentialCoefficients.vX true j)))
      push_cast at hM
      have hD : ((∑ j, κ (ExponentialCoefficients.vX true j)).factorial : ℂ_[p]) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      rw [hκ, hR, Finset.prod_mul_distrib, Finset.prod_pow, map_div₀, map_one, map_natCast]
      rw [← hM] at hD ⊢
      have hMne := right_ne_zero_of_mul hD
      field_simp
    · intro d hd
      rw [if_neg, mul_zero]
      rintro ⟨_, h⟩
      exact hd h.symm
  · rw [finsum_eq_zero_of_forall_eq_zero, mul_zero]
    intro d
    rw [if_neg, mul_zero]
    rintro ⟨h, _⟩
    exact hbal h

end PI.EntAtD.W
end
end

section

noncomputable section

open scoped BigOperators

namespace PI.EntAtD.W

open PI.EntAtD

section DerDet

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A]

theorem minorAff_derProd {ι : Type} [DecidableEq ι] (D : Derivation R A A) (f : ι → A) (s : Finset ι) :
    D (∏ j ∈ s, f j) = ∑ i ∈ s, (∏ j ∈ s.erase i, f j) * D (f i) := by
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro i s hi ih
    rw [Finset.prod_insert hi, Derivation.leibniz, ih, Finset.sum_insert hi, Finset.erase_insert hi,
      smul_eq_mul, smul_eq_mul, add_comm, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.erase_insert_of_ne (by rintro rfl; exact hi hk),
      Finset.prod_insert (fun h => hi (Finset.mem_of_mem_erase h)), mul_assoc]

theorem minorAff_derDet (D : Derivation R A A) {k : ℕ} (M : Matrix (Fin k) (Fin k) A) :
    D M.det = ∑ i, (M.updateCol i (fun r => D (M r i))).det := by
  classical

  simp only [Matrix.det_apply, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Units.smul_def, map_zsmul, minorAff_derProd, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : ∏ j, (M.updateCol i (fun r => D (M r i))) (σ j) j =
      D (M (σ i) i) * ∏ j ∈ Finset.univ.erase i, M (σ j) j := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), Matrix.updateCol_self]
    congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    exact Matrix.updateCol_ne (Finset.ne_of_mem_erase hj)
  rw [Units.smul_def, h1, mul_comm]

theorem minorAff_sumApply {ι : Type} [DecidableEq ι] (s : Finset ι) (D : ι → Derivation R A A) (x : A) :
    (∑ i ∈ s, D i) x = ∑ i ∈ s, D i x := by
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro i s hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi, Derivation.add_apply, ih]

end DerDet

theorem pMinorAff : PMinorAff := by
  intro H N0 N1 t k I b b'
  classical
  let y : Fin k → PolyXZ H N0 N1 := fun i => ∑ a : Fin N0,
    (MvPolynomial.X (Sum.inl ((false, t), 0, a)) : PolyXZ H N0 N1) *
      MvPolynomial.X (Sum.inl ((true, t), (i : ℕ), a))
  have hD : ∀ (bb : Fin N1) (f : PolyXZ H N0 N1), dRow (N0 := N0) t 0 bb f =
      ∑ a : Fin N0, (MvPolynomial.X (Sum.inl ((false, t), 0, a)) : PolyXZ H N0 N1) *
        MvPolynomial.pderiv (R := ℤ) (Sum.inr ((true, t), a, bb)) f := by
    intro bb f
    simp only [dRow]
    rw [minorAff_sumApply]
    simp only [Derivation.smul_apply, smul_eq_mul]
  have hE : ∀ (bb c : Fin N1) (i : Fin k), dRow (N0 := N0) t 0 bb
      (∑ a : Fin N0, (MvPolynomial.X (Sum.inl ((true, t), (i : ℕ), a)) : PolyXZ H N0 N1) *
        MvPolynomial.X (Sum.inr ((true, t), a, c))) = if c = bb then y i else 0 := by
    intro bb c i
    rw [hD]
    by_cases hc : c = bb
    · subst hc

      simp [y, map_sum, Derivation.leibniz, MvPolynomial.pderiv_X, Pi.single_apply]

    · simp [map_sum, Derivation.leibniz, MvPolynomial.pderiv_X, Pi.single_apply, hc]
  have hy : ∀ (bb : Fin N1) (i : Fin k), dRow (N0 := N0) t 0 bb (y i) = 0 := by
    intro bb i
    rw [hD]

    simp [y, map_sum, Derivation.leibniz, MvPolynomial.pderiv_X, Pi.single_apply]
  simp only [minorXZ]

  rw [minorAff_derDet, map_sum]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases hc : I c = b'
  · have hcol : (fun r => dRow (N0 := N0) t 0 b' (Matrix.of (fun i k' : Fin k => ∑ a : Fin N0,
        (MvPolynomial.X (Sum.inl ((true, t), (i : ℕ), a)) : PolyXZ H N0 N1) *
          MvPolynomial.X (Sum.inr ((true, t), a, I k'))) r c)) = y := by
      funext r
      rw [Matrix.of_apply, hE, if_pos hc]
    rw [hcol, minorAff_derDet]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : l = c
    · subst hl
      apply Matrix.det_eq_zero_of_column_eq_zero l
      intro r
      simp only [Matrix.updateCol_self, hy]
    · by_cases hIl : I l = b
      · apply Matrix.det_zero_of_column_eq hl
        intro r
        simp only [Matrix.updateCol_self, Matrix.updateCol_ne hl, Matrix.updateCol_ne (Ne.symm hl),
          Matrix.of_apply, hE, if_pos hIl]
      · apply Matrix.det_eq_zero_of_column_eq_zero l
        intro r
        simp only [Matrix.updateCol_self, Matrix.updateCol_ne hl, Matrix.of_apply, hE, if_neg hIl]
  · have hcol : (fun r => dRow (N0 := N0) t 0 b' (Matrix.of (fun i k' : Fin k => ∑ a : Fin N0,
        (MvPolynomial.X (Sum.inl ((true, t), (i : ℕ), a)) : PolyXZ H N0 N1) *
          MvPolynomial.X (Sum.inr ((true, t), a, I k'))) r c)) = fun _ => 0 := by
      funext r
      rw [Matrix.of_apply, hE, if_neg hc]
    rw [hcol]
    convert map_zero (dRow (N0 := N0) t 0 b)
    exact Matrix.det_eq_zero_of_column_eq_zero c fun r => Matrix.updateCol_self

end PI.EntAtD.W
end
end
