module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 1

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatCris

section Abstract

theorem eq_of_factorial_mul {B : Type} [CommRing B] [Algebra ℚ B] {l : ℕ} (hl : l ≠ 0) (M n : ℕ)
    {D b : B} (h : (n.factorial : B) * D = b ^ n) :
    D = (l : B) ^ (M * n) * (((n.factorial : ℚ))⁻¹ • (((l : ℚ) ^ M)⁻¹ • b) ^ n) := by
  have hl' : (l : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hl
  have hn : (n.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 n.factorial_ne_zero
  rw [smul_pow, ← h, Algebra.smul_def, Algebra.smul_def]
  have e1 : (l : B) = algebraMap ℚ B (l : ℚ) := (map_natCast _ _).symm
  have e2 : (n.factorial : B) = algebraMap ℚ B (n.factorial : ℚ) := (map_natCast _ _).symm
  rw [e1, e2, ← map_pow, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, ← map_mul]
  have e3 : (l : ℚ) ^ (M * n) * (n.factorial : ℚ)⁻¹ * (((l : ℚ) ^ M)⁻¹) ^ n * (n.factorial : ℚ) = 1 := by
    rw [pow_mul, inv_pow]
    have : ((l : ℚ) ^ M) ^ n ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hl')
    field_simp
  rw [e3, map_one, one_mul]

variable {W A B C : Type} [CommRing W] [CommRing A] [Algebra W A] [CommRing B] [Algebra ℚ B]
  [CommRing C] [Algebra ℚ C]

theorem map_dp_mem (T : A →+* B) (g : B →+* C) (f : W →+* C)
    (hf : ∀ w, g (T (algebraMap W A w)) = f w) (ξ : W) {l : ℕ} (hl : l ≠ 0) (M n : ℕ) {d : A}
    (hd : (n.factorial : A) * d = algebraMap W A ξ ^ n) : g (T d) ∈ sub f ξ l M := by
  have h1 : (n.factorial : B) * T d = T (algebraMap W A ξ) ^ n := by
    rw [← map_pow, ← hd, map_mul, map_natCast]
  have h2 : g (T d) = (l : C) ^ (M * n) * dpE f ξ l M n := by
    rw [eq_of_factorial_mul hl M n h1, map_mul, map_pow, map_natCast, dpE, η, map_rat_smul, map_pow,
      map_rat_smul, hf]
  rw [h2]
  exact mul_mem (pow_mem (natCast_mem _ l) _) (Subring.subset_closure (Or.inr ⟨n, rfl⟩))

theorem map_adjoin_mem (T : A →+* B) (g : B →+* C) (f : W →+* C)
    (hf : ∀ w, g (T (algebraMap W A w)) = f w) (ξ : W) {l : ℕ} (hl : l ≠ 0) (M : ℕ) (d : ℕ → A)
    (hd : ∀ n, (n.factorial : A) * d n = algebraMap W A ξ ^ n) {s : A}
    (hs : s ∈ Algebra.adjoin W (Set.range d)) : g (T s) ∈ sub f ξ l M := by
  induction hs using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨n, rfl⟩ := hy
    exact map_dp_mem T g f hf ξ hl M n (hd n)
  | algebraMap x => rw [hf]; exact Subring.subset_closure (Or.inl (Set.mem_range_self x))
  | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _)]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul, map_mul]; exact mul_mem hx hy

end Abstract

variable (l : ℕ) [Fact l.Prime]

local notation "𝔸" => Localization.Away (l : AInf ℂ_[l] l)

theorem mem_adjoin_dpow {s : 𝔸} (hs : s ∈ ACris.ACrisZero ℂ_[l] l) :
    s ∈ Algebra.adjoin (AInf ℂ_[l] l) (Set.range fun n : ℕ => ACris.dpow n (xi0 l)) := by
  rw [← ACris.acrisZero_eq_adjoin ker_theta0]; exact hs

theorem factorial_mul_dpow_xi (n : ℕ) :
    ((n.factorial : 𝔸)) * ACris.dpow n (xi0 l) = algebraMap (AInf ℂ_[l] l) 𝔸 (xi0 l) ^ n :=
  ACris.factorial_mul_dpow n _

theorem pk_toB_algebraMap (k : ℕ) (w : AInf ℂ_[l] l) :
    pk l k (toBDeRhamPlus (normInteger ℂ_[l]) l (algebraMap (AInf ℂ_[l] l) 𝔸 w)) = fk l k w := rfl


theorem pk_toB_mem (k M : ℕ) {s : 𝔸} (hs : s ∈ ACris.ACrisZero ℂ_[l] l) :
    pk l k (toBDeRhamPlus (normInteger ℂ_[l]) l s) ∈ sub (fk l k) (xi0 l) l M :=
  map_adjoin_mem (W := AInf ℂ_[l] l) (A := 𝔸) (B := BdRp l) (C := Bk l k)
    (toBDeRhamPlus (normInteger ℂ_[l]) l) (pk l k) (fk l k) (pk_toB_algebraMap l k) (xi0 l)
    (Fact.out : l.Prime).ne_zero M (fun n => ACris.dpow n (xi0 l))
    (factorial_mul_dpow_xi l) (mem_adjoin_dpow l hs)



theorem cris_in (l : ℕ) [Fact l.Prime] (M k : ℕ) (c : Acris l) :
    Lat.pk l k (ACris.iota ℂ_[l] l c) ∈ Lat.sub (Lat.fk l k) (xi0 l) l M := by
  obtain ⟨s, hs, hst⟩ := (ACris.embedding₂ ℂ_[l] l k c).2
  have e1 : IsPerfectoidField.evalB ℂ_[l] l k (ACris.iota ℂ_[l] l c) =
      (ACris.embedding₂ ℂ_[l] l k c).1 := ACris.evalₐ_iota k c
  have e2 := IsPerfectoidField.evalB_toBDeRhamPlus (K := ℂ_[l]) (p := l) k s
  have e3 : ACris.iota ℂ_[l] l c - toBDeRhamPlus (normInteger ℂ_[l]) l s ∈
      Ideal.span {tBdR l ^ k} := by
    rw [← Ideal.span_singleton_pow, ← maximalIdeal_eq_span_tBdR, ← IsPerfectoidField.ker_evalB,
      RingHom.mem_ker, map_sub, e1, e2, sub_eq_zero]
    exact hst.symm
  have e4 : pk l k (ACris.iota ℂ_[l] l c) = pk l k (toBDeRhamPlus (normInteger ℂ_[l]) l s) :=
    Ideal.Quotient.eq.2 e3
  rw [e4]
  exact pk_toB_mem l k M hs

end GlobalTheory.CompanionTheory.LatCris
end
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatC

theorem existsUnique_limit_of_dvd {R : Type*} [CommRing R] (t : R)
    [IsAdicComplete (Ideal.span {t}) R] (z : ℕ → R)
    (hz : ∀ m, t ^ (m + 1) ∣ z (m + 1) - z m) :
    ∃! x : R, ∀ m, t ^ (m + 1) ∣ x - z m := by
  have hmem : ∀ (n : ℕ) (a : R), a ∈ ((Ideal.span {t}) ^ n • ⊤ : Submodule R R) ↔ t ^ n ∣ a := by
    intro n a
    rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have hchain : ∀ {m n : ℕ}, m ≤ n → t ^ m ∣ z n - z m := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hn ih =>
      have h1 : t ^ m ∣ z (n + 1) - z n := (pow_dvd_pow t (by omega)).trans (hz n)
      have h2 := dvd_add h1 ih
      simpa using h2
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {t}) z (fun {m n} hmn => by
    rw [SModEq.comm, SModEq.sub_mem, hmem]
    exact hchain hmn)
  refine ⟨L, fun m => ?_, fun x hx => ?_⟩
  · have h1 : t ^ (m + 1) ∣ L - z (m + 1) := by
      have := hL (m + 1)
      rw [SModEq.comm, SModEq.sub_mem, hmem] at this
      exact this
    have h2 := dvd_add h1 (hz m)
    simpa using h2
  · have hLd : ∀ m, t ^ (m + 1) ∣ L - z m := by
      intro m
      have h1 : t ^ (m + 1) ∣ L - z (m + 1) := by
        have := hL (m + 1)
        rw [SModEq.comm, SModEq.sub_mem, hmem] at this
        exact this
      have h2 := dvd_add h1 (hz m)
      simpa using h2
    refine sub_eq_zero.1 (IsHausdorff.haus' (I := Ideal.span {t}) _ fun n => ?_)
    rw [SModEq.zero, hmem]
    have h3 := dvd_sub (hx n) (hLd n)
    have h4 : t ^ (n + 1) ∣ x - L := by simpa using h3
    exact (pow_dvd_pow t (Nat.le_succ n)).trans h4

theorem isAdicComplete_span_tBdR (l : ℕ) [Fact l.Prime] :
    IsAdicComplete (Ideal.span {tBdR l}) (BdRp l) := by
  rw [← maximalIdeal_eq_span_tBdR]
  exact IsPerfectoidField.instIsAdicCompleteMaximalIdealBdR

theorem pInv_rangeRestrict (l : ℕ) [Fact l.Prime] (b : BdRp l) :
    pInv l ((algebraMap (BdRp l) (BdR l)).rangeRestrict b) = b :=
  RingEquiv.symm_apply_apply (RingEquiv.ofBijective (algebraMap (BdRp l) (BdR l)).rangeRestrict
    ⟨fun x y h => IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l)
      (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩) b

theorem pInv_injective (l : ℕ) [Fact l.Prime] : Function.Injective (pInv l) :=
  (RingEquiv.ofBijective (algebraMap (BdRp l) (BdR l)).rangeRestrict
    ⟨fun x y h => IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l)
      (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩).symm.injective

theorem existsUnique_bdRp_of_compatible (l : ℕ) [Fact l.Prime]
    (y : ∀ m : ℕ, Bk l (m + 1)) (hy : ∀ m, dk l (m + 1) (y (m + 1)) = y m) :
    ∃! x : BdRp l, ∀ m, pk l (m + 1) x = y m := by
  haveI := isAdicComplete_span_tBdR l
  choose z hz using fun m => Ideal.Quotient.mk_surjective (y m)
  have key : ∀ (m : ℕ) (x : BdRp l), pk l (m + 1) x = y m ↔ tBdR l ^ (m + 1) ∣ x - z m := by
    intro m x
    rw [← hz m, pk, Ideal.Quotient.eq, Ideal.mem_span_singleton]
  have hstep : ∀ m, tBdR l ^ (m + 1) ∣ z (m + 1) - z m := by
    intro m
    rw [← key m]
    have := hy m
    rw [← hz (m + 1)] at this
    exact this
  obtain ⟨x, hx, hu⟩ := existsUnique_limit_of_dvd (tBdR l) z hstep
  exact ⟨x, fun m => (key m x).2 (hx m), fun x' hx' => hu x' fun m => (key m x').1 (hx' m)⟩

theorem levSys_existsUnique {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
    {M : ℕ} (h : LevHyp l K M) :
    ∀ y : ∀ m, ((levSys h).L m).B, (∀ m, (levSys h).dB m (y (m + 1)) = y m) →
      ∃! x : (per l K).P, ∀ m, ((levSys h).L m).toB x = y m := by
  intro y hy
  obtain ⟨b, hb, hu⟩ := existsUnique_bdRp_of_compatible l y hy
  refine ⟨(algebraMap (BdRp l) (BdR l)).rangeRestrict b, fun m => ?_, fun x' hx' => ?_⟩
  · change pk l (m + 1) (pInv l ((algebraMap (BdRp l) (BdR l)).rangeRestrict b)) = y m
    rw [pInv_rangeRestrict]
    exact hb m
  · refine pInv_injective l ?_
    rw [pInv_rangeRestrict]
    exact hu _ hx'

end GlobalTheory.CompanionTheory.LatC
end
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatGal

theorem map_mem_sub_of_mul {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ)
    (g : B →+* B) (s : W → W) (hs : ∀ w, g (f w) = f (s w)) (u : W) (hu : s ξ = u * ξ) :
    ∀ x ∈ sub f ξ l M, g x ∈ sub f ξ l M := by
  have hle : sub f ξ l M ≤ (sub f ξ l M).comap g := by
    refine Subring.closure_le.2 ?_
    rintro z (⟨w, rfl⟩ | ⟨i, rfl⟩)
    · show g (f w) ∈ sub f ξ l M
      rw [hs]
      exact Subring.subset_closure (Or.inl ⟨_, rfl⟩)
    · show g (dpE f ξ l M i) ∈ sub f ξ l M
      have hη : g (η f ξ l M) = f u * η f ξ l M := by
        rw [η, map_rat_smul, hs, hu, map_mul, mul_smul_comm]
      have hd : g (dpE f ξ l M i) = f u ^ i * dpE f ξ l M i := by
        rw [dpE, map_rat_smul, map_pow, hη, mul_pow, mul_smul_comm]
      rw [hd]
      have h1 : f u ∈ sub f ξ l M := Subring.subset_closure (Or.inl ⟨u, rfl⟩)
      have h2 : dpE f ξ l M i ∈ sub f ξ l M := Subring.subset_closure (Or.inr ⟨i, rfl⟩)
      exact (sub f ξ l M).mul_mem ((sub f ξ l M).pow_mem h1 i) h2
  exact fun x hx => hle hx

theorem gal_mem_sub : ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (M k : ℕ)
    (g : K.fixingSubgroup) (hT : Ideal.span {tBdR l ^ k} ≤ (Ideal.span {tBdR l ^ k}).comap (Lat.gP l g)),
    ∀ x ∈ Lat.sub (Lat.fk l k) (xi0 l) l M,
      Ideal.quotientMap _ (Lat.gP l g) hT x ∈ Lat.sub (Lat.fk l k) (xi0 l) l M := by
  intro l _ K M k g hT
  have hmem : toBot g.1 • xi0 l ∈ RingHom.ker (theta0 l) :=
    gal_smul_mem_ker_fontaineTheta (toBot g.1) (by
      rw [ker_theta0]; exact Ideal.mem_span_singleton_self _)
  rw [ker_theta0, Ideal.mem_span_singleton'] at hmem
  obtain ⟨u, hu⟩ := hmem
  refine map_mem_sub_of_mul (fk l k) (xi0 l) l M _ (fun w => toBot g.1 • w) (fun w => ?_) u hu.symm
  show Ideal.quotientMap _ (gP l g) hT (Ideal.Quotient.mk _ (wittToBDeRhamPlus (normInteger ℂ_[l]) l w)) =
    Ideal.Quotient.mk _ (wittToBDeRhamPlus (normInteger ℂ_[l]) l (toBot g.1 • w))
  rw [Ideal.quotientMap_mk, ← gal_smul_wittToBDeRhamPlus]
  rfl

end GlobalTheory.CompanionTheory.LatGal
end
end

section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatLevel

theorem dB_sigmaB {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ}
    (h : LevHyp l K M) : ∀ m g b, (levSys h).dB m (((levSys h).L (m + 1)).σB g b) =
      ((levSys h).L m).σB g ((levSys h).dB m b) := by
  intro m g b
  change Bk l (m + 1 + 1) at b
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective b
  show dk l (m + 1) (gB h (m + 1 + 1) g (Ideal.Quotient.mk _ x)) =
    gB h (m + 1) g (dk l (m + 1) (Ideal.Quotient.mk _ x))
  simp only [gB, dk, Ideal.quotientMap_mk, Ideal.Quotient.factor_mk]

end GlobalTheory.CompanionTheory.LatLevel
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatC

section Gen
variable {W B W' B' : Type} [CommRing W] [CommRing B] [Algebra ℚ B] [CommRing W'] [CommRing B'] [Algebra ℚ B']
  (f : W →+* B) (ξ : W) (f' : W' →+* B') (ξ' : W') (l M : ℕ)

theorem map_isDPMorphism (g : B →+* B') (h : ∀ x ∈ Lat.sub f ξ l M, g x ∈ Lat.sub f' ξ' l M)
    (hg : g (f ξ) = f' ξ')
    (hc : DPClosed (Lat.ι f ξ l M) (Lat.γB f ξ)) (hc' : DPClosed (Lat.ι f' ξ' l M) (Lat.γB f' ξ')) :
    IsDPMorphism (Lat.γ f ξ l M hc) (Lat.γ f' ξ' l M hc') (Lat.map f ξ f' ξ' l M g h) := by
  have hIB : ∀ x ∈ Lat.IB f ξ, g x ∈ Lat.IB f' ξ' := by
    intro x hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    rw [map_mul, hg]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  refine ⟨?_, ?_⟩
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    show Lat.ι f' ξ' l M (Lat.map f ξ f' ξ' l M g h a) ∈ Lat.IB f' ξ'
    rw [Lat.ι_map]
    exact hIB _ ha
  · intro n a ha
    have ha' : Lat.ι f ξ l M a ∈ Lat.IB f ξ := ha
    have hb : Lat.map f ξ f' ξ' l M g h a ∈ Lat.I f' ξ' l M := by
      show Lat.ι f' ξ' l M (Lat.map f ξ f' ξ' l M g h a) ∈ Lat.IB f' ξ'
      rw [Lat.ι_map]
      exact hIB _ ha'
    apply Lat.ι_injective f' ξ' l M
    rw [Lat.ι_γ _ _ _ _ _ hb, Lat.ι_map, Lat.ι_map, Lat.ι_γ _ _ _ _ _ ha, DividedPowers.RatAlgebra.dpow_eq_inv_fact_smul _ _ ha',
      DividedPowers.RatAlgebra.dpow_eq_inv_fact_smul _ _ (hIB _ ha'), map_rat_smul, map_pow]

end Gen

variable {l : ℕ} [Fact l.Prime]

theorem dk_fk (k : ℕ) (w : Ainf l) : dk l k (fk l (k + 1) w) = fk l k w := by
  rfl

theorem levSys_ddp {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (m : ℕ) :
    IsDPMorphism ((levSys h).L (m + 1)).γ ((levSys h).L m).γ ((levSys h).dA m) := by
  exact map_isDPMorphism (fk l (m + 2)) (xi0 l) (fk l (m + 1)) (xi0 l) l M (dk l (m + 1))
    (fun x hx => h.dIn (m + 1) x hx) (dk_fk (m + 1) (xi0 l)) (h.hc (m + 2)) (h.hc (m + 1))

end GlobalTheory.CompanionTheory.LatC
end
end

section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatC

theorem toB_on_K : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), ∀ (a : K) (y : (per l K).P), (y : (per l K).B) = (per l K).o a → (lev h k).toB y = algebraMap K (lev h k).B a := by
  intro l _ K M h k a y hy
  have hinj : Function.Injective (algebraMap (BdRp l) (BdR l)) := fun x y h =>
    IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l) h
  have key : pInv l y = kP l K a := by
    apply hinj
    have h1 : algebraMap (BdRp l) (BdR l) (pInv l y) = y.1 := by
      have := (RingEquiv.ofBijective (algebraMap (BdRp l) (BdR l)).rangeRestrict
        ⟨fun x y h => IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l) (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩).apply_symm_apply y
      exact congrArg Subtype.val this
    rw [h1]
    exact hy
  show pk l k (pInv l y) = pk l k (kP l K a)
  rw [key]

end GlobalTheory.CompanionTheory.LatC
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatC

theorem pInv_algebraMap (l : ℕ) [Fact l.Prime] (b : BdRp l) (hb : algebraMap (BdRp l) (BdR l) b ∈ (algebraMap (BdRp l) (BdR l)).range) :
    pInv l ⟨algebraMap (BdRp l) (BdR l) b, hb⟩ = b := by
  have : (⟨algebraMap (BdRp l) (BdR l) b, hb⟩ : ↥(algebraMap (BdRp l) (BdR l)).range) = (algebraMap (BdRp l) (BdR l)).rangeRestrict b := rfl
  rw [this]
  exact (RingEquiv.ofBijective (algebraMap (BdRp l) (BdR l)).rangeRestrict
    ⟨fun x y h => IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l) (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩).symm_apply_apply b

theorem sigmaB_toB {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ) :
    ∀ (g : K.fixingSubgroup) (x y : (per l K).P), (per l K).σ g x = y →
      (lev h k).σB g ((lev h k).toB x) = (lev h k).toB y := by
  rintro g ⟨_, b, rfl⟩ ⟨y, hy⟩ hxy
  have hy' : y = algebraMap (BdRp l) (BdR l) (gP l g b) := by
    refine (Eq.trans hxy.symm ?_)
    exact galBdRField_algebraMap (toBot g.1) b
  subst hy'
  show gB h k g (pk l k (pInv l ⟨_, _⟩)) = pk l k (pInv l ⟨_, _⟩)
  rw [pInv_algebraMap, pInv_algebraMap]
  rfl

end GlobalTheory.CompanionTheory.LatC
end
end

section

set_option autoImplicit false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatGal

private theorem galBdRHom_mem_maximalIdeal {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) (x : BDeRhamPlus (normInteger ℂ_[p]) p)
    (hx : x ∈ IsLocalRing.maximalIdeal (BDeRhamPlus (normInteger ℂ_[p]) p)) :
    galBdRHom σ x ∈ IsLocalRing.maximalIdeal (BDeRhamPlus (normInteger ℂ_[p]) p) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
  intro hu
  apply hx
  have h1 : galBdRHom σ⁻¹ (galBdRHom σ x) = x := by
    rw [← RingHom.comp_apply, ← galBdRHom_mul, inv_mul_cancel, galBdRHom_one, RingHom.id_apply]
  rw [← h1]
  exact hu.map _

theorem span_tBdR_pow_le_comap (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l))
    (k : ℕ) (g : K.fixingSubgroup) :
    Ideal.span {tBdR l ^ k} ≤ (Ideal.span {tBdR l ^ k}).comap (Lat.gP l g) := by
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]
  have ht : Lat.gP l g (tBdR l) ∈ Ideal.span {tBdR l} := by
    rw [← maximalIdeal_eq_span_tBdR]
    exact galBdRHom_mem_maximalIdeal _ _ (by rw [maximalIdeal_eq_span_tBdR]; exact Ideal.mem_span_singleton_self _)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp ht
  rw [← hc, mul_pow]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

end GlobalTheory.CompanionTheory.LatGal
end
end

section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatC

theorem sigmaB_fixes_K {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ}
    (h : LevHyp l K M) (k : ℕ) : ∀ g (a : K),
    (lev h k).σB g (algebraMap K (lev h k).B a) = algebraMap K (lev h k).B a := by
  intro g a
  have key : gP l g (kP l K a) = kP l K a := by
    have h1 : galBdRHom (toBot g.1) (algClToBdR l (a : PadicAlgCl l))
        = algClToBdR l ((toBot g.1) (a : PadicAlgCl l)) :=
      gal_smul_algClToBdR (toBot g.1) (a : PadicAlgCl l)
    have h2 : (toBot g.1) (a : PadicAlgCl l) = (a : PadicAlgCl l) := g.2 a
    rw [h2] at h1
    exact h1
  change gB h k g (pk l k (kP l K a)) = pk l k (kP l K a)
  change Ideal.quotientMap _ (gP l g) (h.galT k g) (Ideal.Quotient.mk _ (kP l K a)) = Ideal.Quotient.mk _ (kP l K a)
  rw [Ideal.quotientMap_mk, key]

end GlobalTheory.CompanionTheory.LatC
end

end

section

@[expose] public section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

theorem _root_.GlobalTheory.T.level_galois_fixes_field : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), ∀ g (a : K), (lev h k).σB g (algebraMap K (lev h k).B a) = algebraMap K (lev h k).B a := by
  first | exact @GlobalTheory.CompanionTheory.LatC.sigmaB_fixes_K | exact GlobalTheory.CompanionTheory.LatC.sigmaB_fixes_K | (intros; apply GlobalTheory.CompanionTheory.LatC.sigmaB_fixes_K <;> assumption)

end
end

section

@[expose] public section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

theorem _root_.GlobalTheory.T.level_system_transition_galois_B : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M), ∀ m g b, (levSys h).dB m (((levSys h).L (m + 1)).σB g b) = ((levSys h).L m).σB g ((levSys h).dB m b) := by
  first | exact @GlobalTheory.CompanionTheory.LatLevel.dB_sigmaB | exact GlobalTheory.CompanionTheory.LatLevel.dB_sigmaB | (intros; apply GlobalTheory.CompanionTheory.LatLevel.dB_sigmaB <;> assumption)

end
end

section

@[expose] public section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

theorem _root_.GlobalTheory.T.level_system_transition_isDPMorphism : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M), ∀ m, IsDPMorphism ((levSys h).L (m + 1)).γ ((levSys h).L m).γ ((levSys h).dA m) := by
  first | exact @GlobalTheory.CompanionTheory.LatC.levSys_ddp | exact GlobalTheory.CompanionTheory.LatC.levSys_ddp | (intros; apply GlobalTheory.CompanionTheory.LatC.levSys_ddp <;> assumption)

end
end

section

@[expose] public section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

theorem _root_.GlobalTheory.T.level_toB_algebraMap_field : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), ∀ (a : K) (y : (per l K).P), (y : (per l K).B) = (per l K).o a → (lev h k).toB y = algebraMap K (lev h k).B a := by
  first | exact @GlobalTheory.CompanionTheory.LatC.toB_on_K | exact GlobalTheory.CompanionTheory.LatC.toB_on_K | (intros; apply GlobalTheory.CompanionTheory.LatC.toB_on_K <;> assumption)

end
end

section

@[expose] public section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

theorem _root_.GlobalTheory.T.level_toB_galois_equivariant : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), ∀ (g : K.fixingSubgroup) (x y : (per l K).P), (per l K).σ g x = y → (lev h k).σB g ((lev h k).toB x) = (lev h k).toB y := by
  first | exact @GlobalTheory.CompanionTheory.LatC.sigmaB_toB | exact GlobalTheory.CompanionTheory.LatC.sigmaB_toB | (intros; apply GlobalTheory.CompanionTheory.LatC.sigmaB_toB <;> assumption)

end
end
