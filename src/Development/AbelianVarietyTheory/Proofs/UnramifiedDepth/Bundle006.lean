module

public import Mathlib.Basic.NNReal.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Discriminant
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.Valuation.Integers
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.Valuation.Basic
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle001
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.Integral
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
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.DualLattices.Bundle001

@[expose] public section

section

open scoped TensorProduct

namespace GlobalTheory.SplittingIdempotents

open GlobalTheory.EigenSplit

private theorem exists_eq_of_isSplitting {A R ι : Type} [CommRing A] [CommRing R] [IsDomain R]
    [Fintype ι] {σ : ι → A →+* R} (h : IsSplitting σ) (χ : A →+* R) : ∃ i, σ i = χ := by
  classical
  let F : R ⊗[ℤ] A →ₐ[R] (Unit → R) := splitMap (fun _ : Unit => χ)
  have h1 : ∑ i, F (idem h i) () = 1 := by

    rw [← Finset.sum_apply, ← map_sum, (completeOrthogonalIdempotents_idem h).complete, map_one]
    rfl
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (h1 ▸ one_ne_zero :
    ∑ i, F (idem h i) () ≠ 0)
  refine ⟨i, RingHom.ext fun a => ?_⟩
  have h2 := congrArg (fun t => F t ()) (one_tmul_mul_idem h i a)
  simp only [map_mul, map_smul, Pi.mul_apply, Pi.smul_apply, smul_eq_mul] at h2
  have h3 : F (1 ⊗ₜ a) () = χ a := by simp [F]
  rw [h3] at h2
  exact (mul_right_cancel₀ hi h2).symm

private theorem exists_det_sq (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE]
    [Module.Free ℤ OE] [Module.Finite ℤ OE] [DecidableEq (Module.Free.ChooseBasisIndex ℤ OE)]
    (K : Type) [Field K] [CharZero K] [Algebra OE K] [IsFractionRing OE K]
    (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal)
    (R : Type) [CommRing R] [Algebra R C] (hv : v.Integers R) :
    ∃ σ : Module.Free.ChooseBasisIndex ℤ OE → OE →+* R,
      ((Algebra.discr ℤ (Module.Free.chooseBasis ℤ OE) : ℤ) : R) =
        (Matrix.of fun i j => σ i (Module.Free.chooseBasis ℤ OE j)).det ^ 2 := by
  have : IsScalarTower ℤ OE K := AddCommGroup.intIsScalarTower
  have : IsLocalization (Algebra.algebraMapSubmonoid OE (nonZeroDivisors ℤ)) K := inferInstance
  set b := Module.Free.chooseBasis ℤ OE with hb
  let bK := b.localizationLocalization ℚ (nonZeroDivisors ℤ) K
  have : Module.Finite ℚ K := Module.Finite.of_basis bK
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ OE) = Fintype.card (K →ₐ[ℚ] C) := by
    rw [AlgHom.card, Module.finrank_eq_card_basis bK]
  let e := Fintype.equivOfCardEq hcard
  have h1 := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ C bK e
  rw [Algebra.discr_localizationLocalization] at h1
  have hent : ∀ j a, ∃ r : R, algebraMap R C r = e j (algebraMap OE K a) := by
    intro j a
    apply hv.exists_of_le_one
    apply hv.mem_of_integral
    have : IsIntegral ℤ (e j (algebraMap OE K a)) :=
      (Algebra.IsIntegral.isIntegral (R := ℤ) a).map
        ((e j).toRingHom.comp (algebraMap OE K)).toIntAlgHom
    exact this.tower_top
  choose N hN using hent
  let σ : Module.Free.ChooseBasisIndex ℤ OE → OE →+* R := fun j =>
    { toFun := N j
      map_one' := hv.hom_inj (by simp [hN])
      map_mul' := fun x y => hv.hom_inj (by simp [hN])
      map_zero' := hv.hom_inj (by simp [hN])
      map_add' := fun x y => hv.hom_inj (by simp [hN]) }
  refine ⟨σ, ?_⟩
  have hM : Algebra.embeddingsMatrixReindex ℚ C bK e =
      (algebraMap R C).mapMatrix (Matrix.of fun i j => σ i (b j)).transpose := by
    ext i j
    simp [Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix, hN, bK, σ]
  rw [hM, ← RingHom.map_det, ← map_pow, Matrix.det_transpose] at h1
  apply hv.hom_inj
  rw [← h1]
  simp

private theorem exists_isSplitting (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C]
    [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C]
    (hv : v.Integers O) (hp : ¬IsUnit (p : O)) [IsLocalRing O] (OE : Type) [CommRing OE]
    [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE]
    (hd : ¬ ((p : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ OE))) :
    ∃ σ : Module.Free.ChooseBasisIndex ℤ OE → OE →+* O, IsSplitting σ := by
  classical
  obtain ⟨σ, hσ⟩ := exists_det_sq OE (FractionRing OE) C v O hv
  refine ⟨σ, (isSplitting_iff_isUnit_det σ (Module.Free.chooseBasis ℤ OE)).2 ?_⟩
  by_contra hdet
  have hdm : ((Algebra.discr ℤ (Module.Free.chooseBasis ℤ OE) : ℤ) : O) ∈
      IsLocalRing.maximalIdeal O := by
    rw [hσ]
    exact Ideal.pow_mem_of_mem _ (by exact hdet) 2 (by norm_num)
  have hpm : (p : O) ∈ IsLocalRing.maximalIdeal O := hp
  have hcop : IsCoprime (p : ℤ) (Algebra.discr ℤ (Module.Free.chooseBasis ℤ OE)) :=
    (Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.1 Fact.out)).2 hd
  obtain ⟨a, b, hab⟩ := hcop
  have h1 : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
    have := congrArg (Int.cast : ℤ → O) hab
    push_cast at this
    rw [← this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hpm) (Ideal.mul_mem_left _ _ hdm)
  exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).mpr h1)

theorem exists_splitting_idempotents_frobenius : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsLocalRing O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE], ¬ ((p : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ OE)) → ∃ (m : ℕ) (τ : Fin m ≃ (OE →+* O)) (ε : Fin m → O ⊗[ℤ] OE) (φ : Equiv.Perm (Fin m)), CompleteOrthogonalIdempotents ε ∧ (∀ i a, (1 ⊗ₜ[ℤ] a) * ε i = τ i a • ε i) ∧ (∀ i j, i ≠ j → ∃ a, IsUnit (τ i a - τ j a)) ∧ ∀ i a, τ (φ i) a - τ i a ^ p ∈ IsLocalRing.maximalIdeal O := by
  intro p _ C _ _ _ v O _ _ hv hp _ _ OE _ _ _ _ _ hd
  classical
  obtain ⟨σ, hσ⟩ := exists_isSplitting p C v O hv hp.out OE hd
  have : IsDomain O := hv.hom_inj.isDomain
  let ι := Module.Free.ChooseBasisIndex ℤ OE
  let k := IsLocalRing.ResidueField O
  let r : O →+* k := IsLocalRing.residue O
  have hσk : IsSplitting (fun i => r.comp (σ i)) := hσ.map r
  have hinj := hσk.injective
  have hpk : (p : k) = 0 := by
    rw [← map_natCast r]
    exact (IsLocalRing.residue_eq_zero_iff _).2 hp.out
  have : CharP k p := (CharP.charP_iff_prime_eq_zero Fact.out).2 hpk
  have hbij : Function.Bijective σ :=
    ⟨hσ.injective, fun χ => exists_eq_of_isSplitting hσ χ⟩
  choose f hf using fun i => exists_eq_of_isSplitting hσk ((frobenius k p).comp (r.comp (σ i)))
  have hfi : Function.Injective f := by
    intro i j hij
    apply hinj
    ext a
    apply frobenius_inj k p
    have h1 := DFunLike.congr_fun (hf i) a
    have h2 := DFunLike.congr_fun (hf j) a
    rw [hij] at h1
    exact h1.symm.trans h2
  let φ : Equiv.Perm ι := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hfi)
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  refine ⟨Fintype.card ι, e.trans (Equiv.ofBijective σ hbij), idem hσ ∘ e,
    (e.trans φ).trans e.symm, ?_, fun i a => ?_, fun i j hij => ?_, fun i a => ?_⟩
  · exact (CompleteOrthogonalIdempotents.equiv e).2 (completeOrthogonalIdempotents_idem hσ)
  · exact one_tmul_mul_idem hσ (e i) a
  · by_contra hne
    push Not at hne
    apply hij
    apply e.injective
    apply hinj
    ext a
    exact Ideal.Quotient.eq.2 (hne a)
  · have h1 := DFunLike.congr_fun (hf (e i)) a
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.ofBijective_apply, φ]
    apply Ideal.Quotient.eq.1
    change r _ = r _
    rw [map_pow]
    exact h1

end GlobalTheory.SplittingIdempotents
end

section

open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField

namespace GlobalTheory.SatBlocks

def intRing {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) : Subring C where
  carrier := {z | (0 : WithTop ℝ) ≤ v z}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [v.map_mul]; exact add_nonneg ha hb
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    exact v.map_le_add ha hb
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    rwa [v.map_neg]

theorem mem_intRing {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) (z : C) :
    z ∈ intRing v ↔ ((0 : ℝ) : WithTop ℝ) ≤ v z := Iff.rfl

theorem ne_zero_of_val_zero {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {z : C}
    (h : v z = 0) : z ≠ 0 := by
  rintro rfl
  simp at h

theorem inv_mem_of_val_zero {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {z : C}
    (h : v z = 0) : z⁻¹ ∈ intRing v := by
  have h1 : v (z * z⁻¹) = 0 := by rw [mul_inv_cancel₀ (ne_zero_of_val_zero v h)]; simp
  rw [v.map_mul, h, zero_add] at h1
  exact h1.ge

theorem exists_projector {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {O A : Type}
    [DecidableEq A] {n : A → ℕ} {d : ℕ} (M : O → Matrix (Fin d) (Fin d) C) (em : A → O → C)
    (u : (Σ a : A, Fin (n a)) → Fin d → C)
    (hM : ∀ x i j, M x i j ∈ intRing v) (he : ∀ a x, em a x ∈ intRing v)
    (hu : ∀ x q, (M x).mulVec (u q) = em q.1 x • u q)
    (hs : ∀ a a', a ≠ a' → ∃ x, v (em a x - em a' x) = 0) (a : A) (S : Finset A) (ha : a ∉ S) :
    ∃ (P : Matrix (Fin d) (Fin d) C) (c : A → C), (∀ i j, P i j ∈ intRing v) ∧
      (∀ q, P.mulVec (u q) = c q.1 • u q) ∧ c a = 1 ∧ ∀ b ∈ S, c b = 0 := by
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨1, fun _ => 1, ?_, by simp, rfl, by simp⟩
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  | insert b S hb ih =>
    rw [Finset.mem_insert, not_or] at ha
    obtain ⟨P, c, hP, hPu, hca, hcS⟩ := ih ha.2
    obtain ⟨x, hx⟩ := hs a b ha.1
    refine ⟨((em a x - em b x)⁻¹ • (M x - em b x • (1 : Matrix (Fin d) (Fin d) C))) * P,
      fun e => (em a x - em b x)⁻¹ * (em e x - em b x) * c e, ?_, ?_, ?_, ?_⟩
    · intro i j
      rw [Matrix.mul_apply]
      refine sum_mem fun k _ => mul_mem ?_ (hP k j)
      simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
      refine mul_mem (inv_mem_of_val_zero v hx) (sub_mem (hM x i k) (mul_mem (he b x) ?_))
      rw [Matrix.one_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    · intro q
      rw [← Matrix.mulVec_mulVec, hPu, Matrix.mulVec_smul, Matrix.smul_mulVec, Matrix.sub_mulVec,
        Matrix.smul_mulVec, Matrix.one_mulVec, hu]
      ext k
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      ring
    · simp only [hca, mul_one]
      exact inv_mul_cancel₀ (ne_zero_of_val_zero v hx)
    · intro e he'
      rcases Finset.mem_insert.1 he' with rfl | h
      · simp
      · simp [hcS e h]

theorem saturated_blocks_summand : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (O A : Type) [Fintype A] [DecidableEq A] (n : A → ℕ) (d : ℕ) (M : O → Matrix (Fin d) (Fin d) C) (em : A → O → C) (u : (Σ a : A, Fin (n a)) → Fin d → C), (∀ x i j, ((0 : ℝ) : WithTop ℝ) ≤ v (M x i j)) → (∀ a x, ((0 : ℝ) : WithTop ℝ) ≤ v (em a x)) → (∀ x q, (M x).mulVec (u q) = em q.1 x • u q) → (∀ a a', a ≠ a' → ∃ x, v (em a x - em a' x) = 0) → (∀ a, ∃ w : Fin d → Fin (n a) → C, (∀ s i, ((0 : ℝ) : WithTop ℝ) ≤ v (w s i)) ∧ ∀ i i', ∑ s, u ⟨a, i⟩ s * w s i' = if i = i' then 1 else 0) → ∃ w : Fin d → (Σ a : A, Fin (n a)) → C, (∀ s q, ((0 : ℝ) : WithTop ℝ) ≤ v (w s q)) ∧ ∀ q q', ∑ s, u q s * w s q' = if q = q' then 1 else 0 := by
  intro C _ v O A _ _ n d M em u hM he hu hs hw
  choose w hwi hw using hw
  have key := fun a : A => exists_projector v M em u hM he hu hs a (Finset.univ.erase a)
    (Finset.notMem_erase a _)
  choose P c hP hPu hca hcS using key
  refine ⟨fun s q => ∑ t, P q.1 t s * w q.1 t q.2, ?_, ?_⟩
  · intro s q
    exact (mem_intRing v _).1
      (sum_mem fun t _ => mul_mem (hP _ _ _) ((mem_intRing v _).2 (hwi _ _ _)))
  · rintro ⟨b, j⟩ ⟨a, i⟩
    have h1 : ∑ s, u ⟨b, j⟩ s * ∑ t, P a t s * w a t i
        = ∑ t, (P a).mulVec (u ⟨b, j⟩) t * w a t i := by
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => by ring
    dsimp only
    rw [h1, hPu]
    by_cases hba : b = a
    · subst hba
      simp only [hca, one_smul, hw]
      simp
    · have h0 : c a b = 0 := hcS a b (by simp [hba])
      rw [if_neg (fun h => hba (congrArg Sigma.fst h))]
      simp [h0]

end GlobalTheory.SatBlocks
end

section

open ReciprocityTheory.PGsh

namespace GlobalTheory

theorem psWeight_mul {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {σ : Type}
    [DecidableEq σ] (ρ : σ → ℝ) (g g' : MvPowerSeries σ C) (r r' : ℝ)
    (h : ∀ α, (((r) - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ)
      ≤ v (MvPowerSeries.coeff α g))
    (h' : ∀ α, (((r') - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ)
      ≤ v (MvPowerSeries.coeff α g')) :
    ∀ α, (((r + r') - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ)
      ≤ v (MvPowerSeries.coeff α (g * g')) := by
  intro α
  rw [MvPowerSeries.coeff_mul]
  refine AddValuation.map_le_sum v ?_
  intro p hp
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [AddValuation.map_mul]
  have hs : α.sum (fun j e => ρ j * (e : ℝ)) =
      p.1.sum (fun j e => ρ j * (e : ℝ)) + p.2.sum (fun j e => ρ j * (e : ℝ)) := by
    rw [← hp]
    exact Finsupp.sum_add_index' (fun j => by simp) (fun j a b => by push_cast; ring)
  calc (((r + r') - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ)
      = (((r - p.1.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ)
        + ((r' - p.2.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ)) := by
        rw [← WithTop.coe_add, hs]
        congr 1
        ring
    _ ≤ v (MvPowerSeries.coeff p.1 g) + v (MvPowerSeries.coeff p.2 g') :=
        add_le_add (h p.1) (h' p.2)

theorem psWeight_add {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {σ : Type}
    (ρ : σ → ℝ) (g g' : MvPowerSeries σ C) (r r' : ℝ)
    (h : ∀ α, (((r) - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ)
      ≤ v (MvPowerSeries.coeff α g))
    (h' : ∀ α, (((r') - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ)
      ≤ v (MvPowerSeries.coeff α g')) :
    ∀ α, (((min r r') - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ)
      ≤ v (MvPowerSeries.coeff α (g + g')) := by
  intro α
  have hc : MvPowerSeries.coeff α (g + g') =
      MvPowerSeries.coeff α g + MvPowerSeries.coeff α g' := map_add _ _ _
  rw [hc]
  refine AddValuation.map_le_add v ?_ ?_
  · exact le_trans (WithTop.coe_le_coe.mpr (sub_le_sub_right (min_le_left r r') _)) (h α)
  · exact le_trans (WithTop.coe_le_coe.mpr (sub_le_sub_right (min_le_right r r') _)) (h' α)

theorem psWeight_pow {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {σ : Type}
    [DecidableEq σ] (ρ : σ → ℝ) (g : MvPowerSeries σ C) (r : ℝ)
    (h : ∀ α, (((r) - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ)
      ≤ v (MvPowerSeries.coeff α g)) (N : ℕ) :
    ∀ α, (((N * r) - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ)
      ≤ v (MvPowerSeries.coeff α (g ^ N)) := by
  induction N with
  | zero =>
    intro α
    rw [pow_zero, MvPowerSeries.coeff_one]
    split_ifs with hα
    · subst hα
      simp
    · rw [AddValuation.map_zero]
      exact le_top
  | succ n ih =>
    intro α
    rw [pow_succ]
    have e : ((n + 1 : ℕ) : ℝ) * r = n * r + r := by push_cast; ring
    rw [e]
    exact psWeight_mul v ρ (g ^ n) g (n * r) r ih h α

theorem psWeight_calculus :
  (∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (σ : Type) [Fintype σ] [DecidableEq σ] (ρ : σ → ℝ) (g g' : MvPowerSeries σ C) (r r' : ℝ),
    (∀ α, (((r) - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (g))) → ((∀ α, (((r') - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (g'))) → (∀ α, (((r + r') - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (g * g'))) ∧ (∀ α, (((min r r') - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (g + g')))) ∧ ∀ N : ℕ, (∀ α, (((N * r) - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (g ^ N)))) := by
  intro C _ v σ _ _ ρ g g' r r' h
  exact ⟨fun h' => ⟨psWeight_mul v ρ g g' r r' h h', psWeight_add v ρ g g' r r' h h'⟩,
    fun N => psWeight_pow v ρ g r h N⟩

end GlobalTheory
end

section

namespace GlobalTheory.ChF

open MvPowerSeries

section

variable {R : Type*} [CommRing R] (I : Ideal R) {κ : Type*} [Finite κ]

private theorem mem_sup_pow_iff (n : ℕ) (f : MvPowerSeries κ R) :
    f ∈ (I.map (C : R →+* MvPowerSeries κ R) ⊔
      Ideal.span (Set.range (X : κ → MvPowerSeries κ R))) ^ n ↔
      ∀ e : κ →₀ ℕ, coeff e f ∈ I ^ (n - e.degree) := by
  first
  | exact @_root_.GlobalTheory.IdealPowerCoefficients.mem_pow_iff_coeff_mem
  | exact _root_.GlobalTheory.IdealPowerCoefficients.mem_pow_iff_coeff_mem
  | (apply _root_.GlobalTheory.IdealPowerCoefficients.mem_pow_iff_coeff_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.IdealPowerCoefficients.mem_pow_iff_coeff_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IdealPowerCoefficients.mem_pow_iff_coeff_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IdealPowerCoefficients.mem_pow_iff_coeff_mem ..)

private theorem smodEq_pow_iff {S : Type*} [CommRing S] (J : Ideal S) (n : ℕ) (x y : S) :
    x ≡ y [SMOD (J ^ n • ⊤ : Submodule S S)] ↔ x - y ∈ J ^ n := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]

private theorem isAdicComplete_sup (hI : IsAdicComplete I R) :
    IsAdicComplete (I.map (C : R →+* MvPowerSeries κ R) ⊔
      Ideal.span (Set.range (X : κ → MvPowerSeries κ R))) (MvPowerSeries κ R) := by
  have hH : IsHausdorff (I.map (C : R →+* MvPowerSeries κ R) ⊔
      Ideal.span (Set.range (X : κ → MvPowerSeries κ R))) (MvPowerSeries κ R) := by
    refine ⟨fun x hx => ?_⟩
    ext e
    refine hI.toIsHausdorff.haus _ fun n => ?_
    have := (mem_sup_pow_iff I _ _).1 ((smodEq_pow_iff _ _ _ _).1 (hx (n + e.degree))) e
    rw [smodEq_pow_iff]
    simpa using this
  have hP : IsPrecomplete (I.map (C : R →+* MvPowerSeries κ R) ⊔
      Ideal.span (Set.range (X : κ → MvPowerSeries κ R))) (MvPowerSeries κ R) := by
    refine ⟨fun f hf => ?_⟩
    have hf' : ∀ {m n : ℕ}, m ≤ n → ∀ e : κ →₀ ℕ,
        coeff e (f m) - coeff e (f n) ∈ I ^ (m - e.degree) := fun h e => by
      have := (mem_sup_pow_iff I _ _).1 ((smodEq_pow_iff _ _ _ _).1 (hf h)) e
      rwa [map_sub] at this
    have hL : ∀ e : κ →₀ ℕ, ∃ L : R, ∀ n,
        coeff e (f (n + e.degree)) ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)] := fun e =>
      hI.toIsPrecomplete.prec (f := fun n => coeff e (f (n + e.degree))) fun {m n} h => by
        rw [smodEq_pow_iff]
        simpa using hf' (Nat.add_le_add_right h e.degree) e
    choose L hL using hL
    refine ⟨L, fun n => ?_⟩
    refine (smodEq_pow_iff _ _ _ _).2 ((mem_sup_pow_iff I _ _).2 fun e => ?_)
    have h1 := (smodEq_pow_iff _ _ _ _).1 (hL e (n - e.degree))
    have h2 := hf' (show n ≤ n - e.degree + e.degree by omega) e
    have h3 := add_mem h2 h1
    rw [sub_add_sub_cancel] at h3
    exact h3
  exact IsAdicComplete.mk

end

theorem mem_sup_span_X_pow_iff_and_isAdicComplete : ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : Type) [Finite κ], (∀ (n : ℕ) (f : MvPowerSeries κ R), f ∈ (I.map (MvPowerSeries.C : R →+* MvPowerSeries κ R) ⊔ Ideal.span (Set.range (MvPowerSeries.X : κ → MvPowerSeries κ R))) ^ n ↔ ∀ e : κ →₀ ℕ, MvPowerSeries.coeff e f ∈ I ^ (n - e.degree)) ∧ (IsAdicComplete I R → IsAdicComplete (I.map (MvPowerSeries.C : R →+* MvPowerSeries κ R) ⊔ Ideal.span (Set.range (MvPowerSeries.X : κ → MvPowerSeries κ R))) (MvPowerSeries κ R)) :=
  fun _ _ I _ _ => ⟨mem_sup_pow_iff I, isAdicComplete_sup I⟩

end GlobalTheory.ChF
end
