module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
public import ReciprocityTheory.DualLattices.FormalChartAtZero
public import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
public import Mathlib.RingTheory.Noetherian.Nilpotent
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2

namespace GlobalTheory

private lemma chartFirstOrder_mem_span {S : Type} [CommRing S] {g : ℕ} (a : Fin g → S)
    (x : TrivSqZeroExt S (Fin g → S))
    (hx : x ∈ Ideal.span (Set.range fun i => (TrivSqZeroExt.inl (a i) : TrivSqZeroExt S (Fin g → S)))) :
    x.fst ∈ Ideal.span (Set.range a) ∧ ∀ j, x.snd j ∈ Ideal.span (Set.range a) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact ⟨Ideal.subset_span ⟨i, rfl⟩, fun j => by simp⟩
  | zero => exact ⟨by simp, fun j => by simp⟩
  | add y z _ _ hy hz =>
    exact ⟨by simpa using add_mem hy.1 hz.1, fun j => by simpa using add_mem (hy.2 j) (hz.2 j)⟩
  | smul r y _ hy =>
    refine ⟨?_, fun j => ?_⟩
    · rw [smul_eq_mul, TrivSqZeroExt.fst_mul]
      exact Ideal.mul_mem_left _ _ hy.1
    · rw [smul_eq_mul, TrivSqZeroExt.snd_mul]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
        MulOpposite.unop_op]
      exact add_mem (Ideal.mul_mem_left _ _ (hy.2 j)) (Ideal.mul_mem_left _ _ hy.1)

theorem chart_fAdd_firstOrder :
  (∀ {R₀ : Type} [CommRing R₀] {ι : Type} [Fintype ι] [DecidableEq ι] (f : MvPowerSeries ι R₀) (S : Type) [CommRing S] [Algebra R₀ S] (a : ι → S),
    (∀ N : ℕ, (∀ i, a i ^ N = 0) → nEval f a = tEval N f a) ∧
    ((∀ i, IsNilpotent (a i)) → (∀ (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S'), φ (nEval f a) = nEval f (fun i => φ (a i))) ∧
      nEval f a - algebraMap R₀ S (MvPowerSeries.coeff 0 f) ∈ Ideal.span (Set.range a))) →
  (∀ {R₀ : Type} [CommRing R₀] {g : ℕ} {B : BX R₀} {K : LAlg R₀} (ch : FormalChartAtZero B K g) (S : Type) [CommRing S] [Algebra R₀ S] (a : Fin g → S), (∀ i, IsNilpotent (a i)) →
    ∃ M : Matrix (Fin g) (Fin g) S, (∀ k j, M k j - (1 : Matrix (Fin g) (Fin g) S) k j ∈ Ideal.span (Set.range a)) ∧
      ∀ e : Fin g → S, (∀ i j, e i * e j = 0) → fAdd ch.F a e = a + M *ᵥ e) := by
  intro H R₀ _ g B K ch S _ _ a ha

  have nat : ∀ (T : Type) [CommRing T] [Algebra R₀ T] (T' : Type) [CommRing T'] [Algebra R₀ T']
      (φ : T →ₐ[R₀] T') (x y : Fin g → T), (∀ i, IsNilpotent (x i)) → (∀ i, IsNilpotent (y i)) →
      ∀ k, φ (fAdd ch.F x y k) = fAdd ch.F (fun i => φ (x i)) (fun i => φ (y i)) k := by
    intro T _ _ T' _ _ φ x y hx hy k
    have h := ((H (ch.F k) T (Sum.elim x y)).2 (by rintro (i | i); exacts [hx i, hy i])).1 T' φ
    unfold fAdd
    rw [h]
    congr 1
    funext i
    cases i <;> rfl

  let T := TrivSqZeroExt S (Fin g → S)
  let a' : Fin g → T := fun i => TrivSqZeroExt.inl (a i)
  let e' : Fin g → T := fun j => TrivSqZeroExt.inr (Pi.single j 1)
  have ha' : ∀ i, IsNilpotent (a' i) := fun i => (ha i).map (TrivSqZeroExt.inlHom S (Fin g → S))
  have he' : ∀ i, IsNilpotent (e' i) := fun i => ⟨2, by
    rw [pow_two]; exact TrivSqZeroExt.inr_mul_inr _ _ _⟩
  have hfst : ∀ k, (fAdd ch.F a' e' k).fst = a k := by
    intro k
    have h := nat T S (TrivSqZeroExt.fstHom R₀ S (Fin g → S)) a' e' ha' he' k
    have h2 := congrFun (ch.F_unit S a ha) k
    rw [← h2]
    exact h
  refine ⟨fun k j => (fAdd ch.F a' e' k).snd j, ?_, ?_⟩
  · intro k j
    let J : Ideal T := Ideal.span (Set.range a')
    have h := nat T (T ⧸ J) (Ideal.Quotient.mkₐ R₀ J) a' e' ha' he' k
    have h0 : (fun i => Ideal.Quotient.mkₐ R₀ J (a' i)) = 0 := by
      funext i
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨i, rfl⟩)
    have hn : ∀ i, IsNilpotent (Ideal.Quotient.mkₐ R₀ J (e' i)) := fun i => (he' i).map _
    rw [h0, ch.F_comm _ 0 _ (fun _ => IsNilpotent.zero) hn, ch.F_unit _ _ hn] at h
    have hm : fAdd ch.F a' e' k - e' k ∈ J := Ideal.Quotient.eq.1 h
    have := (chartFirstOrder_mem_span a _ hm).2 j
    rw [TrivSqZeroExt.snd_sub] at this
    have h1 : (1 : Matrix (Fin g) (Fin g) S) k j = (e' k).snd j := by
      simp only [e', TrivSqZeroExt.snd_inr, Matrix.one_apply, Pi.single_apply, eq_comm]
    rw [h1]
    exact this
  · intro e he
    let l : (Fin g → S) →ₗ[R₀] S :=
      { toFun := fun v => v ⬝ᵥ e
        map_add' := fun v w => add_dotProduct _ _ _
        map_smul' := fun r v => smul_dotProduct _ _ _ }
    have hl : ∀ v, l v = v ⬝ᵥ e := fun _ => rfl
    let φ : T →ₐ[R₀] S := TrivSqZeroExt.lift (AlgHom.id R₀ S) l
      (fun v w => by
        simp only [hl, dotProduct, Finset.sum_mul_sum]
        refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
        rw [mul_mul_mul_comm, he, mul_zero])
      (fun r v => by simp [hl])
      (fun r v => by simp [hl, mul_comm])
    have hφ : ∀ x : T, φ x = x.fst + x.snd ⬝ᵥ e := fun _ => rfl
    funext k
    have h := nat T S φ a' e' ha' he' k
    have e1 : (fun i => φ (a' i)) = a := by
      funext i; simp [hφ, a']
    have e2 : (fun i => φ (e' i)) = e := by
      funext i; simp [hφ, e']
    rw [e1, e2, hφ, hfst] at h
    rw [← h]
    rfl

end GlobalTheory
end

section

noncomputable section

open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2

namespace GlobalTheory

section

variable {R₀ : Type} [CommRing R₀] {ι : Type} [Fintype ι] [DecidableEq ι]
  {S : Type} [CommRing S] [Algebra R₀ S]

lemma evBasic_tEval_eq_sum (N : ℕ) (f : MvPowerSeries ι R₀) (a : ι → S) :
    tEval N f a = ∑ e ∈ Fintype.piFinset (fun _ : ι => Finset.range N),
      algebraMap R₀ S (MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) f) *
        ∏ i, a i ^ e i := by
  unfold tEval
  refine Finset.sum_bij' (fun e _ => fun i => (e i : ℕ))
    (fun e he => fun i => ⟨e i, Finset.mem_range.mp (Fintype.mem_piFinset.mp he i)⟩) ?_ ?_ ?_ ?_ ?_
  · intro e _
    exact Fintype.mem_piFinset.mpr fun i => Finset.mem_range.mpr (e i).isLt
  · intro e _
    exact Finset.mem_univ _
  · intro e _
    rfl
  · intro e _
    rfl
  · intro e _
    rfl

lemma evBasic_tEval_of_le {N N' : ℕ} (hN : N ≤ N') (f : MvPowerSeries ι R₀) (a : ι → S)
    (ha : ∀ i, a i ^ N = 0) : tEval N f a = tEval N' f a := by
  rw [evBasic_tEval_eq_sum, evBasic_tEval_eq_sum]
  apply Finset.sum_subset
  · intro e he
    rw [Fintype.mem_piFinset] at he ⊢
    exact fun i => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp (he i)) hN)
  · intro e _ hne
    rw [Fintype.mem_piFinset] at hne
    push Not at hne
    obtain ⟨i, hi⟩ := hne
    rw [Finset.mem_range, not_lt] at hi
    have hz : ∏ j, a j ^ e j = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by rw [← Nat.sub_add_cancel hi, pow_add, ha i, mul_zero])
    rw [hz, mul_zero]

lemma evBasic_tEval_indep {N N' : ℕ} (f : MvPowerSeries ι R₀) (a : ι → S)
    (ha : ∀ i, a i ^ N = 0) (ha' : ∀ i, a i ^ N' = 0) : tEval N f a = tEval N' f a := by
  rcases le_total N N' with h | h
  · exact evBasic_tEval_of_le h f a ha
  · exact (evBasic_tEval_of_le h f a ha').symm

lemma evBasic_nEval_eq_tEval (f : MvPowerSeries ι R₀) (a : ι → S) (N : ℕ)
    (ha : ∀ i, a i ^ N = 0) : nEval f a = tEval N f a := by
  classical
  unfold nEval
  split_ifs with h
  · exact evBasic_tEval_indep f a (Nat.find_spec h) ha
  · exact absurd ⟨N, ha⟩ h


omit [DecidableEq ι] in
lemma evBasic_exists_pow (a : ι → S) (ha : ∀ i, IsNilpotent (a i)) :
    ∃ N : ℕ, 0 < N ∧ ∀ i, a i ^ N = 0 := by
  have ha' : ∀ i, ∃ m : ℕ, a i ^ m = 0 := ha
  choose n hn using ha'
  refine ⟨(∑ i, n i) + 1, Nat.succ_pos _, fun i => pow_eq_zero_of_le ?_ (hn i)⟩
  exact (Finset.single_le_sum (fun j _ => Nat.zero_le (n j)) (Finset.mem_univ i)).trans (Nat.le_succ _)

lemma evBasic_map_tEval {S' : Type} [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S') (N : ℕ)
    (f : MvPowerSeries ι R₀) (a : ι → S) :
    φ (tEval N f a) = tEval N f (fun i => φ (a i)) := by
  unfold tEval

  simp only [map_sum, map_mul, map_prod, map_pow, AlgHom.commutes]

lemma evBasic_map_nEval {S' : Type} [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S')
    (f : MvPowerSeries ι R₀) (a : ι → S) (ha : ∀ i, IsNilpotent (a i)) :
    φ (nEval f a) = nEval f (fun i => φ (a i)) := by
  obtain ⟨N, -, hN⟩ := evBasic_exists_pow a ha
  have hN' : ∀ i, φ (a i) ^ N = 0 := fun i => by rw [← map_pow, hN i, map_zero]
  rw [evBasic_nEval_eq_tEval f a N hN, evBasic_nEval_eq_tEval f _ N hN', evBasic_map_tEval]

lemma evBasic_nEval_sub_coeff_mem (f : MvPowerSeries ι R₀) (a : ι → S)
    (ha : ∀ i, IsNilpotent (a i)) :
    nEval f a - algebraMap R₀ S (MvPowerSeries.coeff 0 f) ∈ Ideal.span (Set.range a) := by
  obtain ⟨N, hNpos, hN⟩ := evBasic_exists_pow a ha
  rw [evBasic_nEval_eq_tEval f a N hN, evBasic_tEval_eq_sum]
  have h0 : (0 : ι → ℕ) ∈ Fintype.piFinset (fun _ : ι => Finset.range N) :=
    Fintype.mem_piFinset.mpr fun _ => Finset.mem_range.mpr hNpos
  rw [← Finset.add_sum_erase _ _ h0]
  have hc : algebraMap R₀ S (MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm (0 : ι → ℕ)) f) *
      ∏ i, a i ^ (0 : ι → ℕ) i = algebraMap R₀ S (MvPowerSeries.coeff 0 f) := by
    have hz : Finsupp.equivFunOnFinite.symm (0 : ι → ℕ) = 0 := by
      ext i
      rfl
    simp [hz]
  rw [hc, add_sub_cancel_left]
  refine Ideal.sum_mem _ fun e he => ?_
  obtain ⟨i, hi⟩ : ∃ i, e i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact Finset.ne_of_mem_erase he (funext hcon)
  refine Ideal.mul_mem_left _ _ ?_
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _
    (Ideal.subset_span (Set.mem_range_self i) : a i ∈ Ideal.span (Set.range a)) _ (Nat.pos_of_ne_zero hi))

end

theorem nEval_basic :
  (∀ {R₀ : Type} [CommRing R₀] {ι : Type} [Fintype ι] [DecidableEq ι] (f : MvPowerSeries ι R₀) (S : Type) [CommRing S] [Algebra R₀ S] (a : ι → S),
    (∀ N : ℕ, (∀ i, a i ^ N = 0) → nEval f a = tEval N f a) ∧
    ((∀ i, IsNilpotent (a i)) → (∀ (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S'), φ (nEval f a) = nEval f (fun i => φ (a i))) ∧
      nEval f a - algebraMap R₀ S (MvPowerSeries.coeff 0 f) ∈ Ideal.span (Set.range a))) := by
  intro R₀ _ ι _ _ f S _ _ a
  exact ⟨fun N hN => evBasic_nEval_eq_tEval f a N hN,
    fun ha => ⟨fun S' _ _ φ => evBasic_map_nEval φ f a ha, evBasic_nEval_sub_coeff_mem f a ha⟩⟩

end GlobalTheory
end
end

section

open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SmoothNilLift

theorem exists_lift_of_nil {R A W K : Type} [CommRing R] [CommRing A] [CommRing W] [CommRing K]
    [Algebra R A] [Algebra R W] [Algebra R K] [Algebra.Smooth R A] (ρ : W →ₐ[R] K)
    (hρ : Function.Surjective ρ) (hn : ∀ a ∈ RingHom.ker ρ, IsNilpotent a) (φ : A →ₐ[R] K) :
    ∃ ψ : A →ₐ[R] W, ρ.comp ψ = φ := by
  obtain ⟨n, f, hf, hker⟩ := Algebra.FinitePresentation.out (R := R) (A := A)
  choose w hw using fun i : Fin n => hρ (φ (f (MvPolynomial.X i)))
  let g : MvPolynomial (Fin n) R →ₐ[R] W := MvPolynomial.aeval w
  have hg : ρ.comp g = φ.comp f := by
    ext i
    simp [g, hw]
  have hg' : ∀ p, ρ (g p) = φ (f p) := fun p => AlgHom.congr_fun hg p
  let J : Ideal W := (RingHom.ker f.toRingHom).map g.toRingHom
  have hJ : J ≤ RingHom.ker ρ := by
    refine Ideal.map_le_iff_le_comap.mpr fun p hp => ?_
    have hp' : f p = 0 := hp
    change ρ (g p) = 0
    rw [hg', hp', map_zero]
  have hJfg : J.FG := hker.map _
  have hJn : IsNilpotent J :=
    (Ideal.FG.isNilpotent_iff_le_nilradical hJfg).mpr fun a ha => hn a (hJ ha)
  let g₀ : (MvPolynomial (Fin n) R ⧸ RingHom.ker f) →ₐ[R] W ⧸ J :=
    Ideal.Quotient.liftₐ (RingHom.ker f) ((Ideal.Quotient.mkₐ R J).comp g) fun p hp =>
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem g.toRingHom hp)
  let E := Ideal.quotientKerAlgEquivOfSurjective hf
  let ψ₀ : A →ₐ[R] W ⧸ J := g₀.comp E.symm.toAlgHom
  have hψ₀ : ∀ p, ψ₀ (f p) = Ideal.Quotient.mk J (g p) := by
    intro p
    have h1 : E.symm (f p) = Ideal.Quotient.mk _ p := by
      rw [AlgEquiv.symm_apply_eq]
      rfl
    change g₀ (E.symm (f p)) = _
    rw [h1]
    rfl
  obtain ⟨ψ, hψ⟩ := Algebra.FormallySmooth.exists_lift J hJn ψ₀
  refine ⟨ψ, AlgHom.ext fun a => ?_⟩
  obtain ⟨p, rfl⟩ := hf a
  have h2 : Ideal.Quotient.mk J (ψ (f p)) = Ideal.Quotient.mk J (g p) :=
    (AlgHom.congr_fun hψ (f p)).trans (hψ₀ p)
  have h3 : ρ (ψ (f p) - g p) = 0 := hJ (Ideal.Quotient.eq.mp h2)
  rw [map_sub, sub_eq_zero] at h3
  change ρ (ψ (f p)) = _
  rw [h3, hg']

theorem exists_point_lift {R₀ : Type} [CommRing R₀] (X : Over (Spec (CommRingCat.of R₀)))
    [Smooth X.hom] {W K : Type} [CommRing W] [CommRing K] [Algebra R₀ W] [Algebra R₀ K]
    [IsLocalRing K] (ρ : W →ₐ[R₀] K) (hρ : Function.Surjective ρ)
    (hn : ∀ a ∈ RingHom.ker ρ, IsNilpotent a) (z : sp (R₀ := R₀) K ⟶ X) :
    ∃ y : sp (R₀ := R₀) W ⟶ X, spMap ρ ≫ y = z := by
  let x : Spec (CommRingCat.of K) ⟶ X.left := z.left
  obtain ⟨_, ⟨U, hU, rfl⟩, hmem, -⟩ := X.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (x (IsLocalRing.closedPoint K))) isOpen_univ
  have hU : IsAffineOpen U := hU
  have hx : ⊤ ≤ x ⁻¹ᵁ U := fun p _ => by
    have hsp : (p : PrimeSpectrum K) ⤳ IsLocalRing.closedPoint K :=
      (PrimeSpectrum.le_iff_specializes _ _).mp
        (IsLocalRing.le_maximalIdeal (p : PrimeSpectrum K).isPrime.ne_top)
    exact hsp.mem_open (x ⁻¹ᵁ U).isOpen hmem
  let a0 : R₀ →+* Γ(X.left, U) :=
    ((Scheme.ΓSpecIso (CommRingCat.of R₀)).inv ≫ X.hom.appLE ⊤ U le_top).hom
  letI : Algebra R₀ Γ(X.left, U) := a0.toAlgebra
  have hover : hU.fromSpec ≫ X.hom = Spec.map (CommRingCat.ofHom a0) := by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec X.hom
      (isAffineOpen_top (Spec (CommRingCat.of R₀))) hU (le_top : U ≤ X.hom ⁻¹ᵁ ⊤)
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
    rw [← h, CommRingCat.ofHom_hom, Spec.map_comp]
  haveI : Algebra.Smooth R₀ Γ(X.left, U) := by
    have h1 : RingHom.Smooth (X.hom.appLE ⊤ U le_top).hom :=
      HasRingHomProperty.appLE (P := @Smooth) X.hom inferInstance
        ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of R₀))⟩ ⟨U, hU⟩ le_top
    have h2 : RingHom.Smooth (Scheme.ΓSpecIso (CommRingCat.of R₀)).inv.hom :=
      RingHom.Smooth.of_bijective
        (Scheme.ΓSpecIso (CommRingCat.of R₀)).symm.commRingCatIsoToRingEquiv.bijective
    exact h2.comp h1
  let φ := x.appLE U ⊤ hx ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom
  have hφx : Spec.map φ ≫ hU.fromSpec = x := by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec x hU
      (isAffineOpen_top (Spec (CommRingCat.of K))) hx
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
    rw [Spec.map_comp, Category.assoc, h, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id,
      Spec.map_id, Category.id_comp]
  have hφ : φ.hom.comp a0 = algebraMap R₀ K := by
    have e : Spec.map (CommRingCat.ofHom (φ.hom.comp a0)) =
        Spec.map (CommRingCat.ofHom (algebraMap R₀ K)) := by
      calc Spec.map (CommRingCat.ofHom (φ.hom.comp a0))
          = Spec.map φ ≫ Spec.map (CommRingCat.ofHom a0) := by
            rw [← Spec.map_comp]; rfl
        _ = Spec.map φ ≫ hU.fromSpec ≫ X.hom := by rw [hover]
        _ = x ≫ X.hom := by rw [← Category.assoc, hφx]
        _ = Spec.map (CommRingCat.ofHom (algebraMap R₀ K)) := Over.w z
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  let φ' : Γ(X.left, U) →ₐ[R₀] K := ⟨φ.hom, fun r => RingHom.congr_fun hφ r⟩
  obtain ⟨ψ, hψ⟩ := exists_lift_of_nil ρ hρ hn φ'
  refine ⟨Over.homMk (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ hU.fromSpec) ?_, ?_⟩
  · simp only [sp, Over.mk_hom]
    rw [Category.assoc, hover, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact ψ.comp_algebraMap
  · apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ hU.fromSpec = x
    rw [← hφx, ← Category.assoc, ← Spec.map_comp]
    congr 2
    ext a
    exact AlgHom.congr_fun hψ a

theorem main :
  (∀ {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] (B : BX R₀) (e : ∀ R : LAlg R₀, B.G R → (sp (R₀ := R₀) (R : Type) ⟶ G)), (∀ R, Function.Bijective (e R)) → (∀ R x y, e R (x + y) = e R x * e R y) →
    (∀ {R S : LAlg R₀} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x) →
    Smooth G.hom → ∀ (K W : LAlg R₀) (ρW : LHom W K), IsNilOver ρW → SM B K W ρW) := by
  intro R₀ _ G _ _ B e hb _ hnat hsm K W ρW hρ
  refine ⟨hρ, fun x => ?_⟩
  obtain ⟨y, hy⟩ := exists_point_lift G ρW.1 hρ.1 hρ.2 (e K x)
  obtain ⟨y', rfl⟩ := (hb W).2 y
  exact ⟨y', (hb K).1 (by rw [hnat, hy])⟩

end GlobalTheory.SmoothNilLift
end

section

open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChLaw

private lemma nil_of_mem_span {S : Type} [CommRing S] {s : Set S} (hs : ∀ a ∈ s, IsNilpotent a)
    {c : S} (hc : c ∈ Ideal.span s) : IsNilpotent c := by
  have h : Ideal.span s ≤ nilradical S := Ideal.span_le.2 fun a ha => mem_nilradical.2 (hs a ha)
  exact mem_nilradical.1 (h hc)

theorem groupLaw_powerSeries :
  (∀ {R₀ : Type} [CommRing R₀] {κ : Type} [Fintype κ] [DecidableEq κ] (f : MvPowerSeries κ R₀) (S : Type) [CommRing S] [Algebra R₀ S] (a : κ → S),
    (∀ N : ℕ, (∀ i, a i ^ N = 0) → nEval f a = tEval N f a) ∧
    ((∀ i, IsNilpotent (a i)) → (∀ (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S'), φ (nEval f a) = nEval f (fun i => φ (a i))) ∧
      nEval f a - algebraMap R₀ S (MvPowerSeries.coeff 0 f) ∈ Ideal.span (Set.range a))) →
  (∀ {R₀ : Type} [CommRing R₀] {κ : Type} [Fintype κ] [DecidableEq κ] (c : ∀ (S : Type) [CommRing S] [Algebra R₀ S], (κ → S) → S),
    (∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S') (a : κ → S),
      (∀ i, IsNilpotent (a i)) → φ (c S a) = c S' (fun i => φ (a i))) →
    ∃ f : MvPowerSeries κ R₀, ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a : κ → S), (∀ i, IsNilpotent (a i)) → c S a = nEval f a) →
  (∀ {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] (g : ℕ) (x : ∀ (S : Type) [CommRing S] [Algebra R₀ S], (Fin g → S) → (sp (R₀ := R₀) S ⟶ G)),
    ((∀ (S : Type) [CommRing S] [Algebra R₀ S], x S 0 = 1) ∧
      (∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S') (a : Fin g → S),
        (∀ i, IsNilpotent (a i)) → spMap φ ≫ x S a = x S' (fun i => φ (a i))) ∧
      (∀ (S : Type) [CommRing S] [Algebra R₀ S] (a b : Fin g → S), (∀ i, IsNilpotent (a i)) → (∀ i, IsNilpotent (b i)) → x S a = x S b → a = b) ∧
      (∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S'] (ρ : S →ₐ[R₀] S'), Function.Surjective ρ →
        (∀ a ∈ RingHom.ker ρ, IsNilpotent a) → ∀ z : sp (R₀ := R₀) S ⟶ G, spMap ρ ≫ z = 1 →
        ∃ a : Fin g → S, (∀ i, a i ∈ RingHom.ker ρ) ∧ z = x S a)) →
    ∃ F : Fin g → MvPowerSeries (Fin g ⊕ Fin g) R₀, ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a b : Fin g → S), (∀ i, IsNilpotent (a i)) → (∀ i, IsNilpotent (b i)) →
      (∀ k, fAdd F a b k ∈ Ideal.span (Set.range a ∪ Set.range b)) ∧ x S a * x S b = x S (fAdd F a b)) := by
  classical
  intro _ h2 R₀ _ G _ _ g x ⟨h0, hnat, hinj, hsur⟩
  have hex : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a b : Fin g → S), (∀ i, IsNilpotent (a i)) →
      (∀ i, IsNilpotent (b i)) → ∃ c : Fin g → S,
        (∀ k, c k ∈ Ideal.span (Set.range a ∪ Set.range b)) ∧ (∀ k, IsNilpotent (c k)) ∧
        x S a * x S b = x S c := by
    intro S _ _ a b ha hb
    set I : Ideal S := Ideal.span (Set.range a ∪ Set.range b) with hI
    have hnil : ∀ c ∈ I, IsNilpotent c := fun c hc =>
      nil_of_mem_span (by rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩); exacts [ha i, hb i]) hc
    have hker : ∀ c, c ∈ RingHom.ker (Ideal.Quotient.mkₐ R₀ I) ↔ c ∈ I := fun c => by
      rw [RingHom.mem_ker, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    have hz : spMap (Ideal.Quotient.mkₐ R₀ I) ≫ (x S a * x S b) = 1 := by
      have ea : (fun i => Ideal.Quotient.mkₐ R₀ I (a i)) = 0 := funext fun i =>
        (hker _).2 (Ideal.subset_span (Or.inl ⟨i, rfl⟩))
      have eb : (fun i => Ideal.Quotient.mkₐ R₀ I (b i)) = 0 := funext fun i =>
        (hker _).2 (Ideal.subset_span (Or.inr ⟨i, rfl⟩))
      rw [MonObj.comp_mul, hnat _ _ _ a ha, hnat _ _ _ b hb, ea, eb, h0, _root_.mul_one]
    obtain ⟨c, hc, hzc⟩ := hsur S (S ⧸ I) (Ideal.Quotient.mkₐ R₀ I)
      (Ideal.Quotient.mkₐ_surjective R₀ I) (fun c hc => hnil c ((hker c).1 hc)) _ hz
    exact ⟨c, fun k => (hker _).1 (hc k), fun k => hnil _ ((hker _).1 (hc k)), hzc⟩
  choose cc hc1 hc2 hc3 using hex
  have hF : ∀ k : Fin g, ∃ f : MvPowerSeries (Fin g ⊕ Fin g) R₀,
      ∀ (S : Type) [CommRing S] [Algebra R₀ S] (u : Fin g ⊕ Fin g → S)
        (hu : ∀ i, IsNilpotent (u i)),
        cc S (fun i => u (Sum.inl i)) (fun i => u (Sum.inr i)) (fun _ => hu _) (fun _ => hu _) k =
          nEval f u := by
    intro k
    obtain ⟨f, hf⟩ := h2 (R₀ := R₀) (κ := Fin g ⊕ Fin g)
      (fun S _ _ u => if hu : ∀ i, IsNilpotent (u i) then
        cc S (fun i => u (Sum.inl i)) (fun i => u (Sum.inr i)) (fun _ => hu _) (fun _ => hu _) k
        else 0) (by
        intro S _ _ S' _ _ φ u hu
        have hu' : ∀ i, IsNilpotent (φ (u i)) := fun i => (hu i).map φ
        simp only [dif_pos hu, dif_pos hu']
        have := hinj S'
          (fun j => φ (cc S (fun i => u (Sum.inl i)) (fun i => u (Sum.inr i))
            (fun _ => hu _) (fun _ => hu _) j))
          (cc S' (fun i => φ (u (Sum.inl i))) (fun i => φ (u (Sum.inr i)))
            (fun _ => hu' _) (fun _ => hu' _))
          (fun j => (hc2 _ _ _ _ _ j).map φ) (hc2 _ _ _ _ _) (by
            rw [← hnat _ _ φ _ (hc2 _ _ _ _ _), ← hc3, ← hc3, MonObj.comp_mul,
              hnat _ _ φ _ (fun _ => hu _), hnat _ _ φ _ (fun _ => hu _)])
        exact congrFun this k)
    refine ⟨f, fun S _ _ u hu => ?_⟩
    have := hf S u hu
    simpa only [dif_pos hu] using this
  choose F hF using hF
  refine ⟨F, fun S _ _ a b ha hb => ?_⟩
  have e : fAdd F a b = cc S a b ha hb := by
    funext k
    have hu : ∀ i, IsNilpotent (Sum.elim a b i) := by
      rintro (i | i); exacts [ha i, hb i]
    exact (hF k S (Sum.elim a b) hu).symm
  rw [e]
  exact ⟨hc1 S a b ha hb, hc3 S a b ha hb⟩

end GlobalTheory.ChLaw
end
