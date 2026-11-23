module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt
public import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SplitEquiv
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle052
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import GroundTheory.GlobalFields.TateThesis.AdelicCharLocal
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Objects
public import GroundTheory.PAdicHodge.Bundle007
public import GroundTheory.PAdicHodge.FactorizationFactorialLe
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Matrix IsLocalRing Polynomial

private theorem UpperTheory.Reformulated.B.Qf19.exists_eigvec {R : Type} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] (X : Matrix (Fin 3) (Fin 3) R)
    (hu : ∀ a b : Fin 3, a ≠ b → IsUnit (X a a - X b b))
    (hm : ∀ a b : Fin 3, a ≠ b → X a b ∈ maximalIdeal R) (a : Fin 3) :
    ∃ (l : R) (v : Fin 3 → R), v a = 1 ∧ (∀ b, b ≠ a → v b ∈ maximalIdeal R) ∧ X *ᵥ v = l • v := by
  have hd : X.map (residue R) = diagonal fun b => residue R (X b b) := by
    ext b c
    by_cases h : b = c
    · subst h; simp
    · rw [diagonal_apply_ne _ h, map_apply, residue_eq_zero_iff]; exact hm b c h
  have hne : ∀ b, b ≠ a → residue R (X a a) - residue R (X b b) ≠ 0 := fun b hb => by
    rw [← map_sub]; exact ((hu a b hb.symm).map (residue R)).ne_zero
  have hP : (∏ b ∈ Finset.univ.erase a, (residue R (X a a) - residue R (X b b))) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun b hb => hne b (Finset.ne_of_mem_erase hb)
  have hc : X.charpoly.map (residue R) =
      (Polynomial.X - C (residue R (X a a))) *
        ∏ b ∈ Finset.univ.erase a, (Polynomial.X - C (residue R (X b b))) := by
    rw [← Matrix.charpoly_map, hd, Matrix.charpoly_diagonal,
      Finset.mul_prod_erase Finset.univ (fun b => Polynomial.X - C (residue R (X b b))) (Finset.mem_univ a)]
  obtain ⟨l, hl, hla⟩ := HenselianRing.is_henselian (I := maximalIdeal R) X.charpoly X.charpoly_monic (X a a)
    (by
      rw [← residue_eq_zero_iff, ← eval₂_hom, ← eval_map, hc]
      simp)
    (by
      change IsUnit (residue R _)
      rw [← eval₂_hom, ← eval_map, ← derivative_map, hc, isUnit_iff_ne_zero]
      simpa [eval_prod] using hP)
  have hla' : residue R l = residue R (X a a) := by
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]; exact hla
  set M : Matrix (Fin 3) (Fin 3) R := scalar (Fin 3) l - X with hM
  have hdet : M.det = 0 := by rw [hM, ← Matrix.eval_charpoly]; exact hl
  have hMd : M.map (residue R) = diagonal fun b => residue R (X a a) - residue R (X b b) := by
    ext b c
    have := congrFun (congrFun hd b) c
    by_cases h : b = c
    · subst h; simp [hM, hla']
    · rw [diagonal_apply_ne _ h] at this ⊢
      simpa [hM, diagonal_apply_ne _ h] using this
  have hadj : ∀ b, residue R (M.adjugate b a) = (diagonal fun i => ∏ j ∈ Finset.univ.erase i,
      (residue R (X a a) - residue R (X j j))) b a := fun b => by
    have := (residue R).map_adjugate M
    rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, hMd, adjugate_diagonal] at this
    exact congrFun (congrFun this b) a
  have hun : IsUnit (M.adjugate a a) := by
    rw [← residue_ne_zero_iff_isUnit, hadj, diagonal_apply_eq]; exact hP
  obtain ⟨u, hu'⟩ := hun
  have hker : M *ᵥ (fun b => M.adjugate b a) = 0 := by
    ext b
    have := congrFun (congrFun (mul_adjugate M) b) a
    rw [hdet, zero_smul] at this
    exact this
  refine ⟨l, (↑u⁻¹ : R) • fun b => M.adjugate b a, ?_, fun b hb => ?_, ?_⟩
  · simp [← hu']
  · refine Ideal.mul_mem_left _ _ ?_
    rw [← residue_eq_zero_iff, hadj, diagonal_apply_ne _ hb]
  · rw [hM, sub_mulVec, sub_eq_zero] at hker
    rw [mulVec_smul, ← hker, smul_comm l]
    congr 1
    ext b
    simp [mulVec_diagonal, hM]

theorem UpperTheory.Reformulated.B.Qf19.exists_canon :
    ∀ {R : Type} [inst : CommRing R] [inst_1 : IsLocalRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
      (X : Matrix (Fin (3 : ℕ)) (Fin (3 : ℕ)) R),
      (∀ (a b : Fin (3 : ℕ)), a ≠ b → IsUnit (X a a - X b b)) →
        (∀ (a b : Fin (3 : ℕ)), a ≠ b → X a b ∈ IsLocalRing.maximalIdeal R) →
          ∃ (h : GL (Fin (3 : ℕ)) R), UpperTheory.V.UnitaryThreeInertia.Canon X h := by
  intro R _ _ _ X hu hm
  choose l v h1 h2 h3 using UpperTheory.Reformulated.B.Qf19.exists_eigvec X hu hm
  set H : Matrix (Fin 3) (Fin 3) R := Matrix.of fun b a => v a b with hH
  have hhat : ∀ a b, (H - 1) a b ∈ maximalIdeal R := fun a b => by
    by_cases h : a = b
    · subst h; simp [hH, h1]
    · simpa [hH, one_apply_ne h] using h2 b a h
  have hmap : (residue R).mapMatrix H = 1 := by
    ext a b
    have := (residue_eq_zero_iff _).2 (hhat a b)
    rw [Matrix.sub_apply, map_sub, sub_eq_zero] at this
    rw [RingHom.mapMatrix_apply, map_apply, this]
    by_cases h : a = b
    · subst h; simp
    · simp [one_apply_ne h]
  have hdet : IsUnit H.det := by
    rw [← residue_ne_zero_iff_isUnit, RingHom.map_det, hmap]; simp
  obtain ⟨h, hh⟩ := (Matrix.isUnit_iff_isUnit_det H).2 hdet
  have hXH : X * H = H * diagonal l := by
    ext b a
    have := congrFun (h3 a) b
    rw [mul_diagonal, mul_comm]
    exact this
  refine ⟨h, ?_, fun a => ?_, ?_⟩
  · intro a b; rw [hh]; exact hhat a b
  · rw [hh]; exact h1 a
  · have : ((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * X * h = diagonal l := by
      rw [Matrix.mul_assoc, hh, hXH, ← hh, ← Matrix.mul_assoc]
      simp
    rw [this]; exact isDiag_diagonal l
end

section

theorem UpperTheory.Reformulated.B.Gla1.haar_const_of_haar_exists :
    UpperTheory.ConvolutionTheory.T4.HaarEx → UpperTheory.ConvolutionTheory.T4.HaarConst := by
  intro H V G _ _ _ _ _ _ _ _ Gi _ _ _ _ _ _ _ _ Gv _ _ _ _ _ _ _ _ q p K hRP μ μi m hμ hμi hm
  have hm1 := fun v => (hm v).1
  choose a ha0 ha using H V G Gi Gv q p K hRP μ μi m hμ hμi hm1
  obtain ⟨hq, hp, hK, -⟩ := hRP
  obtain ⟨A⟩ : Nonempty (TopologicalSpace.PositiveCompacts Gi) := inferInstance
  refine ⟨a ∅, ha0 ∅, fun S => ?_⟩
  have h : a ∅ = a S :=
    UpperTheory.restricted_product_measure V G Gi Gv q (fun v => p v) (fun v => K v) μ μi m hq.measurable
      (fun v => (hp v).measurable) (fun v => (hK v).measurableSet) (fun v => (hm v).2)
      ⟨A, A.isCompact.measurableSet,
        (MeasureTheory.Measure.measure_pos_of_nonempty_interior μi A.interior_nonempty).ne',
        A.isCompact.measure_lt_top.ne⟩ ∅ S (a ∅) (a S) (ha ∅) (ha S)
  exact h ▸ ha S
end

section

theorem UpperTheory.Reformulated.B.Qp9.locPair_val_linear :
    ∀ (O : Type) [inst : CommRing O] [inst_1 : IsDomain O]
    [inst_2 : IsDiscreteValuationRing O] (K : Type) [Fintype K] [inst_4 : DecidableEq K] (ι : K → Type)
    [(k : K) → Fintype (ι k)] (σ : Type) [inst_6 : Fintype σ] (T : GlobalTheory.CompanionTheory.Ar.Num.LocPair ι O σ)
    (P : Ideal (GroundTheory.Heights₂.Heights.NumbersDVR.MRing ι O)),
    (∀ (Gs Hs : σ → MvPolynomial (σ ⊕ σ) ℝ), T.val P (Gs + Hs) = T.val P Gs + T.val P Hs) ∧
      (∀ (c : ℝ) (Gs : σ → MvPolynomial (σ ⊕ σ) ℝ),
          (T.val P fun (i : σ) ↦ (MvPolynomial.C : ℝ → MvPolynomial (σ ⊕ σ) ℝ) c * Gs i) = c * T.val P Gs) ∧
        ∀ (α : Type) (s : Finset α) (Gs : α → σ → MvPolynomial (σ ⊕ σ) ℝ),
          (T.val P fun (i : σ) ↦ ∑ a ∈ s, Gs a i) =
            ∑ a ∈ s,
              T.val P
                (Gs
                  a) := by
  intro O _ _ _ K _ _ ι _ σ _ T P
  have key : ∀ Gs : σ → MvPolynomial (σ ⊕ σ) ℝ, T.val P Gs = ∑ i, Finsupp.linearCombination ℝ
      (fun μ => (GlobalTheory.CompanionTheory.Ar.Num.cycList (GroundTheory.Heights₂.Heights.NumbersDVR.ratDiv P (T.f i) (T.g i))
        (GroundTheory.Heights₂.Heights.NumbersDVR.classList (Sum.elim T.x T.x') μ ++ []) : ℝ))
      (MvPolynomial.basisMonomials (σ ⊕ σ) ℝ |>.repr (Gs i)) := fun Gs => rfl
  refine ⟨fun Gs Hs => ?_, fun c Gs => ?_, fun α s Gs => ?_⟩
  · simp only [key, Pi.add_apply, map_add (f := _), Finset.sum_add_distrib]
  · simp only [key, MvPolynomial.C_mul', map_smul, smul_eq_mul, Finset.mul_sum]

  · simp only [key, map_sum]
    exact Finset.sum_comm
end

section

private lemma exists_ne_zero_smul_mem_of_span_eq_top_alt {O LL V : Type} [CommRing O] [IsDomain O] [Field LL] [Algebra O LL]
    [IsFractionRing O LL] [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    (T : Submodule O V) (h : Submodule.span LL (T : Set V) = ⊤) (v : V) :
    ∃ a : O, a ≠ 0 ∧ a • v ∈ T := by
  have hv : v ∈ Submodule.span LL (T : Set V) := h ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine T.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact T.smul_mem _ hax
    · rw [mul_smul]; exact T.smul_mem _ hby
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors O) c
    have hd : (d : O) ≠ 0 := nonZeroDivisors.ne_zero d.2
    refine ⟨(d : O) * a, mul_ne_zero hd ha, ?_⟩
    have key : ((d : O) * a) • c • x = n • a • x := by
      have e : ∀ (r : O) (y : V), r • y = (algebraMap O LL r) • y :=
        fun r y => (algebraMap_smul LL r y).symm
      have hnd' : c * algebraMap O LL (d : O) = algebraMap O LL n := hnd
      rw [e ((d : O) * a), e n, e a, smul_smul, smul_smul, map_mul, ← hnd']
      congr 1
      ring
    rw [key]
    exact T.smul_mem _ hax

open Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations in
theorem UpperTheory.Reformulated.B.ExistsSmulMemBis.exists_smul_mem
    {G : Type} [inst : Group G] [inst_1 : TopologicalSpace G]
    {Qp LL O : Type} [inst_2 : Field Qp] [inst_3 : Field LL] [inst_4 : Algebra Qp LL]
    [inst_5 : CommRing O] [inst_6 : Algebra O LL] [inst_7 : TopologicalSpace LL]
    (A : GRep G Qp LL O) (LA : @Lattice G inst LL inst_3 O inst_5 A.V A.acg A.modLL A.modO A.ρ)
    [IsDomain O] [IsFractionRing O LL] (v : A.V) :
    letI := A.acg
    letI := A.modO
    ∃ a : O, a ≠ 0 ∧ a • v ∈ LA.T := by
  let _ := A.acg
  let _ := A.modLL
  let _ := A.modO
  have _ := A.towO
  obtain ⟨T, _, _, _, hs⟩ := LA
  exact exists_ne_zero_smul_mem_of_span_eq_top_alt T hs v
end

section

theorem UpperTheory.Reformulated.B.Rd3.exists_infiniteAdelicChar_ne_one :
    ∀ {F : Type} [inst : Field F] [inst_1 : NumberField F]
    (w : NumberField.InfinitePlace F),
    ∃ (z : w.Completion),
      (GroundTheory.Global.infiniteAdelicChar F w : w.Completion → Circle) z ≠
        (1 : Circle) := by
  intro F _ _ w
  refine ⟨((2 * w.mult : ℕ) : w.Completion)⁻¹, fun h => ?_⟩
  have hm : (w.mult : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr NumberField.InfinitePlace.mult_pos.ne'
  have hx : 2 * Real.pi * -((w.mult : ℝ) * (((2 * w.mult : ℕ) : ℝ))⁻¹) = -Real.pi := by
    push_cast
    field_simp
  rw [GroundTheory.Global.infiniteAdelicChar_apply, map_inv₀, map_natCast, ← Complex.ofReal_natCast,
    ← Complex.ofReal_inv, Complex.ofReal_re] at h
  have h2 := congrArg (fun c : Circle => (c : ℂ)) h
  simp only [Real.fourierChar_apply, hx, Circle.coe_one] at h2
  rw [Complex.ofReal_neg, neg_mul, Complex.exp_neg, Complex.exp_pi_mul_I] at h2
  norm_num at h2
end

section

theorem UpperTheory.Reformulated.B.ExistsNsmulMem.exists_nsmul_mem.{u_1, u_2} :
    ∀ {E : Type u_1} {W : Type u_2} [inst : Field E] [NumberField E] [inst_2 : AddCommGroup W]
    [inst_3 : _root_.Module E W] {La : AddSubgroup W},
    GroundTheory.Heights₂.Heights.FiniteCovolume.IsLattice (E := E) La →
      ∀ (w : W),
        ∃ (d : ℕ),
          (0 : ℕ) < d ∧
            d • w ∈ La := by
  intro E W _ _ _ _ La hL w
  induction (hL.span_eq_top ▸ Submodule.mem_top : w ∈ Submodule.span E (La : Set W))
    using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨⟨d, hd, hx⟩, ⟨e, he, hy⟩⟩ := And.intro hx hy
    refine ⟨d * e, mul_pos hd he, smul_add (d * e) x y ▸ La.add_mem ?_ ?_⟩
    exacts [mul_comm e d ▸ mul_smul e d x ▸ La.nsmul_mem hx e, mul_smul d e y ▸ La.nsmul_mem hy d]
  | smul a x _ hx =>
    obtain ⟨⟨d, hd, hx⟩, n, s, hn, hs⟩ := And.intro hx (((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2
      (.of_finite ℚ a)).exists_nsmul_eq (NumberField.RingOfIntegers E))
    refine ⟨n * d, mul_pos (Nat.pos_of_ne_zero hn) hd, ?_⟩
    rw [mul_smul, smul_comm d a x, ← smul_assoc, hs]; exact hL.smul_mem s _ hx
end

section

theorem UpperTheory.Reformulated.B.ExistsZsmulMem.exists_zsmul_mem.{u_1, u_2} :
    ∀ {E : Type u_1} [inst : Field E] [NumberField E] {W : Type u_2} [inst_2 : AddCommGroup W]
    [inst_3 : _root_.Module E W] {La : AddSubgroup W},
    GroundTheory.Heights₂.Heights.FiniteCovolume.IsLattice (E := E) La →
      ∀ (x : W),
        ∃ (d : ℤ),
          d ≠ (0 : ℤ) ∧
            d • x ∈ La := by
  intro E _ _ W _ _ La h x
  refine Submodule.span_induction (p := fun x _ => ∃ d : ℤ, d ≠ 0 ∧ d • x ∈ La)
    (fun y hy => ⟨1, one_ne_zero, by simpa using hy⟩) ⟨1, one_ne_zero, by simp⟩ ?_ ?_
    (h.span_eq_top ▸ Submodule.mem_top : x ∈ Submodule.span E (La : Set W))
  · rintro y z - - ⟨d, hd, hy⟩ ⟨e, he, hz⟩
    refine ⟨d * e, mul_ne_zero hd he, ?_⟩
    rw [smul_add, mul_smul d e z, mul_comm d e, mul_smul e d y]
    exact add_mem (La.zsmul_mem hy e) (La.zsmul_mem hz d)
  · rintro a y - ⟨d, hd, hy⟩
    obtain ⟨m, hm, hi⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2
      (Algebra.IsAlgebraic.isAlgebraic a)).exists_integral_multiple
    refine ⟨m * d, mul_ne_zero hm hd, ?_⟩
    rw [mul_smul, smul_comm d a y, ← smul_assoc]
    exact h.smul_mem ⟨m • a, hi⟩ _ hy
end

section

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qi53.Acris :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ GroundTheory.PAdicHodge.ACris.ACris ℂ_[l] l

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qi53.Ainf :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ GroundTheory.PAdicHodge.AInf ℂ_[l] l

noncomputable def UpperTheory.Reformulated.B.Qi53.zA :
    (l : ℕ) → [inst : Fact (Nat.Prime l)] → ℤ_[l] →+* UpperTheory.Reformulated.B.Qi53.Acris l :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦
      (Algebra.algebraMap (UpperTheory.Reformulated.B.Qi53.Ainf l) (UpperTheory.Reformulated.B.Qi53.Acris l)).comp
        (GroundTheory.PAdicHodge.IsPerfectoidField.padicIntToWitt l)

theorem UpperTheory.Reformulated.B.Qi53.zA_smul.{u_1} :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {N : Type u_1} [inst_1 : AddCommGroup N]
      [inst_2 : _root_.Module (UpperTheory.Reformulated.B.Qi53.Acris l) N] (n : ℕ),
      (∀ (y : N), (↑l : UpperTheory.Reformulated.B.Qi53.Acris l) ^ n • y = (0 : N)) →
        ∀ (z : ℤ_[l]) (y : N),
          (UpperTheory.Reformulated.B.Qi53.zA l : ℤ_[l] → UpperTheory.Reformulated.B.Qi53.Acris l) z • y =
            ((PadicInt.toZModPow n : ℤ_[l] → ZMod (l ^ n)) z).val • y := by
  intro l _ N _ _ n h z y
  have hz : z - (((PadicInt.toZModPow n z).val : ℕ) : ℤ_[l]) ∈ RingHom.ker (PadicInt.toZModPow n : ℤ_[l] →+* ZMod (l ^ n)) := by
    haveI : NeZero (l ^ n) := ⟨pow_ne_zero n (Fact.out : Nat.Prime l).ne_zero⟩
    rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hz
  obtain ⟨w, hw⟩ := hz
  have hz' : z = (((PadicInt.toZModPow n z).val : ℕ) : ℤ_[l]) + (l : ℤ_[l]) ^ n * w := by
    rw [← hw]; ring
  generalize (PadicInt.toZModPow n z).val = m at hz' ⊢
  rw [hz', map_add (f := _), map_mul, map_pow, map_natCast, map_natCast, add_smul, mul_smul, h, add_zero,
    Nat.cast_smul_eq_nsmul]
end

section

theorem UpperTheory.Reformulated.B.Gc4.conj_embedding_rt :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E]
    [inst_2 : NumberField.IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (τ : E →+* ℂ),
    (starRingEnd ℂ : ℂ → ℂ) ((τ : E → ℂ) (↑H.rt : E)) =
      -(τ : E → ℂ)
          (↑H.rt :
            E) := by
  intro E _ _ _ H τ
  have h1 : (H.rt : E) ^ 2 = -(H.d : E) := by
    simpa using congrArg (algebraMap (NumberField.RingOfIntegers E) E) H.rt_sq
  have h2 : (τ (H.rt : E)) ^ 2 = -(H.d : ℂ) := by
    rw [← map_pow, h1, map_neg, map_natCast]
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  generalize τ (H.rt : E) = z at h2 ⊢
  have hre : z.re * z.re - z.im * z.im = -(H.d : ℝ) := by simpa [sq] using congrArg Complex.re h2
  have him : z.re * z.im + z.im * z.re = 0 := by simpa [sq] using congrArg Complex.im h2
  have hz : z.im ≠ 0 := fun h => by rw [h] at hre; nlinarith [mul_self_nonneg z.re]
  have h0 : z.re = 0 := mul_right_cancel₀ hz (by linarith)
  apply Complex.ext <;> simp [h0]
end

section

theorem UpperTheory.Reformulated.B.ComplexConjugateRootEqNeg.rt0_conj_neg_ne_zero :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E]
      (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), (starRingEnd ℂ : ℂ → ℂ) H.rt0 = -H.rt0 := by
  intro E _ _ _ H
  have h := H.sqrt_neg_disc_sq
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.natCast_re, Complex.natCast_im, neg_zero] at hre him
  have h0 : H.rt0.re * H.rt0.im = 0 := by linarith
  have hr : H.rt0.re = 0 := by
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact h1
    · exfalso
      rw [h1] at hre
      nlinarith [mul_self_nonneg H.rt0.re]
  apply Complex.ext
  · rw [Complex.conj_re, Complex.neg_re, hr, neg_zero]
  · rw [Complex.conj_im, Complex.neg_im]
end

section

theorem UpperTheory.Reformulated.B.ConjugateRootZeroSecond.rt0_conj_neg_ne_zero :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E]
      (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), (starRingEnd ℂ : ℂ → ℂ) H.rt0 = -H.rt0 := by
  intro E _ _ _ H
  have h := H.sqrt_neg_disc_sq
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [pow_two] at hre him
  have h0 : H.rt0.re = 0 := by
    by_contra hne
    have him0 : H.rt0.im = 0 := by
      have hm : H.rt0.re * H.rt0.im = 0 := by linarith
      exact (mul_eq_zero.mp hm).resolve_left hne
    rw [him0] at hre
    nlinarith [mul_self_nonneg H.rt0.re]
  apply Complex.ext <;> simp [h0]
end

section

theorem UpperTheory.Reformulated.B.StarRingEndRootEqNeg.rt0_conj_neg_ne_zero :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E]
      (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), (starRingEnd ℂ : ℂ → ℂ) H.rt0 = -H.rt0 := by
  intro E _ _ _ H
  have hd : (0 : ℝ) < (H.d : ℝ) := by exact_mod_cast H.d_prime.pos
  have h := H.sqrt_neg_disc_sq
  have hre : H.rt0.re * H.rt0.re - H.rt0.im * H.rt0.im = -(H.d : ℝ) := by
    simpa [pow_two, Complex.mul_re] using congrArg Complex.re h
  have him : H.rt0.re * H.rt0.im + H.rt0.im * H.rt0.re = 0 := by
    simpa [pow_two, Complex.mul_im] using congrArg Complex.im h
  have ha : H.rt0.re = 0 := by
    by_contra ha
    have hm : H.rt0.re * H.rt0.im = 0 := by linarith
    have hb : H.rt0.im = 0 := (mul_eq_zero.mp hm).resolve_left ha
    rw [hb] at hre
    nlinarith [mul_self_nonneg H.rt0.re]
  apply Complex.ext
  · simp [ha]
  · simp
end
