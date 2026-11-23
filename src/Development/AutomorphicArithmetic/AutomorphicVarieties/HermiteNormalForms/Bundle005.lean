module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.NerveFaceClosed
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FaceDSingle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Bundle003
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Bundle001

@[expose] public section

section

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

private theorem UpperTheory.V.KT.fe_lift {X : Type} (s : Set X) (c : X →₀ ℤ)
    (hc : c ∈ Finsupp.supported ℤ ℤ s) :
    ∃ f : {t // t ∈ s} →₀ ℤ, Finsupp.mapDomain Subtype.val f = c := by
  have h := Finsupp.lmapDomain_supported ℤ ℤ (Subtype.val : {t // t ∈ s} → X) Set.univ
  rw [Set.image_univ, Subtype.range_coe_subtype, Set.setOf_mem_eq] at h
  rw [← h] at hc
  obtain ⟨f, -, hf⟩ := hc
  exact ⟨f, hf⟩

private theorem UpperTheory.V.KT.fe_mem {X : Type} (s : Set X) (f : {t // t ∈ s} →₀ ℤ) :
    Finsupp.mapDomain Subtype.val f ∈ Finsupp.supported ℤ ℤ s := by
  have h := Finsupp.lmapDomain_supported (M := ℤ) (R := ℤ) (Subtype.val : {t // t ∈ s} → X) Set.univ
  rw [Set.image_univ, Subtype.range_coe] at h
  rw [← h]
  exact Submodule.mem_map_of_mem (by simp [Finsupp.supported_univ])

private theorem UpperTheory.V.KT.fe_comm {I : Type} (S : ∀ n, Set (Fin n → I)) (hS : ConeExtensionAcyclic.FaceClosed S)
    (p : ℕ) (f : {t : Fin (p + 1) → I // t ∈ S (p + 1)} →₀ ℤ) :
    Finsupp.mapDomain Subtype.val
      (KH.faceD (fun (i : Fin (p + 1)) (t : {t : Fin (p + 1) → I // t ∈ S (p + 1)}) =>
        (⟨t.1 ∘ i.succAbove, hS _ t.1 t.2 i⟩ : {t : Fin p → I // t ∈ S p})) f) =
      ConeExtensionAcyclic.bd I p (Finsupp.mapDomain Subtype.val f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [map_add (f := _), Finsupp.mapDomain_add, hf, hg, Finsupp.mapDomain_add, map_add (f := _)]
  | single t c =>
    rw [KH.faceD_single, Finsupp.mapDomain_single]
    simp only [ConeExtensionAcyclic.bd, Finsupp.linearCombination_single, Finset.smul_sum]

    rw [← Finsupp.lmapDomain_apply ℤ ℤ, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_zsmul, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
    simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [mul_comm]

private theorem UpperTheory.V.KT.fe_aug {I : Type} (s : Set (Fin 1 → I)) (f : {t // t ∈ s} →₀ ℤ) :
    ConeExtensionAcyclic.bd I 0 (Finsupp.mapDomain Subtype.val f) =
      Finsupp.single (Fin.elim0 : Fin 0 → I) (KH.aug _ f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [Finsupp.mapDomain_add, map_add (f := _), hf, hg, map_add (f := _), Finsupp.single_add]
  | single t c =>
    rw [Finsupp.mapDomain_single, KH.aug_single]
    simp only [ConeExtensionAcyclic.bd, Finsupp.linearCombination_single]
    rw [Fin.sum_univ_one]
    simp only [Fin.val_zero, pow_zero, one_smul, Finsupp.smul_single, smul_eq_mul, mul_one]
    congr 1
    funext k
    exact Fin.elim0 k

theorem UpperTheory.V.KT.faceexact :
    ∀ (I : Type) (S : ∀ n, Set (Fin n → I)) (hS : ConeExtensionAcyclic.FaceClosed S), S 0 = Set.univ → ConeExtensionAcyclic.Acyc S → ∀ m : ℕ,
    KH.FaceExactTo (fun p => {t : Fin (p + 1) → I // t ∈ S (p + 1)})
      (fun p i t => ⟨t.1 ∘ i.succAbove, hS _ t.1 t.2 i⟩) m := by
  intro I S hS hS0 hA m
  obtain ⟨hA0, hAn⟩ := hA
  have inj : ∀ n, Function.Injective (Finsupp.mapDomain (M := ℤ) (Subtype.val : {t : Fin n → I // t ∈ S n} → (Fin n → I))) :=
    fun n => Finsupp.mapDomain_injective Subtype.val_injective
  refine ⟨?_, ?_, ?_⟩
  · have hc : Finsupp.single (Fin.elim0 : Fin 0 → I) (1 : ℤ) ∈ Finsupp.supported ℤ ℤ (S 0) := by
      rw [hS0, Finsupp.supported_univ]
      exact Submodule.mem_top
    obtain ⟨b, hb, hbc⟩ := hA0 _ hc
    obtain ⟨f, rfl⟩ := fe_lift (S 1) b hb
    rw [fe_aug] at hbc
    have h1 : KH.aug _ f = 1 := Finsupp.single_injective _ hbc
    intro n
    exact ⟨n • f, by rw [map_zsmul, h1, smul_eq_mul, mul_one]⟩
  · intro y
    constructor
    · intro hy
      have hc := fe_mem (S 1) y
      have hbd : ConeExtensionAcyclic.bd I 0 (Finsupp.mapDomain Subtype.val y) = 0 := by
        rw [fe_aug, hy, Finsupp.single_zero]
      obtain ⟨b, hb, hbc⟩ := hAn 0 _ hc hbd
      obtain ⟨g, rfl⟩ := fe_lift (S 2) b hb
      refine ⟨g, inj 1 ?_⟩
      rw [fe_comm S hS 1 g, hbc]
    · rintro ⟨g, rfl⟩
      have h := fe_aug (S 1) (KH.faceD (fun (i : Fin 2) (t : {t : Fin 2 → I // t ∈ S 2}) =>
        (⟨t.1 ∘ i.succAbove, hS _ t.1 t.2 i⟩ : {t : Fin 1 → I // t ∈ S 1})) g)
      rw [fe_comm S hS 1 g, ConeExtensionAcyclic.bd_bd] at h
      exact Finsupp.single_eq_zero.mp h.symm
  · intro p _ y
    constructor
    · intro hy
      have hc := fe_mem (S (p + 2)) y
      have hbd : ConeExtensionAcyclic.bd I (p + 1) (Finsupp.mapDomain Subtype.val y) = 0 := by
        rw [← fe_comm S hS (p + 1) y, hy, Finsupp.mapDomain_zero]
      obtain ⟨b, hb, hbc⟩ := hAn (p + 1) _ hc hbd
      obtain ⟨g, rfl⟩ := fe_lift (S (p + 3)) b hb
      refine ⟨g, inj (p + 2) ?_⟩
      rw [fe_comm S hS (p + 2) g, hbc]
    · rintro ⟨g, rfl⟩
      apply inj (p + 1)
      rw [fe_comm S hS (p + 1), fe_comm S hS (p + 2) g, ConeExtensionAcyclic.bd_bd, Finsupp.mapDomain_zero]
end

section

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

theorem UpperTheory.V.KT.psdcone :
    ∀ (L : Type) [Field L] [NumberField L] (N : ℕ), IsClosed (Psd L N) ∧ (∀ c : ℝ, 0 < c → ∀ k ∈ Psd L N, c • k ∈ Psd L N) ∧
    Pos L N ⊆ Psd L N ∧ (ConeExtensionAcyclic.posDual (Psd L N)).Nonempty := by
  intro L _ _ N
  have hc : ∀ (w : InfinitePlace L) (i j : Fin N), Continuous (fun h : HS L N => mat h w i j) := by
    intro w i j
    exact (continuous_apply j).comp ((continuous_apply i).comp ((continuous_apply w).comp continuous_subtype_val))
  have htr : ∀ k ∈ Psd L N, ∀ w, 0 ≤ (mat k w).trace := by
    intro k hk w
    exact Finset.sum_nonneg fun i _ => (hk w).diag_nonneg
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hP : Psd L N = ⋂ w : InfinitePlace L, ⋂ x : Fin N →₀ ℂ,
        {h : HS L N | 0 ≤ x.sum fun i xi => x.sum fun j xj => star xi * mat h w i j * xj} := by
      ext h
      simp only [Psd, Set.mem_setOf_eq, Set.mem_iInter]
      constructor
      · intro hh w x
        exact (hh w).2 x
      · intro hh w
        exact ⟨mat_herm h w, hh w⟩
    rw [hP]
    refine isClosed_iInter fun w => isClosed_iInter fun x => ?_
    refine isClosed_le continuous_const ?_
    unfold Finsupp.sum
    exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      (continuous_const.mul (hc w i j)).mul continuous_const
  · intro c hc k hk w
    show (mat (c • k) w).PosSemidef
    rw [mat_smul]
    exact (hk w).smul hc.le
  · intro k hk w
    exact (hk w).posSemidef
  · let f : HS L N →ₗ[ℝ] ℝ :=
      { toFun := fun h => ∑ w, ((mat h w).trace).re
        map_add' := by
          intro h k
          simp only [← Finset.sum_add_distrib, ← Complex.add_re, ← Matrix.trace_add]
          rfl
        map_smul' := by
          intro c h
          simp only [mat_smul, Matrix.trace_smul, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun w _ => ?_
          simp }
    have hf : Continuous f := by
      show Continuous (fun h : HS L N => ∑ w, ((mat h w).trace).re)
      exact continuous_finsetSum _ fun w _ =>
        Complex.continuous_re.comp (continuous_finsetSum _ fun i _ => hc w i i)
    refine ⟨⟨f, hf⟩, ?_⟩
    intro k hk hk0
    have hw : ∃ w, mat k w ≠ 0 := by
      by_contra hne
      push_neg at hne
      exact hk0 (HS_ext fun w => by rw [hne w, mat_zero])
    obtain ⟨w, hw⟩ := hw
    show 0 < ∑ w, ((mat k w).trace).re
    have hpos : 0 < ((mat k w).trace).re := by
      have h1 : 0 ≤ (mat k w).trace := htr k hk w
      have h2 : (mat k w).trace ≠ 0 := fun h0 => hw (((hk w).trace_eq_zero_iff).mp h0)
      exact (Complex.lt_def.mp (lt_of_le_of_ne h1 (Ne.symm h2))).1
    refine lt_of_lt_of_le hpos ?_
    refine Finset.single_le_sum (f := fun w => ((mat k w).trace).re) (fun v _ => ?_) (Finset.mem_univ w)
    exact (Complex.le_def.mp (htr k hk v)).1
end

section

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

theorem UpperTheory.V.KT.spanpsd :
    ∀ (L : Type) [Field L] [NumberField L] (N : ℕ) (M : Set (Lat L N)),
    (∀ k ∈ Psd L N, (∀ y ∈ M, q k y = 0) → k = 0) → Spans M := by
  intro L _ _ N M hM
  classical
  by_contra hS
  have hlt : spanL M < ⊤ := lt_top_iff_ne_top.mpr hS
  obtain ⟨f, hf0, hker⟩ := Submodule.exists_le_ker_of_lt_top _ hlt
  set c : Fin N → L := fun i => f (fun j => if i = j then 1 else 0) with hcdef
  have hfc : ∀ x : Fin N → L, f x = ∑ i, x i * c i := by
    intro x
    rw [LinearMap.pi_apply_eq_sum_univ]
    rfl
  have hc0 : ∃ i, c i ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply hf0
    refine LinearMap.ext fun x => ?_
    rw [hfc]
    simp [hc]
  obtain ⟨i0, hi0⟩ := hc0
  let u : InfinitePlace L → Fin N → ℂ := fun w i => w.embedding (c i)
  let A : InfinitePlace L → Matrix (Fin N) (Fin N) ℂ := fun w => vecMulVec (star (u w)) (u w)
  have hA : ∀ w, (A w).PosSemidef := fun w => posSemidef_vecMulVec_star_self (u w)
  let k : HS L N := mkHS A (fun w => (hA w).isHermitian)
  have hmat : ∀ w, mat k w = A w := fun w => rfl
  have hkP : k ∈ Psd L N := by
    intro w
    rw [hmat]
    exact hA w
  have hq : ∀ y ∈ M, q k y = 0 := by
    intro y hy
    have hyk : f (toL y) = 0 := hker (Submodule.subset_span ⟨y, hy, rfl⟩)
    rw [hfc] at hyk
    show ∑ w, (star (toR y w) ⬝ᵥ mat k w *ᵥ toR y w).re = 0
    refine Finset.sum_eq_zero fun w _ => ?_
    have hsum : ∑ j, u w j * toR y w j = 0 := by
      have : w.embedding (∑ j, toL y j * c j) = 0 := by rw [hyk, map_zero]

      rw [map_sum] at this
      rw [← this]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, mul_comm]
      rfl
    have hAz : mat k w *ᵥ toR y w = 0 := by
      funext i
      rw [hmat]
      simp only [A, mulVec, dotProduct, vecMulVec_apply, mul_assoc, ← Finset.mul_sum, hsum,
        mul_zero, Pi.zero_apply]
    rw [hAz]
    simp
  have hk0 := hM k hkP hq
  have w0 : InfinitePlace L := Classical.arbitrary _
  have h1 : mat k w0 i0 i0 = 0 := by
    rw [hk0]
    rfl
  rw [hmat] at h1
  simp only [A, vecMulVec_apply, Pi.star_apply, u] at h1
  have hne : w0.embedding (c i0) ≠ 0 := (map_ne_zero _).mpr hi0
  exact hne (by
    rcases mul_eq_zero.mp h1 with h | h
    · exact star_eq_zero.mp h
    · exact h)
end

section

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

theorem UpperTheory.V.KT.gramq :
    ∀ (L : Type) [Field L] [NumberField L] (N : ℕ) (h : HS L N), (gram h).IsHermitian ∧
    (∀ x : Fin N × BI L → ℝ, x ⬝ᵥ (gram h *ᵥ x) = qR h (realVec x)) ∧
    (∀ c : Fin N × BI L → ℤ, realVec (fun s => (c s : ℝ)) = toR (intVec c)) ∧
    Function.Bijective (intVec : (Fin N × BI L → ℤ) → Lat L N) := by
  intro L _ _ N h
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine Matrix.IsHermitian.ext fun s t => ?_
    simp only [gram, of_apply, star_trivial]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← (mat_herm h w).apply t.1 s.1]
    simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.mul_im]
    ring
  · intro x
    have key : ∀ w, (star (realVec x w) ⬝ᵥ mat h w *ᵥ realVec x w).re =
        ∑ s, ∑ t, x s * ((star (embO w (RingOfIntegers.basis L s.2)) * mat h w s.1 t.1 *
          embO w (RingOfIntegers.basis L t.2)).re * x t) := by
      intro w
      have hr : ∀ s t, x s * ((star (embO w (RingOfIntegers.basis L s.2)) * mat h w s.1 t.1 *
          embO w (RingOfIntegers.basis L t.2)).re * x t) =
          ((x s : ℂ) * (star (embO w (RingOfIntegers.basis L s.2)) * mat h w s.1 t.1 *
          embO w (RingOfIntegers.basis L t.2)) * (x t : ℂ)).re := by
        intro s t
        rw [Complex.re_mul_ofReal, Complex.re_ofReal_mul]
        ring
      simp only [hr, ← Complex.re_sum]
      congr 1
      simp only [realVec, dotProduct, mulVec, Pi.star_apply, star_sum, star_mul', Complex.star_def,
        Complex.conj_ofReal, Finset.mul_sum, Finset.sum_mul, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun a _ => ?_
      refine Eq.trans ?_ Finset.sum_comm.symm
      refine Finset.sum_congr rfl fun b _ => ?_
      refine Eq.trans ?_ Finset.sum_comm.symm
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
      ring
    simp only [qR, key]
    simp only [dotProduct, mulVec, gram, of_apply, Finset.mul_sum, Finset.sum_mul]
    calc ∑ s, ∑ t, ∑ w, x s * ((star (embO w (RingOfIntegers.basis L s.2)) * mat h w s.1 t.1 *
          embO w (RingOfIntegers.basis L t.2)).re * x t)
        = ∑ s, ∑ w, ∑ t, x s * ((star (embO w (RingOfIntegers.basis L s.2)) * mat h w s.1 t.1 *
          embO w (RingOfIntegers.basis L t.2)).re * x t) :=
          Finset.sum_congr rfl fun s _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  · intro c
    funext w a

    simp [realVec, toR, intVec, map_sum, zsmul_eq_mul]
  · let E : (Fin N × BI L → ℤ) ≃ Lat L N :=
      (Equiv.curry _ _ _).trans
        (Equiv.piCongrRight fun _ => (RingOfIntegers.basis L).equivFun.symm.toEquiv)
    have hE : (intVec : (Fin N × BI L → ℤ) → Lat L N) = E := by
      funext c a
      simp [E, intVec, Module.Basis.equivFun_symm_apply, Equiv.curry]
    rw [hE]
    exact E.bijective
end

section

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

open NumberField.InfinitePlace in
private theorem one_coord (L : Type) [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L]
    (z : InfinitePlace L → ℂ) :
    ∃ x : BI L → ℝ, ∀ w, ∑ i, (x i : ℂ) * embO w (RingOfIntegers.basis L i) = z w := by
  classical
  let m : mixedEmbedding.mixedSpace L := (0, fun w => z w.1)
  let c := (mixedEmbedding.latticeBasis L).repr m
  refine ⟨fun i => c i, fun w => ?_⟩
  have hw : w.IsComplex := IsTotallyComplex.isComplex w
  have hsum := (mixedEmbedding.latticeBasis L).sum_repr m
  have h2 := congrArg (fun p : mixedEmbedding.mixedSpace L => p.2 ⟨w, hw⟩) hsum
  simp only [Prod.snd_sum, Finset.sum_apply, Prod.smul_snd, Pi.smul_apply,
    mixedEmbedding.latticeBasis_apply, mixedEmbedding.mixedEmbedding_apply_isComplex,
    integralBasis_apply, Complex.real_smul, m] at h2
  rw [← h2]
  rfl

theorem UpperTheory.V.KT.realsurj :
    ∀ (L : Type) [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] (N : ℕ),
    Function.Surjective (realVec : (Fin N × BI L → ℝ) → VR L N) := by
  intro L _ _ _ N z
  choose x hx using fun a : Fin N => one_coord L (fun w => z w a)
  exact ⟨fun s => x s.1 s.2, funext fun w => funext fun a => hx a w⟩
end

section

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

private theorem UpperTheory.V.KT.finite_subfamily_spans_dual {E Y : Type*} [AddCommGroup E] [Module ℝ E]
    [Module.Finite ℝ E] (f : Y → Module.Dual ℝ E) (S : Set Y) :
    ∃ M : Finset Y, M.card ≤ Module.finrank ℝ E ∧ (∀ y ∈ M, y ∈ S) ∧
      ∀ k : E, (∀ y ∈ M, f y k = 0) → ∀ y ∈ S, f y k = 0 := by
  classical
  obtain ⟨b, hbs, hspan, hli⟩ := exists_linearIndependent ℝ (f '' S)
  have hbfin : b.Finite := hli.setFinite
  have hch : ∀ φ ∈ b, ∃ y, y ∈ S ∧ f y = φ := fun φ hφ => hbs hφ
  choose g hgS hgf using hch
  refine ⟨hbfin.toFinset.attach.image (fun φ => g φ.1 (hbfin.mem_toFinset.mp φ.2)), ?_, ?_, ?_⟩
  · haveI : Fintype b := hbfin.fintype
    calc (hbfin.toFinset.attach.image (fun φ => g φ.1 (hbfin.mem_toFinset.mp φ.2))).card
        ≤ hbfin.toFinset.attach.card := Finset.card_image_le
      _ = hbfin.toFinset.card := Finset.card_attach
      _ = Fintype.card b := hbfin.card_toFinset
      _ ≤ Module.finrank ℝ (Module.Dual ℝ E) := hli.fintype_card_le_finrank
      _ = Module.finrank ℝ E := Subspace.dual_finrank_eq
  · intro y hy
    obtain ⟨φ, _, rfl⟩ := Finset.mem_image.mp hy
    exact hgS _ _
  · intro k hk y hy
    have hsub : b ⊆ LinearMap.ker (Module.Dual.eval ℝ E k) := by
      intro φ hφ
      rw [SetLike.mem_coe, LinearMap.mem_ker, Module.Dual.eval_apply, ← hgf φ hφ]
      exact hk _ (Finset.mem_image.mpr ⟨⟨φ, hbfin.mem_toFinset.mpr hφ⟩, Finset.mem_attach _ _, rfl⟩)
    have hle := Submodule.span_le.mpr hsub
    rw [hspan] at hle
    have hm := hle (Submodule.subset_span ⟨y, hy, rfl⟩)
    rwa [LinearMap.mem_ker, Module.Dual.eval_apply] at hm

theorem UpperTheory.V.KT.vxdet :
    ∀ (L : Type) [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] (N : ℕ) (v : Vx L N),
    ∃ M : Finset (Lat L N), M.card ≤ dd L N * N ∧ (∀ y ∈ M, q v.1 y = 1) ∧
      ∀ h : HS L N, (∀ y ∈ M, q h y = 1) → h = v.1 := by
  intro L _ _ _ N v
  obtain ⟨M, hMc, hMS, hMk⟩ := UpperTheory.V.KT.finite_subfamily_spans_dual (E := HS L N)
    (fun y : Lat L N => (ev y : Module.Dual ℝ (HS L N))) {y | y ≠ 0 ∧ q v.1 y = 1}
  refine ⟨M, hMc.trans (rankhs L N), fun y hy => (hMS y hy).2, ?_⟩
  intro h hh
  have hk : ∀ y ∈ M, ev y (h - v.1) = 0 := by
    intro y hy
    rw [map_sub, ev_apply, ev_apply, hh y hy, (hMS y hy).2, sub_self]
  have hall := hMk (h - v.1) hk
  have h0 : h - v.1 = 0 := by
    apply v.2.2
    intro y hy
    have hy' : q v.1 y.1 = 1 := by
      rw [← ev_apply]
      exact hy
    exact hall y.1 ⟨y.2, hy'⟩
  exact sub_eq_zero.mp h0
end
