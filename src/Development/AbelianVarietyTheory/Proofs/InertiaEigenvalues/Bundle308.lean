module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
public import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.LengthCommensurableMapIffOfInjective
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle007
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle005
public import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle284
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
import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.Complete
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
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsOpenKerFinIdele
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle001

@[expose] public section

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

namespace GlobalTheory.Decompl.LAdic

def Good (p : ℕ) (R : Type) [CommRing R] : Prop :=
  (∀ x : R, (p : R) * x = 0 → x = 0) ∧ (∀ x : R, (∀ k : ℕ, ∃ r, x = (p : R) ^ k * r) → x = 0) ∧
    ∀ x : ℕ → R, ∃ s, ∀ k : ℕ, ∃ r, s - ∑ i ∈ Finset.range k, (p : R) ^ i * x i = (p : R) ^ k * r

theorem good_of_complete (p : ℕ) (R : Type) [CommRing R] (h : ∀ x : R, (p : R) * x = 0 → x = 0)
    [hc : IsAdicComplete (Ideal.span {(p : R)}) R] : Good p R := by
  have mem : ∀ (k : ℕ) (x : R), x ∈ (Ideal.span {(p : R)} ^ k • ⊤ : Submodule R R) ↔
      ∃ r, x = (p : R) ^ k * r := by
    intro k x
    rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    rfl
  refine ⟨h, fun x hx => ?_, fun x => ?_⟩
  · refine IsHausdorff.haus (I := Ideal.span {(p : R)}) hc.toIsHausdorff x fun k => ?_
    rw [SModEq.zero, mem]
    exact hx k
  · obtain ⟨s, hs⟩ := IsPrecomplete.prec (I := Ideal.span {(p : R)}) hc.toIsPrecomplete
      (f := fun k => ∑ i ∈ Finset.range k, (p : R) ^ i * x i) (by
        intro m n hmn
        rw [SModEq.sub_mem, mem]
        obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
        refine ⟨-∑ i ∈ Finset.range k, (p : R) ^ i * x (m + i), ?_⟩
        rw [Finset.sum_range_add, mul_neg, Finset.mul_sum]
        simp only [pow_add, mul_assoc]
        ring)
    refine ⟨s, fun k => ?_⟩
    have := (hs k).symm
    rwa [SModEq.sub_mem, mem] at this

theorem good_tensor {Z O : Type} [CommRing Z] [CommRing O] [Algebra Z O] {I : Type} [Fintype I]
    (b : Module.Basis I Z O) {W : Type} [CommRing W] [Algebra Z W] (p : ℕ) (h : Good p W) :
    Good p (O ⊗[Z] W) := by
  have hp : ∀ (k : ℕ) (i : I) (x : O ⊗[Z] W),
      crd b i ((p : O ⊗[Z] W) ^ k * x) = (p : W) ^ k * crd b i x := by
    intro k i x
    rw [← Nat.cast_pow, crd_natCast_mul, Nat.cast_pow]
  refine ⟨fun x hx => ext_crd b fun i => ?_, fun x hx => ext_crd b fun i => ?_, fun x => ?_⟩
  · rw [map_zero]
    apply h.1
    rw [← crd_natCast_mul, hx, map_zero]
  · rw [map_zero]
    refine h.2.1 _ fun k => ?_
    obtain ⟨r, hr⟩ := hx k
    exact ⟨crd b i r, by rw [← hp, ← hr]⟩
  · choose s r hs using fun i => h.2.2 fun k => crd b i (x k)
    refine ⟨∑ j, b j ⊗ₜ[Z] s j, fun k => ⟨∑ j, b j ⊗ₜ[Z] r j k, ext_crd b fun i => ?_⟩⟩

    rw [map_sub, hp, crd_sum, crd_sum b (fun j => r j k), map_sum, ← hs]
    simp only [hp]

theorem good_witt (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] :
    Good p (WittVector p k) :=
  good_of_complete p _ fun x hx => WittVector.eq_zero_of_p_mul_eq_zero x (by rw [mul_comm]; exact hx)

theorem ladic_RW (l : ℕ) [Fact l.Prime] (LL : FinExt l) :
    (∀ x : RW LL, (l : RW LL) * x = 0 → x = 0) ∧
    (∀ x : RW LL, (∀ k : ℕ, ∃ r, x = (l : RW LL) ^ k * r) → x = 0) ∧
    ∀ x : ℕ → RW LL, ∃ s, ∀ k : ℕ, ∃ r,
      s - ∑ i ∈ Finset.range k, (l : RW LL) ^ i * x i = (l : RW LL) ^ k * r :=
  good_tensor (W := WCb l) (basisO LL) l (good_witt l (Cb l))

end GlobalTheory.Decompl.LAdic
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys
open scoped TensorProduct

namespace GlobalTheory.EigRed

theorem mem_smul_of_sum_eigenvectors {O V ι α : Type*} [CommRing O] [AddCommGroup V] [Module O V]
    (I : Ideal O) (B : Submodule O V) (T : ι → Module.End O V) (hT : ∀ i, ∀ x ∈ B, T i x ∈ B) (ev : ι → O)
    (s : Finset α) :
    ∀ (y : α → V) (x : V), (∀ a ∈ s, y a = 0 ∨ ∃ e : ι → O, (∀ i, T i (y a) = e i • y a) ∧ ∃ i, IsUnit (ev i - e i)) →
      x = ∑ a ∈ s, y a → x ∈ B → (∀ i, T i x - ev i • x ∈ I • B) → x ∈ I • B := by
  classical
  have hTI : ∀ i, ∀ m ∈ I • B, T i m ∈ I • B := by
    intro i m hm
    refine Submodule.smul_induction_on hm (fun r hr n hn => ?_) (fun a b ha hb => ?_)
    · rw [map_smul]; exact Submodule.smul_mem_smul hr (hT i n hn)
    · rw [map_add]; exact add_mem ha hb
  induction s using Finset.induction_on with
  | empty => intro y x _ hx _ _; simp [hx]
  | insert a s ha ih =>
    intro y x hy hx hxB hev
    rw [Finset.sum_insert ha] at hx
    rcases hy a (Finset.mem_insert_self _ _) with h0 | ⟨e, he, i, hu⟩
    · exact ih y x (fun b hb => hy b (Finset.mem_insert_of_mem hb)) (by simpa [h0] using hx) hxB hev
    · have h1 : T i x - e i • x ∈ I • B := by
        refine ih (fun b => T i (y b) - e i • y b) _ (fun b hb => ?_) ?_ (sub_mem (hT i x hxB) (B.smul_mem _ hxB))
          (fun j => ?_)
        · rcases hy b (Finset.mem_insert_of_mem hb) with h0 | ⟨e', he', hu'⟩
          · left; simp [h0]
          · right
            refine ⟨e', fun j => ?_, hu'⟩
            rw [he' i, ← sub_smul, map_smul, he' j, smul_comm]

        · rw [hx, map_add (f := _), smul_add, he i, map_sum, Finset.smul_sum, Finset.sum_sub_distrib]; abel
        · have h2 : T j (T i x - e i • x) - ev j • (T i x - e i • x) =
              (ev i - e i) • (T j x - ev j • x) + (T j (T i x - ev i • x) - ev j • (T i x - ev i • x)) := by
            simp only [map_sub, map_smul]
            module
          rw [h2]
          exact add_mem (Submodule.smul_mem _ _ (hev j))
            (sub_mem (hTI j _ (hev i)) (Submodule.smul_mem _ _ (hev i)))
      have h3 : (ev i - e i) • x ∈ I • B := by
        have : (ev i - e i) • x = (T i x - e i • x) - (T i x - ev i • x) := by module
        rw [this]; exact sub_mem h1 (hev i)
      obtain ⟨u, hu⟩ := hu
      have h4 := Submodule.smul_mem _ ((u⁻¹ : Oˣ) : O) h3
      rwa [← hu, smul_smul, Units.inv_mul, one_smul] at h4

open Formalism.MainNotions.IntegralHeckeForms

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X)

theorem eG_idem (i : X.Tw) (j : ℕ) (b : Bool) (x : Y.Fm i j b) : eG Y i j b (eG Y i j b x) = eG Y i j b x := by
  rw [← mul_apply_eq_comp]
  unfold eG
  rw [← map_mul, Y.eAlg_idem]

theorem eG_comm (i : X.Tw) (j : ℕ) (b : Bool) (T : Module.End (FractionRing (X.O i)) (Y.Fm i j b))
    (h : ∀ g, (Y.actG i j b g).toLinearMap ∘ₗ T = T ∘ₗ (Y.actG i j b g).toLinearMap) (x : Y.Fm i j b) :
    eG Y i j b (T x) = T (eG Y i j b x) := by
  unfold eG
  induction Y.eAlg i b using MonoidAlgebra.induction_on with
  | of g =>
    simp only [MonoidAlgebra.lift_of]
    exact LinearMap.congr_fun (h g) x
  | add f g hf hg => simp only [map_add (f := _), LinearMap.add_apply, hf, hg]
  | smul r f hf => simp only [map_smul, LinearMap.smul_apply, hf]

theorem idempotentImage_stable_of_equivariant (i : X.Tw) (j : ℕ) (b : Bool) (T : Module.End (FractionRing (X.O i)) (Y.Fm i j b))
    (h : ∀ g, (Y.actG i j b g).toLinearMap ∘ₗ T = T ∘ₗ (Y.actG i j b g).toLinearMap) (x : Y.Fm i j b)
    (hx : x ∈ V0 Y i j b) : T x ∈ V0 Y i j b := by
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨T y, ?_, eG_comm Y i j b T h y⟩
  simp only [Fm0, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hy ⊢
  intro u
  have := LinearMap.congr_fun (h u) y
  simp only [LinearMap.comp_apply] at this
  rw [this, hy u, map_smul]

end GlobalTheory.EigRed
end

section

namespace GlobalTheory

open Formalism.MainNotions.IntegralHeckeForms

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {W : Type} [AddCommGroup W] [Module O W]


variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {W : Type} [AddCommGroup W] [Module O W] in
theorem _root_.GlobalTheory.relLength_ne_top_of_isLatIn {V A B : Submodule O W} (hA : _root_.Formalism.MainNotions.IntegralHeckeForms.IsLatIn A V)
    (hB : _root_.Formalism.MainNotions.IntegralHeckeForms.IsLatIn B V) : _root_.GlobalTheory.relLength A B ≠ ⊤ := by
  rw [_root_.GlobalTheory.relLength_ne_top_iff]
  obtain ⟨hAfg, hAV, -⟩ := hA
  obtain ⟨-, -, hBV⟩ := hB
  have : Module.Finite O A := Module.Finite.iff_fg.mpr hAfg
  apply _root_.GlobalTheory.isFiniteLength_of_isTorsion
  intro x
  induction x using Submodule.Quotient.induction_on with
  | H a =>
    obtain ⟨c, hc, hcB⟩ := hBV a (hAV a.2)
    refine ⟨⟨c, mem_nonZeroDivisors_of_ne_zero hc⟩, ?_⟩
    rw [Submonoid.smul_def, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact hcB


variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {W : Type} [AddCommGroup W] [Module O W] in
theorem _root_.GlobalTheory.lengthCommensurable_of_isLatIn {V A B : Submodule O W} (hA : _root_.Formalism.MainNotions.IntegralHeckeForms.IsLatIn A V)
    (hB : _root_.Formalism.MainNotions.IntegralHeckeForms.IsLatIn B V) : _root_.GlobalTheory.LengthCommensurable A B :=
  ⟨_root_.GlobalTheory.relLength_ne_top_of_isLatIn hA hB,
    _root_.GlobalTheory.relLength_ne_top_of_isLatIn hB hA⟩


variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {W : Type} [AddCommGroup W] [Module O W] in
theorem _root_.GlobalTheory.sIdx_eq_signedLength_div (l : ℕ) (A B : Submodule O W) :
    _root_.Formalism.MainNotions.IntegralHeckeForms.sIdx l A B = (_root_.GlobalTheory.signedLength A B : ℝ) /
      ((IsDiscreteValuationRing.addVal O (l : O)).toNat : ℝ) := by
  unfold _root_.Formalism.MainNotions.IntegralHeckeForms.sIdx _root_.Formalism.MainNotions.IntegralHeckeForms.lenR _root_.GlobalTheory.signedLength
  rw [← _root_.GlobalTheory.relLength_eq_length_quotient_comap,
    ← _root_.GlobalTheory.relLength_eq_length_quotient_comap]
  push_cast
  rw [sub_div]


variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {W : Type} [AddCommGroup W] [Module O W] in
theorem _root_.GlobalTheory.sIdx_add_and_mono :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (W : Type)
      [AddCommGroup W] [Module O W] (l : ℕ) (V L₁ L₂ L₃ : Submodule O W),
      _root_.Formalism.MainNotions.IntegralHeckeForms.IsLatIn L₁ V → _root_.Formalism.MainNotions.IntegralHeckeForms.IsLatIn L₂ V → _root_.Formalism.MainNotions.IntegralHeckeForms.IsLatIn L₃ V →
      _root_.Formalism.MainNotions.IntegralHeckeForms.sIdx l L₁ L₃ = _root_.Formalism.MainNotions.IntegralHeckeForms.sIdx l L₁ L₂ + _root_.Formalism.MainNotions.IntegralHeckeForms.sIdx l L₂ L₃ ∧
        (L₃ ≤ L₂ → _root_.Formalism.MainNotions.IntegralHeckeForms.sIdx l L₁ L₂ ≤ _root_.Formalism.MainNotions.IntegralHeckeForms.sIdx l L₁ L₃) := by
  intro O _ _ _ W _ _ l V L₁ L₂ L₃ h₁ h₂ h₃
  have hadd : _root_.Formalism.MainNotions.IntegralHeckeForms.sIdx l L₁ L₃ = _root_.Formalism.MainNotions.IntegralHeckeForms.sIdx l L₁ L₂ + _root_.Formalism.MainNotions.IntegralHeckeForms.sIdx l L₂ L₃ := by
    simp only [_root_.GlobalTheory.sIdx_eq_signedLength_div]
    rw [(_root_.GlobalTheory.lengthCommensurable_of_isLatIn h₁ h₂).signedLength_eq_add
      (_root_.GlobalTheory.lengthCommensurable_of_isLatIn h₂ h₃)]
    push_cast
    rw [add_div]
  refine ⟨hadd, fun hle => ?_⟩
  rw [hadd, le_add_iff_nonneg_right, _root_.GlobalTheory.sIdx_eq_signedLength_div]
  apply div_nonneg _ (Nat.cast_nonneg _)
  exact_mod_cast (_root_.GlobalTheory.lengthCommensurable_of_isLatIn h₂ h₃).signedLength_nonneg hle

end GlobalTheory
end

section

open scoped TensorProduct

namespace GlobalTheory

section

variable {O : Type} [CommRing O] (O' : Type) [CommRing O'] [Algebra O O']
  {W : Type} [AddCommGroup W] [Module O W]

theorem isLatIn_baseChange [IsDomain O'] (hinj : Function.Injective (algebraMap O O'))
    {V L : Submodule O W} (h : Formalism.MainNotions.IntegralHeckeForms.IsLatIn L V) :
    Formalism.MainNotions.IntegralHeckeForms.IsLatIn (L.baseChange O') (V.baseChange O') := by
  obtain ⟨hfg, hle, hsat⟩ := h
  refine ⟨?_, Submodule.baseChange_mono O' hle, ?_⟩
  · obtain ⟨s, rfl⟩ := hfg
    rw [Submodule.baseChange_span]
    exact Submodule.fg_span (s.finite_toSet.image _)
  · intro x hx
    rw [Submodule.baseChange_eq_span] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨v, hv, rfl⟩ := hy
      obtain ⟨c, hc, hcv⟩ := hsat v hv
      refine ⟨algebraMap O O' c, fun h0 => hc (hinj (by rw [h0, map_zero])), ?_⟩
      rw [algebraMap_smul, ← map_smul]
      exact Submodule.tmul_mem_baseChange_of_mem 1 hcv
    | zero => exact ⟨1, one_ne_zero, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨a, ha, hay⟩ := hy
      obtain ⟨b, hb, hbz⟩ := hz
      refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
      rw [smul_add]
      refine Submodule.add_mem _ ?_ ?_
      · rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ hay
      · rw [mul_smul]; exact Submodule.smul_mem _ _ hbz
    | smul a y _ hy =>
      obtain ⟨b, hb, hby⟩ := hy
      refine ⟨b, hb, ?_⟩
      rw [smul_comm]
      exact Submodule.smul_mem _ _ hby

variable [IsDomain O] [IsDiscreteValuationRing O] [IsDomain O'] [IsDiscreteValuationRing O']
  [IsLocalHom (algebraMap O O')]

theorem lenR_baseChange_subquotient (hinj : Function.Injective (algebraMap O O')) (l : ℕ)
    (A B : Submodule O W) :
    Formalism.MainNotions.IntegralHeckeForms.lenR O' l
              (A.baseChange O' ⧸ (B.baseChange O').comap (A.baseChange O').subtype) =
      Formalism.MainNotions.IntegralHeckeForms.lenR O l (A ⧸ B.comap A.subtype) := by
  haveI : FaithfulSMul O O' := (faithfulSMul_iff_algebraMap_injective O O').mpr hinj
  have h1 : Module.length O'
      (A.baseChange O' ⧸ (B.baseChange O').comap (A.baseChange O').subtype) =
      Module.length O (A ⧸ B.comap A.subtype) *
        (((IsLocalRing.maximalIdeal O').ramificationIdx O : ℕ) : ℕ∞) :=
    length_baseChange_subquotient_dvr O O' (X := W) A B
  have h2 := addVal_algebraMap (R := O) O' (l : O)
  rw [map_natCast] at h2
  have he : (((IsLocalRing.maximalIdeal O').ramificationIdx O : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (ramificationIdx_maximalIdeal_pos O O').ne'
  unfold Formalism.MainNotions.IntegralHeckeForms.lenR
  rw [h1, h2, ENat.toNat_mul, ENat.toNat_mul, ENat.toNat_coe, Nat.cast_mul, Nat.cast_mul,
    mul_div_mul_right _ _ he]

end

theorem sIdx_baseChange :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')], Function.Injective (algebraMap O O') → ∀ (W : Type) [AddCommGroup W] [Module O W] (l : ℕ) (V L₁ L₂ : Submodule O W), Formalism.MainNotions.IntegralHeckeForms.IsLatIn L₁ V → Formalism.MainNotions.IntegralHeckeForms.IsLatIn L₂ V → Formalism.MainNotions.IntegralHeckeForms.IsLatIn (L₁.baseChange O') (V.baseChange O') ∧ Formalism.MainNotions.IntegralHeckeForms.sIdx l (L₁.baseChange O') (L₂.baseChange O') = Formalism.MainNotions.IntegralHeckeForms.sIdx l L₁ L₂ := by
  intro O _ _ _ O' _ _ _ _ _ hinj W _ _ l V L₁ L₂ h₁ _
  refine ⟨isLatIn_baseChange O' hinj h₁, ?_⟩
  unfold Formalism.MainNotions.IntegralHeckeForms.sIdx
  rw [lenR_baseChange_subquotient O' hinj, lenR_baseChange_subquotient O' hinj]

end GlobalTheory
end

section

noncomputable section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.UseLoc

section Gen
variable {l : ℕ} [Fact l.Prime]

def incO {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) : ↥(OL LL) →+* ↥(OL LL') where
  toFun x := ⟨IntermediateField.inclusion h x, by
    have := x.2
    exact IsIntegral.map ((IntermediateField.inclusion h).restrictScalars ℤ_[l]) this⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

def incV {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) (k : ℕ) : (Fin k → ↥LL.1) →+ (Fin k → ↥LL'.1) :=
  (AddMonoidHom.compLeft (IntermediateField.inclusion h).toRingHom.toAddMonoidHom (Fin k))

def liftQ {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) (k : ℕ) :
    (Fin k → ↥LL.1) ⧸ stdG ↥(OL LL) ↥LL.1 k →+ (Fin k → ↥LL'.1) ⧸ stdG ↥(OL LL') ↥LL'.1 k :=
  QuotientAddGroup.lift _ ((QuotientAddGroup.mk' (stdG ↥(OL LL') ↥LL'.1 k).toAddSubgroup).comp (incV h k)) (by
    intro x hx
    obtain ⟨u, rfl⟩ := hx
    exact (QuotientAddGroup.eq_zero_iff _).2 ⟨fun j => incO h (u j), rfl⟩)

theorem liftQ_mk {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) (k : ℕ) (v : Fin k → ↥LL.1) :
    liftQ h k (Submodule.Quotient.mk v) = Submodule.Quotient.mk (incV h k v) := rfl

end Gen
end GlobalTheory.UseLoc

namespace GlobalTheory.UseLoc

section AtW
variable {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}

def locOC (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) :
    Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) ↥(OL C.LL) :=
  mapM (incO C.le) (Br.locO (D.nbr i w hw) (M.comp (decS D.nd w)))

def chiOC (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (χ : GE D.nd →* (D.nd.O i)ˣ) : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ :=
  (Units.map ((incO C.le).comp (D.nbr i w hw).eO.toRingHom).toMonoidHom).comp
    ((χ.comp (decS D.nd w)).comp (Br.iota D.nbr i w hw))

abbrev repV (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) {k : ℕ} (N : Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) ↥(OL C.LL)) :
    Representation ↥C.LL.1 (Br.G D.nbr i w hw) (Fin k → ↥C.LL.1) :=
  matRep (mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) N)

def latC (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) {k : ℕ} (N : Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) ↥(OL C.LL)) :
    Lattice (O := ↥(OL C.LL)) (repV C N) :=
  stdLatG Subtype.val_injective N

def chiT (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (c : ℕ) :
    Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ :=
  chiOC C (chiU D.nd i c * (chiU D.nd i 1)⁻¹) * θ

def embC (HW : HWOf D.loc) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hA : CaseA (D.nbr i w hw).Kw C.LL) :=
  ((HW (D.nd.l i)).W (D.nbr i w hw).Kw 1 C.LL hA.2.2).emb

end AtW
end GlobalTheory.UseLoc

namespace GlobalTheory.UseLoc

section AtW
variable {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}


open Module in
def SetC (HW : HWOf D.loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hA : CaseA (D.nbr i w hw).Kw C.LL) (lam : ↥(OL C.LL))
    (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ)
    (h w' η : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → ℕ)
    (typ : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Bool)
    (U : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Multiset ℤ) : Prop :=
  tableLineDegreeTwo.TopHyp (Br.PD D.loc D.nbr i w hw) (embC HW C hA) D.R.t h w' η typ U
                     (repV C (twistM (locOC C (WpO D.nd i ρ π)) θ)) (chiT C θ) ∧
    ∀ x, tableLineDegreeTwo.IsFull (Br.PD D.loc D.nbr i w hw) (embC HW C hA) lam (tableLineDegreeTwo.jTil U w' D.R.t)
      (tableLineDegreeTwo.resPoly (repV C (twistM (locOC C (WpO D.nd i ρ π)) θ)) (chiT C θ) D.R.t)
      (repV C (twistM (locOC C (rTwO D.nd i r x)) θ))

end AtW
end GlobalTheory.UseLoc
end
end

section

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal

theorem _root_.GlobalTheory.T.hasSum_unfolding_of_complex_invariant_integrable : ∀ {α ι : Type} [MeasurableSpace α] [Countable ι] (μ : Measure α) (𝓕 A : Set α) (c : ι → ℝ), (∀ i, 0 < c i) →
    ∀ (T : ι → α → α), (∀ i, Measurable (T i)) → ∀ (H : Set (α → α)),
    (∀ f : α → ℝ≥0∞, Measurable f → (∀ h ∈ H, ∀ x, f (h x) = f x) →
      ∫⁻ x in 𝓕, f x ∂μ = ∑' i, ENNReal.ofReal (c i) * ∫⁻ x in A, f (T i x) ∂μ) →
    ∀ B : α → ℂ, Measurable B → Integrable B (μ.restrict 𝓕) → (∀ h ∈ H, ∀ x, B (h x) = B x) →
      (∀ i, Integrable (fun x => B (T i x)) (μ.restrict A)) ∧
        HasSum (fun i => (c i : ℂ) * ∫ x in A, B (T i x) ∂μ) (∫ x in 𝓕, B x ∂μ) := by
  first | exact @GlobalTheory.UnfoldCplx.hasSum_complex | exact GlobalTheory.UnfoldCplx.hasSum_complex | (intros; apply GlobalTheory.UnfoldCplx.hasSum_complex <;> assumption)
end

section

open GlobalTheory.UnitDiscAlg

theorem _root_.GlobalTheory.T.exists_integral_idempotent_lift_newton : ∀ (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] [CompleteSpace E] (n : ℕ) (N x a : Matrix (Fin n) (Fin n) E) (ϖ : E), ‖ϖ‖ < 1 → x * N = N * x → (∀ i j, ‖x i j‖ ≤ 1) → (∀ i j, ‖a i j‖ ≤ 1) → x * x - x = ϖ • a → ∃ e a' : Matrix (Fin n) (Fin n) E, e * N = N * e ∧ a' * N = N * a' ∧ e * e = e ∧ (∀ i j, ‖e i j‖ ≤ 1) ∧ (∀ i j, ‖a' i j‖ ≤ 1) ∧ e - x = ϖ • a' := by
  first | exact @GlobalTheory.IdemLift.idem_lift | exact GlobalTheory.IdemLift.idem_lift | (intros; apply GlobalTheory.IdemLift.idem_lift <;> assumption)
end
