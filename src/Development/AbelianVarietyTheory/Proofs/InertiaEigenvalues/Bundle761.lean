module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle746
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle686
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle607
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle748
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle749
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle751
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyBreuilKisinPrismCoproduct
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle495
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle750
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicIwasawaDecompositionOffFinset
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.DiscreteValuationRing
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.EnvPush

theorem c_mem_of_mem_map {S A ι : Type} [CommRing S] [CommRing A] {s : S →+* A} {I : Ideal S}
    (TB : TopBasis s I ι) (L : Ideal S) (i : ι) {x : A} (hx : x ∈ L.map s) : TB.c i x ∈ L := by
  have key : ∀ a : A, TB.c i (a * x) ∈ L := by
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, hj, rfl⟩ := hy
      intro a
      rw [mul_comm, TB.c_mul]
      exact L.mul_mem_right _ hj
    | zero => intro a; rw [mul_zero, map_zero]; exact L.zero_mem
    | add y z _ _ hy hz => intro a; rw [mul_add, map_add (f := _)]; exact L.add_mem (hy a) (hz a)
    | smul b y _ hy => intro a; rw [smul_eq_mul, ← mul_assoc]; exact hy (a * b)
  simpa using key 1

theorem coeff_map {S A S' A' ι : Type} [CommRing S] [CommRing A] [CommRing S'] [CommRing A'] {s : S →+* A}
    {s' : S' →+* A'} {I : Ideal S} {I' : Ideal S'} (TB : TopBasis s I ι) (TB' : TopBasis s' I' ι) (g : S →+* S')
    (qf : A →+* A') (hq : ∀ y, qf (s y) = s' (g y)) (hb : ∀ i, qf (TB.b i) = TB'.b i) (hI : I.map g ≤ I')
    (hH : IsHausdorff I' S') (x : A) (α : ι) : TB'.c α (qf x) = g (TB.c α x) := by
  classical
  refine sub_eq_zero.1 (hH.haus _ fun n => SModEq.zero.2 ((Ideal.mul_top _).ge ?_))
  have hF : ∀ i, i ∉ (TB.fin x n).toFinset ∪ {α} → TB.c i x ∈ I ^ n := fun i hi => by
    by_contra h
    exact hi (Finset.mem_union_left _ ((Set.Finite.mem_toFinset _).2 h))
  have hm : qf (x - ∑ i ∈ (TB.fin x n).toFinset ∪ {α}, s (TB.c i x) * TB.b i) ∈ (I' ^ n).map s' := by
    have h1 := Ideal.mem_map_of_mem qf (TB.approx x n _ hF)
    rw [Ideal.map_map, show qf.comp s = s'.comp g from RingHom.ext hq, ← Ideal.map_map, Ideal.map_pow] at h1
    exact Ideal.map_mono (Ideal.pow_right_mono hI n) h1
  have hc := c_mem_of_mem_map TB' _ α hm
  have e : TB'.c α (qf (x - ∑ i ∈ (TB.fin x n).toFinset ∪ {α}, s (TB.c i x) * TB.b i)) =
      TB'.c α (qf x) - g (TB.c α x) := by

    rw [map_sub, map_sub, map_sum, map_sum, Finset.sum_eq_single α]
    · rw [map_mul, hq, hb, TB'.c_mul, TB'.c_self, mul_one]
    · intro i _ hi
      rw [map_mul, hq, hb, TB'.c_mul, TB'.c_ne α i (Ne.symm hi), mul_zero]
    · intro h
      exact absurd (Finset.mem_union_right _ (Finset.mem_singleton_self α)) h
  rwa [e] at hc

end GlobalTheory.BSP.EnvPush


open GlobalTheory.BSP.EnvPush in
theorem GlobalTheory.BSP.envPush_dvd_l : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) (An : Env bk (ainfObj K) (bk.ev bk.E) (bk.ev X)) (q : Hom En.Q An.Q), q.comp En.inl = An.inl.comp bk.ι → q.comp En.inr = An.inr → ∀ x : En.Q.A, ((l : ℕ) : An.Q.A) ∣ q.f x → ((l : ℕ) : En.Q.A) ∣ x := by
  intro l _ K bk En An q hl hr x hx
  have hql : ∀ y : bk.prism.A, q.f (En.inl.f y) = An.inl.f (bk.ι.f y) := fun y =>
    congrArg (fun h : Hom bk.prism An.Q => h.f y) hl
  have hqr : ∀ y : bk.prism.A, q.f (En.inr.f y) = An.inr.f y := fun y =>
    congrArg (fun h : Hom bk.prism An.Q => h.f y) hr

  have hw : q.f En.w = An.w := by
    have e1 : q.f (En.inr.f (bk.toP X)) = An.inr.f (bk.toP X) := hqr _
    have e2 : En.inr.f (bk.toP X) = En.inl.f (bk.toP X) + En.inl.f (bk.toP bk.E) * En.w := En.w_eq
    have e3 : An.inr.f (bk.toP X) = An.inl.f (bk.ι.f (bk.toP X)) + An.inl.f (bk.ι.f (bk.toP bk.E)) * An.w :=
      An.w_eq
    have e4 : q.f (En.inl.f (bk.toP X) + En.inl.f (bk.toP bk.E) * En.w) =
        An.inl.f (bk.ι.f (bk.toP X)) + An.inl.f (bk.ι.f (bk.toP bk.E)) * q.f En.w :=
      (q.f.map_add _ _).trans (congrArg₂ (· + ·) (hql _) ((q.f.map_mul _ _).trans (congrArg (· * q.f En.w) (hql _))))
    have e5 := add_left_cancel (e4.symm.trans ((congrArg q.f e2).symm.trans (e1.trans e3)))
    have key : ∀ (b u v : An.Q.A), b ∈ nonZeroDivisors An.Q.A → b * u = b * v → u = v := fun b u v hb h =>
      sub_eq_zero.1 ((mul_left_mem_nonZeroDivisors_eq_zero_iff hb).1 (by rw [mul_sub, h, sub_self]))
    have hnz : An.inl.f (bk.ι.f (bk.toP bk.E)) ∈ nonZeroDivisors An.Q.A :=
      (GlobalTheory.T.breuilKisin_two_homs_E_regular_associated l K bk An.Q (An.inl.comp bk.ι) (An.inl.comp bk.ι)).1
    exact key _ _ _ hnz e5

  have hδ : ∀ (n : ℕ) (y : En.Q.A), q.f (En.Q.D.δ^[n] y) = An.Q.D.δ^[n] (q.f y) := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ n ih =>
      intro y
      exact (congrArg q.f (Function.iterate_succ_apply' _ n y)).trans ((q.f_δ _).trans
        ((congrArg An.Q.D.δ (ih y)).trans (Function.iterate_succ_apply' _ n _).symm))
  have hb : ∀ α, q.f (En.tb.b α) = An.tb.b α := by
    intro α
    refine (congrArg q.f (En.tb_b α)).trans ((map_finsuppProd q.f _ _).trans (Eq.trans ?_ (An.tb_b α).symm))
    exact Finsupp.prod_congr fun i _ =>
      (map_pow q.f _ _).trans (congrArg (· ^ α.1 i) ((hδ i En.w).trans (congrArg _ hw)))

  have hJ : (Ideal.span {((l : ℕ) : bk.prism.A)} ⊔ bk.prism.I).map bk.ι.f ≤
      Ideal.span {((l : ℕ) : (ainfObj K).A)} ⊔ (ainfObj K).I := by
    refine Ideal.map_le_iff_le_comap.2 (sup_le (Ideal.span_le.2 (Set.singleton_subset_iff.2 ?_))
      fun y hy => Ideal.mem_sup_right (bk.ι.f_I y hy))
    show bk.ι.f ((l : ℕ) : bk.prism.A) ∈ Ideal.span {((l : ℕ) : (ainfObj K).A)} ⊔ (ainfObj K).I
    rw [map_natCast]
    exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
  have hH : IsHausdorff (Ideal.span {((l : ℕ) : (ainfObj K).A)} ⊔ (ainfObj K).I) (ainfObj K).A :=
    (ainfObj K).complete.toIsHausdorff

  have key : ∀ α, An.tb.c α (q.f x) = bk.ι.f (En.tb.c α x) := fun α =>
    coeff_map En.tb An.tb bk.ι.f q.f hql hb hJ hH x α

  obtain ⟨y, hy⟩ := hx
  have hl' : ∀ α, ((l : ℕ) : bk.S) ∣ En.tb.c α x := fun α => by
    apply (GlobalTheory.T.breuilKisin_evW_isUnit_injective_dvd l K bk).2.2
    refine ⟨An.tb.c α y, ?_⟩
    calc bk.ι.f (En.tb.c α x) = An.tb.c α (q.f x) := (key α).symm
      _ = An.tb.c α (An.inl.f ((l : ℕ) : (ainfObj K).A) * y) := by rw [hy, map_natCast]
      _ = ((l : ℕ) : (ainfObj K).A) * An.tb.c α y := An.tb.c_mul α _ y
  have h := (GlobalTheory.T.dvd_iff_dvd_coeff_breuilKisin l K bk En.Q.A (En.inl.f : bk.S →+* En.Q.A) (Digits l) En.tb ((l : ℕ) : bk.S) x).2 hl'
  have hg : ∀ {R A : Type} [CommRing R] [CommRing A] (s : R →+* A) (y : A) (n : ℕ), s n ∣ y → (n : A) ∣ y :=
    fun s y n h => (map_natCast s n) ▸ h
  exact hg _ _ _ h
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.SatLattice

section abstract

variable {R : Type} [CommRing R] [IsDomain R] {π : R} (O : Subring R)

theorem pid_of_fact (hπ : Irreducible π) (hO : π ∈ O)
    (h4 : ∀ w ∈ O, w ≠ 0 → ∃ (k : ℕ) (v v' : R), v ∈ O ∧ v' ∈ O ∧ v * v' = 1 ∧ w = π ^ k * v) :
    IsPrincipalIdealRing O := by
  have hu : ∀ a : O, IsUnit (a : R) → IsUnit a := by
    intro a ha
    obtain ⟨k, v, v', hv, hv', h1, h2⟩ := h4 a a.2 ha.ne_zero
    rcases k with _ | k
    · refine IsUnit.of_mul_eq_one (⟨v', hv'⟩ : O) (Subtype.ext ?_)
      simp [h2, h1]
    · exfalso
      rw [h2, pow_succ', mul_assoc] at ha
      exact hπ.not_isUnit (isUnit_of_mul_isUnit_left ha)
  have hirr : Irreducible (⟨π, hO⟩ : O) := by
    refine ⟨fun h => hπ.not_isUnit (h.map O.subtype), fun a b hab => ?_⟩
    exact (hπ.isUnit_or_isUnit (congrArg Subtype.val hab)).imp (hu a) (hu b)
  have : IsDiscreteValuationRing O := by
    refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨_, hirr, ?_⟩
    intro x hx
    obtain ⟨k, v, v', hv, hv', h1, h2⟩ := h4 x x.2 (fun h => hx (Subtype.ext h))
    refine ⟨k, ⟨⟨v, hv⟩, ⟨v', hv'⟩, Subtype.ext h1, Subtype.ext (by simp [mul_comm v' v, h1])⟩, Subtype.ext ?_⟩
    simp [h2]
  infer_instance

theorem sat_pow (hπ : π ≠ 0) (h1 : ∀ w ∈ O, π ∣ w → ∃ v ∈ O, w = π * v) (n : ℕ) (x : R)
    (hx : π ^ n * x ∈ O) : x ∈ O := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    obtain ⟨v, hv, h⟩ := h1 _ hx ⟨π ^ n * x, by ring⟩
    refine ih ?_
    have : π ^ n * x = v := mul_left_cancel₀ hπ (by rw [← h]; ring)
    rwa [this]

def divSub {d : ℕ} (Y : Matrix (Fin d) (Fin d) R) (a : R) : Submodule O (Fin d → O) where
  carrier := {x | ∀ i, a ∣ (Y *ᵥ fun j => (x j : R)) i}
  zero_mem' i := by
    simp [Matrix.mulVec, dotProduct]
  add_mem' {x y} hx hy i := by
    have : (fun j => ((x + y) j : R)) = (fun j => (x j : R)) + fun j => (y j : R) := rfl
    rw [this, Matrix.mulVec_add]
    exact dvd_add (hx i) (hy i)
  smul_mem' c x hx i := by
    have : (fun j => ((c • x) j : R)) = (c : R) • fun j => (x j : R) := rfl
    rw [this, Matrix.mulVec_smul]
    exact Dvd.dvd.mul_left (hx i) _

theorem exists_basis_matrix [IsPrincipalIdealRing O] {d : ℕ} (Y : Matrix (Fin d) (Fin d) R) (a : R) (ha : a ≠ 0)
    (haO : a ∈ O) :
    ∃ P : Matrix (Fin d) (Fin d) R, (∀ i j, P i j ∈ O) ∧ P.det ≠ 0 ∧ (∀ i j, a ∣ (Y * P) i j) ∧
      ∀ x : Fin d → R, (∀ i, x i ∈ O) → (∀ i, a ∣ (Y *ᵥ x) i) →
        ∃ w : Fin d → R, (∀ i, w i ∈ O) ∧ x = P *ᵥ w := by
  set N := divSub O Y a with hN
  have hmem : ∀ v : Fin d → O, (⟨a, haO⟩ : O) • v ∈ N := by
    intro v i
    have : (fun j => (((⟨a, haO⟩ : O) • v) j : R)) = a • fun j => (v j : R) := rfl
    rw [this, Matrix.mulVec_smul]
    exact Dvd.intro _ rfl
  let f : (Fin d → O) →ₗ[O] N := LinearMap.codRestrict N ((⟨a, haO⟩ : O) • LinearMap.id) hmem
  have hf : Function.Injective f := by
    intro v w h
    funext i
    have := congrArg (fun z : N => ((z.1 i : O) : R)) h
    exact Subtype.ext (mul_left_cancel₀ ha this)
  have hr : Module.finrank O N = d := by
    apply le_antisymm
    · simpa using N.finrank_le
    · simpa using LinearMap.finrank_le_finrank_of_injective hf
  let b := Module.finBasisOfFinrankEq O N hr
  let P : Matrix (Fin d) (Fin d) R := Matrix.of fun i j => ((b j).1 i : R)
  have hspan : ∀ x : Fin d → R, (∀ i, x i ∈ O) → (∀ i, a ∣ (Y *ᵥ x) i) →
        ∃ w : Fin d → R, (∀ i, w i ∈ O) ∧ x = P *ᵥ w := by
    intro x hx hd
    let z : N := ⟨fun i => ⟨x i, hx i⟩, hd⟩
    refine ⟨fun j => (b.repr z j : R), fun j => (b.repr z j).2, funext fun i => ?_⟩
    have := congrArg (fun z : N => ((z.1 i : O) : R)) (b.sum_repr z)
    refine Eq.trans this.symm ?_
    rw [Submodule.coe_sum, Finset.sum_apply, AddSubmonoidClass.coe_finsetSum]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  refine ⟨P, fun i j => ((b j).1 i).2, ?_, fun i j => (b j).2 i, hspan⟩
  have hcol : ∀ j : Fin d, ∃ w : Fin d → R, (∀ i, w i ∈ O) ∧ a • (Pi.single j 1 : Fin d → R) = P *ᵥ w := by
    intro j
    refine hspan _ (fun i => ?_) (fun i => ?_)
    · by_cases h : i = j
      · simp [h, haO]
      · simp [h]
    · rw [Matrix.mulVec_smul]
      exact Dvd.intro _ rfl
  choose w _ hw using hcol
  have hPQ : P * Matrix.of (fun i j => w j i) = a • (1 : Matrix (Fin d) (Fin d) R) := by
    ext i j
    have := congrFun (hw j) i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, Pi.single_apply] at this
    simp [Matrix.mul_apply, ← this, Matrix.one_apply]
  intro h0
  have := congrArg Matrix.det hPQ
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one] at this
  exact pow_ne_zero _ ha this.symm

theorem lattice_abstract [IsPrincipalIdealRing O] (hπ : π ≠ 0) (hO : π ∈ O)
    (h1 : ∀ w ∈ O, π ∣ w → ∃ v ∈ O, w = π * v) {d : ℕ} (Y : Matrix (Fin d) (Fin d) R) (c : ℕ) (u : Rˣ)
    (hdet : Y.det = π ^ c * u) :
    ∃ (m : ℕ) (P Y' : Matrix (Fin d) (Fin d) R), (∀ i j, P i j ∈ O) ∧ P.det ≠ 0 ∧ π ^ m • Y' = Y * P ∧
      (∀ v : Fin d → R, (∀ i, v i ∈ O) → ∀ n : ℕ, (∀ i, π ^ n ∣ (Y *ᵥ v) i) →
        ∃ w : Fin d → R, (∀ i, w i ∈ O) ∧ π ^ m • v = π ^ n • (P *ᵥ w)) ∧
      ∀ w : Fin d → R, (∀ i, w i ∈ O) → (∀ i, π ∣ (Y' *ᵥ w) i) → ∀ i, π ∣ w i := by
  obtain ⟨P, hPO, hP, hdv, hspan⟩ := exists_basis_matrix O Y (π ^ c) (pow_ne_zero _ hπ) (O.pow_mem hO c)
  choose y hy using hdv
  have hY' : π ^ c • Matrix.of y = Y * P := by
    ext i j
    simp [hy]
  have key : ∀ v : Fin d → R, (∀ i, v i ∈ O) → ∀ n : ℕ, (∀ i, π ^ n ∣ (Y *ᵥ v) i) →
        ∃ w : Fin d → R, (∀ i, w i ∈ O) ∧ π ^ c • v = π ^ n • (P *ᵥ w) := by
    intro v hv n hn
    choose z hz using hn
    have hz' : Y *ᵥ v = π ^ n • z := funext hz
    let x : Fin d → R := ((u⁻¹ : Rˣ) : R) • (Y.adjugate *ᵥ z)
    have hx : π ^ c • v = π ^ n • x := by
      have h := congrArg (fun t => ((u⁻¹ : Rˣ) : R) • (Y.adjugate *ᵥ t)) hz'
      simp only [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.mulVec_smul, Matrix.smul_mulVec,
        Matrix.one_mulVec, hdet] at h
      rw [smul_smul, mul_left_comm, Units.inv_mul, mul_one, smul_comm] at h
      exact h
    have hYx : Y *ᵥ x = π ^ c • z := by
      simp only [x, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.mulVec_smul, Matrix.smul_mulVec,
        Matrix.one_mulVec, hdet]
      rw [smul_smul, mul_left_comm, Units.inv_mul, mul_one]
    obtain ⟨w, hw, hxw⟩ := hspan x (fun i => sat_pow O hπ h1 n _ (by
      have := congrFun hx i
      simp only [Pi.smul_apply, smul_eq_mul] at this
      rw [← this]
      exact O.mul_mem (O.pow_mem hO c) (hv i))) (fun i => by rw [hYx]; exact Dvd.intro _ rfl)
    exact ⟨w, hw, by rw [hx, hxw]⟩
  refine ⟨c, P, Matrix.of y, hPO, hP, hY', key, fun w hw hd => ?_⟩
  obtain ⟨w', -, h⟩ := key (P *ᵥ w) (fun i => by
    simp only [Matrix.mulVec, dotProduct]
    exact O.sum_mem fun j _ => O.mul_mem (hPO i j) (hw j)) (c + 1) (fun i => by
    rw [Matrix.mulVec_mulVec, ← hY', Matrix.smul_mulVec, pow_succ]
    exact mul_dvd_mul_left _ (hd i))
  have h2 : P *ᵥ (w - π • w') = 0 := by
    funext i
    have := congrFun h i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    refine mul_left_cancel₀ (pow_ne_zero c hπ) ?_
    linear_combination this
  have h3 := Matrix.eq_zero_of_mulVec_eq_zero hP h2
  intro i
  exact ⟨w' i, sub_eq_zero.1 (congrFun h3 i)⟩

end abstract

theorem exists_lattice_basis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (Y1 : Matrix (Fin d) (Fin d) (WCb l)), Y1.det ≠ 0 → ∃ (m : ℕ) (P Y' : Matrix (Fin d) (Fin d) (WCb l)), (∀ i j, P i j ∈ bk.OE) ∧ P.det ≠ 0 ∧ (l : WCb l) ^ m • Y' = Y1 * P ∧ (∀ v : Fin d → WCb l, (∀ i, v i ∈ bk.OE) → ∀ n : ℕ, (∀ i, (l : WCb l) ^ n ∣ (Y1 *ᵥ v) i) → ∃ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) ∧ (l : WCb l) ^ m • v = (l : WCb l) ^ n • (P *ᵥ w)) ∧ ∀ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) → (∀ i, (l : WCb l) ∣ (Y' *ᵥ w) i) → ∀ i, (l : WCb l) ∣ w i := by
  intro l _ K bk d Y1 hY
  obtain ⟨h1, -, -, h4, -⟩ := GlobalTheory.T.integral_elements_unit_factorization l K bk
  have hirr : Irreducible (l : WCb l) := WittVector.irreducible l
  have : PerfectRing (Cb l) l := by
    refine PerfectRing.ofSurjective _ l fun x => ?_
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := OCb l) x
    obtain ⟨a', rfl⟩ := surjective_frobenius (OCb l) l a
    obtain ⟨b', rfl⟩ := surjective_frobenius (OCb l) l b
    exact ⟨algebraMap (OCb l) (Cb l) a' / algebraMap (OCb l) (Cb l) b', by
      simp [frobenius_def, div_pow, map_pow]⟩
  obtain ⟨c, u, hu⟩ := WittVector.exists_eq_pow_p_mul' Y1.det hY
  have := pid_of_fact bk.OE hirr (natCast_mem _ l) h4
  exact lattice_abstract bk.OE hirr.ne_zero (natCast_mem _ l) h1 Y1 c u hu

end GlobalTheory.SatLattice
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.breuilKisin_disc_cocycle_frobenius_equation : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d M N : ℕ) (Y : Matrix (Fin d) (Fin d) (Ainf l)) (A A' : Matrix (Fin d) (Fin d) bk.S), A * A' = bk.E ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) bk.S) → bk.ev bk.E ^ N • Y.map WittVector.frobenius = bk.ev bk.E ^ M • (Y * A.map bk.ev) → (Y.map bk.iA).det ≠ 0 → ∀ (g : GQ l) (G Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA g) G → IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius Φ → ∀ (w : (Ainf l)ˣ), Per.σA g (bk.ev bk.E) = bk.ev bk.E * w → ∀ (P : Matrix (Fin d) (Fin d) (Ainf l)), P.map WittVector.frobenius = P → ∀ (e : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)), bk.iA (Per.σA g τ) ^ M • (Y.map bk.iA * e) = bk.iA τ ^ M • (P.map bk.iA * (Y.map (Per.σA g)).map bk.iA) → bk.iS bk.E ^ (2 * N) • e = (((↑w⁻¹ : Ainf l) ^ N) • A.map bk.ev).map bk.iA * e.map Φ * ((A'.map bk.ev).map (Per.σA g)).map bk.iA := by
  first | (exact @GlobalTheory.BSP.CocycleFrob.frob_eq) | (exact GlobalTheory.BSP.CocycleFrob.frob_eq) | (intros; apply GlobalTheory.BSP.CocycleFrob.frob_eq  <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_right_inverse_mod_pow_of_ev : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (M : ℕ), ∃ r : ℕ, ∀ (d d' n : ℕ) (R : Matrix (Fin d) (Fin d') (bk.S)) (a : Matrix (Fin d') (Fin d) (Ainf l)), (∀ i j, (l : Ainf l) ^ n ∣ (R.map bk.ev * a - τ ^ M • (1 : Matrix (Fin d) (Fin d) (Ainf l))) i j) → ∃ G : Matrix (Fin d') (Fin d) (bk.S), (∀ i j, (l : bk.S) ^ n ∣ (R * G - (l : bk.S) ^ r • (1 : Matrix (Fin d) (Fin d) (bk.S))) i j) := by
  first | exact @GlobalTheory.BKLim.descend_rightInverse | exact GlobalTheory.BKLim.descend_rightInverse | (intros; apply GlobalTheory.BKLim.descend_rightInverse; all_goals assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

theorem _root_.GlobalTheory.T.crystallineLattice_frobenius_inverse_matrix : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ), ∀ Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius Φ → (s.X' * s.F.map (C : Wq l bk.a →+* bk.S) * s.X.map (frobS l bk.a)).map bk.iS * s.W'.map Φ = (((l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N) * bk.iS bk.E ^ (2 * s.N)) • s.W' := by
  first | exact @GlobalTheory.BSP.seed_frob_inverse | exact GlobalTheory.BSP.seed_frob_inverse | (intros; apply GlobalTheory.BSP.seed_frob_inverse <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.toDisc_injective_and_nonZeroDivisors_of_topBasis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A) (ι : Type), TopBasis s bk.J ι → Function.Injective (toDisc l (s X) bk.ρ₀) ∧ toDisc l (s X) bk.ρ₀ (s bk.E) ∈ nonZeroDivisors (Disc l (s X) bk.ρ₀) ∧ (l : A) ∈ nonZeroDivisors A ∧ ∀ F : bk.DS bk.ρ₀ →+* Disc l (s X) bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) s F → Function.Injective F := by
  first | exact @GlobalTheory.BSP.topBasis_disc_regular | exact GlobalTheory.BSP.topBasis_disc_regular | (intros; apply GlobalTheory.BSP.topBasis_disc_regular <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.breuilKisin_descent_coefficients_ainf_mod_pow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' n : ℕ) (R : Matrix (Fin d) (Fin d') (WCb l)) (x : Fin d → WCb l) (a : Fin d' → Ainf l), (∀ i j, R i j ∈ bk.OE) → (∀ i, x i ∈ bk.OE) → (∀ i, (l : WCb l) ^ n ∣ (x - R *ᵥ fun j => inclW l (a j)) i) → ∃ s : Fin d' → bk.S, ∀ i, (l : WCb l) ^ n ∣ (x - R *ᵥ fun j => bk.evW (s j)) i := by
  first | exact @GlobalTheory.descentCoefficients | exact GlobalTheory.descentCoefficients | (intros; apply GlobalTheory.descentCoefficients <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.smith_form_coefficientRing_image_or_prime_dvd_row : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), IsDiscreteValuationRing ↥bk.OE → ∀ (d' : ℕ) (P : Matrix (Fin d') (Fin d') (WCb l)), (∀ i j, P i j ∈ bk.OE) → ∃ U Uinv : Matrix (Fin d') (Fin d') (WCb l), (∀ i j, U i j ∈ bk.OE) ∧ (∀ i j, Uinv i j ∈ bk.OE) ∧ Uinv * U = 1 ∧ U * Uinv = 1 ∧ ∀ j, (∃ w : Fin d' → WCb l, (fun i => U i j) = P *ᵥ w) ∨ (∀ k, (l : WCb l) ∣ (Uinv * P) j k) := by
  first | exact @GlobalTheory.SmithOE.main | exact GlobalTheory.SmithOE.main | (intros; apply GlobalTheory.SmithOE.main; all_goals assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

theorem _root_.GlobalTheory.T.crystallineLattice_frobenius_rational_columns : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ) (Y1 : Matrix (Fin d) (Fin d) (Ainf l)) (Z1 : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), Y1.det ≠ 0 → (∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W * Z1.map j = Y1.map bk.iA) → ∃ (δ : bk.S) (A1 : Matrix (Fin d) (Fin d) (bk.S)), δ ≠ 0 ∧ bk.ev δ • Y1.map WittVector.frobenius = Y1 * A1.map bk.ev := by
  first | exact @GlobalTheory.BSP.FrobRational.main | exact GlobalTheory.BSP.FrobRational.main | (intros; apply GlobalTheory.BSP.FrobRational.main <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.nonempty_breuilKisinPrismCoproduct : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)) (d p : B.A), IsFrame bk B d p → Nonempty (Env bk B d p) := by
  first | exact @GlobalTheory.BSP.nonempty_env | exact GlobalTheory.BSP.nonempty_env | (intros; apply GlobalTheory.BSP.nonempty_env <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal

theorem _root_.GlobalTheory.T.exists_tl_inv_mul_mem_C0_off_finset : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ), (∀ v, IsUnifV E v (ϖ v : v.adicCompletion E)) →
    ∀ g : GA E n, ∃ l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ), (∀ v ∈ S, l v = 0) ∧
      (GlobalTheory.CellDec.tl n ϖ l)⁻¹ * g ∈ GlobalTheory.CellDec.C0 E n S := by
  first | exact @GlobalTheory.CellDec.adelic_iwasawa_decomposition_off_finset | exact GlobalTheory.CellDec.adelic_iwasawa_decomposition_off_finset | (intros; apply GlobalTheory.CellDec.adelic_iwasawa_decomposition_off_finset <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal

theorem _root_.GlobalTheory.T.adelic_iwasawa_cells_disjoint_off_finset : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ), (∀ v, IsUnifV E v (ϖ v : v.adicCompletion E)) →
    ∀ (l l' : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (g : GA E n), (∀ v ∈ S, l v = 0) → (∀ v ∈ S, l' v = 0) →
      (GlobalTheory.CellDec.tl n ϖ l)⁻¹ * g ∈ GlobalTheory.CellDec.C0 E n S → (GlobalTheory.CellDec.tl n ϖ l')⁻¹ * g ∈ GlobalTheory.CellDec.C0 E n S → l = l' := by
  first | exact @GlobalTheory.CellDec.eq_of_tl_inv_mul_mem_C0_of_tl_inv_mul_mem_C0 | exact GlobalTheory.CellDec.eq_of_tl_inv_mul_mem_C0_of_tl_inv_mul_mem_C0 | (intros; apply GlobalTheory.CellDec.eq_of_tl_inv_mul_mem_C0_of_tl_inv_mul_mem_C0 <;> assumption)
end
