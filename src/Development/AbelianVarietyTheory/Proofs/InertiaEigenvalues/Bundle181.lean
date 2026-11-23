module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle159
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle151
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle156
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle161
public import ReciprocityTheory.NeutralLocalFields.Bundle001
public import Mathlib.Topology.LocallyConstant.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle162
public import ReciprocityTheory.Hypotheses.GalCohDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransferCardH0H1Eq
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.Artinian.Instances
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle155
public import Formalism.CharacterColumnKernels.Bundle001
import Formalism.WachLatticeTwists.LatticeDualFibres.Statement
public import Mathlib.RingTheory.Filtration
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.closing_numerical_inequality_theoremB : ∀ (CA C b l S η Rw Tb Vd : ℝ) (f r t m p : ℕ), 13 * max CA 0 ≤ C → 260 * f ^ 2 * t ^ 2 * (r + t) ≤ p → 1 ≤ t → 1 ≤ f → m ≤ r → 3 ≤ l → 0 ≤ S → 0 ≤ η → 0 < b → 1 < Real.log b → Rw ≤ max CA 0 * (3 * (f : ℝ) * r * (4 * b / l + 2 * S + 2 * Real.logb l (2 * b) + 1 + η + t) + 6 * (f : ℝ) * m * (2 * b + 1)) + f → Tb ≤ 240 * (t : ℝ) ^ 2 * (f : ℝ) ^ 2 * ((r : ℝ) + t) * Real.log b → Vd ≤ 4 * ((r : ℝ) + t) * t → Rw + Tb + Vd ≤ C * f * (r * (b / l + S + t + η + Real.log b) + m * b) + (p : ℝ) * Real.log b := by
  first | exact @GlobalTheory.closing_numerical_inequality | exact GlobalTheory.closing_numerical_inequality | (intros; apply GlobalTheory.closing_numerical_inequality <;> assumption)
end

section

open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)

namespace GlobalTheory.ZpHomAdic

open IsLocalRing Filter Topology

theorem isPrecomplete_of_compact {O : Type} [CommRing O] [IsLocalRing O] [TopologicalSpace O]
    [IsTopologicalRing O] [CompactSpace O] (hA : IsAdic (maximalIdeal O)) :
    IsPrecomplete (maximalIdeal O) O := by
  refine ⟨fun f hf => ?_⟩
  obtain ⟨L, -, hL⟩ := (isCompact_univ (X := O)).exists_clusterPt (f := Filter.map f atTop)
    (le_principal_iff.2 univ_mem)
  refine ⟨L, fun n => ?_⟩
  have hopen : IsOpen ((maximalIdeal O ^ n : Ideal O) : Set O) := (isAdic_iff.1 hA).1 n
  have hclosed : IsClosed ((maximalIdeal O ^ n : Ideal O) : Set O) :=
    AddSubgroup.isClosed_of_isOpen ((maximalIdeal O ^ n).toAddSubgroup) hopen
  have hS : IsClosed {y : O | f n - y ∈ maximalIdeal O ^ n} :=
    hclosed.preimage (continuous_const.sub continuous_id)
  have hmem : {y : O | f n - y ∈ maximalIdeal O ^ n} ∈ Filter.map f atTop := by
    refine Filter.mem_map.2 (Filter.mem_atTop_sets.2 ⟨n, fun k hk => ?_⟩)
    have := hf hk
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
    exact this
  have hL' : L ∈ closure {y : O | f n - y ∈ maximalIdeal O ^ n} :=
    mem_closure_iff_clusterPt.2 (hL.mono (le_principal_iff.2 hmem))
  rw [hS.closure_eq] at hL'
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
  exact hL'

theorem isHausdorff_dvr {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] :
    IsHausdorff (maximalIdeal O) O := by
  refine ⟨fun x hx => ?_⟩
  rw [← Ideal.mem_bot, ← Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal O)
    (maximalIdeal.isMaximal O).ne_top, Ideal.mem_iInf]
  intro n
  have := hx n
  rwa [SModEq.zero, smul_eq_mul, Ideal.mul_top] at this

theorem ringHom_zmod_apply {N : ℕ} [NeZero N] {R : Type*} [Ring R] (ψ : ZMod N →+* R) (z : ZMod N) :
    ψ z = ((z.val : ℕ) : R) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val z]
  exact map_natCast ψ _

theorem val_toZModPow_sub_mem {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] {m n : ℕ} (h : m ≤ n)
    (x : ℤ_[p]) :
    ((PadicInt.toZModPow n x).val : O) - ((PadicInt.toZModPow m x).val : O) ∈
      Ideal.span {(p : O) ^ m} := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  haveI : NeZero (p ^ m) := ⟨pow_ne_zero _ hp⟩
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ hp⟩
  have h1 : (((PadicInt.toZModPow n x).val : ℕ) : ZMod (p ^ m)) =
      (((PadicInt.toZModPow m x).val : ℕ) : ZMod (p ^ m)) := by
    rw [ZMod.natCast_val, ZMod.natCast_zmod_val, PadicInt.cast_toZModPow m n h]
  rw [ZMod.natCast_eq_natCast_iff] at h1
  obtain ⟨c, hc⟩ := (Nat.modEq_iff_dvd.1 h1.symm)
  rw [Ideal.mem_span_singleton]
  refine ⟨(c : O), ?_⟩
  have := congrArg (fun t : ℤ => (t : O)) hc
  push_cast at this
  exact this

end GlobalTheory.ZpHomAdic

namespace GlobalTheory.ZpHomAdic
open IsLocalRing

noncomputable def zmodToQuot (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsLocalRing O]
    (hp : (p : O) ∈ maximalIdeal O) (n : ℕ) : ZMod (p ^ n) →+* O ⧸ maximalIdeal O ^ n :=
  (Ideal.Quotient.lift (Ideal.span {((p ^ n : ℕ) : ℤ)}) (Int.castRingHom _) (fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, map_natCast, Nat.cast_pow, ← map_natCast (Ideal.Quotient.mk (maximalIdeal O ^ n)) p,
      ← map_pow, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow hp n), mul_zero])).comp
    (Int.quotientSpanNatEquivZMod (p ^ n)).symm.toRingHom

theorem exists_ringHom_padicInt {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [TopologicalSpace O] (hT : IsTopologicalRing O)
    (_hC : CompactSpace O) (_hH : T2Space O) (hA : IsAdic (maximalIdeal O))
    (hp : (p : O) ∈ maximalIdeal O) :
    ∃ ι : ℤ_[p] →+* O, ∀ (x : ℤ_[p]) (k : ℕ),
      ι x - ((PadicInt.toZModPow k x).val : O) ∈ Ideal.span {(p : O) ^ k} := by
  haveI := hT
  haveI : IsAdicComplete (maximalIdeal O) O :=
    { toIsHausdorff := isHausdorff_dvr, toIsPrecomplete := isPrecomplete_of_compact hA }
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  haveI hNZ : ∀ n, NeZero (p ^ n) := fun n => ⟨pow_ne_zero _ hp0⟩
  let f : (n : ℕ) → ℤ_[p] →+* O ⧸ maximalIdeal O ^ n := fun n =>
    (zmodToQuot p O hp n).comp (PadicInt.toZModPow n)
  have hfx : ∀ n x, f n x = Ideal.Quotient.mk _ ((PadicInt.toZModPow n x).val : O) := by
    intro n x
    show zmodToQuot p O hp n _ = _
    rw [ringHom_zmod_apply, map_natCast]
  have hf : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorPow (maximalIdeal O) hle).comp (f n) = f m := by
    intro m n hle
    ext x
    rw [RingHom.comp_apply, hfx, hfx, Ideal.Quotient.factor_mk, Ideal.Quotient.eq]
    exact Ideal.span_singleton_le_iff_mem _ |>.2 (Ideal.pow_mem_pow hp m)
      (val_toZModPow_sub_mem hle x)
  refine ⟨IsAdicComplete.liftRingHom (maximalIdeal O) f hf, fun x k => ?_⟩
  set ι := IsAdicComplete.liftRingHom (maximalIdeal O) f hf
  have hι : ∀ n, ι x - ((PadicInt.toZModPow n x).val : O) ∈ maximalIdeal O ^ n := by
    intro n
    rw [← Ideal.Quotient.eq, IsAdicComplete.mk_liftRingHom, hfx]
  set J : Ideal O := Ideal.span {(p : O) ^ k}
  rw [← Submodule.Quotient.mk_eq_zero (p := J), ← Submodule.mem_bot O,
    ← Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := O ⧸ J) (maximalIdeal O)
      (maximalIdeal.isMaximal O).ne_top, Submodule.mem_iInf]
  intro n
  have hle : maximalIdeal O ^ max n k • (⊤ : Submodule O (O ⧸ J)) ≤ maximalIdeal O ^ n • ⊤ :=
    Submodule.smul_mono_left (Ideal.pow_le_pow_right (le_max_left n k))
  refine hle ?_
  have hsplit : ι x - ((PadicInt.toZModPow k x).val : O) =
      (ι x - ((PadicInt.toZModPow (max n k) x).val : O)) +
      (((PadicInt.toZModPow (max n k) x).val : O) - ((PadicInt.toZModPow k x).val : O)) := by ring
  rw [hsplit, Submodule.Quotient.mk_add,
    (Submodule.Quotient.mk_eq_zero J).2 (val_toZModPow_sub_mem (le_max_right n k) x), add_zero,
    ← mul_one (ι x - _), ← smul_eq_mul, Submodule.Quotient.mk_smul]
  exact Submodule.smul_mem_smul (hι _) Submodule.mem_top

theorem zp_ringHom : ∀ {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O], IsTopologicalRing O → CompactSpace O → T2Space O → IsAdic (IsLocalRing.maximalIdeal O) → (p : O) ∈ IsLocalRing.maximalIdeal O → ∃ ι : ℤ_[p] →+* O, ∀ (x : ℤ_[p]) (k : ℕ), ι x - ((PadicInt.toZModPow k x).val : O) ∈ Ideal.span {(p : O) ^ k} :=
  fun hT hC hH hA hp => exists_ringHom_padicInt hT hC hH hA hp

end GlobalTheory.ZpHomAdic
end

section

open Matrix Polynomial

namespace GlobalTheory.IsoIdem

theorem eq_zero_of_pow_eq_zero {E : Type} [Field E] {r : ℕ} (A : Matrix (Fin r) (Fin r) E)
    (hs : A.charpoly.Separable) (y : Matrix (Fin r) (Fin r) E) (hy : y * A = A * y) (k : ℕ)
    (hk : y ^ k = 0) : y = 0 := by
  obtain ⟨q, rfl⟩ := GlobalTheory.CommSep.eq_aeval_of_commute_of_separable A hs y hy
  rcases k with _ | k
  · rw [pow_zero] at hk
    exact eq_zero_of_zero_eq_one hk.symm _
  have hsq : Squarefree (minpoly E A) :=
    Squarefree.squarefree_of_dvd (Matrix.minpoly_dvd_charpoly A) hs.squarefree
  have h1 : minpoly E A ∣ q ^ (k + 1) := minpoly.dvd E A (by rw [map_pow]; exact hk)
  have h2 : minpoly E A ∣ q := (hsq.dvd_pow_iff_dvd (by omega)).1 h1
  exact minpoly.dvd_iff.1 h2

theorem exists_pow_mul_eq {E : Type} [Field E] {r : ℕ} (A : Matrix (Fin r) (Fin r) E)
    (hs : A.charpoly.Separable) (z : Matrix (Fin r) (Fin r) E) (hz : z * A = A * z) :
    ∃ n : ℕ, ∃ w : Matrix (Fin r) (Fin r) E, w * A = A * w ∧ z ^ (n + 1) * w = z ^ n := by
  let S := Subalgebra.centralizer E ({A} : Set (Matrix (Fin r) (Fin r) E))
  have hmem : ∀ a : Matrix (Fin r) (Fin r) E, a ∈ S ↔ a * A = A * a := by
    intro a; rw [Subalgebra.mem_centralizer_iff]; simp [eq_comm]
  letI : CommRing S := { (inferInstance : Ring S) with
    mul_comm := fun a b => Subtype.ext (GlobalTheory.CommSep.commute_of_commute_separable E r A hs a b
      ((hmem a).1 a.2) ((hmem b).1 b.2)) }
  haveI : IsArtinianRing S := IsArtinianRing.of_finite E S
  obtain ⟨n, w, hw⟩ := IsArtinian.exists_pow_succ_smul_dvd (R := S) (M := S) ⟨z, (hmem z).2 hz⟩ 1
  refine ⟨n, w, (hmem w).1 w.2, ?_⟩
  have := congrArg Subtype.val hw
  simpa using this

theorem star_mul_comm {E : Type} [Field E] [StarRing E] {r : ℕ} (A : Matrix (Fin r) (Fin r) E)
    (hA : A.IsHermitian) (y : Matrix (Fin r) (Fin r) E) (hy : y * A = A * y) :
    star y * A = A * star y := by
  have hA' : star A = A := hA
  have := congrArg star hy
  rw [star_mul, star_mul, hA'] at this
  exact this.symm

theorem pow_add_mul_pow {R : Type} [Ring R] (z w : R) (m : ℕ) (h : z ^ (m + 1) * w = z ^ m) :
    ∀ j : ℕ, z ^ (m + j) * w ^ j = z ^ m := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    calc z ^ (m + (j + 1)) * w ^ (j + 1) = z ^ j * (z ^ (m + 1) * w) * w ^ j := by
          rw [pow_succ' w j, show m + (j + 1) = j + (m + 1) by omega, pow_add]
          simp only [mul_assoc]
      _ = z ^ (m + j) * w ^ j := by rw [h, ← pow_add, show j + m = m + j by omega]
      _ = z ^ m := ih

theorem isoIdem : ∀ (E : Type) [Field E] [StarRing E] (r : ℕ) (A₀ : Matrix (Fin r) (Fin r) E),
    A₀.IsHermitian → A₀.charpoly.Separable → ∃ f : Matrix (Fin r) (Fin r) E, f * A₀ = A₀ * f ∧
      f * f = f ∧ f * star f = 0 ∧ ∀ y : Matrix (Fin r) (Fin r) E, y * A₀ = A₀ * y →
        y * (1 - f - star f) * star (y * (1 - f - star f)) = 0 → y * (1 - f - star f) = 0 := by
  intro E _ _ r A hA hs
  have comm : ∀ a b : Matrix (Fin r) (Fin r) E, a * A = A * a → b * A = A * b → a * b = b * a :=
    GlobalTheory.CommSep.commute_of_commute_separable E r A hs
  have cstar := star_mul_comm A hA
  have cmul : ∀ a b : Matrix (Fin r) (Fin r) E, a * A = A * a → b * A = A * b →
      (a * b) * A = A * (a * b) := by
    intro a b ha hb; rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
  have cadd : ∀ a b : Matrix (Fin r) (Fin r) E, a * A = A * a → b * A = A * b →
      (a + b) * A = A * (a + b) := by
    intro a b ha hb; rw [add_mul, mul_add, ha, hb]
  have csub : ∀ a b : Matrix (Fin r) (Fin r) E, a * A = A * a → b * A = A * b →
      (a - b) * A = A * (a - b) := by
    intro a b ha hb; rw [sub_mul, mul_sub, ha, hb]
  have cone : (1 : Matrix (Fin r) (Fin r) E) * A = A * 1 := by simp
  have cpow : ∀ a : Matrix (Fin r) (Fin r) E, a * A = A * a → ∀ k : ℕ, a ^ k * A = A * a ^ k := by
    intro a ha k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ]; exact cmul _ _ ih ha
  let S : Set (Matrix (Fin r) (Fin r) E) := {f | f * A = A * f ∧ f * f = f ∧ f * star f = 0}
  obtain ⟨f, ⟨hfC, hff, hfs⟩, hmax⟩ :=
    (measure fun f : Matrix (Fin r) (Fin r) E => r - f.rank).wf.has_min S ⟨0, by simp [S]⟩
  refine ⟨f, hfC, hff, hfs, ?_⟩
  intro y hy hiso
  by_contra hz
  set e := 1 - f - star f with he
  set z := y * e with hzdef
  have hfsC := cstar f hfC
  have heC : e * A = A * e := csub _ _ (csub _ _ cone hfC) hfsC
  have hzC : z * A = A * z := cmul _ _ hy heC
  have hsf : star f * f = 0 := by rw [← comm f (star f) hfC hfsC]; exact hfs
  have hsfsf : star f * star f = star f := by rw [← star_mul, hff]
  have hfe : f * e = 0 := by rw [he, mul_sub, mul_sub, mul_one, hff, hfs]; abel
  have hsfe : star f * e = 0 := by rw [he, mul_sub, mul_sub, mul_one, hsf, hsfsf]; abel
  have hef : e * star f = 0 := by rw [← comm _ _ hfsC heC]; exact hsfe
  have hee : e * e = e := by
    calc e * e = (1 - f - star f) * e := by rw [← he]
      _ = e := by rw [sub_mul, sub_mul, one_mul, hfe, hsfe, sub_zero, sub_zero]
  have hestar : star e = e := by
    rw [he, star_sub, star_sub, star_one, star_star, sub_right_comm]
  have hze : z * e = z := by rw [hzdef, mul_assoc, hee]
  obtain ⟨n, w, hwC, hw⟩ := exists_pow_mul_eq A hs z hzC
  have hw' : z ^ (n + 1 + 1) * w = z ^ (n + 1) := by
    rw [pow_succ' z (n + 1), mul_assoc, hw, ← pow_succ']
  have key := pow_add_mul_pow z w (n + 1) hw' (n + 1)
  have hzw : Commute z w := comm _ _ hzC hwC
  set g := z ^ (n + 1) * w ^ (n + 1) with hg
  have hgC : g * A = A * g := cmul _ _ (cpow _ hzC _) (cpow _ hwC _)
  have hgz : g * z ^ (n + 1) = z ^ (n + 1) := by
    rw [hg, mul_assoc, ((hzw.pow_pow (n + 1) (n + 1)).symm).eq, ← mul_assoc, ← pow_add, key]
  have hgg : g * g = g := by
    conv_lhs => rw [hg]
    rw [← mul_assoc, hgz]
  have hg0 : g ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hgz
    exact hz (eq_zero_of_pow_eq_zero A hs z hzC _ hgz.symm)
  set a := z ^ n * w ^ (n + 1) with ha
  have haC : a * A = A * a := cmul _ _ (cpow _ hzC _) (cpow _ hwC _)
  have hgza : g = z * a := by rw [hg, ha, pow_succ', mul_assoc]
  have hgs : g * star g = 0 := by
    have hb : (a * star a) * A = A * (a * star a) := cmul _ _ haC (cstar _ haC)
    rw [hgza, star_mul, mul_assoc, ← mul_assoc a, comm _ _ hb (cstar _ hzC), ← mul_assoc]
    rw [show z * star z = 0 from hiso, zero_mul]
  have hge : g * e = g := by
    rw [hgza, mul_assoc, comm a e haC heC, ← mul_assoc, hze]
  have hfz : f * z = 0 := by
    rw [hzdef, ← mul_assoc, comm f y hfC hy, mul_assoc, hfe, mul_zero]
  have hfg : f * g = 0 := by rw [hgza, ← mul_assoc, hfz, zero_mul]
  have hgf : g * f = 0 := by rw [comm g f hgC hfC]; exact hfg
  have hfsg : f * star g = 0 := by
    rw [← hge, star_mul, hestar, ← mul_assoc, hfe, zero_mul]
  have hgsf : g * star f = 0 := by rw [← hge, mul_assoc, hef, mul_zero]
  have hf'S : f + g ∈ S := by
    refine ⟨cadd _ _ hfC hgC, ?_, ?_⟩
    · rw [add_mul, mul_add, mul_add, hff, hfg, hgf, hgg]; abel
    · rw [star_add, add_mul, mul_add, mul_add, hfs, hfsg, hgsf, hgs]; abel
  have hrank : f.rank < (f + g).rank := by
    simp only [← Matrix.finrank_range_mulVecLin]
    apply Submodule.finrank_lt_finrank_of_lt
    rw [SetLike.lt_iff_le_and_exists]
    constructor
    · have h1 : (f + g) * f = f := by rw [add_mul, hff, hgf, add_zero]
      calc LinearMap.range f.mulVecLin = LinearMap.range ((f + g) * f).mulVecLin := by rw [h1]
        _ ≤ _ := by rw [Matrix.mulVecLin_mul]; exact LinearMap.range_comp_le_range _ _
    · obtain ⟨v, hv⟩ : ∃ v : Fin r → E, g *ᵥ v ≠ 0 := by
        by_contra hall
        simp only [not_exists, not_not] at hall
        apply hg0
        ext i j
        have := congrFun (hall (Pi.single j 1)) i
        simpa [Matrix.mulVec_single] using this
      refine ⟨g *ᵥ v, ⟨g *ᵥ v, ?_⟩, ?_⟩
      · rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, add_mul, hfg, hgg, zero_add]
      · rintro ⟨u, hu⟩
        rw [Matrix.mulVecLin_apply] at hu
        apply hv
        have hgv : g *ᵥ v = g *ᵥ (g *ᵥ v) := by rw [Matrix.mulVec_mulVec, hgg]
        rw [hgv, ← hu, Matrix.mulVec_mulVec, hgf, Matrix.zero_mulVec]
  have hle : (f + g).rank ≤ r := by
    simpa using Matrix.rank_le_card_width (f + g)
  exact hmax (f + g) hf'S (show r - (f + g).rank < r - f.rank by omega)

end GlobalTheory.IsoIdem
end

section

open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

namespace GlobalTheory.CompactRepField

theorem exists_finiteDimensional_entries_mem_of_continuous :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (a : ℕ) (r : Γ →* GL (Fin a) (PadicAlgCl l)), Continuous r → ∃ L : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] L ∧ ∀ g i j, ((r g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i j ∈ L := by
  intro l _ Γ _ _ _ _ a r hr
  let H : Subgroup (GL (Fin a) (PadicAlgCl l)) := r.range
  haveI : CompactSpace H := by
    have hc : IsCompact (H : Set (GL (Fin a) (PadicAlgCl l))) := by
      have : (H : Set (GL (Fin a) (PadicAlgCl l))) = Set.range r := by
        ext x; simp [H]
      rw [this]; exact isCompact_range hr
    exact isCompact_iff_compactSpace.1 hc
  obtain ⟨K, hK, hmem⟩ := exists_finiteDimensional_entries_mem l H a H.subtype
    fun i j => ((Units.continuous_val.comp continuous_subtype_val).matrix_elem i j)
  refine ⟨K, hK, fun g i j => ?_⟩
  exact hmem ⟨r g, ⟨g, rfl⟩⟩ i j

end GlobalTheory.CompactRepField
end

section

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

theorem _root_.GlobalTheory.T.krasnerLemma_decompositionGroup_stabilizer_version : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω) (β β' : Ω), (∀ d ∈ Dec (F := E) A, d β ≠ β → A.valuation (β' - β) < A.valuation (d β - β)) → ∀ σ ∈ Dec (F := E) A, σ β' = β' → σ β = β := by
  first | exact @GlobalTheory.krasner_stabiliser | exact GlobalTheory.krasner_stabiliser | (intros; apply GlobalTheory.krasner_stabiliser <;> assumption)
end

section

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

theorem _root_.GlobalTheory.T.decompositionGroup_orbit_root_same_stabilizer : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (β β' : Ω) (S : Finset Ω), (∀ x, x ∈ S ↔ ∃ d ∈ Dec (F := E) A, d β = x) → ∀ g : Polynomial E, g.Monic → g.natDegree = S.card → aeval β' g = 0 → (∀ σ ∈ Dec (F := E) A, σ β' = β' → σ β = β) → (∀ σ : G E Ω, ∃ d ∈ Dec (F := E) A, σ β' = d β') ∧ (∀ σ ∈ Dec (F := E) A, σ β = β → σ β' = β') := by
  first | exact @GlobalTheory.Count.decOrbit_root_count | exact GlobalTheory.Count.decOrbit_root_count | (intros; apply GlobalTheory.Count.decOrbit_root_count <;> assumption)
end

section

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

theorem _root_.GlobalTheory.T.exists_base_near_of_decomposition_fixed : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (z : Ω), (∀ d ∈ Dec (F := E) A, d z = z) → ∀ r : Ω, r ≠ 0 → ∃ e : E, A.valuation (algebraMap E Ω e - z) < A.valuation r := by
  first | exact @GlobalTheory.exists_base_near_of_dec_fixed | exact GlobalTheory.exists_base_near_of_dec_fixed | (intros; apply GlobalTheory.exists_base_near_of_dec_fixed <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Neutral.HilbertClassField

theorem _root_.GlobalTheory.T.hilbertSubgroup_le_ker_of_kills_inertia : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (Av : HeightOneSpectrum (𝓞 E) → ValuationSubring Ω), (∀ v, IsPlaceOver (Av v) v) →
    ∀ (M : Type) [AddCommGroup M] (z : G E Ω → M), (∀ g h, z (g * h) = z g + z h) →
    IsLocallyConstant z → (∀ v, ∀ σ ∈ Ine (F := E) (Av v), z σ = 0) →
    (∀ c : Ω ≃ₐ[E] Ω, IsComplexConjugation c → z c = 0) →
    ∀ σ ∈ hilbertSubgroup E Ω, z σ = 0 := by
  first | exact @GlobalTheory.HilbertKill.hilbertSubgroup_le_ker | exact GlobalTheory.HilbertKill.hilbertSubgroup_le_ker | (intros; apply GlobalTheory.HilbertKill.hilbertSubgroup_le_ker <;> assumption)
end

section

open ReciprocityTheory.Gal

theorem _root_.GlobalTheory.T.transfer_card_H0_H1_eq : ∀ {O : Type} [CommRing O] {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']
    (i : G ≃ₜ* G') {M : Type} [AddCommGroup M] [Module O M] (ρ : Representation O G M)
    (p r : ℕ) [NeZero (p ^ r)] (c : O) (h : ((p : O) ^ r) ∈ Ideal.span {c}),
    letI := GlobalTheory.ShapeNeg.levZ (M := M) p r h
    Nat.card (ReciprocityTheory.Gal.H0 (GlobalTheory.ShapeNeg.levRep ρ c)) =
        Nat.card (ReciprocityTheory.Gal.H0 (GlobalTheory.ShapeNeg.levRepZ p r h (ρ.comp i.symm.toMulEquiv.toMonoidHom))) ∧
      Nat.card (ReciprocityTheory.Gal.H1 (GlobalTheory.ShapeNeg.levRep ρ c)) =
        Nat.card (ReciprocityTheory.Gal.H1 (GlobalTheory.ShapeNeg.levRepZ p r h (ρ.comp i.symm.toMulEquiv.toMonoidHom))) := by
  first | exact @GlobalTheory.ShapeNeg.transfer_card_H0_H1 | exact GlobalTheory.ShapeNeg.transfer_card_H0_H1 | (intros; apply GlobalTheory.ShapeNeg.transfer_card_H0_H1 <;> assumption)
end
