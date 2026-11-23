module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle495
public import GroundTheory.GlobalFields.Adele.Bundle003
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle096
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle499
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle303
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle475
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle482
import Mathlib.Algebra.AffineMonoid.UniqueSums
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsOpenKerFinIdele
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal

namespace GlobalTheory.CellDec
variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem mem_GLint_iff_entries_cell {K : Type} [Field K] {O : Subring K} {x : GL (Fin n) K} :
    x ∈ GLint (Fin n) O ↔ (∀ i j, x.1 i j ∈ O) ∧ ∀ i j, (x⁻¹).1 i j ∈ O := by
  refine ⟨?_, fun h => ⟨⟨Matrix.of fun i j => ⟨_, h.1 i j⟩, Matrix.of fun i j => ⟨_, h.2 i j⟩, ?_, ?_⟩, rfl⟩⟩
  · rintro ⟨y, rfl⟩
    exact ⟨fun i j => (y.1 i j).2, fun i j => ((y⁻¹).1 i j).2⟩
  · refine Matrix.map_injective O.subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.mul_inv
  · refine Matrix.map_injective O.subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.inv_mul

theorem isOpen_intAway (S : Finset (HeightOneSpectrum (𝓞 E))) :
    IsOpen {f : Af E | ∀ v, v ∉ S → f v ∈ v.adicCompletionIntegers E} := by
  refine RestrictedProduct.isOpen_forall_imp_mem (fun v => ?_)
  have h : (v.adicCompletionIntegers E : Set (v.adicCompletion E)) =
      ((Valued.v : Valuation (v.adicCompletion E) _).integer : Set (v.adicCompletion E)) := by
    ext x
    simp only [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.mem_integer_iff]
  rw [h]
  exact Valued.isOpen_integer _

theorem isOpen_US (S : Finset (HeightOneSpectrum (𝓞 E))) : IsOpen (US E n S : Set (GA E n)) := by
  set A := {f : Af E | ∀ v, v ∉ S → f v ∈ v.adicCompletionIntegers E}
  have e : (US E n S : Set (GA E n)) =
      ⋂ i : Fin n, ⋂ j : Fin n, ((fun g : GA E n => ((g : Matrix (Fin n) (Fin n) (Ad E)) i j).2) ⁻¹' A ∩
        (fun g : GA E n => (((g⁻¹ : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) i j).2) ⁻¹' A) := by
    ext g
    simp only [SetLike.mem_coe, US, Subgroup.mem_iInf, Subgroup.mem_comap, Set.mem_iInter, Set.mem_inter_iff,
      Set.mem_preimage, A, Set.mem_setOf_eq, GlobalTheory.LFun.KGL, mem_GLint_iff_entries_cell, ← map_inv]
    constructor
    · intro h i j
      exact ⟨fun v hv => (h v hv).1 i j, fun v hv => (h v hv).2 i j⟩
    · intro h v hv
      exact ⟨fun i j => (h i j).1 v hv, fun i j => (h i j).2 v hv⟩
  rw [e]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => IsOpen.inter ?_ ?_
  · exact (isOpen_intAway S).preimage
      (continuous_snd.comp ((Units.continuous_val (M := Matrix (Fin n) (Fin n) (Ad E))).matrix_elem i j))
  · exact (isOpen_intAway S).preimage
      (continuous_snd.comp ((Units.continuous_coe_inv (M := Matrix (Fin n) (Fin n) (Ad E))).matrix_elem i j))

theorem isOpen_adelicUnipotentTimesIntegralOutsideSet : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))),
    IsOpen (GlobalTheory.CellDec.C0 E n S) := by
  intro E _ _ n S
  have e : C0 E n S = ⋃ u ∈ (NA E n : Set (GA E n)), (fun k => u * k) '' (US E n S : Set (GA E n)) := by
    ext g
    simp only [C0, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_image, SetLike.mem_coe, exists_prop]
    constructor
    · rintro ⟨u, hu, k, hk, rfl⟩; exact ⟨u, hu, k, hk, rfl⟩
    · rintro ⟨u, hu, k, hk, rfl⟩; exact ⟨u, hu, k, hk, rfl⟩
  rw [e]
  exact isOpen_biUnion fun u _ => isOpenMap_mul_left u _ (isOpen_US S)

end GlobalTheory.CellDec
end

section

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory

noncomputable section

namespace GlobalTheory.CellDec.RatUnip

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem row_mul_split (w : Matrix (Fin n) (Fin n) (Ad E))
    (hl : ∀ i j, j < i → w i j = 0) (hd : ∀ i, w i i = 1) (r : Fin n → E) (j : Fin n) :
    ∑ k, algebraMap E (Ad E) (r k) * w k j =
      (∑ k, if k < j then algebraMap E (Ad E) (r k) * w k j else 0) + algebraMap E (Ad E) (r j) := by
  have key : ∀ k, algebraMap E (Ad E) (r k) * w k j =
      (if k < j then algebraMap E (Ad E) (r k) * w k j else 0) +
        (if j = k then algebraMap E (Ad E) (r k) else 0) := by
    intro k
    rcases lt_trichotomy k j with h | rfl | h
    · simp [h, h.ne']
    · simp [hd]
    · simp [not_lt.2 h.le, h.ne, hl k j h]
  rw [Finset.sum_congr rfl fun k _ => key k, Finset.sum_add_distrib, Finset.sum_ite_eq]
  simp

theorem row_unique (w : Matrix (Fin n) (Fin n) (Ad E))
    (hl : ∀ i j, j < i → w i j = 0) (hd : ∀ i, w i i = 1) (i : Fin n) (r r' : Fin n → E)
    (h0 : ∀ k, k < i → r k = 0) (h0' : ∀ k, k < i → r' k = 0) (h1 : r i = 1) (h1' : r' i = 1)
    (hF : ∀ j, i < j → ∑ k, algebraMap E (Ad E) (r k) * w k j ∈ GroundTheory.Global.fundamentalSet E)
    (hF' : ∀ j, i < j → ∑ k, algebraMap E (Ad E) (r' k) * w k j ∈ GroundTheory.Global.fundamentalSet E) :
    r = r' := by
  suffices h : ∀ m : ℕ, ∀ j : Fin n, j.val < m → r j = r' j from
    funext fun j => h _ j j.val.lt_succ_self
  intro m
  induction m with
  | zero => intro j hj; exact absurd hj (Nat.not_lt_zero _)
  | succ m ih =>
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
    · exact ih j hj
    rcases lt_trichotomy j i with h | rfl | h
    · rw [h0 j h, h0' j h]
    · rw [h1, h1']
    · have hs : (∑ k, if k < j then algebraMap E (Ad E) (r k) * w k j else 0) =
          ∑ k, if k < j then algebraMap E (Ad E) (r' k) * w k j else 0 := by
        refine Finset.sum_congr rfl fun k _ => ?_
        split_ifs with hk
        · rw [ih k (by have := Fin.lt_def.1 hk; omega)]
        · rfl
      have a := hF j h
      have b := hF' j h
      rw [row_mul_split w hl hd] at a b
      rw [hs] at a
      obtain ⟨c, -, hc⟩ := GroundTheory.Global.existsUnique_sub_mem_fundamentalSet E
        (∑ k, if k < j then algebraMap E (Ad E) (r' k) * w k j else 0)
      have e1 := hc (-r j) (by simpa using a)
      have e2 := hc (-r' j) (by simpa using b)
      exact neg_injective (e1.trans e2.symm)

theorem row_exists (w : Matrix (Fin n) (Fin n) (Ad E))
    (hl : ∀ i j, j < i → w i j = 0) (hd : ∀ i, w i i = 1) (i : Fin n) :
    ∃ r : Fin n → E, (∀ k, k < i → r k = 0) ∧ r i = 1 ∧
      ∀ j, i < j → ∑ k, algebraMap E (Ad E) (r k) * w k j ∈ GroundTheory.Global.fundamentalSet E := by
  suffices h : ∀ m : ℕ, ∃ r : Fin n → E, (∀ k, k < i → r k = 0) ∧ r i = 1 ∧
      ∀ j : Fin n, i < j → j.val < m →
        ∑ k, algebraMap E (Ad E) (r k) * w k j ∈ GroundTheory.Global.fundamentalSet E by
    obtain ⟨r, h0, h1, h2⟩ := h n
    exact ⟨r, h0, h1, fun j hj => h2 j hj j.isLt⟩
  intro m
  induction m with
  | zero =>
    exact ⟨Pi.single i 1, fun k hk => by simp [Pi.single_apply, hk.ne], by simp,
      fun j _ hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ m ih =>
    obtain ⟨r, h0, h1, h2⟩ := ih
    by_cases hm : ∃ jm : Fin n, jm.val = m ∧ i < jm
    · obtain ⟨jm, hjm, hijm⟩ := hm
      obtain ⟨c, hc, -⟩ := GroundTheory.Global.existsUnique_sub_mem_fundamentalSet E
        (∑ k, algebraMap E (Ad E) (r k) * w k jm)
      refine ⟨r - Pi.single jm c, fun k hk => ?_, ?_, fun j hij hj => ?_⟩
      · simp [h0 k hk, Pi.single_apply, (hk.trans hijm).ne]
      · simp [h1, Pi.single_apply, hijm.ne]
      · have hsum : ∑ k, algebraMap E (Ad E) ((r - Pi.single jm c : Fin n → E) k) * w k j =
            ∑ k, algebraMap E (Ad E) (r k) * w k j - algebraMap E (Ad E) c * w jm j := by
          simp only [Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]
          congr 1
          rw [Finset.sum_eq_single jm]
          · simp
          · intro k _ hk; simp [Pi.single_apply, hk]
          · simp
        rw [hsum]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
        · have hlt : j < jm := by rw [Fin.lt_def]; omega
          rw [hl jm j hlt, mul_zero, sub_zero]
          exact h2 j hij hj
        · have : j = jm := Fin.ext (hj.trans hjm.symm)
          subst this
          rw [hd, mul_one]; exact hc
    · refine ⟨r, h0, h1, fun j hij hj => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
      · exact h2 j hij hj
      · exact absurd ⟨j, hj, hij⟩ hm

end GlobalTheory.CellDec.RatUnip

namespace GlobalTheory.CellDec

open GlobalTheory.CellDec.RatUnip

theorem existsUnique_ratUnip_mul_mem_fundamentalSet (E : Type) [Field E] [NumberField E] (n : ℕ) (u : GA E n)
    (hu : u ∈ GlobalTheory.CellDec.NA E n) :
    ∃! γ : GL (Fin n) E, γ ∈ GlobalTheory.SmGL.unipB E (Fin n) ∧ ∀ i j : Fin n, i < j →
      ((ratGL E n γ * u : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) i j ∈ GroundTheory.Global.fundamentalSet E := by
  obtain ⟨hl, hd⟩ := (GlobalTheory.SmGL.mem_unipB (Ad E)).1 hu
  have hent : ∀ (γ : GL (Fin n) E) (i j : Fin n),
      ((ratGL E n γ * u : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) i j =
        ∑ k, algebraMap E (Ad E) ((γ : Matrix (Fin n) (Fin n) E) i k) * (u : Matrix (Fin n) (Fin n) (Ad E)) k j := by
    intro γ i j
    simp [ratGL, Matrix.mul_apply]
  choose r h0 h1 hF using row_exists (u : Matrix (Fin n) (Fin n) (Ad E)) hl hd
  let M : Matrix (Fin n) (Fin n) E := Matrix.of fun i k => r i k
  have hM : IsUnit M.det := by
    rw [Matrix.det_of_upperTriangular (show M.BlockTriangular id from fun i j hij => h0 i j hij)]
    simp [M, h1]
  refine ⟨Matrix.nonsingInvUnit M hM,
    ⟨(GlobalTheory.SmGL.mem_unipB E).2 ⟨fun i j hij => h0 i j hij, fun i => h1 i⟩, fun i j hij => ?_⟩, ?_⟩
  · rw [hent]; exact hF i j hij
  · rintro γ ⟨hγ, hγF⟩
    obtain ⟨gl, gd⟩ := (GlobalTheory.SmGL.mem_unipB E).1 hγ
    apply Units.ext
    ext i j
    have := row_unique (u : Matrix (Fin n) (Fin n) (Ad E)) hl hd i
      (fun k => (γ : Matrix (Fin n) (Fin n) E) i k) (r i) (fun k hk => gl i k hk) (h0 i) (gd i) (h1 i)
      (fun j hij => by rw [← hent]; exact hγF i j hij) (hF i)
    exact congrFun this j

end GlobalTheory.CellDec
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.Mem.Chr GlobalTheory.LFun

namespace GlobalTheory.UnitaryBC

variable {E : Type} [Field E] [NumberField E]

theorem pLoc_conjFin_eq (c : E ≃+* E) (w : HeightOneSpectrum (𝓞 E)) (s : w.adicCompletion E →+* w.adicCompletion E)
    (hs : ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (c x)) (hv : ∀ x, Valued.v (s x) = Valued.v x) (x : Af E) :
    pLoc E w (conjFin c x) = s (pLoc E w x) := by
  have hw : ConjPl c w w := fun k => by
    have h1 : Valued.v (algebraMap E (w.adicCompletion E) k) = w.valuation E k :=
      w.valuedAdicCompletion_eq_valuation' k
    have h2 : Valued.v (algebraMap E (w.adicCompletion E) (c k)) = w.valuation E (c k) :=
      w.valuedAdicCompletion_eq_valuation' _
    rw [← h1, ← h2, ← hs, hv]
  have key : ∀ (u : HeightOneSpectrum (𝓞 E)) (_ : w = u) (φ : u.adicCompletion E →+* w.adicCompletion E),
      Continuous φ → (∀ k : E, φ (algebraMap E _ k) = algebraMap E _ (c k)) → φ (pLoc E u x) = s (pLoc E w x) := by
    rintro _ rfl φ h1 h2
    exact congrFun ((HeightOneSpectrum.denseRange_algebraMap E w).equalizer h1
      (continuous_of_valued_eq (w.valuedAdicCompletion_surjective E) s hv)
      (funext fun k => (h2 k).trans (hs k).symm)) _
  rw [pLoc_conjFin]
  exact key _ (eq_conjSrc hw) _ (conjLoc_spec c w).1 (conjLoc_spec c w).2.1

variable [IsCMField E]

theorem cT_cLoc {n : ℕ} (w : HeightOneSpectrum (𝓞 E)) (s : w.adicCompletion E →+* w.adicCompletion E)
    (hs : ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x))
    (hv : ∀ x, Valued.v (s x) = Valued.v x) (g : UA E n) : cT s (cLoc w g).val * (cLoc w g).val = 1 := by
  have hg : cT (conjAd E) g.1.val * 1 * g.1.val = 1 := g.2
  rw [Matrix.mul_one] at hg
  have h := congrArg ((pLoc E w).comp (pFin E)).mapMatrix hg
  rw [map_mul, map_one] at h
  rw [← h]
  congr 1
  refine Matrix.ext fun i j => ?_
  exact (pLoc_conjFin_eq (IsCMField.complexConj E).toRingEquiv w s hs hv (pFin E (g.1.val j i))).symm

end GlobalTheory.UnitaryBC

end
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.UnitaryBC

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem finU_mul_infU_comm (k y : UA E n) (hk : k ∈ finU (E := E) (n := n)) (hy : y ∈ infU E n) : k * y = y * k := by
  have hk' : Matrix.GeneralLinearGroup.map (pInf E) (k : GA E n) = 1 := MonoidHom.mem_ker.1 hk
  have hy' : Matrix.GeneralLinearGroup.map (pFin E) (y : GA E n) = 1 := MonoidHom.mem_ker.1 hy
  apply Subtype.ext
  apply ga_ext
  · simp only [Subgroup.coe_mul, map_mul, hk', one_mul, mul_one]
  · simp only [Subgroup.coe_mul, map_mul, hy', one_mul, mul_one]

def levelForms (L : Subgroup (finU (E := E) (n := n))) (C : Submodule ℂ (infU E n → ℂ)) : Submodule ℂ (UA E n → ℂ) where
  carrier := {ψ | (∀ γ ∈ ratU E n, ∀ g, ψ (γ * g) = ψ g) ∧ (∀ k ∈ L, ∀ g, ψ (g * (k : UA E n)) = ψ g) ∧
    ∀ g, (fun y : infU E n => ψ (g * (y : UA E n))) ∈ C}
  add_mem' := by
    rintro a b ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩
    refine ⟨fun γ hγ g => ?_, fun k hk g => ?_, fun g => ?_⟩
    · simp only [Pi.add_apply, a1 γ hγ g, b1 γ hγ g]
    · simp only [Pi.add_apply, a2 k hk g, b2 k hk g]
    · exact C.add_mem (a3 g) (b3 g)
  zero_mem' := ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ => C.zero_mem⟩
  smul_mem' := by
    rintro c a ⟨a1, a2, a3⟩
    refine ⟨fun γ hγ g => ?_, fun k hk g => ?_, fun g => ?_⟩
    · simp only [Pi.smul_apply, a1 γ hγ g]
    · simp only [Pi.smul_apply, a2 k hk g]
    · exact C.smul_mem c (a3 g)

end GlobalTheory.UnitaryBC


open GlobalTheory.UnitaryBC in
theorem GlobalTheory.UnitaryBC.finiteDimensional_levelForms : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), (∀ L : Subgroup (finU (E := E) (n := n)), IsOpen (L : Set (finU (E := E) (n := n))) → ∃ S : Finset (UA E n), ∀ g : UA E n, ∃ γ ∈ ratU E n, ∃ s ∈ S, ∃ k ∈ L, ∃ y ∈ infU E n, g = γ * s * (k : UA E n) * y) → ∀ L : Subgroup (finU (E := E) (n := n)), IsOpen (L : Set (finU (E := E) (n := n))) → ∀ C : Submodule ℂ (infU E n → ℂ), FiniteDimensional ℂ C → FiniteDimensional ℂ (Submodule.span ℂ {ψ : UA E n → ℂ | (∀ γ ∈ ratU E n, ∀ g, ψ (γ * g) = ψ g) ∧ (∀ k ∈ L, ∀ g, ψ (g * (k : UA E n)) = ψ g) ∧ ∀ g, (fun y : infU E n => ψ (g * (y : UA E n))) ∈ C}) := by
  intro E _ _ _ n hS L hL C _
  obtain ⟨S, hS⟩ := hS L hL
  let M := levelForms L C
  have hle : Submodule.span ℂ {ψ : UA E n → ℂ | (∀ γ ∈ ratU E n, ∀ g, ψ (γ * g) = ψ g) ∧
      (∀ k ∈ L, ∀ g, ψ (g * (k : UA E n)) = ψ g) ∧ ∀ g, (fun y : infU E n => ψ (g * (y : UA E n))) ∈ C} ≤ M :=
    Submodule.span_le.2 fun ψ h => h

  have key : ∀ ψ ∈ M, ∀ g, ∃ s ∈ S, ∃ y ∈ infU E n, ψ g = ψ (s * y) := by
    rintro ψ ⟨h1, h2, -⟩ g
    obtain ⟨γ, hγ, s, hs, k, hk, y, hy, rfl⟩ := hS g
    refine ⟨s, hs, y, hy, ?_⟩
    rw [mul_assoc, mul_assoc, h1 γ hγ, finU_mul_infU_comm _ _ k.2 hy, ← mul_assoc, h2 k hk]
  let f : M →ₗ[ℂ] (S → C) :=
    { toFun := fun ψ s => ⟨fun y : infU E n => ψ.1 ((s : UA E n) * (y : UA E n)), ψ.2.2.2 s⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    funext g
    obtain ⟨s, hs, y, hy, e⟩ := key (a.1 - b.1) (M.sub_mem a.2 b.2) g
    have := congrArg (fun F : S → C => ((F ⟨s, hs⟩ : C) : infU E n → ℂ) ⟨y, hy⟩) hab
    simp only [f, LinearMap.coe_mk, AddHom.coe_mk] at this
    have e' : a.1 g - b.1 g = a.1 (s * y) - b.1 (s * y) := e
    rw [this, sub_self, sub_eq_zero] at e'
    exact e'
  haveI : FiniteDimensional ℂ M := Module.Finite.of_injective f hf
  exact Submodule.finiteDimensional_of_le hle
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions

namespace GlobalTheory.UnitaryBC

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem infGL_mem_UA {n : ℕ} (y : GL (Fin n) (Cinf E)) (hy : y.valᴴ * y.val = 1) : infGL E n y ∈ UA E n := by
  change cT (conjAd E) (infGL E n y).val * 1 * (infGL E n y).val = 1
  have h1 : (infGL E n y).val.map (pInf E) = y.val := congrArg Units.val (pInf_infGL y)
  have h2 : (infGL E n y).val.map (pFin E) = 1 := congrArg Units.val (pFin_infGL y)
  have h3 : (cT (conjAd E) (infGL E n y).val).map (pInf E) = y.valᴴ := by
    ext1 i j
    rw [Matrix.conjTranspose_apply, ← h1]
    exact (infEq E).symm_apply_apply _
  have h4 : (cT (conjAd E) (infGL E n y).val).map (pFin E) = 1 := by
    ext1 i j
    change conjFin (IsCMField.complexConj E).toRingEquiv (((infGL E n y).val.map (pFin E)) j i) = _
    rw [h2]
    simp only [Matrix.one_apply, eq_comm (a := j)]
    split_ifs <;> simp
  have h5 := congrArg₂ (· * ·) h3 h1
  have h6 := congrArg₂ (· * ·) h4 h2
  simp only [← Matrix.map_mul, hy, mul_one] at h5 h6
  rw [mul_one]
  ext1 i j
  refine ad_ext ((congrFun₂ h5 i j).trans ?_) ((congrFun₂ h6 i j).trans ?_) <;>
  · simp only [Matrix.one_apply]
    split_ifs <;> simp


end GlobalTheory.UnitaryBC

end
end

section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LlcDepth

theorem eq_pow_natDegree_of_dvd {p : ℂ[X]} (hp : p.Monic) {n : ℕ} (hd : p ∣ (X - 1) ^ n) :
    p = (X - 1) ^ p.natDegree := by
  have e : (X - 1 : ℂ[X]) = X - C 1 := by simp
  rw [e] at hd ⊢
  obtain ⟨i, -, hi⟩ := (dvd_prime_pow (prime_X_sub_C (1 : ℂ)) n).1 hd
  have hpi := eq_of_monic_of_associated hp ((monic_X_sub_C (1 : ℂ)).pow i) hi
  rw [hpi, natDegree_pow, natDegree_X_sub_C, mul_one]

theorem prod_map_pow {α : Type*} (q : ℂ[X]) (f : α → ℕ) (s : Multiset α) :
    (s.map fun y => q ^ f y).prod = q ^ (s.map f).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [ih, pow_add]

theorem fixed_ne_bot_iff_isTameWD : DepthZeroCuspidalLL → DepthZeroInduction → LanglandsExhaustionGL →
    ZelevinskyPolynomialRing → GeometricLemma → BernsteinZelevinskyFiniteness →
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
      (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion E) → WD h), IsRecLit h rc →
      ∀ x : IrrGL (k := w.adicCompletion E), fixed x.rep (KOne (w.adicCompletion E) (Fin x.1)) ≠ ⊥ ↔ IsTameWD (rc x) := by
  intro hDZC hDZI hEx hZel hGeo hBZ E Ω _ _ _ _ _ A w h rc hrc x
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨a, ha, ε, -, hL⟩ := id hrc
  obtain ⟨m, hm⟩ := hEx _ x
  have hs : HasSupport x.rep (msupp m) := GlobalTheory.T.langlandsClassification_supercuspidalSupport_multisegment hZel _ m x hm
  have hcp := GlobalTheory.T.central_character_rec_compatible hEx hZel hGeo hBZ E Ω A w h a ha _ rc hL x (msupp m) hs
  have hdy : ∀ y ∈ msupp m, (fixed y.rep (KOne (w.adicCompletion E) (Fin y.1)) ≠ ⊥ ↔ IsTameWD (rc y)) :=
    fun y hy => hDZC E Ω A w h rc hrc y (hs.isCusp hy)
  have htame : IsTameWD (rc x) ↔ ∀ y ∈ msupp m, IsTameWD (rc y) := by
    simp only [GlobalTheory.T.isTameWeilDeligne_iff_wild_charpoly E Ω A w h]
    constructor
    · intro H y hy σ hσ
      have hdvd : (rc y).charPol σ ∣ (rc x).charPol σ := by
        rw [hcp σ]
        exact Multiset.dvd_prod (Multiset.mem_map_of_mem _ hy)
      rw [H σ hσ] at hdvd
      have e := eq_pow_natDegree_of_dvd ((rc y).charPol_monic σ) hdvd
      rwa [WD.charPol_natDegree] at e
    · intro H σ hσ
      rw [hcp σ, Multiset.map_congr rfl (fun y hy => H y hy σ hσ), prod_map_pow]
      congr 1
      rw [hL.dim x, Multiset.map_congr rfl (fun y _ => hL.dim y), hs.sum_fst, Fintype.card_fin]
  rw [htame]
  constructor
  · intro hx y hy
    rw [← hdy y hy]
    obtain ⟨n, xs, hxs, hcs⟩ := hs
    have H := GlobalTheory.SmGL.depthZeroSupport _ x.1 (GlobalTheory.SplitRead.Irr.ofIrrRep x.2.rep) n (fun i => (xs i).1)
      (fun i => GlobalTheory.SplitRead.Irr.ofIrrRep (xs i).2.rep) hcs ((Submodule.ne_bot_iff _).1 hx)
    rw [← hxs] at hy
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hy
    obtain ⟨v, hv, hv0⟩ := H i
    exact (Submodule.ne_bot_iff _).2 ⟨v, hv, hv0⟩
  · intro H
    exact hDZI _ x (msupp m) hs fun y hy => (hdy y hy).2 (H y hy)

end GlobalTheory.LlcDepth

end
end
