module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle640
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle194
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle689
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle603
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle279
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle682
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle686
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle199
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle683
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.TraceConjugationCover

theorem cover_exists : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (a : ℕ) (L₀ : FinExt l) (r : Γ →* GL (Fin a) (Om l)), Continuous r → Formalism.MainNotions.N.IsSSRep r → ∀ Cl : Set (Γ →* GL (Fin a) (Om l)), (∀ ρ ∈ Cl, Continuous ρ) → LinApprox r Cl → Nonempty (Cover L₀ r Cl) := by
  intro l _ Γ _ _ _ _ a L₀ r hr hss Cl hCl hap
  classical
  obtain ⟨d, ρ, b, e, hρ, hreads, hind, hbr⟩ := GlobalTheory.T.exists_padicInt_span_image_lattice_regular l Γ a r hr
  obtain ⟨c, hc⟩ := GlobalTheory.T.small_traces_dvd_span_image l Γ a r hr hss
  obtain ⟨K, hK⟩ := traceL l a d b
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := by linarith

  have hch : ∀ ρ' : Γ →* GL (Fin a) (Om l), ∃ (L : FinExt l) (t : Finset (Matrix (Fin a) (Fin a) (Om l))), Continuous ρ' →
      (L₀.1 ≤ L.1 ∧ (∀ g i j, ((ρ' g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j ∈ L.1) ∧ (∀ x ∈ t, ∀ i j, x i j ∈ L.1) ∧
        (∀ x : Matrix (Fin a) (Fin a) (Om l), (∀ i j, x i j ∈ L.1) → x ∈ Submodule.span ℚ_[l] (t : Set (Matrix (Fin a) (Fin a) (Om l)))) ∧
        (∃ c' : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], ∑ y ∈ t, zOm l (c' y) • y = 1) ∧
        ∀ g, ∀ x ∈ t, ∃ c' : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], ((ρ' g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) * x = ∑ y ∈ t, zOm l (c' y) • y) := by
    intro ρ'
    by_cases h : Continuous ρ'
    · obtain ⟨L, hLf, hL⟩ := GlobalTheory.T.exists_finiteExtension_entries_of_compact_rep l Γ a ρ' h
      haveI := hLf
      haveI := L₀.2
      let L' : FinExt l := ⟨L ⊔ L₀.1, inferInstance⟩
      have hL' : ∀ g i j, ((ρ' g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j ∈ L'.1 := fun g i j =>
        (le_sup_left : L ≤ L ⊔ L₀.1) (hL g i j)
      obtain ⟨t, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_stable_spanning_finset_matrices l Γ a ρ' L' h hL'
      exact ⟨L', t, fun _ => ⟨le_sup_right, hL', h1, h2, h3, h4⟩⟩
    · exact ⟨L₀, ∅, fun h' => absurd h' h⟩
  choose Lf tf htf using hch

  have hap' : ∀ n : ℕ, ∃ (s : Finset (Γ →* GL (Fin a) (Om l))) (cc : (Γ →* GL (Fin a) (Om l)) → Om l),
      (s : Set (Γ →* GL (Fin a) (Om l))) ⊆ Cl ∧ ∀ g, ‖trc r g - ∑ ρ' ∈ s, cc ρ' * trc ρ' g‖ ≤ ((l : ℝ)⁻¹) ^ (n + K + c) :=
    fun n => hap _ (by positivity)
  choose s cc hsCl hscc using hap'
  let U : ℕ → Finset (Γ →* GL (Fin a) (Om l)) := fun n => (Finset.range (n + 1)).biUnion s
  have hUmono : ∀ n, U n ⊆ U (n + 1) := fun n =>
    Finset.biUnion_subset_biUnion_of_subset_left _ (fun x hx => by simp only [Finset.mem_range] at hx ⊢; omega)
  have hsU : ∀ n, s n ⊆ U n := fun n => Finset.subset_biUnion_of_mem s (Finset.mem_range.2 (Nat.lt_succ_self n))
  have hUCl : ∀ n, ∀ ρ' ∈ U n, ρ' ∈ Cl := by
    intro n ρ' h
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.1 h
    exact hsCl j hj
  let m : ℕ → ℕ := fun n => (U n).card
  let ρs : ∀ n, Fin (m n) → (Γ →* GL (Fin a) (Om l)) := fun n k => ((U n).equivFin.symm k).1
  have hρsU : ∀ n k, ρs n k ∈ U n := fun n k => ((U n).equivFin.symm k).2
  have hρsC : ∀ n k, Continuous (ρs n k) := fun n k => hCl _ (hUCl n _ (hρsU n k))
  let cs : ∀ n, Fin (m n) → Om l := fun n k => if ρs n k ∈ s n then cc n (ρs n k) else 0
  have hcs : ∀ n g, ∑ k, cs n k * trc (ρs n k) g = ∑ ρ' ∈ s n, cc n ρ' * trc ρ' g := by
    intro n g
    have e1 : ∑ k, cs n k * trc (ρs n k) g = ∑ x : (U n), (if x.1 ∈ s n then cc n x.1 else 0) * trc x.1 g :=
      Fintype.sum_equiv (U n).equivFin.symm _ _ (fun k => rfl)
    rw [e1, Finset.sum_coe_sort (U n) (fun x => (if x ∈ s n then cc n x else 0) * trc x g)]
    simp only [ite_mul, zero_mul]
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 (hsU n)]
  have hK' : ∀ n, ∀ w : Fin d → ℤ_[l], ‖((l : Om l) ^ (n + K) • ∑ i, zOm l (w i) • b i).trace‖ ≤ ((l : ℝ) ^ n)⁻¹ := by
    intro n w
    rw [Matrix.trace_smul, smul_eq_mul, norm_mul, norm_pow, norm_l]
    calc ((l : ℝ)⁻¹) ^ (n + K) * ‖(∑ i, zOm l (w i) • b i).trace‖ ≤ ((l : ℝ)⁻¹) ^ (n + K) * (l : ℝ) ^ K :=
          mul_le_mul_of_nonneg_left (hK w) (by positivity)
      _ = ((l : ℝ) ^ n)⁻¹ := by
          rw [pow_add, inv_pow, inv_pow, mul_assoc, inv_mul_cancel₀ (by positivity), mul_one]
  have hlay : ∀ n, ∃ M₀ : ℕ, ∀ M, M₀ ≤ M → ∃ (d' : ℕ) (ρ' : Γ →* GL (Fin d') ℤ_[l]) (bb : Fin d' → Fin (m n) → Matrix (Fin a) (Fin a) (Om l)) (e' : Fin d' → ℤ_[l]) (P : Matrix (Fin d) (Fin d') ℤ_[l]), Continuous ρ' ∧ (∀ s k i j, bb s k i j ∈ (Lf (ρs n k)).1) ∧ LinearIndependent ℚ_[l] bb ∧ (∀ x : Fin (m n) → Matrix (Fin a) (Fin a) (Om l), (∀ k i j, x k i j ∈ (Lf (ρs n k)).1) → x ∈ Submodule.span ℚ_[l] (Set.range bb)) ∧ (∀ k, Reads ρ' (ρs n k) (fun s => bb s k) e') ∧ (∀ s, bb s ∈ latT (ρs n) (fun k => tf (ρs n k)) M) ∧ (∀ x ∈ latT (ρs n) (fun k => tf (ρs n k)) M, ∃ z : Fin d' → ℤ_[l], x = ∑ s, zOm l (z s) • bb s) ∧ Carries r b (ρs n) (fun k => tf (ρs n k)) M bb P (n + K) ∧ Onto (fun g => ((ρ g : GL (Fin d) ℤ_[l]) : Matrix (Fin d) (Fin d) ℤ_[l])) (fun g => ((ρ' g : GL (Fin d') ℤ_[l]) : Matrix (Fin d') (Fin d') ℤ_[l])) P n ∧ (∀ i, (l : ℤ_[l]) ^ n ∣ (P *ᵥ e' - e) i) ∧ ∀ s, ‖(∑ i, zOm l (P i s) • b i).trace - ∑ k, cs n k * (bb s k).trace‖ ≤ ((l : ℝ) ^ n)⁻¹ := by
    intro n
    exact GlobalTheory.T.exists_lattice_layer_cover_basis_mod_pow l Γ a r d ρ b e hreads hind hbr c hc n (n + K) (by omega) (hK' n) (m n) (ρs n)
      (fun k => Lf (ρs n k)) (fun k => tf (ρs n k)) (hρsC n) (fun k => (htf _ (hρsC n k)).2.1)
      (fun k => (htf _ (hρsC n k)).2.2.1) (fun k => (htf _ (hρsC n k)).2.2.2.1)
      (fun k => (htf _ (hρsC n k)).2.2.2.2.1) (fun k => (htf _ (hρsC n k)).2.2.2.2.2) (cs n)
      (fun g => by rw [hcs n g]; exact hscc n g)
  choose M₀ hM₀ using hlay
  let M : ℕ → ℕ := fun n => ∑ j ∈ Finset.range (n + 1), M₀ j
  have hMle : ∀ n, M₀ n ≤ M n := fun n =>
    Finset.single_le_sum (f := M₀) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (Nat.lt_succ_self n))
  have hMmono : ∀ n, M n ≤ M (n + 1) := fun n => by
    simp only [M]
    rw [Finset.sum_range_succ _ (n + 1)]
    exact Nat.le_add_right _ _
  have hL := fun n => hM₀ n (M n) (hMle n)
  choose d' ρ' bb e' P hcont hbbL hind' hspan' hreads' hmem hcoord hcar honto hunit htr using hL
  let ι : ∀ n, Fin (m n) → Fin (m (n + 1)) := fun n k =>
    (U (n + 1)).equivFin ⟨((U n).equivFin.symm k).1, hUmono n ((U n).equivFin.symm k).2⟩
  have hι : ∀ n k, ρs (n + 1) (ι n k) = ρs n k := by
    intro n k
    simp [ρs, ι]
  have htrans : ∀ n, ∃ f : Matrix (Fin (d' n)) (Fin (d' (n + 1))) ℤ_[l], (∀ g, f * ((ρ' (n + 1) g : GL (Fin (d' (n + 1))) ℤ_[l]) : Matrix (Fin (d' (n + 1))) (Fin (d' (n + 1))) ℤ_[l]) = ((ρ' n g : GL (Fin (d' n)) ℤ_[l]) : Matrix (Fin (d' n)) (Fin (d' n)) ℤ_[l]) * f) ∧ ∀ i j, (l : ℤ_[l]) ^ n ∣ (P n * f - P (n + 1)) i j := by
    intro n
    exact GlobalTheory.T.exists_equivariant_transition_matrix_cover l Γ a r d b hind (m n) (m (n + 1)) (ρs n) (ρs (n + 1)) (ι n) (hι n)
      (fun k => tf (ρs n k)) (fun k => tf (ρs (n + 1) k)) (fun k => by rw [hι n k]) (M n) (M (n + 1)) (hMmono n)
      (d' n) (d' (n + 1)) (ρ' n) (ρ' (n + 1)) (bb n) (bb (n + 1)) (e' n) (e' (n + 1)) (hind' n) (hreads' n)
      (hreads' (n + 1)) (hmem (n + 1)) (hcoord n) (P n) (P (n + 1)) n (n + K) (n + 1 + K) (by omega) (by omega)
      (hcar n) (hcar (n + 1))
  choose f hfe hfP using htrans
  let tw : Tower ρ :=
    { d' := d', ρ' := ρ', Pi := P, onto := honto, f := f, f_equi := hfe, f_Pi := hfP }
  let lay : ∀ n, Layer L₀ Cl (tw.ρ' n) := fun n =>
    { m := m n, rep := ρs n, mem := fun k => hUCl n _ (hρsU n k), L := fun k => Lf (ρs n k),
      le := fun k => (htf _ (hρsC n k)).1, rep_mem := fun k => (htf _ (hρsC n k)).2.1, b := bb n,
      b_mem := hbbL n, indep := hind' n, span := hspan' n, e := e' n, reads := hreads' n, c := cs n }
  exact ⟨{ d := d, ρ := ρ, cont := hρ, b := b, e := e, reads := hreads, tw := tw, cont' := hcont, lay := lay,
            unit := hunit, trace := htr }⟩

end GlobalTheory.TraceConjugationCover

end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP

theorem mem_span_range_of_isBaseChange {R S M N : Type} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    {f : M →ₗ[R] N} (hf : IsBaseChange S f) (w : N) : w ∈ Submodule.span S (Set.range f) := by
  obtain ⟨y, rfl⟩ := hf.equiv.surjective w
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul s x => rw [hf.equiv_tmul]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
  | add a b ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb

theorem le_of_span_eq_top_of_isBaseChange {R S N : Type} [CommRing R] [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    (P Q : Submodule R N) (hPQ : P ≤ Q) (hQ : IsBaseChange S Q.subtype)
    (hP : Submodule.span S (P : Set N) = ⊤) : Q ≤ P := by
  let ι := Submodule.inclusion hPQ
  have hs : Function.Surjective (ι.lTensor S) := by
    intro y
    have hv : hQ.equiv y ∈ Submodule.span S (P : Set N) := hP ▸ Submodule.mem_top
    have key : ∀ v ∈ Submodule.span S (P : Set N), ∃ y' : S ⊗[R] P, hQ.equiv (ι.baseChange S y') = v := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem x hx => exact ⟨1 ⊗ₜ ⟨x, hx⟩, by simp [ι, hQ.equiv_tmul]⟩
      | zero => exact ⟨0, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨a, ha⟩ := hx
        obtain ⟨b, hb⟩ := hy
        exact ⟨a + b, by simp [ha, hb]⟩
      | smul c x _ hx =>
        obtain ⟨a, ha⟩ := hx
        exact ⟨c • a, by simp [ha]⟩
    obtain ⟨y', hy'⟩ := key _ hv
    exact ⟨y', by rw [← LinearMap.baseChange_eq_ltensor]; exact hQ.equiv.injective hy'⟩
  have hι := (Module.FaithfullyFlat.lTensor_surjective_iff_surjective R S ι).mp hs
  intro x hx
  obtain ⟨y, hy⟩ := hι ⟨x, hx⟩
  have hx' : (y : N) = x := congrArg Subtype.val hy
  exact hx' ▸ y.2

theorem lift_solution_succ_of_descent {l : ℕ} {R : Type} [CommRing R] {d : ℕ} {B C D : Obj l R} (h : Hom B C)
    (p q : Hom C D) (hcomm : p.comp h = q.comp h) (m : ℕ) (hff : (qmap h m).FaithfullyFlat)
    (ε : Matrix (Fin d) (Fin d) D.A)
    (H : ∀ k : ℕ, letI := (qmap h k).toAlgebra
      ∃ N : Submodule (B.A ⧸ adI B ^ k) (Fin d → C.A ⧸ adI C ^ k),
        (∀ z, z ∈ N ↔ (fun i => qmap p k (z i)) =
          (ε.map (Ideal.Quotient.mk (adI D ^ k))).mulVec fun i => qmap q k (z i)) ∧
        IsBaseChange (C.A ⧸ adI C ^ k) N.subtype)
    (z : Fin d → C.A) (hz : ∀ i, p.f (z i) - ε.mulVec (fun j => q.f (z j)) i ∈ adI D ^ m) :
    ∃ z' : Fin d → C.A, (∀ i, z' i - z i ∈ adI C ^ m) ∧
      ∀ i, p.f (z' i) - ε.mulVec (fun j => q.f (z' j)) i ∈ adI D ^ (m + 1) := by
  have hmem : ∀ (k : ℕ) (w : Fin d → C.A),
      ((fun i => qmap p k (Ideal.Quotient.mk (adI C ^ k) (w i))) =
        (ε.map (Ideal.Quotient.mk (adI D ^ k))).mulVec (fun i => qmap q k (Ideal.Quotient.mk (adI C ^ k) (w i)))) ↔
      ∀ i, p.f (w i) - ε.mulVec (fun j => q.f (w j)) i ∈ adI D ^ k := by
    intro k w
    rw [funext_iff]
    refine forall_congr' fun i => ?_
    have e1 : qmap p k (Ideal.Quotient.mk (adI C ^ k) (w i)) = Ideal.Quotient.mk (adI D ^ k) (p.f (w i)) :=
      qmap_mk p k _
    have e2 : (ε.map (Ideal.Quotient.mk (adI D ^ k))).mulVec
        (fun i => qmap q k (Ideal.Quotient.mk (adI C ^ k) (w i))) i =
        Ideal.Quotient.mk (adI D ^ k) (ε.mulVec (fun j => q.f (w j)) i) := by
      simp only [qmap_mk]
      exact (RingHom.map_mulVec (Ideal.Quotient.mk (adI D ^ k)) ε (fun j => q.f (w j)) i).symm
    rw [e1, e2]
    exact Ideal.Quotient.eq
  letI alg0 : Algebra (B.A ⧸ adI B ^ m) (C.A ⧸ adI C ^ m) := (qmap h m).toAlgebra
  letI alg1 : Algebra (B.A ⧸ adI B ^ (m + 1)) (C.A ⧸ adI C ^ (m + 1)) := (qmap h (m + 1)).toAlgebra
  haveI : Module.FaithfullyFlat (B.A ⧸ adI B ^ m) (C.A ⧸ adI C ^ m) := hff
  obtain ⟨N, hN, hbN⟩ := H m
  obtain ⟨N', hN', hbN'⟩ := H (m + 1)
  have hpq : ∀ b : B.A, p.f (h.f b) = q.f (h.f b) := fun b => congrArg (fun g : Hom B D => g.f b) hcomm
  let P : Submodule (B.A ⧸ adI B ^ m) (Fin d → C.A ⧸ adI C ^ m) :=
    { carrier := {x | ∃ w : Fin d → C.A, (fun i => Ideal.Quotient.mk (adI C ^ m) (w i)) = x ∧
        ∀ i, p.f (w i) - ε.mulVec (fun j => q.f (w j)) i ∈ adI D ^ (m + 1)}
      zero_mem' := ⟨0, by funext i; simp, fun i => by
        have e : (fun j => q.f ((0 : Fin d → C.A) j)) = 0 := funext fun j => by simp
        rw [e, Matrix.mulVec_zero]
        simp⟩
      add_mem' := by
        rintro _ _ ⟨w₁, rfl, h₁⟩ ⟨w₂, rfl, h₂⟩
        refine ⟨w₁ + w₂, by funext i; simp, fun i => ?_⟩
        have := Ideal.add_mem _ (h₁ i) (h₂ i)
        convert this using 1
        have e : (fun j => q.f ((w₁ + w₂) j)) = (fun j => q.f (w₁ j)) + (fun j => q.f (w₂ j)) := by
          funext j; simp
        rw [e, Matrix.mulVec_add]
        simp only [Pi.add_apply, map_add (f := _)]
        ring
      smul_mem' := by
        rintro c _ ⟨w, rfl, hw⟩
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
        refine ⟨fun i => h.f b * w i, ?_, fun i => ?_⟩
        · funext i
          simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra, qmap_mk]
        · have := Ideal.mul_mem_left _ (q.f (h.f b)) (hw i)
          convert this using 1
          have e : (fun j => q.f (h.f b * w j)) = q.f (h.f b) • (fun j => q.f (w j)) := by
            funext j; simp
          rw [e, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, map_mul, hpq, mul_sub] }
  have hPN : P ≤ N := by
    rintro _ ⟨w, rfl, hw⟩
    exact (hN _).2 ((hmem m w).2 fun i => Ideal.pow_le_pow_right (Nat.le_succ m) (hw i))
  have hspan : Submodule.span (C.A ⧸ adI C ^ m) (P : Set (Fin d → C.A ⧸ adI C ^ m)) = ⊤ := by
    rw [eq_top_iff]
    rintro v -
    let πC := Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ m) : adI C ^ (m + 1) ≤ adI C ^ m)
    let r : (Fin d → C.A ⧸ adI C ^ (m + 1)) → (Fin d → C.A ⧸ adI C ^ m) := fun y i => πC (y i)
    have hr : ∀ y ∈ Submodule.span (C.A ⧸ adI C ^ (m + 1)) (Set.range N'.subtype),
        r y ∈ Submodule.span (C.A ⧸ adI C ^ m) (P : Set (Fin d → C.A ⧸ adI C ^ m)) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨⟨x, hxN⟩, rfl⟩ := hx
        apply Submodule.subset_span
        obtain ⟨w, rfl⟩ : ∃ w : Fin d → C.A, (fun i => Ideal.Quotient.mk _ (w i)) = x :=
          ⟨fun i => (Ideal.Quotient.mk_surjective (x i)).choose,
            funext fun i => (Ideal.Quotient.mk_surjective (x i)).choose_spec⟩
        exact ⟨w, by funext i; simp [r, πC], (hmem (m + 1) w).1 ((hN' _).1 hxN)⟩
      | zero =>
        convert Submodule.zero_mem _ using 1
        funext i; simp [r]
      | add x y _ _ hx hy =>
        convert Submodule.add_mem _ hx hy using 1
        funext i; simp [r]
      | smul c x _ hx =>
        convert Submodule.smul_mem _ (πC c) hx using 1
        funext i; simp [r]
    obtain ⟨w, rfl⟩ : ∃ w : Fin d → C.A, (fun i => Ideal.Quotient.mk (adI C ^ m) (w i)) = v :=
      ⟨fun i => (Ideal.Quotient.mk_surjective (v i)).choose,
        funext fun i => (Ideal.Quotient.mk_surjective (v i)).choose_spec⟩
    have := hr (fun i => Ideal.Quotient.mk _ (w i)) (mem_span_range_of_isBaseChange hbN' _)
    convert this using 1
    funext i; simp [r, πC]
  have hNP : N ≤ P := le_of_span_eq_top_of_isBaseChange P N hPN hbN hspan
  have hzN : (fun i => Ideal.Quotient.mk (adI C ^ m) (z i)) ∈ N := (hN _).2 ((hmem m z).2 hz)
  obtain ⟨w, hw, hwE⟩ := hNP hzN
  exact ⟨w, fun i => Ideal.Quotient.eq.1 (congrFun hw i), hwE⟩

theorem lift_solution_succ : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (B C D : Obj l ↥(OL K)) (h : Hom B C) (f : Hom bk.prism C) (p q : Hom C D), Cover h → IsPO h h p q → ∀ (m : ℕ) (z : Fin d → C.A), (∀ i, p.f (z i) - (S.ε (p.comp f) (q.comp f)).mulVec (fun j => q.f (z j)) i ∈ adI D ^ m) → ∃ z' : Fin d → C.A, (∀ i, z' i - z i ∈ adI C ^ m) ∧ ∀ i, p.f (z' i) - (S.ε (p.comp f) (q.comp f)).mulVec (fun j => q.f (z' j)) i ∈ adI D ^ (m + 1) := by
  intro l _ K bk d S B C D h f p q hcov hpo m z hz
  refine lift_solution_succ_of_descent h p q hpo.comm m (hcov.ff m) _ (fun k => ?_) z hz
  exact (GlobalTheory.T.stratifiedPhiModule_descent_finite_level l K bk d S B C D h f p q hcov hpo k).imp fun N hN => ⟨hN.1, hN.2.2.2⟩

end GlobalTheory.BSP
end
end

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.RelEx

theorem map_smul_ring {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {m n : Type} (a : R)
    (M : Matrix m n R) : (a • M).map φ = φ a • M.map φ := by
  ext i j; simp

theorem alg {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (N : ℕ)
    (A Zf Zfi G Y Zg : Matrix n n R) (gE fE wi c lam : R) (hZ : Zf * Zfi = 1) (hAG : A * G = lam • Y)
    (hw : gE * wi = fE) (hc : c * lam = 1) :
    gE ^ N • (A * Zf * ((wi ^ N * c) • (Zfi * G * Zg))) = fE ^ N • (Y * Zg) := by
  have h1 : A * Zf * (Zfi * G * Zg) = lam • (Y * Zg) := by
    rw [Matrix.mul_assoc A Zf, ← Matrix.mul_assoc Zf, ← Matrix.mul_assoc Zf, hZ, Matrix.one_mul,
      ← Matrix.mul_assoc, hAG, Matrix.smul_mul]
  rw [Matrix.mul_smul, h1, smul_smul, smul_smul]
  congr 1
  calc gE ^ N * (wi ^ N * c) * lam = (gE * wi) ^ N * (c * lam) := by ring
    _ = fE ^ N := by rw [hw, hc, mul_one]

theorem cancel {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (Xf X'f Y G : Matrix n n R)
    (e lk lc : R) (he : e ∈ nonZeroDivisors R) (hXX : Xf * X'f = (lc * e) • 1) (hG : e • G = lk • (X'f * Y)) :
    Xf * G = (lk * lc) • Y := by
  have h2 : e • (Xf * G) = e • ((lk * lc) • Y) := by
    rw [← Matrix.mul_smul, hG, Matrix.mul_smul, ← Matrix.mul_assoc, hXX, Matrix.smul_mul, Matrix.one_mul,
      smul_smul, smul_smul]
    congr 1; ring
  ext i j
  have h3 := congrFun (congrFun h2 i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at h3
  exact (mul_cancel_left_mem_nonZeroDivisors he).1 h3

theorem map_unit_eq {R S : Type} [CommRing R] [CommRing S] (T : R →+* S) (a b : R) (w : Rˣ) (hw : a * w = b) :
    T b * T (↑w⁻¹ : R) = T a := by
  rw [← hw, ← map_mul, mul_assoc, Units.mul_inv, mul_one]

theorem inv_pow_map {R S : Type} [CommRing R] [CommRing S] (T : R →+* S) (x : R) (li : S) (h : li * T x = 1)
    (m : ℕ) : li ^ m * T (x ^ m) = 1 := by
  rw [map_pow, ← mul_pow, h, one_pow]

end GlobalTheory.BSP.RelEx

namespace GlobalTheory.BSP.Height

open GlobalTheory.BSP.RelEx

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} {bk : BK K} {d : ℕ}
  {ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]} {τ : Ainf l} {s : Seed bk d ρ τ} (ht : Height s)

theorem bas_map_disc {B : Obj l ↥(OL K)} (u : B.A) (h : Hom bk.prism B) (F : bk.DS bk.ρ₀ →+* Disc l u bk.ρ₀)
    (hF : IsDiscMap (l := _) (u := _) (ρ := _) (BK.hf h) F) :
    ht.bas.map F = (s.X.map (BK.hf h)).map (toDisc l u bk.ρ₀) * ht.Z.map F := by
  rw [Height.bas, Matrix.map_mul]
  congr 1
  ext i j
  simp only [Matrix.map_apply]
  exact hF.ext _

theorem rel_exists_of {B : Obj l ↥(OL K)} (u : B.A) (f g : Hom bk.prism B)
    (Ff Fg : bk.DS bk.ρ₀ →+* Disc l u bk.ρ₀) (hF : IsDiscMap (l := _) (u := _) (ρ := _) (BK.hf f) Ff) (hG : IsDiscMap (l := _) (u := _) (ρ := _) (BK.hf g) Fg)
    (w : B.Aˣ) (hw : BK.hf f bk.E * w = BK.hf g bk.E) (G : Matrix (Fin d) (Fin d) B.A) (m : ℕ)
    (hAG : s.X.map (BK.hf f) * G = (l : B.A) ^ m • s.X.map (BK.hf g)) :
    ∃ ε : Matrix (Fin d) (Fin d) (Disc l u bk.ρ₀), ht.Rel u f g ε := by
  obtain ⟨Z', hZ'⟩ : ∃ Z', ht.Z * Z' = 1 := by
    obtain ⟨U, hU⟩ := ht.Z_unit
    exact ⟨↑U⁻¹, by rw [← hU]; exact U.mul_inv⟩
  obtain ⟨li, hli⟩ : ∃ li : Disc l u bk.ρ₀, li * toDisc l u bk.ρ₀ (l : B.A) = 1 :=
    ((IsLocalization.Away.algebraMap_isUnit (S := PreDisc l u bk.ρ₀) (l : B.A)).map (ofPre l u bk.ρ₀)).exists_left_inv
  have key : toDisc l u bk.ρ₀ (BK.hf g bk.E) ^ s.N • (ht.bas.map Ff *
      ((toDisc l u bk.ρ₀ (↑w⁻¹ : B.A) ^ s.N * li ^ m) •
        (Z'.map Ff * G.map (toDisc l u bk.ρ₀) * ht.Z.map Fg))) =
      toDisc l u bk.ρ₀ (BK.hf f bk.E) ^ s.N • ht.bas.map Fg := by
    have e1 := ht.bas_map_disc u f Ff hF
    have e2 := ht.bas_map_disc u g Fg hG
    have h4 := alg s.N ((s.X.map (BK.hf f)).map (toDisc l u bk.ρ₀)) (ht.Z.map Ff) (Z'.map Ff)
      (G.map (toDisc l u bk.ρ₀)) ((s.X.map (BK.hf g)).map (toDisc l u bk.ρ₀)) (ht.Z.map Fg)
      (toDisc l u bk.ρ₀ (BK.hf g bk.E)) (toDisc l u bk.ρ₀ (BK.hf f bk.E))
      (toDisc l u bk.ρ₀ (↑w⁻¹ : B.A)) (li ^ m) (toDisc l u bk.ρ₀ ((l : B.A) ^ m))
      (by rw [← Matrix.map_mul, hZ', Matrix.map_one _ (map_zero _) (map_one _)])
      (by rw [← Matrix.map_mul, hAG, map_smul_ring])
      (map_unit_eq _ _ _ w hw)
      (inv_pow_map _ _ li hli m)
    exact (congrArg (fun M => toDisc l u bk.ρ₀ (BK.hf g bk.E) ^ s.N • (M *
      ((toDisc l u bk.ρ₀ (↑w⁻¹ : B.A) ^ s.N * li ^ m) • (Z'.map Ff * G.map (toDisc l u bk.ρ₀) * ht.Z.map Fg)))) e1).trans
      (h4.trans (congrArg (fun M => toDisc l u bk.ρ₀ (BK.hf f bk.E) ^ s.N • M) e2.symm))
  refine ⟨(toDisc l u bk.ρ₀ (↑w⁻¹ : B.A) ^ s.N * li ^ m) •
    (Z'.map Ff * G.map (toDisc l u bk.ρ₀) * ht.Z.map Fg), ?_⟩
  unfold Height.Rel
  intro Ff' Fg' hF' hG'
  have e1 : Ff' = Ff := (hF.unique hF').symm
  have e2 : Fg' = Fg := (hG.unique hG').symm
  subst e1 e2
  exact key

end GlobalTheory.BSP.Height

namespace GlobalTheory.BSP.Height

open GlobalTheory.BSP.RelEx

theorem rel_exists : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ)
    (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s)
    (B : Obj l ↥(OL K)) (u : B.A) (f g : Hom bk.prism B),
    ∃ ε : Matrix (Fin d) (Fin d) (Disc l u bk.ρ₀), ht.Rel u f g ε := by
  intro l _ K bk d ρ τ s ht B u f g
  by_cases hex : ∃ Ff Fg : bk.DS bk.ρ₀ →+* Disc l u bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) (BK.hf f) Ff ∧ IsDiscMap (BK.hf g) Fg
  swap
  · refine ⟨0, ?_⟩
    unfold Height.Rel
    intro Ff Fg hF hG
    exact (hex ⟨Ff, Fg, hF, hG⟩).elim
  obtain ⟨Ff, Fg, hF, hG⟩ := hex
  obtain ⟨hreg, ⟨w, hw⟩, -⟩ := GlobalTheory.T.breuilKisin_two_homs_E_regular_associated l K bk B f g
  obtain ⟨k, hk⟩ := s.nopole f g
  choose G hGc using hk
  have hXX : s.X.map (BK.hf f) * s.X'.map (BK.hf f) = ((l : B.A) ^ s.c₂ * BK.hf f bk.E ^ (2 * s.N)) • 1 := by
    rw [← Matrix.map_mul, s.X_mul, map_smul_ring, Matrix.map_one _ (map_zero _) (map_one _)]
    simp
  have hGm : BK.hf f bk.E ^ (2 * s.N) • Matrix.of G = (l : B.A) ^ k • (s.X'.map (BK.hf f) * s.X.map (BK.hf g)) := by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
    exact (hGc i j).symm
  have hAG : s.X.map (BK.hf f) * Matrix.of G = (l : B.A) ^ (k + s.c₂) • s.X.map (BK.hf g) := by
    rw [pow_add]
    exact cancel _ _ _ _ _ _ _ (pow_mem hreg _) (by rw [hXX, mul_comm]) hGm
  exact ht.rel_exists_of u f g Ff Fg hF hG w hw (Matrix.of G) (k + s.c₂) hAG

end GlobalTheory.BSP.Height
end
end

section

open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp GlobalTheory.SerSys GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders
open scoped Classical

namespace GlobalTheory.SerSys

theorem has_prod_of_inInd : ∀ (g : ℕ) [Fact g.Prime] (S : Sys g) (π : GLRep g) (L : List (GLRep g)), InInd π L → ∀ F, Has S π.2.ρ F → ∃ fs : List (ZMod g)[X], List.Forall₂ (fun (ρ : GLRep g) f => Has S ρ.2.ρ f) L fs ∧ F = fs.prod := by
  intro g _ S π L hL
  induction hL with
  | nil π h0 _ =>
    intro F hF
    refine ⟨[], List.Forall₂.nil, ?_⟩
    obtain ⟨n, r⟩ := π
    simp only at h0
    subst h0
    obtain ⟨v, -, hv⟩ := hF
    have hne : S.e 0 F ≠ 0 := by
      intro h
      apply hv
      simp [h, actK]
    obtain ⟨hm, hd, -⟩ := S.label 0 F hne
    simpa using Polynomial.eq_one_of_monic_natDegree_zero hm hd
  | cons π σ ρ L hπ _ _ hmap ih =>
    intro F hF
    obtain ⟨f, f', hf, hf', rfl⟩ :=
      GlobalTheory.T.seriesIdempotent_mul_of_maps_to_parabolicInduction g S π.1 σ.1 ρ.1 _ π.2.ρ _ _ σ.2.ρ ρ.2.ρ hπ hmap F hF
    obtain ⟨fs, hfs, rfl⟩ := ih f hf
    exact ⟨f' :: fs, List.Forall₂.cons hf' hfs, by simp [mul_comm]⟩

end GlobalTheory.SerSys
end
