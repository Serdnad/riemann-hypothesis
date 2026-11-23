module

public import Formalism.SatakeDualWeyl.Statement
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle645
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
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle631
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle634
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.LeftInv
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.Bundle001
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.PeakCone
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle007
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle004
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle005
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.IsTransl
public import Mathlib.Algebra.Group.Subgroup.Finite
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle622
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

namespace GlobalTheory.CompanionTheory.RapidDecay

abbrev FrameIx (r : ℕ) : Type := Option (Fin r ⊕ Fin r)

variable {E : Type} [Field E] {n r : ℕ}

def frameIdem (S : E →+* E) (J : Matrix (Fin n) (Fin n) E) (X Y : Matrix (Fin n) (Fin r) E) :
    FrameIx r → Matrix (Fin n) (Fin n) E
  | some (Sum.inl i) => X * single i i (1 : E) * (cT S Y * J)
  | some (Sum.inr i) => Y * single i i (1 : E) * (cT S X * J)
  | none => 1 - X * (cT S Y * J) - Y * (cT S X * J)

def frameWt (t : Fin r → ℝ) : FrameIx r → ℝ
  | some (Sum.inl i) => t i
  | some (Sum.inr i) => (t i)⁻¹
  | none => 1

def frameLev (s : Fin r) : FrameIx r → ℕ
  | some (Sum.inl i) => if i ≤ s then 2 else 1
  | some (Sum.inr i) => if i ≤ s then 0 else 1
  | none => 1

theorem sum_frameIdem (S : E →+* E) (J : Matrix (Fin n) (Fin n) E) (X Y : Matrix (Fin n) (Fin r) E) :
    ∑ α, frameIdem S J X Y α = 1 := by
  have key : ∀ (A : Matrix (Fin n) (Fin r) E) (B : Matrix (Fin r) (Fin n) E),
      ∑ i : Fin r, (A * (Matrix.single i i (1 : E) : Matrix (Fin r) (Fin r) E) * B : Matrix (Fin n) (Fin n) E) = A * B := fun A B => by
    rw [← Matrix.sum_mul, ← Matrix.mul_sum, Matrix.sum_single_one, Matrix.mul_one]
  rw [Fintype.sum_option, Fintype.sum_sum_type]
  simp only [frameIdem]
  rw [key, key]
  abel

theorem frameWt_pos {t : Fin r → ℝ} (ht : ∀ i, 0 < t i) (α : FrameIx r) : 0 < frameWt t α := by
  rcases α with _ | i | i
  · exact one_pos
  · exact ht i
  · exact inv_pos.2 (ht i)

end GlobalTheory.CompanionTheory.RapidDecay

end
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.FA
open scoped Classical
open GlobalTheory.CompanionTheory.FinActS

namespace GlobalTheory.CompanionTheory.FinActS.SumFiber

theorem finsum_cosets_retraction {Γ H : Type} [Group Γ] [Group H] (p : Γ →* H) (e : H →* Γ)
    (hpe : ∀ m, p (e m) = m)
    (L : Subgroup Γ) (V : Subgroup H) (hLV : ∀ u ∈ L, p u ∈ V) (φ : Γ → ℂ)
    (hφ : ∀ u ∈ L, ∀ x, φ (x * u) = φ x) (hfin : {q : Γ ⧸ L | φ q.out ≠ 0}.Finite) :
    ∑ᶠ q : Γ ⧸ L, φ q.out =
      ∑ᶠ m : H ⧸ V, ∑ᶠ q : Γ ⧸ L,
        (V : Set H).indicator (1 : H → ℂ) (p q.out) * φ (e m.out * q.out) := by
  have outL : ∀ x : Γ, ∃ u ∈ L, (QuotientGroup.mk x : Γ ⧸ L).out = x * u := by
    intro x
    obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul L x
    exact ⟨u, u.2, hu⟩
  have outV : ∀ x : H, ∃ u ∈ V, (QuotientGroup.mk x : H ⧸ V).out = x * u := by
    intro x
    obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul V x
    exact ⟨u, u.2, hu⟩
  have hφout : ∀ x : Γ, φ (QuotientGroup.mk x : Γ ⧸ L).out = φ x := by
    intro x
    obtain ⟨u, hu, h⟩ := outL x
    rw [h, hφ u hu]
  let S : Set (Γ ⧸ L) := {q | p q.out ∈ V}
  have hS : ∀ x : Γ, p x ∈ V → (QuotientGroup.mk x : Γ ⧸ L) ∈ S := by
    intro x hx
    obtain ⟨u, hu, h⟩ := outL x
    change p (QuotientGroup.mk x : Γ ⧸ L).out ∈ V
    rw [h, map_mul]
    exact V.mul_mem hx (hLV u hu)
  let T : (H ⧸ V) × S → Γ ⧸ L := fun a => QuotientGroup.mk (e a.1.out * a.2.1.out)
  have hinj : Function.Injective T := by
    rintro ⟨m, q, hq⟩ ⟨m', q', hq'⟩ h
    have hq1 : p q.out ∈ V := hq
    have hq2 : p q'.out ∈ V := hq'
    have h1 : (e m.out * q.out)⁻¹ * (e m'.out * q'.out) ∈ L := QuotientGroup.eq.1 h
    have h2 := hLV _ h1
    simp only [map_mul, map_inv, hpe] at h2
    have hm : m = m' := by
      rw [← QuotientGroup.out_eq' m, ← QuotientGroup.out_eq' m']
      refine QuotientGroup.eq.2 ?_
      have h3 : m.out⁻¹ * m'.out
          = p q.out * ((p q.out)⁻¹ * m.out⁻¹ * (m'.out * p q'.out)) * (p q'.out)⁻¹ := by
        group
      rw [h3]
      refine V.mul_mem (V.mul_mem hq1 ?_) (V.inv_mem hq2)
      simpa [_root_.mul_inv_rev] using h2
    subst hm
    have hqq : q = q' := by
      rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
      refine QuotientGroup.eq.2 ?_
      have h3 : q.out⁻¹ * q'.out = (e m.out * q.out)⁻¹ * (e m.out * q'.out) := by group
      rw [h3]
      exact h1
    subst hqq
    rfl
  have hsurj : Function.Surjective T := by
    intro q
    obtain ⟨v, hv, hm⟩ := outV (p q.out)
    let m : H ⧸ V := QuotientGroup.mk (p q.out)
    have hmem : p ((e m.out)⁻¹ * q.out) ∈ V := by
      have : p ((e m.out)⁻¹ * q.out) = v⁻¹ := by
        simp only [map_mul, map_inv, hpe, m]
        rw [hm]
        group
      rw [this]
      exact V.inv_mem hv
    refine ⟨(m, ⟨QuotientGroup.mk ((e m.out)⁻¹ * q.out), hS _ hmem⟩), ?_⟩
    obtain ⟨u, hu, h⟩ := outL ((e m.out)⁻¹ * q.out)
    change (QuotientGroup.mk (e m.out * (QuotientGroup.mk ((e m.out)⁻¹ * q.out) : Γ ⧸ L).out) :
      Γ ⧸ L) = q
    rw [h]
    refine Eq.trans (QuotientGroup.eq.2 ?_) (QuotientGroup.out_eq' q)
    have h3 : (e m.out * ((e m.out)⁻¹ * q.out * u))⁻¹ * q.out = u⁻¹ := by group
    rw [h3]
    exact L.inv_mem hu
  let E : (H ⧸ V) × S ≃ Γ ⧸ L := Equiv.ofBijective T ⟨hinj, hsurj⟩
  have hsupp : (Function.support
      (fun a : (H ⧸ V) × S => φ (e a.1.out * a.2.1.out))).Finite := by
    refine (hfin.preimage (f := T) hinj.injOn).subset ?_
    intro a ha
    change φ (QuotientGroup.mk (e a.1.out * a.2.1.out) : Γ ⧸ L).out ≠ 0
    rw [hφout]
    exact ha
  calc ∑ᶠ q : Γ ⧸ L, φ q.out
      = ∑ᶠ a : (H ⧸ V) × S, φ (E a).out :=
        (finsum_comp_equiv E (f := fun q : Γ ⧸ L => φ q.out)).symm
    _ = ∑ᶠ a : (H ⧸ V) × S, φ (e a.1.out * a.2.1.out) :=
        finsum_congr fun a => hφout _
    _ = ∑ᶠ m : H ⧸ V, ∑ᶠ q : S, φ (e m.out * q.1.out) :=
        finsum_curry (fun a : (H ⧸ V) × S => φ (e a.1.out * a.2.1.out)) hsupp
    _ = _ := by
        refine finsum_congr fun m => ?_
        rw [finsum_set_coe_eq_finsum_mem S (f := fun q : Γ ⧸ L => φ (e m.out * q.out)),
          finsum_mem_def]
        refine finsum_congr fun q => ?_
        by_cases hq : p q.out ∈ V
        · have hq' : q ∈ S := hq
          rw [Set.indicator_of_mem hq', Set.indicator_of_mem (show p q.out ∈ (V : Set H) from hq)]
          simp
        · have hq' : q ∉ S := hq
          rw [Set.indicator_of_notMem hq',
            Set.indicator_of_notMem (show p q.out ∉ (V : Set H) from hq)]
          simp

end GlobalTheory.CompanionTheory.FinActS.SumFiber
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.FA
open scoped Classical
open GlobalTheory.CompanionTheory.FinActS

namespace GlobalTheory.CompanionTheory.FinActS

theorem map_list_prod_embed_of_nodup {ι Γ : Type} [Group Γ] {Hl : ι → Type} [∀ i, Group (Hl i)]
    (p : ∀ i, Γ →* Hl i) (e : ∀ i, Hl i →* Γ)
    (hpe : ∀ i m, p i (e i m) = m) (hpe' : ∀ i j m, i ≠ j → p j (e i m) = 1)
    (f : ∀ i, Hl i) (j : ι) (l : List ι) (hl : l.Nodup) :
    p j (l.map fun i => e i (f i)).prod = if j ∈ l then f j else 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hnd := List.nodup_cons.mp hl
    have ih' := ih hnd.2
    rw [List.map_cons, List.prod_cons, map_mul, ih']
    by_cases hja : a = j
    · subst hja
      simp [hnd.1, hpe]
    · have hne : ¬ j = a := fun h => hja h.symm
      rw [hpe' a j _ hja, one_mul]
      simp [hne]

theorem exists_local_levels_le_open : ∀ {ι Γ : Type} [Group Γ] {Hl : ι → Type} [∀ i, Group (Hl i)] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [∀ i, TopologicalSpace (Hl i)] [∀ i, T2Space (Hl i)]
    (p : ∀ i, Γ →* Hl i) (e : ∀ i, Hl i →* Γ) (K : Subgroup Γ) (KH : ∀ i, Subgroup (Hl i))
    (hpc : ∀ i, Continuous (p i)) (hec : ∀ i, Continuous (e i))
    (hpe : ∀ i m, p i (e i m) = m) (hpe' : ∀ i j m, i ≠ j → p j (e i m) = 1)
    (hsep : ∀ x y : Γ, (∀ i, p i x = p i y) → x = y)
    (hK : ∀ x, x ∈ K ↔ ∀ i, p i x ∈ KH i) (hKc : IsCompact (K : Set Γ))
    (hKo : ∀ i, IsOpen (KH i : Set (Hl i))) (U : Subgroup Γ) (hU : IsOpen (U : Set Γ)),
    ∃ V : ∀ i, Subgroup (Hl i), (∀ i, IsOpen (V i : Set (Hl i))) ∧ (∀ i, V i ≤ KH i) ∧
      (∀ᶠ i in cofinite, V i = KH i) ∧ ∀ u, (∀ i, p i u ∈ V i) → u ∈ U := by
  intro ι Γ _ Hl _ _ _ _ _ p e K KH hpc hec hpe hpe' hsep hK hKc hKo U hU
  classical
  have hcomp : IsCompact ((K : Set Γ) \ (U : Set Γ)) := hKc.diff hU
  have hopen : ∀ i, IsOpen {x : Γ | p i x ≠ 1} := fun i =>
    (isOpen_ne (x := (1 : Hl i))).preimage (hpc i)
  have hcover : (K : Set Γ) \ (U : Set Γ) ⊆ ⋃ i, {x : Γ | p i x ≠ 1} := by
    intro x hx
    by_contra hcon
    have hall : ∀ i, p i x = p i 1 := by
      intro i
      by_contra hi
      exact hcon (Set.mem_iUnion.mpr ⟨i, by simpa using hi⟩)
    have hx1 : x = 1 := hsep x 1 hall
    exact hx.2 (hx1 ▸ U.one_mem)
  obtain ⟨T, hT⟩ := hcomp.elim_finite_subcover _ hopen hcover
  have hTU : ∀ x, x ∈ K → (∀ i ∈ T, p i x = 1) → x ∈ U := by
    intro x hxK hx
    by_contra hxU
    have hmem := hT ⟨hxK, hxU⟩
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hmem
    obtain ⟨i, hi, hne⟩ := hmem
    exact hne (hx i hi)
  refine ⟨fun i => if i ∈ T then KH i ⊓ U.comap (e i) else KH i, ?_, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i ∈ T
    · simp only [hi, if_true]
      exact (hKo i).inter (hU.preimage (hec i))
    · simp only [hi, if_false]
      exact hKo i
  · intro i
    by_cases hi : i ∈ T
    · simp only [hi, if_true]
      exact inf_le_left
    · simp only [hi, if_false]
      exact le_rfl
  · have hfin : ∀ᶠ i in cofinite, i ∉ T := T.finite_toSet.compl_mem_cofinite
    filter_upwards [hfin] with i hi
    simp only [hi, if_false]
  · intro u hu
    have hle : ∀ i, p i u ∈ KH i := by
      intro i
      have := hu i
      by_cases hi : i ∈ T
      · simp only [hi, if_true] at this
        exact this.1
      · simpa only [hi, if_false] using this
    have huK : u ∈ K := (hK u).mpr hle
    set v : Γ := (T.toList.map fun i => e i (p i u)).prod with hv
    have hpv : ∀ j, p j v = if j ∈ T then p j u else 1 := by
      intro j
      have := map_list_prod_embed_of_nodup p e hpe hpe' (fun i => p i u) j T.toList T.nodup_toList
      simpa [hv] using this
    have hvU : v ∈ U := by
      refine U.list_prod_mem ?_
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have hiT : i ∈ T := Finset.mem_toList.mp hi
      have := hu i
      simp only [hiT, if_true] at this
      exact this.2
    have hwK : v⁻¹ * u ∈ K := by
      refine (hK _).mpr fun j => ?_
      rw [map_mul, map_inv, hpv j]
      by_cases hj : j ∈ T
      · simp [hj, (KH j).one_mem]
      · simpa [hj] using hle j
    have hwU : v⁻¹ * u ∈ U := by
      refine hTU _ hwK fun i hi => ?_
      rw [map_mul, map_inv, hpv i]
      simp [hi]
    have := U.mul_mem hvU hwU
    simpa using this

end GlobalTheory.CompanionTheory.FinActS
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.FA
open scoped Classical
open GlobalTheory.CompanionTheory.FinActS

namespace GlobalTheory.CompanionTheory.FinActS

theorem finite_cosets_of_components_mem
    {ι Γ : Type} [Group Γ] {Hl : ι → Type} [∀ i, Group (Hl i)] (p : ∀ i, Γ →* Hl i)
    (V : ∀ i, Subgroup (Hl i)) (Q : ∀ i, Set (Hl i))
    (hQ : ∀ i, ∀ x ∈ Q i, ∀ u ∈ V i, x * u ∈ Q i)
    (hQf : ∀ i, {q : Hl i ⧸ V i | q.out ∈ Q i}.Finite)
    (hQV : ∀ᶠ i in cofinite, Q i ⊆ V i) :
    {q : Γ ⧸ (⨅ i, (V i).comap (p i)) | ∀ i, p i q.out ∈ Q i}.Finite := by
  have hT : {i | ¬ Q i ⊆ V i}.Finite := Filter.eventually_cofinite.mp hQV
  haveI : Finite {i | ¬ Q i ⊆ V i} := hT.to_subtype
  let f : Γ ⧸ (⨅ i, (V i).comap (p i)) → ∀ i : {i | ¬ Q i ⊆ V i}, Hl i.1 ⧸ V i.1 :=
    fun q i => ((p i.1 q.out : Hl i.1) : Hl i.1 ⧸ V i.1)
  have hfin : (Set.univ.pi fun i : {i | ¬ Q i ⊆ V i} =>
      {c : Hl i.1 ⧸ V i.1 | c.out ∈ Q i.1}).Finite :=
    Set.Finite.pi fun i => hQf i.1
  refine Set.Finite.of_injOn (f := f) ?_ ?_ hfin
  · intro q hq i _
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (V i.1) (p i.1 q.out)
    show (((p i.1 q.out : Hl i.1) : Hl i.1 ⧸ V i.1)).out ∈ Q i.1
    rw [hh]
    exact hQ i.1 _ (hq i.1) _ h.2
  · intro q hq q' hq' hfq
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
    refine QuotientGroup.eq.mpr ?_
    refine Subgroup.mem_iInf.mpr fun i => ?_
    rw [Subgroup.mem_comap, map_mul, map_inv]
    by_cases hi : Q i ⊆ V i
    · exact (V i).mul_mem ((V i).inv_mem (hi (hq i))) (hi (hq' i))
    · exact QuotientGroup.eq.mp (congrFun hfq ⟨i, hi⟩)

end GlobalTheory.CompanionTheory.FinActS
end

section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct NNReal

theorem _root_.GlobalTheory.T.split_order_fg_ideal_product : ∀ {k R : Type} [Field k] [CommRing R] (O : ValuationSubring k) (φ : R ≃+* k × k) (𝔬 : Subring R), (∀ r, r ∈ 𝔬 ↔ (φ r).1 ∈ O ∧ (φ r).2 ∈ O) → ∀ I : Submodule 𝔬 R, I.FG → ∃ α β : k, ∀ r, r ∈ I ↔ (∃ x ∈ O, (φ r).1 = α * x) ∧ (∃ y ∈ O, (φ r).2 = β * y) := by
  first | exact @GlobalTheory.CompanionTheory.KFin.fg_eq_prod_principal | exact GlobalTheory.CompanionTheory.KFin.fg_eq_prod_principal | (intros; apply GlobalTheory.CompanionTheory.KFin.fg_eq_prod_principal <;> assumption)
end
