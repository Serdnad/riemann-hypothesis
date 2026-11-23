module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle003
public import Formalism.HermitianLattices.Bundle003
public import Mathlib.Order.CompletePartialOrder
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle043
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle045
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle025
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DualInterSelfDualHermitianLatticeSubspace
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle046
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle047
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
public import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

theorem _root_.GlobalTheory.T.primitive_sublattices_move_with_isometries : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → ∀ (g : isom h) (L : Submodule (𝓞 K) V) (U : Submodule K V) (j n : ℕ), (g • U ∈ primSp h (g • L) j n ↔ U ∈ primSp h L j n) ∧ (primSp h (g • L) j n).encard = (primSp h L j n).encard := by
  first | exact @GlobalTheory.Mass.PrimMove.main | exact GlobalTheory.Mass.PrimMove.main | (intros; apply GlobalTheory.Mass.PrimMove.main <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem exists_common_goodSub {W : Type} [AddCommGroup W] (W0 : AddSubgroup W) {ι : Type}
    (s : Finset ι) (S : ι → Set W) (h : ∀ i ∈ s, IsCO W0 (S i)) :
    ∃ A, GoodSub W0 A ∅ ∧ ∀ i ∈ s, GoodSub W0 A (S i) := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨W0, ⟨by simp, by simp, by simp, by simp⟩, by simp⟩
  | insert j s hj ih =>
    obtain ⟨A, hA0, hA⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    obtain ⟨B, hB⟩ := h j (Finset.mem_insert_self _ _)
    have h1 : (A ⊓ B).relIndex A ≠ 0 := by
      rw [AddSubgroup.inf_relIndex_left]
      exact AddSubgroup.relIndex_ne_zero_trans hB.1 hA0.2.1
    have h2 : (A ⊓ B).relIndex B ≠ 0 := by
      rw [AddSubgroup.inf_relIndex_right]
      exact AddSubgroup.relIndex_ne_zero_trans hA0.1 hB.2.1
    refine ⟨A ⊓ B, (GlobalTheory.T.commensurableCosetUnionContent_independent_nonneg W0 ∅).2.1 A _ hA0 inf_le_left h1, fun i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact (GlobalTheory.T.commensurableCosetUnionContent_independent_nonneg W0 _).2.1 B _ hB inf_le_right h2
    · exact (GlobalTheory.T.commensurableCosetUnionContent_independent_nonneg W0 _).2.1 A _ (hA i hi) inf_le_left h1

theorem cont_biUnion : ∀ {W : Type} [AddCommGroup W] (W0 : AddSubgroup W) {ι : Type} (s : Finset ι) (S : ι → Set W), (∀ i ∈ s, IsCO W0 (S i)) → IsCO W0 (⋃ i ∈ s, S i) ∧ ((∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (S i) (S j)) → cont W0 (⋃ i ∈ s, S i) = ∑ i ∈ s, cont W0 (S i)) := by
  intro W _ W0 ι s S h
  obtain ⟨A, hA0, hA⟩ := exists_common_goodSub W0 s S h
  have himg : (QuotientAddGroup.mk : W → W ⧸ A) '' (⋃ i ∈ s, S i) =
      ⋃ i ∈ s, (QuotientAddGroup.mk : W → W ⧸ A) '' S i := by
    simp only [Set.image_iUnion]
  have hU : GoodSub W0 A (⋃ i ∈ s, S i) := by
    refine ⟨hA0.1, hA0.2.1, ?_, ?_⟩
    · intro x hx a ha
      simp only [Set.mem_iUnion] at hx ⊢
      obtain ⟨i, hi, hx⟩ := hx
      exact ⟨i, hi, (hA i hi).2.2.1 x hx a ha⟩
    · rw [himg]
      exact Set.Finite.biUnion s.finite_toSet fun i hi => (hA i hi).2.2.2
  refine ⟨⟨A, hU⟩, fun hd => ?_⟩
  rw [(GlobalTheory.T.commensurableCosetUnionContent_independent_nonneg W0 _).1 A hU,
    Finset.sum_congr rfl fun i hi => (GlobalTheory.T.commensurableCosetUnionContent_independent_nonneg W0 (S i)).1 A (hA i hi), ← Finset.sum_mul, himg]
  congr 1
  have key := Set.Finite.ncard_biUnion (t := (s : Set ι))
    (s := fun i => (QuotientAddGroup.mk : W → W ⧸ A) '' S i) s.finite_toSet
    (fun i hi => (hA i hi).2.2.2) (by
      intro i hi j hj hij
      refine Set.disjoint_left.2 ?_
      rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
      have hm : -y + x ∈ A := QuotientAddGroup.eq.1 hxy
      have := (hA j hj).2.2.1 y hy _ hm
      rw [add_neg_cancel_left] at this
      exact Set.disjoint_left.1 (hd i hi j hj hij) hx this)
  rw [finsum_mem_coe_finset] at key
  exact_mod_cast key

end GlobalTheory.HL
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.eichlerMove_scalar_fibre_measure_one : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 0 ≤ S.a → ∀ u : S.V, (S.InZ u → cint S.refT (ind fun t : E => (∃ c ∈ L.O, algebraMap F E 2⁻¹ * S.h u u + t = algebraMap F E ((S.ϖ : F) ^ S.a) * c) ∧ t + L.cj t = 0) = 1) ∧ ((∃ t : E, (∃ c ∈ L.O, algebraMap F E 2⁻¹ * S.h u u + t = algebraMap F E ((S.ϖ : F) ^ S.a) * c) ∧ t + L.cj t = 0) → S.InZ u) := by
  first | exact @GlobalTheory.MoveFibre.fibre_scalar | exact GlobalTheory.MoveFibre.fibre_scalar | (intros; apply GlobalTheory.MoveFibre.fibre_scalar <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.MoveChar

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem coords {g : Fin (r + 1) → S.V} {n : S.GLV} (hn : n ∈ S.Nof g) (j : Fin r) {x : S.V}
    (hx : x ∈ S.spanTo g (j + 1)) :
    ∃ c : Fin (r + 1) → E, (∀ i : Fin (r + 1), (j : ℕ) + 1 ≤ i → c i = 0) ∧ x = ∑ i, c i • n (g i) := by
  have h1 : ∀ v, n v ∈ S.spanTo g (j + 1) ↔ v ∈ S.spanTo g (j + 1) :=
    (Subgroup.mem_iInf.1 hn.1.2 j).1
  obtain ⟨y, rfl⟩ := n.surjective x
  have hy := (h1 y).1 hx
  clear hx
  induction hy using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨i, hi, rfl⟩ := hv
    refine ⟨Pi.single i 1, fun i' hi' => Pi.single_eq_of_ne ?_ _, ?_⟩
    · rintro rfl
      exact absurd hi (not_lt.2 hi')
    · simp [Pi.single_apply]
  | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨c, h, e⟩ := ha
    obtain ⟨c', h', e'⟩ := hb
    exact ⟨c + c', fun i hi => by simp [h i hi, h' i hi],
      by rw [map_add (f := _), e, e']; simp [add_smul, Finset.sum_add_distrib]⟩
  | smul t a _ ha =>
    obtain ⟨c, h, e⟩ := ha
    exact ⟨t • c, fun i hi => by simp [h i hi],
      by rw [map_smul, e]; simp [Finset.smul_sum, mul_smul]⟩

theorem uniq {g g' : Fin (r + 1) → S.V} (hl : LinearIndependent E (Sum.elim g g'))
    {a a' b b' : Fin (r + 1) → E}
    (h : ∑ i, a i • g i + ∑ i, a' i • g' i = ∑ i, b i • g i + ∑ i, b' i • g' i) :
    a = b ∧ a' = b' := by
  have := Fintype.linearIndependent_iffₛ.1 hl (Sum.elim a a') (Sum.elim b b')
    (by simpa [Fintype.sum_sum_type] using h)
  exact ⟨funext fun i => this (.inl i), funext fun i => this (.inr i)⟩

theorem lev_le_iff {g g' : Fin (r + 1) → S.V} (hl : LinearIndependent E (Sum.elim g g'))
    (a a' : Fin (r + 1) → E) (j : ℕ) :
    S.lev g g' (∑ i, a i • g i + ∑ i, a' i • g' i) ≤ j ↔
      ∀ i : Fin (r + 1), j ≤ (i : ℕ) → S.RR (a i) (a' i) := by
  refine ⟨fun h i hi => ?_, fun h => Nat.sInf_le ⟨a, a', rfl, h⟩⟩
  have hne : {j : ℕ | ∃ al al' : Fin (r + 1) → E,
      ∑ i, a i • g i + ∑ i, a' i • g' i = ∑ i, al i • g i + ∑ i, al' i • g' i ∧
      ∀ i : Fin (r + 1), j ≤ (i : ℕ) → S.RR (al i) (al' i)}.Nonempty :=
    ⟨r + 1, a, a', rfl, fun i hi => absurd i.2 (not_lt.2 hi)⟩
  obtain ⟨b, b', e, hb⟩ := Nat.sInf_mem hne
  obtain ⟨rfl, rfl⟩ := uniq S hl e
  exact hb i (le_trans h hi)

theorem exists_family {g g' : Fin (r + 1) → S.V} (hl : LinearIndependent E (Sum.elim g g'))
    {J : ℕ} (hJ : J ≤ r + 1) : ∃ y : Fin (J + J) → S.V, LinearIndependent E y ∧
      Submodule.span E (Set.range y) = S.spanTo g J ⊔ S.spanTo g' J := by
  refine ⟨Sum.elim g g' ∘ (Sum.map (Fin.castLE hJ) (Fin.castLE hJ) ∘ finSumFinEquiv.symm),
    hl.comp _ (((Fin.castLE_injective hJ).sumMap (Fin.castLE_injective hJ)).comp
      finSumFinEquiv.symm.injective), ?_⟩
  have e : ∀ g : Fin (r + 1) → S.V, Set.range (g ∘ Fin.castLE hJ) = g '' {i | (i : ℕ) < J} := by
    intro g
    rw [Set.range_comp, Fin.range_castLE]
  rw [← Function.comp_assoc, finSumFinEquiv.symm.surjective.range_comp, Sum.elim_comp_map,
    Set.Sum.elim_range, e, e, Submodule.span_union]
  rfl

end GlobalTheory.HL.MoveChar

theorem GlobalTheory.HL.MoveChar.chi_ne_one : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ x ∈ S.spanTo S.f (j + 1), ∀ x' ∈ S.spanTo S.f' (j + 1), S.InTh Λ (x + x') → S.lev (S.fr d Λ) (S.fr' d Λ) (x + x') = j + 1 → ∀ al al' : Fin (r + 1) → E, x = ∑ i, al i • S.fr d Λ i → x' = ∑ i, al' i • S.fr' d Λ i → ∃ u ∈ Λ, u ∈ perp L S.Hm (S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1)) ∧ L.psi0 (-(algebraMap F E S.th⁻¹ * S.h (al j.castSucc • S.fr d Λ j.succ + al' j.castSucc • S.fr' d Λ j.succ) u)) ≠ 1 := by
  intro F _ _ _ _ _ E _ _ _ L r k S j β βJ d Λ hT hFF x hx x' hx' _ hlev al al' ex ex'
  obtain ⟨hSD, hW, -, h1, h2, hl, -⟩ := TermBasic.term_basic L r k S d Λ hT
  obtain ⟨hl0, -, -, -, -, hth, -⟩ := GlobalTheory.FrameBasic.main L r k S
  obtain ⟨-, -, hn, hn', -⟩ := hW

  have hRR : ¬ S.RR (al j.castSucc) (al' j.castSucc) := by
    intro hR
    obtain ⟨c, hc, e⟩ := MoveChar.coords S hn j hx
    obtain ⟨c', hc', e'⟩ := MoveChar.coords S hn' j hx'
    obtain ⟨rfl, rfl⟩ := MoveChar.uniq S hl (a := al) (a' := al') (b := c) (b' := c')
      (by rw [← ex, ← ex']; exact congrArg₂ (· + ·) e e')
    have : S.lev (S.fr d Λ) (S.fr' d Λ) (x + x') ≤ j := by
      rw [ex, ex', MoveChar.lev_le_iff S hl]
      intro i hi
      rcases hi.eq_or_lt with hi | hi
      · rwa [show i = j.castSucc from Fin.ext hi.symm]
      · rw [hc i hi, hc' i hi]
        exact ⟨L.O.zero_mem, 0, L.O.zero_mem, by simp⟩
    omega
  by_contra hcon
  push Not at hcon
  set z := al j.castSucc • S.fr d Λ j.succ + al' j.castSucc • S.fr' d Λ j.succ with hz
  obtain ⟨y, hy, ey⟩ := MoveChar.exists_family S hl0 (J := j + 1) (by omega)
  have hd := (DualInter.dual_inter L S.Hm S.herm Λ hSD _ y hy).2.1 (algebraMap F E S.th⁻¹ • z)
  rw [ey] at hd
  obtain ⟨a, ha, haY⟩ := hd.1 fun u hu huY => by
    have : -(algebraMap F E S.th⁻¹ * S.h z u) ∈ L.O := by
      refine (L.additive_character_dual_ring _).1 fun c hc => ?_
      have := hcon (L.cj c • u) (Λ.smul_mem ⟨_, GlobalTheory.UnramOrder.cj_mem L hc⟩ hu)
        (Submodule.smul_mem _ _ huY)
      rw [← this, Frames.h, Frames.h, DualInter.smul_r, L.cj_cj]
      congr 1
      ring
    rw [← DualInter.cj_hf S.herm, DualInter.smul_l]
    exact GlobalTheory.UnramOrder.cj_mem L (neg_mem_iff.1 this)
  have hjr : (j : ℕ) + 1 ≤ r + 1 := by omega
  have hzM : z ∈ S.ME :=
    Submodule.add_mem_sup
      (Submodule.smul_mem _ _ ((h1 (r + 1) le_rfl _).2 (Submodule.subset_span ⟨j.succ, j.succ.2, rfl⟩)).2)
      (Submodule.smul_mem _ _ ((h2 (r + 1) le_rfl _).2 (Submodule.subset_span ⟨j.succ, j.succ.2, rfl⟩)).2)
  have haM : a ∈ S.ME := by
    have := S.ME.sub_mem (S.ME.smul_mem (algebraMap F E S.th⁻¹) hzM)
      (sup_le_sup (TermBasic.spanTo_mono S S.f hjr) (TermBasic.spanTo_mono S S.f' hjr) haY)
    rwa [sub_sub_cancel] at this
  have hla : S.levC d Λ a ≤ j + 1 := hFF.2.2.1 a ⟨ha, haM⟩
  obtain ⟨v, hv, v', hv', e0⟩ := Submodule.mem_sup.1 (Submodule.smul_mem _ (algebraMap F E S.th) haY)
  obtain ⟨c, hc, e⟩ := MoveChar.coords S hn j hv
  obtain ⟨c', hc', e'⟩ := MoveChar.coords S hn' j hv'
  have key : algebraMap F E S.th • a =
      ∑ i, (Pi.single j.succ (al j.castSucc) - c : Fin (r + 1) → E) i • S.fr d Λ i +
        ∑ i, (Pi.single j.succ (al' j.castSucc) - c' : Fin (r + 1) → E) i • S.fr' d Λ i := by
    rw [smul_sub, smul_smul, ← map_mul, mul_inv_cancel₀ hth, map_one, one_smul] at e0
    have e1 : v = ∑ i, c i • S.fr d Λ i := e
    have e2 : v' = ∑ i, c' i • S.fr' d Λ i := e'
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, ← e1, ← e2, Pi.single_apply, ite_smul,
      zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [sub_add_sub_comm, e0, ← hz, sub_sub_cancel]
  rw [Frames.levC, key, MoveChar.lev_le_iff S hl] at hla
  have := hla j.succ (by simp)
  rw [Pi.sub_apply, Pi.sub_apply, hc _ (by simp), hc' _ (by simp), Pi.single_eq_same, Pi.single_eq_same,
    sub_zero, sub_zero] at this
  exact hRR this
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.NormalFormRescaled

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)

theorem eich_smul_base (c : E) (hc : L.cj c = c) (x u : Fin n → E) (s : E) (v : Fin n → E) :
    eich L Hm (c • x) u s v = eich L Hm x (c • u) (c ^ 2 * s) v := by
  simp only [eich, Eichler.hf_smul_r, Eichler.hf_smul_l, hc]
  module

theorem cj_alg (a : F) : L.cj (algebraMap F E a) = algebraMap F E a := L.cj.commutes a

omit [TopologicalSpace E] in
theorem alg_inv_mul (a : Fˣ) : algebraMap F E ((a⁻¹ : Fˣ) : F) * algebraMap F E (a : F) = 1 := by
  rw [← map_mul, Units.inv_mul, map_one]

omit [TopologicalSpace E] in
theorem alg_mul_inv (a : Fˣ) : algebraMap F E (a : F) * algebraMap F E ((a⁻¹ : Fˣ) : F) = 1 := by
  rw [← map_mul, Units.mul_inv, map_one]

end

end GlobalTheory.HL.NormalFormRescaled


open GlobalTheory.HL.NormalFormRescaled in
theorem GlobalTheory.HL.nof_normal_form_rescaled : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (r k : ℕ) (S : Frames L r k) (g : Fin (r + 1) → S.V) (gs : Fin r → S.V) (hsel : (g = S.f ∧ gs = S.es) ∨ (g = S.f' ∧ gs = S.es')) (a : Fin r → Fˣ) (X Y : Fin r → S.V) (hX : ∀ i, algebraMap F E (a i) • g i.castSucc = X i) (hY : ∀ i, gs i = algebraMap F E (a i) • Y i), (∀ i j, S.h (X i) (Y j) = if i = j then 1 else 0) ∧ (∀ i j, S.h (X i) (X j) = 0) ∧ (∀ i j, S.h (Y i) (Y j) = 0) ∧ ∀ n : S.GLV, n ∈ S.Nof g ↔ ∃ (u : Fin r → S.V) (s : Fin r → E) (e : Fin r → S.GLV), (∀ i, (∀ j, j ≤ i → S.h (u i) (X j) = 0 ∧ S.h (u i) (Y j) = 0) ∧ s i + L.cj (s i) = S.h (u i) (u i) ∧ ∀ v, e i v = eich L S.Hm (X i) (u i) (s i) v) ∧ n = (List.ofFn e).prod := by
  intro F _ _ _ _ _ E _ _ _ L r k S g gs hsel a X Y hX hY
  have hgg : ∀ i j : Fin r, hf L S.Hm (g i.castSucc) (g j.castSucc) = 0 := by
    intro i j
    rcases hsel with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 h2
    · rw [S.gram]; simp [Fin.castSucc_ne_last]
    · rw [S.gram']; simp [Fin.castSucc_ne_last]
  have hgs : ∀ i j : Fin r, hf L S.Hm (g i.castSucc) (gs j) = if i = j then 1 else 0 := by
    intro i j
    rcases hsel with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 h2
    · rw [S.dual]; simp [Fin.castSucc_inj]
    · rw [S.dual']; simp [Fin.castSucc_inj]
  have hss : ∀ i j : Fin r, hf L S.Hm (gs i) (gs j) = 0 := by
    intro i j
    rcases hsel with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 h2
    · exact S.iso i j
    · exact S.iso' i j
  have hg : ∀ i, g i.castSucc = algebraMap F E ((a i)⁻¹ : Fˣ) • X i := by
    intro i; rw [← hX i, smul_smul, alg_inv_mul, one_smul]
  have hY' : ∀ i, Y i = algebraMap F E ((a i)⁻¹ : Fˣ) • gs i := by
    intro i; rw [hY i, smul_smul, alg_inv_mul, one_smul]
  refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_, fun n => ?_⟩
  · simp only [Frames.h]
    rw [← hX i, hY' j, Eichler.hf_smul_l, Eichler.hf_smul_r, cj_alg, hgs]
    split_ifs with h
    · subst h; rw [mul_one, alg_mul_inv]
    · simp
  · simp only [Frames.h]
    rw [← hX i, ← hX j, Eichler.hf_smul_l, Eichler.hf_smul_r, hgg]; simp
  · simp only [Frames.h]
    rw [hY' i, hY' j, Eichler.hf_smul_l, Eichler.hf_smul_r, hss]; simp
  rw [GlobalTheory.T.mem_flagUnipotent_iff_orderedEichlerProduct L r k S g gs hsel n]
  constructor
  · rintro ⟨u, s, e, he, hn⟩
    refine ⟨fun i => algebraMap F E ((a i)⁻¹ : Fˣ) • u i,
      fun i => algebraMap F E ((a i)⁻¹ : Fˣ) ^ 2 * s i, e, fun i => ?_, hn⟩
    obtain ⟨ho, hs, hev⟩ := he i
    refine ⟨fun j hj => ?_, ?_, fun v => ?_⟩
    · obtain ⟨h1, h2⟩ := ho j hj
      simp only [Frames.h] at h1 h2 ⊢
      constructor
      · rw [← hX j, Eichler.hf_smul_l, Eichler.hf_smul_r, h1]; simp
      · rw [hY' j, Eichler.hf_smul_l, Eichler.hf_smul_r, h2]; simp
    · simp only [Frames.h] at hs ⊢
      rw [map_mul, map_pow, cj_alg, Eichler.hf_smul_l, Eichler.hf_smul_r, cj_alg, ← hs]; ring
    · rw [hev v, hg i, eich_smul_base L _ _ (cj_alg L _)]
  · rintro ⟨u, s, e, he, hn⟩
    refine ⟨fun i => algebraMap F E (a i : F) • u i,
      fun i => algebraMap F E (a i : F) ^ 2 * s i, e, fun i => ?_, hn⟩
    obtain ⟨ho, hs, hev⟩ := he i
    refine ⟨fun j hj => ?_, ?_, fun v => ?_⟩
    · obtain ⟨h1, h2⟩ := ho j hj
      simp only [Frames.h] at h1 h2 ⊢
      constructor
      · rw [hg j, Eichler.hf_smul_l, Eichler.hf_smul_r, h1]; simp
      · rw [hY j, Eichler.hf_smul_l, Eichler.hf_smul_r, h2]; simp
    · simp only [Frames.h] at hs ⊢
      rw [map_mul, map_pow, cj_alg, Eichler.hf_smul_l, Eichler.hf_smul_r, cj_alg, ← hs]; ring
    · rw [hev v, hg i, eich_smul_base L _ _ (cj_alg L _), smul_smul, ← mul_assoc, ← mul_pow,
        alg_inv_mul, one_pow, one_mul, one_smul]
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.GamInv

theorem hf_add_right {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) {n : ℕ}
    (H : Matrix (Fin n) (Fin n) E) (x y z : Fin n → E) :
    hf L H x (y + z) = hf L H x y + hf L H x z := by
  simp [hf, mul_add, Finset.sum_add_distrib]

theorem hf_smul_right {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) {n : ℕ}
    (H : Matrix (Fin n) (Fin n) E) (x z : Fin n → E) (c : E) :
    hf L H x (c • z) = L.cj c * hf L H x z := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem main : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig) (r k : ℕ) (G : GFrames A r k), (Matrix.of fun k l : Fin (r + 1) ⊕ Fin (r + 1) => ∑ i, ∑ j, Sum.elim G.f G.f' k i * G.Hm i j * sig (Sum.elim G.f G.f' l j))⁻¹ * (Matrix.of fun k l : Fin (r + 1) ⊕ Fin (r + 1) => ∑ i, ∑ j, Sum.elim G.f G.f' k i * G.Hm i j * sig (Sum.elim G.f G.f' l j)) = 1 := by
  intro F E _ _ _ _ _ sig A r k G
  classical
  set g : Fin (r + 1) ⊕ Fin (r + 1) → Fin (k + 2 * r + 1) → E := Sum.elim G.f G.f' with hg
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 F)
  let p : HeightOneSpectrum (𝓞 F) :=
    ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField F)⟩
  obtain ⟨hinj, -, -, -, hform, hind⟩ := GlobalTheory.HL.RatExt.rational_extend A (k + 2 * r + 1) p
  haveI := (A.loc p).lf
  haveI := (A.loc p).char0
  obtain ⟨hli, hco, -⟩ := GlobalTheory.FrameBasic.main (A.L p) r k (G.S p)
  set S := G.S p with hS
  set Ep := (A.loc p).Ep
  let s : Fin (r + 1) ⊕ Fin (r + 1) → Epˣ := fun q =>
    Units.map (algebraMap (A.loc p).Fp Ep).toMonoidHom (G.c p ^ (r - (Sum.elim (fun a : Fin (r + 1) => (a : ℕ)) (fun a => (a : ℕ)) q)))
  have hu : ∀ q, A.bc p (g q) = ((s q : Epˣ) : Ep) • Sum.elim S.f S.f' q := by
    intro q
    rcases q with a | a
    · simp only [hg, Sum.elim_inl, s, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.val_pow_eq_pow_val]
      exact (G.f_eq p a).symm
    · simp only [hg, Sum.elim_inr, s, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.val_pow_eq_pow_val]
      exact (G.f'_eq p a).symm
  have hgli : LinearIndependent E g := by
    let e := (finSumFinEquiv (m := r + 1) (n := r + 1))
    refine (linearIndependent_equiv e.symm).1 ((hind _ (g ∘ e.symm)).2 ?_)
    have : (fun q => A.bc p (g q)) = s • Sum.elim S.f S.f' := by
      funext q; rw [hu]; rfl
    have h2 : LinearIndependent Ep (fun q => A.bc p (g q)) := by
      rw [this]; exact hli.units_smul s
    exact (linearIndependent_equiv e.symm).2 h2
  have hME : S.ME = Submodule.span Ep (Set.range (Sum.elim S.f S.f')) := by
    have h1 : ∀ v : Fin (r + 1) → S.V, S.spanTo v (r + 1) = Submodule.span Ep (Set.range v) := by
      intro v
      unfold Frames.spanTo
      congr 1
      ext y
      simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_range]
      exact ⟨fun ⟨a, _, h⟩ => ⟨a, h⟩, fun ⟨a, h⟩ => ⟨a, a.isLt, h⟩⟩
    rw [Frames.ME, h1, h1, Set.Sum.elim_range, Submodule.span_union]
  set Γ : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) E :=
    Matrix.of fun k l => ∑ i, ∑ j, g k i * G.Hm i j * sig (g l j) with hΓ
  have key : ∀ v : Fin (r + 1) ⊕ Fin (r + 1) → E, Matrix.vecMul v Γ = 0 → v = 0 := by
    intro v hv
    set x : Fin (k + 2 * r + 1) → E := ∑ q, v q • g q with hx
    have hx0 : ∀ l, ∑ i, ∑ j, x i * G.Hm i j * sig (g l j) = 0 := by
      intro l
      have h : Matrix.vecMul v Γ l = 0 := congrFun hv l
      rw [← h]
      simp only [Matrix.vecMul, dotProduct, hΓ, Matrix.of_apply, hx, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, Finset.sum_mul, Finset.mul_sum, Pi.zero_apply]
      symm
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun q _ => by ring
    have hloc : ∀ q, hf (A.L p) S.Hm (A.bc p x) (A.bc p (g q)) = 0 := by
      intro q
      rw [G.Hm_eq p, hform, hx0, map_zero]
    have hbcx : A.bc p x = ∑ q, (A.loc p).ιE (v q) • A.bc p (g q) := by
      funext i

      simp [Places.bc, hx, Finset.sum_apply, map_sum]
    have hmem : A.bc p x ∈ S.ME := by
      rw [hbcx, hME]
      refine Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ ?_
      rw [hu]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)
    have hperp : A.bc p x ∈ S.W0 := by
      show ∀ y ∈ S.ME, hf (A.L p) S.Hm (A.bc p x) y = 0
      intro y hy
      rw [hME] at hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨q, rfl⟩ := hy
        have e1 : Sum.elim S.f S.f' q = ((s q)⁻¹ : Epˣ) • A.bc p (g q) := by
          rw [hu, ← Units.smul_def, inv_smul_smul]
        rw [e1, Units.smul_def, hf_smul_right, hloc q, mul_zero]
      | zero => simp [hf]
      | add y z _ _ hy hz => rw [hf_add_right, hy, hz, add_zero]
      | smul c y _ hy => rw [hf_smul_right, hy, mul_zero]
    have hbot : A.bc p x = 0 := by
      have h : A.bc p x ∈ S.ME ⊓ S.W0 := ⟨hmem, hperp⟩
      rw [hco.inf_eq_bot] at h
      exact (Submodule.mem_bot _).1 h
    have hx00 : x = 0 := hinj (by rw [hbot]; funext i; simp [Places.bc])
    funext q
    exact Fintype.linearIndependent_iff.1 hgli v (by rw [← hx]; exact hx00) q
  have hU : IsUnit Γ := Matrix.vecMul_injective_iff_isUnit.1 fun a b h =>
    sub_eq_zero.1 (key _ (by rw [Matrix.sub_vecMul]; exact sub_eq_zero.2 h))
  exact Matrix.nonsing_inv_mul Γ ((Matrix.isUnit_iff_isUnit_det Γ).1 hU)

end GlobalTheory.HL.GamInv
end
