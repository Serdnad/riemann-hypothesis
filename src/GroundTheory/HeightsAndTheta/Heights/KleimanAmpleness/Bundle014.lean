module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CoordIdealIsMultiProjPrime
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Objects
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.EqZeroOrIsHomogeneousOfMemPolyPiece
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTildeTailCone
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Statements
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq

open MvPolynomial

noncomputable section

variable {S : Type} [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω] {x : Fin (N + 1) → Ω}

theorem div_mem_chartRing_of_mem (I : Kleiman.Chart x) {i : Fin (N + 1)} (hi : i ∈ I.1)
    (j : Fin (N + 1)) : x j / x i ∈ Kleiman.chartRing S x I :=
  ⟨X j, X i, 1, Kleiman.X_mem_monos hi, isHomogeneous_X S j, isHomogeneous_X S i, by simp⟩

section First

variable (Q : Kleiman.LineBundle S x)

end First

section Second

variable (Q' : IndefiniteRowSideFullHecke.Kleiman.LineBundle (S := S) x)

def latSub {i : Fin (N + 1)} (h : x i ≠ 0) :
    Submodule (Kleiman.chartRing S x (Kleiman.singleChart h)) Ω where
  carrier := Q'.lat i
  add_mem' := add_mem
  zero_mem' := zero_mem _
  smul_mem' a e he := Q'.stable i a (by rw [chartRing.equiv S x h]; exact a.2) e he

theorem coe_latSub {i : Fin (N + 1)} (h : x i ≠ 0) : (latSub Q' h : Set Ω) = (Q'.lat i : Set Ω) := rfl

def subOf (I : Kleiman.Chart x) : Submodule (Kleiman.chartRing S x I) Ω :=
  Submodule.span _ (⋃ i ∈ I.1, (Q'.lat i : Set Ω))

theorem subOf_eq {I : Kleiman.Chart x} {i : Fin (N + 1)} (hi : i ∈ I.1) :
    subOf Q' I = Submodule.span _ (Q'.lat i : Set Ω) := by
  have hxi : x i ≠ 0 := (Kleiman.mem_support x).1 (I.2.2 hi)
  apply le_antisymm
  · rw [subOf, Submodule.span_le]
    intro e he
    obtain ⟨j, hj, he⟩ := Set.mem_iUnion₂.1 he
    have hxj : x j ≠ 0 := (Kleiman.mem_support x).1 (I.2.2 hj)
    obtain ⟨m, hm⟩ := Q'.overlap j i hxj hxi e he
    have hr : (x i / x j) ^ m ∈ Kleiman.chartRing S x I := pow_mem (div_mem_chartRing_of_mem I hj i) m
    have hc : x i / x j * (x j / x i) = 1 := by field_simp
    have key : e = (⟨_, hr⟩ : Kleiman.chartRing S x I) • ((x j / x i) ^ m • e) := by
      rw [Subalgebra.smul_def, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← mul_pow, hc, one_pow, one_mul]
    rw [key]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hm)
  · exact Submodule.span_mono fun e he => Set.mem_iUnion₂.2 ⟨i, hi, he⟩

theorem subOf_mono (I J : Kleiman.Chart x) (h : I.1 ⊆ J.1) (y : Ω) (hy : y ∈ subOf Q' I) :
    y ∈ subOf Q' J := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨i, hi, hz⟩ := Set.mem_iUnion₂.1 hz
    exact Submodule.subset_span (Set.mem_iUnion₂.2 ⟨i, h hi, hz⟩)
  | zero => exact zero_mem _
  | add u v _ _ hu hv => exact add_mem hu hv
  | smul a z _ hz => exact Submodule.smul_mem _ (Kleiman.chartIncl h a) hz

theorem subOf_mem_iff (I J : Kleiman.Chart x) (h : I.1 ⊆ J.1) (y : Ω) :
    y ∈ subOf Q' J ↔
      ∃ a : Kleiman.chartRing S x I, IsUnit (Kleiman.chartIncl h a) ∧ (a : Ω) • y ∈ subOf Q' I := by
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (Kleiman.mem_support x).1 (I.2.2 hi)
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨j, hj, hz⟩ := Set.mem_iUnion₂.1 hz
      have hxj : x j ≠ 0 := (Kleiman.mem_support x).1 (J.2.2 hj)
      obtain ⟨m, hm⟩ := Q'.overlap j i hxj hxi z hz
      refine ⟨⟨(x j / x i) ^ m, pow_mem (div_mem_chartRing_of_mem I hi j) m⟩, ?_, ?_⟩
      · rw [isUnit_iff_exists_inv]
        refine ⟨⟨(x i / x j) ^ m, pow_mem (div_mem_chartRing_of_mem J hj i) m⟩, Subtype.ext ?_⟩
        change (x j / x i) ^ m * (x i / x j) ^ m = 1
        have hc : x j / x i * (x i / x j) = 1 := by field_simp
        rw [← mul_pow, hc, one_pow]
      · rw [subOf_eq Q' hi]
        exact Submodule.subset_span hm
    | zero => exact ⟨1, by simp, by rw [smul_zero]; exact zero_mem _⟩
    | add u v _ _ hu hv =>
      obtain ⟨a, ha, hau⟩ := hu
      obtain ⟨b, hb, hbv⟩ := hv
      refine ⟨a * b, by rw [map_mul]; exact ha.mul hb, ?_⟩
      have : ((a * b : Kleiman.chartRing S x I) : Ω) • (u + v) = b • ((a : Ω) • u) + a • ((b : Ω) • v) := by
        simp only [Subalgebra.coe_mul, Subalgebra.smul_def, smul_eq_mul]
        ring
      rw [this]
      exact add_mem (Submodule.smul_mem _ b hau) (Submodule.smul_mem _ a hbv)
    | smul c z _ hz =>
      obtain ⟨a, ha, haz⟩ := hz
      obtain ⟨a', ha', hc⟩ := Kleiman.exists_isUnit_mul_mem h c
      refine ⟨a' * a, by rw [map_mul]; exact ha'.mul ha, ?_⟩
      have : ((a' * a : Kleiman.chartRing S x I) : Ω) • (c • z) =
          (⟨(a' : Ω) * c, hc⟩ : Kleiman.chartRing S x I) • ((a : Ω) • z) := by
        simp only [Subalgebra.coe_mul, Subalgebra.smul_def, smul_eq_mul]
        ring
      rw [this]
      exact Submodule.smul_mem _ _ haz
  · rintro ⟨a, ⟨u, hu⟩, hay⟩
    have hay' := subOf_mono Q' I J h _ hay
    have hinv : ((↑u⁻¹ : Kleiman.chartRing S x J) : Ω) * (a : Ω) = 1 := by
      have := congrArg Subtype.val (Units.inv_mul u)
      rw [hu] at this
      exact this
    have hy' : y = (↑u⁻¹ : Kleiman.chartRing S x J) • ((a : Ω) • y) := by
      rw [Subalgebra.smul_def, ← mul_smul, hinv, one_smul]
    rw [hy']
    exact Submodule.smul_mem _ _ hay'

theorem latSub_fg_invertible {i : Fin (N + 1)} (h : x i ≠ 0) :
    (latSub Q' h).FG ∧ ∃ L' : Submodule (Kleiman.chartRing S x (Kleiman.singleChart h)) Ω,
      latSub Q' h * L' = 1 := by
  obtain ⟨k, f, c, hf, hc, hs, hb⟩ := Q'.frame i h
  have hA : ReciprocityTheory.ChartRestriction.G.Geo.chartRing S x i = Kleiman.chartRing S x (Kleiman.singleChart h) :=
    chartRing.equiv S x h
  simp only [hA] at hf hc hb
  choose b hbli _ hiff using hb
  refine fg_and_invertible_of_frame _ f c (latSub Q' h) (fun l => b l 0) hf hc hs
    (fun l => linearIndependent_unique_iff.1 (hbli l)) (fun l e => ?_)
  have := hiff l e
  simp only [Fin.sum_univ_one, smul_eq_mul] at this
  constructor
  · intro hn
    obtain ⟨a, ha, he⟩ := this.1 hn
    exact ⟨a 0, ha 0, he⟩
  · rintro ⟨a, ha, he⟩
    exact this.2 ⟨fun _ => a, fun _ => ha, he⟩

theorem subOf_fg (I : Kleiman.Chart x) : (subOf Q' I).FG := by
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (Kleiman.mem_support x).1 (I.2.2 hi)
  have hle : Kleiman.chartRing S x (Kleiman.singleChart hxi) ≤ Kleiman.chartRing S x I :=
    Kleiman.chartRing_mono (I := Kleiman.singleChart hxi) (J := I) (Finset.singleton_subset_iff.2 hi)
  rw [subOf_eq Q' hi]
  exact fg_span_of_le hle (latSub_fg_invertible Q' hxi).1

theorem subOf_invertible (I : Kleiman.Chart x) :
    ∃ L' : Submodule (Kleiman.chartRing S x I) Ω, subOf Q' I * L' = 1 := by
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (Kleiman.mem_support x).1 (I.2.2 hi)
  have hle : Kleiman.chartRing S x (Kleiman.singleChart hxi) ≤ Kleiman.chartRing S x I :=
    Kleiman.chartRing_mono (I := Kleiman.singleChart hxi) (J := I) (Finset.singleton_subset_iff.2 hi)
  obtain ⟨L', hL'⟩ := (latSub_fg_invertible Q' hxi).2
  have key := mul_span_eq_one_of_le (B := Kleiman.chartRing S x I) hle hL'
  rw [coe_latSub] at key
  refine ⟨Submodule.span (Kleiman.chartRing S x I) (L' : Set Ω), ?_⟩
  rw [subOf_eq Q' hi]
  exact key

def ofSecond : Kleiman.LineBundle S x where
  sub := subOf Q'
  mono := subOf_mono Q'
  mem_iff := subOf_mem_iff Q'
  fg I := subOf_fg Q' I
  invertible I := subOf_invertible Q' I

end Second

end

end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section Loc

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem aeval_ne_zero_of_mem_monos_support {I : Finset (Fin (N + 1))} (hI : I ⊆ support x)
    {s : Poly S N} (hs : s ∈ monos I) : aeval x s ≠ 0 := by
  induction hs using Submonoid.closure_induction with
  | mem a ha =>
    obtain ⟨i, hi, rfl⟩ := ha
    rw [aeval_X]
    exact (mem_support x).mp (hI hi)
  | one => simp
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_ne_zero ha hb

theorem isUnit_coneLaurent_of_mem_monos {I : Finset (Fin (N + 1))} (hI : I ⊆ support x)
    {s : Poly S N} (hs : s ∈ monos I) : IsUnit (coneLaurent S x s) := by
  obtain ⟨e, he⟩ := monos_isHomogeneous hs
  rw [coneLaurent_of_isHomogeneous he]
  exact isUnit_coneSingle (S := S) (x := x) e (aeval_ne_zero_of_mem_monos_support hI hs)

variable (M : FinGradedSub (S := S) (x := x) Ω)

def locCone (I : Finset (Fin (N + 1))) (hI : I ⊆ support x) :
    LocMod S N M.coneSub I →ₗ[Poly S N] ConeLaurent S x :=
  LocalizedModule.lift (monos I) M.coneSub.subtype fun s => by
    rw [Module.End.isUnit_iff]
    exact IsUnit.isUnit_iff_mulLeft_bijective.mp (isUnit_coneLaurent_of_mem_monos hI s.2)

theorem locCone_mk (I : Finset (Fin (N + 1))) (hI : I ⊆ support x) (m : M.coneSub)
    (s : monos (S := S) I) :
    coneLaurent S x s * locCone M I hI (LocalizedModule.mk m s) = m := by
  have h1 : (s : Poly S N) • (LocalizedModule.mk m s : LocalizedModule (monos (S := S) I) M.coneSub) =
      LocalizedModule.mk m 1 := by
    rw [LocalizedModule.smul'_mk]
    exact LocalizedModule.mk_cancel s m
  have h2 : locCone M I hI ((s : Poly S N) • LocalizedModule.mk m s) = m := by
    change LocalizedModule.lift (monos I) M.coneSub.subtype _
      ((s : Poly S N) • (LocalizedModule.mk m s : LocalizedModule (monos (S := S) I) M.coneSub)) = m
    rw [h1]
    simp
  have h3 := (locCone M I hI).map_smul (s : Poly S N) (LocalizedModule.mk m s : LocMod S N M.coneSub I)
  exact h3.symm.trans h2

theorem locCone_mk_eq {I : Finset (Fin (N + 1))} (hI : I ⊆ support x) {m : M.coneSub}
    {s : monos (S := S) I} {w : ConeLaurent S x} (h : coneLaurent S x s * w = m) :
    locCone M I hI (LocalizedModule.mk m s) = w :=
  (isUnit_coneLaurent_of_mem_monos hI s.2).mul_left_cancel ((locCone_mk M I hI m s).trans h.symm)

theorem locCone_injective (I : Finset (Fin (N + 1))) (hI : I ⊆ support x) :
    Function.Injective (locCone M I hI) := by
  refine (injective_iff_map_eq_zero _).mpr fun z => ?_
  refine LocalizedModule.induction_on
    (β := fun z : LocalizedModule (monos (S := S) I) M.coneSub => locCone M I hI z = 0 → z = 0)
    (fun m s hz => ?_) z
  have h := locCone_mk M I hI m s
  rw [hz, mul_zero] at h
  have hm : m = 0 := Subtype.ext h.symm
  rw [hm, LocalizedModule.zero_mk]

theorem locCone_locRes {I J : Finset (Fin (N + 1))} (h : I ⊆ J) (hJ : J ⊆ support x)
    (z : LocMod S N M.coneSub I) :
    locCone M J hJ (locRes h z) = locCone M I (h.trans hJ) z := by
  refine LocalizedModule.induction_on
    (β := fun z : LocalizedModule (monos (S := S) I) M.coneSub =>
      locCone M J hJ (locRes h z) = locCone M I (h.trans hJ) z) (fun m s => ?_) z
  rw [locRes_mk]
  exact locCone_mk_eq M hJ (locCone_mk M I _ m s)

theorem locMod_subsingleton {I : Finset (Fin (N + 1))} {i : Fin (N + 1)} (hi : i ∈ I) (hx : x i = 0) :
    Subsingleton (LocMod S N M.coneSub I) := by
  have hX : ∀ m : M.coneSub, (X i : Poly S N) • m = 0 := fun m => by
    apply Subtype.ext
    change coneLaurent S x (X i) * (m : ConeLaurent S x) = 0
    rw [coneLaurent_of_isHomogeneous (isHomogeneous_X S i), aeval_X, hx, AddMonoidAlgebra.single_zero,
      map_zero, zero_mul]
  refine subsingleton_of_forall_eq 0 fun z => ?_
  refine LocalizedModule.induction_on
    (β := fun z : LocalizedModule (monos (S := S) I) M.coneSub => z = 0) (fun m s => ?_) z
  rw [← LocalizedModule.mk_cancel_common_left ⟨X i, X_mem_monos hi⟩ s m]
  have h0 : (⟨X i, X_mem_monos hi⟩ : monos (S := S) I) • m = 0 := hX m
  rw [h0, LocalizedModule.zero_mk]

theorem locCone_degLoc (c : ℤ) (I : StdCell N) (hI : I.1 ⊆ support x) {z : LocMod S N M.coneSub I.1}
    (hz : z ∈ degLoc M.coneGraded c I) :
    ∃ v ∈ M.tilde c ⟨I.1, I.2.1, hI⟩, locCone M I.1 hI z = coneSingle S x c v := by
  refine Submodule.span_induction (p := fun z _ => ∃ v ∈ M.tilde c ⟨I.1, I.2.1, hI⟩,
    locCone M I.1 hI z = coneSingle S x c v) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨m, s, a, e, hm, hse, hae, rfl⟩
    have hs0 := aeval_ne_zero_of_mem_monos_support hI s.2
    refine ⟨(aeval x (s : Poly S N))⁻¹ • coeffAt S x a (m : ConeLaurent S x),
      Submodule.subset_span ⟨coeffAt S x a m, s, a, e, s.2, hse, m.2 a, hae, rfl⟩, locCone_mk_eq M hI ?_⟩
    rw [← coneLaurent_smul, smul_coneSingle hse, smul_eq_mul, mul_inv_cancel_left₀ hs0,
      show c + (e : ℤ) = a by omega]
    exact (M.eq_coneSingle_of_mem_conePiece hm).symm
  · exact ⟨0, zero_mem _, by rw [map_zero, map_zero]⟩
  · rintro _ _ _ _ ⟨v, hv, hzv⟩ ⟨v', hv', hzv'⟩
    exact ⟨v + v', add_mem hv hv', by rw [map_add (f := _), map_add (f := _), hzv, hzv']⟩
  · rintro s _ _ ⟨v, hv, hzv⟩
    exact ⟨s • v, (M.tilde c _).smul_of_tower_mem s hv, by rw [LinearMap.map_smul_of_tower, hzv, map_smul]⟩

def tildeGens (c : ℤ) (I : Chart x) : Set Ω :=
  {y | ∃ (m : Ω) (s : Poly S N) (a : ℤ) (e : ℕ), s ∈ monos I.1 ∧ s.IsHomogeneous e ∧ m ∈ M.piece a ∧
    a - e = c ∧ y = (aeval x s)⁻¹ • m}

theorem tilde_le_span (c : ℤ) (I : Chart x) :
    (M.tilde c I : Set Ω) ⊆ Submodule.span S (tildeGens M c I) := by
  have hclosed : ∀ a : chartRing S x I, ∀ y ∈ Submodule.span S (tildeGens M c I),
      a • y ∈ Submodule.span S (tildeGens M c I) := by
    intro a y hy
    refine Submodule.span_induction (p := fun y _ => a • y ∈ Submodule.span S (tildeGens M c I))
      ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨m, s, b, e, hs, hse, hm, hbe, rfl⟩
      obtain ⟨f, s', e', hs', hf, hse', ha⟩ := a.2
      refine Submodule.subset_span ⟨aeval x f • m, s' * s, b + e', e' + e, mul_mem hs' hs, hse'.mul hse,
        M.smul_mem e' b f m hf hm, by push_cast; omega, ?_⟩
      simp only [chartRing_smul_def, smul_eq_mul, ha, map_mul, mul_inv, div_eq_mul_inv]
      ring
    · rw [smul_zero]; exact zero_mem _
    · intro y y' _ _ hy hy'; rw [smul_add]; exact add_mem hy hy'
    · intro t y _ hy
      have : a • (t • y) = t • (a • y) := by
        rw [chartRing_smul_def, chartRing_smul_def, Algebra.smul_def, Algebra.smul_def]; ring
      rw [this]; exact Submodule.smul_mem _ t hy
  intro y hy
  exact Submodule.span_induction (p := fun y _ => y ∈ Submodule.span S (tildeGens M c I))
    (fun y hy => Submodule.subset_span hy) (zero_mem _) (fun _ _ _ _ => add_mem)
    (fun a y _ hy => hclosed a y hy) hy

theorem exists_locCone_eq (c : ℤ) (I : StdCell N) (hI : I.1 ⊆ support x) {y : Ω}
    (hy : y ∈ M.tilde c ⟨I.1, I.2.1, hI⟩) :
    ∃ z ∈ degLoc M.coneGraded c I, locCone M I.1 hI z = coneSingle S x c y := by
  refine Submodule.span_induction (p := fun y _ => ∃ z ∈ degLoc M.coneGraded c I,
    locCone M I.1 hI z = coneSingle S x c y) ?_ ?_ ?_ ?_ (tilde_le_span M c _ hy)
  · rintro _ ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩
    refine ⟨LocalizedModule.mk ⟨coneSingle S x a m, M.coneSingle_mem_coneSub hm⟩ ⟨s, hs⟩,
      Submodule.subset_span ⟨_, ⟨s, hs⟩, a, e, M.coneSingle_mem_conePiece hm, hse, hae, rfl⟩,
      locCone_mk_eq M hI ?_⟩
    have hs0 := aeval_ne_zero_of_mem_monos_support hI hs
    change s • coneSingle S x c ((aeval x s)⁻¹ • m) = coneSingle S x a m
    rw [smul_coneSingle hse, smul_eq_mul, mul_inv_cancel_left₀ hs0, show c + (e : ℤ) = a by omega]
  · exact ⟨0, zero_mem _, by rw [map_zero, map_zero]⟩
  · rintro _ _ _ _ ⟨z, hz, hzy⟩ ⟨z', hz', hzy'⟩
    exact ⟨z + z', add_mem hz hz', by rw [map_add (f := _), map_add (f := _), hzy, hzy']⟩
  · rintro t _ _ ⟨z, hz, hzy⟩
    exact ⟨t • z, Submodule.smul_mem _ t hz, by rw [LinearMap.map_smul_of_tower, hzy, map_smul]⟩

end Loc

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

theorem Generated.proof (hE : Extension.Statement.{u, w, w}) : Generated.Statement.{u, w} := by
  intro S _ _ Ω _ _ N x Q
  obtain ⟨M, hMgam, hMtilde⟩ := hE S Ω N x Ω Q.toSubFamily Q.fg
  obtain ⟨n, deg, gen, hgen, hM⟩ := M.fg
  refine ⟨∑ j, |deg j|, fun c hc I => le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le]
    intro z hz
    exact (Submodule.mem_iInf _).mp hz I
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  set T := Submodule.span (chartRing S x I) ((Q.twist (twistSys S x c)).secs : Set Ω) with hT

  have hgenT : ∀ (j : Fin n) (f s : Poly S N) (e e' : ℕ), s ∈ monos I.1 → f.IsHomogeneous e' →
      s.IsHomogeneous e → (e' : ℤ) + deg j = e →
      x i ^ c * ((aeval x s)⁻¹ * (aeval x f * gen j)) ∈ T := by
    intro j f s e e' hs hf hse hee
    have hd : deg j ≤ c := (le_abs_self (deg j)).trans
      ((Finset.single_le_sum (fun j _ => abs_nonneg (deg j)) (Finset.mem_univ j)).trans hc)
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = c - deg j := ⟨(c - deg j).toNat, Int.toNat_of_nonneg (by omega)⟩
    have hsec : x i ^ k * gen j ∈ (Q.twist (twistSys S x c)).secs := by
      have h1 := M.smul_mem k (deg j) (X i ^ k) (gen j) (isHomogeneous_X_pow i k) (hgen j)
      have h2 : deg j + (k : ℤ) = c := by omega
      rw [h2] at h1
      have h3 := hMgam c h1
      rwa [map_pow, aeval_X, smul_eq_mul] at h3
    have hα : aeval x f / aeval x s ∈ twistMod S x (-deg j) I :=
      Submodule.subset_span ⟨f, s, e, e', hs, hf, hse, by omega, rfl⟩
    rw [twistMod_eq_span (-deg j) I hi, Submodule.mem_span_singleton] at hα
    obtain ⟨b, hb⟩ := hα
    rw [chartRing_smul_def] at hb
    have e1 : x i ^ c * x i ^ (-deg j) = x i ^ k := by
      rw [← zpow_add₀ hxi, ← zpow_natCast, hk]
      congr 1
    have e2 : x i ^ c * ((aeval x s)⁻¹ * (aeval x f * gen j)) = b • (x i ^ k * gen j) := by
      rw [chartRing_smul_def, ← e1]
      calc x i ^ c * ((aeval x s)⁻¹ * (aeval x f * gen j))
          = x i ^ c * (aeval x f / aeval x s) * gen j := by ring
        _ = x i ^ c * ((b : Ω) * x i ^ (-deg j)) * gen j := by rw [hb]
        _ = (b : Ω) * (x i ^ c * x i ^ (-deg j) * gen j) := by ring
    rw [e2]
    exact T.smul_mem b (Submodule.subset_span hsec)

  have key : ∀ y ∈ M.tilde 0 I, x i ^ c * y ∈ T := by
    intro y hy
    refine Submodule.span_induction (p := fun y _ => x i ^ c * y ∈ T) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩
      refine Submodule.span_induction
        (p := fun m _ => x i ^ c * ((aeval x s)⁻¹ • m) ∈ T) ?_ ?_ ?_ ?_ (hM a hm)
      · rintro _ ⟨j, f, e', hf, hee, rfl⟩
        rw [smul_eq_mul, smul_eq_mul]
        exact hgenT j f s e e' hs hf hse (by omega)
      · rw [smul_zero, mul_zero]; exact T.zero_mem
      · intro m m' _ _ h h'
        rw [smul_add, mul_add]; exact T.add_mem h h'
      · intro r m _ h
        have : x i ^ c * ((aeval x s)⁻¹ • (r • m)) =
            (algebraMap S (chartRing S x I) r) • (x i ^ c * ((aeval x s)⁻¹ • m)) := by
          rw [chartRing_smul_def]
          simp only [smul_eq_mul, Algebra.smul_def]
          change _ = algebraMap S Ω r * _
          ring
        rw [this]; exact T.smul_mem _ h
    · rw [mul_zero]; exact T.zero_mem
    · intro y y' _ _ h h'
      rw [mul_add]; exact T.add_mem h h'
    · intro b y _ h
      have : x i ^ c * (b • y) = b • (x i ^ c * y) := by
        rw [chartRing_smul_def, chartRing_smul_def]; ring
      rw [this]; exact T.smul_mem b h
  change Submodule.span _ _ ≤ T
  rw [Submodule.span_le]
  rintro _ ⟨q, hq, y, hy, rfl⟩
  change q ∈ twistMod S x c I at hq
  rw [twistMod_eq_span c I hi, Submodule.mem_span_singleton] at hq
  obtain ⟨a, rfl⟩ := hq
  have hy' : y ∈ M.tilde 0 I := by rw [hMtilde I]; exact hy
  have : (a • x i ^ c) • y = a • (x i ^ c * y) := by
    rw [smul_eq_mul, chartRing_smul_def, chartRing_smul_def, mul_assoc]
  rw [SetLike.mem_coe, this]
  exact T.smul_mem a (key y hy')

end

end GroundTheory.Heights₂.Heights.Kleiman
end
