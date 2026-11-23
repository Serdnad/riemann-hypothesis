module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle088
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle041
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle037
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle035
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsEqTransposeMulMapOfIdempotent
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle025
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthonormalBasisAndOneOrbit
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle021
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle035

@[expose] public section

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem coset_fibre_card {G : Type} [Group G] (D H : Subgroup G) (h : D ≤ H) (hDH : D.relIndex H ≠ 0)
    (z : G ⧸ H) : Finite {y : G ⧸ D // Subgroup.quotientMapOfLE h y = z} ∧
      Nat.card {y : G ⧸ D // Subgroup.quotientMapOfLE h y = z} = D.relIndex H := by
  apply GlobalTheory.FibreEquivalence.fibre_finite_card <;> assumption

theorem mass_orbit_eq : ∀ {G : Type} [Group G] (Γ K0 : Subgroup G), ∃ V₀ : ℝ≥0∞, ∀ (X : Type) [MulAction G X] (x : X), K0.relIndex (MulAction.stabilizer G x) ≠ 0 → (MulAction.stabilizer G x).relIndex K0 ≠ 0 → (∑' o : MulAction.orbitRel.Quotient Γ X, if o.out ∈ MulAction.orbit G x then ((((Γ ⊓ MulAction.stabilizer G o.out : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹ else 0) = V₀ * ENNReal.ofReal (invVol K0 (MulAction.stabilizer G x)) := by
  intro G _ Γ K0
  let M : Subgroup G → ℝ≥0∞ := fun U => ∑' o : MulAction.orbitRel.Quotient Γ (G ⧸ U),
    ((((Γ ⊓ MulAction.stabilizer G o.out : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹
  have hq : ∀ (D H : Subgroup G) (h : D ≤ H), D.relIndex H ≠ 0 → M D = (D.relIndex H : ℝ≥0∞) * M H := by
    intro D H h hDH
    have e := GlobalTheory.T.orbit_mass_equivariant_constant_fibre Γ (G ⧸ D) (G ⧸ H) (Subgroup.quotientMapOfLE h) Set.univ (D.relIndex H) ?_
      (fun _ _ _ => trivial) (fun z _ => coset_fibre_card D H h hDH z) (fun z hz => absurd trivial hz)
    · simp only [Set.mem_univ, ite_true] at e
      exact e
    · intro g y
      induction y using QuotientGroup.induction_on with
      | H a => rfl
  refine ⟨M K0, fun X _ x h1 h2 => ?_⟩
  have hX : (∑' o : MulAction.orbitRel.Quotient Γ X, if o.out ∈ MulAction.orbit G x then
      ((((Γ ⊓ MulAction.stabilizer G o.out : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹ else 0) =
      M (MulAction.stabilizer G x) := by
    have e := GlobalTheory.T.orbit_mass_equivariant_constant_fibre Γ (G ⧸ MulAction.stabilizer G x) X (MulAction.ofQuotientStabilizer G x)
      (MulAction.orbit G x) 1 (fun g y => MulAction.ofQuotientStabilizer_smul G x g y)
      (fun g z hz => by obtain ⟨a, rfl⟩ := hz; exact ⟨g * a, mul_smul g a x⟩) ?_ ?_
    · rw [Nat.cast_one, one_mul] at e
      exact e.symm
    · intro z hz
      have hs : Subsingleton {y // MulAction.ofQuotientStabilizer G x y = z} :=
        ⟨fun a b => Subtype.ext (MulAction.injective_ofQuotientStabilizer G x (a.2.trans b.2.symm))⟩
      obtain ⟨a, rfl⟩ := hz
      have hn : Nonempty {y // MulAction.ofQuotientStabilizer G x y = a • x} :=
        ⟨⟨(a : G ⧸ MulAction.stabilizer G x), MulAction.ofQuotientStabilizer_mk G x a⟩⟩
      exact ⟨inferInstance, Nat.card_unique⟩
    · intro z hz
      refine ⟨fun y => hz ?_⟩
      rw [← y.2]
      induction y.1 using QuotientGroup.induction_on with
      | H a => exact ⟨a, (MulAction.ofQuotientStabilizer_mk G x a).symm⟩
  rw [hX]
  set U := MulAction.stabilizer G x
  have ha := hq (U ⊓ K0) U inf_le_left (by rw [Subgroup.inf_relIndex_left]; exact h1)
  have hb := hq (U ⊓ K0) K0 inf_le_right (by rw [Subgroup.inf_relIndex_right]; exact h2)
  rw [Subgroup.inf_relIndex_left] at ha
  rw [Subgroup.inf_relIndex_right] at hb
  rw [ha] at hb
  have hr : ENNReal.ofReal (invVol K0 U) = (U.relIndex K0 : ℝ≥0∞) / (K0.relIndex U : ℝ≥0∞) := by
    rw [invVol, ENNReal.ofReal_div_of_pos (by exact_mod_cast Nat.pos_of_ne_zero h1),
      ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  have hA : (K0.relIndex U : ℝ≥0∞) ≠ 0 := by exact_mod_cast h1
  have hA' : (K0.relIndex U : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [hr, ← mul_div_assoc, ENNReal.eq_div_iff hA hA', mul_comm (M K0), ← hb]

end GlobalTheory.HL
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.FrameOnto
open GlobalTheory.HL.Eichler

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem mem_unipOn {n : ℕ} {A B : Submodule E (Fin n → E)} (hBA : B ≤ A)
    (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) (h1 : ∀ v ∈ A, g v - v ∈ B) (h2 : ∀ v ∈ A, g⁻¹ v - v ∈ B) :
    g ∈ unipOn A B := by
  refine ⟨fun v => ⟨fun hv => ?_, fun hv => ?_⟩, h1⟩
  · have h3 := A.add_mem (hBA (h2 _ hv)) hv
    have h4 : g⁻¹ (g v) = v := g.symm_apply_apply v
    rwa [h4, sub_add_cancel] at h3
  · simpa using A.add_mem (hBA (h1 _ hv)) hv

theorem spanTo_mono (g : Fin (r + 1) → S.V) {a b : ℕ} (h : a ≤ b) : S.spanTo g a ≤ S.spanTo g b :=
  Submodule.span_mono (Set.image_mono fun _ hi => lt_of_lt_of_le hi h)

theorem mem_spanTo (g : Fin (r + 1) → S.V) {i : Fin (r + 1)} {a : ℕ} (h : (i : ℕ) < a) :
    g i ∈ S.spanTo g a := Submodule.subset_span ⟨i, h, rfl⟩

theorem hf_spanTo (g : Fin (r + 1) → S.V) {a : ℕ} {v w : S.V} (hv : v ∈ S.spanTo g a)
    (h : ∀ i : Fin (r + 1), (i : ℕ) < a → hf L S.Hm (g i) w = 0) : hf L S.Hm v w = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx => obtain ⟨i, hi, rfl⟩ := hx; exact h i hi
  | zero => simp [hf]
  | add x y _ _ hx hy => rw [hf_add_l, hx, hy, add_zero]
  | smul c x _ hx => rw [hf_smul_l, hx, mul_zero]

theorem coords (g : Fin (r + 1) → S.V) {a : ℕ} {v : S.V} (hv : v ∈ S.spanTo g a) :
    ∃ c : Fin (r + 1) → E, (∀ i : Fin (r + 1), a ≤ (i : ℕ) → c i = 0) ∧ v = ∑ i, c i • g i := by
  apply GlobalTheory.HL.FrameTri.coeff_of_mem <;> assumption

variable (g : Fin (r + 1) → S.V) (gs : Fin r → S.V) (T : Fˣ)
  (gram : ∀ a b, hf L S.Hm (g a) (g b) =
    if a = Fin.last r ∧ b = Fin.last r then -algebraMap F E T else 0)
  (dual : ∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)

include gram in
theorem mem_perp (j : Fin (r + 1)) : g j ∈ perp L S.Hm (S.spanTo g r) := by
  intro y hy
  rw [← hf_cj L S.herm.1, hf_spanTo S g hy, map_zero]
  intro i hi
  rw [gram, if_neg]
  rintro ⟨rfl, -⟩
  simp at hi

include gram in
theorem spanTo_le_perp : S.spanTo g r ≤ perp L S.Hm (S.spanTo g r) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, -, rfl⟩
  exact mem_perp S g T gram i


include gram in
theorem exists_matrix (n : S.GLV) (hn : n ∈ S.Nof g) :
    ∃ s : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) ∧
      ∀ j, n (g j) = ∑ i, s i j • g i := by
  have key : ∀ j : Fin (r + 1), n (g j) - g j ∈ S.spanTo g j := by
    intro j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · exact hn.2.2 _ (mem_perp S g T gram _)
    · exact (Subgroup.mem_iInf.1 hn.1.2 j).2 _ (mem_spanTo S g (by simp))
  choose c hc hc' using fun j => coords S g (key j)
  refine ⟨fun i j => c j i + if i = j then 1 else 0, ⟨fun i j hij => ?_, fun i => ?_⟩, fun j => ?_⟩
  · simp [hc j i hij.le, hij.ne']
  · simp [hc i i le_rfl]
  · simp [add_smul, Finset.sum_add_distrib, ← hc' j]

include gram dual in
theorem exists_dual (j : Fin (r + 1)) : ∃ u : S.V, ∀ i, hf L S.Hm (g i) u = if i = j then 1 else 0 := by
  refine Fin.lastCases ?_ (fun j => ⟨gs j, fun i => dual i j⟩) j
  refine ⟨algebraMap F E (-(T : F)⁻¹) • g (Fin.last r), fun i => ?_⟩
  rw [hf_smul_r, gram, AlgEquiv.commutes]
  by_cases h : i = Fin.last r
  · simp [h, ← map_mul]
  · simp [h]


include gram dual in
theorem exists_step [IsNonarchimedeanLocalField F] [CharZero F] (j : Fin (r + 1)) (x : S.V)
    (hx : x ∈ S.spanTo g j) :
    ∃ n ∈ S.Nof g, n (g j) = g j + x ∧ (∀ i, i ≠ j → n (g i) = g i) ∧
      ∀ v ∈ S.spanTo g j, n v = v := by
  obtain ⟨u, hu⟩ := exists_dual S g gs T gram dual j
  have hjr : (j : ℕ) ≤ r := Nat.lt_succ_iff.1 j.2
  have hxX : x ∈ S.spanTo g r := spanTo_mono S g hjr hx
  have hlow : ∀ v ∈ S.spanTo g j, hf L S.Hm v u = 0 := fun v hv =>
    hf_spanTo S g hv fun i hi => by
      rw [hu, if_neg]
      rintro rfl
      omega
  have hux : hf L S.Hm u x = 0 := by rw [← hf_cj L S.herm.1, hlow x hx, map_zero]
  have hs : algebraMap F E 2⁻¹ * hf L S.Hm u u + L.cj (algebraMap F E 2⁻¹ * hf L S.Hm u u) =
      hf L S.Hm u u := by
    rw [map_mul, AlgEquiv.commutes, hf_cj L S.herm.1, ← add_mul, ← map_add (f := _)]
    norm_num
  obtain ⟨n, hn, h1, h2⟩ := eichler_isometry L S.Hm S.herm x u _
    (spanTo_le_perp S g T gram hxX x hxX) hux hs
  have e1 : ∀ v ∈ perp L S.Hm (S.spanTo g r), n v - v = hf L S.Hm v u • x := fun v hv => by
    rw [h1, eich, hv x hxX]; simp
  have e2 : ∀ v ∈ perp L S.Hm (S.spanTo g r), n⁻¹ v - v = -(hf L S.Hm v u • x) := fun v hv => by
    rw [h2, eich, hv x hxX, hf_neg_r]; simp
  have e3 : ∀ l : Fin r, ∀ v ∈ S.spanTo g (l + 1), hf L S.Hm v u • x ∈ S.spanTo g l := by
    intro l v hv
    by_cases h : (j : ℕ) ≤ l
    · exact Submodule.smul_mem _ _ (spanTo_mono S g h hx)
    · rw [hlow v (spanTo_mono S g (by omega) hv)]; simp
  refine ⟨n, ⟨⟨hn, Subgroup.mem_iInf.2 fun l => ?_⟩, ?_⟩, ?_, fun i hi => ?_, fun v hv => ?_⟩
  · have hl : S.spanTo g (l + 1) ≤ perp L S.Hm (S.spanTo g r) :=
      (spanTo_mono S g l.2).trans (spanTo_le_perp S g T gram)
    refine mem_unipOn (spanTo_mono S g (Nat.le_succ _)) n (fun v hv => ?_) (fun v hv => ?_)
    · rw [e1 v (hl hv)]; exact e3 l v hv
    · rw [e2 v (hl hv)]; exact Submodule.neg_mem _ (e3 l v hv)
  · refine mem_unipOn (spanTo_le_perp S g T gram) n (fun v hv => ?_) (fun v hv => ?_)
    · rw [e1 v hv]; exact Submodule.smul_mem _ _ hxX
    · rw [e2 v hv]; exact Submodule.neg_mem _ (Submodule.smul_mem _ _ hxX)
  · have := e1 _ (mem_perp S g T gram j)
    rw [hu, if_pos rfl, one_smul] at this
    rw [← this]; abel
  · have := e1 _ (mem_perp S g T gram i)
    rw [hu, if_neg hi, zero_smul] at this
    exact sub_eq_zero.1 this
  · have := e1 _ (spanTo_le_perp S g T gram (spanTo_mono S g hjr hv))
    rw [hlow v hv, zero_smul] at this
    exact sub_eq_zero.1 this

include gram dual in
theorem exists_upto [IsNonarchimedeanLocalField F] [CharZero F] (x : Fin (r + 1) → S.V)
    (hx : ∀ j : Fin (r + 1), x j ∈ S.spanTo g j) (m : ℕ) :
    ∃ n ∈ S.Nof g, ∀ j : Fin (r + 1), n (g j) = if (j : ℕ) < m then g j + x j else g j := by
  induction m with
  | zero => exact ⟨1, one_mem _, fun j => by simp⟩
  | succ m ih =>
    obtain ⟨n, hn, h⟩ := ih
    by_cases hm : m < r + 1
    · obtain ⟨e, he, h1, h2, h3⟩ := exists_step S g gs T gram dual ⟨m, hm⟩ _ (hx ⟨m, hm⟩)
      refine ⟨e * n, mul_mem he hn, fun j => ?_⟩
      change e (n (g j)) = _
      rw [h]
      rcases lt_trichotomy (j : ℕ) m with hj | hj | hj
      · rw [if_pos hj, if_pos (by omega)]
        exact h3 _ (add_mem (mem_spanTo S g hj) (spanTo_mono S g hj.le (hx j)))
      · obtain rfl : j = ⟨m, hm⟩ := Fin.ext hj
        rw [if_neg (by simp), if_pos (by simp), h1]
      · rw [if_neg (by omega), if_neg (by omega)]
        exact h2 j fun hh => by rw [hh] at hj; simp at hj
    · refine ⟨n, hn, fun j => ?_⟩
      have := j.2
      rw [h, if_pos (by omega), if_pos (by omega)]


include gram dual in
theorem exists_elt [IsNonarchimedeanLocalField F] [CharZero F]
    (s : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (hs : (∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) :
    ∃ n ∈ S.Nof g, ∀ j, n (g j) = ∑ i, s i j • g i := by
  have hx : ∀ j : Fin (r + 1), ∑ i ∈ Finset.univ.erase j, s i j • g i ∈ S.spanTo g j := by
    intro j
    refine Submodule.sum_mem _ fun i hi => ?_
    rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hi) with h | h
    · exact Submodule.smul_mem _ _ (mem_spanTo S g h)
    · rw [hs.1 i j h]; simp
  obtain ⟨n, hn, h⟩ := exists_upto S g gs T gram dual _ hx (r + 1)
  refine ⟨n, hn, fun j => ?_⟩
  rw [h, if_pos j.2, ← Finset.add_sum_erase _ _ (Finset.mem_univ j), hs.2, one_smul]

end

theorem unipotent_onto : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), (∀ n ∈ S.N, ∃ s : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) ∧ ∀ j, n (S.f j) = ∑ i, s i j • S.f i) ∧ (∀ n ∈ S.N', ∃ s : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) ∧ ∀ j, n (S.f' j) = ∑ i, s i j • S.f' i) ∧ ∀ s : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) → (∃ n ∈ S.N, ∀ j, n (S.f j) = ∑ i, s i j • S.f i) ∧ ∃ n ∈ S.N', ∀ j, n (S.f' j) = ∑ i, s i j • S.f' i := by
  intro F _ _ _ _ _ E _ _ _ L r k S
  exact ⟨exists_matrix S S.f S.T S.gram, exists_matrix S S.f' S.T' S.gram', fun s hs =>
    ⟨exists_elt S S.f S.es S.T S.gram S.dual s hs, exists_elt S S.f' S.es' S.T' S.gram' S.dual' s hs⟩⟩

end GlobalTheory.HL.FrameOnto
end

section

noncomputable section

namespace GlobalTheory.GaugeQuot

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot
open scoped ENNReal

variable {P Q P' Q' : ℕ}

def hsDist (g : UpqT P Q) : ℝ := ∑ i, ∑ j, ‖(UpqT.mat g - 1) i j‖ ^ 2

def ptSq (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (y : Sp P Q) : ℝ :=
  ‖y (e none) - 1‖ ^ 2 + 2 * ∑ i, ‖y (e (some i))‖ ^ 2

def tanSq (t : ℝ × Sp P' Q') : ℝ := t.1 ^ 2 + 2 * ∑ i, ‖t.2 i‖ ^ 2

def gaussSp (y : Sp P Q) : ℝ := Real.exp (-∑ i, ‖y i‖ ^ 2)

def ballVol (d : ℕ) (r : ℝ) : ℝ≥0∞ := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r)

def HasEuclDensity (μ : Measure (UpqT P Q)) : Prop :=
  Tendsto (fun r : ℝ => μ {g | hsDist g < r ^ 2} / ballVol ((P + Q) ^ 2) r) (𝓝[>] 0) (𝓝 1)

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in
variable {P Q P' Q' : ℕ} in
theorem _root_.GlobalTheory.GaugeQuot.hsDist_nonneg (g : _root_.Formalism.BasicNotions.UpqT P Q) : 0 ≤ _root_.GlobalTheory.GaugeQuot.hsDist g := by
  unfold _root_.GlobalTheory.GaugeQuot.hsDist
  positivity

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in
variable {P Q P' Q' : ℕ} in
theorem _root_.GlobalTheory.GaugeQuot.continuous_hsDist : Continuous (_root_.GlobalTheory.GaugeQuot.hsDist : _root_.Formalism.BasicNotions.UpqT P Q → ℝ) := by
  have hmat : Continuous (_root_.Formalism.BasicNotions.UpqT.mat : _root_.Formalism.BasicNotions.UpqT P Q → _) := _root_.GlobalTheory.UpqTopology.continuous_mat
  unfold _root_.GlobalTheory.GaugeQuot.hsDist
  fun_prop

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in
variable {P Q P' Q' : ℕ} in
theorem _root_.GlobalTheory.GaugeQuot.ptSq_nonneg (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q))
    (y : _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.Sp P Q) : 0 ≤ _root_.GlobalTheory.GaugeQuot.ptSq e y := by
  unfold _root_.GlobalTheory.GaugeQuot.ptSq
  positivity

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in
variable {P Q P' Q' : ℕ} in
theorem _root_.GlobalTheory.GaugeQuot.continuous_ptSq (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) :
    Continuous (_root_.GlobalTheory.GaugeQuot.ptSq e) := by
  unfold _root_.GlobalTheory.GaugeQuot.ptSq
  fun_prop

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in
variable {P Q P' Q' : ℕ} in
theorem _root_.GlobalTheory.GaugeQuot.tanSq_nonneg (t : ℝ × _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.Sp P' Q') :
    0 ≤ _root_.GlobalTheory.GaugeQuot.tanSq t := by
  unfold _root_.GlobalTheory.GaugeQuot.tanSq
  positivity

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in
variable {P Q P' Q' : ℕ} in
theorem _root_.GlobalTheory.GaugeQuot.continuous_tanSq :
    Continuous (_root_.GlobalTheory.GaugeQuot.tanSq : ℝ × _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.Sp P' Q' → ℝ) := by
  unfold _root_.GlobalTheory.GaugeQuot.tanSq
  fun_prop

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in
variable {P Q P' Q' : ℕ} in
theorem _root_.GlobalTheory.GaugeQuot.continuous_gaussSp :
    Continuous (_root_.GlobalTheory.GaugeQuot.gaussSp : _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.Sp P Q → ℝ) := by
  unfold _root_.GlobalTheory.GaugeQuot.gaussSp
  fun_prop

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in
variable {P Q P' Q' : ℕ} in
theorem _root_.GlobalTheory.GaugeQuot.ballVol_mul (d : ℕ) (t r : ℝ) (ht : 0 < t) (hr : 0 < r) :
    _root_.GlobalTheory.GaugeQuot.ballVol d (t * r) = ENNReal.ofReal (t ^ d) * _root_.GlobalTheory.GaugeQuot.ballVol d r := by
  unfold _root_.GlobalTheory.GaugeQuot.ballVol
  rw [Measure.addHaar_ball_mul_of_pos _ _ ht, finrank_euclideanSpace_fin]

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in
variable {P Q P' Q' : ℕ} in
theorem _root_.GlobalTheory.GaugeQuot.ballVol_ne_zero (d : ℕ) {r : ℝ} (hr : 0 < r) :
    _root_.GlobalTheory.GaugeQuot.ballVol d r ≠ 0 :=
  (Metric.measure_ball_pos volume _ hr).ne'

open MeasureTheory Matrix Filter Topology in
open scoped ENNReal in
variable {P Q P' Q' : ℕ} in
theorem _root_.GlobalTheory.GaugeQuot.ballVol_ne_top (d : ℕ) (r : ℝ) : _root_.GlobalTheory.GaugeQuot.ballVol d r ≠ ⊤ :=
  measure_ball_lt_top.ne

end GlobalTheory.GaugeQuot
end
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.HL.StdPlace NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.SelfDual

open Matrix GlobalTheory.HL.Eichler GlobalTheory.UnramOrder

theorem exists_orthonormal_same_span : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ b : Fin m → Fin n → E, (∀ i j, hf L Hm (b i) (b j) ∈ L.O) → (∃ P : Matrix (Fin m) (Fin m) E, IsIntM L P ∧ (Matrix.of fun i j => hf L Hm (b i) (b j)) * P = 1) → ∃ b' : Fin m → Fin n → E, (∀ i j, hf L Hm (b' i) (b' j) = if i = j then 1 else 0) ∧ Submodule.span L.O (Set.range b') = Submodule.span L.O (Set.range b) := by
  intro F _ _ _ _ _ E _ _ _ L n m Hm hH b hint₀ hunim
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨htr, -, -, hpir, -, -, -, hnorm⟩ := order_facts L ϖ hϖ
  obtain ⟨P₀, hP₀, hGP₀⟩ := hunim
  have hmem : ∀ i, b i ∈ Submodule.span L.O (Set.range b) := fun i =>
    Submodule.subset_span ⟨i, rfl⟩
  have hsm : ∀ (a : L.O) (v : Fin n → E), a • v = (a : E) • v := fun _ _ => rfl
  let c : L.O →+* L.O := (L.cj : E →+* E).restrict L.O L.O fun x hx => cj_mem L hx
  have hcv : ∀ x : L.O, ((c x : L.O) : E) = L.cj x := fun _ => rfl
  have hc : ∀ x, c (c x) = x := fun x => Subtype.ext (L.cj_cj x)
  let G : Matrix (Fin m) (Fin m) L.O := fun i j => ⟨hf L Hm (b i) (b j), hint₀ i j⟩
  have hGv : ∀ i j, (G i j : E) = hf L Hm (b i) (b j) := fun _ _ => rfl
  have hG : ∀ i j, c (G i j) = G j i := fun i j => Subtype.ext (hf_cj L hH.1 _ _)
  let Q : Matrix (Fin m) (Fin m) L.O := fun i j => ⟨P₀ i j, hP₀ i j⟩
  have hGQ : G * Q = 1 := by
    ext i j
    have h := congrFun (congrFun hGP₀ i) j
    rw [Matrix.one_apply, apply_ite Subtype.val, OneMemClass.coe_one, ZeroMemClass.coe_zero,
      Matrix.mul_apply, AddSubmonoidClass.coe_finsetSum]
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    exact h
  have hint : ∀ a : 𝒪[F], algebraMap F E a ∈ L.O := fun a => (algebraMap_mem_iff L a).2 a.2
  let i : 𝒪[F] →+* L.O := (algebraMap 𝒪[F] E).codRestrict L.O hint
  let : Algebra 𝒪[F] L.O := i.toAlgebra
  have hfix : ∀ x, c x = x → x ∈ (algebraMap 𝒪[F] L.O).range := fun x hx => by
    obtain ⟨a, ha⟩ := exists_int_of_fixed L x.2 (congrArg Subtype.val hx)
    exact ⟨a, Subtype.ext ha.symm⟩
  have hinj : Function.Injective (algebraMap 𝒪[F] L.O) := fun a b h =>
    Subtype.ext (algebraMap_inj L (congrArg Subtype.val h))
  obtain ⟨P, hP, hGP⟩ := GlobalTheory.UnramifiedHermitian.exists_eq_transpose_mul_map (R₀ := 𝒪[F]) c hc hfix
    (by
      obtain ⟨w, hw, h⟩ := htr 1
      exact ⟨⟨w, hw⟩, Subtype.ext (by simpa [hcv] using h)⟩)
    (fun u hu hu' => by
      obtain ⟨v, hv⟩ := hu'.exists_right_inv
      have hv' := congrArg c hv
      rw [map_mul, hu, map_one] at hv'
      obtain ⟨s, rfl⟩ := hfix v (by linear_combination v * hv' - c v * hv)
      obtain ⟨r, rfl⟩ := hfix u hu
      have hr : IsUnit r := IsUnit.of_mul_eq_one s (hinj (by rw [map_mul, hv, map_one]))
      obtain ⟨x, hx, h⟩ := hnorm hr.unit
      exact ⟨⟨x, hx⟩, Subtype.ext h⟩)
    hG (Matrix.isUnit_det_of_right_inverse hGQ)
  have hQ : (P⁻¹)ᵀ * G * (P⁻¹).map c = 1 := by
    rw [hGP, ← Matrix.mul_assoc, ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hP,
      Matrix.transpose_one, Matrix.one_mul, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hP,
      Matrix.map_one _ (map_zero c) (map_one c)]
  refine ⟨fun i => ∑ k, P⁻¹ k i • b k, fun i j => ?_, le_antisymm ?_ ?_⟩
  · have h := congrArg Subtype.val (congrFun (congrFun hQ i) j)
    rw [Matrix.one_apply, apply_ite Subtype.val, OneMemClass.coe_one, ZeroMemClass.coe_zero] at h
    rw [← h]
    simp only [hsm, hf_sum_l, hf_sum_r, Matrix.mul_apply, AddSubmonoidClass.coe_finsetSum,
      Subring.coe_mul, Matrix.transpose_apply, Matrix.map_apply, hcv, hGv]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hmem l)
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    refine (Submodule.mem_span_range_iff_exists_fun L.O).2 ⟨fun i => P i k, ?_⟩
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    have h : ∀ l, ∑ i, P i k * P⁻¹ l i = if l = k then 1 else 0 := fun l => by
      rw [← Matrix.one_apply, ← Matrix.nonsing_inv_mul _ hP, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    simp [← Finset.sum_smul, h]

end GlobalTheory.HL.SelfDual
end
