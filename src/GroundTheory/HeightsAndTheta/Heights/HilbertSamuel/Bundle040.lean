module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle024
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle023
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle018
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle025
public import Mathlib.Order.CompletePartialOrder
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenSESStep
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle030
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle038
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle034
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

theorem ProjFrameFibreDeg.proof (hPt : ProjFrameFibrePt.Statement) (hRel : ProjFrameGenPtRel.Statement)
    (hTr : ProjFrameGenPtTransc.Statement) (hDeg : TranscRatioDeg.Statement) (hRat : RatioFieldDeg.Statement) :
    ProjFrameFibreDeg.Statement := by
  intro D Ω _ _ κ _ x e hP hF G i hi
  obtain ⟨hc, hcoord, hrel, hrange⟩ := hRel D Ω κ x e hP hF G
  have : CharZero G.Φ' := charZero_of_inj_zero hc

  have hz : ∀ k, G.x' ⟨k.1, i k⟩ ≠ 0 := fun k h => hi k (by
    rw [ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal, RingHom.mem_ker, aeval_X]; exact h)
  have hch := Inter.ChartRankAdjoin.proof (FibreBlock (Sum.inr : Unit → Unit ⊕ Unit))
    (fibreIdx (Sum.elim (GlobalTheory κ) (GlobalTheory (Fin (D + 1)))) Sum.inr) G.Φ G.Φ' (fun q => G.x' ⟨q.1.1, q.2⟩) i hz
    (hPt D Ω κ x e hP hF G).1.2.1
  let k₀ : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit) := ⟨Sum.inl (), fun ⟨_, h⟩ => Sum.inr_ne_inl h⟩
  let u : Ix κ → G.Φ' := fun p => G.x' ⟨Sum.inl p.1, p.2⟩
  have hset : (Set.range fun q : (Σ k : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit),
      fibreIdx (Sum.elim (GlobalTheory κ) (GlobalTheory (Fin (D + 1)))) Sum.inr k) =>
        G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, i q.1⟩) = Set.range fun p : Ix κ => u p / u ⟨(), i k₀⟩ := by
    ext c
    constructor
    · rintro ⟨⟨⟨(t | t), h⟩, j⟩, rfl⟩
      · exact ⟨⟨(), j⟩, rfl⟩
      · exact absurd ⟨t, rfl⟩ h
    · rintro ⟨⟨_, j⟩, rfl⟩
      exact ⟨⟨k₀, j⟩, rfl⟩
  change ptDeg (RingHom.ker _) i = _
  rw [hch, hset]
  rw [hDeg (Ix κ) G.Φ' u D e (fun k => G.x' ⟨Sum.inr (), k⟩) ⟨(), i k₀⟩ G.Φ (hz k₀)
    (fun k => ProjFrameGraph.genFibre_x'_ne_zero G (e k).2 (ProjFrameGraph.frame_ne_zero hF k)) hrel
    (hTr D Ω κ x e hP hF G) hrange]
  exact hRat (Ix κ) G.Φ' Ω u x D e hcoord

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace LocIdealKer

variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
  {𝓜 : (K → ℤ) → Submodule S M}

def degProducts (𝓜 : (K → ℤ) → Submodule S M) (P : Ideal (MRingOver S ι)) (D : K → ℤ) : Set M :=
  {x | ∃ (p : MRingOver S ι) (b : K → ℕ) (n : M), p ∈ P ∧ IsMultiHomog p b ∧
    n ∈ 𝓜 (D - fun k => (b k : ℤ)) ∧ x = p • n}

theorem span_degProducts_le (h𝓜 : KH.IsMGraded S ι 𝓜) (P : Ideal (MRingOver S ι)) (D : K → ℤ) :
    Submodule.span S (degProducts 𝓜 P D) ≤ 𝓜 D := by
  rw [Submodule.span_le]
  rintro _ ⟨p, b, n, -, hp, hn, rfl⟩
  have := h𝓜.2 b _ p n hp hn
  rwa [sub_add_cancel] at this

theorem exists_near (h𝓜 : KH.IsMGraded S ι 𝓜) {P : Ideal (MRingOver S ι)} (hP : IsMultiHomogIdeal P)
    (D : K → ℤ) {x : M} (hx : x ∈ (P • ⊤ : Submodule (MRingOver S ι) M)) :
    ∃ y ∈ Submodule.span S (degProducts 𝓜 P D), x - y ∈ ⨆ (j) (_ : j ≠ D), 𝓜 j := by
  classical
  obtain ⟨G, hG, hPG⟩ := hP
  have hadd : ∀ x₁ x₂ : M,
      (∃ y ∈ Submodule.span S (degProducts 𝓜 P D), x₁ - y ∈ ⨆ (j) (_ : j ≠ D), 𝓜 j) →
      (∃ y ∈ Submodule.span S (degProducts 𝓜 P D), x₂ - y ∈ ⨆ (j) (_ : j ≠ D), 𝓜 j) →
      ∃ y ∈ Submodule.span S (degProducts 𝓜 P D), x₁ + x₂ - y ∈ ⨆ (j) (_ : j ≠ D), 𝓜 j := by
    rintro x₁ x₂ ⟨y₁, hy₁, e₁⟩ ⟨y₂, hy₂, e₂⟩
    refine ⟨y₁ + y₂, add_mem hy₁ hy₂, ?_⟩
    rw [add_sub_add_comm]
    exact add_mem e₁ e₂
  have hzero : ∃ y ∈ Submodule.span S (degProducts 𝓜 P D), (0 : M) - y ∈ ⨆ (j) (_ : j ≠ D), 𝓜 j :=
    ⟨0, zero_mem _, by rw [sub_zero]; exact zero_mem _⟩

  have hgen : ∀ g ∈ G, ∀ n : M,
      ∃ y ∈ Submodule.span S (degProducts 𝓜 P D), g • n - y ∈ ⨆ (j) (_ : j ≠ D), 𝓜 j := by
    intro g hg n
    obtain ⟨b, hb⟩ := hG g hg
    have hgP : g ∈ P := by rw [hPG]; exact Ideal.subset_span hg
    have hn : n ∈ ⨆ j, 𝓜 j := by
      rw [h𝓜.1.submodule_iSup_eq_top]
      exact Submodule.mem_top
    refine Submodule.iSup_induction (motive := fun n => ∃ y ∈ Submodule.span S (degProducts 𝓜 P D),
      g • n - y ∈ ⨆ (j) (_ : j ≠ D), 𝓜 j) 𝓜 hn ?_ ?_ ?_
    · intro j n hn
      have hgn := h𝓜.2 b j g n hb hn
      by_cases hj : (j + fun k => (b k : ℤ)) = D
      · refine ⟨g • n, Submodule.subset_span ⟨g, b, n, hgP, hb, ?_, rfl⟩, ?_⟩
        · rw [← hj, add_sub_cancel_right]
          exact hn
        · rw [sub_self]
          exact zero_mem _
      · refine ⟨0, zero_mem _, ?_⟩
        rw [sub_zero]
        exact Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem hj hgn)
    · rw [smul_zero]
      exact hzero
    · intro n₁ n₂ h₁ h₂
      rw [smul_add]
      exact hadd _ _ h₁ h₂

  have hP' : ∀ p ∈ P, ∀ n : M,
      ∃ y ∈ Submodule.span S (degProducts 𝓜 P D), p • n - y ∈ ⨆ (j) (_ : j ≠ D), 𝓜 j := by
    intro p hp
    rw [hPG] at hp
    induction hp using Submodule.span_induction with
    | mem g hg => exact hgen g hg
    | zero =>
      intro n
      rw [zero_smul]
      exact hzero
    | add p q _ _ hp hq =>
      intro n
      rw [add_smul]
      exact hadd _ _ (hp n) (hq n)
    | smul r p _ hp =>
      intro n
      rw [smul_eq_mul, mul_comm, mul_smul]
      exact hp (r • n)
  exact Submodule.smul_induction_on hx (fun p hp n _ => hP' p hp n) (fun x₁ x₂ h₁ h₂ => hadd _ _ h₁ h₂)

theorem mem_span_degProducts (h𝓜 : KH.IsMGraded S ι 𝓜) {P : Ideal (MRingOver S ι)} (hP : IsMultiHomogIdeal P)
    {D : K → ℤ} {x : M} (hx : x ∈ (P • ⊤ : Submodule (MRingOver S ι) M)) (hxD : x ∈ 𝓜 D) :
    x ∈ Submodule.span S (degProducts 𝓜 P D) := by
  obtain ⟨y, hy, hd⟩ := exists_near h𝓜 hP D hx
  have hc : x - y ∈ 𝓜 D := sub_mem hxD (span_degProducts_le h𝓜 P D hy)
  have h0 : x - y = 0 := Submodule.disjoint_def.mp (h𝓜.1.submodule_iSupIndep D) _ hc hd
  rw [sub_eq_zero] at h0
  rw [h0]
  exact hy

theorem proof : LocIdealKer.Statement := by
  intro S _ K _ ι _ M _ _ _ _ 𝓜 P T d h𝓜 hP hT w hw
  classical
  let _ : LinearOrder K := LinearOrder.lift' (Fintype.equivFin K) (Fintype.equivFin K).injective
  let _ : ∀ k, LinearOrder (ι k) := fun k =>
    LinearOrder.lift' (Fintype.equivFin (ι k)) (Fintype.equivFin (ι k)).injective
  set N := (P • ⊤ : Submodule (MRingOver S ι) M) with hN
  set L := IsLocalizedModule.map T (LocalizedModule.mkLinearMap T M)
    (LocalizedModule.mkLinearMap T (M ⧸ N)) N.mkQ with hL
  have hLmk : ∀ (m : M) (t : T), L (LocalizedModule.mk m t) = LocalizedModule.mk (N.mkQ m) t := by
    intro m t
    rw [hL, IsLocalizedModule.mk_eq_mk', IsLocalizedModule.map_mk', ← IsLocalizedModule.mk_eq_mk']
  constructor
  ·
    have hkill : ∀ p ∈ P, ∀ z : LocalizedModule T (M ⧸ N), p • z = 0 := by
      intro p hp z
      induction z using LocalizedModule.induction_on with
      | h q t =>
        obtain ⟨n, rfl⟩ := Submodule.mkQ_surjective N q
        rw [LocalizedModule.smul'_mk, ← map_smul, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero N).2
          (Submodule.smul_mem_smul hp Submodule.mem_top), LocalizedModule.zero_mk]
    intro hwP
    clear hw
    induction hwP using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨p, a, y, hp, -, -, rfl⟩ := hx
      rw [map_smul]
      exact hkill p hp _
    | zero => exact map_zero L
    | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, add_zero]
    | smul s x _ hx =>
      rw [← algebraMap_smul (MRingOver S ι) s x, map_smul, hx, smul_zero]
  · intro h0
    obtain ⟨m, t, a, ht, hm, rfl⟩ := GenSESStep.locPart_normal h𝓜 hw
    rw [hLmk, ← LocalizedModule.zero_mk (1 : T), LocalizedModule.mk_eq] at h0
    obtain ⟨u, hu⟩ := h0
    rw [one_smul, smul_zero, smul_zero, Submonoid.smul_def, ← map_smul, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero] at hu
    obtain ⟨e, he⟩ := hT u u.2
    set D : K → ℤ := (d + fun k => (a k : ℤ)) + fun k => (e k : ℤ) with hD
    have humD : (u : MRingOver S ι) • m ∈ 𝓜 D := h𝓜.2 e _ _ m he hm
    have hspan := mem_span_degProducts h𝓜 hP hu humD
    have hut : IsMultiHomog ((u * t : T) : MRingOver S ι) (e + a) := GenSESStep.isMultiHomog_mul he ht
    rw [← LocalizedModule.mk_cancel_common_left u t m, Submonoid.smul_def]
    generalize (u : MRingOver S ι) • m = x at hspan ⊢
    induction hspan using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨p, b, n, hp, hpb, hn, rfl⟩ := hx
      rw [← LocalizedModule.smul'_mk]
      refine Submodule.subset_span ⟨p, b, _, hp, hpb, GenSESStep.mk_mem_locPart n (u * t) (e + a) hut ?_, rfl⟩
      have edeg : ((d - fun k => (b k : ℤ)) + fun k => ((e + a) k : ℤ)) = D - fun k => (b k : ℤ) := by
        funext k
        simp only [hD, Pi.add_apply, Pi.sub_apply, Nat.cast_add]
        ring
      rw [edeg]
      exact hn
    | zero =>
      rw [LocalizedModule.zero_mk]
      exact zero_mem _
    | add x y _ _ hx hy =>
      rw [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.mk'_add, ← IsLocalizedModule.mk_eq_mk',
        ← IsLocalizedModule.mk_eq_mk']
      exact add_mem hx hy
    | smul s x _ hx =>
      rw [← LocalizedModule.smul'_mk]
      exact Submodule.smul_mem _ s hx

end LocIdealKer

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace SpanStepHomog

variable {K : Type} [Fintype K] {ι : K → Type} {Ω : Type} [Field Ω]

theorem mul_mem {y : (Σ k, ι k) → Ω} {a : K → ℤ} {n j : ℕ} {s t : Ω} (hs : s ∈ chartLat y a n)
    (ht : t ∈ chartLat y a j) : s * t ∈ chartLat y a (n + j) := by
  intro c hc
  have h : ∏ k, y ⟨k, c k⟩ ^ (-(((n + j : ℕ) : ℤ) * a k)) =
      (∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * ∏ k, y ⟨k, c k⟩ ^ (-((j : ℤ) * a k)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_add₀ (hc k)]
    congr 1
    push_cast
    ring
  rw [h, show s * t * ((∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * ∏ k, y ⟨k, c k⟩ ^ (-((j : ℤ) * a k))) =
      (s * ∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * (t * ∏ k, y ⟨k, c k⟩ ^ (-((j : ℤ) * a k))) by ring]
  exact MulMemClass.mul_mem (hs c hc) (ht c hc)

theorem pow_mem {y : (Σ k, ι k) → Ω} {a : K → ℤ} {v : Ω} (hv : v ∈ chartLat y a 1) (e : ℕ) :
    v ^ e ∈ chartLat y a e := by
  induction e with
  | zero => intro c _; simp
  | succ e ih => rw [pow_succ]; exact mul_mem ih hv

abbrev forms {q : ℕ} (w : Fin q → Ω) (e : ℕ) : AddSubgroup Ω :=
  gradedSpan w (fun _ : Fin 1 => 0) (fun _ => 1) e

theorem mul_forms_mem {q r : ℕ} {w : Fin q → Ω} {d : Fin r → ℕ} {t : Fin r → Ω} {N e : ℕ} {x f : Ω}
    (hx : x ∈ gradedSpan w d t N) (hf : f ∈ forms w e) : x * f ∈ gradedSpan w d t (N + e) := by
  have hmono : ∀ μ : Fin q → ℕ, x * ∏ i, w i ^ μ i ∈ gradedSpan w d t (N + ∑ i, μ i) := by
    intro μ
    induction hx using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨l, ν, hν, rfl⟩ := hz
      have h := gradedSpan_gen_mem w d t l (ν + μ)
      have hdeg : d l + ∑ i, (ν + μ) i = N + ∑ i, μ i := by
        rw [← hν]; simp [Finset.sum_add_distrib, add_assoc]
      have hval : t l * ∏ i, w i ^ (ν + μ) i = t l * (∏ i, w i ^ ν i) * ∏ i, w i ^ μ i := by
        simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]; ring
      rwa [hdeg, hval] at h
    | zero => rw [zero_mul]; exact zero_mem _
    | add z z' _ _ hz hz' => rw [add_mul]; exact add_mem hz hz'
    | neg z _ hz => rw [neg_mul]; exact neg_mem hz
  induction hf using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨l, μ, hμ, rfl⟩ := hz
    have h := hmono μ
    rwa [one_mul, ← hμ, zero_add]
  | zero => rw [mul_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [mul_add]; exact add_mem hz hz'
  | neg z _ hz => rw [mul_neg]; exact neg_mem hz

theorem one_mem_forms {q : ℕ} (w : Fin q → Ω) : (1 : Ω) ∈ forms w 0 := by
  have h := gradedSpan_gen_mem w (fun _ : Fin 1 => 0) (fun _ => (1 : Ω)) 0 (fun _ => 0)
  simpa using h

theorem mem_forms_one {q : ℕ} (w : Fin q → Ω) (i : Fin q) : w i ∈ forms w 1 := by
  have h := gradedSpan_gen_mem w (fun _ : Fin 1 => 0) (fun _ => (1 : Ω)) 0 (Pi.single i 1)
  simpa [Pi.single_apply, pow_ite, Finset.prod_ite_eq'] using h

theorem pow_mem_forms {q : ℕ} (w : Fin q → Ω) (i : Fin q) (e : ℕ) : w i ^ e ∈ forms w e := by
  induction e with
  | zero => simpa using one_mem_forms w
  | succ e ih => rw [pow_succ]; exact mul_forms_mem ih (mem_forms_one w i)

theorem exists_mul_pow_mem_forms {q : ℕ} {w : Fin q → Ω} {j : Fin q} (hj : w j ≠ 0) {c : Ω}
    (hc : c ∈ Algebra.adjoin ℤ (Set.range fun i => w i / w j)) : ∃ E : ℕ, c * w j ^ E ∈ forms w E := by
  induction hc using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    refine ⟨1, ?_⟩
    rw [pow_one, div_mul_cancel₀ _ hj]
    exact mem_forms_one w i
  | algebraMap r =>
    refine ⟨0, ?_⟩
    rw [pow_zero, mul_one, algebraMap_int_eq, eq_intCast, ← zsmul_one]
    exact zsmul_mem (one_mem_forms w) r
  | add x x' _ _ hx hx' =>
    obtain ⟨E, hE⟩ := hx
    obtain ⟨E', hE'⟩ := hx'
    refine ⟨E + E', ?_⟩
    have h1 := mul_forms_mem hE (pow_mem_forms w j E')
    have h2 := mul_forms_mem hE' (pow_mem_forms w j E)
    rw [add_comm E' E] at h2
    rw [show (x + x') * w j ^ (E + E') = x * w j ^ E * w j ^ E' + x' * w j ^ E' * w j ^ E by ring]
    exact add_mem h1 h2
  | mul x x' _ _ hx hx' =>
    obtain ⟨E, hE⟩ := hx
    obtain ⟨E', hE'⟩ := hx'
    refine ⟨E + E', ?_⟩
    rw [show x * x' * w j ^ (E + E') = x * w j ^ E * (x' * w j ^ E') by ring]
    exact mul_forms_mem hE hE'

theorem mul_pow_mem_forms_of_le {q : ℕ} {w : Fin q → Ω} {j : Fin q} {c : Ω} {E E' : ℕ}
    (h : c * w j ^ E ∈ forms w E) (hle : E ≤ E') : c * w j ^ E' ∈ forms w E' := by
  have h' := mul_forms_mem h (pow_mem_forms w j (E' - E))
  rwa [mul_assoc, ← pow_add, Nat.add_sub_cancel' hle] at h'

end SpanStepHomog


open SpanStepHomog in
theorem SpanStepHomog.proof (hL : SpanStepLocal.Statement) : SpanStepHomog.Statement := by
  intro K _ ι _ Ω _ y a q w hy hw hgen
  have H : ∀ j, ∃ (r : ℕ) (b : Fin r → Ω), (∀ l, ∃ n : ℕ, b l * w j ^ n ∈ chartLat y a n) ∧
      (w j ≠ 0 → ∀ (g : Ω) (n : ℕ), g * w j ^ n ∈ chartLat y a n →
        ∃ c : Fin r → Ω, (∀ l, c l ∈ Algebra.adjoin ℤ (Set.range fun i => w i / w j)) ∧
          g = ∑ l, c l * b l) := by
    intro j
    by_cases hj : w j = 0
    · exact ⟨0, Fin.elim0, fun l => l.elim0, fun h => (h hj).elim⟩
    · obtain ⟨r, b, h1, h2⟩ := hL K ι Ω y a q w hy hw hgen j hj
      exact ⟨r, b, h1, fun _ => h2⟩
  choose r b hb hspan using H
  choose nb hnb using hb
  set m := ∑ j, ∑ l, nb j l with hm
  have hle : ∀ j l, nb j l ≤ m := fun j l =>
    (Finset.single_le_sum (f := nb j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)).trans
      (Finset.single_le_sum (f := fun j => ∑ l, nb j l) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))
  let e := Fintype.equivFin (Σ j, Fin (r j))
  let T : (Σ j, Fin (r j)) → Ω := fun p => b p.1 p.2 * w p.1 ^ m
  let t : Fin (Fintype.card (Σ j, Fin (r j))) → Ω := fun i => T (e.symm i)
  have htv : ∀ j l, t (e ⟨j, l⟩) = b j l * w j ^ m := fun j l => by
    show T (e.symm (e ⟨j, l⟩)) = _
    rw [Equiv.symm_apply_apply]
  refine ⟨m, _, t, fun i => ?_, fun n s hs j hj => ?_⟩
  · have h := mul_mem (hnb (e.symm i).1 (e.symm i).2) (pow_mem (hw (e.symm i).1) (m - nb (e.symm i).1 (e.symm i).2))
    rwa [mul_assoc, ← pow_add, Nat.add_sub_cancel' (hle _ _)] at h
  have hwn : w j ^ n ≠ 0 := pow_ne_zero n hj
  obtain ⟨c, hc, hg⟩ := hspan j hj (s / w j ^ n) n (by rwa [div_mul_cancel₀ _ hwn])
  choose E hE using fun l => exists_mul_pow_mem_forms hj (hc l)
  refine ⟨m + ∑ l, E l, ?_⟩
  have hs' : s * w j ^ (m + ∑ l, E l) =
      ∑ l, t (e ⟨j, l⟩) * (c l * w j ^ (∑ l, E l)) * w j ^ n := by
    rw [show s = s / w j ^ n * w j ^ n by rw [div_mul_cancel₀ _ hwn], hg, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [htv, pow_add]; ring
  rw [hs', show n + (m + ∑ l, E l) = m + ∑ l, E l + n by ring]
  refine sum_mem fun l _ => mul_forms_mem (mul_forms_mem ?_ (mul_pow_mem_forms_of_le (hE l)
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)))) (pow_mem_forms w j n)
  have h := gradedSpan_gen_mem w (fun _ => m) t (e ⟨j, l⟩) (fun _ => 0)
  simpa using h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def RelOneStep.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (R : Subalgebra ℤ Ω), IsNoetherianRing R → ∀ (y : (Σ k, ι k) → Ω) (c0 : ∀ k, ι k),
    (∀ k, y ⟨k, c0 k⟩ ≠ 0) → ∃ n₁ : ℕ, ∀ b : K → ℕ, (∀ k, n₁ ≤ b k) → ∀ k0 : K,
      ∀ t ∈ relChartLat R y (fun k => (b k : ℤ)) 1, y ⟨k0, c0 k0⟩ * t ∈ relSecM R y (b + Pi.single k0 1) →
        t ∈ relSecM R y b

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def RelSectionsLarge.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (R : Subalgebra ℤ Ω), IsNoetherianRing R → ∀ y : (Σ k, ι k) → Ω, (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) →
      ∃ n₁ : ℕ, ∀ b : K → ℕ, (∀ k, n₁ ≤ b k) → relChartLat R y (fun k => (b k : ℤ)) 1 ≤ relSecM R y b

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
