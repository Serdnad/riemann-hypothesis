module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle014
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle017
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle073
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3442
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle581
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3193
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2670
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1407
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1476
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1314
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1312
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1313
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3443
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle031

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

theorem _root_.GlobalTheory.T.harrisTaylor_firstOrder_deformations_basis_count : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t), ∃ f : Fin (D.a * (D.n - 1)) → (HdR o₀.A →ₗ[k] HdR o₀.A), (∀ j, ∃ (o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t)) (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), ∀ x ∈ Fil o₀.A, IsFilLift m'.cart x (f j x)) ∧ ∀ (o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t)) (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), ∃! c : Fin (D.a * (D.n - 1)) → k, ∀ x ∈ Fil o₀.A, IsFilLift m'.cart x (∑ j, c j • f j x) := by
  first | (exact @GlobalTheory.HTCount.count) | (exact GlobalTheory.HTCount.count) | (intros; apply GlobalTheory.HTCount.count  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem GlobalTheory.UPel.HT.obj_lift_sqZero : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (A₁ A₀ : Type) [CommRing A₁] [CommRing A₀] [IsLocalRing A₁] [IsArtinianRing A₁] (π : A₁ →+* A₀) (β : R →+* A₁), Function.Surjective π → RingHom.ker π * RingHom.ker π = ⊥ → ∀ o : Obj b N (spMap (π.comp β)), ∃ o' : Obj b N (spMap β), Nonempty (ObjMap o o' (spMap π)) := by
  intro p _ D R _ b N _ hN A₁ A₀ _ _ _ _ π β hπ hk o
  have hc : spMap (π.comp β) = spMap π ≫ spMap β := by
    simp only [spMap, Sp, CommRingCat.ofHom_comp, Spec.map_comp]
  have hk2 : RingHom.ker π ^ 2 = ⊥ := by rw [pow_two]; exact hk
  revert o
  rw [hc]
  intro o
  first
  | exact GlobalTheory.T.harrisTaylor_exists_lift_squareZero_artinian p D R b N hN A₁ A₀ π hπ hk2 (spMap β) o
  | exact GlobalTheory.T.harrisTaylor_exists_lift_squareZero_artinian p D R b N A₁ A₀ π hπ hk2 (spMap β) o
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT

theorem Model.isProjOver_of_compactB (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R]
    [IsDomain R] [CharZero R] [IsNoetherianRing R] (b : Base D R) (N : ℕ) (_hN : 3 ≤ N) (_hNp : N.Coprime p)
    (hD : D.CompactB) (M : Model b N) : IsProjOver M.s :=
  GlobalTheory.UPel.isProjOver_of_isQProjOver_of_isProper R M.X M.s M.qproj
    (GlobalTheory.T.harrisTaylor_integralModel_isProper_of_compact p D R b N M hD)

end GlobalTheory.UPel.HT
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

namespace GlobalTheory.PairStep

theorem exists_lcCut_induction : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
    (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → 1 ≤ n →
    letI := algebraΓOfHom p;
    ∀ (Δ : X → ℚ) (r : ℕ) (N₀ : LB X) (x : X) (c : ℕ → ℝ),
      IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < r → N₀.IsLB → IsNef ℂ N₀ → IsBig ℂ N₀ →
      IsClosed ({x} : Set X) → (∀ e ∈ Finset.Icc 1 n, 0 < c e) →
      (∀ (Z : Closeds X) (e : ℕ), IsIrreducible (Z : Set X) → x ∈ Z → 1 ≤ e →
        topologicalKrullDim (Z : Set X) = e →
        c e ^ e < (interNumRed ℂ Z fun _ : Fin e => N₀ : ℝ) / (r : ℝ) ^ e) →
      ∃ A : CartierDiv X, IsAmpleLB (toLB A) ∧ ∀ j, j < n → ∃ (j' : ℕ) (lam μ : ℚ) (m' : ℕ) (D₀ : CartierDiv X),
        j' ≤ j ∧ 0 < m' ∧ D₀.Eff ∧ 0 < μ ∧ (lam : ℝ) < ∑ e ∈ Finset.Icc (j' + 1) n, (e : ℝ) / c e ∧
        (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![toLB D₀] : ℚ) / m' =
          lam * interNumRed ℂ C ![N₀] / r - μ * interNumRed ℂ C ![toLB A]) ∧
        LcCut p n (Δ + qWeil D₀ m') x j' := by
  intro hPr X _ _ _ p n hP hn hn1
  letI := algebraΓOfHom p
  intro Δ r N₀ x c hΔ hklt hr hN₀ hnef hbig hx hc hZ
  obtain ⟨m, G, hm, hG⟩ := GlobalTheory.T.exists_logCanonicalMultiple_of_globally_klt X p n hP hn Δ hΔ hklt
  have hcpos : ∀ e, 1 ≤ e → e ≤ n → 0 < c e := fun e h1 h2 => hc e (Finset.mem_Icc.2 ⟨h1, h2⟩)
  have hgen : closure ({genericPoint X} : Set X) = Set.univ := (genericPoint_spec X).def
  have hdimX : topologicalKrullDim (closure ({genericPoint X} : Set X)) = n := by
    rw [hgen, ← hn]
    exact ((Homeomorph.Set.univ X).isHomeomorph).topologicalKrullDim_eq
  have hcn := hZ (Closeds.closure ({genericPoint X} : Set X)) n isIrreducible_singleton.closure
    (by simpa using specializes_iff_mem_closure.1 (genericPoint_specializes x)) hn1 hdimX
  obtain ⟨c', hc'v, hc'gt⟩ : ∃ c' : ℝ, c' ^ n < (interNumRed ℂ (Closeds.closure ({genericPoint X} : Set X))
      (fun _ : Fin n => N₀) : ℝ) / (r : ℝ) ^ n ∧ c n < c' := by
    have hev := ((continuous_pow n).tendsto (c n)).eventually_lt_const hcn
    exact ((hev.filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : Set.Ioi (c n) ∈ nhdsWithin (c n) (Set.Ioi (c n)))).exists
  have hcn0 := hcpos n hn1 le_rfl
  have hc'0 : 0 < c' := hcn0.trans hc'gt
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hlt : (n : ℝ) / c' < n / c n := div_lt_div_of_pos_left hnpos hcn0 hc'gt
  obtain ⟨β, hβ0, hβ⟩ := exists_rat_btwn (sub_pos.2 hlt)
  have hβ0' : (0 : ℚ) < β := by exact_mod_cast hβ0
  obtain ⟨A, F, a, hA, ha, hF, lam₀, μ₀, m₀, D₀, hm₀, hD₀, hμ₀, hlam₀, hnum₀, hklt₀⟩ :=
    GlobalTheory.T.exists_ample_effective_klt_inductionStart hPr X p n hP hn Δ r N₀ hN₀ β hΔ hklt hr hnef hbig hβ0'
  refine ⟨A, hA, ?_⟩
  have key : ∀ a : WithBot ℕ∞, ∀ j : ℕ, (j : WithBot ℕ∞) < a → a ≤ ((j + 1 : ℕ) : WithBot ℕ∞) →
      a = ((j + 1 : ℕ) : WithBot ℕ∞) := by
    intro a j h1 h2
    induction a using WithBot.recBotCoe with
    | bot => simp at h1
    | coe a =>
      induction a using ENat.recTopCoe with
      | top =>
        exfalso
        have h3 : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ (((j + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := h2
        exact absurd (WithBot.coe_le_coe.1 h3) (by simp)
      | coe k =>
        have h1' : j < k := by exact_mod_cast h1
        have h2' : k ≤ j + 1 := by exact_mod_cast h2
        have : k = j + 1 := by omega
        subst this; rfl
  have hsplit : ∀ j, j + 1 ≤ n → ∑ e ∈ Finset.Icc (j + 1) n, (e : ℝ) / c e =
      (j + 1 : ℕ) / c (j + 1) + ∑ e ∈ Finset.Icc (j + 2) n, (e : ℝ) / c e := by
    intro j hj
    rw [← Finset.insert_Icc_add_one_left_eq_Icc hj, Finset.sum_insert (by simp)]
    first | rfl | (push_cast; ring_nf) | simp [add_assoc]
  let S : ℕ → Prop := fun j => ∃ (j' : ℕ) (lam μ : ℚ) (m' : ℕ) (D₀ : CartierDiv X),
        j' ≤ j ∧ 0 < m' ∧ D₀.Eff ∧ 0 < μ ∧ (lam : ℝ) < ∑ e ∈ Finset.Icc (j' + 1) n, (e : ℝ) / c e ∧
        (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![toLB D₀] : ℚ) / m' =
          lam * interNumRed ℂ C ![N₀] / r - μ * interNumRed ℂ C ![toLB A]) ∧
        LcCut p n (Δ + qWeil D₀ m') x j'
  have first : S (n - 1) := by
    obtain ⟨lam₁, μ₁, m₁, D₁, hm₁, hD₁, hμ₁, hlam₁, hnum₁, hcut₁⟩ :=
      GlobalTheory.T.angehrnSiu_cut_lower_centre_dimension hPr X p n hP hn Δ m G r N₀ hN₀ A F a x (genericPoint X) n c' lam₀ μ₀ m₀ D₀ hΔ hklt hm hG hr
        hnef hA ha hF hx (genericPoint_specializes x) hn1 hdimX (Or.inl rfl) hc'0 hc'v hm₀ hD₀ hμ₀
        hnum₀ (hklt₀ x).lcAt
    refine ⟨n - 1, lam₁, μ₁, m₁, D₁, le_rfl, hm₁, hD₁, hμ₁, ?_, hnum₁, hcut₁⟩
    rw [Nat.sub_add_cancel hn1, Finset.Icc_self, Finset.sum_singleton]
    have : (lam₀ : ℝ) < β := by exact_mod_cast hlam₀
    linarith
  have step : ∀ j, j + 1 < n → S (j + 1) → S j := by
    intro j hj ⟨j', lam, μ, m', D₁, hj', hm', hD₁, hμ, hlam, hnum, hcut⟩
    by_cases hle : j' ≤ j
    · exact ⟨j', lam, μ, m', D₁, hle, hm', hD₁, hμ, hlam, hnum, hcut⟩
    obtain rfl : j' = j + 1 := by omega
    have hsj := hsplit j (by omega)
    have hcj := hcpos (j + 1) (by omega) (by omega)
    have hpos : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) / c (j + 1) := div_pos (by positivity) hcj
    obtain ⟨hlc, hnk, hdim⟩ := hcut
    by_cases hall : ∀ z, z ⤳ x → ¬ KltAt p n (Δ + qWeil D₁ m') z →
        topologicalKrullDim (closure ({z} : Set X)) ≤ j
    · refine ⟨j, lam, μ, m', D₁, le_rfl, hm', hD₁, hμ, ?_, hnum, hlc, hnk, hall⟩
      rw [hsj]; linarith
    push_neg at hall
    obtain ⟨z, hzx, hzk, hzd⟩ := hall
    have hq : IsQCart (qWeil D₁ m') := ⟨m', D₁, hm', hD₁, rfl⟩
    obtain ⟨w, hwz, hw⟩ := GlobalTheory.T.exists_nonKltCentre_of_not_klt_after_adding X p n hP hn Δ (qWeil D₁ m') z hq (hklt z) hzk
    have hwx : w ⤳ x := hwz.trans hzx
    have hwk : ¬ KltAt p n (Δ + qWeil D₁ m') w :=
      GlobalTheory.PairStep.not_kltAt_of_isNkltCentre X p n hP hn _ w w hw specializes_rfl
    have hsub : closure ({z} : Set X) ⊆ closure ({w} : Set X) := specializes_iff_closure_subset.1 hwz
    have hmono : topologicalKrullDim (closure ({z} : Set X)) ≤ topologicalKrullDim (closure ({w} : Set X)) :=
      (Topology.IsEmbedding.inclusion hsub).isInducing.topologicalKrullDim_le
    have hwd : topologicalKrullDim (closure ({w} : Set X)) = ((j + 1 : ℕ) : WithBot ℕ∞) :=
      key _ j (hzd.trans_le hmono) (hdim w hwx hwk)
    have hZw := hZ (Closeds.closure ({w} : Set X)) (j + 1) isIrreducible_singleton.closure
      (by simpa using specializes_iff_mem_closure.1 hwx) (by omega) hwd
    obtain ⟨lam', μ', m'', D₂, hm'', hD₂, hμ', hlam', hnum', hcut'⟩ :=
      GlobalTheory.T.angehrnSiu_cut_lower_centre_dimension hPr X p n hP hn Δ m G r N₀ hN₀ A F a x w (j + 1) (c (j + 1)) lam μ m' D₁ hΔ hklt hm hG hr
        hnef hA ha hF hx hwx (by omega) hwd (Or.inr hw) hcj hZw hm' hD₁ hμ hnum hlc
    refine ⟨j, lam', μ', m'', D₂, le_rfl, hm'', hD₂, hμ', ?_, hnum', by simpa using hcut'⟩
    rw [hsj]
    push_cast at hlam' ⊢
    linarith
  have hall : ∀ i, i < n → S (n - 1 - i) := by
    intro i
    induction i with
    | zero => intro _; simpa using first
    | succ i ih =>
      intro hi
      have h := ih (by omega)
      rw [show n - 1 - i = (n - 1 - (i + 1)) + 1 by omega] at h
      exact step _ (by omega) h
  intro j hj
  have h := hall (n - 1 - j) (by omega)
  rwa [show n - 1 - (n - 1 - j) = j by omega] at h

end GlobalTheory.PairStep
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

namespace GlobalTheory.PairStep

theorem topologicalKrullDim_closure_closedPt_le_zero {X : Scheme.{0}} {x : X}
    (hx : IsClosed ({x} : Set X)) : topologicalKrullDim (closure ({x} : Set X)) ≤ 0 := by
  have hsing : ∀ a b : closure ({x} : Set X), a = b := by
    intro a b
    apply Subtype.ext
    have ha : (a : X) = x := Set.mem_singleton_iff.mp (hx.closure_subset a.2)
    have hb : (b : X) = x := Set.mem_singleton_iff.mp (hx.closure_subset b.2)
    rw [ha, hb]
  have hirr : ∀ s t : IrreducibleCloseds (closure ({x} : Set X)), s = t := by
    intro s t
    apply SetLike.ext
    intro a
    obtain ⟨b, hb⟩ := s.isIrreducible.nonempty
    obtain ⟨c, hc⟩ := t.isIrreducible.nonempty
    constructor
    · intro _
      rw [hsing a c]
      exact hc
    · intro _
      rw [hsing a b]
      exact hb
  unfold topologicalKrullDim
  rw [Order.krullDim_nonpos_iff_forall_isMax]
  intro s t _
  rw [hirr t s]

theorem eq_of_closedPt_specializes {X : Scheme.{0}} {x y : X} (hx : IsClosed ({x} : Set X))
    (h : x ⤳ y) : y = x := by
  exact Set.mem_singleton_iff.mp (hx.closure_subset (specializes_iff_mem_closure.mp h))

private lemma two_mul_lt_pow_mul_of_le (a t t' c : ℚ) (k : ℕ) (ha : 0 ≤ a) (ht : 0 < t) (htt : t ≤ t')
    (h : 2 * a < t ^ k * c) : 2 * a < t' ^ k * c ∧ a < t' ^ k * c := by
  have htk : 0 < t ^ k := pow_pos ht k
  have hc : 0 < c := by
    by_contra hc
    push_neg at hc
    have : t ^ k * c ≤ 0 := mul_nonpos_of_nonneg_of_nonpos htk.le hc
    linarith
  have hpow : t ^ k ≤ t' ^ k := by
    first
    | exact pow_le_pow_left ht.le htt k
    | exact pow_le_pow_left₀ ht.le htt k
  have : t ^ k * c ≤ t' ^ k * c := mul_le_mul_of_nonneg_right hpow hc.le
  constructor <;> linarith

theorem twoPoint_step : GlobalTheory.Published.Principalisation → GlobalTheory.Published.NadelVanishingPair → GlobalTheory.Published.NefNumerics → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → letI := algebraΓOfHom p; ∀ (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (N : LB X) (D : X → ℚ) (d ε : ℚ) (h : ℕ → ℚ) (x x' : X) (j : ℕ), IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < m → IsLogCanonicalMultiple p n Δ m G → IsAmpleLB N → IsClosed ({x} : Set X) → IsClosed ({x'} : Set X) → x ≠ x' → (∀ e, 0 < h e) → (∀ (z : X) (e : ℕ), z ⤳ x ∨ z ⤳ x' → 1 ≤ e → topologicalKrullDim (closure ({z} : Set X)) = e → 2 * (e : ℚ) ^ e < h e ^ e * (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N : ℤ)) → 0 < ε → QNum p N d D → 0 ≤ d → LcCut p n (Δ + D) x j → ¬ KltAt p n (Δ + D) x' → LcCut p n (Δ + D) x 0 ∨ ∃ (i : ℕ) (D' : X → ℚ) (d' : ℚ), i < j ∧ 0 ≤ d' ∧ d' ≤ d + (h (i + 1) + ε) ∧ QNum p N d' D' ∧ ((LcCut p n (Δ + D') x i ∧ ¬ KltAt p n (Δ + D') x') ∨ (LcCut p n (Δ + D') x' i ∧ ¬ KltAt p n (Δ + D') x)) := by
  intro hP hNV hNef X _ _ _ p n hp hn Δ m G N D d ε h x x' j hΔ hklt hm hG hN hx hx' hxx' hpos hbig
    hε hD hd hcut hnk
  obtain ⟨hlcx, hnkx, hdim⟩ := hcut
  by_cases h0 : LcCut p n (Δ + D) x 0
  · exact Or.inl h0
  right

  have hex : ∃ z, z ⤳ x ∧ ¬ KltAt p n (Δ + D) z ∧
      ¬ topologicalKrullDim (closure ({z} : Set X)) ≤ 0 := by
    by_contra hne
    push_neg at hne
    apply h0
    unfold LcCut
    refine ⟨hlcx, hnkx, fun z hz hkz => ?_⟩
    have := hne z hz hkz
    simpa using this
  obtain ⟨z, hzx, hkz, hz0⟩ := hex
  have hzne : z ≠ x := by
    rintro rfl
    exact hz0 (topologicalKrullDim_closure_closedPt_le_zero hx)
  have hDq : IsQCart D := hD.isQCart

  obtain ⟨w, hwz, hw⟩ := GlobalTheory.T.exists_nonKltCentre_of_not_klt_after_adding X p n hp hn Δ D z hDq (hklt z) hkz
  have hwx : w ⤳ x := hwz.trans hzx
  have hwne : w ≠ x := by
    rintro rfl
    exact hzne (eq_of_closedPt_specializes hx hwz)
  obtain ⟨e, -, hdw, he1⟩ := GlobalTheory.T.exists_topologicalKrullDim_closure_point_le X n w hn
  have he1' : 1 ≤ e := he1 x hwx hwne.symm
  have hkw : ¬ KltAt p n (Δ + D) w :=
    not_kltAt_of_isNkltCentre X p n hp hn (Δ + D) w w hw (specializes_refl w)
  have hej : e ≤ j := by
    have hle := hdim w hwx hkw
    rw [hdw] at hle
    exact_mod_cast hle
  obtain ⟨i, rfl⟩ : ∃ i, e = i + 1 := ⟨e - 1, by omega⟩
  have hwN := hbig w (i + 1) (Or.inl hwx) he1' hdw
  by_cases hlx' : LcAt p n (Δ + D) x'
  ·
    obtain ⟨w', hw'x', hw'⟩ := GlobalTheory.T.exists_nonKltCentre_of_not_klt_after_adding X p n hp hn Δ D x' hDq (hklt x') hnk
    by_cases hw'x : w' ⤳ x
    ·
      have hkw' : ¬ KltAt p n (Δ + D) w' :=
        not_kltAt_of_isNkltCentre X p n hp hn (Δ + D) w' w' hw' (specializes_refl w')
      obtain ⟨e', -, hdw', he1''⟩ := GlobalTheory.T.exists_topologicalKrullDim_closure_point_le X n w' hn
      have h1e' : 1 ≤ e' := by
        by_cases hxw : x = w'
        · refine he1'' x' hw'x' ?_
          intro h2
          exact hxx' (hxw.trans h2.symm)
        · exact he1'' x hw'x hxw
      have he'j : e' ≤ j := by
        have hle := hdim w' hw'x hkw'
        rw [hdw'] at hle
        exact_mod_cast hle
      obtain ⟨i', rfl⟩ : ∃ i', e' = i' + 1 := ⟨e' - 1, by omega⟩
      have hw'N := hbig w' (i' + 1) (Or.inl hw'x) h1e' hdw'
      have hnum := two_mul_lt_pow_mul_of_le _ (h (i' + 1)) (h (i' + 1) + ε) _ (i' + 1) (by positivity)
        (hpos _) (by linarith) hw'N
      obtain ⟨D', d', hd'0, hd'le, hD', hfin⟩ := GlobalTheory.T.lc_cut_two_closed_points_one_centre hP hNV hNef X p n hp hn Δ m G N D d
        (h (i' + 1) + ε) x x' w' i' hΔ hklt hm hG hN hD hd hx hx' hlcx hlx' hw'x hw'x' (Or.inr hw')
        hdw' (by linarith [hpos (i' + 1)]) hnum.1
      exact ⟨i', D', d', by omega, hd'0, hd'le, hD', hfin⟩
    ·
      obtain ⟨b, A, hb0, hbε, hA, hAx, hAw'⟩ := GlobalTheory.T.exists_small_ample_through_off' X p hp N x w' ε hN hw'x hε
      have hAq : IsQCart A := hA.isQCart
      have hsum : Δ + D + (1 : ℚ) • A = Δ + (D + A) := by
        rw [one_smul, add_assoc]
      have hoff := off_add_smul X p n (Δ + D) A 1 x hAx
      rw [hsum] at hoff
      obtain ⟨hkltiff, hlciff, -, hoffz⟩ := hoff
      have hcut' : LcCut p n (Δ + (D + A)) x j := by
        unfold LcCut
        refine ⟨hlciff.mpr hlcx, fun hk => hnkx (hkltiff.mp hk), fun y hy hky => ?_⟩
        have h2 := (off_add_smul X p n (Δ + D) A 1 y (hoffz y hy)).1
        rw [hsum] at h2
        exact hdim y hy (fun hk => hky (h2.mpr hk))
      have hw2 : IsNkltCentre p n (Δ + (D + A)) w := by
        have h3 := (off_add_smul X p n (Δ + D) A 1 w (hoffz w hwx)).2.2.1
        rw [hsum] at h3
        exact h3.mpr hw
      have hnlc : ¬ LcAt p n (Δ + (D + A)) x' := by
        have h4 := GlobalTheory.T.not_lcAt_add_of_isNkltCentre' X p n hp hn (Δ + D) A w' x' hw' hAq hAw' hw'x'
        rw [add_assoc] at h4
        exact h4
      have hDA : QNum p N (d + b) (D + A) := qNum_add X p hp N d b D A hD hA
      have hnum := two_mul_lt_pow_mul_of_le _ (h (i + 1)) (h (i + 1) + ε - b) _ (i + 1) (by positivity)
        (hpos _) (by linarith) hwN
      obtain ⟨hlcx2, -, -⟩ := hcut'
      obtain ⟨D', d', hd'0, hd'le, hD', hcutD', hnkD'⟩ := GlobalTheory.T.exists_lc_cut_point_of_not_lc_other hP hNV hNef X p n hp hn Δ m G
        N (D + A) (d + b) (h (i + 1) + ε - b) x x' w i hΔ hklt hm hG hN hDA (by linarith) hx hlcx2
        hnlc hwx hw2 hdw (by linarith [hpos (i + 1)]) hnum.2
      exact ⟨i, D', d', by omega, hd'0, by linarith, hD', Or.inl ⟨hcutD', hnkD'⟩⟩
  ·
    have hnum := two_mul_lt_pow_mul_of_le _ (h (i + 1)) (h (i + 1) + ε) _ (i + 1) (by positivity)
      (hpos _) (by linarith) hwN
    obtain ⟨D', d', hd'0, hd'le, hD', hcutD', hnkD'⟩ := GlobalTheory.T.exists_lc_cut_point_of_not_lc_other hP hNV hNef X p n hp hn Δ m G
      N D d (h (i + 1) + ε) x x' w i hΔ hklt hm hG hN hD hd hx hlcx hlx' hwx hw hdw
      (by linarith [hpos (i + 1)]) hnum.2
    exact ⟨i, D', d', by omega, hd'0, hd'le, hD', Or.inl ⟨hcutD', hnkD'⟩⟩

end GlobalTheory.PairStep
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.nonempty_labelled_cover_of_odd_prime : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : UCover R) (lab : Labels D.toPre C.A), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → OneTrait D.toPre C.A lab → GalEqN n lab → Nonempty (LabCover D) := by
  first | exact @GlobalTheory.Mum.UCover.labCover | exact GlobalTheory.Mum.UCover.labCover | (intros; apply GlobalTheory.Mum.UCover.labCover <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_fourierTermSystem_regular_traits_given_chart : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ Q.X), Module.finrank ℤ Q.X ≤ g → (∀ k, t k ∈ maximalIdeal V ∧ t k ≠ 0) → (∀ k a b, δ k a b = δ k b a) → (∀ k a, 0 ≤ δ k a a) → (∀ a, a ≠ 0 → ∃ k, 0 < δ k a a) → Q.IsMonomialTau t δ → ∀ ξ : Sp V ⟶ Z, UnifOver F i ξ Q → ∀ l : ℕ, l.Prime → l ∣ n → ∀ j₀ : ℕ, ∃ (j : ℕ) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (Φ : VSys (id : ℤ → ℤ) g W ((l ^ j) ^ 2) (X₁.M.Z.presheaf.stalk z₁)) (y : Φ.Y) (ρ : V →+* Φ.V y) (e : Φ.X y ≃+ Q.X) (h : Fin (Φ.m y) ≃ Fin m), j₀ ≤ j ∧ HasTraitsR X₁ z₁ Φ.pre ∧ IsChartMember X₁ z₁ Φ Q ξ t δ y ρ e h := by
  first | exact @GlobalTheory.Poinc.Sep.exists_chartMember_traitsR | exact GlobalTheory.Poinc.Sep.exists_chartMember_traitsR | (intros; apply GlobalTheory.Poinc.Sep.exists_chartMember_traitsR <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

theorem _root_.GlobalTheory.T.unitary_fourierClassSums_deeper_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (Φ : FPre (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) p (X₁.M.Z.presheaf.stalk z₁)), (∀ y, ∃ t : UCTrait X₁ p z₁, (∀ a, Φ.ev y a = t.val a) ∧ ∃ e : Φ.X y ≃ₗ[𝓞 E] t.T.P.D.toPre.X, ∀ a b, Φ.sc y * Φ.β y a b = t.sc * t.T.be (e a) (e b)) → ∀ (y₀ : Φ.Y) (N₀ : ℕ), ∃ N, N₀ ≤ N ∧ (X₁.S.r * X₁.S.N) ∣ N ∧ ∃ (k : ∀ y, Φ.X y₀ →ₗ[ℤ] Φ.X y) (Q : Type) (t : ∀ y, (Fin 1 → Φ.X y) → Q → PadicAlgCl p) (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : Algebra (X₁.M.Z.presheaf.stalk z₁) B) (_ : Module.Finite (X₁.M.Z.presheaf.stalk z₁) B) (_ : Finite (B ≃ₐ[X₁.M.Z.presheaf.stalk z₁] B)) (𝔷 : Ideal B), Function.Injective (algebraMap (X₁.M.Z.presheaf.stalk z₁) B) ∧ (∀ b : B, (∀ σ : B ≃ₐ[X₁.M.Z.presheaf.stalk z₁] B, σ b = b) → b ∈ Set.range (algebraMap (X₁.M.Z.presheaf.stalk z₁) B)) ∧ 𝔷.IsMaximal ∧ k y₀ = LinearMap.id ∧ (∀ y, IsUnimodMod (𝓞 E) N (k y)) ∧ Φ.IsTerms !![(1 : ℤ)] t ∧ Φ.ClassSums (X₁.S.r * X₁.S.N) N y₀ k t B 𝔷 := by
  first | exact @GlobalTheory.UPoinc.uclassSums_deeper | exact GlobalTheory.UPoinc.uclassSums_deeper | (intros; apply GlobalTheory.UPoinc.uclassSums_deeper <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UPoinc

theorem uMinSt_holds : UMinSt := GlobalTheory.T.unitary_integral_compactification_exists_via_theta

end GlobalTheory.UPoinc
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_kodairaSpencer_regular_framed_affine : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → (∀ x ∈ genBd Y, IsClosed ({x} : Set (gen Y)) → HasRigidChart Y x) → ∀ (U : Y.X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → (∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left)) → ∀ D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U, ∃ Θ, IsKS Y.t (interior Y) U v D.1 Θ := by
  first | exact @GlobalTheory.KReg.exists_isKS_regular | exact GlobalTheory.KReg.exists_isKS_regular | (intros; apply GlobalTheory.KReg.exists_isKS_regular <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.logKodairaSpencer_injective_mod_maximal_boundary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → (∀ x ∈ genBd Y, IsClosed ({x} : Set (gen Y)) → HasRigidChart Y x) → ∀ (U : Y.X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → (∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left)) → ∀ (D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) (Θ : Matrix (Fin n) (Fin n) Γ(Y.X, U.1)) (m : Ideal Γ(Y.X, U.1)), m.IsMaximal → (∃ x, x ∉ interior Y ∧ x ∈ U.1 ∧ ∀ f ∈ m, x ∉ Y.X.basicOpen f) → IsKS Y.t (interior Y) U v D.1 Θ → (∀ a b, Θ a b ∈ m) → D ∈ m • (⊤ : Submodule Γ(Y.X, U.1) (logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U)) := by
  first | exact @GlobalTheory.ChartDer.logKS_inj_mod_boundary | exact GlobalTheory.ChartDer.logKS_inj_mod_boundary | (intros; apply GlobalTheory.ChartDer.logKS_inj_mod_boundary <;> assumption)
end
