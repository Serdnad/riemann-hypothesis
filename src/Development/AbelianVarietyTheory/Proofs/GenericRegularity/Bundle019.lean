module

public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsUnitGramFrameBorelChange
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle017
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle004
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle016
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsPowSmulMemBall
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle018
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.Divisibility.WeightAlgebra
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg

theorem _root_.GlobalTheory.T.exists_unit_gram_frame_borel_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → (∀ k (x : (U.X k).dom), ∃ x' : (U.X k).dom, IsUnitFr (U.X k) x'.1 ∧ (∃ b ∈ FD.Bor (U.X k).Ψ r, x'.1 = FD.rmul x.1 b) ∧ (∃ t : Ix Dw → (CAt σ)ˣ, FrBor t (U.un k x') (U.un k x)) ∧ ∀ (la : FD.Wt (U.X k).Ψ r) (P : FD.Frame (U.X k).Ψ r → ℂ), (U.X k).IsSec la P → (U.X k).pnorm la P x.1 = ‖P x'.1‖) ∧ ∀ y : FrPt Xo c (CAt σ), ∃ (k : U.Comp) (x : (U.X k).dom) (t : Ix Dw → (CAt σ)ˣ), IsUnitFr (U.X k) x.1 ∧ FrBor t (U.un k x) y := by
  first | exact @GlobalTheory.FrameNorm.exists_unitFr_frBor | exact GlobalTheory.FrameNorm.exists_unitFr_frBor | (intros; apply GlobalTheory.FrameNorm.exists_unitFr_frBor <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.Reg

theorem adjoin_insert_union_image {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [DecidableEq Ω] (x : Ω)
    (G : Finset Ω) {m : ℕ} (r : Fin m → Ω) :
    Algebra.adjoin K (insert x ((G ∪ Finset.univ.image r : Finset Ω) : Set Ω)) =
      Algebra.adjoin K ((Algebra.adjoin K (insert x (G : Set Ω)) : Set Ω) ∪ Set.range r) := by
  apply le_antisymm
  · apply Algebra.adjoin_mono
    intro z hz
    rcases hz with rfl | hz
    · exact Or.inl (Algebra.subset_adjoin (Or.inl rfl))
    · rcases Finset.mem_union.1 hz with h | h
      · exact Or.inl (Algebra.subset_adjoin (Or.inr h))
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 h
        exact Or.inr ⟨i, rfl⟩
  · apply Algebra.adjoin_le
    rintro z (hz | ⟨i, rfl⟩)
    · refine Algebra.adjoin_mono ?_ hz
      apply Set.insert_subset_insert
      intro g hg
      exact Finset.mem_coe.2 (Finset.mem_union_left _ hg)
    · exact Algebra.subset_adjoin (Or.inr (Finset.mem_coe.2 (Finset.mem_union_right _
        (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩))))

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}


set_option maxHeartbeats 800000 in
theorem PChart.exists_refine (hL : EvLaws Xo c) {O : Type} [CommRing O] {β : O →+* c.F} (P : PChart Xo c β)
    {m : ℕ} (ws : Fin m → Rul Xo c)
    (hw : ∀ e (he : e ∈ P.es) i, ((evR Xo c (ws i) (P.y e he) : P.R e) : P.Ω) = evR Xo c (ws i) P.yg)
    (hspan : ∀ e (he : e ∈ P.es), Ideal.span (Set.range fun i => (evR Xo c (ws i) (P.y e he) : P.R e)) = ⊤)
    (k : Fin m) (hk : evR Xo c (ws k) P.yg ≠ 0) :
    ∃ P' : PChart Xo c β, P'.Fam ws ∧
      ∀ (L : Type) [Field L] [Algebra c.F L] (W : ValuationSubring L) (y : FrPt Xo c L)
        (e : P.Ω) (he : e ∈ P.es) (ψ : P.R e →ₐ[c.F] L) (z : FrPt Xo c L) (t : Ix Dw → Lˣ),
        (∀ g : P.R e, (g : P.Ω) ∈ P.gens → ψ g ∈ W) → FrMap ψ (P.y e he) z → FrBor t y z →
        ψ (evR Xo c (ws k) (P.y e he)) ≠ 0 →
        (∀ i, ψ (evR Xo c (ws i) (P.y e he)) / ψ (evR Xo c (ws k) (P.y e he)) ∈ W) → P'.Catches W y := by
  classical
  let G : Finset P.Ω := P.gens ∪ Finset.univ.image fun i => evR Xo c (ws i) P.yg / evR Xo c (ws k) P.yg
  have hG : (P.gens : Set P.Ω) ⊆ G := fun g hg => Finset.mem_coe.2 (Finset.mem_union_left _ hg)
  have hGr : ∀ i, evR Xo c (ws i) P.yg / evR Xo c (ws k) P.yg ∈ G := fun i =>
    Finset.mem_union_right _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)
  have hblow := fun e (he : e ∈ P.es) =>
    GlobalTheory.adjoin_ratios_of_span_eq_top c.F P.Ω (P.R e) m (fun i => evR Xo c (ws i) (P.y e he)) k (hspan e he)
      (by rw [hw e he k]; exact hk) (Algebra.adjoin c.F (insert e⁻¹ (G : Set P.Ω)))
      (by simp only [hw e he]; exact adjoin_insert_union_image _ _ _)
  choose hle hinv hsm hext using hblow
  have hy := fun e (he : e ∈ P.es) => hL.bc _ _ (Subalgebra.inclusion (hle e he)) (P.y e he)
  choose y' hy' using hy
  refine ⟨{ Ω := P.Ω
            gens := G
            frac := ?_
            es := P.es
            es_ne := P.es_ne
            es_mem := fun e he => ⟨(P.es_mem e he).1, ?_⟩
            sm := fun e he => hsm e he (P.sm e he)
            yg := P.yg
            y := y'
            gen := fun e he => frMap_cancel _ _ _ (Subalgebra.inclusion (hle e he)) _ (P.y e he) _ _ (hy' e he)
              (P.gen e he)
            int := ?_ }, ⟨k, hk, fun i => ?_, fun e he => ?_⟩, ?_⟩
  · rw [eq_top_iff, ← P.frac]
    exact Subfield.closure_mono (Set.union_subset_union_right _ hG)
  · exact Subring.closure_mono (Set.union_subset_union_right _ hG) (P.es_mem e he).2
  · intro e he T io
    letI := io.toAlgebra
    intro ψ h1 h2 z hz
    refine P.int e he T io (ψ.comp (Subalgebra.inclusion (hle e he))) h1 (fun g hg => ?_) z
      (frMap_trans _ _ _ _ _ _ _ _ (hy' e he) hz)
    exact h2 (Subalgebra.inclusion (hle e he) g) (hG hg)
  · exact Subring.subset_closure (Or.inr (hGr i))
  · have := hinv e he
    rw [hw e he k] at this
    exact this
  · intro L _ _ W y e he ψ z t h1 hz hb hψ hW
    obtain ⟨ψ', hc, hr⟩ := hext e he L ψ hψ
    refine ⟨e, he, ψ', z, t, fun g hg => ?_, ?_, hb⟩
    · rcases Finset.mem_union.1 hg with h | h
      · have e1 : g = Subalgebra.inclusion (hle e he) ⟨g, Algebra.subset_adjoin (Or.inr h)⟩ := Subtype.ext rfl
        have e2 := h1 ⟨g, Algebra.subset_adjoin (Or.inr h)⟩ h
        have e3 := DFunLike.congr_fun hc ⟨g, Algebra.subset_adjoin (Or.inr h)⟩
        rw [AlgHom.comp_apply] at e3
        have e4 := (congrArg ψ' e1).trans e3
        exact e4.symm ▸ e2
      · obtain ⟨i, -, hi⟩ := Finset.mem_image.1 h
        rw [← hw e he i, ← hw e he k] at hi
        have e1 := hr i (hi.symm ▸ g.2)
        have e2 : g = ⟨_, hi.symm ▸ g.2⟩ := Subtype.ext hi.symm
        have e4 := (congrArg ψ' e2).trans e1
        exact e4.symm ▸ hW i
    · refine frMap_cancel _ _ _ (Subalgebra.inclusion (hle e he)) ψ' (P.y e he) _ _ (hy' e he) ?_
      exact hc.symm ▸ hz

theorem exists_covers_fam : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → ∀ (O : Type) [CommRing O] (β : O →+* c.F) (J : Type) [Finite J] (P : J → PChart Xo c β), Covers P → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n m : ℕ) (ws : Fin m → Rul Xo c), (∀ i, ws i ∈ sec Xo c a n) → Formalism.L2.PjFree.NoCommonZero Xo c ws → ∃ (J' : Type) (_ : Finite J') (P' : J' → PChart Xo c β), Covers P' ∧ ∀ j, (P' j).Fam ws := by
  intro E _ _ _ H Dw l Xo c hL O _ β J _ P hP a n m ws hws hnc
  have hw : ∀ j e (he : e ∈ (P j).es) i,
      ((evR Xo c (ws i) ((P j).y e he) : (P j).R e) : (P j).Ω) = evR Xo c (ws i) (P j).yg := fun j e he i =>
    (GlobalTheory.T.naturalRule_value_baseChange_of_isReduced E H Dw l Xo c hL a n (ws i) (hws i) _ _ _ _ _ ((P j).gen e he)).symm
  have hspan : ∀ j e (he : e ∈ (P j).es),
      Ideal.span (Set.range fun i => (evR Xo c (ws i) ((P j).y e he) : (P j).R e)) = ⊤ := fun j e he =>
    GlobalTheory.T.span_eval_eq_top_of_noCommonZero_reduced E H Dw l Xo c hL a n m ws hws hnc _ _
  have h := fun p : {p : J × Fin m // evR Xo c (ws p.2) (P p.1).yg ≠ 0} =>
    PChart.exists_refine hL (P p.1.1) ws (hw p.1.1) (hspan p.1.1) p.1.2 p.2
  choose P' hF hC using h
  refine ⟨_, inferInstance, P', ?_, hF⟩
  intro L _ _ W hW y
  obtain ⟨j, e, he, ψ, z, t, h1, hz, hb⟩ := hP L W hW y
  have hex : ∃ i, ψ (evR Xo c (ws i) ((P j).y e he)) ≠ 0 := by
    by_contra hn
    push_neg at hn
    have hle : Ideal.span (Set.range fun i => (evR Xo c (ws i) ((P j).y e he) : (P j).R e)) ≤ RingHom.ker ψ := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact hn i
    rw [hspan j e he] at hle
    have h1 : ψ 1 = 0 := hle (Submodule.mem_top)
    rw [map_one] at h1
    exact one_ne_zero h1
  obtain ⟨i₀, hi₀⟩ := hex
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ
    (fun i => W.valuation (ψ (evR Xo c (ws i) ((P j).y e he)))) ⟨i₀, Finset.mem_univ _⟩
  have hk0 : ψ (evR Xo c (ws k) ((P j).y e he)) ≠ 0 := by
    intro h0
    have := hk i₀ (Finset.mem_univ _)
    simp only [h0, map_zero, le_zero_iff, map_eq_zero] at this
    exact hi₀ this
  have hk1 : evR Xo c (ws k) (P j).yg ≠ 0 := by
    intro h0
    rw [← hw j e he k] at h0
    apply hk0
    have h2 : (evR Xo c (ws k) ((P j).y e he) : (P j).R e) = 0 := Subtype.ext h0
    rw [h2, map_zero]
  refine ⟨⟨(j, k), hk1⟩, hC ⟨(j, k), hk1⟩ L W y e he ψ z t h1 hz hb hk0 fun i => ?_⟩
  rw [← W.valuation_le_one_iff, map_div₀]
  exact div_le_one_of_le₀ (hk i (Finset.mem_univ _)) zero_le'

end GlobalTheory.Reg
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj

namespace GlobalTheory.LocStructNak

variable {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing A] [Algebra O A]

theorem dvd_of_vL_le [∀ ζ : Pts O A, IsDVRAt ζ] (c b : ↥(As O A))
    (h : ∀ ζ : Pts O A, vL ζ c ≤ vL ζ b) : c ∣ b := by
  have h0 : ∀ ζ : Pts O A, algebraMap ↥(As O A) (Loc ζ) b ∈
      Ideal.map (algebraMap ↥(As O A) (Loc ζ)) (Ideal.span {c}) := by
    intro ζ
    have h1 := h ζ
    rw [vL_eq_addVal, vL_eq_addVal, IsDiscreteValuationRing.addVal_le_iff_dvd] at h1
    rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
    exact h1
  exact Ideal.mem_span_singleton.1 (Ideal.mem_of_localization_maximal (fun P hP => h0 ⟨P, hP⟩))


omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem exists_residue (C : Subalgebra O ↥(As O A)) (ζ : Pts O A) (b c d : ↥(As O A))
    (hc : c ∈ C) (hd : d ∈ C) (hd0 : d ∉ ζ.asIdeal) (h : d * b - c ∈ ζ.asIdeal) :
    ∃ c' ∈ C, b - c' ∈ ζ.asIdeal := by
  haveI : Algebra.IsIntegral ↥C ↥(As O A) := Algebra.IsIntegral.tower_top O
  haveI := ζ.isMaximal
  have hmax : (ζ.asIdeal.comap (algebraMap ↥C ↥(As O A))).IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal ζ.asIdeal
  obtain ⟨y, z, hz, hyz⟩ := hmax.exists_inv (x := ⟨d, hd⟩) (by simpa [Ideal.mem_comap] using hd0)
  have hz' : (z : ↥(As O A)) ∈ ζ.asIdeal := hz
  have hyz' : (y : ↥(As O A)) * d + z = 1 := congrArg Subtype.val hyz
  refine ⟨y * c, C.mul_mem y.2 hc, ?_⟩
  have e : b - y * c = y * (d * b - c) + b * z := by
    linear_combination (-b) * hyz'
  rw [e]
  exact ζ.asIdeal.add_mem (ζ.asIdeal.mul_mem_left _ h) (ζ.asIdeal.mul_mem_left _ hz')

theorem exists_approx [∀ ζ : Pts O A, IsDVRAt ζ] [Finite (Pts O A)] (C : Subalgebra O ↥(As O A))
    (hval : ∀ n : Pts O A → ℕ, ∃ c ∈ C, ∀ ζ, vL ζ c = (n ζ : ℕ∞))
    (hres : ∀ (ζ : Pts O A) (b : ↥(As O A)), ∃ c ∈ C, b - c ∈ ζ.asIdeal)
    (n : Pts O A → ℕ) (b : ↥(As O A)) : ∃ c ∈ C, ∀ ζ, (n ζ : ℕ∞) ≤ vL ζ (b - c) := by
  classical
  letI := Fintype.ofFinite (Pts O A)
  obtain ⟨N, hN⟩ : ∃ N, ∑ ζ, n ζ = N := ⟨_, rfl⟩
  induction N generalizing n with
  | zero =>
    refine ⟨0, C.zero_mem, fun ζ => ?_⟩
    rw [(Finset.sum_eq_zero_iff.1 hN) ζ (Finset.mem_univ _)]
    simp
  | succ N ih =>
    obtain ⟨ζ₀, -, h0⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ) (f := n)
      (by rw [hN]; omega)
    have hsum : ∑ ζ, Function.update n ζ₀ (n ζ₀ - 1) ζ = N := by
      rw [Finset.sum_update_of_mem (Finset.mem_univ _)]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ζ₀), ← Finset.sdiff_singleton_eq_erase] at hN
      omega
    obtain ⟨c₁, hc₁, h₁⟩ := ih _ hsum
    obtain ⟨c, hc, hv⟩ := hval (Function.update n ζ₀ (n ζ₀ - 1))
    obtain ⟨b', hb'⟩ := dvd_of_vL_le c (b - c₁) (fun ζ => by rw [hv]; exact h₁ ζ)
    obtain ⟨c', hc', hm⟩ := hres ζ₀ b'
    refine ⟨c₁ + c * c', C.add_mem hc₁ (C.mul_mem hc hc'), fun ζ => ?_⟩
    have e : b - (c₁ + c * c') = c * (b' - c') := by linear_combination hb'
    rw [e, vL_mul, hv]
    by_cases hζ : ζ = ζ₀
    · subst hζ
      have h1 : 1 ≤ vL ζ (b' - c') := by
        rw [Order.one_le_iff_ne_zero, Ne, vL_eq_zero_iff]
        exact not_not.2 hm
      rw [Function.update_self]
      calc (n ζ : ℕ∞) = ((n ζ - 1 : ℕ) : ℕ∞) + 1 := by
            have : n ζ = (n ζ - 1) + 1 := by omega
            conv_lhs => rw [this]
            push_cast
            rfl
        _ ≤ _ := add_le_add le_rfl h1
    · rw [Function.update_of_ne hζ]
      exact le_self_add

theorem as_le_of_val_of_residue (O A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing A] [Algebra O A] (ϖ : O) (hU : IsUnif A ϖ) [∀ ζ : Pts O A, IsDVRAt ζ] [Finite (Pts O A)]
    [Module.Finite O ↥(As O A)] (C : Subalgebra O A) (hC : C ≤ As O A)
    (hval : ∀ n : Pts O A → ℕ, ∃ c ∈ C, ∀ ζ, ord ϖ ζ c = (((n ζ : ℕ) : ℤ) : WithTop ℤ))
    (hres : ∀ (ζ : Pts O A), ∀ b ∈ As O A, ∃ c ∈ C, ∃ d ∈ C,
      ord ϖ ζ d = 0 ∧ 0 < ord ϖ ζ (d * b - c)) : As O A ≤ C := by
  set C' : Subalgebra O ↥(As O A) := C.comap (As O A).val with hC'
  have hinj : Function.Injective (ENat.map (Nat.cast : ℕ → ℤ)) :=
    (ENat.strictMono_map_iff.2 Nat.strictMono_cast).injective
  have hzero : ∀ (ζ : Pts O A) (a : ↥(As O A)), ord ϖ ζ (a : A) = 0 ↔ a ∉ ζ.asIdeal := by
    intro ζ a
    rw [ord_of_mem ζ hU a.2, ← vL_eq_zero_iff]
    constructor
    · intro h
      exact hinj h
    · intro h
      change (vL ζ a).map (Nat.cast : ℕ → ℤ) = 0
      rw [h]
      rfl
  have hval' : ∀ n : Pts O A → ℕ, ∃ c ∈ C', ∀ ζ, vL ζ c = (n ζ : ℕ∞) := by
    intro n
    obtain ⟨c, hc, h⟩ := hval n
    refine ⟨⟨c, hC hc⟩, hc, fun ζ => hinj ?_⟩
    rw [← ord_of_mem ζ hU (hC hc), h ζ, ENat.map_natCast]
  have hres' : ∀ (ζ : Pts O A) (b : ↥(As O A)), ∃ c ∈ C', b - c ∈ ζ.asIdeal := by
    intro ζ b
    obtain ⟨c, hc, d, hd, hd0, h⟩ := hres ζ b b.2
    refine exists_residue C' ζ b ⟨c, hC hc⟩ ⟨d, hC hd⟩ hc hd ((hzero ζ ⟨d, hC hd⟩).1 hd0) ?_
    by_contra hn
    exact h.ne' ((hzero ζ _).2 hn)
  have key : (⊤ : Submodule O ↥(As O A)) ≤ Subalgebra.toSubmodule C' := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal O)
      Module.Finite.fg_top (IsLocalRing.maximalIdeal_le_jacobson _) ?_
    intro b _
    obtain ⟨c, hc, h⟩ := exists_approx C' hval' hres' (ep ϖ) b
    obtain ⟨b', hb'⟩ := dvd_of_vL_le (algebraMap O ↥(As O A) ϖ) (b - c)
      (fun ζ => by rw [← coe_ep ζ hU]; exact h ζ)
    have e : b = c + ϖ • b' := by rw [Algebra.smul_def, ← hb']; ring
    rw [e]
    exact Submodule.add_mem_sup hc (Submodule.smul_mem_smul
      ((IsLocalRing.mem_maximalIdeal ϖ).2 hU.irreducible.not_isUnit) Submodule.mem_top)
  intro x hx
  exact key (Submodule.mem_top (x := (⟨x, hx⟩ : ↥(As O A))))

end GlobalTheory.LocStructNak
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory

theorem multiset_prod_mem_cuspForms {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (X : Data E r) (la : Wt X.Ψ r) {N : ℕ} (w : Fin N → Frame X.Ψ r → ℂ)
    (hw : ∀ i, w i ∈ X.SS la) (s : Multiset (Fin N)) (hs : s ≠ 0) :
    (s.map w).prod ∈ X.SS (s.card • la) := by
  induction s using Multiset.induction_on with
  | empty => exact absurd rfl hs
  | cons a s ih =>
    by_cases h0 : s = 0
    · subst h0
      simpa using hw a
    · have h := (siegelSpaceAlgebra_holds (E := E) r X (s.card • la) la 0).2.1 _ (ih h0) _ (hw a).1
      rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, succ_nsmul, mul_comm]
      exact h

theorem eval_isHomogeneous_mem_cuspForms :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r),
      ∀ (la : Wt X.Ψ r) (N d : ℕ) (w : Fin N → Frame X.Ψ r → ℂ) (p : MvPolynomial (Fin N) ℂ),
        (∀ i, w i ∈ X.SS la) → 0 < d → p.IsHomogeneous d →
        (fun x => MvPolynomial.eval (fun i => w i x) p) ∈ X.SS (d • la) := by
  intro E _ _ _ r X la N d w p hw hd hp
  obtain ⟨⟨h0, hadd, hsmul⟩, -⟩ := siegelSpaceAlgebra_holds (E := E) r X (d • la) (d • la) 0
  have hmon : ∀ m ∈ p.support, (m.toMultiset.map w).prod ∈ X.SS (d • la) := by
    intro m hm
    have hc : m.toMultiset.card = d := by
      rw [Finsupp.card_toMultiset]
      have := hp (MvPolynomial.mem_support_iff.1 hm)
      simpa [Finsupp.weight_apply, Finsupp.sum] using this
    have := multiset_prod_mem_cuspForms X la w hw m.toMultiset (by
      intro h; rw [h] at hc; simp at hc; omega)
    rwa [hc] at this
  have heq : (fun x => MvPolynomial.eval (fun i => w i x) p) =
      ∑ m ∈ p.support, p.coeff m • (m.toMultiset.map w).prod := by
    funext x
    rw [MvPolynomial.eval_eq, Finset.sum_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, Finsupp.toMultiset_map, Finsupp.prod_toMultiset,
      Finsupp.prod_mapDomain_index (by simp) (by intros; rw [pow_add])]
    simp [Finsupp.prod, Finset.prod_apply]
  rw [heq]
  exact Finset.sum_induction _ (fun P => P ∈ X.SS (d • la)) (fun a b ha hb => hadd a ha b hb) h0
    (fun m hm => hsmul _ _ (hmon m hm))

end GlobalTheory
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory

theorem bddSec_pow_succ_and_constTerm_pow_succ
    (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (hP : X.IsBddSec la P) (m : ℕ) :
    X.IsBddSec ((m + 1) • la) (P ^ (m + 1)) ∧ ∀ ξ, X.IsIso ξ → ∀ x ∈ X.dom,
      X.fj ((m + 1) • la) ξ 0 (P ^ (m + 1)) x = X.fj la ξ 0 P x ^ (m + 1) := by
  induction m with
  | zero =>
    simp only [zero_add, one_smul, pow_one]
    exact ⟨hP, fun _ _ _ _ => trivial⟩
  | succ m ih =>
    have h := bddSec_mul_and_constTerm_mul E r X ((m + 1) • la) la (P ^ (m + 1)) P ih.1 hP
    rw [succ_nsmul la (m + 1), pow_succ P (m + 1)]
    refine ⟨h.1, fun ξ hξ x hx => ?_⟩
    rw [h.2 ξ hξ x hx, ih.2 ξ hξ x hx, pow_succ _ (m + 1)]

theorem cuspForm_of_bddSec_of_pow_succ :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r),
      ∀ (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (m : ℕ), X.IsBddSec la P →
        P ^ (m + 1) ∈ X.SS ((m + 1) • la) → P ∈ X.SS la := by
  intro E _ _ _ r X la P m hP hpow
  refine ⟨hP, fun ξ hξ x hx => ?_⟩
  have h := (bddSec_pow_succ_and_constTerm_pow_succ E r X la P hP m).2 ξ hξ x hx
  rw [hpow.2 ξ hξ x hx] at h
  exact pow_eq_zero_iff (Nat.succ_ne_zero m) |>.1 h.symm

end GlobalTheory
end
