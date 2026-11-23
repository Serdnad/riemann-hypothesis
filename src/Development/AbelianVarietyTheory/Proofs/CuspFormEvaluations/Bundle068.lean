module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle007
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle028
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle036
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle002
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle060
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle066
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle067
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.DifferentiableOnDetHMat
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)

theorem hermForm_diagonal_eq (d z w : Fin g → ℂ) :
    hermForm (Matrix.diagonal d) z w = ∑ j, d j * z j * conj (w j) := by
  simp only [hermForm, dotProduct, mulVec_diagonal]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.star_apply, Complex.star_def]
  ring

theorem selfD_of_isSympl (hs : IsSympl X bas) : SelfD X X.Λ := by
  refine ⟨X.Λ_fg, fun x => ⟨fun hx y hy => ?_, fun h => ?_⟩⟩
  · obtain ⟨a, ha⟩ : ∃ a, (bas a : Fin r → E) = x := ⟨bas.symm ⟨x, hx⟩, by simp⟩
    obtain ⟨b, hb⟩ : ∃ b, (bas b : Fin r → E) = y := ⟨bas.symm ⟨y, hy⟩, by simp⟩
    refine ⟨-omegaStd a b, ?_⟩
    rw [← ha, ← hb, hs a b]
    push_cast
    rfl
  · have hint : ∀ c, ∃ n : ℤ, GlobalTheory.SW.crd X bas x c = n := by
      intro c
      cases c with
      | inl j =>
        obtain ⟨k, hk⟩ := h _ (bas (Pi.single (Sum.inr j) 1)).2
        have e := GlobalTheory.SW.EF_vecQ hs (GlobalTheory.SW.crd X bas x)
          (fun c => (((Pi.single (Sum.inr j) (1 : ℤ) : Fin g ⊕ Fin g → ℤ) c : ℤ) : ℚ))
        rw [GlobalTheory.SW.vecQ_intCast, GlobalTheory.SW.vecQ_crd, hk] at e
        simp [Pi.single_apply] at e
        exact ⟨-k, by push_cast; linarith⟩
      | inr j =>
        obtain ⟨k, hk⟩ := h _ (bas (Pi.single (Sum.inl j) 1)).2
        have e := GlobalTheory.SW.EF_vecQ hs (GlobalTheory.SW.crd X bas x)
          (fun c => (((Pi.single (Sum.inl j) (1 : ℤ) : Fin g ⊕ Fin g → ℤ) c : ℤ) : ℚ))
        rw [GlobalTheory.SW.vecQ_intCast, GlobalTheory.SW.vecQ_crd, hk] at e
        simp [Pi.single_apply] at e
        exact ⟨k, by linarith⟩
    choose n hn using hint
    have hx : x = (bas n : Fin r → E) := by
      rw [← GlobalTheory.SW.vecQ_crd X bas x, ← GlobalTheory.SW.vecQ_intCast]
      congr 1
      funext c
      exact hn c
    rw [hx]
    exact (bas n).2

theorem hx_ortho : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsSympl X bas → ∀ x ∈ X.dom, X.IsOrtho x → (∀ z z', hx X bas idx x z z' = ∑ j, ((X.c (idx j).1 : ℝ) : ℂ) * z j * conj (z' j)) ∧ (∀ u, (hx X bas idx x (pv X idx x u) (pv X idx x u)).re = ∑ τ : X.Ψ, X.c τ * X.maj x τ (Data.emb τ.1 u)) ∧ (∀ u ∈ X.Λ, u ≠ 0 → X.firstMinimumSq x ≤ (hx X bas idx x (pv X idx x u) (pv X idx x u)).re) ∧ IsUnitFr X x ∧ SelfD X X.Λ := by
  intro E _ _ _ r X g bas idx hs x hxd ho
  have hHm := GlobalTheory.ThFr.Hm_of_isOrtho idx hs ho
  have h1 : ∀ z z', hx X bas idx x z z' = ∑ j, ((X.c (idx j).1 : ℝ) : ℂ) * z j * conj (z' j) := by
    intro z z'
    rw [hx_eq_hermForm idx x z z', hHm, hermForm_diagonal_eq]
  have h2 : ∀ u, (hx X bas idx x (pv X idx x u) (pv X idx x u)).re =
      ∑ τ : X.Ψ, X.c τ * X.maj x τ (Data.emb τ.1 u) := by
    intro u
    rw [hx_eq_hermForm idx x, hHm]
    exact (congrArg Complex.re (GlobalTheory.ThFr.hermForm_diagonal_c_self idx hxd ho u)).trans
      (Complex.ofReal_re _)
  have h0 : ∀ z, 0 ≤ (hx X bas idx x z z).re := by
    intro z
    rw [h1, Complex.re_sum]
    refine Finset.sum_nonneg fun j _ => ?_
    have e : ((X.c (idx j).1 : ℝ) : ℂ) * z j * conj (z j) =
        ((X.c (idx j).1 * Complex.normSq (z j) : ℝ) : ℂ) := by
      rw [_root_.mul_assoc, Complex.mul_conj]
      push_cast
      ring
    rw [e, Complex.ofReal_re]
    exact mul_nonneg (GlobalTheory.ThFr.c_pos X _).le (Complex.normSq_nonneg _)
  refine ⟨h1, h2, ?_, ?_, selfD_of_isSympl hs⟩
  · intro u hu hne
    rw [h2]
    unfold Data.firstMinimumSq
    apply csInf_le
    · refine ⟨0, ?_⟩
      rintro t ⟨v, -, -, rfl⟩
      rw [← h2]
      exact h0 _
    · exact ⟨u, hu, hne, rfl⟩
  · unfold IsUnitFr
    intro τ i
    unfold dmin lminor
    rw [ho τ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal, norm_prod]
    refine Finset.prod_eq_one fun a _ => ?_
    simp only [Function.comp_apply, Complex.norm_real]
    unfold sgn
    split_ifs <;> simp

end GlobalTheory.Dict
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

namespace GlobalTheory.UpperRecord

theorem finrank_le_of_parts {Y ι : Type} {Z : ι → Type} (V : Submodule ℂ (Y → ℂ)) (e : Y ≃ Σ k, Z k)
    (d : ι → ℕ) (C δ : ℕ) (en : Fin δ ≃ Σ k, Fin (d k))
    (hb : ∀ (k : ι) (m : ℕ) (g : Fin m → V),
      LinearIndependent ℂ (fun q (z : Z k) => (g q).1 (e.symm ⟨k, z⟩)) → m ≤ d k * C) :
    Module.finrank ℂ V ≤ δ * C := by
  classical
  let ρ : ∀ k, V →ₗ[ℂ] (Z k → ℂ) := fun k =>
    (LinearMap.funLeft ℂ ℂ fun z : Z k => e.symm ⟨k, z⟩).comp V.subtype
  have hr : ∀ k, Module.rank ℂ (LinearMap.range (ρ k)) ≤ (d k * C : ℕ) := fun k => by
    refine rank_le fun s hs => ?_
    have hs' := (hs.comp s.equivFin.symm s.equivFin.symm.injective).map' (LinearMap.range (ρ k)).subtype
      (Submodule.ker_subtype _)
    choose g hg using fun q : Fin s.card => (s.equivFin.symm q).1.2
    refine hb k s.card g ?_
    have heq : (fun q (z : Z k) => (g q).1 (e.symm ⟨k, z⟩)) = _ := funext hg
    rw [heq]
    exact hs'
  have hfin : ∀ k, Module.Finite ℂ (LinearMap.range (ρ k)) := fun k =>
    Module.rank_lt_aleph0_iff.1 ((hr k).trans_lt (Cardinal.natCast_lt_aleph0))
  have hfr : ∀ k, Module.finrank ℂ (LinearMap.range (ρ k)) ≤ d k * C := fun k =>
    Module.finrank_le_of_rank_le (hr k)
  let s : Finset ι := Finset.univ.image fun q => (en q).1
  have hs : ∀ k, k ∉ s → d k = 0 := fun k hk => by
    by_contra h0
    exact hk (Finset.mem_image.2 ⟨en.symm ⟨k, ⟨0, Nat.pos_of_ne_zero h0⟩⟩, Finset.mem_univ _, by simp⟩)
  let Φ : V →ₗ[ℂ] (∀ k : s, LinearMap.range (ρ k)) := LinearMap.pi fun k => (ρ k).rangeRestrict
  have hΦ : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro g hg
    have hk : ∀ k, ρ k g = 0 := fun k => by
      by_cases hk : k ∈ s
      · exact congrArg Subtype.val (congrFun hg ⟨k, hk⟩)
      · have h0 : Module.finrank ℂ (LinearMap.range (ρ k)) = 0 := by
          have := hfr k
          rw [hs k hk] at this
          omega
        have := Submodule.finrank_eq_zero.1 h0
        exact (Submodule.eq_bot_iff _).1 this _ ⟨g, rfl⟩
    ext y
    have := congrFun (hk (e y).1) (e y).2
    simpa [ρ, LinearMap.funLeft_apply] using this
  have hsum : ∑ k : s, d k ≤ δ := by
    have hinj : Function.Injective fun p : Σ k : s, Fin (d k) => en.symm ⟨p.1.1, p.2⟩ := by
      rintro ⟨⟨k, hk⟩, a⟩ ⟨⟨k', hk'⟩, a'⟩ hp
      have := en.symm.injective hp
      obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.1 this
      obtain rfl := eq_of_heq h2
      rfl
    simpa using Fintype.card_le_of_injective _ hinj
  calc Module.finrank ℂ V ≤ Module.finrank ℂ (∀ k : s, LinearMap.range (ρ k)) :=
        LinearMap.finrank_le_finrank_of_injective hΦ
    _ = ∑ k : s, Module.finrank ℂ (LinearMap.range (ρ k)) := Module.finrank_pi_fintype ℂ
    _ ≤ ∑ k : s, d k * C := Finset.sum_le_sum fun k _ => hfr k
    _ = (∑ k : s, d k) * C := (Finset.sum_mul _ _ _).symm
    _ ≤ δ * C := Nat.mul_le_mul_right _ hsum

theorem upper : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j), IsRdgU h j hj n R e → ∀ (N : ℕ) (wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (c1 : ℝ) (A : ArchAt h j w wF Tn c1) (t : Idx D j N → ℂ) (Fl : FlatAt h j A t) (δ : ℕ) (xs : Fin δ → R.Y) (en : Fin δ ≃ Σ k : (T.U j T.σ₀).Comp, Fin (Fl.Fl k).δ), (∀ q, e (xs q) = ⟨(en q).1, ⟨(Fl.Fl (en q).1).xs (en q).2, (Fl.Fl (en q).1).xs_mem _⟩⟩) → Module.finrank ℂ (R.sp (addL wF wL Tn) Set.univ) ≤ δ * (Tn + 2 * WeightFamilies.dimY D j + 6).choose (WeightFamilies.dimY D j) := by
  intro D T h j hj n R e hR N wL wF w Tn c1 A t Fl δ xs en _
  refine finrank_le_of_parts _ e (fun k => (Fl.Fl k).δ) _ δ en fun k m g hg => ?_
  choose f hf hgf using fun q => (GlobalTheory.T.mem_span_cuspReadings_iff_components D T h j hj n R e hR (addL wF wL Tn)).1 (g q).1 (g q).2
  have hw := (GlobalTheory.T.componentModelWeight_dimension_dictionary D T h j hj k).2.2.1 wF wL Tn
  have := GlobalTheory.UpperModel.upper _ _ _ (A.Xa k) (Fl.Fl k) m (fun q => f q k) (fun q => by
    rw [A.hF, A.hL, A.hT, ← hw]
    exact (hf q k).1.1) (fun u hu => by
    funext q
    refine Fintype.linearIndependent_iff.1 hg u ?_ q
    funext z
    have := hu z.1 z.2
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← this]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hgf q, e.apply_symm_apply])
  rwa [A.hT, A.dim] at this

end GlobalTheory.UpperRecord
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

theorem _root_.GlobalTheory.T.exists_algIndependent_coeffs_flatDatum : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (N : ℕ) (wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (c1 : ℝ) (A : ArchAt h j w wF Tn c1), ∃ t : Idx D j N → ℂ, (∀ Q : MvPolynomial (Idx D j N) T.Q.c.F, Q ≠ 0 → MvPolynomial.eval₂ T.σ₀ t Q ≠ 0) ∧ Nonempty (FlatAt h j A t) := by
  first | exact @GlobalTheory.GenericFlat.exists_generic_flatAt | exact GlobalTheory.GenericFlat.exists_generic_flatAt | (intros; apply GlobalTheory.GenericFlat.exists_generic_flatAt <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

theorem _root_.GlobalTheory.T.sizePageRows_of_sizePageAt : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), FamilyHypotheses.HypPage large₂ X H C2 A2 CR CT ka wL wF Tn nP nW h0 → PageAt large₂ C2 A2 → 4 * H.CK ≤ WeightFamilies.PPv D large₂ C2 A2 ^ 2 * D.R.f → ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ ka ∧ 16 ≤ D.R.f := by
  first | exact @GlobalTheory.pageRows_of_pageAt | exact GlobalTheory.pageRows_of_pageAt | (intros; apply GlobalTheory.pageRows_of_pageAt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.familyUnif_index_eq_of_marked_latticeIsometry : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ U : FamilyUnif Xo σ ty, ∀ (i j : Fin U.n) (gam : (U.Di i).La ≃ₗ[𝓞 E] (U.Di j).La), (∀ a b, (U.Di j).EF (gam a) (gam b) = (U.Di i).EF a b) → (∀ a, ∃ e, gam (U.t i a) = U.t j a + l.M' • e) → i = j := by
  first | exact @GlobalTheory.UnifMatch.index_eq_of_isometry | exact GlobalTheory.UnifMatch.index_eq_of_isometry | (intros; apply GlobalTheory.UnifMatch.index_eq_of_isometry <;> assumption)
end
