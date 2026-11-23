module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1616
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1493
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1222
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1223
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1617
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle240
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1618
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1411
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1500
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.Bundle003
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle014
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1619
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1504
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1569
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
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
import Mathlib.SetTheory.ZFC.PSet
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

namespace GlobalTheory.HSNef

theorem le_of_rep : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (P : Pair p) (a b a' b' : ℤ) (M M' : HermLB p) (f : X.functionField), P.Rep a b M → P.Rep a' b' M' → f ≠ 0 → f ∈ P.Bl (a - a') (b - b') 1 → Le M' M := by
  intro k _ X _ p P a b a' b' M M' f hM hM' hf hB
  have hR : P.Rep (a - a') (b - b') (M.tens M'.dual) := by
    have h := Pair.rep_tens k X p P a b (-a') (-b') M M'.dual hM (Pair.rep_dual k X p P a' b' M' hM')
    simpa only [sub_eq_add_neg] using h
  obtain ⟨e, -, hrange, hnorm, hloc⟩ := RepDict.rep_dict k X p P _ _ _ hR
  have hfH : f ∈ (P.H (a - a') (b - b') : Set X.functionField) := hB.1
  rw [← hrange] at hfH
  obtain ⟨u, rfl⟩ := hfH
  refine (GlobalTheory.T.hermLBLeBySmallSection_iff_exists_smallSection_difference k X p M M').2 ⟨u, fun σ y => ?_, fun hu => ?_⟩
  · rw [← hnorm u σ y]
    have h0 : 0 ≤ P.nu (a - a') (b - b') σ y (e u) := by
      unfold Pair.nu; positivity
    exact pow_le_one₀ h0 (hB.2 σ y)
  · obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (P.L.isLB.cover.ge (Opens.mem_top (genericPoint X)))
    obtain ⟨j, hj⟩ := Opens.mem_iSup.1 (P.A.isLB.cover.ge (Opens.mem_top (genericPoint X)))
    have hne : P.loc (a - a') (b - b') (e u) i j ≠ 0 := by
      have h1 := (P.r i).ne_zero
      have h2 := (P.r' j).ne_zero
      simp only [Pair.loc]
      exact mul_ne_zero (mul_ne_zero hf (zpow_ne_zero _ h1)) (zpow_ne_zero _ h2)
    have hg := (hloc u (genericPoint X) i j hi hj).2 (unitAt_genericPoint hne)
    obtain ⟨c, hc⟩ := Opens.mem_iSup.1 ((M.tens M'.dual).isLB.cover.ge (Opens.mem_top (genericPoint X)))
    rw [mem_nonzeroLocus_iff u c hc, hu] at hg
    change genericPoint X ∈ X.basicOpen (0 : Γ(X, _)) at hg
    simp at hg

end GlobalTheory.HSNef
end

section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp.GenCut

theorem exists_finite_drop {T : Type} [TopologicalSpace T] [NoetherianSpace T] (Y : Set T) (d : ℕ)
    (hY : topologicalKrullDim Y ≤ (d + 1 : ℕ)) :
    ∃ S : Set T, S.Finite ∧ ∀ U : Set T, IsOpen U → S ⊆ U → topologicalKrullDim ↥(Y \ U) ≤ d := by
  classical
  have hfin := NoetherianSpace.finite_irreducibleComponents (α := Y)
  have hne : ∀ C : irreducibleComponents Y, ∃ y : Y, y ∈ C.1 := fun C => C.2.1.nonempty
  choose y hy using hne
  have : Finite (irreducibleComponents Y) := hfin.to_subtype
  refine ⟨Set.range fun C => (y C : T), Set.finite_range _, fun U hU hS => ?_⟩
  have hC : IsClosed ((Subtype.val : Y → T) ⁻¹' Uᶜ) := hU.isClosed_compl.preimage continuous_subtype_val
  have h := (GlobalTheory.T.topologicalKrullDim_drop_and_finite_of_dim_zero Y).1 _ (d + 1) hC hY fun Z hZ _ hsub =>
    hsub (hy ⟨Z, hZ⟩) (hS ⟨⟨Z, hZ⟩, rfl⟩)
  let f : ↥(Y \ U) → ↥((Subtype.val : Y → T) ⁻¹' Uᶜ) := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  have hf : IsInducing f := by
    refine (IsInducing.subtypeVal.comp IsInducing.subtypeVal).of_comp_iff.1 ?_
    exact IsInducing.subtypeVal
  have h2 := lt_of_le_of_lt hf.topologicalKrullDim_le h
  rw [Nat.cast_add, Nat.cast_one] at h2
  exact ENat.WithBot.lt_add_one_iff.1 h2

theorem exists_sections_finite : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (d : ℕ) (Z : Set X), IsClosed Z → topologicalKrullDim ↥(Z ∩ fib X 0) ≤ d → ∃ (e : Fin d → ℕ) (g : Fin d → X.functionField), (∀ j, 0 < e j ∧ g j ∈ P.H (e j) 0) ∧ ((Z \ ⋃ j, NV P (e j) 0 (g j)) ∩ fib X 0).Finite := by
  intro k _ X _ p D hp P hA d
  have := hp.isNoetherian
  induction d with
  | zero =>
    intro Z _ hd
    have hf : Finite ↥(Z ∩ fib X 0) := (GlobalTheory.T.topologicalKrullDim_drop_and_finite_of_dim_zero ↥(Z ∩ fib X 0)).2 inferInstance (by simpa using hd)
    refine ⟨Fin.elim0, Fin.elim0, fun j => j.elim0, ?_⟩
    exact (Set.toFinite (Z ∩ fib X 0)).subset (Set.inter_subset_inter_left _ Set.sdiff_subset)
  | succ d ih =>
    intro Z hZ hd
    obtain ⟨S, hS, hdrop⟩ := exists_finite_drop (Z ∩ fib X 0) d hd
    obtain ⟨e₀, he₀, f, hf, hSf⟩ := GlobalTheory.T.exists_ample_power_section_nonvanishing_on_finite k X p D hp P hA S hS
    have hU : IsOpen (NV P e₀ 0 f) := (GlobalTheory.T.regularNonvanishingLocusSection_properties k X p P e₀ 0 f hf).1
    have h := hdrop _ hU hSf
    rw [show (Z ∩ fib X 0) \ NV P e₀ 0 f = (Z \ NV P e₀ 0 f) ∩ fib X 0 from by
      ext x; simp only [Set.mem_sdiff, Set.mem_inter_iff]; tauto] at h
    obtain ⟨e, g, heg, hfin⟩ := ih _ (hZ.sdiff hU) h
    refine ⟨Fin.cons e₀ e, Fin.cons f g, fun j => ?_, hfin.subset ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) j
      · exact ⟨he₀, hf⟩
      · exact heg j
    · rintro x ⟨⟨hxZ, hx⟩, hx0⟩
      simp only [Set.mem_iUnion, not_exists] at hx
      refine ⟨⟨⟨hxZ, hx 0⟩, ?_⟩, hx0⟩
      simp only [Set.mem_iUnion, not_exists]
      exact fun j => hx j.succ

end GlobalTheory.HSAmp.GenCut
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
open scoped ComplexOrder
namespace GlobalTheory.HSAmp

theorem gram_posDef_and_l2_le_sup_bound : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ (P : Pair p) (ω : ∀ σ, VolDens p σ D) (a b : ℤ) (ι : Type) [Fintype ι] [DecidableEq ι] (f : ι → X.functionField), (∀ i, f i ∈ P.H a b) → LinearIndependent ℤ f → IsFam (fun σ => (ω σ).meas) (vals P a b f) ∧ (gram (fun σ => (ω σ).meas) (vals P a b f)).PosDef ∧ ∀ (c : ι → ℂ) (M : ℝ), (∀ σ y, cmb (vals P a b f) c σ y ≤ M) → l2 (fun σ => (ω σ).meas) (vals P a b f) c ≤ (∑ᶠ σ, ((ω σ).meas Set.univ).toReal) * M := by
  intro k _ X _ p D hX hG P ω a b ι _ _ f hf hli
  haveI : Finite (k →+* ℂ) := hX.finite_emb
  have hfin := fun σ => GlobalTheory.T.smoothVolumeDensity_finite_isOpenPos k X p D hX hG σ (ω σ)
  obtain ⟨hprod, hnu⟩ := GlobalTheory.T.continuous_hermSectionValue_mul_conj_and_norm_bounded k X p D hX P a b
  have hfam : IsFam (fun σ => (ω σ).meas) (vals P a b f) := by
    refine ⟨inferInstance, fun σ i j => ?_⟩
    haveI := (hfin σ).1
    obtain ⟨C₁, hC₁⟩ := (hnu (f i) (hf i)).2
    obtain ⟨C₂, hC₂⟩ := (hnu (f j) (hf j)).2
    refine Integrable.of_bound (hprod σ _ (hf i) _ (hf j)).aestronglyMeasurable (C₁ * C₂)
      (Filter.Eventually.of_forall fun y => ?_)
    have h0 : 0 ≤ P.nu a b σ y (f j) := (norm_val P a b σ y (f j)) ▸ norm_nonneg _
    simp only [vals, norm_mul, Complex.norm_conj, norm_val]
    exact mul_le_mul (hC₁ σ y) (hC₂ σ y) h0 (le_trans ((norm_val P a b σ y (f i)) ▸ norm_nonneg _) (hC₁ σ y))
  have hl2 := gram_isHermitian_and_l2_eq_quadratic_form (S := k →+* ℂ) (Y := fun σ => CxPts p σ) (ι := ι) (fun σ => (ω σ).meas) (vals P a b f) hfam
  have hcont : ∀ (c : ι → ℂ) σ, Continuous (cmb (vals P a b f) c σ) := by
    intro c σ
    have e : cmb (vals P a b f) c σ = fun y => (∑ i, ∑ j, (c i * (starRingEnd ℂ) (c j)) *
        (vals P a b f σ y i * (starRingEnd ℂ) (vals P a b f σ y j))).re := by
      funext y
      have h1 := Complex.mul_conj' (∑ i, c i * vals P a b f σ y i)

      rw [map_sum, Finset.sum_mul_sum] at h1
      simp only [cmb]
      rw [← Complex.ofReal_re (‖_‖ ^ 2), Complex.ofReal_pow, ← h1]
      congr 1
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp only [map_mul]; ring
    rw [e]
    exact Complex.continuous_re.comp (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      continuous_const.mul (hprod σ _ (hf i) _ (hf j)))
  haveI : Fintype (k →+* ℂ) := Fintype.ofFinite _
  refine ⟨hfam, GlobalTheory.T.gram_posDef_of_l2_definite (k →+* ℂ) (fun σ => CxPts p σ) ι (fun σ => (ω σ).meas) (vals P a b f) hfam
    fun c hc => ?_, fun c M hM => ?_⟩
  · rw [l2, finsum_eq_sum_of_fintype] at hc
    have hz := (Finset.sum_eq_zero_iff_of_nonneg fun σ _ =>
      integral_nonneg fun y => sq_nonneg ‖∑ i, c i * vals P a b f σ y i‖).1 hc
    refine GlobalTheory.T.linearIndependent_complex_sectionValues_of_int k X p D hX P a b ι f hf hli c fun σ y => ?_
    haveI := (hfin σ).2
    have hae := (integral_eq_zero_iff_of_nonneg (fun y => sq_nonneg ‖∑ i, c i * vals P a b f σ y i‖)
      ((hl2.2 c).1 σ)).1 (hz σ (Finset.mem_univ _))
    have hall := (Continuous.ae_eq_iff_eq _ (hcont c σ) continuous_const).1 hae
    have hy : ‖∑ i, c i * vals P a b f σ y i‖ ^ 2 = 0 := congrFun hall y
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hy)
  · rw [l2, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.sum_mul]
    refine Finset.sum_le_sum fun σ _ => ?_
    haveI := (hfin σ).1
    calc ∫ y, cmb (vals P a b f) c σ y ∂(ω σ).meas ≤ ∫ _y, M ∂(ω σ).meas :=
          integral_mono ((hl2.2 c).1 σ) (integrable_const M) fun y => hM σ y
      _ = ((ω σ).meas Set.univ).toReal * M := by
          rw [integral_const, smul_eq_mul, measureReal_def]

end GlobalTheory.HSAmp
end

section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.PushFinite

theorem coheight_genericPoint (X : Scheme.{0}) [IsIntegral X] :
    Order.coheight (genericPoint X) = 0 :=
  Order.coheight_eq_zero.2 fun b _ => genericPoint_specializes b

theorem dim_closure_add_one_le {X : Scheme.{0}} {a b : X} (hab : a < b) :
    topologicalKrullDim (closure ({a} : Set X)) + 1 ≤ topologicalKrullDim (closure ({b} : Set X)) := by
  refine topologicalKrullDim_add_one_le isClosed_closure isClosed_closure
    fun x hx => ⟨b, subset_closure rfl, fun hb => ?_, ?_⟩
  · exact hab.not_ge (specializes_iff_mem_closure.2 hb)
  · have h1 : b ⤳ a := hab.le
    have h2 : a ⤳ x := specializes_iff_mem_closure.2 hx
    exact h1.trans h2

theorem finite_notMem_coheight_le_one {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X] (U : X.Opens)
    (hU : (U : Set X).Nonempty) : {ξ : X | ξ ∉ U ∧ Order.coheight ξ ≤ 1}.Finite := by
  obtain ⟨S, hS, hcl, hirr, hun⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible U.isOpen.isClosed_compl
  have hg : genericPoint X ∈ U := (genericPoint_specializes hU.some).mem_open U.isOpen hU.some_mem
  refine (hS.biUnion (t := fun C => {κ | IsGenericPoint κ C}) fun C _ =>
    Set.Subsingleton.finite fun _ h _ h' => h.eq h').subset ?_
  rintro ξ ⟨hξ, h1⟩
  obtain ⟨C, hC, hξC⟩ : ξ ∈ ⋃₀ S := hun ▸ hξ
  obtain ⟨κ, hκ⟩ := QuasiSober.sober (hirr C hC) (hcl C hC)
  have hκU : κ ∈ (U : Set X)ᶜ := hun ▸ ⟨C, hC, hκ.mem⟩
  refine Set.mem_biUnion hC ?_
  by_cases h : ξ ⤳ κ
  · rwa [(h.antisymm (hκ.specializes hξC)).eq]
  · have hlt : ξ < κ := lt_of_le_not_ge (hκ.specializes hξC) h
    have hlt' : κ < genericPoint X := lt_of_le_not_ge (genericPoint_specializes κ)
      fun h' => hκU (((genericPoint_specializes κ).antisymm h').eq ▸ hg)
    have h2 := (add_le_add_left (le_add_self.trans (Order.coheight_add_one_le hlt')) 1).trans
      ((Order.coheight_add_one_le hlt).trans h1)
    exact absurd h2 (by decide)

theorem isFinite_restrict_of_le {X Y : Scheme.{0}} (g : Y ⟶ X) {U V : X.Opens} (hVU : V ≤ U)
    [IsFinite (g ∣_ U)] : IsFinite (g ∣_ V) := by
  have e : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.2 hVU
  have h1 : IsFinite ((g ∣_ U) ∣_ (U.ι ⁻¹ᵁ V)) := inferInstance
  haveI : MorphismProperty.RespectsIso (@IsFinite : MorphismProperty Scheme.{0}) :=
    MorphismProperty.RespectsIso.of_respects_arrow_iso _ fun f g e hf => by
      have : IsFinite g.hom := by
        rw [← Arrow.inv_left_hom_right e.hom]
        infer_instance
      exact this
  exact (MorphismProperty.arrow_mk_iso_iff @IsFinite
    (morphismRestrictRestrict g U (U.ι ⁻¹ᵁ V) ≪≫ morphismRestrictEq g e)).1 h1

theorem finite_near_coheight_one : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k), IsAmb p → IsAmb q → ∀ (g : Y ⟶ X) (hg : g ≫ p = q) (hη : g (genericPoint Y) = genericPoint X), g.residueDegree (genericPoint Y) ≠ 0 → ∀ z : X, Order.coheight z = 1 → (g ⁻¹' {z}).Finite ∧ (∀ w : Y, g w = z → Order.coheight w = 1) ∧ ∃ V : X.Opens, IsAffineOpen V ∧ z ∈ V ∧ IsFinite (g ∣_ V) := by
  intro k _ X Y _ _ _ _ p q hp hq g hg hη hd z hz
  obtain ⟨hbX1, -, hbX3, -, -, hbX6⟩ := GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient k X p hp
  obtain ⟨hbY1, -, -, -, -, hbY6⟩ := GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient k Y q hq
  obtain ⟨mX, hmX⟩ := hbX1
  obtain ⟨mY, hmY⟩ := hbY1
  obtain ⟨n, -, hnY⟩ := hmY (genericPoint Y)
  obtain ⟨nX, -, hnX⟩ := hmX (genericPoint X)
  have hnn : n = nX :=
    ((GlobalTheory.T.pointClosureDim_le_and_residueDegree_ne_zero_iff k X Y p q hp hq g hg (genericPoint Y) n nX hnY (hη ▸ hnX)).2).1 hd
  subst hnn
  have hzne : z ≠ genericPoint X := by
    rintro rfl
    rw [coheight_genericPoint] at hz
    exact zero_ne_one hz
  obtain ⟨e, rfl⟩ : ∃ e, n = e + 1 := by
    rcases n with _ | e
    · exfalso
      have hcl := (hbX3 (genericPoint X)).1 hnX
      have huniv : closure ({genericPoint X} : Set X) = Set.univ := genericPoint_spec X
      rw [hcl.closure_eq] at huniv
      have : z ∈ ({genericPoint X} : Set X) := huniv ▸ Set.mem_univ z
      exact hzne this
    · exact ⟨e, rfl⟩
  have hXd : topologicalKrullDim X = ((e + 1 : ℕ) : WithBot ℕ∞) := (hbX6 X (e + 1)).1 hnX
  have hYd : topologicalKrullDim Y = ((e + 1 : ℕ) : WithBot ℕ∞) := (hbY6 Y (e + 1)).1 hnY
  obtain ⟨hoX, -⟩ := GlobalTheory.T.coheight_one_iff_pointClosure_dim_projArith k X p hp e hXd
  obtain ⟨hoY, -⟩ := GlobalTheory.T.coheight_one_iff_pointClosure_dim_projArith k Y q hq e hYd
  have hze : HasDim z e := (hoX z).1 hz
  have hw : ∀ w : Y, g w = z → Order.coheight w = 1 := by
    intro w hwz
    rw [hoY]
    obtain ⟨dw, -, hdw⟩ := hmY w
    have h1 : e ≤ dw := (GlobalTheory.T.pointClosureDim_le_and_residueDegree_ne_zero_iff k X Y p q hp hq g hg w dw e hdw (hwz ▸ hze)).1
    have hwne : w ≠ genericPoint Y := by
      rintro rfl
      exact hzne (hwz.symm.trans hη)
    have hlt := dim_closure_add_one_le (lt_of_le_not_ge (genericPoint_specializes w)
      fun h' => hwne ((genericPoint_specializes w).antisymm h').eq.symm)
    unfold HasDim at hdw hnY
    rw [hdw, hnY] at hlt
    have h2 : dw + 1 ≤ e + 1 := by exact_mod_cast hlt
    have : dw = e := le_antisymm (by omega) h1
    subst this
    exact hdw
  have hfin : (g ⁻¹' {z}).Finite := by
    haveI := hq.isNoetherian
    let U : Y.Opens := g ⁻¹ᵁ ⟨(closure ({z} : Set X))ᶜ, isClosed_closure.isOpen_compl⟩
    have hU : genericPoint Y ∈ U := by
      show g (genericPoint Y) ∈ (closure ({z} : Set X))ᶜ
      rw [hη]
      intro hc
      exact hzne ((specializes_iff_mem_closure.2 hc).antisymm (genericPoint_specializes z)).eq
    refine (finite_notMem_coheight_le_one U ⟨_, hU⟩).subset fun w hwz => ⟨fun hwU => ?_, (hw w hwz).le⟩
    have hwU' : g w ∈ (closure ({z} : Set X))ᶜ := hwU
    exact hwU' (by rw [show g w = z from hwz]; exact subset_closure rfl)
  have := GlobalTheory.SchemeWords.isProper_of_isProjOver hp.isProjOver
  have : IsProper (g ≫ p) := hg ▸ GlobalTheory.SchemeWords.isProper_of_isProjOver hq.isProjOver
  have : IsProper g := IsProper.of_comp g p
  obtain ⟨V₀, hzV₀, hV₀⟩ := exists_isFinite_morphismRestrict_of_finite_preimage_singleton g z hfin
  obtain ⟨V, hV, hzV, hle⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hzV₀
  exact ⟨hfin, hw, V, hV, hzV, isFinite_restrict_of_le g hle⟩

end GlobalTheory.PushFinite
end

section

noncomputable section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR.FactorAct

variable {T : Type} [Fintype T] [DecidableEq T] {V : T → Type} [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)]

omit [Fintype T] in
theorem atPl_tprod' (w : T) (L : Module.End ℂ (V w)) (f : ∀ i, V i) :
    atPl w L (PiTensorProduct.tprod ℂ f) = PiTensorProduct.tprod ℂ (Function.update f w (L (f w))) := by
  rw [atPl, PiTensorProduct.map_tprod]
  congr 1
  funext i
  by_cases h : i = w
  · subst h; simp
  · simp [Function.update_of_ne h]

omit [Fintype T] in
theorem atPl_mul' (w : T) (L L' : Module.End ℂ (V w)) : atPl w (L * L') = atPl w L * atPl w L' := by
  refine PiTensorProduct.ext (MultilinearMap.ext fun f => ?_)
  simp [atPl_tprod']

omit [Fintype T] in
theorem atPl_comm' {w w' : T} (h : w ≠ w') (L : Module.End ℂ (V w)) (L' : Module.End ℂ (V w')) (x : ⨂[ℂ] i, V i) :
    atPl w L (atPl w' L' x) = atPl w' L' (atPl w L x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    simp only [map_smul, atPl_tprod', Function.update_of_ne h, Function.update_of_ne h.symm]
    rw [Function.update_comm h]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

def intersection_update_fsHerm_neg_one (f : ∀ i, V i) (w : T) : V w →ₗ[ℂ] ⨂[ℂ] i, V i := (PiTensorProduct.tprod ℂ (s := V)).toLinearMap f w

omit [Fintype T] in
theorem position_apply (f : ∀ i, V i) (w : T) (v : V w) : intersection_update_fsHerm_neg_one f w v = PiTensorProduct.tprod ℂ (Function.update f w v) := rfl

omit [Fintype T] in
theorem position_self (f : ∀ i, V i) (w : T) : intersection_update_fsHerm_neg_one f w (f w) = PiTensorProduct.tprod ℂ f := by
  rw [position_apply, Function.update_eq_self]

omit [Fintype T] in
theorem atPl_tprod_update (f : ∀ i, V i) (w : T) (L : Module.End ℂ (V w)) (v : V w) :
    atPl w L (intersection_update_fsHerm_neg_one f w v) = intersection_update_fsHerm_neg_one f w (L v) := by
  simp [position_apply, atPl_tprod']

variable {p q : ℕ}

omit [Fintype T] in
theorem atPl_sub' (w : T) (A B : Module.End ℂ (V w)) : atPl w (A - B) = atPl w A - atPl w B :=
  map_sub ((PiTensorProduct.mapMultilinear ℂ V V).toLinearMap (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w) A B

theorem actAt_lie (w : T) {a : Mat p q →ₗ[ℂ] Module.End ℂ (V w)} (h : IsLieAct a) : IsLieAct (actAt w a) := by
  intro X Y
  rw [actAt_apply, actAt_apply, actAt_apply, h X Y, atPl_sub', atPl_mul', atPl_mul']

theorem actAt_wts (w : T) {a : Mat p q →ₗ[ℂ] Module.End ℂ (V w)} (h : ∀ v, v ∈ ⨆ μ : Ix p q → ℚ, wtSub a μ)
    (x : ⨂[ℂ] i, V i) : x ∈ ⨆ μ : Ix p q → ℚ, wtSub (actAt w a) μ := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    refine Submodule.smul_mem _ _ ?_
    rw [← position_self f w]
    refine Submodule.iSup_induction _ (motive := fun v => intersection_update_fsHerm_neg_one f w v ∈ ⨆ μ : Ix p q → ℚ, wtSub (actAt w a) μ) (h (f w))
      ?_ (by simp) ?_
    · intro μ y hy
      refine Submodule.mem_iSup_of_mem μ ?_
      simp only [wtSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.smul_apply, LinearMap.id_apply] at hy ⊢
      intro c
      rw [actAt_apply, atPl_tprod_update, ← map_smul, ← map_sub, hy c, map_zero]
    · intro x y hx hy
      rw [map_add]
      exact add_mem hx hy
  | add x y hx hy => exact Submodule.add_mem _ hx hy

theorem actAt_locU (w : T) {a : Mat p q →ₗ[ℂ] Module.End ℂ (V w)} (h : LocU (fun c : Ix p q => c.isLeft) (units a)) :
    LocU (fun c : Ix p q => c.isLeft) (units (actAt w a)) := by
  refine GlobalTheory.T.isLocallyBlockUnitary_of_iSup_intertwiner_range (Ix p q) (V w) (fun c : Ix p q => c.isLeft) (units a) (⨂[ℂ] i, V i) (units (actAt w a))
    {g | ∃ f : ∀ i, V i, g = intersection_update_fsHerm_neg_one f w} ?_ ?_ h
  · rintro g ⟨f, rfl⟩ c d _ x
    simp only [units, actAt_apply, atPl_tprod_update]
  · refine eq_top_iff.2 ?_
    rw [← PiTensorProduct.span_tprod_eq_top]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, rfl⟩
    refine (le_iSup₂ (f := fun (g : V w →ₗ[ℂ] ⨂[ℂ] i, V i) (_ : g ∈ {g | ∃ f : ∀ i, V i, g = intersection_update_fsHerm_neg_one f w}) =>
      LinearMap.range g) (intersection_update_fsHerm_neg_one f w) ⟨f, rfl⟩ : _) ⟨f w, position_self f w⟩

end GlobalTheory.HoweR.FactorAct

namespace GlobalTheory.HoweR

theorem actAt_good_comm : ∀ (T : Type) [Fintype T] [DecidableEq T] (V : T → Type) [∀ w, AddCommGroup (V w)]
    [∀ w, Module ℂ (V w)], ∀ (R S : T → ℕ) (a : ∀ w, Mat (R w) (S w) →ₗ[ℂ] Module.End ℂ (V w)), (∀ w, Good (a w)) →
    (∀ w, Good (actAt w (a w))) ∧ ∀ w w', w ≠ w' → ∀ Z Z' v,
      actAt w (a w) Z (actAt w' (a w') Z' v) = actAt w' (a w') Z' (actAt w (a w) Z v) := by
  intro T _ _ V _ _ R S a ha
  refine ⟨fun w => ⟨FactorAct.actAt_lie w (ha w).1, FactorAct.actAt_wts w (ha w).2.1, FactorAct.actAt_locU w (ha w).2.2⟩,
    fun w w' hw Z Z' v => ?_⟩
  exact FactorAct.atPl_comm' hw _ _ v

end GlobalTheory.HoweR

end
end

section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

theorem _root_.GlobalTheory.T.thetaLift_submodule_comap_stable_secondMember : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (om : Rep σ X W) (τ : ∀ w : InfinitePlace F, EmbOver E w) (P Q R S : InfinitePlace F → ℕ) (Φ : TensD F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)) (c : InfinitePlace F → ℂ) (N : Submodule ℂ (SInf F (Fin n × Fin d))), IsCMExt F E σ → GlobalTheory.Published.ThetaSubInf M ψ τ om N → ∀ C : ∀ w : InfinitePlace F, Matrix (Fin d) (Ix (R w) (S w)) ℂ, (∀ w, IsFrame (Complex.I • (incM F W.J).map (piInf (τ w))) (C w)) → ActsByD τ C (om.comp (MonoidHom.inr _ _)) Φ (fun w => fockAct2 (P w) (Q w) (R w) (S w)) c → ∀ w, GlobalTheory.HoweR.Stab (GlobalTheory.HoweR.actAt (V := fun w => Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)) w (fockAct2 (P w) (Q w) (R w) (S w))) (N.comap Φ) := by
  first | exact @GlobalTheory.HoweD.stab_comap_of_thetaSubInf | exact GlobalTheory.HoweD.stab_comap_of_thetaSubInf | (intros; apply GlobalTheory.HoweD.stab_comap_of_thetaSubInf <;> assumption)
end

section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

theorem _root_.GlobalTheory.T.thetaLift_submodule_contains_firstMember_coinvariants : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (om : Rep σ X W) (τ : ∀ w : InfinitePlace F, EmbOver E w) (P Q R S : InfinitePlace F → ℕ) (Φ : TensD F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)) (c : InfinitePlace F → ℂ) (N : Submodule ℂ (SInf F (Fin n × Fin d))), IsCMExt F E σ → GlobalTheory.Published.ThetaSubInf M ψ τ om N → LinearMap.range Φ = M.Pol ψ τ → ∀ A : ∀ w : InfinitePlace F, Matrix (Fin n) (Ix (P w) (Q w)) ℂ, (∀ w, IsFrame ((1 : ℂ) • (incM F X.J).map (piInf (τ w))) (A w)) → ActsByD τ A (om.comp (MonoidHom.inl _ _)) Φ (fun w => fockAct1 (P w) (Q w) (R w) (S w)) c → GlobalTheory.HoweR.tensAny (fun w => GlobalTheory.HoweR.coinv (P w) (Q w) (R w) (S w) (-c w)) ≤ N.comap Φ := by
  first | exact @GlobalTheory.HoweD.tensAny_coinv_le_comap | exact GlobalTheory.HoweD.tensAny_coinv_le_comap | (intros; apply GlobalTheory.HoweD.tensAny_coinv_le_comap <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.formGroup_testFunction_support_bounded_denominators : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t) (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (h₁ : G.GAf), ∃ D : ℕ, 0 < D ∧ ∀ y : grp G β, f (h₁⁻¹ * toAfF G β x t hx y * h₁) ≠ 0 → ∀ ℓ : ℕ, ℓ ≠ p → (∀ i, ((Module.finBasis ℚ G.C).repr (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) i).den.factorization ℓ ≤ D.factorization ℓ) ∧ (((((y : G.Cˣ × ℚˣ).2)⁻¹ : ℚˣ) : ℚ)).den.factorization ℓ ≤ D.factorization ℓ := by
  first | (exact @GlobalTheory.LKCx.BoundedDen.main) | (exact GlobalTheory.LKCx.BoundedDen.main) | (intros; apply GlobalTheory.LKCx.BoundedDen.main  <;> assumption)
end
