module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1365
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLocalSubringGenericPoint
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsEffAddNsmulDiv
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToIThCapDegOfAddNsmulDivP
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle240
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1323
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1325
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsQuasiRegularSeqSelfIffLocalizationMaximal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1329
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1324
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle039
import Development.AbelianVarietyTheory.Definitions.Divisors.LeTwoMulOfForallScale
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1326

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

theorem _root_.GlobalTheory.T.hermitianLineBundle_isNef_shift_of_nonneg : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (M : HermLB p) (t : ℝ), 0 ≤ t → M.IsNef D → (M.shift (fun _ => t) fun _ => rfl).IsNef D := by
  first | exact @GlobalTheory.NefShift.isNef_shift_nonneg | exact GlobalTheory.NefShift.isNef_shift_nonneg | (intros; apply GlobalTheory.NefShift.isNef_shift_nonneg <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.semiPos_of_pullback_generically_etale : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D : ℕ), IsArithVar p D → IsArithVar q D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (V : Y.Opens), (V : Set Y).Nonempty → Etale (V.ι ≫ π) → ∀ L : HermLB p, (L.pull π hπ).SemiPos D → L.SemiPos D := by
  first | exact @GlobalTheory.SemiPosEtale.semiPos_of_pull_etale | exact GlobalTheory.SemiPosEtale.semiPos_of_pull_etale | (intros; apply GlobalTheory.SemiPosEtale.semiPos_of_pull_etale <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.ArithCurve

theorem isProper_of_projOver {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R}
    (h : IsProjOver f) : IsProper f := by
  obtain ⟨m, i, hi, rfl⟩ := h
  have := isProper_str R m
  infer_instance

theorem not_isClosed_genericPoint_int : ¬ IsClosed ({genericPoint (Sp ℤ)} : Set (Sp ℤ)) := by
  intro hc
  have hu : ∀ x : Sp ℤ, x = genericPoint (Sp ℤ) := fun x => by
    have hx : x ∈ closure ({genericPoint (Sp ℤ)} : Set (Sp ℤ)) :=
      (genericPoint_spec (Sp ℤ)).def ▸ Set.mem_univ x
    rwa [hc.closure_eq] at hx
  let a : PrimeSpectrum ℤ := ⟨⊥, Ideal.isPrime_bot⟩
  let b : PrimeSpectrum ℤ := ⟨Ideal.span {(2 : ℤ)},
    (Ideal.span_singleton_prime (by norm_num)).2 Int.prime_two⟩
  have hab : a = b := (hu (show Sp ℤ from a)).trans (hu (show Sp ℤ from b)).symm
  have h2 : (2 : ℤ) ∈ b.asIdeal := Ideal.subset_span rfl
  rw [← hab] at h2
  exact absurd ((Submodule.mem_bot ℤ).1 h2) (by norm_num)

theorem isAffine_and_finite : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k),
    IsArithVar q 0 → IsAffine Y ∧ Module.Finite ℤ Γ(Y, ⊤) := by
  intro k _ Y q h
  have := h.isIntegral
  have := h.isNoetherian
  have hd : topologicalKrullDim Y = 1 := by simpa using h.dim_eq
  have : IsProper q := isProper_of_projOver h.isProjOver
  have : IsFinite (spMap (Int.castRingHom k)) := by
    have := h.finite
    rw [IsFinite.SpecMap_iff]
    change (Int.castRingHom k).Finite
    rw [← algebraMap_int_eq]
    exact RingHom.finite_algebraMap.2 ‹_›
  set f : Y ⟶ Sp ℤ := q ≫ spMap (Int.castRingHom k) with hf
  have : Flat f := h.flat
  have : IsProper f := inferInstance
  have hη : f (genericPoint Y) = genericPoint (Sp ℤ) := by
    obtain ⟨y, hy, e⟩ := Flat.generalizingMap f (genericPoint_specializes (f (genericPoint Y)))
    rwa [(hy.antisymm (genericPoint_specializes y)).eq] at e
  have hfib : ∀ z, (f ⁻¹' {z}).Finite := by
    intro z
    by_cases hz : z = genericPoint (Sp ℤ)
    · refine (Set.finite_singleton (genericPoint Y)).subset fun y hy => ?_
      by_contra hne
      have hc := f.isClosedMap _ (ProperCurve.isClosed_singleton hd hne)
      rw [Set.image_singleton, show f y = z from hy, hz] at hc
      exact not_isClosed_genericPoint_int hc
    · refine (ProperCurve.finite_of_isClosed hd (isClosed_closure.preimage f.continuous) ?_).subset
        (Set.preimage_mono subset_closure)
      intro hmem
      rw [Set.mem_preimage, hη, ← specializes_iff_mem_closure] at hmem
      exact hz (hmem.antisymm (genericPoint_specializes z)).eq
  have : LocallyQuasiFinite f := .of_finite_preimage_singleton f hfib
  have : IsFinite f := .of_isProper_of_locallyQuasiFinite f
  have : IsAffine Y := isAffine_of_isAffineHom f
  refine ⟨this, ?_⟩
  have h1 := IsFinite.finite_app f ⊤ (isAffineOpen_top _)
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv.hom.Finite :=
    RingHom.Finite.of_surjective _ fun x => ⟨(Scheme.ΓSpecIso (CommRingCat.of ℤ)).hom x, by simp⟩
  have e : (f.app ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv.hom =
      algebraMap ℤ Γ(Y, ⊤) := RingHom.ext_int _ _
  exact RingHom.finite_algebraMap.1 (e ▸ h1.comp h2)

end GlobalTheory.ArithCurve
end
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.adaptedFrame_eventually_near_complexPoint : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) {y : CxPts X.str σ} {A : Mat (fun _ : Unit => m) X.Fn}, A ∈ E.S (under y) → ∀ᶠ z in 𝓝 y, A ∈ E.S (under z) := by
  first | exact @GlobalTheory.GoodTop.frame_eventually | exact GlobalTheory.GoodTop.frame_eventually | (intros; apply GlobalTheory.GoodTop.frame_eventually <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Vert GlobalTheory.Vert.Model GlobalTheory.VB

namespace GlobalTheory.Vert.Model

theorem topologicalKrullDim_gen : ∀ (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (Z : Model O), topologicalKrullDim Z.gen.toScheme = Z.relDim := by
  intro O _ _ _ Z
  obtain ⟨q, H⟩ := Z.exists_isPullback_gen (FractionRing O)
  obtain ⟨d, hd, -⟩ := exists_topologicalKrullDim_fibres_eq_of_isPullback Z.str (FractionRing O)
    (IsLocalRing.ResidueField O) IsLocalRing.residue_surjective (IsPullback.of_hasPullback _ _) H
  rw [hd, relDim_eq_iff.2
    (IntModel.topologicalKrullDim_eq_succ (IsDiscreteValuationRing.not_isField O) H hd)]

end GlobalTheory.Vert.Model
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair

open IsLocalRing Polynomial

theorem eq_zero_of_eval_mem_maximalIdeal {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    {f : R} (hf0 : f ≠ 0) (hfm : f ∈ maximalIdeal R) (p : R[X])
    (hu : ∀ i, p.coeff i ≠ 0 → IsUnit (p.coeff i)) (he : p.eval f = 0) : p = 0 := by
  suffices h : ∀ d (p : R[X]), p.natDegree = d → (∀ i, p.coeff i ≠ 0 → IsUnit (p.coeff i)) →
      p.eval f = 0 → p = 0 from h _ p rfl hu he
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro p hd hu he
  have hsplit := X_mul_divX_add p
  have h2 : p.eval f = f * (divX p).eval f + p.coeff 0 := by
    have h3 := congrArg (Polynomial.eval f) hsplit
    simp only [eval_add, eval_mul, eval_X, eval_C] at h3
    exact h3.symm
  have he' : f * (divX p).eval f + p.coeff 0 = 0 := by rw [← h2]; exact he
  have hc0 : p.coeff 0 = 0 := by
    by_contra hc
    have hmem : p.coeff 0 ∈ maximalIdeal R := by
      have e : p.coeff 0 = -(f * (divX p).eval f) := by linear_combination he'
      rw [e]
      exact (maximalIdeal R).neg_mem ((maximalIdeal R).mul_mem_right _ hfm)
    exact (mem_maximalIdeal _).1 hmem (hu 0 hc)
  have hdv : (divX p).eval f = 0 := by
    rw [hc0, add_zero] at he'
    exact (mul_eq_zero.1 he').resolve_left hf0
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · rw [eq_C_of_natDegree_eq_zero (hd.trans hd0), hc0, C_0]
  · have h0 : divX p = 0 := ih (d - 1) (by omega) (divX p)
      (by rw [natDegree_divX_eq_natDegree_tsub_one, hd])
      (fun i hi => by rw [coeff_divX] at hi ⊢; exact hu _ hi) hdv
    rw [← hsplit, h0, hc0, mul_zero, C_0, add_zero]

theorem trBasis_uniformiser_cons : ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K)
    (n : ℕ) (S : Place cL) (ψ : S.ring →+* K) (f : S.ring) (w : Fin n → S.ring),
    Function.Surjective ψ → (∀ a, ψ (S.const a) = cK a) → Irreducible f →
    TrBasis cK (fun i => ψ (w i)) →
    TrBasis cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L) ∧
      (fun ω => @dite ℤ (∃ a, S.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (dForm cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L)) = 0 ∧
      S.ord (f : L) = 1 ∧ ∀ g : S.ring, ψ g ≠ 0 → S.ord (g : L) = 0 := by
  intro L K _ _ cL cK n S ψ f w hψ hc hf hwK
  letI : Algebra ℂ S.ring := S.const.toAlgebra
  letI : Algebra ℂ L := cL.toAlgebra
  letI : Algebra ℂ K := cK.toAlgebra
  haveI : IsScalarTower ℂ S.ring L := IsScalarTower.of_algebraMap_eq' rfl
  have hcomp : ψ.comp (algebraMap ℂ S.ring) = algebraMap ℂ K := RingHom.ext hc
  haveI : Algebra.EssFiniteType ℂ S.ring := S.essFiniteType
  haveI := formallySmooth_of_isRegularLocalRing_of_perfectField ℂ S.ring
  have hker : RingHom.ker ψ = maximalIdeal S.ring := by
    haveI := RingHom.ker_isMaximal_of_surjective ψ hψ
    exact IsLocalRing.eq_maximalIdeal this
  have hunit : ∀ g : S.ring, ψ g ≠ 0 → IsUnit g := by
    intro g hg
    by_contra hu
    exact hg (by rw [← RingHom.mem_ker, hker]; exact hu)
  have hwu : ∀ P : MvPolynomial (Fin n) ℂ, P ≠ 0 →
      IsUnit (MvPolynomial.eval₂ (algebraMap ℂ S.ring) w P) := by
    intro P hP
    apply hunit
    rw [MvPolynomial.hom_eval₂, hcomp]
    intro h0
    have hind : AlgebraicIndependent ℂ (fun i => ψ (w i)) := hwK.1
    exact hP ((algebraicIndependent_iff.1 hind) P h0)

  obtain ⟨m, z, b, -, -⟩ := exists_basis_kaehler_uniformiser ℂ hf
  have hL : Algebra.trdeg ℂ L = (m + 1 : ℕ) := trdeg_eq_of_basis_kaehler ℂ L b
  have hR := trdeg_residueField_of_trdeg ℂ S.ring L hL
  simp only [add_tsub_cancel_right] at hR
  have hK : Algebra.trdeg ℂ K = n := by
    have := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) hwK
    rw [Cardinal.mk_fin] at this
    exact this.symm
  have hmn : m ≤ n := by
    obtain ⟨s, hs⟩ := exists_isTranscendenceBasis ℂ (ResidueField S.ring)
    let res := IsLocalRing.residue S.ring
    let lift : s → S.ring := fun i => Function.surjInv IsLocalRing.residue_surjective (i : _)
    have hlift : res ∘ lift = Subtype.val := funext fun i =>
      Function.surjInv_eq IsLocalRing.residue_surjective _
    have hg : AlgebraicIndependent ℂ (fun i => ψ (lift i)) := by
      refine algebraicIndependent_iff.2 fun P hP => ?_
      by_contra hne
      have hu : IsUnit (MvPolynomial.eval₂ (algebraMap ℂ S.ring) lift P) := by
        rw [← IsLocalRing.residue_ne_zero_iff_isUnit, MvPolynomial.eval₂_comp_left]
        change MvPolynomial.aeval (res ∘ lift) P ≠ 0
        rw [hlift]
        exact fun h0 => hne (algebraicIndependent_iff.1 hs.1 P h0)
      apply (hu.map ψ).ne_zero
      rw [MvPolynomial.hom_eval₂, hcomp]
      exact hP
    have h1 := hg.cardinalMk_le_trdeg
    rw [hs.cardinalMk_eq_trdeg, hR, hK] at h1
    exact_mod_cast h1

  have hsplit : ∀ P : MvPolynomial (Fin (n + 1)) ℂ,
      MvPolynomial.eval₂ (algebraMap ℂ S.ring) (Fin.cons f w : Fin (n + 1) → S.ring) P =
        Polynomial.eval f (Polynomial.map (MvPolynomial.eval₂Hom (algebraMap ℂ S.ring) w)
          (MvPolynomial.finSuccEquiv ℂ n P)) := by
    intro P
    have hrh : MvPolynomial.eval₂Hom (algebraMap ℂ S.ring) (Fin.cons f w : Fin (n + 1) → S.ring) =
        (Polynomial.evalRingHom f).comp
          ((Polynomial.mapRingHom (MvPolynomial.eval₂Hom (algebraMap ℂ S.ring) w)).comp
            (MvPolynomial.finSuccEquiv ℂ n : MvPolynomial (Fin (n + 1)) ℂ →+* _)) := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp [MvPolynomial.finSuccEquiv_apply]
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i <;>
          simp [MvPolynomial.finSuccEquiv_X_zero, MvPolynomial.finSuccEquiv_X_succ]
    exact RingHom.congr_fun hrh P
  have hcoe : ∀ P : MvPolynomial (Fin (n + 1)) ℂ,
      MvPolynomial.aeval (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L) P =
        ((MvPolynomial.eval₂ (algebraMap ℂ S.ring) (Fin.cons f w : Fin (n + 1) → S.ring) P :
          S.ring) : L) := by
    intro P
    have h := MvPolynomial.hom_eval₂ P (algebraMap ℂ S.ring) S.ring.subtype
      (Fin.cons f w : Fin (n + 1) → S.ring)
    rw [ValuationSubring.subtype_apply] at h
    rw [h, MvPolynomial.aeval_def]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  have hind : AlgebraicIndependent ℂ (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L) := by
    refine algebraicIndependent_iff.2 fun P hP => ?_
    rw [hcoe, ZeroMemClass.coe_eq_zero, hsplit] at hP
    set Q := MvPolynomial.finSuccEquiv ℂ n P with hQ
    have hq := eq_zero_of_eval_mem_maximalIdeal hf.ne_zero hf.not_isUnit _ (fun i hi => by
      rw [Polynomial.coeff_map] at hi ⊢
      refine hwu _ fun h0 => hi ?_
      rw [h0, map_zero]) hP
    have hQ0 : Q = 0 := by
      apply Polynomial.ext
      intro i
      rw [Polynomial.coeff_zero]
      by_contra h0
      apply (hwu _ h0).ne_zero
      have := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p i) hq
      simpa [Polynomial.coeff_map] using this
    exact (MvPolynomial.finSuccEquiv ℂ n).injective (by rw [← hQ, hQ0, map_zero])
  have htr : TrBasis cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L) := by
    unfold TrBasis
    refine hind.isTranscendenceBasis_of_trdeg_le_of_finite ?_
    rw [hL, Cardinal.mk_fin]
    exact_mod_cast (by omega : m + 1 ≤ n + 1)
  refine ⟨htr, ?_, S.ord_irreducible hf, fun g hg => S.ord_eq_zero (hunit g hg)⟩
  exact GlobalTheory.formOrd_dForm_uniformiser_cons cL n S f w hf hwu ⟨_, htr⟩

end GlobalTheory.FieldPair
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

namespace GlobalTheory.GraphLocal


open scoped IntermediateField.algebraAdjoinAdjoin in
theorem exists_trBasis_lift : ∀ {K κ : Type} [Field K] [Field κ] [Algebra ℂ κ] (k : ℕ) (R : Subring K) (π : R →+* κ),
  (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) → (∃ z : Fin k → κ, TrBasis (algebraMap ℂ κ) z) →
  ∃ zR : Fin k → R, TrBasis (algebraMap ℂ κ) (fun i => π (zR i)) := by
  intro K κ _ _ inst k R π hfrac ⟨z, hz⟩
  have hiff : ∀ u : Fin k → κ, TrBasis (algebraMap ℂ κ) u ↔ IsTranscendenceBasis ℂ u := by
    intro u
    have : (algebraMap ℂ κ).toAlgebra = inst := Algebra.algebra_ext _ _ fun _ => rfl
    unfold TrBasis
    rw [this]
  have hz' := (hiff z).1 hz
  have htop : IntermediateField.adjoin ℂ (Set.range π) = ⊤ := by
    refine eq_top_iff.2 fun f _ => ?_
    obtain ⟨a, b, hb, e⟩ := hfrac f
    have : f = π a / π b := by rw [← e, mul_div_cancel_right₀ _ hb]
    rw [this]
    exact div_mem (IntermediateField.subset_adjoin _ _ ⟨a, rfl⟩)
      (IntermediateField.subset_adjoin _ _ ⟨b, rfl⟩)
  have halg : Algebra.IsAlgebraic (IntermediateField.adjoin ℂ (Set.range π)) κ :=
    ⟨fun f => isAlgebraic_algebraMap
      (⟨f, htop ▸ IntermediateField.mem_top⟩ : IntermediateField.adjoin ℂ (Set.range π))⟩
  have halg' : Algebra.IsAlgebraic (Algebra.adjoin ℂ (Set.range π)) κ :=
    IntermediateField.isAlgebraic_adjoin_iff_top.mp halg
  obtain ⟨t, ht, hb⟩ := exists_isTranscendenceBasis_subset (R := ℂ) (Set.range π)
  have hc : Cardinal.mk (Fin k) = Cardinal.mk t := by
    rw [hb.cardinalMk_eq_trdeg, hz'.cardinalMk_eq_trdeg]
  obtain ⟨e⟩ := Cardinal.eq.mp hc
  choose J hJ using fun i : Fin k => ht (e i).2
  refine ⟨J, (hiff _).2 ?_⟩
  have := (isTranscendenceBasis_equiv e).2 hb
  convert this using 1
  funext i
  exact hJ i

end GlobalTheory.GraphLocal
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_weightedMonomialPlace_of_isLocModel : ∀ {L : Type} [Field L] (c : ℂ →+* L) (Q : Subring L) (hQ : IsLocModel c Q),
    letI := hQ.isLocalRing; ∀ (r : ℕ) (z : Fin (r + 1) → Q) (wt : Fin (r + 1) → ℕ),
    IsNoetherianRing Q → Ideal.span (Set.range z) = IsLocalRing.maximalIdeal Q →
    IsQuasiRegularSeq Q z → wt 0 = 1 → (∀ i, 1 ≤ wt i) →
    ∃ (V : Place c) (hC : V.Contains Q) (u : Fin r → V.ring),
      (∀ i, (u i : L) * (z 0 : L) ^ wt i.succ = z i.succ) ∧
      Irreducible (⟨z 0, hC _ (z 0).2⟩ : V.ring) ∧
      (∀ q ∈ IsLocalRing.maximalIdeal Q,
        (⟨q, hC _ q.2⟩ : V.ring) ∈ IsLocalRing.maximalIdeal V.ring) ∧
      (∀ P : MvPolynomial (Fin r) Q, (∃ α, P.coeff α ∉ IsLocalRing.maximalIdeal Q) →
        IsUnit (MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u P)) ∧
      ∀ f : V.ring, ∃ P R : MvPolynomial (Fin r) Q,
        IsUnit (MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u R) ∧
        f * MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u R =
          MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u P := by
  first | exact @GlobalTheory.exists_weightedMonomialPlace | exact GlobalTheory.exists_weightedMonomialPlace | (intros; apply GlobalTheory.exists_weightedMonomialPlace <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.essFiniteType_of_localRingOfVarietyPoint : ∀ {K : Type} [Field K] [Algebra ℂ K] (R : Subring K),
  IsLocModel (algebraMap ℂ K) R → Algebra.EssFiniteType ℂ K := by
  first | exact @GlobalTheory.essFiniteType_of_isLocModel | exact GlobalTheory.essFiniteType_of_isLocModel | (intros; apply GlobalTheory.essFiniteType_of_isLocModel <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.isFreeModuleGenerator_kaehlerWedge_regularPair_cons : ∀ {L : Type} [Field L] (cL : ℂ →+* L) (Q : Subring L) (hQ : IsLocModel cL Q) (t u : Q),
  Ideal.span {t, u} = (letI := hQ.isLocalRing; IsLocalRing.maximalIdeal Q) → ringKrullDim Q = 2 →
  ∃ (m : ℕ) (z : Fin m → Q),
    (∀ P : MvPolynomial (Fin m) ℂ, P ≠ 0 → IsUnit (MvPolynomial.eval₂ (cL.codRestrict Q hQ.const_mem) z P)) ∧
    IsFreeGen Q (dForm (cL.codRestrict Q hQ.const_mem) (Fin.cons t (Fin.cons u z : Fin (m + 1) → Q) : Fin (m + 2) → Q)) := by
  first | exact @GlobalTheory.FieldPair.isFreeGen_dForm_regularPair_cons | exact GlobalTheory.FieldPair.isFreeGen_dForm_regularPair_cons | (intros; apply GlobalTheory.FieldPair.isFreeGen_dForm_regularPair_cons <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.dvrPlace_topForm_orders_api : ∀ {k K : Type} [Field k] [CharZero k] [Field K] (c : k →+* K) (n : ℕ) (x : Fin n → K), TrBasis c x →
  IsFreeGen K (dForm c x) ∧
  ∀ E : Place c, (∃ ω : Forms E.const n, IsFreeGen E.ring ω) ∧
    (∀ η : Forms c n, η ≠ 0 → E.IsFormOrd η ((fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) η)) ∧
    (∀ (η : Forms c n) (f : K), η ≠ 0 → f ≠ 0 → (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (f • η) = E.ord f + (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) η) ∧
    (∀ (η : Forms c n) (a : ℤ), η ≠ 0 → E.IsFormOrd η a → (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) η = a) := by
  first | exact @GlobalTheory.FieldPair.formOrd_api | exact GlobalTheory.FieldPair.formOrd_api | (intros; apply GlobalTheory.FieldPair.formOrd_api <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_residue_coordinates_of_localModel_below_place : ∀ {L : Type} [Field L] (c : ℂ →+* L) (Q : Subring L) (hQ : IsLocModel c Q),
    letI := hQ.isLocalRing; ∀ (N r : ℕ) (V : Place c) (hC : V.Contains Q) (u : Fin r → V.ring),
    (∃ x : Fin N → L, TrBasis c x) →
    (∀ q ∈ IsLocalRing.maximalIdeal Q,
      (⟨q, hC _ q.2⟩ : V.ring) ∈ IsLocalRing.maximalIdeal V.ring) →
    (∀ P : MvPolynomial (Fin r) Q, (∃ α, P.coeff α ∉ IsLocalRing.maximalIdeal Q) →
      IsUnit (MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u P)) →
    (∀ f : V.ring, ∃ P R : MvPolynomial (Fin r) Q,
      IsUnit (MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u R) ∧
      f * MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u R =
        MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u P) →
    ∃ (j : ℕ) (s : Fin j → Q), r + j + 1 = N ∧
      ∀ P : MvPolynomial (Fin (r + j)) ℂ, P ≠ 0 →
        IsUnit (MvPolynomial.eval₂ V.const
          (Fin.append u fun i => (⟨s i, hC _ (s i).2⟩ : V.ring)) P) := by
  first | exact @GlobalTheory.FieldPair.exists_residue_coords_of_locModel | exact GlobalTheory.FieldPair.exists_residue_coords_of_locModel | (intros; apply GlobalTheory.FieldPair.exists_residue_coords_of_locModel <;> assumption)
end
