module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.IsotypQuot
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle001
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle003
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import GroundTheory.AutomorphicForms.Bundle012
import GroundTheory.AutomorphicForms.GL2.AdelicFourier2TensorCosetIndicatorAlgebraMap
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Lemma
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
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.ThInf
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ConjInv
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical


open GroundTheory.Automorphic.FourierWhittaker in
private noncomputable def latE' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E) :
    vecLattice F (Fin 2) ≃ AdeleRing.principalSubgroup (𝓞 E) E where
  toFun g := ⟨D.coE.symm g.1, by
    obtain ⟨_, ξ, rfl⟩ := g
    refine ⟨algebraMap F E (ξ 0) + algebraMap F E (ξ 1) * D.θ, ?_⟩
    exact (D.mkE_rt (ξ 0) (ξ 1)).symm⟩
  invFun y := ⟨D.coE y.1, by
    obtain ⟨_, z, rfl⟩ := y
    exact mem_vecLattice.2 ⟨fun i => D.b.repr z i, funext fun i => (D.co_rt z i).symm⟩⟩
  left_inv g := Subtype.ext (D.coE.apply_symm_apply g.1)
  right_inv y := Subtype.ext (D.coE.symm_apply_apply y.1)

open GroundTheory.Automorphic.FourierWhittaker in
theorem UpperTheory.integral_unipotentCoordinates_eq_zero_of_cuspidal :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (f : GL (Fin 2) (A E) → ℂ), Pp.Lf f →
        (∀ g, ∫ b in fundamentalSet E, f (gl (nU b) * g) ∂(adeleMeasure E) = 0) →
        ∀ h, ∫ u in FS2 ℚ, f (nE D u * h) ∂(adeleMeasurePi ℚ) = 0 := by
  intro E _ _ D Φ hL h0 h
  have hl := hL.2
  let β : (Fin 2 → A ℚ) ≃ₜ+ A E := D.coE.symm
  let m := β.toHomeomorph.toMeasurableEquiv
  haveI : (adeleMeasurePi ℚ (ι := Fin 2)).IsAddHaarMeasure := inferInstanceAs (Measure.pi fun _ : Fin 2 => adeleMeasure ℚ).IsAddHaarMeasure
  haveI : ((adeleMeasurePi ℚ (ι := Fin 2)).map m).IsAddHaarMeasure := β.isAddHaarMeasure_map (adeleMeasurePi ℚ)
  have hF : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 E) E) (m '' FS2 ℚ) ((adeleMeasurePi ℚ (ι := Fin 2)).map m) :=
    (isAddFundamentalDomain_vecDomain (K := ℚ) (ι := Fin 2)).image_of_equiv m.toEquiv
      (MeasurePreserving.symm m ⟨m.measurable, rfl⟩).quasiMeasurePreserving (latE' D).symm
      fun y x => by
        change β (D.coE y.1 + x) = y.1 + β x
        rw [map_add (f := _)]
        congr 1
        exact D.coE.symm_apply_apply y.1
  have hF' : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 E) E) (m '' FS2 ℚ) (adeleMeasure E) :=
    hF.mono (Measure.absolutelyContinuous_isAddHaarMeasure _ _)
  have hper : ∀ (g : AdeleRing.principalSubgroup (𝓞 E) E) (x : A E),
      Φ (gl (nU (g +ᵥ x)) * h) = Φ (gl (nU x) * h) := by
    rintro ⟨_, k, rfl⟩ x
    obtain ⟨γ, hγ⟩ := Pp.rat_n k
    change Φ (gl (nU (rt k + x)) * h) = _
    rw [Pp.n_add, ← hγ, mul_assoc, hl]
  haveI : Countable (AdeleRing.principalSubgroup (𝓞 E) E) := (latE' D).symm.injective.countable
  have h1 := (isAddFundamentalDomain_fundamentalSet E).setIntegral_eq hF' (f := fun x => Φ (gl (nU x) * h)) hper
  have h2 : ∫ x in fundamentalSet E, Φ (gl (nU x) * h) ∂(adeleMeasure E) = 0 := h0 h
  have hc := (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (adeleMeasure E) ((adeleMeasurePi ℚ (ι := Fin 2)).map m)).ne'
  rw [h1, Measure.isAddLeftInvariant_eq_smul (adeleMeasure E) ((adeleMeasurePi ℚ (ι := Fin 2)).map m), Measure.restrict_smul,
    integral_smul_nnreal_measure, m.measurableEmbedding.setIntegral_map, m.injective.preimage_image] at h2
  exact (smul_eq_zero.1 h2).resolve_left hc
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (Eig EigAt)
open scoped ComplexOrder

theorem UpperTheory.eigAt_cmDatumOperator_of_eigAt :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (φ : GL (Fin 2) (A E) → ℂ) (w : H.P E) (B : Multiset ℂˣ), Continuous φ → EigAt w B φ → EigAt w B (Wo D φ) := by
  intro E _ _ D φ w B hφ hB g
  have hnE : Continuous (nE D) := by
    have hmkE : Continuous fun x : Fin 2 → A ℚ => D.mkE (x 0) (x 1) :=
      (AdeleBaseChange.continuous_adeleMap.comp (continuous_apply 0)).add
        ((AdeleBaseChange.continuous_adeleMap.comp (continuous_apply 1)).mul continuous_const)
    exact (UpperTheory.ConvolutionTheory.R2.M.continuous_gl.comp
      UpperTheory.ConvolutionTheory.R2.M.continuous_nU).comp hmkE
  have hψ : Continuous (ψ (F := ℚ)) := continuous_subtype_val.comp continuous_adelicChar
  have hi : ∀ h : GL (Fin 2) (A E),
      IntegrableOn (fun x : Fin 2 → A ℚ => φ (nE D x * h) * ψ (x 1)) (FS2 ℚ) (adeleMeasurePi ℚ) := by
    intro h
    obtain ⟨C, hC, hEC⟩ : ∃ C, IsCompact C ∧ fundamentalSet ℚ ⊆ C :=
      ⟨closure (fundamentalSetInfinite ℚ) ×ˢ _,
        (isCompact_closure_fundamentalSetInfinite ℚ).prod (isCompact_integralFiniteAdeles ℚ),
        fun x hx => ⟨subset_closure hx.1, hx.2⟩⟩
    have hK : IsCompact (Set.univ.pi fun _ : Fin 2 => C) := isCompact_univ_pi fun _ => hC
    have hc : Continuous fun x : Fin 2 → A ℚ => φ (nE D x * h) * ψ (x 1) :=
      (hφ.comp (hnE.mul continuous_const)).mul (hψ.comp (continuous_apply 1))
    exact (hc.continuousOn.integrableOn_compact hK).mono_set fun x hx i hi => hEC (hx i hi)
  let G (x : Fin 2 → A ℚ) (y : GL (Fin 2) (w.adicCompletion E)) :=
    φ (nE D x * (g * finGL E 2 (locGL E 2 w y)))
  have hG (x : Fin 2 → A ℚ) : Eig w B (G x) := by
    simpa only [G, mul_assoc] using hB (nE D x * g)
  have hGi (z : GL (Fin 2) (w.adicCompletion E)) :
      Integrable (fun x => G x z * ψ (x 1)) ((adeleMeasurePi ℚ).restrict (FS2 ℚ)) := hi _
  change Eig w B (fun y => ∫ x in FS2 ℚ, G x y * ψ (x 1) ∂(adeleMeasurePi ℚ))
  refine ⟨(hB 1).card, fun y k hk => by simp only [fun x => (hG x).inv y k hk],
    fun ϖ hϖ j hj y => ?_⟩
  have hf := Formalism.UG.P.finite_support_cosets (Formalism.UG.Final.GLintComm E w 2)
    (GlobalTheory.LFun.Tj_mem_hecke (n := 2) hϖ j).2
  have hs (f : GL (Fin 2) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w (n := 2) → ℂ) :
      ∑ᶠ c, Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov E w) ϖ j c.out * f c =
        ∑ c ∈ hf.toFinset, Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov E w) ϖ j c.out * f c := by
    refine finsum_eq_sum_of_support_subset _ fun c hc => ?_
    rw [Set.Finite.coe_toFinset]
    exact left_ne_zero_of_mul hc
  rw [hs]
  simp only [← integral_const_mul]
  rw [← integral_finsetSum _ fun c _ => (hGi _).const_mul _]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have e := (hG x).eig ϖ hϖ j hj y
  rw [hs] at e
  simp only [← mul_assoc, ← e, Finset.sum_mul]
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private theorem abs_re (x : A ℚ) : |UpperTheory.ConvolutionTheory.RankTwoDescent.re x| = ‖x.1 Rat.infinitePlace‖ :=
  (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
    (IsTotallyReal.isReal Rat.infinitePlace)).norm_map_of_map_zero (map_zero _) (x.1 Rat.infinitePlace)

open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction in
theorem UpperTheory.exists_rat_mul_idele_finitePart_mem_compact_of_le_norm :
    ∀ c : ℝ, 0 < c → ∃ (S : Set (A ℚ)ˣ) (Bu : ℝ), IsCompact S ∧ 1 ≤ Bu ∧ ∀ a : (A ℚ)ˣ, c ≤ ab a →
        ∃ (q : ℚ) (a' u : (A ℚ)ˣ), q ≠ 0 ∧ (a' : A ℚ) = rt q * (a : A ℚ) ∧ u ∈ S ∧ (a' : A ℚ).2 = (u : A ℚ).2 ∧
          ((a'⁻¹ : (A ℚ)ˣ) : A ℚ).2 = ((u⁻¹ : (A ℚ)ˣ) : A ℚ).2 ∧ Bu⁻¹ ≤ |UpperTheory.ConvolutionTheory.RankTwoDescent.re (a' : A ℚ)| ∧
          |UpperTheory.ConvolutionTheory.RankTwoDescent.re (a' : A ℚ)| ≤ Bu * (ab a / c) := by
  intro c hc
  obtain ⟨S, hS, hSm⟩ := exists_isCompact_mul_mem_of_ideleModule_mem_Icc (K := ℚ) hc c
  have hv : Continuous fun u : IdeleGroup ℚ => ((u : IdeleGroup ℚ) : A ℚ) := Units.continuous_val
  have hi : Continuous fun u : IdeleGroup ℚ => (((u⁻¹ : IdeleGroup ℚ)) : A ℚ) := Units.continuous_coe_inv
  have hcont : Continuous fun u : IdeleGroup ℚ => ‖((u : IdeleGroup ℚ) : A ℚ).1 Rat.infinitePlace‖ +
      ‖(((u⁻¹ : IdeleGroup ℚ) : A ℚ)).1 Rat.infinitePlace‖ :=
    (continuous_norm.comp ((continuous_apply _).comp (continuous_fst.comp hv))).add
      (continuous_norm.comp ((continuous_apply _).comp (continuous_fst.comp hi)))
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn hcont.continuousOn
  set b := max M 1 with hb
  have hb1 : 1 ≤ b := le_max_right _ _
  have hb0 : 0 < b := one_pos.trans_le hb1
  refine ⟨S, b, hS, hb1, fun a ha => ?_⟩
  have hx : 1 ≤ ab a / c := (one_le_div hc).2 ha
  set s := ab a / c with hsdef
  have hs0 : 0 < s := one_pos.trans_le hx
  set p : IdeleGroup ℚ := posIdele s hs0 with hp
  have hm : (IdeleGroup.ideleModule ℚ (p⁻¹ * a) : ℝ) = c := by
    have h1 : (IdeleGroup.ideleModule ℚ (p⁻¹ * a) : ℝ) =
        ((IdeleGroup.ideleModule ℚ p : ℝ))⁻¹ * (IdeleGroup.ideleModule ℚ a : ℝ) := by
      simp [map_mul, map_inv]
    have h2 : (0 : ℝ) < ab a := hc.trans_le ha
    rw [h1, hp, ideleModule_posIdele, Module.finrank_self, pow_one]
    change (ab a / c)⁻¹ * ab a = c
    field_simp
  obtain ⟨t, ht⟩ := hSm _ hm.ge hm.le
  set u := IdeleGroup.diagonal ℚ t * (p⁻¹ * a) with hu
  have hau : IdeleGroup.diagonal ℚ t * a = p * u := by
    rw [hu, mul_left_comm, mul_inv_cancel_left]
  have hp2 : (((p : IdeleGroup ℚ) : A ℚ)).2 = 1 := by
    apply RestrictedProduct.ext
    intro v
    exact posIdele_finite s hs0 v
  have hpi2 : (((p⁻¹ : IdeleGroup ℚ) : A ℚ)).2 = 1 := by
    have e : (((p⁻¹ : IdeleGroup ℚ) : A ℚ)).2 * (((p : IdeleGroup ℚ) : A ℚ)).2 = 1 :=
      congrArg Prod.snd (Units.inv_mul p)
    rwa [hp2, mul_one] at e
  have hre : |UpperTheory.ConvolutionTheory.RankTwoDescent.re (((p * u : IdeleGroup ℚ)) : A ℚ)| = s * ‖((u : IdeleGroup ℚ) : A ℚ).1 Rat.infinitePlace‖ := by
    rw [abs_re]
    have e1 : (((p * u : IdeleGroup ℚ)) : A ℚ).1 Rat.infinitePlace =
        ((p : IdeleGroup ℚ) : A ℚ).1 Rat.infinitePlace * ((u : IdeleGroup ℚ) : A ℚ).1 Rat.infinitePlace := by
      simp only [Units.val_mul]
      rfl
    rw [e1, norm_mul, hp, norm_posIdele_infinite]
  have hbd := hM u ht
  have hn1 : 0 ≤ ‖((u : IdeleGroup ℚ) : A ℚ).1 Rat.infinitePlace‖ := norm_nonneg _
  have hn2 : 0 ≤ ‖(((u⁻¹ : IdeleGroup ℚ) : A ℚ)).1 Rat.infinitePlace‖ := norm_nonneg _
  rw [Real.norm_of_nonneg (by positivity)] at hbd
  have hMb : M ≤ b := le_max_left _ _
  have hprod : ‖((u : IdeleGroup ℚ) : A ℚ).1 Rat.infinitePlace‖ *
      ‖(((u⁻¹ : IdeleGroup ℚ) : A ℚ)).1 Rat.infinitePlace‖ = 1 := by
    rw [← norm_mul]
    have e : ((u : IdeleGroup ℚ) : A ℚ).1 * (((u⁻¹ : IdeleGroup ℚ) : A ℚ)).1 = 1 :=
      congrArg Prod.fst (Units.mul_inv u)
    have e' := congrFun e Rat.infinitePlace
    change ((u : IdeleGroup ℚ) : A ℚ).1 Rat.infinitePlace * (((u⁻¹ : IdeleGroup ℚ) : A ℚ)).1 Rat.infinitePlace = 1 at e'
    rw [e', norm_one]
  refine ⟨(t : ℚ), p * u, u, t.ne_zero, ?_, ht, ?_, ?_, ?_, ?_⟩
  · have h1 : ((IdeleGroup.diagonal ℚ t : IdeleGroup ℚ) : A ℚ) = rt (t : ℚ) := IdeleGroup.coe_diagonal _ _
    rw [← hau, Units.val_mul, h1]
  · change (((p * u : IdeleGroup ℚ)) : A ℚ).2 = _
    rw [Units.val_mul]
    change (((p : IdeleGroup ℚ) : A ℚ)).2 * _ = _
    rw [hp2, one_mul]
  · change ((((p * u)⁻¹ : IdeleGroup ℚ)) : A ℚ).2 = _
    rw [_root_.mul_inv_rev, Units.val_mul]
    change _ * (((p⁻¹ : IdeleGroup ℚ) : A ℚ)).2 = _
    rw [hpi2, mul_one]
  · rw [hre, inv_le_iff_one_le_mul₀ hb0]
    have h1 : 1 ≤ ‖((u : IdeleGroup ℚ) : A ℚ).1 Rat.infinitePlace‖ * b := by
      rw [← hprod]
      exact mul_le_mul_of_nonneg_left (by linarith) hn1
    nlinarith
  · rw [hre, mul_comm b]
    exact mul_le_mul_of_nonneg_left (by linarith) hs0.le
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private theorem sb_le : schwartzBruhatPi (K := ℚ) (ι := Fin 2) ≤ GroundTheory.Automorphic.Adele2.schwartzBruhat2 ℚ := by
  refine Submodule.span_le.mpr ?_
  rintro F ⟨φ, g, hg, rfl⟩
  exact GroundTheory.Automorphic.Adele2.schwartzBruhatTensor2_mem φ
    (show _ ∧ _ from (mem_finiteSchwartzBruhatPi ℚ).mp hg)

private theorem cont_iy : Continuous fun t : ℝ => iy (Real.exp t) := by
  let u : ℝ → (TR.Rinf ℚ)ˣ := fun t => ⟨fun _ => Real.exp t, fun _ => (Real.exp t)⁻¹,
    funext fun _ => mul_inv_cancel₀ (Real.exp_ne_zero t), funext fun _ => inv_mul_cancel₀ (Real.exp_ne_zero t)⟩
  have hu : Continuous u := by
    refine Units.continuous_iff.mpr ⟨continuous_pi fun _ => Real.continuous_exp, continuous_pi fun _ => ?_⟩
    exact Real.continuous_exp.inv₀ Real.exp_ne_zero
  have e : (fun t : ℝ => iy (Real.exp t)) = fun t => TR.infId ℚ (u t) := by
    funext t
    exact dite_eq_right (Real.exp_ne_zero t)
  rw [e]
  exact (TR.continuous_infId ℚ).comp hu

private theorem summable_row {Φ : (Fin 2 → A ℚ) → ℂ} (hΦ : Φ ∈ schwartzBruhatPi (K := ℚ) (ι := Fin 2))
    (a : (A ℚ)ˣ) (g : GL (Fin 2) (A ℚ)) :
    Summable fun ξ : Rw ℚ => Φ fun j => (a : A ℚ) * ((fun i => rt (ξ.1 i)) ᵥ* g.val) j := by
  have hs := (GroundTheory.Automorphic.Adele2.poisson_rightTranslate (sb_le hΦ)
    (Matrix.GeneralLinearGroup.scalar (Fin 2) a * g)).1.of_norm
  have hv : ((Matrix.GeneralLinearGroup.scalar (Fin 2) a * g : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ))
      = (a : A ℚ) • g.val := by
    ext i j
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.smul_apply]
  refine (hs.comp_injective (Subtype.val_injective (p := fun r : Fin 2 → ℚ => r ≠ 0))).congr fun ξ => ?_
  simp only [Function.comp_apply]
  rw [hv, Matrix.vecMul_smul]
  rfl

theorem UpperTheory.measurable_thetaSeries_comp_continuous :
    ∀ (Φ : (Fin 2 → A ℚ) → ℂ), Φ ∈ schwartzBruhatPi (K := ℚ) (ι := Fin 2) → ∀ {X : Type} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
        (τ : X → ℝ) (h : X → GL (Fin 2) (A ℚ)), Continuous τ → Continuous h → Measurable fun x => ThR Φ (τ x) (h x) := by
  intro Φ hΦ X _ _ _ τ h hτ hh
  have hc := continuous_of_mem_schwartzBruhatPi hΦ
  have ha : Continuous fun x => ((iy (Real.exp (τ x)) : (A ℚ)ˣ) : A ℚ) :=
    Units.continuous_val.comp (cont_iy.comp hτ)
  have hg : Continuous fun x => (h x).val := Units.continuous_val.comp hh
  have hterm : ∀ ξ : Rw ℚ, Continuous fun x =>
      Φ fun j => ((iy (Real.exp (τ x)) : (A ℚ)ˣ) : A ℚ) * ((fun i => rt (ξ.1 i)) ᵥ* (h x).val) j := fun ξ =>
    hc.comp (continuous_pi fun j => ha.mul
      ((continuous_apply j).comp (continuous_const.matrix_vecMul hg)))
  refine measurable_of_tendsto_metrizable' (Filter.atTop : Filter (Finset (Rw ℚ)))
    (f := fun (s : Finset (Rw ℚ)) x => ∑ ξ ∈ s,
      Φ fun j => ((iy (Real.exp (τ x)) : (A ℚ)ˣ) : A ℚ) * ((fun i => rt (ξ.1 i)) ᵥ* (h x).val) j)
    (fun s => (continuous_finsetSum s fun ξ _ => hterm ξ).measurable) ?_
  exact tendsto_pi_nhds.mpr fun x => (summable_row hΦ (iy (Real.exp (τ x))) (h x)).hasSum
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ComplexOrder

private lemma conv_prime_pow (a a' : ℕ → ℂ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    LSeries.convolution a a' (p ^ k) =
      PowerSeries.coeff k (PowerSeries.mk (fun k => a (p ^ k)) * PowerSeries.mk (fun k => a' (p ^ k))) := by
  rw [LSeries.convolution_def, PowerSeries.coeff_mul]
  simp only [PowerSeries.coeff_mk]
  rw [Nat.sum_divisorsAntidiagonal (fun x y => a x * a' y), Nat.divisors_prime_pow hp, Finset.sum_map,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => a (p ^ i) * a' (p ^ j))]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  simp [Nat.pow_div hik hp.pos]

private lemma toAF_mult (a : ℕ → ℂ) (h1 : a 1 = 1)
    (hm : ∀ m n, m.Coprime n → a (m * n) = a m * a n) :
    (toArithmeticFunction a).IsMultiplicative := by
  refine ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr ⟨?_, fun {m n} hm0 hn0 hmn => ?_⟩
  · simp [toArithmeticFunction, h1]
  · simp [toArithmeticFunction, hm0, hn0, hm m n hmn]

private lemma conv_nonneg_of_pp (b : ArithmeticFunction ℂ) (hb : b.IsMultiplicative)
    (hpp : ∀ p k : ℕ, p.Prime → 0 ≤ b (p ^ k)) (n : ℕ) : 0 ≤ b n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [hb.multiplicative_factorization _ hn]
  exact Finset.prod_nonneg fun p hp => hpp p _ (Nat.prime_of_mem_primeFactors (by simpa using hp))

theorem UpperTheory.false_of_landau_nonneg_euler_factors_entire :
    ∀ (a a' : ℕ → ℂ) (N : ℕ), 0 < N → a 1 = 1 → a' 1 = 1 → (∀ m n, m.Coprime n → a (m * n) = a m * a n) →
        (∀ m n, m.Coprime n → a' (m * n) = a' m * a' n) → (∀ p k : ℕ, p.Prime → p ∣ N → a (p ^ (k + 1)) = 0) →
        (∀ p k : ℕ, p.Prime → p ∣ N → a' (p ^ (k + 1)) = 0) →
        (∀ p : ℕ, p.Prime → ¬ p ∣ N →
          (∀ k, 0 ≤ PowerSeries.coeff k (PowerSeries.mk (fun k => a (p ^ k)) * PowerSeries.mk (fun k => a' (p ^ k)))) ∧
          1 ≤ PowerSeries.coeff 4 (PowerSeries.mk (fun k => a (p ^ k)) * PowerSeries.mk (fun k => a' (p ^ k)))) →
        (∀ s : ℂ, 4 < s.re → LSeriesSummable a s) → (∀ s : ℂ, 4 < s.re → LSeriesSummable a' s) → Entire a → Entire a' → Landau → False := by
  intro a a' N hN h1 h1' hm hm' hbad hbad' hgood hs hs' hE hE' hL
  have hmul : (toArithmeticFunction a * toArithmeticFunction a').IsMultiplicative :=
    (toAF_mult a h1 hm).mul (toAF_mult a' h1' hm')
  have hcoe : ∀ n, LSeries.convolution a a' n = (toArithmeticFunction a * toArithmeticFunction a') n :=
    fun n => rfl
  have hone : LSeries.convolution a a' 1 = 1 := by rw [hcoe, hmul.map_one]
  have hpp : ∀ p k : ℕ, p.Prime → 0 ≤ LSeries.convolution a a' (p ^ k) := by
    intro p k hp
    by_cases hpN : p ∣ N
    · rcases k with _ | k
      · simp [hone]
      · have hz : LSeries.convolution a a' (p ^ (k + 1)) = 0 := by
          rw [conv_prime_pow a a' hp, PowerSeries.coeff_mul]
          refine Finset.sum_eq_zero fun x hx => ?_
          obtain ⟨i, j⟩ := x
          have hij : i + j = k + 1 := by simpa using hx
          rcases i with _ | i
          · have hj : j = k + 1 := by omega
            subst hj
            simp [hbad' p k hp hpN]
          · simp [hbad p i hp hpN]
        exact hz.ge
    · rw [conv_prime_pow a a' hp]
      exact (hgood p hp hpN).1 k
  have hnn : ∀ n, 0 ≤ LSeries.convolution a a' n :=
    conv_nonneg_of_pp _ hmul hpp
  have hsum : ∀ s : ℂ, 4 < s.re → LSeriesSummable (LSeries.convolution a a') s :=
    fun s h => (hs s h).convolution (hs' s h)
  have hent : Entire (LSeries.convolution a a') := by
    obtain ⟨F, hF, hFe⟩ := hE
    obtain ⟨G, hG, hGe⟩ := hE'
    refine ⟨fun s => F s * G s, hF.mul hG, fun s h => ?_⟩
    rw [LSeries_convolution' (hs s h) (hs' s h)]
    show F s * G s = _
    rw [hFe s h, hGe s h]
  have hfin := hL _ hnn hone hsum hent
  have hfin' : ((fun p : ℕ => p ^ 4) ⁻¹' {n | 1 ≤ LSeries.convolution a a' n}).Finite :=
    hfin.preimage fun x _ y _ h => (Nat.pow_left_inj (by norm_num)).1 h
  obtain ⟨M, hM⟩ := hfin'.bddAbove
  obtain ⟨p, hpl, hp⟩ := Nat.exists_infinite_primes (max M N + 1)
  have hpN : ¬ p ∣ N := fun h => by
    have := Nat.le_of_dvd hN h
    have := le_max_right M N
    omega
  have hmem : p ∈ (fun p : ℕ => p ^ 4) ⁻¹' {n | 1 ≤ LSeries.convolution a a' n} := by
    show 1 ≤ LSeries.convolution a a' (p ^ 4)
    rw [conv_prime_pow a a' hp]
    exact (hgood p hp hpN).2
  have := hM hmem
  have := le_max_left M N
  omega
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

theorem UpperTheory.automorphicForm_baseChange_ratSL2_mul_invariant :
    ∀ {E : Type} [Field E] [NumberField E] (D : Dat ℚ E) (ω : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ), admitted D ω φ →
        ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℚ) (g : G1 ℚ) (h : GL (Fin 2) (A ℚ)), φ (em E (gl (ratS ℚ γ * g) * h)) = φ (em E (gl g * h)) := by
  intro E _ _ D ω φ hφ γ g h
  have key : em E (gl (ratS ℚ γ)) =
      ratGL E 2 (Matrix.GeneralLinearGroup.map (algebraMap ℚ E) (Matrix.SpecialLinearGroup.toGL γ)) := by
    apply Units.ext
    ext i j
    simpa [UpperTheory.ConvolutionTheory.RankTwoDescent.em, gl, ratS, ratGL, Matrix.GeneralLinearGroup.map, Matrix.SpecialLinearGroup.map, Matrix.SpecialLinearGroup.toGL] using
      (AdeleBaseChange.adeleMap_algebraMap (K := ℚ) (L := E) (γ.1 i j))
  have e : gl (ratS ℚ γ * g) * h = gl (ratS ℚ γ) * (gl g * h) := by
    rw [gl, gl, map_mul, mul_assoc]
  rw [e, map_mul, key]
  exact hφ.left _ _
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

theorem UpperTheory.continuous_GL2BaseChange_diagUnit_infiniteIdele :
    ∀ (E : Type) [Field E] [NumberField E], Continuous (em E) ∧ Continuous (dM : (A ℚ)ˣ → GL (Fin 2) (A ℚ)) ∧ Continuous (fun t : ℝ => iy (Real.exp t)) := by
  intro E _ _
  refine ⟨?_, ?_, ?_⟩
  · have hc : Continuous (AdeleBaseChange.adeleMap ℚ E) := AdeleBaseChange.continuous_adeleMap
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · exact Units.continuous_val.matrix_map hc
    · exact Units.continuous_coe_inv.matrix_map hc
  · refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · refine continuous_matrix fun i j => ?_
      fin_cases i <;> fin_cases j
      · exact continuous_const
      · exact continuous_const
      · exact continuous_const
      · exact Units.continuous_val
    · refine continuous_matrix fun i j => ?_
      fin_cases i <;> fin_cases j
      · exact continuous_const
      · exact continuous_const
      · exact continuous_const
      · exact Units.continuous_coe_inv
  · let u : ℝ → (TR.Rinf ℚ)ˣ := fun t =>
      ⟨fun _ => Real.exp t, fun _ => (Real.exp t)⁻¹,
        funext fun _ => mul_inv_cancel₀ (Real.exp_ne_zero t),
        funext fun _ => inv_mul_cancel₀ (Real.exp_ne_zero t)⟩
    have hu : Continuous u := by
      refine Units.continuous_iff.2 ⟨?_, ?_⟩
      · exact continuous_pi fun _ => Real.continuous_exp
      · exact continuous_pi fun _ => (Real.continuous_exp.inv₀ Real.exp_ne_zero)
    have he : (fun t : ℝ => iy (Real.exp t)) = fun t => TR.infId ℚ (u t) := by
      funext t
      simp only [iy, dif_neg (Real.exp_ne_zero t)]
      rfl
    rw [he]
    exact (TR.continuous_infId ℚ).comp hu
end
