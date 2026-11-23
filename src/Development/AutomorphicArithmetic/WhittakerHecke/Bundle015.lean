module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SplitAt
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle003
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1138
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.HeckeExpl
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.Bundle002
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.IsotypQuot
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaLiftTrivialOrbitTermsVanish
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPosNatMemOpenAdeleSubgroup
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.NumberField.Discriminant.Different
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
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.Bundle001
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.ThInf
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ConjInv

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Xg
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem finsum_Tj_eq {E : Type} [Field E] [NumberField E] {w : H.P E} {ϖ : w.adicCompletion E}
    (hϖ : Formalism.UG.IsUnifV E w ϖ) (j : ℕ) :
    ∃ t : Finset (GL (Fin 2) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w (n := 2)),
      ∀ F : GL (Fin 2) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w (n := 2) → ℂ,
        ∑ᶠ x, Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov E w) ϖ j x.out * F x =
          ∑ x ∈ t, Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov E w) ϖ j x.out * F x := by
  have hf := Formalism.UG.P.finite_support_cosets (Formalism.UG.Final.GLintComm E w 2)
    (GlobalTheory.LFun.Tj_mem_hecke (n := 2) hϖ j).2
  refine ⟨hf.toFinset, fun F => finsum_eq_sum_of_support_subset _ fun x hx => ?_⟩
  rw [Set.Finite.coe_toFinset]
  exact left_ne_zero_of_mul hx

theorem UpperTheory.fixed_and_heckeEigen_of_finset_linearCombination :
    ∀ (E : Type) [Field E] [NumberField E] (w : H.P E) (ι : Type) (s : Finset ι) (c : ι → ℂ) (φ : ι → GL (Fin 2) (A E) → ℂ) (B : Multiset ℂˣ), s.Nonempty → (∀ i, H.Fix w (φ i)) → (∀ i, EigAt w B (φ i)) → H.Fix w (fun g => ∑ i ∈ s, c i * φ i g) ∧ EigAt w B (fun g => ∑ i ∈ s, c i * φ i g) := by
  intro E _ _ w ι s c φ B hs hF hE
  obtain ⟨i₀, -⟩ := hs
  refine ⟨fun g k hk => ?_, fun g => ⟨(hE i₀ g).card, fun y k hk => ?_, fun ϖ hϖ j hj y => ?_⟩⟩
  · simp only [fun i => hF i g k hk]
  · simp only [fun i => (hE i g).inv y k hk]
  · obtain ⟨t, ht⟩ := finsum_Tj_eq (w := w) hϖ j
    rw [ht]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e := (hE i g).eig ϖ hϖ j hj y
    rw [ht] at e
    rw [mul_left_comm, ← e, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => mul_left_comm _ _ _
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

theorem UpperTheory.lie_action_preserves_satake_eigen_at_place :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (w : H.P E) (B : Multiset ℂˣ) (f : Sm E 2) (X : Lie E 2), UpperTheory.V.Af.Smo.EigAt w B f.1 → UpperTheory.V.Af.Smo.EigAt w B (lie E 2 X f).1 := by
  intro E _ _ _ w B f X hf g
  have hc : ∀ (k : GL (Fin 2) (Af E)) (φ : Sm E 2) (x : GA E 2),
      (lie E 2 X φ).1 (x * finGL E 2 k) = (lie E 2 X (GlobalTheory.CuspRep.rt E 2 (finGL E 2 k) φ)).1 x := by
    intro k φ x
    have h := LinearMap.congr_fun (lie_rt_fin X k) φ
    exact (congrArg (fun ψ : Sm E 2 => ψ.1 x) h).symm
  have hev : ∀ (k : GA E 2) (φ : Sm E 2) (x : GA E 2), (GlobalTheory.CuspRep.rt E 2 k φ).1 x = φ.1 (x * k) :=
    fun _ _ _ => rfl
  refine ⟨(hf 1).card, ?_, ?_⟩
  · intro y k hk
    have hfix : GlobalTheory.CuspRep.rt E 2 (finGL E 2 (locGL E 2 w k)) f = f := by
      refine Subtype.ext (funext fun x => ?_)
      have h := (hf x).inv 1 k hk
      simp only [one_mul, map_one, mul_one] at h
      rw [hev]
      exact h
    have e1 : g * finGL E 2 (locGL E 2 w (y * k)) =
        g * finGL E 2 (locGL E 2 w y) * finGL E 2 (locGL E 2 w k) := by
      simp only [map_mul, mul_assoc]
    show (lie E 2 X f).1 (g * finGL E 2 (locGL E 2 w (y * k))) = (lie E 2 X f).1 (g * finGL E 2 (locGL E 2 w y))
    rw [e1, hc, hfix]
  · intro ϖ hϖ j hj x
    have hfin := (GlobalTheory.TjCount.tj_cosets_finite_card_le E w 2 ϖ hϖ j hj).1
    have hsum : ∀ W : GL (Fin 2) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w (n := 2) → ℂ,
        ∑ᶠ c, Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov E w) ϖ j c.out * W c =
          ∑ c ∈ hfin.toFinset, Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov E w) ϖ j c.out * W c := by
      intro W
      refine finsum_eq_sum_of_support_subset _ fun c hc' => ?_
      rw [Set.Finite.coe_toFinset]
      exact fun h0 => hc' (by simp [h0])
    have key : ∑ c ∈ hfin.toFinset, Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov E w) ϖ j c.out •
          GlobalTheory.CuspRep.rt E 2 (finGL E 2 (locGL E 2 w c.out)) f =
        GlobalTheory.LFun.satEig (Formalism.UG.qV E w) 2 B j • f := by
      refine Subtype.ext (funext fun z => ?_)
      have h := (hf z).eig ϖ hϖ j hj 1
      simp only [one_mul, map_one, mul_one] at h
      rw [hsum fun c => f.1 (z * finGL E 2 (locGL E 2 w c.out))] at h
      simpa [Submodule.coe_sum, Finset.sum_apply, hev] using h
    have h2 := congrArg (fun ψ : Sm E 2 => (lie E 2 X ψ).1 (g * finGL E 2 (locGL E 2 w x))) key

    simp only [map_sum, map_smul, Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply,
    smul_eq_mul] at h2
    rw [hsum fun c => (lie E 2 X f).1 (g * finGL E 2 (locGL E 2 w (x * c.out)))]
    rw [← h2]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_mul, map_mul, ← mul_assoc, hc]
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

theorem UpperTheory.eigenform_central_uniformizer_eq_satake_product :
    ∀ (K : Type) [Field K] [NumberField K] (v : H.P K) (ϖ : (H.Kv v)ˣ), H.IsU ϖ → ∀ (α β : ℂˣ) (f : GL (Fin 2) (A K) → ℂ),
          EigAt v {α, β} f → ∀ h, f (Matrix.GeneralLinearGroup.scalar (Fin 2) (H.idl v ϖ) * h) = (α : ℂ) * β * f h := by
  intro K _ _ v ϖ hϖ α β f hEig h
  obtain ⟨R, -, -, hR⟩ := H.heckeExpl K v ϖ hϖ
  have hc := (hR α β _ (hEig h) 1).2
  have hcomm : Matrix.GeneralLinearGroup.scalar (Fin 2) (H.idl v ϖ) * h =
      h * Matrix.GeneralLinearGroup.scalar (Fin 2) (H.idl v ϖ) :=
    Units.ext (Matrix.scalar_commute ((H.idl v ϖ : (A K)ˣ) : A K) (fun r => Commute.all _ r) (h : Matrix (Fin 2) (Fin 2) (A K))).eq
  rw [hcomm]
  simp only [one_mul, map_one, mul_one] at hc
  rw [← (H.lcLaws K v).2.2.2.2.1]
  exact hc
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

theorem UpperTheory.whittaker_unipotent_mul_eq_additiveChar_mul :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (f : GL (Fin 2) (A E) → ℂ), Pp.Lf f → ∀ (v : Fin 2 → A ℚ) (h : GL (Fin 2) (A E)),
        Wo D f (nE D v * h) = ψ (-(v 1)) * Wo D f h := by
  intro E _ _ D f hf v h
  have hadd : ∀ u w : Fin 2 → A ℚ, nE D (u + w) = nE D u * nE D w := fun u w => by
    simp only [nE, Pi.add_apply, D.mkE_add, Pp.n_add]
  let G : (Fin 2 → A ℚ) → ℂ := fun u => f (nE D u * h) * ψ (u 1)
  have hper : ∀ ξ ∈ GroundTheory.Automorphic.FourierWhittaker.vecLattice ℚ (Fin 2), ∀ x, G (ξ + x) = G x := by
    intro ξ hξ x
    obtain ⟨η, rfl⟩ := GroundTheory.Automorphic.FourierWhittaker.mem_vecLattice.1 hξ
    have e1 : D.mkE (rt (η 0) + x 0) (rt (η 1) + x 1) =
        rt (algebraMap ℚ E (η 0) + algebraMap ℚ E (η 1) * D.θ) + D.mkE (x 0) (x 1) := by
      rw [D.mkE_add, D.mkE_rt]
    change f (gl (nU (D.mkE (rt (η 0) + x 0) (rt (η 1) + x 1))) * h) * ψ (rt (η 1) + x 1) =
      f (gl (nU (D.mkE (x 0) (x 1))) * h) * ψ (x 1)
    rw [e1, hf.per, Pp.ψ_add, Pp.ψ_rt, one_mul]
  have key : ∫ u in FS2 ℚ, G (u + v) ∂(adeleMeasurePi ℚ) = ∫ u in FS2 ℚ, G u ∂(adeleMeasurePi ℚ) :=
    GroundTheory.Automorphic.FourierWhittaker.setIntegral_comp_add v hper
  have pt : ∀ u : Fin 2 → A ℚ, f (nE D u * (nE D v * h)) * ψ (u 1) = ψ (-(v 1)) * G (u + v) := by
    intro u
    have e2 : ψ (u 1) = ψ (-(v 1)) * ψ ((u + v) 1) := by
      rw [← Pp.ψ_add]
      congr 1
      simp only [Pi.add_apply]
      ring
    change _ = ψ (-(v 1)) * (f (nE D (u + v) * h) * ψ ((u + v) 1))
    rw [hadd, mul_assoc, e2]
    ring
  simp only [Wo, pt]
  rw [integral_const_mul]
  exact congrArg _ key
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

private theorem diff_top : differentIdeal ℤ (𝓞 ℚ) = ⊤ := by
  rw [← Ideal.absNorm_eq_one_iff, absNorm_differentIdeal ℚ (𝓞 ℚ), Rat.numberField_discr]
  rfl

private theorem int_of_inv (v : HeightOneSpectrum (𝓞 ℚ)) {z : v.adicCompletion ℚ}
    (hz : z ∈ GroundTheory.Global.localInvDifferent v) : z ∈ v.adicCompletionIntegers ℚ := by
  rw [GroundTheory.Global.mem_localInvDifferent_iff_valued, diff_top, FractionalIdeal.coeIdeal_top,
    FractionalIdeal.count_one, WithZero.exp_zero] at hz
  exact hz

theorem UpperTheory.exists_isCompact_annihilator_scaled_integralAdeles :
    ∀ N : ℕ, 0 < N → ∃ K : Set (FiniteAdeleRing (𝓞 ℚ) ℚ), IsCompact K ∧ ∀ x : FiniteAdeleRing (𝓞 ℚ) ℚ,
        (∀ b : FiniteAdeleRing (𝓞 ℚ) ℚ, (∀ v, b v ∈ v.adicCompletionIntegers ℚ) → ψ (((0, x * ((N : FiniteAdeleRing (𝓞 ℚ) ℚ) * b)) : A ℚ)) = 1) → x ∈ K := by
  intro N hN
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  set c : FiniteAdeleRing (𝓞 ℚ) ℚ := algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (N : ℚ)⁻¹ with hc
  have hcN : c * (N : FiniteAdeleRing (𝓞 ℚ) ℚ) = 1 := by
    have : (N : FiniteAdeleRing (𝓞 ℚ) ℚ) = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (N : ℚ) := by
      simp
    rw [this, hc, ← map_mul, inv_mul_cancel₀ hNq, map_one]
  refine ⟨(fun z => c * z) '' (integralFiniteAdeles (𝓞 ℚ) ℚ : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)),
    (GroundTheory.Global.isCompact_integralFiniteAdeles ℚ).image (continuous_const.mul continuous_id),
    fun x hx => ?_⟩
  refine ⟨x * (N : FiniteAdeleRing (𝓞 ℚ) ℚ), ?_, ?_⟩
  · intro v
    refine int_of_inv v ((GroundTheory.Global.forall_localAdelicChar_mul_eq_one_iff v _).mp fun a ha => ?_)
    have hb : ∀ u, GroundTheory.Global.finiteAdeleSingleAdd v a u ∈ u.adicCompletionIntegers ℚ := by
      intro u
      rcases eq_or_ne u v with rfl | hu
      · rwa [GroundTheory.Global.finiteAdeleSingleAdd_apply_self]
      · rw [GroundTheory.Global.finiteAdeleSingleAdd_apply_of_ne hu]
        exact zero_mem _
    have h := hx _ hb
    have e : x * ((N : FiniteAdeleRing (𝓞 ℚ) ℚ) * GroundTheory.Global.finiteAdeleSingleAdd v a) =
        GroundTheory.Global.finiteAdeleSingleAdd v (a * (x * (N : FiniteAdeleRing (𝓞 ℚ) ℚ)) v) := by
      rw [← GroundTheory.Global.finiteAdeleSingleAdd_mul]
      ring
    rw [e] at h
    have h' : ((GroundTheory.Global.localAdelicChar ℚ v (a * (x * (N : FiniteAdeleRing (𝓞 ℚ) ℚ)) v) : Circle) : ℂ) = 1 := h
    exact Circle.ext (by simpa using h')
  · show c * (x * (N : FiniteAdeleRing (𝓞 ℚ) ℚ)) = x
    rw [mul_comm x, ← mul_assoc, hcN, one_mul]
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

private theorem gln_val {E : Type} [Field E] [NumberField E] (b : A E) :
    (gl (nU b) : GL (Fin 2) (A E)).val = !![1, b; 0, 1] := rfl

private theorem nU_inv {E : Type} [Field E] [NumberField E] (b : A E) :
    (gl (nU b) : GL (Fin 2) (A E))⁻¹ = gl (nU (-b)) := by
  rw [inv_eq_iff_mul_eq_one]
  refine Units.ext ?_
  rw [Units.val_mul, gln_val, gln_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem cont_n {E : Type} [Field E] [NumberField E] :
    Continuous fun b : A E => (gl (nU b) : GL (Fin 2) (A E)) := by
  have hv : ∀ g : A E → A E, Continuous g →
      Continuous fun b : A E => ((gl (nU (g b)) : GL (Fin 2) (A E)) : Matrix (Fin 2) (Fin 2) (A E)) := by
    intro g hg
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [nU] <;> first | exact hg | exact continuous_const
  refine Units.continuous_iff.2 ⟨hv id continuous_id, ?_⟩
  simp only [nU_inv]
  exact hv _ continuous_neg

private theorem map_unipotent_eq_one {E S : Type} [Field E] [NumberField E] [CommRing S] (p : A E →+* S) (z : A E) (hz : p z = 0) :
    Matrix.GeneralLinearGroup.map p (gl (nU z)) = 1 := by
  refine Units.ext ?_
  ext i j
  change p ((gl (nU z) : GL (Fin 2) (A E)).val i j) = (1 : Matrix (Fin 2) (Fin 2) S) i j
  rw [gln_val]
  fin_cases i <;> fin_cases j <;> simp [hz]

private theorem pInf_mk {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (x : FiniteAdeleRing (𝓞 ℚ) ℚ) :
    pInf E (D.mkE 0 ((0, x) : A ℚ)) = 0 := by
  have h : pInf E (AdeleBaseChange.adeleMap ℚ E ((0, x) : A ℚ)) = 0 := by
    change (infEq E).symm (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (0 : InfiniteAdeleRing ℚ)) = 0
    rw [map_zero, map_zero]
  simp [Dat.mkE, h]

private theorem cont_mk {E : Type} [Field E] [NumberField E] (D : Dat ℚ E) :
    Continuous fun x : FiniteAdeleRing (𝓞 ℚ) ℚ => D.mkE 0 ((0, x) : A ℚ) := by
  have h : Continuous fun x : FiniteAdeleRing (𝓞 ℚ) ℚ => ((0, x) : A ℚ) :=
    continuous_const.prodMk continuous_id
  unfold Dat.mkE
  exact continuous_const.add ((AdeleBaseChange.continuous_adeleMap.comp h).mul continuous_const)

theorem UpperTheory.exists_level_unipotent_invariance_automorphicForm :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (f : Sm E 2), IsAutForm f →
        ∀ C : Set (GL (Fin 2) (A E)), IsCompact C → ∃ N : ℕ, 0 < N ∧ ∀ k ∈ C, ∀ b : FiniteAdeleRing (𝓞 ℚ) ℚ,
          (∀ v, b v ∈ v.adicCompletionIntegers ℚ) → ∀ G, f.1 (G * (gl (nU (D.mkE 0 ((0, (N : FiniteAdeleRing (𝓞 ℚ) ℚ) * b) : A ℚ))) * k)) = f.1 (G * k) := by
  intro E _ _ _ D f hf C hC
  let m : FiniteAdeleRing (𝓞 ℚ) ℚ → GL (Fin 2) (A E) := fun x => gl (nU (D.mkE 0 ((0, x) : A ℚ)))
  have hm : Continuous m := cont_n.comp (cont_mk D)
  have hm0 : m 0 = 1 := by
    have h0 : D.mkE 0 ((0, 0) : A ℚ) = 0 := by
      have h : D.mkE 0 ((0, 0) : A ℚ) = D.mkE 0 (0 : A ℚ) := rfl
      rw [h]
      unfold Dat.mkE
      rw [map_zero, zero_mul, add_zero]
    change gl (nU (D.mkE 0 ((0, 0) : A ℚ))) = 1
    rw [h0]
    refine Units.ext ?_
    rw [gln_val]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  let Φ : FiniteAdeleRing (𝓞 ℚ) ℚ × GL (Fin 2) (A E) → GL (Fin 2) (Af E) :=
    fun p => Matrix.GeneralLinearGroup.map (pFin E) (p.2⁻¹ * m p.1 * p.2)
  have hΦ : Continuous Φ :=
    (Continuous.units_map _ (continuous_id.matrix_map continuous_snd)).comp ((continuous_snd.inv.mul (hm.comp continuous_fst)).mul continuous_snd)
  have hO : IsOpen (Φ ⁻¹' {k | finRep E 2 k f = f}) := hf.level.preimage hΦ
  have hsub : ({0} : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)) ×ˢ C ⊆ Φ ⁻¹' {k | finRep E 2 k f = f} := by
    rintro ⟨x, k⟩ ⟨hx, -⟩
    have hx0 : x = 0 := hx
    subst hx0
    have e : Φ (0, k) = 1 := by
      change Matrix.GeneralLinearGroup.map (pFin E) (k⁻¹ * m 0 * k) = 1
      rw [hm0, mul_one, inv_mul_cancel, map_one]
    change finRep E 2 (Φ (0, k)) f = f
    rw [e, map_one]
    rfl
  obtain ⟨U, V, hU, hV, h0U, hCV, hUV⟩ := generalized_tube_lemma isCompact_singleton hC hO hsub
  have h0 : (0 : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ U := h0U rfl
  have key : ∀ᶠ d in 𝓝 (0 : FiniteAdeleRing (𝓞 ℚ) ℚ),
      ∀ z ∈ (integralFiniteAdeles (𝓞 ℚ) ℚ : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)), d * z ∈ U :=
    (isCompact_integralFiniteAdeles ℚ).eventually_forall_of_forall_eventually fun z _ =>
      (hU.preimage (continuous_fst.mul continuous_snd)).mem_nhds (by simpa using h0)
  obtain ⟨n, hn⟩ := ((GlobalTheory.AdelicFactorial.tendsto_factorial_finiteAdele ℚ).eventually key).exists
  refine ⟨n.factorial, n.factorial_pos, fun k hk b hb G => ?_⟩
  have hx := hn b hb
  have hS : finRep E 2 (Φ (_, k)) f = f := hUV (Set.mk_mem_prod hx (hCV hk))
  have hy : finGL E 2 (Φ ((n.factorial : FiniteAdeleRing (𝓞 ℚ) ℚ) * b, k)) =
      k⁻¹ * m ((n.factorial : FiniteAdeleRing (𝓞 ℚ) ℚ) * b) * k := by
    refine ga_ext ?_ ?_
    · rw [pInf_finGL, map_mul, map_mul, map_unipotent_eq_one _ _ (pInf_mk D _), mul_one, ← map_mul, inv_mul_cancel, map_one]
    · rw [pFin_finGL]
  have e := congrArg (fun ψ : Sm E 2 => ψ.1 (G * k)) hS
  change f.1 (G * k * finGL E 2 _) = f.1 (G * k) at e
  rw [hy] at e
  rw [← e]
  change f.1 (G * (m _ * k)) = _
  congr 1
  group
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

theorem UpperTheory.standardAddChar_neg_archimedean_rat :
    ∀ x : ℝ, ψ (-(TR.sInf ℚ fun _ => x)) = Complex.exp (2 * Real.pi * Complex.I * x) := by
  intro x
  have hu : Nonempty (InfinitePlace ℚ) := inferInstance
  obtain ⟨w⟩ := hu
  have huniq : ∀ v : InfinitePlace ℚ, v = w := fun v => Subsingleton.elim v w
  have hreal : InfinitePlace.IsReal w := IsTotallyReal.isReal w
  have h : adelicChar ℚ (TR.sInf ℚ fun _ => x) = Real.fourierChar (-x) := by
    have e : TR.sInf ℚ (fun _ => x) = infiniteAdeleInl (TR.infEq ℚ fun _ => x) := rfl
    rw [e, adelicChar_infiniteAdeleInl, Fintype.prod_eq_single w (fun v hv => absurd (huniq v) hv)]
    rw [infiniteAdelicChar_apply_of_isReal hreal]
    have e2 : InfinitePlace.Completion.extensionEmbeddingOfIsReal hreal (TR.infEq ℚ (fun _ => x) w) = x :=
      (InfinitePlace.Completion.ringEquivRealOfIsReal hreal).apply_symm_apply x
    rw [e2]
  have h2 : adelicChar ℚ (-(TR.sInf ℚ fun _ => x)) = Real.fourierChar x := by
    rw [AddChar.map_neg_eq_inv, h, AddChar.map_neg_eq_inv, inv_inv]
  have h3 : ψ (-(TR.sInf ℚ fun _ => x)) = ((adelicChar ℚ (-(TR.sInf ℚ fun _ => x)) : Circle) : ℂ) := rfl
  rw [h3, h2, Real.fourierChar_apply]
  congr 1
  push_cast
  ring
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Xg
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

theorem UpperTheory.exists_nat_mul_integral_at_all_finite_places :
    ∀ (E : Type) [Field E] [NumberField E] (θ : E), ∃ d : ℕ, 0 < d ∧ ∀ e : ℕ, d ∣ e → ∀ w : H.P E, Valued.v (H.cp w (rt ((e : E) * θ))) ≤ 1 := by
  intro E _ _ θ
  obtain ⟨y, hy0, hy⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) θ)).exists_integral_multiple
  have hy' : IsIntegral ℤ ((y : E) * θ) := by
    simpa [zsmul_eq_mul] using hy
  have h1 : IsIntegral ℤ ((y.natAbs : E) * θ) := by
    rcases Int.natAbs_eq y with h | h
    · have hc : ((y.natAbs : E)) = (y : E) := by
        conv_rhs => rw [h]
        simp
      rw [hc]
      exact hy'
    · have hc : ((y.natAbs : E)) = -(y : E) := by
        conv_rhs => rw [h]
        simp
      rw [hc, neg_mul]
      exact hy'.neg
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy0, ?_⟩
  rintro e ⟨k, rfl⟩ w
  have hint : IsIntegral ℤ (((y.natAbs * k : ℕ) : E) * θ) := by
    have he : (((y.natAbs * k : ℕ) : E) * θ) = (k : E) * ((y.natAbs : E) * θ) := by
      push_cast
      ring
    rw [he]
    have hk : IsIntegral ℤ (k : E) := by
      simpa using isIntegral_algebraMap (R := ℤ) (A := E) (x := (k : ℤ))
    exact hk.mul h1
  have hm := coe_algebraMap_mem_adicCompletionIntegers w (⟨_, hint⟩ : 𝓞 E)
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp hm
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

theorem UpperTheory.lie_action_preserves_fixed_at_place :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (w : H.P E) (f : Sm E 2) (X : Lie E 2), H.Fix w f.1 → H.Fix w (lie E 2 X f).1 := by
  intro E _ _ _ w f X hf g k hk
  have h1 : rt E 2 (finGL E 2 (locGL E 2 w k)) f = f :=
    Subtype.ext (funext fun x => hf x k hk)
  have h2 : lie E 2 X (rt E 2 (finGL E 2 (locGL E 2 w k)) f) =
      rt E 2 (finGL E 2 (locGL E 2 w k)) (lie E 2 X f) :=
    LinearMap.congr_fun (lie_rt_fin X (locGL E 2 w k)) f
  rw [h1] at h2
  exact (congrArg (fun u : Sm E 2 => u.1 g) h2).symm
end
