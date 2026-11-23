module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle004
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle004
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ExistsPowPrincipalFractionalIdeal
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle005
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPolyRepInducedBundleAndMetric
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AutomorphicArithmetic.WeightCongruences.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle106
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle219
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle163
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
public import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle218
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle026
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorBasisChangeEqSubstitution
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open Matrix
open scoped ComplexOrder Topology

theorem _root_.GlobalTheory.T.poincareNorm_coordinateVector_mul_length_le_five : ∀ (n a : ℕ) (ha : a ≤ n) (ρ : ℝ), ρ ≤ 1 / 2 → ∀ v : ReciprocityTheory.L2DbarEstimates.V n, v.ofLp ∈ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.punctured ha ρ → ∀ k : Fin n, GlobalTheory.HermFrame.gnorm (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.poincareGram a v.ofLp) (Pi.single k 1) * GlobalTheory.GoodMetric.poinWt (Finset.univ.map (Fin.castLEEmb ha)) v k ≤ 5 := by
  first | exact @GlobalTheory.PoinLen.gnorm_mul_poinWt_le_five | exact GlobalTheory.PoinLen.gnorm_mul_poinWt_le_five | (intros; apply GlobalTheory.PoinLen.gnorm_mul_poinWt_le_five <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric NumberField GlobalTheory.Mem.Per
open scoped Pointwise nonZeroDivisors

namespace GlobalTheory.Mem.EigenLine

variable {R : Ranks} (H : Host R)

theorem half_ne_zero :
    ((H.𝔟 : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E) ≠ 0 := by
  refine FractionalIdeal.coeIdeal_ne_zero.2 ?_
  intro h0
  have hd : differentIdeal (𝓞 H.K) (𝓞 H.E) ≠ ⊥ := differentIdeal_ne_bot
  apply hd
  have := H.𝔟_spec.1
  rw [h0, Ideal.bot_mul] at this
  exact this

theorem half_mul_inv :
    ((H.𝔟 : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E) * H.AA0 = 1 :=
  mul_inv_cancel₀ (half_ne_zero H)

theorem inv_mul_different :
    H.AA0 * ((differentIdeal (𝓞 H.K) (𝓞 H.E) : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E) =
      ((H.conj • H.𝔟 : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E) := by
  have h : differentIdeal (𝓞 H.K) (𝓞 H.E) = H.𝔟 * (H.conj • H.𝔟) := H.𝔟_spec.1
  rw [h, FractionalIdeal.coeIdeal_mul, ← mul_assoc, mul_comm H.AA0, half_mul_inv, one_mul]

theorem mem_inv_mul_different (x : H.E) :
    x ∈ H.AA0 * ((differentIdeal (𝓞 H.K) (𝓞 H.E) : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E) ↔
      ∃ b ∈ H.𝔟, x = H.conj ((b : 𝓞 H.E) : H.E) := by
  rw [inv_mul_different, FractionalIdeal.mem_coeIdeal]
  constructor
  · rintro ⟨c, hc, rfl⟩
    rw [Ideal.pointwise_smul_def] at hc
    obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_iff_of_surjective _
      (MulSemiringAction.toRingEquiv _ (𝓞 H.E) H.conj).surjective).1 hc
    exact ⟨b, hb, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨H.conj • b, Ideal.smul_mem_pointwise_smul _ _ _ hb, rfl⟩

theorem map_mem_ellLat {LL : Type} [Field LL] [NumberField LL] (embE : H.E →+* LL)
    (g : R.GG) (x : H.E)
    (hx : x ∈ H.AA0 * ((differentIdeal (𝓞 H.K) (𝓞 H.E) : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E)) :
    embE (H.sigmaOf g x) ∈ ellLat H embE g := by
  refine FractionalIdeal.mul_induction_on hx ?_ ?_
  · intro i hi j hj
    obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hj
    exact Submodule.subset_span ⟨i, hi, b, hb, rfl⟩
  · intro a b ha hb
    rw [map_add (f := _), map_add (f := _)]
    exact Submodule.add_mem _ ha hb

theorem ellT_eq_ellLat : ∀ (D : D7) (M : IntermediateField ℚ ℂ) [NumberField M] (embE : D.host.E →+* M),
    (∀ x, ((embE x : M) : ℂ) = D.host.φ₀ x) → ∀ τ : D.what₂.Tau,
      ellT D M τ = ellLat D.host embE (D.eTau τ).1 := by
  intro D M _ embE hE τ
  have hτ : ∀ (τ : D.what₂.Tau) x, embT D τ x = ((embE (D.host.sigmaOf (D.eTau τ).1 x) : M) : ℂ) := by
    intro τ x
    rw [hE]
    rfl
  have hM : ∀ τ x, embT D τ x ∈ M := fun τ x => by
    rw [hτ]
    exact Subtype.property _
  let φ : D.host.E →+* M := embE.comp (((D.host.sigmaOf (D.eTau τ).1 : D.host.E →+* D.host.E)).comp
    (D.host.conj : D.host.E →+* D.host.E))
  have hφ : ∀ y, φ y = embE (D.host.sigmaOf (D.eTau τ).1 (D.host.conj y)) := fun _ => rfl
  have hone := half_mul_inv D.host
  apply le_antisymm
  · intro x hx
    rw [GlobalTheory.Glob.mem_ellT_iff hM] at hx
    have key : ∀ z ∈ ((D.host.𝔟 : Ideal (𝓞 D.host.E)) :
        FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) * D.host.AA0,
        x * φ z ∈ ellLat D.host embE (D.eTau τ).1 := by
      intro z hz
      refine FractionalIdeal.mul_induction_on hz ?_ ?_
      · intro i hi j hj
        obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hi
        have hint : IsIntegral ℤ (x * φ j) := by
          refine (isIntegral_algHom_iff (M.val.toRingHom.toIntAlgHom) M.val.injective).1 ?_
          have := hx j hj
          rw [hτ] at this
          exact this
        let c : 𝓞 M := ⟨x * φ j, hint⟩
        have : c • φ (b : D.host.E) ∈ ellLat D.host embE (D.eTau τ).1 :=
          Submodule.smul_mem _ _ (map_mem_ellLat D.host embE _ _
            ((mem_inv_mul_different D.host _).2 ⟨b, hb, rfl⟩))
        convert this using 1
        change x * φ (b * j) = x * φ j * φ b
        rw [map_mul]; ring
      · intro a b ha hb
        rw [map_add (f := _), mul_add]
        exact Submodule.add_mem _ ha hb
    have := key 1 (hone ▸ FractionalIdeal.one_mem_one _)
    simpa using this
  · unfold ellLat
    rw [Submodule.span_le]
    rintro x ⟨a, ha, d, hd, rfl⟩
    obtain ⟨b, hb, hab⟩ := (mem_inv_mul_different D.host (a * (d : D.host.E))).1
      (FractionalIdeal.mul_mem_mul ha ((FractionalIdeal.mem_coeIdeal _).2 ⟨d, hd, rfl⟩))
    rw [SetLike.mem_coe, GlobalTheory.Glob.mem_ellT_iff hM]
    intro y hy
    have h1 : (b : D.host.E) * y ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :=
      hone ▸ FractionalIdeal.mul_mem_mul ((FractionalIdeal.mem_coeIdeal _).2 ⟨b, hb, rfl⟩) hy
    obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 h1
    rw [← hτ, hab, ← map_mul, ← map_mul, ← hr]
    exact map_isIntegral_int ((embT D τ).comp (D.host.conj : D.host.E →+* D.host.E)) r.isIntegral_coe

end GlobalTheory.Mem.EigenLine
end
end

section

open AlgebraicGeometry MvPolynomial GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)

theorem _root_.GlobalTheory.T.chernConnection_curvature_polyRep_eval : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (ρ : PolyRep m) (n : ℕ) (G : V n → Mat m ℂ) (v : V n), (∀ τ, MContDiffAt 2 (fun u => G u τ) v) → (∀ τ, (G v τ).det ≠ 0) → (∀ᶠ u in nhds v, ∀ ξ, conn (fun w => ρ.ev (G w)) u ξ = ρ.lie (fun τ => conn (fun w => G w τ) u ξ)) ∧ curvPoly (fun w => ρ.ev (G w)) v = ρ.lie (fun τ => curvPoly (fun w => G w τ) v) := by
  first | exact @GlobalTheory.GoodMetric.conn_curvPoly_ev | exact GlobalTheory.GoodMetric.conn_curvPoly_ev | (intros; apply GlobalTheory.GoodMetric.conn_curvPoly_ev <;> assumption)
end

section

open AlgebraicGeometry MvPolynomial GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)

theorem _root_.GlobalTheory.T.exists_polyRep_inducedBundle_and_metric : ∀ (F : Type) [Field F] (X : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (ρ : PolyRep m) (E : Fr (ratOf X) m 0), ∃ E' : Fr (ratOf X) (fun _ : Unit => ρ.M) 0, (∀ z, ∀ A ∈ E.S z, (fun _ : Unit => ρ.ev A) ∈ E'.S z) ∧ ∀ (σ : F →+* ℂ) (O : X.X.Opens) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricOn E O H → ∃ H' : Mat (fun _ : Unit => ρ.M) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => ρ.M) ℂ, IsMetricOn E' O H' ∧ ∀ y ∈ ptsIn X.str σ O, ∀ A ∈ E.S (under y), H' (fun _ => ρ.ev A) y () = ρ.ev (H A y) := by
  first | exact @GlobalTheory.GoodMetric.RepBundle.exists_repBundle | exact GlobalTheory.GoodMetric.RepBundle.exists_repBundle | (intros; apply GlobalTheory.GoodMetric.RepBundle.exists_repBundle <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.OneRep

variable {E : Type} [Field E] [NumberField E] [NumberField.IsTotallyComplex E] {a : ℕ}


omit [NumberField E] [NumberField.IsTotallyComplex E] in
theorem atEmb_zero (τ : E →+* ℂ) : atEmb τ 0 = 0 := by
  classical
  unfold atEmb; split_ifs <;> simp


omit [NumberField E] [NumberField.IsTotallyComplex E] in
theorem map_single_atEmb (τ : E →+* ℂ) (i k : Fin a) (z : ℂ) :
    (Matrix.single i k z).map (atEmb τ) = Matrix.single i k (atEmb τ z) := by
  ext p q
  simp only [Matrix.map_apply, Matrix.single_apply]
  split_ifs <;> simp [atEmb_zero]

end GlobalTheory.OneRep

end
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section
namespace GlobalTheory.CuspRep.GASplit
variable (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)

theorem continuous_infEq_symm : Continuous (infEq E).symm := by
  refine continuous_pi fun w => ?_
  exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
    (continuous_apply w)

theorem continuous_pInf : Continuous (pInf E) :=
  (continuous_infEq_symm E).comp continuous_fst

theorem continuous_pFin : Continuous (pFin E) := continuous_snd

theorem continuous_sInf : Continuous (sInf E) :=
  (continuous_infEq E).prodMk continuous_const

theorem continuous_sFin : Continuous (sFin E) :=
  continuous_const.prodMk continuous_id

theorem continuous_glMap {R S : Type} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
    [IsTopologicalRing R] [IsTopologicalRing S] (p : R →+* S) (hp : Continuous p) :
    Continuous (GeneralLinearGroup.map (n := Fin a) p) := by
  refine Continuous.units_map _ ?_
  exact continuous_pi fun i => continuous_pi fun j => hp.comp ((continuous_apply j).comp (continuous_apply i))

theorem continuous_cornerGL {R S : Type} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
    [IsTopologicalRing R] [IsTopologicalRing S] (s : R →ₙ+* S) (hs : Continuous s) :
    Continuous (cornerGL a s) := by
  refine Continuous.units_map _ ?_
  change Continuous fun x : Matrix (Fin a) (Fin a) R => 1 - matN a s 1 + matN a s x
  refine continuous_const.add ?_
  exact continuous_pi fun i => continuous_pi fun j => hs.comp ((continuous_apply j).comp (continuous_apply i))

def splitMulEquiv : GA E a ≃* GL (Fin a) (Cinf E) × GL (Fin a) (Af E) where
  toFun g := (GeneralLinearGroup.map (pInf E) g, GeneralLinearGroup.map (pFin E) g)
  invFun p := infGL E a p.1 * finGL E a p.2
  left_inv g := infGL_mul_finGL g
  right_inv p := by
    obtain ⟨y, k⟩ := p
    refine Prod.ext ?_ ?_ <;> simp
  map_mul' g h := by simp

def splitEquiv : GA E a ≃ₜ* GL (Fin a) (Cinf E) × GL (Fin a) (Af E) where
  toMulEquiv := splitMulEquiv E a
  continuous_toFun :=
    ((continuous_glMap a (pInf E) (continuous_pInf E))).prodMk (continuous_glMap a (pFin E) (continuous_pFin E))
  continuous_invFun :=
    ((continuous_cornerGL a (sInf E) (continuous_sInf E)).comp continuous_fst).mul
      ((continuous_cornerGL a (sFin E) (continuous_sFin E)).comp continuous_snd)

theorem exists_split : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ),
    ∃ e : GA E a ≃ₜ* GL (Fin a) (Cinf E) × GL (Fin a) (Af E),
      ∀ g, e g = (GeneralLinearGroup.map (pInf E) g, GeneralLinearGroup.map (pFin E) g) :=
  fun E _ _ _ a => ⟨splitEquiv E a, fun _ => rfl⟩

end GlobalTheory.CuspRep.GASplit
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.Cartier.CommonEqn

variable {X : Scheme.{0}} [IsIntegral X]

theorem generatesAt_add {D : CartierDiv X} {x : X} {f f' : X.functionField}
    (h : D.GeneratesAt x f) (h' : D.VanishesAt x f') : D.GeneratesAt x (f + f') := by
  obtain ⟨g, hg, a, ha, e⟩ := h
  obtain ⟨b, hb, e'⟩ := hg.vanishesAt_iff.1 h'
  refine ⟨g, hg, a + b, ?_, by rw [map_add (f := _), e, e', add_mul]⟩
  by_contra hu
  have : a + b ∈ IsLocalRing.maximalIdeal _ := hu
  exact (show a ∈ IsLocalRing.maximalIdeal _ from by simpa using sub_mem this hb) ha

end GlobalTheory.Cartier.CommonEqn
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical

theorem _root_.GlobalTheory.T.host_delta_character_inertial_order_fifteen_exists : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (p : ℕ), p.Prime → p % 15 = 1 → _root_.GlobalTheory.Mem.Chr.SplitsC H.E p → _root_.Formalism.L2.Host.DeltaExists (H := H) p := by
  first | exact @GlobalTheory.Mem.DeltaZero.delta_exists | exact GlobalTheory.Mem.DeltaZero.delta_exists | (intros; apply GlobalTheory.Mem.DeltaZero.delta_exists <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.MuZero

theorem exists_residue_char {L : Type} [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) {p : ℕ} (hp : p.Prime)
    (hw : Ideal.absNorm w.asIdeal = p) (ω : (ZMod p)ˣ →* ℂˣ) :
    ∃ θ : (𝓞 L ⧸ w.asIdeal)ˣ →* ℂˣ, θ (-1) = ω (-1) ∧ ∀ (a : ℕ) (ha : a.Coprime p),
      ∃ b : (𝓞 L ⧸ w.asIdeal)ˣ, (b : 𝓞 L ⧸ w.asIdeal) = Ideal.Quotient.mk w.asIdeal (a : 𝓞 L) ∧
        θ b = ω (ZMod.unitOfCoprime a ha) := by
  have hc : Nat.card (𝓞 L ⧸ w.asIdeal) = p := by
    rw [← hw, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have : Finite (𝓞 L ⧸ w.asIdeal) := Nat.finite_of_card_ne_zero (hc ▸ hp.ne_zero)
  let _ : Fintype (𝓞 L ⧸ w.asIdeal) := Fintype.ofFinite _
  let ρ : ZMod p ≃+* (𝓞 L ⧸ w.asIdeal) := ZMod.ringEquivOfPrime _ hp (by rw [← Nat.card_eq_fintype_card, hc])
  refine ⟨ω.comp (Units.map (ρ.symm : (𝓞 L ⧸ w.asIdeal) →* ZMod p)), ?_, fun a ha => ?_⟩
  · rw [MonoidHom.comp_apply]
    congr 1
    ext
    simp
  · refine ⟨Units.map (ρ : ZMod p →* (𝓞 L ⧸ w.asIdeal)) (ZMod.unitOfCoprime a ha), ?_, ?_⟩
    · simp
    · rw [MonoidHom.comp_apply]
      congr 1
      ext
      simp

variable {R : Ranks} {H : Formalism.BasicNotions.Host R}

theorem eq_of_overP {k k' : Fin 2} {w : HeightOneSpectrum (𝓞 H.E)} (h : _root_.Formalism.L2.Host.OverP H (H.g k) w)
    (h' : _root_.Formalism.L2.Host.OverP H (H.g k') w) : k = k' := by
  by_contra hne
  have hg : H.g k ≠ H.g k' := by
    fin_cases k <;> fin_cases k'
    · exact absurd rfl hne
    · exact H.g_ne
    · exact H.g_ne.symm
    · exact absurd rfl hne
  have hc : IsCoprime ((H.g k : ℕ) : 𝓞 H.E) ((H.g k' : ℕ) : 𝓞 H.E) :=
    Nat.Coprime.cast ((Nat.coprime_primes (H.g_prime k) (H.g_prime k')).2 hg)
  obtain ⟨s, t, hst⟩ := hc
  apply w.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hst]
  exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ h) (w.asIdeal.mul_mem_left _ h')


open Classical in
theorem exists_unitary_mu_zero_characters_of_split_type_primes : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (P : _root_.Formalism.L2.Host.PiBar H) (W : _root_.Formalism.L2.Host.Omg H) (e : R.Psi → ℚ) (j : ℕ), (∀ k, _root_.GlobalTheory.Mem.Chr.SplitsC H.E (H.g k)) → (∀ τ, ∃ z : ℤ, e τ = z) → UpperTheory.MUQ (_root_.Formalism.L2.Host.embPsi H) e → _root_.Formalism.L2.Host.Mu0Exists P W e j := by
  intro R H P W e j hs hint hev
  choose z hz using hint
  have hmu : UpperTheory.MU (_root_.Formalism.L2.Host.embPsi H) z := hev.mu hz
  haveI := H.galois
  haveI : IsGalois H.K H.E := IsGalois.tower_top_of_isGalois ℚ H.K H.E
  obtain ⟨c, hc, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  have hce : c.toRingEquiv = H.conj.toRingEquiv := RingEquiv.ext hc
  have hsp := fun k => GlobalTheory.T.completelySplitPrime_host_place_properties R H (H.g k) (H.g_prime k) (hs k)
  have hθ : ∀ w : HeightOneSpectrum (𝓞 H.E), ∃ θ : (𝓞 H.E ⧸ w.asIdeal)ˣ →* ℂˣ, θ (-1) = 1 ∧
      ∀ k, P.Div k w → ∀ (a : ℕ) (ha : a.Coprime (H.g k)),
        ∃ b : (𝓞 H.E ⧸ w.asIdeal)ˣ, (b : 𝓞 H.E ⧸ w.asIdeal) = Ideal.Quotient.mk w.asIdeal (a : 𝓞 H.E) ∧
          θ b = (W.om k (ZMod.unitOfCoprime a ha) ^ (2 * (j + 1)))⁻¹ := by
    intro w
    by_cases h : ∃ k, P.Div k w
    · obtain ⟨k, hk⟩ := h
      obtain ⟨θ, h1, h2⟩ := exists_residue_char w (H.g_prime k) (hsp k w (P.overP hk)).1
        ((W.om k ^ (2 * (j + 1)))⁻¹)
      refine ⟨θ, ?_, fun k' hk' => ?_⟩
      · rw [h1, MonoidHom.inv_apply, MonoidHom.pow_apply, pow_mul, ← map_pow, neg_one_sq, map_one, one_pow, inv_one]
      · obtain rfl := eq_of_overP (P.overP hk) (P.overP hk')
        exact h2
    · exact ⟨1, rfl, fun k hk => absurd ⟨k, hk⟩ h⟩
  choose θ hθ1 hθ2 using hθ
  let S : Finset (HeightOneSpectrum (𝓞 H.E)) := Finset.univ.biUnion fun k => _root_.Formalism.L2.Host.aboveF (L := H.E) H.K (P.pb k)
  have hS : ∀ w, w ∈ S ↔ ∃ k, P.Div k w := fun w => by
    simp only [S, Finset.mem_biUnion, Finset.mem_univ, true_and, _root_.Formalism.L2.Host.aboveF, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    rfl
  have hmem : ∀ k w, w ∈ _root_.Formalism.L2.Host.aboveF (L := H.E) H.K (P.pb k) ↔ P.Div k w := fun k w => by
    simp only [_root_.Formalism.L2.Host.aboveF, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    rfl
  have hres : ∀ (k : Fin 2) (ζ : (𝓞 H.E)ˣ), (∃ m : ℕ, 0 < m ∧ ((ζ : 𝓞 H.E) : H.E) ^ m = 1) →
      ∏ w ∈ _root_.Formalism.L2.Host.aboveF (L := H.E) H.K (P.pb k), θ w (Units.map (Ideal.Quotient.mk w.asIdeal).toMonoidHom ζ) = 1 :=
    fun k ζ hζ => UpperTheory.prod_residue_char_norm_one_unit_eq_one H.K H.E (H.g k) (H.g_prime k) (P.pb k) _ (fun w => hmem k w)
      (fun w hw => ⟨(hsp k w (P.overP ((hmem k w).1 hw))).1, (hsp k w (P.overP ((hmem k w).1 hw))).2.1⟩)
      ((W.om k ^ (2 * (j + 1)))⁻¹) θ (fun w hw a ha => hθ2 w k ((hmem k w).1 hw) a ha) ζ (H.der.norm_mu _ hζ)
  have hdisj : (↑(Finset.univ : Finset (Fin 2)) : Set (Fin 2)).PairwiseDisjoint
      (fun k => _root_.Formalism.L2.Host.aboveF (L := H.E) H.K (P.pb k)) := by
    intro k _ k' _ hkk'
    refine Finset.disjoint_left.2 fun w hw hw' => hkk' ?_
    exact eq_of_overP (P.overP ((hmem k w).1 hw)) (P.overP ((hmem k' w).1 hw'))
  obtain ⟨χ, hu, ht, hi, htame, hunr, hloc, -⟩ := GlobalTheory.T.exists_heckeChar_trivOn_realSubfield_infinityType H.F H.E c (R.Psi) (_root_.Formalism.L2.Host.embPsi H) hcm z S θ
    (by
      intro w hw w' hcj hw'
      obtain ⟨k, hk⟩ := (hS w).1 hw
      obtain ⟨k', hk'⟩ := (hS w').1 hw'
      rw [hce] at hcj
      obtain ⟨ho, hiff⟩ := (hsp k w (P.overP hk)).2.2.2 (P.pb k) (P.pb_over k) w' hcj
      obtain rfl := eq_of_overP ho (P.overP hk')
      exact hiff.1 hk hk')
    (by
      intro ζ hζ
      have hinf : ∏ i, _root_.Formalism.L2.Host.embPsi H i ((ζ : 𝓞 H.E) : H.E) ^ (-z i) = 1 := hmu.neg _ hζ
      have hfin : ∏ w ∈ S, θ w (Units.map (Ideal.Quotient.mk w.asIdeal).toMonoidHom ζ) = 1 := by
        rw [Finset.prod_biUnion hdisj]
        exact Finset.prod_eq_one fun k _ => hres k ζ hζ
      rw [hinf, one_mul, ← Units.coe_prod]
      exact (congrArg Units.val hfin).trans Units.val_one)
  refine ⟨χ, hu, ht, ⟨_, fun τ => ?_, hi⟩, fun v hv => hunr v ?_ ?_, htame, fun k w hw a ha x hx => ?_⟩
  · show _ = 2 * -e τ
    rw [hz τ]
    push_cast
    ring
  · intro h
    obtain ⟨k, hk⟩ := (hS v).1 h
    exact hv k (P.overP hk)
  · intro w hw hcj
    obtain ⟨k, hk⟩ := (hS w).1 hw
    rw [hce] at hcj
    exact hv k ((hsp k w (P.overP hk)).2.2.2 (P.pb k) (P.pb_over k) v hcj).1
  · obtain ⟨b, hb, hb'⟩ := hθ2 w k hw a ha
    rw [← hb']
    exact hloc w ((hS w).2 ⟨k, hw⟩) x (a : 𝓞 H.E) b (by rw [hx]; simp) hb

end GlobalTheory.Mem.MuZero
end

section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

theorem _root_.GlobalTheory.T.rowHCParameter_isHCParam_and_formalDegree_pos : ∀ (R : Ranks) (P : HCParam R), Formalism.QuantumDeterminants.IsHCParam (lamSH R P) ∧ 0 < trueDsig R P := by
  first | exact @GlobalTheory.Mem.Vol.lamSH_isHCParam_and_trueDsig_pos | exact GlobalTheory.Mem.Vol.lamSH_isHCParam_and_trueDsig_pos | (intros; apply GlobalTheory.Mem.Vol.lamSH_isHCParam_and_trueDsig_pos <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.Chain GlobalTheory.CompactHowe Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.fockPolynomialVector_basisChange_eq_substitution : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (BS g : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT h : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ), IsThetaFunO ψ S T f → ∀ P, pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (fun τ => BS τ * g τ) (fun τ => BT τ * h τ) f P = pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) BS BT f (substF h (fun τ => ((g τ)⁻¹)ᵀ) P) := by
  first | exact @GlobalTheory.FockBaseChange.pureTensorO_subst | exact GlobalTheory.FockBaseChange.pureTensorO_subst | (intros; apply GlobalTheory.FockBaseChange.pureTensorO_subst <;> assumption)
end
