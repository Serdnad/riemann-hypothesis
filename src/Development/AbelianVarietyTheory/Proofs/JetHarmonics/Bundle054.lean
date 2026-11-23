module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle048
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StAvDefs
import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.TensorProduct.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle007
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxSec
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle006
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGenOfSection
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.GermEvalOneStandardPointSelf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Valuation.Integral
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
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Formalism.HermitianCurvature.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle002
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import Mathlib.Algebra.Algebra.Hom.Rat
public import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005

@[expose] public section

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.norm_sq_integral_inner_weight_le : ∀ (Ω V : Type) [MeasurableSpace Ω] [NormedAddCommGroup V] [InnerProductSpace ℂ V] (ν : Measure Ω) (f g : Ω → V) (ph : Ω → ℂ), AEStronglyMeasurable f ν → AEStronglyMeasurable g ν → AEStronglyMeasurable ph ν → ENNReal.ofReal (‖∫ x, ⟪f x, ph x • g x⟫_ℂ ∂ν‖ ^ 2) ≤ (∫⁻ x, ENNReal.ofReal (‖ph x‖ ^ 2 * ‖f x‖ ^ 2) ∂ν) * ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) ∂ν := by
  first | exact @GlobalTheory.norm_sq_integral_inner_smul_le | exact GlobalTheory.norm_sq_integral_inner_smul_le | (intros; apply GlobalTheory.norm_sq_integral_inner_smul_le <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EmbCount

theorem exists_equiv (E : Type) [Field E] [NumberField E] (C : Type) [Field C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) :
    ∃ Φ : (E →ₐ[ℚ] C) ≃ (𝓞 E →+* O), ∀ σ (y : 𝓞 E), algebraMap O C (Φ σ y) = σ (y : E) := by
  have hinj := hv.hom_inj
  have h1 : ∀ (σ : E →ₐ[ℚ] C) (y : 𝓞 E), ∃ o : O, algebraMap O C o = σ (y : E) := by
    intro σ y
    have hi : IsIntegral ℤ (σ (y : E)) := (y.isIntegral_coe).map (σ.toRingHom.toIntAlgHom)
    have hi' : IsIntegral O (σ (y : E)) := hi.tower_top
    exact hv.exists_of_le_one (hv.mem_of_integral hi')
  choose f hf using h1
  let Ψ : (E →ₐ[ℚ] C) → (𝓞 E →+* O) := fun σ =>
    { toFun := f σ
      map_one' := hinj (by simp [hf])
      map_mul' := fun a b => hinj (by simp [hf])
      map_zero' := hinj (by simp [hf])
      map_add' := fun a b => hinj (by simp [hf]) }
  have hΨ : ∀ σ (y : 𝓞 E), algebraMap O C (Ψ σ y) = σ (y : E) := hf
  refine ⟨Equiv.ofBijective Ψ ⟨?_, ?_⟩, hΨ⟩
  · intro σ σ' h
    apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
    ext y
    have := hΨ σ y
    rw [h, hΨ] at this
    exact this.symm
  · intro τ
    have hu : ∀ y : Algebra.algebraMapSubmonoid (𝓞 E) (nonZeroDivisors ℤ),
        IsUnit (((algebraMap O C).comp τ) y) := by
      rintro ⟨_, n, hn, rfl⟩
      have : (n : C) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero hn
      simpa using this
    refine ⟨(IsLocalization.lift (S := E) hu).toRatAlgHom, ?_⟩
    ext y
    apply hinj
    rw [hΨ]
    exact IsLocalization.lift_eq hu y

theorem trace_eq_sum (E : Type) [Field E] [NumberField E] (p : ℕ) [Fact p.Prime] (C : Type)
    [Field C] [IsAlgClosed C] [CharZero C] (O : Type) [CommRing O] [Algebra O C]
    [Algebra ℤ_[p] O] (Φ : (E →ₐ[ℚ] C) ≃ (𝓞 E →+* O))
    (hΦ : ∀ σ (y : 𝓞 E), algebraMap O C (Φ σ y) = σ (y : E)) (x : ℤ_[p] ⊗[ℤ] 𝓞 E) :
    algebraMap O C (algebraMap ℤ_[p] O (LinearMap.trace ℤ_[p] _ (LinearMap.mulLeft ℤ_[p] x))) =
      ∑ σ : E →ₐ[ℚ] C, algebraMap O C (tauExt (Φ σ) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    have : LinearMap.mulLeft ℤ_[p] (x + y) =
        LinearMap.mulLeft ℤ_[p] x + LinearMap.mulLeft ℤ_[p] y := by
      apply LinearMap.ext; intro z; simp [add_mul]
    simp only [this, map_add (f := _), hx, hy, Finset.sum_add_distrib]
  | tmul a y =>
    have h1 : LinearMap.mulLeft ℤ_[p] (a ⊗ₜ[ℤ] y) =
        a • (LinearMap.mulLeft ℤ y).baseChange ℤ_[p] := by
      ext z
      simp [TensorProduct.smul_tmul']
    have h2 : ((Algebra.trace ℤ (𝓞 E) y : ℤ) : ℚ) = Algebra.trace ℚ E (y : E) :=
      Algebra.coe_trace_int y
    have h3 := trace_eq_sum_embeddings C (K := ℚ) (L := E) (x := (y : E))
    have h4 : LinearMap.trace ℤ _ (LinearMap.mulLeft ℤ y) = Algebra.trace ℤ (𝓞 E) y := rfl
    rw [h1, map_smul, LinearMap.trace_baseChange, h4]
    rw [← h2] at h3
    simp only [tauExt, Algebra.TensorProduct.lift_tmul, map_mul, smul_eq_mul, Algebra.ofId_apply]
    rw [← Finset.mul_sum]
    congr 1
    simp only [RingHom.toIntAlgHom_apply, hΦ]
    rw [← h3]
    simp

theorem card_emb : ∀ (E : Type) [Field E] [NumberField E] (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Algebra ℤ_[p] O] (e : ℤ_[p] ⊗[ℤ] 𝓞 E), e * e = e → Nonempty (Fin (Module.finrank ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] e))) ≃ Emb (O := O) e) ∧ Nat.card (𝓞 E →+* O) = Module.finrank ℚ E := by
  intro E _ _ p _ C _ _ _ v O _ _ hv _ e he
  classical
  obtain ⟨Φ, hΦ⟩ := exists_equiv E C v O hv
  have hinj := hv.hom_inj
  refine ⟨?_, ?_⟩
  · have ht := trace_eq_sum E p C O Φ hΦ e
    have hproj : LinearMap.IsProj (LinearMap.range (LinearMap.mulLeft ℤ_[p] e))
        (LinearMap.mulLeft ℤ_[p] e) :=
      ⟨fun x => ⟨x, rfl⟩, by
        rintro _ ⟨x, rfl⟩
        simp [← mul_assoc, he]⟩
    haveI : Module.Free ℤ_[p] (ℤ_[p] ⊗[ℤ] 𝓞 E) := inferInstance
    haveI : Module.Finite ℤ_[p] (ℤ_[p] ⊗[ℤ] 𝓞 E) := inferInstance
    rw [hproj.trace] at ht
    have hterm : ∀ σ : E →ₐ[ℚ] C, algebraMap O C (tauExt (Φ σ) e) =
        if Φ σ ∈ Emb (O := O) e then 1 else 0 := by
      intro σ
      split_ifs with h
      · have h' : tauExt (Φ σ) e = 1 := h
        rw [h', map_one]
      · have hid : IsIdempotentElem (algebraMap O C (tauExt (Φ σ) e)) := by
          unfold IsIdempotentElem
          rw [← map_mul, ← map_mul, he]
        rcases IsIdempotentElem.iff_eq_zero_or_one.mp hid with h0 | h1
        · exact h0
        · exact absurd (hinj (h1.trans (map_one _).symm)) h
    simp only [hterm, map_natCast, Finset.sum_boole, Nat.cast_inj] at ht
    rw [ht]
    refine ⟨(Finset.equivFin _).symm.trans (Φ.subtypeEquiv ?_)⟩
    intro σ
    simp
  · rw [← Nat.card_congr Φ, Nat.card_eq_fintype_card, AlgHom.card]

end GlobalTheory.EmbCount
end

section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharDepth

theorem padicTensor_eq_mul_add (A : Type) [CommRing A] (p : ℕ) [Fact p.Prime]
    (r : ℤ_[p] ⊗[ℤ] A) :
    ∃ (s : ℤ_[p] ⊗[ℤ] A) (x : A), r = (p : ℤ_[p] ⊗[ℤ] A) * s + (1 : ℤ_[p]) ⊗ₜ[ℤ] x := by
  induction r using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul a x =>
    have h := PadicInt.zmodRepr_spec a
    obtain ⟨-, h⟩ := h
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h
    obtain ⟨c, hc⟩ := h
    refine ⟨c ⊗ₜ[ℤ] x, (a.zmodRepr : ℤ) • x, ?_⟩
    have ha : a = (p : ℕ) • c + (a.zmodRepr : ℤ) • (1 : ℤ_[p]) := by
      rw [nsmul_eq_mul, ← hc]; simp
    rw [← nsmul_eq_mul, TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
      ← TensorProduct.add_tmul, ← ha]
  | add a b ha hb =>
    obtain ⟨s, x, rfl⟩ := ha
    obtain ⟨s', x', rfl⟩ := hb
    exact ⟨s + s', x + x', by rw [TensorProduct.tmul_add]; ring⟩

end GlobalTheory.CharDepth
end

section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.WeilPower

open GlobalTheory.CommutatorPairing GlobalTheory.BoxPhi

variable {S : Scheme.{0}} {j : ℕ} {A A' : PolAV S} (pA : IsPowPolAV A' A j) {k : ℤ} {T : Over S}

theorem exists_box_theta (x : T ⟶ A'.A) (θ : Fin j → ThetaGrp A.A A.L k T) (hθ : ∀ i, (θ i).pt = x ≫ pA.pr i) :
    ∃ θ' : ThetaGrp A'.A A'.L k T, θ'.pt = x ∧ ∀ (Z : Over S) (t : Z ⟶ T) (a : Z ⟶ A'.A) (z : Z.left) (J J'),
      Good A.L z J → Good A'.L z J' →
      om pA.w z J J' a.left ^ k * om pA.w z J J' ((t ≫ x) * a).left ^ (-k) * thetaVal θ' t a z J' =
        ∏ i, thetaVal (θ i) t (a ≫ pA.pr i) z J := by
  have hP : ∀ i, translPt A'.A x ≫ pA.pr i = T ◁ pA.pr i ≫ translPt A.A (θ i).pt := fun i => by
    have := pA.hom i
    rw [hθ, BoxTheta.translPt_hom]
  obtain ⟨u, hu, hv⟩ := exists_box_gen (pr := fun i => (pA.pr i).left) A.isLB A'.isLB pA.w pA.w_gen (K := Fin 2)
    (φ' := ![(snd T A'.A).left, (translPt A'.A x).left])
    (φ := fun i => ![(snd T A.A).left, (translPt A.A (θ i).pt).left]) (ε := ![k, -k])
    (p := fun i => (T ◁ pA.pr i).left) (fun i a => by
      fin_cases a
      · exact congrArg (fun q => q.left) (whiskerLeft_snd T (pA.pr i)).symm
      · exact congrArg (fun q => q.left) (hP i)) (fun i => (θ i).φ) (fun i => (θ i).isGen)
  refine ⟨⟨x, u, hu⟩, rfl, fun Z t a z J J' hJ hJ' => ?_⟩
  have e := hv _ (lift t a).left z J J' hJ hJ'
  rw [prod_theta x t a (om pA.w z J J')] at e
  refine e.trans (Finset.prod_congr rfl fun i _ => ?_)
  rw [← Over.comp_left, lift_whiskerLeft]
  rfl

theorem commVal_pow (hG : GlobalFnsSt) (θx' θy' : ThetaGrp A'.A A'.L k T) (θx θy : Fin j → ThetaGrp A.A A.L k T)
    (hx : ∀ i, (θx i).pt = θx'.pt ≫ pA.pr i) (hy : ∀ i, (θy i).pt = θy'.pt ≫ pA.pr i)
    {Z : Over S} (t : Z ⟶ T) (a : Z ⟶ A'.A) (z : Z.left) {J J'} (hJ : Good A.L z J) (hJ' : Good A'.L z J') :
    commVal θx' θy' t a z J' = ∏ i, commVal (θx i) (θy i) t (a ≫ pA.pr i) z J := by
  have := A'.isAb.comm
  obtain ⟨bx, ex, vx⟩ := exists_box_theta pA θx'.pt θx hx
  obtain ⟨by', ey, vy⟩ := exists_box_theta pA θy'.pt θy hy
  rw [commVal_indep hG A'.isAb A'.isLB θx' θy' bx by' t t (by rw [ex]) (by rw [ey]) a z J' hJ']
  have m : ∀ (x : T ⟶ A'.A) (i), ((t ≫ x) * a) ≫ pA.pr i = (t ≫ x ≫ pA.pr i) * (a ≫ pA.pr i) := fun x i => by
    have := pA.hom i
    rw [MonObj.mul_comp, Category.assoc]
  have e₁ := vx Z t a z J J' hJ hJ'
  have e₂ := vy Z t ((t ≫ θx'.pt) * a) z J J' hJ hJ'
  have e₃ := vy Z t a z J J' hJ hJ'
  have e₄ := vx Z t ((t ≫ θy'.pt) * a) z J J' hJ hJ'
  rw [mul_left_comm (t ≫ θy'.pt)] at e₂
  simp only [m, ← hx, ← hy] at e₂ e₄
  simp only [commVal, Finset.prod_mul_distrib, Finset.prod_inv_distrib, ← e₁, ← e₂, ← e₃, ← e₄, ex, ey, zpow_neg]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem weilIs_pow (hG : GlobalFnsSt) [Subsingleton T.left] (x y : T ⟶ A'.A) (c : Fin j → Γ(T.left, ⊤)ˣ)
    (h : ∀ i, WeilIs A.A A.L k (x ≫ pA.pr i) (y ≫ pA.pr i) (c i)) : WeilIs A'.A A'.L k x y (∏ i, c i) := by
  intro p
  have h' : ∀ i, (∃ θx θy : ThetaGrp A.A A.L k (overRes ⊤), θx.pt = overResι ⊤ ≫ x ≫ pA.pr i ∧
      θy.pt = overResι ⊤ ≫ y ≫ pA.pr i) ∧ ∀ θx θy : ThetaGrp A.A A.L k (overRes ⊤),
      θx.pt = overResι ⊤ ≫ x ≫ pA.pr i → θy.pt = overResι ⊤ ≫ y ≫ pA.pr i →
      CommIsOf A.A A.L k θx θy (unitRes ⊤ (c i)) := fun i => by
    obtain ⟨V, hV, H⟩ := h i p
    obtain rfl : V = ⊤ := top_le_iff.1 fun q _ => by rw [Subsingleton.elim q p]; exact hV
    exact H
  choose θx θy hx hy using fun i => (h' i).1
  obtain ⟨bx, ex, -⟩ := exists_box_theta pA (overResι ⊤ ≫ x) θx (fun i => by rw [hx, Category.assoc])
  obtain ⟨by', ey, -⟩ := exists_box_theta pA (overResι ⊤ ≫ y) θy (fun i => by rw [hy, Category.assoc])
  refine ⟨⊤, trivial, ⟨bx, by', ex, ey⟩, fun θx' θy' ex' ey' => (commIsOf_iff A'.isLB _ _ _).2 fun Z t a z J' hJ' => ?_⟩
  choose J hJ using fun χ : Z.left ⟶ A.A.left => exists_chart A.isLB (χ z)
  rw [commVal_pow pA hG θx' θy' θx θy (fun i => by rw [hx, ex', Category.assoc])
    (fun i => by rw [hy, ey', Category.assoc]) t a z hJ hJ']
  refine (Finset.prod_congr rfl fun i _ => (commIsOf_iff A.isLB _ _ _).1 ((h' i).2 _ _ (hx i) (hy i)) Z t _ z J hJ).trans ?_
  exact (map_prod _ _ _).symm.trans (congrArg _ (map_prod (Units.map (⊤ : T.left.Opens).ι.appTop.hom.toMonoidHom) c _).symm)

theorem weilIs_pow_field : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (pA : IsPowPolAV A' A j) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → ∀ (x x' : TFK (R := R) F ⟶ A'.A) (c : Fin j → Fˣ), (∀ i, WeilIs A.A A.L k (x ≫ pA.pr i) (x' ≫ pA.pr i) (unitOn (c i))) → WeilIs A'.A A'.L k x x' (unitOn (∏ i, c i)) := by
  intro hL _ _ _ R _ _ j A A' pA F _ _ k _ x x' c h
  have : Subsingleton (TFK (R := R) F).left := inferInstanceAs (Subsingleton (Spec (CommRingCat.of F)))
  have e : unitOn (∏ i, c i) = ∏ i, unitOn (c i) := map_prod (Units.map _) _ _
  rw [e]
  exact weilIs_pow pA hL.globalFns x x' (fun i => unitOn (c i)) h

end GlobalTheory.WeilPower
end
end

section

noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionCharacter

open ReciprocityTheory.ChartRestriction.G.Chart GlobalTheory.JetSer GlobalTheory.ChartBaseChange ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (IsGrpPullback isGrpPullback_pullback)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (Pt comp1)
open ReciprocityTheory.ChartRestriction.G.TB (dLin)

abbrev specV {V O : Type} [CommRing V] [CommRing O] (f : V →+* O) (A : Type) [CommRing A] [Algebra O A] :
    Over (Spec (CommRingCat.of V)) :=
  Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap O A).comp f)))

theorem isMapOf_baseChange {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G']
    {π : G'.left ⟶ G.left} (hπ : IsGrpPullback G' G (Spec.map (CommRingCat.ofHom (algebraMap R R'))) π)
    (hJ : JetAlgSt) {d : ℕ} {x : JetSer.Fam G (Fin d)} {x' : JetSer.Fam G' (Fin d)}
    (hx' : ∀ m, push hπ (x' m) = Chart.spMap (jetCoeff R R' (Fin d) m) ≫ x m)
    (f : G ⟶ G) (f' : G' ⟶ G') (α : Pt R 1 d) (hf : f'.left ≫ π = π ≫ f.left) (hα : IsMapOf x x f α) :
    IsMapOf x' x' f' (fun i => MvPowerSeries.map (algebraMap R R') (α i)) := by
  refine ⟨fun i => const_map (hα.1 i), fun n a y hy => ?_⟩
  obtain ⟨Θ, t, hΘ, ht, e⟩ := exists_move hπ hJ hx' ![a] ![y] (fun i => by fin_cases i; exact hy)
  have H := hα.2 1 _ _ (ht 0)
  have hFe : comp1 α (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt R (n := 1) d 0) = α := funext fun i => germEval_oneStandardPoint_self _
  rw [hFe] at H
  refine (rep_iff hπ hJ hx' (single_point_zero_constant hy.1) hΘ H _).2 fun m => ?_
  rw [← Category.assoc, ← e 0 m]
  apply Over.OverMorphism.ext
  show ((y m).left ≫ f'.left) ≫ π = ((y m).left ≫ π) ≫ f.left
  rw [Category.assoc, Category.assoc, hf]

section Transfer
variable {O : Type} [CommRing O] {Gt G' : Over (Spec (CommRingCat.of O))} [GrpObj Gt] [GrpObj G']
  (K : (specO O (DualNumber O) ⟶ Gt) → (specO O (DualNumber O) ⟶ G'))
  (hmul : ∀ w w', K (w * w') = K w * K w') (hinj : Function.Injective K)
  (hnat : ∀ (φ : DualNumber O →ₐ[O] DualNumber O) w, K (ptMap φ ≫ w) = ptMap φ ≫ K w)

include hmul hinj hnat in
theorem isTan_iff (w : specO O (DualNumber O) ⟶ Gt) : IsTan w ↔ IsTan (K w) := by
  have h1 : K 1 = 1 := by
    have := hmul 1 1
    rw [_root_.mul_one] at this
    exact left_eq_mul.mp this
  have key : ∀ {G : Over (Spec (CommRingCat.of O))} [GrpObj G] (z : specO O (DualNumber O) ⟶ G),
      IsTan z ↔ ptMap (scaleD (0 : O)) ≫ z = 1 := fun z => ⟨fun h => spMap_scaleD_zero h, fun h => by
    have e : (fstD O).comp (scaleD (0 : O)) = fstD O := by
      ext
      exact TrivSqZeroExt.fst_map _ _
    have := congrArg (Chart.spMap (fstD O) ≫ ·) h
    simp only [MonObj.comp_one] at this
    refine Eq.trans ?_ this
    show _ = Chart.spMap (fstD O) ≫ Chart.spMap (scaleD (0 : O)) ≫ z
    rw [← Category.assoc, Chart.spMap_comp, e]⟩
  rw [key, key, ← hnat, ← h1]
  exact hinj.eq_iff.symm

end Transfer

theorem exists_lie_coordinates (hJ : JetAlgSt) (hD : DLinSt) {V O : Type} [CommRing V] [IsLocalRing V] [CommRing O]
    (f : V →+* O) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] {d : ℕ} (x : JetSer.Fam G (Fin d))
    (hx : IsUnivChart G d x) (Gt : Over (Spec (CommRingCat.of O))) [GrpObj Gt]
    (J : (specO O (DualNumber O) ⟶ Gt) → (specV f (DualNumber O) ⟶ G))
    (hmul : ∀ w w', J (w * w') = J w * J w') (hinj : Function.Injective J)
    (hnat : ∀ (φ : DualNumber O →ₐ[O] DualNumber O) w,
      (J (ptMap φ ≫ w)).left = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (J w).left)
    (hsurj : ∀ g : specV f (DualNumber O) ⟶ G, Spec.map (CommRingCat.ofHom (fstD O).toRingHom) ≫ g.left =
      Spec.map (CommRingCat.ofHom (fstD O).toRingHom) ≫ (1 : specV f (DualNumber O) ⟶ G).left → ∃ w, J w = g) :
    ∃ (co : LieG Gt → Fin d → O) (tv : (Fin d → O) → LieG Gt), (∀ s, (fun w => co w s) ∈ omega Gt) ∧
      (∀ b, co (tv b) = b) ∧
      (∀ b, ∃ φ : JetR V (Fin d) 1 →+* DualNumber O, (∀ i, φ (zR 1 i) = TrivSqZeroExt.inr (b i)) ∧
        (J (tv b).1).left = Spec.map (CommRingCat.ofHom φ) ≫ (x 1).left) ∧
      ∀ (u : G ⟶ G) [IsMonHom u] (ut : Gt ⟶ Gt) (α : Pt V 1 d), IsMapOf x x u α → (∀ w, J (w ≫ ut) = J w ≫ u) →
        ∀ (b : Fin d → O) (a : O), ((dLin α).map f).mulVec b = a • b →
          (tv b).1 ≫ ut = ptMap (dualScale a) ≫ (tv b).1 := by
  letI : Algebra V O := f.toAlgebra
  letI alg : Algebra V (DualNumber O) := ((algebraMap O (DualNumber O)).comp f).toAlgebra
  haveI tow : @IsScalarTower V O (DualNumber O) _ _ alg.toSMul :=
    IsScalarTower.of_algebraMap_eq (R := V) (S := O) (A := DualNumber O) fun _ => rfl
  let j := Spec.map (CommRingCat.ofHom (algebraMap V O))
  let G' := (Over.pullback j).obj G
  have hπ : IsGrpPullback G' G j (pullback.fst G.hom j) := isGrpPullback_pullback G j
  choose x' hx' using fun m => push_surjective hπ (Chart.spMap (jetCoeff V O (Fin d) m) ≫ x m)
  have hu := isUnivChart_baseChange hπ hx hx'
  choose K hK using fun w => push_surjective (A := DualNumber O) hπ (J w)
  have hK' : ∀ w, (K w).left ≫ pullback.fst G.hom j = (J w).left := fun w => congrArg (·.left) (hK w)
  have Kmul : ∀ w w', K (w * w') = K w * K w' := fun w w' =>
    push_injective hπ (by rw [push_mul, hK, hK, hK]; exact hmul w w')
  have Kinj : Function.Injective K := fun w w' h => hinj (by rw [← hK, ← hK, h])
  have Knat : ∀ (φ : DualNumber O →ₐ[O] DualNumber O) w, K (ptMap φ ≫ w) = ptMap φ ≫ K w := fun φ w =>
    push_injective hπ (Over.OverMorphism.ext (by
      rw [push_left, push_left, hK', hnat, Over.comp_left, Category.assoc, hK']; rfl))
  have htan := isTan_iff K Kmul Kinj Knat
  have lie : ∀ w : specO O (DualNumber O) ⟶ Gt,
      (ptMap (TrivSqZeroExt.fstHom O O O) ≫ w = toUnit (specO O O) ≫ η[Gt]) ↔ IsTan w := fun w => Iff.rfl
  have ex : ∀ b : Fin d → O, ∃ w : LieG Gt, K w.1 = Chart.spMap (dualLift b) ≫ x' 1 := fun b => by
    obtain ⟨w, hw⟩ := hsurj (push hπ (Chart.spMap (dualLift b) ≫ x' 1)) (by
      have h := congrArg (·.left ≫ pullback.fst G.hom j) (isTan_dualLift hu b)
      have h1 := congrArg (·.left) (push_one (A := DualNumber O) hπ)
      have h2 : Chart.spMap (fstD O) ≫ (1 : sp (R₀ := O) (DualNumber O) ⟶ G') = 1 := MonObj.comp_one _
      rw [← h2] at h
      simp only [Over.comp_left, Category.assoc] at h
      rw [push_left] at h1
      rw [h1] at h
      exact h)
    have e : K w = Chart.spMap (dualLift b) ≫ x' 1 := push_injective hπ ((hK w).trans hw)
    exact ⟨⟨w, (lie w).2 ((htan w).2 (e ▸ isTan_dualLift hu b))⟩, e⟩
  choose tv htv using ex
  let co : LieG Gt → Fin d → O := fun w => tcoord hu (K w.1) ((htan _).1 ((lie _).1 w.2))
  have hco : ∀ b, co (tv b) = b := fun b => tcoord_eq hu _ _ b (htv b)
  refine ⟨co, tv, fun s => ⟨fun w w' h => ?_, fun a w h => ?_⟩, hco, fun b => ?_, ?_⟩
  · have := tcoord_mul hu ((htan _).1 ((lie _).1 w.2)) ((htan _).1 ((lie _).1 w'.2))
    exact (congrFun (Chart.tcoord_congr hu (Kmul _ _) _ _) s).trans (congrFun this s)
  · have := tcoord_scale hu a ((htan _).1 ((lie _).1 w.2))
    exact (congrFun (Chart.tcoord_congr hu (Knat _ _) _ _) s).trans (congrFun this s)
  · refine ⟨(dualLift b).toRingHom.comp (jetCoeff V O (Fin d) 1).toRingHom, fun i => ?_, ?_⟩
    · show dualLift b (jetCoeff V O (Fin d) 1 (zR 1 i)) = _
      rw [jetCoeff_zR, dualLift_zR]
    · have h : (x' 1).left ≫ pullback.fst G.hom j = _ := congrArg (·.left) (hx' 1)
      rw [← hK', htv, Over.comp_left, Category.assoc, h, Over.comp_left, ← Category.assoc, Chart.spMap_left, Chart.spMap_left, ← Spec.map_comp]
      rfl
  · intro u _ ut α hα hut b a hb
    let u' : G' ⟶ G' := (Over.pullback j).map u
    have hu' : u'.left ≫ pullback.fst G.hom j = pullback.fst G.hom j ≫ u.left := pullback.lift_fst _ _ _
    have hm := isMapOf_baseChange hπ hJ hx' u u' α hu' hα
    have ht := (htan _).1 ((lie _).1 (tv b).2)
    have h := hD O G' G' d x' x' hu hu u' _ hm (K (tv b).1) ht (Chart.isTan_comp ht u')
    have h2 : dLin (fun i => MvPowerSeries.map (algebraMap V O) (α i)) = (dLin α).map f := by
      ext i k
      simp [dLin, RingHom.algebraMap_toAlgebra]
    have h3 : tcoord hu (K (tv b).1) ht = b := hco b
    rw [h2, h3, hb] at h
    have h4 := tcoord_scale hu a ht
    rw [h3] at h4
    apply Kinj
    rw [Knat]
    have e1 : K ((tv b).1 ≫ ut) = K (tv b).1 ≫ u' := push_injective hπ (Over.OverMorphism.ext (by
      rw [push_left, push_left, hK', hut, Over.comp_left, Over.comp_left, Category.assoc, hu', ← Category.assoc, hK']))
    rw [e1, tcoord_spec hu _ (Chart.isTan_comp ht u'), h, ← h4]
    exact (tcoord_spec hu _ _).symm

end GlobalTheory.TorsionCharacter
end
end
