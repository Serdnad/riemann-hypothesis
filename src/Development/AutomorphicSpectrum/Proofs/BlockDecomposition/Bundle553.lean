module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1441
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import GroundTheory.AutomorphicForms.AdelicGLn
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle306
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapTop
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle531
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle533
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.MapsExist
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle532
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle008
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle534
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle397
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open NumberField Matrix
open GlobalTheory.BCT PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.Tf.Loc (twConj TwConjugate)

namespace GlobalTheory.CompanionTheory.ClassBij

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem conjE_conjE (x : E) : conjE E (conjE E x) = x := by
  simp [PositivityTheory.Rg.BcB.conjE, NumberField.IsCMField.complexConj_apply_apply]

theorem thetaE_thetaE (g : GL (Fin n) E) : thetaE E n (thetaE E n g) = g := by
  apply Units.ext
  ext i j
  simp only [PositivityTheory.Rg.BcB.thetaE, PositivityTheory.Rg.BcB.thetaR_val, ← map_inv, inv_inv, Matrix.transpose_apply,
    Matrix.map_apply]
  exact conjE_conjE _

theorem nrm_twConj (g d : GL (Fin n) E) : nrm (twConj (thetaE E n) g d) = g⁻¹ * nrm d * g := by
  simp only [PositivityTheory.Rg.BcB.nrm, twConj, map_mul, map_inv, thetaE_thetaE]
  group

theorem charpoly_nrm_twConj (g d : GL (Fin n) E) :
    (nrm (twConj (thetaE E n) g d)).val.charpoly = (nrm d).val.charpoly := by
  rw [nrm_twConj, Units.val_mul, Units.val_mul, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
    ← Units.val_mul, _root_.mul_inv_cancel, Units.val_one, Matrix.one_mul]

theorem isRegEll_twConj (g d : GL (Fin n) E) : IsRegEll (twConj (thetaE E n) g d) ↔ IsRegEll d := by
  simp only [PositivityTheory.Rg.BcB.IsRegEll, PositivityTheory.Rg.BcB.IsRegD, charpoly_nrm_twConj]

theorem twConjugate_equivalence : Equivalence (TwConjugate (thetaE E n)) := by
  refine ⟨fun x => ⟨1, by simp [twConj]⟩, ?_, ?_⟩
  · rintro x y ⟨g, rfl⟩
    refine ⟨g⁻¹, ?_⟩
    simp only [twConj, map_inv, inv_inv]
    group
  · rintro x y z ⟨g, rfl⟩ ⟨h, rfl⟩
    refine ⟨g * h, ?_⟩
    simp only [twConj, map_mul, _root_.mul_inv_rev]
    group

theorem exists_out (y : GL (Fin n) E) :
    ∃ g, y = twConj (thetaE E n) g (Quot.out (Quot.mk (TwConjugate (thetaE E n)) y)) :=
  twConjugate_equivalence.eqvGen_iff.1 (Quot.eqvGen_exact (Quot.out_eq _))

theorem classBij : PositivityTheory.Rg.BcB.G8.ClassBij := by
  intro F _ _ _ m u hu
  have hθ : ∀ g : GL (Fin m) F, thE F m g = u * thetaE F m g * u⁻¹ := by
    obtain ⟨h, -⟩ := hu
    exact h
  let e : TwCl (thE F m) ≃ TwClass F m :=
    { toFun := Quot.map (fun x => x * u) (by
        rintro x y ⟨g, rfl⟩
        exact ⟨g, by simp only [twConj, hθ]; group⟩)
      invFun := Quot.map (fun x => x * u⁻¹) (by
        rintro x y ⟨g, rfl⟩
        exact ⟨g, by simp only [twConj, hθ]; group⟩)
      left_inv := by
        intro c
        induction c using Quot.ind with
        | mk x => exact congrArg (Quot.mk _) (mul_inv_cancel_right x u)
      right_inv := by
        intro c
        induction c using Quot.ind with
        | mk x => exact congrArg (Quot.mk _) (inv_mul_cancel_right x u) }
  refine ⟨e, fun c => ?_⟩
  have he : e c = Quot.mk (TwConjugate (thetaE F m)) (c.rep * u) := by
    have hc : c = Quot.mk _ c.rep := (Quot.out_eq c).symm
    calc e c = e (Quot.mk _ c.rep) := congrArg (⇑e) hc
      _ = _ := rfl
  obtain ⟨g, hg⟩ := exists_out (E := F) (n := m) (c.rep * u)
  have key := isRegEll_twConj g (Quot.out (Quot.mk (TwConjugate (thetaE F m)) (c.rep * u)))
  rw [← hg] at key
  rw [he]
  exact ⟨g, hg, key.symm⟩

end GlobalTheory.CompanionTheory.ClassBij

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.G8
open scoped Classical

namespace GlobalTheory.CompanionTheory.AdelCont

open PositivityTheory.Rg.Tf.Loc (twConj)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem orbFn_mul_right (S : Set (Pl E)) (φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ)
    (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E) (U : Subgroup (Gf E a b))
    (hU : ∀ u ∈ U, ∀ y, finFn S φ₁ φ₂ (u⁻¹ * y * thP E a b u) = finFn S φ₁ φ₂ y)
    (x u : Gf E a b) (hu : u ∈ U) : orbFn S φ₁ φ₂ δ₁ δ₂ (x * u) = orbFn S φ₁ φ₂ δ₁ δ₂ x := by
  unfold orbFn
  rw [← hU u hu (x⁻¹ * (ratF E a δ₁, ratF E b δ₂) * thP E a b x), map_mul]
  congr 1
  group

theorem continuous_of_right_invariant {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [TopologicalSpace X] (f : G → X) (U : Subgroup G) (hUo : IsOpen (U : Set G))
    (hf : ∀ x, ∀ u ∈ U, f (x * u) = f x) : Continuous f := by
  have : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hmem : (x⁻¹ * ·) ⁻¹' (U : Set G) ∈ nhds x := by
      apply (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds
      apply hUo.mem_nhds
      simp [U.one_mem]
    filter_upwards [hmem] with y hy
    have := hf x (x⁻¹ * y) hy
    simpa using this
  exact this.continuous

theorem continuous_twConj {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (θ : Monoid.End G) (hθ : Continuous θ) (δ : G) : Continuous fun g : G => twConj θ g δ := by
  unfold twConj
  exact (continuous_inv.mul continuous_const).mul hθ

theorem adelContOf : AdelContOf := by
  intro hEq hFin hComp hTopo E _ _ _ hUnr a b S u₁ u₂ h₁ h₂ ψ φ₁ φ₂ hψ t₁ t₂ d₁ d₂
  obtain ⟨e, he⟩ := hComp E a b
  have hc : Continuous (comps : GA E a × GA E b → Gi E a b × Gf E a b) := by
    have : (comps : GA E a × GA E b → Gi E a b × Gf E a b) = e := funext fun x => (he x).symm
    rw [this]; exact e.continuous
  have hθa : Continuous (thetaR (starRingEnd ℂ) a) := (hTopo E a).2.2.2.2.2
  have hθb : Continuous (thetaR (starRingEnd ℂ) b) := (hTopo E b).2.2.2.2.2
  obtain ⟨U, hUo, hU⟩ := hFin E hUnr a b S φ₁ φ₂ t₁ t₂
  have hfin : Continuous (orbFn S φ₁ φ₂ (d₁ * u₁⁻¹) (d₂ * u₂⁻¹)) :=
    continuous_of_right_invariant _ U hUo fun x u hu => orbFn_mul_right S φ₁ φ₂ _ _ U hU x u hu
  have hrw : (fun x : GA E a × GA E b =>
      adel S u₁ u₂ ψ φ₁ φ₂ (twConj (thetaA E a) x.1 (ratGL E a d₁), twConj (thetaA E b) x.2 (ratGL E b d₂))) =
      fun x => (∏ v, ψ v (twConj (thetaR (starRingEnd ℂ) a) ((comps x).1 v).1 (GeneralLinearGroup.map v.embedding d₁),
        twConj (thetaR (starRingEnd ℂ) b) ((comps x).1 v).2 (GeneralLinearGroup.map v.embedding d₂))) *
      orbFn S φ₁ φ₂ (d₁ * u₁⁻¹) (d₂ * u₂⁻¹) (comps x).2 :=
    funext fun x => hEq E a b S u₁ u₂ h₁ h₂ ψ φ₁ φ₂ d₁ d₂ x
  rw [hrw]
  refine Continuous.mul (continuous_finsetProd _ fun v _ => (hψ v).comp ?_) (hfin.comp (continuous_snd.comp hc))
  have hv : Continuous fun x : GA E a × GA E b => (comps x).1 v :=
    (continuous_apply v).comp (continuous_fst.comp hc)
  exact ((continuous_twConj _ hθa _).comp (continuous_fst.comp hv)).prodMk
    ((continuous_twConj _ hθb _).comp (continuous_snd.comp hv))

end GlobalTheory.CompanionTheory.AdelCont

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.CompanionTheory.FinLevelTw

open PositivityTheory.Rg.BcB.G8

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

def atHom (a b : ℕ) (w : Pl E) : Gf E a b →* GLw a w × GLw b w :=
  (GeneralLinearGroup.map (pLoc E w)).prodMap (GeneralLinearGroup.map (pLoc E w))

omit [IsCMField E] in
theorem atHom_apply (w : Pl E) (y : Gf E a b) : atHom a b w y = atW w y := rfl

theorem continuous_atHom (w : Pl E) : Continuous (atHom (E := E) a b w) :=
  ((GlobalTheory.EulerTwU.continuous_pc w).comp continuous_fst).prodMk ((GlobalTheory.EulerTwU.continuous_pc w).comp continuous_snd)

theorem isOpen_Kf (n : ℕ) : IsOpen (Kf E n : Set (GL (Fin n) (Af E))) := by
  refine Subgroup.isOpen_mono (H₁ := GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n) ?_
    (GroundTheory.Automorphic.AdelicGLn.isOpen_integralFiniteGL E n)
  intro g hg
  obtain ⟨h1, h2⟩ := (GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff E n).1 hg
  refine Subgroup.mem_iInf.2 fun w => Subgroup.mem_comap.2 ?_
  refine GlobalTheory.EulerTwU.mem_GLint _ _ (fun i j => ?_) (fun i j => ?_)
  · exact GroundTheory.Global.mem_integralFiniteAdeles.1 (h1 i j) w
  · rw [← map_inv]
    exact GroundTheory.Global.mem_integralFiniteAdeles.1 (h2 i j) w

theorem continuous_thP : Continuous (thP E a b) := by
  have h : ∀ n, Continuous (thF E n) := fun n => GlobalTheory.ThetaPull.continuous_thetaGL _ (continuous_conjFin _)
  exact ((h a).comp continuous_fst).prodMk ((h b).comp continuous_snd)

theorem thP_thP (y : Gf E a b) : thP E a b (thP E a b y) = y :=
  Prod.ext (GlobalTheory.EulerTwU.thF_thF y.1) (GlobalTheory.EulerTwU.thF_thF y.2)

theorem isOpen_family (M : ∀ w : Pl E, Subgroup (GLw a w × GLw b w)) (hM : ∀ w, IsOpen (M w : Set (GLw a w × GLw b w)))
    (hK : ∀ᶠ w in cofinite, K2 a b w ≤ M w) :
    IsOpen ((⨅ w, (M w).comap (atHom a b w) : Subgroup (Gf E a b)) : Set (Gf E a b)) := by
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  have hT : {w | ¬ K2 a b w ≤ M w}.Finite := hK
  have h1 : ∀ᶠ u in nhds (1 : Gf E a b), ∀ w ∈ {w | ¬ K2 a b w ≤ M w}, atHom a b w u ∈ M w :=
    (Filter.eventually_all_finite hT).2 fun w _ =>
      (continuous_atHom w).continuousAt.eventually_mem
        ((hM w).mem_nhds (by rw [map_one]; exact one_mem _))
  have h2 : ∀ᶠ u in nhds (1 : Gf E a b), u ∈ ((Kf E a).prod (Kf E b) : Subgroup (Gf E a b)) :=
    ((isOpen_Kf a).prod (isOpen_Kf b)).mem_nhds ⟨one_mem _, one_mem _⟩
  filter_upwards [h1, h2] with u hu1 hu2
  refine Subgroup.mem_iInf.2 fun w => Subgroup.mem_comap.2 ?_
  by_cases hw : K2 a b w ≤ M w
  · refine hw ⟨?_, ?_⟩
    · exact Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 hu2.1 w)
    · exact Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 hu2.2 w)
  · exact hu1 w hw

theorem exists_level_of_test {φ : ∀ w : Pl E, GLw a w × GLw b w → ℂ} (h : IsTestP φ) :
    ∃ L : ∀ w : Pl E, Subgroup (GLw a w × GLw b w), (∀ w, IsOpen (L w : Set (GLw a w × GLw b w))) ∧
      (∀ᶠ w in cofinite, L w = K2 a b w) ∧ ∀ w, ∀ k ∈ L w, ∀ x, φ w (k * x) = φ w x ∧ φ w (x * k) = φ w x := by
  obtain ⟨K₁, K₂, h₁, h₂, h₃⟩ := h
  refine ⟨fun w => (K₁ w).prod (K₂ w), fun w => ?_, ?_, fun w => (h₃.1 w).2⟩
  · rw [Subgroup.coe_prod]
    exact (h₁.1 w).1.prod (h₂.1 w).1
  · filter_upwards [h₁.2, h₂.2] with w e₁ e₂
    rw [e₁, e₂]

theorem finLevel : FinLevel := by
  intro E _ _ _ _ a b S φ₁ φ₂ h₁ h₂
  obtain ⟨L₁, o₁, e₁, i₁⟩ := exists_level_of_test h₁
  obtain ⟨L₂, o₂, e₂, i₂⟩ := exists_level_of_test h₂
  let A : Subgroup (Gf E a b) := ⨅ w, (L₁ w ⊓ L₂ w).comap (atHom a b w)
  have hA : IsOpen (A : Set (Gf E a b)) := by
    refine isOpen_family _ (fun w => ?_) ?_
    · rw [Subgroup.coe_inf]
      exact (o₁ w).inter (o₂ w)
    · filter_upwards [e₁, e₂] with w f₁ f₂
      rw [f₁, f₂, inf_idem]
  have mA : ∀ {u}, u ∈ A → ∀ w, atW w u ∈ L₁ w ⊓ L₂ w := fun hu w =>
    Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 hu w)
  refine ⟨A ⊓ A.comap (thP E a b), ?_, fun u hu y => ?_⟩
  · rw [Subgroup.coe_inf]
    exact hA.inter (hA.preimage continuous_thP)
  · have hu₁ := mA hu.1
    have hu₂ := mA (Subgroup.mem_comap.1 hu.2)
    have key : ∀ (w : Pl E) (f : GLw a w × GLw b w → ℂ) (k k' x : GLw a w × GLw b w),
        (∀ c ∈ ({k⁻¹, k'} : Set _), ∀ x, f (c * x) = f x ∧ f (x * c) = f x) → f (k⁻¹ * x * k') = f x := by
      intro w f k k' x h
      rw [(h k' (by simp) _).2, (h k⁻¹ (by simp) _).1]
    unfold finFn
    refine finprod_congr fun w => finprod_congr fun _ => ?_
    have m₁ : atW w (u⁻¹ * y * thP E a b u) = (atW w u)⁻¹ * atW w y * atW w (thP E a b u) := by
      simp only [← atHom_apply, map_mul, map_inv]
    have m₂ : atW w (thP E a b (u⁻¹ * y * thP E a b u)) =
        (atW w (thP E a b u))⁻¹ * atW w (thP E a b y) * atW w u := by
      simp only [← atHom_apply, map_mul, map_inv, thP_thP]
    rw [m₁, m₂, key w (φ₁ w), key w (φ₂ w)]
    · intro c hc x
      rcases hc with rfl | rfl
      · exact i₂ w _ (inv_mem (hu₂ w).2) x
      · exact i₂ w _ (hu₁ w).2 x
    · intro c hc x
      rcases hc with rfl | rfl
      · exact i₁ w _ (inv_mem (hu₁ w).1) x
      · exact i₁ w _ (hu₂ w).1 x

end GlobalTheory.CompanionTheory.FinLevelTw

end
end

section

open NumberField IsDedekindDomain Matrix

namespace GlobalTheory.CompanionTheory.IntegralPoints

theorem isOpen_isCompact_intGL {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    (O : Subring R) (ho : IsOpen (O : Set R)) (hc : IsCompact (O : Set R)) (n : ℕ) :
    IsOpen {g : GL (Fin n) R | (∀ i j, (g : Matrix (Fin n) (Fin n) R) i j ∈ O) ∧
        ∀ i j, ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j ∈ O} ∧
    IsCompact {g : GL (Fin n) R | (∀ i j, (g : Matrix (Fin n) (Fin n) R) i j ∈ O) ∧
        ∀ i j, ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j ∈ O} := by
  constructor
  · have e : {g : GL (Fin n) R | (∀ i j, (g : Matrix (Fin n) (Fin n) R) i j ∈ O) ∧
        ∀ i j, ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j ∈ O} =
        (⋂ i, ⋂ j, (fun g : GL (Fin n) R => (g : Matrix (Fin n) (Fin n) R) i j) ⁻¹' (O : Set R)) ∩
        (⋂ i, ⋂ j, (fun g : GL (Fin n) R => ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j) ⁻¹' (O : Set R)) := by
      ext g
      simp [Set.mem_iInter]
    rw [e]
    refine IsOpen.inter ?_ ?_
    · exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        ho.preimage (Units.continuous_val.matrix_elem i j)
    · exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        ho.preimage (Units.continuous_coe_inv.matrix_elem i j)
  · have hM : IsCompact {A : Matrix (Fin n) (Fin n) R | ∀ i j, A i j ∈ O} := by
      have := isCompact_univ_pi fun _ : Fin n => isCompact_univ_pi fun _ : Fin n => hc
      have e : {A : Matrix (Fin n) (Fin n) R | ∀ i j, A i j ∈ O} =
          Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => (O : Set R) :=
        Set.ext fun A => ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
      exact e ▸ this
    have := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) R)).isCompact_preimage
      (hM.prod (hM.image MulOpposite.continuous_op))
    convert this using 1
    ext g
    exact ⟨fun h => ⟨h.1, _, h.2, rfl⟩, fun ⟨h1, A, hA, e⟩ => ⟨h1, fun i j => by
      have : A = ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) := MulOpposite.op_injective e
      exact this ▸ hA i j⟩⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem coe_Kf (n : ℕ) : (PositivityTheory.Rg.BcB.G8.Kf E n : Set (GL (Fin n) (FiniteAdeleRing (𝓞 E) E))) =
    {g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E) | (∀ i j, (g : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j ∈ Formalism.UG.intAd E) ∧
      ∀ i j, ((g⁻¹ : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j ∈
        Formalism.UG.intAd E} := by
  ext g
  simp only [SetLike.mem_coe, PositivityTheory.Rg.BcB.G8.Kf, Subgroup.mem_iInf, Subgroup.mem_comap, Set.mem_setOf_eq]
  constructor
  · intro h
    refine ⟨fun i j w => ?_, fun i j w => ?_⟩
    · have h1 := h w
      rw [← SetLike.mem_coe, GlobalTheory.LFun.KGL, GlobalTheory.LFun.IntPtsUnitary.coe_GLint] at h1
      exact h1.1 i j
    · have h1 := h w
      rw [← SetLike.mem_coe, GlobalTheory.LFun.KGL, GlobalTheory.LFun.IntPtsUnitary.coe_GLint] at h1
      have h2 := h1.2 i j
      rw [← map_inv] at h2
      exact h2
  · rintro ⟨h1, h2⟩ w
    rw [← SetLike.mem_coe, GlobalTheory.LFun.KGL, GlobalTheory.LFun.IntPtsUnitary.coe_GLint]
    refine ⟨fun i j => h1 i j w, fun i j => ?_⟩
    rw [← map_inv]
    exact h2 i j w

theorem kfOC : PositivityTheory.Rg.BcB.G8.KfOC := by
  intro E _ _ _ n
  haveI : T2Space (FiniteAdeleRing (𝓞 E) E) := Formalism.MainNotions.Gaps.LevGap.t2Space_adeleRing_numberField
  rw [coe_Kf]
  exact isOpen_isCompact_intGL (Formalism.UG.intAd E) Formalism.MainNotions.Gaps.LevGap.isOpen_intAd
    Formalism.MainNotions.Gaps.LevGap.isCompact_intAd n

end GlobalTheory.CompanionTheory.IntegralPoints
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.theta_fourier_coefficient_weyl_integral : ∀ {D : D7} {t ρ : ℕ} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) {θ : InfFam D} {b₀ : HermE D ρ} {μ : Measure (Mx D ρ t)} {Ω : G D t → Mx D ρ t → ℂ} (hΩ : IsTh ψ χ θ b₀ μ Ω) {nb : hermA D t → G D t} (hnb : IsNMap nb) {w : G D t} (hw : IsW w) (b : hermA D t) (y₀ : Mx D ρ t), ∫ y, ψ (trA (Matrix.trace (pr b₀ y y₀))) * conj (Ω (w * nb b) y) ∂μ = conj (ψ (halfTr (Matrix.trace (mm b.1 (pr b₀ y₀ y₀)))) * Ω 1 y₀) := by
  first | exact @GlobalTheory.CompanionTheory.RCellInv.fourier_inv | exact GlobalTheory.CompanionTheory.RCellInv.fourier_inv | (intros; apply GlobalTheory.CompanionTheory.RCellInv.fourier_inv <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.weil_representation_theta_integral : ∀ {D : D7} {n r t : ℕ} (hP : PartFT) {hn : r + t = n} (M : Maps D hn) (m : Meas D r t) (V : HSp D) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (hη : ResEta D χ V.rank) {θ : InfFam D} (hθ : IsInfFam θ) {μ : Measure (Mx D V.rank n)} (hμ : ∃ 𝓕, IsCovolOne (ratMx D V.rank n) μ 𝓕) {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} (hω : IsWeilSch ψ χ θ V μ ω) {μr : Measure (Mx D V.rank r)} (hμr : ∃ 𝓕, IsCovolOne (ratMx D V.rank r) μr 𝓕) {μt : Measure (Mx D V.rank t)} (hμt : ∃ 𝓕, IsCovolOne (ratMx D V.rank t) μt 𝓕) (b₀ : HermE D r) {fib : Measure (Mx D V.rank r)} (hfib : IsFib ψ θ V b₀ μr m.lz fib) (Φ : schwartzA θ V.rank n) (g : G D n), Wz M m ψ b₀ (fun g => (ω g Φ).1 0) g = ∫ x, (ω g Φ).1 (jn hn x 0) ∂fib := by
  first | exact @GlobalTheory.CompanionTheory.WzFib.wz_eq_fib | exact GlobalTheory.CompanionTheory.WzFib.wz_eq_fib | (intros; apply GlobalTheory.CompanionTheory.WzFib.wz_eq_fib <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.weil_representation_fourier_coefficient : ∀ {D : D7} {n r t : ℕ} (hP : PartFT) {hn : r + t = n} (M : Maps D hn) (V : HSp D) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (hη : ResEta D χ V.rank) {θ : InfFam D} (hθ : IsInfFam θ) {μ : Measure (Mx D V.rank n)} (hμ : ∃ 𝓕, IsCovolOne (ratMx D V.rank n) μ 𝓕) {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} (hω : IsWeilSch ψ χ θ V μ ω) {μr : Measure (Mx D V.rank r)} (hμr : ∃ 𝓕, IsCovolOne (ratMx D V.rank r) μr 𝓕) {μt : Measure (Mx D V.rank t)} (hμt : ∃ 𝓕, IsCovolOne (ratMx D V.rank t) μt 𝓕) (Φ : schwartzA θ V.rank n) {nb : hermA D t → G D t} (hnb : IsNMap nb) {w : G D t} (hw : IsW w) (b : hermA D t) (y : Mx D r t) (x : Mx D V.rank r), (ω (M.sh y * M.emb (w * nb b) * 1) Φ).1 (jn hn x 0) = ∫ v, pch ψ b.1 (ip V v v) * Φ.1 (jn hn x v) * ψ (trA (Matrix.trace (ip V (mm x y) v))) ∂μt := by
  first | exact @GlobalTheory.CompanionTheory.CellVal.weil_translate_frame | exact GlobalTheory.CompanionTheory.CellVal.weil_translate_frame | (intros; apply GlobalTheory.CompanionTheory.CellVal.weil_translate_frame <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.shift_unipotent_levi_commutator : ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (g₁ : G D p) (b : Mx D p p), mat g₁ = blk4 1 b 0 1 →
  ∀ y : Mx D ρ p, ∃ (z₀ : hermA D ρ) (x₀ : Mx D ρ p), M.sh y * M.emb g₁ = M.nzx z₀ x₀ * M.emb g₁ * M.sh y ∧
    z₀.1 = HMul.hMul (HMul.hMul y b : Mx D ρ p) (adj y) := by
  first | exact @GlobalTheory.CompanionTheory.ShEmbUnip.sh_emb_unip | exact GlobalTheory.CompanionTheory.ShEmbUnip.sh_emb_unip | (intros; apply GlobalTheory.CompanionTheory.ShEmbUnip.sh_emb_unip <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.Lbc

theorem c3 : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], PositivityTheory.Lbc.C3 k := by
  intro k _ _ _ _ N h d hd J hJo hJc hJf hpos V _ _ π hπ
  exact ⟨GlobalTheory.T.jacquet_projection_fixed_surjective k N h d hd J hJo hJc hJf hpos V π hπ.1,
    GlobalTheory.T.jacquet_fixed_vector_lift k N h d hd J hJo hJc hJf hpos V π hπ,
    GlobalTheory.T.strictly_dominant_hecke_kernel k N h d hd J hJo hJc hJf hpos V π hπ.1⟩

end GlobalTheory.CompanionTheory.Lbc
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)

theorem _root_.GlobalTheory.T.eisenstein_hecke_functional : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), B.IsGood σ → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → ∀ (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → ∀ (χ : Chr F E) (s₁ : ℂ) (f : G2 σ Y → ℂ), IsSec K χ s₁ f → IsHecke F E χ → ∀ (t : ℝ) (Ê : ℂ → G2 σ Y → ℂ), (∀ s : ℂ, t < s.re → ∀ x, HasSum (eisTerm (flat a f s₁ s) x) (Ê s x)) → ∀ s : ℂ, t < s.re → ∀ γ ∈ rat2 σ Y, ∀ x, Ê s (γ * x) = Ê s x := by
  first | exact @GlobalTheory.CompanionTheory.EisRat.eis_left_rat | exact GlobalTheory.CompanionTheory.EisRat.eis_left_rat | (intros; apply GlobalTheory.CompanionTheory.EisRat.eis_left_rat <;> assumption)
end
