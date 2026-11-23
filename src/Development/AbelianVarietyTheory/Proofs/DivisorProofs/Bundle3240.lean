module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle022
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1185
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle296
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2582
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1239
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3205
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle208
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2321
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1342
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2585
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ReadingLinearIndependentAndInjective
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle035
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle107
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2913
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3149
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2901
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2704
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2702
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2703
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3206
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2644
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueAffineCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3208
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3207
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

theorem _root_.GlobalTheory.T.exists_product_small_twistedFunctionalEqn_family : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ b, FormalEnd U.toUnifPre a h' b → ∀ (n j n' j' n'' j'' : ℤ), n'' = n + n' → j'' = j + j' → ∀ (f : ∀ β, SecT D.toPre a n j β) (g : ∀ β, SecT D.toPre a n' j' β), Small (maximalIdeal R) (w := id) f → Small (maximalIdeal R) (w := id) g → TFE h h' f → TFE h h' g → ∃ F : ∀ β, SecT D.toPre a n'' j'' β, Small (maximalIdeal R) (w := id) F ∧ TFE h h' F ∧ ∀ (e : ℕ) (τ : SecE U.toUnifPre (b e) n j) (τ' : SecE U.toUnifPre (b e) n' j'), TExp U.toUnifPre τ (w := id) f → TExp U.toUnifPre τ' (w := id) g → ∃ τ'' : SecE U.toUnifPre (b e) n'' j'', (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J'), Good U.LG.L z J' → sval τ'' x z J' = sval τ x z J' * sval τ' x z J') ∧ TExp U.toUnifPre τ'' (w := id) F := by
  first | exact @GlobalTheory.TwFam.exists_prod_family | exact GlobalTheory.TwFam.exists_prod_family | (intros; apply GlobalTheory.TwFam.exists_prod_family <;> assumption)
end

section

noncomputable section
namespace GlobalTheory.FlatPair
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
  GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

section Lemmas
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem relab_mem {σ : c.F →+* ℂ} (V : Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : IsUnf V) (τ : Psi H) (k : V.Comp) :
    relab c σ τ.1 ∈ (V.X k).Ψ :=
  ((hU.2.1 k).2 _).2 (by
    have hσ0 : σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ = H.rt0 := hσ
    exact (congrArg σ (Subtype.ext τ.2)).trans hσ0)

theorem modelWt_shift {σ : c.F →+* ℂ} (V : Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : IsUnf V) (τ : Psi H)
    {G G' : WTZ E} (hG : Even G.2) (h : exZ Dw G' = exZ Dw (G + wtOf Dw (flatWt Dw τ) 0)) (k : V.Comp)
    (hτ : relab c σ τ.1 ∈ (V.X k).Ψ) : modelWt V G' k = modelWt V G k + modelFlat r ⟨_, hτ⟩ := by
  rw [modelWt_congr V hσ hU h, modelWt_add V hG (even_wtOf _ _), modelWt_flatWt V hσ hU τ k hτ]

theorem cuspOn_congr {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (Z : Comp Xo c)
    {G G' : WTZ E} (h : exZ Dw G = exZ Dw G') : cuspOn U Z G = cuspOn U Z G' := by
  ext f
  simp only [cuspOn, Submodule.mem_inf, mem_cuspW, h]
  refine and_congr_left fun _ => and_congr_right fun _ => forall₂_congr fun σ hσ => ?_
  rw [modelWt_congr (U σ) hσ (hU σ hσ) h]

theorem res_indep {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} (hL : Laws U x) (Z : Comp Xo c)
    (σ : c.F →+* ℂ) (hσ : GoodEmb c σ) (k0 : (U σ).Comp)
    (hk : framesOn (U σ) Z = {z | z.1 = k0 ∧ z.2 ∈ ((U σ).X z.1).dom}) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    (∀ (m : ℕ) (b : Fin m → Rul Xo c), (∀ i, b i ∈ sec Xo c a n) → (∀ i, b i ∈ suppOn Z) →
      LinearIndependent c.F b →
      LinearIndependent ℂ (fun i => fun y : ↥((U σ).X k0).dom => rdU (U σ) (b i) k0 y.1)) ∧
    ∀ f ∈ sec Xo c a n, f ∈ suppOn Z → f ≠ 0 → ∃ y : ↥((U σ).X k0).dom, rdU (U σ) f k0 y.1 ≠ 0 := by
  have hR := GlobalTheory.reading_linearIndependent_and_injective GlobalTheory.abelianSchemeLaws_all.1.secBaseChange _ H Dw l Xo c σ r
    (Formalism.L2.PjFree.Unf.ofPj (U σ)) (hL.unf σ hσ) a n
  simp only [Formalism.L2.PjFree.rdU_ofPj] at hR
  have hoff : ∀ f ∈ suppOn Z, ∀ k y, (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∉ framesOn (U σ) Z →
      rdU (U σ) f k y = 0 := fun f hf k y hz => rdU_eq_zero (U σ) hf hz
  refine ⟨fun m b hb hs hli => ?_, fun f hf hs hne => ?_⟩
  · have h0 : LinearIndependent ℂ (fun i => rdU (U σ) (b i)) := hR.1 m b hb hli
    rw [Fintype.linearIndependent_iff] at h0 ⊢
    intro w hw
    refine h0 w ?_
    funext k y
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    by_cases hz : (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z
    · rw [hk] at hz
      obtain ⟨rfl, hy⟩ := hz
      have := congrFun hw ⟨y, hy⟩
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using this
    · exact Finset.sum_eq_zero fun i _ => by rw [hoff _ (hs i) k y hz, mul_zero]
  · by_contra hall
    push_neg at hall
    refine hne (hR.2 f hf fun k y hy => ?_)
    by_cases hz : (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z
    · rw [hk] at hz
      obtain ⟨rfl, hy'⟩ := hz
      exact hall ⟨y, hy'⟩
    · exact hoff f hs k y hz

theorem horizGen_mem (X : Data E r) (τ : X.Ψ) :
    (fun y : ↥X.dom => horizGen τ y.1) ∈ holAlg X ∧ (fun y : ↥X.dom => (horizGen τ y.1)⁻¹) ∈ holAlg X ∧
      ∀ y ∈ X.dom, horizGen τ y ≠ 0 := by
  have hdet : Differentiable ℂ (fun y : Frame X.Ψ r => (mat y τ).det) := by
    have e : (fun y : Frame X.Ψ r => (mat y τ).det) =
        fun y => ∑ p : Equiv.Perm (Fin r), ((Equiv.Perm.sign p : ℤ) : ℂ) * ∏ i, y τ (p i) i := by
      funext y
      rw [Matrix.det_apply]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Units.smul_def, zsmul_eq_mul]
      rfl
    rw [e]
    fun_prop
  have hne : ∀ y ∈ X.dom, (mat y τ).det ≠ 0 := fun y hy => (hy τ).1
  refine ⟨⟨fun y => horizGen τ y, ?_, fun y => rfl⟩, ⟨fun y => (horizGen τ y)⁻¹, ?_, fun y => rfl⟩,
    fun y hy => inv_ne_zero (hne y hy)⟩
  · exact (hdet.differentiableOn).inv hne
  · have : (fun y => (horizGen τ y)⁻¹) = fun y : Frame X.Ψ r => (mat y τ).det := by
      funext y; simp [horizGen]
    rw [this]; exact hdet.differentiableOn

theorem resRd_mem_holAlg {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} (σ : c.F →+* ℂ) (hσ : GoodEmb c σ)
    (hT : AllTest Xo c) (k : (U σ).Comp) (G : WTZ E) (f : Rul Xo c) (hf : f ∈ cuspW Xo c U G) :
    resRd (U σ) hT k f ∈ holAlg ((U σ).X k) := by
  have h1 := (mem_cuspW.1 hf).2 σ hσ
  have h2 : ∀ P ∈ holSub (U σ).X (modelWt (U σ) G), DifferentiableOn ℂ (P k) ((U σ).X k).dom := by
    intro P hP
    induction hP using Submodule.span_induction with
    | mem P hP => exact (hP k).1.1.1
    | zero => exact differentiableOn_const 0
    | add P Q _ _ hP hQ => exact hP.add hQ
    | smul a P _ hP => exact (differentiableOn_const a).mul hP
  exact ⟨rdU (U σ) f k, h2 _ h1, fun y => rfl⟩

end Lemmas

set_option synthInstance.maxHeartbeats 200000 in
theorem flat_pair : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)
    (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (τ : Psi H), ∃ (G : WTZ E) (f g : Rul Xo c), Even G.2 ∧
      f ∈ cuspOn U Z G ∧ g ∈ cuspOn U Z (G + wtOf Dw (flatWt Dw τ) 0) ∧ f ≠ 0 ∧ IsFlatQuot U Z τ f g := by
  intro E _ _ _ H Dw l Xo c r U x hL Z τ
  obtain ⟨a, n, hD, h2, hn, f0, hf0, hf0ne⟩ := GlobalTheory.T.exists_nonzero_cuspForm_parallelWeight_each_component E H Dw l Xo c r U x hL Z
  obtain ⟨a', hD', h1', hex⟩ := GlobalTheory.T.exists_dominant_weight_shift_flatLineDet E H Dw a n τ hD h2
  have h1 : ∀ ρ i, i < Dw.mult ρ → 1 ≤ a (ρ, i) := fun ρ i hi => le_trans (by norm_num) (h2 ρ i hi)
  have hT : AllTest Xo c :=
    GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H Dw l Xo c
  have hEv : Even (wtZ a n).2 := by
    obtain ⟨m, hm⟩ := hD.2
    exact ⟨m, by simp [wtZ, hm]⟩
  have hVV' : cuspOn U Z (wtZ a' n) = cuspOn U Z (wtZ a n + wtOf Dw (flatWt Dw τ) 0) :=
    cuspOn_congr hL.unf Z hex

  have hsec : ∀ (b : (E →+* ℂ) × ℕ → ℕ), cuspOn U Z (wtZ b n) ≤ sec Xo c b n := fun b f hf => by
    have := cuspW_le_secZ (U := U) (wtZ b n) (cuspOn_le U Z _ hf)
    rwa [AllWt.exZ_wtZ, secZ_nat] at this
  have hsupp : ∀ (G : WTZ E), cuspOn U Z G ≤ suppOn Z := fun G => inf_le_right
  have pk : ∀ σ, GoodEmb c σ → ∃ (k0 : (U σ).Comp) (hτ : relab c σ τ.1 ∈ ((U σ).X k0).Ψ),
      framesOn (U σ) Z = {z | z.1 = k0 ∧ z.2 ∈ ((U σ).X z.1).dom} ∧
      (∀ f ∈ cuspOn U Z (wtZ a n), (fun y : ↥((U σ).X k0).dom => horizGen ⟨_, hτ⟩ y.1) * resRd (U σ) hT k0 f ∈
        Submodule.span ℂ (resRd (U σ) hT k0 '' (cuspOn U Z (wtZ a' n) : Set (Rul Xo c)))) ∧
      (∀ f ∈ cuspOn U Z (wtZ a' n), (fun y : ↥((U σ).X k0).dom => (horizGen ⟨_, hτ⟩ y.1)⁻¹) * resRd (U σ) hT k0 f ∈
        Submodule.span ℂ (resRd (U σ) hT k0 '' (cuspOn U Z (wtZ a n) : Set (Rul Xo c)))) := by
    intro σ hσ
    obtain ⟨k0, hk⟩ := framesOn_eq_model E H Dw l Xo c r U x hL Z σ hσ
    have hτ := relab_mem (U σ) hσ (hL.unf σ hσ) τ k0
    have hw := modelWt_shift (U σ) hσ (hL.unf σ hσ) τ hEv hex k0 hτ
    refine ⟨k0, hτ, hk, fun f hf => ?_, fun f hf => ?_⟩
    · have := GlobalTheory.T.horizontalGenerator_zpow_mul_cuspForm_mem_span E H Dw l Xo c r U x hL Z σ hσ k0 hk ⟨_, hτ⟩ 1 a a' n hD hD' h1' hn (by rw [hw, one_smul]) f hf
      convert this using 1 <;> first | rfl | (funext y; simp [resRd_apply])
    · have := GlobalTheory.T.horizontalGenerator_zpow_mul_cuspForm_mem_span E H Dw l Xo c r U x hL Z σ hσ k0 hk ⟨_, hτ⟩ (-1) a' a n hD' hD h1 hn
        (by rw [hw, neg_one_smul, add_neg_cancel_right]) f hf
      convert this using 1 <;> first | rfl | (funext y; simp [resRd_apply])
  obtain ⟨σ0, hσ0⟩ : ∃ σ, GoodEmb c σ := ⟨_, goodEmb_goodOf c c.F.val.toRingHom⟩
  haveI : FiniteDimensional c.F (cuspOn U Z (wtZ a n)) :=
    (GlobalTheory.T.cuspForms_component_finiteDimensional_and_spanned E H Dw l Xo c r U x hL Z σ0 hσ0 a n hD h1 hn).1
  haveI : FiniteDimensional c.F (cuspOn U Z (wtZ a' n)) :=
    (GlobalTheory.T.cuspForms_component_finiteDimensional_and_spanned E H Dw l Xo c r U x hL Z σ0 hσ0 a' n hD' h1' hn).1
  have hprod : ∀ f ∈ cuspOn U Z (wtZ a n), ∀ g ∈ cuspOn U Z (wtZ a' n),
      f * g ∈ sec Xo c (a + a') (n + n) ⊓ suppOn Z := by
    intro f hf g hg
    have e : exZ Dw (wtZ (a + a') (n + n)) = exZ Dw (wtZ a n) + exZ Dw (wtZ a' n) := by
      rw [wtZ_add]; funext i; exact exZ_add _ _ i
    have hm := mul_mem_secZ (cuspW_le_secZ (U := U) _ (cuspOn_le U Z _ hf))
      (cuspW_le_secZ (U := U) _ (cuspOn_le U Z _ hg))
    rw [← e, AllWt.exZ_wtZ, secZ_nat] at hm
    refine ⟨hm, ?_⟩
    rw [mul_comm]
    exact mul_mem_suppOn g (hsupp _ hf)
  obtain ⟨k0, hτ0, hk0, hA0, -⟩ := pk σ0 hσ0
  obtain ⟨T, hT0, hTc⟩ := GlobalTheory.T.exists_rational_multiplier_of_complex_multiplier c.F (Rul Xo c) (↥((U σ0).X k0).dom → ℂ) σ0 (resRd (U σ0) hT k0)
    (resRd_smul (U σ0) hT k0) (cuspOn U Z (wtZ a n)) (cuspOn U Z (wtZ a' n))
    (fun m b hb hli => by
      have hb' : ∀ i, b i ∈ sec Xo c (a + a') (n + n) ⊓ suppOn Z := fun i =>
        (Submodule.mul_le.2 hprod) (hb i)
      exact (res_indep hL Z σ0 hσ0 k0 hk0 (a + a') (n + n)).1 m b (fun i => (hb' i).1) (fun i => (hb' i).2) hli)
    (fun y => horizGen ⟨_, hτ0⟩ y.1) hA0 ⟨f0, hf0, fun h0 => by
      obtain ⟨y, hy⟩ := (res_indep hL Z σ0 hσ0 k0 hk0 a n).2 f0 (hsec a hf0) (hsupp _ hf0) hf0ne
      have := congrFun h0 y
      simp only [Pi.mul_apply, resRd_apply, Pi.zero_apply, mul_eq_zero] at this
      rcases this with h | h
      · exact (horizGen_mem _ _).2.2 y.1 y.2 h
      · exact hy h⟩
  refine ⟨wtZ a n, f0, T ⟨f0, hf0⟩, hEv, hf0, hVV' ▸ (T ⟨f0, hf0⟩).2, hf0ne, fun σ hσ => ?_⟩
  obtain ⟨k1, hτ, hk, hA, hA'⟩ := pk σ hσ
  obtain ⟨y0, -⟩ := (res_indep hL Z σ hσ k1 hk a n).2 f0 (hsec a hf0) (hsupp _ hf0) hf0ne
  haveI := GlobalTheory.T.holomorphicRestrictionSubalgebraFrameDomain_isDomain E r ((U σ).X k1) ⟨y0.1, y0.2⟩
  obtain ⟨hh, hh', hne⟩ := horizGen_mem ((U σ).X k1) ⟨_, hτ⟩
  obtain ⟨α, hα, hαT⟩ := GlobalTheory.T.commuting_multiplier_eq_const_smul_generator_alt c.F (Rul Xo c) (↥((U σ).X k1).dom → ℂ) σ (resRd (U σ) hT k1)
    (resRd_smul _ _ _) (holAlg ((U σ).X k1)) (cuspOn U Z (wtZ a n)) (cuspOn U Z (wtZ a' n))
    (fun f hf => resRd_mem_holAlg σ hσ hT k1 _ f (cuspOn_le U Z _ hf))
    (fun f hf => resRd_mem_holAlg σ hσ hT k1 _ f (cuspOn_le U Z _ hf))
    (fun m b hb hli => (res_indep hL Z σ hσ k1 hk a n).1 m b (fun i => hsec a (hb i)) (fun i => hsupp _ (hb i)) hli)
    (fun m b hb hli => (res_indep hL Z σ hσ k1 hk a' n).1 m b (fun i => hsec a' (hb i)) (fun i => hsupp _ (hb i))
      hli)
    _ _ hh hh' (by funext y; exact mul_inv_cancel₀ (hne y.1 y.2)) hA' T hT0 hTc
  refine ⟨α, hα, fun k hτk y hy => ?_⟩
  rw [hk] at hy
  obtain ⟨rfl, hyd⟩ := hy
  have e := congrFun (hαT ⟨f0, hf0⟩) ⟨y, hyd⟩
  simp only [resRd_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul] at e
  rw [e]
  ring

end GlobalTheory.FlatPair
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.mixedChernMeasure_finite_integrable_projective : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (D : ℕ), IsProjOver p → topologicalKrullDim X = (D : ℕ) → ∀ (L : Fin D → MLine p σ), (∀ ε : ℤˣ, IsFiniteMeasure (part L ε)) ∧ ∀ f : CxPts p σ → ℝ, Continuous f → Intg L f := by
  first | exact @GlobalTheory.MixFin.finite_and_intg | exact GlobalTheory.MixFin.finite_and_intg | (intros; apply GlobalTheory.MixFin.finite_and_intg <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.ThInt

theorem spMap_comp_ring' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem grpPullback_self' {S : Scheme.{0}} (G : Over S) [GrpObj G] : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let ρ : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have ex : x₀ = ρ ≫ x := Over.OverMorphism.ext (hx.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  have ey : y₀ = ρ ≫ y := Over.OverMorphism.ext (hy.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  rw [ex, ey, ← MonObj.comp_mul]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

theorem sec_eq' {X : Scheme.{0}} {M : LB X} {s s' : LB.Sec M} (h : ∀ j, s.f j = s'.f j) : s = s' := by
  cases s; cases s'
  simp only [LB.Sec.mk.injEq]
  exact funext h

theorem pullS_comp' {S : Scheme.{0}} (G : Over S) [GrpObj G] {L : LB G.left} (hL : L.IsLB) (a : ℤ) {T T' T'' : Over S}
    (h : T' ⟶ T) (h' : T'' ⟶ T') (s : LB.Sec (LPow G L a T)) :
    VVRank.pullS G a h' (VVRank.pullS G a h s) = VVRank.pullS G a (h' ≫ h) s := by
  refine sec_eq' (sec_ext_val hL (fun y J hJ => ?_))
  refine (VVRank.sv_pullS G a h' _ (𝟙 _) y hJ).trans ((VVRank.sv_pullS G a h s _ y hJ).trans ?_)
  refine Eq.trans ?_ (VVRank.sv_pullS G a (h' ≫ h) s (𝟙 _) y hJ).symm
  rw [MonoidalCategory.comp_whiskerRight, Over.comp_left, Category.assoc]

theorem thList_congr' {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} {ρ : LB.Gen (L.pull (eSec G))}
    {m : ℕ} {R : Type} [CommRing R] {x : Sp R ⟶ S} (θ : SecAt G L x) {K : Type} [Field K]
    {y y' : Sp K ⟶ S} (e : y = y') (u : Over.mk y ⟶ Over.mk x) (u' : Over.mk y' ⟶ Over.mk x) (hu : u.left = u'.left)
    {N : ℕ} {pt : Fin N → (Over.mk y ⟶ G)} {c : Fin N → K} (H : ThList G L ρ m y (VVRank.pullS G _ u θ) pt c) :
    ∃ pt' : Fin N → (Over.mk y' ⟶ G), ThList G L ρ m y' (VVRank.pullS G _ u' θ) pt' c := by
  subst e
  obtain rfl : u = u' := Over.OverMorphism.ext hu
  exact ⟨pt, H⟩

theorem thList_pull_pull {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} (hL : L.IsLB)
    {ρ : LB.Gen (L.pull (eSec G))} {m : ℕ} {R R' : Type} [CommRing R] [CommRing R'] {K : Type} [Field K]
    (x : Sp R ⟶ S) (θ : SecAt G L x) (i : R →+* R') (j : R' →+* K) {N : ℕ}
    {pt : Fin N → (Over.mk (spMap j ≫ spMap i ≫ x) ⟶ G)} {c : Fin N → K}
    (H : ThList G L ρ m (spMap j ≫ spMap i ≫ x) (SecAt.pull G L (SecAt.pull G L θ i) j) pt c) :
    ∃ pt' : Fin N → (Over.mk (spMap (j.comp i) ≫ x) ⟶ G), ThList G L ρ m (spMap (j.comp i) ≫ x)
      (SecAt.pull G L θ (j.comp i)) pt' c := by
  simp only [SecAt.pull] at H ⊢
  rw [pullS_comp' G hL] at H
  refine thList_congr' θ (by rw [← Category.assoc, spMap_comp_ring']) _ _ ?_ H
  simp only [Over.comp_left, Over.homMk_left]
  rw [spMap_comp_ring']

end GlobalTheory.UMin.ThInt

namespace GlobalTheory.UMin


open GlobalTheory.UMin.ThInt in
theorem thetaInt_hasDiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (o : Type) [CommRing o] (m n : ℕ) (f : Xo.XF c ⟶ PSpace o n), Odd m → 3 ≤ m → IsUnit (m : o) → n + 1 = m ^ (4 * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) → ThMap Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig m (pullback.fst _ _ : Xo.XF c ⟶ Xo.X) f → ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp (ratHull S.R) ⟶ Xo.XF c), UOver Xo c ρ.P (toRat S.R) u → ∀ (M : RatModel o' Ω) (g : M.Z ⟶ PSpace o n), Geo.Tor.IsNormalScheme M.Z → M.pt ≫ g = spMap (ratHull S.R).val.toRingHom ≫ u ≫ f → M.HasDiv S.th := by
  intro E _ _ _ H Dw l Xo c o _ m n f hm hm3 hmu hn hf o' Ω _ _ _ _ S ρ u hu M g hnorm hg
  haveI : CharZero Ω := ArithBase.char o'
  haveI : IsDedekindDomain o' := ArithBase.ded Ω
  haveI : IsAbelianScheme ρ.P.A := ρ.P.isAb
  haveI : IsCommMonObj ρ.P.A := IsAbelianScheme.comm
  set gd := Module.finrank ℚ E / 2 * (Dw.p + Dw.q) with hgd
  let vH : ratHull S.R →+* Ω := (ratHull S.R).val.toRingHom
  let v : S.R →+* Ω := S.R.val.toRingHom
  have hv : vH.comp (toRat S.R) = v := RingHom.ext fun _ => rfl
  let x₀ : Sp Ω ⟶ Sp S.R := spMap v ≫ 𝟙 (Sp S.R)
  let θ : SecAt ρ.P.A ρ.P.L x₀ := SecAt.pull ρ.P.A ρ.P.L (x := 𝟙 (Sp S.R)) ρ.th₁ v
  have hθ : IsGenSec ρ.P.A ρ.P.L _ θ := GlobalTheory.T.realisedThetaSystem_section_generates_field_fibres o' Ω S ρ Ω v
  obtain ⟨G, _, α, β, hα, hβ, hL⟩ := hu
  haveI : IsAbelianScheme G := PolPull.isAbelianScheme_of_isGrpPullback ρ.P.isAb hα
  haveI : IsCommMonObj G := IsAbelianScheme.comm
  have hLG : (ρ.P.L.pull α).IsLB := pull_isLB ρ.P.isLB α
  have hU := Xo.univ.t.PP.isLB
  have hUr := Xo.univ.t.PP.rigGen

  have hdim := GlobalTheory.UMin.polFib_univ E H Dw l Xo c Ω (spMap vH ≫ u ≫ pullback.fst _ _)
  have hmv1 := GlobalTheory.T.principallyPolarisedFibre_iff_of_grpPullback Xo.X (Sp (ratHull S.R)) Xo.univ.t.G Xo.univ.t.PP.L G (ρ.P.L.pull α) (u ≫ pullback.fst _ _) β
    hU hLG hβ hL gd Ω (spMap vH)
  have hmv2 := GlobalTheory.T.principallyPolarisedFibre_iff_of_grpPullback (Sp S.R) (Sp (ratHull S.R)) ρ.P.A ρ.P.L G (ρ.P.L.pull α) (spMap (toRat S.R)) α
    ρ.P.isLB hLG hα (PolBaseChange.lbIso_refl hLG) gd Ω (spMap vH)
  have hPG : PolFib G (ρ.P.L.pull α) gd (spMap vH) := hmv1.1.2 hdim
  have hPF : PolFib ρ.P.A ρ.P.L gd x₀ := by
    have h := hmv2.1.1 hPG
    rwa [spMap_comp_ring', hv, ← Category.comp_id (spMap v)] at h

  obtain ⟨e, he⟩ := GlobalTheory.T.exists_theta_symmetric_function_values_in_ground_field (Sp S.R) ρ.P.A ρ.P.L ρ.rig ρ.P.isLB ρ.rig_gen gd m (n + 1) Ω x₀ θ hm hn hPF

  obtain ⟨P', φG, hgP, hφG, hφGL⟩ := hPG
  have hPL : P'.L.IsLB := P'.isLB
  have hφGα : IsGrpPullback P'.A ρ.P.A x₀ (φG ≫ α) :=
    (hφG.comp hα).congr (by rw [spMap_comp_ring', hv]; exact (Category.comp_id _).symm) rfl
  have hφGβ : IsGrpPullback P'.A Xo.univ.t.G ((spMap vH ≫ u) ≫ pullback.fst _ _) (φG ≫ β) :=
    (hφG.comp hβ).congr (by rw [Category.assoc]) rfl
  have hLα : LBIso P'.L (ρ.P.L.pull (φG ≫ α)) :=
    LBIso.trans hPL (pull_isLB hLG φG) (pull_isLB ρ.P.isLB _) hφGL
      (GenSpread.lbIso_pull_of_lbIso (PolBaseChange.lbIso_refl hLG) φG rfl)
  have hLβ : LBIso P'.L (Xo.univ.t.PP.L.pull (φG ≫ β)) :=
    LBIso.trans hPL (pull_isLB ρ.P.isLB _) (pull_isLB hU _) hLα (GenSpread.lbIso_pull_comp φG rfl rfl hL)
  have hcrd := GlobalTheory.T.thetaMap_coords_of_symmetric_theta_isomorphic_fibre Xo.X Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig hU hUr gd m n o (Xo.XF c)
    (pullback.fst _ _) f (Sp S.R) ρ.P.A ρ.P.L ρ.rig Ω (spMap vH ≫ u) x₀ P' (φG ≫ β) (φG ≫ α) θ e hm hn hf
    ρ.P.isLB ρ.rig_gen hgP hφGβ hLβ hφGα hLα hθ he
  have hdiv : M.HasDiv e := by
    refine GlobalTheory.T.model_hasDiv_of_genericPoint_projectiveCoords o' Ω o M n g e ?_
    rw [hg, ← Category.assoc]
    exact hcrd

  haveI : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega)⟩
  have hkodd : Odd (S.r * S.N) := by
    obtain ⟨j, -, hj⟩ := ρ.r_eq
    rw [hj, ρ.N_eq]
    exact (ρ.n_odd.pow).mul ((ρ.n_odd.pow).pow)
  have hk3 : 3 ≤ S.r * S.N := by
    have h2 : 2 ≤ S.r * S.N := le_trans S.N_ge (Nat.le_mul_of_pos_left _ S.r_pos)
    obtain ⟨t, ht⟩ := hkodd
    omega
  refine GlobalTheory.T.hasDivisor_of_forall_complete_dvr_points o' Ω M S.Gam (Fin (n + 1)) S.th e (n + 1).factorial (Nat.factorial_pos _) hnorm hdiv ?_
  intro V _ _ _ hV ξ emb _ j₀ hj₀ hej
  haveI : IsDiscreteValuationRing V := hV.1
  let K := AlgebraicClosure (FractionRing V)
  let io : FractionRing V →+* K := algebraMap _ _
  let i : Ω →+* K := io.comp emb
  have hcast : ∀ t : ℕ, t ≠ 0 → (t : K) ≠ 0 := fun t ht => by
    rw [← map_natCast i t]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 ht)
  have hmV : IsUnit (m : V) := by
    simpa using hmu.map (Spec.preimage (ξ ≫ g ≫ PSpace.str o n)).hom
  have hkV : IsUnit ((S.r * S.N : ℕ) : V) := by
    simpa using S.unit.map (Spec.preimage (ξ ≫ M.s)).hom

  have hPK : PolFib ρ.P.A ρ.P.L gd (spMap i ≫ x₀) :=
    (GlobalTheory.T.principallyPolarisedFibre_iff_of_grpPullback (Sp S.R) (Sp S.R) ρ.P.A ρ.P.L ρ.P.A ρ.P.L (𝟙 _) (𝟙 _) ρ.P.isLB ρ.P.isLB (grpPullback_self' _)
      (ThetaAffineGlue.lbIso_pull_id ρ.P.isLB) gd Ω x₀).2 K i hPF
  have hθK := (GlobalTheory.T.principallyPolarisedFibre_exists_generator_stable (Sp S.R) ρ.P.A ρ.P.L ρ.P.isLB gd Ω x₀ hPF).2 θ hθ K i
  obtain ⟨pt, d, hd⟩ := GlobalTheory.T.exists_thetaConstantList_algClosed (Sp S.R) ρ.P.A ρ.P.L ρ.rig ρ.P.isLB ρ.rig_gen gd m (n + 1) K (spMap i ≫ x₀)
    (SecAt.pull ρ.P.A ρ.P.L θ i) hm (hcast m hm.pos.ne') hn hPK
  obtain ⟨pt', d', hd'⟩ := GlobalTheory.T.exists_thetaConstantList_algClosed (Sp S.R) ρ.P.A ρ.P.L ρ.rig ρ.P.isLB ρ.rig_gen gd (S.r * S.N)
    ((S.r * S.N) ^ (4 * gd)) K (spMap i ≫ x₀) (SecAt.pull ρ.P.A ρ.P.L θ i) hkodd (hcast _ (NeZero.ne _)) rfl hPK
  have hsym : ∀ j, io (emb (e j)) = symTup d j := he K i pt d hd
  obtain ⟨pt'', hd''⟩ := thList_pull_pull ρ.P.isLB (𝟙 (Sp S.R)) ρ.th₁ v i hd'
  have hT := GlobalTheory.T.thetaConstantList_realisedSystem_up_to_rootsOfUnity o' Ω S ρ K (i.comp v) _ pt'' d' hd''

  have h₁ : HasTh₂ ρ.P.A ρ.P.L ρ.rig m (S.r * S.N) (spMap i ≫ x₀) d d' := ⟨_, pt, pt', hθK, hd, hd'⟩
  obtain ⟨w, hw⟩ := PolBaseChange.lbIso_refl hLG
  obtain ⟨ρG, hρG, -⟩ := exists_rigidificationPullbackCompatibleIso hα hw ρ.P.isLB hLG ρ.rig_gen
  let xV : Sp K ⟶ Sp (ratHull S.R) := spMap io ≫ spMap emb ≫ spMap vH
  have hxV : spMap i ≫ x₀ = xV ≫ spMap (toRat S.R) := by
    simp only [xV, x₀, i, Category.comp_id, Category.assoc, spMap_comp_ring', ← hv, RingHom.comp_assoc]
  rw [hxV] at h₁
  have h₂ := (GlobalTheory.T.hasThetaConstantsTwoLevels_move_cartesian (Sp S.R) ρ.P.A ρ.P.L ρ.rig ρ.P.isLB ρ.rig_gen (Sp (ratHull S.R)) G (ρ.P.L.pull α) ρG
    (spMap (toRat S.R)) α hLG hρG hα (PolBaseChange.lbIso_refl hLG) m (S.r * S.N) (n + 1) _ K xV d d').2 h₁
  have h₃ := (GlobalTheory.T.hasThetaConstantsTwoLevels_move_cartesian Xo.X Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig hU hUr (Sp (ratHull S.R)) G (ρ.P.L.pull α) ρG
    (u ≫ pullback.fst _ _) β hLG hρG hβ hL m (S.r * S.N) (n + 1) _ K xV d d').1 h₂
  let y : Sp (FractionRing V) ⟶ Xo.XF c := spMap emb ≫ spMap vH ≫ u
  have h₄ : HasTh₂ Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig m (S.r * S.N) (spMap io ≫ y ≫ pullback.fst _ _) d d' := by
    have e₄ : spMap io ≫ y ≫ pullback.fst _ _ = xV ≫ u ≫ pullback.fst _ _ := by
      simp only [xV, y, Category.assoc]
    rw [e₄]
    exact h₃
  obtain ⟨a, ha, hPa, hPa'⟩ := GlobalTheory.T.thetaConstants_two_levels_same_scale_at_trait E H Dw l Xo c V hV y K io m (S.r * S.N) (n + 1) _ d d' hm hm3 hmV hkodd hk3
    hkV h₄
  have hP := GlobalTheory.T.primitive_families_thetaSymmetric_min_member_compare V K io (n + 1) _ ((S.r * S.N) ^ 2) S.Gam d d' a (fun j => emb (e j)) (fun b => emb (S.th b)) ha
    (Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ (NeZero.ne _))) hPa hPa' hsym hT.1 hT.2 j₀ ((map_ne_zero emb).2 hj₀)
    (fun j => by simpa [map_div₀] using hej j)
  refine ⟨fun b => by simpa [map_div₀, map_pow] using hP.1 b, ?_⟩
  obtain ⟨b, hb, hb'⟩ := hP.2
  exact ⟨b, fun h0 => hb (by simp [h0]), by simpa [map_div₀, map_pow] using hb'⟩

end GlobalTheory.UMin
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

theorem _root_.GlobalTheory.T.kawamataLogTerminal_add_generalMember_linearSystem : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ D : X → ℚ) (m : ℕ) (G A : CartierDiv X) (ι : Type) [Fintype ι] (s : ι → X.functionField), 0 < m → IsLogCanonicalMultiple p n Δ m G → IsQCart D → (∀ i, s i ∈ A.sections) → ∃ Q : MvPolynomial ι ℂ, Q ≠ 0 ∧ ∀ u : ι → ℂ, MvPolynomial.eval u Q ≠ 0 → ∀ t : X.functionFieldˣ, (t : X.functionField) = ∑ i, Cartier.constFn p (u i) * s i → ∀ y : X, (∃ i, A.GeneratesAt y (s i)) → ∀ a c : ℚ, 0 ≤ a → c < 1 → KltAt p n (Δ + a • D) y → KltAt p n (Δ + a • D + c • qWeil (GlobalTheory.Cartier.CartierDiv.principal t + A) 1) y := by
  first | exact @GlobalTheory.PairStep.kltAt_add_general_member | exact GlobalTheory.PairStep.kltAt_add_general_member | (intros; apply GlobalTheory.PairStep.kltAt_add_general_member <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.smallSections_lowerBound_ample_minus_twist : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ c : ℕ, GenAt P c → Regime P D → NefFib P.L → P.L.SemiPos D → ∀ a : ℝ, P.L.IsSelfInter a → ∀ ε : ℝ, 0 < ε → ∀ᶠ M : ℕ in atTop, (a / (D + 1).factorial - ε) * (M : ℝ) ^ (D + 1) ≤ P.lc M (-c) 1 := by
  first | exact @GlobalTheory.HSLowerTwist.main | exact GlobalTheory.HSLowerTwist.main | (intros; apply GlobalTheory.HSLowerTwist.main <;> assumption)
end
