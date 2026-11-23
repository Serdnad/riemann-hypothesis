module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle045
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle043
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle055
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Formalism.ConjugateSelfDual.Bundle001
import Formalism.LocalToGlobal.Columns.StdLatUnimodular
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle057
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
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
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle005
public import Mathlib.FieldTheory.Finite.Basic
import Formalism.LocalToGlobal.Divisibility.Tuples
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle003
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle005
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TateDualCrystalline
public import Formalism.LocalRingCardinality.DataParams₂

@[expose] public section

section

namespace GlobalTheory.RowLaws

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.WeilDeligne GlobalTheory.ThetaExh GlobalTheory.RowTie

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}

theorem tie_unit (T : WDTie N A) (w : PlE H) :
    (T.e w (A.lpUnr w {1})).unr ∧ (T.e w (A.lpUnr w {1})).lpDim = 1 ∧
      (T.e w (A.lpUnr w {1})).frobEig = {1} := by
  obtain ⟨h1, h2, h3⟩ := A.lpUnr_spec w {1} (by simp)
  refine ⟨(T.unr w _).1 h1, ?_, ?_⟩
  · rw [T.dim, h3]; rfl
  · rw [← T.frobEig w _ h1, h2]

theorem paramLaws_of_tie (T : WDTie N A) : ParamLaws N A := by
  intro w
  refine ⟨fun a b χ h => (T.e w).injective ?_, fun χ h => (T.e w).injective ?_,
    fun a χ s h => (T.e w).injective ?_, fun a b χ h hab => ?_, fun a b c h => (T.e w).injective ?_⟩
  · rw [T.char _ _ _ h, T.sum, T.sum, T.char _ _ _ h, T.char _ _ _ h]
    exact (GlobalTheory.T.lp_char_compatibilities _ _ _ _ _ _ _ _ 0).1
  · rw [T.char _ _ _ h, T.zero]
    exact (GlobalTheory.T.lp_char_compatibilities _ _ _ _ _
      (WD.lpZero (h := N.plOm.2 w)) (WD.lpZero (h := N.plOm.2 w)) _ 0).2.2.2.2.1
  · rw [T.char _ _ _ h, T.tw, T.tw, T.char _ _ _ h]
    exact (GlobalTheory.T.lp_char_compatibilities _ _ _ _ _ _ (WD.lpZero (h := N.plOm.2 w)) _ s).2.1
  · apply (T.e w).injective
    have hχ : (T.e w χ).lpDim = 1 := by rw [T.dim, h]
    have := congrArg (T.e w) hab
    rw [T.char _ _ _ h, T.char _ _ _ h] at this
    exact GlobalTheory.T.weilDeligneParameter_tensor_oneDim_injective _ _ _ _ _ _ _ _ hχ this
  · have := congrArg (T.e w) h
    rw [T.sum, T.sum] at this
    exact GlobalTheory.T.directSum_cancel_right _ _ _ _ _ _ _ _ this

theorem cancel_of_tie (T : WDTie N A) : Cancel N A := fun w a b c h => (paramLaws_of_tie T w).2.2.2.2 a b c h

theorem charLaws_of_tie (T : WDTie N A) : CharLaws N A := by
  intro w a b χ χ' s h1 h2
  have h3 : A.lpDim (A.lpTw χ s) = 1 := by rw [A.lpDim_tw, h1]
  have h4 : A.lpDim (A.lpChar χ χ') = 1 := by rw [A.lpDim_char _ _ h2, h1]
  have h5 : A.lpDim (A.lpUnr w {1}) = 1 := (A.lpUnr_spec w {1} (by simp)).2.2
  refine ⟨(T.e w).injective ?_, (T.e w).injective ?_, (T.e w).injective ?_, (T.e w).injective ?_,
    (T.e w).injective ?_⟩
  · rw [T.char _ _ _ h1, T.sum, T.sum, T.char _ _ _ h1, T.char _ _ _ h1]
    exact (GlobalTheory.T.lp_char_compatibilities _ _ _ _ _ _ _ _ 0).1
  · rw [T.char _ _ _ h1, T.tw, T.tw, T.char _ _ _ h1]
    exact (GlobalTheory.T.lp_char_compatibilities _ _ _ _ _ _ (WD.lpZero (h := N.plOm.2 w)) _ s).2.1
  · rw [T.char _ _ _ h3, T.tw, T.tw, T.char _ _ _ h1]
    exact (GlobalTheory.T.lp_char_compatibilities _ _ _ _ _ _ (WD.lpZero (h := N.plOm.2 w)) _ s).2.2.1
  · rw [T.char _ _ _ h2, T.char _ _ _ h1, T.char _ _ _ h4, T.char _ _ _ h2]
    exact (GlobalTheory.T.lp_char_compatibilities _ _ _ _ _ _ _ _ 0).2.2.2.1
  · rw [T.char _ _ _ h5]
    obtain ⟨u1, u2, u3⟩ := tie_unit T w
    exact (GlobalTheory.T.lp_char_compatibilities _ _ _ _ _
      (T.e w a) (WD.lpZero (h := N.plOm.2 w)) _ 0).2.2.2.2.2 u1 u2 u3

end GlobalTheory.RowLaws


open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain in
theorem GlobalTheory.RowLaws.main : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N),
    GlobalTheory.RowTie.WDTie N A → GlobalTheory.ThetaExh.ParamLaws N A ∧ GlobalTheory.RowTie.CharLaws N A ∧ GlobalTheory.RowTie.Cancel N A :=
  fun _ _ _ _ _ T => ⟨GlobalTheory.RowLaws.paramLaws_of_tie T, GlobalTheory.RowLaws.charLaws_of_tie T, GlobalTheory.RowLaws.cancel_of_tie T⟩
end

section

open Filter Topology

namespace GlobalTheory.PSerLin

theorem map_subst_linear {σ κ R S : Type*} [Finite σ] [Fintype κ] [CommRing R] [CommRing S]
    (h : R →+* S) (c : σ → κ → R) (F : MvPowerSeries σ R) :
    MvPowerSeries.map h (MvPowerSeries.subst
      (fun k => ∑ x, MvPowerSeries.C (c k x) * (MvPowerSeries.X x : MvPowerSeries κ R)) F) =
    MvPowerSeries.subst
      (fun k => ∑ x, MvPowerSeries.C (h (c k x)) * (MvPowerSeries.X x : MvPowerSeries κ S))
      (MvPowerSeries.map h F) := by
  rw [MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero fun k => by simp)]
  simp

open Formalism.MainNotions.G Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric NumberField


open Classical in
theorem taylorDir_linear (D : D7) {N N' : ℕ} (G : VC D N N' → ℂ)
    (c : D.what₂.Tau × Fin N' × Fin N → D.what₂.Tau × Fin N' × Fin N → ℂ)
    (hG : Differentiable ℂ G) :
    taylorDir (Formalism.MainNotions.TaylorLogMetric.coordV D) (fun z : VC D N N' => G (fun τ i j =>
      ∑ x : D.what₂.Tau × Fin N' × Fin N, c (τ, i, j) x * z x.1 x.2.1 x.2.2)) =
    MvPowerSeries.subst (fun k => ∑ x, MvPowerSeries.C (c k x) *
      (MvPowerSeries.X x : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ))
      (taylorDir (Formalism.MainNotions.TaylorLogMetric.coordV D) G) := by
  let L : (D.what₂.Tau × Fin N' × Fin N → ℂ) →L[ℂ] VC D N N' :=
    ContinuousLinearMap.pi fun τ => ContinuousLinearMap.pi fun a => ContinuousLinearMap.pi fun b =>
      ContinuousLinearMap.proj (τ, a, b)
  have hL : ∀ z τ a b, L z τ a b = z (τ, a, b) := fun _ _ _ _ => rfl
  have hc : Formalism.MainNotions.TaylorLogMetric.coordV D = fun k => L (Pi.single k 1) := by
    funext ⟨k1, k2, k3⟩ τ a b
    simp [hL, Formalism.MainNotions.TaylorLogMetric.coordV, Pi.single_apply]
  have han : AnalyticAt ℂ G 0 :=
    SCV.analyticAt_iff_eventually_differentiableAt.2 (Eventually.of_forall hG)
  have han' : AnalyticAt ℂ (fun z => G (L z)) 0 :=
    han.comp_of_eq (L.analyticAt 0) (map_zero L)
  let ev : (D.what₂.Tau × Fin N' × Fin N) → (VC D N N' →L[ℂ] ℂ) := fun x =>
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) x.2.2).comp
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N' => Fin N → ℂ) x.2.1).comp
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : D.what₂.Tau => Fin N' → Fin N → ℂ) x.1))
  let ℓ : (D.what₂.Tau × Fin N' × Fin N) → (VC D N N' →L[ℂ] ℂ) := fun k => ∑ x, c k x • ev x
  have hℓ : ∀ k z, ℓ k z = ∑ x, c k x * z x.1 x.2.1 x.2.2 := fun k z => by
    simp [ℓ, ev]
  have h := taylorDir_comp (Formalism.MainNotions.TaylorLogMetric.coordV D) (φ := fun z k => ℓ k z)
    (analyticAt_pi_iff.2 fun k => (ℓ k).analyticAt 0) (funext fun k => map_zero (ℓ k)) han'
  rw [taylor_comp_clm L han, ← hc] at h
  convert h using 2
  · funext z
    refine congrArg G ?_
    funext τ i j
    exact (hℓ (τ, i, j) z).symm
  · funext k
    rw [show (fun z => ℓ k z) = ⇑(ℓ k) from rfl, taylorDir_clm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [MvPowerSeries.smul_eq_C_mul, hℓ, hc]
    simp [hL, Pi.single_apply]

end GlobalTheory.PSerLin
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechDR GlobalTheory.PD

set_option autoImplicit false
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.EtProj.RatLin

open GlobalTheory.ProjSpace GlobalTheory.ProjFrac MvPolynomial

theorem frac_smul {N : ℕ} (V : (PSpace ℂ N).Opens) (f g : MvPolynomial (Fin (N + 1)) ℂ)
    (hf : f ∈ grading ℂ N 1) (hg : g ∈ grading ℂ N 1) (hV : V ≤ Proj.basicOpen (grading ℂ N) g) (c : ℂ)
    (hcf : c • f ∈ grading ℂ N 1) :
    frac (grading ℂ N) V (c • f) g hcf hg hV =
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ (PSpace.str ℂ N).appLE ⊤ V le_top).hom c *
        frac (grading ℂ N) V f g hf hg hV := by
  rw [← algebraMap_sections_eq]
  refine ext fun x hx => ?_
  obtain ⟨i, hi⟩ := exists_mem_chart ℂ N x
  have hW : V ⊓ chart ℂ N i ≤ V := inf_le_left
  have hxW : x ∈ V ⊓ chart ℂ N i := ⟨hx, hi⟩
  rw [← ev_resG hW x hxW, ← ev_resG hW x hxW, map_mul, resG_algebraMap, resG_frac, resG_frac,
    ← formOn_C (hi := (inf_le_right : V ⊓ chart ℂ N i ≤ chart ℂ N i)), formOn]
  congr 1
  refine (frac_mul_eq ?_).symm
  rw [smul_eq_C_mul]
  ring

theorem app_const {X : Scheme.{0}} (p : X ⟶ Sp ℂ) {N : ℕ} (ι : X ⟶ PSpace ℂ N) (hι : ι ≫ PSpace.str ℂ N = p)
    (V : (PSpace ℂ N).Opens) (c : ℂ) :
    (ι.app V).hom (((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ (PSpace.str ℂ N).appLE ⊤ V le_top).hom c) =
      algebraMap ℂ (Sec p (ι ⁻¹ᵁ V)) c := by
  subst hι
  change _ = ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ (ι ≫ PSpace.str ℂ N).appLE ⊤ (ι ⁻¹ᵁ V) _).hom c
  rw [Scheme.Hom.app_eq_appLE, ← Scheme.Hom.appLE_comp_appLE]
  rfl

theorem fRatio_add {X : Scheme.{0}} {N : ℕ} (ι : X ⟶ PSpace ℂ N) (f₁ f₂ g : MvPolynomial (Fin (N + 1)) ℂ)
    (h₁ : f₁ ∈ grading ℂ N 1) (h₂ : f₂ ∈ grading ℂ N 1) (h : f₁ + f₂ ∈ grading ℂ N 1)
    (hg : g ∈ grading ℂ N 1) :
    fRatio ι (f₁ + f₂) g h hg = fRatio ι f₁ g h₁ hg + fRatio ι f₂ g h₂ hg := by
  unfold fRatio
  rw [frac_add (ha := h₁) (ha₂ := h₂)]
  exact map_add _ _ _

theorem fRatio_zero {X : Scheme.{0}} {N : ℕ} (ι : X ⟶ PSpace ℂ N) (g : MvPolynomial (Fin (N + 1)) ℂ)
    (h : (0 : MvPolynomial (Fin (N + 1)) ℂ) ∈ grading ℂ N 1) (hg : g ∈ grading ℂ N 1) :
    fRatio ι 0 g h hg = 0 := by
  unfold fRatio
  rw [frac_zero]
  exact map_zero _

theorem fRatio_smul {X : Scheme.{0}} (p : X ⟶ Sp ℂ) {N : ℕ} (ι : X ⟶ PSpace ℂ N)
    (hι : ι ≫ PSpace.str ℂ N = p) (f g : MvPolynomial (Fin (N + 1)) ℂ) (c : ℂ)
    (hf : f ∈ grading ℂ N 1) (h : c • f ∈ grading ℂ N 1) (hg : g ∈ grading ℂ N 1) :
    (show Sec p (fOpen ι g) from fRatio ι (c • f) g h hg) = c • (show Sec p (fOpen ι g) from fRatio ι f g hf hg) := by
  have e := app_const p ι hι (Proj.basicOpen (grading ℂ N) g) c
  refine Eq.trans ?_ (Algebra.smul_def (A := Sec p (fOpen ι g)) c _).symm
  refine Eq.trans ?_ (congrArg (· * (show Sec p (fOpen ι g) from fRatio ι f g hf hg)) e)
  unfold fRatio
  rw [frac_smul _ f g hf hg le_rfl c h]
  exact map_mul _ _ _

end GlobalTheory.EtProj.RatLin


open GlobalTheory.EtProj.RatLin in
theorem GlobalTheory.EtProj.fRatio_linear : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) (N : ℕ) (ι : X ⟶ PSpace ℂ N), ι ≫ PSpace.str ℂ N = p → ∀ (g : MvPolynomial (Fin (N + 1)) ℂ) (hg : g ∈ GlobalTheory.ProjSpace.grading ℂ N 1) (c : Fin (N + 1) → ℂ) (hf : (∑ l, c l • MvPolynomial.X l : MvPolynomial (Fin (N + 1)) ℂ) ∈ GlobalTheory.ProjSpace.grading ℂ N 1), let U := GlobalTheory.EtProj.fOpen ι g; let q : Sec p U := GlobalTheory.EtProj.fRatio ι (∑ l, c l • MvPolynomial.X l) g hf hg; let r : Fin (N + 1) → Sec p U := fun l => GlobalTheory.EtProj.fRatio ι (MvPolynomial.X l) g (GlobalTheory.ProjSpace.X_mem ℂ N l) hg; q = ∑ l, c l • r l := by
  intro X p N ι hι g hg c hf U q r
  have key : ∀ (s : Finset (Fin (N + 1)))
      (h : (∑ l ∈ s, c l • MvPolynomial.X l : MvPolynomial (Fin (N + 1)) ℂ) ∈ GlobalTheory.ProjSpace.grading ℂ N 1),
      (show Sec p U from GlobalTheory.EtProj.fRatio ι (∑ l ∈ s, c l • MvPolynomial.X l) g h hg) = ∑ l ∈ s, c l • r l := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro h
      simp only [Finset.sum_empty]
      exact fRatio_zero ι g _ hg
    | insert a s ha ih =>
      intro h
      have hs : (∑ l ∈ s, c l • MvPolynomial.X l : MvPolynomial (Fin (N + 1)) ℂ) ∈ GlobalTheory.ProjSpace.grading ℂ N 1 :=
        Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (GlobalTheory.ProjSpace.X_mem ℂ N l)
      have ha' : (c a • MvPolynomial.X a : MvPolynomial (Fin (N + 1)) ℂ) ∈ GlobalTheory.ProjSpace.grading ℂ N 1 :=
        Submodule.smul_mem _ _ (GlobalTheory.ProjSpace.X_mem ℂ N a)
      simp only [Finset.sum_insert ha]
      rw [fRatio_add ι _ _ g ha' hs _ hg, ← ih hs]
      congr 1
      exact fRatio_smul p ι hι _ g (c a) (GlobalTheory.ProjSpace.X_mem ℂ N a) ha' hg
  exact key Finset.univ hf
end
end

section

namespace GlobalTheory.NormDivisibility

open NumberField IsDedekindDomain

theorem natCast_eq_zero_of_dvd_card {R : Type*} [CommRing R] [IsDomain R] [Finite R] {l : ℕ}
    (hl : l.Prime) (h : l ∣ Nat.card R) : (l : R) = 0 := by
  classical
  have := Fintype.ofFinite R
  let _ : Field R := Fintype.fieldOfDomain R

  obtain ⟨n, hp, hc⟩ := FiniteField.card R (ringChar R)
  rw [Nat.card_eq_fintype_card, hc] at h
  rw [(Nat.prime_dvd_prime_iff_eq hl hp).mp (hl.dvd_of_dvd_pow h)]
  exact ringChar.Nat.cast_ringChar

theorem not_dvd_norm_of_not_mem {E : Type} [Field E] [NumberField E] {l : ℕ} (hl : Nat.Prime l)
    (w : HeightOneSpectrum (RingOfIntegers E))
    (hw : (l : RingOfIntegers E) ∉ w.asIdeal) : ¬ l ∣ Formalism.ConjugateSelfDual.normV w := by
  intro h
  have : Finite (RingOfIntegers E ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  unfold Formalism.ConjugateSelfDual.normV at h
  have h0 := natCast_eq_zero_of_dvd_card (R := RingOfIntegers E ⧸ w.asIdeal) hl h
  apply hw
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact h0

end GlobalTheory.NormDivisibility
end

section

open NumberField IsDedekindDomain
open _root_.Formalism.BasicNotions _root_.Formalism.L2.Host _root_.Formalism.FrobeniusOrbits
open _root_.Formalism.L2.DIV

namespace GlobalTheory.Formalism.L2.Col

namespace HostOk

variable {R : Ranks} {H : _root_.Formalism.BasicNotions.Host R} (T : Frame H)

theorem sigma_conj (σ : H.E ≃ₐ[ℚ] H.E) (x : H.E) : σ (H.conj x) = H.conj (σ x) := by
  apply H.φ₀.injective
  have h1 := H.conjE_apply (H.φ₀.comp (σ : H.E →+* H.E)) x
  have h2 := H.conjE_apply H.φ₀ (σ x)
  exact h1.trans h2.symm

theorem galE_sigmaOf (g : R.GG) : H.galE (H.sigmaOf g) = g :=
  (H.gal).apply_symm_apply g

theorem sigmaOf_b (g : R.Psi) : H.sigmaOf g H.sqrtMinusD = H.sqrtMinusD :=
  (H.galE_mem_Psi_iff _).1 (by rw [galE_sigmaOf]; exact g.2)

theorem d_pos (H : _root_.Formalism.BasicNotions.Host R) : 0 < H.d := H.hyp.2.1.pos

theorem b_sq (H : _root_.Formalism.BasicNotions.Host R) : H.sqrtMinusD ^ 2 = -(H.d : H.E) := by
  exact H.sqd_sq

theorem conj_b (H : _root_.Formalism.BasicNotions.Host R) : H.conj H.sqrtMinusD = -H.sqrtMinusD := by
  apply H.φ₀.injective
  have h2 := H.conjE_apply H.φ₀ H.sqrtMinusD
  refine h2.trans ?_
  have h3 : H.φ₀ H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ) := H.φ₀_mem
  rw [map_neg, h3]
  simp

theorem b_ne (H : _root_.Formalism.BasicNotions.Host R) : H.sqrtMinusD ≠ -H.sqrtMinusD := by
  intro h
  have h0 : H.sqrtMinusD = 0 := by
    have : (2 : H.E) * H.sqrtMinusD = 0 := by linear_combination h
    exact (mul_eq_zero.1 this).resolve_left two_ne_zero
  have h1 := b_sq H
  rw [h0] at h1
  have h2 : (H.d : H.E) = 0 := by linear_combination h1
  have h3 : H.d = 0 := by exact_mod_cast h2
  exact (d_pos H).ne' h3

variable (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL] (hE : H.EQ ≤ LL)

end HostOk

end GlobalTheory.Formalism.L2.Col
end

section

noncomputable section

namespace GlobalTheory.WordJumpsCompare

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HTW

section Clauses

variable (D : D7)

variable (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))

end Clauses

section Constituent

variable (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
  (hw : w ∈ placesOver D.host.E (D.nd.l i))

theorem continuous_toLL : Continuous (D.nbr i w hw).toLL :=
  continuous_subtype_val.comp (D.nbr i w hw).eO_cont

theorem continuous_toGlobal :
    Continuous fun g : Br.G D.nbr i w hw => decS D.nd w (Br.iota D.nbr i w hw g) :=
  continuous_subtype_val.comp (Br.iota_cont D.nbr i w hw)

theorem loc_apply {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i w hw)
    (a b : Fin k) : Br.loc D.nbr i w hw M g a b =
      (D.nbr i w hw).toLL (M (decS D.nd w (Br.iota D.nbr i w hw g)) a b) := rfl

theorem continuous_loc {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hM : Continuous M) :
    Continuous (Br.loc D.nbr i w hw M) := by
  refine continuous_matrix fun a b => ?_
  simp only [loc_apply]
  exact (continuous_toLL D i w hw).comp
    ((hM.comp (continuous_toGlobal D i w hw)).matrix_elem a b)

theorem toLLK_toK (c : D.nd.O i) :
    Br.toLLK (D.nbr i w hw) (toK D.nd i c) = (D.nbr i w hw).toLL c :=
  Br.toLLK_alg (D.nbr i w hw) c

variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))

end Constituent

section At

variable (D : D7) (L : SizeData₂ D) (ε : ℤˣ) (i : D.nd.Loc)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

end At

end GlobalTheory.WordJumpsCompare
end
end

section

open NumberField IsDedekindDomain Formalism.L2.Col

theorem _root_.GlobalTheory.T.exists_typePrime_under_eq : ∀ (X : Fields) (Pr : Primes X), X.Ok → Pr.Ok → ∀ (i : Fin 2) (P : HeightOneSpectrum (𝓞 X.E)), ((Pr.g i : ℕ) : 𝓞 X.E) ∈ P.asIdeal → ∃ P' ∈ Pr.vG i, P'.under (𝓞 X.F) = P.under (𝓞 X.F) := by
  first | exact @GlobalTheory.GprimUnder.exists_vG_under | exact GlobalTheory.GprimUnder.exists_vG_under | (intros; apply GlobalTheory.GprimUnder.exists_vG_under <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.AmbientDual

theorem twist_locC (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (x : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) :
    twistM (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x)) (TruncatedSeriesCountingIdentities.chi1C C)⁻¹ = TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x) := by
  refine MonoidHom.ext fun g => ?_
  refine Matrix.ext fun a b => ?_
  let ψ : D.nd.O i →+* ↥C.LL.1 := C.inc.comp (D.nbr i w hw).toLL
  let j : Br.G D.nbr i w hw →* GE D.nd := (decS D.nd w).comp (Br.iota D.nbr i w hw)
  have hχ : TruncatedSeriesCountingIdentities.chi1C C g = Units.map (ψ : D.nd.O i →* ↥C.LL.1) (chiU D.nd i 1 (j g)) :=
    Units.ext rfl
  show (((TruncatedSeriesCountingIdentities.chi1C C)⁻¹ g : (↥C.LL.1)ˣ) : ↥C.LL.1) * ψ (rO D.nd i r x (j g) a b) =
    ψ ((((chiU D.nd i 1)⁻¹ (j g) : (D.nd.O i)ˣ) : D.nd.O i) * rO D.nd i r x (j g) a b)
  rw [MonoidHom.inv_apply, hχ, map_mul, MonoidHom.inv_apply, ← map_inv]
  rfl

end GlobalTheory.AmbientDual
end
