module

import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle101
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle002
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle003
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConstantCoeffShiftS
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle013
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle084
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle021
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralWeierstrassChartXyUnitSeries
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle094
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle014
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle027
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle099
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle095
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle024
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle015
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle025
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UwEllipticFlow
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle100
public import Formalism.HermitianCurvature.Bundle009
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle001
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RightTypeAction
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle102
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DerivedActionDiscreteSeriesProperties
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle063
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle081
import Formalism.FormalDegreeBessel.FinalG
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle035
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq

@[expose] public section

section

noncomputable section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.EllBdd

variable {q : ℕ} [Fact q.Prime]

theorem bd_C (a : ℂ_[q]) : Bd ‖a‖ (C a : ℂ_[q]⟦X⟧) := by
  intro n
  rw [coeff_C]
  split_ifs <;> simp

theorem bd_mono {A B : ℝ} {f : ℂ_[q]⟦X⟧} (h : Bd A f) (hAB : A ≤ B) : Bd B f :=
  fun n => (h n).trans hAB

theorem bd_X_pow (k : ℕ) : Bd 1 (X ^ k : ℂ_[q]⟦X⟧) := by
  intro n
  rw [coeff_X_pow]
  split_ifs <;> simp

theorem bd_one_mul {f g : ℂ_[q]⟦X⟧} (hf : Bd 1 f) (hg : Bd 1 g) : Bd 1 (f * g) := by
  simpa using ((sup_norm_laws q).1 f g 1 1 hf hg).2

theorem bd_one_add {f g : ℂ_[q]⟦X⟧} (hf : Bd 1 f) (hg : Bd 1 g) : Bd 1 (f + g) := by
  simpa using ((sup_norm_laws q).1 f g 1 1 hf hg).1

theorem bd_one_pow {f : ℂ_[q]⟦X⟧} (hf : Bd 1 f) (k : ℕ) : Bd 1 (f ^ k) := by
  induction k with
  | zero => simpa using (bd_X_pow (q := q) 0)
  | succ k ih => rw [pow_succ]; exact bd_one_mul ih hf

theorem bd_one_sum {α : Type*} (s : Finset α) (f : α → ℂ_[q]⟦X⟧) (h : ∀ i ∈ s, Bd 1 (f i)) :
    Bd 1 (∑ i ∈ s, f i) :=
  Finset.sum_induction f (Bd 1) (fun _ _ => bd_one_add) (fun n => by simp) h

theorem bdd_mul {f g : ℂ_[q]⟦X⟧} (hf : Bdd f) (hg : Bdd g) : Bdd (f * g) := by
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  exact ⟨_, ((sup_norm_laws q).1 f g A B hA hB).2⟩

theorem bdd_add {f g : ℂ_[q]⟦X⟧} (hf : Bdd f) (hg : Bdd g) : Bdd (f + g) := by
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  exact ⟨_, ((sup_norm_laws q).1 f g A B hA hB).1⟩

theorem bdd_sum {α : Type*} (s : Finset α) (f : α → ℂ_[q]⟦X⟧) (h : ∀ i ∈ s, Bdd (f i)) :
    Bdd (∑ i ∈ s, f i) :=
  Finset.sum_induction f Bdd (fun _ _ => bdd_add) ⟨0, fun n => by simp⟩ h

theorem hat_one (ι : ℂ ≃+* ℂ_[q]) (ℓ : ℂ_[q]⟦X⟧) (hℓ : constantCoeff ℓ = 0) :
    hat ι ℓ (fun _ => 1) = 1 := by
  have h1 : tay (fun _ => 1) = 1 := by
    ext n
    rw [tay, coeff_mk, coeff_one, iteratedDeriv_const]
    split_ifs with h
    · simp [h]
    · simp
  have hs : HasSubst ℓ := HasSubst.of_constantCoeff_zero' hℓ
  rw [hat, h1, map_one, ← coe_substAlgHom hs, map_one]

theorem prod_coeff_le (ι : ℂ ≃+* ℂ_[q]) {m : ℕ} (a : Fin m → ℂ) (ha : ∀ i, ‖ι (a i)‖ ≤ 1) (n : ℕ) :
    ‖ι ((∏ i, (Polynomial.X - Polynomial.C (a i))).coeff n)‖ ≤ 1 := by
  apply GlobalTheory.MomOne.TransNorm.norm_coeff_prod <;> assumption

theorem bdd_hat_of_ell : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (ℓ : ℂ_[q]⟦X⟧) (φ : ℂ → ℂ), M.Chart ℓ → Ell M.L φ → AnalyticAt ℂ φ 0 → (∀ p, meromorphicOrderAt φ p < 0 → ¬ M.Small p) → Bdd (hat M.ι ℓ φ) := by
  intro q _ M ℓ φ hC hE hA hP
  obtain ⟨m, P, A, B, hPi, hz⟩ := GlobalTheory.EllipticModel.exists_mul_prod_eq_xy q M φ hC.1 hE
  obtain ⟨-, v, xs, ys, -, hxs, hys, -, hx0, -, -, -, -, hmain⟩ := GlobalTheory.MomOne.ChartXY.chart_xy q M ℓ hC
  set D : Polynomial ℂ := ∏ i, (Polynomial.X - Polynomial.C (M.x (P i))) with hD
  have hmon : D.Monic := Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _
  have hdeg : D.natDegree = m := by
    rw [hD, Polynomial.natDegree_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _]
    simp
  have hint : ∀ n, ‖M.ι (D.coeff n)‖ ≤ 1 := by
    refine prod_coeff_le M.ι (fun i => M.x (P i)) fun i => ?_
    by_contra h
    exact hP _ (hPi i).2 (Or.inr (not_le.mp h))
  have key := hmain φ A B (max A.natDegree B.natDegree) hA (le_max_left _ _) (le_max_right _ _)
    (fun _ => 1) analyticAt_const D m hdeg.le (by simpa using hz 0)
  set k := max A.natDegree B.natDegree
  set S := ∑ i ∈ Finset.range (m + 1), C (M.ι (D.coeff i)) * X ^ (2 * (m - i)) * xs ^ i with hS
  have hS1 : Bd 1 S := bd_one_sum _ _ fun i _ =>
    bd_one_mul (bd_one_mul (bd_mono (bd_C _) (hint i)) (bd_X_pow _)) (bd_one_pow hxs i)
  have hS0 : ‖constantCoeff S‖ = 1 := by

    rw [hS, Finset.sum_range_succ, map_add (f := _), map_sum, Finset.sum_eq_zero, zero_add]
    · have : D.coeff m = 1 := by rw [← hdeg]; exact hmon.coeff_natDegree
      simp [this, hx0]
    · intro i hi
      have : 2 * (m - i) ≠ 0 := by have := Finset.mem_range.mp hi; omega
      simp [this]
  have hR : Bdd (hat M.ι ℓ φ * X ^ (2 * k + 3) * S) := by
    rw [key, hat_one M.ι ℓ hC.2.1, one_mul]
    refine bdd_mul ⟨_, bd_X_pow _⟩ (bdd_sum _ _ fun i _ => bdd_add ?_ ?_)
    · exact bdd_mul (bdd_mul ⟨_, bd_C _⟩ ⟨_, bd_X_pow _⟩) ⟨_, bd_one_pow hxs i⟩
    · exact bdd_mul (bdd_mul (bdd_mul ⟨_, bd_C _⟩ ⟨_, bd_X_pow _⟩) ⟨_, bd_one_pow hxs i⟩) ⟨_, hys⟩
  obtain ⟨R, hR⟩ := hR
  refine ⟨R, (sup_norm_laws q).2.2.2.2.2 _ S (2 * k + 3) R hS1 hS0 ?_⟩
  rwa [show X ^ (2 * k + 3) * S * hat M.ι ℓ φ = hat M.ι ℓ φ * X ^ (2 * k + 3) * S by ring]

end GlobalTheory.MomOne.EllBdd
end
end

section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.chart_local_depth_le_of_valuedExtension_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (p : ℕ) [Fact p.Prime] (X : ValExt T p) (B : FB X.O (chD Ch.ch) (𝓞 E)), B.G.F = (fun i => MvPowerSeries.map X.ι (Ch.FT i)) → (∀ a, B.A.act a = fun i => MvPowerSeries.map X.ι (Ch.actT a i)) → ∀ (e k n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ), 0 < e → ∀ (P : MvPolynomial (LtN Dw n) X.O), MvPolynomial.map (algebraMap X.O X.C) P ∈ HHa Dw.mult n X.C ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ (f : PS X.O n (chD Ch.ch)) (A : ℝ), (X.v (p : X.C) : ℝ) ^ A ≤ (X.v (nabValN B X.C (letI := io.toAlgebra; MvPowerSeries.map X.ιF Ch.ch.h) H.w0 k (MvPowerSeries.map (algebraMap X.O X.C) f) (fun ℓ : LtN Dw n => ℓ.2.2) (fun (ℓ : LtN Dw n) i => algebraMap X.O X.C (X.ι (Ch.uvecT ⟨ℓ.1, ℓ.2.1⟩ i))) (MvPolynomial.map (algebraMap X.O X.C) P)) : ℝ) → nuLocC Ch e k a n ≤ (((vV T.V (p : T.Fr) : ℝ) / (e : ℝ) * A : ℝ) : EReal) := by
  first | exact @GlobalTheory.CharDepth.nuLocC_le_of_value_extension | exact GlobalTheory.CharDepth.nuLocC_le_of_value_extension | (intros; apply GlobalTheory.CharDepth.nuLocC_le_of_value_extension <;> assumption)
end

section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.exists_selfConjugatePlaceData_intChart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], (∀ x : 𝓞 E, star x = H.bar x) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y → ∀ (Orb : Type) [Fintype Orb] (lab : LabS E Orb), ArithS V io ι lab → ∃ p : ∀ o, SelfData Y 2 (lab.II Dw o), IsSelfOf C3 ι Y lab p ∧ SelfSep Y p ∧ (lab.RankOK Dw → ∀ o, (Y.rawSelf (p o)).RankHyp ∧ (Y.rawSelf (p o)).AltC) := by
  first | exact @GlobalTheory.RowAt.exists_selfData | exact GlobalTheory.RowAt.exists_selfData | (intros; apply GlobalTheory.RowAt.exists_selfData <;> assumption)
end

section

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.AtAdd

variable {q : ℕ} [Fact q.Prime]


open Classical in
theorem sub_mem_of_uw (M : Mdl q) (hM : M.Ok) (s t : ℂ) (ht : t ∉ M.L.lattice) (hy : M.y t ≠ 0)
    (hu : M.u s = M.u t) (hw : M.w s = M.w t) : s - t ∈ M.L.lattice := by
  have hwt : M.w t = -1 / M.y t := by simp [Mdl.w, ht]
  have hwt0 : M.w t ≠ 0 := by rw [hwt]; exact div_ne_zero (by norm_num) hy
  have hs : s ∉ M.L.lattice := by
    intro hs
    apply hwt0
    rw [← hw]; simp [Mdl.w, hs]
  have hws : M.w s = -1 / M.y s := by simp [Mdl.w, hs]
  have hys : M.y s ≠ 0 := by
    intro h
    apply hwt0
    rw [← hw, hws, h, div_zero]
  have hyy : M.y s = M.y t := by
    rw [hws, hwt, div_eq_div_iff hys hy] at hw
    linear_combination hw
  have hxx : M.x s = M.x t := by
    have h1 : M.u s = -M.x s / M.y s := by simp [Mdl.u, hs]
    have h2 : M.u t = -M.x t / M.y t := by simp [Mdl.u, ht]
    rw [h1, h2, hyy, div_left_inj' hy] at hu
    exact neg_injective hu
  obtain ⟨φ, -, hk, hφ⟩ := Mdl.exists_pointHom q M hM
  obtain ⟨h1, e1⟩ := hφ s hs
  obtain ⟨h2, e2⟩ := hφ t ht
  rw [← hk, map_sub, e1, e2, sub_eq_zero]
  congr 1 <;> simp [hxx, hyy]

theorem sub_mem_of_germ (M : Mdl q) (hM : M.Ok) (α s t : ℂ) (hα : α ≠ 0) (ht : M.Small t)
    (hu : ∀ᶠ z in 𝓝[≠] (0 : ℂ), M.u (α * z + s) = M.u (α * z + t))
    (hw : ∀ᶠ z in 𝓝[≠] (0 : ℂ), M.w (α * z + s) = M.w (α * z + t)) : s - t ∈ M.L.lattice := by
  have hg := ((uw_elliptic_flow q M hM).2.2.2.2.2.2.2.2 t ht).2.2.2.2.1
  have htend : Filter.Tendsto (fun z : ℂ => α * z + t) (𝓝[≠] 0) (𝓝[≠] t) := by
    apply tendsto_nhdsWithin_iff.2
    refine ⟨?_, ?_⟩
    · apply Filter.Tendsto.mono_left _ nhdsWithin_le_nhds
      have hc : Continuous (fun z : ℂ => α * z + t) := by fun_prop
      simpa using hc.tendsto 0
    · filter_upwards [self_mem_nhdsWithin] with z hz
      simpa [hα] using hz
  obtain ⟨z, h1, h2, h3⟩ := ((htend.eventually hg).and (hu.and hw)).exists
  have := sub_mem_of_uw M hM _ _ h1.1 h1.2.1 h2 h3
  simpa using this

theorem const_ell (ω : ℂ_[q]) : constantCoeff (C ω * logS : ℂ_[q]⟦X⟧) = 0 := by
  simp [logS, ← coeff_zero_eq_constantCoeff_apply]

theorem bd_w (M : Mdl q) (ℓ : ℂ_[q]⟦X⟧) (h : M.Chart ℓ) : Bd 1 (hat M.ι ℓ M.w) := by
  obtain ⟨-, v, xs, ys, -, -, hys, -, -, hc, -, hw, -⟩ := GlobalTheory.T.integral_weierstrass_chart_xy_unit_series q M ℓ h
  apply (sup_norm_laws q).2.2.2.2.2 _ ys 0 1 hys hc
  rw [pow_zero, one_mul, mul_comm, hw]
  intro n
  rw [map_neg, norm_neg, coeff_X_pow]
  split_ifs <;> simp

theorem germ_add (M : Mdl q) (ω : ℂ_[q]) (hM : M.MChart ω) (F : ℂ → ℂ) (hE : Ell M.L F)
    (hA : ∀ z, M.Small z → AnalyticAt ℂ F z) (hB : Bd 1 (hat M.ι (C ω * logS) F))
    (hT : ∀ ζ p, M.At ω ζ p →
      hat M.ι (C ω * logS) (fun z => F (z + p)) = shiftS ζ (hat M.ι (C ω * logS) F))
    (ζ ζ' : ℂ_[q]) (p p' t : ℂ) (h : M.At ω ζ p) (h' : M.At ω ζ' p') (ht : M.At ω (ζ * ζ') t) :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), F (1 * z + (p + p')) = F (1 * z + t) := by
  have han : ∀ s, M.Small s → AnalyticAt ℂ (fun z => F (z + s)) 0 := fun s hs =>
    AnalyticAt.comp_of_eq (g := F) (f := fun z => z + s) (hA s hs) (by fun_prop) (by simp)
  have hEp : Ell M.L (fun z => F (z + p)) := by
    refine ⟨fun x => ?_, fun l hl z => ?_⟩
    · exact (hE.1 (x + p)).comp_analyticAt (f := F) (g := fun z => z + p) (by fun_prop)
    · show F (z + l + p) = F (z + p)
      rw [add_right_comm, hE.2 l hl]
  have hBp : Bdd (hat M.ι (C ω * logS) (fun z => F (z + p))) := by
    rw [hT ζ p h]
    exact ⟨1, (Shift.shift_laws q ζ h.2.1).1 _ _ hB⟩
  obtain ⟨ψ, hψa, hψe, hψ⟩ := GlobalTheory.T.cpTransportedTaylorSeries_shift_eq_translate q M ω ζ' p' _ hM h' hEp (han p h.1) hBp
  rw [hT ζ p h, (GlobalTheory.T.cpSeriesMultiplicativeShift_comp_and_subst q).1 ζ' ζ _ h'.2.1 h.2.1 ⟨1, hB⟩, mul_comm ζ' ζ, ← hT _ t ht] at hψ
  have h1 := (GlobalTheory.T.integral_weierstrass_chart_xy_unit_series q M _ hM).1
  have he := ((TaylorRead.hat_laws q M.ι _ (const_ell ω)).1 _ _ hψa (han t ht.1)).2.2.2 h1 hψ
  filter_upwards [hψe, he.filter_mono nhdsWithin_le_nhds] with z e1 e2
  rw [one_mul, ← e2, e1]
  congr 1; ring

theorem germ_mul (M : Mdl q) (ω : ℂ_[q]) (hM : M.MChart ω) (F : ℂ → ℂ) (hE : Ell M.L F)
    (hA : ∀ z, M.Small z → AnalyticAt ℂ F z) (hB : Bd 1 (hat M.ι (C ω * logS) F))
    (hT : ∀ ζ p, M.At ω ζ p →
      hat M.ι (C ω * logS) (fun z => F (z + p)) = shiftS ζ (hat M.ι (C ω * logS) F))
    (α : ℂ) (a : ℤ_[q]) (n k : ℕ) (ζ : ℂ_[q]) (p t : ℂ)
    (hL : ∀ l ∈ M.L.lattice, α * l ∈ M.L.lattice) (hα : M.ι α = zc a)
    (hk : ‖a - (k : ℤ_[q])‖ ≤ (q : ℝ) ^ (-(n : ℤ))) (hζ : ζ ^ (q ^ n) = 1)
    (h : M.At ω ζ p) (ht : M.At ω (ζ ^ k) t) :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), F (α * z + α * p) = F (α * z + t) := by
  have han : ∀ s, M.Small s → AnalyticAt ℂ (fun z => F (z + s)) 0 := fun s hs =>
    AnalyticAt.comp_of_eq (g := F) (f := fun z => z + s) (hA s hs) (by fun_prop) (by simp)
  have hF0 : AnalyticAt ℂ F 0 := hA 0 (Or.inl (zero_mem _))
  have hmul : ∀ G : ℂ → ℂ, AnalyticAt ℂ G 0 → AnalyticAt ℂ (fun z => G (α * z)) 0 := fun G hG =>
    AnalyticAt.comp_of_eq (g := G) (f := fun z => α * z) hG (by fun_prop) (by simp)
  have hEα : Ell M.L (fun z => F (α * z)) := by
    refine ⟨fun x => ?_, fun l hl z => ?_⟩
    · exact (hE.1 (α * x)).comp_analyticAt (f := F) (g := fun z => α * z) (by fun_prop)
    · show F (α * (z + l)) = F (α * z)
      rw [mul_add, hE.2 _ (hL l hl)]
  have hsub := (GlobalTheory.T.cpTransportedTaylorSeries_multiplicativeChart q M.ι ω F hF0).2.2.1 α a hα
  have hm := (MulSeries.mulS_laws q).1 a
  have hBα : Bdd (hat M.ι (C ω * logS) (fun z => F (α * z))) := by
    rw [hsub]
    exact ⟨1, (sup_norm_laws q).2.1 _ _ _ hB hm.1 hm.2.1⟩
  obtain ⟨ψ, hψa, hψe, hψ⟩ := GlobalTheory.T.cpTransportedTaylorSeries_shift_eq_translate q M ω ζ p _ hM h hEα (hmul F hF0) hBα
  rw [hsub, ((GlobalTheory.T.cpSeriesMultiplicativeShift_comp_and_subst q).2 ζ n k a _ hζ hk ⟨1, hB⟩).2, ← hT _ t ht,
    ← (GlobalTheory.T.cpTransportedTaylorSeries_multiplicativeChart q M.ι ω _ (han t ht.1)).2.2.1 α a hα] at hψ
  have h1 := (GlobalTheory.T.integral_weierstrass_chart_xy_unit_series q M _ hM).1
  have he := ((TaylorRead.hat_laws q M.ι _ (const_ell ω)).1 _ _ hψa
    (hmul _ (han t ht.1))).2.2.2 h1 hψ
  filter_upwards [hψe, he.filter_mono nhdsWithin_le_nhds] with z e1 e2
  rw [← mul_add, ← e1, e2]

theorem norm_mul_sub_one_lt {ζ ξ : ℂ_[q]} (h : ‖ζ - 1‖ < 1) (h' : ‖ξ - 1‖ < 1) : ‖ζ * ξ - 1‖ < 1 := by
  have e : ζ * ξ - 1 = (ζ - 1) * (ξ - 1) + ((ζ - 1) + (ξ - 1)) := by ring
  rw [e]
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
  · rw [norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) h h'.le
  · exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h h')

theorem norm_pow_sub_one_lt {ζ : ℂ_[q]} (h : ‖ζ - 1‖ < 1) (k : ℕ) : ‖ζ ^ k - 1‖ < 1 := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ]; exact norm_mul_sub_one_lt ih h

theorem at_add_and_mul : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]), M.MChart ω → (∀ ζ ζ' p p', M.At ω ζ p → M.At ω ζ' p' → M.At ω (ζ * ζ') (p + p')) ∧ ∀ (α : ℂ) (a : ℤ_[q]) (n k : ℕ) (ζ : ℂ_[q]) (p : ℂ), (∀ l ∈ M.L.lattice, α * l ∈ M.L.lattice) → M.ι α = zc a → ‖a - (k : ℤ_[q])‖ ≤ (q : ℝ) ^ (-(n : ℤ)) → ζ ^ (q ^ n) = 1 → M.At ω ζ p → M.At ω (ζ ^ k) (α * p) := by
  intro q _ M ω hM
  have hOk : M.Ok := hM.1
  obtain ⟨hex, -, -, hiff, h10⟩ := GlobalTheory.T.smallPoint_multiplicativeCoordinate_existsUnique q M ω hM
  obtain ⟨hEu, hEw, -, -, -, -, -, -, hS⟩ := uw_elliptic_flow q M hOk
  have hBu : Bd 1 (hat M.ι (C ω * logS) M.u) := hM.2.2.1
  have hBw := bd_w M _ hM
  have hTu := fun ζ p h => (GlobalTheory.T.multiplicativeShift_eq_translate_by_small_point q M ω ζ p hM h).1
  have hTw := fun ζ p h => (GlobalTheory.T.multiplicativeShift_eq_translate_by_small_point q M ω ζ p hM h).2
  refine ⟨fun ζ ζ' p p' h h' => ?_, fun α a n k ζ p hL hα hk hζ h => ?_⟩
  · obtain ⟨t, ht⟩ := hex _ (norm_mul_sub_one_lt h.2.1 h'.2.1)
    have := sub_mem_of_germ M hOk 1 (p + p') t one_ne_zero ht.1
      (germ_add M ω hM M.u hEu (fun z hz => (hS z hz).1) hBu hTu ζ ζ' p p' t h h' ht)
      (germ_add M ω hM M.w hEw (fun z hz => (hS z hz).2.1) hBw hTw ζ ζ' p p' t h h' ht)
    refine (hiff _ t _ ht).2 ?_
    simpa using neg_mem this
  · by_cases h0 : α = 0
    · subst h0
      have ha : a = 0 := by
        have := (MulSeries.mulS_laws q).2.2.2.2.2 a
        rw [← hα, map_zero, norm_zero] at this
        exact norm_eq_zero.1 this.symm
      subst ha
      rw [zero_sub, norm_neg] at hk
      have hd : ((q : ℤ) ^ n) ∣ (k : ℤ) := by
        rw [← PadicInt.norm_int_le_pow_iff_dvd]
        simpa using hk
      have hd' : q ^ n ∣ k := by exact_mod_cast hd
      obtain ⟨m, rfl⟩ := hd'
      rw [pow_mul, hζ, one_pow, zero_mul]
      exact h10
    · obtain ⟨t, ht⟩ := hex _ (norm_pow_sub_one_lt h.2.1 k)
      have := sub_mem_of_germ M hOk α (α * p) t h0 ht.1
        (germ_mul M ω hM M.u hEu (fun z hz => (hS z hz).1) hBu hTu α a n k ζ p t hL hα hk hζ h ht)
        (germ_mul M ω hM M.w hEw (fun z hz => (hS z hz).2.1) hBw hTw α a n k ζ p t hL hα hk hζ h ht)
      refine (hiff _ t _ ht).2 ?_
      simpa using neg_mem this

end GlobalTheory.MomOne.AtAdd
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.cayley_endomorphisms_modular : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), 1 ≤ k → R.IsDS ε mu → ∀ (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)), PI.UpqRep.IsCayleyU k r ε Q → R.IsE Q E → IsMod ε E mu := by
  first | exact @GlobalTheory.isMod_smooth_of_isDS | exact GlobalTheory.isMod_smooth_of_isDS | (intros; apply GlobalTheory.isMod_smooth_of_isDS <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.adjoint_besselIntegral_eq_swap_of_gap : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∀ v ∈ R.TK, ∀ w ∈ R.TK, ContinuousLinearMap.adjoint (be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v) = be z Formalism.QuantumDeterminants.cStd π R.σ μW μN v w := by
  first | exact @GlobalTheory.BesselAdjoint.adjoint_be | exact GlobalTheory.BesselAdjoint.adjoint_be | (intros; apply GlobalTheory.BesselAdjoint.adjoint_be <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.quotientMeasure_integral_rmul_besselGroup : ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (F : Mx k r → ℂ), SideG k r z π u μW μN μG νq → ContinuousOn F (GG k r) → (∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, ∀ x ∈ GG k r, F (s * x) = F x) → Integrable (fun x : Formalism.QuantumDeterminants.Mt k r => F (Matrix.of x)) νq → ∀ g ∈ GG k r, ∫ x, F ((Matrix.of x) * g) ∂νq = ∫ x, F (Matrix.of x) ∂νq := by
  first | exact @GlobalTheory.quot_integral_rmul | exact GlobalTheory.quot_integral_rmul | (intros; apply GlobalTheory.quot_integral_rmul <;> assumption)
end

section

open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

theorem _root_.GlobalTheory.T.starProjection_splitCasimir_raising_last : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (β : ℂ) (L : Fin (n + 1) → ℤ) (l : Fin (n + 1)), Hyp E β L → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ a b y c, Et a b y c = E a b (y c) + if c = a then y b else 0) → (∀ y b, Om y b = ∑ c, E c b (y c)) → ∀ (M : Fin n → ℤ) (v : V), v ∈ CapSp (subA E) (shf β M) → (Module.End.eigenspace Om (β + L l + 0)).starProjection (PiLp.single 2 (Fin.last n) v) (Fin.last n) = (GlobalTheory.WigSh.wP L M l : ℂ) • v := by
  first | exact @GlobalTheory.starProjection_splitCasimirStd_last | exact GlobalTheory.starProjection_splitCasimirStd_last | (intros; apply GlobalTheory.starProjection_splitCasimirStd_last <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselIntertwine

theorem bessel_dsig (hK : PI.KFinSmooth) {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ}
    {R : Rep k r} (hR : R.IsDS ε mu) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {l : R.H → Wp} (hz : Formalism.QuantumDeterminants.inWb k r z)
    (hl : IsBes R z π l) {X : Mx k r} (hX : Formalism.FourierDecayAlt.P.QrD.InLieW k r z X) (hX' : PI.UpqRep.InLieHpk k r X)
    {v : R.H} (hv : v ∈ R.sm) :
    l (PI.UpqRep.dsig (k := k) (r := r) R.σ X v) = Formalism.FourierDecayAlt.Q.dRep π X (l v) := by
  have hd := (GlobalTheory.T.frechetContinuous_continuousOn_orbit_hasDerivAt hK k r ε mu R hR Wp l hl.1 hl.2.1 hl.2.2.2 v hv).2 X hX'
  have h1 : (1 : Mx k r) ∈ Formalism.QuantumDeterminants.Nset k r := by
    refine ⟨?_, ?_, ?_⟩
    · simp [Formalism.QuantumDeterminants.UH]
    · intro a i _
      simp [Matrix.one_apply]
    · intro i j _ _ _
      simp [Matrix.one_apply]
  have he : (fun t : ℝ => l (R.σ (NormedSpace.exp ((t : ℂ) • X)) v)) =
      fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X)) (l v) := by
    funext t
    have := hl.2.2.1 _ (Formalism.FourierDecayAlt.P.QrD.exp_uw hX t) 1 h1 v hv
    rw [Matrix.mul_one, Formalism.FourierDecayAlt.P.Qx8.psi_one hz, one_smul] at this
    exact this
  rw [he] at hd
  exact hd.deriv.symm

theorem bessel_intertwines_glW : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (l : R.H → Wp) (g : Mx k r), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → PI.UpqRep.IsFrameW k r z g → IsBes R z π l → ∀ i j : Fin k, ∀ v ∈ R.sm, l (R.dC (g * Matrix.single ((fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) i) ((fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) j) 1 * g⁻¹) v) = Formalism.FourierDecayAlt.Q.EcRep (Formalism.QuantumDeterminants.Hpk k r) π (g * Matrix.single ((fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) i) ((fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) j) 1 * g⁻¹) (l v) := by
  intro hK k r ε mu R hR Wp _ _ _ _ z π l g hz hT hg hl i j v hv
  obtain ⟨hF, hU⟩ := (GlobalTheory.T.frameW_conj_matrix_units k r z g hz hT hg).2.2.1
  rw [← hU i j]
  obtain ⟨h1, h2⟩ := Formalism.FourierDecayAlt.P.QrD.frame_lie hF i j
  set Y := Formalism.FourierDecayAlt.Q.unitB (Formalism.QuantumDeterminants.Hpk k r) _ i j with hY
  have hinv : (Formalism.QuantumDeterminants.Hpk k r)⁻¹ = Formalism.QuantumDeterminants.Hpk k r :=
    Matrix.inv_eq_left_inv (Formalism.QuantumDeterminants.hpkFacts k r).2.1
  have e1 : (1 / 2 : ℂ) • (Y + -(Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r)) =
      Formalism.QuantumDeterminants.hpart1 (Formalism.QuantumDeterminants.Hpk k r) Y := by
    rw [Formalism.QuantumDeterminants.hpart1, hinv, sub_eq_add_neg]
  have e2 : (1 / (2 * Complex.I)) • (Y - -(Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r)) =
      Formalism.QuantumDeterminants.hpart2 (Formalism.QuantumDeterminants.Hpk k r) Y := by
    rw [Formalism.QuantumDeterminants.hpart2, hinv, sub_neg_eq_add]
  have l1 : PI.UpqRep.InLieHpk k r (Formalism.QuantumDeterminants.hpart1 (Formalism.QuantumDeterminants.Hpk k r) Y) := h1.1.1
  have l2 : PI.UpqRep.InLieHpk k r (Formalism.QuantumDeterminants.hpart2 (Formalism.QuantumDeterminants.Hpk k r) Y) := h2.1.1
  have s1 := ((GlobalTheory.DerivedAction.derived_action hK k r ε mu R hR _ l1).1 v hv).1
  have s2 := ((GlobalTheory.DerivedAction.derived_action hK k r ε mu R hR _ l2).1 v hv).1
  rw [Rep.dC, e1, e2, hl.1 _ s1 _ (Formalism.FourierDecayAlt.P.DDSmoothness.smooth_smul _ s2), hl.2.1 _ _ s2,
    bessel_dsig hK hR hz hl h1 l1 hv, bessel_dsig hK hR hz hl h2 l2 hv]
  rfl

end GlobalTheory.BesselIntertwine
end
