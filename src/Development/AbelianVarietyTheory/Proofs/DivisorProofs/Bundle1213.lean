module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.Hermitian
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
import Mathlib.Tactic.Basify
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
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.Bundle001
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.DifferentiableAtChart
public import ReciprocityTheory.AnalyticForms.MaIntEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle002
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle010
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.CmpbHessAtAddConst
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

@[expose] public section

section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

section
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open scoped ComplexOrder ComplexConjugate

theorem cHess_posSemidef_of_levi {n : ℕ} {f : ReciprocityTheory.L2DbarEstimates.V n → ℝ} {x : ReciprocityTheory.L2DbarEstimates.V n} (hf : ContDiffAt ℝ 2 f x)
    (hL : ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun v => ((f v : ℝ) : ℂ)) x ξ).re) :
    (cHess n (fun v => ((f v : ℝ) : ℂ)) x).PosSemidef := by
  classical
  set g : ReciprocityTheory.L2DbarEstimates.V n → ℂ := fun v => ((f v : ℝ) : ℂ) with hg
  have hg2 : ContDiffAt ℝ 2 g x := Complex.ofRealCLM.contDiff.contDiffAt.comp x hf
  have hgc : (fun w => conj (g w)) = g := funext fun w => by simp [g]
  have hH : (cHess n g x).IsHermitian := by
    ext j k
    simp only [Matrix.conjTranspose_apply, cHess, Matrix.of_apply]
    show conj (wd n k (wdb n j g) x) = wd n j (wdb n k g) x
    have h1 : (fun w => conj (wdb n j g w)) = wd n j g := by
      funext w
      rw [← ChartWirtingerDerivatives.wd_conj' n j g w, hgc]
    rw [← ChartWirtingerDerivatives.wdb_conj' n k (wdb n j g) x, h1, comm_wd_wdb g x hg2 j k]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH fun y => ?_
  have hre : dotProduct (star y) (Matrix.mulVec (cHess n g x) y) = leviV n g x (fun k => conj (y k)) := by
    simp only [dotProduct, Matrix.mulVec, leviV, cHess, Matrix.of_apply, Finset.mul_sum,
      Pi.star_apply, Complex.conj_conj]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [Complex.star_def]
    ring
  have him := hH.im_star_dotProduct_mulVec_self y
  refine Complex.le_def.2 ⟨?_, ?_⟩
  · rw [hre]; exact hL _
  · simpa using him.symm

theorem re_sum_perm_det_nonneg {D : ℕ} (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (hA : ∀ i, (A i).PosSemidef) :
    0 ≤ (∑ τ : Equiv.Perm (Fin D), (Matrix.of fun j l => A (τ l) j l).det).re := by
  have h := (ReciprocityTheory.AnForm.A.mdisc_nonneg_of_posSemidef A hA).2
  have h0 : (D.factorial : ℂ) ≠ 0 := by exact_mod_cast D.factorial_ne_zero
  have e : (∑ τ : Equiv.Perm (Fin D), (Matrix.of fun j l => A (τ l) j l).det) =
      ((D.factorial : ℝ) : ℂ) * ReciprocityTheory.AnForm.mdisc A := by
    rw [ReciprocityTheory.AnForm.A.mdisc_eq_sum_perm, Complex.ofReal_natCast, ← mul_assoc, mul_one_div_cancel h0, one_mul]
  rw [e, Complex.re_ofReal_mul]
  exact mul_nonneg (Nat.cast_nonneg _) h

end

theorem dens_nonneg_of_semiPosReg {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
    {L : Fin D → MLine p σ} (h : ∀ i, (L i).φ.SemiPosReg D) (c : AlgChart p σ D) {y : CxPts p σ}
    (hy : y ∈ c.e.source) : 0 ≤ dens L c y :=
  mul_nonneg (by positivity) (re_sum_perm_det_nonneg (fun i => c.hess (L i).φ (pick (L i).φ.isLB y) y) fun i =>
    cHess_posSemidef_of_levi ((L i).cInf.contDiffAt c hy (mem_pick _ y)) (h i _ c y ⟨hy, mem_pick _ y⟩))

theorem part_neg_eq_zero_of_semiPosReg : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) [SecondCountableTopology (CxPts p σ)] (D : ℕ) (L : Fin D → MLine p σ), (∀ i, (L i).φ.SemiPosReg D) → part L (-1) = 0 := by
  intro k _ X p σ _ D L h
  refine le_antisymm (iSup_le fun c => le_of_eq (Measure.measure_univ_eq_zero.1 ?_)) bot_le
  rw [chartMeas_apply _ _ MeasurableSet.univ, inter_univ, c.e.image_source_eq_target]
  refine setLIntegral_eq_zero c.e.open_target.measurableSet fun v hv => ?_
  have := dens_nonneg_of_semiPosReg h c (c.e.map_target hv)
  exact ENNReal.ofReal_eq_zero.2 (by simpa using this)

end GlobalTheory.Mix
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VolBr

theorem le_arVol_of_frequently_le : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (L : HermLB p) (a : ℝ), (∀ ε : ℝ, 0 < ε → ∃ᶠ N : ℕ in atTop, (L.pow N).smallSec.Finite ∧ (a / (D + 1).factorial - ε) * (N : ℝ) ^ (D + 1) ≤ Real.log ((L.pow N).smallSec.ncard : ℝ)) → (a : EReal) ≤ arVol L D := by
  intro k _ X _ p D L a h
  have hc : (0 : ℝ) < ((D + 1).factorial : ℝ) := by positivity
  have key : ∀ δ : ℝ, 0 < δ → ((a - δ : ℝ) : EReal) ≤ arVol L D := by
    intro δ hδ
    refine Filter.le_limsup_of_frequently_le ?_
    have hε : 0 < δ / ((D + 1).factorial : ℝ) := div_pos hδ hc
    refine ((h _ hε).and_eventually (eventually_gt_atTop 0)).mono ?_
    rintro N ⟨⟨hfin, hle⟩, hN⟩
    have h0 : 0 < (L.pow N).smallSec.ncard := (Set.ncard_pos hfin).2 ⟨_, (L.pow N).zero_mem_smallSec⟩
    rw [← hfin.cast_ncard_eq, ENat.toENNReal_coe, ← ENNReal.ofReal_natCast,
      ENNReal.log_ofReal_of_pos (by exact_mod_cast h0), ← EReal.coe_mul, EReal.coe_le_coe_iff]
    have hNp : (0 : ℝ) < (N : ℝ) ^ (D + 1) := by positivity
    rw [mul_div_assoc', le_div_iff₀ hNp]
    have e : (a / ((D + 1).factorial : ℝ) - δ / ((D + 1).factorial : ℝ)) * ((D + 1).factorial : ℝ) = a - δ := by
      field_simp
    calc (a - δ) * (N : ℝ) ^ (D + 1)
        = ((a / ((D + 1).factorial : ℝ) - δ / ((D + 1).factorial : ℝ)) * (N : ℝ) ^ (D + 1)) * ((D + 1).factorial : ℝ) := by
          rw [← e]; ring
      _ ≤ Real.log ((L.pow N).smallSec.ncard : ℝ) * ((D + 1).factorial : ℝ) :=
          mul_le_mul_of_nonneg_right hle hc.le
  refine le_of_forall_lt_imp_le_of_dense fun z hz => ?_
  induction z using EReal.rec with
  | bot => exact bot_le
  | top => exact absurd hz (not_lt.2 le_top)
  | coe r =>
    have hr : r < a := EReal.coe_lt_coe_iff.1 hz
    have := key (a - r) (by linarith)
    rwa [sub_sub_cancel] at this

end GlobalTheory.VolBr
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

theorem det_perm_update_add {D : ℕ} (F : Fin D → Matrix (Fin D) (Fin D) ℂ) (i : Fin D)
    (P Q : Matrix (Fin D) (Fin D) ℂ) (τ : Equiv.Perm (Fin D)) :
    (Matrix.of fun j l => Function.update F i (P + Q) (τ l) j l).det =
      (Matrix.of fun j l => Function.update F i P (τ l) j l).det +
      (Matrix.of fun j l => Function.update F i Q (τ l) j l).det := by
  have key : ∀ R : Matrix (Fin D) (Fin D) ℂ, (Matrix.of fun j l => Function.update F i R (τ l) j l) =
      (Matrix.of fun j l => Function.update F i 0 (τ l) j l).updateCol (τ.symm i)
        (fun j => R j (τ.symm i)) := by
    intro R
    ext j l
    by_cases h : l = τ.symm i
    · subst h
      simp
    · have hl : τ l ≠ i := fun e => h (by rw [← e, Equiv.symm_apply_apply])
      simp [Matrix.updateCol_ne h, Function.update_of_ne hl]
  rw [key (P + Q), key P, key Q, ← Matrix.det_updateCol_add]
  rfl

theorem dens_update_tens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (L : Fin D → MLine p σ) (i : Fin D) (A B : MLine p σ) (c : AlgChart p σ D), ∀ y ∈ c.e.source, dens (Function.update L i (A.tens B)) c y = dens (Function.update L i A) c y + dens (Function.update L i B) c y := by
  intro k _ X p σ D L i A B c y hy
  let G : MLine p σ → Matrix (Fin D) (Fin D) ℂ := fun M => c.hess M.φ (pick M.φ.isLB y) y
  have hd : ∀ L' : Fin D → MLine p σ, dens L' c y = (Real.pi ^ D)⁻¹ *
      (∑ τ : Equiv.Perm (Fin D), (Matrix.of fun j l => (G ∘ L') (τ l) j l).det).re := fun _ => rfl
  have hT : G (A.tens B) = G A + G B := by
    have ha := mem_pick A.φ.isLB y
    have hb := mem_pick B.φ.isLB y
    have hab : y ∈ ptsIn p σ ((A.tens B).B.U (pick A.φ.isLB y, pick B.φ.isLB y)) :=
      mem_ptsIn_inf.2 ⟨ha, hb⟩
    show c.hess (A.tens B).φ _ y = _
    rw [c.hess_eq (A.tens B).cInf hy hab (mem_pick _ y)]
    have ho := isOpen_over c.e
      (isOpen_ptsIn (p := p) (σ := σ) (A.B.U (pick A.φ.isLB y) ⊓ B.B.U (pick B.φ.isLB y)))
    have hm := mem_over c.e hy (mem_ptsIn_inf.2 ⟨ha, hb⟩)
    have e := ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul ho
      ((contDiffOn_chart (A.cInf _) c).mono fun v hv => ⟨hv.1, (mem_ptsIn_inf.1 hv.2).1⟩)
      ((contDiffOn_chart (B.cInf _) c).mono fun v hv => ⟨hv.1, (mem_ptsIn_inf.1 hv.2).2⟩) 1 hm
    simp only [one_mul, Complex.ofReal_one, one_smul, Function.comp_apply] at e
    exact e
  rw [hd, hd, hd, Function.comp_update, Function.comp_update, Function.comp_update, hT]
  simp only [det_perm_update_add, Finset.sum_add_distrib, Complex.add_re]
  ring

end GlobalTheory.Mix
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MixPull

theorem hess_pull {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
    (π : Y ⟶ X) (hπ : π ≫ p = q) (A : MLine p σ) (c : AlgChart p σ D) (c' : AlgChart q σ D)
    (H : ∀ w ∈ c'.e.source, ptMap π hπ σ w ∈ c.e.source ∧ c'.e w = c.e (ptMap π hπ σ w))
    (z : CxPts q σ) (hz : z ∈ c'.e.source) :
    c'.hess (A.pull π hπ).φ (pick (A.pull π hπ).φ.isLB z) z = c.hess A.φ (pick A.φ.isLB (ptMap π hπ σ z)) (ptMap π hπ σ z) := by
  have hz' := (H z hz).1
  have hj := mem_of_mem_linComb (m := fun _ => PtsOver.map π hπ _ z) (fun _ => rfl)
    (mem_pick (A.φ.pull π hπ).isLB z) PUnit.unit
  rw [c.hess_eq A.cInf hz' hj (mem_pick _ _)]
  show c'.hess (A.φ.pull π hπ) _ z = _
  unfold AlgChart.hess
  rw [← (H z hz).2]
  refine ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr ?_
  filter_upwards [c'.e.open_target.mem_nhds (c'.e.map_source hz)] with v hv
  have hw := c'.e.map_target hv
  obtain ⟨h₁, h₂⟩ := H _ hw
  rw [c'.e.right_inv hv] at h₂
  have e₁ : c.e.symm v = PtsOver.map π hπ (spMap σ) (c'.e.symm v) := by
    exact (congrArg c.e.symm h₂).trans (c.e.left_inv h₁)
  rw [e₁]
  exact congrArg _ (A.φ.pull_φ π hπ _ _)

theorem dens_pull : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (π : Y ⟶ X) (hπ : π ≫ p = q) (L : Fin D → MLine p σ) (c : AlgChart p σ D) (c' : AlgChart q σ D), (∀ w ∈ c'.e.source, ptMap π hπ σ w ∈ c.e.source ∧ c'.e w = c.e (ptMap π hπ σ w)) → ∀ w ∈ c'.e.source, dens (fun i => (L i).pull π hπ) c' w = dens L c (ptMap π hπ σ w) := by
  intro k _ X Y p q σ D π hπ L c c' H w hw
  have e : ∀ τ : Equiv.Perm (Fin D), (Matrix.of fun j l =>
      c'.hess ((fun i => (L i).pull π hπ) (τ l)).φ (pick ((fun i => (L i).pull π hπ) (τ l)).φ.isLB w) w j l) =
      Matrix.of fun j l => c.hess (L (τ l)).φ (pick (L (τ l)).φ.isLB (ptMap π hπ σ w)) (ptMap π hπ σ w) j l := by
    intro τ
    ext j l
    simp only [Matrix.of_apply]
    rw [hess_pull π hπ (L (τ l)) c c' H w hw]
  simp only [dens, e]

end GlobalTheory.MixPull
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjSpace

namespace GlobalTheory.AmpleTwistNef

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}

theorem nefFib_of_cls_eq {L M : HermLB p} (h : cls L.B L.isLB = cls M.B M.isLB) (hL : ArInt.NefFib L) :
    ArInt.NefFib M := by
  intro Z i _ _ κ _ _ _ hd
  have e : cls (L.B.pull i) (pull_isLB L.isLB i) = cls (M.B.pull i) (pull_isLB M.isLB i) := by
    rw [cls_pull L.isLB i, cls_pull M.isLB i, h]
  rw [← topSelf_congr κ (pull_isLB L.isLB i) (pull_isLB M.isLB i) ((cls_eq_iff _ _).1 e)]
  exact hL Z i κ hd

end GlobalTheory.AmpleTwistNef

namespace GlobalTheory.AmpleTwistNef

open GlobalTheory.ArInt

end GlobalTheory.AmpleTwistNef
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points

namespace GlobalTheory

theorem addMonoidHom_intCast_mul_real {A : Type} [CommRing A] (θ : A →+ ℝ) (k : ℤ) (z : A) :
    θ ((k : A) * z) = (k : ℝ) * θ z := by
  rw [← zsmul_eq_mul, map_zsmul, zsmul_eq_mul]

theorem polarisation_mixed_term_of_powers : ∀ (A : Type) [CommRing A] (θ : A →+ ℝ) (ι : Type) [Fintype ι] (x : Option ι → A) (D : ℕ) (Φ : MvPolynomial (Option ι) ℝ →ₗ[ℝ] ℝ), (∀ n : Option ι → ℤ, Φ (lin (fun o => (n o : ℝ)) ^ (D + 1)) = θ ((∑ o, n o • x o) ^ (D + 1))) → ∀ n : ι → ℤ, Φ (MvPolynomial.X none * rename some (lin fun i => (n i : ℝ)) ^ D) = θ ((∑ i, n i • x (some i)) ^ D * x none) := by
  intro A _ θ ι _ x D Φ h n
  set Y : MvPolynomial (Option ι) ℝ := MvPolynomial.X none with hY
  set L : MvPolynomial (Option ι) ℝ := rename some (lin fun i => (n i : ℝ)) with hL
  set y : A := ∑ i, n i • x (some i) with hy
  set P : Polynomial ℝ := ∑ a ∈ Finset.range (D + 2),
    Polynomial.C (Φ (Y ^ a * L ^ (D + 1 - a)) * ((D + 1).choose a : ℝ)) * Polynomial.X ^ a with hP
  set Q : Polynomial ℝ := ∑ a ∈ Finset.range (D + 2),
    Polynomial.C (θ (x none ^ a * y ^ (D + 1 - a)) * ((D + 1).choose a : ℝ)) * Polynomial.X ^ a with hQ
  have key : ∀ t : ℤ, P.eval (t : ℝ) = Q.eval (t : ℝ) := by
    intro t
    have ht := h (fun o => Option.elim o t n)
    have hlin : lin (fun o => ((Option.elim o t n : ℤ) : ℝ)) = MvPolynomial.C (t : ℝ) * Y + L := by

      simp only [lin, Fintype.sum_option, Option.elim, hY, hL, map_sum, map_mul, rename_C, rename_X]
    have hsum : (∑ o, (Option.elim o t n) • x o) = (t : A) * x none + y := by
      simp only [Fintype.sum_option, Option.elim, hy, zsmul_eq_mul]

    rw [hlin, hsum, add_pow, add_pow, map_sum, map_sum] at ht
    simp only [hP, hQ, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    have e1 : ∀ a : ℕ, Φ ((MvPolynomial.C (t : ℝ) * Y) ^ a * L ^ (D + 1 - a) * (((D + 1).choose a : ℕ) : MvPolynomial (Option ι) ℝ))
        = Φ (Y ^ a * L ^ (D + 1 - a)) * ((D + 1).choose a : ℝ) * (t : ℝ) ^ a := by
      intro a
      have : (MvPolynomial.C (t : ℝ) * Y) ^ a * L ^ (D + 1 - a) * (((D + 1).choose a : ℕ) : MvPolynomial (Option ι) ℝ)
          = ((t : ℝ) ^ a * ((D + 1).choose a : ℝ)) • (Y ^ a * L ^ (D + 1 - a)) := by
        rw [MvPolynomial.smul_eq_C_mul, map_mul, map_pow, mul_pow, map_natCast]
        ring
      rw [this, map_smul, smul_eq_mul]
      ring
    have e2 : ∀ a : ℕ, θ (((t : A) * x none) ^ a * y ^ (D + 1 - a) * (((D + 1).choose a : ℕ) : A))
        = θ (x none ^ a * y ^ (D + 1 - a)) * ((D + 1).choose a : ℝ) * (t : ℝ) ^ a := by
      intro a
      have : ((t : A) * x none) ^ a * y ^ (D + 1 - a) * (((D + 1).choose a : ℕ) : A)
          = (((t ^ a * ((D + 1).choose a : ℤ)) : ℤ) : A) * (x none ^ a * y ^ (D + 1 - a)) := by
        push_cast
        ring
      rw [this, addMonoidHom_intCast_mul_real]
      push_cast
      ring
    simp only [e1, e2] at ht
    exact ht
  have hPQ : P = Q := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply Set.Infinite.mono (s := Set.range (fun t : ℤ => (t : ℝ)))
    · rintro _ ⟨t, rfl⟩
      exact key t
    · exact Set.infinite_range_of_injective Int.cast_injective
  have hc := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p 1) hPQ
  simp only [hP, hQ, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow] at hc
  simp only [Finset.sum_ite_eq, Finset.mem_range] at hc
  rw [if_pos (by omega), if_pos (by omega)] at hc
  · simp only [pow_one, Nat.choose_one_right, Nat.add_sub_cancel] at hc
    have hD : ((D + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    push_cast at hc hD
    have := mul_right_cancel₀ hD hc
    rw [mul_comm (y ^ D)]
    exact this

end GlobalTheory
end

section

set_option autoImplicit false


noncomputable section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArInt GlobalTheory.VB

namespace GlobalTheory.CovTest

def GdegPull : Prop :=
  ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D : ℕ),
    IsArithVar p D → IsArithVar q D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X →
    π.residueDegree (genericPoint Y) ≠ 0 → ∀ L : HermLB p,
      gdeg (L.pull π hπ) D = (π.residueDegree (genericPoint Y) : ℝ) * gdeg L D

end GlobalTheory.CovTest

end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
open ReciprocityTheory.L2DbarEstimates (V cHess)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mix

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

theorem MLine.Isom.hess_eq {L M : MLine p σ} (h : L.Isom M) (c : AlgChart p σ D) {y : CxPts p σ}
    (hy : y ∈ c.e.source) {a : M.B.ι} {b : L.B.ι} (ha : y ∈ ptsIn p σ (M.B.U a)) (hb : y ∈ ptsIn p σ (L.B.U b)) :
    c.hess M.φ a y = c.hess L.φ b y := by
  obtain ⟨w, -, h⟩ := h
  have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (M.B.U a ⊓ L.B.U b))
  have hm := mem_over c.e hy (mem_ptsIn_inf.2 ⟨ha, hb⟩)
  have hg := c.holo _ (w.s (a, b)).val
  have h0 : ∀ v ∈ c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ (M.B.U a ⊓ L.B.U b),
      (ev p σ _ (w.s (a, b)).val ∘ c.e.symm) v ≠ 0 :=
    fun v hv => ev_ne_zero hv.2 (w.s _).isUnit
  have e := ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul ho
    ((contDiffOn_chart (L.cInf _) c).mono fun v hv => ⟨hv.1, (mem_ptsIn_inf.1 hv.2).2⟩)
    (contDiffOn_log_normSq ho hg h0) 1 hm
  have e₀ : cHess D (fun v => ((Real.log (‖(ev p σ _ (w.s (a, b)).val ∘ c.e.symm) v‖ ^ 2) : ℝ) : ℂ))
      (c.e y) = 0 := by
    ext a b
    exact ReciprocityTheory.L2DbarEstimates.Y.cmpa_hess_log ho hm hg h0 a b
  rw [e₀, smul_zero, add_zero] at e
  refine Eq.trans (ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr ?_) e
  filter_upwards [ho.mem_nhds hm] with v hv
  rw [h _ _ _ (mem_ptsIn_inf.1 hv.2).1 (mem_ptsIn_inf.1 hv.2).2, one_mul]
  rfl

theorem dens_congr_isom {L M : Fin D → MLine p σ} (h : ∀ i, (L i).Isom (M i)) (c : AlgChart p σ D)
    {y : CxPts p σ} (hy : y ∈ c.e.source) : dens L c y = dens M c y := by
  have e (i : Fin D) := (h i).hess_eq c hy (mem_pick (M i).φ.isLB y) (mem_pick (L i).φ.isLB y)
  simp only [dens, e]

theorem part_congr_isom {L M : Fin D → MLine p σ} (h : ∀ i, (L i).Isom (M i)) (ε : ℤˣ) :
    part L ε = part M ε := by
  refine iSup_congr fun c => Measure.ext fun S hS => ?_
  rw [chartMeas_apply _ _ hS, chartMeas_apply _ _ hS]
  refine setLIntegral_congr_fun ?_ ?_
  · exact measurableSet_image c.e (c.e.open_source.measurableSet.inter hS) inter_subset_left
  · rintro _ ⟨y, hy, rfl⟩
    simp only [c.e.left_inv hy.1, dens_congr_isom h c hy.1]

theorem part_eq_of_isom : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ), IsProjOver p → ∀ (D : ℕ) (L M : Fin D → MLine p σ), (∀ i, (L i).Isom (M i)) → ∀ ε : ℤˣ, part L ε = part M ε :=
  fun _ _ _ _ _ _ _ _ _ h ε => part_congr_isom h ε

end GlobalTheory.Mix
end
end
