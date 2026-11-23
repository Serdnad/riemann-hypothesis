module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle088
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.HmSelfRe
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.Bundle003
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.XiHermitianCofactorDet
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle089
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointLeibnizExpansion
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle029
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle086
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle093
import Formalism.FormalDegreeBessel.FinalG
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuadraticFormTwoTwo.GANormSqStar
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Sqrt
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom

open Formalism.QuantumDeterminants PI.UnitaryGroupMassFormula.GsFr
open scoped Matrix

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace S1

variable {k r : ℕ}

lemma smooth_hermitian_rank_two {s : Set (B.Mat k r)} {p q : B.Mat k r → Fin (2 * r + k + 1) → ℂ}
    (hp : Sm p s) (hq : Sm q s) : Sm (fun x => Rk k r (p x) (q x)) s := by
  unfold Sm Rk at *
  refine contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr fun j => ?_
  simp only [Matrix.vecMulVec_apply, Matrix.vecMul, dotProduct, Pi.star_apply]
  have hs : ∀ l, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => star (q x l)) s := fun l => by
    have h := Complex.conjCLE.contDiff.comp_contDiffOn (contDiffOn_pi.mp hq l)
    simpa [Function.comp_def] using h
  exact (contDiffOn_pi.mp hp i).mul (ContDiffOn.sum fun l _ => (hs l).mul contDiffOn_const)

lemma s_unitH {s : Set (B.Mat k r)} {v : B.Mat k r → Fin (2 * r + k + 1) → ℂ} (hv : Sm v s)
    (hp : ∀ x ∈ s, 0 < (Formalism.QuantumDeterminants.herm (Hpk k r) (v x) (v x)).re) : Sm (fun x => unitH k r (v x)) s := by
  unfold Sm unitH Formalism.QuantumDeterminants.herm at *
  have hvi : ∀ i, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => v x i) s := fun i => contDiffOn_pi.mp hv i
  have hsi : ∀ i, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => star (v x i)) s := fun i => by
    have h := Complex.conjCLE.contDiff.comp_contDiffOn (hvi i)
    simpa [Function.comp_def] using h
  have hh : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => star (v x) ⬝ᵥ Hpk k r *ᵥ v x) s := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
    exact ContDiffOn.sum fun i _ => (hsi i).mul (ContDiffOn.sum fun j _ => contDiffOn_const.mul (hvi j))
  have hre : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => (star (v x) ⬝ᵥ Hpk k r *ᵥ v x).re) s := by
    have h := Complex.reCLM.contDiff.comp_contDiffOn hh
    simpa [Function.comp_def] using h
  have hsq := hre.sqrt fun x hx => (hp x hx).ne'
  have hinv := hsq.inv fun x hx => (Real.sqrt_pos.mpr (hp x hx)).ne'
  have hc : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => (((Real.sqrt (star (v x) ⬝ᵥ Hpk k r *ᵥ v x).re)⁻¹ : ℝ) : ℂ)) s := by
    have h := Complex.ofRealCLM.contDiff.comp_contDiffOn hinv
    simpa [Function.comp_def] using h
  exact hc.smul hv

end S1

open S1 in
theorem geometry_smoothness_holds : GeomSmooth := by
  intro k r z z' _hk hz hz'
  let fd : B.Mat k r → ℂ := fun g => (Zhat k r z z' g).det
  let f1 : B.Mat k r → ℝ := fun g =>
    (Formalism.QuantumDeterminants.herm (Hpk k r) (omW k r z z' g) (omW k r z z' g)).re
  let f2 : B.Mat k r → ℝ := fun g =>
    (Formalism.QuantumDeterminants.herm (Hpk k r) (omS k r z z' g) (omS k r z z' g)).re
  have hid : Sm (fun g : B.Mat k r => g) Set.univ := contDiffOn_id
  have cd : Continuous fd := (contDiffOn_univ.1 (s_det (s_Zhat z z' hid))).continuous
  have c1 : Continuous f1 :=
    (contDiffOn_univ.1 (s_re (s_herm _ (s_omW z z' hid) (s_omW z z' hid)))).continuous
  have c2 : Continuous f2 :=
    (contDiffOn_univ.1 (s_re (s_herm _ (s_omS (s := Set.univ) z z') (s_omS z z')))).continuous
  let U : Set (B.Mat k r) := (fd ⁻¹' {0}ᶜ ∩ {g | 0 < f1 g}) ∩ {g | 0 < f2 g}
  have hU : IsOpen U :=
    ((isOpen_compl_singleton.preimage cd).inter (isOpen_lt continuous_const c1)).inter
      (isOpen_lt continuous_const c2)
  have hmem : ∀ g ∈ posG k r z z', g ∈ U := by
    intro g hg
    obtain ⟨hgV, hG⟩ := hg
    refine ⟨⟨det_ne_of_G hz hz' hG, ?_⟩, ?_⟩
    · have hm : omW k r z z' g ∈ Wsp k r z := prW_mem hz _
      exact posV hz hm.1 hm.2 (omW_ne hz hz' hgV hG)
    · have hm : omS k r z z' g ∈ Wsp k r z' := prW_mem hz' _
      have hω : omS k r z z' g ≠ 0 := by rw [← omS_eq z z' hgV]; exact omW'_ne hz hz' hgV hG
      exact posV hz' hm.1 hm.2 hω
  have sU : Sm (fun g : B.Mat k r => g) U := contDiffOn_id
  have hd0 : ∀ g ∈ U, (Zhat k r z z' g).det ≠ 0 := fun g hg => hg.1.1
  have hnu : Sm (fun g => nuG z z' g) U := s_unitH (s_omW z z' sU) fun g hg => hg.1.2
  have hnuS : Sm (fun g => unitH k r (omS k r z z' g)) U := s_unitH (s_omS z z') fun g hg => hg.2
  have hdi : Sm (fun g => -((Zhat k r z z' g).det)⁻¹) U := ((s_det (s_Zhat z z' sU)).inv hd0).neg
  have hL : Sm (fun g => Lm k r z z' g) U := by
    unfold Lm
    exact contDiffOn_const.add (ContDiffOn.sum fun c _ => ContDiffOn.sum fun a _ =>
      s_msmul (hdi.mul (s_adj (s_Zhat z z' sU) c a)) (s_mmul contDiffOn_const sU))
  have hP : Sm (fun g => Phi k r z z' g) U := by
    unfold Phi
    exact s_mmul (s_mmul contDiffOn_const sU) hL
  have hio : Sm (fun g => Phi k r z z' g *
      (Pm k r z' - Rk k r (unitH k r (omS k r z z' g)) (unitH k r (omS k r z z' g)) * Pm k r z')) U :=
    s_mmul hP (contDiffOn_const.sub (s_mmul (smooth_hermitian_rank_two hnuS hnuS) contDiffOn_const))
  refine ⟨fun g₀ hg₀ => ⟨U, fun g => nuG z z' g, hU, hmem g₀ hg₀, hnu, fun g _ _ => rfl⟩,
    fun g₀ hg₀ => ⟨U, fun g => unitH k r (omS k r z z' g), hU, hmem g₀ hg₀, hnuS, fun g _ hgV => ?_⟩,
    fun g₀ hg₀ => ⟨U, _, hU, hmem g₀ hg₀, hio, fun g _ hgV => ?_⟩⟩
  · show unitH k r (omW' k r z z' g) = _
    rw [omS_eq z z' hgV]
  · show Phi k r z z' g * (Pm k r z' - Rk k r (unitH k r (omW' k r z z' g)) (unitH k r (omW' k r z z' g)) *
      Pm k r z') = _
    rw [omS_eq z z' hgV]

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom
end

section

namespace Formalism.FourierDecayAlt.P.CutBP.LeibExp

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def Gc (z z' : Fin (2 * r + k + 1) → ℂ) : B.Mat k r → ℂ := fun g => ((Gf k r z z' g : ℝ) : ℂ)

theorem gc_poly (z z' : Fin (2 * r + k + 1) → ℂ) : ListSumSplittings.PolyClass (2 * r + 2) (Gc (k := k) (r := r) z z') := by
  apply ListSumSplittings.polyClass_of_isPolyDeg
  obtain ⟨q, hq, h⟩ := Formalism.FourierDecayAlt.P.gram_function_polynomial k r z z'
  exact ⟨q, hq, h⟩

abbrev Tm (k r : ℕ) := ℕ × (B.Mat k r → ℂ) × ℕ × List (B.Mat k r)

def coefT (z z' : Fin (2 * r + k + 1) → ℂ) (Ψ : ℕ → ℝ → ℝ) (t : Tm k r) (y : B.Mat k r) : ℂ :=
  ((Ψ t.1 (Gf k r z z' y) : ℝ) : ℂ) * t.2.1 y * ((Gf k r z z' y : ℝ) : ℂ)⁻¹ ^ t.2.2.1

def step (z z' : Fin (2 * r + k + 1) → ℂ) (X : B.Mat k r) (t : Tm k r) : List (Tm k r) :=
  [(t.1 + 1, fun y => Formalism.REAL.RdV X (Gc z z') y * t.2.1 y, t.2.2.1 + 1, t.2.2.2),
   (t.1, Formalism.REAL.RdV X t.2.1, t.2.2.1, t.2.2.2),
   (t.1, fun y => (-(t.2.2.1 : ℂ)) * (Formalism.REAL.RdV X (Gc z z') y * t.2.1 y), t.2.2.1 + 1, t.2.2.2),
   (t.1, t.2.1, t.2.2.1, X :: t.2.2.2)]

theorem sum_flatMap {α β M : Type*} [AddCommMonoid M] (L : List α) (f : α → List β) (g : β → M) :
    ((L.flatMap f).map g).sum = (L.map fun a => ((f a).map g).sum).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih]

theorem term_deriv (z z' : Fin (2 * r + k + 1) → ℂ) (Ψ : ℕ → ℝ → ℝ) (hΨ : ThChain Ψ) (t : Tm k r)
    (hP : ListSumSplittings.PolyClass 0 t.2.1 ∨ B.CkOn ⊤ (B.GV k r) t.2.1)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (hF : B.CkOn ⊤ (B.GV k r) F) (hv : ∀ Y ∈ t.2.2.2, B.inLie k r Y)
    {X x : B.Mat k r} (hX : B.inLie k r X) (hxG : x ∈ B.GV k r) (hxp : 0 < Gf k r z z' x) :
    HasDerivAt (fun s : ℝ => coefT z z' Ψ t (x * NormedSpace.exp ((s : ℂ) • X)) •
        B.Rw t.2.2.2 F (x * NormedSpace.exp ((s : ℂ) • X)))
      (((step z z' X t).map fun t' => coefT z z' Ψ t' x • B.Rw t'.2.2.2 F x).sum) 0 := by
  obtain ⟨q, P, j, v⟩ := t
  simp only at hP hv ⊢
  have hPC : B.CkOn ⊤ (B.GV k r) P := by rcases hP with h | h; exact h.1; exact h
  set c : ℝ → B.Mat k r := fun s => x * NormedSpace.exp ((s : ℂ) • X) with hcdef
  have hc0 : c 0 = x := B5.curve_zero x X
  have hGc : HasDerivAt (fun s => Gc z z' (c s)) (Formalism.REAL.RdV X (Gc z z') x) 0 :=
    JFxI.rdV_hasDerivAt' (B5.ckOn_mono le_top (gc_poly z z').1) hxG hxG hX
  have hdiff : DifferentiableAt ℝ (fun s => Gf k r z z' (c s)) 0 := by
    have h1 : Differentiable ℝ (fun g : B.Mat k r => Gf k r z z' g) :=
      (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf z z').differentiable (by simp)
    have h2 : Differentiable ℝ c := (B5.curve_contDiff x X).differentiable (by simp)
    exact (h1 (c 0)).comp (0 : ℝ) (h2 0)
  set dG : ℝ := deriv (fun s => Gf k r z z' (c s)) 0 with hdG
  have hGr : HasDerivAt (fun s => Gf k r z z' (c s)) dG 0 := hdiff.hasDerivAt
  have hD : Formalism.REAL.RdV X (Gc z z') x = (dG : ℂ) := by
    have h2 := hGr.ofReal_comp
    exact hGc.unique (by simpa [Gc] using h2)
  have hGx : Gf k r z z' (c 0) = Gf k r z z' x := by rw [hc0]
  have hne : Gf k r z z' (c 0) ≠ 0 := by rw [hGx]; exact hxp.ne'
  have hΨq : HasDerivAt (Ψ q) (Ψ (q + 1) (Gf k r z z' x) / Gf k r z z' x) (Gf k r z z' (c 0)) := by
    rw [hGx]; exact hΨ q _ hxp
  have hψ := (hΨq.comp (0 : ℝ) hGr).ofReal_comp
  have hPd : HasDerivAt (fun s => P (c s)) (Formalism.REAL.RdV X P x) 0 :=
    JFxI.rdV_hasDerivAt' (B5.ckOn_mono le_top hPC) hxG hxG hX
  have hI := ((hGr.inv hne).pow j).ofReal_comp
  have hR : HasDerivAt (fun s => B.Rw v F (c s)) (Formalism.REAL.RdV X (B.Rw v F) x) 0 :=
    JFxI.rdV_hasDerivAt' (B5.ckOn_mono le_top (JFxI.ckOn_Rw_top' hF v hv)) hxG hxG hX
  have hA := ((hψ.mul hPd).mul hI).smul hR
  refine (hA.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)).congr_deriv ?_
  · simp only [coefT, Function.comp_apply, Pi.pow_apply, Pi.inv_apply, Complex.ofReal_pow, Complex.ofReal_inv]
    rfl
  simp only [step, coefT, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hc0,
    Function.comp_apply, Pi.mul_apply, Pi.pow_apply, Pi.inv_apply, hD]
  have hRw : B.Rw (X :: v) F x = Formalism.REAL.RdV X (B.Rw v F) x := rfl
  rw [hRw]
  rcases j with _ | j
  · push_cast
    module
  · simp only [Nat.add_sub_cancel]
    push_cast
    module

theorem exp_main (Bs : B.RealPlaceData k r Wp Wq) (w : List (B.Mat k r)) (hw : ∀ X ∈ w, B.inLie k r X) :
    ∃ terms : List (Tm k r),
      (∀ t ∈ terms, t.1 ≤ w.length ∧ ListSumSplittings.PolyClass ((2 * r + 2) * w.length) t.2.1 ∧ t.2.2.2.Sublist w) ∧
      ∀ Ψ : ℕ → ℝ → ℝ, ThChain Ψ → ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) F →
        ∀ x ∈ C6.domL Bs ∅,
          B.Rw w (fun y => ((Ψ 0 (Gf k r Bs.z Bs.z' y) : ℝ) : ℂ) • F y) x =
            (terms.map fun t => coefT Bs.z Bs.z' Ψ t x • B.Rw t.2.2.2 F x).sum := by
  induction w with
  | nil =>
    refine ⟨[(0, fun _ => 1, 0, [])], ?_, ?_⟩
    · intro t ht
      simp only [List.mem_singleton] at ht
      subst ht
      refine ⟨le_rfl, ?_, List.Sublist.refl _⟩
      rw [List.length_nil, mul_zero]
      exact ListSumSplittings.polyClass_const 1
    · intro Ψ _ F _ x _
      simp [coefT, B.Rw]
  | cons X w ih =>
    have hwL : ∀ Y ∈ w, B.inLie k r Y := fun Y hY => hw Y (List.mem_cons_of_mem _ hY)
    have hXL : B.inLie k r X := hw X List.mem_cons_self
    obtain ⟨terms, hprop, hid⟩ := ih hwL
    refine ⟨terms.flatMap (step Bs.z Bs.z' X), ?_, ?_⟩
    · intro t' ht'
      rw [List.mem_flatMap] at ht'
      obtain ⟨t, ht, ht'⟩ := ht'
      obtain ⟨h1, h2, h3⟩ := hprop t ht
      have hGp := gc_poly (k := k) (r := r) Bs.z Bs.z'
      have hdeg : (2 * r + 2) * w.length ≤ (2 * r + 2) * (X :: w).length := by
        simp only [List.length_cons]; exact Nat.mul_le_mul_left _ (Nat.le_succ _)
      have hdeg2 : (2 * r + 2) + (2 * r + 2) * w.length = (2 * r + 2) * (X :: w).length := by
        simp only [List.length_cons]; ring
      simp only [step, List.mem_cons, List.not_mem_nil, or_false] at ht'
      rcases ht' with rfl | rfl | rfl | rfl
      · refine ⟨by simp only [List.length_cons]; omega, ?_, h3.cons X⟩
        rw [← hdeg2]
        exact ListSumSplittings.polyClass_mul (ListSumSplittings.polyClass_op hGp false hXL) h2
      · exact ⟨by simp only [List.length_cons]; omega,
          ListSumSplittings.polyClass_mono hdeg (ListSumSplittings.polyClass_op h2 false hXL), h3.cons X⟩
      · refine ⟨by simp only [List.length_cons]; omega, ?_, h3.cons X⟩
        rw [← hdeg2]
        exact ListSumSplittings.polyClass_cmul _ (ListSumSplittings.polyClass_mul (ListSumSplittings.polyClass_op hGp false hXL) h2)
      · exact ⟨by simp only [List.length_cons]; omega, ListSumSplittings.polyClass_mono hdeg h2, h3.cons_cons X⟩
    · intro Ψ hΨ F hF x hx
      have hVo : IsOpen {g : B.Mat k r | 0 < Gf k r Bs.z Bs.z' g} :=
        isOpen_lt continuous_const (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf Bs.z Bs.z').continuous
      have hloc := PositiveOrbitOpen.rdV_local (f₁ := B.Rw w (fun y => ((Ψ 0 (Gf k r Bs.z Bs.z' y) : ℝ) : ℂ) • F y))
        (f₂ := fun y => (terms.map fun t => coefT Bs.z Bs.z' Ψ t y • B.Rw t.2.2.2 F y).sum) hVo
        (fun y hy hyG => hid Ψ hΨ F hF y ⟨hyG, hy, fun l hl => absurd hl (Finset.notMem_empty l)⟩) hXL x hx.2.1 hx.1
      change Formalism.REAL.RdV X (B.Rw w (fun y => ((Ψ 0 (Gf k r Bs.z Bs.z' y) : ℝ) : ℂ) • F y)) x = _
      rw [hloc]
      have hd := JFxI.hasDerivAt_list_sum terms
        (fun t s => coefT Bs.z Bs.z' Ψ t (x * NormedSpace.exp ((s : ℂ) • X)) •
          B.Rw t.2.2.2 F (x * NormedSpace.exp ((s : ℂ) • X)))
        (fun t => ((step Bs.z Bs.z' X t).map fun t' => coefT Bs.z Bs.z' Ψ t' x • B.Rw t'.2.2.2 F x).sum)
        (t := 0) (fun t ht => term_deriv Bs.z Bs.z' Ψ hΨ t (Or.inr (hprop t ht).2.1.1) F hF
          (fun Y hY => hwL Y ((hprop t ht).2.2.subset hY)) hXL hx.1 hx.2.1)
      change deriv (fun s : ℝ => (terms.map fun t => coefT Bs.z Bs.z' Ψ t (x * NormedSpace.exp ((s : ℂ) • X)) •
          B.Rw t.2.2.2 F (x * NormedSpace.exp ((s : ℂ) • X))).sum) 0 = _
      rw [hd.deriv, sum_flatMap]

end

end Formalism.FourierDecayAlt.P.CutBP.LeibExp

namespace Formalism.FourierDecayAlt.P.CutBP

theorem leibniz_expansion_holds : NFLeibExp := by
  unfold NFLeibExp
  intro k r Wp Wq _ _ _ _ Bs w hw
  exact LeibExp.exp_main Bs w hw

end Formalism.FourierDecayAlt.P.CutBP
end

section

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.PRhoCut

open Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

namespace EigenvectorOrthogonality

variable {k r : ℕ}

private theorem herm_mulVec_of_conjTranspose_mul_H_mul_eq {n : ℕ} {H g : Matrix (Fin n) (Fin n) ℂ} (hg : gᴴ * H * g = H)
    (v w : Fin n → ℂ) : herm H (g *ᵥ v) (g *ᵥ w) = herm H v w := by
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
  simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hg]

theorem frame_move {z e : Fin (2 * r + k + 1) → ℂ} {h : Mx k r} (hh : h ∈ UWset k r z) (he : h *ᵥ e = e) {m : ℕ}
    {F : Fin m → Fin (2 * r + k + 1) → ℂ} (hF : IsFrameOf k r [z, e] F) :
    IsFrameOf k r [z, e] (fun p => h *ᵥ F p) := by
  have hG : h ∈ Glev k r (Fin.last r) := ⟨hh.1, fun a _ => hh.2.1 a⟩
  have hU : hᴴ * Hpk k r * h = Hpk k r := hh.1
  refine ⟨fun a => (Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.glev_inWb hG (hF.1 a)).1, fun a b => ?_, fun a v hv => ?_⟩
  · rw [herm_mulVec_of_conjTranspose_mul_H_mul_eq hU]
    exact hF.2.1 a b
  · have hv' : h *ᵥ v = v := by
      rcases List.mem_cons.1 hv with rfl | hv2
      · exact hh.2.2
      · rcases List.mem_cons.1 hv2 with rfl | hv3
        · exact he
        · simp at hv3
    calc herm (Hpk k r) (h *ᵥ F a) v = herm (Hpk k r) (h *ᵥ F a) (h *ᵥ v) := by rw [hv']
      _ = 0 := by rw [herm_mulVec_of_conjTranspose_mul_H_mul_eq hU]; exact hF.2.2 a v hv

theorem frame_swap {z e : Fin (2 * r + k + 1) → ℂ} {m : ℕ} {F : Fin m → Fin (2 * r + k + 1) → ℂ}
    (hF : IsFrameOf k r [z, e] F) : IsFrameOf k r [e, z] F :=
  ⟨hF.1, hF.2.1, fun a v hv => hF.2.2 a v (by simp only [List.mem_cons] at hv ⊢; tauto)⟩

private theorem isUnit_det_of_mem_UWset {h : Mx k r} {z : Fin (2 * r + k + 1) → ℂ} (hh : h ∈ UWset k r z) :
    IsUnit h.det := by
  have hU : hᴴ * Hpk k r * h = Hpk k r := hh.1
  have hH : (Hpk k r).det ≠ 0 := by
    have h1 := congrArg Matrix.det (Formalism.QuantumDeterminants.hpkFacts k r).2.1
    rw [Matrix.det_mul, Matrix.det_one] at h1
    intro h0
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  have h2 := congrArg Matrix.det hU
  rw [Matrix.det_mul, Matrix.det_mul] at h2
  refine isUnit_iff_ne_zero.2 fun h0 => hH ?_
  rw [h0, mul_zero] at h2
  exact h2.symm

theorem mulVec_inv_cancel {h : Mx k r} {z : Fin (2 * r + k + 1) → ℂ} (hh : h ∈ UWset k r z) (v : Fin (2 * r + k + 1) → ℂ) :
    h *ᵥ (h⁻¹ *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_det_of_mem_UWset hh), Matrix.one_mulVec]

theorem inv_fix {h : Mx k r} {z e : Fin (2 * r + k + 1) → ℂ} (hh : h ∈ UWset k r z) (he : h *ᵥ e = e) :
    h⁻¹ *ᵥ e = e := by
  calc h⁻¹ *ᵥ e = h⁻¹ *ᵥ (h *ᵥ e) := by rw [he]
    _ = e := by rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_det_of_mem_UWset hh), Matrix.one_mulVec]

end EigenvectorOrthogonality

open EigenvectorOrthogonality in
theorem eigenvector_orthogonality_holds : EigOrth := by
  intro Wp _ _ _ k r z e π hz hT hrep hunit hex f g x y hx hy hfg
  obtain ⟨Fr₀, hFr₀⟩ := hex
  obtain ⟨w₀, hw₀⟩ := hfg
  have hlin : ∀ Fr : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ, IsFrameOf k r [z, e] Fr → ∀ w,
      P.Qx8.IsLin (capRep k r π Fr w) := fun Fr hFr w =>
    P.Qx8.capRep_lin hFr (by simp) hrep.1 hrep.2 w
  set S := K k r z e π g with hS

  have hmem : ∀ v ∈ S, v ∈ Kset k r z e π g := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem u hu => exact hu
    | zero =>
      intro Fr hFr w
      rw [(hlin Fr hFr w).map_zero, smul_zero]
    | add a b _ _ ha hb =>
      intro Fr hFr w
      rw [(hlin Fr hFr w).map_add a b, ha Fr hFr w, hb Fr hFr w, smul_add]
    | smul c a _ ha =>
      intro Fr hFr w
      rw [(hlin Fr hFr w).map_smul, ha Fr hFr w, smul_comm]

  have hmul : ∀ a ∈ UWset k r z, ∀ b ∈ UWset k r z, ∀ v, π (a * b) v = π a (π b v) := by
    intro a ha b hb v
    rw [hrep.1.2 a ha b hb]; rfl
  have hinv : ∀ h ∈ UWset k r z, ∀ v, π h (π h⁻¹ v) = v := by
    intro h hh v
    rw [← hmul h hh _ (WeylGroupFacts.uw_inv hh), Matrix.mul_nonsing_inv _ (WeylGroupFacts.isUnit_of_uh hh.1), hrep.1.1]; rfl
  have hstab : ∀ h ∈ UWset k r z, h *ᵥ e = e → ∀ v ∈ Kset k r z e π g, π h v ∈ Kset k r z e π g := by
    intro h hh he v hv Fr hFr w
    have hFr' : IsFrameOf k r [z, e] (fun p => h⁻¹ *ᵥ Fr p) := frame_move (WeylGroupFacts.uw_inv hh) (inv_fix hh he) hFr
    have key := P.Qx8.capRep_intertwine (frame_swap hFr') hrep.1 hrep.2 hh.1 (π h)
      (fun h' hh' _ v => by
        rw [← hmul h hh h' hh', ← hmul _ (WeylGroupFacts.uw_mul (WeylGroupFacts.uw_mul hh hh') (WeylGroupFacts.uw_inv hh)) h hh,
          Matrix.mul_assoc (h * h'), Matrix.nonsing_inv_mul _ (WeylGroupFacts.isUnit_of_uh hh.1), Matrix.mul_one]) w v
    simp only [mulVec_inv_cancel hh] at key
    rw [← key, hv _ hFr' w, map_smul]
  have hstabS : ∀ h ∈ UWset k r z, h *ᵥ e = e → ∀ v ∈ S, π h v ∈ S := fun h hh he v hv =>
    Submodule.subset_span (hstab h hh he v (hmem v hv))
  have hstabO : ∀ h ∈ UWset k r z, h *ᵥ e = e → ∀ u ∈ Sᗮ, π h u ∈ Sᗮ := by
    intro h hh he u hu s hs
    let L : Wp →ₗᵢ[ℂ] Wp := ⟨(π h : Wp →ₗ[ℂ] Wp), hunit h hh⟩
    have hs' : π h⁻¹ s ∈ S := hstabS _ (WeylGroupFacts.uw_inv hh) (inv_fix hh he) s hs
    have e2 : inner ℂ (π h (π h⁻¹ s)) (π h u) = inner ℂ (π h⁻¹ s) u := L.inner_map_map _ _
    rw [hinv h hh s] at e2
    rw [e2]
    exact Submodule.inner_right_of_mem_orthogonal hs' hu
  have hcomm : ∀ h ∈ UWset k r z, h *ᵥ e = e → ∀ v, S.starProjection (π h v) = π h (S.starProjection v) := by
    intro h hh he v
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hstabS h hh he _ (S.starProjection_apply_mem v)) ?_
    intro s hs
    have : π h v - π h (S.starProjection v) = π h (v - S.starProjection v) := by rw [map_sub]
    rw [this]
    exact Submodule.inner_left_of_mem_orthogonal hs
      (hstabO h hh he _ (Submodule.sub_starProjection_mem_orthogonal v))
  have hcap : ∀ v, S.starProjection (capRep k r π Fr₀ w₀ v) = capRep k r π Fr₀ w₀ (S.starProjection v) := by
    intro v
    have key := P.Qx8.capRep_intertwine (frame_swap hFr₀) hrep.1 hrep.2 WeylGroupFacts.uh_one
      (S.starProjection : Wp →L[ℂ] Wp) (fun h' hh' he' v => by
        rw [inv_one, Matrix.one_mul, Matrix.mul_one]; exact hcomm h' hh' he' v) w₀ v
    simpa only [Matrix.one_mulVec] using key
  have hAx : S.starProjection x = 0 := by
    have h1 := hmem _ (S.starProjection_apply_mem x) Fr₀ hFr₀ w₀
    rw [← hcap, hx Fr₀ hFr₀ w₀, map_smul] at h1
    have h2 : (f w₀ - g w₀) • S.starProjection x = 0 := by rw [sub_smul, h1, sub_self]
    exact (smul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hw₀)
  have hyS : y ∈ S := Submodule.subset_span hy
  rw [← (Submodule.starProjection_eq_self_iff).2 hyS, ← Submodule.inner_starProjection_left_eq_right, hAx, inner_zero_left]

end Formalism.FourierDecayAlt.P.CutMP.JA.PRhoCut
end
end
