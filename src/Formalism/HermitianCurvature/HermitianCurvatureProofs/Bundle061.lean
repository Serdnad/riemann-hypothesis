module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle047
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle056
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTConnGaugeB
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle048
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle050
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle057
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle053
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle054
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

private theorem contDiffOn_ann_of_wirt_fnZ_eq (P : M.Par) {u : ℂ → ℂ} (w : M.Var P.r) (F : ℂ → ℂ)
    (hF : ∀ q : MA.Qp P.r P.TT,
      MA.wirt w (MA.ext ((fnZ P u : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ)) q.1 = F q.1.2) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F (Ann P) := by
  have hs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (MA.wirt w (MA.ext ((fnZ P u : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ))) (MA.Qset P.r P.TT) :=
    MA.wirt_smooth (fnZ P u).2 w
  let ι : ℂ → MA.E P.r := fun ζ => ((fun _ => (1 : ℂ)), ζ)
  have hι : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ι := contDiff_const.prodMk contDiff_id
  have hmap : Set.MapsTo ι (Ann P) (MA.Qset P.r P.TT) := fun ζ hζ => ⟨fun _ => one_ne_zero, hζ⟩
  refine (hs.comp hι.contDiffOn hmap).congr fun ζ hζ => ?_
  exact (hF ⟨ι ζ, hmap hζ⟩).symm

theorem dZ_smooth (P : M.Par) {u : ℂ → ℂ} (hu : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (Ann P)) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (NF.dZ u) (Ann P) ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (NF.dZb u) (Ann P) :=
  ⟨contDiffOn_ann_of_wirt_fnZ_eq P M.vz _ fun q => wirtinger_derivative_fibre_function P hu q, contDiffOn_ann_of_wirt_fnZ_eq P M.vzb _ fun q => wirt_fnZ_zb P hu q⟩

section main

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem connF_phase (P : M.Par) (hTT : 0 ≤ P.TT) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (A B u : M.Ty P → ℂ → ℂ) (hAB : SmAB P A B) (hC : ConnF P Bs d e A B)
    (hu : ∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (u ρ) (Ann P) ∧ ∀ ζ ∈ Ann P, ‖u ρ ζ‖ = 1) :
    SmAB P (fun ρ ζ => A ρ ζ + star (u ρ ζ) * NF.dZ (u ρ) ζ) (fun ρ ζ => B ρ ζ - star (u ρ ζ) * NF.dZb (u ρ) ζ) ∧
      ConnF P Bs d (fun ρ ζ => u ρ ζ • e ρ ζ) (fun ρ ζ => A ρ ζ + star (u ρ ζ) * NF.dZ (u ρ) ζ)
        (fun ρ ζ => B ρ ζ - star (u ρ ζ) * NF.dZb (u ρ) ζ) := by
  have hSm : SmAB P (fun ρ ζ => A ρ ζ + star (u ρ ζ) * NF.dZ (u ρ) ζ)
      (fun ρ ζ => B ρ ζ - star (u ρ ζ) * NF.dZb (u ρ) ζ) := fun ρ =>
    ⟨(hAB ρ).1.add ((conj_smooth (hu ρ).1).mul (dZ_smooth P (hu ρ).1).1),
      (hAB ρ).2.sub ((conj_smooth (hu ρ).1).mul (dZ_smooth P (hu ρ).1).2)⟩
  refine ⟨hSm, ?_⟩
  intro Φ ρ
  have hc := conj_smooth (hu ρ).1
  rw [trR_phase P Bs e u hu, trR_phase P Bs e u hu, trR_phase P Bs e u hu, (hC Φ ρ).1, (hC Φ ρ).2]
  set g := trR P Bs e Φ ρ
  constructor
  · apply Subtype.ext
    funext q
    have hq : q.1.2 ∈ Ann P := q.2.2
    have e1 : ((dzQ P (fnZ P (fun ζ => star (u ρ ζ)) * g) : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q =
        NF.dZ (fun ζ => star (u ρ ζ)) q.1.2 * (g : MA.Qp P.r P.TT → ℂ) q +
          star (u ρ q.1.2) * MA.wirt M.vz (MA.ext (g : MA.Qp P.r P.TT → ℂ)) q.1 := by
      rw [dzQ_apply P hTT, wirtQ_mul, wirtinger_derivative_fibre_function P hc, fnZ_val P hc]
    simp only [MulMemClass.coe_mul, AddMemClass.coe_add, Pi.mul_apply, Pi.add_apply]
    rw [e1, dzQ_apply P hTT, fnZ_val P hc, fnZ_val P (hAB ρ).1, fnZ_val P (hSm ρ).1,
      (dZ_conj_unit P (hu ρ).1 (hu ρ).2 hq).1]
    ring
  · apply Subtype.ext
    funext q
    have hq : q.1.2 ∈ Ann P := q.2.2
    have e1 : ((dzbQ P (fnZ P (fun ζ => star (u ρ ζ)) * g) : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q =
        NF.dZb (fun ζ => star (u ρ ζ)) q.1.2 * (g : MA.Qp P.r P.TT → ℂ) q +
          star (u ρ q.1.2) * MA.wirt M.vzb (MA.ext (g : MA.Qp P.r P.TT → ℂ)) q.1 := by
      rw [dzbQ_apply P hTT, wirtQ_mul, wirt_fnZ_zb P hc, fnZ_val P hc]
    simp only [MulMemClass.coe_mul, AddMemClass.coe_add, NegMemClass.coe_neg, Pi.mul_apply,
      Pi.add_apply, Pi.neg_apply]
    rw [e1, dzbQ_apply P hTT, fnZ_val P hc, fnZ_val P (hAB ρ).2, fnZ_val P (hSm ρ).2,
      (dZ_conj_unit P (hu ρ).1 (hu ρ).2 hq).2]
    ring


end main

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section germ

variable {k r : ℕ} {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']

theorem deriv_const_smul_any (c : ℂ) (h : ℝ → E') (t : ℝ) :
    deriv (fun s => c • h s) t = c • deriv h t := by
  by_cases hc : c = 0
  · simp [hc]
  by_cases hd : DifferentiableAt ℝ h t
  · exact deriv_const_smul c hd
  · have hd' : ¬ DifferentiableAt ℝ (fun s => c • h s) t := by
      intro h'
      apply hd
      have e : h = fun s => c⁻¹ • (c • h s) := by
        funext s
        simp [smul_smul, inv_mul_cancel₀ hc]
      rw [e]
      exact h'.const_smul c⁻¹
    rw [deriv_zero_of_not_differentiableAt hd, deriv_zero_of_not_differentiableAt hd', smul_zero]

theorem rdV_smul (X : B.Mat k r) (c : ℂ) (f : B.Mat k r → E') :
    RdV X (c • f) = c • RdV X f := by
  funext g
  exact deriv_const_smul_any c (fun t => f (g * NormedSpace.exp ((t : ℂ) • X))) 0

theorem rw_smul (w : List (B.Mat k r)) (c : ℂ) (f : B.Mat k r → E') :
    B.Rw w (c • f) = c • B.Rw w f := by
  induction w with
  | nil => rfl
  | cons X w ih =>
    show RdV X (B.Rw w (c • f)) = c • RdV X (B.Rw w f)
    rw [ih, rdV_smul]

theorem rdV_local {X : B.Mat k r} (hX : B.inLie k r X) {U : Set (B.Mat k r)} (hU : IsOpen U)
    {f f' : B.Mat k r → E'} (he : ∀ x ∈ U, x ∈ B.GV k r → f x = f' x) {g : B.Mat k r} (hg : g ∈ U)
    (hgG : g ∈ B.GV k r) : RdV X f g = RdV X f' g := by
  show deriv (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) 0 =
    deriv (fun t : ℝ => f' (g * NormedSpace.exp ((t : ℂ) • X))) 0
  apply Filter.EventuallyEq.deriv_eq
  have hc : Continuous (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) :=
    (Formalism.FourierDecayAlt.P.B5.curve_contDiff g X).continuous
  have hev : ∀ᶠ t : ℝ in nhds (0 : ℝ), g * NormedSpace.exp (((t : ℝ) : ℂ) • X) ∈ U := by
    apply hc.continuousAt.preimage_mem_nhds
    show U ∈ nhds (g * NormedSpace.exp (((0 : ℝ) : ℂ) • X))
    rw [Formalism.FourierDecayAlt.P.B5.curve_zero]
    exact hU.mem_nhds hg
  filter_upwards [hev] with t ht
  exact he _ ht (Formalism.FourierDecayAlt.P.B5.curve_mem hgG hX t)

theorem rw_local (w : List (B.Mat k r)) (hw : ∀ X ∈ w, B.inLie k r X) {U : Set (B.Mat k r)} (hU : IsOpen U)
    {f f' : B.Mat k r → E'} (he : ∀ x ∈ U, x ∈ B.GV k r → f x = f' x) :
    ∀ x ∈ U, x ∈ B.GV k r → B.Rw w f x = B.Rw w f' x := by
  induction w with
  | nil => exact he
  | cons X w ih =>
    intro x hx hxG
    exact rdV_local (hw X (by simp)) hU (ih (fun Y hY => hw Y (by simp [hY]))) hx hxG

theorem sum_map_smul' {ι M : Type*} [AddCommMonoid M] [Module ℂ M] (c : ℂ) (l : List ι) (φ : ι → M) :
    (l.map fun i => c • φ i).sum = c • (l.map φ).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, smul_add]

end germ

theorem germ_operators_holds : GermOps := by
  intro k r Wp Wq _ _ _ _ _ Θ
  refine ⟨fun U f f' hU he g hg hgG => ⟨?_, ?_⟩, fun c f g => ⟨?_, ?_⟩⟩
  · unfold B.opApply
    congr 1
    apply List.map_congr_left
    intro T _
    rw [rw_local T.word T.word_lie hU he g hg hgG]
  · unfold B.opAdj
    congr 1
    apply List.map_congr_left
    intro T _
    rw [rw_local T.word.reverse (fun X hX => T.word_lie X (List.mem_reverse.1 hX)) hU
      (f := fun x => T.coefAdj x (f x)) (f' := fun x => T.coefAdj x (f' x))
      (fun x hx hxG => by simp only [he x hx hxG]) g hg hgG]
  · unfold B.opApply
    rw [← sum_map_smul']
    congr 1
    apply List.map_congr_left
    intro T _
    rw [rw_smul, Pi.smul_apply, map_smul]
  · unfold B.opAdj
    rw [← sum_map_smul']
    congr 1
    apply List.map_congr_left
    intro T _
    have e : (fun x => T.coefAdj x ((c • f) x)) = c • (fun x => T.coefAdj x (f x)) := by
      funext x; simp
    rw [e, rw_smul, Pi.smul_apply, smul_comm]

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS
end

section

open MeasureTheory Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra

section Ops

variable {k ρ : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]


variable (k ρ) in
def ParOK (T : (Q.Mx k ρ → E) → Q.Mx k ρ → E) : Prop :=
  ∀ (Par : Type) [NormedAddCommGroup Par] [NormedSpace ℝ Par] [FiniteDimensional ℝ Par] [MeasurableSpace Par]
    [BorelSpace Par] (U₀ : Set (Par × Mt k ρ)), IsOpen U₀ →
  ∀ f : Par → Q.Mx k ρ → E, PBI.ParFam k ρ U₀ (fun q => f q.1 (Matrix.of q.2)) →
    PBI.ParFam k ρ U₀ (fun q => T (f q.1) (Matrix.of q.2)) ∧
    (∀ q ∈ U₀, Matrix.of q.2 ∈ Q.Glev k ρ (Fin.last ρ) → ∀ W : Set (Par × Mt k ρ), IsOpen W → q ∈ W →
      (∀ q' ∈ W, Matrix.of q'.2 ∈ Q.Glev k ρ (Fin.last ρ) → f q'.1 (Matrix.of q'.2) = 0) →
      T (f q.1) (Matrix.of q.2) = 0) ∧
    ∀ (ν : Measure Par) [IsFiniteMeasure ν] (Kp : Set Par), IsCompact Kp → ν Kpᶜ = 0 →
    ∀ (fi : Q.Mx k ρ → E) (y : Mt k ρ) (V : Set (Mt k ρ)), IsOpen V → y ∈ V →
      Matrix.of y ∈ Q.Glev k ρ (Fin.last ρ) → Kp ×ˢ V ⊆ U₀ →
      (∀ y' ∈ V, Matrix.of y' ∈ Q.Glev k ρ (Fin.last ρ) → fi (Matrix.of y') = ∫ Z, f Z (Matrix.of y') ∂ν) →
      T fi (Matrix.of y) = ∫ Z, T (f Z) (Matrix.of y) ∂ν


variable (k ρ) in
def SmoothG (a : Q.Mx k ρ → ℂ) : Prop :=
  ∀ y₀ : Mt k ρ, Matrix.of y₀ ∈ Q.Glev k ρ (Fin.last ρ) → ∃ (U : Set (Mt k ρ)) (F : Mt k ρ → ℂ),
    IsOpen U ∧ y₀ ∈ U ∧ ContDiffOn ℝ ∞ F U ∧ ∀ y ∈ U, Matrix.of y ∈ Q.Glev k ρ (Fin.last ρ) → a (Matrix.of y) = F y

theorem smoothG_const (s : ℂ) : SmoothG k ρ (fun _ => s) := fun _ _ =>
  ⟨Set.univ, fun _ => s, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => rfl⟩

theorem smoothG_mul {a b : Q.Mx k ρ → ℂ} (ha : SmoothG k ρ a) (hb : SmoothG k ρ b) :
    SmoothG k ρ (fun g => a g * b g) := by
  intro y₀ hy
  obtain ⟨U, F, hU, hyU, hF, haF⟩ := ha y₀ hy
  obtain ⟨U', F', hU', hyU', hF', hbF⟩ := hb y₀ hy
  exact ⟨U ∩ U', fun y => F y * F' y, hU.inter hU', ⟨hyU, hyU'⟩,
    (hF.mono Set.inter_subset_left).mul (hF'.mono Set.inter_subset_right),
    fun y hy hG => by show a (Matrix.of y) * b (Matrix.of y) = F y * F' y; rw [haF y hy.1 hG, hbF y hy.2 hG]⟩

theorem smoothG_sub {a b : Q.Mx k ρ → ℂ} (ha : SmoothG k ρ a) (hb : SmoothG k ρ b) :
    SmoothG k ρ (fun g => a g - b g) := by
  intro y₀ hy
  obtain ⟨U, F, hU, hyU, hF, haF⟩ := ha y₀ hy
  obtain ⟨U', F', hU', hyU', hF', hbF⟩ := hb y₀ hy
  exact ⟨U ∩ U', fun y => F y - F' y, hU.inter hU', ⟨hyU, hyU'⟩,
    (hF.mono Set.inter_subset_left).sub (hF'.mono Set.inter_subset_right),
    fun y hy hG => by show a (Matrix.of y) - b (Matrix.of y) = F y - F' y; rw [haF y hy.1 hG, hbF y hy.2 hG]⟩

theorem parFam_congr {Par : Type} [NormedAddCommGroup Par] [NormedSpace ℝ Par] {U₀ : Set (Par × Mt k ρ)}
    {f g : Par × Mt k ρ → E} (hf : PBI.ParFam k ρ U₀ f)
    (h : ∀ q ∈ U₀, Matrix.of q.2 ∈ Q.Glev k ρ (Fin.last ρ) → f q = g q) (hU₀ : IsOpen U₀) :
    PBI.ParFam k ρ U₀ g := by
  intro q₀ hq hG
  obtain ⟨U, F, hU, hqU, hF, hfF⟩ := hf q₀ hq hG
  exact ⟨U ∩ U₀, F, hU.inter hU₀, ⟨hqU, hq⟩, hF.mono Set.inter_subset_left,
    fun q hq' hG' => (h q hq'.2 hG').symm.trans (hfF q hq'.1 hG')⟩

theorem parFam_smulG {Par : Type} [NormedAddCommGroup Par] [NormedSpace ℝ Par] {U₀ : Set (Par × Mt k ρ)}
    {a : Q.Mx k ρ → ℂ} (ha : SmoothG k ρ a) {f : Par × Mt k ρ → E} (hf : PBI.ParFam k ρ U₀ f) :
    PBI.ParFam k ρ U₀ (fun q => a (Matrix.of q.2) • f q) := by
  intro q₀ hq hG
  obtain ⟨U, F, hU, hqU, hF, hfF⟩ := hf q₀ hq hG
  obtain ⟨U', A, hU', hqU', hA, haA⟩ := ha q₀.2 hG
  refine ⟨U ∩ Prod.snd ⁻¹' U', fun q => A q.2 • F q, hU.inter (hU'.preimage continuous_snd), ⟨hqU, hqU'⟩, ?_,
    fun q hq' hG' => ?_⟩
  · exact (hA.comp contDiff_snd.contDiffOn (fun q (hq : q ∈ U ∩ Prod.snd ⁻¹' U') => hq.2)).smul (hF.mono Set.inter_subset_left)
  · show a (Matrix.of q.2) • f q = A q.2 • F q
    rw [haA q.2 hq'.2 hG', hfF q hq'.1 hG']

theorem parOK_id : ParOK k ρ (E := E) (fun f => f) := by
  intro Par _ _ _ _ _ U₀ _ f hf
  refine ⟨hf, fun q _ hG W _ hqW hW => hW q hqW hG, fun ν _ Kp _ _ fi y V _ hyV hyG _ hi => hi y hyV hyG⟩

theorem parOK_zero : ParOK k ρ (E := E) (fun _ _ => 0) := by
  intro Par _ _ _ _ _ U₀ _ f hf
  refine ⟨parFam_zero, fun _ _ _ _ _ _ _ => rfl, fun ν _ Kp _ _ fi y V _ _ _ _ _ => by simp⟩

theorem parOK_congr {T T' : (Q.Mx k ρ → E) → Q.Mx k ρ → E} (hT : ParOK k ρ T) (h : ∀ f g, T f g = T' f g) :
    ParOK k ρ T' := by
  have e : T = T' := funext fun f => funext fun g => h f g
  rw [← e]; exact hT

theorem parOK_add {T₁ T₂ : (Q.Mx k ρ → E) → Q.Mx k ρ → E} (h₁ : ParOK k ρ T₁) (h₂ : ParOK k ρ T₂) :
    ParOK k ρ (fun f g => T₁ f g + T₂ f g) := by
  intro Par _ _ _ _ _ U₀ hU₀ f hf
  obtain ⟨a₁, b₁, c₁⟩ := h₁ Par U₀ hU₀ f hf
  obtain ⟨a₂, b₂, c₂⟩ := h₂ Par U₀ hU₀ f hf
  refine ⟨parFam_add a₁ a₂, fun q hq hG W hW hqW hz => ?_, fun ν _ Kp hKp hν fi y V hV hyV hyG hKV hi => ?_⟩
  · show T₁ (f q.1) (Matrix.of q.2) + T₂ (f q.1) (Matrix.of q.2) = 0
    rw [b₁ q hq hG W hW hqW hz, b₂ q hq hG W hW hqW hz, add_zero]
  · have hKU : ∀ Z ∈ Kp, (Z, y) ∈ U₀ := fun Z hZ => hKV ⟨hZ, hyV⟩
    show T₁ fi (Matrix.of y) + T₂ fi (Matrix.of y) = ∫ Z, (T₁ (f Z) (Matrix.of y) + T₂ (f Z) (Matrix.of y)) ∂ν
    rw [c₁ ν Kp hKp hν fi y V hV hyV hyG hKV hi, c₂ ν Kp hKp hν fi y V hV hyV hyG hKV hi,
      integral_add (parFam_integrable a₁ hKp hν hyG hKU) (parFam_integrable a₂ hKp hν hyG hKU)]

theorem parOK_smulG {a : Q.Mx k ρ → ℂ} (ha : SmoothG k ρ a) {T : (Q.Mx k ρ → E) → Q.Mx k ρ → E}
    (hT : ParOK k ρ T) : ParOK k ρ (fun f g => a g • T f g) := by
  intro Par _ _ _ _ _ U₀ hU₀ f hf
  obtain ⟨a₁, b₁, c₁⟩ := hT Par U₀ hU₀ f hf
  refine ⟨parFam_smulG ha a₁, fun q hq hG W hW hqW hz => ?_, fun ν _ Kp hKp hν fi y V hV hyV hyG hKV hi => ?_⟩
  · show a (Matrix.of q.2) • T (f q.1) (Matrix.of q.2) = 0
    rw [b₁ q hq hG W hW hqW hz, smul_zero]
  · show a (Matrix.of y) • T fi (Matrix.of y) = ∫ Z, a (Matrix.of y) • T (f Z) (Matrix.of y) ∂ν
    rw [c₁ ν Kp hKp hν fi y V hV hyV hyG hKV hi, integral_smul]

theorem parOK_csmul (s : ℂ) {T : (Q.Mx k ρ → E) → Q.Mx k ρ → E} (hT : ParOK k ρ T) :
    ParOK k ρ (fun f g => s • T f g) := parOK_smulG (smoothG_const s) hT

theorem parOK_neg {T : (Q.Mx k ρ → E) → Q.Mx k ρ → E} (hT : ParOK k ρ T) : ParOK k ρ (fun f g => -T f g) :=
  parOK_congr (parOK_csmul (-1) hT) (fun f g => by simp)

theorem parOK_comp {T₁ T₂ : (Q.Mx k ρ → E) → Q.Mx k ρ → E} (h₁ : ParOK k ρ T₁) (h₂ : ParOK k ρ T₂) :
    ParOK k ρ (fun f => T₁ (T₂ f)) := by
  intro Par _ _ _ _ _ U₀ hU₀ f hf
  obtain ⟨a₂, b₂, c₂⟩ := h₂ Par U₀ hU₀ f hf
  obtain ⟨a₁, b₁, c₁⟩ := h₁ Par U₀ hU₀ (fun Z => T₂ (f Z)) a₂
  refine ⟨a₁, fun q hq hG W hW hqW hz => ?_, fun ν _ Kp hKp hν fi y V hV hyV hyG hKV hi => ?_⟩
  · refine b₁ q hq hG (W ∩ U₀) (hW.inter hU₀) ⟨hqW, hq⟩ (fun q' hq' hG' => ?_)
    exact b₂ q' hq'.2 hG' W hW hq'.1 hz
  · refine c₁ ν Kp hKp hν (T₂ fi) y V hV hyV hyG hKV (fun y' hy' hG' => ?_)
    exact c₂ ν Kp hKp hν fi y' V hV hy' hG' hKV hi

theorem parOK_sum {ι : Type} (s : Finset ι) {T : ι → (Q.Mx k ρ → E) → Q.Mx k ρ → E}
    (h : ∀ i ∈ s, ParOK k ρ (T i)) : ParOK k ρ (fun f g => ∑ i ∈ s, T i f g) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact parOK_congr parOK_zero (fun f g => by simp)
  | insert a s ha ih =>
    have := parOK_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    exact parOK_congr this (fun f g => by simp [Finset.sum_insert ha])

theorem parOK_foldr (L : List ((Q.Mx k ρ → E) → Q.Mx k ρ → E)) (hL : ∀ T ∈ L, ParOK k ρ T) :
    ParOK k ρ (fun f => L.foldr (fun T h => T h) f) := by
  induction L with
  | nil => exact parOK_id
  | cons T L ih =>
    exact parOK_comp (hL T List.mem_cons_self) (ih fun T' hT' => hL T' (List.mem_cons_of_mem _ hT'))

end Ops

end Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra
end
end

section

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants

noncomputable section

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem amaps_id (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b : ℝ) :
    Amaps p f (fun _ => ContinuousLinearMap.id ℂ Wq) (fun _ => ContinuousLinearMap.id ℂ Wq)
      (fun _ => ContinuousLinearMap.id ℂ Wq) (fun _ => ContinuousLinearMap.id ℂ Wq) b 0 := by
  refine ⟨fun γ _ _ => by simp, fun γ _ _ => by simp, fun γ _ _ v => ?_, fun γ _ _ => ?_, fun γ _ _ => ?_⟩
  · simp only [mul_zero, pow_zero, one_mul, ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_apply]
    nlinarith [sq_nonneg ‖v‖]
  · rw [pow_zero]
    exact pow_le_one₀ (norm_nonneg _) ContinuousLinearMap.norm_id_le
  · rw [pow_zero]
    exact pow_le_one₀ (norm_nonneg _) ContinuousLinearMap.norm_id_le

end place


end

end Formalism.FourierDecayAlt.P.CutBP
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def ZJ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (k r N : ℕ) (f : Q.Mx k r → E) (g₀ : Q.Mx k r) : Prop :=
  ∃ (U : Set (Q.Mx k r)) (F : Q.Mx k r → E), IsOpen U ∧ g₀ ∈ U ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F U ∧
    (∀ g ∈ U, g ∈ Q.Glev k r (Fin.last r) → f g = F g) ∧ ∀ j ≤ N, iteratedFDeriv ℝ j F g₀ = 0

def GTCLRJetT : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ)
    (a b : Fin 2), ∃ N : ℕ, ∀ (f : Q.Mx k r → E) (g₀ : Q.Mx k r), g₀ ∈ Q.Glev k r (Fin.last r) →
      ZJ k r N f g₀ → Q.tL k r z z' (Fin.last r) Y a b f g₀ = 0

def GTCLRJetRad : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k →
    ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (q : (Fin P.r → ℂ) × ℂ), q ∈ NF.QR P.k P.r Bs.z Bs.z' →
    ∀ N : ℕ, (∀ j ≤ N, iteratedFDeriv ℝ j
        (fun ζ => NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (q.1, ζ)) q.2 = 0) →
      ZJ P.k P.r N ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1) (NF.muZ P.k P.r Bs.μsec q.2)

def GTCLRTaylor : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (ψ : ℂ → V) (U : Set ℂ) (ζ₀ : ℂ) (N : ℕ),
    IsOpen U → ζ₀ ∈ U → ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ U →
    ∀ i ≤ N, iteratedFDeriv ℝ i (fun ζ => ψ ζ - ∑ j ∈ Finset.range (N + 1),
        ((j.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ j ψ ζ₀ (fun _ => ζ - ζ₀)) ζ₀ = 0

def GTCLRadTOfCut : Prop := GTCLRJetT → GTCLRJetRad → GTCLRTaylor → GTCLRadT

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end
