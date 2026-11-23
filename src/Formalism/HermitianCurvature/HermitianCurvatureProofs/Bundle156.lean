module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle144
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle146
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BaseIndexConstantInjective
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

open Matrix Filter Topology
open scoped ComplexConjugate ContDiff

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Formalism.FourierDecayAlt.P.WirtingerOperators

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {j : ℕ}

theorem cont_ofSnd : Continuous fun q : ℂ × (Fin j → Fin j → ℂ) => (Matrix.of q.2 : MJ j) := continuous_snd

theorem contDiff_ofSnd : ContDiff ℝ ∞ fun q : ℂ × (Fin j → Fin j → ℂ) => (Matrix.of q.2 : MJ j) := contDiff_snd

theorem contDiff_pair (τ : ℂ) : ContDiff ℝ ∞ fun Z : MJ j => ((τ, (Z : Fin j → Fin j → ℂ)) : ℂ × (Fin j → Fin j → ℂ)) :=
  contDiff_const.prodMk contDiff_id

theorem isOpen_inv : IsOpen {Z : MJ j | Z.det ≠ 0} :=
  isOpen_ne_fun (Continuous.matrix_det continuous_id) continuous_const

theorem diffAt_fst {G : ℂ × (Fin j → Fin j → ℂ) → E} {U : Set (ℂ × (Fin j → Fin j → ℂ))} (hU : IsOpen U)
    (hG : ContDiffOn ℝ ∞ G U) {q : ℂ × (Fin j → Fin j → ℂ)} (hq : q ∈ U) :
    DifferentiableAt ℝ (fun τ : ℂ => G (τ, q.2)) q.1 := by
  have hd : DifferentiableAt ℝ G q := (hG.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hq)
  exact hd.comp q.1 ((differentiableAt_id).prodMk (differentiableAt_const _))

theorem dz_add {F G : ℂ → E} {τ : ℂ} (hF : DifferentiableAt ℝ F τ) (hG : DifferentiableAt ℝ G τ) :
    PBP.dz (fun s => F s + G s) τ = PBP.dz F τ + PBP.dz G τ := by
  unfold PBP.dz
  rw [show (fun s => F s + G s) = F + G from rfl, (hF.hasFDerivAt.add hG.hasFDerivAt).fderiv]
  simp only [_root_.add_apply]
  module

theorem dzb_add {F G : ℂ → E} {τ : ℂ} (hF : DifferentiableAt ℝ F τ) (hG : DifferentiableAt ℝ G τ) :
    PBP.dzb (fun s => F s + G s) τ = PBP.dzb F τ + PBP.dzb G τ := by
  unfold PBP.dzb
  rw [show (fun s => F s + G s) = F + G from rfl, (hF.hasFDerivAt.add hG.hasFDerivAt).fderiv]
  simp only [_root_.add_apply]
  module

theorem dz_smul {F : ℂ → E} {τ : ℂ} (hF : DifferentiableAt ℝ F τ) (c : ℂ) :
    PBP.dz (fun s => c • F s) τ = c • PBP.dz F τ := by
  unfold PBP.dz
  rw [show (fun s => c • F s) = c • F from rfl, (hF.hasFDerivAt.const_smul c).fderiv]
  simp only [_root_.smul_apply]
  module

theorem dzb_smul {F : ℂ → E} {τ : ℂ} (hF : DifferentiableAt ℝ F τ) (c : ℂ) :
    PBP.dzb (fun s => c • F s) τ = c • PBP.dzb F τ := by
  unfold PBP.dzb
  rw [show (fun s => c • F s) = c • F from rfl, (hF.hasFDerivAt.const_smul c).fderiv]
  simp only [_root_.smul_apply]
  module

theorem dz_const (v : E) (τ : ℂ) : PBP.dz (fun _ : ℂ => v) τ = 0 := by simp [PBP.dz]

theorem dzb_const (v : E) (τ : ℂ) : PBP.dzb (fun _ : ℂ => v) τ = 0 := by simp [PBP.dzb]

theorem zop_id : ZOp (E := E) (j := j) (fun h => h) := by
  refine ⟨fun h₁ h₂ Z h => h.eq_of_nhds, fun _ _ _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ _ => rfl, ?_⟩
  intro U κ _ _ hκ
  exact ⟨hκ, fun q _ => ⟨rfl, rfl⟩⟩

theorem zop_zero : ZOp (E := E) (j := j) (fun _ _ => 0) := by
  refine ⟨fun _ _ _ _ => rfl, fun _ _ _ _ _ _ _ _ _ => by simp, fun _ _ _ _ _ _ _ _ => by simp, ?_⟩
  intro U κ _ _ _
  exact ⟨contDiffOn_const, fun q _ => ⟨dz_const _ _, dzb_const _ _⟩⟩

theorem ZOp.smooth {T : (MJ j → E) → MJ j → E} (hT : ZOp T) {V : Set (MJ j)} (hV : IsOpen V)
    (hVi : V ⊆ {Z | Z.det ≠ 0}) {h : MJ j → E} (hh : ContDiffOn ℝ ∞ h V) : ContDiffOn ℝ ∞ (T h) V := by
  let U : Set (ℂ × (Fin j → Fin j → ℂ)) := {q | (Matrix.of q.2 : MJ j) ∈ V}
  have hU : IsOpen U := hV.preimage cont_ofSnd
  have hUi : U ⊆ {q | (Matrix.of q.2).det ≠ 0} := fun q hq => hVi hq
  have hκ : ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) => (fun _ : ℂ => h) q.1 (Matrix.of q.2)) U :=
    hh.comp contDiff_ofSnd.contDiffOn (fun q hq => hq)
  have h1 := (hT.par U (fun _ => h) hU hUi hκ).1
  exact h1.comp (contDiff_pair 0).contDiffOn (fun Z hZ => hZ)

theorem ZOp.add' {T S : (MJ j → E) → MJ j → E} (hT : ZOp T) (hS : ZOp S) :
    ZOp (fun h Z => T h Z + S h Z) := by
  refine ⟨fun h₁ h₂ Z h => by rw [hT.loc _ _ Z h, hS.loc _ _ Z h], ?_, ?_, ?_⟩
  · intro V h₁ h₂ hV hVi s₁ s₂ Z hZ
    rw [hT.add V h₁ h₂ hV hVi s₁ s₂ Z hZ, hS.add V h₁ h₂ hV hVi s₁ s₂ Z hZ]; abel
  · intro V c h hV hVi s Z hZ
    rw [hT.smul V c h hV hVi s Z hZ, hS.smul V c h hV hVi s Z hZ, smul_add]
  · intro U κ hU hUi hκ
    obtain ⟨t1, t2⟩ := hT.par U κ hU hUi hκ
    obtain ⟨s1, s2⟩ := hS.par U κ hU hUi hκ
    refine ⟨t1.add s1, fun q hq => ?_⟩
    have d1 := diffAt_fst hU t1 hq
    have d2 := diffAt_fst hU s1 hq
    refine ⟨?_, ?_⟩
    · rw [dz_add d1 d2, (t2 q hq).1, (s2 q hq).1]
    · rw [dzb_add d1 d2, (t2 q hq).2, (s2 q hq).2]

theorem ZOp.cmul {T : (MJ j → E) → MJ j → E} (hT : ZOp T) {c : MJ j → ℂ}
    (hc : ContDiffOn ℝ ∞ c {Z | Z.det ≠ 0}) : ZOp (fun h Z => c Z • T h Z) := by
  refine ⟨fun h₁ h₂ Z h => by rw [hT.loc _ _ Z h], ?_, ?_, ?_⟩
  · intro V h₁ h₂ hV hVi s₁ s₂ Z hZ
    rw [hT.add V h₁ h₂ hV hVi s₁ s₂ Z hZ, smul_add]
  · intro V c' h hV hVi s Z hZ
    rw [hT.smul V c' h hV hVi s Z hZ, smul_comm]
  · intro U κ hU hUi hκ
    obtain ⟨t1, t2⟩ := hT.par U κ hU hUi hκ
    have hc' : ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) => c (Matrix.of q.2)) U :=
      hc.comp contDiff_ofSnd.contDiffOn (fun q hq => hUi hq)
    refine ⟨hc'.smul t1, fun q hq => ?_⟩
    have d1 := diffAt_fst hU t1 hq
    exact ⟨by rw [dz_smul d1, (t2 q hq).1], by rw [dzb_smul d1, (t2 q hq).2]⟩

theorem ZOp.csmul {T : (MJ j → E) → MJ j → E} (hT : ZOp T) (c : ℂ) : ZOp (fun h Z => c • T h Z) :=
  hT.cmul (c := fun _ => c) contDiffOn_const

theorem ZOp.comp {T S : (MJ j → E) → MJ j → E} (hT : ZOp T) (hS : ZOp S) : ZOp (fun h => T (S h)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h₁ h₂ Z h
    apply hT.loc
    filter_upwards [h.eventually_nhds] with Z' hZ'
    exact hS.loc _ _ Z' hZ'
  · intro V h₁ h₂ hV hVi s₁ s₂ Z hZ
    have e : S (h₁ + h₂) =ᶠ[𝓝 Z] S h₁ + S h₂ := by
      filter_upwards [hV.mem_nhds hZ] with Z' hZ'
      exact hS.add V h₁ h₂ hV hVi s₁ s₂ Z' hZ'
    rw [hT.loc _ _ Z e]
    exact hT.add V (S h₁) (S h₂) hV hVi (hS.smooth hV hVi s₁) (hS.smooth hV hVi s₂) Z hZ
  · intro V c h hV hVi s Z hZ
    have e : S (c • h) =ᶠ[𝓝 Z] c • S h := by
      filter_upwards [hV.mem_nhds hZ] with Z' hZ'
      exact hS.smul V c h hV hVi s Z' hZ'
    rw [hT.loc _ _ Z e]
    exact hT.smul V c (S h) hV hVi (hS.smooth hV hVi s) Z hZ
  · intro U κ hU hUi hκ
    obtain ⟨s1, s2⟩ := hS.par U κ hU hUi hκ
    obtain ⟨t1, t2⟩ := hT.par U (fun τ => S (κ τ)) hU hUi s1
    refine ⟨t1, fun q hq => ?_⟩
    have hsl : IsOpen {Z : MJ j | ((q.1, (Z : Fin j → Fin j → ℂ)) : ℂ × (Fin j → Fin j → ℂ)) ∈ U} :=
      hU.preimage (contDiff_pair q.1).continuous
    have e1 : (fun Z => PBP.dz (fun τ => S (κ τ) Z) q.1) =ᶠ[𝓝 (Matrix.of q.2)]
        S (fun Z => PBP.dz (fun τ => κ τ Z) q.1) := by
      filter_upwards [hsl.mem_nhds (show (q.1, q.2) ∈ U from hq)] with Z hZ
      exact (s2 (q.1, (Z : Fin j → Fin j → ℂ)) hZ).1
    have e2 : (fun Z => PBP.dzb (fun τ => S (κ τ) Z) q.1) =ᶠ[𝓝 (Matrix.of q.2)]
        S (fun Z => PBP.dzb (fun τ => κ τ Z) q.1) := by
      filter_upwards [hsl.mem_nhds (show (q.1, q.2) ∈ U from hq)] with Z hZ
      exact (s2 (q.1, (Z : Fin j → Fin j → ℂ)) hZ).2
    exact ⟨by rw [(t2 q hq).1, hT.loc _ _ _ e1], by rw [(t2 q hq).2, hT.loc _ _ _ e2]⟩

theorem zop_sum {ι : Type*} (s : Finset ι) {T : ι → (MJ j → E) → MJ j → E} (hT : ∀ i ∈ s, ZOp (T i)) :
    ZOp (fun h Z => ∑ i ∈ s, T i h Z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zop_zero (E := E) (j := j))
  | insert a s ha ih =>
    have h1 := (hT a (by simp)).add' (ih (fun i hi => hT i (by simp [hi])))
    simpa [Finset.sum_insert ha] using h1

theorem zop_foldr : ∀ L : List ((MJ j → E) → MJ j → E), (∀ T ∈ L, ZOp T) →
    ZOp (fun f => L.foldr (fun T h => T h) f)
  | [], _ => zop_id
  | T :: L, h => by
    simp only [List.foldr_cons]
    exact (h T (by simp)).comp (zop_foldr L (fun T' hT' => h T' (by simp [hT'])))

end Formalism.FourierDecayAlt.P.WirtingerOperators
end
end

section

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutHLMZ

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates Formalism.FourierDecayAlt.P.CutHL

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem dmin_zero (z z' : Fin (2 * r + k + 1) → ℂ) (g : Q.Mx k r) (h : 0 < r + 2) :
    Dmin k r z z' g ⟨0, h⟩ = 1 := by
  unfold Dmin
  exact Matrix.det_isEmpty

theorem qminorOp_zero (a b : Fin 0 → Fin (2 * r + k + 1)) (u : ℂ) (f : Q.Mx k r → E) (g : Q.Mx k r) :
    qminorOp (EabH (Hpk k r)) a b u f g = f g := by
  unfold qminorOp
  rw [Finset.sum_apply, Fintype.sum_unique]
  simp

theorem AAvop_zero (h : 0 ≤ r) (ell : ℂ) (f : Q.Mx k r → E) (g : Q.Mx k r) : C3.AAvop k r 0 h ell f g = f g := by
  unfold C3.AAvop
  rw [Fintype.sum_unique, if_pos (Subsingleton.strictMono _), Matrix.det_isEmpty, one_smul, qminorOp_zero]

theorem qminorOp_one (a b : Fin 1 → Fin (2 * r + k + 1)) (u : ℂ) (f : Q.Mx k r → E) (g : Q.Mx k r) :
    qminorOp (EabH (Hpk k r)) a b u f g =
      (if a 0 = b 0 then u • f g else 0) + EabH (Hpk k r) (a 0) (b 0) f g := by
  unfold qminorOp
  rw [Finset.sum_apply, Fintype.sum_unique]
  simp [QuantumDeterminants.Top]

theorem AAvop_one (h : 1 ≤ r) (x : Q.Mx k r) (w : ℂ)
    (hnf : ∀ p : Fin (2 * r + k + 1), PBG.y0 x ⟨0, by omega⟩ p = if p.val = 2 * r + k then w else 0)
    (ell : ℂ) (f : Q.Mx k r → E) :
    C3.AAvop k r 1 h ell f x =
      w • (ell • f x + Q.EH k r (esI k r ⟨0, by omega⟩) (esI k r ⟨0, by omega⟩) f x) := by
  classical
  unfold C3.AAvop
  have hent : ∀ c : Fin 1 → Fin (2 * r + k + 1),
      (Matrix.of fun a l : Fin 1 => (x⁻¹ *ᵥ bvec (eI k r (Fin.castLE h a))) (c l)).det =
        if (c 0).val = 2 * r + k then w else 0 := by
    intro c
    rw [Matrix.det_unique]
    exact hnf (c 0)
  rw [Finset.sum_eq_single (fun _ => esI k r ⟨0, by omega⟩)]
  · rw [if_pos (Subsingleton.strictMono _), hent, if_pos (by simp [esI]),
      qminorOp_one, if_pos (by simp [C3.sR, esI])]
    simp only [C3.sR, Q.EH] at *
    rw [show ell + ((1 : ℕ) : ℂ) - 1 = ell by push_cast; ring]
    rfl
  · intro c _ hc
    split_ifs with hm
    · rw [hent, if_neg, zero_smul]
      intro h0
      apply hc
      funext l
      rw [Subsingleton.elim l 0]
      ext
      simpa [esI] using h0
    · rfl
  · intro hc; exact absurd (Finset.mem_univ _) hc

end Formalism.FourierDecayAlt.P.CutHLMZ

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates Formalism.FourierDecayAlt.P.CutHL Formalism.FourierDecayAlt.P.CutHLMZ

theorem minus_zero_of_parts : CutHL.MinusZeroOfParts := by
  intro hNf hDm hT k r j hj z z' E _ _ Dm Φ Z γ τ hj0 hH Y
  subst hj0
  obtain ⟨_, _, hDo, _, hR, hZ, hτ, hγ, hx⟩ := hH
  have hnfy := (hNf k r 0 hj Z τ γ hZ hτ hγ).2
  have hT' := hT E k r 0 hj Dm Φ Z τ γ hDo hR.1 hZ hτ hγ hx
  have hD1 := (hDm k r 0 hj z z' Z τ γ hZ hτ hγ).2
  rw [Matrix.det_isEmpty, one_mul] at hD1
  have hτc : conj τ ≠ 0 := (map_ne_zero _).2 hτ
  have hv0 : ∀ g, D.vLet k r z z' 0 (by omega) (false, Y) 0 Φ g = Φ g := by
    intro g
    rw [PBG.letter_minus_component_zero, dmin_zero, map_one, inv_one, one_smul, AAvop_zero]
  have hv1 : ∀ g, D.vLet k r z z' 0 (by omega) (false, Y) 1 Φ g = 0 := by
    intro g
    unfold D.vLet
    simp
  have hA := AAvop_one (k := k) (r := r) (E := E) hj (x0 k r 0 hj Z τ γ) (conj τ) (fun p => by
      rw [hnfy ⟨0, by omega⟩ p (by simp)]
      have hp := p.isLt
      by_cases hq : p.val = 2 * r + k
      · rw [if_pos (by omega), if_pos hq, hq, Nat.sub_self]; simp [C3.Zb]
      · rw [if_neg (by omega), if_neg hq])
    ((Y : ℂ) - ((2 * r + k : ℕ) : ℂ) / 2) Φ
  have hu : ((Y : ℂ) - ((2 * r + k : ℕ) : ℂ) / 2) = (Y : ℂ) - levelZeroKernel k r 0 := by
    unfold levelZeroKernel; rw [Nat.sub_zero]; push_cast; ring
  rw [hu] at hA
  unfold Eq3
  simp only [hv0, hv1]
  rw [PBG.letter_minus_component_zero, hD1, hu, hA, smul_smul, inv_mul_cancel₀ hτc, one_smul, smul_zero, sub_zero, sub_eq_add_neg _ (conj τ • _),
    ← hT']

end Formalism.FourierDecayAlt.P
end
end

section

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutHLPZ

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates Formalism.FourierDecayAlt.P.CutHL

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem dmin_zero (z z' : Fin (2 * r + k + 1) → ℂ) (g : Q.Mx k r) (h : 0 < r + 2) :
    Dmin k r z z' g ⟨0, h⟩ = 1 := by
  unfold Dmin
  exact Matrix.det_isEmpty

theorem qminorOp_zero (a b : Fin 0 → Fin (2 * r + k + 1)) (u : ℂ) (f : Q.Mx k r → E) (g : Q.Mx k r) :
    qminorOp (EabH (Hpk k r)) a b u f g = f g := by
  unfold qminorOp
  rw [Finset.sum_apply, Fintype.sum_unique]
  simp

theorem AAop_zero (h : 0 ≤ r) (u : ℂ) (f : Q.Mx k r → E) (g : Q.Mx k r) : C3.AAop k r 0 h u f g = f g := by
  unfold C3.AAop
  rw [Fintype.sum_unique, if_pos (Subsingleton.strictMono _), Matrix.det_isEmpty, one_smul, qminorOp_zero]

theorem qminorOp_one (a b : Fin 1 → Fin (2 * r + k + 1)) (u : ℂ) (f : Q.Mx k r → E) (g : Q.Mx k r) :
    qminorOp (EabH (Hpk k r)) a b u f g =
      (if a 0 = b 0 then u • f g else 0) + EabH (Hpk k r) (a 0) (b 0) f g := by
  unfold qminorOp
  rw [Finset.sum_apply, Fintype.sum_unique]
  simp [QuantumDeterminants.Top]

theorem AAop_one (h : 1 ≤ r) (x : Q.Mx k r) (τ : ℂ)
    (hnf : ∀ p : Fin (2 * r + k + 1), PBG.xi0 x ⟨0, by omega⟩ p = if p.val = 0 then τ else 0)
    (u : ℂ) (f : Q.Mx k r → E) :
    C3.AAop k r 1 h u f x = τ • (u • f x + Q.EH k r (eI k r ⟨0, by omega⟩) (eI k r ⟨0, by omega⟩) f x) := by
  classical
  unfold C3.AAop
  have hent : ∀ c : Fin 1 → Fin (2 * r + k + 1),
      (Matrix.of fun a l : Fin 1 =>
        herm (Hpk k r) (x *ᵥ bvec (c l)) (bvec (eI k r (Fin.castLE h a)))).det =
        if (c 0).val = 0 then τ else 0 := by
    intro c
    rw [Matrix.det_unique]
    exact hnf (c 0)
  rw [Finset.sum_eq_single (fun _ => eI k r ⟨0, by omega⟩)]
  · rw [if_pos (Subsingleton.strictMono _), hent, if_pos (by simp [eI]),
      qminorOp_one, if_pos (by simp [C3.xR, eI])]
    simp [C3.xR, eI, Q.EH]
  · intro c _ hc
    split_ifs with hm
    · rw [hent, if_neg, zero_smul]
      intro h0
      apply hc
      funext l
      rw [Subsingleton.elim l 0]
      ext
      simpa [eI] using h0
    · rfl
  · intro hc; exact absurd (Finset.mem_univ _) hc

end Formalism.FourierDecayAlt.P.CutHLPZ

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates Formalism.FourierDecayAlt.P.CutHL Formalism.FourierDecayAlt.P.CutHLPZ

theorem plus_zero_of_parts : CutHL.PlusZeroOfParts := by
  intro hNf hDm hT k r j hj z z' E _ _ Dm Φ Z γ τ hj0 hH Y
  subst hj0
  obtain ⟨_, _, hDo, _, hR, hZ, hτ, hγ, hx⟩ := hH
  have hnf := (hNf k r 0 hj Z τ γ hZ hτ hγ).1
  have hT' := hT E k r 0 hj Dm Φ Z τ γ hDo hR.1 hZ hτ hγ hx
  have hD1 := (hDm k r 0 hj z z' Z τ γ hZ hτ hγ).2
  rw [Matrix.det_isEmpty, one_mul] at hD1
  have hv0 : ∀ g, D.vLet k r z z' 0 (by omega) (true, Y) 0 Φ g = Φ g := by
    intro g
    rw [PBG.letter_plus_component_zero, dmin_zero, inv_one, one_smul, AAop_zero]
  have hv1 : ∀ g, D.vLet k r z z' 0 (by omega) (true, Y) 1 Φ g = 0 := by
    intro g
    unfold D.vLet
    simp
  have hA := AAop_one (k := k) (r := r) (E := E) hj (x0 k r 0 hj Z τ γ) τ (fun p => by
      rw [hnf ⟨0, by omega⟩ p (by simp)]
      by_cases hp : p.val = 0
      · rw [if_pos (by omega), if_pos hp, hp]; simp [C3.Zb]
      · rw [if_neg (by omega), if_neg hp])
    ((Y : ℂ) + ((2 * r + k : ℕ) : ℂ) / 2) Φ
  have hu : ((Y : ℂ) + ((2 * r + k : ℕ) : ℂ) / 2) = (Y : ℂ) + levelZeroKernel k r 0 := by
    unfold levelZeroKernel; rw [Nat.sub_zero]; push_cast; ring
  rw [hu] at hA
  unfold Eq1
  simp only [hv0, hv1]
  rw [PBG.letter_plus_component_zero, hD1, hu, hA, ← hT', smul_smul, inv_mul_cancel₀ hτ, one_smul, smul_zero, sub_zero]

end Formalism.FourierDecayAlt.P
end
end
