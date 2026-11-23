module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

noncomputable section

open NumberField Matrix MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL

namespace UpperTheory.V.Lit.Geo

def OneStep : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a)
    (Y : GA E a → Herm E a) (C : ℝ), IsFld U Y C → ∀ q : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ η : Co Ξ q, IsLev U Ξ η →
      ∃ η' : Co Ξ q, IsLev U Ξ η' ∧ dCo (smLie Ξ) η' = dCo (smLie Ξ) η ∧ ∀ (g : GA E a) (M M' : ℝ), 0 ≤ M → 0 ≤ M' →
        (∀ h : GL (Fin a) (Cinf E), h.val * star h.val = 1 + (Y g).1 → Bd η (g * infGL E a h) M) →
        (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ h : GL (Fin a) (Cinf E), h.val * star h.val = 1 + t • (Y g).1 →
          Bd (Ξ := Ξ) (dCo (smLie Ξ) η) (g * infGL E a h) M') → Bd η' g (B * (M + M'))

def BdBasis : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (q : ℕ),
    ∃ (T : Finset (Fin q → Herm E a)) (B : ℝ), 0 ≤ B ∧ ∀ (α : Co Ξ q) (g : GA E a) (M : ℝ), 0 ≤ M →
      (∀ X ∈ T, ‖ev (α X) (GroundTheory.Automorphic.CuspidalSpectrum.retractOne g : KernelIndexFullLattice.G1 E a).1‖ ≤ M) → Bd α g (B * M)

def BdCompact : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (U : Subgroup (GL (Fin a) (Af E))),
    IsOpen (U : Set (GL (Fin a) (Af E))) → ∀ (Ξ : AlgRep E a) (q : ℕ) (α : Co Ξ q), IsLev U Ξ α → ∀ R : ℝ,
      ∃ M : ℝ, 0 ≤ M ∧ ∀ g : GA E a, qht g ≤ R → Bd α g M

def BdGrowth : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (q : ℕ) (α : Co Ξ q),
    (Moderate α → ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ g : GA E a, Bd α g (C * qht g ^ N)) ∧
    (Rapid α → ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ g : GA E a, Bd α g (C / qht g ^ N))

def Prim : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (U : Subgroup (GL (Fin a) (Af E))),
    IsOpen (U : Set (GL (Fin a) (Af E))) → ∀ (Ξ : AlgRep E a) (f : GA E a → ℝ) (Y : GA E a → Herm E a) (C c f₀ : ℝ),
    IsStep U f Y C c f₀ → ∀ (q : ℕ) (η : Co Ξ q), IsLev U Ξ η → Moderate (Ξ := Ξ) (dCo (smLie Ξ) η) →
      ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ, ∃ η' : Co Ξ q, IsLev U Ξ η' ∧ dCo (smLie Ξ) η' = dCo (smLie Ξ) η ∧
        ∀ g : GA E a, f g ≤ n * c → Bd η' g (Real.exp (D * (n + 1)))

def CutBd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (q : ℕ) (u : Sm E a) (η ζ : Co Ξ q),
    (∀ (X : Fin (q + 1) → Herm E a) g, ev (dCo (smLie Ξ) ζ X) g = u.1 g • ev (dCo (smLie Ξ) η X) g +
      ∑ i : Fin (q + 1), ((-1 : ℂ) ^ (i : ℕ) * (lie E a (toL (X i).1) u).1 g) • ev (η (i.removeNth X)) g) →
    ∀ (g : GA E a) (s b M M' : ℝ), 0 ≤ M → 0 ≤ M' → 0 ≤ b →
      ‖1 - u.1 (GroundTheory.Automorphic.CuspidalSpectrum.retractOne g : KernelIndexFullLattice.G1 E a).1‖ ≤ s →
      (∀ X, ‖(lie E a X u).1 (GroundTheory.Automorphic.CuspidalSpectrum.retractOne g : KernelIndexFullLattice.G1 E a).1‖ ≤ b * ‖X‖) →
      (b = 0 ∨ Bd η g M) → Bd (Ξ := Ξ) (dCo (smLie Ξ) η) g M' →
      Bd (Ξ := Ξ) (dCo (smLie Ξ) η - dCo (smLie Ξ) ζ) g (s * M' + (q + 1) * b * M)

def Approx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ U : Subgroup (GL (Fin a) (Af E)),
    IsOpen (U : Set (GL (Fin a) (Af E))) → IsCompact (U : Set (GL (Fin a) (Af E))) → ∀ (Ξ : AlgRep E a) (q : ℕ) (η : Co Ξ q),
    IsLev U Ξ η → Moderate (Ξ := Ξ) (dCo (smLie Ξ) η) → ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ R : ℝ, ∃ ζ : Co Ξ q, IsLev U Ξ ζ ∧
      CSupp ζ ∧ CSupp (Ξ := Ξ) (dCo (smLie Ξ) ζ) ∧ ∀ g : GA E a,
        (qht g ≤ R → Bd (Ξ := Ξ) (dCo (smLie Ξ) η - dCo (smLie Ξ) ζ) g 0) ∧
        Bd (Ξ := Ξ) (dCo (smLie Ξ) η - dCo (smLie Ξ) ζ) g (C * qht g ^ N)

def PtRetr : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (U : Subgroup (GL (Fin a) (Af E))),
    IsOpen (U : Set (GL (Fin a) (Af E))) → ∀ (Ξ : AlgRep E a) (r : ℝ) (χ : HChar E) (G : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) (n : ℕ) (e : Fin n → Herm E a),
    IsData Ξ r χ G e → ∀ (q : ℕ) (α β : Co Ξ q), IsLev U Ξ α → IsLev U Ξ β → ∀ g : GA E a,
      ptIp χ G e α β g = ∑ I : Fin q → Fin n,
        star (ev (α fun i => e (I i)) (GroundTheory.Automorphic.CuspidalSpectrum.retractOne g : KernelIndexFullLattice.G1 E a).1) ⬝ᵥ
          G *ᵥ ev (β fun i => e (I i)) (GroundTheory.Automorphic.CuspidalSpectrum.retractOne g : KernelIndexFullLattice.G1 E a).1

def PtBd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (U : Subgroup (GL (Fin a) (Af E))),
    IsOpen (U : Set (GL (Fin a) (Af E))) → ∀ (Ξ : AlgRep E a) (r : ℝ) (χ : HChar E) (G : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) (n : ℕ) (e : Fin n → Herm E a),
    IsData Ξ r χ G e → ∀ q : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ α β : Co Ξ q, IsLev U Ξ α → IsLev U Ξ β → ∀ (g : GA E a) (M M' : ℝ),
      0 ≤ M → 0 ≤ M' → Bd α g M → Bd β g M' → ‖ptIp χ G e α β g‖ ≤ B * M * M'

theorem ptIp_sub {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} {Ξ : AlgRep E a} {q : ℕ} (χ : HChar E)
    (G : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) {n : ℕ} (e : Fin n → Herm E a) (α β β' : Co Ξ q) (g : GA E a) :
    ptIp χ G e α (β - β') g = ptIp χ G e α β g - ptIp χ G e α β' g := by
  simp only [ptIp, AlternatingMap.sub_apply, map_sub, Pi.sub_apply, Matrix.mulVec_sub, dotProduct_sub,
    Finset.sum_sub_distrib, mul_sub]

theorem firstGeometricCondition_of_properties (h1 : PairFacts) (h2 : QhtFacts) (h3 : LevD) (h4 : BdGrowth) (h5 : Approx) (h6 : PtBd)
    (h7 : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure],
      IsFiniteMeasure (GlobalTheory.AutomorphicL2Unitary.quotMeasure (latticeGL E a) μ)) : G1 := by
  intro E _ _ _ a ha μ _ U hUo hUc Ξ r χ G n e hD q β η hβ hη hR hδ hM
  haveI := h7 E a μ
  obtain ⟨N, C, hC, hA⟩ := h5 E a ha U hUo hUc Ξ q η hη hM
  obtain ⟨C', hC', hB⟩ := (h4 E a Ξ (q + 1) β).2 hR (N + 1)
  obtain ⟨B, hB0, hP⟩ := h6 E a ha U hUo Ξ r χ G n e hD (q + 1)
  have hdη := (h3 E a U Ξ q η hη).1
  have hq := (h2 E a).1
  have key : ∀ R : ℝ, 0 < R → ‖pair μ χ G e β (dCo (smLie Ξ) η)‖ ≤
      B * C' * C * (GlobalTheory.AutomorphicL2Unitary.quotMeasure (latticeGL E a) μ).real Set.univ / R := fun R hR0 => by
    obtain ⟨ζ, hζ, hc, hc', hg⟩ := hA R
    have hdζ := (h3 E a U Ξ q ζ hζ).1
    have hγ := (h3 E a U Ξ (q + 1) _ hdη).2 _ hdζ
    have i1 := (h1 E a ha μ U hUo Ξ r χ G n e hD (q + 1)).1 β _ hβ hdη hR hM
    have i2 := ((h1 E a ha μ U hUo Ξ r χ G n e hD (q + 1)).2.1 _ β hdζ hβ hc').2
    have z : pair μ χ G e β (dCo (smLie Ξ) ζ) = 0 := by
      rw [(h1 E a ha μ U hUo Ξ r χ G n e hD q).2.2.2 β ζ hβ hζ (Or.inr hc), hδ]
      simp [pair, ptIp]
    have e1 : pair μ χ G e β (dCo (smLie Ξ) η) = pair μ χ G e β (dCo (smLie Ξ) η - dCo (smLie Ξ) ζ) := by
      rw [← sub_zero (pair μ χ G e β (dCo (smLie Ξ) η)), ← z]
      simp only [pair, ptIp_sub]
      exact (integral_sub i1 i2).symm
    rw [e1, mul_div_right_comm]
    refine norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun x => ?_)
    have q1 := hq x.out
    have q0 : 0 < qht x.out := one_pos.trans_le q1
    by_cases hx : qht x.out ≤ R
    · refine (hP β _ hβ hγ x.out _ 0 (by positivity) le_rfl (hB _) ((hg _).1 hx)).trans ?_
      rw [mul_zero]
      positivity
    · refine (hP β _ hβ hγ x.out _ _ (by positivity) (by positivity) (hB _) (hg _).2).trans ?_
      have e2 : B * (C' / qht x.out ^ (N + 1)) * (C * qht x.out ^ N) = B * C' * C / qht x.out := by
        field_simp
        ring
      rw [e2]
      exact div_le_div_of_nonneg_left (by positivity) hR0 (not_le.1 hx).le
  exact norm_le_zero_iff.1 (ge_of_tendsto (tendsto_const_nhds.div_atTop Filter.tendsto_id)
    ((Filter.eventually_gt_atTop 0).mono key))

end UpperTheory.V.Lit.Geo
end
end

section

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit.Dr
open UpperTheory.V.Lit.Geo

section

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private theorem sand_comp (g h : GL (Fin a) (Cinf E)) (v : HV E a) : sand g (sand h v) = sand (g * h) v := by
  rw [map_mul]; rfl

private theorem unitary_of_eq {g h : GL (Fin a) (Cinf E)} (e : sand g (hOne E a) = sand h (hOne E a)) :
    ∃ k : Kinf E a, h = g * Unitary.toUnits k := by
  have h1 : sand (g⁻¹ * h) (hOne E a) = hOne E a := by
    rw [← sand_comp, ← e, sand_comp, inv_mul_cancel, map_one]; rfl
  have h2 : (g⁻¹ * h).val * star (g⁻¹ * h).val = 1 := by
    have h3 := sand_val (g⁻¹ * h) (hOne E a)
    rw [h1, hOne_val, mul_one] at h3
    exact h3.symm
  refine ⟨⟨(g⁻¹ * h).val, Matrix.mem_unitaryGroup_iff.2 h2⟩, ?_⟩
  rw [← inv_mul_eq_iff_eq_mul]
  exact Units.ext rfl

private theorem hv_adHerm (k : Kinf E a) (X : Herm E a) : hv (adHerm k X) = sand (Unitary.toUnits k) (hv X) := rfl

end

theorem UpperTheory.V.Lit.Geo.fieldDef :
    FieldDef := by
  classical
  intro E _ _ _ a U Y C hY
  refine ⟨fun s p => if h : p ∈ cone E a then
    sand h.choose (hv (Y (infGL E a h.choose * finGL E a s.out))) else 0, fun g x => ?_⟩
  have hp : sand g (hOne E a) ∈ cone E a := ⟨g, rfl⟩
  obtain ⟨k, hk⟩ := unitary_of_eq hp.choose_spec.symm
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U x
  beta_reduce
  rw [dite_eq_left hp, hk, hu, map_mul (finGL E a), ← mul_assoc, hY.lev _ u.2, ← sand_comp, ← hv_adHerm,
    map_mul (infGL E a), mul_assoc, infGL_comm, ← mul_assoc, hY.cpt]
end
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open UpperTheory.V.Lit.Geo
open scoped TensorProduct

private theorem span_val {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a d : ℕ} (P : Sm E a → Prop)
    (x y : GA E a) (c : ℂ) (h : ∀ φ, P φ → φ.1 x = c * φ.1 y) (m : Sm E a ⊗[ℂ] (Fin d → ℂ))
    (hm : m ∈ Submodule.span ℂ {z : Sm E a ⊗[ℂ] (Fin d → ℂ) | ∃ φ v, P φ ∧ z = φ ⊗ₜ[ℂ] v}) : ev m x = c • ev m y := by
  induction hm using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨φ, v, hφ, rfl⟩ := hz
    rw [ev_tmul, ev_tmul, h φ hφ, mul_smul]
  | zero => simp
  | add z w _ _ hz hw => simp only [map_add (f := _), Pi.add_apply, hz, hw, smul_add]
  | smul s z _ hz => simp only [map_smul, Pi.smul_apply, hz, smul_comm s c]

theorem UpperTheory.V.Lit.Geo.centreVal :
    CentreVal := by
  intro E _ _ _ a U Ξ r hr q α hα X γ t g
  refine span_val (IsLevelFn U Ξ) _ _ _ (fun φ hφ => ?_) _ (hα.3 X)
  rw [mul_assoc, hφ.1, aInv E a φ _ (hφ.2.2 r hr), neg_mul]
end

section

noncomputable section

open scoped ContDiff Topology

namespace UpperTheory.V.Lit.Geo

theorem hkSmooth : HkSmooth := by
  intro V F _ _ _ _ _ _ Y hY W hW q w hw
  have hinf : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by
    exact_mod_cast le_top
  have hWat : ∀ p ∈ Y, ContDiffAt ℝ ∞ W p := fun p hp => hW.1.contDiffAt (hY.mem_nhds hp)
  have hwat : ∀ p ∈ Y, ContDiffAt ℝ ∞ w p := fun p hp => hw.contDiffAt (hY.mem_nhds hp)
  have hfd : ∀ p ∈ Y, ∀ t : ℝ, fderiv ℝ (flow W t) p = ContinuousLinearMap.id ℝ V + t • fderiv ℝ W p := by
    intro p hp t
    have hd : DifferentiableAt ℝ W p := (hWat p hp).differentiableAt (by simp)
    exact ((hasFDerivAt_id p).add (hd.hasFDerivAt.const_smul t)).fderiv
  have hflowc : ∀ z : V × ℝ, z.1 ∈ Y → ContDiffAt ℝ ∞ (fun y : V × ℝ => flow W y.2 y.1) z := by
    intro z hz
    exact contDiffAt_fst.add (contDiffAt_snd.smul ((hWat z.1 hz).comp z contDiffAt_fst))
  have hSo : IsOpen {z : V × ℝ | z.1 ∈ Y ∧ flow W z.2 z.1 ∈ Y} := by
    have h := ContinuousOn.isOpen_inter_preimage (f := fun y : V × ℝ => flow W y.2 y.1)
      (s := Prod.fst ⁻¹' Y) (t := Y) ?_ (hY.preimage continuous_fst) hY
    · exact h
    · intro z hz
      exact (hflowc z hz).continuousAt.continuousWithinAt
  have hsm : ContDiffOn ℝ ∞ (fun z : V × ℝ => hk W z.2 w z.1) {z : V × ℝ | z.1 ∈ Y ∧ flow W z.2 z.1 ∈ Y} := by
    intro z hz
    apply ContDiffAt.contDiffWithinAt
    apply UpperTheory.V.Lit.Dr.altSmooth (V × ℝ) V F q
    intro v
    have hf : ContDiffAt ℝ ∞ (fun y : V × ℝ => w (flow W y.2 y.1)) z := (hwat _ hz.2).comp z (hflowc z hz.1)
    have hu : ∀ i : Fin (q + 1), ContDiffAt ℝ ∞ ((Fin.cons (fun y : V × ℝ => W y.1)
        (fun (j : Fin q) (y : V × ℝ) => v j + y.2 • fderiv ℝ W y.1 (v j)) : Fin (q + 1) → V × ℝ → V) i) z := by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.cons_zero]
        exact (hWat z.1 hz.1).comp z contDiffAt_fst
      · simp only [Fin.cons_succ]
        exact contDiffAt_const.add (contDiffAt_snd.smul
          ((((hWat z.1 hz.1).fderiv_right hinf).comp z contDiffAt_fst).clm_apply contDiffAt_const))
    have h3 := UpperTheory.V.Lit.Dr.applySmooth (V × ℝ) V F (q + 1) (fun y : V × ℝ => w (flow W y.2 y.1))
      (Fin.cons (fun y : V × ℝ => W y.1)
        (fun (j : Fin q) (y : V × ℝ) => v j + y.2 • fderiv ℝ W y.1 (v j)) : Fin (q + 1) → V × ℝ → V) z hf hu
    apply h3.congr_of_eventuallyEq
    have hnb : {y : V × ℝ | y.1 ∈ Y} ∈ 𝓝 z := (hY.preimage continuous_fst).mem_nhds hz.1
    filter_upwards [hnb] with y hy
    simp only [hk, ContinuousAlternatingMap.compContinuousLinearMap_apply,
      ContinuousAlternatingMap.curryLeft_apply_apply, hfd y.1 hy y.2]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp
  have hmaps : ∀ p ∈ Y, ∀ t ∈ Set.Icc (0 : ℝ) 1, (p, t) ∈ {z : V × ℝ | z.1 ∈ Y ∧ flow W z.2 z.1 ∈ Y} :=
    fun p hp t ht => ⟨hp, hW.2 p hp t ht⟩
  refine ⟨hSo, hsm, ?_, ?_⟩
  · intro p hp
    have hc : ContinuousOn ((fun z : V × ℝ => hk W z.2 w z.1) ∘ (fun t : ℝ => (p, t))) (Set.Icc 0 1) :=
      hsm.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn (fun t ht => hmaps p hp t ht)
    simpa [Function.comp_def] using hc
  · have h4 := UpperTheory.V.Lit.Dr.paramSmooth V (V [⋀^Fin q]→L[ℝ] F) Y {z : V × ℝ | z.1 ∈ Y ∧ flow W z.2 z.1 ∈ Y}
      (fun z => hk W z.2 w z.1) hY hSo (fun z hz => hmaps z.1 hz.1 z.2 hz.2) hsm
    exact h4

end UpperTheory.V.Lit.Geo
end
end

section

noncomputable section

open UpperTheory.V.Lit.Dr
open scoped ContDiff

namespace UpperTheory.V.Lit.Geo

theorem pbD : PbD := by
  intro V' V F _ _ _ _ _ _ _ _ q H w p hH hw
  have hr : minSmoothness ℝ 2 ≤ ∞ := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.2 le_top
  have hinf : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by
    exact_mod_cast le_top
  refine ⟨?_, extDeriv_pullback (hw.differentiableAt (by simp)) hH hr⟩
  apply altSmooth V' V' F q (pb H w) p
  intro v
  have h1 : ContDiffAt ℝ ∞ (fun y => w (H y)) p := hw.comp p hH
  have h2 : ∀ i, ContDiffAt ℝ ∞ (fun y => fderiv ℝ H y (v i)) p := fun i =>
    (hH.fderiv_right hinf).clm_apply contDiffAt_const
  have h3 := applySmooth V' V F q (fun y => w (H y)) (fun i y => fderiv ℝ H y (v i)) p h1 h2
  simpa [pb, Function.comp_def] using h3

end UpperTheory.V.Lit.Geo
end
end

section

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Lit.Dr
open UpperTheory.V.Lit.Geo

section

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private theorem mul_bd (x y : Matrix (Fin a) (Fin a) (Cinf E)) :
    ‖toL (x * y)‖ ≤ a * (‖toL x‖ * ‖toL y‖) := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  change ‖∑ k, x i k * y k j‖ ≤ _
  refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ (‖toL x‖ * ‖toL y‖) fun k _ => ?_).trans (by simp))
  refine (norm_mul_le _ _).trans (mul_le_mul ?_ ?_ (norm_nonneg _) (norm_nonneg _))
  · exact (norm_le_pi_norm (toL x i) k).trans (norm_le_pi_norm (toL x) i)
  · exact (norm_le_pi_norm (toL y k) j).trans (norm_le_pi_norm (toL y) k)

private theorem star_bd (x : Matrix (Fin a) (Fin a) (Cinf E)) : ‖toL (star x)‖ ≤ ‖toL x‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  change ‖star (x j i)‖ ≤ _
  rw [norm_star]
  exact (norm_le_pi_norm (toL x j) i).trans (norm_le_pi_norm (toL x) j)

private theorem sand_bd {C : ℝ} (h : GL (Fin a) (Cinf E)) (hC : ‖toL h.val‖ ≤ C) (v : HV E a) :
    ‖sand h v‖ ≤ (a * a * C * C) * ‖v‖ := by
  have h0 : 0 ≤ C := (norm_nonneg _).trans hC
  change ‖toL (h.val * Matrix.of v.1 * star h.val)‖ ≤ _
  have h1 : ‖toL (h.val * Matrix.of v.1)‖ ≤ a * (C * ‖v‖) :=
    (mul_bd _ _).trans (by
      change (a : ℝ) * (‖toL h.val‖ * ‖v‖) ≤ _
      gcongr)
  calc _ ≤ _ := mul_bd _ _
    _ ≤ a * ((a * (C * ‖v‖)) * C) := by
      gcongr
      exact (star_bd _).trans hC
    _ = _ := by ring

private theorem exists_cpt (C : ℝ) : ∃ K : Set (Lie E a), IsCompact K ∧ K ⊆ invSet E a ∧
    ∀ h : GL (Fin a) (Cinf E), ‖toL h.val‖ ≤ C → ‖toL (h⁻¹).val‖ ≤ C → toL h.val ∈ K := by
  have hc : IsClosed {z : Lie E a × Lie E a | toL (Matrix.of z.1 * Matrix.of z.2) = toL 1} := by
    refine isClosed_eq ?_ continuous_const
    refine continuous_pi fun i => continuous_pi fun j => ?_
    change Continuous fun z : Lie E a × Lie E a => ∑ k, z.1 i k * z.2 k j
    fun_prop
  refine ⟨Prod.fst '' ((Metric.closedBall 0 C ×ˢ Metric.closedBall 0 C) ∩ _),
    (((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).inter_right hc).image continuous_fst, ?_, ?_⟩
  · rintro _ ⟨z, ⟨-, hz⟩, rfl⟩
    have e : Matrix.of z.1 * Matrix.of z.2 = 1 := hz
    exact (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse e)
  · intro h h1 h2
    exact ⟨(toL h.val, toL (h⁻¹).val), ⟨⟨mem_closedBall_zero_iff.2 h1, mem_closedBall_zero_iff.2 h2⟩,
      congrArg toL h.mul_inv⟩, rfl⟩

private theorem mat_bd (Ξ : AlgRep E a) (C : ℝ) : ∃ B : ℝ, 0 ≤ B ∧
    ∀ h : GL (Fin a) (Cinf E), ‖toL h.val‖ ≤ C → ‖toL (h⁻¹).val‖ ≤ C → ∀ y, ‖Ξ.mat h *ᵥ y‖ ≤ B * ‖y‖ := by
  obtain ⟨K, hK, hs, hm⟩ := exists_cpt (E := E) (a := a) C
  have hb : ∀ i j, ∃ b : ℝ, ∀ x ∈ K, ‖extGL (fun y => Ξ.mat y i j) x‖ ≤ b := fun i j =>
    hK.exists_bound_of_continuousOn ((matSmooth E a Ξ i j).1.continuousOn.mono hs)
  choose b hb using hb
  have h0 : 0 ≤ ∑ i, ∑ j, |b i j| := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨∑ i, ∑ j, |b i j|, h0, fun h h1 h2 y => (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_⟩
  change ‖∑ j, Ξ.mat h i j * y j‖ ≤ _
  calc _ ≤ ∑ j, |b i j| * ‖y‖ := by
        refine norm_sum_le_of_le _ fun j _ => (norm_mul_le _ _).trans
          (mul_le_mul ?_ (norm_le_pi_norm y j) (norm_nonneg _) (abs_nonneg _))
        have := hb i j _ (hm h h1 h2)
        rw [extGL_val] at this
        exact this.trans (le_abs_self _)
    _ = (∑ j, |b i j|) * ‖y‖ := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (f := fun i => ∑ j, |b i j|) (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
          (Finset.mem_univ i)) (norm_nonneg _)

end

theorem UpperTheory.V.Lit.Geo.matBd :
    MatBd := by
  intro E _ _ _ a Ξ C
  obtain ⟨B, hB, h⟩ := mat_bd Ξ C
  refine ⟨max B (a * a * C * C), le_max_of_le_left hB, fun g h1 h2 => ⟨fun y => (h g h1 h2 y).trans ?_,
    fun v => (sand_bd g h1 v).trans ?_, fun v => (sand_bd g⁻¹ h2 v).trans ?_⟩⟩
  · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
  · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
end
end

section

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit.Dr
open scoped ContDiff

namespace UpperTheory.V.Lit.Geo

variable {E : Type} [Field E] [NumberField E] {a : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

private theorem sub_smooth {f : X → HV E a} {x : X} (h : ContDiffAt ℝ ∞ (fun y => (f y).1) x) :
    ContDiffAt ℝ ∞ f x := by
  obtain ⟨r, hr⟩ := (HV E a).subtype.exists_leftInverse_of_injective (Submodule.ker_subtype _)
  have e : f = fun y => LinearMap.toContinuousLinearMap r (f y).1 :=
    funext fun y => (LinearMap.congr_fun hr (f y)).symm
  rw [e]
  exact (LinearMap.toContinuousLinearMap r).contDiff.contDiffAt.comp x h

private theorem sand_smooth {σ : X → GL (Fin a) (Cinf E)} {v : X → HV E a} {x : X}
    (h : ∀ i j, ContDiffAt ℝ ∞ (fun y => (σ y).val i j) x) (hv : ∀ i j, ContDiffAt ℝ ∞ (fun y => (v y).1 i j) x) :
    ContDiffAt ℝ ∞ (fun y => sand (σ y) (v y)) x := by
  refine sub_smooth (contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j => ?_)
  have e : (fun y => (sand (σ y) (v y)).1 i j) =
      fun y => ∑ l, (∑ k, (σ y).val i k * (v y).1 k l) * star ((σ y).val j l) := by
    funext y
    change ((σ y).val * Matrix.of (v y).1 * star (σ y).val) i j = _
    simp [Matrix.mul_apply]
  rw [e]
  refine ContDiffAt.sum fun l _ => (ContDiffAt.sum fun k _ => (h i k).mul (hv k l)).mul ?_
  exact (starL' ℝ : Cinf E ≃L[ℝ] Cinf E).contDiff.contDiffAt.comp x (h j l)

end UpperTheory.V.Lit.Geo

open UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Lit.Geo.fieldSm :
    FieldSm := by
  intro E _ _ _ a U Y C hY W hW s p₀ hp₀
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
  obtain ⟨τ, hτ, hs⟩ := locSec E a p₀ hp₀
  refine ContDiffAt.contDiffWithinAt ?_
  have h1 : ContDiffAt ℝ ∞ (fun p => sand (τ p) (hv (Y (infGL E a (τ p) * finGL E a x)))) p₀ := by
    refine sand_smooth (fun i j => contDiffAt_pi.1 (contDiffAt_pi.1 hτ i) j) fun i j => contDiffAt_pi.2 fun w => ?_
    obtain ⟨φ, hφ, -⟩ := hY.sm i j w
    have := (contDiffAt_chart φ.2 (finGL E a x) (val_mem_invSet (τ p₀))).comp p₀ hτ
    simp only [Function.comp_def, chart_val, hφ] at this
    simp only [infGL_comm]
    exact this
  refine h1.congr_of_eventuallyEq (hs.mono fun p hp => ?_)
  have := hW (τ p) x
  rwa [hp] at this
end
end
