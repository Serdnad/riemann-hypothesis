module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.Bundle002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle242
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PSmoothB
import GroundTheory.GlobalFields.Adele.Bundle002
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open MeasureTheory NumberField GlobalTheory.CuspRep
open scoped Pointwise
open PositivityTheory.RgTw (G)

namespace PositivityTheory.Rg.BcB.CG.ReproL

open Classical

section Gen

variable {G U : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
  [TopologicalSpace U] [CompactSpace U] [T2Space U] [SecondCountableTopology U] [MeasurableSpace U] [BorelSpace U]
  (ν : Measure U) [IsFiniteMeasure ν]
  (K : Subgroup G) (hK : IsCompact (K : Set G)) (ι : U → G) (hι : Continuous ι) (hιK : ∀ u, ι u ∈ K)

include hK in
theorem integral_mul_mem (k : G) (hk : k ∈ K) (F : G → ℂ) : ∫ y, F (y * k) ∂μ = ∫ y, F y ∂μ := by
  have e : Measure.map (⇑(MeasurableEquiv.mulRight k)) μ = μ :=
    GlobalTheory.CompactRight.map_mul_right_eq_of_mem_compact μ K hK k hk
  conv_rhs => rw [← e]
  rw [(MeasurableEquiv.mulRight k).measurableEmbedding.integral_map]
  rfl

include hK hι hιK in
theorem swap_right (c : G → U → ℂ) (hc : Continuous (Function.uncurry c)) (Kc : Set G) (hKc : IsCompact Kc)
    (hcK : ∀ y u, y ∉ Kc → c y u = 0) (h : G → ℂ) (hh : Continuous h) :
    ∫ y, (∫ u, c y u * h (y * ι u) ∂ν) ∂μ = ∫ y, (∫ u, c (y * (ι u)⁻¹) u ∂ν) * h y ∂μ := by
  have hKK : IsCompact (Kc * (K : Set G)) := hKc.mul hK
  have i1 : Integrable (Function.uncurry fun y u => c y u * h (y * ι u)) (μ.prod ν) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact hc.mul (hh.comp (continuous_fst.mul (hι.comp continuous_snd)))
    · refine HasCompactSupport.intro (hKc.prod isCompact_univ) fun p hp => ?_
      have : p.1 ∉ Kc := fun h1 => hp ⟨h1, Set.mem_univ _⟩
      simp [Function.uncurry, hcK _ _ this]
  have i2 : Integrable (Function.uncurry fun y u => c (y * (ι u)⁻¹) u * h y) (μ.prod ν) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (hc.comp ((continuous_fst.mul (hι.comp continuous_snd).inv).prodMk continuous_snd)).mul
        (hh.comp continuous_fst)
    · refine HasCompactSupport.intro (hKK.prod isCompact_univ) fun p hp => ?_
      have : p.1 * (ι p.2)⁻¹ ∉ Kc := fun h1 =>
        hp ⟨⟨p.1 * (ι p.2)⁻¹, h1, ι p.2, hιK p.2, by simp⟩, Set.mem_univ _⟩
      simp [Function.uncurry, hcK _ _ this]
  rw [integral_integral_swap i1]
  have e : ∀ u, ∫ y, c y u * h (y * ι u) ∂μ = ∫ y, c (y * (ι u)⁻¹) u * h y ∂μ := by
    intro u
    have := integral_mul_mem μ K hK (ι u) (hιK u) (fun y => c (y * (ι u)⁻¹) u * h y)
    simpa using this
  simp_rw [e]
  rw [← integral_integral_swap i2]
  congr 1
  funext y
  rw [integral_mul_const]

include hK hι hιK in
theorem avg_cont_supp (c : G → U → ℂ) (hc : Continuous (Function.uncurry c)) (Kc : Set G) (hKc : IsCompact Kc)
    (hcK : ∀ y u, y ∉ Kc → c y u = 0) :
    Continuous (fun y => ∫ u, c (y * (ι u)⁻¹) u ∂ν) ∧ HasCompactSupport (fun y => ∫ u, c (y * (ι u)⁻¹) u ∂ν) := by
  constructor
  · have := continuous_parametric_integral_of_continuous (μ := ν) (f := fun y u => c (y * (ι u)⁻¹) u)
      (hc.comp ((continuous_fst.mul (hι.comp continuous_snd).inv).prodMk continuous_snd)) isCompact_univ
    simpa [Measure.restrict_univ] using this
  · refine HasCompactSupport.intro (hKc.mul hK) fun y hy => ?_
    have : ∀ u, c (y * (ι u)⁻¹) u = 0 := fun u => hcK _ _ fun h1 => hy ⟨_, h1, ι u, hιK u, by simp⟩
    simp [this]

end Gen

theorem continuous_toUnitsU (N : ℕ) :
    Continuous (fun u : Matrix.unitaryGroup (Fin N) ℂ => (Unitary.toUnits u : G N)) := by
  rw [Units.continuous_iff]
  constructor
  · exact continuous_subtype_val
  · exact continuous_star.comp continuous_subtype_val

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

theorem continuous_along_infP (v : InfinitePlace E) (g : GA E N) (φ : GA E N → ℂ) (hs : φ ∈ Sm E N) :
    Continuous fun t : G N => φ (g * infP N (Pi.mulSingle v t)) := by
  let Mt : (InfinitePlace E → G N) → GL (Fin N) (Cinf E) := fun y =>
    Units.map (Matrix.piRingEquiv (n := Fin N) (β := fun _ : InfinitePlace E => ℂ)).symm.toMonoidHom
      (MulEquiv.piUnits.symm y)
  have hM : Continuous Mt := by
    refine Continuous.units_map _ ?_ |>.comp (ContinuousMulEquiv.piUnits (M := fun _ : InfinitePlace E =>
      Matrix (Fin N) (Fin N) ℂ)).symm.continuous
    exact continuous_pi fun i => continuous_pi fun j => continuous_pi fun v => (continuous_apply v).matrix_elem i j
  have hL : Continuous fun x : Matrix (Fin N) (Fin N) (Cinf E) => (toL x : Lie E N) := continuous_id
  have e : (fun t : G N => φ (g * infP N (Pi.mulSingle v t))) =
      fun t => chart φ g (toL (Mt (Pi.mulSingle v t)).val) := by
    funext t
    rw [chart_val]
    rfl
  rw [e]
  exact (hs g).continuousOn.comp_continuous
    (hL.comp ((Units.continuous_val (M := Matrix (Fin N) (Fin N) (Cinf E))).comp (hM.comp (continuous_mulSingle (A := fun _ : InfinitePlace E => G N) v))))
    fun t => val_mem_invSet _

end PositivityTheory.Rg.BcB.CG.ReproL
end
end

section

noncomputable section

open NumberField MeasureTheory Matrix
open GlobalTheory.CuspRep PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf finH)
open scoped ContDiff Classical

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace PositivityTheory.Rg.BcB.CG

namespace SmoothIntegrals

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def entL (M : KMod n) (i j : Ix M) : (M.V →L[ℂ] M.V) →L[ℝ] ℂ :=
  ((innerSL ℂ (stdOrthonormalBasis ℂ M.V i)).comp
    (ContinuousLinearMap.apply ℂ M.V (stdOrthonormalBasis ℂ M.V j))).restrictScalars ℝ

theorem mult_contDiffOn [MeasurableSpace (G n)] {μ : Measure (G n)} {M : KMod n} {k : Mat n → (M.V →L[ℂ] M.V)}
    {val : Inf n → ℂ} {T : ℝ} (h : IsMult μ M k val T) : ContDiffOn ℝ ∞ k (GLs n) := by
  obtain ⟨m, c, w, g, ks, hks, hk, -⟩ := h
  exact (ContDiffOn.sum fun i _ => ((hks i).2.1).const_smul (c i)).congr fun y hy => hk y hy

theorem ent_contDiffOn [MeasurableSpace (G n)] {μ : Measure (G n)} {M : KMod n} {k : Mat n → (M.V →L[ℂ] M.V)}
    {val : Inf n → ℂ} {T : ℝ} (h : IsMult μ M k val T) (i j : Ix M) :
    ContDiffOn ℝ ∞ (fun A => ent M (k A) i j) (GLs n) :=
  (entL M i j).contDiff.comp_contDiffOn (mult_contDiffOn h)

theorem continuous_entA [MeasurableSpace (G n)] {μ : Measure (G n)} {M : Mods E n} {k : Kers M}
    {val : InfinitePlace E → Inf n → ℂ} {T : ℝ} (h : IsMults μ k val T) (I J : IxA M) :
    Continuous fun g : GA E n => entA k I J g :=
  continuous_finsetProd _ fun v _ => (entL (M v) (I v) (J v)).continuous.comp
    ((mult_contDiffOn (h v)).continuousOn.comp_continuous (Units.continuous_val.comp (continuous_gI v))
      fun _ => val_mem_GLs₀ _)

omit [IsCMField E] in
theorem continuous_gFin₀ : Continuous (gFin : GA E n → GL (Fin n) (Af E)) :=
  Continuous.units_map _ (continuous_id.matrix_map continuous_snd)

theorem continuous_hFin₀ {a b : ℕ} : Continuous (hFin : H E a b → Hf E a b) :=
  (continuous_gFin₀.comp continuous_fst).prodMk (continuous_gFin₀.comp continuous_snd)

theorem gFin_infGL₀ (u : GL (Fin n) (Cinf E)) : gFin (infGL E n u) = 1 := pFin_infGL u

end SmoothIntegrals


open SmoothIntegrals in
theorem smoothOf (hTT : TensTest) : SmoothOf := by
  set_option synthInstance.maxHeartbeats 200000 in
    intro E _ _ _ a b _ _ _ _ μa _ μb _ Ma Mb ι _ D ka kb va vb T ψ U f hka hkb hψ _ _ hR
    have : BorelSpace (H E a b) := ⟨rfl⟩
    have : D.μ.IsMulLeftInvariant := D.haar.1
    have : IsLocallyFiniteMeasure D.μ := D.haar.2.2.2
    have : IsFiniteMeasureOnCompacts D.μ := isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure
    obtain ⟨hfc, c, hc, hconv⟩ := hR
    have hTest := (hTT E a b μa μb Ma Mb ι ka kb va vb T ψ hka hkb hψ).1
    have hψc : ∀ x y, Continuous fun w : H E a b => ψ x y (hFin w) := fun x y => (hψ x y).1.comp continuous_hFin₀

    have hrep : ∀ i z, f i z = c⁻¹ * ∑ j, ∫ y, tens ka kb ψ i j y * f j (z * y) ∂D.μ := by
      intro i z
      have h1 := congrFun (congrFun hconv i) z
      have h2 : c * f i z = ∑ j, ∫ y, tens ka kb ψ i j y * f j (z * y) ∂D.μ := h1.symm
      rw [← h2, inv_mul_cancel_left₀ hc]
    refine ⟨fun i m₂ => ?_, fun i m₁ => ?_⟩
    · have hj : ∀ j, (fun x => ∫ y, tens ka kb ψ i j y * f j ((x, m₂) * y) ∂D.μ) ∈ Sm E a := by
        intro j
        have h := mem_Sm_conv D.μ (MonoidHom.inl (GA E a) (GA E b)) (continuous_id.prodMk continuous_const) Prod.fst
          continuous_fst (fun h w => by simp) (fun v A => ent (Ma v) (ka v A) (i.1.1 v) (j.1.1 v))
          (fun v => ent_contDiffOn (hka v) _ _) (fun w => entA kb i.1.2 j.1.2 w.2 * ψ i.2 j.2 (hFin w))
          (((continuous_entA hkb _ _).comp continuous_snd).mul (hψc _ _))
          (fun _ w => by simp [hFin, gFin_infGL₀]) (f j) (hfc j) (tens ka kb ψ i j) (fun w => mul_assoc _ _ _)
          (hTest i j).2 ((1 : GA E a), m₂)
        have e : ∀ x : GA E a, ((1 : GA E a), m₂) * MonoidHom.inl (GA E a) (GA E b) x = (x, m₂) := fun x =>
          Prod.ext (one_mul x) (mul_one m₂)
        simpa only [e] using h
      refine ⟨⟨c⁻¹ • ∑ j, fun x => ∫ y, tens ka kb ψ i j y * f j ((x, m₂) * y) ∂D.μ,
        (Sm E a).smul_mem c⁻¹ ((Sm E a).sum_mem fun j _ => hj j)⟩, ?_⟩
      funext x
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact (hrep i (x, m₂)).symm
    · have hj : ∀ j, (fun x => ∫ y, tens ka kb ψ i j y * f j ((m₁, x) * y) ∂D.μ) ∈ Sm E b := by
        intro j
        have h := mem_Sm_conv D.μ (MonoidHom.inr (GA E a) (GA E b)) (continuous_const.prodMk continuous_id) Prod.snd
          continuous_snd (fun h w => by simp) (fun v A => ent (Mb v) (kb v A) (i.1.2 v) (j.1.2 v))
          (fun v => ent_contDiffOn (hkb v) _ _) (fun w => entA ka i.1.1 j.1.1 w.1 * ψ i.2 j.2 (hFin w))
          (((continuous_entA hka _ _).comp continuous_fst).mul (hψc _ _))
          (fun _ w => by simp [hFin, gFin_infGL₀]) (f j) (hfc j) (tens ka kb ψ i j)
          (fun w => by
            show entA ka _ _ w.1 * entA kb _ _ w.2 * ψ _ _ (hFin w) = entA kb _ _ w.2 * (entA ka _ _ w.1 * ψ _ _ (hFin w))
            ring)
          (hTest i j).2 (m₁, (1 : GA E b))
        have e : ∀ x : GA E b, (m₁, (1 : GA E b)) * MonoidHom.inr (GA E a) (GA E b) x = (m₁, x) := fun x =>
          Prod.ext (mul_one m₁) (one_mul x)
        simpa only [e] using h
      refine ⟨⟨c⁻¹ • ∑ j, fun x => ∫ y, tens ka kb ψ i j y * f j ((m₁, x) * y) ∂D.μ,
        (Sm E b).smul_mem c⁻¹ ((Sm E b).sum_mem fun j _ => hj j)⟩, ?_⟩
      funext x
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact (hrep i (m₁, x)).symm

end PositivityTheory.Rg.BcB.CG

end
end
