module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.ActMat
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Linter.HaveILetI
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

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

private noncomputable def Bf {F : Type} [Field F] [NumberField F] (δ : F)
    (a y : Fin 4 → FiniteAdeleRing (𝓞 F) F) : FiniteAdeleRing (𝓞 F) F :=
  2 * (a 2 * y 2 - algebraMap F (FiniteAdeleRing (𝓞 F) F) δ * (a 3 * y 3)) - a 1 * y 0 - a 0 * y 1

private theorem continuous_Bf {F : Type} [Field F] [NumberField F] (δ : F) :
    Continuous fun p : (Fin 4 → FiniteAdeleRing (𝓞 F) F) × (Fin 4 → FiniteAdeleRing (𝓞 F) F) =>
      Bf δ p.1 p.2 := by
  unfold Bf
  fun_prop

private theorem fin_level {F : Type} [Field F] [NumberField F] (δ : F)
    {g : (Fin 4 → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ finiteSchwartzBruhatPi F (ι := Fin 4)) :
    ∃ Λ : OpenAddSubgroup (FiniteAdeleRing (𝓞 F) F), ∀ a : Fin 4 → FiniteAdeleRing (𝓞 F) F,
      (∀ i, a i ∈ Λ) → ∀ y, g (y + a) = g y ∧ (finiteAdelicChar F (Bf δ a y) : ℂ) * g y = g y := by
  obtain ⟨hl, hc⟩ := hg
  have hev := IsLocallyConstant.iff_eventually_eq g |>.1 hl
  have hP1 : IsOpen {p : (Fin 4 → FiniteAdeleRing (𝓞 F) F) × (Fin 4 → FiniteAdeleRing (𝓞 F) F) |
      g (p.2 + p.1) = g p.2} := by
    rw [isOpen_iff_eventually]
    intro p hp
    have h1 : ∀ᶠ q : (Fin 4 → FiniteAdeleRing (𝓞 F) F) × (Fin 4 → FiniteAdeleRing (𝓞 F) F) in 𝓝 p,
        g (q.2 + q.1) = g (p.2 + p.1) :=
      ((continuous_snd.add continuous_fst).tendsto p).eventually (hev _)
    have h2 : ∀ᶠ q : (Fin 4 → FiniteAdeleRing (𝓞 F) F) × (Fin 4 → FiniteAdeleRing (𝓞 F) F) in 𝓝 p,
        g q.2 = g p.2 :=
      (continuous_snd.tendsto p).eventually (hev _)
    filter_upwards [h1, h2] with q e1 e2
    change g (q.2 + q.1) = g q.2
    rw [e1, e2]
    exact hp
  have hχ : IsLocallyConstant fun x : FiniteAdeleRing (𝓞 F) F => (finiteAdelicChar F x : ℂ) := by
    have := isLocallyConstant_finiteAdelicChar_mul (K := F) (1 : FiniteAdeleRing (𝓞 F) F)
    simpa using this
  have hP2 : IsOpen {p : (Fin 4 → FiniteAdeleRing (𝓞 F) F) × (Fin 4 → FiniteAdeleRing (𝓞 F) F) |
      (finiteAdelicChar F (Bf δ p.1 p.2) : ℂ) = 1} :=
    (hχ.isOpen_fiber 1).preimage (continuous_Bf δ)
  obtain ⟨u, w, hu, -, h0u, hSw, huw⟩ := generalized_tube_lemma (isCompact_singleton (x := (0 : Fin 4 → FiniteAdeleRing (𝓞 F) F)))
    (t := tsupport g) hc (hP1.inter hP2) (by
      rintro ⟨a, y⟩ ⟨ha, -⟩
      obtain rfl : a = 0 := ha
      refine ⟨by simp, ?_⟩
      change (finiteAdelicChar F (Bf δ 0 y) : ℂ) = 1
      have : Bf δ 0 y = 0 := by simp [Bf]
      rw [this, AddChar.map_zero_eq_one, Circle.coe_one])
  have hu0 : u ∈ 𝓝 (0 : Fin 4 → FiniteAdeleRing (𝓞 F) F) := hu.mem_nhds (h0u rfl)
  rw [nhds_pi, Filter.mem_pi] at hu0
  obtain ⟨I, -, t, ht, hIt⟩ := hu0
  have hN : (⋂ i, t i) ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F) := Filter.iInter_mem.mpr ht
  obtain ⟨J, hJ⟩ := exists_idealFiniteAdeles_subset hN
  refine ⟨⟨idealFiniteAdeles J, isOpen_idealFiniteAdeles J⟩, fun a ha y => ?_⟩
  have hmem : ∀ b : Fin 4 → FiniteAdeleRing (𝓞 F) F, (∀ i, b i ∈ idealFiniteAdeles J) → b ∈ u :=
    fun b hb => hIt fun i _ => Set.mem_iInter.1 (hJ (hb i)) i
  have ha' : ∀ i, a i ∈ idealFiniteAdeles J := ha
  have hau : a ∈ u := hmem a ha'
  have hnau : -a ∈ u := hmem (-a) fun i => neg_mem (ha' i)
  by_cases hy : y ∈ tsupport g
  · obtain ⟨e1, e2⟩ := huw (Set.mk_mem_prod hau (hSw hy))
    have e2' : (finiteAdelicChar F (Bf δ a y) : ℂ) = 1 := e2
    refine ⟨e1, ?_⟩
    rw [e2', one_mul]
  · have hy0 : g y = 0 := image_eq_zero_of_notMem_tsupport hy
    refine ⟨?_, by rw [hy0, mul_zero]⟩
    by_cases hy' : y + a ∈ tsupport g
    · have e1 : g (y + a + -a) = g (y + a) := (huw (Set.mk_mem_prod hnau (hSw hy'))).1
      rw [add_neg_cancel_right] at e1
      exact e1.symm
    · rw [hy0]
      exact image_eq_zero_of_notMem_tsupport hy'

private theorem quaternaryForm_polarization {F : Type} [Field F] [NumberField F] (δ : F) (a v : V4 F)
    (ha : ∀ i, (a i).1 = 0) :
    ψ (B4 δ a v) = (finiteAdelicChar F (Bf δ (finPartPi a) (finPartPi v)) : ℂ) := by
  have : B4 δ a v = finiteAdeleInr (Bf δ (finPartPi a) (finPartPi v)) := by
    refine Prod.ext ?_ ?_
    · change (2 : InfiniteAdeleRing F) * ((a 2).1 * (v 2).1 - (rt δ).1 * ((a 3).1 * (v 3).1)) - (a 1).1 * (v 0).1 - (a 0).1 * (v 1).1 = 0
      simp [ha]
    · have h2 : (2 : A F).2 = (2 : FiniteAdeleRing (𝓞 F) F) := map_ofNat (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) 2
      change (2 : FiniteAdeleRing (𝓞 F) F) * ((a 2).2 * (v 2).2 - (rt δ).2 * ((a 3).2 * (v 3).2)) - (a 1).2 * (v 0).2 - (a 0).2 * (v 1).2 = Bf δ (finPartPi a) (finPartPi v)
      rfl
  rw [ψ, this, finiteAdelicChar_apply]

private theorem level_of_mem {F : Type} [Field F] [NumberField F] (δ : F) {f : V4 F → ℂ}
    (hf : f ∈ schwartzBruhatPi (K := F) (ι := Fin 4)) :
    ∃ Λ : OpenAddSubgroup (FiniteAdeleRing (𝓞 F) F), ∀ a : V4 F, (∀ i, (a i).1 = 0 ∧ (a i).2 ∈ Λ) →
      ∀ v, f (v + a) = f v ∧ ψ (B4 δ a v) * f v = f v := by
  induction hf using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, g, hg, rfl⟩ := hG
    obtain ⟨Λ, hΛ⟩ := fin_level δ hg
    refine ⟨Λ, fun a ha v => ?_⟩
    obtain ⟨e1, e2⟩ := hΛ (finPartPi a) (fun i => (ha i).2) (finPartPi v)
    have hinf : infPartPi (v + a) = infPartPi v := by
      funext i
      have : (v + a) i = ((v i).1, (v i).2 + (a i).2) := by
        refine Prod.ext ?_ rfl
        change (v i).1 + (a i).1 = (v i).1
        rw [(ha i).1, add_zero]
      simp only [infPartPi, this]
    have hfin : finPartPi (v + a) = finPartPi v + finPartPi a := rfl
    refine ⟨?_, ?_⟩
    · simp only [schwartzBruhatTensorPi, hinf, hfin, e1]
    · simp only [schwartzBruhatTensorPi]
      rw [quaternaryForm_polarization δ a v fun i => (ha i).1, mul_left_comm, e2]
  | zero =>
    exact ⟨⊤, fun _ _ _ => ⟨rfl, by simp⟩⟩
  | add G H _ _ hG hH =>
    obtain ⟨Λ, hΛ⟩ := hG
    obtain ⟨Λ', hΛ'⟩ := hH
    refine ⟨Λ ⊓ Λ', fun a ha v => ?_⟩
    obtain ⟨e1, e2⟩ := hΛ a (fun i => ⟨(ha i).1, (ha i).2.1⟩) v
    obtain ⟨e1', e2'⟩ := hΛ' a (fun i => ⟨(ha i).1, (ha i).2.2⟩) v
    refine ⟨?_, ?_⟩
    · simp only [Pi.add_apply, e1, e1']
    · simp only [Pi.add_apply, mul_add, e2, e2']
  | smul c G _ hG =>
    obtain ⟨Λ, hΛ⟩ := hG
    refine ⟨Λ, fun a ha v => ?_⟩
    obtain ⟨e1, e2⟩ := hΛ a ha v
    refine ⟨?_, ?_⟩
    · simp only [Pi.smul_apply, e1]
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [mul_left_comm, e2]

theorem UpperTheory.ConvolutionTheory.R2.Fo.fixEx :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F), (∀ φ : S4 F, ∃ Λ, φ ∈ Fix δ Λ) ∧ ∀ Λ Λ', Λ ≤ Λ' → Fix δ Λ' ≤ Fix δ Λ := by
  intro F _ _ δ
  refine ⟨fun φ => ?_, fun Λ Λ' h φ hφ a ha v => hφ a (fun i => ⟨(ha i).1, h (ha i).2⟩) v⟩
  obtain ⟨Λ, hΛ⟩ := level_of_mem δ φ.2
  exact ⟨Λ, fun a ha v => hΛ a ha v⟩
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.Fo

open NumberField.mixedEmbedding

private noncomputable def lin {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
    (w : InfinitePlace F) (i : Fin 4) : (Fin 4 → mixedSpace F) →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : {w : InfinitePlace F // w.IsReal} => ℝ)
      ⟨w, IsTotallyReal.isReal w⟩).comp
      ((ContinuousLinearMap.fst ℝ ({w : InfinitePlace F // w.IsReal} → ℝ)
        ({w : InfinitePlace F // w.IsComplex} → ℂ)).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => mixedSpace F) i)))

end UpperTheory.ConvolutionTheory.R2.Fo

theorem UpperTheory.ConvolutionTheory.R2.Fo.xEx :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (w : InfinitePlace F) (i : Fin 4) (φ : V4 F → ℂ), φ ∈ schwartzBruhatPi (K := F) (ι := Fin 4) → (fun v => cw w (v i) * φ v) ∈ schwartzBruhatPi (K := F) (ι := Fin 4) := by
  intro F _ _ _ w i φ hφ
  induction hφ using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨f, g, hg, rfl⟩ := hG
    have e : (fun v => cw w (v i) * schwartzBruhatTensorPi f g v) =
        schwartzBruhatTensorPi (SchwartzMap.smulLeftCLM ℂ (lin w i) f) g := by
      funext v
      simp only [schwartzBruhatTensorPi]
      rw [SchwartzMap.smulLeftCLM_apply_apply (lin w i).hasTemperateGrowth, smul_eq_mul, mul_assoc]
      congr 1
    rw [e]
    exact schwartzBruhatTensorPi_mem _ hg
  | zero =>
    have e : (fun v => cw w (v i) * (0 : V4 F → ℂ) v) = 0 := by
      funext v
      simp
    rw [e]
    exact zero_mem _
  | add G H _ _ hG hH =>
    have e : (fun v => cw w (v i) * (G + H) v) = (fun v => cw w (v i) * G v) + fun v => cw w (v i) * H v := by
      funext v
      simp [mul_add]
    rw [e]
    exact add_mem hG hH
  | smul c G _ hG =>
    have e : (fun v => cw w (v i) * (c • G) v) = c • fun v => cw w (v i) * G v := by
      funext v
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [e]
    exact Submodule.smul_mem _ c hG
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

private theorem slice_mem {F : Type} [Field F] [NumberField F] {f : V4 F → ℂ}
    (hf : f ∈ schwartzBruhatPi (K := F) (ι := Fin 4)) :
    (fun y : Fin 4 → FiniteAdeleRing (𝓞 F) F => f fun i => ((0, y i) : A F)) ∈
      finiteSchwartzBruhatPi F (ι := Fin 4) := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, g, hg, rfl⟩ := hx
    have e : (fun y : Fin 4 → FiniteAdeleRing (𝓞 F) F =>
        schwartzBruhatTensorPi p g fun i => ((0, y i) : A F)) =
        p (infPartPi fun _ : Fin 4 => (0 : A F)) • g := by
      funext y
      rfl
    rw [e]
    exact Submodule.smul_mem _ _ hg
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul c x _ hx => exact Submodule.smul_mem _ c hx

private theorem gauss_fin {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (δ : F)
    (y : Fin 4 → FiniteAdeleRing (𝓞 F) F) : gauss δ (fun i => ((0, y i) : A F)) = 1 := by
  have key : ∀ a : V4 F, (∀ i, TR.pInf F (a i) = 0) → gauss δ a = 1 := fun a h => by
    simp only [gauss, map_add (f := _), map_sub, map_mul, map_pow, h]
    simp
  exact key _ fun i => map_zero (TR.infEq F).symm

theorem UpperTheory.ConvolutionTheory.R2.Fo.vacForm :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (δ : F), ∀ φ ∈ Vac δ, ∃ g ∈ finiteSchwartzBruhatPi F (ι := Fin 4), φ.1 = fun v => gauss δ v * g (finPartPi v) := by
  intro F _ _ _ δ φ hφ
  refine ⟨_, slice_mem φ.2, funext fun v => ?_⟩
  have h := hφ v (fun i => ((0, (v i).2) : A F)) rfl
  rw [gauss_fin, mul_one] at h
  rw [h, mul_comm]
  rfl
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Fo.fkBasic :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (O : Ops F), (∀ N N' : Submodule ℂ (S4 F), N ≤ N' → ∀ m m', m ≤ m' → O.Fk N m ≤ O.Fk N' m') ∧
    (∀ N m w i, ∀ φ ∈ O.Fk N m, O.x w i φ ∈ O.Fk N (m + 1)) ∧
    ∀ N : Submodule ℂ (S4 F), FiniteDimensional ℂ N → ∀ m, FiniteDimensional ℂ (O.Fk N m) := by
  intro F _ _ _ O
  have hs : ∀ (N : Submodule ℂ (S4 F)) (m : ℕ),
      O.Fk N (m + 1) = O.Fk N m ⊔ ⨆ w, ⨆ i, (O.Fk N m).map (O.x w i) := fun _ _ => rfl
  refine ⟨?_, ?_, ?_⟩
  · intro N N' h m m' hm
    have h1 : ∀ k, O.Fk N k ≤ O.Fk N' k := by
      intro k
      induction k with
      | zero => exact h
      | succ k ih =>
        rw [hs, hs]
        exact sup_le_sup ih (iSup_mono fun w => iSup_mono fun i => Submodule.map_mono ih)
    have h2 : Monotone (O.Fk N') := monotone_nat_of_le_succ fun k => by
      rw [hs]; exact le_sup_left
    exact (h1 m).trans (h2 hm)
  · intro N m w i φ hφ
    rw [hs]
    refine Submodule.mem_sup_right ?_
    refine Submodule.mem_iSup_of_mem w ?_
    refine Submodule.mem_iSup_of_mem i ?_
    exact Submodule.mem_map_of_mem hφ
  · intro N hN m
    induction m with
    | zero => exact hN
    | succ k ih =>
      rw [hs]
      haveI := ih
      haveI : ∀ w : InfinitePlace F, FiniteDimensional ℂ
          (⨆ i, (O.Fk N k).map (O.x w i) : Submodule ℂ (S4 F)) := fun w =>
        Submodule.finiteDimensional_iSup _
      haveI : FiniteDimensional ℂ
          (⨆ w, ⨆ i, (O.Fk N k).map (O.x w i) : Submodule ℂ (S4 F)) :=
        Submodule.finiteDimensional_iSup _
      exact Submodule.finiteDimensional_sup _ _
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

private theorem psi_add {F : Type} [Field F] [NumberField F] (x y : A F) : ψ (x + y) = ψ x * ψ y := by
  simp only [ψ, AddChar.map_add_eq_mul, Circle.coe_mul]

private theorem quaternaryForm_add_left {F : Type} [Field F] [NumberField F] (δ : F) (y a v : V4 F) :
    B4 δ (y + a) v = B4 δ y v + B4 δ a v := by
  simp only [B4, Pi.add_apply]
  ring

private theorem bilinearFour_comm {F : Type} [Field F] [NumberField F] (δ : F) (y v : V4 F) :
    B4 δ y v = B4 δ v y := by
  simp only [B4]
  ring

private theorem quadraticForm_shift_expand {F : Type} [Field F] [NumberField F] (δ : F) (b : A F) (hb : b.2 = 0) (a v : V4 F)
    (ha : ∀ i, (a i).1 = 0) : b * q4 δ (v + a) = b * q4 δ v := by
  have h : ∀ i, b * a i = 0 := fun i => Prod.ext (by
    change b.1 * (a i).1 = 0
    rw [ha i, mul_zero]) (by
    change b.2 * (a i).2 = 0
    rw [hb, zero_mul])
  simp only [q4, Pi.add_apply]
  linear_combination (2 * v 2 + a 2) * h 2 - rt δ * (2 * v 3 + a 3) * h 3 - v 1 * h 0 - (v 0 + a 0) * h 1

theorem UpperTheory.ConvolutionTheory.R2.Fo.fixGen :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) Λ, ∀ φ ∈ Fix D.δ Λ, W.Om (wW F) φ ∈ Fix D.δ Λ ∧ ∀ b : A F, b.2 = 0 → W.Om (nU b) φ ∈ Fix D.δ Λ := by
  intro F E _ _ _ _ _ _ _ D W Λ φ hφ
  refine ⟨?_, fun b hb => ?_⟩
  · intro a ha v
    refine ⟨?_, ?_⟩
    · rw [W.Om_w, W.Om_w]
      unfold ft4
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      have h := (hφ a ha y).2
      change φ.1 y * ψ (B4 D.δ y (v + a)) = φ.1 y * ψ (B4 D.δ y v)
      have e : B4 D.δ y (v + a) = B4 D.δ y v + B4 D.δ a y := by
        rw [bilinearFour_comm D.δ y (v + a), quaternaryForm_add_left, bilinearFour_comm D.δ v y]
      rw [e, psi_add]
      calc φ.1 y * (ψ (B4 D.δ y v) * ψ (B4 D.δ a y))
          = ψ (B4 D.δ y v) * (ψ (B4 D.δ a y) * φ.1 y) := by ring
        _ = φ.1 y * ψ (B4 D.δ y v) := by rw [h]; ring
    · rw [W.Om_w]
      unfold ft4
      rw [← integral_const_mul]
      have key : ∀ y, ψ (B4 D.δ a v) * (φ.1 y * ψ (B4 D.δ y v)) =
          φ.1 (y + a) * ψ (B4 D.δ (y + a) v) := fun y => by
        rw [quaternaryForm_add_left, psi_add, (hφ a ha y).1]
        ring
      simp_rw [key]
      exact integral_add_right_eq_self (μ := adeleMeasurePi F) (fun y => φ.1 y * ψ (B4 D.δ y v)) a
  · intro a ha v
    have ha1 : ∀ i, (a i).1 = 0 := fun i => (ha i).1
    refine ⟨?_, ?_⟩
    · rw [W.Om_n, W.Om_n, quadraticForm_shift_expand D.δ b hb a v ha1, (hφ a ha v).1]
    · rw [W.Om_n, mul_left_comm, (hφ a ha v).2]
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

private noncomputable def UpperTheory.ConvolutionTheory.R2.Fo.mix {F : Type} [Field F] [NumberField F] (g h : G1 F) : G1 F :=
  ⟨Matrix.of fun i j => ((g i j).1, (h i j).2), by
    have hg := g.det_coe
    have hh := h.det_coe
    rw [Matrix.det_fin_two] at hg hh ⊢
    have h1 := congrArg Prod.fst hg
    have h2 := congrArg Prod.snd hh
    exact Prod.ext h1 h2⟩

private theorem UpperTheory.ConvolutionTheory.R2.Fo.mix_apply {F : Type} [Field F] [NumberField F] (g h : G1 F) (i j : Fin 2) :
    mix g h i j = ((g i j).1, (h i j).2) := rfl

private theorem UpperTheory.ConvolutionTheory.R2.Fo.mix_one {F : Type} [Field F] [NumberField F] : mix (1 : G1 F) 1 = 1 := by
  refine Subtype.ext (Matrix.ext fun i j => ?_)
  exact Prod.ext rfl rfl

private theorem UpperTheory.ConvolutionTheory.R2.Fo.mix_mul {F : Type} [Field F] [NumberField F] (g h g' h' : G1 F) :
    mix (g * g') (h * h') = mix g h * mix g' h' := by
  refine Subtype.ext (Matrix.ext fun i j => ?_)
  change mix (g * g') (h * h') i j = (mix g h * mix g' h') i j
  rw [mix_apply, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  exact Prod.ext rfl rfl

theorem UpperTheory.ConvolutionTheory.R2.Fo.proj :
    ∀ (F : Type) [Field F] [NumberField F], ∃ pi pf : G1 F →* G1 F, Continuous pf ∧ ∀ g, FinOne (pi g) ∧ InfOne (pf g) ∧ pi g * pf g = g ∧
    (∀ i j, (pi g i j).1 = (g i j).1) ∧ ∀ i j, (pf g i j).2 = (g i j).2 := by
  intro F _ _
  refine ⟨⟨⟨fun g => mix g 1, mix_one⟩, fun g h => ?_⟩, ⟨⟨fun g => mix 1 g, mix_one⟩, fun g h => ?_⟩, ?_, fun g => ⟨fun _ _ => rfl, fun _ _ => rfl, ?_, fun _ _ => rfl, fun _ _ => rfl⟩⟩
  · change mix (g * h) 1 = mix g 1 * mix h 1
    rw [← mix_mul, one_mul]
  · change mix 1 (g * h) = mix 1 g * mix 1 h
    rw [← mix_mul, one_mul]
  · change Continuous fun g : G1 F => mix 1 g
    refine Continuous.subtype_mk (continuous_matrix fun i j => ?_) _
    have h : Continuous fun g : G1 F => g i j :=
      (continuous_apply_apply i j).comp continuous_subtype_val
    exact continuous_const.prodMk (continuous_snd.comp h)
  · change mix g 1 * mix 1 g = g
    rw [← mix_mul, one_mul, mul_one]
    refine Subtype.ext (Matrix.ext fun i j => ?_)
    exact Prod.ext rfl rfl
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

private theorem cw_sum {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (w : InfinitePlace F)
    (a b : Fin 4 → A F) : cw w (∑ j, a j * b j) = ∑ j, cw w (a j) * cw w (b j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [cw, map_sum, map_mul, Finset.sum_apply, Pi.mul_apply, Complex.ofReal_sum, Complex.ofReal_mul]

theorem UpperTheory.ConvolutionTheory.R2.Fo.lX :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (O : Ops F) (h : GL (Fin 2) (A E)) w i φ, W.L h (O.x w i φ) ∈ Submodule.span ℂ {χ : S4 F | ∃ w' j, χ = O.x w' j (W.L h φ) ∨ χ = O.d w' j (W.L h φ)} := by
  intro F E _ _ _ _ _ _ _ D W O h w i φ
  obtain ⟨ρ, hρ, -, -⟩ := UpperTheory.ConvolutionTheory.R2.D.actMat F E D
  have key : W.L h (O.x w i φ) = ∑ j, cw w ((ρ h⁻¹).val i j) • O.x w j (W.L h φ) := by
    apply Subtype.ext
    funext v
    have hs : ((∑ j, cw w ((ρ h⁻¹).val i j) • O.x w j (W.L h φ) : S4 F)).1 v
        = ∑ j, cw w ((ρ h⁻¹).val i j) * (O.x w j (W.L h φ)).1 v := by
      rw [Submodule.coe_sum, Finset.sum_apply]
      rfl
    rw [hs, W.L_apply, O.x_apply]
    simp only [O.x_apply, W.L_apply]
    have hi : D.act h⁻¹ v i = ∑ j, (ρ h⁻¹).val i j * v j := by
      rw [hρ]; rfl
    rw [hi, cw_sum, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [key]
  refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨w, j, Or.inl rfl⟩)
end
