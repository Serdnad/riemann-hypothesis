module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.OrbitalCosetFiniteness.CvGelfandAlt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1244
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import GroundTheory.AutomorphicForms.Cartan
import GroundTheory.LocalFields.PadicLogSeries
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle005
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.AltSum

@[expose] public section

section

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Th

private lemma avg_const {H : Type} [Group H] (c : ℂ) : GlobalTheory.BCT.avg (fun _ : H => c) = c := by
  have hS : GlobalTheory.BCT.rStab (fun _ : H => c) = ⊤ := by
    ext k
    simp [GlobalTheory.BCT.rStab]
  unfold GlobalTheory.BCT.avg
  rw [hS]
  haveI : Subsingleton (H ⧸ (⊤ : Subgroup H)) := QuotientGroup.subsingleton_quotient_top
  haveI : Unique (H ⧸ (⊤ : Subgroup H)) := Unique.mk' _
  simp [finsum_unique]

private lemma avg_orbit {G : Type} [Group G] (K : Subgroup G) (θ : G →* G) (hθ : ∀ k ∈ K, θ k ∈ K)
    (δ x : G) (h : G → ℂ) (hh : ∀ k ∈ K, ∀ y, h (k * y) = h y ∧ h (y * k) = h y) :
    GlobalTheory.BCT.avg (fun k : K => h ((x * k)⁻¹ * δ * θ (x * k))) = h (x⁻¹ * δ * θ x) := by
  have hc : (fun k : K => h ((x * k)⁻¹ * δ * θ (x * k))) = fun _ : K => h (x⁻¹ * δ * θ x) := by
    funext k
    have e : (x * (k : G))⁻¹ * δ * θ (x * k) = (k : G)⁻¹ * ((x⁻¹ * δ * θ x) * θ k) := by
      simp only [map_mul, mul_inv_rev, mul_assoc]
    rw [e, (hh _ (K.inv_mem k.2) _).1, (hh _ (hθ _ k.2) _).2]
  rw [hc, avg_const]

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Th

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Th.twLin :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Th.TwLin := by
  intro G _ _ _ K _ _ θ hθ δ hfin f g c hf hg
  let W : DoubleCoset.Quotient (GlobalTheory.BCT.twCent θ δ : Set G) (K : Set G) → ℂ := fun q =>
    (((GlobalTheory.BCT.twCent θ δ ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex
      (GlobalTheory.BCT.cptPart (GlobalTheory.BCT.twCent θ δ)) : ℕ) : ℂ)
  let y : DoubleCoset.Quotient (GlobalTheory.BCT.twCent θ δ : Set G) (K : Set G) → G := fun q =>
    (Quotient.out q)⁻¹ * δ * θ (Quotient.out q)
  have form : ∀ h : G → ℂ, (∀ k ∈ K, ∀ z, h (k * z) = h z ∧ h (z * k) = h z) →
      GlobalTheory.BCT.twOrb θ K δ h = ∑ᶠ q, W q * h (y q) := by
    intro h hh
    unfold GlobalTheory.BCT.twOrb
    exact finsum_congr fun q => by rw [avg_orbit K θ hθ δ _ h hh]
  have fin : ∀ h : G → ℂ, GlobalTheory.BCT.IsHecke K h → (Function.support fun q => W q * h (y q)).Finite := by
    intro h hh
    refine (hfin _ hh.1.isCompact).subset fun q hq => ?_
    exact subset_tsupport h (right_ne_zero_of_mul hq)
  have inv : ∀ k ∈ K, ∀ z, (fun u => f u + c * g u) (k * z) = (fun u => f u + c * g u) z ∧
      (fun u => f u + c * g u) (z * k) = (fun u => f u + c * g u) z := by
    intro k hk z
    simp only [(hf.2 k hk z).1, (hf.2 k hk z).2, (hg.2 k hk z).1, (hg.2 k hk z).2, and_self]
  have fin' : (Function.support fun q => c * (W q * g (y q))).Finite :=
    (fin g hg).subset fun q hq => right_ne_zero_of_mul hq
  rw [form _ inv, form f hf.2, form g hg.2, mul_finsum _ c,
    ← finsum_add_distrib (fin f hf) fin']
  exact finsum_congr fun q => by ring
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.BCT GlobalTheory.LFun GroundTheory.Automorphic PositivityTheory.Rg.BcB.G8
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Th

private def trG {F : Type} [Field F] {n : ℕ} (g : GL (Fin n) F) : GL (Fin n) F :=
  ⟨g.val.transpose, (g⁻¹).val.transpose,
    by rw [← Matrix.transpose_mul]; simp,
    by rw [← Matrix.transpose_mul]; simp⟩

private theorem trG_val {F : Type} [Field F] {n : ℕ} (g : GL (Fin n) F) : (trG g).val = g.val.transpose := rfl

private theorem trG_mul {F : Type} [Field F] {n : ℕ} (x y : GL (Fin n) F) : trG (x * y) = trG y * trG x :=
  Units.ext (by simp [trG_val, Matrix.transpose_mul])

private theorem trG_trG {F : Type} [Field F] {n : ℕ} (x : GL (Fin n) F) : trG (trG x) = x :=
  Units.ext (by simp [trG_val])

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

private theorem trG_mem {w : HeightOneSpectrum (𝓞 E)} {k : GL (Fin n) (w.adicCompletion E)}
    (hk : k ∈ KGL w (n := n)) : trG k ∈ KGL w (n := n) := by
  have h := GlobalTheory.StabInt.mem_integralGL_of_mem_KGL hk
  rw [GLnLocal.mem_integralGL_iff] at h
  refine GlobalTheory.StabInt.mem_KGL_of_mem_integralGL ?_
  rw [GLnLocal.mem_integralGL_iff]
  exact ⟨fun i j => h.1 j i, fun i j => h.2 j i⟩

private theorem trG_diagPow (w : HeightOneSpectrum (𝓞 E)) (μ : Fin n → ℤ) :
    trG (Cartan.diagPow (w.adicCompletion E) n μ) = Cartan.diagPow (w.adicCompletion E) n μ :=
  Units.ext (by rw [trG_val, Cartan.coe_diagPow, Matrix.diagonal_transpose])

private theorem trG_double (w : HeightOneSpectrum (𝓞 E)) (x : GL (Fin n) (w.adicCompletion E)) :
    ∃ k ∈ KGL w (n := n), ∃ k' ∈ KGL w (n := n), trG x = k * x * k' := by
  obtain ⟨μ, -, k₁, h₁, k₂, h₂, rfl⟩ := Cartan.exists_eq_mul_diagPow_mul (w.adicCompletion E) n x
  have h₁' := GlobalTheory.StabInt.mem_KGL_of_mem_integralGL h₁
  have h₂' := GlobalTheory.StabInt.mem_KGL_of_mem_integralGL h₂
  refine ⟨trG k₂ * k₁⁻¹, (KGL w (n := n)).mul_mem (trG_mem h₂') ((KGL w (n := n)).inv_mem h₁'),
    k₂⁻¹ * trG k₁, (KGL w (n := n)).mul_mem ((KGL w (n := n)).inv_mem h₂') (trG_mem h₁'), ?_⟩
  rw [trG_mul, trG_mul, trG_diagPow]
  group

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Th

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Th.cvComm2 :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Th.CvGelfand → UpperTheory.V.Z.Tf.GlobalTraceComparison.Th.CvComm2 := by
  intro h E _ _ _ a b w f g hf hg
  obtain ⟨hoa, hca⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a
  obtain ⟨hob, hcb⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b
  refine h (GLw a w × GLw b w) (K2 a b w) (hoa.prod hob) (hca.prod hcb)
    (fun x => (trG x.1, trG x.2)) ?_ ?_ ?_ ?_ f g hf hg
  · intro x y
    exact Prod.ext (trG_mul _ _) (trG_mul _ _)
  · intro x
    exact Prod.ext (trG_trG _) (trG_trG _)
  · intro k hk
    exact ⟨trG_mem hk.1, trG_mem hk.2⟩
  · intro x
    obtain ⟨k₁, h₁, k₂, h₂, e⟩ := trG_double w x.1
    obtain ⟨l₁, i₁, l₂, i₂, e'⟩ := trG_double w x.2
    exact ⟨(k₁, l₁), ⟨h₁, i₁⟩, (k₂, l₂), ⟨h₂, i₂⟩, Prod.ext e e'⟩
end
end

section

open GlobalTheory.BCT UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Th

theorem cvGelfand : CvGelfand :=
  _root_.UpperTheory.Reformulated.B.HeckeGelfandPair.cvGelfand

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Th
end
