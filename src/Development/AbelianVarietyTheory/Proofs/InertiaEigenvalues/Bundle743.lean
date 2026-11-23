module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle400
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle728
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffHeckePolyOfComplex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle555
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle732
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle020
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle717
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle484
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle017
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import ReciprocityTheory.Automorphisms.PlaceA
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.CoefDuty.ExtRing

theorem qCast_trans {a p q : ℕ} [Fact a.Prime] [Fact p.Prime] [Fact q.Prime] (ι : Qbar a ≃+* ℂ) (h₀ : a = p)
    (h₁ : a = q) (hl : p = q) : qCast h₁ ι = qCast hl (qCast h₀ ι) := by
  subst h₀; subst hl; rfl

theorem exists_gens {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (ι : FractionRing O →+* Qbar l)
    (hι : ∀ z : ℤ_[l], ι (algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z)) =
      algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l])) :
    ∃ s : Finset (Qbar l), ∀ x, ι x ∈ Submodule.span ℚ_[l] (s : Set (Qbar l)) := by
  classical
  obtain ⟨K, hK, hfd, -⟩ := GlobalTheory.Proof.CoefField.exists_coefField ι hι
  obtain ⟨t, ht⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℚ_[l] K).FG)
  refine ⟨t.image Subtype.val, fun x => ?_⟩
  have hx : (⟨ι x, (hK _).2 ⟨x, rfl⟩⟩ : K) ∈ Submodule.span ℚ_[l] (t : Set K) := ht ▸ Submodule.mem_top
  have := Submodule.mem_map_of_mem (f := K.val.toLinearMap) hx
  rw [← Submodule.span_image] at this
  rw [Finset.coe_image]
  exact this

theorem exists_ringHom {l₀ l₁ : ℕ} [Fact l₀.Prime] [Fact l₁.Prime] (hl : l₀ = l₁)
    {O₀ : Type} [cr₀ : CommRing O₀] [dm₀ : IsDomain O₀] [dv₀ : IsDiscreteValuationRing O₀] [al₀ : Algebra ℤ_[l₀] O₀]
    [fi₀ : Module.Finite ℤ_[l₀] O₀]
    {O₁ : Type} [cr₁ : CommRing O₁] [dm₁ : IsDomain O₁] [dv₁ : IsDiscreteValuationRing O₁] [al₁ : Algebra ℤ_[l₁] O₁]
    [fi₁ : Module.Finite ℤ_[l₁] O₁]
    (ι₀ : FractionRing O₀ →+* Qbar l₀)
    (hι₀ : ∀ z : ℤ_[l₀], ι₀ (algebraMap O₀ (FractionRing O₀) (algebraMap ℤ_[l₀] O₀ z)) =
      algebraMap ℚ_[l₀] (Qbar l₀) (z : ℚ_[l₀]))
    (ι₁ : FractionRing O₁ →+* Qbar l₁)
    (hι₁ : ∀ z : ℤ_[l₁], ι₁ (algebraMap O₁ (FractionRing O₁) (algebraMap ℤ_[l₁] O₁ z)) =
      algebraMap ℚ_[l₁] (Qbar l₁) (z : ℚ_[l₁]))
    (c₀ : Qbar l₀ ≃+* ℂ) (c₁ : Qbar l₁ ≃+* ℂ) (hc : c₁ = qCast hl c₀) (s : Set (Qbar l₀))
    (hs : ∀ x, ι₀ x ∈ Submodule.span ℚ_[l₀] s) (hs₁ : ∀ y ∈ s, ∃ x, c₁ (ι₁ x) = c₀ y) :
    ∃ φ : O₀ →+* O₁, (∀ z, c₁ (ι₁ (algebraMap O₁ _ (φ z))) = c₀ (ι₀ (algebraMap O₀ _ z))) ∧
      ∀ (z : ℤ_[l₀]) (z' : ℤ_[l₁]), HEq z z' → φ (algebraMap ℤ_[l₀] O₀ z) = algebraMap ℤ_[l₁] O₁ z' := by
  subst hl
  have hc' : ∀ x, c₁ x = c₀ x := fun x => by rw [hc]; rfl
  simp only [hc'] at hs₁ ⊢
  obtain ⟨K₀, hK₀, -, hn₀⟩ := GlobalTheory.Proof.CoefField.exists_coefField ι₀ hι₀
  obtain ⟨K₁, hK₁, -, hn₁⟩ := GlobalTheory.Proof.CoefField.exists_coefField ι₁ hι₁
  have hsK : s ⊆ (K₁ : Set (Qbar l₀)) := by
    intro y hy
    obtain ⟨x, hx⟩ := hs₁ y hy
    exact (hK₁ y).2 ⟨x, c₀.injective hx⟩
  have hspan : Submodule.span ℚ_[l₀] s ≤ K₁.toSubalgebra.toSubmodule := Submodule.span_le.2 hsK
  let f₀ : O₀ →+* Qbar l₀ := ι₀.comp (algebraMap O₀ (FractionRing O₀))
  let f₁ : O₁ →+* Qbar l₀ := ι₁.comp (algebraMap O₁ (FractionRing O₁))
  have hf₁ : Function.Injective f₁ := ι₁.injective.comp (IsFractionRing.injective O₁ (FractionRing O₁))
  have hrange : ∀ z, f₀ z ∈ f₁.range := by
    intro z
    have h1 : f₀ z ∈ K₁ := hspan (hs _)
    obtain ⟨y, hy⟩ := (hK₁ _).1 h1
    have hle : ‖ι₀ (algebraMap O₀ (FractionRing O₀) z)‖ ≤ 1 := (hn₀ _).2 ⟨z, rfl⟩
    have hy1 : ‖ι₁ y‖ ≤ 1 := by rw [hy]; exact hle
    obtain ⟨u, rfl⟩ := (hn₁ y).1 hy1
    exact ⟨u, hy⟩
  let e₁ : O₁ ≃+* f₁.range := RingEquiv.ofBijective f₁.rangeRestrict
    ⟨fun a b h => hf₁ (congrArg Subtype.val h), f₁.rangeRestrict_surjective⟩
  let φ : O₀ →+* O₁ := e₁.symm.toRingHom.comp (f₀.codRestrict f₁.range hrange)
  have hφ : ∀ z, f₁ (φ z) = f₀ z := by
    intro z
    have : e₁ (φ z) = f₀.codRestrict f₁.range hrange z := e₁.apply_symm_apply _
    exact congrArg Subtype.val this
  refine ⟨φ, fun z => congrArg c₀ (hφ z), fun z z' hzz => ?_⟩
  cases eq_of_heq hzz
  apply hf₁
  rw [hφ]
  change ι₀ _ = ι₁ _
  rw [hι₀, hι₁]

end GlobalTheory.CoefDuty.ExtRing

end

end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.UnramDict

theorem fixed_of_mem_KU : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (U : Submodule ℂ (UA L n → ℂ)), IsAutRepU U → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ U0 : Subgroup (GAf L n), (∀ κ, TrivOutside {v} κ → (κ ∈ U0 ↔ κ ∈ Umax L n)) → ∀ (σ : w.adicCompletion L →+* w.adicCompletion L) (b : GL (Fin n) (w.adicCompletion L)), b ∈ GlobalTheory.LFun.KGL w (n := n) → ∀ p : locU n w →* Formalism.UG.GU σ n, (∀ x, (p x).val = b⁻¹ * cLoc w x.val * b) → ∀ φ ∈ U, (∀ g, ∀ κ ∈ U0, φ (F.j (g * κ)) = φ (F.j g)) → ∀ x : locU n w, p x ∈ Formalism.UG.KU σ n → RU L n x.val φ = φ := by
  intro L _ _ _ n F U hU v w hw U0 hU0 σ b hb p hp φ hφU hfix x hK
  obtain rfl : w.under (𝓞 (maximalRealSubfield L)) = v := HeightOneSpectrum.ext hw
  have hK1 : (p x).val ∈ GlobalTheory.LFun.KGL w (n := n) := (Subgroup.mem_subgroupOf.1 hK).2
  have hK2 : cLoc w x.val ∈ GlobalTheory.LFun.KGL w (n := n) := by
    have h : cLoc w x.val = b * (p x).val * b⁻¹ := by rw [hp]; group
    rw [h]
    exact mul_mem (mul_mem hb hK1) (inv_mem hb)
  have hx := x.2
  obtain ⟨y, hy⟩ := F.onto x.val (Subgroup.mem_inf.1 hx).1
  have hyU : y ∈ Umax L n := fun i j => mem_ALint F _ fun u => by
    rw [← F.loc, hy]
    exact cLoc_entry_mem hx hK2 u i j
  have hk (a : L) (z : AFplus L) :
      F.κ.toRingHom (a ⊗ₜ[maximalRealSubfield L] z) =
        algebraMap L _ a * GlobalTheory.AdeleBaseChange.adMap (maximalRealSubfield L) L z := by
    have h1 (z : AFplus L) : F.κ (1 ⊗ₜ z) =
        GlobalTheory.AdeleBaseChange.adMap (maximalRealSubfield L) L z := by
      refine FiniteAdeleRing.ext _ fun q => ?_
      obtain ⟨i, hi, hia⟩ := F.right q (q.under (𝓞 (maximalRealSubfield L))) rfl
      rw [hia]
      change i (z (q.under (𝓞 (maximalRealSubfield L)))) = GlobalTheory.LFun.complMap rfl (z (q.under (𝓞 (maximalRealSubfield L))))
      refine congrFun ((HeightOneSpectrum.denseRange_algebraMap (maximalRealSubfield L)
        (q.under (𝓞 (maximalRealSubfield L)))).equalizer hi
        (GlobalTheory.LFun.InertChart.continuous_complMap rfl) (funext fun k => ?_)) _
      change i (algebraMap _ _ k) = GlobalTheory.LFun.complMap rfl (algebraMap _ _ k)
      rw [GlobalTheory.LFun.complMap_algebraMap]
      have he : (algebraMap (maximalRealSubfield L) (AFplus L) k) (q.under (𝓞 (maximalRealSubfield L))) =
          algebraMap _ (HeightOneSpectrum.adicCompletion (maximalRealSubfield L) (q.under (𝓞 (maximalRealSubfield L)))) k := rfl
      rw [← he, ← hia, Algebra.algebraMap_eq_smul_one (A := AFplus L) k, TensorProduct.tmul_smul,
        TensorProduct.smul_tmul', ← Algebra.algebraMap_eq_smul_one, F.left]
      rfl
    rw [← h1, ← F.left, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rfl
  have hc (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (z : AL L)
      (hz : ∀ u : HeightOneSpectrum (𝓞 L), u.under (𝓞 (maximalRealSubfield L)) = v → F.κ z u = 0) :
      compAt L v z = 0 :=
    (GlobalTheory.AdeleBaseChange.prV_eq_zero_iff (ι := F.κ.toRingHom) hk v z).2 hz
  have hyt : TrivOutside {w.under (𝓞 (maximalRealSubfield L))} y := by
    intro v hv
    refine Matrix.ext fun i j => ?_
    have h0 := hc v (y.1.val i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j) fun u hu => by
      have h := MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hx).2 u)
        (fun e => hv (hu.symm.trans e)))
      have h1 := F.loc y u i j
      rw [hy, h] at h1
      rw [map_sub]
      change F.κ _ u - F.κ _ u = 0
      rw [← h1]
      simp only [Units.val_one, Matrix.one_apply]
      split_ifs <;> simp <;> rfl
    rw [map_sub, sub_eq_zero] at h0
    rw [Matrix.map_apply, h0]
    simp only [Matrix.one_apply]
    split_ifs <;> simp
  have hy0 : y ∈ U0 := (hU0 y hyt).2 hyU
  rw [← sub_eq_zero]
  refine GlobalTheory.DefiniteDense.eq_zero_of_finU L n _ (hU.aut _ (U.sub_mem (hU.stable _ _ hφU) hφU)) fun z hz => ?_
  obtain ⟨g, rfl⟩ := F.onto z hz
  change φ (F.j g * x.val) - φ (F.j g) = 0
  rw [← hy, ← map_mul, sub_eq_zero]
  exact hfix g y hy0

end GlobalTheory.UnramDict

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.LocInteg

theorem kappa_mem_int {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (F : FinIso L n)
    (w : HeightOneSpectrum (𝓞 L)) {z : AL L} (hz : z ∈ ALint L) : F.κ z w ∈ w.adicCompletionIntegers L := by
  induction hz using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨y, rfl⟩ | ⟨a, ha, rfl⟩
    · rw [F.left]
      exact GlobalTheory.AdeleBaseChange.algebraMap_int_mem y w
    · have h := GlobalTheory.UnramDict.kappa_tmul F 1 a
      rw [map_one, one_mul] at h
      change F.κ.toRingHom _ w ∈ _
      rw [h]
      exact GlobalTheory.AdeleBaseChange.adMap_int ha w
  | one => rw [map_one]; exact one_mem _
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb

theorem cLoc_mem_KGL_iff : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (w : HeightOneSpectrum (𝓞 L)) (y : GAf L n), F.j y ∈ locU n w → (cLoc w (F.j y) ∈ GlobalTheory.LFun.KGL w (n := n) ↔ y ∈ Umax L n) := by
  intro L _ _ _ n F w y hy
  constructor
  · intro hK i j
    exact GlobalTheory.UnramDict.mem_ALint F _ fun u => by
      rw [← F.loc]
      exact GlobalTheory.UnramDict.cLoc_entry_mem hy hK u i j
  · intro hyU
    refine GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [F.loc]
      exact kappa_mem_int F w (hyU i j)
    · rw [← map_inv, ← map_inv, F.loc]
      exact kappa_mem_int F w ((inv_mem hyU : y⁻¹ ∈ Umax L n) i j)

end GlobalTheory.LocInteg

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.LocalHeckeLevel

theorem sum_mul_left_eq {Gp M : Type} [Group Gp] [AddCommMonoid M] (K : Subgroup Gp) (α : Gp) (C : Finset Gp)
    (h1 : ∀ γ ∈ C, ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = k₁ * α * k₂)
    (h2 : ∀ x : Gp, (∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * α * k₂) → ∃! γ, γ ∈ C ∧ γ⁻¹ * x ∈ K)
    (F : Gp → M) (hF : ∀ x, ∀ κ ∈ K, F (x * κ) = F x) {k₀ : Gp} (hk₀ : k₀ ∈ K) :
    ∑ δ ∈ C, F (k₀ * δ) = ∑ δ ∈ C, F δ := by
  classical
  have hmem : ∀ k ∈ K, ∀ δ ∈ C, ∃ k₁ ∈ K, ∃ k₂ ∈ K, k * δ = k₁ * α * k₂ := by
    intro k hk δ hδ
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := h1 δ hδ
    exact ⟨k * k₁, K.mul_mem hk hk₁, k₂, hk₂, by simp only [mul_assoc]⟩
  let s : Gp → Gp → Gp := fun k δ =>
    if h : ∃ k₁ ∈ K, ∃ k₂ ∈ K, k * δ = k₁ * α * k₂ then (h2 _ h).exists.choose else δ
  have hs : ∀ k ∈ K, ∀ δ ∈ C, s k δ ∈ C ∧ (s k δ)⁻¹ * (k * δ) ∈ K := by
    intro k hk δ hδ
    have h := hmem k hk δ hδ
    have e : s k δ = (h2 _ h).exists.choose := dif_pos h
    rw [e]
    exact (h2 _ h).exists.choose_spec
  have huniq : ∀ k ∈ K, ∀ δ ∈ C, ∀ γ ∈ C, γ⁻¹ * (k * δ) ∈ K → s k δ = γ := by
    intro k hk δ hδ γ hγ hγK
    exact (h2 _ (hmem k hk δ hδ)).unique (hs k hk δ hδ) ⟨hγ, hγK⟩
  have hinv : ∀ δ ∈ C, s k₀⁻¹ (s k₀ δ) = δ := by
    intro δ hδ
    obtain ⟨hm, hK⟩ := hs k₀ hk₀ δ hδ
    apply huniq _ (K.inv_mem hk₀) _ hm _ hδ
    have e : δ⁻¹ * (k₀⁻¹ * s k₀ δ) = ((s k₀ δ)⁻¹ * (k₀ * δ))⁻¹ := by group
    rw [e]
    exact K.inv_mem hK
  have hinv' : ∀ δ ∈ C, s k₀ (s k₀⁻¹ δ) = δ := by
    intro δ hδ
    obtain ⟨hm, hK⟩ := hs k₀⁻¹ (K.inv_mem hk₀) δ hδ
    apply huniq _ hk₀ _ hm _ hδ
    have e : δ⁻¹ * (k₀ * s k₀⁻¹ δ) = ((s k₀⁻¹ δ)⁻¹ * (k₀⁻¹ * δ))⁻¹ := by group
    rw [e]
    exact K.inv_mem hK
  refine Finset.sum_nbij' (s k₀) (s k₀⁻¹) (fun δ hδ => (hs k₀ hk₀ δ hδ).1)
    (fun δ hδ => (hs _ (K.inv_mem hk₀) δ hδ).1) hinv hinv' ?_
  intro δ hδ
  obtain ⟨_, hK⟩ := hs k₀ hk₀ δ hδ
  calc F (k₀ * δ) = F (s k₀ δ * ((s k₀ δ)⁻¹ * (k₀ * δ))) := by rw [mul_inv_cancel_left]
    _ = F (s k₀ δ) := hF _ _ hK

variable {D : D7}

theorem mt_mul (V : HSp D) (a b : GA D V) : mt V (a * b) = mt V a * mt V b := by
  unfold Formalism.L2.Theta.mt
  rw [map_mul, Units.val_mul]

theorem mt_one (V : HSp D) : mt V 1 = 1 := by
  unfold Formalism.L2.Theta.mt
  rw [map_one, Units.val_one]

theorem mt_injective (V : HSp D) {a b : GA D V} (h : mt V a = mt V b) : a = b :=
  Subtype.val_injective (Units.ext h)

theorem suppF_mul {V : HSp D} {f : AE D} {a b : GA D V} (ha : SuppF V f a) (hb : SuppF V f b) :
    SuppF V f (a * b) := by
  intro i j
  have e : mt V (a * b) - 1 = (mt V a - 1) * mt V b + (mt V b - 1) := by
    rw [mt_mul, sub_mul, one_mul]; abel
  rw [e, Matrix.add_apply, Matrix.mul_apply, mul_add, Finset.mul_sum, hb i j]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← mul_assoc, ha i l]

theorem suppF_inv {V : HSp D} {f : AE D} {a : GA D V} (ha : SuppF V f a) : SuppF V f a⁻¹ := by
  intro i j
  have e : mt V a⁻¹ - 1 = -(mt V a⁻¹ * (mt V a - 1)) := by
    rw [mul_sub, ← mt_mul, inv_mul_cancel, mt_one, mul_one]; abel
  rw [e, Matrix.neg_apply, Matrix.mul_apply, mul_neg, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_left_comm, ha l j]

theorem suppF_one (V : HSp D) (f : AE D) : SuppF V f (1 : GA D V) := by
  intro i j
  simp [mt_one]

def suppSub (V : HSp D) (f : AE D) : Subgroup (GA D V) where
  carrier := {g | SuppF V f g}
  mul_mem' := suppF_mul
  one_mem' := suppF_one V f
  inv_mem' := suppF_inv

theorem comm_of_suppF_trivAt {V : HSp D} {f : AE D} {a b : GA D V} (ha : SuppF V f a) (hb : TrivAt V f b) :
    a * b = b * a := by
  apply mt_injective
  have hAB : (mt V a - 1) * (mt V b - 1) = 0 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [← ha i l, mul_assoc, mul_left_comm, hb l j, mul_zero]
  have hBA : (mt V b - 1) * (mt V a - 1) = 0 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [← ha l j, mul_left_comm, ← mul_assoc, hb i l, zero_mul]
  have e1 : mt V a * mt V b = (mt V a - 1) * (mt V b - 1) + mt V a + mt V b - 1 := by noncomm_ring
  have e2 : mt V b * mt V a = (mt V b - 1) * (mt V a - 1) + mt V b + mt V a - 1 := by noncomm_ring
  rw [mt_mul, mt_mul, e1, e2, hAB, hBA, zero_add, zero_add, add_comm (mt V a)]

theorem heckeOn_mem_wall : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m}, LevProd R i → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (f : AE D), IsFinIdem D v f → ∀ (α : GA D (Wc D i)), SuppF (Wc D i) f α → ∀ (C : Finset (GA D (Wc D i))), (∀ γ ∈ C, SuppF (Wc D i) f γ) → IsCosetRep (Wc D i) {k | k ∈ levW R i ∧ SuppF (Wc D i) f k} α C → ∀ T ∈ R.Wall i (sg0 D A), heckeOn (R.MW i (sg0 D A)) C T ∈ R.Wall i (sg0 D A) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R i hLP v f hf α _ C hC hrep Tm hT
  obtain ⟨hle, hchi, cmp, hcmp1, hcmp2⟩ := hLP
  have hT' : IsMultMap R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv))
      (levChi _ (R.βW i) (R.datWp i R.triv)) Tm := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 hT
  refine (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).2
    (GlobalTheory.HeckeParts.isMultMap_heckeOn hT' (fun γ hγ => (hrep.1 γ hγ).1) ?_)
  intro w κ hκ g
  have hκ' : κ ∈ levW R i := hκ
  rw [hchi κ hκ', one_mul]
  show ∑ δ ∈ C, Tm w (g * κ * δ) = ∑ δ ∈ C, Tm w (g * δ)
  have hF : ∀ x, ∀ c ∈ levW R i, Tm w (x * c) = Tm w x := fun x c hc => by
    rw [hT'.lev w c hc x, hchi c hc, one_mul]
  obtain ⟨hs, ht⟩ := hcmp1 v f hf κ
  have hkv : cmp v κ ∈ levW R i := ((hcmp2 κ (hle hκ')).1.1 hκ') v
  have hk' : κ * (cmp v κ)⁻¹ ∈ levW R i := mul_mem hκ' (inv_mem hkv)
  calc ∑ δ ∈ C, Tm w (g * κ * δ) = ∑ δ ∈ C, Tm w (g * (κ * (cmp v κ)⁻¹) * (cmp v κ * δ)) :=
        Finset.sum_congr rfl fun δ _ => by group
    _ = ∑ δ ∈ C, Tm w (g * (κ * (cmp v κ)⁻¹) * δ) :=
        sum_mul_left_eq (levW R i ⊓ suppSub (Wc D i) f) α C (fun γ hγ => (hrep.1 γ hγ).2)
          (fun x hx => hrep.2 x hx) (fun x => Tm w (g * (κ * (cmp v κ)⁻¹) * x))
          (fun x c hc => by simp only [← mul_assoc]; exact hF _ c hc.1) (k₀ := cmp v κ) ⟨hkv, hs⟩
    _ = ∑ δ ∈ C, Tm w (g * δ) := Finset.sum_congr rfl fun δ hδ => by
        rw [mul_assoc, ← comm_of_suppF_trivAt (hC δ hδ) ht, ← mul_assoc, hF _ _ hk']

end GlobalTheory.LocalHeckeLevel

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.IndexCount

theorem rank_le (D : D7) (i : Fin D.R.m) : 2 * (Wc D i).rank + 5 ≤ (Vc D i).rank := by
  have hV : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have hW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have := D.R.rank_add_five_le
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  omega

theorem two_le_absNorm {D : D7} (v : HeightOneSpectrum (𝓞 D.host.F)) : (2 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  have : 2 ≤ Ideal.absNorm v.asIdeal := by omega
  exact_mod_cast this

theorem indexSum_of_rank {D : D7} (W : HSp D) (n : ℕ) (hn : 2 * W.rank + 5 ≤ n) : IndexSum W n := by
  let q : HeightOneSpectrum (𝓞 D.host.F) → ℝ := fun v => (Ideal.absNorm v.asIdeal : ℝ)
  let z : HeightOneSpectrum (𝓞 D.host.F) → ℝ := fun v =>
    (∏ i ∈ Finset.range W.rank, (1 - q v ^ ((i : ℝ) - (n : ℝ) / 2))⁻¹) ^ 2 - 1
  have hq : ∀ v, 2 ≤ q v := fun v => two_le_absNorm v
  have hσ : (W.rank : ℝ) + 5 / 2 ≤ (n : ℝ) / 2 := by
    have : ((2 * W.rank + 5 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at this; linarith
  have hz : ∀ v, z v < 1 ∧ z v ≤ 16 * q v ^ (-(3 : ℝ)) := fun v => GlobalTheory.lattice_zeta_sq_bound (q v) W.rank ((n : ℝ) / 2) (hq v) hσ
  have h8 : ∀ v, 8 * q v ^ (-(4 : ℝ)) ≤ 8 * q v ^ (-(3 : ℝ)) ∧ 8 * q v ^ (-(4 : ℝ)) ≤ 1 / 2 := by
    intro v
    have h1 : (1 : ℝ) ≤ q v := le_trans (by norm_num) (hq v)
    have hle : q v ^ (-(4 : ℝ)) ≤ q v ^ (-(3 : ℝ)) := Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
    refine ⟨by linarith, ?_⟩
    have : q v ^ (-(4 : ℝ)) ≤ (2 : ℝ) ^ (-(4 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) (hq v) (by norm_num)
    have h2 : (2 : ℝ) ^ (-(4 : ℝ)) = 1 / 16 := by
      rw [Real.rpow_neg (by norm_num)]; norm_num
    rw [h2] at this; linarith
  refine ⟨fun v => max (z v) (8 * q v ^ (-(4 : ℝ))), ?_, ?_, ?_⟩
  · have hs : Summable fun v : HeightOneSpectrum (𝓞 D.host.F) => 16 * q v ^ (-(3 : ℝ)) :=
      (GlobalTheory.summable_absNorm_rpow_heightOneSpectrum D.host.F 3 (by norm_num)).mul_left 16
    refine Summable.of_nonneg_of_le (fun v => ?_) (fun v => ?_) hs
    · exact le_trans (by positivity) (le_max_right _ _)
    · refine max_le (hz v).2 ?_
      have h3 : 0 ≤ q v ^ (-(3 : ℝ)) := by positivity
      linarith [(h8 v).1]
  · intro v
    exact max_lt (hz v).1 (by linarith [(h8 v).2])
  · intro v f hf C hC hd
    rcases GlobalTheory.T.finite_place_split_idempotent_or_inert D v f hf with hs | hi
    · exact le_trans (GlobalTheory.T.split_place_lattice_index_sum_le_zeta_sq_sub_one D W n hn v f hf hs C hC hd) (le_max_left _ _)
    · exact le_trans (GlobalTheory.T.inertPlace_latticeIndex_sum_bound D W n hn v f hf hi C hC hd) (le_max_right _ _)

theorem indexSum_holds : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ i, IndexSum (Wc D i) (Vc D i).rank := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F _ _ i
  exact indexSum_of_rank (Wc D i) (Vc D i).rank (rank_le D i)

end GlobalTheory.IndexCount

end
end
