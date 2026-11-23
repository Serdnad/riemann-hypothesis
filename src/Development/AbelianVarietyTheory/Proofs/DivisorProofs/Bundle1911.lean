module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianLatticeLocalBases
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledBlockSumSelfDualTraceSkewForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFinWeil
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1886
import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle247
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle077
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOfBalanced
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryHeckeCharacterValues
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle077
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle163
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle198
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle168
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.LeafHypothesesConst
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (skewGram)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped nonZeroDivisors
open GlobalTheory.TripleSpaceW (conjSub mem_conjSub conjO coe_conjO)
open GlobalTheory.SkewLat (scLat pairLat)
open GlobalTheory.SkewLat.DualPair

noncomputable section

namespace GlobalTheory.SkewLat.DualPairConj

variable {D : D7}

theorem mem_conj_scLat {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {y : Fin n → D.host.E} :
    y ∈ conjSub (scLat D.host.AA (conjSub Λ)) ↔ ∀ c ∈ D.host.AA⁻¹, star c • y ∈ Λ := by
  rw [mem_conjSub, GlobalTheory.SkewLat.mem_scLat]
  refine forall_congr' fun c => forall_congr' fun _ => ?_
  have e : star (c • star y) = star c • y := by
    ext i; simp only [Pi.star_apply, Pi.smul_apply, smul_eq_mul, star_mul', star_star]
  rw [mem_conjSub, e]

theorem star_smul_mem {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {a : D.host.E} (ha : a ∈ D.host.AA)
    {s : Fin n → D.host.E} (hs : s ∈ Λ) : star a • s ∈ conjSub (scLat D.host.AA (conjSub Λ)) := by
  refine mem_conj_scLat.2 fun c hc => ?_
  obtain ⟨b, hb⟩ := int_of_inv_mul hc ha
  rw [smul_smul, ← star_mul', ← hb, ← coe_conjO]
  exact Λ.smul_mem (conjO b) hs

theorem fwd' (hs : ∀ c ∈ D.host.AA, star c ∈ D.host.AAbar) (S : HSp D)
    {Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    (hΛ : IsSelfDualC S Λ) {x y : Fin S.rank → D.host.E} (hx : x ∈ conjSub (scLat D.host.AA (conjSub Λ)))
    (hy : y ∈ conjSub (scLat D.host.AA (conjSub Λ))) :
    IntTr (D.host.xi0 * hS S x y) := by
  rw [mem_conj_scLat] at hx hy
  have key : ∀ u ∈ D.host.AA * D.host.AA⁻¹, ∀ v ∈ D.host.AA * D.host.AA⁻¹,
      IntTr (D.host.xi0 * u * star v * hS S x y) := by
    intro u hu
    refine FractionalIdeal.mul_induction_on hu
      (C := fun u => ∀ v ∈ D.host.AA * D.host.AA⁻¹, IntTr (D.host.xi0 * u * star v * hS S x y)) ?_ ?_
    · intro a ha c hc v hv
      refine FractionalIdeal.mul_induction_on hv
        (C := fun v => IntTr (D.host.xi0 * (a * c) * star v * hS S x y)) ?_ ?_
      · intro a' ha' c' hc'
        obtain ⟨b, hb⟩ := (hΛ.2 (star c' • y)).1 (hy c' hc') (star c • x) (hx c hc)
        have e1 : D.host.xi0 * (a * c) * star (a' * c') * hS S x y = D.host.xi0 * a * star a' * (b : D.host.E) := by
          rw [hb, show (∑ i, ∑ j, star ((star c • x) i) * S.gram i j * (star c' • y) j) =
            hS S (star c • x) (star c' • y) from rfl, hS_smul, star_mul', star_star]
          ring
        rw [e1]
        exact ((intTr_iff_mem_dual _).2 (xi_mem hs ha ha')).mul_int b
      · intro v1 v2 h1 h2
        rw [star_add, show D.host.xi0 * (a * c) * (star v1 + star v2) * hS S x y =
          D.host.xi0 * (a * c) * star v1 * hS S x y + D.host.xi0 * (a * c) * star v2 * hS S x y by ring]
        exact h1.add h2
    · intro u1 u2 h1 h2 v hv
      rw [show D.host.xi0 * (u1 + u2) * star v * hS S x y =
        D.host.xi0 * u1 * star v * hS S x y + D.host.xi0 * u2 * star v * hS S x y by ring]
      exact (h1 v hv).add (h2 v hv)
  have := key 1 one_mem_AA_mul 1 one_mem_AA_mul
  simpa using this

theorem bwd' (hc : ∀ c ∈ D.host.AAbar, star c ∈ D.host.AA) (S : HSp D)
    {Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} (hΛ : IsSelfDualC S Λ) {y : Fin S.rank → D.host.E}
    (h : ∀ a ∈ D.host.AA, ∀ s ∈ Λ, IntTr (D.host.xi0 * hS S (star a • s) y)) :
    y ∈ conjSub (scLat D.host.AA (conjSub Λ)) := by
  refine mem_conj_scLat.2 fun c hcA => ?_
  refine (hΛ.2 (star c • y)).2 fun s hs => ?_
  have hmem : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (hS S s y) *
      (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AA) ≤ D.host.AAbar *
      (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AA) := by
    rw [show D.host.AAbar * (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AA) =
      FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AA * D.host.AAbar by ring, hX,
      ← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, FractionalIdeal.mul_le]
    intro i hi j hj
    obtain ⟨z, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hi
    have h1 := (intTr_iff_mem_dual _).1 (h j hj s hs)
    rw [hS_smul_left, star_star] at h1
    rw [smul_mul_assoc, show hS S s y * D.host.xi0 * j = D.host.xi0 * (j * hS S s y) by ring]
    exact Submodule.smul_mem _ z h1
  have hXne : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AA ≠ 0 :=
    mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.2 xi_ne) AA_ne
  have hle : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (hS S s y) ≤ D.host.AAbar := by
    calc FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (hS S s y)
        = FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (hS S s y) *
          (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AA) *
          (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AA)⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ hXne, mul_one]
      _ ≤ D.host.AAbar * (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AA) *
          (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AA)⁻¹ := by gcongr
      _ = D.host.AAbar := by rw [mul_assoc, mul_inv_cancel₀ hXne, mul_one]
  obtain ⟨b, hb⟩ := int_of_inv_mul hcA (hc _ (hle (FractionalIdeal.mem_spanSingleton_self _ _)))
  refine ⟨conjO b, ?_⟩
  have e : ((conjO b : 𝓞 D.host.E) : D.host.E) = hS S s (star c • y) := by
    rw [coe_conjO, hb, star_mul', star_star, hS_smul_right]
  first | exact e | exact e.symm

end GlobalTheory.SkewLat.DualPairConj


open GlobalTheory.SkewLat.DualPairConj in
theorem GlobalTheory.SkewLat.pairLat_conj_trace_selfDual : ∀ {D : D7} (A B : HSp D)
    {ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)} {ΛB : Submodule (𝓞 D.host.E) (Fin B.rank → D.host.E)},
    IsSelfDualC A ΛA → IsSelfDualC B ΛB → ∀ {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) (y : Fin d → D.host.E),
    y ∈ pairLat (scLat D.host.AA ΛA) (conjSub (scLat D.host.AA (conjSub ΛB))) e ↔
      ∀ x ∈ pairLat (scLat D.host.AA ΛA) (conjSub (scLat D.host.AA (conjSub ΛB))) e,
      ∀ o : 𝓞 D.host.E, IsIntegral ℤ (Algebra.trace ℚ D.host.E (o * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram A B e) y x)) := by
  intro D A B ΛA ΛB hA hB d e y
  have hs : ∀ c ∈ D.host.AA, star c ∈ D.host.AAbar := fun c h => by
    rw [Formalism.BasicNotions.Examples₂.star_eq_conj]; exact Formalism.L2.Pj.conj_mem_AAbar D h
  have hc : ∀ c ∈ D.host.AAbar, star c ∈ D.host.AA := by
    first | exact GlobalTheory.star_mem_AA_of_mem_AAbar | exact GlobalTheory.star_mem_AA_of_mem_AAbar D | (intros; apply GlobalTheory.star_mem_AA_of_mem_AAbar; assumption)
  constructor
  · intro hy x hx o
    have hy' := GlobalTheory.SkewLat.mem_pairLat.1 hy
    have hx' := GlobalTheory.SkewLat.mem_pairLat.1 hx
    rw [form_skewGram, mul_add]
    exact ((fwd hs A hA hx'.1 hy'.1).add (fwd' hs B hB hx'.2 hy'.2)) o
  · intro h
    refine GlobalTheory.SkewLat.mem_pairLat.2 ⟨bwd hc A hA fun a ha s hs' => ?_, bwd' hc B hB fun a ha s hs' => ?_⟩
    · let x : Fin d → D.host.E := fun i => Sum.elim (fun k => a * s k) (fun _ => 0) (e.symm i)
      have hxA : (fun k => x (e (.inl k))) = a • s := by ext k; simp [x]
      have hxB : (fun k => x (e (.inr k))) = 0 := by ext k; simp [x]
      have hx : x ∈ pairLat (scLat D.host.AA ΛA) (conjSub (scLat D.host.AA (conjSub ΛB))) e := by
        refine GlobalTheory.SkewLat.mem_pairLat.2 ⟨?_, ?_⟩
        · rw [hxA]; exact smul_mem_scLat ha hs'
        · rw [hxB]; exact zero_mem _
      intro o
      have := h x hx o
      rwa [form_skewGram, hxA, hxB, hS_zero_left, add_zero] at this
    · let x : Fin d → D.host.E := fun i => Sum.elim (fun _ => 0) (fun k => star a * s k) (e.symm i)
      have hxA : (fun k => x (e (.inl k))) = 0 := by ext k; simp [x]
      have hxB : (fun k => x (e (.inr k))) = star a • s := by ext k; simp [x]
      have hx : x ∈ pairLat (scLat D.host.AA ΛA) (conjSub (scLat D.host.AA (conjSub ΛB))) e := by
        refine GlobalTheory.SkewLat.mem_pairLat.2 ⟨?_, ?_⟩
        · rw [hxA]; exact zero_mem _
        · rw [hxB]; exact star_smul_mem ha hs'
      intro o
      have := h x hx o
      rwa [form_skewGram, hxA, hxB, hS_zero_left, zero_add] at this

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilProduct

open GlobalTheory.FinWeilO GlobalTheory.FinWeil GlobalTheory.SplitScalar

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
  {χS χT : (AE D)ˣ →* Circle} {of oi : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem actO_mul (g g' : GA D S) (h h' : GA D T) (u : WO S T) :
    actO S T (g * g') (h * h') u = actO S T g h (actO S T g' h' u) := by
  unfold actO
  rw [_root_.mul_inv_rev, mt_mul, mt_mul]
  simp only [Matrix.mul_assoc]

theorem actO_one (u : WO S T) : actO S T 1 1 u = u := by
  unfold actO
  rw [inv_one, mt_one, mt_one, Matrix.one_mul, Matrix.mul_one]

theorem exists_parts (p : GA D S × GA D T) : ∃ a ∈ GinfC S, ∃ b ∈ GinfC T, ∃ k ∈ GfC S, ∃ l ∈ GfC T,
    p = (a, b) * (k, l) ∧ p = (k, l) * (a, b) := by
  obtain ⟨a, ha, k, hk, e1⟩ := (GlobalTheory.UnitarySplit.real_finite_split D S).1 p.1
  obtain ⟨b, hb, l, hl, e2⟩ := (GlobalTheory.UnitarySplit.real_finite_split D T).1 p.2
  refine ⟨a, ha, b, hb, k, hk, l, hl, Prod.ext e1 e2, Prod.ext ?_ ?_⟩
  · exact e1.trans ((GlobalTheory.UnitarySplit.real_finite_split D S).2.1 a ha k hk)
  · exact e2.trans ((GlobalTheory.UnitarySplit.real_finite_split D T).2.1 b hb l hl)

theorem fin_eq_smul (hψ : IsStdChar D ψ (-1)) (hf : IsFinWeil ψ S T ΛS ΛT χS χT of) {w : 𝓞 D.host.E} {lam : ℕ →* ℂ}
    (hlam : GlobalTheory.FinWeil.GoodNorm (sgO D) lam) {Om : GA D S × GA D T →* Module.End ℂ (thetaSub ψ S T)}
    (h : IsLatRep hψ.1 ΛS ΛT w lam Om) (p : GA D S × GA D T) :
    ∃ c : ℂ, ∀ f : thetaSub ψ S T, of p f = c • (Om p f : WO S T → ℂ) := by
  obtain ⟨a, ha, b, hb, k, hk, l, hl, -, rfl⟩ := exists_parts p
  obtain ⟨om, hom⟩ := exists_extend (thetaSub ψ S T) Om
  have ho : ∀ p f (hf : IsThetaFunO ψ S T f), om p f = (Om p ⟨f, hf⟩ : WO S T → ℂ) := fun p f hf => hom p ⟨f, hf⟩
  obtain ⟨c, -, hc⟩ := GlobalTheory.T.schurLemma_thetaFunctions_orientedPair D ψ hψ S T (of (k, l) * om (k⁻¹, l⁻¹))
    (fun f h1 => by
      rw [Module.End.mul_apply, ho _ f h1]
      exact hf.pres _ _ (Om _ ⟨f, h1⟩).2)
    (fun u f h1 => by
      obtain ⟨f', e1, e2⟩ := h.Heisenberg₂ hψ (inv_mem hk) (inv_mem hl) u ⟨f, h1⟩
      have e1' : (f' : WO S T → ℂ) = heisO ψ S T u f := e1
      rw [Module.End.mul_apply, Module.End.mul_apply, ← e1', hom, e2, hf.Heisenberg₂ k hk l hl _ _ (Om _ ⟨f, h1⟩).2,
        ← actO_mul, mul_inv_cancel, mul_inv_cancel, actO_one, ho _ f h1])
    (fun μ 𝓕 hμ h𝓕 f h1 => by
      rw [Module.End.mul_apply, ho _ f h1, hf.unit μ 𝓕 hμ h𝓕 _ _ (Om _ ⟨f, h1⟩).2]
      exact h.unit hlam μ 𝓕 hμ h𝓕 _ ⟨f, h1⟩)
  refine ⟨c, fun f => ?_⟩
  have e := hc _ (Om (k, l) f).2
  rw [Module.End.mul_apply, hom, ← Module.End.mul_apply, ← map_mul,
    show ((k⁻¹, l⁻¹) : GA D S × GA D T) * (k, l) = 1 from inv_mul_cancel ((k, l) : GA D S × GA D T), map_one,
    Module.End.one_apply] at e
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hf.triv a ha b hb _ f.2, h.real_triv ha hb, e]

theorem fin_inf_comm (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (hf : IsFinWeil ψ S T ΛS ΛT χS χT of) (hi : IsInfWeil ψ θ S T oi) (p q : GA D S × GA D T) {f : WO S T → ℂ}
    (h1 : IsThetaFunO ψ S T f) : of p (oi q f) = oi q (of p f) := by
  obtain ⟨lam, hlam, -⟩ := GlobalTheory.FinWeil.exists_goodNorm D
  obtain ⟨w, Om, h⟩ := exists_isLatRep hψ hS hT hlam
  obtain ⟨c, hc⟩ := fin_eq_smul hψ hf hlam h p
  obtain ⟨a, ha, b, hb, k, hk, l, hl, rfl, -⟩ := exists_parts q
  let L : thetaSub ψ S T →ₗ[ℂ] thetaSub ψ S T := (oi (a, b)).restrict fun g hg => hi.pres _ g hg
  have hL : ∀ m, (L m : WO S T → ℂ) = oi (a, b) m := fun _ => rfl
  have e := congrArg Subtype.val (h.comm L (fun x v => Subtype.ext (by
    have e1 := congrArg XF.val (rhoF_real ha hb x)
    rw [coe_rhoF] at e1
    rw [hL, coe_opF, coe_opF, hL, map_smul, hi.Heisenberg₂ a ha b hb _ _ v.2, e1])) p ⟨f, h1⟩)
  rw [map_mul, Module.End.mul_apply, Module.End.mul_apply, hi.triv k hk l hl _ h1,
    hi.triv k hk l hl _ (hf.pres _ _ h1), hc ⟨f, h1⟩, map_smul, ← hL, ← e, ← hc]
  rfl

theorem eventually_smul (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (hf : IsFinWeil ψ S T ΛS ΛT χS χT of) {f : WO S T → ℂ} (h1 : IsThetaFunO ψ S T f) :
    ∀ᶠ p in 𝓝 (1 : GA D S × GA D T), ∃ c : ℂ, of p f = c • f := by
  obtain ⟨lam, hlam, -⟩ := GlobalTheory.FinWeil.exists_goodNorm D
  obtain ⟨w, Om, h⟩ := exists_isLatRep hψ hS hT hlam
  filter_upwards [h.eventually_fix hS hT ⟨f, h1⟩] with p hp
  obtain ⟨c, hc⟩ := fin_eq_smul hψ hf hlam h p
  exact ⟨c, by rw [hc ⟨f, h1⟩, hp]⟩

theorem continuous_product (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (hf : IsFinWeil ψ S T ΛS ΛT χS χT of) (hi : IsInfWeil ψ θ S T oi) {f : WO S T → ℂ}
    (h1 : IsThetaFunO ψ S T f) (u : WO S T) : Continuous fun p : GA D S × GA D T => of p (oi p f) u := by
  haveI : IsTopologicalGroup (GA D S) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig S.gram))
  haveI : IsTopologicalGroup (GA D T) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig T.gram))
  refine continuous_iff_continuousAt.2 fun q => ?_
  have h2 : Filter.Tendsto (fun p => p * q⁻¹) (𝓝 q) (𝓝 1) :=
    (continuous_id.mul continuous_const).tendsto' q 1 (mul_inv_cancel q)
  have h3 := hf.pres q f h1
  have h4 : ∀ᶠ p in 𝓝 q, ∃ c : ℂ, of p f = c • of q f := by
    filter_upwards [h2.eventually (eventually_smul hψ hS hT hf h3)] with p hp
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right] at hp
  by_cases h0 : of q f = 0
  · refine continuousAt_const.congr (f := fun _ => (0 : ℂ)) ?_
    filter_upwards [h4] with p hp
    obtain ⟨c, hc⟩ := hp
    rw [fin_inf_comm hψ hS hT hf hi p p h1, hc, h0, smul_zero, map_zero]
    rfl
  · obtain ⟨x, hx⟩ := Function.ne_iff.1 h0
    have hx' : of q f x ≠ 0 := hx
    refine (((hf.cont f h1 x).div_const (of q f x)).mul (hi.cont _ h3 u)).continuousAt.congr ?_
    filter_upwards [h4] with p hp
    obtain ⟨c, hc⟩ := hp
    show of p f x / of q f x * oi p (of q f) u = _
    rw [fin_inf_comm hψ hS hT hf hi p p h1, hc, map_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
      mul_div_cancel_right₀ _ hx']

end GlobalTheory.WeilProduct

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.BlockForms

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ} (X Y : Matrix (Fin n) (Fin r) E)

structure IsAdapted (C : GL (Fin n) E) : Prop where
  le : 2 * r ≤ n
  colX : ∀ (i : Fin n) (j : Fin r), i.val = j.val → ∀ k, C.1 k i = X k j
  columnBlock : ∀ (i : Fin n) (j : Fin r), i.val + j.val + 1 = n → ∀ k, C.1 k i = Y k j
  perpX : ∀ i : Fin n, r ≤ i.val → i.val + r < n → (cT (σ : E →+* E) X * J) *ᵥ (fun k => C.1 k i) = 0
  perpY : ∀ i : Fin n, r ≤ i.val → i.val + r < n → (cT (σ : E →+* E) Y * J) *ᵥ (fun k => C.1 k i) = 0

def blkCols {l d : ℕ} (h : l + d ≤ r) (Z : Matrix (Fin n) (Fin r) E) : Matrix (Fin n) (Fin d) E :=
  Z.submatrix id fun j => ⟨l + j.val, by omega⟩

def IsBlockEmb {l d : ℕ} (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J) : Prop :=
  ∃ (Φ : AF F ⊗[F] E ≃+* AdeleRing (𝓞 E) E) (j : Ainf F ⊗[F] E ≃+* InfiniteAdeleRing E),
    Continuous Φ ∧ Continuous Φ.symm ∧ (∀ x : E, j ((1 : Ainf F) ⊗ₜ[F] x) = algebraMap E (InfiniteAdeleRing E) x) ∧
    (∀ z, Φ z = (j (GlobalTheory.LFun.infTens F E z), GlobalTheory.LFun.finAdEquiv F E (GlobalTheory.LFun.finTens F E z))) ∧
    ∀ g : GlobalTheory.CuspRep.GA E d, (matHom _ σ J (ι g)).1 =
      1 + adMat F (blkCols h X) * (g.1.map Φ.symm - 1) * adMat F (cT (σ : E →+* E) (blkCols h Y) * J) +
        adMat F (blkCols h Y) * (cT (sigR (AF F) σ) ((g⁻¹).1.map Φ.symm) - 1) *
          adMat F (cT (σ : E →+* E) (blkCols h X) * J)


end GlobalTheory.BlockForms

end
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
noncomputable section

namespace GlobalTheory.NuCharNorm

open Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.Mem.Chr.IdlFact GlobalTheory.Mem.LocTriv
open GlobalTheory.Mem.Chr (finPartI unitIdl locF)
open GlobalTheory.NormSum.UnramHecke GlobalTheory.Mem.Col2.SplitChar

section General

variable {L : Type} [Field L] [NumberField L] {F : Type} [Field F] [NumberField F] [Algebra F L]

theorem inf_upF (χ : HChar L) (k : Fˣ) : χ.inf (upF F k) = ∏ w : InfinitePlace F, χ.resInf w k := by
  classical
  rw [HChar.inf, MonoidHom.comp_apply, infDiag, MonoidHom.finsetProd_apply, map_prod,
    ← Finset.prod_fiberwise Finset.univ fun w : InfinitePlace L => w.comap (algebraMap F L)]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [HChar.resInf_apply]
  exact Finset.prod_congr (by ext; simp [aboveInf]) fun _ _ => rfl

end General

theorem norm_killed (D : D7) (χ : HChar D.host.E) (ht : χ.TrivOn D.host.F) (M : ℕ) (hM : 0 < M)
    (hker : ∀ a : Ideles D.host.E, a ∈ unitIdl D.host.E → (∀ w, (a : AdeleRing (𝓞 D.host.E) D.host.E).1 w = 1) →
      (∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v ((a : AdeleRing (𝓞 D.host.E) D.host.E).2 P - 1) ≤
        Valued.v ((M : D.host.E) : P.adicCompletion D.host.E)) → χ.1 a = 1)
    (x : (AE D)ˣ) : χ.1 (finIdl D (x * sgU D x)) = 1 := by
  have hfin : ∀ k : (D.host.F)ˣ, χ.1 (finIdl D (incU D (upF D.host.F k))) = 1 := fun k => by
    have h1 := χ.2.2 (upF D.host.F k)
    rw [← GlobalTheory.Mem.ChiLaws.infDiag_mul_finPart, map_mul, ← finIdl_incU] at h1
    have h2 : χ.inf (upF D.host.F k) = 1 := by
      rw [inf_upF]
      exact Finset.prod_eq_one fun w _ => ht.2 w k
    rw [HChar.inf, MonoidHom.comp_apply] at h2
    rw [h2, one_mul] at h1
    exact h1
  obtain ⟨n, hn, hx⟩ := GlobalTheory.HeckeVal.exists_denom D ((x⁻¹ : (AE D)ˣ) : AE D)
  obtain ⟨a, r, hr, e⟩ := exists_approx (x : AE D) (Nat.mul_pos (Nat.mul_pos prod_g_pos hM) hn)
  have hs : -(r * ((n : AE D) * ((x⁻¹ : (AE D)ˣ) : AE D))) ∈ OhE D := neg_mem (mul_mem hr hx)
  have h1 : inc D a * ((x⁻¹ : (AE D)ˣ) : AE D) - 1 =
      ((∏ i, D.host.g i : ℕ) : AE D) * ((M : AE D) * -(r * ((n : AE D) * ((x⁻¹ : (AE D)ˣ) : AE D)))) := by
    rw [Nat.cast_mul, Nat.cast_mul] at e
    linear_combination x.mul_inv - ((x⁻¹ : (AE D)ˣ) : AE D) * e
  generalize -(r * ((n : AE D) * ((x⁻¹ : (AE D)ˣ) : AE D))) = s at hs h1
  generalize hG : ((∏ i, D.host.g i : ℕ) : AE D) = G at h1
  have hGm : G ∈ OhE D := hG ▸ natCast_mem _ _
  have hGs : sgA D G = G := hG ▸ map_natCast _ _
  have hMs : sgA D (M : AE D) = M := map_natCast _ _
  have ha : a ≠ 0 := by
    rintro rfl
    obtain ⟨v, hv⟩ := GlobalTheory.exists_heightOneSpectrum_natCast_mem D.host.E (D.host.g_prime 0)
    have := vl_cong (mul_mem (natCast_mem _ M) hs) 0 v hv
    rw [hG, ← h1, map_zero, zero_mul, zero_sub, Valuation.map_neg, map_one] at this
    exact lt_irrefl _ this
  let z : (AE D)ˣ := incU D (Units.mk0 a ha) * x⁻¹
  have hz : (z : AE D) = 1 + G * ((M : AE D) * s) := eq_add_of_sub_eq' h1
  let w : (AE D)ˣ := z * sgU D z
  have hw : (w : AE D) - 1 = (M : AE D) * (G * (s + sgA D s + G * M * s * sgA D s)) := by
    have e1 : (w : AE D) = (z : AE D) * sgA D z := rfl
    rw [e1, hz, map_add (f := _), map_one, map_mul, map_mul, hGs, hMs]
    ring
  have hwM : ∀ P, vl D P ((w : AE D) - 1) ≤ vl D P (M : AE D) := fun P => by
    rw [hw, map_mul]
    exact mul_le_of_le_one_right' (vl_le (mul_mem hGm (add_mem (add_mem hs (sgA_mem D hs))
      (mul_mem (mul_mem (mul_mem hGm (natCast_mem _ _)) hs) (sgA_mem D hs)))) P)
  have hvM : ∀ P, vl D P (M : AE D) = Valued.v (((M : D.host.E) : P.adicCompletion D.host.E)) := fun P => by
    rw [vl_nat]
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P _).symm
  obtain ⟨c, -, -, hu, -⟩ := GlobalTheory.Mem.HostCM.host_cm D.R D.host
  obtain ⟨b, hb, hun, hc⟩ := exists_of_balanced hu ((χ.1.comp (finPartI D.host.E)).ker)
    (fun v k => (MonoidHom.mem_ker).2 (GlobalTheory.Mem.KerDet.map_finPartI_locF ht v k)) (finIdl D w) (norm_balanced z)
  have hb' : χ.1 (finPartI D.host.E b) = 1 := (MonoidHom.mem_ker).1 hb
  have hc1 : χ.1 (finPartI D.host.E (b⁻¹ * finIdl D w)) = 1 := by
    refine hker _ hun (fun _ => rfl) fun P => ?_
    change Valued.v (((b⁻¹ * finIdl D w : Ideles D.host.E) : AdeleRing (𝓞 D.host.E) D.host.E).2 P - 1) ≤ _
    rw [← hvM]
    by_cases hP : vl D P ((w : AE D) - 1) < 1
    · have h2 : valAt P (finIdl D w) = 1 := by
        rw [valAt_apply, ← sub_add_cancel ((finIdl D w : AdeleRing (𝓞 D.host.E) D.host.E).2 P) 1, add_comm]
        exact Valuation.map_one_add_of_lt _ (by rw [vl_sub_one]; exact hP)
      have h3 : Units.map (ev P) (b⁻¹ * finIdl D w) = Units.map (ev P) (finIdl D w) := by
        rw [map_mul, map_inv, hc P h2, inv_one, one_mul]
      have h4 : ((b⁻¹ * finIdl D w : Ideles D.host.E) : AdeleRing (𝓞 D.host.E) D.host.E).2 P =
          (finIdl D w : AdeleRing (𝓞 D.host.E) D.host.E).2 P := congrArg Units.val h3
      rw [h4, vl_sub_one]
      exact hwM P
    · have hM1 : vl D P (M : AE D) = 1 := le_antisymm (vl_le (natCast_mem _ _) P) ((not_lt.1 hP).trans (hwM P))
      rw [hM1]
      refine (Valuation.map_sub _ _ _).trans ?_
      have hP1 : Valued.v (((b⁻¹ * finIdl D w : Ideles D.host.E) : AdeleRing (𝓞 D.host.E) D.host.E).2 P) = 1 := hun P
      rw [hP1, map_one, max_self]
  have e2 : finPartI D.host.E (b⁻¹ * finIdl D w) = (finPartI D.host.E b)⁻¹ * finIdl D w := by
    rw [map_mul, map_inv, finPartI_finIdl]
  rw [e2, map_mul, map_inv, hb', inv_one, one_mul] at hc1
  obtain ⟨k, hk⟩ := exists_real_norm (Units.mk0 a ha)
  have h5 : χ.1 (finIdl D (incU D (Units.mk0 a ha) * sgU D (incU D (Units.mk0 a ha)))) = 1 := by
    rw [hk]
    exact hfin k
  have h6 : χ.1 (finIdl D ((incU D (Units.mk0 a ha) * x⁻¹) * sgU D (incU D (Units.mk0 a ha) * x⁻¹))) = 1 := hc1
  rw [map_mul (sgU D), mul_mul_mul_comm, map_inv, ← mul_inv, map_mul, map_mul, h5, one_mul, map_inv, map_inv,
    inv_eq_one] at h6
  exact h6

end GlobalTheory.NuCharNorm

theorem GlobalTheory.NuCharNorm.chi_norm_one : ∀ (D : D7) (χ : Formalism.L2.Host.HChar D.host.E), χ.TrivOn D.host.F → (∃ M : ℕ, 0 < M ∧ ∀ a : Neutral.B1.Ideles D.host.E, a ∈ GlobalTheory.Mem.Chr.unitIdl D.host.E → (∀ w, (a : AdeleRing (𝓞 D.host.E) D.host.E).1 w = 1) → (∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v ((a : AdeleRing (𝓞 D.host.E) D.host.E).2 P - 1) ≤ Valued.v ((M : D.host.E) : P.adicCompletion D.host.E)) → χ.1 a = 1) → ∀ x : (AE D)ˣ, χ.1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D (x * sgU D x)) = 1 :=
  fun D χ ht ⟨M, hM, h⟩ x => GlobalTheory.NuCharNorm.norm_killed D χ ht M hM h x
end
end
