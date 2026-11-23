module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.BindPow
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalHeckeValuesSameParameters
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle312
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle307
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.Bundle002
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
import Mathlib.Tactic.ENatToNat
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1465
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.TwTrSum
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.PowerBoundFastDecay

@[expose] public section

section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical



open UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.F.RS

attribute [local instance] borelG borelF borelA borelH

section SlopeTestRemainingChoices

open GlobalTheory.LGrp GlobalTheory.LFun.SatCompare GlobalTheory.LocGL GlobalTheory.WeylGL

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private theorem unifIs (w : Pl E) : IsUnifV E w (UpperTheory.V.Z.Tf.GlobalTraceComparison.unif w) :=
  Classical.epsilon_spec (exists_isUnifV w)

private theorem tj_indep (w : Pl E) (n j : ℕ) {ϖ ϖ' : w.adicCompletion E} (hu : IsUnifV E w ϖ)
    (hu' : IsUnifV E w ϖ') : Tj ℂ n (Ov E w) ϖ' j = Tj ℂ n (Ov E w) ϖ j := by
  have h0 := ne_zero_of_isUnifV hu
  have hv : Valued.v (ϖ' / ϖ) = 1 := by
    rw [map_div₀, hu, hu', div_self WithZero.coe_ne_zero]
  have e := Final.TjIndep _ (Ov E w) ϖ (ϖ' / ϖ) ℂ n j hv.le
    (show Valued.v (ϖ' / ϖ)⁻¹ ≤ 1 by rw [map_inv₀, hv, inv_one]) (div_ne_zero (ne_zero_of_isUnifV hu') h0)
  rwa [div_mul_cancel₀ _ h0] at e

private theorem tj_zero_act (w : Pl E) (n : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GLw n w) V) {ϖ : w.adicCompletion E} (hu : IsUnifV E w ϖ) {x : V}
    (hx : x ∈ fixed π (KGL w (n := n))) : heckeVec π (KGL w (n := n)) (Tj ℂ n (Ov E w) ϖ 0) x = x := by
  have h0 := ne_zero_of_isUnifV hu
  have e : Tj ℂ n (Ov E w) ϖ 0 = dosetInd ℂ (KGL w (n := n)) 1 := by
    rw [Tj_eq h0]
    congr 1
  rw [e, heckeVec_one (Final.GLintComm E w n) hx]

private theorem tj_top_ne (w : Pl E) (n : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GLw n w) V) {ϖ : w.adicCompletion E} (hu : IsUnifV E w ϖ) {x : V} (hx0 : x ≠ 0)
    (hx : x ∈ fixed π (KGL w (n := n))) {c : ℂ} (h1 : heckeVec π (KGL w (n := n)) (Tj ℂ n (Ov E w) ϖ n) x = c • x) : c ≠ 0 := by
  intro e
  have h0 := ne_zero_of_isUnifV hu
  have hTn : Tj ℂ n (Ov E w) ϖ n = dosetInd ℂ (KGL w (n := n)) (tor h0 fun _ => 1) := by
    rw [Tj_eq h0]; simp
  rw [e, zero_smul, hTn, heckeVec_dosetInd (R := {tor h0 fun _ => 1}) hx, Finset.sum_singleton] at h1
  · exact hx0 (by simpa [← Module.End.mul_apply, ← map_mul] using congrArg (π (tor h0 fun _ => 1)⁻¹) h1)
  · intro γ hγ
    exact mem_doset.2 ⟨1, one_mem _, 1, one_mem _, by simpa using hγ⟩
  · intro g hg
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_doset.1 hg
    refine ⟨_, ⟨Finset.mem_singleton_self _, ?_⟩, fun γ hγ => Finset.mem_singleton.1 hγ.1⟩
    rw [← tor_const_comm, mul_assoc, inv_mul_cancel_left]
    exact mul_mem ha hb

end SlopeTestRemainingChoices

theorem UpperTheory.Zero.ConvolutionTheory.EB.sat2Ex :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (V ι : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GLw a w × GLw b w) V) (x : ι → V)
    (t : Fin (a + 1) × Fin (b + 1) → ℂ), x ≠ 0 → (∀ i, x i ∈ fixed ρ (K2 a b w)) →
    (∀ (p : Fin (a + 1) × Fin (b + 1)) i, heckeVec ρ (K2 a b w) (fun y : GLw a w × GLw b w => Tj ℂ a (Ov E w) (UpperTheory.V.Z.Tf.GlobalTraceComparison.unif w) p.1 y.1 * Tj ℂ b (Ov E w) (UpperTheory.V.Z.Tf.GlobalTraceComparison.unif w) p.2 y.2) (x i) = t p • x i) →
    ∃ B₁ B₂ : Multiset ℂˣ, B₁.card = a ∧ B₂.card = b ∧ (∀ p, t p = satEig (qV E w) a B₁ p.1 * satEig (qV E w) b B₂ p.2) ∧ ∀ i, IsSat2 w ρ (x i) B₁ B₂ := by
  intro E _ _ _ a b w V ι _ _ ρ x t hx0 hfix ht
  have hu := unifIs w
  have hKa := Final.GLintComm E w a
  have hKb := Final.GLintComm E w b
  have hTa := fun i : ℕ => Tj_mem_hecke (n := a) hu i
  have hTb := fun j : ℕ => Tj_mem_hecke (n := b) hu j
  obtain ⟨k₀, hk₀⟩ : ∃ k, x k ≠ 0 := Function.ne_iff.1 hx0
  have fA : ∀ k, x k ∈ fixed (ρ.comp (MonoidHom.inl _ _)) (KGL w (n := a)) := fun k =>
    GlobalTheory.LGrp.mem_fixed.2 fun g hg =>
      GlobalTheory.LGrp.mem_fixed.1 (hfix k) (g, 1) (Subgroup.mem_prod.2 ⟨hg, one_mem _⟩)
  have fB : ∀ k, x k ∈ fixed (ρ.comp (MonoidHom.inr _ _)) (KGL w (n := b)) := fun k =>
    GlobalTheory.LGrp.mem_fixed.2 fun g hg =>
      GlobalTheory.LGrp.mem_fixed.1 (hfix k) (1, g) (Subgroup.mem_prod.2 ⟨one_mem _, hg⟩)
  have fAB : ∀ k (j : ℕ), heckeVec (ρ.comp (MonoidHom.inr _ _)) (KGL w (n := b))
      (Tj ℂ b (Ov E w) (UpperTheory.V.Z.Tf.GlobalTraceComparison.unif w) j) (x k) ∈ fixed (ρ.comp (MonoidHom.inl _ _)) (KGL w (n := a)) := by
    intro k j
    refine GlobalTheory.LGrp.mem_fixed.2 fun g hg => ?_
    have key := map_heckeVec hKb (hTb j) (ρ := ρ.comp (MonoidHom.inr _ _)) (ρ' := ρ.comp (MonoidHom.inr _ _))
      ((ρ.comp (MonoidHom.inl _ _)) g) (fun g' y => by
        simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inl_apply, MonoidHom.inr_apply]
        rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
        simp) (x k)
    rw [key, GlobalTheory.LGrp.mem_fixed.1 (fA k) g hg]
  have pp : ∀ (p : Fin (a + 1) × Fin (b + 1)) k, heckeVec (ρ.comp (MonoidHom.inl _ _)) (KGL w (n := a))
      (Tj ℂ a (Ov E w) (UpperTheory.V.Z.Tf.GlobalTraceComparison.unif w) p.1) (heckeVec (ρ.comp (MonoidHom.inr _ _)) (KGL w (n := b))
        (Tj ℂ b (Ov E w) (UpperTheory.V.Z.Tf.GlobalTraceComparison.unif w) p.2) (x k)) = t p • x k := fun p k => by
    rw [← heckeVec_pairProd ρ hKa hKb (hTa _) (hTb _) (hfix k)]
    exact ht p k
  have eA : ∀ (i : Fin (a + 1)) k, heckeVec (ρ.comp (MonoidHom.inl _ _)) (KGL w (n := a))
      (Tj ℂ a (Ov E w) (UpperTheory.V.Z.Tf.GlobalTraceComparison.unif w) i) (x k) = t (i, 0) • x k := fun i k => by
    have := pp (i, 0) k
    simp only [Fin.val_zero] at this
    rwa [tj_zero_act w b _ hu (fB k)] at this
  have eB : ∀ (j : Fin (b + 1)) k, heckeVec (ρ.comp (MonoidHom.inr _ _)) (KGL w (n := b))
      (Tj ℂ b (Ov E w) (UpperTheory.V.Z.Tf.GlobalTraceComparison.unif w) j) (x k) = t (0, j) • x k := fun j k => by
    have := pp (0, j) k
    simp only [Fin.val_zero] at this
    rwa [tj_zero_act w a _ hu (fAB k j)] at this
  have t00 : t (0, 0) = 1 := by
    have h1 := eA 0 k₀
    simp only [Fin.val_zero] at h1
    rw [tj_zero_act w a _ hu (fA k₀)] at h1
    exact smul_left_injective ℂ hk₀ (by simpa using h1.symm)
  have mul : ∀ p : Fin (a + 1) × Fin (b + 1), t p = t (p.1, 0) * t (0, p.2) := fun p => by
    have h1 := pp p k₀
    rw [eB p.2 k₀, heckeVec_smul_pair _ hKa (hTa _), eA p.1 k₀, smul_smul, mul_comm] at h1
    exact smul_left_injective ℂ hk₀ h1.symm
  have hta : t (Fin.last a, 0) ≠ 0 :=
    tj_top_ne w a _ hu hk₀ (fA k₀) (by simpa using eA (Fin.last a) k₀)
  have htb : t (0, Fin.last b) ≠ 0 :=
    tj_top_ne w b _ hu hk₀ (fB k₀) (by simpa using eB (Fin.last b) k₀)
  obtain ⟨B₁, c₁, h₁⟩ := GlobalTheory.T.exists_multiset_satakeEigenvalue_eq (qV E w) a (qV_ne_zero w)
    (fun i => if h : i < a + 1 then t (⟨i, h⟩, 0) else 0) (by simpa using t00)
    (by simpa [Fin.last] using hta)
  obtain ⟨B₂, c₂, h₂⟩ := GlobalTheory.T.exists_multiset_satakeEigenvalue_eq (qV E w) b (qV_ne_zero w)
    (fun j => if h : j < b + 1 then t (0, ⟨j, h⟩) else 0) (by simpa using t00)
    (by simpa [Fin.last] using htb)
  have s₁ : ∀ i : Fin (a + 1), satEig (qV E w) a B₁ i = t (i, 0) := fun i => by
    rw [h₁ i (Nat.lt_succ_iff.1 i.2), dite_eq_left i.2]
  have s₂ : ∀ j : Fin (b + 1), satEig (qV E w) b B₂ j = t (0, j) := fun j => by
    rw [h₂ j (Nat.lt_succ_iff.1 j.2), dite_eq_left j.2]
  have tp : ∀ p : Fin (a + 1) × Fin (b + 1), t p = satEig (qV E w) a B₁ p.1 * satEig (qV E w) b B₂ p.2 := fun p => by
    rw [s₁, s₂]
    exact mul p
  refine ⟨B₁, B₂, c₁, c₂, tp, fun k => ⟨hfix k, c₁, c₂, fun ϖ hϖ i hi j hj => ?_⟩⟩
  have h := ht (⟨i, Nat.lt_succ_iff.2 hi⟩, ⟨j, Nat.lt_succ_iff.2 hj⟩) k
  rw [tp] at h
  rw [tj_indep w a i hu hϖ, tj_indep w b j hu hϖ]
  exact h
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical



open UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.F.RS

attribute [local instance] borelG borelF borelA borelH

section Back

open PositivityTheory.Rg.BcB.F.RS.JetMatrixAlgebra GlobalTheory.ThetaSatake
open GlobalTheory.LFun.ConjPlace (dGL invT dGL_comm invT_dGL)

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private theorem fx_dGL_inv (x : Pl E) (n : ℕ) (p : (x.adicCompletion E)ˣ) :
    fx x n (dGL n p n)⁻¹ =
      dGL n (Units.map ((cloc x).symm : x.adicCompletion E →* (cw x).adicCompletion E) p) n := by
  have hc : Commute (dGL n p n) (PhiU n (x.adicCompletion E)) := dGL_comm p _
  have e : (PhiU n (x.adicCompletion E))⁻¹ * (dGL n p n)⁻¹ * PhiU n (x.adicCompletion E) = (dGL n p n)⁻¹ := by
    rw [mul_assoc, hc.inv_left.eq, inv_mul_cancel_left]
  change invT (cloc x).symm n ((MulAut.conj (PhiU n (x.adicCompletion E))).symm (dGL n p n)⁻¹) = _
  rw [MulAut.conj_symm_apply, e]
  exact invT_dGL (cloc x).symm p n

private theorem Tj_fx_symm (x : Pl E) (n : ℕ) {p : x.adicCompletion E} (hp : IsUnifV E x p) (hp0 : p ≠ 0) {i : ℕ}
    (hi : i ≤ n) (g : GLw n (cw x)) :
    Tj ℂ n (Ov E x) p i ((fx x n).symm g) =
      Tj ℂ n (Ov E (cw x))
        ((Units.map ((cloc x).symm : x.adicCompletion E →* (cw x).adicCompletion E) (Units.mk0 p hp0) :
          ((cw x).adicCompletion E)ˣ) : (cw x).adicCompletion E) (n - i)
        (dGL n (Units.map ((cloc x).symm : x.adicCompletion E →* (cw x).adicCompletion E) (Units.mk0 p hp0)) n * g) := by
  have h := Tj_fx x n hp hp0 (Nat.sub_le n i) ((dGL n (Units.mk0 p hp0) n)⁻¹ * (fx x n).symm g)
  rw [map_mul, fx_dGL_inv, MulEquiv.apply_symm_apply, mul_inv_cancel_left, Nat.sub_sub_self hi] at h
  exact h.symm

private theorem satake_conjugate_inverse {a b : ℕ} (x : Pl E) {G : H E a b → ℂ} {B₁ B₂ : Multiset ℂˣ}
    (hs : IsSat2 (cw x) (pairRtT a b (cw x)) G B₁ B₂) :
    IsSat2 x (pairRt a b x) G (B₁.map (·⁻¹)) (B₂.map (·⁻¹)) := by
  rw [pairRtT_cw] at hs
  have h := saturation_transport_pair ((fx x a).prodCongr (fx x b)).symm (fun g => ?_) (absNorm_cw x).symm
    (fun ϖ' hϖ' => ?_) hs
  · have e : ((pairRt a b x).comp ((fx x a).prodCongr (fx x b)).symm.toMonoidHom).comp
        ((fx x a).prodCongr (fx x b)).symm.symm.toMonoidHom = pairRt a b x := by
      ext1 g
      simp
    rw [e] at h
    exact h
  · show g ∈ (KGL (cw x) (n := a)).prod (KGL (cw x) (n := b)) ↔
      ((fx x a).prodCongr (fx x b)).symm g ∈ (KGL x (n := a)).prod (KGL x (n := b))
    rw [Subgroup.mem_prod, Subgroup.mem_prod]
    have h1 := mem_fx_iff x a ((fx x a).symm g.1)
    have h2 := mem_fx_iff x b ((fx x b).symm g.2)
    rw [MulEquiv.apply_symm_apply] at h1 h2
    exact and_congr h1.symm h2.symm
  · have hp0 : ϖ' ≠ 0 := fun e => by simp [IsUnifV, e] at hϖ'
    refine ⟨Units.map ((cloc x).symm : x.adicCompletion E →* (cw x).adicCompletion E) (Units.mk0 ϖ' hp0),
      (cloc_symm_v x ϖ').trans hϖ', fun i hi j hj g => ?_⟩
    exact congrArg₂ (· * ·) (Tj_fx_symm x a hϖ' hp0 hi g.1) (Tj_fx_symm x b hϖ' hp0 hj g.2)

end Back

theorem UpperTheory.Zero.ConvolutionTheory.EB.sat2Back :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (G : H E a b → ℂ) (B₁ B₂ : Multiset ℂˣ), IsSplitAt w → IsSat2 w (pairRtT a b w) G B₁ B₂ →
    IsSat2 (cPl w) (pairRt a b (cPl w)) G (inv B₁) (inv B₂) := by
  intro E _ _ _ a b w G B₁ B₂ _ hs
  have e : GlobalTheory.ThetaSatake.cw (GlobalTheory.ThetaSatake.cw w) = w := GlobalTheory.ThetaPull.conjSrc_conjSrc w
  have hs' : IsSat2 (GlobalTheory.ThetaSatake.cw (GlobalTheory.ThetaSatake.cw w))
      (pairRtT a b (GlobalTheory.ThetaSatake.cw (GlobalTheory.ThetaSatake.cw w))) G B₁ B₂ := by
    rw [e]
    exact hs
  exact satake_conjugate_inverse (GlobalTheory.ThetaSatake.cw w) hs'
end
