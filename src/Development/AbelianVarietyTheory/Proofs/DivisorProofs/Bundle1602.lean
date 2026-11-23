module

public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle197
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.Bundle002
import Mathlib.Algebra.Module.Torsion.Prod
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.OrthonormalBaseFrameNeg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1545
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle170
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle077
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle060
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterAtDetRootCongOneOddEqOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle321
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle327
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle089
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle076
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Development.WeilBound.ThetaLifts.FrameEstimates.ContinuousMixedSymm
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1298
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1446
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001

@[expose] public section

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.StdCharWeilDatum

section Char

variable {F : Type} [Field F] [NumberField F]

theorem at_pairA (x : Ainf F) : At (evI F) (pairA F x 0) := by
  intro u hu
  have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  show (u.1 * x, u.2 * 0) = ((0 : Ainf F), (0 : Af F))
  rw [h1, zero_mul, mul_zero]

theorem psi_pairA {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (x : Ainf F) :
    ψ (pairA F x 0) = Complex.exp (-(2 * Real.pi * Complex.I) *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (InfiniteAdeleRing.ringEquiv_mixedSpace F x) : ℝ)) :=
  hψ.2.2 _ (at_pairA x)

theorem norm_exp_real (r : ℝ) : ‖Complex.exp (-(2 * Real.pi * Complex.I) * (r : ℂ))‖ = 1 := by
  have : -(2 * Real.pi * Complex.I) * (r : ℂ) = ((-(2 * Real.pi * r) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

theorem norm_psi_inf {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (x : Ainf F) : ‖ψ (pairA F x 0)‖ = 1 := by
  rw [psi_pairA hψ]; exact norm_exp_real _

theorem pairA_split (x : AF F) : x = pairA F x.1 0 + pairA F 0 x.2 := by
  show x = ((x.1 + 0 : Ainf F), (0 + x.2 : Af F))
  rw [add_zero, zero_add]
  rfl

theorem norm_psi_fin {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (y : Af F) : ‖ψ (pairA F 0 y)‖ = 1 := by
  have hc : Continuous fun y : Af F => ‖ψ (pairA F 0 y)‖ :=
    (hψ.1.comp (continuous_const.prodMk continuous_id)).norm
  have hcl : IsClosed {y : Af F | ‖ψ (pairA F 0 y)‖ = 1} := isClosed_eq hc continuous_const
  have hrange : Set.range (algebraMap F (Af F)) ⊆ {y : Af F | ‖ψ (pairA F 0 y)‖ = 1} := by
    rintro _ ⟨a, rfl⟩
    have h1 := hψ.2.1 a
    rw [GlobalTheory.AdeleCharTwist.algebraMap_eq_pairA, AddChar.map_add_eq_mul] at h1
    have h2 := congrArg norm h1
    rw [norm_mul, norm_psi_inf hψ, one_mul, norm_one] at h2
    exact h2
  have := hcl.closure_subset_iff.2 hrange
  rw [GlobalTheory.AdeleCharTwist.denseRange_fin.closure_range] at this
  exact this (Set.mem_univ y)

theorem norm_psi {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (x : AF F) : ‖ψ x‖ = 1 := by
  rw [pairA_split x, AddChar.map_add_eq_mul, norm_mul, norm_psi_inf hψ, norm_psi_fin hψ, one_mul]

theorem exists_ne_one {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) : ∃ x, ψ x ≠ 1 := by
  apply _root_.PositivityTheory.ThKEst.W.exists_ne_one <;> assumption

theorem isCharAF {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) : IsCharAF F ψ :=
  ⟨hψ.1, norm_psi hψ, hψ.2.1, exists_ne_one hψ⟩

end Char

section Trace

variable {F : Type} [Field F] [NumberField F]

theorem sum_eq_trace (x : Ainf F) :
    ∑ v : InfinitePlace F, (v.mult : ℝ) * (InfinitePlace.Completion.extensionEmbedding v (x v)).re =
      Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (InfiniteAdeleRing.ringEquiv_mixedSpace F x) := by
  classical
  rw [Algebra.trace_prod_apply, PI.ProdFormulaE.Tr.trace_pi, PI.ProdFormulaE.Tr.trace_pi,
    InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  simp only [Algebra.trace_complex_apply]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun w : InfinitePlace F => w.IsReal)]
  congr 1
  · refine Fintype.sum_congr _ _ fun w => ?_
    rw [InfinitePlace.mult_isReal, Nat.cast_one, one_mul, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply w.2,
      Complex.ofReal_re]
    simp
  · refine Fintype.sum_equiv (Equiv.subtypeEquivRight fun w => InfinitePlace.not_isReal_iff_isComplex) _ _ fun w => ?_
    have h := InfinitePlace.mult_isComplex ⟨w.1, InfinitePlace.not_isReal_iff_isComplex.1 w.2⟩
    simp only at h
    rw [h]
    push_cast
    rfl

end Trace

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sum_infFam [IsTotallyReal F] (B : Base F E) (θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ))
    (hθ : Formalism.IndefR.DatumF.IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ) (x : Ainf F) :
    ∑ w, θ w (x ⊗ₜ[F] (1 : E)) =
      ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (InfiniteAdeleRing.ringEquiv_mixedSpace F x) : ℝ) : ℂ) := by
  rw [← sum_eq_trace]
  push_cast
  refine Fintype.sum_congr _ _ fun w => ?_
  have hv : w.IsReal := IsTotallyReal.isReal w
  rw [GlobalTheory.DualPairCompare.gen_inf_val (B.emb w).1 w (B.emb w).2.symm (θ w) (hθ w) x,
    InfinitePlace.mult_isReal ⟨_, hv⟩, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hv,
    Complex.ofReal_re]
  simp

theorem isStdCharF_of_isGood : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) := by
  intro F E _ _ _ _ _ σ B hB
  haveI : IsTotallyReal F := hB.cm.1
  refine ⟨isCharAF hB.std, ⟨?_, fun θ hθ x => ?_⟩⟩
  · choose θ hθ using fun w : InfinitePlace F =>
      GlobalTheory.DualPairCompare.gen_inf_exists (B.emb w).1 w (B.emb w).2.symm
    exact ⟨θ, hθ⟩
  · show B.ψ (pairA F x 0) = _
    rw [psi_pairA hB.std, sum_infFam B θ hθ x]
    congr 1
    push_cast
    ring

end GlobalTheory.StdCharWeilDatum

end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompAct

open ReciprocityTheory.ChartRestriction.G.FD

theorem exists_action {H G C : Type} [Group H] [Group G] (comp : H → C) (hs : ∀ x, ∃ h, comp h = x)
    (Lift : G → H → Prop) (hex : ∀ g, ∃ k, Lift g k) (h1 : Lift 1 1)
    (hmul : ∀ g g' k k', Lift g k → Lift g' k' → Lift (g * g') (k * k'))
    (key : ∀ g k k' h h', Lift g k → Lift g k' → comp h = comp h' → comp (h * k) = comp (h' * k')) :
    ∃ mv : C → G → C, (∀ x, mv x 1 = x) ∧ (∀ x g g', mv x (g * g') = mv (mv x g) g') ∧ (∀ x, ∃ h, comp h = x) ∧
      ∀ g k, Lift g k → ∀ h, comp (h * k) = mv (comp h) g := by
  choose rep hrep using hs
  choose l hl using hex
  have main : ∀ g k, Lift g k → ∀ h, comp (h * k) = comp (rep (comp h) * l g) :=
    fun g k hk h => key g k (l g) h _ hk (hl g) (hrep _).symm
  refine ⟨fun x g => comp (rep x * l g), fun x => ?_, fun x g g' => ?_, fun x => ⟨rep x, hrep x⟩, main⟩
  · have := main 1 1 h1 (rep x)
    rw [mul_one, hrep] at this
    exact this.symm
  · show comp (rep x * l (g * g')) = comp (rep (comp (rep x * l g)) * l g')
    rw [← main g' (l g') (hl g'), mul_assoc]
    exact key (g * g') _ _ _ _ (hl _) (hmul _ _ _ _ (hl g) (hl g')) rfl

theorem frame_calc {n : Type} [Fintype n] [DecidableEq n] (x B P Q P' M : Matrix n n ℂ) (hy : (B * x).det ≠ 0)
    (h1 : M * B = B * Q) (h2 : P * Q = P') : P * x * ((B * x)⁻¹ * M * (B * x)) = P' * x := by
  have hx : IsUnit x.det := by
    rw [Matrix.det_mul] at hy
    exact (right_ne_zero_of_mul hy).isUnit
  have e : M * (B * x) = (B * x) * (x⁻¹ * (Q * x)) := by
    rw [← Matrix.mul_assoc M, h1, Matrix.mul_assoc B x, Matrix.mul_nonsing_inv_cancel_left _ _ hx, Matrix.mul_assoc]
  rw [Matrix.mul_assoc _ M, e, Matrix.nonsing_inv_mul_cancel_left _ _ hy.isUnit, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv_cancel_left _ _ hx, ← Matrix.mul_assoc, h2]

variable {D : D7} {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}

theorem archM_mul (V : HSp D) (hr : V.rank = r) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (g g' : GA D V) :
    Matrix.reindex (finCongr hr) (finCongr hr) (archM V θ g) * Matrix.reindex (finCongr hr) (finCongr hr) (archM V θ g') =
      Matrix.reindex (finCongr hr) (finCongr hr) (archM V θ (g * g')) := by
  have e : archM V θ (g * g') = archM V θ g * archM V θ g' := by
    unfold archM
    rw [map_mul, Units.val_mul, Matrix.map_mul]
  rw [e]
  exact Matrix.submatrix_mul_equiv (archM V θ g) (archM V θ g') _ (finCongr hr).symm _

theorem coset_of_comp_eq {V : HSp D} {X : Comp → Data E r} {dict : GA D V → Σ k, Frame (X k).Ψ r}
    {Kf : Subgroup (GA D V)} {th : ∀ c, (X c).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {hr : V.rank = r}
    (hd : DictIsUnif V dict Kf th hr) (x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (hf : ∀ h, ∃ p : GA D V, ∀ τ : (X (dict h).1).Ψ, mat (dict h).2 τ =
      Matrix.reindex (finCongr hr) (finCongr hr) (archM V (th (dict h).1 τ) p) * x₀ τ.1)
    {h h' : GA D V} (e : (dict h).1 = (dict h').1) :
    ∃ a ∈ GinfC V, ∃ γ ∈ GQ V, ∃ k ∈ Kf, h * a = γ * h' * k := by
  obtain ⟨-, -, ⟨x0, h0, h3⟩, -, -, h6⟩ := hd
  have hf' : ∀ g c x, dict g = ⟨c, x⟩ → ∃ p : GA D V, ∀ τ : (X c).Ψ, mat x τ =
      Matrix.reindex (finCongr hr) (finCongr hr) (archM V (th c τ) p) * x₀ τ.1 := by
    intro g c x hg
    have := hf g
    rw [hg] at this
    exact this
  have h6' : ∀ g g' c x, dict g = ⟨c, x⟩ → (∃ γ' ∈ (X c).Γ, dict g' = ⟨c, lact γ' x⟩) →
      ∃ γ ∈ GQ V, ∃ k ∈ Kf, g' = γ * g * k := by
    intro g g' c x hg hh
    refine h6 g g' ?_
    rw [hg]
    exact hh
  obtain ⟨x', hx'⟩ : ∃ x' : Frame (X (dict h).1).Ψ r, dict h' = ⟨(dict h).1, x'⟩ := by
    generalize (dict h).1 = c at e
    subst e
    exact ⟨_, rfl⟩
  obtain ⟨hdom, g0, hg0⟩ := h0 (dict h).1
  obtain ⟨b, hb⟩ := hf' _ _ _ hg0
  obtain ⟨p, hp⟩ := hf h
  obtain ⟨p', hp'⟩ := hf' _ _ _ hx'
  obtain ⟨a, a1, a2⟩ := GlobalTheory.UnitarySplit.ga_glue V _ 1 (GlobalTheory.UnitarySplit.infHom_mem V (b * (p⁻¹ * p') * b⁻¹)) (one_mem _)
  obtain ⟨γ', hγ', he⟩ := h3 h a a2
  refine ⟨a, a2, h6' h' _ _ x' hx' ⟨γ', hγ', he.trans ?_⟩⟩
  congr 2
  funext τ
  have ha : archM V (th (dict h).1 τ) a = archM V (th (dict h).1 τ) (b * (p⁻¹ * p') * b⁻¹) := by
    unfold archM
    rw [a1]
  show (mat (dict h).2 τ * ((mat (x0 (dict h).1) τ)⁻¹ * Matrix.reindex (finCongr hr) (finCongr hr)
    (archM V (th (dict h).1 τ) a) * mat (x0 (dict h).1) τ) : Matrix (Fin r) (Fin r) ℂ) = mat x' τ
  have hy := (hdom τ).1
  rw [hb τ] at hy
  rw [hp τ, hp' τ, hb τ, ha]
  refine frame_calc _ _ _ (Matrix.reindex (finCongr hr) (finCongr hr) (archM V (th (dict h).1 τ) (p⁻¹ * p'))) _ _ hy ?_ ?_
  · rw [archM_mul, archM_mul, inv_mul_cancel_right]
  · rw [archM_mul, mul_inv_cancel_left]

theorem comm_real_fin (V : HSp D) {a k : GA D V} (ha : a ∈ GinfC V) (hk : k ∈ GfC V) : a * k = k * a := by
  refine GlobalTheory.UnitarySplit.ga_ext V ?_ ?_
  · rw [map_mul, map_mul, show infHom V k = 1 from hk, mul_one, one_mul]
  · rw [map_mul, map_mul, show finHom V a = 1 from ha, mul_one, one_mul]

theorem exists_action_dict {V W : HSp D} (hV : V = W) {X : Comp → Data E r} {dict : GA D V → Σ k, Frame (X k).Ψ r}
    {Kf : Subgroup (GA D V)} {th : ∀ c, (X c).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {hr : V.rank = r}
    (hd : DictIsUnif V dict Kf th hr) (x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (hf : ∀ h, ∃ p : GA D V, ∀ τ : (X (dict h).1).Ψ, mat (dict h).2 τ =
      Matrix.reindex (finCongr hr) (finCongr hr) (archM V (th (dict h).1 τ) p) * x₀ τ.1)
    (β : GL (Fin W.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ W.rank) {G : Type} [Group G] (eG : G →* G0 L.Pg L.r)
    (hK : ∀ k : GA D W, Lev.IsLevelLift W β L 1 k ↔ cast (congrArg (GA D) hV.symm) k ∈ Kf)
    (hex : ∀ g, ∃ k, Lev.IsLevelLift W β L (eG g) k) :
    ∃ mv : Comp → G → Comp, (∀ x, mv x 1 = x) ∧ (∀ x g g', mv x (g * g') = mv (mv x g) g') ∧
      (∀ x, ∃ h, (castDict hV dict h).1 = x) ∧ ∀ g k, Lev.IsLevelLift W β L (eG g) k →
        ∀ h, (castDict hV dict (h * k)).1 = mv (castDict hV dict h).1 g := by
  subst hV
  have hK' : ∀ k : GA D V, Lev.IsLevelLift V β L 1 k ↔ k ∈ Kf := hK
  refine exists_action (fun h => (dict h).1) (fun x => ?_) (fun g k => Lev.IsLevelLift V β L (eG g) k) hex ?_ ?_ ?_
  · obtain ⟨x0, h0, -⟩ := hd.2.2.1
    obtain ⟨g, hg⟩ := (h0 x).2
    exact ⟨g, congrArg Sigma.fst hg⟩
  · show Lev.IsLevelLift V β L (eG 1) 1
    rw [map_one]
    exact (hK' 1).2 (one_mem _)
  · intro g g' k k' hk hk'
    show Lev.IsLevelLift V β L (eG (g * g')) (k * k')
    rw [map_mul]
    exact GlobalTheory.ProjComm.isLift_mul hk hk'
  · intro g k k' h h' hk hk' e
    obtain ⟨a, ha, γ, hγ, k0, hk0, he⟩ := coset_of_comp_eq hd x₀ hf e
    have h1 := GlobalTheory.ProjComm.isLift_mul (GlobalTheory.ProjComm.isLift_mul (GlobalTheory.ProjComm.isLift_inv hk') ((hK' k0).2 hk0)) hk
    rw [mul_one, inv_mul_cancel] at h1
    have h2 : h * k * a = γ * (h' * k' * (k'⁻¹ * k0 * k)) := by
      rw [mul_assoc h, ← comm_real_fin V ha hk.1, ← mul_assoc h, he]
      group
    obtain ⟨x0, -, h3⟩ := hd.2.2.1
    obtain ⟨_, -, e1⟩ := h3 (h * k) a ha
    obtain ⟨_, -, e2⟩ := hd.1 γ hγ (h' * k' * (k'⁻¹ * k0 * k))
    obtain ⟨_, -, e3⟩ := hd.2.1 _ ((hK' _).1 h1) (h' * k')
    have f1 := congrArg Sigma.fst e1
    have f2 := congrArg Sigma.fst e2
    have f3 := congrArg Sigma.fst e3
    rw [h2] at f1
    exact f1.symm.trans (f2.trans f3)



theorem exists_action_components : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → TieIn T R κ v₀ → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i, (∀ g, ∃ k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k) → ∃ mv : (T.U ((i : ℕ) + 1) σ).Comp → G → (T.U ((i : ℕ) + 1) σ).Comp, (∀ x, mv x 1 = x) ∧ (∀ x g g', mv x (g * g') = mv (mv x g) g') ∧ (∀ x, ∃ h, (castDict hV (T.dict ((i : ℕ) + 1) σ) h).1 = x) ∧ ∀ g k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k → ∀ h, (castDict hV (T.dict ((i : ℕ) + 1) σ) (h * k)).1 = mv (castDict hV (T.dict ((i : ℕ) + 1) σ) h).1 g := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hR ht hpb i σ hσ hV hex
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  obtain ⟨th, hr, hth, hd⟩ := ht.laws.dictU _ hj σ hσ
  obtain ⟨hr', g, e, F, ik, φ, th', -, -, hth', -, hL⟩ := ht.laws.adPin _ hj σ hσ
  have e' : th' = th := funext fun k => funext fun τ => GlobalTheory.LettersCheck.isInfEmb_unique _ _ _ (hth' k τ) (hth k τ)
  subst e'
  exact exists_action_dict hV hd (T.x₀ _ σ) (fun h => (hL h).elim fun γ hγ => ⟨γ * h, hγ.2.2.2⟩)
    (R.βW i) (R.datWp i R.triv) R.eG.toMonoidHom (GlobalTheory.T.level_character_embedding_compat T R κ v₀ hR ht hpb i σ hσ hV) hex

end GlobalTheory.CompAct
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MuLevel

theorem det_cong_of_level {D : D7} (V : HSp D) (N : ℕ) (hN : N ≠ 0) (k : GA D V)
    (hk : ∀ z ∈ latHat V, ∃ y ∈ latHat V, (finHom V k).1.mulVec z - z = N • y) :
    ∃ w ∈ intAE D, (finHom V k).1.det - 1 = N • w := by
  let L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) :=
    V.L0.map (V.frame.equivFun.toLinearMap.restrictScalars (𝓞 D.host.E))
  have hL : latHat V = GlobalTheory.AdLat.hat D.host.F (L : Set (Fin V.rank → D.host.E)) := by
    unfold Formalism.L2.Pj.latHat GlobalTheory.AdLat.hat
    congr 1
    ext z
    constructor
    · rintro ⟨a, ha, x, hx, rfl⟩
      exact ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨a, ha, x, hx, rfl⟩
  have hfg : L.FG := V.standardTuple_isLattice.fg.map _
  have hsp : Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤ := by
    have hspan : Submodule.span D.host.E (V.L0 : Set V.V) = ⊤ := by
      let W := Submodule.span D.host.E (V.L0 : Set V.V)
      change W = ⊤
      by_contra h
      let e : V.V ≃ₗ⋆[D.host.E] V.V :=
        (V.frame.equivFun.trans (starLinearEquiv D.host.E)).trans V.frame.equivFun.symm
      let g : V.V →ₗ[D.host.E] Module.Dual D.host.E W :=
        (LinearMap.domRestrict' W).comp (V.hT.comp e.toLinearMap)
      have hdim : Module.finrank D.host.E (Module.Dual D.host.E W) <
          Module.finrank D.host.E V.V := by
        rw [Subspace.dual_finrank_eq]
        exact Submodule.finrank_lt h
      obtain ⟨z, hz, hz₀⟩ :=
        Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
      have hsmul (a : D.host.E) : a • e z ∈ V.L0 := by
        rw [← V.baseLattice_isUnimodular]
        simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual,
          Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
        intro y hy
        have hzy : V.hT (e z) y = 0 :=
          congrArg (fun f : Module.Dual D.host.E W => f ⟨y, Submodule.subset_span hy⟩)
            (LinearMap.mem_ker.mp hz)
        have hyz : V.hT y (e z) = 0 := by
          have hh := V.herm.eq (e z) y
          simpa [hzy] using hh.symm
        simp [hyz]
      let i : D.host.E →ₗ[𝓞 D.host.E] V.L0 :=
        ((LinearMap.toSpanSingleton D.host.E _ (e z)).restrictScalars (𝓞 D.host.E)).codRestrict V.L0 hsmul
      let : Module.Finite (𝓞 D.host.E) V.L0 := Module.Finite.iff_fg.mpr V.standardTuple_isLattice.fg
      let : Module.Finite (𝓞 D.host.E) D.host.E := Module.Finite.of_injective i fun a b hab =>
        smul_left_injective D.host.E (fun hzero => hz₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
      exact RingOfIntegers.not_isField D.host.E
        (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 D.host.E) D.host.E) (Field.toIsField D.host.E))
    have : (L : Set (Fin V.rank → D.host.E)) = V.frame.equivFun.toLinearMap '' (V.L0 : Set V.V) := rfl
    rw [this, Submodule.span_image, hspan, Submodule.map_top, LinearEquiv.range]
  rw [hL] at hk
  rw [GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers]
  exact GlobalTheory.MarkDet.det_sub_one_of_cong D.host.F L hfg hsp N hN _ hk



theorem exists_root_of_level {D : D7} (V : HSp D) (N : ℕ) (hN : Odd N) (k : GA D V) (hf : k ∈ GfC V)
    (hk : ∀ z ∈ latHat V, ∃ y ∈ latHat V, (finHom V k).1.mulVec z - z = N • y) :
    ∃ x : (AE D)ˣ, IsDetRoot V k x ∧ FinUnit x ∧ ∃ y ∈ intAE D, finPart D (x : AE D) - 1 = N • y := by
  obtain ⟨w, hw, hwe⟩ := det_cong_of_level V N hN.pos.ne' k hk
  have hn := GlobalTheory.RecDict.det_finHom_norm V k
  obtain ⟨y, y', hy, hy', hyy, hroot, p, hp, hpe⟩ := GlobalTheory.OddRoot.exists_root_odd D N hN _ w hw hwe hn
  obtain ⟨Y, hY1, hY2, hY3⟩ := GlobalTheory.DetRootCong.exists_idele D y y' hyy
  refine ⟨Y, ?_, ⟨hY1, hY2 ▸ hy, hY3 ▸ hy'⟩, p, hp, hY2 ▸ hpe⟩
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have he1 : ∀ z, (e z).1 = infPart D z := fun z => (he z).1
  have he2 : ∀ z, (e z).2 = finPart D z := fun z => (he z).2
  have hdet : (finHom V k).1.det = finPart D (matHom V k).1.det := ((finPart D).map_det _).symm
  have hdet' : (infHom V k).1.det = infPart D (matHom V k).1.det := ((infPart D).map_det _).symm
  have h1 : infHom V k = 1 := hf
  have hs : infPart D (sigR (AF D.host.F) D.sp.cm.sig (Y : AE D)) =
      sigR (Ainf D.host.F) D.sp.cm.sig (infPart D (Y : AE D)) := GlobalTheory.DetRootCong.map_sigR _ _ _
  refine e.injective (Prod.ext ?_ ?_)
  · rw [he1, he1, RingHom.map_mul, hs, ← hdet', h1, hY1, RingHom.map_one, mul_one]
    exact Matrix.det_one.symm
  · have hs' := GlobalTheory.DetRootCong.finPart_sigR D (Y : AE D)
    rw [hY2] at hs'
    rw [hdet, ← hs', ← RingHom.map_mul] at hroot
    exact (he2 _).trans ((hY2.trans hroot).trans (he2 _).symm)

theorem exists_ext {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (σ : K →+* ℂ) :
    ∃ τ : L →+* ℂ, τ.comp (algebraMap K L) = σ := by
  letI : Algebra K ℂ := σ.toAlgebra
  have : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  let f : L →ₐ[K] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  exact ⟨f.toRingHom, RingHom.ext fun x => f.commutes x⟩



theorem mu_eq_one_of_mem_level : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → TieIn T R κ v₀ → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i, ∀ k ∈ T.Kf ((i : ℕ) + 1) σ, T.mu ((i : ℕ) + 1) σ k = 1 := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hL h _ i σ hσ _ k hk
  have hj := inR i
  obtain ⟨τ, rfl⟩ := exists_ext (L := D.what₂.LL) σ
  obtain ⟨hf, hk'⟩ := (h.laws.levelK _ hj _ hσ k).1 hk
  have hodd : Odd (D.host.g 0 * D.host.g 1) := h.laws.pins.2.1.1 ▸ T.Q.l.odd
  obtain ⟨x, hx, hu, hc⟩ := exists_root_of_level _ _ hodd k hf hk'
  have hm := R.C.isMu0 i
  have h1 : R.mu0 ((i : ℕ) + 1) x = 1 := by
    refine GlobalTheory.tame_heckeChar_eq_one_of_finUnit D _ _ (hL.mu0 i) hm.tame _ (fun P hP => hm.unr P fun a ha => hP ?_) x hu hc
    rw [Nat.cast_mul]
    fin_cases a
    · exact Ideal.mul_mem_right _ _ ha
    · exact Ideal.mul_mem_left _ _ ha
  obtain ⟨y, hy1, hy2⟩ := (h.chiR i τ hσ).2.2.2.1 x hu.1
  have h2 : algebraMap T.Q.c.F D.what₂.LL y = 1 :=
    D.what₂.embLL.injective (by rw [← hy1, h1, map_one, Circle.coe_one])
  rw [(h.laws.muVal _ hj _ hσ).2 k x hx, hy2, h2, map_one]

end GlobalTheory.MuLevel
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.finiteDimensional_of_commuting_finiteAlgebra_jointEigen : ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (S : Set (Module.End ℂ M)), (∀ s ∈ S, ∀ t ∈ S, s * t = t * s) → FiniteDimensional ℂ (Algebra.adjoin ℂ S) → (∀ c : Module.End ℂ M → ℂ, FiniteDimensional ℂ ↥(⨅ s ∈ S, LinearMap.ker (s - algebraMap ℂ (Module.End ℂ M) (c s)))) → FiniteDimensional ℂ M := by
  first | exact @GlobalTheory.AutGrowth.finiteDimensional_of_commuting_finite_eigen | exact GlobalTheory.AutGrowth.finiteDimensional_of_commuting_finite_eigen | (intros; apply GlobalTheory.AutGrowth.finiteDimensional_of_commuting_finite_eigen <;> assumption)
end
