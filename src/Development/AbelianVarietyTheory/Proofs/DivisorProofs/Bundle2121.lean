module

public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle277
public import GroundTheory.GlobalFields.Adele.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1439
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1196
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1197
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1290
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2076
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2078
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
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenPtSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1910
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

noncomputable section
namespace GlobalTheory.FockLineJ

variable {D : D7}

theorem theta_realAd {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (t : ℝ) :
    θ τ (fstA D.host.F (realAd D.host.F t) ⊗ₜ[D.host.F] (1 : D.host.E)) = t := by
  have h2 : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm := by
    have : ⇑(InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm = ⇑(GroundTheory.Global.homeomorphMixedSpace D.host.F).symm :=
      funext fun y => by
        rw [Homeomorph.eq_symm_apply]
        exact (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).apply_symm_apply y
    rw [this]
    exact (GroundTheory.Global.homeomorphMixedSpace D.host.F).symm.continuous
  let φ : ℝ →+* ℂ := ((θ τ).comp Algebra.TensorProduct.includeLeftRingHom).comp
    ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm.toRingHom.comp
      (algebraMap ℝ (mixedEmbedding.mixedSpace D.host.F)))
  have hφ : Continuous φ :=
    (hθ τ).2.comp (h2.comp (continuous_algebraMap ℝ (mixedEmbedding.mixedSpace D.host.F)))
  have e : ∀ s, φ s = θ τ (fstA D.host.F (realAd D.host.F s) ⊗ₜ[D.host.F] (1 : D.host.E)) := fun s => rfl
  rw [← e]
  have h1 : φ t = t * φ 1 := GlobalTheory.WeilVacMove.additive_real φ.toAddMonoidHom hφ t
  rw [h1, map_one, mul_one]

theorem realAd_smul_eq (t : ℝ) (a : AE D) :
    realAd D.host.F t • a = (realAd D.host.F t ⊗ₜ[D.host.F] (1 : D.host.E)) * a := by
  rw [Algebra.smul_def]; rfl

theorem finPart_realAd_smul (t : ℝ) (a : AE D) : finPart D (realAd D.host.F t • a) = 0 := by
  rw [realAd_smul_eq, map_mul]
  have : finPart D (realAd D.host.F t ⊗ₜ[D.host.F] (1 : D.host.E)) = 0 := by
    show sndA D.host.F (realAd D.host.F t) ⊗ₜ[D.host.F] (AlgHom.id D.host.F D.host.E 1) = 0
    rw [show sndA D.host.F (realAd D.host.F t) = 0 from rfl, TensorProduct.zero_tmul]
  rw [this, zero_mul]

theorem theta_realAd_smul {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (t : ℝ) (a : AE D) :
    θ τ (infPart D (realAd D.host.F t • a)) = t * θ τ (infPart D a) := by
  rw [realAd_smul_eq, map_mul, map_mul]
  have : infPart D (realAd D.host.F t ⊗ₜ[D.host.F] (1 : D.host.E)) =
      fstA D.host.F (realAd D.host.F t) ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
  rw [this, theta_realAd hθ]



theorem realAd_smul_eq_sum {m n : ℕ} {θ : InfFam D} (hθ : IsInfFam θ) {σ : (D.what₂.Tau → ℂ) →+ AE D}
    (hσ : GlobalTheory.FockCompare.Chart θ σ) (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) (y : Mx D m n)
    (hy : ∀ τ, compAt θ τ y = z τ) (t : ℝ) :
    realAd D.host.F t • y = (∑ τ, lineAt θ τ (z τ)) t := by
  classical
  ext i j
  rw [← sub_eq_zero]
  have hl := fun τ => GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ (z τ)
  have hs : ((∑ τ, lineAt θ τ (z τ)) t) i j = ∑ τ, lineAt θ τ (z τ) t i j := by
    generalize (Finset.univ : Finset D.what₂.Tau) = s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih => simp [Finset.sum_insert ha, AddMonoidHom.add_apply, Matrix.add_apply, ih]
  refine hσ.ext _ ?_ fun τ' => ?_

  · rw [map_sub, hs, map_sum, Matrix.smul_apply, finPart_realAd_smul, zero_sub, neg_eq_zero]
    exact Finset.sum_eq_zero fun τ _ => congrFun (congrFun ((hl τ).2.1 t) i) j

  · rw [map_sub, map_sub, hs, map_sum, map_sum, Matrix.smul_apply, theta_realAd_smul hθ, sub_eq_zero]
    have e1 : θ τ' (infPart D (y i j)) = z τ' i j := congrFun (congrFun (hy τ') i) j
    have e2 : ∀ τ, θ τ' (infPart D (lineAt θ τ (z τ) t i j)) = if τ' = τ then (t : ℂ) * z τ i j else 0 := by
      intro τ
      have h := congrFun (congrFun ((hl τ).2.2 t τ') i) j
      rw [compAt, Matrix.map_apply] at h
      rw [h]
      split_ifs <;> simp
    rw [e1, Finset.sum_congr rfl fun τ _ => e2 τ, Finset.sum_ite_eq]
    simp

theorem dLine_sum {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {ι : Type} (s : Finset ι)
    (N : ι → ℝ →+ WO S T) (hN : ∀ i, Continuous (N i)) (hN0 : ∀ i t, (N i t).map (finPart D) = 0)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    Continuous (⇑(∑ i ∈ s, N i) : ℝ → WO S T) ∧ (∀ t, ((∑ i ∈ s, N i) t).map (finPart D) = 0) ∧
      GlobalTheory.WeilVacMove.dLine ψ S T (∑ i ∈ s, N i) f = ∑ i ∈ s, GlobalTheory.WeilVacMove.dLine ψ S T (N i) f := by
  classical
  refine Finset.induction_on s ?_ ?_
  · refine ⟨?_, fun t => ?_, ?_⟩
    · rw [Finset.sum_empty]
      show Continuous fun _ : ℝ => (0 : WO S T)
      exact continuous_const
    · rw [Finset.sum_empty, AddMonoidHom.zero_apply]; ext i j; simp
    · rw [Finset.sum_empty, Finset.sum_empty]
      funext w
      simp [GlobalTheory.WeilVacMove.dLine]
  · intro a s ha ih
    obtain ⟨h1, h2, h3⟩ := ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    refine ⟨?_, fun t => ?_, ?_⟩
    · show Continuous fun t => N a t + (∑ x ∈ s, N x) t
      exact (hN a).add h1
    · rw [AddMonoidHom.add_apply]
      ext i j
      simp only [Matrix.map_apply, Matrix.add_apply, map_add]
      have ha := congrFun (congrFun (hN0 a t) i) j
      have hs := congrFun (congrFun (h2 t) i) j
      simpa only [Matrix.map_apply, Matrix.zero_apply, add_zero] using congrArg₂ (· + ·) ha hs
    · rw [GlobalTheory.BiJoinDeriv.dLine_add_line hψ (hN a) (hN0 a) h1 h2 hf, h3]

theorem fock_line_J : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ),
    IsStdChar D ψ (-1) → IsInfFam θ → IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) →
    ∀ x x' : WO S T, (∀ τ, compAt θ τ x' = cplxO (sS τ) (sT τ) (compAt θ τ x)) → ∀ w : WO S T, ∃ a : ℂ,
      HasDerivAt (fun t : ℝ => heisO ψ S T (realAd D.host.F t • x) f w) a 0 ∧
      HasDerivAt (fun t : ℝ => heisO ψ S T (realAd D.host.F t • x') f w) (Complex.I * a) 0 := by
  intro D ψ θ S T sS sT f hψ hθ hf hvac x x' hx' w
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hl := fun τ (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) => GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ z
  let c : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ := fun τ => compAt θ τ x
  let c' : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ := fun τ => cplxO (sS τ) (sT τ) (c τ)
  obtain ⟨L1, L2, L3⟩ := dLine_sum hψ Finset.univ (fun τ => lineAt θ τ (c τ)) (fun τ => (hl τ _).1)
    (fun τ => (hl τ _).2.1) hf
  obtain ⟨M1, M2, M3⟩ := dLine_sum hψ Finset.univ (fun τ => lineAt θ τ (c' τ)) (fun τ => (hl τ _).1)
    (fun τ => (hl τ _).2.1) hf
  have e : ∀ t, realAd D.host.F t • x = (∑ τ, lineAt θ τ (c τ)) t :=
    realAd_smul_eq_sum hθ hσ c x (fun τ => rfl)
  have e' : ∀ t, realAd D.host.F t • x' = (∑ τ, lineAt θ τ (c' τ)) t :=
    realAd_smul_eq_sum hθ hσ c' x' hx'
  have hd := (GlobalTheory.WeilVacMove.hasDerivAt_zero_and_isTheta hψ L1 L2 hf).1 w
  have hd' := (GlobalTheory.WeilVacMove.hasDerivAt_zero_and_isTheta hψ M1 M2 hf).1 w
  refine ⟨GlobalTheory.WeilVacMove.dLine ψ S T (∑ τ, lineAt θ τ (c τ)) f w, ?_, ?_⟩
  · simp only [e]
    exact hd
  · have key : GlobalTheory.WeilVacMove.dLine ψ S T (∑ τ, lineAt θ τ (c' τ)) f w =
        Complex.I * GlobalTheory.WeilVacMove.dLine ψ S T (∑ τ, lineAt θ τ (c τ)) f w := by
      rw [L3, M3, Finset.sum_apply, Finset.sum_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      have h : GlobalTheory.WeilVacMove.dLine ψ S T (lineAt θ τ (c τ)) f w +
          Complex.I * GlobalTheory.WeilVacMove.dLine ψ S T (lineAt θ τ (c' τ)) f w = 0 := congrFun (hvac τ (c τ)) w
      linear_combination (-Complex.I) * h + GlobalTheory.WeilVacMove.dLine ψ S T (lineAt θ τ (c' τ)) f w * Complex.I_sq
    simp only [e']
    rw [← key]
    exact hd'

end GlobalTheory.FockLineJ
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.inertPlace_unimodular_hermitianFrame_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a'), B.IsGood σ → G.IsGood B → ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)),
    Formalism.UG.IsInertAt F E v w →
    ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σL : L →+* L) (q : ℕ)
      (δ : L) (ψL : AddChar L ℂ) (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      Formalism.UG.IsUnramInv ϖ σL q → Odd q → (Valued.v δ = 1 ∧ σL δ = -δ) → Function.Injective ι →
      (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ↔ ∃ x, ι x = z) → (∀ x y, ι (x * y) = ι x * ι y) →
      (∀ x, ι (σL x) = cA σ (ι x)) →
      (∀ x, x ∈ Formalism.UG.intL L ↔ ι x ∈ AddSubgroup.closure {z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) | ∃ a : AF F, At (evFin F v) a ∧
        evFin F v a ∈ v.adicCompletionIntegers F ∧ ∃ o : 𝓞 E, z = a • inclR (F := F) (AF F) (o : E)}) →
      (∀ x, B.ψ (Algebra.trace (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (ι x)) = ψL (x + σL x)) →
      ∃ (JS : GL (Fin a) L) (JT : GL (Fin (a + a')) L)
        (Xm : Matrix (Fin (a + a')) (Fin a) L →+ Matrix (Fin a) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
        (iV : Formalism.UG.UJ σL (JS : Matrix (Fin a) (Fin a) L) →* UA σ G.V.J)
        (iW : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →* UA σ G.W.J),
        JS ∈ Formalism.UG.GLint (Fin a) (Formalism.UG.intL L) ∧ JT ∈ Formalism.UG.GLint (Fin (a + a')) (Formalism.UG.intL L) ∧
        (∀ i j, σL ((JS : Matrix (Fin a) (Fin a) L) i j) = (JS : Matrix (Fin a) (Fin a) L) j i) ∧
        (∀ i j, σL ((JT : Matrix (Fin (a + a')) (Fin (a + a')) L) i j) = (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) j i) ∧
        (∀ x y, B.ψ (⅟(2 : AF F) * symp (R := AF F) (cA σ) (-1) (incM F G.V.J) (incM F G.W.J) (Xm x) (Xm y)) =
          ψL ((GlobalTheory.Hk3.locH σL δ JS JT x y + σL (GlobalTheory.Hk3.locH σL δ JS JT x y)) / 2)) ∧
        (∀ z : Matrix (Fin a) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) z ↔ ∃ x, Xm x = z) ∧
        (∀ u : Matrix (Fin (a + a')) (Fin a) L, (∀ i j, u i j ∈ Formalism.UG.intL L) → Xm u ∈ latAtV G.V G.W v) ∧
        (∀ z ∈ latAtV G.V G.W v, ∃ u : Matrix (Fin (a + a')) (Fin a) L, (∀ i j, u i j ∈ Formalism.UG.intL L) ∧ Xm u = z) ∧
        (∀ g h x, actAB (cA σ) (iV g, iW h) (Xm x) =
          Xm (((h : GL (Fin (a + a')) L) : Matrix (Fin (a + a')) (Fin (a + a')) L) * x *
            (((g : GL (Fin a) L)⁻¹ : GL (Fin a) L) : Matrix (Fin a) (Fin a) L))) ∧
        (∀ g, iV g ∈ UAt σ G.V (evFin F v)) ∧ (∀ h, iW h ∈ UAt σ G.W (evFin F v)) ∧
        (∀ g : Formalism.UG.UJ σL (JS : Matrix (Fin a) (Fin a) L), (g : GL (Fin a) L) ∈ Formalism.UG.GLint (Fin a) (Formalism.UG.intL L) →
          iV g ∈ GlobalTheory.InertSph.KAt σ G.V v) ∧
        (∀ h : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L),
          (h : GL (Fin (a + a')) L) ∈ Formalism.UG.GLint (Fin (a + a')) (Formalism.UG.intL L) → iW h ∈ GlobalTheory.InertSph.KAt σ G.W v) := by
  first | exact @GlobalTheory.InertLocFrame.frame | exact GlobalTheory.InertLocFrame.frame | (intros; apply GlobalTheory.InertLocFrame.frame <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertTwoFac

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mul_mem_KAt {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} {v : Pl (F := F)} {g h : UA σ W.J}
    (hg : g ∈ GlobalTheory.InertSph.KAt σ W v) (hh : h ∈ GlobalTheory.InertSph.KAt σ W v) : g * h ∈ GlobalTheory.InertSph.KAt σ W v := by
  have e : mat (g * h) = mat g * mat h := rfl
  have e' : mat (g * h)⁻¹ = mat h⁻¹ * mat g⁻¹ := by rw [mul_inv_rev]; rfl
  refine ⟨fun u hu => ?_, fun z hz => ?_⟩
  · have h1 : u • (mat g - 1) = 0 := hg.1 u hu
    have h2 : u • (mat h - 1) = 0 := hh.1 u hu
    have : mat (g * h) - 1 = (mat g - 1) * mat h + (mat h - 1) := by rw [e]; noncomm_ring
    rw [this, smul_add, ← Matrix.smul_mul, h1, h2, Matrix.zero_mul, add_zero]
  · rw [e, e', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact ⟨(hg.2 _ (hh.2 z hz).1).1, (hh.2 _ (hg.2 z hz).2).2⟩

theorem inv_mem_KAt {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} {v : Pl (F := F)} {h : UA σ W.J}
    (hh : h ∈ GlobalTheory.InertSph.KAt σ W v) : h⁻¹ ∈ GlobalTheory.InertSph.KAt σ W v := by
  have e1 : mat h⁻¹ * mat h = 1 := by
    show mat (h⁻¹ * h) = 1
    rw [inv_mul_cancel]; rfl
  refine ⟨fun u hu => ?_, fun z hz => ?_⟩
  · have h2 : u • (mat h - 1) = 0 := hh.1 u hu
    have : mat h⁻¹ - 1 = -(mat h⁻¹ * (mat h - 1)) := by rw [Matrix.mul_sub, e1]; noncomm_ring
    rw [this, smul_neg, ← Matrix.mul_smul, h2, Matrix.mul_zero, neg_zero]
  · rw [inv_inv]; exact ⟨(hh.2 z hz).2, (hh.2 z hz).1⟩

theorem twoFac : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, ∃ k₁ ∈ GlobalTheory.InertSph.KAt σ G.W v, ∃ k₂ ∈ GlobalTheory.InertSph.KAt σ G.W v,
    (∃ M : Matrix (Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), (1 + mat k₁) * M = 1 ∧ M * (1 + mat k₁) = 1 ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) ∧
    (∃ M : Matrix (Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), (1 + mat k₂) * M = 1 ∧ M * (1 + mat k₂) = 1 ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) ∧ k = k₁ * k₂ := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hin k hk
  obtain ⟨Y, hYat, hYint, hYskew, ⟨Np, hNp1, hNp2, hNpi⟩, hm, ⟨ND, hND1, hND2, hNDi⟩⟩ :=
    GlobalTheory.T.exists_skew_cayley_inertPlace_stabilizer F E σ B a a' G X om om' hT v w hin k hk
  obtain ⟨h, hh, hhY⟩ := GlobalTheory.T.cayleyTransform_mem_unitaryLatticeStabilizer F E σ (a + a') G.W v Y hYat hYint hYskew ⟨Np, hNp1, hNp2, hNpi⟩ hm
  have h2 : (2 : 𝓞 F) ∉ v.asIdeal := (hT.base.inert v w hin).1
  have eH : mat h = (1 - Y) * Np := by rw [← hhY, Matrix.mul_assoc, hNp1, Matrix.mul_one]
  have eH' : (1 + Y) * mat h = 1 - Y := by
    rw [eH, ← Matrix.mul_assoc, show (1 + Y) * (1 - Y) = (1 - Y) * (1 + Y) by noncomm_ring, Matrix.mul_assoc, hNp1,
      Matrix.mul_one]
  have eI : mat h⁻¹ * mat h = 1 := by
    show mat (h⁻¹ * h) = 1
    rw [inv_mul_cancel]; rfl
  have intY1 : ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, (1 + Y) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v := fun z hz => by
    rw [Matrix.add_mulVec, Matrix.one_mulVec]; exact add_mem hz (hYint z hz)
  refine ⟨k * h, mul_mem_KAt hk hh, h⁻¹, inv_mem_KAt hh, ?_, ?_, by group⟩
  · have e : mat (k * h) = mat k * mat h := rfl
    have h1 : (1 + mat (k * h)) * ((1 + Y) * ND) = 1 := by
      have : (1 + mat k * mat h) * (1 + Y) = 1 + Y + mat k * (1 - Y) := by
        rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hhY]
      rw [e, ← Matrix.mul_assoc, this, hND1]
    refine ⟨(1 + Y) * ND, h1, mul_eq_one_comm.1 h1, fun z hz => ?_⟩
    rw [← Matrix.mulVec_mulVec]; exact intY1 _ (hNDi z hz)
  · have h1 : (1 + mat h⁻¹) * ((⅟(2 : AF F)) • ((1 + Y) * mat h)) = 1 := by
      rw [Matrix.mul_smul]
      have : (1 + mat h⁻¹) * ((1 + Y) * mat h) = (2 : AF F) • (1 : Matrix (Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) := by
        have c : (1 + Y) * mat h = mat h * (1 + Y) := eH'.trans hhY.symm
        rw [Matrix.add_mul, Matrix.one_mul, c, ← Matrix.mul_assoc, eI, Matrix.one_mul, hhY, two_smul]
        abel
      rw [this, smul_smul, invOf_mul_self, one_smul]
    refine ⟨_, h1, mul_eq_one_comm.1 h1, fun z hz => ?_⟩
    rw [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec]
    exact GlobalTheory.T.inv_two_smul_mem_adelicLatticeAtFinitePlace F E (a + a') G.W v h2 _ (intY1 _ (hh.2 z hz).1)

end GlobalTheory.InertTwoFac
end
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LinWCoords

theorem exists_split_coords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (t : E →ₐ[F] Fv F v),
    ∃ uT uM : Matrix (Fin a) (Fin (a + a')) (Fv F v) →+ Matrix (Fin a) (Fin (a + a')) (AE F E),
      (∀ Y, At (evFin F v) (uT Y) ∧ (uT Y).map (piW (t.comp σ)) = 0 ∧ (uT Y).map (piW t) = Y) ∧
      (∀ z, At (evFin F v) (uM z) ∧ (uM z).map (piW t) = 0 ∧ GlobalTheory.LinWAt.coW G t (uM z) = z) ∧
      (∀ u, At (evFin F v) u → ∃ Y z, u = uT Y + uM z) ∧
      (∀ x u, At (evFin F v) x → At (evFin F v) u →
        evFin F v (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) x u) =
          ∑ i, ∑ j, (x.map (piW t)) i j * GlobalTheory.LinWAt.coW G t u i j -
            ∑ i, ∑ j, GlobalTheory.LinWAt.coW G t x i j * (u.map (piW t)) i j) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v t
  have hcm := hTr.base.cm
  have hP : IsUnit (G.V.J.map t).det :=
    GlobalTheory.LinBarCoords.det_map_isUnit B G.V.J 1 _ _ one_ne_zero (fun w => by rw [one_smul]; exact hTr.geo.hV.sig w) v t
  have hQ : IsUnit ((G.W.J.map t)ᵀ).det := by
    rw [Matrix.det_transpose]
    exact GlobalTheory.LinBarCoords.det_map_isUnit B G.W.J Complex.I _ _ Complex.I_ne_zero hTr.geo.hW.sig v t
  set P := G.V.J.map t with hPdef
  set Q := (G.W.J.map t)ᵀ with hQdef
  let L := GlobalTheory.LinBarCoords.liftM σ hcm (m := Fin a) (n := Fin (a + a')) v t
  let uT : Matrix (Fin a) (Fin (a + a')) (Fv F v) →+ Matrix (Fin a) (Fin (a + a')) (AE F E) :=
    AddMonoidHom.mk' (fun Y => L (Y, 0)) (fun Y Y' => by rw [← map_add (f := _), Prod.mk_add_mk, add_zero])
  let uM : Matrix (Fin a) (Fin (a + a')) (Fv F v) →+ Matrix (Fin a) (Fin (a + a')) (AE F E) :=
    AddMonoidHom.mk' (fun z => L (0, -(P⁻¹ * z * Q⁻¹))) (fun z z' => by
      rw [Matrix.mul_add, Matrix.add_mul, neg_add, ← map_add (f := _), Prod.mk_add_mk, add_zero])
  have hco : ∀ u, GlobalTheory.LinWAt.coW G t u = -(P * u.map (piW (t.comp σ)) * Q) := fun u => by
    simp [GlobalTheory.LinWAt.coW, hPdef, hQdef]
  have hTc : ∀ Y, (uT Y).map (piW (t.comp σ)) = 0 := fun Y => GlobalTheory.LinBarCoords.liftM_snd σ hcm v t _
  have hTt : ∀ Y, (uT Y).map (piW t) = Y := fun Y => GlobalTheory.LinBarCoords.liftM_fst σ hcm v t _
  have hMc : ∀ z, (uM z).map (piW (t.comp σ)) = -(P⁻¹ * z * Q⁻¹) := fun z => GlobalTheory.LinBarCoords.liftM_snd σ hcm v t _
  have hMt : ∀ z, (uM z).map (piW t) = 0 := fun z => GlobalTheory.LinBarCoords.liftM_fst σ hcm v t _
  have hTa : ∀ Y, At (evFin F v) (uT Y) := fun Y => GlobalTheory.LinBarCoords.liftM_at σ hcm v t _
  have hMa : ∀ z, At (evFin F v) (uM z) := fun z => GlobalTheory.LinBarCoords.liftM_at σ hcm v t _
  refine ⟨uT, uM, fun Y => ⟨hTa Y, hTc Y, hTt Y⟩, fun z => ⟨hMa z, hMt z, ?_⟩, fun u hu => ?_, fun x u hx hu => ?_⟩
  · have e1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hP
    have e2 : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul _ hQ
    rw [hco, hMc, Matrix.mul_neg, Matrix.neg_mul, neg_neg]
    simp only [← Matrix.mul_assoc, e1, Matrix.one_mul]
    simp only [Matrix.mul_assoc, e2, Matrix.mul_one]
  · refine ⟨u.map (piW t), GlobalTheory.LinWAt.coW G t u, ?_⟩
    have hd : At (evFin F v) (u - (uT (u.map (piW t)) + uM (GlobalTheory.LinWAt.coW G t u))) := by
      intro c hc
      rw [smul_sub, smul_add, hu c hc, hTa _ c hc, hMa _ c hc, add_zero, sub_zero]
    refine (sub_eq_zero.1 (GlobalTheory.LinBarCoords.eq_zero_of_at σ hcm v t hd ?_ ?_))
    · rw [Matrix.map_sub _ (map_sub _), Matrix.map_add _ (map_add _), hTt, hMt, add_zero, sub_self]
    · rw [Matrix.map_sub _ (map_sub _), Matrix.map_add _ (map_add _), hTc, hMc, zero_add, hco, Matrix.mul_neg, Matrix.neg_mul,
        neg_neg, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hQ, Matrix.mul_one, ← Matrix.mul_assoc,
        Matrix.nonsing_inv_mul _ hP, Matrix.one_mul, sub_self]
  · have h := GlobalTheory.T.local_lattice_hermitian_skew hcm v t G.V.J G.W.J hTr.geo.hV.herm hTr.geo.hW.skew x u hx
    dsimp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM] at h
    rw [hco, hco]
    exact h

end GlobalTheory.LinWCoords
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped GlobalTheory.VacAny

noncomputable section


theorem _root_.GlobalTheory.T.exists_local_unipotent_additive : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (t : E →ₐ[F] Fv F v),
    ∃ uT uM : Matrix (Fin a') (Fin (a + a')) (Fv F v) →+ Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      (∀ Y, At (evFin F v) (uT Y) ∧ (uT Y).map (piW t) = 0 ∧ GlobalTheory.LinBarAt.coAt G t (uT Y) = Y) ∧
      (∀ z, At (evFin F v) (uM z) ∧ (uM z).map (piW (t.comp σ)) = 0 ∧ (uM z).map (piW t) = -z) ∧
      (∀ u, At (evFin F v) u → ∃ Y z, u = uT Y + uM z) ∧
      (∀ x u, At (evFin F v) x → At (evFin F v) u →
        evFin F v (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) x u) =
          ∑ i, ∑ j, (x.map (piW t)) i j * GlobalTheory.LinBarAt.coAt G t u i j -
            ∑ i, ∑ j, GlobalTheory.LinBarAt.coAt G t x i j * (u.map (piW t)) i j) := by
  first | exact @GlobalTheory.LinBarCoords.exists_split_coords | exact GlobalTheory.LinBarCoords.exists_split_coords | (intros; apply GlobalTheory.LinBarCoords.exists_split_coords <;> assumption)
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.heisenbergInvariantForm_comp_localWeilOperator : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (m : ℕ) (C : Matrix (Fin (a + a')) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
    ∀ l : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ, GlobalTheory.InertVacLag.HeisInv G.M' B.ψ v C l →
    ∀ g ∈ UAt σ G.V' (evFin F v),
    ∀ S : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ((Fin a' × Fin (a + a') → Fv F v) → ℂ),
      (∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), S φ ∈ SB (Fin a' × Fin (a + a') → Fv F v) ∧
        Acts (evFin F v) (om' (g, 1)) φ (S φ)) →
      GlobalTheory.InertVacLag.HeisInv G.M' B.ψ v C (l ∘ₗ S) := by
  first | exact @GlobalTheory.InertVacEquiv.heisInv_comp | exact GlobalTheory.InertVacEquiv.heisInv_comp | (intros; apply GlobalTheory.InertVacEquiv.heisInv_comp <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval

theorem _root_.GlobalTheory.T.local_operator_right_partial_pure : ∀ {F : Type} [Field F] [NumberField F] {κ κ' κ₁' : Type} [Fintype κ] [Fintype κ'] [Fintype κ₁'] (e : ((κ' → AF F) → ℂ) →ₗ[ℂ] (κ₁' → AF F) → ℂ), IsLocOp e → ∃ P : SInf F (κ ⊕ κ') →L[ℂ] SInf F (κ ⊕ κ₁'), ∀ g ∈ SB (κ ⊕ κ' → Af F), ∃ g₁ ∈ SB (κ ⊕ κ₁' → Af F), ∀ f : SInf F (κ ⊕ κ'), partR e (pureA F f g) = pureA F (P f) g₁ := by
  first | exact @GlobalTheory.DblEval.BlockSwap.partR_pureA | exact GlobalTheory.DblEval.BlockSwap.partR_pureA | (intros; apply GlobalTheory.DblEval.BlockSwap.partR_pureA <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval

theorem _root_.GlobalTheory.T.local_operators_product_compatible : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (e : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (ei : SInf F κ →L[ℂ] SInf F κ)
    (ev : ∀ v : Pl (F := F), ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ),
    (∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v φ ∈ SB (κ → Fv F v)) →
    (∀ᶠ v in cofinite, ev v (stdInd F κ v) = stdInd F κ v) →
    (∀ (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ), (∀ v, φ v ∈ SB (κ → Fv F v)) →
      (∀ᶠ v in cofinite, φ v = stdInd F κ v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    Set.SurjOn e (schA F κ : Set ((κ → AF F) → ℂ)) (schA F κ : Set ((κ → AF F) → ℂ)) →
    (∀ v, ev v (stdInd F κ v) ≠ 0) →
    ∀ v, ∀ χ ∈ SB (κ → Fv F v), ∃ ψ ∈ SB (κ → Fv F v), ev v ψ = χ := by
  first | exact @GlobalTheory.EvOnto.ev_surjOn_SB | exact GlobalTheory.EvOnto.ev_surjOn_SB | (intros; apply GlobalTheory.EvOnto.ev_surjOn_SB <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval

theorem _root_.GlobalTheory.T.bijective_infinite_part_of_restricted_product : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (e : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (ei : SInf F κ →L[ℂ] SInf F κ)
    (ev : ∀ v : Pl (F := F), ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ),
    (∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v φ ∈ SB (κ → Fv F v)) →
    (∀ᶠ v in cofinite, ev v (stdInd F κ v) = stdInd F κ v) →
    (∀ (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ), (∀ v, φ v ∈ SB (κ → Fv F v)) →
      (∀ᶠ v in cofinite, φ v = stdInd F κ v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    Set.BijOn e (schA F κ : Set ((κ → AF F) → ℂ)) (schA F κ : Set ((κ → AF F) → ℂ)) →
    (∀ v, ev v (stdInd F κ v) ≠ 0) → Function.Bijective ei := by
  first | exact @GlobalTheory.ArchBij.bijective_arch | exact GlobalTheory.ArchBij.bijective_arch | (intros; apply GlobalTheory.ArchBij.bijective_arch <;> assumption)
end
