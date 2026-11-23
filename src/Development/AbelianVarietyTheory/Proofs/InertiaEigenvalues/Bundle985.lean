module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle048
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle043
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermCColMulVec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesSecond
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle029
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle977
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2280
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqConstMulOfNormOne
public import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LinkFD
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle034
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle914
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle984
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle043
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLetterRowWeightDictionary
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle036
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle915
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
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle843
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle854
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.FirstMinimumInvariantContinuousPos
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle028
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalDecayHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle021
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle033
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds

@[expose] public section

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries
open CategoryTheory

noncomputable section

namespace GlobalTheory.CoverConstMove

theorem kappa_eq {D : D7} {r : ℕ} (X X' : Data D.host.E r) (hψ : X.Ψ = X'.Ψ) (hξ : X.ξ0 = X'.ξ0) : X.κ0 = X'.κ0 := by
  obtain ⟨τ, hτ⟩ : ∃ τ, τ ∈ X.Ψ := by
    by_cases h0 : D.host.φ₀ ∈ X.Ψ
    · exact ⟨_, h0⟩
    · exact ⟨_, not_not.1 (mt (X.cmType _).2 h0)⟩
  have s₁ := X.κ0_sign ⟨τ, hτ⟩
  have s₂ := X'.κ0_sign ⟨τ, hψ ▸ hτ⟩
  simp only at s₁ s₂
  rcases X.κ0_xi with h1 | h1 <;> rcases X'.κ0_xi with h2 | h2
  · rw [h1, h2, hξ]
  · exfalso
    rw [h1, hξ] at s₁
    rw [h2, map_neg, Complex.neg_im] at s₂
    linarith
  · exfalso
    rw [h2, ← hξ] at s₂
    rw [h1, map_neg, Complex.neg_im] at s₁
    linarith
  · rw [h1, h2, hξ]



theorem const_cover : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D (T.V j σ) →* Module.End ℂ (WO V (T.V j σ) → ℂ)), IsPair ψ θ V (T.V j σ) χV χW om → ∀ hr : (T.V j σ).rank = D.R.r, (∀ k, IsMod (T.V j σ) hr ((T.U j σ).X k)) → ∀ (h : GA D (T.V j σ)) (δ : GL (Fin D.R.r) D.host.E), (((T.U j σ).X (T.dict j σ h).1).Λ : Set (Fin D.R.r → D.host.E)) = (δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec '' ((C.U₂.X (C.dict₂ h).1).Λ : Set _) → (∀ v w, herm ((T.U j σ).X (T.dict j σ h).1).Gm ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm (C.U₂.X (C.dict₂ h).1).Gm v w) → (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X (C.dict₂ h).1).Ψ) (h₁ : τ ∈ ((T.U j σ).X (T.dict j σ h).1).Ψ), mat (T.dict j σ h).2 ⟨τ, h₁⟩ = (δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat (C.dict₂ h).2 ⟨τ, h₂⟩) → ∀ γ : GA D (T.V j σ), (∀ τ ∈ ((T.U j σ).X (T.dict j σ h).1).Ψ, Matrix.reindex (finCongr hr) (finCongr hr) (realM θ (Formalism.L2.Theta.mt (T.V j σ) γ) τ) = (δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ) → ∀ (hx₁ : (T.dict j σ h).2 ∈ ((T.U j σ).X (T.dict j σ h).1).dom) (hx₂ : (C.dict₂ h).2 ∈ (C.U₂.X (C.dict₂ h).1).dom), IsUnitFr ((T.U j σ).X (T.dict j σ h).1) (T.dict j σ h).2 → ∀ (F₁ F₂ : WO V (T.V j σ) → ℂ) (m₁ m₂ : ℂ), (∀ (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (C.U₂.X (C.dict₂ h).1).Λ) (idx : Fin g ≃ (C.U₂.X (C.dict₂ h).1).Ψ × Fin D.R.r) (e : Fin g ≃ Lt1 (T.Q.Dw j)), IsSympl (C.U₂.X (C.dict₂ h).1) bas → IdxIs C.d.c₂ C.σ₂ (C.U₂.X (C.dict₂ h).1) idx e → ∀ ϑ : (Fin g → ℂ) → ℂ, GenReads C.U₂ (C.dict₂ h).1 bas idx e ⟨(C.dict₂ h).2, hx₂⟩ ϑ → ∀ w : WO V (T.V j σ), w.map (finPart D) = 0 → F₁ w = m₁ * cexp (-(Real.pi / 2 : ℂ) * ∑ b, hx (C.U₂.X (C.dict₂ h).1) bas idx (C.dict₂ h).2 (zOf θ V (T.V j σ) hr (C.U₂.X (C.dict₂ h).1) idx (C.dict₂ h).2 w b) (zOf θ V (T.V j σ) hr (C.U₂.X (C.dict₂ h).1) idx (C.dict₂ h).2 w b)) * ∏ b, ϑ (zOf θ V (T.V j σ) hr (C.U₂.X (C.dict₂ h).1) idx (C.dict₂ h).2 w b)) → (∀ (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] ((T.U j σ).X (T.dict j σ h).1).Λ) (idx : Fin g ≃ ((T.U j σ).X (T.dict j σ h).1).Ψ × Fin D.R.r) (e : Fin g ≃ Lt1 (T.Q.Dw j)), IsSympl ((T.U j σ).X (T.dict j σ h).1) bas → IdxIs T.Q.c σ ((T.U j σ).X (T.dict j σ h).1) idx e → ∀ ϑ : (Fin g → ℂ) → ℂ, GenReads (T.U j σ) (T.dict j σ h).1 bas idx e ⟨(T.dict j σ h).2, hx₁⟩ ϑ → ∀ w : WO V (T.V j σ), w.map (finPart D) = 0 → F₂ w = m₂ * cexp (-(Real.pi / 2 : ℂ) * ∑ b, hx ((T.U j σ).X (T.dict j σ h).1) bas idx (T.dict j σ h).2 (zOf θ V (T.V j σ) hr ((T.U j σ).X (T.dict j σ h).1) idx (T.dict j σ h).2 w b) (zOf θ V (T.V j σ) hr ((T.U j σ).X (T.dict j σ h).1) idx (T.dict j σ h).2 w b)) * ∏ b, ϑ (zOf θ V (T.V j σ) hr ((T.U j σ).X (T.dict j σ h).1) idx (T.dict j σ h).2 w b)) → (∀ w, F₂ (actO V (T.V j σ) 1 γ w) = F₁ w) → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ), ∀ f ∈ sec (T.Q.Xo j) T.Q.c a V.rank, ∀ f₂ ∈ sec C.d.Xo₂ C.d.c₂ a V.rank, C.IsPull f f₂ → m₁ * rdU C.U₂ f₂ (C.dict₂ h).1 (C.dict₂ h).2 = m₂ * rdU (T.U j σ) f (T.dict j σ h).1 (T.dict j σ h).2 := by
  intro D T hT j hj σ hσ C hC ψ θ V χV χW om hP hr hM h δ hΛ hiso hfr γ hγ hx₁ hx₂ hu F₁ F₂ m₁ m₂ c₁ c₂ hF a f hf f₂ hf₂ hp
  obtain ⟨o₁, o₂⟩ := GlobalTheory.CoverFrameOver.un_over D T hT j hj σ hσ C hC h δ hΛ hiso hfr _ _ hx₂ hx₁ hfr
  obtain ⟨t, ht, hval, hlift⟩ := GlobalTheory.T.exists_scalar_levelCover_analyticFibre D T j σ C hC.1 hC.2.2.1 _ _ o₁ o₂
  obtain ⟨hlev, hA₂, hσ₂, hU₂, hdom, hr₂, g₂, e₂, F₂', ik₂, φ₂, th₂, hW₂, hth₂, -⟩ := hC
  have hU := hT.unf j hj σ hσ
  obtain ⟨-, -, -, -, -, -, hnum⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q hT.pins
  have hr1 : 1 ≤ D.R.r := (hnum _ hj).2.1
  obtain ⟨Wt⟩ := nonempty_uw (U := Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) hU
  have hSD : ∀ k, SelfD ((T.U j σ).X k) ((T.U j σ).X k).Λ := fun k => (GlobalTheory.T.uniformisation_component_lattices_markings _ _ _ _ _ _ σ _ (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) hσ hU hr1 Wt k).2.1
  obtain ⟨Dc, hDc, -⟩ := GlobalTheory.Dict.exists_dic _ _ _ _ _ σ _ Wt.g 0 ((T.U j σ).X (T.dict j σ h).1) 0 Wt.e hσ hU.1
    (hU.2.1 _).1 (hU.2.1 _).2 (hSD _) ⟨fun _ => antitone_const, Even.zero⟩
  have hi : IdxIs T.Q.c σ ((T.U j σ).X (T.dict j σ h).1) Dc.idx Wt.e := hDc ▸ ⟨Dc.per_eq, Dc.ty_eq⟩
  obtain ⟨A, hmk, ϑ, hϑ, hone⟩ := GlobalTheory.Dict.uw_anFib _ _ _ _ _ _ σ _ (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) hσ hU hr1 Wt _
    Dc.bas Dc.idx Dc.sympl hi.1 hi.2 ⟨_, hx₁⟩ hu
  obtain ⟨A₂, r₂⟩ := hlift _ _ _ Dc.bas Dc.idx Wt.e _ _ (Wt.mark _) Dc.sympl hx₁ (hSD _) ϑ ⟨A, hmk, hϑ⟩
  have hΨ : ∀ τ, τ ∈ ((T.U j σ).X (T.dict j σ h).1).Ψ ↔ τ ∈ (C.U₂.X (C.dict₂ h).1).Ψ := fun τ =>
    ((hU.2.1 _).2 τ).trans ((hU₂.2.1 _).2 τ).symm
  have hξ : ((T.U j σ).X (T.dict j σ h).1).ξ0 = (C.U₂.X (C.dict₂ h).1).ξ0 := (hM _).model.2.trans (hW₂ _).2.symm
  have hS : SameSp ((T.U j σ).X (T.dict j σ h).1) (C.U₂.X (C.dict₂ h).1) :=
    ⟨Finset.ext hΨ, (hM _).model.1.trans (hW₂ _).1.symm, (hU.2.1 _).1.trans (hU₂.2.1 _).1.symm, hξ,
      kappa_eq _ _ (Finset.ext hΨ) hξ⟩
  have hS' : SameSp (C.U₂.X (C.dict₂ h).1) ((T.U j σ).X (T.dict j σ h).1) :=
    ⟨hS.psi.symm, hS.gm.symm, hS.p0.symm, hS.xi.symm, hS.ka.symm⟩
  have hδ₂ : IsUn (C.U₂.X (C.dict₂ h).1) δ⁻¹ := fun u v => by
    have e := hiso ((δ⁻¹).1 *ᵥ u) ((δ⁻¹).1 *ᵥ v)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, Matrix.one_mulVec, hS.gm] at e
    exact e.symm
  have hδ₁ : IsUn ((T.U j σ).X (T.dict j σ h).1) δ := fun u v => by
    rw [hiso u v, hS.gm]
  obtain ⟨idx₂, hi₂, hpv, hty, hidx⟩ := GlobalTheory.FrameConstMove.exists_idx hS hi
  have hSD₁₂ : SelfD (C.U₂.X (C.dict₂ h).1) ((T.U j σ).X (T.dict j σ h).1).Λ := by
    refine ⟨(hSD _).1, fun v => ((hSD (T.dict j σ h).1).2 v).trans ?_⟩
    exact forall₂_congr fun y _ => by rw [hS.EF_eq]
  have hmt : GlobalTheory.LevelCusp.IsMatch (C.U₂.X (C.dict₂ h).1) ((T.U j σ).X (T.dict j σ h).1) δ := by
    refine ⟨hS.psi.symm, hS.p0.symm, hS.xi.symm, hiso, fun v => ⟨fun hv => ?_, fun hv => ?_⟩⟩
    · show δ.1 *ᵥ v ∈ (((T.U j σ).X (T.dict j σ h).1).Λ : Set (Fin D.R.r → D.host.E))
      rw [hΛ]
      exact ⟨v, hv, rfl⟩
    · have hv' : δ.1 *ᵥ v ∈ (((T.U j σ).X (T.dict j σ h).1).Λ : Set (Fin D.R.r → D.host.E)) := hv
      rw [hΛ] at hv'
      obtain ⟨u, hu', e⟩ := hv'
      have e' := congrArg (fun w => (δ⁻¹).1 *ᵥ w) e
      simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at e'
      exact e' ▸ hu'
  have hlat : mapL δ⁻¹ ((T.U j σ).X (T.dict j σ h).1).Λ = (C.U₂.X (C.dict₂ h).1).Λ := by
    ext v
    rw [Lev.mem_mapL, Lev.lin_apply, inv_inv]
    exact (hmt.lat v).symm
  have hSD₂ : SelfD (C.U₂.X (C.dict₂ h).1) (C.U₂.X (C.dict₂ h).1).Λ := hlat ▸ Lev.selfD_mapL hδ₂ hSD₁₂
  obtain ⟨bas₂, hb₂⟩ := GlobalTheory.Dict.Letters.exists_isSympl (C.U₂.X (C.dict₂ h).1) hSD₂ idx₂
  have hx1eq : (T.dict j σ h).2 = lact δ (castFr hmt.psi (C.dict₂ h).2) := funext fun τ => by
    change mat (T.dict j σ h).2 τ = δ.1.map τ.1 * mat (C.dict₂ h).2 ⟨τ.1, _⟩
    exact hfr τ.1 _ τ.2
  have hfr₂ : lact δ⁻¹ (castFr hS.psi (T.dict j σ h).2) = (C.dict₂ h).2 := funext fun τ => by
    change (δ⁻¹).1.map τ.1 * mat (T.dict j σ h).2 ⟨τ.1, _⟩ = mat (C.dict₂ h).2 τ
    rw [hfr τ.1 τ.2, ← Matrix.mul_assoc, ← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.one_mul]
  obtain ⟨-, -, -, A₃, r₃, -, -⟩ := letI : Algebra C.d.c₂.F ℂ := C.σ₂.toAlgebra
    GlobalTheory.Dict.anFib_move _ _ _ _ _ _ _ _ _ _ hS Dc.bas Dc.idx bas₂ idx₂ Wt.e _ _ _ A₂ δ⁻¹ Dc.sympl hb₂ hx₁ (hSD _) hδ₂
      (hpv _) hty
  have g₂ : GenReads C.U₂ (C.dict₂ h).1 bas₂ idx₂ Wt.e ⟨_, hx₂⟩ fun z => t * ϑ z := by
    have := r₃ _ r₂
    clear r₃
    revert A₃
    rw [hlat, hfr₂]
    exact fun A₃ h => ⟨A₃, h⟩
  have hrel : ∀ τ : D.host.E →+* ℂ, relab T.Q.c σ τ = relab C.d.c₂ C.σ₂ τ := fun τ => by
    ext a
    exact (RingHom.congr_fun hσ₂ _).symm.trans (congrArg C.σ₂ (Subtype.ext rfl))
  have hi₂' : IdxIs C.d.c₂ C.σ₂ (C.U₂.X (C.dict₂ h).1) idx₂ Wt.e :=
    ⟨fun x v j' => (hi₂.1 x v j').trans (by rw [hrel]), fun j' => (hi₂.2 j').trans (hrel _)⟩
  have hM₂ : IsMod (T.V j σ) hr (C.U₂.X (C.dict₂ h).1) :=
    ⟨hW₂ _, fun τ => (hΨ τ).symm.trans ((hM _).psi τ), hS.ka.symm.trans (hM _).kap⟩
  obtain ⟨z, hz⟩ := GlobalTheory.FrameConstMove.exists_ne_zero_of_meanOne hone
  obtain ⟨pt, -, hpt, -⟩ := (GlobalTheory.AdTh.RealCoord.zOf_coordinates D ψ θ V (T.V j σ) _ _ hr (C.U₂.X (C.dict₂ h).1) bas₂ idx₂
    hP.weil.std hP.inf hP.std hP.even hM₂ hb₂ (C.dict₂ h).2).2.2.2.2 hx₂
  obtain ⟨w0, wz⟩ := hpt fun _ => z
  generalize pt (fun _ => z) = w at w0 wz
  have wz' : zOf θ V (T.V j σ) hr ((T.U j σ).X (T.dict j σ h).1) Dc.idx (T.dict j σ h).2 (actO V (T.V j σ) 1 γ w) =
      fun _ => z := by
    rw [← wz]
    funext b j'
    have hid : Dc.idx j' = (⟨(idx₂ j').1.1, hmt.psi.le (idx₂ j').1.2⟩, (idx₂ j').2) := by
      have e := hidx j'
      refine Prod.ext (Subtype.ext ?_) ?_
      · rw [e]
      · rw [e]
    refine Eq.trans ?_ (GlobalTheory.FrameConstMove.perC_match hmt (C.dict₂ h).2
      (fun τ a => realM θ w τ (Fin.cast hr.symm a) b) (idx₂ j').1 (idx₂ j').2)
    show perC _ _ _ (Dc.idx j') = _
    rw [hid, hx1eq]
    refine congrArg (fun u => perC _ _ u _) (funext fun τ => funext fun a' => ?_)
    rw [GlobalTheory.FrameConstMove.actO_one_left, GlobalTheory.FrameConstMove.realM_mul, ← hγ τ.1 τ.2]
    exact Fintype.sum_equiv (finCongr hr) _ _ fun c => rfl
  have v₂ := c₂ _ Dc.bas Dc.idx Wt.e Dc.sympl hi ϑ ⟨A, hϑ⟩ (actO V (T.V j σ) 1 γ w)
    (by rw [GlobalTheory.FrameConstMove.actO_one_left, Matrix.map_mul, w0, Matrix.mul_zero])
  have v₁ := c₁ _ bas₂ idx₂ Wt.e hb₂ hi₂' _ g₂ w w0
  rw [hF, wz'] at v₂
  rw [v₂, wz] at v₁
  have hxx : ∀ z w, hx ((T.U j σ).X (T.dict j σ h).1) Dc.bas Dc.idx (T.dict j σ h).2 z w =
      hx (C.U₂.X (C.dict₂ h).1) bas₂ idx₂ (C.dict₂ h).2 z w := by
    intro z' w'
    rw [hx1eq]
    exact GlobalTheory.FrameConstMove.hx_match hS' hb₂ Dc.sympl hx₂ (fun v => (hpv (castFr hS'.psi (C.dict₂ h).2) v).symm) hδ₁ z' w'
  simp only [hxx, Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow] at v₁
  have key : m₁ * t ^ V.rank = m₂ := by
    have hne : cexp (-(Real.pi / 2 : ℂ) * ∑ b : Fin V.rank, hx (C.U₂.X (C.dict₂ h).1) bas₂ idx₂ (C.dict₂ h).2 z z) *
        ϑ z ^ V.rank ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _) (pow_ne_zero _ hz)
    apply mul_right_cancel₀ hne
    linear_combination -v₁
  have u₁ : rdU C.U₂ f₂ (C.dict₂ h).1 (C.dict₂ h).2 = toC (evR C.d.Xo₂ C.d.c₂ f₂ (C.U₂.un _ ⟨_, hx₂⟩)) := dif_pos hx₂
  have u₂ : rdU (T.U j σ) f (T.dict j σ h).1 (T.dict j σ h).2 =
      toC (evR (T.Q.Xo j) T.Q.c f ((T.U j σ).un _ ⟨_, hx₁⟩)) := dif_pos hx₁
  rw [u₁, u₂, hval V.rank a f hf f₂ hp, ← key]
  ring

end GlobalTheory.CoverConstMove
end
end

section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GoodPts

theorem _root_.GlobalTheory.T.cuspidal_section_bounded_nonzero_multiple : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ), p.Prime → (p : 𝓞 c.F) ∈ la.asIdeal → l.GoodAt p → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), Dom a n → f ∈ cusp Xo c U a n → ∃ κ : c.F, κ ≠ 0 ∧ BddAll Xo c la κ f := by
  first | exact @GlobalTheory.CuspBound.exists_bddAll_cusp | exact GlobalTheory.CuspBound.exists_bddAll_cusp | (intros; apply GlobalTheory.CuspBound.exists_bddAll_cusp <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CoverHol
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem hermC_move (X X₂ : Data E r) {γ : Matrix (Fin r) (Fin r) E}
    (hγ : ∀ v w, herm X.Gm (γ *ᵥ v) (γ *ᵥ w) = herm X₂.Gm v w) (τ : E →+* ℂ) (u w : Fin r → ℂ) :
    hermC τ X.Gm ((γ.map τ) *ᵥ u) ((γ.map τ) *ᵥ w) = hermC τ X₂.Gm u w := by
  have h1 : ((1 : Matrix (Fin r) (Fin r) E).map τ) = 1 := Matrix.map_one τ τ.map_zero τ.map_one
  conv_rhs => rw [← Matrix.one_mulVec u, ← Matrix.one_mulVec w, ← h1]
  rw [CompactEntryBounds.hermC_expand X, CompactEntryBounds.hermC_expand X₂]
  simp only [hγ, Matrix.one_mulVec]

theorem col_mul (A Y : Matrix (Fin r) (Fin r) ℂ) (c : Fin r) :
    ReciprocityTheory.ChartRestriction.G.FD.col (A * Y) c = A *ᵥ ReciprocityTheory.ChartRestriction.G.FD.col Y c := by
  funext i; simp [ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem gram_move (X X₂ : Data E r) {γ : Matrix (Fin r) (Fin r) E}
    (hγ : ∀ v w, herm X.Gm (γ *ᵥ v) (γ *ᵥ w) = herm X₂.Gm v w) (τ : E →+* ℂ)
    (Y : Matrix (Fin r) (Fin r) ℂ) :
    ReciprocityTheory.ChartRestriction.G.FD.gram τ X.Gm (γ.map τ * Y) = ReciprocityTheory.ChartRestriction.G.FD.gram τ X₂.Gm Y := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, Matrix.of_apply]
  rw [col_mul, col_mul, hermC_move X X₂ hγ]

def majM (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (p : ℕ) (hp : p ≤ r) (M : Matrix (Fin r) (Fin r) ℂ)
    (v : Fin r → ℂ) : ℝ :=
  2 * (∑ a : Fin p, ∑ b : Fin p,
    hermC τ G v (ReciprocityTheory.ChartRestriction.G.FD.col M (Fin.castLE hp a)) *
      ((ReciprocityTheory.ChartRestriction.G.FD.gram τ G M).submatrix (Fin.castLE hp) (Fin.castLE hp))⁻¹ a b *
      conj (hermC τ G v (ReciprocityTheory.ChartRestriction.G.FD.col M (Fin.castLE hp b)))).re - (hermC τ G v v).re

theorem maj_eq (X : Data E r) (x : Frame X.Ψ r) (τ : X.Ψ) (v : Fin r → ℂ) :
    X.maj x τ v = majM τ.1 X.Gm X.p0 X.p0_le (mat x τ) v := rfl

omit [NumberField E] [IsCMField E] in
theorem majM_congr (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {p q : ℕ} (hp : p ≤ r) (hq : q ≤ r) (h : p = q)
    (M : Matrix (Fin r) (Fin r) ℂ) (v : Fin r → ℂ) : majM τ G p hp M v = majM τ G q hq M v := by
  subst h; rfl

theorem majM_move (X X₂ : Data E r) {γ : Matrix (Fin r) (Fin r) E}
    (hγ : ∀ v w, herm X.Gm (γ *ᵥ v) (γ *ᵥ w) = herm X₂.Gm v w) (τ : E →+* ℂ) {p : ℕ} (hp : p ≤ r)
    (M : Matrix (Fin r) (Fin r) ℂ) (v : Fin r → ℂ) :
    majM τ X.Gm p hp (γ.map τ * M) (γ.map τ *ᵥ v) = majM τ X₂.Gm p hp M v := by
  unfold majM
  simp only [col_mul, hermC_move X X₂ hγ, gram_move X X₂ hγ]

theorem maj_move (X X₂ : Data E r) {γ : Matrix (Fin r) (Fin r) E}
    (hγ : ∀ v w, herm X.Gm (γ *ᵥ v) (γ *ᵥ w) = herm X₂.Gm v w) (hp : X.p0 = X₂.p0)
    (x : Frame X₂.Ψ r) (x' : Frame X.Ψ r) (τ : E →+* ℂ) (h₂ : τ ∈ X₂.Ψ) (h₁ : τ ∈ X.Ψ)
    (hrel : mat x' ⟨τ, h₁⟩ = γ.map τ * mat x ⟨τ, h₂⟩) (v : Fin r → E) :
    X.maj x' ⟨τ, h₁⟩ (Data.emb τ (γ *ᵥ v)) = X₂.maj x ⟨τ, h₂⟩ (Data.emb τ v) := by
  rw [maj_eq, maj_eq, hrel, ← ReciprocityTheory.ChartRestriction.G.AR.Inst.emb_mulVec, majM_move X X₂ hγ]
  exact majM_congr _ _ _ _ hp _ _

theorem dmin_move (X X₂ : Data E r) {γ : Matrix (Fin r) (Fin r) E}
    (hγ : ∀ v w, herm X.Gm (γ *ᵥ v) (γ *ᵥ w) = herm X₂.Gm v w)
    (x : Frame X₂.Ψ r) (x' : Frame X.Ψ r) (τ : E →+* ℂ) (h₂ : τ ∈ X₂.Ψ) (h₁ : τ ∈ X.Ψ)
    (hrel : mat x' ⟨τ, h₁⟩ = γ.map τ * mat x ⟨τ, h₂⟩) (i : Fin (r + 1)) :
    dmin X.Gm x' ⟨τ, h₁⟩ i = dmin X₂.Gm x ⟨τ, h₂⟩ i := by
  unfold dmin
  rw [hrel, gram_move X X₂ hγ]

theorem pnorm_move (X X₂ : Data E r) (hΨ : ∀ τ, τ ∈ X₂.Ψ ↔ τ ∈ X.Ψ) {γ : Matrix (Fin r) (Fin r) E}
    (hγ : ∀ v w, herm X.Gm (γ *ᵥ v) (γ *ᵥ w) = herm X₂.Gm v w) (la : Wt X.Ψ r) (la₂ : Wt X₂.Ψ r)
    (hla : ∀ τ (h₂ : τ ∈ X₂.Ψ) (h₁ : τ ∈ X.Ψ) i, la₂ ⟨τ, h₂⟩ i = la ⟨τ, h₁⟩ i)
    (P : Frame X.Ψ r → ℂ) (P₂ : Frame X₂.Ψ r → ℂ) (x : Frame X₂.Ψ r) (x' : Frame X.Ψ r)
    (hrel : ∀ τ (h₂ : τ ∈ X₂.Ψ) (h₁ : τ ∈ X.Ψ), mat x' ⟨τ, h₁⟩ = γ.map τ * mat x ⟨τ, h₂⟩)
    (u : ℂ) (hu : ‖u‖ = 1) (hP : P₂ x = u * P x') :
    X₂.pnorm la₂ P₂ x = X.pnorm la P x' := by
  unfold Data.pnorm
  rw [hP, norm_mul, hu, one_mul]
  congr 1
  refine Fintype.prod_equiv (Equiv.subtypeEquivRight hΨ) _ _ (fun τ => ?_)
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have h₁ : τ.1 ∈ X.Ψ := (hΨ τ.1).1 τ.2
  show _ = ‖dmin X.Gm x' ⟨τ.1, h₁⟩ i.succ / dmin X.Gm x' ⟨τ.1, h₁⟩ i.castSucc‖ ^ (-(la ⟨τ.1, h₁⟩ i : ℝ) / 2)
  rw [dmin_move X X₂ hγ x x' τ.1 τ.2 h₁ (hrel τ.1 τ.2 h₁), dmin_move X X₂ hγ x x' τ.1 τ.2 h₁ (hrel τ.1 τ.2 h₁),
    ← hla τ.1 τ.2 h₁ i]

theorem exists_firstMinimumSq_bound_of_rationalIsometry (X X₂ : Data E r) (hr : 0 < r) (hΨ : ∀ τ, τ ∈ X₂.Ψ ↔ τ ∈ X.Ψ) (γ : GL (Fin r) E)
    (hΛ : (X.Λ : Set (Fin r → E)) = (γ : Matrix (Fin r) (Fin r) E).mulVec '' (X₂.Λ : Set (Fin r → E)))
    (hγ : ∀ v w, herm X.Gm ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ w) =
      herm X₂.Gm v w) (hp : X.p0 = X₂.p0) :
    ∃ K : ℝ, 0 < K ∧ ∀ x ∈ X₂.dom, ∀ x' ∈ X.dom,
      (∀ τ (h₂ : τ ∈ X₂.Ψ) (h₁ : τ ∈ X.Ψ), mat x' ⟨τ, h₁⟩ = (γ : Matrix (Fin r) (Fin r) E).map τ * mat x ⟨τ, h₂⟩) →
      X.firstMinimumSq x' ≤ K * X₂.firstMinimumSq x := by
  set K : ℝ := 1 + ∑ τ : X₂.Ψ, X.c ⟨τ.1, (hΨ τ.1).1 τ.2⟩ / X₂.c τ with hKdef
  have hc2 : ∀ τ : X₂.Ψ, 0 < X₂.c τ := fun τ => IsotropicThreshold.c_pos X₂ τ
  have hKτ : ∀ τ : X₂.Ψ, X.c ⟨τ.1, (hΨ τ.1).1 τ.2⟩ ≤ K * X₂.c τ := by
    intro τ
    have h1 : X.c ⟨τ.1, (hΨ τ.1).1 τ.2⟩ / X₂.c τ ≤ K := by
      have := Finset.single_le_sum (f := fun τ : X₂.Ψ => X.c ⟨τ.1, (hΨ τ.1).1 τ.2⟩ / X₂.c τ)
        (fun τ _ => (div_pos (IsotropicThreshold.c_pos X _) (hc2 τ)).le) (Finset.mem_univ τ)
      linarith
    rwa [div_le_iff₀ (hc2 τ)] at h1
  have hK : 0 < K := by
    have := Finset.sum_nonneg (fun τ (_ : τ ∈ (Finset.univ : Finset X₂.Ψ)) =>
      (div_pos (IsotropicThreshold.c_pos X ⟨τ.1, (hΨ τ.1).1 τ.2⟩) (hc2 τ)).le)
    linarith
  refine ⟨K, hK, fun x hx x' hx' hrel => ?_⟩
  obtain ⟨w₀, hw₀, hw₀0⟩ := ReciprocityTheory.ChartRestriction.G.AR.Inst.lam_ne X₂ hr
  unfold Data.firstMinimumSq
  set S := {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = ∑ τ, X.c τ * X.maj x' τ (Data.emb τ.1 v)} with hS
  set S₂ := {t | ∃ v ∈ X₂.Λ, v ≠ 0 ∧ t = ∑ τ, X₂.c τ * X₂.maj x τ (Data.emb τ.1 v)} with hS₂
  have hSb : BddBelow S := ⟨0, by
    rintro _ ⟨v, -, hv0, rfl⟩
    exact Finset.sum_nonneg fun τ _ => mul_nonneg (IsotropicThreshold.c_pos X τ).le
      (X.maj_pos hx' τ (emb_ne_zero τ.1 hv0)).le⟩
  have hS₂ne : S₂.Nonempty := ⟨_, w₀, hw₀, hw₀0, rfl⟩
  have key : sInf S / K ≤ sInf S₂ := by
    refine le_csInf hS₂ne ?_
    rintro _ ⟨w, hw, hw0, rfl⟩
    rw [div_le_iff₀ hK]
    have hγw : (γ : Matrix (Fin r) (Fin r) E) *ᵥ w ∈ X.Λ := by
      have : (γ : Matrix (Fin r) (Fin r) E) *ᵥ w ∈ (X.Λ : Set (Fin r → E)) := by
        rw [hΛ]; exact ⟨w, hw, rfl⟩
      exact this
    have hγw0 : (γ : Matrix (Fin r) (Fin r) E) *ᵥ w ≠ 0 := by
      intro h0
      apply hw0
      have e : (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ ((γ : Matrix (Fin r) (Fin r) E) *ᵥ w)) = w := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      rw [← e, h0, Matrix.mulVec_zero]
    refine (csInf_le hSb ⟨_, hγw, hγw0, rfl⟩).trans ?_
    have hre : ∑ τ : X.Ψ, X.c τ * X.maj x' τ (Data.emb τ.1 ((γ : Matrix (Fin r) (Fin r) E) *ᵥ w)) =
        ∑ τ : X₂.Ψ, X.c ⟨τ.1, (hΨ τ.1).1 τ.2⟩ * X₂.maj x τ (Data.emb τ.1 w) := by
      refine (Fintype.sum_equiv (Equiv.subtypeEquivRight hΨ) _ _ (fun τ => ?_)).symm
      show X.c ⟨τ.1, (hΨ τ.1).1 τ.2⟩ * X₂.maj x τ (Data.emb τ.1 w) = X.c ⟨τ.1, (hΨ τ.1).1 τ.2⟩ *
        X.maj x' ⟨τ.1, (hΨ τ.1).1 τ.2⟩ (Data.emb τ.1 ((γ : Matrix (Fin r) (Fin r) E) *ᵥ w))
      rw [maj_move X X₂ hγ hp x x' τ.1 τ.2 ((hΨ τ.1).1 τ.2) (hrel τ.1 τ.2 _)]
    rw [hre, Finset.sum_mul]
    refine Finset.sum_le_sum fun τ _ => ?_
    have hm := (X₂.maj_pos hx τ (emb_ne_zero τ.1 hw0)).le
    calc _ ≤ (K * X₂.c τ) * X₂.maj x τ (Data.emb τ.1 w) := mul_le_mul_of_nonneg_right (hKτ τ) hm
      _ = _ := by ring
  rwa [div_le_iff₀ hK, mul_comm] at key

theorem cover_pull_holSub0 : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, rdU (T.U j σ) f ∈ holSub0 (T.U j σ).X (laU (T.U j σ) a n) → ∀ f₂ ∈ sec C.d.Xo₂ C.d.c₂ a n, C.IsPull f f₂ → rdU C.U₂ f₂ ∈ holSub0 C.U₂.X (laU C.U₂ a n) := by
  intro D T hL j hj σ hσ C hC a n hDom f hf hfh f₂ hf₂ hP
  refine Submodule.mem_inf.2 ⟨holCusp_mem_holSub _ _ (fun k₂ => ?_), rdU_mem_offZero _ _⟩
  have hU₂ : IsUnf C.U₂ := hC.2.2.2.1
  have hU₁ : IsUnf (T.U j σ) := hL.unf j hj σ hσ
  have hS := Formalism.L2.Pj.abelian₂.holSub_SS ReciprocityTheory.ChartRestriction.G.FD.siegelSpaceAlgebra_holds _ _ (Submodule.mem_inf.1 hfh).1
  obtain ⟨k, γ, hΛ, hh, -, u, hu1, hx⟩ := GlobalTheory.CoverConst.cover_scalar_const D T hL j hj σ hσ C hC n k₂
  obtain ⟨hΨ, hla⟩ := GlobalTheory.CoverConst.psi_and_weight_eq D T hL j hj σ hσ C hC k₂ k
  have hp : ((T.U j σ).X k).p0 = (C.U₂.X k₂).p0 := ((hU₁.2.1 k).1).trans ((hU₂.2.1 k₂).1).symm
  let G : Frame (C.U₂.X k₂).Ψ D.R.r → Frame ((T.U j σ).X k).Ψ D.R.r := fun x τ =>
    ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1 * mat x ⟨τ.1, (hΨ τ.1).2 τ.2⟩ :
      Matrix (Fin D.R.r) (Fin D.R.r) ℂ)
  have hGrel : ∀ x (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X k₂).Ψ) (h₁ : τ ∈ ((T.U j σ).X k).Ψ),
      mat (G x) ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat x ⟨τ, h₂⟩ :=
    fun _ _ _ _ => rfl
  have hG : ∀ x ∈ (C.U₂.X k₂).dom, G x ∈ ((T.U j σ).X k).dom ∧
      rdU C.U₂ f₂ k₂ x = u * rdU (T.U j σ) f k (G x) := fun x hxd =>
    ⟨(hx x (G x) hxd (hGrel x)).1, (hx x (G x) hxd (hGrel x)).2 a hDom f hf f₂ hf₂ hP⟩
  have hpn : ∀ x ∈ (C.U₂.X k₂).dom, (C.U₂.X k₂).pnorm (laU C.U₂ a n k₂) (rdU C.U₂ f₂ k₂) x =
      ((T.U j σ).X k).pnorm (laU (T.U j σ) a n k) (rdU (T.U j σ) f k) (G x) := fun x hxd =>
    pnorm_move _ _ hΨ hh _ _ (fun τ h₂ h₁ i => hla a n τ h₂ h₁ i) _ _ x (G x) (hGrel x) u hu1 (hG x hxd).2
  have hsec := hU₂.2.2.2.2.1 a n hDom f₂ hf₂ k₂
  obtain ⟨B, hB⟩ := (hS k).1.2
  have hbdd : (C.U₂.X k₂).IsBddSec (laU C.U₂ a n k₂) (rdU C.U₂ f₂ k₂) :=
    ⟨hsec, B, fun x hxd => (hpn x hxd).trans_le (hB _ (hG x hxd).1)⟩
  by_cases hr : 0 < D.R.r
  · obtain ⟨c₀, hc₀, hgt⟩ := ReciprocityTheory.ChartRestriction.G.FD.spectralGap_holds D.R.r _ _ _ (hS k)
    obtain ⟨C₁, hC₁⟩ := ReciprocityTheory.ChartRestriction.G.FD.cuspidalDecay_holds D.R.r _ _ _ c₀ hc₀.le hgt
    obtain ⟨K, hK, hle⟩ := exists_firstMinimumSq_bound_of_rationalIsometry _ _ hr hΨ γ hΛ hh hp
    refine GlobalTheory.CuspUnif.mem_SS_of_decay _ hr _ _ hbdd (C := |C₁|) (c := 2 * Real.pi * c₀ / K) (by positivity)
      fun x hxd => ?_
    have hGd := (hG x hxd).1
    have hl : 0 < ((T.U j σ).X k).firstMinimumSq (G x) := Real.sqrt_pos.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.la1_pos_of_mem_dom _ hr hGd)
    have hl₂ : 0 < (C.U₂.X k₂).firstMinimumSq x := Real.sqrt_pos.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.la1_pos_of_mem_dom _ hr hxd)
    have hle' := hle x hxd (G x) hGd (hGrel x)
    rw [hpn x hxd]
    refine (hC₁ (G x) hGd).trans ?_
    refine mul_le_mul (le_abs_self _) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le (abs_nonneg _)
    have hq : 2 * Real.pi * c₀ / K / (C.U₂.X k₂).firstMinimumSq x ≤ 2 * Real.pi * c₀ / ((T.U j σ).X k).firstMinimumSq (G x) := by
      rw [div_div, div_le_div_iff₀ (by positivity) hl]
      exact mul_le_mul_of_nonneg_left hle' (by positivity)
    have e1 : -2 * Real.pi * c₀ / ((T.U j σ).X k).firstMinimumSq (G x) =
        -(2 * Real.pi * c₀ / ((T.U j σ).X k).firstMinimumSq (G x)) := by ring
    rw [e1, neg_div]
    exact neg_le_neg hq
  · refine ⟨hbdd, fun ξ hξ x _ => ?_⟩
    exfalso
    apply hξ.2.2
    funext i
    exact absurd i.2 (by omega)

end GlobalTheory.CoverHol
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section




namespace GlobalTheory.RankOnto

theorem sumOnto_of_goodRange : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), (∀ j t, GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize.GoodRangeAt X.R.toRealDat j t) → ∀ i, BaseTup Y i → SumOnto Y.Z.rd i := by
  intro D X E Y hG i hB j b x hx
  obtain ⟨w, hw, hrd⟩ := GlobalTheory.T.good_form_reading_eq_good_model_vector_evaluation D X E Y i j b x hx
  have hν : Y.Z.ν i j b ≠ 0 := (Y.Z.scalar i j b).ne
  have hT := GlobalTheory.T.good_type_form_reading_right_translate_lift D X E Y i j b x hx
  have hφ : (X.R.HW j (Formalism.IndefR.Links.sg0 D X.A3.A)).e w (X.geo.v₀ j _) = Y.Z.ν i j b • Y.Z.rd i j b x := by
    rw [hrd, smul_smul, mul_inv_cancel₀ hν, one_smul]
  obtain ⟨F, hF, hsum⟩ := GlobalTheory.T.goodModelVector_eq_classSum_baseLevel D X E Y hG i hB j b w hw (fun u hu κ hκ g => by
    rw [hφ, Pi.smul_apply, Pi.smul_apply, hT u hu κ hκ g, smul_eq_mul, smul_eq_mul]; ring)
  refine ⟨(Y.Z.ν i j b)⁻¹ • F, Submodule.smul_mem _ _ hF, ?_⟩
  rw [map_smul, ← hsum, hrd]

end GlobalTheory.RankOnto
end
end
