module

public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle005
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.FirstCoordinateAdmissible
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle045
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle165
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle044
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardCompLePeriodSpaces
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle172
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle052
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DoubledHermitianTestFunctionZeroAndNorm
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle055
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorTestThetaZeroEqThetaSeries
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle028
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle058
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle032
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle007
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle044
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinearStatement
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle042
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle036
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle072
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle035
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle096
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle028
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TypeFnPeriodExistModuliNonempty
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.ThetaValues.PolyDerivSmulLetter
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle002

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

namespace GlobalTheory.PushKeeps

theorem push_keeps : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (c : Coeff l), ∀ (n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (h : Matrix (Fin n) (Fin n) E), IsUnitaryM h → (∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), pushLet c h P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) ∧ ∀ Λ : GenLat E n, (Λ.Unimod → (actLat h Λ).Unimod) ∧ Moves h Λ.La (actLat h Λ).La ∧ ccT h * h = 1 ∧ ∀ P ∈ harmL (Dw := Dw) c Λ a, pushLet c h P ∈ harmL (Dw := Dw) c (actLat h Λ) a := by
  intro E _ _ _ H Dw l c n a h hu
  refine ⟨fun P hP => ?_, fun Λ => ⟨GlobalTheory.RepCompare.unimod_act hu, fun v => ?_, hu,
    fun P hP => GlobalTheory.RepCompare.push_mem c hu hP⟩⟩
  · obtain ⟨h1, h2, h3⟩ := hP
    exact ⟨GlobalTheory.PushHarm.push_mem_harmK E H Dw l c n h P hu h1,
      (GlobalTheory.Proof.ColumnMapShift.push_rows E H Dw l c n h P fun τ i => a (τ, i)).1 h2,
      (GlobalTheory.Proof.ColumnMapShift.push_rows E H Dw l c n h P fun τ i => a (τ, i)).2 h3⟩
  · have h' : adjM h * h = 1 := hu
    rw [GlobalTheory.RepCompare.mem_actLat]
    constructor
    · exact fun hv => ⟨v, hv, rfl⟩
    · rintro ⟨u, hu', e⟩
      have e' := congrArg (adjM h).mulVec e
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h', Matrix.one_mulVec, Matrix.one_mulVec] at e'
      exact e' ▸ hu'

end GlobalTheory.PushKeeps
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

theorem index_eq_of_marked_isometry {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {σ' : KA l →+* ℂ} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ' ty) (hr : 1 ≤ Dw.p + Dw.q) (hσ : σ' (baseKA l).ρ = H.rt0)
    (hty : IsTypeFn H Dw.p Dw.q ty) (k k' : Fin F.n) (gam : (F.Di k).La ≃ₗ[𝓞 E] (F.Di k').La)
    (hEF : ∀ a b, (F.Di k').EF (gam a) (gam b) = (F.Di k).EF a b)
    (hM : ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), ∃ x, gam (F.t k a) = F.t k' a + l.M • x)
    (hA : ∀ a, ∃ x, gam (F.t k a) = F.t k' a + l.A • x) : k = k' := by
  obtain ⟨-, P', hP'⟩ := GlobalTheory.PeriodExists.period_of_isTypeFn H (F.Di k') g ty
    (by rw [(F.sig k').1, (F.sig k').2]; exact hty)
  have hP := GlobalTheory.ClassUniq.isPeriod_comp_isometry gam hEF hP'
  set P := P'.comp gam.toLinearMap.toAddMonoidHom with hPdef
  refine F.disj k k' P P' hP hP' ?_
  exact (GlobalTheory.UnifPoint.point_eq_iff_isometry_closed GlobalTheory.thetaUnifAV_all GlobalTheory.firstFiveLaws.1 E H Dw l Xo σ' g ty
    hr hσ hty (F.Di k) (F.Di k')
    (F.t k) (F.t k') P P' (F.u k P) (F.u k' P') (F.ex k P) (F.ex k' P')
    ⟨F.over_σ k P hP, hP, ⟨F.ex_add k P hP, F.ex_onto k P hP, GlobalTheory.ClassUniq.isHolTo_ex F k P hP,
      (F.ex_diff k P hP).1, (F.ex_diff k P hP).2⟩, F.ex_ker k P hP, F.ex_lin k P hP, F.ex_weil k P hP,
      F.ex_eta k P hP, F.ex_etaA k P hP⟩
    ⟨F.over_σ k' P' hP', hP', ⟨F.ex_add k' P' hP', F.ex_onto k' P' hP', GlobalTheory.ClassUniq.isHolTo_ex F k' P' hP',
      (F.ex_diff k' P' hP').1, (F.ex_diff k' P' hP').2⟩, F.ex_ker k' P' hP', F.ex_lin k' P' hP',
      F.ex_weil k' P' hP', F.ex_eta k' P' hP', F.ex_etaA k' P' hP'⟩).2
    ⟨gam, LinearEquiv.refl ℂ _, hEF, hM, hA, fun a => rfl⟩

theorem UW.ik_injective {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}
    {U : _root_.Formalism.L2.PjFree.Unf Xo c σ r} (hσ : _root_.Formalism.L2.PjFree.GoodEmb c σ) (hU : _root_.Formalism.L2.PjFree.IsUnf U) (h1 : 1 ≤ r) (W : UW U) :
    Function.Injective W.ik := by
  obtain ⟨hr, hX, -, hfib, -⟩ := hU
  obtain ⟨g, e, F, ik, φ, hEF, hP⟩ := W
  intro k k' hk
  change ik k = ik k' at hk
  obtain ⟨x, hx⟩ := CompInj.dom_nonempty (U.X k)
  obtain ⟨x₀, hx₀⟩ := CompInj.dom_nonempty (U.X k')
  obtain ⟨P, -, hper, hpt, hder, -⟩ := hP k ⟨x, hx⟩
  obtain ⟨P₀, hP₀, hper₀, -⟩ := hP k' ⟨x₀, hx₀⟩
  have hP' := fun y => (hP k' y).imp fun _ h => (⟨h.1, h.2.2.1, h.2.2.2.1⟩ : _ ∧ _ ∧ _)
  have hEF' := hEF k'
  generalize φ k' = ψ at hP₀ hP' hEF'
  clear hP hEF φ
  generalize ik k' = n at *
  subst hk
  obtain ⟨x', hx', hPx⟩ := CompInj.exists_frame hσ h1 hr e (U.X k') (hX k').1 (hX k').2 _ (F.sig _).1 (F.sig _).2
    ψ hEF' x₀ hx₀ P₀ hP₀ hper₀ P hper
  obtain ⟨P', hP', hpt', hder'⟩ := hP' ⟨x', hx'⟩
  obtain rfl : P = P' := by
    ext a j
    rw [hPx, hP']
  have hbor := CompInj.frBor_of_eq (U.un k ⟨x, hx⟩) (U.un k' ⟨x', hx'⟩) (hpt'.trans hpt.symm) fun τ i =>
    ((GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F _ P hper).2.1 _).unique (hder' τ i) (hder τ i)
  obtain ⟨ga, -, b, -, h⟩ := (hfib k k' _ _).1 hbor
  exact (congrArg Sigma.fst h).symm

theorem comp_eq_of_matched : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : _root_.Formalism.L2.PjFree.Unf Xo c σ r), _root_.Formalism.L2.PjFree.GoodEmb c σ → _root_.Formalism.L2.PjFree.IsUnf U → 1 ≤ r → l.A = 1 → ∀ (W : UW U) (k k' : U.Comp), SameSp (U.X k) (U.X k') → ∀ ga : GL (Fin r) E, IsUn (U.X k) ga → mapL ga (U.X k).Λ = (U.X k').Λ → (∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), ∃ u ∈ (U.X k').Λ, (ga : Matrix (Fin r) (Fin r) E) *ᵥ W.mark k a = W.mark k' a + l.M • u) → k = k' := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU h1 hA W k k' hS ga hun hΛ hm
  apply W.ik_injective hσ hU h1
  have hinj : Function.Injective
      ((Matrix.toLin' (ga : Matrix (Fin r) (Fin r) E)).restrictScalars (𝓞 E)) := by
    intro u v huv
    have h : (ga : Matrix (Fin r) (Fin r) E) *ᵥ u = (ga : Matrix (Fin r) (Fin r) E) *ᵥ v := huv
    have h2 := congrArg (fun w => ((ga⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ w) h
    simpa only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] using h2
  let ψ : (U.X k).Λ ≃ₗ[𝓞 E] (U.X k').Λ :=
    (Submodule.equivMapOfInjective _ hinj (U.X k).Λ).trans (LinearEquiv.ofEq _ _ hΛ)
  let gam : (W.F.Di (W.ik k)).La ≃ₗ[𝓞 E] (W.F.Di (W.ik k')).La := (W.φ k).trans (ψ.trans (W.φ k').symm)
  have hgam : ∀ a, (W.φ k' (gam a) : Fin r → E) = (ga : Matrix (Fin r) (Fin r) E) *ᵥ (W.φ k a : Fin r → E) := by
    intro a
    change (W.φ k' ((W.φ k').symm (ψ (W.φ k a))) : Fin r → E) = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  refine index_eq_of_marked_isometry W.F (hU.1 ▸ h1) hσ
    ((GlobalTheory.Relab.relab_good E H l c σ hσ).2.2.2 Dw W.g W.e) _ _ gam (fun a b => ?_) (fun a ha => ?_) fun a => ?_
  · have h := W.isom k' (gam a) (gam b)
    rw [hgam, hgam, ← hS.gm, ← hS.xi, hun, ← W.isom k a b] at h
    exact_mod_cast h
  · obtain ⟨w, hw, h⟩ := hm a ha
    refine ⟨(W.φ k').symm ⟨w, hw⟩, (W.φ k').injective (Subtype.ext ?_)⟩
    rw [hgam, map_add (f := _), map_nsmul, LinearEquiv.apply_symm_apply]
    exact h
  · exact ⟨gam (W.F.t _ a) - W.F.t _ a, by rw [hA, one_smul, add_sub_cancel]⟩

end GlobalTheory.Dict
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.RealScalar

variable {D : D7} {S T : HSp D}

theorem mul_tmul_eq_zero {F A B E : Type} [Field F] [CommRing A] [CommRing B] [CommRing E] [Algebra F A]
    [Algebra F B] [Algebra F E] {a : (A × B) ⊗[F] E}
    (ha : Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) a = 0) (y : E) :
    a * (((0, 1) : A × B) ⊗ₜ[F] y) = 0 := by
  have key : ∀ a : (A × B) ⊗[F] E, a * (((0, 1) : A × B) ⊗ₜ[F] y) =
      TensorProduct.map (LinearMap.inr F A B) LinearMap.id
        (Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) a * ((1 : B) ⊗ₜ[F] y)) := by
    intro a
    induction a using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [add_mul, ha, hb, map_add (f := _), add_mul, map_add (f := _)]
    | tmul x e =>
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.map_tmul]
      congr 1
      exact Prod.ext (mul_zero _) rfl
  rw [key, ha, zero_mul, map_zero]

theorem mul_mul_eq_self {R R' : Type} [CommRing R] [CommRing R'] (p : R →+* R') {m n : ℕ}
    {a : Matrix (Fin m) (Fin m) R} {b : Matrix (Fin n) (Fin n) R} {x : Matrix (Fin m) (Fin n) R}
    (ha : a.map p = 1) (hb : b.map p = 1) (hx : ∀ c, p c = 0 → ∀ i j, c * x i j = 0) : a * x * b = x := by
  have k : ∀ {l : ℕ} {c : Matrix (Fin l) (Fin l) R}, c.map p = 1 → ∀ i j, p ((c - 1) i j) = 0 := by
    intro l c hc i j
    have h2 : p (c i j) = (1 : Matrix (Fin l) (Fin l) R') i j := congrFun (congrFun hc i) j
    rw [Matrix.sub_apply, map_sub, h2, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have e1 : (a - 1) * x = 0 := by
    ext i j
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun l _ => hx _ (k ha i l) _ _
  have e2 : x * (b - 1) = 0 := by
    ext i j
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun l _ => by
      rw [mul_comm]
      exact hx _ (k hb l j) _ _
  rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at e1
  rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at e2
  rw [e1, e2]

theorem map_finPart_mt {V : HSp D} {g : GA D V} (hg : g ∈ GinfC V) : (mt V g).map (finPart D) = 1 := by
  have h1 : finHom V g = 1 := hg
  exact congrArg Units.val h1

theorem actO_finW {h : GA D S} (hh : h ∈ GinfC S) {g : GA D T} (hg : g ∈ GinfC T)
    (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) : actO S T h g (finW S T y) = finW S T y :=
  mul_mul_eq_self (finPart D) (map_finPart_mt hg) (map_finPart_mt (inv_mem hh)) fun _ hc i j =>
    mul_tmul_eq_zero (F := D.host.F) (A := Ainf D.host.F) (B := Af D.host.F) hc (y j i)

theorem rho_zero (C : Ctx S T) (f : WO S T → ℂ) : C.rho 0 f = f := by
  funext w
  simp [heisO, symplOH, symplO, hO]

theorem zOf_zero (C : Ctx S T) (x : Frame C.X.Ψ T.rank) : C.zOf x 0 = 0 := by
  have h0 : C.realPt 0 = 0 := by
    funext σ k a
    simp [Ctx.realPt, compAt]
  funext k i
  simp [Ctx.zOf, h0, zR, hermC]

theorem gaussR_zero (C : Ctx S T) (x : Frame C.X.Ψ T.rank) :
    gaussR C.X C.bas C.idx x (0 : Fin S.rank → Fin C.g → ℂ) = 1 := by
  simp [gaussR, hx]

theorem exists_ipO_Th (C : Ctx S T) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (hμ : IsCovolOne (ratL T S) μ 𝓕) : ∃ a : ℂ, a ≠ 0 ∧ ∀ B, C.IsB B → ∀ φ : TF S.rank C.g, SW.IsSB φ →
      ipO μ 𝓕 (C.Th (C.xB B) φ) (C.Th (C.xB B) φ) = a * SW.ip φ φ := by
  obtain ⟨a, ha, b, hab⟩ := GlobalTheory.SW.dbl_zero_and_norm D.host.E T.rank C.X C.g C.bas C.idx S.rank
    C.sympl C.even
  obtain ⟨⟨κ, hκ, hk⟩, -⟩ := GlobalTheory.Ker.kZero_onFr_const_entire D.host.E T.rank C.X C.g C.q0 C.hr C.bas C.idx
    S.rank C.sympl C.even
  refine ⟨a * κ, mul_ne_zero ha (by exact_mod_cast hκ.ne'), fun B hB φ hφ => ?_⟩
  obtain ⟨hon, hdom, -⟩ := (GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2 B hB
  have h0 : IsRealPt (0 : WO S T) := by
    ext i j
    simp
  have := GlobalTheory.T.innerProduct_translated_vacua_eq_gaussianKernel D S T C μ 𝓕 hμ _ hdom _ hdom φ φ hφ hφ 0 0 h0 h0
  have e : (fun (k : Fin S.rank) (i : Fin C.g) => conj ((0 : Fin S.rank → Fin C.g → ℂ) k i)) = 0 := by
    funext k i
    simp
  rw [rho_zero, zOf_zero, gaussR_zero, e, (hk _ hon).2, (hab.2 φ φ hφ hφ).1] at this
  rw [this]
  simp only [map_one]
  ring

theorem om_real_Th : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeak C.ψ S T om → ∀ h ∈ GinfC S, ∀ g ∈ GinfC T, ∀ B, C.IsB B → ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ φ : TF S.rank C.g, SW.IsSB φ → om (h, g) (C.Th (C.xB B) φ) = c • (C.Th (C.xB (C.mvB g B)) φ) := by
  intro D S T C om hom h hh g hg B hB
  obtain ⟨-, hdom, -, -, -, hmv⟩ := (GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2 B hB
  have hB' : C.IsB (C.mvB g B) := (hmv g).1
  obtain ⟨-, hdom', -⟩ := (GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2 _ hB'
  have hth : ∀ x ∈ C.X.dom, ∀ φ : TF S.rank C.g, SW.IsSB φ → C.IsTh (C.Th x φ) :=
    fun x hx φ hφ => (GlobalTheory.T.adelicZakTheta_exists_unique D S T C x hx φ hφ).1.1
  have hex : ∀ φ : TF S.rank C.g, ∃ φ' : TF S.rank C.g, SW.IsSB φ →
      SW.IsSB φ' ∧ om (h, g) (C.Th (C.xB B) φ) = C.Th (C.xB (C.mvB g B)) φ' := by
    intro φ
    by_cases hφ : SW.IsSB φ
    · obtain ⟨φ', h'⟩ := GlobalTheory.T.exists_testFunction_of_fockVacuum_thetaFunction D S T C _ hB' _ (hom.om_pres (h, g) _ (hth _ hdom φ hφ))
        (((GlobalTheory.T.weakWeilRep_carries_derivatives_vacua_fockVectors D S T C om hom h g _ (hth _ hdom φ hφ)).2 B hB).1
          ((GlobalTheory.T.fockPolynomialVector_testTheta_zero_eq_thetaSeries D S T C).2 B hB φ hφ).1)
      exact ⟨φ', fun _ => h'⟩
    · exact ⟨φ, fun h' => absurd h' hφ⟩
  choose A hA using hex
  have L := GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D S T C
  have hadd : ∀ φ ψ : TF S.rank C.g, SW.IsSB φ → SW.IsSB ψ → SW.IsSB (φ + ψ) :=
    fun φ ψ h h' => (isSB_algebra_haar_linear _ _ _ _ _ h h').1
  have hsm : ∀ (a : ℂ) (φ : TF S.rank C.g), SW.IsSB φ → SW.IsSB (a • φ) :=
    fun a φ h => (isSB_algebra_haar_linear _ _ _ _ _ h h).2.1 _
  have hhe : ∀ (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) (φ : TF S.rank C.g), SW.IsSB φ →
      SW.IsSB (heisG C.X C.bas y φ) := fun y φ h =>
    ((GlobalTheory.SW.heisG_laws D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even).2.2.2 y φ h).1
  obtain ⟨c, hc⟩ := GlobalTheory.Ker.schur_heisG D.host.E T.rank C.X C.g C.q0 C.hr C.bas C.idx S.rank C.sympl C.even A
    (fun φ hφ => (hA φ hφ).1)
    (fun φ ψ hφ hψ => by
      have h1 := hA _ (hadd _ _ hφ hψ)
      refine ((L _ hdom' _ h1.1).1 _ (hadd _ _ (hA φ hφ).1 (hA ψ hψ).1)).2 ?_
      rw [← h1.2, ((L _ hdom _ hφ).1 _ hψ).1, map_add (f := _), (hA φ hφ).2, (hA ψ hψ).2,
        ((L _ hdom' _ (hA φ hφ).1).1 _ (hA ψ hψ).1).1])
    (fun a φ hφ => by
      have h1 := hA _ (hsm a _ hφ)
      refine ((L _ hdom' _ h1.1).1 _ (hsm a _ (hA φ hφ).1)).2 ?_
      rw [← h1.2, (L _ hdom _ hφ).2.1, map_smul, (hA φ hφ).2, (L _ hdom' _ (hA φ hφ).1).2.1])
    (fun y φ hφ => by
      have h1 := hA _ (hhe y _ hφ)
      refine ((L _ hdom' _ h1.1).1 _ (hhe y _ (hA φ hφ).1)).2 ?_
      have e1 := (L _ hdom _ hφ).2.2.1 (-y)
      have e2 := (L _ hdom' _ (hA φ hφ).1).2.2.1 (-y)
      rw [neg_neg] at e1 e2
      rw [← h1.2, ← e1, ← e2, ← (hA φ hφ).2, hom.om_heis h g _ _ (hth _ hdom φ hφ), actO_finW hh hg])
  have hc' : ∀ φ : TF S.rank C.g, SW.IsSB φ →
      om (h, g) (C.Th (C.xB B) φ) = c • (C.Th (C.xB (C.mvB g B)) φ) := fun φ hφ => by
    rw [(hA φ hφ).2, hc φ hφ, (L _ hdom' _ hφ).2.1]
  by_cases hne : ∃ φ : TF S.rank C.g, SW.IsSB φ ∧ φ ≠ 0
  · obtain ⟨φ, hφ, h0⟩ := hne
    refine ⟨c, ?_, hc'⟩
    obtain ⟨⟨μ, 𝓕, hμ⟩, hip⟩ := GlobalTheory.T.thetaFunction_fundamentalDomain_innerProduct_basic D S T C
    obtain ⟨a, ha, hn⟩ := exists_ipO_Th C hμ
    have t1 := hth _ hdom φ hφ
    have t2 := hth _ hdom' φ hφ
    have t3 : C.IsTh (c • (C.Th (C.xB (C.mvB g B)) φ)) := hc' φ hφ ▸ hom.om_pres (h, g) _ t1
    have u := ((hip μ 𝓕 hμ _ t1).2.2.2 _ t1).2.2.2.2.2 om hom (h, g)
    rw [hc' φ hφ, ((hip μ 𝓕 hμ _ t2).2.2.2 _ t3).2.2.1, ((hip μ 𝓕 hμ _ t3).2.2.2 _ t2).2.1,
      ((hip μ 𝓕 hμ _ t2).2.2.2 _ t2).2.2.1, map_mul, ← ((hip μ 𝓕 hμ _ t2).2.2.2 _ t2).2.1,
      hn _ hB φ hφ, hn _ hB' φ hφ, ← mul_assoc, Complex.mul_conj'] at u
    have hz := mul_ne_zero ha (GlobalTheory.SW.DblZero.ip_self_ne_zero hφ h0)
    have u' : ((‖c‖ : ℂ)) ^ 2 = 1 := mul_right_cancel₀ hz (by rw [u, one_mul])
    have u'' : ‖c‖ ^ 2 = 1 := by exact_mod_cast u'
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg c) two_ne_zero).1 u''
  · refine ⟨1, norm_one, fun φ hφ => ?_⟩
    have h0 : φ = (0 : ℂ) • φ := by
      by_contra h0
      exact hne ⟨φ, hφ, fun e => h0 (by rw [e, smul_zero])⟩
    rw [h0, (L _ hdom _ hφ).2.1, (L _ hdom' _ hφ).2.1]
    simp

end GlobalTheory.Ker.RealScalar
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KerVacIp

variable {D : D7} {S T : HSp D} (C : Ctx S T)

theorem isONFr_xB (B : C.Bas) (hB : C.IsB B) : IsONFr C.X (C.xB B) := by
  unfold IsONFr
  intro τ
  have h1 : ∀ x y : T.V, star (T.hT x y) = T.hT y x := by
    intro x y
    exact T.herm.eq x y
  have h2 : ∀ x : D.host.E, tauE D (C.m.e.symm τ) (star x) = (starRingEnd ℂ) (tauE D (C.m.e.symm τ) x) := by
    intro x
    unfold tauE
    dsimp only [star, Formalism.BasicNotions.Host.cmStar]
    exact IsCMField.complexEmbedding_complexConj D.host.E (D.host.emb ↑(D.eTau (C.m.e.symm τ))) x
  have key : ∀ i j, (τ : D.host.E →+* ℂ) (C.X.Gm i j) = tauE D (C.m.e.symm τ) (HSpace.gram T i j) := by
    intro i j
    have he := C.m.e_emb (C.m.e.symm τ)
    rw [Equiv.apply_symm_apply] at he
    rw [he, C.m.gT, Matrix.transpose_apply, NumberField.ComplexEmbedding.conjugate_coe_eq, ← h2]
    unfold HSpace.gram
    rw [h1]
  rw [← hB (C.m.e.symm τ)]
  ext a b
  unfold FD.gram mat Ctx.xB hermC FD.col gramAt
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply,
    Complex.star_def, Complex.conj_conj, Finset.sum_mul, key]
  rw [Finset.sum_comm]

theorem rho_zero_pt (f : WO S T → ℂ) : C.rho 0 f = f := by
  unfold Ctx.rho heisO
  funext w
  simp [symplOH, symplO, hO]

theorem zOf_zero (x : Frame C.X.Ψ T.rank) : C.zOf x 0 = 0 := by
  unfold Ctx.zOf Ctx.realPt zR
  funext k i
  simp [compAt, hermC]
  intro _
  simp only [← Pi.zero_def, Matrix.mulVec_zero, Pi.zero_apply]

theorem ip_vacua : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)),
    IsCovolOne (ratL T S) μ 𝓕 → ∃ a : ℂ, a ≠ 0 ∧ ∀ B, C.IsB B → ∀ φ φ' : TF S.rank C.g, SW.IsSB φ → SW.IsSB φ' →
      ipO μ 𝓕 (C.Th (C.xB B) φ) (C.Th (C.xB B) φ') = a * ip φ φ' := by
  intro D S T C μ 𝓕 hμ
  have h0 : IsRealPt (0 : WO S T) := by
    unfold IsRealPt
    simp
  have hg : ∀ x : Frame C.X.Ψ T.rank, gaussR C.X C.bas C.idx x (0 : Fin S.rank → Fin C.g → ℂ) = 1 := by
    intro x
    unfold gaussR
    simp [hx]
  obtain ⟨a, ha, b, -, hdbl⟩ :=
    GlobalTheory.SW.dbl_zero_and_norm D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even
  obtain ⟨⟨κ, hκ, hk⟩, -⟩ :=
    GlobalTheory.Ker.kZero_onFr_const_entire D.host.E T.rank C.X C.g C.q0 C.hr C.bas C.idx S.rank C.sympl C.even
  refine ⟨a * κ, mul_ne_zero ha (Complex.ofReal_ne_zero.mpr hκ.ne'), ?_⟩
  intro B hB φ φ' hφ hφ'
  obtain ⟨hdom, hk0⟩ := hk _ (isONFr_xB C B hB)
  have h := GlobalTheory.T.innerProduct_translated_vacua_eq_gaussianKernel D S T C μ 𝓕 hμ _ hdom _ hdom φ φ' hφ hφ' 0 0 h0 h0
  rw [rho_zero_pt, rho_zero_pt, zOf_zero, hg] at h
  have hz : (fun k i => (starRingEnd ℂ) ((0 : Fin S.rank → Fin C.g → ℂ) k i)) = 0 := by
    funext k i
    simp
  rw [hz, hk0, (hdbl φ φ' hφ hφ').1] at h
  rw [h]
  simp only [map_one, one_mul]
  ring

end GlobalTheory.KerVacIp
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.levelDatumVector_eq_theta_of_testFunction : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) (M : ℕ), IdemTwo Lv.w → 0 < M → (M : 𝓞 D.host.E) ∈ Lv.𝔪 → ∀ B, C.IsB B → (∀ f', C.IsBase Lv B f' → ∀ v, IsVac C.X C.bas Lv.w (tens (stdL D.host.E S.rank) (Lv.sh C.X.Λ)) v → ∃ t : ℂ, t ≠ 0 ∧ f' = t • (C.Th (C.xB B) v)) ∧ ∀ v₀ : Lt D.host.E T.rank → TF S.rank C.g, (∀ L ∈ Lv.lats, IsVac C.X C.bas Lv.w (tens (stdL D.host.E S.rank) (Lv.sh L)) (v₀ L)) → C.IsBase Lv B (C.Th (C.xB B) (v₀ C.X.Λ)) ∧ ∀ t : ℂ, C.uVec Lv hn (t • (C.Th (C.xB B) (v₀ C.X.Λ))) = t • (C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank))) := by
  first | exact @GlobalTheory.Ker.LevVec.uVec_eq | exact GlobalTheory.Ker.LevVec.uVec_eq | (intros; apply GlobalTheory.Ker.LevVec.uVec_eq <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.FramedBaseChange

theorem bcEx_all : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ σ : c.F →+* ℂ, BCEx Xo c σ :=
  fun E _ _ _ H Dw l Xo c σ p y ψ =>
    exists_frMap GlobalTheory.firstFiveLaws.1 E H Dw l Xo c p.R (CAt σ) ψ y

end GlobalTheory.FramedBaseChange
end
