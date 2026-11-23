module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfAeFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle072
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAdelicUnitaryTranslateStandardLattice
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle011
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle042
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle077
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualLatticesAtLevel
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.PeriodCoordinateThetaOfSignedHeisenbergVacuum
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle044
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

theorem _root_.GlobalTheory.T.periodCoordinateTheta_of_signedHeisenbergVacuum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ L : Lt E r, SelfD X L → ∀ v : TF n g, IsVac X bas w (tens (stdL E n) L) v → ∀ b : Fin g ⊕ Fin g → (Fin r → E), (∀ u, u ∈ L ↔ ∃ m : Fin g ⊕ Fin g → ℤ, u = ∑ j, m j • b j) → (∀ i j, EF X (b i) (b j) = -(omegaStd (Pi.single i 1) (Pi.single j 1) : ℤ)) → ∃ (c₁ c₂ : Fin g → ℂ) (C : ℂ), C ≠ 0 ∧ (∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) ∧ (∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) ∧ ∀ x ∈ X.dom, ∀ h τ : Matrix (Fin g) (Fin g) ℂ, h = (Matrix.of fun i k => pv X idx x (b (Sum.inl k)) i)⁻¹ → τ = h * (Matrix.of fun i k => pv X idx x (b (Sum.inr k)) i) → IsUnit h.det ∧ τ ∈ SW.Siegel (Fin g) ∧ (∀ z w' : Fin g → ℂ, hx X bas idx x z w' = (h *ᵥ z) ⬝ᵥ ((τ.map Complex.im)⁻¹.map fun t : ℝ => (t : ℂ)) *ᵥ star (h *ᵥ w')) ∧ (∀ i, eps1 X w (b (Sum.inl i)) = cexp (2 * Real.pi * I * c₁ i) ∧ eps1 X w (b (Sum.inr i)) = cexp (2 * Real.pi * I * c₂ i)) ∧ ∀ z : Fin n → Fin g → ℂ, thA X bas idx v x z = C * h.det ^ (n / 2) * ∏ k, (cexp (Real.pi / 2 * ((h *ᵥ z k) ⬝ᵥ ((τ.map Complex.im)⁻¹.map fun t : ℝ => (t : ℂ)) *ᵥ (h *ᵥ z k))) * thetaChar τ c₁ c₂ (h *ᵥ z k)) := by
  first | exact @GlobalTheory.Dict.VacForm.thA_vacuum | exact GlobalTheory.Dict.VacForm.thA_vacuum | (intros; apply GlobalTheory.Dict.VacForm.thA_vacuum <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaSpace

open GlobalTheory.WeilVacMove

variable {D : D7} {S T : HSp D}

theorem stdL_full (E : Type) [Field E] [NumberField E] (r : ℕ) :
    (stdL E r).FG ∧ Submodule.span E (stdL E r : Set (Fin r → E)) = ⊤ := by
  refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
  rw [eq_top_iff, ← (Pi.basisFun E (Fin r)).span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨a, rfl⟩
  exact Submodule.subset_span ⟨a, by simp⟩

theorem map_sub_eq_zero {A B : Type} [Ring A] [Ring B] (φ : A →+* B) {a b : A} (ha : φ a = 0) (hb : φ b = 0) :
    φ (a - b) = 0 := by rw [map_sub, ha, hb, sub_zero]

theorem map_nsmul_eq_zero {A B : Type} [Ring A] [Ring B] (φ : A →+* B) {a : A} (ha : φ a = 0) (N : ℕ) :
    φ (N • a) = 0 := by rw [map_nsmul, ha, smul_zero]

theorem isRealPt_sub {u v : WO S T} (hu : IsRealPt u) (hv : IsRealPt v) : IsRealPt (u - v) := by
  ext i j
  have h1 : finPart D (u i j) = 0 := congrFun (congrFun hu i) j
  have h2 : finPart D (v i j) = 0 := congrFun (congrFun hv i) j
  exact map_sub_eq_zero (finPart D) h1 h2

theorem isFinPt_nsmul {u : WO S T} (hu : IsFinPt u) (N : ℕ) : IsFinPt (N • u) := by
  ext i j
  have h1 : infPart D (u i j) = 0 := congrFun (congrFun hu i) j
  exact map_nsmul_eq_zero (infPart D) h1 N

theorem exists_fin_add_real (C : Ctx S T) (w : WO S T) : ∃ u v, IsFinPt u ∧ IsRealPt v ∧ w = u + v := by
  obtain ⟨R, -, -, -, h1, -, h2, -⟩ := GlobalTheory.T.realPoints_classicalModel_realVectorSpace D S T C
  exact ⟨_, _, h2 w, (h1 _).1, (sub_add_cancel _ _).symm⟩

theorem isTh_rho (C : Ctx S T) {f : WO S T → ℂ} (hf : C.IsTh f) (w : WO S T) : C.IsTh (C.rho w f) := by
  obtain ⟨u, v, hu, hv, rfl⟩ := exists_fin_add_real C w
  have hfin {a : WO S T} (ha : IsFinPt a) {g : WO S T → ℂ} (hg : C.IsTh g) : C.IsTh (C.rho a g) := {
    quasi := heisO_quasi C.ψ S T a g hg.quasi
    level := by
      obtain ⟨U, hU, h1⟩ := hg.level
      refine ⟨U ⊓ GlobalTheory.FinTranslate.annSub C.ψ S T a, hU.inter (GlobalTheory.FinTranslate.isOpen_annSub C.std.1 ha), fun u hu h0 => ?_⟩
      have h2 : C.ψ (symplOH S T u a) = 1 ∧ C.ψ (symplOH S T a u) = 1 := hu.2
      conv_rhs => rw [← h1 u hu.1 h0]
      unfold Ctx.rho
      rw [heisO_heisO, heisO_heisO, h2.1, h2.2, add_comm]
    cont := by
      haveI : IsTopologicalAddGroup (AE D) := IsTopologicalRing.to_topologicalAddGroup
      haveI : IsTopologicalAddGroup (WO S T) := Pi.topologicalAddGroup
      exact (C.std.1.1.comp (continuous_symplOH S T continuous_id continuous_const)).mul
        (hg.cont.comp (continuous_id.add continuous_const))
    smooth k L h1 h2 w := by
      have e : (fun t => heisO C.ψ S T a g (w + L t)) = fun t => C.ψ (symplOH S T w a) * g (w + a + L t) := by
        funext t
        rw [heisO, symplOH_add_left, (symplOH_fin_real S T a (L t) ha (h2 t)).2, add_zero, add_right_comm]
      rw [e]
      exact contDiff_const.mul (hg.smooth k L h1 h2 (w + a)) }
  have h := hfin hu (isTheta_heisO_real C.std hv hf)
  unfold Ctx.rho at h ⊢
  rwa [heisO_heisO, (symplOH_fin_real S T u v hu hv).1, AddChar.map_zero_eq_one, one_smul] at h

theorem exists_level (C : Ctx S T) {f : WO S T → ℂ} (hf : C.IsTh f) :
    ∃ N : ℕ, 0 < N ∧ ∀ u ∈ hatA S T (tens (stdL D.host.E S.rank) C.X.Λ), C.rho (N • u) f = f := by
  obtain ⟨-, -, h3, h4, -⟩ := GlobalTheory.T.completedTensorLattice_strongApprox_open_compact D S T C _ _ (stdL_full D.host.E S.rank) ⟨C.X.Λ_fg, C.X.Λ_span⟩
  obtain ⟨U, hU, h⟩ := hf.level
  obtain ⟨N, hN, hNU⟩ := h4 U hU
  exact ⟨N, hN, fun u hu => h _ (hNU u hu) (isFinPt_nsmul (h3 u hu).1 N)⟩

theorem eq_zero_of_real (C : Ctx S T) {f : WO S T → ℂ} (hf : C.IsTh f) (h0 : ∀ w, IsRealPt w → f w = 0) :
    f = 0 := by
  obtain ⟨h1, -, h3, -⟩ := GlobalTheory.T.completedTensorLattice_strongApprox_open_compact D S T C _ _ (stdL_full D.host.E S.rank) ⟨C.X.Λ_fg, C.X.Λ_span⟩
  have h7 := (GlobalTheory.T.symplecticCharacter_real_finite_points_match D S T C).2.2.2.2.2.2.2
  obtain ⟨N, hN, hl⟩ := exists_level C hf
  funext w
  obtain ⟨u, v, hu, hv, rfl⟩ := exists_fin_add_real C w
  obtain ⟨y, hy⟩ := h1 u hu
  obtain ⟨-, hy2⟩ := h3 _ hy
  obtain ⟨y', -, u', hu', e⟩ := hy2 N hN
  have hr := isRealPt_sub hv (h7 (y + y')).2.2.1
  have e1 : u + v = ratW T S (y + y')ᵀ + ((v - (ratW T S (y + y')ᵀ - finW S T (y + y'))) + N • u') := by
    rw [(h7 y).2.2.2 y', sub_eq_iff_eq_add.1 e]
    abel
  have e2 := congrFun (hl u' hu') (v - (ratW T S (y + y')ᵀ - finW S T (y + y')))
  rw [h0 _ hr] at e2
  unfold Ctx.rho heisO at e2
  rw [(symplOH_fin_real S T _ _ (isFinPt_nsmul (h3 u' hu').1 N) hr).2, AddChar.map_zero_eq_one, one_mul] at e2
  rw [e1, hf.quasi, e2, mul_zero, Pi.zero_apply]

theorem rho_finW (C : Ctx S T) {f : WO S T → ℂ} (hf : C.IsTh f) (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E)
    (w : WO S T) (hw : IsRealPt w) : C.rho (finW S T y) f w =
      cexp (π * I * (EFR C.X (C.realPt w) (embR C.X y) : ℝ)) * f (w - (ratW T S yᵀ - finW S T y)) := by
  obtain ⟨-, h2, -, -, -, -, -, h7⟩ := GlobalTheory.T.symplecticCharacter_real_finite_points_match D S T C
  obtain ⟨-, -, -, hadd, -, -, -, hfin, -⟩ := GlobalTheory.T.realPoints_classicalModel_realVectorSpace D S T C
  obtain ⟨a1, a2, a3, -⟩ := h7 y
  set z := ratW T S yᵀ - finW S T y with hz
  have hr : ratW T S yᵀ = finW S T y + z := by rw [hz]; abel
  have hp : C.realPt z = embR C.X y := by
    rw [← a1, hr, hadd, hfin _ a2, zero_add]
  have e1 : w + finW S T y = ratW T S yᵀ + (w - z) := by rw [hz]; abel
  have hzz : symplOH S T z z = 0 := by
    unfold symplOH
    rw [(GlobalTheory.T.symplecticCharacter_real_finite_points_match D S T C).2.2.2.2.1, mul_zero]
  have e2 : -symplOH S T (ratW T S yᵀ) (w - z) = symplOH S T w z := by
    have e3 : symplOH S T z w = symplOH S T z (w - z) + symplOH S T z z := by
      rw [← symplOH_add_right, sub_add_cancel]
    rw [hr, symplOH_add_left, (symplOH_fin_real S T _ _ a2 (isRealPt_sub hw a3)).1, zero_add, symplOH_skew S T z w,
      e3, hzz, add_zero]
  unfold Ctx.rho heisO
  rw [(symplOH_fin_real S T _ _ a2 hw).2, AddChar.map_zero_eq_one, one_mul, e1, hf.quasi, e2, h2 w z hw a3, hp]

theorem exists_mt_eq (V : HSp D) {γ : GA D V} (h : γ ∈ GQ V) :
    ∃ m : Matrix (Fin V.rank) (Fin V.rank) D.host.E, mt V γ = m.map (incA D) := by
  obtain ⟨γ', -, e⟩ := h
  exact ⟨γ'.1, (congrArg Units.val e).symm⟩

theorem isTh_actO (C : Ctx S T) {f : WO S T → ℂ} (hf : C.IsTh f) {γ : GA D S} (hγ : γ ∈ GQ S) {γ' : GA D T}
    (hγ' : γ' ∈ GQ T) : C.IsTh fun w => f (actO S T γ γ' w) := by
  have hs : ∀ w w', symplOH S T (actO S T γ γ' w) (actO S T γ γ' w') = symplOH S T w w' := fun w w' => by
    unfold symplOH
    rw [(GlobalTheory.T.symplecticCharacter_real_finite_points_match D S T C).2.2.2.2.2.2.1]
  obtain ⟨R, -, -, -, -, -, -, -, -, hact⟩ := GlobalTheory.T.realPoints_classicalModel_realVectorSpace D S T C
  let A : WO S T →+ WO S T := AddMonoidHom.mk' (actO S T γ γ') (actO_add γ γ')
  have hA : Continuous (actO S T γ γ') := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  refine ⟨fun x w => ?_, ?_, hf.cont.comp hA, fun k L h1 h2 w => ?_⟩
  · obtain ⟨m, hm⟩ := exists_mt_eq S ((GQ S).inv_mem hγ)
    obtain ⟨m', hm'⟩ := exists_mt_eq T hγ'
    have e : actO S T γ γ' (ratW T S x) = ratW T S (m' * x * m) := by
      unfold actO ratW
      rw [hm, hm', Matrix.map_mul, Matrix.map_mul]
    rw [actO_add, ← hs, e, hf.quasi]
  · obtain ⟨U, hU, h⟩ := hf.level
    refine ⟨U.comap A, hU.preimage hA, fun u hu h0 => ?_⟩
    funext w
    have e := congrFun (h _ hu ((hact γ γ' u).2.1 h0)) (actO S T γ γ' w)
    unfold heisO at e ⊢
    rw [← e, ← hs w u]
    exact congrArg (fun x => _ * f x) (actO_add γ γ' w u)
  · have := hf.smooth k (A.comp L) (hA.comp h1) (fun t => (hact γ γ' (L t)).1 (h2 t)) (actO S T γ γ' w)
    simp only [actO_add]
    exact this

theorem theta_space_laws : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), C.IsTh 0 ∧ (∀ f f', C.IsTh f → C.IsTh f' → C.IsTh (f + f') ∧ ((∀ w, IsRealPt w → f w = f' w) → f = f')) ∧ ∀ f, C.IsTh f → (∀ a : ℂ, C.IsTh (a • f)) ∧ (∀ w, C.IsTh (C.rho w f)) ∧ (∀ w w', C.rho w (C.rho w' f) = C.ψ (symplOH S T w w') • C.rho (w + w') f) ∧ (∀ (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) w, IsRealPt w → C.rho (finW S T y) f w = cexp (π * I * (EFR C.X (C.realPt w) (embR C.X y) : ℝ)) * f (w - (ratW T S yᵀ - finW S T y))) ∧ (∀ γ ∈ GQ S, ∀ γ' ∈ GQ T, C.IsTh fun w => f (actO S T γ γ' w)) ∧ ∃ N : ℕ, 0 < N ∧ ∀ u ∈ hatA S T (tens (stdL D.host.E S.rank) C.X.Λ), C.rho (N • u) f = f := by
  intro D S T C
  have hz : C.IsTh 0 := {
    quasi γ w := by simp only [Pi.zero_apply, mul_zero]
    level := ⟨⊤, isOpen_univ, fun u _ _ => by funext w; simp only [heisO, Pi.zero_apply, mul_zero]⟩
    cont := continuous_const
    smooth k L _ _ w := contDiff_const }
  have ha {f g : WO S T → ℂ} (hf : C.IsTh f) (hg : C.IsTh g) : C.IsTh (f + g) := {
    quasi γ w := by simp only [Pi.add_apply, hf.quasi, hg.quasi, mul_add]
    level := by
      obtain ⟨U, hU, h1⟩ := hf.level
      obtain ⟨U', hU', h2⟩ := hg.level
      refine ⟨U ⊓ U', hU.inter hU', fun u hu h0 => ?_⟩
      funext w
      have e1 := congrFun (h1 u hu.1 h0) w
      have e2 := congrFun (h2 u hu.2 h0) w
      unfold heisO at e1 e2 ⊢
      rw [Pi.add_apply, Pi.add_apply, mul_add, e1, e2]
    cont := hf.cont.add hg.cont
    smooth k L h1 h2 w := (hf.smooth k L h1 h2 w).add (hg.smooth k L h1 h2 w) }
  have hs (c : ℂ) {f : WO S T → ℂ} (hf : C.IsTh f) : C.IsTh (c • f) := {
    quasi γ w := by rw [Pi.smul_apply, Pi.smul_apply, hf.quasi, smul_eq_mul, smul_eq_mul, mul_left_comm]
    level := by
      obtain ⟨U, hU, h1⟩ := hf.level
      refine ⟨U, hU, fun u hu h0 => ?_⟩
      funext w
      have e1 := congrFun (h1 u hu h0) w
      unfold heisO at e1 ⊢
      rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm, e1]
    cont := hf.cont.const_smul c
    smooth k L h1 h2 w := contDiff_const.mul (hf.smooth k L h1 h2 w) }
  refine ⟨hz, fun f f' hf hf' => ⟨ha hf hf', fun h => ?_⟩, fun f hf =>
    ⟨fun a => hs a hf, isTh_rho C hf, fun w w' => heisO_heisO _ _ _ _ _ _, rho_finW C hf,
      fun γ hγ γ' hγ' => isTh_actO C hf hγ hγ', exists_level C hf⟩⟩
  exact sub_eq_zero.1 (eq_zero_of_real C (isTheta_sub hf hf') fun w hw => sub_eq_zero.2 (h w hw))

end GlobalTheory.ThetaSpace

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KerOntoStd

open GlobalTheory.AdelTranslate GlobalTheory.AdLat GlobalTheory.UnRep

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem glue_map (c : E ≃ₐ[F] E) (e : FiniteAdeleRing (𝓞 F) F) (γ : Matrix (Fin n) (Fin n) E) :
    (glue e γ).map (sg (FiniteAdeleRing (𝓞 F) F) c) = glue e (γ.map c) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [glue, fm, sg]
  · simp [glue, fm, sg, Matrix.one_apply_ne h]

theorem mul_glue_sub_one {e α : FiniteAdeleRing (𝓞 F) F} (h : α * e = 0) (γ : Matrix (Fin n) (Fin n) E) (i j : Fin n) :
    (α ⊗ₜ[F] (1 : E) : RA F E) * (glue e γ - 1) i j = 0 := by
  have h0 : (α ⊗ₜ[F] (1 : E) : RA F E) * (e ⊗ₜ[F] (1 : E)) = 0 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, h, TensorProduct.zero_tmul]
  simp only [glue, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  linear_combination (fm F γ i j - (1 : Matrix (Fin n) (Fin n) (RA F E)) i j) * h0

theorem mul_idem_eq_zero {k M : ℕ} (hk : k.Coprime M) {v : HeightOneSpectrum (𝓞 F)} (hv : (M : 𝓞 F) ∈ v.asIdeal)
    {α : FiniteAdeleRing (𝓞 F) F} (hα : ∀ v', v' ≠ v → α v' = 0) : α * idem F k = 0 := by
  refine DFunLike.ext _ _ fun w => ?_
  change α w * idem F k w = 0
  by_cases h : w = v
  · subst h
    rw [idem_apply, if_neg, mul_zero]
    intro hk'
    obtain ⟨a, b, hab⟩ : IsCoprime (k : 𝓞 F) (M : 𝓞 F) := Nat.Coprime.cast hk
    exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (hab ▸ add_mem (w.asIdeal.mul_mem_left a hk') (w.asIdeal.mul_mem_left b hv)))
  · rw [hα w h, zero_mul]

end General

theorem finPart_cA (D : D7) (x : AE D) :
    finPart D (cA D x) = sg (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (GlobalTheory.Member.cF D) (finPart D x) :=
  GlobalTheory.UnitarySplit.map_sig (sndA D.host.F) D.sp.cm.sig x



theorem exists_trivAt_isMov : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ M : ℕ, 0 < M → ∀ Λ ∈ Vset D.host.E S.rank M, ∃ h ∈ GfC S, TrivAt S (Ideal.span {(M : 𝓞 D.host.F)}) h ∧ IsMov (fmtC S h) (stdL D.host.E S.rank) Λ := by
  rintro D S T C M - Λ ⟨-, hU', k, hk0, hkM, h1, h2⟩
  have hU : (⟨Λ⟩ : GenLat D.host.E S.rank).Unimod := (GlobalTheory.Dict.GenLatCmp.unimod_iff Λ).2 hU'
  have h₁ : ∀ x ∈ Λ, k • x ∈ stdL D.host.E S.rank := fun x hx => by
    rw [← Nat.cast_smul_eq_nsmul D.host.E]; exact h1 x hx
  have h₂ : ∀ x ∈ stdL D.host.E S.rank, k • x ∈ Λ := fun x hx => by
    rw [← Nat.cast_smul_eq_nsmul D.host.E]; exact h2 x hx
  obtain ⟨k', γ, hk', hγ, h₃, h₄⟩ := GlobalTheory.AdaptUnitary.exists_unitary_adapted D.host.E (hostOfRecord D) S.rank ⟨Λ⟩ k hU hk0
    (by rw [GlobalTheory.Dict.GenLatCmp.std_eq, span_smul_le_iff]; exact h₂) k hk0
  rw [GlobalTheory.Dict.GenLatCmp.std_eq] at h₃ h₄
  set c := GlobalTheory.Member.cF D with hc
  have c2 : ∀ x, c (c x) = x := fun x => star_star x
  set δ : Matrix (Fin S.rank) (Fin S.rank) D.host.E := (γ.map c)ᵀ with hδ
  have hδγ : δ * γ = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply, ← hγ i j]
    rfl
  have hγδ : γ * δ = 1 := mul_eq_one_comm.1 hδγ
  have hδc : γᵀ.map c = δ := rfl
  have h₅ : ∀ x ∈ stdL D.host.E S.rank, k' • δ *ᵥ x ∈ Λ := fun x hx => by
    obtain ⟨w, hw, e⟩ := h₄ x hx
    rwa [← Nat.cast_smul_eq_nsmul D.host.E, ← Matrix.mulVec_smul, e, Matrix.mulVec_mulVec, hδγ, Matrix.one_mulVec]
  have h₆ : ∀ x ∈ Λ, k' • γ *ᵥ x ∈ stdL D.host.E S.rank := fun x hx => by
    rw [← Nat.cast_smul_eq_nsmul D.host.E]
    exact h₃ x hx
  have he := idem_mul (F := D.host.F) k
  have t1 : γᵀ * δᵀ = 1 := by rw [← Matrix.transpose_mul, hδγ, Matrix.transpose_one]
  have t2 : δᵀ * γᵀ = 1 := by rw [← Matrix.transpose_mul, hγδ, Matrix.transpose_one]
  obtain ⟨-, -, -, lift, -⟩ := GlobalTheory.UnitarySplit.real_finite_split D S
  obtain ⟨h, hh, eh⟩ := lift ⟨glue (idem _ k) γᵀ, glue (idem _ k) δᵀ, glue_mul he t1, glue_mul he t2⟩ (by
    rw [C.m.gS, Matrix.transpose_one]
    refine isUnA_of c ?_
    change ((glue (idem _ k) γᵀ).map _)ᵀ * glue (idem _ k) γᵀ = 1
    rw [glue_map_sg, hδc]
    exact glue_mul he t2)
  have e1 : fmt S h = glue (idem _ k) γᵀ := congrArg Units.val eh
  have e2 : fmtC S h = glue (idem _ k) δ := by
    rw [← hδc, ← glue_map, ← e1]
    ext i j
    exact finPart_cA D _
  refine ⟨h, hh, ?_, ?_⟩
  · rintro v hv ε ⟨α, rfl, -, hα⟩ i j
    have hM : (M : 𝓞 D.host.F) ∈ v.asIdeal := hv (Ideal.mem_span_singleton_self _)
    apply GlobalTheory.UnitarySplit.parts_inj D
    · rw [map_mul, map_zero]
      have : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0 := by
        change ((0 : Ainf D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
        exact TensorProduct.zero_tmul _ _
      rw [this, zero_mul]
    · rw [map_mul, map_zero]
      have : finPart D ((mt S h - 1) i j) = (fmt S h - 1) i j := by
        rw [Matrix.sub_apply, Matrix.sub_apply, (finPart D).map_sub]
        congr 1
        by_cases hij : i = j
        · subst hij
          rw [Matrix.one_apply_eq, Matrix.one_apply_eq, (finPart D).map_one]
        · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, (finPart D).map_zero]
      rw [this, e1]
      exact mul_glue_sub_one (mul_idem_eq_zero hkM hM hα) _ i j
  · rw [e2]
    intro u
    constructor
    · intro hu
      refine ⟨_, glue_mem_hat (F := D.host.F) hk' h₆ h₁ u hu, ?_⟩
      rw [Matrix.mulVec_mulVec, glue_mul he hδγ, Matrix.one_mulVec]
    · rintro ⟨z, hz, ez⟩
      rw [ez]
      exact glue_mem_hat (F := D.host.F) hk' h₅ h₂ z hz

end GlobalTheory.KerOntoStd
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.self_dual_lattices_at_level : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), (∀ (M : ℕ) (h : GA D S) (Λ : Lt D.host.E S.rank), 0 < M → TrivAt S (Ideal.span {(M : 𝓞 D.host.F)}) h → Λ.FG → IsMov (fmtC S h) (stdL D.host.E S.rank) Λ → Λ ∈ Vset D.host.E S.rank M) ∧ ∀ (Lv : SW.Level C.X) (g : GA D T) (L : Lt D.host.E T.rank), L.FG → IsMov (fmt T g) C.X.Λ L → SelfD C.X L ∧ (TrivAt T (C.under Lv) g → L ∈ Lv.lats) ∧ C.under Lv ≠ ⊥ ∧ (L ∈ Lv.lats → ∃ g' ∈ GfC T, TrivAt T (C.under Lv) g' ∧ IsMov (fmt T g') C.X.Λ L) := by
  first | exact @GlobalTheory.Ker.MovLev.mov_mem_lattices | exact GlobalTheory.Ker.MovLev.mov_mem_lattices | (intros; apply GlobalTheory.Ker.MovLev.mov_mem_lattices <;> assumption)
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

theorem _root_.GlobalTheory.T.exists_analyticFrame_of_analyticFibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → ∃ Φ : AnVal.AnPt y g (fun j => rowType X (idx j)) e, (∀ z, Φ.e z = A.ex z) ∧ Φ.fr = A.fr ∧ (∀ z, z ∈ Φ.lat ↔ ∃ v ∈ L, z = pv X idx x v) ∧ (∀ z w, hermForm Φ.Hm z w = hx X bas idx x z w) ∧ (∀ v ∈ L, Φ.χ (pv X idx x v) = A.χ v) ∧ (∀ (k : ℤ) F θ, Φ.toAnFr.Rd k F θ ↔ A.Reads k F θ) ∧ ∀ (k : ℕ) a θ, AnVal.fock Φ.Hm (k : ℤ) a θ = Dict.fock X bas idx x k a θ := by
  first | exact @GlobalTheory.Dict.AnFib.exists_anPt | exact GlobalTheory.Dict.AnFib.exists_anPt | (intros; apply GlobalTheory.Dict.AnFib.exists_anPt <;> assumption)
end
