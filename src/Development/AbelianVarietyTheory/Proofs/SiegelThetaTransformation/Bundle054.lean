module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLetterRowWeightDictionary
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle052
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle050
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle049
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle028
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle032
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle007
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RationalUnitaryGroupStructure
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle042
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle044
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle038
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinearStatement
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
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.SW hiding Level

theorem GlobalTheory.Ker.exists_symplectic_basis_of_selfD : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (r : ℕ) (X : Data E r), SelfD X X.Λ →
    ∃ (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (_ : Fin g ≃ X.Ψ × Fin r), IsSympl X bas := by
  intro E _ _ _ r X hL

  obtain ⟨bas, hbas⟩ := GlobalTheory.Dict.Letters.exists_isSympl X hL (Fintype.equivFin (X.Ψ × Fin r)).symm
  exact ⟨_, bas, (Fintype.equivFin _).symm, hbas⟩
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.ZakLaws

theorem embR_neg {E : Type} [Field E] [NumberField E] [IsCMField E] {r n : ℕ} (X : Data E r)
    (y : Matrix (Fin n) (Fin r) E) : embR X (-y) = -embR X y := by
  funext τ k a
  simp only [embR, Matrix.neg_apply, map_neg, Pi.neg_apply]

theorem EFR_neg_right {E : Type} [Field E] [NumberField E] [IsCMField E] {r n : ℕ} (X : Data E r)
    (v v' : WR X n) : EFR X v (-v') = -EFR X v v' := by
  unfold EFR hermC
  simp only [Pi.neg_apply, map_neg, mul_neg, Finset.sum_neg_distrib, Complex.neg_re]

variable {D : D7} {S T : HSp D}

theorem inf_incA (C : Ctx S T) (τ : D.what₂.Tau) (e : D.host.E) :
    C.θ τ (infPart D (incA D e)) = tauE D τ e := by
  have h := (C.inf τ).1 e
  simp only [infPart, Formalism.L2.Theta.incA] at h ⊢
  exact h

theorem realPt_actO (C : Ctx S T) {ga : GL (Fin T.rank) D.host.E} {γ : GA D T} (h : IsRatOf T ga γ)
    (w : WO S T) :
    C.realPt (actO S T 1 γ w) =
      fun σ k => ((ga : Matrix (Fin T.rank) (Fin T.rank) D.host.E).map σ.1) *ᵥ C.realPt w σ k := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hact⟩ := GlobalTheory.T.realPoints_classicalModel_realVectorSpace D S T C
  funext σ k a
  have he : ∀ z, (σ.1 : D.host.E →+* ℂ) z = conj (tauE D (C.m.e.symm σ) z) := by
    intro z
    have hz := C.m.e_emb (C.m.e.symm σ)
    rw [Equiv.apply_symm_apply] at hz
    rw [hz, ComplexEmbedding.conjugate_coe_eq]
  have hm : Formalism.L2.Theta.mt S 1⁻¹ = 1 := by
    simp [Formalism.L2.Theta.mt]
  have hg : Formalism.L2.Theta.mt T γ = (ga : Matrix (Fin T.rank) (Fin T.rank) D.host.E).map (incA D) := h
  have h1 : compAt C.θ (C.m.e.symm σ) (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) = 1 := by
    ext i j
    simp [compAt, Matrix.one_apply, apply_ite]
  simp only [Ctx.realPt]
  rw [(hact 1 γ w).2.2 (C.m.e.symm σ), hm, hg, h1, Matrix.mul_one]

  simp only [compAt, Matrix.map_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct, map_sum, map_mul,
  inf_incA C, he, Ctx.realPt]

end GlobalTheory.Ker.ZakLaws

namespace GlobalTheory.Ker

theorem Ctx.th_laws : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ x ∈ C.X.dom, ∀ φ : TF S.rank C.g, SW.IsSB φ → (∀ φ', SW.IsSB φ' → C.Th x (φ + φ') = C.Th x φ + C.Th x φ' ∧ (C.Th x φ = C.Th x φ' → φ = φ')) ∧ (∀ a : ℂ, C.Th x (a • φ) = a • C.Th x φ) ∧ (∀ y : Matrix (Fin S.rank) (Fin T.rank) D.host.E, C.rho (finW S T y) (C.Th x φ) = C.Th x (heisG C.X C.bas (-y) φ)) ∧ ∀ (ga : GL (Fin T.rank) D.host.E) (γ : GA D T), IsRatOf T ga γ → ∀ w, C.Th (lact ga x) (wG C.X C.bas C.idx ga φ) w = C.Th x φ (actO S T 1 γ⁻¹ w) := by
  intro D S T C x hx φ hφ
  obtain ⟨R, -, -, hadd, hR, -, -, hfin0, -, hact⟩ := GlobalTheory.T.realPoints_classicalModel_realVectorSpace D S T C
  have hth := GlobalTheory.T.thetaFunction_space_heisenberg_laws D S T C
  have hzak := GlobalTheory.T.adelicZakTheta_exists_unique D S T C
  have hlaws := thR_laws D.host.E T.rank C.X C.g C.q0 C.hr C.bas C.idx S.rank C.sympl C.even
  have hZ : C.IsZak x φ (C.Th x φ) := (hzak x hx φ hφ).1
  have huniq : ∀ ψ, SW.IsSB ψ → ∀ f, C.IsZak x ψ f → f = C.Th x ψ := fun ψ hψ => (hzak x hx ψ hψ).2
  have hsub : ∀ w u, C.realPt (w - u) = C.realPt w - C.realPt u := by
    intro w u
    have hwu := hadd (w - u) u
    rw [sub_add_cancel] at hwu
    rw [hwu, add_sub_cancel_right]
  refine ⟨fun φ' hφ' => ⟨?_, ?_⟩, fun a => ?_, fun y => ?_, fun ga γ hγ w => ?_⟩
  · have hsb := (GlobalTheory.SW.isSB_algebra_haar_linear _ _ _ φ φ' hφ hφ').1
    have hZ' := (hzak x hx φ' hφ').1
    refine (huniq _ hsb _ ⟨(hth.2.1 _ _ hZ.1 hZ'.1).1, fun w hw => ?_⟩).symm
    rw [Pi.add_apply, hZ.2 w hw, hZ'.2 w hw, ((hlaws x hx φ hφ).2.2.2.1 φ' hφ').2, Pi.add_apply]
  · intro heq
    have hZ' := (hzak x hx φ' hφ').1
    apply ((hlaws x hx φ hφ).2.2.2.1 φ' hφ').1
    funext v
    obtain ⟨hR1, hR2⟩ := hR v
    have e1 := hZ.2 (R v) hR1
    have e2 := hZ'.2 (R v) hR1
    rw [hR2] at e1 e2
    rw [← e1, ← e2, heq]
  · have hsb := (GlobalTheory.SW.isSB_algebra_haar_linear _ _ _ φ φ hφ hφ).2.1 a
    refine (huniq _ hsb _ ⟨(hth.2.2 _ hZ.1).1 a, fun w hw => ?_⟩).symm
    rw [Pi.smul_apply, hZ.2 w hw, (hlaws x hx φ hφ).2.2.2.2 a, Pi.smul_apply]
  · have hsb := ((heisG_laws D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even).2.2.2 (-y) φ hφ).1
    refine huniq _ hsb _ ⟨(hth.2.2 _ hZ.1).2.1 _, fun w hw => ?_⟩
    obtain ⟨hrat, hfinW, hreal, -⟩ := (GlobalTheory.T.symplecticCharacter_real_finite_points_match D S T C).2.2.2.2.2.2.2 y
    have hw' : IsRealPt (w - (ratW T S yᵀ - finW S T y)) := by
      unfold IsRealPt at hw hreal ⊢
      rw [Matrix.map_sub _ (map_sub (finPart D)), hw, hreal, sub_zero]
    rw [(hth.2.2 _ hZ.1).2.2.2.1 y w hw, hZ.2 _ hw', hsub, hsub, hrat, hfin0 _ hfinW, sub_zero,
      (hlaws x hx φ hφ).2.1 (-y), ZakLaws.embR_neg, ZakLaws.EFR_neg_right]
    simp only [Complex.ofReal_neg, mul_neg, neg_neg, sub_eq_add_neg]
  · have hq := (GlobalTheory.T.rational_unitary_group_structure D S T C).2.1
    have hinv : IsRatOf T ga⁻¹ γ⁻¹ := (hq γ γ ga ga hγ hγ).2.1
    have hun : IsUn C.X ga := (hq γ γ ga ga hγ hγ).2.2.2.1
    have hGQ : γ⁻¹ ∈ GQ T := (hq _ _ _ _ hinv hinv).2.2.1
    have hx' : lact ga x ∈ C.X.dom := IsUn.lact_mem hun hx
    have hsbw := (wG_laws D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even ga hun φ hφ).1
    have hZw : C.IsZak (lact ga x) (wG C.X C.bas C.idx ga φ) (fun w => C.Th x φ (actO S T 1 γ⁻¹ w)) := by
      refine ⟨(hth.2.2 _ hZ.1).2.2.2.2.1 1 (one_mem _) γ⁻¹ hGQ, fun w hw => ?_⟩
      dsimp only
      have hwr : IsRealPt (actO S T 1 γ⁻¹ w) := (hact 1 γ⁻¹ w).1 hw
      rw [hZ.2 _ hwr, ZakLaws.realPt_actO C hinv w,
        ← (hlaws x hx φ hφ).2.2.1 ga hun]
      congr 1
      funext τ k
      rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
    exact (congrFun ((hzak (lact ga x) hx' _ hsbw).2 _ hZw) w).symm

end GlobalTheory.Ker
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.FockOnto

theorem differentiable_of_fderiv_I {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {Φ : V → ℂ}
    (h : Differentiable ℝ Φ) (hI : ∀ z u, fderiv ℝ Φ z (I • u) = I * fderiv ℝ Φ z u) : Differentiable ℂ Φ := by
  intro z
  have hs : ∀ (c : ℂ) (u : V), fderiv ℝ Φ z (c • u) = c * fderiv ℝ Φ z u := by
    intro c u
    have e : c • u = c.re • u + c.im • (I • u) := by
      rw [← Complex.coe_smul, ← Complex.coe_smul, smul_smul, ← add_smul, Complex.re_add_im]
    rw [e, map_add (f := _), map_smul, map_smul, hI, Complex.real_smul, Complex.real_smul, ← mul_assoc, ← add_mul,
      Complex.re_add_im]
  let A : V →L[ℂ] ℂ :=
    { toFun := fderiv ℝ Φ z
      map_add' := map_add _
      map_smul' := hs
      cont := (fderiv ℝ Φ z).continuous }
  exact (hasFDerivAt_of_restrictScalars ℝ (f' := A) (h z).hasFDerivAt (by ext; rfl)).differentiableAt

variable {D : D7} {S T : HSp D}

theorem differentiable_comp {ψ : AddChar (AF D.host.F) ℂ} {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (R : V →+ WO S T)
    (hR : Continuous R) (hr : ∀ v, IsRealPt (R v)) : Differentiable ℝ fun v => f (R v) := by
  let e : V ≃L[ℝ] (Fin (Module.finrank ℝ V) → ℝ) := (Module.finBasis ℝ V).equivFun.toContinuousLinearEquiv
  have h1 := hf.smooth _ (R.comp e.symm.toLinearEquiv.toAddEquiv.toAddMonoidHom) (hR.comp e.symm.continuous)
    (fun t => hr _) 0
  have h2 := (h1.differentiable (by simp)).comp e.differentiable
  refine (funext fun v => ?_ : (fun v => f (R v)) = _) ▸ h2
  change f (R v) = f (0 + R (e.symm (e v)))
  rw [zero_add, e.symm_apply_apply]

theorem finW_neg_nsmul (N : ℕ) (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    finW S T (-(N • y)) = N • finW S T (-y) := by
  have key : ∀ {F A E : Type} [Field F] [CommRing A] [CommRing E] [Algebra F A] [Algebra F E] (p : A) (x : E),
      p ⊗ₜ[F] (-(N • x)) = N • (p ⊗ₜ[F] (-x)) := by
    intro F A E _ _ _ _ _ p x
    rw [← smul_neg]
    exact map_nsmul (TensorProduct.mk F A E p) N (-x)
  funext a k
  exact key (pairA D.host.F 0 1) (y k a)

theorem finW_mem_hatA {A : AddSubgroup (Matrix (Fin S.rank) (Fin T.rank) D.host.E)}
    {y : Matrix (Fin S.rank) (Fin T.rank) D.host.E} (hy : y ∈ A) : finW S T y ∈ hatA S T A :=
  AddSubgroup.subset_closure ⟨1, fun v => by rw [map_one]; exact one_mem _, y, hy, rfl⟩

theorem isRealPt_sub (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    IsRealPt (S := S) (T := T) (ratW T S yᵀ - finW S T y) := by
  ext a k
  change finPart D (incA D (y k a) - (pairA D.host.F 0 1) ⊗ₜ[D.host.F] y k a) = 0
  rw [RingHom.map_sub]
  exact sub_eq_zero.2 rfl

theorem realPt_sub (C : Ctx S T) (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    C.realPt (ratW T S yᵀ - finW S T y) = embR C.X y := by
  funext σ k a
  change conj (C.θ (C.m.e.symm σ) (infPart D (incA D (y k a) - (pairA D.host.F 0 1) ⊗ₜ[D.host.F] y k a))) =
    σ.1 (y k a)
  have h0 : infPart D ((pairA D.host.F 0 1) ⊗ₜ[D.host.F] y k a) = 0 := by
    have : infPart D (pairA D.host.F 0 1 ⊗ₜ[D.host.F] y k a) = (0 : Ainf D.host.F) ⊗ₜ[D.host.F] y k a := rfl
    rw [this, TensorProduct.zero_tmul]
  have h1 : infPart D (incA D (y k a)) = (1 : Ainf D.host.F) ⊗ₜ[D.host.F] y k a := rfl
  have h2 := C.m.e_emb (C.m.e.symm σ)
  rw [Equiv.apply_symm_apply] at h2
  rw [RingHom.map_sub, h0, h1, sub_zero, (C.inf _).1, h2, ComplexEmbedding.conjugate_coe_eq]

end GlobalTheory.Ker.FockOnto


open GlobalTheory.Ker.FockOnto in
theorem GlobalTheory.Ker.exists_test_of_fock : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ B, C.IsB B → ∀ f, C.IsTh f → C.IsFock B f → ∃ φ : TF S.rank C.g, SW.IsSB φ ∧ f = C.Th (C.xB B) φ := by
  intro D S T C B hB f hf hF
  obtain ⟨R, hRc, -, hadd, hR, hR', -⟩ := GlobalTheory.T.realPoints_classicalModel_realVectorSpace D S T C
  have hx : C.xB B ∈ C.X.dom := ((GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2 B hB).2.1
  obtain ⟨⟨L, hL⟩, -⟩ := GlobalTheory.Ker.zR_laws D.host.E T.rank C.X C.g C.q0 C.hr C.bas C.idx S.rank C.sympl C.even _ hx
  have hg0 : ∀ z : Fin S.rank → Fin C.g → ℂ, gaussR C.X C.bas C.idx (C.xB B) z ≠ 0 := fun z => Complex.exp_ne_zero _
  set Φ : (Fin S.rank → Fin C.g → ℂ) → ℂ := fun z => (gaussR C.X C.bas C.idx (C.xB B) z)⁻¹ * f (R (L.symm z))
    with hΦ
  have hd : Differentiable ℝ Φ :=
    (((RealHeis.contDiff_gaussR C.X C.bas C.idx (C.xB B)).differentiable (by simp)).inv hg0).mul
      ((differentiable_comp hf R hRc fun v => (hR v).1).comp L.symm.differentiable)
  have hv : ∀ v, f (R v) = gaussR C.X C.bas C.idx (C.xB B) (zR C.X C.idx (C.xB B) v) *
      Φ (zR C.X C.idx (C.xB B) v) := by
    intro v
    simp only [hΦ]
    rw [mul_inv_cancel_left₀ (hg0 _), ← hL, L.symm_apply_apply]
  have hw : ∀ w, IsRealPt w → f w = gaussR C.X C.bas C.idx (C.xB B) (C.zOf (C.xB B) w) * Φ (C.zOf (C.xB B) w) := by
    intro w hw
    rw [Ctx.zOf, ← hv, hR' w hw]
  have hone : ∀ ζ (σ : C.X.Ψ) (c : Fin S.rank → Fin T.rank → ℂ),
      fderiv ℝ Φ ζ (I • L (Pi.single σ c)) = I * fderiv ℝ Φ ζ (L (Pi.single σ c)) := by
    intro ζ σ c
    have h1 := (GlobalTheory.T.annihilation_creation_periodCoordinates D S T C B hB f Φ hd hw (C.m.e.symm σ) (Matrix.of fun a k => conj (c k a))
      (L (Pi.single σ c)) (by simp [hL]) (R (L.symm ζ)) (hR _).1).1
    have h2 : C.zOf (C.xB B) (R (L.symm ζ)) = ζ := by rw [Ctx.zOf, (hR _).2, ← hL, L.apply_symm_apply]
    rw [hF, h2, Pi.zero_apply] at h1
    have h3 := (mul_eq_zero.1 h1.symm).resolve_left (hg0 _)
    linear_combination (-I) * h3 + (fderiv ℝ Φ ζ (I • L (Pi.single σ c))) * Complex.I_mul_I
  have hC : Differentiable ℂ Φ := by
    refine differentiable_of_fderiv_I hd fun ζ u => ?_
    obtain ⟨v, rfl⟩ := L.surjective u

    rw [← Finset.univ_sum_single v, map_sum, Finset.smul_sum, map_sum, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun σ _ => hone ζ σ _
  obtain ⟨-, hext, hth⟩ := GlobalTheory.T.thetaFunction_space_heisenberg_laws D S T C
  obtain ⟨-, -, -, hfin, -, N, hN, hlev⟩ := hth f hf
  obtain ⟨φ, hφ, hθ⟩ := GlobalTheory.T.exists_theta_eq_of_translation_invariant_multiple D.host.E T.rank C.X C.g C.q0 C.hr C.bas C.idx S.rank C.sympl C.even _ hx N hN
    Φ hC (by
      intro y hy v
      have h1 := hfin (-(N • y)) (R v) (hR v).1
      have h2 : embR C.X (-(N • y)) = -(N • embR C.X y) := by
        funext σ k a
        simp [embR]
      have h3 : ratW T S (-(N • y))ᵀ - finW S T (-(N • y)) = R (-(N • embR C.X y)) := by
        rw [← hR' _ (isRealPt_sub _), realPt_sub, h2]
      have h4 : EFR C.X v (-(N • embR C.X y)) = -EFR C.X v (N • embR C.X y) := by
        generalize N • embR C.X y = a
        simp only [EFR, hermC, Pi.neg_apply, map_neg, mul_neg, Finset.sum_neg_distrib, Complex.neg_re, neg_mul,
          neg_neg]
      rw [h3, finW_neg_nsmul, hlev _ (finW_mem_hatA (neg_mem ((TensLat.mem_tens_stdL _ _).2 hy))), (hR v).2, h2,
        ← map_sub, sub_neg_eq_add, h4, hv, hv] at h1
      rw [h1]
      simp)
  refine ⟨φ, hφ, (GlobalTheory.T.adelicZakTheta_exists_unique D S T C _ hx φ hφ).2 f ⟨hf, fun w hw' => ?_⟩⟩
  rw [hw w hw', thR, hθ, Ctx.zOf]
end
