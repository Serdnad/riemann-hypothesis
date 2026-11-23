module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle067
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle069
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle258
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle259
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1981
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle042
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle048
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle219
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

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory Matrix
open scoped TensorProduct Topology InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.derivative_skew_adjoint_cusp_forms : ∀ (D : D7) (θ : GlobalTheory.Mem.Th.InfF D) (hθ : IsInfFam θ) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hX : X ∈ lieAt V τ) (ψ χ : GlobalTheory.CompanionTheory.HCCusp.Mc θ V), ⟪GlobalTheory.CompanionTheory.HCCusp.io μ hθ (GlobalTheory.CompanionTheory.HCCusp.der hθ τ hX ψ), GlobalTheory.CompanionTheory.HCCusp.io μ hθ χ⟫_ℂ = -⟪GlobalTheory.CompanionTheory.HCCusp.io μ hθ ψ, GlobalTheory.CompanionTheory.HCCusp.io μ hθ (GlobalTheory.CompanionTheory.HCCusp.der hθ τ hX χ)⟫_ℂ := by
  exact @GlobalTheory.CompanionTheory.HCCusp.inner_io_der_skew
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Transl

theorem foldr_lineDer_mul_right {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (b : GAd σ J) (l : List (ℝ → GAd σ J))
    (f : GAd σ J → ℂ) :
    l.foldr lineDer (fun x => f (x * b)) =
      fun x => (l.map fun γ t => b⁻¹ * γ t * b).foldr lineDer f (x * b) := by
  induction l with
  | nil => rfl
  | cons γ l ih =>
    rw [List.foldr_cons, ih, List.map_cons, List.foldr_cons]
    funext x
    simp only [lineDer]
    congr 1
    funext t
    congr 1
    simp only [mul_assoc, mul_inv_cancel_left]

variable {D : D7}

theorem isSmModOn_mul_right (V : HSp D) {Γ : Set (GA D V)} {φ : GA D V → ℂ}
    (h : IsSmModOn D.sp.cm.sig V.gram Γ φ) (b : GA D V) :
    IsSmModOn D.sp.cm.sig V.gram Γ (fun x => φ (x * b)) := by
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hN : (GfC V).Normal := MonoidHom.normal_ker _
  refine ⟨fun γ hγ x => ?_, ?_, h.cont.comp (continuous_id.mul continuous_const), ?_, ?_⟩
  · show φ (γ * x * b) = φ (x * b)
    rw [mul_assoc]
    exact h.left γ hγ _
  · obtain ⟨A, hA, eA⟩ := h.level
    refine ⟨A.comap (MulAut.conj b⁻¹).toMonoidHom, ?_, fun k hk hk' x => ?_⟩
    · have hc : Continuous fun y : GA D V => b⁻¹ * y * b⁻¹⁻¹ :=
        (continuous_const.mul continuous_id).mul continuous_const
      exact hA.preimage hc
    · have hk2 : b⁻¹ * k * b⁻¹⁻¹ ∈ A := hk
      have hk3 : b⁻¹ * k * b⁻¹⁻¹ ∈ GfC V := hN.conj_mem k hk' b⁻¹
      rw [inv_inv] at hk2 hk3
      show φ (x * k * b) = φ (x * b)
      rw [← eA _ hk2 hk3 (x * b)]
      congr 1
      simp only [mul_assoc, mul_inv_cancel_left]
  · exact GlobalTheory.UAut.isSm_mul_right_of_isCMExt _ _ (GlobalTheory.AdelicU.isCMExt_host D) φ b h.smooth
  · obtain ⟨N, hN'⟩ := h.growth
    refine ⟨N, fun l hl => ?_⟩
    obtain ⟨C, hC⟩ := hN' (l.map fun γ t => b⁻¹ * γ t * b) (by
      intro γ' hγ'
      obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hγ'
      exact GlobalTheory.UAut.RightTranslate.isRealLine_conj (GlobalTheory.AdelicU.isCMExt_host D) (hl γ hγ) b)
    refine ⟨max C 0 * (height D.sp.cm.sig V.gram b : ℝ) ^ N, fun x => ?_⟩
    rw [foldr_lineDer_mul_right]
    have h1 : (height D.sp.cm.sig V.gram (x * b) : ℝ) ≤
        (height D.sp.cm.sig V.gram x : ℝ) * (height D.sp.cm.sig V.gram b : ℝ) := by
      exact_mod_cast height_mul_le _ _ x b
    have h0 : (0 : ℝ) ≤ (height D.sp.cm.sig V.gram (x * b) : ℝ) := by positivity
    calc ‖(l.map fun γ t => b⁻¹ * γ t * b).foldr lineDer φ (x * b)‖
        ≤ C * (height D.sp.cm.sig V.gram (x * b) : ℝ) ^ N := hC _
      _ ≤ max C 0 * (height D.sp.cm.sig V.gram (x * b) : ℝ) ^ N :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max C 0 * ((height D.sp.cm.sig V.gram x : ℝ) * (height D.sp.cm.sig V.gram b : ℝ)) ^ N :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h1 N) (le_max_right _ _)
      _ = max C 0 * (height D.sp.cm.sig V.gram b : ℝ) ^ N * (height D.sp.cm.sig V.gram x : ℝ) ^ N := by
          rw [mul_pow]; ring

variable {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}

theorem infMat_inv_mul (hθ : IsInfFam θ) (V : HSp D) (b : GA D V) (τ : D.what₂.Tau) :
    infMat D.sp.cm.sig V.gram (θ τ) b⁻¹ * infMat D.sp.cm.sig V.gram (θ τ) b = 1 ∧
      infMat D.sp.cm.sig V.gram (θ τ) b * infMat D.sp.cm.sig V.gram (θ τ) b⁻¹ = 1 := by
  have rp := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V
  have hm := rp.2.2.2.1
  have h1 : infMat D.sp.cm.sig V.gram (θ τ) 1 = 1 := rp.2.2.2.2.1 1 (one_mem _) τ
  exact ⟨by rw [← hm, inv_mul_cancel, h1], by rw [← hm, mul_inv_cancel, h1]⟩

theorem isFrame_mul_inv (hθ : IsInfFam θ) (V : HSp D) (b : GA D V) (τ : D.what₂.Tau) {e : Fin V.rank → Bool}
    {P : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm e * P = gramAt D V τ) :
    IsUnit (P * (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹) ∧
      (P * (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹)ᴴ * Formalism.REAL.Jm e * (P * (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹) =
        gramAt D V τ := by
  obtain ⟨e1, e2⟩ := infMat_inv_mul hθ V b τ
  rw [Matrix.inv_eq_left_inv e1]
  have hB : IsUnit (infMat D.sp.cm.sig V.gram (θ τ) b⁻¹) := ⟨⟨_, _, e1, e2⟩, rfl⟩
  refine ⟨hP.mul hB, ?_⟩
  have hu : (infMat D.sp.cm.sig V.gram (θ τ) b⁻¹)ᴴ * gramAt D V τ * infMat D.sp.cm.sig V.gram (θ τ) b⁻¹ =
      gramAt D V τ := GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V b⁻¹ τ
  rw [← hu, ← h, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem inv_mul_kAt_mul (hθ : IsInfFam θ) (V : HSp D) (b : GA D V) (τ : D.what₂.Tau) {e : Fin V.rank → Bool}
    {P : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm e * P = gramAt D V τ)
    (k : Formalism.REAL.KG e) :
    b⁻¹ * kAt θ V τ e (P * (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹) k * b = kAt θ V τ e P k := by
  obtain ⟨hP', h'⟩ := isFrame_mul_inv hθ V b τ hP h
  have hx := isAtTau_kAt θ V hθ τ hP' h' k
  have rp := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V
  have hm := rp.2.2.2.1
  have hN : (GinfC V).Normal := MonoidHom.normal_ker _
  refine Model.isAtTau_unique θ V hθ ⟨?_, ?_, fun τ' c => ?_⟩ (isAtTau_kAt θ V hθ τ hP h k)
  · have := hN.conj_mem _ hx.1 b⁻¹
    rwa [inv_inv] at this
  · obtain ⟨e1, e2⟩ := infMat_inv_mul hθ V b τ
    rw [hm, hm, hx.2.1, Matrix.inv_eq_left_inv e1, Matrix.mul_inv_rev, Matrix.inv_eq_left_inv e2]
    simp only [Matrix.mul_assoc]
    rw [e1, Matrix.mul_one, ← Matrix.mul_assoc (infMat D.sp.cm.sig V.gram (θ τ) b⁻¹), e1, Matrix.one_mul]
  · obtain ⟨e1, -⟩ := infMat_inv_mul hθ V b τ'
    rw [hm, hm, hx.2.2 _ c, Matrix.mul_one, e1]

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Transl

namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Transl

theorem cuspOn_mul_right : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (U : Subgroup (GA D V)) (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsFrameFam V ε fr → ∀ (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)) (c : D.what₂.Tau → ℕ → ℂ) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E) (T : Finset (Fin m)) (φ : GA D V → ℂ), φ ∈ cuspOn θ V X Y T U ε fr ρ c → ∀ b : GA D V, (fun x => φ (x * b)) ∈ cuspOn θ V X Y T (U.map (MulAut.conj b).toMonoidHom) ε (fun τ => fr τ * (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹) ρ c := by
  intro D θ hθ V U ε fr hfr W _ _ ρ c m X Y T φ hφ b
  obtain ⟨⟨f1, f2, f3, f4⟩, f5⟩ := hφ
  have hN : (GfC V).Normal := MonoidHom.normal_ker _
  refine ⟨⟨isSmModOn_mul_right V f1 b, fun u hu hu' g => ?_, fun τ x => ?_, fun τ k => ?_⟩, fun T' hT' => ?_⟩
  · obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hu
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hu' ⊢
    have ha' : a ∈ GfC V := by
      have := hN.conj_mem _ hu' b⁻¹
      simpa [mul_assoc] using this
    rw [← f2 a ha ha' (g * b)]
    congr 1
    simp only [mul_assoc, inv_mul_cancel, mul_one]
  · have e : (fun k => φ (x * kAt θ V τ (ε τ) (fr τ * (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹) k * b)) =
        fun k => φ (x * b * kAt θ V τ (ε τ) (fr τ) k) := funext fun k => by
      rw [← inv_mul_kAt_mul hθ V b τ (hfr τ).1 (hfr τ).2 k]
      simp only [mul_assoc, mul_inv_cancel_left]
    show (fun k => φ (x * kAt θ V τ (ε τ) (fr τ * (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹) k * b)) ∈ _root_.GlobalTheory.Published.AutFin.coeffSpan (ρ τ)
    rw [e]
    exact f3 τ (x * b)
  · have := GlobalTheory.RegSch.CentreRight.gelf_rTr_all hθ b τ k (GlobalTheory.SphSmooth.mem_smFun_of_isSm hθ f1.smooth)
    show gelf θ V τ k (rTr V b φ) = c τ k • rTr V b φ
    rw [this, f4]
    rfl
  · intro μ 𝓕 hμ h𝓕 h1 g
    have := f5 T' hT' μ 𝓕 hμ h𝓕 h1 (g * b)
    simpa [mul_assoc] using this

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Transl
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.LeviU

open Formalism.UG (cT)

section Abstract

variable {R : Type} [CommRing R] {a b : ℕ}

theorem eq_zero_of_mem_span_cols {L : Matrix (Fin b) (Fin a) R} {C : Matrix (Fin a) (Fin b) R} (hLC : L * C = 1)
    {I : Set (Fin b)} {w : Fin a → R} (hw : w ∈ Submodule.span R ((fun i => Cᵀ i) '' I))
    (h0 : ∀ i ∈ I, (L *ᵥ w) i = 0) : w = 0 := by
  classical
  have key : ∀ v ∈ Submodule.span R ((fun i => Cᵀ i) '' I), ∃ c : Fin b → R, (∀ i, i ∉ I → c i = 0) ∧ v = C *ᵥ c := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v h =>
      obtain ⟨i, hi, rfl⟩ := h
      refine ⟨Pi.single i 1, fun i' hi' => Pi.single_eq_of_ne (by rintro rfl; exact hi' hi) _, ?_⟩
      rw [mulVec_single_one]
      rfl
    | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, rfl⟩ := hx
      obtain ⟨d, hd, rfl⟩ := hy
      exact ⟨c + d, fun i hi => by simp [hc i hi, hd i hi], by rw [mulVec_add]⟩
    | smul t x _ hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      exact ⟨t • c, fun i hi => by simp [hc i hi], by rw [mulVec_smul]⟩
  obtain ⟨c, hc, rfl⟩ := key w hw
  have e : L *ᵥ (C *ᵥ c) = c := by rw [mulVec_mulVec, hLC, one_mulVec]
  rw [e] at h0
  have : c = 0 := funext fun i => by
    by_cases hi : i ∈ I
    · exact h0 i hi
    · exact hc i hi
  rw [this, mulVec_zero]

theorem mul_eq_of_conj (s : R →+* R) {G H A : Matrix (Fin a) (Fin a) R} {C : Matrix (Fin a) (Fin b) R}
    {B : Matrix (Fin b) (Fin b) R} (hHG : H * G = 1) (hU : cT s H * A * H = A) (hHC : H * C = C * B) :
    cT s C * A * G = cT s B * (cT s C * A) := by
  calc cT s C * A * G = cT s C * (cT s H * A * H) * G := by rw [hU]
    _ = cT s (H * C) * A * (H * G) := by rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
    _ = cT s B * (cT s C * A) := by
      rw [hHC, hHG, Formalism.UG.cT_mul, Matrix.mul_one]; simp only [Matrix.mul_assoc]

theorem mul_eq_self_of_pair (s : R →+* R) {G A : Matrix (Fin a) (Fin a) R} {C D : Matrix (Fin a) (Fin b) R}
    {B : Matrix (Fin b) (Fin b) R} (hU : cT s G * A * G = A) (hCD : cT s C * A * D = 1) (hGC : G * C = C)
    (hGD : G * D = D * B) : G * D = D := by
  have hB : B = 1 := by
    calc B = cT s C * A * D * B := by rw [hCD, Matrix.one_mul]
      _ = cT s (G * C) * A * (G * D) := by rw [hGC, hGD]; simp only [Matrix.mul_assoc]
      _ = cT s C * (cT s G * A * G) * D := by rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hU, hCD]
  rw [hGD, hB, Matrix.mul_one]

end Abstract

section Frame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}

theorem mat_inv_mul (g : GAd σ J) : (matHom _ σ J g⁻¹).1 * (matHom _ σ J g).1 = 1 := by
  rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]

theorem adMat_mul_eq_one {a b : ℕ} {L : Matrix (Fin a) (Fin b) E} {C : Matrix (Fin b) (Fin a) E} (h : L * C = 1) :
    adMat F L * adMat F C = 1 := by
  rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]

theorem cT_initCols_mul (C : Matrix (Fin n) (Fin r) E) (k : Fin r) :
    cT (sigR (AF F) σ) (adMat F (initCols C k)) * adMat F J =
      (adMat F (cT (σ : E →+* E) C * J)).submatrix (Fin.castLE k.2) id := by
  have c1 : cT (sigR (AF F) σ) (adMat F (initCols C k)) = adMat F (cT (σ : E →+* E) (initCols C k)) := rfl
  rw [c1, ← Matrix.map_mul]
  rfl

theorem exists_height_lower_bound (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) {T : Finset (Fin r)} {κ : Fin r}
    (hκ : κ ∉ upTo T) {g : GAd σ J} (hl : g ∈ levi σ J X Y T) (hu : g ∈ unip σ J X (insert κ T)) {j : Fin r}
    (hj : j ∈ upTo T) : (matHom _ σ J g).1 *ᵥ (adMat F X)ᵀ j = (adMat F X)ᵀ j := by
  have hκj : j < κ := by
    obtain ⟨k, hk, hjk⟩ := hj
    by_contra hc
    exact hκ ⟨k, hk, (not_lt.1 hc).trans hjk⟩
  have h1 := (Subgroup.mem_iInf.1 hu.1 j).2 _ (Submodule.subset_span ⟨j, rfl, rfl⟩)
  have hLC : adMat F (cT (σ : E →+* E) Y * J) * adMat F X = 1 := adMat_mul_eq_one (yx h hJ hW)
  refine sub_eq_zero.1 (eq_zero_of_mem_span_cols hLC h1 ?_)
  rintro i ⟨k, hk, hik, hkj⟩
  have hkT : k ∈ T := by
    rcases Finset.mem_insert.1 hk with rfl | hk'
    · exact absurd (hkj.trans hκj) (lt_irrefl _)
    · exact hk'
  have hl' := inv_mem hl
  simp only [levi, Subgroup.mem_iInf] at hl'
  obtain ⟨B, -, e⟩ := (Subgroup.mem_inf.1 (hl' k hkT)).2
  have h2 := mul_eq_of_conj (A := adMat F J) (sigR (AF F) σ) (mat_inv_mul g) (g⁻¹).2 e
  rw [cT_initCols_mul] at h2
  set L := (adMat F (cT (σ : E →+* E) Y * J)).submatrix (Fin.castLE k.2) id with hL
  have h3 : L *ᵥ (adMat F X)ᵀ j = 0 := by
    funext p
    have hp : Fin.castLE k.2 p ≠ j := fun hc => by
      have h4 : (Fin.castLE k.2 p).val ≤ k.val := Nat.le_of_lt_succ p.2
      have h5 : k.val < j.val := hkj
      rw [hc] at h4
      omega
    exact (congrFun (congrFun hLC (Fin.castLE k.2 p)) j).trans (Matrix.one_apply_ne hp)
  have h4 : L *ᵥ ((matHom _ σ J g).1 *ᵥ (adMat F X)ᵀ j - (adMat F X)ᵀ j) = 0 := by
    rw [mulVec_sub, mulVec_mulVec, h2, ← mulVec_mulVec, h3, mulVec_zero, sub_zero]
  exact congrFun h4 ⟨i.val, Nat.lt_succ_of_le hik⟩

theorem fix_y (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) {T : Finset (Fin r)} {κ : Fin r}
    (hκ : κ ∉ upTo T) {g : GAd σ J} (hl : g ∈ levi σ J X Y T) (hu : g ∈ unip σ J X (insert κ T)) {i : Fin r}
    (hi : i ∈ upTo T) : (matHom _ σ J g).1 *ᵥ (adMat F Y)ᵀ i = (adMat F Y)ᵀ i := by
  obtain ⟨k, hkT, hik⟩ := hi
  simp only [levi, Subgroup.mem_iInf] at hl
  obtain ⟨B, -, e⟩ := (Subgroup.mem_inf.1 (hl k hkT)).2
  have hGC : (matHom _ σ J g).1 * adMat F (initCols X k) = adMat F (initCols X k) :=
    Matrix.ext_col fun p => exists_height_lower_bound h hJ hW hκ (by simpa only [levi, Subgroup.mem_iInf] using hl) hu
      ⟨k, hkT, Nat.le_of_lt_succ p.2⟩
  have hCD : cT (sigR (AF F) σ) (adMat F (initCols X k)) * adMat F J * adMat F (initCols Y k) = 1 := by
    rw [cT_initCols_mul]
    have h1 : adMat F (cT (σ : E →+* E) X * J) * adMat F Y = 1 := adMat_mul_eq_one hW.xy
    exact Matrix.ext fun p q => (congrFun (congrFun h1 (Fin.castLE k.2 p)) (Fin.castLE k.2 q)).trans (by simp [Matrix.one_apply])
  have h2 := mul_eq_self_of_pair (A := adMat F J) (sigR (AF F) σ) g.2 hCD hGC e
  exact congrArg (fun M => Mᵀ ⟨i.val, Nat.lt_succ_of_le hik⟩) h2

theorem levi_inf_unip_le_uPart_general (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y)
    (T : Finset (Fin r)) {κ : Fin r} (hκ : κ ∉ upTo T) :
    levi σ J X Y T ⊓ unip σ J X (insert κ T) ≤ uPart σ J X Y T := by
  rintro g ⟨hl, hu⟩
  have key : colSpan F X (upTo T) ⊔ colSpan F Y (upTo T) ≤ LinearMap.eqLocus (matHom _ σ J g).1.mulVecLin LinearMap.id := by
    refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨j, hj, rfl⟩
      exact exists_height_lower_bound h hJ hW hκ hl hu hj
    · rintro _ ⟨j, hj, rfl⟩
      exact fix_y h hJ hW hκ hl hu hj
  exact fun y hy => key hy

end Frame

theorem levi_inf_unip_le_uPart : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)) (κ : Fin m), κ ∉ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T → levi D.sp.cm.sig V.gram X Y T ⊓ unip D.sp.cm.sig V.gram X (insert κ T) ≤ uPart D.sp.cm.sig V.gram X Y T := by
  intro D V m X Y hW T κ hκ
  obtain ⟨h, hJ'⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm
  exact levi_inf_unip_le_uPart_general h (hJ' V) hW T hκ

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.LeviU
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}

theorem mem_frameStab_initCols {C : Matrix (Fin n) (Fin r) E} {k : Fin r} {g : GAd σ J}
    (h : ∀ i : Fin r, i ≤ k → (matHom _ σ J g).1 *ᵥ (adMat F C)ᵀ i = (adMat F C)ᵀ i) :
    g ∈ frameStab σ J (initCols C k) ⊤ := by
  simp only [GlobalTheory.StdPar.frameStab, Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk,
    Set.mem_ofPred_eq, Subgroup.mem_top, true_and]
  refine ⟨1, ?_⟩
  rw [Units.val_one, Matrix.mul_one]
  ext i j
  have hjk : Fin.castLE (Nat.succ_le_of_lt k.isLt) j ≤ k := by
    rw [Fin.le_iff_val_le_val, Fin.val_castLE]
    exact Nat.lt_succ_iff.mp j.isLt
  exact congrFun (h _ hjk) i

theorem uPart_le_levi_general (X Y : Matrix (Fin n) (Fin r) E) (T : Finset (Fin r)) :
    uPart σ J X Y T ≤ levi σ J X Y T := by
  intro g hg
  have hfix : ∀ y ∈ GlobalTheory.StdPar.colSpan F X (GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T) ⊔
      GlobalTheory.StdPar.colSpan F Y (GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T),
      (↑(GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) σ J g) : Matrix (Fin n) (Fin n) _) *ᵥ y = y := hg
  simp only [GlobalTheory.StdPar.levi, Subgroup.mem_iInf, Subgroup.mem_inf]
  intro k hk
  constructor
  · apply mem_frameStab_initCols
    intro i hi
    exact hfix _ (Submodule.mem_sup_left (Submodule.subset_span ⟨i, ⟨k, hk, hi⟩, rfl⟩))
  · apply mem_frameStab_initCols
    intro i hi
    exact hfix _ (Submodule.mem_sup_right (Submodule.subset_span ⟨i, ⟨k, hk, hi⟩, rfl⟩))

end General

theorem uPart_le_levi : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E) (T : Finset (Fin m)),
    uPart D.sp.cm.sig V.gram X Y T ≤ levi D.sp.cm.sig V.gram X Y T := by
  intro D V m X Y T
  exact uPart_le_levi_general X Y T

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice

def IsSliceFrame {D : D7} (V V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V) {m m' : ℕ}
    (X Y : Matrix (Fin V.rank) (Fin m) D.host.E) (T : Finset (Fin m)) (e : Fin m' → Fin m)
    (X' Y' : Matrix (Fin V'.rank) (Fin m') D.host.E) : Prop :=
  StrictMono e ∧ (∀ i, i ∉ upTo T ↔ i ∈ Set.range e) ∧
    frameMat V V' ι * X' = X.submatrix id e ∧ frameMat V V' ι * Y' = Y.submatrix id e

variable {D : D7} {V V' : HSp D} {ι : V'.V →ₗ[D.host.E] V.V}

abbrev prM (V V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V) : Matrix (Fin V'.rank) (Fin V.rank) D.host.E :=
  GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.projMat D.sp.cm V' V ι

theorem repr_symm (V : HSp D) (a : Fin V.rank → D.host.E) (i : Fin V.rank) :
    V.frame.repr (V.frame.equivFun.symm a) i = a i := by
  rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]

theorem hT_frame (V : HSp D) (a b : Fin V.rank → D.host.E) :
    V.hT (V.frame.equivFun.symm a) (V.frame.equivFun.symm b) = ∑ i, ∑ j, star (a i) * V.gram i j * b j := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.hT_coord]
  simp only [repr_symm]

theorem prM_mul_frameMat (hι : HSpace.IsIsomEmb V' V ι) : prM V V' ι * frameMat V V' ι = 1 :=
  GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.projMat_embMat D.sp.cm V' V ι hι

theorem cT_frameMat_mul_gram :
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat V V' ι) * V.gram = V'.gram * prM V V' ι :=
  GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_projMat D.sp.cm V' V ι

theorem mat_eq (hι : HSpace.IsIsomEmb V' V ι) {s : GA D V' →* GA D V} (hs : ∀ h, EmbRel V V' ι (s h) h) (b : GA D V') :
    (matHom V (s b)).1 = 1 + HMul.hMul (HMul.hMul (adMat D.host.F (frameMat V V' ι)) ((matHom V' b).1 - 1)) (adMat D.host.F (prM V V' ι)) := by
  rw [(GlobalTheory.AutFunCompare.embRel_iff V V' ι hι (s b) b).1 (hs b)]
  rfl

theorem prM_mulVec_eq_zero {x : Fin V.rank → D.host.E}
    (h : ∀ v' : V'.V, V.hT (V.frame.equivFun.symm x) (ι v') = 0) : prM V V' ι *ᵥ x = 0 := by
  have hJ : IsUnit V'.gram.det := GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit V'
  have h1 : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat V V' ι) * V.gram) *ᵥ x = 0 := by
    funext j
    have h2 : V.hT (ι (V'.frame j)) (V.frame.equivFun.symm x) = 0 :=
      (V.herm.eq (V.frame.equivFun.symm x) (ι (V'.frame j))).symm.trans (by rw [h]; simp)
    rw [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.hT_coord] at h2
    simp only [repr_symm] at h2
    simp only [Pi.zero_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Eq.trans (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_) h2
    simp only [Formalism.UG.cT, frameMat, LinearMap.toMatrix_apply, Matrix.transpose_apply, Matrix.map_apply]
    rfl
  rw [cT_frameMat_mul_gram, ← Matrix.mulVec_mulVec] at h1
  exact Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 hJ) (h1.trans (Matrix.mulVec_zero _).symm)

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice
end
end
