module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdelicCharacterArchimedeanForm
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle054
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1911
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle309
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ComplexMultiplicationJPremises
public import GroundTheory.GlobalFields.ClassFieldConsequences.HilbertClassField
public import GroundTheory.GlobalFields.ComplexMultiplication.ClassGroupAction
public import GroundTheory.GlobalFields.ComplexMultiplication.HilbertClassField
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle054
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle056
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.Bundle002
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle053
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle319

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal Matrix


theorem _root_.GlobalTheory.T.adelic_character_archimedean_form : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) → IsHomeomorph e → (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∃ a : F, a ≠ 0 ∧ (∀ x : Ainf F, ψ (pairA F x 0) = Complex.exp (2 * Real.pi * Complex.I * ((∑ w, ρ w a * e x w : ℝ) : ℂ))) ∧ ∃ ψf : AddChar (Af F) ℂ, GlobalTheory.CompanionTheory.SW.Core.IsStdChar F ψf ∧ ∀ y : Af F, ψ (pairA F 0 y) = ψf (algebraMap F (Af F) a * y) := by
  first | exact @GlobalTheory.CompanionTheory.Glob.CharAF.exists_char_data | exact GlobalTheory.CompanionTheory.Glob.CharAF.exists_char_data | (intros; apply GlobalTheory.CompanionTheory.Glob.CharAF.exists_char_data <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal NNReal Topology

theorem _root_.GlobalTheory.T.hermitian_measure_scaling_transform : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure (Ainf F)), lam.IsAddHaarMeasure → ∀ t : Ainf F, IsUnit t → ∀ c : ℝ≥0, lam.map (fun y => t * y) = c • lam → ∀ τ : HermR (Ainf F) σ 1 → HermR (Ainf F) σ 1, Measurable τ → (∀ S i j, (τ S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) i j = algebraMap (Ainf F) (Ainf F ⊗[F] E) t * (S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) i j) → (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b lam 1).map τ = c • GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b lam 1 := by
  first | exact @GlobalTheory.CompanionTheory.SW.DilU.coordHerm_map_ainf | exact GlobalTheory.CompanionTheory.SW.DilU.coordHerm_map_ainf | (intros; apply GlobalTheory.CompanionTheory.SW.DilU.coordHerm_map_ainf <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal NNReal Topology

theorem _root_.GlobalTheory.T.coordinate_measure_scaling_tensor : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure (Ainf F)), lam.IsAddHaarMeasure → ∀ t : Ainf F, IsUnit t → ∀ c : ℝ≥0, lam.map (fun y => t * y) = c • lam → (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam 1 M).map (fun X p i => algebraMap (Ainf F) (Ainf F ⊗[F] E) t * X p i) = (c ^ (d * M)) • GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam 1 M := by
  first | exact @GlobalTheory.CompanionTheory.SW.Dil.coordW_map_unit | exact GlobalTheory.CompanionTheory.SW.Dil.coordW_map_unit | (intros; apply GlobalTheory.CompanionTheory.SW.Dil.coordW_map_unit <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.GoodPos

theorem stab_of_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf →
    ∀ (w : InfinitePlace F) (cw : GL (Fin n) (w.Completion ⊗[F] E)),
      (∃ ε : Fin n → Bool, Formalism.UG.cT (sigR _ σ) cw.1 * JR w.Completion J * cw.1 =
        Matrix.diagonal fun i => if ε i then 1 else -1) →
    ∀ (l d : ℕ) (h : l + d ≤ r),
      ∃ (u : GArch σ J w) (N : Matrix (Fin r) (Fin r) (w.Completion ⊗[F] E)),
        (matHom _ σ J u).1 * Xf.map (inclR (F := F) w.Completion) =
          Xf.map (inclR (F := F) w.Completion) + Xf.map (inclR (F := F) w.Completion) * N ∧
        (∀ i j, N i j ≠ 0 → (i.val < l ∧ l ≤ j.val) ∨ (i.val < l + d ∧ l + d ≤ j.val)) ∧
        (∀ v : Fin n → w.Completion ⊗[F] E,
          (∀ i : Fin r, i.val < l + d →
            Matrix.mulVec ((Formalism.UG.cT (σ : E →+* E) Xf * J).map (inclR (F := F) w.Completion)) v i = 0) →
          ∃ a : Fin r → w.Completion ⊗[F] E, (∀ i, a i ≠ 0 → i.val < l + d) ∧
            Matrix.mulVec (matHom _ σ J u).1 v - v = Matrix.mulVec (Xf.map (inclR (F := F) w.Completion)) a) ∧
        ∃ y₀ : GL (Fin d) (w.Completion ⊗[F] E), ∀ k : GL (Fin d) (w.Completion ⊗[F] E),
          Formalism.UG.cT (sigR w.Completion σ) k.1 * k.1 = 1 → ∀ g : GArch σ J w,
          (matHom _ σ J g).1 = 1 + (GlobalTheory.BlockForms.blkCols h Xf).map (inclR (F := F) w.Completion) * ((y₀ * k * y₀⁻¹).1 - 1) *
            (Formalism.UG.cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h Yf) * J).map (inclR (F := F) w.Completion) +
          (GlobalTheory.BlockForms.blkCols h Yf).map (inclR (F := F) w.Completion) * (Formalism.UG.cT (sigR w.Completion σ) ((y₀ * k * y₀⁻¹)⁻¹).1 - 1) *
            (Formalism.UG.cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h Xf) * J).map (inclR (F := F) w.Completion) →
          u * g * u⁻¹ ∈ stabArch σ J w cw := by
  intro F E _ _ _ _ _ σ hcm n J hJ r Xf Yf hW w cw hcw l d h
  obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
  obtain ⟨ε, hε⟩ := hcw
  have hbij := infEmb_bijective hcm τ
  let φ : w.Completion ⊗[F] E →+* ℂ := infEmb τ
  let e : w.Completion ⊗[F] E ≃+* ℂ := RingEquiv.ofBijective φ hbij
  have hsymm : ∀ z, φ (e.symm z) = z := e.apply_symm_apply
  have hinj : ∀ {a b : ℕ} {P Q : Matrix (Fin a) (Fin b) (w.Completion ⊗[F] E)}, P.map φ = Q.map φ → P = Q :=
    fun hPQ => Matrix.map_injective hbij.1 hPQ
  have hincl : ∀ x : E, φ (inclR (F := F) w.Completion x) = τ.1 x := by
    intro x
    change infEmb τ ((1 : w.Completion) ⊗ₜ[F] x) = _
    simp
  have hinclM : ∀ {a b : ℕ} (Z : Matrix (Fin a) (Fin b) E), (Z.map (inclR (F := F) w.Completion)).map φ = Z.map τ.1 := by
    intro a b Z; ext i j; exact hincl _
  have hcTE : ∀ {a b : ℕ} (Z : Matrix (Fin a) (Fin b) E), (Formalism.UG.cT (σ : E →+* E) Z).map τ.1 = (Z.map τ.1).conjTranspose := by
    intro a b Z; ext i j
    simp [Formalism.UG.cT, Matrix.conjTranspose_apply, hcm.2.2.2]
  have hcTR : ∀ {a b : ℕ} (Z : Matrix (Fin a) (Fin b) (w.Completion ⊗[F] E)),
      (Formalism.UG.cT (sigR w.Completion σ) Z).map φ = (Z.map φ).conjTranspose := by
    intro a b Z; ext i j; exact (infEmb_sigR hcm τ _).symm
  have hbcb : ∀ {m : ℕ} (a : GL (Fin m) ℂ), Formalism.UG.bc φ (Formalism.UG.bc e.symm.toRingHom a) = a := by
    intro m a; ext i j; exact hsymm _
  have hJR : (JR w.Completion J).map φ = J.map τ.1 := hinclM J

  have hJ' : (J.map τ.1).conjTranspose = J.map τ.1 := by
    rw [← hcTE]; congr 1; ext i j; exact hJ.1 i j
  have hxx : (Xf.map τ.1).conjTranspose * J.map τ.1 * Xf.map τ.1 = 0 := by
    rw [← hcTE, ← Matrix.map_mul, ← Matrix.map_mul, hW.xx, Matrix.map_zero _ (map_zero _)]
  have hyy : (Yf.map τ.1).conjTranspose * J.map τ.1 * Yf.map τ.1 = 0 := by
    rw [← hcTE, ← Matrix.map_mul, ← Matrix.map_mul, hW.yy, Matrix.map_zero _ (map_zero _)]
  have hxy : (Xf.map τ.1).conjTranspose * J.map τ.1 * Yf.map τ.1 = 1 := by
    rw [← hcTE, ← Matrix.map_mul, ← Matrix.map_mul, hW.xy, Matrix.map_one _ (map_zero _) (map_one _)]
  have hc' : (Formalism.UG.bc φ cw).1.conjTranspose * J.map τ.1 * (Formalism.UG.bc φ cw).1 =
      Matrix.diagonal (fun i => if ε i then 1 else -1) := by
    have := congrArg (fun P => P.map φ) hε
    simp only [Matrix.map_mul, hcTR, hJR, Matrix.diagonal_map (map_zero _)] at this
    change (cw.1.map φ).conjTranspose * _ * cw.1.map φ = _
    rw [this]; congr 1; funext i; split_ifs <;> simp
  obtain ⟨u, N, hu, huXN, hNX, hNv, y₀, hy⟩ := GlobalTheory.MajPosCpx.exists_unip_conj_unitary n r (J.map τ.1) hJ' (Xf.map τ.1) (Yf.map τ.1) hxx hyy hxy
    (Formalism.UG.bc φ cw) ε hc' l d h

  let u0 : GL (Fin n) (w.Completion ⊗[F] E) := Formalism.UG.bc e.symm.toRingHom u
  have hu0 : u0.1.map φ = u.1 := congrArg Units.val (hbcb u)
  have hmem : u0 ∈ HR w.Completion σ J := by
    change Formalism.UG.cT (sigR w.Completion σ) u0.1 * JR w.Completion J * u0.1 = JR w.Completion J
    apply hinj
    rw [Matrix.map_mul, Matrix.map_mul, hcTR, hu0, hJR]
    exact hu
  let uA : GArch σ J w := (⟨u0, hmem⟩ : HR w.Completion σ J)
  have huA : (matHom _ σ J uA) = u0 := rfl
  let N0 : Matrix (Fin r) (Fin r) (w.Completion ⊗[F] E) := N.map e.symm
  have hN0 : N0.map φ = N := by ext i j; exact hsymm _
  refine ⟨uA, N0, ?_, ?_, ?_, Formalism.UG.bc e.symm.toRingHom y₀, ?_⟩
  · rw [huA]
    apply hinj
    rw [Matrix.map_mul, Matrix.map_add φ (map_add φ), Matrix.map_mul, hN0, hinclM, hu0]
    exact huXN
  · intro i j hne
    refine hNX i j ?_
    intro h0
    apply hne
    have : φ (N0 i j) = N i j := hsymm _
    rw [h0] at this
    exact hbij.1 (this.trans (map_zero φ).symm)
  · intro v hv
    have hv' : ∀ i : Fin r, i.val < l + d → Matrix.mulVec ((Xf.map τ.1).conjTranspose * J.map τ.1) (φ ∘ v) i = 0 := by
      intro i hi
      have := congrArg φ (hv i hi)
      rw [RingHom.map_mulVec, hinclM, Matrix.map_mul, hcTE, map_zero] at this
      exact this
    obtain ⟨a', ha', hav⟩ := hNv (φ ∘ v) hv'
    refine ⟨e.symm ∘ a', fun i hi => ha' i fun h0 => hi ?_, ?_⟩
    · show e.symm (a' i) = 0
      rw [h0, map_zero]
    · rw [huA]
      funext i
      apply hbij.1
      have hφa : φ ∘ (e.symm ∘ a') = a' := funext fun i => hsymm _
      rw [Pi.sub_apply, map_sub, RingHom.map_mulVec, RingHom.map_mulVec, hinclM, hφa]
      have h2 := congrFun hav i
      rw [Pi.sub_apply] at h2
      have h3 : (u0.1.map φ) = u.1 := hu0
      rw [h3]
      exact h2
  · intro k hk g hg
    have hval : ∀ {m : ℕ} (a : GL (Fin m) (w.Completion ⊗[F] E)), a.1.map φ = (Formalism.UG.bc φ a).1 := fun a => rfl
    have hk' : (Formalism.UG.bc φ k).1.conjTranspose * (Formalism.UG.bc φ k).1 = 1 := by
      have := congrArg (fun P => P.map φ) hk
      simpa only [Matrix.map_mul, hcTR, Matrix.map_one _ (map_zero _) (map_one _), hval] using this
    have hM := hy (Formalism.UG.bc φ k) hk'
    have hgφ : (matHom _ σ J g).1.map φ = 1 + ((Xf.map τ.1).submatrix id fun j : Fin d => (⟨l + j.val, by omega⟩ : Fin r)) *
        ((y₀ * Formalism.UG.bc φ k * y₀⁻¹).1 - 1) *
        (((Yf.map τ.1).submatrix id fun j : Fin d => (⟨l + j.val, by omega⟩ : Fin r)).conjTranspose * J.map τ.1) +
        ((Yf.map τ.1).submatrix id fun j : Fin d => (⟨l + j.val, by omega⟩ : Fin r)) *
        (((y₀ * Formalism.UG.bc φ k * y₀⁻¹)⁻¹).1.conjTranspose - 1) *
        (((Xf.map τ.1).submatrix id fun j : Fin d => (⟨l + j.val, by omega⟩ : Fin r)).conjTranspose * J.map τ.1) := by
      rw [hg]
      simp only [Matrix.map_add φ (map_add φ), Matrix.map_sub φ (map_sub φ), Matrix.map_mul, Matrix.map_one φ (map_zero φ) (map_one φ),
        hinclM, hcTE, hcTR, hval, map_mul, map_inv, hbcb]
      rfl
    have hbu : Formalism.UG.bc φ u0 = u := hbcb u
    have hmain : (cw⁻¹ * matHom _ σ J (uA * g * uA⁻¹) * cw).1.map φ =
        ((Formalism.UG.bc φ cw)⁻¹).1 * u.1 * (matHom _ σ J g).1.map φ * (u⁻¹).1 * (Formalism.UG.bc φ cw).1 := by
      rw [hval]
      simp only [map_mul, map_inv, huA, hbu, Units.val_mul, mul_assoc]
      rfl
    rw [mem_stabArch]
    generalize hx : cw⁻¹ * matHom _ σ J (uA * g * uA⁻¹) * cw = x
    change Formalism.UG.cT _ x.1 * 1 * x.1 = 1
    apply hinj
    rw [mul_one, Matrix.map_mul, hcTR, Matrix.map_one _ (map_zero _) (map_one _), ← hx, hmain, hgφ]
    exact hM

end GlobalTheory.CompanionTheory.GoodPos
end
end

section

open NumberField IsDedekindDomain IntermediateField GroundTheory.Global GroundTheory.Global.Elliptic
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.Published

section

variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ]

theorem latticeCurve_eq_weierstrassCurve (L : PeriodPair) :
    GlobalTheory.latticeCurve L = weierstrassCurve L := by
  simp [GlobalTheory.latticeCurve, weierstrassCurve, neg_div]

theorem j_eq_of_eq {W W' : WeierstrassCurve ℂ} [W.IsElliptic] [W'.IsElliptic] (h : W = W') :
    W.j = W'.j := by
  subst h
  rfl

theorem latticeCurve_j (L : PeriodPair) : (GlobalTheory.latticeCurve L).j = (weierstrassCurve L).j :=
  j_eq_of_eq (latticeCurve_eq_weierstrassCurve L)

theorem under_ne_bot (M : IntermediateField K ℂ) [NumberField M] {P : Ideal (𝓞 M)} (hP : P ≠ ⊥) :
    P.under (𝓞 K) ≠ ⊥ :=
  fun h => hP (Ideal.eq_bot_of_comap_eq_bot h)

theorem isUnramifiedAbelian_hilbertClassField :
    GlobalTheory.Published.IsUnramifiedAbelian (hilbertClassField K ℂ) := by
  have : NumberField (hilbertClassField K ℂ) := NumberField.of_module_finite K _
  refine ⟨inferInstance, inferInstance, fun P hp hP => ?_⟩
  let v : HeightOneSpectrum (𝓞 K) := ⟨P.under (𝓞 K), inferInstance, under_ne_bot _ hP⟩
  exact (isUnramifiedEverywhere_hilbertClassField K ℂ).1 v P hp ⟨rfl⟩

theorem isUnramifiedEverywhere_of_isUnramifiedAbelian [_root_.NumberField.IsTotallyComplex K]
    {M : IntermediateField K ℂ} [NumberField M] (h : GlobalTheory.Published.IsUnramifiedAbelian M) :
    IsUnramifiedEverywhere K M := by
  refine ⟨fun v P hp hv => ?_, fun v w hw => ?_⟩
  · exact h.2.2 P (Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P)
  · exact InfinitePlace.isUnramified_iff.2 (Or.inr (hw ▸ IsTotallyComplex.isComplex v))

theorem isHilbertClassField_hilbertClassField [_root_.NumberField.IsTotallyComplex K] :
    GlobalTheory.Published.IsHilbertClassField (hilbertClassField K ℂ) := by
  refine ⟨isUnramifiedAbelian_hilbertClassField, fun M hM => ?_⟩
  have := hM.1
  have := hM.2.1
  have : NumberField M := NumberField.of_module_finite K _
  exact (le_hilbertClassField_iff K ℂ M).2 (isUnramifiedEverywhere_of_isUnramifiedAbelian hM)

theorem isArtinMap_hilbertClassFieldArtinEquiv :
    GlobalTheory.Published.IsArtinMap (hilbertClassFieldArtinEquiv K ℂ).toMonoidHom := by
  intro 𝔭 𝔓 hP hO
  have : NumberField (hilbertClassField K ℂ) := NumberField.of_module_finite K _
  have hne : (𝔭 : Ideal (𝓞 K)) ≠ ⊥ := mem_nonZeroDivisors_iff_ne_zero.1 𝔭.2
  have hpp : (𝔭 : Ideal (𝓞 K)).IsPrime := by
    rw [hO.over]
    exact Ideal.IsPrime.under _ _
  let v : HeightOneSpectrum (𝓞 K) := ⟨𝔭, hpp, hne⟩
  let w : HeightOneSpectrum (𝓞 (hilbertClassField K ℂ)) :=
    ⟨𝔓, hP, Ideal.ne_bot_of_liesOver_of_ne_bot hne 𝔓⟩
  have hwv : w.asIdeal.LiesOver v.asIdeal := hO
  have : Finite (𝓞 (hilbertClassField K ℂ) ⧸ w.asIdeal) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  have e : hilbertClassFieldArtinEquiv K ℂ (ClassGroup.mk0 𝔭) = _ :=
    hilbertClassFieldArtinEquiv_mk0 K ℂ v w
  change IsArithFrobAt (𝓞 K) (hilbertClassFieldArtinEquiv K ℂ (ClassGroup.mk0 𝔭)) w.asIdeal
  rw [e]
  exact IsArithFrobAt.arithFrobAt _ _ _

theorem lattice_eq_idealLattice {𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {L : PeriodPair}
    (h : GlobalTheory.Published.IsIdealLattice 𝔞 L) : L.lattice = idealLattice (algebraMap K ℂ) 𝔞.1 :=
  SetLike.coe_injective h

theorem latticeEnd_eq_cmRing [_root_.NumberField.IsTotallyComplex K] (hK : Module.finrank ℚ K = 2)
    {𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {L : PeriodPair} (h : GlobalTheory.Published.IsIdealLattice 𝔞 L) :
    GroundTheory.Global.Elliptic.periodLatticeEnd L = cmRingOfEmbedding (algebraMap K ℂ) := by
  rw [← latticeEnd_ideal (algebraMap K ℂ) hK 𝔞]
  ext α
  show (∀ l ∈ L.lattice, α * l ∈ L.lattice) ↔
    ∀ l ∈ (idealPeriodPair (algebraMap K ℂ) hK 𝔞).lattice,
      α * l ∈ (idealPeriodPair (algebraMap K ℂ) hK 𝔞).lattice
  have e : (idealPeriodPair (algebraMap K ℂ) hK 𝔞).lattice = L.lattice := by
    rw [lattice_eq_idealLattice h]
    exact lattice_idealPeriodPair (algebraMap K ℂ) hK 𝔞
  rw [e]

end

theorem complexMultiplicationJ : GlobalTheory.Published.ComplexMultiplicationJSt := by
  intro K _ _ _ _ hK
  refine ⟨hilbertClassField K ℂ, hilbertClassFieldArtinEquiv K ℂ,
    isHilbertClassField_hilbertClassField, isArtinMap_hilbertClassFieldArtinEquiv, ?_, ?_⟩
  · intro 𝔞 L hL
    rw [latticeCurve_j]
    exact adjoin_j_curve_eq_hilbertClassField hK
      (CMCurve.ofLattice (algebraMap K ℂ) L (latticeEnd_eq_cmRing hK hL))
  · intro 𝔞 𝔟 L L' hL hL' x hx
    have hE := latticeEnd_eq_cmRing hK hL
    have hlat : L'.lattice = idealLattice (algebraMap K ℂ) ↑𝔟⁻¹ * L.lattice := by
      rw [lattice_eq_idealLattice hL', lattice_eq_idealLattice hL, Units.val_mul, idealLattice_mul]
    rw [latticeCurve_j] at hx ⊢
    have hx' : x = ⟨(weierstrassCurve L).j, j_weierstrassCurve_mem_hilbertClassField hK L hE⟩ :=
      Subtype.ext hx
    rw [hx']
    exact hilbertClassFieldArtinEquiv_apply_j_weierstrassCurve hK L L' hE 𝔟 hlat

end GlobalTheory.CompanionTheory.Published
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test

section Abstract

variable {G : Type} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd G]

theorem integral_indicator_char_of_trivial (μ : Measure G) (H : AddSubgroup G)
    (hH : MeasurableSet (H : Set G)) (χ : G → ℂ) (h1 : ∀ x ∈ H, χ x = 1) :
    ∫ x, (H : Set G).indicator χ x ∂μ = ((μ (H : Set G)).toReal : ℂ) := by
  rw [integral_indicator hH, setIntegral_congr_fun hH (g := fun _ => (1 : ℂ)) (fun x hx => h1 x hx)]
  simp [Measure.real]

theorem integral_indicator_char_of_ne (μ : Measure G) [μ.IsAddLeftInvariant] (H : AddSubgroup G)
    (χ : G → ℂ) (hχ : ∀ x y, χ (x + y) = χ x * χ y) {h : G} (hh : h ∈ H) (hne : χ h ≠ 1) :
    ∫ x, (H : Set G).indicator χ x ∂μ = 0 := by
  have key : ∀ x, (H : Set G).indicator χ (x + h) = (H : Set G).indicator χ x * χ h := by
    intro x
    by_cases hx : x ∈ H
    · have hxh : x + h ∈ H := H.add_mem hx hh
      rw [Set.indicator_of_mem (by exact hxh), Set.indicator_of_mem (by exact hx), hχ]
    · have hxh : x + h ∉ H := fun hc => hx (by simpa using H.sub_mem hc hh)
      rw [Set.indicator_of_notMem (by exact hxh), Set.indicator_of_notMem (by exact hx), zero_mul]
  have h2 := integral_add_right_eq_self (μ := μ) ((H : Set G).indicator χ) h
  simp only [key] at h2
  rw [integral_mul_const] at h2
  have h3 : (∫ x, (H : Set G).indicator χ x ∂μ) * (χ h - 1) = 0 := by
    rw [mul_sub, h2, mul_one, sub_self]
  exact (mul_eq_zero.1 h3).resolve_right (sub_ne_zero.2 hne)

end Abstract

variable {F : Type} [Field F] [NumberField F]

def psiF (ψ : AddChar (AF F) ℂ) (y : Af F) : ℂ := ψ (pairA F 0 y)

def annV (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (U : Set (Fv F v)) : Set (Fv F v) :=
  {t | ∀ s ∈ U, psiV F ψ v (s * t) = 1}

def annF (ψ : AddChar (AF F) ℂ) (B : Set (Af F)) : Set (Af F) :=
  {b | ∀ y ∈ B, psiF ψ (y * b) = 1}

def fouInf (ψ : AddChar (AF F) ℂ) (lam : Measure (Ainf F)) (ρ : Ainf F → ℝ) (t : Ainf F) : ℂ :=
  ∫ x, (ρ x : ℂ) * psiInf F ψ (x * t) ∂lam

theorem psiF_add (ψ : AddChar (AF F) ℂ) (x y : Af F) : psiF ψ (x + y) = psiF ψ x * psiF ψ y := by
  have h : pairA F 0 (x + y) = pairA F 0 x + pairA F 0 y := Prod.ext (add_zero (0 : Ainf F)).symm rfl
  rw [psiF, h, AddChar.map_add_eq_mul]
  rfl

theorem psiF_zero (ψ : AddChar (AF F) ℂ) : psiF ψ 0 = 1 := by
  have h : pairA F 0 (0 : Af F) = 0 := rfl
  rw [psiF, h, AddChar.map_zero_eq_one]

theorem psiF_singleV (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (s : Fv F v) :
    psiF ψ (singleV F v s) = psiV F ψ v s := rfl

theorem psi_pairA (ψ : AddChar (AF F) ℂ) (x : Ainf F) (y : Af F) :
    ψ (pairA F x y) = psiInf F ψ x * psiF ψ y := by
  have h : pairA F x y = pairA F x 0 + pairA F 0 y :=
    Prod.ext (add_zero x).symm (zero_add y).symm
  rw [h, AddChar.map_add_eq_mul]
  rfl

theorem psiV_zero (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) : psiV F ψ v 0 = 1 := by
  classical
  have h : singleV F v (0 : Fv F v) = 0 := RestrictedProduct.single_zero _ v
  rw [← psiF_singleV, h, psiF_zero]

theorem psiV_add (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (x y : Fv F v) :
    psiV F ψ v (x + y) = psiV F ψ v x * psiV F ψ v y :=
  GlobalTheory.CompanionTheory.SW.PiV.psiV_add ψ v x y

theorem psiV_neg_of_eq_one (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) {x : Fv F v}
    (hx : psiV F ψ v x = 1) : psiV F ψ v (-x) = 1 := by
  have h := psiV_add ψ v (-x) x
  rw [neg_add_cancel, psiV_zero, hx, mul_one] at h
  exact h.symm

def annS (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (U : Set (Fv F v)) :
    AddSubgroup (Fv F v) where
  carrier := annV ψ v U
  add_mem' := by
    intro a b ha hb s hs
    rw [mul_add, psiV_add, ha s hs, hb s hs, one_mul]
  zero_mem' := by
    intro s _
    rw [mul_zero, psiV_zero]
  neg_mem' := by
    intro a ha s hs
    rw [mul_neg]
    exact psiV_neg_of_eq_one ψ v (ha s hs)

theorem coe_annS (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (U : Set (Fv F v)) :
    (annS ψ v U : Set (Fv F v)) = annV ψ v U := rfl

def boxS (S : Finset (HeightOneSpectrum (𝓞 F))) (U : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (Fv F v)) :
    AddSubgroup (Af F) where
  carrier := Coef.boxA S fun v => (U v : Set (Fv F v))
  add_mem' := by
    intro a b ha hb
    exact ⟨fun v hv => (U v).add_mem (ha.1 v hv) (hb.1 v hv),
      fun v hv => add_mem (ha.2 v hv) (hb.2 v hv)⟩
  zero_mem' := ⟨fun v _ => (U v).zero_mem, fun v _ => zero_mem _⟩
  neg_mem' := by
    intro a ha
    exact ⟨fun v hv => (U v).neg_mem (ha.1 v hv),
      fun v hv => neg_mem (ha.2 v hv)⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal Matrix


theorem _root_.GlobalTheory.T.adele_haar_product_decomposition : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] (m : Measure (ι → AF F)) (μ₁ : Measure (ι → Ainf F)) (μ₂ : Measure (ι → Af F)), m.IsAddHaarMeasure → μ₁.IsAddHaarMeasure → μ₂.IsAddHaarMeasure → ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ m.map (fun y : ι → AF F => ((fun i => (y i).1, fun i => (y i).2) : (ι → Ainf F) × (ι → Af F))) = c • μ₁.prod μ₂ := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.OneV.ProdM.map_split_eq_smul_prod | exact GlobalTheory.CompanionTheory.Hypotheses₂.OneV.ProdM.map_split_eq_smul_prod | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.OneV.ProdM.map_split_eq_smul_prod <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal NNReal Topology

theorem _root_.GlobalTheory.T.archimedean_haar_scaling_norm : ∀ (F : Type) [Field F] [NumberField F] (e : Ainf F ≃+* (InfinitePlace F → ℝ)), IsHomeomorph e → ∀ (lam : Measure (Ainf F)), lam.IsAddHaarMeasure → ∀ t : Ainf F, IsUnit t → lam.map (fun y => t * y) = (∏ w, ‖e t w‖₊)⁻¹ • lam := by
  first | exact @GlobalTheory.CompanionTheory.HaarScale.unit_mul_map_haar | exact GlobalTheory.CompanionTheory.HaarScale.unit_mul_map_haar | (intros; apply GlobalTheory.CompanionTheory.HaarScale.unit_mul_map_haar <;> assumption)
end
