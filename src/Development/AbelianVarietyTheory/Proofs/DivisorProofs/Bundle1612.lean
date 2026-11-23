module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle002
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MovedOfSplitPl
public import Formalism.LocalRingCardinality.DataHost
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Aesop.Main
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1559
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Development.AbelianVarietyTheory.Definitions.Foundations.StrictInterlaceIffDescEnum
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1298
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1446
import GroundTheory.AutomorphicForms.LocallyProfinite
import GroundTheory.AutomorphicForms.Bundle003
import GroundTheory.GlobalFields.KummerTheory.LocalIndex
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.UnitConjFrame

open GlobalTheory.AdLat GlobalTheory.UnRep

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem sg_one_tmul (c : E ≃ₐ[F] E) (e : E) :
    sg (FiniteAdeleRing (𝓞 F) F) c ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] e) = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] c e := by
  simp [sg, Algebra.TensorProduct.map_tmul]

theorem fm_map_sg (c : E ≃ₐ[F] E) (A : Matrix (Fin n) (Fin n) E) :
    (fm F A).map (sg (FiniteAdeleRing (𝓞 F) F) c) = fm F (A.map c) := by
  ext i j
  simp only [fm, Matrix.map_apply, sg_one_tmul]

theorem hermA_eq_dot (c : E ≃ₐ[F] E) (H : Matrix (Fin n) (Fin n) E) (x y : Fin n → RA F E) :
    hermA c H x y = x ⬝ᵥ (fm F H *ᵥ fun b => sg (FiniteAdeleRing (𝓞 F) F) c (y b)) := by
  simp only [hermA, dotProduct, Matrix.mulVec, fm, Matrix.map_apply, Finset.mul_sum, mul_assoc]

theorem hermA_mulVec (c : E ≃ₐ[F] E) (H : Matrix (Fin n) (Fin n) E) (M : Matrix (Fin n) (Fin n) (RA F E))
    (x y : Fin n → RA F E) :
    hermA c H (M *ᵥ x) (M *ᵥ y) =
      x ⬝ᵥ ((Mᵀ * fm F H * M.map (sg (FiniteAdeleRing (𝓞 F) F) c)) *ᵥ
        fun b => sg (FiniteAdeleRing (𝓞 F) F) c (y b)) := by
  rw [hermA_eq_dot]
  have h1 : (fun b => sg (FiniteAdeleRing (𝓞 F) F) c ((M *ᵥ y) b)) =
      M.map (sg (FiniteAdeleRing (𝓞 F) F) c) *ᵥ fun b => sg (FiniteAdeleRing (𝓞 F) F) c (y b) := by
    funext b
    exact RingHom.map_mulVec (sg (FiniteAdeleRing (𝓞 F) F) c).toRingHom M y b
  rw [h1, dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem sg_single (c : E ≃ₐ[F] E) (j : Fin n) :
    (fun b => sg (FiniteAdeleRing (𝓞 F) F) c ((Pi.single j (1 : RA F E) : Fin n → RA F E) b)) = Pi.single j 1 := by
  funext b
  by_cases h : b = j
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem mat_eq_of_dot (c : E ≃ₐ[F] E) {K K' : Matrix (Fin n) (Fin n) (RA F E)}
    (h : ∀ x y : Fin n → RA F E, x ⬝ᵥ (K *ᵥ fun b => sg (FiniteAdeleRing (𝓞 F) F) c (y b)) =
      x ⬝ᵥ (K' *ᵥ fun b => sg (FiniteAdeleRing (𝓞 F) F) c (y b))) : K = K' := by
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  rw [sg_single] at this
  simpa [Matrix.mulVec_single_one] using this

theorem gram_of_isUnA (c : E ≃ₐ[F] E) {g : Matrix (Fin n) (Fin n) (RA F E)} (hg : IsUnA c 1 g) :
    gᵀ * g.map (sg (FiniteAdeleRing (𝓞 F) F) c) = 1 := by
  have h := mat_eq_of_dot c (K := gᵀ * fm F 1 * g.map (sg (FiniteAdeleRing (𝓞 F) F) c)) (K' := fm F 1)
    fun x y => by rw [← hermA_mulVec, ← hermA_eq_dot]; exact hg x y
  rwa [GlobalTheory.UnRep.FullReps.fm_one, Matrix.mul_one] at h

end General

end GlobalTheory.UnitConjFrame

namespace GlobalTheory.UnitConjFrame

open GlobalTheory.AdLat GlobalTheory.UnRep

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem map_mul_sg (c : E ≃ₐ[F] E) (M N : Matrix (Fin n) (Fin n) (RA F E)) :
    (M * N).map (sg (FiniteAdeleRing (𝓞 F) F) c) =
      M.map (sg (FiniteAdeleRing (𝓞 F) F) c) * N.map (sg (FiniteAdeleRing (𝓞 F) F) c) :=
  Matrix.map_mul (f := (sg (FiniteAdeleRing (𝓞 F) F) c).toRingHom)

theorem map_mul_c (c : E ≃ₐ[F] E) (M N : Matrix (Fin n) (Fin n) E) :
    (M * N).map c = M.map c * N.map c :=
  Matrix.map_mul (f := (c : E →+* E))

theorem fm_transpose (A : Matrix (Fin n) (Fin n) E) : (fm F A)ᵀ = fm F Aᵀ := by
  ext i j; rfl

theorem isUnA_conj (c : E ≃ₐ[F] E) (A B G : Matrix (Fin n) (Fin n) E) (hAB : A * B = 1)
    (h : Aᵀ * Gᵀ * A.map c = 1) {g : Matrix (Fin n) (Fin n) (RA F E)} (hg : IsUnA c 1 g) :
    IsUnA c Gᵀ (fm F A * g * fm F B) := by
  have hg' := gram_of_isUnA c hg
  have hB : Bᵀ * B.map c = Gᵀ := by
    have e1 : Bᵀ * B.map c = Bᵀ * (Aᵀ * Gᵀ * A.map c) * B.map c := by rw [h, Matrix.mul_one]
    rw [e1, ← Matrix.transpose_transpose Gᵀ]
    have e2 : (A * B).map c = A.map c * B.map c := map_mul_c c A B
    rw [hAB, Matrix.map_one _ (map_zero c) (map_one c)] at e2
    calc Bᵀ * (Aᵀ * Gᵀᵀᵀ * A.map c) * B.map c = (A * B)ᵀ * Gᵀᵀᵀ * (A.map c * B.map c) := by
          rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = Gᵀᵀᵀ := by rw [hAB, ← e2, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  have hM : (fm F A * g * fm F B)ᵀ * fm F Gᵀ * (fm F A * g * fm F B).map (sg (FiniteAdeleRing (𝓞 F) F) c) =
      fm F Gᵀ := by
    rw [map_mul_sg, map_mul_sg, fm_map_sg, fm_map_sg, Matrix.transpose_mul, Matrix.transpose_mul,
      fm_transpose, fm_transpose]
    have e3 : fm F Aᵀ * fm F Gᵀ * fm F (A.map c) = 1 := by
      rw [← GlobalTheory.UnRep.FullReps.fm_mul, ← GlobalTheory.UnRep.FullReps.fm_mul, h, GlobalTheory.UnRep.FullReps.fm_one]
    calc _ = fm F Bᵀ * (gᵀ * (fm F Aᵀ * fm F Gᵀ * fm F (A.map c)) * g.map (sg (FiniteAdeleRing (𝓞 F) F) c)) *
            fm F (B.map c) := by simp only [Matrix.mul_assoc]
      _ = fm F Gᵀ := by
          rw [e3, Matrix.mul_one, hg', Matrix.mul_one, ← GlobalTheory.UnRep.FullReps.fm_mul, hB]
  intro x y
  rw [hermA_mulVec, hM, hermA_eq_dot]

end General

end GlobalTheory.UnitConjFrame

theorem GlobalTheory.UnitConjFrame.isUnA_frame_conj : ∀ (D : D7) (V : HSp D) (fr : GL (Fin V.rank) D.host.E) (g : Matrix (Fin V.rank) (Fin V.rank) (GlobalTheory.AdLat.RA D.host.F D.host.E)),
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * V.gram * fr.1 = 1 → GlobalTheory.UnRep.IsUnA (GlobalTheory.Member.cF D) 1 g →
    GlobalTheory.UnRep.IsUnA (GlobalTheory.Member.cF D) V.gramᵀ (GlobalTheory.UnRep.fm D.host.F fr.1 * g * GlobalTheory.UnRep.fm D.host.F (fr⁻¹).1) := by
  intro D V fr g hfr hg
  refine GlobalTheory.UnitConjFrame.isUnA_conj (GlobalTheory.Member.cF D) fr.1 (fr⁻¹).1 V.gram (Units.mul_inv fr) ?_ hg
  have h := congrArg Matrix.transpose hfr
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_one] at h
  rw [← h, Formalism.UG.cT, Matrix.transpose_transpose, Matrix.mul_assoc]
  rfl
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HatPullback

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem fm_mulVec_tmul (M : Matrix (Fin n) (Fin n) E) (a : FiniteAdeleRing (𝓞 F) F) (x : Fin n → E) :
    GlobalTheory.UnRep.fm F M *ᵥ (fun i => a ⊗ₜ[F] x i) = fun i => a ⊗ₜ[F] (M *ᵥ x) i := by
  funext i
  simp [GlobalTheory.UnRep.fm, Matrix.mulVec, dotProduct, TensorProduct.tmul_sum]

theorem fm_mul' (A B : Matrix (Fin n) (Fin n) E) :
    GlobalTheory.UnRep.fm F (A * B) = GlobalTheory.UnRep.fm F A * GlobalTheory.UnRep.fm F B :=
  Matrix.map_mul (f := (Algebra.TensorProduct.includeRight :
    E →ₐ[F] FiniteAdeleRing (𝓞 F) F ⊗[F] E).toRingHom)

theorem fm_one' : GlobalTheory.UnRep.fm F (1 : Matrix (Fin n) (Fin n) E) = 1 :=
  Matrix.map_one _ (by simp) rfl

theorem fm_mulVec_mem_hat (M : Matrix (Fin n) (Fin n) E) {L L' : Set (Fin n → E)}
    (h : ∀ x ∈ L, M *ᵥ x ∈ L') {w : Fin n → GlobalTheory.AdLat.RA F E} (hw : w ∈ GlobalTheory.AdLat.hat F L) :
    GlobalTheory.UnRep.fm F M *ᵥ w ∈ GlobalTheory.AdLat.hat F L' := by
  induction hw using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    rw [fm_mulVec_tmul]
    exact AddSubgroup.subset_closure ⟨a, ha, M *ᵥ x, h x hx, rfl⟩
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mulVec_neg]; exact neg_mem hx

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (A : GL (Fin n) E)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (w : Fin n → GlobalTheory.AdLat.RA F E),
    GlobalTheory.UnRep.fm F A.1 *ᵥ w ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)) ↔
      w ∈ GlobalTheory.AdLat.hat F ((Λ.comap ((Matrix.mulVecLin A.1).restrictScalars (𝓞 E)) : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) := by
  intro F E _ _ _ _ _ n A Λ w
  have hmem : ∀ x : Fin n → E, x ∈ ((Λ.comap ((Matrix.mulVecLin A.1).restrictScalars (𝓞 E)) :
      Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) ↔ A.1 *ᵥ x ∈ Λ := fun x => by
    simp [Matrix.mulVecLin_apply]
  constructor
  · intro hw
    have h2 := fm_mulVec_mem_hat (F := F) (A⁻¹).1
      (L := (Λ : Set (Fin n → E)))
      (L' := ((Λ.comap ((Matrix.mulVecLin A.1).restrictScalars (𝓞 E)) :
        Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)))
      (fun y hy => by
        rw [hmem, Matrix.mulVec_mulVec, A.mul_inv, Matrix.one_mulVec]
        exact hy) hw
    rwa [Matrix.mulVec_mulVec, ← fm_mul', A.inv_mul, fm_one', Matrix.one_mulVec] at h2
  · intro hw
    exact fm_mulVec_mem_hat (F := F) A.1 (fun x hx => (hmem x).1 hx) hw

end GlobalTheory.HatPullback
end
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

noncomputable section

namespace GlobalTheory.CuspRep

theorem norm_le_of_unip_variation : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ψ : Sm E a),
    IsCuspForm ψ → ∀ s : ℕ, 0 < s → s < a → ∀ (g : GA E a) (e : ℝ),
      (∀ x : BlockIx a s → Ad E, ‖ψ.1 (unip x * g) - ψ.1 g‖ ≤ e) → ‖ψ.1 g‖ ≤ e := by
  intro E _ _ _ a ψ hψ s hs0 hsa g e he
  letI : MeasurableSpace (BlockIx a s → Ad E) := borel _
  haveI : BorelSpace (BlockIx a s → Ad E) := ⟨rfl⟩
  set μ : Measure (BlockIx a s → Ad E) := Measure.addHaar with hμ
  obtain ⟨𝓕, h𝓕, h0, htop⟩ := GlobalTheory.T.exists_fundamentalDomain_rationalBlockUnipotentGL E a s μ
  have hc := ContAut.continuous_of_isOpen_stab E a ψ hψ.1.level
  have hI := CuspidalL2GL.integrableOn_unip hc hψ.1.left μ h𝓕 g
  have hz : ∫ x in 𝓕, ψ.1 (unip x * g) ∂μ = 0 := hψ.2 s hs0 hsa μ 𝓕 inferInstance h𝓕 g
  have key : ∫ x in 𝓕, (ψ.1 g - ψ.1 (unip x * g)) ∂μ = μ.real 𝓕 • ψ.1 g := by
    have h1 : IntegrableOn (fun _ => ψ.1 g) 𝓕 μ := integrableOn_const htop.ne
    rw [integral_sub h1 hI, hz, setIntegral_const, sub_zero]
  have hb : ‖∫ x in 𝓕, (ψ.1 g - ψ.1 (unip x * g)) ∂μ‖ ≤ e * μ.real 𝓕 :=
    norm_setIntegral_le_of_norm_le_const htop fun x _ => by rw [norm_sub_rev]; exact he x
  rw [key, norm_smul, Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg, mul_comm] at hb
  have hpos : 0 < μ.real 𝓕 := ENNReal.toReal_pos h0 htop.ne
  exact le_of_mul_le_mul_right hb hpos

end GlobalTheory.CuspRep
end
end

section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

noncomputable section
namespace GlobalTheory.SmoothConj
open GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem chart_conj (φ : GA E a → ℂ) (g : GA E a) :
    chart (fun x => starRingEnd ℂ (φ x)) g = Complex.conjCLE ∘ chart φ g := by
  funext x
  simp only [chart, Function.comp_apply]
  split_ifs <;> simp

theorem conj_mem (φ : Sm E a) : (fun x => starRingEnd ℂ (φ.1 x)) ∈ Sm E a := by
  have hφ : ∀ g, ContDiffOn ℝ (↑(⊤ : ℕ∞)) (chart φ.1 g) (invSet E a) := φ.2
  show ∀ g, ContDiffOn ℝ _ (chart (fun x => starRingEnd ℂ (φ.1 x)) g) (invSet E a)
  intro g
  rw [chart_conj]
  exact Complex.conjCLE.contDiff.comp_contDiffOn (hφ g)

def conjMap (φ : Sm E a) : Sm E a := ⟨fun x => starRingEnd ℂ (φ.1 x), conj_mem φ⟩

def conjEquiv : Sm E a ≃ₗ⋆[ℂ] Sm E a where
  toFun := conjMap
  invFun := conjMap
  map_add' x y := by apply Subtype.ext; funext g; simp [conjMap]
  map_smul' c x := by apply Subtype.ext; funext g; simp [conjMap]
  left_inv x := by apply Subtype.ext; funext g; simp [conjMap]
  right_inv x := by apply Subtype.ext; funext g; simp [conjMap]

theorem conjEquiv_act (o : Op E a) (φ : Sm E a) :
    act o (conjEquiv φ) = conjEquiv (act o φ) := by
  cases o with
  | fin k => rfl
  | cpt k => rfl
  | lie X =>
    apply Subtype.ext; funext g
    show lieD X (fun x => starRingEnd ℂ (φ.1 x)) g = starRingEnd ℂ (lieD X φ.1 g)
    simp only [lieD, chart_conj, ContinuousLinearEquiv.comp_fderiv]
    rfl

end GlobalTheory.SmoothConj

namespace GlobalTheory
open GlobalTheory.CuspRep

theorem smooth_conj_commutes_act : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ),
    ∃ C : Sm E a ≃ₗ⋆[ℂ] Sm E a, (∀ φ g, (C φ).1 g = starRingEnd ℂ (φ.1 g)) ∧
      ∀ o φ, act o (C φ) = C (act o φ) :=
  fun _ _ _ _ _ => ⟨SmoothConj.conjEquiv, fun _ _ => rfl, SmoothConj.conjEquiv_act⟩

end GlobalTheory
end
end

section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory.CuspRep.ConjZalg

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem map_qdet_semilinear {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (f : A →+* B) (σ : ℂ →+* ℂ)
    (hf : ∀ c, f (algebraMap ℂ A c) = algebraMap ℂ B (σ c)) (X : Fin a → Fin a → A) (u : ℂ) :
    f (Formalism.REAL.qdet X u) = Formalism.REAL.qdet (fun i j => f (X i j)) (σ u) := by

  simp only [Formalism.REAL.qdet, Formalism.REAL.qminor, map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn]
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 3
  funext k
  by_cases h : s k = k <;> simp [Formalism.REAL.Tm, h, map_add, hf, map_sub, map_natCast]

def conjBy (C : Sm E a ≃ₗ⋆[ℂ] Sm E a) : Module.End ℂ (Sm E a) →+* Module.End ℂ (Sm E a) where
  toFun z :=
    { toFun := fun φ => C.symm (z (C φ))
      map_add' := fun φ ψ => by simp
      map_smul' := fun c φ => by
        rw [LinearEquiv.map_smulₛₗ, LinearMap.map_smul, LinearEquiv.map_smulₛₗ]; simp }
  map_one' := LinearMap.ext fun φ => by simp
  map_mul' z w := LinearMap.ext fun φ => by simp
  map_zero' := LinearMap.ext fun φ => by simp
  map_add' z w := LinearMap.ext fun φ => by simp

theorem conjBy_apply (C : Sm E a ≃ₗ⋆[ℂ] Sm E a) (z : Module.End ℂ (Sm E a)) (φ : Sm E a) :
    conjBy C z φ = C.symm (z (C φ)) := rfl

theorem conjBy_algebraMap (C : Sm E a ≃ₗ⋆[ℂ] Sm E a) (c : ℂ) :
    conjBy C (algebraMap ℂ (Module.End ℂ (Sm E a)) c) = algebraMap ℂ _ (starRingEnd ℂ c) :=
  LinearMap.ext fun φ => by
    rw [conjBy_apply, Module.algebraMap_end_apply, Module.algebraMap_end_apply, LinearEquiv.map_smulₛₗ]; simp

theorem C_Eop (C : Sm E a ≃ₗ⋆[ℂ] Sm E a) (hC : ∀ o φ, act o (C φ) = C (act o φ)) (τ : E →+* ℂ) (i j : Fin a)
    (φ : Sm E a) : C (Eop τ i j φ) = Eop (ComplexEmbedding.conjugate τ) i j (C φ) := by
  have hl : ∀ x φ, C (lieS E a i j x φ) = lieS E a i j x (C φ) := fun x φ => (hC (Op.lie _) φ).symm
  have e : atEmb τ (-Complex.I) = -atEmb τ Complex.I := by
    rw [atEmb_eq]; simp
  simp only [Eop, LinearMap.smul_apply, LinearMap.sub_apply, map_smulₛₗ, map_sub, hl, atEmb_conj, map_one,
    Complex.conj_I, e, map_neg, LinearMap.neg_apply]
  have h2 : starRingEnd ℂ (1 / 2 : ℂ) = 1 / 2 := by simp [map_div₀, map_ofNat]
  rw [h2]
  congr 1
  simp [sub_eq_add_neg, neg_smul, smul_neg]

theorem conjBy_Eop (C : Sm E a ≃ₗ⋆[ℂ] Sm E a) (hC : ∀ o φ, act o (C φ) = C (act o φ)) (τ : E →+* ℂ) (i j : Fin a) :
    conjBy C (Eop τ i j) = Eop (ComplexEmbedding.conjugate τ) i j :=
  LinearMap.ext fun φ => by
    apply C.injective
    have hcc : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ :=
      RingHom.ext fun x => by simp [ComplexEmbedding.conjugate_coe_eq]
    rw [conjBy_apply, LinearEquiv.apply_symm_apply, C_Eop C hC, hcc]

theorem conjBy_cap (C : Sm E a ≃ₗ⋆[ℂ] Sm E a) (hC : ∀ o φ, act o (C φ) = C (act o φ)) (τ : E →+* ℂ) (u : ℂ) :
    conjBy C (cap τ u) = cap (ComplexEmbedding.conjugate τ) (starRingEnd ℂ u) := by
  rw [cap, map_qdet_semilinear (conjBy C) (starRingEnd ℂ) (conjBy_algebraMap C)]
  simp only [conjBy_Eop C hC, cap]
  congr 1
  simp [map_div₀, map_ofNat, map_sub, map_natCast]

theorem conjBy_mem_Zalg (C : Sm E a ≃ₗ⋆[ℂ] Sm E a) (hC : ∀ o φ, act o (C φ) = C (act o φ))
    {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) : conjBy C z ∈ Zalg E a := by
  let S : Subalgebra ℂ (Module.End ℂ (Sm E a)) :=
    { carrier := {z | conjBy C z ∈ Zalg E a}
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, map_mul] at *; exact Subalgebra.mul_mem _ hx hy
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, map_add (f := _)] at *; exact Subalgebra.add_mem _ hx hy
      algebraMap_mem' := fun c => by
        simp only [Set.mem_setOf_eq, conjBy_algebraMap]; exact Subalgebra.algebraMap_mem _ _ }
  refine (Algebra.adjoin_le (S := S) ?_) hz
  rintro _ ⟨τ, u, rfl⟩
  change conjBy C (cap τ u) ∈ Zalg E a
  rw [conjBy_cap C hC]
  exact Algebra.subset_adjoin ⟨_, _, rfl⟩

theorem conj_Zalg : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (C : Sm E a ≃ₗ⋆[ℂ] Sm E a),
    (∀ o φ, act o (C φ) = C (act o φ)) → ∀ z ∈ Zalg E a, ∃ z' ∈ Zalg E a, ∀ φ, z (C φ) = C (z' φ) := by
  intro E _ _ _ a C hC z hz
  exact ⟨conjBy C z, conjBy_mem_Zalg C hC hz, fun φ => by rw [conjBy_apply, LinearEquiv.apply_symm_apply]⟩

end GlobalTheory.CuspRep.ConjZalg
end

section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

noncomputable section

namespace GlobalTheory

theorem isCuspForm_of_conj_pointwise : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (C : Sm E a ≃ₗ⋆[ℂ] Sm E a), (∀ φ g, (C φ).1 g = starRingEnd ℂ (φ.1 g)) → (∀ o φ, act o (C φ) = C (act o φ)) → (∀ z ∈ Zalg E a, ∃ z' ∈ Zalg E a, ∀ φ, z (C φ) = C (z' φ)) → ∀ φ : Sm E a, IsCuspForm φ → IsCuspForm (C φ) := by
  intro E _ _ _ a C hC hact hZ φ hφ
  obtain ⟨h, hc⟩ := hφ
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro γ g
    rw [hC, hC, h.left]
  · convert h.level using 1
    ext k
    change act (.fin k) (C φ) = C φ ↔ act (.fin k) φ = φ
    rw [hact]
    exact C.injective.eq_iff
  · have := h.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)).map
      C.toLinearMap) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨k, rfl⟩, (hact (.cpt k) φ).symm⟩
  · have := h.zfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) ''
      Zalg E a)).map C.toLinearMap) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨z', h1, h2⟩ := hZ z hz
    exact ⟨_, Submodule.subset_span ⟨z', h1, rfl⟩, (h2 φ).symm⟩
  · intro g
    obtain ⟨K, N, h1⟩ := h.growth g
    refine ⟨K, N, fun y => ?_⟩
    rw [hC, RCLike.norm_conj]
    exact h1 y
  · intro r hr0 hra _ _ μ 𝓕 hμ h𝓕 g
    have := hc r hr0 hra μ 𝓕 hμ h𝓕 g
    simp_rw [hC]
    rw [integral_conj, this, map_zero]

end GlobalTheory
end
end
