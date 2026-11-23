module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique
public import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GodementSectionInvariantConvergent
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle294
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DetGramSmul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle299
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2066
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinIsotropicLine

@[expose] public section

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.SphEis.CoreIsom

theorem cT_add' {A : Type} [CommRing A] (s : A →+* A) {p q : ℕ} (X Y : Matrix (Fin p) (Fin q) A) :
    cT s (X + Y) = cT s X + cT s Y := by
  ext i k; simp [cT]

theorem unitary_core {A : Type} [CommRing A] (s : A →+* A) {n j m : ℕ} {J : Matrix (Fin n) (Fin n) A}
    {J₀ : Matrix (Fin m) (Fin m) A} {C : Matrix (Fin n) (Fin j) A} {Z : Matrix (Fin n) (Fin m) A}
    {G : Matrix (Fin n) (Fin n) A} {M : Matrix (Fin m) (Fin m) A} {b : Matrix (Fin j) (Fin m) A}
    (hG : cT s G * J * G = J) (hcz : cT s C * J * Z = 0) (hzc : cT s Z * J * C = 0)
    (hcc : cT s C * J * C = 0) (hzz : cT s Z * J * Z = J₀) (hGZ : G * Z = Z * M + C * b) :
    cT s M * J₀ * M = J₀ := by
  have e : cT s (G * Z) * J * (G * Z) = J₀ := by
    calc cT s (G * Z) * J * (G * Z) = cT s Z * (cT s G * J * G) * Z := by
          rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = J₀ := by rw [hG, hzz]
  rw [hGZ, cT_add', Formalism.UG.cT_mul, Formalism.UG.cT_mul] at e
  have h : (cT s M * cT s Z + cT s b * cT s C) * J * (Z * M + C * b) =
      cT s M * (cT s Z * J * Z) * M + cT s M * (cT s Z * J * C) * b +
        (cT s b * (cT s C * J * Z) * M + cT s b * (cT s C * J * C) * b) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]; abel
  rw [h, hzz, hzc, hcz, hcc] at e
  simpa using e

theorem isUnit_of_form {A : Type} [CommRing A] (s : A →+* A) {m : ℕ} {J₀ M : Matrix (Fin m) (Fin m) A}
    (h : cT s M * J₀ * M = J₀) (hJ : IsUnit J₀.det) : IsUnit M := by
  rw [Matrix.isUnit_iff_isUnit_det]
  have e := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul] at e
  rw [← e] at hJ
  exact isUnit_of_mul_isUnit_right hJ

end GlobalTheory.SphEis.CoreIsom


open GlobalTheory.SphEis.CoreIsom in
theorem GlobalTheory.SphEis.core_isom : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ g ∈ fixG σ J C, ∃ (g₀ : GAd σ J₀) (b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)), (matHom _ σ J g).1 * adMat F Z = adMat F Z * (matHom _ σ J₀ g₀).1 + adMat F C * b ∧ b = adMat F (cT (σ : E →+* E) D * J) * (matHom _ σ J g).1 * adMat F Z ∧ (matHom _ σ J₀ g₀).1 = adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) * (matHom _ σ J g).1 * adMat F Z ∧ (g ∈ ratPts σ J → g₀ ∈ ratPts σ J₀) := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF g hg
  have hmap : ∀ {a b c d : ℕ} (X : Matrix (Fin a) (Fin b) E) (Y : Matrix (Fin a) (Fin c) E)
      (W : Matrix (Fin c) (Fin d) E), cT (sigR (AF F) σ) (adMat F X) * adMat F Y * adMat F W =
        adMat F (cT (σ : E →+* E) X * Y * W) := by
    intro a b c d X Y W
    rw [adMat, adMat, adMat, GlobalTheory.AutFunCounterexample.cT_map_gen, ← Matrix.map_mul, ← Matrix.map_mul]
  have hgC : (matHom _ σ J g).1 * adMat F C = adMat F C := hg
  have hCJ : adMat F (cT (σ : E →+* E) C * J) * (matHom _ σ J g).1 = adMat F (cT (σ : E →+* E) C * J) := by
    have h1 : (matHom _ σ J g⁻¹).1 * adMat F C = adMat F C * (1 : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) := by
      rw [Matrix.mul_one]
      conv_lhs => rw [← hgC]
      rw [← Matrix.mul_assoc, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mul]
    have h2 := form_mul_of_mul_cols h1
    rwa [inv_inv, Formalism.UG.cT_one, Matrix.one_mul] at h2
  have hsum : adMat F C * adMat F (cT (σ : E →+* E) D * J) + adMat F Z * adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) +
      adMat F D * adMat F (cT (σ : E →+* E) C * J) = 1 := by
    simp only [adMat]
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add _),
      ← Matrix.map_add _ (map_add _), hF.sum, Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨M, hM⟩ : ∃ M, M = adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) * (matHom _ σ J g).1 * adMat F Z := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = adMat F (cT (σ : E →+* E) D * J) * (matHom _ σ J g).1 * adMat F Z := ⟨_, rfl⟩
  have hZ : (matHom _ σ J g).1 * adMat F Z = adMat F Z * M + adMat F C * b := by
    calc (matHom _ σ J g).1 * adMat F Z = (adMat F C * adMat F (cT (σ : E →+* E) D * J) +
          adMat F Z * adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) + adMat F D * adMat F (cT (σ : E →+* E) C * J)) *
          ((matHom _ σ J g).1 * adMat F Z) := by rw [hsum, Matrix.one_mul]
      _ = adMat F C * (adMat F (cT (σ : E →+* E) D * J) * (matHom _ σ J g).1 * adMat F Z) +
          adMat F Z * (adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) * (matHom _ σ J g).1 * adMat F Z) +
          adMat F D * (adMat F (cT (σ : E →+* E) C * J) * (matHom _ σ J g).1 * adMat F Z) := by
        simp only [Matrix.add_mul, Matrix.mul_assoc]
      _ = adMat F Z * M + adMat F C * b := by
        rw [hCJ, ← hM, ← hb]
        have h0 : adMat F (cT (σ : E →+* E) C * J) * adMat F Z = 0 := by
          simp only [adMat]; rw [← Matrix.map_mul, hF.cz]; simp
        rw [h0, Matrix.mul_zero, add_zero, add_comm]
  have hG : cT (sigR (AF F) σ) (matHom _ σ J g).1 * adMat F J * (matHom _ σ J g).1 = adMat F J := g.2
  have hMu : cT (sigR (AF F) σ) M * adMat F J₀ * M = adMat F J₀ :=
    unitary_core (sigR (AF F) σ) hG (by rw [hmap, hF.cz]; simp) (by rw [hmap, hF.zc]; simp)
      (by rw [hmap, hF.cc]; simp) (by rw [hmap, hF.zz]) hZ
  have hdet : IsUnit (adMat F J₀).det := by
    rw [adMat, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (Ne.isUnit hF.herm₀.2).map _
  have hMU := isUnit_of_form _ hMu hdet
  let g₀ : GAd σ J₀ := ⟨hMU.unit, by
    show cT (sigR (AF F) σ) (hMU.unit : Matrix (Fin m) (Fin m) (AF F ⊗[F] E)) * adMat F J₀ * hMU.unit = adMat F J₀
    rw [hMU.unit_spec]; exact hMu⟩
  have hg₀ : (matHom _ σ J₀ g₀).1 = M := hMU.unit_spec
  refine ⟨g₀, b, ?_, hb, ?_, ?_⟩
  · rw [hg₀]; exact hZ
  · rw [hg₀]; exact hM
  · intro hr
    have hr' : (show HR (AF F) σ J from g).1 ∈ (Formalism.UG.UJ (σ : E →+* E) J).map (bc (inclR (F := F) (AF F))) := hr
    obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.1 hr'
    have hGx : (matHom _ σ J g).1 = adMat F (x : Matrix (Fin n) (Fin n) E) := by
      exact (congrArg Units.val hxg).symm
    have hMM : M = adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J) * (x : Matrix (Fin n) (Fin n) E) * Z) := by
      rw [hM, hGx]; simp only [adMat, Matrix.map_mul]
    have inj : Function.Injective (inclR (F := F) (E := E) (AF F)) := fun a c h =>
      Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 F) F) h
    have hM₀ : cT (σ : E →+* E) (J₀⁻¹ * (cT (σ : E →+* E) Z * J) * (x : Matrix (Fin n) (Fin n) E) * Z) * J₀ *
        (J₀⁻¹ * (cT (σ : E →+* E) Z * J) * (x : Matrix (Fin n) (Fin n) E) * Z) = J₀ := by
      apply Matrix.map_injective inj
      show adMat F _ = adMat F _
      rw [← hmap, ← hMM]; exact hMu
    have hM₀U := isUnit_of_form _ hM₀ (Ne.isUnit hF.herm₀.2)
    show (show HR (AF F) σ J₀ from g₀).1 ∈ (Formalism.UG.UJ (σ : E →+* E) J₀).map (bc (inclR (F := F) (AF F)))
    refine Subgroup.mem_map.2 ⟨hM₀U.unit, ?_, Units.ext ?_⟩
    · show cT (σ : E →+* E) (hM₀U.unit : Matrix (Fin m) (Fin m) E) * J₀ * hM₀U.unit = J₀
      rw [hM₀U.unit_spec]; exact hM₀
    · show (hM₀U.unit : Matrix (Fin m) (Fin m) E).map (inclR (F := F) (AF F)) = (matHom _ σ J₀ g₀).1
      rw [hM₀U.unit_spec, hg₀, hMM]
end
end

section

noncomputable section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem continuous_of_frameCols : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ (X : Type) [TopologicalSpace X] (f : X → GAd σ J), Continuous (fun x => (matHom _ σ J (f x)).1 * adMat F C) → Continuous (fun x => (matHom _ σ J (f x)).1 * adMat F Z) → Continuous (fun x => (matHom _ σ J (f x)).1 * adMat F D) → Continuous f := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF X _ f hC hZ hD
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hs : adMat F C * adMat F (cT (σ : E →+* E) D * J) + adMat F Z * adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J))
      + adMat F D * adMat F (cT (σ : E →+* E) C * J) = 1 := by
    simp only [adMat, ← Matrix.map_mul]
    rw [← Matrix.map_add _ (map_add _), ← Matrix.map_add _ (map_add _), hF.sum]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hval : Continuous fun x => (matHom _ σ J (f x)).1 := by
    have e : ∀ x, (matHom _ σ J (f x)).1 = (matHom _ σ J (f x)).1 * adMat F C * adMat F (cT (σ : E →+* E) D * J)
        + (matHom _ σ J (f x)).1 * adMat F Z * adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J))
        + (matHom _ σ J (f x)).1 * adMat F D * adMat F (cT (σ : E →+* E) C * J) := by
      intro x
      rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_add, ← Matrix.mul_add, hs, Matrix.mul_one]
    refine Continuous.congr ?_ fun x => (e x).symm
    exact ((hC.matrix_mul continuous_const).add (hZ.matrix_mul continuous_const)).add (hD.matrix_mul continuous_const)
  have hcont : Continuous (adjA σ J) := (continuous_const.matrix_mul (continuous_id.matrix_map
      (GlobalTheory.AdelicUnitaryTop.continuous_sigR (AF F) σ)).matrix_transpose).matrix_mul continuous_const
  have hinv : Continuous fun x => ((matHom _ σ J (f x))⁻¹).1 := by
    have e : ∀ x, ((matHom _ σ J (f x))⁻¹).1 = adjA σ J (matHom _ σ J (f x)).1 := fun x => by
      rw [adjA_mat hF.herm, map_inv]
    exact (hcont.comp hval).congr fun x => (e x).symm
  exact (isEmbedding_matHom (AF F) σ J).continuous_iff.2 (Units.continuous_iff.2 ⟨hval, hinv⟩)

end GlobalTheory.SphEis
end
end

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.SphEis

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {j m : ℕ}
  {C D : Matrix (Fin n) (Fin j) E} {Z : Matrix (Fin n) (Fin m) E} {J₀ : Matrix (Fin m) (Fin m) E}

theorem Fr.invol (hF : Fr σ J C D Z J₀) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  exact τ.injective (by rw [hF.cm.2.2.2, hF.cm.2.2.2, star_star])

theorem Fr.isIsoCols (hF : Fr σ J C D Z J₀) : IsIsoCols σ J C := by
  refine ⟨Matrix.mulVec_injective_iff.1 ?_, hF.cc⟩
  intro v w h
  have := congrArg ((cT (σ : E →+* E) D * J) *ᵥ ·) h
  simpa only [Matrix.mulVec_mulVec, hF.dc, Matrix.one_mulVec] using this

theorem isClosed_fixG' {k : ℕ} (X : Matrix (Fin n) (Fin k) E) : IsClosed (fixG σ J X : Set (GAd σ J)) := by
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  have : T2Space (AF F ⊗[F] E) := GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension
  have hm : Continuous fun g : GAd σ J => (matHom _ σ J g).1 := Units.continuous_val.comp continuous_subtype_val
  exact isClosed_eq (hm.matrix_mul continuous_const) continuous_const

theorem unipRad_le_fixG' (X : Matrix (Fin n) (Fin j) E) : unipRad σ J X ≤ fixG σ J X := by
  rw [unipRad, Subgroup.closure_le]
  intro g hg
  obtain ⟨h, -, -⟩ := hg
  show _ * _ = _
  rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h
  exact h

theorem unipRad_onZ (hF : Fr σ J C D Z J₀) {g : GAd σ J} (hg : g ∈ unipRad σ J C) :
    ∃ b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E), (matHom _ σ J g).1 * adMat F Z = adMat F Z + adMat F C * b := by
  unfold unipRad at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨-, -, h3⟩ := hx
    choose a ha using fun k : Fin m => h3 (fun i => Z i k) (funext fun i => congrFun (congrFun hF.cz i) k)
    have e : ((matHom _ σ J x).1 - 1) * adMat F Z = adMat F C * Matrix.of fun i k => a k i :=
      Matrix.ext fun i k => congrFun (ha k) i
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_iff_eq_add'] at e
    exact ⟨_, e⟩
  | one => exact ⟨0, by simp⟩
  | mul x y hxm _ hx hy =>
    obtain ⟨b, hb⟩ := hx
    obtain ⟨b', hb'⟩ := hy
    have hxC : (matHom _ σ J x).1 * adMat F C = adMat F C := unipRad_le_fixG' (σ := σ) (J := J) C hxm
    refine ⟨b + b', ?_⟩
    rw [map_mul, Units.val_mul, Matrix.mul_assoc, hb', Matrix.mul_add, hb, ← Matrix.mul_assoc, hxC, Matrix.mul_add,
      add_assoc]
  | inv x hxm hx =>
    obtain ⟨b, hb⟩ := hx
    have hi : (matHom _ σ J x⁻¹).1 * (matHom _ σ J x).1 = 1 := Units.inv_mul x.1
    have hxC : (matHom _ σ J x⁻¹).1 * adMat F C = adMat F C :=
      unipRad_le_fixG' (σ := σ) (J := J) C (inv_mem (show x ∈ unipRad σ J C from hxm))
    have e : (matHom _ σ J x⁻¹).1 * ((matHom _ σ J x).1 * adMat F Z) = (matHom _ σ J x⁻¹).1 * (adMat F Z + adMat F C * b) :=
      congrArg _ hb
    rw [← Matrix.mul_assoc, hi, Matrix.one_mul, Matrix.mul_add, ← Matrix.mul_assoc, hxC] at e
    refine ⟨-b, ?_⟩
    rw [Matrix.mul_neg, ← sub_eq_add_neg]
    exact eq_sub_of_add_eq e.symm

theorem unipRad_inf_fixG (hF : Fr σ J C D Z J₀) (g : GAd σ J) (hu : g ∈ unipRad σ J C)
    (hg : g ∈ (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J))) : g = 1 := by
  obtain ⟨b, hb⟩ := unipRad_onZ hF hu
  have hC : (matHom _ σ J g).1 * adMat F C = adMat F C := hg.1
  have hD : (matHom _ σ J g).1 * adMat F D = adMat F D := hg.2
  have hD1 : (matHom _ σ J g).1 * adMat F D = adMat F D * (1 : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) := by rw [Matrix.mul_one]; exact hD
  have e := form_mul_of_mul_cols hD1
  rw [Formalism.UG.cT_one, Matrix.one_mul] at e
  have hi : (matHom _ σ J g⁻¹).1 * (matHom _ σ J g).1 = 1 := Units.inv_mul g.1
  have e2 : adMat F (cT (σ : E →+* E) D * J) * (matHom _ σ J g).1 = adMat F (cT (σ : E →+* E) D * J) := by
    conv_lhs => rw [← e, Matrix.mul_assoc, hi, Matrix.mul_one]
  have hb0 : b = 0 := by
    have h : adMat F (cT (σ : E →+* E) D * J) * ((matHom _ σ J g).1 * adMat F Z) =
        adMat F (cT (σ : E →+* E) D * J) * (adMat F Z + adMat F C * b) := congrArg _ hb
    have hdc : adMat F (cT (σ : E →+* E) D * J) * adMat F C = 1 := by
      rw [adMat, adMat, ← Matrix.map_mul, hF.dc, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [← Matrix.mul_assoc, e2, Matrix.mul_add, ← Matrix.mul_assoc, hdc, Matrix.one_mul] at h
    calc b = (adMat F (cT (σ : E →+* E) D * J) * adMat F Z + b) -
          adMat F (cT (σ : E →+* E) D * J) * adMat F Z := by abel
      _ = 0 := by rw [← h, sub_self]
  rw [hb0, Matrix.mul_zero, add_zero] at hb
  have key : ∀ h : GAd σ J, (matHom _ σ J h).1 =
      (matHom _ σ J h).1 * adMat F C * adMat F (cT (σ : E →+* E) D * J) +
      (matHom _ σ J h).1 * adMat F Z * adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) +
      (matHom _ σ J h).1 * adMat F D * adMat F (cT (σ : E →+* E) C * J) := by
    intro h
    have e : (matHom _ σ J h).1 = (matHom _ σ J h).1 * adMat F (C * (cT (σ : E →+* E) D * J) +
        Z * (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) + D * (cT (σ : E →+* E) C * J)) := by
      rw [hF.sum, adMat, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
    conv_lhs => rw [e]
    simp only [adMat, Matrix.map_add (inclR (F := F) (E := E) (AF F)) (map_add _), Matrix.map_mul, Matrix.mul_add,
      Matrix.mul_assoc]
  apply matHom_injective _ σ J
  apply Units.ext
  have k1 := key 1
  simp only [map_one, Units.val_one, Matrix.one_mul] at k1
  rw [key g, hC, hb, hD, map_one, Units.val_one]
  exact k1.symm

theorem frame_facts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → IsIsoCols σ J C ∧ IsClosed (fixG σ J C : Set (GAd σ J)) ∧ IsClosed ((fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J)) : Set (GAd σ J)) ∧ IsClosed (unipRad σ J C : Set (GAd σ J)) ∧ unipRad σ J C ≤ fixG σ J C ∧ fixG σ J C ≤ parFlag σ J C (fun _ => 0) ∧ (∀ g ∈ unipRad σ J C, g ∈ (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J)) → g = 1) ∧ (∀ p ∈ parFlag σ J C (fun _ => 0), ∀ u, u ∈ unipRad σ J C ↔ p * u * p⁻¹ ∈ unipRad σ J C) ∧ ∀ (p : GAd σ J) (β : GL (Fin j) (AF F ⊗[F] E)), (matHom _ σ J p).1 * adMat F C = adMat F C * β.1 → p ∈ parFlag σ J C (fun _ => 0) := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF
  have hJ := hF.herm
  have hσ := hF.invol
  have hIC := hF.isIsoCols
  refine ⟨hIC, isClosed_fixG' C, ?_, ?_, unipRad_le_fixG' C, ?_, unipRad_inf_fixG hF, ?_, ?_⟩
  · rw [Subgroup.coe_inf]; exact (isClosed_fixG' C).inter (isClosed_fixG' D)
  · rw [← unipFlag_const C 0]; exact isClosed_unipFlag hJ hσ hIC _
  · intro g hg
    have hg' : g⁻¹ ∈ fixG σ J C := inv_mem hg
    refine ⟨⟨1, fun _ _ h => absurd h (lt_irrefl 0), ?_⟩, 1, fun _ _ h => absurd h (lt_irrefl 0), ?_⟩
    · rw [Matrix.mul_one]; exact hg
    · rw [Matrix.mul_one]; exact hg'
  · intro p hp u
    rw [← unipFlag_const C 0]
    exact ⟨fun hu => conj_mem_unipFlag hJ hσ hIC _ hp hu, fun hu => by
      have := conj_mem_unipFlag hJ hσ hIC _ (inv_mem hp) hu
      simpa [mul_assoc] using this⟩
  · intro p β h
    have hi : (matHom _ σ J p⁻¹).1 * (matHom _ σ J p).1 = 1 := Units.inv_mul p.1
    have hb : β.1 * (β⁻¹).1 = 1 := Units.mul_inv β
    refine ⟨⟨β.1, fun _ _ h => absurd h (lt_irrefl 0), h⟩, (β⁻¹).1, fun _ _ h => absurd h (lt_irrefl 0), ?_⟩
    calc (matHom _ σ J p⁻¹).1 * adMat F C = (matHom _ σ J p⁻¹).1 * (adMat F C * (β.1 * (β⁻¹).1)) := by
          rw [hb, Matrix.mul_one]
      _ = (matHom _ σ J p⁻¹).1 * (matHom _ σ J p).1 * adMat F C * (β⁻¹).1 := by
          rw [← Matrix.mul_assoc (adMat F C), ← h]; simp only [Matrix.mul_assoc]
      _ = adMat F C * (β⁻¹).1 := by rw [hi, Matrix.one_mul]

end GlobalTheory.SphEis

end
end

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.SphEis

theorem exists_bound_exponents : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv → ∀ W : Set (GAd σ J), IsCompact W → ∃ m₀ : ℕ, ∀ q ∈ fixG σ J C, ∀ l : Fin j → ℤ, ∀ w ∈ W, q * lv (tor F E l) * w ∈ ratPts σ J → ∀ i, -(m₀ : ℤ) ≤ l i := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF lv hlv W hW
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  set P : Matrix (Fin j) (Fin n) (AF F ⊗[F] E) := adMat F (cT (σ : E →+* E) C * J) with hP
  have hq : ∀ q ∈ fixG σ J C, P * (matHom _ σ J q).1 = P := by
    intro q hq
    have h1 : (matHom _ σ J q⁻¹).1 * adMat F C = adMat F C * (1 : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) := by
      rw [Matrix.mul_one]; exact inv_mem hq
    have h := form_mul_of_mul_cols h1
    rwa [inv_inv, Formalism.UG.cT_one, Matrix.one_mul] at h
  have hl : ∀ α, P * (matHom _ σ J (lv α)).1 = cT (sigR (AF F) σ) (α⁻¹).1 * P := by
    intro α
    have h := form_mul_of_mul_cols (hlv.onC α⁻¹)
    rwa [map_inv lv α, inv_inv] at h
  have hc : Continuous fun w : GAd σ J => P * (matHom _ σ J w).1 :=
    continuous_const.matrix_mul (Units.continuous_val.comp (isEmbedding_matHom (AF F) σ J).continuous)
  have hb : GlobalTheory.Eis.Conv.Bdd fun w : W => (w : GAd σ J) := ⟨W, hW, fun w => w.2⟩
  obtain ⟨Ω, hΩ, hΩw⟩ := GlobalTheory.Eis.Conv.Bdd.entries (GlobalTheory.Eis.Conv.Bdd.map hb hc)
  obtain ⟨m₀, hm₀⟩ := (GlobalTheory.T.compact_adeles_rational_points_finite_eventually_zero F E Ω hΩ).2
  refine ⟨m₀, fun q hqm l w hw hg i => ?_⟩
  have ht : cT (sigR (AF F) σ) (tor F E l)⁻¹.1 = (tor F E l)⁻¹.1 :=
    congrArg Units.val (GlobalTheory.Eis.Conv.cti_dg (GlobalTheory.Eis.Conv.sigR_halfE σ) l)
  have h1 : P * (matHom _ σ J (q * lv (tor F E l) * w)).1 = (tor F E l)⁻¹.1 * (P * (matHom _ σ J w).1) := by
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hq q hqm, hl, ht,
      Matrix.mul_assoc]
  generalize q * lv (tor F E l) * w = g at hg h1
  have hg' : matHom _ σ J g ∈ HFin (AF F) σ J := Subgroup.mem_subgroupOf.1 hg
  obtain ⟨γ, -, e⟩ := Subgroup.mem_map.1 hg'
  have hm : (matHom _ σ J g).1 = γ.1.map (inclR (F := F) (AF F)) := by
    rw [← e]; rfl
  have hy : (cT (σ : E →+* E) C * J * γ.1).map (inclR (F := F) (AF F)) = P * (matHom _ σ J g).1 := by
    rw [hm, Matrix.map_mul]
  have hrow : ¬∀ x, (cT (σ : E →+* E) C * J * γ.1) i x = 0 :=
    GlobalTheory.GodementSectionReduction.row_ne_zero (N := γ⁻¹.1 * D) (by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc γ.1, Units.mul_inv, Matrix.one_mul, hF.cd]) i
  have hrow' : ¬∀ x, (cT (σ : E →+* E) C * J * γ.1).map (inclR (F := F) (AF F)) i x = 0 := fun h =>
    hrow fun x => by
      have := h x
      rwa [Matrix.map_apply, map_eq_zero_iff _ GlobalTheory.AutFunCompare.inclA_injective] at this
  exact GlobalTheory.GodementSectionReduction.bound_aux (inclR (F := F) (AF F)) hm₀ (fun i x => hΩw ⟨w, hw⟩ i x) (hy.trans h1) i hrow'

end GlobalTheory.SphEis

end
end

section

noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem reduce_gl_cm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (hc : IsCMExt F E σ) (j : ℕ) : ∃ (L : Set (GL (Fin j) (AF F ⊗[F] E))) (B : ℝ), IsCompact L ∧
    ∀ α : GL (Fin j) (AF F ⊗[F] E), ∃ (δ : GL (Fin j) E) (l : Fin j → ℤ), ∃ c ∈ L,
      bc (inclR (F := F) (AF F)) δ * α = tor F E l * c ∧
      (absE F E (Matrix.GeneralLinearGroup.det α) : ℝ) ≤ B * ∏ i, (bse F ^ l i)⁻¹ :=
  haveI := GlobalTheory.Doubling.t2Space_adeleRing' (F := F)
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  haveI := GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension (F := F) (E := E) (R := AF F)
  GlobalTheory.GodementSectionReduction.reduction_GL_diagonalUnitPowers_compact (inclR (F := F) (AF F)) GlobalTheory.Doubling.continuous_absE
    (fun u => GlobalTheory.Doubling.absE_inclR u) (by positivity)
    (by rw [GlobalTheory.T.tensorIdeleNormalizedAbs_ideleHalfAtInfinity _ _ _ hc]; simp) (GlobalTheory.Eis.Conv.red_gl _ _ _ hc j)

theorem reduce_levi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv → ∃ (W : Set (GAd σ J)) (B : ℝ), IsCompact W ∧ ∀ (p : GAd σ J) (β : GL (Fin j) (AF F ⊗[F] E)), (matHom _ σ J p).1 * adMat F C = adMat F C * β.1 → ∃ γ ∈ ratPts σ J, γ ∈ parFlag σ J C (fun _ => 0) ∧ ∃ q ∈ fixG σ J C, ∃ l : Fin j → ℤ, ∃ w ∈ W, γ * p = q * lv (tor F E l) * w ∧ (absE F E (Matrix.GeneralLinearGroup.det β) : ℝ) ≤ B * ∏ i, (bse F ^ l i)⁻¹ := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF lv hl
  obtain ⟨L, B, hL, hR⟩ := reduce_gl_cm hF.cm j
  refine ⟨lv '' L, B, hL.image hl.cont, fun p β hp => ?_⟩
  obtain ⟨δ, l, c, hc, hred, hle⟩ := hR β
  have h1 := hl.rat δ
  generalize bc (inclR (F := F) (AF F)) δ = u at h1 hred
  refine ⟨lv u, h1, ⟨⟨u.1, fun _ _ h => absurd h (lt_irrefl _), hl.onC u⟩,
    (u⁻¹).1, fun _ _ h => absurd h (lt_irrefl _), by rw [← map_inv]; exact hl.onC u⁻¹⟩,
    lv u * p * lv (u * β)⁻¹, ?_, l, lv c, ⟨c, hc, rfl⟩, ?_, hle⟩
  · change _ * _ = _
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_assoc, hl.onC, ← Matrix.mul_assoc,
      Matrix.mul_assoc _ _ (adMat F C), hp, ← Matrix.mul_assoc, hl.onC, Matrix.mul_assoc, Matrix.mul_assoc,
      ← Matrix.mul_assoc u.1, ← Units.val_mul, Units.mul_inv, Matrix.mul_one]
  · rw [mul_assoc _ (lv _) (lv c), ← map_mul, ← hred, map_inv, inv_mul_cancel_right]

end GlobalTheory.SphEis

end
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagCell2.GenericCell

theorem upM_zero_eq {ι : Type} {m : ι → ℕ} {K : Type} [Field K] : upM (0 : Cell m → K) = 1 := by
  funext τ
  ext a b
  simp only [upM, upU, Matrix.of_apply, Pi.zero_apply, Pi.one_apply, Matrix.one_apply]
  split_ifs <;> simp_all

theorem exists_inCell_genericPoint : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ (z : X.X) (A : Mat m X.Fn), A ∈ E.S z → ∃ u : Cell m → Y.Fn, InCell E E' φ f A u (genericPoint Y.X) := by
  intro F _ X Y ι _ m E E' φ f hR z A hA
  have hgX : A ∈ E.S (genericPoint X.X) := Fr.mem_genericPoint hA
  have hcp : (ratOf X).pt (IsLocalRing.closedPoint X.Fn) = genericPoint X.X := Scheme.fromSpecStalk_closedPoint
  obtain ⟨p, ⟨hpf, hpb⟩, -⟩ := hR.lifts X.Fn (ratOf X).pt A (hcp ▸ hgX) (upM 0) (by rw [upM_zero_eq]; exact Par.one)
  have hfp : f (p (IsLocalRing.closedPoint X.Fn)) = genericPoint X.X := by
    have h1 := congrArg (fun g : Sp X.Fn ⟶ X.X => g (IsLocalRing.closedPoint X.Fn)) hpf
    simp only [Scheme.Hom.comp_apply] at h1
    exact h1.trans hcp
  obtain ⟨u, hu, -⟩ := (GlobalTheory.T.bearsFlag_unitriangular_iff_mem_cell F X Y ι m E E' φ f hR A X.Fn p (hfp ▸ hgX) 0).1 hpb
  refine ⟨u, Fr.mem_of_specializes (hfp ▸ hgX) ((genericPoint_specializes _).map f.continuous), Fr.mem_genericPoint hu⟩

end GlobalTheory.FlagCell2.GenericCell
end
