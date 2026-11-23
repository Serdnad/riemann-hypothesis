module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle379
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle381
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelOfDualParameter
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle099
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle006
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.AdelicU GlobalTheory.Cusp
open scoped Matrix TensorProduct

noncomputable section

namespace GlobalTheory.SplitFlag

open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (perp extSub coordR act parab)

theorem exists_mulVec_eq_of_maps {K : Type} [Field K] {n : ℕ} (M : GL (Fin n) K) (S : Submodule K (Fin n → K))
    (hS : ∀ u ∈ S, (M : Matrix (Fin n) (Fin n) K) *ᵥ u ∈ S) :
    ∀ u ∈ S, ∃ u₀ ∈ S, (M : Matrix (Fin n) (Fin n) K) *ᵥ u₀ = u := by
  intro u hu
  let f : S →ₗ[K] S := (M : Matrix (Fin n) (Fin n) K).mulVecLin.restrict hS
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have e : (M : Matrix (Fin n) (Fin n) K) *ᵥ (a : Fin n → K) = (M : Matrix (Fin n) (Fin n) K) *ᵥ (b : Fin n → K) :=
      congrArg Subtype.val hab
    have e2 := congrArg (fun x => ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x) e
    simpa only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] using e2
  obtain ⟨a, ha⟩ := LinearMap.injective_iff_surjective.1 hinj ⟨u, hu⟩
  exact ⟨a.1, a.2, congrArg Subtype.val ha⟩

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {V : Formalism.BasicNotions.HSpace E} {v : HeightOneSpectrum (𝓞 F)}

theorem splitHom_mulVec_mem_wPart (hc : Formalism.BasicNotions.CMData F E) (τ : E →ₐ[F] Fv F v) {W : Submodule E V.V}
    {g : GlobalTheory.AdelicU.GLoc hc.sig V.gram v} (hg : g ∈ parab hc V (Fv F v) W) {u : Fin V.rank → Fv F v}
    (hu : u ∈ wPart τ W) :
    ((GlobalTheory.AdelicU.splitHom hc.sig V.gram τ g : GL (Fin V.rank) (Fv F v)) : Matrix (Fin V.rank) (Fin V.rank) (Fv F v)) *ᵥ u
      ∈ wPart τ W := by
  obtain ⟨y, hy, rfl⟩ := hu
  exact ⟨act hc V g y, mem_parab_iff_maps.1 hg y hy, splitVec_matHom_mulVec τ g y⟩

theorem flagChain_eq_X (𝔉 : GlobalTheory.Cusp.IsoFlag V) (τ : E →ₐ[F] Fv F v) (i : Fin (𝔉.k + 1)) :
    flagChain 𝔉 τ ⟨i, by omega⟩ = wPart τ (𝔉.X i) := by
  rw [flagChain_of_le 𝔉 τ (show (i : ℕ) ≤ 𝔉.k by omega)]

theorem flagChain_eq_perp (𝔉 : GlobalTheory.Cusp.IsoFlag V) (τ : E →ₐ[F] Fv F v) (i : Fin (𝔉.k + 1)) :
    flagChain 𝔉 τ ⟨2 * 𝔉.k + 1 - i, by omega⟩ = wPart τ (perp V (𝔉.X i)) := by
  rw [flagChain_of_lt 𝔉 τ (show 𝔉.k < 2 * 𝔉.k + 1 - (i : ℕ) by omega)]
  congr 3
  ext
  simp only
  omega

theorem mem_par_iff_flagChain : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    {V : Formalism.BasicNotions.HSpace E} {v : HeightOneSpectrum (𝓞 F)} (hc : Formalism.BasicNotions.CMData F E), IsCMExt F E hc.sig →
    IsHermND hc.sig V.gram → ∀ (τ : E →ₐ[F] Fv F v) (𝔉 : GlobalTheory.Cusp.IsoFlag V) (g : GlobalTheory.AdelicU.GLoc hc.sig V.gram v),
    g ∈ 𝔉.par hc (Fv F v) ↔ ∀ j, ∀ u ∈ GlobalTheory.SplitFlag.flagChain 𝔉 τ j,
      ((GlobalTheory.AdelicU.splitHom hc.sig V.gram τ g : GL (Fin V.rank) (Fv F v)) : Matrix (Fin V.rank) (Fin V.rank) (Fv F v)) *ᵥ u ∈
        GlobalTheory.SplitFlag.flagChain 𝔉 τ j := by
  intro F E _ _ _ _ _ _ V v hc h hJ τ 𝔉 g
  constructor
  · intro hg j u hu
    rcases le_or_gt (j : ℕ) 𝔉.k with hj | hj
    · rw [flagChain_of_le 𝔉 τ hj] at hu ⊢
      exact splitHom_mulVec_mem_wPart hc τ (Subgroup.mem_iInf.1 hg _) hu
    · rw [flagChain_of_lt 𝔉 τ hj] at hu ⊢
      exact splitHom_mulVec_mem_wPart hc τ (parab_le_perp (Subgroup.mem_iInf.1 hg _)) hu
  · intro H
    refine Subgroup.mem_iInf.2 fun i => mem_parab_iff_maps.2 fun y hy => ?_
    have H1 := H ⟨i, by omega⟩
    rw [flagChain_eq_X] at H1
    have H2 := H ⟨2 * 𝔉.k + 1 - i, by omega⟩
    rw [flagChain_eq_perp] at H2
    have key : ∀ τ' : E →ₐ[F] Fv F v, splitVec τ' (act hc V g y) =
        ((GlobalTheory.AdelicU.splitHom hc.sig V.gram τ' g : GL (Fin V.rank) (Fv F v)) : Matrix (Fin V.rank) (Fin V.rank) (Fv F v))
          *ᵥ splitVec τ' y := fun τ' => splitVec_matHom_mulVec τ' g y
    rw [mem_extSub_iff_split hc h τ] at hy ⊢
    obtain ⟨hy1, hy2⟩ := hy
    refine ⟨?_, ?_⟩
    · rw [key]
      exact H1 _ hy1
    · rw [key, mem_wPart_comp_iff hc h hJ τ]
      intro u hu
      obtain ⟨u₀, hu₀, rfl⟩ := exists_mulVec_eq_of_maps _ _ H2 u hu
      rw [pairing_splitHom]
      exact (mem_wPart_comp_iff hc h hJ τ).1 hy2 u₀ hu₀

end GlobalTheory.SplitFlag
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PackLoc

lemma inUJ_mul' {n : ℕ} {ε : Fin n → Bool} {a b : Matrix (Fin n) (Fin n) ℂ}
    (ha : a ∈ Formalism.MainNotions.S.UJset ε) (hb : b ∈ Formalism.MainNotions.S.UJset ε) : a * b ∈ Formalism.MainNotions.S.UJset ε := by
  have ha' : aᴴ * Formalism.REAL.Jm ε * a = Formalism.REAL.Jm ε := ha
  have hb' : bᴴ * Formalism.REAL.Jm ε * b = Formalism.REAL.Jm ε := hb
  show (a * b)ᴴ * Formalism.REAL.Jm ε * (a * b) = Formalism.REAL.Jm ε
  rw [conjTranspose_mul]
  calc bᴴ * aᴴ * Formalism.REAL.Jm ε * (a * b) = bᴴ * (aᴴ * Formalism.REAL.Jm ε * a) * b := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [ha', hb']

theorem mco_frame : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau)
  (B g₀' : Matrix (Fin V.rank) (Fin V.rank) ℂ) (v₀ : M.H τ),
  IsUnit B → Bᴴ * Formalism.REAL.Jm (M.ε τ) * B = gramAt D V τ → g₀' ∈ Formalism.MainNotions.S.UJset (M.ε τ) →
  B⁻¹ * g₀' * M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) ∧
  ∀ x ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), GlobalTheory.PackLoc.mco M τ (B⁻¹ * g₀' * M.fr τ) v₀ x =
    ⟪M.σ τ g₀' v₀, M.σ τ (B * x * B⁻¹) (M.σ τ g₀' v₀)⟫_ℂ := by
  intro D V S M τ B g v₀ hB hBg hg
  set F := M.fr τ with hFdef
  set J := Formalism.REAL.Jm (M.ε τ) with hJdef
  set G := gramAt D V τ with hGdef
  have hFd : IsUnit F.det := (Matrix.isUnit_iff_isUnit_det F).mp (M.fr_unit τ)
  have hBd : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).mp hB
  have hFg : Fᴴ * J * F = G := M.fr_gram τ
  have hg' : gᴴ * J * g = J := hg
  have hBH : (B⁻¹)ᴴ * Bᴴ = 1 := by
    rw [← conjTranspose_mul, Matrix.mul_nonsing_inv B hBd, conjTranspose_one]
  have hFH : (F⁻¹)ᴴ * Fᴴ = 1 := by
    rw [← conjTranspose_mul, Matrix.mul_nonsing_inv F hFd, conjTranspose_one]
  have hBinv : (B⁻¹)ᴴ * G * B⁻¹ = J := by
    rw [← hBg]
    calc (B⁻¹)ᴴ * (Bᴴ * J * B) * B⁻¹ = ((B⁻¹)ᴴ * Bᴴ) * J * (B * B⁻¹) := by simp only [Matrix.mul_assoc]
      _ = J := by rw [hBH, Matrix.mul_nonsing_inv B hBd]; simp
  have hFinv : (F⁻¹)ᴴ * G * F⁻¹ = J := by
    rw [← hFg]
    calc (F⁻¹)ᴴ * (Fᴴ * J * F) * F⁻¹ = ((F⁻¹)ᴴ * Fᴴ) * J * (F * F⁻¹) := by simp only [Matrix.mul_assoc]
      _ = J := by rw [hFH, Matrix.mul_nonsing_inv F hFd]; simp
  refine ⟨?_, ?_⟩
  · show (B⁻¹ * g * F)ᴴ * G * (B⁻¹ * g * F) = G
    rw [conjTranspose_mul, conjTranspose_mul]
    calc Fᴴ * (gᴴ * (B⁻¹)ᴴ) * G * (B⁻¹ * g * F) = Fᴴ * (gᴴ * ((B⁻¹)ᴴ * G * B⁻¹) * g) * F := by
          simp only [Matrix.mul_assoc]
      _ = G := by rw [hBinv, hg', hFg]
  · intro x hx
    have hx' : xᴴ * G * x = G := hx
    obtain ⟨⟨_, hmul⟩, hiso, _⟩ := (M.ds τ).2.2.1
    have hk : F * B⁻¹ ∈ Formalism.MainNotions.S.UJset (M.ε τ) := by
      show (F * B⁻¹)ᴴ * J * (F * B⁻¹) = J
      rw [conjTranspose_mul]
      calc (B⁻¹)ᴴ * Fᴴ * J * (F * B⁻¹) = (B⁻¹)ᴴ * (Fᴴ * J * F) * B⁻¹ := by simp only [Matrix.mul_assoc]
        _ = J := by rw [hFg, hBinv]
    have hy : B * x * B⁻¹ ∈ Formalism.MainNotions.S.UJset (M.ε τ) := by
      show (B * x * B⁻¹)ᴴ * J * (B * x * B⁻¹) = J
      rw [conjTranspose_mul, conjTranspose_mul]
      calc (B⁻¹)ᴴ * (xᴴ * Bᴴ) * J * (B * x * B⁻¹) = (B⁻¹)ᴴ * (xᴴ * (Bᴴ * J * B) * x) * B⁻¹ := by
            simp only [Matrix.mul_assoc]
        _ = J := by rw [hBg, hx', hBinv]
    have hz : F * x * F⁻¹ ∈ Formalism.MainNotions.S.UJset (M.ε τ) := by
      show (F * x * F⁻¹)ᴴ * J * (F * x * F⁻¹) = J
      rw [conjTranspose_mul, conjTranspose_mul]
      calc (F⁻¹)ᴴ * (xᴴ * Fᴴ) * J * (F * x * F⁻¹) = (F⁻¹)ᴴ * (xᴴ * (Fᴴ * J * F) * x) * F⁻¹ := by
            simp only [Matrix.mul_assoc]
        _ = J := by rw [hFg, hx', hFinv]
    have e1 : F * (B⁻¹ * g * F) * F⁻¹ = F * B⁻¹ * g := by
      simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv F hFd, Matrix.mul_one]
    have e2 : F * x * F⁻¹ * (F * B⁻¹ * g) = F * B⁻¹ * (B * x * B⁻¹ * g) := by
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left F _ hFd,
        Matrix.nonsing_inv_mul_cancel_left B _ hBd]
    have hkg := inUJ_mul' hk hg
    have hyg := inUJ_mul' hy hg
    unfold mco DSModel.rep
    rw [← hFdef, e1, ← ContinuousLinearMap.comp_apply, ← hmul _ hz _ hkg, e2,
      hmul _ hk _ hyg, hmul _ hk _ hg, hmul _ hy _ hg]
    simp only [ContinuousLinearMap.comp_apply]
    let L : M.H τ →ₗᵢ[ℂ] M.H τ := ⟨(M.σ τ (F * B⁻¹)).toLinearMap, hiso _ hk⟩
    exact L.inner_map_map _ _

end GlobalTheory.PackLoc
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PackLocFacts

variable {n : ℕ}

theorem conj_mem_lie {F J G X : Matrix (Fin n) (Fin n) ℂ} (hF : IsUnit F) (hG : Fᴴ * J * F = G)
    (hX : Xᴴ * G + G * X = 0) : (F * X * F⁻¹)ᴴ * J + J * (F * X * F⁻¹) = 0 := by
  have hd : IsUnit F.det := (Matrix.isUnit_iff_isUnit_det F).1 hF
  have h1 : F * F⁻¹ = 1 := Matrix.mul_nonsing_inv F hd
  have h2 : (F⁻¹)ᴴ * Fᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  have e : (F * X * F⁻¹)ᴴ * J + J * (F * X * F⁻¹) = (F⁻¹)ᴴ * (Xᴴ * G + G * X) * F⁻¹ := by
    rw [← hG]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    congr 1
    · rw [h1, Matrix.mul_one]
    · rw [← Matrix.mul_assoc (F⁻¹)ᴴ Fᴴ, h2, Matrix.one_mul]
  rw [e, hX, Matrix.mul_zero, Matrix.zero_mul]

theorem ofFr_mem_UH {F J G g : Matrix (Fin n) (Fin n) ℂ} (hF : IsUnit F) (hG : Fᴴ * J * F = G)
    (hg : gᴴ * J * g = J) : F⁻¹ * g * F ∈ Formalism.QuantumDeterminants.UH G := by
  have hd : IsUnit F.det := (Matrix.isUnit_iff_isUnit_det F).1 hF
  have h1 : F * F⁻¹ = 1 := Matrix.mul_nonsing_inv F hd
  have h2 : (F⁻¹)ᴴ * Fᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  simp only [Formalism.QuantumDeterminants.UH, Set.mem_setOf_eq]
  rw [← hG]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (F⁻¹)ᴴ Fᴴ, h2, Matrix.one_mul, ← Matrix.mul_assoc F F⁻¹, h1, Matrix.one_mul,
    ← Matrix.mul_assoc J g F, ← Matrix.mul_assoc gᴴ (J * g) F, ← Matrix.mul_assoc gᴴ J g, hg]

theorem rev_conj (F g : Matrix (Fin n) (Fin n) ℂ) :
    F.submatrix Fin.revPerm (Equiv.refl _) * g * (F.submatrix Fin.revPerm (Equiv.refl _))⁻¹ =
      GlobalTheory.ConjDS.rv (F * g * F⁻¹) := by
  rw [Matrix.inv_submatrix_equiv]
  ext i j
  simp [GlobalTheory.ConjDS.rv, Matrix.mul_apply]

theorem frame_facts : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (Y : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel Y S) (τ : D.what₂.Tau),
  (∀ u : Formalism.REAL.UJ (M.ε τ), GlobalTheory.PackLoc.ptY M τ u ∈ Formalism.QuantumDeterminants.UH (gramAt D Y τ) ∧
    (GlobalTheory.ConjDS.conjModel M).fr τ * GlobalTheory.PackLoc.ptY M τ u * ((GlobalTheory.ConjDS.conjModel M).fr τ)⁻¹ =
      GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u) ∧
    M.rep τ (GlobalTheory.PackLoc.ptY M τ u) = M.σ τ (Formalism.MainNotions.S.umat u)) ∧
  ∀ X ∈ lieAt Y τ,
    (GlobalTheory.ConjDS.conjModel M).fr τ * X * ((GlobalTheory.ConjDS.conjModel M).fr τ)⁻¹ ∈
      GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ((GlobalTheory.ConjDS.conjModel M).ε τ)) ∧
    ∀ s : ℝ, cmp θ τ (oneP θ Y τ X s) ∈ Formalism.QuantumDeterminants.UH (gramAt D Y τ) ∧
      (GlobalTheory.ConjDS.conjModel M).fr τ * cmp θ τ (oneP θ Y τ X s) * ((GlobalTheory.ConjDS.conjModel M).fr τ)⁻¹ =
        NormedSpace.exp (s • ((GlobalTheory.ConjDS.conjModel M).fr τ * X * ((GlobalTheory.ConjDS.conjModel M).fr τ)⁻¹)) := by
  intro D θ hθ Y S M τ
  have hF : IsUnit (M.fr τ) := M.fr_unit τ
  have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 hF
  have hA : ∀ g, (GlobalTheory.ConjDS.conjModel M).fr τ * g * ((GlobalTheory.ConjDS.conjModel M).fr τ)⁻¹ =
      GlobalTheory.ConjDS.rv (M.fr τ * g * (M.fr τ)⁻¹) := fun g => rev_conj (M.fr τ) g
  have hcan : ∀ U : Matrix (Fin Y.rank) (Fin Y.rank) ℂ, M.fr τ * ((M.fr τ)⁻¹ * U * M.fr τ) * (M.fr τ)⁻¹ = U := by
    intro U
    simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul]
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
  refine ⟨fun u => ⟨?_, ?_, ?_⟩, fun X hX => ⟨?_, fun s => ?_⟩⟩
  · exact ofFr_mem_UH hF (M.fr_gram τ) u.2
  · show _ * ((M.fr τ)⁻¹ * Formalism.MainNotions.S.umat u * M.fr τ) * _ = _
    rw [hA, hcan]
  · show M.σ τ (M.fr τ * ((M.fr τ)⁻¹ * Formalism.MainNotions.S.umat u * M.fr τ) * (M.fr τ)⁻¹) = _
    rw [hcan]
  · exact conj_mem_lie ((GlobalTheory.ConjDS.conjModel M).fr_unit τ) ((GlobalTheory.ConjDS.conjModel M).fr_gram τ) hX
  · have hmem : NormedSpace.exp (s • X) ∈ Formalism.QuantumDeterminants.UH (gramAt D Y τ) :=
      GlobalTheory.SmoothAutCheck.exp_mem_UH (GlobalTheory.SmoothAutCheck.gramAt_unit Y τ) hX s
    have hc : cmp θ τ (oneP θ Y τ X s) = NormedSpace.exp (s • X) :=
      (GlobalTheory.PointAtPlaceHom.atTau_spec hθ Y τ hmem).2.1
    rw [hc]
    refine ⟨hmem, ?_⟩
    rw [← Matrix.exp_conj _ _ ((GlobalTheory.ConjDS.conjModel M).fr_unit τ), Matrix.mul_smul, Matrix.smul_mul]

end GlobalTheory.PackLocFacts

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PackLoc

theorem farClause : ∀ (D : D7) (θ : InfFam D) (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (S S' : D.what₂.Tau → SPar) (M₀ : DSModel Y S')
  (MP : DSModel V S) (τ : D.what₂.Tau) (e : Option (Fin Y.rank) ≃ Fin V.rank) (v₀ v : MP.H τ)
  (g₀ B : Matrix (Fin V.rank) (Fin V.rank) ℂ) (c₁ lam q Cb : ℝ) (k : ℕ),
  IsUnit B → Bᴴ * Formalism.REAL.Jm (MP.ε τ) * B = gramAt D V τ → B *ᵥ (fun i => tauE D τ (zv d i)) = Pi.single (e none) 1 →
  V.rank = k + 1 →
  (∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ u, GlobalTheory.PackLoc.mco MP τ g₀ v₀ (g * GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u)) =
    ⟪v, MP.σ τ (B * g * B⁻¹ * GlobalTheory.PackLoc.embOpt e (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) v⟫_ℂ) →
  (∀ F : Matrix (Fin Y.rank) (Fin Y.rank) ℂ → ℂ,
    Integrable (fun u : Formalism.REAL.UJ (M₀.ε τ) => F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) (Formalism.REAL.muG (M₀.ε τ)) ↔
      Integrable (fun h => F (Formalism.MainNotions.S.umat h)) (Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ))) →
  (∀ F : Matrix (Fin Y.rank) (Fin Y.rank) ℂ → ℝ, ∫ u, F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u)) ∂(Formalism.REAL.muG (M₀.ε τ)) =
    lam • ∫ h, F (Formalism.MainNotions.S.umat h) ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ))) →
  0 < c₁ → 0 < lam → Cb ≤ Real.exp q →
  (∀ g ∈ Formalism.MainNotions.S.UJset (MP.ε τ),
    Integrable (fun h => ⟪v, MP.σ τ (g * GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ)
      (Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ)) ∧
    ∫ h, ‖⟪v, MP.σ τ (g * GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ‖ ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ)) ≤
      c₁ * Cb * Real.sqrt (∑ a, ‖g a (e none)‖ ^ 2) ^ (-(2 * (k : ℝ) + 7))) →
  ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
    Integrable (fun u => GlobalTheory.PackLoc.mco MP τ g₀ v₀ (g * GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u)))
      (Formalism.REAL.muG (M₀.ε τ)) ∧
    (∫ u, ‖GlobalTheory.PackLoc.mco MP τ g₀ v₀ (g * GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u))‖ ∂(Formalism.REAL.muG (M₀.ε τ))) *
      eu (B *ᵥ (g *ᵥ fun i => tauE D τ (zv d i))) ^ (2 * V.rank + 5) ≤ Real.exp q * ‖((lam * c₁ : ℝ) : ℂ)‖ := by
  intro D θ Y V d S S' M₀ MP τ e v₀ v g₀ B c₁ lam q Cb k hB hBJ hBz hk hmco hint hInt hc₁ hlam hCb hb g hg
  set z : Fin V.rank → ℂ := fun i => tauE D τ (zv d i) with hz
  have hBinv : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B ((Matrix.isUnit_iff_isUnit_det B).mp hB)
  have hBinv' : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B ((Matrix.isUnit_iff_isUnit_det B).mp hB)
  have hg' : B * g * B⁻¹ ∈ Formalism.MainNotions.S.UJset (MP.ε τ) := by
    have hg0 : gᴴ * gramAt D V τ * g = gramAt D V τ := hg
    show (B * g * B⁻¹)ᴴ * Formalism.REAL.Jm (MP.ε τ) * (B * g * B⁻¹) = Formalism.REAL.Jm (MP.ε τ)
    have hBi : (B⁻¹)ᴴ * Bᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, hBinv', Matrix.conjTranspose_one]
    calc (B * g * B⁻¹)ᴴ * Formalism.REAL.Jm (MP.ε τ) * (B * g * B⁻¹)
        = (B⁻¹)ᴴ * (gᴴ * (Bᴴ * Formalism.REAL.Jm (MP.ε τ) * B) * g) * B⁻¹ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (B⁻¹)ᴴ * (Bᴴ * Formalism.REAL.Jm (MP.ε τ) * B) * B⁻¹ := by rw [hBJ, hg0]
      _ = ((B⁻¹)ᴴ * Bᴴ) * Formalism.REAL.Jm (MP.ε τ) * (B * B⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm (MP.ε τ) := by rw [hBi, hBinv']; simp
  obtain ⟨hbI, hbB⟩ := hb _ hg'
  set F : Matrix (Fin Y.rank) (Fin Y.rank) ℂ → ℂ :=
    fun x => ⟪v, MP.σ τ (B * g * B⁻¹ * GlobalTheory.PackLoc.embOpt e x) v⟫_ℂ with hF
  have hfun : (fun u => GlobalTheory.PackLoc.mco MP τ g₀ v₀ (g * GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u)))
      = fun u => F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u)) := funext (hmco g hg)
  refine ⟨?_, ?_⟩
  · rw [hfun]; exact (hint F).mpr hbI
  ·
    have hcol : B *ᵥ (g *ᵥ z) = fun a => (B * g * B⁻¹) a (e none) := by
      funext a
      have : (B * g * B⁻¹) *ᵥ (B *ᵥ z) = B *ᵥ (g *ᵥ z) := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_assoc (B * g), hBinv, Matrix.mul_one, ← Matrix.mulVec_mulVec]
      rw [← this, hBz]
      simp [Matrix.mulVec_single]
    set L := eu (B *ᵥ (g *ᵥ z)) with hL
    have hLdef : L = Real.sqrt (∑ a, ‖(B * g * B⁻¹) a (e none)‖ ^ 2) := by
      rw [hL, hcol]; rfl
    have hI : (∫ u, ‖GlobalTheory.PackLoc.mco MP τ g₀ v₀ (g * GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u))‖ ∂(Formalism.REAL.muG (M₀.ε τ)))
        = lam * ∫ h, ‖F (Formalism.MainNotions.S.umat h)‖ ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ)) := by
      have := hInt (fun x => ‖F x‖)
      rw [smul_eq_mul] at this
      rw [← this]
      congr 1
      funext u
      rw [hmco g hg u]
    have hL0 : 0 ≤ L := Real.sqrt_nonneg _
    have hexp : 2 * V.rank + 5 = 2 * k + 7 := by omega
    have hnorm : ‖((lam * c₁ : ℝ) : ℂ)‖ = lam * c₁ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mul_pos hlam hc₁)]
    rw [hI, hnorm, hexp]
    have hInn : 0 ≤ ∫ h, ‖F (Formalism.MainNotions.S.umat h)‖ ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ)) :=
      integral_nonneg (fun _ => norm_nonneg _)
    rcases hL0.lt_or_eq with hLp | hLz
    · have hbB' : ∫ h, ‖F (Formalism.MainNotions.S.umat h)‖ ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ))
          ≤ c₁ * Cb * L ^ (-(2 * (k : ℝ) + 7)) := by rw [hLdef]; exact hbB
      have hpow : L ^ (-(2 * (k : ℝ) + 7)) * L ^ (2 * k + 7) = 1 := by
        rw [Real.rpow_neg hL0, ← Real.rpow_natCast]
        push_cast
        exact inv_mul_cancel₀ (Real.rpow_pos_of_pos hLp _).ne'
      have hLn : 0 ≤ L ^ (2 * k + 7) := pow_nonneg hL0 _
      calc lam * (∫ h, ‖F (Formalism.MainNotions.S.umat h)‖ ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ))) * L ^ (2 * k + 7)
          ≤ lam * (c₁ * Cb * L ^ (-(2 * (k : ℝ) + 7))) * L ^ (2 * k + 7) := by
            gcongr
        _ = lam * c₁ * Cb * (L ^ (-(2 * (k : ℝ) + 7)) * L ^ (2 * k + 7)) := by ring
        _ = lam * c₁ * Cb := by rw [hpow, mul_one]
        _ ≤ lam * c₁ * Real.exp q := by
            exact mul_le_mul_of_nonneg_left hCb (mul_pos hlam hc₁).le
        _ = Real.exp q * (lam * c₁) := by ring
    · rw [← hLz, zero_pow (by omega), mul_zero]
      exact mul_nonneg (Real.exp_pos q).le (mul_pos hlam hc₁).le

end GlobalTheory.PackLoc
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.PackLoc.lipAt : ∀ (D : D7) (θ : InfFam D) (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (S S' : D.what₂.Tau → SPar) (M₀ : DSModel Y S')
  (MP : DSModel V S) (τ : D.what₂.Tau) (e : Option (Fin Y.rank) ≃ Fin V.rank) (v₀ v : MP.H τ)
  (g₀ : Matrix (Fin V.rank) (Fin V.rank) ℂ) (A : Matrix (Fin Y.rank) (Fin Y.rank) ℂ) (K lam q : ℝ) (c : ℂ),
  (∀ u, GlobalTheory.PackLoc.mco MP τ g₀ v₀ (GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u)) =
    ⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) v⟫_ℂ) →
  (∀ X ∈ lieAt Y τ, ∀ (s : ℝ) u,
    GlobalTheory.PackLoc.mco MP τ g₀ v₀ (GlobalTheory.PackLoc.embAt θ d τ (cmp θ τ (oneP θ Y τ X s) * GlobalTheory.PackLoc.ptY M₀ τ u)) =
      ⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (NormedSpace.exp (s • (A * X * A⁻¹)) * GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) v⟫_ℂ) →
  (∀ X ∈ lieAt Y τ, A * X * A⁻¹ ∈ GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ((GlobalTheory.ConjDS.conjModel M₀).ε τ))) →
  (∀ X ∈ GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ((GlobalTheory.ConjDS.conjModel M₀).ε τ)), ∀ s : ℝ,
    Integrable (fun h => ‖⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (NormedSpace.exp (s • X) * Formalism.MainNotions.S.umat h)) v⟫_ℂ -
      ⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ‖) (Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ)) ∧
    ∫ h, ‖⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (NormedSpace.exp (s • X) * Formalism.MainNotions.S.umat h)) v⟫_ℂ -
      ⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ‖ ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ)) ≤
        K * |s| * GlobalTheory.SepReal.hsn X) →
  (∀ F : Matrix (Fin Y.rank) (Fin Y.rank) ℂ → ℝ,
    (Integrable (fun u : Formalism.REAL.UJ (M₀.ε τ) => F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) (Formalism.REAL.muG (M₀.ε τ)) ↔
      Integrable (fun h => F (Formalism.MainNotions.S.umat h)) (Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ))) ∧
    ∫ u, F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u)) ∂(Formalism.REAL.muG (M₀.ε τ)) =
      lam • ∫ h, F (Formalism.MainNotions.S.umat h) ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ))) →
  0 < lam → lam * K ≤ Real.exp q * ‖c‖ →
  ∀ X ∈ lieAt Y τ, ∀ s : ℝ,
    Integrable (fun u => ‖GlobalTheory.PackLoc.mco MP τ g₀ v₀ (GlobalTheory.PackLoc.embAt θ d τ (cmp θ τ (oneP θ Y τ X s) * GlobalTheory.PackLoc.ptY M₀ τ u)) -
      GlobalTheory.PackLoc.mco MP τ g₀ v₀ (GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u))‖) (Formalism.REAL.muG (M₀.ε τ)) ∧
    ∫ u, ‖GlobalTheory.PackLoc.mco MP τ g₀ v₀ (GlobalTheory.PackLoc.embAt θ d τ (cmp θ τ (oneP θ Y τ X s) * GlobalTheory.PackLoc.ptY M₀ τ u)) -
      GlobalTheory.PackLoc.mco MP τ g₀ v₀ (GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u))‖ ∂(Formalism.REAL.muG (M₀.ε τ)) ≤
      Real.exp q * ‖c‖ * |s| * hsn (A * X * A⁻¹) := by
  intro D θ Y V d S S' M₀ MP τ e v₀ v g₀ A K lam q c hB hA hL hK hH hlam hlk X hX s
  set X' := A * X * A⁻¹ with hX'
  have hX'L := hL X hX
  set F : Matrix (Fin Y.rank) (Fin Y.rank) ℂ → ℝ := fun x =>
    ‖⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (NormedSpace.exp (s • X') * x)) v⟫_ℂ -
      ⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e x) v⟫_ℂ‖ with hF
  have hfun : (fun u => ‖GlobalTheory.PackLoc.mco MP τ g₀ v₀ (GlobalTheory.PackLoc.embAt θ d τ (cmp θ τ (oneP θ Y τ X s) * GlobalTheory.PackLoc.ptY M₀ τ u)) -
      GlobalTheory.PackLoc.mco MP τ g₀ v₀ (GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u))‖) =
      fun u => F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u)) := by
    funext u
    rw [hA X hX s u, hB u]
  obtain ⟨hint, hbd⟩ := hK X' hX'L s
  obtain ⟨hiff, heq⟩ := hH F
  have hsnEq : GlobalTheory.SepReal.hsn X' = hsn X' := rfl
  have hsn0 : 0 ≤ hsn X' := Real.sqrt_nonneg _
  rw [hfun]
  refine ⟨hiff.2 hint, ?_⟩
  rw [heq, smul_eq_mul]
  have h1 : lam * ∫ h, F (Formalism.MainNotions.S.umat h) ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ)) ≤
      lam * (K * |s| * hsn X') := by
    rw [← hsnEq]
    exact mul_le_mul_of_nonneg_left hbd hlam.le
  have h2 : lam * (K * |s| * hsn X') ≤ Real.exp q * ‖c‖ * |s| * hsn X' := by
    have hm : 0 ≤ |s| * hsn X' := mul_nonneg (abs_nonneg s) hsn0
    calc lam * (K * |s| * hsn X') = (lam * K) * (|s| * hsn X') := by ring
      _ ≤ (Real.exp q * ‖c‖) * (|s| * hsn X') := mul_le_mul_of_nonneg_right hlk hm
      _ = Real.exp q * ‖c‖ * |s| * hsn X' := by ring
  exact h1.trans h2
end
