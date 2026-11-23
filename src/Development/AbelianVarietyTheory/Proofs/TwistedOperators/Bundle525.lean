module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle476
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle478
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealIntertwinerContractionOnePlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefIntegralEq
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle502
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle504
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical


open Matrix in
theorem GlobalTheory.CuspGK.inK_inv {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : Formalism.IndefR.Mult.DSModel V S)
    (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (h : GlobalTheory.CuspGK.InK M τ g) :
    GlobalTheory.CuspGK.InK M τ g⁻¹ ∧ g⁻¹⁻¹ = g := by
  obtain ⟨hU, hK1, hK2⟩ := h
  set P := M.fr τ with hPdef
  have hP : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  set u := P * g * P⁻¹ with hu
  have huu : IsUnit u.det := Matrix.UnitaryGroup.det_isUnit ⟨u, hK1⟩
  have hg : IsUnit g.det := by
    have hdet : u.det = P.det * g.det * P⁻¹.det := by simp [hu, Matrix.det_mul]
    rw [hdet] at huu
    exact isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left huu)
  have hinv : P * g⁻¹ * P⁻¹ = u⁻¹ := by
    rw [hu, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hP, Matrix.mul_assoc]
  have hsu : star u * u = 1 := Unitary.star_mul_self_of_mem hK1
  have hustar : u⁻¹ = star u := Matrix.inv_eq_left_inv hsu
  have h1 : u⁻¹ * u = 1 := Matrix.nonsing_inv_mul _ huu
  have h2 : u * u⁻¹ = 1 := Matrix.mul_nonsing_inv _ huu
  refine ⟨⟨?_, ?_, ?_⟩, Matrix.nonsing_inv_nonsing_inv _ hg⟩
  · have hU' : gᴴ * gramAt D V τ * g = gramAt D V τ := hU
    show (g⁻¹)ᴴ * gramAt D V τ * g⁻¹ = gramAt D V τ
    have hgg : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv _ hg
    calc (g⁻¹)ᴴ * gramAt D V τ * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * gramAt D V τ * g) * g⁻¹ := by rw [hU']
      _ = (g * g⁻¹)ᴴ * gramAt D V τ * (g * g⁻¹) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = gramAt D V τ := by rw [hgg]; simp
  · show P * g⁻¹ * P⁻¹ ∈ _
    rw [hinv, hustar]
    exact Unitary.star_mem hK1
  · show P * g⁻¹ * P⁻¹ * _ = _ * (P * g⁻¹ * P⁻¹)
    rw [hinv]
    clear_value u
    calc u⁻¹ * Formalism.REAL.Jm (M.ε τ) = u⁻¹ * Formalism.REAL.Jm (M.ε τ) * (u * u⁻¹) := by rw [h2, Matrix.mul_one]
      _ = u⁻¹ * (Formalism.REAL.Jm (M.ε τ) * u) * u⁻¹ := by simp only [Matrix.mul_assoc]
      _ = u⁻¹ * (u * Formalism.REAL.Jm (M.ε τ)) * u⁻¹ := by rw [hK2]
      _ = (u⁻¹ * u) * Formalism.REAL.Jm (M.ε τ) * u⁻¹ := by simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm (M.ε τ) * u⁻¹ := by rw [h1, Matrix.one_mul]
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.CuspGK

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D} {S : D.what₂.Tau → SPar}
  (M : Formalism.IndefR.Mult.DSModel V S)

theorem isGKSub_sInf (s : Set (Submodule ℂ (GA D V → ℂ))) (h : ∀ A ∈ s, IsGKSub θ M A) : IsGKSub θ M (sInf s) := by
  constructor
  · intro τ g hg f hf
    exact Submodule.mem_sInf.2 fun A hA => (h A hA).k τ g hg f (Submodule.mem_sInf.1 hf A hA)
  · intro τ X hX f hf
    exact Submodule.mem_sInf.2 fun A hA => (h A hA).lie τ X hX f (Submodule.mem_sInf.1 hf A hA)


open scoped Matrix in
variable {M} in
theorem InK.inv {τ : D.what₂.Tau} {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (h : InK M τ g) : InK M τ g⁻¹ := by
  obtain ⟨hU, hk⟩ := h
  have hfd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  set k := M.fr τ * g * (M.fr τ)⁻¹ with hkdef
  have hku : k ∈ Matrix.unitaryGroup (Fin V.rank) ℂ := hk.1
  have hsk : star k * k = 1 := Matrix.mem_unitaryGroup_iff'.1 hku
  have hks : k * star k = 1 := Matrix.mem_unitaryGroup_iff.1 hku
  have hkdet : IsUnit k.det := (Matrix.isUnit_iff_isUnit_det _).1 ⟨⟨k, star k, hks, hsk⟩, rfl⟩
  have hdet : k.det = g.det := by
    rw [hkdef, Matrix.det_mul, Matrix.det_mul, mul_comm (M.fr τ).det, mul_assoc, ← Matrix.det_mul,
      Matrix.mul_nonsing_inv _ hfd, Matrix.det_one, mul_one]
  have hgd : IsUnit g.det := hdet ▸ hkdet
  have hg1 : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv _ hgd
  have hU' : gᴴ * gramAt D V τ * g = gramAt D V τ := hU
  refine ⟨?_, ?_⟩
  · show (g⁻¹)ᴴ * gramAt D V τ * g⁻¹ = gramAt D V τ
    calc (g⁻¹)ᴴ * gramAt D V τ * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * gramAt D V τ * g) * g⁻¹ := by rw [hU']
      _ = (g * g⁻¹)ᴴ * gramAt D V τ * (g * g⁻¹) := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = gramAt D V τ := by rw [hg1, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  · have e1 : M.fr τ * g⁻¹ * (M.fr τ)⁻¹ = k⁻¹ := by
      rw [hkdef, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hfd]
      simp only [Matrix.mul_assoc]
    have hinv : k⁻¹ = star k := Matrix.inv_eq_left_inv hsk
    rw [e1, hinv]
    refine ⟨Matrix.mem_unitaryGroup_iff.2 (by rw [star_star]; exact hsk), ?_⟩
    have hJ : star (Formalism.REAL.Jm (M.ε τ)) = Formalism.REAL.Jm (M.ε τ) := Formalism.REAL.Jm_conjTranspose _
    have hcomm : ∀ m : Matrix (Fin V.rank) (Fin V.rank) ℂ, m * Formalism.REAL.Jm (M.ε τ) = Formalism.REAL.Jm (M.ε τ) * m →
        star m * Formalism.REAL.Jm (M.ε τ) = Formalism.REAL.Jm (M.ε τ) * star m := fun m hm => by
      have h2 : star (m * Formalism.REAL.Jm (M.ε τ)) = star (Formalism.REAL.Jm (M.ε τ) * m) := congrArg star hm
      rw [star_mul, star_mul, hJ] at h2
      exact h2.symm
    exact hcomm k hk.2

end GlobalTheory.CuspGK

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.CuspGKId

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D} {S : D.what₂.Tau → SPar}
  (M : Formalism.IndefR.Mult.DSModel V S)

structure IsLocSub (τ : D.what₂.Tau) (B : Submodule ℂ (GA D V → ℂ)) : Prop where
  k : ∀ g, GlobalTheory.CuspGK.InK M τ g → ∀ f ∈ B, rTr V (atTau θ V τ g) f ∈ B
  lie : ∀ X ∈ lieAt V τ, ∀ f ∈ B, Rder θ V τ X f ∈ B

def locGen (τ : D.what₂.Tau) (ψ : GA D V → ℂ) : Submodule ℂ (GA D V → ℂ) :=
  sInf {B | ψ ∈ B ∧ IsLocSub θ M τ B}

theorem mem_locGen (τ : D.what₂.Tau) (ψ : GA D V → ℂ) : ψ ∈ locGen θ M τ ψ :=
  Submodule.mem_sInf.2 fun _ h => h.1

theorem isLocSub_locGen (τ : D.what₂.Tau) (ψ : GA D V → ℂ) : IsLocSub θ M τ (locGen θ M τ ψ) := by
  constructor
  · intro g hg f hf
    exact Submodule.mem_sInf.2 fun B hB => hB.2.k g hg f (Submodule.mem_sInf.1 hf B hB)
  · intro X hX f hf
    exact Submodule.mem_sInf.2 fun B hB => hB.2.lie X hX f (Submodule.mem_sInf.1 hf B hB)

theorem locGen_le {τ : D.what₂.Tau} {ψ : GA D V → ℂ} {B : Submodule ℂ (GA D V → ℂ)} (hψ : ψ ∈ B)
    (hB : IsLocSub θ M τ B) : locGen θ M τ ψ ≤ B :=
  sInf_le ⟨hψ, hB⟩

end GlobalTheory.CuspGKId

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.KTypeProj

section Gen

variable {M ι : Type} [AddCommGroup M] [Module ℂ M]

def typeSpan (ρ : ι → M →ₗ[ℂ] M) (Y₀ G : Submodule ℂ M) : Submodule ℂ M :=
  ⨆ (T : M →ₗ[ℂ] M) (_ : Y₀.map T ≤ G ∧ ∀ i, ∀ w ∈ Y₀, T (ρ i w) = ρ i (T w)), Y₀.map T

theorem typeSpan_le (ρ : ι → M →ₗ[ℂ] M) (Y₀ G : Submodule ℂ M) : typeSpan ρ Y₀ G ≤ G :=
  iSup₂_le fun _ h => h.1

theorem le_typeSpan (ρ : ι → M →ₗ[ℂ] M) {Y₀ G : Submodule ℂ M} (h : Y₀ ≤ G) : Y₀ ≤ typeSpan ρ Y₀ G := by
  have h1 : Y₀.map LinearMap.id ≤ typeSpan ρ Y₀ G :=
    le_iSup₂_of_le (f := fun (T : M →ₗ[ℂ] M) (_ : Y₀.map T ≤ G ∧ ∀ i, ∀ w ∈ Y₀, T (ρ i w) = ρ i (T w)) => Y₀.map T)
      LinearMap.id ⟨by rwa [Submodule.map_id], fun _ _ _ => rfl⟩ le_rfl
  rwa [Submodule.map_id] at h1

theorem map_le_typeSpan (ρ : ι → M →ₗ[ℂ] M) {Y₀ G : Submodule ℂ M} (T : M →ₗ[ℂ] M) (hT : Y₀.map T ≤ G)
    (hc : ∀ i, ∀ w ∈ Y₀, T (ρ i w) = ρ i (T w)) : Y₀.map T ≤ typeSpan ρ Y₀ G :=
  le_iSup₂_of_le (f := fun (T : M →ₗ[ℂ] M) (_ : Y₀.map T ≤ G ∧ ∀ i, ∀ w ∈ Y₀, T (ρ i w) = ρ i (T w)) => Y₀.map T)
    T ⟨hT, hc⟩ le_rfl

end Gen

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D} {S : D.what₂.Tau → SPar}
  (M : Formalism.IndefR.Mult.DSModel V S)

def rTrL (k : GA D V) : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ) where
  toFun := rTr V k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem rTrL_apply (k : GA D V) (f : GA D V → ℂ) : rTrL k f = rTr V k f := rfl

def KIdx : Type := {p : D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ // GlobalTheory.CuspGK.InK M p.1 p.2}

def rhoK (i : KIdx M) : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ) := rTrL (atTau θ V i.1.1 i.1.2)

def KStable (Y : Submodule ℂ (GA D V → ℂ)) : Prop :=
  ∀ τ g, GlobalTheory.CuspGK.InK M τ g → ∀ f ∈ Y, rTr V (atTau θ V τ g) f ∈ Y

theorem kStable_iff (Y : Submodule ℂ (GA D V → ℂ)) : KStable θ M Y ↔ ∀ i, ∀ y ∈ Y, rhoK θ M i y ∈ Y :=
  ⟨fun h i y hy => h i.1.1 i.1.2 i.2 y hy, fun h τ g hg y hy => h ⟨(τ, g), hg⟩ y hy⟩

theorem kStable_inf {Y Y' : Submodule ℂ (GA D V → ℂ)} (h : KStable θ M Y) (h' : KStable θ M Y') :
    KStable θ M (Y ⊓ Y') :=
  fun τ g hg f hf => ⟨h τ g hg f hf.1, h' τ g hg f hf.2⟩

theorem kStable_gkGen (ψ : GA D V → ℂ) : KStable θ M (GlobalTheory.CuspGK.gkGen θ M ψ) :=
  (GlobalTheory.CuspGK.isGKSub_gkGen θ M ψ).k

theorem kStable_of_isGKSub {A : Submodule ℂ (GA D V → ℂ)} (h : GlobalTheory.CuspGK.IsGKSub θ M A) : KStable θ M A := h.k

end GlobalTheory.KTypeProj

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Classical

noncomputable section

namespace GlobalTheory.KFinDecomp

theorem assemble_finset {ι : Type} [DecidableEq ι] {U : ι → Type} [∀ τ, AddCommGroup (U τ)] [∀ τ, Module ℂ (U τ)]
    {E : Type} [AddCommGroup E] [Module ℂ E] (𝒞 : Set E) (Ty : ι → E → Prop)
    (R : ∀ τ, U τ → U τ → (E → E) → Prop) (m : ι → ℕ) (a : ∀ τ, Fin (m τ) → U τ)
    (A : ∀ τ, Fin (m τ) → U τ → E → E)
    (hadd : ∀ τ j u, ∀ f ∈ 𝒞, ∀ f' ∈ 𝒞, A τ j u (f + f') = A τ j u f + A τ j u f')
    (hsmul : ∀ τ j u (c : ℂ), ∀ f ∈ 𝒞, A τ j u (c • f) = c • A τ j u f)
    (hmaps : ∀ τ j u, ∀ f ∈ 𝒞, A τ j u f ∈ 𝒞)
    (hkeep : ∀ τ j u τ', τ' ≠ τ → ∀ f ∈ 𝒞, Ty τ' f → Ty τ' (A τ j u f))
    (hcomm : ∀ τ j u τ', τ' ≠ τ → ∀ x y Φ, R τ' x y Φ → ∀ f ∈ 𝒞, A τ j u (Φ f) = Φ (A τ j u f))
    (hadd' : ∀ τ j, ∀ f ∈ 𝒞, ∀ u u', A τ j (u + u') f = A τ j u f + A τ j u' f)
    (hsmul' : ∀ τ j, ∀ f ∈ 𝒞, ∀ (c : ℂ) u, A τ j (c • u) f = c • A τ j u f)
    (hR : ∀ τ j, ∀ f ∈ 𝒞, ∀ u w Φ, R τ u w Φ → A τ j w f = Φ (A τ j u f))
    (hsum : ∀ τ, ∀ f ∈ 𝒞, Ty τ f → f = ∑ j, A τ j (a τ j) f)
    (ψ : E) (hψ : ψ ∈ 𝒞) (hTy : ∀ τ, Ty τ ψ) (s : Finset ι) :
    ∃ (κ : Type) (_ : Fintype κ) (T : κ → (∀ τ, U τ) → E) (u : κ → ∀ τ, U τ),
      (∀ k v, T k v ∈ 𝒞) ∧ (∀ k v, ∀ τ ∉ s, Ty τ (T k v)) ∧
      (∀ k v, ∀ τ ∉ s, ∀ w, T k (Function.update v τ w) = T k v) ∧
      (∀ k v, ∀ τ ∈ s, ∀ x y, T k (Function.update v τ (x + y)) =
        T k (Function.update v τ x) + T k (Function.update v τ y)) ∧
      (∀ k v, ∀ τ ∈ s, ∀ (c : ℂ) x, T k (Function.update v τ (c • x)) = c • T k (Function.update v τ x)) ∧
      (∀ k v, ∀ τ ∈ s, ∀ w Φ, R τ (v τ) w Φ → T k (Function.update v τ w) = Φ (T k v)) ∧
      ψ = ∑ k, T k (u k) := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨Unit, inferInstance, fun _ _ => ψ, fun _ _ => 0, fun _ _ => hψ, fun _ _ τ _ => hTy τ,
      fun _ _ _ _ _ => rfl, ?_, ?_, ?_, ?_⟩
    · intro _ _ τ hτ; exact absurd hτ (Finset.notMem_empty τ)
    · intro _ _ τ hτ; exact absurd hτ (Finset.notMem_empty τ)
    · intro _ _ τ hτ; exact absurd hτ (Finset.notMem_empty τ)
    · simp
  | @insert τ₀ s hτ₀ ih =>
    obtain ⟨κ, hκ, T, u, hT𝒞, hTTy, hTfix, hTadd, hTsmul, hTR, hψs⟩ := ih

    refine ⟨κ × Fin (m τ₀), inferInstance, fun p v => A τ₀ p.2 (v τ₀) (T p.1 v),
      fun p => Function.update (u p.1) τ₀ (a τ₀ p.2), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro p v
      exact hmaps _ _ _ _ (hT𝒞 _ _)
    · intro p v τ hτ
      have hne : τ ≠ τ₀ := fun h => hτ (h ▸ Finset.mem_insert_self τ₀ s)
      have hs : τ ∉ s := fun h => hτ (Finset.mem_insert_of_mem h)
      exact hkeep τ₀ p.2 (v τ₀) τ hne _ (hT𝒞 _ _) (hTTy _ _ τ hs)
    · intro p v τ hτ w
      have hne : τ ≠ τ₀ := fun h => hτ (h ▸ Finset.mem_insert_self τ₀ s)
      have hs : τ ∉ s := fun h => hτ (Finset.mem_insert_of_mem h)
      show A τ₀ p.2 (Function.update v τ w τ₀) (T p.1 (Function.update v τ w)) = A τ₀ p.2 (v τ₀) (T p.1 v)
      rw [Function.update_of_ne hne.symm, hTfix p.1 v τ hs w]
    · intro p v τ hτ x y
      show A τ₀ p.2 (Function.update v τ (x + y) τ₀) (T p.1 (Function.update v τ (x + y))) =
        A τ₀ p.2 (Function.update v τ x τ₀) (T p.1 (Function.update v τ x)) +
          A τ₀ p.2 (Function.update v τ y τ₀) (T p.1 (Function.update v τ y))
      by_cases h : τ = τ₀
      · subst h
        simp only [Function.update_self]
        rw [hTfix p.1 v τ hτ₀, hTfix p.1 v τ hτ₀, hTfix p.1 v τ hτ₀]
        exact hadd' τ p.2 _ (hT𝒞 _ _) x y
      · have hs : τ ∈ s := (Finset.mem_insert.1 hτ).resolve_left h
        rw [Function.update_of_ne (Ne.symm h), Function.update_of_ne (Ne.symm h),
          Function.update_of_ne (Ne.symm h), hTadd p.1 v τ hs x y]
        exact hadd τ₀ p.2 (v τ₀) _ (hT𝒞 _ _) _ (hT𝒞 _ _)
    · intro p v τ hτ c x
      show A τ₀ p.2 (Function.update v τ (c • x) τ₀) (T p.1 (Function.update v τ (c • x))) =
        c • A τ₀ p.2 (Function.update v τ x τ₀) (T p.1 (Function.update v τ x))
      by_cases h : τ = τ₀
      · subst h
        simp only [Function.update_self]
        rw [hTfix p.1 v τ hτ₀, hTfix p.1 v τ hτ₀]
        exact hsmul' τ p.2 _ (hT𝒞 _ _) c x
      · have hs : τ ∈ s := (Finset.mem_insert.1 hτ).resolve_left h
        rw [Function.update_of_ne (Ne.symm h), Function.update_of_ne (Ne.symm h),
          hTsmul p.1 v τ hs c x]
        exact hsmul τ₀ p.2 (v τ₀) c _ (hT𝒞 _ _)
    · intro p v τ hτ w Φ hRw
      show A τ₀ p.2 (Function.update v τ w τ₀) (T p.1 (Function.update v τ w)) =
        Φ (A τ₀ p.2 (v τ₀) (T p.1 v))
      by_cases h : τ = τ₀
      · subst h
        rw [Function.update_self, hTfix p.1 v τ hτ₀]
        exact hR τ p.2 _ (hT𝒞 _ _) (v τ) w Φ hRw
      · have hs : τ ∈ s := (Finset.mem_insert.1 hτ).resolve_left h
        rw [Function.update_of_ne (Ne.symm h), hTR p.1 v τ hs w Φ hRw]
        exact (hcomm τ₀ p.2 (v τ₀) τ h (v τ) w Φ hRw _ (hT𝒞 _ _)).symm ▸ rfl
    ·
      have hterm : ∀ k, T k (u k) = ∑ j, A τ₀ j (a τ₀ j) (T k (u k)) := fun k =>
        hsum τ₀ _ (hT𝒞 _ _) (hTTy _ _ τ₀ hτ₀)
      rw [Fintype.sum_prod_type, hψs]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hterm k]
      refine Finset.sum_congr rfl fun j _ => ?_
      show A τ₀ j (a τ₀ j) (T k (u k)) =
        A τ₀ j (Function.update (u k) τ₀ (a τ₀ j) τ₀) (T k (Function.update (u k) τ₀ (a τ₀ j)))
      rw [Function.update_self, hTfix k (u k) τ₀ hτ₀]

theorem assemble_places : ∀ (D : D7) (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (𝒞 : Set (GA D N.V → ℂ)) (Ty : D.what₂.Tau → (GA D N.V → ℂ) → Prop), (∀ f ∈ 𝒞, Continuous f) → (∀ τ, GlobalTheory.KFinDecomp.DecompAt θ N 𝒞 Ty τ) → ∀ ψ ∈ 𝒞, (∀ τ, Ty τ ψ) → ∃ (n : ℕ) (T₀ : Fin n → GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KMap N.M) (u : Fin n → GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec N.M), (∀ j v, T₀ j v ∈ 𝒞) ∧ (∀ j, ∀ τ, ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt N.M τ, ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec N.M) (w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ), (w : N.M.H τ) = N.M.rep τ k (v τ) → T₀ j (Function.update v τ w) = rTr N.V (atTau θ N.V τ k) (T₀ j v)) ∧ (∀ j, ∀ τ, ∀ X ∈ lieAt N.V τ, ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec N.M) (w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ), (w : N.M.H τ) = dRep (N.M.rep τ) X (v τ) → T₀ j (Function.update v τ w) = Rder θ N.V τ X (T₀ j v)) ∧ ψ = ∑ j, T₀ j (u j) := by
  intro D θ N 𝒞 Ty hcont hdec ψ hψ hTy
  unfold GlobalTheory.KFinDecomp.DecompAt at hdec
  choose m a A hop hlin hsum using hdec

  have hK : ∀ τ, ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt N.M τ, k ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ) := by
    intro τ k hk
    have hu : IsUnit (N.M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (N.M.fr_unit τ)
    have h := (GlobalTheory.Chain.RealLine.Semi.conj_compact N.M τ (k := N.M.fr τ * k * (N.M.fr τ)⁻¹) hk).1
    have he : (N.M.fr τ)⁻¹ * (N.M.fr τ * k * (N.M.fr τ)⁻¹) * N.M.fr τ = k :=
      calc (N.M.fr τ)⁻¹ * (N.M.fr τ * k * (N.M.fr τ)⁻¹) * N.M.fr τ
          = ((N.M.fr τ)⁻¹ * N.M.fr τ) * k * ((N.M.fr τ)⁻¹ * N.M.fr τ) := by simp only [mul_assoc]
        _ = k := by rw [Matrix.nonsing_inv_mul _ hu, one_mul, mul_one]
    rwa [he] at h

  let R : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ → GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ →
      ((GA D N.V → ℂ) → (GA D N.V → ℂ)) → Prop := fun τ x y Φ =>
    (∃ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt N.M τ, (y : N.M.H τ) = N.M.rep τ k x ∧
        Φ = fun f => rTr N.V (atTau θ N.V τ k) f) ∨
      (∃ X ∈ lieAt N.V τ, (y : N.M.H τ) = dRep (N.M.rep τ) X x ∧ Φ = fun f => Rder θ N.V τ X f)
  have hcomm : ∀ τ j u τ', τ' ≠ τ → ∀ x y Φ, R τ' x y Φ → ∀ f ∈ 𝒞, A τ j u (Φ f) = Φ (A τ j u f) := by
    rintro τ j u τ' hne x y Φ (⟨k, hk, -, rfl⟩ | ⟨X, hX, -, rfl⟩) f hf
    · exact (hop τ j u).tr τ' hne k (hK τ' k hk) f hf
    · exact (hop τ j u).lie τ' hne X hX f hf
  have hRel : ∀ τ j, ∀ f ∈ 𝒞, ∀ x y Φ, R τ x y Φ → A τ j y f = Φ (A τ j x f) := by
    rintro τ j f hf x y Φ (⟨k, hk, hy, rfl⟩ | ⟨X, hX, hy, rfl⟩)
    · exact (hlin τ j f hf).2.2.1 k hk x y hy
    · exact (hlin τ j f hf).2.2.2 X hX x y hy
  obtain ⟨κ, hκ, T, u, hT𝒞, -, -, hTadd, hTsmul, hTR, hψT⟩ :=
    GlobalTheory.KFinDecomp.assemble_finset (U := fun τ => GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ) 𝒞 Ty R m a A
      (fun τ j x f hf f' hf' => (hop τ j x).add f f' (hcont f hf) (hcont f' hf'))
      (fun τ j x c f hf => (hop τ j x).smul c f (hcont f hf))
      (fun τ j x f hf => (hop τ j x).maps f hf)
      (fun τ j x τ' hne f hf h' => (hop τ j x).keep τ' hne f hf h')
      hcomm
      (fun τ j f hf x x' => (hlin τ j f hf).1 x x')
      (fun τ j f hf c x => (hlin τ j f hf).2.1 c x)
      hRel hsum ψ hψ hTy Finset.univ

  let e := Fintype.equivFin κ
  let T₀ : Fin (Fintype.card κ) → GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KMap N.M := fun j =>
    (⟨T (e.symm j),
      fun v τ x y => by convert hTadd (e.symm j) v τ (Finset.mem_univ τ) x y,
      fun v τ c x => by convert hTsmul (e.symm j) v τ (Finset.mem_univ τ) c x⟩ :
      MultilinearMap (RingHom.id ℂ) (fun τ => GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ) (GA D N.V → ℂ))
  refine ⟨Fintype.card κ, T₀, fun j => u (e.symm j), fun j v => hT𝒞 (e.symm j) v, ?_, ?_, ?_⟩
  · intro j τ k hk v w hw
    exact hTR (e.symm j) v τ (Finset.mem_univ τ) w _ (Or.inl ⟨k, hk, hw, rfl⟩)
  · intro j τ X hX v w hw
    exact hTR (e.symm j) v τ (Finset.mem_univ τ) w _ (Or.inr ⟨X, hX, hw, rfl⟩)
  · rw [hψT]
    exact (Equiv.sum_comp e.symm (fun k => T k (u k))).symm

end GlobalTheory.KFinDecomp

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size

noncomputable section

namespace GlobalTheory.PlaceDecomp

variable {D : D7}

def TyOf (θ : InfFam D) (N : GlobalTheory.Grid.Node D) {W : D.what₂.Tau → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)]
    (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (N.M.ε τ)) (W τ)) : D.what₂.Tau → (GA D N.V → ℂ) → Prop :=
  fun τ f => GlobalTheory.Published.AutFin.HasTypeAt θ N.V τ (N.M.ε τ) (N.M.fr τ) (ρ τ) f

def HasCtp (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (U : Subgroup (GA D N.V)) (Ty : D.what₂.Tau → (GA D N.V → ℂ) → Prop)
    (τ : D.what₂.Tau) (T : N.M.H τ → N.M.H τ) : Prop :=
  ∃ A : (GA D N.V → ℂ) → (GA D N.V → ℂ), GlobalTheory.KFinDecomp.IsOpAt θ N (GlobalTheory.KFinDecomp.Cls θ N U) Ty τ A ∧
    ∀ φ ∈ GlobalTheory.KFinDecomp.Cls θ N U, GlobalTheory.SeriesToClosure.Moves θ N.V τ (N.M.ε τ) (N.M.σ τ) (N.M.fr τ) T φ (A φ)

theorem hasCtp_id (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (U : Subgroup (GA D N.V)) (Ty : D.what₂.Tau → (GA D N.V → ℂ) → Prop)
    (τ : D.what₂.Tau) : HasCtp θ N U Ty τ id :=
  ⟨id, GlobalTheory.KFinDecomp.isOpAt_id θ N _ Ty τ, fun _ _ _ _ _ _ _ _ _ h => h⟩

end GlobalTheory.PlaceDecomp

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isotropicIntegrals_determine_thetaMean_products : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → (∀ y y' : Mx D a b, symplO V W (GlobalTheory.IsoMean.emb V W P Q y) (GlobalTheory.IsoMean.emb V W P Q y') = 0) → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b)), IsCovolOne ((incA D).toAddMonoidHom.mapMatrix (m := Fin a) (n := Fin b)).range μ 𝓨 → ∀ F₁ F₁' F₂ F₂' : WO V W → ℂ, IsThetaFunO ψ V W F₁ → IsThetaFunO ψ V W F₁' → IsThetaFunO ψ V W F₂ → IsThetaFunO ψ V W F₂' → (∀ (ν : Measure (WO V W)) (𝓕 : Set (WO V W)), ν.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 ν → ∀ w : WO V W, (∀ y : Mx D a b, symplO V W w (GlobalTheory.IsoMean.emb V W P Q y) = 0) → ∫ y, (∫ u in 𝓕, heisO ψ V W (w + GlobalTheory.IsoMean.emb V W P Q y) F₁ u * star (F₁' u) ∂ν) ∂μ = ∫ y, (∫ u in 𝓕, heisO ψ V W (w + GlobalTheory.IsoMean.emb V W P Q y) F₂ u * star (F₂' u) ∂ν) ∂μ) → GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 F₁ 0 * star (GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 F₁' 0) = GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 F₂ 0 * star (GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 F₂' 0) := by
  first | exact @GlobalTheory.IsoMean.meanX_prod_zero_eq | exact GlobalTheory.IsoMean.meanX_prod_zero_eq | (intros; apply GlobalTheory.IsoMean.meanX_prod_zero_eq <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.period_integrable_bounded_by_product_of_norms : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Mem.Vol.FiniteVolume₂ → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ t ∈ MultT θ M J χ, ∀ (v : GlobalTheory.Unf.Vol V) (F : GA D V → ℂ), GlobalTheory.Unf.IsContAut V F → (∃ C, ∀ g, ‖F g‖ ≤ C) → (∀ x : SmT M, IntegrableOn (fun g => F g * t x g) v.𝓕 v.μ) ∧ ∃ K : ℝ, ∀ w : M.Vec, ‖∫ g in v.𝓕, F g * t (PiTensorProduct.tprod ℂ w) g ∂v.μ‖ ≤ K * ∏ τ, ‖(w τ : M.H τ)‖ := by
  first | exact @GlobalTheory.PeriodBound.period_bound | exact GlobalTheory.PeriodBound.period_bound | (intros; apply GlobalTheory.PeriodBound.period_bound <;> assumption)
end
