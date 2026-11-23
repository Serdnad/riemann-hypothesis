module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsometryOfLinearIndependent
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
public import GroundTheory.GlobalFields.GlobalArtinMap.ArtinMap
public import CompanionTheory.AutomorphicTheory.PlaceSeparation.IsOpenQuotientMapArt0
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle742
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1241
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittHyperbolicAnisotropicCommuteLevi
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GodementSectionInvariantConvergent
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle023
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle025
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle026
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle481
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle483
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle101
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle603
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle063
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle502
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle596
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle599
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle600
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
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle008
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle002
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.LeftInv
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle005
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.IsTransl
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.IsSliceMap

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ConstTermConj

open GlobalTheory.Cusp GlobalTheory.AutomorphicL2Unitary GlobalTheory.MixModel

section Abstract

variable {G : Type} [Group G] [TopologicalSpace G] {Γ N₁ N₂ : Subgroup G}
  [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [DiscreteTopology Γ]
  [LocallyCompactSpace N₁] [LocallyCompactSpace N₂]

theorem constTermOn_eq_of_conj {φ : G → ℂ} (hφ : LeftInv Γ φ) {γ : G} (hγ : γ ∈ Γ)
    (hN : ∀ n, n ∈ N₁ ↔ γ * n * γ⁻¹ ∈ N₂) (x : G) :
    constTermOn Γ N₂ φ x = constTermOn Γ N₁ φ (γ⁻¹ * x) := by
  let e : N₁ ≃ₜ* N₂ :=
    { toFun := fun n => ⟨γ * n * γ⁻¹, (hN _).1 n.2⟩
      invFun := fun n => ⟨γ⁻¹ * n * γ, (hN _).2 (by simp [mul_assoc])⟩
      left_inv := fun n => by simp [mul_assoc]
      right_inv := fun n => by simp [mul_assoc]
      map_mul' := fun a b => by simp [mul_assoc]
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let m := e.toHomeomorph.toMeasurableEquiv
  have h := isFundamentalDomain_stdDom (Γ.subgroupOf N₂) (Measure.haar.map e)
  have hp : MeasurePreserving m Measure.haar (Measure.haar.map e) := ⟨m.measurable, rfl⟩
  have h' : IsFundamentalDomain (Γ.subgroupOf N₁) (m ⁻¹' stdDom (Γ.subgroupOf N₂)) Measure.haar :=
    h.preimage_of_equiv hp.quasiMeasurePreserving
      (e := fun δ => ⟨e.symm δ, mul_mem (mul_mem (inv_mem hγ) δ.2) hγ⟩)
      ⟨fun a b hab => Subtype.ext (e.symm.injective (congrArg Subtype.val hab)),
        fun δ => ⟨⟨e δ, mul_mem (mul_mem hγ δ.2) (inv_mem hγ)⟩, Subtype.ext (e.symm_apply_apply _)⟩⟩
      fun δ n => (map_mul e _ _).trans (congrArg (· * e n) (e.apply_symm_apply _))
  rw [constTermOn_eq h hφ, constTermOn_eq h' hφ, ← hp.setIntegral_preimage_emb m.measurableEmbedding,
    measureReal_def, measureReal_def, hp.measure_preimage h.nullMeasurableSet]
  refine congrArg _ (integral_congr_ae (.of_forall fun n => ?_))
  change φ (γ * n * γ⁻¹ * x) = φ (n * (γ⁻¹ * x))
  rw [mul_assoc, mul_assoc, hφ γ hγ]

end Abstract

variable {D : D7} {V : HSp D} {r : ℕ}

theorem rat_mulVec_inc {n m : ℕ} (A : Matrix (Fin n) (Fin m) D.host.E) (x : Fin m → D.host.E) :
    (rat A).mulVec (fun i => incA D (x i)) = fun i => incA D ((A.mulVec x) i) := by
  funext i

  simp [Matrix.mulVec, dotProduct, rat, map_sum]

theorem conj_conditions {C₁ C₂ : Matrix (Fin V.rank) (Fin r) D.host.E}
    (g₀ gi : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (h1 : g₀ * gi = 1)
    (hC : g₀ * C₁ = C₂) (hC' : gi * C₂ = C₁) (hH : C₂ᴴ * V.gram * g₀ = C₁ᴴ * V.gram)
    (m : Mx D V.rank V.rank) (a1 : m * rat C₁ = 0) (a2 : rat (C₁ᴴ * V.gram) * m = 0)
    (a3 : ∀ x : Fin V.rank → D.host.E, (C₁ᴴ * V.gram).mulVec x = 0 →
      ∃ a : Fin r → AE D, m.mulVec (fun i => incA D (x i)) = (rat C₁).mulVec a) :
    (rat g₀ * m * rat gi) * rat C₂ = 0 ∧ rat (C₂ᴴ * V.gram) * (rat g₀ * m * rat gi) = 0 ∧
      ∀ x : Fin V.rank → D.host.E, (C₂ᴴ * V.gram).mulVec x = 0 →
        ∃ a : Fin r → AE D, (rat g₀ * m * rat gi).mulVec (fun i => incA D (x i)) = (rat C₂).mulVec a := by
  refine ⟨?_, ?_, fun x hx => ?_⟩
  · rw [Matrix.mul_assoc, ← rat_mul, hC', Matrix.mul_assoc, a1, Matrix.mul_zero]
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← rat_mul, hH, a2, Matrix.zero_mul]
  · have hy : (C₁ᴴ * V.gram).mulVec (gi.mulVec x) = 0 := by
      rw [← hH, Matrix.mulVec_mulVec, Matrix.mul_assoc (C₂ᴴ * V.gram) g₀ gi, h1, Matrix.mul_one, hx]
    obtain ⟨a, ha⟩ := a3 _ hy
    refine ⟨a, ?_⟩
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, rat_mulVec_inc, ha, Matrix.mulVec_mulVec, ← rat_mul, hC]

theorem conj_mem_NI {C₁ C₂ : Matrix (Fin V.rank) (Fin r) D.host.E} (γ : GA D V)
    (g₀ gi : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (h1 : g₀ * gi = 1) (h2 : gi * g₀ = 1)
    (hu : g₀ᴴ * V.gram * g₀ = V.gram) (hm : mt V γ = rat g₀) (hmi : mt V γ⁻¹ = rat gi)
    (hC : g₀ * C₁ = C₂) {n : GA D V} (hn : n ∈ NI V C₁) : γ * n * γ⁻¹ ∈ NI V C₂ := by
  have hC' : gi * C₂ = C₁ := by rw [← hC, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  have hH : C₂ᴴ * V.gram * g₀ = C₁ᴴ * V.gram := by
    rw [← hC, Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc g₀ᴴ, hu]
  have ii' : rat g₀ * rat gi = (1 : Mx D V.rank V.rank) := by rw [← rat_mul, h1, rat_one]
  have hle : NI V C₁ ≤ (NI V C₂).comap (MulAut.conj γ).toMonoidHom := by
    refine (Subgroup.closure_le _).2 fun g hg => Subgroup.subset_closure ?_
    obtain ⟨a1, a2, a3⟩ := hg
    have em : (matHom V ((MulAut.conj γ).toMonoidHom g)).1 - 1 = rat g₀ * ((matHom V g).1 - 1) * rat gi := by
      have e : (matHom V ((MulAut.conj γ).toMonoidHom g)).1 = mt V γ * mt V g * mt V γ⁻¹ := rfl
      rw [e, hm, hmi, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, ii']
      rfl
    have := conj_conditions g₀ gi h1 hC hC' hH _ a1 a2 a3
    rw [← em] at this
    exact this
  exact hle hn

theorem rank_eq_of_isIsoFrame {C : Matrix (Fin V.rank) (Fin r) D.host.E} (h : IsIsoFrame V C) : C.rank = r := by
  have := LinearIndependent.rank_matrix (M := Cᵀ) h.2.1
  simpa [Matrix.rank_transpose] using this

theorem constTerm_eq_zero_of_frame : ∀ (D : D7) (V : HSp D) (r : ℕ) (C₁ C₂ : Matrix (Fin V.rank) (Fin r) D.host.E)
    (h₁ : IsIsoFrame V C₁) (h₂ : IsIsoFrame V C₂) (φ : GA D V → ℂ), (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) →
    GlobalTheory.Cusp.constTerm (GlobalTheory.Cusp.frameFlag h₁) φ = 0 → GlobalTheory.Cusp.constTerm (GlobalTheory.Cusp.frameFlag h₂) φ = 0 := by
  intro D V r C₁ C₂ h₁ h₂ φ hφ h0
  have hθ : (1 / 2 : D.host.E) + star (1 / 2 : D.host.E) = 1 := by
    have e : star (1 / 2 : D.host.E) = 1 / 2 := by simp
    rw [e, add_halves]
  have e₁ : C₁ᴴ * V.gram * C₁ = 0 := h₁.2.2
  have e₂ : C₂ᴴ * V.gram * C₂ = 0 := h₂.2.2
  obtain ⟨g₀, hu, hC⟩ := GlobalTheory.WittTrace.exists_isometry_mul_eq D.host.E (1 / 2) hθ V.rank r V.gram C₁ C₂
    (gram_conjTranspose V) (gram_isUnit_det V) (rank_eq_of_isIsoFrame h₁) (rank_eq_of_isIsoFrame h₂) (e₁.trans e₂.symm)
  obtain ⟨gi, hgi⟩ : ∃ gi, gi = V.gram⁻¹ * (g₀ᴴ * V.gram) := ⟨_, rfl⟩
  have h2 : gi * g₀ = 1 := by
    rw [hgi, Matrix.mul_assoc, hu, Matrix.nonsing_inv_mul _ (gram_isUnit_det V)]
  have h1 : g₀ * gi = 1 := mul_eq_one_comm.1 h2
  have hC' : gi * C₂ = C₁ := by rw [← hC, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  have hu' : giᴴ * V.gram * gi = V.gram := by
    calc giᴴ * V.gram * gi = giᴴ * (g₀ᴴ * V.gram * g₀) * gi := by rw [hu]
      _ = (g₀ * gi)ᴴ * V.gram * (g₀ * gi) := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = V.gram := by rw [h1]; simp
  have hh : adj (rat g₀) * (gA V * rat g₀) = gA V := by
    rw [← rat_conjTranspose, gA, ← rat_mul, ← rat_mul, ← Matrix.mul_assoc, hu]
  obtain ⟨γ, hm⟩ : ∃ γ : GA D V, mt V γ = rat g₀ := ⟨ofMat V (rat g₀) hh, mt_ofMat V _ hh⟩
  have hmi : mt V γ⁻¹ = rat gi := by
    have e := mt_mul_inv V γ
    rw [hm] at e
    calc mt V γ⁻¹ = (rat gi * rat g₀) * mt V γ⁻¹ := by rw [← rat_mul, h2, rat_one, Matrix.one_mul]
      _ = rat gi := by rw [Matrix.mul_assoc, e, Matrix.mul_one]
  have hγ : γ ∈ GQ V := (mem_GQ_iff V γ).2 (hm ▸ rat_mem g₀)
  have hN : ∀ n, n ∈ NA (frameFlag h₁) ↔ γ * n * γ⁻¹ ∈ NA (frameFlag h₂) := fun n => by
    rw [NA_frameFlag, NA_frameFlag]
    refine ⟨conj_mem_NI γ g₀ gi h1 h2 hu hm hmi hC, fun h => ?_⟩
    have := conj_mem_NI γ⁻¹ gi g₀ h2 h1 hu' hmi (by simpa using hm) hC' h
    simpa [mul_assoc] using this
  funext x
  exact (constTermOn_eq_of_conj hφ hγ hN x).trans (congrFun h0 _)

end GlobalTheory.CompanionTheory.ConstTermConj

end
end

section

open NumberField
open scoped nonZeroDivisors
open scoped GlobalTheory.Idele

noncomputable section

namespace GlobalTheory.CompanionTheory.EllipticCM

theorem exists_conj_eq_on_algebraicClosure {K : Type} [Field K] [Algebra K ℂ]
    (σ : ℂ ≃ₐ[K] ℂ) (ι : AlgebraicClosure K →ₐ[K] ℂ)
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (hσ : ∀ x, σ (ι x) = ι (g x))
    (e : algebraicClosure K ℂ ≃ₐ[K] AlgebraicClosure K) :
    ∃ ρ : algebraicClosure K ℂ ≃ₐ[K] algebraicClosure K ℂ,
      ∀ y : algebraicClosure K ℂ,
        (((ρ * ((e.trans g).trans e.symm) * ρ⁻¹) y : algebraicClosure K ℂ) : ℂ) = σ (y : ℂ) := by
  let ι' : algebraicClosure K ℂ →ₐ[K] ℂ := ι.comp (e : algebraicClosure K ℂ →ₐ[K] AlgebraicClosure K)
  have hmem : ∀ y, ι' y ∈ (algebraicClosure K ℂ).toSubalgebra := fun y =>
    mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic y).algHom ι')
  let ρ₀ : algebraicClosure K ℂ →ₐ[K] algebraicClosure K ℂ :=
    ι'.codRestrict (algebraicClosure K ℂ).toSubalgebra hmem
  let ρ : algebraicClosure K ℂ ≃ₐ[K] algebraicClosure K ℂ :=
    AlgEquiv.ofBijective ρ₀ (Algebra.IsAlgebraic.algHom_bijective ρ₀)
  have hρ : ∀ w, ((ρ w : algebraicClosure K ℂ) : ℂ) = ι (e w) := fun _ => rfl
  refine ⟨ρ, fun y => ?_⟩
  obtain ⟨z, rfl⟩ := ρ.surjective y
  have h1 : (ρ * ((e.trans g).trans e.symm) * ρ⁻¹) (ρ z) = ρ (e.symm (g (e z))) := by
    simp [AlgEquiv.mul_apply, AlgEquiv.aut_inv]
  rw [h1, hρ, hρ, hσ, AlgEquiv.apply_symm_apply]

theorem exists_globalArtinMap_tied : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Algebra K ℂ], Module.finrank ℚ K = 2 → ∃ Art₀ : Neutral.B1.IdeleClassGroup K →* Field.absoluteGaloisGroupAbelianization K, Neutral.B1.IsGlobalArtinMap K Art₀ ∧ ∀ (σ : ℂ ≃ₐ[K] ℂ) (s : Neutral.B1.Ideles K), GlobalTheory.EllipticCM.RestrictsTo σ (Art₀ (QuotientGroup.mk s)) → ∀ x : GroundTheory.LocalField.maximalAbelianExtension K (algebraicClosure K ℂ), ((GroundTheory.Global.artinMap K (algebraicClosure K ℂ) (GroundTheory.Global.IdeleClassGroup.mk K s) x : algebraicClosure K ℂ) : ℂ) = σ ((x : algebraicClosure K ℂ) : ℂ) := by
  intro K _ _ _ _ _
  let e : algebraicClosure K ℂ ≃ₐ[K] AlgebraicClosure K := IsAlgClosure.equiv K _ _
  obtain ⟨Art, hArt, hArtσ⟩ := GlobalTheory.LatVal.exists_globalArtinMap
    (CompanionTheory.FamInh.isGlobalArtin_inv (E := K) (Ω := algebraicClosure K ℂ)) e
  obtain ⟨φ, -, hφb, hφ⟩ := GlobalTheory.HeckeGal.exists_abMap_of_algEquiv e
  refine ⟨Art, hArt, ?_⟩
  rintro σ s ⟨ι, g, hσ, hg⟩ x
  obtain ⟨ρ, hρ⟩ := exists_conj_eq_on_algebraicClosure σ ι g hσ e
  obtain ⟨τ, hτ⟩ := GlobalTheory.HeckeGal.toAb_surjective (E := K) (Ω := algebraicClosure K ℂ)
    (CompanionTheory.FamInh.art0 K (algebraicClosure K ℂ) s)
  have h1 : Art (QuotientGroup.mk s) = Neutral.B1.toAb K ((e.symm.trans τ).trans e) :=
    hArtσ s τ (by rw [hτ, MonoidHom.inv_apply, inv_inv])
  have h2 : (e.symm.trans ((e.trans g).trans e.symm)).trans e = g := by
    ext y
    simp
  have h3 : GlobalTheory.HeckeGal.toAb K (algebraicClosure K ℂ) ((e.trans g).trans e.symm) =
      GlobalTheory.HeckeGal.toAb K (algebraicClosure K ℂ) τ :=
    hφb.1 (by rw [hφ, hφ, h2, hg, h1])
  have h4 : GlobalTheory.HeckeGal.toAb K (algebraicClosure K ℂ) (ρ * ((e.trans g).trans e.symm) * ρ⁻¹) =
      CompanionTheory.FamInh.art0 K (algebraicClosure K ℂ) s := by
    rw [map_mul, map_mul, map_inv, h3, hτ, mul_comm (GlobalTheory.HeckeGal.toAb K _ ρ), mul_inv_cancel_right]
  have h5 := GroundTheory.LocalField.topologicalAbelianizationEquiv_mk_apply K (algebraicClosure K ℂ)
    (ρ * ((e.trans g).trans e.symm) * ρ⁻¹) x
  have h6 : GroundTheory.LocalField.topologicalAbelianizationEquiv K (algebraicClosure K ℂ)
      (((ρ * ((e.trans g).trans e.symm) * ρ⁻¹ : algebraicClosure K ℂ ≃ₐ[K] algebraicClosure K ℂ)) :
        TopologicalAbelianization (algebraicClosure K ℂ ≃ₐ[K] algebraicClosure K ℂ)) =
      GroundTheory.Global.artinMap K (algebraicClosure K ℂ) (GroundTheory.Global.IdeleClassGroup.mk K s) := by
    refine Eq.trans (congrArg (GroundTheory.LocalField.topologicalAbelianizationEquiv K (algebraicClosure K ℂ)) h4) ?_
    exact (GroundTheory.LocalField.topologicalAbelianizationEquiv K (algebraicClosure K ℂ)).apply_symm_apply _
  rw [h6] at h5
  rw [h5, hρ]

end GlobalTheory.CompanionTheory.EllipticCM

end
end

section

noncomputable section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.QKAvg

variable {D : D7} {B W : HSp D} {t : ℕ} (d : HypDec B W t)

def radN : Subgroup (GlobalTheory.RegSW.stab d) where
  carrier := {q | ∃ (c : skewA D t) (b : Mx D t W.rank), (q : GA D B) = d.nC c * d.nB b}
  mul_mem' := by
    rintro x y ⟨c, b, hx⟩ ⟨c', b', hy⟩
    refine ⟨c + c' + cComm W b b', b + b', ?_⟩
    rw [Subgroup.coe_mul, hx, hy, HypDec.nC_add, HypDec.nC_add]
    calc d.nC c * d.nB b * (d.nC c' * d.nB b')
        = d.nC c * (d.nB b * d.nC c') * d.nB b' := by group
      _ = d.nC c * (d.nC c' * d.nB b) * d.nB b' := by rw [d.nC_mul_nB]
      _ = d.nC c * d.nC c' * (d.nB b * d.nB b') := by group
      _ = d.nC c * d.nC c' * (d.nB (b + b') * d.nC (cComm W b b')) := by rw [d.nB_mul_nB]
      _ = d.nC c * d.nC c' * (d.nC (cComm W b b') * d.nB (b + b')) := by rw [d.nC_mul_nB]
      _ = _ := by group
  one_mem' := ⟨0, 0, by simp [d.nC_zero, d.nB_zero]⟩
  inv_mem' := by
    rintro x ⟨c, b, hx⟩
    refine ⟨-c, -b, ?_⟩
    rw [Subgroup.coe_inv, hx, mul_inv_rev, d.nB_inv, d.nC_inv, d.nC_mul_nB]

def levM : Subgroup (GlobalTheory.RegSW.stab d) where
  carrier := {q | ∃ (g : GA D W) (a : GL (Fin t) (AE D)), (q : GA D B) = d.emb0 g * d.levi a}
  mul_mem' := by
    rintro x y ⟨g, a, hx⟩ ⟨g', a', hy⟩
    refine ⟨g * g', a * a', ?_⟩
    rw [Subgroup.coe_mul, hx, hy, map_mul, map_mul]
    calc d.emb0 g * d.levi a * (d.emb0 g' * d.levi a')
        = d.emb0 g * (d.levi a * d.emb0 g') * d.levi a' := by group
      _ = d.emb0 g * (d.emb0 g' * d.levi a) * d.levi a' := by rw [d.wittHyperbolic_anisotropic_commute_levi]
      _ = _ := by group
  one_mem' := ⟨1, 1, by simp⟩
  inv_mem' := by
    rintro x ⟨g, a, hx⟩
    refine ⟨g⁻¹, a⁻¹, ?_⟩
    rw [Subgroup.coe_inv, hx, mul_inv_rev, map_inv, map_inv, ← map_inv, ← map_inv, d.wittHyperbolic_anisotropic_commute_levi]

theorem mem_radN {q : GlobalTheory.RegSW.stab d} :
    q ∈ radN d ↔ ∃ (c : skewA D t) (b : Mx D t W.rank), (q : GA D B) = d.nC c * d.nB b := Iff.rfl

theorem mem_levM {q : GlobalTheory.RegSW.stab d} :
    q ∈ levM d ↔ ∃ (g : GA D W) (a : GL (Fin t) (AE D)), (q : GA D B) = d.emb0 g * d.levi a := Iff.rfl

theorem exists_radN_mul_levM (q : GlobalTheory.RegSW.stab d) : ∃ n ∈ radN d, ∃ m ∈ levM d, q = n * m := by
  obtain ⟨b, c, g, e⟩ := GlobalTheory.GodementSectionReduction.exists_decomp d q
  refine ⟨⟨d.nC c * d.nB b, mul_mem (GlobalTheory.GodementSectionReduction.nC_mem d c) (GlobalTheory.GodementSectionReduction.nB_mem d b)⟩, ⟨c, b, rfl⟩,
    ⟨d.emb0 g * d.levi (GlobalTheory.RegSW.onX d q), mul_mem (GlobalTheory.GodementSectionReduction.wittCoreEmbedding_mem_isotropicStabilizer d g) (GlobalTheory.RegSW.levi_mem d _)⟩, ⟨g, _, rfl⟩, ?_⟩
  apply Subtype.ext
  rw [Subgroup.coe_mul, e, ← d.nC_mul_nB]
  simp only [mul_assoc]

theorem conj_coord (g : GA D W) (a : GL (Fin t) (AE D)) (c : skewA D t) (b : Mx D t W.rank) :
    (d.emb0 g * d.levi a) * (d.nC c * d.nB b) * (d.emb0 g * d.levi a)⁻¹ =
      d.nC (skewConj a.1 c) * d.nB (a.1 ⬝ b ⬝ mt W g⁻¹) := by
  have h : d.emb0 g * d.levi a * (d.nC c * d.nB b) =
      d.nC (skewConj a.1 c) * d.nB (a.1 ⬝ b ⬝ mt W g⁻¹) * (d.emb0 g * d.levi a) := by
    calc d.emb0 g * d.levi a * (d.nC c * d.nB b)
        = d.emb0 g * (d.levi a * d.nC c) * d.nB b := by group
      _ = d.emb0 g * d.nC (skewConj a.1 c) * (d.levi a * d.nB b) := by rw [d.levi_mul_nC]; group
      _ = d.emb0 g * d.nC (skewConj a.1 c) * (d.nB (a.1 ⬝ b) * d.levi a) := by rw [d.levi_mul_nB]
      _ = d.nC (skewConj a.1 c) * (d.emb0 g * d.nB (a.1 ⬝ b)) * d.levi a := by rw [d.wittHyperbolic_anisotropic_commute_nC]; group
      _ = _ := by rw [d.wittHyperbolic_anisotropic_conj_nB]; group
  rw [h, mul_inv_cancel_right]

instance radN_normal : (radN d).Normal := by
  refine ⟨fun n hn q => ?_⟩
  obtain ⟨n₁, hn₁, m, ⟨g, a, hm⟩, rfl⟩ := exists_radN_mul_levM d q
  obtain ⟨c, b, hc⟩ := hn
  have h : m * n * m⁻¹ ∈ radN d := ⟨skewConj a.1 c, a.1 ⬝ b ⬝ mt W g⁻¹, by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hm, hc, conj_coord]⟩
  have e : n₁ * m * n * (n₁ * m)⁻¹ = n₁ * (m * n * m⁻¹) * n₁⁻¹ := by group
  rw [e]
  exact mul_mem (mul_mem hn₁ h) (inv_mem hn₁)

end GlobalTheory.CompanionTheory.QKAvg
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.Inf0 GlobalTheory.CompanionTheory.SW.BB

namespace GlobalTheory.CompanionTheory.WeilSiegel.Inf0

theorem fibre_rapid_zero_eq_density : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (h₀ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b), ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (μ : Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)) (ν : Measure (HermR (Ainf F) σ 1)) (m : HermR (Ainf F) σ 1 → Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFibFree (Ainf F) σ J 1 μ ν m → ∀ φ : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ, Continuous φ → (∀ X, 0 ≤ φ X) → RapidDecay b (fun X => (φ X : ℂ)) → ∀ D : HermR (Ainf F) σ 1 → ℝ, Continuous D → (∀ U : Set (HermR (Ainf F) σ 1), MeasurableSet U → ∫⁻ X in gramR (Ainf F) σ J ⁻¹' (Subtype.val '' U), ENNReal.ofReal (φ X) ∂μ = ∫⁻ S in U, ENNReal.ofReal (D S) ∂ν) → ∫⁻ X, ENNReal.ofReal (φ X) ∂(m (hermOf (Ainf F) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀)) = ENNReal.ofReal (D (hermOf (Ainf F) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀)) := by
  intro F E _ _ _ _ _ σ hCM M J hJ hM h₀ d b μ ν m hμ hν hm φ hφc hφ0 hφr D hDc hD
  obtain ⟨ρ, e, hρ, he, heρ, hen, -⟩ := GlobalTheory.T.infinite_adele_haar_map_eq_scaled_volume F hCM.1
  have hd : d = 2 := by
    have h := Module.finrank_eq_card_basis b
    simpa [hCM.2.2.1] using h.symm
  have hLoc : IsLocR (Ainf F) := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hCM.1
  obtain ⟨hTR, hLC, hSC, hT2, -, -, -, -⟩ := id hLoc
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨hKr, hKl, hKs, hK2, -, -, -, hVb, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (Ainf F)
  haveI := hKr
  haveI := hKl
  haveI := hKs
  haveI := hK2
  haveI := hVb 1 M
  obtain ⟨hXl, hXs, hX2, hXb, hlift⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hCM (Ainf F) 1
  haveI := hXl
  haveI := hXs
  haveI := hX2
  haveI := hXb
  obtain ⟨g, hgc, hgf⟩ := hlift M J hJ
  have hreal : ∀ (A Pm : InfinitePlace F → Matrix (Fin M × Fin d) (Fin M × Fin d) ℝ) (Di : (InfinitePlace F → ℝ) → ℝ), Continuous Di → (∀ U : Set (InfinitePlace F → ℝ), MeasurableSet U → ∫⁻ x in qR0 A ⁻¹' U, ENNReal.ofReal (gaussR Pm x) = ∫⁻ y in U, ENNReal.ofReal (Di y)) → ∀ f : (InfinitePlace F → Fin M × Fin d → ℝ) → ℝ, Measurable f → (∀ x, 0 ≤ f x) → (∀ N : ℕ, ∃ C' : ℝ, ∀ x, f x * (1 + ∑ w, ‖x w‖) ^ N ≤ C') → ∀ ε : ℝ, 0 < ε → ∃ δ R : ℝ, 0 < δ ∧ 0 < R ∧ ∀ U : Set (InfinitePlace F → ℝ), MeasurableSet U → ∫⁻ x in qR0 A ⁻¹' U ∩ (coreR δ R)ᶜ, ENNReal.ofReal (f x) ≤ ENNReal.ofReal ε * volume U := by
    intro A Pm Di hDi hdens f hf hf0 hfr ε hε
    have hcard : Fintype.card (Fin M × Fin d) = M * 2 := by simp [hd]
    obtain ⟨C, hC⟩ := GlobalTheory.T.quadratic_box_volume_bound (InfinitePlace F) (Fin M × Fin d) A Pm Di (by omega) hDi hdens
    have hQ : Measurable (qR0 A : (InfinitePlace F → Fin M × Fin d → ℝ) → _) := by
      refine Continuous.measurable (continuous_pi fun w => continuous_const.mul ?_)
      exact (continuous_apply w).dotProduct (continuous_const.matrix_mulVec (continuous_apply w))
    exact GlobalTheory.T.quadratic_box_integral_small_ball (InfinitePlace F) (Fin M × Fin d) _ (by omega) (qR0 A) hQ C hC f hf hf0 hfr ε hε
  refine GlobalTheory.T.disintegration_injective_open_map _ _ _ μ ν (gramR (Ainf F) σ J) g Subtype.val Subtype.val_injective hgc hgf _ m (GlobalTheory.CompanionTheory.WeilSiegel.FreeOpen.isOpen_free F E σ hCM (Ainf F) hLoc 1 M) hm φ hφc hφ0 D hDc hD ?_ _
  intro ε hε
  obtain ⟨δ, R, hδ, hR, hK, hb⟩ := GlobalTheory.T.archimedean_rank_one_volume_bound F E σ hCM M J hJ hM d b ρ e hρ he heρ hen hreal μ ν hμ hν φ hφc hφ0 hφr ε hε
  refine ⟨_, hK, ?_, hb⟩
  intro X hX
  refine GlobalTheory.T.archimedean_rank_one_free_of_places F E σ hCM M d b ρ e hρ he heρ X fun w h => ?_
  have h1 := (hX w).1
  have h2 : ‖(fun w => xw e b X w) w‖ = 0 := by
    show ‖xw e b X w‖ = 0
    rw [h, norm_zero]
  linarith

end GlobalTheory.CompanionTheory.WeilSiegel.Inf0
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.twisted_lattice_sums_bounded_product : ∀ {D : D7} {ρ p : ℕ} (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ b₀ : HermE D ρ, b₀.1.det ≠ 0 → ∀ (Φ φ : Mx D ρ p → ℂ) (B₁ B₂ : ℝ), StronglyMeasurable Φ → StronglyMeasurable φ → (∀ y, Summable (fun ξ : Matrix (Fin ρ) (Fin p) D.host.E => ‖Φ (GlobalTheory.CompanionTheory.FJE.rt ξ + y)‖) ∧ ∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, ‖Φ (GlobalTheory.CompanionTheory.FJE.rt ξ + y)‖ ≤ B₁) → (∀ y, Summable (fun ξ : Matrix (Fin ρ) (Fin p) D.host.E => ‖φ (GlobalTheory.CompanionTheory.FJE.rt ξ + y)‖) ∧ ∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, ‖φ (GlobalTheory.CompanionTheory.FJE.rt ξ + y)‖ ≤ B₂) → ∫ v in m.𝓕 ×ˢ m.𝓕, GlobalTheory.CompanionTheory.FJE.Ap ψ b₀ Φ φ v ∂(m.μ.prod m.μ) = ∫ y, Φ y * conj (φ y) ∂m.μ := by
  first | exact @GlobalTheory.CompanionTheory.FJE.fold_parseval | exact GlobalTheory.CompanionTheory.FJE.fold_parseval | (intros; apply GlobalTheory.CompanionTheory.FJE.fold_parseval <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.block_integral_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)), IsInt w (blk h w m X).val ↔ IsInt w m.1.val ∧ IsInt w m.2.val ∧ IsInt w (m.1.val * X) := by
  first | exact @GlobalTheory.CompanionTheory.CtS.isInt_blk_iff | exact GlobalTheory.CompanionTheory.CtS.isInt_blk_iff | (intros; apply GlobalTheory.CompanionTheory.CtS.isInt_blk_iff <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.block_inverse_integral_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (ϖ : w.adicCompletion E) (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)), IsInt w (ϖ • ((blk h w m X)⁻¹).val) ↔ IsInt w (ϖ • (m.1⁻¹).val) ∧ IsInt w (ϖ • (m.2⁻¹).val) ∧ IsInt w (ϖ • (X * (m.2⁻¹).val)) := by
  first | exact @GlobalTheory.CompanionTheory.CtS.isInt_smul_blk_inv_iff | exact GlobalTheory.CompanionTheory.CtS.isInt_smul_blk_inv_iff | (intros; apply GlobalTheory.CompanionTheory.CtS.isInt_smul_blk_inv_iff <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.lattice_indicator_integral_index : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (Λ : AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E))), intSub a b w ≤ Λ → hint (intMat a b w) (fun X => if Multiplicative.toAdd X ∈ Λ then (1 : ℂ) else 0) = (((intSub a b w).relIndex Λ : ℕ) : ℂ) := by
  first | exact @GlobalTheory.CompanionTheory.HintInd.hint_indicator_lattice | exact GlobalTheory.CompanionTheory.HintInd.hint_indicator_lattice | (intros; apply GlobalTheory.CompanionTheory.HintInd.hint_indicator_lattice <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.diagonal_lattice_index_pow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (ϖ : w.adicCompletion E), IsUnifV E w ϖ → ∀ (i j : ℕ), i ≤ a → j ≤ b → (intSub a b w).relIndex (latD ϖ a b i j) = (qV E w) ^ (i * (b - j)) := by
  first | exact @GlobalTheory.CompanionTheory.CtS.LatDiag.relIndex_intSub_latD | exact GlobalTheory.CompanionTheory.CtS.LatDiag.relIndex_intSub_latD | (intros; apply GlobalTheory.CompanionTheory.CtS.LatDiag.relIndex_intSub_latD <;> assumption)
end
