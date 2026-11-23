module

import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletedLatticeStabilizerCompactOpen
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle034
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle023
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.BaseChangeTensorProduct
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle007
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle005
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.HalfGeometricCovers
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NotIsOfFinOrderUnitQuot
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle072
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle004
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SignatureEmbeddingCoverComp
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle035

@[expose] public section

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

namespace GlobalTheory.LevelOpen

theorem exists_cut {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A) (e : A)
    (he : e * e = e) (hσ : σ e = e) (g : GL (Fin n) A) (hg : g ∈ Formalism.UG.UJ σ J) :
    ∃ k ∈ Formalism.UG.UJ σ J, k.1 = e • g.1 + (1 - e) • (1 : Matrix (Fin n) (Fin n) A) := by
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, he, mul_one, sub_self]
  have h2 : (1 - e) * e = 0 := by rw [mul_comm, h1]
  have h3 : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, h1, one_mul, sub_zero]
  have key : ∀ X Y Z W : Matrix (Fin n) (Fin n) A,
      (e • X + (1 - e) • Z) * (e • Y + (1 - e) • W) = e • (X * Y) + (1 - e) • (Z * W) := by
    intro X Y Z W
    simp only [add_mul, mul_add, smul_mul_smul_comm, he, h1, h2, h3, zero_smul, add_zero, zero_add]
  have one : ∀ X : Matrix (Fin n) (Fin n) A, e • X + (1 - e) • X = X := by
    intro X; rw [← add_smul, add_sub_cancel, one_smul]
  refine ⟨⟨e • g.1 + (1 - e) • 1, e • (g⁻¹).1 + (1 - e) • 1, ?_, ?_⟩, ?_, rfl⟩
  · rw [key, Units.mul_inv, one_mul, one]
  · rw [key, Units.inv_mul, one_mul, one]
  · have hg' : Formalism.UG.cT σ g.1 * J * g.1 = J := hg
    change Formalism.UG.cT σ (e • g.1 + (1 - e) • 1) * J * (e • g.1 + (1 - e) • 1) = J
    have hc : Formalism.UG.cT σ (e • g.1 + (1 - e) • (1 : Matrix (Fin n) (Fin n) A)) =
        e • Formalism.UG.cT σ g.1 + (1 - e) • 1 := by
      ext i j
      by_cases h : i = j
      · subst h; simp [Formalism.UG.cT, hσ]
      · simp [Formalism.UG.cT, hσ, Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h)]
    rw [hc]
    conv_lhs => rw [← one J]
    rw [key, key, hg', one_mul, mul_one, one]

theorem congr_mem_nhds (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG) (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (N : ℕ) (hN : 0 < N) :
    {m : Matrix (Fin n) (Fin n) (Af F ⊗[F] E) | ∀ z ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)),
      ∃ y ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)), m.mulVec z - z = N • y} ∈
      𝓝 (1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) := by
  apply GlobalTheory.Mem.Vol.StabGroup.congr_mem_nhds <;> assumption

theorem continuous_fin (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] :
    Continuous (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) : AF F ⊗[F] E → Af F ⊗[F] E) := by
  have : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : ContinuousAdd (Af F ⊗[F] E) := IsModuleTopology.toContinuousAdd (Af F) _
  have : ContinuousSMul (Af F) (Af F ⊗[F] E) := IsModuleTopology.toContinuousSMul _ _
  let φ : AF F ⊗[F] E →ₛₗ[(sndA F).toRingHom] Af F ⊗[F] E :=
    { toFun := Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)
      map_add' := map_add _
      map_smul' := fun a x => by
        rw [Algebra.smul_def, Algebra.smul_def, map_mul]
        rfl }
  have hs : Continuous ((sndA F).toRingHom : AF F → Af F) := continuous_snd
  exact IsModuleTopology.continuous_of_linearMapₛₗ hs φ

theorem exists_finPart_mat {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (g : GL (Fin n) (AF F ⊗[F] E)) (hg : g ∈ HR (AF F) σ J) :
    ∃ k ∈ HR (AF F) σ J, Formalism.UG.bc (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom k = 1 ∧
      Formalism.UG.bc (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom k =
        Formalism.UG.bc (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom g := by
  let e : AF F ⊗[F] E := pairA F 0 1 ⊗ₜ 1
  have he : e * e = e := by
    simp only [e, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    congr 1
    exact Prod.ext (mul_zero _) (mul_one _)
  have hσ : sigR (AF F) σ e = e := by
    simp [e, sigR]
  obtain ⟨k, hk, hke⟩ := exists_cut _ (JR (AF F) J) e he hσ g hg
  have h0 : Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) e = 0 :=
    TensorProduct.zero_tmul _ _
  have h1 : Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) e = 1 := rfl
  refine ⟨k, hk, Units.ext ?_, Units.ext ?_⟩
  · change k.1.map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) = 1
    ext i j
    rw [hke]
    by_cases h : i = j
    · subst h; simp [h0]
    · simp [h0, Matrix.one_apply_ne h]
  · ext i j
    change Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (k.1 i j) =
      Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (g.1 i j)
    rw [hke]
    simp [h1]

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_finPart (D : D7) (V : HSp D) (g : GA D V) : ∃ k ∈ GfC V, finHom V k = finHom V g := by
  let g' : HR (AF D.host.F) D.sp.cm.sig V.gram := g
  obtain ⟨k, hk, h1, h2⟩ := exists_finPart_mat D.sp.cm.sig V.gram (matHom V g) g'.2
  let k' : HR (AF D.host.F) D.sp.cm.sig V.gram := ⟨k, hk⟩
  exact ⟨k', h1, h2⟩

theorem level_mem_nhds : ∀ (D : D7) (V : HSp D) (N : ℕ) (Kf : Subgroup (GA D V)), 0 < N → IsLevelK V N Kf → ∀ g₀ : GA D V, {g : GA D V | ∃ k ∈ Kf, ∃ h ∈ GinfC V, g = g₀ * k * h} ∈ 𝓝 g₀ := by
  intro D V N Kf hN hK g₀
  have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (AF D.host.F) _
  have : IsTopologicalGroup (GA D V) :=
    inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  let ψ : V.V →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E) :=
    V.frame.equivFun.toLinearMap.restrictScalars (𝓞 D.host.E)
  let L := V.L0.map ψ
  have hfg : L.FG := V.standardTuple_isLattice.fg.map ψ
  have hL : Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤ := by
    have hspan : Submodule.span D.host.E (V.L0 : Set V.V) = ⊤ := by
      let W := Submodule.span D.host.E (V.L0 : Set V.V)
      change W = ⊤
      by_contra h
      let e : V.V ≃ₗ⋆[D.host.E] V.V :=
        (V.frame.equivFun.trans (starLinearEquiv D.host.E)).trans V.frame.equivFun.symm
      let g : V.V →ₗ[D.host.E] Module.Dual D.host.E W :=
        (LinearMap.domRestrict' W).comp (V.hT.comp e.toLinearMap)
      have hdim : Module.finrank D.host.E (Module.Dual D.host.E W) <
          Module.finrank D.host.E V.V := by
        rw [Subspace.dual_finrank_eq]
        exact Submodule.finrank_lt h
      obtain ⟨z, hz, hz₀⟩ :=
        Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
      have hsmul (a : D.host.E) : a • e z ∈ V.L0 := by
        rw [← V.baseLattice_isUnimodular]
        simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual,
          Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
        intro y hy
        have hzy : V.hT (e z) y = 0 :=
          congrArg (fun f : Module.Dual D.host.E W => f ⟨y, Submodule.subset_span hy⟩)
            (LinearMap.mem_ker.mp hz)
        have hyz : V.hT y (e z) = 0 := by
          have hh := V.herm.eq (e z) y
          simpa [hzy] using hh.symm
        simp [hyz]
      let i : D.host.E →ₗ[𝓞 D.host.E] V.L0 :=
        ((LinearMap.toSpanSingleton D.host.E _ (e z)).restrictScalars (𝓞 D.host.E)).codRestrict V.L0 hsmul
      let : Module.Finite (𝓞 D.host.E) V.L0 := Module.Finite.iff_fg.mpr V.standardTuple_isLattice.fg
      let : Module.Finite (𝓞 D.host.E) D.host.E := Module.Finite.of_injective i fun a b hab =>
        smul_left_injective D.host.E (fun hzero => hz₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
      exact RingOfIntegers.not_isField D.host.E
        (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 D.host.E) D.host.E) (Field.toIsField D.host.E))
    have h := congrArg (Submodule.map (V.frame.equivFun : V.V →ₗ[D.host.E] (Fin V.rank → D.host.E)))
      hspan
    rw [Submodule.map_span, Submodule.map_top, LinearEquiv.range] at h
    exact h
  have hhat : GlobalTheory.AdLat.hat D.host.F (L : Set (Fin V.rank → D.host.E)) = latHat V := by
    unfold GlobalTheory.AdLat.hat latHat
    congr 1
    ext z
    constructor
    · rintro ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨a, ha, x, hx, rfl⟩
    · rintro ⟨a, ha, x, hx, rfl⟩
      exact ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
  have hn := congr_mem_nhds D.host.F D.host.E V.rank L hfg hL N hN
  rw [hhat] at hn
  have hm : Continuous fun g : GA D V => (matHom V g).1 :=
    Units.continuous_val.comp continuous_subtype_val
  have hf : Continuous fun g : GA D V => (finHom V g).1 := hm.matrix_map (continuous_fin D.host.F D.host.E)
  have hc : Continuous fun g : GA D V => (finHom V (g₀⁻¹ * g)).1 := hf.comp (continuous_const_mul g₀⁻¹)
  have h1 := hc.continuousAt.preimage_mem_nhds (x := g₀) (by rw [inv_mul_cancel, map_one]; exact hn)
  refine Filter.mem_of_superset h1 fun g hg => ?_
  obtain ⟨k, hk, hkg⟩ := exists_finPart D V (g₀⁻¹ * g)
  refine ⟨k, (hK k).mpr ⟨hk, by rw [hkg]; exact hg⟩, k⁻¹ * (g₀⁻¹ * g), ?_, by group⟩
  change finHom V _ = 1
  rw [map_mul, map_inv, hkg, inv_mul_cancel]

end GlobalTheory.LevelOpen
end

section



noncomputable section

namespace GlobalTheory.ReadingComparison

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps
  ReciprocityTheory.ChartRestriction.G.PullbackSections
open scoped TensorProduct
open GlobalTheory.IndefiniteRowSideFullHecke

section General

variable {K L : Type} [Field K] [Field L] [Algebra K L] {σ : K →+* ℂ} {σ' : L →+* ℂ}
  {C W : Type} [AddCommGroup C] [Module K C] [AddCommGroup W] [Module ℂ W]

theorem bcMap_tmul (hσ : ∀ a, σ' (algebraMap K L a) = σ a) (f : C →ₛₗ[σ] W) (t : L) (x : C) :
    BaseChangeTensorProduct.bcMap hσ f (t ⊗ₜ x) = σ' t • f x := rfl

theorem linearIndependent_of_indepToC {f : C →ₛₗ[σ] W} (hf : IndepToC f) {ι : Type} {b : ι → C}
    (hb : LinearIndependent K b) : LinearIndependent ℂ (fun i => f (b i)) := by
  rw [linearIndependent_iff_finset_linearIndependent]
  intro s
  have e := s.equivFin
  have h1 := hf _ (fun i => b (e.symm i).1) (hb.comp (fun i => (e.symm i).1)
    (Subtype.val_injective.comp e.symm.injective))
  have h2 := h1.comp e e.injective
  convert h2 using 1
  funext i
  simp

theorem indepToC_bcMap_iff (hσ : ∀ a, σ' (algebraMap K L a) = σ a) (f : C →ₛₗ[σ] W) :
    IndepToC (BaseChangeTensorProduct.bcMap hσ f) ↔ IndepToC f := by
  constructor
  · intro h n b hb
    have h1 := h n (fun i => (1 : L) ⊗ₜ[K] b i) (Module.Flat.linearIndependent_one_tmul hb)
    simpa only [bcMap_tmul, map_one, one_smul] using h1
  · intro h n b hb
    letI : Algebra K ℂ := σ.toAlgebra
    letI : Algebra L ℂ := σ'.toAlgebra
    haveI : IsScalarTower K L ℂ := IsScalarTower.of_algebraMap_eq fun a => (hσ a).symm
    letI : Module K W := Module.compHom W σ
    haveI : IsScalarTower K ℂ W := ⟨fun a z w => by
      show (σ a * z) • w = σ a • z • w
      rw [mul_smul]⟩
    let g : C →ₗ[K] W :=
      { toFun := f, map_add' := map_add f, map_smul' := fun a x => f.map_smulₛₗ a x }
    let F : ℂ ⊗[K] C →ₗ[ℂ] W := g.liftBaseChange ℂ
    let e := Module.Basis.ofVectorSpace K C
    have hF : Function.Injective F := by
      refine LinearMap.injective_of_linearIndependent (Algebra.TensorProduct.basis ℂ e).span_eq ?_
      have h0 := linearIndependent_of_indepToC h e.linearIndependent
      have e1 : (F ∘ Algebra.TensorProduct.basis ℂ e) = fun i => f (e i) := by
        funext i
        simp only [Function.comp, Algebra.TensorProduct.basis_apply, F, LinearMap.liftBaseChange_one_tmul]
        rfl
      rw [e1]; exact h0
    let φ := TensorProduct.AlgebraTensorModule.cancelBaseChange K L ℂ ℂ C
    have h1 : LinearIndependent ℂ (fun i => (1 : ℂ) ⊗ₜ[L] b i) := Module.Flat.linearIndependent_one_tmul hb
    have h2 := h1.map' (F ∘ₗ φ.toLinearMap) (LinearMap.ker_eq_bot.2 (hF.comp φ.injective))
    have key : ∀ x : L ⊗[K] C, F (φ ((1 : ℂ) ⊗ₜ[L] x)) = BaseChangeTensorProduct.bcMap hσ f x := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul t x =>
        rw [bcMap_tmul]
        simp only [φ, F, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, LinearMap.liftBaseChange_tmul]
        show (σ' t * 1) • f x = _
        rw [mul_one]
      | add x y hx hy => rw [TensorProduct.tmul_add, map_add (f := _), map_add (f := _), hx, hy, map_add (f := _)]
    have e2 : (fun i => BaseChangeTensorProduct.bcMap hσ f (b i)) = (F ∘ₗ φ.toLinearMap) ∘ fun i => (1 : ℂ) ⊗ₜ[L] b i :=
      funext fun i => (key (b i)).symm
    rw [e2]; exact h2

end General

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ)

end GlobalTheory.ReadingComparison
end
end

section

open MeasureTheory Topology Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume
open scoped ENNReal

theorem _root_.GlobalTheory.T.exists_discrete_arithGroupImage_realUnitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), ∃ Λ : Subgroup (RealGrp X), (∀ s, s ∈ Λ ↔ ∃ γ ∈ X.Γ, lact γ (baseFr X) = frameOf X s) ∧ ∃ W ∈ 𝓝 (1 : RealGrp X), ∀ w ∈ Λ, w ∈ W → w = 1 := by
  first | exact @GlobalTheory.ArithImage.exists_discrete_image | exact GlobalTheory.ArithImage.exists_discrete_image | (intros; apply GlobalTheory.ArithImage.exists_discrete_image <;> assumption)
end

section


set_option linter.unusedSectionVars false

noncomputable section

namespace GlobalTheory.ClassTieCompare

open Formalism.L2.Pj NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.ComplexResidueRing GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDeterminantRoot GlobalTheory.IndefiniteRowSideFullHecke.HalfGeometricCovers
open GlobalTheory.XiDetCompare (Reads TrivRat TrivFix XiValC XiValAtC embOf Reaches)
open Formalism.L2.PjFree (Unf.ofPj)
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Scalar

variable {D : D7} (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) {n : ℕ}

def IsDetOf (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (𝔠 : Ideal (𝓞 D.host.E)) : Prop :=
  𝔠 ⊔ barI H 𝔠 = ⊤ ∧ Submodule.span (𝓞 D.host.E) (detSet L) * idlE (barI H 𝔠) = idlE 𝔠

def GenOff (bad : ℕ) (𝔠 : Ideal (𝓞 D.host.E)) (x : (AE D)ˣ) : Prop :=
  infPart D (x : AE D) = 1 ∧ Generates ((finU D x : IdF D) : AdE D.host.F D.host.E) 𝔠 ∧
    ((finU D x : IdF D) : AdE D.host.F D.host.E) - 1 ∈ idHat D.host.F (Ideal.span {(bad : 𝓞 D.host.E)})

def ReadsId {K : IntermediateField ℚ ℂ} (χ : (AE D)ˣ →* Circle) (bad : ℕ) (B : Ideal (𝓞 D.host.E) → K) : Prop :=
  ∀ 𝔠 x, GenOff bad 𝔠 x → ((B 𝔠 : K) : ℂ) = ((χ x : Circle) : ℂ) * ((Real.sqrt (Ideal.absNorm 𝔠 : ℝ) : ℝ) : ℂ)

def SquareLaw (n bad r : ℕ) : Prop :=
  ∀ (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (𝔠 : Ideal (𝓞 D.host.E)), GlobalTheory.ClassScalarCompare.Guard H bad L →
    IsDetOf H L 𝔠 → ∃ q : ℚ, 0 < q ∧
      q ^ 2 * (((L ⊓ stdLat D.host.E n).toAddSubgroup.addSubgroupOf L.toAddSubgroup).index : ℚ) ^ r = (Ideal.absNorm 𝔠 : ℚ)

variable {H} {Dw : Datum H} {l : Level H} {c : Coeff l}

theorem isDetOf_unique {L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {a b : Ideal (𝓞 D.host.E)} (ha : IsDetOf H L a)
    (hb : IsDetOf H L b) : a = b := by
  have e : idlE (a * barI H b) = idlE (b * barI H a) := by
    have m : ∀ I J : Ideal (𝓞 D.host.E), idlE (I * J) = idlE I * idlE J := fun I J =>
      Submodule.map_mul I J (Algebra.ofId (𝓞 D.host.E) D.host.E)
    rw [m, m, ← ha.2]
    conv_rhs => rw [← hb.2]
    ring
  have e' : a * barI H b = b * barI H a :=
    Submodule.map_injective_of_injective (f := Algebra.linearMap (𝓞 D.host.E) D.host.E)
      (FaithfulSMul.algebraMap_injective (𝓞 D.host.E) D.host.E) e
  exact le_antisymm
    (Ideal.le_of_dvd ((Ideal.isCoprime_iff_sup_eq.2 hb.1).dvd_of_dvd_mul_right ⟨_, e'⟩))
    (Ideal.le_of_dvd ((Ideal.isCoprime_iff_sup_eq.2 ha.1).dvd_of_dvd_mul_right ⟨_, e'.symm⟩))

theorem exists_epIs_iff (bad : ℕ) (B : Ideal (𝓞 D.host.E) → c.F) :
    (∃ epF : Submodule (𝓞 D.host.E) (Fin n → D.host.E) → c.F, EpIs (Dw := Dw) c bad B epF) ↔
      SquareLaw H n bad (Dw.p + Dw.q) := by
  classical
  constructor
  · rintro ⟨epF, h⟩ L 𝔠 g h1
    obtain ⟨q, q0, q1, -⟩ := h L 𝔠 g.1 g.2.1 g.2.2 h1.1 h1.2
    exact ⟨q, q0, q1⟩
  · intro h
    have key : ∀ L : Submodule (𝓞 D.host.E) (Fin n → D.host.E), ∃ v : c.F, ∀ 𝔠, GlobalTheory.ClassScalarCompare.Guard H bad L →
        IsDetOf H L 𝔠 → ∃ q : ℚ, 0 < q ∧
          q ^ 2 * (((L ⊓ stdLat D.host.E n).toAddSubgroup.addSubgroupOf L.toAddSubgroup).index : ℚ) ^ (Dw.p + Dw.q) =
            (Ideal.absNorm 𝔠 : ℚ) ∧ v = (B 𝔠)⁻¹ * (q : c.F) := by
      intro L
      by_cases hL : ∃ 𝔠, GlobalTheory.ClassScalarCompare.Guard H bad L ∧ IsDetOf H L 𝔠
      · obtain ⟨𝔠, g, h1⟩ := hL
        obtain ⟨q, q0, q1⟩ := h L 𝔠 g h1
        refine ⟨(B 𝔠)⁻¹ * (q : c.F), fun 𝔠' _ h2 => ?_⟩
        obtain rfl := isDetOf_unique h1 h2
        exact ⟨q, q0, q1, rfl⟩
      · exact ⟨0, fun 𝔠 g h1 => absurd ⟨𝔠, g, h1⟩ hL⟩
    choose epF hepF using key
    exact ⟨epF, fun L 𝔠 g1 g2 g3 h1 h2 => hepF L 𝔠 ⟨g1, g2, g3⟩ ⟨h1, h2⟩⟩

end Scalar

section Value

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {n r : ℕ}
variable (V : HSp D) (hr : V.rank = r)

section One

variable {c : Coeff l} {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (dict : GA D V → Σ k, Frame (U.X k).Ψ r)
  (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)

variable {V hr U dict ι x₀} {c0 : ℂ} {xi : (AdE D.host.F D.host.E)ˣ →* ℂˣ} {ξ : IdF D →* Circle} {f : Rul Xo c}

end One

section Diag

variable {V} {c : Coeff l} {σ : c.F →+* ℂ} {U : Unf Xo c σ V.rank} {dict : GA D V → Σ k, Frame (U.X k).Ψ V.rank}
  {ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)} {x₀ : (D.host.E →+* ℂ) → Matrix (Fin V.rank) (Fin V.rank) ℂ}
  {g : ℕ}

end Diag

section Compare

variable {V hr} {c : Coeff l} {σ : c.F →+* ℂ} {U : Unf Xo c σ r} {dict : GA D V → Σ k, Frame (U.X k).Ψ r}
  {ι : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)} {x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ}
  {c0 : ℂ} {xi : (AdE D.host.F D.host.E)ˣ →* ℂˣ} {ξ : IdF D →* Circle} {f : Rul Xo c}

end Compare

end Value

section Record

variable {D : D7} {T : CoreJ D} {X : ThetaX D} (Tt : ThetaTied D X) (j : ℕ) {c' : Coeff T.Q.l} (h : T.Q.c.F ≤ c'.F)
  (ka : WeightFamilies.Wt D j) (lam : D.what₂.Tau → DomWeight D.R.nV)
  (PQ : D.what₂.Tup → Ideal (𝓞 D.host.E)) (β : Fin D.R.r → (T.Q.Dw j).La)
  (Cl : D.what₂.Tup → Type) [∀ t, Fintype (Cl t)]
  (Lh : ∀ t, Cl t → Submodule (𝓞 D.host.E) (Fin D.R.nV → D.host.E)) (gam : ∀ t, Cl t → ℕ) (vol : D.what₂.Tup → c'.F)
  (thAd : ∀ t, (Cl t → VVc c' lam) → AutQ (T.V j (sig0 T.Q.c)) → ℂ) (Pl : ∀ t, (Cl t → VVc c' lam) → Prop) (ph : ℂ)
  (ξ : D.what₂.Tup → IdF D →* Circle) (bad : D.what₂.Tup → ℕ)
  (d : D.what₂.Tup → DeltaDat (T.Q.Xo j) c' D.R.nV)
  (φ : ∀ t, (Fin D.R.nV → LevQc (T.Q.Dw j) (d t).l₂) → c'.F)
  (w : ∀ t, Cl t → (Fin D.R.nV → LevQ (T.Q.Dw j) (d t).l₂) → c'.F)
  (La : ∀ t, Cl t → GenLat D.host.E D.R.nV) (Nc : ∀ t, Cl t → ℕ) (ep : ∀ t, Cl t → c'.F)
  (io : VVc c' lam →ₗ[c'.F] MvPolynomial (LtN (T.Q.Dw j) D.R.nV) c'.F)
  (hr : (T.V j (sig0 T.Q.c)).rank = D.R.r) (B : D.what₂.Tup → Ideal (𝓞 D.host.E) → c'.F)
  (epF : D.what₂.Tup → Submodule (𝓞 D.host.E) (Fin D.R.nV → D.host.E) → c'.F) (cond : ℕ) (hw : VVc c' lam)
  (U₂ : ∀ t, Unf (d t).Xo₂ (d t).c₂ ((sig0 c').comp ((d t).eF.symm : (d t).c₂.F →+* c'.F)) D.R.r)
  (dict₂ : ∀ t, GA D (T.V j (sig0 T.Q.c)) → Σ k, Frame ((U₂ t).X k).Ψ D.R.r)
  (xi : D.what₂.Tup → (AdE D.host.F D.host.E)ˣ →* ℂˣ)

variable {Tt j h ka lam PQ β Cl Lh gam vol thAd Pl ph ξ bad d φ w La Nc ep io hr B epF cond hw U₂ dict₂ xi}

variable (Tt j h ka lam PQ β Cl Lh gam vol thAd Pl ph ξ bad d φ w La Nc ep io hr B epF cond hw U₂ dict₂ xi)

end Record

end GlobalTheory.ClassTieCompare
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw

theorem _root_.GlobalTheory.T.theorem_of_cube_two_projective_factors : ∀ (k : Type) [Field k] (X Y Z : Over (Sp k)) (x₀ : 𝟙_ (Over (Sp k)) ⟶ X) (y₀ : 𝟙_ (Over (Sp k)) ⟶ Y) (z₀ : 𝟙_ (Over (Sp k)) ⟶ Z), Smooth X.hom → Smooth Y.hom → IsProper X.hom → IsProper Y.hom → IsProjBy X.hom → IsProjBy Y.hom → GeometricallyIntegral X.hom → GeometricallyIntegral Y.hom → ConnectedSpace Z.left → ∀ M : LB (X ⊗ Y ⊗ Z).left, M.IsLB → Triv (M.pull (lift (toUnit (Y ⊗ Z) ≫ x₀) (𝟙 (Y ⊗ Z))).left) → Triv (M.pull (lift (fst X Z) (lift (toUnit (X ⊗ Z) ≫ y₀) (snd X Z))).left) → Triv (M.pull (lift (fst X Y) (lift (snd X Y) (toUnit (X ⊗ Y) ≫ z₀))).left) → Triv M := by
  first | exact @GlobalTheory.CubeGlue.triv_of_triv_faces | exact GlobalTheory.CubeGlue.triv_of_triv_faces | (intros; apply GlobalTheory.CubeGlue.triv_of_triv_faces <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem _root_.GlobalTheory.T.exists_openChart_framedPoint_testRing : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (z : Xo.XF c), ∃ (p : TRing c.F) (j : Sp p.R ⟶ Xo.XF c) (y₀ : FrPt Xo c p.R), OpenChart j y₀ ∧ z ∈ Set.range j := by
  first | exact @GlobalTheory.Frames.exists_openChart_testRing | exact GlobalTheory.Frames.exists_openChart_testRing | (intros; apply GlobalTheory.Frames.exists_openChart_testRing <;> assumption)
end
