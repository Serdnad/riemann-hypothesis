module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle006
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle009
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle320
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle080
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle010
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EqOneOfMembership
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle059
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle125
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle009
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle025
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle321
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle064
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle251
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle010
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinCongMemLevEnv
import Formalism.LocalToGlobal.Columns.CoefColLemmas
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle008
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle009
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle594
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLogDerivQExpansionModPrimePowHeckeNorm
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ApplyAtOriginMinorProductLinear
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle328
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle333
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle001
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaSeriesTies
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace GlobalTheory.ColClassNumber

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.MainNotions.StandardLattice
open GlobalTheory.IndefiniteRowSideFullHecke

theorem card_eq_index_mul_mass {G : Type} [Group G] (Γ U K : Subgroup G) (m : ℝ) (hUK : U ≤ K)
    (hidx : U.relIndex K ≠ 0) (hm : ClassesDoubleCosets.CosetMass Γ K m)
    (hfree : ∀ x γ : G, γ ∈ Γ → x⁻¹ * γ * x ∈ U → γ = 1) :
    (Nat.card (ClassSet Γ U) : ℝ) = (U.relIndex K : ℝ) * m := by
  obtain ⟨hfin, hst, hsum⟩ := hm
  letI : Fintype (ClassSet Γ K) := Fintype.ofFinite _
  have e : ∀ y : G, StabiliserCardinality.stab Γ K y ≃ stabAt Γ K y := fun y =>
    { toFun := fun γ => ⟨⟨γ.1, ((StabiliserCardinality.mem_stab Γ K y _).1 γ.2).1⟩, ((StabiliserCardinality.mem_stab Γ K y _).1 γ.2).2⟩
      invFun := fun γ => ⟨γ.1.1, (StabiliserCardinality.mem_stab Γ K y _).2 ⟨γ.1.2, γ.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hs : ∀ c : ClassSet Γ K, DoubleCoset.mk Γ K (Quotient.out c) = c := fun c => Quotient.out_eq' c
  have h := (GlobalTheory.Proof.DoubleCosetCountGlobalInterpolation.doubleCosetCount G Γ U K hUK ⟨hidx⟩
    (fun y => have := hst y; Finite.of_equiv _ (e y).symm)
    (fun x => (Subgroup.eq_bot_iff_forall _).2 fun γ hγ =>
      hfree x γ ((StabiliserCardinality.mem_stab Γ U x γ).1 hγ).1 ((StabiliserCardinality.mem_stab Γ U x γ).1 hγ).2)
    _ hs).2
  have h' := congrArg (fun q : ℚ => (q : ℝ)) h
  push_cast at h'
  rw [h', ← hsum _ hs]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [one_div, Nat.card_congr (e _)]

section Lattice

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
  [Algebra F E] (sp : Spaces R F E)

theorem exists_lattice (N : Submodule (𝓞 E) (Fin R.k → E)) (hfin : Module.Finite (𝓞 E) N)
    (hspan : Submodule.span E (N : Set (Fin R.k → E)) = ⊤)
    (hdual : dualSet (sp.cm.sig : E →+* E) sp.gram0 N = (N : Set (Fin R.k → E))) :
    ∃ M : Submodule (𝓞 E) (sp.X 0).V, Submodule.IsLattice E M ∧
      Formalism.HermitianLatticesTheory.IsUnimodular (sp.X 0).hT M ∧ sp.crdLat0 M = N := by
  let e : (sp.X 0).V ≃ₗ[𝓞 E] (Fin R.k → E) := sp.crd0.restrictScalars (𝓞 E)
  have hmem : ∀ x, x ∈ N.map (e.symm : (Fin R.k → E) →ₗ[𝓞 E] (sp.X 0).V) ↔ sp.crd0 x ∈ N := fun x => by
    rw [Submodule.mem_map_equiv]; rfl
  refine ⟨N.map (e.symm : (Fin R.k → E) →ₗ[𝓞 E] (sp.X 0).V), ?_, ?_, ?_⟩
  · exact Submodule.IsLattice.of_fg E ((Module.Finite.iff_fg.1 hfin).map _)
  · ext x
    rw [hmem, ← SetLike.mem_coe (p := N), ← hdual]
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
      LinearMap.restrictScalars_apply, Submodule.mem_one, hmem, sp.hermitianForm_base_coordinates, dualSet, Set.mem_setOf_eq,
      RingHom.mem_range]
    constructor
    · intro h y hy
      have := h (sp.crd0.symm y) (by simpa using hy)
      simpa using this
    · intro h y hy
      exact h _ hy
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hmem x).1 hx
    · intro hy
      exact ⟨sp.crd0.symm y, (hmem _).2 (by simpa using hy), by simp⟩

end Lattice

theorem idx_pos (D : D7) : 0 < idxPi D (D.host.g 0) (D.host.g 1) := by
  have h : ∀ g k : ℕ, g.Prime → 0 < idxColLoc g k := by
    intro g k hg
    haveI : NeZero g := ⟨hg.ne_zero⟩
    haveI : Nonempty {A : GL (Fin k) (ZMod g) // IsUnitri (A : Matrix (Fin k) (Fin k) (ZMod g))} :=
      ⟨⟨1, fun i j h => by simp [h.ne'], fun i => by simp⟩⟩
    exact div_pos (Nat.cast_pos.2 Nat.card_pos) (Nat.cast_pos.2 Nat.card_pos)
  exact mul_pos (pow_pos (h _ _ (D.host.g_prime 0)) _) (pow_pos (h _ _ (D.host.g_prime 1)) _)

theorem mass_selfDualLattice_firstSpace_eq (D : D7) : letI := D.host.cmStar
    ∀ M : Submodule (𝓞 D.host.E) (D.sp.X 0).V, Submodule.IsLattice D.host.E M →
      Formalism.HermitianLatticesTheory.IsUnimodular (D.sp.X 0).hT M → Formalism.HermitianLatticesTheory.mass (D.sp.X 0).hT M = massI D D.R.k := by
  letI := D.host.cmStar
  intro M hM hu
  rw [← D.sp.rank0]
  exact GlobalTheory.genusMassStd D { D.sp.X 0 with L0 := M, standardTuple_isLattice := hM, baseLattice_isUnimodular := hu } (D.sp.X_sig 0)
    (baseSpace_posDef _ _ D.sp)

theorem classNumber (hover : SplittingProjection.SelfDualOverBase) (hindex : SelfDualLatticeIndex.StabiliserLevelIndexFormula)
    (hcos : ClassesDoubleCosets.ClassesAsDoubleCosets) (hstab : ColumnStabiliser.ColStabTrivial)
    (D : D7) (Lv : LevelData D) : ClassNumberFormula₂ D Lv := by
  letI := D.host.cmStar
  intro hg hs u hT
  obtain ⟨-, N, ⟨hfin, hspan, hdual, -⟩, -, -, hUK⟩ := hover D Lv u hT
  obtain ⟨M, hM, hu, rfl⟩ := exists_lattice D.sp N hfin hspan hdual
  have hidx := hindex D Lv u hs hT _ ⟨hfin, hspan, hdual.symm⟩ hUK
  have hm := hcos.2 D Lv u M hM hu
  rw [mass_selfDualLattice_firstSpace_eq D M hM hu] at hm
  have hrel := Subgroup.relIndex_subgroupOf (H := SelfDualLatticeIndex.levelU D Lv u)
    (SelfDualLatticeIndex.stabHat_le D (D.sp.crdLat0 M))
  have hne : (SelfDualLatticeIndex.levelU D Lv u).relIndex (SelfDualLatticeIndex.stabHat D (D.sp.crdLat0 M)) ≠ 0 := by
    intro h0
    rw [h0, Nat.cast_zero] at hidx
    exact (mul_pos (idx_pos D) (SelfDualLatticeIndex.factorT_pos D u)).ne hidx
  have h := card_eq_index_mul_mass _ ((Lv u).U.subgroupOf _) _ _ (Subgroup.comap_mono hUK)
    (hrel.trans_ne hne) hm (by
      intro x γ hγ hx
      have h1 := ColumnStabiliser.map_colStab D Lv u x
      rw [hstab D Lv u hg hs x, Subgroup.map_bot] at h1
      have h2 : γ.1 ∈ (⊥ : Subgroup _) := by
        rw [h1]
        exact ⟨hγ, ⟨_, hx, by simp [mul_assoc]⟩⟩
      exact Subtype.ext (Subgroup.mem_bot.1 h2))
  rw [Nat.card_eq_of_bijective _ (Lv u).y_bij]
  refine h.trans ?_
  rw [mul_assoc (massI D D.R.k), mul_comm (massI D D.R.k)]
  exact congrArg (· * massI D D.R.k) ((congrArg (fun n : ℕ => (n : ℝ)) hrel).trans hidx)

theorem classNumber_of_index (hover : SplittingProjection.SelfDualOverBase) (hindex : SelfDualLatticeIndex.StabiliserLevelIndexFormula)
    (D : D7) (Lv : LevelData D) : ClassNumberFormula₂ D Lv :=
  classNumber hover hindex (GlobalTheory.Proof.CosetGroupEquiv.massAsCosetSum_iff.1 GlobalTheory.Proof.TotallyDefiniteMass.massAsCosetSum)
    (GlobalTheory.Proof.StabilizerGroupMap.columnStabilisersTrivial_iff.1 GlobalTheory.Proof.EqOneOfMembership.columnStabilisersTrivial) D Lv

end GlobalTheory.ColClassNumber

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT NumberField
open GlobalTheory.IndefiniteRowSideFullHecke.RationalFormValues (IsCoefExt RationalValues RationalValuesAt ValuesIn)
open GlobalTheory.Proof.PlaceExtensionValues

namespace GlobalTheory.RationalValuesObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Coef

variable {K K' : Type} [Field K] [Field K'] {σ : K →+* ℂ} {σ' : K' →+* ℂ} {ι : K →+* K'}
  {I : Type} [Fintype I] {n : ℕ} {lam : I → DomWeight n} {W : Type} [AddCommGroup W] [Module ℂ W]
  {c₀ : VV K lam →ₛₗ[σ] W} {c' c'' : VV K' lam →ₛₗ[σ'] W}

theorem exists_basis_val (lam : I → DomWeight n) (ι : K →+* K') (j : VVIdx lam) :
    ∃ v : VV K lam, ((bVV K' lam j : VV K' lam) : Pol K' I n) = MvPolynomial.map ι (v : Pol K I n) := by
  obtain ⟨F, hF, hj⟩ := GlobalTheory.Proof.TensorMapDescent.bVVfun_desc ι lam j
  exact ⟨⟨F, hF⟩, (bVV_coe _ _ _).trans hj⟩

theorem ext_unique (h : IsCoefExt ι lam c₀ c') (h' : IsCoefExt ι lam c₀ c'') : c' = c'' := by
  refine (bVV K' lam).ext fun j => ?_
  obtain ⟨v, hv⟩ := exists_basis_val lam ι j
  rw [h v _ hv, h' v _ hv]

end Coef

section Row

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

theorem existsUnique_c0BC (i : Fin D.R.m) {K' : Type} [Field K'] (jL : D.what₂.LL →+* K') (σ' : K' →+* ℂ)
    (hσ : σ'.comp jL = D.what₂.embLL) (c₀ : VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W) :
    ∃! c' : VsV D i K' →ₛₗ[σ'] (R.cV i).W, CoefficientBaseChange R i jL σ' c₀ c' := by
  obtain ⟨c', hc⟩ := GlobalTheory.Mem.PlaceVal.exists_ext_VV (W := (R.cV i).W) jL σ' hσ (FWT.lamV D i) c₀
  exact ⟨c', hc, fun c'' hc'' => ext_unique ((isCoefExt_iff_c0BC R i jL c₀ c'').2 hc'') ((isCoefExt_iff_c0BC R i jL c₀ c').2 hc)⟩

end Row

end GlobalTheory.RationalValuesObj

end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.OnTies
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HLatMove

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem mulVec_mem_hatL {β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}
    (hβ : IsFrame β Λ) (hx : x ∈ St β) {z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F}
    (hz : z ∈ Formalism.L2.Herm.hatL (F := F) Λ) : x.1 *ᵥ z ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
  obtain ⟨y, rfl⟩ := hx
  rw [hβ] at hz ⊢
  intro i
  have e : (β⁻¹).1 *ᵥ ((frGL β y).1 *ᵥ z) = (intGL F E n y).1 *ᵥ ((β⁻¹).1 *ᵥ z) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]
    congr 2
    change β⁻¹ * (β * intGL F E n y * β⁻¹) = _
    group
  rw [e]
  exact Subring.sum_mem (t := Finset.univ) _ fun j _ => mul_mem (y.1 i j).2 (hz j)

theorem mulVec_mem_hat {β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}
    (hβ : IsFrame β Λ) {q : GL (Fin n) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)}
    (hq : Formalism.UG.bc (Algebra.TensorProduct.comm F _ E).toAlgHom.toRingHom q ∈ St β)
    {z : Fin n → FiniteAdeleRing (𝓞 F) F ⊗[F] E} (hz : z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E))) :
    q.1 *ᵥ z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)) := by
  have h := GlobalTheory.PrincInLevel.swap_symm_mem_hat Λ _
    (mulVec_mem_hatL hβ hq (GlobalTheory.PrincInLevel.swap_mem_hatL Λ z hz))
  convert h using 1
  funext i
  rw [AlgEquiv.eq_symm_apply]

  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
  rfl


omit [NumberField F] [NumberField E] in
theorem bc_map_bc_inclR {R S : Type} [CommRing R] [Algebra F R] [CommRing S] [Algebra F S] (f : R →ₐ[F] S)
    (g : GL (Fin n) E) :
    Formalism.UG.bc (Algebra.TensorProduct.map f (AlgHom.id F E)).toRingHom (Formalism.UG.bc (inclR (F := F) R) g) =
      Formalism.UG.bc (inclR (F := F) S) g := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change Algebra.TensorProduct.map f (AlgHom.id F E) (1 ⊗ₜ g.1 i j) = 1 ⊗ₜ g.1 i j
  rw [Algebra.TensorProduct.map_tmul, map_one]; rfl


omit [NumberField F] [NumberField E] in
theorem span_move {R O : Type} [CommRing R] [Algebra F R] [CommRing O] [Algebra O E] (H : AddSubgroup (Fin n → R ⊗[F] E))
    (g : GL (Fin n) E) (h q : GL (Fin n) (R ⊗[F] E)) (h1 : ∀ z ∈ H, q.1 *ᵥ z ∈ H) (h2 : ∀ z ∈ H, (q⁻¹).1 *ᵥ z ∈ H) :
    Submodule.span O {x : Fin n → E |
        ((Formalism.UG.bc (inclR (F := F) R) g * h * q)⁻¹).1 *ᵥ (fun i => (1 : R) ⊗ₜ[F] x i) ∈ H} =
      (Submodule.span O {x : Fin n → E | (h⁻¹).1 *ᵥ (fun i => (1 : R) ⊗ₜ[F] x i) ∈ H}).map
        ((Matrix.mulVecLin g.1).restrictScalars O) := by
  have hv : ∀ (g : GL (Fin n) E) (x : Fin n → E),
      (Formalism.UG.bc (inclR (F := F) R) g).1 *ᵥ (fun i => (1 : R) ⊗ₜ[F] x i) = fun i => (1 : R) ⊗ₜ[F] (g.1 *ᵥ x) i := by
    intro g x
    funext i
    exact (RingHom.map_mulVec (inclR (F := F) R) g.1 x i).symm
  have key : ∀ z, (q⁻¹).1 *ᵥ z ∈ H ↔ z ∈ H := by
    refine fun z => ⟨fun hz => ?_, h2 z⟩
    have := h1 _ hz
    rwa [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at this
  have hs : ∀ x : Fin n → E,
      ((Formalism.UG.bc (inclR (F := F) R) g * h * q)⁻¹).1 *ᵥ (fun i => (1 : R) ⊗ₜ[F] x i) =
        (q⁻¹).1 *ᵥ ((h⁻¹).1 *ᵥ fun i => (1 : R) ⊗ₜ[F] ((g⁻¹).1 *ᵥ x) i) := by
    intro x
    rw [← hv, map_inv, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul,
      mul_inv_rev, mul_inv_rev, mul_assoc]
  rw [Submodule.map_span]
  congr 1
  ext x
  constructor
  · intro hx
    refine ⟨(g⁻¹).1 *ᵥ x, (key _).1 (hs x ▸ hx), ?_⟩
    change g.1 *ᵥ ((g⁻¹).1 *ᵥ x) = x
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  · rintro ⟨y, hy, rfl⟩
    change _ *ᵥ _ ∈ H
    rw [hs, key]
    change _ *ᵥ (fun i => (1 : R) ⊗ₜ[F] ((g⁻¹).1 *ᵥ (g.1 *ᵥ y)) i) ∈ H
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    exact hy

end General

variable {D : D7}

theorem exists_ratMat (V : HSp D) (γ : GQ V) : ∃ γE : GL (Fin V.rank) D.host.E, Bridge.IsRatMat V γ γE ∧
    (Bridge.ratF V γ).1 = Formalism.UG.bc (inclR (F := D.host.F) (Af D.host.F)) γE := by
  obtain ⟨γE, -, hγ⟩ := γ.2
  have hm : matHom V γ.1 = Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) γE := hγ.symm
  refine ⟨γE, hm, ?_⟩
  change finHom V γ.1 = _
  rw [finHom, MonoidHom.comp_apply, hm]
  exact bc_map_bc_inclR _ _

theorem hLat_eq_span {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hΛ : IsSDFrame V β Λ 1) (h : Bridge.Gf V) :
    Bridge.hLat V h = Submodule.span (𝓞 D.host.E) {x : Fin V.rank → D.host.E |
      (h.1⁻¹).1 *ᵥ (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] x i) ∈
        GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E))} := by
  rw [GlobalTheory.PrincInLevel.eq_latC hΛ, GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq]
  rfl

theorem mulVec_mem_hat_swap {n : ℕ} {β : GL (Fin n) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (hβ : IsFrame β Λ) {q : GL (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E)} (hq : Formalism.UG.bc (swapAE D) q ∈ St β) :
    ∀ z ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin n → D.host.E)),
      q.1 *ᵥ z ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin n → D.host.E)) :=
  fun _ hz => mulVec_mem_hat hβ hq hz

theorem hLat_mul {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hΛ : IsSDFrame V β Λ 1) (g h q : Bridge.Gf V) (γE : GL (Fin V.rank) D.host.E)
    (hf : g.1 = Formalism.UG.bc (inclR (F := D.host.F) (Af D.host.F)) γE) (hq : Formalism.UG.bc (swapAE D) q.1 ∈ St β) :
    Bridge.hLat V (g * h * q) = (Bridge.hLat V h).map ((Matrix.mulVecLin γE.1).restrictScalars (𝓞 D.host.E)) := by
  have hfr : IsFrame β Λ := by obtain ⟨c, h, -⟩ := hΛ; exact h
  have hq' : Formalism.UG.bc (swapAE D) (q.1⁻¹) ∈ St β := by
    rw [MonoidHom.map_inv]; exact (St β).inv_mem hq
  have e : (g * h * q).1 = Formalism.UG.bc (inclR (F := D.host.F) (Af D.host.F)) γE * h.1 * q.1 := hf ▸ rfl
  rw [hLat_eq_span hΛ, hLat_eq_span hΛ, e]
  exact span_move _ γE h.1 q.1 (mulVec_mem_hat_swap hfr hq) (mulVec_mem_hat_swap hfr hq')

theorem hLat_rat_mul_stab : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSDFrame V β Λ 1 → ∀ γ : GQ V, ∃ γE : GL (Fin V.rank) D.host.E, Bridge.IsRatMat V γ γE ∧ ∀ h q : Bridge.Gf V, Formalism.UG.bc (swapAE D) (q : GL (Fin V.rank) _) ∈ St β → Bridge.hLat V (Bridge.ratF V γ * h * q) = Formalism.HermitianLatticesTheory.gmap ((Formalism.L2.Col.toGLm D.host.E V.rank).symm γE) (Bridge.hLat V h) := by
  intro D V β Λ hΛ γ
  obtain ⟨γE, hγ, hf⟩ := exists_ratMat V γ
  refine ⟨γE, hγ, fun h q hq => ?_⟩
  rw [Formalism.L2.Col.gmap_eq_map, MulEquiv.apply_symm_apply]
  exact hLat_mul hΛ _ h q γE hf hq

end GlobalTheory.HLatMove
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.KZ Matrix

namespace GlobalTheory.KZ

theorem exists_fixing_mul_frobAt :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (s : Ω ≃ₐ[ℚ] Ω) (E0 : Finset Ω) (S : Finset ℕ),
      ∃ (s' : Ω ≃ₐ[ℚ] Ω) (q : ℕ), (∀ x ∈ E0, s' x = x) ∧ q.Prime ∧ q ∉ S ∧ FrobAt q (s * s') := by
  intro Ω _ _ _ s E0 S
  have : IsGalois ℚ Ω := {}
  let K : IntermediateField ℚ Ω := IntermediateField.adjoin ℚ (E0 : Set Ω)
  have : FiniteDimensional ℚ K :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hKo : IsOpen (K.fixingSubgroup : Set (G ℚ Ω)) := IntermediateField.fixingSubgroup_isOpen K
  let V : Set (G ℚ Ω) := {φ | s⁻¹ * φ ∈ K.fixingSubgroup}
  have hVo : IsOpen V := hKo.preimage (continuous_const_mul s⁻¹)
  have hVne : V.Nonempty := ⟨s, by simp [V, K.fixingSubgroup.one_mem]⟩
  let T : ℕ := ∏ p ∈ S.filter (· ≠ 0), p
  have hT : T ≠ 0 := Finset.prod_ne_zero_iff.2 fun p hp => (Finset.mem_filter.1 hp).2
  have hS : {v : HeightOneSpectrum (𝓞 ℚ) | (T : 𝓞 ℚ) ∈ v.asIdeal}.Finite :=
    (Ideal.finite_factors (I := Ideal.span {(T : 𝓞 ℚ)}) (by simpa using hT)).subset
      fun _ hv => Ideal.dvd_span_singleton.2 hv
  obtain ⟨φ, hφV, v, hv, hd, B, hB, hφ⟩ :=
    (GlobalTheory.Published.ChebotarevDegreeOne.dense (F := ℚ) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne' hS).inter_open_nonempty
      V hVo hVne
  have h2 : Ideal.absNorm v.asIdeal = normV v := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  have hmem : ((normV v : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := h2 ▸ Ideal.absNorm_mem v.asIdeal
  have hq : (normV v).Prime := by
    rw [← h2]
    exact ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified ℚ).1 v).2 hd
  refine ⟨s⁻¹ * φ, normV v, ?_, hq, ?_, ?_⟩
  · intro x hx
    exact (mem_fixingSubgroup_iff _).1 hφV x (IntermediateField.subset_adjoin ℚ _ (by simpa using hx))
  · intro hqS
    apply hv
    show (T : 𝓞 ℚ) ∈ v.asIdeal
    have hdvd : normV v ∣ T := Finset.dvd_prod_of_mem _ (Finset.mem_filter.2 ⟨hqS, hq.ne_zero⟩)
    obtain ⟨k, hk⟩ := hdvd
    rw [hk, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hmem
  · rw [mul_inv_cancel_left]
    have hqB : B.valuation ((normV v : ℕ) : Ω) < 1 := by
      have := (hB ((normV v : ℕ) : 𝓞 ℚ)).2 hmem
      simpa using this
    refine ⟨B, (ValuationSubring.mem_nonunits_iff _).2 hqB, fun x hx => ?_⟩
    have hx1 : B.valuation x ≤ 1 := (B.valuation_le_one_iff x).2 hx
    have hlt := hφ.2 x hx1
    refine ⟨?_, hlt⟩
    have hxq : x ^ normV v ∈ B := pow_mem hx _
    have hd' : φ x - x ^ normV v ∈ B := (B.valuation_le_one_iff _).1 hlt.le
    simpa using add_mem hd' hxq

end GlobalTheory.KZ

end
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.semisimple_tensor_of_semisimple_potentials : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ {E : Type} [Field E] [Algebra ℤ_[l] E] (ι : E ≃+* ℂ) (lam : Letter → E), SSPotB N l w (fun T => ι (lam T)) → X.SSBB N l w E lam := by
  first | exact @GlobalTheory.KZ.Comp.ssbb_of_ssPotB | exact GlobalTheory.KZ.Comp.ssbb_of_ssPotB | (intros; apply GlobalTheory.KZ.Comp.ssbb_of_ssPotB <;> assumption)
end

section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

theorem _root_.GlobalTheory.T.isLogDerivQExpansionModPrimePow_heckeNorm : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (l : ℕ) [Fact l.Prime] (n : ℕ) (f : X.K) (φ : HahnSeries ℚ Ω),
  X.sl (ofSL ModularGroup.T) f = f → (∀ r : ℚ, φ.coeff r ≠ 0 → r.den = 1) → IsDl X A l n 1 f φ →
  IsDl X A l n 1 (∏ j ∈ Finset.range l, X.sl (toGQ !![1, (j : ℤ); 0, (l : ℤ)]) f) (hq ε l φ) := by
  first | exact @GlobalTheory.NormDl.isDl_norm | exact GlobalTheory.NormDl.isDl_norm | (intros; apply GlobalTheory.NormDl.isDl_norm <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.applyAtOrigin_minorProduct_linear : ∀ (D : D7) (a d : ℕ) (n : D.what₂.Tau → ℕ) (G : VC D a d → ℂ), Differentiable ℂ G → (∀ (u : D.what₂.Tau → Matrix (Fin a) (Fin a) ℂ) (t : Tup D a d n), GL3Theta.applyAt0 D (minorPol D t) (fun z => G (fun τ => (Matrix.of (z τ) * u τ : Matrix _ _ ℂ))) = (∏ τ, (u τ).det ^ n τ) * GL3Theta.applyAt0 D (minorPol D t) G) ∧ (∀ (u : D.what₂.Tau → Matrix (Fin d) (Fin d) ℂ), (∀ τ, u τ ∈ Matrix.unitaryGroup (Fin d) ℂ) → ∑ t : Tup D a d n, ‖GL3Theta.applyAt0 D (minorPol D t) (fun z => G (fun τ => (u τ * Matrix.of (z τ) : Matrix _ _ ℂ)))‖ ^ 2 = ∑ t : Tup D a d n, ‖GL3Theta.applyAt0 D (minorPol D t) G‖ ^ 2) ∧ (∀ (c : ℂ) P, GL3Theta.applyAt0 D P (c • G) = c * GL3Theta.applyAt0 D P G) ∧ ∀ G' P, Differentiable ℂ G' → GL3Theta.applyAt0 D P (G + G') = GL3Theta.applyAt0 D P G + GL3Theta.applyAt0 D P G' := by
  first | exact @GlobalTheory.NormSum.applyAt0_minorPol_linear | exact GlobalTheory.NormSum.applyAt0_minorPol_linear | (intros; apply GlobalTheory.NormSum.applyAt0_minorPol_linear <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.OnTies
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.thetaKernelFiniteAdelic_laws : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t : T0), R.models_inf → R.models_cV → R.thP_ωP → R.thP_pt_theta → R.thP_ioP → GlobalTheory.TraceIncl.DatumType R i t → (∀ h, GlobalTheory.TraceIncl.kern R i t (fin (Vc D i) h) = GlobalTheory.TraceIncl.kernA R i t h) ∧ (∀ (γ : GQ (Vc D i)) h w, GlobalTheory.TraceIncl.kern R i t (Bridge.ratF (Vc D i) γ * h) ((R.cV i).coef.ρ γ w) = GlobalTheory.TraceIncl.kern R i t h w) ∧ (∀ h (k : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).J) w, GlobalTheory.TraceIncl.kern R i t (h * k) w = ((((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ k)⁻¹ : ℂˣ) : ℂ) • GlobalTheory.TraceIncl.kern R i t h w) ∧ ∀ (g0 : G0 R.Pg D.R.r) (q : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q), g0 = rTup (R.βV i) (R.datVt i t) (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf (Vc D i)) : GL _ _)) → (∃ κ', IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ') → ∀ h w v, actL (Wc D i) (R.βW i) (R.datWp i R.triv) g0 (GlobalTheory.TraceIncl.kern R i t (h * q) w v) = ((((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch q)⁻¹ : ℂˣ) : ℂ) • GlobalTheory.TraceIncl.kern R i t h w v := by
  first | exact @GlobalTheory.TraceIncl.kern_laws | exact GlobalTheory.TraceIncl.kern_laws | (intros; apply GlobalTheory.TraceIncl.kern_laws <;> assumption)
end
