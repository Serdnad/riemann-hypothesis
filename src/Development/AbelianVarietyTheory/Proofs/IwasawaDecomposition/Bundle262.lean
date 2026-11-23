module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle253
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle155
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle200
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle008
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle009
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
import Mathlib.Tactic.ENatToNat
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.HorizPt

def strHom {R : Type} [CommRing R] {X : Scheme.{0}} (q : X ⟶ Sp R) (U : X.Opens) : CommRingCat.of R ⟶ Γ(X, U) :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ q.appLE ⊤ U le_top

theorem fromSpec_str {R : Type} [CommRing R] {X : Scheme.{0}} (q : X ⟶ Sp R) {U : X.Opens} (hU : IsAffineOpen U) :
    hU.fromSpec ≫ q = Spec.map (strHom q U) := by
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec q (isAffineOpen_top _) hU le_top, IsAffineOpen.fromSpec_top,
    Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  rfl

theorem charZero {X : Scheme.{0}} (q : X ⟶ Sp ℤ) [Flat q] {U : X.Opens} (hU : IsAffineOpen U)
    [Nontrivial Γ(X, U)] : CharZero Γ(X, U) := by
  have h₁ : (q.appLE ⊤ U le_top).hom.Flat :=
    HasRingHomProperty.appLE @Flat q inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  have h₂ : (strHom q U).hom.Flat :=
    RingHom.Flat.comp (RingHom.Flat.of_bijective
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv)) h₁
  have h₃ : (algebraMap ℤ Γ(X, U)).Flat := by
    rwa [Subsingleton.elim (algebraMap ℤ Γ(X, U)) (strHom q U).hom]
  have := RingHom.flat_algebraMap_iff.1 h₃
  exact charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective ℤ Γ(X, U))

theorem main : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (N : TrueGeo.Model Y) (W : N.X.Opens) (z : N.X) (g : Γ(N.X, W)), z ∈ W → g ≠ 0 → z ∉ N.X.basicOpen g → ∃ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (y : AlgPt Y) (yt : Sp e.O ⟶ N.X), spMap e.O.subtype ≫ yt = y.1 ≫ N.j ∧ ⊤ ≤ yt ⁻¹ᵁ W ∧ yt (IsLocalRing.closedPoint e.O) ∉ N.X.basicOpen g ∧ N.j (below y.1) ∈ N.X.basicOpen g := by
  intro F _ _ Y N W z g hz hg hzg
  have := N.ar.isIntegral
  have := N.ar.flat
  have : IsProper N.p := by
    obtain ⟨n, c, hc, h⟩ := N.ar.isProjOver
    have := isProper_str (𝓞 F) n
    rw [← h]
    infer_instance
  obtain ⟨U, hU, hzU, hUW⟩ := exists_isAffineOpen_mem_and_subset hz
  have hle : U ≤ W := hUW
  have : Nonempty U := ⟨⟨z, hzU⟩⟩
  have : CharZero Γ(N.X, U) := charZero (N.p ≫ spMap (Int.castRingHom (𝓞 F))) hU
  let _ : Algebra (𝓞 F) Γ(N.X, U) := (strHom N.p U).hom.toAlgebra
  have : Algebra.FiniteType (𝓞 F) Γ(N.X, U) :=
    RingHom.FiniteType.comp (N.p.finiteType_appLE (isAffineOpen_top _) hU le_top)
      (RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (𝓞 F))).inv).2)
  set g' : Γ(N.X, U) := N.X.presheaf.map (homOfLE hle).op g with hg'
  have hg0 : g' ≠ 0 := fun h => hg (map_injective_of_isIntegral N.X (homOfLE hle) (by rw [← hg', h, map_zero]))
  have hb : ∀ x : PrimeSpectrum Γ(N.X, U), hU.fromSpec x ∈ N.X.basicOpen g ↔ g' ∉ x.asIdeal := by
    intro x
    have h₁ : hU.fromSpec x ∈ U := by
      have := hU.range_fromSpec
      exact (Set.ext_iff.1 this _).1 ⟨x, rfl⟩
    have h₂ : hU.fromSpec x ∈ N.X.basicOpen g' ↔ g' ∉ x.asIdeal := by
      change x ∈ hU.fromSpec ⁻¹ᵁ N.X.basicOpen g' ↔ _
      rw [hU.fromSpec_preimage_basicOpen]
      rfl
    rw [← h₂, hg', Scheme.basicOpen_res]
    exact ⟨fun h => ⟨h₁, h⟩, fun h => h.2⟩
  have hp : g' ∈ (hU.primeIdealOf ⟨z, hzU⟩).asIdeal := by
    by_contra h
    have := (hb _).2 h
    rw [hU.fromSpec_primeIdealOf] at this
    exact hzg this
  obtain ⟨𝔪, h𝔪, hle'⟩ := Ideal.exists_le_maximal _ (hU.primeIdealOf ⟨z, hzU⟩).isPrime.ne_top
  obtain ⟨v, e, φ, h₁, h₂, h₃⟩ := GlobalTheory.T.exists_ext_place_of_ne_zero_maximal F Γ(N.X, U) 𝔪 h𝔪 g' hg0
  let yt : Sp e.O ⟶ N.X := Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec
  have hw : (spMap e.O.subtype ≫ yt) ≫ N.p =
      spMap (algebraMap F (AlgebraicClosure F)) ≫ spMap (algebraMap (𝓞 F) F) := by
    simp only [yt, Category.assoc]
    rw [fromSpec_str, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    exact h₁ a
  have hy := N.pb.lift_fst _ _ hw
  refine ⟨v, e, ⟨N.pb.lift _ _ hw, N.pb.lift_snd _ _ hw⟩, yt, hy.symm, ?_, ?_, ?_⟩
  · intro x _
    exact hle ((Set.ext_iff.1 hU.range_fromSpec _).1 ⟨_, rfl⟩)
  · intro h
    refine (hb (PrimeSpectrum.comap φ (IsLocalRing.closedPoint e.O))).1 h ?_
    have := hle' hp
    rw [← h₂] at this
    exact this
  · change (N.pb.lift _ _ hw ≫ N.j) (IsLocalRing.closedPoint (AlgebraicClosure F)) ∈ _
    rw [hy]
    refine (hb (PrimeSpectrum.comap φ (PrimeSpectrum.comap e.O.subtype
      (IsLocalRing.closedPoint (AlgebraicClosure F))))).2 fun h => h₃ ?_
    have h' : ((φ g' : e.O) : AlgebraicClosure F) ∈ IsLocalRing.maximalIdeal (AlgebraicClosure F) := h
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at h'
    exact Subtype.ext h'

end GlobalTheory.TrueGeo.HorizPt
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.R3.RowsLvl

section Scale

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem isMultiplicityInner_smul_measure (M : DSModel V S) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (T T' : MMap M) {c : ℝ}
    (hc : 0 < c) {k : ℂ} (h : IsMultIP M μ 𝓕 T T' k) :
    IsMultIP M (ENNReal.ofReal c • μ) 𝓕 T T' ((c : ℂ) * k) := by
  intro v v'
  obtain ⟨hi, he⟩ := h v v'
  refine ⟨?_, ?_⟩
  · unfold IntegrableOn at hi ⊢
    rw [Measure.restrict_smul]
    exact hi.smul_measure ENNReal.ofReal_ne_top
  · rw [Measure.restrict_smul, integral_smul_measure, he, ENNReal.toReal_ofReal hc.le, Complex.real_smul, mul_assoc]

theorem ipM_smul (M : DSModel V S) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (T T' : MMap M) {c : ℝ}
    (hc : 0 < c) (hv : ∃ v : M.Vec, ∏ τ, ⟪(v τ : M.H τ), (v τ : M.H τ)⟫_ℂ ≠ 0) :
    ipM M (ENNReal.ofReal c • μ) 𝓕 T T' = (c : ℂ) * ipM M μ 𝓕 T T' := by
  obtain ⟨v, hv⟩ := hv
  by_cases h : ∃ k, IsMultIP M μ 𝓕 T T' k
  · have hs := isMultiplicityInner_smul_measure M μ 𝓕 T T' hc (ipM_spec M μ 𝓕 T T' h)
    exact hasPeterssonInner_unique M _ 𝓕 T T' v hv (ipM_spec M _ 𝓕 T T' ⟨_, hs⟩) hs
  · have h' : ¬ ∃ k, IsMultIP M (ENNReal.ofReal c • μ) 𝓕 T T' k := by
      rintro ⟨k, hk⟩
      have e : ENNReal.ofReal c⁻¹ • ENNReal.ofReal c • μ = μ := by
        rw [smul_smul, ← ENNReal.ofReal_mul (inv_nonneg.2 hc.le), inv_mul_cancel₀ hc.ne', ENNReal.ofReal_one, one_smul]
      have := isMultiplicityInner_smul_measure M _ 𝓕 T T' (inv_pos.2 hc) hk
      rw [e] at this
      exact h ⟨_, this⟩
    unfold ipM
    rw [dite_eq_right h, dite_eq_right h', mul_zero]

theorem mmap_eq_zero (M : DSModel V S) (hv : ¬ ∃ v : M.Vec, ∏ τ, ⟪(v τ : M.H τ), (v τ : M.H τ)⟫_ℂ ≠ 0) (T : MMap M) :
    T = 0 := by
  classical
  have : ∃ τ, ∀ w : M.sm τ, w = 0 := by
    by_contra hne
    push_neg at hne
    choose w hw using hne
    refine hv ⟨w, Finset.prod_ne_zero_iff.2 fun τ _ => ?_⟩
    rw [inner_self_ne_zero]
    exact fun h0 => hw τ (Subtype.ext h0)
  obtain ⟨τ, hτ⟩ := this
  ext v g
  rw [T.map_coord_zero τ (hτ (v τ))]
  rfl

end Scale

end GlobalTheory.Mem.R3.RowsLvl

namespace GlobalTheory.Mem.R3.RowsLvl



theorem range_eE_and_norm : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → LinearMap.range Y.eE = (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)).comap R.HE.e ∧ ∀ x, ‖Y.eE x‖ ^ 2 = RealDat.nP F.lv2 true * ‖x‖ ^ 2 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP _
  have hE : R.models_HE := hP.char.base.models.HE
  have hEEc : (toChainReal R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop).EEc true =
      (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)).map
        (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).toLinearMap := rfl
  have hlift : Function.Injective (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _) :=
    LinearEquiv.injective _
  refine ⟨?_, fun x => ?_⟩
  · ext h
    constructor
    · rintro ⟨x, rfl⟩
      have hm := (Y.Ish.jE x).2
      rw [Y.eE_read, hEEc] at hm
      obtain ⟨u, hu, he⟩ := hm
      have : u = R.HE.e (Y.eE x) := hlift he
      rw [Submodule.mem_comap, ← this]
      exact hu
    · intro hh
      rw [Submodule.mem_comap] at hh
      have hm : (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _) (R.HE.e h) ∈
          (toChainReal R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop).EEc true := by
        rw [hEEc]; exact ⟨_, hh, rfl⟩
      refine ⟨Y.Ish.jE.symm ⟨_, hm⟩, ?_⟩
      have e1 := Y.eE_read (Y.Ish.jE.symm ⟨_, hm⟩)
      rw [LinearEquiv.apply_symm_apply] at e1
      exact (hE.1 (hlift e1)).symm
  · have hx := Y.tied.sharp.ee x x
    have hy := hE.2.2 (Y.eE x) (Y.eE x)
    have hnP : 0 < RealDat.nP F.lv2 true := by
      unfold RealDat.nP; exact_mod_cast Nat.card_pos
    by_cases hv : ∃ v : (R.MY 0).Vec, ∏ τ, ⟪(v τ : (R.MY 0).H τ), (v τ : (R.MY 0).H τ)⟫_ℂ ≠ 0
    · have e : ⟪x, x⟫_ℂ = (((RealDat.nP F.lv2 true)⁻¹ : ℝ) : ℂ) * ⟪Y.eE x, Y.eE x⟫_ℂ := by
        rw [hx, hy]
        show ipMT _ _ _ _ _ = _
        unfold ipMT
        rw [Y.eE_read]
        erw [LinearEquiv.symm_apply_apply]
        exact ipM_smul _ _ _ _ _ (inv_pos.2 hnP) hv
      rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at e
      have e' : ‖x‖ ^ 2 = (RealDat.nP F.lv2 true)⁻¹ * ‖Y.eE x‖ ^ 2 := by
        apply Complex.ofReal_injective
        rw [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_pow]
        exact e
      rw [e', ← mul_assoc, mul_inv_cancel₀ hnP.ne', one_mul]
    · have h0 : Y.eE x = 0 :=
        hE.1 (by rw [mmap_eq_zero _ hv (R.HE.e (Y.eE x)), mmap_eq_zero _ hv (R.HE.e 0)])
      have h1 : (Y.Ish.jE x).1 = 0 := by
        rw [Y.eE_read, h0, map_zero]; exact map_zero _
      have hx0 : x = 0 := (LinearEquiv.map_eq_zero_iff _).1 (Submodule.coe_eq_zero.1 h1)
      simp [h0, hx0]

end GlobalTheory.Mem.R3.RowsLvl
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows

noncomputable section

namespace GlobalTheory.Mem.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def eigOfType (R : RealDat3 D A3 Ks) (F : Face3 D A3) {X0 : BaseLevelRowSide D} (Y : Read (A3 := A3) R.toRealDat F.lv2 X0)
    (π : D.what₂.FT) : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ :=
  principalLevelFrame.cOfT (Y.PW ⟨0, Y.hm⟩)
    (levS _ (R.βW ⟨0, Y.hm⟩) (R.datWp ⟨0, Y.hm⟩ (R.toRealDat.levL F.lv2 false (sg0 D A3.A))))
    (levChi _ (R.βW ⟨0, Y.hm⟩) (R.datWp ⟨0, Y.hm⟩ (R.toRealDat.levL F.lv2 false (sg0 D A3.A))))
    (SsetF R.toRealDat (Y.tupT D.what₂.mu0)) (principalLevelFrame.rowRepR R.θ (Y.eFT π))

def HasEig (R : RealDat3 D A3 Ks) (F : Face3 D A3) {X0 : BaseLevelRowSide D} (Y : Read (A3 := A3) R.toRealDat F.lv2 X0)
    (π : D.what₂.FT) (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ) : Prop :=
  principalLevelFrame.IsEigOf (Y.PW ⟨0, Y.hm⟩)
    (levS _ (R.βW ⟨0, Y.hm⟩) (R.datWp ⟨0, Y.hm⟩ (R.toRealDat.levL F.lv2 false (sg0 D A3.A))))
    (levChi _ (R.βW ⟨0, Y.hm⟩) (R.datWp ⟨0, Y.hm⟩ (R.toRealDat.levL F.lv2 false (sg0 D A3.A))))
    (SsetF R.toRealDat (Y.tupT D.what₂.mu0)) (principalLevelFrame.rowRepR R.θ (Y.eFT π)) c

theorem hasEig_eigOfType {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
    {Y : Read (A3 := A3) R.toRealDat F.lv2 X0} {π : D.what₂.FT} (h : ∃ c, HasEig R F Y π c) :
    HasEig R F Y π (eigOfType R F Y π) := by
  unfold eigOfType principalLevelFrame.cOfT
  unfold HasEig at h ⊢
  rw [dite_eq_left h]
  exact h.choose_spec

end GlobalTheory.Mem.R3

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section
namespace GlobalTheory.Mem.R3.LamPos

theorem lambdaPrime_basis_row_type_pos_at_reference : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → Lam3 Z → (∀ σ (i : Fin D.R.m), D.what₂.isot ((i : ℕ) + 1) (D.what₂.ft σ) ≠ ⊥) → ∀ σ, ∀ j ∈ Finset.Icc 1 D.R.m, 0 < D.what₂.lamP D.what₂.mu0 j (D.what₂.ft σ) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z _ hH hL hI σ j hj
  obtain ⟨cOf, -, h2, -⟩ := hL
  obtain ⟨h1, hm⟩ := Finset.mem_Icc.1 hj
  have hi : j - 1 < D.R.m := by omega
  have hj' : ((⟨j - 1, hi⟩ : Fin D.R.m) : ℕ) + 1 = j := by simp only; omega
  have key := h2 ⟨j - 1, hi⟩ A3.A.μ0 (D.what₂.ft σ) (Or.inl Y.tup0) (hI σ ⟨j - 1, hi⟩)
  rw [Y.tup0, hj'] at key
  rw [key]
  exact hH.prim.posScal.2 _ _ _ _

end GlobalTheory.Mem.R3.LamPos
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
noncomputable section
namespace GlobalTheory.Mem.R3

theorem liftForm_inner_eq_hform : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → ∀ (i : Fin D.R.m) (t : T) (x y : Fin (lDim D A F.P0 F.ψ0 i t) → D.what₂.LL), (((RealDat.nP F false)⁻¹ : ℝ) : ℂ) * ⟪R.jV i t (liftForm A F.P0 F.ψ0 i t x), R.jV i t (liftForm A F.P0 F.ψ0 i t y)⟫_ℂ = D.what₂.embLL (Formalism.DivisionValues.hform (lH D A F.P0 F.ψ0 i t) x y) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hB i t x y
  have h1 : ∀ f g : (A.MtCSD i t).Forms, ⟪R.jV i t f, R.jV i t g⟫_ℂ = D.what₂.embLL ((A.MtCSD i t).csum f g) := by
    intro f g
    refine ((hB.models.HV i t).2.2 _ _).trans ?_
    refine (congrArg₂ _ (hB.models.jV i t f) (hB.models.jV i t g)).trans ?_
    exact (GlobalTheory.classPres_extMem_extBij_isom _ _ _ _ _ _ _ _ _ _ (R.B.L i t).pres).2.2 f g
  have h2 := GlobalTheory.Mem.LiftForms.csum_lvlForm (A.fam.L i t).S (A.fam.L i t).r (A.fam.lvlA F.P0 F.ψ0).P (A.fam.lvlA F.P0 F.ψ0).ψ x y
  have h3 : ⟪R.jV i t (liftForm A F.P0 F.ψ0 i t x), R.jV i t (liftForm A F.P0 F.ψ0 i t y)⟫_ℂ =
      D.what₂.embLL ((Nat.card (A.fam.lvlA F.P0 F.ψ0).P : D.what₂.LL) * Formalism.DivisionValues.hform (lH D A F.P0 F.ψ0 i t) x y) :=
    (h1 (liftForm A F.P0 F.ψ0 i t x) (liftForm A F.P0 F.ψ0 i t y)).trans (congrArg D.what₂.embLL h2)
  have hP : RealDat.nP F false = (Nat.card F.P0 : ℝ) := rfl
  have hc : (Nat.card F.P0 : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := F.P0)).ne'
  rw [h3, map_mul, map_natCast, hP, ← mul_assoc]
  change ((((Nat.card F.P0 : ℝ))⁻¹ : ℝ) : ℂ) * (Nat.card F.P0 : ℂ) * _ = _
  rw [Complex.ofReal_inv, Complex.ofReal_natCast, inv_mul_cancel₀ hc, one_mul]

end GlobalTheory.Mem.R3
end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.TopGram



theorem topGram : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → ∀ (b : Bool) (t : T) (x y : Fin (rDim D A (F.lvl b).P (F.lvl b).ψ t) → D.what₂.LL), (((RealDat.nP F b)⁻¹ : ℝ) : ℂ) * ⟪R.jX t (rowForm A (F.lvl b).P (F.lvl b).ψ t x), R.jX t (rowForm A (F.lvl b).P (F.lvl b).ψ t y)⟫_ℂ = D.what₂.embLL (Formalism.DivisionValues.hform (rH D A (F.lvl b).P (F.lvl b).ψ t) x y) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hW b t x y
  have hHX := (hW.models.HX t).2.2
  have hjX := hW.models.jX t
  rw [hHX, hjX, hjX]
  have hiso := (GlobalTheory.classPres_extMem_extBij_isom _ _ _ _ _ _ _ _ _ _ (R.B.R t).pres).2.2
  have key : ∀ f f' : A.fam.amb.FR t, Bridge.adInner (Bridge.ratF D.sp.X') (levEnv D.sp.X' R.βX (R.datXt t)).J
      (R.B.R t).pres.y (R.B.jR t f) (R.B.jR t f') = D.what₂.embLL ((A.fam.R t).S.csum f f') := fun f f' => hiso f f'
  have hr : ∀ z, rowForm A (F.lvl b).P (F.lvl b).ψ t z =
      GlobalTheory.Mem.LiftForms.lvlForm (A.fam.R t).S (A.fam.R t).r (A.fam.lvl (F.lvl b).P (F.lvl b).ψ).P
        (A.fam.lvl (F.lvl b).P (F.lvl b).ψ).ψ z := fun z => rfl
  refine (congrArg (fun z => (((RealDat.nP F b)⁻¹ : ℝ) : ℂ) * z) (key (rowForm A (F.lvl b).P (F.lvl b).ψ t x) (rowForm A (F.lvl b).P (F.lvl b).ψ t y))).trans ?_
  rw [hr, hr, GlobalTheory.Mem.LiftForms.csum_lvlForm]
  have hc : (Nat.card ↥(A.fam.lvl (F.lvl b).P (F.lvl b).ψ).P : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos).ne'
  have hn : (((RealDat.nP F b)⁻¹ : ℝ) : ℂ) = ((Nat.card ↥(A.fam.lvl (F.lvl b).P (F.lvl b).ψ).P : ℂ))⁻¹ := by
    rw [Complex.ofReal_inv]
    rfl
  rw [map_mul, map_natCast, hn, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  rfl

end GlobalTheory.Mem.TopGram
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3.DTheta

theorem stepLev_change : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Pins R F cG → Holds R F → ∀ (b : Bool) (t : T) (k : ℕ), k + 1 < D.R.m → ∀ (κ : GA D (Yc D k)), ∀ κ' ∈ levS (Yc D (k + 1)) (R.βY (k + 1)) (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)), ∀ c : ℂ, (∀ φ, R.ωY t k (κ, κ') (R.toRealDat.ptY t k φ) = c • R.toRealDat.ptY t k φ) → ∀ y : R.CC t (k + 1), y.1 ∈ MultT R.θ (R.MY (k + 1)) (levS (Yc D (k + 1)) (R.βY (k + 1)) (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b))) (levChi (Yc D (k + 1)) (R.βY (k + 1)) (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b))) → ∀ φ w g, (R.ioY t k y).1 (R.ItY k φ w) (g * κ) = c * levChi (Yc D (k + 1)) (R.βY (k + 1)) (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)) κ' * (R.ioY t k y).1 (R.ItY k φ w) g := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hP hH b t k hk κ κ' hκ' c hc y hy φ w g
  have hch : R.toRealDat.IsChain := RealDat.chain_of_weak hP.char.base.chain hH.aux.ex
  have hio := hch.ioY t k (by omega)
  have e1 := hio.eq y φ w (g * κ)
  have e2 := hio.eq y φ w g
  rw [← e1, ← e2]
  unfold Lift.liftInt

  have hm := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 ((mem_multT _ _ _ _ _).1 hy)
  set χ1 := levChi (Yc D (k + 1)) (R.βY (k + 1)) (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)) with hχ1
  have hlev : ∀ (u : SmT (R.MY (k + 1))) h, y.1 u (h * κ') = χ1 κ' * y.1 u h := by
    intro u h
    induction u using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      have := hm.lev v κ' hκ' h
      simp only [PiTensorProduct.lift_symm, LinearMap.compMultilinearMap_apply] at this
      simp only [map_smul, Pi.smul_apply, smul_eq_mul, this]
      ring
    | add a a' ha ha' =>
      simp only [map_add (f := _), Pi.add_apply, ha, ha']
      ring
  have hleft : ∀ (u : SmT (R.MY (k + 1))), ∀ γ ∈ GQ (Yc D (k + 1)), ∀ h, y.1 u (γ * h) = y.1 u h := by
    intro u γ hγ h
    induction u using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      have := (hm.aut v).left γ hγ h
      simp only [PiTensorProduct.lift_symm, LinearMap.compMultilinearMap_apply] at this
      simp only [map_smul, Pi.smul_apply, smul_eq_mul, this]
    | add a a' ha ha' =>
      simp only [map_add (f := _), Pi.add_apply, ha, ha']
  have hω := hch.ωY t k hk
  have hpt := hch.ptY t k hk φ
  have hθ1 : ∀ h, thetaKO (R.ωY t k) (g * κ) h (R.toRealDat.ptY t k φ) =
      c * thetaKO (R.ωY t k) g (h * κ'⁻¹) (R.toRealDat.ptY t k φ) := by
    intro h
    unfold thetaKO
    have e : ((g * κ, h) : GA D (Yc D k) × GA D (Yc D (k + 1))) = (g, h * κ'⁻¹) * (κ, κ') := by
      ext <;> simp [mul_assoc]
    rw [e, map_mul, Module.End.mul_apply, hc φ, map_smul, Pi.smul_apply, smul_eq_mul]
  have hθ2 : ∀ γ ∈ GQ (Yc D (k + 1)), ∀ h, thetaKO (R.ωY t k) g (γ * h) (R.toRealDat.ptY t k φ) =
      thetaKO (R.ωY t k) g h (R.toRealDat.ptY t k φ) := by
    intro γ hγ h
    unfold thetaKO
    have e : ((g, γ * h) : GA D (Yc D k) × GA D (Yc D (k + 1))) = (1, γ) * (g, h) := by
      ext <;> simp
    rw [e, map_mul, Module.End.mul_apply]
    exact hω.om_aut 1 (one_mem _) γ hγ _ (hω.om_pres _ _ hpt)
  have hmod := hP.char.base.models
  have hHF : (R.νY t (k + 1)).IsHaarMeasure ∧
      IsFundamentalDomain (GQ (Yc D (k + 1))) (R.fdY t (k + 1)) (R.νY t (k + 1)) := by
    by_cases h2 : k + 1 + 1 < D.R.m
    · have h3 := hmod.νY t (k + 1) h2
      exact ⟨h3.1.1, h3.2⟩
    · have h3 := hmod.νY' t
      have e : D.R.m - 1 = k + 1 := by omega
      rw [e] at h3
      exact ⟨h3.1.1, h3.2⟩
  haveI := Formalism.IndefR.Eqv.measurableMul_GA D (Yc D (k + 1))
  haveI := Formalism.IndefR.Eqv.gQ_countable D (Yc D (k + 1))
  haveI := hHF.1
  haveI : (R.νY t (k + 1)).IsMulRightInvariant := Formalism.IndefR.Eqv.unimodGA_holds _ _ hHF.1
  set Ψ : GA D (Yc D (k + 1)) → ℂ := fun h => thetaKO (R.ωY t k) g h (R.toRealDat.ptY t k φ) * y.1 w h with hΨ
  have hRI := Formalism.IndefR.Eqv.rightInv_holds (GA D (Yc D (k + 1))) (GQ (Yc D (k + 1))) (R.νY t (k + 1))
    (R.fdY t (k + 1)) hHF.2 Ψ (fun γ hγ h => by simp only [hΨ, hθ2 γ hγ h, hleft w γ hγ h]) κ'⁻¹
  calc ∫ h in R.fdY t (k + 1), thetaKO (R.ωY t k) (g * κ) h (R.toRealDat.ptY t k φ) * y.1 w h ∂(R.νY t (k + 1))
      = ∫ h in R.fdY t (k + 1), c * χ1 κ' * Ψ (h * κ'⁻¹) ∂(R.νY t (k + 1)) := by
        congr 1
        funext h
        have e := hlev w (h * κ'⁻¹)
        rw [inv_mul_cancel_right] at e
        simp only [hΨ, hθ1 h, e]
        ring
    _ = c * χ1 κ' * ∫ h in R.fdY t (k + 1), Ψ h ∂(R.νY t (k + 1)) := by
        rw [integral_const_mul, hRI.2]

end GlobalTheory.Mem.R3.DTheta
end
