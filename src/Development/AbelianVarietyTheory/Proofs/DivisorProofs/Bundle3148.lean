module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle643
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1698
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2137
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1836
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle672
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2259
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle716
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3089
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle644
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2320
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivLift
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3116
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleGeneratorExtendingDensePart
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle137
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3088
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle231
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle022
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3090
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.Unif

theorem eta_points {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {g : ℕ} {y : Sp ℂ ⟶ S}
    {e : (Fin g → ℂ) → (Over.mk y ⟶ G)} {Λ' : Type} [AddCommGroup Λ'] {lv : Λ' → (𝟙_ (Over S) ⟶ G)} {N : ℕ}
    (hN : 0 < N) (hadd : ∀ z w, e (z + w) = e z * e w) (hsurj : Function.Surjective e)
    (hlv : ∀ x y, lv (x + y) = lv x * lv y) (hker : ∀ x, lv (N • x) = 1) (a : Λ') :
    ∃ z, e z = 1 ∧ toUnit _ ≫ lv a = e ((N : ℂ)⁻¹ • z) := by
  obtain ⟨w, hw⟩ := hsurj (toUnit _ ≫ lv a)
  have hepow : ∀ n : ℕ, e (n • w) = e w ^ n := by
    intro n
    induction n with
    | zero =>
      have h0 := hadd 0 0
      rw [add_zero] at h0
      simpa using (mul_eq_left.mp h0.symm)
    | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]
  have hlvpow : ∀ n : ℕ, lv (n • a) = lv a ^ n := by
    intro n
    induction n with
    | zero =>
      have h0 := hlv 0 0
      rw [add_zero] at h0
      simpa using (mul_eq_left.mp h0.symm)
    | succ n ih => rw [succ_nsmul, hlv, ih, pow_succ]
  refine ⟨N • w, ?_, ?_⟩
  · rw [hepow, hw, ← comp_pow, ← hlvpow, hker, comp_one]
  · have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    rw [← hw, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hN', one_smul]

end GlobalTheory.UPel.HT.Unif

namespace GlobalTheory.UPel.HT.Unif

theorem unifAt_change {O : Type} [Ring O] {bar : O → O} {g : ℕ} {ρ ρ₂ : O →+* Matrix (Fin g) (Fin g) ℂ} {R : Type}
    [CommRing R] {σ : R →+* ℂ} {Λ : Type} {F : Fam R O Λ g} {N : ℕ} {D' : PLat O bar} {t : Λ → D'.La}
    {P : D'.La →+ (Fin g → ℂ)} {y : Sp ℂ ⟶ F.X} {e : (Fin g → ℂ) → (Over.mk y ⟶ F.A)}
    (hU : UnifAt F σ ρ N D' t P y e) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ))
    (hc : ∀ a z, h (ρ a *ᵥ z) = ρ₂ a *ᵥ h z) :
    UnifAt F σ ρ₂ N D' t (h.toLinearMap.toAddMonoidHom.comp P) y (fun z => e (h.symm z)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hU
  have hc' : ∀ a z, h.symm (ρ₂ a *ᵥ z) = ρ a *ᵥ h.symm z := fun a z => by
    rw [LinearEquiv.symm_apply_eq, hc, LinearEquiv.apply_symm_apply]
  have hs : ∀ (k : ℂ) x, h.symm (k • h (P x)) = k • P x := fun k x => by simp
  refine ⟨h1, GlobalTheory.T.comp_linearEquiv_intertwining O bar D' g ρ ρ₂ P h h2 hc, ?_, ?_, ?_, ?_, ?_⟩
  · exact GlobalTheory.LocLift.IsExp.comp h3 (LinearEquiv.toContinuousLinearEquiv h.symm)
  · intro z
    rw [h4]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, by simp [hx]⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, by simp⟩
  · intro a z
    simp only [hc']
    exact h5 a _
  · intro k a b c hk hcc
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe, hs]
    exact h6 k a b c hk hcc
  · intro a
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe, hs]
    exact h7 a

end GlobalTheory.UPel.HT.Unif

namespace GlobalTheory.UPel.HT.Unif

variable {p : ℕ} [Fact p.Prime]

theorem exists_unifAt_of_exp (D : Datum p) {R : Type} [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ)
    (o : Obj b N (spMap σ)) (h : SmoothOfRelativeDimension D.g o.A.hom)
    (hL : (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).IsLB) (hN : 0 < N)
    (ρ' : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (e : (Fin D.g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ o.A))
    (Λ : Submodule ℤ (Fin D.g → ℂ)) (he : IsExp (𝟙 _) e) (hd : DiscreteTopology Λ)
    (hs : Submodule.span ℝ (Λ : Set (Fin D.g → ℂ)) = ⊤) (hk : ∀ z, e z = 1 ↔ z ∈ Λ)
    (hρ : ∀ a z, e (ρ' a *ᵥ z) = e z ≫ o.act.act a) :
    ∃ (D' : PLat D.O D.inv) (t : D.La → D'.La) (Q : D'.La →+ (Fin D.g → ℂ)), UnifAt (o.fam h hL) σ ρ' N D' t Q (𝟙 _) e := by
  have hst : ∀ a z, z ∈ Λ → ρ' a *ᵥ z ∈ Λ := fun a z hz => by
    haveI := o.act.hom a
    rw [← hk, hρ, (hk z).2 hz]
    exact one_comp _
  let φ : D.O →+* Module.End ℤ Λ :=
    { toFun := fun a =>
        { toFun := fun x => ⟨ρ' a *ᵥ (x : Fin D.g → ℂ), hst a x x.2⟩
          map_add' := fun x y => Subtype.ext (by simp [Matrix.mulVec_add])
          map_smul' := fun n x => Subtype.ext (by
            show ρ' a *ᵥ (n • (x : Fin D.g → ℂ)) = n • (ρ' a *ᵥ (x : Fin D.g → ℂ))
            exact map_zsmul (Matrix.mulVecLin (ρ' a)) n (x : Fin D.g → ℂ)) }
      map_one' := by ext x i; simp
      map_mul' := fun a b => by ext x i; simp [Matrix.mulVec_mulVec]
      map_zero' := by ext x i; simp
      map_add' := fun a b => by ext x i; simp [Matrix.add_mulVec] }
  letI : Module D.O Λ := Module.compHom Λ φ
  haveI : IsZLattice ℝ Λ := ⟨hs⟩
  let Q : Λ →+ (Fin D.g → ℂ) := Λ.subtype.toAddMonoidHom
  have hQi : Function.Injective Q := Subtype.val_injective
  have hQk : ∀ z, e z = 1 ↔ z ∈ Q.range := fun z => by
    rw [hk]; simp [Q]
  have hQs : Submodule.span ℝ (Set.range Q) = ⊤ := by
    simpa [Q] using hs
  obtain ⟨Hm, EF, hH, hpos, him, hweil⟩ := GlobalTheory.T.exists_positiveRiemannForm_of_relAmple_exponential (Sp ℂ) o.A D.g o.ab h
    (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) hL o.ample (𝟙 _) e Λ Q he hQi hQk
  obtain ⟨halt, hnd⟩ := GlobalTheory.T.im_hermForm_alternating_nondegenerate_on_lattice Λ D.g Q Hm EF hQi hQs hH hpos him
  have hmv : ∀ (a : D.O) (k : ℂ) (z : Fin D.g → ℂ), k • (ρ' a *ᵥ z) = ρ' a *ᵥ (k • z) := fun a k z => by
    rw [Matrix.mulVec_smul]
  have hadj : ∀ (a : D.O) x y, EF (φ a x) y = EF x (φ (D.inv a) y) := by
    intro a
    have hu : ∀ (c : D.O) (k : ℕ) (x : Λ), 0 < k →
        e ((k : ℂ)⁻¹ • Q ((φ c).toAddMonoidHom x)) = e ((k : ℂ)⁻¹ • Q x) ≫ o.act.act c := fun c k x _ => by
      show e ((k : ℂ)⁻¹ • (ρ' c *ᵥ (x : Fin D.g → ℂ))) = _
      rw [hmv, hρ]
      rfl
    have key := GlobalTheory.T.rosati_adjoint_iff_biextension_pullbacks_isomorphic o.A D.g o.ab h o.P o.isLB o.rig₁ o.rig₂ o.symm o.ample e Λ Q EF he hQi hQk hweil
      (o.act.act a) (o.act.act (D.star a).unop) (φ a).toAddMonoidHom (φ (D.inv a)).toAddMonoidHom (o.act.hom a)
      (o.act.hom _) (hu a) (hu (D.inv a))
    exact key.1 (o.rosati a)
  have het : ∀ a : D.La, ∃ z, e z = 1 ∧ toUnit _ ≫ o.eta a = e ((N : ℂ)⁻¹ • z) :=
    eta_points hN he.1 he.2.1 o.eta_add o.eta_ker
  choose tz htz using het
  let D' : PLat D.O D.inv :=
    { La := Λ
      fin := ZLattice.module_finite ℝ Λ
      free := ZLattice.module_free ℝ Λ
      EF := EF
      alt := halt
      nondeg := hnd
      adj := fun a x y => hadj a x y }
  refine ⟨D', fun a => (⟨tz a, (hk _).1 (htz a).1⟩ : Λ), Q, Category.id_comp _,
    ⟨fun a x => rfl, hQi, ?_, hQs, Hm, hH, hpos, him⟩, he, hQk, hρ, hweil, fun a => (htz a).2⟩
  have : Q.range = Λ.toAddSubgroup := by ext; simp [Q]
  rw [this]
  exact hd

end GlobalTheory.UPel.HT.Unif

namespace GlobalTheory.UPel.HT.Unif

theorem exists_unifAt : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (o : Obj b N (spMap σ)) h hL, 0 < N → N.Coprime p → b.IsType σ ρ → ∃ D' t Q e, D.Cls N D' t ∧ UnifAt (o.fam h hL) σ ρ N D' t Q (𝟙 _) e := by
  intro p _ D R _ b N σ ρ o h hL hN hNp hty
  obtain ⟨e₀, Λ, hexp, hdisc, hspan, hker⟩ := GlobalTheory.T.exists_complexFibreExponential_full_lattice (Sp ℂ) o.A D.g o.ab h (𝟙 _)
  obtain ⟨ρ', hρ'⟩ := GlobalTheory.T.exists_ringHom_matrix_lift_of_orderAction_exponential (Sp ℂ) o.A D.g D.O o.act.act o.ab h o.act.hom o.act.one o.act.mul o.act.add (𝟙 _) e₀ hexp
  obtain ⟨D', t, Q, hU⟩ := exists_unifAt_of_exp D b N σ o h hL hN ρ' e₀ Λ hexp hdisc hspan hker hρ'
  have hty' := GlobalTheory.T.lieCondition_uniformisingSpace_isType p D R b N σ ρ' o h hL D' t Q e₀ hU
  obtain ⟨M, hMu, hM⟩ := GlobalTheory.T.ringHom_conj_of_trace_eq_harrisTaylorOrder p D D.g ρ ρ' (fun c => by rw [hty c, hty' c])
  set u := hMu.unit with hu
  have hM' : ∀ a, ρ' a * (u : Matrix (Fin D.g) (Fin D.g) ℂ) = u * ρ a := fun a => by
    rw [hu, IsUnit.unit_spec]; exact hM a
  let Mi : Matrix (Fin D.g) (Fin D.g) ℂ := ((u⁻¹ : (Matrix (Fin D.g) (Fin D.g) ℂ)ˣ) : Matrix (Fin D.g) (Fin D.g) ℂ)
  have hinv : ∀ a, Mi * ρ' a = ρ a * Mi := fun a => by
    calc Mi * ρ' a = Mi * ρ' a * ((u : Matrix (Fin D.g) (Fin D.g) ℂ) * Mi) := by
          rw [Units.mul_inv, _root_.mul_one]
      _ = Mi * (ρ' a * u) * Mi := by simp only [_root_.mul_assoc]
      _ = Mi * (u * ρ a) * Mi := by rw [hM']
      _ = ρ a * Mi := by rw [← _root_.mul_assoc Mi, Units.inv_mul, _root_.one_mul]
  let hl : (Fin D.g → ℂ) ≃ₗ[ℂ] (Fin D.g → ℂ) := Matrix.toLinearEquiv' Mi (Units.invertible u⁻¹)
  have hc : ∀ a z, hl (ρ' a *ᵥ z) = ρ a *ᵥ hl z := fun a z => by
    show Mi *ᵥ (ρ' a *ᵥ z) = ρ a *ᵥ (Mi *ᵥ z)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hinv]
  have hU2 := unifAt_change hU hl hc
  obtain ⟨t', hcls, ht'⟩ := GlobalTheory.T.uniformised_complex_fibre_marked_lattice_class p D R b N σ ρ o h hL D' t _ _ hN hNp hU2
  have hmk : IsMarkedIsom N D' D' t t' (LinearEquiv.refl D.O D'.La) := by
    refine ⟨fun x y => rfl, fun a => ?_⟩
    obtain ⟨x, hx⟩ := ht' a
    exact ⟨-x, by rw [hx]; simp⟩
  exact ⟨D', t', _, _, hcls, GlobalTheory.T.uniformisationAt_transport_isometry D.O D.inv D.g ρ R σ D.La (o.fam h hL) N D' D' t t' _ _ (𝟙 _) _
    (LinearEquiv.refl D.O D'.La) (LinearEquiv.refl ℂ (Fin D.g → ℂ)) hN hU2 hmk (fun x => rfl) hU2.2.1⟩

end GlobalTheory.UPel.HT.Unif
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.UPel.HT.ES.PIsogExt

theorem comp_pow_pt {S : Scheme.{0}} {T T' A : Over S} [GrpObj A] (f : T' ⟶ T) (g : T ⟶ A) (n : ℕ) :
    f ≫ g ^ n = (f ≫ g) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (f ≫ toUnit T) (toUnit T')]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

theorem pow_comp_of_isGrpPullback {Y₀ Y : Scheme.{0}} {i : Y₀ ⟶ Y} {A₀ : Over Y₀} {A : Over Y}
    [GrpObj A₀] [GrpObj A] {φ : A₀.left ⟶ A.left} (h : IsGrpPullback A₀ A i φ) (k : ℕ) (hk : 0 < k) :
    (𝟙 A₀ ^ k).left ≫ φ = φ ≫ (𝟙 A ^ k).left := by
  let φ₀ : Over.mk (A₀.hom ≫ i) ⟶ A := Over.homMk φ h.1.w
  have key : ∀ n : ℕ, (φ₀ ^ (n + 1)).left = (𝟙 A₀ ^ (n + 1)).left ≫ φ := by
    intro n
    induction n with
    | zero => rw [zero_add, pow_one, pow_one]; rfl
    | succ n ih =>
      rw [pow_succ φ₀, pow_succ (𝟙 A₀)]
      exact h.2 A₀ _ _ _ _ ih rfl
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hk
  rw [zero_add, ← key n]
  have : φ₀ ^ (n + 1) = φ₀ ≫ 𝟙 A ^ (n + 1) := by rw [comp_pow_pt, Category.comp_id]
  rw [this]; rfl

theorem isSquare_square_compatible_homs {Y₀ Y : Scheme.{0}} {A₀ A₀' : Over Y₀} {A A' : Over Y}
    [GrpObj A₀] [IsCommMonObj A₀] [GrpObj A₀'] [IsCommMonObj A₀'] [GrpObj A] [IsCommMonObj A]
    [GrpObj A'] [IsCommMonObj A'] {φ : A₀.left ⟶ A.left} {φ' : A₀'.left ⟶ A'.left}
    {φ₂ : (G2 A₀).left ⟶ (G2 A).left} {φ₂' : (G2 A₀').left ⟶ (G2 A').left}
    (h : IsSquare φ φ₂) (h' : IsSquare φ' φ₂') {ψ₀ : A₀ ⟶ A₀'} {ψ : A ⟶ A'}
    (e : φ ≫ ψ.left = ψ₀.left ≫ φ') : φ₂ ≫ sq2 ψ = sq2 ψ₀ ≫ φ₂' := by
  have f1 : ∀ {B B' : Over Y} [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B'] (χ : B ⟶ B'),
      sq2 χ ≫ (fst B' B').left = (fst B B).left ≫ χ.left := fun χ => by
    rw [sq2, ← Over.comp_left, lift_fst, Over.comp_left]
  have f2 : ∀ {B B' : Over Y} [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B'] (χ : B ⟶ B'),
      sq2 χ ≫ (snd B' B').left = (snd B B).left ≫ χ.left := fun χ => by
    rw [sq2, ← Over.comp_left, lift_snd, Over.comp_left]
  have g1 : sq2 ψ₀ ≫ (fst A₀' A₀').left = (fst A₀ A₀).left ≫ ψ₀.left := by
    rw [sq2, ← Over.comp_left, lift_fst, Over.comp_left]
  have g2 : sq2 ψ₀ ≫ (snd A₀' A₀').left = (snd A₀ A₀).left ≫ ψ₀.left := by
    rw [sq2, ← Over.comp_left, lift_snd, Over.comp_left]
  apply pullback.hom_ext
  · change _ ≫ (fst A' A').left = _ ≫ (fst A' A').left
    rw [Category.assoc, Category.assoc, f1, h'.1, ← Category.assoc, h.1, Category.assoc, e, reassoc_of% g1]
  · change _ ≫ (snd A' A').left = _ ≫ (snd A' A').left
    rw [Category.assoc, Category.assoc, f2, h'.2, ← Category.assoc, h.2, Category.assoc, e, reassoc_of% g2]


open GlobalTheory.CechPic in
theorem lbIso_extend {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {Y₀ Y : Scheme.{0}} [IsLocallyNoetherian Y] (hY : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y) (i : Y₀ ⟶ Y) [IsOpenImmersion i]
    [IsDominant i] {σ₀ : Y₀ ⟶ Sp R} {σ : Y ⟶ Sp R} (o o' : Obj b N σ) (o₀ o₀' : Obj b N σ₀)
    (m : ObjMap o₀ o i) (m' : ObjMap o₀' o' i) (ψ₀ : o₀.A ⟶ o₀'.A) (ψ : o.A ⟶ o'.A) [IsMonHom ψ]
    (e : m.φ ≫ ψ.left = ψ₀.left ≫ m'.φ) (c : ℕ) (h₀ : LBIso (Hecke.lbPow o₀.P c) (o₀'.P.pull (sq2 ψ₀))) :
    LBIso (Hecke.lbPow o.P c) (o'.P.pull (sq2 ψ)) := by
  haveI := GlobalTheory.IsNormalScheme.of_pred hY
  haveI := o.ab.smooth
  haveI := o.ab.geomConnected
  haveI := GlobalTheory.smooth_tensorObj_hom o.A o.A
  haveI := GlobalTheory.geometricallyConnected_tensorObj_hom o.A o.A
  have hpb : IsPullback m.φ₂ (G2 o₀.A).hom (G2 o.A).hom i := GlobalTheory.SiegDesc.isPullback_of_isSquare m.cart.1 m.sq
  have hL : (Hecke.lbPow o.P c).IsLB := LB.isLB_linComb o.isLB _ _
  have hM : (o'.P.pull (sq2 ψ)).IsLB := pull_isLB o'.isLB _
  have hcL : ∀ {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) (h : (Hecke.lbPow L c).IsLB), cls _ h = c • cls L hL :=
    fun {X} L hL h => (cls_linComb (L := L) hL (fun _ => 𝟙 X) (fun _ => 1) h).trans (by simp [pull_id])
  let s : Y ⟶ (G2 o.A).left := (η[o.A] ≫ lift (1 : o.A ⟶ o.A) (𝟙 o.A)).left
  have hs : s ≫ (G2 o.A).hom = 𝟙 Y := Over.w _
  have hss : s ≫ sq2 ψ = (η[o'.A] ≫ lift (1 : o'.A ⟶ o'.A) (𝟙 o'.A)).left := by
    rw [sq2, ← Over.comp_left]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp [Hom.one_def, IsMonHom.one_hom]
  have r0 : ∀ (A : Over Y) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left) (hP : P.IsLB),
      (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) →
      pull (η[A] ≫ lift (1 : A ⟶ A) (𝟙 A)).left (cls P hP) = 0 := by
    intro A _ _ P hP ht
    rw [Over.comp_left, pull_comp, ← cls_pull hP _ (pull_isLB hP _), (cls_eq_zero_iff _).2 ht, map_zero]
  have eq_zero_of_pull_densePart_of_pull_section : ∀ {S Y U YU : Scheme.{0}} [IsLocallyNoetherian S]
      [GlobalTheory.IsNormalScheme S] (f : Y ⟶ S) [Smooth f] [GeometricallyConnected f] (j : U ⟶ S)
      [IsOpenImmersion j] (ρ : YU ⟶ Y) (fU : YU ⟶ U), Dense (Set.range j) → IsPullback ρ fU f j →
      ∀ σ : S ⟶ Y, σ ≫ f = 𝟙 S → ∀ δ : GlobalTheory.CechPic.Pic Y, pull ρ δ = 0 →
        pull σ δ = 0 → δ = 0 := by
    intro S Y U YU _ _ f _ _ j _ ρ fU hd hpb σ hσ δ hρ hσδ
    obtain ⟨N, hN, rfl⟩ := cls_surj δ
    have hdom : IsDominant j := ⟨hd⟩
    have hgi : GeometricallyIntegral f :=
      GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected Y S f inferInstance inferInstance
    have hfst : pullback.fst f j = hpb.isoPullback.inv ≫ ρ := (IsPullback.isoPullback_inv_fst hpb).symm
    have h1 : cls (N.pull σ) (pull_isLB hN σ) = 0 := by rw [cls_pull hN]; exact hσδ
    have h2 : cls (N.pull (pullback.fst f j)) (pull_isLB hN _) = 0 := by
      rw [cls_pull hN, hfst, pull_comp, hρ, map_zero]
    obtain ⟨t, ht⟩ := GlobalTheory.GenericExtend.exists_isGen_of_densePart S U j (GlobalTheory.IsNormalScheme.pred S)
      inferInstance inferInstance hdom inferInstance (Over.mk f) σ N hσ (show Smooth f from inferInstance) hgi hN
      ((cls_eq_zero_iff _).1 h1) ((cls_eq_zero_iff _).1 h2)
    exact (cls_eq_zero_iff hN).2 ⟨t, ht⟩
  have key := eq_zero_of_pull_densePart_of_pull_section (G2 o.A).hom i m.φ₂ (G2 o₀.A).hom i.denseRange hpb s hs
    (cls _ hM - cls _ hL) ?_ ?_
  · exact (cls_eq_iff hL hM).1 (sub_eq_zero.1 key).symm
  · have hsq := PIsogExt.isSquare_square_compatible_homs m.sq m'.sq e
    have e1 := (cls_eq_iff o₀'.isLB (pull_isLB o'.isLB _)).2 m'.pol
    have e2 := (cls_eq_iff o₀.isLB (pull_isLB o.isLB _)).2 m.pol
    have e3 : cls (Hecke.lbPow o₀.P c) (LB.isLB_linComb o₀.isLB _ _) = cls _ (pull_isLB o₀'.isLB (sq2 ψ₀)) :=
      (cls_eq_iff _ _).2 h₀
    rw [map_sub, sub_eq_zero, hcL (X := (G2 o.A).left) o.P o.isLB, map_nsmul, cls_pull o'.isLB, ← pull_comp, hsq, pull_comp,
      ← cls_pull o'.isLB _ (pull_isLB o'.isLB _), ← e1, ← cls_pull o₀'.isLB _ (pull_isLB o₀'.isLB _), ← e3]
    refine (hcL (X := (G2 o₀.A).left) o₀.P o₀.isLB _).trans ?_
    rw [e2, cls_pull o.isLB]
  · rw [map_sub, hcL (X := (G2 o.A).left) o.P o.isLB, map_nsmul, cls_pull o'.isLB, ← pull_comp, hss, r0 _ _ _ o'.rig₁, r0 _ _ _ o.rig₁,
      smul_zero, sub_zero]

theorem exists_isPIsog_extend : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ),
    3 ≤ N → N.Coprime p → ∀ (j c : ℕ), (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) →
    ∀ (Y₀ Y : Scheme.{0}) (i : Y₀ ⟶ Y) (σ₀ : Y₀ ⟶ Sp R) (σ : Y ⟶ Sp R), IsOpenImmersion i → IsDominant i →
    IsLocallyNoetherian Y → (∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) →
    (∀ y : Y, IsDomain (Y.presheaf.stalk y)) →
    ∀ (o o' : Obj b N σ) (o₀ o₀' : Obj b N σ₀) (m : ObjMap o₀ o i) (m' : ObjMap o₀' o' i) (ψ₀ : o₀.A ⟶ o₀'.A),
    IsPIsog c o₀ o₀' ψ₀ → ∃ ψ : o.A ⟶ o'.A, IsPIsog c o o' ψ ∧ m.φ ≫ ψ.left = ψ₀.left ≫ m'.φ := by
  intro p _ D R _ b N _ _ j c _ Y₀ Y i σ₀ σ _ _ _ hic hdom o o' o₀ o₀' m m' ψ₀ hψ₀
  have hY : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y := fun y => ⟨hdom y, hic y⟩
  haveI := GlobalTheory.IsNormalScheme.of_pred hY
  haveI : IsReduced Y := by
    haveI := hdom
    exact isReduced_of_isReduced_stalk Y
  have hcpos : 0 < c := hψ₀.pos
  obtain ⟨hk, hmon₀, hlin₀, heta₀, ⟨hP₀⟩, ψ₀', hmon₀', h₁, h₂⟩ := hψ₀
  haveI := hmon₀
  haveI := hmon₀'
  have hA := GlobalTheory.isSemiAbelian_of_isAbelianScheme o.A o.ab
  have hA' := GlobalTheory.isSemiAbelian_of_isAbelianScheme o'.A o'.ab
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.dense_openImmersion i
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian o.A hA
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian o'.A hA'
  obtain ⟨ψ, hψ⟩ := GlobalTheory.SemiAbDenseExt.exists_extension i i.denseRange o.A o'.A hA hA' o₀.A o₀'.A m.φ m'.φ
    m.cart m'.cart ψ₀ hmon₀
  obtain ⟨ψ', hψ'⟩ := GlobalTheory.SemiAbDenseExt.exists_extension i i.denseRange o'.A o.A hA' hA o₀'.A o₀.A m'.φ m.φ
    m'.cart m.cart ψ₀' hmon₀'
  haveI hψm : IsMonHom ψ := GlobalTheory.ExtUnique.isMonHom_of_isGrpPullback m.cart m'.cart ψ₀ ψ hψ
  haveI hψm' : IsMonHom ψ' := GlobalTheory.ExtUnique.isMonHom_of_isGrpPullback m'.cart m.cart ψ₀' ψ' hψ'
  have e : m.φ ≫ ψ.left = ψ₀.left ≫ m'.φ := hψ.symm
  have e' : m'.φ ≫ ψ'.left = ψ₀'.left ≫ m.φ := hψ'.symm
  refine ⟨ψ, ⟨hk, hψm, fun c' => ?_, fun x => ?_, ⟨lbIso_extend hY i o o' o₀ o₀' m m' ψ₀ ψ e c hP₀⟩, ψ', hψm', ?_, ?_⟩, e⟩
  · refine GlobalTheory.ExtUnique.over_hom_ext_of_isPullback m.cart.1 ?_
    rw [Over.comp_left, Over.comp_left, ← Category.assoc, ← m.act c', Category.assoc, e, ← Category.assoc,
      ← Over.comp_left, hlin₀ c', Over.comp_left, Category.assoc, m'.act c', ← Category.assoc, ← e, Category.assoc]
  · refine Over.OverMorphism.ext (GlobalTheory.ExtUnique.hom_ext_of_dominant o'.A.hom (by rw [Over.w, Over.w]) i ?_)
    have h1 := m'.eta x
    have h2 := m.eta x
    rw [heta₀ x, Over.comp_left, Category.assoc] at h1
    rw [← h1, ← e, Over.comp_left, ← Category.assoc, h2, Category.assoc]
  · refine GlobalTheory.ExtUnique.over_hom_ext_of_isPullback m.cart.1 ?_
    rw [Over.comp_left, ← Category.assoc, e, Category.assoc, e', ← Category.assoc, ← Over.comp_left, h₁,
      PIsogExt.pow_comp_of_isGrpPullback m.cart c hcpos]
  · refine GlobalTheory.ExtUnique.over_hom_ext_of_isPullback m'.cart.1 ?_
    rw [Over.comp_left, ← Category.assoc, e', Category.assoc, e, ← Category.assoc, ← Over.comp_left, h₂,
      PIsogExt.pow_comp_of_isGrpPullback m'.cart c hcpos]

end GlobalTheory.UPel.HT.ES.PIsogExt
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.InvAlg

theorem invariants_of_trivial_on_thickenings : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] [Module.Finite R R'], Function.Injective (algebraMap R R') → IsGal (algebraMap R R') → ∀ (C' : Type) [CommRing C'] [Algebra R C'] [Algebra R' C'] [IsScalarTower R R' C'] [Algebra.FiniteType R' C'] (act : Gal (algebraMap R R') →* (C' ≃ₐ[R] C')), (∀ σ r, act σ (algebraMap R' C' r) = algebraMap R' C' (σ.1 r)) → ∀ (O : Type) [CommRing O] [Algebra R O] [Module.Flat R O] [Algebra.FiniteType R O] (i : ∀ e : ℕ, O →ₐ[R] C' ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R C')), (∀ e x y, Ideal.Quotient.mk _ y = i (e + 1) x → Ideal.Quotient.mk _ y = i e x) → (∀ e σ x y, Ideal.Quotient.mk _ y = i e x → Ideal.Quotient.mk _ (act σ y) = i e x) → (∀ e, Function.Surjective (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) ∧ RingHom.ker (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) = (maximalIdeal R ^ (e + 1)).map (algebraMap R (TensorProduct R O R'))) → ∀ C : Subalgebra R C', (∀ x, x ∈ C ↔ ∀ σ, act σ x = x) → Algebra.FiniteType R C ∧ Module.Finite C C' ∧ ∃ f : C, f - 1 ∈ (maximalIdeal R).map (algebraMap R C) ∧ (∀ x : C', ∃ n : ℕ, (f : C') ^ n * x ∈ Set.range (Algebra.TensorProduct.lift C.val (IsScalarTower.toAlgHom R R' C') fun _ _ => Commute.all _ _)) ∧ (∀ t : TensorProduct R C R', Algebra.TensorProduct.lift C.val (IsScalarTower.toAlgHom R R' C') (fun _ _ => Commute.all _ _) t = 0 → ∃ n : ℕ, ((f ^ n) ⊗ₜ[R] (1 : R')) * t = 0) ∧ ∀ e, Nonempty ((O ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R O)) ≃ₐ[R] (C ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R C))) := by
  intro R _ _ _ hR R' _ _ _ _ hinj hGal C' _ _ _ _ _ act hact O _ _ _ _ i hi1 hi2 hi3 C hC
  haveI : IsNoetherianRing R := hR.1
  haveI : Finite (Gal (algebraMap R R')) := hGal.1
  haveI : Algebra.FiniteType R C' := Algebra.FiniteType.trans (S := R') inferInstance inferInstance
  obtain ⟨hft, hfin⟩ := GlobalTheory.T.finiteType_invariants_finite_group_and_finite R C' (Gal (algebraMap R R')) act C hC
  have hg := GlobalTheory.T.completion_galoisInvariants_agree_mod_maxIdeal_pow R hR R' hinj hGal C' act hact O i hi1 hi2 hi3 C hC hft hfin
  choose gm hgc using hg
  obtain ⟨hs, hinj'⟩ := GlobalTheory.T.tensor_quotient_onto_and_injective_mod_ideal_pow R (maximalIdeal R) R' C' O i hi3 C gm hgc
  haveI : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing R C
  obtain ⟨f, hf1, hf2, hf3⟩ := GlobalTheory.T.exists_unit_approximation_adic_completion C ((maximalIdeal R).map (algebraMap R C)) (TensorProduct R C R') C' _ hs hinj'
  have hL : ∀ t, Algebra.TensorProduct.lift (Algebra.ofId C C') (IsScalarTower.toAlgHom R R' C') (fun _ _ => Commute.all _ _) t = Algebra.TensorProduct.lift C.val (IsScalarTower.toAlgHom R R' C') (fun _ _ => Commute.all _ _) t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  refine ⟨hft, hfin, f, hf1, fun x => ⟨1, ?_⟩, fun t ht => ⟨1, ?_⟩, fun e => ⟨gm e⟩⟩
  · obtain ⟨t, ht⟩ := hf2 x
    exact ⟨t, by rw [← hL]; simpa using ht⟩
  · have := hf3 t (by rw [hL]; exact ht)
    rw [pow_one]
    rwa [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] at this

end GlobalTheory.InvAlg
end

section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

theorem _root_.GlobalTheory.T.izumi_bound_mod_principal_ideal : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (U : M.Z.Opens), (U : Set M.Z).Nonempty → ∀ (x : M.Z), IsClosed ({x} : Set M.Z) → ∀ f ∈ M.O x, f ≠ 0 → ∃ C : ℕ → ℕ, ∀ (e : ℕ) (F : M.O x), (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U x y → ‖M.val (gPt p ≫ y) F‖ ≤ ‖M.val (gPt p ≫ y) f‖ ∨ ∃ h, NonUnitAt M x h ∧ ‖M.val (gPt p ≫ y) F‖ ≤ ‖M.val (gPt p ≫ y) h‖ ^ C e) → ∃ a b : M.O x, (F : Ω) = a * f + b ∧ b ∈ Ideal.span {c : M.O x | ¬ IsUnit c} ^ e := by
  first | exact @GlobalTheory.Izumi.small_mod_principal | exact GlobalTheory.Izumi.small_mod_principal | (intros; apply GlobalTheory.Izumi.small_mod_principal <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

theorem _root_.GlobalTheory.T.exists_normalised_twistedGenerator_of_factor : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ N : ℕ, 1 ≤ N → ∀ (r : D.toPre.X → R) (g : ∀ y : D.toPre.X, LB.Gen (LB.LinComb D.toPre.P.L (K := PUnit) (fun _ => (D.toPre.c y).left) (fun _ => -1))), (∀ y, (g y).IsGen) → (∀ y (z : (TK R).left) (J), Good D.toPre.P.L z J → (val (D.toPre.psi y) (𝟙 _) z J ^ N * (val (D.toPre.psi (h y)) (𝟙 _) z J)⁻¹).val = gs (𝟙 _) z ⊤ (scal (jK R) (r y)) * (val (g y) (toUnit (TK R)).left z J ^ N * (val (g (h y)) (toUnit (TK R)).left z J)⁻¹).val) → ∀ ν : D.toPre.X, ∃ u₀ : LB.Gen (LB.LinComb D.toPre.P.L (Sum.elim (tφ D.toPre a (shift h h' N (-1) ν)) (fun k => (padd D.toPre.P.A (𝟙 _) (toUnit _ ≫ D.toPre.c ν)).left ≫ tφ D.toPre a 0 k)) (dε N (-1))), u₀.IsGen ∧ ∀ u, IsFac D.toPre a h N (-1) ν 0 (shift h h' N (-1) ν) u → ∀ (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF D.toPre (FractionRing R)).left) (z : Z) (J), Good D.toPre.P.L z J → (val u x z J).val = gs x z ⊤ (scal ((fst _ _ : DegPre.BF D.toPre (FractionRing R) ⟶ TF (R := R) (FractionRing R)).left : (DegPre.BF D.toPre (FractionRing R)).left ⟶ Sp (FractionRing R)) (algebraMap R (FractionRing R) (r ν))) * (val u₀ (x ≫ (DegPre.prB D.toPre (FractionRing R)).left) z J).val := by
  first | exact @GlobalTheory.TwNorm.exists_gen_fac | exact GlobalTheory.TwNorm.exists_gen_fac | (intros; apply GlobalTheory.TwNorm.exists_gen_fac <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

theorem _root_.GlobalTheory.T.twistedFunctionalEquation_of_adicSum_termwise : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (n j : ℤ) (Ix : Type) (w : Ix → D.toPre.X) (s : ∀ i, SecT D.toPre a n j (w i)) (F : ∀ β, SecT D.toPre a n j β) (σ : D.toPre.X → Ix ≃ Ix), Small (maximalIdeal R) s → IsSum (maximalIdeal R) s F → (∀ mu i, w (σ mu i) = w i + shift h h' n j mu) → (∀ mu i, TRel h mu (s i) (s (σ mu i))) → TFE h h' F := by
  first | exact @GlobalTheory.TwFam.SumFE.tfe_of_isSum | exact GlobalTheory.TwFam.SumFE.tfe_of_isSum | (intros; apply GlobalTheory.TwFam.SumFE.tfe_of_isSum <;> assumption)
end
