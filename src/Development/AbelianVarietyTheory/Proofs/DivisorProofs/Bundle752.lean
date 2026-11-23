module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle703
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle004
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory

set_option synthInstance.maxHeartbeats 200000 in
theorem exists_grpObj_isAbelianScheme_of_isPullback_spMap : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (R' : Type) [CommRing R'] (σ : R →+* R') (X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ A.left), IsPullback φ s' A.hom (spMap σ) → ∃ _ : GrpObj (Over.mk s'), IsAbelianScheme (Over.mk s') ∧ SmoothOfRelativeDimension g s' := by
  intro R _ A _ g hA hg R' _ σ X' s' φ h
  have hsm : SmoothOfRelativeDimension g s' := by
    have := smoothOfRelativeDimension_isStableUnderBaseChange (n := g)
    exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) h hg
  let F := Over.pullback (spMap σ)
  letI : F.Braided := Functor.Braided.ofChosenFiniteProducts F
  let B := F.obj A
  letI : GrpObj B := Functor.grpObjObj (F := F) (G := A)
  let e : B ≅ Over.mk s' := Over.isoMk h.isoPullback.symm (by simp [B, F])
  letI : GrpObj (Over.mk s') := GrpObj.ofIso e
  refine ⟨this, ?_, hsm⟩
  haveI : IsCommMonObj A := hA.comm
  have hcB : IsCommMonObj B := Functor.isCommMonObj_obj (F := F) (M := A)
  exact {
    comm := by
      constructor
      show (β_ _ _).hom ≫ ((e.inv ⊗ₘ e.inv) ≫ μ[B] ≫ e.hom) = (e.inv ⊗ₘ e.inv) ≫ μ[B] ≫ e.hom
      rw [← Category.assoc, ← BraidedCategory.braiding_naturality, Category.assoc,
        ← Category.assoc (β_ B B).hom, IsCommMonObj.mul_comm]
    smooth := MorphismProperty.of_isPullback (P := @Smooth) h hA.smooth
    proper := MorphismProperty.of_isPullback (P := @IsProper) h hA.proper
    geomConnected := MorphismProperty.of_isPullback (P := @GeometricallyConnected) h hA.geomConnected }

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES


theorem _root_.GlobalTheory.T.isClopen_torsion_kernel_locus : ∀ (Y : Scheme.{0}) (A : Over Y) [GrpObj A] [IsCommMonObj A] (n : ℕ) (J : Type) [Finite J] (B : J → Over Y) [∀ i, GrpObj (B i)] (f : ∀ i, A ⟶ B i) (B' : Over Y) [GrpObj B'] (f' : A ⟶ B'), IsAbelianScheme A → (∀ i, IsAbelianScheme (B i)) → IsAbelianScheme B' → (∀ i, IsMonHom (f i)) → IsMonHom f' → IsUnit (n : Γ(Y, ⊤)) → ∃ W : Set Y, IsOpen W ∧ IsClosed W ∧ (∀ (Tb : Scheme.{0}) (t : Tb ⟶ Y), Set.range t.base ⊆ W ↔ ∀ (T : Over Y) (σ : T.left ⟶ Tb), σ ≫ t = T.hom → ∀ a : T ⟶ A, a ^ n = 1 → (∀ i, a ≫ f i = 1) → a ≫ f' = 1) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Y), Set.range x.base ⊆ W ↔ ∀ a : Over.mk x ⟶ A, a ^ n = 1 → (∀ i, a ≫ f i = 1) → a ≫ f' = 1 := by
  first | (exact @GlobalTheory.LevCover.kerlocus_open_closed) | (exact GlobalTheory.LevCover.kerlocus_open_closed) | (intros; apply GlobalTheory.LevCover.kerlocus_open_closed  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.RigTriv

variable {T X : Scheme.{0}}

theorem exists_lift (W : X.Opens) {Z : Scheme.{0}} (f : Z ⟶ X) (h : ∀ z, f z ∈ W) :
    ∃ g : Z ⟶ W.toScheme, g ≫ W.ι = f :=
  ⟨IsOpenImmersion.lift W.ι f (by rintro _ ⟨z, rfl⟩; rw [Scheme.Opens.range_ι]; exact h z),
    IsOpenImmersion.lift_fac _ _ _⟩

theorem ι_mem (W : X.Opens) (x : W.toScheme) : W.ι x ∈ W := by
  have h : W.ι x ∈ Set.range W.ι := ⟨x, rfl⟩
  rw [W.range_ι] at h; exact h

theorem surj_restrict (A : Over T) [GrpObj A] (hA : IsAbelianScheme A) (U : T.Opens) :
    Function.Surjective (A.hom ∣_ U).appTop.hom := by
  have h1 : Function.Surjective (pullback.snd A.hom U.ι).appTop.hom :=
    (GlobalTheory.SemiRigid.globalFns _ _ (Out.TLinPf.isAb_pullback U.ι A hA)).2
  have e : A.hom ∣_ U = (pullbackRestrictIsoRestrict A.hom U).inv ≫ pullback.snd A.hom U.ι := rfl
  rw [e, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp]
  exact (ConcreteCategory.bijective_of_isIso
    ((pullbackRestrictIsoRestrict A.hom U).inv.app ⊤)).2.comp h1

theorem normalize (p : X ⟶ T) (e : T ⟶ X) {N : LB X} (hN : N.IsLB)
    (t : LB.Gen (N.pull e)) (ht : t.IsGen) (W : X.Opens) (hW : ∀ x ∈ W, e (p x) ∈ W)
    (s : LB.Gen (N.pull W.ι)) (hs : s.IsGen) :
    ∃ n : LB.Gen (LB.LinComb N (fun _ : PUnit => W.ι ≫ 𝟙 X) (fun _ => 1)), n.IsGen ∧
      ∀ (Z : Scheme.{0}) (m : Z ⟶ W.toScheme) (z : Z) (J), Good N z J →
        m ≫ W.ι ≫ p ≫ e = m ≫ W.ι → val n m z J = val t (m ≫ W.ι ≫ p) z J := by
  obtain ⟨q, hq⟩ := exists_lift W (W.ι ≫ p ≫ e) (fun z => by
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]; exact hW _ (ι_mem W z))
  let n₀ := LB.mulGen N _ _ _ _ (LB.mulGen N _ _ _ _ s (LB.invGen N _ _ (LB.pullGen N _ _ s q)))
    (LB.pullGen N (fun _ : PUnit => e) (fun _ => 1) t (W.ι ≫ p))
  have hn₀ : n₀.IsGen := DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ hs
    (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hs _))) (DVR.pullGen_isGen _ _ _ _ ht _)
  obtain ⟨n, hn, hv⟩ := exists_gen hN (φ' := fun _ : PUnit => W.ι ≫ 𝟙 X) (ε' := fun _ => 1)
    (fun U _ h => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, zpow_one,
        zpow_neg, hq, Category.assoc, Category.comp_id]
      exact _root_.inv_mul_cancel_right _ _) n₀ hn₀
  refine ⟨n, hn, fun Z m z J hJ hm => ?_⟩
  have hmq : m ≫ q = m := by
    rw [← cancel_mono W.ι, Category.assoc, hq, hm]
  rw [hv Z m z J hJ, val_mul hJ, val_mul hJ, val_inv, val_pull hJ, val_pull hJ, hmq, mul_inv_cancel, _root_.one_mul]

theorem exists_gen_of_local (p : X ⟶ T) (e : T ⟶ X) (he : e ≫ p = 𝟙 T)
    (hsurj : ∀ U : T.Opens, Function.Surjective (p ∣_ U).appTop.hom) {N : LB X} (hN : N.IsLB)
    (t : LB.Gen (N.pull e)) (ht : t.IsGen)
    (hloc : ∀ τ : T, ∃ V : T.Opens, τ ∈ V ∧ ∃ s : LB.Gen (N.pull (p ⁻¹ᵁ V).ι), s.IsGen) :
    ∃ s : LB.Gen N, s.IsGen := by
  choose V hV s hs using hloc
  have hep : ∀ x : T, p (e x) = x := fun x => by rw [← Scheme.Hom.comp_apply, he]; rfl
  have hW : ∀ τ, ∀ x ∈ p ⁻¹ᵁ V τ, e (p x) ∈ p ⁻¹ᵁ V τ := fun τ x hx => by
    show p (e (p x)) ∈ V τ
    rw [hep]; exact hx
  choose n hn hnv using fun τ => normalize p e hN t ht (p ⁻¹ᵁ V τ) (hW τ) (s τ) (hs τ)
  have agree : ∀ (τ τ' : T) (Z : Scheme.{0}) (r : Z ⟶ (p ⁻¹ᵁ V τ).toScheme)
      (r' : Z ⟶ (p ⁻¹ᵁ V τ').toScheme) (z : Z) (J), Good N z J →
      r ≫ (p ⁻¹ᵁ V τ).ι = r' ≫ (p ⁻¹ᵁ V τ').ι → val (n τ) r z J = val (n τ') r' z J := by
    intro τ τ' Z r r' z J hJ hrr
    set U := V τ ⊓ V τ' with hUdef
    have l₁ : p ⁻¹ᵁ U ≤ p ⁻¹ᵁ V τ := fun x hx => hx.1
    have l₂ : p ⁻¹ᵁ U ≤ p ⁻¹ᵁ V τ' := fun x hx => hx.2
    let i₁ := X.homOfLE l₁
    let i₂ := X.homOfLE l₂
    have hi₁ : i₁ ≫ (p ⁻¹ᵁ V τ).ι = (p ⁻¹ᵁ U).ι := X.homOfLE_ι _
    have hi₂ : i₂ ≫ (p ⁻¹ᵁ V τ').ι = (p ⁻¹ᵁ U).ι := X.homOfLE_ι _
    obtain ⟨e₂, he₂⟩ := exists_lift (p ⁻¹ᵁ U) (U.ι ≫ e) (fun y => by
      show p ((U.ι ≫ e) y) ∈ U
      rw [Scheme.Hom.comp_apply, hep]; exact ι_mem U y)
    have hs₂ : e₂ ≫ (p ∣_ U) = 𝟙 _ := by
      rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, he₂, Category.assoc, he,
        Category.comp_id, Category.id_comp]
    obtain ⟨ρ, hρ⟩ := exists_lift (p ⁻¹ᵁ U) (r ≫ (p ⁻¹ᵁ V τ).ι) (fun y => by
      refine ⟨ι_mem (p ⁻¹ᵁ V τ) (r y), ?_⟩
      have h := ι_mem (p ⁻¹ᵁ V τ') (r' y)
      rw [← Scheme.Hom.comp_apply, ← hrr, Scheme.Hom.comp_apply] at h
      exact h)
    have hρ₁ : ρ ≫ i₁ = r := by rw [← cancel_mono (p ⁻¹ᵁ V τ).ι, Category.assoc, hi₁, hρ]
    have hρ₂ : ρ ≫ i₂ = r' := by rw [← cancel_mono (p ⁻¹ᵁ V τ').ι, Category.assoc, hi₂, hρ, hrr]
    have hφ : i₂ ≫ (p ⁻¹ᵁ V τ').ι ≫ 𝟙 X = i₁ ≫ (p ⁻¹ᵁ V τ).ι ≫ 𝟙 X := by
      rw [← Category.assoc, hi₂, ← Category.assoc, hi₁]
    obtain ⟨b', hb', hbv⟩ := exists_gen hN (φ' := fun _ : PUnit => i₁ ≫ (p ⁻¹ᵁ V τ).ι ≫ 𝟙 X)
      (ε' := fun _ => 1) (fun U _ h => by simp only [hφ]) (LB.pullGen N _ _ (n τ') i₂)
      (DVR.pullGen_isGen _ _ _ _ (hn τ') _)
    have sec : ∀ (σ : T) (l : p ⁻¹ᵁ U ≤ p ⁻¹ᵁ V σ), X.homOfLE l ≫ (p ⁻¹ᵁ V σ).ι = (p ⁻¹ᵁ U).ι →
        (e₂ ≫ X.homOfLE l) ≫ (p ⁻¹ᵁ V σ).ι ≫ p ≫ e = (e₂ ≫ X.homOfLE l) ≫ (p ⁻¹ᵁ V σ).ι := by
      intro σ l hl
      simp only [Category.assoc, reassoc_of% hl, reassoc_of% he₂, reassoc_of% he, hl, he₂]
    have key := gen_unique hN (p ∣_ U) e₂ hs₂ (hsurj U) (u := LB.pullGen N _ _ (n τ) i₁) (u' := b')
      (DVR.pullGen_isGen _ _ _ _ (hn τ) _) hb' (fun y J hJ => by
        rw [hbv _ _ y J hJ, val_pull hJ, val_pull hJ, hnv τ _ (e₂ ≫ i₁) y J hJ (sec τ l₁ hi₁),
          hnv τ' _ (e₂ ≫ i₂) y J hJ (sec τ' l₂ hi₂)]
        simp only [Category.assoc, reassoc_of% hi₁, reassoc_of% hi₂]) Z ρ z J hJ
    rw [val_pull hJ, hρ₁, hbv _ _ z J hJ, val_pull hJ, hρ₂] at key
    exact key
  obtain ⟨u, hu, -⟩ := glue_gen hN (fun _ : PUnit => 𝟙 X) (fun _ => 1) (fun τ => p ⁻¹ᵁ V τ)
    (fun x => ⟨p x, hV (p x)⟩) n hn agree
  have hle : ∀ i, N.U i ≤ LB.wchart N (fun _ : PUnit => 𝟙 X) (fun _ => i) := fun i x hx =>
    Set.mem_iInter.2 fun _ => hx
  refine ⟨⟨fun i => res (hle i) (u.s (fun _ => i))⟩, fun i j => unit_ext fun x hx => ?_⟩
  have h1 : (𝟙 X : X ⟶ X) x ∈ LB.wchart N (fun _ : PUnit => 𝟙 X) (fun _ => i) := hle i hx.1
  have h2 : (𝟙 X : X ⟶ X) x ∈ LB.wchart N (fun _ : PUnit => 𝟙 X) (fun _ => j) := hle j hx.2
  have key := gen_trans hu (𝟙 X) x h1 h2
  simp only [trF, Fintype.prod_unique, zpow_one, Category.comp_id] at key
  dsimp only
  rw [map_mul, gm_res (𝟙 X) x _ hx, gm_res (𝟙 X) x _ hx]
  exact (gm_res (𝟙 X) x (hle i) hx.1 _).trans (key.trans (congrArg _ (gm_res (𝟙 X) x (hle j) hx.2 _).symm))

theorem exists_gen_of_locally_trivial : ∀ (T : Scheme.{0}) (A' : Over T) [GrpObj A'] (N : LB A'.left), IsAbelianScheme A' → N.IsLB → Out.Rigidified A' N → (∀ τ : T, ∃ V : T.Opens, τ ∈ V ∧ ∃ s : (N.pull (A'.hom ⁻¹ᵁ V).ι).Gen, s.IsGen) → ∃ s : N.Gen, s.IsGen := by
  intro T A' _ N hA hN ⟨t, ht⟩ hloc
  exact exists_gen_of_local A'.hom (eSec A') (Over.w η[A']) (surj_restrict A' hA) hN t ht hloc

end GlobalTheory.RigTriv
end
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal UpperHalfPlane ReciprocityTheory.ChartRestriction.L1
open scoped UpperHalfPlane

namespace GlobalTheory.IdealTheta

theorem exists_primitive_rat {K : Type} [Field K] [CharZero K] (a₁ a₂ : K) (r s : ℚ)
    (h : (r : K) * a₁ + (s : K) * a₂ = 1) :
    ∃ (c : ℚ) (p q u v : ℤ), 0 < c ∧ p * v - q * u = 1 ∧ (p : K) * a₁ + (q : K) * a₂ = (c : K) := by
  set A : ℤ := r.num * s.den with hA
  set B : ℤ := s.num * r.den with hB
  have hr : (r : K) * (r.den : K) = (r.num : K) := by
    have := congrArg (fun t : ℚ => (t : K)) (Rat.mul_den_eq_num r)
    push_cast at this; exact this
  have hs : (s : K) * (s.den : K) = (s.num : K) := by
    have := congrArg (fun t : ℚ => (t : K)) (Rat.mul_den_eq_num s)
    push_cast at this; exact this
  have hAB : (A : K) * a₁ + (B : K) * a₂ = (r.den : K) * (s.den : K) := by
    rw [hA, hB]; push_cast
    rw [← hr, ← hs]
    linear_combination ((r.den : K) * (s.den : K)) * h
  have hN : (r.den : K) * (s.den : K) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr r.den_nz) (Nat.cast_ne_zero.mpr s.den_nz)
  have hg : Int.gcd A B ≠ 0 := by
    intro h0
    rw [Int.gcd_eq_zero_iff] at h0
    rw [h0.1, h0.2] at hAB
    apply hN
    rw [← hAB]; simp
  obtain ⟨p, hp⟩ : ((Int.gcd A B : ℕ) : ℤ) ∣ A := Int.gcd_dvd_left A B
  obtain ⟨q, hq⟩ : ((Int.gcd A B : ℕ) : ℤ) ∣ B := Int.gcd_dvd_right A B
  have hbez := Int.gcd_eq_gcd_ab A B
  set g : ℕ := Int.gcd A B with hgdef
  have hgZ : (g : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hg
  have hgK : (g : K) ≠ 0 := Nat.cast_ne_zero.mpr hg
  refine ⟨((r.den : ℚ) * (s.den : ℚ)) / (g : ℚ), p, q, -Int.gcdB A B, Int.gcdA A B, ?_, ?_, ?_⟩
  · have h1 : (0 : ℚ) < r.den := Nat.cast_pos.mpr r.den_pos
    have h2 : (0 : ℚ) < s.den := Nat.cast_pos.mpr s.den_pos
    have h3 : (0 : ℚ) < g := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hg)
    positivity
  · apply mul_left_cancel₀ hgZ
    linear_combination -hbez - Int.gcdA A B * hp - Int.gcdB A B * hq
  · have hpK : (A : K) = (g : K) * (p : K) := by exact_mod_cast congrArg (fun t : ℤ => (t : K)) hp
    have hqK : (B : K) = (g : K) * (q : K) := by exact_mod_cast congrArg (fun t : ℤ => (t : K)) hq
    push_cast
    rw [eq_div_iff hgK, ← hAB, hpK, hqK]
    ring

theorem main : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ) (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (Λ : PeriodPair), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) → 𝔞 ≠ 0 → GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.IsLatOf ι 𝔞 Λ → ∃ (c : ℚ) (θ : K) (τ : ℍ), 0 < c ∧ ι θ = (τ : ℂ) ∧ IsTauOf Λ (c : ℂ) τ ∧ ∀ x : K, x ∈ 𝔞 ↔ ∃ a b : ℤ, x = (c : K) * ((a : K) * θ + (b : K)) := by
  intro K _ _ d δ ι 𝔞 Λ hK _ _ _ hΛ
  obtain ⟨c₀, τ₀, hc₀, hlat⟩ := latTau Λ
  have hmem : ∀ z : ℂ, z ∈ Λ.lattice ↔ ∃ y : K, y ∈ 𝔞 ∧ ι y = z := by
    intro z
    have : z ∈ (Λ.lattice : Set ℂ) ↔ z ∈ ι '' (𝔞 : Set K) := by rw [hΛ]
    exact this
  obtain ⟨a₁, -, ha₁⟩ := (hmem (c₀ * τ₀)).mp ((hlat _).mpr ⟨1, 0, by simp⟩)
  obtain ⟨a₂, -, ha₂⟩ := (hmem c₀).mp ((hlat _).mpr ⟨0, 1, by simp⟩)
  have hA : ∀ x : K, x ∈ 𝔞 ↔ ∃ m n : ℤ, x = (m : K) * a₁ + (n : K) * a₂ := by
    intro x
    have h1 : x ∈ 𝔞 ↔ ι x ∈ Λ.lattice := by
      rw [hmem]
      exact ⟨fun h => ⟨x, h, rfl⟩, fun ⟨y, hy, e⟩ => ι.injective e ▸ hy⟩
    rw [h1, hlat]
    refine exists_congr fun m => exists_congr fun n => ?_
    rw [← ι.injective.eq_iff]
    simp only [map_add (f := _), map_mul, map_intCast, ha₁, ha₂]
    constructor <;> intro h <;> rw [h] <;> ring
  have hli : LinearIndependent ℚ ![a₁, a₂] := by
    rw [LinearIndependent.pair_iff]
    intro r s h
    rw [Rat.smul_def, Rat.smul_def] at h
    have h1 := congrArg ι h
    simp only [map_add (f := _), map_mul, map_ratCast, ha₁, ha₂, map_zero] at h1
    have h2 : (r : ℂ) * τ₀ + (s : ℂ) = 0 := by
      apply mul_left_cancel₀ hc₀
      linear_combination h1
    have h3 := congrArg Complex.im h2
    have hr : r = 0 := by
      have := τ₀.im_ne_zero
      simpa [this] using h3
    subst hr
    simpa using h2
  have hspan := hli.span_eq_top_of_card_eq_finrank (by simp [hK])
  obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp
    (show (1 : K) ∈ Submodule.span ℚ (Set.range ![a₁, a₂]) by rw [hspan]; trivial)
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Rat.smul_def] at hw
  obtain ⟨c, p, q, u, v, hc, hdet, hcK⟩ := exists_primitive_rat a₁ a₂ (w 0) (w 1) hw
  have hcK0 : (c : K) ≠ 0 := by exact_mod_cast hc.ne'
  have hcC0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hdetK : (p : K) * v - q * u = 1 := by exact_mod_cast congrArg (fun t : ℤ => (t : K)) hdet
  have hdetR : (p : ℝ) * v - q * u = 1 := by exact_mod_cast hdet
  set θ : K := -((u : K) * a₁ + (v : K) * a₂) / (c : K) with hθ
  have hcθ : (c : K) * θ = -((u : K) * a₁ + (v : K) * a₂) := by
    rw [hθ]; field_simp
  have hcC : (c : ℂ) = c₀ * ((p : ℂ) * τ₀ + q) := by
    have h1 := congrArg ι hcK
    simp only [map_add (f := _), map_mul, map_ratCast, map_intCast, ha₁, ha₂] at h1
    linear_combination -h1
  have hz : ((p : ℂ) * τ₀ + q) ≠ 0 := by
    intro h0; apply hcC0; rw [hcC, h0, mul_zero]
  have hιθ : ι θ = -((u : ℂ) * τ₀ + v) / ((p : ℂ) * τ₀ + q) := by
    have h1 := congrArg ι hcθ
    simp only [map_add (f := _), map_mul, map_neg, map_ratCast, map_intCast, ha₁, ha₂] at h1
    rw [eq_div_iff hz]
    apply mul_left_cancel₀ hc₀
    rw [hcC] at h1
    linear_combination h1
  have him : 0 < (ι θ).im := by
    rw [hιθ, Complex.div_im, ← sub_div]
    refine div_pos ?_ (Complex.normSq_pos.mpr hz)
    have hy : 0 < (τ₀ : ℂ).im := τ₀.im_pos
    simp only [Complex.neg_im, Complex.neg_re, Complex.add_im, Complex.add_re, Complex.mul_im, Complex.mul_re,
      Complex.intCast_im, Complex.intCast_re]
    have : -(↑u * (τ₀ : ℂ).im + 0 * (τ₀ : ℂ).re + 0) * (↑p * (τ₀ : ℂ).re - 0 * (τ₀ : ℂ).im + ↑q) -
        -(↑u * (τ₀ : ℂ).re - 0 * (τ₀ : ℂ).im + ↑v) * (↑p * (τ₀ : ℂ).im + 0 * (τ₀ : ℂ).re + 0) = (τ₀ : ℂ).im := by
      linear_combination (τ₀ : ℂ).im * hdetR
    rw [this]; exact hy
  have hmain : ∀ x : K, x ∈ 𝔞 ↔ ∃ a b : ℤ, x = (c : K) * ((a : K) * θ + (b : K)) := by
    intro x
    rw [hA]
    constructor
    · rintro ⟨m, n, rfl⟩
      refine ⟨m * q - n * p, m * v - n * u, ?_⟩
      push_cast
      linear_combination (-((m : K) * q - n * p)) * hcθ + ((m : K) * v - n * u) * hcK
        - ((m : K) * a₁ + (n : K) * a₂) * hdetK
    · rintro ⟨a, b, rfl⟩
      refine ⟨b * p - a * u, b * q - a * v, ?_⟩
      push_cast
      linear_combination (a : K) * hcθ - (b : K) * hcK
  refine ⟨c, θ, ⟨ι θ, him⟩, hc, rfl, ⟨hcC0, fun z => ?_⟩, hmain⟩
  rw [hmem]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨a, b, rfl⟩ := (hmain y).mp hy
    exact ⟨a, b, by simp⟩
  · rintro ⟨a, b, rfl⟩
    exact ⟨_, (hmain _).mpr ⟨a, b, rfl⟩, by simp⟩

end GlobalTheory.IdealTheta
end
