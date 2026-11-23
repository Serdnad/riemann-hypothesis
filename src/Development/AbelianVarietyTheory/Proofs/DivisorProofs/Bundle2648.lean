module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle586
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle986
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2621
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle863
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle031
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle001
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ConstDefSym

open GlobalTheory.CechPic

theorem lbIso_pull_of_const : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (k : Type) [Field k] [CharZero k] (ρ : R →+* DualNumber k) (B' : Over (Sp (DualNumber k))) (_ : GrpObj B') (π₁ π₂ : B'.left ⟶ Q.P.A.left), IsGrpPullback B' Q.P.A (spMap ρ) π₁ → IsGrpPullback B' Q.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → LBIso (Q.P.L.pull π₁) (Q.P.L.pull π₂) := by
  intro R _ _ Q k _ _ ρ B' _ π₁ π₂ h₁ h₂ hfib

  let ρ₀ : R →+* k := (TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ
  let A₀ : Over (Sp k) := (Over.pullback (spMap ρ₀)).obj Q.P.A
  letI : (Over.pullback (spMap ρ₀)).Monoidal :=
    (Over.instBraidedPullback (f := spMap ρ₀)).toMonoidal
  letI : GrpObj A₀ := Functor.grpObjObj
  have hj : IsGrpPullback A₀ Q.P.A (spMap ρ₀) (pullback.fst Q.P.A.hom (spMap ρ₀)) := isGrpPullback_pullback Q.P.A (spMap ρ₀)
  have ec : spMap (constHom ρ) = spMap (algebraMap k (DualNumber k)) ≫ spMap ρ₀ := by
    rw [spMap, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have h₂' : IsGrpPullback B' Q.P.A (spMap (algebraMap k (DualNumber k)) ≫ spMap ρ₀) π₂ := h₂.congr ec rfl
  let q : B'.left ⟶ A₀.left := hj.1.lift π₂ (B'.hom ≫ spMap (algebraMap k (DualNumber k)))
    (by rw [h₂'.1.w, Category.assoc])
  have hq₁ : q ≫ pullback.fst Q.P.A.hom (spMap ρ₀) = π₂ := hj.1.lift_fst _ _ _
  have hq₂ : q ≫ A₀.hom = B'.hom ≫ spMap (algebraMap k (DualNumber k)) := hj.1.lift_snd _ _ _
  have hq : IsGrpPullback B' A₀ (spMap (algebraMap k (DualNumber k))) q :=
    IsGrpPullback.cancel hj (h₂'.congr rfl hq₁.symm) hq₂
  have eid : GlobalTheory.DeRham.epsRed k ≫ spMap (algebraMap k (DualNumber k)) = 𝟙 _ := by
    rw [GlobalTheory.DeRham.epsRed, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    convert Spec.map_id (CommRingCat.of k)
    ext x
    simp
  let i : A₀.left ⟶ B'.left := hq.1.lift (𝟙 _) (A₀.hom ≫ GlobalTheory.DeRham.epsRed k)
    (by rw [Category.id_comp, Category.assoc, eid, Category.comp_id])
  have e : i ≫ q = 𝟙 _ := hq.1.lift_fst _ _ _
  have hi₂ : i ≫ B'.hom = A₀.hom ≫ GlobalTheory.DeRham.epsRed k := hq.1.lift_snd _ _ _
  haveI : IsMonHom (Iso.refl A₀).hom := inferInstanceAs (IsMonHom (𝟙 A₀))
  have hi : IsGrpPullback A₀ B' (GlobalTheory.DeRham.epsRed k) i :=
    IsGrpPullback.cancel hq ((isGrpPullback_of_iso (Iso.refl A₀)).congr eid.symm (by rw [e]; rfl)) hi₂
  have hA₀ : IsAbelianScheme A₀ := PolPull.isAbelianScheme_of_isGrpPullback Q.P.isAb hj

  have hL := Q.P.isLB
  have hsymA : pull (GrpObj.inv : Q.P.A ⟶ Q.P.A).left (cls Q.P.L hL) = cls Q.P.L hL := by
    have h0 := (cls_eq_zero_iff (LB.isLB_linComb hL _ _)).2 ⟨Q.sym, Q.sym_gen⟩
    rw [cls_linComb hL] at h0
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, one_smul, neg_smul,
      pull_id] at h0
    exact sub_eq_zero.1 (by simpa [sub_eq_add_neg] using h0)
  have key : ∀ {f : Sp (DualNumber k) ⟶ Sp R} (π : B'.left ⟶ Q.P.A.left), IsGrpPullback B' Q.P.A f π →
      LBIso ((Q.P.L.pull π).pull (GrpObj.inv : B' ⟶ B').left) (Q.P.L.pull π) := by
    intro f π hπ
    rw [← cls_eq_iff (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _)]
    show pull _ (pull π (cls Q.P.L hL)) = pull π (cls Q.P.L hL)
    rw [← pull_comp, GlobalTheory.SymSpread.inv_comp_of_isGrpPullback hπ, pull_comp, hsymA]
  have hfib' : i ≫ π₁ = i ≫ π₂ := hfib A₀.left i A₀.hom hi₂
  have hclosed : LBIso ((Q.P.L.pull π₁).pull i) ((Q.P.L.pull π₂).pull i) := by
    rw [← cls_eq_iff (pull_isLB (pull_isLB hL _) _) (pull_isLB (pull_isLB hL _) _)]
    show pull i (pull π₁ (cls Q.P.L hL)) = pull i (pull π₂ (cls Q.P.L hL))
    rw [← pull_comp, ← pull_comp, hfib']
  exact GlobalTheory.SymFirstOrder.lbIso_of_symmetric k A₀ B' i q hA₀ hi hq e _ _ (pull_isLB hL _) (pull_isLB hL _)
    (key π₁ h₁) (key π₂ h₂) hclosed

end GlobalTheory.ConstDefSym
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem primCris_isBC_of_nilThick : ∀ (A₀ : Over (Sp ℂ)) [GrpObj A₀] (g : ℕ), IsAbelianScheme A₀ → SmoothOfRelativeDimension g A₀.hom → ∀ (D : Type) [CommRing D] [Algebra ℂ D] (π : D →+* ℂ) (κ : DividedPowers (RingHom.ker π)), IsNilDP κ → (∀ a : ℂ, π (algebraMap ℂ D a) = a) → ∀ (k : GrpMor (dp0 ℂ) (𝟙 _) A₀ κ (spMap π) A₀ (algebraMap ℂ D) (𝟙 _) (Over.Hom.left (𝟙 A₀))), k.IsBC ∧ Submodule.span D (Set.range k.pull) = ⊤ := by
  intro A₀ _ g hA _ D _ _ π κ hκ hπ k
  haveI : Smooth A₀.hom := hA.smooth
  haveI : IsProper A₀.hom := hA.proper
  let P : Over (Sp ℂ) := A₀ ⊗ A₀
  haveI : Smooth P.hom := smooth_tensorObj_hom A₀ A₀
  haveI : IsProper P.hom := by
    change IsProper (A₀ ⊗ A₀).hom
    rw [Over.tensorObj_hom]; infer_instance
  have m2 : IsMor (dp0 ℂ) (P.hom ≫ 𝟙 _) κ (P.hom ≫ spMap π) (algebraMap ℂ D) (𝟙 P.left) :=
    ⟨k.dp, by rw [Category.assoc, ← k.base]; simp⟩
  have key : ∀ (f : P ⟶ A₀) (x : FirstDeRham (A₀.hom ≫ 𝟙 _)),
      pullOver κ (spMap π) f (k.isMor.pull1 x) = m2.pull1 (pullOver (dp0 ℂ) (𝟙 _) f x) := by
    intro f x
    have h'' : IsMor (dp0 ℂ) (A₀.hom ≫ 𝟙 _) κ (P.hom ≫ spMap π) (algebraMap ℂ D) f.left :=
      ⟨k.dp, by rw [← Category.assoc, Over.w f, Category.assoc, ← k.base]; simp⟩
    exact (IsMor.pullback1_comp k.isMor
        (IsMor.of_over κ (φ := f.left) (by rw [← Category.assoc, Over.w])) h'' (fun _ ↦ rfl)
        (by simp) x).trans
      (IsMor.pullback1_comp (IsMor.of_over (dp0 ℂ) (φ := f.left) (by rw [← Category.assoc, Over.w]))
        m2 h'' (fun _ ↦ rfl) (by simp) x).symm
  have hM : Function.Bijective (liftSemi k.isMor.pull1) :=
    GlobalTheory.T.crystalline_thickening_pullback_bijective ℂ D π κ hκ hπ A₀.left (A₀.hom ≫ 𝟙 _) (A₀.hom ≫ spMap π) (Over.Hom.left (𝟙 A₀))
      (by rw [Category.comp_id]; infer_instance) (by rw [Category.comp_id]; infer_instance)
      (by rw [Category.comp_id]; infer_instance) (by simp) (by simp) k.isMor
  have hN : Function.Bijective (liftSemi m2.pull1) :=
    GlobalTheory.T.crystalline_thickening_pullback_bijective ℂ D π κ hκ hπ P.left (P.hom ≫ 𝟙 _) (P.hom ≫ spMap π) (𝟙 P.left)
      (by rw [Category.comp_id]; infer_instance) (by rw [Category.comp_id]; infer_instance)
      (by rw [Category.comp_id]; infer_instance) (by simp) rfl m2
  have hZ : Function.Bijective (liftSemi k.pull) := by
    refine GlobalTheory.FlatKerLarge.liftSemi_bijective_of_exact_large ℂ D _ _ _ _ _ _ (prim (dp0 ℂ) (𝟙 _) A₀).subtype
      (pullOver (dp0 ℂ) (𝟙 _) μ[A₀] - pullOver (dp0 ℂ) (𝟙 _) (fst A₀ A₀) - pullOver (dp0 ℂ) (𝟙 _) (snd A₀ A₀))
      (prim κ (spMap π) A₀).subtype
      (pullOver κ (spMap π) μ[A₀] - pullOver κ (spMap π) (fst A₀ A₀) - pullOver κ (spMap π) (snd A₀ A₀))
      k.pull k.isMor.pull1 m2.pull1 (Submodule.injective_subtype _) ?_ (Submodule.injective_subtype _) ?_
      (fun _ ↦ rfl) ?_ hM hN.1
    · intro y
      rw [LinearMap.sub_apply, LinearMap.sub_apply, sub_sub, sub_eq_zero, ← mem_prim_iff]
      exact ⟨fun h ↦ ⟨⟨y, h⟩, rfl⟩, fun ⟨z, hz⟩ ↦ hz ▸ z.2⟩
    · intro y
      rw [LinearMap.sub_apply, LinearMap.sub_apply, sub_sub, sub_eq_zero, ← mem_prim_iff]
      exact ⟨fun h ↦ ⟨⟨y, h⟩, rfl⟩, fun ⟨z, hz⟩ ↦ hz ▸ z.2⟩
    · intro x
      simp only [LinearMap.sub_apply, map_sub, key]
  refine ⟨hZ, eq_top_iff.2 fun y _ ↦ ?_⟩
  obtain ⟨z, rfl⟩ := hZ.2 y
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x c => rw [liftSemi_tmul]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)
  | add x y hx hy => rw [map_add]; exact add_mem (hx trivial) (hy trivial)

end GlobalTheory
end

section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory

theorem relabel_cong {N r : ℕ} (e : (Fin r → ℤ) →ₗ[ℤ] (Fin r → ℤ)) (x y : Fin r → ℤ)
    (h : ∀ i, ((x i : ℤ) : ZMod N) = y i) : ∀ i, ((e x i : ℤ) : ZMod N) = e y i := by
  have hd : ∀ i, (N : ℤ) ∣ x i - y i := fun i => (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 (h i).symm
  choose w hw using hd
  have hxy : x - y = (N : ℤ) • w := by ext i; simp [hw i]
  have he : e x - e y = (N : ℤ) • e w := by rw [← map_sub, hxy, map_smul]
  intro i
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  have := congrFun he i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
  exact ⟨-(e w i), by linarith⟩

theorem qW_pull {s r : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) (f : (Fin r → ℤ) →ₗ[ℤ] (Fin r → ℤ))
    (b : LinearMap.BilinForm ℤ (Fin r → ℤ)) (y : Fin s → Fin r → ℤ) :
    qW W (pull f b) y = qW W b (fun u => f (y u)) := rfl

theorem relabel_minimisers : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (N : ℕ) [NeZero N] (r : ℕ) (μ : ((Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ))), (∀ c u i, ((μ c u i : ℤ) : ZMod N) = c u i) → ∀ e : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ), ∃ σ : Equiv.Perm (Fin 8 → Fin r → ZMod N), (∀ c u i, ((e.symm (μ (σ c) u) i : ℤ) : ZMod N) = c u i) ∧ ∀ b' : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W b' (μ c) ≤ qW W b' α) → (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W (pull e.toLinearMap b') ((fun c u => e.symm (μ (σ c) u)) c) ≤ qW W (pull e.toLinearMap b') α) := by
  intro W N _ r μ hμ e
  have key : ∀ (f g : (Fin r → ℤ) →ₗ[ℤ] (Fin r → ℤ)), (∀ x, g (f x) = x) → ∀ c u i,
      ((g (μ (fun u i => ((f (μ c u) i : ℤ) : ZMod N)) u) i : ℤ) : ZMod N) = c u i := by
    intro f g hgf c u i
    rw [relabel_cong g _ (f (μ c u)) (fun j => hμ _ u j) i, hgf, hμ]
  let σ : Equiv.Perm (Fin 8 → Fin r → ZMod N) :=
    { toFun := fun c u i => ((e (μ c u) i : ℤ) : ZMod N)
      invFun := fun c u i => ((e.symm (μ c u) i : ℤ) : ZMod N)
      left_inv := fun c => by
        funext u i
        exact key e.toLinearMap e.symm.toLinearMap (fun x => e.symm_apply_apply x) c u i
      right_inv := fun c => by
        funext u i
        exact key e.symm.toLinearMap e.toLinearMap (fun x => e.apply_symm_apply x) c u i }
  refine ⟨σ, fun c u i => key e.toLinearMap e.symm.toLinearMap (fun x => e.symm_apply_apply x) c u i, ?_⟩
  intro b' hmin c α hα
  rw [qW_pull, qW_pull]
  have h1 : (fun u => e.toLinearMap ((fun c u => e.symm (μ (σ c) u)) c u)) = μ (σ c) := by
    funext u; simp
  rw [h1]
  apply hmin (σ c) (fun u => e.toLinearMap (α u))
  intro u i
  show _ = ((e (μ c u) i : ℤ) : ZMod N)
  exact relabel_cong e.toLinearMap (α u) (μ c u) (fun j => (hα u j).trans (hμ c u j).symm) i

end GlobalTheory
end

section

noncomputable section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory.Poinc.Bdd

theorem sq_le_of_forall_nonneg {A B D : ℤ} (h : ∀ s t : ℤ, 0 ≤ s * s * A + 2 * (s * t) * B + t * t * D) :
    B * B ≤ A * D := by
  have hA : 0 ≤ A := by simpa using h 1 0
  have hD : 0 ≤ D := by simpa using h 0 1
  rcases hA.eq_or_lt with hA0 | hA0
  · subst hA0
    have h2 := h (-B * (D + 1)) 1
    have : B = 0 := by
      by_contra hB
      have hB2 : 1 ≤ B * B := by nlinarith [mul_self_pos.2 hB]
      nlinarith
    subst this; simp
  · have h1 := h B (-A)
    nlinarith

theorem seq_le (F : ℕ → ℤ) (h0 : ∀ k, 0 ≤ F k) (hlc : ∀ k, F (k + 1) * F (k + 1) ≤ F k * F (k + 2)) (d : ℕ)
    (p : ℕ → ℤ) (hd : p d = 1) (hrec : ∑ i ∈ Finset.range (d + 1), p i * F i = 0) :
    F 1 ≤ (∑ i ∈ Finset.range (d + 1), |p i|) * F 0 := by
  set C := ∑ i ∈ Finset.range (d + 1), |p i| with hCdef
  have hC1 : 1 ≤ C := by
    have := Finset.single_le_sum (f := fun i => |p i|) (fun i _ => abs_nonneg (p i)) (Finset.self_mem_range_succ d)
    simpa [hd] using this
  by_contra hlt
  push_neg at hlt
  have hF0 : 0 < F 0 := by
    rcases (h0 0).eq_or_lt with h | h
    · have := hlc 0
      rw [← h] at this hlt
      have h1 : F 1 * F 1 ≤ 0 := by simpa using this
      have : F 1 = 0 := by nlinarith [mul_self_nonneg (F 1)]
      simp [this] at hlt
    · exact h
  have hF1 : C * F 0 < F 1 := hlt
  have key : ∀ k, 0 < F k ∧ F 1 * F k ≤ F 0 * F (k + 1) := by
    intro k
    induction k with
    | zero => exact ⟨hF0, by rw [mul_comm]⟩
    | succ k ih =>
      obtain ⟨hk, hk'⟩ := ih
      have hpos : 0 < F (k + 1) := by
        have : 0 < F 1 * F k := mul_pos (by nlinarith) hk
        nlinarith
      refine ⟨hpos, ?_⟩
      have h2 := hlc k
      have h3 : F 1 * F k * F (k + 1) ≤ F 0 * F (k + 1) * F (k + 1) := mul_le_mul_of_nonneg_right hk' hpos.le
      have h4 : F k * (F 1 * F (k + 1)) ≤ F k * (F 0 * F (k + 2)) := by nlinarith
      exact le_of_mul_le_mul_left h4 hk
  have inc : ∀ k, C * F k < F (k + 1) := by
    intro k
    obtain ⟨hk, hk'⟩ := key k
    have : F 0 * (C * F k) < F 0 * F (k + 1) := by nlinarith
    exact lt_of_mul_lt_mul_left this hF0.le
  have mono : Monotone F := monotone_nat_of_le_succ fun k => by
    have := inc k
    have := (key k).1
    nlinarith
  cases d with
  | zero =>
    simp [hd] at hrec
    exact hF0.ne' hrec
  | succ e =>
    rw [Finset.sum_range_succ, hd, one_mul] at hrec
    rw [Finset.sum_range_succ, hd] at hCdef
    have hle : -(∑ i ∈ Finset.range (e + 1), p i * F i) ≤ (∑ i ∈ Finset.range (e + 1), |p i|) * F e := by
      rw [← Finset.sum_neg_distrib, Finset.sum_mul]
      refine Finset.sum_le_sum fun i hi => ?_
      have hi' : i ≤ e := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      have h1 : -(p i * F i) ≤ |p i| * F i := by
        have := neg_abs_le (p i)
        nlinarith [h0 i]
      exact h1.trans (mul_le_mul_of_nonneg_left (mono hi') (abs_nonneg _))
    have he := inc e
    have hpe := (key e).1
    have : F (e + 1) = -(∑ i ∈ Finset.range (e + 1), p i * F i) := by linarith
    rw [this] at he
    rw [hCdef] at he
    simp only [abs_one] at he
    nlinarith

theorem bddAct_of_isIntegral {O : Type} [CommRing O] (bar : O → O) (hmul : ∀ a b, bar (a * b) = bar a * bar b)
    (hone : bar 1 = 1) (hinv : ∀ a, bar (bar a) = a) (hint : ∀ a : O, IsIntegral ℤ a) : BddAct bar := by
  intro c
  obtain ⟨P, hPm, hP⟩ := hint (bar c * c)
  refine ⟨∑ i ∈ Finset.range (P.natDegree + 1), |P.coeff i|, ?_⟩
  intro X _ _ _ β hβ hpsd x
  have hpow : ∀ k, bar (c ^ k) = bar c ^ k := by
    intro k
    induction k with
    | zero => simpa using hone
    | succ k ih => rw [pow_succ, hmul, ih, pow_succ]
  have hcs : ∀ u v : X, β u v * β u v ≤ β u u * β v v := by
    intro u v
    refine sq_le_of_forall_nonneg fun s t => ?_
    have := hpsd (s • u + t • v)
    simp only [map_add (f := _), map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hβ.1 v u] at this
    linarith
  have hF : ∀ k, β (c ^ k • x) (c ^ k • x) = β x ((bar c * c) ^ k • x) := by
    intro k
    rw [hβ.2, smul_smul, hpow, mul_pow]
  set F : ℕ → ℤ := fun k => β (c ^ k • x) (c ^ k • x) with hFdef
  have hlc : ∀ k, F (k + 1) * F (k + 1) ≤ F k * F (k + 2) := by
    intro k
    set y := c ^ k • x
    have e1 : F (k + 1) = β y ((bar c * c) • y) := by
      simp only [hFdef, y, pow_succ', mul_smul]
      rw [hβ.2, smul_smul]
    have e2 : F (k + 2) = β ((bar c * c) • y) ((bar c * c) • y) := by
      have hw : bar (c * c) * (c * c) = bar (bar c * c) * (bar c * c) := by rw [hmul, hmul, hinv]; ring
      show β (c ^ (k + 2) • x) (c ^ (k + 2) • x) = β ((bar c * c) • (c ^ k • x)) ((bar c * c) • (c ^ k • x))
      rw [show c ^ (k + 2) = (c * c) * c ^ k by ring, mul_smul, hβ.2, hβ.2 (bar c * c), smul_smul, smul_smul, hw]
      simp only [mul_smul]
    rw [e1, e2]
    exact hcs _ _
  have hrec : ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * F i = 0 := by
    have h0 : β x ((Polynomial.aeval (bar c * c) P) • x) = 0 := by rw [Polynomial.aeval_def, hP, zero_smul, map_zero]

    rw [Polynomial.aeval_eq_sum_range, Finset.sum_smul, map_sum] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hFdef]
    dsimp only
    rw [hF, smul_assoc, map_zsmul, smul_eq_mul]
  have := seq_le F (fun k => hpsd _) hlc P.natDegree P.coeff hPm.coeff_natDegree hrec
  simpa [hFdef] using this

end GlobalTheory.Poinc.Bdd

namespace GlobalTheory.Poinc

open NumberField

theorem bddAct_int_and_cm : BddAct (id : ℤ → ℤ) ∧ ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), BddAct H.bar := by
  refine ⟨Bdd.bddAct_of_isIntegral id (fun _ _ => rfl) rfl (fun _ => rfl) fun a => Algebra.IsIntegral.isIntegral a, ?_⟩
  intro E _ _ _ H
  refine Bdd.bddAct_of_isIntegral H.bar (fun a b => map_mul _ a b) (map_one _) (fun a => ?_)
    fun a => Algebra.IsIntegral.isIntegral a
  apply RingOfIntegers.ext
  rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]

end GlobalTheory.Poinc
end
end

section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem eq_refl_of_isometry_congMod : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (β : LinearMap.BilinForm ℤ X), (∀ x, x ≠ 0 → 0 < β x x) → ∀ (e : X ≃ₗ[ℤ] X), (∀ x y, β (e x) (e y) = β x y) →
    ∀ N : ℕ, 3 ≤ N → (∀ x, CongMod N (e x) x) → e = LinearEquiv.refl ℤ X := by
  intro X _ _ _ β hpos e he N hN hc
  choose u hu using hc
  have hQ0 : ∀ x, 0 ≤ β x x := fun x => by
    by_cases h : x = 0
    · simp [h]
    · exact (hpos x h).le
  have hdec : ∀ x, x ≠ 0 → β (u x) (u x) < β x x := by
    intro x hx
    have h1 : 0 ≤ β (e x + x) (e x + x) := hQ0 _
    have h2 : β (e x - x) (e x - x) = (N : ℤ) * ((N : ℤ) * β (u x) (u x)) := by
      rw [show e x - x = N • u x by rw [hu x]; abel]
      simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
    simp only [map_add (f := _), map_sub, LinearMap.add_apply, LinearMap.sub_apply, he x x] at h1 h2
    have hc := hpos x hx
    have hd := hQ0 (u x)
    have hN' : (3 : ℤ) ≤ N := by exact_mod_cast hN
    nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul hN' hN' (by norm_num) (by omega)) hd]
  have hnil : ∀ n : ℕ, ∀ x, (β x x).toNat = n → ∃ k, u^[k] x = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro x hn
      by_cases hx : x = 0
      · exact ⟨0, by simpa using hx⟩
      · have hlt := hdec x hx
        have hd := hQ0 (u x)
        obtain ⟨k, hk⟩ := ih (β (u x) (u x)).toNat (by omega) (u x) rfl
        exact ⟨k + 1, by rw [Function.iterate_succ_apply]; exact hk⟩
  ext y
  by_contra hne
  have huy : u y ≠ 0 := fun h => hne (by rw [hu y, h]; simp)
  classical
  have hex : ∃ k, u^[k] y = 0 := hnil _ y rfl
  have hk : u^[Nat.find hex] y = 0 := Nat.find_spec hex
  have hmin : ∀ j < Nat.find hex, u^[j] y ≠ 0 := fun j hj => Nat.find_min hex hj
  have hy0 : y ≠ 0 := fun h => hne (by simp [h])
  have hk2 : 2 ≤ Nat.find hex := by
    by_contra h
    interval_cases h' : Nat.find hex
    · exact hy0 (by simpa using hk)
    · exact huy (by simpa using hk)
  have hux : u (u^[Nat.find hex - 2] y) ≠ 0 := by
    rw [← Function.iterate_succ_apply' u]
    exact hmin _ (by omega)
  have huux : u (u (u^[Nat.find hex - 2] y)) = 0 := by
    rw [← Function.iterate_succ_apply' u, ← Function.iterate_succ_apply' u]
    rw [show (Nat.find hex - 2).succ.succ = Nat.find hex by omega]
    exact hk
  set x := u^[Nat.find hex - 2] y
  have key := he x (u x)
  rw [hu x, hu (u x), huux] at key
  simp only [smul_zero, add_zero, map_add (f := _), map_nsmul, LinearMap.add_apply, LinearMap.smul_apply,
    nsmul_eq_mul] at key
  have hp := hpos (u x) hux
  have hN0 : (0 : ℤ) < N := by exact_mod_cast (show 0 < N by omega)
  nlinarith [mul_pos hN0 hp]

end GlobalTheory.Poinc
end
