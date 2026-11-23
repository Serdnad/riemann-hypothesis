module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle854
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3414
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3417
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3419
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle926
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsIsGenOfUniqueFactorizationMonoid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle893
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1264
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3422
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2879
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2737
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2889
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2137
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle226
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1607
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1180
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1909
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle094
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle065
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionOfCharZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
attribute [local instance] Functor.grpObjObj

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HTSummand

private theorem comp_mem_ker_smul_top
    {C C₀ k : Type} [CommRing C] [CommRing C₀] [IsLocalRing C₀] [CommRing k]
    {π : C →+* C₀} (hπ : Function.Surjective π) (q : C₀ →+* k)
    (hq : ∀ c ∈ IsLocalRing.maximalIdeal C₀, q c = 0)
    {H M V : Type 1} [AddCommGroup H] [Module C H]
    [AddCommGroup M] [Module C₀ M] [AddCommGroup V] [Module k V]
    (red : H →ₛₗ[π] M) (f : M →ₛₗ[q] V) (hsurj : Function.Surjective red)
    (hker : ∀ x, red x = 0 → x ∈ RingHom.ker π • (⊤ : Submodule C H))
    (fker : ∀ y, f y = 0 → y ∈ IsLocalRing.maximalIdeal C₀ • (⊤ : Submodule C₀ M))
    (h : H) (hh : f (red h) = 0) :
    h ∈ RingHom.ker (q.comp π) • (⊤ : Submodule C H) := by
  let N : Submodule C H := RingHom.ker (q.comp π) • (⊤ : Submodule C H)
  have lift (y : M) (hy : y ∈ IsLocalRing.maximalIdeal C₀ • (⊤ : Submodule C₀ M)) :
      ∃ x ∈ N, red x = y := by
    refine Submodule.smul_induction_on hy ?_ ?_
    · intro c hc y _
      obtain ⟨b, rfl⟩ := hπ c
      obtain ⟨x, rfl⟩ := hsurj y
      exact ⟨b • x, Submodule.smul_mem_smul (RingHom.mem_ker.2 (hq (π b) hc))
        Submodule.mem_top, red.map_smulₛₗ b x⟩
    · rintro y y' ⟨x, hx, rfl⟩ ⟨x', hx', rfl⟩
      exact ⟨x + x', N.add_mem hx hx', red.map_add x x'⟩
  obtain ⟨x, hx, hxe⟩ := lift _ (fker _ hh)
  have hle : RingHom.ker π ≤ RingHom.ker (q.comp π) := fun b hb ↦
    RingHom.mem_ker.2 (show q (π b) = 0 by rw [RingHom.mem_ker.1 hb, map_zero])
  have hsub : h - x ∈ N :=
    Submodule.smul_mono_left hle (hker _ (by rw [map_sub, hxe, sub_self]))
  simpa only [sub_add_cancel] using N.add_mem hsub hx

-- Check the two tensor module presentations before specializing to the closed fibre.
private theorem fibre_projective_tensorModOf
    (F : Type) [Field F] [NumberField F] (k : Type) [Field k]
    (B : Over (Sp k)) [GrpObj B] [IsCommMonObj B] (hB : IsAbelianScheme B)
    (a : OAct (𝓞 F) B) :
    letI := tensorModOf (act (dp0 k) (𝟙 _) a)
    Module.Projective (k ⊗[ℤ] 𝓞 F) (HdR B) := by
  change @Module.Projective _ _ _ _ (tensorModule (dp0 k) (𝟙 _) a)
  exact GlobalTheory.T.firstDeRhamHomology_projective_over_tensor_integers F k B hB a

theorem crys_projective : ∀ (F : Type) [Field F] [NumberField F] (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (A₀ : Over (Sp C₀)) [GrpObj A₀] [IsCommMonObj A₀], IsAbelianScheme A₀ → ∀ (O : Type) [Ring O] [Algebra (𝓞 F) O] (a : GlobalTheory.UPel.HT.OActN O A₀), letI := GlobalTheory.HTSummand.tensorModOf ((GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) a).comp (algebraMap (𝓞 F) O)); Module.Projective (C ⊗[ℤ] 𝓞 F) (Crys (divided₂ hsq) (spMap π) A₀) := by
  intro F _ _ C C₀ _ _ _ _ π hπ hsq A₀ _ _ hA O _ _ a
  have : Nontrivial C₀ := by
    refine ⟨⟨0, 1, fun h ↦ ?_⟩⟩
    have h1 : (1 : C) ∈ RingHom.ker π := by rw [RingHom.mem_ker, map_one]; exact h.symm
    have h2 : (1 : C) * 1 ∈ RingHom.ker π ^ 2 := by
      rw [pow_two]
      exact Ideal.mul_mem_mul h1 h1
    rw [_root_.one_mul, hsq] at h2
    exact one_ne_zero ((Submodule.mem_bot C).1 h2)
  have : IsLocalRing C₀ := IsLocalRing.of_surjective' π hπ
  obtain ⟨red, hfin, hproj, hsurj, hker, -, hequiv, -⟩ := GlobalTheory.T.exists_crystal_reduction_squareZero_artinian C C₀ π hπ hsq A₀ hA O a
  let a' : OAct (𝓞 F) A₀ :=
    { act := fun x ↦ a.act (algebraMap (𝓞 F) O x)
      hom := fun x ↦ a.hom _
      one := by rw [map_one]; exact a.one
      mul := fun x y ↦ by rw [mul_comm, map_mul, a.mul]
      add := fun x y ↦ by rw [map_add (f := _), a.add] }
  obtain ⟨f, fsurj, fker, fequiv⟩ := GlobalTheory.T.deRhamHomology_closedFibre_surjective_kernel C₀ A₀ hA (𝓞 F) a'
  let q := algebraMap C₀ (IsLocalRing.ResidueField C₀)
  let B := (Over.pullback (spMap q)).obj A₀
  let aB : OAct (𝓞 F) B := OAct.pullback (spMap q) A₀ a'
  have hB := GlobalTheory.isAbelianScheme_pullback_obj (spMap q) A₀ hA
  let σ := q.comp π
  have hσ : Function.Surjective σ := IsLocalRing.residue_surjective.comp hπ
  have : RingHomCompTriple π q σ := ⟨rfl⟩
  let H := Crys (divided₂ hsq) (spMap π) A₀
  let ρ := (crysAct (divided₂ hsq) (spMap π) a).comp (algebraMap (𝓞 F) O)
  let ρB := act (dp0 (IsLocalRing.ResidueField C₀)) (𝟙 _) aB
  have hq (c : C₀) (hc : c ∈ IsLocalRing.maximalIdeal C₀) : q c = 0 := by
    change algebraMap C₀ (IsLocalRing.ResidueField C₀) c = 0
    rw [IsLocalRing.ResidueField.algebraMap_eq]
    exact (IsLocalRing.residue_eq_zero_iff c).2 hc
  refine GlobalTheory.T.projective_tensor_of_fibre_projective'
    C (IsLocalRing.ResidueField C₀) (𝓞 F) σ hσ H (HdR B)
    ρ ρB (f.comp red) hfin hproj (fsurj.comp hsurj) ?_ ?_
      (fibre_projective_tensorModOf F (IsLocalRing.ResidueField C₀) B hB aB)
  · exact comp_mem_ker_smul_top hπ q hq red f hsurj hker fker
  · intro x h
    exact (congrArg (fun y : HdR A₀ ↦ f y) (hequiv (algebraMap (𝓞 F) O x) h)).trans
      (fequiv x (red h))

end GlobalTheory.HTSummand
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.PolLiftComplete

theorem exists_lift : ∀ (K : Type) [Field K] [IsAlgClosed K] (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (π : V →+* K), Function.Surjective π → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → (∀ (T : Over (Sp K)) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x = 1) → ∃ (AV : Over (Sp V)) (_ : GrpObj AV) (_ : IsCommMonObj AV) (φ : A.left ⟶ AV.left) (φ₂ : (G2 A).left ⟶ (G2 AV).left) (PV : LB (G2 AV).left), IsAbelianScheme AV ∧ IsGrpPullback A AV (spMap π) φ ∧ IsSquare φ φ₂ ∧ PV.IsLB ∧ (∃ t : (PV.pull (lift (1 : AV ⟶ AV) (𝟙 AV)).left).Gen, t.IsGen) ∧ (∃ t : (PV.pull (lift (𝟙 AV) (1 : AV ⟶ AV)).left).Gen, t.IsGen) ∧ LBIso PV (PV.pull (lift (snd AV AV) (fst AV AV)).left) ∧ Out.RelAmple AV (PV.pull (lift (𝟙 AV) (𝟙 AV)).left) ∧ (∀ (T : Over (Sp V)) (x : T ⟶ AV), (∃ t : (PV.pull (lift (snd AV T ≫ x) (fst AV T)).left).Gen, t.IsGen) → x = 1) ∧ LBIso P (PV.pull φ₂) := by
  intro K _ _ R₁ _ _ _ _ hc π hπ A _ _ hA P hP r₁ r₂ hs ha hker
  obtain ⟨L, hL, hΛ, haL⟩ := GlobalTheory.PolBundleLoc.exists_ample_root A hA hP r₁ r₂ hs ha
  have hKL : KTriv A L := GlobalTheory.KTrivOfLam.kTriv_of_lam_iso (Sp K) A hA P hP hker L hL hΛ
  set I := RingHom.ker π with hI
  have hItop : I ≠ ⊤ := by
    intro h
    have h1 : (1 : R₁) ∈ I := h ▸ Submodule.mem_top
    rw [hI, RingHom.mem_ker, map_one] at h1
    exact one_ne_zero h1
  have hIc : IsAdicComplete I R₁ := GlobalTheory.T.isAdicComplete_of_le_of_isNoetherianRing' R₁ I (maximalIdeal R₁) (le_maximalIdeal hItop) hc
  have hne : ∀ e : ℕ, I ^ (e + 1) ≠ ⊤ := fun e h =>
    hItop (top_le_iff.1 (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero e)))
  haveI hnt : ∀ e : ℕ, Nontrivial (R₁ ⧸ I ^ (e + 1)) := fun e => Ideal.Quotient.nontrivial_iff.2 (hne e)
  haveI hloc : ∀ e : ℕ, IsLocalRing (R₁ ⧸ I ^ (e + 1)) := fun e =>
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  let St : ℕ → Type 1 := fun e => Σ Y : Over (Sp (R₁ ⧸ I ^ (e + 1))), Σ _ : GrpObj Y,
    {L : LB Y.left // IsAbelianScheme Y ∧ L.IsLB ∧ RelAmple Y L ∧ KTriv Y L}
  have hstep : ∀ (e : ℕ) (y : St e), ∃ (y' : St (e + 1)) (i : y.1.left ⟶ y'.1.left),
      @IsGrpPullback _ _ y.1 y.2.1 y'.1 y'.2.1 (thickTrans R₁ I e) i ∧ LBIso y.2.2.1 (y'.2.2.1.pull i) := by
    rintro e ⟨Y, g, L, hA, hL, ha, hK⟩
    obtain ⟨Y', g', L', i, hA', hL', ha', hK', hi, hLi⟩ := GlobalTheory.SqStep.exists_lift (R₁ ⧸ I ^ (e + 1 + 1))
      (R₁ ⧸ I ^ (e + 1))
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1))))
      (Ideal.Quotient.factor_surjective _) (GlobalTheory.MumLift.ker_factor_sq I e) Y hA L hL ha hK
    exact ⟨⟨Y', g', L', hA', hL', ha', hK'⟩, i, hi, hLi⟩
  choose nx β hβ hLβ using hstep
  let e₀ : R₁ ⧸ I ^ (0 + 1) ≃+* K :=
    (Ideal.quotEquivOfEq (by rw [zero_add, pow_one])).trans (RingHom.quotientKerEquivOfSurjective hπ)
  let s : Sp (R₁ ⧸ I ^ (0 + 1)) ⟶ Sp K := spMap (e₀.symm : K →+* R₁ ⧸ I ^ (0 + 1))
  let t : Sp K ⟶ Sp (R₁ ⧸ I ^ (0 + 1)) := spMap (e₀ : R₁ ⧸ I ^ (0 + 1) →+* K)
  have hts : t ≫ s = 𝟙 _ := by
    simp only [t, s, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [RingEquiv.comp_symm]
    simp
  have htπ : t ≫ thick R₁ I 0 = spMap π := by
    simp only [t, thick, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
  let Y₀ : Over (Sp (R₁ ⧸ I ^ (0 + 1))) := (Over.pullback s).obj A
  let g₀ : Y₀.left ⟶ A.left := pullback.fst A.hom s
  have G₀ : IsGrpPullback Y₀ A s g₀ := isGrpPullback_pullback A s
  have hL₀ : (L.pull g₀).IsLB := pull_isLB hL g₀
  have hA₀ : IsAbelianScheme Y₀ := by
    have hcomm : IsCommMonObj Y₀ := by
      rw [isCommMonObj_iff_isMulCommutative]
      intro T
      refine ⟨⟨fun x y => Over.OverMorphism.ext (G₀.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
      rw [← G₀.2 T x y (pushPt G₀.1.w x) (pushPt G₀.1.w y) rfl rfl,
        ← G₀.2 T y x (pushPt G₀.1.w y) (pushPt G₀.1.w x) rfl rfl, _root_.mul_comm]
    exact { comm := hcomm
            smooth := MorphismProperty.of_isPullback (P := @Smooth) G₀.1 hA.smooth
            proper := MorphismProperty.of_isPullback (P := @IsProper) G₀.1 hA.proper
            geomConnected := MorphismProperty.of_isPullback (P := @GeometricallyConnected) G₀.1 hA.geomConnected }
  haveI := hA.proper
  have ha₀ : RelAmple Y₀ (L.pull g₀) := GlobalTheory.AmpleBaseChange.relAmple_of_isPullback hL haL G₀.1
  have hK₀ : KTriv Y₀ (L.pull g₀) := by
    obtain ⟨w, hw⟩ : LBIso (L.pull g₀) (L.pull g₀) := (GlobalTheory.CechPic.cls_eq_iff hL₀ hL₀).1 rfl
    exact kTriv_pull G₀ hL hL₀ ((isGen_iff w).1 hw) hKL
  let y₀ : St 0 := ⟨Y₀, inferInstance, L.pull g₀, hA₀, hL₀, ha₀, hK₀⟩
  let Y : ∀ n : ℕ, St n := fun n => Nat.rec (motive := fun n => St n) y₀ (fun n y => nx n y) n
  letI : ∀ e, GrpObj (Y e).1 := fun e => (Y e).2.1
  obtain ⟨B, _, M, b, hB, hM, haM, hb, -, hiso⟩ := GlobalTheory.AlgGroup.exists_abelianScheme_of_tower R₁ I hItop hIc hc
    (fun e => (Y e).1) (fun e => β e (Y e)) (fun e => (Y e).2.2.2.1) (fun e => hβ e (Y e))
    (fun e => (Y e).2.2.1) (fun e => (Y e).2.2.2.2.1) (fun e => hLβ e (Y e)) (Y 0).2.2.2.2.2.1
  haveI : IsCommMonObj B := hB.comm
  let φ : A.left ⟶ Y₀.left := pullback.lift (𝟙 _) (A.hom ≫ t)
    (by rw [Category.id_comp, Category.assoc, hts, Category.comp_id])
  have hφ₁ : φ ≫ g₀ = 𝟙 _ := pullback.lift_fst _ _ _
  have hφ₂ : φ ≫ Y₀.hom = A.hom ≫ t := pullback.lift_snd _ _ _
  haveI : IsMonHom (Iso.refl A).hom := inferInstanceAs (IsMonHom (𝟙 A))
  have n₀ : IsGrpPullback A A (t ≫ s) (φ ≫ g₀) :=
    (isGrpPullback_of_iso (Iso.refl A)).congr hts.symm hφ₁.symm
  have hcan : IsGrpPullback A Y₀ t φ := IsGrpPullback.cancel G₀ n₀ hφ₂
  have hi : IsGrpPullback A B (spMap π) (φ ≫ b 0) := (hcan.comp (hb 0)).congr htπ rfl
  have hLi : LBIso L (M.pull (φ ≫ b 0)) := by
    refine (GlobalTheory.CechPic.cls_eq_iff hL (pull_isLB hM _)).1 ?_
    have a₂ : GlobalTheory.CechPic.cls _ hL₀ = GlobalTheory.CechPic.cls _ (pull_isLB hM (b 0)) :=
      (GlobalTheory.CechPic.cls_eq_iff _ _).2 (hiso 0)
    rw [GlobalTheory.CechPic.cls_pull hM, GlobalTheory.CechPic.pull_comp, ← GlobalTheory.CechPic.cls_pull hM (b 0) (pull_isLB hM (b 0)), ← a₂,
      GlobalTheory.CechPic.cls_pull hL, ← GlobalTheory.CechPic.pull_comp, hφ₁, GlobalTheory.CechPic.pull_id]
  have hJ : I ^ (0 + 1) ≤ Ideal.jacobson ⊥ :=
    (Ideal.pow_le_self (Nat.succ_ne_zero 0)).trans (IsAdicComplete.le_jacobson_bot I)
  have hK : KTriv B M :=
    GlobalTheory.KTrivJacobson.kTriv_of_quotient R₁ (I ^ (0 + 1)) hJ B hB M hM haM Y₀ (b 0) (hb 0) _ hL₀ (hiso 0) hK₀
  have hPf := GlobalTheory.AbDual.isPerfect_lam hM hK
  have hr : Out.Rigidified B M := GlobalTheory.LB.exists_isGen_of_isLocalRing (R := R₁) (pull_isLB hM _)
  have hΘ := GlobalTheory.HodgeWeil.triv_theta GlobalTheory.CubeTop.cubeTheorem hB hM
  have w : (φ ≫ b 0) ≫ B.hom = A.hom ≫ spMap π := hi.1.w
  have sq := GlobalTheory.LamPull.exists_isSquare w
  have hlamA : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  have hlamB : (abelian₂ B M).IsLB := LB.isLB_linComb hM _ _
  refine ⟨B, inferInstance, hB.comm, φ ≫ b 0, _, abelian₂ B M, hB, hi, sq, hPf.isLB, hPf.zero_left, hPf.zero_right,
    GlobalTheory.FullSiegel.lam_symm hM, GlobalTheory.EighthPowerLocal.relAmple_diag_lam hB hM hΘ haM,
    fun T x h => GlobalTheory.FullSiegel.eq_one_of_lam_triv hM hr hK T x h, ?_⟩
  exact LBIso.trans hP hlamA (pull_isLB hlamB _) (LBIso.symm hΛ)
    (GlobalTheory.LamPull.lbIso_lam_pull hi hM hL hLi sq)

end GlobalTheory.PolLiftComplete
end
end

end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

theorem _root_.GlobalTheory.T.crystal_projective_over_tensor_ringOfIntegers : ∀ (F : Type) [Field F] [NumberField F] (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (A₀ : Over (Sp C₀)) [GrpObj A₀] [IsCommMonObj A₀], IsAbelianScheme A₀ → ∀ (O : Type) [Ring O] [Algebra (𝓞 F) O] (a : GlobalTheory.UPel.HT.OActN O A₀), letI := GlobalTheory.HTSummand.tensorModOf ((GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) a).comp (algebraMap (𝓞 F) O)); Module.Projective (C ⊗[ℤ] 𝓞 F) (Crys (divided₂ hsq) (spMap π) A₀) := by
  first | exact @GlobalTheory.HTSummand.crys_projective | exact GlobalTheory.HTSummand.crys_projective | (intros; apply GlobalTheory.HTSummand.crys_projective <;> assumption)

end
end
