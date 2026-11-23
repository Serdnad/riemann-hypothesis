module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineHomFromSpecResidueField
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle046
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle021
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SymVeryAmple


open GlobalTheory.CechPic in
theorem exists_of_involution {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
    (σ : X ⟶ X) (hσ : σ ≫ σ = 𝟙 X) (h : IsProjBy f) :
    ∃ (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB ∧ VeryAmpleBy f H s ∧
      Triv (LB.LinComb H (K := Fin 2) ![σ, 𝟙 X] ![1, -1]) := by
  obtain ⟨L, hL, m, s, hs⟩ := h
  have : IsProper f := isProper_of_veryAmpleBy hs
  have : IsIso σ := ⟨σ, hσ, hσ⟩
  have hA : IsAmpleLB L := isAmpleLB_of_veryAmpleBy hs
  have hP : IsAmpleLB (L.pull σ) := hA.pull_of_isAffineHom σ
  have hN : (tens L (L.pull σ)).IsLB := isLB_tens hL hP.isLB
  have hT : IsAmpleLB (tens L (L.pull σ)) := by
    refine hA.tensor hP hN ((cls_eq_zero_iff (LB.isLB_div (LB.isLB_div hN hL) hP.isLB)).1 ?_)
    rw [cls_div (LB.isLB_div hN hL) hP.isLB, cls_div hN hL, cls_tens hL hP.isLB]
    abel
  obtain ⟨n, -, M, t, ht⟩ := hT.exists_veryAmpleBy f
  have hH := isLB_lbPow hN n
  refine ⟨_, M, t, hH, ht, (cls_eq_zero_iff (LB.isLB_linComb hH _ _)).1 ?_⟩
  rw [cls_linComb hH, Fin.sum_univ_two, cls_lbPow hN, cls_tens hL hP.isLB, cls_pull hL]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, pull_id, map_nsmul, map_add (f := _), ← pull_comp, hσ]
  rw [add_comm (pull σ (cls L hL)), one_zsmul, neg_one_zsmul, Category.id_comp, add_neg_cancel]

theorem exists_symmetric_veryAmpleBy : ∀ (R : Type) [CommRing R] (B : Over (Spec (CommRingCat.of R))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → IsProjBy B.hom → ∃ (H : LB B.left) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB ∧ VeryAmpleBy B.hom H s ∧ Triv (LB.LinComb H (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1]) := by
  intro R _ B _ _ _ h
  refine exists_of_involution B.hom _ ?_ h
  rw [← Over.comp_left, GrpObj.inv_comp_inv, Over.id_left]

end GlobalTheory.SymVeryAmple
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PullAmpleFinite

open TopologicalSpace GlobalTheory.MulFinite

theorem sec_gs {Z Y : Scheme.{0}} {M : LB Y} (s : LB.Sec M) (r : Z ⟶ Y) (z : Z) {j j' : M.ι}
    (hj : r z ∈ M.U j) (hj' : r z ∈ M.U j') :
    gs r z (M.U j) (s.f j) = (gm r z (M.U j ⊓ M.U j') (M.g j j')).val * gs r z (M.U j') (s.f j') := by
  have hm : r z ∈ M.U j ⊓ M.U j' := ⟨hj, hj'⟩
  exact (gs_res r z _ hm _).symm.trans ((congrArg (gs r z _) (s.compat j j')).trans ((gs_mul r z _ hm _ _).trans
    (congrArg₂ (· * ·) (gs_unit r z _ hm _) (gs_res r z _ hm _))))

theorem pow_cancel {R : Type} [CommRing R] (g t : Rˣ) (x : R) (e : ℕ) :
    (g.val * x) ^ e * (1 * (g ^ (e : ℤ))⁻¹ * t).val = x ^ e * t.val := by
  have h : (g ^ e * (1 * (g ^ (e : ℤ))⁻¹ * t)) = t := by
    rw [zpow_natCast, _root_.one_mul, mul_inv_cancel_left]
  have h' : g.val ^ e * (1 * (g ^ (e : ℤ))⁻¹ * t).val = t.val := congrArg Units.val h
  rw [mul_pow, ← h']; ring

theorem exists_fn {X W Z : Scheme.{0}} (H : LB X) (hH : H.IsLB) (L : LB W) (hL : L.IsLB)
    (s : LB.Sec L) (m : W ⟶ X) (e : ℕ) (he : e ≠ 0)
    (α : LB.Iso (pw L e) (H.pull m)) (hα : α.IsGen)
    (r : Z ⟶ W) (j₀ : H.ι) (h₀ : ∀ z, m (r z) ∈ H.U j₀) :
    ∃ a : Γ(Z, ⊤), Z.basicOpen a = r ⁻¹ᵁ nonzeroLocus s := by
  let V : L.ι → Z.Opens := fun j => r ⁻¹ᵁ L.U j
  have l₂ : ∀ j, V j ≤ r ⁻¹ᵁ ((H.pull m).U (fun _ => j₀) ⊓ (pw L e).U j) :=
    fun j z hz => ⟨mem_pull.2 (h₀ z), hz⟩
  obtain ⟨u, hu⟩ : ∃ u : ∀ j, Γ(Z, V j), ∀ j z, z ∈ V j → gs (𝟙 Z) z (V j) (u j) =
      gs r z (L.U j) (s.f j) ^ e * (gw α r z j₀ j).val := by
    refine ⟨fun j => (r.appLE _ _ le_rfl).hom (s.f j) ^ e *
      (r.appLE _ _ (l₂ j)).hom (α.s (fun _ => j₀, j)).val, fun j z hz => ?_⟩
    refine (gs_mul (𝟙 Z) z (V j) hz _ _).trans (congrArg₂ (· * ·) ((gs_pow (𝟙 Z) z (V j) hz _ _).trans ?_) ?_)
    · exact congrArg (· ^ e) (gs_appLE r z _ _ _ hz _)
    · exact (gs_appLE r z _ _ _ hz _).trans (gs_unit r z _ (l₂ j hz) _)
  have hcov : (⊤ : Z.Opens) ≤ iSup V := fun z _ => by
    obtain ⟨j, hj⟩ := Geo.Tor.exists_chart hL (r z)
    exact Opens.mem_iSup.2 ⟨j, hj⟩
  obtain ⟨a, ha, -⟩ := Z.sheaf.existsUnique_gluing' V ⊤ (fun j => homOfLE le_top) hcov u
    (fun j j' => fn_ext (V := V j ⊓ V j') fun z hz => by
      refine (gs_res (𝟙 Z) z inf_le_left hz _).trans (Eq.trans ?_ (gs_res (𝟙 Z) z inf_le_right hz _).symm)
      rw [hu j z hz.1, hu j' z hz.2, sec_gs s r z hz.1 hz.2,
        (isGen_iff α).1 hα Z r z j₀ j₀ j j' (h₀ z) (h₀ z) hz.1 hz.2]
      have h1 : gm (r ≫ m) z (H.U j₀ ⊓ H.U j₀) (H.g j₀ j₀) = 1 := gm_self hH _ z (h₀ z)
      have t₁ : gm r z ((pw L e).U j ⊓ (pw L e).U j') ((pw L e).g j j') =
          gm r z (L.U j ⊓ L.U j') (L.g j j') ^ (e : ℤ) := map_zpow _ _ _
      rw [h1, t₁]
      exact pow_cancel _ _ _ _)
  refine ⟨a, ?_⟩
  ext z
  obtain ⟨j, hj⟩ := Geo.Tor.exists_chart hL (r z)
  have k₁ : gs (𝟙 Z) z ⊤ a = gs (𝟙 Z) z (V j) (u j) :=
    (gs_res (𝟙 Z) z le_top hj a).symm.trans (congrArg (gs (𝟙 Z) z (V j)) (ha j))
  have k₂ : z ∈ Z.basicOpen (show Γ(Z, ⊤) from a) ↔ IsUnit (gs r z (L.U j) (s.f j)) := by
    refine (isUnit_gs (𝟙 Z) z ⊤ trivial a).symm.trans ?_
    rw [k₁, hu j z hj, Units.isUnit_mul_units, isUnit_pow_iff he]
  refine k₂.trans ⟨fun h => ?_, fun h => ?_⟩
  · exact Opens.mem_iSup.2 ⟨j, (isUnit_gs r z _ hj _).1 h⟩
  · obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (show r z ∈ nonzeroLocus s from h)
    have hk' : r z ∈ L.U k := W.basicOpen_le _ hk
    rw [sec_gs s r z hj hk']
    exact (Units.isUnit _).mul ((isUnit_gs r z _ hk' _).2 hk)

theorem isFinite_of_pull_iso_pow :
    ∀ (K : Type) [Field K] (X X' : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of K)) (φ : X' ⟶ X) (H : LB X) (H' : LB X') (n : ℕ) (s : Fin (n + 1) → LB.Sec H') (d : ℕ), H.IsLB → H'.IsLB → IsSeparated f → VeryAmpleBy (φ ≫ f) H' s → 1 ≤ d → LBIso (pw H' d) (H.pull φ) → IsFinite φ := by
  intro K _ X X' f φ H H' n s d hH hH' hf hva hd ⟨α, hα⟩
  have : IsProper (φ ≫ f) := isProper_of_isProjBy K X' _ ⟨H', hH', n, s, hva⟩
  have : IsProper φ := .of_comp _ f
  suffices LocallyQuasiFinite φ from .of_isProper_of_locallyQuasiFinite _
  refine .of_fiberToSpecResidueField _ fun y => ?_
  obtain ⟨hcov, hs⟩ := hva
  have hy : ∀ z, φ (φ.fiberι y z) = y := fun z => (φ.range_fiberι y).le ⟨z, rfl⟩
  have := isAffineHom_fromSpecResidueField X y
  have : IsAffineHom (φ.fiberι y) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom.{0})
      (IsPullback.of_hasPullback φ (X.fromSpecResidueField y)).flip this
  obtain ⟨j₀, hj₀⟩ := Geo.Tor.exists_chart hH y
  have key := fun i => exists_fn H hH H' hH' (s i) φ d (by omega) α hα (φ.fiberι y) j₀ (fun z => by
    rw [hy]; exact hj₀)
  choose a ha using key
  have : IsProper (φ.fiberToSpecResidueField y) :=
    inferInstanceAs (IsProper (pullback.snd φ (X.fromSpecResidueField y)))
  refine locallyQuasiFinite_of_cover (K := X.residueField y) (φ.fiberToSpecResidueField y) a ?_ fun i => ?_
  · simp only [ha]
    rw [← Scheme.Hom.preimage_iSup]
    exact (congrArg (fun V => φ.fiberι y ⁻¹ᵁ V) hcov).trans rfl
  · rw [ha]
    exact (hs i).1.preimage _

end GlobalTheory.PullAmpleFinite
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.FiniteCover

variable {X X' : Scheme.{0}} [IsIntegral X] [IsIntegral X']

theorem rankAtStalk_bot {A C : Type} [CommRing A] [IsDomain A] [AddCommGroup C] [Module A C] :
    Module.rankAtStalk (R := A) C ⊥ = Module.finrank A C := by
  have h : (⊥ : PrimeSpectrum A).asIdeal.primeCompl ≤ nonZeroDivisors A := fun x hx =>
    mem_nonZeroDivisors_of_ne_zero fun h0 => hx (h0 ▸ Ideal.zero_mem _)
  rw [Module.rankAtStalk, IsLocalization.finrank_eq _ _ h]
  exact IsLocalizedModule.finrank_eq _ (LocalizedModule.mkLinearMap _ C) h

theorem generic_mem_preimage (φ : X' ⟶ X) [Surjective φ] {U : X.Opens} (h : genericPoint X ∈ U) :
    genericPoint X' ∈ φ ⁻¹ᵁ U := by
  obtain ⟨y, hy⟩ := φ.surjective (genericPoint X)
  exact generic_mem (x := y) (show φ y ∈ U from hy ▸ h)

theorem chart_data (φ : X' ⟶ X) [IsFinite φ] [Flat φ] [Surjective φ]
    [Algebra X.functionField X'.functionField]
    (hF : ∀ x, algebraMap X.functionField X'.functionField x = functionFieldMap φ x)
    {D : X.Opens} (hD : IsAffineOpen D) (h : genericPoint X ∈ D) :
    (∃ x, Module.finrank X.functionField X'.functionField = φ.finrank x) ∧
    ∀ {d : ℕ} (e : Module.Basis (Fin d) X.functionField X'.functionField),
      ∃ c ∈ (toField h).range, c ≠ 0 ∧
        (∀ j, ∀ y ∈ (toField (generic_mem_preimage φ h)).range, c * e.repr y j ∈ (toField h).range) ∧
        ∀ j, c • e j ∈ (toField (generic_mem_preimage φ h)).range := by
  have h' := generic_mem_preimage φ h
  haveI : Nonempty D := ⟨⟨_, h⟩⟩
  haveI : Nonempty (φ ⁻¹ᵁ D) := ⟨⟨_, h'⟩⟩
  letI := (φ.app D).hom.toAlgebra
  haveI : Module.Finite Γ(X, D) Γ(X', φ ⁻¹ᵁ D) := φ.finite_app D hD
  haveI : Module.Flat Γ(X, D) Γ(X', φ ⁻¹ᵁ D) := by
    have := φ.flat_appLE hD (hD.preimage φ) le_rfl
    rwa [Scheme.Hom.appLE_eq_app] at this
  haveI := functionField_isFractionRing_of_isAffineOpen X D hD
  haveI := functionField_isFractionRing_of_isAffineOpen X' _ (hD.preimage φ)
  letI : Algebra Γ(X, D) X'.functionField :=
    ((algebraMap X.functionField X'.functionField).comp (algebraMap Γ(X, D) X.functionField)).toAlgebra
  haveI : IsScalarTower Γ(X, D) X.functionField X'.functionField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower Γ(X, D) Γ(X', φ ⁻¹ᵁ D) X'.functionField :=
    IsScalarTower.of_algebraMap_eq fun a => by
      have e := toField_appLE φ le_rfl h h' a
      rw [Scheme.Hom.appLE_eq_app] at e
      exact (hF _).trans e.symm
  refine ⟨⟨hD.fromSpec (⊥ : PrimeSpectrum Γ(X, D)), ?_⟩, fun e => ?_⟩
  · have hp : IsPullback (hD.preimage φ).fromSpec (Spec.map (φ.app D)) φ hD.fromSpec :=
      (IsOpenImmersion.isPullback _ _ _ _ (by
        rw [Scheme.Hom.app_eq_appLE, IsAffineOpen.SpecMap_appLE_fromSpec φ hD (hD.preimage φ)])
        (by simp)).flip
    rw [IsFractionRing.finrank_eq Γ(X, D) X.functionField Γ(X', φ ⁻¹ᵁ D) X'.functionField,
      ← rankAtStalk_bot]
    refine Eq.trans ?_ (Scheme.Hom.finrank_of_isPullback _ _ _ _ hp _)
    exact (Scheme.Hom.finrank_SpecMap_algebraMap Γ(X, D) Γ(X', φ ⁻¹ᵁ D) _).symm
  · obtain ⟨c, hc, h₁, h₂⟩ := exists_denominator (A := Γ(X, D)) (C := Γ(X', φ ⁻¹ᵁ D)) e
    refine ⟨toField h c, ⟨c, rfl⟩, fun h0 => hc (toField_injective h (h0.trans (map_zero _).symm)),
      ?_, h₂⟩
    rintro j _ ⟨y, rfl⟩
    exact h₁ j y

theorem exists_mul_pow_mem {D D' : X.Opens} (hD : IsAffineOpen D) (h : genericPoint X ∈ D)
    (h' : genericPoint X ∈ D') (r : Γ(X, D)) (hr : toField h r ≠ 0) (hle : X.basicOpen r ≤ D')
    (c : Γ(X, D')) : ∃ m : ℕ, toField h' c * toField h r ^ m ∈ (toField h).range := by
  have hb : genericPoint X ∈ X.basicOpen r :=
    (Scheme.mem_basicOpen X r _ h).2 (isUnit_iff_ne_zero.2 hr)
  have := hD.isLocalization_basicOpen r
  obtain ⟨m, b, e⟩ := IsLocalization.Away.surj r (rs X hle c)
  have e' : toField hb (rs X hle c * rs X (X.basicOpen_le r) r ^ m) =
      toField hb (rs X (X.basicOpen_le r) b) := congrArg (toField hb) e
  rw [map_mul, map_pow, toField_rs, toField_rs, toField_rs] at e'
  exact ⟨m, b, e'.symm⟩


omit [IsIntegral X] in
theorem basicOpen_le_nonzeroLocus {H : LB X} (s s' : LB.Sec H) (r : Γ(X, nonzeroLocus s))
    (h : ∀ k, rs X (inf_le_right : nonzeroLocus s ⊓ H.U k ≤ H.U k) (s'.f k) =
      rs X (inf_le_left : nonzeroLocus s ⊓ H.U k ≤ nonzeroLocus s) r *
        rs X (inf_le_right : nonzeroLocus s ⊓ H.U k ≤ H.U k) (s.f k)) :
    X.basicOpen r ≤ nonzeroLocus s' := by
  intro x hx
  have hs : x ∈ nonzeroLocus s := X.basicOpen_le r hx
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 hs
  have e := congrArg X.basicOpen (h l)
  rw [Scheme.basicOpen_mul] at e
  erw [Scheme.basicOpen_res, Scheme.basicOpen_res, Scheme.basicOpen_res] at e
  have hx' : x ∈ nonzeroLocus s ⊓ H.U l := ⟨hs, X.basicOpen_le _ hl⟩
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨l, (e.ge ⟨⟨hx', hx⟩, hx', hl⟩).2⟩

def powSec {X : Scheme.{0}} {H : LB X} (s : LB.Sec H) (t : ℕ) : LB.Sec (pw H t) where
  f k := (s.f k : Γ(X, H.U k)) ^ t
  compat i j := by
    have e := congrArg (· ^ t) (s.compat i j)
    simp only [mul_pow, ← map_pow] at e
    refine e.trans ?_
    congr 1

end GlobalTheory.FiniteCover

namespace GlobalTheory

open FiniteCover

theorem finrank_sec_pull_sandwich : ∀ (K : Type) [Field K] (X X' : Scheme.{0}) [IsIntegral X] [IsIntegral X'] (f : X ⟶ Spec (CommRingCat.of K)) (φ : X' ⟶ X) [IsFinite φ] [Etale φ] (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ d : ℕ, (∀ x : X, φ.finrank x = d) → (∀ t : ℕ, Module.Finite K (SecOnR f (pw H t) ⊤)) → (∀ t : ℕ, Module.Finite K (SecOnR (φ ≫ f) ((pw H t).pull φ) ⊤)) → ∃ a : ℕ, ∀ t : ℕ, d * Module.finrank K (SecOnR (f) (pw H t) ⊤) ≤ Module.finrank K (SecOnR (φ ≫ f) ((pw H (t + a : ℕ)).pull φ) ⊤) ∧ Module.finrank K (SecOnR (φ ≫ f) ((pw H t).pull φ) ⊤) ≤ d * Module.finrank K (SecOnR (f) (pw H (t + a : ℕ)) ⊤) := by
  intro K _ X X' _ _ f φ _ _ H n s hH hs d hd hV hW
  have hd1 : 1 ≤ d := hd _ ▸ φ.one_le_finrank_map (genericPoint X')
  haveI : Surjective φ := φ.one_le_finrank_iff_surjective.1 fun x => (hd x).symm ▸ hd1
  letI : Algebra X.functionField X'.functionField := (functionFieldMap φ).toAlgebra
  letI : Algebra K X.functionField := ((toField generic_top).comp (cst f ⊤)).toAlgebra
  letI : Algebra K X'.functionField := ((toField generic_top).comp (cst (φ ≫ f) ⊤)).toAlgebra
  haveI : IsScalarTower K X.functionField X'.functionField :=
    IsScalarTower.of_algebraMap_eq fun r => by
      have w : φ ≫ f = (φ ≫ f) ≫ Spec.map (CommRingCat.ofHom (RingHom.id K)) := by simp
      have e := toField_appLE φ (U := ⊤) (V := ⊤) le_top generic_top generic_top (cst f ⊤ r)
      exact (congrArg (toField generic_top)
        (appLE_cst w (V := ⊤) (V' := ⊤) le_top r)).symm.trans e
  obtain ⟨hcov, hs⟩ := hs
  choose haff r hr _ using hs
  let I := {i // genericPoint X ∈ nonzeroLocus (s i)}
  haveI : Fintype I := Fintype.ofFinite I
  let D : I → X.Opens := fun i => nonzeroLocus (s i.1)
  have hη : ∀ i, genericPoint X ∈ D i := fun i => i.2
  have hc : ⊤ ≤ ⨆ i, D i := fun x hx => by
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hcov.ge hx)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i, generic_mem hi⟩, hi⟩
  have hc' : ⊤ ≤ ⨆ i, φ ⁻¹ᵁ D i := fun x _ => by
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc (trivial : φ x ∈ ⊤))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
  obtain ⟨i₀, -⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc generic_top)
  obtain ⟨k₀, h₀⟩ := TopologicalSpace.Opens.mem_iSup.1 (hH.cover.ge generic_top)
  obtain ⟨x, hx⟩ := (chart_data φ (fun _ => rfl) (haff i₀.1) (hη i₀)).1
  rw [hd] at hx
  haveI : Module.Finite X.functionField X'.functionField :=
    Module.finite_of_finrank_pos (by omega)
  let e := Module.finBasisOfFinrankEq _ _ hx
  choose c hcm hc0 hc₁ hc₂ using fun i : I =>
    (chart_data φ (fun _ => rfl) (haff i.1) (hη i)).2 e
  let ρ : I → X.functionField := fun i => toField h₀ ((s i.1).f k₀)
  have hu : ∀ (i : I) k, IsUnit (rs X (inf_le_right : D i ⊓ H.U k ≤ H.U k) ((s i.1).f k)) :=
    fun i k => SecOn.isUnit_rs_of_le_nonzeroLocus _ k _ inf_le_left
  have hρ : ∀ i, ρ i ≠ 0 := fun i => by
    have := ((hu i k₀).map (toField (generic_inf (hη i) h₀))).ne_zero
    rwa [toField_rs] at this
  have hρr : ∀ i k : I, ρ i / ρ k = toField (hη k) (r k.1 i.1) := fun i k => by
    have := congrArg (toField (generic_inf (hη k) h₀)) (hr k.1 i.1 k₀)
    rw [map_mul, toField_rs, toField_rs, toField_rs] at this
    exact (div_eq_iff (hρ k)).2 this
  let τ : ∀ (t : ℕ) (i : I), SecOn (pw H t) (D i) := fun t i => GlobalTheory.LB.ofSec (powSec (s i.1) t) (D i)
  have hτc : ∀ (t : ℕ) (i : I) (k : H.ι), GlobalTheory.LB.coord (τ t i) k =
      rs X (inf_le_right : D i ⊓ H.U k ≤ H.U k) ((s i.1).f k) ^ t := fun t i k =>
    (GlobalTheory.LB.coord_ofSec _ _ _).trans (map_pow (rs X (inf_le_right : D i ⊓ H.U k ≤ H.U k)) _ _)
  have hτ : ∀ (t : ℕ) (i : I) (k : H.ι), IsUnit (GlobalTheory.LB.coord (τ t i) k) := fun t i k =>
    (hτc t i k).symm ▸ (hu i k).pow t
  have hτv : ∀ (t : ℕ) (i : I), secVal (M := pw H t) (k₀ := k₀) h₀ (hη i) (τ t i) = ρ i ^ t :=
    fun t i => (congrArg (toField (generic_inf (hη i) h₀)) (hτc t i k₀)).trans (by
      rw [map_pow, toField_rs])
  have h₀' : ∀ t : ℕ, genericPoint X' ∈ ((pw H t).pull φ).U fun _ => k₀ := fun t =>
    le_pull (pw H t) φ (i := k₀) le_rfl (generic_mem_preimage φ h₀)
  refine finrank_sandwich e (fun i => (toField (hη i)).range)
    (fun i => (toField (generic_mem_preimage φ (hη i))).range) ρ c hρ hc0
    (fun i k => ⟨_, (hρr i k).symm⟩) (fun i k => ?_) ?_ hc₁ hc₂
    (fun t => SecOnR f (pw H t) ⊤) (fun t => SecOnR (φ ≫ f) ((pw H t).pull φ) ⊤) hV hW
    (fun t => secValLin (M := pw H t) (k₀ := k₀) h₀ f fun _ => rfl)
    (fun t => secValLin (h₀' t) (φ ≫ f) fun _ => rfl)
    (fun t => secVal_injective (M := pw H t) (k₀ := k₀) h₀ generic_top)
    (fun t => secVal_injective (h₀' t) generic_top) (fun t x => ?_) fun t y => ?_
  · obtain ⟨a, ha⟩ := hcm i
    rw [← ha, hρr]
    exact exists_mul_pow_mem (haff k.1) (hη k) (hη i) _
      (hρr i k ▸ div_ne_zero (hρ i) (hρ k)) (FiniteCover.basicOpen_le_nonzeroLocus _ _ _ (hr k.1 i.1)) a
  · rintro i _ ⟨a, rfl⟩
    exact ⟨_, toField_appLE φ le_rfl (hη i) _ a⟩
  · refine (exists_secVal_eq_iff (M := pw H t) (k₀ := k₀) h₀ (isLB_pw hH t) D hc hη (τ t) (hτ t)
      x).trans ?_
    simp only [hτv]
  · refine (exists_secVal_eq_iff (h₀' t) (LB.isLB_pull (isLB_pw hH t) φ) (fun i => φ ⁻¹ᵁ D i) hc'
      (fun i => generic_mem_preimage φ (hη i)) (fun i => SecOn.pull (pw H t) φ (D i) (τ t i))
      (fun i k => (hτ t i (k PUnit.unit)).map _) y).trans ?_
    refine forall_congr' fun i => ?_
    rw [secVal_pull (M := pw H t) (k₀ := k₀) h₀ φ (hη i), hτv]
    rfl

end GlobalTheory
end
end

section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem exists_gen_of_chartPull {Y Y' : Scheme.{0}} {A' : LB Y'} {A : LB Y} {h : Y' ⟶ Y} (a : ChartPull A' A h)
    (t : LB.Gen A) (ht : t.IsGen) : ∃ t' : LB.Gen A', t'.IsGen := by
  refine ⟨⟨fun i => res (a.le i) (pullU h _ (t.s (a.idx i)))⟩, fun i j => unit_ext fun y hy => ?_⟩
  have v : ∀ i, y ∈ A'.U i → gm (𝟙 Y') y _ (res (a.le i) (pullU h _ (t.s (a.idx i)))) =
      gm h y (A.U (a.idx i)) (t.s (a.idx i)) := fun i hi =>
    (gm_res (𝟙 Y') y (a.le i) hi _).trans ((gm_pull (𝟙 Y') h y _ (a.le i hi) _).trans (by rw [Category.id_comp]))
  have hm : h y ∈ A.U (a.idx i) ⊓ A.U (a.idx j) := ⟨a.le i hy.1, a.le j hy.2⟩
  have e := congrArg (gm h y (A.U (a.idx i) ⊓ A.U (a.idx j))) (ht (a.idx i) (a.idx j))
  have e' := (gm_res h y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans
    (congrArg (_ * ·) (gm_res h y _ hm _))))
  refine ((gm_res (𝟙 Y') y _ hy _).trans (v i hy.1)).trans (e'.trans (Eq.symm ?_))
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (a.g y i j hy.1 hy.2)
    ((gm_res (𝟙 Y') y _ hy _).trans (v j hy.2)))

theorem polarisation_extends : Laws → (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (gen : (Over.pullback (jK V)).obj G ≅ A.A), IsMonHom gen.hom → ∃ L : RigLB G, LBIso (A.L.pull gen.hom.left) (L.L.pull (pullback.fst G.hom (jK V)))) := by
  intro hL V _ _ _ A G _ _ hG gen hgen
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  have := hG.geomConnected
  obtain ⟨t, ht⟩ := A.rigid
  have e₁ : eSec ((Over.pullback (jK V)).obj G) ≫ gen.hom.left = eSec A.A := by
    unfold eSec
    rw [← Over.comp_left, IsMonHom.one_hom]
  have e₂ : eSec ((Over.pullback (jK V)).obj G) ≫ jA V (FractionRing V) G = eK V (FractionRing V) G := by
    unfold eSec eK eSec
    simp
  obtain ⟨ρ, hρ⟩ := exists_gen_of_chartPull
    (chartPullLinComb A.L gen.hom.left (K := PUnit) (fun _ => eSec ((Over.pullback (jK V)).obj G))
      (fun _ => eSec A.A) (fun _ => 1) (𝟙 _) (fun _ => e₁.trans (Category.id_comp _).symm)) t ht
  obtain ⟨L, φ, hφ⟩ := hL.extend V (FractionRing V) G _ e₂ (A.L.pull gen.hom.left) (pull_isLB A.isLB _) ρ hρ
  exact ⟨L, LBIso.symm ⟨φ, hφ⟩⟩

end GlobalTheory.UU
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

theorem GlobalTheory.UU.torus_coord_add : (GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (x y : T ⟶ thickObj R I e G) (χ : D.X) (z : T.left) (J), Good D.P.L z J → val (g.t χ) (x * y).left z J * @id (T.left.presheaf.stalk z)ˣ (cubV D.cub (T := (Over.map (thick R I e)).obj T) z J (toUnit _ ≫ D.c χ) ((Over.map (thick R I e)).map x ≫ g.pG) ((Over.map (thick R I e)).map y ≫ g.pG)) = val (g.t χ) x.left z J * val (g.t χ) y.left z J) :=
  fun hG _ _ _ _ _ _ _ _ _ g _ x y χ z J hJ => GlobalTheory.TorusCoord.val_t_mul_points g hG χ x y z J hJ
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory

theorem isSemiAbelian_of_grpIso {S : Scheme.{0}} {G₁ G₂ : Over S} [GrpObj G₁] [GrpObj G₂] [hc : IsCommMonObj G₂]
    (e : G₂ ≅ G₁) [IsMonHom e.hom] (h : IsSemiAbelian G₁) : IsSemiAbelian G₂ := by
  have hi : IsIso e.hom.left := ((Over.forget S).mapIso e).isIso_hom
  have hw : G₂.hom = e.hom.left ≫ G₁.hom := (Over.w e.hom).symm
  have := h.smooth
  have := h.separated
  have := h.quasiCompact
  have hg := h.geomConnected
  refine ⟨hc, ?_, ?_, ?_, ?_, fun Ω _ _ q => ?_⟩
  · rw [hw]; infer_instance
  · rw [hw]; infer_instance
  · rw [hw]; infer_instance
  · refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ q => ?_⟩
    have hi' : IsIso ((Over.pullback q).map e.hom).left :=
      ((Over.pullback q ⋙ Over.forget _).mapIso e).isIso_hom
    have h1 : ConnectedSpace ((Over.pullback q).obj G₁).left := pullback_of_geometrically hg.1 K q
    exact (((Over.pullback q).map e.hom).left.homeomorph.connectedSpace_iff).2 h1
  · obtain ⟨E⟩ := h.fibres Ω q
    have : IsMonHom ((Over.pullback q).mapIso e).hom := inferInstanceAs (IsMonHom ((Over.pullback q).map e.hom))
    have : IsMonHom ((Over.pullback q).mapIso e).symm.hom :=
      inferInstanceAs (IsMonHom ((Over.pullback q).mapIso e).inv)
    exact ⟨torusExtOfIso ((Over.pullback q).mapIso e).symm E⟩

end GlobalTheory
end
