module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2765
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1965
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2452
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle014
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionOfIntegralSectionIsIntegral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem fst_generic_app_injective {R : Type} [CommRing R] [IsDomain R] {X : Scheme.{0}} (p : X ⟶ Sp R) [Flat p]
    (W : X.Opens) : Function.Injective ((pullback.fst p (jK R)).app W).hom := by
  have : IsDominant (jK R) := by
    refine ⟨?_⟩
    change DenseRange (PrimeSpectrum.comap (algebraMap R (FractionRing R)))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))]
    exact bot_le
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK R)
  have : IsSchemeTheoreticallyDominant (pullback.fst p (jK R)) :=
    IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback p (jK R)).flip
  exact (pullback.fst p (jK R)).app_injective W

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SquareGeneric

theorem exists_gen_square :
    ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsNoetherianRing R'] [IsIntegrallyClosed R'] [IsLocalRing R'] (G' : Over (Sp R')) [GrpObj G'], IsSemiAbelian G' → IsAbelianScheme ((Over.pullback (jK R')).obj G') → ∀ N : LB G'.left, N.IsLB → ∀ a : 𝟙_ (Over (Sp R')) ⟶ G', ∃ t : LB.Gen (LB.LinComb N (K := Fin 3) ![(𝟙 G' * (toUnit G' ≫ a)).left, (𝟙 G' * (toUnit G' ≫ a⁻¹)).left, 𝟙 G'.left] ![1, 1, -2]), t.IsGen := by
  intro R' _ _ _ _ _ G' _ hG hA N hN a
  have := hG.comm
  let j := jK R'
  let πA := pullback.fst G'.hom j
  have hp : IsProper (pullback.snd G'.hom j) := hA.proper
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.RigCube.exists_gen_theta_generic G' hG hp hN
  let c : G' ⟶ G' := toUnit G' ≫ a
  let c' : G' ⟶ G' := toUnit G' ≫ a⁻¹
  let ℓ : G' ⟶ G3 G' := lift (𝟙 G') (lift c c')
  let h : pullback G'.hom j ⟶ pullback (G3 G').hom j :=
    pullback.map _ _ _ _ ℓ.left (𝟙 _) (𝟙 _) (by rw [Category.comp_id, Over.w]) (by simp)
  have hh : h ≫ pullback.fst (G3 G').hom j = πA ≫ ℓ.left := pullback.lift_fst _ _ _
  let t₁ := LB.pullGen (Theta G' N) (fun _ => pullback.fst (G3 G').hom j) (fun _ => 1) t₀ h
  have ht₁ : t₁.IsGen := DVR.pullGen_isGen _ _ _ _ ht₀ _
  obtain ⟨t₂, ht₂⟩ := gen_chartPull (chartPullIn N (thφ G' (x3 G')) thε (h ≫ pullback.fst (G3 G').hom j)) t₁ ht₁
  have hcc : c * c' = 1 := by
    simp only [c, c']
    rw [← MonObj.comp_mul, _root_.mul_inv_cancel, MonObj.comp_one]

  have hconst : ∀ s : 𝟙_ (Over (Sp R')) ⟶ G', ∃ i, ∀ y, (πA ≫ (toUnit G' ≫ s).left) y ∈ N.U i := by
    intro s
    obtain ⟨p₀⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R'))) := inferInstance
    obtain ⟨i, hi⟩ := exists_chart hN ((j ≫ s.left) p₀)
    have e : πA ≫ (toUnit G' ≫ s).left = pullback.snd G'.hom j ≫ j ≫ s.left := by
      have w : (toUnit G').left = G'.hom := (Category.comp_id _).symm.trans (Over.w (toUnit G'))
      rw [Over.comp_left, w, ← Category.assoc, pullback.condition, Category.assoc]
    refine ⟨i, fun y => ?_⟩
    rw [e, Scheme.Hom.comp_apply, Subsingleton.elim ((pullback.snd G'.hom j) y) p₀]
    exact hi
  let s₃ : Fin 3 → (𝟙_ (Over (Sp R')) ⟶ G') := ![a, a⁻¹, η[G']]
  choose i hi using fun k => hconst (s₃ k)
  let φw : Fin 3 → (pullback G'.hom j ⟶ G'.left) := fun k => πA ≫ (toUnit G' ≫ s₃ k).left
  obtain ⟨w, hw⟩ := GlobalTheory.AbSquare.exists_gen_of_mem_chart hN φw ![1, 1, -2] i hi
  let ψ : Fin 3 → (G'.left ⟶ G'.left) := ![(𝟙 G' * (toUnit G' ≫ a)).left, (𝟙 G' * (toUnit G' ≫ a⁻¹)).left, 𝟙 G'.left]
  have hF : ReciprocityTheory.ChartRestriction.G.Geo.Tor.FormEq
      (Sum.elim (fun I => (h ≫ pullback.fst (G3 G').hom j) ≫ thφ G' (x3 G') I) φw)
      (Sum.elim (fun I => -thε I) ![1, 1, -2]) (fun k => πA ≫ ψ k) ![1, 1, -2] := by
    intro U _ g
    rw [Fintype.prod_sum_type]
    dsimp only [Sum.elim_inl, Sum.elim_inr]
    simp only [zpow_neg, Finset.prod_inv_distrib]
    have e : ∀ I, (h ≫ pullback.fst (G3 G').hom j) ≫ thφ G' (x3 G') I = πA ≫ (ℓ.left ≫ thφ G' (x3 G') I) :=
      fun I => by rw [hh, Category.assoc]
    have e2 : (∏ I : thK, g ((h ≫ pullback.fst (G3 G').hom j) ≫ thφ G' (x3 G') I) ^ thε I) =
        ∏ I : thK, (fun q => g (πA ≫ q)) ((lift (𝟙 G') (lift c c')).left ≫ thφ G' (x3 G') I) ^ thε I :=
      Finset.prod_congr rfl fun I _ => by rw [e I]
    rw [e2, prod_cub (𝟙 G') c c' (fun q => g (πA ≫ q))]
    rw [show 𝟙 G' * c * c' = 𝟙 G' by rw [_root_.mul_assoc, hcc, _root_.mul_one], hcc]
    have f0 : φw 0 = πA ≫ c.left := rfl
    have f1 : φw 1 = πA ≫ c'.left := rfl
    have f2 : φw 2 = πA ≫ (1 : G' ⟶ G').left := rfl
    have p0 : ψ 0 = (𝟙 G' * c).left := rfl
    have p1 : ψ 1 = (𝟙 G' * c').left := rfl
    have p2 : ψ 2 = Over.Hom.left (𝟙 G') := (Over.id_left _).symm
    rw [Fin.prod_univ_three, Fin.prod_univ_three, f0, f1, f2, p0, p1, p2]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    abel
  obtain ⟨u, hu, -⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_gen hN hF (LB.mulGen N _ _ _ _ (LB.invGen N _ _ t₂) w)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.invGen_isGen _ _ _ _ ht₂) hw)
  obtain ⟨v, hv⟩ := gen_chartPull (chartPullOut N ψ ![1, 1, -2] πA (fun k => πA ≫ ψ k) (fun _ => rfl)) u hu
  exact GlobalTheory.PicGenericInj.exists_gen_of_generic R' G' hG _ (LB.isLB_linComb hN _ _) ⟨v, hv⟩

end GlobalTheory.SquareGeneric
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PowExtend

theorem isMonHom_of_components {𝒞 : Type*} [Category 𝒞] [CartesianMonoidalCategory 𝒞] {ι : Type}
    {A B C : 𝒞} [MonObj A] [MonObj B] [MonObj C] (p : ι → (B ⟶ C)) (hp : ∀ a, IsMonHom (p a))
    (hl : IsLimit (Fan.mk B p)) (e : A ⟶ B) (he : ∀ a, IsMonHom (e ≫ p a)) : IsMonHom e := by
  refine ⟨?_, ?_⟩
  · refine Fan.IsLimit.hom_ext hl _ _ fun a => ?_
    have := hp a
    have := he a
    change (_ ≫ e) ≫ p a = _ ≫ p a
    rw [Category.assoc, IsMonHom.one_hom, IsMonHom.one_hom]
  · refine Fan.IsLimit.hom_ext hl _ _ fun a => ?_
    have := hp a
    have := he a
    change (_ ≫ e) ≫ p a = (_ ≫ _) ≫ p a
    rw [Category.assoc, IsMonHom.mul_hom, Category.assoc, IsMonHom.mul_hom, ← Category.assoc,
      tensorHom_comp_tensorHom]

theorem exists_iso_of_universal {𝒞 : Type*} [Category 𝒞] {ι : Type} {A B C : 𝒞} (p : ι → (B ⟶ C))
    (hl : IsLimit (Fan.mk B p)) (q : ι → (A ⟶ C))
    (hq : ∀ (T : 𝒞) (y : ι → (T ⟶ C)), ∃! x : T ⟶ A, ∀ a, x ≫ q a = y a) :
    ∃ e : A ≅ B, ∀ a, e.hom ≫ p a = q a := by
  have hA : IsLimit (Fan.mk A q) :=
    mkFanLimit _ (fun s => (hq s.pt s.proj).exists.choose)
      (fun s a => (hq s.pt s.proj).exists.choose_spec a)
      (fun s m hm => (hq s.pt s.proj).unique hm (hq s.pt s.proj).exists.choose_spec)
  exact ⟨hA.conePointUniqueUpToIso hl, fun a => hA.conePointUniqueUpToIso_hom_comp hl ⟨a⟩⟩

theorem universal_of_iso {𝒞 : Type*} [Category 𝒞] {ι : Type} {A B C : 𝒞} (p : ι → (B ⟶ C))
    (hl : IsLimit (Fan.mk B p)) (E : A ≅ B) (T : 𝒞) (y : ι → (T ⟶ C)) :
    ∃! x : T ⟶ A, ∀ a, x ≫ (E.hom ≫ p a) = y a := by
  refine ⟨hl.lift (Fan.mk T y) ≫ E.inv, fun a => ?_, fun x hx => ?_⟩
  · rw [Category.assoc, E.inv_hom_id_assoc]
    exact hl.fac (Fan.mk T y) ⟨a⟩
  · rw [Iso.eq_comp_inv]
    refine Fan.IsLimit.hom_ext hl _ _ fun a => ?_
    exact ((Category.assoc _ _ _).trans (hx a)).trans (hl.fac (Fan.mk T y) ⟨a⟩).symm

theorem exists_pow_projections : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (G C : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj C] [IsCommMonObj C], IsSemiAbelian G → IsAbelianScheme C → ∀ pr' : Fin 8 → ((Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj C), (∀ a, IsMonHom (pr' a)) → (∀ (T' : Over (Sp (FractionRing R))) (y : Fin 8 → (T' ⟶ (Over.pullback (jK R)).obj C)), ∃! x : T' ⟶ (Over.pullback (jK R)).obj G, ∀ a, x ≫ pr' a = y a) → ∃ prO : Fin 8 → (G ⟶ C), (∀ a, IsMonHom (prO a)) ∧ (∀ a, (Over.pullback (jK R)).map (prO a) = pr' a) ∧ ∀ (T' : Over (Sp R)) (y : Fin 8 → (T' ⟶ C)), ∃! x : T' ⟶ G, ∀ a, x ≫ prO a = y a := by
  intro R _ _ _ _ G C _ _ _ _ hG hC pr' hm hu
  have hH : IsSemiAbelian (powObj C 8) :=
    GlobalTheory.SemiPow.isSemiAbelian_of_isPowGrp _ C (powObj C 8) 8 (powIsPowGrp C 8)
      (GlobalTheory.isSemiAbelian_of_isAbelianScheme C hC)
  let prK : Fin 8 → ((Over.pullback (jK R)).obj (powObj C 8) ⟶ (Over.pullback (jK R)).obj C) :=
    fun i => (Over.pullback (jK R)).map (powPr C i)
  have hlim : IsLimit (Fan.mk ((Over.pullback (jK R)).obj (powObj C 8)) prK) :=
    isLimitFanMkObjOfIsLimit (Over.pullback (jK R)) (fun _ : Fin 8 => C) (powPr C) (powIsLimit C 8)
  have hprKm : ∀ i, IsMonHom (prK i) := fun i =>
    inferInstanceAs (IsMonHom ((Over.pullback (jK R)).map (powPr C i)))
  obtain ⟨e, he⟩ := exists_iso_of_universal prK hlim pr' hu
  have hem : IsMonHom e.hom := isMonHom_of_components prK hprKm hlim e.hom fun a => by
    rw [he a]; exact hm a
  obtain ⟨E, ⟨hE, hEe⟩, -⟩ := @GlobalTheory.SemiAbExtDomain.existsUnique_iso_extension_generic R _ _ _ _
    (FractionRing R) _ _ _ G (powObj C 8) _ _ hG hH e hem
  refine ⟨fun a => E.hom ≫ powPr C a, fun a => inferInstance, fun a => ?_,
    universal_of_iso (powPr C) (powIsLimit C 8) E⟩
  rw [Functor.map_comp, ← he a]
  exact congrArg (· ≫ prK a) hEe

end GlobalTheory.PowExtend
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem ideal_map_stalk_isPrime_of_closedPoint : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'], AdmBase R' (maximalIdeal R') → ∀ (G₁ : Over (Sp R')) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ x : G₁.left, G₁.hom x = closedPoint R' → ∀ q : Ideal R', q.IsPrime → (Ideal.map ((G₁.left.presheaf.germ ⊤ x trivial).hom.comp ((G₁.hom.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom)) q).IsPrime := by
  intro R' _ _ _ _ G₁ _ _ hG x hx q hq
  have := hG.smooth
  have := hG.geomConnected
  obtain ⟨U, hU, hxU, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp G₁.left.isBasis_affineOpens
    (show x ∈ (⊤ : G₁.left.Opens) from trivial)
  replace hU : IsAffineOpen U := hU
  let A := Γ(G₁.left, U)
  let ψ : R' →+* A := (G₁.left.presheaf.map (homOfLE le_top : U ⟶ ⊤).op).hom.comp
    ((G₁.hom.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom)
  have hφ : (G₁.left.presheaf.germ ⊤ x trivial).hom.comp ((G₁.hom.appTop).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom) = (G₁.left.presheaf.germ U x hxU).hom.comp ψ := by
    ext r
    rw [← TopCat.Presheaf.germ_res G₁.left.presheaf (homOfLE le_top : U ⟶ ⊤) x hxU]
    rfl
  rw [hφ, ← Ideal.map_map]
  letI : Algebra R' A := ψ.toAlgebra

  have hnu : ∀ r ∈ q, ¬ IsUnit ((G₁.left.presheaf.germ U x hxU).hom (ψ r)) := by
    intro r hr hu
    have key := DFunLike.congr_fun hφ r
    simp only [RingHom.comp_apply] at key
    rw [← key] at hu
    have hu := (Scheme.mem_basicOpen G₁.left _ x (show x ∈ (⊤ : G₁.left.Opens) from trivial)).mpr hu
    rw [← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine] at hu
    change G₁.hom x ∈ PrimeSpectrum.basicOpen r at hu
    rw [hx] at hu
    exact hu (IsLocalRing.le_maximalIdeal hq.ne_top hr)
  set P := hU.primeIdealOf ⟨x, hxU⟩
  letI : Algebra A (G₁.left.presheaf.stalk x) := TopCat.Presheaf.algebra_section_stalk G₁.left.presheaf ⟨x, hxU⟩
  haveI := hU.isLocalization_stalk ⟨x, hxU⟩
  have hle : Ideal.map ψ q ≤ P.asIdeal := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, ← IsLocalization.AtPrime.to_map_mem_maximal_iff (G₁.left.presheaf.stalk x) P.asIdeal]
    exact hnu r hr
  have hI : (Ideal.map ψ q).IsPrime := by
    haveI := hq
    have hne : Ideal.map ψ q ≠ ⊤ := fun h => P.isPrime.ne_top (top_le_iff.mp (h ▸ hle))
    let e := Algebra.TensorProduct.quotIdealMapEquivTensorQuot (A := R') A q
    haveI : Nontrivial (A ⧸ Ideal.map (algebraMap R' A) q) := Ideal.Quotient.nontrivial_iff.mpr hne
    haveI : Nontrivial (TensorProduct R' A (R' ⧸ q)) := e.symm.toEquiv.nontrivial
    have eSp : Spec.map (CommRingCat.ofHom (algebraMap R' A)) = hU.fromSpec ≫ G₁.hom := by
      apply ext_of_isAffine
      have h1 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R' A))
      rw [← Iso.eq_comp_inv] at h1
      rw [h1, Scheme.Hom.comp_appTop]
      change _ = _ ≫ hU.fromSpec.app ⊤
      rw [IsAffineOpen.fromSpec_app_of_le hU ⊤ le_top]
      rw [show (homOfLE le_top : hU.fromSpec ⁻¹ᵁ ⊤ ⟶ ⊤) = 𝟙 _ from rfl]
      erw [CategoryTheory.Functor.map_id, Category.comp_id]
      ext r
      simp [ψ, RingHom.algebraMap_toAlgebra]
    haveI : IsIntegral (Spec (CommRingCat.of (R' ⧸ q))) :=
      (affine_isIntegral_iff _).mpr (inferInstanceAs (IsDomain (R' ⧸ q)))
    haveI : IsIntegral (pullback G₁.hom (Spec.map (CommRingCat.ofHom (algebraMap R' (R' ⧸ q))))) :=
      GlobalTheory.isIntegral_pullback_of_smooth _ _
    let j := (pullbackSpecIso R' A (R' ⧸ q)).inv ≫ (pullback.congrHom eSp rfl).hom ≫
      (pullbackRightPullbackFstIso G₁.hom _ hU.fromSpec).inv ≫ pullback.snd _ _
    haveI : Nonempty (Spec (CommRingCat.of (TensorProduct R' A (R' ⧸ q)))) :=
      inferInstanceAs (Nonempty (PrimeSpectrum _))
    haveI := isIntegral_of_isOpenImmersion j
    haveI hdom := (affine_isIntegral_iff _).mp this
    haveI : IsDomain (A ⧸ Ideal.map (algebraMap R' A) q) := MulEquiv.isDomain _ e.toRingEquiv.toMulEquiv
    exact (Ideal.Quotient.isDomain_iff_prime _).mp this
  exact IsLocalization.isPrime_of_isPrime_disjoint P.asIdeal.primeCompl _ _ hI
    (Set.disjoint_left.mpr fun a ha h => ha (hle h))

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
noncomputable section

namespace GlobalTheory.SqGlue

theorem res_res {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (s : Γ(X, U)) :
    (X.presheaf.map (homOfLE h₂).op).hom ((X.presheaf.map (homOfLE h₁).op).hom s) =
      (X.presheaf.map (homOfLE (h₂.trans h₁)).op).hom s := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem subsingleton_of_not_nonempty {X : Scheme.{0}} {W : X.Opens} (h : ¬ Nonempty W) : Subsingleton Γ(X, W) := by
  have e : W = ⊥ := by
    ext x
    simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
    exact fun hx => h ⟨⟨x, hx⟩⟩
  subst e
  infer_instance

theorem res_cancel {X : Scheme.{0}} [IsIntegral X] {V W : X.Opens} (hW : W ≤ V) {a : Γ(X, V)} (ha : a ≠ 0)
    {b c : Γ(X, W)} (h : b * (X.presheaf.map (homOfLE hW).op).hom a = c * (X.presheaf.map (homOfLE hW).op).hom a) :
    b = c := by
  by_cases hn : Nonempty W
  · refine mul_right_cancel₀ (fun h0 => ha ?_) h
    apply map_injective_of_isIntegral X (homOfLE hW)
    rw [h0, map_zero]
  · exact (subsingleton_of_not_nonempty hn).elim _ _

theorem exists_unit_of_locally {X : Scheme.{0}} [IsIntegral X] {V W : X.Opens} (hW : W ≤ V) (s : Γ(X, W))
    {t : Γ(X, V)} (ht : t ≠ 0)
    (h : ∀ x ∈ W, ∃ (O : X.Opens) (hO : O ≤ W), x ∈ O ∧ ∃ u : Γ(X, O)ˣ,
      (X.presheaf.map (homOfLE hO).op).hom s = (u : Γ(X, O)) * (X.presheaf.map (homOfLE (hO.trans hW)).op).hom t) :
    ∃ c : Γ(X, W)ˣ, s = (c : Γ(X, W)) * (X.presheaf.map (homOfLE hW).op).hom t := by
  choose O hO hx u hu using fun x : W => h x.1 x.2
  have hcov : W ≤ iSup O := fun x hxW => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hxW⟩, hx _⟩
  have hcomp : TopCat.Presheaf.IsCompatible X.presheaf O (fun x => (u x : Γ(X, O x))) := by
    intro x y
    refine res_cancel (W := O x ⊓ O y) (inf_le_left.trans ((hO x).trans hW)) ht ?_
    have e₁ := congrArg (X.presheaf.map (homOfLE (inf_le_left : O x ⊓ O y ≤ O x)).op).hom (hu x)
    have e₂ := congrArg (X.presheaf.map (homOfLE (inf_le_right : O x ⊓ O y ≤ O y)).op).hom (hu y)
    rw [map_mul, res_res, res_res] at e₁ e₂
    exact e₁.symm.trans e₂
  obtain ⟨c, hc, -⟩ := X.sheaf.existsUnique_gluing' O W (fun x => homOfLE (hO x)) hcov
    (fun x => (u x : Γ(X, O x))) hcomp
  have hc' : ∀ x, (X.presheaf.map (homOfLE (hO x)).op).hom c = (u x : Γ(X, O x)) := hc
  have hunit : IsUnit (c : Γ(X, W)) := by
    refine X.toRingedSpace.isUnit_of_isUnit_germ W c fun x hxW => ?_
    have e := X.presheaf.germ_res_apply (homOfLE (hO ⟨x, hxW⟩)) x (hx ⟨x, hxW⟩) c
    have e' := (u ⟨x, hxW⟩).isUnit.map (X.presheaf.germ (O ⟨x, hxW⟩) x (hx ⟨x, hxW⟩)).hom
    rw [← hc'] at e'
    exact e ▸ e'
  refine ⟨hunit.unit, ?_⟩
  refine X.sheaf.eq_of_locally_eq' O W (fun x => homOfLE (hO x)) hcov _ _ fun x => ?_
  change (X.presheaf.map (homOfLE (hO x)).op).hom s = (X.presheaf.map (homOfLE (hO x)).op).hom _
  rw [map_mul, res_res, IsUnit.unit_spec, hc', hu x]

theorem app_res {X Y : Scheme.{0}} (f : X ⟶ Y) {U U' : Y.Opens} {O : X.Opens} (hU : U' ≤ U) (hO : O ≤ f ⁻¹ᵁ U')
    (s : Γ(Y, U)) :
    (X.presheaf.map (homOfLE (hO.trans (f.preimage_mono hU))).op).hom ((f.app U).hom s) =
      (X.presheaf.map (homOfLE hO).op).hom ((f.app U').hom ((Y.presheaf.map (homOfLE hU).op).hom s)) := by
  rw [← res_res (f.preimage_mono hU) hO]
  congr 1
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]
  rfl

def resU {X : Scheme.{0}} {A B : X.Opens} (h : B ≤ A) (u : Γ(X, A)ˣ) : Γ(X, B)ˣ :=
  Units.map (X.presheaf.map (homOfLE h).op).hom.toMonoidHom u

@[simp] theorem coe_resU {X : Scheme.{0}} {A B : X.Opens} (h : B ≤ A) (u : Γ(X, A)ˣ) :
    (resU h u : Γ(X, B)) = (X.presheaf.map (homOfLE h).op).hom u := rfl

theorem pow_ne_zero' {X : Scheme.{0}} [IsIntegral X] {V : X.Opens} {a : Γ(X, V)} (ha : a ≠ 0) (n : ℕ) : a ^ n ≠ 0 := by
  by_cases hn : Nonempty V
  · exact pow_ne_zero n ha
  · exact (ha ((subsingleton_of_not_nonempty hn).elim _ _)).elim

end GlobalTheory.SqGlue


open GlobalTheory.SqGlue in
theorem GlobalTheory.SqGlue.main : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'], AdmBase R' (maximalIdeal R') → ∀ (G₁ : Over (Sp R')) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (L2 : LB G₁.left), L2.IsLB → ∀ (h : L2.Sec) (Lθ : LB (pullback G₁.hom (jK R'))) (θ : Lθ.Sec), (∀ j i, ∃ w : Γ(pullback G₁.hom (jK R'), pullback.fst G₁.hom (jK R') ⁻¹ᵁ L2.U j ⊓ Lθ.U i)ˣ, ((pullback G₁.hom (jK R')).presheaf.map (homOfLE inf_le_right).op).hom (θ.f i) ^ 2 = (w : Γ(pullback G₁.hom (jK R'), pullback.fst G₁.hom (jK R') ⁻¹ᵁ L2.U j ⊓ Lθ.U i)) * ((pullback G₁.hom (jK R')).presheaf.map (homOfLE inf_le_left).op).hom (((pullback.fst G₁.hom (jK R')).app (L2.U j)).hom (h.f j))) → ∀ (Ix : Type) (V : Ix → G₁.left.Opens) (a : ∀ k, Γ(G₁.left, V k)), (∀ k, a k ≠ 0) → (∀ k j, ∃ u : Γ(G₁.left, V k ⊓ L2.U j)ˣ, (G₁.left.presheaf.map (homOfLE inf_le_right).op).hom (h.f j) = (u : Γ(G₁.left, V k ⊓ L2.U j)) * (G₁.left.presheaf.map (homOfLE inf_le_left).op).hom (a k) ^ 2) → (∀ k l, ∃ c : Γ(G₁.left, V k ⊓ V l)ˣ, (G₁.left.presheaf.map (homOfLE inf_le_left).op).hom (a k) ^ 2 = (c : Γ(G₁.left, V k ⊓ V l)) * (G₁.left.presheaf.map (homOfLE inf_le_right).op).hom (a l) ^ 2) ∧ (∀ k i, ∃ w : Γ(pullback G₁.hom (jK R'), pullback.fst G₁.hom (jK R') ⁻¹ᵁ V k ⊓ Lθ.U i)ˣ, ((pullback G₁.hom (jK R')).presheaf.map (homOfLE inf_le_right).op).hom (θ.f i) ^ 2 = (w : Γ(pullback G₁.hom (jK R'), pullback.fst G₁.hom (jK R') ⁻¹ᵁ V k ⊓ Lθ.U i)) * ((pullback G₁.hom (jK R')).presheaf.map (homOfLE inf_le_left).op).hom (((pullback.fst G₁.hom (jK R')).app (V k)).hom (a k)) ^ 2) := by
  intro R' _ _ _ _ G₁ _ _ hsemi L2 hL h Lθ θ hθ Ix V a hne hu
  haveI : Smooth G₁.hom := hsemi.smooth
  haveI : GeometricallyConnected G₁.hom := hsemi.geomConnected
  haveI : IsIntegral G₁.left := GlobalTheory.isIntegral_left_of_isSemiAbelian G₁
  haveI : IsIntegral (pullback G₁.hom (jK R')) := GlobalTheory.isIntegral_pullback_of_smooth G₁.hom (jK R')
  have hcov : ∀ x : G₁.left, ∃ j, x ∈ L2.U j := fun x => by
    have : x ∈ (⊤ : G₁.left.Opens) := trivial
    rw [← hL.cover] at this
    exact TopologicalSpace.Opens.mem_iSup.1 this
  set f := pullback.fst G₁.hom (jK R') with hf
  refine ⟨fun k l => ?_, fun k i => ?_⟩
  · refine (exists_unit_of_locally inf_le_right
      ((G₁.left.presheaf.map (homOfLE (inf_le_left : V k ⊓ V l ≤ V k)).op).hom (a k) ^ 2)
      (pow_ne_zero' (hne l) 2) fun x hx => ?_).imp fun c hc => by rwa [map_pow] at hc
    obtain ⟨j, hj⟩ := hcov x
    obtain ⟨uk, huk⟩ := hu k j
    obtain ⟨ul, hul⟩ := hu l j
    have hk : V k ⊓ V l ⊓ L2.U j ≤ V k ⊓ L2.U j := inf_le_inf_right _ inf_le_left
    have hl : V k ⊓ V l ⊓ L2.U j ≤ V l ⊓ L2.U j := inf_le_inf_right _ inf_le_right
    have e1 := congrArg (G₁.left.presheaf.map (homOfLE hk).op).hom huk
    have e2 := congrArg (G₁.left.presheaf.map (homOfLE hl).op).hom hul
    rw [map_mul, map_pow, res_res, res_res] at e1 e2
    have e : (resU hk uk : Γ(G₁.left, V k ⊓ V l ⊓ L2.U j)) *
        (G₁.left.presheaf.map (homOfLE (hk.trans inf_le_left)).op).hom (a k) ^ 2 =
        (resU hl ul : Γ(G₁.left, V k ⊓ V l ⊓ L2.U j)) *
        (G₁.left.presheaf.map (homOfLE (hl.trans inf_le_left)).op).hom (a l) ^ 2 := by
      rw [coe_resU, coe_resU, ← e1, ← e2]
    refine ⟨V k ⊓ V l ⊓ L2.U j, inf_le_left, ⟨hx, hj⟩, (resU hk uk)⁻¹ * resU hl ul, ?_⟩
    rw [map_pow, res_res, map_pow, Units.val_mul, _root_.mul_assoc, ← e, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]
  · have ht : (f.app (V k)).hom (a k) ≠ 0 := fun h0 =>
      hne k (GlobalTheory.ExpInt.generic_app_injective G₁ (V k) (h0.trans (map_zero _).symm))
    refine (exists_unit_of_locally inf_le_left
      ((((pullback G₁.hom (jK R')).presheaf.map (homOfLE (inf_le_right : f ⁻¹ᵁ V k ⊓ Lθ.U i ≤ Lθ.U i)).op).hom
        (θ.f i)) ^ 2) (pow_ne_zero' ht 2) fun y hy => ?_).imp fun c hc => by rwa [map_pow] at hc
    obtain ⟨j, hj⟩ := hcov (f.base y)
    obtain ⟨uk, huk⟩ := hu k j
    obtain ⟨w, hw⟩ := hθ j i
    have hO₁ : f ⁻¹ᵁ (V k ⊓ L2.U j) ⊓ Lθ.U i ≤ f ⁻¹ᵁ L2.U j ⊓ Lθ.U i :=
      inf_le_inf_right _ (f.preimage_mono inf_le_right)
    have hO₂ : f ⁻¹ᵁ (V k ⊓ L2.U j) ⊓ Lθ.U i ≤ f ⁻¹ᵁ (V k ⊓ L2.U j) := inf_le_left
    have hO₃ : f ⁻¹ᵁ (V k ⊓ L2.U j) ⊓ Lθ.U i ≤ f ⁻¹ᵁ V k ⊓ Lθ.U i :=
      inf_le_inf_right _ (f.preimage_mono inf_le_left)
    have e1 := congrArg ((pullback G₁.hom (jK R')).presheaf.map (homOfLE hO₁).op).hom hw
    rw [map_mul, map_pow, res_res, res_res] at e1
    rw [app_res f (inf_le_right : V k ⊓ L2.U j ≤ L2.U j) hO₂, huk, map_mul, map_mul, map_pow, map_pow,
      ← app_res f (inf_le_left : V k ⊓ L2.U j ≤ V k) hO₂] at e1
    refine ⟨_, hO₃, ⟨⟨hy.1, hj⟩, hy.2⟩, resU hO₁ w * resU hO₂ (Units.map (f.app (V k ⊓ L2.U j)).hom.toMonoidHom uk), ?_⟩
    rw [map_pow, res_res, map_pow, e1, Units.val_mul, coe_resU, coe_resU, Units.coe_map, _root_.mul_assoc]
    rfl
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.LocalPullGen

theorem main : ∀ (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) (L : LB X), L.IsLB →
    ∀ p : (𝟙_ (Over (Sp R))).left ⟶ X, ∃ ρ : LB.Gen (L.pull p), ρ.IsGen := by
  intro R _ _ X L hL p
  exact ReciprocityTheory.ChartRestriction.G.DVR.exists_gen_of_local (V := R) L hL (K := PUnit) (fun _ => p) (fun _ => 1)

end GlobalTheory.LocalPullGen
end
