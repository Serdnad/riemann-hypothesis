module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle058
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle015
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle059
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubsingletonPrimeSpectrum
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle040
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0OfIsPullback
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorsionFormCompare
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorsionFormCompare

theorem exists_gen_of_eq {X Y : Scheme.{0}} (L : LB X) {p q : Y ⟶ X} (h : q = p) (n : ℤ)
    (a : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => p) (fun _ => n))) :
    ∃ b : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => q) (fun _ => n)),
      (∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : PUnit → L.ι),
        gm r z (LB.wchart L (fun _ => q) j) (b.s j) = gm r z (LB.wchart L (fun _ => p) j) (a.s j)) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι), val b r z J = val a r z J := by
  subst h
  exact ⟨a, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

theorem exists_mapsAt_id {X Y : Scheme.{0}} {L : LB X} {F : X ⟶ X} (hF : F = 𝟙 X) (p : Y ⟶ X) (n : ℤ)
    (a : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => p) (fun _ => n))) (ha : a.IsGen) :
    ∃ b : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => p ≫ F) (fun _ => n)),
      GeneratorPullback.MapsAt L L (J := PUnit) (fun _ => F) (isoPullId (idIso L) hF) p n a b ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι), val b r z J = val a r z J := by
  obtain ⟨b, hb, hv⟩ := exists_gen_of_eq L (q := p ≫ F) (p := p) (by rw [hF, Category.comp_id]) n a
  refine ⟨b, fun jN jL => unit_ext fun y hy => ?_, hv⟩
  have hL : p y ∈ L.U jL := hy.2
  have hN : p y ∈ L.U (jN PUnit.unit) := by
    have := mem_pull.1 hy.1
    rw [hF] at this
    exact this
  have m₁ : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L (fun _ : PUnit => p) jN := Set.mem_iInter.2 fun _ => hN
  have m₂ : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L (fun _ : PUnit => p) (fun _ => jL) := Set.mem_iInter.2 fun _ => hL
  refine (gm_res _ y _ hy _).trans ((hb _ _ y jN).trans ((gen_trans ha (𝟙 Y) y m₁ m₂).trans ?_))
  refine Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_zpow _ _ _).trans ?_) (gm_res _ y _ hy _)))
  rw [trF, Fintype.prod_unique]
  refine congrArg (· ^ n) ((gm_pull (𝟙 Y) p y _ hy _).trans ?_)
  exact gw_isoPullId (idIso L) hF (𝟙 Y ≫ p) y (jN PUnit.unit) jL hN hL

theorem exists_isIdPull : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (W : (Sp R).Opens), genericPoint (Sp R) ∈ W → Nonempty (PsiOn D W) → ∃ hD : IsPullDeg (RingHom.id R) D D, IsIdPull hD := by
  rintro R _ _ D W hW ⟨ψ⟩
  have hs := specOf_id R
  have mR : IsMonHom (Iso.refl D.P.A).hom := by show IsMonHom (𝟙 _); infer_instance
  have gp : IsGrpPullback D.P.A D.P.A (specOf (RingHom.id R)) (Iso.refl D.P.A).hom.left :=
    (isGrpPullback_of_iso (Iso.refl D.P.A)).congr hs.symm rfl
  obtain ⟨e, me, he⟩ := grpPullback_iso gp (isGrpPullback_pullback D.P.A (specOf (RingHom.id R)))
  have hF : e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R)) = 𝟙 _ := he
  have hz : eSec D.P.A ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R)) =
      specOf (RingHom.id R) ≫ eSec D.P.A := by
    rw [hF, hs, Category.comp_id]; exact (Category.id_comp _).symm
  have hgen : ∀ z : Sp (FractionRing R), jK R z ∈ W := by
    intro z
    have : jK R z = genericPoint (Sp R) := by
      rw [genericPoint_eq_bot_of_affine]
      apply PrimeSpectrum.ext
      show Ideal.comap (algebraMap R (FractionRing R)) z.asIdeal = ⊥
      have hz0 : z.asIdeal = ⊥ := @Ideal.eq_bot_of_prime _ _ _ z.isPrime
      rw [hz0]
      exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R _)
    rw [this]; exact hW
  have hr : Set.range (𝟙 (Sp (FractionRing R)) : _ ⟶ _) ⊆ Set.range (jK R ⁻¹ᵁ W).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hgen z
  let l := IsOpenImmersion.lift (jK R ⁻¹ᵁ W).ι (𝟙 _) hr
  have hl : l ≫ (jK R ⁻¹ᵁ W).ι = 𝟙 _ := IsOpenImmersion.lift_fac _ _ _
  refine ⟨{ e := e, e_hom := me, w := isoPullId (idIso D.P.L) hF
            w_gen := (isGen_iff _).2 (isoPullId_pgen (idIso_isGen D.P.isLB) hF)
            he := hz
            w_rig := isoPullId_maps (idIso_maps (⟨D.P.L, D.rig, D.P.isLB, D.rig_gen⟩ : RigLB D.P.A)) hF hs hz
            xe := AddEquiv.refl _
            c_pr := fun x => by rw [hF, hs, Category.comp_id]; exact (Category.id_comp _).symm
            W := W, psiW := ψ, g := l ≫ jK R ∣_ W
            g_comm := by
              rw [hs, Category.comp_id]
              exact (Category.assoc _ _ _).trans ((congrArg (l ≫ ·) (morphismRestrict_ι (jK R) W)).trans
                ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ jK R) hl).trans (Category.id_comp _))))
            psi_pr := fun x => ?_ }, fun _ => rfl, hF, fun Y f y j k hj hk => ?_⟩
  · obtain ⟨b, hb, hv⟩ := exists_mapsAt_id hF (D.xK x) (-1) (D.psi x) (D.psi_gen x)
    refine ⟨b, hb, corr_of_val D.P.isLB fun y J hJ => ?_⟩
    have c := val_corr hJ (ψ.psi_eq x) l
    have c₁ := val_pull hJ (ψ.psi x) (jK R ∣_ W) l
    have c₂ := val_pull hJ (D.psi x) (jK R ⁻¹ᵁ W).ι l
    have c₃ := val_pull hJ (ψ.psi x) (l ≫ jK R ∣_ W) (𝟙 _)
    refine (hv _ _ y J).trans (Eq.trans ?_ c₃.symm)
    refine (congrArg (fun r => val (D.psi x) r y J) hl).symm.trans (c₂.symm.trans (c.symm.trans (c₁.trans ?_)))
    exact congrArg (fun r => val (ψ.psi x) r y J) (Category.id_comp _).symm
  · exact gw_isoPullId (idIso D.P.L) hF f y j k hj hk

end GlobalTheory.TorsionFormCompare
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.DiagCoord

theorem exists_linearIndependent_of_iSupIndep {k V I T : Type} [Field k] [AddCommGroup V] [Module k V] [Finite I]
    (W : T → Submodule k V) (hW : iSupIndep W) (ty : I → T)
    (b : ∀ τ, Nonempty (Module.Basis (Fin (Nat.card {i // ty i = τ})) k (W τ))) :
    ∃ v : I → V, LinearIndependent k v ∧ ∀ i, v i ∈ W (ty i) := by
  classical
  let B : ∀ τ, Module.Basis (Fin (Nat.card {i // ty i = τ})) k (W τ) := fun τ => (b τ).some
  let e : ∀ τ, {i // ty i = τ} ≃ Fin (Nat.card {i // ty i = τ}) := fun τ => Finite.equivFin _
  let f : ∀ τ, {i // ty i = τ} → V := fun τ j => ((B τ (e τ j) : W τ) : V)
  have hmem : ∀ τ j, f τ j ∈ W τ := fun τ j => (B τ (e τ j)).2
  have hspan : ∀ τ, Submodule.span k (Set.range (f τ)) ≤ W τ := by
    intro τ
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact hmem τ j
  have hsig : LinearIndependent k (fun p : Σ τ, {i // ty i = τ} => f p.1 p.2) := by
    refine linearIndependent_iUnion_finite (fun τ => ?_) (fun τ t _ hτ => ?_)
    · exact ((B τ).linearIndependent.map' (W τ).subtype (Submodule.ker_subtype _)).comp
        (e τ) (e τ).injective
    · exact (hW.disjoint_biSup hτ).mono (hspan τ) (iSup₂_mono fun σ _ => hspan σ)
  let s : I → Σ τ, {i // ty i = τ} := fun i => ⟨ty i, ⟨i, rfl⟩⟩
  have hs : Function.Injective s := fun i j h => congrArg (fun p : Σ τ, {i // ty i = τ} => (p.2 : I)) h
  exact ⟨fun i => f (ty i) ⟨i, rfl⟩, hsig.comp s hs, fun i => hmem (ty i) ⟨i, rfl⟩⟩


open GlobalTheory.Serre ReciprocityTheory.ChartRestriction.G.Chart in
theorem exists_diff_linear {O : Type} [CommRing O] {A : Over (Sp ℂ)} [GrpObj A] [IsCommMonObj A] {L : LB A.left} {g : ℕ}
    (u : HolUnif A L g) (act : OAct O A) (h₁ : ∀ v, IsTangent v → ∃! w, u.IsDiff w v)
    (h₂ : ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) :
    ∃ d : Serre.Lie act →ₗ[ℂ] (Fin g → ℂ), Function.Injective d ∧ ∀ v, u.IsDiff (d v) v.hom := by
  classical
  let dd : Serre.Lie act → (Fin g → ℂ) := fun v => (h₁ v.hom (GlobalTheory.Serre.Lie.isTangent v)).exists.choose
  have hdd : ∀ v : Serre.Lie act, u.IsDiff (dd v) v.hom := fun v =>
    (h₁ v.hom (GlobalTheory.Serre.Lie.isTangent v)).exists.choose_spec
  have huniq : ∀ (v : Serre.Lie act) (w : Fin g → ℂ), u.IsDiff w v.hom → dd v = w := fun v w hw =>
    (h₁ v.hom (GlobalTheory.Serre.Lie.isTangent v)).unique (hdd v) hw
  have hcomb : ∀ (n : ℕ) (r : Fin n → ℂ) (vs : Fin n → Serre.Lie act),
      u.IsDiff (∑ i, r i • dd (vs i)) (∑ i, r i • vs i).hom := fun n r vs =>
    GlobalTheory.UnifDifferential.isDiff_of_isLieComb A L g n u (fun i => dd (vs i)) (fun i => (vs i).hom) r _
      (fun i => GlobalTheory.Serre.Lie.isTangent (vs i)) (fun i => hdd (vs i))
      ((GlobalTheory.Serre.Lie.isLieComb_iff r vs _).2 rfl)
  have hadd : ∀ v w : Serre.Lie act, dd (v + w) = dd v + dd w := by
    intro v w
    apply huniq
    have h2 := hcomb 2 ![1, 1] ![v, w]
    simpa [Fin.sum_univ_two] using h2
  have hsmul : ∀ (c : ℂ) (v : Serre.Lie act), dd (c • v) = c • dd v := by
    intro c v
    apply huniq
    have h1 := hcomb 1 ![c] ![v]
    simpa using h1
  refine ⟨{ toFun := dd, map_add' := hadd, map_smul' := hsmul }, ?_, hdd⟩
  intro v w hvw
  apply GlobalTheory.Serre.Lie.ext
  have hw : u.IsDiff (dd v) w.hom := by
    have := hdd w
    have hvw' : dd v = dd w := hvw
    rwa [← hvw'] at this
  exact (h₂ (dd v)).unique ⟨GlobalTheory.Serre.Lie.isTangent v, hdd v⟩ ⟨GlobalTheory.Serre.Lie.isTangent w, hw⟩

end GlobalTheory.DiagCoord


open GlobalTheory.DiagCoord GlobalTheory.Serre in
theorem GlobalTheory.exists_diagonal_coordinates_of_detCond :
    Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (act : OAct (𝓞 E) P.A) (ty : Fin P.g → (E →+* ℂ)), u.IsAH Hm χ → IsTypeFn H D.p D.q ty → DetCond D act (𝟙 (Sp ℂ)) H.rt0 → ∃ h : (Fin P.g → ℂ) ≃ₗ[ℂ] (Fin P.g → ℂ), ∀ (a : 𝓞 E) z, u.ex (h (fun i => ty i (a : E) * z i)) = u.ex (h z) ≫ act.act a := by
  intro _ _ _ _ E _ _ _ H D P u Hm χ act ty _ hty hdet
  unfold DetCond at hdet
  unfold IsTypeFn at hty
  have : IsCommMonObj P.A := Out.PolAV.isCommMonObj P
  obtain ⟨h₁, h₂⟩ := GlobalTheory.TorusTransfer.tangent_bijective u P.smoothDim
  obtain ⟨d, hdinj, hdd⟩ := exists_diff_linear u act h₁ h₂
  let ty' : Fin P.g → (𝓞 E →+* ℂ) := fun i => (ty i).comp (algebraMap (𝓞 E) E)
  have hinj : ∀ τ : 𝓞 E →+* ℂ, Function.Injective τ := by
    intro τ
    refine (RingHom.injective_iff_ker_eq_bot τ).2 (Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_)
    ext n
    simp [RingHom.mem_ker]
  have hcard : ∀ τ : 𝓞 E →+* ℂ, ∃ σ : E →+* ℂ, σ (H.rt : E) = τ H.rt ∧
      Nat.card {i // ty' i = τ} = Nat.card {i // ty i = σ} := by
    intro τ
    refine ⟨IsFractionRing.lift (hinj τ), IsFractionRing.lift_algebraMap (hinj τ) H.rt,
      Nat.card_congr (Equiv.subtypeEquivRight fun i => ⟨fun hi => ?_, fun hi => ?_⟩)⟩
    · refine IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun x => ?_)
      simp only [RingHom.comp_apply, IsFractionRing.lift_algebraMap]
      exact congrArg (fun f : 𝓞 E →+* ℂ => f x) hi
    · refine RingHom.ext fun x => ?_
      show ty i (algebraMap (𝓞 E) E x) = τ x
      rw [hi]
      exact IsFractionRing.lift_algebraMap (hinj τ) x
  have hb : ∀ τ : 𝓞 E →+* ℂ,
      Nonempty (Module.Basis (Fin (Nat.card {i // ty' i = τ})) ℂ (GlobalTheory.Serre.Lie.eig act τ)) := by
    intro τ
    obtain ⟨σ, hσ, hc⟩ := hcard τ
    refine (GlobalTheory.Serre.Lie.lieMult_id_iff act τ _).1 ?_
    rw [hc]
    by_cases hτ : τ H.rt = H.rt0
    · rw [(hty σ).1 (hσ.trans hτ)]
      exact (hdet τ).1 hτ
    · rw [(hty σ).2 (fun h => hτ (hσ.symm.trans h))]
      exact (hdet τ).2 hτ
  obtain ⟨v, hvli, hvmem⟩ :=
    exists_linearIndependent_of_iSupIndep (GlobalTheory.Serre.Lie.eig act) (GlobalTheory.Serre.Lie.iSupIndep_eig act) ty' hb
  choose F hF using fun a : 𝓞 E =>
    GlobalTheory.exists_linear_lift_of_isMonHom_polAV P P P.L P.L u u (act.act a) (act.hom a)
  have key : ∀ (a : 𝓞 E) (i : Fin P.g), F a (d (v i)) = ty i (a : E) • d (v i) := by
    intro a i
    have := act.hom a
    have e1 := GlobalTheory.HomLinear.isDiff_comp u u (act.act a) (F a) (hF a)
      (GlobalTheory.Serre.Lie.isTangent (v i)) (hdd (v i))
    have hv : a • v i = ty' i a • v i := (GlobalTheory.Serre.Lie.mem_eig_iff.1 (hvmem i)) a
    have e2 : (ty' i a • v i).hom = (v i).hom ≫ act.act a := by
      rw [← hv, GlobalTheory.Serre.Lie.hom_act_smul]
    rw [← e2] at e1
    have e3 := hdd (ty' i a • v i)
    rw [map_smul] at e3
    exact (h₁ _ (GlobalTheory.Serre.Lie.isTangent _)).unique e1 e3
  have hli : LinearIndependent ℂ (d ∘ v) := hvli.map' d (LinearMap.ker_eq_bot.2 hdinj)
  let B : Module.Basis (Fin P.g) ℂ (Fin P.g → ℂ) :=
    basisOfLinearIndependentOfCardEqFinrank' (d ∘ v) hli (by simp)
  have hB : ∀ i, B i = d (v i) := fun i => by simp [B]
  refine ⟨B.equivFun.symm, fun a z => ?_⟩
  rw [← hF a]
  refine congrArg u.ex ?_

  simp only [Module.Basis.equivFun_symm_apply, map_sum, map_smul, hB, key, smul_smul]
  exact Finset.sum_congr rfl fun i _ => by rw [mul_comm]
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.PeriodPoint

variable {E : Type} [Field E] [NumberField E]

theorem exists_embedding {k : Type} [Field k] [IsAlgClosed k] (β : ℂ →+* k) (τ : 𝓞 E →+* k) :
    ∃ τ₀ : E →+* ℂ, β.comp (τ₀.comp (algebraMap (𝓞 E) E)) = τ := by
  have : CharZero k := charZero_of_injective_ringHom β.injective
  have hτ : Function.Injective τ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
    rw [Ideal.under_def, RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
    exact RingHom.injective_int _
  have hb : Function.Bijective fun φ : E →+* ℂ => β.comp φ :=
    (Fintype.bijective_iff_injective_and_card _).2 ⟨fun φ ψ h => RingHom.ext fun a => β.injective (DFunLike.congr_fun h a),
      by rw [NumberField.Embeddings.card, NumberField.Embeddings.card]⟩
  obtain ⟨τ₀, h⟩ := hb.2 (IsFractionRing.lift hτ)
  refine ⟨τ₀, RingHom.ext fun a => ?_⟩
  exact (DFunLike.congr_fun h _).trans (IsFractionRing.lift_algebraMap hτ a)

variable [IsCMField E] {H : Host E}

theorem detCond_of_eigenbasis
    (lie : ∀ (k : Type) [Field k] (O : Type) [CommRing O] (G : Over (Sp k)) [GrpObj G] (act : OAct O G) (n : ℕ) (v : Fin n → (epsR k ⟶ G)) (τs : Fin n → (O →+* k)), Smooth G.hom → IsLieBasis v → (∀ i a, (v i ≫ act.act a).left = spMap (epsScale (τs i a)) ≫ (v i).left) → ∀ τ : O →+* k, LieMult act (𝟙 (Sp k)) τ (Nat.card {i // τs i = τ}))
    (D : Datum H) (t : SAB H (Sp ℂ)) {g : ℕ} (ty : Fin g → (E →+* ℂ)) (hty : IsTypeFn H D.p D.q ty)
    (v : Fin g → (epsR ℂ ⟶ t.G)) (hv : IsLieBasis v)
    (heig : ∀ i (a : 𝓞 E), (v i ≫ t.act.act a).left = spMap (epsScale (ty i (a : E))) ≫ (v i).left)
    {k : Type} [Field k] [IsAlgClosed k] (β : ℂ →+* k) : DetCond D t.act (spMap β) (β H.rt0) := by
  obtain ⟨t', m⟩ : ∃ t' : SAB H (Sp k), Nonempty (SABMap t' t (spMap β)) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap β) t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨m⟩ := m
  obtain ⟨v', hv', hφ⟩ := exists_isLieBasis_baseChange ℂ k β t.G t'.G m.cm.F m.cart t.semi.smooth g v hv
  have sc : ∀ c : k, spMap (epsScale c) ≫ spMap (algebraMap k (DualNumber k)) =
      spMap (algebraMap k (DualNumber k)) := fun c => by
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a <;> simp [epsScale, TrivSqZeroExt.algebraMap_eq_inl]
  have dm : ∀ c : ℂ, spMap (Chart.dualMapR β) ≫ spMap (epsScale c) =
      spMap (epsScale (β c)) ≫ spMap (Chart.dualMapR β) := fun c => by
    refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_comp _ _))
    ext a <;> simp [epsScale, Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  have key : ∀ τ₀ : E →+* ℂ, LieMult t.act (spMap β) (β.comp (τ₀.comp (algebraMap (𝓞 E) E)))
      (Nat.card {i // ty i = τ₀}) := fun τ₀ => by
    have h := lie k (𝓞 E) t'.G t'.act g v' (fun i => β.comp ((ty i).comp (algebraMap (𝓞 E) E))) t'.semi.smooth hv'
      (fun i a => m.cart.1.hom_ext ?_ ?_) (β.comp (τ₀.comp (algebraMap (𝓞 E) E)))
    · rw [LiePull.lieMult_pull _ _ _ t.G t'.G _ _ t.act t'.act m.cart m.act, Category.id_comp] at h
      convert h using 1
      refine Nat.card_congr (Equiv.subtypeEquivRight fun i => ⟨fun e => by rw [e], fun e => ?_⟩)
      exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
        (RingHom.ext fun a => β.injective (DFunLike.congr_fun e a))
    · have e := heig i a
      rw [Over.comp_left] at e
      rw [Over.comp_left, Category.assoc, m.act, ← Category.assoc, hφ, Category.assoc, e, Category.assoc, hφ,
        ← Category.assoc, dm, Category.assoc]
    · rw [Over.w, Category.assoc, Over.w]
      exact (sc _).symm
  intro τ
  obtain ⟨τ₀, rfl⟩ := exists_embedding β τ
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← (hty τ₀).1 (β.injective h)]; exact key τ₀
  · rw [← (hty τ₀).2 fun e => h (congrArg β e)]; exact key τ₀

theorem exists_fibre_unif {S : Scheme.{0}} (t : SAB H (Sp ℂ)) (t₀ : SAB H S) (y : Sp ℂ ⟶ S) (m : SABMap t t₀ y)
    {L : LB t.G.left} {g : ℕ} (u : HolUnif t.G L g) (h₁ : ∀ v, IsTangent v → ∃! w, u.IsDiff w v)
    (h₂ : ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) :
    ∃ e : (Fin g → ℂ) → (Over.mk y ⟶ t₀.G), (∀ z, (e z).left = (u.ex z).left ≫ m.cm.F) ∧
      ((∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧ IsHolTo Set.univ (fun z => (e z).left) ∧
        (∀ w, ∃! v : epsPt y ⟶ t₀.G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧
        (∀ v : epsPt y ⟶ t₀.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left →
          ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left)) ∧
      (∀ z, e z = 1 ↔ u.ex z = 1) ∧
      (∀ a z w, u.ex w = u.ex z ≫ t.act.act a → e w = e z ≫ t₀.act.act a) ∧
      ∀ (k : ℤ) z w c, Out.WeilIs t.G t.PP.L k (u.ex z) (u.ex w) c → Out.WeilIs t₀.G t₀.PP.L k (e z) (e w) c := by
  obtain ⟨φ, hφ⟩ := LiePull.exists_pushEquiv m.cart (𝟙_ (Over (Sp ℂ))) y (Category.id_comp y).symm
  obtain ⟨ψ, hψ⟩ := LiePull.exists_pushEquiv m.cart (epsR ℂ) (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y) rfl
  have hee : (fun z => (φ (u.ex z)).left) = fun z => (u.ex z).left ≫ m.cm.F := funext fun z => hφ _
  have hol : IsHolTo Set.univ (fun z => (u.ex z).left ≫ m.cm.F) := fun U f => by
    obtain ⟨a, b⟩ := u.hol (m.cm.F ⁻¹ᵁ U) ((m.cm.F.app U).hom f)
    simp only [← valAt'_comp, Set.mem_univ, true_and]
    exact ⟨a, b⟩
  have key : ∀ (w : Fin g → ℂ) (v : epsR ℂ ⟶ t.G), IsTangent v ∧ u.IsDiff w v ↔
      IsDerivAt0 (fun z => (φ (u.ex z)).left) w (ψ v).left := fun w v => by
    have e₀ : IsTangent v ∧ u.IsDiff w v ↔ IsDerivAt0 (fun z => (u.ex z).left) w v.left :=
      and_congr (by rw [IsTangent, ← TangentOrigin.ex_zero_left u]) Iff.rfl
    rw [e₀, hee, hψ]
    exact ⟨fun h => FibreDeriv.isDerivAt0_comp h _,
      fun h => FibreDeriv.isDerivAt0_of_isPullback m.cart.1 (fun z => Over.w (u.ex z)) hol (Over.w v) h⟩
  refine ⟨fun z => φ (u.ex z), fun z => hφ _, ⟨fun z w => by simp only [u.ex_add, map_mul],
    φ.surjective.comp u.ex_onto, by rw [hee]; exact hol, fun w => ?_, fun v hv => ?_⟩,
    fun z => φ.map_eq_one_iff, fun a z w h => Over.OverMorphism.ext ?_, fun k z w c h => ?_⟩
  · obtain ⟨v, hv, huniq⟩ := h₂ w
    refine ⟨ψ v, (key w v).1 hv, fun v' hv' => ?_⟩
    obtain ⟨v', rfl⟩ := ψ.surjective v'
    rw [huniq v' ((key w v').2 hv')]
  · obtain ⟨v, rfl⟩ := ψ.surjective v
    have ht : IsTangent v := by
      rw [IsTangent, ← TangentOrigin.ex_zero_left u]
      refine m.cart.1.hom_ext (by rw [Category.assoc, ← hψ, hv, hφ]) ?_
      refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Over.w v)).trans (Eq.trans ?_ (Over.w (u.ex 0)).symm))
      refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_id _))
      ext a
      simp [TrivSqZeroExt.algebraMap_eq_inl]
    simp only [← key, ht, true_and]
    exact h₁ v ht
  · rw [Over.comp_left, hφ, hφ, h, Over.comp_left, Category.assoc, m.act, Category.assoc]
  · obtain ⟨ω, hω, -⟩ := m.lin
    have H := fun (y' : Sp ℂ ⟶ S) (hy' : y' = (𝟙_ (Over (Sp ℂ))).hom ≫ y) (x₀ y₀ : Over.mk y' ⟶ t₀.G)
        (hx : x₀.left = (u.ex z).left ≫ m.cm.F) (hy : y₀.left = (u.ex w).left ≫ m.cm.F) =>
      show Out.WeilIs t₀.G t₀.PP.L k x₀ y₀ c by
        subst hy'
        exact (weilIs_grpPullback_of_comm' _ _ t₀.G t.G y _ _ _ t₀.PP.isLB t.PP.isLB m.cart ⟨ω, hω⟩ _ k _ _ x₀ y₀ c
          hx hy).1 h
    exact H y (Category.id_comp y).symm _ _ (hφ _) (hφ _)

theorem exists_halfLevel {D : Datum H} (l : Level H) {Q : Type} [Group Q] (ev : D.La → Q)
    (hadd : ∀ a b, ev (a + b) = ev a * ev b) (hker : ∀ b, ev (l.M • b) = 1) :
    ∃ κ : D.La → Q, (∀ a b, κ (a + b) = κ a * κ b) ∧ (∀ a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La), κ a = 1) ∧
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), κ a = ev a := by
  obtain ⟨v, hv, u, hu, huv⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 l.coprime)
  have hM : ∀ a ∈ (l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) • (⊤ : Submodule (𝓞 E) D.La), ev a = 1 := fun a ha => by
    rw [l.prod, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at ha
    obtain ⟨b, -, rfl⟩ := ha
    rw [Nat.cast_smul_eq_nsmul, hker]
  refine ⟨fun a => ev (u • a), fun a b => by simp only [smul_add, hadd], fun a ha => hM _ ?_, fun a ha => ?_⟩
  · rw [mul_comm, Submodule.mul_smul]
    exact Submodule.smul_mem_smul hu ha
  · have h : ev (v • a) = 1 := hM _ (by rw [Submodule.mul_smul]; exact Submodule.smul_mem_smul hv ha)
    conv_rhs => rw [← one_smul (𝓞 E) a, ← huv, add_smul, hadd, h, _root_.one_mul]

end GlobalTheory.PeriodPoint
end
end
