module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle076
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle077
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitTauScaledGeneratorTorusMonomial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle212
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3246
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataBaseChangeSymmetric
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.StalkMapInjectiveOfFlat
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle036
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueThickTorusLevelWeightExpansion
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3242
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3247
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle032
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Definitions.Divisors.P22
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2810
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2620
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3249
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3167
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3250
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.GtPtsVal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section

namespace GlobalTheory.TInj

theorem appTop_spec_inv {R S : CommRingCat} (f : R ⟶ S) (a : R) :
    (Spec.map f).appTop.hom ((Scheme.ΓSpecIso R).inv.hom a) = (Scheme.ΓSpecIso S).inv.hom (f.hom a) := by
  have := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality f)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  exact this.symm

theorem tautologicalChart_baseGenerator_zero_right {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (a : Fin T.r → ℤ)
    (z J) (hJ : Good T.M.L z J) : val (T.τ₀ a 0) (𝟙 _) z J = 1 := by
  have h := T.τ₀_add 0 0 a z J hJ
  have f : cubV T.cub z J (T.c₀ 0) (T.c₀ 0) (T.c₀ a) = 1 := by
    rw [T.c₀_zero]; exact (isCub_cubV T.cub hJ).face _ _
  rw [add_zero, f, _root_.mul_one] at h
  exact (T.τ₀_symm a 0 z J hJ).trans (mul_eq_left.1 h.symm)

theorem base_eq {o W V : Type} [CommRing o] [CommRing W] [IsLocalRing W] [CommRing V] [IsDomain V] {T : TautBase o W}
    {ω : W →+* V} {D : DegPre V} {β : D.P.A.left ⟶ T.B.left} (hpb : IsGrpPullback D.P.A T.B (spMap ω) β)
    {F : Type} [Field F] [Algebra (FractionRing V) F] {x : D.X} {a : Fin T.r → ℤ}
    (hc : (D.c x).left ≫ β = spMap ω ≫ (T.c₀ a).left) (g : GtPtF D F)
    (hg : g.b.left ≫ β = (TF (R := V) F).hom ≫ spMap ω ≫ (T.c₀ a).left) : g.b = DVR.cP D (TF (R := V) F) x := by
  have ht : (toUnit (TF (R := V) F)).left = (TF (R := V) F).hom := by
    simpa using Over.w (toUnit (TF (R := V) F))
  ext1
  apply hpb.1.hom_ext
  · rw [hg, DVR.cP, Over.comp_left, Category.assoc, hc, ← Category.assoc, ht, Category.assoc]
  · rw [Over.w g.b, Over.w (DVR.cP D (TF (R := V) F) x)]

end GlobalTheory.TInj

theorem GlobalTheory.TInj.tautPt_zero_iota : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (ω : W →+* V) (s : I → V) (e : D.X ≃+ (Fin T.r → ℤ)) (β : D.P.A.left ⟶ T.B.left) (ββ : (G2 D.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ T.B T.M.L).pull ββ)), D.TauBimult → From T ω s ε n D e β ββ w → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (g : GtPtF D F), (TautPt T ω s ε n D e β ββ w F 0 g → g.IsZero) ∧ ∀ y : D.X, TautPt T ω s ε n D e β ββ w F ((n : ℤ) • e y) g → GtPtF.IsIota y g := by
  intro o W _ _ _ T I _ ε n V _ _ D ω s e β ββ w hB hF F _ _ g
  have hF' := hF
  obtain ⟨hpb, -, -, hc, hτ⟩ := hF
  refine ⟨fun h => ?_, fun y h => ?_⟩
  · obtain ⟨hb, hv⟩ := h
    have hb' : g.b = 1 := by
      have := GlobalTheory.TInj.base_eq hpb (x := 0) (a := 0) (by rw [hc 0, map_zero, smul_zero]) g hb
      rwa [cPoint_zero] at this
    refine (isZero_iff g).2 ⟨hb', fun χ z J' hJ' => ?_⟩
    choose I₀ hI using fun ψ : (TF (R := V) F).left ⟶ T.B.left => exists_chart T.M.isLB (ψ z)
    have hJ : Good T.M.L z I₀ := hI
    obtain ⟨k, hk, hval⟩ := hv χ
    rw [hval z I₀ J' hJ hJ']
    have k1 : k = 1 := Units.ext (by rw [hk]; simp)
    have l1 := (GlobalTheory.T.mumford_bundle_iso_eq_one_along_axes T ε n V D ω s e β ββ w hB hF' (TF (R := V) F) (DegPre.cF D F χ) z I₀ J' hJ hJ').2
    have t1 : val (T.τ₀ ((n : ℤ) • e χ) 0) ((TF (R := V) F).hom ≫ spMap ω) z I₀ = 1 := by
      apply Units.ext
      have v := GlobalTheory.LevelExpansion.val_comp (T.τ₀ ((n : ℤ) • e χ) 0) ((TF (R := V) F).hom ≫ spMap ω) (𝟙 _) hJ
      rw [Category.comp_id] at v
      have t0 := GlobalTheory.TInj.tautologicalChart_baseGenerator_zero_right T ((n : ℤ) • e χ) _ _ (GlobalTheory.LevelExpansion.good_comp ((TF (R := V) F).hom ≫ spMap ω) hJ)
      rw [v]
      erw [t0]
      rw [Units.val_one, map_one, Units.val_one]
    rw [hb', l1, t1, k1]
    simp [unitOn]
  · obtain ⟨hb, hv⟩ := h
    have hb' : g.b = DVR.cP D (TF (R := V) F) y := GlobalTheory.TInj.base_eq hpb (hc y) g hb
    refine (isIota_iff y g).2 ⟨hb', fun χ z J' hJ' => ?_⟩
    choose I₀ hI using fun ψ : (TF (R := V) F).left ⟶ T.B.left => exists_chart T.M.isLB (ψ z)
    have hJ : Good T.M.L z I₀ := hI
    obtain ⟨k, hk, hval⟩ := hv χ
    obtain ⟨k₀, hk₀, hval₀⟩ := hτ χ y
    have e₀ := hval₀ (jFK (R := V) F z) (fun ψ => I₀ (jFK (R := V) F ≫ ψ)) (fun ψ => J' (jFK (R := V) F ≫ ψ))
      (GlobalTheory.LevelExpansion.good_comp _ hJ) (GlobalTheory.LevelExpansion.good_comp _ hJ')
    rw [hval z I₀ J' hJ hJ', Category.id_comp, GlobalTheory.DegCompare.val_tau_symm _ hJ' y χ]
    have v := GlobalTheory.LevelExpansion.val_comp (D.tau χ y) (jFK (R := V) F) (𝟙 _) hJ'
    rw [Category.comp_id] at v
    have hl : (lift (DegPre.cF D F χ) g.b).left =
        jFK (R := V) F ≫ (lift (toUnit (TK V) ≫ D.c χ) (toUnit (TK V) ≫ D.c y)).left := by
      rw [hb']
      have : lift (DegPre.cF D F χ) (DVR.cP D (TF (R := V) F) y) =
          (Over.homMk (jFK (R := V) F) rfl : TF (R := V) F ⟶ TK V) ≫
            lift (toUnit (TK V) ≫ D.c χ) (toUnit (TK V) ≫ D.c y) := by
        rw [comp_lift, ← Category.assoc, ← Category.assoc, toUnit_unique (_ ≫ toUnit _) (toUnit _)]; rfl
      rw [this, Over.comp_left]; rfl
    have hL := GlobalTheory.HalfBC.lamVal_comp w (jFK (R := V) F)
      (lift (toUnit (TK V) ≫ D.c χ) (toUnit (TK V) ≫ D.c y)).left z I₀ J' hJ hJ'
    have vt : (val (T.τ₀ ((n : ℤ) • e χ) ((n : ℤ) • e y)) ((TF (R := V) F).hom ≫ spMap ω) z I₀).val =
        (Scheme.Hom.stalkMap (jFK (R := V) F) z).hom (val (T.τ₀ ((n : ℤ) • e χ) ((n : ℤ) • e y))
          ((TK V).hom ≫ spMap ω) (jFK (R := V) F z) (fun ψ => I₀ (jFK (R := V) F ≫ ψ))).val := by
      have := GlobalTheory.LevelExpansion.val_comp (T.τ₀ ((n : ℤ) • e χ) ((n : ℤ) • e y)) (jFK (R := V) F) ((TK V).hom ≫ spMap ω) hJ
      rw [← Category.assoc] at this
      exact this
    have hkk : (algebraMap (FractionRing V) F) (k₀ : FractionRing V) = (k : F) := by
      rw [hk, hk₀, map_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [map_zpow₀, map_zsmul, smul_eq_mul]
    have hg : gm (𝟙 (TF (R := V) F).left) z ⊤ (unitOn k) =
        Units.map (Scheme.Hom.stalkMap (jFK (R := V) F) z).hom.toMonoidHom
          (gm (𝟙 (TK V).left) (jFK (R := V) F z) ⊤ (unitOn k₀)) := by
      rw [← GlobalTheory.ConstFam.gm_comp_stalkMap _ _ z ⊤ trivial, Category.comp_id]
      have := gm_comp_top (𝟙 (TF (R := V) F).left) (jFK (R := V) F) z (unitOn k₀) (unitOn k) (by
        simp only [unitOn, Units.coe_map, MonoidHom.coe_coe]
        exact (GlobalTheory.TInj.appTop_spec_inv (CommRingCat.ofHom (algebraMap (FractionRing V) F)) (k₀ : FractionRing V)).trans
          (congrArg _ hkk))
      rw [Category.id_comp] at this
      exact this.symm
    apply Units.ext
    rw [v, e₀]
    simp only [Units.val_mul, map_mul]
    rw [hg, hl, hL, vt]
    rfl
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtRigid

theorem pointRigid_of_hasRigidCoords : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (C : MonoFam Xo c φ R), HasRigidCoords C → PointRigid C := by
  intro E _ _ _ H Dw l Xo c φ R _ _ _ C hC
  obtain ⟨N, s, ε, τ₀, hs, hε, hu, hτ, hPR⟩ := hC
  intro K _ _ ev k₀ hk hemb hsep
  apply hPR K ev k₀ hk hemb
  obtain ⟨h0, B₀, i₁, i₂, M₀, c₀, B', i₃, π₁, π₀, w, c', α, hB, hM, hp₁, hp₀, hw, hc, hrel⟩ := hsep
  refine ⟨fun i => by rw [hs]; exact h0 i, ⟨B₀, i₁, i₂, M₀, c₀, B', i₃, π₁, π₀, w, c', hB, hM, hp₁, hp₀, hw, hc⟩, ?_⟩
  intro W₀ _ ιb hFB hιb j
  let u : Fin N → Rˣ := fun k => (hu k).unit
  have hu' : ∀ k, (u k : R) = s (.inr k) := fun k => (hu k).unit_spec
  let t : Fin C.m ⊕ Fin N → Kˣ := Sum.elim (fun i => (α i)⁻¹) (fun k => Units.map ev.toMonoidHom (u k))
  have key : ∀ a b : C.P.D.toPre.X,
      ((∏ k, t k ^ ((l.M' : ℤ) * (ε k : LinearMap.BilinForm ℤ C.P.D.toPre.X) a b) : Kˣ) : K) ∈ k₀ := by
    intro a b
    have hτ' := GlobalTheory.T.isUnitTau_scaledGenerator_torusMonomial Xo c φ R C N s ε τ₀ hs hε hτ u hu' a b
    obtain ⟨τ₁, hτ₁, hv⟩ := hrel a b _ hτ'
    obtain ⟨x, hx⟩ := GlobalTheory.T.periodGenerators_agree_over_algClosedSubfield R C.P.D.toPre τ₀ K ev k₀ hk W₀ ιb hFB hιb B₀ M₀ c₀ B' π₁ π₀ w c' hB hM hp₁ hp₀ hw hc
      a b τ₁ hτ₁
    let z : Sp K := IsLocalRing.closedPoint K
    choose J hJ using fun χ : Sp K ⟶ C.P.D.toPre.P.A.left => exists_chart C.P.D.toPre.P.isLB (χ z)
    choose J₀ hJ₀ using fun χ : Sp K ⟶ B₀.left => exists_chart hM (χ z)
    have gJ : Good C.P.D.toPre.P.L z J := hJ
    have gJ₀ : Good M₀ z J₀ := hJ₀
    have e₁ := hv z J J₀ gJ gJ₀
    have e₂ := hx z J J₀ gJ gJ₀
    have vs : ∀ (cc : Γ(Sp R, ⊤)ˣ), val (ReciprocityTheory.ChartRestriction.G.DVR.scaleGen cc (τ₀ a b)) (spMap ev) z J =
        gm (spMap ev) z ⊤ cc * val (τ₀ a b) (spMap ev) z J := fun cc =>
      (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ z le_top (gJ.mem _ _) cc) rfl)
    rw [vs, GlobalTheory.UChart.SepBModel.gm_spMap, e₂] at e₁
    set U' := Units.map ev.toMonoidHom (∏ k, u k ^ ((l.M' : ℤ) * (ε (.inr k) : LinearMap.BilinForm ℤ C.P.D.toPre.X) a b))
    set x' := Units.map k₀.subtype.toMonoidHom x
    set A := ∏ i, α i ^ (((l.M' : ℤ) • C.δ i) a b)
    set L := lamUnit w c' a b z J J₀
    set V := val τ₁ (spMap k₀.subtype) z J₀
    have e₃ : gm (𝟙 (Sp K)) z ⊤ (unitOn U') * gm (𝟙 (Sp K)) z ⊤ (unitOn x') = gm (𝟙 (Sp K)) z ⊤ (unitOn A) := by
      have h₁ : gm (𝟙 (Sp K)) z ⊤ (unitOn U') * (L * gm (𝟙 (Sp K)) z ⊤ (unitOn x') * V) =
          (L * V) * (gm (𝟙 (Sp K)) z ⊤ (unitOn U') * gm (𝟙 (Sp K)) z ⊤ (unitOn x')) := by ac_rfl
      have h₂ : L * gm (𝟙 (Sp K)) z ⊤ (unitOn A) * V = (L * V) * gm (𝟙 (Sp K)) z ⊤ (unitOn A) := by ac_rfl
      rw [h₁, h₂] at e₁
      exact mul_left_cancel e₁
    have e₄ : U' * x' = A := GlobalTheory.UChart.SepBModel.gm_unitOn_inj z (by
      rw [show unitOn (U' * x') = unitOn U' * unitOn x' from map_mul _ _ _, map_mul]; exact e₃)
    have e₅ : (∏ k, t k ^ ((l.M' : ℤ) * (ε k : LinearMap.BilinForm ℤ C.P.D.toPre.X) a b)) = x'⁻¹ := by
      rw [Fintype.prod_sum_type]
      have hA : (∏ i, t (.inl i) ^ ((l.M' : ℤ) * (ε (.inl i) : LinearMap.BilinForm ℤ C.P.D.toPre.X) a b)) = A⁻¹ := by
        simp only [t, Sum.elim_inl, hε, A, inv_zpow, Finset.prod_inv_distrib, LinearMap.smul_apply, smul_eq_mul]
      have hU : (∏ k, t (.inr k) ^ ((l.M' : ℤ) * (ε (.inr k) : LinearMap.BilinForm ℤ C.P.D.toPre.X) a b)) = U' := by
        simp only [t, Sum.elim_inr, U', map_prod, map_zpow]
      rw [hA, hU, ← e₄, mul_inv_rev, inv_mul_cancel_right]
    rw [e₅]
    exact (x⁻¹ : k₀ˣ).val.2
  have := GlobalTheory.T.mem_subfield_of_bilinForm_basis_monomials C.P.D.toPre.X (balForms H.bar C.P.D.toPre.X) (Fin C.m ⊕ Fin N) ε K k₀ hk (l.M')
    (by exact_mod_cast (level_pos l).ne') t key (.inr j)
  simpa [t, u] using this

end GlobalTheory.PtRigid
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.canonicalChart_residueField_dimension : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ {k : Type} [Field k] {m e : ℕ} (C : MonoFam Xo c φ (ChartRing k m e)), Canon C → ((residue (ChartRing k m e)).comp C.b).EssFiniteType ∧ (letI := ((residue (ChartRing k m e)).comp C.b).toAlgebra; ((m + e : ℕ) : Cardinal) + Algebra.trdeg c.F (ResidueField (ChartRing k m e)) = Dw.dim) := by
  first | exact @GlobalTheory.UCanon.canon_residue_dim | exact GlobalTheory.UCanon.canon_residue_dim | (intros; apply GlobalTheory.UCanon.canon_residue_dim <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.canonicalFamily_periods_in_coordinates : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C), ∃ (ε' : Module.Basis (Fin C.m ⊕ Fin Cn.N) ℤ (balForms H.bar C.P.D.toPre.X)) (τ₀ : Gens C.P.D.toPre), (∀ k, (ε' k : LinearMap.BilinForm ℤ C.P.D.toPre.X) = pull Cn.e.toLinearMap (Cn.ε k : LinearMap.BilinForm ℤ Cn.L.D.X)) ∧ FromBase C.P.D.toPre τ₀ (Cn.ψ.comp MvPolynomial.C) ∧ TauIn C.P.D.toPre τ₀ (fun k => Cn.ψ (MvPolynomial.X (finSumFinEquiv.symm k))) (fun k => (l.M' : ℤ) • (ε' (finSumFinEquiv.symm k) : LinearMap.BilinForm ℤ C.P.D.toPre.X)) := by
  first | exact @GlobalTheory.UCanon.PerCoord.main | exact GlobalTheory.UCanon.PerCoord.main | (intros; apply GlobalTheory.UCanon.PerCoord.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.psiUnitOn_basicOpen_of_comesFromBase : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) [Module (𝓞 E) Q.X] (oQ : letI := H.starRing; Q.OAct (𝓞 E)) (iw : L.W →+* V) {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : Q.X ≃ₗ[𝓞 E] L.D.X), DivFrom L Q oQ iw s ε e → ∀ f : V, (∀ k, ∃ n : ℕ, s k ∣ f ^ n) → ∀ y, PsiUnitOn Q y (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum V)) := by
  first | exact @GlobalTheory.UnitOpen.psiUnitOn_basicOpen_of_divFrom | exact GlobalTheory.UnitOpen.psiUnitOn_basicOpen_of_divFrom | (intros; apply GlobalTheory.UnitOpen.psiUnitOn_basicOpen_of_divFrom <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

theorem _root_.GlobalTheory.T.arithHeight_projectionFormula_every_point : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D E : ℕ), IsArithVar p D → IsArithVar q E → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (L : HermLB p) (h : X → ℝ) (h' : Y → ℝ), L.IsArithHeight h → (L.pull π hπ).IsArithHeight h' → ∀ y : Y, h' y = (π.residueDegree y : ℝ) * h (π y) := by
  first | exact @GlobalTheory.MixHt.heightProj | exact GlobalTheory.MixHt.heightProj | (intros; apply GlobalTheory.MixHt.heightProj <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_uniformisedModel_labels_unitaryTrait : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (u' : Sp (ratHull S.R) ⟶ Xo.XF cf) (G : Over (Sp (ratHull S.R))) (_ : GrpObj G) (α : G.left ⟶ ρ.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left), IsGrpPullback G ρ.P.A (spMap (toRat S.R)) α → IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β → LBIso (ρ.P.L.pull α) (Xo.univ.t.PP.L.pull β) → ∀ (p : ℕ) [Fact p.Prime] (y₁ : ratHull S.R →+* PadicAlgCl p) (T : UTrait Xo cf) (ι : FractionRing T.V →+* PadicAlgCl p), (∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T.V (FractionRing T.V))) → spMap y₁ ≫ u' = spMap ι ≫ T.y → (∀ a : o, ‖y₁ (toRat S.R (algebraMap o S.R a))‖ ≤ 1) → ∃ (u : ρ.UTest p (y₁.comp (toRat S.R))) (lb : u.Lab) (j : u.D.toPre.X ≃+ T.P.D.toPre.X), (∀ χ, lb.q χ = -Real.log ‖ι (algebraMap T.V (FractionRing T.V) T.ϖ)‖ * (T.be (j χ) (j χ) : ℝ) / 2) ∧ ∀ (m : ℕ) (a : 𝓞 E) (pk pk' : QkPt u.D.toPre (PadicAlgCl p) m) (x x' : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) (w w' : Sp (PadicAlgCl p) ⟶ G.left), 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk' x' → w ≫ α = x.left ≫ u.φ → w' ≫ α = x'.left ≫ u.φ → w' ≫ β = w ≫ β ≫ (Xo.univ.t.act.act a).left → CongMod m (j pk'.y) (a • j pk.y) := by
  first | exact @GlobalTheory.UPoinc.uTraitLabels | exact GlobalTheory.UPoinc.uTraitLabels | (intros; apply GlobalTheory.UPoinc.uTraitLabels <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.PolDeg

theorem hasChart_of_hasPolChart {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) {S : Scheme.{0}} (s : S ⟶ Sp o)
    (j : F.X ⟶ S) [IsOpenImmersion j] {G : Over S} [GrpObj G] (e : F.univ.A.left ⟶ G.left) (φ : InvFun ℤ)
    (BD : GlobalTheory.EffCartierData S) (d : ℕ) (x : S) (hn : n ≠ 0) (h : HasPolChart F s j e φ BD d x) :
    HasChart F s j e φ BD d x := by
  obtain ⟨R, _, _, _, b, ξ, m, t, Q, δ, a, ⟨hc, hz, hs, hx, he, hu⟩, ⟨ht, hI, hj⟩,
    ⟨hM, hX, hδ, hdef, hmon⟩, ha, hBD⟩ := h
  have hCN : IsCN R := ⟨inferInstance, (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing R).2, hc, hz⟩
  have ht0 : ∀ i, t i ≠ 0 := by
    intro i h0
    have := ht.2 (Pi.single i 1) (by
      rw [Finset.sum_eq_single i (fun k _ hk => by simp [Pi.single_apply, hk]) (by simp)]
      simp [h0]) i
    simp at this
  have hsym : ∀ i y z, ((n : ℤ) • δ i) y z = ((n : ℤ) • δ i) z y := fun i y z => by
    simp only [LinearMap.smul_apply, (mem_balForms_int.1 (hδ.mem i)) y z]
  have hnn : ∀ i y, 0 ≤ ((n : ℤ) • δ i) y y := fun i y => by
    simp only [LinearMap.smul_apply, smul_eq_mul]; exact mul_nonneg (by positivity) (hδ.nonneg i y)
  have hpos : ∀ y, y ≠ 0 → ∃ i, 0 < ((n : ℤ) • δ i) y y := fun y hy => by
    obtain ⟨i, hi⟩ := hdef y hy
    exact ⟨i, by simp only [LinearMap.smul_apply, smul_eq_mul]; exact mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) hi⟩
  obtain ⟨R', _, _, _, ρ, r, D, ε, hCN', hinj, hfin, hloc, hr, href, hmon'⟩ :=
    GlobalTheory.T.refine_polarised_monomial_periods_monomial_data R Q m t (fun i => (n : ℤ) • δ i) hCN hmon ht.1 ht0 hsym hnn hpos
  obtain ⟨G', _, _, π, A, U, hU⟩ := hM.unif R' ρ hCN' hinj hfin D ε href
  let ϑ : Fin m → LinearMap.BilinForm ℤ D.toPre.X := fun i => pull ε.toIntLinearEquiv.toLinearMap (δ i)
  have hϑ : ∀ (k : ℤ) i, pull ε.toIntLinearEquiv.toLinearMap (k • δ i) = k • ϑ i := fun k i =>
    LinearMap.ext₂ fun y z => by simp [ϑ]
  refine ⟨R, inferInstance, inferInstance, b, ξ, m, t, R', inferInstance, inferInstance, inferInstance, ρ, r, G', inferInstance,
    inferInstance, π, D, A, U, ϑ, a, ⟨hc, hs, hx, he, hu⟩, ⟨ht, hI, hj⟩,
    ⟨⟨hCN'.1, inferInstance, hCN'.2.1, hCN'.2.2.1⟩, hCN'.2.2.2, hinj, hfin, hloc, hr⟩,
    ⟨hU, ?_, hδ.pull_equiv ε.toIntLinearEquiv, ?_⟩, fun i => ?_, hBD⟩
  · rw [LinearEquiv.finrank_eq ε.toIntLinearEquiv]; exact hX
  · convert hmon' using 2 with i
    rw [hϑ, ← mul_smul]
  · rw [ha i, ← hϑ, evalZ_pull φ ε.toIntLinearEquiv.surjective]

end GlobalTheory.PolDeg
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.FlagTan

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (φ : A →+* B) (ψ : B →+* C) :
    spMap ψ ≫ spMap φ = spMap (ψ.comp φ) := by
  unfold spMap
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem isTanX_dir {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {K : Type} [Field K] [Algebra c.F K]
    {ι : Type} [Fintype ι] (y : FrPt Xo c K) (X : Sp (TrivSqZeroExt K (ι → K)) ⟶ Xo.X)
    (h1 : X ≫ Xo.s = sOf c _) (h2 : spMap (TrivSqZeroExt.fstHom c.F K (ι → K)).toRingHom ≫ X = y.x)
    (M : ι → K) : GlobalTheory.FlagTan.IsTanX y (spMap (GlobalTheory.FlagTan.dir c M).toRingHom ≫ X) := by
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, h1]
    unfold sOf
    have e : (GlobalTheory.FlagTan.dir c M).toRingHom.comp (algebraMap c.F (TrivSqZeroExt K (ι → K))) =
        algebraMap c.F (DualNumber K) := (GlobalTheory.FlagTan.dir c M).comp_algebraMap
    rw [spMap_comp_spMap, ← RingHom.comp_assoc, e]
  · rw [← Category.assoc, spMap_comp_spMap, ← h2]
    congr 2
    ext z <;> simp

theorem ksIso_psiSet : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y := by
  intro hP hG E _ _ _ H Dw l Xo c K _ _ y hpq
  obtain ⟨X, h1, h2, hks⟩ := GlobalTheory.T.universal_first_order_deformation hP hG E H Dw l Xo c K y hpq
  refine ⟨X, h1, h2, fun x' hx => ?_⟩
  have key : ∀ M, IsKS (psiSet H) y x' M ↔ x' = spMap (dir c M).toRingHom ≫ X := fun M =>
    ⟨fun k => GlobalTheory.T.kodaira_spencer_tangent_difference hP hG E H Dw l Xo c K y _ _ M hpq hx (isTanX_dir y X h1 h2 M) k (hks M),
      fun e => e ▸ hks M⟩
  obtain ⟨M, hM⟩ := GlobalTheory.T.kodaira_spencer_matrix_exists hP E H Dw l Xo c K y x' hpq hx
  exact ⟨⟨M, (key M).1 hM, fun M' e => GlobalTheory.T.kodaira_spencer_matrix_unique hP E H Dw l Xo c K y x' hpq hx M' M ((key M').2 e) hM⟩, key⟩

end GlobalTheory.FlagTan
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_uniformisedGroup_point_sameDerivations : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n : ℕ) (vH : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (vH a) (dd a)) → ∀ (v' : Fin n → TanM (𝟙 (Sp R)) t.G), (∀ a, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv (vH a))) (tv (v' a))) → ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x : Sp Ω ⟶ Y.H.left) (δ : Fin n → Derivation ℤ Ω Ω), IsAdicComplete ((maximalIdeal R).map φ) Ω → Function.Injective φ → ∀ (hx : x ≫ Y.H.hom = spMap φ), (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x ⁻¹ᵁ O → valR x O (dd a O f) = δ a (valR x O f)) → ∃ (x' : Sp Ω ⟶ t.G.left) (hx' : x' ≫ t.G.hom = spMap φ) (dd' : Fin n → Fld t.G.left), (∀ a, IsInv t.G (v' a) (dd' a)) ∧ (∀ a O f, ⊤ ≤ x' ⁻¹ᵁ O → valR x' O (dd' a O f) = δ a (valR x' O f)) ∧ (∀ O (f : Γ(t.G.left, O)), ⊤ ≤ x' ⁻¹ᵁ O → valR x' O f = 0 → f = 0) ∧ GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ (Over.mk (spMap φ)) (Over.homMk x hx)) (Over.homMk x' hx') := by
  exact @GlobalTheory.FormalPointG.exists_point_sameDerivations
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.verticalSecondOrderSymbol_vanishes_of_polarisation : ∀ (K : Type) [Field K] [CharZero K] (P₀ : Out.PolAV (Sp K)) (n : ℕ) (v : Module.Basis (Fin n) K (TanM (𝟙 (Sp K)) P₀.A)) (dd : Fin n → Fld P₀.A.left), (∀ a, IsInv P₀.A (v a) (dd a)) → ∀ (F : Type) [Field F] (ψ : K →+* F) (ξ : Sp F ⟶ P₀.A.left), ξ ≫ P₀.A.hom = spMap ψ → (∀ O (f : Γ(P₀.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0) → ∀ (δ : Fin n → Derivation ℤ F F), (∀ a O f, ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O (dd a O f) = δ a (valR ξ O f)) → ∀ (j₀ : P₀.L.ι), ⊤ ≤ ξ ⁻¹ᵁ P₀.L.U j₀ → ∀ (δ₀ : Derivation ℤ F F) (Λ : Matrix (Fin n) (Fin n) F), Λᵀ = Λ → (∀ r, δ₀ (ψ r) = 0) → (∀ (k : ℕ), 1 ≤ k → ∀ σ τ : SecM (𝟙 P₀.A.left) P₀.L k, ∃ ρ : SecM (𝟙 P₀.A.left) P₀.L (3 * k), ∀ b c : F, b = valR ξ _ (σ.f fun _ => j₀) → c = valR ξ _ (τ.f fun _ => j₀) → (k : F) * b * (b * δ₀ c - c * δ₀ b) - ∑ a, ∑ e, Λ a e * δ a b * (b * δ e c - c * δ e b) = valR ξ _ (ρ.f fun _ => j₀)) → Λ = 0 := by
  first | exact @GlobalTheory.Heat.gc_symbol_vanishes | exact GlobalTheory.Heat.gc_symbol_vanishes | (intros; apply GlobalTheory.Heat.gc_symbol_vanishes <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep

theorem _root_.GlobalTheory.T.exists_finite_cover_linked_thetaSystems : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ n : ℕ, n.Prime → Odd n → ∀ j₀ : ℕ, ∃ (j : ℕ) (Y : Scheme.{0}) (q : Y ⟶ Xo.XF c), j₀ ≤ j ∧ IsFinite q ∧ Surjective q ∧ ∀ (K : Type) [Field K] (y' : Sp K ⟶ Y), ∃ (X₁ : GlobalTheory.GSep.GSet) (act : 𝓞 E → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (u : Sp (ratHull X₁.S.R) ⟶ Xo.XF c) (π : X₁.M.Z ⟶ C.Z) (yM : Sp K ⟶ X₁.M.Z), GlobalTheory.GSep.ULink C X₁ act u π ∧ X₁.S.r * X₁.S.N = (n ^ j) ^ 2 ∧ (∃ (U : C.Z.Opens) (g' : X₁.M.Z ⟶ U.toScheme), IsFinite g' ∧ g' ≫ U.ι = π ∧ Set.range (pullback.fst C.z (spMap C.b)) ⊆ (U : Set C.Z)) ∧ yM ≫ π = y' ≫ q ≫ C.i ∧ ∀ a ∈ X₁.S.R, a ∈ X₁.M.O (yM (closedPoint K)) := by
  first | exact @GlobalTheory.UCovSep.exists_linked_cov | exact GlobalTheory.UCovSep.exists_linked_cov | (intros; apply GlobalTheory.UCovSep.exists_linked_cov <;> assumption)
end
