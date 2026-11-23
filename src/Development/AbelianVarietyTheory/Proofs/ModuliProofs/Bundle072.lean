module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle048
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle015
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle035
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HolDifferentiableAt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0OfIsPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Henselian
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLaw
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.Bundle002
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.SymplecticBasisLevel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsDerivAt0NotIsDerivAlong
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.LieEigenbasis

theorem existsUnique_sum_single {k : Type} [Field k] {n N : ℕ} (s : Fin N → Fin n)
    (hs : Function.Injective s) (c : Fin n → k) (hc : ∀ i, i ∉ Set.range s → c i = 0) :
    ∃! d : Fin N → k, c = ∑ j, d j • (Pi.single (s j) 1 : Fin n → k) := by
  have h : ∀ (d : Fin N → k) (j : Fin N),
      (∑ j, d j • (Pi.single (s j) 1 : Fin n → k)) (s j) = d j := fun d j => by
    simp [Finset.sum_apply, Pi.single_apply, hs.eq_iff]
  refine ⟨fun j => c (s j), funext fun i => ?_, fun d hd => funext fun j => by rw [hd, h]⟩
  by_cases hi : i ∈ Set.range s
  · obtain ⟨j, rfl⟩ := hi
    rw [h]
  · rw [hc i hi, Finset.sum_apply]
    refine (Finset.sum_eq_zero fun j _ => ?_).symm
    have : i ≠ s j := fun e => hi ⟨j, e.symm⟩
    simp [this]

end GlobalTheory.LieEigenbasis


open ReciprocityTheory.ChartRestriction.G.Chart (prodPts scaleD tvec tmap) in
theorem GlobalTheory.lieMult_of_eigenbasis : ∀ (k : Type) [Field k] (O : Type) [CommRing O] (G : Over (Sp k)) [GrpObj G] (act : OAct O G) (n : ℕ) (v : Fin n → (epsR k ⟶ G)) (τs : Fin n → (O →+* k)), Smooth G.hom → IsLieBasis v → (∀ i a, (v i ≫ act.act a).left = spMap (epsScale (τs i a)) ≫ (v i).left) → ∀ τ : O →+* k, LieMult act (𝟙 (Sp k)) τ (Nat.card {i // τs i = τ}) := by
  intro k _ O _ G _ act n v τs _ hv hτ τ
  have := act.hom
  obtain ⟨x, hx, hxv⟩ := Chart.chart_of_basis hv
  have hxv' : ∀ j, v j = tvec (x := x) (Pi.single j 1) := hxv
  have hdiag : ∀ a i, tmap hx (act.act a) (Pi.single i 1) = τs i a • (Pi.single i 1 : Fin n → k) :=
    fun a i => (Chart.tvec_eig_iff hx _ _ _).1 (by
      rw [← hxv']; exact Over.OverMorphism.ext (hτ i a))
  have hmap : ∀ a c i, tmap hx (act.act a) c i = τs i a * c i := fun a c i => by
    conv_lhs => rw [← Finset.univ_sum_single c]
    have : ∀ j, (Pi.single j (c j) : Fin n → k) = c j • (Pi.single j 1 : Fin n → k) := fun j => by
      rw [← Pi.single_smul, smul_eq_mul, _root_.mul_one]

    simp only [this, map_sum, map_smul, hdiag]
    simp [Finset.sum_apply, Pi.single_apply, mul_comm]
  let N := Nat.card {i // τs i = τ}
  let q : Fin N ≃ {i // τs i = τ} := (Finite.equivFin _).symm
  let s : Fin N → Fin n := fun j => (q j).1
  have hs : Function.Injective s := Subtype.val_injective.comp q.injective
  have hpr : ∀ d : Fin N → k, prodPts d (fun j => v (s j)) =
      tvec (x := x) (∑ j, d j • (Pi.single (s j) 1 : Fin n → k)) := fun d => by
    have ht : ∀ j, Chart.IsTan (v (s j)) := fun j => (Chart.isTan_iff _).2 (hv.1 _)
    obtain ⟨h, e⟩ := Chart.prodPts_tan hx d (fun j => v (s j)) ht
    refine (Chart.tcoord_spec hx _ h).trans ?_
    change tvec (x := x) _ = _
    rw [e]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by rw [Chart.tcoord_eq hx _ (ht j) _ (hxv _)]
  let j : epsPt (𝟙 (Sp k)) ≅ epsR k := Over.isoMk (Iso.refl _) (by simp)
  let e : (epsPt (𝟙 (Sp k)) ⟶ G) ≃* (epsR k ⟶ G) :=
    MulEquiv.ofBijective (preHom j.inv) (j.symm.homCongr (Iso.refl G)).symm.bijective
  have he : ∀ w, (e w).left = w.left := fun w => Category.id_comp _
  have he' : ∀ w, (e.symm w).left = w.left := fun w => by rw [← he, e.apply_symm_apply]
  have one : (1 : Over.mk (𝟙 (Sp k)) ⟶ G).left = η[G].left := Category.id_comp _
  refine LiePull.basis_transport e.symm (Q := IsLieEigen act (𝟙 _) τ)
    (R' := fun c u v => u.left = spMap (epsScale c) ≫ v.left)
    (R := fun c u v => u.left = spMap (epsScaleR c) ≫ v.left)
    (P := fun w => IsTangent w ∧ ∀ a, w ≫ act.act a = Chart.spMap (scaleD (τ a)) ≫ w)
    (fun w => and_congr (by rw [IsTangent, he', one]) (forall_congr' fun a => by
      rw [Over.OverMorphism.ext_iff, Over.comp_left, Over.comp_left, Over.comp_left, he']
      rfl))
    (fun c u v => by rw [he', he']; rfl) N ⟨fun j => v (s j), fun j => ⟨hv.1 _, fun a => ?_⟩, ?_⟩
  · have := hτ (s j) a
    rw [(q j).2] at this
    exact Over.OverMorphism.ext this
  · rintro w ⟨hw, hw'⟩
    have ht := (Chart.isTan_iff _).2 hw
    obtain ⟨c, rfl⟩ : ∃ c, w = tvec (x := x) c := ⟨_, Chart.tcoord_spec hx w ht⟩
    refine (existsUnique_congr fun d => ?_).1
      (LieEigenbasis.existsUnique_sum_single s hs c fun i hi => ?_)
    · refine Iff.trans ?_ (Chart.isLieComb_iff d _ _).symm
      rw [hpr]
      exact ⟨fun h => by rw [← h], Chart.tvec_inj hx⟩
    · by_contra hc
      refine hi ⟨q.symm ⟨i, RingHom.ext fun a => ?_⟩, by simp [s]⟩
      have := congrFun ((Chart.tvec_eig_iff hx _ _ _).1 (hw' a)) i
      rw [hmap] at this
      exact mul_right_cancel₀ hc this
end

section

noncomputable section

namespace GlobalTheory.UnifCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding IsTypeFn IsThetaFrame
open GlobalTheory.IndefiniteRowSideFullHecke.PeriodMapPresentation hiding IsTypeFn IsThetaFrame
open GlobalTheory.IndefiniteRowSideFullHecke.SymplecticBasisLevel GlobalTheory.PeriodCompare
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section Lattice

theorem isPeriod_move {D' : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P₀ P₁ P : D'.La →+ (Fin g → ℂ)}
    (h₀ : IsPeriod D' ty P₀) (h₁ : IsPeriod D' ty P₁) (hP : IsPeriod D' ty P) (gam : D'.La ≃ₗ[𝓞 E] D'.La)
    (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (hgam : ∀ a b, D'.EF (gam a) (gam b) = D'.EF a b)
    (hh : ∀ a, P₁ (gam a) = h (P₀ a)) :
    IsPeriod D' ty (h.toLinearMap.toAddMonoidHom.comp (P.comp gam.symm.toLinearMap.toAddMonoidHom)) := by
  have tr : ∀ {Q : D'.La →+ (Fin g → ℂ)}, IsPeriod D' ty Q →
      IsPeriod D' ty (Q.comp gam.symm.toLinearMap.toAddMonoidHom) := by
    rintro Q ⟨h1, h2, h3, h4, Hm, h5, h6, h7⟩
    have hr : (Q.comp gam.symm.toLinearMap.toAddMonoidHom).range = Q.range :=
      SetLike.ext' (gam.symm.surjective.range_comp Q)
    refine ⟨fun a x i => ?_, h2.comp gam.symm.injective, by rw [hr]; exact h3, ?_, Hm, h5, h6, fun x y => ?_⟩
    · simpa using h1 a (gam.symm x) i
    · rw [← h4, ← AddMonoidHom.coe_range, hr, AddMonoidHom.coe_range]
    · change (hermForm Hm (Q (gam.symm x)) (Q (gam.symm y))).im = _
      rw [h7, ← hgam, gam.apply_symm_apply, gam.apply_symm_apply]
  let A := LinearMap.toMatrix' h.toLinearMap
  have hA : A.mulVecLin = h.toLinearMap := by
    rw [← Matrix.toLin'_apply', Matrix.toLin'_toMatrix']
  have hdet : A.det ≠ 0 := by
    rw [LinearMap.det_toMatrix']
    exact h.isUnit_det'.ne_zero
  rw [← hA]
  refine PeriodConn.isPeriod_mulVec (tr hP) hdet (PeriodConn.entry_eq_zero (tr h₀) h₁ fun x => ?_)
  rw [← Matrix.mulVecLin_apply, hA]
  exact (congrArg P₁ (gam.apply_symm_apply x)).symm.trans (hh _)

variable {g : ℕ}

variable {D' : Datum H} {ty : Fin g → (E →+* ℂ)}

end Lattice

section Deriv

variable {X S : Scheme.{0}} {g : ℕ}

theorem isDerivAt0_smul {F : (Fin g → ℂ) → (Sp ℂ ⟶ X)} {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ X}
    (hv : IsDerivAt0 F w v) (c : ℂ) : IsDerivAt0 F (c • w) (spMap (epsScale c) ≫ v) := by
  have h0 : spMap TangentOrigin.fstC ≫ spMap (epsScale c) ≫ v = spMap TangentOrigin.fstC ≫ v := by
    rw [← Category.assoc, TanMod.spMap_comp']
    congr 2
    exact RingHom.ext fun x => by simp [epsScale]
  refine ⟨h0.trans hv.1, fun U h f => ?_⟩
  have h' : ⊤ ≤ v ⁻¹ᵁ U := by
    rw [TangentOrigin.top_le_preimage_iff] at h ⊢
    exact h0 ▸ h
  refine (congrArg TrivSqZeroExt.snd (TangentOrigin.evalPt_spMap_comp (epsScale c) v U h' h f)).trans ?_
  rw [map_smul, ← hv.2 U h' f]
  exact TrivSqZeroExt.snd_map _ _

theorem isDerivAt0_mul {G : Over S} [GrpObj G] {y : Sp ℂ ⟶ S} {F : (Fin g → ℂ) → (Sp ℂ ⟶ G.left)}
    (h0 : F 0 = (1 : Over.mk y ⟶ G).left) {w w' : Fin g → ℂ} {v v' : epsPt y ⟶ G}
    (hv : IsDerivAt0 F w v.left) (hv' : IsDerivAt0 F w' v'.left) : IsDerivAt0 F (w + w') (v * v').left := by
  have t := TanMod.smT_zero_of y v (hv.1.trans h0)
  have t' := TanMod.smT_zero_of y v' (hv'.1.trans h0)
  have t'' : spMap TangentOrigin.fstC ≫ (v * v').left = F 0 :=
    (TanMod.unit_of_smT_zero y (v * v') (by rw [TanMod.smT_mul, t, t', _root_.mul_one])).trans h0.symm
  refine ⟨t'', fun U h f => ?_⟩
  have hF : ⊤ ≤ F 0 ⁻¹ᵁ U := t'' ▸ (TangentOrigin.top_le_preimage_iff _ U).1 h
  have h1 := (TangentOrigin.top_le_preimage_iff v.left U).2 (hv.1.symm ▸ hF)
  have h2 := (TangentOrigin.top_le_preimage_iff v'.left U).2 (hv'.1.symm ▸ hF)
  rw [map_add (f := _), ← hv.2 U h1 f, ← hv'.2 U h2 f]
  exact TanDeriv.snd_evAt_mul v v' t t' U h1 h2 h f

end Deriv

section Piece

variable {D : Datum H} {l : Level H} (Xo : Moduli D l) {g : ℕ} (ty : Fin g → (E →+* ℂ))
  (D' : Datum H) (u : (D'.La →+ (Fin g → ℂ)) → (Sp ℂ ⟶ Xo.X))
  (ex : ∀ P : D'.La →+ (Fin g → ℂ), (Fin g → ℂ) → (Over.mk (u P) ⟶ univG Xo))

variable {Xo ty D' u ex}

end Piece

section Main

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}

end Main

end GlobalTheory.UnifCompare
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.VerticalDeriv

open GlobalTheory.FibreDeriv

variable {g : ℕ} {X Z : Scheme.{0}}

theorem isDerivAt0_unique {e : (Fin g → ℂ) → (Sp ℂ ⟶ Z)} {w : Fin g → ℂ} {v v' : Sp (DualNumber ℂ) ⟶ Z}
    (H : IsDerivAt0 e w v) (H' : IsDerivAt0 e w v') : v = v' := by
  rw [isDerivAt0_iff] at H H'
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := Z) (U := ⊤)
    (x := e 0 (default : PrimeSpectrum ℂ)) trivial
  have h0 : ⊤ ≤ e 0 ⁻¹ᵁ U := (top_le_preimage_iff_mem _ U).2 hxU
  have h := (top_le_preimage_eps v _ H.1 U).2 h0
  have h' := (top_le_preimage_eps v' _ H'.1 U).2 h0
  exact TangentOrigin.ext_evalPt hU h h' (RingHom.ext fun f => (H.2 U h f).trans (H'.2 U h' f).symm)

theorem exists_isDerivAt0 {e : (Fin g → ℂ) → (Sp ℂ ⟶ Z)} (hol : IsHolTo Set.univ e) (w : Fin g → ℂ) :
    ∃ v : Sp (DualNumber ℂ) ⟶ Z, IsDerivAt0 e w v := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := Z) (U := ⊤)
    (x := e 0 (default : PrimeSpectrum ℂ)) trivial
  have h0 : ⊤ ≤ e 0 ⁻¹ᵁ U := (top_le_preimage_iff_mem _ U).2 hxU
  have hd := LocalLift.hol_differentiableAt hol (Set.mem_univ _) h0
  let J : Γ(Z, U) →+* DualNumber ℂ :=
    { toFun := fun f => jet w (fun z => valAt' (e z) U f)
      map_one' := by
        have : (fun z => valAt' (e z) U 1) =ᶠ[nhds 0] fun _ => 1 := by
          filter_upwards [LocalLift.hol_eventually_mem hol (Set.mem_univ _) h0] with z hz
          exact valAt'_one _ hz.2
        rw [jet_congr w this, jet_const, map_one]
      map_zero' := by
        simp only [valAt'_zero]
        rw [jet_const, map_zero]
      map_add' := fun f f' => by
        simp only [valAt'_add]
        exact jet_add w (hd f) (hd f')
      map_mul' := fun f f' => by
        simp only [valAt'_mul]
        exact jet_mul w (hd f) (hd f') }
  obtain ⟨v, hv, hve⟩ := TangentOrigin.exists_evalPt_eq hU J
  refine ⟨v, isDerivAt0_of_affine ?_ hU hv fun a => ⟨hd a, DFunLike.congr_fun hve a⟩⟩
  refine TangentOrigin.ext_evalPt hU ((TangentOrigin.top_le_preimage_iff v U).1 hv) h0 (RingHom.ext fun f => ?_)
  refine (TangentOrigin.evalPt_spMap_comp TangentOrigin.fstC v U hv _ f).trans ?_
  rw [hve, ← TangentOrigin.valAt'_eq_evalPt]
  exact fst_jet w (fun z => valAt' (e z) U f)

theorem isDerivAt0_vertical (p : Z ⟶ X) (x : Sp ℂ ⟶ X) {e : (Fin g → ℂ) → (Sp ℂ ⟶ Z)} (he : ∀ z, e z ≫ p = x)
    {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ Z} (H : IsDerivAt0 e w v) :
    v ≫ p = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ x := by
  have h1 := isDerivAt0_comp H p
  simp only [he] at h1
  exact isDerivAt0_unique h1 (LocalLift.isDerivAt0_const (fun _ => x) w fun U f _ => by simp)

theorem isDerivAt0_snd {e : (Fin g → ℂ) → (Sp ℂ ⟶ Z)} (hol : IsHolTo Set.univ e) {U : Z.Opens} {n : ℕ}
    (t : Fin n → Γ(Z, U)) (h0 : ⊤ ≤ e 0 ⁻¹ᵁ U) {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ Z}
    (H : IsDerivAt0 e w v) (h : ⊤ ≤ v ⁻¹ᵁ U) (i : Fin n) :
    (TangentOrigin.evalPt v U h (t i)).snd = fderiv ℂ (fun z i => valAt' (e z) U (t i)) 0 w i := by
  rw [fderiv_pi fun i => LocalLift.hol_differentiableAt hol (Set.mem_univ _) h0 (t i)]
  exact H.2 U h (t i)

theorem bijective_iff_injective (p : Z ⟶ X) (x : Sp ℂ ⟶ X) {e : (Fin g → ℂ) → (Sp ℂ ⟶ Z)} (he : ∀ z, e z ≫ p = x)
    (hol : IsHolTo Set.univ e) (U : Z.Opens) (t : Fin g → Γ(Z, U)) (h0 : ⊤ ≤ e 0 ⁻¹ᵁ U)
    (hun : ∀ (v v' : Sp (DualNumber ℂ) ⟶ Z) (h : ⊤ ≤ v ⁻¹ᵁ U) (h' : ⊤ ≤ v' ⁻¹ᵁ U), v ≫ p = v' ≫ p →
      spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v' →
      (∀ i, TangentOrigin.evalPt v U h (t i) = TangentOrigin.evalPt v' U h' (t i)) → v = v') :
    (∀ v : Sp (DualNumber ℂ) ⟶ Z, v ≫ p = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ x →
      spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = e 0 → ∃! w, IsDerivAt0 e w v) ↔
      Function.Injective (fderiv ℂ (fun z i => valAt' (e z) U (t i)) 0) := by
  set T := fderiv ℂ (fun z i => valAt' (e z) U (t i)) 0 with hT
  have key : ∀ (v : Sp (DualNumber ℂ) ⟶ Z) (h : ⊤ ≤ v ⁻¹ᵁ U), v ≫ p = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ x →
      spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = e 0 → ∀ w,
      (IsDerivAt0 e w v ↔ T w = fun i => (TangentOrigin.evalPt v U h (t i)).snd) := by
    intro v h hv hv0 w
    refine ⟨fun H => funext fun i => (isDerivAt0_snd hol t h0 H h i).symm, fun H => ?_⟩
    obtain ⟨v', H'⟩ := exists_isDerivAt0 hol w
    have h' := (top_le_preimage_eps v' _ H'.1 U).2 h0
    rw [hun v v' h h' (hv.trans (isDerivAt0_vertical p x he H').symm) (hv0.trans H'.1.symm) fun i => ?_]
    · exact H'
    · refine TrivSqZeroExt.ext ((fst_evEps v _ hv0 U h _).trans (fst_evEps v' _ H'.1 U h' _).symm) ?_
      rw [isDerivAt0_snd hol t h0 H' h' i]
      exact (congrFun H i).symm
  constructor
  · intro H w w' hw
    obtain ⟨v, Hv⟩ := exists_isDerivAt0 hol w
    have h := (top_le_preimage_eps v _ Hv.1 U).2 h0
    have hv := isDerivAt0_vertical p x he Hv
    exact (H v hv Hv.1).unique Hv ((key v h hv Hv.1 w').2 (hw.symm.trans ((key v h hv Hv.1 w).1 Hv)))
  · intro H v hv hv0
    have h := (top_le_preimage_eps v _ hv0 U).2 h0
    simp only [key v h hv hv0]
    have hs : Function.Surjective T := (LinearMap.injective_iff_surjective (f := T.toLinearMap)).1 H
    exact (Function.bijective_iff_existsUnique T).1 ⟨H, hs⟩ _

end GlobalTheory.VerticalDeriv

namespace GlobalTheory


open VerticalDeriv in
theorem vertical_derivative_in_coordinates :
    ∀ (X : Scheme.{0}) (G : Over X) (x : Sp ℂ ⟶ X) (g : ℕ) (e : (Fin g → ℂ) → (Over.mk x ⟶ G)), IsHolTo Set.univ (fun z => (e z).left) → (∀ w, ∃! v : epsPt x ⟶ G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧ ∀ (U : G.left.Opens) (t : Fin g → Γ(G.left, U)), ⊤ ≤ (show Sp ℂ ⟶ G.left from (e 0).left) ⁻¹ᵁ U → (∀ (v v' : Sp (DualNumber ℂ) ⟶ G.left) (h : ⊤ ≤ v ⁻¹ᵁ U) (h' : ⊤ ≤ v' ⁻¹ᵁ U), v ≫ G.hom = v' ≫ G.hom → spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v' → (∀ i, GlobalTheory.TangentOrigin.evalPt v U h (t i) = GlobalTheory.TangentOrigin.evalPt v' U h' (t i)) → v = v') → ((∀ v : epsPt x ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left → ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left) ↔ Function.Injective (fderiv ℂ (fun z i => valAt' (e z).left U (t i)) 0)) := by
  intro X G x g e hol
  have he : ∀ z, (show Sp ℂ ⟶ G.left from (e z).left) ≫ G.hom = x := fun z => Over.w (e z)
  refine ⟨fun w => ?_, fun U t h0 hun => ?_⟩
  · obtain ⟨v, Hv⟩ := exists_isDerivAt0 hol w
    exact ⟨Over.homMk v (isDerivAt0_vertical G.hom x he Hv), Hv,
      fun v' Hv' => Over.OverMorphism.ext (isDerivAt0_unique Hv' Hv)⟩
  · refine Iff.trans ?_ (bijective_iff_injective G.hom x he hol U t h0 hun)
    exact ⟨fun H v hv hv0 => H (Over.homMk v hv) hv0, fun H v hv0 => H v.left (Over.w v) hv0⟩

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.SharpExt

variable {o : Type} [CommRing o] {S S' : Scheme.{0}} {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o}
  {s' : S' ⟶ Sp o}

theorem isMonHom_prod {G H : Over S} [GrpObj G] [GrpObj H] [IsCommMonObj H] {I : Type} (T : Finset I)
    (f : I → (G ⟶ H)) (hf : ∀ i, IsMonHom (f i)) : IsMonHom (∏ i ∈ T, f i) :=
  Finset.prod_induction f (fun x => IsMonHom x) (fun x y _ _ => GlobalTheory.Serre.isMonHom_mul x y) GlobalTheory.Serre.isMonHom_one
    fun i _ => hf i

def matEnd (e : Fin 8 → Fin 8 → J) (t : TObj g k J b s) (m : Matrix (Fin 8) (Fin 8) ℤ) : t.A ⟶ t.A :=
  letI := t.ab.comm
  ∏ u, ∏ v, t.act (e u v) ^ m u v

theorem isMonHom_matEnd (e : Fin 8 → Fin 8 → J) (t : TObj g k J b s) (m : Matrix (Fin 8) (Fin 8) ℤ) :
    IsMonHom (matEnd e t m) :=
  letI := t.ab.comm
  isMonHom_prod _ _ fun u => isMonHom_prod _ _ fun v =>
    haveI := t.hom (e u v)
    GlobalTheory.Serre.isMonHom_zpow _ _

def ext (e : Fin 8 → Fin 8 → J) (t : TObj g k J b s) : TObj g k (J ⊕ Matrix (Fin 8) (Fin 8) ℤ) b s :=
  { t with
    act := Sum.elim t.act (matEnd e t)
    hom := fun j => match j with
      | .inl j => t.hom j
      | .inr m => isMonHom_matEnd e t m }

theorem tMap_ext (e : Fin 8 → Fin 8 → J) {t : TObj g k J b s} {t' : TObj g k J b s'} {f : S' ⟶ S}
    (H : TMap t' t f) : TMap (ext e t') (ext e t) f := by
  obtain ⟨φ, h, hL, hpt, hact⟩ := H
  refine ⟨φ, h, hL, hpt, ?_⟩
  rintro (j | m)
  · exact hact j
  · letI := t.ab.comm
    letI := t'.ab.comm
    let U : Over.mk (t'.A.hom ≫ f) ⟶ t.A := Over.homMk φ h.1.w
    have key : pushHom h t'.A (matEnd e t' m) = preHom (G := t.A) U (matEnd e t m) := by
      simp only [matEnd, map_prod, map_zpow]
      refine Finset.prod_congr rfl fun u _ => Finset.prod_congr rfl fun v _ => congrArg (· ^ m u v) ?_
      exact Over.OverMorphism.ext (hact _)
    exact congrArg (fun q => q.left) key

theorem isSharp_ext {h : ℕ} {W : Matrix (Fin 8) (Fin 8) ℤ} {a : J → Matrix (Fin 8) (Fin 8) ℤ}
    {bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))} {e : Fin 8 → Fin 8 → J}
    (he : ∀ u v, a (e u v) = Matrix.single u v 1) {t : TObj g k J b s} {c : SiegPre h k (b.ζ : o) s}
    (H : IsSharp W a bas t c) : IsSharp W (Sum.elim a id) bas (ext e t) c := by
  obtain ⟨pr, hmon, huniv, hL, hmat, hpt⟩ := H
  refine ⟨pr, hmon, huniv, hL, ?_, hpt⟩
  have hpr : ∀ u v w, t.act (e u v) ≫ pr w = if w = u then pr v else 1 := by
    intro u v w
    rw [hmat, he, List.prod_ofFn]
    split_ifs with hw
    · subst hw
      rw [Finset.prod_eq_single v] <;> simp +contextual [Matrix.single_apply, eq_comm]
    · refine Finset.prod_eq_one fun i _ => ?_
      simp [Ne.symm hw]
  rintro (j | m) w
  · exact hmat j w
  · letI := t.ab.comm
    haveI := hmon w
    let P : (t.A ⟶ t.A) →* (t.A ⟶ c.A) := MonoidHom.mk' (· ≫ pr w) fun x y => MonObj.mul_comp x y (pr w)
    have hP : ∀ x, P x = x ≫ pr w := fun _ => rfl
    have key : P (matEnd e t m) = (List.ofFn fun v => pr v ^ m w v).prod := by
      simp only [matEnd, map_prod, map_zpow]
      simp only [hP, hpr]
      rw [List.prod_ofFn, Finset.prod_eq_single w]
      · simp
      · intro u _ hu
        simp [Ne.symm hu]
      · simp
    exact key

end GlobalTheory.SharpExt

namespace GlobalTheory

open SharpExt

theorem exists_dense_sharp_all_matrices : ∀ (h g : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (em : o →+* ℂ) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g k J b s), (∀ u v, ∃ j, a j = Matrix.single u v 1) → Dense (fromSet em (SharpClass (b := b) W a bas em) t) → ∃ t' : TObj g k (J ⊕ Matrix (Fin 8) (Fin 8) ℤ) b s, Dense (fromSet em (SharpClass (b := b) W (Sum.elim a id) bas em) t') ∧ ∀ c : SiegPre h k (b.ζ : o) s, IsSharp W (Sum.elim a id) bas t' c → IsSharp W a bas t c := by
  intro h g W J a bas k o _ b em S s t he hd
  choose e he using he
  refine ⟨SharpExt.ext e t, hd.mono ?_, ?_⟩
  · rintro p ⟨K, _, x, hp, K₀, _, β, i, j, t₀, tx, tc, h₁, h₂, h₃, h₄, h₅, c, hc, hs⟩
    exact ⟨K, _, x, hp, K₀, _, β, i, j, SharpExt.ext e t₀, SharpExt.ext e tx, SharpExt.ext e tc, h₁, h₂,
      tMap_ext e h₃, tMap_ext e h₄, tMap_ext e h₅, c, hc, isSharp_ext he hs⟩
  · rintro c ⟨pr, hmon, huniv, hL, hmat, hpt⟩
    exact ⟨pr, hmon, huniv, hL, fun j u => hmat (.inl j) u, hpt⟩

end GlobalTheory
end
end
