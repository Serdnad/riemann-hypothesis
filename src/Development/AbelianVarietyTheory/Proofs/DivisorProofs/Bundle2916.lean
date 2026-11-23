module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2788
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle632
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamiliesValuesCorrespond
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle193
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2774
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2775
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2780
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2785
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2789
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2820
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2892
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2898
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2821
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2895
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2835
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2790
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2133
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle065
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2791
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusOfUnit
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle070
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.FirstMinimumInvariantContinuousPos
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPfA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KaUnfoldPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalFlagTranslateHolds
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

theorem _root_.GlobalTheory.T.exists_finite_extension_unitary_point_generic_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V →
    IsDiscreteValuationRing V → ∀ y : Sp (FractionRing V) ⟶ Xo.XF c,
      ∃ (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (f : V →+* V₁)
        (fK : FractionRing V →+* FractionRing V₁), CDvr V₁ ∧ Function.Injective f ∧ IsLocalHom f ∧ f.Finite ∧
        (∀ a, fK (algebraMap V _ a) = algebraMap V₁ _ (f a)) ∧ ∃ t : SAB H (Sp V₁), GenOf Xo c (spMap fK ≫ y) t := by
  first | exact @GlobalTheory.TraitSemi.exists_ext_semi | exact GlobalTheory.TraitSemi.exists_ext_semi | (intros; apply GlobalTheory.TraitSemi.exists_ext_semi <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc

theorem genOf_isGrpPullback : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [IsDomain R] (y : Sp (FractionRing R) ⟶ Xo.XF c) (t : SAB H (Sp R)) (tF : SAB H (Xo.XF c)), GlobalTheory.UPoinc.GenOf Xo c y t → SABMap tF Xo.univ.t (pullback.fst _ _) → ∃ α : pullback t.G.hom (jK R) ⟶ tF.G.left, IsGrpPullback ((Over.pullback (jK R)).obj t.G) tF.G y α := by
  intro E _ _ _ H Dw l Xo c R _ _ y t tF hy mF
  obtain ⟨tK, ⟨m₁⟩, ⟨m₂⟩⟩ := hy
  obtain ⟨b⟩ := GlobalTheory.TraitOrder.cancel rfl mF m₂
  obtain ⟨e, he, -⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.grpPullback_iso (isGrpPullback_pullback t.G (jK R)) m₁.cart
  haveI := he
  exact ⟨e.hom.left ≫ b.φ,
    ((ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_of_iso e).comp b.cart).congr (Category.id_comp _) rfl⟩

end GlobalTheory.UPoinc
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.KeyEven

theorem keyTraitU_of_kapF : ∀ κ : Rule, MBLow.KapF κ → KeyTraitU κ := by
  intro κ hK V _ _ _ _ hcpl hfin D x G _ _ hG U w₀ hN y hy hvec σ hNz hMaps
  obtain ⟨C, i1, i2, i3, i4, i5, i6, hC, hCC⟩ := GlobalTheory.T.exists_complete_algClosed_field_dvr_embedding V hcpl hfin
  obtain ⟨N, ν, hInt⟩ := GlobalTheory.T.exists_degenerationData_values_ultrametric V hcpl D C hC
  obtain ⟨σ₁, f, th, ϑ, h1, h2, h3, h4, h5⟩ := GlobalTheory.T.integralSection_expands_integrally_genericFibre V hcpl D x.P G hG U w₀ hN.1 x.th σ hMaps C
  have hL : GlobalTheory.UT.LL := GlobalTheory.Ex.hv_holds.1
  have hfam : BrFamSt := GlobalTheory.Ex.brFam hL.1 hL.2.1
  obtain ⟨hv₁, -, -, -, hv₅, -⟩ := hfam V D.toPre D.psi_even D.tau_bimult C N ν 1 le_rfl
  obtain ⟨f', hf', -⟩ := hv₁ ϑ
  obtain ⟨c, rfl⟩ := hv₅ ϑ f' hf'
  have hc : ‖c‖ = 1 := GlobalTheory.T.section_nonzero_fibres_unit_multiple_thetaSeries V hcpl D x.P G hG U σ σ₁ f hNz h1 h2 C hC N ν hInt ϑ c h5 hf'
  have e := hK V hcpl hfin D x G hG U w₀ hN y hy hvec C hC hCC N ν hInt th ϑ c h3 h4 hf'
  rw [hc, one_pow, _root_.one_mul] at e
  exact GlobalTheory.T.exists_unit_of_norm_one_fractionRing_dvr V C hC _ e

end GlobalTheory.KeyEven
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_polarised_E8ThetaPower_over_moduli : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∃ (P : PolAV F.X) (rig : LB.Gen (P.L.pull (eSec P.A))), P.g = 8 * g ∧ GlobalTheory.Poinc.SharpOver F W P (𝟙 F.X) ∧ rig.IsGen ∧ (letI := P.isAb.comm; HypS P.A P.L) := by
  first | exact @GlobalTheory.SiegEighth.exists_polAV_sharpOver | exact GlobalTheory.SiegEighth.exists_polAV_sharpOver | (intros; apply GlobalTheory.SiegEighth.exists_polAV_sharpOver <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.idealSheafAlongLocalSpec_monomial_of_cone_combination : ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (φ : InvFun ℤ)
    (J : Z.IdealSheafData) (d : ℕ), ValOn F i φ J d →
    ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (m : ℕ) (ga δ : Fin m → LinearMap.BilinForm ℤ X)
      (M : ℕ), IsCone id φ ga → (∀ k, δ k = (M : ℤ) • ga k) → ∀ b : Fin m → ℕ, (∀ k, (b k : ℝ) = d * φ.evalZ (δ k)) →
    ∀ (T : Trait F) (W : Type) [CommRing W] [IsLocalRing W] (σ : W →+* T.V) (c : Fin m → ℕ) (e' : T.D.toPre.X ≃+ X)
      (x : Sp W ⟶ Z) (s : Fin m → W), Function.Bijective σ → jK T.V ≫ spMap σ ≫ x = T.y ≫ i →
      (∀ k, Associated (σ (s k)) (T.ϖ ^ c k)) → (∀ a b, T.β a b = ∑ k, (c k : ℤ) * δ k (e' a) (e' b)) →
      idlAlong J x = Ideal.span {∏ k, s k ^ b k} := by
  first | exact @GlobalTheory.Poinc.Arith.idlAlong_monomial | exact GlobalTheory.Poinc.Arith.idlAlong_monomial | (intros; apply GlobalTheory.Poinc.Arith.idlAlong_monomial <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.idealSheafAlongLocalSpec_normalisedBlowup_principal : ∀ {S Z : Scheme.{0}} (π : S ⟶ Z) (J : Z.IdealSheafData), IsNormBl π J → ∀ (R : Type) [CommRing R] [IsLocalRing R]
    (ξ : Sp R ⟶ S), ∃ g₀ : R, idlAlong (J.comap π) ξ = Ideal.span {g₀} := by
  first | exact @GlobalTheory.NormBlPrincipal.idlAlong_comap_principal | exact GlobalTheory.NormBlPrincipal.idlAlong_comap_principal | (intros; apply GlobalTheory.NormBlPrincipal.idlAlong_comap_principal <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.sharp_polarization_unique_pullback : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) {T T' : Scheme.{0}} (P : PolAV T) (P' : PolAV T') (u : T ⟶ F.X) (u' : T' ⟶ F.X) (h : T ⟶ T'), h ≫ u' = u → GlobalTheory.Poinc.SharpOver F W P u → GlobalTheory.Poinc.SharpOver F W P' u' → ∃ α : P.A.left ⟶ P'.A.left, IsGrpPullback P.A P'.A h α ∧ LBIso P.L (P'.L.pull α) := by
  first | exact @GlobalTheory.Poinc.sharpOver_unique | exact GlobalTheory.Poinc.sharpOver_unique | (intros; apply GlobalTheory.Poinc.sharpOver_unique <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.KeyEven

theorem keyValue_homog_of_fibres : ∀ κ : Rule, Homog (fun _ => 1) κ → Funct κ → ∀ (K : Type) [Field K] [CharZero K] (G : Over (Sp K)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (σ σ' : L.L.Sec) (g : ℕ) (y y' : Fin g → (epsR K ⟶ G)) (x x' : KeyIn K) (hg : x.P.g = g) (hg' : x'.P.g = g) (a : K) (M : Matrix (Fin g) (Fin g) K), KeyOn (RingHom.id K) x G L σ (fun i => y (i.cast hg)) → KeyOn (RingHom.id K) x' G L σ' (fun i => y' (i.cast hg')) → (∀ i, σ'.f i = constFn G.hom _ a * σ.f i) → (∀ i, IsLieComb (M i) y (y' i)) → a ^ 8 * (κ K x' : K) = M.det ^ 4 * κ K x := by
  intro κ hH hF K _ _ G _ _ L σ σ' g y y' x x' hg hg' a M hx hx' hσ hM
  subst hg
  have ha : a ≠ 0 := by
    rintro rfl
    exact GlobalTheory.T.keyDatum_false_of_modelSection_zero K G L σ' x' (fun i => y' (i.cast hg')) hx' (fun i => by rw [hσ i]; simp [constFn])
  obtain ⟨v, hv, hvM, hx1⟩ := GlobalTheory.T.exists_lieBasis_lift_model_vectors K G L σ σ' x x' hg' y y' M hx hx' hM
  have hth : ∀ s : Sp K, ∃ z : x.P.A.left, x.P.A.hom z = s ∧ z ∈ nonzeroLocus (KeyOnPol.scale x.P.A.hom a x.th) :=
    fun s => (x.th_ne s).imp fun z hz => ⟨hz.1, KeyOnPol.mem_nonzeroLocus_of_unit x.P.A.hom (Units.mk0 a ha) (fun _ => rfl) hz.2⟩
  have hx2 := GlobalTheory.T.keyDatum_scale_sections_by_constant K G L σ σ' ⟨x.P, x.g_pos, x.rig, x.rig_gen, x.th, x.th_ne, v, hv⟩ y' a
    (KeyOnPol.scale x.P.A.hom a x.th) hth (fun _ => rfl) hσ hx1
  have hx'' : KeyOn ((RingHom.id K).comp (RingHom.id K)) x' G L σ' (fun i => y' (i.cast hg')) := by
    rwa [RingHom.id_comp]
  have hpb := GlobalTheory.T.keyDatum_fibre_of_composable_baseChange K K K (RingHom.id K) (RingHom.id K) G L σ' x.P.g y'
    ⟨x.P, x.g_pos, x.rig, x.rig_gen, KeyOnPol.scale x.P.A.hom a x.th, hth, v, hv⟩ x' rfl hg' hx2 hx''
  have e1 := hF K K (RingHom.id K) _ _ hpb
  have e2 := hH K x.P x.g_pos x.rig x.rig_gen x.th x.th_ne x.v x.basis (KeyOnPol.scale x.P.A.hom a x.th) hth v hv a M
    (fun _ => rfl) hvM
  simp only [Nat.mul_one] at e2
  rw [e1, RingHom.id_apply]
  exact e2

end GlobalTheory.KeyEven
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc

theorem sharpOver_baseChange : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (T T' : Scheme.{0}) (P : PolAV T) (P' : PolAV T') (u : T ⟶ F.X) (f : T' ⟶ T) (φ : P'.A.left ⟶ P.A.left), SharpOver F W P u → IsGrpPullback P'.A P.A f φ → LBIso P'.L (P.L.pull φ) → SharpOver F W P' (f ≫ u) := by
  intro g n F W T T' P P' u f φ hS hφ hL
  obtain ⟨c, hc, pr, hpr, huniv, hbun⟩ := hS
  obtain ⟨c', hc', pr', hpr', huniv', hbun', -⟩ :=
    sharpOver_pullback_end g n _ _ F W T T' P P' u f φ c hc pr hpr huniv hbun hφ hL
  exact ⟨c', hc', pr', hpr', huniv', hbun'⟩

end GlobalTheory.Poinc
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeyEven

theorem dualMapR_eq_of_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (F : DualNumber R →+* DualNumber R')
    (h1 : ∀ a, F (algebraMap R _ a) = algebraMap R' _ (f a)) (h2 : F DualNumber.eps = DualNumber.eps) :
    F = Chart.dualMapR f := by
  refine RingHom.ext fun a => ?_
  have hx : ∀ (S : Type) [CommRing S] (b : DualNumber S),
      b = algebraMap S (DualNumber S) (TrivSqZeroExt.fst b) + algebraMap S (DualNumber S) (TrivSqZeroExt.snd b) * DualNumber.eps := by
    intro S _ b
    rw [← Algebra.smul_def, ← DualNumber.inr_eq_smul_eps, TrivSqZeroExt.algebraMap_eq_inl,
      TrivSqZeroExt.inl_fst_add_inr_snd_eq]
  have hF : F a = algebraMap R' (DualNumber R') (f (TrivSqZeroExt.fst a)) +
      algebraMap R' (DualNumber R') (f (TrivSqZeroExt.snd a)) * DualNumber.eps := by
    conv_lhs => rw [hx R a]
    rw [map_add (f := _), map_mul, h1, h1, h2]
  rw [hF, ← Algebra.smul_def, ← DualNumber.inr_eq_smul_eps, TrivSqZeroExt.algebraMap_eq_inl]
  rfl

theorem keyTrait_of_keyTraitU : ∀ κ : Rule, KeyTraitU κ → KeyTrait κ := by
  intro κ hU V _ _ _ _ hA hF G _ _ L σ x y hSA hUn hLie hNz hKey
  obtain ⟨D, A, U, e, he⟩ := hUn
  obtain ⟨φ, hφe, ψ, F, hPB, hψ, hRig, hTh, hF1, hF2, hv⟩ := hKey
  obtain ⟨θ, hθm, hθφ⟩ := grpPullback_iso (isGrpPullback_pullback G (jK V)) hPB

  obtain ⟨e', he', heR⟩ := GlobalTheory.T.exists_rescaled_iso_preserving_rigidification G U.LG L e he
  obtain ⟨σ', hσ', hnz⟩ := GlobalTheory.T.exists_section_transport_along_generating_iso e' he' U.LG.isLB L.isLB σ
  obtain ⟨w₀, hw₀, hPW⟩ := GlobalTheory.T.exists_iso_cancel_pulled_bundles_germs θ.hom.left φ (pullback.fst G.hom (jK V)) hθφ x.P.L L.L U.LG.L x.P.isLB L.isLB U.LG.isLB ψ e' hψ he'
  let U' : Unif (IsLocalRing.maximalIdeal V) D x.P G :=
    { toUnifPre := { U.toUnifPre with gen := θ, gen_hom := hθm, ext := ⟨w₀, hw₀⟩ }, expand := U.expand }
  have hinv : U'.gen.inv.left ≫ pullback.fst G.hom (jK V) = φ := by
    show θ.inv.left ≫ pullback.fst G.hom (jK V) = φ
    rw [← hθφ, ← Category.assoc, ← Over.comp_left, θ.inv_hom_id, Over.id_left, Category.id_comp]
  have hFd := dualMapR_eq_of_map _ F hF1 hF2
  haveI : IsMonHom θ.hom := hθm
  refine hU V hA hF D x G hSA U' w₀ ⟨hw₀, x.rig_gen, ?_⟩ y hLie (fun i => ?_) σ' ?_ ?_
  · exact GlobalTheory.T.iso_preserves_rigidification_at_origin V G x.P.A θ.hom φ hθφ hφe x.P.L L.L U.LG.L x.P.isLB L.isLB U.LG.isLB x.rig L.rig U.LG.rig ψ e' w₀ hPW hRig heR
  · show (x.v i).left ≫ (U'.gen.inv.left ≫ pullback.fst G.hom (jK V)) = _
    rw [hinv, hv i, hFd]
  · intro s
    obtain ⟨z, hz, hz'⟩ := hNz s
    exact ⟨z, hz, hnz hz'⟩
  · exact GlobalTheory.T.secMaps_secPull_of_pointwise_germs θ.hom.left φ _ hθφ x.P.L L.L U.LG.L L.isLB ψ e' w₀ hPW x.th σ σ' hTh hσ'

end GlobalTheory.KeyEven

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

namespace GlobalTheory.ThickBerg

open ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst MeasureTheory

theorem cpt_mem_dom_small : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (x : Frame X.Ψ r) (z : ReciprocityTheory.L2DbarEstimates.V (nd X)), IsOrth X x → ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) →
    cpt X x z ∈ X.dom := GlobalTheory.T.unitriangularChart_mem_domain_small_ball

theorem ball_injects : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r),
    GoodEmb c σ → IsUnf U → (∀ p : ℕ, p.Prime → l.GoodAt p) → 1 ≤ Dw.p → 1 ≤ Dw.q →
    ∀ (k : U.Comp) (x : Frame (U.X k).Ψ r), IsOrth (U.X k) x →
    100 * (((U.X k).Ψ.card : ℝ) * r) ^ 4 ≤ (l.M' : ℝ) * (U.X k).firstMinimumSq x →
    ∀ γ ∈ (U.X k).Γ, ∀ z z' : ReciprocityTheory.L2DbarEstimates.V (nd (U.X k)), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) →
      ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ∀ b ∈ Bor (U.X k).Ψ r,
      lact γ (cpt (U.X k) x z) = rmul (cpt (U.X k) x z') b → γ = 1 := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU hl hp hq k x hx hM γ hγ z z' hz hz' b hb he
  obtain ⟨hsd, horb⟩ := GlobalTheory.T.selfDual_and_principalCongruence_orbits_of_goodLevel E H Dw l Xo c σ r U hσ hU hl hp hq k
  have hwd : cpt (U.X k) x z ∈ (U.X k).dom := cpt_mem_dom_small E r (U.X k) x z hx hz
  obtain ⟨γ', hγ'U, hγ'c, b', hb', he'⟩ := horb γ hγ _ hwd
  have h1 : lact γ' (cpt (U.X k) x z) =
      rmul (cpt (U.X k) x z') (rmul b (ExtFPf.invF (U.X k) b')) := by
    have e1 := congrArg (fun w => rmul w (ExtFPf.invF (U.X k) b')) (he'.symm.trans he)
    simp only [ExtFPf.rmul_assoc, ExtFPf.rmul_invF _ hb', ExtFPf.rmul_oneF] at e1
    exact e1
  have hγ'1 : γ' = 1 := GlobalTheory.T.deep_congruence_element_separates_chart_ball_thick_frame E r (U.X k) l.M' x hsd hx hM γ' hγ'U hγ'c z z' hz hz' _
    (ExtFPf.mul_mem _ hb (ExtFPf.invF_mem _ hb')) h1
  subst hγ'1
  rw [FundSetPf.lact_one] at he'
  exact (U.X k).Γ_free γ hγ _ hwd b' hb' he'

theorem modelWt_shape : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r),
    GoodEmb c σ → IsUnf U → 1 ≤ Dw.p → 1 ≤ Dw.q → ∀ (u1 : GlobalTheory.AllWt.Weight Dw) (g : ℝ),
    (∀ τ (a b : Fin (Dw.p + Dw.q)), (b : ℕ) = a + 1 → g ≤ (u1 τ a : ℝ) - u1 τ b) → ∀ k : U.Comp,
    (∀ τ (a b : Fin r), (b : ℕ) = a + 1 → (b : ℕ) ≠ (U.X k).p0 →
      g ≤ (modelWt U (wtOf Dw u1 0) k τ a : ℝ) - modelWt U (wtOf Dw u1 0) k τ b) ∧
    (∀ τ (a b : Fin r), (a : ℕ) = 0 → (b : ℕ) = r - 1 →
      g ≤ (modelWt U (wtOf Dw u1 0) k τ b : ℝ) - modelWt U (wtOf Dw u1 0) k τ a) ∧
    (∑ τ, ∑ a, |(modelWt U (wtOf Dw u1 0) k τ a : ℝ)|) = l1 u1 ∧
    (U.X k).Ψ.card = Nat.card (Psi H) := GlobalTheory.T.model_weight_gap_l1_card_bound

theorem orth_transfer : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (la : Wt X.Ψ r) (y : Frame X.Ψ r), y ∈ X.dom → ∃ x, IsOrth X x ∧ X.firstMinimumSq x = X.firstMinimumSq y ∧
    ∀ P ∈ X.SS la, P x ≠ 0 → P y ≠ 0 ∧ X.pnorm la P y = X.pnorm la P x := by
  intro E _ _ _ r X la y hy
  obtain ⟨x, hx, b, hb, rfl⟩ := ReciprocityTheory.ChartRestriction.G.AR.Up.ortho_holds r X y hy
  have hxd := ReciprocityTheory.ChartRestriction.G.AR.Up.KU.orth_dom X hx
  refine ⟨x, hx, (firstMinimumSq_rightBorel X hxd hb).symm, fun P hP hPx =>
    ⟨?_, FrameDegreeData.pnorm_rmul X la P hP.1.1.2.1 x hxd b hb⟩⟩
  rw [hP.1.1.2.1 x hxd b hb]
  refine mul_ne_zero ?_ hPx
  unfold bchar
  refine Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ ?_
  have h := (hb τ).1
  rw [Matrix.det_of_upperTriangular ((ExtFPf.upper_iff X b τ).mp (hb τ).2)] at h
  exact Finset.prod_ne_zero_iff.1 h i (Finset.mem_univ i)

theorem nums (a l C0 PP T D b uE : ℝ) (ha : 1 ≤ a) (hl : 10 ≤ l) (hlC : C0 ≤ l) (hPP : (a * l) ^ 12 ≤ PP)
    (hT : (a * l) ^ 24 ≤ T) (hD : 1 ≤ D) (hrows : PP * T * D ^ 2 * l ≤ b) (hbu : b ≤ uE) :
    T * a ^ 8 ≤ uE ∧ C0 * a ^ 8 ≤ T ∧ 100 * a ^ 4 ≤ b := by
  have h1 : 1 ≤ a * l := by nlinarith
  have hal8 : a ^ 8 ≤ (a * l) ^ 12 :=
    calc a ^ 8 ≤ (a * l) ^ 8 := pow_le_pow_left₀ (by linarith) (by nlinarith) 8
      _ ≤ (a * l) ^ 12 := pow_le_pow_right₀ h1 (by norm_num)
  have hPP' : a ^ 8 ≤ PP := hal8.trans hPP
  have hT1 : 1 ≤ T := (one_le_pow₀ h1).trans hT
  have hPP0 : 0 ≤ PP := (by positivity : (0 : ℝ) ≤ a ^ 8).trans hPP'
  have hDl : 1 ≤ D ^ 2 * l := by nlinarith [one_le_pow₀ (n := 2) hD]
  have hTPP : T * PP ≤ b := by
    have h2 : T * PP ≤ PP * T * D ^ 2 * l := by
      have h3 : 0 ≤ PP * T := mul_nonneg hPP0 (by linarith)
      nlinarith
    linarith
  refine ⟨?_, ?_, ?_⟩
  · calc T * a ^ 8 ≤ T * PP := mul_le_mul_of_nonneg_left hPP' (by linarith)
      _ ≤ uE := hTPP.trans hbu
  · have h4 : a ^ 8 * l ≤ (a * l) ^ 24 := by
      rw [mul_pow]
      exact mul_le_mul (pow_le_pow_right₀ ha (by norm_num)) (le_self_pow₀ (by linarith) (by norm_num))
        (by linarith) (by positivity)
    have h5 : C0 * a ^ 8 ≤ l * a ^ 8 := mul_le_mul_of_nonneg_right hlC (by positivity)
    linarith
  · have h12 : 100 * a ^ 4 ≤ (a * l) ^ 12 := by
      rw [mul_pow]
      have h6 : (100 : ℝ) ≤ l ^ 12 :=
        calc (100 : ℝ) ≤ 10 ^ 12 := by norm_num
          _ ≤ l ^ 12 := pow_le_pow_left₀ (by norm_num) hl 12
      have h7 : a ^ 4 ≤ a ^ 12 := pow_le_pow_right₀ ha (by norm_num)
      have h8 : 0 ≤ a ^ 4 := by positivity
      nlinarith
    have h9 : PP ≤ T * PP := le_mul_of_one_le_left hPP0 hT1
    linarith

end GlobalTheory.ThickBerg
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

theorem _root_.GlobalTheory.T.polarisationBundle_symmetric_pullback_of_uniformisation : AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ w : O, LBIso U.LG.L (cubeLB G ![𝟙 G, oG.act w] U.LG.L) → GlobalTheory.PolDeg.IsPrim D.toPre.P (o.onB.act w) := by
  first | exact @GlobalTheory.PrimDescent.isPrim_of_unif | exact GlobalTheory.PrimDescent.isPrim_of_unif | (intros; apply GlobalTheory.PrimDescent.isPrim_of_unif <;> assumption)
end
