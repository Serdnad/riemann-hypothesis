module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle014
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifBijectiveOfParam
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdJet
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteProjectiveBis
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieChartOfSmoothChart
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle003
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle016
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle025
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle001
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle029
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.SpanXLeKerAevalZero

@[expose] public section

section

noncomputable section
namespace PositivityTheory.HtPt.Cd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.ChartCompare GlobalTheory.FrameTangent GlobalTheory.IndefiniteRowSideFullHecke.JetChartLaws

section Gen
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)] {X0 : Scheme.{0}}
  {t : SAB H X0} {S : Type} [CommRing S] {x : Sp S ⟶ X0} {d : ℕ} (g : GermAt t x d)

def jp : JetPts t.G x d := (famEquiv x t.G d).symm g.x

theorem fam_jp : famEquiv x t.G d (jp g) = g.x := Equiv.apply_symm_apply _ _

theorem x_eq (m : ℕ) : g.x m = homAt x (jIn S d m) ≫ jp g m := (congrFun (fam_jp g) m).symm

theorem jp_eq (m : ℕ) : jp g m = homAt x (jOut S d m) ≫ g.x m := rfl

theorem jp_zero (m : ℕ) : algMap x (jetAug : Jet S (Fin d) m →ₐ[S] S) ≫ jp g m = 1 :=
  (zero_iff t x (jp g) m).1 (by rw [fam_jp]; exact g.chart.zero m)

def gd : (Fin d → S) →ₗ[S] TanM x t.G := dif x (jp g 1) (jp_zero g 1)

theorem tg_eq (l : Fin d) : g.tg l = (tv (gd g (Pi.single l 1))).left := by
  have h := (tan_iff t x (jp g) (jp_zero g 1) (g.tg l) (fun j => if l = j then 1 else 0)).2
    (by rw [fam_jp]; exact g.chart.tan l)
  have e : (fun j => if l = j then (1 : S) else 0) = Pi.single l 1 := by
    funext j; simp [Pi.single_apply, eq_comm]
  rw [e] at h
  exact h

theorem comb_iff (a : Fin d → S) (w : Sp (DualNumber S) ⟶ t.G.left) :
    IsCombAtG t x g.tg a w ↔ (tv (gd g a)).left = w := by
  have e : g.tg = fun i => (tv (gd g (Pi.single ((Equiv.refl (Fin d)) i) 1))).left := funext (tg_eq g)
  have e₂ : ∑ i, a i • gd g (Pi.single i 1) = gd g a := by

    simp only [← map_smul, ← map_sum]
    congr 1
    funext k; simp [Pi.single_apply]
  rw [e, ← e₂]
  exact comb_iff_sum t x (Equiv.refl _) (fun i => gd g (Pi.single i 1)) a w

theorem gd_bij : Function.Bijective (gd g) := by
  rw [Function.bijective_iff_existsUnique]
  intro W
  refine (existsUnique_congr fun a => ?_).1 (g.basis _ (isTanAtG_of _ (tv_zero' W)))
  rw [comb_iff]
  exact ⟨fun h => tv_injective (Over.OverMorphism.ext h), fun h => by rw [h]⟩

theorem jp_param : IsFormalParam t.G x (jp g) :=
  param_of_dif_bijective t.semi.smooth
    (fun m => (trunc_iff t x (jp g) m).1 (by rw [fam_jp]; exact g.chart.trunc m)) (jp_zero g) (gd_bij g)

theorem coord_unique {m : ℕ} {B : Type} [CommRing B] [Algebra S B] (I : Ideal B) (hI : I ^ (m + 1) = ⊥)
    (y : overAt x B ⟶ t.G) (hy : homAt x (Ideal.Quotient.mkₐ S I) ≫ y = 1) :
    ∃! χ : Jet S (Fin 1 × Fin d) m →ₐ[S] B, y = homAt x χ ≫ g.x m := by
  obtain ⟨f, hf, hu⟩ := (jp_param g).2.2 m B I hI y hy
  refine ⟨f.comp (jOut S d m), ?_, fun χ hχ => ?_⟩
  · beta_reduce
    rw [← hcomp, ← jp_eq]; exact hf.symm
  · have := hu (χ.comp (jIn S d m)) (by
      beta_reduce
      rw [algMap_eq, ← hcomp, ← x_eq]; exact hχ.symm)
    rw [← this, AlgHom.comp_assoc, jIn_jOut, AlgHom.comp_id]

theorem coord_aug {m : ℕ} {B : Type} [CommRing B] [Algebra S B] (aug : B →ₐ[S] S)
    (hI : RingHom.ker aug ^ (m + 1) = ⊥) (y : overAt x B ⟶ t.G) (hy : homAt x aug ≫ y = 1) :
    ∃! χ : Jet S (Fin 1 × Fin d) m →ₐ[S] B, aug.comp χ = jetAug ∧ y = homAt x χ ≫ g.x m := by
  have e : Ideal.Quotient.mkₐ S (RingHom.ker aug) = (Algebra.ofId S _).comp aug := by
    refine AlgHom.ext fun r => ?_
    show Ideal.Quotient.mk _ r = Ideal.Quotient.mk _ (algebraMap S B (aug r))
    rw [Ideal.Quotient.eq, RingHom.mem_ker, map_sub, AlgHom.commutes]
    simp
  obtain ⟨χ, hχ, hu⟩ := coord_unique g _ hI y (by rw [e, ← hcomp, hy, MonObj.comp_one])
  refine ⟨χ, ⟨?_, hχ⟩, fun χ' h => hu χ' h.2⟩
  exact (coord_unique g (m := m) (B := S) ⊥ (Ideal.bot_pow (by omega)) 1 (MonObj.comp_one _)).unique
    (by rw [← hcomp, ← hχ, hy]) (g.chart.zero m).symm

theorem ker_aug_pow (J : Type) (m : ℕ) : RingHom.ker (jetAug : Jet S J m →ₐ[S] S) ^ (m + 1) = ⊥ :=
  Chart.ker_jetAug_pow (R := S) J m

theorem coord_jet (J : Type) (m : ℕ) (y : overAt x (Jet S J m) ⟶ t.G)
    (hy : homAt x (jetAug : Jet S J m →ₐ[S] S) ≫ y = 1) :
    ∃! χ : Jet S (Fin 1 × Fin d) m →ₐ[S] Jet S J m,
      (∀ q, (jetAug : Jet S J m →ₐ[S] S) (χ (Ideal.Quotient.mk _ (MvPolynomial.X q))) = 0) ∧ y = homAt x χ ≫ g.x m := by
  refine (existsUnique_congr fun χ => and_congr_left fun _ => ?_).1 (coord_aug g jetAug (ker_aug_pow J m) y hy)
  exact ⟨fun h q => (AlgHom.congr_fun h (z m q)).trans (jetAug_z m q),
    fun h => jext fun q => (h q).trans (jetAug_z m q).symm⟩

theorem aeval_inr {κ : Type} [Fintype κ] [DecidableEq κ] (c : κ → S) (P : MvPolynomial κ S) :
    MvPolynomial.aeval (fun s => (TrivSqZeroExt.inr (c s) : DualNumber S)) P =
      TrivSqZeroExt.inl (MvPolynomial.constantCoeff P) +
        TrivSqZeroExt.inr (∑ s, P.coeff (Finsupp.single s 1) * c s) := by
  induction P using MvPolynomial.induction_on with
  | C r =>
    have : ∀ s : κ, (MvPolynomial.C r : MvPolynomial κ S).coeff (Finsupp.single s 1) = 0 := fun s => by
      rw [MvPolynomial.coeff_C, if_neg (Finsupp.single_ne_zero.2 one_ne_zero).symm]
    simp [this, TrivSqZeroExt.algebraMap_eq_inl]
  | add p q hp hq =>
    rw [map_add (f := _), hp, hq]
    ext <;> simp [add_mul, Finset.sum_add_distrib]
  | mul_X p n hp =>
    have : ∀ s : κ, (p * MvPolynomial.X n).coeff (Finsupp.single s 1) =
        if s = n then MvPolynomial.constantCoeff p else 0 := fun s => by
      rw [MvPolynomial.coeff_mul_X']
      by_cases h : s = n
      · subst h; simp [MvPolynomial.constantCoeff_eq]
      · simp [h, Ne.symm h]
    rw [map_mul, hp, MvPolynomial.aeval_X]
    ext <;> simp [this, mul_comm]

theorem vec_subst (φ : Germ.Pt S 1 d) (c : Fin d → S) :
    ((jetVec c).comp (jOut S d 1)).comp (jetSubstP 1 fun p : Fin 1 × Fin d => psTrunc 1 (φ p.2)) =
      (jetVec ((lin φ 1).mulVec c)).comp (jOut S d 1) := by
  have hT : ∀ (c : Fin d → S) (P : MvPolynomial (Fin 1 × Fin d) S),
      ((jetVec c).comp (jOut S d 1)) (Ideal.Quotient.mk _ P) =
        MvPolynomial.aeval (fun s : Fin 1 × Fin d => (TrivSqZeroExt.inr (c s.2) : DualNumber S)) P := fun c P => by
    have : ((jetVec c).comp (jOut S d 1)).comp (Ideal.Quotient.mkₐ S _) =
        MvPolynomial.aeval (fun s : Fin 1 × Fin d => (TrivSqZeroExt.inr (c s.2) : DualNumber S)) :=
      MvPolynomial.algHom_ext fun s => by
        rw [MvPolynomial.aeval_X]
        refine Eq.trans ?_ (jetVec_z_one c s.2)
        exact congrArg (jetVec c) (jetMap_z (S := S) 1 (fun p : Fin 1 × Fin d => MvPolynomial.X p.2)
          (fun _ => X_mem_orig _) s)
    exact AlgHom.congr_fun this P
  refine jext fun p => ?_
  rw [AlgHom.comp_apply, jetSubstP, jetMap_z, hT, hT, map_sub, aeval_inr, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
  have : ∀ s : Fin 1 × Fin d, (psTrunc 1 (φ p.2)).coeff (Finsupp.single s 1) =
      MvPowerSeries.coeff (Finsupp.single s 1) (φ p.2) := fun s => by
    rw [FBIdJet.psTrunc_eq, MvPowerSeries.coeff_truncTotal _ (by simp)]
  simp only [this, Fintype.sum_prod_type, Finset.univ_unique, Finset.sum_singleton]
  ext
  · simp [TrivSqZeroExt.algebraMap_eq_inl]
  · simp [lin, Matrix.mulVec, dotProduct, TrivSqZeroExt.algebraMap_eq_inl]

theorem tv_gd (c : Fin d → S) : tv (gd g c) = homAt x ((jetVec c).comp (jOut S d 1)) ≫ g.x 1 := by
  rw [← hcomp]; rfl

theorem gd_act (a : 𝓞 E) (c : Fin d → S) :
    tv (gd g c) ≫ t.act.act a = tv (gd g ((rho g.B a).mulVec c)) := by
  rw [tv_gd, tv_gd, Category.assoc, g.chart.act 1 a, hcomp, vec_subst]
  rfl

end Gen

theorem germ_univ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] [IsLocalRing S] (x : Sp S ⟶ X0) (d : ℕ) (g : GermAt t x d), (∀ (d₂ : ℕ) (_ : GermAt t x d₂), d = d₂) ∧ ∀ (J : Type) [Finite J] (m : ℕ) (y : overAt x (Jet S J m) ⟶ t.G), homAt x (jetAug : Jet S J m →ₐ[S] S) ≫ y = 1 → ∃! χ : Jet S (Fin 1 × Fin d) m →ₐ[S] Jet S J m, (∀ q, (jetAug : Jet S J m →ₐ[S] S) (χ (Ideal.Quotient.mk _ (MvPolynomial.X q))) = 0) ∧ y = homAt x χ ≫ g.x m := by
  intro E _ _ _ H _ _ X0 t S _ _ x d g
  refine ⟨fun d₂ g₂ => ?_, fun J _ m y hy => coord_jet g J m y hy⟩
  have e := ((LinearEquiv.ofBijective _ (gd_bij g)).trans (LinearEquiv.ofBijective _ (gd_bij g₂)).symm).finrank_eq
  simpa using e

theorem germ_lie : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x : Sp S ⟶ X0) (d : ℕ) (g : GermAt t x d) (V : Type) [AddCommGroup V] [Module S V] (M : GlobalTheory.CompanionTheory.Ar.LieModel t.G x V), ∃ e : V ≃ₗ[S] (Fin d → S), (∀ v, IsCombAtG t x g.tg (e v) (M.pt v).left) ∧ ∀ r : 𝓞 E →+* Module.End S V, M.IsActOf t.act.act r → ∀ a v, e (r a v) = (rho g.B a).mulVec (e v) := by
  intro E _ _ _ H _ _ X0 t S _ x d g V _ _ M
  have ht : ∀ v, IsTanAtG t x (M.pt v).left := fun v => ⟨Over.w (M.pt v), M.tan v⟩
  let L : V →ₗ[S] TanM x t.G :=
    { toFun := fun v => mkT (ovT (ht v)) (smT_zero_ovT (ht v))
      map_add' := fun v w => tv_injective (M.add v w)
      map_smul' := fun c v => tv_injective (Over.OverMorphism.ext (M.smul c v)) }
  have hL : ∀ v, tv (L v) = M.pt v := fun v => rfl
  have hb : Function.Bijective L := by
    refine ⟨fun v w h => M.inj ((hL v).symm.trans ((congrArg tv h).trans (hL w))), fun W => ?_⟩
    obtain ⟨v, hv⟩ := M.onto (tv W) (isTanAtG_of _ (tv_zero' W)).2
    exact ⟨v, tv_injective hv⟩
  let e : V ≃ₗ[S] (Fin d → S) := (LinearEquiv.ofBijective L hb).trans (LinearEquiv.ofBijective _ (gd_bij g)).symm
  have he : ∀ v, gd g (e v) = L v := fun v => (LinearEquiv.ofBijective _ (gd_bij g)).apply_symm_apply _
  refine ⟨e, fun v => (comb_iff g _ _).2 (by rw [he, hL]), fun r hr a v => (gd_bij g).1 (tv_injective ?_)⟩
  rw [← gd_act, he, he, hL, hL]
  exact hr a v

end PositivityTheory.HtPt.Cd
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieFin

noncomputable section

namespace PositivityTheory.HtPt.Htat

namespace Lie

variable {S : Scheme.{0}} {G : Over S} [GrpObj G]

theorem loc_of_charts {R : Type} [CommRing R] (x : Sp R ⟶ S) {J : Type} [Finite J] (f : J → R)
    (hf : Ideal.span (Set.range f) = ⊤) (hch : ∀ i, LieChart G x (f i)) {E : Type} [AddCommGroup E] [Module R E]
    (M : LieModel G x E) (i : J) {F : Type} [AddCommGroup F] [Module R F] [Module (Localization.Away (f i)) F]
    [IsScalarTower R (Localization.Away (f i)) F] (y : Sp (Localization.Away (f i)) ⟶ S) (hy : y = ptAt x (f i))
    (Mi : LieModel G y F) (r : E →ₗ[R] F)
    (hr : ∀ e, (Mi.pt (r e)).left = spMap (dualMap (algebraMap R (Localization.Away (f i)))) ≫ (M.pt e).left) :
    IsLocalizedModule (Submonoid.powers (f i)) r := by
  subst hy
  choose P iA iM iL ist ifin iproj m nat using hch
  have hix : ∀ g : Idx f, ∃ i, f i ∣ g.1 := fun g => g.2
  choose ix hix using hix
  have hqc : ∀ (g g' : Idx f) (h : g.1 ∣ g'.1) (t : R), g'.1 = g.1 * t →
      ∀ r : (P (ix g) →ₗ[R] Localization.Away g.1) →ₗ[R] (P (ix g') →ₗ[R] Localization.Away g'.1),
      (∀ y, ((m (ix g') _ (unit_of_dvd (hix g'))).pt (r y)).left =
        spMap (dualMap (cmap h).toRingHom) ≫ ((m (ix g) _ (unit_of_dvd (hix g))).pt y).left) →
      IsLocalizedModule (Submonoid.powers t) r := by
    intro g g' h t ht r hr
    have hu' : IsUnit (algebraMap R (Localization.Away g'.1) (f (ix g))) :=
      unit_of_dvd ((hix g).trans h)
    obtain ⟨e, he⟩ := exists_equiv (R := R) (ptAt x g'.1) (m (ix g) _ hu') (m (ix g') _ (unit_of_dvd (hix g')))
    haveI := cmap_loc h ht
    haveI hcr := GlobalTheory.T.localized_module_base_change R (P (ix g)) (Localization.Away g.1) (Localization.Away g'.1) (f (ix g)) t
      (unit_of_dvd (hix g)) (cmap h) (cmap_loc h ht)
    have hrr : r = (e : _ →ₗ[R] _) ∘ₗ LinearMap.compRight R (cmap h).toLinearMap := by
      refine LinearMap.ext fun y => pt_left_inj (m (ix g') _ (unit_of_dvd (hix g'))) ?_
      rw [hr]
      refine Eq.trans ?_ (he _).symm
      exact (nat (ix g) _ _ (unit_of_dvd (hix g)) hu' (cmap h) y).symm
    rw [hrr]
    exact IsLocalizedModule.of_linearEquiv _ _ _
  obtain ⟨ρ, hρ, hloc⟩ := loc_of_family x f hf M (fun g => P (ix g) →ₗ[R] Localization.Away g.1)
    (fun g => m (ix g) _ (unit_of_dvd (hix g))) hqc
  obtain ⟨e, he⟩ := exists_equiv (R := R) (ptAt x (f i))
    (m (ix ⟨f i, i, dvd_rfl⟩) _ (unit_of_dvd (hix ⟨f i, i, dvd_rfl⟩))) Mi
  have hrr : r = (e : _ →ₗ[R] _) ∘ₗ ρ ⟨f i, i, dvd_rfl⟩ :=
    LinearMap.ext fun y => pt_left_inj Mi ((hr y).trans ((he _).trans (hρ ⟨f i, i, dvd_rfl⟩ y)).symm)
  rw [hrr]
  haveI := hloc i
  exact IsLocalizedModule.of_linearEquiv _ _ _


variable (G) in
def SmChart {R : Type} [CommRing R] (x : Sp R ⟶ S) (f : R) : Prop :=
  ∃ (U : G.left.Opens) (V : S.Opens) (hU : IsAffineOpen U) (_ : IsAffineOpen V) (hUV : U ≤ G.hom ⁻¹ᵁ V),
    RingHom.Smooth (G.hom.appLE V U hUV).hom ∧ ∃ u : Γ(G.left, U) →+* Localization.Away f,
      (1 : Over.mk (spMap (algebraMap R (Localization.Away f)) ≫ x) ⟶ G).left = spMap u ≫ hU.fromSpec

theorem SmChart.lieChart {R : Type} [CommRing R] {x : Sp R ⟶ S} {f : R} (h : SmChart G x f) : LieChart G x f := by
  obtain ⟨U, V, hU, hV, hUV, hsm, u, hu⟩ := h
  exact lieChart_of_smooth_chart S G R x f U V hU hV hUV hsm u hu

theorem unit_away {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (f : R) :
    IsUnit (algebraMap R (Localization.Away (algebraMap R R' f)) f) := by
  rw [IsScalarTower.algebraMap_apply R R' (Localization.Away (algebraMap R R' f))]
  exact IsLocalization.Away.algebraMap_isUnit _

theorem pt_eq {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (x : Sp R ⟶ S) (g : R') :
    spMap (algebraMap R (Localization.Away g)) ≫ x = ptAt (spMap (algebraMap R R') ≫ x) g := by
  rw [ptAt, ← Category.assoc, spMap_comp', ← IsScalarTower.algebraMap_eq]

theorem SmChart.base {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {x : Sp R ⟶ S} {f : R}
    (h : SmChart G x f) : SmChart G (spMap (algebraMap R R') ≫ x) (algebraMap R R' f) := by
  obtain ⟨U, V, hU, hV, hUV, hsm, u, hu⟩ := h
  let κ : Localization.Away f →+* Localization.Away (algebraMap R R' f) :=
    IsLocalization.Away.lift f (unit_away (R' := R') f)
  have hκ : κ.comp (algebraMap R _) = algebraMap R _ := IsLocalization.Away.lift_comp f _
  refine ⟨U, V, hU, hV, hUV, hsm, κ.comp u, ?_⟩
  rw [ChartDer.one_left] at hu ⊢
  simp only [Over.mk_hom] at hu ⊢
  have e := pt_eq x (algebraMap R R' f)
  rw [← hκ, ← spMap_comp'] at e
  rw [← spMap_comp' u κ, Category.assoc (spMap κ), ← hu]
  refine (congrArg (· ≫ η[G].left) e.symm).trans ?_
  simp only [Category.assoc]

theorem exists_cover [Smooth G.hom] {R : Type} [CommRing R] (x : Sp R ⟶ S) :
    ∃ (J : Type) (_ : Finite J) (f : J → R), Ideal.span (Set.range f) = ⊤ ∧ ∀ i, SmChart G x (f i) := by
  have hspan : Ideal.span {f : R | SmChart G x f} = ⊤ := by
    by_contra hne
    obtain ⟨p, hp, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨f, hf, h⟩ := GlobalTheory.T.smooth_group_tangent_lift S G R x p
    exact hf (hle (Ideal.subset_span h))
  obtain ⟨s, hs, hsp⟩ := (Ideal.span_eq_top_iff_finite _).mp hspan
  refine ⟨s, inferInstance, fun i => i, ?_, fun i => hs i.2⟩
  rw [Subtype.range_coe_subtype]
  exact hsp

theorem isBaseChange_lie [Smooth G.hom] {R : Type} [CommRing R] (x : Sp R ⟶ S) {L : Type} [AddCommGroup L]
    [Module R L] (M : LieModel G x L) (R' : Type) [CommRing R'] [Algebra R R'] (L' : Type) [AddCommGroup L']
    [Module R' L'] [Module R L'] [IsScalarTower R R' L'] (M' : LieModel G (spMap (algebraMap R R') ≫ x) L')
    (β : L →ₗ[R] L') (hβ : ∀ e, (M'.pt (β e)).left = spMap (dualMap (algebraMap R R')) ≫ (M.pt e).left) :
    IsBaseChange R' β := by
  obtain ⟨J, _, f, hf, hch⟩ := exists_cover (G := G) x
  have hf' : Ideal.span (Set.range fun i => algebraMap R R' (f i)) = ⊤ := by
    have := congrArg (Ideal.map (algebraMap R R')) hf
    rwa [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this
  let φ : R' ⊗[R] L →ₗ[R'] L' := β.liftBaseChange R'
  have hφ : ∀ e, φ (1 ⊗ₜ e) = β e := fun e => by
    rw [LinearMap.liftBaseChange_tmul, one_smul]
  have hbij : Function.Bijective φ := by
    refine bijective_of_cover _ hf' φ fun i => ?_
    obtain ⟨P, _, _, _, _, _, _, m, nat⟩ := (hch i).lieChart
    let A := Localization.Away (f i)
    let C := Localization.Away (algebraMap R R' (f i))
    have hA : IsUnit (algebraMap R A (f i)) := IsLocalization.Away.algebraMap_isUnit _
    have hC : IsUnit (algebraMap R C (f i)) := unit_away (f i)
    let κ : A →+* C := IsLocalization.Away.lift (f i) hC
    have hκ : κ.comp (algebraMap R A) = algebraMap R C := IsLocalization.Away.lift_comp _ _
    letI : Algebra A C := κ.toAlgebra
    haveI : IsScalarTower R A C := IsScalarTower.of_algebraMap_eq' hκ.symm
    let c : A →ₐ[R] C := IsScalarTower.toAlgHom R A C
    obtain ⟨a, ha⟩ := exists_trL (R := R') (spMap (algebraMap R R') ≫ x) (spMap (algebraMap R C) ≫ x)
      (algebraMap R' C) (fun _ => rfl) (pt_eq x _).symm M' (m C hC)
    obtain ⟨ρ, hρ⟩ := exists_trL (R := R) x (spMap (algebraMap R A) ≫ x) (algebraMap R A) (fun _ => rfl) rfl M
      (m A hA)
    have l1 : IsLocalizedModule (Submonoid.powers (algebraMap R R' (f i))) a :=
      loc_of_charts (spMap (algebraMap R R') ≫ x) (fun i => algebraMap R R' (f i)) hf'
        (fun i => (hch i).base.lieChart) M' i _ (pt_eq x _) (m C hC) a ha
    have l2 : IsLocalizedModule (Submonoid.powers (f i)) ρ :=
      loc_of_charts x f hf (fun i => (hch i).lieChart) M i _ rfl (m A hA) ρ hρ
    have b2 : IsBaseChange A ρ := (isLocalizedModule_iff_isBaseChange (Submonoid.powers (f i)) A ρ).1 l2
    let g : (P →ₗ[R] A) →ₗ[A] (P →ₗ[R] C) :=
      { toFun := fun w => c.toLinearMap ∘ₗ w
        map_add' := fun w w' => LinearMap.comp_add _ _ _
        map_smul' := fun r w => LinearMap.ext fun p => by
          show κ (r * w p) = r • κ (w p)
          rw [map_mul, Algebra.smul_def]
          rfl }
    have b3 : IsBaseChange C g := isBaseChange_hom
      (fun w r p => GlobalTheory.CompanionTheory.LocHom.map_away_smul (AlgHom.id R A) w r p)
      (fun w r p => GlobalTheory.CompanionTheory.LocHom.map_away_smul c w r p) g fun _ _ => rfl
    have b4 := b2.comp b3
    have e : (g.restrictScalars R) ∘ₗ ρ = ((a ∘ₗ φ).restrictScalars R) ∘ₗ (TensorProduct.mk R R' L 1) := by
      refine LinearMap.ext fun l => pt_left_inj (m C hC) ?_
      show ((m C hC).pt (c.toLinearMap ∘ₗ ρ l)).left = ((m C hC).pt (a (φ (1 ⊗ₜ l)))).left
      rw [nat A C hA hC c, hρ, ha, hφ, hβ, ← Category.assoc, ← Category.assoc, spMap_dual_comp, spMap_dual_comp,
        ← IsScalarTower.algebraMap_eq, ← hκ]
      rfl
    rw [e] at b4
    have b5 : IsBaseChange C (a ∘ₗ φ) := (TensorProduct.isBaseChange R L R').of_comp b4
    exact ⟨P →ₗ[R] C, inferInstance, inferInstance, a, l1,
      (isLocalizedModule_iff_isBaseChange (Submonoid.powers (algebraMap R R' (f i))) C _).2 b5⟩
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective φ hbij) hφ

end Lie

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct in
open GlobalTheory.CompanionTheory.Ar in
theorem lie_proj : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [Smooth G.hom] (R : Type) [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S) (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L), Module.Finite R L ∧ Module.Projective R L ∧ ∀ (R' : Type) [CommRing R'] [Algebra R R'] (L' : Type) [AddCommGroup L'] [Module R' L'] [Module R L'] [IsScalarTower R R' L'] (M' : LieModel G (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x) L') (β : L →ₗ[R] L'), (∀ e, (M'.pt (β e)).left = Spec.map (CommRingCat.ofHom (_root_.GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap R R'))) ≫ (M.pt e).left) → IsBaseChange R' β := by
  intro S G _ _ R _ x L _ _ M
  obtain ⟨J, _, f, hf, hch⟩ := Lie.exists_cover (G := G) x
  obtain ⟨h1, h2⟩ := lieModel_finite_projective S G R x J f hf (fun i => (hch i).lieChart) L M
  exact ⟨h1, h2, fun R' _ _ L' _ _ _ _ M' β hβ => Lie.isBaseChange_lie x M R' L' M' β hβ⟩

end PositivityTheory.HtPt.Htat
end
end
