module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaCoordinatesExistUniqueSeparatePoints
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle118
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibre
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle133
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle160
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle127
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle028
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle158
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle161
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle153
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle006
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle038
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusExtensionPointsDivisible
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

theorem _root_.GlobalTheory.T.thetaCoordinates_exist_unique_separate_points : Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (s : Sp K ⟶ S) (m : ℕ), Odd m → (m : K) ≠ 0 → ∀ (Ix : Type) (x : Ix → (Over.mk s ⟶ P.A)), (∀ i, x i ^ m ^ 2 = 1) → (∀ z, ∃ v : Ix → K, IsCoordPt P m x z fun i => fnOf (v i)) ∧ (∀ z (v v' : Ix → K), (IsCoordPt P m x z fun i => fnOf (v i)) → ((IsCoordPt P m x z fun i => fnOf (v' i)) ↔ ∃ c : Kˣ, v' = (c : K) • v)) ∧ (∀ v : Ix → K, (IsThetaPt P m x fun i => fnOf (v i)) ↔ IsCoordPt P m x 1 fun i => fnOf (v i)) ∧ (3 ≤ m → (∀ y : Over.mk s ⟶ P.A, y ^ m ^ 2 = 1 → ∃ i, x i = y) → ∀ z z' (v : Ix → K), (IsCoordPt P m x z fun i => fnOf (v i)) → (IsCoordPt P m x z' fun i => fnOf (v i)) → z = z' ∧ v ≠ 0) := by
  first | exact @GlobalTheory.CoordSep.coord_exists_unique_separate | exact GlobalTheory.CoordSep.coord_exists_unique_separate | (intros; apply GlobalTheory.CoordSep.coord_exists_unique_separate <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section
namespace GlobalTheory.OneBasis.TabMap
open GlobalTheory.FrameGen GlobalTheory.ConstFam GlobalTheory.FrameMove GlobalTheory.OneBasis.Calc

theorem gs_comp {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (q : Y ⟶ X) (z : Z) (U : X.Opens) (h : q (r z) ∈ U) (a : Γ(X, U)) :
    gs (r ≫ q) z U a = (r.stalkMap z).hom (gs q (r z) U a) := by
  rw [← gs_pull r q z U h a, gs_eq r z _ h, gs_eq q (r z) U h]
  exact (Scheme.Hom.germ_stalkMap_apply r _ z h _).symm

section
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A']
  {φ : A'.left ⟶ A.left} {T : Over S} {T' : Over S'} {h : T'.left ⟶ T.left}

theorem exists_ptHom (gp : IsGrpPullback A' A f φ) (hh : h ≫ T.hom = T'.hom ≫ f) :
    ∃ β : (T ⟶ A) →* (T' ⟶ A'), ∀ x, (β x).left ≫ φ = h ≫ x.left := by
  let u : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk h (by simpa using hh)
  let b : (T ⟶ A) → (T' ⟶ A') := fun x =>
    Over.homMk (gp.1.lift (h ≫ x.left) T'.hom (by rw [Category.assoc, Over.w, hh])) (gp.1.lift_snd _ _ _)
  have hb : ∀ x, (b x).left ≫ φ = h ≫ x.left := fun x => gp.1.lift_fst _ _ _
  have key : ∀ x y : T' ⟶ A', x.left ≫ φ = y.left ≫ φ → x = y := fun x y hxy => by
    ext1
    exact gp.1.hom_ext hxy ((Over.w x).trans (Over.w y).symm)
  refine ⟨MonoidHom.mk' b (fun x y => key _ _ ?_), hb⟩
  have hu : ∀ z : T ⟶ A, (u ≫ z).left = (b z).left ≫ φ := fun z => by
    rw [hb]
    rfl
  rw [← gp.2 T' (b x) (b y) (u ≫ x) (u ≫ y) (hu x) (hu y), hb, ← MonObj.comp_mul]
  rfl


omit [GrpObj A] in
theorem sval_all {L : LB A.left} {k : ℤ} {s : LB.Sec (LPow A L k T)} {q : T.left ⟶ (T ⊗ A).left} {p : T.left ⟶ A.left}
    {e : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => p) (fun _ => k))} {c : Γ(T.left, ⊤)}
    (H : ∀ z J, Good L z J → sval (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) s q z J =
      gs (𝟙 _) z ⊤ c * (val e (𝟙 _) z J).val) {Z : Scheme.{0}} (r : Z ⟶ T.left) (z : Z) {J} (hJ : Good L z J) :
    sval (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) s (r ≫ q) z J = gs r z ⊤ c * (val e r z J).val := by
  have hJ' : Good L (r z) (fun ψ => J (r ≫ ψ)) := fun ψ => by
    have := hJ (r ≫ ψ)
    simpa using this
  have H1 := H (r z) (fun ψ => J (r ≫ ψ)) hJ'
  rw [sval_of s q (r z) _ (fun _ => J (r ≫ q ≫ (snd T A).left)) (fun _ => rfl),
    val_of e (𝟙 _) (r z) _ (fun _ => J (r ≫ p)) (fun _ => by simp)] at H1
  have hm := hJ.mem (fun _ : Fin 1 => (snd T A).left) (r ≫ q)
  have hm' := hJ.mem (fun _ : Fin 1 => p) r
  rw [sval_of s (r ≫ q) z J (fun _ => J (r ≫ q ≫ (snd T A).left)) (fun _ => by simp),
    val_of e r z J (fun _ => J (r ≫ p)) (fun _ => rfl)]
  simp only [Category.assoc] at hm
  refine (gs_comp r q z _ hm _).trans ?_
  erw [H1]
  rw [map_mul]
  congr 1
  · have := gs_comp r (𝟙 _) z ⊤ trivial c
    simpa using this.symm
  · erw [← gs_unit r z _ hm', ← gs_unit (𝟙 _) (r z) _ (by simpa using hm')]
    have := gs_comp r (𝟙 _) z (L.wchart (fun _ => p) fun _ => J (r ≫ p)) hm' (e.s fun _ => J (r ≫ p)).val
    rw [Category.comp_id] at this
    exact this.symm
end

section
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {P : PolAV S} {P' : PolAV S'} {φ : P'.A.left ⟶ P.A.left}
  {w : LB.Iso P'.L (P.L.pull φ)} {T : Over S} {T' : Over S'} {h : T'.left ⟶ T.left}

theorem cmb_move (hφ : φ ≫ P.A.hom = P'.A.hom ≫ f) (hh : h ≫ T.hom = T'.hom ≫ f) {k n : ℕ}
    {b : Fin n → LB.Sec (LPow P.A P.L (k : ℤ) T)} {c : Fin n → Γ(T.left, ⊤)} {t : LB.Sec (LPow P.A P.L (k : ℤ) T)}
    {b' : Fin n → LB.Sec (LPow P'.A P'.L (k : ℤ) T')} {t' : LB.Sec (LPow P'.A P'.L (k : ℤ) T')}
    (H : ∀ j, t.f j = ∑ i, liftFun P.A _ (c i) * (b i).f j) (hb : ∀ i, Thru w k h (b i) (b' i)) (ht : Thru w k h t t') :
    ∀ j, t'.f j = ∑ i, liftFun P'.A _ (h.appTop.hom (c i)) * (b' i).f j := by
  have hl : Lin P.A P.L k (𝟙 T) b c t := by
    intro z J hJ
    have e := (cmb_iff P.isLB b c t).1 H _ (𝟙 _) z J hJ
    have hw : ((𝟙 T) ▷ P.A).left = 𝟙 _ := by simp
    rw [hw]
    refine e.trans (Finset.sum_congr rfl fun i _ => ?_)
    congr 1
    rw [Category.id_comp, gs_eq (fst T P.A).left z ⊤ trivial]
    rfl
  exact cmb_of_lin hφ P.isLB P'.isLB hh (h := 𝟙 T) (p := h) (by simp) hl hb ht

theorem frame_move {ρ ρ'} (R : RigPull P'.A P.A f φ w ρ' ρ) {x : T ⟶ P.A} {x' : T' ⟶ P'.A}
    (hx : x'.left ≫ φ = h ≫ x.left) {n : ℕ} {e} (H : IsTorsFrame P ρ n x e) :
    ∃ e', IsTorsFrame P' ρ' n x' e' ∧ ∀ (k : ℕ) (s : LB.Sec (LPow P.A P.L (k : ℤ) T))
      (s' : LB.Sec (LPow P'.A P'.L (k : ℤ) T')) (c : Γ(T.left, ⊤)), Thru w k h s s' →
      (∀ z J, Good P.L z J → sval (φ := fun _ : Fin 1 => (snd T P.A).left) (ε := fun _ => (k : ℤ)) s
        (ptSecT P.A x).left z J = gs (𝟙 _) z ⊤ c * (val (powFrame P.A P.L x e k) (𝟙 _) z J).val) →
      ∀ z J, Good P'.L z J → sval (φ := fun _ : Fin 1 => (snd T' P'.A).left) (ε := fun _ => (k : ℤ)) s'
        (ptSecT P'.A x').left z J = gs h z ⊤ c * (val (powFrame P'.A P'.L x' e' k) (𝟙 _) z J).val := by
  obtain ⟨gp, hw, -, hpm⟩ := R
  obtain ⟨e', he', hv⟩ := exists_gen_through (φ' := fun _ : Fin 1 => x'.left) (φ := fun _ : Fin 1 => x.left) (h := h)
    (ε := fun _ => 1) hw P.isLB P'.isLB (fun _ => hx) e H.2.1
  have ht : ∀ (z : T'.left) J J', Good P.L z J → Good P'.L z J' →
      val e h z J = wVal w z J J' x'.left * val e' (𝟙 _) z J' := by
    intro z J J' hJ hJ'
    have := hv _ (𝟙 _) z J J' hJ hJ'
    simpa using this
  have hr : ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over S')).left) (z : Z) J J', Good P.L z J → Good P'.L z J' →
      rval ρ (r ≫ f) z J = wVal w z J J' (r ≫ eSec P'.A) * rval ρ' r z J' := by
    intro Z r z J J' hJ hJ'
    have := pmaps_val (fun _ => PolBaseChange.eSec_comm gp) hpm r hJ hJ'
    simpa using this
  refine ⟨e', isTorsFrame_move gp hw hr hx H he' ht, ?_⟩
  intro k s s' c hs hval z J' hJ'
  obtain ⟨J, hJ⟩ := exists_good' P.isLB z
  have pf : ∀ {S₀ : Scheme.{0}} {A₀ U : Over S₀} (y : U ⟶ A₀), (ptSecT A₀ y).left ≫ (fst U A₀).left = 𝟙 _ :=
    fun y => by rw [← Over.comp_left, ptSecT, lift_fst]; rfl
  have ps : ∀ {S₀ : Scheme.{0}} {A₀ U : Over S₀} (y : U ⟶ A₀), (ptSecT A₀ y).left ≫ (snd U A₀).left = y.left :=
    fun y => by rw [← Over.comp_left, ptSecT, lift_snd]
  have c1 : (h ≫ (ptSecT P.A x).left) ≫ (fst T P.A).left = (ptSecT P'.A x').left ≫ (fst T' P'.A).left ≫ h := by
    rw [Category.assoc, pf, ← Category.assoc, pf, Category.comp_id, Category.id_comp]
  have c2 : (h ≫ (ptSecT P.A x).left) ≫ (snd T P.A).left = (ptSecT P'.A x').left ≫ (snd T' P'.A).left ≫ φ := by
    rw [Category.assoc, ps, ← Category.assoc, ps, hx]
  have h1 := hs _ (ptSecT P'.A x').left (h ≫ (ptSecT P.A x).left) c1 c2 z J J' hJ hJ'
  have h2 := sval_all hval h z hJ
  rw [ps] at h1
  rw [h1, val_powFrame, ht z J J' hJ hJ'] at h2
  rw [val_powFrame]
  simp only [zpow_natCast, Units.val_mul, Units.val_pow_eq_pow_val] at h2 ⊢
  apply ((wVal w z J J' x'.left).isUnit.pow k).mul_left_cancel
  rw [h2]
  ring
end

theorem tab_map : LL → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CharZero R] [CommRing R'] [IsDomain R'] (gam : FractionRing R →+* FractionRing R') (A : PolAV (Sp (FractionRing R))) (A' : PolAV (Sp (FractionRing R'))) (ψ : A'.A.left ⟶ A.A.left) (ω : LB.Iso A'.L (A.L.pull ψ)) ρ ρ', RigPull A'.A A.A (spMap gam) ψ ω ρ' ρ → ∀ (F F' : Type) [Field F] [Field F'] [IsAlgClosed F] [IsAlgClosed F'] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F'] (σ : F →+* F'), (∀ x, σ (algebraMap (FractionRing R) F x) = algebraMap (FractionRing R') F' (gam x)) → ∀ (m r : ℕ) (th : SecA A F 1) (th' : SecA A' F' 1) (τ : Fin r → SecA A F (m ^ 2)) (τ' : Fin r → SecA A' F' (m ^ 2)), Thru ω 1 (T' := TFK (R := R') F') (T := TFK (R := R) F) (spMap σ) th th' → (∀ i, Thru ω (m ^ 2) (T' := TFK (R := R') F') (T := TFK (R := R) F) (spMap σ) (τ i) (τ' i)) → Tab.Map σ (tab ρ m th τ) (tab ρ' m th' τ') := by
  intro hLL R R' _ _ _ _ _ gam A A' ψ ω ρ ρ' hR F F' _ _ _ _ _ _ σ hσ m r th th' τ τ' hth hτ
  have gp := hR.1
  have hw := hR.2.1
  have hφ : ψ ≫ A.A.hom = A'.A.hom ≫ spMap gam := gp.1.w
  have hh : spMap σ ≫ (TFK (R := R) F).hom = (TFK (R := R') F').hom ≫ spMap gam := by
    show spMap σ ≫ spMap (algebraMap (FractionRing R) F) = spMap (algebraMap (FractionRing R') F') ≫ spMap gam
    rw [← spMap_comp, ← spMap_comp]
    congr 1
    exact RingHom.ext hσ
  obtain ⟨β, hβ⟩ := exists_ptHom (T := TFK (R := R) F) (T' := TFK (R := R') F') (h := spMap σ) gp hh
  have thru : ∀ (k : ℕ) (s : SecA A F k), ∃ s' : SecA A' F' k,
      Thru ω k (T' := TFK (R := R') F') (T := TFK (R := R) F) (spMap σ) s s' :=
    fun k s => (existsUnique_thru hφ hw A.isLB A'.isLB hh s).exists
  refine ⟨β, ?_, ?_, ?_, ?_⟩
  · intro k y₁ hk hy₁
    obtain ⟨y, rfl⟩ : ∃ y : TFK (R := R') F' ⟶ A'.A, y = y₁ := ⟨y₁, rfl⟩
    have hy : y ^ k = 1 := hy₁
    have hk0 : (k : F) ≠ 0 := by
      rw [← map_natCast (algebraMap (FractionRing R) F), ← map_natCast (algebraMap R (FractionRing R))]
      intro h0
      rw [map_eq_zero_iff _ (algebraMap (FractionRing R) F).injective,
        map_eq_zero_iff _ (IsFractionRing.injective R (FractionRing R))] at h0
      exact (Nat.cast_ne_zero.2 (by omega : k ≠ 0)) h0
    have hz : (y.left ≫ ψ) ≫ A.A.hom = spMap σ ≫ (TFK (R := R) F).hom := by
      rw [Category.assoc, hφ, ← Category.assoc, Over.w, hh]
    let zt : Over.mk (spMap σ ≫ (TFK (R := R) F).hom) ⟶ A.A := Over.homMk (y.left ≫ ψ) hz
    have hzy : y.left ≫ ψ = 𝟙 (TFK (R := R') F').left ≫ zt.left := by simp [zt]
    have hzk : zt ^ k = 1 := by
      have e1 := pow_comm gp hzy k
      have e0 := pow_comm gp hzy 0
      rw [hy] at e1
      simp only [pow_zero] at e0
      ext1
      have := e1.symm.trans e0
      erw [Category.id_comp, Category.id_comp] at this
      exact this
    obtain ⟨x, hxk, hxz⟩ := (GlobalTheory.torsion_points_field_extension hLL.1 _ A F F' σ (TFK (R := R) F).hom).2 k zt hk0 hzk
    refine ⟨x, hxk, ?_⟩
    apply Over.OverMorphism.ext
    apply gp.1.hom_ext
    · refine (hβ x).trans ?_
      have := congrArg CommaMorphism.left hxz
      simpa [zt] using this
    · exact (Over.w (β x)).trans (Over.w y).symm
  · rintro x a ⟨hx, t, c, hc, hcmb⟩
    obtain ⟨t', ht'⟩ := thru _ t
    refine ⟨(map_pow β x _).symm.trans ((congrArg β hx).trans (map_one β)), t', σ c,
      ThMove.thC_move R R' gam A A' ψ ω ρ ρ' hR F F' σ hσ m th th' x (β x) t t' c (hβ x) hth ht' hc, ?_⟩
    intro j
    rw [cmb_move hφ hh hcmb hτ ht' j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show (spMap σ).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (a i)) =
      (Scheme.ΓSpecIso (CommRingCat.of F')).inv.hom (σ (a i)) from appTop_fnR σ (a i)]
    rfl
  · rintro k x c ⟨hx, t, hc⟩
    obtain ⟨t', ht'⟩ := thru _ t
    exact ⟨(map_pow β x _).symm.trans ((congrArg β hx).trans (map_one β)), t',
      ThMove.thC_move R R' gam A A' ψ ω ρ ρ' hR F F' σ hσ k th th' x (β x) t t' c (hβ x) hth ht' hc⟩
  · rintro k x l ⟨e, he, hv⟩
    obtain ⟨e', he', hmv⟩ := frame_move hR (hβ x) he
    refine ⟨e', he', fun j z J' hJ' => ?_⟩
    have := hmv (m ^ 2) (τ j) (τ' j) (fnR (l j)) (hτ j) (hv j) z J' hJ'
    erw [gs_spMap] at this
    exact this

end GlobalTheory.OneBasis.TabMap
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT


theorem _root_.GlobalTheory.T.exists_generator_thetaConstants_over_algClosedExtensions : Laws → Laws2 → ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (x₀ : Sp K ⟶ S) (P : PolAV (Sp K)) (φ : P.A.left ⟶ G.left), IsGrpPullback P.A G x₀ φ → LBIso P.L (L.pull φ) → ∀ (m : ℕ), Odd m → ∀ (Ix : Type) (x : Ix → (baseOver (Sp K) ⟶ P.A)) (v : Ix → K), (∀ y, y ^ (m ^ 2) = 1 ↔ ∃ i, x i = y) → IsThetaPt P m x (fun i => fnOf (v i)) → ∃ th : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk x₀)), IsGenSec G L ((1 : ℕ) : ℤ) th ∧ ∀ (F : Type) [Field F] [IsAlgClosed F] (e : K →+* F) (x' : Sp F ⟶ S) (h : spMap e ≫ x₀ = x') (a : F) (th' : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk x'))), SecM.ofSec G th' = @id Γ((Over.mk x').left, ⊤) (fnOf a) • SecM.ofSec G (VVRank.pullS G _ (Over.homMk (spMap e) h : Over.mk x' ⟶ Over.mk x₀) th) → (∀ i, ∃ z, ThG G L ρ m th' z (fnOf (a * e (v i)))) ∧ ∀ z (c : F), ThG G L ρ m th' z (fnOf c) → ∃ i, c = a * e (v i) := by
  first | exact @GlobalTheory.Ex.OneGen.exists_gen_thG_generic | exact GlobalTheory.Ex.OneGen.exists_gen_thG_generic | (intros; apply GlobalTheory.Ex.OneGen.exists_gen_thG_generic <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenericIso

theorem isDominant_of_flat {X Y : Scheme.{0}} [IsIntegral Y] (f : X ⟶ Y) [Flat f] [Nonempty X] : IsDominant f := by
  have h : genericPoint Y ∈ Set.range f :=
    (Flat.generalizingMap f).stableUnderGeneralization_range (genericPoint_specializes (f (Classical.arbitrary X)))
      ⟨_, rfl⟩
  refine ⟨?_⟩
  rw [DenseRange, dense_iff_closure_eq, ← Set.univ_subset_iff, ← (genericPoint_spec Y).def]
  exact closure_mono (Set.singleton_subset_iff.2 h)

theorem nonempty_pullback_generic {R : Type} [CommRing R] [IsDomain R] {T X : Scheme.{0}} (g : T ⟶ X)
    (p : X ⟶ Spec (CommRingCat.of R)) [Flat g] [Flat p] (t : T) :
    Nonempty ↥(pullback g (pullback.fst p (jK R))) := by
  let ξ : Spec (CommRingCat.of (FractionRing R)) := IsLocalRing.closedPoint (FractionRing R)
  have hs : jK R ξ ⤳ (g ≫ p) t := (PrimeSpectrum.le_iff_specializes _ _).1 fun a ha => by
    have h₁ : algebraMap R (FractionRing R) a ∈ IsLocalRing.maximalIdeal (FractionRing R) := ha
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at h₁
    obtain rfl : a = 0 := IsFractionRing.injective R (FractionRing R) (h₁.trans (map_zero _).symm)
    exact Ideal.zero_mem _
  obtain ⟨b, hb⟩ := (Flat.generalizingMap (g ≫ p)).stableUnderGeneralization_range hs ⟨t, rfl⟩
  obtain ⟨y, hy, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := jK R) (g b) ξ hb
  obtain ⟨z, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := g) (g := pullback.fst p (jK R)) b y hy.symm
  exact ⟨z⟩

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D' : DegData R I}
  {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G G' : Over (Spec (CommRingCat.of R))}
  [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] {U : Unif I D A G} {U' : Unif I D' A' G'}
  {hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre} {j : ∀ e : ℕ, thickObj R I e G' ≅ thickObj R I e G}
  {Φ : (Over.pullback (jK R)).obj G' ≅ (Over.pullback (jK R)).obj G}
  {w : LB.Iso (U'.LG.L.pull (pullback.fst G'.hom (jK R))) (U.LG.L.pull (Φ.hom.left ≫ pullback.fst G.hom (jK R)))}

theorem GenericRel.point (hL : Laws) (hR : AdmBase R I) (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    (hE : Enough U.toUnifPre U'.toUnifPre hD j) (hw : GenericRel U.toUnifPre U'.toUnifPre hD j Φ w)
    {B : Type} [CommRing B] [Algebra R B] {g' : Spec (CommRingCat.of B) ⟶ G'.left}
    {g : Spec (CommRingCat.of B) ⟶ G.left} {jL : U.LG.L.ι} {jL' : U'.LG.L.ι}
    (hB : IsAdicComplete (I.map (algebraMap R B)) B)
    (h₁ : g' ≫ G'.hom = Spec.map (CommRingCat.ofHom (algebraMap R B)))
    (h₂ : g ≫ G.hom = Spec.map (CommRingCat.ofHom (algebraMap R B)))
    (h₃ : ⊤ ≤ g' ⁻¹ᵁ U'.LG.L.U jL') (h₄ : ⊤ ≤ g ⁻¹ᵁ U.LG.L.U jL)
    (h₅ : ∀ (e : ℕ) (Z : Scheme.{0}) (ρ : Z ⟶ Spec (CommRingCat.of B)) (r : Z ⟶ (thickObj R I e G').left),
      r ≫ (fstG I e G').left = ρ ≫ g' → r ≫ (j e).hom.left ≫ (fstG I e G).left = ρ ≫ g)
    {Z : Scheme.{0}} (ρ : Z ⟶ Spec (CommRingCat.of B)) (r : Z ⟶ ((Over.pullback (jK R)).obj G').left)
    (hr : r ≫ pullback.fst G'.hom (jK R) = ρ ≫ g') : r ≫ Φ.hom.left ≫ pullback.fst G.hom (jK R) = ρ ≫ g := by
  have c : (ρ ≫ g) ≫ G.hom = (r ≫ pullback.snd G'.hom (jK R)) ≫ jK R := by
    rw [Category.assoc, h₂, ← h₁, ← Category.assoc, ← hr, Category.assoc, Category.assoc, pullback.condition]
  obtain ⟨f₂, e₁, e₂⟩ : ∃ f₂ : Z ⟶ ((Over.pullback (jK R)).obj G).left, f₂ ≫ pullback.fst G.hom (jK R) = ρ ≫ g ∧
      f₂ ≫ pullback.snd G.hom (jK R) = r ≫ pullback.snd G'.hom (jK R) :=
    ⟨pullback.lift _ _ c, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  rw [← e₁, ← Category.assoc]
  refine congrArg (· ≫ _) (GlobalTheory.hom_ext_of_integral_ratios hL R I D A G U
    (fun k σ => ∃ σ', AgreeAll U.toUnifPre U'.toUnifPre hD j k σ σ') (fun k hk σ₀ => ?_) Z _ _ ?_ fun z => ?_)
  · obtain ⟨c, σ', σ, h⟩ := (hE k hk).1 σ₀
    exact ⟨c, σ, h.1, h.2.1, σ', h.2.2⟩
  · rw [e₂, Category.assoc]
    exact congrArg (r ≫ ·) (Over.w Φ.hom)
  · obtain ⟨i, hi⟩ := exists_chart U.LG.isLB ((r ≫ Φ.hom.left ≫ pullback.fst G.hom (jK R)) z)
    have hi' : (r ≫ pullback.fst G'.hom (jK R)) z ∈ U'.LG.L.U jL' := by rw [hr]; exact h₃ (Set.mem_univ (ρ z))
    rw [Category.assoc, e₁]
    refine ⟨i, jL, hi, h₄ (Set.mem_univ (ρ z)), ?_⟩
    rintro k hk σ τ ⟨σ', hσ⟩ ⟨τ', hτ⟩
    have x := GlobalTheory.GenericIso.cross_identity R I hR D D' A A' G G' hG hG' U U' hD j B g' g jL jL' hB h₁ h₃ h₄ h₅ k σ τ σ' τ' hσ hτ Z ρ z
    rw [hw.2 k hk σ' σ hσ Z r z i jL' hi hi', hw.2 k hk τ' τ hτ Z r z i jL' hi hi', hr, _root_.mul_assoc,
      _root_.mul_assoc]
    exact congrArg _ ((mul_comm _ _).trans (x.symm.trans (mul_comm _ _)))

theorem GenericRel.comm (hL : Laws) (hR : AdmBase R I) (hI : I ≠ ⊤) (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    (hj : LevelIso U.toUnifPre U'.toUnifPre hD j)
    (hE : Enough U.toUnifPre U'.toUnifPre hD j) (hw : GenericRel U.toUnifPre U'.toUnifPre hD j Φ w)
    (a' : G' ⟶ G') (a : G ⟶ G) (ha : ∀ e, (Over.pullback (thick R I e)).map a' ≫ (j e).hom =
      (j e).hom ≫ (Over.pullback (thick R I e)).map a) :
    (Over.pullback (jK R)).map a' ≫ Φ.hom = Φ.hom ≫ (Over.pullback (jK R)).map a := by
  have := hR.1
  have := U'.smooth
  have := U.separated
  have P : ∀ {S : Scheme.{0}} (t : S ⟶ Spec (CommRingCat.of R)) {X Y : Over (Spec (CommRingCat.of R))} (c : X ⟶ Y),
      ((Over.pullback t).map c).left ≫ pullback.fst Y.hom t =
        pullback.fst X.hom t ≫ c.left := fun e _ _ c => pullback.lift_fst _ _ _
  have : Nontrivial (R ⧸ I ^ (0 + 1)) := Ideal.Quotient.nontrivial_iff.2 (by rwa [zero_add, pow_one])
  let x : (thickObj R I 0 G').left := eSec (thickObj R I 0 G') (Classical.arbitrary (PrimeSpectrum (R ⧸ I ^ (0 + 1))))
  obtain ⟨i₁, m₁⟩ := exists_chart U.LG.isLB ((fstG I 0 G).left ((j 0).hom.left x))
  obtain ⟨i₂, m₂⟩ := exists_chart U.LG.isLB (a.left ((fstG I 0 G).left ((j 0).hom.left x)))
  obtain ⟨i₁', m₁'⟩ := exists_chart U'.LG.isLB ((fstG I 0 G').left x)
  obtain ⟨i₂', m₂'⟩ := exists_chart U'.LG.isLB (a'.left ((fstG I 0 G').left x))
  obtain ⟨B, _, _, g', g, hB, -, hf, ⟨b, -⟩, h₁, h₂, h₃, h₄, h₅⟩ := CompletedPoint.exists_completed_point I G G'
    (fun e => (j e).hom) (fun e => (hj e).2.1) x (U.LG.L.U i₁ ⊓ a.left ⁻¹ᵁ U.LG.L.U i₂)
    (U'.LG.L.U i₁' ⊓ a'.left ⁻¹ᵁ U'.LG.L.U i₂') ⟨m₁, m₂⟩ ⟨m₁', m₂'⟩
  have h₆ : ∀ (e : ℕ) (Z : Scheme.{0}) (ρ : Z ⟶ Spec (CommRingCat.of B)) (r : Z ⟶ (thickObj R I e G').left),
      r ≫ (fstG I e G').left = ρ ≫ g' ≫ a'.left → r ≫ (j e).hom.left ≫ (fstG I e G).left = ρ ≫ g ≫ a.left := by
    intro e Z ρ r hr
    have hr' : r ≫ pullback.fst G'.hom (thick R I e) = ρ ≫ g' ≫ a'.left := hr
    have c : (ρ ≫ g') ≫ G'.hom = (r ≫ pullback.snd G'.hom (thick R I e)) ≫ thick R I e := by
      rw [Category.assoc _ (pullback.snd _ _), ← pullback.condition, ← Category.assoc r, hr']
      simp only [Category.assoc, Over.w]
    obtain ⟨r₀, e₁, e₂⟩ : ∃ r₀ : Z ⟶ (thickObj R I e G').left, r₀ ≫ pullback.fst G'.hom (thick R I e) = ρ ≫ g' ∧
        r₀ ≫ pullback.snd G'.hom (thick R I e) = r ≫ pullback.snd G'.hom (thick R I e) :=
      ⟨pullback.lift _ _ c, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    obtain rfl : r = r₀ ≫ ((Over.pullback (thick R I e)).map a').left := by
      refine pullback.hom_ext ?_ ?_
      · rw [hr', Category.assoc, P, ← Category.assoc r₀, e₁, Category.assoc]
      · rw [← e₂, Category.assoc]
        exact congrArg (r₀ ≫ ·) (Over.w ((Over.pullback (thick R I e)).map a')).symm
    have e₃ := congrArg (· ≫ a.left) (h₅ e Z ρ r₀ e₁)
    have e₄ := congrArg (fun q => r₀ ≫ q.left ≫ pullback.fst G.hom (thick R I e)) (ha e)
    simp only [Over.comp_left, Category.assoc, P] at e₃ e₄ ⊢
    exact e₄.trans e₃
  have := (unifPre_genericFibre_surjective_appTop_and_isIntegral hL.globalFns R I D' A' G' U'.toUnifPre).2
  have := nonempty_pullback_generic g' G'.hom b
  have := isDominant_of_flat (pullback.snd g' (pullback.fst G'.hom (jK R)))
  have p₁ := hw.point hL hR hG hG' hE hB h₁ h₂ (fun y hy => (h₃ hy).1) (fun y hy => (h₄ hy).1) h₅
    (pullback.fst g' (pullback.fst G'.hom (jK R))) (pullback.snd g' (pullback.fst G'.hom (jK R)))
    pullback.condition.symm
  have p₂ := hw.point hL hR hG hG' hE (g' := g' ≫ a'.left) (g := g ≫ a.left) hB
    (by rw [Category.assoc, Over.w, h₁]) (by rw [Category.assoc, Over.w, h₂]) (fun y hy => (h₃ hy).2)
    (fun y hy => (h₄ hy).2) h₆ (pullback.fst g' (pullback.fst G'.hom (jK R)))
    (pullback.snd g' (pullback.fst G'.hom (jK R)) ≫ ((Over.pullback (jK R)).map a').left)
    (by rw [Category.assoc, P, ← Category.assoc, ← pullback.condition, Category.assoc])
  refine Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated (X := pullback G'.hom (jK R))
    (pullback.snd G.hom (jK R)) ((Over.w _).trans (Over.w _).symm)
    (pullback.snd g' (pullback.fst G'.hom (jK R))) (pullback.hom_ext ?_ ?_))
  · have e₃ := congrArg (· ≫ a.left) p₁
    simp only [Over.comp_left, Category.assoc, P] at e₃ p₂ ⊢
    exact p₂.trans e₃.symm
  · rw [Category.assoc, Category.assoc]
    exact congrArg (_ ≫ ·) ((Over.w _).trans (Over.w _).symm)

theorem GenericRel.one (hL : Laws) (hR : AdmBase R I) (hI : I ≠ ⊤) (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    (hj : LevelIso U.toUnifPre U'.toUnifPre hD j)
    (hE : Enough U.toUnifPre U'.toUnifPre hD j) (hw : GenericRel U.toUnifPre U'.toUnifPre hD j Φ w) :
    η[(Over.pullback (jK R)).obj G'] ≫ Φ.hom = η[(Over.pullback (jK R)).obj G] := by
  letI : (Over.pullback (jK R)).Monoidal := (Over.instBraidedPullback (f := jK R)).toMonoidal
  have h := hw.comm hL hR hI hG hG' hj hE 1 1 fun e => by
    letI : (Over.pullback (thick R I e)).Monoidal := (Over.instBraidedPullback (f := thick R I e)).toMonoidal
    have := (hj e).1
    rw [Functor.map_one, Functor.map_one, MonObj.comp_one, MonObj.one_comp]
  rw [Functor.map_one, Functor.map_one, MonObj.comp_one] at h
  have e := congrArg (η[(Over.pullback (jK R)).obj G'] ≫ ·) h
  simp only [← Category.assoc, MonObj.comp_one] at e
  simpa [Hom.one_def] using e

end GlobalTheory.GenericIso
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.kTriv_of_closed_fibre_localRing : Laws → Laws2 → ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (B : Over (Spec (CommRingCat.of A))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ N : LB B.left, N.IsLB → RelAmple B N → KTriv ((Over.pullback (spMap (IsLocalRing.residue A))).obj B) (N.pull (pullback.fst B.hom (spMap (IsLocalRing.residue A)))) → KTriv B N := by
  first | exact @GlobalTheory.KTrivLocal.kTriv_of_closed_fibre | exact GlobalTheory.KTrivLocal.kTriv_of_closed_fibre | (intros; apply GlobalTheory.KTrivLocal.kTriv_of_closed_fibre <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.torusExtension_points_divisible' : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G], Nonempty (TorusExtension G) → ∀ (n : ℕ), 1 ≤ n → ∀ y : (𝟙_ (Over (Sp k)) ⟶ G), ∃ x : (𝟙_ (Over (Sp k)) ⟶ G), x ^ n = y := by
  first | exact @GlobalTheory.SS.torusExtension_points_divisible | exact GlobalTheory.SS.torusExtension_points_divisible | (intros; apply GlobalTheory.SS.torusExtension_points_divisible <;> assumption)
end
