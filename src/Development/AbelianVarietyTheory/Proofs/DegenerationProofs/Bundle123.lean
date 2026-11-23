module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DetCondIffOfFieldExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle005
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle072
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle080
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNormsOfTests
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section

namespace GlobalTheory.FullExtend

open ThetaPtMove

theorem isCoordPt_move {S S' : Scheme.{0}} {f : S' ⟶ S} {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left)
    {P₀ : PolAV S} {P : PolAV S'} {φ : P.A.left ⟶ P₀.A.left}
    (hp : IsGrpPullback P.A P₀.A f φ) (hw : LBIso P.L (P₀.L.pull φ)) {B : Over S} (σ : T.left ⟶ B.left) [IsIso σ]
    (β : B ⟶ T₀) (hβ : σ ≫ β.left = τ) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
    (hg : ∀ th₀, IsGenSec P₀.A P₀.L 1 th₀ → IsGenSec P₀.A P₀.L 1 (VVRank.pullS P₀.A 1 β th₀))
    {k : ℕ} {I : Type} {x : I → (T ⟶ P.A)} {x₀ : I → (T₀ ⟶ P₀.A)} (hx : ∀ i, τ ≫ (x₀ i).left = (x i).left ≫ φ)
    (hk : ∀ i, x i ^ (k ^ 2) = 1) {z : T ⟶ P.A} {z₀ : T₀ ⟶ P₀.A} (hz : τ ≫ z₀.left = z.left ≫ φ)
    {v₀ : I → Γ(T₀.left, ⊤)} (H : IsCoordPt P₀ k x₀ z₀ v₀) :
    IsCoordPt P k x z (fun i => τ.appTop.hom (v₀ i)) := by
  obtain ⟨w, hw⟩ := hw
  have hL₀ := P₀.isLB
  have hL₁ := P.isLB
  have := P.isAb.comm
  obtain ⟨ho, hu, th₀, s₀, α₀, ρ₀, U₀, t₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := H
  obtain ⟨th, hth⟩ := exists_secRel hp τ hτ hw hL₀ hL₁ th₀
  obtain ⟨s, hs⟩ := exists_secRel hp τ hτ hw hL₀ hL₁ s₀
  choose t ht using fun i => exists_secRel hp τ hτ hw hL₀ hL₁ (t₀ i)
  obtain ⟨α, hα, vα⟩ := exists_genThrough₂ hp τ hτ hw hL₀ hL₁ (psi_pow hp τ hτ k) α₀ h₂
  obtain ⟨ρ, hρ, vρ⟩ := ConstFam.exists_gen_through (φ' := fun _ : Fin 1 => z.left) (h := τ) hw hL₀ hL₁
    (fun _ => hz.symm) ρ₀ h₃
  choose U hU hU' using fun i => symLift_move hp τ hτ hw hL₀ hL₁ (hx i) (hk i) (h₅ i)
  exact ⟨ho, (map_natCast τ.appTop.hom k) ▸ hu.map τ.appTop.hom, th, s, α, ρ, U, t,
    isGenSec_move hp τ hτ hw hL₀ hL₁ σ β hβ hth (hg _ h₁), hα, hρ,
    isTwistPull_move hp τ hτ hL₀ hL₁ (psi_pow hp τ hτ k) hα vα hth hs h₄, hU,
    fun i => hU' i _ _ _ _ hs (ht i) (h₆ i), fun i => isValueAt_move hp τ hτ hL₀ hL₁ hz vρ (ht i) (h₇ i)⟩

theorem isGenSec_base (hS : SecBaseChangeSt) {K : Type} [Field K] (P : PolAV (Sp K)) {R : Type} [CommRing R]
    (t : Sp R ⟶ (overRes (T := baseOver (Sp K)) ⊤).left) (th : LB.Sec (LPow P.A P.L 1 (baseOver (Sp K))))
    (h : IsGenSec P.A P.L 1 th) : IsGenSec P.A P.L 1 (VVRank.pullS P.A 1 (homAt t ≫ overResι ⊤) th) := by
  have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  obtain ⟨p₀⟩ : Nonempty (Sp K) := inferInstanceAs (Nonempty (PrimeSpectrum K))
  let i : baseOver (Sp K) ⟶ overRes (T := baseOver (Sp K)) ⊤ := Over.homMk (Sp K).topIso.inv
    ((congrArg (_ ≫ ·) (Category.comp_id _)).trans (Scheme.toIso_inv_ι _))
  have hi : overResι (T := baseOver (Sp K)) ⊤ ≫ i = 𝟙 _ := Over.OverMorphism.ext (Sp K).topIso.hom_inv_id
  have h₁ : IsGenSec P.A P.L 1 (VVRank.pullS P.A 1 (overResι ⊤) th) := fun s => by
    obtain ⟨r, hr⟩ := h (VVRank.pullS P.A 1 i s)
    have e : VVRank.pullM P.A P.L 1 i (SecM.ofSec P.A s) = r • SecM.ofSec P.A th := Subtype.ext (funext hr)
    have := congrArg (VVRank.pullM P.A P.L 1 (overResι ⊤)) e
    rw [VVRank.pullM_comp P.A P.isLB, hi, VVRank.pullM_id P.A P.isLB, LinearMap.map_smulₛₗ] at this
    exact ⟨_, fun j => congrArg (fun q => q.1 j) this⟩
  intro s
  obtain ⟨r, hr⟩ := isGenSec_pullS hS p₀ P t _ h₁ s
  have e := VVRank.pullM_comp P.A P.isLB 1 (homAt t) (overResι ⊤) (SecM.ofSec P.A th)
  exact ⟨r, fun j => (hr j).trans (congrArg (_ * ·) (congrArg (fun q => q.1 j) e))⟩

theorem isCoordPt_fibre (hS : SecBaseChangeSt) {K R : Type} [Field K] [CommRing R] {f : K →+* R} {P₀ : PolAV (Sp K)}
    {P : PolAV (Sp R)} {φ : P.A.left ⟶ P₀.A.left} (h : IsPolFibre f P₀ P φ) {k : ℕ} {I : Type}
    {x : I → (baseOver (Sp R) ⟶ P.A)} {x₀ : I → (baseOver (Sp K) ⟶ P₀.A)}
    (hx : ∀ i, spMap f ≫ (x₀ i).left = (x i).left ≫ φ) (hk : ∀ i, x i ^ (k ^ 2) = 1)
    {z : baseOver (Sp R) ⟶ P.A} {z₀ : baseOver (Sp K) ⟶ P₀.A} (hz : spMap f ≫ z₀.left = z.left ≫ φ)
    {v₀ : I → Γ(Sp K, ⊤)} (H : IsCoordPt P₀ k x₀ z₀ v₀) :
    IsCoordPt P k x z (fun i => (spMap f).appTop.hom (v₀ i)) := by
  let t : Sp R ⟶ (overRes (T := baseOver (Sp K)) ⊤).left := spMap f ≫ (Sp K).topIso.inv
  have ht : t ≫ (⊤ : (Sp K).Opens).ι = spMap f := by
    show (spMap f ≫ (Sp K).topIso.inv) ≫ _ = _
    rw [Category.assoc, Scheme.toIso_inv_ι, Category.comp_id]
  let σ : (baseOver (Sp R)).left ⟶ (baseAt t).left := 𝟙 (Sp R)
  have : IsIso σ := inferInstanceAs (IsIso (𝟙 (Sp R)))
  exact isCoordPt_move (T := baseOver (Sp R)) (T₀ := baseOver (Sp K)) (spMap f) h.2.1 h.2.2.symm σ
    (homAt t ≫ overResι ⊤) ((Category.id_comp _).trans ht) ((Category.comp_id _).trans (Category.id_comp _).symm)
    (isGenSec_base hS P₀ t) hx hk hz H

theorem prim_pull {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {L : LB G.left}
    {L' : LB G'.left} (hL : L.IsLB) (hL' : L'.IsLB) (hw : LBIso (L.pull φ) L') {a : G ⟶ G} {a' : G' ⟶ G'}
    (ha : a'.left ≫ φ = φ ≫ a.left) (H : LBIso L (cubeLB G ![𝟙 G, a] L)) : LBIso L' (cubeLB G' ![𝟙 G', a'] L') := by
  have i₁ := pull_isLB hL φ
  have h₁ : LBIso (L.pull φ) (cubeLB G' ![𝟙 G', a'] (L.pull φ)) := by
    let U := pushPt h.1.w (𝟙 G')
    refine LBIso.chartPull (Geo.Tor.chartPullPull L _ U.left (Category.id_comp _))
      (chartPullLinComb L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) H
    fin_cases i
    · exact (Category.comp_id _).symm
    · exact Over.OverMorphism.ext (ha.trans (congrArg (· ≫ a.left) (Category.id_comp _).symm))
  obtain ⟨w, hw'⟩ := id hw
  exact LBIso.trans hL' (DVR.linComb_isLB _ i₁ _ _) (DVR.linComb_isLB _ hL' _ _)
    (LBIso.trans hL' i₁ (DVR.linComb_isLB _ i₁ _ _) hw.symm h₁) ⟨_, DVR.linCombIso_isGen w hw' _ _⟩

theorem exists_pointMap (hL : Laws) {K K' : Type} [Field K] [IsAlgClosed K] [CharZero K] [Field K'] [IsAlgClosed K']
    {f : K →+* K'} {P : PolAV (Sp K)} {P' : PolAV (Sp K')} {φ : P'.A.left ⟶ P.A.left} (h : IsPolFibre f P P' φ) :
    ∃ r : (baseOver (Sp K) ⟶ P.A) →* (baseOver (Sp K') ⟶ P'.A), (∀ x, (r x).left ≫ φ = spMap f ≫ x.left) ∧
      Function.Injective r ∧ (∀ n : ℕ, 0 < n → ∀ y, y ^ n = 1 → ∃ x, x ^ n = 1 ∧ r x = y) ∧
      ∀ (n : ℤ) x y (c : Kˣ), WeilIs P.A P.L n x y (unitOn c) →
        WeilIs P'.A P'.L n (r x) (r y) (unitOn (Units.map f.toMonoidHom c)) := by
  have := P'.isAb.comm
  obtain ⟨e, he⟩ := LiePull.exists_pushEquiv h.2.1 (baseOver (Sp K')) _ rfl
  let U : Over.mk ((baseOver (Sp K')).hom ≫ spMap f) ⟶ baseOver (Sp K) :=
    Over.homMk (spMap f) ((Category.comp_id _).trans (Category.id_comp _).symm)
  let r : (baseOver (Sp K) ⟶ P.A) →* (baseOver (Sp K') ⟶ P'.A) := e.symm.toMonoidHom.comp (preHom U)
  have hr : ∀ x, (r x).left ≫ φ = spMap f ≫ x.left := fun x =>
    (he _).symm.trans (congrArg (fun q => q.left) (e.apply_symm_apply (U ≫ x)))
  have inj : Function.Injective r := by
    letI := f.toAlgebra
    haveI : Flat (spMap f) := by
      rw [HasRingHomProperty.Spec_iff (P := @Flat)]
      exact (inferInstance : Module.Flat K K')
    haveI : Surjective (spMap f) := ⟨fun p => ⟨(⊥ : PrimeSpectrum K'), Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
    haveI : Epi (spMap f) := Flat.epi_of_flat_of_surjective (spMap f)
    exact fun x y E => Over.OverMorphism.ext ((cancel_epi (spMap f)).1
      ((hr x).symm.trans ((congrArg (fun q => q.left ≫ φ) E).trans (hr y))))
  refine ⟨r, hr, inj, fun n hn y hy => ?_, fun n x y c H => ?_⟩
  · have hk : (n : K) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    have hk' : (n : K') ≠ 0 := by rw [← map_natCast f]; exact (map_ne_zero f).2 hk
    have c₁ := (hL.mulN _ P n hn).2.2.2.2 K (𝟙 _) hk
    have c₂ := (hL.mulN _ P' n hn).2.2.2.2 K' (𝟙 _) hk'
    let F : {x : baseOver (Sp K) ⟶ P.A // x ^ n = 1} → {x : baseOver (Sp K') ⟶ P'.A // x ^ n = 1} :=
      fun x => ⟨r x.1, by rw [← map_pow, x.2, map_one]⟩
    have hF : Function.Injective F := fun a b E => Subtype.ext (inj (congrArg Subtype.val E))
    haveI : Finite {x : baseOver (Sp K') ⟶ P'.A // x ^ n = 1} :=
      Nat.finite_of_card_ne_zero (c₂.trans_ne (by positivity))
    obtain ⟨x, hx⟩ := (hF.bijective_of_nat_card_le (c₂.trans (by rw [h.1]; exact c₁.symm)).le).2 ⟨y, hy⟩
    exact ⟨x.1, x.2, congrArg Subtype.val hx⟩
  · have hu : Units.map U.left.appTop.hom.toMonoidHom (unitOn c) = unitOn (Units.map f.toMonoidHom c) :=
      Units.ext (congrArg (fun q => q.hom (c : K)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))).symm
    refine (weilIs_grpPullback_of_comm' _ _ _ _ _ _ _ _ P.isLB P'.isLB h.2.1 h.2.2.symm _ _ _ _ (U ≫ x) (U ≫ y) _
      (hr x).symm (hr y).symm).2 ?_
    exact hu ▸ CommPairing.weilIs_pull hL.globalFns P.isAb P.isLB U H

theorem fnOf_map {K K' : Type} [Field K] [Field K'] (f : K →+* K') (c : K) :
    fnOf (f c) = (spMap f).appTop.hom (fnOf c) :=
  congrArg (fun q => q.hom c) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))

theorem exists_fullExt (hL : Laws) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {K K' : Type} [Field K] [IsAlgClosed K] [CharZero K] [Field K'] [IsAlgClosed K'] (f : K →+* K') (o : Full D K) :
    letI := H.starRing
    ∃ o' : Full D K', (o'.ρ = f o.ρ ∧ (∀ n, 0 < n → (o'.I.ζ n : K') = f (o.I.ζ n)) ∧
      ∃ φ : o'.P.A.left ⟶ o.P.A.left, IsGrpPullback o'.P.A o.P.A (spMap f) φ ∧ LBIso o'.P.L (o.P.L.pull φ) ∧
        (∀ x, (o'.oa.act x).left ≫ φ = φ ≫ (o.oa.act x).left) ∧
        ∀ n v, 0 < n → (o'.I.ev n v).left ≫ φ = spMap f ≫ (o.I.ev n v).left) ∧
      (∀ m v, o.Theta m v → o'.Theta m fun x => f (v x)) ∧
      ∀ m j z v, o.Coord m (o.I.ev j z) v → o'.Coord m (o'.I.ev j z) fun x => f (v x) := by
  letI := H.starRing
  obtain ⟨P', φ, hφ, hg, hm, hw⟩ := hL.polBaseChange _ _ (spMap f) o.P
  have hp : IsGrpPullback P'.A o.P.A (spMap f) φ := ⟨hφ, fun T x y x₀ y₀ hx hy => by
    obtain rfl : x₀ = toBase hφ.w x := Over.OverMorphism.ext hx
    obtain rfl : y₀ = toBase hφ.w y := Over.OverMorphism.ext hy
    exact congrArg (fun q => q.left) (hm T x y).symm⟩
  have h : IsPolFibre f o.P P' φ := ⟨hg, hp, hw⟩
  obtain ⟨oa, hoa⟩ := polOActPull _ _ _ o.P P' φ hp hw (𝓞 E) o.oa
  obtain ⟨r, hr, inj, onto, weil⟩ := exists_pointMap hL h
  have uinj : Function.Injective (Units.map f.toMonoidHom) := Units.map_injective f.injective
  have hact : ∀ c x, r (x ≫ o.oa.act c) = r x ≫ oa.act c := fun c x => Over.OverMorphism.ext (hφ.hom_ext (by
    rw [hr, Over.comp_left, Over.comp_left, Category.assoc, hoa, ← Category.assoc, ← Category.assoc, hr])
    (by rw [Over.w, Over.w]))
  have tors : ∀ m a, r (o.I.ev (m ^ 2) a) ^ (m ^ 2) = 1 := fun m a => by
    rcases Nat.eq_zero_or_pos (m ^ 2) with e | e
    · rw [e, pow_zero]
    · rw [← map_pow, (o.I.onto _ e _).2 ⟨a, rfl⟩, map_one]
  have det : DetCond D (ofRingAct oa.toRingAct) (𝟙 (Sp K')) (f o.ρ) := fun τ => by
    have q := (detCond_iff_of_field_extension E H D _ _ K K' f (𝟙 _) _ _ o.P.isAb.smooth).2 o.det τ
    have e := fun n => LiePull.lieMult_pull (𝓞 E) _ _ _ _ _ φ (ofRingAct o.oa.toRingAct) (ofRingAct oa.toRingAct) hp hoa
      K' (𝟙 _) τ n
    rw [e, e, Category.id_comp]
    rwa [Category.comp_id] at q
  refine ⟨{ P := P', oa := oa, prim := prim_pull hp o.P.isLB P'.isLB hw (hoa _) o.prim, ρ := f o.ρ
            ρ_sq := by rw [← map_pow, o.ρ_sq, map_neg, map_natCast]
            det := det
            closed := ‹_›
            I := { ζ := fun n => Units.map f.toMonoidHom (o.I.ζ n)
                   ζ_prim := fun n hn => (o.I.ζ_prim n hn).map_of_injective uinj
                   ζ_pow := fun n m hn hm => by rw [← map_pow, o.I.ζ_pow n m hn hm]
                   ev := fun n v => r (o.I.ev n v)
                   add := fun n a b => by rw [o.I.add, map_mul]
                   lin := fun n c a => by rw [o.I.lin, hact]
                   ker := fun n hn a => by rw [← o.I.ker n hn a, map_eq_one_iff r inj]
                   onto := fun n hn z => ⟨fun hz => ?_, ?_⟩
                   tower := fun n m hn hm a => by rw [← map_pow, o.I.tower n m hn hm]
                   isom := fun n hn a b => by rw [← map_zpow]; exact weil _ _ _ _ (o.I.isom n hn a b) } },
    ⟨rfl, fun _ _ => rfl, φ, hp, h.2.2.symm, hoa, fun n v _ => hr _⟩, fun m v Q => ?_, fun m j z v Q => ?_⟩
  · obtain ⟨y, hy, rfl⟩ := onto n hn z hz
    obtain ⟨a, rfl⟩ := (o.I.onto n hn y).1 hy
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    rw [← map_pow, (o.I.onto n hn _).2 ⟨a, rfl⟩, map_one]
  · have q := ConstThetaLevel.isThetaPt_fibre hL.secBaseChange h (fun a => (hr _).symm) (tors m) Q
    simp only [← fnOf_map] at q
    exact q
  · have q := isCoordPt_fibre hL.secBaseChange h (fun a => (hr _).symm) (tors m) (hr (o.I.ev j z)).symm Q
    simp only [← fnOf_map] at q
    exact q

end GlobalTheory.FullExtend

end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
namespace GlobalTheory.Ex.TwNest
section
variable {O : Type} [CommRing O] {N : NumD O} {k : ℕ} (β : N.Form k) (u : Oˣ)

def Mult (t : N.X → Oˣ) (g : N.Gt) (g' : (N.twist β u).Gt) : Prop :=
  g'.b = g.b ∧ ∀ z : N.X, g'.s z = g.s z * t z

variable {β u}

theorem Mult.mul {t t' : N.X → Oˣ} {g h : N.Gt} {g' h' : (N.twist β u).Gt} (a : Mult β u t g g')
    (b : Mult β u t' h h') : Mult β u (fun z => t z * t' z) (g * h) (g' * h') := by
  refine ⟨congrArg₂ (fun x y : N.A => x * y) a.1 b.1, fun z => ?_⟩
  change g'.s z * h'.s z / N.θ (N.c z) g'.b h'.b = g.s z * h.s z / N.θ (N.c z) g.b h.b * (t z * t' z)
  rw [a.1, b.1, a.2, b.2]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div]; abel

theorem Mult.pow {t : N.X → Oˣ} {g : N.Gt} {g' : (N.twist β u).Gt} (a : Mult β u t g g') (n : ℕ) :
    Mult β u (fun z => t z ^ n) (g ^ n) (g' ^ n) := by
  induction n with
  | zero => exact ⟨rfl, fun z => by simp only [pow_zero, _root_.mul_one]; rfl⟩
  | succ n ih => simp only [pow_succ]; exact ih.mul a

theorem qEq_of_twRel {s : Oˣ} {j : ℕ} (hs : s ^ j = u) {p p' : N.QT j} {P P' : (N.twist β u).QT j}
    (a : TwRel β u s p P) (b : TwRel β u s p' P') (h : N.QEq p p') : (N.twist β u).QEq P P' := by
  obtain ⟨z, h1, h2⟩ := h
  refine ⟨z, ?_, ?_⟩
  · rw [a.1, b.1]; exact h1
  · have c : Mult β u (fun w => u ^ β.be z w) (N.io z) ((N.twist β u).io z) := ⟨rfl, fun w => N.twist_τ β u z w⟩
    have d := (show Mult β u (fun w => s ^ β.be p.1.1.toAdd w) p.1.2 P.1.2 from a.2).mul c
    refine NumD.Gt.ext (b.2.1.trans ((congrArg NumD.Gt.b h2).trans d.1.symm)) (funext fun (w : N.X) => ?_)
    refine (b.2.2 w).trans (Eq.trans ?_ (d.2 w).symm)
    rw [h2, h1, map_add (f := _), map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul, zpow_add, zpow_mul,
      zpow_natCast, hs]
end

theorem tx_of_qEq {O : Type} [CommRing O] [TopologicalSpace O] (N : NumD O) {m : ℕ} (hm : Odd m) {p p' : N.QT (m ^ 2)}
    (h : N.QEq p p') : N.tx m p' = N.tx m p := by
  obtain ⟨z, h1, h2⟩ := h
  exact (tsum_congr fun χ => (GlobalTheory.T.thetaConstantTerm_representative_dependence O N m hm p p' χ).1 z h1 h2).trans
    ((Equiv.addRight (m • z)).tsum_eq fun χ => N.txT m p χ)

theorem qEq_pow {O : Type} [CommRing O] (N : NumD O) {La : Type} [AddCommGroup La] {j : ℕ} (q : La → N.QT j)
    (hq : ∀ a b, N.QEq (q a * q b) (q (a + b))) (x : La) (n : ℕ) : N.QEq (q x ^ (n + 1)) (q ((n + 1) • x)) := by
  have E : Equivalence (N.QEq (k := j)) := by
    constructor
    · intro p
      exact ⟨0, by simp, by simp⟩
    · rintro p p' ⟨z, h, h'⟩
      exact ⟨-z, by rw [h, smul_neg, add_neg_cancel_right], by rw [h', N.io_neg, mul_inv_cancel_right]⟩
    · rintro p p' p'' ⟨z, h, h'⟩ ⟨w, e, e'⟩
      exact ⟨z + w, by rw [e, h, smul_add, add_assoc], by rw [e', h', N.io_add, _root_.mul_assoc]⟩
  have qmul : ∀ {p p' q q' : N.QT j}, N.QEq p p' → N.QEq q q' → N.QEq (p * q) (p' * q') := by
    intro p p' q q' ⟨z, h1, h2⟩ ⟨w, h3, h4⟩
    refine ⟨z + w, ?_, ?_⟩
    · change p'.1.1.toAdd + q'.1.1.toAdd = p.1.1.toAdd + q.1.1.toAdd + _
      rw [h1, h3, smul_add]; abel
    · change p'.1.2 * q'.1.2 = p.1.2 * q.1.2 * _
      rw [h2, h4, N.io_add]; exact mul_mul_mul_comm _ _ _ _
  induction n with
  | zero => rw [zero_add, pow_one, one_smul]; exact E.refl _
  | succ n ih =>
    rw [pow_succ, succ_nsmul x (n + 1)]
    exact E.trans (qmul ih (E.refl _)) (hq _ _)
end GlobalTheory.Ex.TwNest

namespace GlobalTheory.Ex

open TwNest in
theorem twist_tx_nest : ∀ (C : Type) [NormedField C] (N : NumD C) (La : Type) [AddCommGroup La] (q : ∀ n : ℕ, La → N.QT n), (∀ n, 0 < n → ∀ a b, N.QEq (q n a * q n b) (q n (a + b))) → (∀ n m, 0 < n → 0 < m → ∀ a (p : N.QT n), p.1.1 = (q (n * m) a).1.1 → p.1.2 = (q (n * m) a).1.2 ^ m → N.QEq p (q n a)) → ∀ (k : ℕ) (β : N.Form k) (u : Cˣ) (r : ℕ → Cˣ), Roots u r → ∀ (n m : ℕ), Odd n → Odd m → ∀ (x : La) (p'' : (N.twist β u).QT ((n * m) ^ 2)) (p : (N.twist β u).QT (m ^ 2)), TwRel β u (r ((n * m) ^ 2)) (q _ (n • x)) p'' → TwRel β u (r (m ^ 2)) (q _ x) p → (N.twist β u).tx (n * m) p'' = (N.twist β u).tx m p := by
  intro C _ N La _ q hadd htow k β u r hr n m hn hm x p'' p h'' h
  have hK : (n * m) ^ 2 = m ^ 2 * n ^ 2 := by ring
  have hm2 : 0 < m ^ 2 := pow_pos hm.pos 2
  have hn2 : 0 < n ^ 2 := pow_pos hn.pos 2
  have hK0 : 0 < (n * m) ^ 2 := pow_pos (hn.mul hm).pos 2
  have hρ : r ((n * m) ^ 2) ^ (n ^ 2) = r (m ^ 2) := by rw [hK]; exact hr.2 _ _ hm2 hn2
  have htow' : ∀ K, K = m ^ 2 * n ^ 2 → ∀ p : N.QT (m ^ 2), p.1.1 = (q K x).1.1 → p.1.2 = (q K x).1.2 ^ (n ^ 2) →
      N.QEq p (q (m ^ 2) x) := by
    rintro _ rfl; exact htow _ _ hm2 hn2 x
  set Y := q ((n * m) ^ 2) x with hY
  obtain ⟨P, hP, -⟩ := existsUnique_twRel β u _ (hr.pow hK0) Y
  have hPm : Mult β u (fun w => r ((n * m) ^ 2) ^ β.be Y.1.1.toAdd w) Y.1.2 P.1.2 := hP.2
  let Y' : N.QT (m ^ 2) := ⟨(Y.1.1, Y.1.2 ^ (n ^ 2)), by
    change (Y.1.2 ^ (n ^ 2)) ^ (m ^ 2) = _
    rw [← pow_mul, ← mul_pow n m 2]; exact Y.2⟩
  let P' : (N.twist β u).QT (m ^ 2) := ⟨(P.1.1, P.1.2 ^ (n ^ 2)), by
    change (P.1.2 ^ (n ^ 2)) ^ (m ^ 2) = _
    rw [← pow_mul, ← mul_pow n m 2]; exact P.2⟩
  have t1 : TwRel β u (r (m ^ 2)) Y' P' := ⟨hP.1, (hPm.pow (n ^ 2)).1, fun w => ((hPm.pow (n ^ 2)).2 w).trans (by
    change (Y.1.2 ^ (n ^ 2)).s w * (_ ^ β.be Y.1.1.toAdd w) ^ (n ^ 2) = (Y.1.2 ^ (n ^ 2)).s w * _ ^ β.be Y.1.1.toAdd w
    rw [← hρ, ← zpow_natCast (_ ^ β.be _ _), ← zpow_natCast (r _), ← zpow_mul, ← zpow_mul, mul_comm (β.be _ _)])⟩
  have t2 : TwRel β u (r ((n * m) ^ 2)) (Y ^ n) (P ^ n) := ⟨congrArg (fun y : Multiplicative N.X => y ^ n) hP.1,
    (hPm.pow n).1, fun w => ((hPm.pow n).2 w).trans (by
      change _ = (Y.1.2 ^ n).s w * _ ^ β.be (n • Y.1.1.toAdd) w
      rw [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul, mul_comm (n : ℤ), zpow_mul, zpow_natCast])⟩
  have e1 : N.QEq Y' (q (m ^ 2) x) := htow' _ hK Y' rfl rfl
  have e2 : N.QEq (Y ^ n) (q ((n * m) ^ 2) (n • x)) := by
    have := qEq_pow N (q ((n * m) ^ 2)) (hadd _ hK0) x (n - 1)
    rwa [Nat.sub_add_cancel hn.pos] at this
  rw [tx_of_qEq _ (hn.mul hm) (qEq_of_twRel (hr.pow hK0) t2 h'' e2), tx_of_qEq _ hm (qEq_of_twRel (hr.pow hm2) t1 h e1)]
  refine tsum_congr fun χ => GlobalTheory.T.degenerationSeriesTerms_nest C _ n m hn hm (P ^ n) P' rfl ?_ χ
  change P.1.2 ^ (n ^ 2) = (P.1.2 ^ n) ^ n
  rw [← pow_mul, sq n]
end GlobalTheory.Ex
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.Ex

theorem exists_complete_isAlgClosed_cExt :
    ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (K : Type) [Field K] [Algebra (FractionRing W) K] [Algebra.IsAlgebraic (FractionRing W) K], ∃ (C : Type) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C) (_ : IsAlgClosed C) (_ : Algebra (FractionRing W) C) (gam : K →+* C), (∀ x, gam (algebraMap (FractionRing W) K x) = algebraMap (FractionRing W) C x) ∧ CExt W (IsLocalRing.maximalIdeal W) C := by
  intro W _ _ _ K _ _ _
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible W
  have hmax : IsLocalRing.maximalIdeal W = Ideal.span {π} := hπ.maximalIdeal_eq
  have hπm : π ∈ IsLocalRing.maximalIdeal W := hmax ▸ Ideal.mem_span_singleton_self π
  obtain ⟨C, i1, i2, i3, i4, i5, h1, h2⟩ :=
    GlobalTheory.exists_complete_isAlgClosed_of_isDiscreteValuationRing W (FractionRing W) hπ.ne_zero hπm
      (r := 1 / 2) (by norm_num) (by norm_num)
  have hle : ∀ r : W, ‖algebraMap (FractionRing W) C (algebraMap W _ r)‖ ≤ 1 :=
    fun r => (h1 _).2 ⟨r, rfl⟩
  let g : K →ₐ[FractionRing W] C := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨C, i1, i2, i3, i4, i5, g.toRingHom, fun x => g.commutes x, hle, fun r hr => ?_⟩
  rw [hmax, Ideal.mem_span_singleton] at hr
  obtain ⟨s, rfl⟩ := hr
  rw [map_mul, map_mul, norm_mul, h2]
  have := hle s
  linarith

end GlobalTheory.Ex
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.NestQVal

attribute [local instance] GlobalTheory.TorusExt.gtGroup


open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField in
open scoped CategoryTheory.Obj BigOperators in
attribute [local instance] Over.cartesianMonoidalCategory in
attribute [local instance] _root_.GlobalTheory.TorusExt.gtGroup in
theorem _root_.GlobalTheory.NestQVal.qval_add_tower : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H), ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ : _root_.ReciprocityTheory.ChartRestriction.G.Out.DegPre R) [Module (𝓞 E) D₀.X] (oa : letI := H.starRing; D₀.OAct (𝓞 E)), D₀.PsiEven → D₀.TauBimult → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (I : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.TateIsoQ D D₀ oa F) (N : _root_.GlobalTheory.Ex.NumD F) (ν : _root_.GlobalTheory.Ex.NumOf D₀ F N) (q : ∀ n : ℕ, D.La → N.QT n), (∀ g, ∃! c, ν.Pt g c) → (∀ g g' g'' c c' c'', ν.Pt g c → ν.Pt g' c' → ν.Pt g'' c'' → (_root_.ReciprocityTheory.ChartRestriction.G.Out.GtPtF.IsAdd g g' g'' ↔ c'' = c * c')) → (∀ k, (∀ p : _root_.ReciprocityTheory.ChartRestriction.G.Out.QkPt D₀ F k, ∃! q, ν.QPt p q) ∧ ∀ (p p' : _root_.ReciprocityTheory.ChartRestriction.G.Out.QkPt D₀ F k) q q', ν.QPt p q → ν.QPt p' q' → (_root_.ReciprocityTheory.ChartRestriction.G.Out.QkPt.Equiv D₀ F p p' ↔ N.QEq q q')) → (∀ n a, ν.QPt (I.ev n a) (q n a)) → (∀ n, 0 < n → ∀ a b, N.QEq (q n a * q n b) (q n (a + b))) ∧ ∀ n m, 0 < n → 0 < m → ∀ a (p : N.QT n), p.1.1 = (q (n * m) a).1.1 → p.1.2 = (q (n * m) a).1.2 ^ m → N.QEq p (q n a) := by
  intro E _ _ _ H D R _ _ D₀ _ oa _ _ F _ _ _ I N ν q hPt hAdd hQ hev

  have hzero : ν.Pt 0 1 := by
    obtain ⟨c, hc, -⟩ := hPt 0
    have h := (hAdd 0 0 0 c c c hc hc hc).1 ((_root_.GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).2 (add_zero 0).symm)
    have : c = 1 := by simpa using (mul_eq_left.1 h.symm)
    simpa [this] using hc
  have hsmul : ∀ (m : ℕ) g c, ν.Pt g c → ν.Pt (m • g) (c ^ m) := by
    intro m g c hc
    induction m with
    | zero => simpa using hzero
    | succ k ih =>
      obtain ⟨c', hc', -⟩ := hPt ((k + 1) • g)
      have h := (hAdd _ _ _ _ _ _ ih hc hc').1 ((_root_.GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).2 (succ_nsmul g k))
      simpa [h, pow_succ] using hc'
  refine ⟨fun n hn a b => ?_, fun n m hn hm a p hp1 hp2 => ?_⟩
  · obtain ⟨r, hry, hrg, hr⟩ := I.add n hn a b
    obtain ⟨hya, hga⟩ := hev n a
    obtain ⟨hyb, hgb⟩ := hev n b
    obtain ⟨c'', hc'', -⟩ := hPt r.g
    have hc := (hAdd _ _ _ _ _ _ hga hgb hc'').1 hrg
    have hrs : ν.QPt r (q n a * q n b) := by
      refine ⟨?_, ?_⟩
      · simp [hry, ← hya, ← hyb]
      · simpa [hc] using hc''
    exact ((hQ n).2 _ _ _ _ hrs (hev n (a + b))).1 hr
  · obtain ⟨Q, hQy, hQg, hQe⟩ := I.tower n m hn hm a
    obtain ⟨hy, hg⟩ := hev (n * m) a
    have hQp : ν.QPt Q p := by
      refine ⟨?_, ?_⟩
      · rw [hQy, ← hy, hp1]
      · rw [(_root_.GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).1 hQg, hp2]
        exact hsmul m _ _ hg
    exact ((hQ n).2 _ _ _ _ hQp (hev n a)).1 hQe

end GlobalTheory.NestQVal
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

theorem _root_.GlobalTheory.T.exists_norms_of_tests : Semi.extend_existsSt.{0} → ∀ (C : Core) (L : C.Law) (T : C.Theta), C.HasTests → T.BTest L → ∃ ν, T.Norms (T.Om L) ν := by
  first | exact @GlobalTheory.ZJ.Core.Theta.exists_norms | exact GlobalTheory.ZJ.Core.Theta.exists_norms | (intros; apply GlobalTheory.ZJ.Core.Theta.exists_norms <;> assumption)
end
