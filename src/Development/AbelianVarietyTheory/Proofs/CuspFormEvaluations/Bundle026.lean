module

public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle023
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaEmbeddingSectionsBaseChangeAffine
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsNonvanishing
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle024
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle024
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle018
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointsLiftToLevelCover
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle025
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle007
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace GenBaseChange

open VVRank EmbPull TopologicalSpace

variable {S : Scheme.{0}} (P : PolAV S) {T T' : Over S}

theorem isGenSec_pullS (hS : SecBaseChangeSt) [IsLocallyNoetherian S] [IsAffine T.left] [IsAffine T'.left] (h : T' ⟶ T)
    {th : LB.Sec (LPow P.A P.L 1 T)} (H : IsGenSec P.A P.L 1 th) : IsGenSec P.A P.L 1 (pullS P.A 1 h th) := by
  intro s
  let I : Ideal Γ(T'.left, ⊤) := (Submodule.span Γ(T'.left, ⊤)
    {pullM P.A P.L 1 h (SecM.ofSec P.A th)}).comap (LinearMap.toSpanSingleton _ _ (SecM.ofSec P.A s))
  have key : ∀ p : T'.left, ∃ f ∈ I, p ∈ T'.left.basicOpen f := fun p => by
    obtain ⟨V, hV, b, hb⟩ := hS S P 1 le_rfl (T.hom (h.left p))
    have hq : Unique (Fin (1 ^ P.g)) := by rw [one_pow]; infer_instance
    obtain ⟨f, hf, hp⟩ := (isAffineOpen_top T.left).exists_basicOpen_le (V := T.hom ⁻¹ᵁ V) ⟨h.left p, hV⟩ trivial
    let f' := h.left.appTop.hom f
    have hf' : h.left ⁻¹ᵁ T.left.basicOpen f = T'.left.basicOpen f' := Scheme.preimage_basicOpen_top _ _
    let W := T.left.basicOpen f
    let W' := T'.left.basicOpen f'
    let l : overRes W ⟶ overRes (T := baseOver S) V := Over.homMk
      (IsOpenImmersion.lift V.ι (W.ι ≫ T.hom) (by
        rw [Scheme.Opens.range_ι]
        rintro _ ⟨y, rfl⟩
        exact hf y.2)) ((congrArg (_ ≫ ·) (Category.comp_id _)).trans (IsOpenImmersion.lift_fac _ _ _))
    let k₀ : W'.toScheme ⟶ W.toScheme := IsOpenImmersion.lift W.ι (W'.ι ≫ h.left) (by
        rw [Scheme.Opens.range_ι]
        rintro _ ⟨y, rfl⟩
        exact hf'.ge y.2)
    have hk₀ : k₀ ≫ W.ι = W'.ι ≫ h.left := IsOpenImmersion.lift_fac _ _ _
    let k : overRes W' ⟶ overRes W := Over.homMk k₀ (by
      change k₀ ≫ W.ι ≫ T.hom = W'.ι ≫ T'.hom
      rw [← Category.assoc, hk₀, Category.assoc, Over.w])
    have hk : k ≫ overResι W = overResι W' ≫ h := Over.OverMorphism.ext hk₀
    have hW' : IsAffineOpen W' := (isAffineOpen_top _).basicOpen f'
    have : IsAffine (overRes W').left := hW'
    obtain ⟨c, hc⟩ := exists_basis P 1 b hb (overRes W') (k ≫ l)
    obtain ⟨n, u, hu⟩ := exists_pow_extend_secM P 1 f (pullM P.A P.L 1 l (SecM.ofSec P.A (b hq.default)))
    obtain ⟨r, hr⟩ := H (SecM.toSec P.A u)
    have hr' : u = r • SecM.ofSec P.A th := Subtype.ext (funext hr)
    have e₁ := congrArg (pullM P.A P.L 1 k) hu
    rw [LinearMap.map_smulₛₗ, pullM_comp _ P.isLB, pullM_comp _ P.isLB, hk, ← pullM_comp _ P.isLB, hr',
      LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ] at e₁
    have e₂ : k.left.appTop.hom ((overResι W).left.appTop.hom (f ^ n)) = (overResι W').left.appTop.hom (f' ^ n) :=
      (congrArg (fun q => q.left.appTop.hom (f ^ n)) hk).trans
        (congrArg (overResι W').left.appTop.hom (map_pow h.left.appTop.hom f n))
    rw [e₂] at e₁
    obtain ⟨d, hd⟩ : ∃ d : Γ((overRes W').left, ⊤), pullM P.A P.L 1 (overResι W') (SecM.ofSec P.A s) =
        d • pullM P.A P.L 1 (k ≫ l) (SecM.ofSec P.A (b hq.default)) := by
      have := c.sum_repr (pullM P.A P.L 1 (overResι W') (SecM.ofSec P.A s))
      rw [Fintype.sum_unique, hc] at this
      exact ⟨_, this.symm⟩
    obtain ⟨m, d₀, hd₀⟩ : ∃ (m : ℕ) (d₀ : Γ(T'.left, ⊤)), (overResι W').left.appTop.hom d₀ =
        (overResι W').left.appTop.hom (f' ^ m) * d := exists_pow_mul_extend f' d
    obtain ⟨N, hN⟩ := exists_pow_kill_secM P 1 f' ((f' ^ m * f' ^ n) • SecM.ofSec P.A s -
      (d₀ * h.left.appTop.hom r) • pullM P.A P.L 1 h (SecM.ofSec P.A th))
        (map_sub_eq_zero _ _ _ _ _ _ _ _ _ d e₁ hd hd₀)
    refine ⟨f' ^ N * (f' ^ m * f' ^ n), Submodule.mem_span_singleton.2 ⟨f' ^ N * (d₀ * h.left.appTop.hom r), ?_⟩, ?_⟩
    · rw [smul_sub, sub_eq_zero, ← mul_smul, ← mul_smul] at hN
      exact hN.symm
    · have hp' : p ∈ T'.left.basicOpen f' := hf'.le hp
      rw [Scheme.mem_basicOpen_top] at hp' ⊢
      simp only [map_mul, map_pow]
      exact (hp'.pow _).mul ((hp'.pow _).mul (hp'.pow _))
  have hI : Ideal.span (I : Set Γ(T'.left, ⊤)) = ⊤ :=
    (isAffineOpen_top T'.left).self_le_iSup_basicOpen_iff.1 fun p _ => by
      obtain ⟨f, hf, hp⟩ := key p
      exact Opens.mem_iSup.2 ⟨⟨f, hf⟩, hp⟩
  rw [Ideal.span_eq, Ideal.eq_top_iff_one] at hI
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hI
  rw [LinearMap.toSpanSingleton_apply, one_smul] at hr
  exact ⟨r, fun j => (congrArg (fun q => q.1 j) hr).symm⟩

theorem gs_eq_zero {Y : Scheme.{0}} (f a : Γ(Y, ⊤)) (n : ℕ) (h : (Y.basicOpen f).ι.appTop.hom (a * f ^ n) = 0)
    (p : Y) (hp : p ∈ Y.basicOpen f) : gs (𝟙 Y) p ⊤ a = 0 := by
  let z : (Y.basicOpen f).toScheme := ⟨p, hp⟩
  have q := (gs_pull (𝟙 _) (Y.basicOpen f).ι z ⊤ trivial (a * f ^ n)).symm.trans
    ((congrArg (gs (𝟙 _) z _) h).trans (LBGerm.gs_zero _ z _ trivial))
  rw [Category.id_comp] at q
  replace q := (gs_stalkMap (Y.basicOpen f).ι z ⊤ trivial _).symm.trans q
  have q' : gs (𝟙 Y) p ⊤ (a * f ^ n) = 0 := PushInv.stalk_inj (Y.basicOpen f).ι z (q.trans (map_zero _).symm)
  rw [gs_mul _ p ⊤ trivial, LBGerm.gs_pow _ p ⊤ trivial] at q'
  have hu : IsUnit (gs (𝟙 Y) p ⊤ f) := by
    rw [gs_eq _ p ⊤ trivial]
    exact (Scheme.mem_basicOpen_top _ _ _).1 hp
  exact (hu.pow n).mul_left_eq_zero.1 q'

theorem basis_smul_eq_zero {R M κ : Type} [CommRing R] [AddCommGroup M] [Module R M] (c : Module.Basis κ R M) (i : κ)
    (x : R) (h : x • c i = 0) : x = 0 := by
  simpa using congrArg (fun q => c.repr q i) h

theorem eq_zero_of_smul (hS : SecBaseChangeSt) [IsLocallyNoetherian S] [IsAffine T.left]
    {th : LB.Sec (LPow P.A P.L 1 T)} (H : IsGenSec P.A P.L 1 th) (a : Γ(T.left, ⊤))
    (ha : a • (SecM.ofSec P.A th : SecM P.A P.L 1 T) = 0) : a = 0 := by
  refine fn_ext fun p _ => Eq.trans ?_ (LBGerm.gs_zero _ p ⊤ trivial).symm
  obtain ⟨V, hV, b, hb⟩ := hS S P 1 le_rfl (T.hom p)
  have hq : Unique (Fin (1 ^ P.g)) := by rw [one_pow]; infer_instance
  obtain ⟨f, hf, hp⟩ := (isAffineOpen_top T.left).exists_basicOpen_le (V := T.hom ⁻¹ᵁ V) ⟨p, hV⟩ trivial
  let W := T.left.basicOpen f
  let l : overRes W ⟶ overRes (T := baseOver S) V := Over.homMk
    (IsOpenImmersion.lift V.ι (W.ι ≫ T.hom) (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨y, rfl⟩
      exact hf y.2)) ((congrArg (_ ≫ ·) (Category.comp_id _)).trans (IsOpenImmersion.lift_fac _ _ _))
  have hW : IsAffineOpen W := (isAffineOpen_top _).basicOpen f
  have : IsAffine (overRes W).left := hW
  obtain ⟨c, hc⟩ := exists_basis P 1 b hb (overRes W) l
  obtain ⟨n, u, hu⟩ := exists_pow_extend_secM P 1 f (pullM P.A P.L 1 l (SecM.ofSec P.A (b hq.default)))
  obtain ⟨r, hr⟩ := H (SecM.toSec P.A u)
  have hr' : u = r • SecM.ofSec P.A th := Subtype.ext (funext hr)
  have h0 : a • u = 0 := by rw [hr', smul_comm, ha, smul_zero]
  have e := congrArg (pullM P.A P.L 1 (overResι W)) h0
  rw [LinearMap.map_smulₛₗ, map_zero, hu, ← mul_smul, ← map_mul] at e
  have e' : (overResι W).left.appTop.hom (a * f ^ n) • c hq.default = 0 := by
    rw [hc]; exact e
  have e₂ := basis_smul_eq_zero c _ _ e'
  exact gs_eq_zero f a n e₂ p hp

theorem existsUnique_of_isPullSec (hS : SecBaseChangeSt) [IsLocallyNoetherian S] [IsAffine T.left] [IsAffine T'.left]
    (h : T' ⟶ T) {th : LB.Sec (LPow P.A P.L 1 T)} (H : IsGenSec P.A P.L 1 th) {th' : LB.Sec (LPow P.A P.L 1 T')}
    (hp : IsPullSec P.A P.L 1 (h ▷ P.A) (whiskerRight_snd _ _) th th') (s : LB.Sec (LPow P.A P.L 1 T')) :
    ∃! r : Γ(T'.left, ⊤), ∀ j, s.f j = liftFun P.A _ r * th'.f j := by
  have H' : IsGenSec P.A P.L 1 th' := fun s => by
    obtain ⟨r, hr⟩ := isGenSec_pullS P hS h H s
    exact ⟨r, fun j => (hr j).trans (congrArg (_ * ·) (hp j).symm)⟩
  obtain ⟨r, hr⟩ := H' s
  refine ⟨r, hr, fun r' hr' => sub_eq_zero.1 (eq_zero_of_smul P hS H' _ ?_)⟩
  rw [sub_smul, sub_eq_zero]
  exact Subtype.ext (funext fun j => (hr' j).symm.trans (hr j))

theorem toΓ_bijective (R : Type) [CommRing R] : Function.Bijective (toΓ R) :=
  ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv

end GenBaseChange

theorem framedPoint_generator_baseChange :
    Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] (ψ : S →+* T) (y : FrPt Xo c S) (h : ptO Xo (spMap ψ ≫ y.x) ⟶ ptO Xo y.x), h.left = spMap ψ → ∀ s' : LB.Sec (PPx (spMap ψ ≫ y.x)), IsPullSec Xo.univ.t.G Xo.univ.t.PP.L 1 (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) y.s s' → ∀ s'' : LB.Sec (PPx (spMap ψ ≫ y.x)), ∃! a : T, ∀ i, s''.f i = scal (spMap ψ ≫ y.x) a i * s'.f i := by
  intro hL E _ _ _ H Dw l Xo c S T _ _ _ ψ y h _ s' hs' s''
  have := UnivPol.isLocallyNoetherian Xo
  have : IsAffine (ptO Xo y.x).left := inferInstanceAs (IsAffine (Spec _))
  have : IsAffine (ptO Xo (spMap ψ ≫ y.x)).left := inferInstanceAs (IsAffine (Spec _))
  obtain ⟨r, hr, hu⟩ := GenBaseChange.existsUnique_of_isPullSec (UnivPol.pol Xo) hL.secBaseChange h
    (th := y.s) (fun s => by
      obtain ⟨a, ha, -⟩ := y.gen s
      exact ⟨toΓ S a, ha⟩) (th' := s') hs' s''
  obtain ⟨a, rfl⟩ := (GenBaseChange.toΓ_bijective T).2 r
  exact ⟨a, hr, fun a' ha' => (GenBaseChange.toΓ_bijective T).1 (hu _ ha')⟩

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_faithfullyFlat_nthRoots_of_torsion : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x0 : Sp S ⟶ Xo.X) (N k : ℕ), 0 < N → 0 < k → ∀ (J : Type) [Fintype J] (t : J → (ptO Xo x0 ⟶ Xo.univ.t.G)), (∀ i, t i ^ k = 1) → ∃ (B : Type) (_ : CommRing B) (φ : S →+* B) (w : J → (ptO Xo (spMap φ ≫ x0) ⟶ Xo.univ.t.G)), φ.FaithfullyFlat ∧ ∀ i, (w i ^ N).left = spMap φ ≫ (t i).left := by
  first | exact @GlobalTheory.exists_faithfullyFlat_roots | exact GlobalTheory.exists_faithfullyFlat_roots | (intros; apply GlobalTheory.exists_faithfullyFlat_roots <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace IsotropicEnum

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem comp_list_prod {S : Scheme.{0}} {G T T' : Over S} [GrpObj G] (h : T' ⟶ T) (L : List (T ⟶ G)) :
    h ≫ L.prod = (L.map fun x => h ≫ x).prod := by
  induction L with
  | nil => simp [MonObj.comp_one]
  | cons x L ih => simp [MonObj.comp_mul, ih]

theorem inZh_comp (Xo : Moduli Dw l) {n : ℕ} (Λ : GenLat E n) (N : ℕ) {T T' : Over Xo.X} (h : T' ⟶ T)
    {a : Fin n → (T ⟶ Xo.univ.t.G)} (ha : InZh Xo Λ N a) : InZh Xo Λ N (fun b => h ≫ a b) := by
  refine ⟨fun b => ?_, fun mu hmu cm hcm i => ?_⟩
  · rw [← MonObj.comp_pow, ha.1 b, MonObj.comp_one]
  · have h1 := ha.2 mu hmu cm hcm i
    have hl : (List.ofFn fun j => (h ≫ a j) ≫ Xo.univ.t.act.act (cm i j)) =
        (List.ofFn fun j => a j ≫ Xo.univ.t.act.act (cm i j)).map fun y => h ≫ y := by
      simp [List.map_ofFn, Function.comp_def, Category.assoc]
    rw [hl, ← comp_list_prod, h1, MonObj.comp_one]

theorem ev_sum {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}
    (I : TateIso Dw k Q act e) {m : ℕ} (hm : 0 < m) {n : ℕ} (v : Fin n → Dw.La) :
    I.ev m (∑ j, v j) = (List.ofFn fun j => I.ev m (v j)).prod := by

  have h0 : I.ev m 0 = 1 := by
    have h := I.add m 0 0
    rw [add_zero] at h
    exact mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)
  induction n with
  | zero => simp [h0]
  | succ n ih => rw [Fin.sum_univ_succ, I.add, ih (fun j => v j.succ), List.ofFn_succ, List.prod_cons]

theorem exists_eq_of_isAlgClosed (Xo : Moduli Dw l) {K : Type} [Field K] [IsAlgClosed K] (x : Sp K ⟶ Xo.X)
    {n : ℕ} (Λ : GenLat E n) {N : ℕ} (hΛ : Λ.Unimod) (hN : 0 < N)
    (hle : Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La)
    (w : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo x ⟶ Xo.univ.t.G)) (hw : ∀ i, InZh Xo Λ N (w i))
    (hinj : Function.Injective w) (a : Fin n → (ptO Xo x ⟶ Xo.univ.t.G)) (ha : InZh Xo Λ N a) : ∃ i, w i = a := by
  classical
  obtain ⟨-, I, -⟩ := Xo.univ.geom K x (Spec.preimage (x ≫ Xo.s)).hom
    (by simp only [spMap, CommRingCat.ofHom_hom, Spec.map_preimage])
  have hM : 0 < N ^ 2 := pow_pos hN 2

  have evEq : ∀ u u' : Dw.La, Dw.ModN (N ^ 2) (u - u') → I.ev (N ^ 2) u = I.ev (N ^ 2) u' := by
    intro u u' h
    have h1 : I.ev (N ^ 2) (u - u') = 1 := (I.ker _ hM _).2 h
    have h2 := I.add (N ^ 2) (u - u') u'
    rw [sub_add_cancel, h1, _root_.one_mul] at h2
    exact h2

  have key : ∀ c : Fin n → (ptO Xo x ⟶ Xo.univ.t.G), InZh Xo Λ N c →
      ∃ y : Fin n → Dw.La, (∀ (mu : Matrix (Fin n) (Fin n) E), (∀ v ∈ Λ.La, mu.mulVec v ∈ stdLat E n) →
        ∀ cm : Fin n → Fin n → 𝓞 E, (∀ i j, (cm i j : E) = (N : E) * mu i j) →
          ∀ i, Dw.ModN (N ^ 2) (∑ j, cm i j • y j)) ∧ ∀ b, I.ev (N ^ 2) (y b) = c b := by
    intro c hc
    have hy : ∀ b, ∃ y, I.ev (N ^ 2) y = c b := fun b => (I.onto _ hM (c b)).1 (hc.1 b)
    choose y hy using hy
    refine ⟨y, fun mu hmu cm hcm i => ?_, hy⟩
    have h1 := hc.2 mu hmu cm hcm i
    refine (I.ker _ hM _).1 ?_
    have hfun : (fun j => I.ev (N ^ 2) (cm i j • y j)) = fun j => c j ≫ Xo.univ.t.act.act (cm i j) := by
      funext j
      simp only [I.lin, hy]
    rw [ev_sum I hM, hfun]
    exact h1
  obtain ⟨zz, -, -, hcover⟩ := ZCount.exists_class_representatives E H Dw n Λ N hΛ hN hle
  have hf : ∀ i, ∃ j, w i = fun b => I.ev (N ^ 2) (zz j b) := by
    intro i
    obtain ⟨y, hy, hyw⟩ := key (w i) (hw i)
    obtain ⟨j, hj⟩ := hcover y hy
    refine ⟨j, funext fun b => ?_⟩
    rw [← hyw b]
    exact evEq _ _ (hj b)
  choose f hf using hf

  have finj : Function.Injective f := by
    intro i i' h
    apply hinj
    rw [hf i, hf i', h]
  have fsurj : Function.Surjective f := Finite.surjective_of_injective finj
  obtain ⟨y, hy, hya⟩ := key a ha
  obtain ⟨j, hj⟩ := hcover y hy
  obtain ⟨i, rfl⟩ := fsurj j
  refine ⟨i, ?_⟩
  rw [hf i]
  funext b
  rw [← hya b]
  exact (evEq _ _ (hj b)).symm

end IsotropicEnum


open IsotropicEnum in
theorem isotropic_enumeration_onto_of_isLocalRing :
    Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (T : Type) [CommRing T] [IsLocalRing T] (x0 : Sp T ⟶ Xo.X) (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → 0 < N → Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La → ∀ z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo x0 ⟶ Xo.univ.t.G), (∀ i, InZh Xo Λ N (z i)) → GeoInj Xo x0 z → (∀ a, InZh Xo Λ N a → ∃ i, z i = a) ∧ ∀ z' : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo x0 ⟶ Xo.univ.t.G), (∀ i, InZh Xo Λ N (z' i)) → GeoInj Xo x0 z' → ∃ σ : Equiv.Perm (Fin (Λ.zCard N (Dw.p + Dw.q))), ∀ i, z' i = z (σ i) := by
  intro hL E _ _ _ H Dw l Xo T _ _ x0 n Λ N hΛ hN hle z hz hzi
  classical

  let ψ : T →+* AlgebraicClosure (IsLocalRing.ResidueField T) :=
    (algebraMap (IsLocalRing.ResidueField T) (AlgebraicClosure (IsLocalRing.ResidueField T))).comp
      (IsLocalRing.residue T)
  let g : ptO Xo (spMap ψ ≫ x0) ⟶ ptO Xo x0 := Over.homMk (spMap ψ) rfl
  have hA : ∀ (zz : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo x0 ⟶ Xo.univ.t.G)),
      (∀ i, InZh Xo Λ N (zz i)) → GeoInj Xo x0 zz → ∀ a, InZh Xo Λ N a → ∃ i, zz i = a := by
    intro zz hzz hgi a ha
    obtain ⟨i, hi⟩ := exists_eq_of_isAlgClosed Xo (spMap ψ ≫ x0) Λ hΛ hN hle
      (fun i b => g ≫ zz i b) (fun i => inZh_comp Xo Λ N g (hzz i)) (hgi _ ψ g rfl)
      (fun b => g ≫ a b) (inZh_comp Xo Λ N g ha)
    refine ⟨i, funext fun b => ?_⟩
    have hib : g ≫ zz i b = g ≫ a b := congrFun hi b

    obtain ⟨e, he, hiff⟩ := exists_isIdempotentElem_torsion_eq hL E H Dw l Xo T x0 (N ^ 2) (pow_pos hN 2)
      (zz i b) (a b) ((hzz i).1 b) (ha.1 b)
    have hψ : ψ e = 1 := (hiff _ ψ).2 (congrArg (fun f => f.left) hib)
    have hmul : e * (1 - e) = 0 := by rw [mul_sub, _root_.mul_one, he.eq, sub_self]
    have he1 : e = 1 := by
      rcases IsLocalRing.isUnit_or_isUnit_one_sub_self e with hu | hu
      · exact (sub_eq_zero.1 ((hu.mul_right_eq_zero).1 hmul)).symm
      · rw [(hu.mul_left_eq_zero).1 hmul, map_zero] at hψ
        exact absurd hψ zero_ne_one
    have hid := (hiff T (RingHom.id T)).1 (by rw [he1, map_one])
    have hsp : spMap (RingHom.id T) = 𝟙 _ := by simp [spMap]
    rw [hsp, Category.id_comp, Category.id_comp] at hid
    exact Over.OverMorphism.ext hid
  refine ⟨hA z hz hzi, fun z' hz' hzi' => ?_⟩
  have hsel : ∀ i, ∃ j, z j = z' i := fun i => hA z hz hzi (z' i) (hz' i)
  choose σ' hσ' using hsel
  have hinj' : Function.Injective z' := by
    intro i i' h
    apply hzi' _ ψ g rfl
    show (fun b => g ≫ z' i b) = fun b => g ≫ z' i' b
    rw [h]
  have σinj : Function.Injective σ' := by
    intro i i' h
    apply hinj'
    rw [← hσ' i, ← hσ' i', h]
  exact ⟨Equiv.ofBijective σ' ⟨σinj, Finite.surjective_of_injective σinj⟩, fun i => (hσ' i).symm⟩

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.framedPoints_lift_to_levelCover : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), (∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra d.c₂.F S], (∀ a : c.F, algebraMap d.c₂.F S (d.eF a) = algebraMap c.F S a) → ∀ (y : FrPt Xo c S) (x₂ : Sp S ⟶ d.Xo₂.X), x₂ ≫ d.r = y.x → x₂ ≫ d.Xo₂.s = sOf d.c₂ S → ∃ y₂ : FrPt d.Xo₂ d.c₂ S, y₂.x = x₂ ∧ FrOver d y₂ y) ∧ (∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra d.c₂.F S], (∀ a : c.F, algebraMap d.c₂.F S (d.eF a) = algebraMap c.F S a) → ∀ (T : Type) [CommRing T] [Algebra c.F T] [Algebra d.c₂.F T], (∀ a : c.F, algebraMap d.c₂.F T (d.eF a) = algebraMap c.F T a) → ∀ (ψ : S →ₐ[c.F] T) (ψ₂ : S →ₐ[d.c₂.F] T), ψ₂.toRingHom = ψ.toRingHom → ∀ (y : FrPt Xo c S) (y₂ : FrPt d.Xo₂ d.c₂ S) (z : FrPt Xo c T) (z₂ : FrPt d.Xo₂ d.c₂ T), FrOver d y₂ y → FrMap ψ y z → FrMap ψ₂ y₂ z₂ → FrOver d z₂ z) ∧ ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra d.c₂.F S], (∀ a : c.F, algebraMap d.c₂.F S (d.eF a) = algebraMap c.F S a) → ∀ (t : Ix Dw → Sˣ) (y y' : FrPt Xo c S) (y₂ y₂' : FrPt d.Xo₂ d.c₂ S), FrOver d y₂ y → FrOver d y₂' y' → y₂'.x = y₂.x → FrBor t y y' → FrBor t y₂ y₂' := by
  first | exact @GlobalTheory.frames_lift_to_cover | exact GlobalTheory.frames_lift_to_cover | (intros; apply GlobalTheory.frames_lift_to_cover <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

namespace GlobalTheory.ThetaVal

theorem jetAug_comp_jetSubstP {S A B : Type} [CommRing S] (m : ℕ) (φ : A → MvPolynomial B S) :
    (jetAug : Jet S B m →ₐ[S] S).comp (jetSubstP m φ) = (jetAug : Jet S A m →ₐ[S] S) := by
  apply Ideal.Quotient.algHom_ext S
  apply MvPolynomial.algHom_ext
  intro i
  simp [jetSubstP, jetAug, jetMap, liftJet]
  erw [Ideal.Quotient.lift_mk]
  simp

private theorem homAt_comp_homAt_eq_homAt_comp {X : Scheme.{0}} {S : Type} [CommRing S] (x0 : Sp S ⟶ X) {A B C : Type} [CommRing A]
    [Algebra S A] [CommRing B] [Algebra S B] [CommRing C] [Algebra S C] (f : A →ₐ[S] B) (g : B →ₐ[S] C) :
    Formalism.L2.Pj.homAt x0 g ≫ Formalism.L2.Pj.homAt x0 f = Formalism.L2.Pj.homAt x0 (g.comp f) := by
  unfold Formalism.L2.Pj.homAt
  ext : 1
  simp only [Over.comp_left, Over.homMk_left]
  unfold spMap
  rw [← Spec.map_comp]
  rfl



theorem rig_of_frAxes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (κ : Type) [Fintype κ] (tg : κ → (Sp (DualNumber S) ⟶ t.G.left)) (uvec : κ → Fin d → S) (x : ∀ m, jOG x0 d m 1 ⟶ t.G), (∀ j, MvPowerSeries.constantCoeff (F j) = 0) → (∀ a j, MvPowerSeries.constantCoeff (act a j) = 0) → IsChartG t x0 d F act tg uvec x → ∀ e : ∀ m, FrTyG t x0 d x m, (∀ m, (e m).IsGen) → FrTrunc t x0 d x e → FrAxes t x0 d x e → ∀ wP : PrimTyG t, IsPrimG t wP → Rig0G t x0 d x act e wP := by
  intro E _ _ _ H X0 t S _ x0 d F act κ _ tg uvec x hF hact hch e hgen htr hax wP hP
  have hL : t.PP.L.IsLB := t.PP.isLB
  unfold Rig0G eLG peG
  apply corr_of_val hL
  intro y J hJ
  rw [val_pull hJ, val_mul hJ, val_pull hJ]
  rw [val_pull hJ (φ := cφG t ![jptG t x0 d x 0 (0 : Fin 2), jptG t x0 d x 0 (1 : Fin 2)]) (ε := cε 2) (t := e 0)]
  rw [Formalism.MainNotions.ModuliIntegralCharts.H1.GermB.val_rigT _ _ _ _ _ _ _ hJ]
  have hA : (𝟙 _ ≫ Over.Hom.left (Formalism.L2.Pj.homAt x0 (jetAug : Jet S (Fin 1 × Fin d) 0 →ₐ[S] S))) ≫
      (x 0).left = (overAt x0 S).hom ≫ eSec t.G := by
    rw [Category.id_comp, ← Over.comp_left, hch.zero 0]
    rfl
  have hB : ∀ ψ : Fin 2 × Fin d → MvPolynomial (Fin 1 × Fin d) S,
      (𝟙 _ ≫ Over.Hom.left (Formalism.L2.Pj.homAt x0 (jetAug : Jet S (Fin 1 × Fin d) 0 →ₐ[S] S))) ≫
        Over.Hom.left (Formalism.L2.Pj.homAt x0 (jetSubstP 0 ψ)) =
        Over.Hom.left (Formalism.L2.Pj.homAt x0 (jetAug : Jet S (Fin 2 × Fin d) 0 →ₐ[S] S)) := by
    intro ψ
    rw [Category.id_comp, ← Over.comp_left, homAt_comp_homAt_eq_homAt_comp, jetAug_comp_jetSubstP]
  rw [hA, hB]
  rw [← hB (fun p : Fin 2 × Fin d =>
    (![fun _ => 0, fun j => MvPolynomial.X ((0 : Fin 1), j)] : Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) S)
      p.1 p.2)]
  rw [← val_pull hJ (φ := cφG t ![jptG t x0 d x 0 (0 : Fin 2), jptG t x0 d x 0 (1 : Fin 2)]) (ε := cε 2)
    (t := e 0)]
  rw [val_corr hJ (hax 0).1, val_one, _root_.mul_one]
  rw [← val_pull hJ wP (eSec t.G), val_corr hJ hP.2, Category.id_comp]

end GlobalTheory.ThetaVal
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.universal_weilPairing_pullback_exists_unique : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (N : ℕ), 0 < N → (∀ (T T' : Over Xo.X) (h : T' ⟶ T) (x y : T ⟶ Xo.univ.t.G) (e : Γ(T.left, ⊤)ˣ), x ^ (N ^ 2) = 1 → y ^ (N ^ 2) = 1 → WeilIs Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) x y e → WeilIs Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (h ≫ x) (h ≫ y) (Units.map h.left.appTop.hom.toMonoidHom e)) ∧ (∀ (T : Over Xo.X) (x y : T ⟶ Xo.univ.t.G), x ^ (N ^ 2) = 1 → y ^ (N ^ 2) = 1 → ∃ e : Γ(T.left, ⊤)ˣ, WeilIs Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) x y e ∧ e ^ (N ^ 2) = 1 ∧ ∀ e', WeilIs Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) x y e' → e' = e) ∧ ∀ (B : Type) [CommRing B] (u : B) (k : ℕ), IsUnit (k : B) → u ^ k = 1 → (∀ (K : Type) [Field K] [IsAlgClosed K] (χ : B →+* K), χ u = 1) → u = 1 := by
  first | exact @GlobalTheory.UnivPairing.weilIs_univ_pull_exists_unique | exact GlobalTheory.UnivPairing.weilIs_univ_pull_exists_unique | (intros; apply GlobalTheory.UnivPairing.weilIs_univ_pull_exists_unique <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.universal_normalised_mulByNat_pullback_iso : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (N : ℕ), ∃ α₀ : LB.Gen (LB.LinComb Xo.univ.t.PP.L (K := Fin 2) ![𝟙 Xo.univ.t.G.left, (mulA Xo.univ.t.G N).left] ![(N : ℤ) ^ 2, -1]), α₀.IsGen ∧ IsNormMul Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig N α₀ ∧ (∀ α₁, α₁.IsGen → IsNormMul Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig N α₁ → LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ α₁ α₀) ∧ ∀ T : Over Xo.X, ∃ α : LB.Gen (LB.LinComb Xo.univ.t.PP.L (K := Fin 2) ![(snd T Xo.univ.t.G).left, (snd T Xo.univ.t.G ^ N).left] ![(N : ℤ) ^ 2, -1]), α.IsGen ∧ LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ α (LB.pullGen Xo.univ.t.PP.L _ _ α₀ (snd T Xo.univ.t.G).left) := by
  first | exact @GlobalTheory.moduli_univ_normMul | exact GlobalTheory.moduli_univ_normMul | (intros; apply GlobalTheory.moduli_univ_normMul <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.universal_symLift_exists_unique_global : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (N : ℕ), Odd N → ∀ (T : Over Xo.X) (x : T ⟶ Xo.univ.t.G), x ^ (N ^ 2) = 1 → (∃ U : ThetaGrp Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) T, SymLift Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (N ^ 2) x U) ∧ ∀ U U' : ThetaGrp Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) T, SymLift Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (N ^ 2) x U → SymLift Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (N ^ 2) x U' → LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ U.φ U'.φ := by
  first | exact @GlobalTheory.moduli_univ_symLift_global | exact GlobalTheory.moduli_univ_symLift_global | (intros; apply GlobalTheory.moduli_univ_symLift_global <;> assumption)
end
