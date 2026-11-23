module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Mathlib.Analysis.Complex.Norm
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle027
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFrobGBaseChange
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FrobeniusOnTorsion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle078
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PullPullAndSplitPull
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle168
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle170
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CardTorsionTranslateZerosLt
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle004
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle007
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle128
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
namespace GlobalTheory.SS.SpecialCount

theorem transfer {M N : Type} [CommGroup M] [Group N] (H : Subgroup M) (r : H →* N) (Φ : MulAut M)
    (φ : ℕ → N → N) (hφ : ∀ (j : ℕ) (x : H), ∃ h : Φ^[j] x ∈ H, r ⟨_, h⟩ = φ j (r x)) (l e : ℕ)
    (hinj : ∀ n (x : H), x ^ l ^ n = 1 → r x = 1 → x = 1) (V : Subgroup N)
    (hV : ∀ x ∈ V, φ 1 x = x ^ e) (hfin : ∀ n, Finite {x : N // x ^ l ^ n = 1}) (Q : Polynomial ℤ)
    (hQ : ∀ (x : N) n, x ^ l ^ n = 1 →
      ((List.range (Q.natDegree + 1)).map fun j => φ j x ^ Q.coeff j).prod ∈ V) :
    ∃ U : Subgroup M,
      (∀ n, Nat.card {x : H // x ^ l ^ n = 1} ≤ Nat.card {x : N // x ^ l ^ n = 1} ∧
        Nat.card {x : U // x ^ l ^ n = 1} ≤ Nat.card {x : V // x ^ l ^ n = 1}) ∧
      (∀ n, ∀ x ∈ U, x ^ l ^ n = 1 → Φ x = x ^ e) ∧
      ∀ n, ∀ x ∈ H, x ^ l ^ n = 1 → ∏ j ∈ Finset.range (Q.natDegree + 1), (Φ^[j] x) ^ Q.coeff j ∈ U := by
  have inj : ∀ n (x y : H), x ^ l ^ n = 1 → y ^ l ^ n = 1 → r x = r y → x = y := by
    intro n x y hx hy h
    have := hinj n (x * y⁻¹) (by rw [mul_pow, inv_pow, hx, hy]; simp) (by rw [map_mul, map_inv, h]; simp)
    exact mul_inv_eq_one.1 this
  have memU : ∀ x : M, x ∈ (V.comap r).map H.subtype ↔ ∃ h : x ∈ H, r ⟨x, h⟩ ∈ V := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨h, hx⟩
      exact ⟨⟨x, h⟩, hx, rfl⟩
  refine ⟨(V.comap r).map H.subtype, fun n => ⟨?_, ?_⟩, fun n x hx hn => ?_, fun n x hx hn => ?_⟩
  · have := hfin n
    refine Nat.card_le_card_of_injective
      (fun x => ⟨r x.1, by rw [← map_pow, x.2, map_one]⟩) fun x y h => ?_
    exact Subtype.ext (inj n _ _ x.2 y.2 (congrArg Subtype.val h))
  · have := hfin n
    have : Finite {x : V // x ^ l ^ n = 1} :=
      Finite.of_injective (β := {x : N // x ^ l ^ n = 1})
        (fun x => ⟨x.1.1, congrArg Subtype.val x.2⟩) fun x y h =>
          Subtype.ext (Subtype.ext (by exact congrArg (fun z : {x : N // x ^ l ^ n = 1} => z.1) h))
    have tor : ∀ x : {x : (V.comap r).map H.subtype // x ^ l ^ n = 1},
        (⟨x.1.1, ((memU _).1 x.1.2).1⟩ : H) ^ l ^ n = 1 := fun x =>
      Subtype.ext (by exact congrArg (fun z : (V.comap r).map H.subtype => z.1) x.2)
    refine Nat.card_le_card_of_injective
      (fun x => ⟨⟨r ⟨x.1.1, ((memU _).1 x.1.2).1⟩, ((memU _).1 x.1.2).2⟩, Subtype.ext (by
        change r _ ^ l ^ n = 1
        rw [← map_pow, tor x, map_one])⟩) fun x y h => ?_
    have := inj n _ _ (tor x) (tor y) (congrArg (fun z => z.1.1) h)
    exact Subtype.ext (Subtype.ext (by exact congrArg (fun z : H => z.1) this))
  · obtain ⟨h, hv⟩ := (memU x).1 hx
    obtain ⟨h', e'⟩ := hφ 1 ⟨x, h⟩
    have := inj n ⟨_, h'⟩ (⟨x, h⟩ ^ e) (Subtype.ext (by
        change Φ x ^ l ^ n = 1
        rw [← map_pow, hn, map_one])) (Subtype.ext (by
        change (x ^ e) ^ l ^ n = 1
        rw [← pow_mul, mul_comm, pow_mul, hn, one_pow])) (by rw [e', hV _ hv, map_pow])
    exact congrArg Subtype.val this
  · choose h e' using fun j => hφ j ⟨x, hx⟩
    have hr := hQ (r ⟨x, hx⟩) n (by
      rw [← map_pow, show (⟨x, hx⟩ : H) ^ l ^ n = 1 from Subtype.ext hn, map_one])
    refine ⟨((List.range (Q.natDegree + 1)).map fun j => (⟨_, h j⟩ : H) ^ Q.coeff j).prod, ?_, ?_⟩
    · change r _ ∈ V
      rw [map_list_prod, List.map_map]
      have : (r ∘ fun j => (⟨_, h j⟩ : H) ^ Q.coeff j) = fun j => φ j (r ⟨x, hx⟩) ^ Q.coeff j := by
        funext j
        simp only [Function.comp, map_zpow, e']
      rw [this]
      exact hr
    · rw [map_list_prod, List.map_map]
      rfl

theorem exists_restrict {R Ω : Type} [CommRing R] [IsLocalRing R] [Field Ω] [Algebra R Ω]
    (hi : Function.Injective (algebraMap R Ω)) (q : ℕ) (ψ : Ω →+* Ω)
    (h : ∀ x : R, ∃ y : R, algebraMap R Ω y = ψ (algebraMap R Ω x) ∧ y - x ^ q ∈ IsLocalRing.maximalIdeal R) :
    ∃ σ : R →+* R, (∀ x, algebraMap R Ω (σ x) = ψ (algebraMap R Ω x)) ∧
      ∀ x, IsLocalRing.residue R (σ x) = IsLocalRing.residue R x ^ q := by
  choose f hf hf' using h
  refine ⟨{ toFun := f
            map_one' := hi (by simp [hf])
            map_mul' := fun x y => hi (by simp [hf])
            map_zero' := hi (by simp [hf])
            map_add' := fun x y => hi (by simp [hf]) }, hf, fun x => ?_⟩
  have := (IsLocalRing.residue_eq_zero_iff _).2 (hf' x)
  rw [map_sub, map_pow, sub_eq_zero] at this
  exact this

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

theorem smConn_pullback {S T : Scheme.{0}} (f : T ⟶ S) (G : Over S) [GrpObj G] (h : SmConn G) :
    SmConn ((Over.pullback f).obj G) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨inferInstance, ?_, ?_, ?_, ?_⟩
  · show Smooth (pullback.snd _ _); infer_instance
  · show IsSeparated (pullback.snd _ _); infer_instance
  · show QuasiCompact (pullback.snd _ _); infer_instance
  · show GeometricallyConnected (pullback.snd _ _); infer_instance

end GlobalTheory.SS.SpecialCount

namespace GlobalTheory.SS
open SpecialCount

theorem frobenius_on_integral_torsion : ∀ (W R Ω : Type) [CommRing W] [CommRing R] [IsDomain R] [IsLocalRing R] [Field Ω] [Algebra W R] [Algebra R Ω] [Algebra W Ω] [IsScalarTower W R Ω], Function.Injective (algebraMap R Ω) → IsAlgClosed (IsLocalRing.ResidueField R) → ∀ (p r l : ℕ), p.Prime → CharP (IsLocalRing.ResidueField R) p → 1 ≤ r → l.Prime → IsUnit (l : R) → (∀ c : IsLocalRing.ResidueField R, ∃ m, 1 ≤ m ∧ c ^ ((p ^ r) ^ m) = c) → ∀ ψ : Ω →+* Ω, (∀ w : W, ψ (algebraMap W Ω w) = algebraMap W Ω w) → (∀ x : R, ∃ y : R, algebraMap R Ω y = ψ (algebraMap R Ω x) ∧ y - x ^ (p ^ r) ∈ IsLocalRing.maximalIdeal R) → ∀ (G : Over (Sp W)) [GrpObj G], SmConn G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ L : LB ((Over.pullback (spMap ((IsLocalRing.residue R).comp (algebraMap W R)))).obj G).left, AmpleCub ((Over.pullback (spMap ((IsLocalRing.residue R).comp (algebraMap W R)))).obj G) L → ∀ (M : Type) [CommGroup M] (θ : M ≃* (Over.mk (spMap (algebraMap W Ω)) ⟶ G)) (Ψ : MulAut M), (∀ x, (θ (Ψ x)).left = spMap ψ ≫ (θ x).left) → ∃ (t a m C : ℕ) (Q : Polynomial ℤ) (H U : Subgroup M), 1 ≤ m ∧ (∀ x, x ∈ H ↔ ∃ s : Sp R ⟶ G.left, s ≫ G.hom = spMap (algebraMap W R) ∧ spMap (algebraMap R Ω) ≫ s = (θ x).left) ∧ (∀ n, Nat.card {x : H // x ^ l ^ n = 1} ≤ C * l ^ (n * (t + 2 * a)) ∧ Nat.card {x : U // x ^ l ^ n = 1} ≤ C * l ^ (n * t)) ∧ (∀ β : ℂ, Polynomial.aeval β Q = 0 → ‖β‖ < (((p ^ r) ^ m : ℕ) : ℝ)) ∧ (∀ n, ∀ x ∈ U, x ^ l ^ n = 1 → (Ψ ^ m) x = x ^ ((p ^ r) ^ m)) ∧ (∀ n, ∀ x ∈ H, x ^ l ^ n = 1 → ∏ j ∈ Finset.range (Q.natDegree + 1), ((Ψ ^ m : MulAut M)^[j] x) ^ Q.coeff j ∈ U) ∧ (g ≤ t + a → Nonempty (TorusExtension ((Over.pullback (spMap ((IsLocalRing.residue R).comp (algebraMap W R)))).obj G))) := by
  intro W R Ω _ _ _ _ _ _ _ _ _ hi hac p r l hp hch hr hl hlu hfin ψ hψW hψR G _ hG g hg L hL M _ θ Ψ hΨ
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨σ, hσ, hσ'⟩ := exists_restrict hi (p ^ r) ψ hψR
  have hσW : ∀ w, σ (algebraMap W R w) = algebraMap W R w := fun w => hi (by
    rw [hσ, ← IsScalarTower.algebraMap_apply, hψW])
  obtain ⟨F, hF, hFx⟩ := GlobalTheory.SS.exists_frobG_baseChange W (IsLocalRing.ResidueField R)
    ((IsLocalRing.residue R).comp (algebraMap W R)) p r hr (fun w => by
      rw [RingHom.comp_apply, ← hσ', hσW]) hfin G hG
  have hlp : l ≠ p := by
    rintro rfl
    have := hlu.map (IsLocalRing.residue R)
    rw [map_natCast, CharP.cast_eq_zero] at this
    exact not_isUnit_zero this
  have hq : 2 ≤ p ^ r := hp.two_le.trans (Nat.le_self_pow (by omega) p)
  obtain ⟨t, a, m, C, Q, V, hm, hroot, hV, hcount, hQ, hT⟩ := GlobalTheory.SS.frobenius_on_torsion _ p l hl hlp _
    (smConn_pullback _ G hG) g (by
      show SmoothOfRelativeDimension g (pullback.snd _ _)
      exact (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
        (IsPullback.of_hasPullback _ _) hg) L hL F (p ^ r) hq hF
  obtain ⟨H₀, red, hH, hred, hinj⟩ := GlobalTheory.RedPts.exists_reduction W R Ω hi G hG
  let H : Subgroup M := H₀.comap θ.toMonoidHom
  let κ : H →* H₀ := (θ.toMonoidHom.subgroupComap H₀)
  have step : ∀ x : H, ∃ h : Ψ x ∈ H, red (κ ⟨_, h⟩) = red (κ x) ≫ F.asHom := by
    intro x
    obtain ⟨s, hs, hs'⟩ := (hH _).1 x.2
    have a1 : (spMap σ ≫ s) ≫ G.hom = spMap (algebraMap W R) := by
      rw [Category.assoc, hs, sp_comp]
      congr 1
      exact RingHom.ext hσW
    have a2 : spMap (algebraMap R Ω) ≫ spMap σ ≫ s = (θ (Ψ x)).left := by
      rw [hΨ, ← Category.assoc, sp_comp, show (algebraMap R Ω).comp σ = ψ.comp (algebraMap R Ω) from
        RingHom.ext hσ, ← sp_comp, Category.assoc, hs']
      rfl
    have hx : Ψ x ∈ H := (hH _).2 ⟨_, a1, a2⟩
    refine ⟨hx, ?_⟩
    have b1 := hred (κ ⟨_, hx⟩) _ a1 a2
    have b2 := hred (κ x) s hs hs'
    have b3 := hFx (red (κ x)) (iterateFrobenius _ p r) (fun c => rfl)
    ext1
    apply pullback.hom_ext
    · refine b1.trans (Eq.trans ?_ b3.symm)
      erw [b2]
      rw [← Category.assoc, ← Category.assoc, sp_comp, sp_comp]
      congr 2
      exact RingHom.ext hσ'
    · exact (Over.w _).trans (Over.w _).symm
  have iter : ∀ (n : ℕ) (x : H), ∃ h : (Ψ ^ n) x ∈ H,
      red (κ ⟨_, h⟩) = red (κ x) ≫ (F ^ n).asHom := by
    intro n
    induction n with
    | zero => exact fun x => ⟨x.2, (Category.comp_id _).symm⟩
    | succ n ih =>
      intro x
      obtain ⟨h, e⟩ := step x
      obtain ⟨h', e'⟩ := ih ⟨_, h⟩
      rw [pow_succ, pow_succ]
      refine ⟨h', e'.trans ?_⟩
      rw [e, Category.assoc]
      rfl
  obtain ⟨U, hU1, hU2, hU3⟩ := transfer H (red.comp κ) (Ψ ^ m)
    (fun j x => x ≫ ((F ^ m) ^ j).asHom) (fun j x => by
      have e : (Ψ ^ m : MulAut M)^[j] x = (Ψ ^ (m * j)) x := by
        rw [pow_mul]
        generalize (x : M) = y
        induction j generalizing y with
        | zero => rfl
        | succ j ih => rw [pow_succ, Function.iterate_succ_apply, ih]; rfl
      rw [e, ← pow_mul]
      exact iter (m * j) x) l ((p ^ r) ^ m) (fun n x hx h => by
      have := hinj (l ^ n) (κ x) (by rw [Nat.cast_pow]; exact hlu.pow n)
        (by rw [← map_pow, hx, map_one]) h
      exact Subtype.ext (θ.injective ((congrArg Subtype.val this).trans (map_one θ).symm))) V
    (fun x hx => by rw [pow_one]; exact hV x hx) (fun n => (hcount n).1) Q hQ
  refine ⟨t, a, m, C, Q, H, U, hm, fun x => hH _, fun n => ⟨(hU1 n).1.trans (hcount n).2.1,
    (hU1 n).2.trans (hcount n).2.2⟩, fun β hβ => ?_, hU2, hU3, hT⟩
  rw [Nat.cast_pow]
  exact hroot β hβ

end GlobalTheory.SS
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

noncomputable section
namespace GlobalTheory.ZJ.GenericSplit

theorem split_transport {S : Scheme.{0}} {G : Over S} [GrpObj G] (C : Charts G.left) {d : ℕ} (c : Fin d → C.Cl)
    {K K' : Type} [Field K] [Field K'] {H : Over (Sp K)} [GrpObj H] {H' : Over (Sp K')} [GrpObj H']
    {t : Sp K ⟶ S} {t' : Sp K' ⟶ S} (f : Sp K' ⟶ Sp K) (hf : f ≫ t = t') {φ : H.left ⟶ G.left}
    {ψ : H'.left ⟶ G.left} [IsAffineHom φ] [IsAffineHom ψ] (hφ : IsGrpPullback H G t φ)
    (hψ : IsGrpPullback H' G t' ψ) (h : Charts.Split (C.pull φ) c) : Charts.Split (C.pull ψ) c := by
  subst hf
  have w : ψ ≫ G.hom = (H'.hom ≫ f) ≫ t := by rw [hψ.1.w, Category.assoc]
  obtain ⟨l, h₁, h₂⟩ : ∃ l : H'.left ⟶ H.left, l ≫ φ = ψ ∧ l ≫ H.hom = H'.hom ≫ f :=
    ⟨hφ.1.lift _ _ w, hφ.1.lift_fst _ _ w, hφ.1.lift_snd _ _ w⟩
  subst h₁
  have hl : IsGrpPullback H' H f l := hφ.cancel hψ h₂
  have : IsAffineHom l := MorphismProperty.of_isPullback (P := @IsAffineHom) hl.1.flip inferInstance
  exact SplitPull.pull_pull_and_split_pull.2 K K' H H' f l hl (C.pull φ) d c h

theorem mem_basicOpen_of_mem {X : Scheme.{0}} (C : Charts X) (a a' : {i // C.wt i = C.c₀}) (j : C.I) (x : X)
    (ha : x ∈ C.W a) (h : x ∈ X.basicOpen (C.r a' j)) : x ∈ X.basicOpen (C.r a j) := by
  have hx : x ∈ C.W a ⊓ C.W a' := ⟨ha, X.basicOpen_le _ h⟩
  have e : ∀ (V : X.Opens) (k : C.W a ⊓ C.W a' ≤ V) (u : Γ(X, V)),
      X.basicOpen (resG X k u) = (C.W a ⊓ C.W a') ⊓ X.basicOpen u := fun V k u => X.basicOpen_res u (homOfLE k).op
  have h₁ : x ∈ X.basicOpen (resG X (inf_le_left : C.W a ⊓ C.W a' ≤ C.W a) (C.r a j)) := by
    rw [C.trans a a' j, Scheme.basicOpen_mul, e, e, ← C.inter]
    exact ⟨⟨hx, hx⟩, hx, h⟩
  rw [e] at h₁
  exact h₁.2

theorem exists_open {R : Type} [CommRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G] (C : Charts G.left) {d : ℕ}
    (c : Fin d → C.Cl) (Sg : Set (Sp R)) (hd : Dense Sg) (hs : C.SplitOn c Sg) :
    ∃ (a : {i // C.wt i = C.c₀}) (j : Fin d → C.I) (b : R), b ≠ 0 ∧ (∀ n, C.wt (j n) = c n) ∧
      ∀ x : PrimeSpectrum R, b ∉ x.asIdeal →
        eSec G x ∈ C.W a ∧ ∀ n, eSec G x ∈ G.left.basicOpen (C.r a (j n)) := by
  let e : Sp R ⟶ G.left := eSec G
  obtain ⟨a, ha⟩ : ∃ a, e (⊥ : PrimeSpectrum R) ∈ C.W a :=
    TopologicalSpace.Opens.mem_iSup.1 (C.cover.ge (Set.mem_univ _))
  obtain ⟨x, hxa, hx⟩ := hd.inter_open_nonempty _ (e ⁻¹ᵁ C.W a).isOpen ⟨_, ha⟩
  obtain ⟨K, _, t, _, ht, -, i, hT⟩ := hs x hx
  have hp := isGrpPullback_pullback G t
  have he : (eSec ((Over.pullback t).obj G) : Sp K ⟶ _) ≫ pullback.fst G.hom t = t ≫ e :=
    eSec_comp_of_isGrpPullback hp
  let y : Sp K := (⊥ : PrimeSpectrum K)
  have hy : t y = x := ht.le ⟨y, rfl⟩
  have hj : ∀ n, ∃ j, C.wt j = c n ∧ e x ∈ G.left.basicOpen (C.r a j) := by
    intro n
    obtain ⟨a', j, hj, hm⟩ := hT.bpf n (eSec ((Over.pullback t).obj G) y)
    refine ⟨j, hj, mem_basicOpen_of_mem C a a' j _ hxa ?_⟩
    have hm' : eSec ((Over.pullback t).obj G) y ∈ pullback.fst G.hom t ⁻¹ᵁ G.left.basicOpen (C.r a' j) := by
      rw [Scheme.preimage_basicOpen]
      exact hm
    have h2 : ((eSec ((Over.pullback t).obj G) : Sp K ⟶ _) ≫ pullback.fst G.hom t) y ∈
      G.left.basicOpen (C.r a' j) := hm'
    rw [he] at h2
    rw [← hy]
    exact h2
  choose j hj hjx using hj
  let U : Set (PrimeSpectrum R) := (e ⁻¹ᵁ C.W a : Set (Sp R)) ∩ ⋂ n, (e ⁻¹ᵁ G.left.basicOpen (C.r a (j n)) : Set (Sp R))
  have hU : IsOpen U := (e ⁻¹ᵁ C.W a).isOpen.inter (isOpen_iInter_of_finite fun n => (e ⁻¹ᵁ _).isOpen)
  have hxU : x ∈ U := ⟨hxa, Set.mem_iInter.2 hjx⟩
  obtain ⟨_, ⟨b, rfl⟩, hb, hbU⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hxU hU
  refine ⟨a, j, b, ?_, hj, fun z hz => ⟨(hbU hz).1, fun n => Set.mem_iInter.1 (hbU hz).2 n⟩⟩
  rintro rfl
  exact hb (Ideal.zero_mem _)

theorem split_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] (C : Charts G.left) (d : ℕ) (c : Fin d → C.Cl) (Sg : Set (Sp R)) [IsAffineHom (pullback.fst G.hom (Out.jK R))], Dense Sg → C.SplitOn c Sg → Charts.Split (H := ((Over.pullback (Out.jK R)).obj G)) (C.pull (pullback.fst G.hom (Out.jK R))) c := by
  intro R _ _ _ G _ _ _ _ _ C d c Sg _ hd hs
  obtain ⟨a, j, b, hb, hj, hU⟩ := exists_open G C c Sg hd hs
  let R' := Localization.Away b
  have hle : Submonoid.powers b ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors hb
  haveI : IsDomain R' := IsLocalization.isDomain_localization hle
  haveI : IsNoetherianRing R' := IsLocalization.isNoetherianRing (Submonoid.powers b) R' inferInstance
  let u : Sp R' ⟶ Sp R := spMap (algebraMap R R')
  haveI : IsOpenImmersion u := IsOpenImmersion.of_isLocalization b
  have hu : Set.range u = (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum R)) := PrimeSpectrum.localization_away_comap_range R' b
  let G' : Over (Sp R') := (Over.pullback u).obj G
  let π : G'.left ⟶ G.left := pullback.fst G.hom u
  have hp : IsGrpPullback G' G u π := isGrpPullback_pullback G u
  haveI : IsAffineHom π := MorphismProperty.of_isPullback (P := @IsAffineHom) hp.1.flip inferInstance
  haveI : Smooth G'.hom := inferInstanceAs (Smooth (pullback.snd G.hom u))
  haveI : IsSeparated G'.hom := inferInstanceAs (IsSeparated (pullback.snd G.hom u))
  haveI : QuasiCompact G'.hom := inferInstanceAs (QuasiCompact (pullback.snd G.hom u))
  have hd' : Dense (u ⁻¹' Sg) := hd.preimage u.isOpenEmbedding.isOpenMap
  have hs' : (C.pull π).SplitOn c (u ⁻¹' Sg) := by
    intro x hx
    obtain ⟨K, _, t, _, ht, hsp⟩ := hs _ hx
    have hr : Set.range t ⊆ Set.range u := by
      rw [ht]
      rintro _ rfl
      exact ⟨x, rfl⟩
    obtain ⟨t', ht'⟩ : ∃ t', t' ≫ u = t := ⟨_, IsOpenImmersion.lift_fac u t hr⟩
    haveI : IsAffineHom (pullback.fst G'.hom t') :=
      MorphismProperty.of_isPullback (P := @IsAffineHom) (IsPullback.of_hasPullback _ _).flip inferInstance
    refine ⟨K, inferInstance, t', this, ?_, ?_⟩
    · have h1 : ∀ y, t' y = x := fun y => u.isOpenEmbedding.injective (by
        have : t y = u x := ht.le ⟨y, rfl⟩
        rw [← this, ← ht']; rfl)
      ext z
      exact ⟨fun ⟨y, hy⟩ => hy ▸ h1 y, fun hz => ⟨(⊥ : PrimeSpectrum K), (h1 _).trans hz.symm⟩⟩
    · exact split_transport C c (𝟙 _) (by rw [Category.id_comp, ht']) (isGrpPullback_pullback G t)
        ((isGrpPullback_pullback G' t').comp hp) hsp
  have he : ∀ x : Sp R', π (eSec G' x) = eSec G (u x) := fun x =>
    congrArg (fun q => q x) (eSec_comp_of_isGrpPullback hp)
  have hb' : ∀ x : Sp R', b ∉ (u x).asIdeal := fun x => hu.le ⟨x, rfl⟩
  have hB : (C.pull π).Based c a j := by
    refine ⟨fun x _ => ?_, fun n => ⟨hj n, fun x _ => ?_⟩⟩
    · change π (eSec G' x) ∈ C.W a
      rw [he]
      exact (hU _ (hb' x)).1
    · change eSec G' x ∈ G'.left.basicOpen ((π.app (C.W a)).hom (C.r a (j n)))
      rw [← Scheme.preimage_basicOpen]
      change π (eSec G' x) ∈ G.left.basicOpen (C.r a (j n))
      rw [he]
      exact (hU _ (hb' x)).2 n
  haveI : IsAffineHom (pullback.fst G'.hom (Out.jK R')) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) (IsPullback.of_hasPullback _ _).flip inferInstance
  have h := GlobalTheory.T.split_generic_of_based_weightedCharts R' G' (C.pull π) d c _ hd' hs' a j hB
  have hun : IsUnit (algebraMap R (FractionRing R) b) :=
    IsLocalization.map_units (FractionRing R) (⟨b, mem_nonZeroDivisors_of_ne_zero hb⟩ : nonZeroDivisors R)
  let g : R' →+* FractionRing R := IsLocalization.Away.lift b hun
  have hg : Function.Injective g := by
    refine (IsLocalization.lift_injective_iff _).2 fun x y => ?_
    rw [(IsLocalization.injective R' hle).eq_iff, (IsFractionRing.injective R (FractionRing R)).eq_iff]
  let g' : FractionRing R' →+* FractionRing R := IsFractionRing.lift hg
  refine split_transport C c (spMap g') ?_ ((isGrpPullback_pullback G' (Out.jK R')).comp hp)
    (isGrpPullback_pullback G (Out.jK R)) h
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext x
  change g' (algebraMap R' _ (algebraMap R R' x)) = algebraMap R _ x
  rw [IsFractionRing.lift_algebraMap]
  exact IsLocalization.Away.lift_eq b hun x

end GlobalTheory.ZJ.GenericSplit
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

theorem _root_.GlobalTheory.T.forall_term_ne_zero_of_psiRelation : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (f : ∀ α, SecBT D (𝟙_ _) 1 α), PsiRel D (𝟙_ _) f → (∃ α j, (f α).f j ≠ 0) → ∀ α, ∃ j, (f α).f j ≠ 0 := by
  first | exact @GlobalTheory.forall_ne_zero_of_psiRel | exact GlobalTheory.forall_ne_zero_of_psiRel | (intros; apply GlobalTheory.forall_ne_zero_of_psiRel <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SpecialFibreLocus

theorem exists_sec_nonzeroLocus_iff : GlobalFnsSt → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (U : Unif (IsLocalRing.maximalIdeal V) D A G) (ϑ : H0 U.LG.L 1), ∃ θ : LB.Sec D.toPre.P.L, ∀ y : (thickObj V (IsLocalRing.maximalIdeal V) 0 G).left, (fstG (IsLocalRing.maximalIdeal V) 0 G).left y ∈ nonzeroLocus ϑ ↔ (U.gt 0).pG.left y ∈ nonzeroLocus θ := by
  intro hG V _ _ _ D A G _ _ U ϑ
  obtain ⟨f, hf⟩ := GlobalTheory.FewZeros.exists_weight_zero hG U ϑ
  obtain ⟨s, hs⟩ := GlobalTheory.FewZeros.exists_sec_of_formEq_id D.toPre.P.isLB (fun U _ k => by
    have e : toUnit D.toPre.P.A ≫ D.toPre.c 0 = 1 := cPoint_zero (D := D.toPre) _
    have e₁ : padd D.toPre.P.A (𝟙 D.toPre.P.A) 1 = 𝟙 D.toPre.P.A := _root_.mul_one (𝟙 D.toPre.P.A)
    have e₂ : toUnit D.toPre.P.A ≫ η[D.toPre.P.A] = 1 := rfl
    simp [Out.DegPre.famφB, Out.DegPre.famε, Fin.prod_univ_four, e, e₁, e₂]) f
  exact ⟨s, fun y => hs ▸ hf y⟩

end GlobalTheory.SpecialFibreLocus
end
