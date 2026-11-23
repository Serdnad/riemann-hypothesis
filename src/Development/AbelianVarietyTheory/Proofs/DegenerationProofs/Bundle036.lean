module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsWeakNeronModel
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnionTranslates
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle035
public import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.exists_weak_neron_model : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K], PerfectField (IsLocalRing.ResidueField R) → ∀ (A : Over (Sp K)), Smooth A.hom → IsProper A.hom → GlobalTheory.AbLaw.IsProjBy A.hom → ∃ (n : ℕ) (M : Fin n → Model R A), (∀ i, (M i).Irr) ∧ WeakNeron M := by
  first | exact @GlobalTheory.SS.WeakNeronEx.exists_weakNeron | exact GlobalTheory.SS.WeakNeronEx.exists_weakNeron | (intros; apply GlobalTheory.SS.WeakNeronEx.exists_weakNeron <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SecPow
variable {X X' : Scheme.{0}}

theorem add_pow_succ_of_mul_self {R : Type} [CommRing R] (t e : R) (he : e * e = 0) (m : ℕ) :
    (t + e) ^ (m + 1) = t ^ (m + 1) + ((m + 1 : ℕ) : R) * (t ^ m * e) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ (t + e), ih]
    push_cast
    linear_combination ((m : R) + 1) * t ^ m * he

theorem eq_of_preimage_eq (β : X' ⟶ X) [Surjective β] {U V : X.Opens} (h : β ⁻¹ᵁ U = β ⁻¹ᵁ V) :
    U = V := by
  ext x
  obtain ⟨y, rfl⟩ := β.surjective x
  exact SetLike.ext_iff.1 h y

theorem app_rs (β : X' ⟶ X) {U V : X.Opens} (h : V ≤ U) (x : Γ(X, U)) :
    (β.app V).hom (rs X h x) = rs X' (β.preimage_mono h) ((β.app U).hom x) := by
  have := GlobalTheory.LB.appLE_resG β h le_rfl x
  rw [Scheme.Hom.appLE_eq_app] at this
  exact this

theorem exists_lift_pow (β : X' ⟶ X) [IsClosedImmersion β] [Surjective β]
    (hsq : ∀ (W : X.Opens) (x y : Γ(X, W)), (β.app W).hom x = 0 → (β.app W).hom y = 0 → x * y = 0)
    {V O : X.Opens} (hV : IsAffineOpen V) (hO : O ≤ V) (τ : Γ(X, O)) (s : Γ(X', β ⁻¹ᵁ V))
    (hs : X'.basicOpen s = β ⁻¹ᵁ O) (hτ : (β.app O).hom τ = rs X' (β.preimage_mono hO) s) :
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∃ σ : Γ(X, V), (β.app V).hom σ = s ^ k ∧ rs X hO σ = τ ^ k := by
  obtain ⟨t, rfl⟩ : ∃ t, (β.app V).hom t = s := β.app_surjective V hV s
  obtain rfl : X.basicOpen t = O :=
    eq_of_preimage_eq β ((Scheme.preimage_basicOpen β t).trans hs)
  have hε : (β.app _).hom (τ - rs X hO t) = 0 := by
    rw [map_sub, hτ, app_rs, sub_self]
  obtain ⟨n, w, hw⟩ : ∃ (n : ℕ) (w : Γ(X, V)), rs X hO w = rs X hO t ^ n * (τ - rs X hO t) :=
    exists_eq_pow_mul_of_isAffineOpen X V hV t (τ - rs X hO t)
  have h₁ : rs X' (β.preimage_mono hO) ((β.app V).hom w) = 0 := by
    rw [← app_rs β hO, hw, map_mul, hε, mul_zero]
  obtain ⟨l, hl⟩ : ∃ l : ℕ, (β.app V).hom t ^ l * (β.app V).hom w = 0 := by
    refine exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen X' (hV.preimage β) _ _ ?_
    have := congrArg (rs X' hs.le) h₁
    rw [rs_rs, map_zero] at this
    exact this
  refine ⟨n + l + 1, fun k hk => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = (n + l + j) + 1 := ⟨k - (n + l + 1), by omega⟩
  refine ⟨t ^ (n + l + j + 1) + ((n + l + j + 1 : ℕ) : Γ(X, V)) * (t ^ j * (t ^ l * w)), ?_, ?_⟩
  · simp only [map_add (f := _), map_mul, map_pow, hl, mul_zero, add_zero]
  · have e := add_pow_succ_of_mul_self (rs X hO t) (τ - rs X hO t) (hsq _ _ _ hε hε) (n + l + j)
    rw [add_sub_cancel] at e
    rw [e, map_add (f := _), map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, map_natCast, hw]
    ring

theorem exists_pow_eq {W O : X.Opens} (hW : IsCompact (W : Set X)) (hO : O ≤ W) (x y : Γ(X, W))
    (hsq : (y - x) * (y - x) = 0) (hx : X.basicOpen x ≤ O) (h : rs X hO x = rs X hO y) :
    ∃ l₀ : ℕ, ∀ l, l₀ ≤ l → x ^ l = y ^ l := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, x ^ m * (y - x) = 0 := by
    refine exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact X hW _ _ ?_
    have := congrArg (rs X hx) h
    rw [rs_rs, rs_rs] at this
    change rs X (hx.trans hO) (y - x) = 0
    rw [map_sub, this, sub_self]
  refine ⟨m + 1, fun l hl => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, l = (j + m) + 1 := ⟨l - (m + 1), by omega⟩
  have e := add_pow_succ_of_mul_self x (y - x) hsq (j + m)
  rw [add_sub_cancel, pow_add x j m, _root_.mul_assoc, hm] at e
  simpa using e.symm

theorem exists_finite_affine_cover [CompactSpace X] {H : LB X} (hH : H.IsLB) :
    ∃ (I : Type) (_ : Finite I) (V : I → X.Opens) (c : I → H.ι),
      (∀ a, IsAffineOpen (V a)) ∧ (∀ a, V a ≤ H.U (c a)) ∧ ⊤ ≤ ⨆ a, V a := by
  have h : ∀ x : X, ∃ (V : X.Opens) (i : H.ι), IsAffineOpen V ∧ x ∈ V ∧ V ≤ H.U i := fun x => by
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hH.cover.ge (Set.mem_univ x))
    obtain ⟨_, ⟨V, hV, rfl⟩, hx, hle⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hi (H.U i).isOpen
    exact ⟨V, i, hV, hx, hle⟩
  choose V c hV hx hle using h
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover (fun x => (V x : Set X))
    (fun x => (V x).isOpen) fun x _ => Set.mem_iUnion.2 ⟨x, hx x⟩
  refine ⟨S, inferInstance, fun a => V a, fun a => c a, fun a => hV a, fun a => hle a, fun x _ => ?_⟩
  obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.1 (hS (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨a, ha⟩, hxa⟩

theorem basicOpen_rs_eq {H : LB X} (s : LB.Sec H) (i : H.ι) {V : X.Opens} (h : V ≤ H.U i) :
    X.basicOpen (rs X h (s.f i)) = V ⊓ nonzeroLocus s := by
  apply le_antisymm
  · refine le_inf (X.basicOpen_le _) ?_
    erw [Scheme.basicOpen_res]
    exact inf_le_right.trans (le_iSup (fun k => X.basicOpen (s.f k)) i)
  · have hu := SecOn.isUnit_rs_of_le_nonzeroLocus s i (O := V ⊓ nonzeroLocus s)
      (inf_le_left.trans h) inf_le_right
    rw [← rs_rs h inf_le_left] at hu
    have e := X.basicOpen_of_isUnit hu
    erw [Scheme.basicOpen_res] at e
    exact e.ge.trans inf_le_right

theorem exists_pow_section : ∀ (X X' : Scheme.{0}) (β : X' ⟶ X) [IsClosedImmersion β] [Surjective β] [CompactSpace X] [QuasiSeparatedSpace X], (∀ (W : X.Opens) (x y : Γ(X, W)), (β.app W).hom x = 0 → (β.app W).hom y = 0 → x * y = 0) → ∀ H : LB X, H.IsLB → ∀ (s₀ : LB.Sec (H.pull β)) (D : X.Opens), β ⁻¹ᵁ D = nonzeroLocus s₀ → ∀ t : SecOn H D, SecOn.pull H β D t = GlobalTheory.LB.ofSec s₀ (β ⁻¹ᵁ D) → ∃ n : ℕ, 1 ≤ n ∧ ∃ σ : LB.Sec (pw H n), nonzeroLocus σ = D := by
  intro X X' β _ _ _ _ hsq H hH s₀ D hD t ht
  obtain ⟨I, _, V, c, hV, hc, hcov⟩ := exists_finite_affine_cover hH
  let s (a : I) : Γ(X', β ⁻¹ᵁ V a) := rs X' (le_pull H β (hc a)) (s₀.f fun _ => c a)
  let τ (a : I) : Γ(X, V a ⊓ D) :=
    rs X (le_inf inf_le_right (inf_le_left.trans (hc a))) (GlobalTheory.LB.coord t (c a))
  have hs (a : I) : X'.basicOpen (s a) = β ⁻¹ᵁ (V a ⊓ D) :=
    (basicOpen_rs_eq s₀ (fun _ => c a) (le_pull H β (hc a))).trans
      (congrArg (β ⁻¹ᵁ V a ⊓ ·) hD.symm)
  have hτ (a : I) : (β.app _).hom (τ a) = rs X' (β.preimage_mono inf_le_left) (s a) := by
    have e := congrArg (fun z => rs X' (le_inf (β.preimage_mono inf_le_right)
      (le_pull H β (inf_le_left.trans (hc a))) :
        β ⁻¹ᵁ (V a ⊓ D) ≤ β ⁻¹ᵁ D ⊓ (H.pull β).U fun _ => c a) (GlobalTheory.LB.coord z fun _ => c a)) ht
    rw [app_rs, rs_rs]
    exact ((GlobalTheory.LB.resG_appLE β _ _ _).symm.trans e).trans (rs_rs _ _ _)
  choose k₀ hk₀ using fun a => exists_lift_pow β hsq (hV a) inf_le_left (τ a) (s a) (hs a) (hτ a)
  obtain ⟨k₁, hk₁⟩ := (Set.finite_range k₀).bddAbove
  choose σ hσs hστ using fun a => hk₀ a (k₁ + 1) ((hk₁ ⟨a, rfl⟩).trans (Nat.le_succ _))
  have hbo (a : I) : X.basicOpen (σ a) = V a ⊓ D := by
    refine eq_of_preimage_eq β ((Scheme.preimage_basicOpen β _).trans ?_)
    rw [← hs, ← X'.basicOpen_pow (s a) (Nat.succ_pos k₁)]
    exact congrArg X'.basicOpen (hσs a)
  let g (a b : I) : Γ(X, V a ⊓ V b) := rs X (inf_le_inf (hc a) (hc b)) (H.g (c a) (c b)).val
  have key (p : I × I) : ∃ l₀ : ℕ, ∀ l, l₀ ≤ l → rs X inf_le_left (σ p.1) ^ l =
      (g p.1 p.2 ^ (k₁ + 1) * rs X inf_le_right (σ p.2)) ^ l := by
    obtain ⟨a, b⟩ := p
    have hsm : (β.app _).hom (g a b ^ (k₁ + 1) * rs X inf_le_right (σ b) -
        rs X inf_le_left (σ a)) = 0 := by
      have e := GlobalTheory.LB.sec_rel s₀ (fun _ => c a) (fun _ => c b) (W := β ⁻¹ᵁ (V a ⊓ V b))
        (le_pull H β (inf_le_left.trans (hc a))) (le_pull H β (inf_le_right.trans (hc b)))
        (le_inf (le_pull H β (inf_le_left.trans (hc a))) (le_pull H β (inf_le_right.trans (hc b))))
      erw [GlobalTheory.LB.resG_pull_g] at e
      rw [map_sub, map_mul, map_pow, app_rs, app_rs, app_rs, hσs, hσs, map_pow, map_pow, rs_rs, rs_rs,
        ← mul_pow, sub_eq_zero]
      exact congrArg (· ^ (k₁ + 1)) e.symm
    refine exists_pow_eq (O := V a ⊓ V b ⊓ D)
      (QuasiSeparatedSpace.inter_isCompact _ _ (V a).isOpen (hV a).isCompact (V b).isOpen
        (hV b).isCompact) inf_le_left _ _ (hsq _ _ _ hsm hsm) ?_ ?_
    · erw [Scheme.basicOpen_res]
      rw [hbo]
      exact inf_le_inf_left _ inf_le_right
    · have ea := congrArg (rs X (inf_le_inf_right D inf_le_left : V a ⊓ V b ⊓ D ≤ V a ⊓ D)) (hστ a)
      have eb := congrArg (rs X (inf_le_inf_right D inf_le_right : V a ⊓ V b ⊓ D ≤ V b ⊓ D)) (hστ b)
      rw [rs_rs, map_pow, rs_rs] at ea eb
      rw [map_mul, map_pow, rs_rs, rs_rs, rs_rs, ea, eb, ← mul_pow]
      exact congrArg (· ^ (k₁ + 1)) (SecOn.compat t (c a) (c b) _ _ _)
  choose l₀ hl₀ using key
  obtain ⟨l₁, hl₁⟩ := (Set.finite_range l₀).bddAbove
  obtain ⟨u, hu, -⟩ := SecOn.existsUnique_of_local (V := ⊤)
    (isLB_pw hH (((k₁ + 1) * (l₁ + 1) : ℕ) : ℤ)) V (fun _ => le_top) hcov c hc
    (fun a => σ a ^ (l₁ + 1)) fun a b => by
      have e := hl₀ (a, b) (l₁ + 1) ((hl₁ ⟨(a, b), rfl⟩).trans (Nat.le_succ _))
      rw [mul_pow, ← pow_mul] at e
      rw [map_pow, map_pow]
      refine e.trans (congrArg (· * _) ?_)
      change _ = rs X (inf_le_inf (hc a) (hc b)) (H.g (c a) (c b) ^ (((k₁ + 1) * (l₁ + 1) : ℕ) : ℤ)).val
      rw [zpow_natCast, Units.val_pow_eq_pow_val, map_pow]
  refine ⟨(k₁ + 1) * (l₁ + 1), Nat.succ_le_of_lt (by positivity), SecOn.topEquiv _ u, ?_⟩
  have hloc (a : I) : V a ⊓ nonzeroLocus (SecOn.topEquiv _ u) = V a ⊓ D := by
    rw [← basicOpen_rs_eq (SecOn.topEquiv _ u) (c a) (hc a), ← hbo,
      ← X.basicOpen_pow (σ a) (Nat.succ_pos l₁)]
    exact congrArg X.basicOpen ((rs_rs _ _ _).trans (hu a))
  ext x
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 (hcov (Set.mem_univ x))
  have e := SetLike.ext_iff.1 (hloc a) x
  exact ⟨fun h => (e.1 ⟨ha, h⟩).2, fun h => (e.2 ⟨ha, h⟩).2⟩

end GlobalTheory.SecPow
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.exists_union_translates' : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ M : Model R A, Strict M → ∃ G : Model R A, G.Irr ∧ (∀ a : (𝟙_ (Over (Sp K)) ⟶ A), GenIso M M (transl a).hom → (M.twist (transl a)).Le G) ∧ (∀ y : G.Y.left, ∃ (a : (𝟙_ (Over (Sp K)) ⟶ A)) (g : M.Y ⟶ G.Y), GenIso M M (transl a).hom ∧ IsOpenImmersion g.left ∧ (M.twist (transl a)).j ≫ g.left = G.j ∧ y ∈ Set.range g.left) ∧ ∀ z, DefAt (M.prod M) G (μ[A]) z := by
  first | exact @GlobalTheory.SS.exists_union_translates | exact GlobalTheory.SS.exists_union_translates | (intros; apply GlobalTheory.SS.exists_union_translates <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
namespace GlobalTheory.SS

def Places.sigma {k K : Type} [Field k] [Field K] [Algebra k K] {J : Type} [Finite J]
    (F : J → IntermediateField k K) (P : ∀ j, Places (F j) K) : Places k K where
  I := Σ j, (P j).I
  O := fun i => (P i.1).O i.2
  v := fun i => (P i.1).v i.2
  v_mul := fun i => (P i.1).v_mul i.2
  mem := fun i => (P i.1).mem i.2
  const := fun i c => (P i.1).const i.2 (algebraMap k (F i.1) c)
  fin := fun x => by
    refine (Set.finite_iUnion fun j => ((P j).fin x).image (Sigma.mk (β := fun j => (P j).I) j)).subset ?_
    rintro ⟨j, i⟩ hi
    exact Set.mem_iUnion.2 ⟨j, i, hi, rfl⟩
  sum := fun x => by
    classical
    have := Fintype.ofFinite J
    rw [finsum_eq_sum_of_support_subset (s := Finset.univ.sigma fun j => ((P j).fin x).toFinset),
      Finset.sum_sigma]
    · refine Finset.sum_eq_zero fun j _ => ?_
      rw [← (P j).sum x, finsum_eq_sum _ ((P j).fin x)]
    · rintro ⟨j, i⟩ hi
      simpa using hi

theorem isAlgebraic_of_forall_erase {k K : Type} [Field k] [Field K] [Algebra k K] {s : Set K}
    (hs : IsTranscendenceBasis k ((↑) : s → K)) {x : K}
    (h : ∀ t : s, IsAlgebraic (IntermediateField.adjoin k (s \ {(t : K)})) x) : IsAlgebraic k x := by
  have key : x ∈ (AlgebraicIndependent.matroid k K).closure ∅ := by
    have hB := AlgebraicIndependent.matroid_isBase_iff.2 hs
    rcases s.eq_empty_or_nonempty with rfl | hne
    · rw [hB.closure_eq]; trivial
    · have := hne.coe_sort
      have e : (⋂ t : s, s \ {(t : K)}) = ∅ := by
        refine Set.eq_empty_of_forall_notMem fun y hy => ?_
        rw [Set.mem_iInter] at hy
        exact (hy ⟨y, (hy this.some).1⟩).2 rfl
      rw [← e, hB.indep.closure_iInter_eq_biInter_closure_of_forall_subset fun _ => Set.diff_subset]
      refine Set.mem_iInter.2 fun t => ?_
      rw [AlgebraicIndependent.matroid_closure_eq]
      exact IntermediateField.isAlgebraic_adjoin_iff.1 (h t)
  rw [AlgebraicIndependent.matroid_closure_eq] at key
  have h2 : IsAlgebraic (IntermediateField.adjoin k (∅ : Set K)) x :=
    IntermediateField.isAlgebraic_adjoin_iff.2 key
  have : Algebra.IsAlgebraic k (IntermediateField.adjoin k (∅ : Set K)) :=
    (IntermediateField.isAlgebraic_adjoin_iff_isAlgebraic k K).2 (by simp)
  exact h2.restrictScalars k

theorem transcendental_erase {k K : Type} [Field k] [Field K] [Algebra k K] {s : Set K}
    (hs : IsTranscendenceBasis k ((↑) : s → K)) (t : s) :
    Transcendental (IntermediateField.adjoin k (s \ {(t : K)})) (t : K) := by
  have hB := AlgebraicIndependent.matroid_isBase_iff.2 hs
  intro h
  refine hB.indep.notMem_closure_diff_of_mem t.2 ?_
  rw [AlgebraicIndependent.matroid_closure_eq]
  exact IntermediateField.isAlgebraic_adjoin_iff.1 h

theorem exists_places_of_fg (k : Type) [Field k] [IsAlgClosed k] (K : Type) [Field K] [Algebra k K]
    (hfg : (⊤ : IntermediateField k K).FG) :
    ∃ Pl : Places k K, ∀ x : K, (∀ i, x ∈ Pl.O i) → x ∈ Set.range (algebraMap k K) := by
  have : Algebra.EssFiniteType k K := IntermediateField.fg_top_iff.mp hfg
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField k K
  have : Algebra.EssFiniteType (IntermediateField.adjoin k (s : Set K)) K :=
    Algebra.EssFiniteType.of_comp k _ K
  have hfin : FiniteDimensional (IntermediateField.adjoin k (s : Set K)) K :=
    Algebra.finite_of_essFiniteType_of_isAlgebraic
  have H : ∀ t : (s : Set K), ∃ Pl : Places (IntermediateField.adjoin k ((s : Set K) \ {(t : K)})) K,
      ∀ x : K, (∀ i, x ∈ Pl.O i) →
        IsAlgebraic (IntermediateField.adjoin k ((s : Set K) \ {(t : K)})) x := by
    intro t
    have e : IntermediateField.adjoin k (s : Set K) = (IntermediateField.adjoin
        (IntermediateField.adjoin k ((s : Set K) \ {(t : K)})) {(t : K)}).restrictScalars k := by
      rw [IntermediateField.adjoin_adjoin_left, Set.diff_union_of_subset (by simpa using t.2)]
    rw [e] at hsep hfin
    exact GlobalTheory.T.exists_productFormulaPlaces_function_field _ K t (transcendental_erase hs t) hfin hsep
  choose P hP using H
  refine ⟨Places.sigma _ P, fun x hx => ?_⟩
  have hx' : IsAlgebraic k x := isAlgebraic_of_forall_erase hs fun t => hP t x fun i => hx ⟨t, i⟩
  exact minpoly.mem_range_of_degree_eq_one k x
    (IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hx'.isIntegral))

end GlobalTheory.SS
end
end

section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.PsiQuadratic
variable {O : Type} [CommRing O] (N : NumD O)

theorem τ_self (y : N.X) : N.τ y y = N.ψ y ^ 2 * dbl N.θ N.σ (N.c y) := by
  have a := N.τ_add_left y (-y) y
  rw [add_neg_cancel, N.τ_zero_left, one_mul, N.c_neg] at a
  have b := N.ψ_add (-y) y
  rw [neg_add_cancel, N.ψ_zero] at b
  have a' := congrArg Additive.ofMul a
  have b' := congrArg Additive.ofMul b
  have c' := congrArg Additive.ofMul (N.even y)
  apply Additive.ofMul.injective
  simp only [dbl, sq, ofMul_mul, ofMul_div, ofMul_one] at a' b' c' ⊢
  linear_combination (norm := abel) -a' + b' + c'

theorem s_nsmul (g : N.Gt) (n : ℕ) (y : N.X) : g.s (n • y) * cubN N.θ n 1 (N.c y) g.b = g.s y ^ n := by
  induction n with
  | zero => simp [cubN]
  | succ n ih =>
    have m := g.mult (n • y) y
    rw [N.c_nsmul] at m
    rw [cubN] at ih
    rw [succ_nsmul, cubN, Finset.prod_range_succ, one_mul, pow_succ, ← ih, mul_right_comm _ _ (g.s y), ← m,
      ← mul_assoc, mul_right_comm]

theorem ψ_nsmul (n : ℕ) (y : N.X) : N.ψ (n • y) * mulq N.θ N.σ n (N.c y) = N.ψ y ^ (n ^ 2) := by
  induction n with
  | zero => simp [mulq]
  | succ n ih =>
    have a := s_nsmul N (N.io y) n y
    rw [N.io_s, N.io_s, N.io_b, τ_self, N.τ_symm] at a
    rw [mulq] at ih
    rw [succ_nsmul, N.ψ_add, mulq, Finset.prod_range_succ, show (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 by ring,
      pow_succ, pow_add, pow_mul, ← ih]
    rw [mul_pow] at a
    have a' := congrArg Additive.ofMul a
    apply Additive.ofMul.injective
    generalize (N.ψ y ^ 2) ^ n = u at a' ⊢
    generalize dbl N.θ N.σ (N.c y) ^ n = v at a' ⊢
    simp only [ofMul_mul, ofMul_div] at a' ⊢
    linear_combination (norm := abel) a'

theorem main : ∀ (O : Type) [CommRing O] (N : NumD O), ∀ (n : ℕ) (y : N.X),
    N.τ y y = N.ψ y ^ 2 * dbl N.θ N.σ (N.c y) ∧ N.ψ (n • y) * mulq N.θ N.σ n (N.c y) = N.ψ y ^ (n ^ 2) ∧
    ∀ (g : N.Gt), g.s (n • y) * cubN N.θ n 1 (N.c y) g.b = g.s y ^ n ∧
      (g ^ n).s y * cubN N.θ n 1 g.b (N.c y) = g.s y ^ n :=
  fun _ _ N n y => ⟨τ_self N y, ψ_nsmul N n y, fun g => ⟨s_nsmul N g n y, g.pow_s n y⟩⟩

end GlobalTheory.PsiQuadratic
end

section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.Ex.NumD.Int
variable {C : Type} [NormedField C] {N : NumD C} {q : QuadraticMap ℤ N.X ℝ}

theorem norm_cubN (h : N.Int q) (k : ℕ) (a b x : N.A) : ‖((cubN N.θ k a b x : Cˣ) : C)‖ = 1 := by
  rw [cubN, Units.coe_prod, norm_prod]
  exact Finset.prod_eq_one fun i _ => h.θ _ _ _

theorem norm_dbl (h : N.Int q) (x : N.A) : ‖((dbl N.θ N.σ x : Cˣ) : C)‖ = 1 := by
  rw [dbl, Units.val_div_eq_div_val, norm_div, h.θ, h.σ, div_one]

theorem norm_mulq (h : N.Int q) (n : ℕ) (x : N.A) : ‖((mulq N.θ N.σ n x : Cˣ) : C)‖ = 1 := by
  rw [mulq, Units.coe_prod, norm_prod]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [Units.val_div_eq_div_val, norm_div, h.norm_cubN, Units.val_pow_eq_pow_val, norm_pow, h.norm_dbl,
    one_pow, div_one]

theorem norm_τ (h : N.Int q) (a b : N.X) : ‖(N.τ a b : C)‖ = Real.exp (-QuadraticMap.polar q a b) := by
  rw [NumD.τ, Units.val_div_eq_div_val, Units.val_div_eq_div_val, norm_div, norm_div, h.ψ, h.ψ, h.ψ,
    ← Real.exp_sub, ← Real.exp_sub, QuadraticMap.polar]
  congr 1
  ring

theorem norm_pow_generators_eq_pow (h : N.Int q) (g : N.Gt) (k : ℕ) (χ : N.X) :
    ‖((g ^ k).s χ : C)‖ = ‖(g.s χ : C)‖ ^ k := by
  have := congrArg (fun u : Cˣ => ‖(u : C)‖) (g.pow_s k χ)
  simpa only [Units.val_mul, norm_mul, h.norm_cubN, mul_one, Units.val_pow_eq_pow_val, norm_pow] using this

theorem norm_rep_generators_eq_exp (h : N.Int q) {k : ℕ} (p : N.QT k) (hk : k ≠ 0) (χ : N.X) :
    ‖(p.1.2.s χ : C)‖ = Real.exp (-(QuadraticMap.polar q p.1.1.toAdd χ / k)) := by
  have e := h.norm_pow_generators_eq_pow p.1.2 k χ
  rw [N.mem_QT.1 p.2, NumD.io_s, h.norm_τ] at e
  refine (pow_left_inj₀ (norm_nonneg _) (Real.exp_pos _).le hk).1 ?_
  rw [← e, ← Real.exp_nat_mul]
  congr 1
  have : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk
  field_simp

theorem norm_wQ (h : N.Int q) {k : ℕ} (hk : Odd k) (p : N.QT k) :
    ‖(N.wQ p : C)‖ = Real.exp (-(q p.1.1.toAdd / k)) := by
  have hk0 : k ≠ 0 := hk.pos.ne'
  rw [NumD.wQ, NumB.wS]
  simp only [Units.val_div_eq_div_val, Units.val_mul, Units.val_pow_eq_pow_val, norm_div, norm_mul, norm_pow,
    h.norm_cubN, h.norm_dbl, h.norm_mulq, h.ψ, h.norm_rep_generators_eq_exp p hk0, mul_one, one_pow, div_one]
  rw [← Real.exp_nat_mul, ← Real.exp_sub, QuadraticMap.polar_self]
  congr 1
  obtain ⟨j, rfl⟩ := hk
  have e : (2 * j + 1 - 1) / 2 = j := by omega
  have : ((2 * j + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk0
  rw [e, two_smul]
  field_simp
  push_cast
  ring

theorem norm_txT (h : N.Int q) {m : ℕ} (hm : Odd m) (p : N.QT (m ^ 2)) (χ : N.X) :
    ‖N.txT m p χ‖ = Real.exp (-(q (p.1.1.toAdd + m • χ) / (m : ℝ) ^ 2)) * ‖N.th (N.c χ * p.1.2.b ^ m)‖ := by
  have hm0 : m ≠ 0 := hm.pos.ne'
  rw [NumD.txT, NumD.vt]
  simp only [Units.val_div_eq_div_val, Units.val_mul, norm_div, norm_mul, h.norm_mulq, h.ψ,
    h.norm_wQ hm.pow, h.norm_pow_generators_eq_pow, h.norm_rep_generators_eq_exp p (pow_ne_zero 2 hm0), div_one, NumD.Gt.pow_b]
  rw [← mul_assoc, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
  congr 2
  have e : q (p.1.1.toAdd + m • χ) =
      q p.1.1.toAdd + (m : ℝ) ^ 2 * q χ + m * QuadraticMap.polar q p.1.1.toAdd χ := by
    have a : QuadraticMap.polar q p.1.1.toAdd (m • χ) = m * QuadraticMap.polar q p.1.1.toAdd χ := by
      rw [← natCast_zsmul, QuadraticMap.polar_smul_right, zsmul_eq_mul, Int.cast_natCast]
    have b : q (m • χ) = (m : ℝ) ^ 2 * q χ := by
      rw [← natCast_zsmul, QuadraticMap.map_smul, zsmul_eq_mul]
      push_cast
      ring
    rw [← a, ← b, QuadraticMap.polar]
    ring
  have : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm0
  rw [e]
  push_cast
  field_simp
  ring

end GlobalTheory.Ex.NumD.Int

namespace GlobalTheory.Ex

theorem norm_QT_s_and_norm_txT : ∀ (C : Type) [NormedField C] (N : NumD C) (q : QuadraticMap ℤ N.X ℝ), N.Int q → (∀ (k : ℕ) (p : N.QT k), k ≠ 0 → ∀ χ, ‖(p.1.2.s χ : C)‖ = Real.exp (-(QuadraticMap.polar q p.1.1.toAdd χ / k))) ∧ ∀ (m : ℕ), Odd m → ∀ (p : N.QT (m ^ 2)) χ, ‖N.txT m p χ‖ = Real.exp (-(q (p.1.1.toAdd + m • χ) / (m : ℝ) ^ 2)) * ‖N.th (N.c χ * p.1.2.b ^ m)‖ :=
  fun _ _ _ _ h => ⟨fun _ p hk χ => h.norm_rep_generators_eq_exp p hk χ, fun _ hm p χ => h.norm_txT hm p χ⟩
end GlobalTheory.Ex
end
