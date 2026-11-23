module

public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam
public import CompanionTheory.AutomorphicTheory.SchurLimitBounds.SchurOrthogonality.SchurH
public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.CapelliEigenvalues.BetaAtInfinityZero
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle033
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

noncomputable section

namespace GlobalTheory.CompanionTheory.ZuckDecTens

section Lin

universe u

variable {O : Type u} {N : O → Type} [∀ o, AddCommGroup (N o)] [∀ o, Module ℂ (N o)]

theorem dec_comp {Hom : ∀ a b, (N a →ₗ[ℂ] N b) → Prop} (hc : IsLinCat N Hom) {A B P : Type} [Fintype A] [Fintype B]
    [Fintype P] (e : P ≃ A × B) {X : O} {Z : A → O} {S : A → B → O}
    {j : ∀ a, N (Z a) →ₗ[ℂ] N X} {q : ∀ a, N X →ₗ[ℂ] N (Z a)} (h : IsDec Hom X Z j q)
    {io : ∀ a b, N (S a b) →ₗ[ℂ] N (Z a)} {pr : ∀ a b, N (Z a) →ₗ[ℂ] N (S a b)}
    (h2 : ∀ a, IsDec Hom (Z a) (S a) (io a) (pr a)) :
    IsDec Hom X (fun p => S (e p).1 (e p).2) (fun p => j (e p).1 ∘ₗ io (e p).1 (e p).2)
      (fun p => pr (e p).1 (e p).2 ∘ₗ q (e p).1) := by
  exact {
    io_hom p := hc.comp _ _ _ _ _ ((h2 _).io_hom _) (h.io_hom _)
    pr_hom p := hc.comp _ _ _ _ _ (h.pr_hom _) ((h2 _).pr_hom _)
    sum := by
      rw [Equiv.sum_comp e (fun p : A × B => (j p.1 ∘ₗ io p.1 p.2) ∘ₗ (pr p.1 p.2 ∘ₗ q p.1)),
        Fintype.sum_prod_type, ← h.sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      ext x
      have := congrArg (fun f => j a (f (q a x))) (h2 a).sum

      simpa [map_sum] using this
    pr_io p := by
      ext x
      have h1 := LinearMap.congr_fun (h.pr_io (e p).1) (io (e p).1 (e p).2 x)
      have h3 := LinearMap.congr_fun ((h2 (e p).1).pr_io (e p).2) x
      simp only [LinearMap.comp_apply, LinearMap.id_apply] at h1 h3 ⊢
      rw [h1, h3]
    pr_io_ne p p' hne := by
      have hne' : e p ≠ e p' := fun hh => hne (e.injective hh)
      generalize e p = s at hne'
      generalize e p' = s' at hne'
      obtain ⟨a, b⟩ := s
      obtain ⟨a', b'⟩ := s'
      ext x
      by_cases ha : a = a'
      · subst ha
        have hb : b ≠ b' := fun hh => hne' (by rw [hh])
        have h1 := LinearMap.congr_fun (h.pr_io a) (io a b' x)
        have h3 := LinearMap.congr_fun ((h2 a).pr_io_ne b b' hb) x
        simp only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.zero_apply] at h1 h3 ⊢
        rw [h1, h3]
      · have h1 := LinearMap.congr_fun (h.pr_io_ne a a' ha) (io a' b' x)
        simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h1 ⊢
        rw [h1, map_zero]
  }

end Lin

variable {k r : ℕ}

theorem mAct_reindex {ι ι' V : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup V] [Module ℂ V] (e : ι' → ι) :
    (mAct ((1 : Matrix ι ι ℂ).submatrix e id) : (ι → V) →ₗ[ℂ] (ι' → V)) = LinearMap.funLeft ℂ V e := by
  refine LinearMap.ext fun x => funext fun c => ?_
  simp [mAct, LinearMap.funLeft_apply, Matrix.one_apply]

theorem hom_reindex (hM : MatHom) (F F' : FRep k r) (U : URep k r) (e : F'.ι ≃ F.ι)
    (h : ∀ g, F'.ρ g = (F.ρ g).submatrix e e) :
    IsHom (F, U) (F', U) (LinearMap.funLeft ℂ U.R.smSub e) := by
  have := hM k r F F' U ((1 : Matrix F.ι F.ι ℂ).submatrix e id) (fun g _ => by
    rw [h g, Matrix.submatrix_mul_equiv, Matrix.mul_one]
    have := Matrix.submatrix_mul_equiv (1 : Matrix F.ι F.ι ℂ) (F.ρ g) e (Equiv.refl _) id
    simpa using this)
  rwa [mAct_reindex] at this

theorem hom_cas (hL : HomLie) {X Y : Obj k r} {f : M X →ₗ[ℂ] M Y} (hX : X.1.OK) (hY : Y.1.OK) (hf : IsHom X Y f) :
    cas Y ∘ₗ f = f ∘ₗ cas X := by
  refine LinearMap.ext fun x => ?_
  have h := fun Z y => LinearMap.congr_fun (hL k r X Y f hX hY hf Z) y
  simp only [LinearMap.comp_apply] at h

  simp only [cas, LinearMap.comp_apply, LinearMap.sum_apply, map_sum, mul_apply_eq_comp, h]

theorem dec1 (hC : HomCat) (hM : MatHom) (hT : TensHom) (F F' : FRep k r) (U : URep k r) {A : Type} [Fintype A]
    (T : A → URep k r) {io : ∀ a, M (one (T a)) →ₗ[ℂ] M (F, U)} {pr : ∀ a, M (F, U) →ₗ[ℂ] M (one (T a))}
    (h : IsDec (N := M) IsHom (F, U) (fun a => one (T a)) io pr) :
    IsDec (N := M) IsHom (F.tens F', U) (fun a => (F', T a))
      (fun a => on1 (io a) ∘ₗ LinearMap.funLeft ℂ _ (Prod.snd : Unit × F'.ι → F'.ι))
      (fun a => LinearMap.funLeft ℂ _ (fun c : F'.ι => ((), c)) ∘ₗ on1 (pr a)) := by
  exact {
    io_hom a := (hC k r).comp _ ((triv k r).tens F', T a) _ _ _
      (hom_reindex hM F' ((triv k r).tens F') (T a) (Equiv.punitProd _) (fun g => by
        ext c d; simp))
      (hT k r _ _ F' _ _ _ (h.io_hom a)).1
    pr_hom a := (hC k r).comp _ ((triv k r).tens F', T a) _ _ _
      (hT k r _ _ F' _ _ _ (h.pr_hom a)).1
      (hom_reindex hM ((triv k r).tens F') F' (T a) (Equiv.punitProd _).symm (fun g => by
        ext c d; simp))
    sum := by
      refine LinearMap.ext fun x => funext fun p => ?_
      have := congrFun (LinearMap.congr_fun h.sum (fun c => x (c, p.2))) p.1
      rw [LinearMap.sum_apply, Finset.sum_apply] at this ⊢
      exact this
    pr_io a := by
      refine LinearMap.ext fun x => funext fun c => ?_
      exact congrFun (LinearMap.congr_fun (h.pr_io a) (fun _ => x c)) ()
    pr_io_ne a a' hne := by
      refine LinearMap.ext fun x => funext fun c => ?_
      exact congrFun (LinearMap.congr_fun (h.pr_io_ne a a' hne) (fun _ => x c)) ()
  }

theorem dec2 (hC : HomCat) (hM : MatHom) (hT : TensHom) (F F' : FRep k r) (U : URep k r) {A : Type} [Fintype A]
    (T : A → URep k r) {io : ∀ a, M (one (T a)) →ₗ[ℂ] M (F', U)} {pr : ∀ a, M (F', U) →ₗ[ℂ] M (one (T a))}
    (h : IsDec (N := M) IsHom (F', U) (fun a => one (T a)) io pr) :
    IsDec (N := M) IsHom (F.tens F', U) (fun a => (F, T a))
      (fun a => on2 (io a) ∘ₗ LinearMap.funLeft ℂ _ (Prod.fst : F.ι × Unit → F.ι))
      (fun a => LinearMap.funLeft ℂ _ (fun c : F.ι => (c, ())) ∘ₗ on2 (pr a)) := by
  exact {
    io_hom a := (hC k r).comp _ (F.tens (triv k r), T a) _ _ _
      (hom_reindex hM F (F.tens (triv k r)) (T a) (Equiv.prodPUnit _) (fun g => by
        ext c d; simp))
      (hT k r _ _ F _ _ _ (h.io_hom a)).2
    pr_hom a := (hC k r).comp _ (F.tens (triv k r), T a) _ _ _
      (hT k r _ _ F _ _ _ (h.pr_hom a)).2
      (hom_reindex hM (F.tens (triv k r)) F (T a) (Equiv.prodPUnit _).symm (fun g => by
        ext c d; simp))
    sum := by
      refine LinearMap.ext fun x => funext fun p => ?_
      have := congrFun (LinearMap.congr_fun h.sum (fun c => x (p.1, c))) p.2
      rw [LinearMap.sum_apply, Finset.sum_apply] at this ⊢
      exact this
    pr_io a := by
      refine LinearMap.ext fun x => funext fun c => ?_
      exact congrFun (LinearMap.congr_fun (h.pr_io a) (fun _ => x c)) ()
    pr_io_ne a a' hne := by
      refine LinearMap.ext fun x => funext fun c => ?_
      exact congrFun (LinearMap.congr_fun (h.pr_io_ne a a' hne) (fun _ => x c)) ()
  }

theorem decTens : HomCat → MatHom → TensHom → HomLie → OKTriv → DecTens := by
  intro hC hM hT hL hO k r F F' U hF hF'
  refine ⟨fun A B _ _ T S c ⟨io, pr, h⟩ h2 hc => ?_, fun A B _ _ T S c ⟨io, pr, h⟩ h2 hc => ?_⟩
  · choose io2 pr2 h2 using h2
    refine ⟨_, _, dec_comp (hC k r) (Equiv.refl (A × B)) (S := fun a b => one (S (a, b)))
      (dec1 hC hM hT F F' U T h) h2, fun p => ?_⟩
    have h3 := hom_cas hL (X := one (T p.1)) (Y := (F, U)) (hO k r) hF (h.io_hom p.1)
    rw [hc, LinearMap.comp_smul, LinearMap.comp_id] at h3
    refine LinearMap.ext fun x => funext fun s => ?_
    exact congrFun (LinearMap.congr_fun h3 (fun _ => io2 p.1 p.2 x s.2)) s.1
  · choose io2 pr2 h2 using h2
    refine ⟨_, _, dec_comp (hC k r) (Equiv.prodComm A B) (S := fun b a => one (S (a, b)))
      (dec2 hC hM hT F F' U T h) h2, fun p => ?_⟩
    have h3 := hom_cas hL (X := one (T p.2)) (Y := (F', U)) (hO k r) hF' (h.io_hom p.2)
    rw [hc, LinearMap.comp_smul, LinearMap.comp_id] at h3
    refine LinearMap.ext fun x => funext fun s => ?_
    exact congrFun (LinearMap.congr_fun h3 (fun _ => io2 p.2 p.1 x s.1)) s.2

end GlobalTheory.CompanionTheory.ZuckDecTens

end
end

section

open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

noncomputable section

namespace GlobalTheory.CompanionTheory.ZuckToRaw

variable {k r : ℕ}

theorem dsigW_zero' (R : Rep k r) (W : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) :
    PI.UpqRep.dsigW (k := k) (r := r) R.σ W (0 : R.H) = 0 := by
  induction W with
  | nil => rfl
  | cons X W ih =>
    show PI.UpqRep.dsig (k := k) (r := r) R.σ X (PI.UpqRep.dsigW (k := k) (r := r) R.σ W 0) = 0
    rw [ih]
    simp [PI.UpqRep.dsig]


open Classical in
def extZ {R R' : Rep k r} (f : R.smSub →ₗ[ℂ] R'.smSub) (y : R.H) : R'.H :=
  if h : y ∈ R.smSub then (f ⟨y, h⟩ : R'.H) else 0

theorem extZ_coe {R R' : Rep k r} (f : R.smSub →ₗ[ℂ] R'.smSub) (y : R.smSub) :
    extZ f (y : R.H) = (f y : R'.H) := by
  simp only [extZ, dite_eq_left y.2]

theorem smMap_extZ {R R' : Rep k r} (f : R.smSub →ₗ[ℂ] R'.smSub)
    (hf : ∀ W, LieWd k r W → ∃ (C : ℝ) (Ws : List (List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))), (∀ W' ∈ Ws, LieWd k r W') ∧
      ∀ y : R.smSub, ‖PI.UpqRep.dsigW (k := k) (r := r) R'.σ W (f y : R'.H)‖ ≤
        C * (Ws.map fun W' => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W' (y : R.H)‖).sum) :
    SmMap R R' (extZ f) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hv
    have := extZ_coe f ⟨v, hv⟩
    rw [show extZ f v = _ from this]
    exact (f _).2
  · intro v hv w hw
    have h1 := extZ_coe f ⟨v, hv⟩
    have h2 := extZ_coe f ⟨w, hw⟩
    have h3 := extZ_coe f (⟨v, hv⟩ + ⟨w, hw⟩)
    rw [show extZ f v = _ from h1, show extZ f w = _ from h2, show extZ f (v + w) = _ from h3, map_add (f := _)]
    rfl
  · intro a v hv
    have h1 := extZ_coe f ⟨v, hv⟩
    have h3 := extZ_coe f (a • ⟨v, hv⟩)
    rw [show extZ f v = _ from h1, show extZ f (a • v) = _ from h3, map_smul]
    rfl
  · intro W hW
    obtain ⟨C, Ws, h1, h2⟩ := hf W hW
    refine ⟨C, Ws, h1, fun v hv => ?_⟩
    have h3 := extZ_coe f ⟨v, hv⟩
    show ‖PI.UpqRep.dsigW (k := k) (r := r) R'.σ W (extZ f v)‖ ≤ _
    rw [show extZ f v = _ from h3]
    exact h2 ⟨v, hv⟩

theorem sn_single (X : Obj k r) (W : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (c : X.1.ι) (v : X.2.R.smSub) :
    sn X W (Pi.single c v) = ‖PI.UpqRep.dsigW (k := k) (r := r) X.2.R.σ W (v : X.2.R.H)‖ := by
  unfold sn
  rw [Finset.sum_eq_single c]
  · simp
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, ZeroMemClass.coe_zero, dsigW_zero', norm_zero]
  · simp

theorem le_sn (X : Obj k r) (W : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (c : X.1.ι) (x : M X) :
    ‖PI.UpqRep.dsigW (k := k) (r := r) X.2.R.σ W (x c : X.2.R.H)‖ ≤ sn X W x :=
  Finset.single_le_sum (f := fun c => ‖PI.UpqRep.dsigW (k := k) (r := r) X.2.R.σ W (x c : X.2.R.H)‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_univ c)

def coord {X Y : Obj k r} (f : M X →ₗ[ℂ] M Y) (d : Y.1.ι) (c : X.1.ι) : X.2.R.smSub →ₗ[ℂ] Y.2.R.smSub :=
  LinearMap.proj d ∘ₗ f ∘ₗ LinearMap.single ℂ (fun _ : X.1.ι => X.2.R.smSub) c

theorem coord_apply {X Y : Obj k r} (f : M X →ₗ[ℂ] M Y) (d : Y.1.ι) (c : X.1.ι) (v : X.2.R.smSub) :
    coord f d c v = f (Pi.single c v) d := rfl

theorem smMap_coord {X Y : Obj k r} {f : M X →ₗ[ℂ] M Y} (hf : IsHom X Y f) (d : Y.1.ι) (c : X.1.ι) :
    SmMap X.2.R Y.2.R (extZ (coord f d c)) := by
  refine smMap_extZ _ fun W hW => ?_
  obtain ⟨C, Ws, h1, h2⟩ := hf.cont W hW
  refine ⟨C, Ws, h1, fun y => ?_⟩
  have := (le_sn Y W d _).trans (h2 (Pi.single c y))
  simpa only [sn_single, coord_apply] using this

theorem sum_coord {X Y : Obj k r} (f : M X →ₗ[ℂ] M Y) (d : Y.1.ι) (x : M X) :
    ∑ c, extZ (coord f d c) (x c : X.2.R.H) = (f x d : Y.2.R.H) := by
  simp only [extZ_coe, coord_apply]

  conv_rhs => rw [← Finset.univ_sum_single x, map_sum, Finset.sum_apply]
  simp

theorem act_coe (X : Obj k r) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ GG k r) (x : M X) (c : X.1.ι) :
    (CompanionTheory.Zuck.act X g x c : X.2.R.H) = BranchingSupport.act X.1.ρ X.2.R g (fun d => (x d : X.2.R.H)) c := by
  simp [CompanionTheory.Zuck.act, BranchingSupport.act, mAct, dOp, URep.sig_coe _ hg]

theorem one_coord {U : URep k r} {Y : Obj k r} (f : M (one U) →ₗ[ℂ] M Y) (d : Y.1.ι) (x : M (one U)) :
    extZ (coord f d ()) (x () : U.R.H) = (f x d : Y.2.R.H) := by
  rw [← sum_coord f d x]
  simp

theorem act_one (U : URep k r) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ GG k r) (x : M (one U)) :
    (CompanionTheory.Zuck.act (one U) g x () : U.R.H) = U.R.σ g (x ()) := by
  rw [act_coe (one U) hg]
  simp [BranchingSupport.act]

theorem toRaw : ToRaw := by
  rintro k r F U κ _ _ T ⟨io, pr, h⟩
  refine ⟨fun a c => extZ (coord (io a) c ()), fun a c => extZ (coord (pr a) () c), ?_⟩
  refine ⟨fun I c => smMap_coord (h.io_hom I) c (), fun I c => smMap_coord (h.pr_hom I) () c,
    fun I g hg y hy => ?_, fun I g hg x hx => ?_, fun x hx c => ?_, fun I y hy => ?_, fun I J hIJ y hy => ?_⟩
  · let y' : M (one (T I)) := fun _ => ⟨y, hy⟩
    funext c
    have e1 : (T I).R.σ g y = (CompanionTheory.Zuck.act (one (T I)) g y' () : (T I).R.H) := (act_one (T I) hg y').symm
    have e2 : ∀ d, extZ (coord (io I) d ()) y = (io I y' d : U.R.H) := fun d => one_coord (io I) d y'
    have e3 := LinearMap.congr_fun ((h.io_hom I).equiv g hg) y'
    simp only [LinearMap.comp_apply] at e3
    simp only [e2]
    rw [e1, one_coord, e3]
    exact act_coe (F, U) hg _ c
  · let x' : M (F, U) := fun c => ⟨x c, hx c⟩
    have e1 : ∀ c, BranchingSupport.act F.ρ U.R g x c = (CompanionTheory.Zuck.act (F, U) g x' c : U.R.H) :=
      fun c => (act_coe (F, U) hg x' c).symm
    have e2 : ∑ c, extZ (coord (pr I) () c) (x c) = (pr I x' () : (T I).R.H) := sum_coord (pr I) () x'
    have e3 := LinearMap.congr_fun ((h.pr_hom I).equiv g hg) x'
    simp only [LinearMap.comp_apply] at e3
    simp only [e1]
    rw [e2, ← act_one (T I) hg, ← e3]
    exact sum_coord (pr I) () _
  · let x' : M (F, U) := fun c => ⟨x c, hx c⟩
    have e2 : ∀ I, ∑ c, extZ (coord (pr I) () c) (x c) = (pr I x' () : (T I).R.H) :=
      fun I => sum_coord (pr I) () x'
    have e4 : ∀ I, extZ (coord (io I) c ()) (pr I x' () : (T I).R.H) = (io I (pr I x') c : U.R.H) :=
      fun I => one_coord (io I) c _
    have e3 := congrFun (LinearMap.congr_fun h.sum x') c
    simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply, LinearMap.id_apply] at e3
    simp only [e2, e4]
    rw [← Submodule.coe_sum, e3]
  · let y' : M (one (T I)) := fun _ => ⟨y, hy⟩
    have e2 : ∀ d, extZ (coord (io I) d ()) y = (io I y' d : U.R.H) := fun d => one_coord (io I) d y'
    have e3 := LinearMap.congr_fun (h.pr_io I) y'
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at e3
    simp only [e2]
    refine (sum_coord (pr I) () (io I y')).trans ?_
    rw [e3]
  · let y' : M (one (T J)) := fun _ => ⟨y, hy⟩
    have e2 : ∀ d, extZ (coord (io J) d ()) y = (io J y' d : U.R.H) := fun d => one_coord (io J) d y'
    have e3 := LinearMap.congr_fun (h.pr_io_ne I J hIJ) y'
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at e3
    simp only [e2]
    refine (sum_coord (pr I) () (io J y')).trans ?_
    rw [e3]
    rfl

end GlobalTheory.CompanionTheory.ZuckToRaw

end
end

section

open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

noncomputable section

namespace GlobalTheory.CompanionTheory.ZuckTransport

open PI.UpqRep CompanionTheory.LimBd.SchurHpk

theorem dot_conj {n : ℕ} (P a Q : Matrix (Fin n) (Fin n) ℂ) (u x : Fin n → ℂ) :
    u ⬝ᵥ ((P * a * Q) *ᵥ x) = (u ᵥ* P) ⬝ᵥ (a *ᵥ (Q *ᵥ x)) := by
  rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem dot_expand {n : ℕ} (a : Matrix (Fin n) (Fin n) ℂ) (u x : Fin n → ℂ) :
    u ⬝ᵥ (a *ᵥ x) = ∑ p : Fin n × Fin n, u p.1 * x p.2 * a p.1 p.2 := by
  rw [Fintype.sum_prod_type]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}

theorem kfin_smul {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)} {v : H} (c : ℂ)
    (hv : IsKFinHpk (k := k) (r := r) σ v) : IsKFinHpk (k := k) (r := r) σ (c • v) := by
  obtain ⟨S, h1, h2, h3⟩ := hv
  exact ⟨S, h1, S.smul_mem c h2, h3⟩

theorem transport (U : URep k r) {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : IsCayleyU k r ε P)
    (q : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hq : ∀ g, q (P * g * P⁻¹) = P * q g * P⁻¹)
    (ν : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℝ)
    (Sm : Finset (Fin (2 * r + k + 1))) (Hs : Fin (2 * r + k + 1) → Type)
    [∀ s, NormedAddCommGroup (Hs s)] [∀ s, InnerProductSpace ℂ (Hs s)] [∀ s, CompleteSpace (Hs s)]
    (σs : ∀ s, Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Hs s →L[ℂ] Hs s))
    (hSm : ∀ s, s ∈ Sm ↔ IsHCParam (ν s))
    (ds : ∀ s ∈ Sm, IsHCParam (ν s) ∧ IsDS ε (ν s) (σs s))
    (toSum : ∀ (v w : U.R.H) (x y : Fin (2 * r + k + 1) → ℂ), IsKFin ε (fun g => U.R.σ (P⁻¹ * g * P)) v →
      IsKFin ε (fun g => U.R.σ (P⁻¹ * g * P)) w →
      ∃ (ι : Type) (_ : Fintype ι) (sI : ι → Fin (2 * r + k + 1)) (vI wI : ∀ i, Hs (sI i)),
        (∀ i, sI i ∈ Sm ∧ IsKFin ε (σs (sI i)) (vI i) ∧ IsKFin ε (σs (sI i)) (wI i)) ∧
        ∀ g ∈ UJset ε, ⟪w, U.R.σ (P⁻¹ * g * P) v⟫_ℂ * (star y ⬝ᵥ (q g *ᵥ x)) =
          ∑ i, ⟪wI i, σs (sI i) g (vI i)⟫_ℂ)
    (ofSum : ∀ s ∈ Sm, ∀ v w : Hs s, IsKFin ε (σs s) v → IsKFin ε (σs s) w →
      ∃ (ι : Type) (_ : Fintype ι) (vI wI : ι → U.R.H) (xI yI : ι → Fin (2 * r + k + 1) → ℂ),
        (∀ i, IsKFin ε (fun g => U.R.σ (P⁻¹ * g * P)) (vI i) ∧ IsKFin ε (fun g => U.R.σ (P⁻¹ * g * P)) (wI i)) ∧
        ∀ g ∈ UJset ε, ⟪w, σs s g v⟫_ℂ =
          ∑ i, ⟪wI i, U.R.σ (P⁻¹ * g * P) (vI i)⟫_ℂ * (star (yI i) ⬝ᵥ (q g *ᵥ xI i))) :
    ∃ T : {s // IsHCParam (ν s)} → URep k r, (∀ s, (T s).R.IsDS ε (ν s)) ∧
      (∀ v w, U.R.KFin v → U.R.KFin w → ∀ c d, ∃ (I : Type) (_ : Fintype I) (s : I → {s // IsHCParam (ν s)})
        (y y' : ∀ i, (T (s i)).R.H),
        ∀ g ∈ GG k r, ⟪w, U.R.σ g v⟫_ℂ * q g c d = ∑ i, ⟪y' i, (T (s i)).R.σ g (y i)⟫_ℂ) ∧
      ∀ s, ∃ y : (T s).R.H, y ≠ 0 ∧ ∃ (I : Type) (_ : Fintype I) (v w : I → U.R.H)
        (c d : I → Fin (2 * r + k + 1)), (∀ i, U.R.KFin (v i) ∧ U.R.KFin (w i)) ∧
        ∀ g ∈ GG k r, ⟪y, (T s).R.σ g y⟫_ℂ = ∑ i, ⟪w i, U.R.σ g (v i)⟫_ℂ * q g (c i) (d i) := by
  have hk := fun v => CompanionTheory.CapEig.kfin_iff k r ε P U.R.H U.R.σ v hP
  have hds : ∀ s : {s // IsHCParam (ν s)}, IsDSHpk k r ε (ν s) (fun x => σs s (P * x * P⁻¹)) := fun s =>
    ⟨P, hP, by
      have e : (fun g => (fun x => σs s (P * x * P⁻¹)) (P⁻¹ * g * P)) = σs s := funext fun g => by
        simp only [forth_back hP.1]
      rw [e]
      exact (ds s ((hSm s).2 s.2)).2⟩
  refine ⟨fun s => ⟨⟨Hs s, fun x => σs s (P * x * P⁻¹)⟩, isURepOn_of_ds (hds s)⟩, fun s => ⟨s.2, hds s⟩,
    fun v w hv hw c d => ?_, fun s => ?_⟩
  · obtain ⟨ι, _, sI, vI, wI, hI, hsum⟩ := toSum v w (P *ᵥ Pi.single d 1) (star (Pi.single c 1 ᵥ* P⁻¹))
      ((hk v).1 hv) ((hk w).1 hw)
    refine ⟨ι, inferInstance, fun i => ⟨sI i, (hSm _).1 (hI i).1⟩, vI, wI, fun g hg => ?_⟩
    have := hsum _ (forth_mem hP.1 hg)
    rw [back_forth hP.1, hq, star_star, dot_conj, Matrix.vecMul_vecMul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_assoc (q g), inv_mul_P hP.1, Matrix.mul_one, Matrix.vecMul_one, single_one_dotProduct,
      Matrix.mulVec_single_one] at this
    exact this
  · have hs := (hSm s).2 s.2
    obtain ⟨S, hS, hSK, -, ⟨y, hyS, hy0, -⟩, -⟩ := (ds s hs).2.2.2.2.2.2.1
    have hy : IsKFin ε (σs s) y := ⟨S, hS, hyS, hSK⟩
    obtain ⟨ι, _, vI, wI, xI, yI, hI, hsum⟩ := ofSum s hs y y hy hy
    refine ⟨y, hy0, ι × Fin (2 * r + k + 1) × Fin (2 * r + k + 1), inferInstance,
      fun p => ((star (yI p.1) ᵥ* P) p.2.1 * (P⁻¹ *ᵥ xI p.1) p.2.2) • vI p.1, fun p => wI p.1,
      fun p => p.2.1, fun p => p.2.2, fun p => ⟨kfin_smul _ ((hk _).2 (hI p.1).1), (hk _).2 (hI p.1).2⟩,
      fun g hg => ?_⟩
    have := hsum _ (forth_mem hP.1 hg)
    refine this.trans ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [back_forth hP.1, hq, dot_conj, dot_expand, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_smul, inner_smul_right]
    ring

theorem zuckerman_hypothesis_holds : ZuckH := by
  intro t hZ k r ε μ U b h hU hg hlt
  obtain ⟨hμ, P, hP, hτ⟩ := hU
  obtain ⟨⟨X, hX⟩, ⟨Y, hY⟩⟩ := hZ _ ε μ U.R.H _ hμ hτ h hg hlt
  cases b
  · exact transport U hP (fun g => g) (fun _ => rfl) (shift false μ) X.Sm X.Hs X.σs hX X.ds X.toSum X.ofSum
  · have hi : ∀ g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, (P * g * P⁻¹)⁻¹ = P * g⁻¹ * P⁻¹ :=
      fun g => by
        rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev,
          Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP.1.1), Matrix.mul_assoc]
    obtain ⟨T, h1, h2, h3⟩ :=
      transport U hP (fun g => g⁻¹) hi (shift true μ) Y.Sm Y.Hs Y.σs hY Y.ds Y.toSum Y.ofSum
    refine ⟨T, h1, fun v w hv hw c d => h2 v w hv hw d c, fun s => ?_⟩
    obtain ⟨y, hy, I, _, v, w, c, d, hk, he⟩ := h3 s
    exact ⟨y, hy, I, inferInstance, v, w, d, c, hk, he⟩

end GlobalTheory.CompanionTheory.ZuckTransport

end
end

section

open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.boundary_creation_anticommutator : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V) (e : Pos n),
    (bd (allT n) E * cre e + cre e * bd (allT n) E : Module.End ℂ (Cn n V)) = lF E e.1.1 e.1.2 := by
  first | exact @GlobalTheory.CompanionTheory.Cartan.cartan | exact GlobalTheory.CompanionTheory.Cartan.cartan | (intros; apply GlobalTheory.CompanionTheory.Cartan.cartan <;> assumption)
end

end

section

@[expose] public section

open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

theorem _root_.GlobalTheory.T.decomposition_of_tensor_from_hom_laws : HomCat → MatHom → TensHom → HomLie → OKTriv → DecTens := by
  first | exact @GlobalTheory.CompanionTheory.ZuckDecTens.decTens | exact GlobalTheory.CompanionTheory.ZuckDecTens.decTens | (intros; apply GlobalTheory.CompanionTheory.ZuckDecTens.decTens <;> assumption)

end
end

section

@[expose] public section

open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

theorem _root_.GlobalTheory.T.ToRawComplex : ToRaw := by
  first | exact @GlobalTheory.CompanionTheory.ZuckToRaw.toRaw | exact GlobalTheory.CompanionTheory.ZuckToRaw.toRaw | (intros; apply GlobalTheory.CompanionTheory.ZuckToRaw.toRaw <;> assumption)

end
end

section

@[expose] public section

open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

theorem _root_.GlobalTheory.T.zuckerman_hypothesis : ZuckH := by
  first | exact @GlobalTheory.CompanionTheory.ZuckTransport.zuckerman_hypothesis_holds | exact GlobalTheory.CompanionTheory.ZuckTransport.zuckerman_hypothesis_holds | (intros; apply GlobalTheory.CompanionTheory.ZuckTransport.zuckerman_hypothesis_holds <;> assumption)

end
end
