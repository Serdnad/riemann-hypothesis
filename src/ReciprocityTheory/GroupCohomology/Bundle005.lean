module

public import ReciprocityTheory.GroupCohomology.Bundle003
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.GroupCohomology.Bundle002
public import ReciprocityTheory.GroupCohomology.LocaliseA

@[expose] public section

section

namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Cx Function

universe u

theorem localise_holds : LocaliseStatement.{u} := by
  intro R _ G _ _ _ _ t L V j hφ hu he hcov n
  obtain ⟨e, he⟩ := he
  have localiseCx {A B : Cx R} (f : Hom A B) (hj : ∀ k, Injective (f.f k))
      (ht : ∀ k, Bijective fun x : B.X k => t • x)
      (hc : ∀ k (x : B.X k), ∃ (m : ℕ) (y : A.X k), f.f k y = t ^ m • x)
      (k : ℕ) : IsLocalizedModule (Submonoid.powers t) (f.H k) := by
    constructor
    · rintro ⟨_, m, rfl⟩
      show IsUnit (algebraMap R (Module.End R (B.H k)) (t ^ m))
      rw [map_pow]
      exact ((Module.End.isUnit_iff _).2 (bij_H_of_bij t ht k)).pow m
    · intro y
      induction y using H_ind with
      | h x hx =>
        obtain ⟨m, a, ha⟩ := hc k x
        have ha0 : A.d k a = 0 := (hj (k + 1)) (by
          rw [f.comm, ha, cx_smul_d, hx, smul_zero, map_zero])
        refine ⟨(A.cls k a ha0, ⟨t ^ m, m, rfl⟩), ?_⟩
        show (t ^ m) • B.cls k x hx = f.H k (A.cls k a ha0)
        rw [cls_smul, Hom.H_cls]
        exact cls_congr _ _ ha.symm
    · have key : ∀ z : A.H k, f.H k z = 0 → ∃ c : Submonoid.powers t, c • z = 0 := by
        intro z hz
        induction z using H_ind with
        | h g hg =>
          rw [Hom.H_cls, cls_eq_zero_iff] at hz
          cases k with
          | zero =>
            have h0 : f.f 0 g = 0 := hz
            refine ⟨1, ?_⟩
            rw [one_smul, cls_eq_zero_iff]
            exact (hj 0) (h0.trans (map_zero _).symm)
          | succ k =>
            obtain ⟨h, hh⟩ := hz
            obtain ⟨m, a, ha⟩ := hc k h
            refine ⟨⟨t ^ m, m, rfl⟩, ?_⟩
            show (t ^ m) • A.cls (k + 1) g hg = 0
            rw [cls_smul, cls_eq_zero_iff]
            refine ⟨a, (hj (k + 1)) ?_⟩
            rw [f.comm, ha, cx_smul_d, hh, map_smul]
      intro x₁ x₂ h
      obtain ⟨c, hc'⟩ := key (x₁ - x₂) (by rw [map_sub, h, sub_self])
      exact ⟨c, sub_eq_zero.mp (by simpa only [smul_sub] using hc')⟩
  refine localiseCx j.hom ?_ ?_ ?_ n
  · intro k x y hxy
    rcases j with ⟨φ, u, hφc, huc, heq⟩
    dsimp only at hφ hu
    subst hφ
    refine Subtype.ext (funext fun g => hu.injective ?_)
    exact congrFun (congrArg Subtype.val hxy) g
  · intro k
    constructor
    · intro x y hxy
      refine Subtype.ext (funext fun g => e.injective ?_)
      rw [he, he]
      exact congrFun (congrArg Subtype.val hxy) g
    · intro y
      refine ⟨⟨fun g => e.symm (y.1 g), e.symm.continuous.comp y.2⟩, Subtype.ext (funext fun g => ?_)⟩
      show t • e.symm (y.1 g) = y.1 g
      rw [← he, e.apply_symm_apply]
  · intro k x
    rcases j with ⟨φ, u, hφc, huc, heq⟩
    dsimp only at hφ hu hcov
    subst hφ
    have hx : Continuous x.1 := x.2
    let O : ℕ → Set (Fin k → G) := fun m => x.1 ⁻¹' ((fun v : V.V => t ^ m • v) ⁻¹' Set.range u)
    have hO : ∀ m, IsOpen (O m) := fun m =>
      ((hu.isOpen_range).preimage (continuous_const_smul _)).preimage hx
    have hmono : Monotone O := by
      refine monotone_nat_of_le_succ fun m g hg => ?_
      obtain ⟨l, hl⟩ := hg
      refine ⟨t • l, ?_⟩
      simp only at hl ⊢
      rw [map_smul, hl, pow_succ', mul_smul]
    have hcover : (Set.univ : Set (Fin k → G)) ⊆ ⋃ m, O m := by
      intro g _
      obtain ⟨m, l, hl⟩ := hcov (x.1 g)
      exact Set.mem_iUnion.2 ⟨m, l, hl⟩
    obtain ⟨m, hm⟩ := isCompact_univ.elim_directed_cover O hO hcover hmono.directed_le
    have hy : ∀ g, u (invFun u (t ^ m • x.1 g)) = t ^ m • x.1 g := fun g =>
      invFun_eq (hm (Set.mem_univ g))
    have hyc : Continuous fun g => invFun u (t ^ m • x.1 g) := by
      rw [hu.isEmbedding.continuous_iff]
      have : (u ∘ fun g => invFun u (t ^ m • x.1 g)) = fun g => t ^ m • x.1 g := funext hy
      rw [this]
      exact hx.const_smul _
    refine ⟨m, ⟨fun g => invFun u (t ^ m • x.1 g), hyc⟩, Subtype.ext (funext fun g => ?_)⟩
    exact hy g

end ReciprocityTheory.Coh
end

section

namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Cx Function

noncomputable section

universe u

namespace HomogeneousCochainIso

theorem hgi_val {n : ℕ} (i : Fin (n + 3)) (j : Fin (n + 2)) :
    ((i.succAbove j : ℕ) + (j.predAbove i : ℕ) = i + j + 1) ∨
      ((i.succAbove j : ℕ) + (j.predAbove i : ℕ) + 1 = i + j) := by
  simp only [Fin.succAbove, Fin.predAbove, Fin.lt_def, Fin.val_castSucc, apply_dite Fin.val,
    Fin.val_pred, Fin.coe_castPred, dite_eq_ite, apply_ite Fin.val, Fin.val_succ]
  split_ifs <;> omega

theorem hgi_sign {n : ℕ} (i : Fin (n + 3)) (j : Fin (n + 2)) :
    (-1 : ℤ) ^ (i.succAbove j : ℕ) * (-1) ^ (j.predAbove i : ℕ) = -((-1) ^ (i : ℕ) * (-1) ^ (j : ℕ)) := by
  rw [← pow_add, ← pow_add]
  rcases hgi_val i j with h | h
  · rw [h, pow_succ]; ring
  · rw [← h, pow_succ]; ring

theorem hd_hd {V X : Type u} [AddCommGroup V] (n : ℕ) (F : (Fin (n + 1) → X) → V) :
    hd (n + 1) (hd n F) = 0 := by
  funext x
  simp only [hd, Finset.smul_sum, smul_smul, Pi.zero_apply]
  rw [← Finset.sum_product' (s := Finset.univ) (t := Finset.univ)
    (f := fun (i : Fin (n + 3)) (j : Fin (n + 2)) => ((-1 : ℤ) ^ (i : ℕ) * (-1) ^ (j : ℕ)) • F fun k => x (i.succAbove (j.succAbove k)))]
  refine Finset.sum_involution (fun p _ => (p.1.succAbove p.2, p.2.predAbove p.1)) ?_ ?_ ?_ ?_
  · rintro ⟨i, j⟩ _
    simp only [Fin.succAbove_succAbove_succAbove_predAbove, hgi_sign, neg_smul]
    exact add_neg_cancel _
  · rintro ⟨i, j⟩ _ _ h
    simp only [Prod.mk.injEq] at h
    exact Fin.succAbove_ne i j h.1
  · intros; exact Finset.mem_univ _
  · rintro ⟨i, j⟩ _
    simp only [Fin.succAbove_succAbove_predAbove, Fin.predAbove_predAbove_succAbove]

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def hdL (R : Type u) [CommRing R] {V X : Type u} [AddCommGroup V] [Module R V] (n : ℕ) :
    ((Fin (n + 1) → X) → V) →ₗ[R] ((Fin (n + 2) → X) → V) where
  toFun := hd n
  map_add' F F' := by funext x; simp [hd, Finset.sum_add_distrib]
  map_smul' r F := by
    funext x
    simp only [hd, Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _

theorem hd_mem (M : TRep R G) (X : Type u) [TopologicalSpace X] [MulAction G X] (n : ℕ)
    (F : (Fin (n + 1) → X) → M.V) (hF : F ∈ hcoch M X n) : hd n F ∈ hcoch M X (n + 1) := by
  refine ⟨?_, fun g x => ?_⟩
  · exact continuous_finsetSum _ fun i _ => (continuous_const_smul ((-1 : ℤ) ^ (i : ℕ))).comp
      (hF.1.comp (continuous_pi fun j => continuous_apply (i.succAbove j)))

  · simp only [hd, hF.2, map_sum, map_zsmul]

def hcx (M : TRep R G) (X : Type u) [TopologicalSpace X] [MulAction G X] : Cx R where
  X n := hcoch M X n
  d n := (hdL R n).restrict fun F hF => hd_mem M X n F hF
  dd n F := Subtype.ext (hd_hd n F.1)

theorem continuous_partialProd' {m : ℕ} (i : Fin (m + 1)) :
    Continuous fun g : Fin m → G => Fin.partialProd g i := by
  induction i using Fin.induction with
  | zero => simp only [Fin.partialProd_zero]; exact continuous_const
  | succ i ih => simp only [Fin.partialProd_succ]; exact ih.mul (continuous_apply i)

def eFun (M : TRep R G) (n : ℕ) (f : (Fin n → G) → M.V) (x : Fin (n + 1) → G) : M.V :=
  M.rho (x 0) (f fun i => (x i.castSucc)⁻¹ * x i.succ)

theorem eFun_mem (M : TRep R G) (n : ℕ) (f : (Fin n → G) → M.V) (hf : Continuous f) :
    eFun M n f ∈ hcoch M G n := by
  refine ⟨?_, fun g x => ?_⟩
  · exact M.cont.comp (f := fun x : Fin (n + 1) → G => (x 0, f fun i => (x i.castSucc)⁻¹ * x i.succ))
      ((continuous_apply 0).prodMk (hf.comp (continuous_pi fun i =>
        ((continuous_apply _).inv).mul (continuous_apply _))))
  · simp only [eFun, smul_eq_mul, mul_inv_rev, mul_assoc, inv_mul_cancel_left, map_mul,
      Module.End.mul_apply]

def eIso (M : TRep R G) (n : ℕ) : M.coch.X n ≃ₗ[R] hcoch M G n where
  toFun f := ⟨eFun M n f.1, eFun_mem M n f.1 f.2⟩
  map_add' f f' := Subtype.ext (funext fun x => by
    show M.rho (x 0) ((f.1 + f'.1) fun i => _) = _
    rw [Pi.add_apply, map_add (f := _)]; rfl)
  map_smul' r f := Subtype.ext (funext fun x => by
    show M.rho (x 0) ((r • f.1) fun i => _) = _
    rw [Pi.smul_apply, map_smul]; rfl)
  invFun F := ⟨fun g => F.1 (Fin.partialProd g),
    F.2.1.comp (continuous_pi fun i => continuous_partialProd' i)⟩
  left_inv f := Subtype.ext (funext fun g => by
    simp [eFun, Fin.partialProd_zero, Fin.partialProd_right_inv])
  right_inv F := Subtype.ext (funext fun x => by
    show M.rho (x 0) (F.1 (Fin.partialProd fun i => (x i.castSucc)⁻¹ * x i.succ)) = F.1 x
    rw [← F.2.2]
    conv_rhs => rw [← Fin.partialProd_left_inv x]
    rfl)

theorem hgi_negpow (V : Type u) [AddCommGroup V] [Module R V] (k : ℕ) (v : V) :
    (-1 : R) ^ k • v = (-1 : ℤ) ^ k • v := by
  rw [← Int.cast_smul_eq_zsmul R]; push_cast; rfl

theorem eFun_zero (M : TRep R G) (n : ℕ) (f : (Fin n → G) → M.V) (x : Fin (n + 2) → G) :
    eFun M n f (fun k => x (Fin.succAbove 0 k)) =
      M.rho (x 0) (M.rho ((x (0 : Fin (n + 1)).castSucc)⁻¹ * x (0 : Fin (n + 1)).succ)
        (f fun i => (x i.succ.castSucc)⁻¹ * x i.succ.succ)) := by
  rw [← Module.End.mul_apply, ← map_mul, Fin.castSucc_zero, mul_inv_cancel_left]
  simp only [eFun, Fin.succAbove_zero, Fin.succ_castSucc]

theorem eFun_succ (M : TRep R G) (n : ℕ) (f : (Fin n → G) → M.V) (x : Fin (n + 2) → G)
    (j : Fin (n + 1)) :
    eFun M n f (fun k => x (j.succ.succAbove k)) =
      M.rho (x 0) (f (Fin.contractNth j (· * ·) fun i => (x i.castSucc)⁻¹ * x i.succ)) := by
  have key : (fun i : Fin n => (x (j.succ.succAbove i.castSucc))⁻¹ * x (j.succ.succAbove i.succ)) =
      Fin.contractNth j (· * ·) fun i => (x i.castSucc)⁻¹ * x i.succ := by
    have hp : ∀ c, Fin.partialProd (fun i => (x i.castSucc)⁻¹ * x i.succ) c = (x 0)⁻¹ * x c := by
      intro c
      have h := congrFun (Fin.partialProd_left_inv x) c
      simp only [Pi.smul_apply, smul_eq_mul] at h
      exact eq_inv_mul_of_mul_eq h
    funext k
    rw [← Fin.inv_partialProd_mul_eq_contractNth, ← Fin.succ_succAbove_succ, hp, hp]
    simp only [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]
  simp only [eFun, Fin.succ_succAbove_zero]
  rw [key]

theorem eFun_dn (M : TRep R G) (n : ℕ) (f : (Fin n → G) → M.V) :
    eFun M (n + 1) (dn M.rho n f) = hd n (eFun M n f) := by
  funext x
  rw [hd, Fin.sum_univ_succ, eFun_zero]
  simp only [eFun_succ, Fin.val_zero, pow_zero, one_smul, Fin.val_succ]
  show M.rho (x 0) (dn M.rho n f _) = _

  rw [dn_apply, map_add (f := _), map_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hgi_negpow, map_zsmul]

end HomogeneousCochainIso

open HomogeneousCochainIso

theorem homogExists_holds : HomogExistsStatement.{u} := by
  intro R _ G _ _ _ M X _ _
  exact ⟨hcx M X, fun n => LinearEquiv.refl R _, fun n a => rfl⟩

theorem homogIso_holds : HomogIsoStatement.{u} := by
  intro R _ G _ _ _ M
  refine ⟨eIso M, fun n a => ?_, fun n f x => rfl, fun n f g => ?_⟩
  · exact eFun_dn M n a.1
  · show f.1 g = M.rho (Fin.partialProd g 0) (f.1 fun i => _)
    simp [Fin.partialProd_zero, Fin.partialProd_right_inv]

end

end ReciprocityTheory.Coh
end

section

namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal

universe u

section AdmAux

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

private theorem pair_hom_f_coe_of_id {M M' : TRep R G} (P : Pair M M') (h : P.φ = MonoidHom.id G) (n : ℕ)
    (x : M.coch.X n) : (P.hom.f n x).1 = fun g => P.u (x.1 g) := by
  funext g
  show P.u (x.1 fun i => P.φ (g i)) = P.u (x.1 g)
  rw [h]
  rfl

end AdmAux

theorem admissibility_holds : AdmStatement.{u} := by
  intro R _ G _ _ _ A B C i p h
  refine ⟨fun n x y hxy => ?_, fun n => ?_, fun n => ?_⟩
  · refine Subtype.ext (funext fun g => h.emb.injective ?_)
    have hg := congrArg (fun z => z.1 g) hxy
    simp only [pair_hom_f_coe_of_id i h.i_id] at hg
    exact hg
  · intro y
    constructor
    · intro hy
      have hy' : ∀ g, p.u (y.1 g) = 0 := fun g => by
        have hg := congrArg (fun z => z.1 g) hy
        simp only [pair_hom_f_coe_of_id p h.p_id] at hg
        exact hg
      have hex : ∀ g, ∃ a, i.u a = y.1 g := fun g => (h.exact (y.1 g)).1 (hy' g)
      choose x hx using hex
      have hxc : Continuous x := by
        rw [h.emb.continuous_iff]
        have hfx : (i.u ∘ x) = y.1 := funext hx
        rw [hfx]
        exact y.2
      exact ⟨⟨x, hxc⟩, Subtype.ext ((pair_hom_f_coe_of_id i h.i_id n _).trans (funext hx))⟩
    · rintro ⟨x, rfl⟩
      refine Subtype.ext ((pair_hom_f_coe_of_id p h.p_id n _).trans ?_)
      funext g
      rw [pair_hom_f_coe_of_id i h.i_id]
      exact (h.exact (i.u (x.1 g))).2 ⟨x.1 g, rfl⟩
  · intro c
    obtain ⟨s, hs, hps⟩ := h.sec
    exact ⟨⟨s ∘ c.1, hs.comp c.2⟩,
      Subtype.ext ((pair_hom_f_coe_of_id p h.p_id n _).trans (funext fun g => hps _))⟩

theorem limRep_holds : LimRepStatement.{u} := by
  intro R _ G _ _ _ A _ τ L π hτ hemb hlift
  have cτ : ∀ m n (x : (A (m + 1)).coch.X n), ((τ m).hom.f n x).1 = fun g => (τ m).u (x.1 g) :=
    fun m n x => pair_hom_f_coe_of_id (τ m) (hτ m).1 n x
  have cπ : ∀ m n (x : L.coch.X n), ((π m).hom.f n x).1 = fun g => (π m).u (x.1 g) :=
    fun m n x => pair_hom_f_coe_of_id (π m) (hτ m).2.1 n x
  refine ⟨fun m n c => ?_, fun m n x => ?_, fun n x hx => ?_, fun n y hy => ?_⟩
  · choose s hs using (hτ m).2.2.1
    exact ⟨⟨s ∘ c.1, (continuous_of_discreteTopology (f := s)).comp c.2⟩,
      Subtype.ext ((cτ m n _).trans (funext fun g => hs _))⟩
  · refine Subtype.ext ?_
    rw [cτ, cπ, cπ]
    funext g
    exact (hτ m).2.2.2 _
  · refine Subtype.ext (funext fun g => ?_)
    apply hemb.injective
    funext m
    have hg := congrArg (fun z => z.1 g) (hx m)
    simp only [cπ] at hg
    refine hg.trans ?_
    show (0 : (A m).V) = (π m).u 0
    rw [map_zero]
  · have hy' : ∀ g m, (τ m).u ((y (m + 1)).1 g) = (y m).1 g := fun g m => by
      have hg := congrArg (fun z => z.1 g) (hy m)
      simp only [cτ] at hg
      exact hg
    choose x hx using fun g => hlift (fun m => (y m).1 g) (hy' g)
    have hxc : Continuous x := by
      rw [hemb.continuous_iff]
      have hfx : ((fun (x : L.V) m => (π m).u x) ∘ x) = fun g m => (y m).1 g :=
        funext fun g => funext (hx g)
      rw [hfx]
      exact continuous_pi fun m => by exact (y m).2
    exact ⟨⟨x, hxc⟩, fun m => Subtype.ext ((cπ m n _).trans (funext fun g => hx g m))⟩

section ColimAux

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

end ColimAux

end ReciprocityTheory.Coh
end
