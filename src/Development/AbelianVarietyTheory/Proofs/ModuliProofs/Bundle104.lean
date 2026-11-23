module

public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecMInvariantEqBotOrUnivAtGeometricPoint
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ThetaGrpActsLinearly
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaEmbeddingSectionsBaseChangeAffine
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DenseOfDenseP
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle094
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle099
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle049
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaSpan

open GlobalTheory.VVRank GlobalTheory.EmbPull GlobalTheory.ThetaReal TopologicalSpace

theorem exists_pow_smul_of_mem_span {R R' M M' I : Type} [CommRing R] [CommRing R'] [AddCommGroup M]
    [AddCommGroup M'] [Module R M] [Module R' M'] (σ : R →+* R') (φ : M →ₛₗ[σ] M') (f : R)
    (hf : ∀ d : R', ∃ (m : ℕ) (d₀ : R), σ d₀ = σ (f ^ m) * d) (t : I → M) (y : M')
    (hy : y ∈ Submodule.span R' (Set.range fun i => φ (t i))) :
    ∃ (n : ℕ) (u : M), u ∈ Submodule.span R (Set.range t) ∧ φ u = σ (f ^ n) • y := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact ⟨0, t i, Submodule.subset_span ⟨i, rfl⟩, by simp⟩
  | zero => exact ⟨0, 0, Submodule.zero_mem _, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨n, u, hu, e⟩ := hy
    obtain ⟨k, v, hv, e'⟩ := hz
    refine ⟨n + k, f ^ k • u + f ^ n • v,
      Submodule.add_mem _ (Submodule.smul_mem _ _ hu) (Submodule.smul_mem _ _ hv), ?_⟩
    rw [map_add (f := _), LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, e, e', smul_add, smul_smul, smul_smul,
      ← map_mul, ← map_mul, ← pow_add, ← pow_add, add_comm k n]
  | smul d y _ hy =>
    obtain ⟨n, u, hu, e⟩ := hy
    obtain ⟨k, d₀, hd⟩ := hf d
    refine ⟨k + n, d₀ • u, Submodule.smul_mem _ _ hu, ?_⟩
    rw [LinearMap.map_smulₛₗ, e, hd, smul_smul, smul_smul, pow_add, map_mul]
    congr 1
    ring

variable {S : Scheme.{0}} (P : PolAV S)

theorem span_eq_top_of_geomFibres (hS : SecBaseChangeAnySt) [IsAffine S] (N : ℕ) (hN : 1 ≤ N) {I : Type}
    (t : I → SecM P.A P.L N (baseOver S))
    (H : ∀ (K : Type) [Field K] [IsAlgClosed K] (w : Spec (CommRingCat.of K) ⟶ S) (h : Over.mk w ⟶ baseOver S),
      Submodule.span Γ((Over.mk w).left, ⊤) (Set.range fun i => pullM P.A P.L N h (t i)) = ⊤) :
    Submodule.span Γ((baseOver S).left, ⊤) (Set.range t) = ⊤ := by
  have haff : IsAffine (baseOver S).left := ‹IsAffine S›
  refine eq_top_iff.2 fun x _ => ?_
  let J : Ideal Γ((baseOver S).left, ⊤) := (Submodule.span Γ((baseOver S).left, ⊤) (Set.range t)).comap
    (LinearMap.toSpanSingleton _ _ x)
  have key : ∀ p : (baseOver S).left, ∃ f ∈ J, p ∈ (baseOver S).left.basicOpen f := fun p => by
    obtain ⟨V, hV, b, hb⟩ := hS S P N hN p
    obtain ⟨f, hf, hp⟩ := (isAffineOpen_top (baseOver S).left).exists_basicOpen_le (V := V) ⟨p, hV⟩ trivial
    let W := (baseOver S).left.basicOpen f
    let l : overRes W ⟶ overRes (T := baseOver S) V := Over.homMk ((baseOver S).left.homOfLE hf) (by
      change (baseOver S).left.homOfLE hf ≫ V.ι ≫ _ = W.ι ≫ _
      rw [Scheme.homOfLE_ι_assoc])
    have hW : IsAffineOpen W := (isAffineOpen_top _).basicOpen f
    have : IsAffine (overRes W).left := hW
    obtain ⟨c, hc⟩ := exists_basis P N b hb (overRes W) l
    have hspan : Submodule.span Γ((overRes W).left, ⊤)
        (Set.range fun i => pullM P.A P.L N (overResι W) (t i)) = ⊤ := by
      refine span_eq_top_of_functionals c _ fun 𝔪 h𝔪 ℓ hl y => ?_
      obtain ⟨K, _, _, u, hu⟩ := exists_geomPoint (overRes W).left 𝔪 h𝔪
      let w : Spec (CommRingCat.of K) ⟶ S := u ≫ (overRes W).hom
      let h : Over.mk w ⟶ overRes W := Over.homMk u rfl
      have haffK : IsAffine (Over.mk w).left := inferInstanceAs (IsAffine (Spec _))
      obtain ⟨b', hb'⟩ := exists_basis P N b hb (Over.mk w) (h ≫ l)
      refine (hu _).1 (functional_mem_of_span h.left.appTop.hom (pullM P.A P.L N h) c b'
        (fun i => by rw [hc, hb', pullM_comp P.A P.isLB]) _ ?_ ℓ (fun i => (hu _).2 (hl i)) y)
      simp only [pullM_comp P.A P.isLB]
      exact H K w _
    obtain ⟨n, u, hu, e⟩ := exists_pow_smul_of_mem_span (overResι W).left.appTop.hom
      (pullM P.A P.L N (overResι W)) f (exists_pow_mul_extend f) t (pullM P.A P.L N (overResι W) x)
      (hspan.ge trivial)
    obtain ⟨k, hk⟩ := exists_pow_kill_secM P N f (f ^ n • x - u) (by
      rw [map_sub, LinearMap.map_smulₛₗ, e, sub_self])
    refine ⟨f ^ k * f ^ n, ?_, ?_⟩
    · rw [smul_sub, sub_eq_zero, ← mul_smul] at hk
      change (f ^ k * f ^ n) • x ∈ Submodule.span _ _
      rw [hk]
      exact Submodule.smul_mem _ _ hu
    · rw [Scheme.mem_basicOpen_top] at hp ⊢
      simp only [map_mul, map_pow]
      exact (hp.pow _).mul (hp.pow _)
  have hI : Ideal.span (J : Set Γ((baseOver S).left, ⊤)) = ⊤ :=
    (isAffineOpen_top (baseOver S).left).self_le_iSup_basicOpen_iff.1 fun p _ => by
      obtain ⟨f, hf, hp⟩ := key p
      exact Opens.mem_iSup.2 ⟨⟨f, hf⟩, hp⟩
  rw [Ideal.span_eq, Ideal.eq_top_iff_one] at hI
  have := Submodule.mem_comap.1 hI
  rwa [LinearMap.toSpanSingleton_apply, one_smul] at this

theorem pullS_ne_zero (hS : SecBaseChangeAnySt) {T : Over S} [IsAffine T.left] {th : LB.Sec (LPow P.A P.L 1 T)}
    (hth : IsGenSec P.A P.L 1 th) {K : Type} [Field K] (w : Spec (CommRingCat.of K) ⟶ S) (h : Over.mk w ⟶ T) :
    (SecM.ofSec P.A (pullS P.A 1 h th) : SecM P.A P.L 1 (Over.mk w)) ≠ 0 := by
  intro hz
  have haffK : IsAffine (Over.mk w).left := inferInstanceAs (IsAffine (Spec _))
  have hntK : Nontrivial Γ((Over.mk w).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.domain_nontrivial
  obtain ⟨V, hV, b, hb⟩ := hS S P 1 le_rfl (w (default : Spec (CommRingCat.of K)))
  let l : Over.mk w ⟶ overRes (T := baseOver S) V := Over.homMk
    (IsOpenImmersion.lift V.ι w (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨y, rfl⟩
      rw [Subsingleton.elim (α := Spec (CommRingCat.of K)) y default]
      exact hV)) ((congrArg (_ ≫ ·) (Category.comp_id _)).trans (IsOpenImmersion.lift_fac _ _ _))
  obtain ⟨c, -⟩ := exists_basis P 1 b hb (Over.mk w) l
  let i₀ : Fin (1 ^ P.g) := ⟨0, by simp⟩
  obtain ⟨r, hr⟩ := isGenSec_pullS P hS h hth (SecM.toSec P.A (c i₀))
  have hr' : c i₀ = r • SecM.ofSec P.A (pullS P.A 1 h th) := Subtype.ext (funext hr)
  exact c.ne_zero i₀ (hr'.trans ((congrArg (r • ·) hz).trans (smul_zero r)))

theorem span_translates_mulPull_of_isGenSec : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (P : PolAV (Sp R)) (m N : ℕ), N = m ^ 2 → 1 ≤ m → IsUnit (m : Γ(Sp R, ⊤)) → ∀ (th : LB.Sec (LPow P.A P.L 1 (baseOver (Sp R)))), IsGenSec P.A P.L 1 th → ∀ (α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd (baseOver (Sp R)) P.A).left, (snd (baseOver (Sp R)) P.A ^ m).left] ![(N : ℤ), -1])), α.IsGen → ∀ s₀ : LB.Sec (LPow P.A P.L N (baseOver (Sp R))), IsTwistPull P.A P.L (mulT P.A _ m) (snd _ P.A ^ m) (lift_snd _ _) N 1 α th s₀ → ∀ (I : Type) (U : I → ThetaGrp P.A P.L N (baseOver (Sp R))) (t : I → LB.Sec (LPow P.A P.L N (baseOver (Sp R)))), (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp R) (z : Over.mk x ⟶ P.A), z ^ N = 1 → ∃ i, (Over.homMk x (by simp) : Over.mk x ⟶ baseOver (Sp R)) ≫ (U i).pt = z) → (∀ i, IsActOf P.A P.L N (U i) s₀ (t i)) → Submodule.span Γ((baseOver (Sp R)).left, ⊤) (Set.range fun i => (SecM.ofSec P.A (t i) : SecM P.A P.L N (baseOver (Sp R)))) = ⊤ := by
  intro hL hL2 R _ _ _ P m N hN hm hunit th hth α hα s₁ hs₁ I U t hU ht
  subst hN
  have hk : m ^ 2 = 1 ∨ 4 ≤ m ^ 2 := by
    rcases Nat.lt_or_ge m 2 with h | h
    · left; rw [show m = 1 by omega]; rfl
    · right; nlinarith
  have hsurj : Surjective (mulA P.A m).left := (hL.mulN (Sp R) P m hm).2.2.1
  have haff : IsAffine (baseOver (Sp R)).left := inferInstanceAs (IsAffine (Spec _))
  refine span_eq_top_of_geomFibres P hL2.secBaseChangeAny (m ^ 2) (Nat.one_le_pow _ _ hm) _ fun K _ _ w h => ?_
  obtain rfl : h = Over.homMk w (Category.comp_id _) :=
    Over.OverMorphism.ext ((Category.comp_id _).symm.trans (Over.w h))
  set h : Over.mk w ⟶ baseOver (Sp R) := Over.homMk w (Category.comp_id _)
  obtain ⟨ρ', k₁, -, k₃, k₄⟩ := thetaGrp_acts_linearly hL.globalFns (Sp R) P (m ^ 2 : ℕ) (Over.mk w)
  choose U' hU' using fun c => exists_theta_pull P.A P.isLB h (U c)
  have e : ∀ c, pullM P.A P.L (m ^ 2 : ℕ) h (SecM.ofSec P.A (t c)) =
      ρ' (U' c) (SecM.ofSec P.A (pullS P.A _ h s₁)) := fun c =>
    ((k₁ _ _ _).1 ((hU' c).2 _ _ (ht c))).symm
  simp only [e]
  have hI : Nonempty I := ⟨(hU K w 1 (by have := P.isAb.comm; exact one_pow _)).choose⟩
  refine span_translates_eq_top P.A
    ((secM_invariant_eq_bot_or_univ_at_geometric_point hL.polBaseChange).2 hL.irred (Sp R) P K w (m ^ 2) hk
    (by rw [Nat.cast_pow]; exact pow_ne_zero _ (natCast_ne_zero w hunit))) ρ' k₁ k₃ k₄ U'
    (fun θ => ?_) _ fun h0 => ?_
  · obtain ⟨c, hc'⟩ := hU K w θ.pt ((hL.kerPow (Sp R) P (m ^ 2) (Nat.one_le_pow _ _ hm) (Over.mk w) θ.pt).1 fun _ =>
      ⟨⊤, trivial, _, LB.isGen_genPull _ θ.φ θ.isGen _⟩)
    exact ⟨c, (hU' c).1.trans hc'⟩
  · obtain ⟨α', -, k₂⟩ := exists_twist_pull P.A (ψ := mulT P.A (baseOver (Sp R)) m) (hm := lift_snd _ _)
      (b := 1) P.isLB hα h (ψ' := mulT P.A (Over.mk w) m) (lift_snd _ _) (mulT_comm P.A h m)
    have hint : IsIntegral (Over.mk w ⊗ P.A).left :=
      (forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ P.A.hom P.isAb.smooth
        P.isAb.geomConnected).geometrically_isIntegral w _ _
        (IsPullback.of_hasPullback w P.A.hom).flip
    exact pullS_ne_zero P hL2.secBaseChangeAny hth w h
      (ofSec_eq_zero_of_twist P.A P.isLB (surjective_mulT P.A m hsurj _) (k₂ _ _ hs₁) h0)

end GlobalTheory.ThetaSpan
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.BilinCalc

theorem sum_antisymm {M : Type*} [AddCommGroup M] {n : ℕ} (b : Fin n → Fin n → M) (hb : ∀ i j, b i j = b j i)
    (D : Matrix (Fin n) (Fin n) ℤ) (hD : ∀ i j, D i j + D j i = 0) :
    ∑ uv : Fin n × Fin n, D uv.1 uv.2 • b uv.1 uv.2 = 0 := by
  classical

  let E : Fin n → Fin n → ℤ := fun i j => if i < j then D i j else 0
  have hDE : ∀ i j, D i j = E i j - E j i := by
    intro i j
    rcases lt_trichotomy i j with hij | rfl | hij
    · simp [E, hij, not_lt.mpr hij.le]
    · have := hD i i
      simp [E]
      omega
    · have := hD i j
      simp [E, hij, not_lt.mpr hij.le]
      omega
  have hswap : ∑ uv : Fin n × Fin n, E uv.2 uv.1 • b uv.1 uv.2 =
      ∑ uv : Fin n × Fin n, E uv.1 uv.2 • b uv.1 uv.2 := by
    refine Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun uv => ?_
    simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
    rw [hb]
  simp only [hDE, sub_smul, Finset.sum_sub_distrib, hswap, sub_self]

theorem map_prod_zpow {G M : Type*} [CommGroup G] [AddCommGroup M] (f : G → M) (hf : ∀ x y, f (x * y) = f x + f y)
    {n : ℕ} (x : Fin n → G) (c : Fin n → ℤ) : f (∏ i, x i ^ c i) = ∑ i, c i • f (x i) := by
  let φ : Additive G →+ M := AddMonoidHom.mk' (fun a => f a.toMul) fun a a' => hf _ _
  have hφ : ∀ g : G, f g = φ (Additive.ofMul g) := fun _ => rfl

  rw [hφ, ofMul_prod, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ofMul_zpow, map_zsmul, ← hφ]

theorem sum_subst {G M : Type*} [CommGroup G] [AddCommGroup M] (B : G → G → M)
    (hB : ∀ x x' y, B (x * x') y = B x y + B x' y) (hs : ∀ x y, B x y = B y x) {n m : ℕ} (x : Fin n → G)
    (W : Matrix (Fin m) (Fin m) ℤ) (W' : Matrix (Fin n) (Fin n) ℤ) (c : Matrix (Fin m) (Fin n) ℤ)
    (h : W' + W'.transpose = c.transpose * (W + W.transpose) * c) :
    ∑ uv : Fin n × Fin n, W' uv.1 uv.2 • B (x uv.1) (x uv.2) =
      ∑ uv : Fin m × Fin m, W uv.1 uv.2 • B (∏ i, x i ^ c uv.1 i) (∏ i, x i ^ c uv.2 i) := by
  classical
  have hL : ∀ (y : G) (k : Fin n → ℤ), B (∏ i, x i ^ k i) y = ∑ i, k i • B (x i) y :=
    fun y k => map_prod_zpow (fun g => B g y) (fun g g' => hB g g' y) x k
  have hR : ∀ (z : G) (k : Fin n → ℤ), B z (∏ i, x i ^ k i) = ∑ i, k i • B z (x i) :=
    fun z k => map_prod_zpow (fun g => B z g) (fun g g' => by rw [hs z, hB, hs g, hs g']) x k

  have hV : ∀ i j, ∑ a : Fin m, ∑ a' : Fin m, W a a' * (c a i * c a' j) = (c.transpose * W * c) i j := by
    intro i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hrhs : ∑ uv : Fin m × Fin m, W uv.1 uv.2 • B (∏ i, x i ^ c uv.1 i) (∏ i, x i ^ c uv.2 i) =
      ∑ ij : Fin n × Fin n, (c.transpose * W * c) ij.1 ij.2 • B (x ij.1) (x ij.2) := by
    simp only [hL, hR, Finset.smul_sum, smul_smul, Fintype.sum_prod_type, ← hV, Finset.sum_smul]
    calc _ = ∑ a : Fin m, ∑ i : Fin n, ∑ j : Fin n, ∑ a' : Fin m,
          (W a a' * (c a i * c a' j)) • B (x i) (x j) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = _ := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
  rw [hrhs, ← sub_eq_zero, ← Finset.sum_sub_distrib]
  simp only [← sub_smul]
  refine sum_antisymm (fun i j => B (x i) (x j)) (fun i j => hs _ _) (W' - c.transpose * W * c) fun i j => ?_
  have hij := congrFun (congrFun h i) j
  have ht : (c.transpose * W * c).transpose = c.transpose * W.transpose * c := by
    simp [Matrix.transpose_mul, Matrix.mul_assoc]
  have hji := congrFun (congrFun ht i) j
  simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.mul_add, Matrix.add_mul] at hij hji
  simp only [Matrix.sub_apply]
  linarith


open GlobalTheory.CechPic in
theorem main : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (Pb : LB (G2 A).left), Pb.IsLB → (∀ (T : Over S) (x x' y : T ⟶ A), (∃ t : (LB.LinComb Pb (K := Fin 3) ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]).Gen, t.IsGen) ∧ ∃ t : (LB.LinComb Pb (K := Fin 3) ![(lift y (x * x')).left, (lift y x).left, (lift y x').left] ![1, -1, -1]).Gen, t.IsGen) → LBIso Pb (Pb.pull (lift (snd A A) (fst A A)).left) → ∀ (T : Over S) (n m : ℕ) (x : Fin n → (T ⟶ A)) (W : Matrix (Fin m) (Fin m) ℤ) (W' : Matrix (Fin n) (Fin n) ℤ) (c : Matrix (Fin m) (Fin n) ℤ), W' + W'.transpose = c.transpose * (W + W.transpose) * c → LBIso (LB.LinComb Pb (K := Fin n × Fin n) (fun uv => (lift (x uv.1) (x uv.2)).left) (fun uv => W' uv.1 uv.2)) (LB.LinComb Pb (K := Fin m × Fin m) (fun uv => (lift (∏ i, x i ^ c uv.1 i) (∏ i, x i ^ c uv.2 i)).left) (fun uv => W uv.1 uv.2)) := by
  intro S A _ _ Pb hPb hbi hsym T n m x W W' c h
  classical

  let β : (T ⟶ A) → (T ⟶ A) → Pic T.left := fun u v => pull (lift u v).left (cls Pb hPb)
  have hadd : ∀ u u' v : T ⟶ A, β (u * u') v = β u v + β u' v := by
    intro u u' v
    obtain ⟨t, ht⟩ := (hbi T u u' v).1
    have e := (cls_eq_zero_iff (LB.isLB_linComb hPb _ _)).2 ⟨t, ht⟩
    rw [cls_linComb hPb] at e
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, one_smul, neg_smul] at e
    simp only [β]
    rw [← sub_eq_zero, ← e]
    abel
  have hsw : ∀ u v : T ⟶ A, β u v = β v u := by
    intro u v
    have e : cls Pb hPb = cls _ (pull_isLB hPb _) := (cls_eq_iff hPb (pull_isLB hPb _)).2 hsym
    rw [cls_pull hPb] at e
    simp only [β]
    conv_lhs => rw [e, ← pull_comp, ← Over.comp_left, comp_lift, lift_snd, lift_fst]
  refine (cls_eq_iff (LB.isLB_linComb hPb _ _) (LB.isLB_linComb hPb _ _)).1 ?_
  rw [cls_linComb hPb, cls_linComb hPb]
  exact sum_subst β hadd hsw x W W' c h

end GlobalTheory.BilinCalc
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.CechPic

section Pairing

variable {S : Scheme.{0}} {G G' T T' : Over S} [GrpObj G] [GrpObj G']

def lam (c : Pic G.left) (x y : T ⟶ G) : Pic T.left :=
  pull (x * y).left c - pull x.left c - pull y.left c + pull (1 : T ⟶ G).left c

theorem cls_cube_two {L : LB G.left} (hL : L.IsLB) (x y : T ⟶ G) (h : (cubeLB G ![x, y] L).IsLB) :
    cls _ h = lam (cls L hL) x y := by
  refine (cls_linComb hL _ _ h).trans ?_
  rw [← Equiv.sum_comp Equiv.ulift.symm,
    show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  have e : ((-1 : ℤ) ^ 2) • pull (1 : T ⟶ G).left (cls L hL) + (((-1 : ℤ) ^ 1) • pull (x * 1).left (cls L hL) +
      (((-1 : ℤ) ^ 1) • pull (y * 1).left (cls L hL) + ((-1 : ℤ) ^ 0) • pull (x * (y * 1)).left (cls L hL))) =
      lam (cls L hL) x y := by
    simp only [_root_.mul_one, lam]
    norm_num
    abel
  exact e

theorem cls_cube_three [IsCommMonObj G] {L : LB G.left} (hL : L.IsLB) (x y z : T ⟶ G)
    (h : (cubeLB G ![x, y, z] L).IsLB) :
    cls _ h = lam (cls L hL) (x * y) z - lam (cls L hL) x z - lam (cls L hL) y z := by
  refine (cls_linComb hL _ _ h).trans ?_
  rw [← Equiv.sum_comp Equiv.ulift.symm,
    show (Finset.univ : Finset (Finset (Fin 3))) = {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  have e : ((-1 : ℤ) ^ 3) • pull (1 : T ⟶ G).left (cls L hL) + (((-1 : ℤ) ^ 2) • pull (x * 1).left (cls L hL) +
      (((-1 : ℤ) ^ 2) • pull (y * 1).left (cls L hL) + (((-1 : ℤ) ^ 2) • pull (z * 1).left (cls L hL) +
      (((-1 : ℤ) ^ 1) • pull (x * (y * 1)).left (cls L hL) + (((-1 : ℤ) ^ 1) • pull (x * (z * 1)).left (cls L hL) +
      (((-1 : ℤ) ^ 1) • pull (y * (z * 1)).left (cls L hL) +
        ((-1 : ℤ) ^ 0) • pull (x * (y * (z * 1))).left (cls L hL))))))) =
      lam (cls L hL) (x * y) z - lam (cls L hL) x z - lam (cls L hL) y z := by
    simp only [_root_.mul_one, lam, _root_.mul_assoc]
    norm_num
    abel
  exact e

theorem pull_lam (h : T' ⟶ T) (c : Pic G.left) (x y : T ⟶ G) :
    pull h.left (lam c x y) = lam c (h ≫ x) (h ≫ y) := by
  simp only [lam, map_add (f := _), map_sub, ← pull_comp, ← Over.comp_left, MonObj.comp_mul, MonObj.comp_one]

theorem lam_pull (ψ : G ⟶ G') [IsMonHom ψ] (c : Pic G'.left) (x y : T ⟶ G) :
    lam (pull ψ.left c) x y = lam c (x ≫ ψ) (y ≫ ψ) := by
  simp only [lam, ← pull_comp, ← Over.comp_left, MonObj.mul_comp, MonObj.one_comp]

theorem lam_nsmul (n : ℕ) (c : Pic G.left) (x y : T ⟶ G) : lam (n • c) x y = n • lam c x y := by
  simp only [lam, map_nsmul, nsmul_add, nsmul_sub]

theorem lam_one_left (c : Pic G.left) (y : T ⟶ G) : lam c 1 y = 0 := by
  simp only [lam, _root_.one_mul]; abel

theorem lam_one_right (c : Pic G.left) (x : T ⟶ G) : lam c x 1 = 0 := by
  simp only [lam, _root_.mul_one]; abel

variable [IsCommMonObj G]

theorem lam_comm (c : Pic G.left) (x y : T ⟶ G) : lam c x y = lam c y x := by
  simp only [lam, _root_.mul_comm x y]; abel

theorem lam_mul_left {L : LB G.left} (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta G L), t.IsGen) (x y z : T ⟶ G) :
    lam (cls L hL) (x * y) z = lam (cls L hL) x z + lam (cls L hL) y z := by
  have h₀ := (cls_eq_zero_iff (N := Theta G L) (LB.isLB_linComb hL _ _)).2 hΘ
  have h₁ := (cls_cube_three hL (fst _ _) (snd _ _ ≫ fst _ _) (snd G (G ⊗ G) ≫ snd _ _)
    (LB.isLB_linComb hL _ _)).symm.trans h₀
  have h₂ := congrArg (pull (lift x (lift y z)).left) h₁
  simp only [map_sub, map_zero, pull_lam, MonObj.comp_mul, lift_fst, lift_snd_assoc, lift_snd] at h₂
  rw [sub_sub, sub_eq_zero] at h₂
  exact h₂

theorem lam_pow_left {L : LB G.left} (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta G L), t.IsGen) (x z : T ⟶ G) (n : ℕ) :
    lam (cls L hL) (x ^ n) z = n • lam (cls L hL) x z := by
  induction n with
  | zero => rw [pow_zero, lam_one_left, zero_nsmul]
  | succ n ih => rw [pow_succ, lam_mul_left hL hΘ, ih, succ_nsmul]

theorem lam_pow_right {L : LB G.left} (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta G L), t.IsGen) (x z : T ⟶ G) (n : ℕ) :
    lam (cls L hL) x (z ^ n) = n • lam (cls L hL) x z := by
  rw [lam_comm, lam_pow_left hL hΘ, lam_comm]

theorem sym_of_isSymmetric (L : RigLB G) (h : L.IsSymmetric) : Out.Sym G L.L := by
  obtain ⟨_, w, hw, -⟩ := h
  have e := (cls_eq_iff L.isLB (pull_isLB L.isLB _)).2 ⟨w, hw⟩
  rw [cls_pull L.isLB] at e
  refine fun s => ⟨⊤, trivial, (cls_eq_zero_iff (LB.isLB_linComb L.isLB _ _)).1 ?_⟩
  rw [cls_linComb L.isLB, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, pull_comp, ← e, one_smul, neg_smul, add_neg_cancel]

end Pairing

theorem dense_image_points {k : Type} [Field k] [IsAlgClosed k] {A B : Over (Sp k)} [LocallyOfFiniteType A.hom]
    (f : A ⟶ B) [Surjective f.left] (P : Set (𝟙_ (Over (Sp k)) ⟶ B)) (hP : ∀ u : 𝟙_ (Over (Sp k)) ⟶ A, u ≫ f ∈ P) :
    Dense (⋃ x ∈ P, Set.range x.left) := by
  have : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  have hd : Dense (closedPoints A.left) := dense_iff_closure_eq.2 closure_closedPoints
  refine (f.left.surjective.denseRange.dense_image f.left.continuous hd).mono ?_
  rintro _ ⟨a, ha, rfl⟩
  let u : 𝟙_ (Over (Sp k)) ⟶ A := Over.homMk (pointOfClosedPoint A.hom a ha) (pointOfClosedPoint_comp A.hom a ha)
  refine Set.mem_iUnion₂.2 ⟨u ≫ f, hP u, ⟨(default : PrimeSpectrum k), ?_⟩⟩
  exact congrArg f.left (pointOfClosedPoint_apply A.hom a ha _)

end GlobalTheory.CechPic

namespace GlobalTheory

open CechPic

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

noncomputable section
namespace GlobalTheory.ZM.NearBuild

theorem tmap_of_glies : ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S S₁ S₂ : Scheme.{0}) (A : Over S) [GrpObj A] (L : LB A.left) (act : J → (A ⟶ A)) (Q : Fin (2 * g) → (Out.baseOver S ⟶ A)) (c : S₁ ⟶ S) (s₁ : S₁ ⟶ Sp o) (t₁ : TObj g (N' ^ 2) J b s₁) (ψ₁ : t₁.A.left ⟶ A.left) (y : S₂ ⟶ S₁) (s₂ : S₂ ⟶ Sp o) (u : TObj g (N' ^ 2) J b s₂) (ψ : u.A.left ⟶ A.left), L.IsLB → GLies A act Q c t₁ ψ₁ → LBIso t₁.L (L.pull ψ₁) → GLies A act Q (y ≫ c) u ψ → LBIso u.L (L.pull ψ) → (∀ i, (u.pt i).left ≫ ψ = y ≫ (t₁.pt i).left ≫ ψ₁) → TMap u t₁ y := by
  intro o _ g N' J b S S₁ S₂ A _ L act Q c s₁ t₁ ψ₁ y s₂ u ψ hL ⟨h₁, h₄, _⟩ h₂ ⟨k₁, k₄, _⟩ k₂ k₃
  have hp := h₁.1
  obtain ⟨F, hF, hw⟩ : ∃ F : u.A.left ⟶ t₁.A.left, F ≫ ψ₁ = ψ ∧ F ≫ t₁.A.hom = u.A.hom ≫ y :=
    ⟨hp.lift ψ (u.A.hom ≫ y) (by rw [k₁.1.w, Category.assoc]), hp.lift_fst _ _ _, hp.lift_snd _ _ _⟩
  subst hF
  refine ⟨F, h₁.cancel k₁ hw, ?_, fun i => ?_, fun j => ?_⟩
  · exact LBIso.trans u.isLB (pull_isLB hL _) (pull_isLB t₁.isLB _) k₂ (lbIso_pull_comp h₂ F).symm
  · apply hp.hom_ext
    · rw [Category.assoc, k₃, Category.assoc]
    · have a₁ : (u.pt i).left ≫ u.A.hom = 𝟙 S₂ := Over.w (u.pt i)
      have a₂ : (t₁.pt i).left ≫ t₁.A.hom = 𝟙 S₁ := Over.w (t₁.pt i)
      rw [Category.assoc, hw, ← Category.assoc, a₁, Category.assoc, a₂]; simp
  · apply hp.hom_ext
    · rw [Category.assoc, k₄, Category.assoc, Category.assoc, h₄]
    · rw [Category.assoc, hw, ← Category.assoc, Over.w, Category.assoc, Over.w, hw]

end GlobalTheory.ZM.NearBuild
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.relAmple_of_open_cover_grpPullback_relAmple : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) [GrpObj A] (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left), iSup U = ⊤ → (∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) → ∀ (L : LB A.left) (M : ∀ i, LB (G i).left), L.IsLB → (∀ i, (M i).IsLB) → (∀ i, LBIso (M i) (L.pull (ψ i))) → IsAbelianScheme A → (∀ i, IsAbelianScheme (G i)) → (∀ i, Out.RelAmple (G i) (M i)) → Out.RelAmple A L := by
  first | exact @GlobalTheory.CoverGlue.relAmple_of_cover | exact GlobalTheory.CoverGlue.relAmple_of_cover | (intros; apply GlobalTheory.CoverGlue.relAmple_of_cover <;> assumption)
end
