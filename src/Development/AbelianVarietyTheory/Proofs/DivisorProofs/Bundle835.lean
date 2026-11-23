module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle769
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle807
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle774
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle601
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle808
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle783
public import Mathlib.RepresentationTheory.Irreducible
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle793
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle810
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle305
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankReducedLetterMatrixEqRankModMaximal
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
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp

theorem _root_.GlobalTheory.T.isCob_toCech_d0 : ∀ (I : Type) [Finite I] (X : Scheme.{0}) (R : Type) [CommRing R] (s : X ⟶ Sp R) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)), ∀ g : C0 (capF s U hU hinf), IsCob U (toCech s U hU hinf (d0 (capF s U hU hinf) g)) := by
  first | exact @GlobalTheory.CechCmp.posetOneCochainToCechCochain_coboundary | exact GlobalTheory.CechCmp.posetOneCochainToCechCochain_coboundary | (intros; apply GlobalTheory.CechCmp.posetOneCochainToCechCochain_coboundary <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp

theorem _root_.GlobalTheory.T.posetToCech_cechToPoset_cocycle_eq : ∀ (I : Type) [Finite I] (X : Scheme.{0}) (R : Type) [CommRing R] (s : X ⟶ Sp R) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)), ∀ c : GlobalTheory.KS.C1 U, IsCoc U c → toCech s U hU hinf (toPos s U hU hinf c) = c := by
  first | exact @GlobalTheory.CechCmp.toCech_toPos | exact GlobalTheory.CechCmp.toCech_toPos | (intros; apply GlobalTheory.CechCmp.toCech_toPos <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp

theorem _root_.GlobalTheory.T.isCechOneCocycle_posetOneCochainToCechCochain : ∀ (I : Type) [Finite I] (X : Scheme.{0}) (R : Type) [CommRing R] (s : X ⟶ Sp R) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)), ∀ f : GlobalTheory.CatCoh.C1 (capF s U hU hinf), f ∈ Z1 (capF s U hU hinf) → IsCoc U (toCech s U hU hinf f) := by
  first | exact @GlobalTheory.CechCmp.isCoc_toCech | exact GlobalTheory.CechCmp.isCoc_toCech | (intros; apply GlobalTheory.CechCmp.isCoc_toCech <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.cechClass_pullHO1_eq_zero_of_pullback_coboundary : ∀ (R : Type) [CommRing R] (Z : Scheme.{0}) [Z.IsSeparated] (s : Z ⟶ Sp R) (J : Type) (W : J → Z.Opens) (hW : ⨆ i, W i = ⊤), (∀ i, IsAffineOpen (W i)) → ∀ (R' : Type) [CommRing R'] (σ : R →+* R') (Y : Scheme.{0}) (s' : Y ⟶ Sp R') (ι : Y ⟶ Z) (w : ι ≫ s = s' ≫ spMap σ) (c : ∀ i i' : J, Γ(Z, W i ⊓ W i')), GlobalTheory.CechCmp.IsCocycle W c → (∃ h' : ∀ i, Γ(Y, ι ⁻¹ᵁ W i), ∀ i i', (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom (c i i') = resG Y inf_le_left (h' i) - resG Y inf_le_right (h' i')) → GlobalTheory.CechDR.pullHO1 w (GlobalTheory.CechCmp.cmp s W hW c) = 0 := by
  first | exact @GlobalTheory.CechCmp.pullHO1_cmp_eq_zero_of_coboundary | exact GlobalTheory.CechCmp.pullHO1_cmp_eq_zero_of_coboundary | (intros; apply GlobalTheory.CechCmp.pullHO1_cmp_eq_zero_of_coboundary <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.cechClassMap_sub_sum_const_linear : ∀ (R : Type) [CommRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (J : Type) (W : J → Z.Opens) (hW : ⨆ i, W i = ⊤) (c : ∀ i i' : J, Γ(Z, W i ⊓ W i')), GlobalTheory.CechCmp.IsCocycle W c → ∀ (N : ℕ) (r : Fin N → R) (e : Fin N → ∀ i i' : J, Γ(Z, W i ⊓ W i')), (∀ k, GlobalTheory.CechCmp.IsCocycle W (e k)) → GlobalTheory.CechCmp.cmp s W hW (fun i i' => c i i' - ∑ k, (GlobalTheory.CechDR.secMap s (W i ⊓ W i')).hom (r k) * e k i i') = GlobalTheory.CechCmp.cmp s W hW c - ∑ k, r k • GlobalTheory.CechCmp.cmp s W hW (e k) := by
  first | exact @GlobalTheory.CechCmp.cmp_sub_sum_lin | exact GlobalTheory.CechCmp.cmp_sub_sum_lin | (intros; apply GlobalTheory.CechCmp.cmp_sub_sum_lin <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.cechCocycle_isCoboundary_of_class_eq_zero : ∀ (R : Type) [CommRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (J : Type) (W : J → Z.Opens) (hW : ⨆ i, W i = ⊤), (∀ i, IsAffineOpen (W i)) → (∀ i i', IsAffineOpen (W i ⊓ W i')) → ∀ (c : ∀ i i' : J, Γ(Z, W i ⊓ W i')), GlobalTheory.CechCmp.IsCocycle W c → GlobalTheory.CechCmp.cmp s W hW c = 0 → ∃ h : ∀ i : J, Γ(Z, W i), ∀ i i', c i i' = resG Z inf_le_left (h i) - resG Z inf_le_right (h i') := by
  first | exact @GlobalTheory.CechCmp.exists_coboundary_of_cmp_eq_zero | exact GlobalTheory.CechCmp.exists_coboundary_of_cmp_eq_zero | (intros; apply GlobalTheory.CechCmp.exists_coboundary_of_cmp_eq_zero <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.cech_h1_class_eq_of_cocycle_affine_cover : ∀ (R : Type) [CommRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (J : Type) (W : J → Z.Opens) (hW : ⨆ i, W i = ⊤), (∀ i, IsAffineOpen (W i)) → (∀ i i', IsAffineOpen (W i ⊓ W i')) → (∀ i i' i'', IsAffineOpen (W i ⊓ W i' ⊓ W i'')) → ∀ x : GlobalTheory.CechDR.HO1 s, ∃ c : ∀ i i' : J, Γ(Z, W i ⊓ W i'), GlobalTheory.CechCmp.IsCocycle W c ∧ GlobalTheory.CechCmp.cmp s W hW c = x := by
  first | exact @GlobalTheory.CechCmp.exists_isCocycle_cmp_eq | exact GlobalTheory.CechCmp.exists_isCocycle_cmp_eq | (intros; apply GlobalTheory.CechCmp.exists_isCocycle_cmp_eq <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.HcIrr

open CategoryTheory Polynomial Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.DIV

section UnipGroup

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ}

theorem unip_diag_mul (b : ι → Fin s) {g h : GL ι K} (hg : g ∈ unip K b) (hh : h ∈ unip K b)
    (i j : ι) (hij : b i = b j) : ((g * h : GL ι K) : Matrix ι ι K) i j = if i = j then 1 else 0 := by
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [hg.2 i i rfl, if_pos rfl, one_mul, hh.2 i j hij]
  · intro k _ hki
    rcases lt_trichotomy (b k) (b i) with hlt | heq | hgt
    · rw [hg.1.1 i k hlt, zero_mul]
    · rw [hg.2 i k heq.symm, if_neg (Ne.symm hki), zero_mul]
    · rw [hh.1.1 k j (by rw [← hij]; exact hgt), mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem unip_diag_inv (b : ι → Fin s) {g : GL ι K} (hg : g ∈ unip K b)
    (i j : ι) (hij : b i = b j) : ((g⁻¹ : GL ι K) : Matrix ι ι K) i j = if i = j then 1 else 0 := by
  have h1 : ((g⁻¹ * g : GL ι K) : Matrix ι ι K) i j = if i = j then 1 else 0 := by
    rw [inv_mul_cancel, Units.val_one, Matrix.one_apply]
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single j] at h1
  · rwa [hg.2 j j rfl, if_pos rfl, mul_one] at h1
  · intro k _ hkj
    rcases lt_trichotomy (b k) (b i) with hlt | heq | hgt
    · rw [hg.1.2 i k hlt, zero_mul]
    · rw [hg.2 k j (heq.trans hij), if_neg hkj, mul_zero]
    · rw [hg.1.1 k j (by rw [← hij]; exact hgt), mul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

def cuspUnipGroup (b : ι → Fin s) : Subgroup (GL ι K) where
  carrier := unip K b
  one_mem' := ⟨one_mem _, fun i j _ => by rw [Units.val_one, Matrix.one_apply]⟩
  mul_mem' hg hh := ⟨mul_mem hg.1 hh.1, unip_diag_mul b hg hh⟩
  inv_mem' hg := ⟨inv_mem hg.1, unip_diag_inv b hg⟩

end UnipGroup

theorem tensor_eq_zero_of_fixed {K : Type} [Field K] [Fintype K] [DecidableEq K] {r s : ℕ} (b : Fin r → Fin s)
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) (c : Fin s)
    (U : Subgroup (GL {i // b i = c} K))
    (hU : ∀ v : (lam c : Type), (∀ u ∈ U, (lam c).ρ u v = v) → v = 0)
    (y : PiTensorProduct ℂ (fun c => (lam c : Type)))
    (hy : ∀ u ∈ U, PiTensorProduct.map (Function.update
      (fun c' => (LinearMap.id : (lam c' : Type) →ₗ[ℂ] (lam c' : Type))) c ((lam c).ρ u)) y = y) :
    y = 0 := by
  classical
  let f : U → ((lam c : Type) →ₗ[ℂ] (lam c : Type)) := fun u => (lam c).ρ u
  have hinv : ∀ (g : U) (v : (lam c : Type)), f g (∑ u : U, f u v) = ∑ u : U, f u v := by
    intro g v
    have hm : ∀ u : U, f g (f u v) = f (g * u) v := fun u => by
      simp only [f, Subgroup.coe_mul, map_mul, Module.End.mul_apply]

    rw [map_sum]
    simp_rw [hm]
    exact Equiv.sum_comp (Equiv.mulLeft g) (fun u => f u v)
  have hA : (∑ u : U, f u) = 0 := by
    ext v
    rw [LinearMap.sum_apply, LinearMap.zero_apply]
    exact hU _ fun u hu => hinv ⟨u, hu⟩ v
  let F : MultilinearMap (RingHom.id ℂ) (fun c' => (lam c' : Type) →ₗ[ℂ] (lam c' : Type))
      (PiTensorProduct ℂ (fun c' => (lam c' : Type)) →ₗ[ℂ] PiTensorProduct ℂ (fun c' => (lam c' : Type))) :=
    PiTensorProduct.mapMultilinear ..
  let m : ∀ c', (lam c' : Type) →ₗ[ℂ] (lam c' : Type) := fun c' => LinearMap.id
  have h1 : F (Function.update m c (∑ u : U, f u)) y = (Fintype.card U) • y := by
    rw [MultilinearMap.map_update_sum, LinearMap.sum_apply]
    have : ∀ u : U, F (Function.update m c (f u)) y = y := fun u => hy u u.2
    simp_rw [this]
    rw [Finset.sum_const, Finset.card_univ]
  rw [hA, MultilinearMap.map_update_zero, LinearMap.zero_apply] at h1
  have hcard : (Fintype.card U : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [← Nat.cast_smul_eq_nsmul ℂ] at h1
  exact (smul_eq_zero.1 h1.symm).resolve_left hcard

theorem cuspidal_tensor_no_unip_fixed : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (r s : ℕ) (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)), (∀ c, IsCuspidal K (lam c)) → ∀ S : Finset (Fin r), (∃ i j, natBlocks b i = natBlocks b j ∧ i ∈ S ∧ j ∉ S) → ∀ y : PiTensorProduct ℂ (fun c => (lam c : Type)), (∀ u : blockTri (κ := K) (natBlocks b), (∀ i j, ((u : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) i j ≠ (1 : Matrix (Fin r) (Fin r) K) i j → natBlocks b i = natBlocks b j ∧ i ∈ S ∧ j ∉ S) → leviTensor b lam u y = y) → y = 0 := by
  intro K _ _ _ r s b lam hcusp S ⟨i, j, hb, hi, hj⟩ y hy
  have hb' : b i = b j := Fin.ext hb
  let c := b i
  let b₂ : {k // b k = c} → Fin 2 := fun k => if k.1 ∈ S then 0 else 1
  have hsurj : Function.Surjective b₂ := by
    intro t
    fin_cases t
    · exact ⟨⟨i, rfl⟩, by simp [b₂, hi]⟩
    · exact ⟨⟨j, hb'.symm⟩, by simp [b₂, hj]⟩
  refine tensor_eq_zero_of_fixed b lam c (cuspUnipGroup b₂)
    (fun v hv => hcusp c 2 b₂ hsurj le_rfl v hv) y ?_
  intro u' hu'
  have hu : u' ∈ unip K b₂ := hu'
  rw [← leviTensor_blockExt b lam c u']
  apply hy
  intro x z hxz
  by_cases hin : b x = c ∧ b z = c
  · refine ⟨by simp only [natBlocks, hin.1, hin.2], ?_⟩
    have e := blockExt_in b c u' ⟨x, hin.1⟩ ⟨z, hin.2⟩
    dsimp only at e
    rw [e] at hxz
    by_contra hcon
    apply hxz
    by_cases hxS : x ∈ S <;> by_cases hzS : z ∈ S
    · rw [hu.2 ⟨x, hin.1⟩ ⟨z, hin.2⟩ (by simp [b₂, hxS, hzS])]
      simp [Matrix.one_apply, Subtype.ext_iff]
    · exact absurd ⟨hxS, hzS⟩ hcon
    · rw [hu.1.1 ⟨x, hin.1⟩ ⟨z, hin.2⟩ (by simp [b₂, hxS, hzS]),
        Matrix.one_apply_ne (by rintro rfl; exact hxS hzS)]
    · rw [hu.2 ⟨x, hin.1⟩ ⟨z, hin.2⟩ (by simp [b₂, hxS, hzS])]
      simp [Matrix.one_apply, Subtype.ext_iff]
  · exact absurd (blockExt_out b c u' x z hin) hxz

end GlobalTheory.HcIrr
end
end

section

open CategoryTheory Polynomial Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.DIV GlobalTheory.HcIrr

namespace GlobalTheory.HcIrr

section General

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)]
  [∀ i, Module ℂ (V i)]

theorem map_mem_of_position_stable (W : Submodule ℂ (PiTensorProduct ℂ V))
    (h : ∀ (c : ι) (f : V c →ₗ[ℂ] V c), ∀ x ∈ W, PiTensorProduct.map
      (Function.update (fun c' => (LinearMap.id : V c' →ₗ[ℂ] V c')) c f) x ∈ W)
    (f : ∀ i, V i →ₗ[ℂ] V i) : ∀ x ∈ W, PiTensorProduct.map f x ∈ W := by
  suffices H : ∀ S : Finset ι, ∀ x ∈ W,
      PiTensorProduct.map (fun c => if c ∈ S then f c else LinearMap.id) x ∈ W by
    intro x hx
    simpa using H Finset.univ x hx
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro x hx
    simpa [PiTensorProduct.map_id] using hx
  | insert a S ha ih =>
    intro x hx
    have e : (fun c => if c ∈ insert a S then f c else (LinearMap.id : V c →ₗ[ℂ] V c)) = fun c =>
        (Function.update (fun c' => (LinearMap.id : V c' →ₗ[ℂ] V c')) a (f a)) c ∘ₗ
          (if c ∈ S then f c else LinearMap.id) := by
      funext c
      by_cases hc : c = a
      · subst hc
        simp [ha]
      · simp [hc, Function.update_of_ne]
    rw [e, PiTensorProduct.map_comp]
    exact h a (f a) _ (ih x hx)

theorem position_stable_of_span {c : ι} {G : Type} [Group G] (ρ : Representation ℂ G (V c))
    (hs : Submodule.span ℂ (Set.range ρ) = ⊤) (W : Submodule ℂ (PiTensorProduct ℂ V))
    (h : ∀ g : G, ∀ x ∈ W, PiTensorProduct.map
      (Function.update (fun c' => (LinearMap.id : V c' →ₗ[ℂ] V c')) c (ρ g)) x ∈ W)
    (f : V c →ₗ[ℂ] V c) : ∀ x ∈ W, PiTensorProduct.map
      (Function.update (fun c' => (LinearMap.id : V c' →ₗ[ℂ] V c')) c f) x ∈ W := by
  have hf : f ∈ Submodule.span ℂ (Set.range ρ) := hs ▸ Submodule.mem_top
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨g, rfl⟩ := hf
    exact h g
  | zero =>
    intro x _
    have := PiTensorProduct.map_update_smul (fun c' => (LinearMap.id : V c' →ₗ[ℂ] V c')) c (0 : ℂ)
      LinearMap.id
    rw [zero_smul, zero_smul] at this
    rw [this]
    simp
  | add u v _ _ hu hv =>
    intro x hx
    rw [PiTensorProduct.map_update_add, LinearMap.add_apply]
    exact add_mem (hu x hx) (hv x hx)
  | smul a u _ hu =>
    intro x hx
    rw [PiTensorProduct.map_update_smul, LinearMap.smul_apply]
    exact W.smul_mem _ (hu x hx)

theorem eq_bot_or_top_of_map_stable [∀ i, FiniteDimensional ℂ (V i)]
    (W : Submodule ℂ (PiTensorProduct ℂ V))
    (h : ∀ f : ∀ i, V i →ₗ[ℂ] V i, ∀ x ∈ W, PiTensorProduct.map f x ∈ W) : W = ⊥ ∨ W = ⊤ := by
  by_cases hW : W = ⊥
  · exact Or.inl hW
  right
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  let e := fun c => Module.finBasis ℂ (V c)
  let B := Basis.piTensorProduct e
  obtain ⟨I, hI⟩ : ∃ I, B.repr x I ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hx0 (B.repr.map_eq_zero_iff.1 (Finsupp.ext hc))
  have hJ : ∀ J, B J ∈ W := by
    intro J
    let f : ∀ c, V c →ₗ[ℂ] V c := fun c => ((e c).coord (I c)).smulRight (e c (J c))
    have hf : PiTensorProduct.map f = (B.coord I).smulRight (B J) := by
      refine B.ext fun p => ?_
      have hc : ∀ c, f c (e c (p c)) = (if p c = I c then (1 : ℂ) else 0) • e c (J c) := by
        intro c
        simp [f, Finsupp.single_apply]
      have hq : (∏ c, if p c = I c then (1 : ℂ) else 0) = if p = I then 1 else 0 := by
        rw [Finset.prod_ite_zero]
        simp [funext_iff]
      rw [LinearMap.smulRight_apply, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
      simp only [B, Basis.piTensorProduct_apply, PiTensorProduct.map_tprod, hc,
        MultilinearMap.map_smul_univ, RingHom.id_apply, hq]
    have hm := h f x hx
    rw [hf, LinearMap.smulRight_apply, Module.Basis.coord_apply] at hm
    exact (W.smul_mem_iff hI).1 hm
  refine eq_top_iff.2 ?_
  rw [← B.span_eq]
  exact Submodule.span_le.2 (by rintro _ ⟨J, rfl⟩; exact hJ J)

theorem nontrivial_piTensorProduct [∀ i, FiniteDimensional ℂ (V i)] [∀ i, Nontrivial (V i)] :
    Nontrivial (PiTensorProduct ℂ V) := by
  let B := Basis.piTensorProduct fun c => Module.finBasis ℂ (V c)
  exact ⟨B fun c => ⟨0, Module.finrank_pos⟩, 0, B.ne_zero _⟩

end General

theorem leviTensor_isIrreducible : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (r s : ℕ)
    (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)),
    (∀ c, Simple (lam c)) → (leviTensor b lam).IsIrreducible := by
  intro K _ _ _ r s b lam hs
  have hirr := fun c => GlobalTheory.SerOSys.ZSum.isIrreducible_of_simple (lam c) (hs c)
  have hspan := fun c => GlobalTheory.ClassFin.span_range_eq_top_of_isIrreducible _ _ (lam c).ρ (hirr c)
  haveI : ∀ c, Nontrivial (lam c : Type) := fun c =>
    GlobalTheory.OuterTensor.nontrivial_of_isIrreducible _ (hirr c)
  haveI : Nontrivial (PiTensorProduct ℂ (fun c => (lam c : Type))) := nontrivial_piTensorProduct
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
  · exact bot_ne_top (congrArg Subrepresentation.toSubmodule h :
      (⊥ : Submodule ℂ (PiTensorProduct ℂ (fun c => (lam c : Type)))) = ⊤)
  have hstable : ∀ (c : Fin s) (f : (lam c : Type) →ₗ[ℂ] (lam c : Type)), ∀ x ∈ S.toSubmodule,
      PiTensorProduct.map (Function.update
        (fun c' => (LinearMap.id : (lam c' : Type) →ₗ[ℂ] (lam c' : Type))) c f) x ∈ S.toSubmodule := by
    intro c
    refine position_stable_of_span (lam c).ρ (hspan c) S.toSubmodule fun g x hx => ?_
    rw [← leviTensor_blockExt b lam c g]
    exact S.apply_mem_toSubmodule _ hx
  rcases eq_bot_or_top_of_map_stable S.toSubmodule (map_mem_of_position_stable _ hstable) with h | h
  · exact Or.inl (Subrepresentation.toSubmodule_injective h)
  · exact Or.inr (Subrepresentation.toSubmodule_injective h)

end GlobalTheory.HcIrr
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

variable (p : ℕ) [Fact p.Prime] {k k' : Type} [Field k] [CharP k p] [Field k'] [CharP k' p]

theorem map_inL_fr {R S : Type} [CommRing R] [CommRing S] (h : R →+* S) {d : ℕ}
    (f : MvPowerSeries (Fin d) R) : MvPowerSeries.map h (inL f) = inL (MvPowerSeries.map h f) := by
  unfold inL
  rw [map_subst (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)]
  simp only [map_X]

theorem map_inR_fr {R S : Type} [CommRing R] [CommRing S] (h : R →+* S) {d : ℕ}
    (f : MvPowerSeries (Fin d) R) : MvPowerSeries.map h (inR f) = inR (MvPowerSeries.map h f) := by
  unfold inR
  rw [map_subst (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)]
  simp only [map_X]

theorem map_coboundaryOne_teichmullerLift_law (σ : k →+* k') {d : ℕ} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k)
    (hμ : ∀ i, constantCoeff (μ i) = 0) (f : MvPowerSeries (Fin d) (Fr p k)) :
    MvPowerSeries.map (frMap p σ) (cob1 (fun i => lift p (μ i)) f) =
      cob1 (fun i => lift p (MvPowerSeries.map σ (μ i))) (MvPowerSeries.map (frMap p σ) f) := by
  unfold cob1
  rw [map_sub, map_sub, map_inL_fr, map_inR_fr,
    map_subst (hasSubst_of_constantCoeff_zero fun i => constantCoeff_lift p (hμ i))]
  simp only [map_lift]

theorem map_mem_intBy_one (σ : k →+* k') {ι : Type} {g : MvPowerSeries ι (Fr p k)}
    (hg : g ∈ intBy p k ι 1) : MvPowerSeries.map (frMap p σ) g ∈ intBy p k' ι 1 := by
  intro α
  obtain ⟨w, hw⟩ := hg α
  refine ⟨WittVector.map σ w, ?_⟩
  rw [coeff_map, hw, one_mul, one_mul, frMap_algebraMap]

theorem map_mem_quasiInt (σ : k →+* k') {ι : Type} {g : MvPowerSeries ι (Fr p k)}
    (hg : g ∈ quasiInt p k ι) : MvPowerSeries.map (frMap p σ) g ∈ quasiInt p k' ι := by
  intro α i
  obtain ⟨w, hw⟩ := hg α i
  refine ⟨WittVector.map σ w, ?_⟩
  rw [coeff_map, ← map_natCast (frMap p σ), ← map_mul, hw, frMap_algebraMap]

theorem frMap_red (σ : k →+* k') {x : Fr p k} {a : WittVector p k} {b : k}
    (hx : x = algebraMap _ (Fr p k) a) (ha : WittVector.constantCoeff a = b) :
    frMap p σ x = algebraMap _ (Fr p k') (WittVector.map σ a) ∧
      WittVector.constantCoeff (WittVector.map σ a) = σ b := by
  refine ⟨by rw [hx, frMap_algebraMap], ?_⟩
  rw [← ha, WittVector.constantCoeff_apply, WittVector.constantCoeff_apply, WittVector.map_coeff]

theorem quasiLog_map :
    ∀ (p : ℕ) [Fact p.Prime] (k k' : Type) [Field k] [CharP k p] [Field k'] [CharP k' p]
      (σ : k →+* k') (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (hμ : IsLaw μ)
      (hμ' : IsLaw (fun i => MvPowerSeries.map σ (μ i))), ∀ f ∈ quasiLog p hμ,
      MvPowerSeries.map (frMap p σ) f ∈ quasiLog p hμ' ∧
      (f ∈ intBy p k (Fin d) 1 → MvPowerSeries.map (frMap p σ) f ∈ intBy p k' (Fin d) 1) ∧
      (∀ t, Red p (cob1 (fun i => Katz.lift p (μ i)) f) t →
        Red p (cob1 (fun i => Katz.lift p (MvPowerSeries.map σ (μ i)))
          (MvPowerSeries.map (frMap p σ) f)) (MvPowerSeries.map σ t)) ∧
      ∀ w, RedV p (lin f) w → RedV p (lin (MvPowerSeries.map (frMap p σ) f)) (fun i => σ (w i)) := by
  intro p _ k k' _ _ _ _ σ d μ hμ hμ' f hf
  have key := map_coboundaryOne_teichmullerLift_law p σ μ hμ.const f
  refine ⟨⟨map_mem_quasiInt p σ hf.1, ?_⟩, map_mem_intBy_one p σ, ?_, ?_⟩
  · rw [← key]; exact map_mem_intBy_one p σ hf.2
  · intro t ht α
    obtain ⟨w, hw, hw0⟩ := ht α
    obtain ⟨e1, e2⟩ := frMap_red p σ hw hw0
    refine ⟨WittVector.map σ w, ?_, ?_⟩
    · rw [← key, coeff_map, e1]
    · rw [e2, coeff_map]
  · intro w hw i
    obtain ⟨a, ha, ha0⟩ := hw i
    obtain ⟨e1, e2⟩ := frMap_red p σ ha ha0
    refine ⟨WittVector.map σ a, ?_, e2⟩
    change coeff _ (MvPowerSeries.map (frMap p σ) f) = _
    rw [coeff_map]; exact e1

end GlobalTheory.Katz
end
end

section

open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup Coalgebra Bialgebra

theorem _root_.GlobalTheory.T.finrank_frobeniusDual_add_finrank_ker_verschiebung : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (h : (p : k) = 0) (G : PDivGroup p k), Module.finrank k (LinearMap.range ((relFrob h G.dual).app 1 : (frobTwist h G.dual).A 1 →ₐ[k] G.dual.A 1).toLinearMap) + Module.finrank k (LinearMap.ker ((verschiebung h G).app 1 : G.A 1 →ₐ[k] (frobTwist h G).A 1).toLinearMap) = Module.finrank k (G.A 1) := by
  first | exact @GlobalTheory.PDivGroup.finrank_range_relFrob_dual_add_finrank_ker_verschiebung | exact GlobalTheory.PDivGroup.finrank_range_relFrob_dual_add_finrank_ker_verschiebung | (intros; apply GlobalTheory.PDivGroup.finrank_range_relFrob_dual_add_finrank_ker_verschiebung <;> assumption)
end

section

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

theorem _root_.GlobalTheory.T.rank_reduced_letter_matrix_eq_rank_mod_maximal : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL) (T T' : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (n n' : ℕ) (b : Module.Basis (Fin n) (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥(((HW l).W K 1 LL hA.2.2).N T)) (b' : Module.Basis (Fin n') (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥(((HW l).W K 1 LL hA.2.2).N T')) (g : LatHom T.L T'.L) (A : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Mx (PowerSeries ↥(OL LL)) n' n) (e : Module.Basis (Fin n) ↥(OL LL) ↥T.L.T) (e' : Module.Basis (Fin n') ↥(OL LL) ↥T'.L.T) (a : Mx ↥(OL LL) n' n), IsCrys ((D.loc l).PD K) T.ρ → IsCrys ((D.loc l).PD K) T'.ρ → IsMapMat ((HW l).W K 1 LL hA.2.2) g b b' A → (∀ k, g.f (e k : T.V) = ∑ m, ((a m k : ↥(OL LL)) : ↥LL.1) • (e' m : T'.V)) → ∀ i, lrank ((A i).map (PowerSeries.map (residue ↥(OL LL)))) = (a.map (residue ↥(OL LL))).rank := by
  first | exact @GlobalTheory.WachRank.main | exact GlobalTheory.WachRank.main | (intros; apply GlobalTheory.WachRank.main <;> assumption)
end
