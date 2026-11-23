module

public import Formalism.LocalToGlobal.IndefiniteReal.GramCEqTranspose
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthCommensurableInfRestrictScalarsOfLeSpan
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsOneTmulOfForallFixed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle029
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle002
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle708
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.Basic.Complex.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle707
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle015
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Formalism.LocalRingCardinality.DataTheta

@[expose] public section

section

noncomputable section

open Module
open scoped TensorProduct NumberField

namespace GlobalTheory.BadCount.RankRead

theorem finrank_iInf_ker_semilinear {L M W X ι κ : Type} [Field L] [Field M] [AddCommGroup W] [Module L W] [AddCommGroup X]
    [Module M X] [Finite ι] [Finite κ] {σ : L →+* M} (Φ : W →ₛₗ[σ] X) (b : Basis κ L W) (hb : LinearIndependent M fun k => Φ (b k))
    (a : ι → W →ₗ[L] W) (a' : ι → X →ₗ[M] X) (h : ∀ i w, a' i (Φ w) = Φ (a i w)) :
    finrank L (⨅ i, LinearMap.ker (a i) : Submodule L W) =
      finrank M ((⨅ i, LinearMap.ker (a' i)) ⊓ Submodule.span M (Set.range Φ) : Submodule M X) := by
  haveI := Module.Finite.of_basis b
  letI : Algebra L M := σ.toAlgebra
  letI : Module L X := Module.compHom X σ
  haveI : IsScalarTower L M X := ⟨fun x y z => mul_smul (σ x) y z⟩
  let U := Submodule.span M (Set.range Φ)
  let f : W →ₗ[L] U :=
    { toFun := fun w => ⟨Φ w, Submodule.subset_span ⟨w, rfl⟩⟩
      map_add' := fun x y => Subtype.ext (map_add Φ x y)
      map_smul' := fun x y => Subtype.ext (map_smulₛₗ Φ x y) }
  have hU : U = Submodule.span M (Set.range fun k => Φ (b k)) := by
    refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono (by rintro _ ⟨k, rfl⟩; exact ⟨_, rfl⟩))
    rintro _ ⟨w, rfl⟩
    haveI := Fintype.ofFinite κ

    rw [← b.sum_repr w, map_sum]
    exact Submodule.sum_mem _ fun k _ => by
      rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  let c : Basis κ M U := (Basis.span hb).map (LinearEquiv.ofEq _ _ hU.symm)
  have hc : ∀ k, c k = f (b k) := fun k => Subtype.ext (by simp [c, f])
  have hf : IsBaseChange M f := by
    refine IsBaseChange.of_equiv ((Algebra.TensorProduct.basis M b).equiv c (Equiv.refl _)) fun m => ?_
    have : ((((Algebra.TensorProduct.basis M b).equiv c (Equiv.refl _)).toLinearMap.restrictScalars L) ∘ₗ
        TensorProduct.mk L M W 1) = f := b.ext fun k => by
      rw [← hc]
      simp [← Algebra.TensorProduct.basis_apply]
    exact LinearMap.congr_fun this m
  have hm : ∀ i, ∀ x ∈ U, a' i x ∈ U := fun i => Submodule.span_le (p := U.comap (a' i)) |>.2 (by
    rintro _ ⟨w, rfl⟩
    exact Submodule.subset_span ⟨_, (h i w).symm⟩)
  rw [← GlobalTheory.finrank_iInf_ker_of_isBaseChange L M W U ι f a (fun i => (a' i).restrict (hm i)) hf
    (fun i w => Subtype.ext (h i w)), ← Submodule.finrank_map_subtype_eq U]
  refine congrArg (fun N : Submodule M X => finrank M N) (Submodule.ext fun x => ?_)
  simp only [Submodule.mem_map, Submodule.mem_iInf, LinearMap.mem_ker, Submodule.mem_inf]
  exact ⟨by rintro ⟨y, hy, rfl⟩; exact ⟨fun i => congrArg Subtype.val (hy i), y.2⟩,
    fun ⟨h1, h2⟩ => ⟨⟨x, h2⟩, fun i => Subtype.ext (h1 i), rfl⟩⟩

def twistExt {F M V Γ : Type} [Field F] [Field M] [Algebra F M] [AddCommGroup V] [Module F V] [Group Γ]
    (τ : Representation F Γ V) (χ : Γ →* Mˣ) : Representation M Γ (M ⊗[F] V) where
  toFun γ := ((χ γ : Mˣ) : M) • (τ γ).baseChange M
  map_one' := by simp [Module.End.one_eq_id]
  map_mul' γ δ := by
    rw [map_mul, map_mul, LinearMap.baseChange_mul, Units.val_mul, smul_mul_smul_comm]

theorem twistExt_tmul {F M V Γ : Type} [Field F] [Field M] [Algebra F M] [AddCommGroup V] [Module F V] [Group Γ]
    (τ : Representation F Γ V) (χ : Γ →* Mˣ) (γ : Γ) (m : M) (v : V) :
    twistExt τ χ γ (m ⊗ₜ[F] v) = ((χ γ : Mˣ) : M) • (m ⊗ₜ[F] τ γ v) := rfl

theorem finrank_eq {K L F M C W V G G' Γ : Type} [Field K] [Field L] [Field F] [Field M] [Algebra K L] [Algebra F M]
    [AddCommGroup C] [Module K C] [AddCommGroup W] [Module L W] [Module K W] [IsScalarTower K L W] [AddCommGroup V] [Module F V]
    [Group G] [Fintype G] [Group G'] [Group Γ] [Finite Γ] {j : K →+* F} (σ : L →+* M)
    (hσ : ∀ a, σ (algebraMap K L a) = algebraMap F M (j a)) (ε : C →ₗ[K] W) (π : C →ₛₗ[j] V) {n : ℕ} (b : Fin n → C)
    (b₁ : Submodule.span K (Set.range b) = ⊤) (b₂ : LinearIndependent L fun k => ε (b k))
    (b₃ : Submodule.span L (Set.range fun k => ε (b k)) = ⊤) (b₄ : LinearIndependent F fun k => π (b k))
    (ρ : G →* (W →ₗ[L] W)) (chi : G →* Lˣ) (τ : Representation F Γ V) (θ : Γ →* G) (c : G ≃* G') (s : G' →* Γ)
    (hs : ∀ g, θ (s (c g)) = g) (hρ : ∀ γ f, ∃ f', ρ (θ γ) (ε f) = ε f' ∧ τ γ (π f) = π f')
    (hinv : ∀ v, (∀ γ, θ γ = 1 → τ γ v = v) → v ∈ Submodule.span F (Set.range π))
    (P : Subgroup G) (lam : P →* Lˣ) (Q : Subgroup Γ) (hQ : ∀ γ, γ ∈ Q ↔ θ γ ∈ P) (lamb : Q →* Mˣ)
    (hlam : ∀ γ : Q, ((lamb γ : Mˣ) : M) = σ (lam ⟨θ γ, (hQ _).1 γ.2⟩ : Lˣ))
    (S : Submodule L W) (hS : ∀ w, w ∈ S ↔ ∀ p : P, ρ p w = ((chi p * lam p : Lˣ) : L) • w)
    (eC : G → L) (e : MonoidAlgebra M G') (he : ∀ g, σ (eC g) = e.coeff (c g)) :
    finrank L S = finrank M (eig (twistExt τ ((Units.map (σ : L →* M)).comp (chi.comp θ))⁻¹) Q lamb) ∧
    finrank L (S ⊓ LinearMap.ker (∑ g, (eC g * ((chi g)⁻¹ : Lˣ)) • ρ g) : Submodule L W) =
      finrank M (eig (twistExt τ ((Units.map (σ : L →* M)).comp (chi.comp θ))⁻¹) Q lamb ⊓
        LinearMap.ker (Representation.asAlgebraHom ((twistExt τ ((Units.map (σ : L →* M)).comp (chi.comp θ))⁻¹).comp s :
          Representation M G' (M ⊗[F] V)) e) : Submodule M (M ⊗[F] V)) := by
  set R := twistExt τ ((Units.map (σ : L →* M)).comp (chi.comp θ))⁻¹ with hR
  let bW : Basis (Fin n) L W := Basis.mk b₂ b₃.ge
  let Φ : W →ₛₗ[σ] M ⊗[F] V :=
    { toFun := fun w => ∑ k, σ (bW.repr w k) • ((1 : M) ⊗ₜ[F] π (b k))
      map_add' := fun x y => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun x y => by simp [Finset.smul_sum, mul_smul] }
  have hΦb : ∀ k, Φ (bW k) = (1 : M) ⊗ₜ[F] π (b k) := fun k => by
    show ∑ l, σ (bW.repr (bW k) l) • _ = _
    rw [Finset.sum_eq_single k (fun l _ hl => by simp [Finsupp.single_eq_of_ne hl]) (by simp)]
    simp
  have hΦ : ∀ f, Φ (ε f) = (1 : M) ⊗ₜ[F] π f := fun f => by
    have hf : f ∈ Submodule.span K (Set.range b) := b₁ ▸ Submodule.mem_top
    induction hf using Submodule.span_induction with
    | mem _ h => obtain ⟨k, rfl⟩ := h; rw [← hΦb, Basis.mk_apply]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), TensorProduct.tmul_add]
    | smul t x _ hx =>
      rw [map_smul, ← algebraMap_smul L, map_smulₛₗ, hx, map_smulₛₗ, hσ, algebraMap_smul, TensorProduct.tmul_smul]
  have hind : LinearIndependent M fun k => Φ (bW k) := by
    simp only [hΦb]
    exact Module.Flat.linearIndependent_one_tmul b₄
  have hRΦ : ∀ γ w, R γ (Φ w) = Φ ((((chi (θ γ))⁻¹ : Lˣ) : L) • ρ (θ γ) w) := fun γ w => by
    rw [← bW.sum_repr w]

    simp only [map_sum, map_smulₛₗ, Finset.smul_sum, RingHom.id_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    obtain ⟨f', h1, h2⟩ := hρ γ (b k)
    rw [hΦb, Basis.mk_apply, h1, hΦ, hR, twistExt_tmul, h2, smul_comm]
    simp
  have hE : eig R Q lamb ≤ Submodule.span M (Set.range Φ) := fun x hx => by
    have h0 := GlobalTheory.GaloisDescent.span_image_iInf (TensorProduct.isBaseChange F V M)
      fun γ : θ.ker => LinearMap.ker (τ γ - LinearMap.id)
    have h1 : x ∈ Submodule.span M (TensorProduct.mk F M V 1 ''
        (⨅ γ : θ.ker, LinearMap.ker (τ γ - LinearMap.id) : Submodule F V)) := by
      rw [h0, Submodule.mem_iInf]
      intro γ
      have hγ : θ γ = 1 := γ.2
      have hq : (γ : Γ) ∈ Q := (hQ _).2 (hγ ▸ P.one_mem)
      rw [GlobalTheory.GaloisDescent.span_image_ker (TensorProduct.isBaseChange F V M) (TensorProduct.isBaseChange F V M) _
        ((τ γ).baseChange M - LinearMap.id) (fun v => by simp [TensorProduct.tmul_sub])]
      have := (mem_eig R Q lamb x).1 hx ⟨γ, hq⟩
      rw [hlam, show (⟨θ γ, (hQ _).1 hq⟩ : P) = 1 from Subtype.ext hγ] at this
      simpa [hR, twistExt, hγ, sub_eq_zero] using this
    refine Submodule.span_le.2 ?_ h1
    rintro _ ⟨v, hv, rfl⟩
    have hv' := hinv v fun γ hγ => sub_eq_zero.1 ((Submodule.mem_iInf _).1 hv ⟨γ, hγ⟩)
    clear hv
    induction hv' using Submodule.span_induction with
    | mem _ h => obtain ⟨f, rfl⟩ := h; exact Submodule.subset_span ⟨_, hΦ f⟩
    | zero => simp
    | add x y _ _ hx hy =>
      change (TensorProduct.mk F M V 1) (x + y) ∈ Submodule.span M (Set.range Φ)
      rw [map_add]
      exact add_mem hx hy
    | smul t x _ hx => rw [map_smul, ← algebraMap_smul M]; exact Submodule.smul_mem _ _ hx
  let a : Q → W →ₗ[L] W := fun γ => (((chi (θ γ))⁻¹ : Lˣ) : L) • ρ (θ γ) - ((lam ⟨θ γ, (hQ _).1 γ.2⟩ : Lˣ) : L) • LinearMap.id
  let a' : Q → M ⊗[F] V →ₗ[M] M ⊗[F] V := fun γ => R γ - ((lamb γ : Mˣ) : M) • LinearMap.id
  have ha : ∀ γ w, a' γ (Φ w) = Φ (a γ w) := fun γ w => by
    simp only [a, a', LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hRΦ, map_sub, map_smulₛₗ, hlam]
  have hSa : S = ⨅ γ, LinearMap.ker (a γ) := by
    ext w
    have key : ∀ (g : G) (x : Lˣ), (((chi g)⁻¹ : Lˣ) : L) • ρ g w - (x : L) • w = 0 ↔ ρ g w = ((chi g * x : Lˣ) : L) • w :=
      fun g x => by rw [sub_eq_zero, ← Units.smul_def, inv_smul_eq_iff, Units.smul_def, smul_smul, Units.val_mul]
    rw [hS, Submodule.mem_iInf]
    refine ⟨fun h γ => (key _ _).2 (h ⟨θ γ, (hQ _).1 γ.2⟩), fun h p => ?_⟩
    have := (key _ _).1 (h ⟨s (c p), (hQ _).2 (by rw [hs]; exact p.2)⟩)
    simpa only [hs] using this
  have hEa : eig R Q lamb = ⨅ γ, LinearMap.ker (a' γ) := rfl
  refine ⟨by rw [hSa, finrank_iInf_ker_semilinear Φ bW hind a a' ha, ← hEa, inf_eq_left.2 hE], ?_⟩
  have h2 := finrank_iInf_ker_semilinear Φ bW hind (fun o : Option Q => o.elim (∑ g, (eC g * ((chi g)⁻¹ : Lˣ)) • ρ g) a)
    (fun o => o.elim (Representation.asAlgebraHom (R.comp s : Representation M G' (M ⊗[F] V)) e) a') (by
      rintro (_ | γ) w
      · haveI := Fintype.ofEquiv G c.toEquiv
        simp only [Option.elim]

        rw [Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply, Finsupp.sum_fintype _ _ (fun _ => by simp),
        LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
        refine (Fintype.sum_equiv c.toEquiv _ _ fun g => ?_).symm
        rw [LinearMap.smul_apply, LinearMap.smul_apply, mul_smul, map_smulₛₗ, he]
        exact congrArg _ (by rw [MonoidHom.comp_apply, hRΦ]; simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, hs])
      · exact ha γ w)
  rw [iInf_option, iInf_option] at h2
  simp only [Option.elim] at h2
  rw [hSa, inf_comm]
  refine h2.trans (congrArg (fun N : Submodule M (M ⊗[F] V) => finrank M N) ?_)
  rw [← hEa, inf_assoc, inf_eq_left.2 hE, inf_comm]

theorem rkK_inf {LL Ks WL G : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL] [AddCommGroup WL]
    [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL] [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL]
    [IsScalarTower (𝓞 Ks) Ks WL] {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)] [Group G]
    (A : Formalism.IndefR.Arith.FormsL LL Ks WL W G) (hK : A.IsKsForm) (hM : A.MKFull) (S : Submodule LL WL) :
    Formalism.HN.rkK (Submodule.span (𝓞 LL) (A.MK : Set WL) ⊓ S.restrictScalars (𝓞 LL)) = finrank LL S := by
  obtain ⟨n, b, h1, -, -, -, h5⟩ := hK
  have h : S ≤ Submodule.span LL (Submodule.span (𝓞 LL) (A.MK : Set WL) : Set WL) := by
    refine le_top.trans (h5.ge.trans (Submodule.span_le.2 ?_))
    rintro _ ⟨k, rfl⟩
    exact Submodule.span_mono Submodule.subset_span (Submodule.span_le_restrictScalars Ks LL _ (hM.2 ▸ h1 k))
  rw [Formalism.HN.rkK, GlobalTheory.span_inf_restrictScalars_eq LL h]

end GlobalTheory.BadCount.RankRead
end
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F

namespace GlobalTheory.JInt

theorem not_four_sq {u Δ : ℤ} (hu : Δ ≤ u) (hΔ : 0 < Δ) (r : ℤ) : u ^ 2 + Δ ≠ 4 * (r * r) := by
  intro h
  have h2 : (2 * |r|) ^ 2 = u ^ 2 + Δ := by rw [mul_pow, sq_abs]; linarith
  have hr0 : 0 ≤ 2 * |r| := by positivity
  have hu0 : 0 ≤ u := by linarith
  have a1 : u < 2 * |r| := by nlinarith
  have a2 : 2 * |r| < u + 1 := by nlinarith
  omega

theorem disc_pos {A B C D : ℤ} {τ : ℍ} (hC : C ≠ 0)
    (hfix : (A : ℂ) * τ + B = τ * (C * τ + D)) : 0 < -((D - A) ^ 2 + 4 * B * C) := by
  set x := (τ : ℂ).re
  set y := (τ : ℂ).im
  have hy : 0 < y := τ.im_pos
  have hre := congrArg Complex.re hfix
  have him := congrArg Complex.im hfix
  simp only [Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, Complex.add_im,
    Complex.mul_im] at hre him
  have h1 : ((D : ℝ) - A + 2 * C * x) * y = 0 := by linear_combination -him
  have h1' : (D : ℝ) - A + 2 * C * x = 0 := (mul_eq_zero.mp h1).resolve_right hy.ne'
  have key : (((-((D - A) ^ 2 + 4 * B * C)) : ℤ) : ℝ) = 4 * (C : ℝ) ^ 2 * y ^ 2 := by
    push_cast
    linear_combination (-(D : ℝ) + A - 2 * C * x) * h1' - 4 * (C : ℝ) * hre
  have hCr : (0 : ℝ) < (C : ℝ) ^ 2 := by positivity
  have : (0 : ℝ) < (((-((D - A) ^ 2 + 4 * B * C)) : ℤ) : ℝ) := by rw [key]; positivity
  exact_mod_cast this

theorem main : ∀ (L : PeriodPair) (c : ℂ) (τ : ℍ) (α : ℂ), IsTauOf L c τ → MulStable L α → α.im ≠ 0 →
    IsIntegral ℤ (jT τ) := by
  intro L c τ α hτ hα him
  obtain ⟨hc, hlat⟩ := hτ
  have h1 : c * (τ : ℂ) ∈ L.lattice := (hlat _).2 ⟨1, 0, by simp⟩
  have h2 : c ∈ L.lattice := (hlat _).2 ⟨0, 1, by simp⟩
  obtain ⟨A, B, hAB⟩ := (hlat _).1 (hα _ h1)
  obtain ⟨C, D, hCD⟩ := (hlat _).1 (hα _ h2)
  have e1 : α * (τ : ℂ) = A * τ + B := by apply mul_left_cancel₀ hc; linear_combination hAB
  have e2 : α = C * τ + D := by apply mul_left_cancel₀ hc; linear_combination hCD
  have hfix : (A : ℂ) * τ + B = τ * (C * τ + D) := by rw [← e1, e2]; ring
  have hC : C ≠ 0 := by
    rintro rfl
    apply him; rw [e2]; simp
  have hΔ := disc_pos hC hfix
  set Δ := -((D - A) ^ 2 + 4 * B * C) with hΔdef
  set t := A + D
  set k := Δ + |t|
  set M := (A + k) * (D + k) - B * C with hM
  have h4M : 4 * M = (2 * k + t) ^ 2 + Δ := by rw [hM, hΔdef]; ring
  have hu : Δ ≤ 2 * k + t := by
    have := neg_abs_le t; have := abs_nonneg t; linarith
  have hMpos : 0 < M := by nlinarith
  have hm : 0 < M.toNat := by omega
  have hMc : ((M.toNat : ℕ) : ℤ) = M := Int.toNat_of_nonneg hMpos.le
  refine jT_isIntegral hm ?_ (Gm_vanish hm τ (A + k) B C (D + k) (by rw [hMc]) ?_)
  · rintro ⟨r, hr⟩
    have : M = (r : ℤ) * r := by rw [← hMc, hr]; push_cast; ring
    exact not_four_sq hu hΔ r (by rw [← h4M, this])
  · push_cast; linear_combination hfix

end GlobalTheory.JInt
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal Neutral.B1
open scoped nonZeroDivisors

noncomputable section
namespace GlobalTheory.UnifVal

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem isUnit_iff_v_eq_one (a : v.adicCompletionIntegers K) :
    IsUnit a ↔ Valued.v (a : v.adicCompletion K) = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    have h1 : Valued.v ((u : v.adicCompletionIntegers K) : v.adicCompletion K) ≤ 1 := (u : v.adicCompletionIntegers K).2
    have h2 : Valued.v (((u⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K) : v.adicCompletion K) ≤ 1 :=
      ((u⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K).2
    have h3 : Valued.v ((u : v.adicCompletionIntegers K) : v.adicCompletion K) *
        Valued.v (((u⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K) : v.adicCompletion K) = 1 := by
      rw [← map_mul, ← Subring.coe_mul, Units.mul_inv]; simp
    by_contra hne
    have hlt := lt_of_le_of_ne h1 hne
    have : Valued.v ((u : v.adicCompletionIntegers K) : v.adicCompletion K) *
        Valued.v (((u⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K) : v.adicCompletion K) < 1 :=
      mul_lt_one_of_lt_of_le hlt h2
    rw [h3] at this; exact lt_irrefl _ this
  · intro h
    have ha0 : (a : v.adicCompletion K) ≠ 0 := by
      intro h0; rw [h0, map_zero] at h; exact zero_ne_one h
    have hmem : (a : v.adicCompletion K)⁻¹ ∈ v.adicCompletionIntegers K := by
      show Valued.v ((a : v.adicCompletion K)⁻¹) ≤ 1
      rw [map_inv₀, h, inv_one]
    refine isUnit_iff_exists_inv.2 ⟨⟨_, hmem⟩, ?_⟩
    apply Subtype.ext
    show (a : v.adicCompletion K) * (a : v.adicCompletion K)⁻¹ = 1
    exact mul_inv_cancel₀ ha0

theorem isUniformiserAt_iff_isUnifAt (x : (v.adicCompletion K)ˣ) :
    IsUniformiserAt K v (x : v.adicCompletion K) ↔ Formalism.L2.Host.IsUnifAt v x := by
  unfold IsUniformiserAt Formalism.L2.Host.IsUnifAt
  have hx0 : (x : v.adicCompletion K) ≠ 0 := x.ne_zero
  have hv0 : Valued.v (x : v.adicCompletion K) ≠ 0 := by simpa using hx0
  set m := WithZero.log (Valued.v (x : v.adicCompletion K)) with hm
  have hx : Valued.v (x : v.adicCompletion K) = WithZero.exp m := (WithZero.exp_log hv0).symm
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective K v (WithZero.exp (-1 : ℤ))
  have hπ0 : π ≠ 0 := by
    rintro rfl
    exact WithZero.exp_ne_zero (hπ.symm.trans (map_zero _))
  constructor
  · rintro ⟨hmem, hirr⟩
    have hle : Valued.v (x : v.adicCompletion K) ≤ 1 := hmem
    have hnu : Valued.v (x : v.adicCompletion K) ≠ 1 := fun h =>
      hirr.not_isUnit ((isUnit_iff_v_eq_one v _).2 h)
    rw [hx, ← WithZero.exp_zero, WithZero.exp_le_exp] at hle
    rw [hx, ← WithZero.exp_zero, Ne, WithZero.exp_inj] at hnu
    rw [hx]
    by_contra hne
    rw [WithZero.exp_inj] at hne
    have hm2 : m ≤ -2 := by omega
    have ha : π ∈ v.adicCompletionIntegers K := by
      show Valued.v π ≤ 1
      rw [hπ, ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num
    have hbv : Valued.v ((x : v.adicCompletion K) / π) = WithZero.exp (m + 1) := by
      rw [map_div₀, hx, hπ, ← WithZero.exp_sub, sub_neg_eq_add]
    have hb : (x : v.adicCompletion K) / π ∈ v.adicCompletionIntegers K := by
      show Valued.v ((x : v.adicCompletion K) / π) ≤ 1
      rw [hbv, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega
    have hprod : (⟨(x : v.adicCompletion K), hmem⟩ : v.adicCompletionIntegers K) =
        ⟨π, ha⟩ * ⟨(x : v.adicCompletion K) / π, hb⟩ := by
      apply Subtype.ext
      show (x : v.adicCompletion K) = π * ((x : v.adicCompletion K) / π)
      field_simp
    rcases hirr.isUnit_or_isUnit hprod with h | h
    · rw [isUnit_iff_v_eq_one] at h
      change Valued.v π = 1 at h
      rw [hπ, ← WithZero.exp_zero, WithZero.exp_inj] at h
      norm_num at h
    · rw [isUnit_iff_v_eq_one] at h
      change Valued.v ((x : v.adicCompletion K) / π) = 1 at h
      rw [hbv, ← WithZero.exp_zero, WithZero.exp_inj] at h
      omega
  · intro h
    have hmem : (x : v.adicCompletion K) ∈ v.adicCompletionIntegers K := by
      show Valued.v (x : v.adicCompletion K) ≤ 1
      rw [h, ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num
    refine ⟨hmem, irreducible_iff.2 ⟨?_, ?_⟩⟩
    · intro hu
      rw [isUnit_iff_v_eq_one] at hu
      change Valued.v (x : v.adicCompletion K) = 1 at hu
      rw [h, ← WithZero.exp_zero, WithZero.exp_inj] at hu
      norm_num at hu
    · intro a b hab
      have hv : Valued.v (a : v.adicCompletion K) * Valued.v (b : v.adicCompletion K) = WithZero.exp (-1 : ℤ) := by
        have hab' : (x : v.adicCompletion K) = (a : v.adicCompletion K) * (b : v.adicCompletion K) :=
          congrArg Subtype.val hab
        rw [← map_mul, ← hab', h]
      have ha0 : Valued.v (a : v.adicCompletion K) ≠ 0 := by
        intro h0; rw [h0, zero_mul] at hv; exact WithZero.exp_ne_zero hv.symm
      have hb0 : Valued.v (b : v.adicCompletion K) ≠ 0 := by
        intro h0; rw [h0, mul_zero] at hv; exact WithZero.exp_ne_zero hv.symm
      have hale : Valued.v (a : v.adicCompletion K) ≤ 1 := a.2
      have hble : Valued.v (b : v.adicCompletion K) ≤ 1 := b.2
      rw [← WithZero.exp_log ha0, ← WithZero.exp_zero, WithZero.exp_le_exp] at hale
      rw [← WithZero.exp_log hb0, ← WithZero.exp_zero, WithZero.exp_le_exp] at hble
      rw [← WithZero.exp_log ha0, ← WithZero.exp_log hb0, ← WithZero.exp_add, WithZero.exp_inj] at hv
      by_cases hi : WithZero.log (Valued.v (a : v.adicCompletion K)) = 0
      · left
        rw [isUnit_iff_v_eq_one, ← WithZero.exp_log ha0, hi, WithZero.exp_zero]
      · right
        have hj : WithZero.log (Valued.v (b : v.adicCompletion K)) = 0 := by omega
        rw [isUnit_iff_v_eq_one, ← WithZero.exp_log hb0, hj, WithZero.exp_zero]

end GlobalTheory.UnifVal
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.section_mem_component_generic_of_closed_valuation : ∀ (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of V)) (e σ : Spec (CommRingCat.of V) ⟶ X), Smooth f → e ≫ f = 𝟙 _ → σ ≫ f = 𝟙 _ → σ (IsLocalRing.closedPoint V) ∈ {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} → σ (⊥ : PrimeSpectrum V) ∈ {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} := by
  first | exact @GlobalTheory.section_mem_component_generic_of_closed | exact GlobalTheory.section_mem_component_generic_of_closed | (intros; apply GlobalTheory.section_mem_component_generic_of_closed <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)

namespace GlobalTheory.FibreDim

theorem smoothOfRelativeDimension_of_forall_field : ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (g : ℕ), Smooth X.hom → (∀ (k : Type) [Field k] [Algebra R k], SmoothOfRelativeDimension g (Limits.pullback.snd X.hom (spMap (algebraMap R k)))) → SmoothOfRelativeDimension g X.hom := by
  intro R _ X g hs h
  choose n W hW hd using ReciprocityTheory.ChartRestriction.G.H1.exists_dim X.hom
  have hn : ∀ x, n x = g := fun x => by
    let p : PrimeSpectrum R := X.hom x
    have hk := h p.asIdeal.ResidueField
    let t := spMap (algebraMap R p.asIdeal.ResidueField)
    obtain ⟨y, hy⟩ : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R p.asIdeal.ResidueField)) := by
      refine ⟨⟨⊥, Ideal.isPrime_bot⟩, PrimeSpectrum.ext ?_⟩
      exact Ideal.ker_algebraMap_residueField p.asIdeal
    have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} (n x)
    have h1 : SmoothOfRelativeDimension (n x) (Limits.pullback.snd ((W x).ι ≫ X.hom) t) :=
      this.of_isPullback (IsPullback.of_hasPullback ((W x).ι ≫ X.hom) t) (hd x)
    have h2 : SmoothOfRelativeDimension (0 + (0 + g)) (Limits.pullback.snd ((W x).ι ≫ X.hom) t) := by
      rw [← Limits.pullbackRightPullbackFstIso_inv_snd_snd]
      infer_instance
    obtain ⟨z, -⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback ((W x).ι ≫ X.hom) t)
      ⟨x, hW x⟩ y hy.symm
    simpa using ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ h1 h2 z
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension g) := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension g) W
    (top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hW x⟩) fun x => ?_
  rw [← hn x]; exact hd x

end GlobalTheory.FibreDim
end

section

open scoped Matrix
open Formalism.BasicNotions.TH

theorem _root_.GlobalTheory.T.eq_zero_of_cayley_two_I_zpow_eq_one_forall : ∀ m : ℤ, (∀ x : ℝ, ((1 + 2 * Complex.I * x) / (1 - 2 * Complex.I * x)) ^ m = 1) → m = 0 := by
  first | exact @GlobalTheory.zpow_cayley_two_eq_one_forall | exact GlobalTheory.zpow_cayley_two_eq_one_forall | (intros; apply GlobalTheory.zpow_cayley_two_eq_one_forall <;> assumption)
end
